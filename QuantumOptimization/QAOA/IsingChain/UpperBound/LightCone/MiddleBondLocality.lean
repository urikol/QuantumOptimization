import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ReducedABCtoPBCBridge
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.LayerBlockMatch

/-!
# Middle-Bond Seam-Irrelevance — `genConjugate`, seam-bond peel, cost scalar-shift invariance

This file builds the **operator-identity machinery** for the middle-bond
seam-irrelevance step of the IsingChain FGG closure:

* the off-seam window geometry (`expand_midBond_disjoint_seamSites`),
* the generalized cost-operator conjugate `genConjugate`,
* scalar-shift irrelevance of the cost (`genConjugate_cost_add_smul_one`),
* the seam-bond peel (`genConjugate_seam_peel` and its concrete instantiation
  `genConjugate_middleBond_seam_irrelevance`).

All of the above is sorry-free and axiom-clean.

## Layer-order convention (RESOLVED — Option A)

The `qaoaConjugate P γ β` recursion peels `Fin.last` as the *innermost*
conjugation (`V = (MB₀CB₀)···(MB_{P-1}CB_{P-1})`, layer `P-1` applied first),
whereas the QAOA state `psiTilde` applies layer `0` first. So
`⟨+|qaoaConjugate P γ β cP(0)|+⟩` equals the REVERSED-angle physical
expectation. **Fix (Option A, landed in `ReducedABCtoPBCBridge.lean`):** feed the
REVERSED angle arrays `(fun i ↦ γ i.rev, fun i ↦ β i.rev)` to the reduced-bond
conjugate inside `BridgeSummedExpectation`/`bridge_pbc_reduced_eq_abc_psiTilde`,
keeping `psiTilde false P γ (-β)` FORWARD. This makes the literal identity
NUMERICALLY TRUE to ~1e-14 for P=1,2,3
(numerically). Option A touches no `qaoaConjugate`
definition and no match proof: `canonical_matrix_entry_match` and
`qaoa_full_eq_reduced_on_lightcone_at` stay `{propext,Classical.choice,Quot.sound}`.

CORE (`E_PBC(0) = E_ABC(0)`) is now PROVEN sorry-free, discharged by the chain
`E_PBC(0) =[transl]= E_PBC(mid) =[genConjugate_middleBond_seam_irrelevance]=
E_ABC(mid) =[genConjugate↔psiTilde state bridge + ABC T̃-transl.]= E_ABC(0)`.
The first two steps are sorry-free machinery (this file + `ReducedBondInvariance`).
The THIRD step — the `genConjugate(ABC cost) ↔ psiTilde`
Heisenberg-to-Schrödinger duality (the reduced-chain analog of `Reduction.lean`'s
operator↔state identity) — is now built: it relates
`⟨+|genConjugate P γ' β' (Hred-cost) O|+⟩` to `⟨ψ̃|O|ψ̃⟩` by unfolding
`genConjugate` to an accumulated `U_ABC†·O·U_ABC` and identifying
`U_ABC|+⟩ = psiTilde` with the `-β` mixer-sign threading (see
`StateBridge.psiTilde_expectation_eq_genConjugate`). The whole CORE is assembled
in `Reduction.bridgeSummedExpectation_holds`, axiom-clean.

## The route

After the two proven averaging halves
(`reducedChainQAOAConj_sum_eq_NR_smul_bondZero`,
`psiTilde_neg_bondZero_NR_smul_eq_shifted`), `BridgeSummedExpectation P γ β`
is logically equivalent to the single-bond CORE

```
  E_PBC(0) := ⟨+|^{N_R} reducedChainQAOAConj P γ β |+⟩^{N_R}
            = ⟨ψ̃ false P γ (-β)| cP(0) | ψ̃⟩ =: E_ABC(0).                  (CORE)
```

The CORE is proven by the three-step chain

```
  E_PBC(0) =[step 1: PBC reduced-bond translation invariance]=  E_PBC(mid)
           =[step 2: middle-bond seam-irrelevance]=              E_ABC(mid)
           =[step 3: ABC bond T̃-translation invariance]=         E_ABC(0)
```

at the central bond `mid = ⟨P, _⟩ : Fin (2P+2)`.

The geometric heart (step 2): after only `P-1` conjugation layers, the
middle bond's evolved operator is supported on `{1,…,2P}`, DISJOINT from the
seam sites `{0, 2P+1}`. The seam exponential then commutes with it and cancels
by unitarity in the `⟨+|·|+⟩` sandwich.

Source: arXiv:1906.08948v2 App. C l.1300–1408 + arXiv:1411.4028v1 §II.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Task B — off-seam window geometry (the `P-1`-radius explicit interval)
-- ============================================================================

/-- The central (middle) bond of the reduced chain `Fin (2P+2)`: sites `{P, P+1}`.
For `P ≥ 1` it is at chain-distance exactly `P` from each seam site `{0, 2P+1}`. -/
def midBond (P : ℕ) : Fin (2 * P + 2) := ⟨P, by omega⟩

/-- `(midBond P).val = P`. -/
@[simp]
theorem midBond_val (P : ℕ) : (midBond P).val = P := rfl

/-- The seam bond of the reduced chain: `cP(2P+1) = Z_{2P+1} Z_0`, sites
`{2P+1, 0}`. -/
def seamBond (P : ℕ) : Fin (2 * P + 2) := Fin.last (2 * P + 1)

/-- `(seamBond P).val = 2P+1`. -/
@[simp]
theorem seamBond_val (P : ℕ) : (seamBond P).val = 2 * P + 1 := by
  unfold seamBond; rw [Fin.val_last]

/-- The two seam sites `{0, 2P+1}` (endpoints of the seam bond). -/
def seamSites (P : ℕ) : Finset (Fin (2 * P + 2)) :=
  {(0 : Fin (2 * P + 2)), seamBond P}

/-- `bondSeed (midBond P) = {midBond P, nextSite (midBond P)}` as a `{·, ·}`
finset (matching the form `expand_by_n_seed_subset_cyclicInterval` consumes). -/
theorem bondSeed_midBond_eq (P : ℕ) :
    bondSeed (midBond P) =
      ({midBond P, IsingModel.nextSite (midBond P)} : Finset (Fin (2 * P + 2))) := by
  unfold bondSeed
  rw [Finset.insert_eq]

/-- The `(P-1)`-radius cyclic interval around the middle bond `mid = ⟨P,_⟩` on
`Fin (2P+2)` is contained in the explicit interval `{1,…,2P}`. Each element has
value `(P + ((2P+2)-(P-1)) + i) % (2P+2) = (i+1) ∈ {1,…,2P}` for
`i ∈ {0,…,2P-1}`. -/
theorem cyclicInterval_midBond_subset_interior (P : ℕ) (hP : 1 ≤ P) :
    cyclicInterval (2 * P + 2) (midBond P) (P - 1) ⊆
      Finset.Icc (1 : Fin (2 * P + 2)) ⟨2 * P, by omega⟩ := by
  intro x hx
  unfold cyclicInterval at hx
  rw [Finset.mem_image] at hx
  obtain ⟨i, hi_range, hix⟩ := hx
  rw [Finset.mem_range] at hi_range
  -- i ∈ {0,…,2(P-1)+1} = {0,…,2P-1}.
  have hi_lt : i < 2 * P := by omega
  -- x.val = (P + ((2P+2) - (P-1)) + i) % (2P+2).
  have hxval : x.val = (P + ((2 * P + 2) - (P - 1)) + i) % (2 * P + 2) := by
    rw [← hix]; rfl
  -- (2P+2) - (P-1) = P + 3, and P + (P+3) + i = (2P+2) + (i+1).
  have hsimp : (P + ((2 * P + 2) - (P - 1)) + i) = (2 * P + 2) + (i + 1) := by omega
  rw [hsimp, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : i + 1 < 2 * P + 2)] at hxval
  -- x.val = i + 1 ∈ {1,…,2P}.
  rw [Finset.mem_Icc]
  refine ⟨?_, ?_⟩
  · rw [Fin.le_def]; show (1 : ℕ) ≤ x.val; rw [hxval]; omega
  · rw [Fin.le_def]; show x.val ≤ (2 * P : ℕ); rw [hxval]; omega

/-- **Task B (off-seam window geometry, `P ≥ 1`).** The `(P-1)`-layer lightcone
window of the middle bond is contained in the explicit interval `{1,…,2P}`,
which excludes the two seam sites `0` and `2P+1`.

This is the load-bearing geometric fact for seam-disjointness. We use
`expand_by_n_seed_subset_cyclicInterval` at radius `P-1` and then the explicit
`cyclicInterval` membership computation. -/
theorem expand_midBond_subset_interior (P : ℕ) (hP : 1 ≤ P) :
    expand_by_n (P - 1) (bondSeed (midBond P)) ⊆
      Finset.Icc (1 : Fin (2 * P + 2)) ⟨2 * P, by omega⟩ := by
  rw [bondSeed_midBond_eq]
  refine subset_trans ?_ (cyclicInterval_midBond_subset_interior P hP)
  exact expand_by_n_seed_subset_cyclicInterval (midBond P) (P - 1) (by omega)

/-- The interior interval `{1,…,2P}` is disjoint from the seam sites `{0,2P+1}`. -/
theorem interior_disjoint_seamSites (P : ℕ) (_hP : 1 ≤ P) :
    Disjoint (Finset.Icc (1 : Fin (2 * P + 2)) ⟨2 * P, by omega⟩) (seamSites P) := by
  rw [Finset.disjoint_right]
  intro x hx
  unfold seamSites at hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rw [Finset.mem_Icc]
  rintro ⟨h1, h2⟩
  rcases hx with hx | hx
  · -- x = 0: contradicts 1 ≤ x.
    rw [hx, Fin.le_def] at h1
    simp at h1
  · -- x = seamBond = ⟨2P+1,_⟩: contradicts x ≤ 2P.
    rw [hx, Fin.le_def] at h2
    rw [seamBond_val] at h2
    show False
    have : (⟨2 * P, by omega⟩ : Fin (2 * P + 2)).val = 2 * P := rfl
    omega

/-- **The seam-disjointness of the `(P-1)`-layer middle-bond window.** -/
theorem expand_midBond_disjoint_seamSites (P : ℕ) (hP : 1 ≤ P) :
    Disjoint (expand_by_n (P - 1) (bondSeed (midBond P))) (seamSites P) :=
  Finset.disjoint_of_subset_left (expand_midBond_subset_interior P hP)
    (interior_disjoint_seamSites P hP)

-- ============================================================================
-- Generalized cost-operator conjugate (subsumes PBC `qaoaConjugate` and
-- the seam-flipped ABC cost conjugate)
-- ============================================================================

/-- **Generalized layered QAOA conjugate** with an arbitrary fixed cost operator
`C` (same on every layer) and the standard mixer. In the `U†·O·U` convention:
cost† outermost, mixer† innermost; the right group `mixer·cost` is the layer
unitary and the left group `cost†·mixer†` is its adjoint.

Both the PBC reduced conjugate (`C = Σ_k cP(k)`) and the ABC seam-flipped
conjugate are instances of this. -/
def genConjugate {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ) (C : Qubits.NQubitOp N)
    (O : Qubits.NQubitOp N) : Qubits.NQubitOp N :=
  match P with
  | 0 => O
  | P + 1 =>
      let O_prev := genConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) C O
      (NormedSpace.exp ((((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ)) • C) *
        NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N)) *
       O_prev *
       (NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ (Fin.last P) : ℝ) * Complex.I : ℂ)) • C))

theorem genConjugate_zero {N : ℕ} (γ β : Fin 0 → ℝ) (C O : Qubits.NQubitOp N) :
    genConjugate 0 γ β C O = O := rfl

theorem genConjugate_succ {N : ℕ} (P : ℕ) (γ β : Fin (P + 1) → ℝ)
    (C O : Qubits.NQubitOp N) :
    genConjugate (P + 1) γ β C O =
      (NormedSpace.exp ((((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ)) • C) *
        NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N)) *
       genConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) C O *
       (NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ (Fin.last P) : ℝ) * Complex.I : ℂ)) • C)) := rfl

/-- The PBC `qaoaConjugate` is the special case `C = Σ_k cP(k)`. -/
theorem qaoaConjugate_eq_genConjugate {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ)
    (O : Qubits.NQubitOp N) :
    qaoaConjugate P γ β O =
      genConjugate P γ β (∑ k : Fin N, IsingModel.chainPairInteraction k) O := by
  induction P with
  | zero => rfl
  | succ P ih =>
    rw [genConjugate_succ]
    show qaoaConjugate (P + 1) γ β O = _
    unfold qaoaConjugate
    rw [ih]

-- ============================================================================
-- Scalar-shift irrelevance of the cost operator
-- ============================================================================

/-- `c • (1 : Op)` is central: it commutes with every operator. -/
theorem smul_one_central {N : ℕ} (c : ℂ) (A : Qubits.NQubitOp N) :
    Commute (c • (1 : Qubits.NQubitOp N)) A := by
  unfold Commute SemiconjBy
  rw [smul_mul_assoc, one_mul, mul_smul_comm, mul_one]

/-- `exp(α • (C + c•1)) = exp(α • C) * exp(α • (c•1))`, factoring the central
scalar-shift exponential off. -/
theorem exp_smul_add_smul_one {N : ℕ} (α c : ℂ) (C : Qubits.NQubitOp N) :
    NormedSpace.exp (α • (C + c • (1 : Qubits.NQubitOp N))) =
      NormedSpace.exp (α • C) *
        NormedSpace.exp (α • (c • (1 : Qubits.NQubitOp N))) := by
  rw [smul_add]
  refine Matrix.exp_add_of_commute (α • C) (α • (c • (1 : Qubits.NQubitOp N))) ?_
  exact ((smul_one_central c C).smul_left α |>.smul_right α).symm

/-- The scalar-shift exponential is central (commutes with everything). -/
theorem exp_smul_smul_one_central {N : ℕ} (z c : ℂ) (A : Qubits.NQubitOp N) :
    Commute (NormedSpace.exp (z • (c • (1 : Qubits.NQubitOp N)))) A := by
  have hcomm : Commute (z • (c • (1 : Qubits.NQubitOp N))) A := by
    rw [smul_smul]
    exact smul_one_central (z * c) A
  exact hcomm.exp_left

/-- The scalar-shift exponentials at `z` and `-z` are mutually inverse. -/
theorem exp_smul_smul_one_inv {N : ℕ} (z c : ℂ) :
    NormedSpace.exp (z • (c • (1 : Qubits.NQubitOp N))) *
        NormedSpace.exp ((-z) • (c • (1 : Qubits.NQubitOp N))) = 1 := by
  rw [← Matrix.exp_add_of_commute]
  · rw [← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  · exact ((Commute.refl (c • (1 : Qubits.NQubitOp N))).smul_left z).smul_right (-z)

/-- **Scalar-shift irrelevance.** Adding a scalar multiple of the identity to the
cost operator does not change the conjugate (the scalar phases cancel under
conjugation, being central and inverse-paired across `O_prev`). -/
theorem genConjugate_cost_add_smul_one {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ)
    (c : ℂ) (C O : Qubits.NQubitOp N) :
    genConjugate P γ β (C + c • (1 : Qubits.NQubitOp N)) O =
      genConjugate P γ β C O := by
  induction P with
  | zero => rfl
  | succ P ih =>
    rw [genConjugate_succ, genConjugate_succ, ih]
    -- Abbreviations.
    set zL : ℂ := ((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ) with hzL
    set zR : ℂ := ((-γ (Fin.last P) : ℝ) * Complex.I : ℂ) with hzR
    have hzRL : zR = -zL := by rw [hzL, hzR]; push_cast; ring
    set MB := NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp N) with hMB
    set MB' := NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp N) with hMB'
    set Op := genConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) C O with hOp
    -- Factor the shifted cost exps.
    rw [exp_smul_add_smul_one zL c C, exp_smul_add_smul_one zR c C]
    set CL := NormedSpace.exp (zL • C) with hCL
    set CR := NormedSpace.exp (zR • C) with hCR
    set ZL := NormedSpace.exp (zL • (c • (1 : Qubits.NQubitOp N))) with hZL
    set ZR := NormedSpace.exp (zR • (c • (1 : Qubits.NQubitOp N))) with hZR
    -- Goal: ((CL*ZL)*MB)*Op*(MB'*(CR*ZR)) = (CL*MB)*Op*(MB'*CR).
    -- ZL central, ZR central; ZL * ZR = 1.
    have hZ_inv : ZL * ZR = 1 := by
      rw [hZL, hZR, hzRL]; exact exp_smul_smul_one_inv zL c
    have hZL_cen : ∀ A : Qubits.NQubitOp N, Commute ZL A :=
      fun A => exp_smul_smul_one_central zL c A
    have hZR_cen : ∀ A : Qubits.NQubitOp N, Commute ZR A :=
      fun A => exp_smul_smul_one_central zR c A
    -- Move ZL to the right through MB, Op, MB', CR to meet ZR.
    calc ((CL * ZL) * MB) * Op * (MB' * (CR * ZR))
        = (CL * MB) * Op * (MB' * CR) * (ZL * ZR) := by
          have h1 : (CL * ZL) * MB = (CL * MB) * ZL := by
            rw [mul_assoc, (hZL_cen MB), ← mul_assoc]
          rw [h1]
          have h2 : ((CL * MB) * ZL) * Op = ((CL * MB) * Op) * ZL := by
            rw [mul_assoc, (hZL_cen Op), ← mul_assoc]
          rw [h2]
          have h3 : MB' * (CR * ZR) = (MB' * CR) * ZR := by rw [mul_assoc]
          rw [h3]
          have h4 : (((CL * MB) * Op) * ZL) * ((MB' * CR) * ZR) =
              ((CL * MB) * Op) * (ZL * ((MB' * CR) * ZR)) := by rw [mul_assoc]
          rw [h4]
          have h5 : ZL * ((MB' * CR) * ZR) = (MB' * CR) * (ZL * ZR) := by
            rw [← mul_assoc, (hZL_cen (MB' * CR)), mul_assoc]
          rw [h5, ← mul_assoc]
      _ = (CL * MB) * Op * (MB' * CR) := by rw [hZ_inv, mul_one]

-- ============================================================================
-- Seam-bond irrelevance (Task D) — the middle-bond seam peel
-- ============================================================================

/-- `exp(α • (C + D)) = exp(α • C) * exp(α • D)` when `C` and `D` commute. -/
theorem exp_smul_add_of_commute {N : ℕ} (α : ℂ) (C D : Qubits.NQubitOp N)
    (h : Commute C D) :
    NormedSpace.exp (α • (C + D)) =
      NormedSpace.exp (α • C) * NormedSpace.exp (α • D) := by
  rw [smul_add]
  exact Matrix.exp_add_of_commute (α • C) (α • D) ((h.smul_left α).smul_right α)

/-- `exp(α • (C + D)) = exp(α • D) * exp(α • C)` (the other factoring order). -/
theorem exp_smul_add_of_commute' {N : ℕ} (α : ℂ) (C D : Qubits.NQubitOp N)
    (h : Commute C D) :
    NormedSpace.exp (α • (C + D)) =
      NormedSpace.exp (α • D) * NormedSpace.exp (α • C) := by
  rw [add_comm C D]
  exact exp_smul_add_of_commute α D C h.symm

/-- The seam factors `exp(zL • D)` and `exp(zR • D)` (with `zR = -zL`) are
mutually inverse. -/
theorem exp_smul_D_inv {N : ℕ} (z : ℂ) (D : Qubits.NQubitOp N) :
    NormedSpace.exp (z • D) * NormedSpace.exp ((-z) • D) = 1 := by
  rw [← Matrix.exp_add_of_commute]
  · rw [← add_smul, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  · exact ((Commute.refl D).smul_left z).smul_right (-z)

/-- The mixer-conjugate `MB * Op * MB'` of an operator supported on `W` is still
supported on `W` (the mixer preserves tensor support). Here `MB = exp(βI·M)`,
`MB' = exp(-βI·M)` in the `genConjugate` recursion's notation. -/
theorem mixerConj_supportedOn {N : ℕ} {W : Finset (Fin N)} {Op : Qubits.NQubitOp N}
    (hOp : tensorSupportedOn W Op) (β : ℝ) :
    tensorSupportedOn W
      (NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
        Op *
        NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) := by
  have h := tensorSupportedOn_mixer_layer_conj hOp (-β)
  simpa using h

/-- Monotonicity of `expand_by_n` in the radius. -/
theorem expand_by_n_mono {N : ℕ} {Q R : ℕ} (hQR : Q ≤ R) (S : Finset (Fin N)) :
    expand_by_n Q S ⊆ expand_by_n R S := by
  induction hQR with
  | refl => exact subset_rfl
  | step _ ih => exact subset_trans ih (expand_by_n_subset_succ _ S)

/-- For `Q ≤ P-1`, the radius-`Q` middle-bond window is off the seam sites. -/
theorem expand_midBond_disjoint_seamSites_le (P : ℕ) (hP : 1 ≤ P) (Q : ℕ)
    (hQ : Q ≤ P - 1) :
    Disjoint (expand_by_n Q (bondSeed (midBond P))) (seamSites P) :=
  Finset.disjoint_of_subset_left
    (expand_by_n_mono hQ (bondSeed (midBond P)))
    (expand_midBond_disjoint_seamSites P hP)

/-- **The middle-bond seam peel (operator identity, abstract form).**

Let `Cfull` be the full cost, `D` supported on a fixed set `T` and commuting with
`Cfull`; set `C := Cfull - D`. Suppose the FULL conjugate `genConjugate Q γ' β'
Cfull O` is supported on a window `W Q` disjoint from `T` for every `Q ≤ R` (this
is the PBC support fact, available for all angles). Then for every `Q ≤ R + 1`,

`genConjugate Q γ' β' Cfull O = genConjugate Q γ' β' (Cfull - D) O`,

i.e. the `D` summand of the cost (the seam) is irrelevant.

The peel is per-layer: the outermost cost factor splits as
`exp(α·Cfull) = exp(α·C)·exp(α·D)`; the seam factor `exp(α·D)` (supported on `T`)
commutes with the mixer-conjugate of the inner conjugate (supported on
`W (Q-1)` ⊆ off-`T`), so the two seam factors meet and cancel by unitarity. -/
theorem genConjugate_seam_peel {N : ℕ} {Cfull D O : Qubits.NQubitOp N}
    {T : Finset (Fin N)} {W : ℕ → Finset (Fin N)}
    (hcomm : Commute Cfull D)
    (hDexp : ∀ r : ℝ, tensorSupportedOn T
      (NormedSpace.exp ((((-r : ℝ) * Complex.I : ℂ)) • D)))
    (R : ℕ)
    (hsupp : ∀ Q : ℕ, Q ≤ R → ∀ γ' β' : Fin Q → ℝ,
      tensorSupportedOn (W Q) (genConjugate Q γ' β' Cfull O))
    (hWdisj : ∀ Q : ℕ, Q ≤ R → Disjoint (W Q) T) :
    ∀ Q : ℕ, Q ≤ R + 1 → ∀ γ β : Fin Q → ℝ,
      genConjugate Q γ β Cfull O = genConjugate Q γ β (Cfull - D) O := by
  intro Q
  induction Q with
  | zero => intro _ γ β; rfl
  | succ Q ih =>
    intro hQ γ β
    have hQ' : Q ≤ R := by omega
    have hQ_le : Q ≤ R + 1 := by omega
    rw [genConjugate_succ, genConjugate_succ]
    -- IH: inner conjugates agree.
    rw [ih hQ_le (fun i => γ i.castSucc) (fun i => β i.castSucc)]
    -- Now both sides have inner `genConjugate Q (Cfull - D) O`, but the cost
    -- exponentials differ (Cfull vs Cfull - D). Peel the D factor.
    set Op := genConjugate Q (fun i => γ i.castSucc) (fun i => β i.castSucc)
      (Cfull - D) O with hOp
    -- The inner is supported on `W Q` (off-seam), via the equality to the full side.
    have hOp_supp : tensorSupportedOn (W Q) Op := by
      rw [hOp, ← ih hQ_le (fun i => γ i.castSucc) (fun i => β i.castSucc)]
      exact hsupp Q hQ' (fun i => γ i.castSucc) (fun i => β i.castSucc)
    -- Abbreviate the cost exponent scalars and factors.
    set zL : ℂ := ((-(-γ (Fin.last Q)) : ℝ) * Complex.I : ℂ) with hzL
    set zR : ℂ := ((-γ (Fin.last Q) : ℝ) * Complex.I : ℂ) with hzR
    have hzRL : zR = -zL := by rw [hzL, hzR]; push_cast; ring
    -- C := Cfull - D, so Cfull = C + D.
    set C := Cfull - D with hC
    have hCfull : Cfull = C + D := by rw [hC]; abel
    have hcommC : Commute C D := by
      rw [hC]; exact (hcomm.sub_left (Commute.refl D))
    -- Factor the full cost exps (on the LHS) via Cfull = C + D.
    rw [hCfull]
    rw [exp_smul_add_of_commute zL C D hcommC,
        exp_smul_add_of_commute' zR C D hcommC]
    set CL := NormedSpace.exp (zL • C) with hCL
    set CR := NormedSpace.exp (zR • C) with hCR
    set DL := NormedSpace.exp (zL • D) with hDL
    set DR := NormedSpace.exp (zR • D) with hDR
    set MB := NormedSpace.exp ((((-(-β (Fin.last Q)) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp N) with hMB
    set MB' := NormedSpace.exp ((((-β (Fin.last Q) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp N) with hMB'
    -- Goal: ((CL*DL)*MB)*Op*(MB'*(DR*CR)) = (CL*MB)*Op*(MB'*CR).
    -- The mixer-conjugate `A := MB*Op*MB'` is supported on `W Q` (off-T).
    have hA_supp : tensorSupportedOn (W Q) (MB * Op * MB') := by
      rw [hMB, hMB']; exact mixerConj_supportedOn hOp_supp (β (Fin.last Q))
    -- DL, DR commute with A (disjoint supports T ⟂ W Q).
    have hWT : Disjoint (W Q) T := hWdisj Q hQ'
    have hDL_supp : tensorSupportedOn T DL := by
      rw [hDL, hzL]; exact hDexp (-γ (Fin.last Q))
    have hDR_supp : tensorSupportedOn T DR := by
      rw [hDR, hzR]; exact hDexp (γ (Fin.last Q))
    have hDL_A : Commute DL (MB * Op * MB') :=
      tensorSupportedOn_commute_of_disjoint hDL_supp hA_supp hWT.symm
    have hDR_A : Commute DR (MB * Op * MB') :=
      tensorSupportedOn_commute_of_disjoint hDR_supp hA_supp hWT.symm
    have hD_inv : DL * DR = 1 := by
      rw [hDL, hDR, hzRL]; exact exp_smul_D_inv zL D
    -- Reassociate everything around A = MB*Op*MB' and peel.
    calc ((CL * DL) * MB) * Op * (MB' * (DR * CR))
        = CL * (DL * (MB * Op * MB')) * (DR * CR) := by
          simp only [mul_assoc]
      _ = CL * ((MB * Op * MB') * DL) * (DR * CR) := by rw [hDL_A]
      _ = CL * (MB * Op * MB') * (DL * (DR * CR)) := by simp only [mul_assoc]
      _ = CL * (MB * Op * MB') * ((DL * DR) * CR) := by rw [mul_assoc DL DR CR]
      _ = CL * (MB * Op * MB') * CR := by rw [hD_inv, one_mul]
      _ = (CL * MB) * Op * (MB' * CR) := by simp only [mul_assoc]

-- ============================================================================
-- Concrete instantiation: middle-bond seam-irrelevance for the reduced chain
-- ============================================================================

/-- The full PBC cost `Σ_k cP(k)`. -/
def costFull (P : ℕ) : Qubits.NQubitOp (2 * P + 2) :=
  ∑ k : Fin (2 * P + 2), IsingModel.chainPairInteraction k

/-- The seam summand `D = 2 • cP(seam)` of the cost (the difference between PBC
and the seam-flipped ABC cost). -/
def costSeamDiff (P : ℕ) : Qubits.NQubitOp (2 * P + 2) :=
  (2 : ℂ) • IsingModel.chainPairInteraction (seamBond P)

/-- `bondSeed (seamBond P) = seamSites P` (both equal `{2P+1, 0}`). -/
theorem bondSeed_seamBond_eq (P : ℕ) :
    bondSeed (seamBond P) = seamSites P := by
  unfold bondSeed seamSites seamBond
  -- {Fin.last (2P+1)} ∪ {nextSite (Fin.last (2P+1))} = {0, Fin.last (2P+1)}.
  have hns : IsingModel.nextSite (Fin.last (2 * P + 1) : Fin (2 * P + 2)) =
      (0 : Fin (2 * P + 2)) := by
    apply Fin.ext
    rw [IsingModel.nextSite_val, Fin.val_last]
    have h0 : (0 : Fin (2 * P + 2)).val = 0 := rfl
    rw [h0]
    have : (2 * P + 1 + 1) % (2 * P + 2) = 0 := by
      rw [show 2 * P + 1 + 1 = 2 * P + 2 from by ring]; exact Nat.mod_self _
    exact this
  rw [hns]
  -- {last} ∪ {0} = {0, last}.
  ext x
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]
  tauto

/-- `Commute (costFull P) (costSeamDiff P)`: all bond interactions commute. -/
theorem commute_costFull_costSeamDiff (P : ℕ) :
    Commute (costFull P) (costSeamDiff P) := by
  unfold costFull costSeamDiff
  refine Commute.sum_left _ _ _ ?_
  intro k _
  exact (chainPairInteractions_commute k (seamBond P)).smul_right _

/-- The seam factor `exp((-r·I) • (2•cP(seam)))` is tensor-supported on the seam
sites, for every real angle `r`. We absorb the `2` into a doubled angle and use
the single-bond exponential support lemma. -/
theorem costSeamDiff_exp_supportedOn (P : ℕ) (r : ℝ) :
    tensorSupportedOn (seamSites P)
      (NormedSpace.exp ((((-r : ℝ) * Complex.I : ℂ)) • costSeamDiff P)) := by
  unfold costSeamDiff
  -- (-r·I) • (2 • cP) = (-(2r)·I) • cP.
  rw [smul_smul]
  rw [show (((-r : ℝ) * Complex.I : ℂ)) * (2 : ℂ) =
      (((-(2 * r) : ℝ) * Complex.I : ℂ)) from by push_cast; ring]
  rw [← bondSeed_seamBond_eq]
  unfold bondSeed
  exact tensorSupportedOn_exp_chainPairInteraction (2 * r) (seamBond P)

/-- `costFull P = (costFull P - costSeamDiff P) + costSeamDiff P` and the ABC
seam-flipped cost is `costFull P - costSeamDiff P`. -/
theorem costFull_sub_costSeamDiff_eq (P : ℕ) :
    costFull P - costSeamDiff P =
      (∑ k : Fin (2 * P + 1),
          IsingModel.chainPairInteraction (k.castSucc : Fin (2 * P + 2))) -
        IsingModel.chainPairInteraction (seamBond P) := by
  unfold costFull costSeamDiff seamBond
  rw [Fin.sum_univ_castSucc]
  -- (Σ_interior + cP(last)) - 2•cP(last) = Σ_interior - cP(last).
  rw [two_smul]
  abel

/-- **Middle-bond seam-irrelevance (operator identity, `P ≥ 1`).**
The PBC conjugate of the middle bond equals the seam-flipped (ABC) conjugate:

`genConjugate P γ β (costFull P) (cP mid) =
   genConjugate P γ β (costFull P - costSeamDiff P) (cP mid)`.

The seam summand `costSeamDiff P` is irrelevant because, after `P-1` layers, the
middle-bond conjugate is supported off the seam. -/
theorem genConjugate_middleBond_seam_irrelevance (P : ℕ) (hP : 1 ≤ P)
    (γ β : Fin P → ℝ) :
    genConjugate P γ β (costFull P)
        (IsingModel.chainPairInteraction (midBond P)) =
      genConjugate P γ β (costFull P - costSeamDiff P)
        (IsingModel.chainPairInteraction (midBond P)) := by
  -- Apply the abstract seam peel with R = P - 1 (so R + 1 = P), T = seamSites,
  -- W Q = expand_by_n Q (bondSeed mid).
  have hR1 : (P - 1) + 1 = P := by omega
  have key := genConjugate_seam_peel
    (Cfull := costFull P) (D := costSeamDiff P)
    (O := IsingModel.chainPairInteraction (midBond P))
    (T := seamSites P) (W := fun Q => expand_by_n Q (bondSeed (midBond P)))
    (commute_costFull_costSeamDiff P)
    (costSeamDiff_exp_supportedOn P)
    (P - 1)
    (by
      -- support of the full conjugate = qaoaConjugate, via the bridge.
      intro Q _ γ' β'
      rw [show costFull P = ∑ k : Fin (2 * P + 2),
            IsingModel.chainPairInteraction k from rfl,
          ← qaoaConjugate_eq_genConjugate]
      have hseed : bondSeed (midBond P) =
          ({midBond P} : Finset (Fin (2 * P + 2))) ∪
            ({IsingModel.nextSite (midBond P)} : Finset (Fin (2 * P + 2))) := rfl
      rw [hseed]
      exact tensorSupportedOn_qaoa_conj
        (tensorSupportedOn_chainPairInteraction (midBond P)) Q γ' β')
    (by
      intro Q hQ
      exact expand_midBond_disjoint_seamSites_le P hP Q hQ)
    P (by omega) γ β
  exact key

end

end QAOA.IsingChain.UpperBound.LightCone
