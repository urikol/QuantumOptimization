import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.CommuteSuite

/-!
# Active-Subspace Preservation — `psiTilde_inActiveSubspace`

The reduced QAOA state stays in the active pair-occupation
subspace. Built on the `CommuteSuite` commute calculus:

* the eigenvalue-condition converse `inActiveSubspace_of_conditions` and the per-mode
  preservation `dotTau_preserves_inActiveSubspace`/`HredZMode`/`HredXMode`;
* Hermiticity of `activeProj`, `Hred_z_pm`, `Hred_x_op` (via `noncommProd_isHermitian`),
  turning the one-sided identity `Π·H·Π = H·Π` into the full commutator
  `Commute (Hred_z_pm) (activeProj)` and its exponential `Commute (costExponential …) (activeProj)`;
* the depth induction `reducedQAOA_preserves_inActiveSubspace` and the U1 uniform-state
  base case (`cAnnihK_mulVec_uniformKet` ⟹ `inActiveSubspace_uniformState`), assembled into
  `psiTilde_inActiveSubspace`.

## Main statements
- `Hred_z_pm_commute_activeProj` / `Hred_x_op_commute_activeProj`: the cost/mixer
  reduced Hamiltonians commute with the active-subspace projector
- `noncommProd_isHermitian`: a `noncommProd` of pairwise-commuting Hermitians is Hermitian
- `inActiveSubspace_uniformState`: the uniform initial state is active
- `psiTilde_inActiveSubspace`: the reduced QAOA state `psiTilde false P γ (−β)` is active
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

/-- `S_k = activeFactor` GLOBALLY: the pair-block square operator equals
the active-pair projector factor `(1 + P_k)/2`, as a clean global algebraic identity.
`Spair_eq` (PauliKernel) gives `S_k = 1 − n_k − n_{−k} + 2 n_k n_{−k}`, which matches
`(1 + (1−2n_k)(1−2n_{−k}))/2` term-for-term. -/
theorem Spair_eq_activeFactor (P : ℕ) (n : Fin P) :
    Spair P n = activeFactor P n := by
  rw [Spair, PauliKernel.Spair_eq]
  unfold activeFactor pairParity
  -- numberOpK P (waveVectorABC P n) = cCreateK * cAnnihK, matching d*a / e*b
  change (1 : NQubitOp (2*P+2)) - cCreateK P (waveVectorABC P n) * cAnnihK P (waveVectorABC P n)
      - cCreateK P (-(waveVectorABC P n)) * cAnnihK P (-(waveVectorABC P n))
      + 2 • ((cCreateK P (waveVectorABC P n) * cAnnihK P (waveVectorABC P n)) *
          (cCreateK P (-(waveVectorABC P n)) * cAnnihK P (-(waveVectorABC P n))))
    = (1 / 2 : ℂ) • (1 + (1 - (2 : ℂ) • (cCreateK P (waveVectorABC P n) * cAnnihK P (waveVectorABC P n)))
        * (1 - (2 : ℂ) • (cCreateK P (-(waveVectorABC P n)) * cAnnihK P (-(waveVectorABC P n)))))
  rw [mul_sub, sub_mul, sub_mul, mul_one, one_mul]
  simp only [smul_mul_assoc, mul_smul_comm, mul_one, smul_smul]
  module

-- ----------------------------------------------------------------------------
-- The converse `eigenvalue-conditions → InActiveSubspace`, and per-mode
-- preservation `HredZMode k_n` maps the active subspace to itself.
-- ----------------------------------------------------------------------------

/-- If `v` satisfies the four active-subspace eigenvalue conditions
(`n_0·v = 0`, `n_π·v = 0`, `P_m·v = v` for every active pair `m`), then `v` lies in
the active subspace (`activeProj·v = v`). The converse of the projection lemmas
`inActiveSubspace_{n0,npi}_annih` / `inActiveSubspace_pairParity_eq`. -/
theorem inActiveSubspace_of_conditions (P : ℕ) (v : NQubitKet (2 * P + 2))
    (h0 : numberOpK P 0 * v = 0) (hpi : numberOpK P Real.pi * v = 0)
    (hpar : ∀ m : Fin P, pairParity P (waveVectorABC P m) * v = v) :
    InActiveSubspace P v := by
  unfold InActiveSubspace activeProj
  -- the noncommProd fixes v: each activeFactor m fixes v.
  have hfac : ∀ m : Fin P, activeFactor P m * v = v := by
    intro m
    unfold activeFactor
    rw [smul_op_mul_ket, add_op_mul_ket, hpar m]
    ext i
    simp only [Ket.smul_vec, Ket.add_vec, op_mul_ket_vec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hprod : (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P) * v = v := by
    refine Finset.noncommProd_induction (K_ABC P) (activeFactor P)
      (activeFactor_pairwise_commute P) (fun O => O * v = v) ?_ ?_ ?_
    · intro a b ha hb; rw [op_mul_op_mul_ket, hb, ha]
    · ext i; simp [op_mul_ket_vec]
    · intro x _; exact hfac x
  -- (1 - n_0)(1 - n_π) · (noncommProd · v) = (1 - n_0)(1 - n_π) · v = v.
  rw [op_mul_op_mul_ket, hprod, op_mul_op_mul_ket]
  have hpiv : (1 - numberOpK P Real.pi) * v = v := by
    rw [sub_op_mul_ket, hpi]; ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]
  rw [hpiv, sub_op_mul_ket, h0]
  ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]

/-- `P_n = 2 S_n − 1` (pair-parity in terms of the pair-block square). -/
theorem pairParity_eq_two_Spair_sub_one (P : ℕ) (n : Fin P) :
    pairParity P (waveVectorABC P n) = (2 : ℂ) • Spair P n - 1 := by
  rw [Spair_eq_activeFactor, activeFactor]
  rw [smul_smul]
  rw [show (2 : ℂ) * (1 / 2 : ℂ) = 1 by ring, one_smul]
  abel

/-- `P_n · (û·τ⃗_{k_n}) = û·τ⃗_{k_n}` (same-mode pair parity is `+1` on the pair
pseudospin): from `P_n = 2 S_n − 1` and `S_n · A = A`. -/
theorem pairParity_mul_dotTau_self (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ) :
    pairParity P (waveVectorABC P n) * dotTau P (waveVectorABC P n) u
      = dotTau P (waveVectorABC P n) u := by
  rw [pairParity_eq_two_Spair_sub_one, sub_mul, smul_mul_assoc, Spair_mul_dotTau, one_mul]
  rw [two_smul]; abel

/-- **Per-mode active-subspace preservation.** For active `ψ`, the dotted pair
pseudospin `û·τ⃗_{k_n}·ψ` is again active: `n_{0,π}` commute across to annihilate it,
distinct-pair `P_m` commute across, and the same-pair `P_n` is `+1` on `û·τ⃗_{k_n}`. -/
theorem dotTau_preserves_inActiveSubspace (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ)
    (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (dotTau P (waveVectorABC P n) u * ψ) := by
  apply inActiveSubspace_of_conditions
  · -- n_0 · (A·ψ) = A·(n_0·ψ) = 0
    rw [← op_mul_op_mul_ket, (numberOpK_zero_commute_dotTau P n u).eq, op_mul_op_mul_ket,
      inActiveSubspace_n0_annih P ψ hψ]
    ext i
    rw [op_mul_ket_vec, show (0 : NQubitKet (2*P+2)).vec = 0 from rfl, Matrix.mulVec_zero]
  · rw [← op_mul_op_mul_ket, (numberOpK_pi_commute_dotTau P n u).eq, op_mul_op_mul_ket,
      inActiveSubspace_npi_annih P ψ hψ]
    ext i
    rw [op_mul_ket_vec, show (0 : NQubitKet (2*P+2)).vec = 0 from rfl, Matrix.mulVec_zero]
  · intro m
    by_cases hmn : m = n
    · subst hmn
      rw [← op_mul_op_mul_ket, pairParity_mul_dotTau_self]
    · rw [← op_mul_op_mul_ket, (pairParity_commute_dotTau_cross P m n hmn u).eq,
        op_mul_op_mul_ket, inActiveSubspace_pairParity_eq P m ψ hψ]

/-- `HredZMode k_n` preserves the active subspace (packaged for the cost
Hamiltonian: `HredZMode = −2·(b̂_n·τ⃗_n)`). -/
theorem HredZMode_preserves_inActiveSubspace (P : ℕ) (n : Fin P)
    (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (HredZMode P (waveVectorABC P n) * ψ) := by
  have heq : HredZMode P (waveVectorABC P n)
      = (-2 : ℂ) • dotTau P (waveVectorABC P n) (bHat (waveVectorABC P n)) :=
    HredZMode_eq_dotTau P n
  rw [heq, smul_op_mul_ket]
  have hbase := dotTau_preserves_inActiveSubspace P n (bHat (waveVectorABC P n)) ψ hψ
  unfold InActiveSubspace at hbase ⊢
  rw [op_mul_smul_ket, hbase]

-- ----------------------------------------------------------------------------
-- S1-onesided + S1-commute: `Hred_z_pm`/`Hred_x_op` preserve the active subspace,
-- giving the one-sided operator identity `Π·H·Π = H·Π`, then (with Hermiticity)
-- `Commute H Π`, then `Commute (exp(c•H)) Π` and per-layer preservation.
-- ----------------------------------------------------------------------------

/-- If each summand operator preserves the active subspace at `ψ`, so does their
finite sum (worked at the operator level to avoid a ket `AddCommMonoid`). -/
theorem inActiveSubspace_op_sum {P : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → NQubitOp (2 * P + 2)) (ψ : NQubitKet (2 * P + 2))
    (hf : ∀ i ∈ s, InActiveSubspace P (f i * ψ)) :
    InActiveSubspace P ((∑ i ∈ s, f i) * ψ) := by
  classical
  induction s using Finset.induction with
  | empty =>
      unfold InActiveSubspace
      rw [Finset.sum_empty]
      ext i; simp [op_mul_ket_vec]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, add_op_mul_ket]
      have ha' : InActiveSubspace P (f a * ψ) := hf a (Finset.mem_insert_self a s)
      have ih' : InActiveSubspace P ((∑ i ∈ s, f i) * ψ) :=
        ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      unfold InActiveSubspace at ha' ih' ⊢
      rw [Op_mul_add_ket, ha', ih']

/-- For active `ψ`, the constant-shifted cost `(Hred_z_pm + N_R·1)·ψ = Σ HredZMode·ψ`
is again active (the sum of per-mode preserved states). -/
theorem Hred_z_shifted_preserves_inActiveSubspace (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P
      ((UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • 1) * ψ) := by
  unfold InActiveSubspace
  rw [HredZDecomp_active P ψ hψ]
  exact inActiveSubspace_op_sum _ _ ψ
    (fun n _ => HredZMode_preserves_inActiveSubspace P n ψ hψ)

/-- The active subspace is closed under subtraction (it is a linear subspace). -/
theorem inActiveSubspace_sub {P : ℕ} (φ ξ : NQubitKet (2 * P + 2))
    (hφ : InActiveSubspace P φ) (hξ : InActiveSubspace P ξ) :
    InActiveSubspace P (φ - ξ) := by
  unfold InActiveSubspace at hφ hξ ⊢
  have hsub : activeProj P * (φ - ξ) = activeProj P * φ - activeProj P * ξ := by
    ext i; simp [op_mul_ket_vec]
  rw [hsub, hφ, hξ]

theorem inActiveSubspace_smul {P : ℕ} (c : ℂ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) : InActiveSubspace P (c • ψ) := by
  unfold InActiveSubspace at hψ ⊢
  rw [op_mul_smul_ket, hψ]

/-- For active `ψ`, `Hred_z_pm·ψ` is again active (subtract the scalar shift). -/
theorem Hred_z_pm_preserves_inActiveSubspace (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (UpperBound.Hred_z_pm false P * ψ) := by
  have hshift := Hred_z_shifted_preserves_inActiveSubspace P ψ hψ
  -- (Hred_z_pm + N_R·1)·ψ = Hred_z_pm·ψ + N_R·ψ, so Hred_z_pm·ψ = shifted − N_R·ψ.
  have honeψ : (1 : NQubitOp (2*P+2)) * ψ = ψ := by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]
  have hexpand : (UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • 1) * ψ
      = UpperBound.Hred_z_pm false P * ψ + ((2*P+2 : ℂ)) • ψ := by
    rw [add_op_mul_ket, smul_op_mul_ket, honeψ]
  have hsplit : UpperBound.Hred_z_pm false P * ψ
      = (UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • 1) * ψ
        - ((2*P+2 : ℂ)) • ψ := by
    rw [hexpand]; ext i; simp; ring
  rw [hsplit]
  exact inActiveSubspace_sub _ _ hshift (inActiveSubspace_smul _ _ hψ)

/-- `activeProj·w` is in the active subspace for ANY `w` (the assembled projector lands
in `A`): via the B2 operator absorption lemmas `numberOpK_{zero,npi}_mul_activeProj`
and `pairParity_mul_activeProj`. -/
theorem inActiveSubspace_activeProj_mul (P : ℕ) (w : NQubitKet (2 * P + 2)) :
    InActiveSubspace P (activeProj P * w) := by
  apply inActiveSubspace_of_conditions
  · rw [← op_mul_op_mul_ket, numberOpK_zero_mul_activeProj]
    ext i; simp [op_mul_ket_vec]
  · rw [← op_mul_op_mul_ket, numberOpK_npi_mul_activeProj]
    ext i; simp [op_mul_ket_vec]
  · intro m
    rw [← op_mul_op_mul_ket, pairParity_mul_activeProj]

/-- **S1-onesided (cost).** `Π·Hred_z_pm·Π = Hred_z_pm·Π` as operators: on any state,
`Π·w` is active, `Hred_z_pm` preserves active, so `Π` fixes it. -/
theorem activeProj_Hred_z_pm_activeProj (P : ℕ) :
    activeProj P * UpperBound.Hred_z_pm false P * activeProj P
      = UpperBound.Hred_z_pm false P * activeProj P := by
  apply op_eq_of_on_computationalBasis
  intro z
  -- Both sides applied to z: RHS = Hred_z_pm·(Π·z); LHS = Π·(Hred_z_pm·(Π·z)).
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, op_mul_op_mul_ket]
  -- Π·(Π·z) is active; Hred_z_pm preserves active; so Π fixes Hred_z_pm·(Π·z).
  have hact : InActiveSubspace P (activeProj P * computationalBasisKet (2*P+2) z) :=
    inActiveSubspace_activeProj_mul P _
  have hHact : InActiveSubspace P
      (UpperBound.Hred_z_pm false P * (activeProj P * computationalBasisKet (2*P+2) z)) :=
    Hred_z_pm_preserves_inActiveSubspace P _ hact
  unfold InActiveSubspace at hHact
  exact hHact

-- ----------------------------------------------------------------------------
-- S1-commute: Hermiticity of `activeProj` (+ `Hred_z_pm`) turns the one-sided
-- identity into the full operator commutator `Commute Hred_z_pm activeProj`.
-- ----------------------------------------------------------------------------

/-- `n_k` is Hermitian: `(c_k† c_k)† = c_k† c_k`. -/
theorem numberOpK_isHermitian (P : ℕ) (k : ℝ) :
    (numberOpK P k)† = numberOpK P k := by
  unfold numberOpK cCreateK
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- `pairParity_{k_n}` is Hermitian (product of two commuting Hermitian factors
`1 − 2 n_{±k_n}`). -/
theorem pairParity_isHermitian (P : ℕ) (n : Fin P) :
    (pairParity P (waveVectorABC P n))† = pairParity P (waveVectorABC P n) := by
  unfold pairParity
  rw [Matrix.conjTranspose_mul]
  have h1 : ((1 : NQubitOp (2*P+2)) - (2 : ℂ) • numberOpK P (waveVectorABC P n))†
      = 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      numberOpK_isHermitian]; simp
  have h2 : ((1 : NQubitOp (2*P+2)) - (2 : ℂ) • numberOpK P (-(waveVectorABC P n)))†
      = 1 - (2 : ℂ) • numberOpK P (-(waveVectorABC P n)) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.conjTranspose_smul,
      numberOpK_isHermitian]; simp
  rw [h1, h2]
  -- (AB)† gave (1-2n_{-k})(1-2n_k); reorder via the within-pair commute.
  exact ((commute_one_sub_two_smul (numberOpK_within_pair_commute P n)).symm).eq

/-- A `noncommProd` of pairwise-commuting Hermitian matrices is Hermitian. The
reversed product from the conjugate-transpose anti-homomorphism is reconciled by the
pairwise commutation (each newly-inserted factor commutes with the running product). -/
theorem noncommProd_isHermitian {α : Type*} {N : ℕ}
    (s : Finset α) (f : α → NQubitOp N)
    (comm : (↑s : Set α).Pairwise (Function.onFun Commute f))
    (hH : ∀ x ∈ s, (f x)† = f x) :
    (s.noncommProd f comm)† = s.noncommProd f comm := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.noncommProd_empty]; exact Matrix.conjTranspose_one
  | insert a s ha ih =>
      have comm_s : (↑s : Set α).Pairwise (Function.onFun Commute f) :=
        comm.mono (by simp)
      have hH_s : ∀ x ∈ s, (f x)† = f x := fun x hx => hH x (Finset.mem_insert_of_mem hx)
      rw [Finset.noncommProd_insert_of_notMem s a f comm ha, Matrix.conjTranspose_mul,
        ih comm_s hH_s, hH a (Finset.mem_insert_self a s)]
      -- (noncommProd_s) * (f a) = (f a) * (noncommProd_s) by commutation
      have hcomm : Commute (f a) (s.noncommProd f comm_s) := by
        refine Finset.noncommProd_commute s f comm_s (f a) ?_
        intro x hx
        exact comm (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hx)
          (fun h => ha (h ▸ hx))
      exact hcomm.symm.eq

/-- `activeFactor n` is Hermitian. -/
theorem activeFactor_isHermitian (P : ℕ) (n : Fin P) :
    (activeFactor P n)† = activeFactor P n := by
  unfold activeFactor
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    pairParity_isHermitian]
  simp

/-- The pair-parity noncommProd over `K_ABC` is Hermitian. -/
theorem noncommProd_activeFactor_isHermitian (P : ℕ) :
    ((K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P))†
      = (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P) :=
  noncommProd_isHermitian (K_ABC P) (activeFactor P) (activeFactor_pairwise_commute P)
    (fun x _ => activeFactor_isHermitian P x)

/-- `1 − n_0` is Hermitian. -/
theorem one_sub_numberOpK_isHermitian (P : ℕ) (k : ℝ) :
    ((1 : NQubitOp (2*P+2)) - numberOpK P k)† = 1 - numberOpK P k := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, numberOpK_isHermitian]

/-- `1 − n_0` commutes with each `activeFactor m`. -/
theorem one_sub_numberOpK_zero_commute_activeFactor (P : ℕ) (m : Fin P) :
    Commute ((1 : NQubitOp (2*P+2)) - numberOpK P 0) (activeFactor P m) := by
  unfold activeFactor
  refine Commute.sub_left (Commute.one_left _) ?_
  refine Commute.smul_right ?_ _
  exact (Commute.one_right _).add_right (numberOpK_zero_commute_pairParity P m)

set_option maxHeartbeats 4000000 in
-- Raised: reordering the three big operator factors triggers costly defeq.
/-- **S1-commute prerequisite.** `activeProj` is Hermitian (product of pairwise-commuting
Hermitian factors `(1−n_0)`, `(1−n_π)`, and the pair-parity noncommProd). -/
theorem activeProj_isHermitian (P : ℕ) :
    (activeProj P)† = activeProj P := by
  unfold activeProj
  set A := (1 : NQubitOp (2*P+2)) - numberOpK P 0 with hA
  set B := (1 : NQubitOp (2*P+2)) - numberOpK P Real.pi with hB
  set C := (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P) with hC
  have hAH : A† = A := one_sub_numberOpK_isHermitian P 0
  have hBH : B† = B := one_sub_numberOpK_isHermitian P Real.pi
  have hCH : C† = C := noncommProd_activeFactor_isHermitian P
  have hAB : Commute A B := by
    rw [hA, hB]
    exact Commute.sub_left (Commute.one_left _)
      (Commute.sub_right (Commute.one_right _) (numberOpK_zero_commute_npi P))
  have hAC : Commute A C := by
    rw [hC]
    refine Finset.noncommProd_commute _ _ _ _ (fun x _ => ?_)
    exact one_sub_numberOpK_zero_commute_activeFactor P x
  have hBC : Commute B C := by
    rw [hB, hC]
    refine Finset.noncommProd_commute _ _ _ _ (fun x _ => ?_)
    unfold activeFactor
    refine Commute.sub_left (Commute.one_left _) (Commute.smul_right ?_ _)
    exact (Commute.one_right _).add_right (numberOpK_pi_commute_pairParity P x)
  -- The conjTranspose reorder, proven abstractly on the atoms A, B, C.
  have hreorder : (A * B * C)† = A * B * C := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hAH, hBH, hCH]
    -- goal: C * (B * A) = A * B * C
    calc C * (B * A) = (C * B) * A := by rw [mul_assoc]
      _ = (B * C) * A := by rw [hBC.eq]
      _ = B * (C * A) := by rw [mul_assoc]
      _ = B * (A * C) := by rw [hAC.eq]
      _ = (B * A) * C := by rw [mul_assoc]
      _ = (A * B) * C := by rw [hAB.eq]
  exact hreorder

/-- `Hred_z_pm false P` is Hermitian (it is the underlying op of the Hermitian
packaging `Hred_z_hamiltonian false P`). -/
theorem Hred_z_pm_isHermitian (P : ℕ) :
    (UpperBound.Hred_z_pm false P)† = UpperBound.Hred_z_pm false P := by
  have h := (UpperBound.Hred_z_hamiltonian false P).isHermitian
  rw [UpperBound.Hred_z_hamiltonian_toOp] at h
  exact h

/-- **S1-commute (cost).** `Commute (Hred_z_pm) (activeProj)`: the one-sided identity
`Π·H·Π = H·Π`, daggered with both operators Hermitian, yields `Π·H·Π = Π·H`; chaining
the two gives `H·Π = Π·H`. -/
theorem Hred_z_pm_commute_activeProj (P : ℕ) :
    Commute (UpperBound.Hred_z_pm false P) (activeProj P) := by
  have honesided := activeProj_Hred_z_pm_activeProj P
  -- dagger the one-sided identity
  have hdag : (activeProj P * UpperBound.Hred_z_pm false P * activeProj P)†
      = (UpperBound.Hred_z_pm false P * activeProj P)† := by rw [honesided]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    activeProj_isHermitian, Hred_z_pm_isHermitian,
    Matrix.conjTranspose_mul, activeProj_isHermitian, Hred_z_pm_isHermitian] at hdag
  -- hdag : Π * (H * Π) = Π * H   (after reassoc)
  -- honesided : Π * H * Π = H * Π
  unfold Commute SemiconjBy
  -- H * Π = Π * H
  calc UpperBound.Hred_z_pm false P * activeProj P
      = activeProj P * UpperBound.Hred_z_pm false P * activeProj P := honesided.symm
    _ = activeProj P * UpperBound.Hred_z_pm false P := by
        rw [mul_assoc]; exact hdag

/-- `Commute (costExponential (Hred_z_hamiltonian false P) γ) (activeProj P)`. -/
theorem costExponential_commute_activeProj (P : ℕ) (γ : ℝ) :
    Commute (costExponential (UpperBound.Hred_z_hamiltonian false P) γ) (activeProj P) := by
  unfold costExponential
  rw [UpperBound.Hred_z_hamiltonian_toOp]
  exact Commute.exp_left ((Hred_z_pm_commute_activeProj P).smul_left _)

-- ---- Mixer analogue (S1-commute, mixer) ----

/-- `HredXMode k_n` preserves the active subspace (`HredXMode = −2·(ẑ·τ⃗_n)`). -/
theorem HredXMode_preserves_inActiveSubspace (P : ℕ) (n : Fin P)
    (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (HredXMode P (waveVectorABC P n) * ψ) := by
  have heq : HredXMode P (waveVectorABC P n) = (-2 : ℂ) • dotTau P (waveVectorABC P n) zHat :=
    HredXMode_eq_dotTau P n
  rw [heq, smul_op_mul_ket]
  have hbase := dotTau_preserves_inActiveSubspace P n zHat ψ hψ
  unfold InActiveSubspace at hbase ⊢
  rw [op_mul_smul_ket, hbase]

/-- For active `ψ`, `Hred_x_op·ψ` is again active. -/
theorem Hred_x_op_preserves_inActiveSubspace (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (UpperBound.Hred_x_op P * ψ) := by
  have hshift : InActiveSubspace P ((UpperBound.Hred_x_op P + (2 : ℂ) • 1) * ψ) := by
    unfold InActiveSubspace
    rw [HredXDecomp_active P ψ hψ]
    exact inActiveSubspace_op_sum _ _ ψ
      (fun n _ => HredXMode_preserves_inActiveSubspace P n ψ hψ)
  have honeψ : (1 : NQubitOp (2*P+2)) * ψ = ψ := by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]
  have hexpand : (UpperBound.Hred_x_op P + (2 : ℂ) • 1) * ψ
      = UpperBound.Hred_x_op P * ψ + (2 : ℂ) • ψ := by
    rw [add_op_mul_ket, smul_op_mul_ket, honeψ]
  have hsplit : UpperBound.Hred_x_op P * ψ
      = (UpperBound.Hred_x_op P + (2 : ℂ) • 1) * ψ - (2 : ℂ) • ψ := by
    rw [hexpand]; ext i; simp
  rw [hsplit]
  exact inActiveSubspace_sub _ _ hshift (inActiveSubspace_smul _ _ hψ)

/-- One-sided identity for the mixer: `Π·Hred_x·Π = Hred_x·Π`. -/
theorem activeProj_Hred_x_op_activeProj (P : ℕ) :
    activeProj P * UpperBound.Hred_x_op P * activeProj P
      = UpperBound.Hred_x_op P * activeProj P := by
  apply op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, op_mul_op_mul_ket]
  have hact : InActiveSubspace P (activeProj P * computationalBasisKet (2*P+2) z) :=
    inActiveSubspace_activeProj_mul P _
  have hHact : InActiveSubspace P
      (UpperBound.Hred_x_op P * (activeProj P * computationalBasisKet (2*P+2) z)) :=
    Hred_x_op_preserves_inActiveSubspace P _ hact
  unfold InActiveSubspace at hHact
  exact hHact

/-- `Hred_x_op` is Hermitian. -/
theorem Hred_x_op_isHermitian (P : ℕ) :
    (UpperBound.Hred_x_op P)† = UpperBound.Hred_x_op P := by
  have h := (UpperBound.Hred_x_hamiltonian P).isHermitian
  rw [UpperBound.Hred_x_hamiltonian_toOp] at h
  exact h

/-- **S1-commute (mixer).** `Commute (Hred_x_op) (activeProj)`. -/
theorem Hred_x_op_commute_activeProj (P : ℕ) :
    Commute (UpperBound.Hred_x_op P) (activeProj P) := by
  have honesided := activeProj_Hred_x_op_activeProj P
  have hdag : (activeProj P * UpperBound.Hred_x_op P * activeProj P)†
      = (UpperBound.Hred_x_op P * activeProj P)† := by rw [honesided]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    activeProj_isHermitian, Hred_x_op_isHermitian,
    Matrix.conjTranspose_mul, activeProj_isHermitian, Hred_x_op_isHermitian] at hdag
  unfold Commute SemiconjBy
  calc UpperBound.Hred_x_op P * activeProj P
      = activeProj P * UpperBound.Hred_x_op P * activeProj P := honesided.symm
    _ = activeProj P * UpperBound.Hred_x_op P := by rw [mul_assoc]; exact hdag

/-- `Commute (mixerExponential (Hred_x_hamiltonian P) β) (activeProj P)`. -/
theorem mixerExponential_commute_activeProj (P : ℕ) (β : ℝ) :
    Commute (mixerExponential (UpperBound.Hred_x_hamiltonian P) β) (activeProj P) := by
  unfold mixerExponential
  rw [UpperBound.Hred_x_hamiltonian_toOp]
  exact Commute.exp_left ((Hred_x_op_commute_activeProj P).smul_left _)

-- ----------------------------------------------------------------------------
-- Depth induction (generalized over ψ0) + uniform-state base case ⟹ active-subspace preservation.
-- ----------------------------------------------------------------------------

/-- An operator that commutes with `activeProj` preserves the active subspace. -/
theorem inActiveSubspace_of_commute_activeProj (P : ℕ) (M : NQubitOp (2 * P + 2))
    (hM : Commute M (activeProj P)) (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    InActiveSubspace P (M * ψ) := by
  unfold InActiveSubspace at hψ ⊢
  rw [← op_mul_op_mul_ket, ← hM.eq, op_mul_op_mul_ket, hψ]

/-- `(U * ψ : Ket) = U.toOp * ψ` (the unitary action equals operator-ket mul). -/
theorem unitaryOp_mul_ket_eq_op {n : ℕ} (U : Quantum.Operators.UnitaryOp n)
    (ψ : Quantum.Operators.Ket n) :
    (U * ψ : Quantum.Operators.Ket n) = U.toOp * ψ := by
  ext i; rw [UnitaryOp_mul_ket_vec, op_mul_ket_vec]

/-- One QAOA cost+mixer layer of the reduced chain preserves the active subspace. -/
theorem applyLayer_preserves_inActiveSubspace (P : ℕ) (γ β : ℝ)
    (ψ0 : Qubits.NQubitNormKet (2 * P + 2)) (hψ0 : InActiveSubspace P ψ0.toKet) :
    InActiveSubspace P
      (applyLayer ((UpperBound.reducedChainQAOAExp false P).costUnitary γ)
        ((UpperBound.reducedChainQAOAExp false P).mixerUnitary β) ψ0).toKet := by
  rw [applyLayer_toKet, unitaryOp_mul_ket_eq_op, unitaryOp_mul_ket_eq_op]
  -- mixer · (cost · ψ0); cost = costExponential, mixer = mixerExponential
  have hcost : ((UpperBound.reducedChainQAOAExp false P).costUnitary γ : NQubitOp (2*P+2))
      = costExponential (UpperBound.Hred_z_hamiltonian false P) γ :=
    (UpperBound.reducedChainQAOAExp false P).costUnitary_spec γ
  have hmix : ((UpperBound.reducedChainQAOAExp false P).mixerUnitary β : NQubitOp (2*P+2))
      = mixerExponential (UpperBound.Hred_x_hamiltonian P) β :=
    (UpperBound.reducedChainQAOAExp false P).mixerUnitary_spec β
  rw [hcost, hmix]
  apply inActiveSubspace_of_commute_activeProj P _ (mixerExponential_commute_activeProj P β)
  apply inActiveSubspace_of_commute_activeProj P _ (costExponential_commute_activeProj P γ)
  exact hψ0

/-- Depth induction (generalized over the initial state): if `ψ0` is active then the
depth-`p` reduced QAOA state on `ψ0` is active. Mirrors the upper-bound's
`Ttilde_op_apply_genReducedQAOA` on the PUBLIC `qaoaState` API. -/
theorem reducedQAOA_preserves_inActiveSubspace (P : ℕ) :
    ∀ p : ℕ, ∀ γ β : Fin p → ℝ, ∀ ψ0 : Qubits.NQubitNormKet (2*P+2),
      InActiveSubspace P ψ0.toKet →
      InActiveSubspace P
        (qaoaState (costUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians γ)
          (mixerUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians β) ψ0).toKet := by
  intro p
  induction p with
  | zero =>
      intro γ β ψ0 hψ0
      -- qaoaState at depth 0 is ψ0 by the `qaoaStateAux` base case (any Fin 0 family).
      change InActiveSubspace P (qaoaStateAux 0 _ _ ψ0).toKet
      exact hψ0
  | succ p IH =>
      intro γ β ψ0 hψ0
      rw [qaoaState_succ]
      apply IH
      -- the first layer preserves active
      have hlayer := applyLayer_preserves_inActiveSubspace P (γ 0) (β 0) ψ0 hψ0
      -- costUnitaryFamily ... 0 = costUnitary (γ 0); same for mixer
      exact hlayer

-- ----------------------------------------------------------------------------
-- Site-local Fourier cancellation `cAnnih j · |+⟩^{⊗N} = 0`.
-- ----------------------------------------------------------------------------

/-- The uniform ket equals the constant `1/√D` over the basis-ket sum:
`|+⟩^{⊗N} = (1/√D) Σ_z |z⟩`. -/
theorem uniformKet_eq_sum_basis (N : ℕ) :
    (uniformKet (Qubits.NQubitDim N)).vec
      = ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ) •
        ∑ z : Qubits.BitString N, (computationalBasisKet N z).vec := by
  funext i
  rw [Pi.smul_apply, smul_eq_mul]
  change ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ)
    = ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ) *
      (∑ z : Qubits.BitString N, (computationalBasisKet N z).vec) i
  rw [Finset.sum_apply i Finset.univ (fun z => (computationalBasisKet N z).vec)]
  have hone : (∑ z : Qubits.BitString N, (computationalBasisKet N z).vec i) = 1 := by
    rw [Finset.sum_eq_single ((Qubits.bitStringEquiv N).symm i)]
    · unfold computationalBasisKet
      rw [stdKet_apply, if_pos ((Qubits.bitStringEquiv N).apply_symm_apply i)]
    · intro b _ hb
      unfold computationalBasisKet
      rw [stdKet_apply, if_neg]
      intro hi; apply hb
      apply (Qubits.bitStringEquiv N).injective
      rw [(Qubits.bitStringEquiv N).apply_symm_apply, hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hone, mul_one]

/-- The bit-flip at site `j` as an involutive bijection of bitstrings. -/
def flipBitAtEquiv (N : ℕ) (j : Fin N) : Qubits.BitString N ≃ Qubits.BitString N where
  toFun z := Qubits.flipBitAt z j
  invFun z := Qubits.flipBitAt z j
  left_inv z := Qubits.flipBitAt_involutive z j
  right_inv z := Qubits.flipBitAt_involutive z j

/-- `Z_j · |+⟩^{⊗N} = i · (Y_j · |+⟩^{⊗N})`: the diagonal `Z`-phase equals the
`i`-scaled off-diagonal `Y`-phase after the bit-flip reindexing at site `j`. -/
theorem localPauliZ_mulVec_uniformKet_eq {N : ℕ} (j : Fin N) :
    (Qubits.localPauliZ j) * (uniformKet (Qubits.NQubitDim N))
      = Complex.I • ((Qubits.localPauliY j) * (uniformKet (Qubits.NQubitDim N))) := by
  apply Quantum.Operators.Ket.ext
  set c := ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ) with hc
  have hZ : (Qubits.localPauliZ j * uniformKet (Qubits.NQubitDim N)).vec
      = c • ∑ z : Qubits.BitString N,
          (Qubits.localPauliZ j * computationalBasisKet N z).vec := by
    rw [op_mul_ket_vec, uniformKet_eq_sum_basis, Matrix.mulVec_smul]
    congr 1
    rw [Matrix.mulVec_sum]; rfl
  have hY : (Qubits.localPauliY j * uniformKet (Qubits.NQubitDim N)).vec
      = c • ∑ z : Qubits.BitString N,
          (Qubits.localPauliY j * computationalBasisKet N z).vec := by
    rw [op_mul_ket_vec, uniformKet_eq_sum_basis, Matrix.mulVec_smul]
    congr 1
    rw [Matrix.mulVec_sum]; rfl
  have hsum : (∑ z : Qubits.BitString N, (Qubits.localPauliZ j * computationalBasisKet N z).vec)
      = Complex.I • ∑ z : Qubits.BitString N,
          (Qubits.localPauliY j * computationalBasisKet N z).vec := by
    rw [Finset.smul_sum]
    rw [← Equiv.sum_comp (flipBitAtEquiv N j)
        (fun z => Complex.I • (Qubits.localPauliY j * computationalBasisKet N z).vec)]
    refine Finset.sum_congr rfl (fun z _ => ?_)
    rw [Qubits.localPauliZ_on_basis]
    change (Z (z j) (z j)) • (computationalBasisKet N z).vec
      = Complex.I • (Qubits.localPauliY j *
          computationalBasisKet N (Qubits.flipBitAt z j)).vec
    rw [Qubits.localPauliY_on_basis, Qubits.flipBitAt_involutive, Qubits.flipBitAt_apply_same]
    rw [Quantum.Operators.Ket.smul_vec, smul_smul]
    have hcoef : Z (z j) (z j) = Complex.I * pauliYPhase (Qubits.flipBit (z j)) := by
      set b := z j with hb; clear_value b
      fin_cases b <;>
        simp [pauliZ, pauliYPhase, Qubits.flipBit_zero, Qubits.flipBit_one, Complex.I_mul_I]
    rw [hcoef]
  intro i
  show (Qubits.localPauliZ j * uniformKet (Qubits.NQubitDim N)).vec i
    = (Complex.I • (Qubits.localPauliY j * uniformKet (Qubits.NQubitDim N))).vec i
  rw [hZ, Quantum.Operators.Ket.smul_vec, hY, hsum]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **U1.** Each position-space fermion annihilates the uniform state:
`cAnnih j · |+⟩^{⊗N} = 0` (its local factor `(Z_j − i Y_j)/2` does). -/
theorem cAnnih_mulVec_uniformKet {N : ℕ} (j : Fin N) :
    cAnnih j * (uniformKet (Qubits.NQubitDim N)) = 0 := by
  unfold cAnnih
  rw [op_mul_op_mul_ket]
  have hloc : ((1/2 : ℂ) • (Qubits.localPauliZ j - Complex.I • Qubits.localPauliY j))
        * (uniformKet (Qubits.NQubitDim N)) = 0 := by
    rw [smul_op_mul_ket, sub_op_mul_ket, smul_op_mul_ket]
    rw [localPauliZ_mulVec_uniformKet_eq]
    apply Quantum.Operators.Ket.ext
    intro i; simp
  rw [hloc]
  ext i
  rw [op_mul_ket_vec, show (0 : NQubitKet N).vec = 0 from rfl, Matrix.mulVec_zero]

/-- **U1 (momentum form).** `cAnnihK k · |+⟩^{⊗N} = 0`, a Fourier sum of the site-local
zeros `cAnnih j · |+⟩^{⊗N} = 0`. -/
theorem cAnnihK_mulVec_uniformKet (P : ℕ) (k : ℝ) :
    cAnnihK P k * (uniformKet (Qubits.NQubitDim (2*P+2))) = 0 := by
  unfold cAnnihK
  rw [smul_op_mul_ket]
  rw [show (∑ j : Fin (2*P+2),
        (Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j))
          * (uniformKet (Qubits.NQubitDim (2*P+2))) = 0 by
    apply Quantum.Operators.Ket.ext
    intro i
    rw [sum_op_mul_ket_vec]
    apply Finset.sum_eq_zero
    intro j _
    rw [smul_op_mul_ket, cAnnih_mulVec_uniformKet]
    simp]
  ext i; simp

/-- `numberOpK k · |+⟩^{⊗N} = 0` (from `cAnnihK k · |+⟩ = 0`). -/
theorem numberOpK_mulVec_uniformKet (P : ℕ) (k : ℝ) :
    numberOpK P k * (uniformKet (Qubits.NQubitDim (2*P+2))) = 0 := by
  unfold numberOpK
  rw [op_mul_op_mul_ket, cAnnihK_mulVec_uniformKet]
  ext i
  rw [op_mul_ket_vec, show (0 : NQubitKet (2*P+2)).vec = 0 from rfl, Matrix.mulVec_zero]

/-- `(1 − 2 n_k) · |+⟩^{⊗N} = |+⟩^{⊗N}`. -/
theorem one_sub_two_numberOpK_mulVec_uniformKet (P : ℕ) (k : ℝ) :
    (1 - (2 : ℂ) • numberOpK P k) * (uniformKet (Qubits.NQubitDim (2*P+2)))
      = uniformKet (Qubits.NQubitDim (2*P+2)) := by
  rw [sub_op_mul_ket, smul_op_mul_ket, numberOpK_mulVec_uniformKet]
  rw [show ((2 : ℂ) • (0 : NQubitKet (2*P+2))) = 0 by ext i; simp]
  ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]

/-- (Base case) The uniform initial state `|+⟩^{⊗N_R}` lies in the active subspace.
CLOSED via U1 (`cAnnihK · |+⟩ = 0` ⟹ `n_k · |+⟩ = 0` ⟹ `P_k · |+⟩ = |+⟩`). -/
theorem inActiveSubspace_uniformState (P : ℕ) :
    InActiveSubspace P (uniformState (IsingChainQAOADim (2*P+2))).toKet := by
  change InActiveSubspace P (uniformKet (Qubits.NQubitDim (2*P+2)))
  apply inActiveSubspace_of_conditions
  · exact numberOpK_mulVec_uniformKet P 0
  · exact numberOpK_mulVec_uniformKet P Real.pi
  · intro m
    -- pairParity_m · uniform = (1-2n_k)·((1-2n_{-k})·uniform) = uniform.
    unfold pairParity
    rw [op_mul_op_mul_ket, one_sub_two_numberOpK_mulVec_uniformKet,
      one_sub_two_numberOpK_mulVec_uniformKet]

/-- The QAOA-evolved reduced state lies in the active subspace.

Reduces to the base case (`inActiveSubspace_uniformState`): the depth induction
`reducedQAOA_preserves_inActiveSubspace` propagates active-subspace membership through
every QAOA layer (each cost/mixer exponential commutes with `activeProj`), seeded by the
base case. `psiTilde false P γ (−β)` is exactly the depth-`P` reduced QAOA
state on `uniformState`, by `rfl`. -/
theorem psiTilde_inActiveSubspace {P : ℕ} (γ β : Fin P → ℝ) :
    InActiveSubspace P (UpperBound.psiTilde false P γ (-β)).toKet := by
  have hbase : InActiveSubspace P (UpperBound.psiTilde_init P).toKet :=
    inActiveSubspace_uniformState P
  exact reducedQAOA_preserves_inActiveSubspace P P γ (fun i => -(β i))
    (UpperBound.psiTilde_init P) hbase

end

end QAOA.IsingChain.JordanWigner
