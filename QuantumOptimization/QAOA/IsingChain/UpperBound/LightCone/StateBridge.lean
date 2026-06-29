import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.StructuralIdentification
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ReducedBondInvariance
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAObservables
import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain

/-!
# State Bridge — Heisenberg ↔ Schrödinger for the QAOA conjugation

This file builds the **state bridge** that connects the abstract operator
recursion `qaoaConjugate` (Heisenberg picture) to the physical QAOA *states*
(Schrödinger picture). The load-bearing fact is the operator-level identity

```
  qaoaConjugate P (γ∘rev) (β∘rev) O  =  U_state† · O · U_state
```

where `U_state` is the explicit QAOA unitary built from the SAME `exp` cost/
mixer factors as the state definition (`qaoaState`/`standardExponentialQAOAState`).
Both sides are products of the standard cost exponential
`exp(-iγ · Σ_k chainPairInteraction k)` and the standard mixer exponential
`exp(-iβ · standardMixerOp)`; the angle reversal `Fin.rev` accounts for the
fact that `qaoaConjugate`'s recursion peels `Fin.last` as the *outermost*
conjugation while `qaoaState`'s recursion applies layer `0` *first* (innermost).

## Main results

* `sandwich_conj_mulVec` — the elementary sandwich identity at the matrix
  `dotProduct`/`mulVec` level: `⟨Uψ|O|Uψ⟩ = ⟨ψ|U†OU|ψ⟩`.
* `qaoaStateUnitary` — the explicit state-building unitary operator (a product
  of `mixerExponential`/`costExponential` factors).
* `qaoaState_toKet_eq_qaoaStateUnitary` — `(qaoaState …).toKet = U_state · ψ0`.
* `qaoaConjugate_eq_qaoaStateUnitary_conj` — the **state bridge**:
  `qaoaConjugate P (γ∘rev) (β∘rev) O = U_state† · O · U_state`.

These are generic in the cost generator `C` and mixer generator `B`; the full-
and reduced-chain consumers specialize `C, B` to the chain cost/mixer.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: the elementary sandwich identity
-- ============================================================================

/-- **Sandwich identity (matrix level).** For an operator `O`, a unitary-shaped
operator `U` and a ket vector `v`, the expectation of `O` in the state `U·v`
equals the expectation of `U†·O·U` in the state `v`:
`star(U·v) ⬝ (O · (U·v)) = star v ⬝ ((U†·O·U) · v)`. No unitarity of `U` is
needed — this is pure adjoint bookkeeping. -/
theorem sandwich_conj_mulVec {n : ℕ} (O U : Op n)
    (v : Fin n → ℂ) :
    dotProduct (star (Matrix.mulVec U v))
        (Matrix.mulVec O (Matrix.mulVec U v)) =
      dotProduct (star v)
        (Matrix.mulVec (U† * O * U) v) := by
  -- Work on the LHS: `star (U v) ⬝ (O (U v))`.
  -- First rewrite `star (U v) = star v ᵥ* U†`.
  rw [Matrix.star_mulVec]
  -- Goal: (star v ᵥ* U†) ⬝ᵥ (O *ᵥ (U *ᵥ v)) = star v ⬝ᵥ ((U† * O * U) *ᵥ v).
  -- Convert the vecMul back to a mulVec via `← dotProduct_mulVec`.
  rw [← Matrix.dotProduct_mulVec]
  -- Goal: star v ⬝ᵥ (U† *ᵥ (O *ᵥ (U *ᵥ v))) = star v ⬝ᵥ ((U† * O * U) *ᵥ v).
  congr 1
  -- Collapse the nested `mulVec`s into a single matrix product.
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_assoc]

-- ============================================================================
-- Section: the explicit state-building unitary
-- ============================================================================

/-- A single QAOA layer operator: `mixerExp(β) · costExp(γ)` with
`costExp(γ) = exp(-iγ · C)` and `mixerExp(β) = exp(-iβ · B)`. -/
def layerOp {n : ℕ} (C B : Op n) (γ β : ℝ) : Op n :=
  NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • B) *
    NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) • C)

/-- The explicit QAOA state-building unitary operator at depth `P`, for a cost
generator `C` and mixer generator `B` (as plain operators), built from the same
`exp` factors as the QAOA state recursion `qaoaState`.

`qaoaStateUnitary` mirrors `qaoaState`'s recursion: layer `0` is applied *first*
(innermost, rightmost), and the tail (layers `1..P`) composes on the left:
`U_{P+1}(γ,β) = U_P(tail γ, tail β) · layerOp (γ 0) (β 0)`. -/
def qaoaStateUnitary {n : ℕ} (C B : Op n) (P : ℕ) (γ β : Fin P → ℝ) :
    Op n :=
  match P, γ, β with
  | 0, _, _ => (1 : Op n)
  | P + 1, γ, β =>
      (qaoaStateUnitary C B P (QAOA.tailFamily γ) (QAOA.tailFamily β)) *
        layerOp C B (γ 0) (β 0)

@[simp] theorem qaoaStateUnitary_zero {n : ℕ} (C B : Op n)
    (γ β : Fin 0 → ℝ) : qaoaStateUnitary C B 0 γ β = (1 : Op n) := rfl

theorem qaoaStateUnitary_succ {n : ℕ} (C B : Op n) (P : ℕ)
    (γ β : Fin (P + 1) → ℝ) :
    qaoaStateUnitary C B (P + 1) γ β =
      (qaoaStateUnitary C B P (QAOA.tailFamily γ) (QAOA.tailFamily β)) *
        layerOp C B (γ 0) (β 0) := rfl

-- ============================================================================
-- Section: state-unitary realizes the exponential QAOA state
-- ============================================================================

/-- **The QAOA state is the state unitary applied to the initial state.** For an
exponential QAOA package `Hpkg`, the underlying ket of the depth-`P`
`exponentialQAOAState` equals `qaoaStateUnitary` (built from the SAME exp
factors) applied to the initial state's vector. -/
theorem exponentialQAOAState_toKet_vec {n P : ℕ} (Hpkg : QAOAExponentials n)
    (γ β : Fin P → ℝ) (ψ0 : NormKet n) :
    (QAOA.exponentialQAOAState Hpkg γ β ψ0).toKet.vec =
      Matrix.mulVec
        (qaoaStateUnitary (Hpkg.costHamiltonian : Op n)
          (Hpkg.mixerHamiltonian : Op n) P γ β) ψ0.toKet.vec := by
  induction P generalizing ψ0 with
  | zero =>
    -- depth 0: state is ψ0, unitary is 1.
    rw [qaoaStateUnitary_zero, Matrix.one_mulVec]
    rfl
  | succ P ih =>
    -- Unfold one layer of the QAOA recursion.
    show (QAOA.qaoaState (QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians γ)
          (QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians β) ψ0).toKet.vec = _
    rw [QAOA.qaoaState_succ]
    -- The tail families are the families of the tail angle arrays.
    have htailC : QAOA.tailFamily (QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians γ) =
        QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians (QAOA.tailFamily γ) := rfl
    have htailB : QAOA.tailFamily (QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians β) =
        QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians (QAOA.tailFamily β) := rfl
    rw [htailC, htailB]
    -- Name the new initial state.
    set ψ1 : NormKet n :=
      QAOA.applyLayer (QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians γ 0)
        (QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians β 0) ψ0 with hψ1
    -- Apply IH to ψ1 (the depth-P state on the new initial state).
    rw [show (QAOA.qaoaState (QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians (QAOA.tailFamily γ))
          (QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians (QAOA.tailFamily β)) ψ1) =
        QAOA.exponentialQAOAState Hpkg (QAOA.tailFamily γ) (QAOA.tailFamily β) ψ1 from rfl]
    rw [ih (QAOA.tailFamily γ) (QAOA.tailFamily β) ψ1]
    -- Now rewrite the inner applyLayer at the vector level.
    rw [qaoaStateUnitary_succ]
    -- applyLayer's ket: mixer *ᵥ (cost *ᵥ ψ0.vec).
    have happly : ψ1.toKet.vec =
        Matrix.mulVec (layerOp (Hpkg.costHamiltonian : Op n)
          (Hpkg.mixerHamiltonian : Op n) (γ 0) (β 0)) ψ0.toKet.vec := by
      rw [hψ1, layerOp, ← Matrix.mulVec_mulVec]
      show Matrix.mulVec
          (QAOA.mixerUnitaryFamily Hpkg.toQAOAHamiltonians β 0 : Op n)
          (Matrix.mulVec
            (QAOA.costUnitaryFamily Hpkg.toQAOAHamiltonians γ 0 : Op n) ψ0.toKet.vec) = _
      rw [QAOA.costUnitaryFamily_apply, QAOA.mixerUnitaryFamily_apply,
          QAOA.mixerUnitary_eq_mixerExponential, QAOA.costUnitary_eq_costExponential]
      unfold QAOA.mixerExponential QAOA.costExponential
      norm_num
    rw [happly, Matrix.mulVec_mulVec]

-- ============================================================================
-- Section: generic conjugation recursion (mirror of `qaoaConjugate`)
-- ============================================================================

/-- Generic version of `qaoaConjugate` with arbitrary cost generator `C` and
mixer generator `B`. Mirrors the `FGGClosure.qaoaConjugate` recursion exactly,
peeling `Fin.last` as the outermost conjugation: the left factors are
`exp(γ_last·iC)·exp(β_last·iB)`, the right factors `exp(-iβ_last·B)·exp(-iγ_last·C)`. -/
def genConjTwo {n : ℕ} (C B : Op n) (P : ℕ) (g b : Fin P → ℝ) (O : Op n) :
    Op n :=
  match P, g, b with
  | 0, _, _ => O
  | P + 1, g, b =>
      (NormedSpace.exp (((g (Fin.last P) : ℝ) * Complex.I : ℂ) • C) *
        NormedSpace.exp (((b (Fin.last P) : ℝ) * Complex.I : ℂ) • B)) *
       (genConjTwo C B P (fun i => g i.castSucc) (fun i => b i.castSucc) O) *
       (NormedSpace.exp ((((-b (Fin.last P) : ℝ) * Complex.I : ℂ)) • B) *
        NormedSpace.exp ((((-g (Fin.last P) : ℝ) * Complex.I : ℂ)) • C))

theorem genConjTwo_zero {n : ℕ} (C B : Op n) (g b : Fin 0 → ℝ) (O : Op n) :
    genConjTwo C B 0 g b O = O := rfl

theorem genConjTwo_succ {n : ℕ} (C B : Op n) (P : ℕ) (g b : Fin (P + 1) → ℝ)
    (O : Op n) :
    genConjTwo C B (P + 1) g b O =
      (NormedSpace.exp (((g (Fin.last P) : ℝ) * Complex.I : ℂ) • C) *
        NormedSpace.exp (((b (Fin.last P) : ℝ) * Complex.I : ℂ) • B)) *
       (genConjTwo C B P (fun i => g i.castSucc) (fun i => b i.castSucc) O) *
       (NormedSpace.exp ((((-b (Fin.last P) : ℝ) * Complex.I : ℂ)) • B) *
        NormedSpace.exp ((((-g (Fin.last P) : ℝ) * Complex.I : ℂ)) • C)) := rfl

/-- `qaoaConjugate` is `genConjTwo` for the chain generators
`C = Σ_k chainPairInteraction k` and `B = standardMixerOp N`. -/
theorem qaoaConjugate_eq_genConjTwo {N : ℕ} (O : Qubits.NQubitOp N) :
    ∀ (P : ℕ) (g b : Fin P → ℝ),
      qaoaConjugate P g b O =
        genConjTwo (∑ k : Fin N, IsingModel.chainPairInteraction k)
          (QAOA.standardMixerOp N) P g b O := by
  intro P
  induction P with
  | zero => intro g b; rfl
  | succ P ih =>
    intro g b
    -- Unfold one layer of `qaoaConjugate` (it normalizes `-(-θ)` to `θ`).
    show (NormedSpace.exp ((((-(-g (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
          NormedSpace.exp ((((-(-b (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
            QAOA.standardMixerOp N)) *
         qaoaConjugate P (fun i => g i.castSucc) (fun i => b i.castSucc) O *
         (NormedSpace.exp ((((-b (Fin.last P) : ℝ) * Complex.I : ℂ)) •
            QAOA.standardMixerOp N) *
          NormedSpace.exp ((((-g (Fin.last P) : ℝ) * Complex.I : ℂ)) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k))) = _
    rw [genConjTwo_succ, ih (fun i => g i.castSucc) (fun i => b i.castSucc)]
    -- Both sides now agree up to the `neg_neg` normalization in the left factors.
    simp only [neg_neg]

-- ============================================================================
-- Section: adjoint of a layer; the state bridge
-- ============================================================================

/-- The conjugate transpose of a single layer, for Hermitian generators `C, B`:
`(mixerExp(β) · costExp(γ))† = costExp(-γ)' · mixerExp(-β)'`, i.e. it equals the
"primed" factors `exp(iγ C) · exp(iβ B)` that appear on the left of
`qaoaConjugate`'s recursion. -/
theorem layerOp_conjTranspose {n : ℕ} {C B : Op n}
    (hC : C† = C) (hB : B† = B) (γ β : ℝ) :
    (layerOp C B γ β)† =
      NormedSpace.exp (((γ : ℝ) * Complex.I : ℂ) • C) *
        NormedSpace.exp (((β : ℝ) * Complex.I : ℂ) • B) := by
  unfold layerOp
  rw [Matrix.conjTranspose_mul, ← Matrix.exp_conjTranspose, ← Matrix.exp_conjTranspose]
  -- ((-β I)•B)ᴴ = (β I)•B  and  ((-γ I)•C)ᴴ = (γ I)•C.
  have hstarβ : ((((-β : ℝ) * Complex.I : ℂ)) • B)† = (((β : ℝ) * Complex.I : ℂ)) • B := by
    rw [Matrix.conjTranspose_smul, hB]
    congr 1
    rw [show ((-β : ℝ) * Complex.I : ℂ) = (((-β : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  have hstarγ : ((((-γ : ℝ) * Complex.I : ℂ)) • C)† = (((γ : ℝ) * Complex.I : ℂ)) • C := by
    rw [Matrix.conjTranspose_smul, hC]
    congr 1
    rw [show ((-γ : ℝ) * Complex.I : ℂ) = (((-γ : ℝ)) : ℂ) * Complex.I by push_cast; ring]
    rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring
  rw [hstarβ, hstarγ]

/-- **The state bridge (operator level), generic angle form.** For Hermitian
generators `C, B`, the abstract conjugation recursion built from the SAME
cost/mixer exp factors as `qaoaConjugate` equals the explicit Heisenberg
conjugation `U_state† · O · U_state`, where `U_state` is `qaoaStateUnitary` fed
the *reversed* angle arrays.

This is the load-bearing structural identity: `qaoaConjugate`'s recursion peels
`Fin.last` (outermost), while `qaoaStateUnitary`'s recursion peels `0`
(innermost); the `Fin.rev` reversal aligns the two layer orders. -/
theorem genConjTwo_eq_stateUnitary_conj {n : ℕ} {C B : Op n}
    (hC : C† = C) (hB : B† = B) (O : Op n) :
    ∀ (P : ℕ) (g b : Fin P → ℝ),
      genConjTwo C B P g b O =
        (qaoaStateUnitary C B P (fun i => g i.rev) (fun i => b i.rev))† * O *
          (qaoaStateUnitary C B P (fun i => g i.rev) (fun i => b i.rev)) := by
  intro P
  induction P with
  | zero =>
    intro g b
    simp [genConjTwo, qaoaStateUnitary]
  | succ P ih =>
    intro g b
    -- Unfold one layer of genConjTwo (peels Fin.last P).
    rw [genConjTwo_succ]
    -- The recursive (castSucc) part: apply IH.
    rw [ih (fun i => g i.castSucc) (fun i => b i.castSucc)]
    -- Identify the state unitary at depth P+1 with reversed angles.
    -- U_state(P+1, g∘rev, b∘rev) = U_state(P, tail(g∘rev), tail(b∘rev)) · layerOp(g last, b last).
    rw [qaoaStateUnitary_succ]
    -- Reindex the tail-of-reversed angles to match the IH's `(g∘castSucc)∘rev` form:
    -- `tail(g∘rev) i = g (rev (succ i)) = g (castSucc (rev i)) = g (rev i).castSucc`,
    -- and the IH side carries `g i.rev.castSucc = g (castSucc (rev i))`.
    have hreindexG : (QAOA.tailFamily (fun i : Fin (P + 1) => g i.rev)) =
        (fun i : Fin P => g (Fin.rev i).castSucc) := by
      funext i
      show g (Fin.rev (Fin.succ i)) = g (Fin.castSucc (Fin.rev i))
      rw [Fin.rev_succ]
    have hreindexB : (QAOA.tailFamily (fun i : Fin (P + 1) => b i.rev)) =
        (fun i : Fin P => b (Fin.rev i).castSucc) := by
      funext i
      show b (Fin.rev (Fin.succ i)) = b (Fin.castSucc (Fin.rev i))
      rw [Fin.rev_succ]
    -- The peeled angle: (g∘rev) 0 = g (rev 0) = g (last P).
    have hangG : g (Fin.rev (0 : Fin (P + 1))) = g (Fin.last P) := by rw [Fin.rev_zero]
    have hangB : b (Fin.rev (0 : Fin (P + 1))) = b (Fin.last P) := by rw [Fin.rev_zero]
    rw [hreindexG, hreindexB]
    -- Align the IH's `g i.rev.castSucc` with the reindexed `g (rev i).castSucc`.
    have hIHidxG : (fun i : Fin P => g i.rev.castSucc) =
        (fun i : Fin P => g (Fin.rev i).castSucc) := rfl
    have hIHidxB : (fun i : Fin P => b i.rev.castSucc) =
        (fun i : Fin P => b (Fin.rev i).castSucc) := rfl
    rw [hIHidxG, hIHidxB]
    show _ = ((qaoaStateUnitary C B P (fun i => g (Fin.rev i).castSucc)
        (fun i => b (Fin.rev i).castSucc)) *
        layerOp C B (g (Fin.rev 0)) (b (Fin.rev 0)))† * O *
      ((qaoaStateUnitary C B P (fun i => g (Fin.rev i).castSucc)
        (fun i => b (Fin.rev i).castSucc)) *
        layerOp C B (g (Fin.rev 0)) (b (Fin.rev 0)))
    rw [hangG, hangB]
    -- Expand the dagger of `U_prev · layerOp(last)` and reassociate.
    set Uprev := qaoaStateUnitary C B P (fun i : Fin P => g (Fin.rev i).castSucc)
      (fun i : Fin P => b (Fin.rev i).castSucc) with hUprev
    rw [Matrix.conjTranspose_mul, layerOp_conjTranspose hC hB]
    -- Goal LHS: (CB'(g last) MB'(b last)) · (Uprev† O Uprev) · (MB(b last) CB(g last))
    -- Goal RHS: (CB'(g last) MB'(b last)) · Uprev† · O · Uprev · (MB(b last) CB(g last))
    -- These are equal by associativity + unfolding layerOp on the RHS.
    unfold layerOp
    -- Both sides are products of the same factors; finish by associativity.
    noncomm_ring

-- ============================================================================
-- Section: chain-specialized state bridge + expectation form
-- ============================================================================

/-- Two local Pauli `Z` operators commute (both diagonal in the computational
basis). -/
private theorem localPauliZ_commute' {N : ℕ} (i j : Fin N) :
    Commute (Qubits.localPauliZ i) (Qubits.localPauliZ j) := by
  change Qubits.localPauliZ i * Qubits.localPauliZ j =
    Qubits.localPauliZ j * Qubits.localPauliZ i
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, Qubits.localPauliZ_on_basis,
      op_mul_smul_ket, Qubits.localPauliZ_on_basis,
      op_mul_op_mul_ket, Qubits.localPauliZ_on_basis,
      op_mul_smul_ket, Qubits.localPauliZ_on_basis,
      Ket.smul_smul, Ket.smul_smul, mul_comm]

/-- The full-chain cost generator `Σ_k chainPairInteraction k` is Hermitian. -/
theorem sum_chainPairInteraction_conjTranspose (N : ℕ) :
    (∑ k : Fin N, IsingModel.chainPairInteraction k)† =
      ∑ k : Fin N, IsingModel.chainPairInteraction k := by
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  -- chainPairInteraction k = Z_k · Z_{k+1}, a product of commuting Hermitians.
  unfold IsingModel.chainPairInteraction
  rw [Matrix.conjTranspose_mul]
  have hZk : (Qubits.localPauliZ k)† = Qubits.localPauliZ k := by
    rw [Qubits.localPauliZ_eq_localOp, Qubits.localOp_conjTranspose]
    simp [Quantum.Gates.pauliZ_hermitian]
  have hZk' : (Qubits.localPauliZ (IsingModel.nextSite k))† =
      Qubits.localPauliZ (IsingModel.nextSite k) := by
    rw [Qubits.localPauliZ_eq_localOp, Qubits.localOp_conjTranspose]
    simp [Quantum.Gates.pauliZ_hermitian]
  rw [hZk, hZk']
  -- Z_k and Z_{k+1} commute (both diagonal); so (Z_k Z_{k+1})ᴴ = Z_{k+1} Z_k = Z_k Z_{k+1}.
  exact (localPauliZ_commute' k (IsingModel.nextSite k)).symm

/-- **The state bridge for the chain** (operator level). With the reversed angle
arrays, the FGG conjugation `qaoaConjugate` realizes the physical Heisenberg
conjugation `U_state† · O · U_state`, where `U_state` is the QAOA state unitary
built from the standard chain cost/mixer exp factors. -/
theorem qaoaConjugate_rev_eq_stateUnitary_conj {N P : ℕ} (γ β : Fin P → ℝ)
    (O : Qubits.NQubitOp N) :
    qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) O =
      (qaoaStateUnitary (∑ k : Fin N, IsingModel.chainPairInteraction k)
          (QAOA.standardMixerOp N) P γ β)† * O *
        (qaoaStateUnitary (∑ k : Fin N, IsingModel.chainPairInteraction k)
          (QAOA.standardMixerOp N) P γ β) := by
  rw [qaoaConjugate_eq_genConjTwo O P (fun i => γ i.rev) (fun i => β i.rev)]
  rw [genConjTwo_eq_stateUnitary_conj (sum_chainPairInteraction_conjTranspose N)
      (standardMixerOp_isHermitian N) O P (fun i => γ i.rev) (fun i => β i.rev)]
  -- The reversed-reversed angles collapse: `(γ∘rev)∘rev = γ`.
  simp only [Fin.rev_rev]

/-- The ring-of-disagrees chain Hamiltonian is the unsigned bond sum
`Σ_k chainPairInteraction k` (since `J ≡ 1`). -/
theorem isingChainHamiltonianOp_ringOfDisagrees (N : ℕ) :
    (IsingModel.isingChainHamiltonianOp
        (QAOA.IsingChain.ringOfDisagreesCouplings N)) =
      ∑ k : Fin N, IsingModel.chainPairInteraction k := by
  unfold IsingModel.isingChainHamiltonianOp QAOA.IsingChain.ringOfDisagreesCouplings
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp

/-- The standard chain QAOA state vector is the chain state unitary applied to
the uniform `|+⟩^{⊗N}` ket. -/
theorem standardIsingChainExponentialQAOAState_vec {N P : ℕ}
    {J : IsingModel.IsingChainCouplings N}
    (hChain : QAOA.IsingChainQAOAExponentials N J) (γ β : Fin P → ℝ) :
    (QAOA.standardIsingChainExponentialQAOAState hChain γ β).toKet.vec =
      Matrix.mulVec
        (qaoaStateUnitary (QAOA.isingChainCostOp J) (QAOA.standardMixerOp N) P γ β)
        (QAOA.uniformKet (Qubits.NQubitDim N)).vec := by
  rw [QAOA.standardIsingChainExponentialQAOAState_eq_standardExponentialQAOAState]
  -- standardExponentialQAOAState = exponentialQAOAState on the uniform state.
  show (QAOA.exponentialQAOAState (QAOA.isingChainToQAOAExponentials hChain) γ β
      (QAOA.uniformState (Qubits.NQubitDim N))).toKet.vec = _
  rw [exponentialQAOAState_toKet_vec]
  rfl

/-- **Expectation-form state bridge (full chain).** The QAOA first moment of the
ring-of-disagrees equals the `|+⟩`-sandwich of the FGG conjugation of the bond
sum at reversed angles:
`F_P(γ,β) = ⟨+| qaoaConjugate P (γ∘rev) (β∘rev) (Σ_k cP k) |+⟩`. -/
theorem isingChainQAOAFirstMoment_eq_uniform_conj {N P : ℕ}
    (hChain : QAOA.IsingChainQAOAExponentials N
      (QAOA.IsingChain.ringOfDisagreesCouplings N)) (γ β : Fin P → ℝ) :
    QAOA.isingChainQAOAFirstMoment hChain γ β =
      (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
            (∑ k : Fin N, IsingModel.chainPairInteraction k) *
          QAOA.uniformKet (Qubits.NQubitDim N)) := by
  classical
  -- Local conversion: `ψ.dag * (O * ψ) = dotProduct (star ψ.vec) (O.mulVec ψ.vec)`.
  have hconv : ∀ {M : ℕ} (ψ : Qubits.NQubitKet M) (O : Qubits.NQubitOp M),
      ψ.dag * (O * ψ) = dotProduct (star ψ.vec) (Matrix.mulVec O ψ.vec) := by
    intro M ψ O
    rw [bra_mul_ket_eq]; rfl
  -- Unfold the first moment to `ψ.dag * (H_C * ψ)` and rewrite H_C, the bridge, ψ.
  unfold QAOA.isingChainQAOAFirstMoment IsingModel.chainFirstMoment
  rw [isingChainHamiltonianOp_ringOfDisagrees, hconv,
      qaoaConjugate_rev_eq_stateUnitary_conj, hconv,
      standardIsingChainExponentialQAOAState_vec,
      show (QAOA.isingChainCostOp (QAOA.IsingChain.ringOfDisagreesCouplings N)) =
        ∑ k : Fin N, IsingModel.chainPairInteraction k from
      isingChainHamiltonianOp_ringOfDisagrees N]
  -- Now: star (U v) ⬝ ((ΣcP)(U v)) = star v ⬝ ((U†(ΣcP)U) v). Exactly the sandwich.
  rw [← sandwich_conj_mulVec]

/-- **Expectation-form state bridge (reduced ABC chain).** The ABC `psiTilde`
expectation of any operator `O` equals the `|+⟩`-sandwich of the generic
conjugation built from the reduced cost/mixer generators `Hred_z s`, `Hred_x` at
reversed angles:
`⟨ψ̃ s P γ β| O |ψ̃⟩ = ⟨+| genConjTwo Hred_z Hred_x P (γ∘rev) (β∘rev) O |+⟩`. -/
theorem psiTilde_expectation_eq_genConjugate (s : Bool) (P : ℕ) (γ β : Fin P → ℝ)
    (O : Qubits.NQubitOp (2 * P + 2)) :
    (psiTilde s P γ β).toKet.dag * (O * (psiTilde s P γ β).toKet) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (genConjTwo (Hred_z_hamiltonian s P : Qubits.NQubitOp (2 * P + 2))
            (Hred_x_hamiltonian P : Qubits.NQubitOp (2 * P + 2)) P
            (fun i => γ i.rev) (fun i => β i.rev) O *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  classical
  have hconv : ∀ (ψ : Qubits.NQubitKet (2 * P + 2)) (A : Qubits.NQubitOp (2 * P + 2)),
      ψ.dag * (A * ψ) = dotProduct (star ψ.vec) (Matrix.mulVec A ψ.vec) := by
    intro ψ A; rw [bra_mul_ket_eq]; rfl
  -- Reduce both sides to dotProduct form.
  rw [hconv, hconv]
  -- ψ̃ vec = U_state · |+⟩, where U_state = qaoaStateUnitary Hred_z Hred_x P γ β.
  have hpsi : (psiTilde s P γ β).toKet.vec =
      Matrix.mulVec
        (qaoaStateUnitary (Hred_z_hamiltonian s P : Qubits.NQubitOp (2 * P + 2))
          (Hred_x_hamiltonian P : Qubits.NQubitOp (2 * P + 2)) P γ β)
        (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).vec := by
    show (QAOA.standardExponentialQAOAState (reducedChainQAOAExp s P) γ β).toKet.vec = _
    show (QAOA.exponentialQAOAState (reducedChainQAOAExp s P) γ β
        (QAOA.uniformState (Qubits.NQubitDim (2 * P + 2)))).toKet.vec = _
    rw [exponentialQAOAState_toKet_vec]
    rfl
  rw [hpsi]
  -- The generic state bridge: genConjTwo at reversed angles = U_state† O U_state.
  rw [genConjTwo_eq_stateUnitary_conj
      (show (Hred_z_hamiltonian s P : Qubits.NQubitOp (2 * P + 2))† =
          (Hred_z_hamiltonian s P : Qubits.NQubitOp (2 * P + 2)) from
        (Hred_z_hamiltonian s P).isHermitian)
      (show (Hred_x_hamiltonian P : Qubits.NQubitOp (2 * P + 2))† =
          (Hred_x_hamiltonian P : Qubits.NQubitOp (2 * P + 2)) from
        (Hred_x_hamiltonian P).isHermitian)
      O P (fun i => γ i.rev) (fun i => β i.rev)]
  -- collapse `(γ∘rev)∘rev = γ`.
  simp only [Fin.rev_rev]
  -- Now exactly the sandwich identity.
  rw [← sandwich_conj_mulVec]

-- ============================================================================
-- Section: full-ring per-bond equality + sum (general width `M+1`)
-- ============================================================================

/-- **Per-bond equality of the `|+⟩`-conjugate (general full ring).** For the
full ring of width `M+1`, every bond's QAOA-conjugate `|+⟩`-expectation equals
that of the canonical bond reachable by `nextSite`. This is the full-chain
analogue of `reducedChainQAOAConj_at_expectation_reach`, but at general width
`M+1` (rather than `2P+2`), reusing the general-width
`qaoaConjugate_T_conj` / `uniformKet_expectation_T_conj`. -/
theorem fullRing_conj_expectation_reach (M P : ℕ) (g b : Fin P → ℝ)
    (k k' : Fin (M + 1)) (h_reach : ∃ m : ℕ, (IsingModel.nextSite^[m]) k = k') :
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (qaoaConjugate P g b (IsingModel.chainPairInteraction k') *
          QAOA.uniformKet (Qubits.NQubitDim (M + 1))) =
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (qaoaConjugate P g b (IsingModel.chainPairInteraction k) *
          QAOA.uniformKet (Qubits.NQubitDim (M + 1))) := by
  obtain ⟨m, hm⟩ := h_reach
  subst hm
  induction m with
  | zero => simp [Function.iterate_zero]
  | succ m ih =>
    rw [show (IsingModel.nextSite^[m + 1]) k =
          IsingModel.nextSite ((IsingModel.nextSite^[m]) k) from by
        rw [Function.iterate_succ_apply']]
    rw [← ih]
    -- one step: cP(nextSite j) = T† cP(j) T; pass T through the conjugation; T|+⟩=|+⟩.
    set j := (IsingModel.nextSite^[m]) k with hj
    rw [show IsingModel.chainPairInteraction (IsingModel.nextSite j) =
          (T_op_full M : Qubits.NQubitOp (M + 1))† *
            IsingModel.chainPairInteraction j *
            (T_op_full M : Qubits.NQubitOp (M + 1)) from
        (T_conj_full_chainPairInteraction M j).symm]
    rw [← qaoaConjugate_T_conj M P g b (IsingModel.chainPairInteraction j)]
    exact uniformKet_expectation_T_conj M
      (qaoaConjugate P g b (IsingModel.chainPairInteraction j))

/-- Every bond `0` of the full ring `Fin (M+1)` reaches every other bond `k` by
iterated `nextSite` (cyclic transitivity). -/
theorem nextSite_reaches_all (M : ℕ) (k : Fin (M + 1)) :
    ∃ m : ℕ, (IsingModel.nextSite^[m]) (0 : Fin (M + 1)) = k := by
  refine ⟨k.val, ?_⟩
  -- Track only the underlying value: `(nextSite^[t] 0).val = t % (M+1)`.
  have hval : ∀ t : ℕ, ((IsingModel.nextSite^[t]) (0 : Fin (M + 1))).val =
      t % (M + 1) := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
      rw [Function.iterate_succ_apply', IsingModel.nextSite_val, iht]
      -- `(t % (M+1) + 1) % (M+1) = (t + 1) % (M+1)` via `Nat.add_mod`.
      conv_rhs => rw [Nat.add_mod t 1 (M + 1)]
      rcases Nat.eq_zero_or_pos M with hM | hM
      · subst hM; simp
      · rw [Nat.mod_eq_of_lt (show (1 : ℕ) < M + 1 by omega)]
  apply Fin.ext
  rw [hval k.val]
  exact Nat.mod_eq_of_lt k.isLt

/-- `qaoaConjugate` is additive in its operator argument: `conj(A+B) = conj A + conj B`.
This follows from the `U†·(·)·U` realization (matrix conjugation is linear). -/
theorem qaoaConjugate_rev_add {N P : ℕ} (γ β : Fin P → ℝ) (A B : Qubits.NQubitOp N) :
    qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) (A + B) =
      qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) A +
        qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) B := by
  rw [qaoaConjugate_rev_eq_stateUnitary_conj, qaoaConjugate_rev_eq_stateUnitary_conj,
      qaoaConjugate_rev_eq_stateUnitary_conj]
  noncomm_ring

/-- `qaoaConjugate` of a finite sum equals the sum of conjugates (reversed angles). -/
theorem qaoaConjugate_rev_sum {N P : ℕ} (γ β : Fin P → ℝ)
    {ι : Type*} (s : Finset ι) (f : ι → Qubits.NQubitOp N) :
    qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) (∑ x ∈ s, f x) =
      ∑ x ∈ s, qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev) (f x) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.sum_empty]
    -- conj of 0 is 0.
    rw [qaoaConjugate_rev_eq_stateUnitary_conj]; simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, qaoaConjugate_rev_add, ih]

/-- **Full-ring sum reduces to `(M+1)` copies of the canonical bond conjugate.**
For the full ring `Fin (M+1)`, the `|+⟩`-expectation of the conjugated cost sum
equals `(M+1)` times the canonical bond-`0` conjugate `|+⟩`-expectation. -/
theorem fullRing_conj_sum_eq_smul (M P : ℕ) (γ β : Fin P → ℝ) :
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
            (∑ k : Fin (M + 1), IsingModel.chainPairInteraction k) *
          QAOA.uniformKet (Qubits.NQubitDim (M + 1))) =
      ((M + 1 : ℕ) : ℂ) *
        ((QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
          (qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
              (IsingModel.chainPairInteraction (0 : Fin (M + 1))) *
            QAOA.uniformKet (Qubits.NQubitDim (M + 1)))) := by
  classical
  -- Convert all expectations to dotProduct form to distribute over the sum.
  have hconv : ∀ (O : Qubits.NQubitOp (M + 1)),
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
          (O * QAOA.uniformKet (Qubits.NQubitDim (M + 1))) =
        dotProduct (star (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec)
          (Matrix.mulVec O (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec) := by
    intro O; rw [bra_mul_ket_eq]; rfl
  rw [qaoaConjugate_rev_sum, hconv]
  -- (∑ O_k).mulVec v = ∑ (O_k.mulVec v); dotProduct distributes over the sum.
  rw [Matrix.sum_mulVec, dotProduct_sum]
  -- Each summand back to bra/ket form, then full-ring reach to bond `0`.
  rw [show (∑ k : Fin (M + 1),
        dotProduct (star (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec)
          (Matrix.mulVec
            (qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
              (IsingModel.chainPairInteraction k))
            (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec)) =
      ∑ k : Fin (M + 1),
        (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
          (qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
            (IsingModel.chainPairInteraction k) *
            QAOA.uniformKet (Qubits.NQubitDim (M + 1))) from by
    refine Finset.sum_congr rfl (fun k _ => ?_); rw [(hconv _).symm]]
  -- Each summand equals the canonical bond-`0` term by full-ring reach.
  rw [Finset.sum_congr rfl (fun k _ =>
    fullRing_conj_expectation_reach M P (fun i => γ i.rev) (fun i => β i.rev)
      (0 : Fin (M + 1)) k (nextSite_reaches_all M k))]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end

end QAOA.IsingChain.UpperBound.LightCone
