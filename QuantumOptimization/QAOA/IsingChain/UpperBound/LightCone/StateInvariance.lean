import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ChainIdentification
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials

/-!
# T-invariance of the full-chain QAOA state

This file delivers the **state-level cyclic translation invariance** of the
full-chain QAOA output state `|ψ_P⟩ = U_QAOA · |+⟩^{⊗N}`:

    `T_op_full M · |ψ_P⟩ = |ψ_P⟩`     (on `M + 1`-qubit chains)

This is the `h_inv` precondition consumed by
`first_moment_cyclic_invariance` in `ChainIdentification.lean`, which
in turn is the cyclic-translation-invariance pillar of the FGG
light-cone reduction in `Reduction.lean`.

Source: arXiv:1411.4028v1 §IV (translation invariance of the Ring of
Disagrees Hamiltonian + uniform state); arXiv:1906.08948v2 §IV
(translation argument).

## Proof strategy (mirroring A4 `Ttilde_op_apply_psiTilde`)

1. `T_op_full M · |+⟩^{⊗(M+1)} = |+⟩^{⊗(M+1)}` — the uniform state is
   fixed by any basis permutation.
2. `T_op_full M` commutes with the chain cost Hamiltonian `Σ_k Z_k Z_{k+1}`
   (already in `ChainIdentification` via `T_conj_full_chainPairInteraction_sum`).
3. `T_op_full M` commutes with the standard mixer `Σ_j X_j` (each
   `X_j` cycles into `X_{nextSite j}`).
4. Therefore `T_op_full M` commutes with `exp(-iγ H_C)` and `exp(-iβ H_B)`
   via `Matrix.exp_units_conj'`.
5. By induction on `P`, `T_op_full M · |ψ_P⟩ = |ψ_P⟩`.

## Public deliverables

* `T_op_full_apply_qaoa_state` — `T_op_full M · |ψ_P⟩ = |ψ_P⟩` for the
  standard chain exponential QAOA state on `M + 1` qubits with the
  ring-of-disagrees couplings.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: T_op_full preserves the uniform state
-- ============================================================================

/-- A permutation matrix acting on the uniform-state vector gives the same
vector (uniform vector is constant; a permutation merely reorders it). -/
private theorem permMatrix_mulVec_uniformKet_full {n : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.permMatrix ℂ σ).mulVec (uniformKet n).vec =
      (uniformKet n).vec := by
  funext j
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- `T_op_full M · uniformKet = uniformKet` at the matrix `mulVec` level.

Consumed by the reduced-bond translation
invariance `reducedChainQAOAConj_at_expectation_eq_zero` in
`ReducedBondInvariance.lean`. -/
theorem T_op_full_mulVec_uniformKet (M : ℕ) :
    Matrix.mulVec (T_op_full M : Qubits.NQubitOp (M + 1))
        (uniformKet (Qubits.NQubitDim (M + 1))).vec =
      (uniformKet (Qubits.NQubitDim (M + 1))).vec := by
  rw [T_op_full_toOp]
  exact permMatrix_mulVec_uniformKet_full (T_perm_full M)

-- ============================================================================
-- Section: nextSite injectivity (private helper)
-- ============================================================================

/-- `IsingModel.nextSite` is injective on `Fin (M + 1)`. -/
private theorem nextSite_injective_full (M : ℕ) :
    Function.Injective (IsingModel.nextSite : Fin (M + 1) → Fin (M + 1)) := by
  intro a b hab
  have h1 : (IsingModel.nextSite a).val = (IsingModel.nextSite b).val :=
    congrArg Fin.val hab
  rw [IsingModel.nextSite_val, IsingModel.nextSite_val] at h1
  apply Fin.ext
  have haM : (a : ℕ) < M + 1 := a.isLt
  have hbM : (b : ℕ) < M + 1 := b.isLt
  have ha1 : (a : ℕ) + 1 ≤ M + 1 := haM
  have hb1 : (b : ℕ) + 1 ≤ M + 1 := hbM
  by_cases haLast : (a : ℕ) + 1 = M + 1
  · by_cases hbLast : (b : ℕ) + 1 = M + 1
    · omega
    · have hamod : ((a : ℕ) + 1) % (M + 1) = 0 := by
        rw [haLast]; exact Nat.mod_self _
      have hblt : (b : ℕ) + 1 < M + 1 := lt_of_le_of_ne hb1 hbLast
      have hbmod : ((b : ℕ) + 1) % (M + 1) = (b : ℕ) + 1 :=
        Nat.mod_eq_of_lt hblt
      rw [hamod, hbmod] at h1
      omega
  · by_cases hbLast : (b : ℕ) + 1 = M + 1
    · have hbmod : ((b : ℕ) + 1) % (M + 1) = 0 := by
        rw [hbLast]; exact Nat.mod_self _
      have halt : (a : ℕ) + 1 < M + 1 := lt_of_le_of_ne ha1 haLast
      have hamod : ((a : ℕ) + 1) % (M + 1) = (a : ℕ) + 1 :=
        Nat.mod_eq_of_lt halt
      rw [hbmod, hamod] at h1
      omega
    · have halt : (a : ℕ) + 1 < M + 1 := lt_of_le_of_ne ha1 haLast
      have hblt : (b : ℕ) + 1 < M + 1 := lt_of_le_of_ne hb1 hbLast
      have hamod : ((a : ℕ) + 1) % (M + 1) = (a : ℕ) + 1 :=
        Nat.mod_eq_of_lt halt
      have hbmod : ((b : ℕ) + 1) % (M + 1) = (b : ℕ) + 1 :=
        Nat.mod_eq_of_lt hblt
      rw [hamod, hbmod] at h1
      omega

/-- `IsingModel.nextSite` is bijective on `Fin (M + 1)`. -/
private theorem nextSite_bijective_full (M : ℕ) :
    Function.Bijective (IsingModel.nextSite : Fin (M + 1) → Fin (M + 1)) :=
  ⟨nextSite_injective_full M, Finite.surjective_of_injective (nextSite_injective_full M)⟩

-- ============================================================================
-- Section: T-conjugation of the standard mixer
-- ============================================================================

/-!
The standard mixer `Σ_j X_j` is invariant under cyclic conjugation because
`X_j` cycles to `X_{nextSite j}` and the sum is invariant under reindexing
by the bijection `j ↦ nextSite j`.
-/

/-- The classical-bit-flip action of `localPauliX j` is compatible with the
cyclic rotation: rotating then flipping bit `j` equals flipping bit
`nextSite j` then rotating.

Precisely: `flipBitAt (rotate b) j = rotate (flipBitAt b (nextSite j))`
where `rotate` is the forward bit-rotation `b ↦ b ∘ nextSite`. -/
private theorem flipBitAt_rotateBits_commute (M : ℕ) (b : Qubits.BitString (M + 1))
    (j : Fin (M + 1)) :
    Qubits.flipBitAt (rotateBitsEquivFull M b) j =
      rotateBitsEquivFull M (Qubits.flipBitAt b (IsingModel.nextSite j)) := by
  funext k
  simp only [Qubits.flipBitAt, rotateBitsEquivFull_apply]
  by_cases hk : k = j
  · subst hk
    simp
  · have hk' : IsingModel.nextSite k ≠ IsingModel.nextSite j := fun heq ↦
      hk (nextSite_injective_full M heq)
    simp [hk, hk']

/-- Conjugation by `T_op_full` sends `localPauliX j` to `localPauliX (nextSite j)`. -/
private theorem T_conj_full_localPauliX (M : ℕ) (j : Fin (M + 1)) :
    (T_op_full M : Qubits.NQubitOp (M + 1))† *
        Qubits.localPauliX j *
        (T_op_full M : Qubits.NQubitOp (M + 1)) =
      Qubits.localPauliX (IsingModel.nextSite j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  -- LHS · |z⟩
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, T_op_full_on_basis]
  -- localPauliX j · |rotate z⟩ = |flipBitAt (rotate z) j⟩
  rw [Qubits.localPauliX_on_basis]
  -- T† · |flipBitAt (rotate z) j⟩ = |(rotate)⁻¹ (flipBitAt (rotate z) j)⟩
  rw [T_op_full_adj_on_basis]
  -- Use flipBitAt_rotateBits_commute:
  -- flipBitAt (rotate z) j = rotate (flipBitAt z (nextSite j))
  -- Therefore (rotate)⁻¹ (flipBitAt (rotate z) j) = flipBitAt z (nextSite j)
  rw [flipBitAt_rotateBits_commute]
  rw [Equiv.symm_apply_apply]
  -- RHS · |z⟩ = localPauliX (nextSite j) · |z⟩ = |flipBitAt z (nextSite j)⟩
  rw [Qubits.localPauliX_on_basis]

/-- The standard mixer `Σ_j X_j` is T-invariant.

Consumed by the reduced-bond translation
invariance `reducedChainQAOAConj_at_expectation_eq_zero` in
`ReducedBondInvariance.lean` (to commute `T` past the `qaoaConjugate`
mixer layers). -/
theorem T_conj_full_standardMixer (M : ℕ) :
    (T_op_full M : Qubits.NQubitOp (M + 1))† *
        QAOA.standardMixerOp (M + 1) *
        (T_op_full M : Qubits.NQubitOp (M + 1)) =
      QAOA.standardMixerOp (M + 1) := by
  unfold QAOA.standardMixerOp
  -- Distribute conjugation over the sum.
  rw [Finset.mul_sum]
  rw [show (∑ k : Fin (M + 1),
        (T_op_full M : Qubits.NQubitOp (M + 1))† * Qubits.localPauliX k) *
      (T_op_full M : Qubits.NQubitOp (M + 1)) =
    ∑ k : Fin (M + 1),
      (T_op_full M : Qubits.NQubitOp (M + 1))† * Qubits.localPauliX k *
        (T_op_full M : Qubits.NQubitOp (M + 1)) from by
    rw [Finset.sum_mul]]
  rw [Finset.sum_congr rfl (fun k _ ↦ T_conj_full_localPauliX M k)]
  -- Reindex sum via the bijection j ↦ nextSite j.
  let e : Fin (M + 1) ≃ Fin (M + 1) :=
    Equiv.ofBijective IsingModel.nextSite (nextSite_bijective_full M)
  have heq : ∀ k, e k = IsingModel.nextSite k := fun _ ↦ rfl
  exact Finset.sum_equiv e (by simp) (fun k _ ↦ by rw [heq k])

-- ============================================================================
-- Section: T-conjugation of the chain cost Hamiltonian
-- ============================================================================

/-- The chain cost Hamiltonian with ring-of-disagrees couplings is T-invariant. -/
private theorem T_conj_full_ringOfDisagrees_cost (M : ℕ) :
    (T_op_full M : Qubits.NQubitOp (M + 1))† *
        (IsingModel.isingChainHamiltonianOp
          (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) *
        (T_op_full M : Qubits.NQubitOp (M + 1)) =
      IsingModel.isingChainHamiltonianOp
        (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)) := by
  -- isingChainHamiltonianOp J = Σ_k (J k) • chainPairInteraction k
  -- For ringOfDisagrees, J ≡ 1, so this equals Σ_k chainPairInteraction k.
  unfold IsingModel.isingChainHamiltonianOp
  have hJ : ∀ k : Fin (M + 1),
      (((QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)).J k : ℝ) : ℂ) = 1 := by
    intro k
    show ((1 : ℝ) : ℂ) = 1
    push_cast; rfl
  rw [Finset.sum_congr rfl (fun k _ ↦ by
    rw [hJ k, one_smul])]
  -- Now: T† * (Σ_k chainPairInteraction k) * T = Σ_k chainPairInteraction k.
  exact T_conj_full_chainPairInteraction_sum M

-- ============================================================================
-- Section: Helper — exp commute via conjugation
-- ============================================================================

/-- If a unitary `U` satisfies `U† · H · U = H` for an operator `H`, then
`U` commutes with `exp(α • H)`. Adapted from A4's `exp_commute_of_conj`.

Consumed by the reduced-bond translation
invariance `reducedChainQAOAConj_at_expectation_eq_zero` in
`ReducedBondInvariance.lean` (to commute `T` past each `qaoaConjugate`
exponential layer). -/
theorem exp_commute_of_conj_full {N : ℕ}
    (U : Qubits.NQubitUnitaryOp N) (Hop : Qubits.NQubitOp N) (α : ℂ)
    (hUH : (U : Qubits.NQubitOp N)† * Hop * (U : Qubits.NQubitOp N) = Hop) :
    (U : Qubits.NQubitOp N) * NormedSpace.exp (α • Hop) =
      NormedSpace.exp (α • Hop) * (U : Qubits.NQubitOp N) := by
  let uMat : (Matrix (Fin (Qubits.NQubitDim N)) (Fin (Qubits.NQubitDim N)) ℂ)ˣ :=
    { val := (U : Qubits.NQubitOp N)
      inv := (U : Qubits.NQubitOp N)†
      val_inv := U.unitary_right
      inv_val := U.unitary_left }
  have hUHsmul :
      (U : Qubits.NQubitOp N)† * (α • Hop) * (U : Qubits.NQubitOp N) = α • Hop := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hUH]
  have hexp_conj := Matrix.exp_units_conj' uMat (α • Hop)
  change NormedSpace.exp ((U : Qubits.NQubitOp N)† * (α • Hop) *
      (U : Qubits.NQubitOp N)) =
    (U : Qubits.NQubitOp N)† * NormedSpace.exp (α • Hop) *
      (U : Qubits.NQubitOp N) at hexp_conj
  rw [hUHsmul] at hexp_conj
  have hkey := congrArg ((U : Qubits.NQubitOp N) * ·) hexp_conj
  simp only at hkey
  rw [hkey]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, U.unitary_right, Matrix.one_mul]

/-- `T_op_full M` commutes with the mixer exponential
`exp(-iβ · (isingChainMixerHamiltonian (M+1)))`. -/
private theorem T_op_full_commutes_mixerExponential (M : ℕ) (β : ℝ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        QAOA.mixerExponential (QAOA.isingChainMixerHamiltonian (M + 1)) β =
      QAOA.mixerExponential (QAOA.isingChainMixerHamiltonian (M + 1)) β *
        (T_op_full M : Qubits.NQubitOp (M + 1)) := by
  unfold QAOA.mixerExponential
  have hconj :
      (T_op_full M : Qubits.NQubitOp (M + 1))† *
          ((QAOA.isingChainMixerHamiltonian (M + 1)) :
            Qubits.NQubitOp (M + 1)) *
          (T_op_full M : Qubits.NQubitOp (M + 1)) =
        ((QAOA.isingChainMixerHamiltonian (M + 1)) :
          Qubits.NQubitOp (M + 1)) := by
    rw [QAOA.isingChainMixerHamiltonian_toOp]
    show (T_op_full M : Qubits.NQubitOp (M + 1))† *
        (QAOA.isingChainMixerOp (M + 1)) *
        (T_op_full M : Qubits.NQubitOp (M + 1)) =
      QAOA.isingChainMixerOp (M + 1)
    rw [QAOA.isingChainMixerOp_eq_standardMixerOp]
    exact T_conj_full_standardMixer M
  exact exp_commute_of_conj_full (T_op_full M) _ ((-β * Complex.I : ℂ)) hconj

/-- `T_op_full M` commutes with the cost exponential
`exp(-iγ · (isingChainCostHamiltonian (ringOfDisagrees ...)))`. -/
private theorem T_op_full_commutes_costExponential (M : ℕ) (γ : ℝ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        QAOA.costExponential
          (QAOA.isingChainCostHamiltonian
            (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) γ =
      QAOA.costExponential
          (QAOA.isingChainCostHamiltonian
            (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) γ *
        (T_op_full M : Qubits.NQubitOp (M + 1)) := by
  unfold QAOA.costExponential
  have hconj :
      (T_op_full M : Qubits.NQubitOp (M + 1))† *
          ((QAOA.isingChainCostHamiltonian
            (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) :
            Qubits.NQubitOp (M + 1)) *
          (T_op_full M : Qubits.NQubitOp (M + 1)) =
        ((QAOA.isingChainCostHamiltonian
          (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) :
          Qubits.NQubitOp (M + 1)) := by
    rw [QAOA.isingChainCostHamiltonian_toOp,
        QAOA.isingChainCostOp_eq_isingChainHamiltonianOp]
    exact T_conj_full_ringOfDisagrees_cost M
  exact exp_commute_of_conj_full (T_op_full M) _ ((-γ * Complex.I : ℂ)) hconj

-- ============================================================================
-- Section: Inductive invariance of the QAOA state
-- ============================================================================

/-- Generic chain QAOA state at chain length `M+1` with arbitrary initial state. -/
private def genFullQAOA (M p : ℕ)
    (hChain : QAOA.IsingChainQAOAExponentials (M + 1)
      (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)))
    (γ β : Fin p → ℝ) (ψ0 : Qubits.NQubitNormKet (M + 1)) :
    Qubits.NQubitNormKet (M + 1) :=
  QAOA.qaoaState
    (QAOA.costUnitaryFamily
      (QAOA.isingChainToQAOAExponentials hChain).toQAOAHamiltonians γ)
    (QAOA.mixerUnitaryFamily
      (QAOA.isingChainToQAOAExponentials hChain).toQAOAHamiltonians β)
    ψ0

private theorem genFullQAOA_zero (M : ℕ)
    (hChain : QAOA.IsingChainQAOAExponentials (M + 1)
      (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)))
    (ψ0 : Qubits.NQubitNormKet (M + 1)) :
    genFullQAOA M 0 hChain (fun i ↦ nomatch i) (fun i ↦ nomatch i) ψ0 = ψ0 := by
  unfold genFullQAOA
  exact QAOA.qaoaState_zero ψ0

private theorem genFullQAOA_succ (M p : ℕ)
    (hChain : QAOA.IsingChainQAOAExponentials (M + 1)
      (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)))
    (γ β : Fin (p+1) → ℝ) (ψ0 : Qubits.NQubitNormKet (M + 1)) :
    genFullQAOA M (p+1) hChain γ β ψ0 =
      genFullQAOA M p hChain (QAOA.tailFamily γ) (QAOA.tailFamily β)
        (QAOA.applyLayer
          (hChain.costUnitary (γ 0))
          (hChain.mixerUnitary (β 0))
          ψ0) := rfl

/-- For any T-invariant initial state, the depth-p QAOA state remains T-invariant. -/
private theorem T_op_full_apply_genFullQAOA (M : ℕ)
    (hChain : QAOA.IsingChainQAOAExponentials (M + 1)
      (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) :
    ∀ p : ℕ, ∀ γ β : Fin p → ℝ, ∀ ψ0 : Qubits.NQubitNormKet (M + 1),
      Matrix.mulVec (T_op_full M : Qubits.NQubitOp (M + 1)) ψ0.toKet.vec =
        ψ0.toKet.vec →
        Matrix.mulVec (T_op_full M : Qubits.NQubitOp (M + 1))
            (genFullQAOA M p hChain γ β ψ0).toKet.vec =
          (genFullQAOA M p hChain γ β ψ0).toKet.vec := by
  intro p
  induction p with
  | zero =>
    intro γ β ψ0 hψ0
    have hγ : γ = fun i ↦ nomatch i := by funext i; exact i.elim0
    have hβ : β = fun i ↦ nomatch i := by funext i; exact i.elim0
    rw [hγ, hβ, genFullQAOA_zero]
    exact hψ0
  | succ p IH =>
    intro γ β ψ0 hψ0
    rw [genFullQAOA_succ]
    apply IH
    -- Need: T · (applyLayer cost mixer ψ0).toKet = (applyLayer ...).toKet
    -- where cost = hChain.costUnitary (γ 0), mixer = hChain.mixerUnitary (β 0).
    -- (applyLayer C M ψ).vec = M.toOp *ᵥ (C.toOp *ᵥ ψ.vec)
    have hcost_spec : (hChain.costUnitary (γ 0) : Qubits.NQubitOp (M + 1)) =
        QAOA.costExponential
          (QAOA.isingChainCostHamiltonian
            (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1))) (γ 0) :=
      hChain.costUnitary_spec (γ 0)
    have hmixer_spec : (hChain.mixerUnitary (β 0) : Qubits.NQubitOp (M + 1)) =
        QAOA.mixerExponential
          (QAOA.isingChainMixerHamiltonian (M + 1)) (β 0) :=
      hChain.mixerUnitary_spec (β 0)
    have happly : (QAOA.applyLayer
          (hChain.costUnitary (γ 0))
          (hChain.mixerUnitary (β 0))
          ψ0).toKet.vec =
        Matrix.mulVec
          (hChain.mixerUnitary (β 0) : Qubits.NQubitOp (M + 1))
          (Matrix.mulVec
            (hChain.costUnitary (γ 0) : Qubits.NQubitOp (M + 1)) ψ0.toKet.vec) := by
      unfold QAOA.applyLayer
      rfl
    rw [happly]
    -- Use commutation of T with cost/mixer exponentials.
    have hmix := T_op_full_commutes_mixerExponential M (β 0)
    have hcost := T_op_full_commutes_costExponential M (γ 0)
    -- Rewrite hmix/hcost into the hChain-unitary form via the spec.
    rw [← hmixer_spec] at hmix
    rw [← hcost_spec] at hcost
    -- Combine via commutation: (T * mix * cost) *ᵥ ψ0 = (mix * cost * T) *ᵥ ψ0.
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    have hmul_eq :
        ((T_op_full M : Qubits.NQubitOp (M + 1)) *
            (hChain.mixerUnitary (β 0) : Qubits.NQubitOp (M + 1))) *
            (hChain.costUnitary (γ 0) : Qubits.NQubitOp (M + 1)) =
          (hChain.mixerUnitary (β 0) : Qubits.NQubitOp (M + 1)) *
            (hChain.costUnitary (γ 0) : Qubits.NQubitOp (M + 1)) *
            (T_op_full M : Qubits.NQubitOp (M + 1)) := by
      rw [hmix, Matrix.mul_assoc, hcost, ← Matrix.mul_assoc]
    rw [hmul_eq]
    -- (mix * cost * T) *ᵥ ψ0 = mix *ᵥ (cost *ᵥ (T *ᵥ ψ0)) = mix *ᵥ (cost *ᵥ ψ0).
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hψ0]

-- ============================================================================
-- Section: Main theorem
-- ============================================================================

/-- **T-invariance of the full-chain QAOA state.**

For the standard chain exponential QAOA state with ring-of-disagrees
couplings on `M + 1` sites, `T_op_full M · |ψ_P⟩ = |ψ_P⟩`.

This is the precondition consumed by `first_moment_cyclic_invariance` in
`ChainIdentification.lean`.

Source: arXiv:1411.4028v1 §IV (translation invariance of Ring of Disagrees);
arXiv:1906.08948v2 §IV (translation argument). -/
theorem T_op_full_apply_qaoa_state (M P : ℕ)
    (hChain : QAOA.IsingChainQAOAExponentials (M + 1)
      (QAOA.IsingChain.ringOfDisagreesCouplings (M + 1)))
    (γ β : Fin P → ℝ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        (QAOA.standardIsingChainExponentialQAOAState hChain γ β).toKet =
      (QAOA.standardIsingChainExponentialQAOAState hChain γ β).toKet := by
  -- Prove the mulVec version (which is what we have machinery for).
  apply Ket.ext
  intro i
  have h := T_op_full_apply_genFullQAOA M hChain P γ β
    (QAOA.uniformState (QAOA.IsingChainQAOADim (M + 1))) ?_
  · -- Convert the goal `(T * ψ).vec = ψ.vec`.
    have heq : QAOA.standardIsingChainExponentialQAOAState hChain γ β =
        genFullQAOA M P hChain γ β
          (QAOA.uniformState (QAOA.IsingChainQAOADim (M + 1))) := rfl
    rw [heq]
    show (T_op_full M : Qubits.NQubitOp (M + 1)).mulVec
        (genFullQAOA M P hChain γ β
          (QAOA.uniformState (QAOA.IsingChainQAOADim (M + 1)))).toKet.vec i =
      (genFullQAOA M P hChain γ β
        (QAOA.uniformState (QAOA.IsingChainQAOADim (M + 1)))).toKet.vec i
    exact congrFun h i
  · -- Need: T_op_full · uniformState = uniformState.
    show Matrix.mulVec _
        (QAOA.uniformState (QAOA.IsingChainQAOADim (M + 1))).toKet.vec = _
    -- IsingChainQAOADim (M+1) = Qubits.NQubitDim (M+1) by abbrev.
    exact T_op_full_mulVec_uniformKet M

end

end QAOA.IsingChain.UpperBound.LightCone
