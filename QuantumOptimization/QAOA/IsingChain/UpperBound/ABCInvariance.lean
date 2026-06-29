import QuantumOptimization.QAOA.IsingChain.UpperBound.TranslationOperators
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# ABC Invariance — `Ttilde`-invariance of `Hred_x`, `Hred_z^-`, `|ψ̃⟩`

This file proves the five load-bearing invariance / decomposition theorems for
the elementary upper-bound proof of the QAOA ring-of-disagrees residual energy.
The reduced-chain Hamiltonians and the depth-`P` state `|ψ̃_P(γ,β)⟩` were built
in `ReducedChain.lean`; the standard / twisted translation operators
`T_op, Ttilde_op` and their conjugation action on local Paulis were built in
`TranslationOperators.lean`. This file packages them into the five identities
used in §A6 to deduce the ABC residual-energy bound.

Source: arXiv:1906.08948v2 App. `app:ABC_to_PBC`, l.1308, l.1362–1404.

## Public deliverables

* `Ttilde_op_conj_Hred_x` (l.1365) — `T̃† · Hred_x · T̃ = Hred_x`.
* `Ttilde_op_conj_Hred_z_pm_false` (l.1362) — `T̃† · Hred_z^- · T̃ = Hred_z^-`.
* `Ttilde_op_apply_psiTilde` (l.1373) — `T̃ · |ψ̃_P⟩ = |ψ̃_P⟩`.
* `Hred_z_pm_false_eq_sum_translates` (l.1381) — sum-of-conjugates decomposition
  at the fixed bond `j_s = 0`. (The source's free-`j_s` form is false at
  `j_s = Fin.last`.)
* `chainPairInteraction_expectation_eq_averaged` (l.1308) — averaging identity
  at the fixed bond `j_s = 0`.

The internal packaging uses the signed-periodic-sum `S_pbc` data. The exp-conjugation step in
`Ttilde_op_apply_psiTilde` uses `Matrix.exp_units_conj'` from Mathlib's
`MatrixExponential.lean` packaged through a manual `Units` construction on
`Ttilde_op`.
-/

namespace QAOA.IsingChain.UpperBound

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Generic conjugation distribution helpers
-- ============================================================================

/-- Conjugation by a unitary distributes through a finite sum: `U† · (Σ A_k) · U
= Σ (U† · A_k · U)`. This is just bilinearity of matrix multiplication. -/
private lemma conj_sum_distrib {N : ℕ} {ι : Type*} (s : Finset ι)
    (U : Qubits.NQubitOp N) (A : ι → Qubits.NQubitOp N) :
    U† * (∑ k ∈ s, A k) * U = ∑ k ∈ s, U† * A k * U := by
  rw [Matrix.mul_sum]
  exact Matrix.sum_mul s (fun k ↦ U† * A k) U

/-- Conjugation by a unitary on the identity is the identity. -/
private lemma conj_one {N : ℕ} (U : Qubits.NQubitUnitaryOp N) :
    (U : Qubits.NQubitOp N)† * (1 : Qubits.NQubitOp N) *
        (U : Qubits.NQubitOp N) = (1 : Qubits.NQubitOp N) := by
  rw [Matrix.mul_one]
  exact U.unitary_left

/-- Conjugation distributes through subtraction. -/
private lemma conj_sub {N : ℕ} (U : Qubits.NQubitOp N)
    (A B : Qubits.NQubitOp N) :
    U† * (A - B) * U = U† * A * U - U† * B * U := by
  rw [Matrix.mul_sub, Matrix.sub_mul]

/-- Conjugation distributes through scalar multiplication. -/
private lemma conj_smul {N : ℕ} (U : Qubits.NQubitOp N) (c : ℂ)
    (A : Qubits.NQubitOp N) :
    U† * (c • A) * U = c • (U† * A * U) := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Conjugation distributes through addition. -/
private lemma conj_add {N : ℕ} (U : Qubits.NQubitOp N)
    (A B : Qubits.NQubitOp N) :
    U† * (A + B) * U = U† * A * U + U† * B * U := by
  rw [Matrix.mul_add, Matrix.add_mul]

/-- Conjugation distributes through negation. -/
private lemma conj_neg {N : ℕ} (U : Qubits.NQubitOp N) (A : Qubits.NQubitOp N) :
    U† * (-A) * U = -(U† * A * U) := by
  rw [Matrix.mul_neg, Matrix.neg_mul]

-- ============================================================================
-- Section: nextSite as a bijection
-- ============================================================================

/-- `IsingModel.nextSite` on `Fin (2*P+2)` is exactly Mathlib's `finRotate`. -/
private theorem nextSite_eq_finRotate' (P : ℕ) (j : Fin (2*P+2)) :
    IsingModel.nextSite j = finRotate (2*P+2) j := by
  apply Fin.ext
  have h : (finRotate (2*P+2) j : ℕ) =
      if j = Fin.last (2*P+1) then (0 : ℕ) else (j : ℕ) + 1 := by
    have := coe_finRotate (n := 2*P+1) j
    simpa using this
  rw [h, IsingModel.nextSite_val]
  by_cases hj : j = Fin.last (2*P+1)
  · subst hj
    rw [if_pos rfl, Fin.val_last]
    have h2 : (2*P+1 + 1) = 2*P+2 := by ring
    rw [h2, Nat.mod_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < 2*P+2 := by
      have : (j : ℕ) < 2*P+1 := Fin.val_lt_last hj
      omega
    exact Nat.mod_eq_of_lt hlt

/-- `nextSite (Fin.last (2*P+1)) = 0`. -/
private theorem nextSite_last' (P : ℕ) :
    IsingModel.nextSite (Fin.last (2*P+1) : Fin (2*P+2)) = (0 : Fin (2*P+2)) := by
  rw [nextSite_eq_finRotate']
  exact finRotate_last

/-- `nextSite` packaged as an `Equiv` via `finRotate`. -/
def nextSiteEquiv (P : ℕ) : Fin (2*P+2) ≃ Fin (2*P+2) :=
  { toFun := IsingModel.nextSite
    invFun := (finRotate (2*P+2)).symm
    left_inv := by
      intro j
      rw [nextSite_eq_finRotate']
      exact (finRotate (2*P+2)).symm_apply_apply j
    right_inv := by
      intro j
      rw [nextSite_eq_finRotate']
      exact (finRotate (2*P+2)).apply_symm_apply j }

@[simp]
private theorem nextSiteEquiv_apply (P : ℕ) (j : Fin (2*P+2)) :
    nextSiteEquiv P j = IsingModel.nextSite j := rfl

/-- Sum reindexing along `nextSite`. -/
private lemma sum_nextSite_reindex {α : Type*} [AddCommMonoid α]
    (P : ℕ) (f : Fin (2*P+2) → α) :
    ∑ j : Fin (2*P+2), f (IsingModel.nextSite j) = ∑ j : Fin (2*P+2), f j := by
  apply Finset.sum_equiv (nextSiteEquiv P)
  · intro i; simp
  · intro i _; rfl

-- ============================================================================
-- A4.1 — Hred_x invariance under Ttilde
-- ============================================================================

/-- **A4.1.** `T̃† · Hred_x · T̃ = Hred_x`.

Source: arXiv:1906.08948v2 App. l.1365. Conjugation by `T̃` distributes through
the sum and the leading negation; each `T̃† · X_j · T̃ = X_{nextSite j}` (no sign
flip, via `Ttilde_conj_localPauliX`); the index reindexing under the
`nextSite` bijection closes. -/
theorem Ttilde_op_conj_Hred_x (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        (Hred_x_op P) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Hred_x_op P := by
  unfold Hred_x_op standardMixerOp
  rw [conj_neg]
  congr 1
  rw [conj_sum_distrib]
  have h : ∀ j : Fin (2*P+2),
      (Ttilde_op P : Qubits.NQubitOp (2*P+2))† * Qubits.localPauliX j *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
        Qubits.localPauliX (IsingModel.nextSite j) :=
    fun j ↦ Ttilde_conj_localPauliX P j
  rw [Finset.sum_congr rfl (fun j _ ↦ h j)]
  exact sum_nextSite_reindex (α := Qubits.NQubitOp (2*P+2)) P
    (fun j ↦ Qubits.localPauliX j)

-- ============================================================================
-- Section: Per-bond conjugation lemmas for chainPairInteraction
-- ============================================================================

/-- `T̃†·(A · B)·T̃ = (T̃†·A·T̃)·(T̃†·B·T̃)` by inserting `T̃ · T̃† = 1`. -/
private lemma conj_mul_factor {N : ℕ} (U : Qubits.NQubitUnitaryOp N)
    (A B : Qubits.NQubitOp N) :
    (U : Qubits.NQubitOp N)† * (A * B) * (U : Qubits.NQubitOp N) =
      ((U : Qubits.NQubitOp N)† * A * (U : Qubits.NQubitOp N)) *
        ((U : Qubits.NQubitOp N)† * B * (U : Qubits.NQubitOp N)) := by
  have hU : (U : Qubits.NQubitOp N) * (U : Qubits.NQubitOp N)† =
      (1 : Qubits.NQubitOp N) := U.unitary_right
  -- Insert U * U† = 1 between A and B in the LHS.
  have hgoal :
      ((U : Qubits.NQubitOp N)† * A * (U : Qubits.NQubitOp N)) *
        ((U : Qubits.NQubitOp N)† * B * (U : Qubits.NQubitOp N)) =
      (U : Qubits.NQubitOp N)† * A *
        ((U : Qubits.NQubitOp N) * (U : Qubits.NQubitOp N)†) * B *
        (U : Qubits.NQubitOp N) := by
    noncomm_ring
  rw [hgoal, hU]
  noncomm_ring

private lemma Ttilde_conj_chainPair_factored (P : ℕ) (j_s : Fin (2*P+2)) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        IsingModel.chainPairInteraction j_s *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      ((Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliZ j_s *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2))) *
        ((Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliZ (IsingModel.nextSite j_s) *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2))) := by
  unfold IsingModel.chainPairInteraction
  exact conj_mul_factor (Ttilde_op P) (Qubits.localPauliZ j_s)
    (Qubits.localPauliZ (IsingModel.nextSite j_s))

-- ============================================================================
-- A4.2 — Hred_z^- invariance under Ttilde (Strategy A: signed periodic sum)
-- ============================================================================

/-- Sign coefficient for each bond on the periodic ring: `+1` everywhere except
at the boundary `j = Fin.last`, where it is `-1`. -/
private def bondSign (P : ℕ) (j : Fin (2*P+2)) : ℂ :=
  if j = Fin.last (2*P+1) then -1 else 1

/-- The signed periodic bond sum
`S_pbc P = Σ_{j : Fin (2*P+2)} ε_j • chainPairInteraction j`,
where `ε_j` is `+1` except at `j = Fin.last` where `ε_j = -1`. -/
private def S_pbc (P : ℕ) : Qubits.NQubitOp (2*P+2) :=
  ∑ j : Fin (2*P+2), bondSign P j • IsingModel.chainPairInteraction j

/-- Per-bond conjugation identity in `S_pbc`-coefficient form. The sign
cancellation matches the per-bond `Ttilde_conj_Z` table. -/
private theorem Ttilde_conj_signed_bond (P : ℕ) (j : Fin (2*P+2)) :
    bondSign P j •
        ((Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
          IsingModel.chainPairInteraction j *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2))) =
      bondSign P (IsingModel.nextSite j) •
        IsingModel.chainPairInteraction (IsingModel.nextSite j) := by
  rw [Ttilde_conj_chainPair_factored]
  by_cases hj : j = Fin.last (2*P+1)
  · -- j = last: nextSite j = 0. T̃†·Z_last·T̃ = -Z_0; T̃†·Z_0·T̃ = Z_1.
    subst hj
    rw [nextSite_last']
    rw [Ttilde_conj_Z_last]
    have h0_ne_last : (0 : Fin (2*P+2)) ≠ Fin.last (2*P+1) := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_last] at this
      simp at this
    rw [Ttilde_conj_Z_of_ne_last P (0 : Fin (2*P+2)) h0_ne_last]
    have hbsign_last : bondSign P (Fin.last (2*P+1) : Fin (2*P+2)) = -1 := by
      unfold bondSign; rw [if_pos rfl]
    have hbsign_0 : bondSign P (0 : Fin (2*P+2)) = 1 := by
      unfold bondSign; rw [if_neg h0_ne_last]
    rw [hbsign_last, hbsign_0]
    unfold IsingModel.chainPairInteraction
    rw [Matrix.neg_mul]
    rw [show ((-1 : ℂ)) • (-(Qubits.localPauliZ (0 : Fin (2*P+2)) *
            Qubits.localPauliZ (IsingModel.nextSite (0 : Fin (2*P+2))))) =
        (1 : ℂ) • (Qubits.localPauliZ (0 : Fin (2*P+2)) *
          Qubits.localPauliZ (IsingModel.nextSite (0 : Fin (2*P+2)))) from by
      rw [neg_one_smul, one_smul, neg_neg]]
  · rw [Ttilde_conj_Z_of_ne_last P j hj]
    by_cases hnj : IsingModel.nextSite j = Fin.last (2*P+1)
    · -- nextSite j = last. First rewrite bondSign on nextSite j side.
      have hbsign_j : bondSign P j = 1 := by
        unfold bondSign; rw [if_neg hj]
      have hbsign_next : bondSign P (IsingModel.nextSite j) = -1 := by
        unfold bondSign; rw [hnj, if_pos rfl]
      rw [hbsign_j, hbsign_next, hnj]
      rw [Ttilde_conj_Z_last]
      unfold IsingModel.chainPairInteraction
      rw [Matrix.mul_neg]
      rw [nextSite_last']
      rw [neg_one_smul, one_smul]
    · rw [Ttilde_conj_Z_of_ne_last P (IsingModel.nextSite j) hnj]
      have hbsign_j : bondSign P j = 1 := by
        unfold bondSign; rw [if_neg hj]
      have hbsign_next : bondSign P (IsingModel.nextSite j) = 1 := by
        unfold bondSign; rw [if_neg hnj]
      rw [hbsign_j, hbsign_next]
      rfl

/-- The signed periodic bond sum is invariant under `T̃`-conjugation. -/
private theorem Ttilde_conj_S_pbc (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        S_pbc P *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      S_pbc P := by
  unfold S_pbc
  rw [conj_sum_distrib]
  have hsmul : ∀ j : Fin (2*P+2),
      (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
          (bondSign P j • IsingModel.chainPairInteraction j) *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
        bondSign P j •
          ((Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
            IsingModel.chainPairInteraction j *
            (Ttilde_op P : Qubits.NQubitOp (2*P+2))) :=
    fun j ↦ conj_smul _ _ _
  rw [Finset.sum_congr rfl (fun j _ ↦ hsmul j)]
  -- Now: Σ ε_j • (T̃† · chainPair j · T̃) = Σ ε_j • chainPair j
  -- Reindex the RHS via nextSite (preimage), then use Ttilde_conj_signed_bond.
  rw [show (∑ j : Fin (2*P+2), bondSign P j • IsingModel.chainPairInteraction j) =
        ∑ j : Fin (2*P+2),
          bondSign P (IsingModel.nextSite j) •
            IsingModel.chainPairInteraction (IsingModel.nextSite j) from
    (sum_nextSite_reindex (α := Qubits.NQubitOp (2*P+2)) P
      (fun j ↦ bondSign P j • IsingModel.chainPairInteraction j)).symm]
  exact Finset.sum_congr rfl (fun j _ ↦ Ttilde_conj_signed_bond P j)

/-- `Hred_z_pm false P + N_R • I = S_pbc P`. -/
private lemma Hred_z_pm_false_add_NR_eq_S_pbc (P : ℕ) :
    Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) =
      S_pbc P := by
  unfold Hred_z_pm Hred_z_body Hred_z_boundary S_pbc
  -- Step 1: split the LHS sum and boundary, identify bond and -1 parts.
  -- Use Fin.sum_univ_castSucc on RHS to split body + last.
  have hsum_split :
      (∑ j : Fin (2*P+2), bondSign P j • IsingModel.chainPairInteraction j) =
        (∑ i : Fin (2*P+1),
          bondSign P (i.castSucc : Fin (2*P+2)) •
            IsingModel.chainPairInteraction (i.castSucc : Fin (2*P+2))) +
        bondSign P (Fin.last (2*P+1) : Fin (2*P+2)) •
            IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) :=
    Fin.sum_univ_castSucc _
  rw [hsum_split]
  have hbond_interior : ∀ i : Fin (2*P+1),
      bondSign P (i.castSucc : Fin (2*P+2)) = 1 := by
    intro i
    unfold bondSign
    rw [if_neg]
    intro h
    have hi : (i.castSucc : Fin (2*P+2)).val = (Fin.last (2*P+1) : Fin (2*P+2)).val :=
      congrArg Fin.val h
    rw [Fin.val_castSucc, Fin.val_last] at hi
    have := i.isLt
    omega
  have hinterior :
      (∑ i : Fin (2*P+1),
          bondSign P (i.castSucc : Fin (2*P+2)) •
            IsingModel.chainPairInteraction (i.castSucc : Fin (2*P+2))) =
        ∑ i : Fin (2*P+1),
          IsingModel.chainPairInteraction (i.castSucc : Fin (2*P+2)) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hbond_interior i, one_smul]
  rw [hinterior]
  have hbond_last : bondSign P (Fin.last (2*P+1) : Fin (2*P+2)) = -1 := by
    unfold bondSign; rw [if_pos rfl]
  rw [hbond_last]
  -- LHS: (Σ_i (cP - 1)) + ((-1) • cP last - 1) + N_R • I.
  -- RHS: (Σ_i cP) + (-1) • cP last.
  -- Split LHS body sum.
  have hLHS_body :
      (∑ k : Fin (2*P+1),
        (IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
          (1 : Qubits.NQubitOp (2*P+2)))) =
      (∑ i : Fin (2*P+1),
          IsingModel.chainPairInteraction (i.castSucc : Fin (2*P+2))) -
        ∑ _k : Fin (2*P+1), (1 : Qubits.NQubitOp (2*P+2)) := by
    rw [Finset.sum_sub_distrib]
  rw [hLHS_body]
  -- Convert Σ_{k : Fin (2P+1)} 1 to (2P+1 : ℂ) • 1 via Finset.sum_const.
  have hconst_sum :
      (∑ _k : Fin (2*P+1), (1 : Qubits.NQubitOp (2*P+2))) =
        ((2*P+1 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [show ((2*P+1 : ℕ)) • (1 : Qubits.NQubitOp (2*P+2)) =
        ((2*P+1 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) from by
      rw [Nat.cast_smul_eq_nsmul ℂ]]
  rw [hconst_sum]
  -- Goal:
  -- ((Σ cP) - ((2P+1) • 1)) + ((-1) • cP last - 1) + (2P+2) • 1
  --  = (Σ cP) + (-1) • cP last
  -- Use linear_combination over the smul algebra.
  have hcast : ((2*P+2 : ℕ) : ℂ) =
      ((2*P+1 : ℕ) : ℂ) + (1 : ℂ) := by push_cast; ring
  rw [hcast, add_smul, one_smul]
  abel

/-- **A4.2.** `T̃† · Hred_z^- · T̃ = Hred_z^-`.

Source: arXiv:1906.08948v2 App. l.1362. Via the signed-periodic-sum packaging
`S_pbc = Hred_z^- + N_R • I`: `T̃` conjugation preserves `S_pbc` (per-bond sign
flips reindex through `nextSite`); subtract `N_R • I` (which is `T̃`-invariant
because `T̃†·I·T̃ = I`) to conclude. -/
theorem Ttilde_op_conj_Hred_z_pm_false (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        (Hred_z_pm false P) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Hred_z_pm false P := by
  have hpack := Hred_z_pm_false_add_NR_eq_S_pbc P
  have hsub : Hred_z_pm false P =
      S_pbc P - ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) := by
    rw [← hpack]; abel
  rw [hsub, conj_sub]
  have hcI : (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        (((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) := by
    rw [conj_smul, conj_one]
  rw [hcI, Ttilde_conj_S_pbc]

-- ============================================================================
-- A4.3 — Ttilde · |ψ̃⟩ = |ψ̃⟩
-- ============================================================================

/-- A permutation matrix acting on the uniform-state vector gives the same
vector (the uniform vector is constant, and a permutation reorders it). -/
private theorem permMatrix_mulVec_uniformKet {n : ℕ} [NeZero n]
    (σ : Equiv.Perm (Fin n)) :
    (Equiv.Perm.permMatrix ℂ σ).mulVec (uniformKet n).vec =
      (uniformKet n).vec := by
  funext j
  rw [Matrix.permMatrix_mulVec]
  rfl

/-- `T_op · uniformState = uniformState` at the ket level. -/
private theorem T_op_uniformKet (P : ℕ) :
    Matrix.mulVec (T_op P : Qubits.NQubitOp (2*P+2)) (uniformKet
        (Qubits.NQubitDim (2*P+2))).vec =
      (uniformKet (Qubits.NQubitDim (2*P+2))).vec := by
  rw [T_op_toOp]
  exact permMatrix_mulVec_uniformKet (T_perm P)

/-- `flipBitAt z j` packaged as an involutive `Equiv`. -/
private def flipBitAtEquiv (N : ℕ) (j : Fin N) :
    Qubits.BitString N ≃ Qubits.BitString N :=
  { toFun := fun z ↦ Qubits.flipBitAt z j
    invFun := fun z ↦ Qubits.flipBitAt z j
    left_inv := fun z ↦ Qubits.flipBitAt_involutive z j
    right_inv := fun z ↦ Qubits.flipBitAt_involutive z j }

/-- `localPauliX 0 · uniformState = uniformState`. The local Pauli `X_j` acts
on each computational basis ket by flipping bit `j`, which is a basis-set
permutation. The uniform state is the (1/√D)-weighted sum of all basis kets,
so any basis-set permutation leaves it fixed. -/
private theorem localPauliX_zero_mulVec_uniformKet (P : ℕ) :
    Matrix.mulVec (Qubits.localPauliX (0 : Fin (2*P+2)))
        (uniformKet (Qubits.NQubitDim (2*P+2))).vec =
      (uniformKet (Qubits.NQubitDim (2*P+2))).vec := by
  -- localPauliX 0 · stdKet (bitStringEquiv b) = stdKet (bitStringEquiv (flipBit b 0)).
  -- The uniform vec equals (1/sqrt D) · ones-vec, and ones-vec = Σ_b stdKet(...). The sum
  -- is invariant under the flipBitAt 0 reindex bijection.
  -- The clean way: prove (localPauliX 0) on ones = ones, then scale.
  -- Equivalent: every row of localPauliX 0 sums to 1.
  --
  -- Even simpler: since localPauliX 0 is an involution (X² = 1), its mulVec
  -- on any constant vector equals itself ONLY IF we know X · ones = ones.
  -- Use that localPauliX 0 mulVec preserves the constant-c vector since the
  -- sum-of-stdKets is invariant under flipBit_0 reindexing.
  -- This is essentially permMatrix-style. Cleanest: by `Ket.ext` + a single
  -- `congrFun` on the basis sum.
  -- We compute via the bit-string structure.
  funext i
  -- (M *ᵥ const) i = (Σ_j M i j) * const.
  -- We need Σ_j (localPauliX 0) i j = 1.
  -- M *ᵥ v at i = Σ_j M i j * v j; since v j = c is constant, this is c * Σ_j M i j.
  -- We compute Σ_j (localPauliX 0) i j via a representation as a permutation matrix.
  -- Concrete: localPauliX 0 is the permutation matrix of bitStringEquiv ∘ flipBitAt 0 ∘ bitStringEquiv.symm.
  -- Per the structure of localOp X with X = Pauli X, this permutation has each row sum = 1.
  -- We bound this by appealing to the basis-action lemma.
  -- Strategy: use that
  --   localPauliX 0 *ᵥ ones = ones,
  -- which follows from localPauliX_on_basis + the bijection.
  have hones : Matrix.mulVec (Qubits.localPauliX (0 : Fin (2*P+2)))
      (fun _ ↦ (1 : ℂ)) = fun _ ↦ (1 : ℂ) := by
    -- Decompose ones = Σ_b stdKet (bitStringEquiv b) at the vec level.
    funext k
    have hsum_ones :
        ((fun (_ : Fin (Qubits.NQubitDim (2*P+2))) ↦ (1 : ℂ))) =
          ∑ b : Qubits.BitString (2*P+2),
            (stdKet (Qubits.NQubitDim (2*P+2))
              (Qubits.bitStringEquiv (2*P+2) b)).vec := by
      funext l
      rw [show (∑ b : Qubits.BitString (2*P+2),
            (stdKet (Qubits.NQubitDim (2*P+2))
              (Qubits.bitStringEquiv (2*P+2) b)).vec) l =
          ∑ b : Qubits.BitString (2*P+2),
            (stdKet (Qubits.NQubitDim (2*P+2))
              (Qubits.bitStringEquiv (2*P+2) b)).vec l from
        Finset.sum_apply _ _ _]
      symm
      rw [Finset.sum_eq_single ((Qubits.bitStringEquiv (2*P+2)).symm l)]
      · rw [stdKet_apply]
        have happ : Qubits.bitStringEquiv (2*P+2) ((Qubits.bitStringEquiv (2*P+2)).symm l) = l :=
          (Qubits.bitStringEquiv (2*P+2)).apply_symm_apply l
        rw [if_pos happ]
      · intro b _ hb
        rw [stdKet_apply, if_neg]
        intro hl
        apply hb
        apply (Qubits.bitStringEquiv (2*P+2)).injective
        rw [(Qubits.bitStringEquiv (2*P+2)).apply_symm_apply, hl]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsum_ones]
    rw [Matrix.mulVec_sum]
    -- mulVec M (Σ_b f b) = Σ_b mulVec M (f b). Now apply localPauliX_on_basis:
    -- M *ᵥ stdKet (bitStringEquiv b) = stdKet (bitStringEquiv (flipBitAt b 0)).
    -- Then reindex via flipBitAtEquiv.
    have hbasis_step : ∀ b : Qubits.BitString (2*P+2),
        Matrix.mulVec (Qubits.localPauliX (0 : Fin (2*P+2)))
          (stdKet (Qubits.NQubitDim (2*P+2))
            (Qubits.bitStringEquiv (2*P+2) b)).vec =
        (stdKet (Qubits.NQubitDim (2*P+2))
          (Qubits.bitStringEquiv (2*P+2)
            (Qubits.flipBitAt b (0 : Fin (2*P+2))))).vec := by
      intro b
      have h := Qubits.localPauliX_on_basis (j := (0 : Fin (2*P+2))) (z := b)
      have h' := congrArg Quantum.Operators.Ket.vec h
      exact h'
    rw [Finset.sum_apply,
        Finset.sum_congr rfl (fun b _ ↦ congrFun (hbasis_step b) k)]
    -- Reindex b ↦ flipBitAt b 0 via flipBitAtEquiv:
    have hreindex : (∑ b : Qubits.BitString (2*P+2),
            (stdKet (Qubits.NQubitDim (2*P+2)) (Qubits.bitStringEquiv (2*P+2)
              (Qubits.flipBitAt b (0 : Fin (2*P+2))))).vec k) =
        ∑ b : Qubits.BitString (2*P+2),
            (stdKet (Qubits.NQubitDim (2*P+2)) (Qubits.bitStringEquiv (2*P+2) b)).vec k := by
      apply Finset.sum_equiv (flipBitAtEquiv (2*P+2) (0 : Fin (2*P+2)))
      · intro b; simp
      · intro b _; rfl
    rw [hreindex]
    -- Σ_b stdKet (bitStringEquiv b)_k = 1.
    rw [Finset.sum_eq_single ((Qubits.bitStringEquiv (2*P+2)).symm k)]
    · rw [stdKet_apply]
      have happ : Qubits.bitStringEquiv (2*P+2) ((Qubits.bitStringEquiv (2*P+2)).symm k) = k :=
        (Qubits.bitStringEquiv (2*P+2)).apply_symm_apply k
      rw [if_pos happ]
    · intro b _ hb
      rw [stdKet_apply, if_neg]
      intro hk
      apply hb
      apply (Qubits.bitStringEquiv (2*P+2)).injective
      rw [(Qubits.bitStringEquiv (2*P+2)).apply_symm_apply, hk]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- uniformKet vec = c · ones-vec.
  have huniform_eq : (uniformKet (Qubits.NQubitDim (2*P+2))).vec =
      ((1 / Real.sqrt ((Qubits.NQubitDim (2*P+2) : ℕ) : ℝ) : ℝ) : ℂ) •
        (fun (_ : Fin (Qubits.NQubitDim (2*P+2))) ↦ (1 : ℂ)) := by
    funext k
    show ((1 / Real.sqrt ((Qubits.NQubitDim (2*P+2) : ℕ) : ℝ) : ℝ) : ℂ) =
      ((1 / Real.sqrt ((Qubits.NQubitDim (2*P+2) : ℕ) : ℝ) : ℝ) : ℂ) • (1 : ℂ)
    rw [smul_eq_mul, mul_one]
  rw [huniform_eq]
  rw [Matrix.mulVec_smul]
  rw [hones]

/-- `T̃ · uniformState = uniformState`. -/
private theorem Ttilde_op_mulVec_uniformKet (P : ℕ) :
    Matrix.mulVec (Ttilde_op P : Qubits.NQubitOp (2*P+2))
        (uniformKet (Qubits.NQubitDim (2*P+2))).vec =
      (uniformKet (Qubits.NQubitDim (2*P+2))).vec := by
  rw [Ttilde_op_toOp]
  rw [← Matrix.mulVec_mulVec]
  rw [localPauliX_zero_mulVec_uniformKet, T_op_uniformKet]

/-- Helper: if a unitary `U` satisfies `U† · Hop · U = Hop` for an operator
`Hop`, then `U` commutes with `exp(α • Hop)` for any scalar `α`. Uses
`Matrix.exp_units_conj'`. -/
private theorem exp_commute_of_conj {N : ℕ}
    (U : Qubits.NQubitUnitaryOp N) (Hop : Qubits.NQubitOp N) (α : ℂ)
    (hUH : (U : Qubits.NQubitOp N)† * Hop * (U : Qubits.NQubitOp N) = Hop) :
    (U : Qubits.NQubitOp N) * NormedSpace.exp (α • Hop) =
      NormedSpace.exp (α • Hop) * (U : Qubits.NQubitOp N) := by
  -- Construct U as Matrix unit.
  let uMat : (Matrix (Fin (Qubits.NQubitDim N)) (Fin (Qubits.NQubitDim N)) ℂ)ˣ :=
    { val := (U : Qubits.NQubitOp N)
      inv := (U : Qubits.NQubitOp N)†
      val_inv := U.unitary_right
      inv_val := U.unitary_left }
  have hUHsmul :
      (U : Qubits.NQubitOp N)† * (α • Hop) * (U : Qubits.NQubitOp N) = α • Hop := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hUH]
  have hexp_conj :=
    Matrix.exp_units_conj' uMat (α • Hop)
  -- hexp_conj : exp(uMat⁻¹ * (α • Hop) * uMat) = uMat⁻¹ * exp(α • Hop) * uMat.
  -- Replace uMat / uMat⁻¹ with U / U†.
  change NormedSpace.exp ((U : Qubits.NQubitOp N)† * (α • Hop) *
      (U : Qubits.NQubitOp N)) =
    (U : Qubits.NQubitOp N)† * NormedSpace.exp (α • Hop) *
      (U : Qubits.NQubitOp N) at hexp_conj
  rw [hUHsmul] at hexp_conj
  -- hexp_conj : exp(α • Hop) = U† * exp(α • Hop) * U.
  -- Multiply both sides on the left by U.
  have hkey := congrArg ((U : Qubits.NQubitOp N) * ·) hexp_conj
  simp only at hkey
  rw [hkey]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, U.unitary_right, Matrix.one_mul]

/-- `T̃` commutes with `mixerExponential (Hred_x_hamiltonian P) β`. -/
private theorem Ttilde_commutes_mixerExponential (P : ℕ) (β : ℝ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2)) *
        mixerExponential (Hred_x_hamiltonian P) β =
      mixerExponential (Hred_x_hamiltonian P) β *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) := by
  unfold mixerExponential
  have hconj : (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        ((Hred_x_hamiltonian P) : Qubits.NQubitOp (2*P+2)) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      ((Hred_x_hamiltonian P) : Qubits.NQubitOp (2*P+2)) := by
    rw [Hred_x_hamiltonian_toOp]
    exact Ttilde_op_conj_Hred_x P
  exact exp_commute_of_conj (Ttilde_op P) _ ((-β * Complex.I : ℂ)) hconj

/-- `T̃` commutes with `costExponential (Hred_z_hamiltonian false P) γ`. -/
private theorem Ttilde_commutes_costExponential (P : ℕ) (γ : ℝ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2)) *
        costExponential (Hred_z_hamiltonian false P) γ =
      costExponential (Hred_z_hamiltonian false P) γ *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) := by
  unfold costExponential
  have hconj : (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        ((Hred_z_hamiltonian false P) : Qubits.NQubitOp (2*P+2)) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      ((Hred_z_hamiltonian false P) : Qubits.NQubitOp (2*P+2)) := by
    rw [Hred_z_hamiltonian_toOp]
    exact Ttilde_op_conj_Hred_z_pm_false P
  exact exp_commute_of_conj (Ttilde_op P) _ ((-γ * Complex.I : ℂ)) hconj

/-- The reduced-chain QAOA state at chain depth `P` and *separate* QAOA depth
`p`, with initial state `ψ0`. -/
private def genReducedQAOA (P p : ℕ) (γ β : Fin p → ℝ)
    (ψ0 : Qubits.NQubitNormKet (2*P+2)) : Qubits.NQubitNormKet (2*P+2) :=
  qaoaState
    (costUnitaryFamily (reducedChainQAOAExp false P).toQAOAHamiltonians γ)
    (mixerUnitaryFamily (reducedChainQAOAExp false P).toQAOAHamiltonians β)
    ψ0

private theorem genReducedQAOA_zero (P : ℕ) (ψ0 : Qubits.NQubitNormKet (2*P+2)) :
    genReducedQAOA P 0 (fun i ↦ nomatch i) (fun i ↦ nomatch i) ψ0 = ψ0 := by
  unfold genReducedQAOA
  exact qaoaState_zero ψ0

private theorem genReducedQAOA_succ (P p : ℕ) (γ β : Fin (p+1) → ℝ)
    (ψ0 : Qubits.NQubitNormKet (2*P+2)) :
    genReducedQAOA P (p+1) γ β ψ0 =
      genReducedQAOA P p (tailFamily γ) (tailFamily β)
        (applyLayer
          ((reducedChainQAOAExp false P).costUnitary (γ 0))
          ((reducedChainQAOAExp false P).mixerUnitary (β 0))
          ψ0) := rfl

/-- For any initial state `ψ0` with `T̃ · ψ0 = ψ0`, the depth-`p` reduced-QAOA
state inherits the invariance: `T̃ · genReducedQAOA P p γ β ψ0 =
genReducedQAOA P p γ β ψ0`. -/
private theorem Ttilde_op_apply_genReducedQAOA (P : ℕ) :
    ∀ p : ℕ, ∀ γ β : Fin p → ℝ, ∀ ψ0 : Qubits.NQubitNormKet (2*P+2),
      Matrix.mulVec (Ttilde_op P : Qubits.NQubitOp (2*P+2)) ψ0.toKet.vec =
        ψ0.toKet.vec →
        Matrix.mulVec (Ttilde_op P : Qubits.NQubitOp (2*P+2))
            (genReducedQAOA P p γ β ψ0).toKet.vec =
          (genReducedQAOA P p γ β ψ0).toKet.vec := by
  intro p
  induction p with
  | zero =>
    intro γ β ψ0 hψ0
    have hγ : γ = fun i ↦ nomatch i := by funext i; exact i.elim0
    have hβ : β = fun i ↦ nomatch i := by funext i; exact i.elim0
    rw [hγ, hβ, genReducedQAOA_zero]
    exact hψ0
  | succ p IH =>
    intro γ β ψ0 hψ0
    rw [genReducedQAOA_succ]
    apply IH
    -- Need: T̃ · (applyLayer cost mixer ψ0).toKet = (applyLayer ...).toKet
    -- (applyLayer C M ψ).vec = M.toOp *ᵥ (C.toOp *ᵥ ψ.vec)
    have happly : (applyLayer
          ((reducedChainQAOAExp false P).costUnitary (γ 0))
          ((reducedChainQAOAExp false P).mixerUnitary (β 0))
          ψ0).toKet.vec =
        Matrix.mulVec
          (mixerExponential (Hred_x_hamiltonian P) (β 0))
          (Matrix.mulVec
            (costExponential (Hred_z_hamiltonian false P) (γ 0)) ψ0.toKet.vec) := by
      unfold applyLayer
      rfl
    rw [happly]
    -- Goal: T̃ *ᵥ (mix *ᵥ (cost *ᵥ ψ0.vec)) = (mix *ᵥ (cost *ᵥ ψ0.vec))
    have hmix := Ttilde_commutes_mixerExponential P (β 0)
    have hcost := Ttilde_commutes_costExponential P (γ 0)
    -- Convert nested mulVecs to a single one: (T̃ * mix * cost) *ᵥ ψ0.vec.
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    -- We now have: ((T̃ * mix) * cost) *ᵥ ψ0.vec = ?
    -- Combine via commutation to get (mix * cost * T̃) *ᵥ ψ0.vec.
    have hmul_eq :
        ((Ttilde_op P : Qubits.NQubitOp (2*P+2)) *
            mixerExponential (Hred_x_hamiltonian P) (β 0)) *
            costExponential (Hred_z_hamiltonian false P) (γ 0) =
          mixerExponential (Hred_x_hamiltonian P) (β 0) *
            costExponential (Hred_z_hamiltonian false P) (γ 0) *
            (Ttilde_op P : Qubits.NQubitOp (2*P+2)) := by
      rw [hmix, Matrix.mul_assoc, hcost, ← Matrix.mul_assoc]
    rw [hmul_eq]
    -- Now: (mix * cost * T̃) *ᵥ ψ0.vec = mix *ᵥ (cost *ᵥ (T̃ *ᵥ ψ0.vec))
    --                                   = mix *ᵥ (cost *ᵥ ψ0.vec).
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hψ0]

/-- **A4.3.** `T̃ · |ψ̃_P⟩ = |ψ̃_P⟩`.

Source: arXiv:1906.08948v2 App. l.1373 (eq. `psi_tilde_traslation_invar`). -/
theorem Ttilde_op_apply_psiTilde (P : ℕ) (γ β : Fin P → ℝ) :
    Matrix.mulVec (Ttilde_op P : Qubits.NQubitOp (2*P+2))
        (psiTilde false P γ β).toKet.vec =
      (psiTilde false P γ β).toKet.vec := by
  have heq : psiTilde false P γ β = genReducedQAOA P P γ β (psiTilde_init P) := rfl
  rw [heq]
  apply Ttilde_op_apply_genReducedQAOA P P γ β (psiTilde_init P)
  unfold psiTilde_init
  show Matrix.mulVec _ (uniformState (IsingChainQAOADim (2*P+2))).toKet.vec = _
  exact Ttilde_op_mulVec_uniformKet P

-- ============================================================================
-- A4.4a — Sum-of-conjugates decomposition (at fixed j_s = 0)
-- ============================================================================

/-!
We prove the sum-of-conjugates identity at the fixed starting bond `j_s = 0`
via the `S_pbc` packaging used in A4.2. Numerical validation shows the operator identity
`Hred_z^- + N_R • I = Σ_n (T̃†)^n · cP j_s · T̃^n` is **false** at
`j_s = Fin.last (2*P+1)` (Frobenius distance ≥ 16 at P=1), so we drop the
free `j_s` parameter from the source's presentation-level form and prove the
specialization at `j_s = 0`. Downstream consumers (A4.4b, A6) only use the
identity at this fixed bond.

The proof strategy: iterate `Ttilde_conj_signed_bond` (A4.2's per-bond
sign-tracker) starting from the interior bond `j = 0`. The accumulated identity
after `n` steps is
  `(T̃^n)† · cP(0) · T̃^n = ε_(orbit_n 0) • cP(orbit_n 0)`,
where `orbit_n j = (nextSiteEquiv P)^n j` is the `n`-fold next-site iterate.
Summing over `n : Fin N_R` and reindexing through the orbit bijection
`n ↦ orbit_n 0` (which is the identity on `Fin (2P+2)` since `finRotate^n 0 = n`)
recovers `S_pbc P = Hred_z^- + N_R • I`.
-/

/-- Iterating `Ttilde`-conjugation on `chainPairInteraction 0`. The `n`-fold
conjugation transports the bond label from `0` to `orbit_n 0` with a single
accumulated sign `ε_(orbit_n 0) ∈ {±1}` tracked by `bondSign`. The key form is
the *single signed product* (not a ratio of signs), which composes cleanly under
the per-step `Ttilde_conj_signed_bond` identity. -/
private theorem Ttilde_pow_conj_chainPair_zero (P : ℕ) :
    ∀ n : ℕ,
      ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n)† *
          IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
          ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n) =
        bondSign P (((nextSiteEquiv P)^n) (0 : Fin (2*P+2))) •
          IsingModel.chainPairInteraction
            (((nextSiteEquiv P)^n) (0 : Fin (2*P+2))) := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, pow_zero]
    show ((1 : Qubits.NQubitOp (2*P+2))† *
        IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
          (1 : Qubits.NQubitOp (2*P+2))) =
      bondSign P (((nextSiteEquiv P)^0) (0 : Fin (2*P+2))) •
        IsingModel.chainPairInteraction
          (((nextSiteEquiv P)^0) (0 : Fin (2*P+2)))
    rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    -- pow_zero gives Equiv.Perm.one which acts as identity; bondSign at 0 = 1.
    have horbit : ((nextSiteEquiv P)^0) (0 : Fin (2*P+2)) = (0 : Fin (2*P+2)) := by
      rw [pow_zero]; rfl
    rw [horbit]
    have h0_ne_last : (0 : Fin (2*P+2)) ≠ Fin.last (2*P+1) := by
      intro h
      have := congrArg Fin.val h
      rw [Fin.val_last] at this
      simp at this
    have hbsign_zero : bondSign P (0 : Fin (2*P+2)) = 1 := by
      unfold bondSign; rw [if_neg h0_ne_last]
    rw [hbsign_zero, one_smul]
  | succ k IH =>
    -- (T̃^(k+1))† * cP(0) * T̃^(k+1)
    --   = T̃† * ((T̃^k)† * cP(0) * T̃^k) * T̃                  -- reassociate
    --   = T̃† * (ε_(orbit_k 0) • cP(orbit_k 0)) * T̃             -- IH
    --   = ε_(orbit_k 0) • (T̃† * cP(orbit_k 0) * T̃)             -- linear
    --   = ε_(nextSite (orbit_k 0)) • cP(nextSite (orbit_k 0))   -- Ttilde_conj_signed_bond
    --   = ε_(orbit_(k+1) 0) • cP(orbit_(k+1) 0).
    -- pow_succ : a^(n+1) = a^n * a, and (a*b)† = b† * a†.
    rw [show (Ttilde_op P : Qubits.NQubitOp (2*P+2))^(k+1) =
        ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^k) *
          (Ttilde_op P : Qubits.NQubitOp (2*P+2)) from pow_succ _ _]
    rw [Matrix.conjTranspose_mul]
    -- Reassociate: (T̃† * (T̃^k)†) * cP(0) * (T̃^k * T̃)
    --             = T̃† * ((T̃^k)† * cP(0) * T̃^k) * T̃.
    have hreassoc :
        (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
            ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^k)† *
            IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
            (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^k) *
              (Ttilde_op P : Qubits.NQubitOp (2*P+2))) =
        (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
            (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^k)† *
              IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
              ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^k)) *
            (Ttilde_op P : Qubits.NQubitOp (2*P+2)) := by
      noncomm_ring
    rw [hreassoc, IH]
    -- Now: T̃† * (ε_(orbit_k 0) • cP(orbit_k 0)) * T̃
    rw [conj_smul]
    -- Now: ε_(orbit_k 0) • (T̃† * cP(orbit_k 0) * T̃).
    -- Apply Ttilde_conj_signed_bond at j = orbit_k 0 to get
    -- ε_(orbit_k 0) • (T̃† · cP(orbit_k 0) · T̃) = ε_(nextSite (orbit_k 0)) • cP(nextSite (orbit_k 0)).
    rw [Ttilde_conj_signed_bond P (((nextSiteEquiv P)^k) (0 : Fin (2*P+2)))]
    -- Goal: ε_(nextSite (orbit_k 0)) • cP(nextSite (orbit_k 0))
    --       = ε_(orbit_(k+1) 0) • cP(orbit_(k+1) 0)
    -- Use pow_succ' : f^(k+1) = f * f^k, then Perm.mul_apply : (f*g) x = f (g x).
    have horbit_succ :
        ((nextSiteEquiv P)^(k+1)) (0 : Fin (2*P+2)) =
          IsingModel.nextSite (((nextSiteEquiv P)^k) (0 : Fin (2*P+2))) := by
      rw [pow_succ']
      show ((nextSiteEquiv P) * (nextSiteEquiv P)^k) (0 : Fin (2*P+2)) =
          IsingModel.nextSite _
      rw [Equiv.Perm.mul_apply]
      -- Now: (nextSiteEquiv P) (((nextSiteEquiv P)^k) 0) = nextSite (((nextSiteEquiv P)^k) 0)
      rw [nextSiteEquiv_apply]
    rw [horbit_succ]

/-- The orbit of `0` under `nextSiteEquiv` iteration matches the `Fin (2*P+2)`
indexing: `((nextSiteEquiv P)^k) 0 = ⟨k, _⟩` when `k < 2*P+2`. -/
private lemma orbit_zero_val (P : ℕ) :
    ∀ k : ℕ, k < 2*P+2 →
      (((nextSiteEquiv P)^k) (0 : Fin (2*P+2))).val = k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k IH =>
    intro hk
    have hk_lt : k < 2*P+2 := by omega
    have IH' := IH hk_lt
    rw [pow_succ', Equiv.Perm.mul_apply, nextSiteEquiv_apply,
        IsingModel.nextSite_val, IH']
    -- (k + 1) % (2*P+2) = k + 1 because k + 1 < 2*P+2.
    exact Nat.mod_eq_of_lt hk

/-- Orbit-from-zero bijection: `n ↦ ((nextSiteEquiv P)^n.val) 0` packaged as an
`Equiv` on `Fin (2*P+2)`. The orbit visits every site exactly once, and in fact
is the *identity* on `Fin (2*P+2)` (since `finRotate^k 0 = k` for `k < N_R`). -/
private def orbitFromZeroEquiv (P : ℕ) : Fin (2*P+2) ≃ Fin (2*P+2) where
  toFun := fun n ↦ ((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2))
  invFun := id
  left_inv := by
    intro n
    apply Fin.ext
    show (((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2))).val = n.val
    exact orbit_zero_val P n.val n.isLt
  right_inv := by
    intro n
    apply Fin.ext
    show (((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2))).val = n.val
    exact orbit_zero_val P n.val n.isLt

@[simp]
private lemma orbitFromZeroEquiv_apply (P : ℕ) (n : Fin (2*P+2)) :
    (orbitFromZeroEquiv P) n = ((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2)) := rfl

/-- **A4.4a.** `Hred_z^- + N_R • I = Σ_n (T̃†)^n · chainPair 0 · T̃^n`.

Source: arXiv:1906.08948v2 App. l.1381 (eq. `Hred_traslation_sum`).

**Note on signature.** Numerical validation proved
that the operator equality is FALSE at `j_s = Fin.last (2*P+1)` (Frobenius
distance ≥ 16). The source's free-`j_s` form is presentation-level; the
mathematical content holds at any fixed *interior* bond (i.e. `j_s ≠ last`).
We fix `j_s = 0` here since downstream uses only need a single bond, and
`0` is the cleanest representative. -/
theorem Hred_z_pm_false_eq_sum_translates (P : ℕ) :
    Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)) =
      ∑ n : Fin (2*P+2),
        ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val)† *
          IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
          ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val) := by
  rw [Hred_z_pm_false_add_NR_eq_S_pbc]
  unfold S_pbc
  -- LHS: Σ_j ε_j • cP(j).
  -- RHS: Σ_n (T̃^n)† · cP(0) · T̃^n
  --    = Σ_n ε_(orbit_n 0) • cP(orbit_n 0)         -- by Ttilde_pow_conj_chainPair_zero
  -- Reindex through orbitFromZeroEquiv to recover LHS.
  symm
  have hterm : ∀ n : Fin (2*P+2),
      ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val)† *
          IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
          ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val) =
        bondSign P (((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2))) •
          IsingModel.chainPairInteraction
            (((nextSiteEquiv P)^n.val) (0 : Fin (2*P+2))) :=
    fun n ↦ Ttilde_pow_conj_chainPair_zero P n.val
  rw [Finset.sum_congr rfl (fun n _ ↦ hterm n)]
  -- Now: Σ_n ε_(orbit_n.val 0) • cP(orbit_n.val 0) = Σ_j ε_j • cP(j).
  -- Reindex via orbitFromZeroEquiv.
  apply Finset.sum_equiv (orbitFromZeroEquiv P)
  · intro i; simp
  · intro i _; simp [orbitFromZeroEquiv_apply]

-- ============================================================================
-- A4.4b — Averaging identity
-- ============================================================================

/-- `T̃^n · |ψ̃⟩ = |ψ̃⟩` for every `n : ℕ`. -/
private theorem Ttilde_pow_apply_psiTilde (P : ℕ) (γ β : Fin P → ℝ) :
    ∀ n : ℕ,
      Matrix.mulVec (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n))
          (psiTilde false P γ β).toKet.vec =
        (psiTilde false P γ β).toKet.vec := by
  intro n
  induction n with
  | zero =>
    rw [pow_zero, Matrix.one_mulVec]
  | succ k IH =>
    rw [pow_succ]
    rw [← Matrix.mulVec_mulVec]
    rw [Ttilde_op_apply_psiTilde P γ β, IH]

/-- For any operator `A`, expectation invariance under iterated `T̃`-conjugation. -/
private theorem expectation_invariant_under_TtildePow (P : ℕ) (γ β : Fin P → ℝ)
    (A : Qubits.NQubitOp (2*P+2)) (n : ℕ) :
    dotProduct (star (psiTilde false P γ β).toKet.vec)
        (Matrix.mulVec
          (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n)† * A *
            ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n))
          (psiTilde false P γ β).toKet.vec) =
      dotProduct (star (psiTilde false P γ β).toKet.vec)
        (Matrix.mulVec A (psiTilde false P γ β).toKet.vec) := by
  have hvec := Ttilde_pow_apply_psiTilde P γ β n
  -- (T̃^n)† · A · T̃^n · ψ̃ = (T̃^n)† · A · ψ̃.
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [hvec]
  -- Now: dot (star ψ.vec) ((T̃^n)† *ᵥ (A *ᵥ ψ.vec)) = dot (star ψ.vec) (A *ᵥ ψ.vec).
  rw [Matrix.dotProduct_mulVec]
  -- Now: star ψ.vec ᵥ* (T̃^n)† ⬝ᵥ (A *ᵥ ψ.vec) = star ψ.vec ⬝ᵥ (A *ᵥ ψ.vec).
  have hstar : Matrix.vecMul (star (psiTilde false P γ β).toKet.vec)
        (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n)†) =
      star (Matrix.mulVec ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n)
        (psiTilde false P γ β).toKet.vec) := by
    rw [Matrix.star_mulVec]
  rw [hstar, hvec]

/-- **A4.4b.** `⟨ψ̃|chainPair 0|ψ̃⟩ = (1/N_R) · ⟨ψ̃|(Hred_z^- + N_R • I)|ψ̃⟩`.

Source: arXiv:1906.08948v2 App. l.1308 (eq. `antiperiodic_average`).

**Note on signature.** The `j_s` parameter is dropped (fixed at `0`) to match
the corrected `Hred_z_pm_false_eq_sum_translates`, whose numerically-validated form
holds only at interior bonds (not at `j_s = Fin.last`). Downstream A6
consumers use a single bond's expectation; `0` is the canonical choice. -/
theorem chainPairInteraction_expectation_eq_averaged
    (P : ℕ) (γ β : Fin P → ℝ) :
    dotProduct (star (psiTilde false P γ β).toKet.vec)
        (Matrix.mulVec (IsingModel.chainPairInteraction (0 : Fin (2*P+2)))
          (psiTilde false P γ β).toKet.vec) =
      (1 / ((2*P+2 : ℕ) : ℂ)) *
        dotProduct (star (psiTilde false P γ β).toKet.vec)
          (Matrix.mulVec
            (Hred_z_pm false P +
              ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)))
            (psiTilde false P γ β).toKet.vec) := by
  rw [Hred_z_pm_false_eq_sum_translates P]
  -- Distribute the bra-ket over the sum.
  rw [Matrix.sum_mulVec]
  rw [dotProduct_sum]
  -- Each term equals the chainPair expectation.
  have hconst : ∀ n : Fin (2*P+2),
      dotProduct (star (psiTilde false P γ β).toKet.vec)
        (Matrix.mulVec
          (((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val)† *
            IsingModel.chainPairInteraction (0 : Fin (2*P+2)) *
            ((Ttilde_op P : Qubits.NQubitOp (2*P+2))^n.val))
          (psiTilde false P γ β).toKet.vec) =
      dotProduct (star (psiTilde false P γ β).toKet.vec)
        (Matrix.mulVec (IsingModel.chainPairInteraction (0 : Fin (2*P+2)))
          (psiTilde false P γ β).toKet.vec) :=
    fun n ↦ expectation_invariant_under_TtildePow P γ β
      (IsingModel.chainPairInteraction (0 : Fin (2*P+2))) n.val
  rw [Finset.sum_congr rfl (fun n _ ↦ hconst n)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  have hne : ((2*P+2 : ℕ) : ℂ) ≠ 0 := by
    have h : (2*P+2 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  field_simp

/-- **ABC mid-bond translation invariance.** The ABC `psiTilde`-expectation of the
central bond `⟨P, P+1⟩` equals that of the canonical bond `0`. This is the
ABC-twisted translation invariance specialized to the interior central bond
(`bondSign = +1` there, so no sign appears). It is the ABC analogue of the PBC
reduced-bond translation `reducedChainQAOAConj_at_expectation_reach`, and the
missing step `E_ABC(mid) = E_ABC(0)` of the reduced PBC↔ABC bridge.

Proof: conjugating `cP(0)` by `T̃^P` lands on bond `orbit_P 0 = ⟨P,_⟩ = mid`
with accumulated sign `+1` (the central bond is interior, never the seam), and
`T̃` fixes `psiTilde`, so the conjugate's expectation equals the bare one. -/
theorem psiTilde_midBond_expectation_eq_zero (P : ℕ) (γ β : Fin P → ℝ) :
    (psiTilde false P γ β).toKet.dag *
        ((IsingModel.chainPairInteraction (⟨P, by omega⟩ : Fin (2*P+2))
            : Qubits.NQubitOp (2*P+2)) *
          (psiTilde false P γ β).toKet) =
      (psiTilde false P γ β).toKet.dag *
        ((IsingModel.chainPairInteraction (0 : Fin (2*P+2))
            : Qubits.NQubitOp (2*P+2)) *
          (psiTilde false P γ β).toKet) := by
  -- `orbit_P 0 = ⟨P, _⟩` (the mid bond) with bondSign +1.
  have horbit : ((nextSiteEquiv P)^P) (0 : Fin (2*P+2)) = (⟨P, by omega⟩ : Fin (2*P+2)) := by
    apply Fin.ext
    rw [orbit_zero_val P P (by omega)]
  have hmid_ne_last : (⟨P, by omega⟩ : Fin (2*P+2)) ≠ Fin.last (2*P+1) := by
    intro h
    have hh := congrArg Fin.val h
    rw [Fin.val_last, Fin.val_mk] at hh
    omega
  have hsign : bondSign P (((nextSiteEquiv P)^P) (0 : Fin (2*P+2))) = 1 := by
    rw [horbit]; unfold bondSign; rw [if_neg hmid_ne_last]
  -- The signed-conjugation identity at n = P, with sign +1, lands on the mid bond.
  have hconj := Ttilde_pow_conj_chainPair_zero P P
  rw [hsign, one_smul, horbit] at hconj
  -- hconj : (T̃^P)† cP(0) T̃^P = cP(mid).
  -- The expectation-invariance (T̃ fixes ψ̃) then gives the bond equality.
  have hinv := expectation_invariant_under_TtildePow P γ β
    (IsingModel.chainPairInteraction (0 : Fin (2*P+2))) P
  rw [hconj] at hinv
  -- Convert dotProduct form back to Bra*(Op*Ket) form.
  have hconv : ∀ (A : Qubits.NQubitOp (2*P+2)),
      (psiTilde false P γ β).toKet.dag * (A * (psiTilde false P γ β).toKet) =
        dotProduct (star (psiTilde false P γ β).toKet.vec)
          (Matrix.mulVec A (psiTilde false P γ β).toKet.vec) := by
    intro A; rw [bra_mul_ket_eq]; rfl
  rw [hconv, hconv]
  exact hinv

end

end QAOA.IsingChain.UpperBound
