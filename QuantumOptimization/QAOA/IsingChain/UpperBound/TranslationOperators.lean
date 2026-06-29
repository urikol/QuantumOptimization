import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Translation Operators T and T̃ — cyclic and twisted translation on the (2P+2)-qubit reduced chain

This file defines the two unitary operators that implement standard and twisted
cyclic translation on the reduced chain `N_R = 2P+2`, and proves their
conjugation action on the local Pauli operators `σ^x_j, σ^y_j, σ^z_j`.

Source: arXiv:1906.08948v2 App. `app:ABC_to_PBC`, l.1339–1356.

## Main definitions

* `rotateBitsEquiv P` — the `BitString (2*P+2) ≃ BitString (2*P+2)` cyclic
  bit-shift: `b ↦ (j ↦ b (nextSite j))`.
* `T_op P` — the standard cyclic translation operator on `N_R = 2P+2` qubits,
  defined as the permutation matrix of `rotateBitsEquiv P` lifted through
  `bitStringEquiv`.
* `Ttilde_op P` — the twisted translation operator `T · σ^x_0` (source l.1349).

## Main statements

For `T` (no boundary sign flip on any Pauli):

* `T_conj_X_of_ne_last`, `T_conj_X_last` — `T† σ^x_j T = σ^x_{nextSite j}`.
* `T_conj_Y_of_ne_last`, `T_conj_Y_last` — `T† σ^y_j T = σ^y_{nextSite j}`.
* `T_conj_Z_of_ne_last`, `T_conj_Z_last` — `T† σ^z_j T = σ^z_{nextSite j}`.

For `T̃` (no flip on X; sign flip on Y and Z at the boundary `j = Fin.last`):

* `Ttilde_conj_X_of_ne_last`, `Ttilde_conj_X_last`.
* `Ttilde_conj_Y_of_ne_last`, `Ttilde_conj_Y_last` (negated).
* `Ttilde_conj_Z_of_ne_last`, `Ttilde_conj_Z_last` (negated).

These twelve identities are exactly the source's l.1341, l.1344, l.1351, and
l.1354–1356.
-/

namespace QAOA.IsingChain.UpperBound

open Quantum.Operators
open Quantum.Gates
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Compatibility of `nextSite` with `finRotate`
-- ============================================================================

/-- The `nextSite` cyclic shift on `Fin (2*P+2)` is exactly Mathlib's `finRotate`.
This is the source pin: arXiv:1906.08948v2 App. l.1341 (the `+1`-direction of
the cyclic translation). -/
private theorem nextSite_eq_finRotate (P : ℕ) (j : Fin (2*P+2)) :
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

/-- `nextSite` evaluated at `Fin.last (2*P+1)` wraps to `0`. Source: corresponds
to the boundary identification `σ^z_{N_R+1} = σ^z_1` in arXiv:1906.08948v2 App. -/
private theorem nextSite_last (P : ℕ) :
    IsingModel.nextSite (Fin.last (2*P+1) : Fin (2*P+2)) = (0 : Fin (2*P+2)) := by
  rw [nextSite_eq_finRotate]
  exact finRotate_last

-- ============================================================================
-- Section: Bit-string rotation
-- ============================================================================

/-- The cyclic right-rotation on bit-strings of length `N_R = 2P+2`, packaged as
an `Equiv`. The forward direction sends `b` to `j ↦ b (nextSite j)`.

Source pin: arXiv:1906.08948v2 App. l.1341. With this convention, the standard
translation operator `T_op` defined below satisfies `T† σ_j T = σ_{nextSite j}`. -/
def rotateBitsEquiv (P : ℕ) : Qubits.BitString (2*P+2) ≃ Qubits.BitString (2*P+2) :=
  Equiv.arrowCongr (finRotate (2*P+2)).symm (Equiv.refl (Fin 2))

/-- Forward action: `(rotateBitsEquiv P b) j = b (nextSite j)`. -/
theorem rotateBitsEquiv_apply (P : ℕ) (b : Qubits.BitString (2*P+2))
    (j : Fin (2*P+2)) :
    rotateBitsEquiv P b j = b (IsingModel.nextSite j) := by
  show (Equiv.refl (Fin 2)) (b ((finRotate (2*P+2)).symm.symm j)) = _
  rw [Equiv.symm_symm, Equiv.refl_apply, nextSite_eq_finRotate]

/-- Inverse action: `(rotateBitsEquiv P).symm b j = b ((finRotate (2*P+2)).symm j)`. -/
theorem rotateBitsEquiv_symm_apply (P : ℕ) (b : Qubits.BitString (2*P+2))
    (j : Fin (2*P+2)) :
    (rotateBitsEquiv P).symm b j = b ((finRotate (2*P+2)).symm j) := by
  show (Equiv.refl (Fin 2)).symm (b ((finRotate (2*P+2)).symm j)) = _
  rfl

-- ============================================================================
-- Section: Bit-rotation / flipBitAt compatibility
-- ============================================================================

/-- The key combinatorial identity driving every Pauli-conjugation theorem
below: applying `rotateBitsEquiv.symm` to a string that has been flipped at site
`j` after pre-rotation by `rotateBitsEquiv` equals flipping the original string
at site `nextSite j`.

Source: this is the bit-string analog of `T† X_j T = X_{nextSite j}` (l.1341). -/
private theorem rotateBitsEquiv_symm_flipBitAt_rotateBitsEquiv (P : ℕ)
    (b : Qubits.BitString (2*P+2)) (j : Fin (2*P+2)) :
    (rotateBitsEquiv P).symm
        (Qubits.flipBitAt (rotateBitsEquiv P b) j) =
      Qubits.flipBitAt b (IsingModel.nextSite j) := by
  funext k
  rw [rotateBitsEquiv_symm_apply]
  unfold Qubits.flipBitAt
  -- LHS at k: (if (finRotate _).symm k = j then flipBit ((rotateBitsEquiv P b) ((finRotate _).symm k))
  --                                          else (rotateBitsEquiv P b) ((finRotate _).symm k))
  --         = (if (finRotate _).symm k = j then flipBit (b (finRotate _ ((finRotate _).symm k)))
  --                                          else b (finRotate _ ((finRotate _).symm k)))
  --         = (if (finRotate _).symm k = j then flipBit (b k) else b k)
  -- RHS at k: (if k = nextSite j then flipBit (b k) else b k)
  -- These match because (finRotate _).symm k = j ↔ k = finRotate j = nextSite j.
  have hcond : ((finRotate (2*P+2)).symm k = j) ↔ (k = IsingModel.nextSite j) := by
    rw [nextSite_eq_finRotate]
    constructor
    · intro h
      rw [← h, Equiv.apply_symm_apply]
    · intro h
      rw [h, Equiv.symm_apply_apply]
  -- Rewrite the LHS condition using the iff:
  rw [show (if (finRotate (2*P+2)).symm k = j then
              Qubits.flipBit ((rotateBitsEquiv P b) ((finRotate (2*P+2)).symm k))
            else (rotateBitsEquiv P b) ((finRotate (2*P+2)).symm k)) =
      (if k = IsingModel.nextSite j then
            Qubits.flipBit ((rotateBitsEquiv P b) ((finRotate (2*P+2)).symm k))
          else (rotateBitsEquiv P b) ((finRotate (2*P+2)).symm k)) from
    if_congr hcond rfl rfl]
  -- Now both have `if k = nextSite j ...`. Just need the values to match.
  congr 1
  · rw [rotateBitsEquiv_apply]
    congr 1
    rw [nextSite_eq_finRotate, Equiv.apply_symm_apply]
  · rw [rotateBitsEquiv_apply]
    congr 1
    rw [nextSite_eq_finRotate, Equiv.apply_symm_apply]

-- ============================================================================
-- Section: T — standard cyclic translation operator
-- ============================================================================

/-- The composite cyclic permutation on `Fin (2^(2P+2))`, induced by the
inverse of `rotateBitsEquiv P` through the bitstring/index equivalence. -/
def T_perm (P : ℕ) : Equiv.Perm (Fin (Qubits.NQubitDim (2*P+2))) :=
  (Qubits.bitStringEquiv (2*P+2)).symm.trans
    ((rotateBitsEquiv P).symm.trans (Qubits.bitStringEquiv (2*P+2)))

/-- The standard cyclic translation operator on `N_R = 2P+2` qubits, defined as
the permutation matrix of the cyclic bit-rotation permutation `T_perm P`.
Source: arXiv:1906.08948v2 App. l.1339–1344.

Unitarity follows from `Matrix.conjTranspose_permMatrix` plus `permMatrix_mul`. -/
def T_op (P : ℕ) : Qubits.NQubitUnitaryOp (2*P+2) where
  toOp := Equiv.Perm.permMatrix ℂ (T_perm P)
  unitary_left := by
    rw [show ((Equiv.Perm.permMatrix ℂ (T_perm P)).conjTranspose) =
        Equiv.Perm.permMatrix ℂ (T_perm P)⁻¹ from
      Matrix.conjTranspose_permMatrix (T_perm P)]
    rw [show (Equiv.Perm.permMatrix ℂ (T_perm P)⁻¹) *
            (Equiv.Perm.permMatrix ℂ (T_perm P)) =
          Equiv.Perm.permMatrix ℂ ((T_perm P) * (T_perm P)⁻¹) from
      (Matrix.permMatrix_mul (T_perm P) (T_perm P)⁻¹).symm]
    rw [mul_inv_cancel]
    exact Matrix.permMatrix_one
  unitary_right := by
    rw [show ((Equiv.Perm.permMatrix ℂ (T_perm P)).conjTranspose) =
        Equiv.Perm.permMatrix ℂ (T_perm P)⁻¹ from
      Matrix.conjTranspose_permMatrix (T_perm P)]
    rw [show (Equiv.Perm.permMatrix ℂ (T_perm P)) *
            (Equiv.Perm.permMatrix ℂ (T_perm P)⁻¹) =
          Equiv.Perm.permMatrix ℂ ((T_perm P)⁻¹ * (T_perm P)) from
      (Matrix.permMatrix_mul (T_perm P)⁻¹ (T_perm P)).symm]
    rw [inv_mul_cancel]
    exact Matrix.permMatrix_one

/-- The underlying operator of `T_op` is the permutation matrix of `T_perm`. -/
@[simp] theorem T_op_toOp (P : ℕ) :
    (T_op P : Qubits.NQubitOp (2*P+2)) = Equiv.Perm.permMatrix ℂ (T_perm P) := rfl

/-- The conjugate transpose of `T_op` equals the permutation matrix of
`(T_perm P)⁻¹`. -/
theorem T_op_conjTranspose (P : ℕ) :
    (T_op P : Qubits.NQubitOp (2*P+2))† =
      Equiv.Perm.permMatrix ℂ (T_perm P)⁻¹ := by
  rw [T_op_toOp]
  exact Matrix.conjTranspose_permMatrix (T_perm P)

-- ============================================================================
-- Section: Basis action of T and its adjoint
-- ============================================================================

/-- Action of a permutation matrix on a standard basis ket:
`permMatrix σ * stdKet i = stdKet (σ⁻¹ i)`.

This is the load-bearing lemma: once we identify `T_op` and `T_op†` with
permutation matrices for `T_perm` and `(T_perm)⁻¹` respectively, applying
either to a computational basis ket is just a reindexing. -/
private theorem permMatrix_mul_stdKet {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    Equiv.Perm.permMatrix ℂ σ * stdKet n i = stdKet n (σ⁻¹ i) := by
  ext j
  rw [op_mul_ket_vec]
  have hmul : (Equiv.Perm.permMatrix ℂ σ).mulVec (stdKet n i).vec =
      (stdKet n i).vec ∘ σ := Matrix.permMatrix_mulVec (σ := σ)
  rw [hmul, Function.comp_apply, stdKet_apply, stdKet_apply]
  -- Goal: (if i = σ j then 1 else 0) = (if σ⁻¹ i = j then 1 else 0)
  have hiff : (i = σ j) ↔ (σ⁻¹ i = j) := by
    constructor
    · intro h; rw [h]; exact Equiv.symm_apply_apply σ j
    · intro h; rw [← h]; exact (Equiv.apply_symm_apply σ i).symm
  rw [show (if i = σ j then (1:ℂ) else 0) = (if σ⁻¹ i = j then (1:ℂ) else 0) from
    if_congr hiff rfl rfl]

/-- The basis action of the standard translation operator:
`T_op * |z⟩ = |rotateBitsEquiv z⟩`. Source: arXiv:1906.08948v2 App. l.1341. -/
theorem T_op_on_basis (P : ℕ) (b : Qubits.BitString (2*P+2)) :
    (T_op P : Qubits.NQubitOp (2*P+2)) * Qubits.computationalBasisKet (2*P+2) b =
      Qubits.computationalBasisKet (2*P+2) (rotateBitsEquiv P b) := by
  rw [T_op_toOp, Qubits.computationalBasisKet, permMatrix_mul_stdKet]
  congr 1
  show ((Qubits.bitStringEquiv (2*P+2)).symm.trans
      ((rotateBitsEquiv P).symm.trans (Qubits.bitStringEquiv (2*P+2)))).symm
      (Qubits.bitStringEquiv (2*P+2) b) = _
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_symm]
  -- Goal: bitStringEquiv (rotateBitsEquiv (bitStringEquiv.symm (bitStringEquiv b))) = bitStringEquiv (rotateBitsEquiv b)
  rw [Equiv.symm_apply_apply]

/-- The basis action of the adjoint of the standard translation operator:
`T_op† * |z⟩ = |(rotateBitsEquiv P).symm z⟩`. -/
theorem T_op_adj_on_basis (P : ℕ) (b : Qubits.BitString (2*P+2)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† * Qubits.computationalBasisKet (2*P+2) b =
      Qubits.computationalBasisKet (2*P+2) ((rotateBitsEquiv P).symm b) := by
  rw [T_op_conjTranspose, Qubits.computationalBasisKet, permMatrix_mul_stdKet]
  congr 1
  rw [inv_inv]
  show ((Qubits.bitStringEquiv (2*P+2)).symm.trans
      ((rotateBitsEquiv P).symm.trans (Qubits.bitStringEquiv (2*P+2))))
      (Qubits.bitStringEquiv (2*P+2) b) = _
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

-- ============================================================================
-- Section: T-conjugation of local Pauli X
-- ============================================================================

/-- The unified `T_op`-conjugation of `localPauliX` for any site `j`: the
operator label is shifted forward by `nextSite`, with wrap-around.

Source: arXiv:1906.08948v2 App. l.1341 (`T† σ^x_j T = σ^x_{j+1}`, with
wrap-around `σ^x_{N_R} → σ^x_1`). -/
theorem T_conj_localPauliX (P : ℕ) (j : Fin (2*P+2)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (IsingModel.nextSite j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  -- LHS * |z⟩: chain of basis actions.
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, T_op_on_basis,
      Qubits.localPauliX_on_basis, T_op_adj_on_basis,
      rotateBitsEquiv_symm_flipBitAt_rotateBitsEquiv]
  -- RHS * |z⟩: a single basis action.
  rw [Qubits.localPauliX_on_basis]

/-- Interior case (`j ≠ Fin.last`): `T† σ^x_j T = σ^x_{nextSite j}`.
Source: arXiv:1906.08948v2 App. l.1341. -/
theorem T_conj_X_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (_hj : j ≠ Fin.last (2*P+1)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (IsingModel.nextSite j) :=
  T_conj_localPauliX P j

/-- Boundary case (`j = Fin.last`): `T† σ^x_{N_R} T = σ^x_1`, here written as
`σ^x_0` in 0-indexed Lean. Source: arXiv:1906.08948v2 App. l.1344. -/
theorem T_conj_X_last (P : ℕ) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX (Fin.last (2*P+1)) *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (0 : Fin (2*P+2)) := by
  rw [T_conj_localPauliX, nextSite_last]

-- ============================================================================
-- Section: T-conjugation of local Pauli Z
-- ============================================================================

/-- The unified `T_op`-conjugation of `localPauliZ` for any site `j`: the
operator label is shifted forward by `nextSite`.

For Pauli `Z`, the basis-action picks up a `±1` diagonal phase depending on
the bit at the shifted site. The key step is that `rotateBitsEquiv` preserves
this phase under relabelling: `(rotateBitsEquiv z) (nextSite j) = z (nextSite (nextSite j))`?
No — actually the simpler identity used here is just `rotateBitsEquiv b j = b (nextSite j)`,
which says the relabelled bit at `j` is the old bit at `nextSite j`. Conjugating
by `T_op` recovers a `±1` from the *original* site `nextSite j`, hence the
result is `localPauliZ (nextSite j)`.

Source: arXiv:1906.08948v2 App. l.1341. -/
theorem T_conj_localPauliZ (P : ℕ) (j : Fin (2*P+2)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliZ (IsingModel.nextSite j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  -- LHS * |z⟩: T * |z⟩ = |rotateBits z⟩, then Z_j picks up the diagonal phase
  -- Z (rotateBits z j) (rotateBits z j) = Z (z (nextSite j)) (z (nextSite j)),
  -- then T† scales the same phase on |rotateBits.symm (rotateBits z)⟩ = |z⟩.
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, T_op_on_basis,
      Qubits.localPauliZ_on_basis, op_mul_smul_ket, T_op_adj_on_basis]
  -- After the symm + rotate, we're back at |z⟩.
  -- RHS: Z_{nextSite j} * |z⟩ = Z (z (nextSite j)) (z (nextSite j)) • |z⟩
  rw [Qubits.localPauliZ_on_basis]
  -- Both sides scale the same |z⟩ by the same Z-diagonal at z (nextSite j).
  congr 1
  · -- Diagonal phase equality: the LHS uses (rotateBitsEquiv P z) j, but
    -- (rotateBitsEquiv P z) j = z (nextSite j) by rotateBitsEquiv_apply.
    rw [rotateBitsEquiv_apply]
  · -- The remaining ket is |rotateBitsEquiv.symm (rotateBitsEquiv z)⟩ = |z⟩.
    rw [Equiv.symm_apply_apply]

/-- Interior case: `T† σ^z_j T = σ^z_{nextSite j}`. Source: l.1341. -/
theorem T_conj_Z_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (_hj : j ≠ Fin.last (2*P+1)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliZ (IsingModel.nextSite j) :=
  T_conj_localPauliZ P j

/-- Boundary case: `T† σ^z_{N_R} T = σ^z_1`. Source: l.1344. -/
theorem T_conj_Z_last (P : ℕ) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ (Fin.last (2*P+1)) *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliZ (0 : Fin (2*P+2)) := by
  rw [T_conj_localPauliZ, nextSite_last]

-- ============================================================================
-- Section: T-conjugation of local Pauli Y
-- ============================================================================

/-- The unified `T_op`-conjugation of `localPauliY` for any site `j`: the
operator label is shifted forward by `nextSite`. Like Z, Pauli Y picks up an
imaginary `±i` phase depending on the bit at the shifted site, which is again
preserved by `rotateBitsEquiv`.

Source: arXiv:1906.08948v2 App. l.1341. -/
theorem T_conj_localPauliY (P : ℕ) (j : Fin (2*P+2)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliY (IsingModel.nextSite j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, T_op_on_basis,
      Qubits.localPauliY_on_basis, op_mul_smul_ket, T_op_adj_on_basis,
      rotateBitsEquiv_symm_flipBitAt_rotateBitsEquiv]
  rw [Qubits.localPauliY_on_basis]
  -- Both sides scale |flipBitAt z (nextSite j)⟩ by `pauliYPhase (... j)`.
  -- LHS phase: pauliYPhase ((rotateBitsEquiv P z) j) = pauliYPhase (z (nextSite j)).
  -- RHS phase: pauliYPhase (z (nextSite j)).
  congr 1
  rw [rotateBitsEquiv_apply]

/-- Interior case: `T† σ^y_j T = σ^y_{nextSite j}`. Source: l.1341. -/
theorem T_conj_Y_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (_hj : j ≠ Fin.last (2*P+1)) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY j *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliY (IsingModel.nextSite j) :=
  T_conj_localPauliY P j

/-- Boundary case: `T† σ^y_{N_R} T = σ^y_1`. Source: l.1344. -/
theorem T_conj_Y_last (P : ℕ) :
    (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY (Fin.last (2*P+1)) *
        (T_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliY (0 : Fin (2*P+2)) := by
  rw [T_conj_localPauliY, nextSite_last]

-- ============================================================================
-- Section: Local Pauli site-disjoint commutation helpers
-- ============================================================================

/-!
The twisted translation `Ttilde = T * X_0` requires conjugating a Pauli at site
`nextSite j` by `X_0`. When the two sites differ (`nextSite j ≠ 0`, which holds
iff `j ≠ Fin.last`), the conjugation is trivial because Pauli operators on
different sites commute and `X_0^2 = 1`.

We prove the three site-disjoint commutation lemmas (X-X already exists as
`localPauliX_commute`; we add Y-X and Z-X) directly from the basis-action
lemmas plus `flipBitAt_comm`. Extraction candidates for `Qubits/`.
-/

/-- Local Pauli `Y_i` and `X_j` on different sites commute. -/
private theorem localPauliY_localPauliX_commute_of_ne {N : ℕ} {i j : Fin N}
    (hij : i ≠ j) :
    Qubits.localPauliY i * Qubits.localPauliX j =
      Qubits.localPauliX j * Qubits.localPauliY i := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, Qubits.localPauliX_on_basis, Qubits.localPauliY_on_basis,
      op_mul_op_mul_ket, Qubits.localPauliY_on_basis, op_mul_smul_ket,
      Qubits.localPauliX_on_basis]
  -- LHS: pauliYPhase ((flipBitAt z j) i) • |flipBitAt (flipBitAt z j) i⟩
  -- RHS: pauliYPhase (z i) • |flipBitAt (flipBitAt z i) j⟩
  rw [Qubits.flipBitAt_apply_of_ne (z := z) hij,
      ← Qubits.flipBitAt_comm (z := z) hij]

/-- Local Pauli `Z_i` and `X_j` on different sites commute. -/
private theorem localPauliZ_localPauliX_commute_of_ne {N : ℕ} {i j : Fin N}
    (hij : i ≠ j) :
    Qubits.localPauliZ i * Qubits.localPauliX j =
      Qubits.localPauliX j * Qubits.localPauliZ i := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, Qubits.localPauliX_on_basis, Qubits.localPauliZ_on_basis,
      op_mul_op_mul_ket, Qubits.localPauliZ_on_basis, op_mul_smul_ket,
      Qubits.localPauliX_on_basis]
  -- LHS: Z ((flipBitAt z j) i) ((flipBitAt z j) i) • |flipBitAt z j⟩
  -- RHS: Z (z i) (z i) • |flipBitAt z j⟩
  rw [Qubits.flipBitAt_apply_of_ne (z := z) hij]

-- ============================================================================
-- Section: Same-site Pauli anticommutation at site 0 (lifted)
-- ============================================================================

/-- Helper: multiplication by `-A` on a ket distributes the negation. -/
private lemma neg_op_mul_ket {N : ℕ} (A : Qubits.NQubitOp N) (ψ : Qubits.NQubitKet N) :
    (-A) * ψ = -(A * ψ) := by
  ext i
  simp [Matrix.neg_mulVec]

/-- Same-site Pauli Y anticommutes with X. Extraction candidate for `Qubits/`. -/
private theorem localPauliX_localPauliY_anticomm_at {N : ℕ} (j : Fin N) :
    Qubits.localPauliX j * Qubits.localPauliY j =
      -(Qubits.localPauliY j * Qubits.localPauliX j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  -- LHS * |z⟩
  rw [op_mul_op_mul_ket, Qubits.localPauliY_on_basis, op_mul_smul_ket,
      Qubits.localPauliX_on_basis, Qubits.flipBitAt_involutive]
  -- RHS * |z⟩
  rw [neg_op_mul_ket, op_mul_op_mul_ket, Qubits.localPauliX_on_basis,
      Qubits.localPauliY_on_basis, Qubits.flipBitAt_apply_same,
      Qubits.flipBitAt_involutive]
  -- Need: pauliYPhase (z j) • |z⟩ = -(pauliYPhase (flipBit (z j)) • |z⟩)
  have hphase :
      Qubits.pauliYPhase (z j) =
        -(Qubits.pauliYPhase (Qubits.flipBit (z j))) := by
    rcases hzj : z j with ⟨k, hk⟩
    interval_cases k <;> simp [Qubits.pauliYPhase, Qubits.flipBit]
  rw [hphase]
  ext i
  simp

/-- Same-site Pauli Z anticommutes with X. Lifts `pauliXZ_anticommute` from
`Op 2` to local Paulis on a single site of an `N`-qubit register. Extraction
candidate for `Qubits/`. -/
private theorem localPauliX_localPauliZ_anticomm_at {N : ℕ} (j : Fin N) :
    Qubits.localPauliX j * Qubits.localPauliZ j =
      -(Qubits.localPauliZ j * Qubits.localPauliX j) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, Qubits.localPauliZ_on_basis, op_mul_smul_ket,
      Qubits.localPauliX_on_basis]
  rw [neg_op_mul_ket, op_mul_op_mul_ket, Qubits.localPauliX_on_basis,
      Qubits.localPauliZ_on_basis, Qubits.flipBitAt_apply_same]
  have hphase :
      Z (z j) (z j) = -(Z (Qubits.flipBit (z j)) (Qubits.flipBit (z j))) := by
    rcases hzj : z j with ⟨k, hk⟩
    interval_cases k <;> simp [pauliZ, Qubits.flipBit]
  rw [hphase]
  ext i
  simp

-- ============================================================================
-- Section: Ttilde — twisted cyclic translation operator
-- ============================================================================

/-- Unitarity packaging of `localPauliX (0 : Fin (2*P+2))`: the single-qubit
Pauli `X` is involutive and Hermitian, so it is unitary. -/
private def localPauliX_zero_unitary (P : ℕ) : Qubits.NQubitUnitaryOp (2*P+2) where
  toOp := Qubits.localPauliX (0 : Fin (2*P+2))
  unitary_left := by
    rw [show ((Qubits.localPauliX (0 : Fin (2*P+2))).conjTranspose) =
        Qubits.localPauliX (0 : Fin (2*P+2)) from
      Qubits.localPauliX_hermitian 0]
    exact Qubits.localPauliX_sq 0
  unitary_right := by
    rw [show ((Qubits.localPauliX (0 : Fin (2*P+2))).conjTranspose) =
        Qubits.localPauliX (0 : Fin (2*P+2)) from
      Qubits.localPauliX_hermitian 0]
    exact Qubits.localPauliX_sq 0

/-- The twisted (anti-periodic) translation operator on `N_R = 2P+2` qubits:
`T̃ = T · σ^x_0`. Source: arXiv:1906.08948v2 App. l.1349 (`Ttwistop ≡ Top · σ^x_1`,
where source spin `1` is Lean's site `0`). -/
def Ttilde_op (P : ℕ) : Qubits.NQubitUnitaryOp (2*P+2) :=
  T_op P * localPauliX_zero_unitary P

/-- The underlying operator of `Ttilde_op` is `T_op * localPauliX 0`. -/
@[simp] theorem Ttilde_op_toOp (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      (T_op P : Qubits.NQubitOp (2*P+2)) * Qubits.localPauliX (0 : Fin (2*P+2)) := rfl

/-- Conjugate transpose of `Ttilde_op`: `T̃† = X_0 · T†`, using
`(AB)† = B† A†` and `X_0† = X_0`. -/
theorem Ttilde_op_conjTranspose (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† := by
  rw [Ttilde_op_toOp, Matrix.conjTranspose_mul, Qubits.localPauliX_hermitian]

-- ============================================================================
-- Section: Ttilde-conjugation of local Pauli X
-- ============================================================================

/-- The unified `Ttilde_op`-conjugation of `localPauliX` at any site `j`: the
operator label is shifted forward by `nextSite`, with NO sign flip (Pauli `X`
self-commutes with `X_0` so the `X_0` sandwich is invisible).

For interior sites (`nextSite j ≠ 0`): commute past, then `X_0^2 = 1`.
For the boundary (`nextSite j = 0`): same site, but `X_0^3 = X_0`.

Both cases are handled uniformly via `localPauliX_commute` + `localPauliX_sq`.

Source: arXiv:1906.08948v2 App. l.1351 (interior) + l.1354 (boundary, no flip
on X). -/
theorem Ttilde_conj_localPauliX (P : ℕ) (j : Fin (2*P+2)) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX j *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (IsingModel.nextSite j) := by
  rw [Ttilde_op_conjTranspose, Ttilde_op_toOp]
  -- (X_0 * T†) * X_j * (T * X_0)
  -- = X_0 * (T† * X_j * T) * X_0
  -- = X_0 * X_{nextSite j} * X_0
  -- = X_{nextSite j} * X_0 * X_0
  -- = X_{nextSite j}
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX j *
        ((T_op P : Qubits.NQubitOp (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        ((T_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliX j *
          (T_op P : Qubits.NQubitOp (2*P+2))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) by noncomm_ring]
  rw [T_conj_localPauliX]
  -- Goal: X_0 * X_{nextSite j} * X_0 = X_{nextSite j}
  have hcomm := Qubits.localPauliX_commute (N := 2*P+2)
    (0 : Fin (2*P+2)) (IsingModel.nextSite j)
  -- Commute.eq says: a * b = b * a (in our convention here, X_0 * X_{nextSite j} = X_{nextSite j} * X_0)
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        Qubits.localPauliX (IsingModel.nextSite j) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      Qubits.localPauliX (IsingModel.nextSite j) *
        (Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) from by
    rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (IsingModel.nextSite j) =
        Qubits.localPauliX (IsingModel.nextSite j) *
          Qubits.localPauliX (0 : Fin (2*P+2)) from hcomm]
    noncomm_ring]
  rw [Qubits.localPauliX_sq, mul_one]

/-- Interior case: `T̃† σ^x_j T̃ = σ^x_{nextSite j}`. Source: l.1351. -/
theorem Ttilde_conj_X_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (_hj : j ≠ Fin.last (2*P+1)) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX j *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (IsingModel.nextSite j) :=
  Ttilde_conj_localPauliX P j

/-- Boundary case: `T̃† σ^x_{N_R} T̃ = σ^x_1` (i.e. site `0`), with no sign
flip — same as the standard `T`. Source: l.1354 (no sign flip on X). -/
theorem Ttilde_conj_X_last (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliX (Fin.last (2*P+1)) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliX (0 : Fin (2*P+2)) := by
  rw [Ttilde_conj_localPauliX, nextSite_last]

-- ============================================================================
-- Section: Ttilde-conjugation of local Pauli Y
-- ============================================================================

/-- Interior case (`j ≠ Fin.last`, hence `nextSite j ≠ 0`): `T̃† σ^y_j T̃ =
σ^y_{nextSite j}`, with NO sign flip because Pauli Y at `nextSite j ≠ 0`
commutes with `X_0`.

Source: arXiv:1906.08948v2 App. l.1351. -/
theorem Ttilde_conj_Y_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (hj : j ≠ Fin.last (2*P+1)) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY j *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliY (IsingModel.nextSite j) := by
  rw [Ttilde_op_conjTranspose, Ttilde_op_toOp]
  -- Reorganize: X_0 * (T† * Y_j * T) * X_0 = X_0 * Y_{nextSite j} * X_0
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY j *
        ((T_op P : Qubits.NQubitOp (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        ((T_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliY j *
          (T_op P : Qubits.NQubitOp (2*P+2))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) by noncomm_ring]
  rw [T_conj_localPauliY]
  -- Now: X_0 * Y_{nextSite j} * X_0 = Y_{nextSite j} (different sites commute, X_0^2 = 1).
  have hne : IsingModel.nextSite j ≠ (0 : Fin (2*P+2)) := by
    intro h
    apply hj
    -- nextSite j = 0 ⟺ (j.val + 1) % (2*P+2) = 0 ⟺ j.val = 2*P+1 = (Fin.last).val
    have hval : (IsingModel.nextSite j).val = (0 : Fin (2*P+2)).val :=
      congrArg Fin.val h
    rw [IsingModel.nextSite_val] at hval
    have h0 : ((0 : Fin (2*P+2)) : ℕ) = 0 := rfl
    rw [h0] at hval
    -- hval : (j.val + 1) % (2*P+2) = 0
    have hjlt : (j : ℕ) < 2*P+2 := j.isLt
    -- j.val + 1 ≤ 2*P+2; if j.val + 1 < 2*P+2 then mod = j.val + 1 ≠ 0; so j.val + 1 = 2*P+2.
    have heq : (j : ℕ) + 1 = 2*P+2 := by
      by_contra hne'
      have hlt : (j : ℕ) + 1 < 2*P+2 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    apply Fin.ext
    show (j : ℕ) = (Fin.last (2*P+1) : Fin (2*P+2)).val
    have hlast : (Fin.last (2*P+1) : Fin (2*P+2)).val = 2*P+1 := Fin.val_last _
    rw [hlast]
    omega
  have hY : Qubits.localPauliY (IsingModel.nextSite j) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        Qubits.localPauliY (IsingModel.nextSite j) :=
    localPauliY_localPauliX_commute_of_ne hne
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        Qubits.localPauliY (IsingModel.nextSite j) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      Qubits.localPauliY (IsingModel.nextSite j) *
        (Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) from by
    rw [← hY]; noncomm_ring]
  rw [Qubits.localPauliX_sq, mul_one]

/-- Boundary case (`j = Fin.last`, hence `nextSite j = 0`): `T̃† σ^y_{N_R} T̃ =
-σ^y_1` (sign flipped). This is the load-bearing feature for A4's ABC
invariance: same-site `X_0 Y_0 X_0 = -Y_0` via `pauliXY_anticommute` + `X_0^2 = 1`.

Source: arXiv:1906.08948v2 App. l.1355 (the Y sign flip at the boundary). -/
theorem Ttilde_conj_Y_last (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY (Fin.last (2*P+1)) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      -(Qubits.localPauliY (0 : Fin (2*P+2))) := by
  rw [Ttilde_op_conjTranspose, Ttilde_op_toOp]
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliY (Fin.last (2*P+1)) *
        ((T_op P : Qubits.NQubitOp (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        ((T_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliY (Fin.last (2*P+1)) *
          (T_op P : Qubits.NQubitOp (2*P+2))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) by noncomm_ring]
  rw [T_conj_localPauliY, nextSite_last]
  -- Goal: X_0 * Y_0 * X_0 = -Y_0
  -- X_0 * Y_0 = -(Y_0 * X_0) (same-site anticomm), then * X_0 = -(Y_0 * X_0 * X_0) = -(Y_0 * 1) = -Y_0
  rw [localPauliX_localPauliY_anticomm_at (0 : Fin (2*P+2))]
  rw [show (-(Qubits.localPauliY (0 : Fin (2*P+2)) *
        Qubits.localPauliX (0 : Fin (2*P+2)))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      -(Qubits.localPauliY (0 : Fin (2*P+2)) *
        (Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2)))) from by noncomm_ring]
  rw [Qubits.localPauliX_sq, mul_one]

-- ============================================================================
-- Section: Ttilde-conjugation of local Pauli Z
-- ============================================================================

/-- Interior case (`j ≠ Fin.last`, hence `nextSite j ≠ 0`): `T̃† σ^z_j T̃ =
σ^z_{nextSite j}`, with NO sign flip. Source: arXiv:1906.08948v2 App. l.1351. -/
theorem Ttilde_conj_Z_of_ne_last (P : ℕ) (j : Fin (2*P+2))
    (hj : j ≠ Fin.last (2*P+1)) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ j *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      Qubits.localPauliZ (IsingModel.nextSite j) := by
  rw [Ttilde_op_conjTranspose, Ttilde_op_toOp]
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ j *
        ((T_op P : Qubits.NQubitOp (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        ((T_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliZ j *
          (T_op P : Qubits.NQubitOp (2*P+2))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) by noncomm_ring]
  rw [T_conj_localPauliZ]
  -- Different-site commutation: Z_{nextSite j} commutes with X_0 because nextSite j ≠ 0.
  have hne : IsingModel.nextSite j ≠ (0 : Fin (2*P+2)) := by
    intro h
    apply hj
    have hval : (IsingModel.nextSite j).val = (0 : Fin (2*P+2)).val :=
      congrArg Fin.val h
    rw [IsingModel.nextSite_val] at hval
    have h0 : ((0 : Fin (2*P+2)) : ℕ) = 0 := rfl
    rw [h0] at hval
    have hjlt : (j : ℕ) < 2*P+2 := j.isLt
    have heq : (j : ℕ) + 1 = 2*P+2 := by
      by_contra hne'
      have hlt : (j : ℕ) + 1 < 2*P+2 := by omega
      rw [Nat.mod_eq_of_lt hlt] at hval
      omega
    apply Fin.ext
    show (j : ℕ) = (Fin.last (2*P+1) : Fin (2*P+2)).val
    have hlast : (Fin.last (2*P+1) : Fin (2*P+2)).val = 2*P+1 := Fin.val_last _
    rw [hlast]
    omega
  have hZ : Qubits.localPauliZ (IsingModel.nextSite j) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        Qubits.localPauliZ (IsingModel.nextSite j) :=
    localPauliZ_localPauliX_commute_of_ne hne
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        Qubits.localPauliZ (IsingModel.nextSite j) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      Qubits.localPauliZ (IsingModel.nextSite j) *
        (Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) from by
    rw [← hZ]; noncomm_ring]
  rw [Qubits.localPauliX_sq, mul_one]

/-- Boundary case (`j = Fin.last`, hence `nextSite j = 0`): `T̃† σ^z_{N_R} T̃ =
-σ^z_1` (sign flipped). Same load-bearing mechanism as `Ttilde_conj_Y_last`:
same-site `X_0 Z_0 X_0 = -Z_0`. Source: arXiv:1906.08948v2 App. l.1356. -/
theorem Ttilde_conj_Z_last (P : ℕ) :
    (Ttilde_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ (Fin.last (2*P+1)) *
        (Ttilde_op P : Qubits.NQubitOp (2*P+2)) =
      -(Qubits.localPauliZ (0 : Fin (2*P+2))) := by
  rw [Ttilde_op_conjTranspose, Ttilde_op_toOp]
  rw [show Qubits.localPauliX (0 : Fin (2*P+2)) *
        (T_op P : Qubits.NQubitOp (2*P+2))† *
        Qubits.localPauliZ (Fin.last (2*P+1)) *
        ((T_op P : Qubits.NQubitOp (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2))) =
      Qubits.localPauliX (0 : Fin (2*P+2)) *
        ((T_op P : Qubits.NQubitOp (2*P+2))† *
          Qubits.localPauliZ (Fin.last (2*P+1)) *
          (T_op P : Qubits.NQubitOp (2*P+2))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) by noncomm_ring]
  rw [T_conj_localPauliZ, nextSite_last]
  -- Goal: X_0 * Z_0 * X_0 = -Z_0
  rw [localPauliX_localPauliZ_anticomm_at (0 : Fin (2*P+2))]
  rw [show (-(Qubits.localPauliZ (0 : Fin (2*P+2)) *
        Qubits.localPauliX (0 : Fin (2*P+2)))) *
        Qubits.localPauliX (0 : Fin (2*P+2)) =
      -(Qubits.localPauliZ (0 : Fin (2*P+2)) *
        (Qubits.localPauliX (0 : Fin (2*P+2)) *
          Qubits.localPauliX (0 : Fin (2*P+2)))) from by noncomm_ring]
  rw [Qubits.localPauliX_sq, mul_one]

end

end QAOA.IsingChain.UpperBound
