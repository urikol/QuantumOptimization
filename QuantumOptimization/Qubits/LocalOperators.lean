import QuantumOptimization.Qubits.NQubitSpace

/-!
# Local Operators on N Qubits

Single-qubit operators acting on a specified qubit inside an `N`-qubit register.

This file contains the generic machinery for lifting a one-qubit operator to an
operator on the full `N`-qubit Hilbert space. It deliberately stays at the
level of arbitrary single-qubit operators; Pauli-specific specializations are
developed separately in `PauliOperators.lean`.
-/

namespace Qubits

open Quantum.Operators
open Matrix

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section defines what it means for two computational-basis bitstrings to
agree away from a chosen qubit, and then uses that notion to define the action
of a single-qubit operator on a specified qubit of an `N`-qubit Hilbert space.

The definition is entrywise in the computational basis indexed by bitstrings.
This keeps the construction explicit and makes later coordinate calculations
straightforward.
-/

/-- Two bitstrings agree away from qubit `j`.

This relation means that `z` and `w` may differ at the chosen qubit `j`, but
must agree at every other position. It is exactly the condition that describes
when a local operator acting on qubit `j` can have a nonzero matrix entry
between the computational-basis states `|z⟩` and `|w⟩`.
-/
def SameOutside {N : ℕ} (j : Fin N) (z w : BitString N) : Prop :=
  ∀ k : Fin N, k ≠ j → z k = w k

instance instDecidableSameOutside {N : ℕ} (j : Fin N) (z w : BitString N) :
    Decidable (SameOutside j z w) := by
  classical
  unfold SameOutside
  infer_instance

/-- The lift of a single-qubit operator `A : Op 2` to qubit `j` of an `N`-qubit
register. In the computational basis, the matrix element is `A (x j) (y j)`
when the bitstrings `z` and `w` agree on all qubits other than `j`, and `0`
otherwise.

Equivalently, `localOp A j` acts as the operator `A` on the `j`-th qubit and as
the identity on every other qubit. The present definition expresses that action
directly in matrix-entry form, which is convenient for explicit basis
calculations.
-/
def localOp {N : ℕ} (A : Op 2) (j : Fin N) : NQubitOp N :=
  by
    classical
    exact Matrix.of fun ix iy =>
      let z := (bitStringEquiv N).symm ix
      let w := (bitStringEquiv N).symm iy
      if SameOutside j z w then A (z j) (w j) else 0

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas expose the computational-basis matrix entries of local operators
and provide the generic infrastructure for reasoning about one-qubit operators
lifted to an `N`-qubit register.

They are meant to be the workhorse interface for later specialized files. In
particular, `PauliOperators.lean` relies on them to derive the computational-
basis action of the lifted Pauli matrices.
-/

/-- Two `N`-qubit operators are equal if they agree on every
computational-basis ket.

This is the finite-dimensional statement that a linear operator is determined by
its action on a basis.
-/
theorem op_eq_of_on_computationalBasis {N : ℕ} {A B : NQubitOp N}
    (h : ∀ z : BitString N,
      A * computationalBasisKet N z = B * computationalBasisKet N z) :
    A = B := by
  ext ix iy
  let z := (bitStringEquiv N).symm iy
  have hix :=
    congrArg (fun ψ : NQubitKet N => ψ.vec ix) (h z)
  simpa [z, computationalBasisKet, op_mul_ket_vec, Matrix.mulVec, dotProduct] using hix

/-- Entrywise expansion of `localOp` in the computational basis.

This theorem simply unfolds the definition of `localOp` at a pair of basis
indices. It is the starting point for most direct calculations with lifted
single-qubit operators.
-/
@[simp]
theorem localOp_apply {N : ℕ} (A : Op 2) (j : Fin N) (ix iy : Fin (NQubitDim N)) :
    localOp A j ix iy =
      let z := (bitStringEquiv N).symm ix
      let w := (bitStringEquiv N).symm iy
      if SameOutside j z w then A (z j) (w j) else 0 := by
  classical
  rfl

/-- If two basis indices disagree away from qubit `j`, the corresponding matrix
entry of a local operator on `j` is zero.

This formalizes the fact that a local operator acting on qubit `j` cannot change
any other qubit. So if two computational-basis strings differ somewhere outside
`j`, the corresponding matrix entry must vanish.
-/
theorem localOp_apply_of_not_sameOutside {N : ℕ} (A : Op 2) (j : Fin N)
    (ix iy : Fin (NQubitDim N))
    (h : ¬ SameOutside j ((bitStringEquiv N).symm ix) ((bitStringEquiv N).symm iy)) :
    localOp A j ix iy = 0 := by
  classical
  simp [localOp, h]

/-- If two basis indices agree away from qubit `j`, the corresponding matrix
entry of a local operator on `j` is determined by the underlying single-qubit
operator.

In that case, the only relevant data is the pair of bits at position `j`, so
the matrix entry is exactly the corresponding entry of the underlying one-qubit
operator `A`.
-/
theorem localOp_apply_of_sameOutside {N : ℕ} (A : Op 2) (j : Fin N)
    (ix iy : Fin (NQubitDim N))
    (h : SameOutside j ((bitStringEquiv N).symm ix) ((bitStringEquiv N).symm iy)) :
    localOp A j ix iy =
      A (((bitStringEquiv N).symm ix) j) (((bitStringEquiv N).symm iy) j) := by
  classical
  simp [localOp, h]

/-- A local operator whose underlying single-qubit matrix is diagonal acts
diagonally on computational-basis kets, with eigenvalue determined by the
selected basis bit.

This is the generic diagonal-action theorem for local operators. Whenever the
single-qubit matrix `A` is diagonal with diagonal entries `η b`, the lifted
operator `localOp A j` has each computational-basis ket `|z⟩` as an eigenvector,
with eigenvalue `η (z j)` determined by the bit carried by qubit `j`.

This theorem is later specialized to the Pauli `Z` operator in
`PauliOperators.lean`.
-/
theorem localOp_apply_computationalBasisKet_of_diagonal {N : ℕ} (A : Op 2)
    (η : Fin 2 → ℂ) (j : Fin N) (z : BitString N)
    (hdiag : ∀ b : Fin 2, A b b = η b)
    (hoffdiag : ∀ b c : Fin 2, b ≠ c → A b c = 0) :
    localOp A j * computationalBasisKet N z =
      (η (z j)) • computationalBasisKet N z := by
  ext iy
  let w := (bitStringEquiv N).symm iy
  have hsymm : (bitStringEquiv N).symm (bitStringEquiv N z) = z := by
    simp [bitStringEquiv]
  have hvec :
      (localOp A j * computationalBasisKet N z : NQubitKet N).vec iy =
        localOp A j iy (bitStringEquiv N z) := by
    simp [computationalBasisKet, Matrix.mulVec, dotProduct]
  rw [hvec]
  by_cases hsame : SameOutside j w z
  · have hsame' :
        SameOutside j ((bitStringEquiv N).symm iy)
          ((bitStringEquiv N).symm (bitStringEquiv N z)) := by
        intro k hk
        rw [hsymm]
        simpa [w] using hsame k hk
    rw [localOp_apply_of_sameOutside (A := A) (h := hsame')]
    by_cases hj : w j = z j
    · have hwz : w = z := by
        funext k
        by_cases hk : k = j
        · simpa [hk] using hj
        · exact hsame k hk
      have hiy : iy = bitStringEquiv N z := by
        simpa [w] using congrArg (bitStringEquiv N) hwz
      have hiy' : bitStringEquiv N z = iy := hiy.symm
      have hη : η ((bitStringEquiv N).symm iy j) = η (z j) := by
        simpa [w] using congrArg η (congrArg (fun u => u j) hwz)
      simp [computationalBasisKet, hdiag, hiy', hη]
    · have hwz : w ≠ z := by
        intro h
        apply hj
        exact congrArg (fun u => u j) h
      have hiy : iy ≠ bitStringEquiv N z := by
        intro h
        apply hwz
        exact (bitStringEquiv N).injective (by simpa [w] using h)
      have hiy' : bitStringEquiv N z ≠ iy := Ne.symm hiy
      have hneq : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 N) z = iy := by
        simpa [bitStringEquiv] using hiy'
      have hA :
          A ((bitStringEquiv N).symm iy j)
            (((bitStringEquiv N).symm (bitStringEquiv N z)) j) = 0 := by
        simpa [bitStringEquiv, w, hsymm] using
          hoffdiag (w j) (z j) hj
      have hrhs :
          ((η (z j)) • computationalBasisKet N z : NQubitKet N).vec iy = 0 := by
        simp [computationalBasisKet, hneq]
      rw [hrhs]
      exact hA
  · rw [localOp_apply_of_not_sameOutside (A := A)]
    · have hwz : w ≠ z := by
        intro h
        apply hsame
        intro k hk
        exact congrArg (fun u => u k) h
      have hiy : iy ≠ bitStringEquiv N z := by
        intro h
        apply hwz
        exact (bitStringEquiv N).injective (by simpa [w] using h)
      have hneq : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 N) z = iy := by
        simpa [bitStringEquiv] using Ne.symm hiy
      simp [computationalBasisKet, hneq]
    · have hsame' :
          ¬ SameOutside j ((bitStringEquiv N).symm iy)
              ((bitStringEquiv N).symm (bitStringEquiv N z)) := by
        intro h'
        apply hsame
        intro k hk
        rw [← hsymm]
        simpa [w] using h' k hk
      exact hsame'

end

end Qubits
