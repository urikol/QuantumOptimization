import QuantumOptimization.Math.RepresentationTheory.PermutationAction
import QuantumOptimization.Quantum.Operators.BraKet
import QuantumOptimization.Quantum.Operators.Types
import Mathlib.InformationTheory.Hamming

/-!
# N-Qubit Hilbert Space

Basic packaging for the Hilbert space of `N` qubits.

This file introduces the standard dimension `2 ^ N`, the corresponding quantum
state and operator types, and the equivalence between computational basis
bitstrings and indices in `Fin (2 ^ N)`.

The purpose of the file is not to develop qubit physics in detail, but to give
a clean and reusable ambient language for later constructions. In particular, it
provides:

* the canonical `N`-qubit Hilbert-space dimension,
* convenient abbreviations for the main quantum types on that space, and
* the basic computational-basis kets and states indexed by classical
  bitstrings.

This file is intentionally lightweight. More structured operator constructions,
such as local single-qubit actions and lifted Pauli operators, are developed in
later files of the `Qubits` folder.
-/

namespace Qubits

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section packages the standard `N`-qubit Hilbert space as the dimension
`2 ^ N`, together with convenient abbreviations for kets, normalized kets,
operators, density operators, and unitaries on that space.

It also defines the computational-basis indexing by bitstrings
`Fin N → Fin 2`.

The point of these definitions is to let later files speak about `N`-qubit
objects directly, instead of repeatedly writing everything in terms of the raw
dimension `2 ^ N`.
-/

/-- The dimension of the Hilbert space of `N` qubits.

This is the usual dimension `2 ^ N` obtained by taking the tensor product of `N`
copies of a two-dimensional qubit space.
-/
abbrev NQubitDim (N : ℕ) : ℕ := 2 ^ N

/-- Bitstrings of length `N`, represented as functions `Fin N → Fin 2`.

Such a bitstring may be viewed either as a classical `N`-bit configuration or
as the label of a computational-basis vector in the `N`-qubit Hilbert space.
-/
abbrev BitString (N : ℕ) := Fin N → Fin 2

/-- Hamming distance between two `N`-bit strings.

This is the number of qubit positions on which the two computational-basis
labels differ.
-/
abbrev bitStringHammingDist {N : ℕ} (z w : BitString N) : ℕ :=
  hammingDist z w

/-- Hamming distance restricted to a chosen set of qubit positions.

This counts the number of indices in `s` on which the two bitstrings differ.
-/
abbrev bitStringHammingDistOn {N : ℕ} (s : Finset (Fin N)) (z w : BitString N) : ℕ :=
  (s.filter (fun j => z j ≠ w j)).card

/-- Kets on the Hilbert space of `N` qubits.

This is simply `Ket (2 ^ N)` under a more readable name.
-/
abbrev NQubitKet (N : ℕ) := Ket (NQubitDim N)

/-- Normalized kets on the Hilbert space of `N` qubits.

This is the normalized-state version of `NQubitKet`.
-/
abbrev NQubitNormKet (N : ℕ) := NormKet (NQubitDim N)

/-- Operators on the Hilbert space of `N` qubits.

This is the space of linear operators acting on `NQubitKet N`.
-/
abbrev NQubitOp (N : ℕ) := Op (NQubitDim N)

/-- Hermitian operators on the Hilbert space of `N` qubits.

These are the self-adjoint operators on the `N`-qubit Hilbert space, used for
observables and Hamiltonians.
-/
abbrev NQubitHermitianOp (N : ℕ) := HermitianOp (NQubitDim N)

/-- Density operators on the Hilbert space of `N` qubits.

These represent mixed quantum states on `N` qubits.
-/
abbrev NQubitDensityOp (N : ℕ) := DensityOp (NQubitDim N)

/-- Unitary operators on the Hilbert space of `N` qubits.

These are the reversible evolutions on `N` qubits.
-/
abbrev NQubitUnitaryOp (N : ℕ) := UnitaryOp (NQubitDim N)

/-- The computational-basis indexing equivalence
`BitString N ≃ Fin (2 ^ N)`.

This equivalence is the basic bridge between two equivalent ways of labeling the
standard basis:

* by bitstrings `z : BitString N`, and
* by raw indices in `Fin (2 ^ N)`.

Later files use this equivalence repeatedly when defining operators entrywise in
the computational basis.
-/
def bitStringEquiv (N : ℕ) : BitString N ≃ Fin (NQubitDim N) :=
  Math.RepresentationTheory.tensorIndexEquiv 2 N

/-- The computational-basis ket corresponding to a bitstring.

This is the basis vector `|z⟩` associated with the bitstring `z`.
-/
def computationalBasisKet (N : ℕ) (z : BitString N) : NQubitKet N :=
  stdKet (NQubitDim N) (bitStringEquiv N z)

/-- The normalized computational-basis state corresponding to a bitstring.

This is the same computational-basis vector as `computationalBasisKet`, but
packaged as a normalized ket.
-/
def computationalBasisState (N : ℕ) (z : BitString N) : NQubitNormKet N :=
  stdNormKet (NQubitDim N) (bitStringEquiv N z)

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas expose the basic structural properties of the `N`-qubit packaging.
They are intended as the first interface for later definitions of local qubit
operators, Pauli strings, and the standard QAOA mixer Hamiltonian.

Most of them are small, but they serve as stable rewrite rules for later files.
In particular, they make it easy to move back and forth between bitstring
notation and normalized computational-basis states.
-/

/-- The `N`-qubit Hilbert-space dimension `2 ^ N` is nonzero.

This is the minimal type-level fact needed so that standard basis kets and
normalized basis states are available on the `N`-qubit space.
-/
instance instNeZeroNQubitDim (N : ℕ) : NeZero (NQubitDim N) where
  out := pow_ne_zero N (by decide : (2 : ℕ) ≠ 0)

/-- The computational-basis indexing equivalence acts as
`tensorIndexEquiv 2 N`.

This theorem is mostly definitional, but it is useful as a named simplification
rule when later proofs want to unfold `bitStringEquiv`.
-/
@[simp]
theorem bitStringEquiv_apply {N : ℕ} (z : BitString N) :
    bitStringEquiv N z = Math.RepresentationTheory.tensorIndexEquiv 2 N z := rfl

/-- The underlying ket of a computational-basis state is the corresponding
computational-basis ket.

In other words, forgetting the normalization wrapper around `computationalBasisState`
recovers the plain basis ket `computationalBasisKet`.
-/
@[simp]
theorem computationalBasisState_toKet (N : ℕ) (z : BitString N) :
    (computationalBasisState N z).toKet = computationalBasisKet N z := rfl

/-- Computational-basis states are normalized by construction.

This records explicitly that each basis ket has unit norm.
-/
@[simp]
theorem computationalBasisKet_IsNormalized (N : ℕ) (z : BitString N) :
    (computationalBasisKet N z).IsNormalized := by
  unfold computationalBasisKet
  simp

/-- The normalized computational-basis state associated with a bitstring is
obtained by packaging the corresponding computational-basis ket with its
normalization proof.

This theorem makes the structure of `computationalBasisState` explicit and is
useful when later proofs want to unfold it down to the underlying ket and its
normalization certificate.
-/
@[simp]
theorem computationalBasisState_eq (N : ℕ) (z : BitString N) :
    computationalBasisState N z =
      ⟨computationalBasisKet N z, computationalBasisKet_IsNormalized N z⟩ := rfl

/-- `bitStringHammingDist` is just Mathlib's `hammingDist` on `Fin N → Fin 2`. -/
@[simp]
theorem bitStringHammingDist_eq_hammingDist {N : ℕ} (z w : BitString N) :
    bitStringHammingDist z w = hammingDist z w := rfl

/-- A bitstring has Hamming distance `0` from itself. -/
@[simp]
theorem bitStringHammingDist_self {N : ℕ} (z : BitString N) :
    bitStringHammingDist z z = 0 := hammingDist_self z

/-- Hamming distance on bitstrings is symmetric. -/
theorem bitStringHammingDist_comm {N : ℕ} (z w : BitString N) :
    bitStringHammingDist z w = bitStringHammingDist w z := hammingDist_comm z w

/-- Restricted Hamming distance on all qubits is the ordinary Hamming distance. -/
@[simp]
theorem bitStringHammingDistOn_univ {N : ℕ} (z w : BitString N) :
    bitStringHammingDistOn (Finset.univ : Finset (Fin N)) z w = bitStringHammingDist z w := rfl

/-- If the selected qubit does not change, inserting it into the restricted
distance set does not change the restricted Hamming distance. -/
theorem bitStringHammingDistOn_insert_same {N : ℕ} (s : Finset (Fin N))
    (z w : BitString N) (j : Fin N) (_hj : j ∉ s) (hwj : w j = z j) :
    bitStringHammingDistOn (insert j s) z w = bitStringHammingDistOn s z w := by
  unfold bitStringHammingDistOn
  rw [Finset.filter_insert]
  simp [hwj]

/-- Acting on a computational-basis ket picks out the corresponding matrix
column.

This is the standard linear-algebra fact that multiplying a matrix by a basis
vector selects the corresponding column. It is used repeatedly when turning
operator equalities into coordinate formulas on computational-basis states.
-/
@[simp]
theorem op_mul_computationalBasisKet_vec {N : ℕ} (A : NQubitOp N)
    (z : BitString N) (iy : Fin (NQubitDim N)) :
    (A * computationalBasisKet N z : NQubitKet N).vec iy =
      A iy (bitStringEquiv N z) := by
  simp [computationalBasisKet, Matrix.mulVec, dotProduct]

end

end Qubits
