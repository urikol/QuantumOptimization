import QuantumOptimization.Qubits.LocalOperators
import QuantumOptimization.Quantum.Gates

/-!
# Pauli Operators on N Qubits

Pauli-specific local operators acting on a designated qubit inside an `N`-qubit
register.

This file specializes the generic local-operator construction from
`LocalOperators.lean` to the Pauli `X`, `Y`, and `Z` matrices. It also records
their explicit action on computational-basis states.

Those basis-action theorems are especially important for later developments:

* `Z` acts diagonally and is therefore suited to Ising- and spin-glass-style
  Hamiltonians,
* `X` flips a chosen computational-basis bit, and
* `Y` flips a chosen computational-basis bit while introducing the standard
  phase.

Together, these results provide the core Pauli interface for the QAOA and
spin-glass files.
-/

namespace Qubits

open Quantum.Operators
open Quantum.Gates

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section specializes the generic `localOp` construction to the Pauli `X`,
`Y`, and `Z` operators on a chosen qubit.

It also introduces the basic auxiliary notions needed to describe their action
on computational-basis states, namely bit flipping and the phase attached to
Pauli `Y`.
-/

/-- Bit flip on a single computational-basis bit.

This is the permutation exchanging `0` and `1`.
-/
def flipBit (b : Fin 2) : Fin 2 :=
  if b = 0 then 1 else 0

/-- Flip the bit at qubit `j` in an `N`-bit string.

This is the bitstring obtained from `z` by applying `flipBit` at position `j`
and leaving all other positions unchanged.
-/
def flipBitAt {N : ℕ} (z : BitString N) (j : Fin N) : BitString N :=
  fun k => if k = j then flipBit (z k) else z k

/-- The phase picked up by the Pauli `Y` operator on a computational-basis bit.

With the usual convention for the Pauli `Y` matrix, the basis state `|0⟩` is
sent to `i |1⟩`, while `|1⟩` is sent to `-i |0⟩`. This definition packages that
phase factor as a function of the input bit.
-/
def pauliYPhase (b : Fin 2) : ℂ :=
  if b = 0 then Complex.I else -Complex.I

/-- The Pauli `X` operator acting on qubit `j`.

This is the lifted single-qubit Pauli `X`, acting nontrivially only at the
chosen qubit position.
-/
def localPauliX {N : ℕ} (j : Fin N) : NQubitOp N :=
  localOp X j

/-- The Pauli `Y` operator acting on qubit `j`.

This is the lifted single-qubit Pauli `Y`, acting nontrivially only at the
chosen qubit position.
-/
def localPauliY {N : ℕ} (j : Fin N) : NQubitOp N :=
  localOp Y j

/-- The Pauli `Z` operator acting on qubit `j`.

This is the lifted single-qubit Pauli `Z`, acting nontrivially only at the
chosen qubit position.
-/
def localPauliZ {N : ℕ} (j : Fin N) : NQubitOp N :=
  localOp Z j

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas identify the lifted Pauli operators with `localOp` and describe
their computational-basis action.

The theorems naturally split into several layers:

* elementary bit-flip identities,
* Hamming-distance bookkeeping for bit flips,
* one-qubit matrix-entry facts for `X` and `Y`, and
* lifted-operator structure and computational-basis action.
-/

-- ----------------------------------------------------------------------------
-- Subsection: Bitstring Operations
-- ----------------------------------------------------------------------------

/-!
These lemmas are purely classical. They describe how `flipBit` and `flipBitAt`
behave before any operator-theoretic structure enters.
-/

/-- Flipping `0` gives `1`.

This is one half of the defining behavior of `flipBit`.
-/
@[simp]
theorem flipBit_zero : flipBit (0 : Fin 2) = 1 := by
  simp [flipBit]

/-- Flipping `1` gives `0`.

This is the other half of the defining behavior of `flipBit`.
-/
@[simp]
theorem flipBit_one : flipBit (1 : Fin 2) = 0 := by
  simp [flipBit]

/-- Flipping a bit changes it.

This records that `flipBit` has no fixed points.
-/
theorem flipBit_ne_self (b : Fin 2) : flipBit b ≠ b := by
  fin_cases b <;> simp [flipBit]

/-- Any bit different from `b` is its flip.

Since a qubit basis bit has only two possible values, the only alternative to
`b` is `flipBit b`.
-/
theorem eq_flipBit_of_ne {b c : Fin 2} (h : c ≠ b) : c = flipBit b := by
  fin_cases b <;> fin_cases c <;> simp [flipBit] at h ⊢

/-- The flipped bitstring differs from the original only at the chosen qubit.

At the chosen position `j`, `flipBitAt` applies `flipBit`.
-/
@[simp]
theorem flipBitAt_apply_same {N : ℕ} (z : BitString N) (j : Fin N) :
    flipBitAt z j j = flipBit (z j) := by
  simp [flipBitAt]

/-- Away from the chosen qubit, `flipBitAt` leaves the bitstring unchanged.

So `flipBitAt` modifies exactly one qubit position.
-/
theorem flipBitAt_apply_of_ne {N : ℕ} (z : BitString N) {j k : Fin N} (h : k ≠ j) :
    flipBitAt z j k = z k := by
  simp [flipBitAt, h]

/-- Flipping two distinct qubits commutes.

If `i ≠ j`, then flipping qubit `i` and then qubit `j` gives the same bitstring
as flipping qubit `j` and then qubit `i`.
-/
theorem flipBitAt_comm {N : ℕ} (z : BitString N) {i j : Fin N} (hij : i ≠ j) :
    flipBitAt (flipBitAt z i) j = flipBitAt (flipBitAt z j) i := by
  funext k
  by_cases hk_i : k = i
  · subst k
    simp [flipBitAt, hij]
  · by_cases hk_j : k = j
    · subst k
      simp [flipBitAt, hk_i]
    · simp [flipBitAt, hk_i, hk_j]

/-- Flipping the same qubit twice returns the original bitstring. -/
theorem flipBitAt_involutive {N : ℕ} (z : BitString N) (j : Fin N) :
    flipBitAt (flipBitAt z j) j = z := by
  funext k
  by_cases hk : k = j
  · subst k
    have hz : z j ≠ flipBit (z j) := by
      intro h
      exact flipBit_ne_self (z j) h.symm
    have hflip : flipBit (flipBit (z j)) = z j := by
      symm
      exact eq_flipBit_of_ne (b := flipBit (z j)) (c := z j) hz
    simp [flipBitAt, hflip]
  · simp [flipBitAt, hk]

-- ----------------------------------------------------------------------------
-- Subsection: Hamming Distance on Bitstrings
-- ----------------------------------------------------------------------------

/-!
These lemmas connect the elementary bit-flip operations to the Hamming-distance
interface introduced in `NQubitSpace.lean`. They are the combinatorial bridge
used later by the mixer analysis.
-/

/-- Flipping one qubit changes a bitstring by Hamming distance `1`. -/
theorem bitStringHammingDist_flipBitAt {N : ℕ} (z : BitString N) (j : Fin N) :
    bitStringHammingDist z (flipBitAt z j) = 1 := by
  classical
  unfold bitStringHammingDist hammingDist
  rw [Finset.card_eq_one]
  refine ⟨j, ?_⟩
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hk
    by_cases hkj : k = j
    · exact hkj
    · rw [flipBitAt_apply_of_ne z hkj] at hk
      exact False.elim (hk rfl)
  · intro hk
    subst hk
    simp [flipBitAt]
    simpa [eq_comm] using flipBit_ne_self (z k)

/-- Flipping a qubit outside the selected set does not change the restricted
Hamming distance on that set. -/
theorem bitStringHammingDistOn_flipBitAt_of_not_mem {N : ℕ} (s : Finset (Fin N))
    (z w : BitString N) (j : Fin N) (hj : j ∉ s) :
    bitStringHammingDistOn s (flipBitAt z j) w = bitStringHammingDistOn s z w := by
  unfold bitStringHammingDistOn
  have hfilter :
      s.filter (fun k => flipBitAt z j k ≠ w k) = s.filter (fun k => z k ≠ w k) := by
    apply Finset.filter_congr
    intro k hk
    rw [flipBitAt_apply_of_ne z (by
      intro h
      exact hj (h.symm ▸ hk))]
  exact congrArg Finset.card hfilter

/-- If the selected qubit is flipped, inserting it into the restricted
distance set increases the restricted Hamming distance by `1`. -/
theorem bitStringHammingDistOn_insert_flip {N : ℕ} (s : Finset (Fin N))
    (z w : BitString N) (j : Fin N) (hj : j ∉ s) (hwj : w j = flipBit (z j)) :
    bitStringHammingDistOn (insert j s) z w = bitStringHammingDistOn s z w + 1 := by
  unfold bitStringHammingDistOn
  rw [Finset.filter_insert]
  have hne : z j ≠ w j := by
    simpa [eq_comm, hwj] using flipBit_ne_self (z j)
  simp [hj, hne, Nat.add_comm]

-- ----------------------------------------------------------------------------
-- Subsection: One-Qubit Pauli Entries
-- ----------------------------------------------------------------------------

/-!
These are the raw matrix-entry facts for the single-qubit Pauli matrices. They
feed directly into the generic computational-basis action theorem below.
-/

/-- Diagonal entries of `X` vanish.

This expresses that Pauli `X` does not preserve computational-basis bits; it
always flips them.
-/
@[simp]
theorem pauliX_diag_zero (b : Fin 2) : X b b = 0 := by
  fin_cases b <;> simp [pauliX]

/-- `X` maps each basis bit to its flip with coefficient `1`.

This is the single-qubit matrix-entry form of the usual action of Pauli `X`.
-/
@[simp]
theorem pauliX_flipBit_entry (b : Fin 2) : X (flipBit b) b = 1 := by
  fin_cases b <;> simp [pauliX, flipBit]

/-- Diagonal entries of `Y` vanish.

Like Pauli `X`, Pauli `Y` moves between the two basis bits rather than acting
diagonally.
-/
@[simp]
theorem pauliY_diag_zero (b : Fin 2) : Y b b = 0 := by
  fin_cases b <;> simp [pauliY]

/-- `Y` maps each basis bit to its flip with the standard phase.

This is the single-qubit matrix-entry form of the usual Pauli `Y` action.
-/
@[simp]
theorem pauliY_flipBit_entry (b : Fin 2) : Y (flipBit b) b = pauliYPhase b := by
  fin_cases b <;> simp [pauliY, flipBit, pauliYPhase]

/-- A local operator whose underlying single-qubit matrix flips the basis bit
acts on computational-basis kets by flipping the corresponding qubit.

This is the generic bit-flip analog of
`localOp_apply_computationalBasisKet_of_diagonal` from `LocalOperators.lean`.
If the one-qubit matrix `A` has zero diagonal and sends each basis bit `b` to
its flipped bit with coefficient `η b`, then the lifted operator `localOp A j`
sends `|z⟩` to the basis ket with the `j`-th bit flipped, multiplied by the
corresponding coefficient `η (z j)`.

This theorem is later specialized to the Pauli `X` and `Y` operators.
-/
theorem localOp_on_basis_of_bitFlip {N : ℕ} (A : Op 2)
    (η : Fin 2 → ℂ) (j : Fin N) (z : BitString N)
    (hdiag : ∀ b : Fin 2, A b b = 0)
    (hflip : ∀ b : Fin 2, A (flipBit b) b = η b) :
    localOp A j * computationalBasisKet N z =
      (η (z j)) • computationalBasisKet N (flipBitAt z j) := by
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
      have hwflip : w ≠ flipBitAt z j := by
        intro h
        have : z j = flipBit (z j) := by
          simpa [hwz, flipBitAt] using congrArg (fun u => u j) h
        exact flipBit_ne_self (z j) this.symm
      have hiy : iy ≠ bitStringEquiv N (flipBitAt z j) := by
        intro h
        apply hwflip
        exact (bitStringEquiv N).injective (by simpa [w] using h)
      have hneq : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 N) (flipBitAt z j) = iy := by
        simpa [bitStringEquiv] using Ne.symm hiy
      have hA :
          A ((bitStringEquiv N).symm iy j)
            (((bitStringEquiv N).symm (bitStringEquiv N z)) j) = 0 := by
        have hzj : ((bitStringEquiv N).symm (bitStringEquiv N z)) j = z j := by
          simpa using congrArg (fun z => z j) hsymm
        have hwj : (bitStringEquiv N).symm iy j = z j := by
          simpa [w] using congrArg (fun u => u j) hwz
        rw [hwj, hzj]
        exact hdiag (z j)
      have hrhs :
          ((η (z j)) • computationalBasisKet N (flipBitAt z j) : NQubitKet N).vec iy = 0 := by
        simp [computationalBasisKet, hneq]
      rw [hrhs]
      exact hA
    · have hwflip : w = flipBitAt z j := by
        funext k
        by_cases hk : k = j
        · subst hk
          simp [flipBitAt, eq_flipBit_of_ne hj]
        · rw [flipBitAt_apply_of_ne z hk]
          exact hsame k hk
      have hiy : iy = bitStringEquiv N (flipBitAt z j) := by
        simpa [w] using congrArg (bitStringEquiv N) hwflip
      have hiy' : bitStringEquiv N (flipBitAt z j) = iy := hiy.symm
      have hη :
          A ((bitStringEquiv N).symm iy j)
            (((bitStringEquiv N).symm (bitStringEquiv N z)) j) = η (z j) := by
        have hzj : ((bitStringEquiv N).symm (bitStringEquiv N z)) j = z j := by
          simpa using congrArg (fun z => z j) hsymm
        have hwj : (bitStringEquiv N).symm iy j = flipBit (z j) := by
          simpa [w] using congrArg (fun u => u j) hwflip
        rw [hwj, hzj]
        exact hflip (z j)
      have hrhs :
          ((η (z j)) • computationalBasisKet N (flipBitAt z j) : NQubitKet N).vec iy =
            η (z j) := by
        simp [computationalBasisKet, hiy']
      rw [hrhs]
      exact hη
  · rw [localOp_apply_of_not_sameOutside (A := A)]
    · have hwflip : w ≠ flipBitAt z j := by
        intro h
        apply hsame
        intro k hk
        rw [h]
        exact flipBitAt_apply_of_ne z hk
      have hiy : iy ≠ bitStringEquiv N (flipBitAt z j) := by
        intro h
        apply hwflip
        exact (bitStringEquiv N).injective (by simpa [w] using h)
      have hneq : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 N) (flipBitAt z j) = iy := by
        simpa [bitStringEquiv] using Ne.symm hiy
      simp [computationalBasisKet, hneq]
    · intro h'
      apply hsame
      intro k hk
      have hzk : ((bitStringEquiv N).symm (bitStringEquiv N z)) k = z k := by
        simpa using congrArg (fun z => z k) hsymm
      rw [← hzk]
      simpa [w] using h' k hk

-- ----------------------------------------------------------------------------
-- Subsection: Lifted Pauli Rewriting Lemmas
-- ----------------------------------------------------------------------------

/-!
These lemmas are the basic rewriting bridges between the named lifted Pauli
operators and the underlying generic `localOp` construction.
-/

/-- The lifted Pauli `X` operator is the local lift of the single-qubit Pauli
`X` gate.

This is a definitional bridge theorem for rewriting.
-/
@[simp]
theorem localPauliX_eq_localOp {N : ℕ} (j : Fin N) :
    localPauliX j = localOp X j := rfl

/-- The lifted Pauli `Y` operator is the local lift of the single-qubit Pauli
`Y` gate.

This is a definitional bridge theorem for rewriting.
-/
@[simp]
theorem localPauliY_eq_localOp {N : ℕ} (j : Fin N) :
    localPauliY j = localOp Y j := rfl

/-- The lifted Pauli `Z` operator is the local lift of the single-qubit Pauli
`Z` gate.

This is a definitional bridge theorem for rewriting.
-/
@[simp]
theorem localPauliZ_eq_localOp {N : ℕ} (j : Fin N) :
    localPauliZ j = localOp Z j := rfl

-- ----------------------------------------------------------------------------
-- Subsection: Structural Pauli Lemmas
-- ----------------------------------------------------------------------------

/-!
These theorems record operator-theoretic structure of the lifted Pauli
operators. The dagger/Hermitian facts are available immediately from the
rewriting lemmas above, while the commutation theorem is placed later because
its proof uses the explicit basis action of `localPauliX`.
-/

/-- `SameOutside` is symmetric in its two bitstring arguments. -/
theorem sameOutside_symm {N : ℕ} {j : Fin N} {x y : BitString N} :
    SameOutside j x y ↔ SameOutside j y x := by
  constructor <;> intro h <;> intro k hk
  · symm
    exact h k hk
  · symm
    exact h k hk

/-- Conjugate transpose commutes with lifting a single-qubit operator to a local
operator on qubit `j`. -/
theorem localOp_conjTranspose {N : ℕ} (A : Op 2) (j : Fin N) :
    (localOp A j)† = localOp A† j := by
  ext ix iy
  classical
  let x := (bitStringEquiv N).symm ix
  let y := (bitStringEquiv N).symm iy
  by_cases h : SameOutside j x y
  · have h' : SameOutside j y x := (sameOutside_symm).mp h
    simp [localOp, x, y, h, h', Matrix.conjTranspose_apply]
  · have h' : ¬ SameOutside j y x := by
      intro hyx
      exact h ((sameOutside_symm).mpr hyx)
    simp [localOp, x, y, h, h', Matrix.conjTranspose_apply]

/-- Each local Pauli `X` operator is Hermitian. -/
theorem localPauliX_hermitian {N : ℕ} (j : Fin N) :
    (localPauliX j)† = localPauliX j := by
  rw [localPauliX_eq_localOp, localOp_conjTranspose]
  simp [pauliX_hermitian]

-- ----------------------------------------------------------------------------
-- Subsection: Lifted Pauli Basis Action
-- ----------------------------------------------------------------------------

/-!
These are the main operational theorems for the lifted Pauli operators on
computational-basis states.
-/

/-- A local Pauli `Z` operator acts diagonally on computational-basis kets.

The eigenvalue is the diagonal entry of the one-qubit Pauli `Z` matrix
corresponding to the bit carried by qubit `j`.
-/
theorem localPauliZ_on_basis {N : ℕ} (j : Fin N) (z : BitString N) :
    localPauliZ j * computationalBasisKet N z =
      (Z (z j) (z j)) • computationalBasisKet N z := by
  unfold localPauliZ
  simpa using
    (localOp_apply_computationalBasisKet_of_diagonal
      (A := Z) (η := fun b => Z b b) (j := j) (z := z)
      (hdiag := by intro b; rfl)
      (hoffdiag := by
        intro b c hbc
        fin_cases b <;> fin_cases c <;> simp [pauliZ] at hbc ⊢))

/-- A local Pauli `X` operator flips the chosen computational-basis bit.

This is the `N`-qubit version of the familiar single-qubit identity
`X |b⟩ = |flipBit b⟩`.
-/
theorem localPauliX_on_basis {N : ℕ} (j : Fin N) (z : BitString N) :
    localPauliX j * computationalBasisKet N z =
      computationalBasisKet N (flipBitAt z j) := by
  unfold localPauliX
  simpa using
    (localOp_on_basis_of_bitFlip
      (A := X) (η := fun _ => (1 : ℂ)) (j := j) (z := z)
      (hdiag := pauliX_diag_zero)
      (hflip := pauliX_flipBit_entry))

/-- Each local Pauli `X` operator squares to the identity on the full
`N`-qubit Hilbert space.

This is the lifted version of the familiar single-qubit relation `X^2 = I`.
-/
theorem localPauliX_sq {N : ℕ} (j : Fin N) :
    localPauliX j * localPauliX j = (1 : NQubitOp N) := by
  refine op_eq_of_on_computationalBasis ?_
  intro z
  calc
    (localPauliX j * localPauliX j) * computationalBasisKet N z
        = localPauliX j * (localPauliX j * computationalBasisKet N z) := by
            rw [op_mul_op_mul_ket]
    _ = localPauliX j * computationalBasisKet N (flipBitAt z j) := by
          rw [localPauliX_on_basis]
    _ = computationalBasisKet N (flipBitAt (flipBitAt z j) j) := by
          rw [localPauliX_on_basis]
    _ = computationalBasisKet N z := by rw [flipBitAt_involutive]
    _ = (1 : NQubitOp N) * computationalBasisKet N z := by
          symm
          ext i
          rw [op_mul_ket_vec]
          exact congrArg (fun v => v i) (Matrix.one_mulVec ((computationalBasisKet N z).vec))

/-- Even powers of a local Pauli `X` operator are the identity.

This generalizes `localPauliX_sq` from exponent `2` to any even exponent `2 n`.
-/
theorem localPauliX_pow_even {N : ℕ} (j : Fin N) (n : ℕ) :
    localPauliX j ^ (2 * n) = (1 : NQubitOp N) := by
  have hsq : localPauliX j ^ 2 = (1 : NQubitOp N) := by
    simpa [sq] using localPauliX_sq (N := N) j
  rw [pow_mul, hsq]
  simp

/-- Odd powers of a local Pauli `X` operator reduce to the operator itself.

Together with `localPauliX_pow_even` this gives a complete parity reduction for
powers of `X_j`.
-/
theorem localPauliX_pow_odd {N : ℕ} (j : Fin N) (n : ℕ) :
    localPauliX j ^ (2 * n + 1) = localPauliX j := by
  rw [pow_add, localPauliX_pow_even j n]
  simp

/-- Local Pauli `X` operators on different qubits commute.

More generally, the family `X_j` is pairwise commuting: if `i = j` this is
trivial, and if `i ≠ j` both compositions act on a computational-basis ket by
flipping the same two bits in either order.
-/
theorem localPauliX_commute {N : ℕ} (i j : Fin N) :
    Commute (localPauliX i) (localPauliX j) := by
  by_cases hij : i = j
  · subst hij
    exact Commute.refl _
  · dsimp [Commute]
    exact op_eq_of_on_computationalBasis
      (A := localPauliX i * localPauliX j)
      (B := localPauliX j * localPauliX i) (by
    intro z
    calc
      (localPauliX i * localPauliX j) * computationalBasisKet N z
          = localPauliX i * (localPauliX j * computationalBasisKet N z) := by
              rw [op_mul_op_mul_ket]
      _ = localPauliX i * computationalBasisKet N (flipBitAt z j) := by
            rw [localPauliX_on_basis]
      _ = computationalBasisKet N (flipBitAt (flipBitAt z j) i) := by
            rw [localPauliX_on_basis]
      _ = computationalBasisKet N (flipBitAt (flipBitAt z i) j) := by
            rw [flipBitAt_comm (z := z) (hij := hij)]
      _ = localPauliX j * computationalBasisKet N (flipBitAt z i) := by
            rw [localPauliX_on_basis]
      _ = localPauliX j * (localPauliX i * computationalBasisKet N z) := by
            rw [← localPauliX_on_basis]
      _ = (localPauliX j * localPauliX i) * computationalBasisKet N z := by
            rw [op_mul_op_mul_ket])

/-- A local Pauli `Y` operator flips the chosen computational-basis bit and
adds the standard phase.

This is the `N`-qubit version of the familiar single-qubit identity
`Y |b⟩ = pauliYPhase b • |flipBit b⟩`.
-/
theorem localPauliY_on_basis {N : ℕ} (j : Fin N) (z : BitString N) :
    localPauliY j * computationalBasisKet N z =
      (pauliYPhase (z j)) • computationalBasisKet N (flipBitAt z j) := by
  unfold localPauliY
  simpa using
    (localOp_on_basis_of_bitFlip
      (A := Y) (η := pauliYPhase) (j := j) (z := z)
      (hdiag := pauliY_diag_zero)
      (hflip := pauliY_flipBit_entry))

end

end Qubits
