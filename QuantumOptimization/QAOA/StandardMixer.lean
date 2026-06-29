import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import QuantumOptimization.Qubits.PauliOperators

/-!
# Standard QAOA Mixer — local exponential formulas, Hamming-distance amplitudes

The standard QAOA mixer Hamiltonian `B = ∑_j X_j` on an `N`-qubit Hilbert space,
together with its matrix-exponential factorization and explicit basis-state amplitudes.

Because the local Pauli `X` terms commute, the exponential `exp(-i β B)` factors into
a product of single-qubit exponentials, and each factor has the closed form
`cos β · I - i sin β · X_j`. The final amplitude of a target basis state `|w⟩` starting
from `|z⟩` depends only on the Hamming distance `d_H(z, w)`.

## Main definitions
- `standardMixerOp`: the mixer operator `B = ∑_j X_j`
- `localMixerFactor`: the one-qubit factor `cos β · I - i sin β · X_j`
- `standardMixerHamiltonian`: the Hermitian packaging of the mixer

## Main statements
- `exp_localPauliX`: `exp(-i β X_j) = localMixerFactor N β j`
- `standardMixerOp_isHermitian`: the standard mixer is Hermitian
- `exp_standardMixerOp`: `exp(-i β B) = ∏_j exp(-i β X_j)`
- `exp_standardMixerOp_on_basis_vec`: amplitude is `(cos β)^(N-d) · (-i sin β)^d`
-/

namespace QAOA

open Quantum.Operators
open Quantum.Gates
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section defines the standard QAOA mixer as the sum of the local Pauli `X`
operators on each qubit of an `N`-qubit register.
-/

/-- The standard mixer operator `B = ∑_j X_j` on `N` qubits. -/
def standardMixerOp (N : ℕ) : Qubits.NQubitOp N :=
  ∑ j : Fin N, Qubits.localPauliX j

/-- The one-qubit mixer factor attached to qubit `j`.

This is the closed form of `exp(-i β X_j)`.
-/
def localMixerFactor (N : ℕ) (β : ℝ) (j : Fin N) : Qubits.NQubitOp N :=
  (Real.cos β : ℂ) • (1 : Qubits.NQubitOp N) +
    (((-Complex.I) * Real.sin β : ℂ)) • Qubits.localPauliX j

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas establish the basic structural properties needed for QAOA:

- the standard mixer is Hermitian, so it can serve as a valid Hamiltonian;
- the local Pauli `X` terms commute, so the exponential of the mixer factors
  into a product of single-qubit exponentials;
- each local exponential `exp(-i β X_j)` has the expected closed form
  `cos β · I - i sin β · X_j`.

They also record the first operational fact about the mixer: on a
computational-basis ket, the standard mixer produces the superposition obtained
by flipping each qubit in turn.
-/

-- ----------------------------------------------------------------------------
-- Subsection: Local Exponential Formulas
-- ----------------------------------------------------------------------------

/-!
This block isolates the single-qubit building blocks of the mixer unitary. The
structural Pauli facts needed here, such as Hermiticity and commutation of the
lifted `X_j`, live in `Qubits.PauliOperators`. What remains in this file is the
QAOA-specific exponential analysis.
-/

/-- The local mixer factor acts on a computational-basis ket by leaving it in
place with amplitude `cos β` and flipping the selected qubit with amplitude
`-i sin β`.
-/
theorem localMixerFactor_on_basis {N : ℕ} (β : ℝ) (j : Fin N) (z : Qubits.BitString N) :
    localMixerFactor N β j * Qubits.computationalBasisKet N z =
      (Real.cos β : ℂ) • Qubits.computationalBasisKet N z +
        (((-Complex.I) * Real.sin β : ℂ)) •
          Qubits.computationalBasisKet N (Qubits.flipBitAt z j) := by
  have h1 :
      (1 : Qubits.NQubitOp N) * Qubits.computationalBasisKet N z =
        Qubits.computationalBasisKet N z := by
    ext i
    rw [op_mul_ket_vec]
    exact congrArg (fun v => v i) (Matrix.one_mulVec ((Qubits.computationalBasisKet N z).vec))
  unfold localMixerFactor
  rw [add_op_mul_ket, smul_op_mul_ket, smul_op_mul_ket]
  rw [h1, Qubits.localPauliX_on_basis]

/-- The even powers of `(-β i)` are the expected scalar coefficients in the
matrix-exponential expansion of `exp(-i β X_j)`. -/
private lemma localMixerScalar_pow_even (β : ℝ) (n : ℕ) :
    ((((-β : ℝ) * Complex.I : ℂ)) ^ (2 * n)) =
      ((-1 : ℂ) ^ n) * ((β : ℂ) ^ (2 * n)) := by
  have hc2 : ((((-β : ℝ) * Complex.I : ℂ)) ^ 2) = -((β : ℂ) ^ 2) := by
    ring_nf
    simp
  rw [pow_mul, hc2]
  rw [show (-((β : ℂ) ^ 2)) = (-1 : ℂ) * ((β : ℂ) ^ 2) by ring]
  rw [mul_pow, ← pow_mul]

/-- The odd powers of `(-β i)` are the expected scalar coefficients in the
matrix-exponential expansion of `exp(-i β X_j)`. -/
private lemma localMixerScalar_pow_odd (β : ℝ) (n : ℕ) :
    ((((-β : ℝ) * Complex.I : ℂ)) ^ (2 * n + 1)) =
      (((-1 : ℂ) ^ n) * ((β : ℂ) ^ (2 * n + 1))) * (-Complex.I) := by
  rw [pow_add, localMixerScalar_pow_even β n]
  rw [show ((β : ℂ) ^ (2 * n + 1)) = ((β : ℂ) ^ (2 * n)) * (β : ℂ) by
    rw [pow_add]
    simp]
  simp [Complex.ofReal_neg]
  ring

set_option maxHeartbeats 600000 in
-- These `HasSum` conversions are expensive for the elaborator.
private lemma localMixer_even_hasSum {N : ℕ} (β : ℝ) (j : Fin N) :
    HasSum
      (fun n : ℕ =>
        (((2 * n).factorial : ℂ)⁻¹) •
          (((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) ^ (2 * n)))
      ((Real.cos β : ℂ) • (1 : Qubits.NQubitOp N)) := by
  -- After restricting to even powers, `X_j^(2n)` collapses to the identity and the
  -- scalar coefficients are exactly the cosine power series.
  have h_even_term (n : ℕ) :
      (((2 * n).factorial : ℂ)⁻¹) •
          (((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) ^ (2 * n)) =
        ((((-1 : ℂ) ^ n) * ((β : ℂ) ^ (2 * n)) / ((2 * n).factorial : ℂ)) : ℂ) •
          (1 : Qubits.NQubitOp N) := by
    rw [smul_pow, Qubits.localPauliX_pow_even, localMixerScalar_pow_even, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hcos :
      HasSum (fun n : ℕ => (-1 : ℂ) ^ n * (β : ℂ) ^ (2 * n) / ((2 * n).factorial : ℂ))
        (Real.cos β) := by
    simpa using (Complex.hasSum_cos (β : ℂ))
  convert hcos.smul_const (1 : Qubits.NQubitOp N) using 1
  funext n
  exact h_even_term n

set_option maxHeartbeats 600000 in
-- These `HasSum` conversions are expensive for the elaborator.
private lemma localMixer_odd_hasSum {N : ℕ} (β : ℝ) (j : Fin N) :
    HasSum
      (fun n : ℕ =>
        (((2 * n + 1).factorial : ℂ)⁻¹) •
          (((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) ^ (2 * n + 1)))
      ((((-Complex.I) * Real.sin β : ℂ)) • Qubits.localPauliX j) := by
  -- The odd powers contribute a single copy of `X_j`, and the remaining scalar
  -- series is the sine series multiplied by `-i`.
  have h_odd_term (n : ℕ) :
      (((2 * n + 1).factorial : ℂ)⁻¹) •
          (((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) ^ (2 * n + 1)) =
        (((-Complex.I) *
              (((-1 : ℂ) ^ n) * (β : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)) :
            ℂ)) •
          Qubits.localPauliX j := by
    rw [smul_pow, Qubits.localPauliX_pow_odd, localMixerScalar_pow_odd, smul_smul]
    congr 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hsin :
      HasSum (fun n : ℕ =>
          (-1 : ℂ) ^ n * (β : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ))
        (Real.sin β) := by
    simpa using (Complex.hasSum_sin (β : ℂ))
  have h_odd_coeff :
      HasSum
        (fun n : ℕ =>
          (-Complex.I) *
            (((-1 : ℂ) ^ n) * (β : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ)))
        (((-Complex.I) * Real.sin β : ℂ)) := by
    simpa using hsin.mul_left (-Complex.I)
  convert h_odd_coeff.smul_const (Qubits.localPauliX j) using 1
  funext n
  exact h_odd_term n

set_option maxHeartbeats 600000 in
-- Combining the even and odd matrix-exponential series also needs extra heartbeats.
private lemma exp_localPauliX_aux (N : ℕ) (β : ℝ) (j : Fin N) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) =
      localMixerFactor N β j := by
  -- Split the exponential series into even and odd parts, then identify those
  -- two subseries with cosine and `-i` times sine.
  have hsum :
      HasSum
        (fun n : ℕ =>
          ((n.factorial : ℂ)⁻¹) • (((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) ^ n))
        (((Real.cos β : ℂ) • (1 : Qubits.NQubitOp N)) +
          ((((-Complex.I) * Real.sin β : ℂ)) • Qubits.localPauliX j)) :=
    (localMixer_even_hasSum β j).even_add_odd (localMixer_odd_hasSum β j)
  rw [NormedSpace.exp_eq_tsum ℂ]
  simpa [localMixerFactor] using hsum.tsum_eq

/-- The exponential of a local Pauli `X` term has the expected closed form.

This is the operator identity
\[
  e^{-i \beta X_j} = \cos(\beta)\, I - i \sin(\beta)\, X_j.
\]

It is the local building block for explicit formulas for the standard mixer
unitary.
-/
theorem exp_localPauliX (N : ℕ) (β : ℝ) (j : Fin N) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) =
      localMixerFactor N β j := by
  simpa using exp_localPauliX_aux N β j

/-- The local exponential `exp(-i β X_j)` acts on a computational-basis ket by
leaving it in place with amplitude `cos β` and flipping the selected qubit with
amplitude `-i sin β`.

This follows immediately from `exp_localPauliX` and the explicit basis action
of `localMixerFactor`.
-/
theorem exp_localPauliX_on_basis {N : ℕ} (β : ℝ) (j : Fin N) (z : Qubits.BitString N) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) *
        Qubits.computationalBasisKet N z =
      (Real.cos β : ℂ) • Qubits.computationalBasisKet N z +
        (((-Complex.I) * Real.sin β : ℂ)) •
          Qubits.computationalBasisKet N (Qubits.flipBitAt z j) := by
  rw [exp_localPauliX]
  exact localMixerFactor_on_basis β j z

-- ----------------------------------------------------------------------------
-- Subsection: Global Mixer Properties
-- ----------------------------------------------------------------------------

/-!
These are the first genuinely global facts about the standard mixer
\[
  B = \sum_j X_j.
\]
They show that `B` is a valid Hermitian Hamiltonian and describe its direct
action on computational-basis states.
-/

/-- The standard mixer operator is Hermitian. -/
theorem standardMixerOp_isHermitian (N : ℕ) :
    (standardMixerOp N).IsHermitian := by
  unfold standardMixerOp
  rw [Matrix.IsHermitian]
  rw [Matrix.conjTranspose_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact Qubits.localPauliX_hermitian j

/-- The standard mixer acts on a computational-basis ket by producing the
superposition of all basis kets obtained from it by flipping one qubit at a
time.

Equivalently,
\[
  B |z\rangle = \sum_j |z^{(j)}\rangle,
\]
where `z^{(j)}` denotes the bitstring obtained from `z` by flipping its `j`-th
bit.

Because `Ket` does not carry a `Finset.sum` instance in this library, the
right-hand side is expressed by its coordinate function rather than by a direct
finite sum of kets.
-/
theorem standardMixerOp_on_basis (N : ℕ) (z : Qubits.BitString N) :
    standardMixerOp N * Qubits.computationalBasisKet N z =
      ⟨fun iy => ∑ j : Fin N, (Qubits.computationalBasisKet N (Qubits.flipBitAt z j)).vec iy⟩ := by
  ext iy
  unfold standardMixerOp
  rw [sum_op_mul_ket_vec]
  apply Finset.sum_congr rfl
  intro j hj
  simpa using congrArg (fun ψ : Qubits.NQubitKet N => ψ.vec iy)
    (Qubits.localPauliX_on_basis (j := j) (z := z))

-- ----------------------------------------------------------------------------
-- Subsection: Global Exponential Formulas
-- ----------------------------------------------------------------------------

/-!
The final block upgrades the global mixer from an operator to a unitary
evolution. Since the local Pauli `X` terms commute, the matrix exponential of
the full mixer factors into the product of the local exponentials.
-/

-- ----------------------------------------------------------------------------
-- Subsection: Finite-Set Mixer Products
-- ----------------------------------------------------------------------------

/-!
The private helpers below organize the finite-set induction behind the final
Hamming-distance formula. They are kept local to this file because they encode
proof structure rather than reusable quantum interfaces.
-/

/-- Agreement of bitstrings outside a chosen finite set of qubits. -/
private def SameOutsideSet {N : ℕ} (s : Finset (Fin N))
    (z w : Qubits.BitString N) : Prop :=
  ∀ k : Fin N, k ∉ s → w k = z k

private instance sameOutsideSetDecidable {N : ℕ} (s : Finset (Fin N))
    (z w : Qubits.BitString N) : Decidable (SameOutsideSet s z w) := by
  classical
  infer_instance

/-- The amplitude contributed by a single flipped qubit in the standard mixer. -/
private def localMixerCoeff (β : ℝ) : ℂ :=
  (-Complex.I * Real.sin β : ℂ)

/-- The product of the local mixer factors over a finite set of qubits. -/
private def mixerProdOn (N : ℕ) (s : Finset (Fin N)) (β : ℝ) : Qubits.NQubitOp N :=
  s.noncommProd
    (fun j => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
    (by
      intro i hi j hj hij
      exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)

/-- Agreement outside the empty set means equality of bitstrings. -/
private theorem sameOutsideSet_empty {N : ℕ} (z w : Qubits.BitString N) :
    SameOutsideSet (∅ : Finset (Fin N)) z w ↔ w = z := by
  constructor
  · intro h
    funext k
    exact h k (by simp)
  · intro h k hk
    simp [h]

/-- If the inserted qubit is unchanged, agreement outside `insert j s` reduces
to agreement outside `s`. -/
private theorem sameOutsideSet_insert_same {N : ℕ} (s : Finset (Fin N))
    (z w : Qubits.BitString N) (j : Fin N)
    (h : SameOutsideSet (insert j s) z w) (hwj : w j = z j) :
    SameOutsideSet s z w := by
  intro k hk
  by_cases hkj : k = j
  · simpa [hkj] using hwj
  · exact h k (by simp [hk, hkj])

/-- If the inserted qubit is flipped, agreement outside `insert j s` becomes
agreement outside `s` relative to the flipped bitstring. -/
private theorem sameOutsideSet_insert_flip {N : ℕ} (s : Finset (Fin N))
    (z w : Qubits.BitString N) (j : Fin N) (hj : j ∉ s)
    (h : SameOutsideSet (insert j s) z w)
    (hwj : w j = Qubits.flipBit (z j)) :
    SameOutsideSet s (Qubits.flipBitAt z j) w := by
  intro k hk
  by_cases hkj : k = j
  · subst hkj
    simpa [Qubits.flipBitAt]
  · rw [Qubits.flipBitAt_apply_of_ne z hkj]
    exact h k (by simp [hk, hkj])

set_option maxHeartbeats 600000 in
-- The insert-step coefficient recursion combines basis action and finite-set combinatorics.
private theorem mixerProdOn_basis_coeff {N : ℕ} (s : Finset (Fin N)) (β : ℝ) :
    ∀ z w : Qubits.BitString N,
      ((mixerProdOn N s β) * Qubits.computationalBasisKet N z).vec (Qubits.bitStringEquiv N w) =
        if SameOutsideSet s z w then
          (Real.cos β : ℂ) ^ (s.card - Qubits.bitStringHammingDistOn s z w) *
            (localMixerCoeff β) ^ Qubits.bitStringHammingDistOn s z w
        else 0 := by
  classical
  refine Finset.induction_on s ?_ ?_
  · intro z w
    -- On the empty set, the product is the identity, so the only surviving
    -- basis amplitude is the diagonal one `w = z`.
    by_cases h : w = z
    · subst h
      simp [mixerProdOn, Qubits.bitStringHammingDistOn, Qubits.computationalBasisKet,
        op_mul_ket_vec, SameOutsideSet]
    · have hex : ∃ x, w x ≠ z x := by
        by_contra hforall
        push_neg at hforall
        exact h (funext hforall)
      have hz : z ≠ w := by simpa [eq_comm] using h
      simp [mixerProdOn, Qubits.bitStringHammingDistOn, Qubits.computationalBasisKet,
        op_mul_ket_vec, SameOutsideSet, hz, hex]
  · intro j s hj ih z w
    -- Insert one more qubit factor, commute it to the right, and apply the local
    -- two-term basis-action formula. The two branches correspond to whether `w`
    -- agrees with `z` at `j` or is obtained by flipping the `j`-th bit.
    have hinsert :
        mixerProdOn N (insert j s) β =
          NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) *
            mixerProdOn N s β := by
      unfold mixerProdOn
      rw [Finset.noncommProd_insert_of_notMem
        (s := s)
        (a := j)
        (f := fun k => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX k))
        (comm := fun i _ k _ _ =>
          (Qubits.localPauliX_commute i k).smul_left _ |>.smul_right _ |>.exp)
        hj]
    have hcomm :
        Commute
          (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
          (mixerProdOn N s β) := by
      unfold mixerProdOn
      exact Finset.noncommProd_commute
        s
        (fun k => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX k))
        (fun i _ k _ _ => (Qubits.localPauliX_commute i k).smul_left _ |>.smul_right _ |>.exp)
        (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
        (fun k _ => (Qubits.localPauliX_commute j k).smul_left _ |>.smul_right _ |>.exp)
    have hprod :
        mixerProdOn N (insert j s) β =
          mixerProdOn N s β *
            NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) := by
      rw [hinsert, hcomm.eq]
    have hlocal := exp_localPauliX_on_basis (N := N) β j z
    rw [hprod, op_mul_op_mul_ket, hlocal, Op_mul_add_ket, op_mul_smul_ket, op_mul_smul_ket,
      Ket.add_vec, Ket.smul_vec, Ket.smul_vec]
    by_cases hout : SameOutsideSet (insert j s) z w
    · by_cases hwj : w j = z j
      · have hs : SameOutsideSet s z w :=
          sameOutsideSet_insert_same s z w j hout hwj
        have hsflip : ¬ SameOutsideSet s (Qubits.flipBitAt z j) w := by
          intro hs'
          have hbad := hs' j hj
          rw [Qubits.flipBitAt] at hbad
          exact Qubits.flipBit_ne_self (z j) (by simpa [hwj] using hbad.symm)
        simp only [Pi.smul_apply] at *
        rw [ih z w, ih (Qubits.flipBitAt z j) w]
        rw [if_pos hout, if_pos hs, if_neg hsflip]
        simp only [Complex.ofReal_cos, Complex.ofReal_sin, localMixerCoeff, smul_eq_mul,
          mul_zero, add_zero, neg_mul]
        rw [Qubits.bitStringHammingDistOn_insert_same s z w j hj hwj,
          Finset.card_insert_of_notMem hj]
        have hdist_le : Qubits.bitStringHammingDistOn s z w ≤ s.card := by
          unfold Qubits.bitStringHammingDistOn
          exact Finset.card_filter_le _ _
        -- The new qubit contributes one extra factor of `cos β`, while the
        -- restricted Hamming distance on `s` is unchanged.
        rw [Nat.succ_sub hdist_le, pow_succ]
        ring_nf
      · have hwj' : w j = Qubits.flipBit (z j) := Qubits.eq_flipBit_of_ne hwj
        have hsz : ¬ SameOutsideSet s z w := by
          intro hs
          exact hwj (hs j hj)
        have hsflip : SameOutsideSet s (Qubits.flipBitAt z j) w :=
          sameOutsideSet_insert_flip s z w j hj hout hwj'
        simp only [Pi.smul_apply] at *
        rw [ih z w, ih (Qubits.flipBitAt z j) w]
        rw [if_pos hout, if_neg hsz, if_pos hsflip]
        simp only [Complex.ofReal_cos, Complex.ofReal_sin, localMixerCoeff, smul_eq_mul,
          mul_zero, zero_add, neg_mul]
        rw [Qubits.bitStringHammingDistOn_flipBitAt_of_not_mem s z w j hj,
          Qubits.bitStringHammingDistOn_insert_flip s z w j hj hwj',
          Finset.card_insert_of_notMem hj]
        -- In the flipped branch, the new qubit contributes one extra factor of
        -- `-i sin β`, and the restricted Hamming distance increases by one.
        rw [show s.card + 1 - (Qubits.bitStringHammingDistOn s z w + 1) =
            s.card - Qubits.bitStringHammingDistOn s z w by omega]
        ring_nf
    · have hsz : ¬ SameOutsideSet s z w := by
        intro hs
        exact hout (fun k hk => by
          have hks : k ∉ s := by
            intro hks
            exact hk (by simp [hks])
          exact hs k hks)
      have hsflip : ¬ SameOutsideSet s (Qubits.flipBitAt z j) w := by
        intro hs
        exact hout (fun k hk => by
          by_cases hkj : k = j
          · subst hkj
            exact False.elim (hk (by simp))
          · have hks : k ∉ s := by
              intro hks
              exact hk (by simp [hks, hkj])
            have hk' := hs k hks
            rw [Qubits.flipBitAt_apply_of_ne z hkj] at hk'
            exact hk')
      simp only [Pi.smul_apply] at *
      rw [ih z w, ih (Qubits.flipBitAt z j) w]
      simp [hout, hsz, hsflip]

-- ----------------------------------------------------------------------------
-- Subsection: Exponential Factorization
-- ----------------------------------------------------------------------------

/-- The exponential of the standard mixer factors into the product of the
single-qubit exponentials.

This is the matrix-exponential form of the familiar identity
\[
  e^{-i \beta \sum_j X_j} = \prod_j e^{-i \beta X_j},
\]
valid because the local Pauli `X` terms commute.
-/
theorem exp_standardMixerOp (N : ℕ) (β : ℝ) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • standardMixerOp N) =
      mixerProdOn N (Finset.univ : Finset (Fin N)) β := by
  change NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • standardMixerOp N) =
      (Finset.univ : Finset (Fin N)).noncommProd
        (fun j => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
        (fun i _ j _ _ => (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)
  simpa [standardMixerOp, Finset.smul_sum] using
    (Matrix.exp_sum_of_commute (s := (Finset.univ : Finset (Fin N)))
      (f := fun j => ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
      (h := by
        intro i hi j hj hij
        exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _))

-- ----------------------------------------------------------------------------
-- Subsection: Hamming-Distance Amplitudes
-- ----------------------------------------------------------------------------

/-!
These theorems are the operational payoff of the previous factorization and
finite-set induction. They express the amplitude of a target basis state
entirely in terms of its Hamming distance from the input bitstring.
-/

/-- The coordinate of the standard mixer exponential on a target computational
basis state depends only on the Hamming distance from the input bitstring.

For a basis input `|z⟩`, the amplitude of `|w⟩` is
`(cos β)^(N - d_H(z,w)) (-i sin β)^(d_H(z,w))`.
-/
theorem exp_standardMixerOp_on_basis_vec (N : ℕ) (β : ℝ)
    (z w : Qubits.BitString N) :
    (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • standardMixerOp N) *
        Qubits.computationalBasisKet N z).vec (Qubits.bitStringEquiv N w) =
      (Real.cos β : ℂ) ^ (N - Qubits.bitStringHammingDist z w) *
        (((-Complex.I) * Real.sin β : ℂ) ^ Qubits.bitStringHammingDist z w) := by
  rw [exp_standardMixerOp]
  simpa [mixerProdOn, SameOutsideSet, localMixerCoeff, Qubits.bitStringHammingDistOn_univ] using
    mixerProdOn_basis_coeff (N := N) (s := (Finset.univ : Finset (Fin N))) β z w

/-- The exponential mixer acts on a computational-basis ket with amplitudes
determined by Hamming distance from the input bitstring.

The coefficient of the basis state labeled by `w` is
`(cos β)^(N - d_H(z,w)) (-i sin β)^(d_H(z,w))`.
-/
theorem exp_standardMixerOp_on_basis (N : ℕ) (β : ℝ) (z : Qubits.BitString N) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • standardMixerOp N) *
        Qubits.computationalBasisKet N z =
      ⟨fun iy =>
        let w := (Qubits.bitStringEquiv N).symm iy
        (Real.cos β : ℂ) ^ (N - Qubits.bitStringHammingDist z w) *
          (((-Complex.I) * Real.sin β : ℂ) ^ Qubits.bitStringHammingDist z w)⟩ := by
  ext iy
  let w := (Qubits.bitStringEquiv N).symm iy
  simpa [w] using exp_standardMixerOp_on_basis_vec N β z w

/-- The standard QAOA mixer Hamiltonian on `N` qubits. -/
def standardMixerHamiltonian (N : ℕ) : Qubits.NQubitHermitianOp N :=
  ⟨standardMixerOp N, standardMixerOp_isHermitian N⟩

end

end QAOA
