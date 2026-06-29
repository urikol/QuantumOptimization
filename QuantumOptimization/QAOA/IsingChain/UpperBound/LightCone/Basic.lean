import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import QuantumOptimization.IsingModel.IsingHamiltonian

/-!
# Light-Cone Locality Calculus — `supportedOn` predicate and cost exponential factorization

This file is the foundational layer of the light-cone analysis used in the
elementary upper-bound proof of the QAOA ring-of-disagrees residual energy.

Source: arXiv:1906.08948v2 §IV, l.620–678.

The locality machinery is anchored in a single predicate `supportedOn S O`,
which states that an `N`-qubit operator `O` acts as the identity on every qubit
outside the finite set `S ⊆ Fin N`. It is formulated as a matrix-entry condition
extending `Qubits.SameOutside` from singletons to arbitrary finite subsets, so
that composition under sum / product / scalar multiplication is mechanical.

This file also contains the cost analog of `QAOA.exp_standardMixerOp`, namely
`exp_chainPairInteraction_sum`, factoring the cost-layer exponential into a
non-commutative product of single-bond exponentials. The key step is that any
two `IsingModel.chainPairInteraction k`, `chainPairInteraction k'` commute (both
are diagonal in the computational basis).

## Public deliverables

* `supportedOn` (def) — the matrix-entry predicate.
* `supportedOn_one`, `supportedOn_smul`, `supportedOn_add`, `supportedOn_mul`,
  `supportedOn_mono` — calculus closure properties.
* `supportedOn_localOp`, `supportedOn_localPauliX/Y/Z` — generators.
* `chainPairInteractions_commute` — diagonal-operator commutation.
* `exp_chainPairInteraction_sum` — the cost-layer exponential factorization.

This file is the first of three (`Basic.lean` + `Spreading.lean` +
`Reduction.lean`) implementing the light-cone reduction. The per-layer spreading
bounds live in `Spreading.lean`; the
full-chain ↔ reduced-chain bond expectation reduction (FGG black-box) lives in
`Reduction.lean`.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: AgreeOutside — bitstring agreement on the complement of a finset
-- ============================================================================

/-!
This section generalizes `Qubits.SameOutside` from singletons `{j}` to arbitrary
finite subsets `S ⊆ Fin N`. It is the bitstring-level support predicate that
underlies the matrix-entry definition of `supportedOn`.
-/

/-- Two bitstrings agree outside the set `S`.

This relation means that `z` and `w` may differ at positions inside `S`, but
must agree at every position outside `S`. It is the natural generalization of
`Qubits.SameOutside j z w`, which is the special case `S = {j}`.

Source: arXiv:1906.08948v2 §IV l.620–678 (light-cone support condition).
-/
def AgreeOutside {N : ℕ} (S : Finset (Fin N)) (z w : Qubits.BitString N) : Prop :=
  ∀ k : Fin N, k ∉ S → z k = w k

instance instDecidableAgreeOutside {N : ℕ} (S : Finset (Fin N))
    (z w : Qubits.BitString N) : Decidable (AgreeOutside S z w) := by
  classical
  unfold AgreeOutside
  infer_instance

/-- `AgreeOutside` is reflexive. -/
theorem AgreeOutside.refl {N : ℕ} (S : Finset (Fin N))
    (z : Qubits.BitString N) : AgreeOutside S z z := by
  intro _ _; rfl

/-- `AgreeOutside` is symmetric. -/
theorem AgreeOutside.symm {N : ℕ} {S : Finset (Fin N)}
    {z w : Qubits.BitString N} (h : AgreeOutside S z w) :
    AgreeOutside S w z := by
  intro k hk
  exact (h k hk).symm

/-- `AgreeOutside` is transitive. -/
theorem AgreeOutside.trans {N : ℕ} {S : Finset (Fin N)}
    {x y z : Qubits.BitString N}
    (hxy : AgreeOutside S x y) (hyz : AgreeOutside S y z) :
    AgreeOutside S x z := by
  intro k hk
  exact (hxy k hk).trans (hyz k hk)

/-- Enlarging the exception set keeps agreement: if `S ⊆ T` and the bitstrings
agree outside `S`, they also agree outside `T`. -/
theorem AgreeOutside.mono {N : ℕ} {S T : Finset (Fin N)} (hST : S ⊆ T)
    {z w : Qubits.BitString N} (h : AgreeOutside S z w) :
    AgreeOutside T z w := by
  intro k hk
  exact h k (fun hkS => hk (hST hkS))

/-- Agreement outside `S ∪ T` follows from chaining agreement outside `S` and
outside `T`. -/
theorem AgreeOutside.trans_union {N : ℕ} {S T : Finset (Fin N)}
    {x y z : Qubits.BitString N}
    (hxy : AgreeOutside S x y) (hyz : AgreeOutside T y z) :
    AgreeOutside (S ∪ T) x z := by
  intro k hk
  have hkS : k ∉ S := fun h => hk (Finset.mem_union.mpr (Or.inl h))
  have hkT : k ∉ T := fun h => hk (Finset.mem_union.mpr (Or.inr h))
  exact (hxy k hkS).trans (hyz k hkT)

/-- `AgreeOutside {j}` coincides with `Qubits.SameOutside j`. -/
theorem agreeOutside_singleton {N : ℕ} (j : Fin N)
    (z w : Qubits.BitString N) :
    AgreeOutside ({j} : Finset (Fin N)) z w ↔ Qubits.SameOutside j z w := by
  unfold AgreeOutside Qubits.SameOutside
  constructor
  · intro h k hk
    exact h k (by simp [hk])
  · intro h k hk
    have hk' : k ≠ j := by simpa using hk
    exact h k hk'

-- ============================================================================
-- Section: supportedOn — the support predicate on N-qubit operators
-- ============================================================================

/-!
This section defines the support predicate `supportedOn S O` and develops its
closure calculus under scalar multiplication, addition, multiplication, and
monotonicity in `S`. The formulation extends `Qubits.localOp_apply_of_not_sameOutside`
from singletons to arbitrary finite subsets.
-/

/-- An `N`-qubit operator `O` is **supported on** the finite set `S ⊆ Fin N` if
every matrix entry between two computational-basis indices whose bitstrings
disagree somewhere outside `S` vanishes.

Equivalently, `O` acts as the identity on every qubit outside `S` (each such
qubit is unchanged in transit). This is the matrix-entry generalization of
`Qubits.localOp_apply_of_not_sameOutside`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
def supportedOn {N : ℕ} (S : Finset (Fin N)) (O : Qubits.NQubitOp N) : Prop :=
  ∀ ix iy : Fin (Qubits.NQubitDim N),
    ¬ AgreeOutside S ((Qubits.bitStringEquiv N).symm ix)
        ((Qubits.bitStringEquiv N).symm iy) →
      O ix iy = 0

/-- The zero operator is supported on every subset. -/
theorem supportedOn_zero {N : ℕ} (S : Finset (Fin N)) :
    supportedOn S (0 : Qubits.NQubitOp N) := by
  intro ix iy _; rfl

/-- The identity operator is supported on the empty set: its matrix entries are
nonzero only on the diagonal, where the two bitstrings are equal and therefore
agree outside any set (including `∅`).

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_one {N : ℕ} :
    supportedOn (∅ : Finset (Fin N)) (1 : Qubits.NQubitOp N) := by
  intro ix iy hne
  by_contra hne0
  apply hne
  have hone : (1 : Qubits.NQubitOp N) ix iy = if ix = iy then 1 else 0 := by
    simp [Matrix.one_apply]
  by_cases h : ix = iy
  · subst h
    intro k _
    rfl
  · rw [hone, if_neg h] at hne0
    exact (hne0 rfl).elim

/-- Scalar multiplication preserves support: if `O` is supported on `S`, so is
`c • O`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_smul {N : ℕ} {S : Finset (Fin N)} {O : Qubits.NQubitOp N}
    (c : ℂ) (hO : supportedOn S O) :
    supportedOn S (c • O) := by
  intro ix iy hne
  have h := hO ix iy hne
  simp [Matrix.smul_apply, h]

/-- Sum preserves support, with support set the union: if `O` is supported on
`S` and `O'` is supported on `T`, then `O + O'` is supported on `S ∪ T`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_add {N : ℕ} {S T : Finset (Fin N)}
    {O O' : Qubits.NQubitOp N}
    (hO : supportedOn S O) (hO' : supportedOn T O') :
    supportedOn (S ∪ T) (O + O') := by
  intro ix iy hne
  have hneS : ¬ AgreeOutside S
      ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iy) := by
    intro h
    exact hne (AgreeOutside.mono (Finset.subset_union_left) h)
  have hneT : ¬ AgreeOutside T
      ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iy) := by
    intro h
    exact hne (AgreeOutside.mono (Finset.subset_union_right) h)
  have h₁ := hO ix iy hneS
  have h₂ := hO' ix iy hneT
  simp [Matrix.add_apply, h₁, h₂]

/-- Enlarging the support set keeps the support property.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_mono {N : ℕ} {S T : Finset (Fin N)} (hST : S ⊆ T)
    {O : Qubits.NQubitOp N} (hO : supportedOn S O) :
    supportedOn T O := by
  intro ix iy hne
  apply hO
  intro h
  exact hne (AgreeOutside.mono hST h)

/-- Product preserves support, with support set the union: if `O` is supported
on `S` and `O'` is supported on `T`, then `O * O'` is supported on `S ∪ T`.

The proof expands the matrix product `(O * O') ix iy = ∑_iz O ix iz * O' iz iy`
and uses contrapositive: if the sum is nonzero, some intermediate index `iz`
gives a nonzero contribution, forcing agreement outside `S` and outside `T`,
hence agreement outside `S ∪ T`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_mul {N : ℕ} {S T : Finset (Fin N)}
    {O O' : Qubits.NQubitOp N}
    (hO : supportedOn S O) (hO' : supportedOn T O') :
    supportedOn (S ∪ T) (O * O') := by
  classical
  intro ix iy hne
  by_contra hne0
  apply hne
  -- The product entry is nonzero, so some intermediate index contributes nonzero.
  have hmul : (O * O') ix iy = ∑ iz, O ix iz * O' iz iy := by
    simp [Matrix.mul_apply]
  rw [hmul] at hne0
  -- Pick an intermediate index with a nonzero contribution.
  obtain ⟨iz, _, hiz⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne0
  have hne_left : O ix iz ≠ 0 := fun h => hiz (by simp [h])
  have hne_right : O' iz iy ≠ 0 := fun h => hiz (by simp [h])
  -- Each side gives agreement outside its respective set.
  have hS : AgreeOutside S
      ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iz) := by
    by_contra hSne
    exact hne_left (hO ix iz hSne)
  have hT : AgreeOutside T
      ((Qubits.bitStringEquiv N).symm iz)
      ((Qubits.bitStringEquiv N).symm iy) := by
    by_contra hTne
    exact hne_right (hO' iz iy hTne)
  exact AgreeOutside.trans_union hS hT

/-- A scalar multiple of the identity (e.g. `c • 1`) is supported on `∅`.

This is the basic constant generator of the support calculus and is recovered
from `supportedOn_one` and `supportedOn_smul`.
-/
theorem supportedOn_smul_one {N : ℕ} (c : ℂ) :
    supportedOn (∅ : Finset (Fin N)) (c • (1 : Qubits.NQubitOp N)) :=
  supportedOn_smul c supportedOn_one

-- ============================================================================
-- Section: Generators — localOp / localPauli operators are supported on {j}
-- ============================================================================

/-!
These lemmas show that the basic single-qubit lifts are supported on the
singleton `{j}`. They are the atomic generators of the calculus above.
-/

/-- A local lift of any single-qubit operator `A` to qubit `j` is supported on
`{j}`. This is the generic singleton-support theorem; the Pauli specializations
follow immediately.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_localOp {N : ℕ} (A : Quantum.Operators.Op 2) (j : Fin N) :
    supportedOn ({j} : Finset (Fin N)) (Qubits.localOp A j) := by
  intro ix iy hne
  have hsing : ¬ Qubits.SameOutside j
      ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iy) := by
    intro hsame
    exact hne ((agreeOutside_singleton (N := N) j _ _).mpr hsame)
  exact Qubits.localOp_apply_of_not_sameOutside (A := A) (j := j) ix iy hsing

/-- The local Pauli `X` operator on qubit `j` is supported on `{j}`. -/
theorem supportedOn_localPauliX {N : ℕ} (j : Fin N) :
    supportedOn ({j} : Finset (Fin N)) (Qubits.localPauliX j) := by
  rw [Qubits.localPauliX_eq_localOp]
  exact supportedOn_localOp _ j

/-- The local Pauli `Y` operator on qubit `j` is supported on `{j}`. -/
theorem supportedOn_localPauliY {N : ℕ} (j : Fin N) :
    supportedOn ({j} : Finset (Fin N)) (Qubits.localPauliY j) := by
  rw [Qubits.localPauliY_eq_localOp]
  exact supportedOn_localOp _ j

/-- The local Pauli `Z` operator on qubit `j` is supported on `{j}`. -/
theorem supportedOn_localPauliZ {N : ℕ} (j : Fin N) :
    supportedOn ({j} : Finset (Fin N)) (Qubits.localPauliZ j) := by
  rw [Qubits.localPauliZ_eq_localOp]
  exact supportedOn_localOp _ j

/-- A pair interaction `Z_k Z_{(k+1) mod n}` is supported on
`{k, IsingModel.nextSite k}`. This is the support of a single bond of the
Ising chain Hamiltonian; it feeds the spreading analysis in `Spreading.lean`.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_chainPairInteraction {n : ℕ} (k : Fin n) :
    supportedOn (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (IsingModel.chainPairInteraction k) := by
  unfold IsingModel.chainPairInteraction
  exact supportedOn_mul (supportedOn_localPauliZ k)
    (supportedOn_localPauliZ (IsingModel.nextSite k))

-- ============================================================================
-- Section: Commutation of chain pair interactions
-- ============================================================================

/-!
This section proves that any two `IsingModel.chainPairInteraction k`,
`chainPairInteraction k'` commute, by leveraging the fact that both act
diagonally on every computational-basis ket
(via `IsingModel.chainPairInteraction_apply_computationalBasisKet`). This is the
commute hypothesis required by `Matrix.exp_sum_of_commute` for the cost-layer
exponential factorization.
-/

/-- Any two nearest-neighbour pair interactions on the periodic Ising chain
commute. Both operators are diagonal in the computational basis, so their
product equals their composition in either order on every basis ket, and
operators agreeing on a basis are equal.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem chainPairInteractions_commute {n : ℕ} (k k' : Fin n) :
    Commute (IsingModel.chainPairInteraction k) (IsingModel.chainPairInteraction k') := by
  -- `Commute a b` unfolds to `a * b = b * a`.
  change IsingModel.chainPairInteraction k * IsingModel.chainPairInteraction k' =
    IsingModel.chainPairInteraction k' * IsingModel.chainPairInteraction k
  refine Qubits.op_eq_of_on_computationalBasis ?_
  intro z
  have hk : IsingModel.chainPairInteraction k * Qubits.computationalBasisKet n z =
      (((IsingModel.classicalSpin z k *
          IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ)) •
        Qubits.computationalBasisKet n z :=
    IsingModel.chainPairInteraction_apply_computationalBasisKet (k := k) (z := z)
  have hk' : IsingModel.chainPairInteraction k' * Qubits.computationalBasisKet n z =
      (((IsingModel.classicalSpin z k' *
          IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ)) •
        Qubits.computationalBasisKet n z :=
    IsingModel.chainPairInteraction_apply_computationalBasisKet (k := k') (z := z)
  calc
    (IsingModel.chainPairInteraction k * IsingModel.chainPairInteraction k') *
          Qubits.computationalBasisKet n z
        = IsingModel.chainPairInteraction k *
            (IsingModel.chainPairInteraction k' * Qubits.computationalBasisKet n z) := by
          rw [op_mul_op_mul_ket]
    _ = IsingModel.chainPairInteraction k *
            ((((IsingModel.classicalSpin z k' *
                IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ)) •
              Qubits.computationalBasisKet n z) := by
          rw [hk']
    _ = ((((IsingModel.classicalSpin z k' *
              IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ))) •
            (IsingModel.chainPairInteraction k * Qubits.computationalBasisKet n z) := by
          rw [op_mul_smul_ket]
    _ = ((((IsingModel.classicalSpin z k' *
              IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ))) •
            ((((IsingModel.classicalSpin z k *
                IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ)) •
              Qubits.computationalBasisKet n z) := by
          rw [hk]
    _ = ((((IsingModel.classicalSpin z k' *
              IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ)) *
            (((IsingModel.classicalSpin z k *
                IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ))) •
              Qubits.computationalBasisKet n z := by
          rw [Ket.smul_smul]
    _ = ((((IsingModel.classicalSpin z k *
              IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ)) *
            (((IsingModel.classicalSpin z k' *
                IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ))) •
              Qubits.computationalBasisKet n z := by
          rw [mul_comm]
    _ = ((((IsingModel.classicalSpin z k *
              IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ))) •
            ((((IsingModel.classicalSpin z k' *
                IsingModel.classicalSpin z (IsingModel.nextSite k') : ℝ) : ℂ)) •
              Qubits.computationalBasisKet n z) := by
          rw [← Ket.smul_smul]
    _ = ((((IsingModel.classicalSpin z k *
              IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ))) •
            (IsingModel.chainPairInteraction k' * Qubits.computationalBasisKet n z) := by
          rw [hk']
    _ = IsingModel.chainPairInteraction k' *
            ((((IsingModel.classicalSpin z k *
                IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ) : ℂ)) •
              Qubits.computationalBasisKet n z) := by
          rw [op_mul_smul_ket]
    _ = IsingModel.chainPairInteraction k' *
            (IsingModel.chainPairInteraction k * Qubits.computationalBasisKet n z) := by
          rw [hk]
    _ = (IsingModel.chainPairInteraction k' * IsingModel.chainPairInteraction k) *
            Qubits.computationalBasisKet n z := by
          rw [op_mul_op_mul_ket]

-- ============================================================================
-- Section: Cost-layer exponential factorization
-- ============================================================================

/-!
This section is the cost-Hamiltonian analog of `QAOA.exp_standardMixerOp`. The
proof template is identical: invoke `Matrix.exp_sum_of_commute` on the family of
pair interactions, using the commute lemma above; then repackage the result as
a `noncommProd`.
-/

/-- The exponential of the sum of pair interactions `∑_k Z_k Z_{k+1}` factors
into the non-commutative product of single-bond exponentials. This is the
cost-Hamiltonian analog of `QAOA.exp_standardMixerOp` and uses
`Matrix.exp_sum_of_commute` (Mathlib `MatrixExponential.lean`).

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem exp_chainPairInteraction_sum (N : ℕ) (γ : ℝ) :
    NormedSpace.exp (((((-γ : ℝ) * Complex.I : ℂ))) •
        (∑ k : Fin N, IsingModel.chainPairInteraction k)) =
      (Finset.univ : Finset (Fin N)).noncommProd
        (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k))
        (fun i _ j _ _ =>
          (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp) := by
  simpa [Finset.smul_sum] using
    (Matrix.exp_sum_of_commute (s := (Finset.univ : Finset (Fin N)))
      (f := fun k => ((((-γ : ℝ) * Complex.I : ℂ)) •
        IsingModel.chainPairInteraction k))
      (h := by
        intro i _ j _ _
        exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _))

end

end QAOA.IsingChain.UpperBound.LightCone
