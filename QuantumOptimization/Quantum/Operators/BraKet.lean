import QuantumOptimization.Quantum.Operators.Types
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-!
# HMul Instances for Quantum Types

This module defines multiplication (HMul) instances for quantum types,
making `*` the primary notation for:
- Ket × Bra → Op (outer product)
- Bra × Ket → ℂ (inner product)
- Op × Ket → Ket (operator action)
- Bra × Op → Bra (bra action)
- ℂ × anything, anything × ℂ (scalar multiplication)

## Design Principles

1. **HMul is primary**: All quantum products use `*` notation
2. **Associativity**: `(a * b) * c = a * (b * c)` wherever types allow
3. **Scalar commutativity**: `c * A = A * c` for scalars c and any quantum object A
4. **Physics-style proofs**: simp should work with basic axioms

## Key Lemmas (to be added as needed)

- `Op.mul_assoc`: Operator multiplication is associative
- `scalar_mul_comm`: Scalars commute with everything
- `ketbra_mul_ketbra`: `|ψ⟩⟨φ| * |χ⟩⟨ξ| = ⟨φ|χ⟩ * |ψ⟩⟨ξ|`
-/

-- ============================================================================
-- Section 1: HMul Instances (Primary Definitions)
-- ============================================================================

/-- HMul: Ket × Bra → Op (outer product |ψ⟩⟨φ|) -/
instance instHMulKetBra {n : ℕ} : HMul (Ket n) (Bra n) (Op n) where
  hMul ψ φ := Matrix.of fun i j => ψ.vec i * φ.vec j

/-- HMul: Bra × Ket → ℂ (inner product ⟨φ|ψ⟩) -/
instance instHMulBraKet {n : ℕ} : HMul (Bra n) (Ket n) ℂ where
  hMul φ ψ := ∑ i, φ.vec i * ψ.vec i

/-- HMul: Op × Ket → Ket (operator action A|ψ⟩) -/
instance instHMulOpKet {n : ℕ} : HMul (Op n) (Ket n) (Ket n) where
  hMul A ψ := ⟨A.mulVec ψ.vec⟩

/-- HMul: Bra × Op → Bra (bra action ⟨φ|A) -/
instance instHMulBraOp {n : ℕ} : HMul (Bra n) (Op n) (Bra n) where
  hMul φ A := ⟨fun j => ∑ i, φ.vec i * A i j⟩

/-- HMul: UnitaryOp × Ket → Ket (unitary action on kets) -/
instance instHMulUnitaryOpKet {n : ℕ} : HMul (UnitaryOp n) (Ket n) (Ket n) where
  hMul U ψ := ⟨U.toOp.mulVec ψ.vec⟩

-- Note: UnitaryOp × NormKet → NormKet instance is defined after NormKet (Section 10)

-- ============================================================================
-- Section 2: Expansion Lemmas (for proofs that need to unfold *)
-- ============================================================================

/-- Expand ψ * φ (Ket × Bra) -/
@[simp] lemma ket_mul_bra_apply {n : ℕ} (ψ : Ket n) (φ : Bra n) (i j : Fin n) :
    (ψ * φ : Op n) i j = ψ.vec i * φ.vec j := rfl

/-- Expand φ * ψ (Bra × Ket) to sum form.
    Note: NOT @[simp] to allow algebraic simp lemmas (bra_mul_smul_ket, etc.)
    to simplify structure before unfolding to sums. -/
lemma bra_mul_ket_eq {n : ℕ} (φ : Bra n) (ψ : Ket n) :
    (φ * ψ : ℂ) = ∑ i, φ.vec i * ψ.vec i := rfl

/-- Expand A * ψ (Op × Ket) -/
@[simp] lemma op_mul_ket_vec {n : ℕ} (A : Op n) (ψ : Ket n) :
    (A * ψ : Ket n).vec = A.mulVec ψ.vec := rfl

/-- Expand φ * A (Bra × Op) -/
@[simp] lemma bra_mul_op_vec {n : ℕ} (φ : Bra n) (A : Op n) (j : Fin n) :
    (φ * A : Bra n).vec j = ∑ i, φ.vec i * A i j := rfl

-- ============================================================================
-- Section 3: Scalar Multiplication (uses SMul • notation)
-- ============================================================================

-- Note: We use SMul (•) for scalar multiplication to align with Mathlib conventions
-- This makes all standard simplification lemmas work automatically
-- Scalar multiplication remains commutative: c • X for all quantum objects X

-- Component-level SMul is handled by Mathlib's Pi.smul_apply and smul_eq_mul

-- ============================================================================
-- Section 4: Basic Algebraic Properties
-- ============================================================================

-- Note: Scalar commutativity is built into SMul (c • X is the standard form)

-- ============================================================================
-- Section 5: Associativity Laws
-- ============================================================================

/-- Op * (Ket * Bra) = (Op * Ket) * Bra -/
@[simp]
theorem op_mul_ketbra {n : ℕ} (A : Op n) (ψ : Ket n) (φ : Bra n) :
    A * (ψ * φ) = (A * ψ) * φ := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul]
  congr 1
  ext k
  ring

/-- (Ket * Bra) * Op = Ket * (Bra * Op) -/
@[simp]
theorem ketbra_mul_op {n : ℕ} (ψ : Ket n) (φ : Bra n) (A : Op n) :
    (ψ * φ) * A = ψ * (φ * A) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_op_vec]
  rw [Finset.mul_sum]
  congr 1
  ext k
  ring

/-- (Bra * Op) * Ket = Bra * (Op * Ket) -/
@[simp]
theorem braop_mul_ket {n : ℕ} (φ : Bra n) (A : Op n) (ψ : Ket n) :
    (φ * A) * ψ = φ * (A * ψ) := by
  simp only [bra_mul_ket_eq, bra_mul_op_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  -- LHS: ∑ j, (∑ i, φ.vec i * A i j) * ψ.vec j
  -- RHS: ∑ i, φ.vec i * (∑ j, A i j * ψ.vec j)
  conv_lhs =>
    arg 2; ext j
    rw [Finset.sum_mul]
  conv_rhs =>
    arg 2; ext i
    rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  ext i
  congr 1
  ext j
  ring

/-- (Op * Op) * Ket = Op * (Op * Ket) -/
@[simp]
theorem op_mul_op_mul_ket {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A * B) * ψ = A * (B * ψ) := by
  ext i
  simp [op_mul_ket_vec, Matrix.mulVec_mulVec]

-- ============================================================================
-- Section 6: Bra-Ketbra Multiplication
-- ============================================================================

/-- Bra * (Ket * Bra) = (Bra * Ket) * Bra
    Fundamental: ⟨φ|(|χ⟩⟨ξ|) = ⟨φ|χ⟩⟨ξ| -/
@[simp]
theorem bra_mul_ketbra {n : ℕ} (φ : Bra n) (χ : Ket n) (ξ : Bra n) :
    φ * (χ * ξ) = (φ * χ) • ξ := by
  ext j
  simp only [bra_mul_op_vec, ket_mul_bra_apply, bra_mul_ket_eq]
  trans (∑ x, (φ.vec x * χ.vec x) * ξ.vec j)
  · congr 1; funext k; ring
  rw [← Finset.sum_mul]
  rfl

-- ============================================================================
-- Section 7: Scalar Distribution
-- ============================================================================

/-- Helper: (c • ψ).vec = c • ψ.vec -/
@[simp]
lemma Ket.smul_vec {n : ℕ} (c : ℂ) (ψ : Ket n) : (c • ψ).vec = c • ψ.vec := rfl

/-- Helper: (c • φ).vec = c • φ.vec for Bra -/
@[simp]
lemma Bra.smul_vec {n : ℕ} (c : ℂ) (φ : Bra n) : (c • φ).vec = c • φ.vec := rfl

/-- (c • A) * ψ = c • (A * ψ) -/
@[simp]
theorem smul_op_mul_ket {n : ℕ} (c : ℂ) (A : Op n) (ψ : Ket n) :
    (c • A) * ψ = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]

/-- A * (c • ψ) = c • (A * ψ) -/
@[simp]
theorem op_mul_smul_ket {n : ℕ} (A : Op n) (c : ℂ) (ψ : Ket n) :
    A * (c • ψ) = c • (A * ψ) := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec,
             Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  ext j
  ring

/-- (c • ψ) * φ = c • (ψ * φ) -/
@[simp]
theorem smul_ket_mul_bra {n : ℕ} (c : ℂ) (ψ : Ket n) (φ : Bra n) :
    (c • ψ) * φ = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.smul_vec, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- ψ * (c • φ) = c • (ψ * φ) -/
@[simp]
theorem ket_mul_smul_bra {n : ℕ} (ψ : Ket n) (c : ℂ) (φ : Bra n) :
    ψ * (c • φ) = c • (ψ * φ) := by
  ext i j
  simp only [ket_mul_bra_apply, Matrix.smul_apply, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  ring

/-- (c • φ) * ψ = c • (φ * ψ) -/
@[simp]
theorem smul_bra_mul_ket {n : ℕ} (c : ℂ) (φ : Bra n) (ψ : Ket n) :
    (c • φ) * ψ = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Bra.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- φ * (c • ψ) = c • (φ * ψ) -/
@[simp]
theorem bra_mul_smul_ket {n : ℕ} (φ : Bra n) (c : ℂ) (ψ : Ket n) :
    φ * (c • ψ) = c • (φ * ψ) := by
  simp only [bra_mul_ket_eq, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  trans (∑ i, φ.vec i * (c * ψ.vec i))
  · rfl
  trans (∑ i, c * (φ.vec i * ψ.vec i))
  · congr 1; ext i; ring
  rw [← Finset.mul_sum]

/-- (⟨ψ| + ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ + ⟨φ|χ⟩ (left distributivity) -/
@[simp]
theorem bra_add_mul_ket {n : ℕ} (ψ φ : Bra n) (χ : Ket n) :
    (ψ + φ) * χ = ψ * χ + φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ + φ).vec i = ψ.vec i + φ.vec i from rfl, add_mul]
  rw [Finset.sum_add_distrib]

/-- ⟨ψ|(|φ⟩ + |χ⟩) = ⟨ψ|φ⟩ + ⟨ψ|χ⟩ (right distributivity) -/
@[simp]
theorem bra_mul_add_ket {n : ℕ} (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ + χ) = ψ * φ + ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ + χ).vec i = φ.vec i + χ.vec i from rfl, mul_add]
  rw [Finset.sum_add_distrib]

/-- (⟨ψ| - ⟨φ|)|χ⟩ = ⟨ψ|χ⟩ - ⟨φ|χ⟩ (left distributivity for subtraction) -/
@[simp]
theorem bra_sub_mul_ket {n : ℕ} (ψ φ : Bra n) (χ : Ket n) :
    (ψ - φ) * χ = ψ * χ - φ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (ψ - φ).vec i = ψ.vec i - φ.vec i from rfl, sub_mul]
  rw [Finset.sum_sub_distrib]

/-- ⟨ψ|(|φ⟩ - |χ⟩) = ⟨ψ|φ⟩ - ⟨ψ|χ⟩ (right distributivity for subtraction) -/
@[simp]
theorem bra_mul_sub_ket {n : ℕ} (ψ : Bra n) (φ χ : Ket n) :
    ψ * (φ - χ) = ψ * φ - ψ * χ := by
  simp only [bra_mul_ket_eq]
  conv_lhs => arg 2; ext i; rw [show (φ - χ).vec i = φ.vec i - χ.vec i from rfl, mul_sub]
  rw [Finset.sum_sub_distrib]

-- ============================================================================
-- Section 8: Scalar-Scalar Multiplication
-- ============================================================================

-- Note: (c₁ * c₂) • A = c₁ • (c₂ • A) follows from smul_smul in Mathlib

-- ============================================================================
-- Section 9: Ketbra-Ketbra Multiplication (Derived)
-- ============================================================================

/-- Physics: (|ψ⟩⟨φ|)(|χ⟩⟨ξ|) = ⟨φ|χ⟩ • |ψ⟩⟨ξ|

    Direct proof by matrix calculation.
-/
@[simp]
theorem ketbra_mul_ketbra {n : ℕ} (ψ χ : Ket n) (φ ξ : Bra n) :
    (ψ * φ) * (χ * ξ) = (φ * χ) • (ψ * ξ) := by
  ext i j
  simp only [Matrix.mul_apply, ket_mul_bra_apply, bra_mul_ket_eq, Matrix.smul_apply, smul_eq_mul]
  -- LHS: ∑ x, ψ.vec i * φ.vec x * (χ.vec x * ξ.vec j)
  -- RHS: (∑ k, φ.vec k * χ.vec k) * (ψ.vec i * ξ.vec j)
  trans (∑ x, (φ.vec x * χ.vec x) * (ψ.vec i * ξ.vec j))
  · congr 1; funext x; ring
  · rw [← Finset.sum_mul]

/-- Zero ket times any bra is zero matrix -/
@[simp]
lemma zero_ket_mul_bra {n : ℕ} (φ : Bra n) : (0 : Ket n) * φ = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Zero bra component -/
@[simp]
lemma Bra.zero_vec {n : ℕ} (j : Fin n) : (0 : Bra n).vec j = 0 := rfl

/-- Any ket times zero bra is zero matrix -/
@[simp]
lemma ket_mul_zero_bra {n : ℕ} (ψ : Ket n) : ψ * (0 : Bra n) = 0 := by
  ext i j; simp [ket_mul_bra_apply]

/-- Ket addition at component level -/
@[simp]
lemma Ket.add_vec {n : ℕ} (ψ φ : Ket n) (i : Fin n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra addition at component level -/
@[simp]
lemma Bra.add_vec {n : ℕ} (ψ φ : Bra n) (i : Fin n) : (ψ + φ).vec i = ψ.vec i + φ.vec i := rfl

/-- Bra subtraction at component level -/
@[simp]
lemma Bra.sub_vec {n : ℕ} (ψ φ : Bra n) (i : Fin n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Bra negation at component level -/
@[simp]
lemma Bra.neg_vec {n : ℕ} (φ : Bra n) (i : Fin n) : (-φ).vec i = -φ.vec i := rfl

/-- Ket subtraction at component level -/
@[simp]
lemma Ket.sub_vec {n : ℕ} (ψ φ : Ket n) (i : Fin n) : (ψ - φ).vec i = ψ.vec i - φ.vec i := rfl

/-- Ket negation at component level -/
@[simp]
lemma Ket.neg_vec {n : ℕ} (ψ : Ket n) (i : Fin n) : (-ψ).vec i = -ψ.vec i := rfl

/-- Ket minus zero: |ψ⟩ - 0 = |ψ⟩ -/
@[simp]
lemma Ket.sub_zero {n : ℕ} (ψ : Ket n) : ψ - 0 = ψ := by
  ext i; simp [Ket.sub_vec]

/-- Zero minus ket: 0 - |ψ⟩ = -|ψ⟩ -/
@[simp]
lemma Ket.zero_sub {n : ℕ} (ψ : Ket n) : 0 - ψ = -ψ := by
  ext i; simp [Ket.sub_vec, Ket.neg_vec]

/-- Negation as scalar: -|ψ⟩ = (-1) • |ψ⟩ -/
@[simp]
lemma Ket.neg_eq_smul {n : ℕ} (ψ : Ket n) : -ψ = (-1 : ℂ) • ψ := by
  ext i; simp [Ket.neg_vec]

/-- Subtraction as addition with negation: |ψ⟩ - |φ⟩ = |ψ⟩ + (-1) • |φ⟩ -/
@[simp]
lemma Ket.sub_eq_add_neg_smul {n : ℕ} (ψ φ : Ket n) : ψ - φ = ψ + (-1 : ℂ) • φ := by
  ext i
  simp only [Ket.sub_vec, Ket.add_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul, neg_one_mul]
  ring

/-- Physics: |ψ⟩⟨φ| acting on |χ⟩ gives ⟨φ|χ⟩·|ψ⟩ -/
@[simp]
theorem ketbra_mul_ket {n : ℕ} (ψ χ : Ket n) (φ : Bra n) :
    (ψ * φ) * χ = (φ * χ) • ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul,
             bra_mul_ket_eq, ket_mul_bra_apply, Matrix.mulVec, dotProduct]
  -- Goal: ∑ x, ψ.vec i * φ.vec x * χ.vec x = (∑ j, φ.vec j * χ.vec j) * ψ.vec i
  trans (ψ.vec i * ∑ x, φ.vec x * χ.vec x)
  · rw [Finset.mul_sum]; congr 1; funext x; ring
  · ring

/-- Physics: Addition of operators distributes over ket multiplication -/
@[simp]
theorem add_op_mul_ket {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A + B) * ψ = A * ψ + B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.add_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Physics: Subtraction of operators distributes over ket multiplication -/
@[simp]
theorem sub_op_mul_ket {n : ℕ} (A B : Op n) (ψ : Ket n) :
    (A - B) * ψ = A * ψ - B * ψ := by
  ext i
  simp only [op_mul_ket_vec, Ket.sub_vec, Matrix.sub_apply, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_sub_distrib]; congr 1; funext j; ring

/-- Finite sums of operators act on ket components termwise.

This is the coordinate-level linearity of operator action on kets. It is useful
whenever an operator is defined as a finite sum and one wants to compute its
action on a ket one coordinate at a time.
-/
theorem sum_op_mul_ket_vec {n : ℕ} {α : Type*} (s : Finset α)
    (A : α → Op n) (ψ : Ket n) (i : Fin n) :
    ((s.sum A) * ψ).vec i = s.sum (fun a => (A a * ψ : Ket n).vec i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | insert a s ha ih =>
      simp [ha, add_op_mul_ket, ih, Ket.add_vec]

/-- Physics: A(|ψ⟩ + |φ⟩) = A|ψ⟩ + A|φ⟩ (right linearity of operator action) -/
@[simp]
theorem Op_mul_add_ket {n : ℕ} (A : Op n) (ψ φ : Ket n) :
    A * (ψ + φ) = A * ψ + A * φ := by
  ext i
  simp only [op_mul_ket_vec, Ket.add_vec, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Expand U * ψ (UnitaryOp × Ket) -/
@[simp] lemma UnitaryOp_mul_ket_vec {n : ℕ} (U : UnitaryOp n) (ψ : Ket n) :
    (U * ψ : Ket n).vec = U.toOp.mulVec ψ.vec := rfl

/-- Physics: U(|ψ⟩ + |φ⟩) = U|ψ⟩ + U|φ⟩ (linearity of unitary action on kets) -/
@[simp]
theorem UnitaryOp_mul_add_ket {n : ℕ} (U : UnitaryOp n) (ψ φ : Ket n) :
    U * (ψ + φ) = U * ψ + U * φ := by
  ext i
  simp only [UnitaryOp_mul_ket_vec, Ket.add_vec, Matrix.mulVec, dotProduct]
  rw [← Finset.sum_add_distrib]; congr 1; funext j; ring

/-- Physics: U(c|ψ⟩) = c(U|ψ⟩) (scalar compatibility of unitary action) -/
@[simp]
theorem UnitaryOp_mul_smul_ket {n : ℕ} (U : UnitaryOp n) (c : ℂ) (ψ : Ket n) :
    U * (c • ψ) = c • (U * ψ) := by
  ext i
  simp only [UnitaryOp_mul_ket_vec, Ket.smul_vec, Matrix.mulVec, dotProduct,
             Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]; congr 1; funext j; ring

-- ============================================================================
-- Section 10: Dagger Operations
-- ============================================================================

/-- Dagger: |ψ⟩ ↦ ⟨ψ| -/
def Ket.dag {n : ℕ} (ψ : Ket n) : Bra n :=
  ⟨fun i => conj (ψ.vec i)⟩

/-- Dagger: ⟨ψ| ↦ |ψ⟩ -/
def Bra.dag {n : ℕ} (φ : Bra n) : Ket n :=
  ⟨fun i => conj (φ.vec i)⟩

/-- Physics: ⟨ψ|† = |ψ⟩ (dagger involution for bras) -/
@[simp]
theorem Bra.dag_dag {n : ℕ} (φ : Bra n) : φ.dag.dag = φ := by
  ext i
  simp only [Ket.dag, Bra.dag]
  exact star_star (φ.vec i)

/-- Physics: |ψ⟩† = ⟨ψ| (dagger involution for kets) -/
@[simp]
theorem Ket.dag_dag {n : ℕ} (ψ : Ket n) : ψ.dag.dag = ψ := by
  ext i
  simp only [Ket.dag, Bra.dag]
  exact star_star (ψ.vec i)

/-- Expand ψ.dag.vec -/
@[simp] lemma Ket.dag_vec {n : ℕ} (ψ : Ket n) (i : Fin n) :
    ψ.dag.vec i = conj (ψ.vec i) := rfl

/-- Expand φ.dag.vec -/
@[simp] lemma Bra.dag_vec {n : ℕ} (φ : Bra n) (i : Fin n) :
    φ.dag.vec i = conj (φ.vec i) := rfl

/-- Physics: (c|ψ⟩)† = c*⟨ψ| (conjugate-linearity of dagger) -/
@[simp]
theorem Ket.dag_smul {n : ℕ} (c : ℂ) (ψ : Ket n) : (c • ψ).dag = star c • ψ.dag := by
  ext i
  simp only [Ket.dag, Ket.smul_vec, Pi.smul_apply, Bra.smul_vec, starRingEnd_apply,
             smul_eq_mul, star_mul']

/-- Physics: (|ψ⟩ + |φ⟩)† = ⟨ψ| + ⟨φ| (linearity of dagger for addition) -/
@[simp]
theorem Ket.dag_add {n : ℕ} (ψ φ : Ket n) : (ψ + φ).dag = ψ.dag + φ.dag := by
  ext i
  simp only [Ket.dag, Ket.add_vec, map_add, Bra.add_vec]

/-- Physics: (|ψ⟩ - |φ⟩)† = ⟨ψ| - ⟨φ| (linearity of dagger for subtraction) -/
@[simp]
theorem Ket.dag_sub {n : ℕ} (ψ φ : Ket n) : (ψ - φ).dag = ψ.dag - φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.sub_vec, Bra.sub_vec, map_sub]

/-- Convert dag of subtraction to addition with negation: (|ψ⟩ - |φ⟩)† = ⟨ψ| + (-1) • ⟨φ| -/
@[simp]
theorem Ket.dag_sub_eq_add_neg_smul {n : ℕ} (ψ φ : Ket n) :
    (ψ - φ).dag = ψ.dag + (-1 : ℂ) • φ.dag := by
  ext i
  simp only [Ket.dag_vec, Ket.sub_vec, Bra.add_vec, Bra.smul_vec, Pi.smul_apply, smul_eq_mul,
             neg_one_mul, map_sub]
  ring

-- ============================================================================
-- Section 11: Inner Product and Normalization
-- ============================================================================

/-- Inner product of two kets ⟨φ|ψ⟩ (via HMul: φ.dag * ψ) -/
def Ket.inner {n : ℕ} (φ ψ : Ket n) : ℂ := φ.dag * ψ

/-- Physics: ⟨φ|ψ⟩ = conj(⟨ψ|φ⟩) (conjugate symmetry of inner product) -/
theorem Ket.inner_conj {n : ℕ} (φ ψ : Ket n) : Ket.inner φ ψ = star (Ket.inner ψ φ) := by
  unfold Ket.inner
  simp only [bra_mul_ket_eq, Ket.dag_vec]
  rw [star_sum]
  congr 1; ext i
  simp only [starRingEnd_apply, star_mul', star_star]
  ring

/-- Predicate: a ket is normalized, i.e., ⟨ψ|ψ⟩ = 1 -/
def Ket.IsNormalized {n : ℕ} (ψ : Ket n) : Prop := ψ.dag * ψ = 1

/-- Real-valued inner product: Re⟨φ|ψ⟩ (utility function) -/
def Ket.realInner {n : ℕ} (φ ψ : Ket n) : ℝ := (Ket.inner φ ψ).re

/-- Squared norm of a ket (utility function) -/
def Ket.normSq {n : ℕ} (ψ : Ket n) : ℝ := Ket.realInner ψ ψ

/-- A normalized ket (pure quantum state) -/
structure NormKet (n : ℕ) extends Ket n where
  normalized : toKet.IsNormalized

instance {n : ℕ} : Coe (NormKet n) (Ket n) where
  coe := NormKet.toKet

/-- HMul: UnitaryOp × NormKet → NormKet (unitary action preserves normalization)
    Physics: Unitary operators preserve the norm of quantum states: ‖U|ψ⟩‖ = ‖|ψ⟩‖ -/
instance instHMulUnitaryOpNormKet {n : ℕ} : HMul (UnitaryOp n) (NormKet n) (NormKet n) where
  hMul U ψ := ⟨⟨U.toOp.mulVec ψ.vec⟩, by
    -- Proof: ⟨Uψ|Uψ⟩ = ⟨ψ|U†U|ψ⟩ = ⟨ψ|ψ⟩ = 1
    unfold Ket.IsNormalized
    simp only [bra_mul_ket_eq, Ket.dag, starRingEnd_apply]
    -- Goal: ∑ i, star ((U.toOp *ᵥ ψ.vec) i) * (U.toOp *ᵥ ψ.vec) i = 1
    rw [show (∑ i, star ((U.toOp *ᵥ ψ.vec) i) * (U.toOp *ᵥ ψ.vec) i) =
             dotProduct (star (U.toOp *ᵥ ψ.vec)) (U.toOp *ᵥ ψ.vec) by
      unfold dotProduct; rfl]
    rw [U.preserves_inner]
    rw [show dotProduct (star ψ.vec) ψ.vec =
             ∑ i, star (ψ.vec i) * ψ.vec i by
      unfold dotProduct; rfl]
    exact ψ.normalized⟩

/-- Connection: (U * ψ).toKet = U * ψ.toKet for UnitaryOp acting on NormKet -/
@[simp]
theorem UnitaryOp_mul_NormKet_toKet {n : ℕ} (U : UnitaryOp n) (ψ : NormKet n) :
    (U * ψ).toKet = U * ψ.toKet := rfl

-- ============================================================================
-- Section 12: Standard Basis Kets
-- ============================================================================

/-- Standard basis ket |i⟩ in n-dimensional space -/
def stdKet (n : ℕ) (i : Fin n) : Ket n :=
  ⟨fun j => if i = j then 1 else 0⟩

/-- Standard basis ket component -/
@[simp] theorem stdKet_apply {n : ℕ} (i j : Fin n) :
    (stdKet n i).vec j = if i = j then 1 else 0 := rfl

/-- Standard basis inner product: ⟨i|j⟩ = δᵢⱼ -/
@[simp] theorem stdKet_braket (n : ℕ) (i j : Fin n) :
    (stdKet n i).dag * (stdKet n j) = if i = j then 1 else 0 := by
  simp only [bra_mul_ket_eq, Ket.dag_vec, stdKet_apply]
  by_cases h : i = j
  · subst h
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd (Finset.mem_univ i) h
  · simp only [h, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    by_cases hi : i = k
    · subst hi; simp [Ne.symm h]
    · simp [hi]

-- ============================================================================
-- Specialized braket lemmas (direct evaluation without `if`)
-- ============================================================================

/-- ⟨i|i⟩ = 1 for any basis state -/
@[simp] theorem stdKet_braket_self {n : ℕ} (i : Fin n) :
    (stdKet n i).dag * (stdKet n i) = 1 := by simp only [stdKet_braket, ↓reduceIte]

/-- ⟨0|0⟩ = 1 using Fin coercion -/
@[simp] theorem stdKet_braket_0_0 {n : ℕ} [NeZero n] :
    (stdKet n (0 : Fin n)).dag * (stdKet n (0 : Fin n)) = 1 := stdKet_braket_self 0

/-- ⟨1|1⟩ = 1 using Fin coercion -/
@[simp] theorem stdKet_braket_1_1 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (1 : Fin n)).dag * (stdKet n (1 : Fin n)) = 1 := stdKet_braket_self 1

/-- ⟨0|1⟩ = 0 using Fin coercion -/
@[simp] theorem stdKet_braket_0_1 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (0 : Fin n)).dag * (stdKet n (1 : Fin n)) = 0 := by
  simp only [stdKet_braket]
  have h : (0 : Fin n) ≠ 1 := Fin.ne_of_val_ne (by simp; have := Fact.out (p := 1 < n); omega)
  simp [h]

/-- ⟨1|0⟩ = 0 using Fin coercion -/
@[simp] theorem stdKet_braket_1_0 {n : ℕ} [Fact (1 < n)] :
    (stdKet n (1 : Fin n)).dag * (stdKet n (0 : Fin n)) = 0 := by
  simp only [stdKet_braket]
  have h : (1 : Fin n) ≠ 0 := Fin.ne_of_val_ne (by simp; have := Fact.out (p := 1 < n); omega)
  simp [h]

/-- Standard basis kets are normalized: ⟨i|i⟩ = 1 -/
@[simp] theorem stdKet_IsNormalized {n : ℕ} (i : Fin n) :
    (stdKet n i).IsNormalized := stdKet_braket_self i

/-- Standard basis kets have norm squared 1 (utility lemma) -/
@[simp] theorem stdKet_normSq {n : ℕ} (i : Fin n) :
    (stdKet n i).normSq = 1 := by
  unfold Ket.normSq Ket.realInner Ket.inner
  simp only [stdKet_braket_self, Complex.one_re]

/-- Standard normalized ket: |i⟩ as a NormKet -/
def stdNormKet (n : ℕ) (i : Fin n) : NormKet n :=
  ⟨stdKet n i, stdKet_IsNormalized i⟩

/-- Connection: stdNormKet as Ket equals stdKet -/
@[simp]
theorem stdNormKet_toKet (n : ℕ) (i : Fin n) :
    (stdNormKet n i).toKet = stdKet n i := rfl

-- ============================================================================
-- Section 13: Type Classes for Flexible Bra-Ket Notation
-- ============================================================================

/-- Type class for things that can be converted to a Bra.
    - Ket n → Bra n via .dag
    - Bra n → Bra n via identity -/
class ToBra (α : Type*) (n : outParam ℕ) where
  toBra : α → Bra n

/-- Type class for things that can be converted to a Ket.
    - Ket n → Ket n via identity
    - Bra n → Ket n via .dag -/
class ToKet (α : Type*) (n : outParam ℕ) where
  toKet : α → Ket n

-- Instances for Ket
instance instToKetKet {n : ℕ} : ToKet (Ket n) n where
  toKet := id

instance instToBraKet {n : ℕ} : ToBra (Ket n) n where
  toBra := Ket.dag

-- Instances for Bra
instance instToBraBra {n : ℕ} : ToBra (Bra n) n where
  toBra := id

instance instToKetBra {n : ℕ} : ToKet (Bra n) n where
  toKet := Bra.dag

-- Simp lemmas to reduce type class applications
@[simp] theorem ToKet.toKet_ket {n : ℕ} (ψ : Ket n) : ToKet.toKet ψ = ψ := rfl
@[simp] theorem ToBra.toBra_bra {n : ℕ} (β : Bra n) : ToBra.toBra β = β := rfl
@[simp] theorem ToKet.toKet_bra {n : ℕ} (β : Bra n) : ToKet.toKet β = β.dag := rfl
@[simp] theorem ToBra.toBra_ket {n : ℕ} (ψ : Ket n) : ToBra.toBra ψ = ψ.dag := rfl

/-- Type class for things that can be converted to a NormKet.
    Used by the ‖x, y, ...⟩ tensor product notation. -/
class ToNormKet (α : Type*) (n : outParam ℕ) where
  toNormKet : α → NormKet n

-- Instance for NormKet (identity)
instance instToNormKetNormKet {n : ℕ} : ToNormKet (NormKet n) n where
  toNormKet := id

@[simp]
theorem ToNormKet.toNormKet_normket {n : ℕ} (ψ : NormKet n) : ToNormKet.toNormKet ψ = ψ := rfl

-- ============================================================================
-- Section 14: Standard Basis Notation
-- ============================================================================

-- Qubit notation (specific, higher priority)
notation "|0⟩" => stdKet 2 0
notation "|1⟩" => stdKet 2 1

set_option quotPrecheck false in
notation "⟨0|" => Ket.dag (stdKet 2 0)

set_option quotPrecheck false in
notation "⟨1|" => Ket.dag (stdKet 2 1)

-- General notation: |i:n⟩ creates stdKet n i
notation "|" i ":" n "⟩" => stdKet n i

-- General bra notation: ⟨x| converts x to Bra (dags Kets, keeps Bras)
set_option quotPrecheck false in
notation "⟨" x "|" => ToBra.toBra x

-- General ket notation: |x⟩ converts x to Ket (keeps Kets, dags Bras)
notation "|" x "⟩" => ToKet.toKet x

-- NormKet notation: ‖i:n⟩ creates stdNormKet n i
notation "‖" i ":" n "⟩" => stdNormKet n i

-- Qubit shorthand for NormKets (dimension 2)
notation "‖0⟩" => stdNormKet 2 0
notation "‖1⟩" => stdNormKet 2 1

-- ============================================================================
-- Section 15: Completeness and Outer Product Lemmas
-- ============================================================================

/-- Completeness relation for qubits: |0⟩⟨0| + |1⟩⟨1| = 1 -/
theorem completeness_2 :
    stdKet 2 0 * (stdKet 2 0).dag + stdKet 2 1 * (stdKet 2 1).dag = (1 : Op 2) := by
  ext i j
  simp only [Matrix.add_apply, ket_mul_bra_apply, stdKet_apply, Ket.dag_vec]
  fin_cases i <;> fin_cases j <;> simp

/-- Outer product |i⟩⟨j| applied at indices -/
@[simp] lemma ketbra_std_apply (i j k l : Fin 2) :
    (stdKet 2 i * (stdKet 2 j).dag : Op 2) k l =
    if i = k then (if j = l then 1 else 0) else 0 := by
  simp only [ket_mul_bra_apply, stdKet_apply, Ket.dag_vec]
  by_cases hi : i = k <;> by_cases hj : j = l <;> simp [hi, hj]

/-- Conjugate transpose of outer product: (|ψ⟩⟨φ|)† = |φ.dag.dag⟩⟨ψ.dag| -/
@[simp]
theorem ket_mul_bra_conjTranspose {n : ℕ} (ψ : Ket n) (φ : Bra n) :
    (ψ * φ)† = φ.dag * ψ.dag := by
  ext i j
  simp only [Matrix.conjTranspose_apply, ket_mul_bra_apply, Bra.dag_vec, Ket.dag_vec, star]
  change (starRingEnd ℂ) (ψ.vec j * φ.vec i) = (starRingEnd ℂ) (φ.vec i) * (starRingEnd ℂ) (ψ.vec j)
  rw [RingHom.map_mul, mul_comm]

/-- Dagger of standard ket: (stdKet n i).dag.dag = stdKet n i -/
@[simp] lemma stdKet_dag_dag (n : ℕ) (i : Fin n) : (stdKet n i).dag.dag = stdKet n i := by
  ext j
  simp only [Bra.dag_vec, Ket.dag_vec, stdKet_apply]
  by_cases h : i = j <;> simp [h]

-- ============================================================================
-- Section 15: Operator Dagger Lemmas
-- ============================================================================

/-- Dagger distributes over operator addition -/
@[simp]
theorem Op.dag_add {n : ℕ} (A B : Op n) : (A + B)† = A† + B† :=
  Matrix.conjTranspose_add A B

/-- Dagger distributes over operator subtraction -/
@[simp]
theorem Op.dag_sub {n : ℕ} (A B : Op n) : (A - B)† = A† - B† :=
  Matrix.conjTranspose_sub A B

/-- Dagger of scalar times operator -/
@[simp]
theorem Op.dag_smul {n : ℕ} (c : ℂ) (A : Op n) : (c • A)† = star c • A† :=
  Matrix.conjTranspose_smul c A

-- ============================================================================
-- Quantum Information Tactic
-- ============================================================================

/-- Basic simplification tactic for quantum information proofs.
    Expands products, applies completeness relations, and simplifies complex arithmetic.
    Uses SMul (•) notation for all scalar multiplication.
    Note: Use `qisimp` from QuantumInformationHMul.lean for tensor product support. -/
macro "qisimp_basic" : tactic =>
  `(tactic| (
    simp (config := { decide := true }) [
      -- Scalar multiplication
      Op.dag_smul, smul_mul_assoc, mul_smul_comm, smul_smul, smul_sub, smul_add,
      -- Conjugate transpose
      Op.dag_sub, Op.dag_add, ket_mul_bra_conjTranspose, stdKet_dag_dag,
      -- Products
      sub_mul, mul_sub, add_mul, mul_add, ketbra_mul_ketbra, ketbra_mul_ket,
      add_op_mul_ket, sub_op_mul_ket, smul_op_mul_ket,
      -- Inner products (brakets)
      stdKet_braket, bra_mul_smul_ket, bra_mul_add_ket,
      -- Complex arithmetic
      Complex.star_def, Complex.conj_I, Complex.I_mul_I, mul_neg, neg_mul,
      neg_neg, neg_one_smul, one_smul, neg_smul,
      -- Zero/one simplification
      zero_mul, mul_zero, zero_smul, smul_zero, zero_add, add_zero, zero_sub, sub_zero,
      mul_one, one_mul, zero_ket_mul_bra, ket_mul_zero_bra,
      -- Ket arithmetic
      Ket.add_vec, Ket.sub_vec, Ket.smul_vec, Ket.neg_vec,
      Ket.sub_zero, Ket.zero_sub,
      -- Negation and subtraction
      sub_neg_eq_add, neg_add, add_neg_cancel_right, add_neg_cancel_left,
      -- Completeness (dimension 2 for qubits)
      completeness_2
    ]
  ))

-- ============================================================================
-- Section 16: Inner Product and Hermitian Operator Properties
-- ============================================================================

/-- Inner product of two vectors: ⟨v|w⟩ = Σᵢ v̄ᵢ wᵢ -/
def innerProduct {n : ℕ} (v w : Fin n → ℂ) : ℂ :=
  ∑ i, star (v i) * w i

/-!
## Projector Properties

Properties of projectors formed from outer products |ψ⟩⟨ψ|.
-/

/-- Left distributivity of outer product: (ψ + φ) * χ = ψ * χ + φ * χ -/
@[simp]
lemma ket_add_mul_bra {n : ℕ} (ψ φ : Ket n) (χ : Bra n) :
    (ψ + φ) * χ = ψ * χ + φ * χ := by
  ext i j
  simp only [ket_mul_bra_apply, Ket.add_vec, Matrix.add_apply]
  ring

/-- Right distributivity of outer product: ψ * (φ + χ) = ψ * φ + ψ * χ -/
@[simp]
lemma ket_mul_add_bra {n : ℕ} (ψ : Ket n) (φ χ : Bra n) :
    ψ * (φ + χ) = ψ * φ + ψ * χ := by
  ext i j
  simp only [ket_mul_bra_apply, Bra.add_vec, Matrix.add_apply]
  ring

end  -- noncomputable section

end Quantum.Operators
