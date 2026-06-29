import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Matrix.PosDef

namespace Quantum.Operators

open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-!
# Quantum Operator Types — Op, HermitianOp, PosSemidefOp, DensityOp, UnitaryOp, Ket, Bra

Core type hierarchy for quantum mechanics on finite-dimensional Hilbert spaces.
Operators are represented as complex matrices `Matrix (Fin n) (Fin n) ℂ`, with
successive refinements encoding Hermiticity, positive semidefiniteness, and unit trace.
Normalized kets/bras and inner-product operations are in `Quantum.Operators.BraKet`.

## Main definitions
- `Op n`: alias for `Matrix (Fin n) (Fin n) ℂ`, the space of linear operators
- `HermitianOp n`: Hermitian operator (`A† = A`), with `AddCommGroup`
  and `Module ℝ` instances
- `PosSemidefOp n`: positive semidefinite operator, with `AddCommMonoid`
  and `Module NNReal` instances
- `DensityOp n`: density operator (PSD with `Tr = 1`), with convex combinations and purity
- `UnitaryOp n`: unitary operator (`U†U = UU† = I`), with group-like operations
- `Ket n` / `Bra n`: ket and bra vectors with basic algebraic instances

## Main statements
- `posSemidefOp_implies_mathlib`: connects `PosSemidefOp` to Mathlib's `Matrix.PosSemidef`
- `DensityOp.purity_bounds`: `1/n ≤ Tr(ρ²) ≤ 1` for density operators
- `pos_semidef_off_diag_bound`: `|Aᵢⱼ|² ≤ Aᵢᵢ · Aⱼⱼ` for PSD matrices
- `UnitaryOp.preserves_inner`: unitary operators preserve inner products
-/

-- ============================================================================
-- Section 1: Basic Operator Type
-- ============================================================================

/-- The space of linear operators on an n-dimensional Hilbert space -/
abbrev Op (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Dagger notation for conjugate transpose of operators -/
postfix:max "†" => Matrix.conjTranspose

-- ============================================================================
-- Section 2: Hermitian Operators (Observables)
-- ============================================================================

/-- A Hermitian operator satisfies A† = A -/
structure HermitianOp (n : ℕ) where
  toOp : Op n
  isHermitian : toOp.IsHermitian

@[ext]
theorem HermitianOp.ext {n : ℕ} {A B : HermitianOp n} (h : A.toOp = B.toOp) : A = B := by
  cases A; cases B; congr

instance {n : ℕ} : Coe (HermitianOp n) (Op n) where
  coe := HermitianOp.toOp

/-- Hermitian operators form a real vector space -/
instance {n : ℕ} : Zero (HermitianOp n) where
  zero := ⟨0, by simp [IsHermitian]⟩

instance {n : ℕ} : Add (HermitianOp n) where
  add A B := ⟨A.toOp + B.toOp, by
    unfold IsHermitian
    rw [conjTranspose_add, A.isHermitian, B.isHermitian]⟩

instance {n : ℕ} : Neg (HermitianOp n) where
  neg A := ⟨-A.toOp, by
  unfold IsHermitian
  rw [conjTranspose_neg, A.isHermitian]
  ⟩

instance {n : ℕ} : Sub (HermitianOp n) where
  sub A B := ⟨A.toOp - B.toOp, by
  unfold IsHermitian
  rw [conjTranspose_sub,A.isHermitian,B.isHermitian]
  ⟩

instance {n : ℕ} : SMul ℝ (HermitianOp n) where
  smul r A := ⟨(r : ℂ) • A.toOp, by
  unfold IsHermitian
  rw [conjTranspose_smul,A.isHermitian]
  simp
  ⟩

instance {n : ℕ} : AddCommGroup (HermitianOp n) where
  add_assoc := by intros; ext; apply add_assoc
  zero_add := by intros; ext; apply zero_add
  add_zero := by intros; ext; apply add_zero
  neg_add_cancel := by intros; ext; apply neg_add_cancel
  add_comm := by intros; ext; apply add_comm
  nsmul := nsmulRec
  zsmul := zsmulRec

instance {n : ℕ} : Module ℝ (HermitianOp n) where
  one_smul := by
    intros b; ext i j
    change (1 : ℂ) • b.toOp i j = b.toOp i j
    exact @one_smul ℂ ℂ _ _ (b.toOp i j)
  mul_smul := by
    intros x y b; ext i j
    change ((x * y : ℝ) : ℂ) • b.toOp i j = ((x : ℝ) : ℂ) • ((y : ℝ) : ℂ) • b.toOp i j
    rw [← SemigroupAction.mul_smul]
    congr 1
    exact Complex.ofReal_mul x y
  smul_zero := by
    intros a; ext i j
    change ((a : ℝ) : ℂ) • (0 : ℂ) = 0
    exact smul_zero ((a : ℝ) : ℂ)
  smul_add := by
    intros a b c; ext i j
    change ((a : ℝ) : ℂ) • (b.toOp i j + c.toOp i j) =
      ((a : ℝ) : ℂ) • b.toOp i j + ((a : ℝ) : ℂ) • c.toOp i j
    exact smul_add ((a : ℝ) : ℂ) (b.toOp i j) (c.toOp i j)
  add_smul := by
    intros r s x; ext i j
    change (((r + s) : ℝ) : ℂ) • x.toOp i j =
      ((r : ℝ) : ℂ) • x.toOp i j + ((s : ℝ) : ℂ) • x.toOp i j
    rw [Complex.ofReal_add, add_smul]
  zero_smul := by
    intros x; ext i j
    change ((0 : ℝ) : ℂ) • x.toOp i j = 0
    exact zero_smul ℂ (x.toOp i j)

-- ============================================================================
-- Section 3: Positive Semidefinite Operators
-- ============================================================================

/-- Quadratic form ⟨x|A|x⟩ -/
def quadraticForm {n : ℕ} (A : Op n) (x : Fin n → ℂ) : ℂ :=
  dotProduct (star x) (A.mulVec x)

/-- A positive semidefinite operator is Hermitian with non-negative quadratic form -/
structure PosSemidefOp (n : ℕ) extends HermitianOp n where
  pos_semidef : ∀ x : Fin n → ℂ, 0 ≤ (quadraticForm toOp x).re

@[ext]
theorem PosSemidefOp.ext {n : ℕ} {A B : PosSemidefOp n} (h : A.toOp = B.toOp) : A = B := by
  cases A; cases B
  simp only [mk.injEq]
  exact HermitianOp.ext h

instance {n : ℕ} : Coe (PosSemidefOp n) (HermitianOp n) where
  coe := PosSemidefOp.toHermitianOp

instance {n : ℕ} : Coe (PosSemidefOp n) (Op n) where
  coe A := A.toOp

/-- Positive semidefinite operators form a convex cone -/
instance {n : ℕ} : Zero (PosSemidefOp n) where
  zero := ⟨0, by
    intro x
    change 0 ≤ (quadraticForm (0 : Op n) x).re
    unfold quadraticForm
    simp [zero_mulVec, dotProduct_zero]⟩

instance {n : ℕ} : Add (PosSemidefOp n) where
  add A B := ⟨A.toHermitianOp + B.toHermitianOp, by
    intro x
    change 0 ≤ (quadraticForm (A.toHermitianOp.toOp + B.toHermitianOp.toOp) x).re
    unfold quadraticForm
    rw [add_mulVec, dotProduct_add, Complex.add_re]
    apply add_nonneg
    · exact A.pos_semidef x
    · exact B.pos_semidef x⟩

instance {n : ℕ} : SMul NNReal (PosSemidefOp n) where
  smul r A := ⟨(r : ℝ) • A.toHermitianOp, by
    intro x
    change 0 ≤ (quadraticForm ((r : ℝ) • A.toHermitianOp.toOp) x).re
    unfold quadraticForm
    rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
    rw [smul_eq_mul]
    apply mul_nonneg
    · exact NNReal.coe_nonneg r
    · exact A.pos_semidef x⟩

instance {n : ℕ} : AddCommMonoid (PosSemidefOp n) where
  add_assoc := by
    intros a b c
    ext i j
    apply add_assoc
  zero_add := by
    intros a
    ext i j
    apply zero_add
  add_zero := by intros; ext; apply add_zero
  add_comm := by intros; ext; apply add_comm
  nsmul := nsmulRec

instance {n : ℕ} : Module NNReal (PosSemidefOp n) where
  one_smul := by
    intros x
    ext i j
    -- After ext, goal is: (1 • x).toOp i j = x.toOp i j
    -- Scalar multiplication converts NNReal → ℝ then applies to HermitianOp
    change ((1 : ℝ) • x.toHermitianOp).toOp i j = x.toOp i j
    rw [one_smul]
  mul_smul := by
    intros x y b; ext i j
    change (((x * y : NNReal) : ℝ) : ℂ) • b.toHermitianOp.toOp i j =
      ((x : ℝ) : ℂ) • ((y : ℝ) : ℂ) • b.toHermitianOp.toOp i j
    rw [← SemigroupAction.mul_smul]
    congr 1
    simp only [NNReal.coe_mul]
    exact Complex.ofReal_mul (x : ℝ) (y : ℝ)
  smul_zero := by
    intros a; ext i j
    change ((a : ℝ) : ℂ) • (0 : ℂ) = 0
    exact smul_zero ((a : ℝ) : ℂ)
  smul_add := by
    intros a b c; ext i j
    change ((a : ℝ) : ℂ) • (b.toHermitianOp.toOp i j + c.toHermitianOp.toOp i j) =
      ((a : ℝ) : ℂ) • b.toHermitianOp.toOp i j + ((a : ℝ) : ℂ) • c.toHermitianOp.toOp i j
    exact smul_add ((a : ℝ) : ℂ) (b.toHermitianOp.toOp i j) (c.toHermitianOp.toOp i j)
  add_smul := by
    intros r s x; ext i j
    change (((r + s : NNReal) : ℝ) : ℂ) • x.toHermitianOp.toOp i j =
      ((r : ℝ) : ℂ) • x.toHermitianOp.toOp i j + ((s : ℝ) : ℂ) • x.toHermitianOp.toOp i j
    rw [show ((r + s : NNReal) : ℝ) = (r : ℝ) + (s : ℝ) from NNReal.coe_add r s]
    rw [Complex.ofReal_add, add_smul]
  zero_smul := by
    intros x; ext i j
    change ((0 : ℝ) : ℂ) • x.toHermitianOp.toOp i j = 0
    exact zero_smul ℂ (x.toHermitianOp.toOp i j)

-- Note: For eigenvalues of PSD operators being non-negative, use:
--   (posSemidefOp_implies_mathlib A).eigenvalues_nonneg i

-- ============================================================================
-- Section 4: Density Operators (Quantum States)
-- ============================================================================

/-- A density operator is positive semidefinite with trace 1 -/
structure DensityOp (n : ℕ) extends PosSemidefOp n where
  trace_one : toOp.trace = 1

instance {n : ℕ} : Coe (DensityOp n) (PosSemidefOp n) where
  coe := DensityOp.toPosSemidefOp

instance {n : ℕ} : Coe (DensityOp n) (HermitianOp n) where
  coe ρ := ρ.toHermitianOp

instance {n : ℕ} : Coe (DensityOp n) (Op n) where
  coe ρ := ρ.toOp

/-- DensityOp extensionality -/
@[ext]
theorem DensityOp.ext {n : ℕ} {ρ σ : DensityOp n} (h : ρ.toOp = σ.toOp) : ρ = σ := by
  cases ρ; cases σ
  simp only [DensityOp.mk.injEq]
  apply PosSemidefOp.ext
  exact h

/-- A density operator is pure iff ρ² = ρ -/
def DensityOp.IsPure {n : ℕ} (ρ : DensityOp n) : Prop :=
  ρ.toOp * ρ.toOp = ρ.toOp

-- ============================================================================
-- Dimension Casting
-- ============================================================================

/-- Cast an operator between equal dimensions -/
def Op.castDim {n m : ℕ} (h : n = m) (A : Op n) : Op m :=
  h ▸ A

/-- Cast a density operator between equal dimensions -/
def DensityOp.castDim {n m : ℕ} (h : n = m) (ρ : DensityOp n) : DensityOp m :=
  h ▸ ρ

-- ============================================================================
-- Purity Helper Lemmas
-- ============================================================================

-- ============================================================================
-- Connecting to Mathlib's PosSemidef for off-diagonal bound
-- ============================================================================

/-- Quadratic form of Hermitian matrix is real (equals its own conjugate) -/
lemma quadraticForm_hermitian_conj_eq_self {n : ℕ} (A : Op n) (hA : A.IsHermitian)
    (x : Fin n → ℂ) : conj (quadraticForm A x) = quadraticForm A x := by
  unfold quadraticForm
  simp only [dotProduct, mulVec, Pi.star_apply]
  have herm : ∀ i j, conj (A i j) = A j i := fun i j => by
    have := congr_fun₂ hA j i
    simp only [conjTranspose_apply, star] at this
    exact this
  have star_eq_conj : ∀ (z : ℂ), star z = conj z := fun _ => rfl
  simp only [map_sum, map_mul, star_eq_conj, Complex.conj_conj, herm]
  conv_lhs => arg 2; ext i; rw [Finset.mul_sum]
  conv_rhs => arg 2; ext i; rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1; ext j; congr 1; ext i
  ring

/-- Connect our PosSemidefOp to Mathlib's Matrix.PosSemidef -/
lemma posSemidefOp_implies_mathlib {n : ℕ} (A : PosSemidefOp n) :
    Matrix.PosSemidef A.toOp := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨A.toHermitianOp.isHermitian, fun x => ?_⟩
  have h := A.pos_semidef x
  have hA := A.toHermitianOp.isHermitian
  have heq : star x ⬝ᵥ (A.toOp *ᵥ x) = quadraticForm A.toOp x := rfl
  have h_real := quadraticForm_hermitian_conj_eq_self A.toOp hA x
  have h_im : (quadraticForm A.toOp x).im = 0 := by
    rw [Complex.ext_iff] at h_real
    simp only [Complex.conj_re, Complex.conj_im] at h_real
    linarith [h_real.2]
  rw [heq, Complex.nonneg_iff]
  exact ⟨h, h_im.symm⟩

/-- Helper for 2-element index function -/
private def twoElems (i j : α) : Fin 2 → α := ![i, j]

/-- The 2×2 submatrix indexed by {i, j} -/
private def submatrix_2x2 {n : ℕ} (A : Op n) (i j : Fin n) : Matrix (Fin 2) (Fin 2) ℂ :=
  A.submatrix (twoElems i j) (twoElems i j)

/-- The 2×2 submatrix of a PSD matrix is PSD -/
private lemma submatrix_2x2_posSemidef {n : ℕ} (A : PosSemidefOp n) (i j : Fin n) :
    Matrix.PosSemidef (submatrix_2x2 A.toOp i j) :=
  (posSemidefOp_implies_mathlib A).submatrix (twoElems i j)

-- ============================================================================
-- Purity Definition and Bounds
-- ============================================================================

-- ============================================================================
-- Section 5: Unitary Operators (Quantum Gates)
-- ============================================================================

/-- A unitary operator satisfies U†U = UU† = I -/
structure UnitaryOp (n : ℕ) where
  toOp : Op n
  unitary_left : toOp.conjTranspose * toOp = 1
  unitary_right : toOp * toOp.conjTranspose = 1

instance {n : ℕ} : Coe (UnitaryOp n) (Op n) where
  coe := UnitaryOp.toOp

/-- Product of unitaries is unitary -/
def UnitaryOp.mul {n : ℕ} (U V : UnitaryOp n) : UnitaryOp n :=
  ⟨U.toOp * V.toOp, by
    -- Need: (U * V)† * (U * V) = 1
    rw [conjTranspose_mul]
    -- Goal: V† * U† * (U * V) = 1
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc U.toOp.conjTranspose]
    rw [U.unitary_left, Matrix.one_mul]
    exact V.unitary_left,
   by
    -- Need: (U * V) * (U * V)† = 1
    rw [conjTranspose_mul]
    -- Goal: (U * V) * (V† * U†) = 1
    rw [← Matrix.mul_assoc, Matrix.mul_assoc U.toOp]
    rw [V.unitary_right, Matrix.mul_one]
    exact U.unitary_right⟩

instance {n : ℕ} : Mul (UnitaryOp n) where
  mul := UnitaryOp.mul

postfix:max "†" => UnitaryOp.adj

@[ext]
theorem UnitaryOp.ext {n : ℕ} {U V : UnitaryOp n} (h : U.toOp = V.toOp) : U = V := by
  cases U; cases V
  simp only [mk.injEq]
  exact h

/-- Unitary preserves inner products -/
theorem UnitaryOp.preserves_inner {n : ℕ} (U : UnitaryOp n) (x y : Fin n → ℂ) :
    dotProduct (star (U.toOp.mulVec x)) (U.toOp.mulVec y) = dotProduct (star x) y := by
  -- ⟨Ux|Uy⟩ = ⟨x|U†U|y⟩ = ⟨x|y⟩
  rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, U.unitary_left, vecMul_one]

-- ============================================================================
-- Section 6: Ket and Bra Types
-- ============================================================================

/-- A ket |ψ⟩ is an element of the Hilbert space -/
structure Ket (n : ℕ) where
  vec : Fin n → ℂ

/-- A bra ⟨ψ| is an element of the dual space -/
structure Bra (n : ℕ) where
  vec : Fin n → ℂ

/-- Addition of kets (vector space structure) -/
instance {n : ℕ} : Add (Ket n) where
  add ψ φ := ⟨ψ.vec + φ.vec⟩

/-- Scalar multiplication of kets (vector space structure) -/
instance {n : ℕ} : SMul ℂ (Ket n) where
  smul c ψ := ⟨c • ψ.vec⟩

/-- Scalar multiplication of bras (vector space structure) -/
instance {n : ℕ} : SMul ℂ (Bra n) where
  smul c φ := ⟨c • φ.vec⟩

/-- Addition of bras (vector space structure) -/
instance {n : ℕ} : Add (Bra n) where
  add ψ φ := ⟨ψ.vec + φ.vec⟩

/-- Negation of bras -/
instance {n : ℕ} : Neg (Bra n) where
  neg φ := ⟨-φ.vec⟩

/-- Subtraction of bras -/
instance {n : ℕ} : Sub (Bra n) where
  sub ψ φ := ⟨ψ.vec - φ.vec⟩

/-- Zero ket -/
instance {n : ℕ} : Zero (Ket n) where
  zero := ⟨0⟩

/-- Zero bra -/
instance {n : ℕ} : Zero (Bra n) where
  zero := ⟨0⟩

/-- Negation of kets -/
instance {n : ℕ} : Neg (Ket n) where
  neg ψ := ⟨-ψ.vec⟩

/-- Subtraction of kets -/
instance {n : ℕ} : Sub (Ket n) where
  sub ψ φ := ⟨ψ.vec - φ.vec⟩

/-- Extensionality for kets: two kets are equal if their components are equal -/
@[ext]
theorem Ket.ext {n : ℕ} {ψ φ : Ket n} (h : ∀ i, ψ.vec i = φ.vec i) : ψ = φ := by
  cases ψ; cases φ; congr; funext i; exact h i

/-- Extensionality for bras: two bras are equal if their components are equal -/
@[ext]
theorem Bra.ext {n : ℕ} {φ ψ : Bra n} (h : ∀ i, φ.vec i = ψ.vec i) : φ = ψ := by
  cases φ; cases ψ; congr; funext i; exact h i

-- ============================================================================
-- Ket Algebra Lemmas (Essential for algebraic proofs)
-- ============================================================================

/-- One times a ket: 1 • |ψ⟩ = |ψ⟩ -/
@[simp]
theorem Ket.one_smul {n : ℕ} (ψ : Ket n) : (1 : ℂ) • ψ = ψ := by
  ext i
  change (1 : ℂ) * ψ.vec i = ψ.vec i
  exact one_mul _

/-- Zero times a ket: 0 • |ψ⟩ = 0 -/
@[simp]
theorem Ket.zero_smul {n : ℕ} (ψ : Ket n) : (0 : ℂ) • ψ = 0 := by
  ext i
  change (0 : ℂ) * ψ.vec i = (0 : Ket n).vec i
  simp only [zero_mul]
  rfl

/-- Ket plus zero: |ψ⟩ + 0 = |ψ⟩ -/
@[simp]
theorem Ket.add_zero' {n : ℕ} (ψ : Ket n) : ψ + 0 = ψ := by
  ext i
  change ψ.vec i + 0 = ψ.vec i
  exact _root_.add_zero (ψ.vec i)

/-- Zero plus ket: 0 + |ψ⟩ = |ψ⟩ -/
@[simp]
theorem Ket.zero_add' {n : ℕ} (ψ : Ket n) : 0 + ψ = ψ := by
  ext i
  change 0 + ψ.vec i = ψ.vec i
  exact _root_.zero_add (ψ.vec i)

/-- Scalars add: (c + d) • |ψ⟩ = c • |ψ⟩ + d • |ψ⟩ -/
theorem Ket.add_smul {n : ℕ} (c d : ℂ) (ψ : Ket n) : (c + d) • ψ = c • ψ + d • ψ := by
  ext i
  change (c + d) * ψ.vec i = c * ψ.vec i + d * ψ.vec i
  ring

/-- Zero ket has zero components -/
@[simp] lemma Ket.zero_vec {n : ℕ} (j : Fin n) : (0 : Ket n).vec j = 0 := rfl

/-- Scalar times zero ket is zero -/
@[simp] lemma Ket.smul_zero {n : ℕ} (c : ℂ) : c • (0 : Ket n) = 0 := by
  ext i
  change c * (0 : Ket n).vec i = (0 : Ket n).vec i
  simp only [Ket.zero_vec, mul_zero]

/-- Scalar multiplication is associative: c • (d • ψ) = (c * d) • ψ -/
@[simp] lemma Ket.smul_smul {n : ℕ} (c d : ℂ) (ψ : Ket n) :
    c • (d • ψ) = (c * d) • ψ := by
  ext i
  change c * (d * ψ.vec i) = (c * d) * ψ.vec i
  ring

end  -- noncomputable section

end Quantum.Operators

open scoped BigOperators ComplexConjugate

/-- (conj z * z).im = 0 (product with conjugate is real) -/
lemma Complex.im_conj_mul_self (z : ℂ) : (starRingEnd ℂ z * z).im = 0 := by
  simp [mul_comm]
