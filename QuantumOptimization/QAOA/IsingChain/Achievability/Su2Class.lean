import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Geometry

/-!
# The SU(2) Laurent class in `w`-polynomial form — `Cstar`, `IsClassL`, `QSPRealizable`

The polynomial-pair encoding of the achievable per-mode QSP unitaries. A realizable
`G(z)` of half-degree `L = 2P+1` (odd Laurent entries in `z = e^{ik/2}`, SU(2)-valued
on the circle) is encoded by the pair `(a, b)` of ordinary polynomials in `w = z²`:
`G(z) = z^{−L}·[[a(w), −(Cstar L b)(w)],[b(w), (Cstar L a)(w)]]`, where
`Cstar L x = reflect L (map conj x)` is the polynomial avatar of the circle dagger
`x*(z) = conj-coeffs x (1/z)`.

Class invariants (`IsClassL`): degree bounds, the unitarity identity
`a·Cstar L a + b·Cstar L b = X^L`, palindromy `reflect L a = a` and antipalindromy
`reflect L b = −b` (the `G(1/z) = σz G(z) σz` symmetry of the layer products).

`QSPRealizable P` is the **isolated crux predicate**: every class
member is realized by real QAOA angles, in the precise sense that vanishing of `b` at
an active node forces the corresponding `epsilonMode` to vanish. `Angles.lean` and
`Tightness.lean` consume it as a hypothesis (conditional closure);
`Factorization.lean` discharges it.

## Main definitions
- `Cstar`, `IsClassL`, `classMat`, `QSPRealizable`.

## Main statements
- `det_classMat` — `det (classMat L a b) = X^L` for class members.
- `Cstar_Cstar` — involutivity of `Cstar` on degree-bounded polynomials.
-/

namespace QAOA.IsingChain.Achievability

open Polynomial

noncomputable section

/-- The conj-reflect involution `Cstar L x = reflect L (x.map conj)` — the
`w`-polynomial avatar of the circle dagger `x*(z) = Σ conj(x_j) z^{−j}` after
clearing `z^L`. -/
def Cstar (L : ℕ) (x : Polynomial ℂ) : Polynomial ℂ :=
  Polynomial.reflect L (x.map (starRingEnd ℂ))

/-- Membership in the achievable SU(2) Laurent class at half-degree `L`: degree
bounds, the unitarity identity, palindromy of `a`, antipalindromy of `b`. -/
structure IsClassL (L : ℕ) (a b : Polynomial ℂ) where
  degA : a.natDegree ≤ L
  degB : b.natDegree ≤ L
  unitarity : a * Cstar L a + b * Cstar L b = Polynomial.X ^ L
  palinA : Polynomial.reflect L a = a
  antiB : Polynomial.reflect L b = -b

/-- The 2×2 polynomial matrix of a class member. -/
def classMat (L : ℕ) (a b : Polynomial ℂ) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![a, -(Cstar L b); b, Cstar L a]

/-- **The QSP realizability predicate (the isolated crux).** Every
class member `(a, b) ∈ C_{2P+1}` is realized by real angle families `(γ, β)`: at any
active node `w_n = e^{i k_n}` where `b` vanishes, the per-mode residual energy
vanishes. `Factorization.lean` discharges this (Haah peel + parity ⟹ equatorial);
`Angles.lean` consumes it applied to the explicit pair `(Rpoly P, Tpoly P)`, whose
`b = T` vanishes at *all* nodes. -/
def QSPRealizable (P : ℕ) :=
  ∀ a b : Polynomial ℂ, IsClassL (2 * P + 1) a b →
    ∃ γ β : Fin P → ℝ, ∀ n : Fin P,
      b.eval (Complex.exp (Complex.I * (JordanWigner.waveVectorABC P n : ℝ))) = 0 →
      JordanWigner.epsilonMode (n : JordanWigner.WaveVectorABC P) γ β = 0

/-- The determinant of the class matrix is exactly `X^L` (the SU(2)-on-circle
determinant, cleared of `z^{−2L}`). -/
theorem det_classMat (L : ℕ) (a b : Polynomial ℂ) (h : IsClassL L a b) :
    (classMat L a b).det = Polynomial.X ^ L := by
  unfold classMat
  rw [Matrix.det_fin_two_of]
  linear_combination h.unitarity

/-- `Cstar` is additive. -/
theorem Cstar_add (L : ℕ) (x y : Polynomial ℂ) :
    Cstar L (x + y) = Cstar L x + Cstar L y := by
  unfold Cstar
  rw [Polynomial.map_add, reflect_add]

/-- `Cstar` and negation. -/
theorem Cstar_neg (L : ℕ) (x : Polynomial ℂ) : Cstar L (-x) = -(Cstar L x) := by
  unfold Cstar
  rw [Polynomial.map_neg, reflect_neg]

/-- `Cstar` is an involution. -/
theorem Cstar_Cstar (L : ℕ) (x : Polynomial ℂ) :
    Cstar L (Cstar L x) = x := by
  unfold Cstar
  rw [reflect_map, reflect_reflect, map_map]
  have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
    ext z
    exact Complex.conj_conj z
  rw [hcc, Polynomial.map_id]

/-- Coefficients of `Cstar`: `(Cstar L x).coeff j = conj (x.coeff (L − j))` for
`j ≤ L` (and `revAt` fixes indices above `L`). -/
theorem Cstar_coeff (L : ℕ) (x : Polynomial ℂ) (j : ℕ) :
    (Cstar L x).coeff j = (starRingEnd ℂ) (x.coeff (revAt L j)) := by
  unfold Cstar
  rw [coeff_reflect, coeff_map]

-- ============================================================================
-- Primitive equatorial factors (the Factorization ↔ Angles frozen interface)
-- ============================================================================

/-- The equatorial rank-1 projector at Bloch phase `φ`:
`P_φ = (I + cos φ·σx + sin φ·σy)/2 = ½·!![1, e^{−iφ}; e^{iφ}, 1]`.
These are exactly the projectors Haah's parity argument forces (`Tr(σz P) = 0`). -/
def equatorialProj (φ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1/2, Complex.exp (-φ * Complex.I) / 2; Complex.exp (φ * Complex.I) / 2, 1/2]

/-- The degree-1 primitive polynomial matrix `E_φ(w) = w·P_φ + (I − P_φ)`
(Haah's primitive matrix, in the `w = z²`-cleared form `z·P + z⁻¹·Q = z⁻¹(w·P + Q)`). -/
def primFactor (φ : ℝ) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  ((equatorialProj φ).map fun c => Polynomial.C c * Polynomial.X) +
    ((1 - equatorialProj φ).map fun c => Polynomial.C c)

/-- The constant diagonal phase matrix `e^{iχσz}` lifted to polynomial entries. -/
def diagPhaseMat (χ : ℝ) : Matrix (Fin 2) (Fin 2) (Polynomial ℂ) :=
  !![Polynomial.C (Complex.exp (χ * Complex.I)), 0;
     0, Polynomial.C (Complex.exp (-χ * Complex.I))]

/-- `e^{−iφ}·e^{iφ} = 1` (the exponential cancellation used throughout the
equatorial algebra). -/
theorem exp_neg_mul_exp (φ : ℝ) :
    Complex.exp (-φ * Complex.I) * Complex.exp (φ * Complex.I) = 1 := by
  rw [← Complex.exp_add, show (-φ * Complex.I + φ * Complex.I : ℂ) = 0 by ring,
    Complex.exp_zero]

/-- The equatorial projector is idempotent. -/
theorem equatorialProj_idem (φ : ℝ) :
    equatorialProj φ * equatorialProj φ = equatorialProj φ := by
  have hE : Complex.exp (φ * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  unfold equatorialProj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, neg_mul, Complex.exp_neg] <;>
    field_simp <;>
    ring

/-- The equatorial projector has zero `σz`-component: its diagonal entries are equal
(`Tr(σz P_φ) = 0` in matrix-entry form). -/
theorem equatorialProj_diag_eq (φ : ℝ) :
    equatorialProj φ 0 0 = equatorialProj φ 1 1 := by
  unfold equatorialProj
  simp

end

end QAOA.IsingChain.Achievability
