import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.LinearCombination
import QuantumOptimization.QAOA.IsingChain.Achievability.AlternatingPoly
import QuantumOptimization.QAOA.IsingChain.Achievability.RootSplit
import QuantumOptimization.QAOA.IsingChain.Achievability.Su2Class

/-!
# The Fejér–Riesz complement target `q̃`, its root structure, and the factor `R`

This module builds the polynomial `q̃ := X^{2P+1} + T²` (`L = 2P+1`), the
Fejér–Riesz factorand whose square root `R` is the spectral complement of the
alternating node polynomial `T`. We establish its degree, reality, leading
coefficient, the self-reciprocity `reflect (2L) q̃ = q̃`, and the root-location
facts: the only real or unit-circle root is `−1`, a root of multiplicity exactly
two. Off-axis roots come in inversion/conjugation-closed quadruples.

The §3.4 capstone applies the root-selection lemma `exists_conj_split` to
`(qtilde P).roots`, extracting an inversion-closed spectral half `S₀` and the
spectral factor `Rpoly P := C(1/(2P+2))·∏_{ζ∈S₀}(X − C ζ)`. We prove the
Fejér–Riesz identity `R·R̄ = q̃`, the palindromy `reflect L R = R`, and the
class membership `IsClassL L (Rpoly P) (Tpoly P)` consumed by `Angles.lean`.

## Main definitions
- `qtilde P` — `X^{2P+1} + (Tpoly P)²`.
- `RpolyRootHalf P` — an inversion-closed spectral half of `(qtilde P).roots`.
- `Rpoly P` — the spectral factor `C(1/(2P+2))·∏_{ζ∈S₀}(X − C ζ)`.

## Main statements
- `qtilde_natDegree`, `qtilde_map_conj`, `qtilde_ne_zero`, `qtilde_eval_zero_ne`,
  `qtilde_leadingCoeff` — basic structure.
- `reflect_qtilde` — self-reciprocity at degree `2L`.
- `qtilde_inv_root`, `qtilde_root_ne_zero`, `qtilde_conj_root` — root symmetries.
- `qtilde_real_root_iff`, `qtilde_circle_root_iff` — only real/circle root is `−1`.
- `qtilde_rootMultiplicity_neg_one` — `−1` has multiplicity exactly `2`.
- `qtilde_roots_card`, `qtilde_roots_map_conj`, `qtilde_roots_map_inv`,
  `qtilde_roots_filter_axis` — the four `exists_conj_split` hypotheses.
- `Rpoly_natDegree`, `Rpoly_mul_conj`, `reflect_Rpoly`, `Rpoly_eval_neg_one` —
  the spectral factor's structure (`R·R̄ = q̃`, palindromy).
- `isClassL_R_T` — the §3.4 capstone: `(Rpoly P, Tpoly P) ∈ IsClassL (2P+1)`.
-/

namespace QAOA.IsingChain.Achievability

open Polynomial Finset

/-- Re-bind the `X` token to `Polynomial.X` at high priority (the transitive
`Quantum.Gates` import otherwise shadows it with `pauliX`). -/
local notation (priority := high) "X" => Polynomial.X

noncomputable section

/-- The complement target `q̃ := X^{2P+1} + T²`, `L = 2P+1`. Real coefficients;
the Fejér–Riesz factorand. -/
def qtilde (P : ℕ) : Polynomial ℂ := X ^ (2 * P + 1) + (Tpoly P) ^ 2

/-- `T` has leading coefficient `1/(2P+2)`. -/
theorem Tpoly_leadingCoeff (P : ℕ) : (Tpoly P).leadingCoeff = 1 / (2 * (P : ℂ) + 2) := by
  rw [Polynomial.leadingCoeff, Tpoly_natDegree, Tpoly_coeff P (by omega)]
  have : ((-1 : ℂ)) ^ (2 * P + 1 + 1) = 1 := by
    rw [show 2 * P + 1 + 1 = 2 * (P + 1) by ring, pow_mul]; norm_num
  rw [this]

/-- The square `T²` has natDegree `2(2P+1)`. -/
theorem Tpoly_sq_natDegree (P : ℕ) : ((Tpoly P) ^ 2).natDegree = 2 * (2 * P + 1) := by
  rw [natDegree_pow, Tpoly_natDegree]

/-- `q̃` has natDegree exactly `2(2P+1)`. -/
theorem qtilde_natDegree (P : ℕ) : (qtilde P).natDegree = 2 * (2 * P + 1) := by
  unfold qtilde
  rw [natDegree_add_eq_right_of_natDegree_lt, Tpoly_sq_natDegree]
  rw [Tpoly_sq_natDegree, natDegree_X_pow]
  omega

/-- `q̃` has real coefficients: conjugating coefficients fixes it. -/
theorem qtilde_map_conj (P : ℕ) : (qtilde P).map (starRingEnd ℂ) = qtilde P := by
  unfold qtilde
  rw [Polynomial.map_add, Polynomial.map_pow, Polynomial.map_pow, Polynomial.map_X,
    Tpoly_map_conj]

/-- The leading coefficient of `q̃` is `1/(2P+2)²`. -/
theorem qtilde_leadingCoeff (P : ℕ) :
    (qtilde P).leadingCoeff = 1 / (2 * (P : ℂ) + 2) ^ 2 := by
  unfold qtilde
  have hlt : (X ^ (2 * P + 1) : Polynomial ℂ).degree < ((Tpoly P) ^ 2).degree := by
    apply degree_lt_degree
    rw [Tpoly_sq_natDegree, natDegree_X_pow]
    omega
  rw [leadingCoeff_add_of_degree_lt hlt, leadingCoeff_pow, Tpoly_leadingCoeff,
    div_pow, one_pow]

/-- `q̃ ≠ 0` (positive degree). -/
theorem qtilde_ne_zero (P : ℕ) : qtilde P ≠ 0 := by
  intro hc
  have hd : (qtilde P).natDegree = 2 * (2 * P + 1) := qtilde_natDegree P
  rw [hc, natDegree_zero] at hd
  omega

/-- `q̃(0) = T(0)² = 1/(2P+2)² ≠ 0`. -/
theorem qtilde_eval_zero_ne (P : ℕ) : (qtilde P).eval 0 ≠ 0 := by
  unfold qtilde
  rw [eval_add, eval_pow, eval_X, eval_pow]
  have hX : (0 : ℂ) ^ (2 * P + 1) = 0 := by
    rw [zero_pow]; omega
  rw [hX, zero_add]
  -- T(0) = coeff 0 = -1/(2P+2) ≠ 0
  rw [← coeff_zero_eq_eval_zero, Tpoly_coeff P (by omega)]
  intro hc
  rw [pow_eq_zero_iff (by norm_num)] at hc
  rw [div_eq_zero_iff] at hc
  rcases hc with hc | hc
  · norm_num at hc
  · exact two_P_add_two_ne_zero P hc

/-! ### §3.1 Root symmetries -/

/-- `q̃` is self-reciprocal at degree `2L`: `reflect (2L) q̃ = q̃`. -/
theorem reflect_qtilde (P : ℕ) :
    (qtilde P).reflect (2 * (2 * P + 1)) = qtilde P := by
  unfold qtilde
  rw [reflect_add]
  congr 1
  · -- reflect (2L) X^L = X^L
    rw [show (X : Polynomial ℂ) ^ (2 * P + 1) = X ^ (2 * P + 1) * (1 : Polynomial ℂ) by ring,
      mul_one]
    rw [reflect_monomial, revAt_le (by omega)]
    congr 1
    omega
  · -- reflect (2L) T² = T²
    rw [sq, show 2 * (2 * P + 1) = (2 * P + 1) + (2 * P + 1) by ring,
      reflect_mul (Tpoly P) (Tpoly P) (le_of_eq (Tpoly_natDegree P))
        (le_of_eq (Tpoly_natDegree P)), reflect_Tpoly, neg_mul_neg, ← sq]

/-- Every root of `q̃` is nonzero (since `q̃(0) ≠ 0`). -/
theorem qtilde_root_ne_zero (P : ℕ) {ζ : ℂ} (hζ : (qtilde P).IsRoot ζ) : ζ ≠ 0 := by
  intro h0
  apply qtilde_eval_zero_ne P
  rw [h0] at hζ
  exact hζ

/-- `eval₂` along the identity ring hom is ordinary `eval`. -/
private lemma eval₂_id_eq_eval (p : Polynomial ℂ) (x : ℂ) :
    eval₂ (RingHom.id ℂ) x p = eval x p := by
  rw [eval₂_eq_eval_map, Polynomial.map_id]

/-- Inversion-closure of roots: a nonzero root `ζ` has `ζ⁻¹` a root too. -/
theorem qtilde_inv_root (P : ℕ) {ζ : ℂ} (hζ0 : ζ ≠ 0) (hζ : (qtilde P).IsRoot ζ) :
    (qtilde P).IsRoot ζ⁻¹ := by
  letI : Invertible ζ := invertibleOfNonzero hζ0
  have hdeg : (qtilde P).natDegree ≤ 2 * (2 * P + 1) := le_of_eq (qtilde_natDegree P)
  have hkey := (eval₂_reflect_eq_zero_iff (RingHom.id ℂ) ζ (2 * (2 * P + 1)) (qtilde P) hdeg)
  rw [reflect_qtilde] at hkey
  have hinv : (⅟ ζ : ℂ) = ζ⁻¹ := invOf_eq_left_inv (inv_mul_cancel₀ hζ0)
  rw [hinv, eval₂_id_eq_eval, eval₂_id_eq_eval] at hkey
  rw [Polynomial.IsRoot, hkey]
  exact hζ

/-- Conjugation-closure of roots: real coefficients ⟹ `conj ζ` is a root when `ζ` is. -/
theorem qtilde_conj_root (P : ℕ) {ζ : ℂ} (hζ : (qtilde P).IsRoot ζ) :
    (qtilde P).IsRoot ((starRingEnd ℂ) ζ) := by
  -- eval (conj ζ) (q̃.map conj) = conj (eval ζ q̃); and q̃.map conj = q̃.
  have hcommute : eval ((starRingEnd ℂ) ζ) ((qtilde P).map (starRingEnd ℂ))
      = (starRingEnd ℂ) (eval ζ (qtilde P)) := by
    rw [← eval₂_eq_eval_map]
    exact Polynomial.eval₂_at_apply (starRingEnd ℂ) ζ
  rw [qtilde_map_conj] at hcommute
  rw [Polynomial.IsRoot, hcommute, hζ, map_zero]

/-! ### §3.2 Root location: real and circle roots are only `−1`

The derivative facts for the multiplicity computation are obtained by repeatedly
differentiating the telescoping identity `(X+1)·T = C(1/M)·(X^M − 1)`. -/

/-- `T(−1) = −1`. -/
theorem Tpoly_eval_neg_one (P : ℕ) : (Tpoly P).eval (-1 : ℂ) = -1 := by
  have h := Tpoly_eval_neg_real P 1
  simp only [Complex.ofReal_one, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h
  rw [h]
  push_cast
  field_simp

/-- Differentiating once: `T + (X+1)·T' = C(1/M)·(C M · X^{M−1})`. -/
theorem Tpoly_deriv_identity (P : ℕ) :
    Tpoly P + (X + 1) * derivative (Tpoly P)
      = C (1 / (2 * (P : ℂ) + 2)) * (C ((2 * P + 2 : ℕ) : ℂ) * X ^ (2 * P + 1)) := by
  have h := congrArg derivative (X_add_one_mul_Tpoly P)
  simp only [derivative_mul, derivative_add, derivative_X, derivative_one,
    derivative_sub, derivative_X_pow, derivative_C,
    zero_mul, add_zero, zero_add, sub_zero] at h
  rw [show (2 * P + 2 - 1) = 2 * P + 1 by omega] at h
  linear_combination h

/-- Differentiating twice: `2·T' + (X+1)·T'' = C(1/M)·(C M · (C (M−1) · X^{M−2}))`. -/
theorem Tpoly_deriv2_identity (P : ℕ) :
    (2 : Polynomial ℂ) * derivative (Tpoly P)
        + (X + 1) * derivative (derivative (Tpoly P))
      = C (1 / (2 * (P : ℂ) + 2))
        * (C ((2 * P + 2 : ℕ) : ℂ) * (C ((2 * P + 1 : ℕ) : ℂ) * X ^ (2 * P))) := by
  have h := congrArg derivative (Tpoly_deriv_identity P)
  simp only [derivative_mul, derivative_add, derivative_X, derivative_one,
    derivative_X_pow, derivative_C,
    zero_mul, add_zero, zero_add] at h
  rw [show (2 * P + 1 - 1) = 2 * P by omega] at h
  linear_combination h

/-- Differentiating three times:
`3·T'' + (X+1)·T''' = C(1/M)·(C M · (C (M−1) · (C (M−2) · X^{M−3})))`.
(At `P = 0` both sides vanish, since `C (2P) = 0` and `T'' = 0`.) -/
theorem Tpoly_deriv3_identity (P : ℕ) :
    (3 : Polynomial ℂ) * derivative (derivative (Tpoly P))
        + (X + 1) * derivative (derivative (derivative (Tpoly P)))
      = C (1 / (2 * (P : ℂ) + 2))
        * (C ((2 * P + 2 : ℕ) : ℂ)
          * (C ((2 * P + 1 : ℕ) : ℂ)
            * (C ((2 * P : ℕ) : ℂ) * X ^ (2 * P - 1)))) := by
  have h := congrArg derivative (Tpoly_deriv2_identity P)
  simp only [derivative_mul, derivative_add, derivative_X, derivative_one,
    derivative_X_pow, derivative_C, derivative_ofNat,
    zero_mul, add_zero, zero_add] at h
  linear_combination h

/-- Evaluating the once-differentiated identity at `−1`: `2·T'(−1) = 2P+1`. -/
theorem Tpoly_deriv_eval_neg_one (P : ℕ) :
    2 * (derivative (Tpoly P)).eval (-1 : ℂ) = (2 * (P : ℂ) + 1) := by
  have h := congrArg (Polynomial.eval (-1 : ℂ)) (Tpoly_deriv2_identity P)
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat, eval_one] at h
  rw [show (-1 : ℂ) + 1 = 0 by ring, zero_mul, add_zero] at h
  rw [show ((-1 : ℂ)) ^ (2 * P) = 1 by
    rw [pow_mul]; norm_num] at h
  rw [mul_one] at h
  rw [h]
  have hM := two_P_add_two_ne_zero P
  push_cast
  field_simp

/-- Evaluating the thrice-differentiated identity at `−1`: `3·T''(−1) = −(2P+1)(2P)`. -/
theorem Tpoly_deriv2_eval_neg_one (P : ℕ) :
    3 * (derivative (derivative (Tpoly P))).eval (-1 : ℂ)
      = -((2 * (P : ℂ) + 1) * (2 * (P : ℂ))) := by
  rcases Nat.eq_zero_or_pos P with hP0 | hP1
  · -- P = 0: T'' = 0, RHS = 0
    subst hP0
    -- Tpoly 0 = (X-1)/2, so T'' = 0
    have hd2 : derivative (derivative (Tpoly 0)) = 0 := by
      have := Tpoly_natDegree 0
      have hle : (Tpoly 0).natDegree ≤ 1 := by omega
      have h1 : (derivative (Tpoly 0)).natDegree ≤ 0 :=
        le_trans (natDegree_derivative_le _) (by omega)
      have : derivative (Tpoly 0) = C ((derivative (Tpoly 0)).coeff 0) :=
        (Polynomial.eq_C_of_natDegree_le_zero h1)
      rw [this, derivative_C]
    rw [hd2]
    simp
  · have h := congrArg (Polynomial.eval (-1 : ℂ)) (Tpoly_deriv3_identity P)
    simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow, eval_ofNat, eval_one] at h
    rw [show (-1 : ℂ) + 1 = 0 by ring, zero_mul, add_zero] at h
    rw [show ((-1 : ℂ)) ^ (2 * P - 1) = -1 by
      rw [show 2 * P - 1 = 2 * (P - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num] at h
    rw [h]
    have hM := two_P_add_two_ne_zero P
    push_cast
    field_simp

/-- `q̃(−1) = (−1)^L + T(−1)² = −1 + 1 = 0`. -/
theorem qtilde_eval_neg_one (P : ℕ) : (qtilde P).eval (-1 : ℂ) = 0 := by
  unfold qtilde
  rw [eval_add, eval_pow, eval_X, eval_pow, Tpoly_eval_neg_one]
  rw [show ((-1 : ℂ)) ^ (2 * P + 1) = -1 by
    rw [pow_succ, pow_mul]; norm_num]
  ring

/-- The derivative of `q̃`: `q̃' = C L · X^{L−1} + C 2 · T · T'`. -/
theorem derivative_qtilde (P : ℕ) :
    derivative (qtilde P)
      = C ((2 * P + 1 : ℕ) : ℂ) * X ^ (2 * P) + C 2 * Tpoly P * derivative (Tpoly P) := by
  unfold qtilde
  rw [derivative_add, derivative_X_pow, derivative_sq]
  rw [show (2 * P + 1 - 1) = 2 * P by omega]

/-- `q̃'(−1) = L − 2·T'(−1) = L − L = 0`. -/
theorem qtilde_deriv_eval_neg_one (P : ℕ) : (derivative (qtilde P)).eval (-1 : ℂ) = 0 := by
  rw [derivative_qtilde]
  rw [eval_add, eval_mul, eval_mul, eval_mul, eval_C, eval_pow, eval_X, eval_C,
    Tpoly_eval_neg_one]
  rw [show ((-1 : ℂ)) ^ (2 * P) = 1 by rw [pow_mul]; norm_num]
  have hd := Tpoly_deriv_eval_neg_one P
  push_cast
  linear_combination -hd

/-- The second derivative of `q̃`:
`q̃'' = C L · (C (L−1) · X^{L−2}) + C 2 · (T' · T' + T · T'')`. -/
theorem derivative2_qtilde (P : ℕ) :
    derivative (derivative (qtilde P))
      = C ((2 * P + 1 : ℕ) : ℂ) * (C ((2 * P : ℕ) : ℂ) * X ^ (2 * P - 1))
        + C 2 * (derivative (Tpoly P) * derivative (Tpoly P)
          + Tpoly P * derivative (derivative (Tpoly P))) := by
  rw [derivative_qtilde]
  simp only [derivative_add, derivative_X_pow, derivative_mul,
    derivative_C, zero_mul, zero_add]
  ring

/-- The single value `T'(−1) = (2P+1)/2` (used to make `q̃''(−1)` explicit). -/
theorem Tpoly_deriv_eval_neg_one' (P : ℕ) :
    (derivative (Tpoly P)).eval (-1 : ℂ) = (2 * (P : ℂ) + 1) / 2 := by
  have hd := Tpoly_deriv_eval_neg_one P
  linear_combination hd / 2

/-- The single value `T''(−1) = −(2P+1)(2P)/3`. -/
theorem Tpoly_deriv2_eval_neg_one' (P : ℕ) :
    (derivative (derivative (Tpoly P))).eval (-1 : ℂ)
      = -((2 * (P : ℂ) + 1) * (2 * (P : ℂ))) / 3 := by
  have hd := Tpoly_deriv2_eval_neg_one P
  linear_combination hd / 3

/-- `q̃''(−1) = (2P+1)(2P+3)/6` — in particular nonzero. The `X^{L−2}` term is
handled per `P = 0` (where its coefficient `C (2P)` vanishes) and `P ≥ 1`. -/
theorem qtilde_deriv2_eval_neg_one (P : ℕ) :
    (derivative (derivative (qtilde P))).eval (-1 : ℂ)
      = (2 * (P : ℂ) + 1) * (2 * (P : ℂ) + 3) / 6 := by
  rw [derivative2_qtilde]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X, Tpoly_eval_neg_one,
    Tpoly_deriv_eval_neg_one', Tpoly_deriv2_eval_neg_one']
  rcases Nat.eq_zero_or_pos P with hP0 | hP1
  · subst hP0
    norm_num
  · rw [show ((-1 : ℂ)) ^ (2 * P - 1) = -1 by
      rw [show 2 * P - 1 = 2 * (P - 1) + 1 by omega, pow_succ, pow_mul]
      norm_num]
    push_cast
    ring

/-- `q̃''(−1) ≠ 0`. -/
theorem qtilde_deriv2_eval_neg_one_ne (P : ℕ) :
    (derivative (derivative (qtilde P))).eval (-1 : ℂ) ≠ 0 := by
  rw [qtilde_deriv2_eval_neg_one]
  apply div_ne_zero
  · apply mul_ne_zero
    · have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
      intro hc
      have hc' : (2 * (P : ℝ) + 1) = 0 := by exact_mod_cast congrArg Complex.re hc
      linarith
    · have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
      intro hc
      have hc' : (2 * (P : ℝ) + 3) = 0 := by exact_mod_cast congrArg Complex.re hc
      linarith
  · norm_num

/-- `−1` is a root of `q̃` of multiplicity exactly `2`. Proven by the char-0
derivative-multiplicity chain: `q̃(−1) = q̃'(−1) = 0` but `q̃''(−1) ≠ 0`. -/
theorem qtilde_rootMultiplicity_neg_one (P : ℕ) :
    Polynomial.rootMultiplicity (-1) (qtilde P) = 2 := by
  -- the three eval facts
  have h0 : (qtilde P).IsRoot (-1) := qtilde_eval_neg_one P
  have h1 : (derivative (qtilde P)).IsRoot (-1) := qtilde_deriv_eval_neg_one P
  have h2ne := qtilde_deriv2_eval_neg_one_ne P
  -- nonvanishing of q̃'' and q̃' as polynomials
  have hq2_ne : derivative (derivative (qtilde P)) ≠ 0 := by
    intro hc; rw [hc, eval_zero] at h2ne; exact h2ne rfl
  have hq1_ne : derivative (qtilde P) ≠ 0 := by
    intro hc; apply hq2_ne; rw [hc, derivative_zero]
  have hq_ne : qtilde P ≠ 0 := qtilde_ne_zero P
  -- multiplicity drops by 1 under each derivative at the root
  have step1 : rootMultiplicity (-1 : ℂ) (derivative (qtilde P))
      = rootMultiplicity (-1) (qtilde P) - 1 :=
    derivative_rootMultiplicity_of_root h0
  have step2 : rootMultiplicity (-1 : ℂ) (derivative (derivative (qtilde P)))
      = rootMultiplicity (-1) (derivative (qtilde P)) - 1 :=
    derivative_rootMultiplicity_of_root h1
  -- q̃'' does NOT vanish at −1, so its multiplicity is 0
  have hm2 : rootMultiplicity (-1 : ℂ) (derivative (derivative (qtilde P))) = 0 :=
    rootMultiplicity_eq_zero (by
      simpa [Polynomial.IsRoot] using h2ne)
  -- lower bounds from the roots
  have hpos0 : 0 < rootMultiplicity (-1 : ℂ) (qtilde P) :=
    (rootMultiplicity_pos hq_ne).mpr h0
  have hpos1 : 0 < rootMultiplicity (-1 : ℂ) (derivative (qtilde P)) :=
    (rootMultiplicity_pos hq1_ne).mpr h1
  -- assemble by omega
  omega

/-- `T` evaluated at a real point is real (its imaginary part vanishes). -/
theorem Tpoly_eval_ofReal_im (P : ℕ) (x : ℝ) : ((Tpoly P).eval (x : ℂ)).im = 0 := by
  have hconj : (starRingEnd ℂ) ((Tpoly P).eval (x : ℂ)) = (Tpoly P).eval (x : ℂ) := by
    have hcommute : eval ((starRingEnd ℂ) (x : ℂ)) ((Tpoly P).map (starRingEnd ℂ))
        = (starRingEnd ℂ) (eval (x : ℂ) (Tpoly P)) := by
      rw [← eval₂_eq_eval_map]
      exact Polynomial.eval₂_at_apply (starRingEnd ℂ) (x : ℂ)
    rw [Tpoly_map_conj, Complex.conj_ofReal] at hcommute
    exact hcommute.symm
  have := congrArg Complex.im hconj
  simp only [Complex.conj_im] at this
  linarith

/-- For real `x`, the real evaluation `q̃(x).re = x^L + (T(x).re)²`. -/
theorem qtilde_eval_ofReal_re (P : ℕ) (x : ℝ) :
    ((qtilde P).eval (x : ℂ)).re = x ^ (2 * P + 1) + (((Tpoly P).eval (x : ℂ)).re) ^ 2 := by
  unfold qtilde
  rw [eval_add, eval_pow, eval_X, Complex.add_re]
  have him := Tpoly_eval_ofReal_im P x
  have hxpow : ((x : ℂ) ^ (2 * P + 1)).re = x ^ (2 * P + 1) := by
    rw [← Complex.ofReal_pow]
    exact Complex.ofReal_re _
  have hTsq : (eval (x : ℂ) (Tpoly P) ^ 2).re = ((eval (x : ℂ) (Tpoly P)).re) ^ 2 := by
    rw [sq, sq, Complex.mul_re, him]
    ring
  rw [hxpow, eval_pow, hTsq]

/-- On the negative real axis, `T(−ρ).re = TpolyRealNeg P ρ`. -/
theorem Tpoly_eval_neg_re (P : ℕ) (ρ : ℝ) :
    ((Tpoly P).eval (-(ρ : ℂ))).re = TpolyRealNeg P ρ := by
  rw [Tpoly_eval_neg_eq, Complex.ofReal_re]

/-- **The only real root of `q̃` is `−1`.** -/
theorem qtilde_real_root_iff (P : ℕ) {x : ℝ} :
    (qtilde P).IsRoot (x : ℂ) ↔ x = -1 := by
  constructor
  · intro hroot
    -- the real part of q̃(x) is zero
    have hre : ((qtilde P).eval (x : ℂ)).re = 0 := by rw [hroot]; rfl
    rw [qtilde_eval_ofReal_re] at hre
    rcases lt_trichotomy x 0 with hx | hx | hx
    · -- x < 0: write x = -ρ, ρ > 0
      set ρ : ℝ := -x with hρdef
      have hρ : 0 < ρ := by rw [hρdef]; linarith
      have hxρ : (x : ℝ) = -ρ := by rw [hρdef]; ring
      -- rewrite the real-part identity in terms of ρ
      have hTre : ((Tpoly P).eval (x : ℂ)).re = TpolyRealNeg P ρ := by
        rw [hxρ]
        push_cast
        rw [Tpoly_eval_neg_re]
      rw [hTre] at hre
      -- x^L = (-ρ)^L = -ρ^L  (L odd)
      have hxL : x ^ (2 * P + 1) = -(ρ ^ (2 * P + 1)) := by
        rw [hxρ, show 2 * P + 1 = 2 * P + 1 by rfl]
        rw [neg_pow, show ((-1 : ℝ)) ^ (2 * P + 1) = -1 by
          rw [pow_succ, pow_mul]; norm_num]
        ring
      rw [hxL] at hre
      -- hence (TpolyRealNeg)² = ρ^L, so ρ = 1, so x = -1
      have heq : (TpolyRealNeg P ρ) ^ 2 = ρ ^ (2 * P + 1) := by linarith
      have hρ1 : ρ = 1 := (Tpoly_neg_sq_eq_iff P hρ).mp heq
      rw [hρdef] at hρ1
      linarith
    · -- x = 0: contradiction with q̃(0) ≠ 0
      exfalso
      apply qtilde_eval_zero_ne P
      rw [hx] at hroot
      simpa using hroot
    · -- x > 0: q̃(x).re = x^L + (T(x).re)² > 0
      exfalso
      have hxL : 0 < x ^ (2 * P + 1) := by positivity
      have hsq : 0 ≤ (((Tpoly P).eval (x : ℂ)).re) ^ 2 := sq_nonneg _
      linarith
  · intro hx
    subst hx
    change (qtilde P).eval ((-1 : ℝ) : ℂ) = 0
    rw [Complex.ofReal_neg, Complex.ofReal_one]
    exact qtilde_eval_neg_one P

/-- **The only unit-circle root of `q̃` is `−1`.** -/
theorem qtilde_circle_root_iff (P : ℕ) {θ : ℝ} :
    (qtilde P).IsRoot (Complex.exp (Complex.I * θ)) ↔ Complex.exp (Complex.I * θ) = -1 := by
  set w : ℂ := Complex.exp (Complex.I * θ) with hwdef
  have hwnorm : ‖w‖ = 1 := by rw [hwdef, Complex.norm_exp]; simp
  constructor
  · intro hroot
    by_contra hne
    -- q̃(w) = 0 ⟹ T(w)² = -w^L
    have hTsq : (Tpoly P).eval w ^ 2 = -(w ^ (2 * P + 1)) := by
      have hr : (qtilde P).eval w = 0 := hroot
      unfold qtilde at hr
      rw [eval_add, eval_pow, eval_X, eval_pow] at hr
      linear_combination hr
    -- take norms: ‖T(w)‖² = ‖w^L‖ = 1
    have hnorm_sq : ‖(Tpoly P).eval w‖ ^ 2 = 1 := by
      have h1 : ‖(Tpoly P).eval w ^ 2‖ = ‖w ^ (2 * P + 1)‖ := by
        rw [hTsq, norm_neg]
      rw [norm_pow, norm_pow, hwnorm, one_pow] at h1
      exact h1
    have hnorm : ‖(Tpoly P).eval w‖ = 1 := by
      nlinarith [norm_nonneg ((Tpoly P).eval w), hnorm_sq]
    -- but ‖T(w)‖ < 1 since w ≠ -1
    have hlt : ‖(Tpoly P).eval w‖ < 1 := Tpoly_abs_circle_lt_one P hne
    linarith
  · intro hw
    rw [hw]
    exact qtilde_eval_neg_one P

/-! ### §3.3a Factorisation and reflect helpers (shared by `qtilde_roots_map_inv`,
`Rpoly_mul_conj`, `reflect_Rpoly`) -/

/-- `reflect 1 X = 1` (the degree-1 reversal sends `X` to the constant `1`). -/
private lemma reflect_one_X : Polynomial.reflect 1 (X : Polynomial ℂ) = 1 := by
  simp [Polynomial.reflect]

/-- The per-factor reflection: for `ζ ≠ 0`,
`reflect 1 (X − C ζ) = C (−ζ) · (X − C ζ⁻¹)`. -/
private lemma reflect_one_X_sub_C {ζ : ℂ} (hζ : ζ ≠ 0) :
    Polynomial.reflect 1 (X - Polynomial.C ζ) = Polynomial.C (-ζ) * (X - Polynomial.C ζ⁻¹) := by
  rw [reflect_sub, reflect_one_X, show (Polynomial.C ζ : Polynomial ℂ) = Polynomial.C ζ * X ^ 0 by
    rw [pow_zero, mul_one], reflect_C_mul_X_pow, revAt_le (by omega), pow_one]
  rw [mul_sub, ← Polynomial.C_mul, neg_mul, mul_inv_cancel₀ hζ]
  rw [show Polynomial.C (-(1 : ℂ)) = -1 by rw [Polynomial.C_neg, Polynomial.C_1],
    Polynomial.C_neg]
  ring

/-- Reflection of a product of monic linear factors over a multiset avoiding `0`:
each factor `X − C ζ` reflects to `C (−ζ)·(X − C ζ⁻¹)`. Proven by induction on the
multiset, using `reflect_mul` with the degree count `natDegree ∏ = card`. -/
private lemma reflect_multiset_prod_X_sub_C (S : Multiset ℂ) (h0 : (0 : ℂ) ∉ S) :
    Polynomial.reflect S.card ((S.map (fun ζ => X - Polynomial.C ζ)).prod)
      = (S.map (fun ζ => Polynomial.C (-ζ) * (X - Polynomial.C ζ⁻¹))).prod := by
  induction S using Multiset.induction with
  | empty => simp [Polynomial.reflect_one]
  | cons ζ S ih =>
    have hζ : ζ ≠ 0 := fun h => h0 (h ▸ Multiset.mem_cons_self ζ S)
    have h0' : (0 : ℂ) ∉ S := fun h => h0 (Multiset.mem_cons_of_mem h)
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
      Multiset.map_cons, Multiset.prod_cons]
    rw [show S.card + 1 = 1 + S.card by ring,
      reflect_mul (X - Polynomial.C ζ) ((S.map (fun ζ => X - Polynomial.C ζ)).prod)
        (by rw [natDegree_X_sub_C])
        (by rw [natDegree_multiset_prod_X_sub_C_eq_card])]
    rw [reflect_one_X_sub_C hζ, ih h0']

/-- `card roots = natDegree` for `q̃` (it splits over `ℂ`). -/
private lemma qtilde_roots_card_eq_natDegree (P : ℕ) :
    (qtilde P).roots.card = (qtilde P).natDegree :=
  Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)

/-- The full factorisation of `q̃` into linear factors over its roots:
`q̃ = C(1/(2P+2)²)·∏_{ζ∈roots}(X − C ζ)`. -/
private lemma qtilde_eq_C_lc_mul_prod (P : ℕ) :
    Polynomial.C (1 / (2 * (P : ℂ) + 2) ^ 2)
        * (((qtilde P).roots.map (fun ζ => X - Polynomial.C ζ)).prod)
      = qtilde P := by
  have h := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
    (qtilde_roots_card_eq_natDegree P)
  rwa [qtilde_leadingCoeff] at h

/-! ### §3.3 The four `exists_conj_split` hypotheses for `(qtilde P).roots` -/

/-- `q̃` splits over `ℂ` into `2L = 2(2P+1)` linear factors: its root multiset has
that cardinality. -/
theorem qtilde_roots_card (P : ℕ) : (qtilde P).roots.card = 2 * (2 * P + 1) := by
  rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _), qtilde_natDegree]

/-- The root multiset of `q̃` is conjugation-closed (real coefficients). -/
theorem qtilde_roots_map_conj (P : ℕ) :
    (qtilde P).roots.map (starRingEnd ℂ) = (qtilde P).roots := by
  rw [← Polynomial.Splits.roots_map (IsAlgClosed.splits (qtilde P)) (starRingEnd ℂ),
    qtilde_map_conj]

/-- `0` is not a root of `q̃`. -/
theorem zero_not_mem_qtilde_roots (P : ℕ) : (0 : ℂ) ∉ (qtilde P).roots := by
  intro h
  exact qtilde_root_ne_zero P (Polynomial.isRoot_of_mem_roots h) rfl

/-- **The inversion bridge.** The root multiset of `q̃` is inversion-closed. Reflecting
the linear factorisation `q̃ = C(lc)·∏(X − C ζ)` at degree `2L = card roots` (using
`reflect (2L) q̃ = q̃`) turns each factor `X − C ζ` into `C(−ζ)·(X − C ζ⁻¹)`; reading
off the resulting root multiset gives `roots = roots.map (·⁻¹)`. -/
theorem qtilde_roots_map_inv (P : ℕ) :
    (qtilde P).roots.map (·⁻¹) = (qtilde P).roots := by
  set rts := (qtilde P).roots with hrts
  have h0 : (0 : ℂ) ∉ rts := zero_not_mem_qtilde_roots P
  -- The nonzero constant `c := lc · ∏(−ζ)`.
  have hprodne : (rts.map (fun ζ => -ζ)).prod ≠ 0 := by
    apply Multiset.prod_ne_zero
    intro hmem
    rw [Multiset.mem_map] at hmem
    obtain ⟨ζ, hζ, hζ0⟩ := hmem
    exact h0 (by rw [show ζ = 0 by linear_combination -hζ0] at hζ; exact hζ)
  have hcard : rts.card = 2 * (2 * P + 1) := qtilde_roots_card P
  -- Reflect the factorisation.
  have hfac := qtilde_eq_C_lc_mul_prod P
  rw [← hrts] at hfac
  have hkey : qtilde P
      = Polynomial.C ((1 / (2 * (P : ℂ) + 2) ^ 2) * (rts.map (fun ζ => -ζ)).prod)
          * ((rts.map (·⁻¹)).map (fun w => X - Polynomial.C w)).prod := by
    conv_lhs => rw [← reflect_qtilde P, ← hfac]
    rw [reflect_C_mul, ← hcard, reflect_multiset_prod_X_sub_C rts h0]
    rw [Multiset.prod_map_mul, Multiset.map_map]
    rw [show (rts.map (fun ζ => Polynomial.C (-ζ))).prod
        = Polynomial.C ((rts.map (fun ζ => -ζ)).prod) by
      rw [← Multiset.prod_hom (rts.map (fun ζ => -ζ)) (Polynomial.C : ℂ →+* Polynomial ℂ),
        Multiset.map_map]; rfl]
    rw [Polynomial.C_mul]
    simp only [Function.comp]
    ring
  -- Read off the roots.
  have hroots : (qtilde P).roots = (rts.map (·⁻¹)) := by
    rw [hkey, roots_C_mul _ (by
      rw [one_div]; exact mul_ne_zero (inv_ne_zero (pow_ne_zero _ (two_P_add_two_ne_zero P)))
        hprodne), roots_multiset_prod_X_sub_C]
  exact hroots.symm

/-- Any root of `q̃` lying on the real axis or the unit circle equals `−1`. -/
theorem qtilde_axis_root_eq_neg_one (P : ℕ) {ζ : ℂ} (hroot : (qtilde P).IsRoot ζ)
    (haxis : ζ.im = 0 ∨ ‖ζ‖ = 1) : ζ = -1 := by
  rcases haxis with him | hcirc
  · -- real: ζ = ↑ζ.re, apply the real-root iff
    have hζeq : ζ = (ζ.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    rw [hζeq] at hroot ⊢
    rw [qtilde_real_root_iff] at hroot
    rw [hroot]; push_cast; ring
  · -- circle: ζ = exp(I·arg ζ), apply the circle-root iff
    have hζeq : ζ = Complex.exp (Complex.I * (ζ.arg : ℝ)) := by
      conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I ζ, hcirc]
      rw [Complex.ofReal_one, one_mul, mul_comm]
    rw [hζeq] at hroot
    rw [qtilde_circle_root_iff] at hroot
    rw [hζeq, hroot]

/-- The real-or-unit-circle part of `q̃`'s roots is exactly `{−1, −1}` (the double
root at `−1` is the unique on-axis root). -/
theorem qtilde_roots_filter_axis (P : ℕ) :
    (qtilde P).roots.filter (fun ζ => ζ.im = 0 ∨ ‖ζ‖ = 1) = {(-1 : ℂ), -1} := by
  classical
  refine Multiset.ext.mpr (fun a => ?_)
  rw [Multiset.count_filter]
  -- RHS: {-1, -1} = (-1) ::ₘ {-1}, count a = if a = -1 then 2 else 0
  rw [show ({(-1 : ℂ), -1} : Multiset ℂ) = (-1 : ℂ) ::ₘ (-1 : ℂ) ::ₘ 0 by rfl]
  rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero]
  by_cases ha : a = -1
  · -- a = -1: predicate holds (im = 0), count = rootMultiplicity = 2
    subst ha
    rw [if_pos (Or.inl (by simp))]
    rw [Polynomial.count_roots, qtilde_rootMultiplicity_neg_one]
    simp
  · -- a ≠ -1: RHS is 0; show LHS is 0 too.
    rw [show (0 + if a = -1 then 1 else 0) + (if a = -1 then (1 : ℕ) else 0) = 0 by
      rw [if_neg ha]]
    by_cases hpred : a.im = 0 ∨ ‖a‖ = 1
    · rw [if_pos hpred]
      -- a satisfies predicate but a ≠ -1, so a is not a root
      rw [Polynomial.count_roots, Polynomial.rootMultiplicity_eq_zero]
      intro hroot
      exact ha (qtilde_axis_root_eq_neg_one P hroot hpred)
    · rw [if_neg hpred]

/-! ### §3.4 The spectral factor `R` -/

/-- The four-hypothesis package: `(qtilde P).roots` admits an inversion-closed
conjugate split (Fejér–Riesz root selection applied to `q̃`). -/
theorem qtilde_roots_exists_conj_split (P : ℕ) :
    ∃ S₀ : Multiset ℂ, S₀.map (·⁻¹) = S₀ ∧
      (qtilde P).roots = S₀ + S₀.map (starRingEnd ℂ) :=
  exists_conj_split (qtilde P).roots (zero_not_mem_qtilde_roots P)
    (qtilde_roots_map_conj P) (qtilde_roots_map_inv P) (qtilde_roots_filter_axis P)

/-- A chosen inversion-closed spectral half of `(qtilde P).roots`. -/
def RpolyRootHalf (P : ℕ) : Multiset ℂ := (qtilde_roots_exists_conj_split P).choose

/-- `RpolyRootHalf P` is inversion-closed. -/
theorem RpolyRootHalf_map_inv (P : ℕ) : (RpolyRootHalf P).map (·⁻¹) = RpolyRootHalf P :=
  (qtilde_roots_exists_conj_split P).choose_spec.1

/-- `(qtilde P).roots` splits as `S₀ + S₀.map conj` for the chosen half `S₀`. -/
theorem qtilde_roots_eq_RpolyRootHalf (P : ℕ) :
    (qtilde P).roots = RpolyRootHalf P + (RpolyRootHalf P).map (starRingEnd ℂ) :=
  (qtilde_roots_exists_conj_split P).choose_spec.2

/-- The spectral factor `R := C(1/(2P+2))·∏_{ζ∈S₀}(X − C ζ)`. -/
def Rpoly (P : ℕ) : Polynomial ℂ :=
  Polynomial.C (1 / (2 * (P : ℂ) + 2)) *
    ((RpolyRootHalf P).map (fun ζ => X - Polynomial.C ζ)).prod

/-- The chosen spectral half is `≤` the full root multiset. -/
theorem RpolyRootHalf_le_roots (P : ℕ) : RpolyRootHalf P ≤ (qtilde P).roots := by
  rw [qtilde_roots_eq_RpolyRootHalf P]
  exact Multiset.le_add_right _ _

/-- `0` is not in the chosen spectral half. -/
theorem zero_not_mem_RpolyRootHalf (P : ℕ) : (0 : ℂ) ∉ RpolyRootHalf P :=
  fun h => zero_not_mem_qtilde_roots P (Multiset.mem_of_le (RpolyRootHalf_le_roots P) h)

/-- The chosen spectral half has cardinality `L = 2P+1` (half of `2L`). -/
theorem RpolyRootHalf_card (P : ℕ) : (RpolyRootHalf P).card = 2 * P + 1 := by
  have hcard := qtilde_roots_card P
  rw [qtilde_roots_eq_RpolyRootHalf P, Multiset.card_add, Multiset.card_map] at hcard
  omega

/-- `R` has natDegree exactly `L = 2P+1`. -/
theorem Rpoly_natDegree (P : ℕ) : (Rpoly P).natDegree = 2 * P + 1 := by
  unfold Rpoly
  rw [natDegree_C_mul (by
    rw [one_div]; exact inv_ne_zero (two_P_add_two_ne_zero P)),
    natDegree_multiset_prod_X_sub_C_eq_card, RpolyRootHalf_card]

/-- Mapping `conj` over a product of monic linear factors conjugates the roots:
`((S.map (X − C·)).prod).map conj = ((S.map conj).map (X − C·)).prod`. -/
private lemma map_conj_prod_X_sub_C (S : Multiset ℂ) :
    ((S.map (fun ζ => X - Polynomial.C ζ)).prod).map (starRingEnd ℂ)
      = ((S.map (starRingEnd ℂ)).map (fun ζ => X - Polynomial.C ζ)).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro ζ _
  simp [Polynomial.map_sub]

/-- `R̄ = R.map conj` in factored form: `R̄ = C(1/M)·∏_{ζ∈S₀.map conj}(X − C ζ)`
(the constant `1/M` is real, so `conj` fixes it). -/
theorem Rpoly_map_conj (P : ℕ) :
    (Rpoly P).map (starRingEnd ℂ)
      = Polynomial.C (1 / (2 * (P : ℂ) + 2))
          * (((RpolyRootHalf P).map (starRingEnd ℂ)).map (fun ζ => X - Polynomial.C ζ)).prod := by
  unfold Rpoly
  rw [Polynomial.map_mul, Polynomial.map_C, map_conj_prod_X_sub_C]
  congr 2
  rw [map_div₀, map_one]
  congr 1
  simp [map_add, map_mul, map_ofNat]

/-- **The Fejér–Riesz identity.** `R · R̄ = q̃ = X^L + T²`. The product of the two
half-factorisations recombines into the full root factorisation of `q̃`. -/
theorem Rpoly_mul_conj (P : ℕ) :
    (Rpoly P) * ((Rpoly P).map (starRingEnd ℂ)) = qtilde P := by
  rw [Rpoly_map_conj P]
  conv_lhs => unfold Rpoly
  rw [show ∀ A B C D : Polynomial ℂ, (A * B) * (C * D) = (A * C) * (B * D) from
    fun A B C D => by ring]
  rw [← Polynomial.C_mul, ← Multiset.prod_add, ← Multiset.map_add,
    ← qtilde_roots_eq_RpolyRootHalf P]
  rw [show (1 / (2 * (P : ℂ) + 2)) * (1 / (2 * (P : ℂ) + 2)) = 1 / (2 * (P : ℂ) + 2) ^ 2 by
    rw [div_mul_div_comm, one_mul, sq]]
  exact qtilde_eq_C_lc_mul_prod P

/-- `−1` appears exactly once in the chosen spectral half: its multiplicity `2` in
`q̃`'s roots splits evenly across `S₀` and `S₀.map conj` (since `conj(−1) = −1`). -/
theorem count_neg_one_RpolyRootHalf (P : ℕ) :
    Multiset.count (-1 : ℂ) (RpolyRootHalf P) = 1 := by
  classical
  have htot : Multiset.count (-1 : ℂ) (qtilde P).roots = 2 := by
    rw [Polynomial.count_roots, qtilde_rootMultiplicity_neg_one]
  rw [qtilde_roots_eq_RpolyRootHalf P, Multiset.count_add] at htot
  have hmap : Multiset.count (-1 : ℂ) ((RpolyRootHalf P).map (starRingEnd ℂ))
      = Multiset.count (-1 : ℂ) (RpolyRootHalf P) := by
    have key := Multiset.count_map_eq_count' (starRingEnd ℂ) (RpolyRootHalf P)
      (starRingEnd ℂ).injective (-1 : ℂ)
    rwa [show (starRingEnd ℂ) (-1 : ℂ) = -1 by simp] at key
  rw [hmap] at htot
  omega

/-- `−1 ∈ S₀`. -/
theorem neg_one_mem_RpolyRootHalf (P : ℕ) : (-1 : ℂ) ∈ RpolyRootHalf P := by
  rw [← Multiset.count_pos, count_neg_one_RpolyRootHalf P]; norm_num

/-- `R(−1) = 0` — the factor `(X − C(−1))` lies in `R`'s product. -/
theorem Rpoly_eval_neg_one (P : ℕ) : (Rpoly P).eval (-1) = 0 := by
  unfold Rpoly
  rw [eval_mul, eval_multiset_prod]
  rw [show ((RpolyRootHalf P).map (fun ζ => X - Polynomial.C ζ)).map (eval (-1 : ℂ))
      = (RpolyRootHalf P).map (fun ζ => eval (-1 : ℂ) (X - Polynomial.C ζ)) by
    rw [Multiset.map_map]; rfl]
  rw [Multiset.prod_eq_zero (by
    rw [Multiset.mem_map]
    exact ⟨-1, neg_one_mem_RpolyRootHalf P, by simp⟩)]
  ring

/-- `q̃(1) = 1 + T(1)² = 1 ≠ 0`, so `1` is not a root of `q̃`. -/
theorem one_not_mem_qtilde_roots (P : ℕ) : (1 : ℂ) ∉ (qtilde P).roots := by
  have heval : (qtilde P).eval 1 = 1 := by
    unfold qtilde
    rw [eval_add, eval_pow, eval_X, eval_pow, Tpoly_eval_one]
    ring
  intro h
  have hr : (qtilde P).eval 1 = 0 := Polynomial.isRoot_of_mem_roots h
  rw [heval] at hr
  exact one_ne_zero hr

/-- `1 ∉ S₀` (since `1` is not a root of `q̃` and `S₀ ≤ roots`). -/
theorem one_not_mem_RpolyRootHalf (P : ℕ) : (1 : ℂ) ∉ RpolyRootHalf P :=
  fun h => one_not_mem_qtilde_roots P (Multiset.mem_of_le (RpolyRootHalf_le_roots P) h)

/-- The inversion-pair `{ζ, ζ⁻¹}` is inversion-closed as a count function. -/
private lemma pair_inv_count (ζ : ℂ) (a : ℂ) :
    Multiset.count a⁻¹ ((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0) = Multiset.count a ((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0) := by
  classical
  have key := Multiset.count_map_eq_count' (fun x : ℂ => x⁻¹) ((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0)
    inv_injective a
  rwa [show (((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0).map (fun x => x⁻¹)) = (ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0 by
    simp only [Multiset.map_cons, Multiset.map_zero, inv_inv]
    exact Multiset.cons_swap _ _ _] at key

/-- **Sign-pinning mini-lemma.** A multiset of nonzero complexes that is inversion-closed
and has *no* inversion-fixed point has product `1`: the elements pair off as `ζ, ζ⁻¹`. -/
private lemma prod_eq_one_of_invclosed_no_fixed (S : Multiset ℂ)
    (h0 : (0 : ℂ) ∉ S) (hinv : S.map (·⁻¹) = S) (hnf : ∀ ζ ∈ S, ζ⁻¹ ≠ ζ) :
    S.prod = 1 := by
  classical
  -- count form of inv-closure
  have hinvc : ∀ a, S.count a⁻¹ = S.count a := by
    intro a
    have key := Multiset.count_map_eq_count' (fun x : ℂ => x⁻¹) S inv_injective a
    rwa [hinv] at key
  induction S using Multiset.strongInductionOn with
  | _ S ih =>
    by_cases hS : S = 0
    · rw [hS]; rfl
    · obtain ⟨ζ, hζS⟩ := Multiset.exists_mem_of_ne_zero hS
      have hζ0 : ζ ≠ 0 := fun h => h0 (h ▸ hζS)
      have hζinvne : ζ⁻¹ ≠ ζ := hnf ζ hζS
      have hζinvS : ζ⁻¹ ∈ S := by
        rw [← Multiset.count_pos, hinvc]; exact Multiset.count_pos.mpr hζS
      -- the pair `pr := ζ ::ₘ ζ⁻¹ ::ₘ 0` is `≤ S`.
      have hpr_le : (ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0 ≤ S := by
        rw [Multiset.le_iff_count]
        intro a
        rcases eq_or_ne a ζ with rfl | hne
        · -- a = ζ: first if (a=ζ) true, second if (a=ζ⁻¹) false
          rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero,
            if_pos rfl, if_neg (fun h => hζinvne h.symm)]
          simpa using Multiset.count_pos.mpr hζS
        · rcases eq_or_ne a ζ⁻¹ with rfl | hne2
          · -- a = ζ⁻¹: first if (a=ζ) false, second if (a=ζ⁻¹) true
            rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero,
              if_neg hne, if_pos rfl]
            simpa using Multiset.count_pos.mpr hζinvS
          · rw [Multiset.count_cons, Multiset.count_cons, Multiset.count_zero,
              if_neg hne, if_neg hne2]; omega
      set S' := S - ((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0) with hS'def
      have hsplit : S = ((ζ : ℂ) ::ₘ ζ⁻¹ ::ₘ 0) + S' := by
        rw [hS'def, add_comm, Multiset.sub_add_cancel hpr_le]
      -- S' is strictly smaller.
      have hlt : S' < S := by
        rw [hS'def]
        refine lt_of_le_of_ne (Multiset.sub_le_self S _) (fun heq => ?_)
        have hc := congrArg Multiset.card heq
        rw [Multiset.card_sub hpr_le] at hc
        simp only [Multiset.card_cons, Multiset.card_zero] at hc
        have : 0 < S.card := Multiset.card_pos.mpr hS
        omega
      -- re-establish hypotheses for S'.
      have h0' : (0 : ℂ) ∉ S' := fun h => h0 (Multiset.mem_of_le (Multiset.sub_le_self _ _) h)
      have hnf' : ∀ a ∈ S', a⁻¹ ≠ a := fun a ha => hnf a (Multiset.mem_of_le
        (Multiset.sub_le_self _ _) ha)
      have hinvc' : ∀ a, S'.count a⁻¹ = S'.count a := by
        intro a
        rw [hS'def, Multiset.count_sub, Multiset.count_sub, hinvc, pair_inv_count]
      have hinv' : S'.map (·⁻¹) = S' := by
        refine Multiset.ext.mpr (fun a => ?_)
        have key := Multiset.count_map_eq_count' (fun x : ℂ => x⁻¹) S' inv_injective a⁻¹
        rw [inv_inv] at key
        rw [key, hinvc']
      -- conclude.
      rw [hsplit, Multiset.prod_add, Multiset.prod_cons, Multiset.prod_cons,
        Multiset.prod_zero, mul_one, mul_inv_cancel₀ hζ0, one_mul]
      exact ih S' hlt h0' hinv' hnf' hinvc'

/-- An inversion-fixed complex number is `±1`. -/
private lemma inv_eq_self_iff {a : ℂ} (ha : a ≠ 0) : a⁻¹ = a ↔ a = 1 ∨ a = -1 := by
  rw [← mul_self_eq_one_iff]
  constructor
  · intro h
    field_simp at h
    linear_combination -h
  · intro h
    exact inv_eq_of_mul_eq_one_left h

/-- The count form of inversion-closure for the chosen spectral half. -/
theorem RpolyRootHalf_count_inv (P : ℕ) (a : ℂ) :
    Multiset.count a⁻¹ (RpolyRootHalf P) = Multiset.count a (RpolyRootHalf P) := by
  classical
  have key := Multiset.count_map_eq_count' (fun x : ℂ => x⁻¹) (RpolyRootHalf P) inv_injective a
  rwa [RpolyRootHalf_map_inv] at key

/-- **The sign-pinned product.** `∏_{ζ∈S₀} ζ = −1`: the lone inversion-fixed point in
`S₀` is `−1` (count 1), the rest pairs off to product `1`. -/
theorem RpolyRootHalf_prod_eq_neg_one (P : ℕ) : (RpolyRootHalf P).prod = -1 := by
  classical
  set S₀ := RpolyRootHalf P with hS₀
  -- peel the lone `−1`.
  have hmem : (-1 : ℂ) ∈ S₀ := neg_one_mem_RpolyRootHalf P
  set S₀' := S₀.erase (-1) with hS₀'
  have hcons : S₀ = (-1 : ℂ) ::ₘ S₀' := (Multiset.cons_erase hmem).symm
  -- count of −1 in the erased residue is 0.
  have hcount_neg : Multiset.count (-1 : ℂ) S₀' = 0 := by
    rw [hS₀', Multiset.count_erase_self, count_neg_one_RpolyRootHalf P]
  -- residue is inversion-closed.
  have hinv' : S₀'.map (·⁻¹) = S₀' := by
    refine Multiset.ext.mpr (fun a => ?_)
    have key := Multiset.count_map_eq_count' (fun x : ℂ => x⁻¹) S₀' inv_injective a⁻¹
    rw [inv_inv] at key
    rw [key]
    by_cases ha : a = -1
    · -- a = -1: a⁻¹ = -1, both counts equal trivially
      subst ha
      rw [show (-1 : ℂ)⁻¹ = -1 by norm_num]
    · -- a ≠ -1: a⁻¹ ≠ -1, erasing -1 doesn't affect either count
      have hainv : a⁻¹ ≠ -1 := by
        intro h
        exact ha (by rw [← inv_inv a, h]; norm_num)
      rw [hS₀', Multiset.count_erase_of_ne hainv, Multiset.count_erase_of_ne ha,
        RpolyRootHalf_count_inv P a]
  -- residue avoids 0.
  have h0' : (0 : ℂ) ∉ S₀' :=
    fun h => zero_not_mem_RpolyRootHalf P (Multiset.mem_of_mem_erase (hS₀' ▸ h))
  -- residue has no inversion-fixed point.
  have hnf' : ∀ a ∈ S₀', a⁻¹ ≠ a := by
    intro a ha hfix
    have ha0 : a ≠ 0 := fun h => h0' (h ▸ ha)
    rcases (inv_eq_self_iff ha0).mp hfix with h1 | h1
    · subst h1
      exact one_not_mem_RpolyRootHalf P (Multiset.mem_of_mem_erase (hS₀' ▸ ha))
    · subst h1
      rw [← Multiset.count_pos, hcount_neg] at ha
      exact Nat.lt_irrefl 0 ha
  -- assemble.
  rw [hcons, Multiset.prod_cons,
    prod_eq_one_of_invclosed_no_fixed S₀' h0' hinv' hnf', mul_one]

/-- **Palindromy of `R`.** `reflect L R = R` (`L = 2P+1`). Reflecting the factored
form turns each `X − C ζ` into `C(−ζ)·(X − C ζ⁻¹)`; inversion-closure of `S₀`
restores the same product, and the accumulated scalar `(1/M)·∏(−ζ) = (1/M)·(−1)^L·(−1)
= 1/M` is unchanged because `L` is odd and `∏_{S₀} ζ = −1`. -/
theorem reflect_Rpoly (P : ℕ) : Polynomial.reflect (2 * P + 1) (Rpoly P) = Rpoly P := by
  have h0 : (0 : ℂ) ∉ RpolyRootHalf P := zero_not_mem_RpolyRootHalf P
  -- the accumulated scalar `(1/M)·∏(−ζ) = 1/M`.
  have hscalar : (1 / (2 * (P : ℂ) + 2)) * ((RpolyRootHalf P).map (fun ζ => -ζ)).prod
      = 1 / (2 * (P : ℂ) + 2) := by
    rw [show (fun ζ : ℂ => -ζ) = Neg.neg from rfl, Multiset.prod_map_neg, RpolyRootHalf_card,
      RpolyRootHalf_prod_eq_neg_one]
    rw [show ((-1 : ℂ)) ^ (2 * P + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
    ring
  conv_rhs => unfold Rpoly
  unfold Rpoly
  rw [reflect_C_mul, ← RpolyRootHalf_card P, reflect_multiset_prod_X_sub_C _ h0,
    Multiset.prod_map_mul]
  rw [show ((RpolyRootHalf P).map (fun ζ => Polynomial.C (-ζ))).prod
      = Polynomial.C (((RpolyRootHalf P).map (fun ζ => -ζ)).prod) by
    rw [← Multiset.prod_hom ((RpolyRootHalf P).map (fun ζ => -ζ))
      (Polynomial.C : ℂ →+* Polynomial ℂ), Multiset.map_map]; rfl]
  -- collapse `S₀.map (·⁻¹) = S₀` inside the second product
  rw [show (RpolyRootHalf P).map (fun ζ : ℂ => X - Polynomial.C ζ⁻¹)
      = ((RpolyRootHalf P).map (·⁻¹)).map (fun ζ => X - Polynomial.C ζ) by
    rw [Multiset.map_map]; rfl, RpolyRootHalf_map_inv]
  rw [← mul_assoc, ← Polynomial.C_mul, hscalar]

/-! ### §3.4 capstone: class membership of `(R, T)` -/

/-- `Cstar L R = R.map conj` (via `reflect_map` + palindromy of `R`). -/
theorem Cstar_Rpoly (P : ℕ) :
    Cstar (2 * P + 1) (Rpoly P) = (Rpoly P).map (starRingEnd ℂ) := by
  unfold Cstar
  rw [reflect_map, reflect_Rpoly]

/-- `Cstar L T = −T` (via `Tpoly_map_conj` + antipalindromy of `T`). -/
theorem Cstar_Tpoly (P : ℕ) : Cstar (2 * P + 1) (Tpoly P) = -(Tpoly P) := by
  unfold Cstar
  rw [Tpoly_map_conj, reflect_Tpoly]

/-- **The §3.4 capstone.** The pair `(Rpoly P, Tpoly P)` is a member of the SU(2)
Laurent class at half-degree `L = 2P+1`. Consumed verbatim by `Angles.lean`. -/
theorem isClassL_R_T (P : ℕ) : IsClassL (2 * P + 1) (Rpoly P) (Tpoly P) where
  degA := le_of_eq (Rpoly_natDegree P)
  degB := le_of_eq (Tpoly_natDegree P)
  unitarity := by
    rw [Cstar_Rpoly, Cstar_Tpoly]
    rw [show (Tpoly P) * -(Tpoly P) = -(Tpoly P ^ 2) by ring]
    rw [Rpoly_mul_conj]
    unfold qtilde
    ring
  palinA := reflect_Rpoly P
  antiB := reflect_Tpoly P

end

end QAOA.IsingChain.Achievability
