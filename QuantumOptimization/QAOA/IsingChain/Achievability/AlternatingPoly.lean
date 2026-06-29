import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import QuantumOptimization.QAOA.IsingChain.Achievability.SinBound
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.Basic

/-!
# The alternating node polynomial `T`

The polynomial `T(w) = (1/(2P+2)) · (w^{2P+1} − w^{2P} + ⋯ + w − 1)`, i.e.
`(w+1)·T(w) = (w^{2P+2} − 1)/(2P+2)`. It is the unique (up to scalar)
anti-self-reciprocal polynomial of degree `2P+1` vanishing at all active QAOA
wavevector nodes `w_n = e^{i k_n}` (`k_n = (n+1)π/(P+1)`): its root set is exactly
the `(2P+2)`-th roots of unity except `−1`. The normalization `1/(2P+2)` — the
residual-energy constant — is forced downstream by `|T(−1)| = 1`.

## Main definitions
- `Tpoly P` — the alternating polynomial above (degree `2P+1`, complex coefficients).
- `TpolyRealNeg P ρ` — the real value `T(−ρ) = −(1/(2P+2)) Σ_{j<2P+2} ρ^j`.

## Main statements
- `X_add_one_mul_Tpoly` — `(X + 1) * T = C (1/(2P+2)) * (X^{2P+2} − 1)`.
- `Tpoly_coeff` — `T.coeff j = (−1)^{j+1}/(2P+2)` for `j ≤ 2P+1`.
- `Tpoly_eval_eq_zero` — `T(w) = 0` whenever `w^{2P+2} = 1` and `w ≠ −1`.
- `reflect_Tpoly` — anti-self-reciprocity `reflect (2P+1) T = −T`.
- `Tpoly_natDegree`, `Tpoly_ne_zero` — degree exactly `2P+1`.
- `Tpoly_eval_neg_real` — `T(−ρ) = −(1/(2P+2)) Σ_{j<2P+2} ρ^j` (negative real axis).
- `Tpoly_eval_neg_eq` — bridge `T(−ρ) = (TpolyRealNeg P ρ : ℂ)`.
- `Tpoly_eval_node` — `T` vanishes at every active node `w_n = e^{i k_n}`.
- `two_mul_pow_le_add_pow`, `two_mul_pow_lt_add_pow` — AM–GM pairing `2ρ^t ≤ ρ^s + ρ^{2t−s}`
  (and its strict form), integer exponents only.
- `sq_geom_sum_ge`, `sq_geom_sum_eq_iff` — `(2P+2)² ρ^{2P+1} ≤ (Σ_{j<2P+2} ρ^j)²`,
  equality iff `ρ = 1` (AM–GM on the squared geometric sum).
- `Tpoly_neg_sq_ge`, `Tpoly_neg_sq_eq_iff` — `ρ^{2P+1} ≤ T(−ρ)²`, equality iff `ρ = 1`.
- `norm_exp_mul_I_sub_one`, `norm_exp_mul_I_add_one` — `‖e^{iα} ∓ 1‖ = 2|sin(α/2)|`,
  `2|cos(α/2)|`.
- `Tpoly_abs_circle_lt_one` — circle sup-norm `‖T(e^{iθ})‖ < 1` for `θ ≠ π (mod 2π)`.
-/

namespace QAOA.IsingChain.Achievability

open Polynomial Finset

/-- Re-bind the `X` token to `Polynomial.X` at high priority. Importing
`JordanWigner.MomentumModes.Basic` (needed for the wave-vector nodes) transitively
brings `Quantum.Gates`' global `notation "X" => pauliX` into scope, which would
otherwise shadow `Polynomial.X`. This local notation restores the polynomial reading
throughout this file. -/
local notation (priority := high) "X" => Polynomial.X

noncomputable section

/-- The alternating node polynomial
`T = −(1/(2P+2)) · Σ_{j<2P+2} (−X)^j ∈ ℂ[X]`, with coefficients
`T.coeff j = (−1)^{j+1}/(2P+2)`. -/
def Tpoly (P : ℕ) : Polynomial ℂ :=
  -(C (1 / (2 * (P : ℂ) + 2)) * ∑ j ∈ range (2 * P + 2), (-X) ^ j)

/-- The denominator `2P+2` is a nonzero complex number. -/
lemma two_P_add_two_ne_zero (P : ℕ) : (2 * (P : ℂ) + 2) ≠ 0 := by
  intro h
  have h' : (2 * (P : ℝ) + 2) = 0 := by exact_mod_cast congrArg Complex.re h
  have : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
  linarith

/-- Defining identity: `(X + 1) * T = C (1/(2P+2)) * (X^{2P+2} − 1)`.
(The telescoping uses that `2P+2` is even: `(−X)^{2P+2} = X^{2P+2}`.) -/
theorem X_add_one_mul_Tpoly (P : ℕ) :
    (X + 1) * Tpoly P = C (1 / (2 * (P : ℂ) + 2)) * (X ^ (2 * P + 2) - 1) := by
  have hgeom := geom_sum_mul (-X : Polynomial ℂ) (2 * P + 2)
  -- hgeom : (Σ (−X)^i) * (−X − 1) = (−X)^(2P+2) − 1
  have heven : (-X : Polynomial ℂ) ^ (2 * P + 2) = X ^ (2 * P + 2) := by
    rw [neg_pow]
    have : (-1 : Polynomial ℂ) ^ (2 * P + 2) = 1 := by
      rw [show 2 * P + 2 = 2 * (P + 1) by ring, pow_mul]
      norm_num
    rw [this, one_mul]
  rw [heven] at hgeom
  -- (Σ (−X)^i) * (X + 1) = 1 − X^(2P+2)
  have hflip : (∑ i ∈ range (2 * P + 2), (-X : Polynomial ℂ) ^ i) * (X + 1)
      = 1 - X ^ (2 * P + 2) := by
    linear_combination (-1 : Polynomial ℂ) * hgeom
  unfold Tpoly
  calc (X + 1) * -(C (1 / (2 * (P : ℂ) + 2)) * ∑ j ∈ range (2 * P + 2), (-X) ^ j)
      = -(C (1 / (2 * (P : ℂ) + 2)) *
          ((∑ j ∈ range (2 * P + 2), (-X : Polynomial ℂ) ^ j) * (X + 1))) := by ring
    _ = -(C (1 / (2 * (P : ℂ) + 2)) * (1 - X ^ (2 * P + 2))) := by rw [hflip]
    _ = C (1 / (2 * (P : ℂ) + 2)) * (X ^ (2 * P + 2) - 1) := by ring

/-- `T` kills every `(2P+2)`-th root of unity other than `−1` (in particular all the
active wavevector nodes `w_n = e^{ik_n}`, and also `w = 1`). -/
theorem Tpoly_eval_eq_zero (P : ℕ) {w : ℂ} (hroot : w ^ (2 * P + 2) = 1)
    (hw : w ≠ -1) : (Tpoly P).eval w = 0 := by
  have h := congrArg (Polynomial.eval w) (X_add_one_mul_Tpoly P)
  simp only [eval_mul, eval_add, eval_X, eval_one, eval_C, eval_sub, eval_pow] at h
  rw [hroot, sub_self, mul_zero] at h
  have hw1 : w + 1 ≠ 0 := fun hc => hw (eq_neg_of_add_eq_zero_left hc)
  exact (mul_eq_zero.mp h).resolve_left hw1

/-- The `j`-th coefficient of the bare alternating geometric sum. -/
lemma alt_geom_sum_coeff (M : ℕ) (j : ℕ) :
    (∑ i ∈ range M, (-X : Polynomial ℂ) ^ i).coeff j
      = if j < M then (-1) ^ j else 0 := by
  rw [finset_sum_coeff]
  have hterm : ∀ i, ((-X : Polynomial ℂ) ^ i).coeff j
      = if j = i then ((-1 : ℂ)) ^ i else 0 := by
    intro i
    rw [show (-X : Polynomial ℂ) ^ i = C ((-1) ^ i) * X ^ i by
      rw [neg_pow]
      congr 1
      rw [map_pow, map_neg, map_one]]
    rw [coeff_C_mul, coeff_X_pow]
    by_cases hij : j = i
    · rw [if_pos hij, if_pos hij, mul_one]
    · rw [if_neg hij, if_neg hij, mul_zero]
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  by_cases hjM : j < M
  · rw [Finset.sum_ite_eq (range M) j (fun i => ((-1 : ℂ)) ^ i),
      if_pos (Finset.mem_range.mpr hjM), if_pos hjM]
  · rw [if_neg hjM]
    apply Finset.sum_eq_zero
    intro i hi
    have : j ≠ i := by
      have := Finset.mem_range.mp hi
      omega
    rw [if_neg this]

/-- Coefficient formula: `T.coeff j = (−1)^{j+1}/(2P+2)` for `j < 2P+2`. -/
theorem Tpoly_coeff (P : ℕ) {j : ℕ} (hj : j < 2 * P + 2) :
    (Tpoly P).coeff j = (-1) ^ (j + 1) / (2 * (P : ℂ) + 2) := by
  unfold Tpoly
  rw [coeff_neg, coeff_C_mul, alt_geom_sum_coeff, if_pos hj, pow_succ]
  have h2 := two_P_add_two_ne_zero P
  field_simp

/-- Coefficients vanish above the degree bound. -/
theorem Tpoly_coeff_of_le (P : ℕ) {j : ℕ} (hj : 2 * P + 2 ≤ j) :
    (Tpoly P).coeff j = 0 := by
  unfold Tpoly
  rw [coeff_neg, coeff_C_mul, alt_geom_sum_coeff, if_neg (by omega), mul_zero, neg_zero]

/-- `T` has natDegree exactly `2P+1`. -/
theorem Tpoly_natDegree (P : ℕ) : (Tpoly P).natDegree = 2 * P + 1 := by
  have hlead : (Tpoly P).coeff (2 * P + 1) ≠ 0 := by
    rw [Tpoly_coeff P (by omega)]
    have h2 := two_P_add_two_ne_zero P
    intro hc
    rw [div_eq_zero_iff] at hc
    rcases hc with hc | hc
    · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) hc
    · exact h2 hc
  have hle : (Tpoly P).natDegree ≤ 2 * P + 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro j hj
    exact Tpoly_coeff_of_le P (by omega)
  have hge : 2 * P + 1 ≤ (Tpoly P).natDegree := le_natDegree_of_ne_zero hlead
  omega

/-- `T ≠ 0`. -/
theorem Tpoly_ne_zero (P : ℕ) : Tpoly P ≠ 0 := by
  intro hc
  have := Tpoly_coeff P (j := 2 * P + 1) (by omega)
  rw [hc] at this
  simp only [coeff_zero] at this
  have h2 := two_P_add_two_ne_zero P
  rw [eq_comm, div_eq_zero_iff] at this
  rcases this with hc' | hc'
  · exact pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0) hc'
  · exact h2 hc'

/-- Anti-self-reciprocity: `reflect (2P+1) T = −T`. -/
theorem reflect_Tpoly (P : ℕ) : (Tpoly P).reflect (2 * P + 1) = -(Tpoly P) := by
  ext j
  rw [coeff_reflect, coeff_neg]
  rcases lt_or_ge j (2 * P + 2) with hj | hj
  · -- in range: revAt maps j ↦ 2P+1−j, and the alternating sign flips
    have hrev : (revAt (2 * P + 1) j : ℕ) = 2 * P + 1 - j := by
      rw [revAt_le (by omega)]
    rw [hrev, Tpoly_coeff P (by omega), Tpoly_coeff P hj]
    have hsign : ((-1 : ℂ)) ^ (2 * P + 1 - j + 1) = -((-1) ^ (j + 1)) := by
      have hexp : 2 * P + 1 - j + 1 + (j + 1) = 2 * P + 2 + 1 - 0 := by omega
      have h1 : ((-1 : ℂ)) ^ (2 * P + 1 - j + 1) * ((-1 : ℂ)) ^ (j + 1)
          = ((-1 : ℂ)) ^ (2 * P + 3) := by
        rw [← pow_add]
        congr 1
      have h2 : ((-1 : ℂ)) ^ (2 * P + 3) = -1 := by
        rw [show 2 * P + 3 = 2 * (P + 1) + 1 by ring, pow_succ, pow_mul]
        norm_num
      have hsq : ((-1 : ℂ)) ^ (j + 1) * ((-1 : ℂ)) ^ (j + 1) = 1 := by
        rw [← pow_add, show j + 1 + (j + 1) = 2 * (j + 1) by ring, pow_mul]
        norm_num
      calc ((-1 : ℂ)) ^ (2 * P + 1 - j + 1)
          = ((-1 : ℂ)) ^ (2 * P + 1 - j + 1) * (((-1 : ℂ)) ^ (j + 1) * ((-1 : ℂ)) ^ (j + 1)) := by
            rw [hsq, mul_one]
        _ = (((-1 : ℂ)) ^ (2 * P + 1 - j + 1) * ((-1 : ℂ)) ^ (j + 1)) * ((-1 : ℂ)) ^ (j + 1) := by
            ring
        _ = -((-1) ^ (j + 1)) := by rw [h1, h2]; ring
    rw [hsign, neg_div]
  · -- above range: both sides vanish
    have hrev : revAt (2 * P + 1) j = j := by
      apply revAt_eq_self_of_lt
      omega
    rw [hrev, Tpoly_coeff_of_le P hj, neg_zero]

/-- `T(1) = 0` — the coefficient sum vanishes (the class-forced `b₀(1) = 0`). -/
theorem Tpoly_eval_one (P : ℕ) : (Tpoly P).eval 1 = 0 :=
  Tpoly_eval_eq_zero P (one_pow _) (by norm_num)

/-- `T` has real coefficients: conjugating coefficients fixes it. -/
theorem Tpoly_map_conj (P : ℕ) : (Tpoly P).map (starRingEnd ℂ) = Tpoly P := by
  ext j
  rw [coeff_map]
  rcases lt_or_ge j (2 * P + 2) with hj | hj
  · rw [Tpoly_coeff P hj, map_div₀, map_pow, map_neg, map_one]
    congr 1
    simp [map_add, map_mul, map_ofNat]
  · rw [Tpoly_coeff_of_le P hj, map_zero]

/-- The coefficients of `T` are real. -/
theorem Tpoly_coeff_real (P : ℕ) (j : ℕ) : ((Tpoly P).coeff j).im = 0 := by
  have h := congrArg (fun p => Polynomial.coeff p j) (Tpoly_map_conj P)
  simp only [coeff_map] at h
  have him := congrArg Complex.im h
  simp only [Complex.conj_im] at him
  linarith

/-- Evaluation on the negative real axis: `T(−ρ) = −(1/(2P+2)) Σ_{j<2P+2} ρ^j`
(as complex numbers, `ρ : ℝ`). -/
theorem Tpoly_eval_neg_real (P : ℕ) (ρ : ℝ) :
    (Tpoly P).eval (-(ρ : ℂ)) =
      -((1 / (2 * (P : ℂ) + 2)) * ∑ j ∈ range (2 * P + 2), (ρ : ℂ) ^ j) := by
  unfold Tpoly
  rw [eval_neg, eval_mul, eval_C, eval_finset_sum]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [eval_pow, eval_neg, eval_X, neg_neg]

/-- The real value of `T` on the negative real axis:
`T(−ρ) = −(1/(2P+2)) Σ_{j<2P+2} ρ^j` packaged as a real number. -/
def TpolyRealNeg (P : ℕ) (ρ : ℝ) : ℝ :=
  -(1 / (2 * (P : ℝ) + 2) * ∑ j ∈ range (2 * P + 2), ρ ^ j)

/-- Bridge: the complex evaluation `T(−ρ)` is the real number `TpolyRealNeg P ρ`. -/
theorem Tpoly_eval_neg_eq (P : ℕ) (ρ : ℝ) :
    (Tpoly P).eval (-(ρ : ℂ)) = ((TpolyRealNeg P ρ : ℝ) : ℂ) := by
  rw [Tpoly_eval_neg_real, TpolyRealNeg]
  push_cast
  ring

/-- AM–GM pairing (integer exponents): `2 ρ^t ≤ ρ^s + ρ^(2t−s)` for `ρ > 0`, `s ≤ t`.
The defect is `ρ^s · (1 − ρ^(t−s))² ≥ 0`. -/
theorem two_mul_pow_le_add_pow {ρ : ℝ} (hρ : 0 < ρ) {s t : ℕ} (hst : s ≤ t) :
    2 * ρ ^ t ≤ ρ ^ s + ρ ^ (2 * t - s) := by
  have hd : ρ ^ (2 * t - s) = ρ ^ s * (ρ ^ (t - s)) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have ht : ρ ^ t = ρ ^ s * ρ ^ (t - s) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hd, ht]
  nlinarith [sq_nonneg (1 - ρ ^ (t - s)), pow_pos hρ s]

/-- Strict AM–GM pairing: when `ρ ≠ 1` and `s < t`, the inequality is strict. -/
theorem two_mul_pow_lt_add_pow {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {s t : ℕ}
    (hst : s < t) : 2 * ρ ^ t < ρ ^ s + ρ ^ (2 * t - s) := by
  have hd : ρ ^ (2 * t - s) = ρ ^ s * (ρ ^ (t - s)) ^ 2 := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have ht : ρ ^ t = ρ ^ s * ρ ^ (t - s) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hd, ht]
  -- the square is strictly positive: ρ^(t−s) ≠ 1 since ρ ≠ 1 and t − s ≥ 1
  have hne : ρ ^ (t - s) ≠ 1 := by
    intro hc
    have hpos : 0 < t - s := by omega
    rcases lt_trichotomy ρ 1 with h | h | h
    · exact absurd hc (ne_of_lt (pow_lt_one₀ hρ.le h (by omega)))
    · exact hρ1 h
    · exact absurd hc (ne_of_gt (one_lt_pow₀ h (by omega)))
  have hsq : 0 < (1 - ρ ^ (t - s)) ^ 2 := by
    apply sq_pos_of_ne_zero
    intro hc
    apply hne
    linarith [sub_eq_zero.mp hc]
  nlinarith [hsq, pow_pos hρ s]

/-- Symmetric AM–GM pairing: `2 ρ^t ≤ ρ^a + ρ^b` whenever `a + b = 2t`. -/
theorem two_mul_pow_le_add_pow_of_add {ρ : ℝ} (hρ : 0 < ρ) {a b t : ℕ}
    (hab : a + b = 2 * t) : 2 * ρ ^ t ≤ ρ ^ a + ρ ^ b := by
  rcases le_total a b with h | h
  · have hb : 2 * t - a = b := by omega
    have := two_mul_pow_le_add_pow hρ (s := a) (t := t) (by omega)
    rw [hb] at this
    exact this
  · have hb : 2 * t - b = a := by omega
    have := two_mul_pow_le_add_pow hρ (s := b) (t := t) (by omega)
    rw [hb] at this
    linarith

/-- **The squared geometric-sum AM–GM bound (RISK #2).** For `ρ > 0`,
`(2P+2)² ρ^{2P+1} ≤ (Σ_{j<2P+2} ρ^j)²`. The clean route: expand the square into the
ordered double sum `Σ_{i,j} ρ^{i+j}`, average against its reflection `(i,j) ↦
(M−1−i, M−1−j)` (so paired exponents sum to `2(M−1)`), then apply the symmetric
AM–GM pairing termwise. -/
theorem sq_geom_sum_ge (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (2 * P + 2 : ℝ) ^ 2 * ρ ^ (2 * P + 1) ≤ (∑ j ∈ range (2 * P + 2), ρ ^ j) ^ 2 := by
  set M := 2 * P + 2 with hM
  have hML : M - 1 = 2 * P + 1 := by omega
  have hexpand : (∑ j ∈ range M, ρ ^ j) ^ 2 = ∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j) := by
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pow_add]
  have hrefl : (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j))
      = ∑ i ∈ range M, ∑ j ∈ range M, ρ ^ ((M - 1 - i) + (M - 1 - j)) := by
    rw [← Finset.sum_range_reflect (fun i => ∑ j ∈ range M, ρ ^ (i + j)) M]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_range_reflect (fun j => ρ ^ ((M - 1 - i) + j)) M]
  have hcard : (range M).card = M := Finset.card_range M
  have hsum2 : 2 * (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j))
      = ∑ i ∈ range M, ∑ j ∈ range M, (ρ ^ (i + j) + ρ ^ ((M - 1 - i) + (M - 1 - j))) := by
    rw [two_mul]
    nth_rewrite 2 [hrefl]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_add_distrib]
  have hge : (M : ℝ) ^ 2 * (2 * ρ ^ (M - 1))
      ≤ ∑ i ∈ range M, ∑ j ∈ range M, (ρ ^ (i + j) + ρ ^ ((M - 1 - i) + (M - 1 - j))) := by
    calc (M : ℝ) ^ 2 * (2 * ρ ^ (M - 1))
        = ∑ _i ∈ range M, ∑ _j ∈ range M, (2 * ρ ^ (M - 1)) := by
          simp only [Finset.sum_const, hcard, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ range M, ∑ j ∈ range M, (ρ ^ (i + j) + ρ ^ ((M - 1 - i) + (M - 1 - j))) := by
          refine Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => ?_))
          rw [Finset.mem_range] at hi hj
          exact two_mul_pow_le_add_pow_of_add hρ (by omega)
  -- combine: M²·(2ρ^(M-1)) ≤ 2·ΣΣ ⟹ M²·ρ^(M-1) ≤ ΣΣ = (Σ)²
  rw [← hsum2] at hge
  have hMcast : (M : ℝ) = 2 * (P : ℝ) + 2 := by push_cast [hM]; ring
  rw [hMcast] at hge
  rw [hexpand, ← hML]
  nlinarith [hge]

/-- Equality in `sq_geom_sum_ge` holds exactly at `ρ = 1`. -/
theorem sq_geom_sum_eq_iff (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∑ j ∈ range (2 * P + 2), ρ ^ j) ^ 2 = (2 * P + 2 : ℝ) ^ 2 * ρ ^ (2 * P + 1) ↔ ρ = 1 := by
  constructor
  · intro heq
    by_contra hρ1
    -- if ρ ≠ 1, the strict bound on the (0,0) term contradicts equality
    set M := 2 * P + 2 with hM
    have hML : M - 1 = 2 * P + 1 := by omega
    have hexpand : (∑ j ∈ range M, ρ ^ j) ^ 2
        = ∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j) := by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_add]
    have hrefl : (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j))
        = ∑ i ∈ range M, ∑ j ∈ range M, ρ ^ ((M - 1 - i) + (M - 1 - j)) := by
      rw [← Finset.sum_range_reflect (fun i => ∑ j ∈ range M, ρ ^ (i + j)) M]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_range_reflect (fun j => ρ ^ ((M - 1 - i) + j)) M]
    have hcard : (range M).card = M := Finset.card_range M
    have hsum2 : 2 * (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j))
        = ∑ i ∈ range M, ∑ j ∈ range M, (ρ ^ (i + j) + ρ ^ ((M - 1 - i) + (M - 1 - j))) := by
      rw [two_mul]
      nth_rewrite 2 [hrefl]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_add_distrib]
    set F : ℕ → ℝ := fun i => ∑ j ∈ range M, (ρ ^ (i + j) + ρ ^ ((M - 1 - i) + (M - 1 - j)))
      with hF
    set G : ℕ → ℝ := fun _i => ∑ _j ∈ range M, (2 * ρ ^ (M - 1)) with hG
    have hle_outer : ∀ i ∈ range M, G i ≤ F i := by
      intro i hi
      rw [Finset.mem_range] at hi
      exact Finset.sum_le_sum (fun j hj => by
        rw [Finset.mem_range] at hj
        exact two_mul_pow_le_add_pow_of_add hρ (by omega))
    have hlt_at0 : G 0 < F 0 := by
      rw [hF, hG]
      refine Finset.sum_lt_sum (fun j hj => ?_) ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
      · rw [Finset.mem_range] at hj
        exact two_mul_pow_le_add_pow_of_add hρ (by omega)
      · have he1 : (0 : ℕ) + 0 = 0 := by omega
        have he2 : (M - 1 - 0) + (M - 1 - 0) = 2 * (M - 1) - 0 := by omega
        rw [he1, he2]
        exact two_mul_pow_lt_add_pow hρ hρ1 (by omega : (0 : ℕ) < M - 1)
    have hstrict : ∑ i ∈ range M, G i < ∑ i ∈ range M, F i :=
      Finset.sum_lt_sum hle_outer ⟨0, Finset.mem_range.mpr (by omega), hlt_at0⟩
    have hGval : ∑ i ∈ range M, G i = (M : ℝ) ^ 2 * (2 * ρ ^ (M - 1)) := by
      rw [hG]; simp only [Finset.sum_const, hcard, nsmul_eq_mul]; ring
    have hFval : ∑ i ∈ range M, F i = 2 * (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j)) :=
      hsum2.symm
    rw [hGval, hFval, hML] at hstrict
    -- hstrict : M² (2 ρ^{2P+1}) < 2 ΣΣ;  heq + hexpand give ΣΣ = M² ρ^{2P+1}
    have hSS : (∑ i ∈ range M, ∑ j ∈ range M, ρ ^ (i + j)) = (M : ℝ) ^ 2 * ρ ^ (2 * P + 1) := by
      rw [← hexpand, heq]; push_cast [hM]; ring
    rw [hSS] at hstrict
    nlinarith [hstrict]
  · intro hρ1
    subst hρ1
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    push_cast
    ring

/-- `T` vanishes at every active wavevector node `w_n = e^{i k_n}`
(`k_n = waveVectorABC P n`): the nodes are `(2P+2)`-th roots of unity other than `−1`. -/
theorem Tpoly_eval_node (P : ℕ) (n : Fin P) :
    (Tpoly P).eval
      (Complex.exp (Complex.I * (JordanWigner.waveVectorABC P n : ℝ))) = 0 := by
  apply Tpoly_eval_eq_zero
  · -- `(e^{i k_n})^{2P+2} = 1`: the within-pair / combination root-of-unity fact
    have h := JordanWigner.exp_combo_root P n n 1 0
    simp only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero] at h
    exact h
  · -- `e^{i k_n} ≠ −1`, since `0 < k_n < π`
    intro hc
    have hdiff : Complex.exp
        (Complex.I * (JordanWigner.waveVectorABC P n : ℝ) - (Real.pi : ℝ) * Complex.I) = 1 := by
      rw [Complex.exp_sub, hc, Complex.exp_pi_mul_I]; norm_num
    rw [Complex.exp_eq_one_iff] at hdiff
    obtain ⟨m, hm⟩ := hdiff
    -- cancel `I`: `k_n − π = 2π m`
    have hcancel : (JordanWigner.waveVectorABC P n : ℂ) - (Real.pi : ℂ)
        = (m : ℂ) * (2 * Real.pi) := by
      have h2 : Complex.I * ((JordanWigner.waveVectorABC P n : ℝ) - (Real.pi : ℝ))
          = Complex.I * ((m : ℂ) * (2 * Real.pi)) := by linear_combination hm
      exact mul_left_cancel₀ Complex.I_ne_zero h2
    have hR : (JordanWigner.waveVectorABC P n) - Real.pi = (m : ℝ) * (2 * Real.pi) := by
      exact_mod_cast hcancel
    -- `0 < k_n < π`
    have h0 : 0 < JordanWigner.waveVectorABC P n := by
      unfold JordanWigner.waveVectorABC
      have hn : (0 : ℝ) ≤ (n.val : ℝ) := Nat.cast_nonneg _
      positivity
    have hpiub : JordanWigner.waveVectorABC P n < Real.pi := by
      unfold JordanWigner.waveVectorABC
      have hPpos : (0 : ℝ) < 2 * (P : ℝ) + 2 := by positivity
      rw [div_lt_iff₀ hPpos]
      have hnP : (n.val : ℝ) < (P : ℝ) := by exact_mod_cast n.isLt
      nlinarith [Real.pi_pos, hnP]
    have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
    -- `k_n − π = 2π m ∈ (−π, 0)` forces `m = 0`, impossible
    have hub : (m : ℝ) * (2 * Real.pi) < 0 := by nlinarith [hR, hpiub]
    have hlb : -Real.pi < (m : ℝ) * (2 * Real.pi) := by nlinarith [hR, h0]
    have hmle : m ≤ 0 := by
      by_contra h
      push_neg at h
      have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
      nlinarith [hub, hpi]
    have hmge : 0 ≤ m := by
      by_contra h
      push_neg at h
      have : (m : ℝ) ≤ -1 := by exact_mod_cast (by omega : m ≤ -1)
      nlinarith [hlb, hpi]
    have hm0 : m = 0 := by omega
    rw [hm0] at hub
    simp at hub

/-- On the negative real axis, `T(−ρ)² ≥ ρ^{2P+1}` for `ρ > 0`. (Follows from
`sq_geom_sum_ge` since `T(−ρ)² = (Σ ρ^j)²/(2P+2)²`.) -/
theorem Tpoly_neg_sq_ge (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ρ ^ (2 * P + 1) ≤ (TpolyRealNeg P ρ) ^ 2 := by
  have hsq := sq_geom_sum_ge P hρ
  have hM2 : (0 : ℝ) < (2 * P + 2 : ℝ) ^ 2 := by positivity
  have hT : (TpolyRealNeg P ρ) ^ 2
      = (∑ j ∈ range (2 * P + 2), ρ ^ j) ^ 2 / (2 * P + 2 : ℝ) ^ 2 := by
    rw [TpolyRealNeg, neg_sq, mul_pow, div_pow, one_pow]
    field_simp
  rw [hT, le_div_iff₀ hM2]
  nlinarith [hsq]

/-- Equality `T(−ρ)² = ρ^{2P+1}` holds exactly at `ρ = 1`. -/
theorem Tpoly_neg_sq_eq_iff (P : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (TpolyRealNeg P ρ) ^ 2 = ρ ^ (2 * P + 1) ↔ ρ = 1 := by
  have hM2 : (0 : ℝ) < (2 * P + 2 : ℝ) ^ 2 := by positivity
  have hT : (TpolyRealNeg P ρ) ^ 2
      = (∑ j ∈ range (2 * P + 2), ρ ^ j) ^ 2 / (2 * P + 2 : ℝ) ^ 2 := by
    rw [TpolyRealNeg, neg_sq, mul_pow, div_pow, one_pow]
    field_simp
  rw [hT, div_eq_iff (ne_of_gt hM2), ← sq_geom_sum_eq_iff P hρ]
  constructor
  · intro h; linarith [h]
  · intro h; linarith [h]

/-- `‖e^{iα} − 1‖ = 2|sin(α/2)|`: factor `e^{iα} − 1 = e^{iα/2}(e^{iα/2} − e^{−iα/2})
= e^{iα/2}·2i·sin(α/2)` and take norms. -/
theorem norm_exp_mul_I_sub_one (α : ℝ) :
    ‖Complex.exp (Complex.I * (α : ℝ)) - 1‖ = 2 * |Real.sin (α / 2)| := by
  set h := (α / 2 : ℝ) with hh
  have hfac : Complex.exp (Complex.I * (α : ℝ)) - 1
      = Complex.exp (Complex.I * (h : ℝ))
        * (Complex.exp ((h : ℝ) * Complex.I) - Complex.exp (-((h : ℝ) * Complex.I))) := by
    rw [mul_sub, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1; rw [hh]; push_cast; ring
    · rw [show Complex.I * (h : ℝ) + -((h : ℝ) * Complex.I) = 0 by ring, Complex.exp_zero]
  rw [hfac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hval : Complex.exp ((h : ℝ) * Complex.I) - Complex.exp (-((h : ℝ) * Complex.I))
      = (2 * (Real.sin h : ℂ)) * Complex.I := by
    have h2 := Complex.two_sin (h : ℂ)
    rw [show Complex.sin (h : ℂ) = (Real.sin h : ℂ) by rw [← Complex.ofReal_sin]] at h2
    rw [show (-(h : ℂ) * Complex.I) = -((h : ℂ) * Complex.I) by ring] at h2
    have hIsq : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (-Complex.I) * h2
      + (Complex.exp ((h : ℝ) * Complex.I) - Complex.exp (-((h : ℝ) * Complex.I))) * hIsq
  rw [hval, norm_mul, Complex.norm_I, mul_one, norm_mul,
    show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- `‖e^{iα} + 1‖ = 2|cos(α/2)|`: factor `e^{iα} + 1 = e^{iα/2}(e^{iα/2} + e^{−iα/2})
= e^{iα/2}·2·cos(α/2)` and take norms. -/
theorem norm_exp_mul_I_add_one (α : ℝ) :
    ‖Complex.exp (Complex.I * (α : ℝ)) + 1‖ = 2 * |Real.cos (α / 2)| := by
  set h := (α / 2 : ℝ) with hh
  have hfac : Complex.exp (Complex.I * (α : ℝ)) + 1
      = Complex.exp (Complex.I * (h : ℝ))
        * (Complex.exp ((h : ℝ) * Complex.I) + Complex.exp (-((h : ℝ) * Complex.I))) := by
    rw [mul_add, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1; rw [hh]; push_cast; ring
    · rw [show Complex.I * (h : ℝ) + -((h : ℝ) * Complex.I) = 0 by ring, Complex.exp_zero]
  rw [hfac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hval : Complex.exp ((h : ℝ) * Complex.I) + Complex.exp (-((h : ℝ) * Complex.I))
      = (2 * (Real.cos h : ℂ)) := by
    have h2 := Complex.two_cos (h : ℂ)
    rw [show Complex.cos (h : ℂ) = (Real.cos h : ℂ) by rw [← Complex.ofReal_cos]] at h2
    rw [show (-(h : ℂ) * Complex.I) = -((h : ℂ) * Complex.I) by ring] at h2
    exact h2.symm
  rw [hval, norm_mul, show ((2 : ℂ)) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]

/-- Reflection identity used to fold the numerator phase: for `M = 2P+2` (even),
`|sin(M·(π/2 − x))| = |sin(M·x)|`. (Since `M·(π/2 − x) = (P+1)π − M·x` and
`sin((P+1)π − y) = ±sin y`.) -/
theorem abs_sin_node_id (P : ℕ) (x : ℝ) :
    |Real.sin (((2 * P + 2 : ℕ) : ℝ) * (Real.pi / 2 - x))|
      = |Real.sin (((2 * P + 2 : ℕ) : ℝ) * x)| := by
  have hM : ((2 * P + 2 : ℕ) : ℝ) * (Real.pi / 2 - x)
      = ((P + 1 : ℕ) : ℝ) * Real.pi - ((2 * P + 2 : ℕ) : ℝ) * x := by push_cast; ring
  rw [hM, Real.sin_sub, Real.sin_nat_mul_pi, Real.cos_nat_mul_pi,
    zero_mul, zero_sub, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]

/-- **Circle sup-norm bound.** Away from `θ = π (mod 2π)`, `‖T(e^{iθ})‖ < 1`.
From `(w+1)·T(w) = (1/M)(w^M − 1)` (`w = e^{iθ}`, `M = 2P+2`):
`‖T(w)‖ = ‖w^M − 1‖/(M‖w+1‖) = |sin(Mθ/2)|/(M|cos(θ/2)|)`, and the strict multiple-angle
bound `|sin(M·x)| < M|sin x|` (`x = π/2 − θ/2`, `sin x = cos(θ/2) ≠ 0`) gives `< 1`. -/
theorem Tpoly_abs_circle_lt_one (P : ℕ) {θ : ℝ}
    (hθ : Complex.exp (Complex.I * θ) ≠ -1) :
    ‖(Tpoly P).eval (Complex.exp (Complex.I * θ))‖ < 1 := by
  set w := Complex.exp (Complex.I * (θ : ℝ)) with hw
  -- `cos(θ/2) ≠ 0`, else `‖w+1‖ = 0` so `w = −1`.
  have hcos : Real.cos (θ / 2) ≠ 0 := by
    intro hc
    apply hθ
    have hnorm : ‖w + 1‖ = 0 := by rw [norm_exp_mul_I_add_one, hc]; simp
    rw [norm_eq_zero] at hnorm
    rw [hw]
    exact add_eq_zero_iff_eq_neg.mp hnorm
  -- `(w+1)·T(w) = (1/M)(w^M − 1)`.
  have hkey := congrArg (Polynomial.eval w) (X_add_one_mul_Tpoly P)
  simp only [eval_mul, eval_add, eval_X, eval_one, eval_C, eval_sub, eval_pow] at hkey
  have hwM : w ^ (2 * P + 2)
      = Complex.exp (Complex.I * ((((2 * P + 2 : ℕ) : ℝ) * θ : ℝ) : ℂ)) := by
    rw [hw, ← Complex.exp_nat_mul]; congr 1; push_cast; ring
  have hMpos : (0 : ℝ) < ((2 * P + 2 : ℕ) : ℝ) := by positivity
  have hconstnorm : ‖(1 / (2 * (P : ℂ) + 2))‖ = 1 / ((2 * P + 2 : ℕ) : ℝ) := by
    rw [norm_div, norm_one]
    congr 1
    rw [show (2 * (P : ℂ) + 2) = (((2 * P + 2 : ℕ) : ℝ) : ℂ) by push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnormeq : ‖w + 1‖ * ‖(Tpoly P).eval w‖
      = (1 / ((2 * P + 2 : ℕ) : ℝ)) * ‖w ^ (2 * P + 2) - 1‖ := by
    have hn := congrArg norm hkey
    rw [norm_mul, norm_mul, hconstnorm] at hn
    exact hn
  rw [norm_exp_mul_I_add_one, hwM, norm_exp_mul_I_sub_one] at hnormeq
  -- substitute `x = π/2 − θ/2`: `cos(θ/2) = sin x`, `|sin(Mθ/2)| = |sin(M x)|`.
  set x := Real.pi / 2 - θ / 2 with hx
  have hcosx : Real.cos (θ / 2) = Real.sin x := by rw [hx, Real.sin_pi_div_two_sub]
  have hsinx : Real.sin x ≠ 0 := by rw [← hcosx]; exact hcos
  have hθx : θ / 2 = Real.pi / 2 - x := by rw [hx]; ring
  have hMθ : (((2 * P + 2 : ℕ) : ℝ) * θ : ℝ) / 2 = ((2 * P + 2 : ℕ) : ℝ) * (Real.pi / 2 - x) := by
    rw [← hθx]; ring
  rw [hMθ, abs_sin_node_id, hcosx] at hnormeq
  -- `hnormeq : 2|sin x|·‖T‖ = (1/M)(2|sin(M x)|)`; the strict bound finishes it.
  have hstrict := abs_sin_nat_mul_lt (n := 2 * P + 2) (by omega) hsinx
  have hsinpos : 0 < |Real.sin x| := abs_pos.mpr hsinx
  have h2sinpos : (0 : ℝ) < 2 * |Real.sin x| := by linarith
  have hRHS : (1 / ((2 * P + 2 : ℕ) : ℝ)) * (2 * |Real.sin (((2 * P + 2 : ℕ) : ℝ) * x)|)
      < 2 * |Real.sin x| := by
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ hMpos]
    nlinarith [hstrict, hMpos]
  rw [← hnormeq] at hRHS
  -- `hRHS : 2|sin x|·‖T‖ < 2|sin x|`, divide by `2|sin x| > 0`.
  have hTnn : 0 ≤ ‖(Tpoly P).eval w‖ := norm_nonneg _
  nlinarith [hRHS, h2sinpos, hTnn]

end

end QAOA.IsingChain.Achievability
