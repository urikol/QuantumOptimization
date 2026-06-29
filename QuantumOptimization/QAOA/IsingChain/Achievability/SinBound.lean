import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Sine multiple-angle bound — `|sin (n·x)| ≤ n·|sin x|` and its strict version

Elementary bounds on `sin` at integer multiples of an angle, proved by induction from
the addition formula. These anchor the circle-root analysis of the achievability
complement polynomial: `|T(e^{iθ})| < 1` away from `θ = π` reduces to the strict
inequality `|sin (n x)| < n |sin x|` (for `n ≥ 2`, `sin x ≠ 0`).

## Main statements
- `abs_sin_nat_mul_le`: `|sin (n x)| ≤ n |sin x|`.
- `abs_sin_nat_mul_lt`: `|sin (n x)| < n |sin x|` for `2 ≤ n` and `sin x ≠ 0`.
-/

namespace QAOA.IsingChain.Achievability

/-- Multiple-angle bound: `|sin (n x)| ≤ n |sin x|` for natural `n`. -/
theorem abs_sin_nat_mul_le (n : ℕ) (x : ℝ) :
    |Real.sin (n * x)| ≤ n * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hsplit : ((m + 1 : ℕ) : ℝ) * x = m * x + x := by push_cast; ring
    rw [hsplit, Real.sin_add]
    calc |Real.sin (m * x) * Real.cos x + Real.cos (m * x) * Real.sin x|
        ≤ |Real.sin (m * x) * Real.cos x| + |Real.cos (m * x) * Real.sin x| :=
          abs_add_le _ _
      _ ≤ |Real.sin (m * x)| * 1 + 1 * |Real.sin x| := by
          rw [abs_mul, abs_mul]
          have h1 : |Real.cos x| ≤ 1 := Real.abs_cos_le_one x
          have h2 : |Real.cos (m * x)| ≤ 1 := Real.abs_cos_le_one (m * x)
          have ha : (0 : ℝ) ≤ |Real.sin (m * x)| := abs_nonneg _
          have hb : (0 : ℝ) ≤ |Real.sin x| := abs_nonneg _
          nlinarith
      _ ≤ (m : ℝ) * |Real.sin x| + 1 * |Real.sin x| := by
          rw [mul_one]
          gcongr
      _ = ((m + 1 : ℕ) : ℝ) * |Real.sin x| := by push_cast; ring

/-- Strict multiple-angle bound: `|sin (n x)| < n |sin x|` once `n ≥ 2` and
`sin x ≠ 0`. (At `n = 0, 1` or `sin x = 0` equality can occur.) -/
theorem abs_sin_nat_mul_lt {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : Real.sin x ≠ 0) :
    |Real.sin (n * x)| < n * |Real.sin x| := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hsx : 0 < |Real.sin x| := abs_pos.mpr hx
  have hsplit : ((m + 1 : ℕ) : ℝ) * x = m * x + x := by push_cast; ring
  rw [hsplit, Real.sin_add]
  have htri : |Real.sin (m * x) * Real.cos x + Real.cos (m * x) * Real.sin x|
      ≤ |Real.sin (m * x)| * |Real.cos x| + |Real.cos (m * x)| * |Real.sin x| := by
    calc |Real.sin (m * x) * Real.cos x + Real.cos (m * x) * Real.sin x|
        ≤ |Real.sin (m * x) * Real.cos x| + |Real.cos (m * x) * Real.sin x| :=
          abs_add_le _ _
      _ = |Real.sin (m * x)| * |Real.cos x| + |Real.cos (m * x)| * |Real.sin x| := by
          rw [abs_mul, abs_mul]
  rcases eq_or_ne (Real.sin (m * x)) 0 with hsm | hsm
  · -- the `sin (m x) = 0` branch: the bound collapses to `|sin x| < (m+1)|sin x|`
    have hbound : |Real.sin (m * x)| * |Real.cos x| + |Real.cos (m * x)| * |Real.sin x|
        ≤ |Real.sin x| := by
      rw [hsm, abs_zero, zero_mul, zero_add]
      calc |Real.cos (m * x)| * |Real.sin x| ≤ 1 * |Real.sin x| := by
            gcongr
            exact Real.abs_cos_le_one (m * x)
        _ = |Real.sin x| := one_mul _
    have hlt : |Real.sin x| < ((m + 1 : ℕ) : ℝ) * |Real.sin x| := by
      have : (1 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < m + 1)
      nlinarith
    linarith [htri, hbound, hlt]
  · -- the `sin (m x) ≠ 0` branch: `|cos x| < 1` makes the first term strictly drop
    have hcx : |Real.cos x| < 1 := by
      rcases lt_or_eq_of_le (Real.abs_cos_le_one x) with h | h
      · exact h
      · exfalso
        have h1 : Real.cos x ^ 2 = 1 := by
          have := sq_abs (Real.cos x)
          rw [h] at this
          linarith [this]
        have h2 : Real.sin x ^ 2 = 0 := by
          have := Real.sin_sq_add_cos_sq x
          linarith
        exact hx (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2)
    have hsm' : 0 < |Real.sin (m * x)| := abs_pos.mpr hsm
    have hstep1 : |Real.sin (m * x)| * |Real.cos x| < |Real.sin (m * x)| := by
      nlinarith
    have hstep2 : |Real.cos (m * x)| * |Real.sin x| ≤ |Real.sin x| := by
      calc |Real.cos (m * x)| * |Real.sin x| ≤ 1 * |Real.sin x| := by
            gcongr
            exact Real.abs_cos_le_one (m * x)
        _ = |Real.sin x| := one_mul _
    have hih := abs_sin_nat_mul_le m x
    have : |Real.sin (m * x)| ≤ (m : ℝ) * |Real.sin x| := hih
    have hfinal : |Real.sin (m * x)| * |Real.cos x| + |Real.cos (m * x)| * |Real.sin x|
        < ((m + 1 : ℕ) : ℝ) * |Real.sin x| := by
      push_cast
      nlinarith
    linarith [htri, hfinal]

end QAOA.IsingChain.Achievability
