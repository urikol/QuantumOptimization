import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Geometry

/-!
# SU(2) → SO(3) Bloch bridge — concrete `2×2` circuits onto the Rodrigues `tauVec`

The load-bearing dictionary connecting an explicit per-mode `2×2` QSP circuit (built from
the three generators `A`, `B`, `W`) to the existing SO(3) Rodrigues machinery
(`tauVec`, `epsilonMode`).

The bridge is `blochZ`, the image of `ẑ` under the adjoint action `U ↦ U σz U†` read off
the matrix entries (the third column of the SO(3) matrix `Ad(U)`):
`blochZ U = (2 Re(U₁₀ conj U₀₀), 2 Im(U₁₀ conj U₀₀), |U₀₀|² − |U₁₀|²)`. For unitary `U`
with unit first column (all our circuits) this is exactly `Ad(U) ẑ`.

## FROZEN conventions (numerically verified to ~1e-15)
- `Amat γ = e^{−i2γσz} = diag(e^{−i2γ}, e^{+i2γ})`, `Ad(Amat γ) = R(ẑ, 4γ)`.
- `Bmat β = e^{+i2βσz} = diag(e^{+i2β}, e^{−i2β})` (β **UN-negated**),
  `Ad(Bmat β) = R(ẑ, −4β)` — the `−β` of `epsilonMode` emerges HERE.
- `Wmat k = e^{−ikσy/2} = !![cos(k/2), −sin(k/2); sin(k/2), cos(k/2)]`,
  real entries, `Wmat (−k) = (Wmat k)†`.
- `Ad(Wmat (−k) · Amat γ · Wmat k) = R(b̂_k, 4γ)` exactly (no residual sign).

## Main definitions
- `Amat`, `Bmat`, `Wmat`: the three `2×2` generators.
- `blochZ`: the `ẑ`-image of `Ad(U)` from `U`'s entries.
- `Uk`: the per-mode circuit `B_{P−1} W(−k) A_{P−1} W(k) ⋯ B_0 W(−k) A_0 W(k)`.
- `Gmat`: the magnetization circuit `Wmat k · Uk`.

## Main statements
- `blochZ_one`, `blochZ_Bmat_mul`, `blochZ_WAW_mul`: the base + two layer-step lemmas.
- `blochZ_Uk`, `blochZ_Uk_fin`: the circuit→`tauVec` bridge.
- `epsilonMode_eq_zero_of_G21_eq_zero`: the keystone — `G₂₁ = 0 ⟹ ε = 0`.
-/

namespace QAOA.IsingChain.Achievability

open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- The three `2×2` generators
-- ============================================================================

/-- The cost-layer phase `A_m = e^{−i2γσz} = diag(e^{−i2γ}, e^{+i2γ})`. -/
noncomputable def Amat (γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(2 * γ) * Complex.I), 0; 0, Complex.exp ((2 * γ) * Complex.I)]

/-- The mixer-layer phase `B_m = e^{+i2βσz} = diag(e^{+i2β}, e^{−i2β})`. The mixer angle
`β` is fed **un-negated**; the `−β` of `epsilonMode` emerges from `Ad(B) = R(ẑ, −4β)`. -/
noncomputable def Bmat (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp ((2 * β) * Complex.I), 0; 0, Complex.exp (-(2 * β) * Complex.I)]

/-- The signal-rotation `W(k) = e^{−ikσy/2} = !![cos(k/2), −sin(k/2); sin(k/2), cos(k/2)]`.
Real entries; `Wmat (−k) = (Wmat k)†`. -/
noncomputable def Wmat (k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.cos (k / 2) : ℂ), -(Real.sin (k / 2) : ℂ);
     (Real.sin (k / 2) : ℂ), (Real.cos (k / 2) : ℂ)]

-- ============================================================================
-- The Bloch bridge `blochZ`
-- ============================================================================

/-- The image of `ẑ` under the adjoint action `U ↦ U σz U†`, read off `U`'s first column
`(U₀₀, U₁₀)`. For unitary `U` with unit first column, `U σz U† = 2(col₀)(col₀)† − I`, whose
Bloch vector is `n₀ = 2 Re(U₁₀ conj U₀₀)`, `n₁ = 2 Im(U₁₀ conj U₀₀)`,
`n₂ = |U₀₀|² − |U₁₀|²`. (Defined unconditionally by the entry formula.) -/
noncomputable def blochZ (U : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℝ :=
  ![2 * ((U 1 0) * (starRingEnd ℂ) (U 0 0)).re,
    2 * ((U 1 0) * (starRingEnd ℂ) (U 0 0)).im,
    Complex.normSq (U 0 0) - Complex.normSq (U 1 0)]

/-- The base case: `blochZ 1 = ẑ`. -/
theorem blochZ_one : blochZ 1 = JordanWigner.zHat := by
  funext i
  fin_cases i <;>
    simp [blochZ, JordanWigner.zHat, Complex.normSq]

-- ---------------------------------------------------------------------------
-- Entry extraction for the diagonal `Bmat` / `Amat` products
-- ---------------------------------------------------------------------------

/-- First-column entries of `Bmat β * U`: the diagonal phase scales each row. -/
theorem Bmat_mul_col (β : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (Bmat β * U) 0 0 = Complex.exp ((2 * β) * Complex.I) * U 0 0 ∧
    (Bmat β * U) 1 0 = Complex.exp (-(2 * β) * Complex.I) * U 1 0 := by
  constructor <;>
    simp [Bmat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Explicit coordinates of a `ẑ`-axis Rodrigues rotation applied to a vector:
`R ẑ θ *ᵥ v = (cosθ·v₀ − sinθ·v₁, sinθ·v₀ + cosθ·v₁, v₂)`. -/
theorem R_zHat_mulVec (θ : ℝ) (v : Fin 3 → ℝ) :
    JordanWigner.R JordanWigner.zHat θ *ᵥ v =
      ![Real.cos θ * v 0 - Real.sin θ * v 1,
        Real.sin θ * v 0 + Real.cos θ * v 1, v 2] := by
  rw [JordanWigner.R_mulVec]
  funext i
  fin_cases i <;>
    simp [JordanWigner.zHat, dotProduct, Fin.sum_univ_three, cross_apply, Pi.smul_apply,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

-- ---------------------------------------------------------------------------
-- Phase-fold helpers for the diagonal step
-- ---------------------------------------------------------------------------

/-- Folding the two `B`-phases into a single `−4β` phase on the entry product:
`(e^{−i2β}·a)·conj(e^{i2β}·b) = e^{−i4β}·(a·conj b)`. -/
theorem phase_fold_neg (β : ℝ) (a b : ℂ) :
    Complex.exp (-(2 * β) * Complex.I) * a *
        (starRingEnd ℂ) (Complex.exp ((2 * β) * Complex.I) * b)
      = Complex.exp (-(4 * β) * Complex.I) * (a * (starRingEnd ℂ) b) := by
  have hconj : (starRingEnd ℂ) (Complex.exp ((2 * β) * Complex.I))
      = Complex.exp (-(2 * β) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_mul, Complex.conj_I, Complex.conj_ofNat, Complex.conj_ofReal]
    ring
  rw [map_mul, hconj]
  rw [show Complex.exp (-(2 * β) * Complex.I) * a *
        (Complex.exp (-(2 * β) * Complex.I) * (starRingEnd ℂ) b)
      = (Complex.exp (-(2 * β) * Complex.I) * Complex.exp (-(2 * β) * Complex.I)) *
        (a * (starRingEnd ℂ) b) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- Real part of a `−4β`-phase-twisted complex number. -/
theorem exp_neg_four_mul_re (β : ℝ) (w : ℂ) :
    (Complex.exp (-(4 * β) * Complex.I) * w).re
      = Real.cos (4 * β) * w.re + Real.sin (4 * β) * w.im := by
  have hre : (Complex.exp (-(4 * β) * Complex.I)).re = Real.cos (4 * β) := by
    rw [show (-(4 * β) * Complex.I) = ((-(4 * β) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (Complex.exp (-(4 * β) * Complex.I)).im = -Real.sin (4 * β) := by
    rw [show (-(4 * β) * Complex.I) = ((-(4 * β) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  rw [Complex.mul_re, hre, him]; ring

/-- Imaginary part of a `−4β`-phase-twisted complex number. -/
theorem exp_neg_four_mul_im (β : ℝ) (w : ℂ) :
    (Complex.exp (-(4 * β) * Complex.I) * w).im
      = Real.cos (4 * β) * w.im - Real.sin (4 * β) * w.re := by
  have hre : (Complex.exp (-(4 * β) * Complex.I)).re = Real.cos (4 * β) := by
    rw [show (-(4 * β) * Complex.I) = ((-(4 * β) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have him : (Complex.exp (-(4 * β) * Complex.I)).im = -Real.sin (4 * β) := by
    rw [show (-(4 * β) * Complex.I) = ((-(4 * β) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]
  rw [Complex.mul_im, hre, him]; ring

/-- A unit-modulus phase leaves `normSq` invariant: `normSq (e^{iθ}·x) = normSq x`. -/
theorem normSq_exp_mul (θ : ℝ) (x : ℂ) :
    Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I) * x) = Complex.normSq x := by
  rw [map_mul]
  have h1 : Complex.normSq (Complex.exp ((θ : ℂ) * Complex.I)) = 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]
  rw [h1, one_mul]

/-- `normSq` of the `B`-phase is `1` (in the exact matrix-entry form `2 * ↑β`). -/
theorem normSq_Bphase (c : ℝ) :
    Complex.normSq (Complex.exp ((2 * (c : ℂ)) * Complex.I)) = 1 := by
  rw [show (2 * (c : ℂ)) * Complex.I = ((2 * c : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

/-- `normSq` of the negated `B`-phase is `1`. -/
theorem normSq_Bphase_neg (c : ℝ) :
    Complex.normSq (Complex.exp (-(2 * (c : ℂ)) * Complex.I)) = 1 := by
  rw [show (-(2 * (c : ℂ))) * Complex.I = ((-(2 * c) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I, one_pow]

-- ============================================================================
-- The B-layer step (numerically validated sign): `Ad(Bmat β) = R(ẑ, −4β)`
-- ============================================================================

/-- B-step: `blochZ (Bmat β · U) = R(ẑ, −4β) *ᵥ blochZ U`. The `−4β` sign is the
numerically validated mixer convention (β un-negated in the circuit). -/
theorem blochZ_Bmat_mul (β : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (Bmat β * U) = JordanWigner.R JordanWigner.zHat (-(4 * β)) *ᵥ blochZ U := by
  obtain ⟨hc0, hc1⟩ := Bmat_mul_col β U
  rw [R_zHat_mulVec]
  have key0 : blochZ (Bmat β * U) 0
      = Real.cos (-(4 * β)) * (blochZ U 0) - Real.sin (-(4 * β)) * (blochZ U 1) := by
    simp only [blochZ, Matrix.cons_val_zero, Matrix.cons_val_one, hc0, hc1]
    rw [phase_fold_neg, exp_neg_four_mul_re, Real.cos_neg, Real.sin_neg]
    ring
  have key1 : blochZ (Bmat β * U) 1
      = Real.sin (-(4 * β)) * (blochZ U 0) + Real.cos (-(4 * β)) * (blochZ U 1) := by
    simp only [blochZ, Matrix.cons_val_one, Matrix.cons_val_zero, hc0, hc1]
    rw [phase_fold_neg, exp_neg_four_mul_im, Real.cos_neg, Real.sin_neg]
    ring
  have key2 : blochZ (Bmat β * U) 2 = blochZ U 2 := by
    simp only [blochZ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hc0, hc1]
    rw [Complex.normSq_mul, Complex.normSq_mul, normSq_Bphase, normSq_Bphase_neg, one_mul, one_mul]
  funext i
  fin_cases i
  · simpa using key0
  · simpa using key1
  · simpa using key2

-- ============================================================================
-- The A-layer step: `Ad(Amat γ) = R(ẑ, 4γ)`
-- ============================================================================

/-- First-column entries of `Amat γ * U`. -/
theorem Amat_mul_col (γ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (Amat γ * U) 0 0 = Complex.exp (-(2 * γ) * Complex.I) * U 0 0 ∧
    (Amat γ * U) 1 0 = Complex.exp ((2 * γ) * Complex.I) * U 1 0 := by
  constructor <;>
    simp [Amat, Matrix.mul_apply, Fin.sum_univ_two]

/-- Folding the two `A`-phases into a single `+4γ` phase on the entry product:
`(e^{i2γ}·a)·conj(e^{−i2γ}·b) = e^{i4γ}·(a·conj b)`. -/
theorem phase_fold_pos (γ : ℝ) (a b : ℂ) :
    Complex.exp ((2 * γ) * Complex.I) * a *
        (starRingEnd ℂ) (Complex.exp (-(2 * γ) * Complex.I) * b)
      = Complex.exp ((4 * γ) * Complex.I) * (a * (starRingEnd ℂ) b) := by
  have hconj : (starRingEnd ℂ) (Complex.exp (-(2 * γ) * Complex.I))
      = Complex.exp ((2 * γ) * Complex.I) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, map_neg, map_mul, Complex.conj_I, Complex.conj_ofNat, Complex.conj_ofReal]
    ring
  rw [map_mul, hconj]
  rw [show Complex.exp ((2 * γ) * Complex.I) * a *
        (Complex.exp ((2 * γ) * Complex.I) * (starRingEnd ℂ) b)
      = (Complex.exp ((2 * γ) * Complex.I) * Complex.exp ((2 * γ) * Complex.I)) *
        (a * (starRingEnd ℂ) b) by ring]
  rw [← Complex.exp_add]
  congr 2
  ring

/-- Real part of a `+4γ`-phase-twisted complex number. -/
theorem exp_pos_four_mul_re (γ : ℝ) (w : ℂ) :
    (Complex.exp ((4 * γ) * Complex.I) * w).re
      = Real.cos (4 * γ) * w.re - Real.sin (4 * γ) * w.im := by
  have hre : (Complex.exp ((4 * γ) * Complex.I)).re = Real.cos (4 * γ) := by
    rw [show ((4 * γ) * Complex.I) = ((4 * γ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((4 * γ) * Complex.I)).im = Real.sin (4 * γ) := by
    rw [show ((4 * γ) * Complex.I) = ((4 * γ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im]
  rw [Complex.mul_re, hre, him]

/-- Imaginary part of a `+4γ`-phase-twisted complex number. -/
theorem exp_pos_four_mul_im (γ : ℝ) (w : ℂ) :
    (Complex.exp ((4 * γ) * Complex.I) * w).im
      = Real.sin (4 * γ) * w.re + Real.cos (4 * γ) * w.im := by
  have hre : (Complex.exp ((4 * γ) * Complex.I)).re = Real.cos (4 * γ) := by
    rw [show ((4 * γ) * Complex.I) = ((4 * γ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_re]
  have him : (Complex.exp ((4 * γ) * Complex.I)).im = Real.sin (4 * γ) := by
    rw [show ((4 * γ) * Complex.I) = ((4 * γ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_ofReal_mul_I_im]
  rw [Complex.mul_im, hre, him]; ring

/-- A-step: `blochZ (Amat γ · U) = R(ẑ, 4γ) *ᵥ blochZ U`. -/
theorem blochZ_Amat_mul (γ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (Amat γ * U) = JordanWigner.R JordanWigner.zHat (4 * γ) *ᵥ blochZ U := by
  obtain ⟨hc0, hc1⟩ := Amat_mul_col γ U
  rw [R_zHat_mulVec]
  have key0 : blochZ (Amat γ * U) 0
      = Real.cos (4 * γ) * (blochZ U 0) - Real.sin (4 * γ) * (blochZ U 1) := by
    simp only [blochZ, Matrix.cons_val_zero, Matrix.cons_val_one, hc0, hc1]
    rw [phase_fold_pos, exp_pos_four_mul_re]
    ring
  have key1 : blochZ (Amat γ * U) 1
      = Real.sin (4 * γ) * (blochZ U 0) + Real.cos (4 * γ) * (blochZ U 1) := by
    simp only [blochZ, Matrix.cons_val_one, Matrix.cons_val_zero, hc0, hc1]
    rw [phase_fold_pos, exp_pos_four_mul_im]
    ring
  have key2 : blochZ (Amat γ * U) 2 = blochZ U 2 := by
    simp only [blochZ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hc0, hc1]
    rw [Complex.normSq_mul, Complex.normSq_mul, normSq_Bphase_neg, normSq_Bphase,
      one_mul, one_mul]
  funext i
  fin_cases i
  · simpa using key0
  · simpa using key1
  · simpa using key2

-- ============================================================================
-- The W-layer step: `Ad(Wmat k) = R(ŷ, k)`
-- ============================================================================

/-- The `ŷ` rotation axis `(0, 1, 0)`. -/
def yHat : Fin 3 → ℝ := ![0, 1, 0]

/-- Explicit coordinates of a `ŷ`-axis Rodrigues rotation applied to a vector:
`R ŷ θ *ᵥ v = (cosθ·v₀ + sinθ·v₂, v₁, −sinθ·v₀ + cosθ·v₂)`. -/
theorem R_yHat_mulVec (θ : ℝ) (v : Fin 3 → ℝ) :
    JordanWigner.R yHat θ *ᵥ v =
      ![Real.cos θ * v 0 + Real.sin θ * v 2, v 1,
        -(Real.sin θ * v 0) + Real.cos θ * v 2] := by
  rw [JordanWigner.R_mulVec]
  funext i
  fin_cases i <;>
    simp [yHat, dotProduct, Fin.sum_univ_three, cross_apply, Pi.smul_apply,
      Matrix.vecHead, Matrix.vecTail] <;>
    ring

/-- First-column entries of `Wmat k * U`. -/
theorem Wmat_mul_col (k : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    (Wmat k * U) 0 0 = (Real.cos (k / 2) : ℂ) * U 0 0 - (Real.sin (k / 2) : ℂ) * U 1 0 ∧
    (Wmat k * U) 1 0 = (Real.sin (k / 2) : ℂ) * U 0 0 + (Real.cos (k / 2) : ℂ) * U 1 0 := by
  constructor
  · simp only [Wmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, neg_mul]
    ring
  · simp only [Wmat, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply]

/-- The half-angle Pythagorean identity in `ℝ`, as a `have`-ready fact. -/
theorem cos_sq_half_add_sin_sq_half (k : ℝ) :
    Real.cos (k / 2) ^ 2 + Real.sin (k / 2) ^ 2 = 1 := by
  rw [add_comm]; exact Real.sin_sq_add_cos_sq (k / 2)

/-- Double-angle: `Real.cos k = cos(k/2)² − sin(k/2)²`. -/
theorem cos_eq_cos_sq_half_sub (k : ℝ) :
    Real.cos k = Real.cos (k / 2) ^ 2 - Real.sin (k / 2) ^ 2 := by
  conv_lhs => rw [show k = 2 * (k / 2) by ring]
  rw [Real.cos_two_mul']

/-- Double-angle: `Real.sin k = 2 sin(k/2) cos(k/2)`. -/
theorem sin_eq_two_mul_half (k : ℝ) :
    Real.sin k = 2 * Real.sin (k / 2) * Real.cos (k / 2) := by
  conv_lhs => rw [show k = 2 * (k / 2) by ring]
  rw [Real.sin_two_mul]

/-- W-step: `blochZ (Wmat k · U) = R(ŷ, k) *ᵥ blochZ U`. -/
theorem blochZ_Wmat_mul (k : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (Wmat k * U) = JordanWigner.R yHat k *ᵥ blochZ U := by
  obtain ⟨hc0, hc1⟩ := Wmat_mul_col k U
  rw [R_yHat_mulVec]
  set c := Real.cos (k / 2)
  set s := Real.sin (k / 2)
  have hpy : c ^ 2 + s ^ 2 = 1 := cos_sq_half_add_sin_sq_half k
  have hck : Real.cos k = c ^ 2 - s ^ 2 := cos_eq_cos_sq_half_sub k
  have hsk : Real.sin k = 2 * s * c := sin_eq_two_mul_half k
  have key0 : blochZ (Wmat k * U) 0
      = Real.cos k * (blochZ U 0) + Real.sin k * (blochZ U 2) := by
    simp only [blochZ, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons, hc0, hc1, hck, hsk, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_sub, map_mul,
      Complex.conj_ofReal]
    ring
  have key1 : blochZ (Wmat k * U) 1 = blochZ U 1 := by
    simp only [blochZ, Matrix.cons_val_one, Matrix.cons_val_zero, hc0, hc1,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
      Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
      map_sub, map_mul, Complex.conj_ofReal]
    linear_combination (2 * (U 0 0).re * (U 1 0).im - 2 * (U 0 0).im * (U 1 0).re) * hpy
  have key2 : blochZ (Wmat k * U) 2
      = -(Real.sin k * (blochZ U 0)) + Real.cos k * (blochZ U 2) := by
    simp only [blochZ, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
      Matrix.cons_val_zero, hc0, hc1, hck, hsk, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im, map_sub, map_mul,
      Complex.conj_ofReal]
    ring
  funext i
  fin_cases i
  · simpa using key0
  · simpa using key1
  · simpa using key2

-- ============================================================================
-- SO(3) conjugation: `R(ŷ,−k)·R(ẑ,θ)·R(ŷ,k) = R(b̂_k, θ)`
-- ============================================================================

/-- SO(3) conjugation identity: rotating about `ẑ` then conjugating by `R(ŷ,±k)`
yields a rotation about the conjugated axis `b̂_k`. Proven by direct `3×3` entry
computation; `Real.sin_sq_add_cos_sq` closes the diagonal entries. -/
theorem R_conj_yHat_zHat (k θ : ℝ) :
    JordanWigner.R yHat (-k) * JordanWigner.R JordanWigner.zHat θ * JordanWigner.R yHat k
      = JordanWigner.R (JordanWigner.bHat k) θ := by
  have hpy : Real.sin k ^ 2 + Real.cos k ^ 2 = 1 := Real.sin_sq_add_cos_sq k
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [JordanWigner.R, JordanWigner.crossMatrix, JordanWigner.bHat, JordanWigner.zHat,
      yHat, Matrix.mul_apply, Matrix.vecMulVec, Fin.sum_univ_three, Real.sin_neg,
      Real.cos_neg]
  -- six surviving entries (the ŷ-row is fixed by simp), in order
  -- (0,0),(0,1),(0,2),(2,0),(2,1),(2,2): diagonals need `cos²+sin² = 1`, off-diagonals are ring.
  · linear_combination Real.cos θ * hpy
  · ring
  · ring
  · ring
  · ring
  · linear_combination Real.cos θ * hpy

-- ============================================================================
-- The conjugated-cost step: `Ad(W(−k)·A(γ)·W(k)) = R(b̂_k, 4γ)`
-- ============================================================================

/-- Conjugated-cost step: `blochZ (Wmat (−k) · Amat γ · Wmat k · U) = R(b̂_k, 4γ) *ᵥ blochZ U`
exactly (no residual sign). Composes the W/A/W single-generator steps with the SO(3)
conjugation identity `R_conj_yHat_zHat`. -/
theorem blochZ_WAW_mul (k γ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    blochZ (Wmat (-k) * Amat γ * Wmat k * U)
      = JordanWigner.R (JordanWigner.bHat k) (4 * γ) *ᵥ blochZ U := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, blochZ_Wmat_mul, blochZ_Amat_mul, blochZ_Wmat_mul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, R_conj_yHat_zHat]

-- ============================================================================
-- The per-mode circuit `Uk` and the Bloch bridge `blochZ ∘ Uk = tauVec`
-- ============================================================================

/-- The per-mode QSP circuit
`U_k = B_{P−1} W(−k) A_{P−1} W(k) ⋯ B_0 W(−k) A_0 W(k)` (layer `m = 0` acts first,
rightmost), mirroring `layerProd`'s left-multiply order. The mixer angle `β` is fed
un-negated into the `B`-slots.

The per-layer factor is grouped `Bmat · (Wmat(−k) · Amat · Wmat k · Uk p)` so the leading
`B`-generator and the `W(−k)·A·W(k)` cost-conjugate block feed `blochZ_Bmat_mul` and
`blochZ_WAW_mul` directly (an associativity-only choice; the matrix is unchanged). -/
noncomputable def Uk (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  match P with
  | 0 => 1
  | Nat.succ p => Bmat (β p) * (Wmat (-k) * Amat (γ p) * Wmat k * Uk p k γ β)

/-- One-layer unfolding of `tauVec` at the negated mixer feed: stacking the mixer
rotation `R(ẑ, −4β_p)` and cost rotation `R(b̂_k, 4γ_p)` onto `tauVec p`. -/
theorem tauVec_succ (p : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    JordanWigner.tauVec (p + 1) k γ (fun m => -(β m))
      = JordanWigner.R JordanWigner.zHat (-(4 * β p)) *ᵥ
          (JordanWigner.R (JordanWigner.bHat k) (4 * γ p) *ᵥ
            JordanWigner.tauVec p k γ (fun m => -(β m))) := by
  conv_lhs => rw [JordanWigner.tauVec, JordanWigner.layerProd, JordanWigner.layerBlock]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← JordanWigner.tauVec]
  rw [show (4 : ℝ) * (fun m => -(β m)) p = -(4 * β p) by simp]

/-- **The Bloch bridge.** `blochZ (Uk P k γ β) = tauVec P k γ (−β)`: the SU(2) circuit's
adjoint magnetization is the SO(3) Rodrigues `tauVec`, with the `(−β)` mixer feed emerging
from `Ad(B) = R(ẑ, −4β)`. By induction on `P`, composing the B-step and WAW-step. -/
theorem blochZ_Uk (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    blochZ (Uk P k γ β) = JordanWigner.tauVec P k γ (fun m => -(β m)) := by
  induction P with
  | zero =>
      rw [Uk, JordanWigner.tauVec_zero, blochZ_one]
  | succ p ih =>
      rw [Uk, blochZ_Bmat_mul, blochZ_WAW_mul, ih, tauVec_succ]

/-- Negation commutes with `extendFin`: `(fun m => −(extendFin β m)) = extendFin (−β)`.
Both pad with `0` beyond `P` (`−0 = 0`), so they agree everywhere on `ℕ`. -/
theorem neg_extendFin {P : ℕ} (β : Fin P → ℝ) :
    (fun m => -(JordanWigner.extendFin β m)) = JordanWigner.extendFin (fun i => -(β i)) := by
  funext m
  simp only [JordanWigner.extendFin]
  by_cases h : m < P
  · simp [h]
  · simp [h]

/-- The `Fin`-indexed Bloch bridge, matching `epsilonMode`'s internal `tauVec` form:
`blochZ (Uk P k (extendFin γ) (extendFin β)) = tauVec P k (extendFin γ) (extendFin (−β))`. -/
theorem blochZ_Uk_fin (P : ℕ) (k : ℝ) (γ β : Fin P → ℝ) :
    blochZ (Uk P k (JordanWigner.extendFin γ) (JordanWigner.extendFin β))
      = JordanWigner.tauVec P k (JordanWigner.extendFin γ)
          (JordanWigner.extendFin (fun i => -(β i))) := by
  rw [blochZ_Uk, neg_extendFin]

-- ============================================================================
-- The magnetization circuit `Gmat`, the unit-column invariant, and the keystone
-- ============================================================================

/-- The squared 2-norm of a matrix's first column. -/
noncomputable def colNormSq (U : Matrix (Fin 2) (Fin 2) ℂ) : ℝ :=
  Complex.normSq (U 0 0) + Complex.normSq (U 1 0)

/-- `Bmat β` (a unit-modulus diagonal) preserves the first-column norm. -/
theorem colNormSq_Bmat_mul (β : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    colNormSq (Bmat β * U) = colNormSq U := by
  obtain ⟨hc0, hc1⟩ := Bmat_mul_col β U
  simp only [colNormSq, hc0, hc1, Complex.normSq_mul, normSq_Bphase, normSq_Bphase_neg,
    one_mul]

/-- `Amat γ` preserves the first-column norm. -/
theorem colNormSq_Amat_mul (γ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    colNormSq (Amat γ * U) = colNormSq U := by
  obtain ⟨hc0, hc1⟩ := Amat_mul_col γ U
  simp only [colNormSq, hc0, hc1, Complex.normSq_mul, normSq_Bphase, normSq_Bphase_neg,
    one_mul]

/-- `Wmat k` (a real rotation) preserves the first-column norm (`cos² + sin² = 1`). -/
theorem colNormSq_Wmat_mul (k : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    colNormSq (Wmat k * U) = colNormSq U := by
  obtain ⟨hc0, hc1⟩ := Wmat_mul_col k U
  have hpy : Real.cos (k / 2) ^ 2 + Real.sin (k / 2) ^ 2 = 1 := cos_sq_half_add_sin_sq_half k
  simp only [colNormSq, hc0, hc1, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  linear_combination ((U 0 0).re ^ 2 + (U 0 0).im ^ 2 + (U 1 0).re ^ 2 + (U 1 0).im ^ 2) * hpy

/-- The cost-conjugate block `W(−k)·A·W(k)` preserves the first-column norm. -/
theorem colNormSq_WAW_mul (k γ : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ) :
    colNormSq (Wmat (-k) * Amat γ * Wmat k * U) = colNormSq U := by
  rw [Matrix.mul_assoc, Matrix.mul_assoc, colNormSq_Wmat_mul, colNormSq_Amat_mul,
    colNormSq_Wmat_mul]

/-- **Unit first column.** Every `Uk`-product has a unit first column. By induction:
each generator (`Bmat`, the `W(−k)·A·W(k)` block) is an isometry. -/
theorem colNormSq_Uk (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    colNormSq (Uk P k γ β) = 1 := by
  induction P with
  | zero => simp [colNormSq, Uk, Complex.normSq]
  | succ p ih =>
      rw [Uk, colNormSq_Bmat_mul, colNormSq_WAW_mul, ih]

/-- The magnetization circuit `G_k = W(k) · U_k`; its `(1,0)` entry vanishing at a node
is the achievability condition (`ε = 2|G₂₁|²`). -/
noncomputable def Gmat (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Wmat k * Uk P k γ β

/-- **Keystone algebra.** If the magnetization circuit's `(1,0)` entry `(Wmat k · U) 1 0`
vanishes and `U` has a unit first column, then `b̂_k ⬝ᵥ blochZ U = 1` (the magnetization is
pinned to the cost axis). With `c = cos(k/2)`, `s = sin(k/2)`, the hypothesis is the complex
relation `s·U₀₀ + c·U₁₀ = 0`; the conclusion follows from the polynomial identity
`−4sc·Re(z) + (c²−s²)(|U₀₀|²−|U₁₀|²) = (|U₀₀|²+|U₁₀|²)(c²+s²) − 2(s·U₀₀+c·U₁₀ real/imag)²`. -/
theorem bHat_dot_blochZ_of_W_col_zero (k : ℝ) (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hcol : colNormSq U = 1) (hG : (Wmat k * U) 1 0 = 0) :
    JordanWigner.bHat k ⬝ᵥ blochZ U = 1 := by
  obtain ⟨_, hc1⟩ := Wmat_mul_col k U
  rw [hc1] at hG
  -- real / imaginary parts of `s·U₀₀ + c·U₁₀ = 0`
  have hre : Real.sin (k / 2) * (U 0 0).re + Real.cos (k / 2) * (U 1 0).re = 0 := by
    have h := congrArg Complex.re hG
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_re, zero_mul, sub_zero] at h
    linarith [h]
  have him : Real.sin (k / 2) * (U 0 0).im + Real.cos (k / 2) * (U 1 0).im = 0 := by
    have h := congrArg Complex.im hG
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.zero_im, zero_mul, add_zero] at h
    linarith [h]
  have hpy : Real.cos (k / 2) ^ 2 + Real.sin (k / 2) ^ 2 = 1 := cos_sq_half_add_sin_sq_half k
  have hck : Real.cos k = Real.cos (k / 2) ^ 2 - Real.sin (k / 2) ^ 2 := cos_eq_cos_sq_half_sub k
  have hsk : Real.sin k = 2 * Real.sin (k / 2) * Real.cos (k / 2) := sin_eq_two_mul_half k
  simp only [colNormSq, Complex.normSq_apply] at hcol
  simp only [JordanWigner.bHat, blochZ, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, hck, hsk,
    Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  -- the symbolically-verified identity (cofactors `−2(s·U₀₀+c·U₁₀)²` from sympy Groebner)
  linear_combination (Real.cos (k / 2) ^ 2 + Real.sin (k / 2) ^ 2) * hcol + hpy
    + (-2 * (Real.sin (k / 2) * (U 0 0).re + Real.cos (k / 2) * (U 1 0).re)) * hre
    + (-2 * (Real.sin (k / 2) * (U 0 0).im + Real.cos (k / 2) * (U 1 0).im)) * him

/-- **KEYSTONE.** If the magnetization circuit's off-diagonal `G₂₁` vanishes at the node,
the per-mode residual energy vanishes. Composes `geometric_form`, `blochZ_Uk_fin`, the
unit-column invariant `colNormSq_Uk`, and the keystone algebra. -/
theorem epsilonMode_eq_zero_of_G21_eq_zero (P : ℕ) (n : Fin P) (γ β : Fin P → ℝ)
    (hG : Gmat P (JordanWigner.waveVectorABC P n)
      (JordanWigner.extendFin γ) (JordanWigner.extendFin β) 1 0 = 0) :
    JordanWigner.epsilonMode (n : JordanWigner.WaveVectorABC P) γ β = 0 := by
  rw [JordanWigner.geometric_form]
  have hbridge := blochZ_Uk_fin P (JordanWigner.waveVectorABC P n) γ β
  rw [show (JordanWigner.waveVectorABC P (n : JordanWigner.WaveVectorABC P))
      = JordanWigner.waveVectorABC P n from rfl]
  rw [← hbridge]
  rw [bHat_dot_blochZ_of_W_col_zero (JordanWigner.waveVectorABC P n) _
    (colNormSq_Uk P _ _ _) hG]
  ring

end

end QAOA.IsingChain.Achievability
