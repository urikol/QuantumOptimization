import QuantumOptimization.QAOA.IsingChain.Achievability.Su2Class

/-!
# Haah product decomposition — the converse QSP existence step (`w`-polynomial form)

Every member `(a, b)` of the SU(2) Laurent class `IsClassL L` factors as a constant
diagonal phase times a product of `L` primitive equatorial factors `primFactor φⱼ`:

`classMat L a b = diagPhaseMat χ * (List.ofFn fun j => primFactor (φ j)).prod`.

This is the polynomial avatar of Haah's `thm:composition` converse (arXiv:1806.10236,
`composeSignal`, l.268–399) specialised to the parity-constrained (reciprocal-diagonal /
anti-reciprocal-off-diagonal) class, where the projectors are forced onto the equator.

The proof is **pure polynomial algebra** — no trigonometry, no `epsilonMode`. It is a
strong induction on `L`:

* **(F0)** top-coefficient balance `‖a.coeff L‖² = ‖b.coeff L‖²` from unitarity;
* **(F1)** base case `L = 0`: a constant unimodular diagonal phase;
* **(F2)** non-degenerate step (`(a.coeff (L+1), b.coeff (L+1)) ≠ 0`): peel the rightmost
  primitive factor `primFactor (φ + π)` with `e := −a_top / conj b_top`, both extreme
  coefficients of the peeled combination vanish, divide by `X`, recurse;
* **(F3)** degenerate step (`a.coeff (L+1) = b.coeff (L+1) = 0`): then `X ∣ a`, `X ∣ b`;
  recurse on `(a/X, b/X) ∈ IsClassL (L−1)` and pad two trivial factors
  (`primFactor ψ * primFactor (ψ+π) = X • 1`).

φ-ordering convention: the product is `List.ofFn (fun j : Fin L => primFactor (φ j))`,
peeled **right-to-left** — `primFactor (φ (Fin.last))` is the factor removed first.

## Main statement
- `exists_primFactor_decomposition` — the product decomposition (frozen interface for
  `Angles.lean`).
-/

namespace QAOA.IsingChain.Achievability

open Polynomial

noncomputable section

-- ============================================================================
-- (F-coeff) Coefficient lemmas for palindromy / antipalindromy and `Cstar`
-- ============================================================================

/-- Palindromy at the coefficient level: `reflect L a = a` gives
`a.coeff (L − j) = a.coeff j` for `j ≤ L`. -/
theorem coeff_of_palin {L : ℕ} {a : Polynomial ℂ} (h : Polynomial.reflect L a = a)
    {j : ℕ} (hj : j ≤ L) : a.coeff (L - j) = a.coeff j := by
  have := congrArg (fun p => p.coeff j) h
  simpa only [coeff_reflect, revAt_le hj] using this

/-- Antipalindromy at the coefficient level: `reflect L b = −b` gives
`b.coeff (L − j) = −b.coeff j` for `j ≤ L`. -/
theorem coeff_of_anti {L : ℕ} {b : Polynomial ℂ} (h : Polynomial.reflect L b = -b)
    {j : ℕ} (hj : j ≤ L) : b.coeff (L - j) = -b.coeff j := by
  have := congrArg (fun p => p.coeff j) h
  simpa only [coeff_reflect, revAt_le hj, coeff_neg] using this

/-- `Cstar L x` has `natDegree ≤ L` whenever `x` does. -/
theorem Cstar_natDegree_le (L : ℕ) (x : Polynomial ℂ) (hx : x.natDegree ≤ L) :
    (Cstar L x).natDegree ≤ L := by
  unfold Cstar
  refine le_trans natDegree_reflect_le ?_
  rw [natDegree_map_eq_of_injective (RingHom.injective _)]
  exact max_le le_rfl hx

/-- Top coefficient of a product when both factors have degree `≤ L`: the convolution at
`2L` collapses to the single product of top coefficients. -/
theorem coeff_mul_two_mul (L : ℕ) (x y : Polynomial ℂ) (hx : x.natDegree ≤ L)
    (hy : y.natDegree ≤ L) : (x * y).coeff (2 * L) = x.coeff L * y.coeff L := by
  rw [coeff_mul, Finset.sum_eq_single (L, L)]
  · intro c hc hne
    rw [Finset.mem_antidiagonal] at hc
    rcases lt_trichotomy c.1 L with hlt | heq | hgt
    · have : c.2 > L := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hy this)]; ring
    · exact absurd (Prod.ext_iff.mpr ⟨heq, by omega⟩) hne
    · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hx hgt)]; ring
  · intro h; exact absurd (Finset.mem_antidiagonal.mpr (by omega)) h

/-- `(Cstar L a).coeff L = conj (a.coeff 0)` (the top coefficient of `Cstar` reads the
constant of `a`). -/
theorem Cstar_coeff_top (L : ℕ) (a : Polynomial ℂ) :
    (Cstar L a).coeff L = (starRingEnd ℂ) (a.coeff 0) := by
  rw [Cstar_coeff, revAt_le (le_refl L), Nat.sub_self]

-- ============================================================================
-- (F0) Top-coefficient balance from unitarity
-- ============================================================================

/-- **(F0) Top-coefficient balance.** For a class member at degree `L > 0`, the top
coefficients of `a` and `b` have equal modulus:
`Complex.normSq (a.coeff L) = Complex.normSq (b.coeff L)`. -/
theorem normSq_coeff_top_eq {L : ℕ} {a b : Polynomial ℂ} (h : IsClassL L a b) (hL : 0 < L) :
    Complex.normSq (a.coeff L) = Complex.normSq (b.coeff L) := by
  -- Take the coefficient at `2L` of the unitarity identity.
  have hcoeff := congrArg (fun p => p.coeff (2 * L)) h.unitarity
  simp only at hcoeff
  rw [coeff_add,
    coeff_mul_two_mul L a (Cstar L a) h.degA (Cstar_natDegree_le L a h.degA),
    coeff_mul_two_mul L b (Cstar L b) h.degB (Cstar_natDegree_le L b h.degB),
    Cstar_coeff_top, Cstar_coeff_top] at hcoeff
  -- `(X^L).coeff (2L) = 0` since `2L ≠ L` for `L > 0`.
  rw [coeff_X_pow, if_neg (by omega)] at hcoeff
  -- palin: `a.coeff 0 = a.coeff L`; anti: `b.coeff 0 = −b.coeff L`.
  have hpa : a.coeff 0 = a.coeff L := by
    have := coeff_of_palin h.palinA (le_refl L); rwa [Nat.sub_self] at this
  have hpb : b.coeff 0 = -b.coeff L := by
    have := coeff_of_anti h.antiB (le_refl L); rwa [Nat.sub_self] at this
  rw [hpa, hpb] at hcoeff
  -- Now `a_top * conj a_top + b_top * conj (−b_top) = 0`, i.e. `normSq a − normSq b = 0`.
  rw [map_neg, mul_neg] at hcoeff
  have key : ((Complex.normSq (a.coeff L) : ℂ) - (Complex.normSq (b.coeff L) : ℂ)) = 0 := by
    rw [← Complex.mul_conj (a.coeff L), ← Complex.mul_conj (b.coeff L)]
    linear_combination hcoeff
  have hreal : (Complex.normSq (a.coeff L) - Complex.normSq (b.coeff L) : ℝ) = 0 := by
    have := key; push_cast at this; exact_mod_cast this
  linarith

-- ============================================================================
-- Phase extraction and the `primFactor` / `equatorialProj` algebra
-- ============================================================================

/-- Every unit-modulus complex number is `Complex.exp (φ * I)` for a real `φ`
(`φ := arg z`). -/
theorem exists_phase_of_norm_one (z : ℂ) (hz : ‖z‖ = 1) :
    ∃ φ : ℝ, Complex.exp (↑φ * Complex.I) = z := by
  refine ⟨z.arg, ?_⟩
  have := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at this
  simpa using this

/-- `exp ((φ + π) I) = − exp (φ I)`. -/
theorem exp_add_pi (φ : ℝ) :
    Complex.exp ((↑φ + ↑Real.pi) * Complex.I) = - Complex.exp (↑φ * Complex.I) := by
  rw [show ((↑φ + ↑Real.pi) * Complex.I : ℂ) = (↑φ * Complex.I) + (↑Real.pi * Complex.I) by
    ring, Complex.exp_add, Complex.exp_pi_mul_I]; ring

/-- `exp (−(φ + π) I) = − exp (−φ I)`. -/
theorem exp_neg_pi (φ : ℝ) :
    Complex.exp (-(↑φ + ↑Real.pi) * Complex.I) = - Complex.exp (-↑φ * Complex.I) := by
  rw [show (-(↑φ + ↑Real.pi) * Complex.I : ℂ) = (-↑φ * Complex.I) + (-↑Real.pi * Complex.I) by
    ring, Complex.exp_add, neg_mul (Real.pi:ℂ), Complex.exp_neg, Complex.exp_pi_mul_I]; ring

/-- `equatorialProj (φ + π) = 1 − equatorialProj φ` (the equatorial complement). -/
theorem equatorialProj_add_pi (φ : ℝ) :
    equatorialProj (φ + Real.pi) = 1 - equatorialProj φ := by
  unfold equatorialProj
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.cons_val',
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.of_apply, Fin.mk_one, Fin.isValue]
  · norm_num
  · push_cast; rw [exp_neg_pi φ]; ring
  · push_cast; rw [exp_add_pi φ]; ring
  · norm_num

/-- Entry `(0,0)` of the primitive factor: `½(X + 1)`. -/
theorem primFactor_apply_zero_zero (φ : ℝ) :
    primFactor φ 0 0 = Polynomial.C (1/2) * (Polynomial.X + 1) := by
  unfold primFactor equatorialProj
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.of_apply, Fin.isValue, if_true, mul_add, mul_one]
  rw [show (1 - 1/2 : ℂ) = 1/2 by ring]

/-- Entry `(0,1)` of the primitive factor: `½ e^{−iφ}(X − 1)`. -/
theorem primFactor_apply_zero_one (φ : ℝ) :
    primFactor φ 0 1 = Polynomial.C (Complex.exp (-↑φ * Complex.I)/2) * (Polynomial.X - 1) := by
  unfold primFactor equatorialProj
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, if_neg (by decide : ¬(0:Fin 2)=1),
    zero_sub, mul_sub, mul_one, map_neg]
  ring

/-- Entry `(1,0)` of the primitive factor: `½ e^{iφ}(X − 1)`. -/
theorem primFactor_apply_one_zero (φ : ℝ) :
    primFactor φ 1 0 = Polynomial.C (Complex.exp (↑φ * Complex.I)/2) * (Polynomial.X - 1) := by
  unfold primFactor equatorialProj
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, if_neg (by decide : ¬(1:Fin 2)=0),
    zero_sub, mul_sub, mul_one, map_neg]
  ring

/-- Entry `(1,1)` of the primitive factor: `½(X + 1)`. -/
theorem primFactor_apply_one_one (φ : ℝ) :
    primFactor φ 1 1 = Polynomial.C (1/2) * (Polynomial.X + 1) := by
  unfold primFactor equatorialProj
  simp only [Matrix.add_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.cons_val', Matrix.cons_val_one, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, if_true, mul_add, mul_one]
  rw [show (1 - 1/2 : ℂ) = 1/2 by ring]

-- ============================================================================
-- Reflection/`Cstar` shift lemmas (for the degenerate step)
-- ============================================================================

/-- `reflect (N+1) (X * p) = reflect N p` when `natDegree p ≤ N`. -/
theorem reflect_X_mul_of_le {N : ℕ} {p : Polynomial ℂ} (hp : p.natDegree ≤ N) :
    Polynomial.reflect (N+1) (Polynomial.X * p) = Polynomial.reflect N p := by
  ext n
  rw [coeff_reflect, coeff_reflect]
  rcases Nat.lt_or_ge n (N+1) with h | h
  · have hn : n ≤ N := by omega
    rw [revAt_le (le_of_lt h), revAt_le hn, show N+1-n = (N-n)+1 by omega, coeff_X_mul]
  · rw [revAt_eq_self_of_lt (by omega : N < n)]
    rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [← heq, revAt_le (le_refl (N+1)), Nat.sub_self, coeff_X_mul_zero]
      exact (coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < N+1)).symm
    · rw [revAt_eq_self_of_lt (by omega : N+1 < n), show n = (n-1)+1 by omega, coeff_X_mul,
          coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n-1),
          coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < (n-1)+1)]

/-- `reflect (N+1) p = X * reflect N p` when `natDegree p ≤ N` (the trailing coefficient is
zero, so reflection picks up a factor of `X`). -/
theorem reflect_of_natDegree_le {N : ℕ} {p : Polynomial ℂ} (hp : p.natDegree ≤ N) :
    Polynomial.reflect (N+1) p = Polynomial.X * Polynomial.reflect N p := by
  ext n
  rw [coeff_reflect]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [revAt_zero, coeff_X_mul_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < N+1)
  · rw [show n = (n-1)+1 by omega, coeff_X_mul, coeff_reflect]
    rcases Nat.lt_or_ge n (N+1) with h | h
    · rw [revAt_le (by omega : (n-1)+1 ≤ N+1), revAt_le (by omega : n-1 ≤ N),
          show N+1-((n-1)+1) = N-(n-1) by omega]
    · rcases Nat.eq_or_lt_of_le h with heq | hlt
      · rw [show (revAt (N+1)) ((n-1)+1) = 0 by
              rw [show (n-1)+1 = N+1 by omega, revAt_le (le_refl _), Nat.sub_self],
            show (revAt N) (n-1) = 0 by
              rw [revAt_le (by omega : n-1 ≤ N), show N-(n-1) = 0 by omega]]
      · rw [revAt_eq_self_of_lt (by omega : N+1 < (n-1)+1), revAt_eq_self_of_lt (by omega : N < n-1),
            coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < (n-1)+1),
            coeff_eq_zero_of_natDegree_lt (by omega : p.natDegree < n-1)]

/-- `Cstar (L+1) (X * p) = X * Cstar (L−1) p` when `natDegree p ≤ L−1` and `L ≥ 1`. -/
theorem Cstar_X_mul {L : ℕ} {p : Polynomial ℂ} (hp : p.natDegree ≤ L - 1) (hL : 1 ≤ L) :
    Cstar (L+1) (Polynomial.X * p) = Polynomial.X * Cstar (L-1) p := by
  unfold Cstar
  rw [Polynomial.map_mul, Polynomial.map_X]
  have hmapdeg : (p.map (starRingEnd ℂ)).natDegree ≤ L - 1 := by
    rw [natDegree_map_eq_of_injective (RingHom.injective _)]; exact hp
  have hmapdeg' : (p.map (starRingEnd ℂ)).natDegree ≤ L := le_trans hmapdeg (by omega)
  rw [reflect_X_mul_of_le hmapdeg']
  have hLeq : L = (L-1)+1 := by omega
  rw [hLeq]
  exact reflect_of_natDegree_le hmapdeg

-- ============================================================================
-- Determinant and the trivial-pair product identity
-- ============================================================================

/-- A reusable `C`-product fact: `C(1/2) * C(1/2) = C(1/4)`. -/
private theorem C_half_sq : Polynomial.C (1/2 : ℂ) * Polynomial.C (1/2:ℂ) = Polynomial.C (1/4) := by
  rw [← Polynomial.C_mul]; norm_num

/-- A reusable `C`-product fact: `C(e^{−iφ}/2) * C(e^{iφ}/2) = C(1/4)`. -/
private theorem C_exp_half_mul (φ : ℝ) :
    Polynomial.C (Complex.exp (-↑φ * Complex.I)/2) * Polynomial.C (Complex.exp (↑φ * Complex.I)/2)
      = Polynomial.C (1/4 : ℂ) := by
  rw [← Polynomial.C_mul]; congr 1
  rw [show (Complex.exp (-↑φ * Complex.I)/2 * (Complex.exp (↑φ * Complex.I)/2))
    = (Complex.exp (-↑φ * Complex.I) * Complex.exp (↑φ * Complex.I))/4 by ring, exp_neg_mul_exp]

/-- A reusable `C`-product fact: `C(1/4) * 4 = 1`. -/
private theorem C_quarter_mul_four : Polynomial.C (1/4 : ℂ) * 4 = 1 := by
  rw [show (4 : Polynomial ℂ) = Polynomial.C 4 by rw [map_ofNat], ← Polynomial.C_mul]; norm_num

/-- The determinant of a primitive factor is `X`. -/
theorem det_primFactor (φ : ℝ) : (primFactor φ).det = Polynomial.X := by
  rw [Matrix.det_fin_two, primFactor_apply_zero_zero, primFactor_apply_zero_one,
    primFactor_apply_one_zero, primFactor_apply_one_one]
  linear_combination (Polynomial.X + 1)*(Polynomial.X + 1) * C_half_sq
    - (Polynomial.X - 1)*(Polynomial.X - 1) * C_exp_half_mul φ + Polynomial.X * C_quarter_mul_four

/-- **The trivial-pair identity:** `primFactor φ * primFactor (φ + π) = X • 1`. The product
of a primitive factor with its equatorial complement is the scalar `X`. Used to pad two
factors in the degenerate step. -/
theorem primFactor_mul_compl (φ : ℝ) :
    primFactor φ * primFactor (φ + Real.pi) =
      (Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) := by
  have hCe : Polynomial.C (Complex.exp (↑(φ + Real.pi) * Complex.I) / 2)
      = - Polynomial.C (Complex.exp (↑φ * Complex.I) / 2) := by
    rw [← Polynomial.C_neg]; congr 1; push_cast; rw [exp_add_pi]; ring
  have hCe' : Polynomial.C (Complex.exp (-↑(φ + Real.pi) * Complex.I) / 2)
      = - Polynomial.C (Complex.exp (-↑φ * Complex.I) / 2) := by
    rw [← Polynomial.C_neg]; congr 1; push_cast; rw [exp_neg_pi]; ring
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one,
      primFactor_apply_zero_one, primFactor_apply_one_zero, primFactor_apply_one_one,
      primFactor_apply_zero_zero, if_true, if_neg (by decide : ¬(0:Fin 2)=1),
      if_neg (by decide : ¬(1:Fin 2)=0), mul_one, mul_zero, hCe, hCe']
  · linear_combination (Polynomial.X + 1)*(Polynomial.X + 1) * C_half_sq
      - (Polynomial.X - 1)*(Polynomial.X - 1) * C_exp_half_mul φ + Polynomial.X * C_quarter_mul_four
  · ring
  · ring
  · linear_combination (Polynomial.X + 1)*(Polynomial.X + 1) * C_half_sq
      - (Polynomial.X - 1)*(Polynomial.X - 1) * C_exp_half_mul φ + Polynomial.X * C_quarter_mul_four

-- ============================================================================
-- (F1) Base case `L = 0`
-- ============================================================================

/-- For a constant polynomial, `Cstar 0 a = C (conj (a.coeff 0))`. -/
theorem Cstar_zero_of_const (a : Polynomial ℂ) (ha : a.natDegree ≤ 0) :
    Cstar 0 a = Polynomial.C ((starRingEnd ℂ) (a.coeff 0)) := by
  ext n; rw [Cstar_coeff, Polynomial.coeff_C]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [revAt_eq_self_of_lt (by omega : 0 < n), if_neg (by omega : n ≠ 0),
        coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < n), map_zero]

/-- `reflect 0` fixes constant polynomials. -/
theorem reflect_zero_const (b : Polynomial ℂ) (_hb : b.natDegree ≤ 0) :
    Polynomial.reflect 0 b = b := by
  ext n; rw [coeff_reflect]
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp
  · rw [revAt_eq_self_of_lt (by omega : 0 < n)]

/-- **(F1) Base case.** A class member at `L = 0` is a constant diagonal phase: `b = 0`,
`a = C (e^{iχ})`, and `classMat 0 a b = diagPhaseMat χ` (the empty product is `1`). -/
theorem decomp_base (a b : Polynomial ℂ) (h : IsClassL 0 a b) :
    ∃ (φ : Fin 0 → ℝ) (χ : ℝ),
      classMat 0 a b = diagPhaseMat χ * (List.ofFn fun j : Fin 0 => primFactor (φ j)).prod := by
  have hb0 : b = 0 := by
    have h1 := h.antiB
    rw [reflect_zero_const b h.degB] at h1
    have h2 : (2:ℂ[X]) * b = 0 := by linear_combination h1
    rcases mul_eq_zero.mp h2 with h' | h'
    · exact absurd h' two_ne_zero
    · exact h'
  have ha : a = Polynomial.C (a.coeff 0) := eq_C_of_natDegree_le_zero h.degA
  have hns : a.coeff 0 * (starRingEnd ℂ) (a.coeff 0) = 1 := by
    have hu := h.unitarity
    rw [hb0, zero_mul, add_zero, pow_zero, Cstar_zero_of_const a h.degA, ha, ← Polynomial.C_mul,
        coeff_C_zero] at hu
    exact Polynomial.C_inj.mp (by rw [hu]; simp)
  have hnorm : ‖a.coeff 0‖ = 1 := by
    rw [Complex.mul_conj] at hns
    have hns2 : Complex.normSq (a.coeff 0) = 1 := by exact_mod_cast hns
    rw [Complex.normSq_eq_norm_sq] at hns2; nlinarith [norm_nonneg (a.coeff 0)]
  obtain ⟨χ, hχ⟩ := exists_phase_of_norm_one (a.coeff 0) hnorm
  refine ⟨Fin.elim0, χ, ?_⟩
  rw [show (List.ofFn fun j : Fin 0 => primFactor (Fin.elim0 j)).prod = 1 by simp, mul_one]
  unfold classMat diagPhaseMat
  rw [hb0]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, Fin.zero_eta,
      Fin.mk_one]
  · rw [ha, hχ]
  · simp [Cstar]
  · rw [Cstar_zero_of_const a h.degA, ← hχ, ← Complex.exp_conj]
    congr 2; rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; ring

-- ============================================================================
-- `divX` ergonomics and the trivial-pair padding
-- ============================================================================

/-- If a class member at `L+1` has a vanishing top coefficient, `divX` lands in degree
`≤ L − 1`. -/
theorem divX_natDegree_le {L : ℕ} (a : Polynomial ℂ) (hda : a.natDegree ≤ L + 1)
    (htop : a.coeff (L + 1) = 0) : (a.divX).natDegree ≤ L - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn; rw [coeff_divX]
  rcases Nat.lt_or_ge (n+1) (L+1) with h | h
  · omega
  · rcases Nat.eq_or_lt_of_le h with heq | hlt
    · rw [← heq]; exact htop
    · exact coeff_eq_zero_of_natDegree_lt (by omega)

/-- When `a.coeff 0 = 0`, `X * a.divX = a`. -/
theorem X_mul_divX_of_coeff_zero (a : Polynomial ℂ) (h0 : a.coeff 0 = 0) :
    Polynomial.X * a.divX = a := by
  conv_rhs => rw [← Polynomial.X_mul_divX_add a]
  rw [h0, map_zero, add_zero]

/-- Left cancellation of `X` on polynomials. -/
theorem X_mul_cancel {p q : Polynomial ℂ} (h : Polynomial.X * p = Polynomial.X * q) : p = q :=
  mul_left_cancel₀ Polynomial.X_ne_zero h

/-- `X • M = M * primFactor ψ * primFactor (ψ + π)` for any matrix `M` and phase `ψ`
(scaling by `X` is realized by two trivial factors). -/
theorem smul_X_eq_mul_primFactor_pair (M : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (ψ : ℝ) :
    (Polynomial.X : Polynomial ℂ) • M = M * primFactor ψ * primFactor (ψ + Real.pi) := by
  rw [Matrix.mul_assoc, primFactor_mul_compl, Matrix.mul_smul, Matrix.mul_one]

-- ============================================================================
-- Coefficient helpers for `(X ± 1) * p`
-- ============================================================================

/-- `((X + 1) * p).coeff 0 = p.coeff 0`. -/
theorem coeff_X_add_one_mul_zero (p : Polynomial ℂ) :
    ((Polynomial.X + 1) * p).coeff 0 = p.coeff 0 := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul_zero, zero_add]

/-- `((X − 1) * p).coeff 0 = −p.coeff 0`. -/
theorem coeff_X_sub_one_mul_zero (p : Polynomial ℂ) :
    ((Polynomial.X - 1) * p).coeff 0 = -p.coeff 0 := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul_zero, zero_sub]

/-- `((X + 1) * p).coeff (n+1) = p.coeff n + p.coeff (n+1)`. -/
theorem coeff_X_add_one_mul_succ (p : Polynomial ℂ) (n : ℕ) :
    ((Polynomial.X + 1) * p).coeff (n+1) = p.coeff n + p.coeff (n+1) := by
  rw [add_mul, one_mul, coeff_add, coeff_X_mul]

/-- `((X − 1) * p).coeff (n+1) = p.coeff n − p.coeff (n+1)`. -/
theorem coeff_X_sub_one_mul_succ (p : Polynomial ℂ) (n : ℕ) :
    ((Polynomial.X - 1) * p).coeff (n+1) = p.coeff n - p.coeff (n+1) := by
  rw [sub_mul, one_mul, coeff_sub, coeff_X_mul]

-- ============================================================================
-- Small reflection facts and the `Cstar`/`map`/palindromy identities
-- ============================================================================

/-- `reflect 1 (X + 1) = X + 1`. -/
theorem reflect_one_X_add_one :
    Polynomial.reflect 1 ((Polynomial.X : Polynomial ℂ) + 1) = Polynomial.X + 1 := by
  rw [reflect_add, show (Polynomial.X : Polynomial ℂ) = Polynomial.C 1 * Polynomial.X^1 by simp,
      reflect_C_mul_X_pow, revAt_le (le_refl 1), Nat.sub_self,
      show (1 : Polynomial ℂ) = Polynomial.C 1 * Polynomial.X^0 by simp, reflect_C_mul_X_pow,
      revAt_zero]; simp; ring

/-- `reflect 1 (X − 1) = −(X − 1)`. -/
theorem reflect_one_X_sub_one :
    Polynomial.reflect 1 ((Polynomial.X : Polynomial ℂ) - 1) = -(Polynomial.X - 1) := by
  rw [sub_eq_add_neg, reflect_add, reflect_neg,
      show (Polynomial.X : Polynomial ℂ) = Polynomial.C 1 * Polynomial.X^1 by simp,
      reflect_C_mul_X_pow, revAt_le (le_refl 1), Nat.sub_self,
      show (1 : Polynomial ℂ) = Polynomial.C 1 * Polynomial.X^0 by simp, reflect_C_mul_X_pow,
      revAt_zero]; simp

/-- From antipalindromy, `Cstar (L+1) b = −(b.map conj)`. -/
theorem Cstar_eq_neg_map (L : ℕ) (b : Polynomial ℂ) (hanti : Polynomial.reflect (L + 1) b = -b) :
    Cstar (L+1) b = - (b.map (starRingEnd ℂ)) := by
  unfold Cstar; rw [reflect_map, hanti, Polynomial.map_neg]

/-- From palindromy, `Cstar (L+1) a = a.map conj`. -/
theorem Cstar_eq_map_of_palin (L : ℕ) (a : Polynomial ℂ) (hpal : Polynomial.reflect (L + 1) a = a) :
    Cstar (L+1) a = a.map (starRingEnd ℂ) := by
  unfold Cstar; rw [reflect_map, hpal]

-- ============================================================================
-- (F3) Degenerate step infrastructure: divide out `X`, recurse, pad
-- ============================================================================

/-- **(F3) Degenerate descent.** If both top coefficients vanish then `X ∣ a, X ∣ b` and the
quotients `(a.divX, b.divX)` lie in `IsClassL (L−1)`. -/
theorem degenerate_class {L : ℕ} (hL : 1 ≤ L) {a b : Polynomial ℂ} (h : IsClassL (L + 1) a b)
    (hta : a.coeff (L + 1) = 0) (htb : b.coeff (L + 1) = 0) :
    IsClassL (L-1) a.divX b.divX := by
  have ha0 : a.coeff 0 = 0 := by
    have := coeff_of_palin h.palinA (le_refl (L+1)); rw [Nat.sub_self] at this; rw [this]; exact hta
  have hb0 : b.coeff 0 = 0 := by
    have := coeff_of_anti h.antiB (le_refl (L+1)); rw [Nat.sub_self] at this; rw [this, htb]; ring
  have hXa : Polynomial.X * a.divX = a := X_mul_divX_of_coeff_zero a ha0
  have hXb : Polynomial.X * b.divX = b := X_mul_divX_of_coeff_zero b hb0
  have hda1 : a.divX.natDegree ≤ L - 1 := divX_natDegree_le a h.degA hta
  have hdb1 : b.divX.natDegree ≤ L - 1 := divX_natDegree_le b h.degB htb
  refine ⟨hda1, hdb1, ?_, ?_, ?_⟩
  · have hu := h.unitarity
    rw [← hXa, ← hXb, Cstar_X_mul hda1 hL, Cstar_X_mul hdb1 hL] at hu
    rw [show L + 1 = 2 + (L - 1) by omega, pow_add] at hu
    have key : Polynomial.X^2 * (a.divX * Cstar (L-1) a.divX + b.divX * Cstar (L-1) b.divX)
        = Polynomial.X^2 * (Polynomial.X^(L-1)) := by ring_nf; ring_nf at hu; linear_combination hu
    exact mul_left_cancel₀ (pow_ne_zero 2 Polynomial.X_ne_zero) key
  · have hpa := h.palinA
    rw [← hXa, reflect_X_mul_of_le (by omega : a.divX.natDegree ≤ L),
        show L = (L-1)+1 by omega, reflect_of_natDegree_le hda1] at hpa
    exact X_mul_cancel hpa
  · have hab := h.antiB
    rw [← hXb, reflect_X_mul_of_le (by omega : b.divX.natDegree ≤ L),
        show L = (L-1)+1 by omega, reflect_of_natDegree_le hdb1, ← mul_neg] at hab
    exact X_mul_cancel hab

/-- **(F3) Degenerate reconstruction.** When both top coefficients vanish,
`classMat (L+1) a b = X • classMat (L−1) (a.divX) (b.divX)`. -/
theorem degenerate_recon {L : ℕ} (hL : 1 ≤ L) {a b : Polynomial ℂ} (h : IsClassL (L + 1) a b)
    (hta : a.coeff (L + 1) = 0) (htb : b.coeff (L + 1) = 0) :
    classMat (L+1) a b = (Polynomial.X : Polynomial ℂ) • classMat (L-1) a.divX b.divX := by
  have ha0 : a.coeff 0 = 0 := by
    have := coeff_of_palin h.palinA (le_refl (L+1)); rw [Nat.sub_self] at this; rw [this]; exact hta
  have hb0 : b.coeff 0 = 0 := by
    have := coeff_of_anti h.antiB (le_refl (L+1)); rw [Nat.sub_self] at this; rw [this, htb]; ring
  have hXa : Polynomial.X * a.divX = a := X_mul_divX_of_coeff_zero a ha0
  have hXb : Polynomial.X * b.divX = b := X_mul_divX_of_coeff_zero b hb0
  have hda1 : a.divX.natDegree ≤ L - 1 := divX_natDegree_le a h.degA hta
  have hdb1 : b.divX.natDegree ≤ L - 1 := divX_natDegree_le b h.degB htb
  unfold classMat
  apply Matrix.ext; intro i j
  rw [Matrix.smul_apply]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, smul_eq_mul]
  · rw [hXa]
  · rw [mul_neg, ← Cstar_X_mul hdb1 hL, hXb]
  · rw [hXb]
  · rw [← Cstar_X_mul hda1 hL, hXa]

-- ============================================================================
-- (F2) Non-degenerate step: the explicit peel
-- ============================================================================

/-- The peel numerator for `a`: `(X+1)a − (X−1)·e·(Cstar (L+1) b)`. -/
def comboA (L : ℕ) (a b : Polynomial ℂ) (e : ℂ) : Polynomial ℂ :=
  (Polynomial.X + 1) * a - (Polynomial.X - 1) * ((Polynomial.C e) * Cstar (L+1) b)

/-- The peel numerator for `b`: `(X+1)b + (X−1)·e·(Cstar (L+1) a)`. -/
def comboB (L : ℕ) (a b : Polynomial ℂ) (e : ℂ) : Polynomial ℂ :=
  (Polynomial.X + 1) * b + (Polynomial.X - 1) * ((Polynomial.C e) * Cstar (L+1) a)

/-- The peeled `a` at level `L`: `½ · (comboA).divX`. -/
def aPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ) : Polynomial ℂ :=
  Polynomial.C (1/2) * (comboA L a b e).divX

/-- The peeled `b` at level `L`: `½ · (comboB).divX`. -/
def bPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ) : Polynomial ℂ :=
  Polynomial.C (1/2) * (comboB L a b e).divX

/-- `comboA` has vanishing constant term (peel divisibility), under the phase condition
`e·conj(b_top) = −a_top` and palindromy `a.coeff 0 = a_top`. -/
theorem comboA_coeff_zero (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hpa0 : a.coeff 0 = a.coeff (L + 1))
    (hphase : e * (starRingEnd ℂ) (b.coeff (L + 1)) = -a.coeff (L + 1)) :
    (comboA L a b e).coeff 0 = 0 := by
  unfold comboA
  rw [coeff_sub, coeff_X_add_one_mul_zero, coeff_X_sub_one_mul_zero, Polynomial.coeff_C_mul,
      Cstar_coeff, revAt_le (Nat.zero_le _), Nat.sub_zero, hpa0, hphase]; ring

/-- `comboB` has vanishing constant term, under `e·conj(a_top) = −b_top` and antipalindromy. -/
theorem comboB_coeff_zero (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hanti0 : b.coeff 0 = -b.coeff (L + 1))
    (hphase2 : e * (starRingEnd ℂ) (a.coeff (L + 1)) = -b.coeff (L + 1)) :
    (comboB L a b e).coeff 0 = 0 := by
  unfold comboB
  rw [coeff_add, coeff_X_add_one_mul_zero, coeff_X_sub_one_mul_zero, Polynomial.coeff_C_mul,
      Cstar_coeff, revAt_le (Nat.zero_le _), Nat.sub_zero, hanti0, hphase2]; ring

/-- `comboA` has degree `≤ L+2`. -/
theorem comboA_natDegree_le (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1) :
    (comboA L a b e).natDegree ≤ L+2 := by
  unfold comboA
  refine le_trans (natDegree_sub_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le ?_
    have : (Polynomial.X + 1 : Polynomial ℂ).natDegree ≤ 1 := by compute_degree
    omega
  · refine le_trans natDegree_mul_le ?_
    have h1 : (Polynomial.X - 1 : Polynomial ℂ).natDegree ≤ 1 := by compute_degree
    have h2 : ((Polynomial.C e) * Cstar (L+1) b).natDegree ≤ L+1 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]; exact Cstar_natDegree_le _ _ hdb
    omega

/-- `comboB` has degree `≤ L+2`. -/
theorem comboB_natDegree_le (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1) :
    (comboB L a b e).natDegree ≤ L+2 := by
  unfold comboB
  refine le_trans (natDegree_add_le _ _) (max_le ?_ ?_)
  · refine le_trans natDegree_mul_le ?_
    have : (Polynomial.X + 1 : Polynomial ℂ).natDegree ≤ 1 := by compute_degree
    omega
  · refine le_trans natDegree_mul_le ?_
    have h1 : (Polynomial.X - 1 : Polynomial ℂ).natDegree ≤ 1 := by compute_degree
    have h2 : ((Polynomial.C e) * Cstar (L+1) a).natDegree ≤ L+1 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]; exact Cstar_natDegree_le _ _ hda
    omega

/-- `comboA`'s top (`X^{L+2}`) coefficient vanishes (the degree-drop / top-kill). -/
theorem comboA_top_kill (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hanti0 : b.coeff 0 = -b.coeff (L + 1))
    (hphase : e * (starRingEnd ℂ) (b.coeff (L + 1)) = -a.coeff (L + 1)) :
    (comboA L a b e).coeff (L+2) = 0 := by
  unfold comboA
  rw [coeff_sub, show L+2 = (L+1)+1 by rfl, coeff_X_add_one_mul_succ, coeff_X_sub_one_mul_succ,
      coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < L+2),
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Cstar_coeff, Cstar_coeff,
      revAt_le (le_refl (L+1)), Nat.sub_self, revAt_eq_self_of_lt (by omega : L+1 < L+2),
      coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < L+2), map_zero, mul_zero,
      hanti0, map_neg, mul_neg, hphase]; ring

/-- `comboB`'s top coefficient vanishes. -/
theorem comboB_top_kill (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hpa0 : a.coeff 0 = a.coeff (L + 1))
    (hphase2 : e * (starRingEnd ℂ) (a.coeff (L + 1)) = -b.coeff (L + 1)) :
    (comboB L a b e).coeff (L+2) = 0 := by
  unfold comboB
  rw [coeff_add, show L+2 = (L+1)+1 by rfl, coeff_X_add_one_mul_succ, coeff_X_sub_one_mul_succ,
      coeff_eq_zero_of_natDegree_lt (by omega : b.natDegree < L+2),
      Polynomial.coeff_C_mul, Polynomial.coeff_C_mul, Cstar_coeff, Cstar_coeff,
      revAt_le (le_refl (L+1)), Nat.sub_self, revAt_eq_self_of_lt (by omega : L+1 < L+2),
      coeff_eq_zero_of_natDegree_lt (by omega : a.natDegree < L+2), map_zero, mul_zero,
      hpa0, hphase2]; ring

/-- `comboA` is palindromic at degree `L+2` (so the peel stays in the class). -/
theorem comboA_palin (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hpalA : Polynomial.reflect (L + 1) a = a) (hantiB : Polynomial.reflect (L + 1) b = -b) :
    Polynomial.reflect (L+2) (comboA L a b e) = comboA L a b e := by
  unfold comboA
  rw [reflect_sub]
  congr 1
  · rw [show L+2 = 1 + (L+1) by omega,
        reflect_mul _ _ (by compute_degree) hda, reflect_one_X_add_one, hpalA]
  · have hdg : ((Polynomial.C e) * Cstar (L+1) b).natDegree ≤ L+1 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]; exact Cstar_natDegree_le _ _ hdb
    rw [show L+2 = 1 + (L+1) by omega,
        reflect_mul _ _ (by compute_degree) hdg, reflect_one_X_sub_one, reflect_C_mul]
    have hrr : Polynomial.reflect (L+1) (Cstar (L+1) b) = b.map (starRingEnd ℂ) := by
      unfold Cstar; rw [reflect_reflect]
    rw [hrr, Cstar_eq_neg_map L b hantiB]; ring

/-- `comboB` is antipalindromic at degree `L+2`. -/
theorem comboB_anti (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hpalA : Polynomial.reflect (L + 1) a = a) (hantiB : Polynomial.reflect (L + 1) b = -b) :
    Polynomial.reflect (L+2) (comboB L a b e) = -(comboB L a b e) := by
  unfold comboB
  rw [reflect_add, neg_add]
  congr 1
  · rw [show L+2 = 1 + (L+1) by omega,
        reflect_mul _ _ (by compute_degree) hdb, reflect_one_X_add_one, hantiB]; ring
  · have hdg : ((Polynomial.C e) * Cstar (L+1) a).natDegree ≤ L+1 := by
      refine le_trans natDegree_mul_le ?_
      rw [natDegree_C, zero_add]; exact Cstar_natDegree_le _ _ hda
    rw [show L+2 = 1 + (L+1) by omega,
        reflect_mul _ _ (by compute_degree) hdg, reflect_one_X_sub_one, reflect_C_mul]
    have hrr : Polynomial.reflect (L+1) (Cstar (L+1) a) = a.map (starRingEnd ℂ) := by
      unfold Cstar; rw [reflect_reflect]
    rw [hrr, Cstar_eq_map_of_palin L a hpalA]; ring

/-- `comboA` has degree `≤ L+1` (degree `≤ L+2` plus the top-kill). -/
theorem comboA_natDegree_le_succ (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hanti0 : b.coeff 0 = -b.coeff (L + 1))
    (hphase : e * (starRingEnd ℂ) (b.coeff (L + 1)) = -a.coeff (L + 1)) :
    (comboA L a b e).natDegree ≤ L+1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
  rcases Nat.eq_or_lt_of_le (by omega : L+2 ≤ n) with heq | hlt
  · rw [← heq]; exact comboA_top_kill L a b e hda hdb hanti0 hphase
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (comboA_natDegree_le L a b e hda hdb) hlt)

/-- `comboB` has degree `≤ L+1`. -/
theorem comboB_natDegree_le_succ (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (hpa0 : a.coeff 0 = a.coeff (L + 1))
    (hphase2 : e * (starRingEnd ℂ) (a.coeff (L + 1)) = -b.coeff (L + 1)) :
    (comboB L a b e).natDegree ≤ L+1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
  rcases Nat.eq_or_lt_of_le (by omega : L+2 ≤ n) with heq | hlt
  · rw [← heq]; exact comboB_top_kill L a b e hda hdb hpa0 hphase2
  · exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (comboB_natDegree_le L a b e hda hdb) hlt)

/-- The peeled `aPeel` has degree `≤ L`. -/
theorem aPeel_natDegree_le (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (h0 : (comboA L a b e).coeff 0 = 0)
    (hanti0 : b.coeff 0 = -b.coeff (L + 1))
    (hphase : e * (starRingEnd ℂ) (b.coeff (L + 1)) = -a.coeff (L + 1)) :
    (aPeel L a b e).natDegree ≤ L := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
  have hX : Polynomial.X * aPeel L a b e = Polynomial.C (1/2) * comboA L a b e := by
    unfold aPeel
    rw [show Polynomial.X * (Polynomial.C (1/2) * (comboA L a b e).divX)
        = Polynomial.C (1/2) * (Polynomial.X * (comboA L a b e).divX) by ring,
        X_mul_divX_of_coeff_zero _ h0]
  have hcoeff : (aPeel L a b e).coeff n = (Polynomial.C (1/2:ℂ) * comboA L a b e).coeff (n+1) := by
    rw [← hX, coeff_X_mul]
  rw [hcoeff, Polynomial.coeff_C_mul]
  rcases Nat.eq_or_lt_of_le (by omega : L+2 ≤ n+1) with heq | hlt
  · rw [← heq, comboA_top_kill L a b e hda hdb hanti0 hphase, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (comboA_natDegree_le L a b e hda hdb) hlt),
        mul_zero]

/-- The peeled `bPeel` has degree `≤ L`. -/
theorem bPeel_natDegree_le (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hda : a.natDegree ≤ L + 1) (hdb : b.natDegree ≤ L + 1)
    (h0 : (comboB L a b e).coeff 0 = 0)
    (hpa0 : a.coeff 0 = a.coeff (L + 1))
    (hphase2 : e * (starRingEnd ℂ) (a.coeff (L + 1)) = -b.coeff (L + 1)) :
    (bPeel L a b e).natDegree ≤ L := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
  have hX : Polynomial.X * bPeel L a b e = Polynomial.C (1/2) * comboB L a b e := by
    unfold bPeel
    rw [show Polynomial.X * (Polynomial.C (1/2) * (comboB L a b e).divX)
        = Polynomial.C (1/2) * (Polynomial.X * (comboB L a b e).divX) by ring,
        X_mul_divX_of_coeff_zero _ h0]
  have hcoeff : (bPeel L a b e).coeff n = (Polynomial.C (1/2:ℂ) * comboB L a b e).coeff (n+1) := by
    rw [← hX, coeff_X_mul]
  rw [hcoeff, Polynomial.coeff_C_mul]
  rcases Nat.eq_or_lt_of_le (by omega : L+2 ≤ n+1) with heq | hlt
  · rw [← heq, comboB_top_kill L a b e hda hdb hpa0 hphase2, mul_zero]
  · rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (comboB_natDegree_le L a b e hda hdb) hlt),
        mul_zero]

/-- The peeled `aPeel` is palindromic at level `L`. -/
theorem aPeel_palin (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hdcomboA : (comboA L a b e).natDegree ≤ L + 1)
    (h0 : (comboA L a b e).coeff 0 = 0)
    (hpalcombo : Polynomial.reflect (L + 2) (comboA L a b e) = comboA L a b e) :
    Polynomial.reflect L (aPeel L a b e) = aPeel L a b e := by
  have hXc : Polynomial.X * (comboA L a b e).divX = comboA L a b e :=
    X_mul_divX_of_coeff_zero _ h0
  have hddivX : (comboA L a b e).divX.natDegree ≤ L := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
    rw [coeff_divX]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hrefl_combo : Polynomial.reflect (L+1) (comboA L a b e) = (comboA L a b e).divX := by
    have hstep : Polynomial.reflect (L+2) (comboA L a b e)
        = Polynomial.X * Polynomial.reflect (L+1) (comboA L a b e) := by
      rw [show L+2 = (L+1)+1 by rfl]; exact reflect_of_natDegree_le hdcomboA
    rw [hpalcombo] at hstep
    have hcomb : Polynomial.X * Polynomial.reflect (L+1) (comboA L a b e)
        = Polynomial.X * (comboA L a b e).divX := hstep.symm.trans hXc.symm
    exact X_mul_cancel hcomb
  have hrefl_divX : Polynomial.reflect L (comboA L a b e).divX = (comboA L a b e).divX := by
    have h1 : Polynomial.reflect (L+1) (Polynomial.X * (comboA L a b e).divX)
        = Polynomial.reflect L (comboA L a b e).divX := reflect_X_mul_of_le hddivX
    rw [hXc] at h1; rw [← h1, hrefl_combo]
  unfold aPeel; rw [reflect_C_mul, hrefl_divX]

/-- The peeled `bPeel` is antipalindromic at level `L`. -/
theorem bPeel_anti (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hdcomboB : (comboB L a b e).natDegree ≤ L + 1)
    (h0 : (comboB L a b e).coeff 0 = 0)
    (hanticombo : Polynomial.reflect (L + 2) (comboB L a b e) = -(comboB L a b e)) :
    Polynomial.reflect L (bPeel L a b e) = -(bPeel L a b e) := by
  have hXc : Polynomial.X * (comboB L a b e).divX = comboB L a b e :=
    X_mul_divX_of_coeff_zero _ h0
  have hddivX : (comboB L a b e).divX.natDegree ≤ L := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]; intro n hn
    rw [coeff_divX]; exact coeff_eq_zero_of_natDegree_lt (by omega)
  have hrefl_combo : Polynomial.reflect (L+1) (comboB L a b e) = -(comboB L a b e).divX := by
    have hstep : Polynomial.reflect (L+2) (comboB L a b e)
        = Polynomial.X * Polynomial.reflect (L+1) (comboB L a b e) := by
      rw [show L+2 = (L+1)+1 by rfl]; exact reflect_of_natDegree_le hdcomboB
    rw [hanticombo] at hstep
    have hcomb : Polynomial.X * Polynomial.reflect (L+1) (comboB L a b e)
        = Polynomial.X * (-(comboB L a b e).divX) := by
      rw [← hstep, mul_neg, hXc]
    exact X_mul_cancel hcomb
  have hrefl_divX : Polynomial.reflect L (comboB L a b e).divX = -(comboB L a b e).divX := by
    have h1 : Polynomial.reflect (L+1) (Polynomial.X * (comboB L a b e).divX)
        = Polynomial.reflect L (comboB L a b e).divX := reflect_X_mul_of_le hddivX
    rw [hXc] at h1; rw [← h1, hrefl_combo]
  unfold bPeel; rw [reflect_C_mul, hrefl_divX, mul_neg]

-- ============================================================================
-- (F2) The peel reconstruction `M · primFactor φ = X • M'` and unitarity'
-- ============================================================================

/-- `conj (e^{iφ}) = e^{−iφ}`. -/
theorem conj_exp_phase (φ : ℝ) :
    (starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)) = Complex.exp (-↑φ * Complex.I) := by
  rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]; ring_nf

/-- General-`L` palindromic form of `Cstar`. -/
theorem Cstar_eq_map_palin (L : ℕ) (p : Polynomial ℂ) (hpal : Polynomial.reflect L p = p) :
    Cstar L p = p.map (starRingEnd ℂ) := by unfold Cstar; rw [reflect_map, hpal]

/-- General-`L` antipalindromic form of `Cstar`. -/
theorem Cstar_eq_neg_map_anti (L : ℕ) (p : Polynomial ℂ) (hanti : Polynomial.reflect L p = -p) :
    Cstar L p = -(p.map (starRingEnd ℂ)) := by
  unfold Cstar; rw [reflect_map, hanti, Polynomial.map_neg]

/-- `divX` commutes with coefficient maps. -/
theorem divX_map (p : Polynomial ℂ) (f : ℂ →+* ℂ) : (p.divX).map f = (p.map f).divX := by
  ext n; rw [coeff_map, coeff_divX, coeff_divX, coeff_map]

/-- The conjugate of `comboA`: `comboA.map conj = (X+1)·conj(a) + (X−1)·conj(e)·b`
(using antipalindromy of `b`). -/
theorem comboA_map_conj (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hantiB : Polynomial.reflect (L + 1) b = -b) :
    (comboA L a b e).map (starRingEnd ℂ)
      = (Polynomial.X + 1) * (a.map (starRingEnd ℂ))
        + (Polynomial.X - 1) * ((Polynomial.C ((starRingEnd ℂ) e)) * b) := by
  unfold comboA
  rw [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
  have hcc : (Cstar (L+1) b).map (starRingEnd ℂ) = -b := by
    unfold Cstar; rw [reflect_map, map_map]
    have hid : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; exact Complex.conj_conj z
    rw [hid, Polynomial.map_id, hantiB]
  rw [hcc]; ring

/-- The conjugate of `comboB`: `comboB.map conj = (X+1)·conj(b) + (X−1)·conj(e)·a`
(using palindromy of `a`). -/
theorem comboB_map_conj (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hpalA : Polynomial.reflect (L + 1) a = a) :
    (comboB L a b e).map (starRingEnd ℂ)
      = (Polynomial.X + 1) * (b.map (starRingEnd ℂ))
        + (Polynomial.X - 1) * ((Polynomial.C ((starRingEnd ℂ) e)) * a) := by
  unfold comboB
  rw [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_mul, Polynomial.map_mul,
      Polynomial.map_add, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, Polynomial.map_C]
  have hcc : (Cstar (L+1) a).map (starRingEnd ℂ) = a := by
    unfold Cstar; rw [reflect_map, map_map]
    have hid : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := by
      ext z; exact Complex.conj_conj z
    rw [hid, Polynomial.map_id, hpalA]
  rw [hcc]

/-- `X · aPeel = ½ · comboA` (from `divX`). -/
theorem X_mul_aPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (h0 : (comboA L a b e).coeff 0 = 0) :
    Polynomial.X * aPeel L a b e = Polynomial.C (1/2) * comboA L a b e := by
  unfold aPeel
  rw [show Polynomial.X * (Polynomial.C (1/2) * (comboA L a b e).divX)
      = Polynomial.C (1/2) * (Polynomial.X * (comboA L a b e).divX) by ring,
      X_mul_divX_of_coeff_zero _ h0]

/-- `X · bPeel = ½ · comboB`. -/
theorem X_mul_bPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (h0 : (comboB L a b e).coeff 0 = 0) :
    Polynomial.X * bPeel L a b e = Polynomial.C (1/2) * comboB L a b e := by
  unfold bPeel
  rw [show Polynomial.X * (Polynomial.C (1/2) * (comboB L a b e).divX)
      = Polynomial.C (1/2) * (Polynomial.X * (comboB L a b e).divX) by ring,
      X_mul_divX_of_coeff_zero _ h0]

/-- `X · Cstar L aPeel = ½ · (comboA.map conj)` (from palindromy of `aPeel` + `divX`). -/
theorem X_mul_Cstar_aPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hpalAPeel : Polynomial.reflect L (aPeel L a b e) = aPeel L a b e)
    (hcombo0 : (comboA L a b e).coeff 0 = 0) :
    Polynomial.X * Cstar L (aPeel L a b e)
      = Polynomial.C (1/2) * (comboA L a b e).map (starRingEnd ℂ) := by
  rw [Cstar_eq_map_palin L (aPeel L a b e) hpalAPeel]
  unfold aPeel
  rw [Polynomial.map_mul, Polynomial.map_C, show (starRingEnd ℂ) (1/2 : ℂ) = 1/2 by
      rw [map_div₀, map_one, map_ofNat], divX_map,
      show Polynomial.X * (Polynomial.C (1/2) * ((comboA L a b e).map (starRingEnd ℂ)).divX)
        = Polynomial.C (1/2) * (Polynomial.X * ((comboA L a b e).map (starRingEnd ℂ)).divX) by ring]
  congr 1
  apply X_mul_divX_of_coeff_zero
  rw [coeff_map, hcombo0, map_zero]

/-- `X · Cstar L bPeel = −(½ · (comboB.map conj))` (from antipalindromy of `bPeel` + `divX`). -/
theorem X_mul_Cstar_bPeel (L : ℕ) (a b : Polynomial ℂ) (e : ℂ)
    (hantiBPeel : Polynomial.reflect L (bPeel L a b e) = -(bPeel L a b e))
    (hcombo0 : (comboB L a b e).coeff 0 = 0) :
    Polynomial.X * Cstar L (bPeel L a b e)
      = -(Polynomial.C (1/2) * (comboB L a b e).map (starRingEnd ℂ)) := by
  rw [Cstar_eq_neg_map_anti L (bPeel L a b e) hantiBPeel]
  unfold bPeel
  rw [Polynomial.map_mul, Polynomial.map_C, show (starRingEnd ℂ) (1/2 : ℂ) = 1/2 by
      rw [map_div₀, map_one, map_ofNat], divX_map,
      show Polynomial.X * (-(Polynomial.C (1/2) * ((comboB L a b e).map (starRingEnd ℂ)).divX))
        = -(Polynomial.C (1/2) * (Polynomial.X * ((comboB L a b e).map (starRingEnd ℂ)).divX)) by ring]
  congr 2
  apply X_mul_divX_of_coeff_zero
  rw [coeff_map, hcombo0, map_zero]

/-- **(F2) The peel equation.** `classMat (L+1) a b · primFactor φ = X • classMat L aPeel bPeel`
with `e = e^{iφ}`. -/
theorem peel_eq (L : ℕ) (a b : Polynomial ℂ) (φ : ℝ)
    (hXaP : Polynomial.X * aPeel L a b (Complex.exp (↑φ * Complex.I))
        = Polynomial.C (1 / 2) * comboA L a b (Complex.exp (↑φ * Complex.I)))
    (hXbP : Polynomial.X * bPeel L a b (Complex.exp (↑φ * Complex.I))
        = Polynomial.C (1 / 2) * comboB L a b (Complex.exp (↑φ * Complex.I)))
    (hXCa : Polynomial.X * Cstar L (aPeel L a b (Complex.exp (↑φ * Complex.I)))
        = Polynomial.C (1 / 2) * (comboA L a b (Complex.exp (↑φ * Complex.I))).map (starRingEnd ℂ))
    (hXCb : Polynomial.X * Cstar L (bPeel L a b (Complex.exp (↑φ * Complex.I)))
        = -(Polynomial.C (1 / 2) * (comboB L a b (Complex.exp (↑φ * Complex.I))).map (starRingEnd ℂ)))
    (hcombAconj : (comboA L a b (Complex.exp (↑φ * Complex.I))).map (starRingEnd ℂ)
        = (Polynomial.X + 1) * (a.map (starRingEnd ℂ))
          + (Polynomial.X - 1) * ((Polynomial.C ((starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)))) * b))
    (hcombBconj : (comboB L a b (Complex.exp (↑φ * Complex.I))).map (starRingEnd ℂ)
        = (Polynomial.X + 1) * (b.map (starRingEnd ℂ))
          + (Polynomial.X - 1) * ((Polynomial.C ((starRingEnd ℂ) (Complex.exp (↑φ * Complex.I)))) * a))
    (hCsa : Cstar (L + 1) a = a.map (starRingEnd ℂ))
    (hCsb : Cstar (L + 1) b = -(b.map (starRingEnd ℂ))) :
    classMat (L+1) a b * primFactor φ
      = (Polynomial.X : Polynomial ℂ) • classMat L (aPeel L a b (Complex.exp (↑φ * Complex.I)))
          (bPeel L a b (Complex.exp (↑φ * Complex.I))) := by
  set e := Complex.exp (↑φ * Complex.I) with he
  apply Matrix.ext; intro i j
  rw [Matrix.smul_apply]
  unfold classMat
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue, Fin.zero_eta,
      Fin.mk_one, smul_eq_mul, primFactor_apply_zero_zero, primFactor_apply_zero_one,
      primFactor_apply_one_zero, primFactor_apply_one_one]
  · rw [hXaP]; unfold comboA
    rw [show Polynomial.C (Complex.exp (↑φ * Complex.I)/2) = Polynomial.C (1/2:ℂ) * Polynomial.C e by
      rw [← Polynomial.C_mul]; congr 1; rw [he]; ring]
    ring
  · rw [mul_neg, hXCb, hcombBconj, hCsb,
        show Polynomial.C (Complex.exp (-↑φ * Complex.I)/2) = Polynomial.C (1/2:ℂ) * Polynomial.C ((starRingEnd ℂ) e) by
          rw [← Polynomial.C_mul]; congr 1; rw [he, conj_exp_phase]; ring]
    ring
  · rw [hXbP]; unfold comboB
    rw [show Polynomial.C (Complex.exp (↑φ * Complex.I)/2) = Polynomial.C (1/2:ℂ) * Polynomial.C e by
      rw [← Polynomial.C_mul]; congr 1; rw [he]; ring]
    ring
  · rw [hXCa, hcombAconj, hCsa,
        show Polynomial.C (Complex.exp (-↑φ * Complex.I)/2) = Polynomial.C (1/2:ℂ) * Polynomial.C ((starRingEnd ℂ) e) by
          rw [← Polynomial.C_mul]; congr 1; rw [he, conj_exp_phase]; ring]
    ring

/-- Left cancellation of `X` on a `2×2` matrix of polynomials. -/
theorem smul_X_cancel {A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)}
    (h : (Polynomial.X : Polynomial ℂ) • A = (Polynomial.X : Polynomial ℂ) • B) : A = B := by
  apply Matrix.ext; intro i j
  have := congrFun (congrFun h i) j
  rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at this
  exact X_mul_cancel this

/-- The reconstruction `M = M' · primFactor (φ + π)` from the peel equation
`M · primFactor φ = X • M'`. -/
theorem recon_of_peel_eq (M M' : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) (φ : ℝ)
    (hpe : M * primFactor φ = (Polynomial.X : Polynomial ℂ) • M') :
    M = M' * primFactor (φ + Real.pi) := by
  apply smul_X_cancel (A := M) (B := M' * primFactor (φ + Real.pi))
  calc (Polynomial.X : Polynomial ℂ) • M
      = M * ((Polynomial.X : Polynomial ℂ) • (1 : Matrix (Fin 2) (Fin 2) (Polynomial ℂ))) := by
        rw [Matrix.mul_smul, Matrix.mul_one]
    _ = M * (primFactor φ * primFactor (φ + Real.pi)) := by rw [primFactor_mul_compl]
    _ = (M * primFactor φ) * primFactor (φ + Real.pi) := by rw [Matrix.mul_assoc]
    _ = ((Polynomial.X : Polynomial ℂ) • M') * primFactor (φ + Real.pi) := by rw [hpe]
    _ = (Polynomial.X : Polynomial ℂ) • (M' * primFactor (φ + Real.pi)) := by rw [Matrix.smul_mul]

/-- **(F2) Unitarity of the peeled pair**, obtained from the reconstruction by taking
determinants (`det M = X^{L+1}`, `det (primFactor) = X`). -/
theorem unitarity_peel (L : ℕ) (a b aP bP : Polynomial ℂ) (φ : ℝ)
    (h : IsClassL (L + 1) a b)
    (hrecon : classMat (L + 1) a b = classMat L aP bP * primFactor (φ + Real.pi)) :
    aP * Cstar L aP + bP * Cstar L bP = Polynomial.X ^ L := by
  have hdet := congrArg Matrix.det hrecon
  rw [det_classMat (L+1) a b h, Matrix.det_mul, det_primFactor, Matrix.det_fin_two] at hdet
  unfold classMat at hdet
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply, Fin.isValue] at hdet
  have hX : (aP * Cstar L aP + bP * Cstar L bP) * Polynomial.X = Polynomial.X^L * Polynomial.X := by
    rw [← pow_succ, hdet]; ring
  exact mul_right_cancel₀ Polynomial.X_ne_zero hX

-- ============================================================================
-- (F2) Phase selection and the second phase relation
-- ============================================================================

/-- Equal `normSq` ⟹ equal norms. -/
theorem norm_eq_of_normSq_eq {z w : ℂ} (h : Complex.normSq z = Complex.normSq w) : ‖z‖ = ‖w‖ := by
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at h
  nlinarith [norm_nonneg z, norm_nonneg w]

/-- In the non-degenerate case (not both top coefficients zero), the `normSq` balance forces
both to be nonzero. -/
theorem both_ne_zero (atop btop : ℂ) (hbal : Complex.normSq atop = Complex.normSq btop)
    (hnd : ¬(atop = 0 ∧ btop = 0)) : atop ≠ 0 ∧ btop ≠ 0 := by
  constructor
  · intro h0; apply hnd; refine ⟨h0, ?_⟩
    rw [h0, map_zero] at hbal; rw [← Complex.normSq_eq_zero, ← hbal]
  · intro h0; apply hnd; refine ⟨?_, h0⟩
    rw [h0, map_zero] at hbal; rw [← Complex.normSq_eq_zero, hbal]

/-- The peel phase `−a_top / conj(b_top)` is unit-modulus (by the balance). -/
theorem norm_peel_phase (atop btop : ℂ) (hbne : btop ≠ 0)
    (hbal : Complex.normSq atop = Complex.normSq btop) :
    ‖- atop / (starRingEnd ℂ) btop‖ = 1 := by
  rw [norm_div, norm_neg, Complex.norm_conj, norm_eq_of_normSq_eq hbal]
  field_simp

/-- The second phase relation `e·conj(a_top) = −b_top` from `e·conj(b_top) = −a_top` and the
balance `normSq a_top = normSq b_top`. -/
theorem phase_relation_two {e atop btop : ℂ} (hbne : btop ≠ 0)
    (hphase : e * (starRingEnd ℂ) btop = -atop)
    (hbal : Complex.normSq atop = Complex.normSq btop) :
    e * (starRingEnd ℂ) atop = - btop := by
  have hbalC : atop * (starRingEnd ℂ) atop = btop * (starRingEnd ℂ) btop := by
    rw [Complex.mul_conj, Complex.mul_conj]; exact_mod_cast congrArg Complex.ofReal hbal
  have hcbne : (starRingEnd ℂ) btop ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact hbne
  have key : (e * (starRingEnd ℂ) atop) * (starRingEnd ℂ) btop = (- btop) * (starRingEnd ℂ) btop := by
    calc (e * (starRingEnd ℂ) atop) * (starRingEnd ℂ) btop
        = (e * (starRingEnd ℂ) btop) * (starRingEnd ℂ) atop := by ring
      _ = (- atop) * (starRingEnd ℂ) atop := by rw [hphase]
      _ = - (atop * (starRingEnd ℂ) atop) := by ring
      _ = - (btop * (starRingEnd ℂ) btop) := by rw [hbalC]
      _ = (- btop) * (starRingEnd ℂ) btop := by ring
  exact mul_right_cancel₀ hcbne key

-- ============================================================================
-- (F2) / (F3) The two induction steps and (F-main) the strong induction
-- ============================================================================

/-- **(F2) Non-degenerate step.** Given the decomposition at level `L`, peel one factor and
extend it to a decomposition at level `L+1`, when not both top coefficients vanish. -/
theorem decomp_nondegen (L : ℕ)
    (IH : ∀ a b : Polynomial ℂ, IsClassL L a b →
      ∃ (φ : Fin L → ℝ) (χ : ℝ),
        classMat L a b = diagPhaseMat χ * (List.ofFn fun j : Fin L => primFactor (φ j)).prod)
    (a b : Polynomial ℂ) (h : IsClassL (L+1) a b)
    (hnd : ¬(a.coeff (L+1) = 0 ∧ b.coeff (L+1) = 0)) :
    ∃ (φ : Fin (L+1) → ℝ) (χ : ℝ),
      classMat (L+1) a b
        = diagPhaseMat χ * (List.ofFn fun j : Fin (L+1) => primFactor (φ j)).prod := by
  have hbal : Complex.normSq (a.coeff (L+1)) = Complex.normSq (b.coeff (L+1)) :=
    normSq_coeff_top_eq h (by omega)
  obtain ⟨hane, hbne⟩ := both_ne_zero _ _ hbal hnd
  obtain ⟨φ, hφ⟩ := exists_phase_of_norm_one (- a.coeff (L+1) / (starRingEnd ℂ) (b.coeff (L+1)))
    (norm_peel_phase _ _ hbne hbal)
  set e := Complex.exp (↑φ * Complex.I) with he
  have hcbne : (starRingEnd ℂ) (b.coeff (L+1)) ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact hbne
  have hphase : e * (starRingEnd ℂ) (b.coeff (L+1)) = - a.coeff (L+1) := by
    rw [hφ, div_mul_cancel₀ _ hcbne]
  have hphase2 : e * (starRingEnd ℂ) (a.coeff (L+1)) = - b.coeff (L+1) :=
    phase_relation_two hbne hphase hbal
  have hpa0 : a.coeff 0 = a.coeff (L+1) := by
    have := coeff_of_palin h.palinA (le_refl (L+1)); rwa [Nat.sub_self] at this
  have hanti0 : b.coeff 0 = - b.coeff (L+1) := by
    have := coeff_of_anti h.antiB (le_refl (L+1)); rwa [Nat.sub_self] at this
  have hcA0 : (comboA L a b e).coeff 0 = 0 := comboA_coeff_zero L a b e hpa0 hphase
  have hcB0 : (comboB L a b e).coeff 0 = 0 := comboB_coeff_zero L a b e hanti0 hphase2
  have hdcA : (comboA L a b e).natDegree ≤ L+1 :=
    comboA_natDegree_le_succ L a b e h.degA h.degB hanti0 hphase
  have hdcB : (comboB L a b e).natDegree ≤ L+1 :=
    comboB_natDegree_le_succ L a b e h.degA h.degB hpa0 hphase2
  have hpcA : Polynomial.reflect (L+2) (comboA L a b e) = comboA L a b e :=
    comboA_palin L a b e h.degA h.degB h.palinA h.antiB
  have hacB : Polynomial.reflect (L+2) (comboB L a b e) = -(comboB L a b e) :=
    comboB_anti L a b e h.degA h.degB h.palinA h.antiB
  have hpalAP : Polynomial.reflect L (aPeel L a b e) = aPeel L a b e :=
    aPeel_palin L a b e hdcA hcA0 hpcA
  have hantiBP : Polynomial.reflect L (bPeel L a b e) = -(bPeel L a b e) :=
    bPeel_anti L a b e hdcB hcB0 hacB
  have hCsa : Cstar (L+1) a = a.map (starRingEnd ℂ) := Cstar_eq_map_of_palin L a h.palinA
  have hCsb : Cstar (L+1) b = -(b.map (starRingEnd ℂ)) := Cstar_eq_neg_map L b h.antiB
  have hpe : classMat (L+1) a b * primFactor φ
      = (Polynomial.X : Polynomial ℂ) • classMat L (aPeel L a b e) (bPeel L a b e) :=
    peel_eq L a b φ (X_mul_aPeel L a b e hcA0) (X_mul_bPeel L a b e hcB0)
      (X_mul_Cstar_aPeel L a b e hpalAP hcA0) (X_mul_Cstar_bPeel L a b e hantiBP hcB0)
      (comboA_map_conj L a b e h.antiB) (comboB_map_conj L a b e h.palinA) hCsa hCsb
  have hrecon : classMat (L+1) a b
      = classMat L (aPeel L a b e) (bPeel L a b e) * primFactor (φ + Real.pi) :=
    recon_of_peel_eq _ _ φ hpe
  have hunit : aPeel L a b e * Cstar L (aPeel L a b e) + bPeel L a b e * Cstar L (bPeel L a b e)
      = Polynomial.X ^ L := unitarity_peel L a b _ _ φ h hrecon
  have hclassP : IsClassL L (aPeel L a b e) (bPeel L a b e) :=
    ⟨aPeel_natDegree_le L a b e h.degA h.degB hcA0 hanti0 hphase,
     bPeel_natDegree_le L a b e h.degA h.degB hcB0 hpa0 hphase2, hunit, hpalAP, hantiBP⟩
  obtain ⟨φ', χ, hdecomp⟩ := IH (aPeel L a b e) (bPeel L a b e) hclassP
  refine ⟨Fin.snoc φ' (φ + Real.pi), χ, ?_⟩
  rw [hrecon, hdecomp, List.ofFn_succ_last, List.prod_append, List.prod_singleton]
  have hsnoc_cast : ∀ i : Fin L, (Fin.snoc φ' (φ + Real.pi) : Fin (L+1) → ℝ) i.castSucc = φ' i := by
    intro i; rw [Fin.snoc_castSucc]
  have hsnoc_last : (Fin.snoc φ' (φ + Real.pi) : Fin (L+1) → ℝ) (Fin.last L) = φ + Real.pi := by
    rw [Fin.snoc_last]
  simp only [hsnoc_cast, hsnoc_last]
  rw [Matrix.mul_assoc]

/-- **(F3) Degenerate step.** When both top coefficients vanish, descend by `divX` to level
`L−1`, apply the (strong) induction hypothesis, and pad two trivial factors. -/
theorem decomp_degen (L : ℕ)
    (IHs : ∀ m, m < L + 1 → ∀ a b : Polynomial ℂ, IsClassL m a b →
      ∃ (φ : Fin m → ℝ) (χ : ℝ),
        classMat m a b = diagPhaseMat χ * (List.ofFn fun j : Fin m => primFactor (φ j)).prod)
    (a b : Polynomial ℂ) (h : IsClassL (L+1) a b)
    (hta : a.coeff (L+1) = 0) (htb : b.coeff (L+1) = 0) :
    ∃ (φ : Fin (L+1) → ℝ) (χ : ℝ),
      classMat (L+1) a b
        = diagPhaseMat χ * (List.ofFn fun j : Fin (L+1) => primFactor (φ j)).prod := by
  rcases Nat.eq_zero_or_pos L with hL0 | hLpos
  · subst hL0; exfalso
    have ha0 : a.coeff 0 = 0 := by
      have := coeff_of_palin h.palinA (le_refl 1); rw [Nat.sub_self] at this; rw [this]; exact hta
    have hb0 : b.coeff 0 = 0 := by
      have := coeff_of_anti h.antiB (le_refl 1); rw [Nat.sub_self] at this; rw [this, htb]; ring
    have haz : a = 0 := by
      ext n; rcases n with _ | _ | n
      · exact ha0
      · exact hta
      · exact coeff_eq_zero_of_natDegree_lt (by have := h.degA; omega)
    have hbz : b = 0 := by
      ext n; rcases n with _ | _ | n
      · exact hb0
      · exact htb
      · exact coeff_eq_zero_of_natDegree_lt (by have := h.degB; omega)
    have hu := h.unitarity
    rw [haz, hbz] at hu; simp at hu
    exact Polynomial.X_ne_zero hu.symm
  · obtain ⟨M, rfl⟩ : ∃ M, L = M+1 := ⟨L-1, by omega⟩
    have hclass1 : IsClassL M a.divX b.divX := by
      have := degenerate_class (by omega : 1 ≤ M+1) h hta htb; simpa using this
    have hrecon : classMat (M+2) a b = (Polynomial.X : Polynomial ℂ) • classMat M a.divX b.divX := by
      have := degenerate_recon (by omega : 1 ≤ M+1) h hta htb; simpa using this
    obtain ⟨φ', χ, hdecomp⟩ := IHs M (by omega) a.divX b.divX hclass1
    refine ⟨Fin.snoc (Fin.snoc φ' (0:ℝ)) Real.pi, χ, ?_⟩
    rw [hrecon, hdecomp, smul_X_eq_mul_primFactor_pair _ 0,
        List.ofFn_succ_last, List.prod_append, List.prod_singleton,
        List.ofFn_succ_last, List.prod_append, List.prod_singleton]
    have e1 : (Fin.snoc (Fin.snoc φ' (0:ℝ)) Real.pi : Fin (M+2) → ℝ) (Fin.last (M+1)) = Real.pi := by
      rw [Fin.snoc_last]
    have e2 : ∀ i : Fin (M+1), (Fin.snoc (Fin.snoc φ' (0:ℝ)) Real.pi : Fin (M+2) → ℝ) i.castSucc
        = (Fin.snoc φ' (0:ℝ) : Fin (M+1) → ℝ) i := by intro i; rw [Fin.snoc_castSucc]
    simp only [e1, e2]
    have e3 : (Fin.snoc φ' (0:ℝ) : Fin (M+1) → ℝ) (Fin.last M) = 0 := by rw [Fin.snoc_last]
    have e4 : ∀ i : Fin M, (Fin.snoc φ' (0:ℝ) : Fin (M+1) → ℝ) i.castSucc = φ' i := by
      intro i; rw [Fin.snoc_castSucc]
    simp only [e3, e4]
    rw [show (0:ℝ) + Real.pi = Real.pi by ring, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc]

/-- **The Haah product decomposition (converse QSP existence step).** Every member of the
SU(2) Laurent class `IsClassL L` factors as a constant diagonal phase times a product of `L`
primitive equatorial factors. φ-ordering: the product is `List.ofFn (fun j : Fin L => …)`,
with the **last** factor `primFactor (φ (Fin.last))` peeled first in the induction. -/
theorem exists_primFactor_decomposition (L : ℕ) (a b : Polynomial ℂ)
    (h : IsClassL L a b) :
    ∃ (φ : Fin L → ℝ) (χ : ℝ),
      classMat L a b = diagPhaseMat χ * (List.ofFn fun j : Fin L => primFactor (φ j)).prod := by
  induction L using Nat.strong_induction_on generalizing a b with
  | _ L IH =>
    match L, a, b, h, IH with
    | 0, a, b, h, _ => exact decomp_base a b h
    | (M+1), a, b, h, IH =>
      by_cases hnd : a.coeff (M+1) = 0 ∧ b.coeff (M+1) = 0
      · exact decomp_degen M (fun m hm => IH m (by omega)) a b h hnd.1 hnd.2
      · exact decomp_nondegen M (IH M (by omega)) a b h hnd

end

end QAOA.IsingChain.Achievability
