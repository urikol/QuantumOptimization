import QuantumOptimization.QAOA.IsingChain.JordanWigner.PseudospinDynamics.PseudospinAlgebra
import QuantumOptimization.QAOA.IsingChain.JordanWigner.PseudospinDynamics.Rodrigues

/-!
# Pseudospin Dynamics — exp→SO(3) homomorphism, QAOA layers as rotations

(arXiv:1911.12259v2 SM l.859–909.) The dynamical core:
the `Matrix.exp` even/odd collapse to the Euler closed form, the abstract→concrete
exp→SO(3) homomorphism `exp_conj_dotTau`, and the per-layer QAOA cost/mixer
conjugations realised as Rodrigues rotations of the pseudospin (`costLayer_conj`,
`mixerLayer_conj`, `layerBlock_conj`).

The driving algebraic input is the cubic `A³ = A` (`A = û·τ⃗_k`, unit axis) and the
projector-swallowing facts from `PseudospinAlgebra`; the one analysis step is the
`expSeries` even→cos / odd→sin split (mirrors `Quaternion.exp_of_re_eq_zero`).

Mathlib's `Matrix` carries no canonical norm, so the ℓ∞-operator norm/ring/algebra
instances are pinned as LOCAL instances here (purely a synthesis aid for `Matrix.exp`;
its value is norm-independent), and the `Matrix.exp` instantiations raise heartbeats
because synthesising those instances on `NQubitOp (2P+2)` is costly for the symbolic
dimension.

## FROZEN conventions (mirror the numerically-validated F7 sign convention; do NOT reverse)
- Heisenberg conjugation, POSITIVE exponent on the LEFT; cost `R_{b̂_k}(+4γ)`, mixer
  `R_ẑ(+4β)`. Abstract: `e^{−iθ(n̂·τ⃗)}(m̂·τ⃗)e^{+iθ(n̂·τ⃗)} = (R_{n̂}(2θ) m̂)·τ⃗`.

## Main statements
- `exp_smul_mul_of_pow_mul_collapse`, `mul_exp_smul_of_pow_mul_collapse`: abstract Euler
  closed forms.
- `exp_dotTau_mul_Spair`, `Spair_mul_exp_dotTau`: concrete Euler closed forms.
- `exp_conj_dotTau` (L4): the exp→SO(3) homomorphism on the active block.
- `HredZMode_eq_dotTau`, `HredXMode_eq_dotTau`, `costLayer_conj`, `mixerLayer_conj`,
  `layerBlock_conj` (D2): the per-layer QAOA conjugations as Rodrigues rotations.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

section TauTable

variable (P : ℕ) (n : Fin P)

private abbrev kn := waveVectorABC P n

-- ============================================================================
-- B3-L4 (exp→SO(3) homomorphism): the projector-swallowing operator facts and
-- the cubic `A³ = A`, then the `Matrix.exp` even/odd collapse on active kets.
-- ============================================================================

/-- `S_k · τ^x_k = τ^x_k`. -/
theorem Spair_mul_tauX : Spair P n * tauX P (kn P n) = tauX P (kn P n) := by
  rw [tauX_eq_kernel, Spair]; exact PauliKernel.Spair_mul_tX (carPair P n)

/-- `S_k · τ^y_k = τ^y_k`. -/
theorem Spair_mul_tauY : Spair P n * tauY P (kn P n) = tauY P (kn P n) := by
  rw [tauY_eq_kernel, Spair, mul_smul_comm, PauliKernel.Spair_mul_tY (carPair P n)]

/-- `S_k · τ^z_k = τ^z_k`. -/
theorem Spair_mul_tauZ : Spair P n * tauZ P (kn P n) = tauZ P (kn P n) := by
  rw [tauZ_eq_kernel, Spair]; exact PauliKernel.Spair_mul_tZ (carPair P n)

/-- `S_k · (û·τ⃗_k) = (û·τ⃗_k)`: the projector swallows the dotted pseudospin. -/
theorem Spair_mul_dotTau (u : Fin 3 → ℝ) :
    Spair P n * dotTau P (kn P n) u = dotTau P (kn P n) u := by
  unfold dotTau
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [mul_smul_comm]
  congr 1
  fin_cases a
  · exact Spair_mul_tauX P n
  · exact Spair_mul_tauY P n
  · exact Spair_mul_tauZ P n

/-- `τ^x_k · S_k = τ^x_k` (right swallow). -/
theorem tauX_mul_Spair : tauX P (kn P n) * Spair P n = tauX P (kn P n) := by
  rw [tauX_eq_kernel, Spair]; exact PauliKernel.tX_mul_Spair (carPair P n)

/-- `τ^y_k · S_k = τ^y_k` (right swallow). -/
theorem tauY_mul_Spair : tauY P (kn P n) * Spair P n = tauY P (kn P n) := by
  rw [tauY_eq_kernel, Spair, smul_mul_assoc, PauliKernel.tY_mul_Spair (carPair P n)]

/-- `τ^z_k · S_k = τ^z_k` (right swallow). -/
theorem tauZ_mul_Spair : tauZ P (kn P n) * Spair P n = tauZ P (kn P n) := by
  rw [tauZ_eq_kernel, Spair]; exact PauliKernel.tZ_mul_Spair (carPair P n)

/-- `(û·τ⃗_k) · S_k = (û·τ⃗_k)` for ANY `û` (right swallow; no unit hypothesis). -/
theorem dotTau_mul_Spair_any (u : Fin 3 → ℝ) :
    dotTau P (kn P n) u * Spair P n = dotTau P (kn P n) u := by
  unfold dotTau
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [smul_mul_assoc]
  congr 1
  fin_cases a
  · exact tauX_mul_Spair P n
  · exact tauY_mul_Spair P n
  · exact tauZ_mul_Spair P n

/-- `A² = S_k` for a unit axis (`A = û·τ⃗_k`, `û⬝ᵥû = 1`): the involution-up-to-
projector that drives the even/odd `Matrix.exp` collapse. -/
theorem dotTau_sq (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    dotTau P (kn P n) u * dotTau P (kn P n) u = Spair P n := by
  rw [pauli_dot_mul_dot, cross_self, hu]
  simp [dotTau]

/-- The cubic relation `A³ = A` (`A = û·τ⃗_k`, unit `û`): `A³ = A²·A = S·A = A`,
using `A² = S` and `S·A = A`. Equivalent to `A` having minimal polynomial dividing
`x³ − x` (eigenvalues `0, ±1`). -/
theorem dotTau_cube (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    dotTau P (kn P n) u * dotTau P (kn P n) u * dotTau P (kn P n) u
      = dotTau P (kn P n) u := by
  rw [dotTau_sq P n u hu, Spair_mul_dotTau]

/-- `A · S = A` (right projector swallow), from `A³ = A`. -/
theorem dotTau_mul_Spair (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    dotTau P (kn P n) u * Spair P n = dotTau P (kn P n) u := by
  rw [← dotTau_sq P n u hu, ← mul_assoc, dotTau_sq P n u hu, Spair_mul_dotTau]

/-- `S² = S` (`S` is idempotent), from `S = A²`, `A·S = A`. -/
theorem Spair_mul_Spair (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    Spair P n * Spair P n = Spair P n := by
  nth_rewrite 1 [← dotTau_sq P n u hu]
  rw [mul_assoc, dotTau_mul_Spair P n u hu, dotTau_sq P n u hu]

/-- `A² · S = S`. -/
theorem dotTau_sq_mul_Spair (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    (dotTau P (kn P n) u * dotTau P (kn P n) u) * Spair P n = Spair P n := by
  rw [dotTau_sq P n u hu, Spair_mul_Spair P n u hu]

/-- Powers of `A` times `S`: `A^(2m)·S = S` and `A^(2m+1)·S = A` for unit `û`.
Proven via the two-step recurrence `A^(k+2)·S = A^k·S` (`A²·S = S`). -/
theorem dotTau_pow_mul_Spair (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    ∀ m : ℕ,
      (dotTau P (kn P n) u ^ (2 * m)) * Spair P n = Spair P n
      ∧ (dotTau P (kn P n) u ^ (2 * m + 1)) * Spair P n = dotTau P (kn P n) u := by
  intro m
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_zero, pow_zero, one_mul]
      · rw [Nat.mul_zero, Nat.zero_add, pow_one, dotTau_mul_Spair P n u hu]
  | succ p ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hsq : dotTau P (kn P n) u ^ 2 * Spair P n = Spair P n := by
        rw [pow_two, dotTau_sq_mul_Spair P n u hu]
      have hrec : ∀ k : ℕ,
          (dotTau P (kn P n) u ^ (k + 2)) * Spair P n
            = (dotTau P (kn P n) u ^ k) * Spair P n := by
        intro k
        rw [pow_add, mul_assoc, hsq]
      refine ⟨?_, ?_⟩
      · rw [show 2 * (p + 1) = 2 * p + 2 by ring, hrec, ih1]
      · rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 2 by ring, hrec, ih2]

/-- Powers of `A` left-multiplied by `S`: `S·A^(2m) = S` and `S·A^(2m+1) = A`
(the right-conjugation companion of `dotTau_pow_mul_Spair`). -/
theorem Spair_mul_dotTau_pow (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) :
    ∀ m : ℕ,
      Spair P n * (dotTau P (kn P n) u ^ (2 * m)) = Spair P n
      ∧ Spair P n * (dotTau P (kn P n) u ^ (2 * m + 1)) = dotTau P (kn P n) u := by
  intro m
  induction m with
  | zero =>
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_zero, pow_zero, mul_one]
      · rw [Nat.mul_zero, Nat.zero_add, pow_one, Spair_mul_dotTau]
  | succ p ih =>
      obtain ⟨ih1, ih2⟩ := ih
      have hsq : Spair P n * dotTau P (kn P n) u ^ 2 = Spair P n := by
        rw [pow_two, ← mul_assoc, ← dotTau_sq P n u hu, dotTau_sq P n u hu,
          Spair_mul_dotTau, dotTau_sq P n u hu]
      have hrec : ∀ k : ℕ,
          Spair P n * (dotTau P (kn P n) u ^ (k + 2))
            = Spair P n * (dotTau P (kn P n) u ^ k) := by
        intro k
        rw [show k + 2 = 2 + k by ring, pow_add, ← mul_assoc, hsq]
      refine ⟨?_, ?_⟩
      · rw [show 2 * (p + 1) = 2 * p + 2 by ring, hrec, ih1]
      · rw [show 2 * (p + 1) + 1 = (2 * p + 1) + 2 by ring, hrec, ih2]

-- ---------------------------------------------------------------------------
-- The `Matrix.exp` even/odd collapse (the one analysis step). With `z = −iθ`,
-- the even `expSeries` terms (times `S`) sum to `cos θ • S`, the odd ones to
-- `−i sin θ • A`. Mirrors `Quaternion.exp_of_re_eq_zero` (even→cos, odd→sin).
--
-- `Matrix` has several sensible norms (Frobenius, ℓ∞-op, …), none canonical, so
-- the generic `NormedSpace.expSeries_hasSum_exp` cannot synthesise a `NormedRing`
-- on `NQubitOp` by default. We pin the ℓ∞-operator norm as a LOCAL instance for
-- the `Matrix.exp` arguments below (the value of `Matrix.exp` is norm-independent,
-- so this is purely a synthesis aid). Mirrors Mathlib's own `MatrixExponential`
-- convention (module docstring: "choose a norm via `attribute [local instance]`").
-- ---------------------------------------------------------------------------

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- ABSTRACT Euler closed form (right-multiplied by a swallowing element `S`). For
any complex Banach algebra `𝔸` and `A S : 𝔸` such that the powers of `A` collapse
onto `S`/`A` after right-multiplication by `S`
(`A^(2m)·S = S`, `A^(2m+1)·S = A`), the exponential satisfies
`e^{−iθ A}·S = cos θ • S − i sin θ • A`.

Generic over `𝔸` so the proof never unfolds the `NQubitOp` dimension `2^(2P+2)`
(which makes the `Matrix.exp` `whnf` blow up); the instantiation
`exp_dotTau_mul_Spair` plugs in `A = û·τ⃗_k`, `S = S_k`. The even `expSeries` terms
sum to `cos θ`, the odd to `−i sin θ` (mirrors `Quaternion.exp_of_re_eq_zero`). -/
theorem exp_smul_mul_of_pow_mul_collapse
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (A S : 𝔸) (θ : ℝ)
    (hpow : ∀ m : ℕ, A ^ (2 * m) * S = S ∧ A ^ (2 * m + 1) * S = A) :
    NormedSpace.exp ((-Complex.I * (θ : ℂ)) • A) * S
      = (Real.cos θ : ℂ) • S + (-Complex.I * (Real.sin θ : ℂ)) • A := by
  -- even terms → cos θ • S
  have heven : HasSum (fun k => (NormedSpace.expSeries ℂ 𝔸 (2 * k)
      (fun _ => (-Complex.I * (θ : ℂ)) • A)) * S) ((Real.cos θ : ℂ) • S) := by
    have hscalar : HasSum
        (fun k => ((((2 * k).factorial : ℂ))⁻¹ * (-Complex.I * (θ : ℂ)) ^ (2 * k)))
        (Real.cos θ : ℂ) := by
      have hr : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * θ ^ (2 * k) / (2 * k).factorial)
          (Real.cos θ) := Real.hasSum_cos θ
      refine (Complex.hasSum_ofReal.mpr hr).congr_fun ?_
      intro k
      push_cast
      rw [mul_pow, show (-Complex.I) ^ (2 * k) = (-1 : ℂ) ^ k by
        rw [pow_mul]; norm_num [Complex.I_sq]]
      ring
    refine (hscalar.smul_const S).congr_fun ?_
    intro k
    rw [NormedSpace.expSeries_apply_eq, smul_pow, smul_mul_assoc, smul_mul_assoc,
      (hpow k).1, smul_smul]
  -- odd terms → −i sin θ • A
  have hodd : HasSum (fun k => (NormedSpace.expSeries ℂ 𝔸 (2 * k + 1)
      (fun _ => (-Complex.I * (θ : ℂ)) • A)) * S)
      ((-Complex.I * (Real.sin θ : ℂ)) • A) := by
    have hscalar : HasSum
        (fun k => ((((2 * k + 1).factorial : ℂ))⁻¹ * (-Complex.I * (θ : ℂ)) ^ (2 * k + 1)))
        (-Complex.I * (Real.sin θ : ℂ)) := by
      have hr : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * θ ^ (2 * k + 1) / (2 * k + 1).factorial)
          (Real.sin θ) := Real.hasSum_sin θ
      refine ((Complex.hasSum_ofReal.mpr hr).mul_left (-Complex.I)).congr_fun ?_
      intro k
      push_cast
      rw [pow_succ, mul_pow, show (-Complex.I) ^ (2 * k) = (-1 : ℂ) ^ k by
        rw [pow_mul]; norm_num [Complex.I_sq]]
      ring
    refine (hscalar.smul_const A).congr_fun ?_
    intro k
    rw [NormedSpace.expSeries_apply_eq, smul_pow, smul_mul_assoc, smul_mul_assoc,
      (hpow k).2, smul_smul]
  have hexp := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ)
      ((-Complex.I * (θ : ℂ)) • A)).mul_right S
  exact hexp.unique (HasSum.even_add_odd heven hodd)

/-- ABSTRACT Euler closed form (left-multiplied by `S`): the right-conjugation
companion of `exp_smul_mul_of_pow_mul_collapse`. With `S·A^(2m) = S`,
`S·A^(2m+1) = A`, `S·e^{−iθ A} = cos θ • S − i sin θ • A`. -/
theorem mul_exp_smul_of_pow_mul_collapse
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]
    (A S : 𝔸) (θ : ℝ)
    (hpow : ∀ m : ℕ, S * A ^ (2 * m) = S ∧ S * A ^ (2 * m + 1) = A) :
    S * NormedSpace.exp ((-Complex.I * (θ : ℂ)) • A)
      = (Real.cos θ : ℂ) • S + (-Complex.I * (Real.sin θ : ℂ)) • A := by
  have heven : HasSum (fun k => S * (NormedSpace.expSeries ℂ 𝔸 (2 * k)
      (fun _ => (-Complex.I * (θ : ℂ)) • A))) ((Real.cos θ : ℂ) • S) := by
    have hscalar : HasSum
        (fun k => ((((2 * k).factorial : ℂ))⁻¹ * (-Complex.I * (θ : ℂ)) ^ (2 * k)))
        (Real.cos θ : ℂ) := by
      have hr : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * θ ^ (2 * k) / (2 * k).factorial)
          (Real.cos θ) := Real.hasSum_cos θ
      refine (Complex.hasSum_ofReal.mpr hr).congr_fun ?_
      intro k
      push_cast
      rw [mul_pow, show (-Complex.I) ^ (2 * k) = (-1 : ℂ) ^ k by
        rw [pow_mul]; norm_num [Complex.I_sq]]
      ring
    refine ((hscalar.smul_const S).congr_fun ?_)
    intro k
    rw [NormedSpace.expSeries_apply_eq, smul_pow, mul_smul_comm, mul_smul_comm,
      (hpow k).1, smul_smul, mul_comm]
  have hodd : HasSum (fun k => S * (NormedSpace.expSeries ℂ 𝔸 (2 * k + 1)
      (fun _ => (-Complex.I * (θ : ℂ)) • A)))
      ((-Complex.I * (Real.sin θ : ℂ)) • A) := by
    have hscalar : HasSum
        (fun k => ((((2 * k + 1).factorial : ℂ))⁻¹ * (-Complex.I * (θ : ℂ)) ^ (2 * k + 1)))
        (-Complex.I * (Real.sin θ : ℂ)) := by
      have hr : HasSum (fun k : ℕ => (-1 : ℝ) ^ k * θ ^ (2 * k + 1) / (2 * k + 1).factorial)
          (Real.sin θ) := Real.hasSum_sin θ
      refine ((Complex.hasSum_ofReal.mpr hr).mul_left (-Complex.I)).congr_fun ?_
      intro k
      push_cast
      rw [pow_succ, mul_pow, show (-Complex.I) ^ (2 * k) = (-1 : ℂ) ^ k by
        rw [pow_mul]; norm_num [Complex.I_sq]]
      ring
    refine ((hscalar.smul_const A).congr_fun ?_)
    intro k
    rw [NormedSpace.expSeries_apply_eq, smul_pow, mul_smul_comm, mul_smul_comm,
      (hpow k).2, smul_smul, mul_comm]
  have hexp := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ)
      ((-Complex.I * (θ : ℂ)) • A)).mul_left S
  exact hexp.unique (HasSum.even_add_odd heven hodd)

set_option maxHeartbeats 1000000 in
-- Raised heartbeats: synthesising `NormedRing`/`NormedAlgebra ℂ`/`CompleteSpace` on
-- `NQubitOp (2P+2)` via the local ℓ∞ instances is costly for the symbolic dimension.
/-- L4 core (Euler closed form, right-multiplied by `S`):
`e^{−iθ A} · S = cos θ • S − i sin θ • A` for a unit axis `û` (`A = û·τ⃗_k`).
The off-block correction `(1−S)` drops because we land on `S`. Instantiation of
`exp_smul_mul_of_pow_mul_collapse` with the ℓ∞-operator norm pinned locally. -/
theorem exp_dotTau_mul_Spair (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) (θ : ℝ) :
    NormedSpace.exp ((-Complex.I * (θ : ℂ)) • dotTau P (kn P n) u) * Spair P n
      = (Real.cos θ : ℂ) • Spair P n + (-Complex.I * (Real.sin θ : ℂ)) • dotTau P (kn P n) u :=
  exp_smul_mul_of_pow_mul_collapse (dotTau P (kn P n) u) (Spair P n) θ
    (dotTau_pow_mul_Spair P n u hu)

set_option maxHeartbeats 1000000 in
-- Raised heartbeats: same `NQubitOp` instance-synthesis cost as `exp_dotTau_mul_Spair`.
/-- L4 core (left-multiplied by `S`): `S · e^{+iθ A} = cos θ • S + i sin θ • A`.
(Right-conjugation companion; note the `+iθ` exponent flips the sign of the `A`
term.) -/
theorem Spair_mul_exp_dotTau (u : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) (θ : ℝ) :
    Spair P n * NormedSpace.exp ((Complex.I * (θ : ℂ)) • dotTau P (kn P n) u)
      = (Real.cos θ : ℂ) • Spair P n + (Complex.I * (Real.sin θ : ℂ)) • dotTau P (kn P n) u := by
  have h := mul_exp_smul_of_pow_mul_collapse (dotTau P (kn P n) u) (Spair P n) (-θ)
    (fun m => ⟨(Spair_mul_dotTau_pow P n u hu m).1, (Spair_mul_dotTau_pow P n u hu m).2⟩)
  rw [Real.cos_neg, Real.sin_neg] at h
  rw [show (-Complex.I * ((-θ : ℝ) : ℂ)) = Complex.I * (θ : ℂ) by push_cast; ring] at h
  rw [h]
  push_cast
  module

-- ---------------------------------------------------------------------------
-- L4: the exp→SO(3) homomorphism (Heisenberg conjugation). Linearity of `dotTau`
-- + the two Euler closed forms + L3 assemble the Rodrigues image.
-- ---------------------------------------------------------------------------

/-- `dotTau` is additive in the vector argument. -/
theorem dotTau_add (u w : Fin 3 → ℝ) :
    dotTau P (kn P n) (u + w) = dotTau P (kn P n) u + dotTau P (kn P n) w := by
  unfold dotTau
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.add_apply, Complex.ofReal_add, add_smul]

/-- `dotTau` is ℝ-homogeneous in the vector argument. -/
theorem dotTau_smul (a : ℝ) (u : Fin 3 → ℝ) :
    dotTau P (kn P n) (a • u) = (a : ℂ) • dotTau P (kn P n) u := by
  unfold dotTau
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, smul_smul]

/-- `dotTau` is negation-compatible in the vector argument. -/
theorem dotTau_neg (u : Fin 3 → ℝ) :
    dotTau P (kn P n) (-u) = -dotTau P (kn P n) u := by
  rw [show (-u : Fin 3 → ℝ) = (-1 : ℝ) • u by module, dotTau_smul]
  push_cast; module

/-- `dotTau` is subtraction-compatible in the vector argument. -/
theorem dotTau_sub (u w : Fin 3 → ℝ) :
    dotTau P (kn P n) (u - w) = dotTau P (kn P n) u - dotTau P (kn P n) w := by
  rw [sub_eq_add_neg, dotTau_add, dotTau_neg, sub_eq_add_neg]

/-- `dotTau` of the Rodrigues image expands into the three-term combination. -/
theorem dotTau_R_mulVec (u m : Fin 3 → ℝ) (θ : ℝ) :
    dotTau P (kn P n) (R u θ *ᵥ m)
      = (Real.cos θ : ℂ) • dotTau P (kn P n) m
        + ((1 - Real.cos θ : ℝ) : ℂ) • (((u ⬝ᵥ m : ℝ) : ℂ) • dotTau P (kn P n) u)
        + (Real.sin θ : ℂ) • dotTau P (kn P n) (u ⨯₃ m) := by
  rw [R_mulVec, dotTau_add, dotTau_add, dotTau_smul, dotTau_smul, dotTau_smul,
    dotTau_smul]

/-- L4 (`exp_conj_dotTau`) — the exp→SO(3) homomorphism on the active block.
Heisenberg conjugation by `e^{−iθ A}` with the NEGATIVE exponent on the LEFT
(`A = n̂·τ⃗_k`, unit axis `n̂`):
`e^{−iθ(n̂·τ⃗_k)}(m̂·τ⃗_k)e^{+iθ(n̂·τ⃗_k)} = (R_{n̂}(2θ) m̂)·τ⃗_k`.
The generator angle `θ` becomes the rotation angle `2θ` (the factor-2 of the
adjoint/Rodrigues map). The conjugation is sandwiched between the two Euler closed
forms; the cross term collapses via L3 (`pauli_dot_mul_dot`) and the BAC−CAB
identity (`cross_cross`) to the Rodrigues combination at the double angle `2θ`. -/
theorem exp_conj_dotTau (u m : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) (θ : ℝ) :
    NormedSpace.exp ((-Complex.I * (θ : ℂ)) • dotTau P (kn P n) u)
        * dotTau P (kn P n) m
        * NormedSpace.exp ((Complex.I * (θ : ℂ)) • dotTau P (kn P n) u)
      = dotTau P (kn P n) (R u (2 * θ) *ᵥ m) := by
  -- Abbreviations.
  set A := dotTau P (kn P n) u with hA
  set B := dotTau P (kn P n) m with hB
  set eL := NormedSpace.exp ((-Complex.I * (θ : ℂ)) • A) with heL
  set eR := NormedSpace.exp ((Complex.I * (θ : ℂ)) • A) with heR
  have hSB : Spair P n * B = B := Spair_mul_dotTau P n m
  have hBS : B * Spair P n = B := dotTau_mul_Spair_any P n m
  have heLS : eL * Spair P n
      = (Real.cos θ : ℂ) • Spair P n + (-Complex.I * (Real.sin θ : ℂ)) • A :=
    exp_dotTau_mul_Spair P n u hu θ
  have hSeR : Spair P n * eR
      = (Real.cos θ : ℂ) • Spair P n + (Complex.I * (Real.sin θ : ℂ)) • A :=
    Spair_mul_exp_dotTau P n u hu θ
  -- Sandwich: insert `B = S·B·S`, group, and apply the two Euler closed forms.
  have hsandwich : eL * B * eR
      = ((Real.cos θ : ℂ) • Spair P n + (-Complex.I * (Real.sin θ : ℂ)) • A) * B
          * ((Real.cos θ : ℂ) • Spair P n + (Complex.I * (Real.sin θ : ℂ)) • A) := by
    rw [← heLS, ← hSeR]
    calc eL * B * eR
        = eL * (Spair P n * B) * eR := by rw [hSB]
      _ = eL * Spair P n * (B * Spair P n) * eR := by rw [hBS]; noncomm_ring
      _ = eL * Spair P n * B * (Spair P n * eR) := by noncomm_ring
  rw [hsandwich, dotTau_R_mulVec]
  -- Operator products reduced to the linear span of `S, A, B, dotTau(u×m)`.
  have hSA : Spair P n * A = A := Spair_mul_dotTau P n u
  have hSS : Spair P n * Spair P n = Spair P n := Spair_mul_Spair P n u hu
  have hXmS : dotTau P (kn P n) (u ⨯₃ m) * Spair P n = dotTau P (kn P n) (u ⨯₃ m) :=
    dotTau_mul_Spair_any P n (u ⨯₃ m)
  -- Cross-product / dot identities.
  have hmu : m ⬝ᵥ u = u ⬝ᵥ m := dotProduct_comm m u
  have hmxu : m ⨯₃ u = -(u ⨯₃ m) := by rw [cross_anticomm]
  have huxu : u ⬝ᵥ (u ⨯₃ m) = 0 := dot_self_cross u m
  have hbac : u ⨯₃ (u ⨯₃ m) = (u ⬝ᵥ m) • u - m := by rw [cross_cross, hu, one_smul]
  -- L3 products, each reduced to atoms.
  have hAB : A * B = ((u ⬝ᵥ m : ℝ) : ℂ) • Spair P n
      + Complex.I • dotTau P (kn P n) (u ⨯₃ m) := pauli_dot_mul_dot P n u m
  have hBA : B * A = ((u ⬝ᵥ m : ℝ) : ℂ) • Spair P n
      - Complex.I • dotTau P (kn P n) (u ⨯₃ m) := by
    rw [hB, hA, pauli_dot_mul_dot, hmu, hmxu, dotTau_neg]
    module
  -- `(dotTau(u×m))·A = i(B − (u·m)•A)`.
  have hXmu : (u ⨯₃ m) ⬝ᵥ u = 0 := by
    rw [dotProduct_comm]; exact dot_self_cross u m
  have hXmxu : (u ⨯₃ m) ⨯₃ u = m - (u ⬝ᵥ m) • u := by
    rw [show (u ⨯₃ m) ⨯₃ u = -(u ⨯₃ (u ⨯₃ m)) from (cross_anticomm u (u ⨯₃ m)).symm,
      cross_cross, hu, one_smul, neg_sub]
  have hXmA : dotTau P (kn P n) (u ⨯₃ m) * A
      = Complex.I • (B - ((u ⬝ᵥ m : ℝ) : ℂ) • A) := by
    rw [hA, pauli_dot_mul_dot, hXmu, hXmxu, dotTau_sub, dotTau_smul, ← hA, ← hB]
    push_cast; module
  have hSXm : Spair P n * dotTau P (kn P n) (u ⨯₃ m) = dotTau P (kn P n) (u ⨯₃ m) :=
    Spair_mul_dotTau P n (u ⨯₃ m)
  -- Trig double-angle identities.
  have hc2 : Real.cos (2 * θ) = Real.cos θ ^ 2 - Real.sin θ ^ 2 := by
    rw [Real.cos_two_mul']
  have hs2 : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := by
    rw [Real.sin_two_mul]
  -- Expand the full product `(cS − isA)·B·(cS + isA)` into the atom basis.
  -- Left product reduced to atoms: `(cS − isA)·B = c•B − is•(↑(u·m)•S + I•Xm)`.
  have hleft : ((Real.cos θ : ℂ) • Spair P n + (-Complex.I * (Real.sin θ : ℂ)) • A) * B
      = (Real.cos θ : ℂ) • B
        + (-Complex.I * (Real.sin θ : ℂ)) • (((u ⬝ᵥ m : ℝ) : ℂ) • Spair P n
            + Complex.I • dotTau P (kn P n) (u ⨯₃ m)) := by
    rw [add_mul, smul_mul_assoc, hSB, smul_mul_assoc, hAB]
  have key :
      ((Real.cos θ : ℂ) • Spair P n + (-Complex.I * (Real.sin θ : ℂ)) • A) * B
          * ((Real.cos θ : ℂ) • Spair P n + (Complex.I * (Real.sin θ : ℂ)) • A)
        = ((Real.cos θ ^ 2 - Real.sin θ ^ 2 : ℝ) : ℂ) • B
          + ((2 * Real.sin θ * Real.cos θ : ℝ) : ℂ) • dotTau P (kn P n) (u ⨯₃ m)
          + ((2 * Real.sin θ ^ 2 : ℝ) : ℂ) • (((u ⬝ᵥ m : ℝ) : ℂ) • A) := by
    rw [hleft]
    -- Distribute over the right factor; all products are now bare atom products.
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add]
    rw [hBS, hBA, hSS, hSA, hXmS, hXmA]
    -- Reconcile the four atom coefficients. Each scalar identity (in
    -- `cos, sin, I, (u·m)`) holds by `I² = −1`, `I⁴ = 1`; `linear_combination`'s
    -- residual (closed by `ring`, which treats `I` as a variable) discharges them.
    -- A single combination works because `I_sq`/`I_pow_four` supply the missing
    -- `I²+1 = 0`, `I⁴−1 = 0` relations for every monomial that occurs.
    match_scalars
    all_goals try linear_combination (-(Complex.sin (θ : ℂ) ^ 2)) * Complex.I_pow_four
    all_goals try
      linear_combination (-(Complex.cos (θ : ℂ) * Complex.sin (θ : ℂ) * 2)) * Complex.I_sq
    all_goals try
      linear_combination
        (-(Complex.sin (θ : ℂ) ^ 2 * ((u ⬝ᵥ m : ℝ) : ℂ))) * Complex.I_sq
          + (Complex.sin (θ : ℂ) ^ 2 * ((u ⬝ᵥ m : ℝ) : ℂ)) * Complex.I_pow_four
    all_goals ring
  rw [key, hc2, hs2, hB, hA]
  -- Reconcile the four atom coefficients; the `2 sin²` vs `1 − (cos² − sin²)`
  -- coefficient closes with the Pythagorean identity `sin² + cos² = 1`.
  have hpyth : Complex.sin (θ : ℂ) ^ 2 + Complex.cos (θ : ℂ) ^ 2 = 1 :=
    Complex.sin_sq_add_cos_sq (θ : ℂ)
  match_scalars
  all_goals try linear_combination (((u ⬝ᵥ m : ℝ) : ℂ)) * hpyth
  all_goals ring

-- ---------------------------------------------------------------------------
-- D2: per-layer cost/mixer rotations as the source Heisenberg conjugation.
-- Pure instantiation of L4 (`exp_conj_dotTau`) via the axis substitutions
-- `Hred_z^(k) = −2 b̂_k·τ⃗`, `Hred_x^(k) = −2 ẑ·τ⃗` and the FROZEN positive-left
-- direction (the conjugating LEFT factor is `e^{+iγ Hred}`, giving `+4γ`/`+4β`).
-- ---------------------------------------------------------------------------

/-- The per-mode cost Hamiltonian is `−2 (b̂_k·τ⃗_k)`. -/
theorem HredZMode_eq_dotTau : HredZMode P (kn P n) = (-2 : ℂ) • dotTau P (kn P n) (bHat (kn P n)) := by
  unfold HredZMode dotTau bHat tauVecOp
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  module

/-- The per-mode mixer Hamiltonian is `−2 (ẑ·τ⃗_k)`. -/
theorem HredXMode_eq_dotTau : HredXMode P (kn P n) = (-2 : ℂ) • dotTau P (kn P n) zHat := by
  unfold HredXMode dotTau zHat tauVecOp
  rw [Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

/-- D2 (cost layer): the source Heisenberg conjugation by the cost layer
`U_C = e^{−iγ Hred_z^(k)}` rotates `m̂·τ⃗_k` by `R_{b̂_k}(+4γ)`:
`e^{+iγ Hred_z^(k)} (m̂·τ⃗_k) e^{−iγ Hred_z^(k)} = (R_{b̂_k}(4γ) m̂)·τ⃗_k`.
The `−2` axis factor carries into `θ = +2γ`, so `R(2θ) = R(+4γ)` (F7 sign). -/
theorem costLayer_conj (m : Fin 3 → ℝ) (γ : ℝ) :
    NormedSpace.exp ((Complex.I * (γ : ℂ)) • HredZMode P (kn P n))
        * dotTau P (kn P n) m
        * NormedSpace.exp ((-Complex.I * (γ : ℂ)) • HredZMode P (kn P n))
      = dotTau P (kn P n) (R (bHat (kn P n)) (4 * γ) *ᵥ m) := by
  have hu : bHat (kn P n) ⬝ᵥ bHat (kn P n) = 1 := bHat_dotProduct (kn P n)
  have hL : (Complex.I * (γ : ℂ)) • HredZMode P (kn P n)
      = (-Complex.I * ((2 * γ : ℝ) : ℂ)) • dotTau P (kn P n) (bHat (kn P n)) := by
    rw [HredZMode_eq_dotTau, smul_smul]; push_cast; module
  have hR : (-Complex.I * (γ : ℂ)) • HredZMode P (kn P n)
      = (Complex.I * ((2 * γ : ℝ) : ℂ)) • dotTau P (kn P n) (bHat (kn P n)) := by
    rw [HredZMode_eq_dotTau, smul_smul]; push_cast; module
  rw [hL, hR, exp_conj_dotTau P n (bHat (kn P n)) m hu (2 * γ),
    show 2 * (2 * γ) = 4 * γ by ring]

/-- D2 (mixer layer): the source Heisenberg conjugation by the mixer layer
`U_B = e^{−iβ Hred_x^(k)}` rotates `m̂·τ⃗_k` by `R_ẑ(+4β)` (F7 sign s = +1):
`e^{+iβ Hred_x^(k)} (m̂·τ⃗_k) e^{−iβ Hred_x^(k)} = (R_ẑ(4β) m̂)·τ⃗_k`. -/
theorem mixerLayer_conj (m : Fin 3 → ℝ) (β : ℝ) :
    NormedSpace.exp ((Complex.I * (β : ℂ)) • HredXMode P (kn P n))
        * dotTau P (kn P n) m
        * NormedSpace.exp ((-Complex.I * (β : ℂ)) • HredXMode P (kn P n))
      = dotTau P (kn P n) (R zHat (4 * β) *ᵥ m) := by
  have hu : zHat ⬝ᵥ zHat = 1 := zHat_dotProduct
  have hL : (Complex.I * (β : ℂ)) • HredXMode P (kn P n)
      = (-Complex.I * ((2 * β : ℝ) : ℂ)) • dotTau P (kn P n) zHat := by
    rw [HredXMode_eq_dotTau, smul_smul]; push_cast; module
  have hR : (-Complex.I * (β : ℂ)) • HredXMode P (kn P n)
      = (Complex.I * ((2 * β : ℝ) : ℂ)) • dotTau P (kn P n) zHat := by
    rw [HredXMode_eq_dotTau, smul_smul]; push_cast; module
  rw [hL, hR, exp_conj_dotTau P n zHat m hu (2 * β),
    show 2 * (2 * β) = 4 * β by ring]

/-- D2 → D3 bridge: one QAOA layer (cost then mixer, Heisenberg) conjugates
`m̂·τ⃗_k` by the `layerBlock` rotation `R_ẑ(4β) R_{b̂_k}(4γ)` — exactly the per-layer
factor in `tauVec_eq`. So the magnetization `τ⃗_k(γ,β)` (`tauVec`, the time-ordered
product of these blocks applied to `ẑ`) is the QAOA-evolved per-mode pseudospin on
the active subspace, the form B4 consumes.

B4 HANDOFF NOTE (reviewer W1): the nesting here is the F7-consistent
MIXER-OUTERMOST form `R_ẑ(4β) R_{b̂_k}(4γ)` (the operator conjugation has the mixer
exp on the outside, cost exp on the inside). This is the nesting that reproduces
`residualEnergy` end-to-end and is F7-validated; it is NOT the verbatim cost-outermost
`U_B U_C` conjugation. When B4 connects `tauVec` to the QAOA expectation it must use
THIS nesting (the one matched by `tauVec_eq`/`layerBlock`), not the literal `U_B U_C`
operator order. -/
theorem layerBlock_conj (m : Fin 3 → ℝ) (γ β : ℝ) :
    NormedSpace.exp ((Complex.I * (β : ℂ)) • HredXMode P (kn P n))
        * (NormedSpace.exp ((Complex.I * (γ : ℂ)) • HredZMode P (kn P n))
            * dotTau P (kn P n) m
            * NormedSpace.exp ((-Complex.I * (γ : ℂ)) • HredZMode P (kn P n)))
        * NormedSpace.exp ((-Complex.I * (β : ℂ)) • HredXMode P (kn P n))
      = dotTau P (kn P n) ((R zHat (4 * β) * R (bHat (kn P n)) (4 * γ)) *ᵥ m) := by
  rw [costLayer_conj P n m γ, mixerLayer_conj P n _ β, ← Matrix.mulVec_mulVec]

end TauTable

end

end QAOA.IsingChain.JordanWigner
