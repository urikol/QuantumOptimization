import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Geometry

/-!
# Active-Subspace Commute Suite — `n`/`τ`/`HredMode` (cross- and same-pair) commutators

Infrastructure for the active-subspace preservation. Establishes the full
single-fermion Wick commute calculus needed to show that the reduced cost/mixer mode
operators preserve the active pair-occupation subspace:

* a generic single-fermion Wick bilinear commute (`number_commute_single`) and the
  self-conjugate (`0`, `π`) and cross-pair (`m ≠ n`) CAR vanishing facts;
* the resulting commutes `n_{0,π}`/`n_{±k_m}` ↔ `τ⃗_{k_n}`, packaged up to the
  cross-mode pseudospin commute `dotTau_commute_dotTau_cross`;
* the mode-operator cross commutes `HredZMode`/`HredXMode k_m` ↔ `dotTau`/`Hred*Mode k_n`,
  the seeds for the sum-exponential factorization in `ExpReduction`.

## Main statements
- `number_commute_single`: a number-like bilinear `d * c` commutes with `e` when `e`
  cross-anticommutes with both `c` and `d`
- `dotTau_commute_dotTau_cross`: cross-mode `û·τ⃗_{k_m}` commutes with `ŵ·τ⃗_{k_n}` (`m ≠ n`)
- `HredZMode_commute_HredZMode_cross` / `HredXMode_commute_HredXMode_cross`: cross-mode
  reduced-Hamiltonian commutes
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

-- ----------------------------------------------------------------------------
-- Infrastructure: cross-mode τ commutes via the generic Wick bilinear lemma
-- `number_commute_of_car` (Basic.lean). Each self-conjugate number op `n_{0,π}`
-- commutes with the pair pseudospin `τ^±_n`, `τ^z_n` of a DISTINCT active pair,
-- because all four cross CAR anticommutators between `{c_{0/π}, c_{0/π}†}` and
-- `{c_{±k_n}}` vanish (the self-conjugate modes `0, π` differ from every `±k_n`).
-- ----------------------------------------------------------------------------

/-- Generic single-fermion Wick commute: a number-like bilinear `d * c` commutes
with `e` whenever `e` cross-anticommutes with both factors `c` and `d`. Used to
show a self-conjugate number op `n_{0,π} = c†c` commutes with each individual
active-pair fermion `c_{±k_n}` / `c_{±k_n}†`. -/
theorem number_commute_single {R : Type*} [Ring R] {c d e : R}
    (hce : c * e + e * c = 0) (hde : d * e + e * d = 0) :
    Commute (d * c) e := by
  have hce' : c * e = -(e * c) := by rw [eq_neg_iff_add_eq_zero]; exact hce
  have hde' : d * e = -(e * d) := by rw [eq_neg_iff_add_eq_zero]; exact hde
  unfold Commute SemiconjBy
  calc d * c * e = d * (c * e) := by rw [mul_assoc]
    _ = d * (-(e * c)) := by rw [hce']
    _ = -(d * e * c) := by rw [mul_neg, ← mul_assoc]
    _ = -((-(e * d)) * c) := by rw [hde']
    _ = e * (d * c) := by rw [neg_mul, neg_neg, mul_assoc]

/-- `{c_0, c_{σ k_n}†} = 0` and `{c_{σ k_n}, c_0†} = 0`: the self-conjugate `k=0`
fermion cross-anticommutes with every active-pair fermion (oriented form used by
the Wick bilinear lemma). -/
theorem car_cAnnihK_zero_cCreateK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    cCreateK P 0 * cAnnihK P ((σ : ℝ) * waveVectorABC P n)
      + cAnnihK P ((σ : ℝ) * waveVectorABC P n) * cCreateK P 0 = 0 := by
  have h := car_annihK_createK_zero P ((σ : ℝ) * waveVectorABC P n) 0
    (by have := exp_signed_sub_zero_ne_one P n hσ
        rw [show (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - ((0 : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P n - (0 : ℝ) : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
    (by have := exp_signed_sub_zero_root P n σ
        rw [show (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - ((0 : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P n - (0 : ℝ) : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
  linear_combination (norm := abel) h

theorem car_cAnnihK_pi_cCreateK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    cCreateK P Real.pi * cAnnihK P ((σ : ℝ) * waveVectorABC P n)
      + cAnnihK P ((σ : ℝ) * waveVectorABC P n) * cCreateK P Real.pi = 0 := by
  have h := car_annihK_createK_zero P ((σ : ℝ) * waveVectorABC P n) Real.pi
    (by have := exp_signed_sub_pi_ne_one P n hσ
        rw [show (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P n - Real.pi : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
    (by have := exp_signed_sub_pi_root P n σ
        rw [show (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P n - Real.pi : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
  linear_combination (norm := abel) h

/-- `{c_0, c_{σ k_n}†} = 0` (the OTHER orientation: bare-`c_0` with create at `σk_n`). -/
theorem car_cAnnihK_zero_cCreateK_signed' (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    cAnnihK P 0 * cCreateK P ((σ : ℝ) * waveVectorABC P n)
      + cCreateK P ((σ : ℝ) * waveVectorABC P n) * cAnnihK P 0 = 0 := by
  have h := car_annihK_createK_zero P 0 ((σ : ℝ) * waveVectorABC P n)
    (by have := exp_zero_sub_signed_ne_one P n hσ
        rw [show ((0 : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = (((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
    (by have := exp_zero_sub_signed_root P n σ
        rw [show ((0 : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = (((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
  exact h

theorem car_cAnnihK_pi_cCreateK_signed' (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    cAnnihK P Real.pi * cCreateK P ((σ : ℝ) * waveVectorABC P n)
      + cCreateK P ((σ : ℝ) * waveVectorABC P n) * cAnnihK P Real.pi = 0 := by
  have h := car_annihK_createK_zero P Real.pi ((σ : ℝ) * waveVectorABC P n)
    (by have := exp_pi_sub_signed_ne_one P n hσ
        rw [show ((Real.pi : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
    (by have := exp_pi_sub_signed_root P n σ
        rw [show ((Real.pi : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        simpa using this)
  exact h

/-- `{c_0†, c_{σ k_n}†} = 0` (creates cross-anticommute, adjoint of `{c_0, c_{σk_n}}`). -/
theorem car_cCreateK_zero_cCreateK_signed (P : ℕ) (n : Fin P) (σ : ℤ) :
    cCreateK P 0 * cCreateK P ((σ : ℝ) * waveVectorABC P n)
      + cCreateK P ((σ : ℝ) * waveVectorABC P n) * cCreateK P 0 = 0 := by
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul,
      ← Matrix.conjTranspose_add,
      add_comm (cAnnihK P ((σ : ℝ) * waveVectorABC P n) * cAnnihK P 0),
      car_annihK_annihK, Matrix.conjTranspose_zero]

theorem car_cCreateK_pi_cCreateK_signed (P : ℕ) (n : Fin P) (σ : ℤ) :
    cCreateK P Real.pi * cCreateK P ((σ : ℝ) * waveVectorABC P n)
      + cCreateK P ((σ : ℝ) * waveVectorABC P n) * cCreateK P Real.pi = 0 := by
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul,
      ← Matrix.conjTranspose_add,
      add_comm (cAnnihK P ((σ : ℝ) * waveVectorABC P n) * cAnnihK P Real.pi),
      car_annihK_annihK, Matrix.conjTranspose_zero]

/-- `n_0` commutes with each individual active-pair fermion `c_{σk_n}`. -/
theorem numberOpK_zero_commute_cAnnihK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P 0) (cAnnihK P ((σ : ℝ) * waveVectorABC P n)) := by
  unfold numberOpK
  exact number_commute_single (car_annihK_annihK P 0 ((σ : ℝ) * waveVectorABC P n))
    (car_cAnnihK_zero_cCreateK_signed P n hσ)

theorem numberOpK_zero_commute_cCreateK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P 0) (cCreateK P ((σ : ℝ) * waveVectorABC P n)) := by
  unfold numberOpK
  exact number_commute_single (car_cAnnihK_zero_cCreateK_signed' P n hσ)
    (car_cCreateK_zero_cCreateK_signed P n σ)

theorem numberOpK_pi_commute_cAnnihK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P Real.pi) (cAnnihK P ((σ : ℝ) * waveVectorABC P n)) := by
  unfold numberOpK
  exact number_commute_single (car_annihK_annihK P Real.pi ((σ : ℝ) * waveVectorABC P n))
    (car_cAnnihK_pi_cCreateK_signed P n hσ)

theorem numberOpK_pi_commute_cCreateK_signed (P : ℕ) (n : Fin P) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P Real.pi) (cCreateK P ((σ : ℝ) * waveVectorABC P n)) := by
  unfold numberOpK
  exact number_commute_single (car_cAnnihK_pi_cCreateK_signed' P n hσ)
    (car_cCreateK_pi_cCreateK_signed P n σ)

/-- `cAnnihK` at the unsigned active mode `k_n` is `cAnnihK ((1:ℝ)*k_n)`. -/
theorem cAnnihK_one_coe (P : ℕ) (n : Fin P) :
    cAnnihK P (((1 : ℤ) : ℝ) * waveVectorABC P n) = cAnnihK P (waveVectorABC P n) := by
  norm_num

theorem cAnnihK_negone_coe (P : ℕ) (n : Fin P) :
    cAnnihK P (((-1 : ℤ) : ℝ) * waveVectorABC P n) = cAnnihK P (-(waveVectorABC P n)) := by
  congr 1; push_cast; ring

theorem cCreateK_one_coe (P : ℕ) (n : Fin P) :
    cCreateK P (((1 : ℤ) : ℝ) * waveVectorABC P n) = cCreateK P (waveVectorABC P n) := by
  norm_num

theorem cCreateK_negone_coe (P : ℕ) (n : Fin P) :
    cCreateK P (((-1 : ℤ) : ℝ) * waveVectorABC P n) = cCreateK P (-(waveVectorABC P n)) := by
  congr 1; push_cast; ring

/-- `n_0` commutes with `c_{k_n}` and `c_{-k_n}` (unsigned/negated active modes). -/
theorem numberOpK_zero_commute_cAnnihK (P : ℕ) (n : Fin P) :
    Commute (numberOpK P 0) (cAnnihK P (waveVectorABC P n))
      ∧ Commute (numberOpK P 0) (cAnnihK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_⟩
  · have := numberOpK_zero_commute_cAnnihK_signed P n (Or.inl rfl); rwa [cAnnihK_one_coe] at this
  · have := numberOpK_zero_commute_cAnnihK_signed P n (Or.inr rfl); rwa [cAnnihK_negone_coe] at this

theorem numberOpK_zero_commute_cCreateK (P : ℕ) (n : Fin P) :
    Commute (numberOpK P 0) (cCreateK P (waveVectorABC P n))
      ∧ Commute (numberOpK P 0) (cCreateK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_⟩
  · have := numberOpK_zero_commute_cCreateK_signed P n (Or.inl rfl); rwa [cCreateK_one_coe] at this
  · have := numberOpK_zero_commute_cCreateK_signed P n (Or.inr rfl); rwa [cCreateK_negone_coe] at this

theorem numberOpK_pi_commute_cAnnihK (P : ℕ) (n : Fin P) :
    Commute (numberOpK P Real.pi) (cAnnihK P (waveVectorABC P n))
      ∧ Commute (numberOpK P Real.pi) (cAnnihK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_⟩
  · have := numberOpK_pi_commute_cAnnihK_signed P n (Or.inl rfl); rwa [cAnnihK_one_coe] at this
  · have := numberOpK_pi_commute_cAnnihK_signed P n (Or.inr rfl); rwa [cAnnihK_negone_coe] at this

theorem numberOpK_pi_commute_cCreateK (P : ℕ) (n : Fin P) :
    Commute (numberOpK P Real.pi) (cCreateK P (waveVectorABC P n))
      ∧ Commute (numberOpK P Real.pi) (cCreateK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_⟩
  · have := numberOpK_pi_commute_cCreateK_signed P n (Or.inl rfl); rwa [cCreateK_one_coe] at this
  · have := numberOpK_pi_commute_cCreateK_signed P n (Or.inr rfl); rwa [cCreateK_negone_coe] at this

/-- `n_0` commutes with `τ^x_{k_n}, τ^y_{k_n}, τ^z_{k_n}` (self-conjugate ↔ active-pair
pseudospin commute: each is a bilinear in `c_{±k_n}` / `c_{±k_n}†`, with which `n_0`
commutes individually). -/
theorem numberOpK_zero_commute_tauVecOp (P : ℕ) (n : Fin P) (a : Fin 3) :
    Commute (numberOpK P 0) (tauVecOp P (waveVectorABC P n) a) := by
  obtain ⟨ca1, ca2⟩ := numberOpK_zero_commute_cAnnihK P n
  obtain ⟨cc1, cc2⟩ := numberOpK_zero_commute_cCreateK P n
  have hP : Commute (numberOpK P 0) (tauPlus P (waveVectorABC P n)) := by
    unfold tauPlus; exact Commute.mul_right ca2 ca1
  have hM : Commute (numberOpK P 0) (tauMinus P (waveVectorABC P n)) := by
    unfold tauMinus; exact Commute.mul_right cc1 cc2
  fin_cases a
  · change Commute (numberOpK P 0) (tauX P (waveVectorABC P n))
    unfold tauX; exact Commute.add_right hP hM
  · change Commute (numberOpK P 0) (tauY P (waveVectorABC P n))
    unfold tauY; exact (Commute.sub_right hP hM).smul_right _
  · change Commute (numberOpK P 0) (tauZ P (waveVectorABC P n))
    unfold tauZ
    have c1 : Commute (numberOpK P 0) (numberOpK P (waveVectorABC P n)) := by
      have := numberOpK_zero_commute_signed P n (Or.inl rfl); rwa [numberOpK_one_coe] at this
    have c2 : Commute (numberOpK P 0) (numberOpK P (-(waveVectorABC P n))) := by
      have := numberOpK_zero_commute_signed P n (Or.inr rfl); rwa [numberOpK_negone_coe] at this
    exact Commute.sub_right (Commute.sub_right (Commute.one_right _) c1) c2

theorem numberOpK_pi_commute_tauVecOp (P : ℕ) (n : Fin P) (a : Fin 3) :
    Commute (numberOpK P Real.pi) (tauVecOp P (waveVectorABC P n) a) := by
  obtain ⟨ca1, ca2⟩ := numberOpK_pi_commute_cAnnihK P n
  obtain ⟨cc1, cc2⟩ := numberOpK_pi_commute_cCreateK P n
  have hP : Commute (numberOpK P Real.pi) (tauPlus P (waveVectorABC P n)) := by
    unfold tauPlus; exact Commute.mul_right ca2 ca1
  have hM : Commute (numberOpK P Real.pi) (tauMinus P (waveVectorABC P n)) := by
    unfold tauMinus; exact Commute.mul_right cc1 cc2
  fin_cases a
  · change Commute (numberOpK P Real.pi) (tauX P (waveVectorABC P n))
    unfold tauX; exact Commute.add_right hP hM
  · change Commute (numberOpK P Real.pi) (tauY P (waveVectorABC P n))
    unfold tauY; exact (Commute.sub_right hP hM).smul_right _
  · change Commute (numberOpK P Real.pi) (tauZ P (waveVectorABC P n))
    unfold tauZ
    have c1 : Commute (numberOpK P Real.pi) (numberOpK P (waveVectorABC P n)) := by
      have := numberOpK_pi_commute_signed P n (Or.inl rfl); rwa [numberOpK_one_coe] at this
    have c2 : Commute (numberOpK P Real.pi) (numberOpK P (-(waveVectorABC P n))) := by
      have := numberOpK_pi_commute_signed P n (Or.inr rfl); rwa [numberOpK_negone_coe] at this
    exact Commute.sub_right (Commute.sub_right (Commute.one_right _) c1) c2

/-- `n_0` commutes with `û·τ⃗_{k_n}` for any axis `û`. -/
theorem numberOpK_zero_commute_dotTau (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ) :
    Commute (numberOpK P 0) (dotTau P (waveVectorABC P n) u) := by
  unfold dotTau
  exact Commute.sum_right _ _ _ (fun a _ => (numberOpK_zero_commute_tauVecOp P n a).smul_right _)

theorem numberOpK_pi_commute_dotTau (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ) :
    Commute (numberOpK P Real.pi) (dotTau P (waveVectorABC P n) u) := by
  unfold dotTau
  exact Commute.sum_right _ _ _ (fun a _ => (numberOpK_pi_commute_tauVecOp P n a).smul_right _)

-- ----------------------------------------------------------------------------
-- Infrastructure: CROSS-PAIR τ commutes (`n_{σk_m}` ↔ `τ_{k_n}`, m ≠ n).
-- ----------------------------------------------------------------------------

set_option maxHeartbeats 800000 in
-- Raised: matching `car_annihK_createK_zero`'s hypotheses against the big-operator
-- `cAnnihK`/`cCreateK` definitions triggers a costly `whnf` at the symbolic dimension.
/-- Cross-pair CAR `{c_{σ k_m}, c_{τ k_n}†} = 0` for DISTINCT active pairs `m ≠ n`
and signs `σ, τ ∈ {±1}` (the wave-vector difference `σ k_m − τ k_n` is a non-trivial
root of unity, `N_R ∤ σ(m+1) − τ(n+1)`). -/
theorem car_cAnnihK_signed_cCreateK_signed_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    cAnnihK P ((σ : ℝ) * waveVectorABC P m) * cCreateK P ((τ : ℝ) * waveVectorABC P n)
      + cCreateK P ((τ : ℝ) * waveVectorABC P n) * cAnnihK P ((σ : ℝ) * waveVectorABC P m) = 0 := by
  have hne : Complex.exp (Complex.I *
        (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ))) ≠ 1 := by
    rw [show (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
        = ((((-τ : ℤ)) : ℝ) * waveVectorABC P n + ((σ : ℤ) : ℝ) * waveVectorABC P m : ℝ) by
      push_cast; ring]
    apply exp_combo_ne_one P n m (-τ) σ
    intro hdvd
    have := combo_not_dvd_of_ne P m n hmn hσ hτ
    apply this
    rwa [show σ * ((m.val : ℤ) + 1) - τ * ((n.val : ℤ) + 1)
        = (-τ) * ((n.val : ℤ) + 1) + σ * ((m.val : ℤ) + 1) by ring]
  have hroot : (Complex.exp (Complex.I *
        (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ)))) ^ (2 * P + 2) = 1 := by
    rw [show (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
        = ((((-τ : ℤ)) : ℝ) * waveVectorABC P n + ((σ : ℤ) : ℝ) * waveVectorABC P m : ℝ) by
      push_cast; ring]
    exact exp_combo_root P n m (-τ) σ
  have h := car_annihK_createK_zero P ((σ : ℝ) * waveVectorABC P m) ((τ : ℝ) * waveVectorABC P n)
    (by rw [show (((σ : ℝ) * waveVectorABC P m : ℝ) : ℂ) - (((τ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        exact hne)
    (by rw [show (((σ : ℝ) * waveVectorABC P m : ℝ) : ℂ) - (((τ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
            = (((σ : ℝ) * waveVectorABC P m - (τ : ℝ) * waveVectorABC P n : ℝ) : ℂ) by push_cast; ring]
        exact hroot)
  exact h

/-- Cross-pair `{c_{σ k_m}†, c_{τ k_n}†} = 0` (creates anticommute, always). -/
theorem car_cCreateK_signed_cCreateK_signed_cross (P : ℕ) (m n : Fin P) (σ τ : ℤ) :
    cCreateK P ((σ : ℝ) * waveVectorABC P m) * cCreateK P ((τ : ℝ) * waveVectorABC P n)
      + cCreateK P ((τ : ℝ) * waveVectorABC P n) * cCreateK P ((σ : ℝ) * waveVectorABC P m) = 0 := by
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_add,
      add_comm (cAnnihK P ((τ : ℝ) * waveVectorABC P n) * cAnnihK P ((σ : ℝ) * waveVectorABC P m)),
      car_annihK_annihK, Matrix.conjTranspose_zero]

set_option maxHeartbeats 800000 in
-- Raised: matching `car_annihK_createK_zero` against the big-operator factors (whnf).
/-- Cross-pair CAR `{c_{σ k_m}†, c_{τ k_n}} = 0` for DISTINCT active pairs (the
create-at-`m`, annihilate-at-`n` orientation; same vanishing difference). -/
theorem car_cCreateK_signed_cAnnihK_signed_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    cCreateK P ((σ : ℝ) * waveVectorABC P m) * cAnnihK P ((τ : ℝ) * waveVectorABC P n)
      + cAnnihK P ((τ : ℝ) * waveVectorABC P n) * cCreateK P ((σ : ℝ) * waveVectorABC P m) = 0 := by
  have hne : Complex.exp (Complex.I *
        (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ))) ≠ 1 := by
    rw [show (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ) : ℂ)
        = (((τ : ℤ) : ℝ) * waveVectorABC P n + ((-σ : ℤ) : ℝ) * waveVectorABC P m : ℝ) by
      push_cast; ring]
    apply exp_combo_ne_one P n m τ (-σ)
    intro hdvd
    have := combo_not_dvd_of_ne P n m hmn.symm hτ hσ
    apply this
    rwa [show τ * ((n.val : ℤ) + 1) - σ * ((m.val : ℤ) + 1)
        = τ * ((n.val : ℤ) + 1) + (-σ) * ((m.val : ℤ) + 1) by ring]
  have hroot : (Complex.exp (Complex.I *
        (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ)))) ^ (2 * P + 2) = 1 := by
    rw [show (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ) : ℂ)
        = (((τ : ℤ) : ℝ) * waveVectorABC P n + ((-σ : ℤ) : ℝ) * waveVectorABC P m : ℝ) by
      push_cast; ring]
    exact exp_combo_root P n m τ (-σ)
  have h := car_annihK_createK_zero P ((τ : ℝ) * waveVectorABC P n) ((σ : ℝ) * waveVectorABC P m)
    (by rw [show (((τ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P m : ℝ) : ℂ)
            = (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ) : ℂ) by push_cast; ring]
        exact hne)
    (by rw [show (((τ : ℝ) * waveVectorABC P n : ℝ) : ℂ) - (((σ : ℝ) * waveVectorABC P m : ℝ) : ℂ)
            = (((τ : ℝ) * waveVectorABC P n - (σ : ℝ) * waveVectorABC P m : ℝ) : ℂ) by push_cast; ring]
        exact hroot)
  -- h : cAnnihK(τk_n)·cCreateK(σk_m) + cCreateK(σk_m)·cAnnihK(τk_n) = 0
  linear_combination (norm := abel) h

set_option maxHeartbeats 1000000 in
-- Raised: the `numberOpK` def-unfold defeq against the big-operator fermion factors.
/-- `n_{σ k_m}` commutes with each individual fermion `c_{τ k_n}` / `c_{τ k_n}†` of a
DISTINCT active pair (`m ≠ n`). -/
theorem numberOpK_signed_commute_cAnnihK_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Commute (numberOpK P ((σ : ℝ) * waveVectorABC P m))
      (cAnnihK P ((τ : ℝ) * waveVectorABC P n)) := by
  rw [numberOpK]
  exact number_commute_single
    (c := cAnnihK P ((σ : ℝ) * waveVectorABC P m))
    (d := cCreateK P ((σ : ℝ) * waveVectorABC P m))
    (e := cAnnihK P ((τ : ℝ) * waveVectorABC P n))
    (car_annihK_annihK P ((σ : ℝ) * waveVectorABC P m) ((τ : ℝ) * waveVectorABC P n))
    (car_cCreateK_signed_cAnnihK_signed_cross P m n hmn hσ hτ)

set_option maxHeartbeats 1000000 in
-- Raised: same `numberOpK` def-unfold defeq cost at the symbolic dimension.
theorem numberOpK_signed_commute_cCreateK_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Commute (numberOpK P ((σ : ℝ) * waveVectorABC P m))
      (cCreateK P ((τ : ℝ) * waveVectorABC P n)) := by
  rw [numberOpK]
  exact number_commute_single
    (c := cAnnihK P ((σ : ℝ) * waveVectorABC P m))
    (d := cCreateK P ((σ : ℝ) * waveVectorABC P m))
    (e := cCreateK P ((τ : ℝ) * waveVectorABC P n))
    (car_cAnnihK_signed_cCreateK_signed_cross P m n hmn hσ hτ)
    (car_cCreateK_signed_cCreateK_signed_cross P m n σ τ)

/-- `c_{±k_m}` (annihilation) at the unsigned/negated active mode equals the σ-coerced
fermion (mirror of `cAnnihK_one_coe`/`cAnnihK_negone_coe`, packaged for the cross commute). -/
theorem numberOpK_pos_commute_cAnnihK_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) :
    Commute (numberOpK P (waveVectorABC P m)) (cAnnihK P (waveVectorABC P n))
      ∧ Commute (numberOpK P (waveVectorABC P m)) (cAnnihK P (-(waveVectorABC P n)))
      ∧ Commute (numberOpK P (waveVectorABC P m)) (cCreateK P (waveVectorABC P n))
      ∧ Commute (numberOpK P (waveVectorABC P m)) (cCreateK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := numberOpK_signed_commute_cAnnihK_cross P m n hmn (Or.inl rfl) (Or.inl rfl)
    rwa [numberOpK_one_coe, cAnnihK_one_coe] at this
  · have := numberOpK_signed_commute_cAnnihK_cross P m n hmn (Or.inl rfl) (Or.inr rfl)
    rwa [numberOpK_one_coe, cAnnihK_negone_coe] at this
  · have := numberOpK_signed_commute_cCreateK_cross P m n hmn (Or.inl rfl) (Or.inl rfl)
    rwa [numberOpK_one_coe, cCreateK_one_coe] at this
  · have := numberOpK_signed_commute_cCreateK_cross P m n hmn (Or.inl rfl) (Or.inr rfl)
    rwa [numberOpK_one_coe, cCreateK_negone_coe] at this

theorem numberOpK_neg_commute_cAnnihK_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) :
    Commute (numberOpK P (-(waveVectorABC P m))) (cAnnihK P (waveVectorABC P n))
      ∧ Commute (numberOpK P (-(waveVectorABC P m))) (cAnnihK P (-(waveVectorABC P n)))
      ∧ Commute (numberOpK P (-(waveVectorABC P m))) (cCreateK P (waveVectorABC P n))
      ∧ Commute (numberOpK P (-(waveVectorABC P m))) (cCreateK P (-(waveVectorABC P n))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := numberOpK_signed_commute_cAnnihK_cross P m n hmn (Or.inr rfl) (Or.inl rfl)
    rwa [numberOpK_negone_coe, cAnnihK_one_coe] at this
  · have := numberOpK_signed_commute_cAnnihK_cross P m n hmn (Or.inr rfl) (Or.inr rfl)
    rwa [numberOpK_negone_coe, cAnnihK_negone_coe] at this
  · have := numberOpK_signed_commute_cCreateK_cross P m n hmn (Or.inr rfl) (Or.inl rfl)
    rwa [numberOpK_negone_coe, cCreateK_one_coe] at this
  · have := numberOpK_signed_commute_cCreateK_cross P m n hmn (Or.inr rfl) (Or.inr rfl)
    rwa [numberOpK_negone_coe, cCreateK_negone_coe] at this

/-- Generic packaging: given that a number-like op `N` commutes with all four pair
fermions `c_{±k_n}`/`c_{±k_n}†` AND with `n_{k_n}`, `n_{-k_n}`, it commutes with each
pseudospin `τ^a_{k_n}`. -/
theorem commute_tauVecOp_of_commute_fermions (P : ℕ) (n : Fin P)
    (N : NQubitOp (2 * P + 2))
    (ca1 : Commute N (cAnnihK P (waveVectorABC P n)))
    (ca2 : Commute N (cAnnihK P (-(waveVectorABC P n))))
    (cc1 : Commute N (cCreateK P (waveVectorABC P n)))
    (cc2 : Commute N (cCreateK P (-(waveVectorABC P n))))
    (cz1 : Commute N (numberOpK P (waveVectorABC P n)))
    (cz2 : Commute N (numberOpK P (-(waveVectorABC P n))))
    (a : Fin 3) :
    Commute N (tauVecOp P (waveVectorABC P n) a) := by
  have hP : Commute N (tauPlus P (waveVectorABC P n)) := by
    unfold tauPlus; exact Commute.mul_right ca2 ca1
  have hM : Commute N (tauMinus P (waveVectorABC P n)) := by
    unfold tauMinus; exact Commute.mul_right cc1 cc2
  fin_cases a
  · change Commute N (tauX P (waveVectorABC P n)); unfold tauX; exact Commute.add_right hP hM
  · change Commute N (tauY P (waveVectorABC P n)); unfold tauY
    exact (Commute.sub_right hP hM).smul_right _
  · change Commute N (tauZ P (waveVectorABC P n)); unfold tauZ
    exact Commute.sub_right (Commute.sub_right (Commute.one_right _) cz1) cz2

/-- For `m ≠ n`, `n_{k_m}` commutes with `û·τ⃗_{k_n}` (cross-pair). -/
theorem numberOpK_pos_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    (u : Fin 3 → ℝ) :
    Commute (numberOpK P (waveVectorABC P m)) (dotTau P (waveVectorABC P n) u) := by
  obtain ⟨ca1, ca2, cc1, cc2⟩ := numberOpK_pos_commute_cAnnihK_cross P m n hmn
  have cz1 : Commute (numberOpK P (waveVectorABC P m)) (numberOpK P (waveVectorABC P n)) := by
    have := numberOpK_commute_cross P m n hmn (Or.inl rfl) (Or.inl rfl)
    rwa [numberOpK_one_coe, numberOpK_one_coe] at this
  have cz2 : Commute (numberOpK P (waveVectorABC P m)) (numberOpK P (-(waveVectorABC P n))) := by
    have := numberOpK_commute_cross P m n hmn (Or.inl rfl) (Or.inr rfl)
    rwa [numberOpK_one_coe, numberOpK_negone_coe] at this
  unfold dotTau
  exact Commute.sum_right _ _ _ (fun a _ =>
    (commute_tauVecOp_of_commute_fermions P n _ ca1 ca2 cc1 cc2 cz1 cz2 a).smul_right _)

/-- For `m ≠ n`, `n_{-k_m}` commutes with `û·τ⃗_{k_n}` (cross-pair). -/
theorem numberOpK_neg_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    (u : Fin 3 → ℝ) :
    Commute (numberOpK P (-(waveVectorABC P m))) (dotTau P (waveVectorABC P n) u) := by
  obtain ⟨ca1, ca2, cc1, cc2⟩ := numberOpK_neg_commute_cAnnihK_cross P m n hmn
  have cz1 : Commute (numberOpK P (-(waveVectorABC P m))) (numberOpK P (waveVectorABC P n)) := by
    have := numberOpK_commute_cross P m n hmn (Or.inr rfl) (Or.inl rfl)
    rwa [numberOpK_negone_coe, numberOpK_one_coe] at this
  have cz2 : Commute (numberOpK P (-(waveVectorABC P m))) (numberOpK P (-(waveVectorABC P n))) := by
    have := numberOpK_commute_cross P m n hmn (Or.inr rfl) (Or.inr rfl)
    rwa [numberOpK_negone_coe, numberOpK_negone_coe] at this
  unfold dotTau
  exact Commute.sum_right _ _ _ (fun a _ =>
    (commute_tauVecOp_of_commute_fermions P n _ ca1 ca2 cc1 cc2 cz1 cz2 a).smul_right _)

/-- For `m ≠ n`, `pairParity_{k_m}` commutes with `û·τ⃗_{k_n}` (cross-pair). -/
theorem pairParity_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    (u : Fin 3 → ℝ) :
    Commute (pairParity P (waveVectorABC P m)) (dotTau P (waveVectorABC P n) u) := by
  unfold pairParity
  exact Commute.mul_left
    (Commute.sub_left (Commute.one_left _)
      ((numberOpK_pos_commute_dotTau_cross P m n hmn u).smul_left 2))
    (Commute.sub_left (Commute.one_left _)
      ((numberOpK_neg_commute_dotTau_cross P m n hmn u).smul_left 2))

/-- Generic packaging (single-fermion side): if a fermion `e` cross-anticommutes with
all four pair-`m` fermions `c_{±k_m}`/`c_{±k_m}†`, then it commutes with each pseudospin
`τ^a_{k_m}` (the bilinear is even in the pair fermions). The `τ^z` case additionally
needs `e` to commute with `n_{±k_m}`, supplied separately. -/
theorem commute_tauVecOp_fermion_cross (P : ℕ) (m : Fin P) (e : NQubitOp (2 * P + 2))
    (ha1 : cAnnihK P (waveVectorABC P m) * e + e * cAnnihK P (waveVectorABC P m) = 0)
    (ha2 : cAnnihK P (-(waveVectorABC P m)) * e + e * cAnnihK P (-(waveVectorABC P m)) = 0)
    (hc1 : cCreateK P (waveVectorABC P m) * e + e * cCreateK P (waveVectorABC P m) = 0)
    (hc2 : cCreateK P (-(waveVectorABC P m)) * e + e * cCreateK P (-(waveVectorABC P m)) = 0)
    (cz1 : Commute (numberOpK P (waveVectorABC P m)) e)
    (cz2 : Commute (numberOpK P (-(waveVectorABC P m))) e)
    (a : Fin 3) :
    Commute (tauVecOp P (waveVectorABC P m) a) e := by
  have hP : Commute (tauPlus P (waveVectorABC P m)) e := by
    unfold tauPlus; exact number_commute_single ha1 ha2
  have hM : Commute (tauMinus P (waveVectorABC P m)) e := by
    unfold tauMinus; exact number_commute_single hc2 hc1
  fin_cases a
  · change Commute (tauX P (waveVectorABC P m)) e; unfold tauX; exact Commute.add_left hP hM
  · change Commute (tauY P (waveVectorABC P m)) e; unfold tauY
    exact (Commute.sub_left hP hM).smul_left _
  · change Commute (tauZ P (waveVectorABC P m)) e; unfold tauZ
    exact Commute.sub_left (Commute.sub_left (Commute.one_left _) cz1) cz2

/-- The four pair-`m`/pair-`n` anticommutators against a fixed pair-`n` fermion `e`,
unsigned-coerced. The signed cross-CAR lemmas (`car_*_signed_*_cross`) are converted to
the unsigned active-mode form via the `_coe` bridges. -/
theorem pairM_anticommute_fermion_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n)
    (e : NQubitOp (2 * P + 2))
    (he : e = cAnnihK P (waveVectorABC P n) ∨ e = cAnnihK P (-(waveVectorABC P n))
        ∨ e = cCreateK P (waveVectorABC P n) ∨ e = cCreateK P (-(waveVectorABC P n))) :
    (cAnnihK P (waveVectorABC P m) * e + e * cAnnihK P (waveVectorABC P m) = 0)
      ∧ (cAnnihK P (-(waveVectorABC P m)) * e + e * cAnnihK P (-(waveVectorABC P m)) = 0)
      ∧ (cCreateK P (waveVectorABC P m) * e + e * cCreateK P (waveVectorABC P m) = 0)
      ∧ (cCreateK P (-(waveVectorABC P m)) * e + e * cCreateK P (-(waveVectorABC P m)) = 0) := by
  -- Pull all signed cross-CAR facts and coerce signs.
  have caa : ∀ σ τ : ℤ, cAnnihK P ((σ:ℝ) * waveVectorABC P m) * cAnnihK P ((τ:ℝ) * waveVectorABC P n)
      + cAnnihK P ((τ:ℝ) * waveVectorABC P n) * cAnnihK P ((σ:ℝ) * waveVectorABC P m) = 0 :=
    fun σ τ => car_annihK_annihK P _ _
  have cac : ∀ {σ τ : ℤ}, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      cAnnihK P ((σ:ℝ) * waveVectorABC P m) * cCreateK P ((τ:ℝ) * waveVectorABC P n)
      + cCreateK P ((τ:ℝ) * waveVectorABC P n) * cAnnihK P ((σ:ℝ) * waveVectorABC P m) = 0 :=
    fun hσ hτ => car_cAnnihK_signed_cCreateK_signed_cross P m n hmn hσ hτ
  have cca : ∀ {σ τ : ℤ}, (σ = 1 ∨ σ = -1) → (τ = 1 ∨ τ = -1) →
      cCreateK P ((σ:ℝ) * waveVectorABC P m) * cAnnihK P ((τ:ℝ) * waveVectorABC P n)
      + cAnnihK P ((τ:ℝ) * waveVectorABC P n) * cCreateK P ((σ:ℝ) * waveVectorABC P m) = 0 :=
    fun hσ hτ => car_cCreateK_signed_cAnnihK_signed_cross P m n hmn hσ hτ
  have ccc : ∀ σ τ : ℤ, cCreateK P ((σ:ℝ) * waveVectorABC P m) * cCreateK P ((τ:ℝ) * waveVectorABC P n)
      + cCreateK P ((τ:ℝ) * waveVectorABC P n) * cCreateK P ((σ:ℝ) * waveVectorABC P m) = 0 :=
    fun σ τ => car_cCreateK_signed_cCreateK_signed_cross P m n σ τ
  -- coe rewrites for m and n.
  have ea1 := cAnnihK_one_coe P m; have ea2 := cAnnihK_negone_coe P m
  have ec1 := cCreateK_one_coe P m; have ec2 := cCreateK_negone_coe P m
  have ea1n := cAnnihK_one_coe P n; have ea2n := cAnnihK_negone_coe P n
  have ec1n := cCreateK_one_coe P n; have ec2n := cCreateK_negone_coe P n
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨by have := caa 1 1; rwa [ea1, ea1n] at this,
      by have := caa (-1) 1; rwa [ea2, ea1n] at this,
      by have := cca (Or.inl rfl) (Or.inl rfl); rwa [ec1, ea1n] at this,
      by have := cca (Or.inr rfl) (Or.inl rfl); rwa [ec2, ea1n] at this⟩
  · exact ⟨by have := caa 1 (-1); rwa [ea1, ea2n] at this,
      by have := caa (-1) (-1); rwa [ea2, ea2n] at this,
      by have := cca (Or.inl rfl) (Or.inr rfl); rwa [ec1, ea2n] at this,
      by have := cca (Or.inr rfl) (Or.inr rfl); rwa [ec2, ea2n] at this⟩
  · exact ⟨by have := cac (Or.inl rfl) (Or.inl rfl); rwa [ea1, ec1n] at this,
      by have := cac (Or.inr rfl) (Or.inl rfl); rwa [ea2, ec1n] at this,
      by have := ccc 1 1; rwa [ec1, ec1n] at this,
      by have := ccc (-1) 1; rwa [ec2, ec1n] at this⟩
  · exact ⟨by have := cac (Or.inl rfl) (Or.inr rfl); rwa [ea1, ec2n] at this,
      by have := cac (Or.inr rfl) (Or.inr rfl); rwa [ea2, ec2n] at this,
      by have := ccc 1 (-1); rwa [ec1, ec2n] at this,
      by have := ccc (-1) (-1); rwa [ec2, ec2n] at this⟩

set_option maxHeartbeats 1000000 in
-- Raised: the `number_commute_single` defeq against the big-operator fermion factors
-- (the bilinear `tauPlus`/`tauMinus` unfolds) is costly at the symbolic dimension 2^(2P+2).
/-- For `m ≠ n`, the dotted pseudospin `û·τ⃗_{k_m}` commutes with each pair-`n` fermion
`c_{±k_n}`/`c_{±k_n}†` (cross-pair: the bilinear is even, fermions cross-anticommute). -/
theorem dotTau_commute_fermion_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) (u : Fin 3 → ℝ)
    (e : NQubitOp (2 * P + 2))
    (he : e = cAnnihK P (waveVectorABC P n) ∨ e = cAnnihK P (-(waveVectorABC P n))
        ∨ e = cCreateK P (waveVectorABC P n) ∨ e = cCreateK P (-(waveVectorABC P n)))
    (cz1 : Commute (numberOpK P (waveVectorABC P m)) e)
    (cz2 : Commute (numberOpK P (-(waveVectorABC P m))) e) :
    Commute (dotTau P (waveVectorABC P m) u) e := by
  obtain ⟨ha1, ha2, hc1, hc2⟩ := pairM_anticommute_fermion_cross P m n hmn e he
  unfold dotTau
  exact Commute.sum_left _ _ _ (fun a _ =>
    (commute_tauVecOp_fermion_cross P m e ha1 ha2 hc1 hc2 cz1 cz2 a).smul_left _)

/-- For `m ≠ n`, `û·τ⃗_{k_m}` commutes with `n_{k_n}`, `n_{-k_n}` (cross-pair). -/
theorem dotTau_commute_numberOpK_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) (u : Fin 3 → ℝ) :
    Commute (dotTau P (waveVectorABC P m) u) (numberOpK P (waveVectorABC P n))
      ∧ Commute (dotTau P (waveVectorABC P m) u) (numberOpK P (-(waveVectorABC P n))) := by
  exact ⟨(numberOpK_pos_commute_dotTau_cross P n m hmn.symm u).symm,
    (numberOpK_neg_commute_dotTau_cross P n m hmn.symm u).symm⟩

set_option maxHeartbeats 1000000 in
-- Raised: the τ↔τ cross-commute assembles many big-operator commute facts; the
-- `commute_tauVecOp_of_commute_fermions` defeq is costly at the symbolic dimension.
/-- **Cross-mode dotTau commute.** For `m ≠ n`, `û·τ⃗_{k_m}` commutes with `ŵ·τ⃗_{k_n}`. -/
theorem dotTau_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) (u w : Fin 3 → ℝ) :
    Commute (dotTau P (waveVectorABC P m) u) (dotTau P (waveVectorABC P n) w) := by
  -- `Commute (dotTau k_m u)(numberOpK k_n)` (for the τ^z piece of pair n).
  obtain ⟨cnz1, cnz2⟩ := dotTau_commute_numberOpK_cross P m n hmn u
  -- `Commute (numberOpK k_m)(pair-n fermion)` (needed by dotTau_commute_fermion_cross).
  obtain ⟨pca1, pca2, pcc1, pcc2⟩ := numberOpK_pos_commute_cAnnihK_cross P m n hmn
  obtain ⟨nca1, nca2, ncc1, ncc2⟩ := numberOpK_neg_commute_cAnnihK_cross P m n hmn
  have ca1 := dotTau_commute_fermion_cross P m n hmn u _ (Or.inl rfl) pca1 nca1
  have ca2 := dotTau_commute_fermion_cross P m n hmn u _ (Or.inr (Or.inl rfl)) pca2 nca2
  have cc1 := dotTau_commute_fermion_cross P m n hmn u _ (Or.inr (Or.inr (Or.inl rfl))) pcc1 ncc1
  have cc2 := dotTau_commute_fermion_cross P m n hmn u _ (Or.inr (Or.inr (Or.inr rfl))) pcc2 ncc2
  -- `dotTau k_m u` commutes with each `τ^a_{k_n}`; sum over the RHS pseudospin axes.
  conv_rhs => rw [dotTau]
  refine Commute.sum_right _ _ _ (fun a _ => ?_)
  refine (Commute.smul_right ?_ _)
  exact commute_tauVecOp_of_commute_fermions P n _ ca1 ca2 cc1 cc2 cnz1 cnz2 a

/-- For `m ≠ n`, `HredZMode k_m` commutes with `û·τ⃗_{k_n}` (cross-mode). -/
theorem HredZMode_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) (u : Fin 3 → ℝ) :
    Commute (HredZMode P (waveVectorABC P m)) (dotTau P (waveVectorABC P n) u) := by
  have h := HredZMode_eq_dotTau P m
  change Commute (HredZMode P (waveVectorABC P m)) (dotTau P (waveVectorABC P n) u)
  rw [show waveVectorABC P m = waveVectorABC P m from rfl]
  rw [h]
  exact (dotTau_commute_dotTau_cross P m n hmn (bHat (waveVectorABC P m)) u).smul_left _

/-- For `m ≠ n`, `HredZMode k_m` commutes with `HredZMode k_n` (cross-mode). The seed
for the sum-exp factorization `exp(Σ) = ∏ exp`. -/
theorem HredZMode_commute_HredZMode_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) :
    Commute (HredZMode P (waveVectorABC P m)) (HredZMode P (waveVectorABC P n)) := by
  rw [HredZMode_eq_dotTau P n]
  exact (HredZMode_commute_dotTau_cross P m n hmn (bHat (waveVectorABC P n))).smul_right _

/-- For `m ≠ n`, `HredXMode k_m` commutes with `û·τ⃗_{k_n}` (cross-mode). -/
theorem HredXMode_commute_dotTau_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) (u : Fin 3 → ℝ) :
    Commute (HredXMode P (waveVectorABC P m)) (dotTau P (waveVectorABC P n) u) := by
  rw [HredXMode_eq_dotTau P m]
  exact (dotTau_commute_dotTau_cross P m n hmn zHat u).smul_left _

/-- For `m ≠ n`, `HredXMode k_m` commutes with `HredXMode k_n` (cross-mode). -/
theorem HredXMode_commute_HredXMode_cross (P : ℕ) (m n : Fin P) (hmn : m ≠ n) :
    Commute (HredXMode P (waveVectorABC P m)) (HredXMode P (waveVectorABC P n)) := by
  rw [HredXMode_eq_dotTau P n]
  exact (HredXMode_commute_dotTau_cross P m n hmn zHat).smul_right _

end

end QAOA.IsingChain.JordanWigner
