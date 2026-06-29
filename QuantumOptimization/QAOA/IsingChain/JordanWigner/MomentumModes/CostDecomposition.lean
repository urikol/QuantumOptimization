import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.Basic
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.ActiveSubspace
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.FourierCollection
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.ParityIdentity

/-!
# Momentum Modes (Cost Decomposition) — bilinear Fourier collection and the cost decomposition

The cost-side (Block B) bilinear Fourier collection (arXiv:1911.12259v2 SM
l.770–856). The periodic nearest-neighbour fermion bilinears are Fourier-collected by
directed-hopping product (`c†c†`, `c†c`, `cc†`, `cc`) via the dual orthogonality of
`MomentumModes.FourierCollection`, landing on the per-mode pseudospin cost operator
`HredZMode` on the active subspace. This is the bilinear analogue of the number collection,
and uses even fermion parity (`inActiveSubspace_imp_even`) on the active subspace.

## Main definitions
- `periodicBilinear`, `gridZMode`: the periodic NN fermion bilinear and the per-grid cost mode.
- `reflIdx`, `posGridIdx`, `negGridIdx`: grid reflection / pair index maps.

## Main statements
- `sum_periodic_eq_gridZMode`: the periodic bilinear sum equals the grid cost-mode sum.
- `gridZMode_pair_eq_HredZMode`: each `(k,−k)` grid pair collapses onto `HredZMode`.
- `HredZDecomp_active`: (B2-z) `Hred_z_pm false P + N_R·1 = Σ_k HredZMode` on the active subspace.
- `HredZDecomp_active_expectation`: the matching expectation-value form.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 13: BLOCK B — cost-side bilinear Fourier collection (B2-z)
--
-- The body+wrap fermion bilinears form the PERIODIC nearest-neighbour cost
-- operator `∑_{j} (c_j† − c_j)(c_{j+1}† + c_{j+1})` (mod N_R). We Fourier-collect
-- each of the four directed-hopping products `c†c†`, `c†c`, `cc†`, `cc` via the
-- proven dual orthogonality, landing on the per-mode pseudospin operator
-- `HredZMode` on the active subspace. This is the bilinear analogue of the
-- Section 11 NUMBER collection (`sum_numberOpK_grid_eq_sum_numberOp`).
-- ============================================================================

/-- The periodic nearest-neighbour fermion bilinear at grid site `j`:
`(c_j† − c_j)(c_{j+1}† + c_{j+1})`, with `j+1` cyclic in `Fin (2P+2)`. -/
def periodicBilinear (P : ℕ) (j : Fin (2 * P + 2)) : NQubitOp (2*P+2) :=
  (cCreate j - cAnnih j) * (cCreate (j + 1) + cAnnih (j + 1))

/-- The body-bond sum plus the wrap bond equals the periodic bilinear sum over the
full grid: `∑_{k} bodyBilinear k + wrapBilinear = ∑_{j} periodicBilinear j`. The
body bonds `k.castSucc ↦ k.castSucc+1` tile sites `0..2P`, and the wrap bond
`last ↦ 0 = last+1` is the missing `j = last` term. -/
theorem sum_body_add_wrap_eq_periodic (P : ℕ) :
    (∑ k : Fin (2*P+1), bodyBilinear P k) + wrapBilinear P =
      ∑ j : Fin (2 * P + 2), periodicBilinear P j := by
  -- The map `Fin (2P+1) → Fin (2P+2)`, `k ↦ k.castSucc`, together with `last`,
  -- exhausts the grid. Split off `j = last` from the RHS.
  rw [Fin.sum_univ_castSucc (fun j : Fin (2 * P + 2) => periodicBilinear P j)]
  have hbody : (∑ k : Fin (2*P+1), bodyBilinear P k)
      = ∑ i : Fin (2 * P + 1), periodicBilinear P i.castSucc := by
    apply Finset.sum_congr rfl
    intro k _
    unfold bodyBilinear periodicBilinear
    rfl
  have hwrap : wrapBilinear P = periodicBilinear P (Fin.last (2 * P + 1)) := by
    unfold wrapBilinear periodicBilinear
    rw [show (Fin.last (2 * P + 1) : Fin (2 * P + 2)) + 1 = (0 : Fin (2 * P + 2)) by
      apply Fin.ext; simp]
  rw [hbody, hwrap]

/-- INVERSE FOURIER for the annihilation operator: `c_j = (e^{−iπ/4}/√N_R) Σ_ℓ
e^{−i·gridK(ℓ)·j} c_{gridK ℓ}`. The dual orthogonality collapses the momentum sum
to the diagonal `j' = j`. This is the inverse of the `cAnnihK` definition and lets
us substitute position fermions by their momentum expansion. -/
theorem cAnnih_eq_grid_sum (P : ℕ) (j : Fin (2 * P + 2)) :
    cAnnih j =
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) •
        ∑ ℓ : Fin (2 * P + 2),
          Complex.exp (-(Complex.I * (gridK P ℓ * (j.val : ℝ)))) • cAnnihK P (gridK P ℓ) := by
  symm
  -- Per-(ℓ, j') scalar factor: combine the two prefactors into 1/N_R and the two
  -- exponentials into the position-difference phase.
  have hfac : ∀ (ℓ : Fin (2 * P + 2)) (j' : Fin (2 * P + 2)),
      Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ) *
        (Complex.exp (-(Complex.I * (gridK P ℓ * (j.val : ℝ)))) *
          (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ) *
            Complex.exp (Complex.I * (gridK P ℓ * (j'.val : ℝ)))))
      = ((1 : ℂ) / ((2 * P + 2 : ℕ) : ℂ)) *
          Complex.exp (Complex.I * (gridK P ℓ * (((j'.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ))) := by
    intro ℓ j'
    rw [← fourier_prefactor_mul P]
    rw [show Complex.exp (Complex.I * (gridK P ℓ * (((j'.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ)))
        = Complex.exp (-(Complex.I * (gridK P ℓ * (j.val : ℝ)))) *
            Complex.exp (Complex.I * (gridK P ℓ * (j'.val : ℝ))) by
      rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  -- expand cAnnihK and pull prefactors / combine the two sums into a double sum
  simp only [cAnnihK, Finset.smul_sum, smul_smul]
  -- swap the two sums: put the ℓ-sum innermost on the exponential
  rw [Finset.sum_comm]
  -- the diagonal `j' = j` term survives the ℓ-collapse, contributing `cAnnih j`
  rw [Finset.sum_eq_single j]
  · -- the j' = j term: the scalar prefactor sum is N_R · (1/N_R) = 1
    rw [← Finset.sum_smul, Finset.sum_congr rfl (fun ℓ _ => hfac ℓ j)]
    rw [show (∑ ℓ : Fin (2 * P + 2),
        ((1 : ℂ) / ((2 * P + 2 : ℕ) : ℂ)) *
          Complex.exp (Complex.I * (gridK P ℓ * (((j.val : ℤ) - (j.val : ℤ) : ℤ) : ℝ)))) = 1 by
      rw [← Finset.mul_sum, sub_self]
      rw [sum_exp_dual_orthogonality P 0]
      rw [if_pos (dvd_zero _), one_div,
        inv_mul_cancel₀ (by exact_mod_cast (by omega : (2 * P + 2 : ℕ) ≠ 0))]]
    rw [one_smul]
  · -- the off-diagonal j' ≠ j terms vanish: the ℓ-sum is zero by dual orthogonality
    intro j' _ hj'
    rw [← Finset.sum_smul, Finset.sum_congr rfl (fun ℓ _ => hfac ℓ j')]
    rw [← Finset.mul_sum, sum_exp_dual_orthogonality P ((j'.val : ℤ) - (j.val : ℤ))]
    rw [if_neg (by rw [dvd_sub_iff_eq]; exact hj'), mul_zero, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- INVERSE FOURIER for the creation operator: `c_j† = (e^{iπ/4}/√N_R) Σ_ℓ
e^{i·gridK(ℓ)·j} c_{gridK ℓ}†`. The adjoint of `cAnnih_eq_grid_sum`. -/
theorem cCreate_eq_grid_sum (P : ℕ) (j : Fin (2 * P + 2)) :
    cCreate j =
      (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) •
        ∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * (gridK P ℓ * (j.val : ℝ))) • cCreateK P (gridK P ℓ) := by
  rw [cCreate_eq_adjoint, cAnnih_eq_grid_sum P j]
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  -- conjugate the scalar prefactor and each summand
  congr 1
  · -- the prefactor conjugates: star(e^{-iπ/4}/√N) = e^{iπ/4}/√N
    rw [Complex.star_def, map_div₀, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_neg, map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  · apply Finset.sum_congr rfl
    intro ℓ _
    rw [Matrix.conjTranspose_smul, ← cCreateK]
    congr 1
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_neg, map_mul, Complex.conj_I, map_mul, Complex.conj_ofReal,
      Complex.conj_ofReal]
    ring

/-- POSITION-SITE orthogonality keyed by an integer combination: for `d : ℤ`,
`Σ_j e^{i·(2π d / N_R)·j} = N_R` if `N_R ∣ d`, else `0`. Mirrors
`sum_exp_dual_orthogonality` but sums over the position index `j`. -/
theorem sum_exp_pos_orthogonality (P : ℕ) (d : ℤ) :
    (∑ j : Fin (2*P+2),
        Complex.exp (Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2)) * (j.val : ℝ)))) =
      if ((2*P+2 : ℤ) ∣ d) then ((2*P+2 : ℕ) : ℂ) else 0 := by
  set ω := Complex.exp (Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))) with hω
  have hterm : ∀ j : Fin (2*P+2),
      Complex.exp (Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2)) * (j.val : ℝ)))
        = ω ^ (j.val) := by
    intro j
    rw [hω, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), Fin.sum_univ_eq_sum_range (fun j => ω ^ j)]
  have hroot : ω ^ (2*P+2) = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    rw [show ((2*P+2 : ℕ) : ℂ) * (Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2)))
        = (d : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
    rw [Complex.exp_int_mul_two_pi_mul_I]
  by_cases hdvd : (2*P+2 : ℤ) ∣ d
  · rw [if_pos hdvd]
    have hω1 : ω = 1 := by
      rw [hω]
      obtain ⟨c, hc⟩ := hdvd
      rw [show Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))
          = (c : ℂ) * (2 * Real.pi * Complex.I) by rw [hc]; push_cast; field_simp]
      rw [Complex.exp_int_mul_two_pi_mul_I]
    rw [hω1]; simp
  · rw [if_neg hdvd]
    have hωne : ω ≠ 1 := by
      intro hcontra
      apply hdvd
      rw [hω, Complex.exp_eq_one_iff] at hcontra
      obtain ⟨c, hc⟩ := hcontra
      refine ⟨c, ?_⟩
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hc' : (d : ℂ) / ((2 * P + 2 : ℝ) : ℂ) = (c : ℂ) := by
        have h2 : Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))
            = Complex.I * ((2 * Real.pi) * ((c : ℂ))) := by rw [hc]; ring
        have h3 : (2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℂ)
            = (2 * Real.pi) * (c : ℂ) := mul_left_cancel₀ hI h2
        have h2pi : (2 : ℂ) * Real.pi ≠ 0 := by simp [hpi]
        have h4 : (2 * Real.pi) * ((d : ℂ) / ((2 * P + 2 : ℝ) : ℂ))
            = (2 * Real.pi) * (c : ℂ) := by rw [← h3]; push_cast; ring
        exact mul_left_cancel₀ h2pi h4
      have h6 : (d : ℂ) = (((2 * P + 2 : ℤ) * c : ℤ) : ℂ) := by
        field_simp at hc'; push_cast at hc' ⊢; linear_combination hc'
      exact_mod_cast h6
    rw [geom_sum_eq hωne (2*P+2), hroot]; simp

/-- MASTER DIRECTED DOUBLE-FOURIER COLLAPSE. For integer signs `s, t` and per-mode
operator families `A, B : Fin (2P+2) → NQubitOp`, the bond sum of two
momentum-expanded position factors (with the `B` factor carried at the next site
`j+1`) collapses on the position index `j` to the selected `(ℓ, m)` pairs with
`N_R ∣ (s·ℓ + t·m)`, picking up the offset phase `e^{i·t·gridK(m)}`. -/
theorem directed_hop_collapse (P : ℕ) (s t : ℤ)
    (A B : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) :
    (∑ j : Fin (2 * P + 2),
        (∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • A ℓ) *
        (∑ m : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((t : ℝ) * gridK P m * ((j.val : ℝ) + 1))) • B m))
      = ∑ ℓ : Fin (2 * P + 2), ∑ m : Fin (2 * P + 2),
          (if ((2*P+2 : ℤ) ∣ (s * (ℓ.val : ℤ) + t * (m.val : ℤ))) then ((2*P+2 : ℕ) : ℂ) else 0) •
            (Complex.exp (Complex.I * ((t : ℝ) * gridK P m)) • (A ℓ * B m)) := by
  -- expand the bond product into a double sum per j, then swap to bring j innermost
  rw [Finset.sum_congr rfl (fun j _ => Finset.sum_mul_sum Finset.univ Finset.univ
    (fun ℓ => Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • A ℓ)
    (fun m => Complex.exp (Complex.I * ((t : ℝ) * gridK P m * ((j.val : ℝ) + 1))) • B m))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  -- the (ℓ,m) summand: Σ_j  e^{i s k_ℓ j} e^{i t k_m (j+1)} • (A ℓ * B m)
  -- = (Σ_j e^{i (s k_ℓ + t k_m) j}) e^{i t k_m} • (A ℓ * B m)
  rw [show (∑ j : Fin (2 * P + 2),
        (Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • A ℓ) *
          (Complex.exp (Complex.I * ((t : ℝ) * gridK P m * ((j.val : ℝ) + 1))) • B m))
      = (∑ j : Fin (2 * P + 2),
          Complex.exp (Complex.I *
            ((2 * Real.pi * ((s * (ℓ.val : ℤ) + t * (m.val : ℤ) : ℤ) : ℝ) / (2 * P + 2))
              * (j.val : ℝ)))) •
          (Complex.exp (Complex.I * ((t : ℝ) * gridK P m)) • (A ℓ * B m)) by
    rw [Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_smul_comm, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    unfold gridK
    push_cast
    ring]
  rw [sum_exp_pos_orthogonality P (s * (ℓ.val : ℤ) + t * (m.val : ℤ))]

/-- The next-site phase is periodic: `e^{i·t·gridK ℓ·(j+1).val} = e^{i·t·gridK ℓ·(j.val+1)}`
since `gridK ℓ · N_R = 2π ℓ`, so wrapping at `j = last` is invisible to the exponential. -/
theorem exp_gridK_succ (P : ℕ) (t : ℤ) (ℓ j : Fin (2 * P + 2)) :
    Complex.exp (Complex.I * ((t : ℝ) * gridK P ℓ * (((j + 1).val : ℝ)))) =
      Complex.exp (Complex.I * ((t : ℝ) * gridK P ℓ * ((j.val : ℝ) + 1))) := by
  by_cases hj : j = Fin.last (2 * P + 1)
  · -- j = last: (j+1).val = 0, but the exponential of 2π·t·ℓ is 1
    subst hj
    have hl0 : (Fin.last (2 * P + 1) + 1 : Fin (2 * P + 2)) = 0 := by apply Fin.ext; simp
    rw [hl0]
    have hlhs : Complex.exp (Complex.I * ((t : ℝ) * gridK P ℓ * (((0 : Fin (2 * P + 2)).val : ℝ))))
        = 1 := by simp
    have hrhs : Complex.exp (Complex.I *
        ((t : ℝ) * gridK P ℓ * (((Fin.last (2 * P + 1) : Fin (2 * P + 2)).val : ℝ) + 1))) = 1 := by
      rw [show ((Fin.last (2 * P + 1) : Fin (2 * P + 2)).val : ℝ) = (2 * P + 1 : ℝ) by
        simp [Fin.val_last]]
      rw [show Complex.I * ((t : ℝ) * gridK P ℓ * ((2 * P + 1 : ℝ) + 1))
          = (t * (ℓ.val : ℤ) : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
        unfold gridK
        push_cast
        have hne : ((2 * P + 2 : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast (by positivity : (2 * P + 2 : ℝ) ≠ 0)
        field_simp
        ring]
      rw [Complex.exp_int_mul_two_pi_mul_I]
    rw [hlhs, hrhs]
  · rw [Fin.val_add_one, if_neg hj]
    congr 2
    push_cast
    ring

/-- DIAGONAL collapse: when the index selector picks `m = ℓ` (i.e. `s = -t`, with
`t = ±1`), the double sum collapses to a single grid sum with the offset phase
`e^{i·t·gridK ℓ}`. -/
theorem hop_collapse_diag (P : ℕ) (s t : ℤ) (hst : s = -t) (ht : t = 1 ∨ t = -1)
    (A B : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) :
    (∑ ℓ : Fin (2 * P + 2), ∑ m : Fin (2 * P + 2),
        (if ((2*P+2 : ℤ) ∣ (s * (ℓ.val : ℤ) + t * (m.val : ℤ))) then ((2*P+2 : ℕ) : ℂ) else 0) •
          (Complex.exp (Complex.I * ((t : ℝ) * gridK P m)) • (A ℓ * B m)))
      = ((2*P+2 : ℕ) : ℂ) •
          ∑ ℓ : Fin (2 * P + 2),
            Complex.exp (Complex.I * ((t : ℝ) * gridK P ℓ)) • (A ℓ * B ℓ) := by
  subst hst
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_eq_single ℓ]
  · rw [show (-t) * (ℓ.val : ℤ) + t * (ℓ.val : ℤ) = 0 by ring, if_pos (dvd_zero _), smul_smul]
  · intro m _ hm
    rw [if_neg, zero_smul]
    intro hdvd
    apply hm
    -- N ∣ (-t·ℓ + t·m) = t·(m−ℓ); with t = ±1 this gives N ∣ (m−ℓ), hence m = ℓ
    have hmℓ : (2*P+2 : ℤ) ∣ ((m.val : ℤ) - (ℓ.val : ℤ)) := by
      have hd : (-t) * (ℓ.val : ℤ) + t * (m.val : ℤ) = t * ((m.val : ℤ) - (ℓ.val : ℤ)) := by ring
      rw [hd] at hdvd
      rcases ht with h1 | h1 <;> subst h1
      · simpa using hdvd
      · rw [show (-1 : ℤ) * ((m.val : ℤ) - (ℓ.val : ℤ)) = -((m.val : ℤ) - (ℓ.val : ℤ)) by ring] at hdvd
        exact (dvd_neg.mp hdvd)
    exact (dvd_sub_iff_eq P m ℓ).mp hmℓ
  · intro h; exact absurd (Finset.mem_univ ℓ) h

/-- The grid reflection index `ℓ ↦ (N_R − ℓ) mod N_R`, picking the mode `−k_ℓ`
(its grid value satisfies `gridK (reflIdx ℓ) = 2π − gridK ℓ` mod 2π). -/
def reflIdx (P : ℕ) (ℓ : Fin (2 * P + 2)) : Fin (2 * P + 2) :=
  ⟨(2 * P + 2 - ℓ.val) % (2 * P + 2), Nat.mod_lt _ (by omega)⟩

/-- `N_R ∣ (ℓ + m)` (with `ℓ, m : Fin N_R`) iff `m = reflIdx ℓ`. -/
theorem dvd_add_iff_reflIdx (P : ℕ) (ℓ m : Fin (2 * P + 2)) :
    ((2*P+2 : ℤ) ∣ ((ℓ.val : ℤ) + (m.val : ℤ))) ↔ m = reflIdx P ℓ := by
  constructor
  · intro hdvd
    apply Fin.ext
    change m.val = (2 * P + 2 - ℓ.val) % (2 * P + 2)
    obtain ⟨c, hc⟩ := hdvd
    have hℓ : ℓ.val < 2 * P + 2 := ℓ.isLt
    have hm : m.val < 2 * P + 2 := m.isLt
    -- ℓ + m = c·N with 0 ≤ ℓ+m < 2N, so c ∈ {0,1}; c=0 ⟹ ℓ=m=0, c=1 ⟹ m = N−ℓ
    have hcval : (ℓ.val : ℤ) + (m.val : ℤ) = (2*P+2 : ℤ) * c := hc
    have hc01 : c = 0 ∨ c = 1 := by
      rcases lt_trichotomy c 0 with h | h | h
      · exfalso; nlinarith [hcval]
      · left; exact h
      · rcases lt_trichotomy c 1 with h2 | h2 | h2
        · omega
        · right; exact h2
        · exfalso; nlinarith [hcval]
    rcases hc01 with h0 | h1
    · subst h0
      have hz : (ℓ.val : ℤ) + (m.val : ℤ) = 0 := by rw [hcval]; ring
      have hℓ0 : ℓ.val = 0 := by omega
      have hm0 : m.val = 0 := by omega
      rw [hm0, hℓ0]; simp
    · subst h1
      have hN : (ℓ.val : ℤ) + (m.val : ℤ) = (2*P+2 : ℤ) := by rw [hcval]; ring
      have hmv : m.val = 2 * P + 2 - ℓ.val := by omega
      rw [hmv, Nat.mod_eq_of_lt (by omega)]
  · intro h
    subst h
    change (2*P+2 : ℤ) ∣ ((ℓ.val : ℤ) + (((2 * P + 2 - ℓ.val) % (2 * P + 2) : ℕ) : ℤ))
    have hℓ : ℓ.val < 2 * P + 2 := ℓ.isLt
    by_cases hℓ0 : ℓ.val = 0
    · rw [hℓ0]
      simp [Nat.mod_self]
    · rw [Nat.mod_eq_of_lt (by omega)]
      refine ⟨1, ?_⟩
      have : (2 * P + 2 - ℓ.val : ℕ) = (2 * P + 2) - ℓ.val := rfl
      push_cast [Nat.cast_sub (by omega : ℓ.val ≤ 2 * P + 2)]
      ring

/-- REFLECTION collapse: when the index selector picks `m = reflIdx ℓ` (i.e.
`s = t = ±1`, so `N_R ∣ (s·ℓ + s·m)` ⟺ `N_R ∣ (ℓ + m)`), the double sum collapses
to a single grid sum over `(ℓ, reflIdx ℓ)` with offset phase `e^{i·t·gridK(reflIdx ℓ)}`. -/
theorem hop_collapse_refl (P : ℕ) (t : ℤ) (ht : t = 1 ∨ t = -1)
    (A B : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) :
    (∑ ℓ : Fin (2 * P + 2), ∑ m : Fin (2 * P + 2),
        (if ((2*P+2 : ℤ) ∣ (t * (ℓ.val : ℤ) + t * (m.val : ℤ))) then ((2*P+2 : ℕ) : ℂ) else 0) •
          (Complex.exp (Complex.I * ((t : ℝ) * gridK P m)) • (A ℓ * B m)))
      = ((2*P+2 : ℕ) : ℂ) •
          ∑ ℓ : Fin (2 * P + 2),
            Complex.exp (Complex.I * ((t : ℝ) * gridK P (reflIdx P ℓ))) • (A ℓ * B (reflIdx P ℓ)) := by
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro ℓ _
  rw [Finset.sum_eq_single (reflIdx P ℓ)]
  · rw [if_pos, smul_smul]
    -- N ∣ (t·ℓ + t·reflIdx ℓ): since m = reflIdx ℓ, N ∣ (ℓ + reflIdx ℓ)
    have hadd : (2*P+2 : ℤ) ∣ ((ℓ.val : ℤ) + ((reflIdx P ℓ).val : ℤ)) :=
      (dvd_add_iff_reflIdx P ℓ (reflIdx P ℓ)).mpr rfl
    rw [show t * (ℓ.val : ℤ) + t * ((reflIdx P ℓ).val : ℤ)
        = t * ((ℓ.val : ℤ) + ((reflIdx P ℓ).val : ℤ)) by ring]
    exact Dvd.dvd.mul_left hadd t
  · intro m _ hm
    rw [if_neg, zero_smul]
    intro hdvd
    apply hm
    -- N ∣ (t·ℓ + t·m) = t·(ℓ+m), with t = ±1 gives N ∣ (ℓ+m), so m = reflIdx ℓ
    have hℓm : (2*P+2 : ℤ) ∣ ((ℓ.val : ℤ) + (m.val : ℤ)) := by
      have hd : t * (ℓ.val : ℤ) + t * (m.val : ℤ) = t * ((ℓ.val : ℤ) + (m.val : ℤ)) := by ring
      rw [hd] at hdvd
      rcases ht with h1 | h1 <;> subst h1
      · simpa using hdvd
      · rw [show (-1 : ℤ) * ((ℓ.val : ℤ) + (m.val : ℤ)) = -((ℓ.val : ℤ) + (m.val : ℤ)) by ring]
          at hdvd
        exact (dvd_neg.mp hdvd)
    exact (dvd_add_iff_reflIdx P ℓ m).mp hℓm
  · intro h; exact absurd (Finset.mem_univ (reflIdx P ℓ)) h

/-- GENERIC DIAGONAL bond-sum collapse. Given position operators `op1, op2` with
inverse-Fourier expansions (phase signs `s` and `t = -s`, prefactors `pf1, pf2`
with `pf1·pf2 = 1/N_R`), the bond sum collapses on the diagonal `m = ℓ`. -/
theorem bond_diag (P : ℕ) (s t : ℤ) (hst : s = -t) (ht : t = 1 ∨ t = -1)
    (op1 op2 : Fin (2 * P + 2) → NQubitOp (2 * P + 2))
    (Op1 Op2 : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) (pf1 pf2 c : ℂ)
    (hpf : pf1 * pf2 * ((2 * P + 2 : ℕ) : ℂ) = c)
    (hsub1 : ∀ j : Fin (2 * P + 2), op1 j =
      pf1 • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • Op1 ℓ)
    (hsub2 : ∀ j : Fin (2 * P + 2), op2 j =
      pf2 • ∑ m : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((t : ℝ) * gridK P m * (j.val : ℝ))) • Op2 m) :
    (∑ j : Fin (2 * P + 2), op1 j * op2 (j + 1)) =
      c • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((t : ℝ) * gridK P ℓ)) • (Op1 ℓ * Op2 ℓ) := by
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [hsub1 j, hsub2 (j + 1), smul_mul_smul_comm] :
    ∀ j ∈ Finset.univ, op1 j * op2 (j + 1) = (pf1 * pf2) •
      ((∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • Op1 ℓ) *
        (∑ m : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((t : ℝ) * gridK P m * (((j + 1).val) : ℝ))) • Op2 m)))]
  rw [← Finset.smul_sum]
  -- convert the next-site phase to (j.val + 1)
  simp only [exp_gridK_succ P t]
  rw [directed_hop_collapse P s t Op1 Op2]
  rw [hst]
  rw [hop_collapse_diag P (-t) t (by ring) ht]
  rw [smul_smul, hpf]

/-- GENERIC REFLECTION bond-sum collapse. As `bond_diag` but with phase signs
`s = t = ±1`, so the selector picks `m = reflIdx ℓ` (the `−k` partner). -/
theorem bond_refl (P : ℕ) (s t : ℤ) (hst : s = t) (ht : t = 1 ∨ t = -1)
    (op1 op2 : Fin (2 * P + 2) → NQubitOp (2 * P + 2))
    (Op1 Op2 : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) (pf1 pf2 c : ℂ)
    (hpf : pf1 * pf2 * ((2 * P + 2 : ℕ) : ℂ) = c)
    (hsub1 : ∀ j : Fin (2 * P + 2), op1 j =
      pf1 • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • Op1 ℓ)
    (hsub2 : ∀ j : Fin (2 * P + 2), op2 j =
      pf2 • ∑ m : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((t : ℝ) * gridK P m * (j.val : ℝ))) • Op2 m) :
    (∑ j : Fin (2 * P + 2), op1 j * op2 (j + 1)) =
      c • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * ((t : ℝ) * gridK P (reflIdx P ℓ))) • (Op1 ℓ * Op2 (reflIdx P ℓ)) := by
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [hsub1 j, hsub2 (j + 1), smul_mul_smul_comm] :
    ∀ j ∈ Finset.univ, op1 j * op2 (j + 1) = (pf1 * pf2) •
      ((∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((s : ℝ) * gridK P ℓ * (j.val : ℝ))) • Op1 ℓ) *
        (∑ m : Fin (2 * P + 2),
          Complex.exp (Complex.I * ((t : ℝ) * gridK P m * (((j + 1).val) : ℝ))) • Op2 m)))]
  rw [← Finset.smul_sum]
  simp only [exp_gridK_succ P t]
  rw [directed_hop_collapse P s t Op1 Op2]
  rw [hst]
  rw [hop_collapse_refl P t ht]
  rw [smul_smul, hpf]

/-- `cCreate j` in the canonical bond form (phase sign `+1`, prefactor `e^{iπ/4}/√N`). -/
theorem cCreate_sub_form (P : ℕ) (j : Fin (2 * P + 2)) :
    cCreate j =
      (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) •
        ∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * gridK P ℓ * (j.val : ℝ))) •
            cCreateK P (gridK P ℓ) := by
  rw [cCreate_eq_grid_sum P j]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 2
  push_cast; ring

/-- `cAnnih j` in the canonical bond form (phase sign `−1`, prefactor `e^{−iπ/4}/√N`). -/
theorem cAnnih_sub_form (P : ℕ) (j : Fin (2 * P + 2)) :
    cAnnih j =
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) •
        ∑ ℓ : Fin (2 * P + 2),
          Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P ℓ * (j.val : ℝ))) •
            cAnnihK P (gridK P ℓ) := by
  rw [cAnnih_eq_grid_sum P j]
  congr 1
  apply Finset.sum_congr rfl
  intro ℓ _
  congr 2
  push_cast; ring

/-- Prefactor product `a·b·N = 1` (the `c†c`/`cc†` "normal" hops). -/
theorem pf_ab_mul (P : ℕ) :
    (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) *
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) *
      ((2 * P + 2 : ℕ) : ℂ) = 1 := by
  rw [fourier_prefactor_mul, one_div,
    inv_mul_cancel₀ (by exact_mod_cast (by omega : (2 * P + 2 : ℕ) ≠ 0))]

/-- Prefactor product `a·a·N = i` (the `c†c†` anomalous creation hop). -/
theorem pf_aa_mul (P : ℕ) :
    (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) *
      (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) *
      ((2 * P + 2 : ℕ) : ℂ) = Complex.I := by
  rw [div_mul_div_comm, ← Complex.exp_add]
  rw [show Complex.I * (Real.pi / 4 : ℂ) + Complex.I * (Real.pi / 4 : ℂ)
      = (Real.pi / 2 : ℂ) * Complex.I by ring]
  rw [Complex.exp_mul_I, Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  rw [show ((0 : ℂ) + 1 * Complex.I) = Complex.I by ring]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hne : ((2 * P + 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * P + 2 : ℝ) ≠ 0)
  push_cast
  field_simp

/-- Prefactor product `b·b·N = −i` (the `cc` anomalous annihilation hop). -/
theorem pf_bb_mul (P : ℕ) :
    (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) *
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) *
      ((2 * P + 2 : ℕ) : ℂ) = -Complex.I := by
  rw [div_mul_div_comm, ← Complex.exp_add]
  rw [show -(Complex.I * (Real.pi / 4 : ℂ)) + -(Complex.I * (Real.pi / 4 : ℂ))
      = (-(Real.pi / 2 : ℂ)) * Complex.I by ring]
  rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  rw [show ((0 : ℂ) + -1 * Complex.I) = -Complex.I by ring]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  have hne : ((2 * P + 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * P + 2 : ℝ) ≠ 0)
  push_cast
  field_simp

/-- `S2 = Σ_j c_j† c_{j+1}` collected: `Σ_ℓ e^{−i·gridK ℓ}·(c_{k_ℓ}† c_{k_ℓ})`. -/
theorem sum_cCreate_cAnnih_succ (P : ℕ) :
    (∑ j : Fin (2 * P + 2), cCreate j * cAnnih (j + 1)) =
      (1 : ℂ) • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P ℓ)) •
          (cCreateK P (gridK P ℓ) * cAnnihK P (gridK P ℓ)) :=
  bond_diag P 1 (-1) (by norm_num) (Or.inr rfl) cCreate cAnnih
    (fun ℓ => cCreateK P (gridK P ℓ)) (fun ℓ => cAnnihK P (gridK P ℓ)) _ _ 1
    (pf_ab_mul P) (cCreate_sub_form P) (cAnnih_sub_form P)

/-- `S3 = Σ_j c_j c_{j+1}†` collected: `Σ_ℓ e^{+i·gridK ℓ}·(c_{k_ℓ} c_{k_ℓ}†)`. -/
theorem sum_cAnnih_cCreate_succ (P : ℕ) :
    (∑ j : Fin (2 * P + 2), cAnnih j * cCreate (j + 1)) =
      (1 : ℂ) • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * gridK P ℓ)) •
          (cAnnihK P (gridK P ℓ) * cCreateK P (gridK P ℓ)) :=
  bond_diag P (-1) 1 (by norm_num) (Or.inl rfl) cAnnih cCreate
    (fun ℓ => cAnnihK P (gridK P ℓ)) (fun ℓ => cCreateK P (gridK P ℓ))
    (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ))
    (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) 1
    (by rw [mul_comm (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ))]
        exact pf_ab_mul P) (cAnnih_sub_form P) (cCreate_sub_form P)

/-- `S1 = Σ_j c_j† c_{j+1}†` collected: `i·Σ_ℓ e^{i·gridK(reflIdx ℓ)}·(c_{k_ℓ}† c_{−k_ℓ}†)`. -/
theorem sum_cCreate_cCreate_succ (P : ℕ) :
    (∑ j : Fin (2 * P + 2), cCreate j * cCreate (j + 1)) =
      Complex.I • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ))) •
          (cCreateK P (gridK P ℓ) * cCreateK P (gridK P (reflIdx P ℓ))) :=
  bond_refl P 1 1 rfl (Or.inl rfl) cCreate cCreate
    (fun ℓ => cCreateK P (gridK P ℓ)) (fun ℓ => cCreateK P (gridK P ℓ)) _ _ Complex.I
    (pf_aa_mul P) (cCreate_sub_form P) (cCreate_sub_form P)

/-- `S4 = Σ_j c_j c_{j+1}` collected: `−i·Σ_ℓ e^{−i·gridK(reflIdx ℓ)}·(c_{k_ℓ} c_{−k_ℓ})`. -/
theorem sum_cAnnih_cAnnih_succ (P : ℕ) :
    (∑ j : Fin (2 * P + 2), cAnnih j * cAnnih (j + 1)) =
      (-Complex.I) • ∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ))) •
          (cAnnihK P (gridK P ℓ) * cAnnihK P (gridK P (reflIdx P ℓ))) :=
  bond_refl P (-1) (-1) rfl (Or.inr rfl) cAnnih cAnnih
    (fun ℓ => cAnnihK P (gridK P ℓ)) (fun ℓ => cAnnihK P (gridK P ℓ)) _ _ (-Complex.I)
    (pf_bb_mul P) (cAnnih_sub_form P) (cAnnih_sub_form P)

/-- The periodic bilinear sum decomposes into the four directed hopping sums:
`Σ_j (c_j†−c_j)(c_{j+1}†+c_{j+1}) = S1 + S2 − S3 − S4`. -/
theorem sum_periodic_eq_four (P : ℕ) :
    (∑ j : Fin (2 * P + 2), periodicBilinear P j) =
      (∑ j : Fin (2 * P + 2), cCreate j * cCreate (j + 1)) +
        (∑ j : Fin (2 * P + 2), cCreate j * cAnnih (j + 1)) -
        (∑ j : Fin (2 * P + 2), cAnnih j * cCreate (j + 1)) -
        (∑ j : Fin (2 * P + 2), cAnnih j * cAnnih (j + 1)) := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold periodicBilinear
  noncomm_ring

/-- The per-grid-mode cost operator after Fourier collection: collects the four
directed-hopping contributions anchored at grid index `ℓ` (with its `−k`-partner
`reflIdx ℓ` for the anomalous terms). Summing over `ℓ` gives `Σ_j periodicBilinear`. -/
def gridZMode (P : ℕ) (ℓ : Fin (2 * P + 2)) : NQubitOp (2 * P + 2) :=
  (Complex.I * Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ)))) •
      (cCreateK P (gridK P ℓ) * cCreateK P (gridK P (reflIdx P ℓ))) +
    (Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P ℓ))) •
      (cCreateK P (gridK P ℓ) * cAnnihK P (gridK P ℓ)) -
    (Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * gridK P ℓ))) •
      (cAnnihK P (gridK P ℓ) * cCreateK P (gridK P ℓ)) +
    (Complex.I * Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ)))) •
      (cAnnihK P (gridK P ℓ) * cAnnihK P (gridK P (reflIdx P ℓ)))

/-- The periodic bilinear sum equals the grid-mode sum (full Fourier collection). -/
theorem sum_periodic_eq_gridZMode (P : ℕ) :
    (∑ j : Fin (2 * P + 2), periodicBilinear P j) =
      ∑ ℓ : Fin (2 * P + 2), gridZMode P ℓ := by
  rw [sum_periodic_eq_four, sum_cCreate_cCreate_succ, sum_cCreate_cAnnih_succ,
    sum_cAnnih_cCreate_succ, sum_cAnnih_cAnnih_succ]
  simp only [one_smul]
  -- distribute the leading I / −I scalars into the per-ℓ summands and recombine
  rw [Finset.smul_sum, Finset.smul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro ℓ _
  unfold gridZMode
  rw [smul_smul, smul_smul]
  rw [show (-Complex.I * Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ))))
      = -(Complex.I * Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * gridK P (reflIdx P ℓ)))) by ring]
  rw [neg_smul, sub_neg_eq_add]

/-- The grid index `n+1` (for `n : Fin P`) as an element of `Fin (2P+2)`. -/
def posGridIdx (P : ℕ) (n : Fin P) : Fin (2 * P + 2) := ⟨n.val + 1, by omega⟩

/-- The grid index `2P+1−n` (for `n : Fin P`) as an element of `Fin (2P+2)`. -/
def negGridIdx (P : ℕ) (n : Fin P) : Fin (2 * P + 2) := ⟨2 * P + 1 - n.val, by omega⟩

/-- GENERIC GRID REINDEX: any operator family summed over the grid splits into the
self-conjugate modes (index `0` and `P+1`) plus the active pairs (`posGridIdx`,
`negGridIdx`). Mirrors `sum_numberOpK_grid_reindex` for an arbitrary `f`. -/
theorem sum_grid_reindex (P : ℕ) (f : Fin (2 * P + 2) → NQubitOp (2 * P + 2)) :
    (∑ ℓ : Fin (2 * P + 2), f ℓ) =
      f ⟨0, by omega⟩ + f ⟨P + 1, by omega⟩ +
        ∑ n : Fin P, (f (posGridIdx P n) + f (negGridIdx P n)) := by
  have hcast : 2 * P + 2 = (P + 1) + (P + 1) := by ring
  rw [← Equiv.sum_comp (finCongr hcast).symm (fun ℓ : Fin (2 * P + 2) => f ℓ)]
  rw [Fin.sum_univ_add]
  have hval : ∀ z : Fin ((P + 1) + (P + 1)),
      (finCongr hcast).symm z = (⟨z.val, by rw [hcast]; exact z.isLt⟩ : Fin (2 * P + 2)) := by
    intro z; apply Fin.ext; rw [finCongr_symm, finCongr_apply_coe]
  simp only [hval]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hp1 : f (⟨(Fin.castAdd (P + 1) (0 : Fin (P + 1))).val,
        by rw [hcast]; exact (Fin.castAdd (P + 1) (0 : Fin (P + 1))).isLt⟩ : Fin (2 * P + 2))
      = f ⟨0, by omega⟩ := by
    congr 1
  have hp3 : f (⟨(Fin.natAdd (P + 1) (0 : Fin (P + 1))).val,
        by rw [hcast]; exact (Fin.natAdd (P + 1) (0 : Fin (P + 1))).isLt⟩ : Fin (2 * P + 2))
      = f ⟨P + 1, by omega⟩ := by
    congr 1
  have hp2 : (∑ i : Fin P, f (⟨(Fin.castAdd (P + 1) i.succ).val,
        by rw [hcast]; exact (Fin.castAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2)))
      = ∑ n : Fin P, f (posGridIdx P n) := by
    apply Finset.sum_congr rfl
    intro i _; congr 1
  have hp4 : (∑ i : Fin P, f (⟨(Fin.natAdd (P + 1) i.succ).val,
        by rw [hcast]; exact (Fin.natAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2)))
      = ∑ n : Fin P, f (negGridIdx P n) := by
    rw [← Equiv.sum_comp Fin.revPerm
      (fun i : Fin P => f (⟨(Fin.natAdd (P + 1) i.succ).val,
        by rw [hcast]; exact (Fin.natAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2)))]
    apply Finset.sum_congr rfl
    intro n _
    rw [Fin.revPerm_apply]
    congr 1
    apply Fin.ext
    simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_rev, negGridIdx]
    omega
  rw [hp1, hp3, hp2, hp4, Finset.sum_add_distrib]
  abel

/-- `reflIdx` maps the `+k_n` grid index to the `−k_n` index. -/
theorem reflIdx_posGridIdx (P : ℕ) (n : Fin P) :
    reflIdx P (posGridIdx P n) = negGridIdx P n := by
  apply Fin.ext
  have hn : n.val < P := n.isLt
  change (2 * P + 2 - (n.val + 1)) % (2 * P + 2) = 2 * P + 1 - n.val
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `reflIdx` maps the `−k_n` grid index to the `+k_n` index. -/
theorem reflIdx_negGridIdx (P : ℕ) (n : Fin P) :
    reflIdx P (negGridIdx P n) = posGridIdx P n := by
  apply Fin.ext
  have hn : n.val < P := n.isLt
  change (2 * P + 2 - (2 * P + 1 - n.val)) % (2 * P + 2) = n.val + 1
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The `+k_n` grid value is the active wave vector `k_n`. -/
theorem gridK_posGridIdx (P : ℕ) (n : Fin P) :
    gridK P (posGridIdx P n) = waveVectorABC P n := by
  unfold gridK posGridIdx waveVectorABC
  push_cast
  ring

/-- The `−k_n` grid value is `2π − k_n`. -/
theorem gridK_negGridIdx (P : ℕ) (n : Fin P) :
    gridK P (negGridIdx P n) = 2 * Real.pi - waveVectorABC P n := by
  have hn : n.val < P := n.isLt
  unfold gridK negGridIdx waveVectorABC
  rw [show ((2 * P + 1 - n.val : ℕ) : ℝ) = (2 * P + 1 : ℝ) - (n.val : ℝ) by
    have : n.val ≤ 2 * P + 1 := by omega
    push_cast [Nat.cast_sub this]; ring]
  have hne : (2 * P + 2 : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- `c_k` is `2π`-periodic for the creation operator: `c_{k+2π}† = c_k†`. -/
theorem cCreateK_periodic_2pi (P : ℕ) (k : ℝ) :
    cCreateK P (k + 2 * Real.pi) = cCreateK P k := by
  unfold cCreateK
  rw [cAnnihK_periodic_2pi]

/-- `c_{2π−k} = c_{−k}` (annihilation, via `2π`-periodicity). -/
theorem cAnnihK_two_pi_sub (P : ℕ) (k : ℝ) :
    cAnnihK P (2 * Real.pi - k) = cAnnihK P (-k) := by
  rw [show (2 * Real.pi - k : ℝ) = (-k) + 2 * Real.pi by ring, cAnnihK_periodic_2pi]

/-- `c_{2π−k}† = c_{−k}†` (creation, via `2π`-periodicity). -/
theorem cCreateK_two_pi_sub (P : ℕ) (k : ℝ) :
    cCreateK P (2 * Real.pi - k) = cCreateK P (-k) := by
  rw [show (2 * Real.pi - k : ℝ) = (-k) + 2 * Real.pi by ring, cCreateK_periodic_2pi]

/-- CAR hole identity: `c_k c_k† = 1 − n_k`. -/
theorem cAnnihK_cCreateK_eq (P : ℕ) (k : ℝ) :
    cAnnihK P k * cCreateK P k = 1 - numberOpK P k := by
  have hcar := car_annihK_createK_same P k
  unfold numberOpK
  rw [eq_sub_iff_add_eq]; exact hcar

/-- Anomalous reorder: `c_k c_{−k} = −(c_{−k} c_k)` (distinct-mode CAR). -/
theorem cAnnihK_swap (P : ℕ) (k : ℝ) :
    cAnnihK P k * cAnnihK P (-k) = -(cAnnihK P (-k) * cAnnihK P k) := by
  have h := car_annihK_annihK P k (-k)
  rw [eq_neg_iff_add_eq_zero]; exact h

/-- Anomalous reorder: `c_{−k}† c_k† = −(c_k† c_{−k}†)`. -/
theorem cCreateK_swap (P : ℕ) (k : ℝ) :
    cCreateK P (-k) * cCreateK P k = -(cCreateK P k * cCreateK P (-k)) := by
  have h := car_annihK_annihK P k (-k)
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_neg]
  congr 1
  rw [eq_neg_iff_add_eq_zero]; exact h

/-- `gridZMode` at the `+k_n` grid index, rewritten with explicit `±k` momentum
operators (`k = waveVectorABC P n`). -/
theorem gridZMode_posGridIdx (P : ℕ) (n : Fin P) :
    gridZMode P (posGridIdx P n) =
      (Complex.I * Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * (2 * Real.pi - waveVectorABC P n)))) •
          (cCreateK P (waveVectorABC P n) * cCreateK P (-waveVectorABC P n)) +
        (Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * waveVectorABC P n))) •
          (cCreateK P (waveVectorABC P n) * cAnnihK P (waveVectorABC P n)) -
        (Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * waveVectorABC P n))) •
          (cAnnihK P (waveVectorABC P n) * cCreateK P (waveVectorABC P n)) +
        (Complex.I * Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * (2 * Real.pi - waveVectorABC P n)))) •
          (cAnnihK P (waveVectorABC P n) * cAnnihK P (-waveVectorABC P n)) := by
  unfold gridZMode
  rw [reflIdx_posGridIdx, gridK_posGridIdx, gridK_negGridIdx]
  rw [cCreateK_two_pi_sub, cAnnihK_two_pi_sub]
  push_cast
  ring_nf

/-- `gridZMode` at the `−k_n` grid index, rewritten with explicit `±k` momentum
operators (`k = waveVectorABC P n`; the index has grid value `2π−k`). -/
theorem gridZMode_negGridIdx (P : ℕ) (n : Fin P) :
    gridZMode P (negGridIdx P n) =
      (Complex.I * Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * waveVectorABC P n))) •
          (cCreateK P (-waveVectorABC P n) * cCreateK P (waveVectorABC P n)) +
        (Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * (2 * Real.pi - waveVectorABC P n)))) •
          (cCreateK P (-waveVectorABC P n) * cAnnihK P (-waveVectorABC P n)) -
        (Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * (2 * Real.pi - waveVectorABC P n)))) •
          (cAnnihK P (-waveVectorABC P n) * cCreateK P (-waveVectorABC P n)) +
        (Complex.I * Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * waveVectorABC P n))) •
          (cAnnihK P (-waveVectorABC P n) * cAnnihK P (waveVectorABC P n)) := by
  unfold gridZMode
  rw [reflIdx_negGridIdx, gridK_negGridIdx, gridK_posGridIdx]
  rw [cCreateK_two_pi_sub, cAnnihK_two_pi_sub]
  push_cast
  ring_nf

/-- Phase periodicity: `e^{i·(2π−k)} = e^{−ik}`. -/
theorem exp_two_pi_sub (k : ℝ) :
    Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * (2 * Real.pi - k))) =
      Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * k)) := by
  rw [show Complex.I * (((1 : ℤ) : ℝ) * (2 * Real.pi - k) : ℂ)
      = Complex.I * (((-1 : ℤ) : ℝ) * k : ℂ) + (1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Phase periodicity: `e^{−i·(2π−k)} = e^{ik}`. -/
theorem exp_neg_two_pi_sub (k : ℝ) :
    Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * (2 * Real.pi - k))) =
      Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * k)) := by
  rw [show Complex.I * (((-1 : ℤ) : ℝ) * (2 * Real.pi - k) : ℂ)
      = Complex.I * (((1 : ℤ) : ℝ) * k : ℂ) + (-1 : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **PAIR RECOGNITION (the heart of Block B).** The two grid-mode contributions of
an active pair `(k_n, −k_n)` assemble — as an OPERATOR identity (using same-mode CAR
`c c† = 1 − n` and the distinct-mode anticommutators) — into the per-mode pseudospin
cost Hamiltonian `HredZMode P (k_n) = 2 sin k_n·τ^x − 2 cos k_n·τ^z`. -/
theorem gridZMode_pair_eq_HredZMode (P : ℕ) (n : Fin P) :
    gridZMode P (posGridIdx P n) + gridZMode P (negGridIdx P n) =
      HredZMode P (waveVectorABC P n) := by
  set k := waveVectorABC P n with hk
  rw [gridZMode_posGridIdx, gridZMode_negGridIdx]
  -- simplify the 2π-shifted phases
  simp only [exp_two_pi_sub, exp_neg_two_pi_sub]
  -- rewrite the same-mode `c c† = 1 − n` holes and the anomalous reorderings
  rw [cAnnihK_cCreateK_eq P k]
  rw [show cAnnihK P (-k) * cCreateK P (-k) = 1 - numberOpK P (-k) from cAnnihK_cCreateK_eq P (-k)]
  rw [cCreateK_swap P k, cAnnihK_swap P k]
  -- recognize tauPlus, tauMinus, tauX, tauZ; collect with the e^{±ik} phases
  unfold HredZMode tauX tauZ tauPlus tauMinus numberOpK
  -- fold all `waveVectorABC P n` occurrences to `k`
  simp only [← hk]
  -- convert e^{±ik} to cos/sin form
  rw [show Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * k)) = Complex.exp ((k : ℂ) * Complex.I) by
    congr 1; push_cast; ring]
  rw [show Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * k)) = Complex.exp ((-k : ℂ) * Complex.I) by
    congr 1; push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  -- now a linear identity in the 5 operator monomials with cos/sin/I coefficients
  match_scalars <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

/-- `reflIdx` fixes the `k=0` self-conjugate index. -/
theorem reflIdx_zero (P : ℕ) : reflIdx P ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  apply Fin.ext
  change (2 * P + 2 - 0) % (2 * P + 2) = 0
  simp

/-- `reflIdx` fixes the `k=π` self-conjugate index. -/
theorem reflIdx_mid (P : ℕ) : reflIdx P ⟨P + 1, by omega⟩ = ⟨P + 1, by omega⟩ := by
  apply Fin.ext
  change (2 * P + 2 - (P + 1)) % (2 * P + 2) = P + 1
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- `gridK` at the reindex `k=0` index is `0`. -/
theorem gridK_zero' (P : ℕ) : gridK P ⟨0, by omega⟩ = 0 := by
  unfold gridK; simp

/-- `gridK` at the reindex `k=π` index is `π`. -/
theorem gridK_mid' (P : ℕ) : gridK P ⟨P + 1, by omega⟩ = Real.pi := by
  unfold gridK
  rw [show ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 by push_cast; ring]
  have hne : (2 * P + 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- The self-conjugate `k=0` mode contributes `2 n_0 − 1`. -/
theorem gridZMode_zero (P : ℕ) :
    gridZMode P ⟨0, by omega⟩ = (2 : ℂ) • numberOpK P 0 - 1 := by
  unfold gridZMode
  rw [reflIdx_zero, gridK_zero']
  rw [show Complex.exp (Complex.I * (((1 : ℤ) : ℝ) * (0 : ℝ))) = 1 by norm_num,
    show Complex.exp (Complex.I * (((-1 : ℤ) : ℝ) * (0 : ℝ))) = 1 by norm_num]
  rw [cCreateK_mul_self, cAnnihK_mul_self, cAnnihK_cCreateK_eq]
  simp only [one_smul, smul_zero, mul_one]
  rw [two_smul]
  unfold numberOpK
  abel

/-- The self-conjugate `k=π` mode contributes `1 − 2 n_π`. -/
theorem gridZMode_mid (P : ℕ) :
    gridZMode P ⟨P + 1, by omega⟩ = 1 - (2 : ℂ) • numberOpK P Real.pi := by
  unfold gridZMode
  rw [reflIdx_mid, gridK_mid']
  rw [cCreateK_mul_self, cAnnihK_mul_self, cAnnihK_cCreateK_eq]
  rw [show Complex.exp (Complex.I * ((((-1 : ℤ) : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ))) = -1 by
    rw [show Complex.I * ((((-1 : ℤ) : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ))
        = -((Real.pi : ℂ) * Complex.I) by push_cast; ring]
    rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num]
  rw [show Complex.exp (Complex.I * ((((1 : ℤ) : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ))) = -1 by
    rw [show Complex.I * ((((1 : ℤ) : ℝ) : ℂ) * ((Real.pi : ℝ) : ℂ))
        = (Real.pi : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.exp_pi_mul_I]]
  simp only [smul_zero, mul_neg, mul_one, neg_smul, one_smul]
  rw [two_smul]
  unfold numberOpK
  abel

/-- The self-conjugate modes sum to `2 n_0 − 2 n_π`, which vanishes on the active subspace. -/
theorem gridZMode_selfconj (P : ℕ) :
    gridZMode P ⟨0, by omega⟩ + gridZMode P ⟨P + 1, by omega⟩ =
      (2 : ℂ) • numberOpK P 0 - (2 : ℂ) • numberOpK P Real.pi := by
  rw [gridZMode_zero, gridZMode_mid]
  abel

/-- **BLOCK B (operator level).** The full Fourier collection: the position-space
periodic bilinear sum equals the self-conjugate-mode contribution `2 n_0 − 2 n_π`
plus the sum of per-mode pseudospin cost Hamiltonians over the active pairs. -/
theorem sum_body_add_wrap_eq_gridZMode_collected (P : ℕ) :
    (∑ k : Fin (2*P+1), bodyBilinear P k) + wrapBilinear P =
      ((2 : ℂ) • numberOpK P 0 - (2 : ℂ) • numberOpK P Real.pi) +
        ∑ n : Fin P, HredZMode P (waveVectorABC P n) := by
  rw [sum_body_add_wrap_eq_periodic, sum_periodic_eq_gridZMode, sum_grid_reindex]
  rw [gridZMode_selfconj]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  exact gridZMode_pair_eq_HredZMode P n

/-- (B2-z) Active-subspace cost decomposition: for `ψ` with `InActiveSubspace P ψ`,
the constant-shifted reduced cost `Hred_z_pm false P + (2P+2)·1` acts on `ψ` as the
sum of per-mode pseudospin cost Hamiltonians `Σ_n HredZMode P (k_n)`. The pinned
constant is `+(2P+2)·1` (source l.846/l.853). Chains B1's `Hred_z_image_even`
(premise discharged by `inActiveSubspace_imp_even`) into the Fourier collection;
the self-conjugate `n_0`/`n_π` residual is killed on `ψ`. -/
theorem HredZDecomp_active (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) :
    (UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • 1) * ψ =
      (∑ n : Fin P, HredZMode P (waveVectorABC P n)) * ψ := by
  rw [Hred_z_image_even P ψ (inActiveSubspace_imp_even P ψ hψ)]
  rw [sum_body_add_wrap_eq_gridZMode_collected]
  -- the self-conjugate residual `2 n_0 − 2 n_π` vanishes on ψ
  rw [add_op_mul_ket, sub_op_mul_ket, smul_op_mul_ket, smul_op_mul_ket]
  rw [inActiveSubspace_n0_annih P ψ hψ, inActiveSubspace_npi_annih P ψ hψ]
  simp

/-- Expectation-value corollary of (B2-z). -/
theorem HredZDecomp_active_expectation (P : ℕ) (φ : Bra (NQubitDim (2 * P + 2)))
    (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    φ * ((UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • 1) * ψ) =
      φ * ((∑ n : Fin P, HredZMode P (waveVectorABC P n)) * ψ) := by
  rw [HredZDecomp_active P ψ hψ]

end

end QAOA.IsingChain.JordanWigner
