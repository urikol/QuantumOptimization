import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.Basic
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.ActiveSubspace

/-!
# Momentum Modes (Fourier Collection) — full-grid number collection and the mixer decomposition

The full-momentum-grid Fourier collection (arXiv:1911.12259v2 SM l.770–856).
Introduces the full grid `gridK P` of `2P+2` momenta, the dual orthogonality relation, and
the collapse of the grid number sum onto the position number sum. Then assembles the mixer
decomposition: the constant-shifted reduced mixer Hamiltonian equals the sum of
per-mode pseudospin mixer Hamiltonians on the active subspace.

## Main definitions
- `gridK`: the full momentum grid `gridK P ℓ = 2πℓ/(2P+2)`, `ℓ : Fin (2P+2)`.

## Main statements
- `sum_exp_dual_orthogonality`: the grid Fourier orthogonality `Σ_ℓ e^{i d·gridK ℓ}`.
- `sum_numberOpK_grid_eq_sum_numberOp`: `Σ_ℓ n_{gridK ℓ} = Σ_j n_j` (number collection).
- `HredXDecomp_active`: (B2-x) `Hred_x_op P + 2·1 = Σ_k HredXMode` on the active subspace.
- `HredXDecomp_active_expectation`: the matching expectation-value form.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 11: The full-momentum-grid Fourier collection
--
-- The shared structural block: a grid `gridK ℓ = 2π ℓ / N_R` over `Fin N_R`,
-- the DUAL orthogonality (sum over the grid INDEX, not position sites), the
-- bilinear/number double-sum substitution, and the reindexing of the grid sum
-- onto `n_0 + n_π + Σ_n (n_{k_n} + n_{−k_n})`. Unlocks both remaining
-- decomposition deliverables.
-- ============================================================================

/-- The full momentum grid `gridK ℓ = 2π ℓ / N_R` for `ℓ : Fin (2P+2)`. The grid
values are `{0, π} ∪ {±k_n}` (mod 2π): `gridK 0 = 0`, `gridK (P+1) = π`, and the
remaining indices pair up into `±k_n`. -/
def gridK (P : ℕ) (ℓ : Fin (2 * P + 2)) : ℝ :=
  2 * Real.pi * (ℓ.val : ℝ) / (2 * P + 2)

/-- DUAL orthogonality on the grid index: for a fixed integer difference `d`,
`Σ_ℓ e^{i·gridK(ℓ)·d} = N_R` if `N_R ∣ d`, else `0`. This is the dual to
`sum_exp_orthogonality_*` (which sums over position sites); here the sum runs over
the momentum grid index `ℓ`, with `d = j − j'` a position difference. -/
theorem sum_exp_dual_orthogonality (P : ℕ) (d : ℤ) :
    (∑ ℓ : Fin (2*P+2), Complex.exp (Complex.I * (gridK P ℓ * (d : ℝ)))) =
      if ((2*P+2 : ℤ) ∣ d) then ((2*P+2 : ℕ) : ℂ) else 0 := by
  have hNne : ((2 * P + 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * P + 2 : ℝ) ≠ 0)
  -- The summand is ω^ℓ with ω = exp(i 2π d / N_R)
  set ω := Complex.exp (Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))) with hω
  have hterm : ∀ ℓ : Fin (2*P+2),
      Complex.exp (Complex.I * (gridK P ℓ * (d : ℝ))) = ω ^ (ℓ.val) := by
    intro ℓ
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    unfold gridK
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun ℓ _ => hterm ℓ)]
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => ω ^ ℓ)]
  -- ω^N_R = exp(i 2π d) = 1 always
  have hroot : ω ^ (2*P+2) = 1 := by
    rw [hω, ← Complex.exp_nat_mul]
    rw [show ((2*P+2 : ℕ) : ℂ) * (Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2)))
        = (d : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast
      field_simp]
    rw [Complex.exp_int_mul_two_pi_mul_I]
  by_cases hdvd : (2*P+2 : ℤ) ∣ d
  · rw [if_pos hdvd]
    -- ω = 1 in this case, so each term is 1, sum = N_R
    have hω1 : ω = 1 := by
      rw [hω]
      obtain ⟨c, hc⟩ := hdvd
      rw [show Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))
          = (c : ℂ) * (2 * Real.pi * Complex.I) by
        rw [hc]
        push_cast
        field_simp]
      rw [Complex.exp_int_mul_two_pi_mul_I]
    rw [hω1]
    simp
  · rw [if_neg hdvd]
    -- ω ≠ 1: geometric sum, numerator ω^N_R − 1 = 0
    have hωne : ω ≠ 1 := by
      intro hcontra
      apply hdvd
      rw [hω] at hcontra
      rw [Complex.exp_eq_one_iff] at hcontra
      obtain ⟨c, hc⟩ := hcontra
      -- I * 2π d / N = c * 2π I  ⟹  d = c N  ⟹  N ∣ d
      refine ⟨c, ?_⟩
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      -- cancel I and 2π from hc to get  d / N = c
      have hc' : (d : ℂ) / ((2 * P + 2 : ℝ) : ℂ) = (c : ℂ) := by
        have h2 : Complex.I * (2 * Real.pi * (d : ℝ) / (2 * P + 2))
            = Complex.I * ((2 * Real.pi) * ((c : ℂ) )) := by
          rw [hc]; ring
        have h3 : (2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℂ)
            = (2 * Real.pi) * (c : ℂ) := mul_left_cancel₀ hI h2
        have h2pi : (2 : ℂ) * Real.pi ≠ 0 := by simp [hpi]
        have h4 : (2 * Real.pi) * ((d : ℂ) / ((2 * P + 2 : ℝ) : ℂ))
            = (2 * Real.pi) * (c : ℂ) := by
          rw [← h3]; push_cast; ring
        exact mul_left_cancel₀ h2pi h4
      have h6 : (d : ℂ) = ((c * (2 * P + 2 : ℤ) : ℤ) : ℂ) := by
        field_simp at hc'
        push_cast at hc' ⊢
        linear_combination hc'
      have h7 : d = c * (2 * P + 2 : ℤ) := by exact_mod_cast h6
      linarith [h7]
    rw [geom_sum_eq hωne (2*P+2), hroot]
    simp

/-- The momentum number operator as a position double sum:
`n_k = (1/N_R) Σ_{j'} Σ_j e^{ik(j−j')} • (c_{j'}† c_j)`. -/
theorem numberOpK_double_sum (P : ℕ) (k : ℝ) :
    numberOpK P k =
      ((1 : ℂ) / ((2 * P + 2 : ℕ) : ℂ)) •
        ∑ j' : Fin (2 * P + 2), ∑ j : Fin (2 * P + 2),
          Complex.exp (Complex.I * (k * ((j.val : ℝ) - (j'.val : ℝ)))) •
            (cCreate j' * cAnnih j) := by
  unfold numberOpK cAnnihK
  rw [cCreateK_eq]
  -- expand prefactors and the product of the two sums
  rw [smul_mul_smul_comm, Finset.sum_mul_sum,
    mul_comm (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2 * P + 2) : ℂ)),
    fourier_prefactor_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j' _
  apply Finset.sum_congr rfl
  intro j _
  rw [smul_mul_smul_comm]
  rw [show Complex.exp (-(Complex.I * (k * (j'.val : ℝ)))) *
        Complex.exp (Complex.I * (k * (j.val : ℝ)))
      = Complex.exp (Complex.I * (k * ((j.val : ℝ) - (j'.val : ℝ)))) by
    rw [← Complex.exp_add]
    congr 1
    ring]

/-- For `j, j' : Fin (2P+2)`, `(2P+2) ∣ (j − j')` (as integers) iff `j = j'`
(the difference has absolute value `< N_R`, so the only multiple is `0`). -/
theorem dvd_sub_iff_eq (P : ℕ) (j j' : Fin (2 * P + 2)) :
    ((2 * P + 2 : ℤ) ∣ ((j.val : ℤ) - (j'.val : ℤ))) ↔ j = j' := by
  constructor
  · intro hdvd
    have hj : (j.val : ℤ) < 2 * P + 2 := by exact_mod_cast j.isLt
    have hj' : (j'.val : ℤ) < 2 * P + 2 := by exact_mod_cast j'.isLt
    have hjnn : (0 : ℤ) ≤ (j.val : ℤ) := by positivity
    have hj'nn : (0 : ℤ) ≤ (j'.val : ℤ) := by positivity
    rcases hdvd with ⟨c, hc⟩
    have hzero : (j.val : ℤ) - (j'.val : ℤ) = 0 := by
      rcases lt_trichotomy c 0 with hcneg | hc0 | hcpos
      · nlinarith [hc, hcneg]
      · subst hc0; simpa using hc
      · nlinarith [hc, hcpos]
    have : j.val = j'.val := by omega
    exact Fin.ext this
  · intro h
    subst h
    simp

/-- TOTAL-NUMBER FOURIER INVARIANCE: the number operator summed over the full
momentum grid equals the number operator summed over position sites,
`Σ_ℓ n_{gridK ℓ} = Σ_j n_j`. The dual orthogonality collapses the position
double sum to its diagonal. -/
theorem sum_numberOpK_grid_eq_sum_numberOp (P : ℕ) :
    (∑ ℓ : Fin (2 * P + 2), numberOpK P (gridK P ℓ)) =
      ∑ j : Fin (2 * P + 2), numberOp j := by
  -- substitute the double-sum form for each grid mode
  simp only [numberOpK_double_sum]
  rw [← Finset.smul_sum]
  -- Now: 1/N • Σ_ℓ Σ_{j'} Σ_j  e^{i gridK(ℓ) (j - j')} • (c_{j'}† c_j)
  -- reorder to put Σ_ℓ innermost on the exponential, collecting it
  have hswap : (∑ ℓ : Fin (2 * P + 2), ∑ j' : Fin (2 * P + 2), ∑ j : Fin (2 * P + 2),
        Complex.exp (Complex.I * (gridK P ℓ * ((j.val : ℝ) - (j'.val : ℝ)))) •
          (cCreate j' * cAnnih j))
      = ∑ j' : Fin (2 * P + 2), ∑ j : Fin (2 * P + 2),
          (∑ ℓ : Fin (2 * P + 2),
            Complex.exp (Complex.I * (gridK P ℓ * ((j.val : ℝ) - (j'.val : ℝ))))) •
            (cCreate j' * cAnnih j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_smul]
  rw [hswap]
  -- apply the dual orthogonality with d = j - j'
  have hcollapse : ∀ j' j : Fin (2 * P + 2),
      (∑ ℓ : Fin (2 * P + 2),
        Complex.exp (Complex.I * (gridK P ℓ * ((j.val : ℝ) - (j'.val : ℝ))))) =
        if j = j' then ((2 * P + 2 : ℕ) : ℂ) else 0 := by
    intro j' j
    have hsum := sum_exp_dual_orthogonality P ((j.val : ℤ) - (j'.val : ℤ))
    simp only [dvd_sub_iff_eq] at hsum
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro ℓ _
    congr 2
    push_cast
    ring
  simp only [hcollapse]
  -- collapse the j-sum to the diagonal, then multiply by 1/N
  rw [show (∑ j' : Fin (2 * P + 2), ∑ j : Fin (2 * P + 2),
        (if j = j' then ((2 * P + 2 : ℕ) : ℂ) else 0) • (cCreate j' * cAnnih j))
      = ∑ j' : Fin (2 * P + 2),
          ((2 * P + 2 : ℕ) : ℂ) • (cCreate j' * cAnnih j') by
    apply Finset.sum_congr rfl
    intro j' _
    rw [Finset.sum_eq_single j']
    · rw [if_pos rfl]
    · intro j _ hj; rw [if_neg hj, zero_smul]
    · intro h; exact absurd (Finset.mem_univ j') h]
  rw [← Finset.smul_sum, smul_smul]
  rw [one_div, inv_mul_cancel₀ (by exact_mod_cast (by omega : (2 * P + 2 : ℕ) ≠ 0)), one_smul]
  rfl

/-- `c_k` is `2π`-periodic in `k`: `c_{k+2π} = c_k` (since `e^{i·2π·j} = 1` for
integer site index `j`). -/
theorem cAnnihK_periodic_2pi (P : ℕ) (k : ℝ) :
    cAnnihK P (k + 2 * Real.pi) = cAnnihK P k := by
  unfold cAnnihK
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [show ((k + 2 * Real.pi : ℝ) : ℂ) * (j.val : ℝ)
      = (k : ℝ) * (j.val : ℝ) + (j.val : ℤ) * (2 * Real.pi) by push_cast; ring]
  rw [mul_add, Complex.exp_add]
  rw [show Complex.I * ((j.val : ℤ) * (2 * Real.pi) : ℂ)
      = (j.val : ℤ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  rw [Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- `n_k` is `2π`-periodic in `k`: `n_{k+2π} = n_k`. -/
theorem numberOpK_periodic_2pi (P : ℕ) (k : ℝ) :
    numberOpK P (k + 2 * Real.pi) = numberOpK P k := by
  unfold numberOpK cCreateK
  rw [cAnnihK_periodic_2pi]

/-- `n_{2π − k} = n_{−k}` (via `2π`-periodicity). -/
theorem numberOpK_two_pi_sub (P : ℕ) (k : ℝ) :
    numberOpK P (2 * Real.pi - k) = numberOpK P (-k) := by
  rw [show (2 * Real.pi - k : ℝ) = (-k) + 2 * Real.pi by ring]
  rw [numberOpK_periodic_2pi]

/-- Grid value at index `0` is `k = 0`. -/
theorem gridK_zero (P : ℕ) : gridK P ⟨0, by omega⟩ = 0 := by
  unfold gridK; simp

/-- Grid value at index `P+1` is `k = π`. -/
theorem gridK_mid (P : ℕ) : gridK P ⟨P + 1, by omega⟩ = Real.pi := by
  unfold gridK
  rw [show ((P + 1 : ℕ) : ℝ) = (P : ℝ) + 1 by push_cast; ring]
  have hne : (2 * P + 2 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Grid value at index `m+1` (`m : Fin P`) is the `m`-th active wave vector. -/
theorem gridK_pos (P : ℕ) (m : Fin P) :
    gridK P ⟨m.val + 1, by omega⟩ = waveVectorABC P m := by
  unfold gridK waveVectorABC
  push_cast
  ring

/-- Grid value at index `2P+1−m` (`m : Fin P`) is `2π − k_m`, so its number operator
is `n_{−k_m}`. -/
theorem numberOpK_gridK_neg (P : ℕ) (m : Fin P) :
    numberOpK P (gridK P ⟨2 * P + 1 - m.val, by omega⟩) = numberOpK P (-waveVectorABC P m) := by
  have hm : m.val < P := m.isLt
  rw [show gridK P ⟨2 * P + 1 - m.val, by omega⟩ = 2 * Real.pi - waveVectorABC P m by
    unfold gridK waveVectorABC
    rw [show ((2 * P + 1 - m.val : ℕ) : ℝ) = (2 * P + 1 : ℝ) - (m.val : ℝ) by
      have : m.val ≤ 2 * P + 1 := by omega
      push_cast [Nat.cast_sub this]
      ring]
    have hne : (2 * P + 2 : ℝ) ≠ 0 := by positivity
    field_simp
    ring]
  rw [numberOpK_two_pi_sub]

/-- GRID REINDEXING: the grid number sum splits into the self-conjugate modes
`n_0`, `n_π` and the active pairs `Σ_n (n_{k_n} + n_{−k_n})`. The grid index
`Fin (2P+2)` partitions as `{0} ⊔ {1..P} ⊔ {P+1} ⊔ {P+2..2P+1}` mapping to
`0 ⊔ {k_n} ⊔ π ⊔ {−k_n}`. -/
theorem sum_numberOpK_grid_reindex (P : ℕ) :
    (∑ ℓ : Fin (2 * P + 2), numberOpK P (gridK P ℓ)) =
      numberOpK P 0 + numberOpK P Real.pi +
        ∑ n : Fin P, (numberOpK P (waveVectorABC P n) + numberOpK P (-waveVectorABC P n)) := by
  -- recast Fin (2P+2) as Fin ((P+1)+(P+1)) and split
  have hcast : 2 * P + 2 = (P + 1) + (P + 1) := by ring
  rw [← Equiv.sum_comp (finCongr hcast).symm
    (fun ℓ : Fin (2 * P + 2) => numberOpK P (gridK P ℓ))]
  rw [Fin.sum_univ_add]
  -- helper: the symm-cast preserves `.val`, so gridK only sees the value
  have hval : ∀ z : Fin ((P + 1) + (P + 1)),
      (finCongr hcast).symm z = (⟨z.val, by rw [hcast]; exact z.isLt⟩ : Fin (2 * P + 2)) := by
    intro z
    apply Fin.ext
    rw [finCongr_symm]
    rw [finCongr_apply_coe]
  simp only [hval]
  -- first block: Fin (P+1) → castAdd; second block: Fin (P+1) → natAdd
  -- peel off ℓ=0 from the first block and ℓ=P+1 from the second
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  -- now identify the 4 pieces
  -- piece 1: castAdd 0 → val 0 → gridK = 0 → n_0
  have hp1 : numberOpK P (gridK P (⟨(Fin.castAdd (P + 1) (0 : Fin (P + 1))).val,
        by rw [hcast]; exact (Fin.castAdd (P + 1) (0 : Fin (P + 1))).isLt⟩ : Fin (2 * P + 2)))
      = numberOpK P 0 := by
    congr 1
    rw [show (⟨(Fin.castAdd (P + 1) (0 : Fin (P + 1))).val, _⟩ : Fin (2 * P + 2))
        = (⟨0, by omega⟩ : Fin (2 * P + 2)) from Fin.ext (by simp)]
    exact gridK_zero P
  -- piece 3: natAdd 0 → val (P+1) → gridK = π → n_π
  have hp3 : numberOpK P (gridK P (⟨(Fin.natAdd (P + 1) (0 : Fin (P + 1))).val,
        by rw [hcast]; exact (Fin.natAdd (P + 1) (0 : Fin (P + 1))).isLt⟩ : Fin (2 * P + 2)))
      = numberOpK P Real.pi := by
    congr 1
    rw [show (⟨(Fin.natAdd (P + 1) (0 : Fin (P + 1))).val, _⟩ : Fin (2 * P + 2))
        = (⟨P + 1, by omega⟩ : Fin (2 * P + 2)) from Fin.ext (by simp)]
    exact gridK_mid P
  -- piece 2: castAdd i.succ → val (i+1) → gridK = k_i → n_{k_i}
  have hp2 : (∑ i : Fin P, numberOpK P (gridK P
        (⟨(Fin.castAdd (P + 1) i.succ).val,
          by rw [hcast]; exact (Fin.castAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2))))
      = ∑ n : Fin P, numberOpK P (waveVectorABC P n) := by
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [show (⟨(Fin.castAdd (P + 1) i.succ).val, _⟩ : Fin (2 * P + 2))
        = (⟨i.val + 1, by omega⟩ : Fin (2 * P + 2)) from Fin.ext (by simp [Fin.val_succ])]
    exact gridK_pos P i
  -- piece 4: natAdd i.succ → val (P+2+i) → gridK → n_{-k_{P-1-i}}; reverse reindex
  have hp4 : (∑ i : Fin P, numberOpK P (gridK P
        (⟨(Fin.natAdd (P + 1) i.succ).val,
          by rw [hcast]; exact (Fin.natAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2))))
      = ∑ n : Fin P, numberOpK P (-waveVectorABC P n) := by
    rw [← Equiv.sum_comp Fin.revPerm
      (fun i : Fin P => numberOpK P (gridK P
        (⟨(Fin.natAdd (P + 1) i.succ).val,
          by rw [hcast]; exact (Fin.natAdd (P + 1) i.succ).isLt⟩ : Fin (2 * P + 2))))]
    apply Finset.sum_congr rfl
    intro n _
    rw [Fin.revPerm_apply]
    -- the reversed natAdd index has val 2P+1-n, so this is n_{-k_n}
    rw [show (⟨(Fin.natAdd (P + 1) (Fin.rev n).succ).val, _⟩ : Fin (2 * P + 2))
        = (⟨2 * P + 1 - n.val, by omega⟩ : Fin (2 * P + 2)) from
      Fin.ext (by
        simp only [Fin.val_natAdd, Fin.val_succ, Fin.val_rev]
        omega)]
    exact numberOpK_gridK_neg P n
  rw [hp1, hp3, hp2, hp4]
  rw [Finset.sum_add_distrib]
  abel

-- ============================================================================
-- Section 12: The mixer decomposition (B2-x)
-- ============================================================================

/-- Per-site mixer image as a number operator: `c_j† c_j − c_j c_j† = 2 n_j − 1`
(from the position CAR `{c_j, c_j†} = 1`). -/
theorem mixer_site_eq (P : ℕ) (j : Fin (2 * P + 2)) :
    cCreate j * cAnnih j - cAnnih j * cCreate j = (2 : ℂ) • numberOp j - 1 := by
  have hcar := car_annih_create j j
  rw [if_pos rfl] at hcar
  have hnum : numberOp j = cCreate j * cAnnih j := rfl
  have hhole : cAnnih j * cCreate j = 1 - numberOp j := by
    rw [hnum, eq_sub_iff_add_eq]; exact hcar
  rw [hhole, hnum, two_smul]; abel

/-- Per-mode mixer Hamiltonian expanded: `Hred_x^(k_n) = −2·1 + 2 n_{k_n} + 2 n_{−k_n}`. -/
theorem HredXMode_eq (P : ℕ) (n : Fin P) :
    HredXMode P (waveVectorABC P n) =
      (-2 : ℂ) • 1 + (2 : ℂ) • numberOpK P (waveVectorABC P n)
        + (2 : ℂ) • numberOpK P (-waveVectorABC P n) := by
  unfold HredXMode tauZ
  rw [smul_sub, smul_sub]
  module

/-- Operator-level mixer decomposition (no active subspace yet): the shifted mixer
equals the sum of per-mode mixers plus the self-conjugate-mode contribution
`2(n_0 + n_π)`. -/
theorem Hred_x_op_shift_eq (P : ℕ) :
    UpperBound.Hred_x_op P + (2 : ℂ) • 1 =
      (∑ n : Fin P, HredXMode P (waveVectorABC P n))
        + (2 : ℂ) • numberOpK P 0 + (2 : ℂ) • numberOpK P Real.pi := by
  rw [Hred_x_image]
  -- Σ_j (c_j† c_j − c_j c_j†) = Σ_j (2 n_j − 1) = 2 Σ_j n_j − N_R • 1
  rw [Finset.sum_congr rfl (fun j _ => mixer_site_eq P j)]
  rw [Finset.sum_sub_distrib, ← Finset.smul_sum]
  -- Σ_j n_j = n_0 + n_π + Σ_n (n_{k_n} + n_{−k_n})  (invariance + reindex)
  rw [← sum_numberOpK_grid_eq_sum_numberOp, sum_numberOpK_grid_reindex]
  -- Σ_n HredXMode expanded
  rw [Finset.sum_congr rfl (fun n _ => HredXMode_eq P n)]
  -- now pure module arithmetic over the operator algebra
  simp only [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  module

/-- (B2-x) Active-subspace mixer decomposition: for `ψ` with `InActiveSubspace P ψ`,
the constant-shifted reduced mixer `Hred_x_op P + 2·1` acts on `ψ` as the sum of
per-mode pseudospin mixers `Σ_n HredXMode P (k_n)`. The pinned constant is `+2·1`
(source l.812, 845, 852). -/
theorem HredXDecomp_active (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) :
    (UpperBound.Hred_x_op P + (2 : ℂ) • 1) * ψ =
      (∑ n : Fin P, HredXMode P (waveVectorABC P n)) * ψ := by
  rw [Hred_x_op_shift_eq]
  -- the n_0, n_π terms annihilate ψ
  rw [add_op_mul_ket, add_op_mul_ket, smul_op_mul_ket, smul_op_mul_ket]
  rw [inActiveSubspace_n0_annih P ψ hψ, inActiveSubspace_npi_annih P ψ hψ]
  simp

/-- Expectation-value corollary of (B2-x). -/
theorem HredXDecomp_active_expectation (P : ℕ) (φ : Bra (NQubitDim (2 * P + 2)))
    (ψ : NQubitKet (2 * P + 2)) (hψ : InActiveSubspace P ψ) :
    φ * ((UpperBound.Hred_x_op P + (2 : ℂ) • 1) * ψ) =
      φ * ((∑ n : Fin P, HredXMode P (waveVectorABC P n)) * ψ) := by
  rw [HredXDecomp_active P ψ hψ]


end

end QAOA.IsingChain.JordanWigner
