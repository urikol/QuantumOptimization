import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.SpectralReflection
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.Basic
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.ActiveSubspace
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.FourierCollection

/-!
# Momentum Modes (Parity Identity) — the parity/Bogoliubov identity and even-parity on the active subspace

The parity (Block A) identity (arXiv:1911.12259v2 SM). Applies the generic
spectral-reflection machinery of `MomentumModes.SpectralReflection` to the two physical
idempotent number families (position `n_j` and momentum-grid `n_{gridK ℓ}`): both reflection
products equal `parityFn` of their common total number operator, yielding the parity
Bogoliubov identity `parityOp = ∏_ℓ (1 − 2 n_{gridK ℓ})`. The momentum-grid product then
absorbs the active projector, giving even fermion parity on the active subspace.

## Main statements
- `numberOp_idem`, `numberOp_commute`, `parityOp_eq_noncommProd`: position-number idempotent
  algebra and `parityOp` as a reflection product.
- `numberOpK_gridK_pairwise_commute`, `parity_eq_grid_prod`: the parity Bogoliubov identity.
- `noncommProd_pairParity_mul_activeProj`, `momentumParityProd_mul_activeProj`: the grid
  reflection product absorbs `Π_A`.
- `inActiveSubspace_imp_even`: `parityOp · ψ = ψ` (even fermion parity) on the active subspace.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ----------------------------------------------------------------------------
-- Section 12 (cont.): applying the spectral machinery to the two physical families
-- ----------------------------------------------------------------------------

/-- The position number operator is idempotent (`n_j² = n_j`), from
`1 − 2 n_j = X_j` being an involution. -/
theorem numberOp_idem (j : Fin (2 * P + 2)) :
    numberOp j * numberOp j = numberOp j := by
  rw [numberOp_eq, smul_mul_smul_comm, mul_sub, sub_mul, sub_mul, localPauliX_sq]
  simp only [mul_one, one_mul]
  module

/-- Position number operators pairwise commute (computational-basis diagonal). -/
theorem numberOp_commute (j j' : Fin (2 * P + 2)) :
    Commute (numberOp j) (numberOp j') := by
  rw [numberOp_eq, numberOp_eq]
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.sub_left (Commute.one_left _)
  apply Commute.sub_right (Commute.one_right _)
  exact Qubits.localPauliX_commute j j'

/-- `parityOp = Π_j (1 − 2 n_j)`: the position-space parity is the reflection product
of the position number operators (via `sigmaX_reconstruction`). -/
theorem parityOp_eq_noncommProd (P : ℕ) :
    parityOp (2 * P + 2)
      = (Finset.univ : Finset (Fin (2 * P + 2))).noncommProd
          (fun j => 1 - (2 : ℂ) • numberOp j)
          (one_sub_two_smul_pairwise_commute _ _
            (fun i _ j _ _ => numberOp_commute i j)) := by
  unfold parityOp
  apply Finset.noncommProd_congr rfl
  intro j _
  exact (sigmaX_reconstruction j).symm

/-- The grid momentum number operators pairwise commute on `Finset.univ`. -/
theorem numberOpK_gridK_pairwise_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin (2 * P + 2))) : Set (Fin (2 * P + 2))).Pairwise
      (Function.onFun Commute (fun ℓ => numberOpK P (gridK P ℓ))) := by
  intro ℓ _ ℓ' _ hne
  -- exp(I·(gridK ℓ − gridK ℓ')) facts via N ∤ (ℓ − ℓ')
  have hdvd : ¬ ((2 * P + 2 : ℤ) ∣ ((ℓ.val : ℤ) - (ℓ'.val : ℤ))) := by
    rw [dvd_sub_iff_eq]; exact hne
  have hdvd' : ¬ ((2 * P + 2 : ℤ) ∣ ((ℓ'.val : ℤ) - (ℓ.val : ℤ))) := by
    rw [dvd_sub_iff_eq]; exact fun h => hne h.symm
  -- gridK ℓ − gridK ℓ' = 2π·d/N, real, with d the integer difference
  have hgdiff : (gridK P ℓ - gridK P ℓ' : ℝ)
      = 2 * Real.pi * (((ℓ.val : ℤ) - (ℓ'.val : ℤ) : ℤ) : ℝ) / (2 * P + 2) := by
    unfold gridK; push_cast; ring
  have hgdiff' : (gridK P ℓ' - gridK P ℓ : ℝ)
      = 2 * Real.pi * (((ℓ'.val : ℤ) - (ℓ.val : ℤ) : ℤ) : ℝ) / (2 * P + 2) := by
    unfold gridK; push_cast; ring
  have hNne : ((2 * P + 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * P + 2 : ℝ) ≠ 0)
  -- helper: for an integer d not divisible by N, exp(I·2π d/N) ≠ 1 and ^N = 1
  have key : ∀ d : ℤ, ¬ ((2 * P + 2 : ℤ) ∣ d) →
      Complex.exp (Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℝ))) ≠ 1
      ∧ (Complex.exp (Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℝ)))) ^ (2 * P + 2)
          = 1 := by
    intro d hd
    constructor
    · intro hcontra
      apply hd
      rw [Complex.exp_eq_one_iff] at hcontra
      obtain ⟨c, hc⟩ := hcontra
      refine ⟨c, ?_⟩
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hc' : (d : ℂ) / ((2 * P + 2 : ℝ) : ℂ) = (c : ℂ) := by
        have h2 : Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℝ))
            = Complex.I * ((2 * Real.pi) * ((c : ℂ))) := by rw [hc]; ring
        have h3 : ((2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℝ) : ℂ)
            = (2 * Real.pi) * (c : ℂ) := mul_left_cancel₀ hI h2
        have h2pi : (2 : ℂ) * Real.pi ≠ 0 := by simp [hpi]
        have h4 : (2 * Real.pi) * ((d : ℂ) / ((2 * P + 2 : ℝ) : ℂ))
            = (2 * Real.pi) * (c : ℂ) := by rw [← h3]; push_cast; ring
        exact mul_left_cancel₀ h2pi h4
      have h6 : (d : ℂ) = (((2 * P + 2 : ℤ) * c : ℤ) : ℂ) := by
        field_simp at hc'; push_cast at hc' ⊢; linear_combination hc'
      exact_mod_cast h6
    · rw [← Complex.exp_nat_mul]
      rw [show ((2 * P + 2 : ℕ) : ℂ) * (Complex.I * ((2 * Real.pi * (d : ℝ) / (2 * P + 2) : ℝ)))
          = (d : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
      rw [Complex.exp_int_mul_two_pi_mul_I]
  obtain ⟨hne1, hroot1⟩ := key _ hdvd
  obtain ⟨hne2, hroot2⟩ := key _ hdvd'
  refine numberOpK_commute_of_diff P (gridK P ℓ) (gridK P ℓ') ?_ ?_ ?_ ?_
  · rw [hgdiff]; exact hne1
  · rw [hgdiff]; exact hroot1
  · rw [hgdiff']; exact hne2
  · rw [hgdiff']; exact hroot2

/-- The parity Bogoliubov identity: the position-space parity operator equals the
product over the full momentum grid of per-mode reflections,
`parityOp (2P+2) = Π_ℓ (1 − 2 n_{gridK ℓ})` (`noncommProd` over `univ`; the grid
factors pairwise commute, so the order is irrelevant). Both sides equal `parityFn`
of their (equal) total number sums. -/
theorem parity_eq_grid_prod (P : ℕ) :
    parityOp (2 * P + 2)
      = (Finset.univ : Finset (Fin (2 * P + 2))).noncommProd
          (fun ℓ => 1 - (2 : ℂ) • numberOpK P (gridK P ℓ))
          (one_sub_two_smul_pairwise_commute _ _ (numberOpK_gridK_pairwise_commute P)) := by
  rw [parityOp_eq_noncommProd]
  -- both products equal parityFn of their (equal) sums
  rw [noncommProd_one_sub_two_smul_eq_parityFn Finset.univ (fun j => numberOp j)
      (fun i _ => numberOp_idem i) (fun i _ j _ _ => numberOp_commute i j)]
  rw [noncommProd_one_sub_two_smul_eq_parityFn Finset.univ (fun ℓ => numberOpK P (gridK P ℓ))
      (fun i _ => numberOpK_idem P (gridK P i)) (numberOpK_gridK_pairwise_commute P)]
  -- equal sums ⟹ equal parityFn
  rw [sum_numberOpK_grid_eq_sum_numberOp]

-- ----------------------------------------------------------------------------
-- Section 12 (cont.): the parity product absorbs the active projector
-- ----------------------------------------------------------------------------

/-- The pair-parity factors over `Fin P` pairwise commute (distinct active pairs). -/
theorem pairParity_pairwise_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => pairParity P (waveVectorABC P n))) :=
  fun n _ m _ hnm => pairParity_commute_pairParity_cross P n m hnm

/-- The pair-parity product over any `s : Finset (Fin P)` absorbs the active projector. -/
theorem noncommProd_pairParity_mul_activeProj_of (P : ℕ) (s : Finset (Fin P))
    (comm : (s : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => pairParity P (waveVectorABC P n)))) :
    s.noncommProd (fun n => pairParity P (waveVectorABC P n)) comm * activeProj P = activeProj P := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.noncommProd_empty, one_mul]
  | @insert a s ha ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha, mul_assoc,
      ih (comm.mono (by simp)), pairParity_mul_activeProj]

/-- The full pair-parity product absorbs the active projector:
`(∏_n P_{k_n}) · activeProj = activeProj`. -/
theorem noncommProd_pairParity_mul_activeProj (P : ℕ) :
    (Finset.univ : Finset (Fin P)).noncommProd
        (fun n => pairParity P (waveVectorABC P n)) (pairParity_pairwise_commute P)
      * activeProj P = activeProj P :=
  noncommProd_pairParity_mul_activeProj_of P Finset.univ (pairParity_pairwise_commute P)

/-- The `+k_n` grid-index embedding `n ↦ ⟨n+1⟩ : Fin (2P+2)`. -/
def posEmb (P : ℕ) : Fin P ↪ Fin (2 * P + 2) where
  toFun n := ⟨n.val + 1, by omega⟩
  inj' := by intro a b h; simpa [Fin.ext_iff] using h

/-- The `−k_n` grid-index embedding `n ↦ ⟨2P+1−n⟩ : Fin (2P+2)`. -/
def negEmb (P : ℕ) : Fin P ↪ Fin (2 * P + 2) where
  toFun n := ⟨2 * P + 1 - n.val, by omega⟩
  inj' := by
    intro a b h
    have ha := a.isLt; have hb := b.isLt
    simp only [Fin.ext_iff] at h ⊢
    omega

theorem posEmb_grid (P : ℕ) (n : Fin P) :
    numberOpK P (gridK P (posEmb P n)) = numberOpK P (waveVectorABC P n) := by
  change numberOpK P (gridK P ⟨n.val + 1, by omega⟩) = _
  rw [gridK_pos]

theorem negEmb_grid (P : ℕ) (n : Fin P) :
    numberOpK P (gridK P (negEmb P n)) = numberOpK P (-waveVectorABC P n) := by
  change numberOpK P (gridK P ⟨2 * P + 1 - n.val, by omega⟩) = _
  rw [numberOpK_gridK_neg]

/-- `univ : Fin (2P+2)` is the disjoint union of the two self-conjugate indices `{0, P+1}`,
the `+k` block `posEmb '' univ`, and the `−k` block `negEmb '' univ`. -/
theorem grid_univ_partition (P : ℕ) :
    (Finset.univ : Finset (Fin (2 * P + 2)))
      = ({⟨0, by omega⟩, ⟨P + 1, by omega⟩} : Finset (Fin (2 * P + 2)))
        ∪ ((Finset.univ.map (posEmb P)) ∪ (Finset.univ.map (negEmb P))) := by
  classical
  refine (Finset.eq_of_subset_of_card_le (Finset.subset_univ _) ?_).symm
  rw [Finset.card_univ, Fintype.card_fin]
  -- card of the RHS: the three blocks are pairwise disjoint, sizes 2, P, P
  have hposcard : (Finset.univ.map (posEmb P)).card = P := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hnegcard : (Finset.univ.map (negEmb P)).card = P := by
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have hposneg : Disjoint (Finset.univ.map (posEmb P)) (Finset.univ.map (negEmb P)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx
    obtain ⟨b, _, hb⟩ := hx'
    have ha := a.isLt; have hb' := b.isLt
    simp only [posEmb, negEmb, Function.Embedding.coeFn_mk, Fin.ext_iff] at hb
    omega
  have hspec : Disjoint ({⟨0, by omega⟩, ⟨P + 1, by omega⟩} : Finset (Fin (2 * P + 2)))
      ((Finset.univ.map (posEmb P)) ∪ (Finset.univ.map (negEmb P))) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_union, Finset.mem_map] at hx'
    rcases hx' with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;>
      · have ha := a.isLt
        simp only [posEmb, negEmb, Function.Embedding.coeFn_mk, Fin.ext_iff] at hx
        omega
  have hspeccard : ({⟨0, by omega⟩, ⟨P + 1, by omega⟩} : Finset (Fin (2 * P + 2))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]), Finset.card_singleton]
  rw [Finset.card_union_of_disjoint hspec, Finset.card_union_of_disjoint hposneg,
    hspeccard, hposcard, hnegcard]
  omega

/-- Commute helper: the `+k` reflections pairwise commute. -/
theorem posRefl_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n))) := by
  intro n _ m _ hnm
  refine commute_one_sub_two_smul ?_
  have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inl rfl)
  rwa [numberOpK_one_coe, numberOpK_one_coe] at this

/-- Commute helper: the `−k` reflections pairwise commute. -/
theorem negRefl_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => 1 - (2 : ℂ) • numberOpK P (-waveVectorABC P n))) := by
  intro n _ m _ hnm
  refine commute_one_sub_two_smul ?_
  have := numberOpK_commute_cross P n m hnm (Or.inr rfl) (Or.inr rfl)
  rwa [numberOpK_negone_coe, numberOpK_negone_coe] at this

/-- The `+k` and `−k` grid reflection products combine into the pair-parity product:
`(∏_n (1−2n_{k_n}))·(∏_n (1−2n_{−k_n})) = ∏_n P_{k_n}`. -/
theorem posneg_prod_eq_pairParity_prod (P : ℕ) :
    (Finset.univ : Finset (Fin P)).noncommProd
        (fun n => 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n)) (posRefl_commute P)
      * (Finset.univ : Finset (Fin P)).noncommProd
          (fun n => 1 - (2 : ℂ) • numberOpK P (-waveVectorABC P n)) (negRefl_commute P)
      = (Finset.univ : Finset (Fin P)).noncommProd
          (fun n => pairParity P (waveVectorABC P n)) (pairParity_pairwise_commute P) := by
  classical
  have comm_gf : ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (fun n m => Commute ((fun n => 1 - (2 : ℂ) • numberOpK P (-waveVectorABC P n)) n)
        ((fun n => 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n)) m)) := by
    intro n _ m _ hnm
    refine commute_one_sub_two_smul ?_
    have := numberOpK_commute_cross P n m hnm (Or.inr rfl) (Or.inl rfl)
    rwa [numberOpK_negone_coe, numberOpK_one_coe] at this
  rw [← Finset.noncommProd_mul_distrib _ _ (posRefl_commute P) (negRefl_commute P) comm_gf]
  rfl

/-- Commute hyp for the `posEmb`-reindexed reflections (image of the pos block). -/
theorem posEmbRefl_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => 1 - (2 : ℂ) • numberOpK P (gridK P (posEmb P n)))) := by
  intro n _ m _ hnm
  refine commute_one_sub_two_smul ?_
  rw [posEmb_grid, posEmb_grid]
  have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inl rfl)
  rwa [numberOpK_one_coe, numberOpK_one_coe] at this

/-- Commute hyp for the `negEmb`-reindexed reflections. -/
theorem negEmbRefl_commute (P : ℕ) :
    ((Finset.univ : Finset (Fin P)) : Set (Fin P)).Pairwise
      (Function.onFun Commute (fun n => 1 - (2 : ℂ) • numberOpK P (gridK P (negEmb P n)))) := by
  intro n _ m _ hnm
  refine commute_one_sub_two_smul ?_
  rw [negEmb_grid, negEmb_grid]
  have := numberOpK_commute_cross P n m hnm (Or.inr rfl) (Or.inr rfl)
  rwa [numberOpK_negone_coe, numberOpK_negone_coe] at this

theorem posprod_reindex (P : ℕ) :
    (Finset.univ : Finset (Fin P)).noncommProd
        (fun n => 1 - (2 : ℂ) • numberOpK P (gridK P (posEmb P n))) (posEmbRefl_commute P)
      = (Finset.univ : Finset (Fin P)).noncommProd
          (fun n => 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n)) (posRefl_commute P) :=
  Finset.noncommProd_congr rfl (fun n _ => by rw [posEmb_grid]) _

theorem negprod_reindex (P : ℕ) :
    (Finset.univ : Finset (Fin P)).noncommProd
        (fun n => 1 - (2 : ℂ) • numberOpK P (gridK P (negEmb P n))) (negEmbRefl_commute P)
      = (Finset.univ : Finset (Fin P)).noncommProd
          (fun n => 1 - (2 : ℂ) • numberOpK P (-waveVectorABC P n)) (negRefl_commute P) :=
  Finset.noncommProd_congr rfl (fun n _ => by rw [negEmb_grid]) _

set_option maxHeartbeats 400000 in
-- Raised heartbeat budget: this proof partitions a `noncommProd` over the full
-- `Fin (2P+2)` grid into the `{0, π}` and `±k_n` blocks via `grid_univ_partition`
-- and repeated `noncommProd` reindexing, which exceeds the default budget.
/-- The momentum-grid parity product factors as
`(1−2n_0)·(1−2n_π)·((∏_n (1−2n_{k_n}))·(∏_n (1−2n_{−k_n})))`. -/
theorem momentumParityProd_factor (P : ℕ) :
    (Finset.univ : Finset (Fin (2 * P + 2))).noncommProd
        (fun ℓ => 1 - (2 : ℂ) • numberOpK P (gridK P ℓ))
        (one_sub_two_smul_pairwise_commute _ _ (numberOpK_gridK_pairwise_commute P))
      = (1 - (2 : ℂ) • numberOpK P 0) * ((1 - (2 : ℂ) • numberOpK P Real.pi) *
          ((Finset.univ : Finset (Fin P)).noncommProd
              (fun n => 1 - (2 : ℂ) • numberOpK P (waveVectorABC P n)) (posRefl_commute P)
            * (Finset.univ : Finset (Fin P)).noncommProd
                (fun n => 1 - (2 : ℂ) • numberOpK P (-waveVectorABC P n)) (negRefl_commute P))) := by
  classical
  have hgcomm := one_sub_two_smul_pairwise_commute _ _ (numberOpK_gridK_pairwise_commute P)
  rw [Finset.noncommProd_congr (grid_univ_partition P) (fun _ _ => rfl) hgcomm]
  have hposneg : Disjoint (Finset.univ.map (posEmb P)) (Finset.univ.map (negEmb P)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_map] at hx hx'
    obtain ⟨a, _, rfl⟩ := hx; obtain ⟨b, _, hb⟩ := hx'
    have ha := a.isLt; have hb' := b.isLt
    simp only [posEmb, negEmb, Function.Embedding.coeFn_mk, Fin.ext_iff] at hb
    omega
  have hspecpn : Disjoint ({⟨0, by omega⟩, ⟨P + 1, by omega⟩} : Finset (Fin (2 * P + 2)))
      (Finset.univ.map (posEmb P) ∪ Finset.univ.map (negEmb P)) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_union, Finset.mem_map] at hx'
    rcases hx' with ⟨a, _, rfl⟩ | ⟨a, _, rfl⟩ <;>
      · have ha := a.isLt
        simp only [posEmb, negEmb, Function.Embedding.coeFn_mk, Fin.ext_iff] at hx
        omega
  rw [Finset.noncommProd_union_of_disjoint hspecpn,
    Finset.noncommProd_union_of_disjoint hposneg]
  -- specs = {0, P+1}: noncommProd = g 0 * g (P+1)
  have hne0pi : (⟨0, by omega⟩ : Fin (2 * P + 2)) ∉ ({⟨P + 1, by omega⟩} : Finset _) := by
    simp [Fin.ext_iff]
  rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hne0pi, Finset.noncommProd_singleton]
  -- reindex pos and neg products
  rw [noncommProd_map_embedding, noncommProd_map_embedding]
  -- rewrite grid values: gridK 0 → 0, gridK (P+1) → π, posEmb→k_n, negEmb→-k_n
  rw [gridK_zero, gridK_mid, posprod_reindex, negprod_reindex, mul_assoc]

/-- Absorption of a self-conjugate reflection: if `n_k · activeProj = 0` then
`(1 − 2 n_k) · activeProj = activeProj`. -/
theorem one_sub_two_numberOpK_mul_activeProj {P : ℕ} {k : ℝ}
    (h : numberOpK P k * activeProj P = 0) :
    (1 - (2 : ℂ) • numberOpK P k) * activeProj P = activeProj P := by
  rw [sub_mul, one_mul, smul_mul_assoc, h, smul_zero, sub_zero]

/-- The full momentum-grid parity product absorbs the active projector:
`(∏_ℓ (1−2n_{gridK ℓ}))·Π_A = Π_A`. Factor into `(1−2n_0)(1−2n_π)·∏_n P_{k_n}`
(`momentumParityProd_factor` + `posneg_prod_eq_pairParity_prod`), then absorb each: the
`n_0, n_π` self-conjugate factors via `numberOpK_{zero,npi}_mul_activeProj`, and the
pair-parity product via `noncommProd_pairParity_mul_activeProj`. -/
theorem momentumParityProd_mul_activeProj (P : ℕ) :
    (Finset.univ : Finset (Fin (2 * P + 2))).noncommProd
        (fun ℓ => 1 - (2 : ℂ) • numberOpK P (gridK P ℓ))
        (one_sub_two_smul_pairwise_commute _ _ (numberOpK_gridK_pairwise_commute P))
      * activeProj P = activeProj P := by
  rw [momentumParityProd_factor, posneg_prod_eq_pairParity_prod, mul_assoc, mul_assoc,
    noncommProd_pairParity_mul_activeProj,
    one_sub_two_numberOpK_mul_activeProj (numberOpK_npi_mul_activeProj P),
    one_sub_two_numberOpK_mul_activeProj (numberOpK_zero_mul_activeProj P)]

/-- On the dynamically-active subspace, the global parity operator acts as the
identity: `parityOp (2P+2) · ψ = ψ`.
Chains `parity_eq_grid_prod` (parity = momentum-grid product) →
`momentumParityProd_mul_activeProj` (the product absorbs `Π_A`) → `Π_A ψ = ψ`. -/
theorem inActiveSubspace_imp_even (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) : parityOp (2 * P + 2) * ψ = ψ := by
  unfold InActiveSubspace at hψ
  calc parityOp (2 * P + 2) * ψ
      = parityOp (2 * P + 2) * (activeProj P * ψ) := by rw [hψ]
    _ = (parityOp (2 * P + 2) * activeProj P) * ψ := by rw [op_mul_op_mul_ket]
    _ = ((Finset.univ : Finset (Fin (2 * P + 2))).noncommProd
          (fun ℓ => 1 - (2 : ℂ) • numberOpK P (gridK P ℓ))
          (one_sub_two_smul_pairwise_commute _ _ (numberOpK_gridK_pairwise_commute P))
          * activeProj P) * ψ := by rw [parity_eq_grid_prod]
    _ = activeProj P * ψ := by rw [momentumParityProd_mul_activeProj]
    _ = ψ := hψ

end

end QAOA.IsingChain.JordanWigner
