import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ReducedBondInvariance
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.WindowBlock
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.LayerBlockMatch
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.NestedWindow
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.NoncommProdBlock

/-!
# Canonical Light-Cone Matching — `LightconeStructuralMatching` inhabitant at an interior bond

This file constructs an inhabitant of the FGG light-cone matrix-entry
matching predicate `LightconeStructuralMatching` at an arbitrary interior
bond `j_s` (with `2*P+2 ≤ N`), the load-bearing structural piece of the
Path-1 closure of `bond_expectation_full_eq_reduced`.

## Status (COMPLETE — sorry-free and axiom-clean)

The entire light-cone match is **sorry-free and axiom-clean**
(`{propext, Classical.choice, Quot.sound}`): the exact window equality, the
canonical window bijection, the diagonal calculus, the base case `P = 0` (block
form), the **N-general window-block induction** (`canonical_windowBlock_match`),
the **nested-window restriction (piece (i))**
(`NestedWindow.restrictedMatrixEntry_of_subset` / `windowBlock_of_subset`), the
**middle factor** of the inductive step (`middle_factor_block_match`, including
the spectator-offset analysis and the cross-dimension recursion via the IH at
both `N` and `2P+4`), and the **two FGG §III generator-block-match lemmas**
(`mixer_factor_block_match`, `cost_factor_block_match`). The matrix-entry theorem
`canonical_matrix_entry_match` is derived from the block form with no induction.

The two generator-block-match lemmas reduce — via the
`windowBlock`-of-`noncommProd` calculus of `NoncommProdBlock` — both the
full-chain and reduced-chain layer touching-products to the **same** offset-
indexed `noncommProd` over `Fin (2P+4)` of per-offset block factors
(`exp(-iβ X_o)` for the mixer, `exp(-iγ cP(o))` for the cost). The PBC seam bond
`cP(2P+3)` never enters the cost product: it does not touch the depth-`P`
window (`costTouching_eq_offset_image`), confirming the numerical seam check at the
Lean level.

## Strategy (validated numerically to machine precision)

Three numerically-validated facts underpin the construction:

1. **Exact window equality.** When `2P+2 ≤ N`, the lightcone window
   `expand_by_n P (bondSeed j_s)` equals the cyclic interval
   `cyclicInterval N j_s P` *exactly* (not just `⊆`). This upgrades
   `expand_by_n_seed_subset_cyclicInterval` (a `⊆`) to an equality, which
   is what the bijection field `e` needs.

2. **Canonical bijection.** Both windows are `.map`-images of
   `Fin (2P+2)` under `lightconeInjection` (`lightconeInjection_range`),
   so `Fin (2P+2) ≃ expand_by_n P (bondSeed j_s)` and likewise at bond
   `0`; composing yields the bijection `e`.

3. **Matrix-entry match** (the FGG light-cone theorem proper): the
   restricted matrix entries of the full-chain and reduced-chain
   QAOA-conjugated bond observables agree under `e`. Numerically TRUE to
   ~1e-14; the seam bond `cP(2P+1)` of the PBC reduced cost contributes
   *exactly* `0` to the window matrix entries, so the reduced (ring) and
   full (path) window operators have identical restricted blocks.

Sources:
* FGG arXiv:1411.4028v1 §II l.113–134 (operator spreading, `j_s`-agnostic).
* arXiv:1906.08948v2 §IV l.620–678 (chain reduction).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: exact window equality (upgrade `⊆` to `=`)
-- ============================================================================

/-- The cyclic interval has cardinality **exactly** `2 * P + 2` when
`2 * P + 2 ≤ N`. The affine shift `lightconeInjection` is injective, so the
`.map` of `Finset.univ` has full card; `lightconeInjection_range` identifies
that image with `cyclicInterval`. -/
theorem cyclicInterval_card {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    (cyclicInterval N j P).card = 2 * P + 2 := by
  rw [← lightconeInjection_range j P hP, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]

/-- `bondSeed j` is definitionally the two-element finset `{j, nextSite j}`. -/
theorem bondSeed_eq {n : ℕ} (k : Fin n) :
    bondSeed k = ({k, IsingModel.nextSite k} : Finset (Fin n)) := by
  unfold bondSeed
  rw [Finset.union_comm]
  ext x
  simp [Finset.mem_insert, or_comm]

/-- A modular-arithmetic helper: for `a ≥ 1` and `N > 0`,
`(a + N - 1) % N = (a % N + N - 1) % N`. Used to identify `prevSite` of a
mod-`N` site with the next interval offset. -/
private theorem mod_pred_eq {a N : ℕ} (hN : 0 < N) :
    (a + N - 1) % N = (a % N + N - 1) % N := by
  conv_lhs => rw [show a + N - 1 = (a + (N - 1)) from by omega]
  conv_rhs => rw [show a % N + N - 1 = a % N + (N - 1) from by omega]
  conv_rhs => rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]

/-- The reverse inclusion at the single-step level: the larger cyclic
interval `cyclicInterval N j (P+1)` is contained in `expand_by_one` of the
smaller one. Geometrically, `expand_by_one` extends the connected interval
by one site on each end (`prevSite` on the left, `nextSite` on the right),
which is exactly the two extra offsets `cyclicInterval N j (P+1)` adds. -/
theorem cyclicInterval_succ_subset_expand_by_one {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    cyclicInterval N j (P + 1) ⊆ expand_by_one (cyclicInterval N j P) := by
  intro y hy
  unfold cyclicInterval at hy
  rw [Finset.mem_image] at hy
  obtain ⟨i, hi_range, hiy⟩ := hy
  rw [Finset.mem_range] at hi_range
  -- y.val = (j.val + (N - (P+1)) + i) % N for some i ∈ [0, 2P+3].
  --   * i = 0          → y is the new left site = prevSite of the old left end.
  --   * 1 ≤ i ≤ 2P+2   → y is in the old interval (offset i-1).
  --   * i = 2P+3       → y is the new right site = nextSite of the old right end.
  have hP1 : P + 1 ≤ N := by omega
  have hP_le : P ≤ N := by omega
  have hjN : j.val < N := j.isLt
  have hN0 : 0 < N := by omega
  unfold expand_by_one
  by_cases hi0 : i = 0
  · -- New left end: y = prevSite (interval offset 0 of the old interval).
    subst hi0
    refine Finset.mem_union_right _ ?_
    rw [Finset.mem_image]
    refine ⟨⟨(j.val + (N - P) + 0) % N,
      Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩, ?_, ?_⟩
    · unfold cyclicInterval
      rw [Finset.mem_image]
      exact ⟨0, Finset.mem_range.mpr (by omega), rfl⟩
    · apply Fin.ext
      rw [prevSite_val, ← hiy]
      change ((j.val + (N - P) + 0) % N + N - 1) % N =
          ((j.val + (N - (P + 1)) + 0) % N)
      -- LHS = (x % N + N - 1) % N with x := j.val+(N-P)+0; rewrite to (x + N - 1) % N.
      rw [← mod_pred_eq hN0]
      -- Goal: (j.val + (N - P) + 0 + N - 1) % N = (j.val + (N - (P+1)) + 0) % N.
      have hrw : j.val + (N - P) + 0 + N - 1 = (j.val + (N - (P + 1)) + 0) + N := by omega
      rw [hrw, Nat.add_mod_right]
  · by_cases hilast : i = 2 * P + 3
    · -- New right end: y = nextSite (interval offset 2P+1 of the old interval).
      subst hilast
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [Finset.mem_image]
      refine ⟨⟨(j.val + (N - P) + (2 * P + 1)) % N,
        Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩, ?_, ?_⟩
      · unfold cyclicInterval
        rw [Finset.mem_image]
        exact ⟨2 * P + 1, Finset.mem_range.mpr (by omega), rfl⟩
      · apply Fin.ext
        rw [IsingModel.nextSite_val, ← hiy]
        change ((j.val + (N - P) + (2 * P + 1)) % N + 1) % N =
            ((j.val + (N - (P + 1)) + (2 * P + 3)) % N)
        rw [Nat.add_mod ((j.val + (N - P) + (2 * P + 1)) % N) 1 N, Nat.mod_mod,
            ← Nat.add_mod]
        congr 1
        omega
    · -- Interior: offset i-1 of the old interval, in cyclicInterval N j P.
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      unfold cyclicInterval
      rw [Finset.mem_image]
      refine ⟨i - 1, Finset.mem_range.mpr (by omega), ?_⟩
      apply Fin.ext
      rw [← hiy]
      change ((j.val + (N - P) + (i - 1)) % N) = ((j.val + (N - (P + 1)) + i) % N)
      congr 1
      omega

/-- `expand_by_one` is monotone in its argument. -/
theorem expand_by_one_mono {N : ℕ} {S T : Finset (Fin N)} (h : S ⊆ T) :
    expand_by_one S ⊆ expand_by_one T := by
  unfold expand_by_one
  intro x hx
  rw [Finset.mem_union, Finset.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (h hx))
  · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, h ha, hax⟩
  · refine Finset.mem_union_right _ ?_
    rw [Finset.mem_image] at hx ⊢
    obtain ⟨a, ha, hax⟩ := hx
    exact ⟨a, h ha, hax⟩

/-- **Reverse inclusion.** When `2 * P + 2 ≤ N`, the cyclic interval is
contained in the `P`-fold lightcone window of the bond seed. By induction on
`P`: the base case `cyclicInterval N j 0 = {j, nextSite j} = bondSeed j`, and
the step extends one site on each end via
`cyclicInterval_succ_subset_expand_by_one`. -/
theorem cyclicInterval_subset_expand_by_n {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    cyclicInterval N j P ⊆ expand_by_n P (bondSeed j) := by
  induction P with
  | zero =>
    rw [expand_by_n_zero, bondSeed_eq]
    -- cyclicInterval N j 0 = {j, nextSite j}: offsets {0, 1}.
    intro x hx
    unfold cyclicInterval at hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi_range, hix⟩ := hx
    rw [Finset.mem_range] at hi_range
    interval_cases i
    · -- offset 0 → j.
      rw [Finset.mem_insert]
      left
      apply Fin.ext
      rw [← hix]
      change (j.val + (N - 0) + 0) % N = j.val
      have : j.val + (N - 0) + 0 = j.val + N := by omega
      rw [this, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt j.isLt
    · -- offset 1 → nextSite j.
      rw [Finset.mem_insert, Finset.mem_singleton]
      right
      apply Fin.ext
      rw [← hix, IsingModel.nextSite_val]
      change (j.val + (N - 0) + 1) % N = (j.val + 1) % N
      have hrw : j.val + (N - 0) + 1 = (j.val + 1) + N := by omega
      rw [hrw, Nat.add_mod_right]
  | succ P ih =>
    have hP' : 2 * P + 2 ≤ N := by omega
    rw [expand_by_n_succ]
    refine subset_trans (cyclicInterval_succ_subset_expand_by_one j P hP) ?_
    exact expand_by_one_mono (ih hP')

/-- **Exact lightcone-window equality.** When `2 * P + 2 ≤ N`, the
`P`-fold lightcone window of the bond seed equals the cyclic interval. -/
theorem expand_by_n_bondSeed_eq_cyclicInterval {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    expand_by_n P (bondSeed j) = cyclicInterval N j P := by
  apply Finset.Subset.antisymm
  · rw [bondSeed_eq]
    exact expand_by_n_seed_subset_cyclicInterval j P hP
  · exact cyclicInterval_subset_expand_by_n j P hP

-- ============================================================================
-- Section: the canonical bijection `e` between the two windows
-- ============================================================================

/-- The lightcone injection lands in the window `expand_by_n P (bondSeed j)`. -/
theorem lightconeInjection_mem_window {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) (k : Fin (2 * P + 2)) :
    lightconeInjection j P hP k ∈ expand_by_n P (bondSeed j) := by
  rw [expand_by_n_bondSeed_eq_cyclicInterval j P hP,
      ← lightconeInjection_range j P hP]
  exact Finset.mem_map_of_mem _ (Finset.mem_univ k)

/-- `Fin (2P+2) ≃ ↥(expand_by_n P (bondSeed j))`, the canonical identification
of the reduced-chain index set with the full-chain lightcone window, induced
by `lightconeInjection`. -/
def windowEquiv {N : ℕ} (j : Fin N) (P : ℕ) (hP : 2 * P + 2 ≤ N) :
    Fin (2 * P + 2) ≃ (expand_by_n P (bondSeed j)) := by
  refine Equiv.ofBijective
    (fun k => ⟨lightconeInjection j P hP k, lightconeInjection_mem_window j P hP k⟩) ?_
  constructor
  · -- injective: `lightconeInjection` is an embedding.
    intro a b hab
    have : lightconeInjection j P hP a = lightconeInjection j P hP b :=
      congrArg Subtype.val hab
    exact (lightconeInjection j P hP).injective this
  · -- surjective: every window element is in the image.
    rintro ⟨x, hx⟩
    rw [expand_by_n_bondSeed_eq_cyclicInterval j P hP,
        ← lightconeInjection_range j P hP, Finset.mem_map] at hx
    obtain ⟨k, _hk, hkx⟩ := hx
    exact ⟨k, by apply Subtype.ext; exact hkx⟩

@[simp] theorem windowEquiv_apply_val {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) (k : Fin (2 * P + 2)) :
    ((windowEquiv j P hP) k : Fin N) = lightconeInjection j P hP k := rfl

/-- The window of `windowEquiv j P hP` has cardinality exactly `2P+2`, matching
the offset type `Fin (2P+2)`. -/
theorem windowEquiv_card {N : ℕ} (j : Fin N) (P : ℕ) (hP : 2 * P + 2 ≤ N) :
    Fintype.card (Fin (2 * P + 2)) = (expand_by_n P (bondSeed j)).card := by
  rw [Fintype.card_fin, expand_by_n_bondSeed_eq_cyclicInterval j P hP,
      cyclicInterval_card j P hP]

/-- **The canonical bijection between the two lightcone windows.** Identifies
the full-chain window at `j_s` with the reduced-chain window at bond `0`,
both via `lightconeInjection`. This is the `e` field of
`LightconeStructuralMatching`. -/
def canonicalWindowEquiv {N : ℕ} (j_s : Fin N) (P : ℕ) (hP : 2 * P + 2 ≤ N) :
    (expand_by_n P (bondSeed j_s)) ≃
      (expand_by_n P (bondSeed (⟨0, by omega⟩ : Fin (2 * P + 2)))) :=
  (windowEquiv j_s P hP).symm.trans
    (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))

-- ============================================================================
-- Section: membership facts for the bond seed
-- ============================================================================

theorem self_mem_bondSeed {n : ℕ} (k : Fin n) : k ∈ bondSeed k := by
  rw [bondSeed_eq]; exact Finset.mem_insert_self _ _

theorem nextSite_mem_bondSeed {n : ℕ} (k : Fin n) :
    IsingModel.nextSite k ∈ bondSeed k := by
  rw [bondSeed_eq]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- The canonical window bijection threads through the common index set:
applying `e.symm` to the reduced-window image of `m` yields the full-window
image of the same index `m`. -/
theorem canonicalWindowEquiv_symm_windowEquiv {N : ℕ} (j_s : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) (m : Fin (2 * P + 2)) :
    (canonicalWindowEquiv j_s P hP).symm
        (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega) m) =
      windowEquiv j_s P hP m := by
  unfold canonicalWindowEquiv
  rw [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]

/-- `extendByZeroOnS` is injective on the restricted data: two extensions
agree iff the restricted data agree (both are `0` off `S`). -/
theorem extendByZeroOnS_eq_iff {n : ℕ} (S : Finset (Fin n)) (zs ws : S → Fin 2) :
    extendByZeroOnS S zs = extendByZeroOnS S ws ↔ zs = ws := by
  constructor
  · intro h
    funext k
    have := congrFun h k.1
    rw [extendByZeroOnS_apply_mem (h := k.2), extendByZeroOnS_apply_mem (h := k.2)] at this
    exact this
  · intro h; rw [h]

-- ============================================================================
-- Section: diagonal restricted-matrix-entry of `chainPairInteraction`
-- ============================================================================

/-- The restricted matrix entry of the (diagonal) bond observable
`chainPairInteraction k` on a window `S ⊇ {k, nextSite k}`: it is the spin
product `s_k · s_{k+1}` when the row/column data agree, and `0` otherwise.
The spins are read directly off the restricted data via the membership of
`k` and `nextSite k` in `S`. -/
theorem restrictedMatrixEntry_chainPairInteraction {n : ℕ} (S : Finset (Fin n))
    (k : Fin n) (hk : k ∈ S) (hnk : IsingModel.nextSite k ∈ S)
    (zs ws : S → Fin 2) :
    restrictedMatrixEntry S (IsingModel.chainPairInteraction k) zs ws =
      (if extendByZeroOnS S zs = extendByZeroOnS S ws then
        ((IsingModel.spinValue (ws ⟨k, hk⟩) *
          IsingModel.spinValue (ws ⟨IsingModel.nextSite k, hnk⟩) : ℝ) : ℂ)
       else 0) := by
  unfold restrictedMatrixEntry
  rw [IsingModel.chainPairInteraction_entry_on_computationalBasis k
        (extendByZeroOnS S ws) ((Qubits.bitStringEquiv n) (extendByZeroOnS S zs))]
  -- value = (spin·spin) * (computationalBasisKet (ext ws)).vec (be (ext zs))
  show (((IsingModel.classicalSpin (extendByZeroOnS S ws) k *
      IsingModel.classicalSpin (extendByZeroOnS S ws) (IsingModel.nextSite k) : ℝ) : ℂ)) *
        (Qubits.computationalBasisKet n (extendByZeroOnS S ws)).vec
          ((Qubits.bitStringEquiv n) (extendByZeroOnS S zs)) = _
  rw [Qubits.computationalBasisKet]
  -- stdKet vec at index: if be(ext ws) = be(ext zs) then 1 else 0.
  have hstd : (stdKet (Qubits.NQubitDim n) ((Qubits.bitStringEquiv n) (extendByZeroOnS S ws))).vec
      ((Qubits.bitStringEquiv n) (extendByZeroOnS S zs)) =
      (if (Qubits.bitStringEquiv n) (extendByZeroOnS S ws) =
          (Qubits.bitStringEquiv n) (extendByZeroOnS S zs) then (1 : ℂ) else 0) :=
    stdKet_apply _ _
  rw [hstd]
  -- classicalSpin (ext ws) k = spinValue (ws ⟨k, hk⟩) since k ∈ S.
  rw [show IsingModel.classicalSpin (extendByZeroOnS S ws) k =
        IsingModel.spinValue (ws ⟨k, hk⟩) from by
      unfold IsingModel.classicalSpin
      rw [extendByZeroOnS_apply_mem (h := hk)]]
  rw [show IsingModel.classicalSpin (extendByZeroOnS S ws) (IsingModel.nextSite k) =
        IsingModel.spinValue (ws ⟨IsingModel.nextSite k, hnk⟩) from by
      unfold IsingModel.classicalSpin
      rw [extendByZeroOnS_apply_mem (h := hnk)]]
  -- Reconcile the `if` conditions: be a = be b ↔ a = b (injective), and
  -- swap the equality direction.
  by_cases hd : extendByZeroOnS S zs = extendByZeroOnS S ws
  · rw [if_pos hd, if_pos (by rw [hd])]
    rw [mul_one]
  · rw [if_neg hd, if_neg ?_, mul_zero]
    intro hcontra
    exact hd ((Qubits.bitStringEquiv n).injective hcontra).symm

-- ============================================================================
-- Section: depth-`P` ↔ depth-`P+1` window-offset compatibility
-- ============================================================================

/-- **Window-offset shift.** The depth-`P` lightcone window sits inside the
depth-`P+1` window at offsets `[1, 2P+2]`: offset `k` of the depth-`P`
injection equals offset `k+1` of the depth-`P+1` injection. (The depth-`P+1`
window adds the two end sites at offsets `0` and `2P+3`.) -/
theorem lightconeInjection_succ_shift {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (hP' : 2 * P + 2 ≤ N) (k : Fin (2 * P + 2)) :
    (lightconeInjection j (P + 1) hP ⟨k.val + 1, by omega⟩ : Fin N) =
      lightconeInjection j P hP' k := by
  apply Fin.ext
  change (j.val + (N - (P + 1)) + (k.val + 1)) % N = (j.val + (N - P) + k.val) % N
  congr 1
  omega

/-- The depth-`P+1` window equivalence sends the depth-`P` window site at offset
`i` back to the offset `i+1` index: `εF.symm ⟨depth-P site i⟩ = ⟨i+1⟩`. The two
extra end sites occupy offsets `0` and `2P+3`. -/
theorem windowEquiv_succ_symm_lightconeInjection {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (hP' : 2 * P + 2 ≤ N) (i : Fin (2 * P + 2))
    (hmem : (lightconeInjection j P hP' i : Fin N) ∈ expand_by_n (P + 1) (bondSeed j)) :
    (windowEquiv j (P + 1) hP).symm ⟨lightconeInjection j P hP' i, hmem⟩ =
      (⟨i.val + 1, by omega⟩ : Fin (2 * (P + 1) + 2)) := by
  apply (windowEquiv j (P + 1) hP).injective
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  rw [windowEquiv_apply_val]
  exact (lightconeInjection_succ_shift j P hP hP' i).symm

/-- **Spectator-offset characterization.** The depth-`P+1` window site at offset
`o` lies in the depth-`P` window iff `o` is an *interior* offset `1 ≤ o ≤ 2P+2`;
the two spectator (end) sites are exactly offsets `0` and `2P+3`. -/
theorem windowEquiv_succ_mem_depthP_iff {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (o : Fin (2 * (P + 1) + 2)) :
    (windowEquiv j (P + 1) hP o : Fin N) ∈ expand_by_n P (bondSeed j) ↔
      (o.val ≠ 0 ∧ o.val ≠ 2 * P + 3) := by
  have hP' : 2 * P + 2 ≤ N := by omega
  rw [expand_by_n_bondSeed_eq_cyclicInterval j P hP', windowEquiv_apply_val]
  constructor
  · intro hin
    unfold cyclicInterval at hin
    rw [Finset.mem_image] at hin
    obtain ⟨i, hi, hival⟩ := hin
    rw [Finset.mem_range] at hi
    -- The cyclic-interval point at offset `i` is `lightconeInjection j (P+1) ⟨i+1⟩`
    -- (offset shift); injectivity of `lightconeInjection j (P+1)` gives `o = i+1`.
    have hshift : (lightconeInjection j (P + 1) hP ⟨i + 1, by omega⟩ : Fin N) =
        lightconeInjection j P hP' ⟨i, by omega⟩ :=
      lightconeInjection_succ_shift j P hP hP' ⟨i, by omega⟩
    have hpoint : (lightconeInjection j P hP' ⟨i, by omega⟩ : Fin N) =
        lightconeInjection j (P + 1) hP o := by
      apply Fin.ext; rw [← hival]; rfl
    have hoeq : lightconeInjection j (P + 1) hP ⟨i + 1, by omega⟩ =
        lightconeInjection j (P + 1) hP o := by rw [hshift, hpoint]
    have : (⟨i + 1, by omega⟩ : Fin (2 * (P + 1) + 2)) = o :=
      (lightconeInjection j (P + 1) hP).injective hoeq
    have hov : o.val = i + 1 := by rw [← this]
    omega
  · intro ⟨hne0, hne3⟩
    -- `1 ≤ o ≤ 2P+2`, so `o = (o-1)+1` is an interior offset.
    have ho_lt : o.val < 2 * (P + 1) + 2 := o.isLt
    unfold cyclicInterval
    rw [Finset.mem_image]
    refine ⟨o.val - 1, Finset.mem_range.mpr (by omega), ?_⟩
    apply Fin.ext
    show (j.val + (N - P) + (o.val - 1)) % N = (lightconeInjection j (P + 1) hP o : Fin N).val
    change _ = (j.val + (N - (P + 1)) + o.val) % N
    congr 1
    omega

-- ============================================================================
-- Section: window-block layer match (piece (ii) — the inductive step)
-- ============================================================================

/-- **Middle-factor block match.** The depth-`P` QAOA conjugate of the bond
observable, viewed as a window block over the depth-`P+1` window, matches the
reduced-chain depth-`P` conjugate block, given the depth-`P` block equality
`hblock`. The depth-`P` conjugate is tensor-supported on the depth-`P` window
(a strict sub-window of the depth-`P+1` window), so the nested-window
restriction (`restrictedMatrixEntry_of_subset`, piece (i)) reduces the
depth-`P+1` block to the depth-`P` block, which `hblock` then discharges.

Note this lemma takes *two* depth-`P` block hypotheses: `hblockF` matches the
full chain (dim `N`) to the canonical reduced chain (dim `2P+2`), and `hblockR`
matches the reduced chain at the *larger* dimension `2P+4` (the depth-`P`
conjugate of the bond `0` on `Fin (2P+4)`) to the same canonical reduced chain.
Both are instances of the depth-`P` light-cone block match (the latter at
`N := 2P+4`); the middle factor is their transitive composition through the
common `2P+2` block, after the nested-window restriction on each side.

Source: FGG arXiv:1411.4028v1 §III (lightcone middle factor). -/
private theorem spectator_cond_iff {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N)
    (a b : Fin (Qubits.NQubitDim (2 * (P + 1) + 2))) :
    (∀ (k : ↥(expand_by_n (P + 1) (bondSeed j))),
        (k : Fin N) ∉ expand_by_n P (bondSeed j) →
        windowData (windowEquiv j (P + 1) hP) a k =
          windowData (windowEquiv j (P + 1) hP) b k) ↔
      (∀ o : Fin (2 * (P + 1) + 2), (o.val = 0 ∨ o.val = 2 * P + 3) →
        (Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm a o =
          (Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm b o) := by
  constructor
  · intro h o ho
    -- Spectator offset `o`; its window site `εF o` is outside `S_P`.
    have hnotmem : (windowEquiv j (P + 1) hP o : Fin N) ∉ expand_by_n P (bondSeed j) := by
      rw [windowEquiv_succ_mem_depthP_iff j P hP]
      push_neg
      intro _; omega
    have := h (windowEquiv j (P + 1) hP o) hnotmem
    -- `windowData εF a (εF o) = bitStringEquiv.symm a o` (since `εF.symm (εF o) = o`).
    unfold windowData at this
    simpa only [Equiv.symm_apply_apply] using this
  · intro h k hk
    -- `k = εF o` for `o := εF.symm k`; `k ∉ S_P` forces `o` a spectator offset.
    set o := (windowEquiv j (P + 1) hP).symm k with ho_def
    have hko : windowEquiv j (P + 1) hP o = k := Equiv.apply_symm_apply _ _
    have ho_spec : o.val = 0 ∨ o.val = 2 * P + 3 := by
      by_contra hcon
      push_neg at hcon
      apply hk
      rw [← hko, windowEquiv_succ_mem_depthP_iff j P hP]
      exact ⟨hcon.1, hcon.2⟩
    have hval := h o ho_spec
    unfold windowData
    exact hval
theorem middle_factor_block_match {N : ℕ} (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (γ β : Fin (P + 1) → ℝ) (j_s : Fin N)
    (hP' : 2 * P + 2 ≤ N)
    (hblockF :
      windowBlock (windowEquiv j_s P hP') (fullChainQAOAConj P
          (fun i => γ i.castSucc) (fun i => β i.castSucc) j_s) =
        windowBlock
          (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))
          (reducedChainQAOAConj P (fun i => γ i.castSucc) (fun i => β i.castSucc)))
    (hblockR :
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) P (by omega))
          (fullChainQAOAConj P (fun i => γ i.castSucc) (fun i => β i.castSucc)
            (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2))) =
        windowBlock
          (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))
          (reducedChainQAOAConj P (fun i => γ i.castSucc) (fun i => β i.castSucc))) :
    windowBlock (windowEquiv j_s (P + 1) hP)
        (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
          (IsingModel.chainPairInteraction j_s)) =
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
          (IsingModel.chainPairInteraction (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) := by
  classical
  -- Abbreviations.
  set zr : Fin (2 * (P + 1) + 2) := ⟨0, by omega⟩ with hzr
  -- The depth-`P` conjugates are tensor-supported on the depth-`P` windows,
  -- strict sub-windows of the depth-`P+1` windows.
  have hOfull : tensorSupportedOn (expand_by_n P (bondSeed j_s))
      (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
        (IsingModel.chainPairInteraction j_s)) :=
    tensorSupportedOn_qaoa_conj (tensorSupportedOn_chainPairInteraction j_s) P _ _
  have hOred : tensorSupportedOn (expand_by_n P (bondSeed zr))
      (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
        (IsingModel.chainPairInteraction zr)) :=
    tensorSupportedOn_qaoa_conj (tensorSupportedOn_chainPairInteraction zr) P _ _
  have hsubF : expand_by_n P (bondSeed j_s) ⊆ expand_by_n (P + 1) (bondSeed j_s) :=
    expand_by_n_subset_succ P (bondSeed j_s)
  have hsubR : expand_by_n P (bondSeed zr) ⊆ expand_by_n (P + 1) (bondSeed zr) :=
    expand_by_n_subset_succ P (bondSeed zr)
  funext a b
  -- Apply the nested-window restriction (piece (i)) to both blocks.
  rw [windowBlock_of_subset hsubF (windowEquiv j_s (P + 1) hP) hOfull,
      windowBlock_of_subset hsubR (windowEquiv zr (P + 1) (by omega)) hOred]
  -- The restricted depth-`P` data are *chain-independent* once read through the
  -- offset shift: both equal the depth-`P+1` bit-data at offsets `[1, 2P+2]`.
  -- `innerF`/`innerR`: the depth-`P` window data, read at offset `i`, equals
  -- the depth-`P+1` bit-data at offset `i+1` (same on both chains).
  have innerF : ∀ (c : Fin (Qubits.NQubitDim (2 * (P + 1) + 2)))
      (i : Fin (2 * P + 2)),
      restrictData hsubF (windowData (windowEquiv j_s (P + 1) hP) c)
          (windowEquiv j_s P hP' i) =
        (Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm c ⟨i.val + 1, by omega⟩ := by
    intro c i
    unfold restrictData windowData
    exact congrArg ((Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm c)
      (windowEquiv_succ_symm_lightconeInjection j_s P hP hP' i _)
  have innerR : ∀ (c : Fin (Qubits.NQubitDim (2 * (P + 1) + 2)))
      (i : Fin (2 * P + 2)),
      restrictData hsubR (windowData (windowEquiv zr (P + 1) (by omega)) c)
          (windowEquiv zr P (by omega) i) =
        (Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm c ⟨i.val + 1, by omega⟩ := by
    intro c i
    unfold restrictData windowData
    exact congrArg ((Qubits.bitStringEquiv (2 * (P + 1) + 2)).symm c)
      (windowEquiv_succ_symm_lightconeInjection zr P (by omega) (by omega) i _)
  -- (B) The depth-`P` restricted entries match: route through the common
  -- canonical reduced (dim `2P+2`) block via `hblockF` then `hblockR.symm`.
  have hB :
      restrictedMatrixEntry (expand_by_n P (bondSeed j_s))
          (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
            (IsingModel.chainPairInteraction j_s))
          (restrictData hsubF (windowData (windowEquiv j_s (P + 1) hP) a))
          (restrictData hsubF (windowData (windowEquiv j_s (P + 1) hP) b)) =
        restrictedMatrixEntry (expand_by_n P (bondSeed zr))
          (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
            (IsingModel.chainPairInteraction zr))
          (restrictData hsubR (windowData (windowEquiv zr (P + 1) (by omega)) a))
          (restrictData hsubR (windowData (windowEquiv zr (P + 1) (by omega)) b)) := by
    rw [restrictedMatrixEntry_eq_windowBlock (windowEquiv j_s P hP'),
        restrictedMatrixEntry_eq_windowBlock (windowEquiv zr P (by omega))]
    -- Rewrite the encode arguments via `innerF`/`innerR` to chain-independent
    -- bit-data; both encodes become the same `Fin (2^(2P+4))` index.
    simp only [innerF, innerR]
    -- `qaoaConjugate ... j_s = fullChainQAOAConj`, `... zr = fullChainQAOAConj`
    -- (both by def); route `hblockF` then `hblockR.symm`.
    exact congrFun (congrFun (hblockF.trans hblockR.symm) _) _
  -- (A) The spectator conditions are equivalent.
  have hspec :
      (∀ (k : ↥(expand_by_n (P + 1) (bondSeed j_s))),
          (k : Fin N) ∉ expand_by_n P (bondSeed j_s) →
          windowData (windowEquiv j_s (P + 1) hP) a k =
            windowData (windowEquiv j_s (P + 1) hP) b k) ↔
        (∀ (k : ↥(expand_by_n (P + 1) (bondSeed zr))),
          (k : Fin (2 * (P + 1) + 2)) ∉ expand_by_n P (bondSeed zr) →
          windowData (windowEquiv zr (P + 1) (by omega)) a k =
            windowData (windowEquiv zr (P + 1) (by omega)) b k) := by
    rw [spectator_cond_iff j_s P hP a b, spectator_cond_iff zr P (by omega) a b]
  by_cases hc : (∀ (k : ↥(expand_by_n (P + 1) (bondSeed j_s))),
      (k : Fin N) ∉ expand_by_n P (bondSeed j_s) →
      windowData (windowEquiv j_s (P + 1) hP) a k =
        windowData (windowEquiv j_s (P + 1) hP) b k)
  · rw [if_pos hc, if_pos (hspec.mp hc), hB]
  · rw [if_neg hc, if_neg (fun h => hc (hspec.mpr h))]

/-- **Mixer-factor block match (FGG §III edge analysis).** The window block of
the full-chain mixer touching-product over the depth-`P` one-ring matches the
reduced-chain mixer touching-product block. Each single-site mixer factor
`exp(-iβ X_j)` whose site lies in the window maps to the reduced-chain factor at
the bijected site; factors outside act trivially. -/
theorem mixer_factor_block_match {N : ℕ} (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (j_s : Fin N) (_hP' : 2 * P + 2 ≤ N) (b : ℝ) :
    windowBlock (windowEquiv j_s (P + 1) hP)
        (mixerTouchingProd (expand_by_one (expand_by_n P (bondSeed j_s))) b) =
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (mixerTouchingProd (expand_by_one (expand_by_n P
          (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2))))) b) := by
  -- Both windows are `expand_by_n (P+1)` of their bond seed (= the
  -- `expand_by_one (expand_by_n P …)` of the mixer set, definitionally).
  rw [show expand_by_one (expand_by_n P (bondSeed j_s)) =
        expand_by_n (P + 1) (bondSeed j_s) from rfl,
      show expand_by_one (expand_by_n P
            (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) =
        expand_by_n (P + 1) (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2))) from rfl]
  rw [windowBlock_mixerTouchingProd (windowEquiv j_s (P + 1) hP)
        (windowEquiv_card j_s (P + 1) hP) b,
      windowBlock_mixerTouchingProd
        (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (windowEquiv_card (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega)) b]

-- ============================================================================
-- Section: mixer touching-set offset characterization (depth-`P` window)
-- ============================================================================
-- After the convention flip `U·O·U† → U†·O·U`, the mixer layer is INNERMOST and
-- its touching product is indexed by the depth-`P` window `expand_by_n P (bondSeed j)`
-- (not its one-ring). The depth-`P+1` window block of that product is again a
-- chain-independent offset `noncommProd` (over the interior offsets `1…2P+2`),
-- so the full and reduced blocks match. Modeled on `windowBlock_costTouchingProd`.

/-- The mixer offset set: the interior offsets `o` with `o.val ≠ 0` and
`o.val ≠ 2P+3` — exactly the offsets whose window site lies in the depth-`P`
window (`windowEquiv_succ_mem_depthP_iff`). -/
private def mixerOffsetSet (P : ℕ) : Finset (Fin (2 * (P + 1) + 2)) :=
  Finset.univ.filter (fun o => o.val ≠ 0 ∧ o.val ≠ 2 * P + 3)

/-- **Mixer touching-set offset characterization (depth-`P` window).** The sites
of the depth-`P` window are exactly the `windowEmbedding`-image of the mixer
offset set. Chain-independent: holds identically on every chain length `N`. -/
theorem mixerTouching_eq_offset_image {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    (Finset.univ.filter (fun k : Fin N => k ∈ expand_by_n P (bondSeed j))) =
      (mixerOffsetSet P).map (windowEmbedding (windowEquiv j (P + 1) hP)) := by
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    mixerOffsetSet, windowEmbedding_apply]
  constructor
  · intro hk
    have hkW1 : k ∈ expand_by_n (P + 1) (bondSeed j) :=
      expand_by_n_subset_succ P (bondSeed j) hk
    refine ⟨(windowEquiv j (P + 1) hP).symm ⟨k, hkW1⟩, ?_, ?_⟩
    · have hmem : (windowEquiv j (P + 1) hP
          ((windowEquiv j (P + 1) hP).symm ⟨k, hkW1⟩) : Fin N) ∈
          expand_by_n P (bondSeed j) := by
        rw [Equiv.apply_symm_apply]; exact hk
      rw [windowEquiv_succ_mem_depthP_iff] at hmem
      exact hmem
    · rw [Equiv.apply_symm_apply]
  · rintro ⟨o, ho, hok⟩
    rw [← hok, windowEquiv_succ_mem_depthP_iff]
    exact ho

/-- **`windowBlock` of `mixerTouchingProd` over the depth-`P` window is the
offset mixer product.** The depth-`P+1` window block of the mixer touching-product
over the depth-`P` window equals the `noncommProd` over the mixer offset set of
the offset mixer factors `exp(-iβ X_o)` — entirely chain-independent. -/
theorem windowBlock_mixerTouchingProd_depthP {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (b : ℝ) :
    windowBlock (windowEquiv j (P + 1) hP)
        (mixerTouchingProd (expand_by_n P (bondSeed j)) b) =
      (mixerOffsetSet P).noncommProd
        (fun o => NormedSpace.exp ((((-b : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX o))
        (fun i _ j' _ _ =>
          (Qubits.localPauliX_commute i j').smul_left _ |>.smul_right _ |>.exp) := by
  classical
  unfold mixerTouchingProd
  set W := expand_by_n (P + 1) (bondSeed j) with hW_def
  -- Each single-site mixer factor at a depth-`P` site is supported on `W`.
  have hsupp : ∀ k ∈ (Finset.univ.filter (fun k : Fin N => k ∈ expand_by_n P (bondSeed j))),
      tensorSupportedOn W
        (NormedSpace.exp ((((-b : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX k)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    have hkW : k ∈ W := expand_by_n_subset_succ P (bondSeed j) hk.2
    refine tensorSupportedOn_mono (S := ({k} : Finset (Fin N))) ?_
      (tensorSupportedOn_exp_localPauliX b k)
    intro x hx; rw [Finset.mem_singleton] at hx; rw [hx]; exact hkW
  rw [windowBlock_noncommProd (windowEquiv j (P + 1) hP) _ _ _ hsupp]
  rw [Finset.noncommProd_congr (mixerTouching_eq_offset_image j P hP)
        (fun _ _ => rfl)]
  rw [noncommProd_map_embedding (windowEmbedding (windowEquiv j (P + 1) hP))
        (mixerOffsetSet P)]
  refine Finset.noncommProd_congr rfl (fun o ho => ?_) _
  rw [windowEmbedding_apply]
  exact windowBlock_mixerFactor (windowEquiv j (P + 1) hP) o b

/-- **Mixer-factor block match over the depth-`P` window (post-flip convention).**
The full-chain mixer touching-product block over the depth-`P` window matches the
reduced-chain block: both equal the same chain-independent offset mixer product. -/
theorem mixer_factor_block_match_depthP {N : ℕ} (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (j_s : Fin N) (_hP' : 2 * P + 2 ≤ N) (b : ℝ) :
    windowBlock (windowEquiv j_s (P + 1) hP)
        (mixerTouchingProd (expand_by_n P (bondSeed j_s)) b) =
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (mixerTouchingProd (expand_by_n P
          (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) b) := by
  rw [windowBlock_mixerTouchingProd_depthP j_s P hP b,
      windowBlock_mixerTouchingProd_depthP (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) P (by omega) b]

-- ============================================================================
-- Section: cost touching-set offset characterization (no seam in the window)
-- ============================================================================

/-- **Window adjacency.** Inside the depth-`P+1` window, consecutive offsets are
adjacent sites: for an offset `o` with `o.val ≤ 2P+2`, the next chain site of
`windowEquiv j (P+1) o` is the window site at offset `nextSite o`. (The wrap-
around — the seam — only happens at the last offset `2P+3`, which is excluded.) -/
theorem nextSite_windowEquiv_succ {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (o : Fin (2 * (P + 1) + 2)) (ho : o.val ≤ 2 * P + 2) :
    IsingModel.nextSite ((windowEquiv j (P + 1) hP o : Fin N)) =
      (windowEquiv j (P + 1) hP (IsingModel.nextSite o) : Fin N) := by
  apply Fin.ext
  rw [windowEquiv_apply_val, windowEquiv_apply_val, IsingModel.nextSite_val]
  change ((j.val + (N - (P + 1)) + o.val) % N + 1) % N =
      (j.val + (N - (P + 1)) + (IsingModel.nextSite o).val) % N
  rw [IsingModel.nextSite_val]
  rw [show (o.val + 1) % (2 * (P + 1) + 2) = o.val + 1 from
      Nat.mod_eq_of_lt (by omega)]
  rw [Nat.add_mod ((j.val + (N - (P + 1)) + o.val) % N) 1 N, Nat.mod_mod,
      ← Nat.add_mod, Nat.add_assoc (j.val + (N - (P + 1))) o.val 1]

/-- The cost offset set: offsets `o` with `o.val ≤ 2P+2` (all window-internal
bonds; the wrap-around seam offset `2P+3` is excluded). -/
private def costOffsetSet (P : ℕ) : Finset (Fin (2 * (P + 1) + 2)) :=
  Finset.univ.filter (fun o => o.val ≤ 2 * P + 2)

/-- **Cost touching-set offset characterization.** The bonds touching the
depth-`P` window are exactly the window-internal bonds, parametrized by their
left endpoint's offset `o ∈ {0,…,2P+2}` (excluding the seam offset `2P+3`). As
a `Finset` of `Fin N`, the touching set equals the `windowEmbedding`-image of
the cost offset set. This holds identically on every chain length `N` — the
seam never enters because it does not touch the depth-`P` window. -/
theorem costTouching_eq_offset_image {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    (Finset.univ.filter (fun k : Fin N =>
        k ∈ expand_by_n P (bondSeed j) ∨
          IsingModel.nextSite k ∈ expand_by_n P (bondSeed j))) =
      (costOffsetSet P).map (windowEmbedding (windowEquiv j (P + 1) hP)) := by
  have hP' : 2 * P + 2 ≤ N := by omega
  classical
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    costOffsetSet, windowEmbedding_apply]
  constructor
  · -- A touching bond's left endpoint is a window site at an offset `≤ 2P+2`.
    rintro (hk | hnk)
    · -- `k ∈ W_P` : `k = εF o` for some offset `o`; show `o.val ≤ 2P+2`.
      have hkW1 : k ∈ expand_by_n (P + 1) (bondSeed j) :=
        expand_by_n_subset_succ P (bondSeed j) hk
      refine ⟨(windowEquiv j (P + 1) hP).symm ⟨k, hkW1⟩, ?_, ?_⟩
      · -- `o` indexes a `W_P` site, so it is an interior offset `1 ≤ o ≤ 2P+2`.
        by_contra hcon
        push_neg at hcon
        have hmem : (windowEquiv j (P + 1) hP
            ((windowEquiv j (P + 1) hP).symm ⟨k, hkW1⟩) : Fin N) ∈
            expand_by_n P (bondSeed j) := by
          rw [Equiv.apply_symm_apply]; exact hk
        rw [windowEquiv_succ_mem_depthP_iff] at hmem
        -- `hmem.2 : o ≠ 2P+3`; combined with `hcon : o > 2P+2` gives a contradiction.
        omega
      · rw [Equiv.apply_symm_apply]
    · -- `nextSite k ∈ W_P` : `k` is `prevSite` of a `W_P` site, also in `W_{P+1}`.
      have hkW1 : k ∈ expand_by_n (P + 1) (bondSeed j) := by
        rw [expand_by_n_succ]
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_image]
        exact ⟨IsingModel.nextSite k, hnk, prevSite_nextSite k⟩
      -- Obtain the offset `o` of `k` and clear `k` to avoid dependent rewrites.
      set o := (windowEquiv j (P + 1) hP).symm ⟨k, hkW1⟩ with ho_def
      have hko : (windowEquiv j (P + 1) hP o : Fin N) = k := by
        rw [ho_def, Equiv.apply_symm_apply]
      refine ⟨o, ?_, hko⟩
      -- `nextSite (εF o) ∈ W_P`, so `o.val ≤ 2P+2` (else `o = 2P+3`, whose next
      -- site is exterior/wrapped and never lies in `W_P`).
      by_contra hcon
      push_neg at hcon
      have hoval : o.val = 2 * P + 3 := by have := o.isLt; omega
      -- `nextSite k ∈ W_P = cyclicInterval N j P`, so it is some interior offset.
      rw [expand_by_n_bondSeed_eq_cyclicInterval j P hP'] at hnk
      unfold cyclicInterval at hnk
      rw [Finset.mem_image] at hnk
      obtain ⟨i, hi, hival⟩ := hnk
      rw [Finset.mem_range] at hi
      -- The values: `nextSite k = (j + N-(P+1) + (2P+4)) % N` and the `W_P`
      -- point at offset `i` is `(j + N-P + i) % N`. These cannot coincide.
      have hkv : k.val = (j.val + (N - (P + 1)) + o.val) % N := by rw [← hko]; rfl
      have hN0 : 0 < N := by omega
      have hnkv : (IsingModel.nextSite k).val =
          (j.val + (N - (P + 1)) + (2 * P + 4)) % N := by
        rw [IsingModel.nextSite_val, hkv, hoval]
        rw [Nat.add_mod ((j.val + (N - (P + 1)) + (2 * P + 3)) % N) 1 N, Nat.mod_mod,
            ← Nat.add_mod, show j.val + (N - (P + 1)) + (2 * P + 3) + 1 =
              j.val + (N - (P + 1)) + (2 * P + 4) from by omega]
      -- `hival : (j + N-P + i) % N = nextSite k`.
      have hcontra : (j.val + (N - P) + i) % N =
          (j.val + (N - (P + 1)) + (2 * P + 4)) % N := by
        rw [← hnkv]; exact congrArg Fin.val hival
      -- The two affine shifts are `≡ mod N`. Their difference is
      -- `(2P+4) - 1 - i = 2P+3 - i ∈ [2, 2P+3]`, strictly between `0` and `N`,
      -- so they cannot be congruent mod `N`.
      have hjlt : j.val < N := j.isLt
      have hNP : N - P + P = N := Nat.sub_add_cancel (by omega)
      have hNP1 : N - (P + 1) + (P + 1) = N := Nat.sub_add_cancel (by omega)
      have hmodeq : (j.val + (N - (P + 1)) + (2 * P + 4)) ≡
          (j.val + (N - P) + i) [MOD N] := hcontra.symm
      have hle : j.val + (N - P) + i ≤ j.val + (N - (P + 1)) + (2 * P + 4) := by omega
      have hdvd : N ∣ ((j.val + (N - (P + 1)) + (2 * P + 4)) - (j.val + (N - P) + i)) :=
        (Nat.modEq_iff_dvd' hle).mp hmodeq.symm
      have hdiff : (j.val + (N - (P + 1)) + (2 * P + 4)) - (j.val + (N - P) + i) =
          2 * P + 3 - i := by omega
      rw [hdiff] at hdvd
      have hdle : 2 * P + 3 - i < N := by omega
      have hdpos : 0 < 2 * P + 3 - i := by omega
      exact absurd (Nat.le_of_dvd hdpos hdvd) (by omega)
  · -- Conversely, any window-internal bond `o ≤ 2P+2` touches `W_P`.
    rintro ⟨o, ho, hok⟩
    rw [← hok]
    -- The bond at offset `o ≤ 2P+2`: if `o ≥ 1` its left endpoint is in `W_P`;
    -- if `o = 0` its right endpoint `nextSite` (offset 1) is in `W_P`.
    by_cases ho0 : o.val = 0
    · -- offset 0: right endpoint at offset 1 ∈ W_P.
      right
      rw [nextSite_windowEquiv_succ j P hP o (by omega)]
      rw [windowEquiv_succ_mem_depthP_iff]
      rw [IsingModel.nextSite_val, ho0]
      refine ⟨?_, ?_⟩ <;> · rw [Nat.mod_eq_of_lt (by omega)]; omega
    · -- offset `1 ≤ o ≤ 2P+2`: left endpoint ∈ W_P.
      left
      rw [windowEquiv_succ_mem_depthP_iff]
      exact ⟨ho0, by omega⟩

/-- **`windowBlock` of `costTouchingProd` is the offset cost product.** For the
depth-`P` window `W_P` of a bond seed at `j`, the depth-`P+1` window block of the
cost touching-product over `W_P` equals the `noncommProd` over the cost offset
set (`{o : o.val ≤ 2P+2}`) of the offset cost factors
`exp(-iγ chainPairInteraction o)` — entirely chain-independent. The PBC seam
never enters: it does not touch `W_P`. -/
theorem windowBlock_costTouchingProd {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (g : ℝ) :
    windowBlock (windowEquiv j (P + 1) hP)
        (costTouchingProd (expand_by_n P (bondSeed j)) g) =
      (costOffsetSet P).noncommProd
        (fun o => NormedSpace.exp ((((-g : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction o))
        (fun i _ j' _ _ =>
          (chainPairInteractions_commute i j').smul_left _ |>.smul_right _ |>.exp) := by
  classical
  have hP' : 2 * P + 2 ≤ N := by omega
  unfold costTouchingProd
  set W := expand_by_n (P + 1) (bondSeed j) with hW_def
  -- Each touching bond is supported on the depth-`P+1` window `W`.
  have hsupp : ∀ k ∈ (Finset.univ.filter (fun k : Fin N =>
        k ∈ expand_by_n P (bondSeed j) ∨
          IsingModel.nextSite k ∈ expand_by_n P (bondSeed j))),
      tensorSupportedOn W
        (NormedSpace.exp ((((-g : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    -- `k` and `nextSite k` are both in `W = expand_by_one (expand_by_n P …)`.
    have hkW : k ∈ W := by
      rcases hk.2 with hkin | hnk
      · exact expand_by_n_subset_succ P (bondSeed j) hkin
      · rw [hW_def, expand_by_n_succ]
        refine Finset.mem_union_right _ ?_
        rw [Finset.mem_image]
        exact ⟨IsingModel.nextSite k, hnk, prevSite_nextSite k⟩
    have hnkW : IsingModel.nextSite k ∈ W := by
      rcases hk.2 with hkin | hnk
      · rw [hW_def, expand_by_n_succ]
        refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
        rw [Finset.mem_image]
        exact ⟨k, hkin, rfl⟩
      · exact expand_by_n_subset_succ P (bondSeed j) hnk
    refine tensorSupportedOn_mono
      (S := ({k} : Finset (Fin N)) ∪ ({IsingModel.nextSite k} : Finset (Fin N))) ?_
      (tensorSupportedOn_exp_chainPairInteraction g k)
    intro x hx
    rw [Finset.mem_union, Finset.mem_singleton, Finset.mem_singleton] at hx
    rcases hx with hx | hx <;> · rw [hx]; assumption
  -- Push the block through the product, reindex to offsets, match per-offset.
  rw [windowBlock_noncommProd (windowEquiv j (P + 1) hP) _ _ _ hsupp]
  rw [Finset.noncommProd_congr (costTouching_eq_offset_image j P hP)
        (fun _ _ => rfl)]
  rw [noncommProd_map_embedding (windowEmbedding (windowEquiv j (P + 1) hP))
        (costOffsetSet P)]
  refine Finset.noncommProd_congr rfl (fun o ho => ?_) _
  rw [windowEmbedding_apply]
  -- Per-offset cost factor block; adjacency holds since `o.val ≤ 2P+2`.
  rw [costOffsetSet, Finset.mem_filter] at ho
  exact windowBlock_costFactor (windowEquiv j (P + 1) hP) o
    (nextSite_windowEquiv_succ j P hP o ho.2) g

/-- **Cost-factor block match (FGG §III edge analysis, incl. PBC seam).** The
window block of the full-chain cost touching-product over the depth-`P` window
matches the reduced-chain cost touching-product block. Each cost bond
`exp(-iγ cP(k))` touching the window maps to the reduced-chain bond at the
bijected position; the reduced PBC seam bond `cP(2P+3)` (= `Z_{2P+3} Z_0`) never
touches the depth-`P` window, so it never enters the touching product
(confirmed numerically). -/
theorem cost_factor_block_match {N : ℕ} (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (j_s : Fin N) (_hP' : 2 * P + 2 ≤ N) (g : ℝ) :
    windowBlock (windowEquiv j_s (P + 1) hP)
        (costTouchingProd (expand_by_n P (bondSeed j_s)) g) =
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (costTouchingProd (expand_by_n P
          (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) g) := by
  rw [windowBlock_costTouchingProd j_s P hP g,
      windowBlock_costTouchingProd (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) P (by omega) g]

/-- **Window-block layer match (inductive step, piece (ii)).** Given the
depth-`P` window-BLOCK equality of the full- and reduced-chain QAOA conjugates
at *every* chain length (`ih`), the depth-`P+1` window-block equality holds.
Both sides expand by `windowBlock_qaoaConjugate_succ` into the product of five
tight layer-factor blocks; the middle factor is discharged by `ih` at `N`
(full → reduced `2P+2`) and at `2P+4` (reduced `2P+4` → reduced `2P+2`), each
after the nested-window restriction to the depth-`P` window, and the cost/mixer
touching-product factors match across `Fin N ↔ Fin (2P+4)` — the genuine FGG
§III edge analysis (including the PBC seam bond, which acts trivially on the
window block).

Source: FGG arXiv:1411.4028v1 §III. -/
theorem canonical_windowBlock_match_succ {N : ℕ} (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) (γ β : Fin (P + 1) → ℝ) (j_s : Fin N)
    (hP' : 2 * P + 2 ≤ N)
    (ih : ∀ {N' : ℕ} (hP'' : 2 * P + 2 ≤ N') (γ' β' : Fin P → ℝ) (j' : Fin N'),
      windowBlock (windowEquiv j' P hP'') (fullChainQAOAConj P γ' β' j') =
        windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))
          (reducedChainQAOAConj P γ' β')) :
    windowBlock (windowEquiv j_s (P + 1) hP) (fullChainQAOAConj (P + 1) γ β j_s) =
      windowBlock
        (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (reducedChainQAOAConj (P + 1) γ β) := by
  -- The two depth-`P` block hypotheses for the middle factor: full chain at `N`
  -- and reduced chain at `2P+4` (both via `ih`).
  have hblockF := ih hP' (fun i => γ i.castSucc) (fun i => β i.castSucc) j_s
  have hblockR := ih (show 2 * P + 2 ≤ 2 * (P + 1) + 2 by omega)
    (fun i => γ i.castSucc) (fun i => β i.castSucc)
    (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2))
  -- Push the window block through one QAOA layer on both sides, factor by
  -- factor, via the dimension-stable block recursion.
  unfold fullChainQAOAConj reducedChainQAOAConj
  rw [windowBlock_qaoaConjugate_succ P (windowEquiv j_s (P + 1) hP)
        (tensorSupportedOn_chainPairInteraction j_s) γ β,
      windowBlock_qaoaConjugate_succ P
        (windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega))
        (tensorSupportedOn_chainPairInteraction _) γ β]
  -- Match factor by factor: the two outer mixer blocks, the two cost blocks,
  -- and the middle depth-`P` conjugate block.
  set εF := windowEquiv j_s (P + 1) hP with hεF
  set εR := windowEquiv (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)) (P + 1) (by omega) with hεR
  -- (3) middle: the depth-`P` conjugate block, via nested-window restriction
  -- (piece (i)) reducing the depth-`P+1` block to the depth-`P` block (`hblock`).
  have hmid :
      windowBlock εF
          (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
            (IsingModel.chainPairInteraction j_s)) =
        windowBlock εR
          (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
            (IsingModel.chainPairInteraction (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) :=
    middle_factor_block_match P hP γ β j_s hP' hblockF hblockR
  -- (1)(5) mixer blocks; (2)(4) cost blocks: the FGG §III generator block-match.
  have hmixerP :
      windowBlock εF
          (mixerTouchingProd (expand_by_n P (bondSeed j_s))
            (β (Fin.last P))) =
        windowBlock εR
          (mixerTouchingProd (expand_by_n P
            (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) (β (Fin.last P))) :=
    mixer_factor_block_match_depthP P hP j_s hP' (β (Fin.last P))
  have hmixerM :
      windowBlock εF
          (mixerTouchingProd (expand_by_n P (bondSeed j_s))
            (-β (Fin.last P))) =
        windowBlock εR
          (mixerTouchingProd (expand_by_n P
            (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) (-β (Fin.last P))) :=
    mixer_factor_block_match_depthP P hP j_s hP' (-β (Fin.last P))
  have hcostP :
      windowBlock εF
          (costTouchingProd (expand_by_n P (bondSeed j_s)) (γ (Fin.last P))) =
        windowBlock εR
          (costTouchingProd (expand_by_n P
            (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) (γ (Fin.last P))) :=
    cost_factor_block_match P hP j_s hP' (γ (Fin.last P))
  have hcostM :
      windowBlock εF
          (costTouchingProd (expand_by_n P (bondSeed j_s)) (-γ (Fin.last P))) =
        windowBlock εR
          (costTouchingProd (expand_by_n P
            (bondSeed (⟨0, by omega⟩ : Fin (2 * (P + 1) + 2)))) (-γ (Fin.last P))) :=
    cost_factor_block_match P hP j_s hP' (-γ (Fin.last P))
  rw [hmixerP, hmixerM, hcostP, hcostM, hmid]

-- ============================================================================
-- Section: window-block match (FGG light-cone theorem, block form, N-general)
-- ============================================================================

/-- **The FGG light-cone window-BLOCK match (N-general).**

The depth-`P` full-chain QAOA-conjugated bond block equals the reduced-chain
(PBC) QAOA-conjugated bond block at bond `0`, under the canonical window
equivalences — for *every* chain length `N` with `2P+2 ≤ N`. The `N`-generality
is essential: the inductive step's middle factor invokes this lemma both at the
ambient `N` and at the reduced length `2P+4`.

Proved by induction on `P`: the base case `P = 0` is the diagonal bare-bond
block match; the step is `canonical_windowBlock_match_succ` (piece (i) + (ii)),
fed the depth-`P` block match at all lengths via the induction hypothesis.

Source: FGG arXiv:1411.4028v1 §III. -/
theorem canonical_windowBlock_match {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) (j_s : Fin N) :
    windowBlock (windowEquiv j_s P hP) (fullChainQAOAConj P γ β j_s) =
      windowBlock (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))
        (reducedChainQAOAConj P γ β) := by
  induction P generalizing N with
  | zero =>
    -- Base case: bare bond block match. Funext the block, unfold to a restricted
    -- matrix entry, and run the diagonal calculus on arbitrary window data.
    funext a b
    unfold windowBlock
    set zs := windowData (windowEquiv j_s 0 hP) a with hzs_def
    set ws := windowData (windowEquiv j_s 0 hP) b with hws_def
    set zs' := windowData (windowEquiv (⟨0, by omega⟩ : Fin 2) 0 (by omega)) a with hzs'_def
    set ws' := windowData (windowEquiv (⟨0, by omega⟩ : Fin 2) 0 (by omega)) b with hws'_def
    -- The reduced-side window data agree with the canonical reindexing of the
    -- full-side data: `windowData εR a = windowData εF a ∘ e.symm`.
    have hzsR : zs' = (fun k => zs ((canonicalWindowEquiv j_s 0 hP).symm k)) := by
      funext k
      rw [hzs'_def, hzs_def]
      show windowData (windowEquiv (⟨0, by omega⟩ : Fin 2) 0 (by omega)) a k =
        windowData (windowEquiv j_s 0 hP) a ((canonicalWindowEquiv j_s 0 hP).symm k)
      unfold windowData canonicalWindowEquiv
      rw [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    have hwsR : ws' = (fun k => ws ((canonicalWindowEquiv j_s 0 hP).symm k)) := by
      funext k
      rw [hws'_def, hws_def]
      show windowData (windowEquiv (⟨0, by omega⟩ : Fin 2) 0 (by omega)) b k =
        windowData (windowEquiv j_s 0 hP) b ((canonicalWindowEquiv j_s 0 hP).symm k)
      unfold windowData canonicalWindowEquiv
      rw [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
    rw [hzsR, hwsR]
    -- Now exactly the matrix-entry base case at `zs, ws`.
    have hj_mem : j_s ∈ expand_by_n 0 (bondSeed j_s) := by
      rw [expand_by_n_zero]; exact self_mem_bondSeed j_s
    have hnj_mem : IsingModel.nextSite j_s ∈ expand_by_n 0 (bondSeed j_s) := by
      rw [expand_by_n_zero]; exact nextSite_mem_bondSeed j_s
    set zr : Fin 2 := ⟨0, by omega⟩ with hzr
    have h0_mem : zr ∈ expand_by_n 0 (bondSeed zr) := by
      rw [expand_by_n_zero]; exact self_mem_bondSeed zr
    have hn0_mem : IsingModel.nextSite zr ∈ expand_by_n 0 (bondSeed zr) := by
      rw [expand_by_n_zero]; exact nextSite_mem_bondSeed zr
    -- Unfold both conjugates to the bare bond observable.
    rw [show fullChainQAOAConj 0 γ β j_s = IsingModel.chainPairInteraction j_s from rfl,
        show reducedChainQAOAConj 0 γ β = IsingModel.chainPairInteraction zr from rfl]
    rw [restrictedMatrixEntry_chainPairInteraction _ j_s hj_mem hnj_mem zs ws,
        restrictedMatrixEntry_chainPairInteraction _ zr h0_mem hn0_mem _ _]
    -- e maps the full window's `j_s`/`nextSite j_s` to the reduced `0`/`1`.
    -- Show: `e.symm ⟨zr⟩ = ⟨j_s⟩` and `e.symm ⟨nextSite zr⟩ = ⟨nextSite j_s⟩`.
    have he0 : (canonicalWindowEquiv j_s 0 hP).symm ⟨zr, h0_mem⟩ = ⟨j_s, hj_mem⟩ := by
      have hval : windowEquiv (zr) 0 (by omega) (0 : Fin 2) = ⟨zr, h0_mem⟩ := by
        apply Subtype.ext
        rw [windowEquiv_apply_val]
        apply Fin.ext
        change (zr.val + (2 - 0) + (0 : Fin 2).val) % 2 = zr.val
        simp [hzr]
      have hfull : windowEquiv j_s 0 hP (0 : Fin 2) = ⟨j_s, hj_mem⟩ := by
        apply Subtype.ext
        rw [windowEquiv_apply_val]
        apply Fin.ext
        change (j_s.val + (N - 0) + (0 : Fin 2).val) % N = j_s.val
        have hcast : (0 : Fin 2).val = 0 := rfl
        have : j_s.val + (N - 0) + (0 : Fin 2).val = j_s.val + N := by rw [hcast]; omega
        rw [this, Nat.add_mod_right]; exact Nat.mod_eq_of_lt j_s.isLt
      rw [← hval, canonicalWindowEquiv_symm_windowEquiv, hfull]
    have he1 : (canonicalWindowEquiv j_s 0 hP).symm ⟨IsingModel.nextSite zr, hn0_mem⟩ =
        ⟨IsingModel.nextSite j_s, hnj_mem⟩ := by
      have hval : windowEquiv (zr) 0 (by omega) (1 : Fin 2) = ⟨IsingModel.nextSite zr, hn0_mem⟩ := by
        apply Subtype.ext
        rw [windowEquiv_apply_val]
        apply Fin.ext
        rw [IsingModel.nextSite_val]
        change (zr.val + (2 - 0) + (1 : Fin 2).val) % 2 = (zr.val + 1) % 2
        simp [hzr]
      have hfull : windowEquiv j_s 0 hP (1 : Fin 2) = ⟨IsingModel.nextSite j_s, hnj_mem⟩ := by
        apply Subtype.ext
        rw [windowEquiv_apply_val]
        apply Fin.ext
        rw [IsingModel.nextSite_val]
        change (j_s.val + (N - 0) + (1 : Fin 2).val) % N = (j_s.val + 1) % N
        have hcast : (1 : Fin 2).val = 1 := rfl
        have : j_s.val + (N - 0) + (1 : Fin 2).val = (j_s.val + 1) + N := by rw [hcast]; omega
        rw [this, Nat.add_mod_right]
      rw [← hval, canonicalWindowEquiv_symm_windowEquiv, hfull]
    -- Rewrite the reduced-side spin arguments and diagonal condition.
    simp only [he0, he1]
    -- Diagonal conditions: both reduce to `zs = ws` via `extendByZeroOnS_eq_iff`
    -- (full side) and the reindexed bijection (reduced side).
    simp only [extendByZeroOnS_eq_iff]
    -- Now: (if zs = ws then s·s else 0) = (if (zs∘e.symm) = (ws∘e.symm) then s·s else 0),
    -- with matching spin values by he0/he1.
    by_cases hd : zs = ws
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg ?_]
      intro hcontra
      apply hd
      funext x
      have := congrFun hcontra ((canonicalWindowEquiv j_s 0 hP) x)
      simpa using this
  | succ P ih =>
    -- Inductive step: discharge via the layer-match lemma, fed the N-general
    -- depth-`P` block match (`ih`) for both the full-chain and reduced-chain
    -- middle factors (piece (i) + (ii)).
    exact canonical_windowBlock_match_succ P hP γ β j_s (by omega)
      (fun {N'} hP'' γ' β' j' => ih hP'' γ' β' j')

-- ============================================================================
-- Section: matrix-entry matching (FGG light-cone theorem proper)
-- ============================================================================

/-- **The FGG light-cone matrix-entry match.**

For all window-restricted row/column data `zs ws`, the restricted matrix
entry of the full-chain QAOA-conjugated bond observable at `j_s` equals the
restricted matrix entry of the reduced-chain (PBC) QAOA-conjugated bond
observable at bond `0`, under the canonical window bijection.

Derived from the window-BLOCK match `canonical_windowBlock_match` by reading
both restricted entries as honest block entries at the canonical window
equivalences (`restrictedMatrixEntry_eq_windowBlock`) and matching the index
encodings through `canonicalWindowEquiv`.

Source: FGG arXiv:1411.4028v1 §III. -/
theorem canonical_matrix_entry_match {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) (j_s : Fin N)
    (zs ws : (expand_by_n P (bondSeed j_s)) → Fin 2) :
    restrictedMatrixEntry (expand_by_n P (bondSeed j_s))
        (fullChainQAOAConj P γ β j_s) zs ws =
      restrictedMatrixEntry
        (expand_by_n P (bondSeed (⟨0, by omega⟩ : Fin (2 * P + 2))))
        (reducedChainQAOAConj P γ β)
        (fun k => zs ((canonicalWindowEquiv j_s P hP).symm k))
        (fun k => ws ((canonicalWindowEquiv j_s P hP).symm k)) := by
  rw [restrictedMatrixEntry_eq_windowBlock (windowEquiv j_s P hP),
      restrictedMatrixEntry_eq_windowBlock
        (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega))]
  -- The reduced-side index encodings simplify to the full-side ones.
  have hidx : ∀ i : Fin (2 * P + 2),
      (canonicalWindowEquiv j_s P hP).symm
          (windowEquiv (⟨0, by omega⟩ : Fin (2 * P + 2)) P (by omega) i) =
        windowEquiv j_s P hP i := by
    intro i
    unfold canonicalWindowEquiv
    rw [Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  simp only [hidx]
  exact congrFun (congrFun (canonical_windowBlock_match P hP γ β j_s) _) _

-- ============================================================================
-- Section: the canonical inhabitant
-- ============================================================================

/-- **Canonical inhabitant of `LightconeStructuralMatching`.**

Assembles a term of `LightconeStructuralMatching P hP γ β j_s` for an
arbitrary interior bond `j_s` with `2*P+2 ≤ N`: the bijection field is the
canonical window equivalence `canonicalWindowEquiv` (sorry-free,
axiom-clean), and the matrix-entry field is the FGG light-cone match
`canonical_matrix_entry_match`.

This term is **sorry-free and axiom-clean** (`{propext, Classical.choice,
Quot.sound}`): both the structure and the two generator-block-match lemmas are
discharged.

Feeding this to `qaoa_full_eq_reduced_on_lightcone_closed` (and onward to
`qaoa_full_eq_reduced_on_lightcone_at`) discharges the chain-reduction
identity that the Path-1 closure of `bond_expectation_full_eq_reduced`
consumes.

Source: FGG arXiv:1411.4028v1 §III; arXiv:1906.08948v2 §IV l.620–678. -/
def lightconeStructuralMatching_canonical {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) (j_s : Fin N) :
    LightconeStructuralMatching P hP γ β j_s where
  e := canonicalWindowEquiv j_s P hP
  matrix_entry_match := canonical_matrix_entry_match P hP γ β j_s

end

end QAOA.IsingChain.UpperBound.LightCone
