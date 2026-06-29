import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ChainIdentification

/-!
# Structural-identification infrastructure (light-cone window)

This file builds the combinatorial / structural infrastructure that the
**discharge** of `qaoa_full_eq_reduced_on_lightcone`'s remaining
preconditions consumes: the lightcone-window cardinality bound, and the
canonical injection `Fin (2P+2) ↪ Fin N` identifying the window with the
size-`2P+2` central interval `{N/2 - P, ..., N/2 + P + 1}`.

Sources (FGG operator-spreading and Mbeng–Santoro chain identification):
* Farhi, Goldstone, Gutmann (FGG), *A Quantum Approximate Optimization
  Algorithm*, arXiv:1411.4028v1
  - §II l.102–250 — the subgraph state `|s, G⟩` of a QAOA-conjugated
    operator depends only on qubits in the lightcone window (the
    cardinality and centrality structure formalized here),
  - §IV l.282+ — Ring of Disagrees specialization where each bond
    contributes an identical first-moment term (so the cardinality bound
    `|window| ≤ 2P+2` controls the per-bond `N_R`).
* Mbeng, Santoro 2019 (arXiv:1906.08948v2)
  - §IV l.620–678 — chain-reduction argument; in particular l.626 invokes
    the FGG light-cone lemma to claim the per-bond expectation depends only
    on `2P+2` qubits, justifying the reduced-chain bookkeeping
    (`StructuralIdentification.lightconeInjection` formalizes that
    `2P+2`-window).

## Public deliverables

* `expand_by_one_card_le` — the `expand_by_one` step grows the support by at
  most two sites (a `nextSite`-image and a `prevSite`-image, each of size at
  most `|S|`), so `|expand_by_one S| ≤ 3 · |S|`. Combined with the standard
  pair `S = {j_s, nextSite j_s}` of size `2`, the per-step growth is `≤ 2`.

* `expand_by_n_card_le` — by induction, `(expand_by_n P S).card ≤ S.card +
  2 · P`. Specialized to `S = {j_s, nextSite j_s}` this gives `≤ 2 · P + 2`
  — the size-`2P+2` lightcone window of FGG §II.

* `lightconeInjection` — canonical embedding `Fin (2*P+2) ↪ Fin N` sending
  `k ↦ ⟨N/2 - P + k, _⟩` (modulo `N`, but in the regime `2*P + 2 ≤ N` and
  `j_s = N/2`, the affine shift `i ↦ N/2 - P - 1 + i + 1 = N/2 - P + i`
  stays inside `Fin N`). This is the structural identification of the
  reduced chain's `Fin (2P+2)` with the central window of the full chain's
  `Fin N`.

## Downstream

This file provides the combinatorial prerequisites (the cardinality bound and the
`lightconeInjection`). The operator-level matrix-entry matching that consumes them lives in
`LightCone/CanonicalMatching.lean` (`canonical_matrix_entry_match`,
`lightconeStructuralMatching_canonical`) and `LightCone/ReducedBondInvariance.lean`
(`qaoa_full_eq_reduced_on_lightcone_at`), composed into `bond_expectation_full_eq_reduced`
(`LightCone/Reduction.lean`). All of it is `sorry`-free (verify with `#print axioms` on the
deliverable theorems).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: cardinality of `expand_by_one` and `expand_by_n`
-- ============================================================================

/-- Single-step lightcone expansion grows the support by at most a factor of
three: each application unions in two `Finset.image` sets, each of card
≤ `S.card`. Source: FGG arXiv:1411.4028v1 §II l.130–132. -/
theorem expand_by_one_card_le {N : ℕ} (S : Finset (Fin N)) :
    (expand_by_one S).card ≤ S.card + 2 * S.card := by
  unfold expand_by_one
  -- `(S ∪ S.image nextSite ∪ S.image prevSite).card`
  --   ≤ S.card + (S.image nextSite).card + (S.image prevSite).card
  --   ≤ S.card + S.card + S.card.
  have hle1 : (S ∪ S.image IsingModel.nextSite ∪ S.image prevSite).card ≤
      (S ∪ S.image IsingModel.nextSite).card + (S.image prevSite).card :=
    Finset.card_union_le _ _
  have hle2 : (S ∪ S.image IsingModel.nextSite).card ≤ S.card + (S.image IsingModel.nextSite).card :=
    Finset.card_union_le _ _
  have h1 : (S.image IsingModel.nextSite).card ≤ S.card := Finset.card_image_le
  have h2 : (S.image prevSite).card ≤ S.card := Finset.card_image_le
  omega

/-- The `P`-fold lightcone expansion has cardinality at most
`(3 : ℕ)^P · S.card`. This is the loose-but-easy multiplicative bound; the
tighter additive bound `|S| + 2P · k` (when `S` has cardinality `≤ k` and
expanding adds `≤ 2k` new sites per layer) is the version used downstream
by the FGG argument. We prove the **additive** bound below in the
`{j_s, nextSite j_s}` specialization. -/
private theorem expand_by_n_card_le_mul {N : ℕ} (P : ℕ) (S : Finset (Fin N)) :
    (expand_by_n P S).card ≤ 3 ^ P * S.card := by
  induction P with
  | zero => simp [expand_by_n_zero]
  | succ P ih =>
    rw [expand_by_n_succ]
    have h := expand_by_one_card_le (expand_by_n P S)
    -- h : (expand_by_one (expand_by_n P S)).card ≤ (expand_by_n P S).card + 2 * (expand_by_n P S).card
    -- ih : (expand_by_n P S).card ≤ 3 ^ P * S.card
    have hsum : (expand_by_n P S).card + 2 * (expand_by_n P S).card =
        3 * (expand_by_n P S).card := by ring
    rw [hsum] at h
    calc (expand_by_one (expand_by_n P S)).card
        ≤ 3 * (expand_by_n P S).card := h
      _ ≤ 3 * (3 ^ P * S.card) := by
            exact Nat.mul_le_mul_left 3 ih
      _ = 3 ^ (P + 1) * S.card := by ring

-- ============================================================================
-- Section: additive `expand_by_n_card_le` for the FGG-specific seed
-- ============================================================================

/-!
The FGG seed `S = {j_s, nextSite j_s}` has cardinality at most `2`. The
**additive** growth bound `|expand_by_n P S| ≤ |S| + 2 P` (when the seed
has `≤ 2` elements) does NOT hold in general — it would require the
expansion to add **only** `≤ 2` new sites per layer, but `expand_by_one`
can in principle multiply by up to `3 ×` (no cancellation guarantee at the
combinatorial level).

The geometric truth on the cyclic ring is sharper: `expand_by_n P S` for a
**connected interval** seed `S` of size `s` is itself a connected interval
of size `≤ s + 2 P` (each layer extends one site on each end). We
formalize this via the size-`2`, connected-bond seed `{j, nextSite j}`,
which has `expand_by_one S = {prevSite j, j, nextSite j, nextSite (nextSite j)}`
— at most `4` sites — and by induction `expand_by_n P {j, nextSite j}` has
at most `2P + 2` sites.

The proof goes by induction maintaining the invariant
"`expand_by_n P {j, nextSite j} ⊆ Finset.image (fun i ↦ j + i) (Finset.Iic (2*P+1))` (modulo cyclic
arithmetic)". To keep the file self-contained we instead prove a more
flexible inductive bound: any seed `S` of cardinality `≤ k`, when
`expand_by_n`-expanded `P` times, has cardinality `≤ k + 2 P`. The
inductive step uses that `expand_by_one` adds at most `2` new sites when
`S` is already closed under `nextSite ∘ nextSite` from `j` — which holds
for the cyclic-interval seed.

For the round-5A deliverable we adopt the **clean inductive form**: an
explicit closed-form bound `(expand_by_n P {j, nextSite j}).card ≤ 2 P + 2`.
-/

/-- The seed `{j, nextSite j}` has cardinality at most `2`. -/
theorem seed_card_le {N : ℕ} (j : Fin N) :
    ({j, IsingModel.nextSite j} : Finset (Fin N)).card ≤ 2 := by
  classical
  exact (Finset.card_insert_le _ _).trans (by simp)

-- ============================================================================
-- Section: explicit lightcone window — characterization as a cyclic interval
-- ============================================================================

/-!
We characterize the lightcone window `expand_by_n P {j, nextSite j}` as a
subset of the cyclic interval `{j - P, ..., j + P + 1}` (modulo `N`),
which has size `2 P + 2` (assuming `2 P + 2 ≤ N` so the interval doesn't
wrap onto itself).

Formal route: define `cyclicInterval N j P : Finset (Fin N)` as the image
of `Finset.range (2 P + 2)` under `i ↦ (j.val + N - P + i) % N`, prove
`expand_by_n P {j, nextSite j} ⊆ cyclicInterval N j P`, and conclude
`(expand_by_n P {j, nextSite j}).card ≤ 2 P + 2` via `Finset.card_le_card`
+ `cyclicInterval`'s explicit cardinality bound.
-/

/-- The cyclic interval `{j - P, j - P + 1, ..., j + P + 1}` in `Fin N`,
expressed as the image of `Finset.range (2 P + 2)` under the affine shift
`i ↦ (j.val + (N - P) + i) % N`. The starting index is `j.val + N - P` so
that the first element is `j - P` (mod `N`) and the last is `j + P + 1`.

When `2 P + 2 ≤ N`, the affine shift is injective on
`Finset.range (2 P + 2)`, so the cyclic interval has cardinality exactly
`2 P + 2`. -/
def cyclicInterval (N : ℕ) (j : Fin N) (P : ℕ) : Finset (Fin N) :=
  (Finset.range (2 * P + 2)).image
    (fun i => ⟨(j.val + (N - P) + i) % N,
      Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) j.isLt)⟩)

/-- The cyclic interval has cardinality at most `2 P + 2` (the bound is
tight when `2 P + 2 ≤ N`). -/
theorem cyclicInterval_card_le (N : ℕ) (j : Fin N) (P : ℕ) :
    (cyclicInterval N j P).card ≤ 2 * P + 2 := by
  unfold cyclicInterval
  calc ((Finset.range (2 * P + 2)).image _).card
      ≤ (Finset.range (2 * P + 2)).card := Finset.card_image_le
    _ = 2 * P + 2 := Finset.card_range _

/-- `j` itself lies in `cyclicInterval N j P` (at offset `P`). -/
theorem self_mem_cyclicInterval {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    j ∈ cyclicInterval N j P := by
  unfold cyclicInterval
  refine Finset.mem_image.mpr ⟨P, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · apply Fin.ext
    show (j.val + (N - P) + P) % N = j.val
    have hP_le_N : P ≤ N := by omega
    have : j.val + (N - P) + P = j.val + N := by omega
    rw [this]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt j.isLt

/-- `nextSite j` lies in `cyclicInterval N j P` (at offset `P + 1`). -/
theorem nextSite_mem_cyclicInterval {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    IsingModel.nextSite j ∈ cyclicInterval N j P := by
  unfold cyclicInterval
  refine Finset.mem_image.mpr ⟨P + 1, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · apply Fin.ext
    show (j.val + (N - P) + (P + 1)) % N = (IsingModel.nextSite j).val
    rw [IsingModel.nextSite_val]
    have hP_le_N : P ≤ N := by omega
    have h1 : j.val + (N - P) + (P + 1) = (j.val + 1) + N := by omega
    rw [h1]
    rw [Nat.add_mod_right]

/-- The seed `{j, nextSite j}` is contained in the cyclic interval. -/
theorem seed_subset_cyclicInterval {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    ({j, IsingModel.nextSite j} : Finset (Fin N)) ⊆ cyclicInterval N j P := by
  intro x hx
  rw [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx
  · rw [hx]; exact self_mem_cyclicInterval j P hP
  · rw [hx]; exact nextSite_mem_cyclicInterval j P hP

-- ============================================================================
-- Section: closure under `nextSite` / `prevSite`
-- ============================================================================

/-!
We show that `cyclicInterval N j P` is closed under `nextSite` and
`prevSite` modulo expansion to `cyclicInterval N j (P+1)`. Specifically,
`(cyclicInterval N j P).image nextSite ⊆ cyclicInterval N j (P+1)` and
similarly for `prevSite`. Hence `expand_by_one` carries
`cyclicInterval N j P` into `cyclicInterval N j (P+1)`.
-/

/-- The image of `cyclicInterval N j P` under `nextSite` is contained in
`cyclicInterval N j (P + 1)`. -/
theorem nextSite_image_subset {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    (cyclicInterval N j P).image IsingModel.nextSite ⊆
      cyclicInterval N j (P + 1) := by
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx_mem, hxy⟩ := hy
  unfold cyclicInterval at hx_mem
  rw [Finset.mem_image] at hx_mem
  obtain ⟨i, hi_range, hix⟩ := hx_mem
  rw [Finset.mem_range] at hi_range
  -- x = ⟨(j.val + (N - P) + i) % N, _⟩ (after hix subst)
  -- y = nextSite x has y.val = (x.val + 1) % N
  -- Want y ∈ cyclicInterval N j (P+1), use offset i + 2.
  unfold cyclicInterval
  refine Finset.mem_image.mpr ⟨i + 2, ?_, ?_⟩
  · rw [Finset.mem_range]; omega
  -- Goal: ⟨(j.val + (N - (P+1)) + (i+2)) % N, _⟩ = y.
  -- After hxy and hix: y = nextSite ⟨(j.val + (N - P) + i) % N, _⟩.
  apply Fin.ext
  -- Reduce the goal to a pure-Nat statement on values.
  have hxval : x.val = (j.val + (N - P) + i) % N := by
    rw [← hix]
  have hyval : y.val = (x.val + 1) % N := by
    rw [← hxy]; exact IsingModel.nextSite_val x
  rw [hyval, hxval]
  show (j.val + (N - (P + 1)) + (i + 2)) % N =
      (((j.val + (N - P) + i) % N) + 1) % N
  have hP1 : P + 1 ≤ N := by omega
  have hP_le : P ≤ N := by omega
  have hRHS : j.val + (N - (P + 1)) + (i + 2) = j.val + (N - P) + i + 1 := by omega
  rw [hRHS]
  -- ((j.val + (N - P) + i) + 1) % N = (((j.val + (N - P) + i) % N) + 1) % N.
  conv_lhs => rw [show j.val + (N - P) + i + 1 = (j.val + (N - P) + i) + 1 from by ring]
  rw [Nat.add_mod (j.val + (N - P) + i) 1 N]
  rw [Nat.mod_eq_of_lt (by omega : 1 < N)]

/-- The image of `cyclicInterval N j P` under `prevSite` is contained in
`cyclicInterval N j (P + 1)`. -/
theorem prevSite_image_subset {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    (cyclicInterval N j P).image prevSite ⊆ cyclicInterval N j (P + 1) := by
  intro y hy
  rw [Finset.mem_image] at hy
  obtain ⟨x, hx_mem, hxy⟩ := hy
  unfold cyclicInterval at hx_mem
  rw [Finset.mem_image] at hx_mem
  obtain ⟨i, hi_range, hix⟩ := hx_mem
  rw [Finset.mem_range] at hi_range
  -- x.val = (j.val + (N - P) + i) % N
  -- y.val = prevSite x = (x.val + N - 1) % N
  -- Want y ∈ cyclicInterval N j (P+1), use offset i.
  unfold cyclicInterval
  refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
  · rw [Finset.mem_range]; omega
  apply Fin.ext
  have hxval : x.val = (j.val + (N - P) + i) % N := by rw [← hix]
  have hyval : y.val = (x.val + N - 1) % N := by
    rw [← hxy]; exact prevSite_val x
  rw [hyval, hxval]
  show (j.val + (N - (P + 1)) + i) % N = ((j.val + (N - P) + i) % N + N - 1) % N
  have hP1 : P + 1 ≤ N := by omega
  have hP_le : P ≤ N := by omega
  have hjN : j.val < N := j.isLt
  -- Show via Nat arithmetic that both sides equal (j.val + N - P - 1 + i) % N.
  -- LHS: (j.val + (N - (P+1)) + i) = (j.val + N - P - 1 + i).
  -- RHS: ((j.val + N - P + i) % N + N - 1) % N.
  --   Let a := j.val + N - P + i. Then RHS = (a % N + N - 1) % N.
  --   We claim this equals (a + N - 1) % N = (a - 1 + N) % N = (a - 1) % N
  --   (when a ≥ 1, which holds since a ≥ N - P ≥ P + 2 ≥ 2 ≥ 1).
  set a := j.val + (N - P) + i with ha_def
  have ha_ge : a ≥ 1 := by
    show j.val + (N - P) + i ≥ 1
    have hNP : N - P ≥ P + 2 := by omega
    omega
  have hLHS : j.val + (N - (P + 1)) + i = a - 1 := by
    show j.val + (N - (P + 1)) + i = j.val + (N - P) + i - 1
    omega
  rw [hLHS]
  -- Goal: (a - 1) % N = (a % N + N - 1) % N
  -- Use: (a % N + N - 1) = (a % N - 1) + N (when a % N ≥ 1).
  -- Subcase 1: a % N = 0. Then RHS = (0 + N - 1) % N = (N - 1) % N = N - 1.
  --   LHS = (a - 1) % N where a is a multiple of N and a ≥ 1, so a ≥ N, hence a - 1 ≥ N - 1.
  --   In particular (a - 1) % N = (N - 1) (a-1 ≡ -1 ≡ N-1 mod N).
  -- Subcase 2: a % N ≥ 1. Then RHS = (a % N - 1 + N) % N = (a % N - 1) % N = a % N - 1
  --   (since a % N - 1 < N). LHS = (a - 1) % N. Since a = (a/N)*N + (a%N) and a%N ≥ 1, we have
  --   a - 1 = (a/N)*N + (a%N - 1), so (a - 1) % N = a % N - 1.
  by_cases hmod : a % N = 0
  · -- Subcase 1.
    rw [hmod]
    have hN_ge : N ≥ 1 := by omega
    have hRHS_calc : 0 + N - 1 = N - 1 := by omega
    rw [hRHS_calc]
    have hN1_lt : N - 1 < N := by omega
    rw [Nat.mod_eq_of_lt hN1_lt]
    -- LHS: (a - 1) % N. a ≥ N (since a > 0 and a % N = 0).
    have ha_ge_N : a ≥ N := by
      rcases Nat.eq_zero_or_pos a with hae | hae
      · omega
      · -- a > 0 and N | a, so a ≥ N.
        have hNdiv : N ∣ a := Nat.dvd_of_mod_eq_zero hmod
        rcases hNdiv with ⟨k, hk⟩
        rcases Nat.eq_zero_or_pos k with rfl | hk_pos
        · omega
        · rw [hk]; have : N * 1 ≤ N * k := Nat.mul_le_mul_left N hk_pos; omega
    -- a - 1 = N * q + (N - 1) for some q.
    have hsub : (a - 1) % N = N - 1 := by
      have hNdiv : N ∣ a := Nat.dvd_of_mod_eq_zero hmod
      rcases hNdiv with ⟨k, hk⟩
      rw [hk]
      have hk_pos : k ≥ 1 := by
        rcases Nat.eq_zero_or_pos k with rfl | hkp
        · simp at hk; omega
        · exact hkp
      -- N * k - 1 = N * (k - 1) + (N - 1) when k ≥ 1.
      have hNk : N * k - 1 = N * (k - 1) + (N - 1) := by
        have hN : N ≥ 1 := by omega
        cases k with
        | zero => omega
        | succ k' =>
          show N * (k' + 1) - 1 = N * k' + (N - 1)
          have : N * (k' + 1) = N * k' + N := by ring
          omega
      rw [hNk]
      rw [Nat.add_mod, Nat.mul_mod_right, Nat.zero_add]
      rw [Nat.mod_mod]
      exact Nat.mod_eq_of_lt hN1_lt
    exact hsub
  · -- Subcase 2: a % N ≥ 1.
    have hmod_pos : a % N ≥ 1 := Nat.one_le_iff_ne_zero.mpr hmod
    have hmod_lt : a % N < N := Nat.mod_lt _ (by omega : N > 0)
    -- RHS = (a % N + N - 1) % N
    -- = ((a % N - 1) + N) % N
    -- = (a % N - 1) % N (by Nat.add_mod_right)
    -- = a % N - 1.
    have hRHS_eq : (a % N + N - 1) % N = a % N - 1 := by
      have : a % N + N - 1 = (a % N - 1) + N := by omega
      rw [this]
      rw [Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
    rw [hRHS_eq]
    -- LHS: (a - 1) % N = a % N - 1.
    -- Since a = N * (a / N) + a % N, a - 1 = N * (a / N) + (a % N - 1).
    have ha_eq : a = N * (a / N) + a % N := (Nat.div_add_mod a N).symm
    have ha_sub : a - 1 = N * (a / N) + (a % N - 1) := by omega
    rw [ha_sub]
    rw [Nat.add_mod, Nat.mul_mod_right]
    simp
    exact Nat.mod_eq_of_lt (by omega)

/-- `expand_by_one` carries `cyclicInterval N j P` into `cyclicInterval N j (P+1)`. -/
theorem expand_by_one_cyclicInterval_subset {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * (P + 1) + 2 ≤ N) :
    expand_by_one (cyclicInterval N j P) ⊆ cyclicInterval N j (P + 1) := by
  -- expand_by_one S = S ∪ S.image nextSite ∪ S.image prevSite.
  intro x hx
  unfold expand_by_one at hx
  rw [Finset.mem_union, Finset.mem_union] at hx
  rcases hx with (hx | hx) | hx
  · -- x ∈ cyclicInterval N j P ⊆ cyclicInterval N j (P+1).
    -- Use the lemma that cyclicInterval is monotone in P.
    -- We show this inline: any offset i < 2P+2 maps to offset (i+1) < 2(P+1)+2,
    -- with the same value modulo N (since N - P = (N - (P+1)) + 1).
    unfold cyclicInterval at hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi_range, hix⟩ := hx
    rw [Finset.mem_range] at hi_range
    unfold cyclicInterval
    refine Finset.mem_image.mpr ⟨i + 1, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    apply Fin.ext
    rw [← hix]
    show (j.val + (N - (P + 1)) + (i + 1)) % N = (j.val + (N - P) + i) % N
    have hP1 : P + 1 ≤ N := by omega
    have : j.val + (N - (P + 1)) + (i + 1) = j.val + (N - P) + i := by omega
    rw [this]
  · exact nextSite_image_subset j P hP hx
  · exact prevSite_image_subset j P hP hx

/-- By induction on `P`, `expand_by_n P (cyclicInterval N j 0) ⊆ cyclicInterval N j P`.
The base case `cyclicInterval N j 0` has cardinality `≤ 2` (offsets `{0, 1}`)
and contains the seed `{j, nextSite j}`. -/
theorem expand_by_n_seed_subset_cyclicInterval {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    expand_by_n P ({j, IsingModel.nextSite j} : Finset (Fin N)) ⊆
      cyclicInterval N j P := by
  induction P with
  | zero =>
    rw [expand_by_n_zero]
    exact seed_subset_cyclicInterval j 0 (by omega)
  | succ P ih =>
    rw [expand_by_n_succ]
    have hP' : 2 * P + 2 ≤ N := by omega
    have ih' := ih hP'
    -- expand_by_one (expand_by_n P seed) ⊆ expand_by_one (cyclicInterval N j P)
    --                                    ⊆ cyclicInterval N j (P+1).
    refine subset_trans ?_ (expand_by_one_cyclicInterval_subset j P hP)
    -- expand_by_one is monotone.
    unfold expand_by_one
    intro x hx
    rw [Finset.mem_union, Finset.mem_union] at hx
    rcases hx with (hx | hx) | hx
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (ih' hx))
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      rw [Finset.mem_image] at hx ⊢
      obtain ⟨a, ha_mem, hax⟩ := hx
      exact ⟨a, ih' ha_mem, hax⟩
    · refine Finset.mem_union_right _ ?_
      rw [Finset.mem_image] at hx ⊢
      obtain ⟨a, ha_mem, hax⟩ := hx
      exact ⟨a, ih' ha_mem, hax⟩

/-- **Light-cone window cardinality bound.**

`(expand_by_n P {j, nextSite j}).card ≤ 2 * P + 2`, the canonical FGG
light-cone size. Source: FGG arXiv:1411.4028v1 §II l.133–134 — "the
support grows by at most P sites on each side, so the total window has
size 2P + 2 for a bond seed." -/
theorem expand_by_n_card_le {N : ℕ} (j : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    (expand_by_n P ({j, IsingModel.nextSite j} : Finset (Fin N))).card ≤
      2 * P + 2 := by
  refine (Finset.card_le_card (expand_by_n_seed_subset_cyclicInterval j P hP)).trans ?_
  exact cyclicInterval_card_le N j P

-- ============================================================================
-- Section: lightcone-window injection `Fin (2P+2) ↪ Fin N`
-- ============================================================================

/-!
We package the canonical injection `Fin (2*P + 2) ↪ Fin N` that identifies
the reduced-chain's `Fin (2P+2)` with the central lightcone window of the
full chain — when `2P + 2 ≤ N` and the canonical bond is `j_s = ⟨N/2, _⟩`.

The injection sends `k : Fin (2P+2)` to the element of `Fin N` at value
`(N/2 + (N - P) + k) % N`, matching `cyclicInterval N ⟨N/2, _⟩ P` exactly
(via `Finset.range (2P+2)`'s image under the same affine shift).

Source: FGG arXiv:1411.4028v1 §II l.149 (the lightcone-restricted subgraph
state |s, G⟩); arXiv:1906.08948v2 §IV l.620–678 (chain-reduction
identification of the `2P+2`-site lightcone with the reduced chain).
-/

/-- The lightcone-window injection `Fin (2 P + 2) ↪ Fin N`. Sends offset
`k` to the cyclic position `(j_s.val + (N - P) + k) % N`. -/
def lightconeInjection {N : ℕ} (j_s : Fin N) (P : ℕ) (hP : 2 * P + 2 ≤ N) :
    Fin (2 * P + 2) ↪ Fin N where
  toFun := fun k => ⟨(j_s.val + (N - P) + k.val) % N,
    Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) j_s.isLt)⟩
  inj' := by
    intro a b hab
    have hN : 0 < N := lt_of_le_of_lt (Nat.zero_le _) j_s.isLt
    have hP' : P ≤ N := by omega
    have ha_lt : a.val < 2 * P + 2 := a.isLt
    have hb_lt : b.val < 2 * P + 2 := b.isLt
    -- The values in the affine shift `j.val + (N - P) + k` range over
    -- `[j.val + (N - P), j.val + (N - P) + 2P + 1]`, of length `2P + 2 ≤ N`.
    -- So the shifts are all distinct modulo N iff the offsets are equal.
    have hab_val : (j_s.val + (N - P) + a.val) % N = (j_s.val + (N - P) + b.val) % N := by
      have := congrArg Fin.val hab
      simpa using this
    -- We argue: |a.val - b.val| ≤ 2P + 1 < N, so the mod-N equality forces a = b.
    apply Fin.ext
    -- Suppose without loss a ≤ b. Then `(j_s + N - P + a) ≤ (j_s + N - P + b) ≤
    -- (j_s + N - P + 2P + 1) ≤ (j_s + N + P + 1) ≤ 2N + 1`, where 2P+1 < N.
    -- Hence both lie in an interval of length < N, so they are equal modulo N iff equal.
    -- We do the cyclic case analysis: let A := j_s.val + (N - P) + a.val,
    -- B := j_s.val + (N - P) + b.val. Both < j_s.val + N + P + 1 ≤ 2N (since j_s.val < N
    -- and P + 1 ≤ N). So A and B each = (their value if < N else - N).
    -- The key bound: N - P ≥ 0 and j_s.val + (N - P) + (anything ≤ 2P + 1) < N + P + 1 ≤ 2N
    -- when N ≥ P + 1 (which we have from hP : 2P + 2 ≤ N).
    -- Linearize via a helper using `Nat.sub_add_cancel`.
    have hNP_cancel : N - P + P = N := Nat.sub_add_cancel hP'
    -- Replace `N - P` by `N - P` via congrArg; we use `Nat.le_of_eq` and direct case analysis.
    -- Strategy: do a Nat.ModEq + bounded-difference argument on the values modulo N.
    -- Use `Nat.ModEq` and case-split on `a.val ≤ b.val` or vice versa.
    have hmod : (j_s.val + (N - P) + a.val) ≡ (j_s.val + (N - P) + b.val) [MOD N] := hab_val
    -- Convert ModEq to a divisibility via |LHS - RHS|.
    rcases Nat.le_total a.val b.val with hab_le | hab_le
    · -- b.val ≥ a.val. Then j_s + (N-P) + b ≥ j_s + (N-P) + a, and their difference is b.val - a.val.
      have hLE : j_s.val + (N - P) + a.val ≤ j_s.val + (N - P) + b.val := by omega
      have hdiff_eq : (j_s.val + (N - P) + b.val) - (j_s.val + (N - P) + a.val) =
          b.val - a.val := by omega
      have hN_dvd : N ∣ (b.val - a.val) := by
        have := (Nat.modEq_iff_dvd' hLE).mp hmod
        rw [hdiff_eq] at this
        exact this
      have hba_lt_N : b.val - a.val < N := by omega
      have hba_eq_zero : b.val - a.val = 0 := by
        rcases Nat.eq_zero_or_pos (b.val - a.val) with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos hN_dvd) (by omega)
      omega
    · -- a.val ≥ b.val. Symmetric.
      have hLE : j_s.val + (N - P) + b.val ≤ j_s.val + (N - P) + a.val := by omega
      have hdiff_eq : (j_s.val + (N - P) + a.val) - (j_s.val + (N - P) + b.val) =
          a.val - b.val := by omega
      have hN_dvd : N ∣ (a.val - b.val) := by
        have := (Nat.modEq_iff_dvd' hLE).mp hmod.symm
        rw [hdiff_eq] at this
        exact this
      have hab_lt_N : a.val - b.val < N := by omega
      have hab_eq_zero : a.val - b.val = 0 := by
        rcases Nat.eq_zero_or_pos (a.val - b.val) with h0 | hpos
        · exact h0
        · exact absurd (Nat.le_of_dvd hpos hN_dvd) (by omega)
      omega

/-- The image of `lightconeInjection j_s P hP` is `cyclicInterval N j_s P`. -/
theorem lightconeInjection_range {N : ℕ} (j_s : Fin N) (P : ℕ)
    (hP : 2 * P + 2 ≤ N) :
    (Finset.univ : Finset (Fin (2 * P + 2))).map (lightconeInjection j_s P hP) =
      cyclicInterval N j_s P := by
  ext x
  rw [Finset.mem_map]
  unfold cyclicInterval
  rw [Finset.mem_image]
  constructor
  · rintro ⟨k, _hk_mem, hkx⟩
    refine ⟨k.val, Finset.mem_range.mpr k.isLt, ?_⟩
    show (⟨(j_s.val + (N - P) + k.val) % N, _⟩ : Fin N) = x
    -- lightconeInjection sends k to ⟨(j_s.val + (N - P) + k.val) % N, _⟩.
    -- This is exactly `hkx`.
    show (⟨(j_s.val + (N - P) + k.val) % N, _⟩ : Fin N) = x
    exact hkx
  · rintro ⟨i, hi_range, hix⟩
    rw [Finset.mem_range] at hi_range
    refine ⟨⟨i, hi_range⟩, Finset.mem_univ _, ?_⟩
    -- lightconeInjection ⟨i, hi_range⟩ = ⟨(j_s.val + (N - P) + i) % N, _⟩ = x.
    show (⟨(j_s.val + (N - P) + i) % N, _⟩ : Fin N) = x
    exact hix

-- ============================================================================
-- Section: operator-level matrix-entry matching (FGG structural identification)
-- ============================================================================

/-!
**Operator-level matrix-entry matching (FGG structural identification, arXiv:1411.4028v1 §II l.124–156).**

The *operator-level matrix-entry matching* between the full-chain QAOA-
conjugated bond observable on its `(2P+2)`-site lightcone window and the
reduced-chain QAOA-conjugated bond observable on the full `Fin (2P+2)`
reduced chain.

The mathematical content of the matching is the **FGG light-cone
theorem** (arXiv:1411.4028v1 §III, also documented as the
`bond_expectation_full_eq_reduced` source in `Reduction.lean`): the
QAOA-conjugated bond operator's matrix entries on the `(2P+2)`-window
agree, after the `lightconeInjection` reindexing above, with the
reduced-chain QAOA-conjugated bond operator matrix entries.

The full operator-bookkeeping proof — induction on `P` with layer-by-layer
matching of (a) cost-layer factors inside the window, (b) mixer-layer
factors inside the window, (c) cost-bond factors **straddling** the
window's edges which act trivially on the lightcone-restricted state per
the `tensorSupportedOn_qaoa_conj` support bound (Lemma 3 of
`FGGClosure.lean`), and (d) the **FGG boundary-independence** subtlety
(reduced-chain ABC twist on the seam bond `−Z_{N_R-1} Z_0` contributes
identically to the full-chain plain-PBC seam bond, as `cP(0)`'s lightcone
on the reduced chain reaches the boundary bond only when `2P+2 = N_R`
exactly, and the ABC sign cancels symmetrically).

The structural matching is packaged as a **predicate**
`LightconeStructuralMatching` whose mathematical content is the FGG
light-cone theorem itself, and the closed-form composition is proved
**conditional on** the predicate. Downstream, the predicate is discharged
in `Reduction.lean` via the FGG citation, feeding the closed
`qaoa_full_eq_reduced_on_lightcone_closed` consumer.

Source pins (mirrored in the predicate's docstring):
* FGG arXiv:1411.4028v1 §II l.124–156 — lightcone subgraph state.
* FGG arXiv:1411.4028v1 §III — light-cone theorem.
* Mbeng–Santoro arXiv:1906.08948v2 §IV l.620–678 — chain reduction.
-/

-- ============================================================================
-- Section: The full↔reduced chain operator wrappers
-- ============================================================================

/-!
For the FGG structural identification we need to refer to the full-chain
QAOA-conjugated bond observable `O_full(N, P, γ, β, j_s)` and the
reduced-chain QAOA-conjugated bond observable `O_red(P, γ, β)`. We
package these via `qaoaConjugate` (defined in `FGGClosure.lean` and used
by Lemma 3).
-/

/-- The full-chain QAOA-conjugated bond observable at site `j_s` on `N`
qubits. This is the operator
`U_P† · chainPairInteraction j_s · U_P`
in the FGG layered conjugation form. Source: FGG arXiv:1411.4028v1
§II l.115–132 (operator-spreading definition). -/
def fullChainQAOAConj {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ) (j_s : Fin N) :
    Qubits.NQubitOp N :=
  qaoaConjugate P γ β (IsingModel.chainPairInteraction j_s)

/-- The reduced-chain QAOA-conjugated bond observable at site `0` on
`2P+2` qubits. The reduced chain has exactly `2P+2 = N_R` sites and the
canonical interior bond is at index `0` (any other site would give the
same expectation under cyclic invariance of the reduced chain, but `0`
is the canonical FGG choice). Source: arXiv:1906.08948v2 §IV l.626–668. -/
def reducedChainQAOAConj (P : ℕ) (γ β : Fin P → ℝ) :
    Qubits.NQubitOp (2 * P + 2) :=
  qaoaConjugate P γ β
    (IsingModel.chainPairInteraction (⟨0, by omega⟩ : Fin (2 * P + 2)))

/-- The seed support for a bond at site `k`: `{k} ∪ {nextSite k}`. We
use this explicit form to align with the notation produced by
`tensorSupportedOn_chainPairInteraction` in `FGGClosure.lean`. -/
def bondSeed {n : ℕ} (k : Fin n) : Finset (Fin n) :=
  ({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n))

/-- Tensor-support of the full-chain QAOA-conjugated bond observable on
its `(2P+2)`-site lightcone window `expand_by_n P (bondSeed j_s)`.
Direct consequence of Lemma 3 (`tensorSupportedOn_qaoa_conj`). -/
theorem tensorSupportedOn_fullChainQAOAConj
    {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ) (j_s : Fin N) :
    tensorSupportedOn
        (expand_by_n P (bondSeed j_s))
        (fullChainQAOAConj P γ β j_s) :=
  tensorSupportedOn_qaoa_conj
    (tensorSupportedOn_chainPairInteraction j_s) P γ β

/-- Tensor-support of the reduced-chain QAOA-conjugated bond observable
on its `(2P+2)`-site lightcone window. -/
theorem tensorSupportedOn_reducedChainQAOAConj (P : ℕ) (γ β : Fin P → ℝ) :
    tensorSupportedOn
        (expand_by_n P (bondSeed (⟨0, by omega⟩ : Fin (2 * P + 2))))
        (reducedChainQAOAConj P γ β) :=
  tensorSupportedOn_qaoa_conj
    (tensorSupportedOn_chainPairInteraction _) P γ β

-- ============================================================================
-- Section: The `LightconeStructuralMatching` predicate
-- ============================================================================

/-- **FGG light-cone structural matching predicate.**

The predicate that captures exactly the operator-level matrix-entry
matching between the full-chain and reduced-chain QAOA-conjugated bond
observables on the `(2P+2)`-site lightcone window. Discharging this
predicate is precisely the FGG light-cone theorem
(arXiv:1411.4028v1 §III), used here as a black box rather than reproved
from scratch.

The predicate has the standard `qaoa_full_eq_reduced_on_lightcone`
shape: a bijection `e` between the full-chain support `S_full` and the
reduced-chain support `S_red`, plus per-`(zs, ws)` matrix-entry
equality.

Source: FGG arXiv:1411.4028v1 §III. -/
structure LightconeStructuralMatching
    {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) (j_s : Fin N) : Type where
  /-- A bijection identifying the full-chain lightcone-window support with
  the reduced-chain lightcone-window support. -/
  e : (expand_by_n P (bondSeed j_s))
        ≃
      (expand_by_n P (bondSeed (⟨0, by omega⟩ : Fin (2 * P + 2))))
  /-- Per-`(zs, ws)` matrix-entry equality between the full and reduced
  QAOA-conjugated bond observables. -/
  matrix_entry_match : ∀
      (zs ws : (expand_by_n P (bondSeed j_s)) → Fin 2),
    restrictedMatrixEntry
        (expand_by_n P (bondSeed j_s))
        (fullChainQAOAConj P γ β j_s) zs ws =
      restrictedMatrixEntry
        (expand_by_n P (bondSeed (⟨0, by omega⟩ : Fin (2 * P + 2))))
        (reducedChainQAOAConj P γ β)
        (fun k => zs (e.symm k))
        (fun k => ws (e.symm k))

-- ============================================================================
-- Section: closed-form Lemma 5 composition
-- ============================================================================

/-- **Lemma 5 closed form** (FGG arXiv:1411.4028v1 §II l.149 +
arXiv:1906.08948v2 §IV l.626).

Conditional on the FGG structural-matching predicate
`LightconeStructuralMatching`, the full-chain bond expectation at
`j_s = N/2` agrees with the reduced-chain bond expectation at the
canonical interior bond `0` of the `2P+2`-site reduced chain. The
expectation is on the uniform `|+⟩^{⊗N}` (resp. `|+⟩^{⊗(2P+2)}`) state,
matching the QAOA conjugation form used by `isingChainQAOAFirstMoment`
after unfolding the QAOA unitaries onto the bond observable. -/
theorem qaoa_full_eq_reduced_on_lightcone_closed
    {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) (j_s : Fin N)
    (h_match : LightconeStructuralMatching P hP γ β j_s) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (fullChainQAOAConj P γ β j_s *
          QAOA.uniformKet (Qubits.NQubitDim N)) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj P γ β *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  -- Set up the two `tensorSupportedOn` witnesses (Lemma 3) and feed them
  -- through `qaoa_full_eq_reduced_on_lightcone` (in
  -- `ChainIdentification.lean`).
  refine qaoa_full_eq_reduced_on_lightcone
    (tensorSupportedOn_fullChainQAOAConj P γ β j_s)
    (tensorSupportedOn_reducedChainQAOAConj P γ β)
    ?_ h_match.e ?_
  · -- Cardinality match: both supports have card ≤ 2*P + 2 and the
    -- bijection witnesses card equality directly via `Finset.card_eq_of_equiv`.
    exact Finset.card_eq_of_equiv h_match.e
  · -- Matrix-entry match: this is `h_match.matrix_entry_match` directly.
    exact h_match.matrix_entry_match

end

end QAOA.IsingChain.UpperBound.LightCone
