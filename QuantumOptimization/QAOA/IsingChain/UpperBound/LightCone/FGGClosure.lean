import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.Spreading

/-!
# FGG Closure — strengthened tensor-support predicate for disjoint-commute

This file introduces a **tensor-support** predicate `tensorSupportedOn` that
captures the genuine `A = A_S ⊗ I_{Sᶜ}` structure of a multi-qubit operator
on a finite set `S ⊆ Fin N`. It is strictly stronger than the matrix-entry
locality predicate `supportedOn` of `LightCone.Basic`: as a concrete N=2
counter-example shows, `supportedOn`
allows nonzero matrix entries on the `AgreeOutside`-diagonal to depend on
the bits outside `S`, which is incompatible with the disjoint-commute
Lemma 1 of the FGG light-cone analysis.

The predicate is formulated as a **conjunctive form** — `supportedOn` plus
the additional clause that nonzero matrix entries depend only on the
restriction to `S`. The conjunction characterizes operators of the form
`A_S ⊗ I_{Sᶜ}` (up to reindexing). The bridge
`tensorSupportedOn → supportedOn` is then literally the first projection
and keeps the `LightCone.Basic` calculus reachable downstream.

Sources:
* Farhi, Goldstone, Gutmann (FGG), *A Quantum Approximate Optimization
  Algorithm*, arXiv:1411.4028v1 §II l.102–250 (operator-spreading
  argument).

## Main definitions

* `tensorSupportedOn` — the conjunctive tensor-support predicate.
* `costTouchingProd`, `mixerTouchingProd` — the per-layer products of the
  cost/mixer generator factors that touch a given window.
* `expand_by_one`, `expand_by_n` — one-ring / `n`-ring window expansion.
* `qaoaConjugate` — the Heisenberg-picture QAOA conjugation recursion
  (recursion peels `Fin.last` innermost; see the WARNING on its definition).
* `prevSite` — the cyclic predecessor on `Fin (2P+2)`.

## Main statements

* `tensorSupportedOn.toSupportedOn` — one-way bridge to `LightCone.Basic`.
* `tensorSupportedOn_one/smul/add/mono/mul/noncommProd` — closure calculus.
* `tensorSupportedOn_localOp`, `tensorSupportedOn_localPauliX/Y/Z`,
  `tensorSupportedOn_chainPairInteraction` — generator witnesses.
* `tensorSupportedOn_exp_chainPairInteraction`, `tensorSupportedOn_exp_localPauliX`
  — cost-bond / mixer single-site exponential witnesses.
* `tensorSupportedOn_commute_of_disjoint` (**Lemma 1**) — disjoint supports
  commute (FGG arXiv:1411.4028v1 §II l.115–125 lightcone factorization).
* `cost_layer_conj_eq_touching`, `mixer_layer_conj_eq_touching` — one-layer
  conjugation rewrites to the touching-factor products.
* `tensorSupportedOn_cost_layer_conj_tight`, `tensorSupportedOn_mixer_layer_conj`,
  `tensorSupportedOn_qaoa_conj` — light-cone spreading of the conjugates.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: The `tensorSupportedOn` predicate
-- ============================================================================

/-- An `N`-qubit operator `A` is **tensor-supported** on `S ⊆ Fin N` if it
both
1. acts as the identity off `S` in the matrix-entry sense
   (`supportedOn S A`), and
2. its nonzero matrix entries depend only on the `S`-restriction of the
   row and column indices — i.e. moving the outside-`S` bits of `ix`/`iy`
   to any other matching outside-`S` configuration leaves the entry
   unchanged.

Equivalently, `A = A_S ⊗ I_{Sᶜ}` for some single-block operator `A_S` on
the `S`-qubits, modulo the bitstring reindexing.

Source: arXiv:1411.4028v1 §II l.102–250 (lightcone tensor structure). -/
def tensorSupportedOn {N : ℕ} (S : Finset (Fin N)) (A : Qubits.NQubitOp N) : Prop :=
  supportedOn S A ∧
    ∀ ix iy ix' iy' : Fin (Qubits.NQubitDim N),
      (∀ k ∈ S, (Qubits.bitStringEquiv N).symm ix k =
          (Qubits.bitStringEquiv N).symm ix' k) →
      (∀ k ∈ S, (Qubits.bitStringEquiv N).symm iy k =
          (Qubits.bitStringEquiv N).symm iy' k) →
      AgreeOutside S ((Qubits.bitStringEquiv N).symm ix)
          ((Qubits.bitStringEquiv N).symm iy) →
      AgreeOutside S ((Qubits.bitStringEquiv N).symm ix')
          ((Qubits.bitStringEquiv N).symm iy') →
      A ix iy = A ix' iy'

/-- Bridge: `tensorSupportedOn` implies `supportedOn`. The converse is
provably false (an N=2 counter-example). -/
theorem tensorSupportedOn.toSupportedOn {N : ℕ} {S : Finset (Fin N)}
    {A : Qubits.NQubitOp N} (hA : tensorSupportedOn S A) :
    supportedOn S A :=
  hA.1

-- ============================================================================
-- Section: Closure calculus
-- ============================================================================

/-- The identity operator is tensor-supported on `∅`. -/
theorem tensorSupportedOn_one {N : ℕ} :
    tensorSupportedOn (∅ : Finset (Fin N)) (1 : Qubits.NQubitOp N) := by
  refine ⟨supportedOn_one, ?_⟩
  intro ix iy ix' iy' _hS_ix _hS_iy hAO hAO'
  -- With `S = ∅`, `AgreeOutside ∅` is equality of bitstrings.
  have h1 : (Qubits.bitStringEquiv N).symm ix = (Qubits.bitStringEquiv N).symm iy := by
    funext k; exact hAO k (by simp)
  have h2 : (Qubits.bitStringEquiv N).symm ix' = (Qubits.bitStringEquiv N).symm iy' := by
    funext k; exact hAO' k (by simp)
  have hxy : ix = iy := by
    have := congrArg (Qubits.bitStringEquiv N) h1
    simpa using this
  have hxy' : ix' = iy' := by
    have := congrArg (Qubits.bitStringEquiv N) h2
    simpa using this
  subst hxy
  subst hxy'
  simp

/-- Scalar multiplication preserves tensor-support. -/
theorem tensorSupportedOn_smul {N : ℕ} {S : Finset (Fin N)} {A : Qubits.NQubitOp N}
    (c : ℂ) (hA : tensorSupportedOn S A) :
    tensorSupportedOn S (c • A) := by
  refine ⟨supportedOn_smul c hA.1, ?_⟩
  intro ix iy ix' iy' hS_ix hS_iy hAO hAO'
  have h := hA.2 ix iy ix' iy' hS_ix hS_iy hAO hAO'
  simp [Matrix.smul_apply, h]

/-- Enlarging the support set keeps tensor-support. The "within-block
constant" clause is strengthened from `S` to `T ⊇ S` by noting that
agreement on `T` and `AgreeOutside T` together imply the corresponding
relations on `S` via the bridge `supportedOn`. -/
theorem tensorSupportedOn_mono {N : ℕ} {S T : Finset (Fin N)} (hST : S ⊆ T)
    {A : Qubits.NQubitOp N} (hA : tensorSupportedOn S A) :
    tensorSupportedOn T A := by
  refine ⟨supportedOn_mono hST hA.1, ?_⟩
  intro ix iy ix' iy' hT_ix hT_iy hAO hAO'
  -- We argue by case analysis on whether the four indices agree outside `S`.
  by_cases hAOS : AgreeOutside S ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iy)
  · by_cases hAOS' : AgreeOutside S ((Qubits.bitStringEquiv N).symm ix')
        ((Qubits.bitStringEquiv N).symm iy')
    · -- Both pairs agree outside `S`; apply the inner clause directly,
      -- using that `T`-agreement on rows implies `S`-agreement on rows
      -- (since `S ⊆ T`).
      refine hA.2 ix iy ix' iy' ?_ ?_ hAOS hAOS'
      · intro k hk; exact hT_ix k (hST hk)
      · intro k hk; exact hT_iy k (hST hk)
    · -- `(ix', iy')` disagrees outside `S`, so `A ix' iy' = 0`.
      have := hA.1 ix' iy' hAOS'
      -- We need `A ix iy = 0` as well. Use disagreement outside `S` of
      -- `(ix, iy)`: actually `(ix, iy)` agrees outside `S` by hypothesis;
      -- but we can still show both sides equal zero by exploiting the
      -- within-block clause with a clever choice. Instead, observe that
      -- if `(ix', iy')` disagrees outside `S` but agrees outside `T`,
      -- there must be `k ∈ T \ S` where they disagree, AND on `T` the
      -- restrictions match `ix, iy`. Use those restrictions to derive
      -- a contradiction with `(ix, iy)`'s `S`-outside agreement.
      exfalso
      obtain ⟨k, hkS, hkne⟩ : ∃ k, k ∉ S ∧
          (Qubits.bitStringEquiv N).symm ix' k ≠
          (Qubits.bitStringEquiv N).symm iy' k := by
        by_contra hcon
        push_neg at hcon
        exact hAOS' (fun k hk => hcon k hk)
      -- `k ∉ S`. If `k ∈ T`, use `hT_ix k hk` and `hT_iy k hk`.
      by_cases hkT : k ∈ T
      · have e1 : (Qubits.bitStringEquiv N).symm ix k =
            (Qubits.bitStringEquiv N).symm ix' k := hT_ix k hkT
        have e2 : (Qubits.bitStringEquiv N).symm iy k =
            (Qubits.bitStringEquiv N).symm iy' k := hT_iy k hkT
        -- `(ix, iy)` agrees outside `S` at `k`:
        have e3 : (Qubits.bitStringEquiv N).symm ix k =
            (Qubits.bitStringEquiv N).symm iy k := hAOS k hkS
        exact hkne (e1.symm.trans (e3.trans e2))
      · -- `k ∉ T`, so `AgreeOutside T (ix', iy')` gives equality at `k`.
        exact hkne (hAO' k hkT)
  · -- `(ix, iy)` disagrees outside `S`; by symmetry of the argument
    -- above (swap the four indices), `(ix', iy')` also disagrees
    -- outside `S`, and both matrix entries are zero.
    have hAOS' : ¬ AgreeOutside S ((Qubits.bitStringEquiv N).symm ix')
        ((Qubits.bitStringEquiv N).symm iy') := by
      intro hcon
      apply hAOS
      -- Mirror the case-analysis above with primes/unprimes swapped.
      obtain ⟨k, hkS, hkne⟩ : ∃ k, k ∉ S ∧
          (Qubits.bitStringEquiv N).symm ix k ≠
          (Qubits.bitStringEquiv N).symm iy k := by
        by_contra hcon2
        push_neg at hcon2
        exact hAOS (fun k hk => hcon2 k hk)
      by_cases hkT : k ∈ T
      · have e1 : (Qubits.bitStringEquiv N).symm ix k =
            (Qubits.bitStringEquiv N).symm ix' k := hT_ix k hkT
        have e2 : (Qubits.bitStringEquiv N).symm iy k =
            (Qubits.bitStringEquiv N).symm iy' k := hT_iy k hkT
        have e3 : (Qubits.bitStringEquiv N).symm ix' k =
            (Qubits.bitStringEquiv N).symm iy' k := hcon k hkS
        exact (hkne (e1.trans (e3.trans e2.symm))).elim
      · exact (hkne (hAO k hkT)).elim
    have h1 := hA.1 ix iy hAOS
    have h2 := hA.1 ix' iy' hAOS'
    rw [h1, h2]

/-- Sum preserves tensor-support, with support set the union.

The within-block clause is proved on the union by case analysis: if a
pair agrees outside `S` (resp. `T`), the corresponding summand's value
is constant on `S`-blocks (resp. `T`-blocks); pairs that disagree
outside one of `S, T` contribute zero from that summand. -/
theorem tensorSupportedOn_add {N : ℕ} {S T : Finset (Fin N)}
    {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn S A) (hB : tensorSupportedOn T B) :
    tensorSupportedOn (S ∪ T) (A + B) := by
  refine ⟨supportedOn_add hA.1 hB.1, ?_⟩
  intro ix iy ix' iy' hU_ix hU_iy hAO hAO'
  -- For `A`-summand: use `tensorSupportedOn_mono S → S ∪ T` then the
  -- within-block clause.
  have hA' : tensorSupportedOn (S ∪ T) A :=
    tensorSupportedOn_mono Finset.subset_union_left hA
  have hB' : tensorSupportedOn (S ∪ T) B :=
    tensorSupportedOn_mono Finset.subset_union_right hB
  have eA := hA'.2 ix iy ix' iy' hU_ix hU_iy hAO hAO'
  have eB := hB'.2 ix iy ix' iy' hU_ix hU_iy hAO hAO'
  simp [Matrix.add_apply, eA, eB]

-- ============================================================================
-- Section: `tensorSupportedOn_mul` — the central closure rule
-- ============================================================================

/-!
The product `A * B` is tensor-supported on `S ∪ T`. Proof: given indices
`ix, iy, ix', iy'` with the prescribed `(S∪T)`-agreement, we build a
bijection on the matrix-product summand index `iz` that pairs each
nonzero contribution `A ix iz · B iz iy` with a matching contribution
`A ix' iz' · B iz' iy'` of equal value. The bijection is defined by
pinning the outside-`S` bits of `iz'` to `ix'` and the outside-`T` bits
of `iz'` to `iy'`; these constraints are consistent on `Sᶜ ∩ Tᶜ` because
`ix'` and `iy'` agree there (by `AgreeOutside (S ∪ T) ix' iy'`).

This is the most delicate piece of the predicate's closure calculus.
The strong tensor-support clause is precisely what is needed to make
the re-indexing work; the weaker `supportedOn` predicate of
`LightCone.Basic` is provably not enough.
-/

/-- Internal helper: build the matching summand index `iz'` from `iz`
given the four boundary indices.

For each site `k`, `iz'` is:
* `ix' k` if `k ∉ S` (forces `AgreeOutside S (ix', iz')`),
* `iy' k` if `k ∉ T` (forces `AgreeOutside T (iz', iy')`),
* `iz k` if `k ∈ S ∩ T` (the free part — runs over the same range as `iz`).

The two non-overlapping rules agree on `Sᶜ ∩ Tᶜ` whenever
`AgreeOutside (S ∪ T) ix' iy'` holds. -/
private def mulMatchBitString {N : ℕ} (S T : Finset (Fin N))
    (ix' iy' : Qubits.BitString N) (iz : Qubits.BitString N) :
    Qubits.BitString N :=
  fun k =>
    if k ∈ S then
      if k ∈ T then iz k else iy' k
    else ix' k

private lemma mulMatchBitString_S_eq {N : ℕ} {S T : Finset (Fin N)}
    {ix' iy' iz : Qubits.BitString N} {k : Fin N} (hkS : k ∈ S) (hkT : k ∈ T) :
    mulMatchBitString S T ix' iy' iz k = iz k := by
  unfold mulMatchBitString
  simp [hkS, hkT]

private lemma mulMatchBitString_SnotT {N : ℕ} {S T : Finset (Fin N)}
    {ix' iy' iz : Qubits.BitString N} {k : Fin N} (hkS : k ∈ S) (hkT : k ∉ T) :
    mulMatchBitString S T ix' iy' iz k = iy' k := by
  unfold mulMatchBitString
  simp [hkS, hkT]

private lemma mulMatchBitString_notS {N : ℕ} {S T : Finset (Fin N)}
    {ix' iy' iz : Qubits.BitString N} {k : Fin N} (hkS : k ∉ S) :
    mulMatchBitString S T ix' iy' iz k = ix' k := by
  unfold mulMatchBitString
  simp [hkS]

/-- Product preserves tensor-support, with support set the union.

Proof structure: expand both matrix entries as sums `∑ iz, A · iz * B iz ·`,
restrict each sum to the "good" indices `iz` where both factors are
nonzero (i.e., `AgreeOutside S (ix, iz)` and `AgreeOutside T (iz, iy)`),
and exhibit a bijection between the two good sets that pins the
outside-`(S ∪ T)` bits of `iz` to the appropriate boundary index. The
within-block clauses of `hA` and `hB` then equate matched summands. -/
theorem tensorSupportedOn_mul {N : ℕ} {S T : Finset (Fin N)}
    {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn S A) (hB : tensorSupportedOn T B) :
    tensorSupportedOn (S ∪ T) (A * B) := by
  classical
  refine ⟨supportedOn_mul hA.1 hB.1, ?_⟩
  intro ix iy ix' iy' hU_ix hU_iy hAO hAO'
  -- Expand both matrix entries as sums over the intermediate index.
  have hmul₁ : (A * B) ix iy = ∑ iz, A ix iz * B iz iy := by
    simp [Matrix.mul_apply]
  have hmul₂ : (A * B) ix' iy' = ∑ iz, A ix' iz * B iz iy' := by
    simp [Matrix.mul_apply]
  rw [hmul₁, hmul₂]
  -- Build the bijection on `iz` via `mulMatchBitString`, but restrict it
  -- to the "good" indices where both factors are nonzero.
  -- We reindex the LHS sum by `iz ↦ iz'` where `iz' = bitStringEquiv N (mulMatchBitString ...)`.
  set e := Qubits.bitStringEquiv N with he_def
  -- "Good" predicate: iz contributes nonzero to the matrix product entry.
  let good : Qubits.BitString N → Qubits.BitString N → Qubits.BitString N → Prop :=
    fun a b z => AgreeOutside S a z ∧ AgreeOutside T z b
  -- Restrict each sum to good indices: non-good terms vanish.
  have hsumLHS :
      (∑ iz, A ix iz * B iz iy) =
        ∑ iz ∈ (Finset.univ.filter (fun iz => good (e.symm ix) (e.symm iy) (e.symm iz))),
          A ix iz * B iz iy := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro iz _ hne
    by_contra hgood
    apply hne
    by_cases hAS : AgreeOutside S (e.symm ix) (e.symm iz)
    · by_cases hBT : AgreeOutside T (e.symm iz) (e.symm iy)
      · exact (hgood ⟨hAS, hBT⟩).elim
      · have := hB.1 iz iy hBT; simp [this]
    · have := hA.1 ix iz hAS; simp [this]
  have hsumRHS :
      (∑ iz, A ix' iz * B iz iy') =
        ∑ iz ∈ (Finset.univ.filter (fun iz => good (e.symm ix') (e.symm iy') (e.symm iz))),
          A ix' iz * B iz iy' := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro iz _ hne
    by_contra hgood
    apply hne
    by_cases hAS : AgreeOutside S (e.symm ix') (e.symm iz)
    · by_cases hBT : AgreeOutside T (e.symm iz) (e.symm iy')
      · exact (hgood ⟨hAS, hBT⟩).elim
      · have := hB.1 iz iy' hBT; simp [this]
    · have := hA.1 ix' iz hAS; simp [this]
  rw [hsumLHS, hsumRHS]
  -- The map on bitstrings.
  let φ : Qubits.BitString N → Qubits.BitString N :=
    mulMatchBitString S T (e.symm ix') (e.symm iy')
  let ψ : Qubits.BitString N → Qubits.BitString N :=
    mulMatchBitString S T (e.symm ix) (e.symm iy)
  have hψφ : ∀ z : Qubits.BitString N, good (e.symm ix) (e.symm iy) z → ψ (φ z) = z := by
    intro z hz
    funext k
    by_cases hkS : k ∈ S
    · by_cases hkT : k ∈ T
      · simp [ψ, φ, mulMatchBitString_S_eq hkS hkT]
      · -- ψ(φ z) k = iy k; need = z k. Use hz.2 (k ∉ T): z k = iy k.
        simp only [ψ, φ, mulMatchBitString_SnotT hkS hkT]
        exact (hz.2 k hkT).symm
    · -- k ∉ S: ψ(φ z) k = ix k; need = z k. Use hz.1 (k ∉ S): ix k = z k.
      simp only [ψ, φ, mulMatchBitString_notS hkS]
      exact (hz.1 k hkS)
  have hφψ : ∀ z : Qubits.BitString N, good (e.symm ix') (e.symm iy') z → φ (ψ z) = z := by
    intro z hz
    funext k
    by_cases hkS : k ∈ S
    · by_cases hkT : k ∈ T
      · simp [ψ, φ, mulMatchBitString_S_eq hkS hkT]
      · simp only [ψ, φ, mulMatchBitString_SnotT hkS hkT]
        exact (hz.2 k hkT).symm
    · simp only [ψ, φ, mulMatchBitString_notS hkS]
      exact (hz.1 k hkS)
  -- Define the lifted bijection on indices.
  let mapφ : Fin (Qubits.NQubitDim N) → Fin (Qubits.NQubitDim N) :=
    fun iz => e (φ (e.symm iz))
  -- Show that mapφ sends LHS good set to RHS good set.
  have hφ_good : ∀ z : Qubits.BitString N,
      good (e.symm ix') (e.symm iy') (φ z) := by
    intro z
    refine ⟨?_, ?_⟩
    · -- AgreeOutside S (e.symm ix') (φ z): for k ∉ S, ix' k = φ z k.
      intro k hkS
      simp only [φ, mulMatchBitString_notS hkS]
    · -- AgreeOutside T (φ z) (e.symm iy'): for k ∉ T, φ z k = iy' k.
      intro k hkT
      by_cases hkS : k ∈ S
      · simp only [φ, mulMatchBitString_SnotT hkS hkT]
      · -- k ∉ S, k ∉ T: φ z k = ix' k. Need = iy' k. Use hAO'.
        simp only [φ, mulMatchBitString_notS hkS]
        have hkU : k ∉ S ∪ T := by
          intro hkU; rcases Finset.mem_union.mp hkU with h | h
          · exact hkS h
          · exact hkT h
        exact hAO' k hkU
  have hψ_good : ∀ z : Qubits.BitString N,
      good (e.symm ix) (e.symm iy) (ψ z) := by
    intro z
    refine ⟨?_, ?_⟩
    · intro k hkS
      simp only [ψ, mulMatchBitString_notS hkS]
    · intro k hkT
      by_cases hkS : k ∈ S
      · simp only [ψ, mulMatchBitString_SnotT hkS hkT]
      · simp only [ψ, mulMatchBitString_notS hkS]
        have hkU : k ∉ S ∪ T := by
          intro hkU; rcases Finset.mem_union.mp hkU with h | h
          · exact hkS h
          · exact hkT h
        exact hAO k hkU
  -- Sum bijection.
  refine Finset.sum_bij (fun iz _ => mapφ iz) ?_ ?_ ?_ ?_
  · -- maps LHS filter into RHS filter.
    intro iz hiz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz ⊢
    have hg := hφ_good (e.symm iz)
    -- mapφ iz = e (φ (e.symm iz)), so e.symm (mapφ iz) = φ (e.symm iz).
    have : e.symm (mapφ iz) = φ (e.symm iz) := by simp [mapφ]
    rw [this]
    exact hg
  · -- injectivity on LHS filter.
    intro iz₁ hiz₁ iz₂ hiz₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz₁ hiz₂
    -- heq : mapφ iz₁ = mapφ iz₂.
    have h1 : φ (e.symm iz₁) = φ (e.symm iz₂) := by
      have := congrArg e.symm heq
      simpa [mapφ] using this
    have h2 : ψ (φ (e.symm iz₁)) = ψ (φ (e.symm iz₂)) := by rw [h1]
    rw [hψφ (e.symm iz₁) hiz₁, hψφ (e.symm iz₂) hiz₂] at h2
    have := congrArg e h2
    simpa using this
  · -- surjectivity onto RHS filter.
    intro iz' hiz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz'
    refine ⟨e (ψ (e.symm iz')), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : e.symm (e (ψ (e.symm iz'))) = ψ (e.symm iz') := by simp
      rw [this]
      exact hψ_good (e.symm iz')
    · -- mapφ (e (ψ (e.symm iz'))) = iz'.
      simp only [mapφ]
      have h1 : e.symm (e (ψ (e.symm iz'))) = ψ (e.symm iz') := by simp
      rw [h1, hφψ (e.symm iz') hiz']
      simp
  · -- matched values.
    intro iz hiz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz
    obtain ⟨hAS, hBT⟩ := hiz
    -- Equate A ix iz with A ix' (mapφ iz) using hA.2.
    have hmapφ : e.symm (mapφ iz) = φ (e.symm iz) := by simp [mapφ]
    have hg' := hφ_good (e.symm iz)
    have hAS' : AgreeOutside S (e.symm ix') (φ (e.symm iz)) := hg'.1
    have hBT' : AgreeOutside T (φ (e.symm iz)) (e.symm iy') := hg'.2
    have hA_eq : A ix iz = A ix' (mapφ iz) := by
      apply hA.2 ix iz ix' (mapφ iz)
      · intro k hkS; exact hU_ix k (Finset.mem_union.mpr (Or.inl hkS))
      · intro k hkS
        rw [hmapφ]
        change e.symm iz k = φ (e.symm iz) k
        by_cases hkT : k ∈ T
        · -- φ (e.symm iz) k = iz k.
          rw [show φ (e.symm iz) k = (e.symm iz) k from
            mulMatchBitString_S_eq hkS hkT]
        · -- φ (e.symm iz) k = iy' k. iz k = iy k (from hBT, k ∉ T), iy k = iy' k (k ∈ S).
          rw [show φ (e.symm iz) k = e.symm iy' k from
            mulMatchBitString_SnotT hkS hkT]
          have h1 : e.symm iz k = e.symm iy k := hBT k hkT
          have h2 : e.symm iy k = e.symm iy' k :=
            hU_iy k (Finset.mem_union.mpr (Or.inl hkS))
          exact h1.trans h2
      · exact hAS
      · rw [hmapφ]; exact hAS'
    have hB_eq : B iz iy = B (mapφ iz) iy' := by
      apply hB.2 iz iy (mapφ iz) iy'
      · intro k hkT
        rw [hmapφ]
        change e.symm iz k = φ (e.symm iz) k
        by_cases hkS : k ∈ S
        · rw [show φ (e.symm iz) k = (e.symm iz) k from
            mulMatchBitString_S_eq hkS hkT]
        · -- φ (e.symm iz) k = ix' k. iz k = ix k (from hAS, k ∉ S), ix k = ix' k (k ∈ T).
          rw [show φ (e.symm iz) k = e.symm ix' k from
            mulMatchBitString_notS hkS]
          have h1 : e.symm iz k = e.symm ix k := (hAS k hkS).symm
          have h2 : e.symm ix k = e.symm ix' k :=
            hU_ix k (Finset.mem_union.mpr (Or.inr hkT))
          exact h1.trans h2
      · intro k hkT; exact hU_iy k (Finset.mem_union.mpr (Or.inr hkT))
      · exact hBT
      · rw [hmapφ]; exact hBT'
    rw [hA_eq, hB_eq]

-- ============================================================================
-- Section: Generator witnesses
-- ============================================================================

/-- A generic local lift `localOp A j` is tensor-supported on `{j}`. -/
theorem tensorSupportedOn_localOp {N : ℕ} (A : Quantum.Operators.Op 2) (j : Fin N) :
    tensorSupportedOn ({j} : Finset (Fin N)) (Qubits.localOp A j) := by
  refine ⟨supportedOn_localOp A j, ?_⟩
  intro ix iy ix' iy' hS_ix hS_iy hAO hAO'
  -- Both pairs agree outside `{j}` ↔ `SameOutside j`.
  have hsame : Qubits.SameOutside j ((Qubits.bitStringEquiv N).symm ix)
      ((Qubits.bitStringEquiv N).symm iy) :=
    (agreeOutside_singleton (N := N) j _ _).mp hAO
  have hsame' : Qubits.SameOutside j ((Qubits.bitStringEquiv N).symm ix')
      ((Qubits.bitStringEquiv N).symm iy') :=
    (agreeOutside_singleton (N := N) j _ _).mp hAO'
  -- The j-bit equalities from the row/column hypotheses.
  have hj_ix : (Qubits.bitStringEquiv N).symm ix j =
      (Qubits.bitStringEquiv N).symm ix' j :=
    hS_ix j (Finset.mem_singleton.mpr rfl)
  have hj_iy : (Qubits.bitStringEquiv N).symm iy j =
      (Qubits.bitStringEquiv N).symm iy' j :=
    hS_iy j (Finset.mem_singleton.mpr rfl)
  rw [Qubits.localOp_apply_of_sameOutside A j ix iy hsame]
  rw [Qubits.localOp_apply_of_sameOutside A j ix' iy' hsame']
  rw [hj_ix, hj_iy]

/-- Local Pauli `X` is tensor-supported on `{j}`. -/
theorem tensorSupportedOn_localPauliX {N : ℕ} (j : Fin N) :
    tensorSupportedOn ({j} : Finset (Fin N)) (Qubits.localPauliX j) := by
  rw [Qubits.localPauliX_eq_localOp]
  exact tensorSupportedOn_localOp _ j

/-- Local Pauli `Y` is tensor-supported on `{j}`. -/
theorem tensorSupportedOn_localPauliY {N : ℕ} (j : Fin N) :
    tensorSupportedOn ({j} : Finset (Fin N)) (Qubits.localPauliY j) := by
  rw [Qubits.localPauliY_eq_localOp]
  exact tensorSupportedOn_localOp _ j

/-- Local Pauli `Z` is tensor-supported on `{j}`. -/
theorem tensorSupportedOn_localPauliZ {N : ℕ} (j : Fin N) :
    tensorSupportedOn ({j} : Finset (Fin N)) (Qubits.localPauliZ j) := by
  rw [Qubits.localPauliZ_eq_localOp]
  exact tensorSupportedOn_localOp _ j

/-- A scalar multiple of the identity is tensor-supported on `∅`. -/
theorem tensorSupportedOn_smul_one {N : ℕ} (c : ℂ) :
    tensorSupportedOn (∅ : Finset (Fin N)) (c • (1 : Qubits.NQubitOp N)) :=
  tensorSupportedOn_smul c tensorSupportedOn_one

/-- The pair interaction `Z_k Z_{nextSite k}` is tensor-supported on
`{k, nextSite k}`. -/
theorem tensorSupportedOn_chainPairInteraction {n : ℕ} (k : Fin n) :
    tensorSupportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (IsingModel.chainPairInteraction k) := by
  unfold IsingModel.chainPairInteraction
  exact tensorSupportedOn_mul (tensorSupportedOn_localPauliZ k)
    (tensorSupportedOn_localPauliZ (IsingModel.nextSite k))

/-- The cost-bond exponential is tensor-supported on the bond
`{k, nextSite k}`. Uses the closed form from
`exp_chainPairInteraction_closed_form`. -/
theorem tensorSupportedOn_exp_chainPairInteraction {n : ℕ} (γ : ℝ) (k : Fin n) :
    tensorSupportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        IsingModel.chainPairInteraction k)) := by
  rw [exp_chainPairInteraction_closed_form]
  -- The identity summand is tensor-supported on `∅`, hence on the bond.
  have h_one : tensorSupportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      ((Real.cos γ : ℂ) • (1 : Qubits.NQubitOp n)) :=
    tensorSupportedOn_mono (Finset.empty_subset _)
      (tensorSupportedOn_smul_one (Real.cos γ : ℂ))
  -- The chain-pair summand is tensor-supported on the bond.
  have h_cp : tensorSupportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (((((-Complex.I) * Real.sin γ : ℂ))) • IsingModel.chainPairInteraction k) :=
    tensorSupportedOn_smul _ (tensorSupportedOn_chainPairInteraction k)
  -- Their sum is tensor-supported on the union (which collapses to the bond).
  have h_sum := tensorSupportedOn_add h_one h_cp
  refine tensorSupportedOn_mono ?_ h_sum
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

/-- The mixer single-site exponential `exp(-i β X_j)` is tensor-supported
on `{j}`. Uses the closed form from `QAOA.exp_localPauliX`. -/
theorem tensorSupportedOn_exp_localPauliX {N : ℕ} (β : ℝ) (j : Fin N) :
    tensorSupportedOn ({j} : Finset (Fin N))
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j)) := by
  rw [QAOA.exp_localPauliX]
  -- localMixerFactor N β j = cos β · I + (-i sin β) · X_j.
  unfold QAOA.localMixerFactor
  have h_one : tensorSupportedOn ({j} : Finset (Fin N))
      ((Real.cos β : ℂ) • (1 : Qubits.NQubitOp N)) :=
    tensorSupportedOn_mono (Finset.empty_subset _)
      (tensorSupportedOn_smul_one (Real.cos β : ℂ))
  have h_X : tensorSupportedOn ({j} : Finset (Fin N))
      ((((-Complex.I) * Real.sin β : ℂ)) • Qubits.localPauliX j) :=
    tensorSupportedOn_smul _ (tensorSupportedOn_localPauliX j)
  have h_sum := tensorSupportedOn_add h_one h_X
  simpa using h_sum

-- ============================================================================
-- Section: Lemma 1 — disjoint tensor-supports commute
-- ============================================================================

/-- **FGG Lemma 1.** If `A` and `B` are tensor-supported on disjoint
subsets, then `A * B = B * A`.

This is the central locality fact of the FGG light-cone analysis (FGG
arXiv:1411.4028v1 §II l.115–125): operators acting on disjoint sub-
registers commute. The proof expands both products at an arbitrary
matrix-entry index and exhibits a bijection between the summands of
`A * B` and `B * A` using the tensor-support clauses. -/
theorem tensorSupportedOn_commute_of_disjoint {N : ℕ}
    {S T : Finset (Fin N)} {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn S A) (hB : tensorSupportedOn T B)
    (hST : Disjoint S T) :
    Commute A B := by
  classical
  -- `Commute A B` unfolds to `A * B = B * A`.
  change A * B = B * A
  -- Equality of matrices via pointwise equality.
  ext ix iy
  set e := Qubits.bitStringEquiv N with he_def
  -- Expand each product as a sum over intermediate indices.
  have hAB : (A * B) ix iy = ∑ iz, A ix iz * B iz iy := by
    simp [Matrix.mul_apply]
  have hBA : (B * A) ix iy = ∑ iz, B ix iz * A iz iy := by
    simp [Matrix.mul_apply]
  rw [hAB, hBA]
  -- For `A * B`, the contributing `iz` satisfies `AgreeOutside S (ix, iz)`
  -- (from A) and `AgreeOutside T (iz, iy)` (from B).
  -- For `B * A`, the contributing `iz` satisfies `AgreeOutside T (ix, iz)`
  -- and `AgreeOutside S (iz, iy)`.
  -- Both restrict the same `iz` because S and T are disjoint: for `iz ∉ S`,
  -- iz_k is pinned by `A`'s side; for `iz ∉ T`, pinned by `B`'s side.
  -- We use the same `mulMatchBitString` style bijection.
  -- Build the bijection: for AB-good iz (AgreeOutside S (ix, iz), AgreeOutside T (iz, iy)),
  -- map to BA-good iz' = (mulMatchBitString T S ix iy iz). The construction:
  --   for k ∈ T: iz'_k = ix_k (forced by AgreeOutside T (ix, iz'))
  --   for k ∈ S: iz'_k = iy_k (forced by AgreeOutside S (iz', iy))
  --   for k ∈ Sᶜ ∩ Tᶜ: free; pin to iz_k.
  -- BUT: with S, T DISJOINT, S ∩ T = ∅, so iz_k on Sᶜ ∩ Tᶜ = (S ∪ T)ᶜ.
  -- The AB-good iz has iz_k = ix_k on Sᶜ AND iz_k = iy_k on Tᶜ. So
  -- on Sᶜ ∩ Tᶜ, ix_k = iz_k = iy_k.
  -- For the BA-side, BA-good iz' has iz'_k = ix_k on Tᶜ and iz'_k = iy_k on Sᶜ.
  -- Since S ∩ T = ∅, on S: iz'_k = ? Tᶜ-side forces iz'_k = ix_k. On T: iz'_k = iy_k
  -- (from Sᶜ-side, since T ⊆ Sᶜ).
  -- So a natural bijection: φ(iz)_k :=
  --   if k ∈ S then iy_k  (since S ⊆ Tᶜ, BA-good forces this)
  --   if k ∈ T then ix_k
  --   else iz_k  (on (S∪T)ᶜ, take iz_k = ix_k = iy_k from AB-good).
  -- Refactor: define a closed-form map.
  -- Restrict each sum to good indices.
  have hsumAB :
      (∑ iz, A ix iz * B iz iy) =
        ∑ iz ∈ (Finset.univ.filter
          (fun iz => AgreeOutside S (e.symm ix) (e.symm iz) ∧
            AgreeOutside T (e.symm iz) (e.symm iy))),
          A ix iz * B iz iy := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro iz _ hne
    by_contra hgood
    push_neg at hgood
    apply hne
    by_cases hAS : AgreeOutside S (e.symm ix) (e.symm iz)
    · have hBT : ¬ AgreeOutside T (e.symm iz) (e.symm iy) := hgood hAS
      have := hB.1 iz iy hBT; simp [this]
    · have := hA.1 ix iz hAS; simp [this]
  have hsumBA :
      (∑ iz, B ix iz * A iz iy) =
        ∑ iz ∈ (Finset.univ.filter
          (fun iz => AgreeOutside T (e.symm ix) (e.symm iz) ∧
            AgreeOutside S (e.symm iz) (e.symm iy))),
          B ix iz * A iz iy := by
    refine (Finset.sum_filter_of_ne ?_).symm
    intro iz _ hne
    by_contra hgood
    push_neg at hgood
    apply hne
    by_cases hBT : AgreeOutside T (e.symm ix) (e.symm iz)
    · have hAS : ¬ AgreeOutside S (e.symm iz) (e.symm iy) := hgood hBT
      have := hA.1 iz iy hAS; simp [this]
    · have := hB.1 ix iz hBT; simp [this]
  rw [hsumAB, hsumBA]
  -- Define the bijection on bitstrings.
  -- For an AB-good iz (AgreeOutside S (ix, iz), AgreeOutside T (iz, iy)),
  -- map it to a BA-good iz' via:
  --   for k ∈ S: iz' k = ix k  (forced by AgreeOutside T (ix, iz') since S ⊆ Tᶜ)
  --   for k ∈ T: iz' k = iy k  (forced by AgreeOutside S (iz', iy) since T ⊆ Sᶜ)
  --   else:      iz' k = iz k.
  -- The bijection is self-inverse (φ ∘ φ = id) when restricted to good sets.
  let φ : Qubits.BitString N → Qubits.BitString N :=
    fun z k => if k ∈ S then (e.symm ix) k
               else if k ∈ T then (e.symm iy) k
               else z k
  -- Inverse: for a BA-good iz' (AgreeOutside T (ix, iz'), AgreeOutside S (iz', iy)),
  -- map to AB-good iz via:
  --   for k ∈ S: iz k = iy k (forced by AgreeOutside S (iz', iy)? wait — that's iz' = iy on Sᶜ.
  --   For AB-good iz: AgreeOutside S (ix, iz) means iz k = ix k for k ∉ S.
  --   Need iz k on S: free (AgreeOutside S doesn't constrain in S; only need agreement on Sᶜ).
  --   But we need AB-good to be consistent. AB-good iz also has AgreeOutside T (iz, iy):
  --     iz k = iy k for k ∉ T (e.g. k ∈ S, since S ⊆ Tᶜ).
  --   So actually iz k = iy k for k ∈ S.
  --   And iz k = ix k for k ∈ T.
  --   And iz k = ix k = iy k for k ∉ S ∪ T (=iz' k from else branch).
  -- ψ : BA-good iz' → AB-good iz:
  --   for k ∈ S: iz k = iy k
  --   for k ∈ T: iz k = ix k
  --   else: iz k = iz' k.
  let ψ : Qubits.BitString N → Qubits.BitString N :=
    fun z k => if k ∈ S then (e.symm iy) k
               else if k ∈ T then (e.symm ix) k
               else z k
  have hST_S : ∀ k, k ∈ S → k ∉ T := fun k hkS hkT =>
    Finset.disjoint_left.mp hST hkS hkT
  -- Lift to indices.
  let mapφ : Fin (Qubits.NQubitDim N) → Fin (Qubits.NQubitDim N) :=
    fun iz => e (φ (e.symm iz))
  -- Bijection setup.
  refine Finset.sum_bij (fun iz _ => mapφ iz) ?_ ?_ ?_ ?_
  · -- mapφ sends AB-good to BA-good.
    intro iz hiz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz ⊢
    obtain ⟨hAS, hBT⟩ := hiz
    have hmap : e.symm (mapφ iz) = φ (e.symm iz) := by simp [mapφ]
    rw [hmap]
    refine ⟨?_, ?_⟩
    · -- AgreeOutside T (e.symm ix) (φ (e.symm iz)).
      intro k hkT
      by_cases hkS : k ∈ S
      · -- k ∈ S: φ z k = ix k. ix k = ix k. ✓
        simp only [φ, if_pos hkS]
      · by_cases hkT' : k ∈ T
        · exact absurd hkT' hkT
        · simp only [φ, if_neg hkS, if_neg hkT']
          exact hAS k hkS
    · -- AgreeOutside S (φ (e.symm iz)) (e.symm iy).
      intro k hkS
      by_cases hkT : k ∈ T
      · simp only [φ, if_neg hkS, if_pos hkT]
      · by_cases hkS' : k ∈ S
        · exact absurd hkS' hkS
        · simp only [φ, if_neg hkS', if_neg hkT]
          exact hBT k hkT
  · -- Injectivity on AB-good.
    intro iz₁ hiz₁ iz₂ hiz₂ heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz₁ hiz₂
    obtain ⟨hAS₁, hBT₁⟩ := hiz₁
    obtain ⟨hAS₂, hBT₂⟩ := hiz₂
    have h1 : φ (e.symm iz₁) = φ (e.symm iz₂) := by
      have := congrArg e.symm heq
      simpa [mapφ] using this
    -- φ z agrees with z outside S ∪ T (the else branch), with ix on S, with iy on T.
    -- Combined with AB-good hypotheses, iz₁ = iz₂ on Sᶜ ∩ Tᶜ from h1; on S, both iz₁
    -- and iz₂ equal iy (from AgreeOutside T at k ∈ S ⊆ Tᶜ); on T, both equal ix.
    have h_iz : e.symm iz₁ = e.symm iz₂ := by
      funext k
      by_cases hkS : k ∈ S
      · -- iz₁ k = iy k (from hBT₁ at k ∉ T, since k ∈ S ⊆ Tᶜ) = iz₂ k.
        have hkT : k ∉ T := hST_S k hkS
        exact (hBT₁ k hkT).trans (hBT₂ k hkT).symm
      · by_cases hkT : k ∈ T
        · -- iz₁ k = ix k (from hAS₁ at k ∉ S, since k ∈ T ⊆ Sᶜ).
          exact (hAS₁ k hkS).symm.trans (hAS₂ k hkS)
        · -- k ∉ S ∪ T: φ z₁ k = z₁ k, φ z₂ k = z₂ k. From h1: z₁ k = z₂ k.
          have := congrFun h1 k
          simp only [φ, if_neg hkS, if_neg hkT] at this
          exact this
    have := congrArg e h_iz
    simpa using this
  · -- Surjectivity onto BA-good.
    intro iz' hiz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz'
    obtain ⟨hBT', hAS'⟩ := hiz'
    refine ⟨e (ψ (e.symm iz')), ?_, ?_⟩
    · -- e (ψ (...)) is in AB-good filter.
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have : e.symm (e (ψ (e.symm iz'))) = ψ (e.symm iz') := by simp
      rw [this]
      refine ⟨?_, ?_⟩
      · intro k hkS
        by_cases hkT : k ∈ T
        · -- k ∉ S, k ∈ T: ψ z k = ix k. Need ix k = ix k ✓.
          simp only [ψ, if_neg hkS, if_pos hkT]
        · simp only [ψ, if_neg hkS, if_neg hkT]
          exact hBT' k hkT
      · intro k hkT
        by_cases hkS : k ∈ S
        · simp only [ψ, if_pos hkS]
        · by_cases hkT' : k ∈ T
          · exact absurd hkT' hkT
          · simp only [ψ, if_neg hkS, if_neg hkT']
            exact hAS' k hkS
    · -- mapφ (e (ψ (e.symm iz'))) = iz'.
      simp only [mapφ]
      have h1 : e.symm (e (ψ (e.symm iz'))) = ψ (e.symm iz') := by simp
      rw [h1]
      -- φ (ψ z) = z when z is BA-good.
      have hφψ : φ (ψ (e.symm iz')) = e.symm iz' := by
        funext k
        by_cases hkS : k ∈ S
        · -- φ (ψ z) k = ix k. From hAS' (k ∉ S? no k ∈ S). Use hBT' (k ∉ T since hST_S).
          have hkT : k ∉ T := hST_S k hkS
          simp only [φ, if_pos hkS]
          exact hBT' k hkT
        · by_cases hkT : k ∈ T
          · simp only [φ, if_neg hkS, if_pos hkT]
            exact (hAS' k hkS).symm
          · simp only [φ, if_neg hkS, if_neg hkT, ψ]
      rw [hφψ]
      simp
  · -- Equal summands: A ix iz * B iz iy = B ix (mapφ iz) * A (mapφ iz) iy.
    intro iz hiz
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hiz
    obtain ⟨hAS, hBT⟩ := hiz
    have hmap : e.symm (mapφ iz) = φ (e.symm iz) := by simp [mapφ]
    -- A ix iz = A (mapφ iz) iy: use hA.2 with row pair (ix, iz) and (mapφ iz, iy).
    -- WAIT: we want A ix iz = ? on the RHS. The RHS is B ix (mapφ iz) * A (mapφ iz) iy.
    -- So we need: A ix iz = A (mapφ iz) iy AND B iz iy = B ix (mapφ iz).
    --
    -- For A ix iz = A (mapφ iz) iy:
    -- Apply hA.2 with arguments (ix, iz) and (mapφ iz, iy):
    --   row-S: ∀ k ∈ S, e.symm ix k = e.symm (mapφ iz) k = φ z k.
    --     For k ∈ S: φ z k = ix k. ✓
    --   col-S: ∀ k ∈ S, e.symm iz k = e.symm iy k.
    --     For k ∈ S: k ∉ T, hBT k hkT: e.symm iz k = e.symm iy k. ✓ (with k ∉ T from hST_S)
    --   AgreeOutside S (ix, iz): given (hAS). ✓
    --   AgreeOutside S (mapφ iz, iy): we proved above as part of BA-good. ✓
    have hA_eq : A ix iz = A (mapφ iz) iy := by
      apply hA.2 ix iz (mapφ iz) iy
      · intro k hkS
        rw [hmap]
        change e.symm ix k = if k ∈ S then e.symm ix k
          else if k ∈ T then e.symm iy k else e.symm iz k
        rw [if_pos hkS]
      · intro k hkS
        have hkT : k ∉ T := hST_S k hkS
        exact hBT k hkT
      · exact hAS
      · -- AgreeOutside S (e.symm (mapφ iz)) (e.symm iy).
        intro k hkS
        rw [hmap]
        change (if k ∈ S then e.symm ix k
          else if k ∈ T then e.symm iy k else e.symm iz k) = e.symm iy k
        rw [if_neg hkS]
        by_cases hkT : k ∈ T
        · rw [if_pos hkT]
        · rw [if_neg hkT]
          exact hBT k hkT
    -- For B iz iy = B ix (mapφ iz):
    -- Apply hB.2 with arguments (iz, iy) and (ix, mapφ iz):
    --   row-T: ∀ k ∈ T, e.symm iz k = e.symm ix k.
    --     For k ∈ T: k ∉ S (by hST_T), so hAS k hkS: e.symm ix k = e.symm iz k. ✓
    --   col-T: ∀ k ∈ T, e.symm iy k = e.symm (mapφ iz) k = φ z k.
    --     For k ∈ T: k ∉ S, so φ z k = iy k. ✓
    --   AgreeOutside T (iz, iy): given (hBT). ✓
    --   AgreeOutside T (ix, mapφ iz): we proved above. ✓
    have hB_eq : B iz iy = B ix (mapφ iz) := by
      apply hB.2 iz iy ix (mapφ iz)
      · intro k hkT
        have hkS : k ∉ S := fun hkS => hST_S k hkS hkT
        exact (hAS k hkS).symm
      · intro k hkT
        rw [hmap]
        have hkS : k ∉ S := fun hkS => hST_S k hkS hkT
        change e.symm iy k = if k ∈ S then e.symm ix k
          else if k ∈ T then e.symm iy k else e.symm iz k
        rw [if_neg hkS, if_pos hkT]
      · exact hBT
      · -- AgreeOutside T (e.symm ix) (e.symm (mapφ iz)).
        intro k hkT
        rw [hmap]
        change e.symm ix k = if k ∈ S then e.symm ix k
          else if k ∈ T then e.symm iy k else e.symm iz k
        by_cases hkS : k ∈ S
        · rw [if_pos hkS]
        · by_cases hkT' : k ∈ T
          · exact absurd hkT' hkT
          · rw [if_neg hkS, if_neg hkT']
            exact hAS k hkS
    rw [hA_eq, hB_eq]
    ring

-- ============================================================================
-- Section: `tensorSupportedOn_noncommProd` — closure under noncomm products
-- ============================================================================

/-- The tensor-support analog of `supportedOn_noncommProd`. If every factor
`f i` is tensor-supported on `g i`, then the noncomm product is tensor-
supported on the union of the `g i`. The proof is induction on the noncomm
product via `Finset.noncommProd_induction`.

Source: arXiv:1411.4028v1 §II l.115–135 (tensor structure preserved by product). -/
theorem tensorSupportedOn_noncommProd {N : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Qubits.NQubitOp N) (g : ι → Finset (Fin N))
    (comm : (s : Set ι).Pairwise (Function.onFun Commute f))
    (h : ∀ i ∈ s, tensorSupportedOn (g i) (f i)) :
    tensorSupportedOn (s.biUnion g) (s.noncommProd f comm) := by
  classical
  refine Finset.noncommProd_induction s f comm
    (p := fun M => tensorSupportedOn (s.biUnion g) M) ?_ ?_ ?_
  · intro a b ha hb
    have := tensorSupportedOn_mul ha hb
    refine tensorSupportedOn_mono ?_ this
    intro k hk
    simp only [Finset.mem_union] at hk
    rcases hk with h1 | h2 <;> assumption
  · -- The unit `1` is tensor-supported on `∅`, hence on `s.biUnion g` by mono.
    exact tensorSupportedOn_mono (Finset.empty_subset _) tensorSupportedOn_one
  · intro i hi
    refine tensorSupportedOn_mono ?_ (h i hi)
    intro k hk
    exact Finset.mem_biUnion.mpr ⟨i, hi, hk⟩

-- ============================================================================
-- Section: Tensor-support strengthening of A2.2's bond-conjugation lemma
-- ============================================================================

/-- Per-bond cost-layer conjugation strengthened to `tensorSupportedOn`. Given a
tensor-supported `O` on `S`, conjugation by the bond exponential
`exp(-iγ Z_k Z_{nextSite k})` (possibly at different angles) lands in
`tensorSupportedOn (S ∪ {k, nextSite k})`.

This is the strict-predicate version of `supportedOn_conj_chainPair_exp` of
`LightCone.Spreading.lean`. It follows directly from
`tensorSupportedOn_exp_chainPairInteraction` + `tensorSupportedOn_mul`.

Source: arXiv:1411.4028v1 §II l.127–132 (per-layer support growth). -/
theorem tensorSupportedOn_conj_chainPair_exp {n : ℕ} {S : Finset (Fin n)}
    {O : Qubits.NQubitOp n} (hO : tensorSupportedOn S O) (γ γ' : ℝ) (k : Fin n) :
    tensorSupportedOn (S ∪ (({k} : Finset (Fin n)) ∪
        ({IsingModel.nextSite k} : Finset (Fin n))))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k) *
        O *
        NormedSpace.exp ((((-γ' : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k)) := by
  have h_left := tensorSupportedOn_exp_chainPairInteraction γ k
  have h_right := tensorSupportedOn_exp_chainPairInteraction γ' k
  have h₁ := tensorSupportedOn_mul h_left hO
  have h₂ := tensorSupportedOn_mul h₁ h_right
  refine tensorSupportedOn_mono ?_ h₂
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

-- ============================================================================
-- Section: Auxiliary — the cyclic predecessor `prevSite`
-- ============================================================================

/-- The cyclic predecessor `prevSite k = (k - 1) mod n` on the periodic ring.
This is the inverse of `IsingModel.nextSite` and is the right-hand site of the
bond `{prevSite k, k}`.

Defined locally inside `FGGClosure.lean` to keep this round self-contained;
matches the cyclic structure of `IsingModel.nextSite` from
`IsingModel.IsingHamiltonian`. -/
def prevSite {n : ℕ} (k : Fin n) : Fin n :=
  ⟨(k.val + n - 1) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) k.isLt)⟩

/-- Explicit value formula for `prevSite`. -/
theorem prevSite_val {n : ℕ} (k : Fin n) :
    (prevSite k).val = (k.val + n - 1) % n := rfl

/-- `nextSite` and `prevSite` are inverses (left-inverse direction). -/
theorem prevSite_nextSite {n : ℕ} (k : Fin n) :
    prevSite (IsingModel.nextSite k) = k := by
  apply Fin.ext
  simp only [prevSite_val, IsingModel.nextSite_val]
  -- Need: ((k.val + 1) % n + n - 1) % n = k.val
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  -- (k.val + 1) % n: either k.val + 1 if k.val + 1 < n, or 0 if k.val + 1 = n.
  by_cases h : k.val + 1 < n
  · -- (k.val + 1) % n = k.val + 1.
    rw [Nat.mod_eq_of_lt h]
    -- ((k.val + 1) + n - 1) % n = (k.val + n) % n = k.val % n = k.val.
    have hge : k.val + 1 + n ≥ 1 := by omega
    have : k.val + 1 + n - 1 = k.val + n := by omega
    rw [this]
    rw [Nat.add_mod_right]
    exact Nat.mod_eq_of_lt k.isLt
  · -- k.val + 1 = n (since k.val < n means k.val + 1 ≤ n; not <, means = n).
    have heq : k.val + 1 = n := by omega
    have : (k.val + 1) % n = 0 := by rw [heq]; exact Nat.mod_self n
    rw [this]
    -- (0 + n - 1) % n = (n - 1) % n = n - 1, and we need = k.val = n - 1.
    have hk : k.val = n - 1 := by omega
    rw [hk]
    have : 0 + n - 1 = n - 1 := by omega
    rw [this]
    exact Nat.mod_eq_of_lt (by omega)

/-- `nextSite` is a right-inverse of `prevSite`. -/
theorem nextSite_prevSite {n : ℕ} (k : Fin n) :
    IsingModel.nextSite (prevSite k) = k := by
  apply Fin.ext
  simp only [IsingModel.nextSite_val, prevSite_val]
  -- Need: ((k.val + n - 1) % n + 1) % n = k.val
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le _) k.isLt
  by_cases h0 : k.val = 0
  · -- prevSite 0 = (0 + n - 1) % n = (n - 1) % n = n - 1, then nextSite (n-1) = ((n-1)+1)%n = 0 = k.
    rw [h0]
    have : (0 + n - 1) % n = n - 1 := by
      have : 0 + n - 1 = n - 1 := by omega
      rw [this]; exact Nat.mod_eq_of_lt (by omega)
    rw [this]
    have : n - 1 + 1 = n := by omega
    rw [this]; exact Nat.mod_self n
  · -- k.val ≥ 1, so k.val + n - 1 < 2n - 1, but more usefully: (k.val + n - 1) % n = k.val - 1.
    have hk_pos : 1 ≤ k.val := by omega
    have hrw : k.val + n - 1 = (k.val - 1) + n := by omega
    rw [hrw, Nat.add_mod_right]
    have hk1_lt : k.val - 1 < n := by omega
    rw [Nat.mod_eq_of_lt hk1_lt]
    -- Now we have ((k.val - 1) + 1) % n = k.val.
    have : k.val - 1 + 1 = k.val := by omega
    rw [this]; exact Nat.mod_eq_of_lt k.isLt

-- ============================================================================
-- Section: Lemma 2 — tight cost-layer conjugation spread
-- ============================================================================

/-!
Lemma 2 of the FGG light-cone chain: conjugating a tensor-supported operator
by the full cost-layer exponential `exp(-iγ ∑_k Z_k Z_{nextSite k})` enlarges
the support by AT MOST one site on each end — namely, the support grows by
`S.image nextSite ∪ S.image prevSite`.

The tightness is the key fact that bounds the per-layer growth at ≤ 1 site per
side; this is precisely the "lightcone" property used in the FGG argument
(arXiv:1411.4028v1 §II l.130–132: "Any factors in U(C, γ₁) which do not involve
qubits j or k will commute through and cancel.").

The proof:
1. Factor the cost layer via `exp_chainPairInteraction_sum` into a noncommProd
   of single-bond exponentials.
2. Partition `Finset.univ` into bonds **touching** S (at least one endpoint in
   S) and bonds **disjoint** from S.
3. Each disjoint bond's exponential commutes with `O` by
   `tensorSupportedOn_commute_of_disjoint` (Lemma 1) and pairs with its
   `-γ`-twin to give the identity. The touching bonds remain and yield the
   ≤ 1-site-per-side growth.

This file proves the simpler equivalent form `cost_layer_γ · O · cost_layer_{-γ}`
which corresponds to the standard `U · O · U†` conjugation pattern (the
adjoint of `exp(-iγ H)` for Hermitian `H` is `exp(iγ H) = exp(-(-γ) i H)`).
-/

/-- A bond `k` **touches** `S` iff `k ∈ S` or `nextSite k ∈ S`. -/
private def bondTouches {n : ℕ} (S : Finset (Fin n)) (k : Fin n) : Prop :=
  k ∈ S ∨ IsingModel.nextSite k ∈ S

instance bondTouches_dec {n : ℕ} (S : Finset (Fin n)) (k : Fin n) :
    Decidable (bondTouches S k) := by
  unfold bondTouches
  infer_instance

private lemma bondUnion_subset {n : ℕ} {S : Finset (Fin n)} :
    (Finset.univ.filter (bondTouches S)).biUnion
      (fun k => ({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n))) ⊆
    S ∪ S.image IsingModel.nextSite ∪ S.image prevSite := by
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨k, hk_filter, hk⟩ := hx
  rw [Finset.mem_filter] at hk_filter
  obtain ⟨_, htouches⟩ := hk_filter
  simp only [Finset.mem_union, Finset.mem_singleton] at hk
  rcases hk with hxk | hxn
  · -- x = k. Either k ∈ S (so x ∈ S) or nextSite k ∈ S (so x = k = prevSite (nextSite k) ∈ image prevSite).
    rcases htouches with hkS | hnkS
    · simp only [Finset.mem_union]
      exact Or.inl (Or.inl (hxk ▸ hkS))
    · -- x = k = prevSite (nextSite k), nextSite k ∈ S.
      simp only [Finset.mem_union, Finset.mem_image]
      refine Or.inr ⟨IsingModel.nextSite k, hnkS, ?_⟩
      rw [prevSite_nextSite]; exact hxk.symm
  · -- x = nextSite k.
    rcases htouches with hkS | hnkS
    · -- k ∈ S, so x = nextSite k ∈ image nextSite.
      simp only [Finset.mem_union, Finset.mem_image]
      refine Or.inl (Or.inr ⟨k, hkS, ?_⟩)
      exact hxn.symm
    · -- nextSite k ∈ S, x = nextSite k.
      simp only [Finset.mem_union]
      exact Or.inl (Or.inl (hxn ▸ hnkS))

/-- For a bond `k` NOT touching `S`, the bond `{k, nextSite k}` is disjoint
from `S`. -/
private lemma bond_disjoint_of_not_touches {n : ℕ} {S : Finset (Fin n)} {k : Fin n}
    (hk : ¬ bondTouches S k) :
    Disjoint S
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n))) := by
  rw [Finset.disjoint_union_right]
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_singleton_right]
    intro h
    exact hk (Or.inl h)
  · rw [Finset.disjoint_singleton_right]
    intro h
    exact hk (Or.inr h)

/-- Auxiliary: the product over disjoint bonds commutes with `O`. -/
private lemma disjoint_noncommProd_commute_O {N : ℕ}
    {S : Finset (Fin N)} {O : Qubits.NQubitOp N}
    (hO : tensorSupportedOn S O) (γ : ℝ) :
    Commute O
      ((Finset.univ.filter (fun k => ¬ bondTouches S k)).noncommProd
        (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k))
        (fun i _ j _ _ =>
          (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)) := by
  classical
  -- Apply `noncommProd_commute` on the outer side (y = O commutes with each factor).
  refine Finset.noncommProd_commute _ _ _ O ?_
  intro k hk
  rw [Finset.mem_filter] at hk
  obtain ⟨_, hk_disj⟩ := hk
  -- The k-th factor is tensorSupportedOn `{k, nextSite k}`, disjoint from S.
  have hkexp := tensorSupportedOn_exp_chainPairInteraction γ k
  have hdisj := bond_disjoint_of_not_touches hk_disj
  exact (tensorSupportedOn_commute_of_disjoint hkexp hO hdisj.symm).symm

/-- Auxiliary: the product over disjoint bonds with `-γ` cancels its `γ` twin. -/
private lemma disjoint_noncommProd_cancel {N : ℕ} (S : Finset (Fin N)) (γ : ℝ) :
    ((Finset.univ.filter (fun k => ¬ bondTouches S k)).noncommProd
        (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k))
        (fun i _ j _ _ =>
          (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)) *
      ((Finset.univ.filter (fun k => ¬ bondTouches S k)).noncommProd
        (fun k => NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k))
        (fun i _ j _ _ =>
          (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)) =
    1 := by
  classical
  -- Combine via `noncommProd_mul_distrib`: ∏ (e^γ * e^(-γ)) = ∏ 1 = 1.
  set s := Finset.univ.filter (fun k => ¬ bondTouches S (n := N) k)
  set f : Fin N → Qubits.NQubitOp N :=
    fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) • IsingModel.chainPairInteraction k)
    with hf
  set g : Fin N → Qubits.NQubitOp N :=
    fun k => NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) •
      IsingModel.chainPairInteraction k)
    with hg
  have hcomm_ff : (s : Set (Fin N)).Pairwise (Function.onFun Commute f) := by
    intro i _ j _ _
    exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp
  have hcomm_gg : (s : Set (Fin N)).Pairwise (Function.onFun Commute g) := by
    intro i _ j _ _
    exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp
  have hcomm_gf : (s : Set (Fin N)).Pairwise (fun x y => Commute (g x) (f y)) := by
    intro i _ j _ _
    exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp
  have hdist := Finset.noncommProd_mul_distrib (s := s) f g hcomm_ff hcomm_gg hcomm_gf
  -- Each factor f k * g k = 1 because they are exp(-x) * exp(x) on commuting argument.
  have hone : ∀ k ∈ s, (f * g) k = 1 := by
    intro k _
    simp only [Pi.mul_apply, hf, hg]
    -- exp(-γ i C) * exp(γ i C) = exp(0) = 1 via Matrix.exp_add_of_commute on commuting C.
    set C : Qubits.NQubitOp N := IsingModel.chainPairInteraction k
    have hC_comm : Commute ((((-γ : ℝ) * Complex.I : ℂ)) • C) ((((-(-γ) : ℝ) * Complex.I : ℂ)) • C) :=
      (Commute.refl C).smul_left _ |>.smul_right _
    rw [show NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) • C) *
        NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) • C) =
        NormedSpace.exp (((((-γ : ℝ) * Complex.I : ℂ)) • C) +
          ((((-(-γ) : ℝ) * Complex.I : ℂ)) • C)) from
      (Matrix.exp_add_of_commute _ _ hC_comm).symm]
    rw [show ((((-γ : ℝ) * Complex.I : ℂ)) • C) + ((((-(-γ) : ℝ) * Complex.I : ℂ)) • C) =
        (((((-γ : ℝ) * Complex.I : ℂ)) + ((((-(-γ) : ℝ) * Complex.I : ℂ)))) • C) from
      (add_smul _ _ _).symm]
    rw [show (((((-γ : ℝ) * Complex.I : ℂ)) + ((((-(-γ) : ℝ) * Complex.I : ℂ)))) : ℂ) = 0 by
      push_cast; ring, zero_smul]
    exact NormedSpace.exp_zero
  -- Use `noncommProd_eq_pow_card` with `m = 1`.
  have hfg_one : s.noncommProd (f * g) (Finset.noncommProd_mul_distrib_aux hcomm_ff hcomm_gg hcomm_gf) = 1 := by
    rw [Finset.noncommProd_eq_pow_card s (f * g) _ 1 hone]
    simp
  rw [show s.noncommProd f hcomm_ff * s.noncommProd g hcomm_gg = _ from hdist.symm]
  exact hfg_one

/-- The product of single-bond cost exponentials over the bonds **touching**
`S`, at angle `γ`. This is the `Tγ` factor of the tight cost-layer
conjugation: the only bonds that survive after the disjoint bonds cancel. -/
def costTouchingProd {N : ℕ} (S : Finset (Fin N)) (γ : ℝ) :
    Qubits.NQubitOp N :=
  (Finset.univ.filter (fun k => k ∈ S ∨ IsingModel.nextSite k ∈ S)).noncommProd
    (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
      IsingModel.chainPairInteraction k))
    (fun i _ j _ _ =>
      (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)

/-- **Tight cost-layer conjugation, as an operator equality (piece (a)).**

For `O` tensor-supported on `S`, the cost-layer conjugation
`CB · O · CB'` (full cost exponential at `γ`, then `O`, then the inverse
cost exponential at `-γ`) equals `Tγ · O · Tm`, where `Tγ`, `Tm` are the
products over only the bonds **touching** `S`. The disjoint bonds commute
through `O` and cancel against their `-γ`/`+γ` twins.

This is the operator-level cancellation that underlies
`tensorSupportedOn_cost_layer_conj_tight` (which only used it to conclude
the support); exposing it as a reusable equality lets the window-block
recursion of `canonical_matrix_entry_match` expose the matching layer form.

Source: arXiv:1411.4028v1 §II l.130. -/
theorem cost_layer_conj_eq_touching {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) (γ : ℝ) :
    NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
      O *
      NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) •
        (∑ k : Fin N, IsingModel.chainPairInteraction k)) =
    costTouchingProd S γ * O * costTouchingProd S (-γ) := by
  classical
  -- Replace each cost-exp by its noncommProd factorization, then split into
  -- touching (`sT`) and disjoint (`sD`) bonds.
  rw [exp_chainPairInteraction_sum N γ, exp_chainPairInteraction_sum N (-γ)]
  set sT := Finset.univ.filter (fun k => k ∈ S ∨ IsingModel.nextSite k ∈ S) with hsT_def
  set sD := Finset.univ.filter (fun k => ¬ bondTouches S k) with hsD_def
  have hsT_eq : sT = Finset.univ.filter (bondTouches (n := N) S) := by
    rw [hsT_def]; rfl
  have hdisj : Disjoint sT sD := by
    rw [hsT_eq, hsD_def]; exact Finset.disjoint_filter_filter_not _ _ _
  have hunion : sT ∪ sD = Finset.univ := by
    rw [hsT_eq, hsD_def]; exact Finset.filter_union_filter_not_eq _ _
  set eγ : Fin N → Qubits.NQubitOp N := fun k =>
    NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) • IsingModel.chainPairInteraction k)
    with heγ_def
  set em : Fin N → Qubits.NQubitOp N := fun k =>
    NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) • IsingModel.chainPairInteraction k)
    with hem_def
  have eγ_pairwise : ∀ (s : Finset (Fin N)), (s : Set (Fin N)).Pairwise
      (Function.onFun Commute eγ) := by
    intro s i _ j _ _
    exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp
  have em_pairwise : ∀ (s : Finset (Fin N)), (s : Set (Fin N)).Pairwise
      (Function.onFun Commute em) := by
    intro s i _ j _ _
    exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp
  -- Split the full products into touching * disjoint.
  have hsplit_γ : (Finset.univ : Finset (Fin N)).noncommProd eγ (eγ_pairwise _) =
      sT.noncommProd eγ (eγ_pairwise _) * sD.noncommProd eγ (eγ_pairwise _) := by
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisj eγ
      (by intro i _ j _ _;
          exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)
  have hsplit_m : (Finset.univ : Finset (Fin N)).noncommProd em (em_pairwise _) =
      sT.noncommProd em (em_pairwise _) * sD.noncommProd em (em_pairwise _) := by
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisj em
      (by intro i _ j _ _;
          exact (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)
  rw [hsplit_γ, hsplit_m]
  set Tγ := sT.noncommProd eγ (eγ_pairwise _) with hTγ_def
  set Dγ := sD.noncommProd eγ (eγ_pairwise _) with hDγ_def
  set Tm := sT.noncommProd em (em_pairwise _) with hTm_def
  set Dm := sD.noncommProd em (em_pairwise _) with hDm_def
  -- `Dγ` commutes with `O`; `Dγ * Dm = 1`; reshuffle.
  have hDγ_comm_O : Commute O Dγ := by
    have h := disjoint_noncommProd_commute_O hO γ
    rw [hDγ_def, hsD_def]; exact h
  have hD_cancel : Dγ * Dm = 1 := by
    have h := disjoint_noncommProd_cancel S γ
    rw [hDγ_def, hDm_def, hsD_def]; exact h
  have hcomm_DT : Commute Dγ Tm := by
    have h_TmDγ : Commute Tm Dγ := by
      refine Finset.noncommProd_commute (s := sD) eγ _ Tm ?_
      intro k _
      have : Commute (eγ k) Tm := by
        refine Finset.noncommProd_commute (s := sT) em _ (eγ k) ?_
        intro k' _
        exact ((chainPairInteractions_commute k k').smul_left _ |>.smul_right _ |>.exp)
      exact this.symm
    exact h_TmDγ.symm
  have halg : (Tγ * Dγ) * O * (Tm * Dm) = Tγ * O * Tm := by
    calc (Tγ * Dγ) * O * (Tm * Dm)
        = Tγ * (Dγ * O) * (Tm * Dm) := by rw [mul_assoc Tγ Dγ O]
      _ = Tγ * (O * Dγ) * (Tm * Dm) := by rw [hDγ_comm_O]
      _ = ((Tγ * O) * Dγ) * (Tm * Dm) := by rw [← mul_assoc Tγ O Dγ]
      _ = (Tγ * O) * (Dγ * (Tm * Dm)) := by rw [mul_assoc (Tγ * O) Dγ (Tm * Dm)]
      _ = (Tγ * O) * ((Dγ * Tm) * Dm) := by rw [mul_assoc Dγ Tm Dm]
      _ = (Tγ * O) * ((Tm * Dγ) * Dm) := by rw [hcomm_DT]
      _ = (Tγ * O) * (Tm * (Dγ * Dm)) := by rw [mul_assoc Tm Dγ Dm]
      _ = (Tγ * O) * (Tm * 1) := by rw [hD_cancel]
      _ = (Tγ * O) * Tm := by rw [mul_one]
      _ = Tγ * O * Tm := rfl
  rw [halg]
  -- `Tγ = costTouchingProd S γ` and `Tm = costTouchingProd S (-γ)` definitionally.
  rfl

/-- The touching-bond cost product `costTouchingProd S γ` is tensor-supported
on the one-ring expansion `S ∪ S.image nextSite ∪ S.image prevSite`: each
touching bond `{k, nextSite k}` lands inside that one-ring. -/
theorem costTouchingProd_supportedOn {N : ℕ} (S : Finset (Fin N)) (γ : ℝ) :
    tensorSupportedOn
      (S ∪ S.image IsingModel.nextSite ∪ S.image prevSite)
      (costTouchingProd S γ) := by
  classical
  unfold costTouchingProd
  refine tensorSupportedOn_mono bondUnion_subset ?_
  have h_each : ∀ k ∈ Finset.univ.filter (bondTouches (n := N) S),
      tensorSupportedOn
        (({k} : Finset (Fin N)) ∪ ({IsingModel.nextSite k} : Finset (Fin N)))
        (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k)) := by
    intro k _; exact tensorSupportedOn_exp_chainPairInteraction γ k
  exact tensorSupportedOn_noncommProd (Finset.univ.filter (bondTouches (n := N) S))
    (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
      IsingModel.chainPairInteraction k))
    (fun k => ({k} : Finset (Fin N)) ∪ ({IsingModel.nextSite k} : Finset (Fin N)))
    _ h_each

/-- Composing the tight cost-layer conjugation: `Tγ · O · Tm` is tensor-
supported on the one-ring expansion of `S`. -/
theorem costTouchingProd_mul_supportedOn {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) (γ : ℝ) :
    tensorSupportedOn
      (S ∪ S.image IsingModel.nextSite ∪ S.image prevSite)
      (costTouchingProd S γ * O * costTouchingProd S (-γ)) := by
  have h1 := tensorSupportedOn_mul (costTouchingProd_supportedOn S γ) hO
  have h2 := tensorSupportedOn_mul h1 (costTouchingProd_supportedOn S (-γ))
  refine tensorSupportedOn_mono ?_ h2
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

/-- **FGG Lemma 2 (tight cost-layer conjugation spread).** Conjugating a
tensor-supported operator `O` on `S` by the full cost-layer exponential
enlarges the support by at most one site on each end of `S`. Specifically,
the resulting operator is tensor-supported on
`S ∪ S.image nextSite ∪ S.image prevSite`.

Strategy: factor the cost layer into a noncommutative product of single-bond
exponentials. Partition the bonds into those **touching** `S` and those
**disjoint**. Disjoint bonds commute with `O` (Lemma 1) and their `-γ`-twins
cancel pairwise. The touching bonds are supported within
`S ∪ image nextSite ∪ image prevSite`.

Source: arXiv:1411.4028v1 §II l.130 — "Any factors in U(C, γ₁) which do not
involve qubits j or k will commute through and cancel." -/
theorem tensorSupportedOn_cost_layer_conj_tight {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N}
    (hO : tensorSupportedOn S O) (γ : ℝ) :
    tensorSupportedOn
      (S ∪ S.image IsingModel.nextSite ∪ S.image prevSite)
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        O *
        NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k))) := by
  classical
  -- Reduce to the tight operator equality `CB · O · CB' = Tγ · O · Tm`
  -- (`cost_layer_conj_eq_touching`), then bound the support of the touching
  -- factors `Tγ = costTouchingProd S γ`, `Tm = costTouchingProd S (-γ)`.
  rw [cost_layer_conj_eq_touching hO γ]
  exact costTouchingProd_mul_supportedOn hO γ

-- ============================================================================
-- Section: Mixer-layer conjugation preserves tensor-support
-- ============================================================================

/-!
The mixer-layer unitary `exp(-iβ ∑_j X_j)` factors via `QAOA.exp_standardMixerOp`
into a noncomm product of single-site exponentials `e^{-iβ X_j}`. Conjugation by
this layer of a tensor-supported `O` on `S` PRESERVES the support `S` exactly
— no growth: single-site factors at `j ∈ S` stay within `S` (`{j} ⊆ S`); factors
at `j ∉ S` commute with `O` by Lemma 1 and cancel against their `-β` twin.

This contrasts with the cost layer (Lemma 2) where the bond exponentials
straddle pairs of sites, contributing the `± 1` lightcone growth on each side.
-/

/-- Auxiliary set: sites in `S`. -/
private lemma site_disjoint_of_not_mem {n : ℕ} {S : Finset (Fin n)} {j : Fin n}
    (hj : j ∉ S) : Disjoint S ({j} : Finset (Fin n)) := by
  rw [Finset.disjoint_singleton_right]; exact hj

/-- The product of single-site mixer exponentials over the sites **in** `S`,
at angle `β`. This is the `Tβ` factor of the tight mixer-layer conjugation:
the only single-site factors that survive after the outside-`S` factors
cancel. -/
def mixerTouchingProd {N : ℕ} (S : Finset (Fin N)) (β : ℝ) :
    Qubits.NQubitOp N :=
  (Finset.univ.filter (fun j : Fin N => j ∈ S)).noncommProd
    (fun j => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
    (fun i _ j _ _ =>
      (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)

/-- **Tight mixer-layer conjugation, as an operator equality (piece (a)).**

For `O` tensor-supported on `S`, the mixer-layer conjugation
`MB · O · MB'` equals `Tβ · O · Tm`, where `Tβ`, `Tm` are the products
over only the single-site factors **inside** `S`. The outside-`S` factors
commute through `O` and cancel against their `-β`/`+β` twins.

Companion of `cost_layer_conj_eq_touching`; together they expose both
layer factors of one QAOA layer in a window-supported form, enabling the
window-block layer-conjugation recursion.

Source: arXiv:1411.4028v1 §II l.132–135. -/
theorem mixer_layer_conj_eq_touching {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) (β : ℝ) :
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
      O *
      NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) =
    mixerTouchingProd S β * O * mixerTouchingProd S (-β) := by
  classical
  rw [QAOA.exp_standardMixerOp, QAOA.exp_standardMixerOp]
  set sT := Finset.univ.filter (fun j : Fin N => j ∈ S) with hsT_def
  set sD := Finset.univ.filter (fun j : Fin N => j ∉ S) with hsD_def
  have hdisj : Disjoint sT sD := by
    rw [hsT_def, hsD_def]; exact Finset.disjoint_filter_filter_not _ _ _
  have hunion : sT ∪ sD = Finset.univ := by
    rw [hsT_def, hsD_def]; exact Finset.filter_union_filter_not_eq _ _
  set eβ : Fin N → Qubits.NQubitOp N := fun j =>
    NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j)
    with heβ_def
  set em : Fin N → Qubits.NQubitOp N := fun j =>
    NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j)
    with hem_def
  have eβ_pairwise : ∀ (s : Finset (Fin N)), (s : Set (Fin N)).Pairwise
      (Function.onFun Commute eβ) := by
    intro s i _ j _ _
    exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp
  have em_pairwise : ∀ (s : Finset (Fin N)), (s : Set (Fin N)).Pairwise
      (Function.onFun Commute em) := by
    intro s i _ j _ _
    exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp
  have hsplit_β : (Finset.univ : Finset (Fin N)).noncommProd eβ (eβ_pairwise _) =
      sT.noncommProd eβ (eβ_pairwise _) * sD.noncommProd eβ (eβ_pairwise _) := by
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisj eβ
      (by intro i _ j _ _;
          exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)
  have hsplit_m : (Finset.univ : Finset (Fin N)).noncommProd em (em_pairwise _) =
      sT.noncommProd em (em_pairwise _) * sD.noncommProd em (em_pairwise _) := by
    rw [← hunion]
    exact Finset.noncommProd_union_of_disjoint hdisj em
      (by intro i _ j _ _;
          exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)
  -- Match the goal's mixer products (`mixerProdOn N univ`) to the `eβ`/`em`
  -- noncommProds, then split into touching * disjoint and reshuffle.
  change (Finset.univ : Finset (Fin N)).noncommProd eβ (eβ_pairwise _) * O *
      (Finset.univ : Finset (Fin N)).noncommProd em (em_pairwise _) = _
  rw [hsplit_β, hsplit_m]
  set Tβ := sT.noncommProd eβ (eβ_pairwise _) with hTβ_def
  set Dβ := sD.noncommProd eβ (eβ_pairwise _) with hDβ_def
  set Tm := sT.noncommProd em (em_pairwise _) with hTm_def
  set Dm := sD.noncommProd em (em_pairwise _) with hDm_def
  have hDβ_comm_O : Commute O Dβ := by
    refine Finset.noncommProd_commute _ _ _ O ?_
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨_, hj_out⟩ := hj
    have hexp := tensorSupportedOn_exp_localPauliX β j
    have hsite_disj := site_disjoint_of_not_mem hj_out
    exact (tensorSupportedOn_commute_of_disjoint hexp hO hsite_disj.symm).symm
  have hD_cancel : Dβ * Dm = 1 := by
    have hcomm_ff : (sD : Set (Fin N)).Pairwise (Function.onFun Commute eβ) :=
      eβ_pairwise sD
    have hcomm_gg : (sD : Set (Fin N)).Pairwise (Function.onFun Commute em) :=
      em_pairwise sD
    have hcomm_gf : (sD : Set (Fin N)).Pairwise (fun x y => Commute (em x) (eβ y)) := by
      intro i _ j _ _
      exact (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp
    have hdist := Finset.noncommProd_mul_distrib (s := sD) eβ em hcomm_ff hcomm_gg hcomm_gf
    have hone : ∀ j ∈ sD, (eβ * em) j = 1 := by
      intro j _
      simp only [Pi.mul_apply, heβ_def, hem_def]
      set Xj : Qubits.NQubitOp N := Qubits.localPauliX j with hXj_def
      have hX_comm : Commute ((((-β : ℝ) * Complex.I : ℂ)) • Xj) ((((-(-β) : ℝ) * Complex.I : ℂ)) • Xj) :=
        (Commute.refl Xj).smul_left _ |>.smul_right _
      rw [show NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Xj) *
          NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • Xj) =
          NormedSpace.exp (((((-β : ℝ) * Complex.I : ℂ)) • Xj) +
            ((((-(-β) : ℝ) * Complex.I : ℂ)) • Xj)) from
        (Matrix.exp_add_of_commute _ _ hX_comm).symm]
      rw [show ((((-β : ℝ) * Complex.I : ℂ)) • Xj) + ((((-(-β) : ℝ) * Complex.I : ℂ)) • Xj) =
          (((((-β : ℝ) * Complex.I : ℂ)) + ((((-(-β) : ℝ) * Complex.I : ℂ)))) • Xj) from
        (add_smul _ _ _).symm]
      rw [show (((((-β : ℝ) * Complex.I : ℂ)) + ((((-(-β) : ℝ) * Complex.I : ℂ)))) : ℂ) = 0 by
        push_cast; ring, zero_smul]
      exact NormedSpace.exp_zero
    have hfg_one : sD.noncommProd (eβ * em)
        (Finset.noncommProd_mul_distrib_aux hcomm_ff hcomm_gg hcomm_gf) = 1 := by
      rw [Finset.noncommProd_eq_pow_card sD (eβ * em) _ 1 hone]; simp
    have : sD.noncommProd eβ hcomm_ff * sD.noncommProd em hcomm_gg = 1 := by
      rw [← hdist]; exact hfg_one
    exact this
  have hcomm_DT : Commute Dβ Tm := by
    have h_TmDβ : Commute Tm Dβ := by
      refine Finset.noncommProd_commute (s := sD) eβ _ Tm ?_
      intro k _
      have : Commute (eβ k) Tm := by
        refine Finset.noncommProd_commute (s := sT) em _ (eβ k) ?_
        intro k' _
        exact ((Qubits.localPauliX_commute k k').smul_left _ |>.smul_right _ |>.exp)
      exact this.symm
    exact h_TmDβ.symm
  have halg : (Tβ * Dβ) * O * (Tm * Dm) = Tβ * O * Tm := by
    calc (Tβ * Dβ) * O * (Tm * Dm)
        = Tβ * (Dβ * O) * (Tm * Dm) := by rw [mul_assoc Tβ Dβ O]
      _ = Tβ * (O * Dβ) * (Tm * Dm) := by rw [hDβ_comm_O]
      _ = ((Tβ * O) * Dβ) * (Tm * Dm) := by rw [← mul_assoc Tβ O Dβ]
      _ = (Tβ * O) * (Dβ * (Tm * Dm)) := by rw [mul_assoc (Tβ * O) Dβ (Tm * Dm)]
      _ = (Tβ * O) * ((Dβ * Tm) * Dm) := by rw [mul_assoc Dβ Tm Dm]
      _ = (Tβ * O) * ((Tm * Dβ) * Dm) := by rw [hcomm_DT]
      _ = (Tβ * O) * (Tm * (Dβ * Dm)) := by rw [mul_assoc Tm Dβ Dm]
      _ = (Tβ * O) * (Tm * 1) := by rw [hD_cancel]
      _ = (Tβ * O) * Tm := by rw [mul_one]
      _ = Tβ * O * Tm := rfl
  rw [halg]
  -- `Tβ = mixerTouchingProd S β` and `Tm = mixerTouchingProd S (-β)` definitionally.
  rfl

/-- The touching-site mixer product `mixerTouchingProd S β` is tensor-
supported on `S`: each single-site factor at `j ∈ S` has support `{j} ⊆ S`. -/
theorem mixerTouchingProd_supportedOn {N : ℕ} (S : Finset (Fin N)) (β : ℝ) :
    tensorSupportedOn S (mixerTouchingProd S β) := by
  classical
  unfold mixerTouchingProd
  set sT := Finset.univ.filter (fun j : Fin N => j ∈ S) with hsT_def
  have sT_sub_S : sT ⊆ S := by
    intro k hk; rw [hsT_def, Finset.mem_filter] at hk; exact hk.2
  have h_each : ∀ k ∈ sT, tensorSupportedOn ({k} : Finset (Fin N))
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX k)) := by
    intro k _; exact tensorSupportedOn_exp_localPauliX β k
  have h := tensorSupportedOn_noncommProd sT
    (fun k => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX k))
    (fun k => ({k} : Finset (Fin N)))
    (fun i _ j _ _ => (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)
    h_each
  refine tensorSupportedOn_mono ?_ h
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨k, hk_sT, hxk⟩ := hx
  rw [Finset.mem_singleton] at hxk
  rw [hxk]; exact sT_sub_S hk_sT

/-- **Mixer-layer support preservation.** Conjugating a tensor-supported `O`
on `S` by the full mixer-layer exponential preserves the support exactly:
the result is tensor-supported on `S` (no growth).

Strategy: factor the mixer layer into a noncomm product of single-site
exponentials via `QAOA.exp_standardMixerOp`. Partition `Finset.univ` into
sites in `S` and sites outside `S`. Outside-`S` factors commute with `O`
(Lemma 1) and pair with their `-β` twins to give the identity. Inside-`S`
factors are supported within `S`, so the conjugation stays within `S`.

Source: arXiv:1411.4028v1 §II l.132–135 (P-layer composition; mixer layer
contributes no support growth). -/
theorem tensorSupportedOn_mixer_layer_conj {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N}
    (hO : tensorSupportedOn S O) (β : ℝ) :
    tensorSupportedOn S
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
        O *
        NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) := by
  -- Reduce to the tight operator equality `MB · O · MB' = Tβ · O · Tm`
  -- (`mixer_layer_conj_eq_touching`); the touching factors are supported on `S`.
  rw [mixer_layer_conj_eq_touching hO β]
  have h1 := tensorSupportedOn_mul (mixerTouchingProd_supportedOn S β) hO
  have h2 := tensorSupportedOn_mul h1 (mixerTouchingProd_supportedOn S (-β))
  refine tensorSupportedOn_mono ?_ h2
  intro x hx
  simp only [Finset.mem_union] at hx
  rcases hx with (h | h) | h <;> exact h

-- ============================================================================
-- Section: P-fold lightcone expansion `expand_by_n`
-- ============================================================================

/-- Single-step lightcone expansion: enlarge `S` by one ring of cyclic neighbors
on each side. -/
def expand_by_one {N : ℕ} (S : Finset (Fin N)) : Finset (Fin N) :=
  S ∪ S.image IsingModel.nextSite ∪ S.image prevSite

/-- P-fold lightcone expansion of `S`. -/
def expand_by_n {N : ℕ} (P : ℕ) (S : Finset (Fin N)) : Finset (Fin N) :=
  match P with
  | 0 => S
  | P + 1 => expand_by_one (expand_by_n P S)

lemma expand_by_n_zero {N : ℕ} (S : Finset (Fin N)) :
    expand_by_n 0 S = S := rfl

lemma expand_by_n_succ {N : ℕ} (P : ℕ) (S : Finset (Fin N)) :
    expand_by_n (P + 1) S = expand_by_one (expand_by_n P S) := rfl

-- ============================================================================
-- Section: Lemma 3 — P-layer QAOA conjugation spread
-- ============================================================================

/-!
Lemma 3 of the FGG light-cone chain: a single QAOA layer (cost + mixer) expands
the support of `O` by at most one cyclic-neighbor ring; iterating `P` layers
gives the lightcone window `expand_by_n P S`.

Source: arXiv:1411.4028v1 §II l.132–135 — "After P applications of the cost
and mixer layers, the support of the conjugated operator grows by at most P
sites on each side of the original support."
-/

/-- Single-layer QAOA conjugation: mixer composed with cost. Each layer
spreads the support by at most one ring of neighbors. -/
-- CHANGED (convention flip U·O·U† → U†·O·U): the single-layer conjugate now has
-- `U_layer† = cost† · mixer†` on the LEFT and `U_layer = mixer · cost` on the RIGHT.
-- Support spreading is direction-symmetric; we apply the cost-layer spread at angle
-- `-γ` (so the cost† factor is the `exp(γ)` side) and the mixer spread at angle `-β`.
private theorem tensorSupportedOn_one_layer_conj {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) (γ β : ℝ) :
    tensorSupportedOn (expand_by_one S)
      ((NormedSpace.exp ((((-(-γ) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        NormedSpace.exp ((((-(-β) : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) * O *
       (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)))) := by
  -- In the U†·O·U convention the factors touching `O` are the MIXER factors:
  -- innermost is mixer† · O · mixer, then cost† · (...) · cost wraps outside.
  -- Innermost: mixer† · O · mixer = exp(β)·O·exp(-β); spread by mixer layer at `-β`.
  -- `tensorSupportedOn_mixer_layer_conj hO (-β)` gives
  --   `exp(-(-β))·O·exp(-(--β)) = exp(β)·O·exp(-β)` supported on `S` (mixer preserves).
  have h_mixer := tensorSupportedOn_mixer_layer_conj hO (-β)
  -- Wrap with the cost layer at `-γ`: cost† · (mixer-conj) · cost.
  have h_cost := tensorSupportedOn_cost_layer_conj_tight h_mixer (-γ)
  -- Normalize the double/triple negations `- -θ`, `- - -θ` introduced by applying
  -- the lemmas at `-θ`, in both `h_cost` and the goal, then close by associativity.
  simp only [neg_neg] at h_cost ⊢
  rw [show expand_by_one S
      = S ∪ S.image IsingModel.nextSite ∪ S.image prevSite from rfl]
  -- Goal: tensorSupportedOn _ ((CB' * MB') * O * (MB * CB)) with all negs normalized.
  -- h_cost: tensorSupportedOn _ (CB' * (MB' * O * MB) * CB).
  set MB := NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) with hMB
  set CB := NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
    (∑ k : Fin N, IsingModel.chainPairInteraction k)) with hCB
  set CB' := NormedSpace.exp (((γ : ℝ) * Complex.I : ℂ) •
    (∑ k : Fin N, IsingModel.chainPairInteraction k)) with hCB'
  set MB' := NormedSpace.exp (((β : ℝ) * Complex.I : ℂ) • QAOA.standardMixerOp N) with hMB'
  have hreshuf : (CB' * MB') * O * (MB * CB) = CB' * (MB' * O * MB) * CB := by
    rw [mul_assoc CB' MB' O, ← mul_assoc (CB' * (MB' * O)) MB CB,
        mul_assoc CB' (MB' * O) MB, mul_assoc MB' O MB]
  rw [hreshuf]
  exact h_cost

/-- **FGG Lemma 3 (P-layer QAOA conjugation spread).** Conjugating a tensor-
supported `O` on `S` by the full `P`-layer QAOA unitary lands the result in
`tensorSupportedOn (expand_by_n P S)`. Each layer expands the support by at
most one cyclic-neighbor ring; `P` layers give a lightcone window of radius
`P` around `S`.

The `U_QAOA` here is built layer by layer: starting from `O`, apply the cost
layer at angle `γ p`, then the mixer layer at angle `β p`, for each
`p : Fin P`. The full conjugation can be expressed structurally without
defining `U_QAOA` explicitly: the inductive form `qaoaConjugate` below
captures the layered structure.

**WARNING — layer-order / reversed-angle convention.** The recursion peels
`Fin.last P` as the *innermost* conjugation, so `qaoaConjugate P γ β` realizes
`V(γ∘rev, β∘rev)† · O · V(γ∘rev, β∘rev)`, i.e. layer `P-1` is applied first. The
physical FORWARD QAOA conjugation `U† · O · U` (layer `0` applied first, matching
the state `psiTilde`) is only obtained when callers thread the REVERSED angle
arrays `(fun i ↦ γ i.rev, fun i ↦ β i.rev)`. For `P = 1` the reversal is a
no-op, but for `P ≥ 2` feeding FORWARD angles gives a silently-WRONG result
(numerically off; dev ≈ 3.7/4.1 at P=2/3). Always pass `.rev`-composed angles
when matching the physical forward QAOA state.

Source: arXiv:1411.4028v1 §II l.132–135. -/
def qaoaConjugate {N : ℕ} (P : ℕ) (γ β : Fin P → ℝ) (O : Qubits.NQubitOp N) :
    Qubits.NQubitOp N :=
  match P with
  | 0 => O
  | P + 1 =>
      let O_prev := qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O
      -- CHANGED: flipped conjugation direction U·O·U† → U†·O·U so that
      -- ⟨+|qaoaConjugate|+⟩ realizes the physical first moment ⟨ψ|O|ψ⟩ with ψ = U|+⟩.
      (NormedSpace.exp ((((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N)) *
       O_prev *
       (NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)))

/-- The QAOA-conjugate of a tensor-supported operator is tensor-supported on
the lightcone window `expand_by_n P S`. Inductive proof: each layer expands
support by `expand_by_one` (Lemma 2 on cost, mixer preservation), composing
to `expand_by_n P` after P layers. -/
theorem tensorSupportedOn_qaoa_conj {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O)
    (P : ℕ) (γ β : Fin P → ℝ) :
    tensorSupportedOn (expand_by_n P S) (qaoaConjugate P γ β O) := by
  induction P with
  | zero => simpa using hO
  | succ P ih =>
    -- Inductive step: apply one_layer_conj to the (P)-conjugated O.
    have hprev := ih (fun i => γ i.castSucc) (fun i => β i.castSucc)
    rw [expand_by_n_succ]
    -- Apply the single-layer conjugation lemma to hprev.
    change tensorSupportedOn (expand_by_one (expand_by_n P S)) (qaoaConjugate (P + 1) γ β O)
    unfold qaoaConjugate
    exact tensorSupportedOn_one_layer_conj hprev (γ (Fin.last P)) (β (Fin.last P))

end

end QAOA.IsingChain.UpperBound.LightCone
