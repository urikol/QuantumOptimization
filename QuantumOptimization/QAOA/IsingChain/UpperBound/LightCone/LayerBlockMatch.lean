import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.WindowBlock

/-!
# Layer-Conjugation Tight Decomposition — one QAOA layer through window-supported touching factors

This file assembles the **tight one-layer decomposition** of `qaoaConjugate`,
the reusable structural ingredient needed for the `P → P+1` window-block
recursion of `canonical_matrix_entry_match` (CanonicalMatching.lean line ~482).

Building on the two layer-tight operator equalities landed in
`FGGClosure.lean` this round —
* `cost_layer_conj_eq_touching` : `CB · O · CB' = costTouchingProd S γ · O · costTouchingProd S (-γ)`
* `mixer_layer_conj_eq_touching` : `MB · O · MB' = mixerTouchingProd S β · O · mixerTouchingProd S (-β)`
— and their support lemmas (`costTouchingProd_supportedOn`,
`mixerTouchingProd_supportedOn`), we express one QAOA layer's conjugation of a
**window-supported** operator entirely through factors that are themselves
supported on the one-ring expansion of the window. This is exactly the form
`windowBlock_mul` consumes (every factor window-supported), which is the
prerequisite for pushing the block through the layer.

## Status

The tight decomposition `qaoaConjugate_succ_eq_tight` is landed **sorry-free**
and axiom-clean. The remaining genuine FGG edge analysis — the
cross-dimension match of the touching layer products to the reduced-chain
layer block (including the PBC seam bond) — is *not* in this file; it is
discharged downstream by `NoncommProdBlock.lean` and `CanonicalMatching.lean`.

Source: FGG arXiv:1411.4028v1 §II l.130–135, §III.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: tight one-layer decomposition of `qaoaConjugate`
-- ============================================================================

/-- **Tight one-layer decomposition.** For `O` tensor-supported on a window
`S`, conjugating `O` by one full QAOA layer in the `U†·O·U` convention (cost†
outermost, mixer† innermost; mixer at `β₀`, cost at `γ₀`) equals the four-factor
product of touching layer products around `O`:

`(CB' · MB') · O · (MB · CB) = C_T' · (M_T' · O · M_T) · C_T`

where `M_T' = mixerTouchingProd S (-β₀)`, `M_T = mixerTouchingProd S β₀`
(both indexed by `S`, since the mixer is innermost and touches the support of `O`),
and `C_T' = costTouchingProd S (-γ₀)`, `C_T = costTouchingProd S γ₀` (indexed by
`S` — the support of the mixer-conjugate is still `S`, since the mixer preserves
support). The whole product is tensor-supported on the one-ring expansion of `S`
(the cost layer is the only one that spreads). This is the form `windowBlock_mul`
consumes. -/
theorem one_layer_conj_eq_tight {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) (γ₀ β₀ : ℝ) :
    (NormedSpace.exp ((((-(-γ₀) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        NormedSpace.exp ((((-(-β₀) : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) * O *
       (NormedSpace.exp ((((-β₀ : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ₀ : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k))) =
      costTouchingProd S (-γ₀) *
        (mixerTouchingProd S (-β₀) * O * mixerTouchingProd S β₀) *
        costTouchingProd S γ₀ := by
  -- Normalize the double negations `-(-θ)` in the LHS so the touching lemmas
  -- (applied at angle `-θ`, also normalized) line up.
  simp only [neg_neg]
  -- Goal: (exp(γ₀·C) * exp(β₀·M)) * O * (exp(-β₀·M) * exp(-γ₀·C))
  --       = costTouchingProd S (-γ₀) * (mixerTouchingProd S (-β₀) * O * mixerTouchingProd S β₀)
  --         * costTouchingProd S γ₀
  -- The touching lemmas (normalized) we will use:
  have hmix := mixer_layer_conj_eq_touching hO (-β₀)
  simp only [neg_neg] at hmix
  -- hmix : exp(β₀·M)·O·exp(-β₀·M) = mixerTouchingProd S (-β₀) · O · mixerTouchingProd S β₀
  -- The mixer conjugate is supported on `S` (mixer preserves support).
  have hMO : tensorSupportedOn S
      (mixerTouchingProd S (-β₀) * O * mixerTouchingProd S β₀) := by
    have h := tensorSupportedOn_mixer_layer_conj hO (-β₀)
    simp only [neg_neg] at h
    rwa [hmix] at h
  have hcost := cost_layer_conj_eq_touching hMO (-γ₀)
  simp only [neg_neg] at hcost
  -- hcost : exp(γ₀·C)·(mixer-conj)·exp(-γ₀·C)
  --         = costTouchingProd S (-γ₀) · (mixer-conj) · costTouchingProd S γ₀
  -- Reassociate the LHS to expose the mixer-conjugation inside the cost-conjugation,
  -- then rewrite by the mixer and cost touching identities.
  have hreshuf :
      (NormedSpace.exp (((γ₀ : ℝ) * Complex.I : ℂ) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
          NormedSpace.exp (((β₀ : ℝ) * Complex.I : ℂ) • QAOA.standardMixerOp N)) * O *
         (NormedSpace.exp ((((-β₀ : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N) *
          NormedSpace.exp ((((-γ₀ : ℝ) * Complex.I : ℂ)) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k)))
        = NormedSpace.exp (((γ₀ : ℝ) * Complex.I : ℂ) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
          (NormedSpace.exp (((β₀ : ℝ) * Complex.I : ℂ) • QAOA.standardMixerOp N) * O *
            NormedSpace.exp ((((-β₀ : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) *
          NormedSpace.exp ((((-γ₀ : ℝ) * Complex.I : ℂ)) •
            (∑ k : Fin N, IsingModel.chainPairInteraction k)) := by
    set a := NormedSpace.exp (((γ₀ : ℝ) * Complex.I : ℂ) •
      (∑ k : Fin N, IsingModel.chainPairInteraction k))
    set b := NormedSpace.exp (((β₀ : ℝ) * Complex.I : ℂ) • QAOA.standardMixerOp N)
    set c := NormedSpace.exp ((((-β₀ : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)
    set d := NormedSpace.exp ((((-γ₀ : ℝ) * Complex.I : ℂ)) •
      (∑ k : Fin N, IsingModel.chainPairInteraction k))
    rw [mul_assoc a b O, ← mul_assoc (a * (b * O)) c d,
        mul_assoc a (b * O) c, mul_assoc b O c]
  rw [hreshuf, hmix, hcost]

/-- **Tight `qaoaConjugate` recursion (operator form, `U†·O·U` convention).**
For `O` tensor-supported on `S`, the depth-`P+1` QAOA conjugate decomposes as
the tight one-layer wrap of the depth-`P` conjugate, with cost† OUTERMOST and
mixer† INNERMOST:

`qaoaConjugate (P+1) γ β O =
   C_T' · (M_T' · qaoaConjugate P γ.castSucc β.castSucc O · M_T) · C_T`

where `M_T'/M_T` are mixer touching-products and `C_T'/C_T` cost touching-products,
ALL indexed by the depth-`P` window `expand_by_n P S` (the mixer is innermost and
touches the support of the depth-`P` conjugate; the cost wraps the mixer-conjugate,
which is still supported on `expand_by_n P S` because the mixer preserves support).
Every factor is window-supported on `expand_by_n (P+1) S`, so `windowBlock_mul`
applies to push the block through the product — the entry point for the
window-block layer recursion. -/
theorem qaoaConjugate_succ_eq_tight {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O)
    (P : ℕ) (γ β : Fin (P + 1) → ℝ) :
    qaoaConjugate (P + 1) γ β O =
      costTouchingProd (expand_by_n P S) (-(γ (Fin.last P))) *
        (mixerTouchingProd (expand_by_n P S) (-(β (Fin.last P))) *
          qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O *
          mixerTouchingProd (expand_by_n P S) (β (Fin.last P))) *
        costTouchingProd (expand_by_n P S) (γ (Fin.last P)) := by
  -- The depth-P conjugate is supported on `expand_by_n P S` (Lemma 3).
  have hprev : tensorSupportedOn (expand_by_n P S)
      (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O) :=
    tensorSupportedOn_qaoa_conj hO P _ _
  -- Unfold one layer of `qaoaConjugate` (new convention: cost† · mixer† outermost-left,
  -- mixer · cost outermost-right), then apply the tight one-layer lemma.
  change (NormedSpace.exp ((((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N)) *
       qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O *
       (NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          QAOA.standardMixerOp N) *
        NormedSpace.exp ((((-γ (Fin.last P) : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k))) = _
  exact one_layer_conj_eq_tight hprev (γ (Fin.last P)) (β (Fin.last P))

-- ============================================================================
-- Section: window-block recursion (within fixed dimension `2(P+1)+2`)
-- ============================================================================

/-- `expand_by_n (P+1) S = expand_by_one (expand_by_n P S)` (restated for
local convenience). -/
private theorem expand_succ_eq {N : ℕ} (P : ℕ) (S : Finset (Fin N)) :
    expand_by_n (P + 1) S = expand_by_one (expand_by_n P S) := rfl

/-- `expand_by_n P S ⊆ expand_by_n (P+1) S`: one extra ring of expansion. -/
theorem expand_by_n_subset_succ {N : ℕ} (P : ℕ) (S : Finset (Fin N)) :
    expand_by_n P S ⊆ expand_by_n (P + 1) S := by
  rw [expand_succ_eq]
  intro x hx
  unfold expand_by_one
  exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)

/-- Same-window product: if `A, B` are both tensor-supported on `W`, so is
`A * B` (the union `W ∪ W = W` collapses). -/
theorem tensorSupportedOn_mul_same {N : ℕ} {W : Finset (Fin N)}
    {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn W A) (hB : tensorSupportedOn W B) :
    tensorSupportedOn W (A * B) := by
  have h := tensorSupportedOn_mul hA hB
  rwa [Finset.union_self] at h

/-- **Window-block recursion (fixed dimension).** Taking the window block of
the depth-`P+1` QAOA conjugate over the depth-`P+1` window splits — entirely
inside dimension `m = card (expand_by_n (P+1) S)` — into the product of the
window blocks of the five tight layer factors. This is the
`windowBlock_mul`-driven push of the block through `qaoaConjugate_succ_eq_tight`:
all factors are tensor-supported on the depth-`P+1` window, so block
multiplicativity applies factor by factor.

This is the dimension-stable half of the layer-conjugation-block recursion;
the remaining (genuinely structural) half is matching the factor blocks of the
full chain to those of the reduced chain across `Fin N ↔ Fin (2P+4)`. -/
theorem windowBlock_qaoaConjugate_succ {N m : ℕ} {S : Finset (Fin N)} (P : ℕ)
    (ε : Fin m ≃ (expand_by_one (expand_by_n P S)))
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O)
    (γ β : Fin (P + 1) → ℝ) :
    windowBlock ε (qaoaConjugate (P + 1) γ β O) =
      windowBlock ε (costTouchingProd (expand_by_n P S) (-(γ (Fin.last P)))) *
        (windowBlock ε (mixerTouchingProd (expand_by_n P S) (-(β (Fin.last P)))) *
          windowBlock ε
            (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O) *
          windowBlock ε (mixerTouchingProd (expand_by_n P S) (β (Fin.last P)))) *
        windowBlock ε (costTouchingProd (expand_by_n P S) (γ (Fin.last P))) := by
  classical
  -- All five factors are tensor-supported on the depth-`P+1` window
  -- `expand_by_one (expand_by_n P S)`.
  -- mixer factors (innermost): touching set `expand_by_n P S`, supported on its
  -- one-ring `expand_by_one (expand_by_n P S)` = the window.
  have hM : tensorSupportedOn (expand_by_one (expand_by_n P S))
      (mixerTouchingProd (expand_by_n P S) (β (Fin.last P))) := by
    have h := mixerTouchingProd_supportedOn (expand_by_n P S) (β (Fin.last P))
    exact tensorSupportedOn_mono (by
      rw [← expand_succ_eq]; exact expand_by_n_subset_succ P S) h
  have hM' : tensorSupportedOn (expand_by_one (expand_by_n P S))
      (mixerTouchingProd (expand_by_n P S) (-(β (Fin.last P)))) := by
    have h := mixerTouchingProd_supportedOn (expand_by_n P S) (-(β (Fin.last P)))
    exact tensorSupportedOn_mono (by
      rw [← expand_succ_eq]; exact expand_by_n_subset_succ P S) h
  -- cost factors (outermost): supported on one-ring of `expand_by_n P S` = the window.
  have hC : tensorSupportedOn (expand_by_one (expand_by_n P S))
      (costTouchingProd (expand_by_n P S) (γ (Fin.last P))) :=
    costTouchingProd_supportedOn _ _
  have hC' : tensorSupportedOn (expand_by_one (expand_by_n P S))
      (costTouchingProd (expand_by_n P S) (-(γ (Fin.last P)))) :=
    costTouchingProd_supportedOn _ _
  -- middle factor: supported on `expand_by_n P S ⊆ window`.
  have hsub : expand_by_n P S ⊆ expand_by_one (expand_by_n P S) := by
    rw [← expand_succ_eq]; exact expand_by_n_subset_succ P S
  have hOprev : tensorSupportedOn (expand_by_one (expand_by_n P S))
      (qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O) :=
    tensorSupportedOn_mono hsub (tensorSupportedOn_qaoa_conj hO P _ _)
  -- products that arise in the associated decomposition (new order:
  -- `C_T' · (M_T' · conjP · M_T) · C_T`).
  have hMO := tensorSupportedOn_mul_same hM' hOprev
  have hMOM := tensorSupportedOn_mul_same hMO hM
  have hCMOM := tensorSupportedOn_mul_same hC' hMOM
  -- Rewrite the conjugate via the tight recursion, then push the block through.
  rw [qaoaConjugate_succ_eq_tight hO P γ β]
  rw [windowBlock_mul ε hCMOM hC]
  rw [windowBlock_mul ε hC' hMOM]
  rw [windowBlock_mul ε hMO hM]
  rw [windowBlock_mul ε hM' hOprev]

end

end QAOA.IsingChain.UpperBound.LightCone
