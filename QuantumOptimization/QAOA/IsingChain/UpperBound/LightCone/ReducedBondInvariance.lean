import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.StateInvariance
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.StructuralIdentification

/-!
# Reduced-Bond Translation Invariance — `j_s`-parametric light-cone via per-bond collapse to bond 0

This file delivers the **`j_s`-parametric** light-cone structural
identification that the Bridge step consumes, in the
simplified form licensed by numerical validation: rather than re-proving a
genuinely different matrix-entry calculation for each reduced bond
`k : Fin (2P+2)`, we exploit the **translation invariance of the PBC
reduced chain** to collapse every per-bond reduced expectation onto the
single canonical reduced bond `0`. The single canonical full↔reduced
matching (the FGG light-cone predicate `LightconeStructuralMatching` at
`j_s = ⟨N/2,_⟩`, already packaged in `StructuralIdentification.lean`) then
suffices to bridge ALL reduced bonds to the common full-chain bond
expectation.

## What numerical validation established (and we exploit)

Numerical validation confirmed (deviations ~1e-15, independent of
bond index): every per-bond PBC reduced expectation
`⟨+|·U_PBC†·cP(k)·U_PBC·|+⟩` equals the common full-chain bond expectation
`F`, AND equals every other reduced `P_k`. So the `j_s`-parametric LIGHTCONE
factors as:

  (i)  reduced-bond translation invariance — `⟨+|·U_PBC†·cP(k)·U_PBC·|+⟩`
       is independent of `k` (PBC reduced-chain analogue of
       `first_moment_cyclic_invariance`), proved here SORRY-FREE; PLUS
  (ii) the single canonical matching `qaoa_full_eq_reduced_on_lightcone_closed`
       (full `j_s` ↔ reduced `0`), already in `StructuralIdentification.lean`.

This is the "stronger than needed" shortcut: it removes the per-`k`
matrix-entry burden (~450 LOC in the naive multi-`j_s` plan) entirely; the
FGG matrix-entry black-box `LightconeStructuralMatching` is only ever
instantiated at the single canonical bond.

## Mathematical content of the reduced-bond invariance

`U_PBC = qaoaConjugate P γ β` on the reduced chain `Fin (2P+2)` uses the
PBC cost sum `Σ_{k:Fin(2P+2)} cP(k)` and the `+Σ X` mixer (no `-β`
correction — that enters only later at the ABC crossing, plan
"Mixer-sign convention"). Both layers are invariant under the cyclic
translation `T := T_op_full (2P+1)` (note `2P+2 = (2P+1)+1`):

  `T† · (Σ_k cP(k)) · T = Σ_k cP(k)`   (`T_conj_full_chainPairInteraction_sum`)
  `T† · standardMixerOp · T = standardMixerOp`   (`T_conj_full_standardMixer`)

so `T` commutes with every `qaoaConjugate` exponential factor, giving the
operator identity

  `T† · (qaoaConjugate P γ β O) · T = qaoaConjugate P γ β (T† · O · T)`.

Specialized to `O = cP(k)` and using `T† · cP(k) · T = cP(nextSite k)`
(`T_conj_full_chainPairInteraction`) and `T · |+⟩ = |+⟩`
(`T_op_full_mulVec_uniformKet`), the `|+⟩`-sandwich expectation is
invariant under `k ↦ nextSite k`, hence (by iterating the bijection)
independent of `k`.

Sources:
* arXiv:1411.4028v1 §II l.113–134 (FGG operator-spreading, `j_s`-agnostic).
* arXiv:1906.08948v2 §IV l.620–702 (chain reduction + full-chain
  translation invariance; the reduced-chain analogue here is the routine
  PBC mirror).

## Public deliverables

* `qaoaConjugate_T_conj` — operator-level: `T† · qaoaConjugate(O) · T =
  qaoaConjugate(T† · O · T)`.
* `uniformKet_expectation_T_conj` — `⟨+|·(T†·X·T)·|+⟩ = ⟨+|·X·|+⟩`.
* `reducedChainQAOAConj_at` — `j_s`-parametric reduced-bond conjugate at
  bond `k : Fin (2P+2)`.
* `reducedChainQAOAConj_at_expectation_indep` — the reduced-bond
  expectation is independent of the bond `k` (the load-bearing shortcut).
* `reducedChainQAOAConj_at_expectation_eq_zero` — every reduced bond's
  expectation equals the canonical bond-`0` expectation.
* `qaoa_full_eq_reduced_on_lightcone_at` — the `j_s`-parametric LIGHTCONE
  identity the Bridge consumes: full `j_s` (with canonical matching) ↔
  reduced bond `k` (any `k`).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: `T` commutes with the `qaoaConjugate` exponential factors
-- ============================================================================

/-- `T_op_full M` commutes with the cost-layer exponential
`exp((-γ·I) • Σ_k cP(k))` of `qaoaConjugate`. -/
theorem T_op_full_commutes_costFactor (M : ℕ) (γc : ℂ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        NormedSpace.exp (γc • (∑ k : Fin (M + 1), IsingModel.chainPairInteraction k)) =
      NormedSpace.exp (γc • (∑ k : Fin (M + 1), IsingModel.chainPairInteraction k)) *
        (T_op_full M : Qubits.NQubitOp (M + 1)) :=
  exp_commute_of_conj_full (T_op_full M) _ γc
    (T_conj_full_chainPairInteraction_sum M)

/-- `T_op_full M` commutes with the mixer-layer exponential
`exp((-β·I) • standardMixerOp)` of `qaoaConjugate`. -/
theorem T_op_full_commutes_mixerFactor (M : ℕ) (βc : ℂ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        NormedSpace.exp (βc • QAOA.standardMixerOp (M + 1)) =
      NormedSpace.exp (βc • QAOA.standardMixerOp (M + 1)) *
        (T_op_full M : Qubits.NQubitOp (M + 1)) :=
  exp_commute_of_conj_full (T_op_full M) _ βc (T_conj_full_standardMixer M)

/-- From a commutation `T · A = A · T` we get the "pull `T†` past `A`" form
`T† · A = A · T†`. (`T†` is the two-sided inverse of `T`.) -/
private theorem adj_commute_of_commute (M : ℕ)
    (A : Qubits.NQubitOp (M + 1))
    (hcomm : (T_op_full M : Qubits.NQubitOp (M + 1)) * A =
      A * (T_op_full M : Qubits.NQubitOp (M + 1))) :
    (T_op_full M : Qubits.NQubitOp (M + 1))† * A =
      A * (T_op_full M : Qubits.NQubitOp (M + 1))† := by
  have hL := (T_op_full M).unitary_left
  have hR := (T_op_full M).unitary_right
  -- A * T† = (T† * T) * A * T† = T† * (T * A) * T† = T† * (A * T) * T†
  --        = T† * A * (T * T†) = T† * A.
  symm
  calc A * (T_op_full M : Qubits.NQubitOp (M + 1))†
      = ((T_op_full M : Qubits.NQubitOp (M + 1))† *
          (T_op_full M : Qubits.NQubitOp (M + 1))) * A *
          (T_op_full M : Qubits.NQubitOp (M + 1))† := by
        rw [hL, Matrix.one_mul]
    _ = (T_op_full M : Qubits.NQubitOp (M + 1))† *
          (((T_op_full M : Qubits.NQubitOp (M + 1)) * A) *
            (T_op_full M : Qubits.NQubitOp (M + 1))†) := by
        simp only [Matrix.mul_assoc]
    _ = (T_op_full M : Qubits.NQubitOp (M + 1))† *
          ((A * (T_op_full M : Qubits.NQubitOp (M + 1))) *
            (T_op_full M : Qubits.NQubitOp (M + 1))†) := by
        rw [hcomm]
    _ = (T_op_full M : Qubits.NQubitOp (M + 1))† * A *
          ((T_op_full M : Qubits.NQubitOp (M + 1)) *
            (T_op_full M : Qubits.NQubitOp (M + 1))†) := by
        simp only [Matrix.mul_assoc]
    _ = (T_op_full M : Qubits.NQubitOp (M + 1))† * A := by
        rw [hR, Matrix.mul_one]

-- ============================================================================
-- Section: operator-level T-conjugation of `qaoaConjugate`
-- ============================================================================

/-- **T-conjugation passes through `qaoaConjugate`.**

`T† · qaoaConjugate P γ β O · T = qaoaConjugate P γ β (T† · O · T)`.

Each cost/mixer exponential layer of `qaoaConjugate` is `T`-invariant
(`T_op_full_commutes_costFactor` / `T_op_full_commutes_mixerFactor`), so
the conjugating unitary commutes with `T`; conjugation by `T` therefore
acts only on the central operator `O`. Proved by induction on `P`. -/
theorem qaoaConjugate_T_conj (M P : ℕ) (γ β : Fin P → ℝ)
    (O : Qubits.NQubitOp (M + 1)) :
    (T_op_full M : Qubits.NQubitOp (M + 1))† *
        qaoaConjugate P γ β O *
        (T_op_full M : Qubits.NQubitOp (M + 1)) =
      qaoaConjugate P γ β
        ((T_op_full M : Qubits.NQubitOp (M + 1))† * O *
          (T_op_full M : Qubits.NQubitOp (M + 1))) := by
  induction P with
  | zero =>
    -- `qaoaConjugate 0 γ β O = O` on both sides, so the goal is `rfl`.
    rfl
  | succ P ih =>
    -- Abbreviations for the four exponential factors.
    set T := (T_op_full M : Qubits.NQubitOp (M + 1)) with hT
    set MB := NormedSpace.exp ((((-β (Fin.last P) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp (M + 1)) with hMB
    set CB := NormedSpace.exp ((((-γ (Fin.last P) : ℝ) * Complex.I : ℂ)) •
        (∑ k : Fin (M + 1), IsingModel.chainPairInteraction k)) with hCB
    set CB' := NormedSpace.exp ((((-(-γ (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
        (∑ k : Fin (M + 1), IsingModel.chainPairInteraction k)) with hCB'
    set MB' := NormedSpace.exp ((((-(-β (Fin.last P)) : ℝ) * Complex.I : ℂ)) •
        QAOA.standardMixerOp (M + 1)) with hMB'
    set Oprev := qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc) O
      with hOprev
    -- New convention `U†·O·U`: left group is `CB' * MB'`, right group is `MB * CB`.
    have hLeft : T† * (CB' * MB') = (CB' * MB') * T† := by
      have hCB'_cadj : T† * CB' = CB' * T† :=
        adj_commute_of_commute M CB' (T_op_full_commutes_costFactor M _)
      have hMB'_cadj : T† * MB' = MB' * T† :=
        adj_commute_of_commute M MB' (T_op_full_commutes_mixerFactor M _)
      rw [← Matrix.mul_assoc, hCB'_cadj, Matrix.mul_assoc, hMB'_cadj, ← Matrix.mul_assoc]
    have hRight : (MB * CB) * T = T * (MB * CB) := by
      have hCB_cT : T * CB = CB * T := T_op_full_commutes_costFactor M _
      have hMB_cT : T * MB = MB * T := T_op_full_commutes_mixerFactor M _
      rw [Matrix.mul_assoc, ← hCB_cT, ← Matrix.mul_assoc, ← hMB_cT, Matrix.mul_assoc]
    -- Unfold qaoaConjugate (P+1) in the new factor order.
    change T† * ((CB' * MB') * Oprev * (MB * CB)) * T =
      qaoaConjugate (P + 1) γ β (T† * O * T)
    -- RHS unfolds to (CB' * MB') * (qaoaConjugate P ... (T† * O * T)) * (MB * CB).
    rw [show qaoaConjugate (P + 1) γ β (T† * O * T) =
          (CB' * MB') *
            qaoaConjugate P (fun i => γ i.castSucc) (fun i => β i.castSucc)
              (T† * O * T) *
            (MB * CB) from rfl]
    rw [← ih]
    -- LHS reshuffle: T† * (CB'*MB') * Oprev * (MB*CB) * T
    --    = (CB'*MB') * (T† * Oprev * T) * (MB*CB).
    -- First move T† rightwards: T† * (CB'*MB') = (CB'*MB') * T†.
    rw [show T† * ((CB' * MB') * Oprev * (MB * CB)) * T =
          (T† * (CB' * MB')) * Oprev * (MB * CB) * T by
            simp only [Matrix.mul_assoc]]
    rw [hLeft]
    -- Then move T leftwards: (MB*CB) * T = T * (MB*CB).
    rw [show (CB' * MB') * T† * Oprev * (MB * CB) * T =
          (CB' * MB') * T† * Oprev * ((MB * CB) * T) by
            simp only [Matrix.mul_assoc]]
    rw [hRight]
    -- Now pure associativity gives the target (unfold the `set` binding `Oprev`).
    rw [hOprev]
    simp only [Matrix.mul_assoc]

-- ============================================================================
-- Section: expectation invariance on the uniform `|+⟩` state
-- ============================================================================

/-- `T_op_full M · |+⟩ = |+⟩` in `Op × Ket` form. -/
theorem T_op_full_mul_uniformKet (M : ℕ) :
    (T_op_full M : Qubits.NQubitOp (M + 1)) *
        QAOA.uniformKet (Qubits.NQubitDim (M + 1)) =
      QAOA.uniformKet (Qubits.NQubitDim (M + 1)) := by
  apply Ket.ext
  intro i
  rw [op_mul_ket_vec]
  exact congrFun (T_op_full_mulVec_uniformKet M) i

/-- `⟨+| · T† = ⟨+|`: the bra version of `T · |+⟩ = |+⟩`. -/
theorem uniformKet_dag_mul_T_adj (M : ℕ) :
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (T_op_full M : Qubits.NQubitOp (M + 1))† =
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag := by
  ext j
  show ((QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
      (T_op_full M : Qubits.NQubitOp (M + 1))†).vec j =
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag.vec j
  rw [bra_mul_op_vec]
  simp only [Ket.dag_vec, Matrix.conjTranspose_apply]
  -- Σ_i star(ψ_i) · star(T_{j,i}) = star(Σ_i T_{j,i} · ψ_i) = star((T ψ)_j) = star(ψ_j).
  have hvec : ((T_op_full M : Qubits.NQubitOp (M + 1)) *
      QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec j =
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec j := by
    rw [T_op_full_mul_uniformKet]
  rw [op_mul_ket_vec] at hvec
  change (T_op_full M : Qubits.NQubitOp (M + 1)).mulVec
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec j =
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec j at hvec
  have hsum : ∑ i, (T_op_full M : Qubits.NQubitOp (M + 1)) j i *
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec i =
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec j := hvec
  rw [show ∑ i, (starRingEnd ℂ) ((QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec i) *
          star ((T_op_full M : Qubits.NQubitOp (M + 1)) j i) =
        (starRingEnd ℂ)
          (∑ i, (T_op_full M : Qubits.NQubitOp (M + 1)) j i *
            (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).vec i) from by
    rw [map_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [map_mul, mul_comm]
    rfl]
  rw [hsum]

/-- **Expectation invariance under T-conjugation on `|+⟩`.**

`⟨+| · (T† · X · T) · |+⟩ = ⟨+| · X · |+⟩` for any operator `X`, since
`T · |+⟩ = |+⟩` (and dually `⟨+| · T† = ⟨+|`). -/
theorem uniformKet_expectation_T_conj (M : ℕ) (Xop : Qubits.NQubitOp (M + 1)) :
    (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (((T_op_full M : Qubits.NQubitOp (M + 1))† * Xop *
            (T_op_full M : Qubits.NQubitOp (M + 1))) *
          QAOA.uniformKet (Qubits.NQubitDim (M + 1))) =
      (QAOA.uniformKet (Qubits.NQubitDim (M + 1))).dag *
        (Xop * QAOA.uniformKet (Qubits.NQubitDim (M + 1))) := by
  set u := QAOA.uniformKet (Qubits.NQubitDim (M + 1)) with hu
  set T := (T_op_full M : Qubits.NQubitOp (M + 1)) with hT
  have hTu : T * u = u := T_op_full_mul_uniformKet M
  have hbra : u.dag * T† = u.dag := uniformKet_dag_mul_T_adj M
  -- Reassociate the ket side: (T† * Xop) * (T * u) = (T† * Xop) * u = T† * (Xop * u).
  have hket : (T† * Xop * T) * u = T† * (Xop * u) := by
    rw [op_mul_op_mul_ket (T† * Xop) T u, hTu, op_mul_op_mul_ket]
  rw [hket]
  -- Reassociate the bra side: u.dag * (T† * (Xop * u)) = (u.dag * T†) * (Xop * u) = u.dag * (Xop * u).
  rw [← braop_mul_ket u.dag T† (Xop * u), hbra]

-- ============================================================================
-- Section: `j_s`-parametric reduced-bond conjugate + translation invariance
-- ============================================================================

/-- The reduced-chain QAOA-conjugated bond observable at an **arbitrary** bond
`k : Fin (2P+2)` (the bond-`0` special case is `reducedChainQAOAConj`). This
is `U_PBC† · cP(k) · U_PBC` in the layered conjugation form, where `U_PBC`
uses the PBC cost sum and `+Σ X` mixer. -/
def reducedChainQAOAConj_at (P : ℕ) (γ β : Fin P → ℝ) (k : Fin (2 * P + 2)) :
    Qubits.NQubitOp (2 * P + 2) :=
  qaoaConjugate P γ β (IsingModel.chainPairInteraction k)

/-- The reduced-bond conjugate at bond `0` agrees with `reducedChainQAOAConj`. -/
theorem reducedChainQAOAConj_at_zero (P : ℕ) (γ β : Fin P → ℝ) :
    reducedChainQAOAConj_at P γ β (⟨0, by omega⟩ : Fin (2 * P + 2)) =
      reducedChainQAOAConj P γ β := rfl

/-- **One-step reduced-bond translation invariance.** The `|+⟩`-expectation of
the reduced-bond conjugate is invariant under `k ↦ nextSite k`. Combines
`qaoaConjugate_T_conj` (T passes through the conjugating unitary) with
`T_conj_full_chainPairInteraction` (`cP(nextSite k) = T† · cP(k) · T`) and
`uniformKet_expectation_T_conj` (`T · |+⟩ = |+⟩`). -/
theorem reducedChainQAOAConj_at_expectation_nextSite
    (P : ℕ) (γ β : Fin P → ℝ) (k : Fin (2 * P + 2)) :
    (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β (IsingModel.nextSite k) *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β k *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  -- `M := 2*P+1`, so `M + 1 = 2*P+2` (defeq).
  unfold reducedChainQAOAConj_at
  -- Rewrite cP(nextSite k) = T† · cP(k) · T.
  have hCP : IsingModel.chainPairInteraction (IsingModel.nextSite k) =
      (T_op_full (2 * P + 1) : Qubits.NQubitOp (2 * P + 2))† *
        IsingModel.chainPairInteraction k *
        (T_op_full (2 * P + 1) : Qubits.NQubitOp (2 * P + 2)) :=
    (T_conj_full_chainPairInteraction (2 * P + 1) k).symm
  rw [hCP]
  -- qaoaConjugate(T† · cP(k) · T) = T† · qaoaConjugate(cP(k)) · T.
  rw [← qaoaConjugate_T_conj (2 * P + 1) P γ β
        (IsingModel.chainPairInteraction k)]
  -- Apply the expectation invariance.
  exact uniformKet_expectation_T_conj (2 * P + 1)
    (qaoaConjugate P γ β (IsingModel.chainPairInteraction k))

/-- **Reduced-bond expectation reaches across the cyclic chain.** For any two
bonds related by iterated `nextSite`, the `|+⟩`-expectations agree. -/
theorem reducedChainQAOAConj_at_expectation_reach
    (P : ℕ) (γ β : Fin P → ℝ) (k k' : Fin (2 * P + 2))
    (h_reach : ∃ m : ℕ, (IsingModel.nextSite^[m]) k = k') :
    (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β k' *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β k *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  obtain ⟨m, hm⟩ := h_reach
  subst hm
  induction m with
  | zero => simp [Function.iterate_zero]
  | succ m ih =>
    rw [show (IsingModel.nextSite^[m + 1]) k =
          IsingModel.nextSite ((IsingModel.nextSite^[m]) k) from
        Function.iterate_succ_apply' _ _ _]
    rw [reducedChainQAOAConj_at_expectation_nextSite, ih]

/-- **`nextSite` reaches every bond from `0`** on the cyclic reduced chain.
Source: `nextSite` is the `finRotate` generator of `Fin (2P+2)`. -/
theorem nextSite_reach_from_zero (P : ℕ) (k : Fin (2 * P + 2)) :
    ∃ m : ℕ, (IsingModel.nextSite^[m]) (⟨0, by omega⟩ : Fin (2 * P + 2)) = k := by
  -- `nextSite^[k.val] 0 = k` since `nextSite` advances by one (mod `2P+2`).
  refine ⟨k.val, ?_⟩
  apply Fin.ext
  -- `(nextSite^[m] ⟨0,_⟩).val = m % (2P+2)`.
  have hiter : ∀ m : ℕ,
      ((IsingModel.nextSite^[m]) (⟨0, by omega⟩ : Fin (2 * P + 2))).val =
        m % (2 * P + 2) := by
    intro m
    induction m with
    | zero => simp [Nat.zero_mod]
    | succ m ih =>
      rw [Function.iterate_succ_apply', IsingModel.nextSite_val, ih]
      rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hiter k.val]
  exact Nat.mod_eq_of_lt k.isLt

/-- **Reduced-bond expectation is independent of the bond `k`** (the
load-bearing shortcut, validated numerically to ~1e-15). Every
reduced bond's `|+⟩`-expectation equals the canonical bond-`0` expectation. -/
theorem reducedChainQAOAConj_at_expectation_eq_zero
    (P : ℕ) (γ β : Fin P → ℝ) (k : Fin (2 * P + 2)) :
    (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β k *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj P γ β *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  rw [← reducedChainQAOAConj_at_zero P γ β]
  exact reducedChainQAOAConj_at_expectation_reach P γ β
    (⟨0, by omega⟩ : Fin (2 * P + 2)) k (nextSite_reach_from_zero P k)

-- ============================================================================
-- Section: the `j_s`-parametric LIGHTCONE identity (Bridge interface)
-- ============================================================================

/-- **`j_s`-parametric LIGHTCONE identity (Bridge interface).**

For any reduced bond `k : Fin (2P+2)`, the full-chain QAOA-conjugated bond
expectation at the canonical interior bond `j_s` equals the PBC reduced-chain
QAOA-conjugated bond expectation at bond `k`. This is the load-bearing
structural piece the Bridge consumes.

It is delivered as a composition of:
* the single canonical FGG matching `qaoa_full_eq_reduced_on_lightcone_closed`
  (full `j_s` ↔ reduced bond `0`), conditional on the `j_s`-parametric
  predicate `LightconeStructuralMatching` at the canonical `j_s`; and
* the reduced-bond translation invariance
  `reducedChainQAOAConj_at_expectation_eq_zero` (reduced `k` ↔ reduced `0`),
  proved SORRY-FREE here.

This is the "stronger than needed" shortcut that numerical validation established:
every reduced bond `k` collapses onto bond `0` by the PBC reduced-chain
translation invariance, so the FGG matrix-entry black-box is instantiated
only ONCE (at the canonical `j_s`), never per-`k`.

Source: FGG arXiv:1411.4028v1 §II l.113–134 (operator spreading, `j_s`-agnostic)
+ arXiv:1906.08948v2 §IV l.620–702 (chain reduction + translation invariance). -/
theorem qaoa_full_eq_reduced_on_lightcone_at
    {N : ℕ} (P : ℕ) (hP : 2 * P + 2 ≤ N) (γ β : Fin P → ℝ)
    (j_s : Fin N) (k : Fin (2 * P + 2))
    (h_match : LightconeStructuralMatching P hP γ β j_s) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (fullChainQAOAConj P γ β j_s *
          QAOA.uniformKet (Qubits.NQubitDim N)) =
      (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (reducedChainQAOAConj_at P γ β k *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) := by
  rw [qaoa_full_eq_reduced_on_lightcone_closed P hP γ β j_s h_match]
  exact (reducedChainQAOAConj_at_expectation_eq_zero P γ β k).symm

end

end QAOA.IsingChain.UpperBound.LightCone
