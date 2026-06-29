import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.WindowBlock

/-!
# Nested-Window Restriction — restricted matrix entries across a sub-window `S ⊆ T`

This file builds the **nested-window restriction** bridge needed to apply the
depth-`P` inductive hypothesis (a `restrictedMatrixEntry` equality on the
depth-`P` window `S`, dim `2P+2`) inside the depth-`P+1` window-block recursion
(which lives on the depth-`P+1` window `T ⊇ S`, dim `2P+4`).

The key fact (`restrictedMatrixEntry_of_subset`): for an operator `O` that is
`tensorSupportedOn` a *sub*-window `S ⊆ T`, its `T`-restricted matrix entry on
data `zs ws : T → Fin 2` equals its `S`-restricted matrix entry on the
`S`-restrictions of `zs, ws` **when** `zs` and `ws` agree on `T \ S`, and is
`0` otherwise. The extra `T \ S` bits are "spectator" qubits on which `O` acts
trivially, so they must match diagonally (else the entry vanishes) and
contribute nothing to the value.

Composing this with the depth-`P` IH lets the middle factor of
`windowBlock_qaoaConjugate_succ` be discharged: the depth-`P` conjugate is
tensor-supported on the depth-`P` window, a strict subset of the depth-`P+1`
window over which the block recursion takes its `windowBlock`.

Source: arXiv:1411.4028v1 §II l.102–135 (lightcone tensor structure / spectator
qubits).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: restriction of `T`-data to a sub-window `S`
-- ============================================================================

/-- Restrict `T`-window data `zs : T → Fin 2` to the sub-window `S ⊆ T`,
reading off the value at the inclusion of each `S`-site into `T`. -/
def restrictData {N : ℕ} {S T : Finset (Fin N)} (hST : S ⊆ T)
    (zs : T → Fin 2) : S → Fin 2 :=
  fun k => zs ⟨(k : Fin N), hST k.2⟩

/-- `extendByZeroOnS T zs` and `extendByZeroOnS S (restrictData hST zs)` agree
on every site of `S`: both equal `zs` there. -/
theorem extendByZeroOnS_restrict_agree_on_S {N : ℕ} {S T : Finset (Fin N)}
    (hST : S ⊆ T) (zs : T → Fin 2) (k : Fin N) (hk : k ∈ S) :
    extendByZeroOnS T zs k = extendByZeroOnS S (restrictData hST zs) k := by
  rw [extendByZeroOnS_apply_mem (h := hST hk), extendByZeroOnS_apply_mem (h := hk)]
  rfl

/-- `extendByZeroOnS S (restrictData hST zs)` agrees with `extendByZeroOnS S
(restrictData hST ws)` outside `S`: both are `0` there. -/
theorem extendByZeroOnS_restrict_agreeOutside {N : ℕ} {S T : Finset (Fin N)}
    (hST : S ⊆ T) (zs ws : T → Fin 2) :
    AgreeOutside S (extendByZeroOnS S (restrictData hST zs))
      (extendByZeroOnS S (restrictData hST ws)) :=
  extendByZeroOnS_agreeOutside S _ _

-- ============================================================================
-- Section: the nested-window restriction bridge
-- ============================================================================

/-- **Nested-window restriction bridge.** For `O` tensor-supported on a
*sub*-window `S ⊆ T`, the `T`-restricted matrix entry equals the `S`-restricted
matrix entry on the `S`-restrictions of the data, **provided** the two data
agree on the spectator sites `T \ S`; otherwise the entry vanishes.

This is the precise statement that lets the depth-`P` matrix-entry IH (on the
depth-`P` window `S`) discharge the middle factor of the depth-`P+1` window
block (on the depth-`P+1` window `T ⊇ S`). -/
theorem restrictedMatrixEntry_of_subset {N : ℕ} {S T : Finset (Fin N)}
    (hST : S ⊆ T) {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O)
    (zs ws : T → Fin 2) :
    restrictedMatrixEntry T O zs ws =
      (if (∀ k : T, (k : Fin N) ∉ S → zs k = ws k) then
        restrictedMatrixEntry S O (restrictData hST zs) (restrictData hST ws)
       else 0) := by
  classical
  unfold restrictedMatrixEntry
  set extT_z := extendByZeroOnS T zs with hextTz
  set extT_w := extendByZeroOnS T ws with hextTw
  set extS_z := extendByZeroOnS S (restrictData hST zs) with hextSz
  set extS_w := extendByZeroOnS S (restrictData hST ws) with hextSw
  by_cases hagree : (∀ k : T, (k : Fin N) ∉ S → zs k = ws k)
  · rw [if_pos hagree]
    -- The `T`-extensions agree outside `S` (off `T` both 0; on `T\S` by
    -- `hagree`); the `S`-extensions agree outside `S` trivially; both pairs
    -- match on `S`. Apply the within-block clause of tensor-support.
    have hAO_T : AgreeOutside S extT_z extT_w := by
      intro k hkS
      by_cases hkT : k ∈ T
      · rw [hextTz, hextTw, extendByZeroOnS_apply_mem (h := hkT),
            extendByZeroOnS_apply_mem (h := hkT)]
        exact hagree ⟨k, hkT⟩ hkS
      · rw [hextTz, hextTw, extendByZeroOnS_apply_not_mem (h := hkT),
            extendByZeroOnS_apply_not_mem (h := hkT)]
    have hAO_S : AgreeOutside S extS_z extS_w :=
      extendByZeroOnS_restrict_agreeOutside hST zs ws
    have hrow : ∀ k ∈ S,
        (Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extT_z) k =
        (Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extS_z) k := by
      intro k hk
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [hextTz, hextSz]
      exact extendByZeroOnS_restrict_agree_on_S hST zs k hk
    have hcol : ∀ k ∈ S,
        (Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extT_w) k =
        (Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extS_w) k := by
      intro k hk
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      rw [hextTw, hextSw]
      exact extendByZeroOnS_restrict_agree_on_S hST ws k hk
    have hAO_T' : AgreeOutside S
        ((Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extT_z))
        ((Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extT_w)) := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact hAO_T
    have hAO_S' : AgreeOutside S
        ((Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extS_z))
        ((Qubits.bitStringEquiv N).symm ((Qubits.bitStringEquiv N) extS_w)) := by
      rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]; exact hAO_S
    exact hO.2 _ _ _ _ hrow hcol hAO_T' hAO_S'
  · rw [if_neg hagree]
    -- `zs, ws` disagree at some spectator site `k ∈ T \ S`; the `T`-extensions
    -- disagree outside `S`, so the entry vanishes by `supportedOn`.
    push_neg at hagree
    obtain ⟨k, hkS, hkne⟩ := hagree
    apply hO.1
    intro hAO
    apply hkne
    have := hAO (k : Fin N) hkS
    rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
    rw [hextTz, hextTw, extendByZeroOnS_apply_mem (h := k.2),
        extendByZeroOnS_apply_mem (h := k.2)] at this
    exact this

-- ============================================================================
-- Section: window-block of a sub-window-supported operator
-- ============================================================================

/-- **Window block of a sub-window-supported operator.** For `O` tensor-
supported on `S ⊆ T`, an entry of the depth-`T` block equals the spectator-gated
depth-`S` restricted entry: if the two `T`-window data agree on the spectator
sites `T \ S`, the entry is the `S`-restricted entry of the (restricted) data;
otherwise it vanishes. This is `restrictedMatrixEntry_of_subset` lifted to
`windowBlock`. -/
theorem windowBlock_of_subset {N mT : ℕ} {S T : Finset (Fin N)} (hST : S ⊆ T)
    (εT : Fin mT ≃ T) {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O)
    (a b : Fin (Qubits.NQubitDim mT)) :
    windowBlock εT O a b =
      (if (∀ k : T, (k : Fin N) ∉ S → windowData εT a k = windowData εT b k) then
        restrictedMatrixEntry S O (restrictData hST (windowData εT a))
          (restrictData hST (windowData εT b))
       else 0) := by
  unfold windowBlock
  rw [restrictedMatrixEntry_of_subset hST hO]

end

end QAOA.IsingChain.UpperBound.LightCone
