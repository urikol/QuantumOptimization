import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.StructuralIdentification
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.PlusStateFactorization

/-!
# Window-Block Extraction — `windowBlock` of a tensor-supported operator, block ring calculus

This file builds the **window-block extraction** calculus recommended after
the direct entry-tracking wall of `canonical_matrix_entry_match`. The idea
is to *restrict first, then reason entirely in the reduced dimension*: for an
operator `O : NQubitOp N` tensor-supported on a window `S` of card `m`, we
extract its `m`-qubit **block** `windowBlock ε O : NQubitOp m` (via a chosen
equivalence `ε : Fin m ≃ ↥S`) whose matrix entries are exactly the restricted
matrix entries of `O`. We then prove:

* `restrictedMatrixEntry_eq_windowBlock` — the bridge: a restricted matrix
  entry of `O` is an honest matrix entry of `windowBlock ε O`. (Lemma 1.)
* `windowBlock_mul` — block multiplicativity: for `A, B` tensor-supported on
  the *same* window `S`, `windowBlock ε (A * B) = windowBlock ε A *
  windowBlock ε B`. (Lemma 2.) This is the load-bearing kernel: it collapses
  a full-`2^N` intermediate sum to a window-restricted `2^m` sum entirely
  inside dimension `m`.
* `windowBlock_one`, `windowBlock_smul`, `windowBlock_add` — the rest of the
  ring calculus, so the block of a closed-form generator pushes through.

With these in hand the FGG light-cone matrix-entry identity becomes an
equality of `m = 2P+2`-qubit block operators built by the *same* recursion,
provable without crossing the `N ↔ 2P+2` dimension boundary inside any sum.

Source: FGG arXiv:1411.4028v1 §II–III (operator spreading + light-cone
theorem); the block-extraction realization mirrors the partial-trace /
tensor-factor restriction of `A = A_S ⊗ I_{Sᶜ}`.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: window data and the block operator
-- ============================================================================

/-- The window-restricted data of a basis index `a : Fin (2^m)` pulled back
to `↥S` along `ε : Fin m ≃ ↥S`: read off the bit at site `k ∈ S` as the bit
of `a` at index `ε.symm k`. -/
def windowData {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    (a : Fin (Qubits.NQubitDim m)) : S → Fin 2 :=
  fun k => (Qubits.bitStringEquiv m).symm a (ε.symm k)

/-- The `m`-qubit **block** of an operator `O` on its window `S` (card `m`),
relative to the chosen identification `ε : Fin m ≃ ↥S`. Its matrix entries
are the restricted matrix entries of `O` read through `ε`. -/
def windowBlock {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    (O : Qubits.NQubitOp N) : Qubits.NQubitOp m :=
  fun a b => restrictedMatrixEntry S O (windowData ε a) (windowData ε b)

/-- `windowData` and the `bitStringEquiv`-encoding of an `S`-restricted datum
are mutually inverse: pulling `zs : S → Fin 2` back through `ε` (giving a
`Fin m → Fin 2` then a `Fin (2^m)` index) and reading it off as window data
recovers `zs`. -/
theorem windowData_encode {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    (zs : S → Fin 2) :
    windowData ε ((Qubits.bitStringEquiv m) (fun i => zs (ε i))) = zs := by
  funext k
  unfold windowData
  rw [Equiv.symm_apply_apply]
  rw [Equiv.apply_symm_apply]

-- ============================================================================
-- Section: restricted-entry multiplicativity (kernel of Lemma 2)
-- ============================================================================

/-- **Restricted-entry multiplicativity.** For `A, B` both tensor-supported
on the *same* window `S`, the restricted matrix entry of the product `A * B`
is the sum, over window-restricted intermediate data `ms : S → Fin 2`, of the
product of restricted entries. The full-`2^N` intermediate sum collapses to a
window-`2^|S|` sum because tensor-support pins the outside-`S` bits of every
nonzero intermediate index to the canonical `0`. -/
theorem restrictedMatrixEntry_mul {N : ℕ} {S : Finset (Fin N)}
    {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn S A) (_hB : tensorSupportedOn S B)
    (zs ws : S → Fin 2) :
    restrictedMatrixEntry S (A * B) zs ws =
      ∑ ms : S → Fin 2,
        restrictedMatrixEntry S A zs ms * restrictedMatrixEntry S B ms ws := by
  classical
  unfold restrictedMatrixEntry
  set e := Qubits.bitStringEquiv N with he_def
  set ext := extendByZeroOnS S with hext_def
  -- Expand the product entry as a sum over the intermediate `BitString N`.
  have hmul : (A * B) (e (ext zs)) (e (ext ws)) =
      ∑ z : Qubits.BitString N, A (e (ext zs)) (e z) * B (e z) (e (ext ws)) := by
    rw [Matrix.mul_apply]
    rw [← (Qubits.bitStringEquiv N).sum_comp
      (fun iz => A (e (ext zs)) iz * B iz (e (ext ws)))]
  -- The full-`BitString N` sum reindexes via the split equivalence.
  set E := bitStringSplitEquiv (N := N) S with hE_def
  have hreindex :
      ∑ z : Qubits.BitString N, A (e (ext zs)) (e z) * B (e z) (e (ext ws)) =
        ∑ p : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
          A (e (ext zs)) (e (E.symm p)) * B (e (E.symm p)) (e (ext ws)) := by
    rw [← E.symm.sum_comp
      (fun z => A (e (ext zs)) (e z) * B (e z) (e (ext ws)))]
  -- A term is nonzero only when the complement part `p.2` is the all-zero
  -- configuration `(extendByZeroOnS)`-style; for any other `p.2` the entry
  -- agrees with `ext zs` outside `S` is broken, killing the `A` factor.
  have hval : ∀ p : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
      A (e (ext zs)) (e (E.symm p)) * B (e (E.symm p)) (e (ext ws)) =
        if p.2 = (fun _ => 0) then
          restrictedMatrixEntry S A zs p.1 * restrictedMatrixEntry S B p.1 ws
        else 0 := by
    rintro ⟨ms, z_out⟩
    by_cases hout : z_out = (fun _ => 0)
    · subst hout
      rw [if_pos rfl]
      -- `E.symm (ms, 0)` is exactly `ext ms` as a bitstring.
      have hEms : E.symm (ms, (fun _ => 0)) = ext ms := by
        funext k
        by_cases hk : k ∈ S
        · rw [bitStringSplitEquiv_symm_apply_mem (h := hk)]
          rw [hext_def, extendByZeroOnS_apply_mem (h := hk)]
        · rw [bitStringSplitEquiv_symm_apply_not_mem (h := hk)]
          rw [hext_def, extendByZeroOnS_apply_not_mem (h := hk)]
      rw [hEms]
      rfl
    · rw [if_neg hout]
      -- There is a site `k ∉ S` where `z_out k ≠ 0 = ext zs k`, so the `A`
      -- factor vanishes by `supportedOn`.
      obtain ⟨k, hk_ne⟩ : ∃ k : {k // k ∉ S}, z_out k ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hout (funext fun k => hcon k)
      have hAzero : A (e (ext zs)) (e (E.symm (ms, z_out))) = 0 := by
        apply hA.1
        intro hAO
        -- AgreeOutside S forces equality at the outside site k.
        have := hAO (k : Fin N) k.2
        rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply] at this
        rw [bitStringSplitEquiv_symm_apply_not_mem (h := k.2)] at this
        rw [hext_def, extendByZeroOnS_apply_not_mem (h := k.2)] at this
        exact hk_ne this.symm
      rw [hAzero, zero_mul]
  rw [hmul, hreindex]
  rw [show (Finset.univ : Finset ((S → Fin 2) × ({k // k ∉ S} → Fin 2))) =
        (Finset.univ : Finset (S → Fin 2)) ×ˢ
          (Finset.univ : Finset ({k // k ∉ S} → Fin 2)) from rfl]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl ?_
  intro ms _
  -- Inner sum over `z_out` collapses to the single `z_out = 0` term.
  have hinner : ∀ z_out : {k // k ∉ S} → Fin 2,
      A (e (ext zs)) (e (E.symm (ms, z_out))) * B (e (E.symm (ms, z_out))) (e (ext ws)) =
        if z_out = (fun _ => 0) then
          restrictedMatrixEntry S A zs ms * restrictedMatrixEntry S B ms ws
        else 0 := fun z_out => hval (ms, z_out)
  rw [Finset.sum_congr rfl (fun z_out _ => hinner z_out)]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset ({k // k ∉ S} → Fin 2)) (fun _ => 0)]
  rw [if_pos (Finset.mem_univ _)]
  rfl

-- ============================================================================
-- Section: Lemma 1 — the bridge
-- ============================================================================

/-- **Lemma 1 (block bridge).** A restricted matrix entry of `O` on the
window `S` equals an honest matrix entry of the `m`-qubit block
`windowBlock ε O`, at the `bitStringEquiv`-encodings of the pulled-back
window data. -/
theorem restrictedMatrixEntry_eq_windowBlock {N m : ℕ} {S : Finset (Fin N)}
    (ε : Fin m ≃ S) (O : Qubits.NQubitOp N) (zs ws : S → Fin 2) :
    restrictedMatrixEntry S O zs ws =
      windowBlock ε O
        ((Qubits.bitStringEquiv m) (fun i => zs (ε i)))
        ((Qubits.bitStringEquiv m) (fun i => ws (ε i))) := by
  unfold windowBlock
  rw [windowData_encode, windowData_encode]

-- ============================================================================
-- Section: `windowData` as an equivalence `Fin (2^m) ≃ (S → Fin 2)`
-- ============================================================================

/-- `windowData ε` realizes a bijection `Fin (2^m) ≃ (↥S → Fin 2)`: read an
`m`-qubit basis index off its bits, then transport along `ε`. -/
def windowDataEquiv {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S) :
    Fin (Qubits.NQubitDim m) ≃ (S → Fin 2) :=
  (Qubits.bitStringEquiv m).symm.trans (Equiv.arrowCongr ε (Equiv.refl (Fin 2)))

@[simp] theorem windowDataEquiv_apply {N m : ℕ} {S : Finset (Fin N)}
    (ε : Fin m ≃ S) (a : Fin (Qubits.NQubitDim m)) :
    windowDataEquiv ε a = windowData ε a := by
  funext k
  show (Equiv.refl (Fin 2)) ((Qubits.bitStringEquiv m).symm a (ε.symm k)) = _
  rfl

-- ============================================================================
-- Section: Lemma 2 — block multiplicativity, and the ring calculus
-- ============================================================================

/-- **Lemma 2 (block multiplicativity).** For `A, B` both tensor-supported on
the same window `S` (card `m` via `ε`), the block of the product is the
product of the blocks, computed entirely in dimension `m`. -/
theorem windowBlock_mul {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    {A B : Qubits.NQubitOp N}
    (hA : tensorSupportedOn S A) (hB : tensorSupportedOn S B) :
    windowBlock ε (A * B) = windowBlock ε A * windowBlock ε B := by
  classical
  funext a b
  unfold windowBlock
  rw [restrictedMatrixEntry_mul hA hB]
  rw [Matrix.mul_apply]
  -- Reindex the `S → Fin 2` sum as a `Fin (2^m)` sum via `windowDataEquiv`.
  rw [← (windowDataEquiv ε).sum_comp
    (fun ms => restrictedMatrixEntry S A (windowData ε a) ms *
      restrictedMatrixEntry S B ms (windowData ε b))]
  refine Finset.sum_congr rfl ?_
  intro c _
  rw [windowDataEquiv_apply]

/-- The block of the identity is the identity. -/
theorem windowBlock_one {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S) :
    windowBlock ε (1 : Qubits.NQubitOp N) = (1 : Qubits.NQubitOp m) := by
  classical
  funext a b
  unfold windowBlock restrictedMatrixEntry
  rw [Matrix.one_apply, Matrix.one_apply]
  -- `1`'s entry is `if row = col then 1 else 0`; transport the condition.
  have hiff : ((Qubits.bitStringEquiv N) (extendByZeroOnS S (windowData ε a)) =
        (Qubits.bitStringEquiv N) (extendByZeroOnS S (windowData ε b))) ↔ a = b := by
    constructor
    · intro h
      have h1 : extendByZeroOnS S (windowData ε a) = extendByZeroOnS S (windowData ε b) :=
        (Qubits.bitStringEquiv N).injective h
      have h2 : windowData ε a = windowData ε b := by
        funext k
        have := congrFun h1 (k : Fin N)
        rwa [extendByZeroOnS_apply_mem (h := k.2),
            extendByZeroOnS_apply_mem (h := k.2)] at this
      have h3 : windowDataEquiv ε a = windowDataEquiv ε b := by
        rw [windowDataEquiv_apply, windowDataEquiv_apply]; exact h2
      exact (windowDataEquiv ε).injective h3
    · intro h; rw [h]
  by_cases hab : a = b
  · rw [if_pos hab, if_pos (hiff.mpr hab)]
  · rw [if_neg hab, if_neg (fun h => hab (hiff.mp h))]

/-- The block of a scalar multiple is the scalar multiple of the block. -/
theorem windowBlock_smul {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    (c : ℂ) (O : Qubits.NQubitOp N) :
    windowBlock ε (c • O) = c • windowBlock ε O := by
  funext a b
  unfold windowBlock restrictedMatrixEntry
  rfl

/-- The block of a sum is the sum of the blocks. -/
theorem windowBlock_add {N m : ℕ} {S : Finset (Fin N)} (ε : Fin m ≃ S)
    (A B : Qubits.NQubitOp N) :
    windowBlock ε (A + B) = windowBlock ε A + windowBlock ε B := by
  funext a b
  unfold windowBlock restrictedMatrixEntry
  rfl

end

end QAOA.IsingChain.UpperBound.LightCone
