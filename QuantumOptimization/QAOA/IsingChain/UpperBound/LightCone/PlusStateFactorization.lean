import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.FGGClosure
import QuantumOptimization.QAOA.StandardQAOA

/-!
# FGG Lemma 4 — Plus-state expectation factorization over the support

This file implements **Lemma 4** of the FGG light-cone chain: for an
`N`-qubit operator `O` that is *tensor-supported* on a finite set
`S ⊆ Fin N`, the `|+⟩^{⊗N}` sandwich

  ⟨+|^{⊗N} · O · |+⟩^{⊗N}

reduces to a sandwich on the `|S|`-qubit subspace, with the `2^{|S^c|}`
outside-`S` factor cancelling the `1/2^{N}` global normalization to give
`1/2^{|S|}`. This is the FGG argument of arXiv:1411.4028v1 §II l.151–156:
the expectation only involves the qubits in the lightcone subgraph.

The reduction is stated as the closed-form identity

  ⟨+|^{⊗N} · O · |+⟩^{⊗N}
    = (1 / 2^{|S|}) · ∑_{zs, ws : S → Fin 2}
        O[extend(zs)][extend(ws)],

where `extend : (S → Fin 2) → BitString N` extends an `S`-bitstring with
zeros outside `S` (a canonical choice; well-definedness is the strong
predicate clause of `tensorSupportedOn`).

Sources:
* Farhi, Goldstone, Gutmann (FGG), arXiv:1411.4028v1 §II l.151–156.

## Public deliverables

* `extendByZeroOnS` — canonical extension `(S → Fin 2) → BitString N`.
* `restrictedMatrixEntry` — `O`'s value on a `(zs, ws)` pair after
  extension.
* `expectation_factors_over_support` — Lemma 4 in closed form.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Canonical extension and restricted matrix entry
-- ============================================================================

/-- Extend an `S`-restricted bitstring to a full `BitString N` by placing
zero on every qubit outside `S`. This is the canonical choice used to
define the `S`-restricted matrix entries of an operator tensor-supported
on `S`. The choice of "zero outside `S`" is arbitrary in the sense that
any fixed configuration outside `S` gives the same restricted entry under
`tensorSupportedOn` (cf. the strong-predicate clause). -/
def extendByZeroOnS {N : ℕ} (S : Finset (Fin N)) (zs : S → Fin 2) :
    Qubits.BitString N :=
  fun k => if h : k ∈ S then zs ⟨k, h⟩ else 0

/-- `extendByZeroOnS` agrees with `zs` on `S`. -/
@[simp]
theorem extendByZeroOnS_apply_mem {N : ℕ} {S : Finset (Fin N)}
    (zs : S → Fin 2) {k : Fin N} (h : k ∈ S) :
    extendByZeroOnS S zs k = zs ⟨k, h⟩ := by
  unfold extendByZeroOnS
  simp [h]

/-- `extendByZeroOnS` is zero off `S`. -/
@[simp]
theorem extendByZeroOnS_apply_not_mem {N : ℕ} {S : Finset (Fin N)}
    (zs : S → Fin 2) {k : Fin N} (h : k ∉ S) :
    extendByZeroOnS S zs k = 0 := by
  unfold extendByZeroOnS
  simp [h]

/-- Two `extendByZeroOnS` extensions agree outside `S`. -/
theorem extendByZeroOnS_agreeOutside {N : ℕ} (S : Finset (Fin N))
    (zs ws : S → Fin 2) :
    AgreeOutside S (extendByZeroOnS S zs) (extendByZeroOnS S ws) := by
  intro k hk
  simp [hk]

/-- `O`'s matrix entry on the canonical extensions of `(zs, ws)`. By the
strong-predicate clause of `tensorSupportedOn`, this captures the value
of `O` on any pair of bitstrings whose `S`-restriction matches `(zs, ws)`
and which agree outside `S`. -/
def restrictedMatrixEntry {N : ℕ} (S : Finset (Fin N))
    (O : Qubits.NQubitOp N) (zs ws : S → Fin 2) : ℂ :=
  O ((Qubits.bitStringEquiv N) (extendByZeroOnS S zs))
    ((Qubits.bitStringEquiv N) (extendByZeroOnS S ws))

-- ============================================================================
-- Section: Uniform-ket sandwich expansion
-- ============================================================================

/-- The uniform `N`-qubit ket `|+⟩^{⊗N}` has every amplitude equal to
`1 / √(2^N)`. -/
theorem uniformKet_vec_eq {N : ℕ}
    (i : Fin (Qubits.NQubitDim N)) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).vec i =
      ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ) := rfl

/-- The uniform-ket sandwich expands to `(1/2^N) · ∑_{ix, iy} O[ix][iy]`.

Source: standard quantum mechanics, restated for the uniform `N`-qubit
state. -/
theorem uniform_sandwich_eq_sum {N : ℕ} (O : Qubits.NQubitOp N) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (O * QAOA.uniformKet (Qubits.NQubitDim N)) =
      (1 / ((Qubits.NQubitDim N : ℕ) : ℂ)) *
        ∑ ix : Fin (Qubits.NQubitDim N), ∑ iy : Fin (Qubits.NQubitDim N), O ix iy := by
  have hpos : 0 < ((Qubits.NQubitDim N : ℕ) : ℝ) := by
    have : 0 < (Qubits.NQubitDim N : ℕ) := Nat.pos_of_ne_zero (NeZero.ne _)
    exact_mod_cast this
  have hsqrt_sq :
      Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) *
        Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) =
          ((Qubits.NQubitDim N : ℕ) : ℝ) :=
    Real.mul_self_sqrt (le_of_lt hpos)
  have hsqrt_ne : Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) ≠ 0 :=
    Real.sqrt_ne_zero'.mpr hpos
  have hd_ne : ((Qubits.NQubitDim N : ℕ) : ℂ) ≠ 0 := by
    have : ((Qubits.NQubitDim N : ℕ) : ℝ) ≠ 0 := ne_of_gt hpos
    exact_mod_cast this
  have hinv_sq :
      (((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ)) *
        (((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ)) =
      1 / ((Qubits.NQubitDim N : ℕ) : ℂ) := by
    rw [show ((1 / Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℝ) : ℂ) =
            (Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℂ)⁻¹ by
        push_cast; rw [one_div]]
    rw [← mul_inv]
    rw [show (Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℂ) *
            (Real.sqrt ((Qubits.NQubitDim N : ℕ) : ℝ) : ℂ) =
            ((Qubits.NQubitDim N : ℕ) : ℂ) by
        push_cast
        exact_mod_cast hsqrt_sq]
    rw [one_div]
  rw [bra_mul_ket_eq]
  simp only [Ket.dag_vec, op_mul_ket_vec, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro ix _
  show ((starRingEnd ℂ) ((QAOA.uniformKet (Qubits.NQubitDim N)).vec ix)) *
      ∑ iy, O ix iy * (QAOA.uniformKet (Qubits.NQubitDim N)).vec iy =
    (1 / ((Qubits.NQubitDim N : ℕ) : ℂ)) * ∑ iy, O ix iy
  rw [uniformKet_vec_eq]
  simp only [Complex.conj_ofReal]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro iy _
  rw [uniformKet_vec_eq]
  -- Goal: (1/√d : ℂ) * (O ix iy * (1/√d : ℂ)) = (1/d : ℂ) * O ix iy
  have := hinv_sq
  ring_nf
  ring_nf at this
  linear_combination (O ix iy) * this

-- ============================================================================
-- Section: Lemma 4
-- ============================================================================

/-- A `BitString N ≃ (S → Fin 2) × ({k // k ∉ S} → Fin 2)` decomposition.

This is the canonical splitting of a full bitstring into its `S`-
restriction and its complement-restriction. -/
def bitStringSplitEquiv {N : ℕ} (S : Finset (Fin N)) :
    Qubits.BitString N ≃ (S → Fin 2) × ({k // k ∉ S} → Fin 2) := by
  classical
  refine (Equiv.piEquivPiSubtypeProd (fun k : Fin N => k ∈ S) (fun _ => Fin 2)).trans ?_
  refine Equiv.prodCongr ?_ (Equiv.refl _)
  exact Equiv.piCongrLeft (fun _ => Fin 2)
    ⟨fun k : {k : Fin N // k ∈ S} => (⟨k.1, k.2⟩ : S),
     fun k => ⟨k.1, k.2⟩, fun _ => rfl, fun _ => rfl⟩

theorem bitStringSplitEquiv_symm_apply_mem {N : ℕ} (S : Finset (Fin N))
    (zs : S → Fin 2) (z_out : {k // k ∉ S} → Fin 2) {k : Fin N} (h : k ∈ S) :
    ((bitStringSplitEquiv S).symm (zs, z_out)) k = zs ⟨k, h⟩ := by
  classical
  simp [bitStringSplitEquiv, Equiv.piEquivPiSubtypeProd, Equiv.piCongrLeft, h]

theorem bitStringSplitEquiv_symm_apply_not_mem {N : ℕ} (S : Finset (Fin N))
    (zs : S → Fin 2) (z_out : {k // k ∉ S} → Fin 2) {k : Fin N} (h : k ∉ S) :
    ((bitStringSplitEquiv S).symm (zs, z_out)) k = z_out ⟨k, h⟩ := by
  classical
  simp [bitStringSplitEquiv, Equiv.piEquivPiSubtypeProd, Equiv.piCongrLeft, h]

/-- **Lemma 4: plus-state expectation factorization.** For an operator
`O` tensor-supported on `S ⊆ Fin N`, the `|+⟩^{⊗N}` sandwich equals the
restricted sandwich on the `|S|`-qubit subspace.

Source: FGG arXiv:1411.4028v1 §II l.151–156. -/
theorem expectation_factors_over_support {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : tensorSupportedOn S O) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (O * QAOA.uniformKet (Qubits.NQubitDim N)) =
      (1 / ((2 ^ S.card : ℕ) : ℂ)) *
        ∑ zs : S → Fin 2, ∑ ws : S → Fin 2, restrictedMatrixEntry S O zs ws := by
  classical
  -- Step 1: expand the sandwich as `(1/2^N) · Σ_{ix, iy} O ix iy`.
  rw [uniform_sandwich_eq_sum]
  -- Step 2: re-index the double sum over `Fin (2^N) × Fin (2^N)` as a
  -- double sum over `BitString N × BitString N` via `bitStringEquiv`.
  have hsum_reindex :
      ∑ ix : Fin (Qubits.NQubitDim N), ∑ iy : Fin (Qubits.NQubitDim N), O ix iy
        = ∑ z : Qubits.BitString N, ∑ w : Qubits.BitString N,
            O ((Qubits.bitStringEquiv N) z) ((Qubits.bitStringEquiv N) w) := by
    rw [← (Qubits.bitStringEquiv N).sum_comp
      (fun ix => ∑ iy : Fin (Qubits.NQubitDim N), O ix iy)]
    refine Finset.sum_congr rfl ?_
    intro z _
    rw [← (Qubits.bitStringEquiv N).sum_comp
      (fun iy => O ((Qubits.bitStringEquiv N) z) iy)]
  rw [hsum_reindex]
  -- Step 3: re-index each BitString N via bitStringSplitEquiv.
  set E := bitStringSplitEquiv (N := N) S with hE_def
  have hsum_z :
      ∑ z : Qubits.BitString N, ∑ w : Qubits.BitString N,
          O ((Qubits.bitStringEquiv N) z) ((Qubits.bitStringEquiv N) w) =
      ∑ p : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
        ∑ q : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
          O ((Qubits.bitStringEquiv N) (E.symm p))
            ((Qubits.bitStringEquiv N) (E.symm q)) := by
    rw [← E.symm.sum_comp
      (fun z => ∑ w : Qubits.BitString N,
          O ((Qubits.bitStringEquiv N) z) ((Qubits.bitStringEquiv N) w))]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [← E.symm.sum_comp
      (fun w => O ((Qubits.bitStringEquiv N) (E.symm p))
        ((Qubits.bitStringEquiv N) w))]
  rw [hsum_z]
  -- Step 4: for each fixed (zs, ws, z_out, w_out), the value of O is:
  --   0 if z_out ≠ w_out (by supportedOn),
  --   restrictedMatrixEntry S O zs ws if z_out = w_out (by tensorSupportedOn).
  have hval :
      ∀ p q : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
        O ((Qubits.bitStringEquiv N) (E.symm p))
          ((Qubits.bitStringEquiv N) (E.symm q)) =
          if p.2 = q.2 then restrictedMatrixEntry S O p.1 q.1 else 0 := by
    rintro ⟨zs, z_out⟩ ⟨ws, w_out⟩
    show O ((Qubits.bitStringEquiv N) (E.symm (zs, z_out)))
        ((Qubits.bitStringEquiv N) (E.symm (ws, w_out))) =
      if z_out = w_out then restrictedMatrixEntry S O zs ws else 0
    by_cases hout : z_out = w_out
    · subst hout
      rw [if_pos rfl]
      unfold restrictedMatrixEntry
      -- Apply hO.2 to identify the two pairs of indices.
      refine hO.2 _ _ _ _ ?_ ?_ ?_ ?_
      · intro k hkS
        simp only [Equiv.symm_apply_apply]
        rw [bitStringSplitEquiv_symm_apply_mem (h := hkS),
            extendByZeroOnS_apply_mem (h := hkS)]
      · intro k hkS
        simp only [Equiv.symm_apply_apply]
        rw [bitStringSplitEquiv_symm_apply_mem (h := hkS),
            extendByZeroOnS_apply_mem (h := hkS)]
      · intro k hk
        simp only [Equiv.symm_apply_apply]
        rw [bitStringSplitEquiv_symm_apply_not_mem (h := hk),
            bitStringSplitEquiv_symm_apply_not_mem (h := hk)]
      · intro k hk
        simp only [Equiv.symm_apply_apply]
        rw [extendByZeroOnS_apply_not_mem (h := hk),
            extendByZeroOnS_apply_not_mem (h := hk)]
    · rw [if_neg hout]
      -- The off-diagonal entry vanishes by supportedOn.
      apply hO.1
      intro hAO
      apply hout
      funext k
      have hk : (k : Fin N) ∉ S := k.2
      have := hAO (k : Fin N) hk
      simp only [Equiv.symm_apply_apply] at this
      rw [bitStringSplitEquiv_symm_apply_not_mem (h := hk),
          bitStringSplitEquiv_symm_apply_not_mem (h := hk)] at this
      exact this
  -- Step 5: collapse the inner double sum (over q) using hval, then
  -- collapse the outer (over z_out).
  have hkey :
      ∑ p : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
        ∑ q : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
          O ((Qubits.bitStringEquiv N) (E.symm p))
            ((Qubits.bitStringEquiv N) (E.symm q)) =
      ((2 ^ (N - S.card) : ℕ) : ℂ) *
        ∑ zs : S → Fin 2, ∑ ws : S → Fin 2,
          restrictedMatrixEntry S O zs ws := by
    -- First, substitute hval everywhere.
    rw [show (Finset.univ : Finset ((S → Fin 2) × ({k // k ∉ S} → Fin 2))) =
          (Finset.univ : Finset (S → Fin 2)) ×ˢ
            (Finset.univ : Finset ({k // k ∉ S} → Fin 2)) from rfl]
    rw [Finset.sum_product]
    -- LHS now: Σ_{zs, z_out} (Σ_q O[..][..])
    -- Inner Σ_q split:
    have hinner : ∀ (zs : S → Fin 2) (z_out : {k // k ∉ S} → Fin 2),
        ∑ q : (S → Fin 2) × ({k // k ∉ S} → Fin 2),
            O ((Qubits.bitStringEquiv N) (E.symm (zs, z_out)))
              ((Qubits.bitStringEquiv N) (E.symm q)) =
          ∑ ws : S → Fin 2, restrictedMatrixEntry S O zs ws := by
      intro zs z_out
      rw [show (Finset.univ : Finset ((S → Fin 2) × ({k // k ∉ S} → Fin 2))) =
            (Finset.univ : Finset (S → Fin 2)) ×ˢ
              (Finset.univ : Finset ({k // k ∉ S} → Fin 2)) from rfl]
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl ?_
      intro ws _
      -- For fixed (zs, ws), Σ_{w_out} [hval] = restrictedMatrixEntry zs ws.
      have hwsum :
          ∑ w_out : {k // k ∉ S} → Fin 2,
            O ((Qubits.bitStringEquiv N) (E.symm (zs, z_out)))
              ((Qubits.bitStringEquiv N) (E.symm (ws, w_out))) =
          ∑ w_out : {k // k ∉ S} → Fin 2,
            (if w_out = z_out then restrictedMatrixEntry S O zs ws else 0) := by
        refine Finset.sum_congr rfl ?_
        intro w_out _
        have := hval (zs, z_out) (ws, w_out)
        -- this : O .. .. = if (z_out = w_out) then ... else 0
        -- we want the if in the form `w_out = z_out`.
        rw [this]
        by_cases heq : w_out = z_out
        · subst heq; simp
        · rw [if_neg heq, if_neg (Ne.symm heq)]
      rw [hwsum, Finset.sum_ite_eq']
      simp
    -- Substitute hinner everywhere:
    refine Eq.trans (b :=
        ∑ x : S → Fin 2, ∑ _y : {k // k ∉ S} → Fin 2,
          ∑ ws : S → Fin 2, restrictedMatrixEntry S O x ws) ?_ ?_
    · refine Finset.sum_congr rfl ?_
      intro zs _
      refine Finset.sum_congr rfl ?_
      intro z_out _
      -- The inner sum is over `Finset.univ ×ˢ Finset.univ`; replace by Finset.univ.
      rw [show
        (Finset.univ : Finset (S → Fin 2)) ×ˢ
            (Finset.univ : Finset ({k // k ∉ S} → Fin 2)) =
        (Finset.univ : Finset ((S → Fin 2) × ({k // k ∉ S} → Fin 2))) from rfl]
      exact hinner zs z_out
    -- Now: Σ_{zs} Σ_{z_out} Σ_{ws} f(zs, ws) = card(z_out) · Σ_{zs} Σ_{ws} f.
    have hcard_compl : (Finset.univ : Finset ({k : Fin N // k ∉ S})).card = N - S.card := by
      rw [Finset.card_univ]
      rw [Fintype.card_subtype_compl]
      simp [Fintype.card_coe]
    have hcard_fun : (Finset.univ : Finset ({k : Fin N // k ∉ S} → Fin 2)).card =
        2 ^ (N - S.card) := by
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
      rw [show Fintype.card { k : Fin N // k ∉ S } = N - S.card from ?_]
      have := hcard_compl
      rw [Finset.card_univ] at this
      exact this
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro x _
    rw [Finset.sum_const, hcard_fun, nsmul_eq_mul]
  rw [hkey]
  -- Final algebra: (1/2^N) * (2^(N-|S|) * X) = (1/2^|S|) * X.
  have hSle : S.card ≤ N := by
    have : S.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ _
    simpa using this
  have hpow_split : (Qubits.NQubitDim N : ℕ) = 2 ^ (N - S.card) * 2 ^ S.card := by
    show 2 ^ N = 2 ^ (N - S.card) * 2 ^ S.card
    rw [← pow_add, Nat.sub_add_cancel hSle]
  have h2_ne : ((2 ^ S.card : ℕ) : ℂ) ≠ 0 := by
    have : (2 ^ S.card : ℕ) ≠ 0 := pow_ne_zero _ (by decide)
    exact_mod_cast this
  have h2c_ne : ((2 ^ (N - S.card) : ℕ) : ℂ) ≠ 0 := by
    have : (2 ^ (N - S.card) : ℕ) ≠ 0 := pow_ne_zero _ (by decide)
    exact_mod_cast this
  have h2N_eq : ((Qubits.NQubitDim N : ℕ) : ℂ) =
      ((2 ^ (N - S.card) : ℕ) : ℂ) * ((2 ^ S.card : ℕ) : ℂ) := by
    exact_mod_cast hpow_split
  rw [h2N_eq]
  field_simp

end

end QAOA.IsingChain.UpperBound.LightCone
