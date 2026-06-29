import QuantumOptimization.QAOA.IsingChain.JordanWigner.Transformation.Operators

/-!
# Jordan–Wigner Image of the Reduced Hamiltonians — mixer image, body/wrap bond bilinears, even-parity cost image

This file computes the Jordan–Wigner image of the reduced-chain mixer and cost
Hamiltonians. It builds on the JW operators and CAR in `Operators`.

The mixer maps to the global field `−∑_j X_j`. Interior bonds `Z_k Z_{k+1}` map
to the bare fermion bilinear `(c_k† − c_k)(c_{k+1}† + c_{k+1})`; the periodic wrap
bond carries an extra parity factor (spin-ABC ↔ fermion-PBC), which is trivial on
the even-parity sector — yielding the PRIMARY state-applied deliverable
`Hred_z_image_even` and its expectation-value corollary.

## Main definitions

* `bodyBilinear`: the interior-bond fermion bilinear `(c_k† − c_k)(c_{k+1}† + c_{k+1})`.
* `wrapBilinear`: the bare periodic wrap-bond bilinear `(c_last† − c_last)(c_0† + c_0)`.

## Main statements

* `Hred_x_image`: JW image of the reduced mixer Hamiltonian `−∑_j X_j`.
* `bond_image_of_succ`, `bond_image_body`: interior bond `Z_j Z_{j'}` image.
* `bond_image_wrap`: structural wrap bond carrying the parity factor.
* `Hred_z_shift_eq`, `Hred_z_shift_fermion`: the `+N_R·I`-shifted cost Hamiltonian
  as a fermion bilinear sum.
* `Hred_z_image_even` (PRIMARY): even-parity-sector cost image with periodic wrap.
* `Hred_z_image_even_expectation`: derived scalar matrix-element corollary.

## Source pins

* JW image of Hamiltonians + "spin PBC ↔ fermion ABC": arXiv:1911.12259v2
  (`QAOA_arXiv.tex`) l.761–768. See `Operators.lean` for the full source pin list.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Jordan–Wigner image of the reduced Hamiltonians
-- ============================================================================

/-- Per-site mixer image: `c_j† c_j - c_j c_j† = -X_j`. -/
theorem numberOp_sub_hole_eq {N : ℕ} (j : Fin N) :
    cCreate j * cAnnih j - cAnnih j * cCreate j = - localPauliX j := by
  have h1 : cCreate j * cAnnih j = numberOp j := rfl
  rw [h1, numberOp_eq, cAnnih_mul_cCreate_same, ← smul_sub]
  rw [show (1 - localPauliX j) - (1 + localPauliX j) = (-2 : ℂ) • localPauliX j by
    rw [neg_smul, two_smul]; abel]
  rw [smul_smul]
  norm_num

/-- JW image of the reduced mixer Hamiltonian:
`Hred_x_op P = Σ_j (c_j† c_j - c_j c_j†) = −∑_{all j} X_j`, the sum running over
**all** `N_R = 2P+2` sites.

Note on the source: eq. (762) of arXiv:1911.12259v2 writes the range as
`j = 1 .. N_R − 1`, but that range is a typo — the mixer is the global field
`−∑_j X_j` over every site (`Hred_x_op = QAOA.standardMixerOp`, which sums over
`Finset.univ`). The Lean statement (full sum) is the correct one and is what the
numerical check (4a) verifies; the lemma is intentionally stated over all sites. -/
theorem Hred_x_image (P : ℕ) :
    UpperBound.Hred_x_op P =
      ∑ j : Fin (2*P+2), (cCreate j * cAnnih j - cAnnih j * cCreate j) := by
  rw [UpperBound.Hred_x_op, QAOA.standardMixerOp, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun j _ => (numberOp_sub_hole_eq j).symm)

/-- String telescope across one bond: if `j.val + 1 = j'.val` then
`jwString j' = jwString j * X_j`. -/
theorem jwString_succ {N : ℕ} {j j' : Fin N} (hsucc : j.val + 1 = j'.val) :
    jwString j' = jwString j * localPauliX j := by
  have hset : (Finset.univ.filter (· < j')) =
      insert j (Finset.univ.filter (· < j)) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro hm
      have hmlt : m.val < j.val + 1 := hsucc ▸ hm
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hmlt) with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · intro hm
      rcases hm with h | h
      · subst h
        exact (Fin.lt_def).mpr (by omega)
      · exact (Fin.lt_def).mpr (by have := (Fin.lt_def).mp h; omega)
  have hnotmem : j ∉ Finset.univ.filter (· < j) := by simp
  rw [jwString, jwString,
      Finset.noncommProd_congr hset (fun _ _ => rfl) (localPauliX_pairwise_commute _),
      Finset.noncommProd_insert_of_notMem' _ _ _ _ hnotmem]

/-- `c_j† - c_j = i · (string_j · Y_j)`. -/
theorem cCreate_sub_cAnnih {N : ℕ} (j : Fin N) :
    cCreate j - cAnnih j = Complex.I • (jwString j * localPauliY j) := by
  unfold cCreate cAnnih
  rw [← (jwString_commute_localPart j Complex.I).eq, ← mul_sub]
  rw [show ((1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j) -
        (1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j)) =
        Complex.I • localPauliY j by
    rw [smul_add, smul_sub]; module]
  rw [mul_smul_comm]

/-- `c_j† + c_j = string_j · Z_j`. -/
theorem cCreate_add_cAnnih {N : ℕ} (j : Fin N) :
    cCreate j + cAnnih j = jwString j * localPauliZ j := by
  unfold cCreate cAnnih
  rw [← (jwString_commute_localPart j Complex.I).eq, ← mul_add]
  congr 1
  rw [smul_add, smul_sub]
  rw [show (1/2 : ℂ) • localPauliZ j + (1/2 : ℂ) • Complex.I • localPauliY j +
        ((1/2 : ℂ) • localPauliZ j - (1/2 : ℂ) • Complex.I • localPauliY j) =
        (2 * (1/2) : ℂ) • localPauliZ j by
    rw [two_mul]; module]
  rw [show (2 * (1/2) : ℂ) = 1 by norm_num, one_smul]

/-- JW image of an interior bond between sites `j, j'` with `j.val + 1 = j'.val`:
`Z_j Z_{j'} = (c_j† - c_j)(c_{j'}† + c_{j'})`. (source l.764 body; numerical check (4b)). -/
theorem bond_image_of_succ {N : ℕ} {j j' : Fin N} (hsucc : j.val + 1 = j'.val) :
    localPauliZ j * localPauliZ j' =
      (cCreate j - cAnnih j) * (cCreate j' + cAnnih j') := by
  rw [cCreate_sub_cAnnih, cCreate_add_cAnnih, jwString_succ hsucc]
  have hYstr : Commute (localPauliY j) (jwString j) :=
    (jwString_commute_localPauliY_of_le (le_refl j)).symm
  -- RHS = i • (string_j Y_j) * (string_j X_j Z_{j'})
  rw [smul_mul_assoc]
  -- collapse the strings: (string_j Y_j)(string_j X_j Z_{j'}) = Y_j X_j Z_{j'}
  have hcollapse : (jwString j * localPauliY j) *
      (jwString j * localPauliX j * localPauliZ j') =
      localPauliY j * localPauliX j * localPauliZ j' := by
    calc (jwString j * localPauliY j) * (jwString j * localPauliX j * localPauliZ j')
        = jwString j * (localPauliY j * jwString j) *
            (localPauliX j * localPauliZ j') := by
              simp only [mul_assoc]
      _ = jwString j * (jwString j * localPauliY j) *
            (localPauliX j * localPauliZ j') := by rw [hYstr.eq]
      _ = (jwString j * jwString j) *
            (localPauliY j * (localPauliX j * localPauliZ j')) := by
              simp only [mul_assoc]
      _ = localPauliY j * localPauliX j * localPauliZ j' := by
              rw [jwString_sq_eq_one, one_mul]; simp only [mul_assoc]
  rw [hcollapse]
  -- i • (Y_j X_j Z_{j'}) = Z_j Z_{j'}
  rw [localPauliY_mul_localPauliX_anti, neg_mul, smul_neg, ← neg_smul]
  rw [localPauliX_mul_localPauliY, smul_mul_assoc, smul_smul,
      show -Complex.I * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I]; ring,
      one_smul]

/-- JW image of an interior reduced-chain bond `k : Fin (2P+1)`:
`Z_{k} Z_{k+1} = (c_k† - c_k)(c_{k+1}† + c_{k+1})`. -/
theorem bond_image_body (P : ℕ) (k : Fin (2 * P + 1)) :
    localPauliZ (k.castSucc : Fin (2*P+2)) *
        localPauliZ ((k.castSucc : Fin (2*P+2)) + 1) =
      (cCreate (k.castSucc : Fin (2*P+2)) - cAnnih (k.castSucc : Fin (2*P+2))) *
        (cCreate ((k.castSucc : Fin (2*P+2)) + 1) +
          cAnnih ((k.castSucc : Fin (2*P+2)) + 1)) := by
  apply bond_image_of_succ
  rw [Fin.val_add_one]
  simp [(Fin.castSucc_lt_last k).ne]

-- ----------------------------------------------------------------------------
-- Subsection: The wrap bond (structural — parity dressing) and even-parity image
-- ----------------------------------------------------------------------------

/-- The empty Jordan–Wigner string at site `0` is the identity. -/
theorem jwString_zero {N : ℕ} (h : 0 < N) : jwString (⟨0, h⟩ : Fin N) = 1 := by
  unfold jwString
  have hempty : (Finset.univ.filter (· < (⟨0, h⟩ : Fin N))) = ∅ := by
    ext m; simp [Fin.lt_def]
  rw [Finset.noncommProd_congr hempty (fun _ _ => rfl) (localPauliX_pairwise_commute _),
      Finset.noncommProd_empty]

/-- The parity operator equals the full string times the last `X`:
`parityOp = jwString (last) · X_last`. -/
theorem parityOp_eq_jwString_last (P : ℕ) :
    parityOp (2*P+2) =
      jwString (Fin.last (2*P+1)) * localPauliX (Fin.last (2*P+1)) := by
  unfold parityOp jwString
  have hset : (Finset.univ : Finset (Fin (2*P+2))) =
      insert (Fin.last (2*P+1)) (Finset.univ.filter (· < Fin.last (2*P+1))) := by
    ext m
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_filter, true_and]
    rcases eq_or_lt_of_le (Fin.le_last m) with h | h
    · exact ⟨fun _ => Or.inl h, fun _ => trivial⟩
    · exact ⟨fun _ => Or.inr h, fun _ => trivial⟩
  rw [Finset.noncommProd_congr hset (fun _ _ => rfl) (localPauliX_pairwise_commute _),
      Finset.noncommProd_insert_of_notMem' _ _ _ _ (by simp)]

/-- STRUCTURAL: the wrap bond `Z_{N_R−1} Z_0` is **not** the bare fermion bilinear;
the exact full-space identity carries the parity factor:
`Z_{last} Z_0 = -(c_last† - c_last)(c_0† + c_0) · parityOp`. (source l.768;
reviewer-verified `dev = 0` at `N_R = 4, 6`). -/
theorem bond_image_wrap (P : ℕ) :
    localPauliZ (Fin.last (2*P+1)) * localPauliZ (0 : Fin (2*P+2)) =
      - ((cCreate (Fin.last (2*P+1)) - cAnnih (Fin.last (2*P+1))) *
          (cCreate (0 : Fin (2*P+2)) + cAnnih (0 : Fin (2*P+2)))) *
        parityOp (2*P+2) := by
  have h0lt : (0 : Fin (2*P+2)) < Fin.last (2*P+1) := by
    rw [Fin.lt_def]; simp
  -- c_0† + c_0 = Z_0 (string_0 = 1)
  have hPlus0 : cCreate (0 : Fin (2*P+2)) + cAnnih (0 : Fin (2*P+2)) =
      localPauliZ (0 : Fin (2*P+2)) := by
    rw [cCreate_add_cAnnih]
    rw [show (0 : Fin (2*P+2)) = (⟨0, by omega⟩ : Fin (2*P+2)) from rfl, jwString_zero,
        one_mul]
  -- c_last† - c_last = i • (string_last * Y_last)
  rw [cCreate_sub_cAnnih, hPlus0, parityOp_eq_jwString_last]
  set s := jwString (Fin.last (2*P+1)) with hs
  set Yl := localPauliY (Fin.last (2*P+1)) with hYl
  set Xl := localPauliX (Fin.last (2*P+1)) with hXl
  set Z0 := localPauliZ (0 : Fin (2*P+2)) with hZ0
  -- RHS = -(i • (s * Yl) * Z0) * (s * Xl)
  have hZ0s : Z0 * s = - (s * Z0) := by
    rw [hZ0, hs]; exact localPauliZ_anticomm_jwString_of_lt h0lt
  have hYls : Commute Yl s := by
    rw [hYl, hs]; exact (jwString_commute_localPauliY_of_le (le_refl _)).symm
  have hZ0Xl : Commute Z0 Xl := by
    rw [hZ0, hXl]
    exact localPauliZ_commute_localPauliX (ne_of_lt h0lt)
  calc localPauliZ (Fin.last (2*P+1)) * Z0
      = Complex.I • (Yl * Xl * Z0) := by
          rw [hYl, hXl, hZ0, localPauliY_mul_localPauliX_anti, neg_mul, smul_neg,
              ← neg_smul, localPauliX_mul_localPauliY, smul_mul_assoc, smul_smul,
              show -Complex.I * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I]; ring,
              one_smul]
    _ = Complex.I • (Yl * (Z0 * Xl)) := by rw [hZ0Xl.eq, ← mul_assoc]
    _ = Complex.I • ((s * s) * Yl * (Z0 * Xl)) := by
          rw [jwString_sq_eq_one, one_mul]
    _ = Complex.I • (s * (Yl * s) * (Z0 * Xl)) := by
          rw [hYls.eq]; simp only [mul_assoc]
    _ = Complex.I • (s * Yl * (s * Z0) * Xl) := by simp only [mul_assoc]
    _ = Complex.I • (s * Yl * (- (Z0 * s)) * Xl) := by rw [hZ0s, neg_neg]
    _ = - (Complex.I • (s * Yl * Z0 * (s * Xl))) := by
          rw [mul_neg, neg_mul, smul_neg]; simp only [mul_assoc]
    _ = - (Complex.I • (s * Yl) * Z0) * (s * Xl) := by
          rw [neg_mul, smul_mul_assoc, smul_mul_assoc]

/-- `nextSite (k.castSucc) = k.castSucc + 1` for an interior reduced-chain bond. -/
private theorem nextSite_castSucc (P : ℕ) (k : Fin (2 * P + 1)) :
    IsingModel.nextSite (k.castSucc : Fin (2*P+2)) = (k.castSucc : Fin (2*P+2)) + 1 := by
  apply Fin.ext
  change ((k.castSucc : Fin (2*P+2)).val + 1) % (2*P+2) = ((k.castSucc : Fin (2*P+2)) + 1).val
  rw [Fin.val_add_one]
  simp only [(Fin.castSucc_lt_last k).ne, if_false]
  have hk : (k.castSucc : Fin (2*P+2)).val = (k : ℕ) := rfl
  rw [hk, Nat.mod_eq_of_lt (by have := k.isLt; omega)]

/-- `nextSite (Fin.last (2P+1)) = 0`. -/
private theorem nextSite_last (P : ℕ) :
    IsingModel.nextSite (Fin.last (2*P+1) : Fin (2*P+2)) = (0 : Fin (2*P+2)) := by
  apply Fin.ext
  change ((Fin.last (2*P+1) : Fin (2*P+2)).val + 1) % (2*P+2) = (0 : Fin (2*P+2)).val
  simp [Fin.val_last]

/-- Interior `chainPairInteraction` equals the adjacent `Z·Z` bond. -/
private theorem chainPairInteraction_castSucc (P : ℕ) (k : Fin (2 * P + 1)) :
    IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) =
      localPauliZ (k.castSucc : Fin (2*P+2)) * localPauliZ ((k.castSucc : Fin (2*P+2)) + 1) := by
  rw [IsingModel.chainPairInteraction, nextSite_castSucc]

/-- Boundary `chainPairInteraction` equals the wrap `Z·Z` bond. -/
private theorem chainPairInteraction_last (P : ℕ) :
    IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) =
      localPauliZ (Fin.last (2*P+1)) * localPauliZ (0 : Fin (2*P+2)) := by
  rw [IsingModel.chainPairInteraction, nextSite_last]

/-- The fermion bilinear for the interior bond `k ↦ k+1` of the reduced chain:
`(c_k† − c_k)(c_{k+1}† + c_{k+1})`. By `bond_image_body` this equals the spin bond
`Z_k Z_{k+1}` exactly (no parity dressing on interior bonds). -/
def bodyBilinear (P : ℕ) (k : Fin (2 * P + 1)) : NQubitOp (2*P+2) :=
  (cCreate (k.castSucc : Fin (2*P+2)) - cAnnih (k.castSucc : Fin (2*P+2))) *
    (cCreate ((k.castSucc : Fin (2*P+2)) + 1) + cAnnih ((k.castSucc : Fin (2*P+2)) + 1))

/-- The fermion bilinear for the periodic wrap bond `(last) ↦ 0`:
`(c_last† − c_last)(c_0† + c_0)`. This is the *bare* (PBC) bilinear; the exact
spin wrap bond carries an extra parity factor (`bond_image_wrap`), which becomes
trivial on the even-parity sector. Realizes spin-ABC ↔ fermion-PBC. -/
def wrapBilinear (P : ℕ) : NQubitOp (2*P+2) :=
  (cCreate (Fin.last (2*P+1)) - cAnnih (Fin.last (2*P+1))) *
    (cCreate (0 : Fin (2*P+2)) + cAnnih (0 : Fin (2*P+2)))

/-- The reduced cost Hamiltonian plus the `+N_R·I` shift collapses (the per-bond
`−1` constants and the `+N_R` cancel) to the bare bond sum minus the wrap bond. -/
theorem Hred_z_shift_eq (P : ℕ) :
    UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2)) =
      (∑ k : Fin (2*P+1), IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)))
        - IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) := by
  rw [UpperBound.Hred_z_pm, UpperBound.Hred_z_body, UpperBound.Hred_z_boundary]
  simp only [Bool.false_eq_true, if_false]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [neg_one_smul]
  -- convert the `nsmul` constant to a `ℂ`-smul, then collect.
  rw [show ((2*P+1 : ℕ) • (1 : NQubitOp (2*P+2))) =
        ((2*P+1 : ℕ) : ℂ) • (1 : NQubitOp (2*P+2)) by
    rw [Nat.cast_smul_eq_nsmul]]
  rw [show ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2)) =
        ((2*P+1 : ℕ) : ℂ) • (1 : NQubitOp (2*P+2)) + (1 : NQubitOp (2*P+2)) by
    push_cast; module]
  abel

/-- Operator form of the collapsed cost Hamiltonian: bond sum minus wrap bond
becomes the body bilinear sum minus `bilinear · parityOp` (the latter via the
structural wrap identity). -/
theorem Hred_z_shift_fermion (P : ℕ) :
    UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2)) =
      (∑ k : Fin (2*P+1), bodyBilinear P k) + wrapBilinear P * parityOp (2*P+2) := by
  rw [Hred_z_shift_eq]
  have hbody : (∑ k : Fin (2*P+1), IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)))
      = ∑ k : Fin (2*P+1), bodyBilinear P k := by
    apply Finset.sum_congr rfl
    intro k _
    rw [chainPairInteraction_castSucc, bond_image_body]
    rfl
  have hwrap : - IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) =
      wrapBilinear P * parityOp (2*P+2) := by
    rw [chainPairInteraction_last, bond_image_wrap, neg_mul, neg_neg]
    rfl
  rw [hbody, sub_eq_add_neg, hwrap]

/-- STRUCTURAL (state-applied, PRIMARY deliverable): on the even-parity sector
`parityOp · ψ = ψ`, the reduced cost Hamiltonian (with the `+N_R·I` shift) acts
as the fermion bilinear with a **periodic** wrap (spin-ABC ↔ fermion-PBC,
source l.768). -/
theorem Hred_z_image_even (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : parityOp (2 * P + 2) * ψ = ψ) :
    (UpperBound.Hred_z_pm false P + ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2))) * ψ =
      ((∑ k : Fin (2*P+1), bodyBilinear P k) + wrapBilinear P) * ψ := by
  rw [Hred_z_shift_fermion]
  rw [add_op_mul_ket, add_op_mul_ket]
  congr 1
  rw [op_mul_op_mul_ket, hψ]

/-- DERIVED COROLLARY (scalar matrix element): pairing the state-applied identity
with any bra `φ`. With `φ = ⟨ψ|` this is the expectation-value form
`⟨ψ| (Hred_z + N_R·I) |ψ⟩ = ⟨ψ| (Σ body + wrap) |ψ⟩` (numerical check (4c)). -/
theorem Hred_z_image_even_expectation (P : ℕ) (φ : Bra (NQubitDim (2 * P + 2)))
    (ψ : NQubitKet (2 * P + 2)) (hψ : parityOp (2 * P + 2) * ψ = ψ) :
    φ * ((UpperBound.Hred_z_pm false P +
        ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2))) * ψ) =
      φ * (((∑ k : Fin (2*P+1), bodyBilinear P k) + wrapBilinear P) * ψ) := by
  rw [Hred_z_image_even P ψ hψ]

end

end QAOA.IsingChain.JordanWigner
