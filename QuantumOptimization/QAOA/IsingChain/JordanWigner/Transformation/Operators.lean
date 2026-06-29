import QuantumOptimization.QAOA.IsingChain.JordanWigner.Transformation.PauliAlgebra

/-!
# Jordan–Wigner Operators and CAR — jwString, cAnnih/cCreate, numberOp, parityOp, reconstructions, anticommutation relations

This file defines the Jordan–Wigner (JW) map in its validated **X-quantized** form
on the reduced-chain qubit register and proves the canonical anticommutation
relations (CAR). It builds on the single-site Pauli algebra in `PauliAlgebra`.

## Conventions (X-quantized — validated numerically)

The occupation is read off the Pauli `X` axis (`n_j = (1 - X_j)/2`), which is the
source's own convention (arXiv:1911.12259v2 l.748, `σ^x_j = 1 - 2 c_j† c_j`).
The Z-quantized candidate is incorrect. The validated forms are:

* `jwString j = ∏_{k < j} localPauliX k`   (note `+X_k`, realizing
  `exp(-iπ Σ_{l<j} n_l)`).
* `cAnnih j  = jwString j * ((1/2) • (Z_j - i Y_j))`   (string-before-local).
* `cCreate j = ((1/2) • (Z_j + i Y_j)) * jwString j`   (local-before-string).
* `numberOp j = cCreate j * cAnnih j = (1/2) • (1 - X_j)`, so `σ^x_j = 1 - 2 n_j`.
* `parityOp = ∏_j localPauliX j` is the conserved even-parity operator.

Every identity below was verified numerically at machine precision (max dev ≤ ~2e-15)
at `N_R = 4` (P=1) and `N_R = 6` (P=2).

## Main definitions

* `jwString`, `cAnnih`, `cCreate`, `numberOp`, `parityOp`.

## Main statements

* `jwString` Hermiticity / square / commutation (`jwString_hermitian`,
  `jwString_sq_eq_one`, `jwString_commute_*`); same for `parityOp`.
* `cCreate_eq_adjoint`: `cCreate j = (cAnnih j)†`.
* Discriminating reconstructions: `sigmaX_reconstruction`, `sigmaZ_reconstruction`,
  `numberOp_eq`.
* CAR triple: `car_annih_create`, `car_annih_annih`, `car_create_create`.

## Source pins

* JW map + σ-reconstruction: arXiv:1911.12259v2 (`QAOA_arXiv.tex`) l.748–749.
* CAR / neighbor-phase cancellation: arXiv:1706.02998v2 §VI.B l.657–676.

The exponential equivalence `jwString j = exp(-iπ Σ_{l<j} numberOp l)` was
verified numerically (numerical check (1a)) but is **not** stated here as a
Lean lemma: downstream files consume `jwString` as the `∏ X_k` product directly,
and the matrix-exponential route would pull `Matrix.exp` infrastructure into scope
for no load-bearing gain.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Jordan–Wigner operators
-- ============================================================================

/-!
The Jordan–Wigner map in its validated **X-quantized** form. Each fermion mode
carries a string of Pauli-`X` operators on the preceding sites; the local part
is `(Z_j ∓ i Y_j)/2`. All scalar multiplications are `(c : ℂ) • Op`, the module
structure on `NQubitOp N = Op (2^N)`.
-/

/-- The lifted Pauli-`X` operators pairwise commute (for all pairs, including
equal indices), as needed for noncommutative finite products. -/
theorem localPauliX_pairwise_commute {N : ℕ} (s : Finset (Fin N)) :
    (↑s : Set (Fin N)).Pairwise (Function.onFun Commute (fun k => localPauliX k)) :=
  fun i _ j _ _ => localPauliX_commute i j

/-- The Jordan–Wigner string at site `j`: `∏_{k < j} X_k` (noncommutative product
over commuting `X`-factors). Realizes `exp(-iπ Σ_{l<j} n_l)` (numerical check (1a)). -/
def jwString {N : ℕ} (j : Fin N) : NQubitOp N :=
  (Finset.univ.filter (· < j)).noncommProd (fun k => localPauliX k)
    (localPauliX_pairwise_commute _)

/-- The fermion annihilation operator `c_j = (∏_{k<j} X_k) · (Z_j - i Y_j)/2`
(string-before-local). -/
def cAnnih {N : ℕ} (j : Fin N) : NQubitOp N :=
  jwString j * ((1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j))

/-- The fermion creation operator `c_j† = (Z_j + i Y_j)/2 · (∏_{k<j} X_k)`
(local-before-string). -/
def cCreate {N : ℕ} (j : Fin N) : NQubitOp N :=
  ((1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j)) * jwString j

/-- The fermion number operator at site `j`, `n_j = c_j† c_j`. -/
def numberOp {N : ℕ} (j : Fin N) : NQubitOp N :=
  cCreate j * cAnnih j

/-- The conserved even-parity operator `P = ∏_j X_j` (source l.745). -/
def parityOp (N : ℕ) : NQubitOp N :=
  (Finset.univ : Finset (Fin N)).noncommProd (fun k => localPauliX k)
    (localPauliX_pairwise_commute _)

-- ----------------------------------------------------------------------------
-- Subsection: jwString / parityOp structural lemmas
-- ----------------------------------------------------------------------------

/-- A noncommutative product of pairwise-commuting Hermitian involutions is itself
a Hermitian involution that commutes with each factor. Stated for the lifted
Pauli-`X` family, which is exactly this situation. -/
private theorem noncommProd_localPauliX_props {N : ℕ} (s : Finset (Fin N)) :
    (s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _))† =
      s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _) ∧
    (s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _)) *
      (s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _)) = 1 ∧
    (∀ i : Fin N, Commute (s.noncommProd (fun k => localPauliX k)
      (localPauliX_pairwise_commute _)) (localPauliX i)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨?_, ?_, ?_⟩
      · simp [Finset.noncommProd_empty]
      · simp [Finset.noncommProd_empty]
      · intro i; rw [Finset.noncommProd_empty]; exact Commute.one_left _
  | insert a s ha ih =>
      obtain ⟨ihHerm, ihSq, ihComm⟩ := ih
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      set P := s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _) with hP
      refine ⟨?_, ?_, ?_⟩
      · rw [Matrix.conjTranspose_mul, ihHerm, localPauliX_hermitian]
        exact (ihComm a).eq
      · calc (localPauliX a * P) * (localPauliX a * P)
            = localPauliX a * ((P * localPauliX a) * P) := by
                rw [mul_assoc, mul_assoc]
          _ = localPauliX a * ((localPauliX a * P) * P) := by rw [(ihComm a).eq]
          _ = (localPauliX a * localPauliX a) * (P * P) := by
                rw [mul_assoc, mul_assoc]
          _ = 1 := by rw [localPauliX_sq, ihSq, one_mul]
      · intro i
        exact (Commute.mul_left (localPauliX_commute a i) (ihComm i))

/-- The Jordan–Wigner string is Hermitian. -/
theorem jwString_hermitian {N : ℕ} (j : Fin N) : (jwString j)† = jwString j :=
  (noncommProd_localPauliX_props _).1

/-- The Jordan–Wigner string squares to the identity. -/
theorem jwString_sq_eq_one {N : ℕ} (j : Fin N) : jwString j * jwString j = 1 :=
  (noncommProd_localPauliX_props _).2.1

/-- The Jordan–Wigner string commutes with `localPauliX i` for every site `i`. -/
theorem jwString_commute_localPauliX {N : ℕ} (j i : Fin N) :
    Commute (jwString j) (localPauliX i) :=
  (noncommProd_localPauliX_props _).2.2 i

/-- The parity operator is Hermitian. -/
theorem parityOp_hermitian (N : ℕ) : (parityOp N)† = parityOp N :=
  (noncommProd_localPauliX_props _).1

/-- The parity operator squares to the identity. -/
theorem parityOp_sq_eq_one (N : ℕ) : parityOp N * parityOp N = 1 :=
  (noncommProd_localPauliX_props _).2.1

/-- The parity operator commutes with `localPauliX i` for every site `i`. -/
theorem parityOp_commute_localPauliX {N : ℕ} (i : Fin N) :
    Commute (parityOp N) (localPauliX i) :=
  (noncommProd_localPauliX_props _).2.2 i

/-- If `B` commutes with `localPauliX k` for every `k < j`, then `B` commutes
with `jwString j`. -/
theorem jwString_commute_of_forall {N : ℕ} (j : Fin N) (B : NQubitOp N)
    (h : ∀ k : Fin N, k < j → Commute B (localPauliX k)) :
    Commute B (jwString j) := by
  unfold jwString
  refine Finset.noncommProd_commute _ _ _ _ ?_
  intro k hk
  exact h k (Finset.mem_filter.mp hk).2

/-- `jwString j` commutes with `localPauliZ i` whenever `j ≤ i` (the string
factors live strictly below `j ≤ i`, so all are at sites `≠ i`). -/
theorem jwString_commute_localPauliZ_of_le {N : ℕ} {j i : Fin N} (hji : j ≤ i) :
    Commute (jwString j) (localPauliZ i) :=
  (jwString_commute_of_forall j (localPauliZ i)
    (fun k hk => (localPauliZ_commute_localPauliX
      (j := i) (k := k) (ne_of_gt (lt_of_lt_of_le hk hji))))).symm

/-- `jwString j` commutes with `localPauliY i` whenever `j ≤ i`. -/
theorem jwString_commute_localPauliY_of_le {N : ℕ} {j i : Fin N} (hji : j ≤ i) :
    Commute (jwString j) (localPauliY i) :=
  (jwString_commute_of_forall j (localPauliY i)
    (fun k hk => (localPauliY_commute_localPauliX
      (j := i) (k := k) (ne_of_gt (lt_of_lt_of_le hk hji))))).symm

-- ----------------------------------------------------------------------------
-- Subsection: Adjoint relation between cCreate and cAnnih
-- ----------------------------------------------------------------------------

/-- The creation operator is the adjoint of the annihilation operator:
`cCreate j = (cAnnih j)†`. -/
theorem cCreate_eq_adjoint {N : ℕ} (j : Fin N) : cCreate j = (cAnnih j)† := by
  unfold cCreate cAnnih
  rw [Matrix.conjTranspose_mul, jwString_hermitian,
      Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, localPauliZ_hermitian, localPauliY_hermitian]
  congr 1
  rw [show star (1/2 : ℂ) = (1/2 : ℂ) by norm_num]
  rw [Complex.star_def, Complex.conj_I, neg_smul, sub_neg_eq_add]

-- ----------------------------------------------------------------------------
-- Subsection: Reconstruction identities (discriminating checks)
-- ----------------------------------------------------------------------------

/-- Single-site product `Z_j Y_j = -i X_j` (from `Y_j Z_j = i X_j` and
`{Y_j, Z_j} = 0`). -/
theorem localPauliZ_mul_localPauliY {N : ℕ} (j : Fin N) :
    localPauliZ j * localPauliY j = (-Complex.I) • localPauliX j := by
  have h := localPauliY_anticomm_localPauliZ j
  have hZY : localPauliZ j * localPauliY j = -(localPauliY j * localPauliZ j) :=
    eq_neg_of_add_eq_zero_right (add_comm (localPauliY j * localPauliZ j)
      (localPauliZ j * localPauliY j) ▸ h)
  rw [hZY, localPauliY_mul_localPauliZ, ← neg_smul]

/-- The operator product `(Z_j + iY_j)(Z_j - iY_j) = 2(1 - X_j)`. -/
theorem localPart_product {N : ℕ} (j : Fin N) :
    (localPauliZ j + Complex.I • localPauliY j) *
      (localPauliZ j - Complex.I • localPauliY j) =
      (2 : ℂ) • (1 - localPauliX j) := by
  rw [mul_sub, add_mul, add_mul]
  rw [localPauliZ_sq]
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      localPauliY_mul_localPauliZ, localPauliZ_mul_localPauliY, localPauliY_sq]
  rw [smul_smul, smul_smul, smul_smul]
  simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_one_smul]
  module

/-- The local-part product `((Z_j + iY_j)/2)((Z_j - iY_j)/2) = (1 - X_j)/2`. -/
theorem localPart_number {N : ℕ} (j : Fin N) :
    ((1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j)) *
      ((1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j)) =
      (1/2 : ℂ) • (1 - localPauliX j) := by
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, localPart_product, smul_smul]
  congr 1
  norm_num

/-- The number operator equals `(1 - X_j)/2` (occupation read off the `X` axis). -/
theorem numberOp_eq {N : ℕ} (j : Fin N) :
    numberOp j = (1/2 : ℂ) • (1 - localPauliX j) := by
  unfold numberOp cCreate cAnnih
  rw [mul_assoc, ← mul_assoc (jwString j) (jwString j), jwString_sq_eq_one, one_mul]
  exact localPart_number j

/-- Discriminating reconstruction `1 - 2 n_j = X_j` (source l.748). This pins the
X-quantization axis: the CAR triple alone does NOT determine it. -/
theorem sigmaX_reconstruction {N : ℕ} (j : Fin N) :
    (1 : NQubitOp N) - (2 : ℂ) • numberOp j = localPauliX j := by
  rw [numberOp_eq, smul_smul]
  rw [show (2 : ℂ) * (1/2) = 1 by norm_num, one_smul]
  rw [sub_sub_cancel]

/-- `jwString j` commutes with the same-site local fermion part `(Z_j ± iY_j)/2`. -/
theorem jwString_commute_localPart {N : ℕ} (j : Fin N) (s : ℂ) :
    Commute (jwString j) ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j)) := by
  apply Commute.smul_right
  apply Commute.add_right
  · exact jwString_commute_localPauliZ_of_le (le_refl j)
  · exact (jwString_commute_localPauliY_of_le (le_refl j)).smul_right s

/-- Discriminating reconstruction `(c_j + c_j†) · string_j = Z_j` (source l.749
under X-quantization, sign-corrected to `+`; numerical check (2b)). -/
theorem sigmaZ_reconstruction {N : ℕ} (j : Fin N) :
    (cAnnih j + cCreate j) * jwString j = localPauliZ j := by
  unfold cAnnih cCreate
  rw [add_mul]
  -- c_j * string = string * (Z-iY)/2 * string = (Z-iY)/2  (string² = 1, commute)
  have hAnnih :
      jwString j * ((1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j)) * jwString j =
        (1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j) := by
    rw [sub_eq_add_neg, ← neg_smul]
    rw [(jwString_commute_localPart j (-Complex.I)).eq,
        mul_assoc, jwString_sq_eq_one, mul_one]
  have hCreate :
      (1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j) * jwString j * jwString j =
        (1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j) := by
    rw [smul_mul_assoc, smul_mul_assoc, mul_assoc, jwString_sq_eq_one, mul_one]
  rw [hAnnih, hCreate]
  rw [← smul_add]
  rw [show (localPauliZ j - Complex.I • localPauliY j) +
        (localPauliZ j + Complex.I • localPauliY j) = (2 : ℂ) • localPauliZ j by
    rw [two_smul]; abel]
  rw [smul_smul]
  norm_num

-- ============================================================================
-- Section: Canonical Anticommutation Relations (CAR)
-- ============================================================================

/-- The "hole" local product `(Z_j - iY_j)(Z_j + iY_j) = 2(1 + X_j)`. -/
theorem localPart_product_hole {N : ℕ} (j : Fin N) :
    (localPauliZ j - Complex.I • localPauliY j) *
      (localPauliZ j + Complex.I • localPauliY j) =
      (2 : ℂ) • (1 + localPauliX j) := by
  rw [mul_add, sub_mul, sub_mul]
  rw [localPauliZ_sq]
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      localPauliY_mul_localPauliZ, localPauliZ_mul_localPauliY, localPauliY_sq]
  rw [smul_smul, smul_smul, smul_smul]
  simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_one_smul]
  module

/-- `jwString j` commutes with `1 + X_j` (the `X_j` factor is at site `j`, the
string factors are at sites `< j`). -/
private theorem jwString_commute_one_add_X {N : ℕ} (j : Fin N) :
    Commute (jwString j) ((1/2 : ℂ) • (1 + localPauliX j)) := by
  apply Commute.smul_right
  apply Commute.add_right (Commute.one_right _)
  exact jwString_commute_localPauliX j j

/-- The same-site product `c_j c_j† = (1 + X_j)/2`. -/
theorem cAnnih_mul_cCreate_same {N : ℕ} (j : Fin N) :
    cAnnih j * cCreate j = (1/2 : ℂ) • (1 + localPauliX j) := by
  unfold cAnnih cCreate
  -- string * (Z-iY)/2 * ((Z+iY)/2 * string)
  rw [mul_assoc, ← mul_assoc ((1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j))]
  rw [smul_mul_smul_comm, localPart_product_hole, smul_smul]
  rw [show (1/2 : ℂ) * (1/2) * 2 = (1/2) by norm_num]
  rw [← mul_assoc, (jwString_commute_one_add_X j).eq, mul_assoc,
      jwString_sq_eq_one, mul_one]

/-- The "raising" local part is nilpotent: `((Z_j + iY_j)/2)² = 0`. -/
theorem localPart_plus_sq {N : ℕ} (j : Fin N) :
    ((1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j)) *
      ((1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j)) = 0 := by
  rw [smul_mul_smul_comm]
  rw [mul_add, add_mul, add_mul, localPauliZ_sq]
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      localPauliY_mul_localPauliZ, localPauliZ_mul_localPauliY, localPauliY_sq]
  rw [smul_smul, smul_smul, smul_smul]
  simp only [mul_neg, Complex.I_mul_I, neg_neg, one_smul, neg_one_smul]
  module

/-- A generic same-site nilpotency for the local fermion part `(Z_j + s·Y_j)/2`
when `s² = -1` (i.e. `s = ±i`). -/
theorem localPart_gen_sq {N : ℕ} (j : Fin N) {s : ℂ} (hs : s * s = -1) :
    ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j)) *
      ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j)) = 0 := by
  rw [smul_mul_smul_comm]
  rw [mul_add, add_mul, add_mul, localPauliZ_sq]
  rw [mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      localPauliY_mul_localPauliZ, localPauliZ_mul_localPauliY, localPauliY_sq]
  rw [smul_smul, smul_smul, smul_smul]
  rw [mul_neg, hs]
  module

/-- Same-site annihilation square vanishes: `c_j c_j = 0`. -/
theorem cAnnih_mul_cAnnih_same {N : ℕ} (j : Fin N) : cAnnih j * cAnnih j = 0 := by
  unfold cAnnih
  -- string * Lm * (string * Lm) = string * (Lm * string) * Lm
  --   = string * (string * Lm) * Lm = (string * string) * (Lm * Lm)
  rw [mul_assoc, ← mul_assoc ((1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j))]
  rw [sub_eq_add_neg, ← neg_smul]
  rw [← (jwString_commute_localPart j (-Complex.I)).eq]
  rw [← mul_assoc, ← mul_assoc (jwString j) (jwString j), jwString_sq_eq_one, one_mul,
      localPart_gen_sq j (by rw [neg_mul_neg, Complex.I_mul_I])]

/-- Same-site creation square vanishes: `c_j† c_j† = 0`. -/
theorem cCreate_mul_cCreate_same {N : ℕ} (j : Fin N) : cCreate j * cCreate j = 0 := by
  unfold cCreate
  -- Lp * string * (Lp * string) = Lp * (string * Lp) * string
  --   = Lp * (Lp * string) * string = (Lp * Lp) * (string * string)
  rw [mul_assoc, ← mul_assoc (jwString j)]
  rw [(jwString_commute_localPart j Complex.I).eq]
  rw [← mul_assoc, ← mul_assoc, localPart_plus_sq, zero_mul, zero_mul]

-- ----------------------------------------------------------------------------
-- Subsection: String / local-part (anti)commutation for cross-site CAR
-- ----------------------------------------------------------------------------

/-- If `A` anticommutes with `localPauliX a₀` (for some `a₀ ∈ s`) and commutes
with `localPauliX m` for every other `m ∈ s`, then `A` anticommutes with the
noncommutative `X`-product over `s`. (One anticommuting factor flips the overall
sign; the rest pass through.) -/
theorem anticomm_noncommProd_localPauliX {N : ℕ} (A : NQubitOp N)
    (s : Finset (Fin N)) (a₀ : Fin N) (ha₀ : a₀ ∈ s)
    (hanti : A * localPauliX a₀ = -(localPauliX a₀ * A))
    (hcomm : ∀ m ∈ s, m ≠ a₀ → Commute A (localPauliX m)) :
    A * s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _) =
      - (s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _) * A) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact absurd ha₀ (Finset.notMem_empty a₀)
  | insert a s ha ih =>
      rw [Finset.noncommProd_insert_of_notMem _ _ _ _ ha]
      by_cases hae : a = a₀
      · -- the anticommuting factor is the head
        subst hae
        have hrest : ∀ m ∈ s, Commute A (localPauliX m) := by
          intro m hm
          exact hcomm m (Finset.mem_insert_of_mem hm)
            (fun h => ha (h ▸ hm))
        have hAcommP : Commute A
            (s.noncommProd (fun k => localPauliX k) (localPauliX_pairwise_commute _)) :=
          Finset.noncommProd_commute _ _ _ _ (fun m hm => hrest m hm)
        rw [← mul_assoc, hanti, neg_mul, mul_assoc, hAcommP.eq, ← mul_assoc, ← neg_mul]
      · -- the anticommuting factor is in the tail
        have ha₀s : a₀ ∈ s := by
          rcases Finset.mem_insert.mp ha₀ with h | h
          · exact absurd h.symm hae
          · exact h
        have hAcommHead : Commute A (localPauliX a) :=
          hcomm a (Finset.mem_insert_self a s) (fun h => hae h)
        have ihApplied := ih ha₀s
          (fun m hm hm0 => hcomm m (Finset.mem_insert_of_mem hm) hm0)
        rw [← mul_assoc, hAcommHead.eq, mul_assoc, ihApplied, mul_neg, ← mul_assoc]

/-- `Z_j * X_j = -(X_j * Z_j)`. -/
theorem localPauliZ_mul_localPauliX_anti {N : ℕ} (j : Fin N) :
    localPauliZ j * localPauliX j = -(localPauliX j * localPauliZ j) := by
  have h := localPauliX_anticomm_localPauliZ j
  linear_combination (norm := abel) h

/-- `Y_j * X_j = -(X_j * Y_j)`. -/
theorem localPauliY_mul_localPauliX_anti {N : ℕ} (j : Fin N) :
    localPauliY j * localPauliX j = -(localPauliX j * localPauliY j) := by
  have h := localPauliX_anticomm_localPauliY j
  linear_combination (norm := abel) h

/-- `localPauliZ j` anticommutes with `jwString k` for `j < k` (the `X_j` factor of
the string anticommutes with `Z_j`; all other factors commute). -/
theorem localPauliZ_anticomm_jwString_of_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    localPauliZ j * jwString k = -(jwString k * localPauliZ j) := by
  unfold jwString
  apply anticomm_noncommProd_localPauliX (a₀ := j)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk⟩
  · rw [localPauliZ_mul_localPauliX_anti]
  · intro m _ hmj
    exact (localPauliZ_commute_localPauliX hmj.symm)

/-- `localPauliY j` anticommutes with `jwString k` for `j < k`. -/
theorem localPauliY_anticomm_jwString_of_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    localPauliY j * jwString k = -(jwString k * localPauliY j) := by
  unfold jwString
  apply anticomm_noncommProd_localPauliX (a₀ := j)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjk⟩
  · rw [localPauliY_mul_localPauliX_anti]
  · intro m _ hmj
    exact (localPauliY_commute_localPauliX hmj.symm)

/-- The bare local fermion part `Z_j + s·Y_j` anticommutes with `jwString k` for
`j < k`. -/
theorem localPart_bare_anticomm_jwString_of_lt {N : ℕ} {j k : Fin N} (hjk : j < k) (s : ℂ) :
    (localPauliZ j + s • localPauliY j) * jwString k =
      -(jwString k * (localPauliZ j + s • localPauliY j)) := by
  rw [add_mul, smul_mul_assoc,
      localPauliZ_anticomm_jwString_of_lt hjk, localPauliY_anticomm_jwString_of_lt hjk]
  rw [mul_add, mul_smul_comm, smul_neg, ← neg_add]

/-- The local fermion part `(Z_j + s·Y_j)/2` anticommutes with `jwString k` for
`j < k`. -/
theorem localPart_anticomm_jwString_of_lt {N : ℕ} {j k : Fin N} (hjk : j < k) (s : ℂ) :
    ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j)) * jwString k =
      -(jwString k * ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j))) := by
  rw [smul_mul_assoc, localPart_bare_anticomm_jwString_of_lt hjk, mul_smul_comm, smul_neg]

/-- Two single-site local fermion parts at distinct sites commute. -/
theorem localPart_commute_of_ne {N : ℕ} {j k : Fin N} (hjk : j ≠ k) (s t : ℂ) :
    Commute ((1/2 : ℂ) • (localPauliZ j + s • localPauliY j))
      ((1/2 : ℂ) • (localPauliZ k + t • localPauliY k)) := by
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left
  · apply Commute.add_right
    · exact localPauliZ_commute_localPauliZ hjk
    · exact Commute.smul_right (localPauliZ_commute_localPauliY hjk) t
  · apply Commute.smul_left
    apply Commute.add_right
    · exact localPauliY_commute_localPauliZ hjk
    · exact Commute.smul_right (localPauliY_commute_localPauliY hjk) t

/-- `jwString j` commutes with the local fermion part `(Z_k + t·Y_k)/2` when
`j ≤ k` (the string sits at sites `< j ≤ k`). -/
theorem jwString_commute_localPart_of_le {N : ℕ} {j k : Fin N} (hjk : j ≤ k) (t : ℂ) :
    Commute (jwString j) ((1/2 : ℂ) • (localPauliZ k + t • localPauliY k)) := by
  apply Commute.smul_right
  apply Commute.add_right
  · exact jwString_commute_localPauliZ_of_le hjk
  · exact (jwString_commute_localPauliY_of_le hjk).smul_right t

/-- Two Jordan–Wigner strings commute (both are products of commuting `X`s). -/
theorem jwString_commute_jwString {N : ℕ} (j k : Fin N) :
    Commute (jwString j) (jwString k) := by
  apply jwString_commute_of_forall
  intro m _
  exact jwString_commute_localPauliX j m

-- ----------------------------------------------------------------------------
-- Subsection: Cross-site fermion anticommutation (j < k)
-- ----------------------------------------------------------------------------

/-- For `j < k`, the annihilation/creation product anticommutes:
`c_j c_k† = - c_k† c_j`. The single `X_j` factor in `string_k` supplies the JW
sign; all other factors pass through (commute). -/
theorem cAnnih_mul_cCreate_anti_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    cAnnih j * cCreate k = - (cCreate k * cAnnih j) := by
  unfold cAnnih cCreate
  set Lm := (1/2 : ℂ) • (localPauliZ j - Complex.I • localPauliY j) with hLm
  set Lp := (1/2 : ℂ) • (localPauliZ k + Complex.I • localPauliY k) with hLp
  -- LHS = string_j * Lm * (Lp * string_k)
  -- Step 1: Lm and Lp commute (sites j ≠ k).
  have hLmLp : Commute Lm Lp := by
    rw [hLm, hLp, sub_eq_add_neg, ← neg_smul]
    exact localPart_commute_of_ne (ne_of_lt hjk) (-Complex.I) Complex.I
  -- Step 2: Lm anticommutes with string_k (j < k).
  have hLmStr : Lm * jwString k = -(jwString k * Lm) := by
    rw [hLm, sub_eq_add_neg, ← neg_smul]
    exact localPart_anticomm_jwString_of_lt hjk (-Complex.I)
  -- Step 3: string_j commutes with Lp (j ≤ k).
  have hStrLp : Commute (jwString j) Lp := by
    rw [hLp]; exact jwString_commute_localPart_of_le (le_of_lt hjk) Complex.I
  calc jwString j * Lm * (Lp * jwString k)
      = jwString j * (Lm * Lp) * jwString k := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = jwString j * (Lp * Lm) * jwString k := by rw [hLmLp.eq]
    _ = jwString j * Lp * (Lm * jwString k) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = jwString j * Lp * (-(jwString k * Lm)) := by rw [hLmStr]
    _ = -(jwString j * Lp * (jwString k * Lm)) := by rw [mul_neg]
    _ = - (Lp * jwString j * (jwString k * Lm)) := by rw [hStrLp.eq]
    _ = - (Lp * (jwString j * jwString k) * Lm) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = - (Lp * (jwString k * jwString j) * Lm) := by
          rw [(jwString_commute_jwString j k).eq]
    _ = - (Lp * jwString k * (jwString j * Lm)) := by
          rw [mul_assoc, mul_assoc, mul_assoc]

/-- A generic cross-site anticommutation for two "string·local" operators at
sites `j < k`, given the two local parts commute and the left local part
anticommutes with the right string. -/
private theorem stringLocal_anti_lt {N : ℕ} {j k : Fin N} (_hjk : j < k)
    (La Lb : NQubitOp N)
    (hLab : Commute La Lb)
    (hLaStr : La * jwString k = -(jwString k * La))
    (hStrLb : Commute (jwString j) Lb) :
    (jwString j * La) * (jwString k * Lb) =
      - ((jwString k * Lb) * (jwString j * La)) := by
  calc (jwString j * La) * (jwString k * Lb)
      = jwString j * (La * jwString k) * Lb := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = jwString j * (-(jwString k * La)) * Lb := by rw [hLaStr]
    _ = -(jwString j * (jwString k * La) * Lb) := by
          rw [mul_neg, neg_mul]
    _ = - ((jwString j * jwString k) * (La * Lb)) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = - ((jwString k * jwString j) * (Lb * La)) := by
          rw [(jwString_commute_jwString j k).eq, hLab.eq]
    _ = -(jwString k * (jwString j * Lb) * La) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = -(jwString k * (Lb * jwString j) * La) := by rw [hStrLb.eq]
    _ = - ((jwString k * Lb) * (jwString j * La)) := by
          rw [mul_assoc, mul_assoc, mul_assoc]

/-- For `j < k`, `c_j c_k = - c_k c_j`. -/
theorem cAnnih_mul_cAnnih_anti_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    cAnnih j * cAnnih k = - (cAnnih k * cAnnih j) := by
  unfold cAnnih
  apply stringLocal_anti_lt hjk
  · rw [sub_eq_add_neg, ← neg_smul, sub_eq_add_neg, ← neg_smul]
    exact localPart_commute_of_ne (ne_of_lt hjk) (-Complex.I) (-Complex.I)
  · rw [sub_eq_add_neg, ← neg_smul]
    exact localPart_anticomm_jwString_of_lt hjk (-Complex.I)
  · rw [sub_eq_add_neg, ← neg_smul]
    exact jwString_commute_localPart_of_le (le_of_lt hjk) (-Complex.I)

/-- A generic cross-site anticommutation for two "local·string" operators at
sites `j < k`. -/
private theorem localString_anti_lt {N : ℕ} {j k : Fin N} (_hjk : j < k)
    (La Lb : NQubitOp N)
    (hLab : Commute La Lb)
    (hStrLaLeft : Commute (jwString j) Lb)
    (hLaStrk : La * jwString k = -(jwString k * La)) :
    (La * jwString j) * (Lb * jwString k) =
      - ((Lb * jwString k) * (La * jwString j)) := by
  calc (La * jwString j) * (Lb * jwString k)
      = La * (jwString j * Lb) * jwString k := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = La * (Lb * jwString j) * jwString k := by rw [hStrLaLeft.eq]
    _ = (La * Lb) * (jwString j * jwString k) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = (Lb * La) * (jwString k * jwString j) := by
          rw [hLab.eq, (jwString_commute_jwString j k).eq]
    _ = Lb * (La * jwString k) * jwString j := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = Lb * (-(jwString k * La)) * jwString j := by rw [hLaStrk]
    _ = - (Lb * jwString k * (La * jwString j)) := by
          rw [mul_neg, neg_mul, mul_assoc, mul_assoc, mul_assoc]

/-- For `j < k`, `c_j† c_k† = - c_k† c_j†`. -/
theorem cCreate_mul_cCreate_anti_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    cCreate j * cCreate k = - (cCreate k * cCreate j) := by
  unfold cCreate
  apply localString_anti_lt hjk
  · exact localPart_commute_of_ne (ne_of_lt hjk) Complex.I Complex.I
  · exact jwString_commute_localPart_of_le (le_of_lt hjk) Complex.I
  · exact localPart_anticomm_jwString_of_lt hjk Complex.I

/-- For `j < k`, `c_j† c_k = - c_k c_j†`. -/
theorem cCreate_mul_cAnnih_anti_lt {N : ℕ} {j k : Fin N} (hjk : j < k) :
    cCreate j * cAnnih k = - (cAnnih k * cCreate j) := by
  unfold cCreate cAnnih
  set Lp := (1/2 : ℂ) • (localPauliZ j + Complex.I • localPauliY j) with hLp
  set Lm := (1/2 : ℂ) • (localPauliZ k - Complex.I • localPauliY k) with hLm
  have hLpLm : Commute Lp Lm := by
    rw [hLp, hLm, sub_eq_add_neg, ← neg_smul]
    exact localPart_commute_of_ne (ne_of_lt hjk) Complex.I (-Complex.I)
  have hStrLm : Commute (jwString j) Lm := by
    rw [hLm, sub_eq_add_neg, ← neg_smul]
    exact jwString_commute_localPart_of_le (le_of_lt hjk) (-Complex.I)
  have hLpStr : Lp * jwString k = -(jwString k * Lp) := by
    rw [hLp]; exact localPart_anticomm_jwString_of_lt hjk Complex.I
  calc Lp * jwString j * (jwString k * Lm)
      = Lp * (jwString j * jwString k) * Lm := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = Lp * (jwString k * jwString j) * Lm := by
          rw [(jwString_commute_jwString j k).eq]
    _ = Lp * jwString k * (jwString j * Lm) := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = Lp * jwString k * (Lm * jwString j) := by rw [hStrLm.eq]
    _ = (Lp * jwString k) * Lm * jwString j := by
          rw [mul_assoc, mul_assoc, mul_assoc]
    _ = (-(jwString k * Lp)) * Lm * jwString j := by rw [hLpStr]
    _ = -(jwString k * (Lp * Lm) * jwString j) := by
          rw [neg_mul, neg_mul]; simp only [mul_assoc]
    _ = -(jwString k * (Lm * Lp) * jwString j) := by rw [hLpLm.eq]
    _ = -(jwString k * Lm * (Lp * jwString j)) := by
          rw [mul_assoc, mul_assoc, mul_assoc]

-- ----------------------------------------------------------------------------
-- Subsection: The CAR triple (all pairs)
-- ----------------------------------------------------------------------------

/-- CAR: `{c_j, c_k†} = δ_{jk} · 1` for all pairs `(j, k)`. -/
theorem car_annih_create {N : ℕ} (j k : Fin N) :
    cAnnih j * cCreate k + cCreate k * cAnnih j =
      (if j = k then (1 : NQubitOp N) else 0) := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · rw [if_neg (ne_of_lt hlt), cAnnih_mul_cCreate_anti_lt hlt, neg_add_cancel]
  · subst heq
    rw [if_pos rfl, cAnnih_mul_cCreate_same]
    have hnum : cCreate j * cAnnih j = numberOp j := rfl
    rw [hnum, numberOp_eq, ← smul_add]
    rw [show (1 + localPauliX j) + (1 - localPauliX j) = (2 : ℂ) • 1 by
      rw [two_smul]; abel]
    rw [smul_smul]; norm_num
  · rw [if_neg (ne_of_gt hgt), cCreate_mul_cAnnih_anti_lt hgt, add_neg_cancel]

/-- CAR: `{c_j, c_k} = 0` for all pairs `(j, k)`. -/
theorem car_annih_annih {N : ℕ} (j k : Fin N) :
    cAnnih j * cAnnih k + cAnnih k * cAnnih j = 0 := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · rw [cAnnih_mul_cAnnih_anti_lt hlt, neg_add_cancel]
  · subst heq
    rw [cAnnih_mul_cAnnih_same, add_zero]
  · rw [cAnnih_mul_cAnnih_anti_lt hgt, add_neg_cancel]

/-- CAR: `{c_j†, c_k†} = 0` for all pairs `(j, k)`. -/
theorem car_create_create {N : ℕ} (j k : Fin N) :
    cCreate j * cCreate k + cCreate k * cCreate j = 0 := by
  rcases lt_trichotomy j k with hlt | heq | hgt
  · rw [cCreate_mul_cCreate_anti_lt hlt, neg_add_cancel]
  · subst heq
    rw [cCreate_mul_cCreate_same, add_zero]
  · rw [cCreate_mul_cCreate_anti_lt hgt, add_neg_cancel]

end

end QAOA.IsingChain.JordanWigner
