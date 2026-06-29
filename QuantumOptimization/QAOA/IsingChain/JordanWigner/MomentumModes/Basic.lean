import QuantumOptimization.QAOA.IsingChain.JordanWigner.Transformation.Operators
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Transformation.HamiltonianImage
import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain

/-!
# Momentum Modes (Basic) — wave vectors, momentum-space fermions, pseudospin operators, CAR algebra

Foundational layer of the momentum-mode Fourier transform on the reduced ABC
chain `Qubits.NQubitOp (2*P+2)`. Defines the active wave-vector set, the momentum-space
Jordan–Wigner fermions, the per-mode pseudospin Pauli operators and per-mode Hamiltonians,
and develops the full canonical-anticommutation (CAR) and number-operator commutation
algebra used downstream (active subspace, Fourier collection, decomposition identities).
Realizes arXiv:1911.12259v2 SM l.770–856.

## Main definitions
- `waveVectorABC`, `WaveVectorABC`, `K_ABC`: the active wave vectors `k_n = 2(n+1)π/(2P+2)`.
- `cAnnihK`, `cCreateK`, `numberOpK`, `pairParity`: momentum-space fermions and number/pair-parity.
- `tauZ`/`tauPlus`/`tauMinus`/`tauX`/`tauY`, `HredXMode`, `HredZMode`: pseudospin Pauli operators
  and the per-mode pseudospin Hamiltonians.

## Main statements
- `K_ABC_card`: `(K_ABC P).card = P`.
- `sum_exp_orthogonality_same` / `sum_exp_orthogonality_diff`: discrete Fourier orthogonality.
- `car_annihK_createK_*`, `numberOpK_idem`, `pairParity_involution`: the CAR / idempotent algebra.
- `numberOpK_commute_*`, `pairParity_commute_pairParity_cross`, `numberOpK_*_commute_pairParity`:
  the cross-mode and self-conjugate-mode commutation lemmas.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 0: The wave-vector set K_ABC
-- ============================================================================

/-- The `n`-th active wave vector `k_n = 2·(n.val+1)·π / (2P+2)`. The `+1` shift
absorbs the source's off-by-one (`n = 1..N_R/2−1` ↦ Lean index `n = 0..P−1`).
`k = 0` and `k = π` are excluded by construction. -/
def waveVectorABC (P : ℕ) (n : Fin P) : ℝ :=
  2 * ((n.val : ℝ) + 1) * Real.pi / (2 * P + 2)

/-- The abstract type of active modes (a type synonym for `Fin P`); the index of a
single `(k,−k)` pair. The real angle is recovered by `waveVectorABC`. -/
def WaveVectorABC (P : ℕ) : Type := Fin P

instance (P : ℕ) : Fintype (WaveVectorABC P) := inferInstanceAs (Fintype (Fin P))

instance (P : ℕ) : DecidableEq (WaveVectorABC P) := inferInstanceAs (DecidableEq (Fin P))

/-- The index set of active modes, a `Finset (WaveVectorABC P)` of card exactly `P`. -/
def K_ABC (P : ℕ) : Finset (WaveVectorABC P) := Finset.univ

/-- The cardinality of the active mode set is exactly `P`. -/
theorem K_ABC_card (P : ℕ) : (K_ABC P).card = P := by
  rw [K_ABC, Finset.card_univ]
  exact Fintype.card_fin P

-- ============================================================================
-- Section 1: Momentum-space fermions and discrete orthogonality
-- ============================================================================

/-- The momentum-space annihilation operator, the inverse Fourier transform of the
position-space fermions: `c_k = (e^{iπ/4}/√N_R) Σ_j e^{ikj} c_j` (source l.787,
inverted). `N_R = 2P+2`. -/
def cAnnihK (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) •
    ∑ j : Fin (2*P+2),
      Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j

/-- The momentum-space creation operator `c_k† = (c_k)†`. -/
def cCreateK (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (cAnnihK P k)†

/-- The momentum-mode number operator `n_k = c_k† c_k`. -/
def numberOpK (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  cCreateK P k * cAnnihK P k

/-- The pair-parity operator `P_k = (1 − 2 n_k)(1 − 2 n_{−k}) = e^{iπ(n_k+n_{−k})}`
(source l.831–834). -/
def pairParity (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (1 - (2 : ℂ) • numberOpK P k) * (1 - (2 : ℂ) • numberOpK P (-k))

/-- Discrete orthogonality on the `N_R`-point grid: `Σ_j e^{i(k−k')j} = N_R` when
`(k − k')·N_R` is an integer multiple of `2π` (equivalently `e^{i(k−k')N_R} = 1`
and `e^{i(k−k')} = 1`), and `0` otherwise (`e^{i(k−k')} ≠ 1`). Stated as the two
cases needed downstream.

Same wave-vector case: if `e^{i(k−k')} = 1` then the sum is `N_R`. -/
theorem sum_exp_orthogonality_same (P : ℕ) (k k' : ℝ)
    (h : Complex.exp (Complex.I * ((k - k'))) = 1) :
    (∑ j : Fin (2*P+2), Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))) =
      ((2*P+2 : ℕ) : ℂ) := by
  have hterm : ∀ j : Fin (2*P+2),
      Complex.exp (Complex.I * ((k - k') * (j.val : ℝ))) = 1 := by
    intro j
    have : Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))
        = (Complex.exp (Complex.I * ((k - k')))) ^ (j.val) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [this, h, one_pow]
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  simp

/-- Distinct wave-vector case: if `e^{i(k−k')} ≠ 1` but `e^{i(k−k')N_R} = 1` then
the geometric sum vanishes. -/
theorem sum_exp_orthogonality_diff (P : ℕ) (k k' : ℝ)
    (hne : Complex.exp (Complex.I * ((k - k'))) ≠ 1)
    (hroot : (Complex.exp (Complex.I * ((k - k')))) ^ (2 * P + 2) = 1) :
    (∑ j : Fin (2*P+2), Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))) = 0 := by
  set ω := Complex.exp (Complex.I * ((k - k'))) with hω
  have hterm : ∀ j : Fin (2*P+2),
      Complex.exp (Complex.I * ((k - k') * (j.val : ℝ))) = ω ^ (j.val) := by
    intro j
    rw [hω, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j)]
  -- Σ_{j : Fin n} ω^j is a geometric sum over Fin n
  rw [Fin.sum_univ_eq_sum_range (fun j => ω ^ j)]
  have hgeom := geom_sum_eq hne (2*P+2)
  rw [hgeom, hroot]
  simp

-- ============================================================================
-- Section 2: Pseudospin Pauli operators and per-mode Hamiltonians
-- ============================================================================

/-- The pseudospin `τ^z_k = I − n_k − n_{−k}` on the `(k,−k)` pair: `+1` on the
empty pair `|↑_k⟩`, `−1` on the full pair `|↓_k⟩` (source l.836–841). -/
def tauZ (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  1 - numberOpK P k - numberOpK P (-k)

/-- The pseudospin raising operator `τ^+_k = c_{−k} c_k` (maps full pair → empty
pair, raising `τ^z`). -/
def tauPlus (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  cAnnihK P (-k) * cAnnihK P k

/-- The pseudospin lowering operator `τ^−_k = c_k† c_{−k}† = (τ^+_k)†`. -/
def tauMinus (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  cCreateK P k * cCreateK P (-k)

/-- The pseudospin `τ^x_k = τ^+_k + τ^−_k`. -/
def tauX (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  tauPlus P k + tauMinus P k

/-- The pseudospin `τ^y_k = −i(τ^+_k − τ^−_k)`. Third member of the pseudospin
Pauli triple `(τ^x, τ^y, τ^z)`; consumed by B3's SO(3) rotation calculus through
the cross-product term `i(û×v̂)·τ⃗` in `(û·τ)(v̂·τ) = (û·v̂) + i(û×v̂)·τ`. -/
def tauY (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (-Complex.I) • (tauPlus P k - tauMinus P k)

/-- The per-mode mixer Hamiltonian `Hred_x^(k) = −2 τ^z_k = −2 ẑ·τ⃗_k`
(PSEUDOSPIN form — source l.852). -/
def HredXMode (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (-2 : ℂ) • tauZ P k

/-- The per-mode cost Hamiltonian
`Hred_z^(k) = 2 sin k·τ^x_k − 2 cos k·τ^z_k = −2 b̂_k·τ⃗_k`, with
`b̂_k = (−sin k, 0, cos k)` (PSEUDOSPIN form — source l.853–856). -/
def HredZMode (P : ℕ) (k : ℝ) : NQubitOp (2*P+2) :=
  (2 * Real.sin k : ℂ) • tauX P k - (2 * Real.cos k : ℂ) • tauZ P k

-- ============================================================================
-- Section 4: Momentum-space CAR (foundation for the active-subspace algebra)
-- ============================================================================

/-- Expansion of the momentum creation operator into a sum of position creation
operators: `c_k† = (e^{-iπ/4}/√N_R) Σ_j e^{-ikj} c_j†`. -/
theorem cCreateK_eq (P : ℕ) (k : ℝ) :
    cCreateK P k =
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) •
        ∑ j : Fin (2*P+2),
          Complex.exp (-(Complex.I * (k * (j.val : ℝ)))) • cCreate j := by
  unfold cCreateK cAnnihK
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sum]
  -- conjugate scalar exponentials helper
  have hexp : ∀ z : ℝ, star (Complex.exp (Complex.I * (z : ℂ))) =
      Complex.exp (-(Complex.I * (z : ℂ))) := by
    intro z
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  congr 1
  · -- the scalar prefactor's conjugate
    rw [Complex.star_def, map_div₀, Complex.conj_ofReal]
    congr 1
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  · -- the summand conjugates
    apply Finset.sum_congr rfl
    intro j _
    rw [Matrix.conjTranspose_smul, ← cCreate_eq_adjoint]
    congr 1
    have := hexp (k * (j.val : ℝ))
    rw [Complex.ofReal_mul] at this
    convert this using 3

/-- Bare double-sum anticommutator: the Fourier-weighted position-fermion sums
anticommute to the diagonal orthogonality sum, using position CAR
(`car_annih_create`). -/
theorem car_annihK_createK_double (P : ℕ) (k k' : ℝ) :
    (∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j) *
        (∑ j : Fin (2*P+2), Complex.exp (-(Complex.I * (k' * (j.val : ℝ)))) • cCreate j) +
      (∑ j : Fin (2*P+2), Complex.exp (-(Complex.I * (k' * (j.val : ℝ)))) • cCreate j) *
        (∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j) =
      (∑ j : Fin (2*P+2),
        Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))) • (1 : NQubitOp (2*P+2)) := by
  -- expand both products into double sums
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
  -- swap order of the SECOND double sum so its outer index ranges over cAnnih (j),
  -- matching the first sum's outer index
  rw [Finset.sum_comm (γ := Fin (2*P+2)) (s := Finset.univ) (t := Finset.univ)
      (f := fun i j => (Complex.exp (-(Complex.I * (k' * (i.val : ℝ)))) • cCreate i) *
        (Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j))]
  -- combine the two double sums termwise (both now: outer over cAnnih index, inner over cCreate)
  rw [← Finset.sum_add_distrib]
  -- rewrite RHS as a sum over the outer index (only the diagonal survives)
  rw [show (∑ j : Fin (2*P+2),
        Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))) • (1 : NQubitOp (2*P+2)) =
      ∑ i : Fin (2*P+2),
        Complex.exp (Complex.I * ((k - k') * (i.val : ℝ))) • (1 : NQubitOp (2*P+2)) by
    rw [Finset.sum_smul]]
  apply Finset.sum_congr rfl
  intro i _
  -- inner: Σ_j [ e^{iki} c_i · e^{-ik'j} c_j† + e^{-ik'j} c_j† · e^{iki} c_i ]
  --        = e^{i(k-k')i} • 1
  rw [← Finset.sum_add_distrib]
  rw [show Complex.exp (Complex.I * ((k - k') * (i.val : ℝ))) • (1 : NQubitOp (2*P+2)) =
      ∑ j : Fin (2*P+2), (if i = j then
        Complex.exp (Complex.I * ((k - k') * (i.val : ℝ))) • (1 : NQubitOp (2*P+2)) else 0) by
    rw [Finset.sum_ite_eq Finset.univ i
      (fun _ => Complex.exp (Complex.I * ((k - k') * (i.val : ℝ))) • (1 : NQubitOp (2*P+2)))]
    simp]
  apply Finset.sum_congr rfl
  intro j _
  -- per-(i,j): e^{iki}e^{-ik'j} (c_i c_j† + c_j† c_i) = δ_{ij} e^{i(k-k')i} • 1
  rw [smul_mul_smul_comm, smul_mul_smul_comm,
      mul_comm (Complex.exp (-(Complex.I * (k' * (j.val : ℝ)))))
        (Complex.exp (Complex.I * (k * (i.val : ℝ)))),
      ← smul_add, car_annih_create]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [if_neg hij, if_neg hij, smul_zero]

/-- The Fourier prefactor product collapses to `1/N_R`:
`(e^{iπ/4}/√N_R)(e^{-iπ/4}/√N_R) = 1/N_R`. -/
theorem fourier_prefactor_mul (P : ℕ) :
    (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) *
      (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ)) =
      (1 : ℂ) / ((2*P+2 : ℕ) : ℂ) := by
  rw [div_mul_div_comm, ← Complex.exp_add]
  rw [add_neg_cancel, Complex.exp_zero]
  congr 1
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
  push_cast
  ring

/-- The anticommutator `c_k c_{k'}† + c_{k'}† c_k` expands, via position-space CAR,
to a single scalar times the Fourier orthogonality sum `Σ_j e^{i(k−k')j}`. -/
theorem car_annihK_createK_sum (P : ℕ) (k k' : ℝ) :
    cAnnihK P k * cCreateK P k' + cCreateK P k' * cAnnihK P k =
      ((Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)) *
        (Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ))) •
        ((∑ j : Fin (2*P+2),
          Complex.exp (Complex.I * ((k - k') * (j.val : ℝ)))) • (1 : NQubitOp (2*P+2))) := by
  unfold cAnnihK
  rw [cCreateK_eq]
  set a := Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ) with ha
  set b := Complex.exp (-(Complex.I * (Real.pi / 4))) / (Real.sqrt (2*P+2) : ℂ) with hb
  set SA := ∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j with hSA
  set SC := ∑ j : Fin (2*P+2), Complex.exp (-(Complex.I * (k' * (j.val : ℝ)))) • cCreate j with hSC
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  rw [smul_smul, smul_smul, mul_comm b a, ← smul_add]
  rw [car_annihK_createK_double]

/-- Same-mode CAR: `{c_k, c_k†} = c_k c_k† + c_k† c_k = 1`. -/
theorem car_annihK_createK_same (P : ℕ) (k : ℝ) :
    cAnnihK P k * cCreateK P k + cCreateK P k * cAnnihK P k = (1 : NQubitOp (2*P+2)) := by
  rw [car_annihK_createK_sum, fourier_prefactor_mul]
  have hsum : (∑ j : Fin (2*P+2),
      Complex.exp (Complex.I * ((k - k) * (j.val : ℝ)))) = ((2*P+2 : ℕ) : ℂ) := by
    apply sum_exp_orthogonality_same
    rw [sub_self]
    simp
  rw [hsum, smul_smul]
  rw [one_div, inv_mul_cancel₀ (by exact_mod_cast (by omega : (2*P+2 : ℕ) ≠ 0)), one_smul]

/-- Momentum-space anticommutator `{c_k, c_{k'}} = 0` (inherited from position CAR
`car_annih_annih`). -/
theorem car_annihK_annihK (P : ℕ) (k k' : ℝ) :
    cAnnihK P k * cAnnihK P k' + cAnnihK P k' * cAnnihK P k = 0 := by
  unfold cAnnihK
  rw [smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm, smul_smul, smul_smul,
      mul_comm (Complex.exp (Complex.I * (Real.pi / 4)) / (Real.sqrt (2*P+2) : ℂ)),
      ← smul_add]
  have hzero : ((∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j) *
        ∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k' * (j.val : ℝ))) • cAnnih j) +
      ((∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k' * (j.val : ℝ))) • cAnnih j) *
        ∑ j : Fin (2*P+2), Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j) = 0 := by
    rw [Finset.sum_mul_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm (γ := Fin (2*P+2)) (s := Finset.univ) (t := Finset.univ)
        (f := fun i j => (Complex.exp (Complex.I * (k' * (i.val : ℝ))) • cAnnih i) *
          (Complex.exp (Complex.I * (k * (j.val : ℝ))) • cAnnih j))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro j _
    rw [smul_mul_smul_comm, smul_mul_smul_comm,
        mul_comm (Complex.exp (Complex.I * (k' * (j.val : ℝ))))
          (Complex.exp (Complex.I * (k * (i.val : ℝ)))),
        ← smul_add, car_annih_annih, smul_zero]
  rw [hzero, smul_zero]

/-- Same-mode nilpotency: `c_k c_k = 0`. -/
theorem cAnnihK_mul_self (P : ℕ) (k : ℝ) : cAnnihK P k * cAnnihK P k = 0 := by
  have h := car_annihK_annihK P k k
  rw [← two_smul ℂ (cAnnihK P k * cAnnihK P k)] at h
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  exact (smul_eq_zero.mp h).resolve_left h2

/-- Same-mode nilpotency: `c_k† c_k† = 0`. -/
theorem cCreateK_mul_self (P : ℕ) (k : ℝ) : cCreateK P k * cCreateK P k = 0 := by
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, cAnnihK_mul_self, Matrix.conjTranspose_zero]

/-- Algebraic kernel: if `a*a = 0`, `c*c = 0`, and `a*c + c*a = 1` in a ring, then
`(c*a)` is idempotent. (Abstracts the momentum-mode CAR away from the heavy
`cAnnihK`/`cCreateK` terms to avoid `whnf` blowups.) -/
theorem car_factor_idem {R : Type*} [Ring R] {a c : R}
    (hself : a * a = 0) (hself' : c * c = 0) (hcar : a * c + c * a = 1) :
    (c * a) * (c * a) = c * a := by
  have hac : a * c = 1 - c * a := by rw [eq_sub_iff_add_eq]; exact hcar
  calc c * a * (c * a)
      = c * (a * c) * a := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = c * (1 - c * a) * a := by rw [hac]
    _ = c * a - (c * c) * (a * a) := by
        rw [mul_sub, mul_one, sub_mul]; congr 1; rw [mul_assoc, mul_assoc, mul_assoc]
    _ = c * a := by rw [hself, hself', zero_mul, sub_zero]

/-- The momentum number operator is idempotent: `n_k² = n_k`. -/
theorem numberOpK_idem (P : ℕ) (k : ℝ) :
    numberOpK P k * numberOpK P k = numberOpK P k :=
  car_factor_idem (cAnnihK_mul_self P k) (cCreateK_mul_self P k)
    (car_annihK_createK_same P k)

-- ============================================================================
-- Section 5: Self-conjugate-mode algebra (n_0, n_π) and idempotent helpers
-- ============================================================================

/-- The leftmost factor of `Π_A` annihilates `n_0`: `n_0 · (1 − n_0) = 0` (since
`n_0` is idempotent). -/
theorem numberOpK_mul_one_sub_self (P : ℕ) (k : ℝ) :
    numberOpK P k * (1 - numberOpK P k) = 0 := by
  rw [mul_sub, mul_one, numberOpK_idem, sub_self]

/-- Cross-mode CAR `{c_k, c_{k'}†} = 0` when `k ≢ k' (mod 2π)` but `(k−k')·N_R`
is a `2π`-multiple (`e^{i(k−k')} ≠ 1`, `(e^{i(k−k')})^{N_R} = 1`). -/
theorem car_annihK_createK_zero (P : ℕ) (k k' : ℝ)
    (hne : Complex.exp (Complex.I * ((k - k'))) ≠ 1)
    (hroot : (Complex.exp (Complex.I * ((k - k')))) ^ (2 * P + 2) = 1) :
    cAnnihK P k * cCreateK P k' + cCreateK P k' * cAnnihK P k = 0 := by
  rw [car_annihK_createK_sum, sum_exp_orthogonality_diff P k k' hne hroot]
  rw [zero_smul, smul_zero]

/-- `e^{i(0−π)} = e^{−iπ} = −1`. -/
theorem exp_I_zero_sub_pi :
    Complex.exp (Complex.I * (((0 : ℝ) : ℂ) - ((Real.pi : ℝ) : ℂ))) = -1 := by
  rw [Complex.ofReal_zero, zero_sub, mul_neg]
  rw [show (Complex.I * (Real.pi : ℂ)) = (Real.pi : ℂ) * Complex.I by ring]
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

/-- `{c_0, c_π†} = 0`. -/
theorem car_c0_cpiCreate (P : ℕ) :
    cAnnihK P 0 * cCreateK P Real.pi + cCreateK P Real.pi * cAnnihK P 0 = 0 := by
  have hexp := exp_I_zero_sub_pi
  apply car_annihK_createK_zero
  · rw [hexp]; norm_num
  · rw [hexp]
    rw [show (-1 : ℂ) ^ (2 * P + 2) = ((-1 : ℂ) ^ 2) ^ (P + 1) by rw [← pow_mul]; ring_nf]
    norm_num

/-- `{c_π, c_0†} = 0`. -/
theorem car_cpi_c0Create (P : ℕ) :
    cAnnihK P Real.pi * cCreateK P 0 + cCreateK P 0 * cAnnihK P Real.pi = 0 := by
  have hexp := exp_I_zero_sub_pi
  apply car_annihK_createK_zero
  · rw [show ((Real.pi : ℝ) : ℂ) - ((0 : ℝ) : ℂ) = -(((0 : ℝ):ℂ) - ((Real.pi:ℝ):ℂ)) by ring,
        mul_neg, Complex.exp_neg, hexp]
    norm_num
  · rw [show ((Real.pi : ℝ) : ℂ) - ((0 : ℝ) : ℂ) = -(((0 : ℝ):ℂ) - ((Real.pi:ℝ):ℂ)) by ring,
        mul_neg, Complex.exp_neg, hexp]
    rw [show ((-1 : ℂ)⁻¹) = (-1 : ℂ) by norm_num]
    rw [show (-1 : ℂ) ^ (2 * P + 2) = ((-1 : ℂ) ^ 2) ^ (P + 1) by rw [← pow_mul]; ring_nf]
    norm_num

/-- `{c_0†, c_π†} = 0` (adjoint of `{c_0, c_π} = 0`). -/
theorem car_c0Create_cpiCreate (P : ℕ) :
    cCreateK P 0 * cCreateK P Real.pi + cCreateK P Real.pi * cCreateK P 0 = 0 := by
  unfold cCreateK
  rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_add,
      add_comm (cAnnihK P Real.pi * cAnnihK P 0), car_annihK_annihK, Matrix.conjTranspose_zero]

/-- Ring kernel: two number operators built from anticommuting fermion pairs
commute. Given annihilators `a, a'` and creators `d, d'` (`d = a†`, `d' = a'†`)
with `a*a = 0`, `d*d = 0`, and all four cross-anticommutators vanishing, the
number operators `d*a` and `d'*a'` commute. -/
theorem number_commute_of_car {R : Type*} [Ring R] {a a' d d' : R}
    (had' : a * d' + d' * a = 0) (hda' : d * a' + a' * d = 0)
    (hdd' : d * d' + d' * d = 0) (haa' : a * a' + a' * a = 0) :
    (d * a) * (d' * a') = (d' * a') * (d * a) := by
  have had'' : a * d' = -(d' * a) := by rw [eq_neg_iff_add_eq_zero]; exact had'
  have hda'' : d * a' = -(a' * d) := by rw [eq_neg_iff_add_eq_zero]; exact hda'
  have hdd'' : d * d' = -(d' * d) := by rw [eq_neg_iff_add_eq_zero]; exact hdd'
  have haa'' : a * a' = -(a' * a) := by rw [eq_neg_iff_add_eq_zero]; exact haa'
  -- d a d' a' = -d d' a a' = d' d a a' = -d' d a' a = d' a' d a
  calc d * a * (d' * a')
      = d * (a * d') * a' := by rw [mul_assoc, mul_assoc, mul_assoc]
    _ = d * (-(d' * a)) * a' := by rw [had'']
    _ = -(d * d' * (a * a')) := by rw [mul_neg, neg_mul]; simp only [mul_assoc]
    _ = -((-(d' * d)) * (a * a')) := by rw [hdd'']
    _ = d' * d * (a * a') := by rw [neg_mul, neg_neg]
    _ = d' * d * (-(a' * a)) := by rw [haa'']
    _ = -(d' * (d * a') * a) := by rw [mul_neg]; simp only [mul_assoc]
    _ = -(d' * (-(a' * d)) * a) := by rw [hda'']
    _ = d' * a' * (d * a) := by
        rw [mul_neg, neg_mul, neg_neg]; simp only [mul_assoc]

/-- `n_0` and `n_π` commute. -/
theorem numberOpK_zero_commute_npi (P : ℕ) :
    Commute (numberOpK P 0) (numberOpK P Real.pi) := by
  unfold numberOpK Commute SemiconjBy
  exact number_commute_of_car
    (by have := car_c0_cpiCreate P; linear_combination (norm := abel) this)
    (by have := car_cpi_c0Create P; linear_combination (norm := abel) this)
    (by have := car_c0Create_cpiCreate P; linear_combination (norm := abel) this)
    (by have := car_annihK_annihK P 0 Real.pi; linear_combination (norm := abel) this)

-- ============================================================================
-- Section 6: Within-pair root-of-unity facts and pair-parity involution
-- ============================================================================

/-- `e^{i·2 k_n·N_R} = 1` for an active wave vector `k_n`: the within-pair phase
`(k_n − (−k_n)) = 2 k_n` is a root of unity of order dividing `N_R = 2P+2`,
since `2 k_n·N_R = 4(n+1)π`. -/
theorem exp_within_pair_root (P : ℕ) (n : Fin P) :
    (Complex.exp (Complex.I *
        ((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ))) ^ (2 * P + 2) = 1 := by
  rw [← Complex.exp_nat_mul]
  -- exponent = (2P+2) * (I * (2 k_n)) = I * (4(n+1)π) = (2(n+1)) * (2π I)
  rw [show ((2 * P + 2 : ℕ) : ℂ) * (Complex.I *
        (((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ) : ℂ))
      = ((2 * (n.val + 1) : ℕ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    unfold waveVectorABC
    have hPne : ((2 * (P : ℝ) + 2) : ℂ) ≠ 0 := by
      have : (2 * (P : ℝ) + 2) ≠ 0 := by positivity
      exact_mod_cast this
    push_cast
    field_simp
    ring]
  rw [Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

/-- `e^{i·2 k_n} ≠ 1` for an active wave vector `k_n`: the pair `(k_n, −k_n)` is a
genuine two-mode pair (`k_n ≠ −k_n` mod 2π), since `2 k_n = 2(n+1)π/(P+1)` is not
a multiple of `2π` for `0 ≤ n < P`. -/
theorem exp_within_pair_ne_one (P : ℕ) (n : Fin P) :
    Complex.exp (Complex.I *
        ((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ)) ≠ 1 := by
  intro hcontra
  rw [Complex.exp_eq_one_iff] at hcontra
  obtain ⟨m, hm⟩ := hcontra
  -- I * (2 k_n) = m * (2π I)  ⟹  2 k_n = 2π m  (cancel I), a real equation
  have hmI : (((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ) : ℂ)
      = (m : ℂ) * (2 * Real.pi) := by
    have h2 : Complex.I * (((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ) : ℂ)
        = Complex.I * ((m : ℂ) * (2 * Real.pi)) := by
      rw [hm]; ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hmR : ((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ)) = (m : ℝ) * (2 * Real.pi) := by
    exact_mod_cast hmI
  unfold waveVectorABC at hmR
  have hPpos : (0 : ℝ) < 2 * (P : ℝ) + 2 := by positivity
  -- 4(n+1)π/(2P+2) = 2πm ⟹ (n+1) = m(P+1)
  have hfrac : ((n.val : ℝ) + 1) = (m : ℝ) * ((P : ℝ) + 1) := by
    have hpi2 : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    have hPne : (2 * (P : ℝ) + 2) ≠ 0 := ne_of_gt hPpos
    have hexpand : 2 * (2 * ((n.val:ℝ) + 1) * Real.pi / (2 * P + 2))
        = (m : ℝ) * (2 * Real.pi) := by
      have := hmR; ring_nf at this ⊢; linarith [this]
    field_simp at hexpand
    nlinarith [hexpand, Real.pi_pos]
  -- 0 < n+1 ≤ P < P+1, so (n+1)/(P+1) ∈ (0,1), cannot equal integer m
  have hn1 : (0 : ℝ) < (n.val : ℝ) + 1 := by positivity
  have hnP : (n.val : ℝ) + 1 ≤ (P : ℝ) := by
    have := n.isLt; exact_mod_cast (by omega : n.val + 1 ≤ P)
  have hP1 : (P : ℝ) < (P : ℝ) + 1 := by linarith
  have hP1pos : (0 : ℝ) < (P : ℝ) + 1 := by positivity
  -- m must be a positive integer with m(P+1) = n+1 < P+1 ⟹ m < 1 and m > 0
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    by_contra h
    push_neg at h
    nlinarith [hfrac, hn1, hP1pos]
  have hmlt : (m : ℝ) < 1 := by
    nlinarith [hfrac, hnP, hP1, hP1pos]
  -- m integer with 0 < m < 1: impossible
  have : (1 : ℝ) ≤ (m : ℝ) := by
    have hm1 : (1 : ℤ) ≤ m := by
      by_contra hc; push_neg at hc
      have : m ≤ 0 := by omega
      have : (m : ℝ) ≤ 0 := by exact_mod_cast this
      linarith
    exact_mod_cast hm1
  linarith

/-- `e^{i(−k_n − k_n)} ≠ 1` (the reverse within-pair difference). -/
theorem exp_within_pair_neg_ne_one (P : ℕ) (n : Fin P) :
    Complex.exp (Complex.I *
        ((-(waveVectorABC P n) : ℝ) - (waveVectorABC P n) : ℝ)) ≠ 1 := by
  have h := exp_within_pair_ne_one P n
  intro hc
  apply h
  rw [show (((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ)) : ℝ)
      = -(((-(waveVectorABC P n) : ℝ) - (waveVectorABC P n)) : ℝ) by ring]
  rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg, hc, inv_one]

/-- `(e^{i(−k_n − k_n)})^{N_R} = 1`. -/
theorem exp_within_pair_neg_root (P : ℕ) (n : Fin P) :
    (Complex.exp (Complex.I *
        ((-(waveVectorABC P n) : ℝ) - (waveVectorABC P n) : ℝ))) ^ (2 * P + 2) = 1 := by
  have h := exp_within_pair_root P n
  rw [show (((-(waveVectorABC P n) : ℝ) - (waveVectorABC P n)) : ℝ)
      = -(((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ)) : ℝ) by ring]
  rw [Complex.ofReal_neg, mul_neg, Complex.exp_neg, inv_pow, h, inv_one]

/-- Within an active pair the two number operators commute: `[n_{k_n}, n_{−k_n}] = 0`. -/
theorem numberOpK_within_pair_commute (P : ℕ) (n : Fin P) :
    Commute (numberOpK P (waveVectorABC P n)) (numberOpK P (-(waveVectorABC P n))) := by
  unfold numberOpK Commute SemiconjBy
  have hcast1 : ((waveVectorABC P n : ℝ) : ℂ) - ((-(waveVectorABC P n) : ℝ) : ℂ)
      = (((waveVectorABC P n : ℝ) - (-(waveVectorABC P n) : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
  have hcast2 : ((-(waveVectorABC P n) : ℝ) : ℂ) - ((waveVectorABC P n : ℝ) : ℂ)
      = (((-(waveVectorABC P n) : ℝ) - (waveVectorABC P n) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
  refine number_commute_of_car ?_ ?_ ?_ ?_
  · -- {c_{k_n}, c_{-k_n}†} = 0
    have := car_annihK_createK_zero P (waveVectorABC P n) (-(waveVectorABC P n))
      (by rw [hcast1]; exact exp_within_pair_ne_one P n)
      (by rw [hcast1]; exact exp_within_pair_root P n)
    linear_combination (norm := abel) this
  · -- {c_{k_n}†, c_{-k_n}} = 0   (from {c_{-k_n}, c_{k_n}†} = 0)
    have := car_annihK_createK_zero P (-(waveVectorABC P n)) (waveVectorABC P n)
      (by rw [hcast2]; exact exp_within_pair_neg_ne_one P n)
      (by rw [hcast2]; exact exp_within_pair_neg_root P n)
    linear_combination (norm := abel) this
  · -- {c_{k_n}†, c_{-k_n}†} = 0   (adjoint of {c_{k_n}, c_{-k_n}} = 0)
    have : cCreateK P (waveVectorABC P n) * cCreateK P (-(waveVectorABC P n))
        + cCreateK P (-(waveVectorABC P n)) * cCreateK P (waveVectorABC P n) = 0 := by
      unfold cCreateK
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul,
          ← Matrix.conjTranspose_add,
          add_comm (cAnnihK P (-(waveVectorABC P n)) * cAnnihK P (waveVectorABC P n)),
          car_annihK_annihK, Matrix.conjTranspose_zero]
    linear_combination (norm := abel) this
  · -- {c_{k_n}, c_{-k_n}} = 0
    have := car_annihK_annihK P (waveVectorABC P n) (-(waveVectorABC P n))
    linear_combination (norm := abel) this

/-- Ring kernel: if `p` and `q` are commuting idempotents in a `ℂ`-algebra, then
`((1−2p)(1−2q))² = 1` (each `(1−2p)` is an involution). -/
theorem pairParity_factor_involution {A : Type*} [Ring A] [Algebra ℂ A] {p q : A}
    (hp : p * p = p) (hq : q * q = q) (hpq : Commute p q) :
    ((1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • q)) * ((1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • q)) = 1 := by
  have hinv : ∀ r : A, r * r = r → (1 - (2 : ℂ) • r) * (1 - (2 : ℂ) • r) = 1 := by
    intro r hr
    have hexp : (1 - (2 : ℂ) • r) * (1 - (2 : ℂ) • r)
        = 1 - (4 : ℂ) • r + (4 : ℂ) • (r * r) := by
      simp only [mul_sub, sub_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm]
      module
    rw [hexp, hr]
    abel
  have hp2 := hinv p hp
  have hq2 := hinv q hq
  have hcomm : Commute (1 - (2 : ℂ) • q) (1 - (2 : ℂ) • p) := by
    apply Commute.sub_left (Commute.one_left _)
    apply Commute.sub_right (Commute.one_right _)
    exact (hpq.symm.smul_left 2).smul_right 2
  calc (1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • q) * ((1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • q))
      = (1 - (2 : ℂ) • p) * ((1 - (2 : ℂ) • q) * (1 - (2 : ℂ) • p)) * (1 - (2 : ℂ) • q) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = (1 - (2 : ℂ) • p) * ((1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • q)) * (1 - (2 : ℂ) • q) := by
        rw [hcomm.eq]
    _ = ((1 - (2 : ℂ) • p) * (1 - (2 : ℂ) • p)) * ((1 - (2 : ℂ) • q) * (1 - (2 : ℂ) • q)) := by
        rw [mul_assoc, mul_assoc, mul_assoc]
    _ = 1 := by rw [hp2, hq2, one_mul]

/-- The pair-parity operator at an active wave vector is an involution:
`P_{k_n}² = 1`. -/
theorem pairParity_involution (P : ℕ) (n : Fin P) :
    pairParity P (waveVectorABC P n) * pairParity P (waveVectorABC P n) = 1 := by
  unfold pairParity
  exact pairParity_factor_involution (numberOpK_idem P (waveVectorABC P n))
    (numberOpK_idem P (-(waveVectorABC P n))) (numberOpK_within_pair_commute P n)

-- ============================================================================
-- Section 7: General cross-mode root-of-unity facts (for cross-pair CARs)
-- ============================================================================

/-- General root-of-unity fact: for integer coefficients `a, b`, the combination
`a·k_n + b·k_m` of active wave vectors is a root of unity of order dividing
`N_R = 2P+2`: `(e^{i(a k_n + b k_m)})^{N_R} = 1` because
`(a k_n + b k_m)·N_R = 2π(a(n+1) + b(m+1))`. -/
theorem exp_combo_root (P : ℕ) (n m : Fin P) (a b : ℤ) :
    (Complex.exp (Complex.I *
        ((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m : ℝ))) ^ (2 * P + 2) = 1 := by
  rw [← Complex.exp_nat_mul]
  rw [show ((2 * P + 2 : ℕ) : ℂ) * (Complex.I *
        ((((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m) : ℝ) : ℂ))
      = ((a * (n.val + 1) + b * (m.val + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    unfold waveVectorABC
    have hPne : ((2 * (P : ℝ) + 2) : ℂ) ≠ 0 := by
      have : (2 * (P : ℝ) + 2) ≠ 0 := by positivity
      exact_mod_cast this
    push_cast
    field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- General distinctness: `e^{i(a k_n + b k_m)} ≠ 1` when `N_R ∤ (a(n+1) + b(m+1))`
(the combination is not a `2π`-multiple). -/
theorem exp_combo_ne_one (P : ℕ) (n m : Fin P) (a b : ℤ)
    (hdvd : ¬ ((2 * P + 2 : ℤ) ∣ (a * (n.val + 1) + b * (m.val + 1)))) :
    Complex.exp (Complex.I *
        ((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m : ℝ)) ≠ 1 := by
  intro hcontra
  rw [Complex.exp_eq_one_iff] at hcontra
  obtain ⟨j, hj⟩ := hcontra
  apply hdvd
  -- I*(a k_n + b k_m) = j*(2π I) ⟹ a k_n + b k_m = 2π j ⟹ S = j*N_R
  have hI : (((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m : ℝ) : ℂ)
      = (j : ℂ) * (2 * Real.pi) := by
    have h2 : Complex.I * (((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m : ℝ) : ℂ)
        = Complex.I * ((j : ℂ) * (2 * Real.pi)) := by rw [hj]; ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hR : ((a : ℝ) * waveVectorABC P n + (b : ℝ) * waveVectorABC P m)
      = (j : ℝ) * (2 * Real.pi) := by exact_mod_cast hI
  unfold waveVectorABC at hR
  have hPpos : (0 : ℝ) < 2 * (P : ℝ) + 2 := by positivity
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  -- (a(n+1) + b(m+1)) = j * (2P+2)
  have hS : (a : ℝ) * ((n.val : ℝ) + 1) + (b : ℝ) * ((m.val : ℝ) + 1)
      = (j : ℝ) * (2 * (P : ℝ) + 2) := by
    have hclear : (a : ℝ) * (2 * ((n.val:ℝ) + 1) * Real.pi / (2 * P + 2))
        + (b : ℝ) * (2 * ((m.val:ℝ) + 1) * Real.pi / (2 * P + 2))
        = (j : ℝ) * (2 * Real.pi) := hR
    field_simp at hclear
    nlinarith [hclear, Real.pi_pos]
  -- conclude integer divisibility
  refine ⟨j, ?_⟩
  have : (a * ((n.val : ℤ) + 1) + b * ((m.val : ℤ) + 1) : ℤ) = (j * (2 * (P : ℤ) + 2) : ℤ) := by
    have hScast : ((a * ((n.val : ℤ) + 1) + b * ((m.val : ℤ) + 1) : ℤ) : ℝ)
        = ((j * (2 * (P : ℤ) + 2) : ℤ) : ℝ) := by push_cast; push_cast at hS; linarith [hS]
    exact_mod_cast hScast
  push_cast at this ⊢
  linarith [this]

/-- Cross-mode CAR `{c_k, c_{k'}†} = 0` for modes whose difference (cast both ways)
is a non-trivial root of unity. Convenience wrapper aligning the cast forms. -/
theorem car_annihK_createK_zero' (P : ℕ) (k k' : ℝ)
    (hne : Complex.exp (Complex.I * ((k : ℝ) - (k' : ℝ) : ℝ)) ≠ 1)
    (hroot : (Complex.exp (Complex.I * ((k : ℝ) - (k' : ℝ) : ℝ))) ^ (2 * P + 2) = 1) :
    cAnnihK P k * cCreateK P k' + cCreateK P k' * cAnnihK P k = 0 := by
  apply car_annihK_createK_zero
  · rw [show ((k : ℝ) : ℂ) - ((k' : ℝ) : ℂ) = (((k : ℝ) - (k' : ℝ) : ℝ) : ℂ) by
      rw [Complex.ofReal_sub]]
    exact hne
  · rw [show ((k : ℝ) : ℂ) - ((k' : ℝ) : ℂ) = (((k : ℝ) - (k' : ℝ) : ℝ) : ℂ) by
      rw [Complex.ofReal_sub]]
    exact hroot

/-- Two number operators at modes `k, k'` commute, provided all four cross
anticommutators vanish (encoded via the two difference roots-of-unity). -/
theorem numberOpK_commute_of_diff (P : ℕ) (k k' : ℝ)
    (hne1 : Complex.exp (Complex.I * ((k : ℝ) - (k' : ℝ) : ℝ)) ≠ 1)
    (hroot1 : (Complex.exp (Complex.I * ((k : ℝ) - (k' : ℝ) : ℝ))) ^ (2 * P + 2) = 1)
    (hne2 : Complex.exp (Complex.I * ((k' : ℝ) - (k : ℝ) : ℝ)) ≠ 1)
    (hroot2 : (Complex.exp (Complex.I * ((k' : ℝ) - (k : ℝ) : ℝ))) ^ (2 * P + 2) = 1) :
    Commute (numberOpK P k) (numberOpK P k') := by
  unfold numberOpK Commute SemiconjBy
  refine number_commute_of_car ?_ ?_ ?_ ?_
  · have := car_annihK_createK_zero' P k k' hne1 hroot1
    linear_combination (norm := abel) this
  · have := car_annihK_createK_zero' P k' k hne2 hroot2
    linear_combination (norm := abel) this
  · have : cCreateK P k * cCreateK P k' + cCreateK P k' * cCreateK P k = 0 := by
      unfold cCreateK
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_add,
          add_comm (cAnnihK P k' * cAnnihK P k), car_annihK_annihK, Matrix.conjTranspose_zero]
    linear_combination (norm := abel) this
  · have := car_annihK_annihK P k k'
    linear_combination (norm := abel) this

-- ============================================================================
-- Section 8: Cross-pair number / pair-parity commutation
-- ============================================================================

/-- Signed cross-mode number commute: `n_{σ k_n}` and `n_{τ k_m}` commute when the
two integer combinations `σ(n+1) − τ(m+1)` and `τ(m+1) − σ(n+1)` are both NOT
divisible by `N_R = 2P+2` (so neither difference is a `2π`-multiple). The signs
`σ, τ ∈ {±1}` are passed as the integer coefficients. -/
theorem numberOpK_commute_signed (P : ℕ) (n m : Fin P) (σ τ : ℤ)
    (hdvd1 : ¬ ((2 * P + 2 : ℤ) ∣ (σ * (n.val + 1) - τ * (m.val + 1))))
    (hdvd2 : ¬ ((2 * P + 2 : ℤ) ∣ (τ * (m.val + 1) - σ * (n.val + 1)))) :
    Commute (numberOpK P ((σ : ℝ) * waveVectorABC P n))
      (numberOpK P ((τ : ℝ) * waveVectorABC P m)) := by
  -- bridge each difference into the `exp_combo_*` form with coefficients (σ, −τ) / (τ, −σ)
  have hcast1 : (((σ : ℝ) * waveVectorABC P n - (τ : ℝ) * waveVectorABC P m : ℝ) : ℂ)
      = ((((σ : ℤ) : ℝ) * waveVectorABC P n + (((-τ : ℤ)) : ℝ) * waveVectorABC P m : ℝ) : ℂ) := by
    push_cast; ring
  have hcast2 : (((τ : ℝ) * waveVectorABC P m - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
      = ((((τ : ℤ) : ℝ) * waveVectorABC P m + (((-σ : ℤ)) : ℝ) * waveVectorABC P n : ℝ) : ℂ) := by
    push_cast; ring
  apply numberOpK_commute_of_diff
  · rw [hcast1]
    apply exp_combo_ne_one P n m σ (-τ)
    intro hc; apply hdvd1
    have : σ * (n.val + 1) + (-τ) * (m.val + 1) = σ * (n.val + 1) - τ * (m.val + 1) := by ring
    rwa [this] at hc
  · rw [hcast1]; exact exp_combo_root P n m σ (-τ)
  · rw [hcast2]
    apply exp_combo_ne_one P m n τ (-σ)
    intro hc; apply hdvd2
    have : τ * (m.val + 1) + (-σ) * (n.val + 1) = τ * (m.val + 1) - σ * (n.val + 1) := by ring
    rwa [this] at hc
  · rw [hcast2]; exact exp_combo_root P m n τ (-σ)

/-- For distinct active pairs `n ≠ m` and any signs `σ, τ ∈ {−1, +1}`, the combo
`σ(n+1) − τ(m+1)` is not divisible by `N_R = 2P+2`: its absolute value lies in
`[1, 2P]`, strictly between `0` and `N_R`. -/
theorem combo_not_dvd_of_ne (P : ℕ) (n m : Fin P) (hnm : n ≠ m) {σ τ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    ¬ ((2 * P + 2 : ℤ) ∣ (σ * (n.val + 1) - τ * (m.val + 1))) := by
  have hnlt : (n.val : ℤ) < P := by exact_mod_cast n.isLt
  have hmlt : (m.val : ℤ) < P := by exact_mod_cast m.isLt
  have hnpos : (0 : ℤ) ≤ n.val := Int.natCast_nonneg n.val
  have hmpos : (0 : ℤ) ≤ m.val := Int.natCast_nonneg m.val
  have hnmval : (n.val : ℤ) ≠ (m.val : ℤ) := by
    intro h; apply hnm; exact Fin.ext (by exact_mod_cast h)
  -- |σ(n+1) − τ(m+1)| ∈ [1, 2P], strictly inside (0, N_R). `omega` cannot handle a
  -- non-literal divisor `2P+2`, so extract the witness `c`, case on its sign, and use
  -- that `|(2P+2)·c| ≥ 2P+2 > 2P` for `c ≠ 0`.
  have hNR : (0 : ℤ) < 2 * P + 2 := by positivity
  rcases hσ with hσ | hσ <;> rcases hτ with hτ | hτ <;> subst hσ <;> subst hτ <;>
    (intro hdvd; obtain ⟨c, hc⟩ := hdvd;
     rcases lt_trichotomy c 0 with hcneg | hcz | hcpos
     · have hcle : c ≤ -1 := by omega
       nlinarith [hc, hNR, hcle, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ -1 - c)]
     · subst hcz; simp at hc; omega
     · have hcge : 1 ≤ c := by omega
       nlinarith [hc, hNR, hcge, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ c - 1)])

/-- Lifting a number-operator commute to the `(1 − 2 n)` factors: if `a` and `b`
commute then so do `1 − 2•a` and `1 − 2•b`. -/
theorem commute_one_sub_two_smul {P : ℕ} {a b : NQubitOp (2 * P + 2)} (h : Commute a b) :
    Commute (1 - (2 : ℂ) • a) (1 - (2 : ℂ) • b) := by
  apply Commute.sub_left
  · exact Commute.one_left _
  · apply Commute.sub_right
    · exact Commute.one_right _
    · exact (h.smul_left 2).smul_right 2

/-- The four signed cross-pair number commutes for distinct active pairs `n ≠ m`. -/
theorem numberOpK_commute_cross (P : ℕ) (n m : Fin P) (hnm : n ≠ m)
    {σ τ : ℤ} (hσ : σ = 1 ∨ σ = -1) (hτ : τ = 1 ∨ τ = -1) :
    Commute (numberOpK P ((σ : ℝ) * waveVectorABC P n))
      (numberOpK P ((τ : ℝ) * waveVectorABC P m)) :=
  numberOpK_commute_signed P n m σ τ
    (combo_not_dvd_of_ne P n m hnm hσ hτ)
    (combo_not_dvd_of_ne P m n hnm.symm hτ hσ)

/-- Helper: number ops at signed wave vectors, where the sign is absorbed as an
integer coefficient, equal the bare signed wave vectors. -/
theorem numberOpK_one_coe (P : ℕ) (n : Fin P) :
    numberOpK P (((1 : ℤ) : ℝ) * waveVectorABC P n) = numberOpK P (waveVectorABC P n) := by
  norm_num

theorem numberOpK_negone_coe (P : ℕ) (n : Fin P) :
    numberOpK P (((-1 : ℤ) : ℝ) * waveVectorABC P n) = numberOpK P (-(waveVectorABC P n)) := by
  congr 1; push_cast; ring

/-- `numberOpK P (k_n)` commutes with each of the two factors `(1 − 2 n_{±k_m})` of
`pairParity P (k_m)`, hence with the product. -/
theorem numberOpK_commute_pairParity_cross (P : ℕ) (n m : Fin P) (hnm : n ≠ m) :
    Commute (numberOpK P (waveVectorABC P n)) (pairParity P (waveVectorABC P m)) := by
  have c1 : Commute (numberOpK P (waveVectorABC P n)) (numberOpK P (waveVectorABC P m)) := by
    have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inl rfl)
    rwa [numberOpK_one_coe, numberOpK_one_coe] at this
  have c2 : Commute (numberOpK P (waveVectorABC P n)) (numberOpK P (-(waveVectorABC P m))) := by
    have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inr rfl)
    rwa [numberOpK_one_coe, numberOpK_negone_coe] at this
  unfold pairParity
  exact Commute.mul_right
    (Commute.sub_right (Commute.one_right _) (c1.smul_right 2))
    (Commute.sub_right (Commute.one_right _) (c2.smul_right 2))

/-- `pairParity P (k_n)` commutes with `pairParity P (k_m)` for distinct active pairs
`n ≠ m`. -/
theorem pairParity_commute_pairParity_cross (P : ℕ) (n m : Fin P) (hnm : n ≠ m) :
    Commute (pairParity P (waveVectorABC P n)) (pairParity P (waveVectorABC P m)) := by
  have c11 : Commute (numberOpK P (waveVectorABC P n)) (numberOpK P (waveVectorABC P m)) := by
    have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inl rfl)
    rwa [numberOpK_one_coe, numberOpK_one_coe] at this
  have c1m1 : Commute (numberOpK P (waveVectorABC P n)) (numberOpK P (-(waveVectorABC P m))) := by
    have := numberOpK_commute_cross P n m hnm (Or.inl rfl) (Or.inr rfl)
    rwa [numberOpK_one_coe, numberOpK_negone_coe] at this
  have cm11 : Commute (numberOpK P (-(waveVectorABC P n))) (numberOpK P (waveVectorABC P m)) := by
    have := numberOpK_commute_cross P n m hnm (Or.inr rfl) (Or.inl rfl)
    rwa [numberOpK_negone_coe, numberOpK_one_coe] at this
  have cm1m1 : Commute (numberOpK P (-(waveVectorABC P n))) (numberOpK P (-(waveVectorABC P m))) := by
    have := numberOpK_commute_cross P n m hnm (Or.inr rfl) (Or.inr rfl)
    rwa [numberOpK_negone_coe, numberOpK_negone_coe] at this
  unfold pairParity
  -- (1−2n_{k_n})(1−2n_{−k_n}) commutes with (1−2n_{k_m})(1−2n_{−k_m})
  exact Commute.mul_left
    (Commute.mul_right (commute_one_sub_two_smul c11) (commute_one_sub_two_smul c1m1))
    (Commute.mul_right (commute_one_sub_two_smul cm11) (commute_one_sub_two_smul cm1m1))

-- ============================================================================
-- Section 9: Self-conjugate vs active-pair commutation
-- ============================================================================

/-- `e^{i(0 − σ k_n)} ≠ 1` for `σ = ±1`: the difference `−σ k_n` is a non-trivial
root of unity (`N_R ∤ (n+1)`). -/
theorem exp_zero_sub_signed_ne_one (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (Complex.I * (((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ))) ≠ 1 := by
  rw [show ((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ)
      = ((-σ : ℤ) : ℝ) * waveVectorABC P n + ((0 : ℤ) : ℝ) * waveVectorABC P n by push_cast; ring]
  apply exp_combo_ne_one P n n (-σ) 0
  intro hdvd
  obtain ⟨c, hc⟩ := hdvd
  have hnlt : (n.val : ℤ) < P := by exact_mod_cast n.isLt
  have hnpos : (0 : ℤ) ≤ n.val := Int.natCast_nonneg n.val
  have hNR : (0 : ℤ) < 2 * P + 2 := by positivity
  rcases hσ with hσ | hσ <;> subst hσ <;>
    (rcases lt_trichotomy c 0 with hcneg | hcz | hcpos
     · have : c ≤ -1 := by omega
       nlinarith [hc, hNR, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ -1 - c)]
     · subst hcz; simp at hc; omega
     · have : 1 ≤ c := by omega
       nlinarith [hc, hNR, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ c - 1)])

/-- `(e^{i(0 − σ k_n)})^{N_R} = 1` for `σ = ±1`. -/
theorem exp_zero_sub_signed_root (P : ℕ) (n : Fin P) (σ : ℤ) :
    (Complex.exp (Complex.I * (((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ)))) ^ (2 * P + 2) = 1 := by
  rw [show ((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ)
      = ((-σ : ℤ) : ℝ) * waveVectorABC P n + ((0 : ℤ) : ℝ) * waveVectorABC P n by push_cast; ring]
  exact exp_combo_root P n n (-σ) 0

/-- `e^{i(σ k_n − 0)} ≠ 1` for `σ = ±1`. -/
theorem exp_signed_sub_zero_ne_one (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (Complex.I * (((σ : ℝ) * waveVectorABC P n - (0 : ℝ) : ℝ))) ≠ 1 := by
  have h := exp_zero_sub_signed_ne_one P n hσ
  intro hc; apply h
  rw [show ((0 : ℝ) - (σ : ℝ) * waveVectorABC P n : ℝ)
      = -(((σ : ℝ) * waveVectorABC P n - (0 : ℝ)) : ℝ) by ring,
      Complex.ofReal_neg, mul_neg, Complex.exp_neg, hc, inv_one]

/-- `(e^{i(σ k_n − 0)})^{N_R} = 1` for `σ = ±1`. -/
theorem exp_signed_sub_zero_root (P : ℕ) (n : Fin P) (σ : ℤ) :
    (Complex.exp (Complex.I * (((σ : ℝ) * waveVectorABC P n - (0 : ℝ) : ℝ)))) ^ (2 * P + 2) = 1 := by
  have h := exp_zero_sub_signed_root P n σ
  rw [show (((σ : ℝ) * waveVectorABC P n - (0 : ℝ)) : ℝ)
      = -(((0 : ℝ) - (σ : ℝ) * waveVectorABC P n) : ℝ) by ring,
      Complex.ofReal_neg, mul_neg, Complex.exp_neg, inv_pow, h, inv_one]

/-- `numberOpK P 0` commutes with `numberOpK P (σ k_n)` for `σ = ±1` (the self-
conjugate `k=0` mode commutes with each active-pair mode). -/
theorem numberOpK_zero_commute_signed (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P 0) (numberOpK P ((σ : ℝ) * waveVectorABC P n)) := by
  apply numberOpK_commute_of_diff
  · exact exp_zero_sub_signed_ne_one P n hσ
  · exact exp_zero_sub_signed_root P n σ
  · exact exp_signed_sub_zero_ne_one P n hσ
  · exact exp_signed_sub_zero_root P n σ

/-- `numberOpK P 0` commutes with `pairParity P (k_n)`. -/
theorem numberOpK_zero_commute_pairParity (P : ℕ) (n : Fin P) :
    Commute (numberOpK P 0) (pairParity P (waveVectorABC P n)) := by
  have c1 : Commute (numberOpK P 0) (numberOpK P (waveVectorABC P n)) := by
    have := numberOpK_zero_commute_signed P n (Or.inl rfl); rwa [numberOpK_one_coe] at this
  have c2 : Commute (numberOpK P 0) (numberOpK P (-(waveVectorABC P n))) := by
    have := numberOpK_zero_commute_signed P n (Or.inr rfl); rwa [numberOpK_negone_coe] at this
  unfold pairParity
  exact Commute.mul_right
    (Commute.sub_right (Commute.one_right _) (c1.smul_right 2))
    (Commute.sub_right (Commute.one_right _) (c2.smul_right 2))

/-- `e^{i(π − σ k_n)} ≠ 1` for `σ = ±1`: `π − σ k_n` corresponds to `(P+1) − σ(n+1)`,
which is not a `2π`-multiple (`N_R ∤ (P+1) − σ(n+1)` since `1 ≤ |·| ≤ 2P`). -/
theorem exp_pi_sub_signed_ne_one (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (Complex.I * ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ))) ≠ 1 := by
  intro hcontra
  rw [Complex.exp_eq_one_iff] at hcontra
  obtain ⟨j, hj⟩ := hcontra
  have hI : ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ) = (j : ℂ) * (2 * Real.pi) := by
    have h2 : Complex.I * ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ) : ℂ)
        = Complex.I * ((j : ℂ) * (2 * Real.pi)) := by rw [hj]; ring
    exact mul_left_cancel₀ Complex.I_ne_zero h2
  have hR : (Real.pi - (σ : ℝ) * waveVectorABC P n) = (j : ℝ) * (2 * Real.pi) := by
    exact_mod_cast hI
  unfold waveVectorABC at hR
  have hPpos : (0 : ℝ) < 2 * (P : ℝ) + 2 := by positivity
  have hpi : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
  -- (P+1) − σ(n+1) = j·(2P+2)
  have hS : ((P : ℝ) + 1) - (σ : ℝ) * ((n.val : ℝ) + 1) = (j : ℝ) * (2 * (P : ℝ) + 2) := by
    have hclear : Real.pi - (σ : ℝ) * (2 * ((n.val:ℝ) + 1) * Real.pi / (2 * P + 2))
        = (j : ℝ) * (2 * Real.pi) := hR
    field_simp at hclear
    nlinarith [hclear, Real.pi_pos]
  -- conclude integer relation and bound j
  have hSint : ((P : ℤ) + 1) - σ * ((n.val : ℤ) + 1) = j * (2 * (P : ℤ) + 2) := by
    have : (((P : ℤ) + 1) - σ * ((n.val : ℤ) + 1) : ℤ) = ((j * (2 * (P : ℤ) + 2) : ℤ)) := by
      have hcast : (((P : ℤ) + 1) - σ * ((n.val : ℤ) + 1) : ℝ)
          = ((j * (2 * (P : ℤ) + 2) : ℤ) : ℝ) := by push_cast; push_cast at hS; linarith [hS]
      exact_mod_cast hcast
    exact this
  -- 1 ≤ |(P+1) − σ(n+1)| ≤ 2P  ⟹  j = 0  ⟹  contradiction
  have hnlt : (n.val : ℤ) < P := by exact_mod_cast n.isLt
  have hnpos : (0 : ℤ) ≤ n.val := Int.natCast_nonneg n.val
  have hPpos' : (0 : ℤ) ≤ P := Int.natCast_nonneg P
  have hNR : (0 : ℤ) < 2 * P + 2 := by positivity
  rcases hσ with hσ | hσ <;> subst hσ <;>
    (rcases lt_trichotomy j 0 with hjneg | hjz | hjpos
     · have : j ≤ -1 := by omega
       nlinarith [hSint, hNR, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ -1 - j)]
     · subst hjz; simp at hSint; omega
     · have : 1 ≤ j := by omega
       nlinarith [hSint, hNR, mul_nonneg (le_of_lt hNR) (by linarith : (0:ℤ) ≤ j - 1)])

/-- `(e^{i(π − σ k_n)})^{N_R} = 1` for `σ = ±1`: `e^{iπ N_R} = 1` since `N_R` is even,
and `(e^{-iσ k_n})^{N_R} = 1`. -/
theorem exp_pi_sub_signed_root (P : ℕ) (n : Fin P) (σ : ℤ) :
    (Complex.exp (Complex.I * ((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ)))) ^ (2 * P + 2) = 1 := by
  rw [← Complex.exp_nat_mul]
  -- (N_R)·(π − σk_n) = (P+1)·(2π) − σ(n+1)·(2π)·... we route through exp_int_mul_two_pi_mul_I
  rw [show ((2 * P + 2 : ℕ) : ℂ) * (Complex.I * (((Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ)) : ℂ))
      = (((P : ℤ) + 1 - σ * (n.val + 1) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by
    unfold waveVectorABC
    have hPne : ((2 * (P : ℝ) + 2) : ℂ) ≠ 0 := by
      have : (2 * (P : ℝ) + 2) ≠ 0 := by positivity
      exact_mod_cast this
    push_cast
    field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- `e^{i(σ k_n − π)} ≠ 1` for `σ = ±1`. -/
theorem exp_signed_sub_pi_ne_one (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Complex.exp (Complex.I * (((σ : ℝ) * waveVectorABC P n - Real.pi : ℝ))) ≠ 1 := by
  have h := exp_pi_sub_signed_ne_one P n hσ
  intro hc; apply h
  rw [show (Real.pi - (σ : ℝ) * waveVectorABC P n : ℝ)
      = -(((σ : ℝ) * waveVectorABC P n - Real.pi) : ℝ) by ring,
      Complex.ofReal_neg, mul_neg, Complex.exp_neg, hc, inv_one]

/-- `(e^{i(σ k_n − π)})^{N_R} = 1` for `σ = ±1`. -/
theorem exp_signed_sub_pi_root (P : ℕ) (n : Fin P) (σ : ℤ) :
    (Complex.exp (Complex.I * (((σ : ℝ) * waveVectorABC P n - Real.pi : ℝ)))) ^ (2 * P + 2) = 1 := by
  have h := exp_pi_sub_signed_root P n σ
  rw [show (((σ : ℝ) * waveVectorABC P n - Real.pi) : ℝ)
      = -((Real.pi - (σ : ℝ) * waveVectorABC P n) : ℝ) by ring,
      Complex.ofReal_neg, mul_neg, Complex.exp_neg, inv_pow, h, inv_one]

/-- `numberOpK P π` commutes with `numberOpK P (σ k_n)` for `σ = ±1`. -/
theorem numberOpK_pi_commute_signed (P : ℕ) (n : Fin P) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) :
    Commute (numberOpK P Real.pi) (numberOpK P ((σ : ℝ) * waveVectorABC P n)) := by
  apply numberOpK_commute_of_diff
  · exact exp_pi_sub_signed_ne_one P n hσ
  · exact exp_pi_sub_signed_root P n σ
  · exact exp_signed_sub_pi_ne_one P n hσ
  · exact exp_signed_sub_pi_root P n σ

/-- `numberOpK P π` commutes with `pairParity P (k_n)`. -/
theorem numberOpK_pi_commute_pairParity (P : ℕ) (n : Fin P) :
    Commute (numberOpK P Real.pi) (pairParity P (waveVectorABC P n)) := by
  have c1 : Commute (numberOpK P Real.pi) (numberOpK P (waveVectorABC P n)) := by
    have := numberOpK_pi_commute_signed P n (Or.inl rfl); rwa [numberOpK_one_coe] at this
  have c2 : Commute (numberOpK P Real.pi) (numberOpK P (-(waveVectorABC P n))) := by
    have := numberOpK_pi_commute_signed P n (Or.inr rfl); rwa [numberOpK_negone_coe] at this
  unfold pairParity
  exact Commute.mul_right
    (Commute.sub_right (Commute.one_right _) (c1.smul_right 2))
    (Commute.sub_right (Commute.one_right _) (c2.smul_right 2))

end

end QAOA.IsingChain.JordanWigner
