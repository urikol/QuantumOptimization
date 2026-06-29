import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.Basic
import QuantumOptimization.QAOA.StandardMixer

/-!
# Light-Cone Spreading — per-layer support growth under QAOA conjugation

This file extends the support calculus of `LightCone.Basic` to the per-layer
QAOA conjugation operation. Source: arXiv:1906.08948v2 §IV l.620–678.

The single-site mixer exponential `e^{-i β X_j}` admits the closed form
`localMixerFactor N β j = cos β · I + (-i sin β) · X_j`. Both summands are
supported on the singleton `{j}` (the identity is supported on the empty set,
and `X_j` on `{j}`), so the local mixer factor itself is supported on `{j}`.
Conjugation by it therefore only adds the site `{j}` to whatever support set
the conjugated operator already had: this is the elementary per-layer
spreading bound used throughout the FGG light-cone analysis (eq. (3.10) in the
source).

This file delivers:

* `supportedOn_localMixerFactor` — the explicit local mixer factor is supported
  on `{j}`.
* `supportedOn_exp_localPauliX` — the mixer-layer single-site exponential
  `exp(-i β X_j)` is supported on `{j}`.
* `supportedOn_conj` — the generic conjugation lemma `U * O * V ↾ S_U ∪ S ∪ S_V`.
* `supportedOn_conj_localPauliX_exp` — conjugation by `exp(-i β X_j)`
  preserves support up to the singleton site `{j}`. Special case of
  `supportedOn_conj` with `S_U = S_V = {j}`.
* `chainPairInteraction_sq` — the involutory identity `(Z_k Z_{k+1})² = 1`.
* `exp_chainPairInteraction_closed_form` — closed form
  `exp(-i γ · Z_k Z_{k+1}) = cos γ · I + (-i sin γ) · Z_k Z_{k+1}`.
* `supportedOn_exp_chainPairInteraction` — single-bond cost exponential
  is supported on `{k, nextSite k}`.
* `supportedOn_conj_chainPair_exp` — per-bond cost-layer conjugation
  spreading.
* `supportedOn_cost_layer_conj` — full-cost-layer conjugation spreading
  (loose form: `Finset.univ`).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Local mixer factor support
-- ============================================================================

/-!
The local mixer factor `localMixerFactor N β j = cos β · I + (-i sin β) · X_j`
is supported on `{j}` because both summands are: `I` is supported on `∅` (and
hence on any set by `supportedOn_mono`), and `X_j` on `{j}`.
-/

/-- The local mixer factor `cos β · I + (-i sin β) · X_j` is supported on the
singleton `{j}`.

This is the elementary support fact for the single-site mixer exponential,
since `exp(-i β X_j) = localMixerFactor N β j` (Mathlib
`QAOA.exp_localPauliX`).

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_localMixerFactor {N : ℕ} (β : ℝ) (j : Fin N) :
    supportedOn ({j} : Finset (Fin N)) (QAOA.localMixerFactor N β j) := by
  unfold QAOA.localMixerFactor
  -- The identity summand is supported on `∅ ⊆ {j}`.
  have h_one : supportedOn ({j} : Finset (Fin N))
      ((Real.cos β : ℂ) • (1 : Qubits.NQubitOp N)) :=
    supportedOn_mono (Finset.empty_subset _) (supportedOn_smul_one (Real.cos β : ℂ))
  -- The X_j summand is supported on `{j}`.
  have h_X : supportedOn ({j} : Finset (Fin N))
      ((((-Complex.I) * Real.sin β : ℂ)) • Qubits.localPauliX j) :=
    supportedOn_smul _ (supportedOn_localPauliX j)
  -- Their sum is supported on `{j} ∪ {j} = {j}`.
  have h_sum := supportedOn_add h_one h_X
  simpa using h_sum

/-- The single-site mixer exponential `exp(-i β X_j)` is supported on the
singleton `{j}`.

This is the operator identity `exp(-i β X_j) = cos β · I − i sin β · X_j`
(`QAOA.exp_localPauliX`) packaged through the closed-form support lemma above.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_exp_localPauliX {N : ℕ} (β : ℝ) (j : Fin N) :
    supportedOn ({j} : Finset (Fin N))
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j)) := by
  rw [QAOA.exp_localPauliX]
  exact supportedOn_localMixerFactor β j

-- ============================================================================
-- Section: Generic conjugation lemma
-- ============================================================================

/-!
The basic per-layer spreading bound is a direct application of
`supportedOn_mul`: a triple product `U * O * V` is supported on the union of
the three supports.
-/

/-- Triple product spreading: if `U` is supported on `S_U`, `O` on `S`, and
`V` on `S_V`, then `U * O * V` is supported on `S_U ∪ S ∪ S_V`.

This is the abstract conjugation spreading bound. For the QAOA application
the relevant special cases instantiate `V = U†` (so `S_U = S_V`), reducing the
result to `S_U ∪ S`.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_conj {N : ℕ} {S_U S S_V : Finset (Fin N)}
    {U O V : Qubits.NQubitOp N}
    (hU : supportedOn S_U U) (hO : supportedOn S O) (hV : supportedOn S_V V) :
    supportedOn (S_U ∪ S ∪ S_V) (U * O * V) :=
  supportedOn_mul (supportedOn_mul hU hO) hV

-- ============================================================================
-- Section: Conjugation by single-site Pauli-X exponentials
-- ============================================================================

/-!
The mixer layer's per-site exponential `e^{-i β X_j}` is unitary, with adjoint
equal to `e^{i β X_j}`. Rather than working with the adjoint directly, we
state the spreading lemma in the more general form `U * O * V` with both `U`
and `V` themselves single-site Pauli-X exponentials (possibly at different
angles or opposite signs). This subsumes the conjugation pattern
`e^{-iβX_j} O e^{iβX_j}` because both factors are still supported on `{j}`.
-/

/-- Conjugation by a single-site Pauli-X exponential preserves support up to
the singleton site `{j}`. More generally, the triple product
`exp(-iβ X_j) · O · exp(-iβ' X_j)` is supported on `S ∪ {j}` whenever `O` is
supported on `S`. Specializing `β' = -β` recovers the standard conjugation
`U O U†`.

This is the elementary per-layer mixer spreading bound: the cost layer is
absorbed elsewhere (cf. `exp_chainPairInteraction_sum` factorization), and the
mixer layer is a product of factors of this shape, so the P-layer recursion
adds at most one site per side per QAOA layer.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_conj_localPauliX_exp {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : supportedOn S O) (j : Fin N) (β β' : ℝ) :
    supportedOn (S ∪ ({j} : Finset (Fin N)))
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j) *
        O *
        NormedSpace.exp ((((-β' : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j)) := by
  have h_left := supportedOn_exp_localPauliX β j
  have h_right := supportedOn_exp_localPauliX β' j
  -- The triple product is supported on `{j} ∪ S ∪ {j} = S ∪ {j}`.
  have h := supportedOn_conj h_left hO h_right
  -- Re-associate `{j} ∪ S ∪ {j}` into `S ∪ {j}`.
  refine supportedOn_mono ?_ h
  intro k hk
  simp only [Finset.mem_union] at hk ⊢
  tauto

-- ============================================================================
-- Section: Product spreading via noncomm products
-- ============================================================================

/-!
This section lifts `supportedOn` through `Finset.noncommProd`. It is the
ingredient needed to combine the per-site mixer exponentials produced by
`exp_standardMixerOp` (whose RHS is a noncomm product over `Finset.univ`) and
the per-bond cost exponentials produced by `exp_chainPairInteraction_sum`.

Each factor's support is its own per-site singleton (mixer) or per-bond pair
(cost); the product's support is the union of all factor supports. The proof
is an induction on the noncomm product via `Finset.noncommProd_induction`.
-/

/-- If every factor `f i` in a `Finset.noncommProd` is supported on `g i`,
then the product is supported on the union `s.biUnion g`. This is the
inductive lift of `supportedOn_mul` to a non-commutative product.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_noncommProd {N : ℕ} {ι : Type*}
    (s : Finset ι) (f : ι → Qubits.NQubitOp N) (g : ι → Finset (Fin N))
    (comm : (s : Set ι).Pairwise (Function.onFun Commute f))
    (h : ∀ i ∈ s, supportedOn (g i) (f i)) :
    supportedOn (s.biUnion g) (s.noncommProd f comm) := by
  classical
  refine Finset.noncommProd_induction s f comm
    (p := fun M => supportedOn (s.biUnion g) M) ?_ ?_ ?_
  · intro a b ha hb
    -- `supportedOn` is closed under product (with union of supports);
    -- inside `s.biUnion g` the union is reflexive, so the result lands back
    -- in `s.biUnion g`.
    have := supportedOn_mul ha hb
    simpa using supportedOn_mono (by intro k hk; simpa using hk) this
  · -- The unit `1` is supported on `∅`, hence on `s.biUnion g` by mono.
    exact supportedOn_mono (Finset.empty_subset _) supportedOn_one
  · intro i hi
    refine supportedOn_mono ?_ (h i hi)
    intro k hk
    exact Finset.mem_biUnion.mpr ⟨i, hi, hk⟩

-- ============================================================================
-- Section: Mixer-layer support
-- ============================================================================

/-!
Combining `exp_standardMixerOp` (factorization into noncomm product of
single-site exponentials) and `supportedOn_noncommProd` (lift of singleton
supports through that product) gives the mixer-layer support: the unitary
`exp(-i β H_B)` is supported on the entire qubit register `Finset.univ`. This
is trivially true (every `N`-qubit operator is supported on `Finset.univ`) but
is recorded here as a structural fact about the layer's exponential form,
ready for combination with the cost-layer side.
-/

/-- The mixer-layer exponential `exp(-i β ∑_j X_j)` is supported on the full
qubit set `Finset.univ`. Trivially true entrywise, but the proof here goes
through the noncomm-product factorization to expose the building blocks.

Source: arXiv:1906.08948v2 §IV l.620–678. -/
theorem supportedOn_exp_standardMixerOp (N : ℕ) (β : ℝ) :
    supportedOn (Finset.univ : Finset (Fin N))
      (NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • QAOA.standardMixerOp N)) := by
  rw [QAOA.exp_standardMixerOp]
  change supportedOn (Finset.univ : Finset (Fin N))
    ((Finset.univ : Finset (Fin N)).noncommProd
      (fun j => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
      _)
  -- The biUnion of singletons over `Finset.univ` is `Finset.univ`.
  have hbu :
      (Finset.univ : Finset (Fin N)).biUnion (fun j => ({j} : Finset (Fin N))) =
        Finset.univ := by
    ext k; simp
  have h_supported :
      supportedOn
        ((Finset.univ : Finset (Fin N)).biUnion (fun j => ({j} : Finset (Fin N))))
        ((Finset.univ : Finset (Fin N)).noncommProd
          (fun j => NormedSpace.exp ((((-β : ℝ) * Complex.I : ℂ)) • Qubits.localPauliX j))
          (fun i _ j _ _ =>
            (Qubits.localPauliX_commute i j).smul_left _ |>.smul_right _ |>.exp)) := by
    refine supportedOn_noncommProd _ _ _ _ ?_
    intro j _
    exact supportedOn_exp_localPauliX β j
  rw [hbu] at h_supported
  exact h_supported

-- ============================================================================
-- Section: Chain-pair interaction is involutory
-- ============================================================================

/-!
The pair interaction `chainPairInteraction k = Z_k · Z_{nextSite k}` is
diagonal in the computational basis with eigenvalues ±1 (the product of two
classical spin values), so its square is the identity. The proof mirrors
`Qubits.localPauliX_sq`: equality on every computational basis ket suffices.
-/

/-- The pair interaction squares to the identity, since each computational
basis ket is an eigenvector with eigenvalue `±1`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem chainPairInteraction_sq {n : ℕ} (k : Fin n) :
    IsingModel.chainPairInteraction k * IsingModel.chainPairInteraction k =
      (1 : Qubits.NQubitOp n) := by
  refine Qubits.op_eq_of_on_computationalBasis ?_
  intro z
  set s : ℝ :=
    IsingModel.classicalSpin z k * IsingModel.classicalSpin z (IsingModel.nextSite k)
    with hs_def
  -- The eigenvalue product `s` is `±1`, so `s * s = 1`.
  have hs_sq : s * s = 1 := by
    -- `classicalSpin z i = spinValue (z i)` and `spinValue b ∈ {±1}`.
    have hk : IsingModel.classicalSpin z k = IsingModel.spinValue (z k) := rfl
    have hk' : IsingModel.classicalSpin z (IsingModel.nextSite k) =
        IsingModel.spinValue (z (IsingModel.nextSite k)) := rfl
    have hsv : ∀ b : Fin 2, IsingModel.spinValue b * IsingModel.spinValue b = 1 := by
      intro b
      fin_cases b <;> simp [IsingModel.spinValue]
    -- `s * s = (a * b) * (a * b) = (a*a) * (b*b) = 1 * 1 = 1`.
    have : s * s = (IsingModel.spinValue (z k) * IsingModel.spinValue (z k)) *
        (IsingModel.spinValue (z (IsingModel.nextSite k)) *
          IsingModel.spinValue (z (IsingModel.nextSite k))) := by
      simp [hs_def, hk, hk']; ring
    rw [this, hsv, hsv]; ring
  have hcpi : IsingModel.chainPairInteraction k * Qubits.computationalBasisKet n z =
      ((s : ℂ)) • Qubits.computationalBasisKet n z := by
    simpa [hs_def] using
      IsingModel.chainPairInteraction_apply_computationalBasisKet (k := k) (z := z)
  calc
    (IsingModel.chainPairInteraction k * IsingModel.chainPairInteraction k) *
          Qubits.computationalBasisKet n z
        = IsingModel.chainPairInteraction k *
            (IsingModel.chainPairInteraction k *
              Qubits.computationalBasisKet n z) := by
          rw [op_mul_op_mul_ket]
    _ = IsingModel.chainPairInteraction k *
            (((s : ℂ)) • Qubits.computationalBasisKet n z) := by
          rw [hcpi]
    _ = ((s : ℂ)) •
            (IsingModel.chainPairInteraction k *
              Qubits.computationalBasisKet n z) := by
          rw [op_mul_smul_ket]
    _ = ((s : ℂ)) • ((s : ℂ) • Qubits.computationalBasisKet n z) := by
          rw [hcpi]
    _ = (((s : ℂ)) * ((s : ℂ))) • Qubits.computationalBasisKet n z := by
          rw [Ket.smul_smul]
    _ = ((1 : ℂ)) • Qubits.computationalBasisKet n z := by
          rw [show (((s : ℂ)) * ((s : ℂ))) = ((s * s : ℝ) : ℂ) by push_cast; ring]
          rw [hs_sq]; simp
    _ = (1 : Qubits.NQubitOp n) * Qubits.computationalBasisKet n z := by
          symm
          ext i
          rw [op_mul_ket_vec]
          simp [Matrix.one_mulVec]

/-- Even powers of the pair interaction reduce to the identity. -/
theorem chainPairInteraction_pow_even {n : ℕ} (k : Fin n) (m : ℕ) :
    IsingModel.chainPairInteraction k ^ (2 * m) = (1 : Qubits.NQubitOp n) := by
  have hsq : IsingModel.chainPairInteraction k ^ 2 = (1 : Qubits.NQubitOp n) := by
    simpa [sq] using chainPairInteraction_sq (n := n) k
  rw [pow_mul, hsq]
  simp

/-- Odd powers of the pair interaction reduce to itself. -/
theorem chainPairInteraction_pow_odd {n : ℕ} (k : Fin n) (m : ℕ) :
    IsingModel.chainPairInteraction k ^ (2 * m + 1) =
      IsingModel.chainPairInteraction k := by
  rw [pow_add, chainPairInteraction_pow_even k m]
  simp

-- ============================================================================
-- Section: Closed form for the cost-bond exponential
-- ============================================================================

/-!
Since the pair interaction is an involution, its exponential has the same
closed form as `exp(-i β X_j)`: separate the Taylor series into even and odd
parts, identify the even subseries with `cos γ · I` and the odd subseries with
`(-i sin γ) · chainPairInteraction k`. The proof template is the one used in
`QAOA.exp_localPauliX` for the single-site Pauli-X case; here we apply it to
the chain-pair interaction.
-/

/-- Even part of the matrix-exponential series for `-iγ · chainPairInteraction k`
collapses to `cos γ · I` (the involution makes every even power the identity).
-/
private lemma chainPair_even_hasSum {n : ℕ} (γ : ℝ) (k : Fin n) :
    HasSum
      (fun m : ℕ =>
        (((2 * m).factorial : ℂ)⁻¹) •
          (((((-γ : ℝ) * Complex.I : ℂ)) •
              IsingModel.chainPairInteraction k) ^ (2 * m)))
      ((Real.cos γ : ℂ) • (1 : Qubits.NQubitOp n)) := by
  have h_even_term (m : ℕ) :
      (((2 * m).factorial : ℂ)⁻¹) •
          (((((-γ : ℝ) * Complex.I : ℂ)) •
              IsingModel.chainPairInteraction k) ^ (2 * m)) =
        ((((-1 : ℂ) ^ m) * ((γ : ℂ) ^ (2 * m)) / ((2 * m).factorial : ℂ)) : ℂ) •
          (1 : Qubits.NQubitOp n) := by
    rw [smul_pow, chainPairInteraction_pow_even, smul_smul]
    -- Scalar coefficient: same as in `localMixerScalar_pow_even`.
    have hc2 : ((((-γ : ℝ) * Complex.I : ℂ)) ^ 2) = -((γ : ℂ) ^ 2) := by
      ring_nf; simp
    have hpow : ((((-γ : ℝ) * Complex.I : ℂ)) ^ (2 * m)) =
        ((-1 : ℂ) ^ m) * ((γ : ℂ) ^ (2 * m)) := by
      rw [pow_mul, hc2]
      rw [show (-((γ : ℂ) ^ 2)) = (-1 : ℂ) * ((γ : ℂ) ^ 2) by ring]
      rw [mul_pow, ← pow_mul]
    rw [hpow]
    congr 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hcos :
      HasSum (fun m : ℕ => (-1 : ℂ) ^ m * (γ : ℂ) ^ (2 * m) / ((2 * m).factorial : ℂ))
        (Real.cos γ) := by
    simpa using (Complex.hasSum_cos (γ : ℂ))
  convert hcos.smul_const (1 : Qubits.NQubitOp n) using 1
  funext m
  exact h_even_term m

/-- Odd part of the matrix-exponential series for `-iγ · chainPairInteraction k`
collapses to `(-i sin γ) · chainPairInteraction k`.
-/
private lemma chainPair_odd_hasSum {n : ℕ} (γ : ℝ) (k : Fin n) :
    HasSum
      (fun m : ℕ =>
        (((2 * m + 1).factorial : ℂ)⁻¹) •
          (((((-γ : ℝ) * Complex.I : ℂ)) •
              IsingModel.chainPairInteraction k) ^ (2 * m + 1)))
      ((((-Complex.I) * Real.sin γ : ℂ)) • IsingModel.chainPairInteraction k) := by
  have h_odd_term (m : ℕ) :
      (((2 * m + 1).factorial : ℂ)⁻¹) •
          (((((-γ : ℝ) * Complex.I : ℂ)) •
              IsingModel.chainPairInteraction k) ^ (2 * m + 1)) =
        (((-Complex.I) *
              (((-1 : ℂ) ^ m) * (γ : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)) :
            ℂ)) •
          IsingModel.chainPairInteraction k := by
    rw [smul_pow, chainPairInteraction_pow_odd, smul_smul]
    have hc2 : ((((-γ : ℝ) * Complex.I : ℂ)) ^ 2) = -((γ : ℂ) ^ 2) := by
      ring_nf; simp
    have heven_pow : ((((-γ : ℝ) * Complex.I : ℂ)) ^ (2 * m)) =
        ((-1 : ℂ) ^ m) * ((γ : ℂ) ^ (2 * m)) := by
      rw [pow_mul, hc2]
      rw [show (-((γ : ℂ) ^ 2)) = (-1 : ℂ) * ((γ : ℂ) ^ 2) by ring]
      rw [mul_pow, ← pow_mul]
    have hpow : ((((-γ : ℝ) * Complex.I : ℂ)) ^ (2 * m + 1)) =
        (((-1 : ℂ) ^ m) * ((γ : ℂ) ^ (2 * m + 1))) * (-Complex.I) := by
      rw [pow_add, heven_pow]
      rw [show ((γ : ℂ) ^ (2 * m + 1)) = ((γ : ℂ) ^ (2 * m)) * (γ : ℂ) by
        rw [pow_add]; simp]
      simp [Complex.ofReal_neg]
      ring
    rw [hpow]
    congr 1
    simp [div_eq_mul_inv, mul_assoc, mul_comm]
  have hsin :
      HasSum (fun m : ℕ =>
          (-1 : ℂ) ^ m * (γ : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ))
        (Real.sin γ) := by
    simpa using (Complex.hasSum_sin (γ : ℂ))
  have h_odd_coeff :
      HasSum
        (fun m : ℕ =>
          (-Complex.I) *
            (((-1 : ℂ) ^ m) * (γ : ℂ) ^ (2 * m + 1) / ((2 * m + 1).factorial : ℂ)))
        (((-Complex.I) * Real.sin γ : ℂ)) := by
    simpa using hsin.mul_left (-Complex.I)
  convert h_odd_coeff.smul_const (IsingModel.chainPairInteraction k) using 1
  funext m
  exact h_odd_term m

set_option maxHeartbeats 600000 in
/-- Closed form for the cost-bond exponential:
`exp(-iγ · Z_k Z_{k+1}) = cos γ · I + (-i sin γ) · Z_k Z_{k+1}`.

Proof mirrors `QAOA.exp_localPauliX`: split the matrix-exponential series
into even and odd parts and identify those subseries with `cos γ · I` and
`(-i sin γ) · chainPairInteraction k` respectively.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem exp_chainPairInteraction_closed_form {n : ℕ} (γ : ℝ) (k : Fin n) :
    NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        IsingModel.chainPairInteraction k) =
      (Real.cos γ : ℂ) • (1 : Qubits.NQubitOp n) +
        ((((-Complex.I) * Real.sin γ : ℂ))) •
          IsingModel.chainPairInteraction k := by
  have hsum :
      HasSum
        (fun m : ℕ =>
          ((m.factorial : ℂ)⁻¹) •
            (((((-γ : ℝ) * Complex.I : ℂ)) •
                IsingModel.chainPairInteraction k) ^ m))
        (((Real.cos γ : ℂ) • (1 : Qubits.NQubitOp n)) +
          ((((-Complex.I) * Real.sin γ : ℂ)) •
            IsingModel.chainPairInteraction k)) :=
    (chainPair_even_hasSum γ k).even_add_odd (chainPair_odd_hasSum γ k)
  rw [NormedSpace.exp_eq_tsum ℂ]
  simpa using hsum.tsum_eq

-- ============================================================================
-- Section: Support of the cost-bond exponential
-- ============================================================================

/-!
With the closed form in hand, the support of the single-bond cost exponential
is read off from its two summands: `cos γ · I` is supported on `∅` (and hence
on any set), and `(-i sin γ) · Z_k Z_{k+1}` on `{k, nextSite k}` via
`supportedOn_chainPairInteraction` (`LightCone.Basic`).
-/

/-- The cost-bond exponential `exp(-iγ · Z_k Z_{k+1})` is supported on the
two-site bond `{k, nextSite k}`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_exp_chainPairInteraction {n : ℕ} (γ : ℝ) (k : Fin n) :
    supportedOn (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        IsingModel.chainPairInteraction k)) := by
  rw [exp_chainPairInteraction_closed_form]
  -- The identity summand is supported on `∅`, hence on any set.
  have h_one : supportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      ((Real.cos γ : ℂ) • (1 : Qubits.NQubitOp n)) :=
    supportedOn_mono (Finset.empty_subset _) (supportedOn_smul_one (Real.cos γ : ℂ))
  -- The chain-pair summand is supported on `{k, nextSite k}`.
  have h_cp : supportedOn
      (({k} : Finset (Fin n)) ∪ ({IsingModel.nextSite k} : Finset (Fin n)))
      (((((-Complex.I) * Real.sin γ : ℂ))) • IsingModel.chainPairInteraction k) :=
    supportedOn_smul _ (supportedOn_chainPairInteraction k)
  -- Their sum is supported on the same union.
  have h_sum := supportedOn_add h_one h_cp
  refine supportedOn_mono ?_ h_sum
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

-- ============================================================================
-- Section: Conjugation by the cost-bond exponential
-- ============================================================================

/-!
Per-bond cost-layer conjugation `U_k · O · V_k`, where `U_k`, `V_k` are
single-bond cost exponentials (possibly at different angles or opposite
signs), is supported on `S ∪ {k, nextSite k}` whenever `O` is supported on
`S`. This is the elementary per-layer cost spreading bound — specializing
`V_k = U_k⁻¹` recovers the standard conjugation form.
-/

/-- Conjugation by a single-bond cost exponential preserves support up to the
bond sites `{k, nextSite k}`. Used to thread the cost layer through the
P-layer recursion in the FGG light-cone analysis.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_conj_chainPair_exp {n : ℕ} {S : Finset (Fin n)}
    {O : Qubits.NQubitOp n} (hO : supportedOn S O) (γ γ' : ℝ) (k : Fin n) :
    supportedOn (S ∪ (({k} : Finset (Fin n)) ∪
        ({IsingModel.nextSite k} : Finset (Fin n))))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k) *
        O *
        NormedSpace.exp ((((-γ' : ℝ) * Complex.I : ℂ)) •
          IsingModel.chainPairInteraction k)) := by
  have h_left := supportedOn_exp_chainPairInteraction γ k
  have h_right := supportedOn_exp_chainPairInteraction γ' k
  have h := supportedOn_conj h_left hO h_right
  -- Re-associate `({k}∪{nextSite k}) ∪ S ∪ ({k}∪{nextSite k}) = S ∪ ({k}∪{nextSite k})`.
  refine supportedOn_mono ?_ h
  intro x hx
  simp only [Finset.mem_union] at hx ⊢
  tauto

-- ============================================================================
-- Section: Full cost-layer support (loose form)
-- ============================================================================

/-!
The cost-layer unitary `exp(-iγ · ∑_k Z_k Z_{k+1})` factors into a noncomm
product of single-bond exponentials (`exp_chainPairInteraction_sum`). Each
factor is supported on its bond `{k, nextSite k}`, so the whole product is
supported on the union of all bonds, which is `Finset.univ`. We record this
as the loose support bound for the full cost layer; the tight per-conjugation
spread (extending `S` only by the layer's reachable sites) is what
`supportedOn_conj_chainPair_exp` provides bond-by-bond, and the full lightcone
expansion is assembled in the downstream A2.3 reduction file.

This is the cost-side analog of `supportedOn_exp_standardMixerOp` above.
-/

/-- The full cost-layer exponential `exp(-iγ · ∑_k Z_k Z_{k+1})` is supported
on the entire qubit register `Finset.univ`. Trivially true entrywise, but the
proof here goes through the noncomm-product factorization to expose the
per-bond building blocks.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_exp_chainPairInteraction_sum (N : ℕ) (γ : ℝ) :
    supportedOn (Finset.univ : Finset (Fin N))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
        (∑ k : Fin N, IsingModel.chainPairInteraction k))) := by
  rw [exp_chainPairInteraction_sum]
  -- The product is supported on `biUnion` of per-bond supports.
  have h_supported :
      supportedOn
        ((Finset.univ : Finset (Fin N)).biUnion
          (fun k => ({k} : Finset (Fin N)) ∪
            ({IsingModel.nextSite k} : Finset (Fin N))))
        ((Finset.univ : Finset (Fin N)).noncommProd
          (fun k => NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
              IsingModel.chainPairInteraction k))
          (fun i _ j _ _ =>
            (chainPairInteractions_commute i j).smul_left _ |>.smul_right _ |>.exp)) := by
    refine supportedOn_noncommProd _ _ _ _ ?_
    intro k _
    exact supportedOn_exp_chainPairInteraction γ k
  -- The biUnion is a subset of `Finset.univ`, so monotone the support up.
  refine supportedOn_mono ?_ h_supported
  intro x _
  exact Finset.mem_univ x

/-- Conjugation by the full cost-layer unitary `exp(-iγ · ∑_k Z_k Z_{k+1})`
preserves support up to `Finset.univ`. This is the loose cost-layer
spreading bound; the tight per-bond version is
`supportedOn_conj_chainPair_exp`.

Source: arXiv:1906.08948v2 §IV l.620–678.
-/
theorem supportedOn_cost_layer_conj {N : ℕ} {S : Finset (Fin N)}
    {O : Qubits.NQubitOp N} (hO : supportedOn S O) (γ γ' : ℝ) :
    supportedOn (Finset.univ : Finset (Fin N))
      (NormedSpace.exp ((((-γ : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k)) *
        O *
        NormedSpace.exp ((((-γ' : ℝ) * Complex.I : ℂ)) •
          (∑ k : Fin N, IsingModel.chainPairInteraction k))) := by
  have h_left := supportedOn_exp_chainPairInteraction_sum N γ
  have h_right := supportedOn_exp_chainPairInteraction_sum N γ'
  have h := supportedOn_conj h_left hO h_right
  refine supportedOn_mono ?_ h
  intro x _
  exact Finset.mem_univ x

end

end QAOA.IsingChain.UpperBound.LightCone
