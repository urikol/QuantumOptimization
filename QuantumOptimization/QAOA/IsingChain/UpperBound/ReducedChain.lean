import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials

/-!
# Reduced Chain Hamiltonians — `Hred_x`, `Hred_z^±`, `|ψ̃⟩` on `N_R = 2P+2` sites

This file collects the *reduced-chain* objects used in the elementary upper-bound
proof of the QAOA ring-of-disagrees residual energy (arXiv:1906.08948v2 §IV,
lines 661–686). For depth `P : ℕ`, the reduced chain has `N_R = 2P+2` sites; the
two-namespace split below separates the public targets:

* `QAOA.IsingChain.ringOfDisagreesCouplings` — the uniform unit antiferromagnetic
  coupling data `J ≡ 1`, in the *parent* namespace, since `residualEnergy` and
  every Theorem A/B/C statement names it at this exact fully-qualified path.

* `QAOA.IsingChain.UpperBound.{Hred_x_op, Hred_z_pm, psiTilde_init, psiTilde}` —
  the reduced-chain mixer and cost Hamiltonians, the uniform initial state, and
  the depth-`P` reduced-chain QAOA state, all private to the upper-bound proof.

## Source pins (arXiv:1906.08948v2)

* `Hred_x`        — eq. at l.669: `Hred_x = -Σ_{j=1}^{N_R} σ^x_j`.
* `Hred_z^±`      — eq. at l.662:
  `Hred_z^± = Σ_{j=1}^{N_R-1}(σ^z_j σ^z_{j+1} - 1) + (± σ^z_{N_R} σ^z_1 - 1)`.
  We split this into a `Hred_z_body` (body bonds) and `Hred_z_boundary` (the
  sign-twisted boundary bond), per the A1 plan's fallback recommendation.
* `|ψ̃_0⟩ = |+⟩^{⊗N_R}` — l.686.
* `|ψ̃_P(γ,β)⟩`    — l.683: time-ordered product
  `T-prod_{m=1}^{P} e^{-iβ_m Hred_x} e^{-iγ_m Hred_z^±} |ψ̃_0⟩`.

The boundary fork is fixed: `s = false ↔ ABC
(J_b = -1)` is the binding branch; `s = true ↔ PBC (J_b = +1)` is included for
symmetry with the source's exposition. This file does not pick the fork — it
keeps both available as a function of `s : Bool`.

## Main definitions

* `ringOfDisagreesCouplings` — `IsingModel.IsingChainCouplings n` with `J ≡ 1`.
* `Hred_x_op` — reduced-chain mixer Hamiltonian operator `-Σ X_j`.
* `Hred_x_hamiltonian` — Hermitian packaging of `Hred_x_op`.
* `Hred_z_body`, `Hred_z_boundary`, `Hred_z_pm` — reduced-chain cost Hamiltonian
  operator with the ABC / PBC sign fork.
* `Hred_z_hamiltonian` — Hermitian packaging of `Hred_z_pm`.
* `psiTilde_init` — reduced-chain initial state `|+⟩^{⊗N_R}` as `NQubitNormKet`.
* `reducedChainQAOAExp` — `QAOAExponentials` package on the reduced chain.
* `psiTilde` — depth-`P` reduced-chain QAOA state.

## Main statements

* `psiTilde_zero` — base case of the QAOA recursion: at depth `0`,
  `psiTilde s 0 γ β = psiTilde_init 0` (both at `NQubitNormKet 2`).
-/

namespace QAOA.IsingChain

open Quantum.Operators
open scoped BigOperators

noncomputable section

/-- Coupling data for the **ring of disagrees**: the uniform unit
antiferromagnetic chain `J_k ≡ 1` on `n` sites.

This is
the only coupling specialization used by the public targets `residualEnergy_…`,
and it must live in the parent namespace `QAOA.IsingChain` (NOT under
`UpperBound`) because every Theorem A/B/C statement refers to it at this
exact fully-qualified name.
-/
def ringOfDisagreesCouplings (n : ℕ) : IsingModel.IsingChainCouplings n :=
  ⟨fun _ ↦ 1⟩

namespace UpperBound

-- ============================================================================
-- Local Hermitian helpers
-- ============================================================================

/-!
The QAOA exponential interface (`QAOAExponentials`) packages cost and mixer
layers as `UnitaryOp` values together with a `costUnitary_spec` /
`mixerUnitary_spec` field certifying that the underlying operator is
`costExponential` / `mixerExponential`. The two helpers below produce such
unitary packagings from a plain `HermitianOp`, by proving that the matrix
exponential of an anti-Hermitian operator is unitary. They are kept local to
this file because they sit at the `NQubitOp` / `NQubitUnitaryOp` level rather
than the more generic `Op` / `UnitaryOp` level used in
`QAOAExponentials.lean`.
-/

/-- The skew-Hermitian generator `(-x * i) • A` for a Hermitian `A` has
conjugate transpose equal to its negation. -/
private lemma neg_iSmul_hermitian_conjTranspose {N : ℕ}
    (A : Qubits.NQubitHermitianOp N) (x : ℝ) :
    (((-x * Complex.I) • (A : Qubits.NQubitOp N))†) =
      -((-x * Complex.I) • (A : Qubits.NQubitOp N)) := by
  rw [Matrix.conjTranspose_smul, A.isHermitian]
  -- star (-↑x * I) = (-↑x) * (-I) = ↑x * I = -(-↑x * I)
  have hstar : star ((-x : ℝ) * Complex.I : ℂ) = -((-x : ℝ) * Complex.I : ℂ) := by
    change (starRingEnd ℂ) (((-x : ℝ) : ℂ) * Complex.I) =
      -(((-x : ℝ) : ℂ) * Complex.I)
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [show ((-↑x * Complex.I : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
      hstar, neg_smul]

/-- For Hermitian `A`, `exp(-iy A)` is unitary: its conjugate-transpose-product
with itself is the identity. -/
private lemma exp_neg_iSmul_hermitian_unitary {N : ℕ}
    (A : Qubits.NQubitHermitianOp N) (y : ℝ) :
    (NormedSpace.exp ((-y * Complex.I) • (A : Qubits.NQubitOp N)))† *
        NormedSpace.exp ((-y * Complex.I) • (A : Qubits.NQubitOp N)) = 1 := by
  set S : Qubits.NQubitOp N := (-y * Complex.I) • (A : Qubits.NQubitOp N) with hS
  rw [← Matrix.exp_conjTranspose, neg_iSmul_hermitian_conjTranspose A y]
  have hcomm : Commute (-S) S := Commute.neg_left (Commute.refl _)
  rw [show NormedSpace.exp (-S) * NormedSpace.exp S =
      NormedSpace.exp (-S + S) from (Matrix.exp_add_of_commute (-S) S hcomm).symm]
  rw [neg_add_cancel, NormedSpace.exp_zero]

/-- For Hermitian `A`, `exp(-iy A) * exp(-iy A)† = 1`. -/
private lemma exp_neg_iSmul_hermitian_unitary' {N : ℕ}
    (A : Qubits.NQubitHermitianOp N) (y : ℝ) :
    NormedSpace.exp ((-y * Complex.I) • (A : Qubits.NQubitOp N)) *
        (NormedSpace.exp ((-y * Complex.I) • (A : Qubits.NQubitOp N)))† = 1 := by
  set S : Qubits.NQubitOp N := (-y * Complex.I) • (A : Qubits.NQubitOp N) with hS
  rw [← Matrix.exp_conjTranspose, neg_iSmul_hermitian_conjTranspose A y]
  have hcomm : Commute S (-S) := Commute.neg_right (Commute.refl _)
  rw [show NormedSpace.exp S * NormedSpace.exp (-S) =
      NormedSpace.exp (S + (-S)) from (Matrix.exp_add_of_commute S (-S) hcomm).symm]
  rw [add_neg_cancel, NormedSpace.exp_zero]

/-- Unitarity packaging of `costExponential A γ = exp(-iγ A)` for a Hermitian
operator `A` on `N` qubits. -/
def costUnitaryOfHermitian {N : ℕ} (A : Qubits.NQubitHermitianOp N) (γ : ℝ) :
    Qubits.NQubitUnitaryOp N where
  toOp := costExponential A γ
  unitary_left := by
    change (NormedSpace.exp ((-γ * Complex.I) • (A : Qubits.NQubitOp N)))† *
        NormedSpace.exp ((-γ * Complex.I) • (A : Qubits.NQubitOp N)) = 1
    exact exp_neg_iSmul_hermitian_unitary A γ
  unitary_right := by
    change NormedSpace.exp ((-γ * Complex.I) • (A : Qubits.NQubitOp N)) *
        (NormedSpace.exp ((-γ * Complex.I) • (A : Qubits.NQubitOp N)))† = 1
    exact exp_neg_iSmul_hermitian_unitary' A γ

/-- Unitarity packaging of `mixerExponential A β = exp(-iβ A)` for a Hermitian
operator `A` on `N` qubits. -/
def mixerUnitaryOfHermitian {N : ℕ} (A : Qubits.NQubitHermitianOp N) (β : ℝ) :
    Qubits.NQubitUnitaryOp N where
  toOp := mixerExponential A β
  unitary_left := by
    change (NormedSpace.exp ((-β * Complex.I) • (A : Qubits.NQubitOp N)))† *
        NormedSpace.exp ((-β * Complex.I) • (A : Qubits.NQubitOp N)) = 1
    exact exp_neg_iSmul_hermitian_unitary A β
  unitary_right := by
    change NormedSpace.exp ((-β * Complex.I) • (A : Qubits.NQubitOp N)) *
        (NormedSpace.exp ((-β * Complex.I) • (A : Qubits.NQubitOp N)))† = 1
    exact exp_neg_iSmul_hermitian_unitary' A β

@[simp]
theorem costUnitaryOfHermitian_toOp {N : ℕ} (A : Qubits.NQubitHermitianOp N) (γ : ℝ) :
    ((costUnitaryOfHermitian A γ : Qubits.NQubitUnitaryOp N) : Qubits.NQubitOp N) =
      costExponential A γ := rfl

@[simp]
theorem mixerUnitaryOfHermitian_toOp {N : ℕ} (A : Qubits.NQubitHermitianOp N) (β : ℝ) :
    ((mixerUnitaryOfHermitian A β : Qubits.NQubitUnitaryOp N) : Qubits.NQubitOp N) =
      mixerExponential A β := rfl

-- ============================================================================
-- Hred_x — reduced mixer Hamiltonian
-- ============================================================================

/-- Reduced-chain mixer Hamiltonian operator on `N_R = 2P+2` sites:
`Hred_x = -Σ_{j=0}^{2P+1} X_j`.

Source pin: arXiv:1906.08948v2 l.669 (eq. `Hred_x`). The 1-based source sum
`j = 1..N_R` matches Lean's `j : Fin (2*P+2)` over all sites — there is no
off-by-one because we sum over all sites without a boundary distinction. We
realize this as `-(standardMixerOp (2*P+2))`, reusing the existing scaffold for
later access to the standard-mixer Hermitian / exponential lemmas.
-/
def Hred_x_op (P : ℕ) : Qubits.NQubitOp (2*P+2) :=
  -(standardMixerOp (2*P+2))

/-- Hermitian packaging of the reduced-chain mixer Hamiltonian `Hred_x_op`. -/
def Hred_x_hamiltonian (P : ℕ) : Qubits.NQubitHermitianOp (2*P+2) :=
  -(standardMixerHamiltonian (2*P+2))

@[simp]
theorem Hred_x_hamiltonian_toOp (P : ℕ) :
    (Hred_x_hamiltonian P : Qubits.NQubitOp (2*P+2)) = Hred_x_op P := rfl

-- ============================================================================
-- Hred_z^± — reduced cost Hamiltonian (body + boundary form)
-- ============================================================================

/-- Body part of the reduced-chain cost Hamiltonian:
`Σ_{j=0}^{2P}(Z_j Z_{j+1} - 1)`, the `2P+1` interior bonds, each shifted by
`-1`.

Source pin: arXiv:1906.08948v2 l.662, body sum
`Σ_{j=1}^{N_R-1}(σ^z_j σ^z_{j+1} - 1)`. In 0-indexed Lean, the source's
`j = 1..N_R-1` translates to `k : Fin (2P+1)` via the `Fin.castSucc` inclusion
into `Fin (2P+2)`; on each such `k` the `chainPairInteraction k.castSucc`
operator equals `Z_k * Z_{k+1}` because
`nextSite k.castSucc = ⟨(k.val+1) mod (2P+2), …⟩ = k.castSucc.succ` for
`k.val < 2P+1` (no wrap-around).
-/
def Hred_z_body (P : ℕ) : Qubits.NQubitOp (2*P+2) :=
  ∑ k : Fin (2*P+1),
    (IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
      (1 : Qubits.NQubitOp (2*P+2)))

/-- Boundary (wrap-around) bond of the reduced-chain cost Hamiltonian:
`s · Z_{N_R} Z_1 - 1`, with `s = true ↔ +1 (PBC, J_b = +1)` and
`s = false ↔ -1 (ABC, J_b = -1)`.

Source pin: arXiv:1906.08948v2 l.662, boundary `± σ^z_{N_R} σ^z_1 - 1`. In
0-indexed Lean the source's `σ^z_{N_R} σ^z_1` corresponds to the
`chainPairInteraction (Fin.last (2*P+1))` operator, whose underlying expression
`Z_k * Z_{nextSite k}` evaluates at `k = Fin.last (2*P+1)` to
`Z_{2P+1} * Z_0` (since `nextSite (Fin.last n) = ⟨(n+1) mod (n+1), …⟩ = 0`).
-/
def Hred_z_boundary (s : Bool) (P : ℕ) : Qubits.NQubitOp (2*P+2) :=
  (if s then (1 : ℂ) else (-1 : ℂ)) •
      IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) -
    (1 : Qubits.NQubitOp (2*P+2))

/-- Reduced-chain cost Hamiltonian on `N_R = 2P+2` sites:
`Hred_z^± = Σ_{j=0}^{2P}(Z_j Z_{j+1} - 1) + (± Z_{2P+1} Z_0 - 1)`.

Source pin: arXiv:1906.08948v2 l.662 (eq. `Hred_z`). `s = false` selects the
ABC sector (`J_b = -1`) which is binding for the upper-bound proof (fork
resolution); `s = true` selects PBC (`J_b = +1`) and is included only
for symmetry with the source's exposition. The body + boundary decomposition
is used to keep the boundary sign fork off the body sum.
-/
def Hred_z_pm (s : Bool) (P : ℕ) : Qubits.NQubitOp (2*P+2) :=
  Hred_z_body P + Hred_z_boundary s P

-- ============================================================================
-- Hermitian packaging of Hred_z^±
-- ============================================================================

/-- Local Pauli `Z` operator is Hermitian. -/
private theorem localPauliZ_hermitian {N : ℕ} (j : Fin N) :
    (Qubits.localPauliZ j)† = Qubits.localPauliZ j := by
  rw [Qubits.localPauliZ_eq_localOp, Qubits.localOp_conjTranspose]
  simp [Quantum.Gates.pauliZ_hermitian]

/-- Two local Pauli `Z` operators commute (both are diagonal in the
computational basis). -/
private theorem localPauliZ_commute {N : ℕ} (i j : Fin N) :
    Commute (Qubits.localPauliZ i) (Qubits.localPauliZ j) := by
  change Qubits.localPauliZ i * Qubits.localPauliZ j =
    Qubits.localPauliZ j * Qubits.localPauliZ i
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  rw [op_mul_op_mul_ket, Qubits.localPauliZ_on_basis,
      op_mul_smul_ket, Qubits.localPauliZ_on_basis,
      op_mul_op_mul_ket, Qubits.localPauliZ_on_basis,
      op_mul_smul_ket, Qubits.localPauliZ_on_basis,
      Ket.smul_smul, Ket.smul_smul, mul_comm]

/-- Hermiticity of a single chain pair interaction `Z_k * Z_{nextSite k}`. The
two factors act on different sites (`k ≠ nextSite k` for `n ≥ 2`) and are
diagonal in the computational basis, so they commute; the product of two
commuting Hermitian operators is Hermitian. -/
private theorem chainPairInteraction_isHermitian {n : ℕ} (k : Fin n) :
    (IsingModel.chainPairInteraction k).IsHermitian := by
  unfold IsingModel.chainPairInteraction
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul,
      localPauliZ_hermitian, localPauliZ_hermitian]
  exact (localPauliZ_commute k (IsingModel.nextSite k)).symm

/-- Hermitian packaging of the reduced-chain cost Hamiltonian. The sum of
Hermitian operators is Hermitian; subtracting a real-scalar multiple of the
identity preserves Hermiticity; the boundary `± Z_{2P+1} Z_0` is Hermitian
(since `Z * Z` is Hermitian and `±` is a real scalar). -/
def Hred_z_hamiltonian (s : Bool) (P : ℕ) : Qubits.NQubitHermitianOp (2*P+2) where
  toOp := Hred_z_pm s P
  isHermitian := by
    unfold Hred_z_pm Hred_z_body Hred_z_boundary
    rw [Matrix.IsHermitian]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
        Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        Matrix.conjTranspose_one]
    have hbond_herm : ∀ k : Fin (2*P+1),
        (IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
            (1 : Qubits.NQubitOp (2*P+2)))† =
          IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
            (1 : Qubits.NQubitOp (2*P+2)) := by
      intro k
      rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
          chainPairInteraction_isHermitian]
    have hboundary_herm :
        (IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)))† =
          IsingModel.chainPairInteraction (Fin.last (2*P+1) : Fin (2*P+2)) :=
      chainPairInteraction_isHermitian _
    have hcoef_real :
        star (if s then (1 : ℂ) else (-1 : ℂ)) =
          (if s then (1 : ℂ) else (-1 : ℂ)) := by
      by_cases hs : s
      · simp [hs]
      · simp [hs]
    rw [Finset.sum_congr rfl (fun k _ ↦ hbond_herm k), hboundary_herm, hcoef_real]

@[simp]
theorem Hred_z_hamiltonian_toOp (s : Bool) (P : ℕ) :
    (Hred_z_hamiltonian s P : Qubits.NQubitOp (2*P+2)) = Hred_z_pm s P := rfl

-- ============================================================================
-- psiTilde_init — uniform initial state
-- ============================================================================

/-- Reduced-chain initial state `|ψ̃_0⟩ = |+⟩^{⊗N_R}` on `N_R = 2P+2` sites,
realized as `uniformState (IsingChainQAOADim (2*P+2))`.

Source pin: arXiv:1906.08948v2 l.686. Routing through `IsingChainQAOADim`
matches the existing `standardIsingChainExponentialQAOAState` packaging so the
`psiTilde_zero` sanity lemma below holds by `rfl`.
-/
def psiTilde_init (P : ℕ) : Qubits.NQubitNormKet (2*P+2) :=
  uniformState (IsingChainQAOADim (2*P+2))

-- ============================================================================
-- psiTilde — depth-P QAOA state via the QAOAExponentials wrapper
-- ============================================================================

/-- `QAOAExponentials` packaging for the reduced-chain QAOA: the cost
Hamiltonian is `Hred_z^±` and the mixer Hamiltonian is `Hred_x`; the cost /
mixer unitaries are realized by `costExponential` / `mixerExponential` (with
the unitarity proof provided by the local helpers above). -/
def reducedChainQAOAExp (s : Bool) (P : ℕ) :
    QAOAExponentials (IsingChainQAOADim (2*P+2)) where
  costHamiltonian := Hred_z_hamiltonian s P
  mixerHamiltonian := Hred_x_hamiltonian P
  costUnitary γ := costUnitaryOfHermitian (Hred_z_hamiltonian s P) γ
  mixerUnitary β := mixerUnitaryOfHermitian (Hred_x_hamiltonian P) β
  costUnitary_spec := fun _ ↦ rfl
  mixerUnitary_spec := fun _ ↦ rfl

/-- Depth-`P` reduced-chain QAOA state
`|ψ̃_P(γ,β)⟩ = T-prod_{m=1}^{P} e^{-iβ_m Hred_x} e^{-iγ_m Hred_z^±} |ψ̃_0⟩`.

Source pin: arXiv:1906.08948v2 l.683 (eq. `psi_tilde_qaoa`). The "time-ordered
product" convention here is the same as in `standardExponentialQAOAState`: the
layer `(γ 0, β 0)` is applied first (cost then mixer), and subsequent layers
recurse on top. The boundary sign fork `s : Bool` selects ABC (`s = false`,
binding for the upper-bound proof) or PBC (`s = true`).
-/
def psiTilde (s : Bool) (P : ℕ) (γ β : Fin P → ℝ) :
    Qubits.NQubitNormKet (2*P+2) :=
  standardExponentialQAOAState (reducedChainQAOAExp s P) γ β

-- ============================================================================
-- Base case: psiTilde at depth 0
-- ============================================================================

/-- Base case of the QAOA depth recursion: at depth `P = 0`, the reduced-chain
QAOA state is the uniform initial state on `N_R = 2` sites. This is the form
needed by the `P`-induction in `ABCInvariance.lean`.

Both sides have type `Qubits.NQubitNormKet (2*0+2) = Qubits.NQubitNormKet 2`.
-/
theorem psiTilde_zero (s : Bool) (γ β : Fin 0 → ℝ) :
    psiTilde s 0 γ β = psiTilde_init 0 := by
  -- Both sides reduce to `uniformState (IsingChainQAOADim 2)` by unfolding the
  -- `qaoaStateAux 0` base case (which ignores its angle arguments).
  rfl

end UpperBound

end

end QAOA.IsingChain
