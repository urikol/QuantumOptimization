import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import QuantumOptimization.IsingModel.IsingHamiltonian

/-!
# 1D Ising Chain Observables — generating functional, first and second moments

Observable-valued quantities associated with the 1D Ising chain Hamiltonian
defined in `QuantumOptimization.IsingModel.IsingHamiltonian`.

This file introduces the basic state-dependent observables for the
periodic 1D Ising chain: the generating functional and the first two moments
of the chain Hamiltonian. These are obtained by evaluating the exponential of
the chain Hamiltonian, and its first two powers, in a normalized `n`-qubit
state.

Unlike the Sherrington–Kirkpatrick model, the chain has no mean-field
`1/√N` normalization and is conventionally studied without a coupling
disorder distribution. We therefore define only the fixed-coupling versions of
the observables.

The intent is to provide a clean interface above the Hamiltonian/state layer,
so that later files (e.g. `QuantumOptimization.QAOA.IsingChain`) can work directly with
moments and generating functions rather than repeatedly unfolding operator
expressions.

## Main definitions
- `chainGeneratingFunctional`: ⟨ψ|exp(iλH_C)|ψ⟩
- `chainFirstMoment`: ⟨ψ|H_C|ψ⟩
- `chainSecondMoment`: ⟨ψ|H_C²|ψ⟩
-/

namespace IsingModel

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
The observables in this file are defined for arbitrary normalized `n`-qubit
states. They can later be specialized to QAOA states by substitution.

The coupling data `J` is held fixed throughout — the 1D Ising chain is
conventionally studied with deterministic couplings (uniform in the ring of
disagrees, edge-weighted in the QAOA literature on weighted chains), rather
than as a disorder ensemble.
-/

/-- The generating functional of the 1D Ising chain in a normalized
`n`-qubit state.

For coupling data `J`, state `|ψ⟩`, and parameter `λ`, this is the scalar
\[
  \left\langle \psi \middle| \exp(i\lambda H_C) \middle| \psi \right\rangle,
\]
where `H_C = isingChainHamiltonianOp J` is the periodic 1D Ising chain
Hamiltonian.

Unlike the SK generating functional, no `1/N` rescaling of the Hamiltonian is
applied: the chain Hamiltonian has no mean-field normalization in the QAOA
literature on the ring of disagrees.
-/
def chainGeneratingFunctional {n : ℕ} (J : IsingChainCouplings n) (lam : ℝ)
    (ψ : Qubits.NQubitNormKet n) : ℂ :=
  ψ.toKet.dag *
    (NormedSpace.exp ((((lam : ℝ) : ℂ) * Complex.I) •
      (isingChainHamiltonianOp J : Qubits.NQubitOp n)) *
      ψ.toKet)

/-- The first moment of the 1D Ising chain Hamiltonian in a normalized
`n`-qubit state.

For coupling data `J` and state `|ψ⟩`, this is
\[
  \left\langle \psi \middle| H_C \middle| \psi \right\rangle.
\]

This is the QAOA cost-function expectation value `F(γ, β)` of
Farhi–Goldstone–Gutmann (arXiv:1411.4028, eq. (8)) when `|ψ⟩` is the
QAOA output state. It is the first derivative of `chainGeneratingFunctional`
at `λ = 0`.
-/
def chainFirstMoment {n : ℕ} (J : IsingChainCouplings n)
    (ψ : Qubits.NQubitNormKet n) : ℂ :=
  ψ.toKet.dag * ((isingChainHamiltonianOp J : Qubits.NQubitOp n) * ψ.toKet)

/-- The second moment of the 1D Ising chain Hamiltonian in a normalized
`n`-qubit state.

For coupling data `J` and state `|ψ⟩`, this is
\[
  \left\langle \psi \middle| H_C^2 \middle| \psi \right\rangle.
\]

Together with `chainFirstMoment`, this gives the variance of the cost
operator and underlies the concentration arguments of
Farhi–Goldstone–Gutmann (arXiv:1411.4028, §III). It is the second derivative
of `chainGeneratingFunctional` at `λ = 0`, up to a factor of `i²`.
-/
def chainSecondMoment {n : ℕ} (J : IsingChainCouplings n)
    (ψ : Qubits.NQubitNormKet n) : ℂ :=
  ψ.toKet.dag *
    (((isingChainHamiltonianOp J : Qubits.NQubitOp n) ^ 2) * ψ.toKet)

end

end IsingModel
