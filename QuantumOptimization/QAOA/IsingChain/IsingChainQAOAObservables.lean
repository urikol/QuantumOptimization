import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials
import QuantumOptimization.IsingModel.IsingObservables

/-!
# Ising Chain QAOA Observables — generating functional and moments for chain-QAOA states

Chain observables specialized to the standard chain exponential-QAOA state.

The generic chain observables in `IsingModel.IsingObservables` are defined
for arbitrary normalized `n`-qubit states at fixed couplings. Unlike the SK
analogue, no disorder ensemble is averaged over: the periodic 1D Ising chain
is studied in the QAOA literature with deterministic couplings (uniform in
the ring of disagrees, edge-weighted in the weighted variants).

This file therefore provides direct chain-QAOA specializations:
for fixed coupling data `J` and an exponential realization `hChain`, evaluate
the chain observable on `standardIsingChainExponentialQAOAState hChain γ β`.

## Main definitions
- `QAOA.isingChainQAOAGeneratingFunctional`: ⟨γ,β| exp(iλ H_C) |γ,β⟩
- `QAOA.isingChainQAOAFirstMoment`: F_p(γ,β) = ⟨γ,β| H_C |γ,β⟩, the central
  observable of all three QAOA-on-the-ring papers.
- `QAOA.isingChainQAOASecondMoment`: ⟨γ,β| H_C² |γ,β⟩, used by the
  Farhi–Goldstone–Gutmann concentration argument (arXiv:1411.4028, §III).
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Standard Chain Exponential-QAOA Observables
-- ============================================================================

/-!
For fixed coupling data `J`, the standard chain exponential-QAOA state
`standardIsingChainExponentialQAOAState (hChain J) γ β` realizes the QAOA
output `|γ, β⟩` of the papers. The observables below are obtained by
plugging this state into the corresponding chain observables of
`IsingModel.IsingObservables`.

No integration over `J` is performed: the chain QAOA is conventionally
studied at deterministic couplings.
-/

/-- Generating functional of the chain Hamiltonian evaluated on the standard
chain exponential-QAOA state.

For coupling data `J`, exponential realization `hChain`, angle parameters
`(γ, β)`, and parameter `λ`, this is
\[
  \left\langle \gamma, \beta \middle| \exp(i\lambda H_C) \middle| \gamma, \beta \right\rangle,
\]
where `H_C = isingChainHamiltonianOp J` and `|γ, β⟩` is the standard chain
exponential-QAOA state.
-/
def isingChainQAOAGeneratingFunctional {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J)
    (γ β : Fin p → ℝ) (lam : ℝ) : ℂ :=
  IsingModel.chainGeneratingFunctional J lam
    (standardIsingChainExponentialQAOAState hChain γ β)

/-- First moment of the chain Hamiltonian evaluated on the standard chain
exponential-QAOA state.

This is the QAOA cost-function expectation
\[
  F_p(\boldsymbol\gamma, \boldsymbol\beta) =
    \left\langle \gamma, \beta \middle| H_C \middle| \gamma, \beta \right\rangle
\]
of Farhi–Goldstone–Gutmann (arXiv:1411.4028, eq. (8)) — the central
quantity whose maximization defines the QAOA approximation ratio for the ring
of disagrees.
-/
def isingChainQAOAFirstMoment {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J)
    (γ β : Fin p → ℝ) : ℂ :=
  IsingModel.chainFirstMoment J
    (standardIsingChainExponentialQAOAState hChain γ β)

/-- Second moment of the chain Hamiltonian evaluated on the standard chain
exponential-QAOA state.

Together with `isingChainQAOAFirstMoment`, this gives the variance of the
cost operator, underlying the concentration argument of
Farhi–Goldstone–Gutmann (arXiv:1411.4028, §III).
-/
def isingChainQAOASecondMoment {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J)
    (γ β : Fin p → ℝ) : ℂ :=
  IsingModel.chainSecondMoment J
    (standardIsingChainExponentialQAOAState hChain γ β)

end

end QAOA
