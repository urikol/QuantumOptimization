import QuantumOptimization.QAOA.IsingChain.IsingChainQAOA

/-!
# Ising Chain QAOA State — depth-p variational states for the periodic 1D Ising chain

State-level specialization of the generic QAOA constructions to the periodic
1D Ising chain. This file sits one layer above `IsingChainQAOA.lean`: the
latter packages the chain cost Hamiltonian and the standard mixer into
Hamiltonian data, while the present file uses that data to define the
corresponding depth-`p` QAOA states.

The angle-dependent unitary layer maps are kept abstract, so that these
definitions remain compatible with the current Hamiltonian-level QAOA API
without committing to a concrete matrix-exponential realization.

In the notation of Farhi–Goldstone–Gutmann (arXiv:1411.4028, eq. (7)), the
state `standardIsingChainQAOAState J γ β` is the QAOA output
`|γ, β⟩ = U(B,β_p) U(C,γ_p) ⋯ U(B,β_1) U(C,γ_1) |+⟩^{⊗n}` for the cost
Hamiltonian `C = isingChainHamiltonianOp J` and the standard transverse mixer
`B = ∑_j X_j`.

## Main definitions
- `QAOA.isingChainHamiltonianQAOAState`: chain-QAOA state with an arbitrary
  normalized initial state.
- `QAOA.standardIsingChainQAOAState`: chain-QAOA state using the uniform
  superposition as initial state.

## Main statements
- `QAOA.isingChainHamiltonianQAOAState_zero`: depth-0 chain-QAOA returns the
  initial state unchanged.
- `QAOA.isingChainHamiltonianQAOAState_succ`: depth-(p+1) chain-QAOA unfolds
  one layer then recurses.
- `QAOA.standardIsingChainQAOAState_zero`: depth-0 standard chain-QAOA is the
  uniform state.
- `QAOA.standardIsingChainQAOAState_succ`: depth-(p+1) standard chain-QAOA
  unfolds one layer then recurses.
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section specializes the generic Hamiltonian-based QAOA state definitions
to the periodic 1D Ising chain.

Two versions are provided:

* `isingChainHamiltonianQAOAState`, which allows an arbitrary normalized
  initial state,
* `standardIsingChainQAOAState`, which uses the standard uniform superposition
  as the initial state — this is the QAOA state `|γ, β⟩` of the papers.
-/

/-- Hamiltonian-based chain-QAOA state with an arbitrary normalized initial
state.

The cost Hamiltonian is the chain Hamiltonian determined by the couplings
`J`, and the mixer Hamiltonian is the standard QAOA mixer. The actual cost
and mixer unitaries are still passed in abstractly as angle-parameterized
unitary maps, so that this definition stays compatible with the current
Hamiltonian-level QAOA API.
-/
def isingChainHamiltonianQAOAState {n p : ℕ} (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n)
    (γ β : Fin p → ℝ) (ψ0 : Qubits.NQubitNormKet n) : Qubits.NQubitNormKet n :=
  hamiltonianQAOAState (isingChainQAOAHamiltonians J costUnitary mixerUnitary) γ β ψ0

/-- Standard chain-QAOA state, using the uniform superposition as the initial
state.

This is the chain specialization of `standardHamiltonianQAOAState`, and it is
the state `|γ, β⟩` analyzed in
Farhi–Goldstone–Gutmann (arXiv:1411.4028, §IV) and
Wang–Hadfield–Jiang–Rieffel (arXiv:1706.02998).
-/
def standardIsingChainQAOAState {n p : ℕ} (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n)
    (γ β : Fin p → ℝ) : Qubits.NQubitNormKet n :=
  standardHamiltonianQAOAState (isingChainQAOAHamiltonians J costUnitary mixerUnitary) γ β

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These theorems expose the chain-QAOA states through the generic recursion
lemmas already proved for Hamiltonian-based QAOA.

They give the basic interface for later proofs about low-depth chain-QAOA
states:

* depth `0` is the initial state,
* depth `p + 1` is obtained by applying the first cost and mixer layers and
  then recursing on the remaining `p` layers.
-/

/-- Chain-QAOA with depth `0` leaves an arbitrary normalized initial state
unchanged. -/
@[simp]
theorem isingChainHamiltonianQAOAState_zero {n : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n)
    (ψ0 : Qubits.NQubitNormKet n) :
    isingChainHamiltonianQAOAState (n := n) (p := 0) J costUnitary mixerUnitary
      (fun i => nomatch i) (fun i => nomatch i) ψ0 = ψ0 := by
  unfold isingChainHamiltonianQAOAState hamiltonianQAOAState
  exact qaoaState_zero (n := IsingChainQAOADim n) (ψ0 := ψ0)

/-- A depth-`p + 1` chain-QAOA state is obtained by applying the first cost
and mixer layers and then recursing on the remaining `p` layers. -/
@[simp]
theorem isingChainHamiltonianQAOAState_succ {n p : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n)
    (γ β : Fin (p + 1) → ℝ) (ψ0 : Qubits.NQubitNormKet n) :
    isingChainHamiltonianQAOAState J costUnitary mixerUnitary γ β ψ0 =
      qaoaState
        (tailFamily (costUnitaryFamily
          (isingChainQAOAHamiltonians J costUnitary mixerUnitary) γ))
        (tailFamily (mixerUnitaryFamily
          (isingChainQAOAHamiltonians J costUnitary mixerUnitary) β))
        (applyLayer (costUnitary (γ 0)) (mixerUnitary (β 0)) ψ0) := by
  rfl

/-- Standard chain-QAOA with depth `0` is the uniform initial state on the
underlying `n`-qubit Hilbert space. -/
@[simp]
theorem standardIsingChainQAOAState_zero {n : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n) :
    standardIsingChainQAOAState (n := n) (p := 0) J costUnitary mixerUnitary
      (fun i => nomatch i) (fun i => nomatch i) =
        uniformState (IsingChainQAOADim n) := by
  unfold standardIsingChainQAOAState standardHamiltonianQAOAState
  exact standardQAOAState_zero (n := IsingChainQAOADim n)

/-- A depth-`p + 1` standard chain-QAOA state is obtained by applying the
first cost and mixer layers to the uniform state and then recursing on the
remaining `p` layers. -/
@[simp]
theorem standardIsingChainQAOAState_succ {n p : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n)
    (γ β : Fin (p + 1) → ℝ) :
    standardIsingChainQAOAState J costUnitary mixerUnitary γ β =
      qaoaState
        (tailFamily (costUnitaryFamily
          (isingChainQAOAHamiltonians J costUnitary mixerUnitary) γ))
        (tailFamily (mixerUnitaryFamily
          (isingChainQAOAHamiltonians J costUnitary mixerUnitary) β))
        (applyLayer (costUnitary (γ 0)) (mixerUnitary (β 0))
          (uniformState (IsingChainQAOADim n))) := by
  rfl

end

end QAOA
