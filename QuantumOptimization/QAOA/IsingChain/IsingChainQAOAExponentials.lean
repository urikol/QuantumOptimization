import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import QuantumOptimization.QAOA.QAOAExponentials
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAState

/-!
# Ising Chain QAOA Exponentials — exponential realization of cost and mixer layers

This file specializes the generic exponential QAOA interface to the periodic
1D Ising chain. It records that the cost and mixer unitary families are
given by the standard expressions `exp(-i γ H_C)` and `exp(-i β B)`, and
derives the diagonal action of the cost exponential on computational-basis
kets.

## Main definitions
- `IsingChainQAOAExponentials`: structure packaging the exponential cost and
  mixer unitaries for the chain, with proofs that they match the operator
  exponentials.
- `isingChainToQAOAExponentials`: converts an `IsingChainQAOAExponentials` instance to
  the generic `QAOAExponentials` package.
- `isingChainExponentialQAOAState`: depth-`p` chain-QAOA state from an
  exponential realization and an arbitrary initial state.
- `standardIsingChainExponentialQAOAState`: standard chain-QAOA state using
  the uniform superposition.

## Main statements
- `isingChainCostExponential_on_basis`: the chain cost exponential acts
  diagonally on computational-basis kets, with phase given by the classical
  chain energy.
- `isingChainCostUnitary_on_basis`: the chain cost unitary multiplies a basis
  ket by the corresponding energy phase.
- `isingChainExponentialQAOAState_zero`: depth-`0` chain exponential QAOA is
  the identity.
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section packages the exponential realization of chain QAOA.

The structure `IsingChainQAOAExponentials` keeps the Hamiltonians fixed to
the chain cost Hamiltonian and the standard mixer Hamiltonian. The only
remaining data are the angle-parameterized unitary families, together with
proofs that they agree with the corresponding operator exponentials.
-/

/-- Exponential realization of the cost and mixer layers for chain QAOA.

For fixed coupling data `J`, this structure records unitary families whose
underlying operators are exactly the exponentials of the chain cost
Hamiltonian and the standard mixer Hamiltonian.
-/
structure IsingChainQAOAExponentials (n : ℕ)
    (J : IsingModel.IsingChainCouplings n) where
  costUnitary : ℝ → Qubits.NQubitUnitaryOp n
  mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n
  costUnitary_spec :
    ∀ γ : ℝ, (costUnitary γ : Qubits.NQubitOp n) =
      costExponential (isingChainCostHamiltonian J) γ
  mixerUnitary_spec :
    ∀ β : ℝ, (mixerUnitary β : Qubits.NQubitOp n) =
      mixerExponential (isingChainMixerHamiltonian n) β

/-- The generic exponential-QAOA package associated with a chain exponential
realization. -/
def isingChainToQAOAExponentials {n : ℕ} {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) :
    QAOAExponentials (IsingChainQAOADim n) where
  costHamiltonian := isingChainCostHamiltonian J
  mixerHamiltonian := isingChainMixerHamiltonian n
  costUnitary := hChain.costUnitary
  mixerUnitary := hChain.mixerUnitary
  costUnitary_spec := hChain.costUnitary_spec
  mixerUnitary_spec := hChain.mixerUnitary_spec

/-- Chain-QAOA state obtained from an exponential realization and an
arbitrary normalized initial state. -/
def isingChainExponentialQAOAState {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ)
    (ψ0 : Qubits.NQubitNormKet n) : Qubits.NQubitNormKet n :=
  exponentialQAOAState (isingChainToQAOAExponentials hChain) γ β ψ0

/-- Standard chain-QAOA state obtained from an exponential realization, using
the uniform superposition as the initial state. -/
def standardIsingChainExponentialQAOAState {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ) :
    Qubits.NQubitNormKet n :=
  standardExponentialQAOAState (isingChainToQAOAExponentials hChain) γ β

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas expose the chain-specific exponential interface in a form
convenient for later calculations. They identify the layer maps with the
intended exponentials and relate the new definitions both to the generic
exponential QAOA state and to the previously defined abstract chain-QAOA
state.
-/

/-- In a chain exponential realization, the cost layer at angle `γ` is
exactly `exp(-i γ H_C)` on the underlying operator level. -/
@[simp]
theorem isingChainCostUnitary_eq_costExponential {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ : ℝ) :
    (hChain.costUnitary γ : Qubits.NQubitOp n) =
      costExponential (isingChainCostHamiltonian J) γ :=
  hChain.costUnitary_spec γ

/-- In a chain exponential realization, the mixer layer at angle `β` is
exactly `exp(-i β B)` for the standard mixer Hamiltonian `B`. -/
@[simp]
theorem isingChainMixerUnitary_eq_mixerExponential {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (β : ℝ) :
    (hChain.mixerUnitary β : Qubits.NQubitOp n) =
      mixerExponential (isingChainMixerHamiltonian n) β :=
  hChain.mixerUnitary_spec β

/-- The chain cost exponential acts diagonally on computational-basis kets.

Since the chain cost Hamiltonian is diagonal in the computational basis with
eigenvalues `IsingModel.classicalChainEnergy J z`, exponentiating it simply
exponentiates those scalar eigenvalues.
-/
theorem isingChainCostExponential_on_basis {n : ℕ}
    (J : IsingModel.IsingChainCouplings n) (γ : ℝ) (z : Qubits.BitString n) :
    costExponential (isingChainCostHamiltonian J) γ *
        Qubits.computationalBasisKet n z =
      (NormedSpace.exp (((-γ * Complex.I) *
          (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ))))) •
        Qubits.computationalBasisKet n z := by
  ext ix
  rw [costExponential, isingChainCostHamiltonian_toOp, isingChainCostOp_eq_diagonal]
  have hscaled :
      (-γ * Complex.I) •
          Matrix.diagonal
            (fun ix =>
              (((IsingModel.classicalChainEnergy J
                  ((Qubits.bitStringEquiv n).symm ix) : ℝ) : ℂ))) =
        Matrix.diagonal
          (fun ix =>
            (-γ * Complex.I) *
              (((IsingModel.classicalChainEnergy J
                  ((Qubits.bitStringEquiv n).symm ix) : ℝ) : ℂ))) := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [Matrix.diagonal_apply_eq]
    · simp [h]
  rw [hscaled, Matrix.exp_diagonal, Qubits.op_mul_computationalBasisKet_vec]
  by_cases hix : ix = Qubits.bitStringEquiv n z
  · subst ix
    have hcoord :
        (Qubits.computationalBasisKet n z).vec
            ((Math.RepresentationTheory.tensorIndexEquiv 2 n) z) = 1 := by
      simp [Qubits.computationalBasisKet]
    simp [Qubits.bitStringEquiv, Quantum.TensorProducts.Ket.smul_vec_apply, hcoord]
  · rw [Matrix.diagonal_apply_ne _ hix]
    have hcoord :
        (Qubits.computationalBasisKet n z).vec ix = 0 := by
      have hneq : (Math.RepresentationTheory.tensorIndexEquiv 2 n) z ≠ ix := by
        simpa [Qubits.bitStringEquiv] using Ne.symm hix
      simp [Qubits.computationalBasisKet, hneq]
    simp [Quantum.TensorProducts.Ket.smul_vec_apply, hcoord]

/-- In a chain exponential realization, the cost layer at angle `γ`
multiplies a computational-basis ket by the phase determined by the classical
chain energy. -/
theorem isingChainCostUnitary_on_basis {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ : ℝ) (z : Qubits.BitString n) :
    hChain.costUnitary γ * Qubits.computationalBasisKet n z =
      (NormedSpace.exp (((-γ * Complex.I) *
          (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ))))) •
        Qubits.computationalBasisKet n z := by
  change ((hChain.costUnitary γ : Qubits.NQubitOp n) *
      Qubits.computationalBasisKet n z =
    (NormedSpace.exp (((-γ * Complex.I) *
        (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ))))) •
      Qubits.computationalBasisKet n z)
  calc
    ((hChain.costUnitary γ : Qubits.NQubitOp n) *
        Qubits.computationalBasisKet n z)
      = costExponential (isingChainCostHamiltonian J) γ *
            Qubits.computationalBasisKet n z := by
          simp [isingChainCostUnitary_eq_costExponential]
    _ =
      (NormedSpace.exp (((-γ * Complex.I) *
          (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ))))) •
        Qubits.computationalBasisKet n z := by
          exact isingChainCostExponential_on_basis J γ z

/-- The generic cost Hamiltonian stored in the associated exponential-QAOA
package is the packaged chain cost Hamiltonian. -/
@[simp]
theorem isingChainToQAOAExponentials_costHamiltonian_isingChain {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) :
    (isingChainToQAOAExponentials hChain).costHamiltonian = isingChainCostHamiltonian J := rfl

/-- The generic mixer Hamiltonian stored in the associated exponential-QAOA
package is the packaged standard mixer Hamiltonian. -/
@[simp]
theorem isingChainToQAOAExponentials_mixerHamiltonian_isingChain {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) :
    (isingChainToQAOAExponentials hChain).mixerHamiltonian = isingChainMixerHamiltonian n := rfl

/-- Chain exponential QAOA is the generic exponential QAOA state specialized
to the chain exponential package. -/
@[simp]
theorem isingChainExponentialQAOAState_eq_exponentialQAOAState {n p : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ)
    (ψ0 : Qubits.NQubitNormKet n) :
    isingChainExponentialQAOAState hChain γ β ψ0 =
      exponentialQAOAState (isingChainToQAOAExponentials hChain) γ β ψ0 := rfl

/-- Standard chain exponential QAOA is the standard generic exponential QAOA
state attached to the same chain exponential realization. -/
@[simp]
theorem standardIsingChainExponentialQAOAState_eq_standardExponentialQAOAState
    {n p : ℕ} {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ) :
    standardIsingChainExponentialQAOAState hChain γ β =
      standardExponentialQAOAState (isingChainToQAOAExponentials hChain) γ β := rfl

/-- Forgetting the exponential specification reduces chain exponential QAOA
to the abstract Hamiltonian-based chain-QAOA state with the same unitary
families. -/
@[simp]
theorem isingChainExponentialQAOAState_eq_isingChainHamiltonianQAOAState
    {n p : ℕ} {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ)
    (ψ0 : Qubits.NQubitNormKet n) :
    isingChainExponentialQAOAState hChain γ β ψ0 =
      isingChainHamiltonianQAOAState J hChain.costUnitary hChain.mixerUnitary γ β ψ0 := rfl

/-- The standard chain exponential QAOA state reduces to the abstract
standard chain-QAOA state with the same unitary families. -/
@[simp]
theorem standardIsingChainExponentialQAOAState_eq_standardIsingChainQAOAState
    {n p : ℕ} {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (γ β : Fin p → ℝ) :
    standardIsingChainExponentialQAOAState hChain γ β =
      standardIsingChainQAOAState J hChain.costUnitary hChain.mixerUnitary γ β := rfl

/-- Depth-`0` chain exponential QAOA leaves an arbitrary normalized initial
state unchanged. -/
@[simp]
theorem isingChainExponentialQAOAState_zero {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) (ψ0 : Qubits.NQubitNormKet n) :
    isingChainExponentialQAOAState (n := n) (p := 0) hChain
      (fun i => nomatch i) (fun i => nomatch i) ψ0 = ψ0 := by
  exact exponentialQAOAState_zero (isingChainToQAOAExponentials hChain) ψ0

/-- Depth-`0` standard chain exponential QAOA is the uniform initial state on
the underlying `n`-qubit Hilbert space. -/
@[simp]
theorem standardIsingChainExponentialQAOAState_zero {n : ℕ}
    {J : IsingModel.IsingChainCouplings n}
    (hChain : IsingChainQAOAExponentials n J) :
    standardIsingChainExponentialQAOAState (n := n) (p := 0) hChain
        (fun i => nomatch i) (fun i => nomatch i) =
      uniformState (IsingChainQAOADim n) := by
  exact standardExponentialQAOAState_zero (isingChainToQAOAExponentials hChain)

end

end QAOA
