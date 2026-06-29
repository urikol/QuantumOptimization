import QuantumOptimization.QAOA.QAOAHamiltonians
import Mathlib.Analysis.Normed.Algebra.Exponential

/-!
# QAOA Exponentials

Exponential realization of the Hamiltonian QAOA layer maps.

This file refines the abstract Hamiltonian interface by recording that the cost
and mixer unitary families are given by exponentials of the corresponding
Hermitian Hamiltonians.
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section defines the operator-valued exponential expressions associated with
cost and mixer Hamiltonians and packages the statement that a Hamiltonian QAOA
instance realizes its layer maps through those exponentials.

At this stage, the file records the exponential form as part of a structure.
This keeps the intended mathematics explicit without forcing us yet to build the
custom `UnitaryOp` values directly from the matrix exponential API.
-/

/-- The operator `exp(-i γ C)` associated with a cost Hamiltonian `C`. -/
def costExponential {n : ℕ} (C : HermitianOp n) (γ : ℝ) : Op n :=
  NormedSpace.exp ((-γ * Complex.I) • (C : Op n))

/-- The operator `exp(-i β B)` associated with a mixer Hamiltonian `B`. -/
def mixerExponential {n : ℕ} (B : HermitianOp n) (β : ℝ) : Op n :=
  NormedSpace.exp ((-β * Complex.I) • (B : Op n))

/-- A Hamiltonian QAOA instance whose layer maps are explicitly realized as
exponentials of the stored Hermitian Hamiltonians. -/
structure QAOAExponentials (n : ℕ) extends QAOAHamiltonians n where
  costUnitary_spec : ∀ γ : ℝ, (costUnitary γ : Op n) = costExponential costHamiltonian γ
  mixerUnitary_spec : ∀ β : ℝ, (mixerUnitary β : Op n) = mixerExponential mixerHamiltonian β

/-- The Hamiltonian QAOA state associated with an exponential realization and an
arbitrary normalized initial state. -/
def exponentialQAOAState {n p : ℕ} (H : QAOAExponentials n)
    (γ β : Fin p → ℝ) (ψ0 : NormKet n) : NormKet n :=
  hamiltonianQAOAState H.toQAOAHamiltonians γ β ψ0

/-- The standard QAOA state associated with an exponential realization, using
the uniform superposition as initial state. -/
def standardExponentialQAOAState {n p : ℕ} [NeZero n] (H : QAOAExponentials n)
    (γ β : Fin p → ℝ) : NormKet n :=
  standardHamiltonianQAOAState H.toQAOAHamiltonians γ β

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas expose the exponential interpretation of the layer maps and relate
the new constructions back to the Hamiltonian-based QAOA states defined in
`QAOAHamiltonians.lean`.
-/

/-- In an exponential realization, the cost layer at angle `γ` is exactly
`exp(-i γ C)` on the underlying operator level. -/
@[simp]
theorem costUnitary_eq_costExponential {n : ℕ} (H : QAOAExponentials n) (γ : ℝ) :
    (H.costUnitary γ : Op n) = costExponential H.costHamiltonian γ :=
  H.costUnitary_spec γ

/-- In an exponential realization, the mixer layer at angle `β` is exactly
`exp(-i β B)` on the underlying operator level. -/
@[simp]
theorem mixerUnitary_eq_mixerExponential {n : ℕ} (H : QAOAExponentials n) (β : ℝ) :
    (H.mixerUnitary β : Op n) = mixerExponential H.mixerHamiltonian β :=
  H.mixerUnitary_spec β

/-- The cost-unitary family associated with an exponential realization evaluates
to the corresponding cost exponential at each angle. -/
@[simp]
theorem costUnitaryFamily_eq_costExponential {n p : ℕ} (H : QAOAExponentials n)
    (γ : Fin p → ℝ) (i : Fin p) :
    (costUnitaryFamily H.toQAOAHamiltonians γ i : Op n) =
      costExponential H.costHamiltonian (γ i) := by
  simp [costUnitaryFamily]

/-- The mixer-unitary family associated with an exponential realization evaluates
to the corresponding mixer exponential at each angle. -/
@[simp]
theorem mixerUnitaryFamily_eq_mixerExponential {n p : ℕ} (H : QAOAExponentials n)
    (β : Fin p → ℝ) (i : Fin p) :
    (mixerUnitaryFamily H.toQAOAHamiltonians β i : Op n) =
      mixerExponential H.mixerHamiltonian (β i) := by
  simp [mixerUnitaryFamily]

/-- Exponential QAOA is just Hamiltonian QAOA specialized to a Hamiltonian
instance whose layer maps satisfy the exponential specification. -/
@[simp]
theorem exponentialQAOAState_eq_hamiltonianQAOAState {n p : ℕ} (H : QAOAExponentials n)
    (γ β : Fin p → ℝ) (ψ0 : NormKet n) :
    exponentialQAOAState H γ β ψ0 =
      hamiltonianQAOAState H.toQAOAHamiltonians γ β ψ0 := rfl

/-- Standard exponential QAOA is the standard Hamiltonian QAOA state attached to
the same exponential realization. -/
@[simp]
theorem standardExponentialQAOAState_eq_standardHamiltonianQAOAState
    {n p : ℕ} [NeZero n] (H : QAOAExponentials n) (γ β : Fin p → ℝ) :
    standardExponentialQAOAState H γ β =
      standardHamiltonianQAOAState H.toQAOAHamiltonians γ β := rfl

/-- Depth-`0` exponential QAOA leaves the initial state unchanged. -/
@[simp]
theorem exponentialQAOAState_zero {n : ℕ} (H : QAOAExponentials n) (ψ0 : NormKet n) :
    exponentialQAOAState (n := n) (p := 0) H (fun i => nomatch i) (fun i => nomatch i) ψ0 = ψ0 := by
  exact hamiltonianQAOAState_zero (H := H.toQAOAHamiltonians) ψ0

/-- Depth-`0` standard exponential QAOA is the uniform initial state. -/
@[simp]
theorem standardExponentialQAOAState_zero {n : ℕ} [NeZero n] (H : QAOAExponentials n) :
    standardExponentialQAOAState (n := n) (p := 0) H (fun i => nomatch i) (fun i => nomatch i) =
      uniformState n := by
  exact standardHamiltonianQAOAState_zero (H := H.toQAOAHamiltonians)

end

end QAOA
