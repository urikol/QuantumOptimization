import QuantumOptimization.QAOA.StandardQAOA

/-!
# QAOA Hamiltonians

Hamiltonian-based interface for QAOA.

This file sits between the generic unitary-layer definition of QAOA and later
problem-specific files. It records the cost and mixer Hamiltonians together with
their associated angle-parameterized unitary layers.
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section packages the Hamiltonian data for a QAOA instance and defines the
unitary families obtained by evaluating the cost and mixer layers at angle
parameters `γ` and `β`.

At this level the layer maps are kept abstract. They are intended to represent
the standard expressions `exp(-i γ C)` and `exp(-i β B)`, but we do not yet
commit to a concrete matrix-exponential API in the library.
-/

/-- Hamiltonian data for a QAOA instance together with its angle-parameterized
cost and mixer unitaries. -/
structure QAOAHamiltonians (n : ℕ) where
  costHamiltonian : HermitianOp n
  mixerHamiltonian : HermitianOp n
  costUnitary : ℝ → UnitaryOp n
  mixerUnitary : ℝ → UnitaryOp n

/-- The family of cost unitaries obtained from a sequence of cost angles `γ`. -/
def costUnitaryFamily {n p : ℕ} (H : QAOAHamiltonians n) (γ : Fin p → ℝ) :
    Fin p → UnitaryOp n :=
  fun i => H.costUnitary (γ i)

/-- The family of mixer unitaries obtained from a sequence of mixer angles `β`. -/
def mixerUnitaryFamily {n p : ℕ} (H : QAOAHamiltonians n) (β : Fin p → ℝ) :
    Fin p → UnitaryOp n :=
  fun i => H.mixerUnitary (β i)

/-- QAOA state generated from Hamiltonian data, angle families, and an arbitrary
normalized initial state. -/
def hamiltonianQAOAState {n p : ℕ} (H : QAOAHamiltonians n)
    (γ β : Fin p → ℝ) (ψ0 : NormKet n) : NormKet n :=
  qaoaState (costUnitaryFamily H γ) (mixerUnitaryFamily H β) ψ0

/-- Standard QAOA state generated from Hamiltonian data and angle families,
using the uniform superposition as the initial state. -/
def standardHamiltonianQAOAState {n p : ℕ} [NeZero n] (H : QAOAHamiltonians n)
    (γ β : Fin p → ℝ) : NormKet n :=
  standardQAOAState (costUnitaryFamily H γ) (mixerUnitaryFamily H β)

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas expose the Hamiltonian-based constructions through the recursion
already proved for `qaoaState` and `standardQAOAState`. They are intended as the
main interface for later proofs that reason about QAOA in terms of angle
parameters rather than preassembled unitary families.
-/

/-- Evaluating the cost-unitary family at index `i` simply returns the cost
layer corresponding to the angle `γ i`. This is useful for rewriting family
entries into explicit angle-parameterized unitaries. -/
@[simp]
theorem costUnitaryFamily_apply {n p : ℕ} (H : QAOAHamiltonians n)
    (γ : Fin p → ℝ) (i : Fin p) :
    costUnitaryFamily H γ i = H.costUnitary (γ i) := rfl

/-- Evaluating the mixer-unitary family at index `i` simply returns the mixer
layer corresponding to the angle `β i`. This is the mixer analogue of
`costUnitaryFamily_apply`. -/
@[simp]
theorem mixerUnitaryFamily_apply {n p : ℕ} (H : QAOAHamiltonians n)
    (β : Fin p → ℝ) (i : Fin p) :
    mixerUnitaryFamily H β i = H.mixerUnitary (β i) := rfl

/-- Depth-`0` Hamiltonian QAOA leaves the initial state unchanged. -/
@[simp]
theorem hamiltonianQAOAState_zero {n : ℕ} (H : QAOAHamiltonians n)
    (ψ0 : NormKet n) :
    hamiltonianQAOAState (n := n) (p := 0) H (fun i => nomatch i) (fun i => nomatch i) ψ0 = ψ0 := by
  exact qaoaState_zero (n := n) (ψ0 := ψ0)

/-- A depth-`p + 1` Hamiltonian QAOA state is obtained by applying the first
cost and mixer layers and then recursing on the remaining `p` layers. -/
@[simp]
theorem hamiltonianQAOAState_succ {n p : ℕ} (H : QAOAHamiltonians n)
    (γ β : Fin (p + 1) → ℝ) (ψ0 : NormKet n) :
    hamiltonianQAOAState H γ β ψ0 =
      qaoaState
        (tailFamily (costUnitaryFamily H γ))
        (tailFamily (mixerUnitaryFamily H β))
        (applyLayer (H.costUnitary (γ 0)) (H.mixerUnitary (β 0)) ψ0) := by
  rfl

/-- Depth-`0` standard Hamiltonian QAOA is the uniform initial state. -/
@[simp]
theorem standardHamiltonianQAOAState_zero {n : ℕ} [NeZero n] (H : QAOAHamiltonians n) :
    standardHamiltonianQAOAState (n := n) (p := 0) H (fun i => nomatch i) (fun i => nomatch i) =
      uniformState n := by
  exact standardQAOAState_zero (n := n)

/-- A depth-`p + 1` standard Hamiltonian QAOA state is obtained by applying the
first cost and mixer layers to the uniform state and then recursing on the
remaining `p` layers. -/
@[simp]
theorem standardHamiltonianQAOAState_succ {n p : ℕ} [NeZero n] (H : QAOAHamiltonians n)
    (γ β : Fin (p + 1) → ℝ) :
    standardHamiltonianQAOAState H γ β =
      qaoaState
        (tailFamily (costUnitaryFamily H γ))
        (tailFamily (mixerUnitaryFamily H β))
        (applyLayer (H.costUnitary (γ 0)) (H.mixerUnitary (β 0)) (uniformState n)) := by
  rfl

end

end QAOA
