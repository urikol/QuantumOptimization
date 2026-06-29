import QuantumOptimization.Quantum.Operators.BraKet
import QuantumOptimization.Quantum.Operators.Types

/-!
# QAOA State

Generic formalization of a depth-`p` QAOA state.

This first version keeps the layer unitaries abstract. A QAOA instance is specified by:
- an initial normalized state `ψ₀`
- a sequence of cost unitaries `U_C^1, ..., U_C^p`
- a sequence of mixer unitaries `U_B^1, ..., U_B^p`

The depth-`p` QAOA state is then

`|ψ_p⟩ = U_B^p U_C^p ... U_B^1 U_C^1 |ψ_0⟩`.

This matches the standard QAOA circuit structure while avoiding an early commitment
to a specific Hamiltonian exponential API.

Implementation note:
- the Lean family `costUnitary : Fin p → UnitaryOp n` is interpreted as the ordered list
  `U_C^1, ..., U_C^p`
- the Lean family `mixerUnitary : Fin p → UnitaryOp n` is interpreted as the ordered list
  `U_B^1, ..., U_B^p`
- so `costUnitary 0` means the first layer unitary `U_C^1`, and similarly for the mixer
-/




namespace QAOA

open Quantum.Operators

noncomputable section



-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section introduces the basic objects used to define a generic QAOA state:
how to discard the first layer of a family of unitaries, how to apply one QAOA
layer to a normalized state, and how to recursively build the depth-`p` state.
-/

/-- Drop the first element of a `Fin (p + 1)`-indexed family. -/
def tailFamily {α : Type*} {p : ℕ} (f : Fin (p + 1) → α) : Fin p → α :=
  fun i => f i.succ

/-- One QAOA layer: apply `U_C^j`, then `U_B^j`, for layer `j`. -/
def applyLayer {n : ℕ} (costUnitary mixerUnitary : UnitaryOp n) (ψ : NormKet n) : NormKet n :=
  mixerUnitary * (costUnitary * ψ)

/-- Recursive auxiliary definition of the depth-`p` QAOA state.

At recursive depth `p + 1`, the first entries `costUnitary 0` and `mixerUnitary 0`
represent the first-layer operators `U_C^1` and `U_B^1`. After applying them,
the recursion continues on the tail, which corresponds to layers `2` through `p + 1`. -/
def qaoaStateAux {n : ℕ}
    (depth : ℕ)
    (costUnitary : Fin depth → UnitaryOp n)
    (mixerUnitary : Fin depth → UnitaryOp n)
    (ψ0 : NormKet n) : NormKet n :=
  match depth with
  | 0 => ψ0
  | depth + 1 =>
      qaoaStateAux depth
        (tailFamily costUnitary)
        (tailFamily mixerUnitary)
        (applyLayer (costUnitary 0) (mixerUnitary 0) ψ0)

/-- The depth-`p` QAOA state generated from an initial normalized state.

Mathematically this is

`|ψ_p⟩ = U_B^p U_C^p ... U_B^1 U_C^1 |ψ_0⟩`,

where `costUnitary` and `mixerUnitary` store the layer operators in order starting
from layer `1`. -/
def qaoaState {n p : ℕ}
    (costUnitary : Fin p → UnitaryOp n)
    (mixerUnitary : Fin p → UnitaryOp n)
    (ψ0 : NormKet n) : NormKet n :=
  qaoaStateAux p costUnitary mixerUnitary ψ0





-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These first theorems expose the recursive structure of `qaoaState` and connect the
normalized-state definition to ordinary ket algebra.

- `qaoaState_zero` is the base case: depth `0` leaves the initial state unchanged.
- `qaoaState_succ` is the recursion step: a depth-`p + 1` state is obtained by applying
  the first layer and then recursing on the remaining `p` layers.
- `applyLayer_toKet` rewrites one QAOA layer at the level of ordinary kets, which is
  often the convenient form for algebraic manipulations and later expectation-value
  calculations.

Together these lemmas are the basic interface for proofs by induction on the QAOA depth
and for moving between `NormKet`-based definitions and ket-level expressions.
-/

/-- Depth-`0` QAOA applies no layers, so the resulting state is exactly the initial state. -/
@[simp]
theorem qaoaState_zero {n : ℕ} (ψ0 : NormKet n) :
    qaoaState (n := n) (p := 0) (fun i => nomatch i) (fun i => nomatch i) ψ0 = ψ0 := by
  simp [qaoaState, qaoaStateAux]

/-- A depth-`p + 1` QAOA state is obtained by applying the first layer and then
recursing on the remaining `p` layers. -/
@[simp]
theorem qaoaState_succ {n p : ℕ}
    (costUnitary : Fin (p + 1) → UnitaryOp n)
    (mixerUnitary : Fin (p + 1) → UnitaryOp n)
    (ψ0 : NormKet n) :
    qaoaState costUnitary mixerUnitary ψ0 =
      qaoaState
        (tailFamily costUnitary)
        (tailFamily mixerUnitary)
        (applyLayer (costUnitary 0) (mixerUnitary 0) ψ0) := rfl

/-- Converting `applyLayer` to an ordinary ket exposes the expected ket-level action
`U_B (U_C |ψ⟩)`, which is convenient for algebraic rewriting. -/
@[simp]
theorem applyLayer_toKet {n : ℕ} (costUnitary mixerUnitary : UnitaryOp n) (ψ : NormKet n) :
    (applyLayer costUnitary mixerUnitary ψ).toKet =
      mixerUnitary * (costUnitary * ψ.toKet) := by
  simp [applyLayer, UnitaryOp_mul_NormKet_toKet]




end

end QAOA
