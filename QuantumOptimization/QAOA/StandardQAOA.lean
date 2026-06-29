import QuantumOptimization.QAOA.QAOAState
import Mathlib.Data.Real.Sqrt

/-!
# Standard QAOA

Specialization of the generic QAOA state to the standard choice of initial state:
the uniform superposition over the computational basis.
-/

namespace QAOA

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section defines the standard uniform initial state and then specializes the
generic `qaoaState` construction to that choice of initial state.
-/

/-- The uniform superposition ket in dimension `n`, with amplitude `1 / sqrt n`
on every computational basis vector. -/
def uniformKet (n : ℕ) [NeZero n] : Ket n :=
  ⟨fun _ => ((1 / Real.sqrt (n : ℝ) : ℝ) : ℂ)⟩

/-- The uniform superposition state is normalized. -/
theorem uniformKet_IsNormalized (n : ℕ) [NeZero n] :
    (uniformKet n).IsNormalized := by
  unfold Ket.IsNormalized uniformKet
  simp only [bra_mul_ket_eq, Ket.dag_vec, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have hn_real : (n : ℝ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 := Real.sqrt_ne_zero'.mpr hn_pos
  have hsq_real : (n : ℝ) * ((1 / Real.sqrt (n : ℝ)) * (1 / Real.sqrt (n : ℝ))) = 1 := by
    field_simp [hsqrt]
    nlinarith [Real.sq_sqrt (show 0 ≤ (n : ℝ) by positivity)]
  rw [nsmul_eq_mul]
  simp only [Complex.conj_ofReal]
  exact_mod_cast hsq_real

/-- The normalized uniform superposition state in dimension `n`. -/
def uniformState (n : ℕ) [NeZero n] : NormKet n :=
  ⟨uniformKet n, uniformKet_IsNormalized n⟩

/-- Standard QAOA uses the uniform superposition as the initial normalized state. -/
def standardQAOAState {n p : ℕ} [NeZero n]
    (costUnitary : Fin p → UnitaryOp n)
    (mixerUnitary : Fin p → UnitaryOp n) : NormKet n :=
  qaoaState costUnitary mixerUnitary (uniformState n)

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These theorems expose the standard QAOA state through the generic recursion lemmas.
They let later proofs work directly with the uniform initial state while still using
the recursive structure already developed in `QAOAState.lean`.
-/

/-- The underlying ket of `uniformState` is `uniformKet`. -/
@[simp]
theorem uniformState_toKet (n : ℕ) [NeZero n] :
    (uniformState n).toKet = uniformKet n := rfl

/-- Depth-`0` standard QAOA is exactly the uniform initial state. -/
@[simp]
theorem standardQAOAState_zero {n : ℕ} [NeZero n] :
    standardQAOAState (n := n) (p := 0) (fun i => nomatch i) (fun i => nomatch i) =
      uniformState n := by
  unfold standardQAOAState
  exact qaoaState_zero (n := n) (ψ0 := uniformState n)

/-- A depth-`p + 1` standard QAOA state is obtained by applying the first layer
to the uniform state and then recursing on the remaining `p` layers. -/
@[simp]
theorem standardQAOAState_succ {n p : ℕ} [NeZero n]
    (costUnitary : Fin (p + 1) → UnitaryOp n)
    (mixerUnitary : Fin (p + 1) → UnitaryOp n) :
    standardQAOAState costUnitary mixerUnitary =
      qaoaState
        (tailFamily costUnitary)
        (tailFamily mixerUnitary)
        (applyLayer (costUnitary 0) (mixerUnitary 0) (uniformState n)) := by
  simp [standardQAOAState, qaoaState_succ]

end

end QAOA
