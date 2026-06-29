import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.CostDecomposition
import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.FourierCollection
import QuantumOptimization.QAOA.IsingChain.JordanWigner.PseudospinDynamics.Dynamics
import QuantumOptimization.QAOA.IsingChain.UpperBound.ResidualEnergyBound

/-!
# Mode-Decomposition Geometry — `epsilonMode`, its geometric form, and the L0 bra-op-ket bridge

Foundation layer of the mode decomposition. Provides the per-mode residual
energy definition together with its two consumers' building blocks:

* `epsilonMode k γ β = ‖τ⃗_k(γ,−β) − b̂_k‖²/2` — the per-mode residual energy
  (arXiv:1911.12259v2 SM `eqn:eresk_geometrical_def`), with `extendFin` padding the
  `Fin P → ℝ` angle families to the `ℕ → ℝ` families the pseudospin `tauVec` consumes.
* `geometric_form` — the geometric rewrite `ε_k = 1 − b̂_k ⬝ᵥ τ⃗_k(γ,−β)` (both unit vectors).
* `braOpKet_eq_dotProduct` — the L0 matrix-level expansion `⟨ψ|O|ψ⟩ = (star v) ⬝ᵥ (O *ᵥ v)`,
  reused by the magnetization expectations (`ExpReduction`) and the final assembly.

## Main definitions
- `extendFin`: pad a `Fin P → ℝ` angle family to `ℕ → ℝ` (zero beyond `P`)
- `epsilonMode`: the per-mode residual energy `‖τ⃗_k(γ,−β) − b̂_k‖²/2`

## Main statements
- `norm_sub_sq_of_unit`: `‖u − v‖² = 2 − 2 (u ⬝ᵥ v)` for unit vectors `u`, `v`
- `geometric_form`: `ε_k = 1 − b̂_k ⬝ᵥ τ⃗_k(γ,−β)`
- `braOpKet_eq_dotProduct`: `ψ.dag * (O * ψ) = (star ψ.vec) ⬝ᵥ (O *ᵥ ψ.vec)`
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 0: angle-family extension and the `epsilonMode` definition
-- ============================================================================

/-- Pad a `Fin P → ℝ` angle family to a `ℕ → ℝ` family (zero beyond `P`). B3's
`tauVec` consumes `ℕ → ℝ` families but only reads indices in `range P`, so the
padding value is irrelevant. -/
def extendFin {P : ℕ} (γ : Fin P → ℝ) : ℕ → ℝ :=
  fun m => if h : m < P then γ ⟨m, h⟩ else 0

/-- **The per-mode residual energy** `ε_k = ‖τ⃗_k(γ,−β) − b̂_k‖²/2` (arXiv:1911.12259v2
SM `eqn:eresk_geometrical_def`, l.957). The c-number magnetization `tauVec` (from the
pseudospin dynamics) is fed the `(−β)` mixer angles (matching the upper-bound
`psiTilde false P γ (−β)`) and the pseudospin-dynamics internal F7 rotation sign
`s = +1`; the difference with the cost axis `b̂_k` is taken in the
Euclidean `Fin 3 → ℝ` space. -/
def epsilonMode {P : ℕ} (k : WaveVectorABC P) (γ β : Fin P → ℝ) : ℝ :=
  ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm
      (tauVec P (waveVectorABC P k) (extendFin γ) (extendFin (fun i => -(β i)))
        - bHat (waveVectorABC P k))‖ ^ 2 / 2

-- ============================================================================
-- Section 1: geometric form  ε_k = 1 − b̂_k · τ⃗_k(γ,−β)
-- ============================================================================

/-- The squared Euclidean distance of two unit vectors `u`, `v` (given via their
`dotProduct` self-products) equals `2 − 2 (u ⬝ᵥ v)`. -/
theorem norm_sub_sq_of_unit (u v : Fin 3 → ℝ) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (u - v)‖ ^ 2 = 2 - 2 * (u ⬝ᵥ v) := by
  have hnorm : ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (u - v)‖ ^ 2
      = (u - v) ⬝ᵥ (u - v) := by
    rw [EuclideanSpace.norm_eq]
    rw [Real.sq_sqrt (by positivity)]
    rw [dotProduct]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs]
    change ((EuclideanSpace.equiv (Fin 3) ℝ).symm (u - v)).ofLp i ^ 2 = (u - v) i * (u - v) i
    rw [show ((EuclideanSpace.equiv (Fin 3) ℝ).symm (u - v)).ofLp i = (u - v) i from rfl, sq]
  rw [hnorm]
  -- (u - v)·(u - v) = u·u − 2 u·v + v·v
  rw [dotProduct_sub, sub_dotProduct, sub_dotProduct, hu, hv, dotProduct_comm v u]
  ring

/-- **Geometric form** of the per-mode residual energy: `ε_k = 1 − b̂_k ⬝ᵥ τ⃗_k(γ,−β)`
(arXiv:1911.12259v2 SM, `eqn:eresk_geometrical_def`). Both `τ⃗_k` and `b̂_k` are unit
vectors. -/
theorem geometric_form {P : ℕ} (k : WaveVectorABC P) (γ β : Fin P → ℝ) :
    epsilonMode k γ β =
      1 - (bHat (waveVectorABC P k)) ⬝ᵥ
        (tauVec P (waveVectorABC P k) (extendFin γ) (extendFin (fun i => -(β i)))) := by
  unfold epsilonMode
  set kk := waveVectorABC P k
  set tv := tauVec P kk (extendFin γ) (extendFin (fun i => -(β i))) with htv
  rw [norm_sub_sq_of_unit tv (bHat kk)
      (tauVec_dot_self P kk (extendFin γ) (extendFin (fun i => -(β i))))
      (bHat_dot_self kk)]
  rw [dotProduct_comm tv (bHat kk)]
  ring

-- ============================================================================
-- Section 2: in-scope copy of the upper-bound's private `bra_op_ket_eq_dotProduct` (L0)
-- ============================================================================

/-- (L0) `Bra * (Op * Ket)` equals the matrix-level `dotProduct (star v) (M *ᵥ v)`.
In-scope copy of the upper-bound's `private bra_op_ket_eq_dotProduct`
(ResidualEnergyBound.lean:83). -/
theorem braOpKet_eq_dotProduct {N : ℕ}
    (ψ : Qubits.NQubitKet N) (O : Qubits.NQubitOp N) :
    ψ.dag * (O * ψ) = dotProduct (star ψ.vec) (Matrix.mulVec O ψ.vec) := by
  rw [bra_mul_ket_eq]
  rfl

end

end QAOA.IsingChain.JordanWigner
