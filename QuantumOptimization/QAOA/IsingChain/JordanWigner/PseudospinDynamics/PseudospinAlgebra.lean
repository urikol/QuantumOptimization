import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.CostDecomposition
import QuantumOptimization.QAOA.IsingChain.JordanWigner.PseudospinDynamics.PauliKernel
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Pseudospin Algebra at the Active Pair — `τ⃗_k` operators, `dotTau`, L3 product identity

(arXiv:1911.12259v2 SM l.859–909.) Instantiates the
abstract `PauliKernel` at the concrete active fermion pair `(c_{k_n}, c_{-k_n})`,
producing the per-mode pseudospin operators `τ⃗_k = (τ^x_k, τ^y_k, τ^z_k)`, the dotted
operator `û·τ⃗_k` (`dotTau`), the pair-block operator `S_k` (`Spair`), and the full
operator-level Pauli product table.

The headline result is L3 (`pauli_dot_mul_dot`): the operator product identity
`(û·τ⃗_k)(v̂·τ⃗_k) = (û·v̂)·S_k + i (û×v̂)·τ⃗_k`, where the symmetric part carries the
pair-block projector `S_k`, not the identity.

## Main definitions
- `tauVecOp`: the pseudospin vector `(τ^x_k, τ^y_k, τ^z_k)` as `Fin 3 → NQubitOp`.
- `dotTau`: the dotted pseudospin operator `û·τ⃗_k = Σ_a û_a τ^a_k`.
- `Spair`: the per-mode pair-block operator `S_k`.

## Main statements
- `carPair`: the CAR bundle holds at the active pair.
- `tauX_eq_kernel`, `tauY_eq_kernel`, `tauZ_eq_kernel`: the B2 pseudospins equal the
  abstract-kernel forms.
- `pauli_dot_mul_dot` (L3): the pseudospin Pauli product identity.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- B3-L3: instantiate the abstract Pauli kernel at the active `(k_n, −k_n)` pair
-- ============================================================================

/-- The within-pair canonical anticommutation relations hold for the active mode
`(c_{k_n}, c_{−k_n})` (annihilators `a = c_{k_n}, b = c_{−k_n}`, creators
`d = c_{k_n}†, e = c_{−k_n}†`), assembling B2's CAR lemmas into a `PauliKernel.CAR`. -/
theorem carPair (P : ℕ) (n : Fin P) :
    PauliKernel.CAR (cAnnihK P (waveVectorABC P n)) (cAnnihK P (-(waveVectorABC P n)))
      (cCreateK P (waveVectorABC P n)) (cCreateK P (-(waveVectorABC P n))) := by
  set k := waveVectorABC P n with hk
  have hcast1 : ((k : ℝ) : ℂ) - ((-k : ℝ) : ℂ) = (((k : ℝ) - (-k : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
  have hcast2 : ((-k : ℝ) : ℂ) - ((k : ℝ) : ℂ) = (((-k : ℝ) - (k : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_sub]
  refine
    { aa := cAnnihK_mul_self P k
      bb := cAnnihK_mul_self P (-k)
      dd := cCreateK_mul_self P k
      ee := cCreateK_mul_self P (-k)
      ad := ?_
      be := ?_
      ab := ?_
      ae := ?_
      db := ?_
      de := ?_ }
  · -- {c_k, c_k†} = 1
    have := car_annihK_createK_same P k
    linear_combination (norm := noncomm_ring) this
  · -- {c_{-k}, c_{-k}†} = 1
    have := car_annihK_createK_same P (-k)
    linear_combination (norm := noncomm_ring) this
  · -- {c_k, c_{-k}} = 0
    have := car_annihK_annihK P k (-k)
    linear_combination (norm := noncomm_ring) this
  · -- {c_k, c_{-k}†} = 0
    have := car_annihK_createK_zero P k (-k)
      (by rw [hcast1]; exact exp_within_pair_ne_one P n)
      (by rw [hcast1]; exact exp_within_pair_root P n)
    linear_combination (norm := noncomm_ring) this
  · -- {c_k†, c_{-k}} = 0  (from {c_{-k}, c_k†} = 0)
    have := car_annihK_createK_zero P (-k) k
      (by rw [hcast2]; exact exp_within_pair_neg_ne_one P n)
      (by rw [hcast2]; exact exp_within_pair_neg_root P n)
    linear_combination (norm := noncomm_ring) this
  · -- {c_k†, c_{-k}†} = 0  (adjoint of {c_k, c_{-k}} = 0)
    have : cCreateK P k * cCreateK P (-k) + cCreateK P (-k) * cCreateK P k = 0 := by
      unfold cCreateK
      rw [← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_mul, ← Matrix.conjTranspose_add,
        add_comm (cAnnihK P (-k) * cAnnihK P k), car_annihK_annihK, Matrix.conjTranspose_zero]
    linear_combination (norm := noncomm_ring) this

/-- The B2 pseudospin operators equal the abstract-kernel forms at the active pair. -/
theorem tauX_eq_kernel (P : ℕ) (n : Fin P) :
    tauX P (waveVectorABC P n)
      = PauliKernel.tX (cAnnihK P (waveVectorABC P n)) (cAnnihK P (-(waveVectorABC P n)))
          (cCreateK P (waveVectorABC P n)) (cCreateK P (-(waveVectorABC P n))) := by
  unfold tauX tauPlus tauMinus PauliKernel.tX
  rfl

theorem tauZ_eq_kernel (P : ℕ) (n : Fin P) :
    tauZ P (waveVectorABC P n)
      = PauliKernel.tZ (cAnnihK P (waveVectorABC P n)) (cAnnihK P (-(waveVectorABC P n)))
          (cCreateK P (waveVectorABC P n)) (cCreateK P (-(waveVectorABC P n))) := by
  unfold tauZ numberOpK PauliKernel.tZ
  rfl

theorem tauY_eq_kernel (P : ℕ) (n : Fin P) :
    tauY P (waveVectorABC P n)
      = (-Complex.I) • PauliKernel.tY (cAnnihK P (waveVectorABC P n))
          (cAnnihK P (-(waveVectorABC P n)))
          (cCreateK P (waveVectorABC P n)) (cCreateK P (-(waveVectorABC P n))) := by
  unfold tauY tauPlus tauMinus PauliKernel.tY
  rfl

/-- The per-mode pseudospin vector as a function `Fin 3 → NQubitOp`,
`(τ^x_k, τ^y_k, τ^z_k)`. -/
def tauVecOp (P : ℕ) (k : ℝ) : Fin 3 → NQubitOp (2*P+2) :=
  ![tauX P k, tauY P k, tauZ P k]

/-- The dotted pseudospin operator `û·τ⃗_k = Σ_a û_a τ^a_k`. -/
def dotTau (P : ℕ) (k : ℝ) (u : Fin 3 → ℝ) : NQubitOp (2*P+2) :=
  ∑ a : Fin 3, (u a : ℂ) • tauVecOp P k a

/-- The pair-block square operator `S_k` (image of `PauliKernel.Spair`), equal to all
three pseudospin squares; on the active subspace it is the pair-block identity. -/
def Spair (P : ℕ) (n : Fin P) : NQubitOp (2*P+2) :=
  PauliKernel.Spair (cAnnihK P (waveVectorABC P n)) (cAnnihK P (-(waveVectorABC P n)))
    (cCreateK P (waveVectorABC P n)) (cCreateK P (-(waveVectorABC P n)))

section TauTable

variable (P : ℕ) (n : Fin P)

private abbrev kn := waveVectorABC P n

theorem tauX_mul_tauX : tauX P (kn P n) * tauX P (kn P n) = Spair P n := by
  rw [tauX_eq_kernel]; exact PauliKernel.tX_sq (carPair P n)
theorem tauY_mul_tauY : tauY P (kn P n) * tauY P (kn P n) = Spair P n := by
  rw [tauY_eq_kernel, smul_mul_smul_comm, PauliKernel.tY_sq_neg (carPair P n)]
  rw [show (-Complex.I) * (-Complex.I) = -1 by
    rw [neg_mul_neg, Complex.I_mul_I]]
  rw [Spair]; module
theorem tauZ_mul_tauZ : tauZ P (kn P n) * tauZ P (kn P n) = Spair P n := by
  rw [tauZ_eq_kernel]; exact PauliKernel.tZ_sq (carPair P n)

theorem tauX_mul_tauY : tauX P (kn P n) * tauY P (kn P n) = Complex.I • tauZ P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel, mul_smul_comm,
    PauliKernel.tX_mul_tY (carPair P n)]
  module
theorem tauY_mul_tauX : tauY P (kn P n) * tauX P (kn P n) = (-Complex.I) • tauZ P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel, smul_mul_assoc,
    PauliKernel.tY_mul_tX (carPair P n)]
theorem tauY_mul_tauZ : tauY P (kn P n) * tauZ P (kn P n) = Complex.I • tauX P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel, smul_mul_assoc,
    PauliKernel.tY_mul_tZ (carPair P n)]
  module
theorem tauZ_mul_tauY : tauZ P (kn P n) * tauY P (kn P n) = (-Complex.I) • tauX P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel, mul_smul_comm,
    PauliKernel.tZ_mul_tY (carPair P n)]
theorem tauZ_mul_tauX : tauZ P (kn P n) * tauX P (kn P n) = Complex.I • tauY P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel,
    PauliKernel.tZ_mul_tX (carPair P n), smul_smul,
    show Complex.I * (-Complex.I) = 1 by rw [mul_neg, Complex.I_mul_I]; ring, one_smul]
theorem tauX_mul_tauZ : tauX P (kn P n) * tauZ P (kn P n) = (-Complex.I) • tauY P (kn P n) := by
  rw [tauX_eq_kernel, tauY_eq_kernel, tauZ_eq_kernel,
    PauliKernel.tX_mul_tZ (carPair P n), smul_smul,
    show (-Complex.I) * (-Complex.I) = -1 by rw [neg_mul_neg, Complex.I_mul_I]]
  module

/-- L3 — the pseudospin Pauli product identity:
`(û·τ⃗_k)(v̂·τ⃗_k) = (û·v̂)·S_k + i (û×v̂)·τ⃗_k`.
NOTE the symmetric (dot-product) part carries the pair-block projector `S_k = Spair P n`,
NOT the identity `1`: the pseudospin algebra closes only on the two-dimensional active
subspace of the `(k,−k)` fermion pair, where `S_k` acts as the unit. -/
theorem pauli_dot_mul_dot (u v : Fin 3 → ℝ) :
    dotTau P (kn P n) u * dotTau P (kn P n) v
      = ((u ⬝ᵥ v : ℝ) : ℂ) • Spair P n
        + Complex.I • dotTau P (kn P n) (u ⨯₃ v) := by
  unfold dotTau
  -- expand the products of the two Fin 3 sums into a double sum
  rw [Finset.sum_mul_sum]
  simp only [smul_mul_smul_comm]
  -- evaluate the 3×3 table; `tauVecOp _ 0/1/2 = tauX/tauY/tauZ`
  simp only [Fin.sum_univ_three, tauVecOp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  rw [tauX_mul_tauX, tauX_mul_tauY, tauX_mul_tauZ,
    tauY_mul_tauX, tauY_mul_tauY, tauY_mul_tauZ,
    tauZ_mul_tauX, tauZ_mul_tauY, tauZ_mul_tauZ]
  rw [cross_apply, dotProduct]
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  -- both sides are ℂ-linear combinations of S_k, tauX, tauY, tauZ; match coefficients
  simp only [smul_smul, smul_add]
  module

end TauTable

end

end QAOA.IsingChain.JordanWigner
