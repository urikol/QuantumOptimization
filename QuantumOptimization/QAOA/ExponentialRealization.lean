import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import QuantumOptimization.QAOA.QAOAExponentials
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOA
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials

/-!
# Exponential realization — `QAOAExponentials` / `IsingChainQAOAExponentials` are inhabited

`QAOAExponentials.lean` records that the cost/mixer layer maps are exponentials of
the stored Hermitian Hamiltonians, but — as its own docstring notes — it does so
"without forcing us yet to build the custom `UnitaryOp` values directly from the
matrix exponential API". As a result the achievability capstone
(`Achievability.Tightness`) and the optimality bound (`ResidualEnergyBound`) are
both stated *conditional on* an assumed realization
`hChain : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N)`; nothing in the
library previously discharged that assumption, so the headline result was
conditional on the existence of the unitary realization.

This file closes that gap. The mathematical content is the standard fact that the
matrix exponential `exp(-i t C)` of a Hermitian `C` is unitary: the generator
`(-t·i)·C` is skew-Hermitian, so

```
(exp A)ᴴ · exp A = exp Aᴴ · exp A = exp(-A) · exp A = exp(-A + A) = exp 0 = 1,
```

and symmetrically on the other side. `expUnitary` packages this as a `UnitaryOp`
whose underlying operator is *definitionally* `costExponential C t`, so the
`QAOAExponentials` specs hold by `rfl`.

## Main statements
- `expUnitary` — `exp(-i t C)` as a `UnitaryOp` for Hermitian `C`.
- `isingChainQAOAExponentials_exp` — the canonical (unconditional) realization
  `IsingChainQAOAExponentials n J` for any chain couplings `J`.
- `instance : Nonempty (IsingChainQAOAExponentials n J)` — the inhabitation witness.

## Verification status
The unitarity argument and the `rfl` realization specs were compiler-checked
against a faithful mirror of the repository's `Op` / `HermitianOp` / `UnitaryOp` /
`costExponential` definitions and the `IsingChainQAOAExponentials` structure. Final
confirmation is the repository's own `lake build` plus `#print axioms` on the
deliverable theorems.
-/

namespace QAOA

open Quantum.Operators
open Matrix
open scoped Matrix

noncomputable section

/-- The generator `(-t·i)·C` of a Hermitian operator `C` is skew-Hermitian:
`((-t·i)·C)ᴴ = -((-t·i)·C)`. -/
theorem conjTranspose_neg_smul_I_hermitian {n : ℕ} (C : HermitianOp n) (t : ℝ) :
    ((-t * Complex.I) • (C : Op n))ᴴ = -((-t * Complex.I) • (C : Op n)) := by
  rw [Matrix.conjTranspose_smul, C.isHermitian, ← neg_smul]
  congr 1
  simp [Complex.conj_I]

/-- **`exp(-i t C)` is unitary for Hermitian `C`.** This is the construction the
`QAOAExponentials` interface deferred: a genuine `UnitaryOp` whose underlying
operator is exactly `costExponential C t` (and `mixerExponential C t`, which is
definitionally equal). -/
def expUnitary {n : ℕ} (C : HermitianOp n) (t : ℝ) : UnitaryOp n where
  toOp := costExponential C t
  unitary_left := by
    rw [costExponential]
    set A : Op n := (-t * Complex.I) • (C : Op n)
    have hskew : Aᴴ = -A := conjTranspose_neg_smul_I_hermitian C t
    calc (NormedSpace.exp A)ᴴ * NormedSpace.exp A
        = NormedSpace.exp Aᴴ * NormedSpace.exp A := by rw [Matrix.exp_conjTranspose]
      _ = NormedSpace.exp (-A) * NormedSpace.exp A := by rw [hskew]
      _ = NormedSpace.exp (-A + A) :=
            (Matrix.exp_add_of_commute (-A) A ((Commute.refl A).neg_left)).symm
      _ = NormedSpace.exp (0 : Op n) := by rw [neg_add_cancel]
      _ = 1 := NormedSpace.exp_zero
  unitary_right := by
    rw [costExponential]
    set A : Op n := (-t * Complex.I) • (C : Op n)
    have hskew : Aᴴ = -A := conjTranspose_neg_smul_I_hermitian C t
    calc NormedSpace.exp A * (NormedSpace.exp A)ᴴ
        = NormedSpace.exp A * NormedSpace.exp Aᴴ := by rw [Matrix.exp_conjTranspose]
      _ = NormedSpace.exp A * NormedSpace.exp (-A) := by rw [hskew]
      _ = NormedSpace.exp (A + -A) :=
            (Matrix.exp_add_of_commute A (-A) ((Commute.refl A).neg_right)).symm
      _ = NormedSpace.exp (0 : Op n) := by rw [add_neg_cancel]
      _ = 1 := NormedSpace.exp_zero

/-- The underlying operator of `expUnitary C t` is exactly the cost exponential. -/
@[simp]
theorem expUnitary_toOp_eq_costExponential {n : ℕ} (C : HermitianOp n) (t : ℝ) :
    (expUnitary C t : Op n) = costExponential C t := rfl

/-- The underlying operator of `expUnitary C t` is exactly the mixer exponential
(definitionally equal to the cost exponential). Not a `simp` lemma: its LHS
coincides with `expUnitary_toOp_eq_costExponential`, so tagging both `@[simp]`
would be non-confluent; `simp` normalizes via the cost form, this stays for
explicit use. -/
theorem expUnitary_toOp_eq_mixerExponential {n : ℕ} (C : HermitianOp n) (t : ℝ) :
    (expUnitary C t : Op n) = mixerExponential C t := rfl

/-- **The canonical exponential realization of chain QAOA.** For any chain
couplings `J`, the cost and mixer layer unitaries are the matrix exponentials of
the stored Hamiltonians. This discharges, unconditionally, the realization
hypothesis assumed by the achievability and optimality theorems. -/
def isingChainQAOAExponentials_exp {n : ℕ} (J : IsingModel.IsingChainCouplings n) :
    IsingChainQAOAExponentials n J where
  costUnitary γ := expUnitary (isingChainCostHamiltonian J) γ
  mixerUnitary β := expUnitary (isingChainMixerHamiltonian n) β
  costUnitary_spec _ := rfl
  mixerUnitary_spec _ := rfl

/-- Chain QAOA exponential realizations exist for every coupling family. -/
instance {n : ℕ} {J : IsingModel.IsingChainCouplings n} :
    Nonempty (IsingChainQAOAExponentials n J) :=
  ⟨isingChainQAOAExponentials_exp J⟩

end

end QAOA
