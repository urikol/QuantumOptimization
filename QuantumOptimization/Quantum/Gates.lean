import QuantumOptimization.Quantum.Operators.BraKet
-- Re-exported so downstream files keep transitive access to TensorProducts.
import QuantumOptimization.Quantum.TensorProducts.PartialTrace

/-!
# Quantum Gates — Pauli operators

The single-qubit Pauli gates `pauliX`, `pauliY`, `pauliZ` (notations `X`, `Y`,
`Z`) and the Hermiticity of `X` and `Z`.
-/

namespace Quantum.Gates

open Quantum.Operators
open scoped Matrix BigOperators ComplexConjugate ComplexOrder
open Matrix

noncomputable section

/-- Pauli X gate (NOT gate): |0⟩ ↔ |1⟩ -/
def pauliX : Op 2 := |1⟩ * ⟨0| + |0⟩ * ⟨1|

/-- Pauli Y gate -/
def pauliY : Op 2 := Complex.I • (|1⟩ * ⟨0|) - Complex.I • (|0⟩ * ⟨1|)

/-- Pauli Z gate (phase flip): |0⟩ → |0⟩, |1⟩ → -|1⟩ -/
def pauliZ : Op 2 := |0⟩ * ⟨0| - |1⟩ * ⟨1|

notation "X" => pauliX
notation "Y" => pauliY
notation "Z" => pauliZ

/-- Pauli X is Hermitian: X† = X -/
@[simp]
theorem pauliX_hermitian : X† = X := by
  unfold pauliX
  qisimp_basic
  abel

/-- Pauli Z is Hermitian: Z† = Z -/
@[simp]
theorem pauliZ_hermitian : Z† = Z := by
  unfold pauliZ
  qisimp_basic

end

end Quantum.Gates
