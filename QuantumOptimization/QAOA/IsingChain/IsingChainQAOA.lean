import QuantumOptimization.QAOA.QAOAHamiltonians
import QuantumOptimization.QAOA.StandardMixer
import QuantumOptimization.IsingModel.IsingHamiltonian

/-!
# Ising Chain QAOA — cost and mixer Hamiltonians, Hamiltonian packaging

This file packages the periodic 1D Ising chain model for use with the generic
QAOA framework. It identifies the chain Hamiltonian as the cost operator and
the standard transverse-field mixer as the mixer operator, and wraps them into
the `QAOAHamiltonians` interface.

This is the QAOA-on-the-ring-of-disagrees setting analyzed in
Farhi–Goldstone–Gutmann (arXiv:1411.4028, §IV),
Wang–Hadfield–Jiang–Rieffel (arXiv:1706.02998), and
Zhou–Wang–Choi–Pichler–Lukin (arXiv:1812.01041, footnote on $r=(2p+1)/(2p+2)$).

The file keeps the model-specific QAOA layer separate from both the generic
QAOA infrastructure and the stand-alone Ising-model theory, while still making
the chain usable inside the QAOA API.

## Main definitions
- `IsingChainQAOADim`: Hilbert-space dimension `2 ^ n` for the chain on `n` qubits
- `isingChainCostOp`: the chain Hamiltonian viewed as the QAOA cost operator
- `isingChainMixerOp`: the standard mixer `∑ⱼ Xⱼ` on `n` qubits
- `isingChainCostHamiltonian`: Hermitian packaging of the chain cost operator
- `isingChainMixerHamiltonian`: Hermitian packaging of the mixer
- `isingChainQAOAHamiltonians`: the full `QAOAHamiltonians` package for chain QAOA

## Main statements
- `isingChainCostOp_apply_computationalBasisKet`: the cost operator acts diagonally on
  computational-basis kets with eigenvalue given by the classical chain energy
- `isingChainCostOp_eq_diagonal`: the cost operator equals a diagonal matrix of classical energies
-/

namespace QAOA

open Quantum.Operators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section packages the concrete operators that appear in the QAOA
application to the periodic 1D Ising chain.

The cost side is provided by the chain Hamiltonian built from the coupling
data `J`, while the mixer side is the standard QAOA mixer `B = ∑_j X_j` on
the same `n`-qubit Hilbert space.

The definitions are organized in two layers:

* first as plain operators, to keep contact with the underlying Ising-model
  and qubit files, and
* then as Hermitian operators and Hamiltonian packages, which is the level
  used by the generic QAOA interface.
-/

/-- The Hilbert-space dimension used for chain QAOA on `n` spins.

Since the chain is realized on `n` qubits, the underlying Hilbert space has
dimension `2 ^ n`.
-/
abbrev IsingChainQAOADim (n : ℕ) : ℕ := Qubits.NQubitDim n

/-- The cost operator for chain QAOA.

This is exactly the periodic 1D Ising chain Hamiltonian associated with the
coupling data `J`, now viewed as the cost operator in the QAOA application.
-/
def isingChainCostOp {n : ℕ} (J : IsingModel.IsingChainCouplings n) :
    Qubits.NQubitOp n :=
  IsingModel.isingChainHamiltonianOp J

/-- The mixer operator for chain QAOA.

This is the standard QAOA mixer `B = ∑_j X_j` on the `n`-qubit Hilbert space.
-/
def isingChainMixerOp (n : ℕ) : Qubits.NQubitOp n :=
  standardMixerOp n

/-- The cost Hamiltonian for chain QAOA.

This is the chain cost operator packaged as a Hermitian operator, so that it
can be used directly in the Hamiltonian-based QAOA interface.

In other words, `isingChainCostOp` and `isingChainCostHamiltonian` have the
same underlying operator, but `isingChainCostHamiltonian` also carries the
proof that this operator is Hermitian. That additional structure is what the
generic QAOA Hamiltonian layer expects from a valid cost Hamiltonian.
-/
def isingChainCostHamiltonian {n : ℕ} (J : IsingModel.IsingChainCouplings n) :
    Qubits.NQubitHermitianOp n :=
  ⟨isingChainCostOp J, by
    ext ix iy
    change star (isingChainCostOp J iy ix) = isingChainCostOp J ix iy
    by_cases h : ix = iy
    · subst iy
      let z : Qubits.BitString n := (Qubits.bitStringEquiv n).symm ix
      have hz : Qubits.bitStringEquiv n z = ix := by
        simp [z, Qubits.bitStringEquiv]
      have hdiag :=
        congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec ix)
          (IsingModel.isingChainHamiltonianOp_apply_computationalBasisKet J z)
      have hbasis : (Qubits.computationalBasisKet n z).vec ix = 1 := by
        simp [Qubits.computationalBasisKet, hz]
      have hentry :
          isingChainCostOp J ix ix =
            (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ)) := by
        simpa [isingChainCostOp, hz, hbasis] using hdiag
      simp [hentry]
    · let zix : Qubits.BitString n := (Qubits.bitStringEquiv n).symm ix
      let ziy : Qubits.BitString n := (Qubits.bitStringEquiv n).symm iy
      have hix : (Qubits.bitStringEquiv n) zix = ix := by
        simp [zix, Qubits.bitStringEquiv]
      have hiy : (Qubits.bitStringEquiv n) ziy = iy := by
        simp [ziy, Qubits.bitStringEquiv]
      have hentry_ix :
          isingChainCostOp J ix iy =
            (((IsingModel.classicalChainEnergy J ziy : ℝ) : ℂ)) *
              (Qubits.computationalBasisKet n ziy).vec ix := by
        simpa [isingChainCostOp, hiy] using
          congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec ix)
            (IsingModel.isingChainHamiltonianOp_apply_computationalBasisKet J ziy)
      have hentry_iy :
          isingChainCostOp J iy ix =
            (((IsingModel.classicalChainEnergy J zix : ℝ) : ℂ)) *
              (Qubits.computationalBasisKet n zix).vec iy := by
        simpa [isingChainCostOp, hix] using
          congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec iy)
            (IsingModel.isingChainHamiltonianOp_apply_computationalBasisKet J zix)
      have hneq_ix : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 n) ziy = ix := by
        simpa [Qubits.bitStringEquiv, ziy] using Ne.symm h
      have hneq_iy : ¬ (Math.RepresentationTheory.tensorIndexEquiv 2 n) zix = iy := by
        simpa [Qubits.bitStringEquiv, zix] using h
      have hbasis_ix : (Qubits.computationalBasisKet n ziy).vec ix = 0 := by
        simp [Qubits.computationalBasisKet, hneq_ix]
      have hbasis_iy : (Qubits.computationalBasisKet n zix).vec iy = 0 := by
        simp [Qubits.computationalBasisKet, hneq_iy]
      rw [hentry_ix, hentry_iy, hbasis_ix, hbasis_iy]
      simp⟩

/-- The mixer Hamiltonian for chain QAOA.

This is the standard QAOA mixer packaged as a Hermitian operator.
-/
def isingChainMixerHamiltonian (n : ℕ) : Qubits.NQubitHermitianOp n :=
  standardMixerHamiltonian n

/-- Hamiltonian data for chain QAOA.

This packages the chain cost Hamiltonian and the standard mixer Hamiltonian
together with abstract angle-parameterized cost and mixer unitaries on the
same `n`-qubit Hilbert space. It is the chain-specific entry point into the
generic `QAOAHamiltonians` interface.
-/
def isingChainQAOAHamiltonians {n : ℕ} (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n) :
    QAOAHamiltonians (IsingChainQAOADim n) where
  costHamiltonian := isingChainCostHamiltonian J
  mixerHamiltonian := isingChainMixerHamiltonian n
  costUnitary := costUnitary
  mixerUnitary := mixerUnitary

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
These lemmas record that the newly introduced chain-QAOA operators are simply
the model-specific names for the existing chain Hamiltonian and standard
mixer.

They also expose the Hermitian packaging needed to use the chain inside the
generic QAOA API.
-/

/-- The chain-QAOA cost operator is definitionally the chain Hamiltonian. -/
@[simp]
theorem isingChainCostOp_eq_isingChainHamiltonianOp {n : ℕ}
    (J : IsingModel.IsingChainCouplings n) :
    isingChainCostOp J = IsingModel.isingChainHamiltonianOp J := rfl

/-- The chain-QAOA mixer operator is definitionally the standard QAOA mixer. -/
@[simp]
theorem isingChainMixerOp_eq_standardMixerOp {n : ℕ} :
    isingChainMixerOp n = standardMixerOp n := rfl

/-- The chain-QAOA mixer Hamiltonian is definitionally the standard mixer
Hamiltonian. -/
@[simp]
theorem isingChainMixerHamiltonian_eq_standardMixerHamiltonian {n : ℕ} :
    isingChainMixerHamiltonian n = standardMixerHamiltonian n := rfl

/-- The chain-QAOA cost operator acts diagonally on computational-basis kets,
with eigenvalue given by the classical chain energy of the corresponding
bitstring.

This is just the diagonalization theorem for the chain Hamiltonian restated
using the application-specific name `isingChainCostOp`.
-/
theorem isingChainCostOp_apply_computationalBasisKet {n : ℕ}
    (J : IsingModel.IsingChainCouplings n) (z : Qubits.BitString n) :
    isingChainCostOp J * Qubits.computationalBasisKet n z =
      (((IsingModel.classicalChainEnergy J z : ℝ) : ℂ)) •
        Qubits.computationalBasisKet n z := by
  simpa [isingChainCostOp] using
    IsingModel.isingChainHamiltonianOp_apply_computationalBasisKet J z

/-- The chain-QAOA cost operator is diagonal in the computational basis.

The diagonal entry indexed by `ix` is the classical chain energy of the
bitstring corresponding to `ix` under `Qubits.bitStringEquiv n`.
-/
theorem isingChainCostOp_eq_diagonal {n : ℕ}
    (J : IsingModel.IsingChainCouplings n) :
    isingChainCostOp J =
      Matrix.diagonal (fun ix =>
        (((IsingModel.classicalChainEnergy J
            ((Qubits.bitStringEquiv n).symm ix) : ℝ) : ℂ))) := by
  ext ix iy
  by_cases h : ix = iy
  · subst iy
    let z : Qubits.BitString n := (Qubits.bitStringEquiv n).symm ix
    have hdiag :=
      congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec ix)
        (isingChainCostOp_apply_computationalBasisKet J z)
    have hbasis : (Qubits.computationalBasisKet n z).vec ix = 1 := by
      simp [Qubits.computationalBasisKet, z, Qubits.bitStringEquiv]
    simpa [Matrix.diagonal_apply_eq, z, hbasis] using hdiag
  · let z : Qubits.BitString n := (Qubits.bitStringEquiv n).symm iy
    have hoff :=
      congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec ix)
        (isingChainCostOp_apply_computationalBasisKet J z)
    have hbasis : (Qubits.computationalBasisKet n z).vec ix = 0 := by
      have hneq : Qubits.bitStringEquiv n z ≠ ix := by
        simpa [z, Qubits.bitStringEquiv] using Ne.symm h
      have hneq' : (Math.RepresentationTheory.tensorIndexEquiv 2 n) z ≠ ix := by
        simpa [Qubits.bitStringEquiv, z] using hneq
      simp [Qubits.computationalBasisKet, hneq']
    simpa [Matrix.diagonal_apply_ne _ h, z, hbasis] using hoff

/-- The underlying operator of the chain cost Hamiltonian is the chain cost
operator. -/
@[simp]
theorem isingChainCostHamiltonian_toOp {n : ℕ}
    (J : IsingModel.IsingChainCouplings n) :
    (isingChainCostHamiltonian J : Qubits.NQubitOp n) = isingChainCostOp J := rfl

/-- The underlying operator of the chain mixer Hamiltonian is the chain mixer
operator. -/
@[simp]
theorem isingChainMixerHamiltonian_toOp {n : ℕ} :
    (isingChainMixerHamiltonian n : Qubits.NQubitOp n) = isingChainMixerOp n := rfl

/-- The cost Hamiltonian field of `isingChainQAOAHamiltonians` is the packaged
chain cost Hamiltonian. -/
@[simp]
theorem isingChainQAOAHamiltonians_costHamiltonian {n : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n) :
    (isingChainQAOAHamiltonians J costUnitary mixerUnitary).costHamiltonian =
      isingChainCostHamiltonian J := rfl

/-- The mixer Hamiltonian field of `isingChainQAOAHamiltonians` is the packaged
standard mixer Hamiltonian. -/
@[simp]
theorem isingChainQAOAHamiltonians_mixerHamiltonian {n : ℕ}
    (J : IsingModel.IsingChainCouplings n)
    (costUnitary mixerUnitary : ℝ → Qubits.NQubitUnitaryOp n) :
    (isingChainQAOAHamiltonians J costUnitary mixerUnitary).mixerHamiltonian =
      isingChainMixerHamiltonian n := rfl

end

end QAOA
