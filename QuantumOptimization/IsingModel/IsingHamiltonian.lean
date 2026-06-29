import QuantumOptimization.Qubits.PauliOperators
import QuantumOptimization.Quantum.Operators.BraKet
import QuantumOptimization.Quantum.Gates

/-!
# 1D Ising Chain Hamiltonian — periodic ring, classical energy, operator diagonalization

This file defines the one-dimensional Ising chain with periodic boundary
conditions, as it appears in the analyses of QAOA on the "ring of disagrees"
in Farhi–Goldstone–Gutmann (arXiv:1411.4028), Wang–Hadfield–Jiang–Rieffel
(arXiv:1706.02998), and Zhou–Wang–Choi–Pichler–Lukin (arXiv:1812.01041).

Concretely, the file introduces:

* a type of chain coupling data, consisting of one real coupling per edge
  on the ring,
* the cyclic next-site operation `nextSite : Fin n → Fin n` realizing the
  periodic boundary,
* the classical spin and energy functions on computational-basis bitstrings,
  and
* the corresponding operator-valued Hamiltonian built from local Pauli `Z`
  operators.

The main structural result proved here is that the resulting Hamiltonian is
diagonal in the computational basis, with eigenvalues given by the classical
Ising chain energies of the corresponding bitstrings. The unweighted
antiferromagnetic ring (the "ring of disagrees") is the special case
`J k = 1`.

## Main definitions
- `IsingChainCouplings`: coupling data for the periodic 1D Ising chain
- `nextSite`: cyclic next-site map `k ↦ (k + 1) mod n`
- `spinValue`: classical spin value `±1` attached to a computational-basis bit
- `classicalSpin`: classical spin value of site `i` in a bitstring
- `chainPairInteraction`: nearest-neighbour pair operator `Z_k Z_{k+1}`
- `classicalChainEnergy`: classical Ising-chain energy of a bitstring
- `isingChainHamiltonianOp`: 1D Ising chain Hamiltonian on `n` qubits

## Main statements
- `chainPairInteraction_apply_computationalBasisKet`: diagonality of a single
  pair interaction in the computational basis
- `isingChainHamiltonianOp_apply_computationalBasisKet`: diagonality of the
  full Hamiltonian, with eigenvalues equal to `classicalChainEnergy`
- `pauliZ_diag_eq_spinValue`: Pauli `Z` diagonal entries equal classical
  spin values
- `nextSite_val`: explicit formula `(nextSite k).val = (k.val + 1) % n`
-/

namespace IsingModel

open Quantum.Operators
open Quantum.Gates
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Definitions
-- ============================================================================

/-!
This section introduces the coupling data for the periodic 1D Ising chain,
the cyclic next-site map, the classical spin and energy functions, and the
corresponding pair-interaction and Hamiltonian operators.

The definitions are organized so that the classical and operator pictures can
be compared directly later in the file. The classical side is encoded by
`spinValue`, `classicalSpin`, and `classicalChainEnergy`, while the quantum
side is encoded by `chainPairInteraction` and `isingChainHamiltonianOp`.
-/

/-- Coupling data for a periodic 1D Ising chain on `n` sites.

For `k : Fin n`, the field `J k` is the coupling constant on the edge
connecting site `k` to site `(k + 1) mod n`. With `n` sites and periodic
boundary conditions, the chain therefore carries exactly `n` edges.

The unweighted antiferromagnetic ring (the "ring of disagrees" of
Farhi–Goldstone–Gutmann) is the special case `J k = 1` for all `k`. The
weighted variants studied in Zhou et al. correspond to general real-valued
`J`.
-/
structure IsingChainCouplings (n : ℕ) where
  J : Fin n → ℝ

/-- The cyclic next-site index on the periodic ring: `nextSite k = (k+1) mod n`.

This is the operator-level realization of the periodic boundary condition
`σ^z_{n+1} = σ^z_1` used throughout the QAOA literature on the ring of
disagrees.
-/
def nextSite {n : ℕ} (k : Fin n) : Fin n :=
  ⟨(k.val + 1) % n, Nat.mod_lt _ (lt_of_le_of_lt (Nat.zero_le _) k.isLt)⟩

/-- The local two-spin nearest-neighbour interaction `Z_k Z_{(k+1) mod n}` on
the periodic chain.

Implemented as the product of the local Pauli `Z` operators acting on qubits
`k` and `nextSite k`. Since each local Pauli `Z` is diagonal in the
computational basis, this interaction is diagonal as well.

These pair interactions are the basic building blocks of the full chain
Hamiltonian.
-/
def chainPairInteraction {n : ℕ} (k : Fin n) : Qubits.NQubitOp n :=
  Qubits.localPauliZ k * Qubits.localPauliZ (nextSite k)

/-- The classical spin value attached to a computational-basis bit.

We use the standard convention

* bit `0` corresponds to spin `+1`,
* bit `1` corresponds to spin `-1`.

This convention is chosen so that the eigenvalues of the Pauli `Z` operator on
computational-basis states agree with the associated classical spin values.
-/
def spinValue (b : Fin 2) : ℝ :=
  if b = 0 then 1 else -1

/-- The classical spin value of site `i` in a computational-basis bitstring.

If `z : Qubits.BitString n` is viewed as a classical spin configuration in the
computational basis, then `classicalSpin z i` is the corresponding `±1` spin
at site `i`.
-/
def classicalSpin {n : ℕ} (z : Qubits.BitString n) (i : Fin n) : ℝ :=
  spinValue (z i)

/-- The classical Ising-chain energy of a computational-basis bitstring on
the periodic ring.

For coupling data `J` and a configuration `z`, this is the classical energy
\[
  E_J(z) = \sum_{k} J_k\, z_k\, z_{k+1\,\mathrm{mod}\,n},
\]
with each `z_k` interpreted through `classicalSpin z k`.

This definition is chosen to match exactly the eigenvalue of the operator
Hamiltonian `isingChainHamiltonianOp J` on the basis ket `|z⟩`.
-/
def classicalChainEnergy {n : ℕ} (J : IsingChainCouplings n)
    (z : Qubits.BitString n) : ℝ :=
  ∑ k : Fin n, J.J k * classicalSpin z k * classicalSpin z (nextSite k)

/-- The 1D Ising chain Hamiltonian on `n` qubits with periodic boundary:
\[
  H_C = \sum_{k=0}^{n-1} J_k\, Z_k\, Z_{(k+1) \bmod n}.
\]

The Hamiltonian is written entirely in terms of local Pauli `Z` operators, so
it is manifestly diagonal in the computational basis. The
diagonalization theorems below make that diagonal structure explicit and
identify its eigenvalues with the classical energies defined by
`classicalChainEnergy`.

This matches the definition of the cost Hamiltonian for the ring of disagrees
used in Farhi–Goldstone–Gutmann (arXiv:1411.4028, §IV) and in
Wang–Hadfield–Jiang–Rieffel (arXiv:1706.02998, eq. (H1)).
-/
def isingChainHamiltonianOp {n : ℕ} (J : IsingChainCouplings n) :
    Qubits.NQubitOp n :=
  ∑ k : Fin n, ((J.J k : ℝ) : ℂ) • chainPairInteraction k

-- ============================================================================
-- Section: Theorems
-- ============================================================================

/-!
The first group of theorems concerns the cyclic next-site map and the `±1`
interpretation of computational-basis bits. The second group establishes the
diagonalization of the chain Hamiltonian in the computational basis.
-/

/-- Explicit formula for the underlying `Nat` value of `nextSite`. -/
@[simp]
theorem nextSite_val {n : ℕ} (k : Fin n) :
    (nextSite k).val = (k.val + 1) % n := rfl

/-- The classical spin value of the computational-basis bit `0` is `+1`. -/
@[simp]
theorem spinValue_zero :
    spinValue (0 : Fin 2) = 1 := by
  simp [spinValue]

/-- The classical spin value of the computational-basis bit `1` is `-1`. -/
@[simp]
theorem spinValue_one :
    spinValue (1 : Fin 2) = -1 := by
  simp [spinValue]

/-- The diagonal entry of `Z` on a computational-basis bit equals the
corresponding classical spin value.

This is the bridge between the operator language and the classical Ising
energy function: the eigenvalues of the one-qubit Pauli `Z` operator are
exactly the classical spin values attached to the corresponding
computational-basis bits.
-/
@[simp]
theorem pauliZ_diag_eq_spinValue (b : Fin 2) :
    Z b b = ((spinValue b : ℝ) : ℂ) := by
  fin_cases b <;> simp [spinValue, pauliZ]

-- --------------------------------------------------------------------------
-- Subsection: Diagonalization In The Computational Basis
-- --------------------------------------------------------------------------

/-!
This subsection proves that the 1D Ising chain Hamiltonian is diagonal in the
computational basis with eigenvalues equal to the classical Ising-chain
energies of the corresponding bitstrings.

The proof is organized in the expected order:

* first prove the diagonal action of a single pair interaction `Z_k Z_{k+1}`,
* then rewrite that action in coordinate form,
* and finally sum these contributions to obtain the full chain Hamiltonian.
-/

/-- A nearest-neighbour pair interaction acts diagonally on a
computational-basis ket, with eigenvalue equal to the product of the two
classical spin values.

This is the two-site analog of the fact that a single Pauli `Z` acts
diagonally on computational-basis states. It identifies the basis ket `|z⟩`
as an eigenvector of `Z_k Z_{(k+1) mod n}`, with eigenvalue
`classicalSpin z k * classicalSpin z (nextSite k)`.
-/
theorem chainPairInteraction_apply_computationalBasisKet {n : ℕ} (k : Fin n)
    (z : Qubits.BitString n) :
    chainPairInteraction k * Qubits.computationalBasisKet n z =
      ((((classicalSpin z k * classicalSpin z (nextSite k) : ℝ)) : ℂ)) •
        Qubits.computationalBasisKet n z := by
  unfold chainPairInteraction
  rw [op_mul_op_mul_ket]
  rw [Qubits.localPauliZ_on_basis (j := nextSite k) (z := z)]
  rw [op_mul_smul_ket]
  rw [Qubits.localPauliZ_on_basis (j := k) (z := z)]
  simp [mul_comm, classicalSpin, pauliZ_diag_eq_spinValue]

/-- Matrix-entry form of the pair interaction on a computational-basis column.

This is the coordinate version of
`chainPairInteraction_apply_computationalBasisKet`. It is useful inside the
proof of the full Hamiltonian theorem, where one works componentwise after
expanding the sum defining `isingChainHamiltonianOp`.
-/
theorem chainPairInteraction_entry_on_computationalBasis {n : ℕ} (k : Fin n)
    (z : Qubits.BitString n) (iy : Fin (Qubits.NQubitDim n)) :
    chainPairInteraction k iy (Qubits.bitStringEquiv n z) =
      (((classicalSpin z k * classicalSpin z (nextSite k) : ℝ) : ℂ)) *
        (Qubits.computationalBasisKet n z).vec iy := by
  have h :=
    congrArg (fun ψ : Qubits.NQubitKet n => ψ.vec iy)
      (chainPairInteraction_apply_computationalBasisKet (k := k) (z := z))
  simpa using h

/-- Entry-free expansion of the chain Hamiltonian definition.

This theorem is definitional, but is convenient as a named rewrite rule. It
lets later proofs unfold the Hamiltonian into its sum of weighted pair
interactions without manually expanding the definition each time.
-/
@[simp]
theorem isingChainHamiltonianOp_eq_sum {n : ℕ} (J : IsingChainCouplings n) :
    isingChainHamiltonianOp J =
      ∑ k : Fin n, ((J.J k : ℝ) : ℂ) • chainPairInteraction k := rfl

/-- The 1D Ising chain Hamiltonian acts diagonally on a computational-basis
ket, with eigenvalue given by the classical chain energy of the corresponding
bitstring.

This is the main theorem of the file. It shows that the operator-level
definition `isingChainHamiltonianOp J` really realizes the classical Ising
chain: computational-basis states are eigenvectors, and their eigenvalues are
exactly the numbers computed by `classicalChainEnergy J`.

Equivalently, the theorem identifies the computational basis as an eigenbasis
of the chain Hamiltonian and identifies the corresponding spectrum pointwise
with the classical energy landscape.
-/
theorem isingChainHamiltonianOp_apply_computationalBasisKet {n : ℕ}
    (J : IsingChainCouplings n) (z : Qubits.BitString n) :
    isingChainHamiltonianOp J * Qubits.computationalBasisKet n z =
      (((classicalChainEnergy J z : ℝ) : ℂ)) • Qubits.computationalBasisKet n z := by
  ext iy
  rw [isingChainHamiltonianOp_eq_sum]
  simp only [sum_op_mul_ket_vec, smul_op_mul_ket,
    Quantum.TensorProducts.Ket.smul_vec_apply,
    Qubits.op_mul_computationalBasisKet_vec]
  by_cases hiy : Qubits.bitStringEquiv n z = iy
  · subst iy
    have hbasis :
        (Qubits.computationalBasisKet n z).vec (Qubits.bitStringEquiv n z) = 1 := by
      simp [Qubits.computationalBasisKet]
    have hpair :
        ∀ k : Fin n,
          chainPairInteraction k
              (Math.RepresentationTheory.tensorIndexEquiv 2 n z)
              (Math.RepresentationTheory.tensorIndexEquiv 2 n z) =
            (((classicalSpin z k * classicalSpin z (nextSite k) : ℝ) : ℂ)) *
              (Qubits.computationalBasisKet n z).vec
                (Qubits.bitStringEquiv n z) := by
      intro k
      simpa [Qubits.bitStringEquiv] using
        (chainPairInteraction_entry_on_computationalBasis (k := k) (z := z)
          (iy := Qubits.bitStringEquiv n z))
    have hsum :
        ∑ k : Fin n,
            ((J.J k : ℝ) : ℂ) *
              chainPairInteraction k
                (Math.RepresentationTheory.tensorIndexEquiv 2 n z)
                (Math.RepresentationTheory.tensorIndexEquiv 2 n z) =
          ∑ k : Fin n,
            ((J.J k : ℝ) : ℂ) *
              ((((classicalSpin z k * classicalSpin z (nextSite k) : ℝ) : ℂ)) * 1) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hpair k, hbasis]
    rw [hbasis]
    simpa [Qubits.bitStringEquiv, classicalChainEnergy, Complex.ofReal_sum,
      Complex.ofReal_mul, mul_assoc, mul_left_comm, mul_comm] using hsum
  · have hneq : (Math.RepresentationTheory.tensorIndexEquiv 2 n) z ≠ iy := by
      simpa [Qubits.bitStringEquiv] using hiy
    have hbasis : (Qubits.computationalBasisKet n z).vec iy = 0 := by
      simp [Qubits.computationalBasisKet, hneq]
    have hpair :
        ∀ k : Fin n,
          chainPairInteraction k iy (Qubits.bitStringEquiv n z) =
            (((classicalSpin z k * classicalSpin z (nextSite k) : ℝ) : ℂ)) *
              (Qubits.computationalBasisKet n z).vec iy := by
      intro k
      exact chainPairInteraction_entry_on_computationalBasis (k := k) (z := z) (iy := iy)
    have hsum :
        ∑ k : Fin n,
            ((J.J k : ℝ) : ℂ) *
              chainPairInteraction k iy (Qubits.bitStringEquiv n z) =
          ∑ k : Fin n, ((J.J k : ℝ) : ℂ) * 0 := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hpair k, hbasis]
      simp
    rw [hsum]
    simp [hbasis]

end

end IsingModel
