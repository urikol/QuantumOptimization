# Architecture

A map of the library and the structure of the FGG ring-of-disagrees proof.
All source lives under `QuantumOptimization/`; the root file
`QuantumOptimization.lean` imports every module (the library manifest).

## Foundations

| Directory | Contents |
|---|---|
| `Quantum/` | Core operator objects: `Op`/`Bra`/`Ket`/`UnitaryOp`/`HermitianOp` (`Operators/`), inner products and braket algebra (`Operators/BraKet`), Pauli gates (`Gates`), tensor products and partial trace (`TensorProducts/`). |
| `Qubits/` | The $n$-qubit space `NQubitSpace`, single-qubit Pauli operators lifted to a site (`PauliOperators`, `LocalOperators`). |
| `Math/` | Supporting mathematics: spectral theory, submodule dimension, the permutation/tensor-index equivalence (`RepresentationTheory`). |
| `IsingModel/` | The cost Hamiltonian $H_C = \sum_k J_k Z_k Z_{k+1}$ on the periodic ring (`IsingHamiltonian`) and its expectation observables (`IsingObservables`). |
| `QAOA/` | The depth-$p$ QAOA framework: layered state (`QAOAState`), cost/mixer Hamiltonians and their exponentials (`QAOAHamiltonians`, `QAOAExponentials`, `ExponentialRealization`), and the standard mixer/circuit (`StandardMixer`, `StandardQAOA`). |

## The FGG proof — `QAOA/IsingChain/`

The model setup (`IsingChainQAOA`, `IsingChainQAOAState`,
`IsingChainQAOAExponentials`, `IsingChainQAOAObservables`) fixes the
ring-of-disagrees instance. The result then splits into three independent
tracks, combined in `Achievability/Tightness.lean`.

### 1. Lower bound — `UpperBound/`

That depth-$p$ QAOA cannot beat residual energy $1/(2p+2)$ for *any* angles.
Proved via the Farhi–Goldstone–Gutmann light-cone reduction: a bond's
expectation depends only on a bounded neighborhood, so the periodic ring reduces
to a finite open chain whose energy is bounded by an elementary variational
argument.

- `LightCone/` — the locality/reduction machinery (light-cone spreading, window
  blocks, ABC↔PBC bridge, canonical matching).
- `ReducedChain`, `TranslationOperators`, `ABCInvariance`, `GroundStateEnergy` —
  the reduced-chain spectrum.
- **`ResidualEnergyBound.lean`** → `residualEnergy_lower_bound`.

### 2. Exact per-mode decomposition — `JordanWigner/`

Rewrites the residual energy as a closed-form sum over momentum modes.

- `Transformation/` — the Jordan–Wigner map (Pauli algebra → fermionic image of
  $H_C$).
- `MomentumModes/` — diagonalization into decoupled momentum modes (active
  subspace, cost decomposition, parity, spectral reflection).
- `PseudospinDynamics/` — each mode as an SU(2)/SO(3) pseudospin; Rodrigues
  rotation and the per-mode dynamics.
- **`Decomposition.lean`** → `residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum`
  and `epsilonMode_nonneg` (every mode's contribution is non-negative — the
  decomposition behind the lower bound).

### 3. Achievability — `Achievability/`

That the bound is *attained*: explicit angles reach $1/(2p+2)$. Built by quantum
signal processing — the per-mode response is engineered through a
Fejér–Riesz spectral factorization and a Haah-style angle-extraction.

- `AlternatingPoly`, `ComplementRoots`, `RootSplit`, `Factorization` —
  Fejér–Riesz / complementary-polynomial construction.
- `Su2Class`, `BlochBridge`, `Realization`, `Angles`, `SinBound` — mapping the
  factorization back to QAOA angles.
- **`Tightness.lean`** → `residualEnergy_attained` and, combining tracks 1 and 3,
  `residualEnergy_isLeast` (so the optimal ratio is exactly $(2p+1)/(2p+2)$).

### Human audit — `Achievability/HumanAudit/`

`AuditHarness.lean` defines the `#auditPrint`/`#audit_gate` commands;
`Human_audit_achievability.lean` is the single-file surface a human certifies
(statements + the definitions they unfold through). See the README's
"Human audit" section.
