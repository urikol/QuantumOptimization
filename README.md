# QuantumOptimization

A Lean 4 / Mathlib formalization library for results in quantum optimization,
machine-verified down to Lean's trusted kernel.

## Requirements

- [`elan`](https://github.com/leanprover/elan), the Lean toolchain manager. The
  pinned toolchain (`leanprover/lean4:v4.28.0`) is installed automatically from
  `lean-toolchain`; the matching Mathlib revision is pinned in `lake-manifest.json`.

## Build

```bash
lake exe cache get   # fetch prebuilt Mathlib (recommended; large download)
lake build
```

A successful `lake build` exits 0 and compiles the entire library. See
[`ARCHITECTURE.md`](ARCHITECTURE.md) for a map of the library and the structure
of the proof.

## Contents

### The FGG ring-of-disagrees conjecture

A machine-checked proof that depth-$p$ QAOA on the Ising ring (the "ring of
disagrees") attains residual energy exactly $1/(2p+2)$ — equivalently, that the
optimal approximation ratio is exactly $(2p+1)/(2p+2)$ — resolving the
Farhi–Goldstone–Gutmann (FGG) conjecture for this model. Accompanies:

> **A Machine-Verified Proof of a Quantum-Optimization Conjecture**
> Uri Kol, Maor Ben-Shahar, Kfir Sulimany, Dirk Englund
> *(arXiv: TBD)*

The headline theorems, all **axiom-clean** — depending only on `propext`,
`Classical.choice`, `Quot.sound`, with no `sorry`:

| Theorem | Statement | File |
|---|---|---|
| `residualEnergy_lower_bound` | $1/(2p+2) \le$ residual energy, for every $\gamma,\beta$ | `QuantumOptimization/QAOA/IsingChain/UpperBound/ResidualEnergyBound.lean` |
| `residualEnergy_attained` | $\exists\,\gamma,\beta$ attaining $1/(2p+2)$ | `QuantumOptimization/QAOA/IsingChain/Achievability/Tightness.lean` |
| `residualEnergy_isLeast` | $1/(2p+2)$ is the least attainable residual energy | `QuantumOptimization/QAOA/IsingChain/Achievability/Tightness.lean` |
| `residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum`, `epsilonMode_nonneg` | exact per-mode decomposition behind the lower bound | `QuantumOptimization/QAOA/IsingChain/JordanWigner/Decomposition.lean` |

To check axiom cleanliness yourself, add `#print axioms` for any of these to the
relevant file, e.g.

```lean
#print axioms QAOA.IsingChain.Achievability.residualEnergy_isLeast
-- 'QAOA.IsingChain.Achievability.residualEnergy_isLeast' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

Or run the bundled check, which fails on any axiom outside that baseline (in
particular, on `sorry`):

```bash
lake env lean test/AxiomCheck.lean
```

This check and the full build run in CI (`.github/workflows/build.yml`) on
every push.

#### Human audit

`lake build` and the axiom check establish that the proofs are correct and rest
only on the standard foundations. What a machine cannot establish is that the
*formal statements* faithfully encode the intended mathematical claims — that
requires a human reading the statements and the definitions they unfold through
(never the proofs).

That surface is collected in a single file:

```
QuantumOptimization/QAOA/IsingChain/Achievability/HumanAudit/Human_audit_achievability.lean
```

It `#print`s each headline theorem's statement together with every project-local
definition it depends on, and provides a per-item audit checklist with a build
gate (`#audit_gate`) that turns green only when every item has been certified.
Run it standalone with:

```bash
lake env lean QuantumOptimization/QAOA/IsingChain/Achievability/HumanAudit/Human_audit_achievability.lean
```

(Installing the recommended "Highlight" VS Code extension — see `.vscode/` —
colors each certified line green live as you mark it.)

## Authorship

- **Maor Ben-Shahar** — the `Quantum` and `Math` libraries
  (`QuantumOptimization/Quantum/`, `QuantumOptimization/Math/`), providing the
  quantum-mechanical definitions and supporting mathematics.
- **Uri Kol** — everything else, including the QAOA framework, the qubit and
  Ising-model layers, and the FGG ring-of-disagrees proof
  (`QuantumOptimization/QAOA/`, `QuantumOptimization/Qubits/`,
  `QuantumOptimization/IsingModel/`).

## License

Apache License 2.0 — see [LICENSE](LICENSE).
