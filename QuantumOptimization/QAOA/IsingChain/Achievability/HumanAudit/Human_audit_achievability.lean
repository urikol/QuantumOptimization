import QuantumOptimization.QAOA.IsingChain.Achievability.Tightness
import QuantumOptimization.QAOA.IsingChain.Achievability.HumanAudit.AuditHarness

/-!
# Statement-level human-audit interface for THE MAIN THEOREMS

This is the surface a human must certify for the three main theorems of the paper — the
lower bound `residualEnergy_lower_bound`, the achievability theorem `residualEnergy_attained`,
and the optimality theorem `residualEnergy_isLeast` — together with every project-local
definition their statements unfold through. (The `#auditPrint`/`#audit_gate` commands used below
are defined in the companion `AuditHarness` module.)

## Why only this file needs a human

A formalized theorem is trustworthy when three things hold:

1. it **type-checks** against Lean's small trusted kernel;
2. an **axiom audit** (`#print axioms`) confirms it rests only on the accepted foundations,
   with no `sorry` — all three theorems pass with `{propext, Classical.choice,
   Quot.sound}`;
3. the **formal statement faithfully encodes the intended mathematical claim**.

Steps 1–2 are mechanical: Lean performs them with no appeal to human judgement. Only step 3
needs a person — and it requires reading *only the statement and the definitions it refers
to*, never the proof. That surface is exactly what this file collects.

How to read it:

- The **target under audit** and every **supporting definition** are `#print`ed, emitting
  the *real, authoritative declaration* from the library (not a transcription that could
  drift). Open the Lean infoview **"All Messages"** to read everything in file order (grouped
  by source file: IsingModel → QAOA.IsingChain → QAOA → Qubits → Quantum → Math), or read each
  `#print` line's inline message. For the target theorems the proof term is
  collapsed to `⋯` (via `pp.proofs false`), so `#print` displays only their **statements** —
  the thing you audit. (The proof's correctness is established mechanically elsewhere — the
  library build and the axiom audit, per "Why only this file needs a human" above — not by
  anything in this harness.)

- `#print` shows a definition's *type and body* but not its source doc-comment. For the
  library's prose explanation of a name, hover it in the editor, or open the module named in
  the `-- From …` header above each group.

- Each line pairs `#print <name>` with **`#auditPrint`** (from `AuditHarness`). With the cursor
  on a line, the infoview panel lists the *audited declarations* `<name>` references — i.e.
  those that have their own `#print` line below — each with a green ✓ (its line is `[x]`) or
  red ✗ (not yet), and each a click-link to that line. So you can see at a glance whether
  everything a definition depends on is already audited, and jump to anything that isn't.
  (Names without their own `#print` line — e.g. auto-generated projections like `NormKet.toKet`
  — are not listed; auditing the declaration they belong to covers them.)

## What you are certifying

For the **targets** — that, under the stated hypotheses (`N` even, `2P+2 ≤ N`), each statement
really says what it claims about depth-`P` QAOA on the ring of disagrees, nothing weaker or
vacuous:
- `residualEnergy_lower_bound`: `1/(2P+2) ≤ residualEnergy … ` for *every* `γ, β` — no choice
  of angles beats residual energy `1/(2P+2)`;
- `residualEnergy_attained`: `∃ γ β, residualEnergy … = 1/(2P+2)` — that value *is* reached;
- `residualEnergy_isLeast`: `IsLeast {e | ∃ γ β, residualEnergy … = e} (1/(2P+2))` — `1/(2P+2)`
  is the *least* attainable residual energy (the conjunction of the two above), so the optimal
  approximation ratio is exactly `(2P+1)/(2P+2)`.

For each **definition** — that its body matches the standard meaning of its name. Spot-checks
worth making: `ringOfDisagreesCouplings` is the uniform `J ≡ 1`; the cost Hamiltonian is
`∑_k J_k Z_k Z_{k+1}` and the mixer is `∑_j X_j`; `residualEnergy` normalizes by the
`[E_min, E_max] = [-n, n]` span as `⟨H_C⟩.re / (2n) + 1/2`; and the reducible type synonyms
(`NQubitOp`, `Op`, …) collapse to the expected matrix types.

## Audit marks  (flip as you review each item)

```
-- [ ]   not yet audited                         (blocks the gate)
-- [x]   audited and faithful — CLEARS the gate   (optionally add note: `-- [x] initials YYYY-MM-DD`)
-- [!]   audited, needs discussion                (still blocks the gate — resolve, then -> [x])
```

Only `[x]` clears an item; both `[ ]` and `[!]` keep the gate red.

To mark an item, just type the `x` into its `[ ]`. With the **Highlight** VS Code extension
installed (recommended in `.vscode/extensions.json`; config in `.vscode/settings.json`), the
line turns **green** the instant you add the `x` — `[!]` lines turn amber — with no save or
rebuild. The coloring is purely cosmetic; the authoritative check remains the build gate.

Progress, from the project root:

```
F=QuantumOptimization/QAOA/IsingChain/Achievability/HumanAudit/Human_audit_achievability.lean
grep -cE '^#print .*\[x\]' "$F"   # done       (anchored to item lines, so the legend above
grep -E  '^#print .*\[ \]' "$F"   # remaining   isn't miscounted)
```

**Build gate.** The `#audit_gate` command at the bottom of the file errors while any item in
the audit region is still unaudited or flagged for discussion (only an audited mark clears an
item), so a *green* build (no error) certifies a *complete* audit.
It reads the source being elaborated (`getFileMap.source`) — the **live editor buffer** — so
the count updates the instant you type a mark, with no save or restart; it works identically
under `lake env lean`. It is intentionally not wired into `QuantumOptimization.lean`; for a CLI/CI check
run `lake env lean QuantumOptimization/QAOA/IsingChain/Achievability/HumanAudit/Human_audit_achievability.lean`.
-/

open QAOA QAOA.IsingChain Quantum.Operators Qubits IsingModel

-- `#auditPrint` / `#audit_gate` come from `AuditHarness`;
-- the lines below pair `#print` with `#auditPrint`.


-- Silence Mathlib's linters that forbid `#`-commands and off-column commands.
set_option linter.hashCommand false
set_option linter.style.whitespace false




-- AUDIT-REGION-START  (the gate scans only between these sentinels)





-- ════════════════════ Target declarations (under audit) ════════════════════
-- The three main theorems of the paper, for the ring of disagrees with `N` even and
-- `2P+2 ≤ N`. Together they pin the optimal performance of depth-`P` QAOA exactly:
--
--   • **Lower bound** (`residualEnergy_lower_bound`): every `γ, β` gives
--     `residualEnergy (ringQAOA N) γ β ≥ 1/(2P+2)`.
--   • **Achievability** (`residualEnergy_attained`): there exist angle families `γ, β`
--     with `residualEnergy (ringQAOA N) γ β = 1/(2P+2)` — the saturation half of the
--     Farhi–Goldstone–Gutmann ring-of-disagrees conjecture.
--   • **Optimality** (`residualEnergy_isLeast`): `1/(2P+2)` is the *least* attainable
--     residual energy — the conjunction of the two above (`IsLeast`) — i.e. the optimal
--     approximation ratio is exactly `(2P+1)/(2P+2)`.
--
-- `#print` shows each real statement; `pp.proofs false` collapses the proof term to `⋯`, so
-- only the statement (the thing you audit) is displayed.

-- From QAOA.IsingChain.UpperBound.ResidualEnergyBound
set_option pp.proofs false in
#print QAOA.IsingChain.residualEnergy_lower_bound              #auditPrint   -- 1/(2P+2) ≤ e_res ∀ γ β                      -- [x]

-- From QAOA.IsingChain.Achievability.Tightness
set_option pp.proofs false in
#print QAOA.IsingChain.Achievability.residualEnergy_attained   #auditPrint   -- ∃ γ β, e_res = 1/(2P+2)                     -- [x]
set_option pp.proofs false in
#print QAOA.IsingChain.Achievability.residualEnergy_isLeast    #auditPrint   -- IsLeast {e_res} (1/(2P+2))                  -- [x]





-- ════════════════════ Required context (real definition bodies) ════════════════════
-- Each `#print` dumps the genuine library definition. Read them in "All Messages".

-- ── 1. IsingModel ─────────────────────────────────────────────

-- From IsingModel.IsingHamiltonian
#print IsingModel.IsingChainCouplings                #auditPrint   -- coupling data J : Fin n → ℝ on the periodic ring      -- [x]
#print IsingModel.nextSite                           #auditPrint   -- cyclic next-site index (k+1) mod n                    -- [x]
#print IsingModel.chainPairInteraction               #auditPrint   -- local Z_k Z_{(k+1) mod n}                             -- [x]
#print IsingModel.isingChainHamiltonianOp            #auditPrint   -- H_C = ∑ J_k Z_k Z_{k+1}                               -- [x]

-- From IsingModel.IsingObservables
#print IsingModel.chainFirstMoment                   #auditPrint   -- ⟨ψ|H_C|ψ⟩                                             -- [x]

-- ── 2. QAOA.IsingChain ────────────────────────────────────────

-- From QAOA.IsingChain.UpperBound.ReducedChain
#print QAOA.IsingChain.ringOfDisagreesCouplings      #auditPrint   -- the uniform J ≡ 1 ring                                -- [x]

-- From QAOA.IsingChain.IsingChainQAOA
#print QAOA.IsingChainQAOADim                        #auditPrint                                                            -- [x]
#print QAOA.isingChainMixerHamiltonian               #auditPrint                                                            -- [x]
#print QAOA.isingChainCostOp                         #auditPrint                                                            -- [x]
#print QAOA.isingChainCostHamiltonian                #auditPrint                                                            -- [x]

-- From QAOA.IsingChain.IsingChainQAOAExponentials
#print QAOA.IsingChainQAOAExponentials               #auditPrint                                                            -- [x]
#print QAOA.isingChainToQAOAExponentials             #auditPrint                                                            -- [x]
#print QAOA.standardIsingChainExponentialQAOAState   #auditPrint                                                            -- [x]

-- From QAOA.ExponentialRealization
#print QAOA.expUnitary                               #auditPrint   -- exp(-i t C) as a UnitaryOp (C Hermitian)              -- [x]
#print QAOA.isingChainQAOAExponentials_exp           #auditPrint   -- canonical exp realization for chain couplings J       -- [x]

-- From QAOA.IsingChain.IsingChainQAOAObservables
#print QAOA.isingChainQAOAFirstMoment                #auditPrint   -- F_p(γ, β) = ⟨γ,β|H_C|γ,β⟩                             -- [x]

-- From QAOA.IsingChain.UpperBound.ResidualEnergyBound
#print QAOA.IsingChain.residualEnergy                #auditPrint   -- ⟨H_C⟩.re / (2n) + 1/2                                 -- [x]
#print QAOA.IsingChain.ringQAOA                      #auditPrint   -- the ring-of-disagrees QAOA circuit (exp realization)  -- [x]

-- ── 3. Generic QAOA ───────────────────────────────────────────

-- From QAOA.QAOAState
#print QAOA.tailFamily                               #auditPrint                                                            -- [x]
#print QAOA.applyLayer                               #auditPrint   -- one QAOA layer: U_B (U_C ψ)                           -- [x]
#print QAOA.qaoaStateAux                             #auditPrint                                                            -- [x]
#print QAOA.qaoaState                                #auditPrint   -- |ψ_p⟩ = U_B^p U_C^p ⋯ U_B^1 U_C^1 |ψ_0⟩               -- [x]

-- From QAOA.StandardQAOA
#print QAOA.uniformKet                               #auditPrint                                                            -- [x]
#print QAOA.uniformState                             #auditPrint                                                            -- [x]
#print QAOA.standardQAOAState                        #auditPrint                                                            -- [x]

-- From QAOA.QAOAExponentials
#print QAOA.mixerExponential                         #auditPrint   -- exp(-i β B)                                           -- [x]
#print QAOA.costExponential                          #auditPrint   -- exp(-i γ C)                                           -- [x]
#print QAOA.QAOAExponentials                         #auditPrint                                                            -- [x]
#print QAOA.standardExponentialQAOAState             #auditPrint                                                            -- [x]

-- From QAOA.QAOAHamiltonians
#print QAOA.QAOAHamiltonians                         #auditPrint                                                            -- [x]
#print QAOA.costUnitaryFamily                        #auditPrint                                                            -- [x]
#print QAOA.mixerUnitaryFamily                       #auditPrint                                                            -- [x]
#print QAOA.standardHamiltonianQAOAState             #auditPrint                                                            -- [x]

-- From QAOA.StandardMixer
#print QAOA.standardMixerOp                          #auditPrint   -- B = ∑_j X_j                                           -- [x]
#print QAOA.standardMixerHamiltonian                 #auditPrint                                                            -- [x]

-- ── 4. Qubits ─────────────────────────────────────────────────

-- From Qubits.NQubitSpace
#print Qubits.NQubitDim                              #auditPrint   -- 2 ^ N                                                 -- [x]
#print Qubits.BitString                              #auditPrint                                                            -- [x]
#print Qubits.NQubitOp                               #auditPrint                                                            -- [x]
#print Qubits.NQubitUnitaryOp                        #auditPrint                                                            -- [x]
#print Qubits.NQubitHermitianOp                      #auditPrint                                                            -- [x]
#print Qubits.bitStringEquiv                         #auditPrint                                                            -- [x]
#print Qubits.NQubitNormKet                          #auditPrint                                                            -- [x]

-- From Qubits.LocalOperators
#print Qubits.SameOutside                            #auditPrint                                                            -- [x]
#print Qubits.instDecidableSameOutside               #auditPrint                                                            -- [x]
#print Qubits.localOp                                #auditPrint   -- lift A : Op 2 to qubit j                              -- [x]

-- From Qubits.PauliOperators
#print Qubits.localPauliX                            #auditPrint                                                            -- [x]
#print Qubits.localPauliZ                            #auditPrint                                                            -- [x]

-- ── 5. Quantum ────────────────────────────────────────────────

-- From Quantum.Operators.Types
#print Quantum.Operators.Op                          #auditPrint   -- Matrix (Fin n) (Fin n) ℂ                              -- [x]
#print Quantum.Operators.Bra                         #auditPrint                                                            -- [x]
#print Quantum.Operators.Ket                         #auditPrint                                                            -- [x]
#print Quantum.Operators.UnitaryOp                   #auditPrint                                                            -- [x]
#print Quantum.Operators.HermitianOp                 #auditPrint                                                            -- [x]

-- From Quantum.Operators.BraKet
#print Quantum.Operators.instHMulBraKet              #auditPrint   -- ⟨φ|ψ⟩                                                 -- [x]
#print Quantum.Operators.Ket.dag                     #auditPrint   -- |ψ⟩ ↦ ⟨ψ|                                             -- [x]
#print Quantum.Operators.instHMulOpKet               #auditPrint   -- A|ψ⟩                                                  -- [x]
#print Quantum.Operators.instHMulKetBra              #auditPrint   -- |ψ⟩⟨φ|                                                -- [x]
#print Quantum.Operators.stdKet                      #auditPrint                                                            -- [x]
#print Quantum.Operators.Ket.IsNormalized            #auditPrint                                                            -- [x]
#print Quantum.Operators.NormKet                     #auditPrint                                                            -- [x]
#print Quantum.Operators.instHMulUnitaryOpNormKet    #auditPrint                                                            -- [x]

-- From Quantum.Gates
#print Quantum.Gates.pauliX                          #auditPrint                                                            -- [x]
#print Quantum.Gates.pauliZ                          #auditPrint                                                            -- [x]

-- ── 6. Math ───────────────────────────────────────────────────

-- From Math.RepresentationTheory.PermutationAction
#print Math.RepresentationTheory.TensorIndex         #auditPrint                                                            -- [x]
#print Math.RepresentationTheory.tensorIndexEquiv    #auditPrint                                                            -- [x]




-- AUDIT-REGION-END






-- ════════════════════ Audit-completeness gate ════════════════════
-- `#audit_gate` (from `AuditHarness`) scans the `AUDIT-REGION` above and **errors** until every
-- item is `[x]` — both `[ ]` (unaudited) and `[!]` (flagged) keep it red — so a green
-- elaboration certifies a complete audit. It reads the live source, so it refreshes as you
-- type a mark, and is the same check under `lake env lean`.
#audit_gate
