/-
Axiom-cleanliness check for the headline theorems.

This file is NOT part of the library (`QuantumOptimization.lean` does not import
it, so `lake build` ignores it). Run it directly:

    lake env lean test/AxiomCheck.lean

It errors if any headline theorem depends on an axiom outside the Lean/Mathlib
trusted baseline `{propext, Classical.choice, Quot.sound}` — in particular it
fails on `sorryAx`, so it certifies the proofs are `sorry`-free. CI runs it.
-/
import QuantumOptimization.QAOA.IsingChain.UpperBound.ResidualEnergyBound
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition
import QuantumOptimization.QAOA.IsingChain.Achievability.Tightness

open Lean

/-- The Lean / Mathlib trusted baseline. -/
def baselineAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The public deliverables backing the paper. -/
def headlineTheorems : List Name :=
  [``QAOA.IsingChain.residualEnergy_lower_bound,
   ``QAOA.IsingChain.residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum,
   ``QAOA.IsingChain.epsilonMode_nonneg,
   ``QAOA.IsingChain.Achievability.residualEnergy_attained,
   ``QAOA.IsingChain.Achievability.residualEnergy_isLeast]

run_cmd do
  for t in headlineTheorems do
    let axs ← Lean.collectAxioms t
    let bad := axs.filter (fun a => ¬ baselineAxioms.contains a)
    unless bad.isEmpty do
      throwError m!"✗ {t} depends on disallowed axioms: {bad.toList}"
    Lean.logInfo m!"✓ {t} — axioms {axs.toList}"
