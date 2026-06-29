import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ReducedBondInvariance
import QuantumOptimization.QAOA.IsingChain.UpperBound.ABCInvariance

/-!
# PBC-Reduced ↔ ABC Bridge — summed-expectation matching of the reduced-chain bond pictures (Route B)

This file delivers the **Bridge** step of the FGG closure: it connects the two reduced-chain pictures
of the central bond expectation that the COMP step (`Reduction.lean`) needs to
join.

* **PBC reduced** (produced by the now-complete LIGHTCONE machinery):
  `⟨+|^{N_R} · U_PBC† · cP(0) · U_PBC · |+⟩^{N_R}`, i.e. the `|+⟩`-expectation
  of `reducedChainQAOAConj P γ β`, with `+Σ X` mixer and PBC cost sum.
* **ABC reduced** (wanted by `Reduction.lean:139` RHS):
  `⟨ψ̃ false P γ (-β) | cP(0) | ψ̃ false P γ (-β)⟩`, with `-Σ X` mixer and the
  `Hred_z_pm false`-driven (anti-periodic, body-shifted) cost.

## Route B — summed-expectation matching (NOT state-level identification)

State-level identification of the two reduced states does not work — the two
states have overlaps strictly < 1. Route B instead factors the Bridge through
two averaged pictures and the single operator-state **summed-expectation
identity**:

```
  Σ_{k:Fin N_R} ⟨+|^{N_R} · U_PBC† · cP(k) · U_PBC · |+⟩^{N_R}
     =  ⟨ψ̃ false P γ (-β) | (Hred_z_pm false P + N_R·I) | ψ̃ false P γ (-β)⟩
```

This file proves the two **averaging** halves SORRY-FREE and packages the
Bridge in terms of the summed-expectation identity:

* **(LHS-avg)** `reducedChainQAOAConj_sum_eq_NR_smul_bondZero` — by reduced-bond
  translation invariance (`reducedChainQAOAConj_at_expectation_eq_zero`), the
  sum over all `N_R` reduced bonds equals `N_R` copies of the canonical bond-`0`
  expectation. SORRY-FREE.
* **(RHS-avg)** `psiTilde_neg_bondZero_NR_smul_eq_shifted` — ABCEQ
  (`chainPairInteraction_expectation_eq_averaged`, universal in `(γ,β)`, applied
  at `(γ,-β)`) repackaged in `Ket.dag * (O * Ket)` form: `N_R` copies of the
  ABC bond-`0` expectation equal the shifted-operator expectation. SORRY-FREE.

The remaining **summed-expectation identity** is the Bridge core. It is not
derivable on the reduced chain by a fixed unitary (the PBC-reduced and ABC
states are structurally unrelated — since state-level identification fails); its rigorous proof
routes through the seam-irrelevance machinery and the reduced state bridge. That
proof now lives in `Reduction.bridgeSummedExpectation_holds` (axiom-clean). The
composite Bridge lemma `bridge_pbc_reduced_eq_abc_psiTilde` takes the summed
identity as an explicit typed hypothesis `BridgeSummedExpectation` so it can be
stated in this upstream file; downstream `Reduction.lean` feeds in the proven
`bridgeSummedExpectation_holds`. The two averaging halves discharge everything
else SORRY-FREE.

Sources:
* arXiv:1906.08948v2 App. `app:ABC_to_PBC` l.1300–1408 (ABC averaging; RHS-avg).
* arXiv:1906.08948v2 §IV l.699–702 (full-chain T-invariance; summed-core).
* arXiv:1411.4028v1 §II l.113–134 (FGG operator spreading; summed-core LIGHTCONE).

## Public deliverables

* `reducedChainQAOAConj_sum_eq_NR_smul_bondZero` — LHS averaging (sorry-free).
* `psiTilde_neg_bondZero_NR_smul_eq_shifted` — RHS averaging (sorry-free).
* `BridgeSummedExpectation` — the typed summed-expectation core (proven
  downstream by `Reduction.bridgeSummedExpectation_holds`).
* `bridge_pbc_reduced_eq_abc_psiTilde` — the composite Bridge identity,
  sorry-free, conditional on `BridgeSummedExpectation` (fed the proven core).
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

/-- Abbreviation for the uniform `|+⟩^{⊗N_R}` ket on the reduced chain. -/
private abbrev uPlus (P : ℕ) : Qubits.NQubitKet (2 * P + 2) :=
  QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))

-- ============================================================================
-- (LHS-avg) PBC-reduced averaging — sorry-free
-- ============================================================================

/-- **(LHS-avg) PBC-reduced averaging.** The sum over all `N_R = 2P+2` reduced
bonds of the `|+⟩`-expectation of the QAOA-conjugated bond observable equals
`N_R` copies of the canonical bond-`0` expectation
`⟨+| · reducedChainQAOAConj P γ β · |+⟩`.

This is the PBC reduced-chain analogue of full-chain cyclic invariance: every
reduced bond contributes the SAME expectation (proved sorry-free by
`reducedChainQAOAConj_at_expectation_eq_zero` via the cyclic translation `T`),
so the sum is exactly `N_R` times the canonical term.

Source: arXiv:1906.08948v2 §IV l.699–702 (per-bond invariance, PBC mirror). -/
theorem reducedChainQAOAConj_sum_eq_NR_smul_bondZero (P : ℕ) (γ β : Fin P → ℝ) :
    ∑ k : Fin (2 * P + 2),
        (uPlus P).dag * (reducedChainQAOAConj_at P γ β k * uPlus P) =
      ((2 * P + 2 : ℕ) : ℂ) •
        ((uPlus P).dag * (reducedChainQAOAConj P γ β * uPlus P)) := by
  -- Each summand equals the canonical bond-`0` term by translation invariance.
  rw [Finset.sum_congr rfl
      (fun k _ => reducedChainQAOAConj_at_expectation_eq_zero P γ β k)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul, smul_eq_mul]

-- ============================================================================
-- (RHS-avg) ABC averaging in `Ket.dag` form — sorry-free (reuses ABCEQ)
-- ============================================================================

/-- Conversion: the `Ket.dag * (O * Ket)` inner-product form equals the
`dotProduct (star ψ.vec) (mulVec O ψ.vec)` form used by the ABC lemmas. -/
private theorem braket_eq_dotProduct {n : ℕ}
    (ψ : Qubits.NQubitKet n) (O : Qubits.NQubitOp n) :
    ψ.dag * (O * ψ) = dotProduct (star ψ.vec) (Matrix.mulVec O ψ.vec) := by
  rw [bra_mul_ket_eq]
  rfl

/-- **(RHS-avg) ABC averaging.** `N_R` copies of the ABC bond-`0` expectation
`⟨ψ̃ false P γ (-β) | cP(0) | ψ̃⟩` equal the shifted-operator expectation
`⟨ψ̃ | (Hred_z_pm false P + N_R·I) | ψ̃⟩`.

This is `chainPairInteraction_expectation_eq_averaged` (ABCEQ, MS App. C
l.1308; universal in `(γ,β)`, here applied at `(γ,-β)`) cleared of the `1/N_R`
factor and translated from `dotProduct` form into `Ket.dag * (O * Ket)` form.

Note the constant-shift bookkeeping: the operator is the SHIFTED Lean cost
`Hred_z_pm false P` (carrying an internal `−N_R`) plus `+N_R·I`; the two
constants cancel to the bare-bond operator (a constant-shift trap). We use
the shifted operator literally; do NOT pre-cancel. -/
theorem psiTilde_neg_bondZero_NR_smul_eq_shifted (P : ℕ) (γ β : Fin P → ℝ) :
    ((2 * P + 2 : ℕ) : ℂ) •
        ((psiTilde false P γ (-β)).toKet.dag *
          ((IsingModel.chainPairInteraction (0 : Fin (2 * P + 2))
              : Qubits.NQubitOp (2 * P + 2)) *
            (psiTilde false P γ (-β)).toKet)) =
      (psiTilde false P γ (-β)).toKet.dag *
        ((Hred_z_pm false P +
            ((2 * P + 2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2 * P + 2))) *
          (psiTilde false P γ (-β)).toKet) := by
  -- ABCEQ at (γ, -β), in dotProduct form.
  have habceq := chainPairInteraction_expectation_eq_averaged P γ (-β)
  -- Translate both braket sides into dotProduct form and clear the 1/N_R.
  rw [braket_eq_dotProduct (psiTilde false P γ (-β)).toKet, smul_eq_mul]
  rw [braket_eq_dotProduct (psiTilde false P γ (-β)).toKet]
  -- Now goal: N_R * (dotProduct cP(0)) = dotProduct (Hred + N_R·I).
  rw [habceq]
  -- RHS = (1/N_R) * dotProduct(Hred+N_R); LHS = N_R * ((1/N_R) * dotProduct(...)).
  have hne : ((2 * P + 2 : ℕ) : ℂ) ≠ 0 := by
    have h : (2 * P + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  field_simp

-- ============================================================================
-- The irreducible summed-expectation core + the composite Bridge
-- ============================================================================

/-- **The summed-expectation Bridge core** (numerically validated).

This `Prop` is stated here (upstream) and PROVEN downstream by
`Reduction.bridgeSummedExpectation_holds` (axiom-clean), via the seam-irrelevance
machinery and the reduced state bridge. It is surfaced as a named `Prop` so the
composite Bridge `bridge_pbc_reduced_eq_abc_psiTilde` below can be stated in this
file ahead of that proof.

```
  Σ_{k:Fin N_R} ⟨+|^{N_R} · U_PBC(γ∘rev,β∘rev)† · cP(k) · U_PBC(γ∘rev,β∘rev) · |+⟩^{N_R}
     =  ⟨ψ̃ false P γ (-β) | (Hred_z_pm false P + N_R·I) | ψ̃ false P γ (-β)⟩
```

**Layer-order fix (Option A).** The reduced-bond conjugate on the LHS is fed the
REVERSED angle arrays `(fun i ↦ γ i.rev, fun i ↦ β i.rev)`. `qaoaConjugate`'s
recursion peels `Fin.last` as the *innermost* conjugation, so `qaoaConjugate P γ β`
realizes `V(γ∘rev,β∘rev)† · O · V(γ∘rev,β∘rev)` (the index-`P-1`-first product);
feeding reversed angles undoes this so the `⟨+|·|+⟩` expectation matches the
FORWARD physical QAOA state `ψ̃ false P γ (-β)` (index-`0`-first), the
convention `Reduction.lean:139` expects. Without the reversal the literal
identity is numerically FALSE for `P ≥ 2` (dev ≈ 3.7/4.1 at P=2/3); WITH it the
identity holds to ~1e-14 for P=1,2,3 (numerically).

This is the load-bearing operator-state identity that joins the PBC-reduced and
ABC pictures. It is not derivable on the reduced chain by a fixed unitary: the
PBC-reduced state `U_PBC|+⟩^{N_R}` and the ABC state `ψ̃ false P γ (-β)` are
structurally unrelated by any fixed unitary (their overlaps are strictly
< 1). The rigorous proof routes
both sides through the seam-irrelevance machinery via the reduction chain
```
  E_PBC(0) =[PBC reduced-bond transl., reducedChainQAOAConj_at_expectation_eq_zero]= E_PBC(mid)
           =[seam-irrelevance, genConjugate_middleBond_seam_irrelevance]=           E_ABC(mid)
           =[genConjugate↔psiTilde state bridge + ABC T̃-transl.]=                  E_ABC(0).
```
The first two steps are this file's averaging halves + `MiddleBondLocality.lean`.
The THIRD step — the `genConjugate(ABC cost) ↔ psiTilde`
Heisenberg-to-Schrödinger duality — is `StateBridge.psiTilde_expectation_eq_genConjugate`.
The whole core is assembled and PROVEN in `Reduction.bridgeSummedExpectation_holds`
(axiom-clean); we surface it here as a typed hypothesis so the composite Bridge
can be stated upstream of that proof.

Source: arXiv:1906.08948v2 §IV l.699–702 + App. C l.1300–1408;
arXiv:1411.4028v1 §II l.113–134 (composed). -/
def BridgeSummedExpectation (P : ℕ) (γ β : Fin P → ℝ) : Prop :=
    ∑ k : Fin (2 * P + 2),
        (uPlus P).dag *
          (reducedChainQAOAConj_at P (fun i => γ i.rev) (fun i => β i.rev) k *
            uPlus P) =
      (psiTilde false P γ (-β)).toKet.dag *
        ((Hred_z_pm false P +
            ((2 * P + 2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2 * P + 2))) *
          (psiTilde false P γ (-β)).toKet)

/-- **The composite Bridge identity.**

```
  ⟨+|^{N_R} · reducedChainQAOAConj P γ β · |+⟩^{N_R}
     =  ⟨ψ̃ false P γ (-β) | cP(0) | ψ̃ false P γ (-β)⟩
```

Takes the summed-expectation core `BridgeSummedExpectation` as a hypothesis
(`hcore`); downstream `Reduction.lean` feeds in the proven
`bridgeSummedExpectation_holds`, so the assembled identity is unconditional and
axiom-clean. Given `hcore`, the two averaging halves close the Bridge SORRY-FREE:

* `reducedChainQAOAConj_sum_eq_NR_smul_bondZero` rewrites the LHS sum of the core
  as `N_R • ⟨+|·reducedChainQAOAConj·|+⟩`;
* `psiTilde_neg_bondZero_NR_smul_eq_shifted` rewrites the RHS of the core as
  `N_R • ⟨ψ̃|cP(0)|ψ̃⟩`;

so the core becomes `N_R • LHS = N_R • RHS`, and cancelling the nonzero scalar
`N_R` gives the single-bond Bridge identity that `Reduction.lean` (COMP)
consumes.

The output form matches `Reduction.lean:139`'s RHS factor
`(psiTilde false P γ (-β)).toKet.dag * (chainPairInteraction 0 * …)` exactly. -/
theorem bridge_pbc_reduced_eq_abc_psiTilde (P : ℕ) (γ β : Fin P → ℝ)
    (hcore : BridgeSummedExpectation P γ β) :
    (uPlus P).dag *
        (reducedChainQAOAConj P (fun i => γ i.rev) (fun i => β i.rev) * uPlus P) =
      (psiTilde false P γ (-β)).toKet.dag *
        ((IsingModel.chainPairInteraction (0 : Fin (2 * P + 2))
            : Qubits.NQubitOp (2 * P + 2)) *
          (psiTilde false P γ (-β)).toKet) := by
  -- Rewrite the core's two sides via the averaging halves. The LHS reduced-bond
  -- conjugate carries the REVERSED angles `(γ∘rev, β∘rev)` (Option A layer-order
  -- fix); the averaging half is generic in the angle arrays so it applies
  -- verbatim at the reversed angles. The RHS `psiTilde false P γ (-β)` stays
  -- FORWARD: `qaoaConjugate` at reversed angles realizes the forward physical
  -- QAOA state expectation (numerically, ~1e-15).
  unfold BridgeSummedExpectation at hcore
  rw [reducedChainQAOAConj_sum_eq_NR_smul_bondZero P
        (fun i => γ i.rev) (fun i => β i.rev),
      ← psiTilde_neg_bondZero_NR_smul_eq_shifted P γ β] at hcore
  -- hcore : N_R • LHS = N_R • RHS. Cancel the nonzero scalar.
  have hne : ((2 * P + 2 : ℕ) : ℂ) ≠ 0 := by
    have h : (2 * P + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast h
  rw [smul_eq_mul, smul_eq_mul] at hcore
  exact mul_left_cancel₀ hne hcore

end

end QAOA.IsingChain.UpperBound.LightCone
