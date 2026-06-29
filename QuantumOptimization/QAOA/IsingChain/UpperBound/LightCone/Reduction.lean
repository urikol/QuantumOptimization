import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.Spreading
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.StateBridge
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.CanonicalMatching
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.ReducedABCtoPBCBridge
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.MiddleBondLocality
import QuantumOptimization.QAOA.IsingChain.UpperBound.ABCInvariance
import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAObservables

/-!
# Light-Cone Reduction — full-chain ↔ reduced-chain bond expectation (FGG black-box)

This file packages the final consumer-facing identity of the light-cone
analysis: the QAOA first-moment expectation `⟨ψ_P|H_C|ψ_P⟩` on the full
periodic ring of `N` sites with uniform unit antiferromagnetic couplings
equals `N` times the single-bond expectation
`⟨ψ̃_P|chainPairInteraction 0|ψ̃_P⟩` on the reduced `2P+2`-site chain
with the ABC boundary fork (`s = false`), with the **β parameters
negated** on the reduced side.

## Mixer-convention adjustment: `β ↦ -β` on the reduced side

The full-chain QAOA mixer layer uses `standardMixerHamiltonian = +Σ_j X_j`,
so its mixer unitaries are `exp(-i β · (+Σ X)) = exp(-i β Σ X)`. The
reduced-chain object `Hred_x_op P` used by `psiTilde` is defined as
`-(standardMixerOp (2*P+2))` (matching Mbeng–Santoro l.669, where the
reduced-chain mixer carries the sign convention `-Σ X`); its mixer
unitaries are `exp(-i β · (-Σ X)) = exp(+i β Σ X)`. To make the two
QAOA states match operationally we therefore pass `(-β)` (componentwise
negation on `Fin P → ℝ`) into `psiTilde` on the reduced side. Numerical
validation confirms machine-precision
agreement (`|LHS − RHS| ≈ 1e-14`) once the `-β` adjustment is applied.

## Source pin — FGG black-box

Sources:
* Farhi–Goldstone–Gutmann (FGG), arXiv:1411.4028v1 §II l.115–134, supplies
  the operator-spreading SUPPORT bound (the cone of light is at most `P`
  sites away from the link after `P` mixer layers); FGG does not perform
  the seam-cancellation identification.
* Mbeng–Santoro, arXiv:1906.08948v2 §IV l.620–697 and the appendix
  `ABC_to_PBC`, performs the actual structural identification of the
  full-chain bond expectation with the reduced-chain expectation, and
  packages the periodic-seam cancellation step.

Mbeng–Santoro §IV l.626 reads: *"As demonstrated in Ref. Farhi_arXiv2014,
the application of the digitized unitary operator … involves only spins
which have a distance at most P from the link"*. This file is now the
**sorry-free** final composition step: it threads the full-chain state
bridge (`StateBridge.isingChainQAOAFirstMoment_eq_uniform_conj`), the
full-ring cyclic invariance (`StateBridge.fullRing_conj_sum_eq_smul`),
the FGG light-cone match (`qaoa_full_eq_reduced_on_lightcone_at` with the
canonical witness `lightconeStructuralMatching_canonical`), and the
reduced PBC ↔ ABC `psiTilde` bridge (`bridge_pbc_reduced_eq_abc_psiTilde`,
discharged via `bridgeSummedExpectation_holds`).

## Reduced PBC ↔ ABC bridge (the former wall)

The irreducible reduced bridge `reduced_single_bond_bridge` is closed by
the chain
```
E_PBC(0) =[reduced bond transl.]=     E_PBC(mid)
         =[seam irrelevance]=         E_genConj(costFull − costSeamDiff)(mid)
         =[scalar shift]=             E_genConj(Hred_z)(mid)
         =[mixer/angle bridge]=       E_genConjTwo(Hred_z, Hred_x; −β)(mid)
         =[reduced state bridge]=     ⟨ψ̃|cP(mid)|ψ̃⟩
         =[ABC T̃-translation]=        ⟨ψ̃|cP(0)|ψ̃⟩.
```
The reduced state bridge is `StateBridge.psiTilde_expectation_eq_genConjugate`;
the ABC translation is `ABCInvariance.psiTilde_midBond_expectation_eq_zero`;
the seam irrelevance is `MiddleBondLocality.genConjugate_middleBond_seam_irrelevance`.

## Public deliverables

* `bond_expectation_full_eq_reduced` — the reduction theorem with
  `-β` on the reduced side, now **sorry-free**. Used downstream by the
  Theorem A composition `residualEnergy_lower_bound` in
  `ResidualEnergyBound.lean`.
-/

namespace QAOA.IsingChain.UpperBound

open Quantum.Operators
open scoped BigOperators

noncomputable section

/-- The seam-flipped reduced cost `costFull - costSeamDiff` equals the ABC cost
`Hred_z_pm false P` shifted by `+N_R · I`. (The `-1` per bond in `Hred_z`
accumulates to `-N_R`; the seam flip `Σ - 2·cP(seam)` removes the seam bond's
contribution and flips its sign.) -/
theorem costFull_sub_costSeamDiff_eq (P : ℕ) :
    LightCone.costFull P - LightCone.costSeamDiff P =
      Hred_z_pm false P +
        ((2 * P + 2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2 * P + 2)) := by
  -- Expand both sides to `Σ_{interior} cP - cP(last)` (a constant-shift trap:
  -- the `-1`-per-bond shifts in `Hred_z` cancel against `+N_R·I`).
  unfold LightCone.costFull LightCone.costSeamDiff LightCone.seamBond
    Hred_z_pm Hred_z_body Hred_z_boundary
  -- Split the full bond sum into interior bonds (castSucc) + the seam (last).
  rw [Fin.sum_univ_castSucc
      (f := fun k : Fin (2 * P + 2) => IsingModel.chainPairInteraction k)]
  -- Distribute the interior `(cP - 1)` body sum.
  rw [Finset.sum_sub_distrib]
  -- Both sides are now affine combinations of the interior bonds, `cP(last)`, `1`.
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Abstract the three operator atoms (interior sum, seam bond, identity) and
  -- close the ℂ-linear combination with `module`.
  generalize (∑ i : Fin (2 * P + 1),
      IsingModel.chainPairInteraction (i.castSucc : Fin (2 * P + 2))) = Sint
  generalize (IsingModel.chainPairInteraction (Fin.last (2 * P + 1) : Fin (2 * P + 2))) = Sl
  push_cast
  module

/-- **Mixer/angle bridge.** The MiddleBondLocality conjugate (cost `C`, standard
`+Σ X` mixer, `qaoaConjugate` angle convention) equals the two-generator
conjugate `genConjTwo` with the *reduced* mixer `Hred_x = -Σ X` at *negated*
mixer angles. The two `-` signs (on the mixer operator and on the angle) cancel
in every layer's mixer exponential. -/
theorem genConjugate_eq_genConjTwo_negMixer {N : ℕ} (C : Qubits.NQubitOp N) :
    ∀ (P : ℕ) (g b : Fin P → ℝ) (O : Qubits.NQubitOp N),
      LightCone.genConjugate P g b C O =
        LightCone.genConjTwo C (-(QAOA.standardMixerOp N)) P g (fun i => -(b i)) O := by
  intro P
  induction P with
  | zero => intro g b O; rfl
  | succ P ih =>
    intro g b O
    rw [LightCone.genConjugate_succ, LightCone.genConjTwo_succ,
        ih (fun i => g i.castSucc) (fun i => b i.castSucc) O]
    -- Rewrite the two mixer factors `exp(z • SM)` into `exp((-z) • (-SM))` form,
    -- which is what the `genConjTwo` (with mixer `-SM`) side carries.
    have hmix : ∀ z : ℂ,
        z • QAOA.standardMixerOp N = (-z) • (-(QAOA.standardMixerOp N)) := by
      intro z; rw [smul_neg, neg_smul, neg_neg]
    rw [hmix (((-(-b (Fin.last P)) : ℝ) * Complex.I : ℂ)),
        hmix (((-b (Fin.last P) : ℝ) * Complex.I : ℂ))]
    -- All four factors now match up to scalar normalization of the angles.
    congr 3 <;> push_cast <;> ring_nf

/-- Specialization to the reduced chain: mixer `Hred_x_op P = -(standardMixerOp (2P+2))`. -/
theorem genConjugate_eq_genConjTwo_Hred_x {P : ℕ}
    (C : Qubits.NQubitOp (2 * P + 2)) (g b : Fin P → ℝ)
    (O : Qubits.NQubitOp (2 * P + 2)) :
    LightCone.genConjugate P g b C O =
      LightCone.genConjTwo C (Hred_x_op P) P g (fun i => -(b i)) O :=
  genConjugate_eq_genConjTwo_negMixer C P g b O

/-- **Single-bond reduced bridge** (the irreducible content of
`BridgeSummedExpectation`): the canonical reduced PBC bond-`0` `|+⟩`-conjugate
expectation equals the ABC `psiTilde` bond-`0` expectation.

This is the genuinely structural reduced PBC ↔ ABC identification: the PBC
reduced conjugate sums over all `2P+2` bonds (including the seam), while the ABC
`psiTilde` removes the seam. They agree because the canonical bond's lightcone is
disjoint from the seam (`genConjugate_middleBond_seam_irrelevance`), combined
with reduced/ABC translation invariance and the reduced state bridge
(`psiTilde_expectation_eq_genConjugate`). -/
theorem reduced_single_bond_bridge (P : ℕ) (γ β : Fin P → ℝ) :
    (QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))).dag *
        (LightCone.reducedChainQAOAConj P (fun i => γ i.rev) (fun i => β i.rev) *
          QAOA.uniformKet (Qubits.NQubitDim (2 * P + 2))) =
      (psiTilde false P γ (-β)).toKet.dag *
        ((IsingModel.chainPairInteraction (0 : Fin (2 * P + 2))
            : Qubits.NQubitOp (2 * P + 2)) *
          (psiTilde false P γ (-β)).toKet) := by
  set g : Fin P → ℝ := (fun i => γ i.rev) with hg
  set b : Fin P → ℝ := (fun i => β i.rev) with hb
  -- Reduced state bridge (RHS) → genConjTwo form at the mid bond, after ABC translation.
  -- RHS = ⟨ψ̃|cP 0|ψ̃⟩ = ⟨ψ̃|cP mid|ψ̃⟩ (ABC translation) =
  --       ⟨+|genConjTwo Hred_z Hred_x g (-b) (cP mid)|+⟩ (reduced state bridge).
  rw [← psiTilde_midBond_expectation_eq_zero P γ (-β)]
  rw [LightCone.psiTilde_expectation_eq_genConjugate false P γ (-β)
      (IsingModel.chainPairInteraction (⟨P, by omega⟩ : Fin (2 * P + 2)))]
  -- The reduced state bridge feeds reversed angles: `((-β)∘rev) = -(β∘rev) = -b`,
  -- and `(γ∘rev) = g`. Rewrite the angle arrays to `g`, `-b`.
  rw [show (fun i => (-β) i.rev) = (fun i => -(b i)) from by funext i; simp [hb]]
  rw [show (fun i => γ i.rev) = g from rfl]
  -- LHS: unfold the PBC reduced conjugate, translate bond 0 → mid, then descend
  -- through the seam-irrelevance + scalar-shift + mixer bridge to the same genConjTwo.
  rw [show LightCone.reducedChainQAOAConj P g b =
        LightCone.qaoaConjugate P g b
          (IsingModel.chainPairInteraction (⟨0, by omega⟩ : Fin (2 * P + 2))) from rfl]
  rcases Nat.eq_zero_or_pos P with hP0 | hP1
  · -- Base case P = 0: depth-0 conjugation is the identity; both sides are ⟨+|cP 0|+⟩.
    subst hP0
    -- mid bond = ⟨0,_⟩ = bond 0; genConjTwo at depth 0 is the bare operator.
    rfl
  · -- Inductive width P ≥ 1.
    -- Step 2 — PBC reduced bond translation 0 → mid (width `(2P+1)+1 = 2P+2`).
    rw [show (IsingModel.chainPairInteraction (⟨0, by omega⟩ : Fin (2 * P + 2))
            : Qubits.NQubitOp (2 * P + 2)) =
        IsingModel.chainPairInteraction (0 : Fin (2 * P + 1 + 1)) from rfl]
    rw [← LightCone.fullRing_conj_expectation_reach (2 * P + 1) P g b
        (0 : Fin (2 * P + 1 + 1)) (⟨P, by omega⟩ : Fin (2 * P + 1 + 1))
        (LightCone.nextSite_reaches_all (2 * P + 1) (⟨P, by omega⟩ : Fin (2 * P + 1 + 1)))]
    -- Step 3 — PBC conjugate = genConjugate of `costFull` at the mid bond.
    rw [show (⟨P, by omega⟩ : Fin (2 * P + 1 + 1)) = LightCone.midBond P from rfl]
    rw [LightCone.qaoaConjugate_eq_genConjugate P g b
        (IsingModel.chainPairInteraction (LightCone.midBond P))]
    rw [show (∑ k : Fin (2 * P + 2), IsingModel.chainPairInteraction k) =
        LightCone.costFull P from rfl]
    -- Step 4 — seam irrelevance: costFull → costFull - costSeamDiff at the mid bond.
    rw [LightCone.genConjugate_middleBond_seam_irrelevance P hP1 g b]
    -- Step 5 — scalar shift: costFull - costSeamDiff = Hred_z + N_R·1.
    rw [costFull_sub_costSeamDiff_eq P,
        LightCone.genConjugate_cost_add_smul_one P g b
          (((2 * P + 2 : ℕ) : ℂ)) (Hred_z_pm false P)
          (IsingModel.chainPairInteraction (LightCone.midBond P))]
    -- Step 6 — mixer/angle bridge: genConjugate (cost Hred_z, +ΣX) =
    --          genConjTwo (cost Hred_z, mixer Hred_x, angles -b).
    rw [show Hred_z_pm false P = (Hred_z_hamiltonian false P : Qubits.NQubitOp (2 * P + 2))
        from rfl]
    rw [genConjugate_eq_genConjTwo_Hred_x
        (Hred_z_hamiltonian false P : Qubits.NQubitOp (2 * P + 2)) g b
        (IsingModel.chainPairInteraction (LightCone.midBond P))]
    -- Now both sides are `⟨+| genConjTwo Hred_z Hred_x P g (-b) (cP mid) |+⟩`.
    rfl

/-- The irreducible summed-expectation core (`BridgeSummedExpectation`),
assembled from the single-bond reduced bridge via the two sorry-free averaging
halves (`reducedChainQAOAConj_sum_eq_NR_smul_bondZero` and
`psiTilde_neg_bondZero_NR_smul_eq_shifted`). -/
theorem bridgeSummedExpectation_holds (P : ℕ) (γ β : Fin P → ℝ) :
    LightCone.BridgeSummedExpectation P γ β := by
  unfold LightCone.BridgeSummedExpectation
  -- LHS sum = N_R • (canonical reduced bond-0 conjugate expectation).
  rw [LightCone.reducedChainQAOAConj_sum_eq_NR_smul_bondZero P
      (fun i => γ i.rev) (fun i => β i.rev)]
  -- RHS = N_R • (ABC bond-0 expectation), via the RHS averaging half (backwards).
  rw [← LightCone.psiTilde_neg_bondZero_NR_smul_eq_shifted P γ β]
  -- Now `N_R • LHS₀ = N_R • RHS₀`; close by the single-bond identity.
  rw [reduced_single_bond_bridge P γ β]

/-- **FGG light-cone (arXiv:1411.4028v1 §II) + Mbeng–Santoro seam cancellation
(arXiv:1906.08948v2 §IV + App. `ABC_to_PBC`) — now fully formalized.**

Mbeng–Santoro arXiv:1906.08948v2 §IV l.626 reads: *"As demonstrated in
Ref. Farhi_arXiv2014, the application of the digitized unitary operator …
involves only spins which have a distance at most P from the link"*,
citing Farhi–Goldstone–Gutmann (arXiv:1411.4028v1 §II l.115–134) for the
operator-spreading SUPPORT bound. Mbeng–Santoro §IV l.620–697 together
with App. `ABC_to_PBC` then performs the structural identification of
the full-chain bond expectation with the reduced-chain expectation,
including the periodic-seam cancellation step. This theorem is now a
**sorry-free** composition of the Lean-side realizations of those steps
(see the module docstring for the proof skeleton).

**Mixer-convention `-β` on the reduced side.** The full-chain QAOA
uses `standardMixerHamiltonian = +Σ_j X_j`, while the reduced-chain
object `Hred_x_op P` used by `psiTilde` is defined as
`-(standardMixerOp (2*P+2))` (per Mbeng–Santoro l.669, the reduced-chain
mixer carries the `-Σ X` sign convention). The reduced-side mixer
unitaries `exp(-i β · Hred_x_op P) = exp(+i β Σ X)` are inverses of
the full-side mixer unitaries `exp(-i β Σ X)`; passing `(-β)` to
`psiTilde` on the reduced side recovers the full-side mixer action.
Numerically verified to machine precision
for (P=1, N=6) and (P=2, N=8). The `(-β)` here
is componentwise negation on `Fin P → ℝ` via the standard `Neg`
instance on pi-types.

Mathematical content. For the QAOA state `|ψ_P⟩` on the full periodic
`N`-site ring with uniform unit antiferromagnetic couplings `J_k ≡ 1`,
the first-moment expectation of the cost Hamiltonian
`H_C = Σ_k Z_k Z_{k+1}` equals `N` times the single-bond expectation
`⟨ψ̃_P|Z_0 Z_1|ψ̃_P⟩` on the reduced `2P+2`-site ABC chain (with the
`-β` mixer-convention adjustment). This bundles two consequences of
the FGG + Mbeng–Santoro composition:

1. **Full-chain cyclic translation invariance.** All `N` bond expectations
   `⟨ψ_P|Z_k Z_{k+1}|ψ_P⟩` are equal, since `|+⟩^{⊗N}` is fixed by every
   cyclic translation and both `H_C` and the standard mixer Hamiltonian
   are cyclically invariant; hence `⟨ψ_P|H_C|ψ_P⟩ = N · ⟨ψ_P|Z_{j_s} Z_{j_s+1}|ψ_P⟩`
   at the canonical interior bond `j_s = N/2`.

2. **Light-cone reduction to the reduced chain.** Under the hypothesis
   `2P+2 ≤ N`, FGG arXiv:1411.4028v1 §II ensures the operator
   `U_P† Z_{j_s} Z_{j_s+1} U_P` is supported on the `2P+2`-site window
   centered on the chosen bond, disconnected from the periodic seam.
   Mbeng–Santoro §IV + App. `ABC_to_PBC` then identifies this with the
   corresponding expectation on the reduced `2P+2`-site ABC chain
   (where the seam appears as the frustrating boundary bond), modulo
   the `β ↦ -β` adjustment forced by the reduced-chain mixer sign
   convention.

The Lean-side groundwork for the support calculus sits in
`LightCone/Basic.lean` and `LightCone/Spreading.lean`; this theorem
composes those building blocks with cyclic translation invariance
(`StateBridge.fullRing_conj_sum_eq_smul`) and the Mbeng–Santoro
seam-cancellation step (`reduced_single_bond_bridge`), sorry-free. -/
theorem bond_expectation_full_eq_reduced
    {N P : ℕ} (_hN_even : 2 ∣ N) (hP : 2*P + 2 ≤ N)
    (hChain : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N))
    (γ β : Fin P → ℝ) :
    QAOA.isingChainQAOAFirstMoment hChain γ β =
      (N : ℂ) *
        ((psiTilde false P γ (-β)).toKet.dag *
          ((IsingModel.chainPairInteraction (0 : Fin (2*P+2))
              : Qubits.NQubitOp (2*P+2)) *
            (psiTilde false P γ (-β)).toKet)) := by
  -- Write `N = M + 1` (legal since `2P+2 ≤ N ⇒ N ≥ 2 > 0`).
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  -- Step 1 — full state bridge: F_P = ⟨+| qaoaConjugate(γ∘rev,β∘rev)(Σ cP) |+⟩.
  rw [LightCone.isingChainQAOAFirstMoment_eq_uniform_conj hChain γ β]
  -- Step 2 — full-ring cyclic invariance: the conjugated cost sum is `(M+1)` copies
  -- of the canonical bond-`0` conjugate `|+⟩`-expectation.
  rw [LightCone.fullRing_conj_sum_eq_smul M P γ β]
  -- Step 3 — FGG light-cone match (at reversed angles, canonical bond `j_s = 0`):
  -- `⟨+| qaoaConjugate(γ∘rev,β∘rev)(cP 0_full) |+⟩ = ⟨+| reducedChainQAOAConj(γ∘rev,β∘rev) |+⟩`.
  -- `fullChainQAOAConj P g b 0 = qaoaConjugate P g b (cP 0)` definitionally.
  rw [show (LightCone.qaoaConjugate P (fun i => γ i.rev) (fun i => β i.rev)
        (IsingModel.chainPairInteraction (0 : Fin (M + 1)))) =
      LightCone.fullChainQAOAConj P (fun i => γ i.rev) (fun i => β i.rev)
        (0 : Fin (M + 1)) from rfl]
  rw [LightCone.qaoa_full_eq_reduced_on_lightcone_at P hP
      (fun i => γ i.rev) (fun i => β i.rev) (0 : Fin (M + 1))
      (⟨0, by omega⟩ : Fin (2 * P + 2))
      (LightCone.lightconeStructuralMatching_canonical P hP
        (fun i => γ i.rev) (fun i => β i.rev) (0 : Fin (M + 1)))]
  rw [LightCone.reducedChainQAOAConj_at_zero]
  -- Step 4 — reduced PBC ↔ ABC `psiTilde` bridge (irreducible summed core).
  rw [LightCone.bridge_pbc_reduced_eq_abc_psiTilde P γ β
      (bridgeSummedExpectation_holds P γ β)]

end

end QAOA.IsingChain.UpperBound
