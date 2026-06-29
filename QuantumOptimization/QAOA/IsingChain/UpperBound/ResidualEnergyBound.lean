import QuantumOptimization.QAOA.IsingChain.UpperBound.GroundStateEnergy
import QuantumOptimization.QAOA.IsingChain.UpperBound.ABCInvariance
import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.Reduction
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAObservables
import QuantumOptimization.QAOA.ExponentialRealization

/-!
# Residual Energy Bound — Theorem A composition (1906.08948v2 §IV l.715–725)

This file delivers **Theorem A**:
for the periodic 1D Ising ring of disagrees with `N` even sites and depth
`P` satisfying `2P + 2 ≤ N`, the QAOA residual energy is bounded below by
`1/(2P+2)` (equivalently, the approximation ratio `r_P` is at most
`(2P+1)/(2P+2)`).

Source pin: arXiv:1906.08948v2 §IV l.715–725, eq. (E_gs lower-bound argument).

## Proof composition

The proof chains six previously-established results:

```
residualEnergy ≥ 1/(2P+2)
  -- (1) definition of `residualEnergy`
  = (isingChainQAOAFirstMoment hChain γ β).re / (2N) + 1/2
  -- (2) `bond_expectation_full_eq_reduced` (A2.3, FGG light-cone reduction; sorry-free)
  = ((N · ⟨ψ̃|cP(0)|ψ̃⟩).re) / (2N) + 1/2
  -- (3) algebra
  = ⟨ψ̃|cP(0)|ψ̃⟩.re / 2 + 1/2
  -- (4) `chainPairInteraction_expectation_eq_averaged` (A4.4b, sorry-free)
  = (1/(2·N_R)) · ⟨ψ̃|(Hred_z^- + N_R · I)|ψ̃⟩.re + 1/2
  -- (5) variational principle + `eigenvalueOnBasis_lower_bound` (A5, sorry-free)
  ≥ (1/(2·N_R)) · (-(4P+2) + N_R) + 1/2
  -- (6) arithmetic with N_R = 2P+2
  = 1/(2P+2).
```

This file does NOT introduce any new mathematical content; it is the
algebraic composition of A1, A2.3, A4.4b, A5, plus the elementary
variational principle "diagonal operator with eigenvalues `≥ c` has
expectation `≥ c` on any normalized state".

## Public deliverables

* `QAOA.IsingChain.residualEnergy` — the residual-energy functional.
* `QAOA.IsingChain.residualEnergy_lower_bound` — **Theorem A**.
-/

namespace QAOA.IsingChain

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Residual energy functional
-- ============================================================================

/-- **Residual energy** of the standard chain exponential-QAOA state for the
ring of disagrees couplings (`J ≡ 1`).

The residual energy `eres = (⟨H_C⟩ − E_min) / (E_max − E_min)` with
`E_min = −n`, `E_max = +n` (so `E_max − E_min = 2n`) rearranges to
`⟨H_C⟩.re / (2n) + 1/2`. The `.re` projection is justified because
`⟨ψ|H|ψ⟩ ∈ ℝ` for any Hermitian `H` and any normalized state. -/
def residualEnergy {n p : ℕ}
    (hChain : IsingChainQAOAExponentials n (ringOfDisagreesCouplings n))
    (γ β : Fin p → ℝ) : ℝ :=
  (QAOA.isingChainQAOAFirstMoment hChain γ β).re / (2 * (n : ℝ)) + 1/2

namespace UpperBound

-- ============================================================================
-- Section: Bra-Op-Ket / dotProduct conversion
-- ============================================================================

/-- The `Bra * (Op * Ket)` form coincides with the matrix-level
`dotProduct (star v) (M *ᵥ v)`. This is the natural conversion between
the BraKet API used by `chainFirstMoment` / `psiTilde` and the matrix
API used in A4 (`chainPairInteraction_expectation_eq_averaged`). -/
private lemma bra_op_ket_eq_dotProduct {N : ℕ}
    (ψ : Qubits.NQubitKet N) (O : Qubits.NQubitOp N) :
    ψ.dag * (O * ψ) =
      dotProduct (star ψ.vec) (Matrix.mulVec O ψ.vec) := by
  rw [bra_mul_ket_eq]
  rfl

-- ============================================================================
-- Section: Variational principle for diagonal operators
-- ============================================================================

/-!
Elementary variational principle for an operator that acts diagonally on the
computational basis with bounded-below eigenvalues. Specialized to
`H = Hred_z_pm false P + N_R • I`, whose eigenvalues are `eigenvalueOnBasis P z + N_R`
on each basis ket `|z⟩` and bounded below by
`-(4P+2) + (2P+2) = -2P` via A5's `eigenvalueOnBasis_lower_bound`.
-/

/-- The operator `Hred_z_pm false P + N_R • I` acts diagonally on
the computational basis with eigenvalue `eigenvalueOnBasis P z + (2*P+2 : ℝ)`,
which is bounded below by `-(2*P : ℝ)`. -/
private lemma Hred_z_pm_plus_NR_apply_basis (P : ℕ)
    (z : Qubits.BitString (2*P+2)) :
    (Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
        Qubits.computationalBasisKet (2*P+2) z =
      (((eigenvalueOnBasis P z + (2*P+2 : ℝ) : ℝ) : ℂ)) •
        Qubits.computationalBasisKet (2*P+2) z := by
  rw [add_op_mul_ket, Hred_z_pm_false_apply_computationalBasisKet,
      smul_op_mul_ket]
  -- one_op_mul_ket: (1 : NQubitOp) * |z⟩ = |z⟩
  have h1 : (1 : Qubits.NQubitOp (2*P+2)) *
      Qubits.computationalBasisKet (2*P+2) z =
        Qubits.computationalBasisKet (2*P+2) z := by
    apply Ket.ext; intro i
    change (1 : Qubits.NQubitOp (2*P+2)).mulVec
        (Qubits.computationalBasisKet (2*P+2) z).vec i = _
    simp [Matrix.one_mulVec]
  rw [h1]
  -- Combine the two scaling factors into a single ((eig + N_R) : ℝ) : ℂ scalar.
  apply Ket.ext; intro i
  simp only [Ket.add_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

/-- The eigenvalue of `H := Hred_z_pm false P + N_R • I` on `|z⟩` is
`≥ -2P`. -/
private lemma Hred_z_pm_plus_NR_eigenvalue_lower_bound (P : ℕ)
    (z : Qubits.BitString (2*P+2)) :
    -(2*P : ℝ) ≤ eigenvalueOnBasis P z + (2*P+2 : ℝ) := by
  have h := eigenvalueOnBasis_lower_bound P z
  linarith

/-- The bra-op-ket expectation of `H = Hred_z_pm false P + N_R • I` on a
normalized reduced-chain state can be written as a real-coefficient sum
`Σ_i (eigenvalueOnBasis P (decode i) + N_R) * |ψ̃.vec i|²`, hence is
real-valued. -/
private lemma bra_H_ket_real_sum (P : ℕ) (ψ : Qubits.NQubitNormKet (2 * P + 2)) :
    ψ.toKet.dag * ((Hred_z_pm false P +
        ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) * ψ.toKet) =
      ((∑ i : Fin (Qubits.NQubitDim (2*P+2)),
        (eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ)) *
          Complex.normSq (ψ.toKet.vec i) : ℝ) : ℂ) := by
  -- Let H := Hred_z_pm false P + N_R • I; H acts diagonally with eigenvalue
  -- c i := eig + N_R on basis ket stdKet i.
  have hO : ∀ i : Fin (Qubits.NQubitDim (2*P+2)),
      (Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
          stdKet (Qubits.NQubitDim (2*P+2)) i =
        ((((eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ) : ℝ) : ℂ))) •
          stdKet (Qubits.NQubitDim (2*P+2)) i := by
    intro i
    have heq : stdKet (Qubits.NQubitDim (2*P+2)) i =
        Qubits.computationalBasisKet (2*P+2)
          ((Qubits.bitStringEquiv (2*P+2)).symm i) := by
      unfold Qubits.computationalBasisKet
      congr 1
      exact (Qubits.bitStringEquiv (2*P+2)).apply_symm_apply i |>.symm
    rw [heq]
    exact Hred_z_pm_plus_NR_apply_basis P _
  -- Componentwise action: (H * ψ).vec i = c i * ψ.vec i, via the diagonal lemma.
  -- We use `diagonal_op_mul_ket_component` via local restatement.
  have hcomp : ∀ i,
      ((Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
        ψ.toKet : Qubits.NQubitKet (2*P+2)).vec i =
        ((((eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ) : ℝ) : ℂ))) * ψ.toKet.vec i := by
    intro i
    have hOij : ∀ j,
        (Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) i j =
        if j = i then
          ((((eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm j) +
              (2*P+2 : ℝ) : ℝ) : ℂ)))
        else 0 := by
      intro j
      have h := congrArg Ket.vec (hO j)
      have h' := congrFun h i
      simp only [op_mul_ket_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul,
        stdKet_apply] at h'
      -- h' : (H.mulVec (fun k => if j = k then 1 else 0)) i = c j * (if j = i then 1 else 0)
      -- LHS = H i j after dotProduct expansion.
      simp only [Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero] at h'
      simpa using h'
    show (∑ j, _ * ψ.toKet.vec j) = _
    simp_rw [hOij, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  -- Now: ψ.dag * (H * ψ) = ∑ i, star(ψ.vec i) * ((c i) * ψ.vec i).
  rw [bra_mul_ket_eq]
  simp_rw [hcomp]
  -- ∑ i, star(ψ.vec i) * (c i * ψ.vec i) = ∑ i, c i * |ψ.vec i|² (c real).
  rw [show
      (((∑ i : Fin (Qubits.NQubitDim (2*P+2)),
        (eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ)) *
          Complex.normSq (ψ.toKet.vec i) : ℝ) : ℂ)) =
      ∑ i : Fin (Qubits.NQubitDim (2*P+2)),
        ((((eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ) : ℝ) : ℂ))) *
          ((((Complex.normSq (ψ.toKet.vec i) : ℝ) : ℂ))) by
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    push_cast; ring]
  apply Finset.sum_congr rfl
  intro i _
  rw [Ket.dag_vec]
  -- Goal: conj(ψ.vec i) * (c * ψ.vec i) = c * normSq
  have hnormSq : ((Complex.normSq (ψ.toKet.vec i) : ℝ) : ℂ) =
      (starRingEnd ℂ) (ψ.toKet.vec i) * ψ.toKet.vec i := Complex.normSq_eq_conj_mul_self
  rw [hnormSq]
  ring

/-- The bra-op-ket expectation of `H = Hred_z_pm false P + N_R • I` on a
normalized reduced-chain state is bounded below by `-2P`. -/
private lemma bra_H_ket_re_lower_bound (P : ℕ) (ψ : Qubits.NQubitNormKet (2 * P + 2)) :
    -(2 * P : ℝ) ≤
      (ψ.toKet.dag *
        ((Hred_z_pm false P +
            ((2 * P + 2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2 * P + 2))) *
          ψ.toKet)).re := by
  rw [bra_H_ket_real_sum]
  rw [Complex.ofReal_re]
  -- Need: -(2P) ≤ ∑_i (eig + N_R) * normSq (ψ.vec i).
  -- Each (eig + N_R) ≥ -(2P) and normSq ≥ 0 and ∑ normSq = 1.
  have hpos : ∀ i : Fin (Qubits.NQubitDim (2*P+2)),
      (0 : ℝ) ≤ Complex.normSq (ψ.toKet.vec i) := fun i ↦ Complex.normSq_nonneg _
  have hbound : ∀ i : Fin (Qubits.NQubitDim (2*P+2)),
      -(2*P : ℝ) * Complex.normSq (ψ.toKet.vec i) ≤
        (eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ)) * Complex.normSq (ψ.toKet.vec i) := by
    intro i
    apply mul_le_mul_of_nonneg_right _ (hpos i)
    exact Hred_z_pm_plus_NR_eigenvalue_lower_bound P _
  -- Sum bound:
  have hsum_bound :
      ∑ i, (-(2*P : ℝ)) * Complex.normSq (ψ.toKet.vec i) ≤
        ∑ i, (eigenvalueOnBasis P ((Qubits.bitStringEquiv (2*P+2)).symm i) +
            (2*P+2 : ℝ)) * Complex.normSq (ψ.toKet.vec i) :=
    Finset.sum_le_sum (fun i _ ↦ hbound i)
  -- ∑ -(2P) * normSq = -(2P) * (∑ normSq) = -(2P) * 1 = -(2P).
  have hnorm_total :
      ∑ i : Fin (Qubits.NQubitDim (2*P+2)),
        Complex.normSq (ψ.toKet.vec i) = 1 := by
    have hnormalized : ψ.toKet.dag * ψ.toKet = 1 := ψ.normalized
    have hexp : ψ.toKet.dag * ψ.toKet =
        ((∑ i : Fin (Qubits.NQubitDim (2*P+2)),
          Complex.normSq (ψ.toKet.vec i) : ℝ) : ℂ) := by
      rw [bra_mul_ket_eq]
      push_cast
      apply Finset.sum_congr rfl
      intro i _
      rw [Ket.dag_vec, ← Complex.normSq_eq_conj_mul_self]
    rw [hexp] at hnormalized
    -- hnormalized : ((∑ normSq) : ℝ) : ℂ = 1
    exact_mod_cast hnormalized
  rw [show -(2 * P : ℝ) = -(2*P : ℝ) * 1 from by ring]
  rw [← hnorm_total, Finset.mul_sum] at *
  exact hsum_bound

end UpperBound

/-- The depth-`P` QAOA circuit on the ring of disagrees (`N` sites): the canonical
exponential realization (`isingChainQAOAExponentials_exp`) specialized to the
ring-of-disagrees couplings. Its cost and mixer layers are the genuine matrix
exponentials of the Ising-chain cost and standard mixer Hamiltonians. -/
def ringQAOA (N : ℕ) : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N) :=
  isingChainQAOAExponentials_exp (ringOfDisagreesCouplings N)

-- ============================================================================
-- Theorem A — main composition
-- ============================================================================

open UpperBound in
/-- **Theorem A.** Upper bound on the QAOA approximation ratio for the ring
of disagrees: for the periodic 1D Ising ring with even `N` and depth `P`
satisfying `2P + 2 ≤ N`, the residual energy is bounded below by
`1/(2P+2)` (equivalently, the approximation ratio `r_P ≤ (2P+1)/(2P+2)`).

Source pin: arXiv:1906.08948v2 §IV l.715–725.

Proof: compose `bond_expectation_full_eq_reduced` (A2.3, FGG light-cone
reduction; sorry-free) with `chainPairInteraction_expectation_eq_averaged`
(A4.4b, sorry-free) and the elementary variational principle on
`Hred_z_pm false P + N_R • I` (whose eigenvalues are bounded below by
`-2P` per A5's `eigenvalueOnBasis_lower_bound`). -/
theorem residualEnergy_lower_bound
    {N P : ℕ} (hN_even : 2 ∣ N) (hP : 2 * P + 2 ≤ N)
    (γ β : Fin P → ℝ) :
    (1 : ℝ) / (2 * P + 2) ≤ residualEnergy (ringQAOA N) γ β := by
  set hChain : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N) := ringQAOA N
  -- Step 1: apply A2.3 to rewrite the first moment in terms of the reduced bond.
  -- Note: A2.3 (bond_expectation_full_eq_reduced) introduces a `(-β)` on the
  -- reduced side per the mixer-convention adjustment (the reduced-chain
  -- mixer is `-Σ X`, so its mixer-layer unitaries are inverses of the
  -- full-chain `+Σ X` ones; we feed `(-β)` to recover the full-chain
  -- mixer action). The variational bound below is universal in the
  -- reduced-chain state, hence holds equally well for the `(-β)` state.
  unfold residualEnergy
  rw [bond_expectation_full_eq_reduced hN_even hP hChain γ β]
  -- Step 2: convert RHS to A4.4b's dotProduct form via the conversion lemma.
  -- Let X := (psiTilde false P γ (-β)).toKet.dag *
  --          (chainPairInteraction 0 * (psiTilde false P γ (-β)).toKet) : ℂ.
  -- We have (N · X).re / (2N) + 1/2 = X.re / 2 + 1/2.
  set Xval : ℂ := (psiTilde false P γ (-β)).toKet.dag *
    ((IsingModel.chainPairInteraction (0 : Fin (2*P+2)) :
      Qubits.NQubitOp (2*P+2)) * (psiTilde false P γ (-β)).toKet) with hXval_def
  -- Apply A4.4b in `Bra * (Op * Ket)` form:
  -- X = (1/N_R) · ⟨ψ̃|H|ψ̃⟩ where H = Hred_z_pm false P + N_R • I.
  have hA44b : Xval =
      (1 / ((2*P+2 : ℕ) : ℂ)) *
        ((psiTilde false P γ (-β)).toKet.dag *
          ((Hred_z_pm false P +
              ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
            (psiTilde false P γ (-β)).toKet)) := by
    have h := chainPairInteraction_expectation_eq_averaged P γ (-β)
    -- h is in dotProduct form; Xval and the RHS are in Bra*Op*Ket form.
    -- Both sides are definitionally equal: ψ.dag * (Op * ψ) = ∑ i, star (ψ.vec i) * (Op *ᵥ ψ.vec) i.
    change (psiTilde false P γ (-β)).toKet.dag *
        ((IsingModel.chainPairInteraction (0 : Fin (2 * P + 2)) :
          Qubits.NQubitOp (2 * P + 2)) * (psiTilde false P γ (-β)).toKet) = _
    rw [bra_op_ket_eq_dotProduct (psiTilde false P γ (-β)).toKet
        (IsingModel.chainPairInteraction (0 : Fin (2*P+2)))]
    rw [bra_op_ket_eq_dotProduct (psiTilde false P γ (-β)).toKet
        (Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)))]
    exact h
  -- Let Yval := ⟨ψ̃|H|ψ̃⟩.
  set Yval : ℂ := (psiTilde false P γ (-β)).toKet.dag *
    ((Hred_z_pm false P +
        ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
      (psiTilde false P γ (-β)).toKet) with hYval_def
  -- Step 3: variational bound: Yval.re ≥ -2P (universal in the reduced-chain
  -- state, so applies equally to `psiTilde false P γ (-β)`).
  have hY_re_bound : -(2*P : ℝ) ≤ Yval.re := bra_H_ket_re_lower_bound P (psiTilde false P γ (-β))
  -- Step 4: do the algebra. After A2.3, the first moment is N * X.
  -- (N * X).re / (2N) + 1/2 ≥ 1/(2P+2).
  -- (N * X).re = N * X.re (since N : ℂ is real).
  -- X.re = (1/N_R) * Yval.re via hA44b.
  -- (N * X).re / (2N) + 1/2 = X.re/2 + 1/2 = (1/(2·N_R)) * Yval.re + 1/2.
  -- ≥ (1/(2·N_R)) * (-2P) + 1/2 = -2P/(2·(2P+2)) + 1/2 = -P/(2P+2) + 1/2.
  -- = (-(P) + (P+1)) / (2P+2) = 1/(2P+2). ✓
  have hNcoe_real : (((N : ℕ) : ℂ) * Xval).re = (N : ℝ) * Xval.re := by
    rw [show (((N : ℕ) : ℂ) * Xval) = (((N : ℝ) : ℂ)) * Xval from by push_cast; rfl]
    rw [Complex.re_ofReal_mul]
  -- Move ((N : ℕ) : ℂ) to ((N : ℝ) : ℂ) for the goal LHS.
  rw [show (((N : ℕ) : ℂ) * Xval).re = (N : ℝ) * Xval.re from hNcoe_real]
  -- From hA44b: Xval.re = (1/N_R) * Yval.re.
  have hN_R_pos : (0 : ℝ) < ((2*P + 2 : ℕ) : ℝ) := by
    have : (0 : ℕ) < 2*P + 2 := by omega
    exact_mod_cast this
  have hN_R_ne : ((2*P+2 : ℕ) : ℂ) ≠ 0 := by
    have : (2*P + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hXval_re : Xval.re = (1 / ((2*P+2 : ℕ) : ℝ)) * Yval.re := by
    have h := congrArg Complex.re hA44b
    rw [Complex.mul_re] at h
    -- (1 / ((2P+2):ℂ)) = (1/((2P+2):ℝ) : ℝ) : ℂ which has Im = 0.
    have h1 : (1 / ((2*P+2 : ℕ) : ℂ)).im = 0 := by
      rw [show (1 / ((2*P+2 : ℕ) : ℂ)) = (((1 / ((2*P+2 : ℕ) : ℝ) : ℝ)) : ℂ) from by
        push_cast; field_simp]
      exact Complex.ofReal_im _
    have h2 : (1 / ((2*P+2 : ℕ) : ℂ)).re = 1 / ((2*P+2 : ℕ) : ℝ) := by
      rw [show (1 / ((2*P+2 : ℕ) : ℂ)) = (((1 / ((2*P+2 : ℕ) : ℝ) : ℝ)) : ℂ) from by
        push_cast; field_simp]
      exact Complex.ofReal_re _
    rw [h1, h2] at h
    linarith
  rw [hXval_re]
  -- Now: 1/(2P+2) ≤ (N : ℝ) * ((1/N_R) * Yval.re) / (2*N) + 1/2.
  -- Simplify: N * (1/N_R) * Yval.re / (2N) = Yval.re / (2·N_R).
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    -- N > 0 since 2P+2 ≤ N implies N ≥ 2 > 0.
    have : (2 : ℕ) ≤ N := by omega
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) this)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hN_R_real_ne : ((2*P+2 : ℕ) : ℝ) ≠ 0 := ne_of_gt hN_R_pos
  -- Compute: (N : ℝ) * ((1/N_R) * Yval.re) / (2N) = Yval.re / (2 N_R).
  have hsimplify :
      (N : ℝ) * (1 / ((2*P+2 : ℕ) : ℝ) * Yval.re) / (2 * (N : ℝ)) =
        Yval.re / (2 * ((2*P+2 : ℕ) : ℝ)) := by
    field_simp
  rw [hsimplify]
  -- Goal: 1/(2P+2) ≤ Yval.re / (2 * (2P+2)) + 1/2.
  -- From hY_re_bound: Yval.re ≥ -2P.
  have hNR_eq : ((2*P+2 : ℕ) : ℝ) = (2*P + 2 : ℝ) := by push_cast; ring
  rw [hNR_eq]
  -- Goal: 1/(2*P + 2) ≤ Yval.re / (2 * (2*P + 2)) + 1/2.
  have hPP : (0 : ℝ) < 2*P + 2 := by
    have : (0 : ℕ) < 2*P + 2 := by omega
    exact_mod_cast this
  have h2NR_pos : (0 : ℝ) < 2 * (2*P + 2 : ℝ) := by linarith
  have hdiv_bound : -(2*P : ℝ) / (2 * (2*P + 2 : ℝ)) ≤
      Yval.re / (2 * (2*P + 2 : ℝ)) :=
    div_le_div_of_nonneg_right hY_re_bound h2NR_pos.le
  -- Final arithmetic:
  -- 1/(2P+2) ≤ -2P/(2(2P+2)) + 1/2 = (-2P + (2P+2))/(2(2P+2)) = 2/(2(2P+2)) = 1/(2P+2). ✓
  have hfinal_arith : (1 : ℝ) / (2*P + 2) =
      -(2*P : ℝ) / (2 * (2*P + 2 : ℝ)) + 1/2 := by
    field_simp
    ring
  linarith [hdiv_bound, hfinal_arith.le]

end

end QAOA.IsingChain
