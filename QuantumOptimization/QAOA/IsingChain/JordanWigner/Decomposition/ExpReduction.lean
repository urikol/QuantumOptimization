import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Preservation

/-!
# Exp-Conjugation Reduction — magnetization base case + per-mode `exp` conjugation

Machinery for the per-mode exp conjugation: the quantum base case for the dotted-pseudospin
expectation on the uniform state, plus the operator-conjugation reductions that collapse
the FULL reduced cost/mixer exponential conjugation of `dotTau_n` to the PER-MODE one on
active states.

* **base case** — `dotTau_expectation_uniformKet`: `⟨ψ0|û·τ⃗_k|ψ0⟩ = û ⬝ᵥ ẑ`
  (`τ^±` annihilate, `τ^z` fixes the uniform state).
* **exp-on-active machinery** — `mulVecCLM`/`leftMulVecCLM` and `exp_op_mul_ket_eq_of_pow`
  push the `expSeries` `HasSum` through `· *ᵥ v`; the active-subspace operators
  `modesSubShift`/`modesSubShiftX` agree with `Hred_z_pm`/`Hred_x_op` on active states and
  factor as `exp(c•(Hmode + Hrest)) = exp(c•Hrest)·exp(c•Hmode)`.
* **conjugation reductions** — `costExp_conj_dotTau_eq_modeExp` / `mixerExp_conj_dotTau_eq_modeExp`:
  on active `v`, `exp(±c•Hred)·dotTau_n·exp(∓c•Hred)·v = exp(±c•HMode_n)·dotTau_n·exp(∓c•HMode_n)·v`.

The `attribute [local instance]` matrix-`linftyOp` norm instances (needed for `NormedSpace.exp`
on `NQubitOp`) are declared in-file, scoped to this module's exp machinery; the load-bearing
`set_option maxHeartbeats` raises travel with their declarations.

## Main statements
- `dotTau_expectation_uniformKet`: the quantum base case `⟨ψ0|û·τ⃗_k|ψ0⟩ = û ⬝ᵥ ẑ`
- `costExp_conj_dotTau_eq_modeExp` / `mixerExp_conj_dotTau_eq_modeExp`: the per-mode
  conjugation reductions on active states
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 4 (S2): magnetization ↔ expectation
--   DELIVERABLE: mode_sum_expectation
-- ============================================================================

-- ----------------------------------------------------------------------------
-- Base case: ⟨ψ0|τ⃗_k|ψ0⟩ = ẑ on the uniform state.
-- ----------------------------------------------------------------------------

/-- Expectation/adjoint identity: `⟨ψ|A|ψ⟩ = conj ⟨ψ|A†|ψ⟩`. Matrix-level: swap the
two summation indices and conjugate. -/
theorem braOpKet_eq_conj_braOpKet_dag {N : ℕ} (ψ : NQubitKet N) (A : NQubitOp N) :
    ψ.dag * (A * ψ) = star (ψ.dag * (A.conjTranspose * ψ)) := by
  rw [braOpKet_eq_dotProduct, braOpKet_eq_dotProduct]
  -- ∑ i, conj(ψ i) * (A *ᵥ ψ) i  =  conj (∑ i, conj(ψ i) * (Aᴴ *ᵥ ψ) i)
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
  -- LHS as a double sum.
  have hLHS : (∑ i, star (ψ.vec i) * ∑ j, A i j * ψ.vec j)
      = ∑ i, ∑ j, star (ψ.vec i) * A i j * ψ.vec j := by
    apply Finset.sum_congr rfl; intro i _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _; ring
  -- RHS as a double sum.
  have hRHS : star (∑ i, star (ψ.vec i) * ∑ j, Aᴴ i j * ψ.vec j)
      = ∑ i, ∑ j, star (ψ.vec j) * A j i * ψ.vec i := by
    rw [star_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [star_mul', star_star, star_sum, mul_comm, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _
    rw [star_mul', Matrix.conjTranspose_apply, star_star]
    ring
  rw [hLHS, hRHS, Finset.sum_comm]

/-- `τ^+_k · |+⟩^{⊗N_R} = 0`: the raising operator `τ^+_k = c_{−k} c_k` annihilates the
uniform state (its inner `c_k` already does, by U1). -/
theorem tauPlus_mulVec_uniformKet (P : ℕ) (k : ℝ) :
    tauPlus P k * (uniformKet (Qubits.NQubitDim (2*P+2))) = 0 := by
  unfold tauPlus
  rw [op_mul_op_mul_ket, cAnnihK_mulVec_uniformKet]
  ext i
  rw [op_mul_ket_vec, show (0 : NQubitKet (2*P+2)).vec = 0 from rfl, Matrix.mulVec_zero]

/-- `(τ^+_k)† = τ^−_k` (the lowering operator is the adjoint of the raising operator). -/
theorem tauMinus_eq_tauPlus_conjTranspose (P : ℕ) (k : ℝ) :
    tauMinus P k = (tauPlus P k).conjTranspose := by
  unfold tauMinus tauPlus cCreateK
  rw [Matrix.conjTranspose_mul]

/-- `⟨ψ0|τ^+_k|ψ0⟩ = 0`. -/
theorem tauPlus_expectation_uniformKet (P : ℕ) (k : ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (tauPlus P k * (uniformKet (Qubits.NQubitDim (2*P+2)))) = 0 := by
  rw [tauPlus_mulVec_uniformKet]
  rw [show (0 : NQubitKet (2*P+2)) = (0 : ℂ) • (uniformKet (Qubits.NQubitDim (2*P+2)))
    by ext i; simp]
  rw [bra_mul_smul_ket]
  simp

/-- `⟨ψ0|τ^−_k|ψ0⟩ = 0` (conjugate of `⟨ψ0|τ^+_k|ψ0⟩` via the adjoint identity). -/
theorem tauMinus_expectation_uniformKet (P : ℕ) (k : ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (tauMinus P k * (uniformKet (Qubits.NQubitDim (2*P+2)))) = 0 := by
  rw [tauMinus_eq_tauPlus_conjTranspose, braOpKet_eq_conj_braOpKet_dag,
    Matrix.conjTranspose_conjTranspose, tauPlus_expectation_uniformKet]
  simp

/-- `⟨ψ0|τ^x_k|ψ0⟩ = 0` (sum of the two off-diagonal pieces). -/
theorem tauX_expectation_uniformKet (P : ℕ) (k : ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (tauX P k * (uniformKet (Qubits.NQubitDim (2*P+2)))) = 0 := by
  unfold tauX
  rw [add_op_mul_ket, bra_mul_add_ket, tauPlus_expectation_uniformKet,
    tauMinus_expectation_uniformKet]
  ring

/-- `⟨ψ0|τ^y_k|ψ0⟩ = 0`. -/
theorem tauY_expectation_uniformKet (P : ℕ) (k : ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (tauY P k * (uniformKet (Qubits.NQubitDim (2*P+2)))) = 0 := by
  unfold tauY
  rw [smul_op_mul_ket, bra_mul_smul_ket, sub_op_mul_ket, bra_mul_sub_ket,
    tauPlus_expectation_uniformKet, tauMinus_expectation_uniformKet]
  simp

/-- `τ^z_k · |+⟩^{⊗N_R} = |+⟩^{⊗N_R}` (`τ^z = 1 − n_k − n_{−k}`, and both number
operators annihilate the uniform state, U1 ⟹ U2). -/
theorem tauZ_mulVec_uniformKet (P : ℕ) (k : ℝ) :
    tauZ P k * (uniformKet (Qubits.NQubitDim (2*P+2)))
      = uniformKet (Qubits.NQubitDim (2*P+2)) := by
  unfold tauZ
  rw [sub_op_mul_ket, sub_op_mul_ket, numberOpK_mulVec_uniformKet,
    numberOpK_mulVec_uniformKet]
  ext i
  simp [op_mul_ket_vec, Matrix.one_mulVec]

/-- `⟨ψ0|τ^z_k|ψ0⟩ = 1` (the uniform state is `τ^z`-positive; normalization). -/
theorem tauZ_expectation_uniformKet (P : ℕ) (k : ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (tauZ P k * (uniformKet (Qubits.NQubitDim (2*P+2)))) = 1 := by
  rw [tauZ_mulVec_uniformKet]
  exact uniformKet_IsNormalized (Qubits.NQubitDim (2*P+2))

/-- **Quantum base case.** `⟨ψ0|û·τ⃗_k|ψ0⟩ = (û ⬝ᵥ ẑ : ℂ)`: the magnetization
of the uniform initial state is `ẑ`, so the dotted expectation reads off the `ẑ`
component of the axis `û`. -/
theorem dotTau_expectation_uniformKet (P : ℕ) (k : ℝ) (u : Fin 3 → ℝ) :
    (uniformKet (Qubits.NQubitDim (2*P+2))).dag *
      (dotTau P k u * (uniformKet (Qubits.NQubitDim (2*P+2))))
      = ((u ⬝ᵥ zHat : ℝ) : ℂ) := by
  unfold dotTau tauVecOp
  rw [Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  rw [add_op_mul_ket, add_op_mul_ket, bra_mul_add_ket, bra_mul_add_ket,
    smul_op_mul_ket, smul_op_mul_ket, smul_op_mul_ket,
    bra_mul_smul_ket, bra_mul_smul_ket, bra_mul_smul_ket,
    tauX_expectation_uniformKet, tauY_expectation_uniformKet,
    tauZ_expectation_uniformKet]
  unfold zHat
  rw [dotProduct, Fin.sum_univ_three]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]

-- ----------------------------------------------------------------------------
-- Aux: exp-on-active-subspace, the operator-free `exp` agreement helper.
-- ----------------------------------------------------------------------------

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

/-- The continuous-linear map `M ↦ M *ᵥ v` (`Op → (Fin N → ℂ)`), built from finite
dimensionality. Used to push the `expSeries` `HasSum` through `· *ᵥ v`. -/
noncomputable def mulVecCLM {N : ℕ} (v : Fin N → ℂ) :
    Matrix (Fin N) (Fin N) ℂ →L[ℂ] (Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M M' => by ext i; simp [Matrix.add_mulVec]
      map_smul' := fun c M => by ext i; simp [Matrix.smul_mulVec] }

@[simp] theorem mulVecCLM_apply {N : ℕ} (v : Fin N → ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    mulVecCLM v M = M *ᵥ v := rfl

/-- The continuous-linear map `w ↦ M *ᵥ w` (`(Fin N → ℂ) → (Fin N → ℂ)`), built from
finite dimensionality. Used to push a vector `HasSum` through `M *ᵥ ·`. -/
noncomputable def leftMulVecCLM {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) :
    (Fin N → ℂ) →L[ℂ] (Fin N → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin M)

@[simp] theorem leftMulVecCLM_apply {N : ℕ} (M : Matrix (Fin N) (Fin N) ℂ) (w : Fin N → ℂ) :
    leftMulVecCLM M w = M *ᵥ w := rfl

/-- **Exp-agrees-on-vector core.** If the powers of `M` and `M'` agree when
applied to `v` (`M^j *ᵥ v = M'^j *ᵥ v` for all `j`), then `exp(M) *ᵥ v = exp(M') *ᵥ v`.
Operator-free: pushes the `expSeries` `HasSum` through the continuous map `· *ᵥ v`. -/
theorem exp_mulVec_eq_of_pow_mulVec_eq {N : ℕ}
    (M M' : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ)
    (hpow : ∀ j : ℕ, (M ^ j) *ᵥ v = (M' ^ j) *ᵥ v) :
    (NormedSpace.exp M) *ᵥ v = (NormedSpace.exp M') *ᵥ v := by
  have hM := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) M).map (mulVecCLM v)
    (mulVecCLM v).continuous
  have hM' := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) M').map (mulVecCLM v)
    (mulVecCLM v).continuous
  simp only [Function.comp_def, mulVecCLM_apply] at hM hM'
  have hterm : ∀ j : ℕ,
      (NormedSpace.expSeries ℂ (Matrix (Fin N) (Fin N) ℂ) j (fun _ => M)) *ᵥ v
        = (NormedSpace.expSeries ℂ (Matrix (Fin N) (Fin N) ℂ) j (fun _ => M')) *ᵥ v := by
    intro j
    rw [NormedSpace.expSeries_apply_eq, NormedSpace.expSeries_apply_eq,
      Matrix.smul_mulVec, Matrix.smul_mulVec, hpow j]
  exact hM.unique (hM'.congr_fun (fun j => hterm j))

/-- Ket-level version of `exp_mulVec_eq_of_pow_mulVec_eq`: if the powers of `M` and `M'`
agree on the ket `v`, then `exp(M) * v = exp(M') * v` (as kets). -/
theorem exp_op_mul_ket_eq_of_pow {N : ℕ}
    (M M' : NQubitOp N) (v : NQubitKet N)
    (hpow : ∀ j : ℕ, (M ^ j) * v = (M' ^ j) * v) :
    (NormedSpace.exp M) * v = (NormedSpace.exp M') * v := by
  ext i
  rw [op_mul_ket_vec, op_mul_ket_vec]
  have hpow' : ∀ j : ℕ, (M ^ j) *ᵥ v.vec = (M' ^ j) *ᵥ v.vec := by
    intro j
    have := congrArg Ket.vec (hpow j)
    rwa [op_mul_ket_vec, op_mul_ket_vec] at this
  rw [exp_mulVec_eq_of_pow_mulVec_eq M M' v.vec hpow']

/-- Local abbreviation: the active-subspace cost operator `H'' = (∑ HredZMode) − N_R·1`.
On active states this agrees with `Hred_z_pm` (`HredZDecomp_active`). -/
def modesSubShift (P : ℕ) : NQubitOp (2*P+2) :=
  (∑ n : Fin P, HredZMode P (waveVectorABC P n)) - ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2))

set_option maxHeartbeats 1600000 in
-- Raised: unfolding the big-operator `modesSubShift` sum at the symbolic dimension.
/-- `modesSubShift` preserves the active subspace. -/
theorem modesSubShift_preserves_inActiveSubspace (P : ℕ) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) : InActiveSubspace P (modesSubShift P * w) := by
  -- Split the operator action first to dodge the costly `inActiveSubspace_sub` unification.
  have hsum : InActiveSubspace P ((∑ n : Fin P, HredZMode P (waveVectorABC P n)) * w) :=
    inActiveSubspace_op_sum Finset.univ _ w
      (fun n _ => HredZMode_preserves_inActiveSubspace P n w hw)
  have hscal : InActiveSubspace P (((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2)) * w) := by
    rw [smul_op_mul_ket]
    refine inActiveSubspace_smul _ _ ?_
    rw [show (1 : NQubitOp (2*P+2)) * w = w by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]]
    exact hw
  unfold modesSubShift
  rw [sub_op_mul_ket]
  exact inActiveSubspace_sub _ _ hsum hscal

/-- On active `w`, `Hred_z_pm * w = modesSubShift * w` (`HredZDecomp_active` rearranged). -/
theorem Hred_z_pm_eq_modesSubShift_on_active (P : ℕ) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) :
    (UpperBound.Hred_z_pm false P) * w = modesSubShift P * w := by
  have h := HredZDecomp_active P w hw
  rw [add_op_mul_ket] at h
  unfold modesSubShift
  rw [sub_op_mul_ket, ← h]
  ext i; simp only [Ket.sub_vec, Ket.add_vec, smul_op_mul_ket, Ket.smul_vec,
    op_mul_ket_vec, Pi.smul_apply, smul_eq_mul, Matrix.one_mulVec]
  ring

set_option maxHeartbeats 800000 in
-- Raised: `pow_succ'`/`op_mul_op_mul_ket` defeq on the big-operator `Hred_z_pm`.
/-- A power of `Hred_z_pm` applied to an active state stays active. -/
theorem Hred_z_pm_pow_preserves_inActiveSubspace (P : ℕ) :
    ∀ (j : ℕ) (v : NQubitKet (2 * P + 2)), InActiveSubspace P v →
    InActiveSubspace P ((UpperBound.Hred_z_pm false P) ^ j * v) := by
  intro j
  induction j with
  | zero =>
      intro v hv; rw [pow_zero]
      rw [show (1 : NQubitOp (2*P+2)) * v = v by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]]
      exact hv
  | succ j IH =>
      intro v hv
      rw [pow_succ', op_mul_op_mul_ket]
      exact Hred_z_pm_preserves_inActiveSubspace P _ (IH v hv)

set_option maxHeartbeats 800000 in
-- Raised: `pow_succ'`/`op_mul_op_mul_ket` defeq on the big-operator `Hred_z_pm`.
/-- For active `v`, the powers of `Hred_z_pm` and of `modesSubShift` agree on `v`. -/
theorem Hred_z_pm_pow_eq_modesSubShift_on_active (P : ℕ) :
    ∀ (j : ℕ) (v : NQubitKet (2 * P + 2)), InActiveSubspace P v →
    (UpperBound.Hred_z_pm false P) ^ j * v = (modesSubShift P) ^ j * v := by
  intro j
  induction j with
  | zero => intro v _; rw [pow_zero, pow_zero]
  | succ j IH =>
      intro v hv
      -- `modesSubShift^j * v` is active (= Hred_z_pm^j * v which is active).
      have hact : InActiveSubspace P ((modesSubShift P) ^ j * v) := by
        rw [← IH v hv]; exact Hred_z_pm_pow_preserves_inActiveSubspace P j v hv
      -- M^(j+1) v = M (M^j v); rewrite inner via IH, then agreement on active (M^j v).
      rw [pow_succ', op_mul_op_mul_ket, IH v hv,
        Hred_z_pm_eq_modesSubShift_on_active P _ hact, ← op_mul_op_mul_ket, ← pow_succ']

/-- For active `v`, `exp(c • Hred_z_pm) * v = exp(c • modesSubShift) * v`: the scaled
exponentials agree on the active subspace (powers agree, `exp_op_mul_ket_eq_of_pow`). -/
theorem exp_smul_Hred_z_pm_eq_modesSubShift_on_active (P : ℕ) (c : ℂ)
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    (NormedSpace.exp (c • UpperBound.Hred_z_pm false P)) * v
      = (NormedSpace.exp (c • modesSubShift P)) * v := by
  refine exp_op_mul_ket_eq_of_pow _ _ v (fun j => ?_)
  rw [smul_pow, smul_pow, smul_op_mul_ket, smul_op_mul_ket,
    Hred_z_pm_pow_eq_modesSubShift_on_active P j v hv]

-- ----------------------------------------------------------------------------
-- Per-mode conjugation reduction (full unitary → per-mode).
-- Hred_z_pm = HredZMode_n + Hrest_n on active states, with Hrest_n commuting with
-- BOTH HredZMode_n and dotTau_n; the cost conjugation collapses to the per-mode one.
-- ----------------------------------------------------------------------------

/-- The "rest" cost operator for mode `n`: `Hrest_n = modesSubShift − HredZMode k_n
= (∑_{m≠n} HredZMode k_m) − N_R·1`. Commutes with `HredZMode k_n` and with `dotTau k_n`. -/
def costRest (P : ℕ) (n : Fin P) : NQubitOp (2*P+2) :=
  modesSubShift P - HredZMode P (waveVectorABC P n)

/-- `modesSubShift = HredZMode k_n + costRest n` (definitional rearrangement). -/
theorem modesSubShift_eq_add_costRest (P : ℕ) (n : Fin P) :
    modesSubShift P = HredZMode P (waveVectorABC P n) + costRest P n := by
  unfold costRest; abel

/-- `HredZMode k_n` commutes with `costRest n`. -/
theorem HredZMode_commute_costRest (P : ℕ) (n : Fin P) :
    Commute (HredZMode P (waveVectorABC P n)) (costRest P n) := by
  unfold costRest modesSubShift
  refine Commute.sub_right (Commute.sub_right ?_ ?_) ?_
  · -- Commute (HredZMode k_n) (∑ m, HredZMode k_m): split the sum at n.
    refine Commute.sum_right _ _ _ (fun m _ => ?_)
    by_cases hmn : m = n
    · subst hmn; exact Commute.refl _
    · exact (HredZMode_commute_HredZMode_cross P n m (fun h => hmn h.symm))
  · exact (Commute.one_right _).smul_right _
  · exact Commute.refl _

/-- `costRest n` rewritten with the mode-`n` term removed: `costRest n =
(∑_{m ≠ n} HredZMode k_m) − N_R·1` (the `∑ − HredZMode_n` collapses to the erased sum). -/
theorem costRest_eq_erase_sum (P : ℕ) (n : Fin P) :
    costRest P n = (∑ m ∈ Finset.univ.erase n, HredZMode P (waveVectorABC P m))
      - ((2*P+2 : ℂ)) • (1 : NQubitOp (2*P+2)) := by
  unfold costRest modesSubShift
  have h : (∑ m : Fin P, HredZMode P (waveVectorABC P m))
      = HredZMode P (waveVectorABC P n)
        + ∑ m ∈ Finset.univ.erase n, HredZMode P (waveVectorABC P m) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ n)).symm
  rw [h]; abel

/-- `costRest n` commutes with `û·τ⃗_{k_n}` (only cross-mode terms survive). -/
theorem costRest_commute_dotTau (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ) :
    Commute (costRest P n) (dotTau P (waveVectorABC P n) u) := by
  rw [costRest_eq_erase_sum]
  refine Commute.sub_left ?_ ((Commute.one_left _).smul_left _)
  refine Commute.sum_left _ _ _ (fun m hm => ?_)
  exact HredZMode_commute_dotTau_cross P m n (Finset.ne_of_mem_erase hm) u

/-- `exp(c•A)` commutes with `B` whenever `A` commutes with `B`. -/
theorem exp_smul_commute_of_commute {N : ℕ} (c : ℂ) (A B : NQubitOp N)
    (h : Commute A B) : Commute (NormedSpace.exp (c • A)) B :=
  (h.smul_left c).exp_left

/-- If every power `(c•A)^j` keeps `v` in the active subspace, then so does `exp(c•A)`:
push the `expSeries` `HasSum` through `· *ᵥ v` and through `activeProj *ᵥ ·` (both
continuous), using that the active subspace is the fixed-point set of `activeProj`. -/
theorem exp_smul_preserves_inActiveSubspace (P : ℕ) (c : ℂ) (A : NQubitOp (2 * P + 2))
    (v : NQubitKet (2 * P + 2))
    (hpow : ∀ j : ℕ, InActiveSubspace P ((c • A) ^ j * v)) :
    InActiveSubspace P (NormedSpace.exp (c • A) * v) := by
  unfold InActiveSubspace
  ext i
  simp only [op_mul_ket_vec]
  -- `exp(c•A) *ᵥ v` as the HasSum of `(c•A)^j/j! *ᵥ v`.
  have hexp := (NormedSpace.expSeries_hasSum_exp (𝕂 := ℂ) (c • A)).map (mulVecCLM v.vec)
    (mulVecCLM v.vec).continuous
  simp only [Function.comp_def, mulVecCLM_apply] at hexp
  -- Each term is fixed by `activeProj` (its power keeps `v` active).
  have hterm : ∀ j : ℕ,
      (activeProj P) *ᵥ ((NormedSpace.expSeries ℂ (NQubitOp (2*P+2)) j (fun _ => c • A)) *ᵥ v.vec)
        = (NormedSpace.expSeries ℂ (NQubitOp (2*P+2)) j (fun _ => c • A)) *ᵥ v.vec := by
    intro j
    rw [NormedSpace.expSeries_apply_eq, Matrix.smul_mulVec, Matrix.mulVec_smul]
    have hact : (activeProj P) *ᵥ (((c • A) ^ j) *ᵥ v.vec) = ((c • A) ^ j) *ᵥ v.vec := by
      have h2 := congrArg Ket.vec (hpow j)
      simp only [op_mul_ket_vec] at h2
      exact h2
    rw [hact]
  -- Push `hexp` through `activeProj *ᵥ ·` (continuous); the image sum equals the original.
  have hsum1 := hexp.map (leftMulVecCLM (activeProj P)) (leftMulVecCLM (activeProj P)).continuous
  simp only [Function.comp_def, leftMulVecCLM_apply] at hsum1
  have hsum2 := hsum1.congr_fun (fun j => (hterm j).symm)
  -- hsum2 : HasSum (term *ᵥ v) (activeProj *ᵥ (exp *ᵥ v)); hexp : HasSum (term *ᵥ v) (exp *ᵥ v)
  exact congrFun (hexp.unique hsum2).symm i

/-- `exp(c • modesSubShift) = exp(c • costRest_n) * exp(c • HredZMode_n)` (the two pieces
commute, so the exponential of the sum factors; `costRest_n` placed on the LEFT so it can
later be commuted out past `dotTau_n`). -/
theorem exp_smul_modesSubShift_factor (P : ℕ) (n : Fin P) (c : ℂ) :
    NormedSpace.exp (c • modesSubShift P)
      = NormedSpace.exp (c • costRest P n) * NormedSpace.exp (c • HredZMode P (waveVectorABC P n)) := by
  have hcomm : Commute (c • costRest P n) (c • HredZMode P (waveVectorABC P n)) :=
    ((HredZMode_commute_costRest P n).symm.smul_left c).smul_right c
  rw [← NormedSpace.exp_add_of_commute hcomm, ← smul_add]
  congr 2
  rw [modesSubShift_eq_add_costRest P n]; abel

/-- Generic: if `M` preserves the active subspace then so does every power `M^j`. -/
theorem op_pow_preserves_inActiveSubspace (P : ℕ) (M : NQubitOp (2 * P + 2))
    (hM : ∀ w : NQubitKet (2 * P + 2), InActiveSubspace P w → InActiveSubspace P (M * w)) :
    ∀ (j : ℕ) (v : NQubitKet (2 * P + 2)), InActiveSubspace P v → InActiveSubspace P (M ^ j * v) := by
  intro j
  induction j with
  | zero =>
      intro v hv; rw [pow_zero]
      rw [show (1 : NQubitOp (2*P+2)) * v = v by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]]
      exact hv
  | succ j IH => intro v hv; rw [pow_succ', op_mul_op_mul_ket]; exact hM _ (IH v hv)

/-- `exp(c•M)` preserves the active subspace when `M` does (every `(c•M)^j` keeps `v`
active: `(c•M)^j = c^j • M^j`, scalar multiples stay active). -/
theorem exp_smul_preserves_inActiveSubspace_of_op (P : ℕ) (c : ℂ) (M : NQubitOp (2 * P + 2))
    (hM : ∀ w : NQubitKet (2 * P + 2), InActiveSubspace P w → InActiveSubspace P (M * w))
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    InActiveSubspace P (NormedSpace.exp (c • M) * v) := by
  refine exp_smul_preserves_inActiveSubspace P c M v (fun j => ?_)
  have : InActiveSubspace P ((c ^ j) • (M ^ j * v)) :=
    inActiveSubspace_smul _ _ (op_pow_preserves_inActiveSubspace P M hM j v hv)
  rwa [← smul_op_mul_ket, ← smul_pow] at this

/-- `costRest n` preserves the active subspace (`= modesSubShift − HredZMode_n`, both do). -/
theorem costRest_preserves_inActiveSubspace (P : ℕ) (n : Fin P) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) : InActiveSubspace P (costRest P n * w) := by
  unfold costRest
  rw [sub_op_mul_ket]
  exact inActiveSubspace_sub _ _ (modesSubShift_preserves_inActiveSubspace P w hw)
    (HredZMode_preserves_inActiveSubspace P n w hw)

/-- **Cost conjugation reduction (active states).** For active `v`, conjugating the
per-mode `dotTau_n` by the FULL cost exponential `exp(±c•Hred_z_pm)` equals conjugating
by the PER-MODE exponential `exp(±c•HredZMode_n)`: the `costRest_n` factor commutes with
`dotTau_n` and cancels against its inverse, and the central `N_R` phase cancels. -/
theorem costExp_conj_dotTau_eq_modeExp (P : ℕ) (n : Fin P) (c : ℂ) (m : Fin 3 → ℝ)
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    NormedSpace.exp (c • UpperBound.Hred_z_pm false P) *
        (dotTau P (waveVectorABC P n) m *
          (NormedSpace.exp (-c • UpperBound.Hred_z_pm false P) * v))
      = NormedSpace.exp (c • HredZMode P (waveVectorABC P n)) *
          (dotTau P (waveVectorABC P n) m *
            (NormedSpace.exp (-c • HredZMode P (waveVectorABC P n)) * v)) := by
  set Hn := HredZMode P (waveVectorABC P n) with hHn
  set Hr := costRest P n with hHr
  set D := dotTau P (waveVectorABC P n) m with hD
  -- Step 1: rewrite both inner `exp(-c•Hz)*v` on active v to `exp(-c•Hr)*(exp(-c•Hn)*v)`.
  have hinner : NormedSpace.exp (-c • UpperBound.Hred_z_pm false P) * v
      = NormedSpace.exp (-c • Hr) * (NormedSpace.exp (-c • Hn) * v) := by
    rw [exp_smul_Hred_z_pm_eq_modesSubShift_on_active P (-c) v hv,
      exp_smul_modesSubShift_factor P n (-c), op_mul_op_mul_ket]
  rw [hinner]
  -- Step 2: D commutes with exp(-c•Hr): move it left of D.
  have hcommDr : Commute (NormedSpace.exp (-c • Hr)) D :=
    exp_smul_commute_of_commute (-c) Hr D (costRest_commute_dotTau P n m)
  rw [← op_mul_op_mul_ket D, ← hcommDr.eq, op_mul_op_mul_ket]
  -- Goal now: exp(c•Hz) * (exp(-c•Hr) * (D * (exp(-c•Hn) * v))) = RHS.
  -- The argument exp(-c•Hr)*(D*(exp(-c•Hn)*v)) is active.
  have hactInner : InActiveSubspace P (NormedSpace.exp (-c • Hn) * v) :=
    exp_smul_preserves_inActiveSubspace_of_op P (-c) Hn
      (fun w hw => HredZMode_preserves_inActiveSubspace P n w hw) v hv
  have hactD : InActiveSubspace P (D * (NormedSpace.exp (-c • Hn) * v)) :=
    dotTau_preserves_inActiveSubspace P n m _ hactInner
  have hactArg : InActiveSubspace P
      (NormedSpace.exp (-c • Hr) * (D * (NormedSpace.exp (-c • Hn) * v))) :=
    exp_smul_preserves_inActiveSubspace_of_op P (-c) Hr
      (fun w hw => costRest_preserves_inActiveSubspace P n w hw) _ hactD
  -- Step 3: split exp(c•Hz) on the active argument.
  rw [exp_smul_Hred_z_pm_eq_modesSubShift_on_active P c _ hactArg,
    exp_smul_modesSubShift_factor P n c, op_mul_op_mul_ket]
  -- Goal: exp(c•Hr) * (exp(c•Hn) * (exp(-c•Hr) * (D * (exp(-c•Hn)*v)))) = RHS.
  -- exp(c•Hn) commutes with exp(-c•Hr): swap them.
  have hcommHnHr : Commute (NormedSpace.exp (c • Hn)) (NormedSpace.exp (-c • Hr)) :=
    (((HredZMode_commute_costRest P n).smul_left c).smul_right (-c)).exp_left.exp_right
  rw [← op_mul_op_mul_ket (NormedSpace.exp (c • Hn)), hcommHnHr.eq,
    op_mul_op_mul_ket]
  -- Fold `costRest P n → Hr`, left-associate, then collapse `exp(c•Hr)*exp(-c•Hr) = 1`.
  change NormedSpace.exp (c • Hr) *
      (NormedSpace.exp (-c • Hr) * (NormedSpace.exp (c • Hn) * (D * (NormedSpace.exp (-c • Hn) * v))))
    = NormedSpace.exp (c • Hn) * (D * (NormedSpace.exp (-c • Hn) * v))
  rw [← op_mul_op_mul_ket (NormedSpace.exp (c • Hr))]
  have hinv : NormedSpace.exp (c • Hr) * NormedSpace.exp (-c • Hr)
      = (1 : NQubitOp (2*P+2)) := by
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl _).smul_left c |>.smul_right (-c)),
      show c • Hr + -c • Hr = (0 : NQubitOp (2*P+2)) by rw [neg_smul]; abel,
      NormedSpace.exp_zero]
  rw [hinv]
  ext i; simp [op_mul_ket_vec]

-- ----------------------------------------------------------------------------
-- Mixer-side analogue of the cost conjugation reduction (shift = 2, HredXMode).
-- ----------------------------------------------------------------------------

/-- The active-subspace mixer operator `H''_x = (∑ HredXMode) − 2·1`. -/
def modesSubShiftX (P : ℕ) : NQubitOp (2*P+2) :=
  (∑ n : Fin P, HredXMode P (waveVectorABC P n)) - ((2 : ℂ)) • (1 : NQubitOp (2*P+2))

/-- `modesSubShiftX` preserves the active subspace. -/
theorem modesSubShiftX_preserves_inActiveSubspace (P : ℕ) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) : InActiveSubspace P (modesSubShiftX P * w) := by
  have hsum : InActiveSubspace P ((∑ n : Fin P, HredXMode P (waveVectorABC P n)) * w) :=
    inActiveSubspace_op_sum Finset.univ _ w
      (fun n _ => HredXMode_preserves_inActiveSubspace P n w hw)
  have hscal : InActiveSubspace P (((2 : ℂ)) • (1 : NQubitOp (2*P+2)) * w) := by
    rw [smul_op_mul_ket]
    refine inActiveSubspace_smul _ _ ?_
    rw [show (1 : NQubitOp (2*P+2)) * w = w by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]]
    exact hw
  unfold modesSubShiftX
  rw [sub_op_mul_ket]
  exact inActiveSubspace_sub _ _ hsum hscal

/-- On active `w`, `Hred_x_op * w = modesSubShiftX * w` (`HredXDecomp_active` rearranged). -/
theorem Hred_x_op_eq_modesSubShiftX_on_active (P : ℕ) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) :
    (UpperBound.Hred_x_op P) * w = modesSubShiftX P * w := by
  have h := HredXDecomp_active P w hw
  rw [add_op_mul_ket] at h
  unfold modesSubShiftX
  rw [sub_op_mul_ket, ← h]
  ext i; simp [Ket.add_vec]

set_option maxHeartbeats 800000 in
-- Raised: `pow_succ'`/`op_mul_op_mul_ket` defeq on the big-operator `Hred_x_op`.
theorem Hred_x_op_pow_preserves_inActiveSubspace (P : ℕ) :
    ∀ (j : ℕ) (v : NQubitKet (2 * P + 2)), InActiveSubspace P v →
    InActiveSubspace P ((UpperBound.Hred_x_op P) ^ j * v) := by
  intro j
  induction j with
  | zero =>
      intro v hv; rw [pow_zero]
      rw [show (1 : NQubitOp (2*P+2)) * v = v by ext i; simp [op_mul_ket_vec, Matrix.one_mulVec]]
      exact hv
  | succ j IH =>
      intro v hv
      rw [pow_succ', op_mul_op_mul_ket]
      exact Hred_x_op_preserves_inActiveSubspace P _ (IH v hv)

set_option maxHeartbeats 800000 in
-- Raised: `pow_succ'`/`op_mul_op_mul_ket` defeq on the big-operator `Hred_x_op`.
theorem Hred_x_op_pow_eq_modesSubShiftX_on_active (P : ℕ) :
    ∀ (j : ℕ) (v : NQubitKet (2 * P + 2)), InActiveSubspace P v →
    (UpperBound.Hred_x_op P) ^ j * v = (modesSubShiftX P) ^ j * v := by
  intro j
  induction j with
  | zero => intro v _; rw [pow_zero, pow_zero]
  | succ j IH =>
      intro v hv
      have hact : InActiveSubspace P ((modesSubShiftX P) ^ j * v) := by
        rw [← IH v hv]; exact Hred_x_op_pow_preserves_inActiveSubspace P j v hv
      rw [pow_succ', op_mul_op_mul_ket, IH v hv,
        Hred_x_op_eq_modesSubShiftX_on_active P _ hact, ← op_mul_op_mul_ket, ← pow_succ']

/-- For active `v`, `exp(c • Hred_x_op) * v = exp(c • modesSubShiftX) * v`. -/
theorem exp_smul_Hred_x_op_eq_modesSubShiftX_on_active (P : ℕ) (c : ℂ)
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    (NormedSpace.exp (c • UpperBound.Hred_x_op P)) * v
      = (NormedSpace.exp (c • modesSubShiftX P)) * v := by
  refine exp_op_mul_ket_eq_of_pow _ _ v (fun j => ?_)
  rw [smul_pow, smul_pow, smul_op_mul_ket, smul_op_mul_ket,
    Hred_x_op_pow_eq_modesSubShiftX_on_active P j v hv]

/-- The mixer "rest" operator for mode `n`: `Hrest_x n = modesSubShiftX − HredXMode k_n`. -/
def costRestX (P : ℕ) (n : Fin P) : NQubitOp (2*P+2) :=
  modesSubShiftX P - HredXMode P (waveVectorABC P n)

theorem modesSubShiftX_eq_add_costRestX (P : ℕ) (n : Fin P) :
    modesSubShiftX P = HredXMode P (waveVectorABC P n) + costRestX P n := by
  unfold costRestX; abel

theorem HredXMode_commute_costRestX (P : ℕ) (n : Fin P) :
    Commute (HredXMode P (waveVectorABC P n)) (costRestX P n) := by
  unfold costRestX modesSubShiftX
  refine Commute.sub_right (Commute.sub_right ?_ ?_) ?_
  · refine Commute.sum_right _ _ _ (fun m _ => ?_)
    by_cases hmn : m = n
    · subst hmn; exact Commute.refl _
    · exact (HredXMode_commute_HredXMode_cross P n m (fun h => hmn h.symm))
  · exact (Commute.one_right _).smul_right _
  · exact Commute.refl _

theorem costRestX_eq_erase_sum (P : ℕ) (n : Fin P) :
    costRestX P n = (∑ m ∈ Finset.univ.erase n, HredXMode P (waveVectorABC P m))
      - ((2 : ℂ)) • (1 : NQubitOp (2*P+2)) := by
  unfold costRestX modesSubShiftX
  have h : (∑ m : Fin P, HredXMode P (waveVectorABC P m))
      = HredXMode P (waveVectorABC P n)
        + ∑ m ∈ Finset.univ.erase n, HredXMode P (waveVectorABC P m) :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ n)).symm
  rw [h]; abel

theorem costRestX_commute_dotTau (P : ℕ) (n : Fin P) (u : Fin 3 → ℝ) :
    Commute (costRestX P n) (dotTau P (waveVectorABC P n) u) := by
  rw [costRestX_eq_erase_sum]
  refine Commute.sub_left ?_ ((Commute.one_left _).smul_left _)
  refine Commute.sum_left _ _ _ (fun m hm => ?_)
  exact HredXMode_commute_dotTau_cross P m n (Finset.ne_of_mem_erase hm) u

theorem costRestX_preserves_inActiveSubspace (P : ℕ) (n : Fin P) (w : NQubitKet (2 * P + 2))
    (hw : InActiveSubspace P w) : InActiveSubspace P (costRestX P n * w) := by
  unfold costRestX
  rw [sub_op_mul_ket]
  exact inActiveSubspace_sub _ _ (modesSubShiftX_preserves_inActiveSubspace P w hw)
    (HredXMode_preserves_inActiveSubspace P n w hw)

theorem exp_smul_modesSubShiftX_factor (P : ℕ) (n : Fin P) (c : ℂ) :
    NormedSpace.exp (c • modesSubShiftX P)
      = NormedSpace.exp (c • costRestX P n) * NormedSpace.exp (c • HredXMode P (waveVectorABC P n)) := by
  have hcomm : Commute (c • costRestX P n) (c • HredXMode P (waveVectorABC P n)) :=
    ((HredXMode_commute_costRestX P n).symm.smul_left c).smul_right c
  rw [← NormedSpace.exp_add_of_commute hcomm, ← smul_add]
  congr 2
  rw [modesSubShiftX_eq_add_costRestX P n]; abel

/-- **Mixer conjugation reduction (active states).** Mirror of the cost reduction. -/
theorem mixerExp_conj_dotTau_eq_modeExp (P : ℕ) (n : Fin P) (c : ℂ) (m : Fin 3 → ℝ)
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    NormedSpace.exp (c • UpperBound.Hred_x_op P) *
        (dotTau P (waveVectorABC P n) m *
          (NormedSpace.exp (-c • UpperBound.Hred_x_op P) * v))
      = NormedSpace.exp (c • HredXMode P (waveVectorABC P n)) *
          (dotTau P (waveVectorABC P n) m *
            (NormedSpace.exp (-c • HredXMode P (waveVectorABC P n)) * v)) := by
  set Hn := HredXMode P (waveVectorABC P n) with hHn
  set Hr := costRestX P n with hHr
  set D := dotTau P (waveVectorABC P n) m with hD
  have hinner : NormedSpace.exp (-c • UpperBound.Hred_x_op P) * v
      = NormedSpace.exp (-c • Hr) * (NormedSpace.exp (-c • Hn) * v) := by
    rw [exp_smul_Hred_x_op_eq_modesSubShiftX_on_active P (-c) v hv,
      exp_smul_modesSubShiftX_factor P n (-c), op_mul_op_mul_ket]
  rw [hinner]
  have hcommDr : Commute (NormedSpace.exp (-c • Hr)) D :=
    exp_smul_commute_of_commute (-c) Hr D (costRestX_commute_dotTau P n m)
  rw [← op_mul_op_mul_ket D, ← hcommDr.eq, op_mul_op_mul_ket]
  have hactInner : InActiveSubspace P (NormedSpace.exp (-c • Hn) * v) :=
    exp_smul_preserves_inActiveSubspace_of_op P (-c) Hn
      (fun w hw => HredXMode_preserves_inActiveSubspace P n w hw) v hv
  have hactD : InActiveSubspace P (D * (NormedSpace.exp (-c • Hn) * v)) :=
    dotTau_preserves_inActiveSubspace P n m _ hactInner
  have hactArg : InActiveSubspace P
      (NormedSpace.exp (-c • Hr) * (D * (NormedSpace.exp (-c • Hn) * v))) :=
    exp_smul_preserves_inActiveSubspace_of_op P (-c) Hr
      (fun w hw => costRestX_preserves_inActiveSubspace P n w hw) _ hactD
  rw [exp_smul_Hred_x_op_eq_modesSubShiftX_on_active P c _ hactArg,
    exp_smul_modesSubShiftX_factor P n c, op_mul_op_mul_ket]
  have hcommHnHr : Commute (NormedSpace.exp (c • Hn)) (NormedSpace.exp (-c • Hr)) :=
    (((HredXMode_commute_costRestX P n).smul_left c).smul_right (-c)).exp_left.exp_right
  rw [← op_mul_op_mul_ket (NormedSpace.exp (c • Hn)), hcommHnHr.eq, op_mul_op_mul_ket]
  change NormedSpace.exp (c • Hr) *
      (NormedSpace.exp (-c • Hr) * (NormedSpace.exp (c • Hn) * (D * (NormedSpace.exp (-c • Hn) * v))))
    = NormedSpace.exp (c • Hn) * (D * (NormedSpace.exp (-c • Hn) * v))
  rw [← op_mul_op_mul_ket (NormedSpace.exp (c • Hr))]
  have hinv : NormedSpace.exp (c • Hr) * NormedSpace.exp (-c • Hr)
      = (1 : NQubitOp (2*P+2)) := by
    rw [← NormedSpace.exp_add_of_commute ((Commute.refl _).smul_left c |>.smul_right (-c)),
      show c • Hr + -c • Hr = (0 : NQubitOp (2*P+2)) by rw [neg_smul]; abel,
      NormedSpace.exp_zero]
  rw [hinv]
  ext i; simp [op_mul_ket_vec]

end

end QAOA.IsingChain.JordanWigner
