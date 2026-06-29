import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain
import Mathlib.Algebra.Ring.Parity

/-!
# GroundStateEnergy — `E_gs(Hred_z_pm false) = -(4P+2)` (1906.08948v2 §IV l.715–725)

This file proves the **ground-state energy** of the ABC reduced cost
Hamiltonian `Hred_z_pm false P` on the `N_R = 2P+2`-site chain is exactly
`E_gs = -(4P + 2)`. It supplies the variational lower bound consumed by A6
(`ResidualEnergyBound.lean`).

Source pin: arXiv:1906.08948v2 §IV l.715–725. The source asserts (l.718):
*"the inequality becomes non-trivial if ABC are used, since
`E^{(-)}_{gs} = −4P − 2` due to the frustrating boundary term `J_b = −1`"*.
The source asserts the value without proof; this file supplies the elementary
classical-bitstring minimization that justifies it.

## Strategy

`Hred_z_pm false P` is **diagonal in the computational basis** with a
closed-form eigenvalue
`eigenvalueOnBasis P z = (Σ_k (s_k s_{k+1} − 1)) + (−s_{2P+1} s_0 − 1)`
where `s_j = classicalSpin z j ∈ {+1, −1}`. Body bonds contribute `−2` per
disagreement, `0` per agreement; the **frustrating** ABC boundary contributes
`−2` per agreement, `0` per disagreement. The minimum is the saturating
combination, achieved by the alternating string `01010…`.

The key combinatorial step is the **cyclic parity lemma**: on a cycle, the
number of `±1` sign flips along a closed walk is even, proved via the
spectator identity `∏_k s_k * s_{k+1} = (∏_j s_j)² = 1` (each `s_j`
appears in exactly two bonds of the cycle).
-/

namespace QAOA.IsingChain.UpperBound

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- D1 — Closed-form diagonal eigenvalue
-- ============================================================================

/-- Closed-form eigenvalue of `Hred_z_pm false P` on the computational-basis
ket `|z⟩`, as a real number.

`eigenvalueOnBasis P z = Σ_{k : Fin (2P+1)} (s_{k.castSucc} · s_{k.succ} − 1)
  + (−s_{2P+1} · s_0 − 1)`,

where `s_j := IsingModel.classicalSpin z j ∈ {+1, −1}`.

Source pin: arXiv:1906.08948v2 §IV l.715–725. -/
def eigenvalueOnBasis (P : ℕ) (z : Qubits.BitString (2*P+2)) : ℝ :=
  (∑ k : Fin (2*P+1),
      (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1)) +
    (-(IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
          IsingModel.classicalSpin z (0 : Fin (2*P+2))) - 1)

-- ============================================================================
-- D2 — Combinatorial helpers
-- ============================================================================

/-- Number of *body* bonds on which the bitstring `z` flips: count of
`k : Fin (2P+1)` for which `z k.castSucc ≠ z k.succ`. -/
def bodyDisagreeCount (P : ℕ) (z : Qubits.BitString (2*P+2)) : ℕ :=
  ((Finset.univ : Finset (Fin (2*P+1))).filter
    (fun k ↦ z (k.castSucc : Fin (2*P+2)) ≠ z (k.succ : Fin (2*P+2)))).card

/-- The alternating bitstring `0, 1, 0, 1, …` of length `n`.

At index `j`, returns `j.val % 2 ∈ Fin 2`. -/
def alternatingBitString (n : ℕ) : Qubits.BitString n :=
  fun j ↦ ⟨j.val % 2, Nat.mod_lt _ (by decide : (0 : ℕ) < 2)⟩

-- ============================================================================
-- Local site-arithmetic helpers
-- ============================================================================

/-- For `k : Fin (2P+1)`, `nextSite k.castSucc = k.succ` inside `Fin (2P+2)`. -/
private lemma nextSite_castSucc {P : ℕ} (k : Fin (2*P+1)) :
    IsingModel.nextSite (k.castSucc : Fin (2*P+2)) =
      (k.succ : Fin (2*P+2)) := by
  apply Fin.ext
  rw [IsingModel.nextSite_val, Fin.val_succ, Fin.val_castSucc]
  have hk : k.val + 1 < 2*P + 2 := by omega
  exact Nat.mod_eq_of_lt hk

/-- For the boundary, `nextSite (Fin.last (2P+1)) = 0` inside `Fin (2P+2)`. -/
private lemma nextSite_last (P : ℕ) :
    IsingModel.nextSite (Fin.last (2*P+1) : Fin (2*P+2)) =
      (0 : Fin (2*P+2)) := by
  apply Fin.ext
  simp [IsingModel.nextSite_val, Fin.val_last]

-- ============================================================================
-- D3 — Diagonalization
-- ============================================================================

/-- Identity action on a ket: `(1 : NQubitOp _) * ψ = ψ`. -/
private lemma one_op_mul_ket {N : ℕ} (ψ : Qubits.NQubitKet N) :
    (1 : Qubits.NQubitOp N) * ψ = ψ := by
  apply Ket.ext
  intro j
  change (1 : Qubits.NQubitOp N).mulVec ψ.vec j = ψ.vec j
  simp [Matrix.one_mulVec]

/-- Action of each body bond `(chain k.castSucc - 1)` on `|z⟩` as a scalar. -/
private lemma body_bond_apply_basis (P : ℕ) (z : Qubits.BitString (2*P+2))
    (k : Fin (2*P+1)) :
    (IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
      (1 : Qubits.NQubitOp (2*P+2))) *
        Qubits.computationalBasisKet (2*P+2) z =
      (((IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1 : ℝ) : ℂ)) •
        Qubits.computationalBasisKet (2*P+2) z := by
  rw [sub_op_mul_ket,
      IsingModel.chainPairInteraction_apply_computationalBasisKet,
      nextSite_castSucc, one_op_mul_ket]
  -- Goal: cast(s_k*s_{k+1}) • ψ - ψ = cast(s_k*s_{k+1} - 1) • ψ.
  apply Ket.ext
  intro i
  simp only [Ket.sub_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

/-- Action of the body operator on `|z⟩`: a sum-of-scalars times `|z⟩`. -/
private lemma Hred_z_body_apply_computationalBasisKet (P : ℕ)
    (z : Qubits.BitString (2*P+2)) :
    Hred_z_body P * Qubits.computationalBasisKet (2*P+2) z =
      ((((∑ k : Fin (2*P+1),
          (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
            IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) -
              1) : ℝ)) : ℂ)) •
        Qubits.computationalBasisKet (2*P+2) z := by
  classical
  unfold Hred_z_body
  -- Pull out the sum.
  apply Ket.ext
  intro i
  rw [sum_op_mul_ket_vec]
  -- Per-bond identity
  have hk_term : ∀ k : Fin (2*P+1),
      ((IsingModel.chainPairInteraction (k.castSucc : Fin (2*P+2)) -
        (1 : Qubits.NQubitOp (2*P+2))) *
          Qubits.computationalBasisKet (2*P+2) z : Qubits.NQubitKet (2*P+2)).vec i =
      (((IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1 : ℝ) : ℂ) *
        (Qubits.computationalBasisKet (2*P+2) z).vec i) := by
    intro k
    rw [body_bond_apply_basis]
    rfl
  rw [Finset.sum_congr rfl (fun k _ ↦ hk_term k)]
  -- RHS coordinatewise
  rw [Ket.smul_vec]
  show ∑ k : Fin (2*P+1),
        ((((IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
            IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1 : ℝ)) : ℂ) *
          (Qubits.computationalBasisKet (2*P+2) z).vec i) =
      ((((∑ k : Fin (2*P+1),
          (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
            IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1) : ℝ)) : ℂ)) *
        (Qubits.computationalBasisKet (2*P+2) z).vec i
  rw [← Finset.sum_mul]
  congr 1
  push_cast; rfl

/-- Action of the boundary operator (ABC, `s = false`) on `|z⟩`: scalar times `|z⟩`. -/
private lemma Hred_z_boundary_false_apply_computationalBasisKet (P : ℕ)
    (z : Qubits.BitString (2*P+2)) :
    Hred_z_boundary false P * Qubits.computationalBasisKet (2*P+2) z =
      ((((-(IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
            IsingModel.classicalSpin z (0 : Fin (2*P+2))) - 1 : ℝ)) : ℂ)) •
        Qubits.computationalBasisKet (2*P+2) z := by
  unfold Hred_z_boundary
  rw [show (if (false : Bool) then (1 : ℂ) else (-1 : ℂ)) = -1 from rfl]
  rw [sub_op_mul_ket, smul_op_mul_ket,
      IsingModel.chainPairInteraction_apply_computationalBasisKet,
      nextSite_last, one_op_mul_ket, Ket.smul_smul]
  apply Ket.ext
  intro i
  simp only [Ket.sub_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

/-- **Diagonalization.** The reduced cost Hamiltonian `Hred_z_pm false P`
acts diagonally on a computational-basis ket with eigenvalue
`eigenvalueOnBasis P z`.

Source pin: arXiv:1906.08948v2 §IV l.715–725 (direct unfolding of the
operator definition). -/
theorem Hred_z_pm_false_apply_computationalBasisKet (P : ℕ)
    (z : Qubits.BitString (2*P+2)) :
    Hred_z_pm false P * Qubits.computationalBasisKet (2*P+2) z =
      (((eigenvalueOnBasis P z : ℝ) : ℂ)) •
        Qubits.computationalBasisKet (2*P+2) z := by
  unfold Hred_z_pm eigenvalueOnBasis
  rw [add_op_mul_ket, Hred_z_body_apply_computationalBasisKet,
      Hred_z_boundary_false_apply_computationalBasisKet]
  apply Ket.ext
  intro i
  simp only [Ket.add_vec, Ket.smul_vec, Pi.smul_apply, smul_eq_mul]
  push_cast; ring

-- ============================================================================
-- D4 — Closed-form rewrite via signed counts
-- ============================================================================

/-- Per-bond eigenvalue identity: `spinValue b₁ · spinValue b₂ = 1` if
`b₁ = b₂`, `-1` if not. -/
private lemma spinValue_mul_spinValue (b₁ b₂ : Fin 2) :
    IsingModel.spinValue b₁ * IsingModel.spinValue b₂ =
      if b₁ = b₂ then (1 : ℝ) else (-1 : ℝ) := by
  fin_cases b₁ <;> fin_cases b₂ <;> simp [IsingModel.spinValue]

/-- Body-sum identity. The body part of `eigenvalueOnBasis` equals
`−2 · bodyDisagreeCount P z`. -/
private lemma bodySum_eq (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    (∑ k : Fin (2*P+1),
      (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1)) =
      -2 * (bodyDisagreeCount P z : ℝ) := by
  classical
  -- Per-bond: 0 if agree, −2 if disagree.
  have hterm : ∀ k : Fin (2*P+1),
      IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) - 1 =
        if z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2))
          then (0 : ℝ) else (-2 : ℝ) := by
    intro k
    unfold IsingModel.classicalSpin
    rw [spinValue_mul_spinValue]
    split_ifs <;> norm_num
  rw [Finset.sum_congr rfl (fun k _ ↦ hterm k)]
  -- Split via agree/disagree.
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const]
  -- Now ((Finset.univ.filter (fun k ↦ ¬ ...)).card : ℝ) • (-2 : ℝ).
  rw [nsmul_eq_mul]
  -- bodyDisagreeCount uses `≠`, the same as `¬ =`. Cast and multiply.
  show ((((Finset.univ : Finset (Fin (2*P+1))).filter
        (fun k ↦ ¬ z (k.castSucc : Fin (2*P+2)) =
                  z (k.succ : Fin (2*P+2)))).card : ℕ) : ℝ) * (-2 : ℝ) =
      -2 * (bodyDisagreeCount P z : ℝ)
  unfold bodyDisagreeCount
  ring

/-- Boundary-term identity: `−s_{2P+1} · s_0 − 1` is `−2` if the boundary
spins agree, `0` if they disagree. -/
private lemma boundaryTerm_eq (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    -(IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
        IsingModel.classicalSpin z (0 : Fin (2*P+2))) - 1 =
      if z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
        then (-2 : ℝ) else (0 : ℝ) := by
  unfold IsingModel.classicalSpin
  rw [spinValue_mul_spinValue]
  split_ifs <;> norm_num

/-- Closed-form rewrite of `eigenvalueOnBasis` via signed counts. -/
private lemma eigenvalueOnBasis_eq (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    eigenvalueOnBasis P z =
      -2 * (bodyDisagreeCount P z : ℝ) -
        2 * (if z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
              then (1 : ℝ) else 0) := by
  unfold eigenvalueOnBasis
  rw [bodySum_eq, boundaryTerm_eq]
  split_ifs <;> ring

-- ============================================================================
-- D5 — Body disagreement is at most 2P+1
-- ============================================================================

/-- The body-disagree count is at most `2P + 1` (the number of body bonds). -/
private lemma bodyDisagreeCount_le (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    bodyDisagreeCount P z ≤ 2*P + 1 := by
  unfold bodyDisagreeCount
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Finset.card_univ]

-- ============================================================================
-- D6 — Cyclic parity lemma
-- ============================================================================

/-- Each spin value is `±1`. -/
private lemma spinValue_sq (b : Fin 2) : IsingModel.spinValue b * IsingModel.spinValue b = 1 := by
  have := spinValue_mul_spinValue b b
  simpa using this

/-- The body product equals `(-1)^T` where `T` is the body-disagree count. -/
private lemma body_prod_eq (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    (∏ k : Fin (2*P+1),
        (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)))) =
      (-1 : ℝ) ^ (bodyDisagreeCount P z) := by
  classical
  have hterm : ∀ k : Fin (2*P+1),
      IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)) =
        if z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2))
          then (1 : ℝ) else (-1 : ℝ) := by
    intro k
    unfold IsingModel.classicalSpin
    exact spinValue_mul_spinValue _ _
  rw [Finset.prod_congr rfl (fun k _ ↦ hterm k)]
  -- Split product via agree/disagree filters.
  rw [show (∏ k : Fin (2*P+1),
        (if z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2))
            then (1 : ℝ) else (-1 : ℝ))) =
      ((∏ _k ∈ (Finset.univ : Finset (Fin (2*P+1))).filter
            (fun k ↦ z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2))),
            (1 : ℝ)) *
        (∏ _k ∈ (Finset.univ : Finset (Fin (2*P+1))).filter
            (fun k ↦ ¬ z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2))),
            (-1 : ℝ))) from ?_]
  · rw [Finset.prod_const_one, one_mul, Finset.prod_const]
    rfl
  · -- Use Finset.prod_filter_mul_prod_filter_not on the conditional.
    rw [← Finset.prod_filter_mul_prod_filter_not (Finset.univ : Finset (Fin (2*P+1)))
        (fun k ↦ z (k.castSucc : Fin (2*P+2)) = z (k.succ : Fin (2*P+2)))]
    congr 1
    · apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      simp [hk.2]
    · apply Finset.prod_congr rfl
      intro k hk
      rw [Finset.mem_filter] at hk
      simp [hk.2]

/-- The boundary product is `(-1)^B` where `B = 1` if boundary spins differ. -/
private lemma boundary_prod_eq (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
        IsingModel.classicalSpin z (0 : Fin (2*P+2)) =
      (-1 : ℝ) ^ (if z (Fin.last (2*P+1) : Fin (2*P+2)) =
                      z (0 : Fin (2*P+2)) then 0 else 1) := by
  unfold IsingModel.classicalSpin
  rw [spinValue_mul_spinValue]
  by_cases hk : z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
  · simp [hk]
  · simp [hk]

/-- Cyclic combined product: the product `∏_k s_{k.castSucc} * s_{k.succ}` times
the boundary product `s_{2P+1} * s_0` equals `1`.

Reason: each `s_j` for `j : Fin (2P+2)` appears exactly twice (once as
`s_{k.castSucc}` for some `k`, once as `s_{k.succ}` for some `k`, or in the
boundary), so the combined product is `(∏_j s_j)^2 = 1`. -/
private lemma cyclic_combined_prod_eq_one (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    (∏ k : Fin (2*P+1),
        (IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2)) *
          IsingModel.classicalSpin z (k.succ : Fin (2*P+2)))) *
      (IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
        IsingModel.classicalSpin z (0 : Fin (2*P+2))) = 1 := by
  classical
  -- Strategy: rewrite the body product as the product of pairs and split.
  -- Each k contributes s_{k.castSucc} * s_{k.succ}. Then add s_last * s_0.
  -- Combined = (∏_k s_{k.castSucc}) * (∏_k s_{k.succ}) * s_last * s_0.
  rw [Finset.prod_mul_distrib]
  -- Now rearrange: ∏_k s_{k.castSucc} * s_0 = ∏_{j : Fin (2P+2)} s_j
  -- (using Fin.prod_univ_castSucc: ∏_{j : Fin (n+1)} = (∏_k : Fin n, f k.castSucc) * f (Fin.last n)).
  -- Wait, we want all of Fin (2P+2) = Fin ((2P+1)+1).
  -- ∏_{j : Fin ((2P+1)+1)} f j = (∏_{k : Fin (2P+1)} f k.castSucc) * f (Fin.last (2P+1)).
  -- So (∏_{k : Fin (2P+1)} s_{k.castSucc}) * s_{Fin.last (2P+1)} = ∏_j s_j.
  -- Similarly ∏_{j : Fin ((2P+1)+1)} f j = f 0 * ∏_{k : Fin (2P+1)} f k.succ.
  -- So s_0 * (∏_{k : Fin (2P+1)} s_{k.succ}) = ∏_j s_j.
  have hcast :
      (∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2))) *
        IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) =
      (∏ j : Fin (2*P+2), IsingModel.classicalSpin z j) := by
    rw [← Fin.prod_univ_castSucc (n := 2*P+1)
        (f := fun j : Fin (2*P+2) ↦ IsingModel.classicalSpin z j)]
  have hsucc :
      IsingModel.classicalSpin z (0 : Fin (2*P+2)) *
        (∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.succ : Fin (2*P+2))) =
      (∏ j : Fin (2*P+2), IsingModel.classicalSpin z j) := by
    rw [← Fin.prod_univ_succ (n := 2*P+1)
        (f := fun j : Fin (2*P+2) ↦ IsingModel.classicalSpin z j)]
  -- LHS: (∏_k s_{k.castSucc}) * (∏_k s_{k.succ}) * (s_last * s_0)
  --    = ((∏_k s_{k.castSucc}) * s_last) * (s_0 * (∏_k s_{k.succ}))
  --    = (∏_j s_j) * (∏_j s_j) = (∏_j s_j)^2.
  have hrearrange :
      ((∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2))) *
        (∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.succ : Fin (2*P+2)))) *
      (IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2)) *
        IsingModel.classicalSpin z (0 : Fin (2*P+2))) =
      ((∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.castSucc : Fin (2*P+2))) *
          IsingModel.classicalSpin z (Fin.last (2*P+1) : Fin (2*P+2))) *
      (IsingModel.classicalSpin z (0 : Fin (2*P+2)) *
        (∏ k : Fin (2*P+1), IsingModel.classicalSpin z (k.succ : Fin (2*P+2)))) := by
    ring
  rw [hrearrange, hcast, hsucc]
  -- Now: (∏_j s_j) * (∏_j s_j) = 1 since each s_j is ±1 hence (s_j)^2 = 1.
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro j _
  exact spinValue_sq (z j)

/-- **Cyclic parity lemma.** For any bitstring `z` on the `2P+2`-site cycle,
the total number of sign-flips along the cyclic walk is even:
`bodyDisagreeCount P z + B` is even, where `B = 1` iff the boundary spins
differ. -/
private lemma cyclic_flip_parity_even (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    Even (bodyDisagreeCount P z +
      (if z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
        then 0 else 1)) := by
  set T : ℕ := bodyDisagreeCount P z
  set B : ℕ :=
    if z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
      then 0 else 1
  -- (-1)^T * (-1)^B = 1 by `cyclic_combined_prod_eq_one`, body_prod_eq, boundary_prod_eq.
  have hprod : (-1 : ℝ) ^ T * (-1 : ℝ) ^ B = 1 := by
    have := cyclic_combined_prod_eq_one P z
    rw [body_prod_eq, boundary_prod_eq] at this
    exact this
  -- (-1)^(T+B) = 1 ⟹ Even (T+B).
  have hpow : (-1 : ℝ) ^ (T + B) = 1 := by rw [pow_add]; exact hprod
  -- Use Nat.even_iff: in ℝ, neg_one_pow = 1 iff even exponent.
  -- We use the standard equivalence via Nat.neg_one_pow_eq_one_iff_even.
  by_contra hne
  rw [Nat.not_even_iff_odd] at hne
  rcases hne with ⟨m, hm⟩
  rw [hm] at hpow
  have : (-1 : ℝ) ^ (2*m+1) = -1 := by
    rw [pow_add, pow_mul, pow_one]
    ring
  rw [this] at hpow
  linarith

-- ============================================================================
-- D7 — Eigenvalue lower bound
-- ============================================================================

/-- **Lower bound** on the diagonal eigenvalue: `eigenvalueOnBasis P z ≥ −(4P+2)`.

Combines D4 (closed form), D5 (`T ≤ 2P+1`), and D6 (`T + B` even).

Source pin: arXiv:1906.08948v2 §IV l.718 — `E^{(-)}_{gs} = −4P − 2`. -/
theorem eigenvalueOnBasis_lower_bound (P : ℕ) (z : Qubits.BitString (2*P+2)) :
    -(4*P + 2 : ℝ) ≤ eigenvalueOnBasis P z := by
  classical
  rw [eigenvalueOnBasis_eq]
  have hT_le : bodyDisagreeCount P z ≤ 2*P + 1 := bodyDisagreeCount_le P z
  have hpar := cyclic_flip_parity_even P z
  by_cases hk : z (Fin.last (2*P+1) : Fin (2*P+2)) = z (0 : Fin (2*P+2))
  · -- agree case: [agree] = 1, B = 0, so T + 0 = T is even.
    simp only [if_pos hk] at hpar
    rw [if_pos hk]
    have hTle2P : bodyDisagreeCount P z ≤ 2*P := by
      rcases hpar with ⟨k, hk2⟩
      have hT_even : bodyDisagreeCount P z = 2 * k := by omega
      omega
    have hcast : (bodyDisagreeCount P z : ℝ) ≤ 2*P := by exact_mod_cast hTle2P
    nlinarith
  · -- disagree case: [agree] = 0.
    rw [if_neg hk]
    have hcast : (bodyDisagreeCount P z : ℝ) ≤ 2*P + 1 := by exact_mod_cast hT_le
    nlinarith

-- ============================================================================
-- D8 — Witness: alternating bitstring attains the bound
-- ============================================================================

/-- For `alternatingBitString n`, the bit at index `j` is `j.val % 2`. -/
@[simp] private lemma alternatingBitString_apply (n : ℕ) (j : Fin n) :
    (alternatingBitString n) j = ⟨j.val % 2, Nat.mod_lt _ (by decide)⟩ := rfl

/-- For `k : Fin (2P+1)`, the alternating bit at `k.castSucc` differs from that
at `k.succ`. -/
private lemma alternatingBitString_body_disagree (P : ℕ) (k : Fin (2*P+1)) :
    (alternatingBitString (2*P+2)) (k.castSucc : Fin (2*P+2)) ≠
      (alternatingBitString (2*P+2)) (k.succ : Fin (2*P+2)) := by
  rw [alternatingBitString_apply, alternatingBitString_apply]
  intro h
  have hval : (k.castSucc : Fin (2*P+2)).val % 2 = (k.succ : Fin (2*P+2)).val % 2 := by
    have := Fin.val_eq_of_eq h
    exact this
  have h1 : (k.castSucc : Fin (2*P+2)).val = k.val := Fin.val_castSucc k
  have h2 : (k.succ : Fin (2*P+2)).val = k.val + 1 := Fin.val_succ k
  rw [h1, h2] at hval
  omega

/-- For the alternating bitstring on `2P+2` sites, the body sees all-disagree:
`bodyDisagreeCount P (alternatingBitString (2*P+2)) = 2*P + 1`. -/
private lemma alternatingBitString_bodyDisagreeCount (P : ℕ) :
    bodyDisagreeCount P (alternatingBitString (2*P+2)) = 2*P + 1 := by
  unfold bodyDisagreeCount
  rw [show (Finset.univ : Finset (Fin (2*P+1))).filter
        (fun k ↦ (alternatingBitString (2*P+2))
            (k.castSucc : Fin (2*P+2)) ≠
          (alternatingBitString (2*P+2))
            (k.succ : Fin (2*P+2))) =
        Finset.univ from ?_]
  · simp [Finset.card_univ]
  · apply Finset.ext
    intro k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact alternatingBitString_body_disagree P k

/-- The alternating bitstring has disagreeing boundary spins
`s_{2P+1} ≠ s_0`. -/
private lemma alternatingBitString_boundary_disagree (P : ℕ) :
    (alternatingBitString (2*P+2)) (Fin.last (2*P+1) : Fin (2*P+2)) ≠
      (alternatingBitString (2*P+2)) (0 : Fin (2*P+2)) := by
  rw [alternatingBitString_apply, alternatingBitString_apply]
  intro h
  have hval :
      ((Fin.last (2*P+1) : Fin (2*P+2)).val) % 2 =
        ((0 : Fin (2*P+2)).val) % 2 := Fin.val_eq_of_eq h
  have h1 : ((Fin.last (2*P+1) : Fin (2*P+2)).val) = 2*P + 1 := Fin.val_last _
  have h2 : ((0 : Fin (2*P+2)).val) = 0 := rfl
  rw [h1, h2] at hval
  omega

/-- **Witness attainment.** The alternating bitstring saturates the lower
bound: `eigenvalueOnBasis P (alternatingBitString (2*P+2)) = −(4P + 2)`.

Source pin: arXiv:1906.08948v2 §IV l.718 — the alternating string is the
classical ground state of `Hred_z^-`. -/
theorem alternatingBitString_eigenvalue (P : ℕ) :
    eigenvalueOnBasis P (alternatingBitString (2*P+2)) =
      -(4*P + 2 : ℝ) := by
  rw [eigenvalueOnBasis_eq, alternatingBitString_bodyDisagreeCount,
      if_neg (alternatingBitString_boundary_disagree P)]
  push_cast; ring

end

end QAOA.IsingChain.UpperBound
