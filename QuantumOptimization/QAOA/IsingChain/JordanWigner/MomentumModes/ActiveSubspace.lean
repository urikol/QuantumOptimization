import QuantumOptimization.QAOA.IsingChain.JordanWigner.MomentumModes.Basic

/-!
# Momentum Modes (Active Subspace) — the assembled active projector `Π_A` and its eigenstate algebra

Builds the dynamically-active subspace of the momentum-mode picture
(arXiv:1911.12259v2 SM l.806–808, 833–834). The active projector
`activeProj P = (1−n_0)(1−n_π)·∏_k (1+P_k)/2` is assembled with the pair-parity product
encoded as a `Finset.noncommProd` over `K_ABC P`, and `InActiveSubspace P ψ` is the
eigenstate condition `Π_A ψ = ψ`. Derives the per-factor annihilation/eigenvalue
consequences (`n_{0,π} ψ = 0`, `P_{k_m} ψ = ψ`) via the commutation algebra of `Basic`
and `noncommProd` factor extraction.

## Main definitions
- `activeFactor`, `activeProj`: per-pair projector factors and the assembled active projector.
- `InActiveSubspace`: the assembled-projector eigenstate condition `Π_A ψ = ψ`.

## Main statements
- `inActiveSubspace_n0_annih`, `inActiveSubspace_npi_annih`: `n_{0,π}·ψ = 0` on the active subspace.
- `inActiveSubspace_pairParity_eq`: `P_{k_m}·ψ = ψ` on the active subspace.
- `pairParity_mul_activeProj`: each pair-parity factor absorbs the active projector.
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 10: The active subspace (assembled projector via `noncommProd`)
-- ============================================================================

/-- The per-pair projector factor `(1 + P_{k_n})/2` (projects onto `P_{k_n} = +1`). -/
def activeFactor (P : ℕ) (n : WaveVectorABC P) : NQubitOp (2*P+2) :=
  (1 / 2 : ℂ) • (1 + pairParity P (waveVectorABC P n))

/-- The pair-parity factors pairwise commute (distinct active pairs commute via
`pairParity_commute_pairParity_cross`). -/
theorem activeFactor_pairwise_commute (P : ℕ) :
    ((K_ABC P : Finset (WaveVectorABC P)) : Set (WaveVectorABC P)).Pairwise
      (Function.onFun Commute (activeFactor P)) := by
  intro n _ m _ hnm
  unfold Function.onFun activeFactor
  apply Commute.smul_left
  apply Commute.smul_right
  apply Commute.add_left (Commute.one_left _)
  apply Commute.add_right (Commute.one_right _)
  exact pairParity_commute_pairParity_cross P n m hnm

/-- The assembled active-subspace projector
`Π_A = (1 − n_0)(1 − n_π)·∏_{k} (1 + P_k)/2` (source l.806–808, 833–834).
The pair-parity product is a `Finset.noncommProd` over `K_ABC P` (the factors
pairwise commute, `activeFactor_pairwise_commute`), enabling per-pair factor
extraction. Projects onto `A = {n_0 = n_π = 0, P_k = +1 ∀ k ∈ K_ABC}`. -/
def activeProj (P : ℕ) : NQubitOp (2*P+2) :=
  (1 - numberOpK P 0) * (1 - numberOpK P Real.pi) *
    (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P)

/-- The dynamically-active subspace condition: `ψ` is a `+1`-eigenstate of the
assembled projector `Π_A` (`activeProj P * ψ = ψ`). Equivalent to
`{n_0 = n_π = 0 ∧ ∀ k, P_k = +1}`, but the assembled-projector phrasing is the
one whose preservation along QAOA evolution is cleanly provable at B4. -/
def InActiveSubspace (P : ℕ) (ψ : NQubitKet (2 * P + 2)) : Prop :=
  activeProj P * ψ = ψ

/-- `n_0 · Π_A = 0`: the self-conjugate `k=0` mode is annihilated by the assembled
projector (its first factor is `(1 − n_0)`). -/
theorem numberOpK_zero_mul_activeProj (P : ℕ) :
    numberOpK P 0 * activeProj P = 0 := by
  unfold activeProj
  rw [← mul_assoc, ← mul_assoc, numberOpK_mul_one_sub_self, zero_mul, zero_mul]

/-- DERIVED HELPER: on the active subspace, the `k=0` self-conjugate mode is empty:
`n_0 · ψ = 0`. -/
theorem inActiveSubspace_n0_annih (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) : numberOpK P 0 * ψ = 0 := by
  unfold InActiveSubspace at hψ
  calc numberOpK P 0 * ψ = numberOpK P 0 * (activeProj P * ψ) := by rw [hψ]
    _ = (numberOpK P 0 * activeProj P) * ψ := by rw [op_mul_op_mul_ket]
    _ = (0 : NQubitOp (2*P+2)) * ψ := by rw [numberOpK_zero_mul_activeProj]
    _ = 0 := by ext i; simp [op_mul_ket_vec]

/-- `n_π · Π_A = 0`: the `k=π` self-conjugate mode is annihilated by `Π_A` (its
second factor is `(1 − n_π)`, and `n_π` commutes with the first factor `(1−n_0)`). -/
theorem numberOpK_npi_mul_activeProj (P : ℕ) :
    numberOpK P Real.pi * activeProj P = 0 := by
  unfold activeProj
  have hcomm : numberOpK P Real.pi * (1 - numberOpK P 0)
      = (1 - numberOpK P 0) * numberOpK P Real.pi := by
    rw [mul_sub, sub_mul, mul_one, one_mul, (numberOpK_zero_commute_npi P).symm.eq]
  have hkey : numberOpK P Real.pi * ((1 - numberOpK P 0) * (1 - numberOpK P Real.pi)) = 0 := by
    rw [← mul_assoc, hcomm, mul_assoc, numberOpK_mul_one_sub_self, mul_zero]
  rw [← mul_assoc, hkey, zero_mul]

/-- DERIVED HELPER: on the active subspace, the `k=π` self-conjugate mode is empty:
`n_π · ψ = 0`. -/
theorem inActiveSubspace_npi_annih (P : ℕ) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) : numberOpK P Real.pi * ψ = 0 := by
  unfold InActiveSubspace at hψ
  calc numberOpK P Real.pi * ψ = numberOpK P Real.pi * (activeProj P * ψ) := by rw [hψ]
    _ = (numberOpK P Real.pi * activeProj P) * ψ := by rw [op_mul_op_mul_ket]
    _ = (0 : NQubitOp (2*P+2)) * ψ := by rw [numberOpK_npi_mul_activeProj]
    _ = 0 := by ext i; simp [op_mul_ket_vec]

/-- Per-pair absorption: `P_{k_m} · activeFactor m = activeFactor m` (since
`P_{k_m}·(1 + P_{k_m})/2 = (P_{k_m} + 1)/2 = (1 + P_{k_m})/2`, using
`pairParity_involution`). -/
theorem pairParity_mul_activeFactor_self (P : ℕ) (m : Fin P) :
    pairParity P (waveVectorABC P m) * activeFactor P m = activeFactor P m := by
  unfold activeFactor
  rw [mul_smul_comm, mul_add, mul_one, pairParity_involution]
  rw [add_comm (pairParity P (waveVectorABC P m)) 1]

/-- `P_{k_m}` commutes with the pair-parity product over `K_ABC P` (each factor of
the product commutes with `P_{k_m}` — distinct pairs via cross-commute, and the
`m`-th factor via the pair-parity involution algebra). -/
theorem pairParity_commute_noncommProd (P : ℕ) (m : Fin P) :
    Commute (pairParity P (waveVectorABC P m))
      ((K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P)) := by
  apply Finset.noncommProd_commute
  intro x _
  unfold activeFactor
  apply Commute.smul_right
  apply Commute.add_right (Commute.one_right _)
  by_cases hxm : x = m
  · subst hxm; exact Commute.refl _
  · exact pairParity_commute_pairParity_cross P m x (fun h => hxm h.symm)

/-- `P_{k_m} · (noncommProd over K_ABC) = noncommProd over K_ABC`: the pair-parity
factor is absorbed by its own slot (extract the `m`-th factor via
`Finset.mul_noncommProd_erase`, absorb with `pairParity_mul_activeFactor_self`). -/
theorem pairParity_mul_noncommProd (P : ℕ) (m : Fin P) :
    pairParity P (waveVectorABC P m) *
        (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P)
      = (K_ABC P).noncommProd (activeFactor P) (activeFactor_pairwise_commute P) := by
  have hmem : m ∈ K_ABC P := Finset.mem_univ m
  rw [← Finset.mul_noncommProd_erase (K_ABC P) hmem (activeFactor P)
    (activeFactor_pairwise_commute P)]
  -- P_{k_m} * (activeFactor m * erase_prod) = activeFactor m * erase_prod
  rw [← mul_assoc, pairParity_mul_activeFactor_self]

/-- `P_{k_m} · Π_A = Π_A`. -/
theorem pairParity_mul_activeProj (P : ℕ) (m : Fin P) :
    pairParity P (waveVectorABC P m) * activeProj P = activeProj P := by
  unfold activeProj
  -- P_{k_m} commutes with (1 − n_0) and (1 − n_π); push it to the noncommProd and absorb
  have hc0 : Commute (pairParity P (waveVectorABC P m)) (1 - numberOpK P 0) :=
    Commute.sub_right (Commute.one_right _) (numberOpK_zero_commute_pairParity P m).symm
  have hcpi : Commute (pairParity P (waveVectorABC P m)) (1 - numberOpK P Real.pi) :=
    Commute.sub_right (Commute.one_right _) (numberOpK_pi_commute_pairParity P m).symm
  rw [mul_assoc]
  rw [← mul_assoc (pairParity P (waveVectorABC P m)), hc0.eq, mul_assoc]
  rw [← mul_assoc (pairParity P (waveVectorABC P m)), hcpi.eq, mul_assoc]
  rw [pairParity_mul_noncommProd, ← mul_assoc]

/-- DERIVED HELPER: on the active subspace, every active pair has `+1` parity:
`pairParity P (k_m) · ψ = ψ`. -/
theorem inActiveSubspace_pairParity_eq (P : ℕ) (m : Fin P) (ψ : NQubitKet (2 * P + 2))
    (hψ : InActiveSubspace P ψ) : pairParity P (waveVectorABC P m) * ψ = ψ := by
  unfold InActiveSubspace at hψ
  calc pairParity P (waveVectorABC P m) * ψ
      = pairParity P (waveVectorABC P m) * (activeProj P * ψ) := by rw [hψ]
    _ = (pairParity P (waveVectorABC P m) * activeProj P) * ψ := by rw [op_mul_op_mul_ket]
    _ = activeProj P * ψ := by rw [pairParity_mul_activeProj]
    _ = ψ := hψ


end

end QAOA.IsingChain.JordanWigner
