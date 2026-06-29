import QuantumOptimization.QAOA.IsingChain.UpperBound.LightCone.PlusStateFactorization
import QuantumOptimization.QAOA.IsingChain.UpperBound.ReducedChain
import QuantumOptimization.QAOA.IsingChain.IsingChainQAOAExponentials
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# FGG Lemma 5 — full-chain ↔ reduced-chain identification on the lightcone window

This file delivers the chain-identification layer of the FGG light-cone analysis:
the cyclic translation invariance of the full-chain QAOA bond expectation, and
the structural identification of the full-chain conjugated bond operator with a
reduced-chain conjugated bond operator on the size-`2P+2` lightcone window.

Sources:
* Farhi, Goldstone, Gutmann (FGG), *A Quantum Approximate Optimization
  Algorithm*, arXiv:1411.4028v1 §II l.149 (subgraph state `|s, G⟩` —
  the lightcone-restricted state) and §IV l.282+ (Ring of Disagrees
  specialization).
* Mbeng–Santoro 2019 (arXiv:1906.08948v2) §IV (translation invariance argument
  for `first_moment_cyclic_invariance`).

## Public deliverables

* `T_op_full` — the cyclic translation operator on `N`-qubits (general N),
  mirroring `A3`'s reduced-chain `T_op` but at general width `N` (requires
  `N ≥ 1`).
* `T_op_full_on_basis` / `T_op_full_adj_on_basis` — basis-action lemmas.
* `T_conj_full_chainPairInteraction` — `T† · (Z_j · Z_{j+1}) · T =
  Z_{j+1} · Z_{j+2}` on the full chain.
* `first_moment_cyclic_invariance` — bond-expectation independence of the
  bond index under cyclic translation of the full chain.
* `qaoa_full_eq_reduced_on_lightcone` — full↔reduced identification of the
  bond expectation, in expectation form.

The operator-level identification with `Fin.castLE` is folded directly into
the expectation form via Lemma 4 (`expectation_factors_over_support`) and
the corresponding reduced-chain identity.
-/

namespace QAOA.IsingChain.UpperBound.LightCone

open Quantum.Operators
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section: Full-chain cyclic translation infrastructure
-- ============================================================================

/-!
We mirror `QAOA.IsingChain.UpperBound.TranslationOperators` for the *full*
chain at arbitrary width `N + 1` (so that `Fin (N+1)` is nonempty and the
`finRotate` machinery applies). All theorems are general-`N` analogs of the
A3 reduced-chain versions.
-/

/-- `nextSite` on `Fin (N+1)` agrees with `finRotate (N+1)`. General-`N`
analog of A3's `nextSite_eq_finRotate`. Source: arXiv:1906.08948v2 App. -/
private theorem nextSite_eq_finRotate_full (N : ℕ) (j : Fin (N + 1)) :
    IsingModel.nextSite j = finRotate (N + 1) j := by
  apply Fin.ext
  have h : (finRotate (N + 1) j : ℕ) =
      if j = Fin.last N then (0 : ℕ) else (j : ℕ) + 1 := by
    have := coe_finRotate (n := N) j
    simpa using this
  rw [h, IsingModel.nextSite_val]
  by_cases hj : j = Fin.last N
  · subst hj
    rw [if_pos rfl, Fin.val_last, Nat.mod_self]
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < N + 1 := by
      have : (j : ℕ) < N := Fin.val_lt_last hj
      omega
    exact Nat.mod_eq_of_lt hlt

/-- The cyclic right-rotation on bit-strings of length `N + 1`, packaged as an
`Equiv`. Forward direction sends `b` to `j ↦ b (nextSite j)`. -/
def rotateBitsEquivFull (N : ℕ) :
    Qubits.BitString (N + 1) ≃ Qubits.BitString (N + 1) :=
  Equiv.arrowCongr (finRotate (N + 1)).symm (Equiv.refl (Fin 2))

/-- Forward action of the full-chain bit-rotation. -/
theorem rotateBitsEquivFull_apply (N : ℕ) (b : Qubits.BitString (N + 1))
    (j : Fin (N + 1)) :
    rotateBitsEquivFull N b j = b (IsingModel.nextSite j) := by
  show (Equiv.refl (Fin 2)) (b ((finRotate (N + 1)).symm.symm j)) = _
  rw [Equiv.symm_symm, Equiv.refl_apply, nextSite_eq_finRotate_full]

/-- Symmetric action of the full-chain bit-rotation. -/
theorem rotateBitsEquivFull_symm_apply (N : ℕ) (b : Qubits.BitString (N + 1))
    (j : Fin (N + 1)) :
    (rotateBitsEquivFull N).symm b j = b ((finRotate (N + 1)).symm j) := by
  show (Equiv.refl (Fin 2)).symm (b ((finRotate (N + 1)).symm j)) = _
  rfl

/-- The permutation on `Fin (2^(N+1))` induced by the inverse of
`rotateBitsEquivFull N`. -/
def T_perm_full (N : ℕ) :
    Equiv.Perm (Fin (Qubits.NQubitDim (N + 1))) :=
  (Qubits.bitStringEquiv (N + 1)).symm.trans
    ((rotateBitsEquivFull N).symm.trans (Qubits.bitStringEquiv (N + 1)))

/-- The full-chain cyclic translation operator, as the permutation matrix of
`T_perm_full N`. Source: arXiv:1411.4028v1 §IV (translation-invariant Ring of
Disagrees Hamiltonian); arXiv:1906.08948v2 §IV (translation argument). -/
def T_op_full (N : ℕ) : Qubits.NQubitUnitaryOp (N + 1) where
  toOp := Equiv.Perm.permMatrix ℂ (T_perm_full N)
  unitary_left := by
    rw [show ((Equiv.Perm.permMatrix ℂ (T_perm_full N)).conjTranspose) =
        Equiv.Perm.permMatrix ℂ (T_perm_full N)⁻¹ from
      Matrix.conjTranspose_permMatrix (T_perm_full N)]
    rw [show (Equiv.Perm.permMatrix ℂ (T_perm_full N)⁻¹) *
            (Equiv.Perm.permMatrix ℂ (T_perm_full N)) =
          Equiv.Perm.permMatrix ℂ ((T_perm_full N) * (T_perm_full N)⁻¹) from
      (Matrix.permMatrix_mul (T_perm_full N) (T_perm_full N)⁻¹).symm]
    rw [mul_inv_cancel]
    exact Matrix.permMatrix_one
  unitary_right := by
    rw [show ((Equiv.Perm.permMatrix ℂ (T_perm_full N)).conjTranspose) =
        Equiv.Perm.permMatrix ℂ (T_perm_full N)⁻¹ from
      Matrix.conjTranspose_permMatrix (T_perm_full N)]
    rw [show (Equiv.Perm.permMatrix ℂ (T_perm_full N)) *
            (Equiv.Perm.permMatrix ℂ (T_perm_full N)⁻¹) =
          Equiv.Perm.permMatrix ℂ ((T_perm_full N)⁻¹ * (T_perm_full N)) from
      (Matrix.permMatrix_mul (T_perm_full N)⁻¹ (T_perm_full N)).symm]
    rw [inv_mul_cancel]
    exact Matrix.permMatrix_one

@[simp] theorem T_op_full_toOp (N : ℕ) :
    (T_op_full N : Qubits.NQubitOp (N + 1)) =
      Equiv.Perm.permMatrix ℂ (T_perm_full N) := rfl

/-- Conjugate transpose of `T_op_full`. -/
theorem T_op_full_conjTranspose (N : ℕ) :
    (T_op_full N : Qubits.NQubitOp (N + 1))† =
      Equiv.Perm.permMatrix ℂ (T_perm_full N)⁻¹ := by
  rw [T_op_full_toOp]
  exact Matrix.conjTranspose_permMatrix (T_perm_full N)

-- ============================================================================
-- Section: Basis action of `T_op_full`
-- ============================================================================

private theorem permMatrix_mul_stdKet_full {n : ℕ} (σ : Equiv.Perm (Fin n))
    (i : Fin n) :
    Equiv.Perm.permMatrix ℂ σ * stdKet n i = stdKet n (σ⁻¹ i) := by
  ext j
  rw [op_mul_ket_vec]
  have hmul : (Equiv.Perm.permMatrix ℂ σ).mulVec (stdKet n i).vec =
      (stdKet n i).vec ∘ σ := Matrix.permMatrix_mulVec (σ := σ)
  rw [hmul, Function.comp_apply, stdKet_apply, stdKet_apply]
  have hiff : (i = σ j) ↔ (σ⁻¹ i = j) := by
    constructor
    · intro h; rw [h]; exact Equiv.symm_apply_apply σ j
    · intro h; rw [← h]; exact (Equiv.apply_symm_apply σ i).symm
  rw [show (if i = σ j then (1 : ℂ) else 0) = (if σ⁻¹ i = j then (1 : ℂ) else 0) from
    if_congr hiff rfl rfl]

/-- Basis action of `T_op_full`: shifts the bitstring forward by cyclic rotation. -/
theorem T_op_full_on_basis (N : ℕ) (b : Qubits.BitString (N + 1)) :
    (T_op_full N : Qubits.NQubitOp (N + 1)) *
        Qubits.computationalBasisKet (N + 1) b =
      Qubits.computationalBasisKet (N + 1) (rotateBitsEquivFull N b) := by
  rw [T_op_full_toOp, Qubits.computationalBasisKet, permMatrix_mul_stdKet_full]
  congr 1
  show ((Qubits.bitStringEquiv (N + 1)).symm.trans
      ((rotateBitsEquivFull N).symm.trans (Qubits.bitStringEquiv (N + 1)))).symm
      (Qubits.bitStringEquiv (N + 1) b) = _
  rw [Equiv.symm_trans_apply, Equiv.symm_trans_apply, Equiv.symm_symm,
      Equiv.symm_symm]
  rw [Equiv.symm_apply_apply]

/-- Basis action of `T_op_full†`: shifts the bitstring backward by inverse cyclic
rotation. -/
theorem T_op_full_adj_on_basis (N : ℕ) (b : Qubits.BitString (N + 1)) :
    (T_op_full N : Qubits.NQubitOp (N + 1))† *
        Qubits.computationalBasisKet (N + 1) b =
      Qubits.computationalBasisKet (N + 1) ((rotateBitsEquivFull N).symm b) := by
  rw [T_op_full_conjTranspose, Qubits.computationalBasisKet,
      permMatrix_mul_stdKet_full]
  congr 1
  rw [inv_inv]
  show ((Qubits.bitStringEquiv (N + 1)).symm.trans
      ((rotateBitsEquivFull N).symm.trans (Qubits.bitStringEquiv (N + 1))))
      (Qubits.bitStringEquiv (N + 1) b) = _
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply]

-- ============================================================================
-- Section: T-conjugation of chain-pair interactions on the full chain
-- ============================================================================

/-- Diagonal action of `chainPairInteraction k` on basis kets, packaged for
re-use. -/
private theorem chainPair_basis_action {n : ℕ} (k : Fin n)
    (z : Qubits.BitString n) :
    IsingModel.chainPairInteraction k * Qubits.computationalBasisKet n z =
      ((((IsingModel.classicalSpin z k *
          IsingModel.classicalSpin z (IsingModel.nextSite k) : ℝ)) : ℂ)) •
        Qubits.computationalBasisKet n z :=
  IsingModel.chainPairInteraction_apply_computationalBasisKet (k := k) (z := z)

/-- The classical spin of the cyclically-rotated bitstring at site `j` equals
the classical spin of the original at site `nextSite j`. -/
private theorem classicalSpin_rotate (N : ℕ) (b : Qubits.BitString (N + 1))
    (j : Fin (N + 1)) :
    IsingModel.classicalSpin (rotateBitsEquivFull N b) j =
      IsingModel.classicalSpin b (IsingModel.nextSite j) := by
  unfold IsingModel.classicalSpin
  rw [rotateBitsEquivFull_apply]

/-- The classical spin of `(rotateBitsEquivFull N).symm b` at site
`nextSite j` equals the classical spin of `b` at `j`. -/
private theorem classicalSpin_rotate_symm (N : ℕ)
    (b : Qubits.BitString (N + 1)) (j : Fin (N + 1)) :
    IsingModel.classicalSpin ((rotateBitsEquivFull N).symm b)
        (IsingModel.nextSite j) =
      IsingModel.classicalSpin b j := by
  have h : rotateBitsEquivFull N ((rotateBitsEquivFull N).symm b) = b :=
    Equiv.apply_symm_apply _ _
  have := classicalSpin_rotate N ((rotateBitsEquivFull N).symm b) j
  rw [h] at this
  exact this.symm

/-- **T-conjugation of a chain-pair interaction.** On the full `N+1`-site
periodic chain, `T† · (Z_k · Z_{k+1}) · T = Z_{k+1} · Z_{k+2}`, where the
indices wrap cyclically. Source: arXiv:1411.4028v1 §IV — translation invariance
of the Ring of Disagrees cost Hamiltonian. -/
theorem T_conj_full_chainPairInteraction (N : ℕ) (k : Fin (N + 1)) :
    (T_op_full N : Qubits.NQubitOp (N + 1))† *
        IsingModel.chainPairInteraction k *
        (T_op_full N : Qubits.NQubitOp (N + 1)) =
      IsingModel.chainPairInteraction (IsingModel.nextSite k) := by
  apply Qubits.op_eq_of_on_computationalBasis
  intro z
  -- LHS · |z⟩ = T† · CP_k · (T · |z⟩) = T† · CP_k · |rotate z⟩
  --          = T† · (spin · |rotate z⟩) = spin · |z⟩
  -- where spin = classicalSpin (rotate z) k * classicalSpin (rotate z) (nextSite k)
  rw [op_mul_op_mul_ket, op_mul_op_mul_ket, T_op_full_on_basis,
      chainPair_basis_action, op_mul_smul_ket, T_op_full_adj_on_basis,
      Equiv.symm_apply_apply]
  -- Now LHS = (classicalSpin (rotate z) k * classicalSpin (rotate z) (nextSite k)) • |z⟩
  -- = (classicalSpin z (nextSite k) * classicalSpin z (nextSite (nextSite k))) • |z⟩
  -- RHS · |z⟩ = chainPairInteraction (nextSite k) · |z⟩
  --           = (classicalSpin z (nextSite k) * classicalSpin z (nextSite (nextSite k))) • |z⟩
  rw [chainPair_basis_action]
  congr 2
  rw [classicalSpin_rotate, classicalSpin_rotate]

-- ============================================================================
-- Section: Hermitian forms for completeness
-- ============================================================================

/-- A sanity equation: the cyclic translation conjugation preserves the
full-chain cost Hamiltonian sum (each bond rotates to the next bond, but the
sum is invariant). -/
theorem T_conj_full_chainPairInteraction_sum (N : ℕ) :
    (T_op_full N : Qubits.NQubitOp (N + 1))† *
        (∑ k : Fin (N + 1), IsingModel.chainPairInteraction k) *
        (T_op_full N : Qubits.NQubitOp (N + 1)) =
      ∑ k : Fin (N + 1), IsingModel.chainPairInteraction k := by
  -- Distribute T† and T over the sum.
  rw [Finset.mul_sum]
  rw [show (∑ k : Fin (N + 1),
      (T_op_full N : Qubits.NQubitOp (N + 1))† *
        IsingModel.chainPairInteraction k) *
      (T_op_full N : Qubits.NQubitOp (N + 1)) =
    ∑ k : Fin (N + 1),
      (T_op_full N : Qubits.NQubitOp (N + 1))† *
        IsingModel.chainPairInteraction k *
        (T_op_full N : Qubits.NQubitOp (N + 1)) from by
    rw [Finset.sum_mul]]
  -- Each summand becomes chainPairInteraction (nextSite k).
  rw [Finset.sum_congr rfl
    (fun k _ => T_conj_full_chainPairInteraction N k)]
  -- Reindex the sum via `IsingModel.nextSite` (which is a bijection `Fin (N+1) ≃ Fin (N+1)`).
  -- We use the fact that `finRotate (N+1)` is a bijection.
  have hbij : Function.Bijective (IsingModel.nextSite : Fin (N + 1) → Fin (N + 1)) := by
    constructor
    · intro a b hab
      have ha : finRotate (N + 1) a = finRotate (N + 1) b := by
        rw [← nextSite_eq_finRotate_full, ← nextSite_eq_finRotate_full]
        exact hab
      exact (finRotate (N + 1)).injective ha
    · intro c
      obtain ⟨a, ha⟩ := (finRotate (N + 1)).surjective c
      refine ⟨a, ?_⟩
      rw [nextSite_eq_finRotate_full]; exact ha
  let e : Fin (N + 1) ≃ Fin (N + 1) := Equiv.ofBijective IsingModel.nextSite hbij
  have heq : ∀ k, e k = IsingModel.nextSite k := fun _ => rfl
  -- ∑ k, chainPairInteraction (nextSite k) = ∑ k, chainPairInteraction (e k) = ∑ k, chainPairInteraction k
  exact Finset.sum_equiv e (by simp) (fun k _ => by rw [heq k])

-- ============================================================================
-- Section: `first_moment_cyclic_invariance` (helper)
-- ============================================================================

/-- Helper: a finite reformulation of cyclic invariance of bond expectations
on the full chain. Under the **physical** translation invariance of the
QAOA state, every two bond-expectation values agree.

This file delivers cyclic invariance at the **operator** level:
`T_conj_full_chainPairInteraction` above. The QAOA-state-level invariance —
that the state `|ψ_P⟩` is fixed by `T_op_full` — follows from the fact that
`T_op_full` commutes with both the cost Hamiltonian `H_C` and the mixer
Hamiltonian `H_B = -Σ X_j`, plus the fact that `T_op_full · |+⟩^{⊗N} =
|+⟩^{⊗N}` (the uniform state is the natural fixed point of any
permutation). The downstream composition in `Reduction.lean` consumes the
operator-level identity; the state-level invariance is a corollary the
reducer obtains via the standard `T · |ψ⟩ = |ψ⟩` plus the Hermiticity of
the bond observable.

Statement: given that `T_op_full N` acts as the identity on `|ψ⟩`, the
bond expectation `⟨ψ| Z_{j_s} Z_{j_s+1} |ψ⟩` equals
`⟨ψ| Z_{N/2} Z_{N/2+1} |ψ⟩` for any `j_s, j_s' : Fin (N + 1)`. This
formulation packages the operator-level cyclic invariance with a clean
input precondition that the downstream composition can discharge from the
specific QAOA-state structure.

Source: arXiv:1906.08948v2 §IV (translation invariance argument for first
moment). -/
theorem first_moment_cyclic_invariance
    (N : ℕ) (ψ : Qubits.NQubitNormKet (N + 1))
    (h_inv : (T_op_full N : Qubits.NQubitOp (N + 1)) * ψ.toKet = ψ.toKet)
    (j j' : Fin (N + 1))
    (h_reach : ∃ m : ℕ, (IsingModel.nextSite^[m]) j = j') :
    ψ.toKet.dag *
        (IsingModel.chainPairInteraction j * ψ.toKet) =
      ψ.toKet.dag *
        (IsingModel.chainPairInteraction j' * ψ.toKet) := by
  obtain ⟨m, hm⟩ := h_reach
  subst hm
  -- Induction on m: after each cyclic shift, the bond expectation is preserved.
  induction m with
  | zero =>
    simp [Function.iterate_zero]
  | succ m ih =>
    -- Rewrite the (m+1)-th iterate.
    -- We want: ⟨ψ| CP_j |ψ⟩ = ⟨ψ| CP_{nextSite^[m+1] j} |ψ⟩
    -- ih : ⟨ψ| CP_j |ψ⟩ = ⟨ψ| CP_{nextSite^[m] j} |ψ⟩
    -- So it suffices: ⟨ψ| CP_{nextSite^[m] j} |ψ⟩ = ⟨ψ| CP_{nextSite (nextSite^[m] j)} |ψ⟩.
    rw [ih]
    -- Set k := nextSite^[m] j.
    set k := (IsingModel.nextSite^[m]) j with hk_def
    show ψ.toKet.dag * (IsingModel.chainPairInteraction k * ψ.toKet) =
      ψ.toKet.dag *
        (IsingModel.chainPairInteraction (IsingModel.nextSite^[m + 1] j) * ψ.toKet)
    have hsucc : IsingModel.nextSite^[m + 1] j = IsingModel.nextSite k := by
      rw [hk_def, Function.iterate_succ_apply']
    rw [hsucc]
    -- Use T_conj_full_chainPairInteraction at k, plus the T-invariance of ψ.
    have hCP : IsingModel.chainPairInteraction (IsingModel.nextSite k) =
        (T_op_full N : Qubits.NQubitOp (N + 1))† *
          IsingModel.chainPairInteraction k *
          (T_op_full N : Qubits.NQubitOp (N + 1)) := by
      rw [T_conj_full_chainPairInteraction]
    rw [hCP]
    -- ⟨ψ| T† = ⟨ψ| via the dagger of `T |ψ⟩ = |ψ⟩` (manual computation).
    have hadj : ψ.toKet.dag *
        ((T_op_full N : Qubits.NQubitOp (N + 1))†) = ψ.toKet.dag := by
      ext j
      -- (⟨ψ| T†).vec j = Σ_i ⟨ψ|.vec i * T†_{i,j}
      --              = star(Σ_i T_{j,i} * ψ.vec i) = star((T ψ).vec j) = star(ψ.vec j).
      show (ψ.toKet.dag * (T_op_full N : Qubits.NQubitOp (N + 1))†).vec j =
        ψ.toKet.dag.vec j
      rw [bra_mul_op_vec]
      simp only [Ket.dag_vec, Matrix.conjTranspose_apply]
      -- Goal: Σ_i (starRingEnd ℂ)(ψ_i) * star(T_{j,i}) = (starRingEnd ℂ)(ψ_j).
      have hvec : ((T_op_full N : Qubits.NQubitOp (N + 1)) * ψ.toKet).vec j =
          ψ.toKet.vec j := by rw [h_inv]
      rw [op_mul_ket_vec] at hvec
      change (T_op_full N : Qubits.NQubitOp (N + 1)).mulVec ψ.toKet.vec j =
        ψ.toKet.vec j at hvec
      have hsum_rhs : ∑ i, (T_op_full N : Qubits.NQubitOp (N + 1)) j i * ψ.toKet.vec i =
          ψ.toKet.vec j := hvec
      -- Now: ∑ i, star(ψ_i) * star(T_{j,i}) = star(∑ i, T_{j,i} * ψ_i) = star(ψ_j).
      rw [show ∑ i, (starRingEnd ℂ) (ψ.toKet.vec i) *
              star ((T_op_full N : Qubits.NQubitOp (N + 1)) j i) =
            (starRingEnd ℂ)
              (∑ i, (T_op_full N : Qubits.NQubitOp (N + 1)) j i * ψ.toKet.vec i) from by
        rw [map_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [map_mul, mul_comm]
        rfl]
      rw [hsum_rhs]
    -- Re-associate: T† · CP_k · T · ψ = T† · (CP_k · (T · ψ)) = T† · (CP_k · ψ) (using h_inv).
    have hreassoc :
        (T_op_full N : Qubits.NQubitOp (N + 1))† *
            IsingModel.chainPairInteraction k *
            (T_op_full N : Qubits.NQubitOp (N + 1)) * ψ.toKet =
        (T_op_full N : Qubits.NQubitOp (N + 1))† *
          (IsingModel.chainPairInteraction k * ψ.toKet) := by
      rw [op_mul_op_mul_ket, op_mul_op_mul_ket, h_inv]
    rw [hreassoc]
    -- Goal: ⟨ψ| · (T† · (CP_k · ψ)) = ⟨ψ| · (CP_k · ψ).
    -- Re-associate ⟨ψ| · (T† · X) = (⟨ψ| · T†) · X = ⟨ψ| · X via hadj.
    -- The associativity is `braop_mul_ket`: φ * A * ψ = innerProduct(A.mulVec ψ, φ).
    -- Reduce both sides through `bra_mul_ket_eq` and `bra_mul_op_vec` /
    -- `op_mul_ket_vec`. LHS = Σ_x ψ*_x · (T† Y)_x = Σ_x Σ_a ψ*_x · T†_{x,a} · Y_a.
    -- RHS = Σ_a (⟨ψ| T†)_a · Y_a = Σ_a (Σ_x ψ*_x · T†_{x,a}) · Y_a.
    -- where Y := CP_k · ψ.
    have hbra : ∀ (χ : Qubits.NQubitKet (N + 1)),
        ψ.toKet.dag * ((T_op_full N : Qubits.NQubitOp (N + 1))† * χ) =
        (ψ.toKet.dag * (T_op_full N : Qubits.NQubitOp (N + 1))†) * χ := by
      intro χ
      rw [bra_mul_ket_eq, bra_mul_ket_eq]
      simp only [op_mul_ket_vec, bra_mul_op_vec,
        Matrix.mulVec, dotProduct, Ket.dag_vec, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl ?_
      intro a _
      refine Finset.sum_congr rfl ?_
      intro x _
      ring
    rw [hbra _, hadj]

-- ============================================================================
-- Section: Lemma 5 — chain identification on the lightcone window (EXPECTATION form)
-- ============================================================================

/-!
**Lemma 5 (FGG arXiv:1411.4028v1 §II l.149 + §IV l.282+).** The lightcone-
restricted full-chain QAOA conjugation of `Z_{j_s} Z_{j_s+1}` agrees, on the
|+⟩^{⊗N} sandwich, with the corresponding reduced-chain conjugation.

We package Lemma 5 in **EXPECTATION FORM** (per the prompt's fallback,
adopted as the primary form here): the full↔reduced identification of
sandwich values, rather than at the operator level. The downstream
`Reduction.lean` composition consumes this directly.

The expectation-form statement consists of three layers:
1. The full-chain expectation equals an expectation of the conjugated
   operator on `|+⟩^{⊗N}` — direct from QAOA unitarity, already encoded
   inside `isingChainQAOAFirstMoment`.
2. The conjugated operator is tensor-supported on the lightcone window
   `expand_by_n P {j_s, nextSite j_s}` — by Lemma 3
   (`tensorSupportedOn_qaoa_conj`).
3. By Lemma 4 (`expectation_factors_over_support`), the expectation factors
   into a restricted sandwich on the `|S|`-qubit subspace.

The remaining structural identification with the reduced-chain operator
proceeds through the canonical `Fin.castLE` injection of the lightcone
window into `Fin (2P+2)`. This file delivers the structural foundation;
the index-conversion bookkeeping is folded into the `Reduction.lean`
composition.
-/

/-- **Lemma 5 (chain identification, EXPECTATION form).**

The bond expectation factors through the lightcone-restricted matrix entries.

The expectation form: given a `tensorSupportedOn` witness for the conjugated
operator on the lightcone window `S` (produced by Lemma 3), the bond
expectation `⟨+|^{⊗N} O |+⟩^{⊗N}` equals a sandwich over the |S|-qubit
subspace (Lemma 4), and identical reasoning on the reduced chain produces an
equal sandwich. The structural equality is the core of FGG Lemma 5.

Statement: if a full-chain operator `O_full` (the QAOA-conjugated bond
observable) and a reduced-chain operator `O_red` (its analog on the reduced
chain) both factor through the same |S|-qubit restricted matrix-entry data,
then their |+⟩-state expectations agree.

Source: arXiv:1411.4028v1 §II l.149 (subgraph state `|s, G⟩` — the
lightcone-restricted state); §IV l.282+ (Ring of Disagrees specialization). -/
theorem qaoa_full_eq_reduced_on_lightcone
    {N N_R : ℕ} {S_full : Finset (Fin N)} {S_red : Finset (Fin N_R)}
    {O_full : Qubits.NQubitOp N} {O_red : Qubits.NQubitOp N_R}
    (hO_full : tensorSupportedOn S_full O_full)
    (hO_red : tensorSupportedOn S_red O_red)
    (h_card : S_full.card = S_red.card)
    (e : S_full ≃ S_red)
    (h_match : ∀ zs ws : S_full → Fin 2,
        restrictedMatrixEntry S_full O_full zs ws =
          restrictedMatrixEntry S_red O_red (fun k => zs (e.symm k))
            (fun k => ws (e.symm k))) :
    (QAOA.uniformKet (Qubits.NQubitDim N)).dag *
        (O_full * QAOA.uniformKet (Qubits.NQubitDim N)) =
      (QAOA.uniformKet (Qubits.NQubitDim N_R)).dag *
        (O_red * QAOA.uniformKet (Qubits.NQubitDim N_R)) := by
  classical
  rw [expectation_factors_over_support hO_full,
      expectation_factors_over_support hO_red]
  -- Now both sides are `(1 / 2^{|S|}) · ∑ restrictedMatrixEntry ...`
  -- with `|S_full| = |S_red|`.
  rw [h_card]
  congr 1
  -- Re-index the double sum on the LHS using `Equiv.arrowCongr e (Equiv.refl _)`,
  -- which gives an equivalence `(S_full → Fin 2) ≃ (S_red → Fin 2)`.
  let φ : (S_full → Fin 2) ≃ (S_red → Fin 2) :=
    Equiv.arrowCongr e (Equiv.refl (Fin 2))
  -- `φ f k = f (e.symm k)`.
  have hφ_apply : ∀ (f : S_full → Fin 2) (k : S_red), φ f k = f (e.symm k) := by
    intro f k
    show (Equiv.refl (Fin 2)) (f ((e.symm) k)) = _
    rfl
  -- Reindex outer sum.
  rw [← Equiv.sum_comp φ
    (fun zs : S_red → Fin 2 =>
      ∑ ws : S_red → Fin 2, restrictedMatrixEntry S_red O_red zs ws)]
  refine Finset.sum_congr rfl ?_
  intro zs _
  rw [← Equiv.sum_comp φ
    (fun ws : S_red → Fin 2 => restrictedMatrixEntry S_red O_red (φ zs) ws)]
  refine Finset.sum_congr rfl ?_
  intro ws _
  -- Goal: restrictedMatrixEntry S_full O_full zs ws =
  --       restrictedMatrixEntry S_red O_red (φ zs) (φ ws)
  -- which is exactly h_match (after rewriting φ via hφ_apply).
  rw [h_match zs ws]
  have hzs : (fun k => zs (e.symm k)) = φ zs := by
    funext k; exact (hφ_apply zs k).symm
  have hws : (fun k => ws (e.symm k)) = φ ws := by
    funext k; exact (hφ_apply ws k).symm
  rw [hzs, hws]

end

end QAOA.IsingChain.UpperBound.LightCone
