import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Geometry
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.CommuteSuite
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Preservation
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.ExpReduction
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.Heisenberg
import QuantumOptimization.QAOA.IsingChain.UpperBound.ResidualEnergyBound

/-!
# Decomposition — Theorem B: the exact residual-energy mode decomposition

Assembles the Jordan–Wigner image, the momentum-mode / active-subspace decomposition,
the pseudospin dynamics / Rodrigues rotations, and the residual-energy / reduced-chain
bridge into the two public theorems realizing arXiv:1911.12259v2 SM l.903–963:

* `residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum` — the exact decomposition
  `eres = 1/(2P+2) + (1/(2P+2)) Σ_k ε_k`.
* `epsilonMode_nonneg` — each mode energy `ε_k ≥ 0`.

This top module carries the two public theorems (`QAOA.IsingChain` namespace) and the
final assembly. The supporting machinery lives in the `Decomposition/` subfiles:

* `Decomposition/Geometry.lean` — `extendFin`, `epsilonMode`, `geometric_form`,
  `braOpKet_eq_dotProduct`.
* `Decomposition/CommuteSuite.lean` — the single-fermion Wick commute calculus
  (`n`/`τ`/`HredMode` cross- and same-pair commutators).
* `Decomposition/Preservation.lean` — the active-subspace preservation result
  `psiTilde_inActiveSubspace` (Hermiticity, `Commute (Hred*) (activeProj)`, depth induction,
  uniform-state base case).
* `Decomposition/ExpReduction.lean` — the base case and the per-mode `exp`-conjugation
  reductions `costExp_conj_dotTau_eq_modeExp` / `mixerExp_conj_dotTau_eq_modeExp`.
* `Decomposition/Heisenberg.lean` — the Heisenberg depth induction + y-flip bridge,
  delivering `mode_sum_expectation`.

The upper-bound development is reused (its `bond_expectation_full_eq_reduced` +
`chainPairInteraction_expectation_eq_averaged` bridge), not collapsed or re-derived.
-/

namespace QAOA.IsingChain

open JordanWigner in
open Quantum.Operators in
open UpperBound in
/-- **PUBLIC #1.** The exact residual-energy mode decomposition (arXiv:1911.12259v2 SM
`eqn:eres_chain`, l.946):
`eres = 1/(2P+2) + (1/(2P+2)) Σ_{k ∈ K_ABC} ε_k`.

Mirrors the `residualEnergy_lower_bound` algebra (l.280–339), but
replaces its final variational `≥ E_gs` step with the exact `=` supplied by the mode
expectation `mode_sum_expectation` and the active-subspace discharge
`psiTilde_inActiveSubspace`. -/
theorem residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum
    {N P : ℕ} (hN_even : 2 ∣ N) (hP : 2 * P + 2 ≤ N)
    (hChain : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N))
    (γ β : Fin P → ℝ) :
    residualEnergy hChain γ β =
      1 / (2*P + 2) + (1 / (2*P + 2)) * ∑ k ∈ JordanWigner.K_ABC P,
        JordanWigner.epsilonMode k γ β := by
  -- Step 1 — A2.3: rewrite the first moment via the reduced bond.
  unfold residualEnergy
  rw [UpperBound.bond_expectation_full_eq_reduced hN_even hP hChain γ β]
  -- Step 2 — A4.4b: Xval = (1/N_R) · Yval.
  set Xval : ℂ := (psiTilde false P γ (-β)).toKet.dag *
    ((IsingModel.chainPairInteraction (0 : Fin (2*P+2)) :
      Qubits.NQubitOp (2*P+2)) * (psiTilde false P γ (-β)).toKet) with hXval_def
  have hA44b : Xval =
      (1 / ((2*P+2 : ℕ) : ℂ)) *
        ((psiTilde false P γ (-β)).toKet.dag *
          ((Hred_z_pm false P +
              ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
            (psiTilde false P γ (-β)).toKet)) := by
    have h := UpperBound.chainPairInteraction_expectation_eq_averaged P γ (-β)
    change (psiTilde false P γ (-β)).toKet.dag *
        ((IsingModel.chainPairInteraction (0 : Fin (2 * P + 2)) :
          Qubits.NQubitOp (2 * P + 2)) * (psiTilde false P γ (-β)).toKet) = _
    rw [JordanWigner.braOpKet_eq_dotProduct (psiTilde false P γ (-β)).toKet
        (IsingModel.chainPairInteraction (0 : Fin (2*P+2)))]
    rw [JordanWigner.braOpKet_eq_dotProduct (psiTilde false P γ (-β)).toKet
        (Hred_z_pm false P + ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2)))]
    exact h
  -- Step 3: Yval = ⟨ψ̃|Σ HredZMode|ψ̃⟩ = −2 Σ bHat·tauVec.
  -- First bridge the N_R cast: ((2*P+2 : ℕ) : ℂ) = ((2*P+2 : ℂ)) (R1).
  set Yval : ℂ := (psiTilde false P γ (-β)).toKet.dag *
    ((Hred_z_pm false P +
        ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))) *
      (psiTilde false P γ (-β)).toKet) with hYval_def
  have hYval_modes : Yval =
      ((-2 : ℂ)) * ∑ n : Fin P,
        ((bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ)
            (extendFin (fun i => -(β i))) : ℝ) : ℂ) := by
    rw [hYval_def]
    -- R1 cast: ((2*P+2 : ℕ) : ℂ) • 1 = ((2*P+2 : ℂ)) • 1
    rw [show ((2*P+2 : ℕ) : ℂ) • (1 : Qubits.NQubitOp (2*P+2))
          = ((2*P+2 : ℂ)) • (1 : Qubits.NQubitOp (2*P+2)) by push_cast; ring_nf]
    rw [JordanWigner.HredZDecomp_active P (psiTilde false P γ (-β)).toKet
        (psiTilde_inActiveSubspace γ β)]
    exact mode_sum_expectation γ β
  -- Step 4 — the algebra (mirrors the lower-bound algebra l.328–394, exact version).
  rw [show (((N : ℕ) : ℂ) * Xval) = (((N : ℝ) : ℂ)) * Xval from by push_cast; rfl]
  rw [Complex.re_ofReal_mul]
  -- Xval.re = (1/N_R) * Yval.re.
  have hN_R_real_ne : ((2*P+2 : ℕ) : ℝ) ≠ 0 := by
    have : (2*P + 2 : ℕ) ≠ 0 := by omega
    exact_mod_cast this
  have hXval_re : Xval.re = (1 / ((2*P+2 : ℕ) : ℝ)) * Yval.re := by
    have h := congrArg Complex.re hA44b
    rw [Complex.mul_re] at h
    have h1 : (1 / ((2*P+2 : ℕ) : ℂ)).im = 0 := by
      rw [show (1 / ((2*P+2 : ℕ) : ℂ)) = (((1 / ((2*P+2 : ℕ) : ℝ) : ℝ)) : ℂ) from by
        push_cast; field_simp]
      exact Complex.ofReal_im _
    have h2 : (1 / ((2*P+2 : ℕ) : ℂ)).re = 1 / ((2*P+2 : ℕ) : ℝ) := by
      rw [show (1 / ((2*P+2 : ℕ) : ℂ)) = (((1 / ((2*P+2 : ℕ) : ℝ) : ℝ)) : ℂ) from by
        push_cast; field_simp]
      exact Complex.ofReal_re _
    rw [h1, h2] at h
    -- h : Xval.re = (1/N_R) * Yval.re - 0 * Yval.im
    linarith
  rw [hXval_re]
  -- Yval.re = -2 Σ bHat·tauVec (real).
  have hYval_re : Yval.re =
      (-2 : ℝ) * ∑ n : Fin P,
        (bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ) (extendFin (fun i => -(β i)))) := by
    rw [hYval_modes]
    rw [show ((-2 : ℂ)) * ∑ n : Fin P,
        ((bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ)
            (extendFin (fun i => -(β i))) : ℝ) : ℂ)
        = (((-2 : ℝ) * ∑ n : Fin P,
            (bHat (waveVectorABC P n) ⬝ᵥ
              tauVec P (waveVectorABC P n) (extendFin γ)
                (extendFin (fun i => -(β i)))) : ℝ) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hYval_re]
  -- Now substitute bHat·tauVec = 1 − ε via geometric_form, reindex, and do field_simp.
  have hgeo : ∀ n : Fin P,
      (bHat (waveVectorABC P n) ⬝ᵥ
        tauVec P (waveVectorABC P n) (extendFin γ) (extendFin (fun i => -(β i))))
        = 1 - JordanWigner.epsilonMode (n : JordanWigner.WaveVectorABC P) γ β := by
    intro n
    have h := JordanWigner.geometric_form (n : JordanWigner.WaveVectorABC P) γ β
    -- h : epsilonMode n γ β = 1 - bHat·tauVec
    have : JordanWigner.epsilonMode (n : JordanWigner.WaveVectorABC P) γ β
        = 1 - (bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ) (extendFin (fun i => -(β i)))) := h
    linarith
  simp_rw [hgeo]
  -- reindex Σ_{n:Fin P} = Σ_{k ∈ K_ABC P}
  rw [show (∑ n : Fin P, (1 - JordanWigner.epsilonMode (n : JordanWigner.WaveVectorABC P) γ β))
        = ∑ k ∈ JordanWigner.K_ABC P, (1 - JordanWigner.epsilonMode k γ β) by
    rw [JordanWigner.K_ABC]; rfl]
  -- Final arithmetic. Σ(1 − ε) = P − Σε. N cancels.
  rw [Finset.sum_sub_distrib, Finset.sum_const, JordanWigner.K_ABC_card, nsmul_eq_mul, mul_one]
  have hN_pos : (0 : ℝ) < (N : ℝ) := by
    have : (2 : ℕ) ≤ N := by omega
    exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 2) this)
  have hN_ne : (N : ℝ) ≠ 0 := ne_of_gt hN_pos
  have hNR_eq : ((2*P+2 : ℕ) : ℝ) = (2*(P:ℝ) + 2) := by push_cast; ring
  rw [hNR_eq]
  have hPP : (0 : ℝ) < 2*(P:ℝ) + 2 := by positivity
  field_simp
  ring

/-- **PUBLIC #2.** Each per-mode residual energy is nonnegative, `ε_k ≥ 0`, since
`ε_k = ‖τ⃗_k(γ,−β) − b̂_k‖²/2` is a squared Euclidean norm divided by two
(arXiv:1911.12259v2 SM `eqn:eresk_geometrical_def`, l.957). -/
theorem epsilonMode_nonneg {P : ℕ} (k : JordanWigner.WaveVectorABC P) (γ β : Fin P → ℝ) :
    0 ≤ JordanWigner.epsilonMode k γ β := by
  unfold JordanWigner.epsilonMode
  positivity

end QAOA.IsingChain
