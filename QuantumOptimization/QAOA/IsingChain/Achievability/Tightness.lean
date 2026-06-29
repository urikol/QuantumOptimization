import QuantumOptimization.QAOA.IsingChain.Achievability.Angles
import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition
import QuantumOptimization.QAOA.ExponentialRealization

/-!
# Tightness — the residual energy attains `1/(2P+2)` (the achievability theorem)

The capstone of the achievability construction. Theorem B
(`residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum`) writes the residual energy
as `1/(2P+2) + (1/(2P+2))·Σ_k ε_k`; the core theorem
(`exists_angles_epsilonMode_eq_zero`, `Angles.lean`) supplies angle families
annihilating every `epsilonMode`, so the sum vanishes and the residual energy equals
exactly `1/(2P+2)` — **the achievability / saturation half of the FGG
ring-of-disagrees conjecture**, for `N` even with `2P+2 ≤ N`. Theorem A
(`residualEnergy_lower_bound`) upgrades attainment to an `IsLeast`:
`1/(2P+2)` is exactly the optimal residual energy, equivalently the optimal
approximation ratio is exactly `(2P+1)/(2P+2)`.

## Main statements
- `residualEnergy_attained` — **the achievability theorem**:
  `∃ γ β, residualEnergy = 1/(2P+2)`.
- `residualEnergy_isLeast` — `1/(2P+2)` is the least attainable residual energy.
-/

namespace QAOA.IsingChain.Achievability

open scoped BigOperators

/-- **THE ACHIEVABILITY THEOREM.** For the ring of disagrees with `N` even and
`2P+2 ≤ N`, depth-`P` QAOA attains residual energy exactly `1/(2P+2)`
(equivalently, approximation ratio exactly `(2P+1)/(2P+2)`): there exist angle
families `γ, β` with `residualEnergy hChain γ β = 1/(2P+2)`. Together with
Theorem A this resolves the saturation half of the Farhi–Goldstone–Gutmann
ring-of-disagrees conjecture.

The core construction `exists_angles_epsilonMode_eq_zero` (`Angles.lean`) supplies
angle families annihilating every `epsilonMode`; Theorem B
(`residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum`) then collapses the
per-mode sum to `0`, leaving exactly `1/(2P+2)`. -/
theorem residualEnergy_attained {N P : ℕ}
    (hN_even : 2 ∣ N) (hP : 2 * P + 2 ≤ N) :
    ∃ γ β : Fin P → ℝ, residualEnergy (ringQAOA N) γ β = 1 / (2 * P + 2) := by
  set hChain : IsingChainQAOAExponentials N (ringOfDisagreesCouplings N) := ringQAOA N
  obtain ⟨γ, β, hzero⟩ := exists_angles_epsilonMode_eq_zero P
  refine ⟨γ, β, ?_⟩
  rw [residualEnergy_eq_one_div_two_P_plus_two_add_modes_sum hN_even hP hChain γ β]
  rw [Finset.sum_eq_zero (fun k _ => hzero k), mul_zero, add_zero]

/-- **Optimality.** `1/(2P+2)` is the least attainable residual energy of the
canonical depth-`P` exponential QAOA on the ring of disagrees (`N` even,
`2P+2 ≤ N`) — equivalently the optimal approximation ratio is exactly
`(2P+1)/(2P+2)`: attained by `residualEnergy_attained`, bounded below by Theorem A
(`residualEnergy_lower_bound`). -/
theorem residualEnergy_isLeast {N P : ℕ}
    (hN_even : 2 ∣ N) (hP : 2 * P + 2 ≤ N) :
    IsLeast {e | ∃ γ β : Fin P → ℝ, residualEnergy (ringQAOA N) γ β = e}
      (1 / (2 * P + 2)) :=
  ⟨residualEnergy_attained hN_even hP,
    fun _ ⟨γ, β, he⟩ => he ▸ residualEnergy_lower_bound hN_even hP γ β⟩

end QAOA.IsingChain.Achievability
