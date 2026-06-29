import QuantumOptimization.QAOA.IsingChain.Achievability.ComplementRoots
import QuantumOptimization.QAOA.IsingChain.Achievability.Factorization
import QuantumOptimization.QAOA.IsingChain.Achievability.Realization

/-!
# Angles — optimal QAOA angle families exist (the core achievability theorem)

The final composition of the achievability chain. The explicit pair
`(Rpoly P, Tpoly P)` is a member of the SU(2) Laurent class (`isClassL_R_T`,
the Fejér–Riesz step); every class member factors into a diagonal times primitive
equatorial factors (`exists_primFactor_decomposition`, the Haah step); every such
factorization is realized by a QAOA circuit whose `Gmat` off-diagonal entry vanishes
wherever `b` does (`exists_angles_of_decomposition`, the dictionary step); `Tpoly`
vanishes at every active wavevector node (`Tpoly_eval_node`); and a vanishing
off-diagonal forces the per-mode residual energy to zero
(`epsilonMode_eq_zero_of_G21_eq_zero`, the Bloch-bridge keystone). Composing:
**there exist depth-`P` angle families annihilating every `epsilonMode`** — the
`N`-free core of the FGG ring-of-disagrees achievability conjecture.

## Main statements
- `exists_angles_epsilonMode_eq_zero` — the core theorem.
- `qspRealizable_holds` — the general realizability predicate `QSPRealizable P`
  holds for every `P` (the same composition for an arbitrary class member).
-/

namespace QAOA.IsingChain.Achievability

/-- **The general QSP realizability theorem**: every member of the SU(2) Laurent
class at half-degree `2P+1` is realized by real QAOA angle families, in the sense
that vanishing of the off-diagonal polynomial `b` at an active node forces the
corresponding per-mode residual energy to vanish. -/
theorem qspRealizable_holds (P : ℕ) : QSPRealizable P := by
  intro a b hclass
  obtain ⟨φ, χ, hmat⟩ := exists_primFactor_decomposition (2 * P + 1) a b hclass
  obtain ⟨γ, β, hG⟩ := exists_angles_of_decomposition P a b φ χ hmat
  refine ⟨γ, β, fun n hb => ?_⟩
  exact epsilonMode_eq_zero_of_G21_eq_zero P n γ β
    (hG (JordanWigner.waveVectorABC P n) hb)

/-- **The core achievability theorem (`N`-free).** There exist depth-`P` angle
families `γ, β` driving every per-mode residual energy to zero:
`∃ γ β, ∀ k, ε_k(γ, β) = 0`. -/
theorem exists_angles_epsilonMode_eq_zero (P : ℕ) :
    ∃ γ β : Fin P → ℝ, ∀ k : JordanWigner.WaveVectorABC P,
      JordanWigner.epsilonMode k γ β = 0 := by
  obtain ⟨γ, β, h⟩ := qspRealizable_holds P (Rpoly P) (Tpoly P) (isClassL_R_T P)
  exact ⟨γ, β, fun n => h n (Tpoly_eval_node P n)⟩

end QAOA.IsingChain.Achievability
