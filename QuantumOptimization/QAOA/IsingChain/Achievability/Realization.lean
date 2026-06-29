import QuantumOptimization.QAOA.IsingChain.Achievability.Su2Class
import QuantumOptimization.QAOA.IsingChain.Achievability.BlochBridge

/-!
# Primitive-product → QAOA-circuit realization (the angle dictionary)

The **angle dictionary**: any SU(2)-class member that factors as a diagonal phase times
a product of equatorial primitive factors `diagPhaseMat χ · ∏_j primFactor (φ j)` is
*realized* by an explicit QAOA circuit `Gmat P k (extendFin γ) (extendFin β)`, in the
precise sense that the circuit's magnetization off-diagonal `G₂₁(k)` vanishes at every
node `k` where the encoding polynomial `b` vanishes.

The bridge is a `2×2` matrix identity, established entrywise after evaluating the
polynomial product at `w = e^{ik}`:

`Gmat P k (extendFin γ) (extendFin β) = (unimodular) · Dc(−s₀) · evalMat (e^{ik}) (RHS) · Dc(t_{2P})`,

a *pure diagonal dressing* of the evaluated factorization. Both dressings are
unit-modulus diagonals, so the `(1,0)` entry of the LHS is a nonzero scalar times the
`(1,0)` entry of the evaluated RHS, which is exactly `b.eval (e^{ik})` (via `hmat` and
`(classMat L a b) 1 0 = b`). Hence `b.eval (e^{ik}) = 0 ⟹ G₂₁(k) = 0`.

All signs are pinned bit-for-bit and numerically validated
(machine-precision validation to ~1e-15 at P = 1,2,3,5).

## Main definitions
- `Dc`: the diagonal phase generator `diag(e^{it}, e^{−it})` — the common normal-form atom.
- `evalMat`: evaluate a polynomial matrix at `w` entrywise.
- `Dprod`: the alternating diagonal/`Wmat` product `W·∏(Dc sⱼ · W)` (shared normal form).

## Main statements
- `exists_angles_of_decomposition` — **the frozen interface**: a decomposing class member
  is realized by real angle families with `G₂₁ = 0` at every node of `b`.
-/

namespace QAOA.IsingChain.Achievability

open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- The diagonal phase generator `Dc` and its algebra
-- ============================================================================

/-- The diagonal phase generator `Dc t = diag(e^{it}, e^{−it})` — the common normal-form
atom into which `Bmat`, `Amat`, `diagPhaseMat` and the equatorial conjugations all
collapse. -/
def Dc (t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (t * Complex.I), 0; 0, Complex.exp (-t * Complex.I)]

@[simp] theorem Dc_apply_zero_zero (t : ℝ) : Dc t 0 0 = Complex.exp (t * Complex.I) := rfl
@[simp] theorem Dc_apply_zero_one (t : ℝ) : Dc t 0 1 = 0 := rfl
@[simp] theorem Dc_apply_one_zero (t : ℝ) : Dc t 1 0 = 0 := rfl
@[simp] theorem Dc_apply_one_one (t : ℝ) : Dc t 1 1 = Complex.exp (-t * Complex.I) := rfl

/-- `Dc` multiplies by adding phases: `Dc s · Dc t = Dc (s + t)`. -/
theorem Dc_mul (s t : ℝ) : Dc s * Dc t = Dc (s + t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dc, Matrix.mul_apply, Fin.sum_univ_two, ← Complex.exp_add] <;>
    ring_nf

/-- `Dc 0 = 1`. -/
theorem Dc_zero : Dc 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dc]

/-- `Dc t · Dc (−t) = 1`. -/
theorem Dc_neg (t : ℝ) : Dc t * Dc (-t) = 1 := by
  rw [Dc_mul, add_neg_cancel, Dc_zero]

/-- `e^{−iπ} = −1`. -/
theorem exp_neg_pi_eq_neg_one : Complex.exp (-((Real.pi : ℂ) * Complex.I)) = -1 := by
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num

/-- `Dc π = −1` (the matrix negation of the identity). -/
theorem Dc_pi : Dc Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dc, exp_neg_pi_eq_neg_one]

/-- The mixer generator is a `Dc`: `Bmat β = Dc (2β)`. -/
theorem Bmat_eq_Dc (β : ℝ) : Bmat β = Dc (2 * β) := by
  unfold Bmat Dc
  norm_num [Complex.ofReal_mul]

/-- The cost generator is a `Dc`: `Amat γ = Dc (−2γ)`. -/
theorem Amat_eq_Dc (γ : ℝ) : Amat γ = Dc (-(2 * γ)) := by
  unfold Amat Dc
  norm_num [Complex.ofReal_mul]

-- ---------------------------------------------------------------------------
-- The reflection identity `Wmat (−k) = Dc (π/2) · Wmat k · Dc (−π/2)`
-- ---------------------------------------------------------------------------

/-- `e^{i π/2} = i` (cast-normalized form matching `Dc`'s `(0,0)` entry at `π/2`). -/
theorem exp_pi_div_two : Complex.exp ((Real.pi : ℂ) / 2 * Complex.I) = Complex.I := by
  rw [Complex.exp_pi_div_two_mul_I]

/-- `e^{−i π/2} = −i`. -/
theorem exp_neg_pi_div_two : Complex.exp (-((Real.pi : ℂ) / 2 * Complex.I)) = -Complex.I := by
  rw [Complex.exp_neg, Complex.exp_pi_div_two_mul_I, Complex.inv_I]

/-- `Dc (π/2) = diag(i, −i)`. -/
theorem Dc_pi_div_two : Dc (Real.pi / 2) = !![Complex.I, 0; 0, -Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dc, exp_neg_pi_div_two]

/-- `Dc (−(π/2)) = diag(−i, i)`. -/
theorem Dc_neg_pi_div_two : Dc (-(Real.pi / 2)) = !![-Complex.I, 0; 0, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Dc, exp_neg_pi_div_two]

/-- `i · z · i = −z` (used to collapse the conjugation `diag(i,−i)·Wmat·diag(−i,i)`). -/
theorem I_mul_mul_I (z : ℂ) : Complex.I * z * Complex.I = -z := by
  rw [mul_comm Complex.I z, mul_assoc, Complex.I_mul_I, mul_neg_one]

/-- **The reflection identity.** `Wmat (−k) = Dc (π/2) · Wmat k · Dc (−π/2)`: conjugating
`Wmat k` by `diag(i, −i)` flips the off-diagonal signs exactly, which is `Wmat (−k)`
(real entries, `cos` even, `sin` odd). Verified entrywise; the python pins the sign. -/
theorem Wmat_neg (k : ℝ) : Wmat (-k) = Dc (Real.pi / 2) * Wmat k * Dc (-(Real.pi / 2)) := by
  rw [Dc_pi_div_two, Dc_neg_pi_div_two, Wmat, Wmat, Matrix.mul_fin_two, Matrix.mul_fin_two,
    show Real.cos (-k / 2) = Real.cos (k / 2) by rw [show -k / 2 = -(k/2) by ring, Real.cos_neg],
    show Real.sin (-k / 2) = -Real.sin (k / 2) by rw [show -k / 2 = -(k/2) by ring, Real.sin_neg]]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [I_mul_mul_I]

-- ============================================================================
-- The shared alternating normal form `Dprod` and the circuit reduction
-- ============================================================================

/-- The alternating diagonal/`Wmat` product
`Dprod k [s₀, s₁, …, sₙ] = Wmat k · (Dc s₀ · Wmat k) · (Dc s₁ · Wmat k) · ⋯ · (Dc sₙ · Wmat k)`,
i.e. `(n+1)` interior `Dc`-factors between `(n+2)` copies of `Wmat k`. This is the common
normal form into which BOTH the QAOA circuit `Gmat` and the evaluated primitive product
collapse. -/
def Dprod (k : ℝ) (S : List ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Wmat k * (S.map (fun s => Dc s * Wmat k)).prod

@[simp] theorem Dprod_nil (k : ℝ) : Dprod k [] = Wmat k := by
  simp [Dprod]

/-- Cons unfolding: prepending `s` adds a leading `Wmat k · Dc s` before the rest. -/
theorem Dprod_cons (k s : ℝ) (S : List ℝ) :
    Dprod k (s :: S) = Wmat k * Dc s * Dprod k S := by
  simp only [Dprod, List.map_cons, List.prod_cons, ← Matrix.mul_assoc]

/-- The per-layer circuit sequence read off the angles: layer `m` contributes the pair
`[2β_m + π/2, −π/2 − 2γ_m]`, with the **outermost** layer (`P−1`) first. Recurses on the
layer count `P`. -/
def circuitSeq (P : ℕ) (γ β : ℕ → ℝ) : List ℝ :=
  match P with
  | 0 => []
  | Nat.succ p => (2 * β p + Real.pi / 2) :: (-(Real.pi / 2) - 2 * γ p) :: circuitSeq p γ β

/-- **The clean circuit recursion.**
`Gmat (p+1) = Wmat k · Dc(2β_p+π/2) · Wmat k · Dc(−π/2−2γ_p) · Gmat p`.
Unfolds one `Uk` layer, rewrites `Bmat = Dc(2β)`, `Amat = Dc(−2γ)`, `Wmat(−k)` via the
reflection identity, and folds the adjacent `Dc`s. The python pins every sign. -/
theorem Gmat_succ (p : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    Gmat (p + 1) k γ β
      = Wmat k * Dc (2 * β p + Real.pi / 2) * Wmat k * Dc (-(Real.pi / 2) - 2 * γ p)
          * Gmat p k γ β := by
  rw [Gmat, Uk, Gmat, Bmat_eq_Dc, Amat_eq_Dc, Wmat_neg]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Dc (2 * β p)) (Dc (Real.pi / 2)), Dc_mul]
  rw [show Dc (-(Real.pi / 2)) * (Dc (-(2 * γ p)) * (Wmat k * Uk p k γ β))
      = (Dc (-(Real.pi / 2)) * Dc (-(2 * γ p))) * (Wmat k * Uk p k γ β) by
    rw [Matrix.mul_assoc]]
  rw [Dc_mul, show -(Real.pi / 2) + -(2 * γ p) = -(Real.pi / 2) - 2 * γ p by ring]

/-- **Circuit reduction.** `Gmat P k γ β = Dprod k (circuitSeq P γ β)`. By induction on `P`,
using the clean layer recursion `Gmat_succ` and the `Dprod` cons rule. -/
theorem Gmat_eq_Dprod (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    Gmat P k γ β = Dprod k (circuitSeq P γ β) := by
  induction P with
  | zero => simp [Gmat, Uk, circuitSeq, Dprod]
  | succ p ih =>
      rw [Gmat_succ, circuitSeq, Dprod_cons, Dprod_cons, ih]
      simp only [Matrix.mul_assoc]

-- ============================================================================
-- Evaluating the polynomial matrices at `w = e^{ik}`
-- ============================================================================

/-- Evaluate a polynomial matrix at `w` entrywise. -/
def evalMat (w : ℂ) (M : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) : Matrix (Fin 2) (Fin 2) ℂ :=
  M.map (Polynomial.eval w)

/-- `evalMat` is multiplicative (it is the entrywise image of the ring hom `evalRingHom w`). -/
theorem evalMat_mul (w : ℂ) (A B : Matrix (Fin 2) (Fin 2) (Polynomial ℂ)) :
    evalMat w (A * B) = evalMat w A * evalMat w B := by
  unfold evalMat
  rw [← Polynomial.coe_evalRingHom, Matrix.map_mul]

/-- `evalMat` of a `List.prod` is the `List.prod` of the evaluated factors. -/
theorem evalMat_list_prod (w : ℂ) (L : List (Matrix (Fin 2) (Fin 2) (Polynomial ℂ))) :
    evalMat w L.prod = (L.map (evalMat w)).prod := by
  induction L with
  | nil => simp [evalMat, Matrix.map_one, Polynomial.eval_one, Polynomial.eval_zero]
  | cons A T ih => rw [List.prod_cons, evalMat_mul, ih, List.map_cons, List.prod_cons]

/-- `evalMat` of the diagonal phase matrix is the scalar diagonal `Dc χ`. -/
theorem evalMat_diagPhaseMat (w : ℂ) (χ : ℝ) :
    evalMat w (diagPhaseMat χ) = Dc χ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evalMat, diagPhaseMat, Dc, neg_mul]

/-- Raw evaluation of a primitive factor: `evalMat w (primFactor φ) = w·E + (1 − E)` where
`E = equatorialProj φ` (the `w·P + (I − P)` form, evaluated). -/
theorem evalMat_primFactor_raw (w : ℂ) (φ : ℝ) :
    evalMat w (primFactor φ) = w • equatorialProj φ + (1 - equatorialProj φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [evalMat, primFactor, equatorialProj, Matrix.add_apply, Matrix.sub_apply,
      Matrix.map_apply] <;>
    ring

/-- The signal rotation `Wmat k` is the symmetric phase combination of the canonical
equatorial projector `E₊ = equatorialProj (−π/2) = (I − σy)/2` and its complement:
`e^{ik/2}·E₊ + e^{−ik/2}·(I − E₊) = Wmat k`. -/
theorem Wmat_eq_phase_eqProj (k : ℝ) :
    Complex.exp (Complex.I * (k / 2)) • equatorialProj (-(Real.pi / 2))
        + Complex.exp (-(Complex.I * (k / 2))) • (1 - equatorialProj (-(Real.pi / 2)))
      = Wmat k := by
  have hcos : Complex.exp (Complex.I * (↑k / 2 : ℂ))
      = Complex.cos (↑k / 2) + Complex.sin (↑k / 2) * Complex.I := by
    rw [show Complex.I * (↑k / 2 : ℂ) = (↑k / 2 : ℂ) * Complex.I by ring, Complex.exp_mul_I]
  have hcosn : Complex.exp (-(Complex.I * (↑k / 2 : ℂ)))
      = Complex.cos (↑k / 2) - Complex.sin (↑k / 2) * Complex.I := by
    rw [show -(Complex.I * (↑k / 2 : ℂ)) = -((↑k / 2 : ℂ)) * Complex.I by ring, Complex.exp_mul_I,
      Complex.cos_neg, Complex.sin_neg]; ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [equatorialProj, Wmat, Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      smul_eq_mul, exp_neg_pi_div_two, hcos, hcosn] <;>
    ring_nf <;>
    simp [Complex.I_sq]

-- ---------------------------------------------------------------------------
-- The equatorial conjugation `Dc t · E_ψ · Dc(−t) = E_{ψ − 2t}` and `Wmat` decomposition
-- ---------------------------------------------------------------------------

set_option linter.flexible false in
/-- **Equatorial conjugation.** `Dc t · equatorialProj ψ · Dc (−t) = equatorialProj (ψ − 2t)`:
conjugating an equatorial projector by the diagonal phase shifts its Bloch phase by `−2t`.
Verified entrywise; the python pins the `−2t` sign. The `simp` extraction is flexible (it must
reduce the `2×2` indexing); the four residual complex equations are closed uniformly. -/
theorem Dc_conj_equatorialProj (t ψ : ℝ) :
    Dc t * equatorialProj ψ * Dc (-t) = equatorialProj (ψ - 2 * t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Dc, equatorialProj, Matrix.mul_apply, Fin.sum_univ_two]
  -- after plain extraction the four entries are clean complex equations (`2⁻¹` / `/2` forms)
  all_goals first
    | (rw [mul_comm _ ((2:ℂ)⁻¹), mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero,
        mul_one])
    | (rw [mul_comm _ ((2:ℂ)⁻¹), mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
        mul_one])
    | (rw [show ∀ a b c : ℂ, a * (b / 2) * c = (a * b * c) / 2 from fun a b c => by ring,
        ← Complex.exp_add, ← Complex.exp_add]; congr 2; ring)

/-- The equatorial projector at phase `φ` is the diagonal conjugate of the canonical one:
`equatorialProj φ = Dc t · equatorialProj (−π/2) · Dc (−t)` with `t = −(φ + π/2)/2`. -/
theorem equatorialProj_eq_conj (φ : ℝ) :
    equatorialProj φ
      = Dc (-(φ + Real.pi / 2) / 2) * equatorialProj (-(Real.pi / 2))
          * Dc (-(-(φ + Real.pi / 2) / 2)) := by
  rw [Dc_conj_equatorialProj]
  congr 1
  ring

/-- The complement of an equatorial projector conjugates identically:
`1 − Dc t · E · Dc (−t) = Dc t · (1 − E) · Dc (−t)` (uses `Dc t · Dc (−t) = 1`). -/
theorem one_sub_Dc_conj (t : ℝ) (E : Matrix (Fin 2) (Fin 2) ℂ) :
    1 - Dc t * E * Dc (-t) = Dc t * (1 - E) * Dc (-t) := by
  rw [mul_sub, sub_mul, mul_one, Dc_neg]

/-- **Per-slot evaluation.** At the node `w = e^{ik}`, a primitive factor evaluates to a
unit-modulus scalar times a `Dc`-conjugated signal rotation:
`evalMat (e^{ik}) (primFactor φ) = e^{ik/2} • (Dc t · Wmat k · Dc (−t))` with `t = −(φ+π/2)/2`.
Combines the raw evaluation, the equatorial conjugation, and the `Wmat` decomposition. The
python pins the `t = −(φ+π/2)/2` sign. -/
theorem evalMat_primFactor (φ k : ℝ) :
    evalMat (Complex.exp (Complex.I * k)) (primFactor φ)
      = Complex.exp (Complex.I * (k / 2)) •
          (Dc (-(φ + Real.pi / 2) / 2) * Wmat k * Dc (-(-(φ + Real.pi / 2) / 2))) := by
  set t : ℝ := -(φ + Real.pi / 2) / 2 with ht
  rw [evalMat_primFactor_raw, equatorialProj_eq_conj φ, ← ht]
  -- the `(1 - Dc t E Dc(-t))` block via `one_sub_Dc_conj`
  rw [one_sub_Dc_conj t (equatorialProj (-(Real.pi / 2)))]
  -- replace the inner `Wmat k` by its equatorial decomposition, then match by mul/smul algebra
  rw [← Wmat_eq_phase_eqProj k]
  have hzz : Complex.exp (Complex.I * (k : ℂ))
      = Complex.exp (Complex.I * (k / 2)) * Complex.exp (Complex.I * (k / 2)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h1 : (1 : ℂ)
      = Complex.exp (Complex.I * (k / 2)) * Complex.exp (-(Complex.I * (k / 2))) := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  rw [hzz]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, smul_add,
    smul_smul, Matrix.mul_assoc]
  rw [← h1, one_smul]

-- ============================================================================
-- Telescoping `Dc χ · ∏ⱼ (Dc tⱼ · W · Dc(−tⱼ))` into the `Dprod` normal form
-- ============================================================================

/-- The per-slot conjugated-`Wmat` factor `Dc s · Wmat k · Dc (−s)`. -/
def pfoldFactor (k s : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := Dc s * Wmat k * Dc (-s)

/-- The consecutive-difference list `[t₀−prev, t₁−t₀, …, tₙ−tₙ₋₁]` (threads `prev`). -/
def consecDiffs (prev : ℝ) (ts : List ℝ) : List ℝ :=
  match ts with
  | [] => []
  | t :: T => (t - prev) :: consecDiffs t T

/-- The last value of `prev :: ts` (total; `prev` if `ts` empty). -/
def lastVal (prev : ℝ) (ts : List ℝ) : ℝ :=
  match ts with
  | [] => prev
  | t :: T => lastVal t T

/-- **Telescoping.** `Dc A · ∏ⱼ (Dc tⱼ · W · Dc(−tⱼ)) = Dc(A+t₀) · Dprod k (consecDiffs t₀ T)
· Dc(−lastVal t₀ T)` for `ts = t₀ :: T`. By induction on `T` with a running leading phase: each
peeled head merges `Dc A · Dc t₀ = Dc(A+t₀)`, emits a `Wmat k`, and recurses with leading
phase `−t₀`. The python pins the merge. -/
theorem Dc_mul_pfold_cons (k A t₀ : ℝ) (T : List ℝ) :
    Dc A * ((t₀ :: T).map (pfoldFactor k)).prod
      = Dc (A + t₀) * Dprod k (consecDiffs t₀ T) * Dc (-(lastVal t₀ T)) := by
  induction T generalizing A t₀ with
  | nil =>
      simp only [consecDiffs, lastVal, Dprod_nil, List.map_cons, List.map_nil, List.prod_cons,
        List.prod_nil, pfoldFactor, mul_one]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Dc_mul]
  | cons t₁ T' ih =>
      rw [List.map_cons, List.prod_cons]
      rw [show pfoldFactor k t₀ = Dc t₀ * Wmat k * Dc (-t₀) from rfl]
      -- `Dc A · (Dc t₀ · W · Dc(-t₀)) · rest = Dc(A+t₀) · W · (Dc(-t₀) · rest)`
      rw [show Dc A * (Dc t₀ * Wmat k * Dc (-t₀) * ((t₁ :: T').map (pfoldFactor k)).prod)
          = (Dc A * Dc t₀) * Wmat k * (Dc (-t₀) * ((t₁ :: T').map (pfoldFactor k)).prod) by
        simp only [Matrix.mul_assoc]]
      rw [Dc_mul, ih (-t₀) t₁]
      -- assemble: consecDiffs t₀ (t₁::T') = (t₁-t₀)::consecDiffs t₁ T'; lastVal t₀ (t₁::T') = lastVal t₁ T'
      rw [consecDiffs, Dprod_cons, lastVal]
      simp only [Matrix.mul_assoc]
      congr 2
      rw [show -t₀ + t₁ = t₁ - t₀ by ring]

-- ============================================================================
-- Realizing an arbitrary even-length interior sequence by real angle families
-- ============================================================================

/-- `circuitSeq P` only reads `γ, β` at indices `< P`, so it is a congruence in that range. -/
theorem circuitSeq_congr (P : ℕ) (γ β γ' β' : ℕ → ℝ)
    (hγ : ∀ i < P, γ i = γ' i) (hβ : ∀ i < P, β i = β' i) :
    circuitSeq P γ β = circuitSeq P γ' β' := by
  induction P with
  | zero => rfl
  | succ p ih =>
      rw [circuitSeq, circuitSeq, hγ p (Nat.lt_succ_self p), hβ p (Nat.lt_succ_self p),
        ih (fun i hi => hγ i (Nat.lt_succ_of_lt hi)) (fun i hi => hβ i (Nat.lt_succ_of_lt hi))]

/-- **Interior realizability.** Any even-length list `S` (length `2P`) is the circuit
sequence of some real angle families: `∃ γ β : Fin P → ℝ, circuitSeq P (extendFin γ)
(extendFin β) = S`. Built by induction on `P`, peeling the leading layer pair off `S`. -/
theorem exists_angles_circuitSeq (P : ℕ) (S : List ℝ) (hlen : S.length = 2 * P) :
    ∃ γ β : Fin P → ℝ,
      circuitSeq P (JordanWigner.extendFin γ) (JordanWigner.extendFin β) = S := by
  induction P generalizing S with
  | zero =>
      refine ⟨Fin.elim0, Fin.elim0, ?_⟩
      rw [circuitSeq]
      exact (List.length_eq_zero_iff.mp (by simpa using hlen)).symm
  | succ p ih =>
      -- S has length 2p+2 ≥ 2, so S = s₀ :: s₁ :: rest with rest.length = 2p
      match S, hlen with
      | s₀ :: s₁ :: rest, hlen =>
        have hrest : rest.length = 2 * p := by
          simpa [Nat.mul_succ] using hlen
        obtain ⟨γ', β', hgb⟩ := ih rest hrest
        -- extend γ', β' with the new outermost layer values
        refine ⟨Fin.snoc γ' (-(s₁ + Real.pi / 2) / 2), Fin.snoc β' ((s₀ - Real.pi / 2) / 2), ?_⟩
        rw [circuitSeq]
        -- the head pair from index p, then `circuitSeq p` over the snoc'd families = rest
        have hβp : JordanWigner.extendFin (Fin.snoc β' ((s₀ - Real.pi / 2) / 2)) p
            = (s₀ - Real.pi / 2) / 2 := by
          rw [JordanWigner.extendFin, dif_pos (Nat.lt_succ_self p)]
          simp [Fin.snoc]
        have hγp : JordanWigner.extendFin (Fin.snoc γ' (-(s₁ + Real.pi / 2) / 2)) p
            = -(s₁ + Real.pi / 2) / 2 := by
          rw [JordanWigner.extendFin, dif_pos (Nat.lt_succ_self p)]
          simp [Fin.snoc]
        rw [hβp, hγp]
        have hcong : circuitSeq p (JordanWigner.extendFin (Fin.snoc γ' (-(s₁ + Real.pi / 2) / 2)))
            (JordanWigner.extendFin (Fin.snoc β' ((s₀ - Real.pi / 2) / 2)))
            = circuitSeq p (JordanWigner.extendFin γ') (JordanWigner.extendFin β') := by
          refine circuitSeq_congr p _ _ _ _ (fun i hi => ?_) (fun i hi => ?_)
          · rw [JordanWigner.extendFin, JordanWigner.extendFin,
              dif_pos (Nat.lt_succ_of_lt hi), dif_pos hi]
            exact Fin.snoc_castSucc (i := ⟨i, hi⟩) ..
          · rw [JordanWigner.extendFin, JordanWigner.extendFin,
              dif_pos (Nat.lt_succ_of_lt hi), dif_pos hi]
            exact Fin.snoc_castSucc (i := ⟨i, hi⟩) ..
        rw [hcong, hgb]
        congr 1
        · ring
        · congr 1
          ring

-- ============================================================================
-- Evaluating the full primitive product: scalar factoring and the (1,0) link
-- ============================================================================

/-- Pulling a common scalar out of a `List.prod` of scaled matrices:
`∏ (c • Mⱼ) = c^(len) • ∏ Mⱼ`. -/
theorem prod_smul_list (c : ℂ) (L : List (Matrix (Fin 2) (Fin 2) ℂ)) :
    (L.map (fun M => c • M)).prod = c ^ L.length • L.prod := by
  induction L with
  | nil => simp
  | cons M T ih =>
      rw [List.map_cons, List.prod_cons, ih, List.prod_cons, List.length_cons, pow_succ,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      congr 1
      ring

/-- `consecDiffs` preserves length. -/
theorem consecDiffs_length (prev : ℝ) (ts : List ℝ) :
    (consecDiffs prev ts).length = ts.length := by
  induction ts generalizing prev with
  | nil => rfl
  | cons t T ih => rw [consecDiffs, List.length_cons, List.length_cons, ih]

/-- The half-angle node phase `z = e^{ik/2}` is nonzero. -/
theorem z_ne_zero (k : ℝ) : Complex.exp (Complex.I * (k / 2)) ≠ 0 := Complex.exp_ne_zero _

/-- **Full-product evaluation.** Evaluating the primitive product at `w = e^{ik}` gives a
unit-modulus scalar power times the `pfoldFactor` product:
`evalMat (e^{ik}) (∏ⱼ primFactor (φ j)) = (e^{ik/2})^(2P+1) • ∏ⱼ pfoldFactor k (tⱼ)`,
with `tⱼ = −(φ j + π/2)/2`. Combines `evalMat`-multiplicativity, the per-slot evaluation,
and the scalar-factoring `prod_smul_list`. -/
theorem evalMat_prod (P : ℕ) (φ : Fin (2 * P + 1) → ℝ) (k : ℝ) :
    evalMat (Complex.exp (Complex.I * k))
        (List.ofFn fun j : Fin (2 * P + 1) => primFactor (φ j)).prod
      = Complex.exp (Complex.I * (k / 2)) ^ (2 * P + 1) •
          (List.ofFn fun j : Fin (2 * P + 1) =>
            pfoldFactor k (-(φ j + Real.pi / 2) / 2)).prod := by
  rw [evalMat_list_prod, List.map_ofFn]
  have hslot : (fun j : Fin (2 * P + 1) => evalMat (Complex.exp (Complex.I * k)) (primFactor (φ j)))
      = fun j : Fin (2 * P + 1) =>
        Complex.exp (Complex.I * (k / 2)) • pfoldFactor k (-(φ j + Real.pi / 2) / 2) := by
    funext j
    rw [evalMat_primFactor]
    rfl
  rw [show (Function.comp (evalMat (Complex.exp (Complex.I * k)))
        fun j : Fin (2 * P + 1) => primFactor (φ j))
      = fun j : Fin (2 * P + 1) => evalMat (Complex.exp (Complex.I * k)) (primFactor (φ j)) from rfl,
    hslot]
  rw [show (List.ofFn fun j : Fin (2 * P + 1) =>
        Complex.exp (Complex.I * (k / 2)) • pfoldFactor k (-(φ j + Real.pi / 2) / 2))
      = (List.ofFn fun j : Fin (2 * P + 1) => pfoldFactor k (-(φ j + Real.pi / 2) / 2)).map
          (fun M => Complex.exp (Complex.I * (k / 2)) • M) by rw [List.map_ofFn]; rfl]
  rw [prod_smul_list, List.length_ofFn]

/-- The `(1,0)` entry of a diagonal-dressed matrix `Dc a · M · Dc b` is the scaled `(1,0)`
entry of `M`: `(Dc a · M · Dc b) 1 0 = e^{−ia} · M₁₀ · e^{ib}`. (Diagonal left/right
multiplication scales row 1 / column 0.) -/
theorem Dc_mul_mul_Dc_apply_one_zero (a b : ℝ) (M : Matrix (Fin 2) (Fin 2) ℂ) :
    (Dc a * M * Dc b) 1 0
      = Complex.exp (-a * Complex.I) * M 1 0 * Complex.exp (b * Complex.I) := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp [Dc]

-- ============================================================================
-- The frozen interface: a decomposing class member is realized by real angles
-- ============================================================================

/-- **THE ANGLE DICTIONARY.** Any class member that decomposes into a diagonal times
primitive equatorial factors is realized by a QAOA circuit: there are real angle families
`(γ, β)` whose magnetization `Gmat` has vanishing `(1,0)` entry at every node `k` where the
encoding polynomial `b` vanishes on the unit circle.

The proof constructs the angles from the factorization data via the telescoped normal form
`Dprod` (`exists_angles_circuitSeq`), establishes the diagonal-dressing identity
`Dc(χ+t₀)·Gmat·Dc(−lastVal) = Dc χ · ∏ pfoldFactor` (telescoping `Dc_mul_pfold_cons`), and
extracts the `(1,0)` entry: `Gmat₁₀ = (unit)·b.eval(e^{ik})·(unit)`, which vanishes with
`b.eval`. All signs pinned bit-for-bit (numerically validated). -/
theorem exists_angles_of_decomposition (P : ℕ) (a b : Polynomial ℂ)
    (φ : Fin (2 * P + 1) → ℝ) (χ : ℝ)
    (hmat : classMat (2 * P + 1) a b
      = diagPhaseMat χ * (List.ofFn fun j : Fin (2 * P + 1) => primFactor (φ j)).prod) :
    ∃ γ β : Fin P → ℝ, ∀ k : ℝ,
      b.eval (Complex.exp (Complex.I * k)) = 0 →
      Gmat P k (JordanWigner.extendFin γ) (JordanWigner.extendFin β) 1 0 = 0 := by
  -- the `t`-sequence and its head/tail decomposition (nonempty since `2P+1 ≥ 1`)
  set tfun : Fin (2 * P + 1) → ℝ := fun j => -(φ j + Real.pi / 2) / 2 with htfun
  set tlist : List ℝ := List.ofFn tfun with htlist
  -- `tlist = t₀ :: T`
  obtain ⟨t₀, T, htlistEq⟩ : ∃ t₀ T, tlist = t₀ :: T := by
    refine ⟨tfun 0, List.ofFn (fun i : Fin (2 * P) => tfun i.succ), ?_⟩
    rw [htlist, List.ofFn_succ]
  -- the interior circuit sequence and its realizability by real angles
  set S : List ℝ := consecDiffs t₀ T with hS
  have hSlen : S.length = 2 * P := by
    rw [hS, consecDiffs_length]
    have hTlen : T.length = 2 * P := by
      have := congrArg List.length htlistEq
      rw [htlist, List.length_ofFn, List.length_cons] at this
      omega
    rw [hTlen]
  obtain ⟨γ, β, hgb⟩ := exists_angles_circuitSeq P S hSlen
  refine ⟨γ, β, fun k hb => ?_⟩
  -- the `pfoldFactor` product `Pfold` and the telescoping
  set Pfold : Matrix (Fin 2) (Fin 2) ℂ := (tlist.map (pfoldFactor k)).prod with hPfold
  -- circuit normal form `Gmat = Dprod k S`
  have hGmat : Gmat P k (JordanWigner.extendFin γ) (JordanWigner.extendFin β) = Dprod k S := by
    rw [Gmat_eq_Dprod, hgb]
  -- telescoping with `A = χ`
  have htel : Dc χ * Pfold
      = Dc (χ + t₀) * Dprod k S * Dc (-(lastVal t₀ T)) := by
    rw [hPfold, htlistEq, hS]
    exact Dc_mul_pfold_cons k χ t₀ T
  -- the diagonal-dressing identity for `Gmat`
  have hdress : Gmat P k (JordanWigner.extendFin γ) (JordanWigner.extendFin β)
      = Dc (-(χ + t₀)) * (Dc χ * Pfold) * Dc (lastVal t₀ T) := by
    rw [htel, hGmat]
    rw [show Dc (-(χ + t₀)) * (Dc (χ + t₀) * Dprod k S * Dc (-(lastVal t₀ T)))
          * Dc (lastVal t₀ T)
        = (Dc (-(χ + t₀)) * Dc (χ + t₀)) * Dprod k S
            * (Dc (-(lastVal t₀ T)) * Dc (lastVal t₀ T)) by
      simp only [Matrix.mul_assoc]]
    rw [Dc_mul, Dc_mul, neg_add_cancel, neg_add_cancel, Dc_zero, one_mul, mul_one]
  -- evaluate `classMat` at `w = e^{ik}` two ways
  have hwclass : evalMat (Complex.exp (Complex.I * k)) (classMat (2 * P + 1) a b) 1 0
      = b.eval (Complex.exp (Complex.I * k)) := by
    simp [evalMat, classMat]
  have hwprod : evalMat (Complex.exp (Complex.I * k)) (classMat (2 * P + 1) a b)
      = Complex.exp (Complex.I * (k / 2)) ^ (2 * P + 1) • (Dc χ * Pfold) := by
    rw [hmat, evalMat_mul, evalMat_diagPhaseMat, evalMat_prod, Matrix.mul_smul]
    congr 2
    rw [hPfold, htlist, htfun, List.map_ofFn]
    rfl
  -- therefore `(Dc χ · Pfold) 1 0 = 0`
  have hP10 : (Dc χ * Pfold) 1 0 = 0 := by
    have h1 : (Complex.exp (Complex.I * (k / 2)) ^ (2 * P + 1) • (Dc χ * Pfold)) 1 0
        = b.eval (Complex.exp (Complex.I * k)) := by
      rw [← hwprod, hwclass]
    rw [Matrix.smul_apply, smul_eq_mul, hb] at h1
    have hz : Complex.exp (Complex.I * (k / 2)) ^ (2 * P + 1) ≠ 0 := pow_ne_zero _ (z_ne_zero k)
    exact (mul_eq_zero.mp h1).resolve_left hz
  -- extract `(1,0)` of the dressed `Gmat`
  rw [hdress, Dc_mul_mul_Dc_apply_one_zero, hP10, mul_zero, zero_mul]

end

end QAOA.IsingChain.Achievability
