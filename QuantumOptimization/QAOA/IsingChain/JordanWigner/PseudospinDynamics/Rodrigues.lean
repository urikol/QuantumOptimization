import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# SO(3) Rodrigues Calculus — axis–angle rotation `R n̂ θ`, magnetization product `τ⃗_k`

(arXiv:1911.12259v2 SM l.859–909.) The self-contained
3D real-vector layer underneath the pseudospin dynamics: the Rodrigues axis–angle
rotation matrix `R n̂ θ`, its action on vectors, its isometry property, and the
time-ordered rotation product `τ⃗_k = (∏_m R_ẑ(4β_m) R_{b̂_k}(4γ_m)) ẑ` (the classical
magnetization carrier). Vectors live in `Fin 3 → ℝ`; the genuine Euclidean norm is
recovered via `EuclideanSpace.equiv`.

Mathlib has no 3D axis–angle rotation matrix, so it is built here on top of Mathlib's
`crossProduct`, `dotProduct`, and `EuclideanSpace` norm.

## FROZEN conventions (mirror the numerically-validated F7 sign convention; do NOT reverse)
- Rodrigues: `R_n̂(θ) = cos θ·I + (1−cos θ)·n̂ n̂ᵀ + sin θ·[n̂]_×`,
  axes `bHat k = (−sin k, 0, cos k)`, `zHat = (0,0,1)`.
- `tauVec k γ β = (∏_{m=1}^{P} R_ẑ(+4β_m) R_{b̂_k}(4γ_m)) ẑ`, later layers left-multiply,
  seed `ẑ`.

## Main definitions
- `crossMatrix` (the `[n̂]_×` hat matrix), `R` (Rodrigues), `bHat`, `zHat`,
  `layerBlock`, `layerProd`, `tauVec`.

## Main statements
- `R_mulVec`, `R_apply_axis`, `R_dotProduct` (isometry), `bHat_unit`, `zHat_dotProduct`,
  `tauVec_unit`, `tauVec_zero`, `tauVec_eq` (the time-ordered rotation product form).
-/

namespace QAOA.IsingChain.JordanWigner

open Matrix
open scoped BigOperators

noncomputable section

-- ============================================================================
-- B3-L1: Rodrigues rotation matrix and basics (vectors as `Fin 3 → ℝ`)
-- ============================================================================

/-- The cross-product (hat) matrix `[n̂]_×`, hard-coded so that
`crossMatrix n *ᵥ v = n ×ᵥ v` (`cross_apply`). -/
def crossMatrix (n : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, -n 2, n 1; n 2, 0, -n 0; -n 1, n 0, 0]

/-- `crossMatrix n` applied to `v` is the cross product `n ×ᵥ v`. -/
theorem crossMatrix_mulVec (n v : Fin 3 → ℝ) : crossMatrix n *ᵥ v = n ⨯₃ v := by
  rw [cross_apply]
  funext i
  fin_cases i <;>
    simp [crossMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

/-- The Rodrigues rotation matrix about (unit) axis `n` by angle `θ`:
`R n θ = cos θ·I + (1−cos θ)·n nᵀ + sin θ·[n]_×`. -/
def R (n : Fin 3 → ℝ) (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (Real.cos θ) • (1 : Matrix (Fin 3) (Fin 3) ℝ) +
    (1 - Real.cos θ) • (Matrix.vecMulVec n n) +
    (Real.sin θ) • crossMatrix n

/-- The unit axis `b̂_k = (−sin k, 0, cos k)`. -/
def bHat (k : ℝ) : Fin 3 → ℝ := ![-Real.sin k, 0, Real.cos k]

/-- The seed axis `ẑ = (0, 0, 1)`. -/
def zHat : Fin 3 → ℝ := ![0, 0, 1]

-- ---------------------------------------------------------------------------
-- Cross-product / dot-product helper lemmas (the load-bearing BAC−CAB identity)
-- ---------------------------------------------------------------------------

/-- BAC−CAB triple cross-product identity:
`n ×ᵥ (n ×ᵥ m) = (n ⬝ᵥ m)·n − (n ⬝ᵥ n)·m`. -/
theorem cross_cross (n m : Fin 3 → ℝ) :
    n ⨯₃ (n ⨯₃ m) = (n ⬝ᵥ m) • n - (n ⬝ᵥ n) • m := by
  funext i
  fin_cases i <;>
    simp [cross_apply, dotProduct, Fin.sum_univ_three, Pi.smul_apply,
      Pi.sub_apply] <;> ring

/-- The matrix `vecMulVec n n` applied to `v` is `(n ⬝ᵥ v) • n`. -/
theorem vecMulVec_mulVec (n v : Fin 3 → ℝ) :
    (Matrix.vecMulVec n n) *ᵥ v = (n ⬝ᵥ v) • n := by
  funext i
  simp only [Matrix.vecMulVec, Matrix.mulVec, dotProduct, Matrix.of_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `R n θ` applied to `v` in expanded form. -/
theorem R_mulVec (n v : Fin 3 → ℝ) (θ : ℝ) :
    R n θ *ᵥ v =
      (Real.cos θ) • v + (1 - Real.cos θ) • ((n ⬝ᵥ v) • n) + (Real.sin θ) • (n ⨯₃ v) := by
  unfold R
  rw [Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    vecMulVec_mulVec, crossMatrix_mulVec]

/-- A unit axis is fixed by its own rotation: `R n θ *ᵥ n = n` when `n ⬝ᵥ n = 1`. -/
theorem R_apply_axis (n : Fin 3 → ℝ) (θ : ℝ) (hn : n ⬝ᵥ n = 1) :
    R n θ *ᵥ n = n := by
  rw [R_mulVec, hn, one_smul, cross_self, smul_zero, add_zero]
  rw [show (1 - Real.cos θ) • n = n - Real.cos θ • n by module]
  abel

/-- `R n θ` preserves the dot product (orthogonality) for a unit axis: it is a
genuine isometry of the inner product. -/
theorem R_dotProduct (n v w : Fin 3 → ℝ) (θ : ℝ) (hn : n ⬝ᵥ n = 1) :
    (R n θ *ᵥ v) ⬝ᵥ (R n θ *ᵥ w) = v ⬝ᵥ w := by
  rw [R_mulVec, R_mulVec]
  -- expand the bilinear dot product over the three summands each
  simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct,
    smul_eq_mul]
  -- all the scalar dot-product facts, in whatever orientation appears
  have e1 : (crossProduct n) v ⬝ᵥ n = 0 := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e2 : v ⬝ᵥ (crossProduct n) w = -((crossProduct n) v ⬝ᵥ w) := by
    simp only [cross_apply, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    ring
  have e3 : n ⬝ᵥ (crossProduct n) w = 0 := dot_self_cross n w
  have e4 : (crossProduct n) v ⬝ᵥ (crossProduct n) w = (v ⬝ᵥ w) - (n ⬝ᵥ w) * (n ⬝ᵥ v) := by
    rw [cross_dot_cross n v n w, hn, one_mul, dotProduct_comm v n]
  have evn : v ⬝ᵥ n = n ⬝ᵥ v := dotProduct_comm v n
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
  rw [e1, e2, e3, e4, hn, evn]
  linear_combination (v ⬝ᵥ w - n ⬝ᵥ v * (n ⬝ᵥ w)) * hcs

/-- `b̂_k ⬝ᵥ b̂_k = 1`. -/
theorem bHat_dotProduct (k : ℝ) : bHat k ⬝ᵥ bHat k = 1 := by
  simp only [bHat, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  have := Real.sin_sq_add_cos_sq k
  nlinarith [this]

/-- `ẑ ⬝ᵥ ẑ = 1`. -/
theorem zHat_dotProduct : zHat ⬝ᵥ zHat = 1 := by
  simp [zHat, dotProduct, Fin.sum_univ_three]

/-- Bridge from the `dotProduct` self-inner-product to the genuine Euclidean norm:
for `v : Fin 3 → ℝ` with `v ⬝ᵥ v = 1`, the wrapped vector in `EuclideanSpace ℝ (Fin 3)`
has norm `1`. (`EuclideanSpace ℝ (Fin 3)` is the type `Fin 3 → ℝ` carries the genuine
`ℓ²` norm; the working algebra above stays in `Fin 3 → ℝ`.) -/
theorem euclidean_norm_eq_one_of_dotProduct (v : Fin 3 → ℝ) (h : v ⬝ᵥ v = 1) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm v‖ = 1 := by
  rw [EuclideanSpace.norm_eq]
  have hsum : (∑ i, ‖((EuclideanSpace.equiv (Fin 3) ℝ).symm v).ofLp i‖ ^ 2) = 1 := by
    have : ∀ i, ((EuclideanSpace.equiv (Fin 3) ℝ).symm v).ofLp i = v i := fun i => rfl
    simp only [this, Real.norm_eq_abs, sq_abs]
    rw [← h]
    simp [dotProduct, pow_two]
  rw [hsum, Real.sqrt_one]

-- ============================================================================
-- B3-L2: per-layer rotation block and the time-ordered magnetization `tauVec`
-- ============================================================================

/-- The per-layer SO(3) block for mode `k` at layer `m`:
`R_ẑ(4β_m) R_{b̂_k}(4γ_m)` (cost rotation first, then mixer rotation; F7 sign s=+1). -/
def layerBlock (k : ℝ) (γ β : ℕ → ℝ) (m : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  R zHat (4 * β m) * R (bHat k) (4 * γ m)

/-- The time-ordered rotation product over `P` layers, with later layers
left-multiplying (m increasing right-to-left): `∏_{m=P−1..0} layerBlock m`. -/
def layerProd (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  match P with
  | 0 => 1
  | Nat.succ p => layerBlock k γ β p * layerProd p k γ β

/-- The per-mode magnetization vector `τ⃗_k(γ,β) = (∏_{m} R_ẑ(4β_m) R_{b̂_k}(4γ_m)) ẑ`,
the time-ordered rotation product applied to the seed `ẑ` (later layers left-multiply,
m increasing right-to-left; F7 sign convention s = +1 on both axes).
DIRECT form: no `(−β)` is baked in here — B4's `epsilonMode` carries the physical
`(−β)` by feeding `(γ, −β)` into this `τ⃗`. -/
def tauVec (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) : Fin 3 → ℝ :=
  layerProd P k γ β *ᵥ zHat

/-- D1 base case: at `P = 0`, the empty rotation product fixes the seed, `τ⃗_k(0) = ẑ`. -/
theorem tauVec_zero (k : ℝ) (γ β : ℕ → ℝ) : tauVec 0 k γ β = zHat := by
  unfold tauVec layerProd
  rw [Matrix.one_mulVec]

/-- The cost-rotation axis `b̂_k` is a unit vector (`dotProduct` form). -/
theorem bHat_dot_self (k : ℝ) : bHat k ⬝ᵥ bHat k = 1 := bHat_dotProduct k

/-- A single Rodrigues rotation about a unit axis preserves the dot-product norm. -/
theorem R_preserves_dot_self (n v : Fin 3 → ℝ) (θ : ℝ) (hn : n ⬝ᵥ n = 1) :
    (R n θ *ᵥ v) ⬝ᵥ (R n θ *ᵥ v) = v ⬝ᵥ v := R_dotProduct n v v θ hn

/-- The full layer product applied to `ẑ` is a unit vector (`dotProduct` form):
each Rodrigues factor is an isometry and the seed `ẑ` is a unit vector. -/
theorem tauVec_dot_self (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    tauVec P k γ β ⬝ᵥ tauVec P k γ β = 1 := by
  unfold tauVec
  induction P with
  | zero => rw [layerProd, Matrix.one_mulVec]; exact zHat_dotProduct
  | succ p ih =>
      rw [layerProd, layerBlock]
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      rw [R_preserves_dot_self zHat _ _ zHat_dotProduct]
      rw [R_preserves_dot_self (bHat k) _ _ (bHat_dot_self k)]
      exact ih

/-- D3 export: `‖τ⃗_k(γ,β)‖ = 1` (genuine Euclidean norm). -/
theorem tauVec_unit (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (tauVec P k γ β)‖ = 1 :=
  euclidean_norm_eq_one_of_dotProduct _ (tauVec_dot_self P k γ β)

/-- Export: `‖b̂_k‖ = 1` (genuine Euclidean norm). -/
theorem bHat_unit (k : ℝ) :
    ‖(EuclideanSpace.equiv (Fin 3) ℝ).symm (bHat k)‖ = 1 :=
  euclidean_norm_eq_one_of_dotProduct _ (bHat_dot_self k)

/-- `layerProd` as an explicit time-ordered `List.prod`: the layer blocks for
`m = P−1, …, 0` (later layers leftmost), so the head of the list is the last layer. -/
theorem layerProd_eq_listProd (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    layerProd P k γ β =
      ((List.range P).reverse.map (fun m => layerBlock k γ β m)).prod := by
  induction P with
  | zero => simp [layerProd]
  | succ p ih =>
      rw [layerProd, ih, List.range_succ, List.reverse_append]
      simp

/-- D3 (`tauVec_eq`): the magnetization is the time-ordered rotation product applied
to the seed `ẑ`. The product lists the per-layer blocks `R_ẑ(4β_m) R_{b̂_k}(4γ_m)`
with later layers leftmost (m increasing right-to-left), matching
`eqn:pseudospin_full_rotation` (source l.890–897). -/
theorem tauVec_eq (P : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    tauVec P k γ β =
      ((List.range P).reverse.map
        (fun m => R zHat (4 * β m) * R (bHat k) (4 * γ m))).prod *ᵥ zHat := by
  unfold tauVec
  rw [layerProd_eq_listProd]
  rfl

end

end QAOA.IsingChain.JordanWigner
