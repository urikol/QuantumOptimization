import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.LinearCombination

/-!
# Pseudospin Pauli Kernel — abstract CAR → `su(2)` algebra `(û·τ⃗)(v̂·τ⃗)`

(arXiv:1911.12259v2 SM l.859–909.) The purely abstract,
ring-level core of the pseudospin Pauli algebra, parametrised by four elements
`a b d e : R` of an arbitrary ring satisfying the within-pair canonical
anticommutation relations (CAR) of the fermion pair `(c_k, c_{-k})`.

From the CAR bundle alone it derives the full pseudospin Pauli product table: the
square atoms equal the pair-block operator `S` (only on the active subspace), and the
cyclic atoms (`τ^aτ^b = i τ^c`) are global ring identities. The operator `S` acts as a
left/right identity on every pseudospin (the projector-swallowing facts), the
load-bearing input to the `Matrix.exp` even/odd collapse downstream.

Mathlib has no pseudospin Pauli identity, so it is built here over an abstract `Ring`;
the instantiation at the concrete fermion pair lives in `PseudospinAlgebra`.

## Main definitions
- `PauliKernel.CAR`: the within-pair canonical anticommutation relation bundle.
- `PauliKernel.tP/tM/nK/nMK/tZ/tX/tY`: the abstract pseudospin operators.
- `PauliKernel.Spair`: the pair-block operator `S = (1−n_k)(1−n_{-k}) + n_k n_{-k}`.

## Main statements
- `PauliKernel.tX_sq`, `tY_sq_neg`, `tZ_sq`: the squares equal `±S`.
- `PauliKernel.tX_mul_tY` … `tY_mul_tZ`: the cyclic Pauli products.
- `PauliKernel.Spair_mul_tX` … `tZ_mul_Spair`: `S` swallows each pseudospin.
-/

namespace QAOA.IsingChain.JordanWigner

-- ============================================================================
-- B3-L3: the pseudospin Pauli product identity (THE ALGEBRAIC HEART)
--
-- Abstract CAR → Pauli kernel: from the within-pair canonical-anticommutation
-- relations for the fermion pair `(a, b) = (c_k, c_{-k})` (with creators
-- `d = c_k†, e = c_{-k}†`), derive the pseudospin Pauli products. The pseudospins
-- are `τ⁺ = b a`, `τ⁻ = d e`, `n_k = d a`, `n_{-k} = e b`, and
-- `τ^x = τ⁺+τ⁻`, `τ^y = −i(τ⁺−τ⁻)`, `τ^z = 1 − n_k − n_{-k}`.
-- The square atoms equal the pair-block projector only on the active subspace;
-- the cyclic atoms (`τ^aτ^b = i τ^c`) are GLOBAL ring identities.
-- ============================================================================

namespace PauliKernel

variable {R : Type*} [Ring R] {a b d e : R}

/-- Within-pair CAR bundle: nilpotency of each fermion, same-mode normalisation,
and the four cross anticommutators of the `(k,−k)` pair. -/
structure CAR (a b d e : R) : Prop where
  aa : a * a = 0
  bb : b * b = 0
  dd : d * d = 0
  ee : e * e = 0
  ad : a * d + d * a = 1
  be : b * e + e * b = 1
  ab : a * b + b * a = 0
  ae : a * e + e * a = 0
  db : d * b + b * d = 0
  de : d * e + e * d = 0

variable (a b d e)

/-- Pseudospin operators in the abstract kernel. -/
def tP : R := b * a
def tM : R := d * e
def nK : R := d * a
def nMK : R := e * b
def tZ : R := 1 - d * a - e * b
def tX : R := b * a + d * e
def tY : R := b * a - d * e   -- the `−i` prefactor is applied at instantiation

variable {a b d e}

/-- Rewrite helpers from the anticommutators (as directed rewrites). -/
theorem eb_eq (h : CAR a b d e) : e * b = 1 - b * e := by
  have := h.be; linear_combination (norm := noncomm_ring) this
theorem be_eq (h : CAR a b d e) : b * e = 1 - e * b := by
  have := h.be; linear_combination (norm := noncomm_ring) this
theorem db_eq (h : CAR a b d e) : d * b = - (b * d) := by
  have := h.db; linear_combination (norm := noncomm_ring) this
theorem de_eq (h : CAR a b d e) : d * e = - (e * d) := by
  have := h.de; linear_combination (norm := noncomm_ring) this
theorem ae_eq (h : CAR a b d e) : a * e = - (e * a) := by
  have := h.ae; linear_combination (norm := noncomm_ring) this
theorem ad_eq (h : CAR a b d e) : a * d = 1 - d * a := by
  have := h.ad; linear_combination (norm := noncomm_ring) this
theorem ab_eq (h : CAR a b d e) : a * b = - (b * a) := by
  have := h.ab; linear_combination (norm := noncomm_ring) this
theorem ba_eq (h : CAR a b d e) : b * a = - (a * b) := by
  have := h.ab; linear_combination (norm := noncomm_ring) this
theorem bd_eq (h : CAR a b d e) : b * d = - (d * b) := by
  have := h.db; linear_combination (norm := noncomm_ring) this

/-- `n_k` and `n_{-k}` commute (within-pair number commute), from the cross
anticommutators (mirrors `number_commute_of_car`). -/
theorem number_commute (h : CAR a b d e) : (d * a) * (e * b) = (e * b) * (d * a) := by
  have had' : a * e = -(e * a) := ae_eq h
  have hda' : d * b = -(b * d) := db_eq h
  have hdd' : d * e = -(e * d) := de_eq h
  have haa' : a * b = -(b * a) := ab_eq h
  calc d * a * (e * b)
      = d * (a * e) * b := by noncomm_ring
    _ = d * (-(e * a)) * b := by rw [had']
    _ = -(d * e * (a * b)) := by noncomm_ring
    _ = -((-(e * d)) * (a * b)) := by rw [hdd']
    _ = e * d * (a * b) := by noncomm_ring
    _ = e * d * (-(b * a)) := by rw [haa']
    _ = -(e * (d * b) * a) := by noncomm_ring
    _ = -(e * (-(b * d)) * a) := by rw [hda']
    _ = e * b * (d * a) := by noncomm_ring

/-- `τ⁻ τ⁺ = n_k n_{-k}` (and `= n_{-k} n_k`). -/
theorem tM_mul_tP (h : CAR a b d e) : (d * e) * (b * a) = (d * a) * (e * b) := by
  have key : d * e * (b * a) = (e * b) * (d * a) := by
    calc d * e * (b * a)
        = d * (e * b) * a := by noncomm_ring
      _ = d * (1 - b * e) * a := by rw [eb_eq h]
      _ = d * a - (d * b) * (e * a) := by noncomm_ring
      _ = d * a - (- (b * d)) * (e * a) := by rw [db_eq h]
      _ = d * a + b * ((d * e) * a) := by noncomm_ring
      _ = d * a + b * ((- (e * d)) * a) := by rw [de_eq h]
      _ = d * a - (b * e) * (d * a) := by noncomm_ring
      _ = d * a - (1 - e * b) * (d * a) := by rw [be_eq h]
      _ = d * a - (d * a) + (e * b) * (d * a) := by noncomm_ring
      _ = (e * b) * (d * a) := by noncomm_ring
  rw [key, ← number_commute h]

/-- `τ⁺ τ⁺ = 0`. -/
theorem tP_mul_tP (h : CAR a b d e) : (b * a) * (b * a) = 0 := by
  calc b * a * (b * a) = b * (a * b) * a := by noncomm_ring
    _ = b * (-(b * a)) * a := by rw [ab_eq h]
    _ = -((b * b) * (a * a)) := by noncomm_ring
    _ = 0 := by rw [h.aa, h.bb]; noncomm_ring

/-- `τ⁻ τ⁻ = 0`. -/
theorem tM_mul_tM (h : CAR a b d e) : (d * e) * (d * e) = 0 := by
  have hed : e * d = -(d * e) := by have := h.de; linear_combination (norm := noncomm_ring) this
  calc d * e * (d * e) = d * (e * d) * e := by noncomm_ring
    _ = d * (-(d * e)) * e := by rw [hed]
    _ = -((d * d) * (e * e)) := by noncomm_ring
    _ = 0 := by rw [h.dd, h.ee]; noncomm_ring

/-- `n_k` is idempotent. -/
theorem nK_idem (h : CAR a b d e) : (d * a) * (d * a) = d * a := by
  calc (d * a) * (d * a) = d * (a * d) * a := by noncomm_ring
    _ = d * (1 - d * a) * a := by rw [ad_eq h]
    _ = d * a - (d * d) * (a * a) := by noncomm_ring
    _ = d * a := by rw [h.dd, h.aa]; noncomm_ring

/-- `n_{-k}` is idempotent. -/
theorem nMK_idem (h : CAR a b d e) : (e * b) * (e * b) = e * b := by
  calc (e * b) * (e * b) = e * (b * e) * b := by noncomm_ring
    _ = e * (1 - e * b) * b := by rw [be_eq h]
    _ = e * b - (e * e) * (b * b) := by noncomm_ring
    _ = e * b := by rw [h.ee, h.bb]; noncomm_ring

/-- `τ⁺ τ⁻ = (1 − n_k)(1 − n_{-k})`. -/
theorem tP_mul_tM (h : CAR a b d e) :
    (b * a) * (d * e) = (1 - d * a) * (1 - e * b) := by
  have key : b * a * (d * e) = (1 - e * b) * (1 - d * a) := by
    calc b * a * (d * e)
        = b * (a * d) * e := by noncomm_ring
      _ = b * (1 - d * a) * e := by rw [ad_eq h]
      _ = (b * e) - (b * d) * (a * e) := by noncomm_ring
      _ = (b * e) - (-(d * b)) * (a * e) := by rw [bd_eq h]
      _ = (b * e) + d * ((b * a) * e) := by noncomm_ring
      _ = (b * e) + d * ((-(a * b)) * e) := by rw [ba_eq h]
      _ = (b * e) - (d * a) * (b * e) := by noncomm_ring
      _ = (1 - e * b) - (d * a) * (1 - e * b) := by rw [be_eq h]
      _ = 1 - e * b - d * a + (d * a) * (e * b) := by noncomm_ring
      _ = 1 - e * b - d * a + (e * b) * (d * a) := by rw [number_commute h]
      _ = (1 - e * b) * (1 - d * a) := by noncomm_ring
  rw [key]
  -- (1 − e b)(1 − d a) = (1 − d a)(1 − e b) since n_k, n_{-k} commute
  have hc := number_commute h
  linear_combination (norm := noncomm_ring) (-1 : R) * hc

variable (a b d e)

/-- The common pair-block operator `S = (1−n_k)(1−n_{-k}) + n_k n_{-k}`, equal to all
three pseudospin squares `(τ^x)² = (τ^y)² = (τ^z)²`. On the active `(k,−k)` block
(where `n_k = n_{-k}`) this equals the pair-block identity `Π_pair`. -/
def Spair : R := (1 - d * a) * (1 - e * b) + (d * a) * (e * b)

variable {a b d e}

/-- `(τ^x)² = S`. -/
theorem tX_sq (h : CAR a b d e) : tX a b d e * tX a b d e = Spair a b d e := by
  unfold tX Spair
  have h1 := tP_mul_tP h
  have h2 := tM_mul_tM h
  have h3 := tP_mul_tM h
  have h4 := tM_mul_tP h
  rw [add_mul, mul_add, mul_add, h1, h3, h4, h2]
  noncomm_ring

/-- `(τ^z)² = S`. -/
theorem tZ_sq (h : CAR a b d e) : tZ a b d e * tZ a b d e = Spair a b d e := by
  unfold tZ Spair
  have hidem1 := nK_idem h
  have hidem2 := nMK_idem h
  have hc := number_commute h
  have hexp : (1 - d * a - e * b) * (1 - d * a - e * b)
      = 1 - 2 • (d * a) - 2 • (e * b) + (d * a) * (d * a) + (e * b) * (e * b)
        + (d * a) * (e * b) + (e * b) * (d * a) := by noncomm_ring
  rw [hexp, hidem1, hidem2, ← hc]
  noncomm_ring

/-- The two-term form `S = 1 − n_k − n_{-k} + 2 n_k n_{-k}`. -/
theorem Spair_eq :
    Spair a b d e = 1 - d * a - e * b + 2 • ((d * a) * (e * b)) := by
  unfold Spair
  rw [two_smul]
  noncomm_ring

/-- `n_k · τ⁺ = 0`. -/
theorem nK_mul_tP (h : CAR a b d e) : (d * a) * (b * a) = 0 := by
  calc (d * a) * (b * a) = d * (a * b) * a := by noncomm_ring
    _ = d * (-(b * a)) * a := by rw [ab_eq h]
    _ = -(d * b) * (a * a) := by noncomm_ring
    _ = 0 := by rw [h.aa]; noncomm_ring

/-- `n_k · τ⁻ = τ⁻`. -/
theorem nK_mul_tM (h : CAR a b d e) : (d * a) * (d * e) = d * e := by
  calc (d * a) * (d * e) = d * (a * d) * e := by noncomm_ring
    _ = d * (1 - d * a) * e := by rw [ad_eq h]
    _ = d * e - (d * d) * (a * e) := by noncomm_ring
    _ = d * e := by rw [h.dd]; noncomm_ring

/-- `n_{-k} · τ⁺ = 0`. -/
theorem nMK_mul_tP (h : CAR a b d e) : (e * b) * (b * a) = 0 := by
  calc (e * b) * (b * a) = e * (b * b) * a := by noncomm_ring
    _ = 0 := by rw [h.bb]; noncomm_ring

/-- `n_{-k} · τ⁻ = τ⁻`. -/
theorem nMK_mul_tM (h : CAR a b d e) : (e * b) * (d * e) = d * e := by
  calc (e * b) * (d * e) = e * (b * d) * e := by noncomm_ring
    _ = e * (-(d * b)) * e := by rw [bd_eq h]
    _ = -(e * d) * (b * e) := by noncomm_ring
    _ = -(e * d) * (1 - e * b) := by rw [be_eq h]
    _ = -(e * d) + (e * d) * (e * b) := by noncomm_ring
    _ = -(e * d) + e * (d * e) * b := by noncomm_ring
    _ = -(e * d) + e * (-(e * d)) * b := by rw [de_eq h]
    _ = -(e * d) - (e * e) * (d * b) := by noncomm_ring
    _ = -(e * d) := by rw [h.ee]; noncomm_ring
    _ = d * e := by rw [de_eq h]

/-- `τ⁺ · n_k = τ⁺`. -/
theorem tP_mul_nK (h : CAR a b d e) : (b * a) * (d * a) = b * a := by
  calc (b * a) * (d * a) = b * (a * d) * a := by noncomm_ring
    _ = b * (1 - d * a) * a := by rw [ad_eq h]
    _ = b * a - (b * d) * (a * a) := by noncomm_ring
    _ = b * a := by rw [h.aa]; noncomm_ring

/-- `τ⁺ · n_{-k} = τ⁺`. -/
theorem tP_mul_nMK (h : CAR a b d e) : (b * a) * (e * b) = b * a := by
  calc (b * a) * (e * b) = b * (a * e) * b := by noncomm_ring
    _ = b * (-(e * a)) * b := by rw [ae_eq h]
    _ = -(b * e) * (a * b) := by noncomm_ring
    _ = -(b * e) * (-(b * a)) := by rw [ab_eq h]
    _ = (b * e) * (b * a) := by noncomm_ring
    _ = (1 - e * b) * (b * a) := by rw [be_eq h]
    _ = b * a - e * (b * b) * a := by noncomm_ring
    _ = b * a := by rw [h.bb]; noncomm_ring

/-- `τ⁻ · n_k = 0`. -/
theorem tM_mul_nK (h : CAR a b d e) : (d * e) * (d * a) = 0 := by
  calc (d * e) * (d * a) = d * (e * d) * a := by noncomm_ring
    _ = d * (-(d * e)) * a := by
          rw [show e * d = -(d * e) by have := h.de; linear_combination (norm := noncomm_ring) this]
    _ = -(d * d) * (e * a) := by noncomm_ring
    _ = 0 := by rw [h.dd]; noncomm_ring

/-- `τ⁻ · n_{-k} = 0`. -/
theorem tM_mul_nMK (h : CAR a b d e) : (d * e) * (e * b) = 0 := by
  calc (d * e) * (e * b) = d * (e * e) * b := by noncomm_ring
    _ = 0 := by rw [h.ee]; noncomm_ring

/-- `(τ^y)² = S` (with the `−i` prefactor squared to `−1`, applied at instantiation,
the kernel `tY = τ⁺−τ⁻` squares to `−S`; documented in `tY_sq_neg`). -/
theorem tY_sq_neg (h : CAR a b d e) : tY a b d e * tY a b d e = - Spair a b d e := by
  unfold tY Spair
  have h1 := tP_mul_tP h
  have h2 := tM_mul_tM h
  have h3 := tP_mul_tM h
  have h4 := tM_mul_tP h
  rw [sub_mul, mul_sub, mul_sub, h1, h3, h4, h2]
  noncomm_ring

/-- Cyclic product `τ^x · τ^y = −τ^z` (kernel form; with the `−i` prefactor on the
actual `τ^y` this becomes `τ^xτ^y = iτ^z`). -/
theorem tX_mul_tY (h : CAR a b d e) : tX a b d e * tY a b d e = - tZ a b d e := by
  unfold tX tY tZ
  have h1 := tP_mul_tP h
  have h2 := tM_mul_tM h
  have h3 := tP_mul_tM h
  have h4 := tM_mul_tP h
  rw [add_mul, mul_sub, mul_sub, h1, h3, h4, h2]
  noncomm_ring

/-- Cyclic product `τ^y · τ^x = τ^z` (kernel form), giving `τ^yτ^x = −iτ^z`. -/
theorem tY_mul_tX (h : CAR a b d e) : tY a b d e * tX a b d e = tZ a b d e := by
  unfold tX tY tZ
  have h1 := tP_mul_tP h
  have h2 := tM_mul_tM h
  have h3 := tP_mul_tM h
  have h4 := tM_mul_tP h
  rw [sub_mul, mul_add, mul_add, h1, h3, h4, h2]
  noncomm_ring

/-- Cyclic product `τ^z · τ^x = τ^y` (kernel form), giving `τ^zτ^x = iτ^y`. -/
theorem tZ_mul_tX (h : CAR a b d e) : tZ a b d e * tX a b d e = tY a b d e := by
  unfold tX tY tZ
  rw [show (1 - d * a - e * b) = 1 - (d * a) - (e * b) from rfl]
  rw [sub_mul, sub_mul, one_mul, mul_add, mul_add, nK_mul_tP h, nK_mul_tM h,
    nMK_mul_tP h, nMK_mul_tM h]
  noncomm_ring

/-- Cyclic product `τ^x · τ^z = −τ^y` (kernel form), giving `τ^xτ^z = −iτ^y`. -/
theorem tX_mul_tZ (h : CAR a b d e) : tX a b d e * tZ a b d e = - tY a b d e := by
  unfold tX tY tZ
  rw [mul_sub, mul_sub, mul_one, add_mul, add_mul, tP_mul_nK h, tP_mul_nMK h,
    tM_mul_nK h, tM_mul_nMK h]
  noncomm_ring

/-- Cyclic product `τ^z · τ^y = τ^x` (kernel form), giving `τ^zτ^y = ... `. -/
theorem tZ_mul_tY (h : CAR a b d e) : tZ a b d e * tY a b d e = tX a b d e := by
  unfold tX tY tZ
  rw [sub_mul, sub_mul, one_mul, mul_sub, mul_sub, nK_mul_tP h, nK_mul_tM h,
    nMK_mul_tP h, nMK_mul_tM h]
  noncomm_ring

/-- Cyclic product `τ^y · τ^z = −τ^x` (kernel form). -/
theorem tY_mul_tZ (h : CAR a b d e) : tY a b d e * tZ a b d e = - tX a b d e := by
  unfold tX tY tZ
  rw [mul_sub, mul_sub, mul_one, sub_mul, sub_mul, tP_mul_nK h, tP_mul_nMK h,
    tM_mul_nK h, tM_mul_nMK h]
  noncomm_ring

-- ---------------------------------------------------------------------------
-- `S` acts as a left identity on each pseudospin `τ^a` (the projector swallows
-- the off-block component): `S·τ^x = τ^x`, `S·τ^y = τ^y`, `S·τ^z = τ^z`. These
-- give `S·A = A` for `A = û·τ⃗` (a linear combination of the three), hence (with
-- `A² = S`) the cubic `A³ = A` — the load-bearing fact for the `Matrix.exp`
-- even/odd collapse to the Euler closed form. NB `S·n_k = n_k n_{-k} ≠ n_k`
-- (the number ops are NOT swallowed), so `tZ` must be handled directly.
-- ---------------------------------------------------------------------------

/-- `S · τ⁺ = τ⁺`. -/
theorem Spair_mul_tP (h : CAR a b d e) : Spair a b d e * (b * a) = b * a := by
  rw [Spair_eq, two_smul]
  have h1 := nK_mul_tP h
  have h2 := nMK_mul_tP h
  calc (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b))) * (b * a)
      = b * a - (d * a) * (b * a) - (e * b) * (b * a)
        + ((d * a) * ((e * b) * (b * a)) + (d * a) * ((e * b) * (b * a))) := by noncomm_ring
    _ = b * a := by rw [h1, h2, mul_zero]; noncomm_ring

/-- `S · τ⁻ = τ⁻`. -/
theorem Spair_mul_tM (h : CAR a b d e) : Spair a b d e * (d * e) = d * e := by
  rw [Spair_eq, two_smul]
  have h3 := nK_mul_tM h
  have h4 := nMK_mul_tM h
  have h5 : (d * a) * ((e * b) * (d * e)) = d * e := by rw [h4, h3]
  calc (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b))) * (d * e)
      = d * e - (d * a) * (d * e) - (e * b) * (d * e)
        + ((d * a) * ((e * b) * (d * e)) + (d * a) * ((e * b) * (d * e))) := by noncomm_ring
    _ = d * e := by rw [h5, h3, h4]; noncomm_ring

/-- `S · n_k = n_k n_{-k}` (the projector swallows the off-block part of `n_k`). -/
theorem Spair_mul_nK (h : CAR a b d e) : Spair a b d e * (d * a) = (d * a) * (e * b) := by
  rw [Spair_eq, two_smul]
  have i1 := nK_idem h
  have hc := number_commute h
  have h6 : (e * b) * (d * a) = (d * a) * (e * b) := hc.symm
  have h7 : (d * a) * ((e * b) * (d * a)) = (d * a) * (e * b) := by
    rw [h6, ← mul_assoc, i1]
  calc (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b))) * (d * a)
      = d * a - (d * a) * (d * a) - (e * b) * (d * a)
        + ((d * a) * ((e * b) * (d * a)) + (d * a) * ((e * b) * (d * a))) := by noncomm_ring
    _ = (d * a) * (e * b) := by rw [h7, i1, h6]; noncomm_ring

/-- `S · n_{-k} = n_k n_{-k}`. -/
theorem Spair_mul_nMK (h : CAR a b d e) : Spair a b d e * (e * b) = (d * a) * (e * b) := by
  rw [Spair_eq, two_smul]
  have i2 := nMK_idem h
  have h8 : (d * a) * ((e * b) * (e * b)) = (d * a) * (e * b) := by rw [i2]
  calc (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b))) * (e * b)
      = e * b - (d * a) * (e * b) - (e * b) * (e * b)
        + ((d * a) * ((e * b) * (e * b)) + (d * a) * ((e * b) * (e * b))) := by noncomm_ring
    _ = (d * a) * (e * b) := by rw [h8, i2]; noncomm_ring

/-- `S · τ^x = τ^x`. -/
theorem Spair_mul_tX (h : CAR a b d e) : Spair a b d e * tX a b d e = tX a b d e := by
  unfold tX; rw [mul_add, Spair_mul_tP h, Spair_mul_tM h]

/-- `S · τ^y = τ^y` (kernel form). -/
theorem Spair_mul_tY (h : CAR a b d e) : Spair a b d e * tY a b d e = tY a b d e := by
  unfold tY; rw [mul_sub, Spair_mul_tP h, Spair_mul_tM h]

/-- `S · τ^z = τ^z`: from `S·n_k = S·n_{-k} = n_k n_{-k}` and `S = 1 − n_k − n_{-k}
+ 2 n_k n_{-k}` the two `n_k n_{-k}` cancel. -/
theorem Spair_mul_tZ (h : CAR a b d e) : Spair a b d e * tZ a b d e = tZ a b d e := by
  have hN := Spair_mul_nK h
  have hM := Spair_mul_nMK h
  have hSeq := Spair_eq (a := a) (b := b) (d := d) (e := e)
  unfold tZ
  rw [mul_sub, mul_sub, mul_one, hN, hM, hSeq, two_smul]
  noncomm_ring

-- Right-projector companions: `τ^a · S = τ^a` (mirror of the left swallows).

/-- `τ⁺ · S = τ⁺`. -/
theorem tP_mul_Spair (h : CAR a b d e) : (b * a) * Spair a b d e = b * a := by
  rw [Spair_eq, two_smul]
  have h1 := tP_mul_nK h
  have h2 := tP_mul_nMK h
  have h3 : (b * a) * ((d * a) * (e * b)) = b * a := by rw [← mul_assoc, h1, h2]
  calc (b * a) * (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b)))
      = b * a - (b * a) * (d * a) - (b * a) * (e * b)
        + ((b * a) * ((d * a) * (e * b)) + (b * a) * ((d * a) * (e * b))) := by noncomm_ring
    _ = b * a := by rw [h1, h2, h3]; noncomm_ring

/-- `τ⁻ · S = τ⁻`. -/
theorem tM_mul_Spair (h : CAR a b d e) : (d * e) * Spair a b d e = d * e := by
  rw [Spair_eq, two_smul]
  have h1 := tM_mul_nK h
  have h2 := tM_mul_nMK h
  have h3 : (d * e) * ((d * a) * (e * b)) = 0 := by rw [← mul_assoc, h1, zero_mul]
  calc (d * e) * (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b)))
      = d * e - (d * e) * (d * a) - (d * e) * (e * b)
        + ((d * e) * ((d * a) * (e * b)) + (d * e) * ((d * a) * (e * b))) := by noncomm_ring
    _ = d * e := by rw [h1, h2, h3]; noncomm_ring

/-- `n_k · S = n_k n_{-k}`. -/
theorem nK_mul_Spair (h : CAR a b d e) : (d * a) * Spair a b d e = (d * a) * (e * b) := by
  rw [Spair_eq, two_smul]
  have i1 := nK_idem h
  have h7 : (d * a) * ((d * a) * (e * b)) = (d * a) * (e * b) := by rw [← mul_assoc, i1]
  calc (d * a) * (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b)))
      = d * a - (d * a) * (d * a) - (d * a) * (e * b)
        + ((d * a) * ((d * a) * (e * b)) + (d * a) * ((d * a) * (e * b))) := by noncomm_ring
    _ = (d * a) * (e * b) := by rw [i1, h7]; noncomm_ring

/-- `n_{-k} · S = n_k n_{-k}`. -/
theorem nMK_mul_Spair (h : CAR a b d e) : (e * b) * Spair a b d e = (d * a) * (e * b) := by
  rw [Spair_eq, two_smul]
  have i2 := nMK_idem h
  have hc := number_commute h
  have h8 : (e * b) * (d * a) = (d * a) * (e * b) := hc.symm
  have h9 : (e * b) * ((d * a) * (e * b)) = (d * a) * (e * b) := by
    rw [← mul_assoc, h8, mul_assoc, i2]
  calc (e * b) * (1 - d * a - e * b + ((d * a) * (e * b) + (d * a) * (e * b)))
      = e * b - (e * b) * (d * a) - (e * b) * (e * b)
        + ((e * b) * ((d * a) * (e * b)) + (e * b) * ((d * a) * (e * b))) := by noncomm_ring
    _ = (d * a) * (e * b) := by rw [i2, h8, h9]; noncomm_ring

/-- `τ^x · S = τ^x`. -/
theorem tX_mul_Spair (h : CAR a b d e) : tX a b d e * Spair a b d e = tX a b d e := by
  unfold tX; rw [add_mul, tP_mul_Spair h, tM_mul_Spair h]

/-- `τ^y · S = τ^y` (kernel form). -/
theorem tY_mul_Spair (h : CAR a b d e) : tY a b d e * Spair a b d e = tY a b d e := by
  unfold tY; rw [sub_mul, tP_mul_Spair h, tM_mul_Spair h]

/-- `τ^z · S = τ^z`. -/
theorem tZ_mul_Spair (h : CAR a b d e) : tZ a b d e * Spair a b d e = tZ a b d e := by
  have hN := nK_mul_Spair h
  have hM := nMK_mul_Spair h
  have hSeq := Spair_eq (a := a) (b := b) (d := d) (e := e)
  unfold tZ
  rw [sub_mul, sub_mul, one_mul, hN, hM, hSeq, two_smul]
  noncomm_ring

end PauliKernel

end QAOA.IsingChain.JordanWigner
