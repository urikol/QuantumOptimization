import QuantumOptimization.QAOA.IsingChain.JordanWigner.Decomposition.ExpReduction

/-!
# Heisenberg Mode Expectation — `mode_sum_expectation`

The cost expectation on the reduced QAOA state equals
`−2 Σ_k b̂_k ⬝ᵥ τ⃗_k(γ,−β)`. The Heisenberg depth induction transports the `dotTau`
expectation axis by the COST-OUTERMOST per-layer block `R_{b̂}(4γ)·R_ẑ(4·(−β))`, then a
y-flip c-number bridge identifies the accumulated axis with the `tauVec` rotation product.

* **per-layer transport** — `layer_conj_dotTau_transport`/`applyLayer_dotTau_expectation`:
  conjugating `dotTau_n a` by one reduced QAOA layer rotates the axis by
  `R_{b̂}(4g)·R_ẑ(4b)` on active states (`costUnitary_dag`/`mixerUnitary_dag` supply the
  `+i` direction).
* **depth induction** — `qaoa_dotTau_expectation`: the depth-`p` expectation transports the
  axis by the cost-outer accumulation `accCO`.
* **y-flip bridge** — `flipY`/`flipY_bHat`/`accCO_dotProduct_eq`: the full magnetization is
  `m⃗ = (τx,−τy,τz)`; the cost-axis projection is flip-invariant (`b̂_y = 0`), giving the
  single-mode `mode_expectation` and the mode-sum `mode_sum_expectation`.

The `attribute [local instance]` matrix-`linftyOp` norm instances (needed for `NormedSpace.exp`
on `NQubitOp`) are declared in-file, scoped to this module's exp machinery.

## Main statements
- `applyLayer_dotTau_expectation` / `qaoa_dotTau_expectation`: per-layer / depth-`p`
  Heisenberg axis transport
- `accCO_dotProduct_eq`: the y-flip c-number bridge `accCO·s = (F·a) ⬝ᵥ (layerProd *ᵥ F·s)`
- `mode_sum_expectation`: `⟨ψ̃|Σ HredZMode|ψ̃⟩ = −2 Σ_n b̂_{k_n} ⬝ᵥ τ⃗_{k_n}(γ,−β)`
-/

namespace QAOA.IsingChain.JordanWigner

open Quantum.Operators
open Quantum.Gates
open Qubits
open Matrix
open scoped BigOperators

noncomputable section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace
  Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

-- ----------------------------------------------------------------------------
-- Final assembly: the Heisenberg depth induction.
--
-- ARCHITECTURE (numerically pinned, P=1,2,3):
--   * By linearity `⟨ψ|û·τ⃗|ψ⟩ = û ⬝ᵥ m⃗` with `m⃗` the magnetization. Numerical validation
--     CONFIRMS the general-axis identity `⟨ψ̃|û·τ⃗|ψ̃⟩ = û ⬝ᵥ tauVec` is FALSE
--     (y-flip: `m⃗ = (τ_x,−τ_y,τ_z)`), so we must NOT carry that. Instead we carry the
--     TRUE per-layer OPERATOR-CONJUGATION transport, which (numerically verified, "CO" column,
--     machine precision) is COST-OUTERMOST per layer:
--         U_layer† (û·τ⃗) U_layer = (R_{b̂}(4γ)·R_ẑ(4·(−β))·û)·τ⃗   on active states,
--     where `U_layer = U_B U_C`, `U_C = exp(−iγ Hz)`, `U_B = exp(+iβ Hx)` (the (−β) feed).
--   * Depth induction over `qaoaStateAux` (inner-peel, layer 0 first) lands at
--         ⟨ψ̃|û·τ⃗|ψ̃⟩ = (W·û) ⬝ᵥ ẑ ,   W = ∏_{m=0}^{P−1} R_{b̂}(4γ_m)·R_ẑ(4·(−β_m)).
--   * The c-number BRIDGE (numerically verified "(W u).z = (F u).tauVec", all u, machine precision):
--         (W·û) ⬝ᵥ ẑ = (F·û) ⬝ᵥ tauVec ,   F = diag(1,−1,1),
--     proven transpose-free from the per-layer fact `R_{b̂}/R_ẑ` are isometries.
--     Specialize `û = b̂_k`: since `b̂_k` has zero y-component, `F·b̂_k = b̂_k`, hence
--         (W·b̂_k) ⬝ᵥ ẑ = b̂_k ⬝ᵥ tauVec  ⟹  ⟨ψ̃|b̂·τ⃗|ψ̃⟩ = b̂ ⬝ᵥ tauVec.
--   * Combine with `HredZMode_eq_dotTau` (factor −2) and sum over k∈K_ABC.
-- ----------------------------------------------------------------------------

/-- Adjoint move across the inner product: `⟨A ψ | χ⟩ = ⟨ψ | A† χ⟩`. -/
theorem braAKet_move_dag {N : ℕ} (ψ χ : NQubitKet N) (A : NQubitOp N) :
    (A * ψ).dag * χ = ψ.dag * (A.conjTranspose * χ) := by
  rw [bra_mul_ket_eq, bra_mul_ket_eq]
  simp only [Ket.dag_vec, op_mul_ket_vec, starRingEnd_apply]
  -- ∑ i, star((A *ᵥ ψ.vec) i) * χ.vec i  =  ∑ i, star(ψ.vec i) * (Aᴴ *ᵥ χ.vec) i
  have hL : (∑ i, star ((A *ᵥ ψ.vec) i) * χ.vec i)
        = ∑ i, ∑ j, star (A i j) * star (ψ.vec j) * χ.vec i := by
    apply Finset.sum_congr rfl; intro i _
    simp only [Matrix.mulVec, dotProduct, star_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro j _; rw [star_mul']
  have hR : (∑ i, star (ψ.vec i) * (A.conjTranspose *ᵥ χ.vec) i)
        = ∑ i, ∑ j, star (ψ.vec i) * (star (A j i) * χ.vec j) := by
    apply Finset.sum_congr rfl; intro i _
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Matrix.conjTranspose_apply]
  rw [hL, hR, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _; ring

/-- The conjugate-transpose of the reduced cost unitary `U_C = exp(−iγ Hz)` is
`exp(+iγ Hz)` (Hermiticity of `Hred_z_pm`). -/
theorem costUnitary_dag (P : ℕ) (γ : ℝ) :
    ((UpperBound.reducedChainQAOAExp false P).costUnitary γ : NQubitOp (2*P+2)).conjTranspose
      = NormedSpace.exp ((Complex.I * (γ : ℂ)) • UpperBound.Hred_z_pm false P) := by
  rw [(UpperBound.reducedChainQAOAExp false P).costUnitary_spec γ]
  unfold costExponential
  change (NormedSpace.exp ((-γ * Complex.I) • (UpperBound.Hred_z_hamiltonian false P).toOp))ᴴ
      = NormedSpace.exp ((Complex.I * (γ : ℂ)) • UpperBound.Hred_z_pm false P)
  rw [UpperBound.Hred_z_hamiltonian_toOp, ← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, Hred_z_pm_isHermitian]
  rw [show ((-γ * Complex.I : ℂ)) = ((-γ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [show star (((-γ : ℝ) : ℂ) * Complex.I) = Complex.I * (γ : ℂ) by
    rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring]

/-- The conjugate-transpose of the reduced mixer unitary `U_B = exp(−iβ Hx)` is
`exp(+iβ Hx)` (Hermiticity of `Hred_x_op`). -/
theorem mixerUnitary_dag (P : ℕ) (β : ℝ) :
    ((UpperBound.reducedChainQAOAExp false P).mixerUnitary β : NQubitOp (2*P+2)).conjTranspose
      = NormedSpace.exp ((Complex.I * (β : ℂ)) • UpperBound.Hred_x_op P) := by
  rw [(UpperBound.reducedChainQAOAExp false P).mixerUnitary_spec β]
  unfold mixerExponential
  change (NormedSpace.exp ((-β * Complex.I) • (UpperBound.Hred_x_hamiltonian P).toOp))ᴴ
      = NormedSpace.exp ((Complex.I * (β : ℂ)) • UpperBound.Hred_x_op P)
  rw [UpperBound.Hred_x_hamiltonian_toOp, ← Matrix.exp_conjTranspose]
  congr 1
  rw [Matrix.conjTranspose_smul, Hred_x_op_isHermitian]
  rw [show ((-β * Complex.I : ℂ)) = ((-β : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [show star (((-β : ℝ) : ℂ) * Complex.I) = Complex.I * (β : ℂ) by
    rw [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast; ring]

/-- **Per-layer operator-conjugation transport (active states), per mode `n`.**
For active `v`, conjugating `dotTau_n a` by one reduced QAOA layer `U_layer = U_B(b) U_C(g)`
rotates the axis by the COST-OUTERMOST block `R_{b̂}(4g)·R_ẑ(4b)`:
`U_layer† (dotTau_n a) U_layer v = dotTau_n (R_{b̂}(4g) R_ẑ(4b) a) v`.
(`U_C(g) = exp(−ig Hz)`, `U_B(b) = exp(−ib Hx)`; the daggers give the `+i` direction
matching `costLayer_conj`/`mixerLayer_conj`.) -/
theorem layer_conj_dotTau_transport (P : ℕ) (n : Fin P) (g b : ℝ) (a : Fin 3 → ℝ)
    (v : NQubitKet (2 * P + 2)) (hv : InActiveSubspace P v) :
    NormedSpace.exp ((Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) *
        (NormedSpace.exp ((Complex.I * (b : ℂ)) • UpperBound.Hred_x_op P) *
          (dotTau P (waveVectorABC P n) a *
            (NormedSpace.exp ((-Complex.I * (b : ℂ)) • UpperBound.Hred_x_op P) *
              (NormedSpace.exp ((-Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) * v))))
      = dotTau P (waveVectorABC P n)
          (R (bHat (waveVectorABC P n)) (4 * g) *ᵥ (R zHat (4 * b) *ᵥ a)) * v := by
  -- `vC := exp(−ig Hz) v` is active.
  have hvC : InActiveSubspace P
      (NormedSpace.exp ((-Complex.I * (b : ℂ)) • UpperBound.Hred_x_op P) *
        (NormedSpace.exp ((-Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) * v)) := by
    have h1 : InActiveSubspace P
        (NormedSpace.exp ((-Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) * v) :=
      exp_smul_preserves_inActiveSubspace_of_op P (-Complex.I * (g : ℂ)) _
        (fun w hw => Hred_z_pm_preserves_inActiveSubspace P w hw) v hv
    exact exp_smul_preserves_inActiveSubspace_of_op P (-Complex.I * (b : ℂ)) _
      (fun w hw => Hred_x_op_preserves_inActiveSubspace P w hw) _ h1
  set vC := NormedSpace.exp ((-Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) * v with hvCdef
  have hvCact : InActiveSubspace P vC :=
    exp_smul_preserves_inActiveSubspace_of_op P (-Complex.I * (g : ℂ)) _
      (fun w hw => Hred_z_pm_preserves_inActiveSubspace P w hw) v hv
  -- Normalize `-Complex.I * x` to `-(Complex.I * x)` so the reduction lemmas (which use `-c`) fire.
  rw [show (-Complex.I * (b : ℂ)) = -(Complex.I * (b : ℂ)) by ring,
    show (-Complex.I * (g : ℂ)) = -(Complex.I * (g : ℂ)) by ring] at *
  -- Step 1: inner mixer conjugation reduces (active vC) to the per-mode `HXMode` conjugation.
  rw [mixerExp_conj_dotTau_eq_modeExp P n (Complex.I * (b : ℂ)) a vC hvCact]
  -- Collapse it via `mixerLayer_conj` (op-level): re-associate to `(exp·dotTau·exp)·vC`.
  rw [← op_mul_op_mul_ket (dotTau P (waveVectorABC P n) a),
    ← op_mul_op_mul_ket (NormedSpace.exp ((Complex.I * (b : ℂ)) • HredXMode P (waveVectorABC P n))),
    ← mul_assoc]
  rw [show (NormedSpace.exp ((Complex.I * (b : ℂ)) • HredXMode P (waveVectorABC P n))
        * dotTau P (waveVectorABC P n) a
        * NormedSpace.exp (-(Complex.I * (b : ℂ)) • HredXMode P (waveVectorABC P n)))
      = dotTau P (waveVectorABC P n) (R zHat (4 * b) *ᵥ a) by
    have := mixerLayer_conj P n a b
    rw [show ((-Complex.I * (b : ℂ))) = -(Complex.I * (b : ℂ)) by ring] at this
    exact this]
  -- Step 2: outer cost conjugation. Unfold `vC = exp(−ig Hz)·v` so the inner cost exp is visible.
  rw [hvCdef]
  rw [costExp_conj_dotTau_eq_modeExp P n (Complex.I * (g : ℂ)) (R zHat (4 * b) *ᵥ a) v hv]
  rw [← op_mul_op_mul_ket (dotTau P (waveVectorABC P n) (R zHat (4 * b) *ᵥ a)),
    ← op_mul_op_mul_ket (NormedSpace.exp ((Complex.I * (g : ℂ)) • HredZMode P (waveVectorABC P n))),
    ← mul_assoc]
  rw [show (NormedSpace.exp ((Complex.I * (g : ℂ)) • HredZMode P (waveVectorABC P n))
        * dotTau P (waveVectorABC P n) (R zHat (4 * b) *ᵥ a)
        * NormedSpace.exp (-(Complex.I * (g : ℂ)) • HredZMode P (waveVectorABC P n)))
      = dotTau P (waveVectorABC P n) (R (bHat (waveVectorABC P n)) (4 * g) *ᵥ (R zHat (4 * b) *ᵥ a)) by
    have := costLayer_conj P n (R zHat (4 * b) *ᵥ a) g
    rw [show ((-Complex.I * (g : ℂ))) = -(Complex.I * (g : ℂ)) by ring] at this
    exact this]

/-- **Per-layer EXPECTATION transport.** Applying one reduced QAOA layer to an active
`ψ0` rotates the `dotTau` expectation axis by the cost-outer block `R_{b̂}(4g)·R_ẑ(4b)`:
`⟨U_B(b)U_C(g)ψ0 | dotTau_n a | U_B(b)U_C(g)ψ0⟩ = ⟨ψ0 | dotTau_n (R_{b̂}(4g) R_ẑ(4b) a) | ψ0⟩`. -/
theorem applyLayer_dotTau_expectation (P : ℕ) (n : Fin P) (g b : ℝ) (a : Fin 3 → ℝ)
    (ψ0 : Qubits.NQubitNormKet (2 * P + 2)) (hψ0 : InActiveSubspace P ψ0.toKet) :
    (applyLayer ((UpperBound.reducedChainQAOAExp false P).costUnitary g)
        ((UpperBound.reducedChainQAOAExp false P).mixerUnitary b) ψ0).toKet.dag *
      (dotTau P (waveVectorABC P n) a *
        (applyLayer ((UpperBound.reducedChainQAOAExp false P).costUnitary g)
          ((UpperBound.reducedChainQAOAExp false P).mixerUnitary b) ψ0).toKet) =
      ψ0.toKet.dag *
        (dotTau P (waveVectorABC P n)
          (R (bHat (waveVectorABC P n)) (4 * g) *ᵥ (R zHat (4 * b) *ᵥ a)) * ψ0.toKet) := by
  rw [applyLayer_toKet, unitaryOp_mul_ket_eq_op, unitaryOp_mul_ket_eq_op]
  set UC := ((UpperBound.reducedChainQAOAExp false P).costUnitary g : NQubitOp (2*P+2)) with hUC
  set UB := ((UpperBound.reducedChainQAOAExp false P).mixerUnitary b : NQubitOp (2*P+2)) with hUB
  -- Move both unitaries from the bra to the ket as their conjugate-transposes.
  rw [braAKet_move_dag (UC * ψ0.toKet) _ UB, braAKet_move_dag ψ0.toKet _ UC]
  -- Identify the conjugate-transposes with the `+i` exponentials.
  rw [hUC, hUB, costUnitary_dag, mixerUnitary_dag,
    (UpperBound.reducedChainQAOAExp false P).costUnitary_spec g,
    (UpperBound.reducedChainQAOAExp false P).mixerUnitary_spec b]
  unfold costExponential mixerExponential
  change ψ0.toKet.dag *
      (NormedSpace.exp ((Complex.I * (g : ℂ)) • UpperBound.Hred_z_pm false P) *
        (NormedSpace.exp ((Complex.I * (b : ℂ)) • UpperBound.Hred_x_op P) *
          (dotTau P (waveVectorABC P n) a *
            (NormedSpace.exp ((-b * Complex.I) • (UpperBound.Hred_x_hamiltonian P).toOp) *
              (NormedSpace.exp ((-g * Complex.I) • (UpperBound.Hred_z_hamiltonian false P).toOp) *
                ψ0.toKet))))) = _
  rw [UpperBound.Hred_z_hamiltonian_toOp, UpperBound.Hred_x_hamiltonian_toOp]
  -- Now reshape the operator chain to the `layer_conj_dotTau_transport` form and apply it.
  rw [show ((-g * Complex.I) : ℂ) = (-Complex.I * (g : ℂ)) by ring,
    show ((-b * Complex.I) : ℂ) = (-Complex.I * (b : ℂ)) by ring]
  congr 1
  rw [← layer_conj_dotTau_transport P n g b a ψ0.toKet hψ0]

/-- The cost-outer axis accumulation `W·a` for `p` layers and mode-axis `k`:
`accCO 0 a = a`, `accCO (p+1) a = R_{b̂}(4γ₀)·R_ẑ(4β₀)·(accCO p (tail γ,tail β) a)`. -/
def accCO (k : ℝ) : (p : ℕ) → (Fin p → ℝ) → (Fin p → ℝ) → (Fin 3 → ℝ) → (Fin 3 → ℝ) :=
  fun p =>
    match p with
    | 0 => fun _ _ a => a
    | _ + 1 => fun γ β a =>
        R (bHat k) (4 * γ 0) *ᵥ (R zHat (4 * β 0) *ᵥ accCO k _ (tailFamily γ) (tailFamily β) a)

/-- `tailFamily ∘ costUnitaryFamily = costUnitaryFamily ∘ tailFamily` (rfl). -/
theorem tailFamily_costUnitaryFamily {N q : ℕ} (Ham : QAOA.QAOAHamiltonians N) (γ : Fin (q + 1) → ℝ) :
    QAOA.tailFamily (QAOA.costUnitaryFamily Ham γ)
      = QAOA.costUnitaryFamily Ham (QAOA.tailFamily γ) := rfl

/-- `tailFamily ∘ mixerUnitaryFamily = mixerUnitaryFamily ∘ tailFamily` (rfl). -/
theorem tailFamily_mixerUnitaryFamily {N q : ℕ} (Ham : QAOA.QAOAHamiltonians N) (β : Fin (q + 1) → ℝ) :
    QAOA.tailFamily (QAOA.mixerUnitaryFamily Ham β)
      = QAOA.mixerUnitaryFamily Ham (QAOA.tailFamily β) := rfl

/-- **Heisenberg depth induction (general over initial state and axis).** For active `ψ0`,
the depth-`p` reduced-QAOA `dotTau_n` expectation transports the axis by the cost-outer
accumulation `accCO`:
`⟨ψ_p[ψ0] | dotTau_n a | ψ_p[ψ0]⟩ = ⟨ψ0 | dotTau_n (accCO_p a) | ψ0⟩`. -/
theorem qaoa_dotTau_expectation (P : ℕ) (n : Fin P) :
    ∀ (p : ℕ) (γ β : Fin p → ℝ) (a : Fin 3 → ℝ) (ψ0 : Qubits.NQubitNormKet (2*P+2)),
      InActiveSubspace P ψ0.toKet →
      (qaoaState
          (costUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians γ)
          (mixerUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians β)
          ψ0).toKet.dag *
        (dotTau P (waveVectorABC P n) a *
          (qaoaState
            (costUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians γ)
            (mixerUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians β)
            ψ0).toKet) =
        ψ0.toKet.dag *
          (dotTau P (waveVectorABC P n) (accCO (waveVectorABC P n) p γ β a) * ψ0.toKet) := by
  intro p
  induction p with
  | zero =>
      intro γ β a ψ0 hψ0
      -- depth-0 qaoaState is ψ0; accCO 0 = id.
      rfl
  | succ p IH =>
      intro γ β a ψ0 hψ0
      rw [qaoaState_succ, tailFamily_costUnitaryFamily, tailFamily_mixerUnitaryFamily]
      simp only [QAOA.costUnitaryFamily_apply, QAOA.mixerUnitaryFamily_apply]
      -- the first layer (cost γ 0, mixer β 0) is applied; recurse on the tail.
      have hlayer : InActiveSubspace P
          (applyLayer ((UpperBound.reducedChainQAOAExp false P).costUnitary (γ 0))
            ((UpperBound.reducedChainQAOAExp false P).mixerUnitary (β 0)) ψ0).toKet :=
        applyLayer_preserves_inActiveSubspace P (γ 0) (β 0) ψ0 hψ0
      rw [IH (tailFamily γ) (tailFamily β) a _ hlayer]
      -- one-layer expectation transport on ψ0.
      rw [applyLayer_dotTau_expectation P n (γ 0) (β 0)
        (accCO (waveVectorABC P n) p (tailFamily γ) (tailFamily β) a) ψ0 hψ0]
      rfl

-- ----------------------------------------------------------------------------
-- The c-number BRIDGE  `accCO ⬝ᵥ ẑ = b̂ ⬝ᵥ tauVec`  (transpose-free).
-- ----------------------------------------------------------------------------

/-- The y-sign flip `F = diag(1,−1,1)` on `Fin 3 → ℝ`, relating the full Heisenberg
magnetization `m⃗ = (τx,−τy,τz)` to the c-number `tauVec`. -/
def flipY (a : Fin 3 → ℝ) : Fin 3 → ℝ := ![a 0, -(a 1), a 2]

@[simp] theorem flipY_flipY (a : Fin 3 → ℝ) : flipY (flipY a) = a := by
  funext i; fin_cases i <;> simp [flipY]

/-- `F·b̂_k = b̂_k` (the cost axis has zero y-component). -/
theorem flipY_bHat (k : ℝ) : flipY (bHat k) = bHat k := by
  funext i; fin_cases i <;> simp [flipY, bHat]

/-- `F·ẑ = ẑ`. -/
theorem flipY_zHat : flipY zHat = zHat := by
  funext i; fin_cases i <;> simp [flipY, zHat]

/-- Move a `*ᵥ` across the dot product as the transpose: `(A *ᵥ v) ⬝ᵥ s = v ⬝ᵥ (Aᵀ *ᵥ s)`. -/
theorem mulVec_dotProduct_transpose {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (v s : Fin N → ℝ) :
    (A *ᵥ v) ⬝ᵥ s = v ⬝ᵥ (A.transpose *ᵥ s) := by
  rw [dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose]

/-- The transpose of a Rodrigues rotation, applied to a vector:
`(R n θ)ᵀ *ᵥ v = cos θ • v + (1−cos θ)•((n⬝ᵥv)•n) − sin θ • (n ⨯₃ v)` (the `−θ` rotation:
`(nnᵀ)ᵀ = nnᵀ`, `crossMatrixᵀ = −crossMatrix`). -/
theorem R_transpose_mulVec (n v : Fin 3 → ℝ) (θ : ℝ) :
    (R n θ).transpose *ᵥ v =
      (Real.cos θ) • v + (1 - Real.cos θ) • ((n ⬝ᵥ v) • n) - (Real.sin θ) • (n ⨯₃ v) := by
  unfold R
  rw [Matrix.transpose_add, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
    Matrix.transpose_smul, Matrix.transpose_one, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [show (Matrix.vecMulVec n n).transpose = Matrix.vecMulVec n n by
    ext i j; simp [Matrix.vecMulVec, Matrix.transpose_apply, mul_comm]]
  rw [vecMulVec_mulVec]
  rw [show (crossMatrix n).transpose = -crossMatrix n by
    ext i j; fin_cases i <;> fin_cases j <;> simp [crossMatrix, Matrix.transpose_apply]]
  rw [Matrix.neg_mulVec, crossMatrix_mulVec, smul_neg]
  abel

/-- Per-layer `F`-conjugation fact for `b̂_k`: `F·(R_{b̂}(θ)ᵀ *ᵥ v) = R_{b̂}(θ) *ᵥ (F·v)`
(the `b̂` axis has zero y-component, so the y-flip commutes through the rotation). -/
theorem flipY_R_bHat_transpose (k θ : ℝ) (v : Fin 3 → ℝ) :
    flipY ((R (bHat k) θ).transpose *ᵥ v) = R (bHat k) θ *ᵥ flipY v := by
  rw [R_transpose_mulVec, R_mulVec]
  funext i
  fin_cases i <;>
    (simp [flipY, bHat, dotProduct, cross_apply, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> try ring)

/-- Per-layer `F`-conjugation fact for `ẑ`: `F·(R_ẑ(θ)ᵀ *ᵥ v) = R_ẑ(θ) *ᵥ (F·v)`. -/
theorem flipY_R_zHat_transpose (θ : ℝ) (v : Fin 3 → ℝ) :
    flipY ((R zHat θ).transpose *ᵥ v) = R zHat θ *ᵥ flipY v := by
  rw [R_transpose_mulVec, R_mulVec]
  funext i
  fin_cases i <;>
    (simp [flipY, zHat, dotProduct, cross_apply, Fin.sum_univ_three, Matrix.vecHead,
      Matrix.vecTail, Pi.smul_apply, smul_eq_mul] <;> try ring)

/-- `F` preserves the dot product: `(F·a) ⬝ᵥ (F·s) = a ⬝ᵥ s` (it only flips signs in pairs). -/
theorem flipY_dotProduct (a s : Fin 3 → ℝ) : flipY a ⬝ᵥ flipY s = a ⬝ᵥ s := by
  simp only [flipY, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- `extendFin (tailFamily γ) m = extendFin γ (m+1)` (the padded tail is the shift). -/
theorem extendFin_tailFamily {p : ℕ} (γ : Fin (p + 1) → ℝ) (m : ℕ) :
    extendFin (tailFamily γ) m = extendFin γ (m + 1) := by
  unfold extendFin tailFamily
  by_cases h : m < p
  · rw [dif_pos h, dif_pos (by omega : m + 1 < p + 1)]; rfl
  · rw [dif_neg h, dif_neg (by omega : ¬ m + 1 < p + 1)]

/-- `layerProd (p+1) = layerProd p (shifted) · layerBlock 0`: peel the INNERMOST (index-0)
layer at the seed end. Pure structural fact on the `ℕ`-indexed families. -/
theorem layerProd_succ_shift (p : ℕ) (k : ℝ) (γ β : ℕ → ℝ) :
    layerProd (p + 1) k γ β
      = layerProd p k (fun m => γ (m + 1)) (fun m => β (m + 1)) * layerBlock k γ β 0 := by
  induction p with
  | zero => simp only [layerProd, one_mul, mul_one]
  | succ p IH =>
      rw [show layerProd (p + 1 + 1) k γ β
            = layerBlock k γ β (p + 1) * layerProd (p + 1) k γ β from rfl, IH]
      rw [show layerProd (p + 1) k (fun m => γ (m + 1)) (fun m => β (m + 1))
            = layerBlock k (fun m => γ (m + 1)) (fun m => β (m + 1)) p
              * layerProd p k (fun m => γ (m + 1)) (fun m => β (m + 1)) from rfl]
      rw [show layerBlock k (fun m => γ (m + 1)) (fun m => β (m + 1)) p
            = layerBlock k γ β (p + 1) from rfl]
      rw [mul_assoc]

/-- **The c-number bridge (generalized over the seed `s`).** The cost-outer accumulation
`accCO` and the `tauVec` rotation product `layerProd` are y-flip conjugate:
`accCO_p a ⬝ᵥ s = (F·a) ⬝ᵥ (layerProd_p *ᵥ (F·s))`. Inner-peel induction on `p`, each step
discharged by the per-layer `F`-conjugation facts. -/
theorem accCO_dotProduct_eq (k : ℝ) :
    ∀ (p : ℕ) (γ β : Fin p → ℝ) (a s : Fin 3 → ℝ),
      accCO k p γ β a ⬝ᵥ s
        = (flipY a) ⬝ᵥ (layerProd p k (extendFin γ) (extendFin β) *ᵥ (flipY s)) := by
  intro p
  induction p with
  | zero =>
      intro γ β a s
      simp only [accCO, layerProd, Matrix.one_mulVec]
      exact (flipY_dotProduct a s).symm
  | succ p IH =>
      intro γ β a s
      -- accCO peels the INNERMOST (index-0) layer: B_co(0) on the outside.
      change (R (bHat k) (4 * γ 0) *ᵥ (R zHat (4 * β 0) *ᵥ
          accCO k p (tailFamily γ) (tailFamily β) a)) ⬝ᵥ s = _
      -- move the two leading rotations onto `s` as transposes.
      rw [mulVec_dotProduct_transpose, mulVec_dotProduct_transpose]
      -- IH on the tail with the transported seed.
      rw [IH (tailFamily γ) (tailFamily β) a _]
      -- rewrite `layerProd (p+1)` via the index-0 peel and `extendFin`-tail = shift.
      have hshift : (fun m => extendFin γ (m + 1)) = extendFin (tailFamily γ) := by
        funext m; rw [extendFin_tailFamily]
      have hshiftβ : (fun m => extendFin β (m + 1)) = extendFin (tailFamily β) := by
        funext m; rw [extendFin_tailFamily]
      rw [show layerProd (p + 1) k (extendFin γ) (extendFin β)
            = layerProd p k (extendFin (tailFamily γ)) (extendFin (tailFamily β))
              * layerBlock k (extendFin γ) (extendFin β) 0 by
        rw [layerProd_succ_shift p k (extendFin γ) (extendFin β), hshift, hshiftβ]]
      rw [← Matrix.mulVec_mulVec]
      congr 2
      -- the per-layer F-conjugation: flipY((R_ẑᵀ)(R_b̂ᵀ s)) = layerBlock 0 (flipY s).
      unfold layerBlock
      rw [show extendFin β 0 = β 0 by rw [extendFin, dif_pos (Nat.zero_lt_succ p)]; rfl,
        show extendFin γ 0 = γ 0 by rw [extendFin, dif_pos (Nat.zero_lt_succ p)]; rfl]
      rw [← Matrix.mulVec_mulVec, flipY_R_zHat_transpose, flipY_R_bHat_transpose]

/-- `psiTilde false P γ (-β)` is the depth-`P` reduced-chain QAOA state on the uniform
initial state (definitional unfolding of `standardExponentialQAOAState`). -/
theorem psiTilde_eq_qaoaState {P : ℕ} (γ β : Fin P → ℝ) :
    (UpperBound.psiTilde false P γ (-β)) =
      qaoaState
        (costUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians γ)
        (mixerUnitaryFamily (UpperBound.reducedChainQAOAExp false P).toQAOAHamiltonians
          (fun i => -(β i)))
        (UpperBound.psiTilde_init P) := rfl

/-- **Single-mode cost expectation.** `⟨ψ̃ | HredZMode_n | ψ̃⟩ = −2 (b̂_{k_n} ⬝ᵥ τ⃗_{k_n}(γ,−β))`.
The Heisenberg depth induction `qaoa_dotTau_expectation` (seeded by the base case
`dotTau_expectation_uniformKet`) followed by the c-number bridge `accCO_dotProduct_eq`
(`F·b̂ = b̂`, `F·ẑ = ẑ`). -/
theorem mode_expectation {P : ℕ} (n : Fin P) (γ β : Fin P → ℝ) :
    (UpperBound.psiTilde false P γ (-β)).toKet.dag *
        (HredZMode P (waveVectorABC P n) * (UpperBound.psiTilde false P γ (-β)).toKet) =
      ((-2 : ℂ)) *
        ((bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ) (extendFin (fun i => -(β i))) : ℝ) : ℂ) := by
  -- Step A: `HredZMode = −2 • dotTau b̂`; pull the scalar out of the expectation.
  rw [HredZMode_eq_dotTau P n, smul_op_mul_ket, bra_mul_smul_ket]
  -- Step B: the Heisenberg depth induction (ψ̃ = qaoaState on the uniform init).
  rw [psiTilde_eq_qaoaState γ β]
  have hbase : InActiveSubspace P (UpperBound.psiTilde_init P).toKet :=
    inActiveSubspace_uniformState P
  rw [qaoa_dotTau_expectation P n P γ (fun i => -(β i)) (bHat (waveVectorABC P n))
    (UpperBound.psiTilde_init P) hbase]
  -- Step C: the quantum base case `⟨ψ0|dotTau u|ψ0⟩ = (u ⬝ᵥ ẑ : ℂ)`.
  change ((-2 : ℂ)) * ((UpperBound.psiTilde_init P).toKet.dag *
      (dotTau P (waveVectorABC P n) _ * (UpperBound.psiTilde_init P).toKet)) = _
  rw [show (UpperBound.psiTilde_init P).toKet = uniformKet (Qubits.NQubitDim (2*P+2)) from rfl,
    dotTau_expectation_uniformKet P (waveVectorABC P n)
      (accCO (waveVectorABC P n) P γ (fun i => -(β i)) (bHat (waveVectorABC P n)))]
  -- Step D: the c-number bridge (seed `s = ẑ`), `F·b̂ = b̂`, `F·ẑ = ẑ`.
  congr 1
  rw [accCO_dotProduct_eq (waveVectorABC P n) P γ (fun i => -(β i))
    (bHat (waveVectorABC P n)) zHat, flipY_bHat, flipY_zHat]
  rfl

/-- The mode-sum cost expectation on `ψ̃` equals `−2 Σ_n b̂_{k_n} ⬝ᵥ τ⃗_{k_n}(γ,−β)`:
the Heisenberg depth induction `qaoa_dotTau_expectation` (whose per-layer operator
transport `applyLayer_dotTau_expectation` rotates the axis by the COST-OUTER block
`R_{b̂}(4γ)·R_ẑ(4·(−β))`) composed with the y-flip c-number bridge `accCO_dotProduct_eq`,
summed over `k ∈ K_ABC`. The full magnetization is the y-flip `m⃗ = (τx,−τy,τz)` of `tauVec`;
This holds because the projection onto the cost axis `b̂_k` is flip-invariant (`b̂_y = 0`). -/
theorem mode_sum_expectation {P : ℕ} (γ β : Fin P → ℝ) :
    (UpperBound.psiTilde false P γ (-β)).toKet.dag *
        ((∑ n : Fin P, HredZMode P (waveVectorABC P n)) *
          (UpperBound.psiTilde false P γ (-β)).toKet) =
      ((-2 : ℂ)) * ∑ n : Fin P,
        ((bHat (waveVectorABC P n) ⬝ᵥ
          tauVec P (waveVectorABC P n) (extendFin γ) (extendFin (fun i => -(β i))) : ℝ) : ℂ) := by
  rw [Finset.mul_sum]
  -- distribute the bra-op-ket over the operator sum (induction over `Finset.univ`).
  have hdist : ∀ (s : Finset (Fin P)),
      (UpperBound.psiTilde false P γ (-β)).toKet.dag *
        ((∑ n ∈ s, HredZMode P (waveVectorABC P n)) *
          (UpperBound.psiTilde false P γ (-β)).toKet)
      = ∑ n ∈ s, (UpperBound.psiTilde false P γ (-β)).toKet.dag *
          (HredZMode P (waveVectorABC P n) * (UpperBound.psiTilde false P γ (-β)).toKet) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : NQubitOp (2*P+2)) * (UpperBound.psiTilde false P γ (-β)).toKet
              = (0 : NQubitKet (2*P+2)) by ext i; simp [op_mul_ket_vec]]
        rw [show (UpperBound.psiTilde false P γ (-β)).toKet.dag * (0 : NQubitKet (2*P+2))
              = (0 : ℂ) by rw [bra_mul_ket_eq]; simp]
    | insert a s ha ih =>
        rw [Finset.sum_insert ha, Finset.sum_insert ha, add_op_mul_ket, bra_mul_add_ket, ih]
  rw [hdist Finset.univ]
  apply Finset.sum_congr rfl
  intro n _
  exact mode_expectation n γ β

end

end QAOA.IsingChain.JordanWigner
