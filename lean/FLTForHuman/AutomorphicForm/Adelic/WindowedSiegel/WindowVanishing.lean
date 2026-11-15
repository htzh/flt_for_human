/-
  The vanishing of the `(1,0)` entry of a global point, at archimedean height.

  `exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem`:
  for a compact set `C` of `GL₂(𝔸_F)` there is a height threshold `T₀` such that whenever
  `x` and `y` are finite-integral with archimedean height above `T₀`, every global
  `γ : GL₂(F)` and central scalar `z` with `x⁻¹ · globalPoints γ · y · centralScalar z ∈ C`
  has `γ 1 0 = 0`. In words: a compact set of the adelic quotient above the height `T₀`
  sees no nontrivial unipotent part of a rational point.

  Transcribed from `P2M/Sol/S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem.lean`
  (pinned `aa2d8b3`, 386 lines: 23 private engine declarations and this headline).

  **The two height bounds.** The proof is a product of two independent bounds, both read
  off the compactness of `C`. On the archimedean side a `GL₂(K_∞)`-element `k` carries a
  correction factor `archTransFactor k = ∏_v transFactor (k_v)^{v.mult}`, where
  `transFactor k = ‖k‖²_F / ‖det k‖` (squared Frobenius norm over the determinant), such
  that `archHeight g ≤ archTransFactor k * archHeight (g * k)`; it is continuous, so
  bounded on `C`. On the finite side `finHeight (x · glFin k)` is bounded below by `1/B`
  for `x` finite-integral and `k ∈ C`, again by compactness — of the finite level-zero
  subgroup in which `C` is contained. The row then argues by contradiction: a nonvanishing
  `γ 1 0` gives `adelicHeight (globalPoints γ · y) · adelicHeight y ≤ 1`, and the two
  bounds turn the height hypotheses into `1 < archHeight x · finHeight x · archHeight y`
  with `archHeight y` large, a contradiction.

  **What is reused.** The pin's four ultrametric/local transport lemmas
  (`rowMaxNorm_mul_le`, `finLocalHeight_mul_eq`, `finHeight_mul_of_mem`,
  `continuous_finHeight`) are already public in
  `FLTForHuman/NumberTheory/AdelicHeight.lean` and are used from there rather than
  restated; so is the pin's `mul_centralScalar_eq`, which is the general
  `AutomorphicForm.centralScalar_mul_comm` (`AutomorphicForm/Adelic/Basic.lean`). The pin's
  `centralScalar_coe` is kept as a private helper because the port's public statement of it
  (`AutomorphicForm.centralScalar_val`, `NumberTheory/AdelicVolume.lean`) lives outside this
  module's import closure.

  spec-pin: P2M/Sol/S_AutomorphicForm_WindowedSiegel_exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Set
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicLevel.Projections

set_option autoImplicit false

-- Heartbeat probe (work order AF83C, gate 6) — **recorded, not installed**. Playbook §3.5 is
-- explicit: no module carries a `set_option maxHeartbeats`, because an in-file cap is a defect
-- marker rather than a budget, and `lake build` runs at the project cap anyway. The number is kept
-- here for the next reader. Bisection with `-DmaxHeartbeats=N`: *silent* at 7000 and above;
-- timeouts at 6000 (`whnf`, the row theorem), 5000 (`isDefEq`, `rowNormSq_mul_le`'s `ring`), 4000
-- and 2000 (`nlinarith`/`isDefEq`). The module's natural cost is ≈7000 units — 29× below the edit
-- loop's 200000 — so no floor is owed.

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHeight
open IsDedekindDomain
open scoped Classical

namespace AutomorphicForm

namespace WindowedSiegel

open Matrix

/-! ### The local comparison `localHeight g ≤ transFactor k * localHeight (g * k)` -/

section Local

variable {K : Type*} [NormedField K]

/-- The squared Frobenius norm of a `2 × 2` matrix: the sum of the squared norms of its
four entries. -/
private def entryNormSq (M : Matrix (Fin 2) (Fin 2) K) : ℝ :=
  ‖M 0 0‖ ^ 2 + ‖M 0 1‖ ^ 2 + ‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2

/-- The bottom-row norm of `M * N` is bounded by that of `M` times the Frobenius norm of
`N` (Cauchy–Schwarz in two terms). -/
private theorem rowNormSq_mul_le (M N : Matrix (Fin 2) (Fin 2) K) :
    rowNormSq (M * N) ≤ rowNormSq M * entryNormSq N := by
  have h : ∀ j : Fin 2, ‖(M * N) 1 j‖ ^ 2
      ≤ (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 j‖ ^ 2 + ‖N 1 j‖ ^ 2) := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    have h1 : ‖M 1 0 * N 0 j + M 1 1 * N 1 j‖ ≤ ‖M 1 0‖ * ‖N 0 j‖ + ‖M 1 1‖ * ‖N 1 j‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul]
    have h2 : ‖M 1 0 * N 0 j + M 1 1 * N 1 j‖ ^ 2
        ≤ (‖M 1 0‖ * ‖N 0 j‖ + ‖M 1 1‖ * ‖N 1 j‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    refine h2.trans ?_
    nlinarith [sq_nonneg (‖M 1 0‖ * ‖N 1 j‖ - ‖M 1 1‖ * ‖N 0 j‖), norm_nonneg (M 1 0),
      norm_nonneg (M 1 1), norm_nonneg (N 0 j), norm_nonneg (N 1 j)]
  calc rowNormSq (M * N) = ‖(M * N) 1 0‖ ^ 2 + ‖(M * N) 1 1‖ ^ 2 := rfl
    _ ≤ (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 0‖ ^ 2 + ‖N 1 0‖ ^ 2)
        + (‖M 1 0‖ ^ 2 + ‖M 1 1‖ ^ 2) * (‖N 0 1‖ ^ 2 + ‖N 1 1‖ ^ 2) := add_le_add (h 0) (h 1)
    _ = rowNormSq M * entryNormSq N := by
        unfold rowNormSq entryNormSq
        ring

/-- The correction factor of a local `GL₂`-element: the squared Frobenius norm of its
entries over the norm of its determinant. -/
private def transFactor (k : GL (Fin 2) K) : ℝ :=
  entryNormSq (k : Matrix (Fin 2) (Fin 2) K) / ‖(k : Matrix (Fin 2) (Fin 2) K).det‖

/-- The arithmetic core of `localHeight_le_transFactor_mul`: given `Rgk ≤ Rg * E`, the
quotient `dg / Rg` is bounded by `E / dk` times `dg * dk / Rgk`. -/
private theorem div_le_div_mul_of_le_mul {dg dk Rg Rgk E : ℝ} (hdk : 0 < dk) (hRg : 0 < Rg)
    (hRgk : 0 < Rgk) (hdg : 0 ≤ dg) (hle : Rgk ≤ Rg * E) :
    dg / Rg ≤ E / dk * (dg * dk / Rgk) := by
  rw [div_mul_div_comm, div_le_div_iff₀ hRg (mul_pos hdk hRgk)]
  have h := mul_le_mul_of_nonneg_left hle (mul_nonneg hdg hdk.le)
  calc dg * (dk * Rgk) = dg * dk * Rgk := by ring
    _ ≤ dg * dk * (Rg * E) := h
    _ = E * (dg * dk) * Rg := by ring

/-- Right multiplication by `k` changes the local height at most by the correction factor
`transFactor k`. -/
private theorem localHeight_le_transFactor_mul (g k : GL (Fin 2) K) :
    localHeight g ≤ transFactor k * localHeight (g * k) := by
  have hRg := rowNormSq_pos g
  have hRgk := rowNormSq_pos (g * k)
  rw [Units.val_mul] at hRgk
  have hdk : 0 < ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ :=
    norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero
  unfold localHeight transFactor
  rw [Units.val_mul, Matrix.det_mul, norm_mul]
  exact div_le_div_mul_of_le_mul hdk hRg hRgk (norm_nonneg _) (rowNormSq_mul_le _ _)

/-- A scalar matrix (zero off-diagonal entries, both diagonal entries `a ≠ 0`) acts on the
local height by the identity. -/
private theorem finLocalHeight_scalar_entries_mul {s : GL (Fin 2) K} {a : K} (ha : a ≠ 0)
    (h00 : (s : Matrix (Fin 2) (Fin 2) K) 0 0 = a)
    (h01 : (s : Matrix (Fin 2) (Fin 2) K) 0 1 = 0)
    (h10 : (s : Matrix (Fin 2) (Fin 2) K) 1 0 = 0)
    (h11 : (s : Matrix (Fin 2) (Fin 2) K) 1 1 = a)
    (g : GL (Fin 2) K) :
    finLocalHeight (s * g) = finLocalHeight g := by
  have hcoe : ((s * g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = (s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K) := rfl
  have hrow : ∀ j : Fin 2,
      ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K)) 1 j
        = a * (g : Matrix (Fin 2) (Fin 2) K) 1 j := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two, h10, h11]
    ring
  have hdets : (s : Matrix (Fin 2) (Fin 2) K).det = a ^ 2 := by
    rw [Matrix.det_fin_two, h00, h01, h10, h11]
    ring
  have hmax : rowMaxNorm ((s : Matrix (Fin 2) (Fin 2) K) * (g : Matrix (Fin 2) (Fin 2) K))
      = ‖a‖ * rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowMaxNorm
    rw [hrow 0, hrow 1, norm_mul, norm_mul, mul_max_of_nonneg _ _ (norm_nonneg a)]
  have ha2 : (‖a‖ ^ 2 : ℝ) ≠ 0 := (pow_pos (norm_pos_iff.mpr ha) 2).ne'
  unfold finLocalHeight
  rw [hcoe, Matrix.det_mul, hdets, norm_mul, norm_pow, hmax, mul_pow, mul_div_mul_left _ _ ha2]

variable [IsTopologicalRing K]

/-- The correction factor is continuous on `GL₂(K)`. -/
private theorem continuous_transFactor : Continuous (transFactor : GL (Fin 2) K → ℝ) := by
  have hc : ∀ i j : Fin 2,
      Continuous fun k : GL (Fin 2) K => ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ :=
    fun i j => (Units.continuous_val.matrix_elem i j).norm
  have hnum : Continuous fun k : GL (Fin 2) K => entryNormSq (k : Matrix (Fin 2) (Fin 2) K) := by
    unfold entryNormSq
    exact ((((hc 0 0).pow 2).add ((hc 0 1).pow 2)).add ((hc 1 0).pow 2)).add ((hc 1 1).pow 2)
  have hdet : Continuous fun k : GL (Fin 2) K => ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ :=
    (Units.continuous_val.matrix_det).norm
  exact hnum.div hdet fun k => (norm_pos_iff.mpr (Matrix.isUnits_det_units k).ne_zero).ne'

end Local

/-! ### The finite height at a compact set -/

section Finite

variable (F : Type) [Field F] [NumberField F]

/-- For `x` finite-integral and `k` in a compact set `C`, the finite height of
`x · glFin k` is bounded below by `1/B` for some `B ≥ 1`. -/
private theorem exists_one_le_mul_finHeight {C : Set (AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ x ∈ finiteIntegralGL2 (𝓞 F) F, ∀ k ∈ C,
      1 ≤ B * finHeight F (x * glFin (𝓞 F) F k) := by
  set Φ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) × AdelicGL2 (𝓞 F) F → ℝ :=
    fun p => (finHeight F (p.1 * glFin (𝓞 F) F p.2))⁻¹ with hΦdef
  have hΦ : Continuous Φ :=
    ((continuous_finHeight F).comp
      (continuous_fst.mul ((continuous_glFin (𝓞 F) F).comp continuous_snd))).inv₀
      fun p => (finHeight_pos _).ne'
  obtain ⟨B, hB⟩ := (((isCompact_finiteLevelZero (𝓞 F) F ⊤).prod hC).image hΦ).bddAbove
  refine ⟨max B 1, le_max_right _ _, fun x hx k hk => ?_⟩
  have h : Φ (x, k) ≤ B := hB ⟨(x, k), ⟨hx, hk⟩, rfl⟩
  have hpos := finHeight_pos (F := F) (x * glFin (𝓞 F) F k)
  calc (1 : ℝ) = Φ (x, k) * finHeight F (x * glFin (𝓞 F) F k) := (inv_mul_cancel₀ hpos.ne').symm
    _ ≤ max B 1 * finHeight F (x * glFin (𝓞 F) F k) :=
        mul_le_mul_of_nonneg_right (h.trans (le_max_left _ _)) hpos.le

/-- The underlying matrix of a central scalar is the scalar matrix. -/
private theorem centralScalar_coe (z : (AdeleRing (𝓞 F) F)ˣ) :
    ((centralScalar (𝓞 F) F z : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))
      = Matrix.diagonal fun _ => (z : AdeleRing (𝓞 F) F) := by
  show Matrix.scalar (Fin 2) (z : AdeleRing (𝓞 F) F) = _
  rw [Matrix.scalar_apply]

/-- A unit of the adèle ring has no vanishing finite component. -/
private theorem snd_apply_ne_zero (z : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((z : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ≠ 0 := by
  intro h0
  have h : ((z : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      * (((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = 1 :=
    congrArg (fun a : AdeleRing (𝓞 F) F => (a.2 : FiniteAdeleRing (𝓞 F) F) v) z.mul_inv
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- A unit of the adèle ring has no vanishing archimedean component. -/
private theorem fst_apply_ne_zero (z : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    (((z : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F) w) ≠ 0 := by
  intro h0
  have h : ((z : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F) w
      * (((z⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 : InfiniteAdeleRing F) w = 1 :=
    congrArg (fun a : AdeleRing (𝓞 F) F => (a.1 : InfiniteAdeleRing F) w) z.mul_inv
  rw [h0, zero_mul] at h
  exact zero_ne_one h

/-- Left multiplication by a central scalar does not change the finite height. -/
private theorem finHeight_centralScalar_left (z : (AdeleRing (𝓞 F) F)ˣ)
    (g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    finHeight F (glFin (𝓞 F) F (centralScalar (𝓞 F) F z) * g) = finHeight F g := by
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_scalar_entries_mul (snd_apply_ne_zero F z v) ?_ ?_ ?_ ?_
    (finComponent (𝓞 F) F v g)
  · rw [finComponent_apply, glFin_apply, centralScalar_coe, Matrix.diagonal_apply_eq]
  · rw [finComponent_apply, glFin_apply, centralScalar_coe,
      Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)]
    rfl
  · rw [finComponent_apply, glFin_apply, centralScalar_coe,
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    rfl
  · rw [finComponent_apply, glFin_apply, centralScalar_coe, Matrix.diagonal_apply_eq]

/-- Left multiplication by a central scalar does not change the archimedean height. -/
private theorem archHeight_centralScalar_left (z : (AdeleRing (𝓞 F) F)ˣ)
    (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F (glArch (𝓞 F) F (centralScalar (𝓞 F) F z) * g) = archHeight F g := by
  refine archHeight_scalar_entries_mul F (fst_apply_ne_zero F z) ?_ ?_ ?_ ?_ g
  · rw [glArch_apply, centralScalar_coe, Matrix.diagonal_apply_eq]
  · rw [glArch_apply, centralScalar_coe, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1)]
    rfl
  · rw [glArch_apply, centralScalar_coe, Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0)]
    rfl
  · rw [glArch_apply, centralScalar_coe, Matrix.diagonal_apply_eq]

/-- The adèlic height is invariant under right multiplication by a central scalar. -/
private theorem adelicHeight_mul_centralScalar (g : AdelicGL2 (𝓞 F) F)
    (z : (AdeleRing (𝓞 F) F)ˣ) :
    adelicHeight F (g * centralScalar (𝓞 F) F z) = adelicHeight F g := by
  rw [(centralScalar_mul_comm z g).symm]
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_centralScalar_left, finHeight_centralScalar_left]

end Finite

/-! ### The archimedean height at a compact set -/

section Arch

variable (F : Type) [Field F] [NumberField F]

/-- The archimedean correction factor: the product of the local correction factors over
the infinite places, with the multiplicities `v.mult`. -/
private def archTransFactor (k : GL (Fin 2) (InfiniteAdeleRing F)) : ℝ :=
  ∏ v : InfinitePlace F, transFactor (archComponent F v k) ^ v.mult

/-- Right multiplication by `k` changes the archimedean height at most by
`archTransFactor k`. -/
private theorem archHeight_le_archTransFactor_mul (g k : GL (Fin 2) (InfiniteAdeleRing F)) :
    archHeight F g ≤ archTransFactor F k * archHeight F (g * k) := by
  unfold archHeight archTransFactor
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod₀ (fun v _ => pow_nonneg (localHeight_pos _).le _) fun v _ => ?_
  rw [← mul_pow, map_mul]
  exact pow_le_pow_left₀ (localHeight_pos _).le (localHeight_le_transFactor_mul _ _) _

/-- The archimedean correction factor is continuous. -/
private theorem continuous_archTransFactor : Continuous (archTransFactor F) := by
  unfold archTransFactor
  exact continuous_finsetProd _ fun v _ =>
    (continuous_transFactor.comp (continuous_archComponent F v)).pow _

/-- The archimedean correction factor is bounded on a compact set. -/
private theorem exists_archTransFactor_le {C : Set (AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ k ∈ C, archTransFactor F (glArch (𝓞 F) F k) ≤ B := by
  obtain ⟨B, hB⟩ :=
    (hC.image ((continuous_archTransFactor F).comp (continuous_glArch (𝓞 F) F))).bddAbove
  exact ⟨max B 1, le_max_right _ _, fun k hk => (hB ⟨k, hk, rfl⟩).trans (le_max_left _ _)⟩

end Arch

theorem exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem
    (F : Type) [Field F] [NumberField F]
    {C : Set (AutomorphicForm.AdelicGL2 (𝓞 F) F)} (hC : IsCompact C) :
    ∃ T₀ : ℝ, ∀ (x y : AutomorphicForm.AdelicGL2 (𝓞 F) F),
      NumberField.AdelicLevel.glFin (𝓞 F) F x ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      NumberField.AdelicLevel.glFin (𝓞 F) F y ∈ NumberField.AdelicLevel.finiteIntegralGL2 (𝓞 F) F →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F x) →
      T₀ < AutomorphicForm.WindowedSiegel.archHeight F (NumberField.AdelicLevel.glArch (𝓞 F) F y) →
      ∀ (γ : GL (Fin 2) F) (z : (NumberField.AdeleRing (𝓞 F) F)ˣ),
        x⁻¹ * AutomorphicForm.globalPoints (𝓞 F) F γ * y * AutomorphicForm.centralScalar (𝓞 F) F z
            ∈ C →
          (γ : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  obtain ⟨B₁, hB₁, hB₁C⟩ := exists_archTransFactor_le F hC
  obtain ⟨B₂, hB₂, hB₂C⟩ := exists_one_le_mul_finHeight F hC
  refine ⟨B₁ * B₂, fun x y hx hy hTx hTy γ z hk => ?_⟩
  by_contra hγ
  have hγy : globalPoints (𝓞 F) F γ * (y * centralScalar (𝓞 F) F z)
      = x * (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z) := by
    simp only [mul_assoc, mul_inv_cancel_left]
  have hle := adelicHeight_globalPoints_mul_mul_adelicHeight_le_one γ hγ (y * centralScalar (𝓞 F) F z)
  rw [adelicHeight_mul_centralScalar F y z, adelicHeight_eq_archHeight_of_mem hy, hγy] at hle
  simp only [adelicHeight] at hle
  have eA : glArch (𝓞 F) F (x * (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
      = glArch (𝓞 F) F x
        * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z) :=
    map_mul _ _ _
  have eF : glFin (𝓞 F) F (x * (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
      = glFin (𝓞 F) F x
        * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z) :=
    map_mul _ _ _
  rw [eA, eF] at hle
  have h1 : archHeight F (glArch (𝓞 F) F x)
      ≤ B₁ * archHeight F (glArch (𝓞 F) F x
          * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) :=
    (archHeight_le_archTransFactor_mul F _ _).trans
      (mul_le_mul_of_nonneg_right (hB₁C _ hk) (archHeight_pos F _).le)
  have h2 : 1 ≤ B₂ * finHeight F (glFin (𝓞 F) F x
      * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) :=
    hB₂C _ hx _ hk
  have ha := archHeight_pos F (glArch (𝓞 F) F x
    * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
  have hf := finHeight_pos (F := F) (glFin (𝓞 F) F x
    * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
  have hB₁pos : 0 < B₁ := lt_of_lt_of_le one_pos hB₁
  have hB₁B₂ : 1 ≤ B₁ * B₂ := one_le_mul_of_one_le_of_one_le hB₁ hB₂
  have hB₂a : B₂ < archHeight F (glArch (𝓞 F) F x
      * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) := by
    by_contra h
    push Not at h
    have h' := mul_le_mul_of_nonneg_left h hB₁pos.le
    linarith
  have haf : 1 < archHeight F (glArch (𝓞 F) F x
        * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
      * finHeight F (glFin (𝓞 F) F x
        * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) :=
    calc (1 : ℝ) ≤ B₂ * finHeight F (glFin (𝓞 F) F x
          * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) := h2
      _ < _ := mul_lt_mul_of_pos_right hB₂a hf
  have hY : 1 < archHeight F (glArch (𝓞 F) F y) := lt_of_le_of_lt hB₁B₂ hTy
  have hlt : 1 < archHeight F (glArch (𝓞 F) F x
        * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
      * finHeight F (glFin (𝓞 F) F x
        * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
      * archHeight F (glArch (𝓞 F) F y) :=
    calc (1 : ℝ) < archHeight F (glArch (𝓞 F) F x
          * glArch (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z))
        * finHeight F (glFin (𝓞 F) F x
          * glFin (𝓞 F) F (x⁻¹ * globalPoints (𝓞 F) F γ * y * centralScalar (𝓞 F) F z)) := haf
      _ = _ * 1 := (mul_one _).symm
      _ < _ := mul_lt_mul_of_pos_left hY (lt_trans one_pos haf)
  linarith

end WindowedSiegel

end AutomorphicForm
