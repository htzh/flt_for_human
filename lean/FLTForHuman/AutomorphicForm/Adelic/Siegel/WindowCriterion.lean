/-
  Siegel windows: compactness, monotone covers, and the covering criterion.

  Five rows on the windowed Siegel picture: the centre-cut Siegel set inside a height cap is compact;
  a cover at one window covers at every larger window; the windows' union is a neighbourhood of the
  identity; an `L`-function vanishing on a covering set vanishes.

  The pins are *flattened* files whose declarations are all public (9 + 7 + 1 + 1); their subject
  namespaces are search-stage labels and are renamed here. The fifth row of this subject —
  `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre`
  — is deferred: its statement needs `AutomorphicForm.IsBoundedOnSiegelWindows`, which lives in the
  unported `Def_AutomorphicForm_BoundedGenuineCuspRealization` (316 lines of definitions), and that module
  is the next set's definition-gate work.

  **Namespace renames.** The compaction pin's label namespaces `M4aP1R` / `BoxedBlock` become
  `WindowedSiegel`: its `boxedBlock` is the cap-`C` sibling of `centreCutSiegelSet` /
  `cappedSiegelBlock`, and its row already lives at `WindowedSiegel.isCompact_…`. The monotone-cover
  pin's label namespace `C8DetBand` (part label `C8` + subject `DetBand`) becomes `DetBand`. The pins'
  outer `P2MW.S_…` wrappers go: they are the pipeline's file label, not mathematics.

  The compaction pin carries two wrapper statements the row folds: `…_impl` and `solution` state the
  *same* set as `isCompact_centreCutSiegelSet_inter_heightCap`, and both are declared — the audit
  credits by last name and the checker counts declarations, so a flattened pin lands one declaration
  per pinned public.

  **Proof-level drift (statements unchanged).**
  * `exists_central_adjust`: the pin's `if_pos` / `if_neg` are the deprecated `ite_eq_left` /
    `ite_eq_right` in this mathlib.
  * `isCompact_boxedBlock`: the pin's `haveI := properSpace_completion …` is spelled `have := …` (a
    class-typed local hypothesis still feeds instance search, and the `haveI`/`letI` linter is not
    tripped).
  * `covers_narrow` / the vanishing row: `mul_centralScalar_comm` is qualified `SiegelCovering.…`
    (both `AutomorphicForm` and `AutomorphicForm.SiegelCovering` are open here), and the pin's closing
    rewrite chain is `rw […]; group` — the same steps, with the associativity re-bracket left to
    `group`.

  **Heartbeat probe (measured, never installed — FR-0225).** At the project cap the module is silent;
  `-DmaxHeartbeats=25000` is silent and `-DmaxHeartbeats=12500` (= 25000 / 2) fails at
  `entry_norm_le_of_box` (`isDefEq`), so the floor lies between the two. No `set_option
  maxHeartbeats` is carried — the probe is a measurement, not a floor.

  **Dedup (gate 4) — the pin's own pair.** `dedup.py --within` reports exactly one cluster:
  `isCompact_centreCutSiegelSet_inter_heightCap_impl` (pin `…S_….lean:268`) and the row
  `isCompact_centreCutSiegelSet_inter_heightCap` (pin `…:276`, the pin's `solution`) state the same
  set. The pin publishes both and the port declares both: the audit credits the row's last name only
  from a declaration that carries it, and the 18-declaration count is the pin's 9 + 7 + 1 + 1.

  **Premises (FR-0229, measured).** `premise_imports.py --nodes <all four rows> --missing-from <this
  module> --olean` prints `# nothing to add`: all four rows are leaves with no graph premises.

  spec-pin: P2M/Sol/S_AutomorphicForm_WindowedSiegel_isCompact_centreCutSiegelSet_inter_heightCap.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_coversModCentre_of_le_of_lt_of_coversModCentre.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_iUnion_centreCutSiegelSet_mem_nhds.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSet
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.ProductionPins
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.Siegel.Covering

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric NumberField NumberField.AdelicHaar NumberField.AdelicLevel
  IsDedekindDomain NumberField.AdelicVolume NumberField.AdelicCentre
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped Classical ENNReal NNReal BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicForm

namespace WindowedSiegel

section GenericBox

variable {K : Type*} [NormedField K]

theorem topNormSq_le_of_box {g : GL (Fin 2) K} {c u d₂ C : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ≤ d₂) :
    topNormSq (g : Matrix (Fin 2) (Fin 2) K) ≤ d₂ / c * (u ^ 2 + C ^ 2) := by
  have hrow := rowNormSq_pos g
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet

  have htop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      = rowNormSq (g : Matrix (Fin 2) (Fin 2) K) * (xWindowSq g + localHeight g ^ 2) := by
    unfold xWindowSq
    field_simp
    ring
  rw [htop]
  have hlh0 : 0 ≤ localHeight g := le_trans hc.le hlh
  have hxlh : xWindowSq g + localHeight g ^ 2 ≤ u ^ 2 + C ^ 2 := by
    have : localHeight g ^ 2 ≤ C ^ 2 := by nlinarith [hlh0, hcap]
    linarith
  have hxlh0 : 0 ≤ xWindowSq g + localHeight g ^ 2 := by
    have h1 : 0 ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
      unfold topNormSq; positivity
    nlinarith [htop, hrow]
  have hd20 : 0 ≤ d₂ / c := hrow.le.trans hrowle
  exact mul_le_mul hrowle hxlh hxlh0 hd20

theorem entry_norm_le_of_box {g : GL (Fin 2) K} {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖(g : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
  have hrowle := rowNormSq_le_of_clauses hc hlh hdet.2
  have htople := topNormSq_le_of_box hc hlh hcap hxw hdet.2
  have hd₂0 : 0 ≤ d₂ / c := div_nonneg (le_trans (norm_nonneg _) hdet.2) hc.le
  have h00 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖]
  have h01 : ‖(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ^ 2
      ≤ topNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold topNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖]
  have h10 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖]
  have h11 : ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
      ≤ rowNormSq (g : Matrix (Fin 2) (Fin 2) K) := by
    unfold rowNormSq
    nlinarith [sq_nonneg ‖(g : Matrix (Fin 2) (Fin 2) K) 1 0‖]
  have hsplit : d₂ / c * (1 + u ^ 2 + C ^ 2)
      = d₂ / c + d₂ / c * (u ^ 2 + C ^ 2) := by ring
  have hterm : 0 ≤ d₂ / c * (u ^ 2 + C ^ 2) :=
    mul_nonneg hd₂0 (by positivity)
  have hRtop : topNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + C ^ 2) := by
    rw [hsplit]
    linarith
  have hRrow : rowNormSq (g : Matrix (Fin 2) (Fin 2) K)
      ≤ d₂ / c * (1 + u ^ 2 + C ^ 2) := by
    rw [hsplit]
    linarith
  refine Real.le_sqrt_of_sq_le ?_
  fin_cases i <;> fin_cases j
  · exact h00.trans hRtop
  · exact h01.trans hRtop
  · exact h10.trans hRrow
  · exact h11.trans hRrow

theorem inv_entry_norm_le_of_box {g : GL (Fin 2) K} {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) (hlh : c ≤ localHeight g) (hcap : localHeight g ≤ C)
    (hxw : xWindowSq g ≤ u ^ 2)
    (hdet : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂) (i j : Fin 2) :
    ‖((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) / d₁ := by
  have hB := entry_norm_le_of_box hc hlh hcap hxw hdet
  have hdet0 : ((g : Matrix (Fin 2) (Fin 2) K)).det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact absurd hdet.1 (not_le.mpr hd₁)

  have hcoe : ((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      = ((g : Matrix (Fin 2) (Fin 2) K))⁻¹ := Matrix.coe_units_inv g
  rw [hcoe, Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, norm_smul, norm_inv]
  have hadj : ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
    rw [Matrix.adjugate_fin_two]
    fin_cases i <;> fin_cases j
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 1 1‖ ≤ _
      exact hB 1 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 0 1‖ ≤ _
      rw [norm_neg]; exact hB 0 1
    · show ‖-(g : Matrix (Fin 2) (Fin 2) K) 1 0‖ ≤ _
      rw [norm_neg]; exact hB 1 0
    · show ‖(g : Matrix (Fin 2) (Fin 2) K) 0 0‖ ≤ _
      exact hB 0 0
  have hdinv : ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ ≤ d₁⁻¹ := by
    rw [← one_div, ← one_div]
    exact one_div_le_one_div_of_le hd₁ hdet.1
  have h0 : (0 : ℝ) ≤ ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ := by positivity
  calc ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖⁻¹ * ‖((g : Matrix (Fin 2) (Fin 2) K)).adjugate i j‖
      ≤ d₁⁻¹ * Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) := by
        exact mul_le_mul hdinv hadj (norm_nonneg _) (by positivity)
    _ = Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) / d₁ := by
        ring

theorem isCompact_glBox [ProperSpace K] {c u d₁ d₂ C : ℝ} (hc : 0 < c)
    (hd₁ : 0 < d₁) :
    IsCompact {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ C) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) with hB_def
  set S : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) B with hS_def
  set S' : Set (Matrix (Fin 2) (Fin 2) K) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      closedBall (0 : K) (B / d₁) with hS'_def
  have hS : IsCompact S :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hS' : IsCompact S' :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hK : IsCompact ((Units.embedProduct (Matrix (Fin 2) (Fin 2) K)) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS'.image MulOpposite.continuous_op))
  have hclosed : IsClosed {g : GL (Fin 2) K |
      (c ≤ localHeight g ∧ localHeight g ≤ C) ∧ xWindowSq g ≤ u ^ 2 ∧
      ‖((g : Matrix (Fin 2) (Fin 2) K)).det‖ ∈ Icc d₁ d₂} := by
    refine IsClosed.inter (IsClosed.inter ?_ ?_) (IsClosed.inter ?_ ?_)
    · exact isClosed_le continuous_const continuous_localHeight
    · exact isClosed_le continuous_localHeight continuous_const
    · exact isClosed_le continuous_xWindowSq continuous_const
    · exact (isClosed_Icc).preimage continuous_det_gl.norm
  refine hK.of_isClosed_subset hclosed ?_
  rintro g ⟨⟨hlh, hcap⟩, hxw, hdet⟩
  have hent := entry_norm_le_of_box hc hlh hcap hxw hdet
  have hinv := inv_entry_norm_le_of_box hc hd₁ hlh hcap hxw hdet
  refine ⟨fun i _ => fun j _ => ?_, ?_⟩
  · rw [mem_closedBall_zero_iff]
    exact hent i j
  · refine ⟨((g⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K), fun i _ => fun j _ => ?_, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact hinv i j

end GenericBox

section Adelic

variable (F : Type) [Field F] [NumberField F]

def boxedBlock (c u d₁ d₂ C : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  centreCutSiegelSet F c u d₁ d₂ ∩
    {g | ∀ w : InfinitePlace F, localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C}

theorem isClosed_boxedBlock (c u d₁ d₂ C : ℝ) : IsClosed (boxedBlock F c u d₁ d₂ C) := by
  refine (isClosed_centreCutSiegelSet c u d₁ d₂).inter ?_
  have hset : {g : AdelicGL2 (𝓞 F) F | ∀ w : InfinitePlace F,
      localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C}
      = ⋂ w : InfinitePlace F, {g : AdelicGL2 (𝓞 F) F |
          localHeight (archComponent F w (glArch (𝓞 F) F g)) ≤ C} := by
    ext g
    simp [Set.mem_iInter]
  rw [hset]
  exact isClosed_iInter fun w =>
    isClosed_le (continuous_localHeight_place w) continuous_const

theorem isCompact_boxedBlock {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (boxedBlock F c u d₁ d₂ C) := by
  classical
  set B := Real.sqrt (d₂ / c * (1 + u ^ 2 + C ^ 2)) with hB_def
  set A : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) B) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA_def
  set A' : Set (AdeleRing (𝓞 F) F) :=
    (Set.pi Set.univ fun w : InfinitePlace F =>
      Metric.closedBall (0 : w.Completion) (B / d₁)) ×ˢ
      integralFiniteAdeles (𝓞 F) F with hA'_def
  have hApi : IsCompact A := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    have := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  have hA'pi : IsCompact A' := by
    refine IsCompact.prod (isCompact_univ_pi fun w => ?_)
      (isCompact_integralFiniteAdeles (𝓞 F) F)
    have := properSpace_completion (F := F) w
    exact isCompact_closedBall _ _
  set S : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A with hS_def
  set S' : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :=
    Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => A' with hS'_def
  have hS : IsCompact S := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hApi
  have hS' : IsCompact S' := isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hA'pi
  have hK : IsCompact ((Units.embedProduct
      (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ⁻¹'
      (S ×ˢ (MulOpposite.op '' S'))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage
      (hS.prod (hS'.image MulOpposite.continuous_op))
  refine hK.of_isClosed_subset (isClosed_boxedBlock F c u d₁ d₂ C) ?_
  rintro g ⟨⟨hKf, hfloor, hwin, hdet⟩, hcap⟩
  have hKf2 := mem_finiteIntegralGL2_iff.mp hKf

  have harch : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(archComponent F w (glArch (𝓞 F) F g) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B := fun w i j =>
    entry_norm_le_of_box hc (hfloor w) (hcap w) (hwin w) (hdet w) i j
  have harch' : ∀ (w : InfinitePlace F) (i j : Fin 2),
      ‖(((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
          Matrix (Fin 2) (Fin 2) w.Completion) i j‖ ≤ B / d₁ := fun w i j =>
    inv_entry_norm_le_of_box hc hd₁ (hfloor w) (hcap w) (hwin w) (hdet w) i j
  constructor
  ·
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B
      have hbridge : ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (archComponent F w (glArch (𝓞 F) F g) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
      rw [hbridge]
      exact harch w i j
    · exact hKf2.1 i j
  ·
    refine ⟨((g⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)),
      ?_, rfl⟩
    intro i _ j _
    constructor
    · intro w _
      rw [mem_closedBall_zero_iff]
      show ‖(((g⁻¹ : AdelicGL2 (𝓞 F) F) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w‖ ≤ B / d₁
      have hbridge : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
            Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
          = (((archComponent F w (glArch (𝓞 F) F g))⁻¹ : GL (Fin 2) w.Completion) :
              Matrix (Fin 2) (Fin 2) w.Completion) i j := by
        have h1 : (((g⁻¹ : AdelicGL2 (𝓞 F) F) :
              Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 w
            = (archComponent F w (glArch (𝓞 F) F (g⁻¹ : AdelicGL2 (𝓞 F) F)) :
                Matrix (Fin 2) (Fin 2) w.Completion) i j := rfl
        rw [h1, map_inv (glArch (𝓞 F) F), map_inv (archComponent F w)]
      rw [hbridge]
      exact harch' w i j
    · exact hKf2.2 i j

end Adelic

theorem isCompact_centreCutSiegelSet_inter_heightCap_impl (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) :=
  isCompact_boxedBlock F hc hd₁

end WindowedSiegel

namespace DetBand

variable {K : Type} [Field K] [NumberField K]

omit [NumberField K] in
theorem exists_unit_norm_eq (w : InfinitePlace K) {t : ℝ} (ht : 0 < t) :
    ∃ a : (w.Completion)ˣ, ‖(a : w.Completion)‖ = t := by
  rcases w.isReal_or_isComplex with hw | hw
  · set a₀ : w.Completion := (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm t with ha₀
    have hna : ‖a₀‖ = t := by
      have h1 := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
        (map_zero _) a₀
      rw [← h1, ← InfinitePlace.Completion.ringEquivRealOfIsReal_apply hw, ha₀,
        RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos ht]
    have hpos : 0 < ‖a₀‖ := by rw [hna]; exact ht
    exact ⟨Units.mk0 a₀ (norm_pos_iff.mp hpos), by rw [Units.val_mk0]; exact hna⟩
  · set a₀ : w.Completion := (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm (t : ℂ) with ha₀
    have hna : ‖a₀‖ = t := by
      have h1 := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
        (map_zero _) a₀
      rw [← h1, ← InfinitePlace.Completion.ringEquivComplexOfIsComplex_apply hw, ha₀,
        RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have hpos : 0 < ‖a₀‖ := by rw [hna]; exact ht
    exact ⟨Units.mk0 a₀ (norm_pos_iff.mp hpos), by rw [Units.val_mk0]; exact hna⟩

theorem archComponent_acu_of_ne (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace K} (hw : w ≠ w₀) :
    archComponent K w (glArch (𝓞 K) K (centralScalar (𝓞 K) K (archCentralUnit K w₀ a))) = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_one, Matrix.one_apply]
  simp only [archComponent_apply, glArch_apply]
  split_ifs with h
  · subst h
    rw [centralScalar_apply_eq]
    exact archCentralUnit_fst_of_ne w₀ a hw
  · rw [centralScalar_apply_ne _ h]
    rfl

theorem archDetNorm_acu_of_ne (w₀ : InfinitePlace K) (a : (w₀.Completion)ˣ)
    {w : InfinitePlace K} (hw : w ≠ w₀) (X : AdelicGL2 (𝓞 K) K) :
    archDetNorm w (centralScalar (𝓞 K) K (archCentralUnit K w₀ a) * X) = archDetNorm w X := by
  unfold archDetNorm
  rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]

theorem exists_central_adjust {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (h : AdelicGL2 (𝓞 K) K) (hh : h ∈ centreCutSiegelSet K c u d₁ d₂) (S : Finset (InfinitePlace K)) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, centralScalar (𝓞 K) K z * h ∈ centreCutSiegelSet K c u d₁ d₂ ∧
      ∀ w ∈ S, archDetNorm w (centralScalar (𝓞 K) K z * h) ∈ Set.Icc d₁' d₂ := by
  classical
  refine Finset.induction_on S ⟨1, by rw [map_one, one_mul]; exact hh, fun w hw => absurd hw (by simp)⟩ ?_
  intro w₀ S hw₀S ih
  obtain ⟨z, hzW, hzS⟩ := ih
  set X := centralScalar (𝓞 K) K z * h with hX
  have hN : 0 < archDetNorm w₀ X := archDetNorm_pos w₀ X
  have hd₂ : 0 < d₂ := lt_of_lt_of_le hN ((mem_centreCutSiegelSet_iff.1 hzW).2.2.2 w₀).2
  obtain ⟨a, hna⟩ := exists_unit_norm_eq w₀ (Real.sqrt_pos.2 (div_pos hd₂ hN))
  have hsq : ‖(a : w₀.Completion)‖ * ‖(a : w₀.Completion)‖ * archDetNorm w₀ X = d₂ := by
    rw [hna, Real.mul_self_sqrt (div_pos hd₂ hN).le, div_mul_cancel₀ _ hN.ne']
  have hprod : centralScalar (𝓞 K) K (archCentralUnit K w₀ a * z) * h
      = centralScalar (𝓞 K) K (archCentralUnit K w₀ a) * X := by
    rw [map_mul, mul_assoc]
  have h00 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 0 0
  have h01 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 0 1
  have h10 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 1 0
  have h11 := archComponent_centralScalar_archCentralUnit_apply (F := K) w₀ a 1 1
  rw [ite_eq_left rfl] at h00 h11
  rw [ite_eq_right (by decide)] at h01 h10
  refine ⟨archCentralUnit K w₀ a * z, ?_, ?_⟩
  · rw [hprod, mem_centreCutSiegelSet_iff]
    obtain ⟨hfin, hht, hxw, hdet⟩ := mem_centreCutSiegelSet_iff.1 hzW
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_mul, glFin_centralScalar_archCentralUnit, one_mul]; exact hfin
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [map_mul, map_mul, localHeight_scalar_entries_mul a.ne_zero h00 h01 h10 h11]
        exact hht w
      · rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]; exact hht w
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [map_mul, map_mul, xWindowSq_scalar_entries_mul a.ne_zero h00 h01 h10 h11]
        exact hxw w
      · rw [map_mul, map_mul, archComponent_acu_of_ne w₀ a hw, one_mul]; exact hxw w
    · intro w
      by_cases hw : w = w₀
      · subst hw
        rw [archDetNorm_centralScalar_mul, hsq]
        exact ⟨hle.trans hlt.le, le_rfl⟩
      · rw [archDetNorm_acu_of_ne w₀ a hw]; exact hdet w
  · intro w hw
    rw [hprod]
    rcases Finset.mem_insert.1 hw with rfl | hwS
    · rw [archDetNorm_centralScalar_mul, hsq]
      exact ⟨hlt.le, le_rfl⟩
    · have hne : w ≠ w₀ := fun e => hw₀S (e ▸ hwS)
      rw [archDetNorm_acu_of_ne w₀ a hne]
      exact hzS w hwS

theorem window_mono {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') :
    centreCutSiegelSet K c u d₁' d₂ ⊆ centreCutSiegelSet K c u d₁ d₂ := fun g hg => by
  rw [mem_centreCutSiegelSet_iff] at hg ⊢
  exact ⟨hg.1, hg.2.1, hg.2.2.1, fun w => Set.Icc_subset_Icc hle le_rfl (hg.2.2.2 w)⟩

theorem covers_narrow {c u d₁ d₂ d₁' : ℝ} (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (T : Finset (AdelicGL2 (𝓞 K) K))
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)) :
    CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁' d₂) := by
  intro g
  obtain ⟨γ, z₀, hmem⟩ := hcov g
  obtain ⟨x, hx, h, hh, hhx⟩ := Set.mem_iUnion₂.1 hmem
  obtain ⟨z₁, hz₁W, hz₁S⟩ := exists_central_adjust hle hlt h hh Finset.univ
  have hnarrow : centralScalar (𝓞 K) K z₁ * h ∈ centreCutSiegelSet K c u d₁' d₂ := by
    rw [mem_centreCutSiegelSet_iff]
    obtain ⟨hfin, hht, hxw, _⟩ := mem_centreCutSiegelSet_iff.1 hz₁W
    exact ⟨hfin, hht, hxw, fun w => hz₁S w (Finset.mem_univ w)⟩
  refine ⟨γ, z₀ * z₁, Set.mem_iUnion₂.2 ⟨x, hx, centralScalar (𝓞 K) K z₁ * h, hnarrow, ?_⟩⟩
  show centralScalar (𝓞 K) K z₁ * h * x = _
  have hhx' : h * x = globalPoints (𝓞 K) K γ * g * centralScalar (𝓞 K) K z₀ := hhx
  rw [map_mul, mul_assoc, hhx', ← SiegelCovering.mul_centralScalar_comm]
  group

end DetBand

/-- **Compactness of a capped window.** The centre-cut Siegel set inside a height cap is compact. -/
theorem WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap (F : Type) [Field F]
    [NumberField F] {c u d₁ d₂ C : ℝ} (hc : 0 < c) (hd₁ : 0 < d₁) :
    IsCompact (AutomorphicForm.WindowedSiegel.centreCutSiegelSet F c u d₁ d₂ ∩
      {g | ∀ w : NumberField.InfinitePlace F,
        AutomorphicForm.WindowedSiegel.localHeight (NumberField.AdelicLevel.archComponent F w
          (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers F) F g)) ≤ C}) :=
  WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap_impl F hc hd₁

/-- **Monotone windows.** A cover of the centre-cut Siegel set at one window covers at every larger window. -/
theorem coversModCentre_of_le_of_lt_of_coversModCentre
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ d₁' : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hle : d₁ ≤ d₁') (hlt : d₁' < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)) :
    CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁' d₂) :=
  DetBand.covers_narrow hle hlt T hcov

/-- **The windows exhaust the identity.** The union of the centre-cut Siegel sets is a neighbourhood of
the identity. -/
theorem exists_iUnion_centreCutSiegelSet_mem_nhds (F : Type) [Field F] [NumberField F] (g : AdelicGL2 (𝓞 F) F) :
    ∃ (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)), 0 < c ∧ 0 < d₁ ∧
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) ∈ 𝓝 g := by
  classical
  refine ⟨1 / 2, 1, 1 / 2, 2, {g}, by norm_num, by norm_num, ?_⟩
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ interior (centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) :=
    one_mem_interior_centreCutSiegelSet (by norm_num) one_ne_zero (by norm_num) (by norm_num)
  have hW : (⋃ x ∈ ({g} : Finset (AdelicGL2 (𝓞 F) F)), (· * x) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2) =
      (· * g) '' centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 := by
    ext h
    simp only [Finset.mem_singleton, Set.mem_iUnion, exists_prop, exists_eq_left]
  rw [hW]
  have hn : centreCutSiegelSet F (1 / 2) 1 (1 / 2) 2 ∈ 𝓝 (1 : AdelicGL2 (𝓞 F) F) := mem_interior_iff_mem_nhds.mp h1
  have him := (Homeomorph.mulRight g).isOpenMap.image_mem_nhds hn
  rw [Homeomorph.coe_mulRight] at him
  simpa only [one_mul] using him

/-- **Vanishing from a cover.** An `L`-function that vanishes on a set covering the group modulo the
centre vanishes. -/
theorem eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero
    (F : Type) [Field F] [NumberField F]
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsLsXiFunction (𝓞 F) F ⊤ ξ φ)
    (W : Set (AdelicGL2 (𝓞 F) F)) (hcov : CoversModCentre F W)
    (h0 : ∀ x ∈ W, φ x = 0) : φ = 0 := by
  funext g
  obtain ⟨γ, z, hmem⟩ := hcov g
  have h1 : φ (globalPoints (𝓞 F) F γ * g * centralScalar (𝓞 F) F z) = 0 := h0 _ hmem
  have h2 : φ (centralScalar (𝓞 F) F z * (globalPoints (𝓞 F) F γ * g)) =
      ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * φ (globalPoints (𝓞 F) F γ * g) :=
    hφ.central_transform ⟨z, Subgroup.mem_top z⟩ _
  rw [SiegelCovering.mul_centralScalar_comm, h2, hφ.left_invariant] at h1
  exact (mul_eq_zero.mp h1).resolve_left (Units.ne_zero _)

end AutomorphicForm
