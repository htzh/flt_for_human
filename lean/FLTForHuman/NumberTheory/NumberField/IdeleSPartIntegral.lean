/-
  The `S`-part measure of the idèles and its product integrals.

  Five rows: the two product formulas for `lintegral`s against the `S`-part measure, the positivity of
  that measure on a set with a nonempty slice, and the two approximation statements for the finite
  adèles (each place separately, and simultaneously).

  The pins are *flattened* files whose declarations are all public (28 + 39 + 3 + 13 + 9); their subject
  namespaces are search-stage labels and are renamed here.

  * the `S`-part integral (`NumberField.Idele.SPartIntegral`, pin 1): the unit-component algebra of
    `partAt`/`unitPart`, the `uniformizerIdele` coset decomposition of `unitIdelesOutside`, and the two
    rewrites carrying `sPartMeasure F S` to `sPartMeasure F ∅` times a product of local `tsum`s;
  * the archimedean product formula (`NumberField.Idele.NormProduct`, pin 2): a product of local factors
    integrates against `sPartMeasure F ∅` as the additive Haar measure `muLog` on `InfinitePlace F → ℝ`;
  * the positivity slice (`NumberField.Idele.PartAt`, pin 5): an idèle that is a unit outside `S` is
    fixed by `partAt F S`;
  * the approximation engine (`IsDedekindDomain.FiniteAdeleRing.Approx`, pin 4, and its `s2_` copy under
    `…FiniteAdeleRing.HeightOneSpectrum`, pin 3): a finite adèle differs from a global element by
    something integral at every finite place.

  Premise closure (FR-0229): the five rows have **no graph premises beyond `IdeleProductMeasure`**, which
  is imported. The proof also wants `Mathlib.MeasureTheory.Function.JacobianOneDim`
  (`lintegral_image_eq_lintegral_abs_deriv_mul`, for `lintegral_comp_exp`), which is *not* a premise of
  any row and is imported below for that reason.

  Heartbeat probe (gate 6 of the order, recorded here and **not installed** — FR-0225): the module is
  silent at `-DmaxHeartbeats=13000`; the first offender appears at 10 000, an `isDefEq` timeout inside
  `SPartIntegral.setLIntegral_eq_lintegral_sPartMeasure_mul_prod` (the `iUnion`-decomposition rewrite
  chain). So the natural per-declaration cost is under 13 k, ~6 % of the 200 k edit-loop cap, and no
  `set_option maxHeartbeats` appears anywhere below.

  Dedup (gate 4): `dedup.py --within --module IdeleSPartIntegral` reports 7 shape clusters, and every one
  of them is a pair the *pin* publishes twice, so the wire requires both copies (FR-0226: one port
  declaration per wire public) — the `s2_` engine of the `forall` pin against the `Approx` engine of its
  twin (`exists_ofAdd_natCast_of_le_one`, `exists_ofAdd_natCast_lt`,
  `exists_nonZeroDivisor_smul_mem_adicCompletionIntegers`, `exists_sub_algebraMap_mem_adicCompletionIntegers`,
  `exists_forall_adicValued_sub_lt`), the `_impl`/two-`solution` triple of one statement, and
  `NormProduct.main` against row B2 (the pin's `solution` folds onto its own engine). Nothing is dead:
  `move_dead.py --dry-run` reads `0 declarations, 0 lines`.

  Names: the pins' machine-generated stage labels are renamed to subject namespaces —
  `S37E41` → `SPartIntegral`, `C5P3` → `NormProduct`, `RS40LMb` → `PartAt`, `M4aP1R` → the row namespace
  with `Approx` kept, and the `forall` pin's `p2m`-copied `IsDedekindDomain.HeightOneSpectrum` →
  `…FiniteAdeleRing.HeightOneSpectrum`. Every *declaration* keeps the pin's last name, `s2_` prefixes
  included (the checker's stage-label tier strips only `_s0`…`_s19` suffixes).

  spec-pin: P2M/Sol/S_NumberField_Idele_lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum.lean
  spec-pin: P2M/Sol/S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral.lean
  spec-pin: P2M/Sol/S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq.lean
  spec-pin: P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_forall_sub_algebraMap_mem_adicCompletionIntegers.lean
  spec-pin: P2M/Sol/S_IsDedekindDomain_FiniteAdeleRing_exists_sub_algebraMap_mem_adicCompletionIntegers.lean
-/
import FLTForHuman.NumberTheory.NumberField.IdeleProductMeasure
import FLTForHuman.NumberTheory.NumberField.FiniteIdeles
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.NumberField.UnitIdelesOutside
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicLevel.IdealBall
import Mathlib.MeasureTheory.Function.JacobianOneDim

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain NumberField.AdeleRing
open scoped Classical ENNReal NNReal BigOperators WithZero

namespace NumberField.Idele

/-! ### The component algebra of the idèles, and the `S`-part integral

Transcribed from `S37E41` of the `S_NumberField_Idele_lintegral_mul_prod_ord_…` pin (the pipeline's
stage label, renamed here to `SPartIntegral`): the unit-component API of `partAt`/`unitPart`, the order
`ord`, the `uniformizerIdele` coset decomposition of `unitIdelesOutside`, and the two rewrites that
carry `sPartMeasure F S` to `sPartMeasure F ∅` times a product of local `tsum`s. -/
namespace SPartIntegral

section Components

variable (F : Type) [Field F] [NumberField F]

theorem idele_ext {a b : (AdeleRing (𝓞 F) F)ˣ}
    (h₁ : ∀ w : InfinitePlace F, infiniteUnitsComponent (𝓞 F) F w a = infiniteUnitsComponent (𝓞 F) F w b)
    (h₂ : ∀ w : HeightOneSpectrum (𝓞 F), finiteUnitsComponent (𝓞 F) F w a = finiteUnitsComponent (𝓞 F) F w b) :
    a = b :=
  Units.ext (Prod.ext (funext fun w => congrArg Units.val (h₁ w))
    (Subtype.ext (funext fun w => congrArg Units.val (h₂ w))))

theorem iUC_partAt (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (w : InfinitePlace F) : infiniteUnitsComponent (𝓞 F) F w (partAt F S a) = infiniteUnitsComponent (𝓞 F) F w a :=
  Units.ext rfl

theorem iUC_unitPart (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    (w : InfinitePlace F) : infiniteUnitsComponent (𝓞 F) F w (unitPart F S a) = 1 :=
  Units.ext rfl

theorem iUC_uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) :
    infiniteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F v) = 1 :=
  Units.ext rfl

theorem fUC_partAt_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) :
    finiteUnitsComponent (𝓞 F) F w (partAt F S a) = finiteUnitsComponent (𝓞 F) F w a :=
  Units.ext (ite_eq_left hw)

theorem fUC_partAt_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) : finiteUnitsComponent (𝓞 F) F w (partAt F S a) = 1 :=
  Units.ext (ite_eq_right hw)

theorem fUC_unitPart_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∈ S) : finiteUnitsComponent (𝓞 F) F w (unitPart F S a) = 1 :=
  Units.ext (ite_eq_left hw)

theorem val_fUC_unitPart_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {w : HeightOneSpectrum (𝓞 F)} (hw : w ∉ S) :
    ((finiteUnitsComponent (𝓞 F) F w (unitPart F S a) : (w.adicCompletion F)ˣ) : w.adicCompletion F) =
      (a : AdeleRing (𝓞 F) F).2 w * (uniformizerUnit F w : w.adicCompletion F) ^ (-(ord F w a)) :=
  ite_eq_right hw

theorem fUC_uniformizerIdele_self (w : HeightOneSpectrum (𝓞 F)) :
    finiteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F w) = uniformizerUnit F w :=
  Units.ext (by
    show ((localUnit (𝓞 F) F w (uniformizerUnit F w) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = _
    rw [localUnit_apply_self])

theorem fUC_uniformizerIdele_of_ne {v w : HeightOneSpectrum (𝓞 F)} (h : w ≠ v) :
    finiteUnitsComponent (𝓞 F) F w (AutomorphicForm.uniformizerIdele F v) = 1 :=
  Units.ext (by
    show ((localUnit (𝓞 F) F v (uniformizerUnit F v) : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) w = 1
    rw [localUnit_apply_of_ne (𝓞 F) F v (uniformizerUnit F v) h])

def ordHom (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (ord F v a)
  map_one' := by rw [ord_one]; rfl
  map_mul' a b := by rw [ord_mul]; rfl

theorem ord_zpow (v : HeightOneSpectrum (𝓞 F)) (a : (AdeleRing (𝓞 F) F)ˣ) (n : ℤ) :
    ord F v (a ^ n) = n * ord F v a := by
  have h : Multiplicative.ofAdd (ord F v (a ^ n)) = Multiplicative.ofAdd (ord F v a) ^ n :=
    map_zpow (ordHom F v) a n
  rw [← ofAdd_zsmul] at h
  rw [Multiplicative.ofAdd.injective h, smul_eq_mul]

theorem fUC_partAt_uniformizerIdele (S : Finset (HeightOneSpectrum (𝓞 F))) {v : HeightOneSpectrum (𝓞 F)}
    (hv : v ∉ S) (w : HeightOneSpectrum (𝓞 F)) :
    finiteUnitsComponent (𝓞 F) F w (partAt F S (AutomorphicForm.uniformizerIdele F v)) = 1 := by
  by_cases hw : w ∈ S
  · rw [fUC_partAt_of_mem F S _ hw]
    exact fUC_uniformizerIdele_of_ne F fun h => hv (h ▸ hw)
  · exact fUC_partAt_of_not_mem F S _ hw

theorem partAt_uniformizerIdele_of_not_mem (S : Finset (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : partAt F S (AutomorphicForm.uniformizerIdele F v) = 1 := by
  refine idele_ext F (fun w => ?_) (fun w => ?_)
  · rw [iUC_partAt, iUC_uniformizerIdele, map_one]
  · rw [fUC_partAt_uniformizerIdele F S hv, map_one]

theorem mem_unitIdelesOutside_iff_ord (T : Set (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T ↔ ∀ w, w ∉ T → ord F w a = 0 := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  refine forall_congr' fun w => imp_congr_right fun _ => ?_
  rw [ord_eq_zero_iff]
  rfl

theorem mem_image_uniformizerIdele_zpow_mul_iff (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') (n : ℤ) (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ) ↔
      a ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) ∧
        ord F v a = n := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
    refine ⟨?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      rw [Set.mem_insert_iff, not_or] at hw
      rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hw.1, mul_zero, zero_add, hb w hw.2]
    · rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv, add_zero]
  · rintro ⟨ha, hn⟩
    rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at ha
    refine ⟨AutomorphicForm.uniformizerIdele F v ^ (-n) * a, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord]
      intro w hw
      by_cases hwv : w = v
      · rw [hwv, ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hn, neg_add_cancel]
      · rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
        exact ha w fun h => (Set.mem_insert_iff.mp h).elim hwv hw
    · show AutomorphicForm.uniformizerIdele F v ^ n * (AutomorphicForm.uniformizerIdele F v ^ (-n) * a) = a
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]

theorem iUnion_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    (⋃ n : ℤ, (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) =
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (insert v T') : Set (AdeleRing (𝓞 F) F)ˣ) := by
  ext a
  rw [Set.mem_iUnion]
  constructor
  · rintro ⟨n, h⟩
    exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp h).1
  · intro h
    exact ⟨ord F v a, (mem_image_uniformizerIdele_zpow_mul_iff F T' hv _ a).mpr ⟨h, rfl⟩⟩

theorem pairwise_disjoint_image_uniformizerIdele_zpow_mul (T' : Set (HeightOneSpectrum (𝓞 F)))
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ T') :
    Pairwise (Function.onFun Disjoint fun n : ℤ =>
      (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F T' : Set (AdeleRing (𝓞 F) F)ˣ)) := by
  intro m n hmn
  refine Set.disjoint_left.mpr fun a ham han => hmn ?_
  exact ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv m a).mp ham).2.symm.trans
    ((mem_image_uniformizerIdele_zpow_mul_iff F T' hv n a).mp han).2

end Components

/-! The integral itself: measurability of `ord` and of the local product, the translation identity on the
`uniformizerIdele`-cosets, and the two rewrites that carry the `S`-part measure to the Haar measure of the
unit idèles. -/
section Integral

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem isOpen_setOf_valued_le (w : HeightOneSpectrum (𝓞 F)) (m : ℤ) :
    IsOpen {x : w.adicCompletion F | Valued.v x ≤ WithZero.exp (-m)} := by
  set u : w.adicCompletion F := ((uniformizerUnit F w ^ (-m) : (w.adicCompletion F)ˣ) : w.adicCompletion F)
    with hudef
  have hvu : Valued.v u = WithZero.exp m := by
    rw [hudef, Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
    congr 1
    simp
  have hset : {x : w.adicCompletion F | Valued.v x ≤ WithZero.exp (-m)} =
      (fun x => u * x) ⁻¹' ((w.adicCompletionIntegers F : ValuationSubring (w.adicCompletion F)) :
        Set (w.adicCompletion F)) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, SetLike.mem_coe,
      HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hvu]
    constructor
    · intro h
      calc WithZero.exp m * Valued.v x ≤ WithZero.exp m * WithZero.exp (-m) := mul_le_mul_right h _
        _ = 1 := by rw [← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero]
    · intro h
      calc Valued.v x = WithZero.exp (-m) * (WithZero.exp m * Valued.v x) := by
            rw [← mul_assoc, ← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero, one_mul]
        _ ≤ WithZero.exp (-m) * 1 := mul_le_mul_right h _
        _ = WithZero.exp (-m) := mul_one _
  rw [hset]
  exact (Valued.isOpen_valuationSubring _).preimage (continuous_const_mul u)

theorem measurable_ord (w : HeightOneSpectrum (𝓞 F)) : Measurable (ord F w) := by
  refine measurable_to_countable' fun m => ?_
  have hcont : Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2 w :=
    (RestrictedProduct.continuous_eval w).comp (continuous_snd.comp Units.continuous_val)
  have hset : ord F w ⁻¹' {m} =
      (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2 w) ⁻¹'
          {x | Valued.v x ≤ WithZero.exp (-m)} \
        (fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).2 w) ⁻¹'
          {x | Valued.v x ≤ WithZero.exp (-(m + 1))} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
    rw [valued_snd_eq_exp_neg_ord, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega
  rw [hset]
  exact (((isOpen_setOf_valued_le F w m).preimage hcont).measurableSet).diff
    (((isOpen_setOf_valued_le F w (m + 1)).preimage hcont).measurableSet)

theorem measurable_prodOrd (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) (L : List (HeightOneSpectrum (𝓞 F))) :
    Measurable fun a : (AdeleRing (𝓞 F) F)ˣ => (L.map fun w => φ w (ord F w a)).prod := by
  induction L with
  | nil => simp
  | cons v L' IH =>
    simp only [List.map_cons, List.prod_cons]
    exact ((measurable_from_top (f := φ v)).comp (measurable_ord F v)).mul IH

theorem key_translate (S : Finset (HeightOneSpectrum (𝓞 F))) (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) (v : HeightOneSpectrum (𝓞 F)) (L' : List (HeightOneSpectrum (𝓞 F)))
    (hvS : v ∉ S) (hvL' : v ∉ L') (n : ℤ) (b : (AdeleRing (𝓞 F) F)ˣ)
    (hb : b ∈ (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)) :
    f (partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b)) *
        ((v :: L').map fun w => φ w (ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b))).prod =
      φ v n * (f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod) := by
  have hv' : v ∉ (↑S ∪ {w | w ∈ L'} : Set (HeightOneSpectrum (𝓞 F))) := by
    rintro (h | h)
    · exact hvS (Finset.mem_coe.mp h)
    · exact hvL' h
  rw [SetLike.mem_coe, mem_unitIdelesOutside_iff_ord] at hb
  have h1 : partAt F S (AutomorphicForm.uniformizerIdele F v ^ n * b) = partAt F S b := by
    rw [map_mul, map_zpow, partAt_uniformizerIdele_of_not_mem F S hvS, one_zpow, one_mul]
  have h2 : ord F v (AutomorphicForm.uniformizerIdele F v ^ n * b) = n := by
    rw [ord_mul, ord_zpow, ord_uniformizerIdele_self, mul_one, hb v hv', add_zero]
  have h3 : ∀ w ∈ L', ord F w (AutomorphicForm.uniformizerIdele F v ^ n * b) = ord F w b := by
    intro w hw
    have hwv : w ≠ v := fun h => hvL' (h ▸ hw)
    rw [ord_mul, ord_zpow, ord_uniformizerIdele_of_ne F hwv, mul_zero, zero_add]
  rw [h1, List.map_cons, List.prod_cons, h2, List.map_congr_left (fun w hw => by rw [h3 w hw])]
  ring

theorem setLIntegral_eq_lintegral_sPartMeasure_mul_prod (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable f) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    ∀ (L : List (HeightOneSpectrum (𝓞 F))), (∀ v ∈ L, v ∉ S) → L.Nodup →
      (∫⁻ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {v | v ∈ L}) : Set (AdeleRing (𝓞 F) F)ˣ),
          f (partAt F S a) * (L.map fun v => φ v (ord F v a)).prod ∂(idelicHaar F)) =
        (∫⁻ a, f a ∂(sPartMeasure F S)) * (L.map fun v => ∑' m : ℤ, φ v m).prod := by
  intro L
  induction L with
  | nil =>
    intro _ _
    have hT : (↑S ∪ {v | v ∈ ([] : List (HeightOneSpectrum (𝓞 F)))} : Set (HeightOneSpectrum (𝓞 F))) = ↑S := by
      ext w
      simp only [Set.mem_union, Set.mem_ofPred_eq, List.not_mem_nil, or_false]
    simp only [List.map_nil, List.prod_nil, mul_one, hT]
    rw [sPartMeasure, lintegral_map hf (measurable_partAt F S)]
  | cons v L' IH =>
    intro hLS hL
    have hvS : v ∉ S := hLS v (List.mem_cons.mpr (Or.inl rfl))
    have hLS' : ∀ w ∈ L', w ∉ S := fun w hw => hLS w (List.mem_cons.mpr (Or.inr hw))
    have hvL' : v ∉ L' := (List.nodup_cons.mp hL).1
    have hL' : L'.Nodup := (List.nodup_cons.mp hL).2
    have IHe := IH hLS' hL'
    have hv' : v ∉ (↑S ∪ {w | w ∈ L'} : Set (HeightOneSpectrum (𝓞 F))) := by
      rintro (h | h)
      · exact hvS (Finset.mem_coe.mp h)
      · exact hvL' h
    have hset : (↑S ∪ {w | w ∈ v :: L'} : Set (HeightOneSpectrum (𝓞 F))) = insert v (↑S ∪ {w | w ∈ L'}) := by
      ext w
      simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, List.mem_cons, Set.mem_insert_iff]
      tauto
    rw [hset, ← iUnion_image_uniformizerIdele_zpow_mul F _ hv']
    have hme : ∀ n : ℤ, MeasurableEmbedding
        (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) := fun n =>
      (Homeomorph.mulLeft (AutomorphicForm.uniformizerIdele F v ^ n)).measurableEmbedding
    have hmp : ∀ n : ℤ, MeasurePreserving
        (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) (idelicHaar F) (idelicHaar F) :=
      fun n => measurePreserving_mul_left (idelicHaar F) _
    have hU' : MeasurableSet
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ) :=
      (isOpen_unitIdelesOutside F _).measurableSet
    have hmeas : ∀ n : ℤ, MeasurableSet ((fun b : (AdeleRing (𝓞 F) F)ˣ =>
        AutomorphicForm.uniformizerIdele F v ^ n * b) ''
        (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      fun n => (hme n).measurableSet_image.mpr hU'
    rw [lintegral_iUnion hmeas (pairwise_disjoint_image_uniformizerIdele_zpow_mul F _ hv')]
    have hGm : AEMeasurable (fun b => f (partAt F S b) * (L'.map fun w => φ w (ord F w b)).prod)
        ((idelicHaar F).restrict
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ)) :=
      ((hf.comp (measurable_partAt F S)).mul (measurable_prodOrd F φ L')).aemeasurable
    have hval : ∀ n : ℤ, (∫⁻ a in (fun b : (AdeleRing (𝓞 F) F)ˣ => AutomorphicForm.uniformizerIdele F v ^ n * b) ''
          (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S ∪ {w | w ∈ L'}) : Set (AdeleRing (𝓞 F) F)ˣ),
          f (partAt F S a) * ((v :: L').map fun w => φ w (ord F w a)).prod ∂(idelicHaar F)) =
        φ v n * ((∫⁻ a, f a ∂(sPartMeasure F S)) * (L'.map fun w => ∑' m : ℤ, φ w m).prod) := by
      intro n
      rw [← (hmp n).setLIntegral_comp_emb (hme n), ← IHe, ← lintegral_const_mul'' _ hGm]
      exact setLIntegral_congr_fun hU' (fun b hb => key_translate F S f φ v L' hvS hvL' n b hb)
    simp_rw [hval]
    rw [ENNReal.tsum_mul_right, List.map_cons, List.prod_cons]
    ring

theorem ord_partAt_of_mem (S : Finset (HeightOneSpectrum (𝓞 F))) (a : (AdeleRing (𝓞 F) F)ˣ)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) : ord F v (partAt F S a) = ord F v a := by
  simp only [ord, partAt_snd_of_mem F S a hv]

theorem measurable_mul_prod_ord (S : Finset (HeightOneSpectrum (𝓞 F))) (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞)
    (hf : Measurable f) (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    Measurable fun a : (AdeleRing (𝓞 F) F)ˣ => f a * ∏ v ∈ S, φ v (ord F v a) :=
  hf.mul (Finset.measurable_prod S fun v _ => (measurable_from_top (f := φ v)).comp (measurable_ord F v))

theorem lintegral_sPartMeasure_eq_setLIntegral (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a, f a * ∏ v ∈ S, φ v (ord F v a) ∂(sPartMeasure F S)) =
      ∫⁻ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ),
        f a * ∏ v ∈ S, φ v (ord F v a) ∂(idelicHaar F) := by
  rw [sPartMeasure, lintegral_map (measurable_mul_prod_ord F S f hf φ) (measurable_partAt F S)]
  refine lintegral_congr fun a => ?_
  show f (partAt F S a) * ∏ v ∈ S, φ v (ord F v (partAt F S a)) = f a * ∏ v ∈ S, φ v (ord F v a)
  rw [hf1 (partAt F S a) a (partAt_fst F S a)]
  exact congrArg _ (Finset.prod_congr rfl fun v hv => by rw [ord_partAt_of_mem F S a hv])

theorem setLIntegral_eq_lintegral_sPartMeasure_empty_mul_prod (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a in (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S) : Set (AdeleRing (𝓞 F) F)ˣ),
        f a * ∏ v ∈ S, φ v (ord F v a) ∂(idelicHaar F)) =
      (∫⁻ a, f a ∂(sPartMeasure F ∅)) * ∏ v ∈ S, ∑' m : ℤ, φ v m := by
  have key := setLIntegral_eq_lintegral_sPartMeasure_mul_prod F ∅ f hf φ S.toList
    (fun v _ => by simp) (Finset.nodup_toList S)
  have hT : (↑(∅ : Finset (HeightOneSpectrum (𝓞 F))) ∪ {v | v ∈ S.toList} : Set (HeightOneSpectrum (𝓞 F))) =
      ↑S := by
    ext w
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_ofPred_eq, Finset.mem_toList]
    simp
  have h2 : ∀ a : (AdeleRing (𝓞 F) F)ˣ, f (partAt F ∅ a) = f a := fun a => hf1 _ _ (partAt_fst F ∅ a)
  rw [hT] at key
  simp_rw [h2, Finset.prod_map_toList] at key
  exact key

end Integral

end SPartIntegral
/-! ### The archimedean product formula

Transcribed from the `S_NumberField_Idele_exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral`
pin (stage label `C5P3` → `NormProduct`): a product of archimedean local factors integrates against
`sPartMeasure F ∅` as the additive Haar measure `muLog` on `InfinitePlace F → ℝ`, together with the
`WithZero.log`/`sect`-section machinery that identifies the two. -/
namespace NormProduct

section Generic

open Function in
theorem lmarginal_prod_eq_prod {ι : Type*} [DecidableEq ι] {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i))
    (s : Finset ι) (x : ∀ i, X i) :
    (∫⋯∫⁻_s, (fun y => ∏ i ∈ s, f i (y i)) ∂μ) x = ∏ i ∈ s, ∫⁻ y, f i y ∂μ i := by
  induction s using Finset.induction_on generalizing x with
  | empty => simp [lmarginal_empty]
  | @insert i s hi ih =>
    have hmeas : ∀ t : Finset ι, Measurable fun y : ∀ j, X j => ∏ j ∈ t, f j (y j) := fun t =>
      Finset.measurable_prod _ fun j _ => (hf j).comp (measurable_pi_apply j)
    rw [lmarginal_insert' _ (hmeas _) hi]
    have hinner : (fun y : ∀ j, X j => ∫⁻ xi, ∏ j ∈ insert i s, f j (update y i xi j) ∂μ i)
        = fun y => (∫⁻ xi, f i xi ∂μ i) * ∏ j ∈ s, f j (y j) := by
      funext y
      have hrw : ∀ xi : X i, ∏ j ∈ insert i s, f j (update y i xi j) = f i xi * ∏ j ∈ s, f j (y j) := by
        intro xi
        rw [Finset.prod_insert hi, update_self]
        congr 1
        refine Finset.prod_congr rfl fun j hj => ?_
        have hji : j ≠ i := fun h => hi (h ▸ hj)
        rw [update_of_ne hji]
      simp_rw [hrw]
      rw [lintegral_mul_const _ (hf i)]
    rw [hinner, Finset.prod_insert hi]
    have hconst : (∫⋯∫⁻_s, (fun y => (∫⁻ xi, f i xi ∂μ i) * ∏ j ∈ s, f j (y j)) ∂μ) x
        = (∫⁻ xi, f i xi ∂μ i) * (∫⋯∫⁻_s, (fun y => ∏ j ∈ s, f j (y j)) ∂μ) x := by
      unfold lmarginal
      exact lintegral_const_mul _ ((hmeas s).comp measurable_updateFinset)
    rw [hconst, ih]

theorem lintegral_fintype_prod_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (f : ∀ i, X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (x₀ : ∀ i, X i) :
    ∫⁻ x, ∏ i, f i (x i) ∂Measure.pi μ = ∏ i, ∫⁻ y, f i y ∂μ i := by
  rw [lintegral_eq_lmarginal_univ x₀, lmarginal_prod_eq_prod μ f hf Finset.univ x₀]

theorem lintegral_comp_exp (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g (Real.exp x) = ∫⁻ t in Set.Ioi 0, g t * (ENNReal.ofReal t)⁻¹ := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => g t * (ENNReal.ofReal t)⁻¹)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun x => ?_
  have h0 : ENNReal.ofReal (Real.exp x) ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos x)).ne'
  rw [abs_of_pos (Real.exp_pos x), mul_comm (g _), ← mul_assoc, ENNReal.mul_inv_cancel h0 ENNReal.ofReal_ne_top,
    one_mul]

end Generic

section Completion

open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

variable {F : Type} [Field F]

theorem norm_ringEquivRealOfIsReal {w : InfinitePlace F} (hw : w.IsReal) (x : w.Completion) :
    ‖ringEquivRealOfIsReal hw x‖ = ‖x‖ :=
  (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _) x

theorem norm_ringEquivComplexOfIsComplex {w : InfinitePlace F} (hw : w.IsComplex) (x : w.Completion) :
    ‖ringEquivComplexOfIsComplex hw x‖ = ‖x‖ :=
  (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x

open scoped Classical in

def ofRealAt (w : InfinitePlace F) : ℝ →+* w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm.toRingHom
  else ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm.toRingHom).comp Complex.ofRealHom

theorem norm_ofRealAt (w : InfinitePlace F) (t : ℝ) : ‖ofRealAt w t‖ = |t| := by
  classical
  unfold ofRealAt
  split_ifs with hw
  · have h := norm_ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm t)
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs] at h
    show ‖(ringEquivRealOfIsReal hw).symm t‖ = |t|
    exact h.symm
  · have h := norm_ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)
      ((ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ))
    rw [RingEquiv.apply_symm_apply, Complex.norm_real, Real.norm_eq_abs] at h
    show ‖(ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (t : ℂ)‖ = |t|
    exact h.symm

theorem isCompact_annulus (w : InfinitePlace F) (r R : ℝ) :
    IsCompact {x : w.Completion | ‖x‖ ∈ Set.Icc r R} := by
  have hC : IsCompact {z : ℂ | ‖z‖ ∈ Set.Icc r R} := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.preimage continuous_norm) ?_
    refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset fun z hz => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz.2
  have he : {x : w.Completion | ‖x‖ ∈ Set.Icc r R} = extensionEmbedding w ⁻¹' {z : ℂ | ‖z‖ ∈ Set.Icc r R} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [(isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x]
  rw [he]
  exact (isometry_extensionEmbedding w).isClosedEmbedding.isCompact_preimage hC

end Completion

section Idele

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

theorem fst_apply_ne_zero (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) : (a : AdeleRing (𝓞 F) F).1 w ≠ 0 := by
  intro h0
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  change (a : AdeleRing (𝓞 F) F).1 w * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 at h
  rw [h0, zero_mul] at h
  exact zero_ne_one h

theorem norm_fst_apply_pos (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) : 0 < ‖(a : AdeleRing (𝓞 F) F).1 w‖ :=
  norm_pos_iff.mpr (fst_apply_ne_zero F a w)

theorem fst_apply_inv (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = ((a : AdeleRing (𝓞 F) F).1 w)⁻¹ := by
  have h := congrArg (fun x : AdeleRing (𝓞 F) F => x.1 w) a.mul_inv
  change (a : AdeleRing (𝓞 F) F).1 w * ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w = 1 at h
  exact (eq_inv_of_mul_eq_one_right h)

theorem continuous_fst_apply (w : InfinitePlace F) :
    Continuous fun a : (AdeleRing (𝓞 F) F)ˣ => (a : AdeleRing (𝓞 F) F).1 w :=
  (continuous_apply w).comp (continuous_fst.comp Units.continuous_val)

def logNorms (a : (AdeleRing (𝓞 F) F)ˣ) : InfinitePlace F → ℝ := fun w => Real.log ‖(a : AdeleRing (𝓞 F) F).1 w‖

theorem logNorms_apply (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    logNorms F a w = Real.log ‖(a : AdeleRing (𝓞 F) F).1 w‖ := rfl

theorem exp_logNorms (a : (AdeleRing (𝓞 F) F)ˣ) (w : InfinitePlace F) :
    Real.exp (logNorms F a w) = ‖(a : AdeleRing (𝓞 F) F).1 w‖ :=
  Real.exp_log (norm_fst_apply_pos F a w)

theorem continuous_logNorms : Continuous (logNorms F) :=
  continuous_pi fun w => ((continuous_fst_apply F w).norm).log fun a => (norm_fst_apply_pos F a w).ne'

theorem measurable_logNorms : Measurable (logNorms F) := (continuous_logNorms F).measurable

theorem logNorms_mul (a b : (AdeleRing (𝓞 F) F)ˣ) : logNorms F (a * b) = logNorms F a + logNorms F b := by
  funext w
  change Real.log ‖(a : AdeleRing (𝓞 F) F).1 w * (b : AdeleRing (𝓞 F) F).1 w‖ = _
  rw [norm_mul, Real.log_mul (norm_fst_apply_pos F a w).ne' (norm_fst_apply_pos F b w).ne']
  rfl

def unitSet : Set (AdeleRing (𝓞 F) F)ˣ :=
  (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑(∅ : Finset (HeightOneSpectrum (𝓞 F)))) :
    Set (AdeleRing (𝓞 F) F)ˣ)

theorem mem_unitSet_iff (a : (AdeleRing (𝓞 F) F)ˣ) :
    a ∈ unitSet F ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      (a : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F ∧
        ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F := by
  unfold unitSet
  rw [SetLike.mem_coe, NumberField.AdeleRing.mem_unitIdelesOutside_iff,
    IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  simp only [Finset.coe_empty, Set.mem_empty_iff_false, not_false_eq_true, forall_const]
  rfl

theorem isOpen_unitSet : IsOpen (unitSet F) := isOpen_unitIdelesOutside F _

theorem one_mem_unitSet : (1 : (AdeleRing (𝓞 F) F)ˣ) ∈ unitSet F := Subgroup.one_mem _

theorem mul_mem_unitSet_iff {a b : (AdeleRing (𝓞 F) F)ˣ} (ha : a ∈ unitSet F) : a * b ∈ unitSet F ↔ b ∈ unitSet F :=
  Subgroup.mul_mem_cancel_left _ ha

def sect (x : InfinitePlace F → ℝ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (fun w => ofRealAt w (Real.exp (x w)), 1)
  inv := (fun w => ofRealAt w (Real.exp (-x w)), 1)
  val_inv := by
    refine Prod.ext (funext fun w => ?_) (mul_one _)
    change ofRealAt w (Real.exp (x w)) * ofRealAt w (Real.exp (-x w)) = 1
    rw [← map_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, map_one]
  inv_val := by
    refine Prod.ext (funext fun w => ?_) (mul_one _)
    change ofRealAt w (Real.exp (-x w)) * ofRealAt w (Real.exp (x w)) = 1
    rw [← map_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, map_one]

theorem sect_mem_unitSet (x : InfinitePlace F → ℝ) : sect F x ∈ unitSet F := by
  rw [mem_unitSet_iff]
  intro v
  exact ⟨one_mem _, one_mem _⟩

theorem logNorms_sect (x : InfinitePlace F → ℝ) : logNorms F (sect F x) = x := by
  funext w
  change Real.log ‖ofRealAt w (Real.exp (x w))‖ = x w
  rw [norm_ofRealAt, abs_of_pos (Real.exp_pos _), Real.log_exp]

def idBox (r R : ℝ) : Set (AdeleRing (𝓞 F) F)ˣ :=
  {a | (∀ w : InfinitePlace F, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ∈ Set.Icc r R) ∧
    (∀ w : InfinitePlace F, ‖((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖ ∈ Set.Icc r R) ∧
    (∀ v : HeightOneSpectrum (𝓞 F), (a : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F) ∧
    ∀ v : HeightOneSpectrum (𝓞 F), ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v ∈ v.adicCompletionIntegers F}

theorem isCompact_idBox (r R : ℝ) : IsCompact (idBox F r R) := by
  set C : Set (AdeleRing (𝓞 F) F) :=
    {x | (∀ w : InfinitePlace F, ‖x.1 w‖ ∈ Set.Icc r R) ∧
      ∀ v : HeightOneSpectrum (𝓞 F), x.2 v ∈ v.adicCompletionIntegers F} with hCdef
  have hC : IsCompact C := by
    have hpi : C = (Set.pi Set.univ fun w : InfinitePlace F => {c : w.Completion | ‖c‖ ∈ Set.Icc r R}) ×ˢ
        NumberField.AdelicLevel.integralFiniteAdeles (𝓞 F) F := by
      ext x
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun w _ => h1 w, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun w => h1 w (Set.mem_univ _), h2⟩
    rw [hpi]
    exact (isCompact_univ_pi fun w => isCompact_annulus w r R).prod
      (NumberField.AdelicLevel.isCompact_integralFiniteAdeles (𝓞 F) F)
  have hK : IsCompact ((Units.embedProduct (AdeleRing (𝓞 F) F)) ⁻¹' (C ×ˢ (MulOpposite.op '' C))) :=
    Units.isClosedEmbedding_embedProduct.isCompact_preimage (hC.prod (hC.image MulOpposite.continuous_op))
  have heq : idBox F r R = (Units.embedProduct (AdeleRing (𝓞 F) F)) ⁻¹' (C ×ˢ (MulOpposite.op '' C)) := by
    ext a
    simp only [idBox, hCdef, Set.mem_ofPred_eq, Set.mem_preimage, Units.embedProduct_apply, Set.mem_prod,
      Set.mem_image]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3⟩, _, ⟨h2, h4⟩, rfl⟩
    · rintro ⟨⟨h1, h3⟩, m, ⟨h2, h4⟩, hm⟩
      have : m = ((a⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F) := MulOpposite.op_injective hm
      subst this
      exact ⟨h1, h2, h3, h4⟩
  rw [heq]; exact hK

theorem preimage_logNorms_inter_unitSet_subset {K : Set (InfinitePlace F → ℝ)} {Rb : ℝ}
    (hK : ∀ x ∈ K, ∀ w, |x w| ≤ Rb) :
    logNorms F ⁻¹' K ∩ unitSet F ⊆ idBox F (Real.exp (-Rb)) (Real.exp Rb) := by
  rintro a ⟨haK, haU⟩
  rw [mem_unitSet_iff] at haU
  have hb : ∀ w, ‖(a : AdeleRing (𝓞 F) F).1 w‖ ∈ Set.Icc (Real.exp (-Rb)) (Real.exp Rb) := by
    intro w
    have h := abs_le.mp (hK _ haK w)
    rw [logNorms_apply] at h
    rw [← exp_logNorms F a w, logNorms_apply]
    exact ⟨Real.exp_le_exp.mpr h.1, Real.exp_le_exp.mpr h.2⟩
  refine ⟨hb, fun w => ?_, fun v => (haU v).1, fun v => (haU v).2⟩
  rw [fst_apply_inv, norm_inv]
  obtain ⟨h1, h2⟩ := hb w
  have hpos := norm_fst_apply_pos F a w
  constructor
  · rw [Real.exp_neg, inv_le_inv₀ (Real.exp_pos _) hpos]; exact h2
  · rw [inv_le_comm₀ hpos (Real.exp_pos _), ← Real.exp_neg]; exact h1

end Idele

section Measure

variable (F : Type) [Field F] [NumberField F]

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

def muU : Measure (AdeleRing (𝓞 F) F)ˣ := (idelicHaar F).restrict (unitSet F)

def muLog : Measure (InfinitePlace F → ℝ) := Measure.map (logNorms F) (muU F)

theorem sPartMeasure_empty : sPartMeasure F ∅ = Measure.map (partAt F ∅) (muU F) := rfl

theorem muLog_apply {s : Set (InfinitePlace F → ℝ)} (hs : MeasurableSet s) :
    muLog F s = idelicHaar F (logNorms F ⁻¹' s ∩ unitSet F) := by
  rw [muLog, Measure.map_apply (measurable_logNorms F) hs, muU,
    Measure.restrict_apply ((measurable_logNorms F) hs)]

scoped instance isAddLeftInvariant_muLog : (muLog F).IsAddLeftInvariant := by
  refine ⟨fun g => Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply (measurable_const_add g) hs, muLog_apply F hs,
    muLog_apply F ((measurable_const_add g) hs)]
  set a : (AdeleRing (𝓞 F) F)ˣ := sect F g with hadef
  have ha : a ∈ unitSet F := sect_mem_unitSet F g
  have hpre : logNorms F ⁻¹' ((fun x => g + x) ⁻¹' s) ∩ unitSet F
      = (fun b => a * b) ⁻¹' (logNorms F ⁻¹' s ∩ unitSet F) := by
    ext b
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    rw [logNorms_mul, logNorms_sect, mul_mem_unitSet_iff F ha]
  rw [hpre, measure_preimage_mul]

scoped instance isFiniteMeasureOnCompacts_muLog : IsFiniteMeasureOnCompacts (muLog F) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨Rb, hRb⟩ := hK.isBounded.exists_norm_le
  have hK' : ∀ x ∈ K, ∀ w, |x w| ≤ Rb := fun x hx w =>
    (Real.norm_eq_abs _ ▸ norm_le_pi_norm x w).trans (hRb x hx)
  rw [muLog_apply F hK.measurableSet]
  exact (measure_mono (preimage_logNorms_inter_unitSet_subset F hK')).trans_lt
    (isCompact_idBox F _ _).measure_lt_top

theorem muLog_ne_zero : muLog F ≠ 0 := by
  intro h
  have h1 : muLog F Set.univ = 0 := by rw [h]; rfl
  rw [muLog_apply F MeasurableSet.univ, Set.preimage_univ, Set.univ_inter] at h1
  exact ((isOpen_unitSet F).measure_pos (idelicHaar F) ⟨1, one_mem_unitSet F⟩).ne' h1

theorem muLog_eq_smul_volume :
    muLog F = (muLog F).addHaarScalarFactor volume • (volume : Measure (InfinitePlace F → ℝ)) :=
  Measure.isAddLeftInvariant_eq_smul _ _

theorem addHaarScalarFactor_muLog_ne_zero : (muLog F).addHaarScalarFactor volume ≠ 0 := by
  intro h0
  apply muLog_ne_zero F
  rw [muLog_eq_smul_volume F, h0, zero_smul]

theorem prod_eq_comp_logNorms (h : InfinitePlace F → ℝ → ℝ≥0∞) (a : (AdeleRing (𝓞 F) F)ˣ) :
    ∏ w : InfinitePlace F, h w ‖(a : AdeleRing (𝓞 F) F).1 w‖
      = (fun x : InfinitePlace F → ℝ => ∏ w, h w (Real.exp (x w))) (logNorms F a) := by
  simp only [exp_logNorms]

theorem main :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ h : InfinitePlace F → ℝ → ℝ≥0∞, (∀ w, Measurable (h w)) →
        (∫⁻ a, ∏ w : InfinitePlace F, h w ‖((a : AdeleRing (𝓞 F) F).1 w)‖ ∂(sPartMeasure F ∅)) =
          C * ∏ w : InfinitePlace F, ∫⁻ t in Set.Ioi (0 : ℝ), h w t * (ENNReal.ofReal t)⁻¹ := by
  classical
  refine ⟨((muLog F).addHaarScalarFactor volume : ℝ≥0∞), ?_, ENNReal.coe_ne_top, fun h hh => ?_⟩
  · exact ENNReal.coe_ne_zero.mpr (addHaarScalarFactor_muLog_ne_zero F)
  have hΦ : Measurable fun a : (AdeleRing (𝓞 F) F)ˣ => ∏ w : InfinitePlace F, h w ‖(a : AdeleRing (𝓞 F) F).1 w‖ :=
    Finset.measurable_prod _ fun w _ => (hh w).comp ((continuous_fst_apply F w).norm).measurable
  have hG : Measurable fun x : InfinitePlace F → ℝ => ∏ w, h w (Real.exp (x w)) :=
    Finset.measurable_prod _ fun w _ => (hh w).comp (Real.measurable_exp.comp (measurable_pi_apply w))
  rw [sPartMeasure_empty, lintegral_map hΦ (measurable_partAt F ∅)]
  have hpart : (fun a : (AdeleRing (𝓞 F) F)ˣ => ∏ w : InfinitePlace F,
      h w ‖((partAt F ∅ a : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 w‖)
      = fun a => (fun x : InfinitePlace F → ℝ => ∏ w, h w (Real.exp (x w))) (logNorms F a) := by
    funext a
    rw [← prod_eq_comp_logNorms]
    rfl
  rw [hpart, ← lintegral_map hG (measurable_logNorms F)]
  change ∫⁻ x, ∏ w, h w (Real.exp (x w)) ∂(muLog F) = _
  have hμ := muLog_eq_smul_volume F
  set c := (muLog F).addHaarScalarFactor volume with hcdef
  rw [hμ, lintegral_smul_measure, volume_pi,
    lintegral_fintype_prod_eq_prod (fun _ : InfinitePlace F => (volume : Measure ℝ))
      (fun w t => h w (Real.exp t)) (fun w => (hh w).comp Real.measurable_exp) (fun _ => 0),
    ENNReal.smul_def, smul_eq_mul]
  congr 1
  exact Finset.prod_congr rfl fun w _ => lintegral_comp_exp (h w)

end Measure

end NormProduct
/-! ### Positivity of the `S`-part measure

Transcribed from the `S_NumberField_Idele_sPartMeasure_pos_of_isOpen_of_partAt_eq` pin (stage label
`RS40LMb` → `PartAt`): an idèle that is a unit outside `S` is fixed by `partAt F S`, so the `S`-part
measure of an open set containing it is positive. -/
namespace PartAt

open Topology

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

variable (K : Type) [Field K] [NumberField K]

theorem partAt_eq_self_of_forall_snd_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (ht₀ : ∀ v, v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1) :
    partAt K S t₀ = t₀ := by
  classical
  apply Units.ext
  refine Prod.ext (partAt_fst K S t₀) (RestrictedProduct.ext _ _ fun v => ?_)
  by_cases hv : v ∈ S
  · exact partAt_snd_of_mem K S t₀ hv
  · exact (partAt_snd_of_not_mem K S t₀ hv).trans (ht₀ v hv).symm

theorem mem_unitIdelesOutside_of_forall_snd_eq_one (S : Finset (HeightOneSpectrum (𝓞 K)))
    (t₀ : (AdeleRing (𝓞 K) K)ˣ) (ht₀ : ∀ v, v ∉ S → ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1) :
    t₀ ∈ NumberField.AdeleRing.unitIdelesOutside (𝓞 K) K (↑S : Set (HeightOneSpectrum (𝓞 K))) := by
  rw [NumberField.AdeleRing.mem_unitIdelesOutside_iff, IsDedekindDomain.FiniteAdeleRing.mem_unitIdelesOutside_iff]
  intro v hv
  have hv' : v ∉ S := fun h => hv (Finset.mem_coe.mpr h)
  have h1 : ((t₀ : AdeleRing (𝓞 K) K)).2 v = 1 := ht₀ v hv'
  have h2 : (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
    have hmul : ((t₀ : AdeleRing (𝓞 K) K)).2 v * (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by
      have h : (((t₀ * t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v = 1 := by rw [mul_inv_cancel]; rfl
      exact h
    rwa [h1, one_mul] at hmul
  refine ⟨?_, ?_⟩
  · change ((t₀ : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K
    rw [h1]; exact one_mem _
  · change (((t₀⁻¹ : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v ∈ v.adicCompletionIntegers K
    rw [h2]; exact one_mem _

end PartAt

section Rows

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel
  NumberField.Idele.isHaarMeasure_idelicHaar

/-- **The `S`-part measure, factored.** The `lintegral` of a product of local orders against the `S`-part
measure is its value at the empty set times the `tsum` of the remaining local factors. -/
theorem lintegral_mul_prod_ord_sPartMeasure_eq_lintegral_sPartMeasure_empty_mul_prod_tsum
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : (AdeleRing (𝓞 F) F)ˣ → ℝ≥0∞) (hf : Measurable[ideleBorel F] f)
    (hf1 : ∀ a b : (AdeleRing (𝓞 F) F)ˣ, ((a : AdeleRing (𝓞 F) F)).1 = ((b : AdeleRing (𝓞 F) F)).1 → f a = f b)
    (φ : HeightOneSpectrum (𝓞 F) → ℤ → ℝ≥0∞) :
    (∫⁻ a, f a * ∏ v ∈ S, φ v (ord F v a) ∂(sPartMeasure F S)) =
      (∫⁻ a, f a ∂(sPartMeasure F ∅)) * ∏ v ∈ S, ∑' m : ℤ, φ v m := by
  rw [SPartIntegral.lintegral_sPartMeasure_eq_setLIntegral F S f hf hf1 φ]
  exact SPartIntegral.setLIntegral_eq_lintegral_sPartMeasure_empty_mul_prod F S f hf hf1 φ

/-- **The product formula.** The `lintegral` of a norm product against the `S`-part measure at the empty
set factors as the product of the local `lintegral`s. -/
theorem exists_lintegral_prod_norm_sPartMeasure_empty_eq_mul_prod_lintegral
    (F : Type) [Field F] [NumberField F] :
    ∃ C : ℝ≥0∞, C ≠ 0 ∧ C ≠ ∞ ∧
      ∀ h : InfinitePlace F → ℝ → ℝ≥0∞, (∀ w, Measurable (h w)) →
        (∫⁻ a, ∏ w : InfinitePlace F, h w ‖((a : AdeleRing (𝓞 F) F).1 w)‖ ∂(sPartMeasure F ∅)) =
          C * ∏ w : InfinitePlace F, ∫⁻ t in Set.Ioi (0 : ℝ), h w t * (ENNReal.ofReal t)⁻¹ := by
  exact NormProduct.main F

/-- **Positivity.** An open set with a nonempty slice at one component has positive `S`-part measure. -/
theorem sPartMeasure_pos_of_isOpen_of_partAt_eq
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t₀ : (AdeleRing (𝓞 F) F)ˣ)
    (ht₀ : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((t₀ : AdeleRing (𝓞 F) F)).2 v = 1)
    (U : Set (AdeleRing (𝓞 F) F)ˣ) (hU : IsOpen U) (hU₀ : t₀ ∈ U) :
    0 < sPartMeasure F S U := by
  have hmeas : MeasurableSet U := hU.measurableSet
  rw [NumberField.Idele.sPartMeasure, Measure.map_apply (measurable_partAt F S) hmeas,
    Measure.restrict_apply (hmeas.preimage (measurable_partAt F S))]
  have hopen : IsOpen ((partAt F S) ⁻¹' U ∩
      (NumberField.AdeleRing.unitIdelesOutside (𝓞 F) F (↑S : Set (HeightOneSpectrum (𝓞 F))) :
        Set (AdeleRing (𝓞 F) F)ˣ)) :=
    (hU.preimage (continuous_partAt F S)).inter (isOpen_unitIdelesOutside F _)
  refine hopen.measure_pos (idelicHaar F)
    ⟨t₀, ?_, PartAt.mem_unitIdelesOutside_of_forall_snd_eq_one F S t₀ ht₀⟩
  show partAt F S t₀ ∈ U
  rw [PartAt.partAt_eq_self_of_forall_snd_eq_one F S t₀ ht₀]
  exact hU₀

end Rows

end NumberField.Idele
/-! ### Approximation of a finite adèle by a global element

Both `S_` pins of this subject prove the same theorem — a finite adèle differs from the image of a global
element by something integral at *every* finite place — and the two flattened files carry two copies of
the engine under different stage prefixes (`s2_` in the `forall` copy, none in the other). The port keeps
both copies at the pins' last names, since each is a public declaration of its own wire.
`M4aP1R` is the pipeline's stage label; its sub-namespace `Approx` is the subject's. -/
namespace IsDedekindDomain.FiniteAdeleRing

namespace Approx

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Multiplicative

lemma exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  have h1 : WithZero.log x ≤ 0 := by
    have h2 : WithZero.exp (WithZero.log x) ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_log hx, WithZero.exp_zero]; exact hx'
    exact WithZero.exp_le_exp.mp h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos h1)
  refine ⟨k, ?_⟩
  have hk' : (-(k : ℤ)) = WithZero.log x := by omega
  rw [← WithZero.exp_log hx, hk']
  rfl

lemma exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(WithZero.log x))
  refine ⟨k, ?_⟩
  rw [← WithZero.exp_log hx]
  change WithZero.exp (-(k : ℤ)) < WithZero.exp (WithZero.log x)
  rw [WithZero.exp_lt_exp]
  omega

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] (v : HeightOneSpectrum A)

theorem exists_valued_algebraMap_sub_lt (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ)
    (hγ : (γ : ℤᵐ⁰) ≤ 1) :
    ∃ a : A, Valued.v (((algebraMap A K a : K) : v.adicCompletion K) - (x : v.adicCompletion K)) < γ := by
  obtain ⟨t, ht⟩ := valuedAdicCompletion_surjective K v (γ : ℤᵐ⁰)
  have ht0 : t ≠ 0 := fun h => γ.ne_zero (by rw [← ht, h, map_zero])
  have hrt : (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).restrict t ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr ht0
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < γ} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨Units.mk0 _ hrt, fun z hz => ?_⟩
    have hz' : Valued.v (z - (x : v.adicCompletion K)) < Valued.v t :=
      (Valuation.restrict_lt_iff _).mp hz
    rw [ht] at hz'
    exact hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < γ := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le (hy1.le.trans hγ) hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint γ
  refine ⟨a, ?_⟩
  have ha' : Valued.v (((algebraMap A K a : K) : v.adicCompletion K) -
      algebraMap K (v.adicCompletion K) y) < γ := by
    rw [show ((algebraMap A K a : K) : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y
        = ((algebraMap A K a - y : K) : v.adicCompletion K) from
        (map_sub (algebraMap K (v.adicCompletion K)) (algebraMap A K a) y).symm,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    (((algebraMap A K a : K) : v.adicCompletion K) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

theorem exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃ a, Valued.v ((algebraMap A K a : v.adicCompletion K) - (x : v.adicCompletion K)) < γ.val := by
  by_cases hγ : (γ : ℤᵐ⁰) ≤ 1
  · exact exists_valued_algebraMap_sub_lt K v x γ hγ
  · obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt K v x 1 (by rw [Units.val_one])
    exact ⟨a, ha.trans (by rw [Units.val_one]; exact lt_of_not_ge hγ)⟩

variable {v}

theorem exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by
  choose f hf using fun (i : s) =>
    exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)
  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K),
    ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

open scoped algebraMap

theorem exists_nonZeroDivisor_smul_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical
  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  ·
    exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  ·
    have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem exists_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  classical
  obtain ⟨d, hd, hda⟩ := exists_nonZeroDivisor_smul_mem_adicCompletionIntegers K a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hsupp : {v : HeightOneSpectrum A | v.intValuation d < 1}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {d})
      (by simpa [Ideal.span_singleton_eq_bot] using hd0)
    refine h.subset fun v hv ↦ ?_
    rw [Set.mem_ofPred_eq, intValuation_lt_one_iff_mem] at hv
    exact (Ideal.dvd_span_singleton).mpr hv
  obtain ⟨c, hc⟩ := exists_forall_adicValued_sub_lt K hsupp.toFinset
    (fun v ↦ Units.mk0 (v.intValuation d) (v.intValuation_ne_zero d hd0))
    id Function.injective_id (fun v ↦ ⟨(d : v.adicCompletion K) * a v, hda v⟩)
  refine ⟨algebraMap A K c / algebraMap A K d, fun v ↦ ?_⟩
  have hdK : algebraMap A K d ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hd
  have hdv : Valued.v ((d : A) : v.adicCompletion K) ≠ 0 := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
    exact v.intValuation_ne_zero d hd0
  have key : ∀ v : HeightOneSpectrum A,
      Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        ≤ Valued.v (((d : A) : v.adicCompletion K)) := by
    intro v
    by_cases hv : v.intValuation d < 1
    ·
      have h := hc v (hsupp.mem_toFinset.mpr hv)
      simp only [id_eq, Units.val_mk0] at h
      rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
      calc Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
          = Valued.v (((c : A) : v.adicCompletion K) - (d : v.adicCompletion K) * a v) := by
            rw [← Valuation.map_neg, neg_sub]
        _ ≤ v.intValuation d := le_of_lt h
    ·
      rw [not_lt] at hv
      have hd1 : Valued.v (((d : A) : v.adicCompletion K)) = 1 := by
        rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d) hv
      rw [hd1, ← mem_adicCompletionIntegers]
      exact sub_mem (hda v) (coe_mem_adicCompletionIntegers v c)
  rw [mem_adicCompletionIntegers]
  have hdne : ((d : A) : v.adicCompletion K) ≠ 0 := by
    intro h0
    exact hdv (by rw [h0, map_zero])
  have hmap : algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((c : A) : v.adicCompletion K) / ((d : A) : v.adicCompletion K) := by
    rw [map_div₀]
    rfl
  have hrw : a v - algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        / ((d : A) : v.adicCompletion K) := by
    rw [hmap, sub_div, mul_comm ((d : A) : v.adicCompletion K) (a v),
      mul_div_assoc, div_self hdne, mul_one]
  rw [hrw, map_div₀, div_le_one₀ (zero_lt_iff.mpr hdv)]
  exact key v

end Approx

theorem Approx.exists_sub_algebraMap_mem_adicCompletionIntegers_impl
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  Approx.exists_sub_algebraMap_mem_adicCompletionIntegers K a

/-! The `s2_` copy: the same engine, with the extra valuation layer
(`s2_closureAlgebraMapIntegers_eq_integers`, `s2_exists_adicValued_sub_lt_of_adicValued_le_one`) that the
`forall` pin's witness needs. The pin's `vK` local notation and its `scoped` rank-one instance are kept
as they are. -/
namespace HeightOneSpectrum

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero
lemma s2_exists_ofAdd_natCast_of_le_one {x : ℤᵐ⁰} (hx : x ≠ 0) (hx' : x ≤ 1) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) = x := by
  have h1 : WithZero.log x ≤ 0 := by
    have h2 : WithZero.exp (WithZero.log x) ≤ WithZero.exp (0 : ℤ) := by
      rw [WithZero.exp_log hx, WithZero.exp_zero]; exact hx'
    exact WithZero.exp_le_exp.mp h2
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (Int.neg_nonneg_of_nonpos h1)
  refine ⟨k, ?_⟩
  have hk' : (-(k : ℤ)) = WithZero.log x := by omega
  rw [← WithZero.exp_log hx, hk']
  rfl

lemma s2_exists_ofAdd_natCast_lt {x : ℤᵐ⁰} (hx : x ≠ 0) :
    ∃ (k : ℕ), (Multiplicative.ofAdd (-(k : ℤ))) < x := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-(WithZero.log x))
  refine ⟨k, ?_⟩
  rw [← WithZero.exp_log hx]
  change WithZero.exp (-(k : ℤ)) < WithZero.exp (WithZero.log x)
  rw [WithZero.exp_lt_exp]
  omega

end Multiplicative

lemma s2_intValuation_eq_coe_neg_multiplicity {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) {a : A} (hnz : a ≠ 0) :
    v.intValuation a = WithZero.exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) := by
  classical
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [intValuation_if_neg _ hnz, Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot]
  nth_rw 1 [← normalize_eq v.asIdeal]
  congr
  symm
  apply multiplicity_eq_of_emultiplicity_eq_some
  rw [← UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb]

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)

lemma s2_ne_zero_of_some_le_intValuation {a : A} {m : Multiplicative ℤ} (h : m ≤ v.intValuation a)
    : a ≠ 0 := by
  rintro rfl
  simp at h

lemma s2_emultiplicity_eq_of_valuation_eq_ofAdd {a : A} {k : ℕ}
    (hv : v.intValuation a = (Multiplicative.ofAdd (-(k : ℤ)))) :
    emultiplicity v.asIdeal (Ideal.span {a}) = k := by
  classical
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ (le_of_eq hv.symm)
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  simp only [intValuation_if_neg _ hnz, WithZero.exp, ofAdd_neg, WithZero.coe_inv, inv_inj,
    WithZero.coe_inj, EmbeddingLike.apply_eq_iff_eq, Nat.cast_inj] at hv
  rw [← hv, UniqueFactorizationMonoid.emultiplicity_eq_count_normalizedFactors v.irreducible hnb,
    Ideal.count_associates_factors_eq hnb v.isPrime v.ne_bot, normalize_eq]

lemma s2_exists_adicValued_mul_sub_le {a b : A} {γ : WithZero (Multiplicative ℤ)} (hγ : γ ≠ 0)
    (hle : γ ≤ v.intValuation a)
    (hle' : v.intValuation b ≤ v.intValuation a) :
    ∃ y, v.intValuation (y * a - b) ≤ γ := by
  have hγ' : γ ≤ 1 := by
    apply hle.trans
    apply intValuation_le_one
  obtain ⟨n, hn⟩ := s2_exists_ofAdd_natCast_of_le_one hγ hγ'
  rw [← hn, ← WithZero.exp] at hle ⊢
  have hnz : a ≠ 0 := s2_ne_zero_of_some_le_intValuation _ hle
  have hnb : Ideal.span {a} ≠ ⊥ := by
    rwa [ne_eq, Ideal.span_singleton_eq_bot]
  rw [s2_intValuation_eq_coe_neg_multiplicity _ hnz, WithZero.exp_le_exp, neg_le_neg_iff,
    Int.ofNat_le] at hle
  have hm : emultiplicity v.asIdeal (Ideal.span {a}) ≤ n :=
    le_of_eq_of_le
      (s2_emultiplicity_eq_of_valuation_eq_ofAdd v <| s2_intValuation_eq_coe_neg_multiplicity v hnz)
      (ENat.natCast_le_natCast.mpr hle)
  have hb : b ∈ v.asIdeal ^ multiplicity v.asIdeal (Ideal.span {a}) := by
    rwa [← intValuation_le_pow_iff_mem, ← s2_intValuation_eq_coe_neg_multiplicity _ hnz]
  rw [← Ideal.irreducible_pow_sup_of_ge hnb (irreducible v) n hm] at hb
  obtain ⟨x, hx, z, hz, hxz⟩ := Submodule.mem_sup.mp hb
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hz
  use y
  rwa [hy, ← hxz, sub_add_cancel_right, intValuation_le_pow_iff_mem, neg_mem_iff]

open MonoidWithZeroHom in
lemma s2_exists_adicValued_sub_lt_of_adicValued_le_one {x : (WithVal (v.valuation K))}
    (γ : ((WithZero (Multiplicative ℤ)))ˣ) (hx : Valued.v x ≤ 1) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  obtain ⟨⟨n, d, hd⟩, hnd⟩ := IsLocalization.surj (nonZeroDivisors A) x
  dsimp only at hnd
  have hnd' := congr_arg Valued.v hnd
  simp only [map_mul] at hnd'
  have hge : Valued.v ((algebraMap A (WithVal (v.valuation K))) d) ≥
      Valued.v ((algebraMap A (WithVal (v.valuation K))) n) :=
    calc Valued.v ((algebraMap A (WithVal (v.valuation K))) d)
          ≥ (valuation K v) x.ofVal *
            (valuation K v) ((algebraMap A (WithVal (v.valuation K))) d).ofVal :=
                mul_le_of_le_one_left' hx
        _ = Valued.v ((algebraMap A (WithVal (v.valuation K))) n) := hnd'
  simp only [ge_iff_le, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hge
  simp only [valuation_of_algebraMap] at hge
  have hdz : (algebraMap A (WithVal (v.valuation K)) d) ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _ (fun _ ↦ id) hd
  have hv : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact hdz
  let hu : Valued.v ((algebraMap A (WithVal (v.valuation K)) d)) * γ.val ≠ 0 := by
    rw [mul_ne_zero_iff]
    exact ⟨hv, γ.ne_zero⟩
  obtain ⟨γ', hγ, hγu, hγv⟩ := WithZero.exists_ne_zero_and_lt_and_lt hu hv
  simp only [WithVal.algebraMap_right_apply, WithVal.valued_toVal, valuation_of_algebraMap] at hγv
  obtain ⟨a, hval⟩ := s2_exists_adicValued_mul_sub_le v hγ hγv.le hge
  use a
  rw [← eq_div_iff_mul_eq hdz] at hnd
  rw [adicCompletion.valuedAdicCompletion_def, ← adicCompletion.equiv_apply, map_sub,
    adicCompletion.equiv_apply, adicCompletion.equiv_apply,
    adicCompletion.toCompletion_ofCompletion, adicCompletion.toCompletion_ofCompletion,
    ← UniformSpace.Completion.coe_sub, Valued.extensionValuation_apply_coe, hnd, sub_div' hdz,
    map_div₀]
  rw [← Valuation.pos_iff Valued.v, WithVal.algebraMap_right_apply, WithVal.valued_toVal] at hdz
  simp only [WithVal.algebraMap_right_apply,
    ← WithVal.toVal_mul, ← WithVal.toVal_sub, WithVal.valued_toVal, ← map_mul, ← map_sub] at hγu ⊢
  rw [div_lt_iff₀' hdz, valuation_of_algebraMap]
  exact lt_of_le_of_lt hval hγu

open scoped WithZero

local notation "vK" => (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

scoped instance s2_isRankOneDiscrete_valuedAdicCompletion : Valuation.IsRankOneDiscrete vK where
  exists_generator_lt_one' := by
    have h : (v.valuation K).IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' (valuation K v)
    exact ⟨h.generator, by rw [h.generator_zpowers_eq_valueGroup, adicCompletion_valueGroup_eq],
      h.generator_lt_one⟩

open Valuation.IsRankOneDiscrete in

theorem s2_closureAlgebraMapIntegers_eq_integers :
    closure (algebraMap A (v.adicCompletion K)).range =
    SetLike.coe (v.adicCompletionIntegers K) := by
  apply subset_antisymm
  · apply closure_minimal _ (Valued.isClosed_valuationSubring _)
    rintro b ⟨a, rfl⟩
    exact coe_mem_adicCompletionIntegers v a
  · let f := fun (k : WithVal (v.valuation K)) => (k : v.adicCompletion K)
    suffices h : closure (f '' (f ⁻¹' (adicCompletionIntegers K v))) ⊆
        closure (algebraMap A (adicCompletion K v)).range by
      apply Set.Subset.trans _ h
      exact DenseRange.subset_closure_image_preimage_of_isOpen
        ((adicCompletion.ofCompletion_surjective K v).denseRange.comp
          UniformSpace.Completion.denseRange_coe (adicCompletion.continuous_ofCompletion K v))
        (Valued.isOpen_valuationSubring _)
    apply closure_minimal _ isClosed_closure
    rintro k ⟨x, hx, rfl⟩
    unfold f at hx
    rw [Set.mem_preimage, SetLike.mem_coe, mem_adicCompletionIntegers,
        adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply] at hx
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Valued.mem_nhds] at hU
    obtain ⟨γ, hγ⟩ := hU
    let γ' := Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv γ
    obtain ⟨a, ha⟩ := s2_exists_adicValued_sub_lt_of_adicValued_le_one K v γ' hx
    use algebraMap A K a
    constructor
    · use a
      rfl
    · apply hγ
      simp only [sub_zero, Set.mem_ofPred_eq]
      rwa [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
        (valuedAdicCompletion_surjective K v)]

open Valuation.IsRankOneDiscrete in

theorem s2_exists_adicValued_sub_lt_of_adicCompletionInteger
    (x : v.adicCompletionIntegers K) (γ : ℤᵐ⁰ˣ) :
    ∃a, Valued.v ((algebraMap A K a) - (x : v.adicCompletion K)) < γ.val := by
  have h := s2_closureAlgebraMapIntegers_eq_integers K v
  rw [Set.ext_iff] at h
  specialize h x
  simp_rw [RingHom.coe_range, Subtype.coe_prop, iff_true, mem_closure_iff_nhds] at h
  specialize h { y | Valued.v (y  - (x : v.adicCompletion K)) < γ.val }
  have hn : {y | Valued.v (y - (x : v.adicCompletion K)) < γ.val} ∈ nhds x.val := by
    rw [Valued.mem_nhds]
    use (Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv).symm γ
    have hsurj := (valuedAdicCompletion_surjective K v)
    intro y hy
    have hy' := (valueGroup₀_equiv_withZeroMulInt_strictMono vK) hy
    rw [valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective hsurj] at hy'
    refine lt_of_lt_of_eq hy' ?_
    exact MulEquiv.apply_symm_apply (valueGroup₀_equiv_withZeroMulInt vK).toMulEquiv _
  obtain ⟨z, ⟨hz, a, ha⟩⟩ := h hn
  use a
  rw [algebraMap_adicCompletion, Function.comp_apply] at ha
  rwa [ha]

theorem s2_exists_forall_adicValued_sub_lt {ι : Type*} (s : Finset ι)
    (e : ι → (WithZero (Multiplicative ℤ))ˣ) (valuation : ι → HeightOneSpectrum A)
    (injective : Function.Injective valuation)
    (x : (i : ι) → (valuation i).adicCompletionIntegers K) :
    ∃ a, ∀ i ∈ s, Valued.v ((algebraMap A K a) - (x i).val) < (e i).val := by
  choose f hf using fun (i : s) =>
    s2_exists_adicValued_sub_lt_of_adicCompletionInteger K (valuation i) (x i) (e i)
  have hexists_e' : ∀ (i : ι), ∃ (e' : ℕ), (Multiplicative.ofAdd (-(e' : ℤ))) < (e i).val := by
    intro i
    apply s2_exists_ofAdd_natCast_lt (e i).ne_zero
  choose e' he' using hexists_e'
  have hinj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      (fun i ↦ (valuation i).asIdeal) i ≠ (fun i ↦ (valuation i).asIdeal) j := by
    intro _ _ _ _
    exact mt <| fun hij ↦ injective (HeightOneSpectrum.ext hij)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := s)
    (fun i => (valuation i).asIdeal) e' (fun i hi => (valuation i).prime) hinj f
  use a
  intro i hi
  specialize ha i hi
  specialize hf ⟨i, hi⟩
  rw [← intValuation_le_pow_iff_mem, ← valuation_of_algebraMap (K := K),
    ← valuedAdicCompletion_eq_valuation, algebraMap.coe_sub] at ha
  refine lt_of_le_of_lt ?_ (Valuation.map_add_lt _ (ha.trans_lt (he' i)) hf)
  apply le_of_eq
  congr
  rw [add_sub, sub_eq_sub_iff_add_eq_add, add_right_cancel_iff,
    add_comm_sub, add_sub, eq_sub_iff_add_eq]
  rfl

open scoped algebraMap

theorem s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ d ∈ nonZeroDivisors A, ∀ v : HeightOneSpectrum A,
      (d : v.adicCompletion K) * a v ∈ v.adicCompletionIntegers K := by
  classical
  have hbad : {v : HeightOneSpectrum A | a v ∉ v.adicCompletionIntegers K}.Finite :=
    Filter.eventually_cofinite.mp a.2
  choose b hb hba using fun v : HeightOneSpectrum A ↦
    adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (a v)
  refine ⟨∏ v ∈ hbad.toFinset, b v, prod_mem fun v _ ↦ hb v, fun v ↦ ?_⟩
  by_cases hv : a v ∈ v.adicCompletionIntegers K
  ·
    exact mul_mem (coe_mem_adicCompletionIntegers v _) hv
  ·
    have hvmem : v ∈ hbad.toFinset := hbad.mem_toFinset.mpr hv
    rw [← Finset.prod_erase_mul _ _ hvmem, algebraMap.coe_mul, mul_assoc]
    exact mul_mem (coe_mem_adicCompletionIntegers v _) (by rw [mul_comm]; exact hba v)

theorem s2_exists_sub_algebraMap_mem_adicCompletionIntegers (a : FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  classical
  obtain ⟨d, hd, hda⟩ := s2_exists_nonZeroDivisor_smul_mem_adicCompletionIntegers K a
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hsupp : {v : HeightOneSpectrum A | v.intValuation d < 1}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {d})
      (by simpa [Ideal.span_singleton_eq_bot] using hd0)
    refine h.subset fun v hv ↦ ?_
    rw [Set.mem_ofPred_eq, intValuation_lt_one_iff_mem] at hv
    exact (Ideal.dvd_span_singleton).mpr hv
  obtain ⟨c, hc⟩ := s2_exists_forall_adicValued_sub_lt K hsupp.toFinset
    (fun v ↦ Units.mk0 (v.intValuation d) (v.intValuation_ne_zero d hd0))
    id Function.injective_id (fun v ↦ ⟨(d : v.adicCompletion K) * a v, hda v⟩)
  refine ⟨algebraMap A K c / algebraMap A K d, fun v ↦ ?_⟩
  have hdK : algebraMap A K d ≠ 0 :=
    IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors K (fun _ ↦ id) hd
  have hdv : Valued.v ((d : A) : v.adicCompletion K) ≠ 0 := by
    rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
    exact v.intValuation_ne_zero d hd0
  have key : ∀ v : HeightOneSpectrum A,
      Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        ≤ Valued.v (((d : A) : v.adicCompletion K)) := by
    intro v
    by_cases hv : v.intValuation d < 1
    ·
      have h := hc v (hsupp.mem_toFinset.mpr hv)
      simp only [id_eq, Units.val_mk0] at h
      rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
      calc Valued.v ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
          = Valued.v (((c : A) : v.adicCompletion K) - (d : v.adicCompletion K) * a v) := by
            rw [← Valuation.map_neg, neg_sub]
        _ ≤ v.intValuation d := le_of_lt h
    ·
      rw [not_lt] at hv
      have hd1 : Valued.v (((d : A) : v.adicCompletion K)) = 1 := by
        rw [valuedAdicCompletion_eq_valuation, valuation_of_algebraMap]
        exact le_antisymm (v.intValuation_le_one d) hv
      rw [hd1, ← mem_adicCompletionIntegers]
      exact sub_mem (hda v) (coe_mem_adicCompletionIntegers v c)
  rw [mem_adicCompletionIntegers]
  have hdne : ((d : A) : v.adicCompletion K) ≠ 0 := by
    intro h0
    exact hdv (by rw [h0, map_zero])
  have hmap : algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((c : A) : v.adicCompletion K) / ((d : A) : v.adicCompletion K) := by
    rw [map_div₀]
    rfl
  have hrw : a v - algebraMap K (v.adicCompletion K) (algebraMap A K c / algebraMap A K d)
      = ((d : v.adicCompletion K) * a v - ((c : A) : v.adicCompletion K))
        / ((d : A) : v.adicCompletion K) := by
    rw [hmap, sub_div, mul_comm ((d : A) : v.adicCompletion K) (a v),
      mul_div_assoc, div_self hdne, mul_one]
  rw [hrw, map_div₀, div_le_one₀ (zero_lt_iff.mpr hdv)]
  exact key v

end HeightOneSpectrum

/-- **Approximation at each place.** Every finite adele is close to a global element at every place, in the
adic completion's integers, when one place is allowed to give way. -/
theorem exists_forall_sub_algebraMap_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K] [IsFractionRing A K]
    (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  HeightOneSpectrum.s2_exists_sub_algebraMap_mem_adicCompletionIntegers K a

/-- **Simultaneous approximation.** A finite adele minus a global element is integral at a prescribed set
of places. -/
theorem exists_sub_algebraMap_mem_adicCompletionIntegers
    {A : Type*} (K : Type*) [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
    [IsFractionRing A K] (a : IsDedekindDomain.FiniteAdeleRing A K) :
    ∃ x : K, ∀ v : IsDedekindDomain.HeightOneSpectrum A,
      a v - algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K :=
  Approx.exists_sub_algebraMap_mem_adicCompletionIntegers_impl K a

end IsDedekindDomain.FiniteAdeleRing
