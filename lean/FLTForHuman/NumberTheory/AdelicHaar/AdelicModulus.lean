/-
  The modulus character of the adèle ring, computed place by place: the finite-place half.

  `P6B.JE2aFlat.placeModulus` is the explicit product of the local normalised absolute
  values over the infinite places (weighted by the multiplicity `w.mult`) and the
  height-one primes, evaluated on an idele. The `P6B.JE2aHMod` blocks compute the modulus of
  an idele with trivial archimedean component as that product, by counting the index of
  `y • ẑ` in the integral lattice `ẑ = integralFiniteAdeles` — `card_zhat_quot_eq_absNorm`,
  `absNorm_globalIdeal_mul_finprod_norm`, `card_zhat_quot_mul_finprod_norm` — and then
  assemble the general idele from its archimedean unit and its finite unit
  (`distribHaarChar_eq_placeModulus`).

  Transcribed from
  `S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean`
  (pinned `aa2d8b3`), the genuinely new blocks: lines 14–72, 74–447, 1011–1101, 1103–1211
  and 1213–1349, keeping the pin namespaces `P6B.JE2aFlat`, `P6B.JE2aHMod` and `M4aS4`. The
  pin's `NumberField.AdelicCountability` block (449–585) and its first `M4aS4` block
  (587–1008) are already homed at `AdelicLevel/Countability.lean` and
  `AdelicHaar/PlaceMeasure.lean` and are imported, not re-transcribed; the pin's
  `import Mathlib` is replaced by specific mathlib modules, its final `theorem solution`
  (1352–1362) is left to the façade, and its `import Def_NumberField_AdelicHeight` is kept —
  the pin's `norm_finComp_eventually_eq_one` really does use that node's
  `norm_le_one_of_mem_adicCompletionIntegers` (the pin's lines 51 and 53), which the port
  homes whole at `FLTForHuman/NumberTheory/AdelicHeight.lean` (tier 1).

  The pin's `S_` file is a `P2MW` wrapper: its outer namespace and every `p2m_*` line are
  dropped here.
-/
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import FLTForHuman.NumberTheory.AdelicHeight
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option autoImplicit false

open MeasureTheory Complex NumberField NumberField.InfinitePlace IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum TopologicalSpace Filter NumberField.AdelicLevel
open NumberField.AdelicHeight
open scoped Pointwise ENNReal NNReal RestrictedProduct

noncomputable section

section RHMODFold_JE2aFlatAdelic

namespace P6B
namespace JE2aFlat

variable (F : Type) [Field F] [NumberField F]

-- pin: placeModulus (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:27)
def placeModulus (x : (AdeleRing (𝓞 F) F)ˣ) : ℝ :=
  (∏ w : InfinitePlace F, ‖(x : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult)
    * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(x : AdeleRing (𝓞 F) F).2 v‖

variable {F}

-- pin: finComp_mul_finComp_inv (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:33)
theorem finComp_mul_finComp_inv (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1 := by
  have h : ((x : AdeleRing (𝓞 F) F) * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)).2 v = 1 := by
    rw [x.mul_inv]; rfl
  exact h

-- pin: finComp_ne_zero (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:39)
theorem finComp_ne_zero (x : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (x : AdeleRing (𝓞 F) F).2 v ≠ 0 := by
  intro h0
  have h := finComp_mul_finComp_inv x v
  rw [h0, zero_mul] at h
  exact zero_ne_one h

-- pin: norm_finComp_eventually_eq_one (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:46)
theorem norm_finComp_eventually_eq_one (x : (AdeleRing (𝓞 F) F)ˣ) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ‖(x : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have hx := ((x : AdeleRing (𝓞 F) F).2).2
  have hx' := (((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2).2
  filter_upwards [hx, hx'] with v hv hv'
  have h1 : ‖(x : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 := norm_le_one_of_mem_adicCompletionIntegers hv
  have h2 : ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
    norm_le_one_of_mem_adicCompletionIntegers hv'
  have hprod : ‖(x : AdeleRing (𝓞 F) F).2 v‖
      * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    rw [← norm_mul, finComp_mul_finComp_inv, norm_one]
  refine le_antisymm h1 ?_
  by_contra hlt
  push Not at hlt
  have h3 : ‖(x : AdeleRing (𝓞 F) F).2 v‖
      * ‖((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v‖ < 1 :=
    (mul_le_mul_of_nonneg_left h2 (norm_nonneg _)).trans_lt (by simpa using hlt)
  rw [hprod] at h3
  exact lt_irrefl _ h3

-- pin: hasFiniteMulSupport_norm_finComp (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:64)
theorem hasFiniteMulSupport_norm_finComp (x : (AdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(x : AdeleRing (𝓞 F) F).2 v‖).HasFiniteMulSupport :=
  Filter.eventually_cofinite.mp (norm_finComp_eventually_eq_one x)

end P6B.JE2aFlat

end RHMODFold_JE2aFlatAdelic

section RHMODFold_JE2aHMod1

namespace P6B
namespace JE2aHMod

variable (F : Type) [Field F] [NumberField F]

-- pin: zhatAddSubgroup (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:86)
def zhatAddSubgroup : AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := integralFiniteAdeles (𝓞 F) F
  zero_mem' := fun _ => zero_mem _
  add_mem' := fun hx hy v => add_mem (hx v) (hy v)
  neg_mem' := fun hx v => neg_mem (hx v)

-- pin: mem_zhatAddSubgroup (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:92)
@[scoped simp] theorem mem_zhatAddSubgroup {x : FiniteAdeleRing (𝓞 F) F} :
    x ∈ zhatAddSubgroup F ↔ x ∈ integralFiniteAdeles (𝓞 F) F := Iff.rfl

-- pin: mul_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:95)
theorem mul_apply (a b : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (a * b) v = a v * b v := rfl

-- pin: one_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:98)
theorem one_apply (v : HeightOneSpectrum (𝓞 F)) :
    (1 : FiniteAdeleRing (𝓞 F) F) v = 1 := rfl

-- pin: zero_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:101)
theorem zero_apply (v : HeightOneSpectrum (𝓞 F)) :
    (0 : FiniteAdeleRing (𝓞 F) F) v = 0 := rfl

-- pin: neg_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:104)
theorem neg_apply (a : FiniteAdeleRing (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    (-a) v = -a v := rfl

-- pin: isUnit_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:107)
theorem isUnit_apply (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    IsUnit ((y : FiniteAdeleRing (𝓞 F) F) v) := by
  refine ⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v, ?_, ?_⟩, rfl⟩
  · rw [← mul_apply, y.mul_inv, one_apply]
  · rw [← mul_apply, y.inv_mul, one_apply]

-- pin: inv_apply (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:113)
theorem inv_apply (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = ((y : FiniteAdeleRing (𝓞 F) F) v)⁻¹ :=
  eq_inv_of_mul_eq_one_right
    (show (y : FiniteAdeleRing (𝓞 F) F) v * ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.mul_inv, one_apply])

-- pin: valued_apply_ne_zero (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:119)
theorem valued_apply_ne_zero (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) ≠ 0 :=
  (Valuation.ne_zero_iff _).mpr (isUnit_apply F y v).ne_zero

-- pin: ySmulZhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:123)
def ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (_hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    AddSubgroup (FiniteAdeleRing (𝓞 F) F) where
  carrier := {z | ∀ v : HeightOneSpectrum (𝓞 F),
    Valued.v (z v) ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v)}
  zero_mem' := fun v => by rw [zero_apply, map_zero]; exact zero_le
  add_mem' := fun {a b} ha hb v => (Valuation.map_add _ _ _).trans (max_le (ha v) (hb v))
  neg_mem' := fun {a} ha v => by rw [neg_apply, Valuation.map_neg]; exact ha v

-- pin: mem_ySmulZhat_iff (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:132)
@[scoped simp] theorem mem_ySmulZhat_iff (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    {z : FiniteAdeleRing (𝓞 F) F} :
    z ∈ ySmulZhat F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (z v) ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := Iff.rfl

-- pin: ySmulZhat_le_zhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:138)
theorem ySmulZhat_le_zhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    ySmulZhat F y hy ≤ zhatAddSubgroup F := fun _ hz v =>
  (mem_adicCompletionIntegers _ _ _).mpr
    ((hz v).trans ((mem_adicCompletionIntegers _ _ _).mp (hy v)))

-- pin: smul_integralFiniteAdeles_eq_ySmulZhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:144)
theorem smul_integralFiniteAdeles_eq_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    ((fun a => (y : FiniteAdeleRing (𝓞 F) F) * a) '' integralFiniteAdeles (𝓞 F) F)
      = (ySmulZhat F y hy : Set (FiniteAdeleRing (𝓞 F) F)) := by
  ext z; constructor
  · rintro ⟨a, ha, rfl⟩ v
    rw [mul_apply, Valuation.map_mul]
    exact mul_le_of_le_one_right' ((mem_adicCompletionIntegers _ _ _).mp (ha v))
  · intro hz
    refine ⟨((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) * z, fun v => ?_, ?_⟩
    · rw [mem_adicCompletionIntegers, mul_apply, Valuation.map_mul, inv_apply, map_inv₀,
        inv_mul_le_one₀ (zero_lt_iff.mpr (valued_apply_ne_zero F y v))]
      exact hz v
    · show (y : FiniteAdeleRing (𝓞 F) F) * (_ * z) = z
      rw [← mul_assoc, y.mul_inv, one_mul]

-- pin: finite_support_not_unit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:160)
theorem finite_support_not_unit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    {v : HeightOneSpectrum (𝓞 F) |
      ¬ IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)}.Finite := by

  have hfin : {v : HeightOneSpectrum (𝓞 F) |
      ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.mp
      (show Πʳ v : HeightOneSpectrum (𝓞 F), [v.adicCompletion F, v.adicCompletionIntegers F]
        from ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F)).eventually
  refine hfin.subset fun v hv hinv => hv ?_

  refine ⟨⟨⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩,
    ⟨((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v, hinv⟩, ?_, ?_⟩, rfl⟩
  · exact Subtype.ext (show (y : FiniteAdeleRing (𝓞 F) F) v
      * ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.mul_inv, one_apply])
  · exact Subtype.ext (show ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F) v
      * (y : FiniteAdeleRing (𝓞 F) F) v = 1 by
      rw [← mul_apply, y.inv_mul, one_apply])

-- pin: globalIdeal (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:181)
def globalIdeal (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Ideal (𝓞 F) where
  carrier := {r | algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r ∈ ySmulZhat F y hy}
  zero_mem' := by simp only [Set.mem_ofPred_eq, map_zero]; exact (ySmulZhat F y hy).zero_mem
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, map_add]; exact (ySmulZhat F y hy).add_mem ha hb
  smul_mem' := fun c {r} hr v => by
    simp only [Set.mem_ofPred_eq, smul_eq_mul, map_mul] at hr ⊢
    rw [mul_apply, Valuation.map_mul]
    exact (mul_le_of_le_one_left zero_le
      ((mem_adicCompletionIntegers _ _ _).mp
        (algebraMap_mem_adicCompletionIntegers v c))).trans (hr v)

-- pin: mem_globalIdeal_iff (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:195)
theorem mem_globalIdeal_iff (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) {r : 𝓞 F} :
    r ∈ globalIdeal F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F),
      Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r v)
        ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := Iff.rfl

-- pin: globalIdeal_ne_bot (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:201)
theorem globalIdeal_ne_bot (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    globalIdeal F y hy ≠ ⊥ := by
  obtain ⟨s, hs0, hsy⟩ := AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 F) F
    ((y⁻¹ : _) : FiniteAdeleRing (𝓞 F) F)
  rw [Submodule.ne_bot_iff]
  refine ⟨s, fun v => ?_, hs0⟩

  have := (mem_adicCompletionIntegers _ _ _).mp (hsy v)
  rw [mul_apply, Valuation.map_mul, inv_apply, map_inv₀] at this
  calc Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s v)
      = Valued.v (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s v)
        * (Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v))⁻¹
        * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by
          rw [mul_assoc, inv_mul_cancel₀ (valued_apply_ne_zero F y v), mul_one]
    _ ≤ 1 * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by gcongr; exact this
    _ = Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := one_mul _

-- pin: surjective_zhat_mod_ySmulZhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:219)
theorem surjective_zhat_mod_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (z : zhatAddSubgroup F) :
    ∃ a : 𝓞 F, ((⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
        fun v => algebraMap_mem_adicCompletionIntegers v a⟩ : zhatAddSubgroup F) - z)
      ∈ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) := by

  obtain ⟨s, hs_mem, hs0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (globalIdeal_ne_bot F y hy)
  obtain ⟨a, ha⟩ := AdelicBox.exists_forall_valued_sub_le (𝓞 F) F (z := (z : FiniteAdeleRing (𝓞 F) F))
    z.2 (s := s) hs0
  refine ⟨a, fun v => ?_⟩
  show Valued.v (((⟨algebraMap _ _ a, _⟩ - z : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) v)
    ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v)
  calc Valued.v (((⟨algebraMap _ _ a, _⟩ - z : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) v)
      = Valued.v ((z : FiniteAdeleRing (𝓞 F) F) v
        - algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F a)) := by
          rw [Valuation.map_sub_swap]; rfl
    _ ≤ Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s)) := ha v
    _ = Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s) v) := by rfl
    _ ≤ Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := hs_mem v

-- pin: finite_zhat_quot_ySmulZhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:240)
theorem finite_zhat_quot_ySmulZhat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Finite (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)) := by

  have hfin : Finite ((𝓞 F) ⧸ globalIdeal F y hy) :=
    (globalIdeal F y hy).finiteQuotientOfFreeOfNeBot (globalIdeal_ne_bot F y hy)

  set H := (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)
  let q : (𝓞 F) →+ zhatAddSubgroup F ⧸ H :=
    (QuotientAddGroup.mk' H).comp
      { toFun := fun a => ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
          fun v => algebraMap_mem_adicCompletionIntegers v a⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }
  have hsurj : Function.Surjective q := by
    refine Quotient.ind fun z => ?_
    obtain ⟨a, ha⟩ := surjective_zhat_mod_ySmulZhat F y hy z
    exact ⟨a, (QuotientAddGroup.eq_iff_sub_mem).mpr ha⟩

  have hker : ∀ a b : 𝓞 F, Submodule.quotientRel (globalIdeal F y hy) a b → q a = q b := by
    intro a b hab
    have hmem : -a + b ∈ globalIdeal F y hy := QuotientAddGroup.leftRel_apply.mp hab
    rw [eq_comm, show q b = q a ↔ q b - q a = 0 from sub_eq_zero.symm, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).mpr
      (by rw [show b - a = -a + b from by ring]; exact hmem)

  let f : (𝓞 F) ⧸ globalIdeal F y hy → zhatAddSubgroup F ⧸ H :=
    fun c => Quotient.liftOn' c q hker
  have hfsurj : Function.Surjective f := fun z => by
    obtain ⟨a, ha⟩ := hsurj z
    exact ⟨Ideal.Quotient.mk _ a, ha⟩
  exact Finite.of_surjective f hfsurj

-- pin: quotZhatHom (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:273)
def quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (𝓞 F) →+ zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) :=
  (QuotientAddGroup.mk' _).comp
    { toFun := fun a => ⟨algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) a,
        fun v => algebraMap_mem_adicCompletionIntegers v a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' := fun _ _ => Subtype.ext (map_add _ _ _) }

-- pin: ker_quotZhatHom (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:282)
theorem ker_quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (quotZhatHom F y hy).ker = (globalIdeal F y hy).toAddSubgroup := by
  ext a; simp only [AddMonoidHom.mem_ker, quotZhatHom, AddMonoidHom.coe_comp,
    QuotientAddGroup.coe_mk', Function.comp_apply, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  rfl

-- pin: surjective_quotZhatHom (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:290)
theorem surjective_quotZhatHom (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Function.Surjective (quotZhatHom F y hy) := by
  refine Quotient.ind fun z => ?_
  obtain ⟨a, ha⟩ := surjective_zhat_mod_ySmulZhat F y hy z
  exact ⟨a, (QuotientAddGroup.eq_iff_sub_mem).mpr ha⟩

-- pin: card_zhat_quot_eq_absNorm (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:297)
theorem card_zhat_quot_eq_absNorm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    Nat.card (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F))
      = Ideal.absNorm (globalIdeal F y hy) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot, ← ker_quotZhatHom F y hy]
  exact (Nat.card_congr
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (surjective_quotZhatHom F y hy)).toEquiv).symm

-- pin: ordNat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:305)
def ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (-((WithZero.unzero (valued_apply_ne_zero F y v)).toAdd)).toNat

-- pin: valued_eq_exp_neg_ordNat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:308)
theorem valued_eq_exp_neg_ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = WithZero.exp (-(ordNat F y v : ℤ)) := by
  have hle : (WithZero.unzero (valued_apply_ne_zero F y v)).toAdd ≤ 0 := by
    have := (mem_adicCompletionIntegers _ _ _).mp (hy v)
    rwa [← WithZero.coe_unzero (valued_apply_ne_zero F y v), ← WithZero.coe_one,
      WithZero.coe_le_coe, ← ofAdd_toAdd (WithZero.unzero _),
      show (1 : Multiplicative ℤ) = Multiplicative.ofAdd (0 : ℤ) from rfl,
      Multiplicative.ofAdd_le] at this
  rw [ordNat, Int.toNat_of_nonneg (neg_nonneg.mpr hle), neg_neg, WithZero.exp,
    ofAdd_toAdd, WithZero.coe_unzero]

-- pin: toAdd_unzero_eq_neg_ordNat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:321)
theorem toAdd_unzero_eq_neg_ordNat (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) :
    (WithZero.unzero (valued_apply_ne_zero F y v)).toAdd = -(ordNat F y v : ℤ) := by
  have := valued_eq_exp_neg_ordNat F y hy v
  rw [← WithZero.coe_unzero (valued_apply_ne_zero F y v), WithZero.exp,
    WithZero.coe_inj] at this
  rw [← toAdd_ofAdd (-(ordNat F y v : ℤ)), ← this]

-- pin: mem_globalIdeal_iff_forall_mem_pow (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:330)
theorem mem_globalIdeal_iff_forall_mem_pow (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) (r : 𝓞 F) :
    r ∈ globalIdeal F y hy ↔ ∀ v : HeightOneSpectrum (𝓞 F), r ∈ v.asIdeal ^ ordNat F y v := by
  rw [mem_globalIdeal_iff]
  refine forall_congr' fun v => ?_
  have hval : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) v) = v.intValuation r := by
    have h1 : Valued.v ((algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) r) v)
        = Valued.v (algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F r)) := rfl
    rw [h1, valued_algebraMap v r]
  rw [hval, valued_eq_exp_neg_ordNat F y hy v, HeightOneSpectrum.intValuation_le_pow_iff_mem]

-- pin: ordNat_eq_zero_of_isUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:341)
theorem ordNat_eq_zero_of_isUnit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F))
    (hu : IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)) :
    ordNat F y v = 0 := by

  have h1 : Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
    obtain ⟨u, hu⟩ := hu
    have huv : (((u : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) = (y : FiniteAdeleRing (𝓞 F) F) v := congrArg Subtype.val hu
    have huvinv : (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) * (y : FiniteAdeleRing (𝓞 F) F) v = 1 := by
      rw [← huv]; exact_mod_cast u.inv_mul
    refine le_antisymm ((mem_adicCompletionIntegers _ _ _).mp (hy v)) ?_
    have hinvle : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
        : v.adicCompletion F) ≤ 1 :=
      (mem_adicCompletionIntegers _ _ _).mp
        ((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F).2
    have hone : Valued.v (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
        * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) = 1 := by
      rw [← Valuation.map_mul, huvinv, map_one]
    calc (1 : WithZero (Multiplicative ℤ)) = _ := hone.symm
      _ ≤ 1 * Valued.v ((y : FiniteAdeleRing (𝓞 F) F) v) := by gcongr
      _ = _ := one_mul _

  simp only [ordNat]
  rw [show WithZero.unzero (valued_apply_ne_zero F y v) = (1 : Multiplicative ℤ) from by
    rw [← WithZero.coe_inj, WithZero.coe_unzero, h1]; rfl, toAdd_one, neg_zero, Int.toNat_zero]

-- pin: norm_apply_eq_one_of_isUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:371)
theorem norm_apply_eq_one_of_isUnit (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F))
    (hu : IsUnit (⟨(y : FiniteAdeleRing (𝓞 F) F) v, hy v⟩ : v.adicCompletionIntegers F)) :
    ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  rw [NumberField.FinitePlace.norm_def, valued_eq_exp_neg_ordNat F y hy v,
    ordNat_eq_zero_of_isUnit F y hy v hu, Nat.cast_zero, neg_zero,
    show WithZero.exp (0 : ℤ) = (1 : WithZero (Multiplicative ℤ)) from rfl,
    map_one, NNReal.coe_one]

-- pin: absNorm_globalIdeal_mul_finprod_norm (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:381)
theorem absNorm_globalIdeal_mul_finprod_norm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (Ideal.absNorm (globalIdeal F y hy) : ℝ)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  classical
  set S := (finite_support_not_unit F y hy).toFinset with hS

  have hI : globalIdeal F y hy = ∏ v ∈ S, v.asIdeal ^ ordNat F y v := by
    have hinf : globalIdeal F y hy = S.inf (fun v => v.asIdeal ^ ordNat F y v) := by
      ext r
      rw [mem_globalIdeal_iff_forall_mem_pow, Finset.inf_eq_iInf]
      simp only [Ideal.mem_iInf]
      constructor
      · exact fun h v _ => h v
      · intro h v
        by_cases hv : v ∈ S
        · exact h v hv
        · rw [ordNat_eq_zero_of_isUnit F y hy v
            (by simpa [hS, Set.Finite.mem_toFinset] using hv), pow_zero, Ideal.one_eq_top]
          exact trivial
    rw [hinf]
    exact HeightOneSpectrum.inf_pow_eq_prod S (ordNat F y) (fun v => v)
      (fun i _ j _ hij => hij)

  have hN : (Ideal.absNorm (globalIdeal F y hy) : ℝ)
      = ∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℝ)) ^ ordNat F y v := by
    rw [hI, map_prod]
    push_cast
    exact Finset.prod_congr rfl fun v _ => by rw [map_pow]; push_cast; ring

  have hNorm : ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖
      = ∏ v ∈ S, ((Ideal.absNorm v.asIdeal : ℝ)) ^ (-(ordNat F y v : ℤ)) := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S) ?_]
    · refine Finset.prod_congr rfl fun v _ => ?_
      rw [NumberField.FinitePlace.norm_def,
        WithZeroMulInt.toNNReal_neg_apply _ (valued_apply_ne_zero F y v),
        toAdd_unzero_eq_neg_ordNat F y hy v]
      push_cast
      ring
    · intro v hv
      rw [Function.mem_mulSupport] at hv
      rw [Finset.mem_coe, hS, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
      intro hu; exact hv (norm_apply_eq_one_of_isUnit F y hy v hu)

  rw [hN, hNorm, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun v _ => ?_
  have hq : (Ideal.absNorm v.asIdeal : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    ((Ideal.absNorm_ne_zero_iff _).mpr (v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot))
  rw [← zpow_natCast, ← zpow_add₀ hq, add_neg_cancel, zpow_zero]

-- pin: card_zhat_quot_mul_finprod_norm (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:431)
theorem card_zhat_quot_mul_finprod_norm (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (Nat.card (zhatAddSubgroup F ⧸ (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F)) : ℝ)
      * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(y : FiniteAdeleRing (𝓞 F) F) v‖ = 1 := by
  rw [card_zhat_quot_eq_absNorm F y hy]
  exact absNorm_globalIdeal_mul_finprod_norm F y hy

end P6B.JE2aHMod

end RHMODFold_JE2aHMod1

namespace M4aS4

attribute [local instance] placeBorel infMS finBorel adeleMS

variable {F : Type} [Field F] [NumberField F]

-- pin: HasTransversal (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1017)
def HasTransversal (y : FiniteAdeleRing (𝓞 F) F) : Prop :=
  ∃ T : Finset (FiniteAdeleRing (𝓞 F) F),
    (↑T ⊆ AdelicBox.integralFiniteAdeles (𝓞 F) F) ∧
    ((T.card : ℝ) * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖ = 1) ∧
    (↑T : Set (FiniteAdeleRing (𝓞 F) F)).PairwiseDisjoint
        (fun t => t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)) ∧
    (⋃ t ∈ T, t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F))
        = AdelicBox.integralFiniteAdeles (𝓞 F) F

-- pin: measurableSet_smul_zhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1026)
theorem measurableSet_smul_zhat (y : FiniteAdeleRing (𝓞 F) F) :
    MeasurableSet (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) := by
  rw [← Set.image_smul]
  exact ((AdelicBox.isCompact_integralFiniteAdeles F).image (continuous_const_smul y)).isClosed.measurableSet

-- pin: finMeasure_smul_zhat (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1031)
theorem finMeasure_smul_zhat {y : FiniteAdeleRing (𝓞 F) F} (hT : HasTransversal y) :
    finMeasure F (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) := by
  obtain ⟨T, -, hcard, hdisj, hcover⟩ := hT
  have hmeas : MeasurableSet (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) := measurableSet_smul_zhat y
  have hsum : finMeasure F (AdelicBox.integralFiniteAdeles (𝓞 F) F)
      = ∑ t ∈ T, finMeasure F (t +ᵥ (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)) := by
    conv_lhs => rw [← hcover]
    exact measure_biUnion_finset hdisj fun t _ => hmeas.const_vadd t
  simp only [measure_vadd, Finset.sum_const, nsmul_eq_mul, finMeasure_zhat] at hsum

  have hcard0 : (0 : ℝ) < T.card := by
    rcases (Nat.cast_nonneg (α := ℝ) T.card).eq_or_lt with h | h
    · rw [← h, zero_mul] at hcard; exact absurd hcard zero_ne_one
    · exact h
  have hm : finMeasure F (y • AdelicBox.integralFiniteAdeles (𝓞 F) F) = ((T.card : ℝ≥0∞))⁻¹ := by
    rw [ENNReal.eq_inv_of_mul_eq_one_left hsum.symm, inv_inv]
  have hr : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) = (T.card : ℝ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hcard
  rw [hm, hr, ENNReal.ofReal_inv_of_pos hcard0, ENNReal.ofReal_natCast]

-- pin: distribHaarChar_of_fst_eq_one (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1052)
theorem distribHaarChar_of_fst_eq_one (a : (AdeleRing (𝓞 F) F)ˣ) (ha : (a : AdeleRing (𝓞 F) F).1 = 1)
    (hT : HasTransversal (a : AdeleRing (𝓞 F) F).2) :
    (distribHaarChar (AdeleRing (𝓞 F) F) a : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(a : AdeleRing (𝓞 F) F).2 v‖ := by
  classical
  set y : FiniteAdeleRing (𝓞 F) F := (a : AdeleRing (𝓞 F) F).2 with hy
  have hr0 : 0 ≤ ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖ := finprod_nonneg fun v => norm_nonneg _
  set r : ℝ≥0 := ⟨∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖, hr0⟩ with hrdef
  have hr : ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖) = (r : ℝ≥0∞) :=
    ENNReal.ofReal_eq_coe_nnreal hr0
  have hs₀ : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ 0 :=
    adelicMeasure_refSet_ne_zero F
  have hsfin : adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) ≠ ⊤ :=
    adelicMeasure_refSet_ne_top F

  have hsplit : (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (show Set (AdeleRing (𝓞 F) F) from
          ((Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
            (y • AdelicBox.integralFiniteAdeles (𝓞 F) F))) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, ⟨z.2, hz.2, rfl⟩⟩
      show ((a : AdeleRing (𝓞 F) F) * z).1 ∈ _
      rw [show ((a : AdeleRing (𝓞 F) F) * z).1 = (a : AdeleRing (𝓞 F) F).1 * z.1 from rfl, ha, one_mul]
      exact hz.1
    · rintro ⟨hx1, ⟨z2, hz2, hxz2⟩⟩
      refine ⟨(show AdeleRing (𝓞 F) F from ((show InfiniteAdeleRing F from x.1), z2)), ⟨hx1, hz2⟩,
        Prod.ext ?_ ?_⟩
      · show (a : AdeleRing (𝓞 F) F).1 * x.1 = x.1
        rw [ha, one_mul]
      · show (a : AdeleRing (𝓞 F) F).2 * z2 = x.2
        exact hxz2
  have hcompute : (archMeasure F).prod (finMeasure F)
      (((Set.univ.pi fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1) ×ˢ
        (y • AdelicBox.integralFiniteAdeles (𝓞 F) F)))
      = ENNReal.ofReal (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖y v‖)
        * (archMeasure F).prod (finMeasure F) (refSet F) := by
    unfold refSet
    rw [Measure.prod_prod, Measure.prod_prod, finMeasure_smul_zhat hT, finMeasure_zhat, mul_one, mul_comm]
  have hμgs : adelicMeasure F (a • (show Set (AdeleRing (𝓞 F) F) from refSet F))
      = (r : ℝ≥0∞) * adelicMeasure F (show Set (AdeleRing (𝓞 F) F) from refSet F) := by
    rw [hsplit, ← hr]
    exact hcompute
  have key := distribHaarChar_eq_of_measure_smul_eq_mul (μ := adelicMeasure F)
    (s := (show Set (AdeleRing (𝓞 F) F) from refSet F)) (g := a) hs₀ hsfin hμgs
  rw [key]
  rfl

end M4aS4

section RHMODFold_JE2aHMod1b

namespace P6B
namespace JE2aHMod

variable (F : Type) [Field F] [NumberField F]

-- pin: coe_ySmulZhat_eq_smul (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1122)
theorem coe_ySmulZhat_eq_smul (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    (ySmulZhat F y hy : Set (FiniteAdeleRing (𝓞 F) F))
      = (y : FiniteAdeleRing (𝓞 F) F) • integralFiniteAdeles (𝓞 F) F := by
  rw [← smul_integralFiniteAdeles_eq_ySmulZhat F y hy, ← Set.image_smul]
  rfl

-- pin: hasTransversal (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1129)
theorem hasTransversal (y : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hy : (y : FiniteAdeleRing (𝓞 F) F) ∈ integralFiniteAdeles (𝓞 F) F) :
    M4aS4.HasTransversal (y : FiniteAdeleRing (𝓞 F) F) := by
  classical
  set H := (ySmulZhat F y hy).addSubgroupOf (zhatAddSubgroup F) with hH
  have hquotFinite : Finite (zhatAddSubgroup F ⧸ H) := finite_zhat_quot_ySmulZhat F y hy
  have hquotFintype : Fintype (zhatAddSubgroup F ⧸ H) := Fintype.ofFinite _

  set T : Finset (FiniteAdeleRing (𝓞 F) F) :=
    Finset.univ.image (fun c : zhatAddSubgroup F ⧸ H =>
      ((Quotient.out c : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F))
    with hT
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  ·
    intro t ht
    simp only [hT, Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
      true_and] at ht
    obtain ⟨c, rfl⟩ := ht
    exact (Quotient.out c).2
  ·
    have hcard : T.card = Nat.card (zhatAddSubgroup F ⧸ H) := by
      rw [hT, Finset.card_image_of_injective _ ?_, Finset.card_univ, Nat.card_eq_fintype_card]
      intro c₁ c₂ heq
      have : (Quotient.out c₁ : zhatAddSubgroup F) = Quotient.out c₂ :=
        Subtype.val_injective heq
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂, this]
    rw [hcard]
    exact card_zhat_quot_mul_finprod_norm F y hy
  ·
    rw [← coe_ySmulZhat_eq_smul F y hy]
    intro t₁ ht₁ t₂ ht₂ hne
    simp only [hT, Finset.coe_image, Set.mem_image, Finset.coe_univ, Set.mem_univ,
      true_and] at ht₁ ht₂
    obtain ⟨c₁, rfl⟩ := ht₁; obtain ⟨c₂, rfl⟩ := ht₂
    rw [Function.onFun, Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem]
    rintro w ⟨⟨a₁, ha₁, hw₁⟩, ⟨a₂, ha₂, hw₂⟩⟩

    apply hne

    have h₁ : ((Quotient.out c₁ : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) + a₁ = w := hw₁
    have h₂ : ((Quotient.out c₂ : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F) + a₂ = w := hw₂
    have hdiff : ((Quotient.out c₁ - Quotient.out c₂ : zhatAddSubgroup F)
        : FiniteAdeleRing (𝓞 F) F) ∈ ySmulZhat F y hy := by
      have hsub : ((Quotient.out c₁ - Quotient.out c₂ : zhatAddSubgroup F)
          : FiniteAdeleRing (𝓞 F) F) = a₂ - a₁ := by
        push_cast
        linear_combination h₁ - h₂
      rw [hsub]; exact (ySmulZhat F y hy).sub_mem ha₂ ha₁
    have : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂, QuotientAddGroup.eq_iff_sub_mem]
      exact hdiff
    rw [this]
  ·
    rw [← coe_ySmulZhat_eq_smul F y hy]
    apply Set.Subset.antisymm
    · rintro w ⟨_, ⟨t, rfl⟩, _, ⟨ht, rfl⟩, ⟨a, ha, rfl⟩⟩
      simp only [hT, Finset.mem_image, Finset.mem_univ, true_and] at ht
      obtain ⟨c, rfl⟩ := ht
      simp only [vadd_eq_add]
      exact add_mem (Quotient.out c).2 (ySmulZhat_le_zhat F y hy ha)
    · intro z hz
      set zc : zhatAddSubgroup F := ⟨z, hz⟩
      refine Set.mem_iUnion₂.mpr ⟨((Quotient.out (⟦zc⟧ : zhatAddSubgroup F ⧸ H)
        : zhatAddSubgroup F) : FiniteAdeleRing (𝓞 F) F), ?_, ?_⟩
      · exact Finset.mem_image.mpr ⟨⟦zc⟧, Finset.mem_univ _, rfl⟩
      · refine ⟨z - ((Quotient.out (⟦zc⟧ : _ ⧸ H) : zhatAddSubgroup F) : _), ?_, by
          simp [vadd_eq_add]⟩

        have : zc - Quotient.out (⟦zc⟧ : _ ⧸ H) ∈ H :=
          QuotientAddGroup.eq_iff_sub_mem.mp (Quotient.out_eq _).symm
        exact this

end P6B.JE2aHMod

end RHMODFold_JE2aHMod1b

section RHMODFold_JE2aHMod3

open M4aS4 P6B.JE2aFlat

namespace P6B
namespace JE2aHMod

variable {F : Type} [Field F] [NumberField F]

-- pin: finUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1229)
def finUnit (u : (FiniteAdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ where
  val := (show AdeleRing (𝓞 F) F from ((1 : InfiniteAdeleRing F), (u : FiniteAdeleRing (𝓞 F) F)))
  inv := (show AdeleRing (𝓞 F) F from
    ((1 : InfiniteAdeleRing F), ((u⁻¹ : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)))
  val_inv := Prod.ext (one_mul 1) u.mul_inv
  inv_val := Prod.ext (one_mul 1) u.inv_mul

-- pin: finUnit_fst (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1236)
theorem finUnit_fst (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((finUnit u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 := rfl

-- pin: finUnit_snd (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1239)
theorem finUnit_snd (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    ((finUnit u : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = u := rfl

-- pin: finUnit_mul (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1242)
theorem finUnit_mul (u v : (FiniteAdeleRing (𝓞 F) F)ˣ) : finUnit (u * v) = finUnit u * finUnit v :=
  Units.ext (Prod.ext (one_mul (1 : InfiniteAdeleRing F)).symm rfl)

-- pin: finPartUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1245)
def finPartUnit (x : (AdeleRing (𝓞 F) F)ˣ) : (FiniteAdeleRing (𝓞 F) F)ˣ where
  val := (x : AdeleRing (𝓞 F) F).2
  inv := ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2
  val_inv := by
    have h := congrArg Prod.snd x.mul_inv
    exact h
  inv_val := by
    have h := congrArg Prod.snd x.inv_mul
    exact h

-- pin: archUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1255)
def archUnit (x : (AdeleRing (𝓞 F) F)ˣ) : (AdeleRing (𝓞 F) F)ˣ := x * (finUnit (finPartUnit x))⁻¹

-- pin: eq_archUnit_mul_finUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1257)
theorem eq_archUnit_mul_finUnit (x : (AdeleRing (𝓞 F) F)ˣ) : x = archUnit x * finUnit (finPartUnit x) :=
  (inv_mul_cancel_right x _).symm

-- pin: archUnit_fst (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1260)
theorem archUnit_fst (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((archUnit x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = (x : AdeleRing (𝓞 F) F).1 := by
  show (x : AdeleRing (𝓞 F) F).1 * (1 : InfiniteAdeleRing F) = (x : AdeleRing (𝓞 F) F).1
  exact mul_one _

-- pin: archUnit_snd (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1265)
theorem archUnit_snd (x : (AdeleRing (𝓞 F) F)ˣ) :
    ((archUnit x : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  show (x : AdeleRing (𝓞 F) F).2 * ((x⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1
  have h := congrArg Prod.snd x.mul_inv
  exact h

-- pin: hasFiniteMulSupport_norm (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1271)
theorem hasFiniteMulSupport_norm (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (fun v : HeightOneSpectrum (𝓞 F) => ‖(u : FiniteAdeleRing (𝓞 F) F) v‖).HasFiniteMulSupport :=
  hasFiniteMulSupport_norm_finComp (finUnit u)

-- pin: finprod_norm_pos (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1275)
theorem finprod_norm_pos (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    0 < ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ :=
  finprod_induction (fun r : ℝ => 0 < r) one_pos (fun _ _ => mul_pos)
    fun v => norm_pos_iff.mpr (finComp_ne_zero (finUnit u) v)

-- pin: finprod_norm_mul (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1280)
theorem finprod_norm_mul (u w : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖((u * w : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) v‖)
      = (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖)
        * ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(w : FiniteAdeleRing (𝓞 F) F) v‖ := by
  rw [← finprod_mul_distrib (hasFiniteMulSupport_norm u) (hasFiniteMulSupport_norm w)]
  refine finprod_congr fun v => ?_
  rw [Units.val_mul, show ((u : FiniteAdeleRing (𝓞 F) F) * (w : FiniteAdeleRing (𝓞 F) F)) v
      = (u : FiniteAdeleRing (𝓞 F) F) v * (w : FiniteAdeleRing (𝓞 F) F) v from rfl, norm_mul]

-- pin: distribHaarChar_finUnit_of_hasTransversal (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1289)
theorem distribHaarChar_finUnit_of_hasTransversal (w : (FiniteAdeleRing (𝓞 F) F)ˣ)
    (hw : HasTransversal (w : FiniteAdeleRing (𝓞 F) F)) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (finUnit w) : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(w : FiniteAdeleRing (𝓞 F) F) v‖ :=
  distribHaarChar_of_fst_eq_one (finUnit w) rfl hw

-- pin: distribHaarChar_finUnit (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1295)
theorem distribHaarChar_finUnit
    (hT : ∀ y : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (y : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F →
        HasTransversal (y : FiniteAdeleRing (𝓞 F) F))
    (u : (FiniteAdeleRing (𝓞 F) F)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 F) F) (finUnit u) : ℝ)
      = ∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(u : FiniteAdeleRing (𝓞 F) F) v‖ := by

  obtain ⟨s, hs0, hsu⟩ :=
    AdelicBox.exists_mul_mem_integralFiniteAdeles (𝓞 F) F (u : FiniteAdeleRing (𝓞 F) F)
  have hsK : algebraMap (𝓞 F) F s ≠ 0 := fun h =>
    hs0 ((injective_iff_map_eq_zero _).mp (IsFractionRing.injective (𝓞 F) F) s h)
  have hsA : IsUnit (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F)]
    exact (isUnit_iff_ne_zero.mpr hsK).map _
  obtain ⟨sU, hsUval⟩ : ∃ sU : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (sU : FiniteAdeleRing (𝓞 F) F) = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) s :=
    ⟨hsA.unit, hsA.unit_spec⟩

  have hsZ : (sU : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
    intro v
    rw [hsUval]
    change algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F s) ∈ _
    exact algebraMap_mem_adicCompletionIntegers v s
  have hsuZ : ((sU * u : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F := by
    rw [Units.val_mul, hsUval]
    exact hsu

  have h1 := distribHaarChar_finUnit_of_hasTransversal (sU * u) (hT (sU * u) hsuZ)
  have h2 := distribHaarChar_finUnit_of_hasTransversal sU (hT sU hsZ)
  rw [finUnit_mul, map_mul, NNReal.coe_mul, h2, finprod_norm_mul] at h1
  exact mul_left_cancel₀ (finprod_norm_pos sU).ne' h1

-- pin: distribHaarChar_eq_placeModulus (S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean:1329)
theorem distribHaarChar_eq_placeModulus
    (hT : ∀ y : (FiniteAdeleRing (𝓞 F) F)ˣ,
      (y : FiniteAdeleRing (𝓞 F) F) ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F →
        HasTransversal (y : FiniteAdeleRing (𝓞 F) F))
    (x : (AdeleRing (𝓞 F) F)ˣ) :
    (distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ) = placeModulus F x := by
  conv_lhs => rw [eq_archUnit_mul_finUnit x]
  rw [map_mul, NNReal.coe_mul,
    M4aS4.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one (archUnit x) (archUnit_snd x),
    distribHaarChar_finUnit hT]
  simp only [archUnit_fst]
  rfl

end P6B.JE2aHMod

end RHMODFold_JE2aHMod3
