/-
  The residual unramified-Weyl prelude: the declarations the pin's two
  `AutomorphicForm.LocalIntertwining` files re-carry and the T1 port did not need.

  This is the companion of `TateGlobal/WeylPrelude.lean` (Set 0's definition layer).
  Everything here is read off the pin's `FinGKFold_LocalZetaUnramified` /
  `FinGKFold_ValuedOrdBridge` / `FinGKFold_WeylGK` sections of
  `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
  and of the `_smooth_` sibling, and it is homed once here for both sets. LI-2
  (`…_smooth…`) imports this module rather than re-carrying the text.

  The generic block (`ordA_unit`, `map_maximalIdeal_ringEquiv`, `ordA_ringEquiv`,
  `ord_surjective`, `ord_units_map_of_mem_decompositionSubgroup`) mathematically belongs
  beside the rest of the `ord` API in `RingTheory/DiscreteValuationRing/Order.lean`; that
  module is frozen, so it sits here until the refactor round moves it. It is written in
  this module's own namespace rather than in `IsDiscreteValuationRing`, because that
  namespace prefix would capture the unqualified `maximalIdeal` (mathlib has both
  `IsLocalRing.maximalIdeal` and `IsDiscreteValuationRing.maximalIdeal`, the latter a
  `HeightOneSpectrum`) and the pin's statements say `maximalIdeal A`. The pin keeps
  `ordA_unit`/`map_maximalIdeal_ringEquiv`/`ordA_ringEquiv` `private` in every file; the
  port writes them once, publicly, because LI-2 consumes them.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib `v4.34.0`. Names are the pin's
  (prefix-stripped) except the recorded `ValuationOrd.ord` →
  `IsDiscreteValuationRing.ord` rename.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.WeylPrelude
-- `ValuationSubring.decompositionSubgroup`, used by the `ord`-refinement block below; also
-- reached transitively through `WeylPrelude`, imported explicitly to keep the dependency visible.
import Mathlib.RingTheory.Valuation.RamificationGroup

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing Set
open WithZero Multiplicative
open scoped NNReal ENNReal Pointwise
open LanglandsTunnell.TateLocal

noncomputable section

namespace NumberField

namespace TateGlobal

namespace WeylShell

open WeylPrelude LocalZetaUnramified MulHaarFromAdditive ValuedOrdBridge
-- only the `ord` API, not the whole namespace: `IsDiscreteValuationRing.maximalIdeal` is a
-- `HeightOneSpectrum` and would shadow the `Ideal`-valued `maximalIdeal` the pin's
-- statements use.
open IsDiscreteValuationRing (ord ordA ordZ ord_spec ordA_span ordA_unique ordA_mul
  ordZ_spec exists_rep coe_mk_ne_zero ord_eq_zero_iff ord_ofMul_of_mem
  ord_ofMul_mk0_of_irreducible)
open _root_.Ideal

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

section ValuationOrd

variable {L : Type*} [Field L] (A : ValuationSubring L) [IsDiscreteValuationRing A]

-- pin: ordA_unit (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:70)
theorem ordA_unit (u : Aˣ) : ordA A (u : A) = 0 :=
  ordA_unique A u.ne_zero (by rw [span_singleton_eq_top.mpr u.isUnit, pow_zero, one_eq_top])

omit [IsDiscreteValuationRing ↥A] in
-- pin: map_maximalIdeal_ringEquiv (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:223)
theorem map_maximalIdeal_ringEquiv (e : A ≃+* A) :
    Ideal.map (e : A →+* A) (maximalIdeal A) = maximalIdeal A := by
  have key : ∀ f : A ≃+* A, Ideal.map (f : A →+* A) (maximalIdeal A) ≤ maximalIdeal A := by
    intro f
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [mem_comap, mem_maximalIdeal, mem_nonunits_iff]
    rw [mem_maximalIdeal, mem_nonunits_iff] at hy
    intro hu
    exact hy (by simpa using hu.map f.symm.toRingHom)
  refine le_antisymm (key e) ?_
  intro y hy
  have : e.symm y ∈ maximalIdeal A := by
    have := key e.symm
    rw [Ideal.map_le_iff_le_comap] at this
    exact this hy
  simpa using mem_map_of_mem (e : A →+* A) this

-- pin: ordA_ringEquiv (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:241)
theorem ordA_ringEquiv (e : A ≃+* A) {a : A} (ha : a ≠ 0) :
    ordA A (e a) = ordA A a := by
  have hea : e a ≠ 0 := by
    intro h0
    exact ha (by simpa using congrArg e.symm h0)
  refine ordA_unique A hea ?_
  have hmap : span {e a} = Ideal.map (e : A →+* A) (span {a}) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  rw [hmap, ordA_span A ha, Ideal.map_pow, map_maximalIdeal_ringEquiv A e]

-- pin: ord_surjective (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:168)
theorem ord_surjective : Function.Surjective (ord A) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have h0 : ((ϖ : A) : L) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (Subtype.ext h)
  intro k
  refine ⟨.ofMul ((Units.mk0 ((ϖ : A) : L) h0) ^ k), ?_⟩
  rw [show Additive.ofMul ((Units.mk0 ((ϖ : A) : L) h0) ^ k)
        = k • Additive.ofMul (Units.mk0 ((ϖ : A) : L) h0) from rfl,
    map_zsmul, ord_ofMul_mk0_of_irreducible A hϖ h0, smul_eq_mul, mul_one]

-- pin: ord_units_map_of_mem_decompositionSubgroup (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:252)
theorem ord_units_map_of_mem_decompositionSubgroup {K : Type*} [Field K] [Algebra K L]
    {d : L ≃ₐ[K] L} (hd : d ∈ A.decompositionSubgroup K) (x : Lˣ) :
    ord A (.ofMul (Units.map d.toAlgHom.toRingHom.toMonoidHom x)) = ord A (.ofMul x) := by
  obtain ⟨a, b, ha, hb, hx⟩ := exists_rep A x
  set e : A ≃+* A :=
    MulSemiringAction.toRingEquiv (A.decompositionSubgroup K) A (⟨d, hd⟩ : A.decompositionSubgroup K)
    with he
  have hcoe : ∀ c : A, ((e c : A) : L) = d (c : L) := fun c => rfl
  have hea : e a ≠ 0 := fun h0 => ha (by simpa using congrArg e.symm h0)
  have heb : e b ≠ 0 := fun h0 => hb (by simpa using congrArg e.symm h0)
  have hrep : ((Units.map d.toAlgHom.toRingHom.toMonoidHom x : Lˣ) : L) * ((e b : A) : L)
      = ((e a : A) : L) := by
    rw [hcoe, hcoe]
    have := congrArg d hx
    rw [map_mul] at this
    simpa using this
  have h1 := ordZ_spec A hea heb hrep
  have h2 := ordZ_spec A ha hb hx
  show ordZ A (Units.map d.toAlgHom.toRingHom.toMonoidHom x) = ordZ A x
  rw [h1, h2, ordA_ringEquiv A e ha, ordA_ringEquiv A e hb]

end ValuationOrd

section Shells

variable {ϖ : v.adicCompletionIntegers F}

-- pin: smul_integers_succ_subset (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:664)
theorem smul_integers_succ_subset (hϖ : Irreducible ϖ) (k : ℕ) :
    (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      ⊆ (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro x hx
  obtain ⟨y, hy⟩ := mem_smul_integers_iff.mp hx
  refine mem_smul_integers_iff.mpr ⟨ϖ * y, ?_⟩
  rw [← hy]
  push_cast [pow_succ, piUnit_val]
  ring

-- pin: integers_diff_zero_eq_iUnion (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:788)
theorem integers_diff_zero_eq_iUnion (hϖ : Irreducible ϖ) :
    ((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0}) = ⋃ k : ℕ, shellSet hϖ k := by
  ext x
  constructor
  · rintro ⟨hxO, hx0⟩
    have hx : x ≠ 0 := hx0
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible
      (x := (⟨x, hxO⟩ : v.adicCompletionIntegers F)) (fun h => hx (by
        simpa using congrArg (Subtype.val) h)) hϖ
    have hspan : Ideal.span {(⟨x, hxO⟩ : v.adicCompletionIntegers F)}
        = maximalIdeal (v.adicCompletionIntegers F) ^ n := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
        Ideal.span_singleton_eq_span_singleton.mpr hn.symm]
    have hord := IsDiscreteValuationRing.ord_ofMul_of_mem (v.adicCompletionIntegers F)
      (x := Units.mk0 x hx) hxO hspan
    exact mem_iUnion.mpr ⟨n, (mem_shellSet_iff_ord_eq hϖ n hx).mpr hord⟩
  · intro hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact ⟨shellSet_subset_integers hϖ k hk,
      fun h => zero_notMem_shellSet hϖ k (h ▸ hk)⟩

end Shells

section Measures

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

set_option linter.overlappingInstances false in
-- pin: measure_smul_integers_pow (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:827)
theorem measure_smul_integers_pow (hϖ : Irreducible ϖ) (k : ℕ) :
    μ (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        • (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (normQ v ^ (-(k : ℤ)) : ℝ≥0) * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have h := LocalHaarModulus.measure_smul_integers μ (piUnit hϖ ^ k)
  rwa [ord_piUnit_pow] at h

set_option linter.overlappingInstances false in
-- pin: measure_shellSet (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:834)
theorem measure_shellSet (hϖ : Irreducible ϖ) (k : ℕ) :
    μ (shellSet hϖ k)
      = ((normQ v ^ (-(k : ℤ)) * (1 - (normQ v)⁻¹) : ℝ≥0) : ℝ≥0∞)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hsub := smul_integers_succ_subset hϖ k
  have hfin : μ (((piUnit hϖ ^ (k + 1) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      • (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ≠ ∞ := by
    rw [measure_smul_integers_pow μ hϖ]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_integers_lt_top μ).ne
  rw [shellSet, measure_sdiff hsub ((measurableSet_smul_integers _).nullMeasurableSet) hfin,
    measure_smul_integers_pow μ hϖ, measure_smul_integers_pow μ hϖ]
  rw [← ENNReal.sub_mul (fun _ _ => (measure_integers_lt_top μ).ne)]
  congr 1
  rw [← ENNReal.coe_sub]
  congr 1
  rw [mul_tsub, mul_one]
  congr 1
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, pow_succ, mul_inv]

end Measures

section Integrand

variable {ϖ : v.adicCompletionIntegers F}

-- pin: charExt_of_mem_shellSet (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:867)
theorem charExt_of_mem_shellSet (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    {k : ℕ} {x : v.adicCompletion F} (hx : x ∈ shellSet hϖ k) :
    charExt χ x = (charExt χ ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F)) ^ k := by
  have hx0 : x ≠ 0 := fun h => zero_notMem_shellSet hϖ k (h ▸ hx)
  have hord := (mem_shellSet_iff_ord_eq hϖ k hx0).mp hx
  set w : (v.adicCompletion F)ˣ := Units.mk0 x hx0 * (piUnit hϖ ^ k)⁻¹ with hwdef
  have hword : IsDiscreteValuationRing.ord (v.adicCompletionIntegers F) (Additive.ofMul w) = 0 := by
    have hsub : Additive.ofMul w = Additive.ofMul (Units.mk0 x hx0)
        - Additive.ofMul (piUnit hϖ ^ k) := rfl
    rw [hsub, map_sub, hord, ord_piUnit_pow, sub_self]
  have hχw : χ w = 1 := hχ w ((IsDiscreteValuationRing.ord_eq_zero_iff _ _).mp hword)
  have hfac : Units.mk0 x hx0 = piUnit hϖ ^ k * w := by
    rw [hwdef, mul_comm (Units.mk0 x hx0) ((piUnit hϖ ^ k)⁻¹), mul_inv_cancel_left]
  rw [charExt_of_ne_zero χ hx0, hfac, map_mul, hχw, mul_one, map_pow]
  have hϖ0 := coe_ne_zero_of_irreducible hϖ
  rw [charExt_of_ne_zero χ hϖ0]
  norm_cast

-- A file-local copy of the pin's `ofReal_pow_cpow` (line 888 of the same file), whose
-- statement is `(((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k`. The port already has a
-- `ofReal_pow_cpow` in `NumberField/CompletedDedekindZeta/Mellin.lean`, but it is a different
-- statement (`((a : ℂ) ^ n) ^ z = (a : ℂ) ^ (n * z)`) and that module is not on the import
-- path here, so the pin's 8-line proof is re-run locally rather than dragging in the olean.
-- pin: ofReal_pow_cpow (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:888)
private theorem ofReal_pow_cpow {a : ℝ} (ha : 0 ≤ a) (s : ℂ) (k : ℕ) :
    (((a ^ k : ℝ)) : ℂ) ^ s = (((a : ℝ) : ℂ) ^ s) ^ k := by
  induction k with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (pow_nonneg ha n) ha, ih,
        pow_succ]

-- pin: cpow_qpow_bridge (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:896)
theorem cpow_qpow_bridge (s : ℂ) (k : ℕ) :
    ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ) : ℂ) ^ s
      = ((((normQ v : ℝ≥0) : ℝ) : ℂ) ^ (-s)) ^ k := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hq0 : (0 : ℝ) < ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast lt_of_lt_of_le one_pos hq1
  have hinv : ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ)) = (((normQ v : ℝ≥0) : ℝ))⁻¹ ^ k := by
    push_cast
    rw [zpow_neg, zpow_natCast, inv_pow]
  rw [show ((((normQ v) ^ (-(k : ℤ)) : ℝ≥0) : ℝ) : ℂ)
        = (((((normQ v : ℝ≥0) : ℝ))⁻¹ ^ k : ℝ) : ℂ) by exact_mod_cast congrArg Complex.ofReal hinv]
  rw [ofReal_pow_cpow (inv_nonneg.mpr hq0.le) s k]
  congr 1
  push_cast
  rw [Complex.inv_cpow _ _
      (by rw [Complex.natCast_arg]; exact Ne.symm Real.pi_ne_zero),
    ← Complex.cpow_neg]

end Integrand

section Zeta

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {ϖ : v.adicCompletionIntegers F}

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

omit [μ.IsAddHaarMeasure] [μ.Regular] in
-- pin: mulMeasure_restrict_shellSet (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:927)
theorem mulMeasure_restrict_shellSet (hϖ : Irreducible ϖ) (k : ℕ) :
    (mulMeasure μ).restrict (shellSet hϖ k)
      = ((normQ v ^ (k : ℤ) : ℝ≥0) : ℝ≥0∞) • μ.restrict (shellSet hϖ k) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hqne : (normQ v : ℝ≥0) ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  rw [mulMeasure, restrict_withDensity hS, Measure.restrict_restrict hS,
    Set.inter_eq_left.mpr (shellSet_subset_compl_zero hϖ k)]
  rw [withDensity_congr_ae (f := fun x => ((modulus x : ℝ≥0∞))⁻¹)
    (g := fun _ => ((normQ v ^ (k : ℤ) : ℝ≥0) : ℝ≥0∞))
    (by
      rw [Filter.EventuallyEq, ae_restrict_iff' hS]
      refine Filter.Eventually.of_forall fun x hx => ?_
      rw [modulus_of_mem_shellSet hϖ hx, ← ENNReal.coe_inv (by positivity), ← zpow_neg,
        neg_neg])]
  rw [withDensity_const]

set_option linter.overlappingInstances false in
-- pin: setIntegral_shellSet_const (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:944)
theorem setIntegral_shellSet_const (hϖ : Irreducible ϖ) (k : ℕ)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : v.adicCompletion F → E) (c : E)
    (hA : Set.EqOn A (fun _ => c) (shellSet hϖ k)) :
    ∫ x in shellSet hϖ k, A x ∂(mulMeasure μ)
      = ((((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ) * μ.real (v.adicCompletionIntegers F :
          Set (v.adicCompletion F)))) • c := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have hqne : (normQ v : ℝ≥0) ≠ 0 := (lt_of_lt_of_le one_pos hq1).ne'
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  rw [show (∫ x in shellSet hϖ k, A x ∂(mulMeasure μ))
        = ∫ x, A x ∂((mulMeasure μ).restrict (shellSet hϖ k)) from rfl,
    mulMeasure_restrict_shellSet μ hϖ k, integral_smul_measure]
  rw [show (∫ x, A x ∂(μ.restrict (shellSet hϖ k)))
        = ∫ x in shellSet hϖ k, A x ∂μ from rfl,
    setIntegral_congr_fun hS hA, setIntegral_const, smul_smul]
  congr 1
  have hsh : μ.real (shellSet hϖ k)
      = (((normQ v ^ (-(k : ℤ)) * (1 - (normQ v)⁻¹) : ℝ≥0)) : ℝ)
        * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
    show (μ (shellSet hϖ k)).toReal = _
    rw [measure_shellSet μ hϖ k, ENNReal.toReal_mul, ENNReal.coe_toReal]
    rfl
  rw [hsh, ENNReal.coe_toReal, NNReal.coe_mul, NNReal.coe_zpow, NNReal.coe_zpow]
  rw [show ((normQ v : ℝ≥0) : ℝ) ^ (k : ℤ)
        * (((normQ v : ℝ≥0) : ℝ) ^ (-(k : ℤ)) * (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
          * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      = (((normQ v : ℝ≥0) : ℝ) ^ (k : ℤ) * ((normQ v : ℝ≥0) : ℝ) ^ (-(k : ℤ)))
        * ((((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
          * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F))) from by ring]
  rw [← zpow_add₀ (by positivity : ((normQ v : ℝ≥0) : ℝ) ≠ 0)]
  simp

omit [μ.Regular] in
-- pin: mulMeasure_shellSet_lt_top (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:979)
theorem mulMeasure_shellSet_lt_top (hϖ : Irreducible ϖ) (k : ℕ) :
    mulMeasure μ (shellSet hϖ k) < ∞ := by
  have hS := measurableSet_shellSet (F := F) (v := v) hϖ k
  have h1 : mulMeasure μ (shellSet hϖ k)
      = ((mulMeasure μ).restrict (shellSet hϖ k)) (shellSet hϖ k) := by
    rw [Measure.restrict_apply hS, Set.inter_self]
  rw [h1, mulMeasure_restrict_shellSet μ hϖ k, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply hS, Set.inter_self]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top
    (lt_of_le_of_lt (measure_mono (shellSet_subset_integers hϖ k)) (measure_integers_lt_top μ))

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: indicator_integrand (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:992)
theorem indicator_integrand (χ : (v.adicCompletion F)ˣ →* ℂˣ) (s : ℂ)
    (x : v.adicCompletion F) :
    (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ)) x) * charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s
      = Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          (fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s) x := by
  by_cases hx : x ∈ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: eqOn_integrand_shellSet (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1004)
theorem eqOn_integrand_shellSet (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (k : ℕ) :
    Set.EqOn (fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s)
      (fun _ => eulerVar ϖ χ s ^ k) (shellSet hϖ k) := by
  intro x hx
  have h1 := charExt_of_mem_shellSet hϖ hχ hx
  have h2 := modulus_of_mem_shellSet hϖ hx
  simp only
  rw [h1, h2, cpow_qpow_bridge s k, eulerVar, mul_pow]

set_option linter.overlappingInstances false in
-- pin: hasSum_localZeta_indicator (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1017)
theorem hasSum_localZeta_indicator (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (hconv : ‖eulerVar ϖ χ s‖ < 1) :
    HasSum (fun k : ℕ => eulerVar ϖ χ s ^ k
        * (((((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ)
            * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ)) : ℂ))
      (localZeta μ (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ))) χ s) := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  set g : v.adicCompletion F → ℂ :=
    fun y => charExt χ y * (((modulus y : ℝ)) : ℂ) ^ s with hg
  set C : ℝ := (((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ))
    * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) with hC
  have hOmeas : MeasurableSet (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
    (isCompact_integers (F := F) (v := v)).isClosed.measurableSet

  have hze : mulMeasure μ ({0} : Set (v.adicCompletion F)) = 0 := by
    rw [mulMeasure, withDensity_apply _ (measurableSet_singleton (0 : v.adicCompletion F)),
      Measure.restrict_restrict (measurableSet_singleton (0 : v.adicCompletion F)),
      Set.inter_compl_self, Measure.restrict_empty, lintegral_zero_measure]
  have hae : (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      =ᵐ[mulMeasure μ]
        (((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0} :
          Set (v.adicCompletion F))) := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · refine measure_mono_null (fun x hx => ?_) hze
      by_contra hx0
      exact hx.2 ⟨hx.1, hx0⟩
    · have h0 : ((v.adicCompletionIntegers F : Set (v.adicCompletion F)) \ {0})
          \ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) = ∅ :=
        Set.sdiff_eq_empty.mpr Set.sdiff_subset
      rw [h0]
      exact measure_empty
  have hloc : localZeta μ (Set.indicator
        (v.adicCompletionIntegers F : Set (v.adicCompletion F)) (fun _ => (1 : ℂ))) χ s
      = ∫ x in (⋃ k : ℕ, shellSet hϖ k), g x ∂(mulMeasure μ) := by
    rw [localZeta]
    rw [show (∫ x, Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
          (fun _ => (1 : ℂ)) x * charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s ∂(mulMeasure μ))
        = ∫ x, Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F)) g x
            ∂(mulMeasure μ) from
      integral_congr_ae (Filter.Eventually.of_forall fun x => indicator_integrand χ s x)]
    rw [MeasureTheory.integral_indicator hOmeas,
      show ((mulMeasure μ).restrict (v.adicCompletionIntegers F :
          Set (v.adicCompletion F)))
        = ((mulMeasure μ).restrict ((v.adicCompletionIntegers F :
          Set (v.adicCompletion F)) \ {0})) from Measure.restrict_congr_set hae,
      integers_diff_zero_eq_iUnion hϖ]

  have hiOn : ∀ k : ℕ, IntegrableOn g (shellSet hϖ k) (mulMeasure μ) := by
    intro k
    refine (integrableOn_congr_fun (eqOn_integrand_shellSet hϖ hχ s k)
      (measurableSet_shellSet hϖ k)).mpr ?_
    exact integrableOn_const ((mulMeasure_shellSet_lt_top μ hϖ k).ne)
  have hnorm : ∀ k : ℕ,
      (∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ)) = ‖eulerVar ϖ χ s‖ ^ k * C := by
    intro k
    have heq : Set.EqOn (fun y => ‖g y‖) (fun _ => ‖eulerVar ϖ χ s ^ k‖)
        (shellSet hϖ k) := fun x hx => by
      have h' : charExt χ x * (((modulus x : ℝ)) : ℂ) ^ s = eulerVar ϖ χ s ^ k :=
        eqOn_integrand_shellSet hϖ hχ s k hx
      simp only [hg]
      rw [h']
    rw [setIntegral_shellSet_const μ hϖ k _ _ heq, smul_eq_mul, norm_pow, mul_comm]
  have hsummable : Summable fun k : ℕ => ∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ) := by
    rw [show (fun k : ℕ => ∫ x in shellSet hϖ k, ‖g x‖ ∂(mulMeasure μ))
        = fun k : ℕ => ‖eulerVar ϖ χ s‖ ^ k * C from funext hnorm]
    exact (summable_geometric_of_lt_one (norm_nonneg _) hconv).mul_right C
  have hInt : IntegrableOn g (⋃ k : ℕ, shellSet hϖ k) (mulMeasure μ) :=
    MeasureTheory.integrableOn_iUnion_of_summable_integral_norm hiOn hsummable
  have hshellval : ∀ k : ℕ,
      (∫ x in shellSet hϖ k, g x ∂(mulMeasure μ)) = eulerVar ϖ χ s ^ k * (C : ℂ) := by
    intro k
    rw [setIntegral_shellSet_const μ hϖ k _ _ (eqOn_integrand_shellSet hϖ hχ s k)]
    rw [Complex.real_smul, mul_comm]
  have hsum := MeasureTheory.hasSum_integral_iUnion
    (fun k => measurableSet_shellSet hϖ k)
    (shellSet_disjoint hϖ) hInt
  rw [show (fun k : ℕ => ∫ x in shellSet hϖ k, g x ∂(mulMeasure μ))
      = fun k : ℕ => eulerVar ϖ χ s ^ k * (C : ℂ) from funext hshellval] at hsum
  rw [hloc]
  exact hsum

set_option linter.overlappingInstances false in
-- pin: localZeta_indicator_integers (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1103)
theorem localZeta_indicator_integers (hϖ : Irreducible ϖ)
    {χ : (v.adicCompletion F)ˣ →* ℂˣ}
    (hχ : ∀ w : (v.adicCompletion F)ˣ,
      w ∈ (Units.map ((v.adicCompletionIntegers F).subtype.toMonoidHom)).range → χ w = 1)
    (s : ℂ) (hconv : ‖eulerVar ϖ χ s‖ < 1) :
    localZeta μ (Set.indicator (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        (fun _ => (1 : ℂ))) χ s
      = ((μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) : ℝ) : ℂ)
        * (1 - ((((normQ v : ℝ≥0) : ℝ)) : ℂ)⁻¹) * (1 - eulerVar ϖ χ s)⁻¹ := by
  have hq1 : (1 : ℝ≥0) ≤ normQ v := one_le_normQ
  have h := (hasSum_localZeta_indicator μ hϖ hχ s hconv).tsum_eq
  rw [← h, tsum_mul_right, tsum_geometric_of_norm_lt_one hconv]
  have hqR : (1 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := by exact_mod_cast hq1
  have hsub : (((1 - (normQ v)⁻¹ : ℝ≥0) : ℝ))
      = 1 - (((normQ v : ℝ≥0) : ℝ))⁻¹ := by
    rw [NNReal.coe_sub (by
      rw [inv_le_one_iff₀]
      right
      exact hq1)]
    push_cast
    ring
  rw [hsub]
  push_cast
  ring

end Zeta

section ValuedOrdBridge

variable {ϖ : v.adicCompletionIntegers F}

-- pin: valued_coe_ne_zero (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1528)
theorem valued_coe_ne_zero (x : (v.adicCompletion F)ˣ) :
    Valued.v ((x : (v.adicCompletion F)ˣ) : v.adicCompletion F) ≠ 0 :=
  valued_ne_zero_of_ne_zero x.ne_zero

-- pin: valued_zpow_piUnit (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1705)
theorem valued_zpow_piUnit (hϖ : Irreducible ϖ) (k : ℤ) :
    Valued.v (((piUnit hϖ ^ k : (v.adicCompletion F)ˣ)) : v.adicCompletion F)
      = WithZero.exp (-k) := by
  rw [valued_coe_units_eq_exp_neg_ord, ord_ofMul_zpow_piUnit hϖ]

end ValuedOrdBridge

section WeylGK

variable [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)]

variable {π : v.adicCompletionIntegers F}

variable {χ : (v.adicCompletion F)ˣ →* ℂˣ}

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: charExt_inv_of_mem_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1844)
theorem charExt_inv_of_mem_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    {m : ℕ} {x : v.adicCompletion F} (hx : x ∈ negShell hπ m) :
    charExt χ⁻¹ x = ((χ (piUnit hπ) : ℂˣ) : ℂ) ^ (m + 1) := by
  have hx0 : x ≠ 0 := ne_zero_of_mem_negShell hπ hx
  rw [charExt_of_ne_zero χ⁻¹ hx0, MonoidHom.inv_apply,
    char_eq_zpow_of_ord hπ hχ (Units.mk0 x hx0) _ (ord_of_mem_negShell hπ hx hx0),
    ← zpow_neg, neg_neg, show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    Units.val_pow_eq_pow_val]

omit [MeasurableSpace (v.adicCompletion F)] [BorelSpace (v.adicCompletion F)] in
-- pin: integrand_eqOn_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1856)
theorem integrand_eqOn_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    Set.EqOn (fun y => charExt χ⁻¹ y * (((modulus y : ℝ)) : ℂ) ^ w)
      (fun _ => (((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w) ^ (m + 1))
      (negShell hπ m) := by
  intro x hx
  have hq0 : (0 : ℝ) ≤ ((normQ v : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  simp only
  rw [charExt_inv_of_mem_negShell hπ hχ hx, modulus_of_mem_negShell hπ hx, NNReal.coe_pow,
    ofReal_pow_cpow hq0 w (m + 1), mul_pow]

variable (μ : Measure (v.adicCompletion F)) [μ.IsAddHaarMeasure] [μ.Regular]

set_option linter.overlappingInstances false in
-- pin: measure_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1870)
theorem measure_negShell (hπ : Irreducible π) (m : ℕ) :
    μ (negShell hπ m)
      = ((normQ v ^ (m + 1) * (1 - (normQ v)⁻¹) : ℝ≥0) : ℝ≥0∞)
        * μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  have hΔ : distribHaarChar (v.adicCompletion F) (piUnit hπ ^ (-((m : ℤ) + 1)))
      = normQ v ^ (m + 1) := by
    rw [LocalHaarModulus.distribHaarChar_adicCompletion, ord_ofMul_zpow_piUnit hπ, neg_neg,
      show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have h0 := measure_shellSet μ hπ 0
  rw [show (-((0 : ℕ) : ℤ)) = 0 from by simp, zpow_zero, one_mul] at h0
  rw [negShell, genShell, measure_units_smul μ (piUnit hπ ^ (-((m : ℤ) + 1))) (shellSet hπ 0), hΔ, h0,
    ← mul_assoc, ← ENNReal.coe_mul]

omit [BorelSpace (v.adicCompletion F)] [μ.Regular] in
-- pin: measure_integers_lt_top' (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1884)
theorem measure_integers_lt_top' : μ (v.adicCompletionIntegers F : Set (v.adicCompletion F)) < ∞ :=
  (isCompact_integers (F := F) (v := v)).measure_lt_top

set_option linter.overlappingInstances false in
-- pin: measure_negShell_lt_top (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1887)
theorem measure_negShell_lt_top (hπ : Irreducible π) (m : ℕ) : μ (negShell hπ m) < ∞ := by
  rw [measure_negShell μ hπ m]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (measure_integers_lt_top' μ)

set_option linter.overlappingInstances false in
-- pin: measureReal_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1891)
theorem measureReal_negShell (hπ : Irreducible π) (m : ℕ) :
    μ.real (negShell hπ m)
      = ((normQ v : ℝ≥0) : ℝ) ^ (m + 1) * (((1 - (normQ v)⁻¹ : ℝ≥0)) : ℝ)
        * μ.real (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  rw [measureReal_def, measure_negShell μ hπ m, ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_mul,
    NNReal.coe_pow, measureReal_def]

omit [μ.IsAddHaarMeasure] [μ.Regular] in
-- pin: setIntegral_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1900)
theorem setIntegral_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    ∫ x in negShell hπ m, charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w ∂μ
      = ((μ.real (negShell hπ m) : ℝ) : ℂ)
        * (((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w) ^ (m + 1) := by
  rw [setIntegral_congr_fun (measurableSet_negShell hπ m) (integrand_eqOn_negShell hπ hχ w m),
    setIntegral_const, Complex.real_smul]

omit [μ.IsAddHaarMeasure] [μ.Regular] in
-- pin: setIntegral_norm_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1911)
theorem setIntegral_norm_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    ∫ x in negShell hπ m, ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w‖ ∂μ
      = μ.real (negShell hπ m)
        * ‖((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w‖ ^ (m + 1) := by
  have heq : Set.EqOn (fun x => ‖charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w‖)
      (fun _ => ‖((χ (piUnit hπ) : ℂˣ) : ℂ) * ((((normQ v : ℝ≥0) : ℝ) : ℂ)) ^ w‖ ^ (m + 1))
      (negShell hπ m) := by
    intro x hx
    have h := integrand_eqOn_negShell hπ hχ w m hx
    simp only at h ⊢
    rw [h, norm_pow]
  rw [setIntegral_congr_fun (measurableSet_negShell hπ m) heq, setIntegral_const, smul_eq_mul]

set_option linter.overlappingInstances false in
-- pin: integrableOn_negShell (S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean:1926)
theorem integrableOn_negShell (hπ : Irreducible π)
    (hχ : ∀ u : (v.adicCompletion F)ˣ, Valued.v (u : v.adicCompletion F) = 1 → χ u = 1)
    (w : ℂ) (m : ℕ) :
    IntegrableOn (fun x => charExt χ⁻¹ x * (((modulus x : ℝ)) : ℂ) ^ w) (negShell hπ m) μ := by
  refine (integrableOn_congr_fun (integrand_eqOn_negShell hπ hχ w m) (measurableSet_negShell hπ m)).mpr ?_
  exact integrableOn_const ((measure_negShell_lt_top μ hπ m).ne)

end WeylGK

end WeylShell

end TateGlobal

end NumberField
