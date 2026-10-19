/-
A correspondence between two curves preserves regular differentials: the differential
half of the AC column, after FLT's
`Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean`
and its 829-line proof. `Differential.correspondence φ ψ ω` is the trace down along the
finite integral `φ` of the pull-back up along `ψ`, and the module carries its two halves:
`pullbackAlong_mem` (the pull-back of a regular differential is regular) and
`traceAlong_mem` (so is its trace), the second consuming the trace-different bound
`trace_mem_of_le_ord` and the local derivation `exists_D_eq_smul_D` at each place. The
headline is the wrapper's statement verbatim, and the pin's `solution` body —
`traceAlong_mem` applied to `pullbackAlong_mem` — is its proof.

Statements are transcribed verbatim from the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`); only proof bodies are adapted to mathlib
`v4.34.0`. Seven declarations of the pin's prelude are the port's already and are
imported, not restated:

* pin 30 `ord_nonneg_of_mem'` — `Place.ord_nonneg_of_mem`
  (`AlgebraicCurve/Defs/PushPull.lean`); the pin's row is the section-variable spelling
  of the same lemma, so the port's copy is applied at `v`;
* pin 45 `mem_of_ord_nonneg'` — `Place.mem_toValuationSubring_of_ord_nonneg_alt`
  (`AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean`);
* pin 63 `eq_ord_of_addHom_of_nonneg_iff` — `Place.eq_ord_of_addHom_of_nonneg_iff`
  (`AlgebraicCurve/P1/Differential.lean`);
* pin 138 `neg_log_valuation_fiberCenter_eq_ord`, pin 177
  `le_ord_iff_mem_pow_fiberCenter` and pin 200
  `ramificationIndex_eq_ramificationIdx_fiberCenter` — the same names, in
  `AlgebraicCurve/Defs/PlaceDictionary.lean`;
* pin 640 `exists_restrict_eq` — `Place.exists_restrict_eq`
  (`AlgebraicCurve/WeilExchange/Bifibre.lean`), in its general `{K F' M}` form; the
  pin's is its instance at `M := F'` and is used here as
  `Place.exists_restrict_eq (M := F') v`, not restated.

The wrapper's `attribute [-instance]`/`attribute [-simp]` prelude (five lines each) is
*not* copied: it exists only because the pin's `S_` files re-declare instances and simp
lemmas that the port carries once.

Role: tier 1. One public headline,
`AlgebraicCurve.Differential.correspondence_mem_regularDifferentials`, stated at the
wrapper's name and text, over the internal blocks `Place.TraceDifferentBound`,
`Place.LocalDerivation` and `Differential.CorrespondenceRegular`.

spec-pin: Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean
-/
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.Differential.TraceDiff
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluationAlgebra
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import Mathlib.RingTheory.DedekindDomain.Different

set_option autoImplicit false

-- The pin's `letI`/`haveI` instance walls are load-bearing (SET-1 §3): the along-level
-- `Algebra F F'` must be the local one for `pullbackAlong`/`traceAlong` to unfold.
set_option linter.style.haveILetI false

noncomputable section

open IsDedekindDomain WithZero IsLocalRing Polynomial nonZeroDivisors
open scoped IntermediateField

namespace AlgebraicCurve

namespace Place

namespace TraceDifferentBound

section SinglePlace

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem mem_iff_ord_nonneg' {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨ord_nonneg_of_mem v, mem_toValuationSubring_of_ord_nonneg_alt v hf⟩

end SinglePlace

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F']

section Different

variable (v : Place K F)

omit [Algebra K F'] [IsScalarTower K F F'] in

theorem differentIdeal_le_pow (P : HeightOneSpectrum (integralClosureAt F' v)) :
    differentIdeal v.toValuationSubring (integralClosureAt F' v) ≤
      P.asIdeal ^ ((IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal - 1) := by
  set e := (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal with he_def
  by_cases he : e = 0
  · rw [he]
    simp
  rw [← Ideal.dvd_iff_le]
  exact pow_sub_one_dvd_differentIdeal_aux v.toValuationSubring F F' P.asIdeal he
    (maximalIdeal_ne_bot v) (Ideal.dvd_iff_le.mpr Ideal.le_pow_ramificationIdx')

theorem trace_mem_of_le_ord (g : F')
    (hg : ∀ w : Place K F', w.restrict F = v → 1 - (w.ramificationIndex F : ℤ) ≤ w.ord g) :
    Algebra.trace F F' g ∈ v.toValuationSubring := by
  rcases eq_or_ne g 0 with rfl | hg0
  · rw [map_zero]
    exact zero_mem _
  set B := integralClosureAt F' v with hB

  have hcoe : ((differentIdeal v.toValuationSubring B : Ideal B) : FractionalIdeal B⁰ F') =
      (FractionalIdeal.dual v.toValuationSubring F (1 : FractionalIdeal B⁰ F'))⁻¹ :=
    coeIdeal_differentIdeal v.toValuationSubring F F' B
  have h1ne : (1 : FractionalIdeal B⁰ F') ≠ 0 := one_ne_zero
  have hdual0 : FractionalIdeal.dual v.toValuationSubring F (1 : FractionalIdeal B⁰ F') ≠ 0 :=
    FractionalIdeal.dual_ne_zero _ _ h1ne
  have hD0 : ((differentIdeal v.toValuationSubring B : Ideal B) : FractionalIdeal B⁰ F') ≠ 0 := by
    rw [hcoe]
    exact inv_ne_zero hdual0

  have hmem : g ∈ ((differentIdeal v.toValuationSubring B : Ideal B) :
      FractionalIdeal B⁰ F')⁻¹ := by
    rw [FractionalIdeal.mem_inv_iff hD0]
    intro y hy
    obtain ⟨d, hd, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    rw [FractionalIdeal.mem_one_iff]
    suffices hval : ∀ P : HeightOneSpectrum B, P.valuation F' (g * algebraMap B F' d) ≤ 1 by
      obtain ⟨b, hb⟩ :=
        HeightOneSpectrum.mem_integers_of_valuation_le_one (R := B) F' _ hval
      exact ⟨b, hb⟩
    intro P

    rcases eq_or_ne d 0 with rfl | hd0
    · simp
    set w : Place K F' := placeOfPrime P with hw_def
    have hw : w.restrict F = v := restrict_placeOfPrime P
    have hP : fiberCenter F' v hw = P := fiberCenter_placeOfPrime P
    set e := (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx' P.asIdeal with he_def
    have he : w.ramificationIndex F = e := by
      rw [ramificationIndex_eq_ramificationIdx_fiberCenter hw, hP]

    have hdmem : d ∈ P.asIdeal ^ (e - 1) := differentIdeal_le_pow v P hd
    have hvd : P.valuation F' (algebraMap B F' d) ≤ exp (-((e - 1 : ℕ) : ℤ)) := by
      rw [HeightOneSpectrum.valuation_of_algebraMap]
      exact (HeightOneSpectrum.intValuation_le_pow_iff_mem _ _ _).mpr hdmem

    have hg0' : P.valuation F' g ≠ 0 := (Valuation.ne_zero_iff _).mpr hg0
    have hlog : -log (P.valuation F' g) = w.ord g := by
      have := neg_log_valuation_fiberCenter_eq_ord hw hg0
      rwa [hP] at this
    have hbound := hg w hw
    have hepos : 0 < e := he ▸ w.ramificationIndex_pos
    have hvg : P.valuation F' g ≤ exp (((e - 1 : ℕ) : ℤ)) := by
      rw [← exp_log hg0', exp_le_exp]
      push_cast [hepos]
      rw [he] at hbound
      omega
    calc P.valuation F' (g * algebraMap B F' d)
        = P.valuation F' g * P.valuation F' (algebraMap B F' d) := map_mul _ _ _
      _ ≤ exp (((e - 1 : ℕ) : ℤ)) * exp (-((e - 1 : ℕ) : ℤ)) := mul_le_mul' hvg hvd
      _ = 1 := by rw [← exp_add, add_neg_cancel, exp_zero]
  rw [hcoe, inv_inv, FractionalIdeal.mem_dual h1ne] at hmem
  have h1 := hmem 1 (FractionalIdeal.one_mem_one _)
  rw [Algebra.traceForm_apply, mul_one] at h1
  obtain ⟨r, hr⟩ := h1
  rw [← hr]
  exact r.2

end Different

end TraceDifferentBound

namespace LocalDerivation

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem exists_mem_finiteDimensional (v : Place K F)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ y : F, y ∈ v.toValuationSubring ∧
      FiniteDimensional (IntermediateField.adjoin K ({y} : Set F)) F := by
  obtain ⟨x, -, hxfin⟩ := hfg
  by_cases hx : x ∈ v.toValuationSubring
  · exact ⟨x, hx, hxfin⟩
  have hxinv : x⁻¹ ∈ v.toValuationSubring :=
    (v.toValuationSubring.mem_or_inv_mem x).resolve_left hx
  have hE : IntermediateField.adjoin K ({x⁻¹} : Set F) =
      IntermediateField.adjoin K ({x} : Set F) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_simple_le_iff]
      exact inv_mem (IntermediateField.mem_adjoin_simple_self K x)
    · rw [IntermediateField.adjoin_simple_le_iff]
      have := IntermediateField.mem_adjoin_simple_self K x⁻¹
      simpa using inv_mem this
  refine ⟨x⁻¹, hxinv, ?_⟩
  rw [hE]
  exact hxfin

theorem essFiniteType_of_finiteType (v : Place K F) {R : Type*} [CommRing R]
    [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F] [Algebra K R]
    [Algebra.FiniteType K R]
    (hRK : ∀ k : K, algebraMap R F (algebraMap K R k) = algebraMap K F k)
    (hR : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  classical
  have heq := v.toValuationSubring_eq_of_forall_mem hR

  let φ : R →+* v.toValuationSubring :=
    (algebraMap R F).codRestrict v.toValuationSubring.toSubring hR
  have hφ : ∀ r : R, (φ r : F) = algebraMap R F r := fun r => rfl
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := K) (A := R)
  let σ : Finset v.toValuationSubring := s.image φ
  have hφσ : ∀ r : R, φ r ∈ Algebra.adjoin K (σ : Set v.toValuationSubring) := by
    intro r
    have hr : r ∈ Algebra.adjoin K (s : Set R) := by rw [hs]; exact Algebra.mem_top
    induction hr using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      simp only [σ, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      exact ⟨x, hx, rfl⟩
    | algebraMap k =>
      have : φ (algebraMap K R k) = algebraMap K v.toValuationSubring k :=
        Subtype.ext (by rw [hφ, hRK, coe_algebraMap])
      rw [this]
      exact Subalgebra.algebraMap_mem _ k
    | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
    | mul x z _ _ hx hz => rw [map_mul]; exact mul_mem hx hz
  rw [Algebra.essFiniteType_iff]
  refine ⟨σ, fun t => ?_⟩
  have ht : (t : F) ∈ HeightOneSpectrum.valuationSubringAtPrime F
      (centerHeightOneSpectrum R v hR) := heq ▸ t.2
  obtain ⟨a, b, hb, hab⟩ := ht
  have hbunit : IsUnit (φ b) := by
    rw [← IsLocalRing.notMem_maximalIdeal]
    exact fun hmem => hb hmem
  have hb0 : algebraMap R F b ≠ 0 := by
    intro h0
    apply hb
    have : b = 0 := (map_eq_zero_iff _ (IsFractionRing.injective R F)).mp h0
    rw [this]
    exact Ideal.zero_mem _
  refine ⟨φ b, hφσ b, hbunit, ?_⟩
  have hprod : t * φ b = φ a := by
    apply Subtype.ext
    show (t : F) * algebraMap R F b = algebraMap R F a
    rw [hab, inv_mul_cancel_right₀ hb0]
  rw [hprod]
  exact hφσ a

theorem adjoin_le_of_mem (v : Place K F) {y : F} (hy : y ∈ v.toValuationSubring)
    {a : F} (ha : a ∈ Algebra.adjoin K ({y} : Set F)) : a ∈ v.toValuationSubring := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact hy
  | algebraMap r => exact v.algebraMap_mem' r
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

open scoped IntermediateField.algebraAdjoinAdjoin in

theorem essFiniteType_of_mem [CharZero K] (v : Place K F) {y : F}
    (hyv : y ∈ v.toValuationSubring) [FiniteDimensional K⟮y⟯ F] :
    Algebra.EssFiniteType K v.toValuationSubring := by
  haveI : CharZero K⟮y⟯ := charZero_of_injective_algebraMap (algebraMap K K⟮y⟯).injective
  haveI : Algebra.IsSeparable K⟮y⟯ F := inferInstance
  have hAr : ∀ p : K[X], aeval y p ∈ Algebra.adjoin K ({y} : Set F) := fun p => by
    rw [Algebra.adjoin_singleton_eq_range_aeval]
    exact ⟨p, rfl⟩
  let f : K[X] →ₐ[K] Algebra.adjoin K ({y} : Set F) := (aeval y).codRestrict _ hAr
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
    obtain ⟨p, rfl⟩ := ha
    exact ⟨p, rfl⟩
  haveI : IsPrincipalIdealRing (Algebra.adjoin K ({y} : Set F)) :=
    IsPrincipalIdealRing.of_surjective f hf
  haveI : IsDedekindDomain (Algebra.adjoin K ({y} : Set F)) := inferInstance
  haveI : IsDedekindDomain (integralClosure (Algebra.adjoin K ({y} : Set F)) F) :=
    integralClosure.isDedekindDomain (Algebra.adjoin K ({y} : Set F)) K⟮y⟯ F
  haveI : IsFractionRing (integralClosure (Algebra.adjoin K ({y} : Set F)) F) F :=
    integralClosure.isFractionRing_of_finite_extension K⟮y⟯ F
  haveI : Module.Finite (Algebra.adjoin K ({y} : Set F))
      (integralClosure (Algebra.adjoin K ({y} : Set F)) F) :=
    IsIntegralClosure.finite (Algebra.adjoin K ({y} : Set F)) K⟮y⟯ F _
  haveI : IsScalarTower K (Algebra.adjoin K ({y} : Set F))
      (integralClosure (Algebra.adjoin K ({y} : Set F)) F) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : Algebra.FiniteType K (Algebra.adjoin K ({y} : Set F)) :=
    Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton y)
  haveI : Algebra.FiniteType K (integralClosure (Algebra.adjoin K ({y} : Set F)) F) :=
    Algebra.FiniteType.trans (S := Algebra.adjoin K ({y} : Set F)) inferInstance inferInstance
  refine essFiniteType_of_finiteType v (R := integralClosure (Algebra.adjoin K ({y} : Set F)) F)
    (fun _ => rfl) ?_
  intro b
  obtain ⟨p, hp, hpb⟩ : IsIntegral (Algebra.adjoin K ({y} : Set F)) (b : F) := b.2
  refine v.mem_of_eval_monic_eq_zero (P := p.map (algebraMap (Algebra.adjoin K ({y} : Set F)) F))
    (hp.map _) ?_ ?_
  · intro i
    rw [coeff_map]
    exact adjoin_le_of_mem v hyv (p.coeff i).2
  · rw [eval_map]
    exact hpb

theorem essFiniteType [CharZero K] (v : Place K F)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    Algebra.EssFiniteType K v.toValuationSubring := by
  obtain ⟨y, hyv, hfin⟩ := exists_mem_finiteDimensional v hfg
  haveI := hfin
  exact essFiniteType_of_mem v hyv

theorem exists_eq_algebraMap_add_mul [IsAlgClosed K] (v : Place K F) [v.FiniteResidue]
    {ϖ : v.toValuationSubring} (hϖ : Irreducible ϖ) (a : v.toValuationSubring) :
    ∃ c : K, ∃ b : v.toValuationSubring, a = algebraMap K v.toValuationSubring c + ϖ * b := by
  haveI : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K _
  obtain ⟨c, hc⟩ :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2
      (IsLocalRing.residue v.toValuationSubring a)
  have hmem : a - algebraMap K v.toValuationSubring c ∈
      IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero, ← hc]
    rfl
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hmem
  obtain ⟨b, hb⟩ := hmem
  exact ⟨c, b, by linear_combination -hb⟩

theorem span_D_eq_top [IsAlgClosed K] (v : Place K F) [v.FiniteResidue]
    [Algebra.EssFiniteType K v.toValuationSubring]
    {ϖ : v.toValuationSubring} (hϖ : Irreducible ϖ) :
    Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring ϖ} = ⊤ := by
  refine top_le_iff.mp (Submodule.le_of_le_smul_of_le_jacobson_bot
    (I := IsLocalRing.maximalIdeal v.toValuationSubring)
    (N := Submodule.span v.toValuationSubring
      {KaehlerDifferential.D K v.toValuationSubring ϖ})
    (N' := ⊤) Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_)
  conv_lhs => rw [← KaehlerDifferential.span_range_derivation]
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  obtain ⟨c, b, hab⟩ := exists_eq_algebraMap_add_mul v hϖ a
  have hD : KaehlerDifferential.D K v.toValuationSubring a =
      b • KaehlerDifferential.D K v.toValuationSubring ϖ +
        ϖ • KaehlerDifferential.D K v.toValuationSubring b := by
    rw [hab, map_add, Derivation.map_algebraMap, zero_add, Derivation.leibniz, add_comm]
  rw [SetLike.mem_coe, hD]
  refine Submodule.add_mem_sup (Submodule.smul_mem _ _ (Submodule.subset_span rfl)) ?_
  exact Submodule.smul_mem_smul (hϖ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ)
    Submodule.mem_top

theorem exists_irreducible_coe_eq (v : Place K F) {π : F} (hπ : v.ord π = 1) :
    ∃ ϖ : v.toValuationSubring, Irreducible ϖ ∧ (ϖ : F) = π := by
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hπ
    exact zero_ne_one hπ
  obtain ⟨ϖ₀, hϖ₀⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hπ0 hϖ₀
  rw [hπ, zpow_one] at hu
  refine ⟨(u : v.toValuationSubring) * ϖ₀, ?_, by push_cast; exact hu.symm⟩
  exact Associated.irreducible ⟨u, mul_comm _ _⟩ hϖ₀

theorem exists_D_eq_smul_D [IsAlgClosed K] [CharZero K] (v : Place K F) [v.FiniteResidue]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {π f : F} (hπ : v.ord π = 1) (hf : f ∈ v.toValuationSubring) :
    ∃ g ∈ v.toValuationSubring,
      KaehlerDifferential.D K F f = g • KaehlerDifferential.D K F π := by
  haveI := essFiniteType v hfg
  obtain ⟨ϖ, hϖ, rfl⟩ := exists_irreducible_coe_eq v hπ

  have htop := span_D_eq_top v hϖ
  have hmem : KaehlerDifferential.D K v.toValuationSubring ⟨f, hf⟩ ∈
      Submodule.span v.toValuationSubring
        {KaehlerDifferential.D K v.toValuationSubring ϖ} := by
    rw [htop]; exact Submodule.mem_top
  obtain ⟨g, hg⟩ := Submodule.mem_span_singleton.mp hmem
  refine ⟨(g : F), g.2, ?_⟩
  have h2 := congrArg (KaehlerDifferential.map K K v.toValuationSubring F) hg
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at h2
  have h3 : g • KaehlerDifferential.D K F (ϖ : F) = KaehlerDifferential.D K F f := h2
  rw [← h3]
  exact (algebraMap_smul F g _).symm

theorem D_ne_zero_of_ord_eq_one [IsAlgClosed K] [CharZero K] [Nontrivial (Ω[F⁄K])]
    (v : Place K F) [v.FiniteResidue]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ϖ : F} (hϖ : v.ord ϖ = 1) : KaehlerDifferential.D K F ϖ ≠ 0 := by
  intro h0
  have key : ∀ f ∈ v.toValuationSubring, KaehlerDifferential.D K F f = 0 := fun f hf => by
    obtain ⟨g, -, hg⟩ := exists_D_eq_smul_D v hfg hϖ hf
    rw [hg, h0, smul_zero]
  have hall : ∀ f : F, KaehlerDifferential.D K F f = 0 := by
    intro f
    rcases v.toValuationSubring.mem_or_inv_mem f with hf | hf
    · exact key f hf
    rcases eq_or_ne f 0 with rfl | hf0
    · exact map_zero _
    have h1 : KaehlerDifferential.D K F (f * f⁻¹) = 0 := by
      rw [mul_inv_cancel₀ hf0]
      exact Derivation.map_one_eq_zero _
    rw [Derivation.leibniz, key _ hf, smul_zero, zero_add, smul_eq_zero] at h1
    exact h1.resolve_left (inv_ne_zero hf0)
  have htop : (⊤ : Submodule F (Ω[F⁄K])) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨f, rfl⟩
    exact hall f
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hxmem : x ∈ (⊤ : Submodule F (Ω[F⁄K])) := Submodule.mem_top
  rw [htop, Submodule.mem_bot] at hxmem
  exact hx hxmem

theorem isUnit_add_of_mem_maximalIdeal {R : Type*} [CommRing R] [IsLocalRing R] {a b : R}
    (ha : IsUnit a) (hb : b ∈ IsLocalRing.maximalIdeal R) : IsUnit (a + b) := by
  by_contra h
  have h1 : a + b ∈ IsLocalRing.maximalIdeal R := (IsLocalRing.mem_maximalIdeal _).mpr h
  have h2 : a ∈ IsLocalRing.maximalIdeal R := by
    have := sub_mem h1 hb
    rwa [add_sub_cancel_right] at this
  exact (IsLocalRing.mem_maximalIdeal _).mp h2 ha

theorem exists_D_eq_smul_D_of_ord_pos [IsAlgClosed K] [CharZero K] (v : Place K F)
    [v.FiniteResidue]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ϖ y : F} (hϖ : v.ord ϖ = 1) (hy0 : y ≠ 0) (hy : 0 < v.ord y) :
    ∃ δ : F, δ ≠ 0 ∧ v.ord δ = v.ord y - 1 ∧
      KaehlerDifferential.D K F y = δ • KaehlerDifferential.D K F ϖ := by
  have hϖ0 : ϖ ≠ 0 := by
    rintro rfl
    rw [v.ord_zero] at hϖ
    exact zero_ne_one hϖ
  obtain ⟨ϖ', hirr, rfl⟩ := exists_irreducible_coe_eq v hϖ
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hy0 hirr
  obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hy.le
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [hm] at hy
    exact lt_irrefl _ hy
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  rw [hm, zpow_natCast] at hu

  obtain ⟨gu, hgu, hDu⟩ := exists_D_eq_smul_D v hfg hϖ (u : v.toValuationSubring).2

  have hKunit : IsUnit (((k.succ : ℕ) : v.toValuationSubring) * (u : v.toValuationSubring)) := by
    refine IsUnit.mul ?_ u.isUnit
    rw [← map_natCast (algebraMap K v.toValuationSubring)]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))).map _
  have hmax : ϖ' * ⟨gu, hgu⟩ ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
    Ideal.mul_mem_right _ _ (hirr.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self ϖ')
  obtain ⟨s, hs⟩ := isUnit_add_of_mem_maximalIdeal hKunit hmax
  have hsF : ((s : v.toValuationSubring) : F) =
      ((k.succ : ℕ) : F) * (u : v.toValuationSubring) + (ϖ' : F) * gu := by
    rw [hs]
    push_cast
    rfl
  have hs0 : ((k.succ : ℕ) : F) * (u : v.toValuationSubring) + (ϖ' : F) * gu ≠ 0 := by
    rw [← hsF]
    simp [ne_eq, ZeroMemClass.coe_eq_zero]
  refine ⟨(ϖ' : F) ^ k * (((k.succ : ℕ) : F) * (u : v.toValuationSubring) + (ϖ' : F) * gu),
    mul_ne_zero (pow_ne_zero _ hϖ0) hs0, ?_, ?_⟩
  · rw [v.ord_mul (pow_ne_zero _ hϖ0) hs0, ← hsF, v.ord_coe_unit s, ← zpow_natCast,
      v.ord_zpow, hϖ, hm]
    push_cast
    ring
  · rw [hu, Derivation.leibniz, Derivation.leibniz_pow, hDu, Nat.succ_sub_one,
      ← Nat.cast_smul_eq_nsmul F, smul_smul, smul_smul, smul_smul, ← add_smul]
    congr 1
    rw [pow_succ]
    push_cast
    ring

end LocalDerivation

end Place

namespace Differential

namespace CorrespondenceRegular

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem hfg_along (ψ : F →ₐ[K] F') (hψfin : FiniteAlong K ψ)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F' := by
  obtain ⟨x, hx, hfin⟩ := hfg
  refine ⟨ψ x, ?_, ?_⟩
  · rw [transcendental_iff_injective] at hx ⊢
    intro p q hpq
    apply hx
    apply ψ.toRingHom.injective
    simp only [Polynomial.aeval_algHom_apply] at hpq
    exact hpq
  · letI : Algebra F F' := algebraAlong ψ
    haveI : IsScalarTower K F F' := isScalarTower_along ψ
    haveI : Module.Finite F F' := hψfin
    letI : Algebra K⟮x⟯ F' := ((algebraMap F F').comp (algebraMap K⟮x⟯ F)).toAlgebra
    haveI : IsScalarTower K⟮x⟯ F F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    haveI : Module.Finite K⟮x⟯ F' := Module.Finite.trans F F'
    have hmapeq : (K⟮x⟯.map ψ : IntermediateField K F') = K⟮ψ x⟯ := by
      rw [IntermediateField.adjoin_map, Set.image_singleton]
    have hmap : ∀ a : K⟮x⟯, (ψ.toRingHom.comp (algebraMap K⟮x⟯ F)) a ∈ K⟮ψ x⟯ := fun a => by
      rw [← hmapeq]
      exact ⟨a, a.2, rfl⟩
    letI : Algebra K⟮x⟯ K⟮ψ x⟯ :=
      ((ψ.toRingHom.comp (algebraMap K⟮x⟯ F)).codRestrict K⟮ψ x⟯ hmap).toAlgebra
    haveI : IsScalarTower K⟮x⟯ K⟮ψ x⟯ F' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    exact Module.Finite.of_restrictScalars_finite K⟮x⟯ K⟮ψ x⟯ F'

theorem pullbackAlong_mem [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (ψ : F →ₐ[K] F') (hψ : ψ.toRingHom.IsIntegral) (hψfin : FiniteAlong K ψ)
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) :
    pullbackAlong ψ ω ∈ regularDifferentials K F' := by
  have hfg' := hfg_along ψ hψfin hfg
  letI : Algebra F F' := algebraAlong ψ
  haveI : IsScalarTower K F F' := isScalarTower_along ψ
  haveI : Algebra.IsIntegral F F' := isIntegral_along ψ hψ
  rw [mem_regularDifferentials_iff]
  intro w
  obtain ⟨f, hf, hωf⟩ := (mem_regularDifferentials_iff).mp hω (w.restrict F)
  obtain ⟨π, hπ1, hdc⟩ := (w.restrict F).exists_ord_eq_one_and_dCoord_eq
  obtain ⟨ϖ, hϖ1, hdcw⟩ := w.exists_ord_eq_one_and_dCoord_eq
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hπw : ψ π ∈ w.toValuationSubring :=
    (Place.mem_restrict_iff (F := F) (w := w)).mp
      (Place.mem_toValuationSubring_of_ord_nonneg_alt _ hπ0 (by rw [hπ1]; exact zero_le_one))
  have hfw : ψ f ∈ w.toValuationSubring := (Place.mem_restrict_iff (F := F) (w := w)).mp hf
  obtain ⟨g, hg, hDg⟩ := Place.LocalDerivation.exists_D_eq_smul_D w hfg' hϖ1 hπw
  refine ⟨ψ f * g, mul_mem hfw hg, ?_⟩
  rw [hωf, hdc, pullbackAlong_smul, pullbackAlong_D, hDg, hdcw, smul_smul]

theorem traceAlong_mem [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F')) F')
    {η : Ω[F'⁄K]} (hη : η ∈ regularDifferentials K F') :
    traceAlong φ η ∈ regularDifferentials K F := by
  by_cases hsep : SeparableAlong K φ
  swap
  · rw [traceAlong_of_not φ hsep, LinearMap.zero_apply]
    exact zero_mem _
  letI : Algebra F F' := algebraAlong φ
  haveI : IsScalarTower K F F' := isScalarTower_along φ
  haveI : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  by_cases hfin : FiniteAlong K φ
  swap
  ·
    have htr : Algebra.trace F F' = 0 := by
      refine Algebra.trace_eq_zero_of_not_exists_basis F ?_
      rintro ⟨s, ⟨b⟩⟩
      exact hfin (Module.Finite.of_basis b)
    have h0 : traceAlong φ = 0 := by
      rw [traceAlong, dite_eq_left hsep]
      simp only [htr, LinearMap.rTensor_zero, LinearMap.zero_comp, LinearMap.comp_zero,
        LinearMap.restrictScalars_zero]
    rw [h0, LinearMap.zero_apply]
    exact zero_mem _
  haveI : Module.Finite F F' := hfin
  haveI : Algebra.IsSeparable F F' := hsep
  rw [mem_regularDifferentials_iff]
  intro v
  obtain ⟨π, hπ1, hdc⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [Place.ord_zero] at hπ1
    exact zero_ne_one hπ1
  have hφπ0 : φ π ≠ 0 := (map_ne_zero_iff _ φ.toRingHom.injective).mpr hπ0
  have hθ : pullbackAlong φ (KaehlerDifferential.D K F π) =
      KaehlerDifferential.D K F' (φ π) := pullbackAlong_D φ π

  have hcoef : ∀ w : Place K F', w.restrict F = v → ∀ {ϖ : F'}, w.ord ϖ = 1 →
      ∃ δ : F', δ ≠ 0 ∧ w.ord δ = (w.ramificationIndex F : ℤ) - 1 ∧
        KaehlerDifferential.D K F' (φ π) = δ • KaehlerDifferential.D K F' ϖ := by
    intro w hw ϖ hϖ
    have hord : w.ord (φ π) = w.ramificationIndex F := by
      have h := w.ord_restrict (F := F) π
      rw [hw, hπ1, mul_one] at h
      exact h
    have hpos : 0 < w.ord (φ π) := by
      rw [hord]
      exact_mod_cast w.ramificationIndex_pos
    obtain ⟨δ, hδ0, hδord, hD⟩ :=
      Place.LocalDerivation.exists_D_eq_smul_D_of_ord_pos w hfg' hϖ hφπ0 hpos
    exact ⟨δ, hδ0, by rw [hδord, hord], hD⟩

  obtain ⟨w₀, hw₀⟩ := Place.exists_restrict_eq (M := F') v
  obtain ⟨ϖ₀, hϖ₀, -⟩ := w₀.exists_ord_eq_one_and_dCoord_eq
  have hθ0 : KaehlerDifferential.D K F' (φ π) ≠ 0 := by
    obtain ⟨δ, hδ0, -, hD⟩ := hcoef w₀ hw₀ hϖ₀
    rw [hD]
    exact smul_ne_zero hδ0 (Place.LocalDerivation.D_ne_zero_of_ord_eq_one w₀ hfg' hϖ₀)

  obtain ⟨g, hg⟩ :=
    (finrank_eq_one_iff_of_nonzero' _ hθ0).mp (IsCurveOver.finrank_kaehler (K := K) (F := F')) η

  have hgbound : ∀ w : Place K F', w.restrict F = v →
      1 - (w.ramificationIndex F : ℤ) ≤ w.ord g := by
    intro w hw
    obtain ⟨ϖ, hϖ, hdcw⟩ := w.exists_ord_eq_one_and_dCoord_eq
    obtain ⟨f, hf, hηf⟩ := (mem_regularDifferentials_iff).mp hη w
    obtain ⟨δ, hδ0, hδord, hD⟩ := hcoef w hw hϖ
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [Place.ord_zero]
      have := w.ramificationIndex_pos (F := F)
      omega
    have hgδ : g * δ = f := by
      apply smul_left_injective F' (Place.LocalDerivation.D_ne_zero_of_ord_eq_one w hfg' hϖ)
      show (g * δ) • KaehlerDifferential.D K F' ϖ = f • KaehlerDifferential.D K F' ϖ
      rw [← smul_smul, ← hD, hg, hηf, hdcw]
    have h1 : 0 ≤ w.ord (g * δ) := by
      rw [hgδ]
      exact Place.ord_nonneg_of_mem w hf
    rw [w.ord_mul hg0 hδ0, hδord] at h1
    omega
  refine ⟨Algebra.trace F F' g, Place.TraceDifferentBound.trace_mem_of_le_ord v g hgbound, ?_⟩
  rw [← hg, ← hθ, traceAlong_smul_pullbackAlong φ hsep g, hdc]

end CorrespondenceRegular

end Differential

namespace Differential

-- pin: AlgebraicCurve.Differential.correspondence_mem_regularDifferentials (Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean:12)
theorem correspondence_mem_regularDifferentials
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ)
    {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) :
    Differential.correspondence φ ψ ω ∈ regularDifferentials K F := by
  rw [Differential.correspondence_apply]
  exact Differential.CorrespondenceRegular.traceAlong_mem φ hφ
    (Differential.CorrespondenceRegular.hfg_along ψ hψfin hfg)
    (Differential.CorrespondenceRegular.pullbackAlong_mem ψ hψ hψfin hfg hω)

end Differential

end AlgebraicCurve

end
