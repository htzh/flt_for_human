/-
  Consumer specification for SET 8 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed across modules, expressed in Lean so
  that each is either bound or not.  It is a deliverable measure, not a proof obligation.  It
  is **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet8Consumer.lean 2>&1 | grep -c error

  The error count is the metric.

  ZONES
  -----
    [span-lift] ZONE A — the new LSpace-lift
                `lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed`
                (`IsCurveOver/ConstantFieldExtensionSpan.lean`) applied at `D = 0` puts the
                constants of `F'` in the span of the image of `L 0`, with the constant
                membership `algebraMap_mem_lSpace_zero` from `Defs/AdelicIndex.lean`.
    [rec]       ZONE B — the new `weilReciprocity_algebraMap` (`Place/EvalAtNorm.lean`) read in
                product form by `Divisor.evalFun_def` (`Defs/PlaceEvaluation.lean`): the
                transported identity is a product of place evaluations over the divisor.
    [pole]      ZONE C — the two new pole rows (`Genus/ConstantFieldExtensionConsequences.lean`,
                the pole bound and the pole-set sum) at the pole divisor of
                `exists_poleDivisor_of_transcendental` (`PrincipalDivisors/PoleDivisor.lean`),
                with the degree identity of the same module: one statement carrying the
                divisor, its degree, the pole set and the span bound.
-/

import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionSpan
import FLTForHuman.AlgebraicCurve.Genus.ConstantFieldExtensionConsequences
import FLTForHuman.AlgebraicCurve.Place.EvalAtNorm
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.PoleDivisor
import FLTForHuman.AlgebraicCurve.Genus.Index

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

universe u v

/-! ## Zone A — `[span-lift]` the constants lie in the span of the image -/

theorem set8_span_lift_constants
    (K : Type u) (F : Type v) (K' : Type v) (F' : Type v)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (hlift_new : ∀ v' : Place K' F', (∀ v, lift v ≠ v') →
      ∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring)
    (c : K') :
    algebraMap K' F' c ∈
      Submodule.span K' ((algebraMap F F') '' (LSpace (K := K) (0 : Divisor K F) : Set F)) := by
  have hf' : algebraMap K' F' c ∈
      LSpace (K := K') (Finsupp.mapDomain lift (0 : Divisor K F)) := by
    rw [Finsupp.mapDomain_zero]
    exact algebraMap_mem_lSpace_zero c
  exact
    lSpace_mapDomain_subset_span_image_lSpace_of_constantFieldExtension_of_isAlgClosed
      K F K' F' hfg hfg' hgen lift hlift_ord hlift_inj hlift_new 0 hf'

/-! ## Zone B — `[rec]` the transported reciprocity in product form -/

theorem set8_reciprocity_product_form {K : Type u} {F F' : Type v} [Field K] [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (hbase : WeilReciprocity K F) {f : F'} {g : F} (hf : f ≠ 0) (hg : g ≠ 0)
    (Df Dg : Divisor K F') (hDf : ∀ w : Place K F', Df w = w.ord f)
    (hDg : ∀ w : Place K F', Dg w = w.ord (algebraMap F F' g))
    (hdisj : ∀ w : Place K F', w.ord f = 0 ∨ w.ord (algebraMap F F' g) = 0)
    (hratf : ∀ w ∈ Df.support, Place.IsRational w)
    (hratF : ∀ v : Place K F, v.IsRational)
    (hratfib : ∀ v : Place K F, v.ord g ≠ 0 → ∀ w ∈ v.fiber F', Place.IsRational w) :
    Divisor.evalFun f Dg =
      ∏ w ∈ Df.support, w.evalAt (algebraMap F F' g) ^ Df w := by
  rw [weilReciprocity_algebraMap hbase hf hg Df Dg hDf hDg hdisj hratf hratF hratfib,
    Divisor.evalFun_def]

/-! ## Zone C — `[pole]` the pole divisor, its degree, the pole set and the span bound -/

theorem set8_pole_set_and_bound (k : Type u) [Field k] [IsAlgClosed k] {F : Type v} [Field F]
    [Algebra k F] (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F) :
    ∃ D : Divisor k F, (∀ v : Place k F, D v = max 0 (-v.ord x)) ∧
      Divisor.degree D = (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) ∧
      ∃ S : Finset (Place k F), (∀ P, P ∈ S ↔ P.ord x < 0) ∧
        (∑ P ∈ S, (-P.ord x) =
          (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ)) ∧
        ∃ M₁ : ℕ, ∀ h : F, (∀ v : Place k F, 0 ≤ v.ord x → 0 ≤ v.ord h) →
          h ∈ Submodule.span k {g : F | ∃ j : ℕ, ∃ y ∈ LSpace (M₁ • D), g = x ^ j * y} := by
  classical
  haveI := hfin
  obtain ⟨D, hD⟩ := exists_poleDivisor_of_transcendental x hx
  obtain ⟨S, hS, hsum⟩ :=
    exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed k x hx hfin
  obtain ⟨M₁, hM⟩ :=
    exists_forall_mem_span_pow_mul_of_forall_ord_nonneg x hx D hD
  exact ⟨D, hD,
    degree_poleDivisor_eq_finrank_adjoin_of_isAlgClosed_of_transcendental x hx D hD,
    S, hS, hsum, M₁, hM⟩
