/-
  Consumer specification for the `AlgebraicCurve` layer (SET 1: AC0 + T1).

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of the generic curve vocabulary: the statements the port
  must make possible, expressed in Lean so that each one is either bound or not.
  It is a deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**. `lake build` does not see it
  (nothing globs `spec/`), so it cannot break the verified port's green build.
  Run it by hand:

      cd lean
      lake env lean spec/AlgebraicCurveConsumer.lean 2>&1 | grep -c error

  The error count is the metric.

  HOW TO READ IT
  --------------
  Every block is labelled:

    [vocab]      ZONE A — after AC0. The objects exist with the pinned shapes and
                 the `Place` ↔ `ValuationSubring` ↔ `HeightOneSpectrum` bridge
                 typechecks. These are live imports and `#check`s, not
                 restatements (the FFG `Universal.lean` lesson).
    [interface]  ZONE B — after T1. The four high-indegree ord leaves at their
                 pinned statements, plus a real cross-module wire test that
                 consumes a `Place` lemma from `Defs/Place.lean` and a `Divisor`
                 lemma from `Defs/Divisor.lean`.

  Zones C (T2's dictionary), D (T3's Galois action), E (T4's transport) and the
  SET 2 zones F–I are appended by their topics. The file stays at 0 errors.
-/

import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
import FLTForHuman.AlgebraicCurve.Defs.Correspondence
import FLTForHuman.AlgebraicCurve.Defs.SemilinearAut
import FLTForHuman.AlgebraicCurve.Defs.RatFuncPlaces
import FLTForHuman.AlgebraicCurve.Defs.IntegralAdjoin
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.WeilExchange.FiberOverCount
import FLTForHuman.AlgebraicCurve.WeilExchange.GaloisRamification
import FLTForHuman.AlgebraicCurve.WeilExchange.Transport
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
import FLTForHuman.AlgebraicCurve.WeilExchange.LocalExchange
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree
import FLTForHuman.AlgebraicCurve.PrincipalDivisors.Transcendence
import FLTForHuman.AlgebraicCurve.WeilExchange.DivisorExchange
import FLTForHuman.FieldTheory.FiniteGroupAction

open AlgebraicCurve

-- The dictionary facts are stated with the pin's primed `Ideal.inertiaDeg'`.
set_option linter.deprecated false

noncomputable section

/-! ## Zone A — `[vocab]` the objects and the bridge -/

-- The pinned signatures. `#check` is against the port's live imports.
#check Place
#check Place.ord
#check Place.deg
#check Divisor
#check Divisor.degree
#check Divisor.IsPrincipal
#check HasPrincipalDivisors
#check Pic0.mk
#check Place.ofHeightOneSpectrum
#check Place.fiberOver
#check Place.heightOneSpectrum
#check Place.adicValuation
#check Place.restrict
#check Place.ramificationIndex
#check Place.inertiaDeg

-- Inhabitedness: `Place` from the place at infinity of `K(t)`, `Divisor`/`Pic0`
-- from zero.
example (K : Type*) [Field K] [DecidableEq (RatFunc K)] :
    Inhabited (Place K (RatFunc K)) := ⟨RationalFunctionField.placeInfty K⟩

example {K F : Type*} [Field K] [Field F] [Algebra K F] : Inhabited (Divisor K F) := ⟨0⟩

example {K F : Type*} [Field K] [Field F] [Algebra K F] : Inhabited (Pic0 K F) := ⟨0⟩

-- The `Place` ↔ `ValuationSubring` ↔ `HeightOneSpectrum` bridge, used for real.
example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.heightOneSpectrum.asIdeal = IsLocalRing.maximalIdeal v.toValuationSubring :=
  v.heightOneSpectrum_asIdeal

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) :
    v.adicValuation.valuationSubring = v.toValuationSubring :=
  v.adicValuation_valuationSubring

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F} :
    f ∈ v.toValuationSubring ↔ v.adicValuation f ≤ 1 :=
  v.mem_iff_adicValuation_le_one

/-! ## Zone B — `[interface]` T1's ord interface and the cross-module wire test -/

-- The four high-indegree leaves, at their pinned statements.
#check @Place.mem_iff_ord_nonneg
#check @Place.ord_algebraMap
#check @Place.mem_of_ord_nonneg
#check @Place.ord_nonneg_of_mem

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) : f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  v.mem_iff_ord_nonneg hf

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :
    v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ≠ 0) (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring :=
  v.mem_of_ord_nonneg hf h

example {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f :=
  v.ord_nonneg_of_mem hf

-- The cross-module wire test: a real composition of a `Place` lemma from
-- `Defs/Place.lean` with a `Divisor` lemma from `Defs/Divisor.lean`, discharged
-- for the place at infinity of `K(t)`.
theorem zoneB_wire (K : Type*) [Field K] [DecidableEq (RatFunc K)] (c : K) (n : ℤ) :
    Divisor.degree (Finsupp.single (RationalFunctionField.placeInfty K) n) =
        n * ((RationalFunctionField.placeInfty K).deg : ℤ) ∧
      (RationalFunctionField.placeInfty K).ord (algebraMap K (RatFunc K) c) = 0 :=
  ⟨Divisor.degree_single _ _, Place.ord_algebraMap _ c⟩

example (K : Type*) [Field K] [DecidableEq (RatFunc K)] (n : ℤ) :
    Divisor.degree (Finsupp.single (RationalFunctionField.placeInfty K) n)
      = n * ((RationalFunctionField.placeInfty K).deg : ℤ) :=
  Divisor.degree_single _ _

/-! ## Zone C — `[dictionary]` T2's fibre dictionary and the bifibre count -/

-- The promoted dictionary's two centre identifications at their pinned statements.
#check @Place.ramificationIndex_eq_ramificationIdx_fiberCenter
#check @Place.inertiaDeg_eq_inertiaDeg_fiberCenter
#check @Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver
#check @Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank
#check @Place.inertiaDeg_pos

example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (w : Place K F') (hw : w.restrict F = v) :
    w.ramificationIndex F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (Place.fiberCenter F' v hw).asIdeal :=
  Place.ramificationIndex_eq_ramificationIdx_fiberCenter hw

example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (w : Place K F') (hw : w.restrict F = v) :
    w.inertiaDeg F =
      (IsLocalRing.maximalIdeal v.toValuationSubring).inertiaDeg'
        (Place.fiberCenter F' v hw).asIdeal :=
  Place.inertiaDeg_eq_inertiaDeg_fiberCenter hw

-- The bifibre count, and the `≤` form applied to an abstract separable extension
-- (all hypotheses accept; the place is abstract because a `Place K K` is empty).
example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) :
    ∑ w ∈ v.fiberOver F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) =
      (Module.finrank F F' : ℤ) :=
  Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver v

example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (v : Place K F) (S : Finset (Place K F')) (hS : ∀ w ∈ S, w.restrict F = v) :
    ∑ w ∈ S, (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ) ≤
      (Module.finrank F F' : ℤ) :=
  Place.sum_ramificationIndex_mul_inertiaDeg_le_finrank v S hS

/-! ## Zone D — `[galois]` T3's Galois action on places -/

#check @Place.exists_algEquiv_smul_eq_of_restrict_eq
#check @Place.ramificationIndex_eq_of_restrict_eq
#check @Place.inertiaDeg_eq_of_restrict_eq
#check @SemilinearAut.ramificationIndex_smul
#check @SemilinearAut.inertiaDeg_smul

-- The transitivity statement instantiated at an abstract Galois extension (all
-- hypotheses accept; a concrete `Gal` extension of the port's `RatFunc` is not
-- available in this layer).
example {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W' :=
  Place.exists_algEquiv_smul_eq_of_restrict_eq W W' h

example {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    W'.ramificationIndex F' = W.ramificationIndex F' :=
  Place.ramificationIndex_eq_of_restrict_eq W W' h

example {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F' :=
  Place.inertiaDeg_eq_of_restrict_eq W W' h

/-! ## Zone E — `[transport]` T4's along-map transport and `Pic0` descent -/

#check @Place.restrictAlong_restrictAlong
#check @Place.ramificationIndexAlong_comp
#check @Place.inertiaDegAlong_comp
#check @Divisor.pushforwardAlong_pushforwardAlong
#check @Divisor.pullbackAlong_pullbackAlong
#check @Pic0.mk_eq_zero_iff
#check @Pic0.zsmul_mk
#check @finiteAlong_comp
#check @separableAlong_of_charZero
#check @BifibreDev.restrict_restrict
#check @Place.ramificationIndex_eq_mul_ramificationIndex_restrict
#check @Place.inertiaDeg_eq_mul_inertiaDeg_restrict

-- `finiteAlong_comp` on an abstract tower, and `separableAlong_of_charZero` at the
-- concrete `ℚ → ℚ`.
example {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F'']
    [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'')
    (hφ : FiniteAlong K φ) (hχ : FiniteAlong K χ) : FiniteAlong K (χ.comp φ) :=
  finiteAlong_comp φ χ hφ hχ

example : FiniteAlong ℚ (AlgHom.id ℚ ℚ) :=
  finiteAlong_of_surjective (AlgHom.id ℚ ℚ) Function.surjective_id

example : SeparableAlong ℚ (AlgHom.id ℚ ℚ) :=
  separableAlong_of_charZero (AlgHom.id ℚ ℚ) (fun _ => isIntegral_algebraMap)

-- A `Pic0` descent check: the order of `mk D` divides `m` once `m • D` is
-- principal, composing `nsmul_mk_eq_zero_of_isPrincipal` (via `zsmul_mk` and
-- `mk_eq_zero_iff`) with `addOrderOf_dvd_of_nsmul_eq_zero`.
example {K F : Type*} [Field K] [Field F] [Algebra K F]
    (D : Divisor.degZero (K := K) (F := F)) (m : ℕ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) :
    addOrderOf (Pic0.mk D) ∣ m :=
  Pic0.addOrderOf_mk_dvd_of_isPrincipal D m hD

/-! ## Zone F — `[bifibre]` T5's generic orbit engine and the bifibre count -/

#check @MulAction.ncard_orbit_inter_orbit_mul_card
#check @Subgroup.exists_eq_mul_of_index_inf_eq
#check @Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg
#check @Place.exists_restrict_eq
#check @Place.sum_ramificationIndex_mul_inertiaDeg_bifiber

-- The generic pair instantiated concretely, and *composed*: on the two-element
-- permutation group acting on `Fin 2`, the index equality for `⊤ ⊓ ⊥` is real
-- (`[G : ⊥] = [G : ⊤] · [G : ⊥]`), it feeds the `hprod` hypothesis of the
-- orbit-intersection count, and the count then has a closed numeric conclusion
-- (`1 * 2 = 2 * 1`). This is the FFG generic-kernel wire test: the instantiation,
-- not the transcription, is what must typecheck.
example :
    (MulAction.orbit (⊤ : Subgroup (Equiv.Perm (Fin 2))) (0 : Fin 2) ∩
        MulAction.orbit (⊥ : Subgroup (Equiv.Perm (Fin 2))) (1 : Fin 2)).ncard
          * Nat.card (Fin 2) =
      (MulAction.orbit (⊤ : Subgroup (Equiv.Perm (Fin 2))) (0 : Fin 2)).ncard
        * (MulAction.orbit (⊥ : Subgroup (Equiv.Perm (Fin 2))) (1 : Fin 2)).ncard := by
  have hidx : (⊤ ⊓ ⊥ : Subgroup (Equiv.Perm (Fin 2))).index =
      (⊤ : Subgroup (Equiv.Perm (Fin 2))).index * (⊥ : Subgroup (Equiv.Perm (Fin 2))).index := by
    rw [inf_bot_eq, Subgroup.index_top, Subgroup.index_bot]; simp
  exact MulAction.ncard_orbit_inter_orbit_mul_card ⊤ ⊥
    (Subgroup.exists_eq_mul_of_index_inf_eq ⊤ ⊥ hidx) 0 1

-- The two `Place` bridges at their pinned statements (the places are abstract:
-- a `Place K K` is empty, as in Zones C/D).
example {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (w : Place K F') (W : Place K M) (hW : W.restrict F' = w) :
    (w.fiberOver M).card * (W.ramificationIndex F' * W.inertiaDeg F') =
      Module.finrank F' M :=
  Place.card_fiberOver_mul_ramificationIndex_mul_inertiaDeg w W hW

example {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M]
    [Algebra.IsSeparable F' M] (w : Place K F') :
    ∃ W : Place K M, W.restrict F' = w :=
  Place.exists_restrict_eq w

-- The bifibre count, applied at an abstract Hecke roof (generation `hgen`, degree
-- `hLD`); every hypothesis is a binder, so the statement is the pinned one.
section BifibreZone

variable {K F F₁ F₂ E : Type*} (M : Type*) [Field K] [Field F] [Field F₁] [Field F₂]
  [Field E] [Field M] [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E]
  [Algebra K M] [Algebra F F₁] [Algebra F F₂] [Algebra F E] [Algebra F M] [Algebra F₁ E]
  [Algebra F₂ E] [Algebra F₁ M] [Algebra F₂ M] [Algebra E M] [IsScalarTower K F F₁]
  [IsScalarTower K F F₂] [IsScalarTower K F E] [IsScalarTower K F M]
  [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower K F₁ M]
  [IsScalarTower K F₂ M] [IsScalarTower K E M] [IsScalarTower F F₁ M]
  [IsScalarTower F F₂ M] [IsScalarTower F E M] [IsScalarTower F₁ E M]
  [IsScalarTower F₂ E M] [FiniteDimensional F F₁] [FiniteDimensional F F₂]
  [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
  [FiniteDimensional F M] [IsGalois F M]

example
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v)
    (hw₂ : w₂.restrict F = v) (T : Finset (Place K E))
    (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F * W.inertiaDeg F =
      (w₁.ramificationIndex F * w₁.inertiaDeg F)
        * (w₂.ramificationIndex F * w₂.inertiaDeg F) :=
  Place.sum_ramificationIndex_mul_inertiaDeg_bifiber M hgen hLD v w₁ w₂ hw₁ hw₂ T hT

end BifibreZone

/-! ## Zone G — `[exchange]` T6's local exchange and the normal closure -/

#check @Place.sum_ramificationIndex_mul_inertiaDeg_exchange
#check @BifibreW2.exchange_of_isGalois
#check @Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable

-- The `algebraAlong`/`IsScalarTower` setup T7 rehearses: installing the along-map
-- algebra on an abstract algebra hom gives the scalar tower the capstone's own
-- `letI` block needs before calling the exchange.
example {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') :
    letI := algebraAlong φ
    IsScalarTower K F F' :=
  isScalarTower_along φ

-- T7's wire test: the local exchange applied to an abstract square, with the
-- generation and degree hypotheses (`hgen`/`hLD`) as binders so the statement is
-- the pinned one. The `BifibreW2` Galois stage is checked in the same block.
section ExchangeZone

variable {K F F₁ F₂ E : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field E]
  [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K E] [Algebra F F₁] [Algebra F F₂]
  [Algebra F E] [Algebra F₁ E] [Algebra F₂ E] [IsScalarTower K F F₁] [IsScalarTower K F F₂]
  [IsScalarTower K F E] [IsScalarTower K F₁ E] [IsScalarTower K F₂ E] [IsScalarTower F F₁ E]
  [IsScalarTower F F₂ E] [FiniteDimensional F F₁] [FiniteDimensional F F₂]
  [FiniteDimensional F E] [FiniteDimensional F₁ E] [FiniteDimensional F₂ E]
  [Algebra.IsSeparable F E]

example
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ E) ∪ Set.range (algebraMap F₂ E)) = ⊤)
    (hLD : Module.finrank F E = Module.finrank F F₁ * Module.finrank F F₂)
    (v : Place K F) (w₁ : Place K F₁) (w₂ : Place K F₂) (hw₁ : w₁.restrict F = v)
    (hw₂ : w₂.restrict F = v) (T : Finset (Place K E))
    (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂ =
      w₁.inertiaDeg F * w₂.ramificationIndex F :=
  Place.sum_ramificationIndex_mul_inertiaDeg_exchange hgen hLD v w₁ w₂ hw₁ hw₂ T hT

end ExchangeZone

/-! ## Zone H — `[principal]` T8's `P¹` places and degree -/

#check @RationalFunctionField.finite_setOf_ord_ne_zero
#check @RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum
#check @RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum
#check @RationalFunctionField.deg_ofHeightOneSpectrum
#check @RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
#check @RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
#check @RationalFunctionField.degree_eq_zero_of_forall_eq_ord

-- `finite_setOf_ord_ne_zero` and `degree_eq_zero_of_forall_eq_ord`, composed, on
-- the concrete rational function `RatFunc.X`: its ord-support is finite, and the
-- divisor it defines has degree zero.
example (K : Type*) [Field K] :
    {v : Place K (RatFunc K) | v.ord (RatFunc.X : RatFunc K) ≠ 0}.Finite :=
  RationalFunctionField.finite_setOf_ord_ne_zero RatFunc.X_ne_zero

example (K : Type*) [Field K] :
    Divisor.degree (Finsupp.ofSupportFinite
      (fun v : Place K (RatFunc K) => v.ord (RatFunc.X : RatFunc K))
      (RationalFunctionField.finite_setOf_ord_ne_zero RatFunc.X_ne_zero)) = 0 :=
  RationalFunctionField.degree_eq_zero_of_forall_eq_ord _ (fun _ => rfl)

-- `deg_ofHeightOneSpectrum` at the finite place of `Polynomial.X` reads `1`, and
-- `deg_eq_one_of_forall_ne…` composed with `exists_forall_ne…` gives the place at
-- infinity degree `1`.
example (K : Type*) [Field K] :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
      (RationalFunctionField.heightOneSpectrumOfIrreducible K
        Polynomial.irreducible_X)).deg = 1 := by
  rw [RationalFunctionField.deg_ofHeightOneSpectrum K
    (RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal K Polynomial.irreducible_X)]
  exact Polynomial.natDegree_X

example (K : Type*) [Field K] :
    ∃ v : Place K (RatFunc K), v.deg = 1 := by
  obtain ⟨v, hv⟩ := RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  exact ⟨v, RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum v hv⟩

/-! ## Zone I — `[transcendence]` T9's `HasPrincipalDivisors` -/

#check @hasPrincipalDivisors_of_transcendental
#check @hasPrincipalDivisors_adjoin_of_transcendental
#check @hasPrincipalDivisors_of_finiteDimensional_ratFunc

-- `HasPrincipalDivisors K (RatFunc K)` — the `P¹` function field itself.
example (K : Type*) [Field K] [CharZero K] : HasPrincipalDivisors K (RatFunc K) :=
  hasPrincipalDivisors_of_finiteDimensional_ratFunc K (RatFunc K)

-- The transcendence statement at an abstract transcendental generator.
example {K F : Type*} [Field K] [CharZero K] [Field F] [Algebra K F] (x : F)
    (hx : Transcendental K x) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    HasPrincipalDivisors K F :=
  hasPrincipalDivisors_of_transcendental K x hx

-- The composition of the two T9 headlines: the `adjoin` node at `T = ∅` gives
-- `K(x)` itself principal divisors (its proof is `hasPrincipalDivisors_of_transcendental`).
example (K : Type*) [Field K] [CharZero K] {LF : Type*} [Field LF] [Algebra K LF]
    (x : LF) (hx : Transcendental K x) :
    HasPrincipalDivisors K (IntermediateField.adjoin K ({x} : Set LF)) := by
  have h := hasPrincipalDivisors_adjoin_of_transcendental K x hx (∅ : Finset LF) (by simp)
  have hset : (insert x (↑(∅ : Finset LF) : Set LF)) = ({x} : Set LF) := by
    rw [Finset.coe_empty, Set.singleton_def]
  rw [hset] at h
  exact h

/-! ## Zone J — `[exchange]` T7's divisor exchange (the capstone) -/

-- The capstone at its pinned statement. Its hypotheses are `ModularCurve`'s roof
-- square: `hfin`/`hsep` are the free `FiniteAlong`/`SeparableAlong`,
-- `hgen`/`hLD` are the roof's generation and degree facts, and the two
-- `HasPrincipalDivisors` instances are what T9 produces for the modular fields.
#check @Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
#check @Pic0.correspondence_correspondence_comm

-- The wire test: T7's exchange is *applied*, and its conclusion is then consumed
-- as the `hex` hypothesis of T4's `Divisor.correspondence_correspondence`. This is
-- a genuine cross-module composition — the capstone's output discharges a
-- hypothesis no other module supplies — at an abstract square, which is the only
-- possible one (a `Place K K` is empty, as in Zones C–E).
example {K F F₁ F₂ Z : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z]
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] [HasPrincipalDivisors K Z]
    (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂) (u : F₁ →ₐ[K] Z) (u' : F₂ →ₐ[K] Z)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hφ' : φ'.toRingHom.IsIntegral) (hψ' : ψ'.toRingHom.IsIntegral)
    (hu : u.toRingHom.IsIntegral) (hu' : u'.toRingHom.IsIntegral)
    (huφ' : (u'.comp φ').toRingHom.IsIntegral) (huψ : (u.comp ψ).toRingHom.IsIntegral)
    (hsq : u.comp φ = u'.comp ψ')
    (hfin : FiniteAlong K (u'.comp ψ')) (hsep : SeparableAlong K (u'.comp ψ'))
    (hgen : Algebra.adjoin K (Set.range u' ∪ Set.range u) = ⊤)
    (hLD : finrankAlong K (u'.comp ψ') = finrankAlong K ψ' * finrankAlong K φ)
    (D : Divisor K F) :
    Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) =
      Divisor.correspondence (u'.comp φ') (u.comp ψ) huφ' huψ D :=
  Divisor.correspondence_correspondence φ ψ φ' ψ' u u' hφ hψ hφ' hψ' hu hu' huφ' huψ
    (fun E => Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
      ψ' φ u' u hψ' hφ hu' hu hsq hfin hsep hgen hLD E)
    D
