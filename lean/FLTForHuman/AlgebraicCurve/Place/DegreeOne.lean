/-
The generic degree-one place facts: over an algebraically closed base `K`, every
place of a function field `F` has degree one as soon as `F` is algebraic over
`K(t)` for one `t`.

Two public statements, both `Theorems/` wrappers and so verified by name:

* `AlgebraicCurve.isAlgebraic_adjoin_of_transcendental` — two elements of `F`
  transcendental over `K` generate the same algebraic closure, so `F` is algebraic
  over `K(t)` whenever it is algebraic over `K(x)`;
* `AlgebraicCurve.Place.deg_eq_one_of_isAlgebraic_adjoin` — the `deg = 1`
  conclusion for any place, from the residue-field surjectivity below.

The pin's `B2Deg` block in
`P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean` carries the last
statement plus the two helpers `valuation_aeval_eq_one` /
`surjective_algebraMap_residueField`; the pin keeps them out of the exported
surface, so the port writes them `private` here and promotes only
`deg_eq_one_of_isAlgebraic_adjoin`, which the pin's `S_` file declares publicly
under `B2Deg`.

**Third subject (SET 9): `Place.isRational_of_isAlgClosed`.**  The same conclusion one level up:
for `[IsAlgClosed K]` and `F` a finite extension of `RatFunc K` (`[Algebra (RatFunc K) F]`,
`[IsScalarTower K (RatFunc K) F]`, `[FiniteDimensional (RatFunc K) F]`), **every** place of `F`
over `K` is rational — no `IsCurveOver` and no characteristic bound.  The proof restricts the
place to `RatFunc K` (where `deg = 1` is `deg_eq_one_of_isAlgebraic_adjoin`'s own case), picks a
coefficient of minimal `v`-order in a polynomial annihilating a residue generator, and concludes
that the residue of every element is the residue of a constant.

The `isAlgebraic_adjoin_of_transcendental` proof is the pin's
`P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean` verbatim: two
transcendence bases of a domain have the same cardinality, and `{x}` is one for
`K(x)`, so the transcendence basis extending `{t}` must be `{t}` itself.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean

spec-pin: Theorems/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean   -- comparable copy
spec-pin: Theorems/Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean
spec-pin: P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean   -- the `B2Deg` block
spec-pin: Theorems/Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.PlaceEvaluation
import Mathlib.FieldTheory.RatFunc.IntermediateField
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Data.Set.Subsingleton
import Mathlib.SetTheory.Cardinal.Basic

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false

noncomputable section

open Set Cardinal Polynomial

namespace AlgebraicCurve

theorem isAlgebraic_adjoin_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) [Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F] {t : F}
    (ht : Transcendental K t) :
    Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F := by
  have halg : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F := inferInstance
  have hx : Transcendental K x := by
    intro hxalg
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K ({x} : Set F)) :=
      IntermediateField.isAlgebraic_adjoin_simple hxalg.isIntegral
    haveI : Algebra.IsAlgebraic K F :=
      Algebra.IsAlgebraic.trans K (IntermediateField.adjoin K ({x} : Set F)) F
    exact ht (Algebra.IsAlgebraic.isAlgebraic t)

  have hbx : IsTranscendenceBasis K ![x] := by
    rw [isTranscendenceBasis_iff_algebraicIndependent_isAlgebraic]
    refine ⟨algebraicIndependent_iff_transcendental.mpr hx, ?_⟩
    have : Set.range ![x] = {x} := by simp
    rw [this]
    exact (IntermediateField.isAlgebraic_adjoin_iff_top (F := K) (s := ({x} : Set F))).mp halg

  have hind : AlgebraicIndepOn K id ({t} : Set F) := by
    rw [AlgebraicIndepOn, algebraicIndependent_unique_type_iff]
    simpa using ht
  obtain ⟨S, htS, hS⟩ := exists_isTranscendenceBasis_superset hind

  have hcard := hS.lift_cardinalMk_eq hbx
  simp only [Cardinal.mk_fin, Nat.cast_one, Cardinal.lift_one, Cardinal.lift_eq_one] at hcard
  have hS_eq : S = {t} :=
    (Cardinal.mk_le_one_iff_set_subsingleton.mp hcard.le).eq_singleton_of_mem (htS rfl)
  subst hS_eq
  have h := hS.isAlgebraic_field
  rwa [Subtype.range_coe] at h

private theorem valuation_aeval_eq_one {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (w : Place K F) (y : F)
    (hy : ∀ c : K, w.toValuationSubring.valuation (y - algebraMap K F c) = 1)
    (p : K[X]) (hp : p ≠ 0) :
    w.toValuationSubring.valuation (aeval y p) = 1 := by
  have hconst : ∀ a : K, a ≠ 0 → w.toValuationSubring.valuation (algebraMap K F a) = 1 := by
    intro a ha
    have hu := (IsUnit.mk0 a ha).map (algebraMap K w.toValuationSubring)
    have h1 := (w.toValuationSubring.valuation_eq_one_iff _).mp hu
    rwa [Place.coe_algebraMap] at h1
  have hsplit := IsAlgClosed.splits p
  have hp' : aeval y p = aeval y (C p.leadingCoeff * (p.roots.map (X - C ·)).prod) := by
    rw [← hsplit.eq_prod_roots]
  rw [hp']
  simp only [map_mul, map_multiset_prod, Multiset.map_map]
  rw [aeval_C, hconst _ (leadingCoeff_ne_zero.mpr hp), one_mul]
  refine Multiset.prod_eq_one fun x hx => ?_
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.mp hx
  simpa using hy c

private theorem surjective_algebraMap_residueField {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (t : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F] (w : Place K F) :
    Function.Surjective (algebraMap K w.ResidueField) := by
  intro yb
  obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective yb
  suffices h : ∃ c : K, y - algebraMap K w.toValuationSubring c ∈
      IsLocalRing.maximalIdeal w.toValuationSubring by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    show IsLocalRing.residue _ (algebraMap K w.toValuationSubring c) = IsLocalRing.residue _ y
    rw [eq_comm, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact hc
  by_cases halg : IsAlgebraic K (y : F)
  ·
    have hdeg := IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral)
    obtain ⟨c, hc⟩ := minpoly.mem_range_of_degree_eq_one K (y : F) hdeg
    refine ⟨c, ?_⟩
    have h0 : y - algebraMap K w.toValuationSubring c = 0 := Subtype.ext (by simp [← hc])
    rw [h0]
    exact zero_mem _
  ·

    have ht : Transcendental K (y : F) := halg
    haveI := AlgebraicCurve.isAlgebraic_adjoin_of_transcendental t ht
    by_contra hcon
    simp only [not_exists] at hcon
    have hunit : ∀ c : K, w.toValuationSubring.valuation ((y : F) - algebraMap K F c) = 1 := by
      intro c
      have hle := w.toValuationSubring.valuation_le_one (y - algebraMap K w.toValuationSubring c)
      have hnlt : ¬ w.toValuationSubring.valuation
          ((y - algebraMap K w.toValuationSubring c : w.toValuationSubring) : F) < 1 :=
        fun hlt => hcon c ((w.toValuationSubring.valuation_lt_one_iff _).mpr hlt)
      have heq := hle.eq_of_not_lt hnlt
      simpa using heq
    have hadj : ∀ z : F, z ∈ IntermediateField.adjoin K ({(y : F)} : Set F) →
        z ∈ w.toValuationSubring := by
      intro z hz
      rw [IntermediateField.mem_adjoin_simple_iff] at hz
      obtain ⟨r, s, rfl⟩ := hz
      rw [← w.toValuationSubring.valuation_le_one_iff, map_div₀]
      by_cases hr : r = 0
      · simp [hr]
      by_cases hs : s = 0
      · simp [hs]
      simp only [valuation_aeval_eq_one w y hunit r hr, valuation_aeval_eq_one w y hunit s hs, div_one,
        le_refl]
    apply (w.restrict (IntermediateField.adjoin K ({(y : F)} : Set F))).ne_top'
    refine SetLike.ext fun z => ⟨fun _ => ValuationSubring.mem_top z, fun _ => ?_⟩
    rw [Place.mem_restrict_iff, IntermediateField.algebraMap_apply]
    exact hadj z z.2

theorem Place.deg_eq_one_of_isAlgebraic_adjoin {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsAlgClosed K] (t : F)
    [Algebra.IsAlgebraic (IntermediateField.adjoin K ({t} : Set F)) F] (w : Place K F) :
    w.deg = 1 := by
  haveI : Module.Finite K w.ResidueField :=
    Module.Finite.of_surjective (Algebra.linearMap K w.ResidueField)
      (surjective_algebraMap_residueField t w)
  exact w.deg_eq_one_of_isAlgClosed_of_finite

/-- **Every place over an algebraically closed constant field is rational**, for `F` a finite
extension of `RatFunc K`.  Statement from
`Theorems/Thm_AlgebraicCurve_Place_isRational_of_isAlgClosed.lean`, proof from the pin's
`solution`: restrict `v` to `RatFunc K` (rational by the ℙ¹ case), take a polynomial `p`
annihilating a residue generator `x`, divide by the coefficient of minimal `v`-order to land in
the valuation ring, and read through `IsLocalRing.residue` that the residue of `x` is the residue
of a constant. -/
theorem Place.isRational_of_isAlgClosed {K F : Type*} [Field K] [IsAlgClosed K] [Field F]
    [Algebra K F] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [FiniteDimensional (RatFunc K) F] (v : Place K F) : v.IsRational := by
  classical
  intro y
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y

  let u : Place K (RatFunc K) := v.restrict (RatFunc K)
  -- the ℙ¹ step: the module's own engine at `t = RatFunc.X`, whose `K`-adjoin is everything
  -- (the pin takes it from `RationalFunctionField.deg_eq_one_of_isAlgClosed`)
  have hu : u.IsRational := by
    haveI : Algebra.IsAlgebraic (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K) := by
      rw [RatFunc.adjoin_X]
      infer_instance
    exact (Place.isRational_iff_deg_eq_one u).2
      (Place.deg_eq_one_of_isAlgebraic_adjoin (K := K) (F := RatFunc K) RatFunc.X u)

  have hconst : ∀ {b : RatFunc K} (hb : algebraMap (RatFunc K) F b ∈ v.toValuationSubring),
      ∃ c : K, algebraMap K v.ResidueField c
        = IsLocalRing.residue _ (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring) := by
    intro b hb
    have hb' : b ∈ u.toValuationSubring := ValuationSubring.mem_comap.mpr hb
    refine ⟨u.evalAt b, ?_⟩
    have h1 : algebraMap K u.ResidueField (u.evalAt b) = IsLocalRing.residue _ ⟨b, hb'⟩ :=
      u.algebraMap_evalAt hu hb'
    have h2 : (⟨algebraMap (RatFunc K) F b, hb⟩ : v.toValuationSubring)
        = Place.restrictInclusion (RatFunc K) v ⟨b, hb'⟩ := rfl
    rw [h2, ← Place.restrictResidueMap_residue, ← h1, ← Place.algebraMap_residueField_eq,
      ← IsScalarTower.algebraMap_apply]

  obtain ⟨p, hp0, hpx⟩ : IsAlgebraic (RatFunc K) (x : F) := Algebra.IsAlgebraic.isAlgebraic _

  have hsupp : p.support.Nonempty := Polynomial.support_nonempty.mpr hp0
  obtain ⟨j, hj, hjmin⟩ := p.support.exists_min_image
    (fun i => v.ord (algebraMap (RatFunc K) F (p.coeff i))) hsupp
  have haj0 : p.coeff j ≠ 0 := Polynomial.mem_support_iff.mp hj
  have hajF : algebraMap (RatFunc K) F (p.coeff j) ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr haj0

  have hbmem : ∀ i, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) ∈ v.toValuationSubring := by
    intro i
    by_cases hi : i ∈ p.support
    · have hai0 : p.coeff i ≠ 0 := Polynomial.mem_support_iff.mp hi
      have haiF : algebraMap (RatFunc K) F (p.coeff i) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap (RatFunc K) F).injective).mpr hai0
      rw [map_div₀]
      refine v.mem_of_ord_nonneg (div_ne_zero haiF hajF) ?_
      rw [div_eq_mul_inv, v.ord_mul haiF (inv_ne_zero hajF), v.ord_inv]
      have := hjmin i hi
      omega
    · rw [Polynomial.notMem_support_iff.mp hi, zero_div, map_zero]
      exact zero_mem _

  have haeval : ∀ (q : (RatFunc K)[X]) (z : F),
      aeval z q = ∑ i ∈ q.support, algebraMap (RatFunc K) F (q.coeff i) * z ^ i := by
    intro q z
    conv_lhs => rw [q.as_sum_support]
    simp [map_sum, ← C_mul_X_pow_eq_monomial]

  have hrel : ∑ i ∈ p.support,
      algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i = 0 := by
    have hsum : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i = 0 := by
      rw [← haeval, hpx]
    have hfac : ∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i / p.coeff j) * (x : F) ^ i
        = (∑ i ∈ p.support, algebraMap (RatFunc K) F (p.coeff i) * (x : F) ^ i)
            / algebraMap (RatFunc K) F (p.coeff j) := by
      rw [div_eq_mul_inv, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_div₀]
      ring
    rw [hfac, hsum, zero_div]

  set B : ℕ → v.toValuationSubring := fun i => ⟨_, hbmem i⟩ with hB
  have hrelO : ∑ i ∈ p.support, B i * x ^ i = 0 := by
    apply Subtype.ext
    simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, SubmonoidClass.coe_pow,
      ZeroMemClass.coe_zero, hB]
    exact hrel

  choose c hc using fun i => hconst (hbmem i)
  have hcj : c j = 1 := by
    have h1 : (B j) = 1 := Subtype.ext (by simp [hB, haj0])
    have := hc j
    rw [show (⟨_, hbmem j⟩ : v.toValuationSubring) = B j from rfl, h1, map_one] at this
    exact (algebraMap K v.ResidueField).injective (by rw [this, map_one])

  set R : K[X] := ∑ i ∈ p.support, C (c i) * X ^ i with hR
  have hRy : aeval (IsLocalRing.residue v.toValuationSubring x) R = 0 := by
    have h := congrArg (IsLocalRing.residue v.toValuationSubring) hrelO
    rw [map_sum, map_zero] at h
    simp only [map_mul, map_pow] at h
    rw [hR, map_sum]
    simp only [map_mul, map_pow, aeval_C, aeval_X]
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hc i]
  have hRj : R.coeff j = 1 := by
    rw [hR, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    simp [hj, hcj]
  have hR0 : R ≠ 0 := fun h => by
    have := hRj
    rw [h, coeff_zero] at this
    exact zero_ne_one this

  have halgy : IsAlgebraic K (IsLocalRing.residue v.toValuationSubring x) := ⟨R, hR0, hRy⟩
  have hdeg : (minpoly K (IsLocalRing.residue v.toValuationSubring x)).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halgy.isIntegral)
  obtain ⟨a, ha⟩ := minpoly.degree_eq_one_iff.mp hdeg
  exact ⟨a, ha⟩

end AlgebraicCurve

end
