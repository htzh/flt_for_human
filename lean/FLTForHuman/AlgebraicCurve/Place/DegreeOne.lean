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

The `isAlgebraic_adjoin_of_transcendental` proof is the pin's
`P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean` verbatim: two
transcendence bases of a domain have the same cardinality, and `{x}` is one for
`K(x)`, so the transcendence basis extending `{t}` must be `{t}` itself.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_isAlgebraic_adjoin_of_transcendental.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_deg_eq_one_modularFunctionFieldBar.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
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

end AlgebraicCurve

end
