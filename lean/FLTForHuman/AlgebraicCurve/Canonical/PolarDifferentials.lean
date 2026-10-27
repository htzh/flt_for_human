/-
The pole-bound dictionary for differentials: after FLT's
`P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean` (334 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean>).

**Subject.**  For a curve `F/K`, a non-zero differential `ω₀` with divisor `W = (ω₀)`
and a finite set `S` of places, the "pole bound `Σ_S = polarDivisor S`" dictionary:
multiplication by `ω₀` identifies the Riemann–Roch space `L(W + Σ_S)` with the
differentials `polarDifferentials K F (S : Set _)`, i.e. those regular off `S` and with
at most a simple pole at every place of `S`.  Per place the two halves of the
dictionary are `IsRegularAt (h • ω₀) ↔ 0 ≤ v.ord h + W v` and
`HasSimplePoleAt (h • ω₀) ↔ -1 ≤ v.ord h + W v`; taking `S = ∅`
(`polarDifferentials ∅ = regularDifferentials`, `polarDivisor ∅ = 0`) is the regular
case, which `Canonical/RegularDifferentialsFinrank.lean` specializes.  The dimension
half is Riemann–Roch at `D = -Σ_S`: `ℓ(W + Σ_S) = deg W + |S| + 1 - g + ℓ(-Σ_S)`,
where `deg W = 2g - 2`, `ℓ(-Σ_S) = 0` for `S ≠ ∅`; hence the headline
`finrank K (polarDifferentials K F S) = genus K F + S.card - 1`.

**Assumed from earlier modules.**  The pole-bound vocabulary (`Place.IsRegularAt`,
`Place.HasSimplePoleAt`, `polarDifferentials`, `polarDivisor`, and their closure
lemmas) is `Defs/PolarDifferentials.lean`; `Place.dCoord`/`differentialCoeff`/
`ordDifferential`, `canonicalDivisorOf` and `genus` are `Defs/CanonicalDivisor.lean`;
`LSpace`/`ell`/`ConstantsAreBase` are `Defs/AdelicIndex.lean`; `Divisor.degree` is
`Defs/Divisor.lean`.  Riemann–Roch and `ConstantsAreBase` come from
`ResidueTheorem/RRAssembly.lean` (`riemannRoch_and_constantsAreBase`, with the ℤ form
of `ℓ(W) = g` as `ell_canonicalDivisor_eq_genus_of_riemannRoch`); the two side inputs
are `dCoordGenerates_of_isCurveOver` (`Canonical/HasCanonicalDivisor.lean`) and
`finiteDimensional_lSpace` (`Genus/Index.lean`).

`toPolar_bijective`'s surjectivity inlines the pin's `exists_smul_eq` (its `S_` :65),
which is a declaration of the *regular* member of this pair and is stated there; the
two-line rank-one argument is repeated here rather than exported twice.

  spec-pin: Theorems/Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean   -- comparable copy
  spec-pin: Theorems/Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch.lean   -- comparable copy
  Drift against `v4.34.0`: none — the pin's duplicated prelude is not restated (its `ord_nonneg_of_mem_valuationSubring` / `mem_valuationSubring_of_ord_nonneg` / `differentialCoeff_ne_zero` are the port's `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg` / `Place.differentialCoeff_ne_zero`, its `riemannRoch_and_constantsAreBase` is `ResidueTheorem/RRAssembly.lean`, and its ℤ-form `ell_canonical_eq_genus` is `ell_canonicalDivisor_eq_genus_of_riemannRoch`), and no statement differs from the pin's.
-/
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.IsCurveOver
import FLTForHuman.AlgebraicCurve.Defs.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows
import FLTForHuman.AlgebraicCurve.Genus.Index
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace PolarFinrank

section Comparison

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

theorem isRegularAt_smul_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0) (v : Place K F) :
    v.IsRegularAt (h • ω₀) ↔ 0 ≤ v.ord h + canonicalDivisorOf hω₀ v :=
  v.isRegularAt_smul_iff_ord hω₀ hh

theorem hasSimplePoleAt_smul_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0)
    (v : Place K F) :
    v.HasSimplePoleAt (h • ω₀) ↔ -1 ≤ v.ord h + canonicalDivisorOf hω₀ v := by
  have hc : v.differentialCoeff ω₀ ≠ 0 := v.differentialCoeff_ne_zero hω₀
  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  have hπ : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩
    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    subst hgu
    have h0 : 0 ≤ v.ord (v.uniformizer * (h * v.differentialCoeff ω₀)) :=
      v.ord_nonneg_of_mem hg
    rw [v.ord_mul hπ hprod, v.ord_uniformizer, v.ord_mul hh hc] at h0
    linarith
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine v.mem_of_ord_nonneg (mul_ne_zero hπ hprod) ?_
    rw [v.ord_mul hπ hprod, v.ord_uniformizer, v.ord_mul hh hc]
    linarith

theorem smul_mem_polarDifferentials_iff (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (h : F) :
    h • ω₀ ∈ polarDifferentials K F (S : Set (Place K F)) ↔
      h ∈ LSpace (canonicalDivisorOf hω₀ + polarDivisor S) := by
  classical
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [zero_smul, Submodule.zero_mem]
  rw [mem_polarDifferentials_iff, mem_lSpace_iff_ord, or_iff_right hh]
  refine forall_congr' fun v => ?_
  rw [Finsupp.add_apply, polarDivisor_apply, Finset.mem_coe]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv, hasSimplePoleAt_smul_iff hω₀ hh]
    constructor
    · rintro ⟨-, h2⟩; have := h2 hv; linarith
    · intro hle; exact ⟨fun h' => (h' hv).elim, fun _ => by linarith⟩
  · rw [ite_eq_right hv, isRegularAt_smul_iff hω₀ hh]
    constructor
    · rintro ⟨h1, -⟩; have := h1 hv; linarith
    · intro hle; exact ⟨fun _ => by linarith, fun h' => (hv h').elim⟩

def toPolar (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀ + polarDivisor S) →ₗ[K]
      polarDifferentials K F (S : Set (Place K F)) where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_polarDifferentials_iff S hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toPolar_apply (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (h : LSpace (canonicalDivisorOf hω₀ + polarDivisor S)) :
    ((toPolar S hω₀ h : polarDifferentials K F (S : Set (Place K F))) : Ω[F⁄K]) = (h : F) • ω₀ :=
  rfl

theorem toPolar_bijective (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toPolar (K := K) (F := F) S hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : polarDifferentials K F (S : Set (Place K F)) => (x : Ω[F⁄K])) hEq
      simp only [toPolar_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ :=
      (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω
    exact ⟨⟨h, (smul_mem_polarDifferentials_iff S hω₀ h).mp hω⟩, rfl⟩

def lSpaceEquivPolar (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀ + polarDivisor S) ≃ₗ[K]
      polarDifferentials K F (S : Set (Place K F)) :=
  LinearEquiv.ofBijective (toPolar S hω₀) (toPolar_bijective S hω₀)

theorem degree_canonical_eq (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω₀) = 2 * (genus K F : ℤ) - 2 := by
  have h := hRR hω₀ (canonicalDivisorOf hω₀)
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at h
  have hg := ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω₀
  push_cast at h
  linarith

omit [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] in

theorem ord_algebraMap_eq_zero (v : Place K F) {c : K} (hc : c ≠ 0) :
    v.ord (algebraMap K F c) = 0 := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := v.ord_nonneg_of_mem (v.algebraMap_mem' c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := v.ord_nonneg_of_mem (v.algebraMap_mem' c⁻¹)
  have hne : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hne' : algebraMap K F c⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hc)
  have h3 : v.ord (algebraMap K F c * algebraMap K F c⁻¹) = 0 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one, v.ord_one]
  rw [v.ord_mul hne hne'] at h3
  linarith

omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] in
-- The pin's `omit` here drops only those two, so the declaration keeps the unused
-- `[IsCurveOver K F]` section binder: the binder list is part of the verbatim signature.
set_option linter.unusedSectionVars false in

theorem lSpace_neg_polarDivisor_eq_bot (hC : ConstantsAreBase K F) (S : Finset (Place K F))
    (hS : S.Nonempty) : LSpace (-polarDivisor S) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have hle : -polarDivisor S ≤ (0 : Divisor K F) := by
    intro v
    rw [Finsupp.neg_apply, polarDivisor_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs <;> norm_num
  have hf0 : f ∈ LSpace (0 : Divisor K F) := lSpace_mono hle hf
  rw [show LSpace (0 : Divisor K F) = _ from hC] at hf0
  obtain ⟨c, rfl⟩ := hf0
  rw [Submodule.mem_bot]
  by_contra hne
  have hc : c ≠ 0 := fun h => hne (by rw [h]; simp)
  obtain ⟨v₀, hv₀⟩ := hS
  have h := (mem_lSpace_iff_ord.mp hf).resolve_left hne v₀
  rw [Finsupp.neg_apply, neg_neg, polarDivisor_apply, ite_eq_left hv₀] at h
  have h0 : v₀.ord (Algebra.linearMap K F c) = 0 := ord_algebraMap_eq_zero v₀ hc
  rw [h0] at h
  exact absurd h (by norm_num)

omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] in

theorem degree_polarDivisor [IsAlgClosed K] (S : Finset (Place K F)) :
    Divisor.degree (polarDivisor S) = S.card := by
  rw [polarDivisor, map_sum]
  have h : ∀ v ∈ S, Divisor.degree (Finsupp.single v (1 : ℤ)) = 1 := by
    intro v _
    have : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
    rw [Divisor.degree_single, v.deg_eq_one_of_isAlgClosed_of_finite]
    norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem ell_canonical_add_polarDivisor [IsAlgClosed K] (hRR : FunctionFieldRiemannRoch K F)
    (hC : ConstantsAreBase K F) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (S : Finset (Place K F))
    (hS : S.Nonempty) :
    ell (canonicalDivisorOf hω₀ + polarDivisor S) = genus K F + S.card - 1 := by
  have h := hRR hω₀ (canonicalDivisorOf hω₀ + polarDivisor S)
  rw [sub_add_cancel_left, show ell (-polarDivisor S) = 0 by
      rw [ell, lSpace_neg_polarDivisor_eq_bot hC S hS, finrank_bot],
    map_add, degree_canonical_eq hRR hC hω₀, degree_polarDivisor S] at h
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  push_cast at h
  omega

end Comparison

end PolarFinrank

/-- **The dimension of the polar differentials**: `Ω^1(S)` has dimension
`g + |S| - 1`.  Verbatim from
`Theorems/Thm_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean`; the proof
is the pin's `S_` file's `solution` (`lSpaceEquivPolar` onto `L(W + Σ_S)` and
`ell_canonical_add_polarDivisor`). -/
theorem finite_and_finrank_polarDifferentials_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (hS : S.Nonempty) :
    Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧
      Module.finrank K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) =
        AlgebraicCurve.genus K F + S.card - 1 := by
  classical
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨hRR, hC⟩ := riemannRoch_and_constantsAreBase (K := K) (F := F)
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
    rw [show LSpace (0 : Divisor K F) = _ from hC]
    infer_instance
  have : FiniteDimensional K ↥(LSpace (canonicalDivisorOf hω₀ + polarDivisor S)) :=
    finiteDimensional_lSpace _
  set e := PolarFinrank.lSpaceEquivPolar (K := K) (F := F) S hω₀
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact PolarFinrank.ell_canonical_add_polarDivisor hRR hC hω₀ S hS

/-- **The degree of the canonical divisor** is `2g - 2`, from Riemann–Roch at `0` and at
`W` together with `ℓ(0) = 1`.  The statement is the pin's
(`Theorems/Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch.lean`); the port
already has it as `PolarFinrank.degree_canonical_eq` above, so this declaration is a
restatement of that one under the pinned name. -/
theorem degree_canonicalDivisor_eq_of_riemannRoch {K F : Type*} [Field K] [Field F] [Algebra K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : ℤ) - 2 :=
  PolarFinrank.degree_canonical_eq hRR hC hω

end AlgebraicCurve

end
