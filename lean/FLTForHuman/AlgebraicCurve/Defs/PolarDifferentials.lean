/-
The pole-bound differential submodule: regular at all but finitely many places, at most a
simple pole at the places of a finite set `S`, after FLT's
`Definitions/Def_AlgebraicCurve_PolarDifferentials.lean` (200 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_PolarDifferentials.lean>).

Vocabulary only: the per-place predicates `IsRegularAt` / `HasSimplePoleAt` (a differential is
regular at `v` when it is an `O_v`-multiple of `dCoord`, and has at most a simple pole there when
`uniformizer · f` is integral), the submodule `polarDifferentials S`, and the divisor
`polarDivisor S = Σ_{v ∈ S} v` that bounds it — both are taken from the pin's `S_` file
`P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean:74`
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean#L74>),
where the pin defines it beside its first use; the port keeps definitions in the definition
layer, and the divisor vocabulary lives here beside `Divisor` and `canonicalDivisorOf`.

`polarDifferentials ∅ = regularDifferentials` (`polarDifferentials_empty`), so the regular
differentials are the `S = ∅` instance; the theory module `Canonical/PolarDifferentials.lean`
states the divisor dictionary for a general finite `S` and
`Canonical/RegularDifferentialsFinrank.lean` specializes it.

The per-place engine `Place.isRegularAt_smul_iff_ord` (no `IsCurveOver` binder) is shared by that
theory and by `Canonical/WeilDifferential.lean`, whose `h = 1` case is the
`regular ↔ canonical divisor is effective` pair.  See
`topics/algebraicCurve/TOPIC-differentials-pole-bound.md`.

**Deferred, not this module** (none of it is reached by the dimension theory; its consumers are
the residue theorem's residue-data nodes and the Pic⁰ gluing): `Place.HasSimpleResidue`,
`Place.irreducible_mk_uniformizer`, `HasSimpleResidue.hasSimplePoleAt`,
`hasSimpleResidue_zero_of_mem`, `IsGluedPolarPair`, `gluedPolarDifferentials` and its five
lemmas, and the `Place.HasValue` block they rest on (which lives in
`Definitions/Def_AlgebraicCurve_GluedPic0.lean` together with `GluingData` / `gluedPrincipal`).

  spec-pin: Definitions/Def_AlgebraicCurve_PolarDifferentials.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean   -- polarDivisor
  Drift against `v4.34.0`: definitions only, statements are the pin's verbatim.
-/
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Defs.LocalResidue
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

/-- `ω` is regular at `v`: it is an integral multiple of the local generator `dCoord`. -/
def IsRegularAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord

/-- `ω` has at most a simple pole at `v`: `uniformizer · f` is integral. -/
def HasSimplePoleAt (ω : Ω[F⁄K]) : Prop :=
  ∃ f : F, v.uniformizer * f ∈ v.toValuationSubring ∧ ω = f • v.dCoord

variable {v}

variable (v) in
theorem uniformizer_mem_toValuationSubring : v.uniformizer ∈ v.toValuationSubring :=
  SetLike.coe_mem (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose

theorem IsRegularAt.hasSimplePoleAt {ω : Ω[F⁄K]} (h : v.IsRegularAt ω) : v.HasSimplePoleAt ω := by
  obtain ⟨f, hf, rfl⟩ := h
  exact ⟨f, mul_mem v.uniformizer_mem_toValuationSubring hf, rfl⟩

variable (v) in
theorem isRegularAt_zero : v.IsRegularAt (0 : Ω[F⁄K]) :=
  ⟨0, zero_mem _, by rw [zero_smul]⟩

theorem IsRegularAt.add {ω η : Ω[F⁄K]} (hω : v.IsRegularAt ω) (hη : v.IsRegularAt η) :
    v.IsRegularAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, add_mem hf hg, by rw [add_smul]⟩

theorem IsRegularAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.IsRegularAt ω) : v.IsRegularAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, mul_mem (v.algebraMap_mem' c) hf, ?_⟩
  rw [mul_smul, algebraMap_smul]

variable (v) in
theorem hasSimplePoleAt_zero : v.HasSimplePoleAt (0 : Ω[F⁄K]) :=
  ⟨0, by rw [mul_zero]; exact zero_mem _, by rw [zero_smul]⟩

theorem HasSimplePoleAt.add {ω η : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) (hη : v.HasSimplePoleAt η) :
    v.HasSimplePoleAt (ω + η) := by
  obtain ⟨f, hf, rfl⟩ := hω
  obtain ⟨g, hg, rfl⟩ := hη
  exact ⟨f + g, by rw [mul_add]; exact add_mem hf hg, by rw [add_smul]⟩

theorem HasSimplePoleAt.smul (c : K) {ω : Ω[F⁄K]} (hω : v.HasSimplePoleAt ω) :
    v.HasSimplePoleAt (c • ω) := by
  obtain ⟨f, hf, rfl⟩ := hω
  refine ⟨algebraMap K F c * f, ?_, by rw [mul_smul, algebraMap_smul]⟩
  rw [mul_left_comm]
  exact mul_mem (v.algebraMap_mem' c) hf

section Dictionary

variable [HasCanonicalDivisor (K := K) (F := F)]

/-- **The per-place half of the pole-bound dictionary.**  Multiplying by `h` shifts the divisor by
`(h)`, so `h · ω₀` is regular at `v` exactly when `0 ≤ v.ord h + (ω₀)(v)`.

Named `_ord` because it is the general engine, not the pin's declaration: it is the pin's
`isRegularAt_smul_iff` without its unused `[IsCurveOver K F]` section binder.  The proof needs only
`[HasCanonicalDivisor]`, `[v.DCoordGenerates]` and `[Nontrivial Ω[F⁄K]]`, and the Weil-differential
bridge (`Canonical/WeilDifferential.lean`) has no `IsCurveOver` to offer; the polar theory states the
pin's binder verbatim on top of this lemma. -/
theorem isRegularAt_smul_iff_ord (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0) :
    v.IsRegularAt (h • ω₀) ↔ 0 ≤ v.ord h + canonicalDivisorOf hω₀ v := by
  have hc : v.differentialCoeff ω₀ ≠ 0 := v.differentialCoeff_ne_zero hω₀
  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩
    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    have h0 : 0 ≤ v.ord (h * v.differentialCoeff ω₀) := hgu ▸ v.ord_nonneg_of_mem hg
    rw [v.ord_mul hh hc] at h0
    exact h0
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine v.mem_of_ord_nonneg hprod ?_
    rw [v.ord_mul hh hc]
    exact hle

end Dictionary

end Place

section Polar

variable (K F)

/-- Differentials regular off `S` and with at most a simple pole at every place of `S`. -/
def polarDifferentials (S : Set (Place K F)) : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω)}
  zero_mem' v := ⟨fun _ => v.isRegularAt_zero, fun _ => v.hasSimplePoleAt_zero⟩
  add_mem' hω hη v :=
    ⟨fun hv => ((hω v).1 hv).add ((hη v).1 hv), fun hv => ((hω v).2 hv).add ((hη v).2 hv)⟩
  smul_mem' c _ hω v := ⟨fun hv => ((hω v).1 hv).smul c, fun hv => ((hω v).2 hv).smul c⟩

variable {K F}

/-- The divisor `Σ_{v ∈ S} v` of a finite pole set: the pole bound of `polarDifferentials S`. -/
def polarDivisor (S : Finset (Place K F)) : Divisor K F := ∑ v ∈ S, Finsupp.single v 1

theorem mem_polarDifferentials_iff {S : Set (Place K F)} {ω : Ω[F⁄K]} :
    ω ∈ polarDifferentials K F S ↔
      ∀ v : Place K F, (v ∉ S → v.IsRegularAt ω) ∧ (v ∈ S → v.HasSimplePoleAt ω) :=
  Iff.rfl

open scoped Classical in
theorem polarDivisor_apply (S : Finset (Place K F)) (v : Place K F) :
    polarDivisor S v = if v ∈ S then 1 else 0 := by
  rw [polarDivisor, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem hasSimplePoleAt_of_mem_polarDifferentials {S : Set (Place K F)} {ω : Ω[F⁄K]}
    (h : ω ∈ polarDifferentials K F S) (v : Place K F) : v.HasSimplePoleAt ω := by
  by_cases hv : v ∈ S
  · exact (h v).2 hv
  · exact ((h v).1 hv).hasSimplePoleAt

theorem regularDifferentials_le_polarDifferentials (S : Set (Place K F)) :
    regularDifferentials K F ≤ polarDifferentials K F S := fun ω hω v =>
  ⟨fun _ => hω v, fun _ => (show v.IsRegularAt ω from hω v).hasSimplePoleAt⟩

theorem polarDifferentials_mono {S T : Set (Place K F)} (h : S ⊆ T) :
    polarDifferentials K F S ≤ polarDifferentials K F T := fun _ hω v =>
  ⟨fun hv => (hω v).1 fun hs => hv (h hs), fun _ => hasSimplePoleAt_of_mem_polarDifferentials hω v⟩

theorem polarDifferentials_empty : polarDifferentials K F ∅ = regularDifferentials K F := by
  refine le_antisymm (fun ω hω v => (hω v).1 (Set.notMem_empty v)) ?_
  exact regularDifferentials_le_polarDifferentials ∅

end Polar

end AlgebraicCurve

end
