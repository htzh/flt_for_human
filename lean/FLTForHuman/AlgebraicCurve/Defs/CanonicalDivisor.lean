/-
Canonical divisors and the Kähler differential coefficient, after FLT's
`Definitions/Def_ModularCurve_CanonicalDivisor.lean` (97 ln) and
`Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean` (42 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_CanonicalDivisor.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean>).

The pin splits this by artifact kind (`ModularCurve` = the `Place.dCoord` block,
`AlgebraicCurve` = `HasCanonicalDivisor`/`genus`); in the port's tree both are
`AlgebraicCurve.Place`/`AlgebraicCurve` vocabulary, so they merge here.

The pin keeps `uniformizer` (and its two order lemmas) `private` in this file and
re-exposes them publicly in
`Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean:18–27`.  Set D
transcribed the `private` copies; the refactor round promotes them here (their
pin-public home is that re-export file, already in `SOURCES`) and leaves
`Defs/CanonicalDivisorUniformizer.lean` only `dCoord_eq`, so the port has a single
`Place.uniformizer`.  `Pic` now lives in `Defs/Divisor.lean` beside `Pic0`.
-/
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Kaehler.Basic

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable (v : Place K F)

def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer

class DCoordGenerates : Prop where
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 := by
  intro h0
  have htop := DCoordGenerates.span_eq_top (v := v)
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hx_mem : x ∈ Submodule.span F {v.dCoord} := htop ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hx_mem
  exact hx hx_mem

def differentialCoeff (ω : Ω[F⁄K]) : F :=
  letI := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0

theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω := by
  rw [differentialCoeff, dif_pos (v.exists_eq_smul_dCoord ω)]
  exact (v.exists_eq_smul_dCoord ω).choose_spec.symm

theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f := by
  have key : (v.differentialCoeff ω - f) • v.dCoord = 0 := by
    rw [sub_smul, v.differentialCoeff_smul_dCoord ω, hf, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h v.dCoord_ne_zero

@[simp]
theorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff v.dCoord = 1 :=
  v.differentialCoeff_unique (one_smul F v.dCoord).symm

@[simp]
theorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=
  v.differentialCoeff_unique (zero_smul F v.dCoord).symm

theorem differentialCoeff_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : F) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = c * v.differentialCoeff ω :=
  v.differentialCoeff_unique
    (by rw [mul_smul, v.differentialCoeff_smul_dCoord])

def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.ordDifferential v.dCoord = 0 := by
  rw [ordDifferential, v.differentialCoeff_dCoord, v.ord_one]

theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :
    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω := by
  rw [ordDifferential, ordDifferential, v.differentialCoeff_smul, v.ord_mul hc hω]

end Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

class HasCanonicalDivisor : Prop where
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose

theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : Pic K F :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0 then QuotientAddGroup.mk (canonicalDivisorOf h.choose_spec)
  else 0

def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0
  then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
  else 0

end AlgebraicCurve

end
