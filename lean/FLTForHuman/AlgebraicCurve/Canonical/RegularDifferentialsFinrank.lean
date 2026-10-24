/-
The dimension of the regular differentials, after FLT's
`P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean` (220 ln)
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean>).

**Subject.**  The `S = ∅` branch of the pole-bound dictionary: for a non-zero
differential `ω₀` with divisor `W = (ω₀)`, multiplication by `ω₀` identifies the
Riemann–Roch space `L(W)` with the regular differentials `Ω^1_reg`
(`regularDifferentials K F`), and `ell (canonicalDivisorOf hω₀) = genus K F`.  The
dimension statement is Riemann–Roch at `D = 0`: `ℓ(W) = deg W + 1 - g + ℓ(0) =
(2g - 2) + 1 - g + 1 = g`.  The headline is the resulting
`finrank K Ω^1_reg = genus K F`.

**Assumed from earlier modules.**  `smul_mem_regularDifferentials_iff` and everything
below it are the specialization of the general (polar) dictionary in
`Canonical/PolarDifferentials.lean` at `S = ∅`, via
`Defs/PolarDifferentials.lean`'s `polarDifferentials_empty` and
`polarDivisor ∅ = 0`; `regularDifferentials` / `mem_regularDifferentials_iff` are
`Defs/RegularDifferentials.lean`; `canonicalDivisorOf`/`genus` are
`Defs/CanonicalDivisor.lean`; `LSpace`/`ell`/`ConstantsAreBase` are
`Defs/AdelicIndex.lean`.  Riemann–Roch and `ConstantsAreBase` come from
`ResidueTheorem/RRAssembly.lean` (`riemannRoch_and_constantsAreBase`), and the ℤ form
of `ℓ(W) = g` is its `ell_canonicalDivisor_eq_genus_of_riemannRoch`; the ℕ form
`ell_canonical_eq_genus` is that statement cast to `ℕ`.  `exists_smul_eq` is the pin's
`S_` :65 declaration — the rank-one statement with no non-zero hypothesis on the
second argument, which is *not* `IsCurveOver.exists_smul_eq` (that one is Hurwitz's,
with both arguments non-zero, in `Differential/Hurwitz.lean`).

  spec-pin: Theorems/Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean
  Drift against `v4.34.0`: none — the pin's duplicated prelude is not restated (its helpers are the port's `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg` / `Place.differentialCoeff_ne_zero`, its `riemannRoch_and_constantsAreBase` is `ResidueTheorem/RRAssembly.lean`, and its local ℤ-form `ell_canonical_eq_genus` is that module's `ell_canonicalDivisor_eq_genus_of_riemannRoch`), and `smul_mem_regularDifferentials_iff` is *proved* as the `S = ∅` instance of the polar dictionary rather than re-derived per place — its statement is the pin's verbatim.
-/
import FLTForHuman.AlgebraicCurve.Canonical.PolarDifferentials
import FLTForHuman.AlgebraicCurve.Defs.AdelicIndex
import FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor
import FLTForHuman.AlgebraicCurve.Defs.RegularDifferentials
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace RegularDifferentialsFinrank

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ h : F, h • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω

section Comparison

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

theorem smul_mem_regularDifferentials_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : F) :
    h • ω₀ ∈ regularDifferentials K F ↔ h ∈ LSpace (canonicalDivisorOf hω₀) := by
  have hp := PolarFinrank.smul_mem_polarDifferentials_iff (K := K) (F := F)
    (∅ : Finset (Place K F)) hω₀ h
  simpa [polarDivisor, polarDifferentials_empty] using hp

def toRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) →ₗ[K] regularDifferentials K F where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_regularDifferentials_iff hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toRegular_apply {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (h : LSpace (canonicalDivisorOf hω₀)) :
    ((toRegular hω₀ h : regularDifferentials K F) : Ω[F⁄K]) = (h : F) • ω₀ := rfl

theorem toRegular_bijective {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toRegular (K := K) (F := F) hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : regularDifferentials K F => (x : Ω[F⁄K])) hEq
      simp only [toRegular_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ := exists_smul_eq hω₀ ω
    exact ⟨⟨h, (smul_mem_regularDifferentials_iff hω₀ h).mp hω⟩, rfl⟩

def lSpaceCanonicalEquivRegular {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀) ≃ₗ[K] regularDifferentials K F :=
  LinearEquiv.ofBijective (toRegular hω₀) (toRegular_bijective hω₀)

theorem ell_canonical_eq_genus (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    ell (canonicalDivisorOf hω₀) = genus K F := by
  have h := ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω₀
  exact_mod_cast h

end Comparison

end RegularDifferentialsFinrank

/-- **The dimension of the regular differentials is the genus**: `dim Ω^1_reg = g`.
Verbatim from
`Theorems/Thm_AlgebraicCurve_finite_and_finrank_regularDifferentials_eq_genus.lean`; the
proof is the pin's `S_` file's `solution` (`lSpaceCanonicalEquivRegular` onto `L(W)` and
`ell_canonical_eq_genus`). -/
theorem finite_and_finrank_regularDifferentials_eq_genus {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)] :
    Module.Finite K ↥(AlgebraicCurve.regularDifferentials K F) ∧
      Module.finrank K ↥(AlgebraicCurve.regularDifferentials K F) =
        AlgebraicCurve.genus K F := by
  classical
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨hRR, hC⟩ := riemannRoch_and_constantsAreBase (K := K) (F := F)
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
    rw [show LSpace (0 : Divisor K F) = _ from hC]
    infer_instance
  have : FiniteDimensional K ↥(LSpace (canonicalDivisorOf hω₀)) :=
    finiteDimensional_lSpace _
  set e := RegularDifferentialsFinrank.lSpaceCanonicalEquivRegular (K := K) (F := F) hω₀
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact RegularDifferentialsFinrank.ell_canonical_eq_genus hRR hC hω₀

end AlgebraicCurve

end
