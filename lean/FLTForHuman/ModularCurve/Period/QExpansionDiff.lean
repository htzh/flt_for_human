/-
The `q`-expansion of a Kähler differential along a place extension.  This is the
`QExpansionDiff` half of the pin's `Definitions/Def_ModularCurve_QExpansionDiff.lean`
(pinned `aa2d8b3`); the file's `Theta` half (`thetaL`, `thetaL_apply`) is homed in
`ModularCurve/Period/QExpansionDerivative.lean`, and its `TraceDiff` half in
`AlgebraicCurve/Differential/TraceDiff.lean`.  Statements are transcribed verbatim.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QExpansionDiff.lean>

spec-pin: Definitions/Def_ModularCurve_QExpansionDiff.lean
spec-pin: Theorems/Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong.lean
spec-pin: P2M/Sol/S_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.Period.QExpansionDerivative
import FLTForHuman.ModularCurve.Period.ThetaMul
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

set_option autoImplicit false

noncomputable section

namespace ModularCurve

section QExpansionDiff

variable {K F L : Type*} [Field K] [Field F] [Algebra K F] [Field L] [Algebra K L]

def IsQExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) (φ : Ω[F⁄K] →ₗ[K] LaurentSeries L) :
    Prop :=
  (∀ x : F, φ (KaehlerDifferential.D K F x) = thetaL L (σ x)) ∧
    ∀ (f : F) (ω : Ω[F⁄K]), φ (f • ω) = σ f * φ ω

open scoped Classical in

def qExpansionDiffAlong (σ : F →ₐ[K] LaurentSeries L) : Ω[F⁄K] →ₗ[K] LaurentSeries L :=
  if h : ∃ φ : Ω[F⁄K] →ₗ[K] LaurentSeries L, IsQExpansionDiffAlong σ φ then h.choose else 0

/-! ### The canonicity of the `q`-expansion differential

`qExpansionDiffAlong` is a `Classical.choose`, so the content of the leaf row is
that a `K`-linear map agreeing with `θ` on exact differentials and satisfying the
Leibniz rule is *uniquely* determined: the `S_` copy's
`isQExpansionDiffAlong_unique` over the existence construction
`exists_isQExpansionDiffAlong`. -/

/-- `θ = q d/dq` is a derivation on `LaurentSeries L`.  The `S_` copy's
`thetaL_mul`, read off the port's `ModularCurve.theta_mul`. -/
private theorem thetaL_mul {L : Type*} [Field L] (f g : LaurentSeries L) :
    thetaL L (f * g) = thetaL L f * g + f * thetaL L g := by
  rw [thetaL_apply, thetaL_apply, thetaL_apply, theta_mul]
  ring

private theorem algebraMap_laurentSeries_mul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (k : K) (x : LaurentSeries L) :
    algebraMap K (LaurentSeries L) k * x = k • x := by
  rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_mul_eq_smul, algebraMap_smul]

private theorem exists_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F] [Algebra K F]
    [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) :
    ∃ φ : Ω[F⁄K] →ₗ[K] LaurentSeries L, IsQExpansionDiffAlong σ φ := by
  let instF : Module F (LaurentSeries L) :=
    Module.compHom (LaurentSeries L) (σ : F →+* LaurentSeries L)
  have : IsScalarTower K F (LaurentSeries L) :=
    ⟨fun k f x => by
      change σ (k • f) * x = k • (σ f * x)
      rw [Algebra.smul_def k f, map_mul, σ.commutes, mul_assoc, algebraMap_laurentSeries_mul]⟩
  let d₀ : F →ₗ[K] LaurentSeries L :=
    { toFun := fun f => thetaL L (σ f)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun k f => by
        rw [RingHom.id_apply, Algebra.smul_def k f, map_mul, σ.commutes,
          algebraMap_laurentSeries_mul, ← algebraMap_smul (A := L) k (σ f),
          ← algebraMap_smul (A := L) k (thetaL L (σ f)), map_smul] }
  let d : Derivation K F (LaurentSeries L) :=
    Derivation.mk' d₀ fun a b => by
      change thetaL L (σ (a * b)) = σ a * thetaL L (σ b) + σ b * thetaL L (σ a)
      rw [map_mul, thetaL_mul, mul_comm (thetaL L (σ a)) (σ b), add_comm]
  refine ⟨{ toFun := d.liftKaehlerDifferential
            map_add' := fun ω₁ ω₂ => map_add _ ω₁ ω₂
            map_smul' := fun k ω => ?_ }, fun x => ?_, fun f ω => ?_⟩
  · rw [RingHom.id_apply, ← algebraMap_smul (A := F) k ω, map_smul]
    change σ (algebraMap K F k) * _ = _
    rw [σ.commutes, algebraMap_laurentSeries_mul]
  · exact d.liftKaehlerDifferential_comp_D x
  · change d.liftKaehlerDifferential (f • ω) = σ f * d.liftKaehlerDifferential ω
    rw [map_smul]
    rfl

private theorem isQExpansionDiffAlong_qExpansionDiffAlong {K F L : Type*} [Field K] [Field F]
    [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L) :
    IsQExpansionDiffAlong σ (qExpansionDiffAlong σ) := by
  unfold qExpansionDiffAlong
  rw [dite_eq_left (exists_isQExpansionDiffAlong σ)]
  exact (exists_isQExpansionDiffAlong σ).choose_spec

private theorem isQExpansionDiffAlong_unique {K F L : Type*} [Field K] [Field F] [Algebra K F]
    [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L)
    {φ ψ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ)
    (hψ : IsQExpansionDiffAlong σ ψ) : φ = ψ := by
  apply LinearMap.ext
  intro ω
  have hω : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
    rw [KaehlerDifferential.span_range_derivation]; exact Submodule.mem_top
  induction hω using Submodule.span_induction with
  | mem _ hx =>
    obtain ⟨x, rfl⟩ := hx
    rw [hφ.1, hψ.1]
  | zero => rw [map_zero, map_zero]
  | add _ _ _ _ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | smul f _ _ h => rw [hφ.2, hψ.2, h]

/-- **The `q`-expansion differential is canonical.** A `K`-linear map
`Ω[F⁄K] →ₗ[K] LaurentSeries L` that agrees with `θ` on exact differentials and
satisfies the Leibniz rule is `qExpansionDiffAlong σ`. -/
theorem eq_qExpansionDiffAlong_of_isQExpansionDiffAlong {K F L : Type*} [Field K] [Field F]
    [Algebra K F] [Field L] [Algebra K L] (σ : F →ₐ[K] LaurentSeries L)
    {φ : Ω[F⁄K] →ₗ[K] LaurentSeries L} (hφ : IsQExpansionDiffAlong σ φ) :
    φ = qExpansionDiffAlong σ :=
  isQExpansionDiffAlong_unique σ hφ (isQExpansionDiffAlong_qExpansionDiffAlong σ)

end QExpansionDiff

end ModularCurve
