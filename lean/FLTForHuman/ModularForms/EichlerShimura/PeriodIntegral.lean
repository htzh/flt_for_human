/-
  The path-integral period of a weight-2 cusp form for `Γ₀(N)`.

  `segmentPoint`/`segmentPath` are the straight segment from `τ₀` to `τ₁` in `ℍ`
  (with `clamp01` pinning the parameter to `[0,1]`); `periodIntegrand` is the
  integrand `f (τ(t)) · (τ₁ - τ₀)`, and `periodAlong τ₀ τ₁` is its integral over
  `0..1`, a `ℂ`-linear functional on `CuspForm (Γ₀ N) 2`. The `period` of
  `γ ∈ Γ₀(N)` is the along-integral from `I` to `γ • I`, and `periodLattice` is
  the `ℤ`-span of the `period`s — the lattice of periods of weight-2 cusp forms.

  Transcribed verbatim from `Definitions/Def_ModularCurve_PeriodLattice.lean:17–106`
  (the pin's `Period` section, pinned `aa2d8b3`); mathlib-only. The pin's
  `Hecke` section of the same file (the Hecke-stability of the lattice,
  `cuspHeckeGen`/`cuspHeckeRep`/`dualHeckeRep`/`PeriodLatticeHeckeStable`/
  `periodLatticeModule`) is **not** ported: none of the 28 consumers of
  `ModularCurve.exists_hasEquivariantPrimitiveOf` reaches it, and it is the only
  thing that pulls in the Hecke-algebra layer.
-/
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Dual.Defs

set_option autoImplicit false

noncomputable section

open UpperHalfPlane

open scoped MatrixGroups

namespace ModularCurve

section Period

def clamp01 (t : ℝ) : ℝ := max 0 (min t 1)

theorem clamp01_nonneg (t : ℝ) : 0 ≤ clamp01 t := le_max_left _ _

theorem clamp01_le_one (t : ℝ) : clamp01 t ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem continuous_clamp01 : Continuous clamp01 :=
  continuous_const.max (continuous_id.min continuous_const)

theorem clamp01_of_mem {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clamp01 t = t := by
  rw [clamp01, min_eq_left ht.2, max_eq_right ht.1]

def segmentPoint (τ₀ τ₁ : ℍ) (t : ℝ) : ℂ :=
  (1 - clamp01 t) • (τ₀ : ℂ) + clamp01 t • (τ₁ : ℂ)

theorem segmentPoint_im_pos (τ₀ τ₁ : ℍ) (t : ℝ) : 0 < (segmentPoint τ₀ τ₁ t).im := by
  have h0 := clamp01_nonneg t
  have h1 := clamp01_le_one t
  simp only [segmentPoint, Complex.add_im, Complex.smul_im, smul_eq_mul]
  rcases eq_or_lt_of_le h1 with h | h
  · rw [h]; simpa using τ₁.im_pos
  · exact add_pos_of_pos_of_nonneg (mul_pos (by linarith) τ₀.im_pos)
      (mul_nonneg h0 τ₁.im_pos.le)

theorem continuous_segmentPoint (τ₀ τ₁ : ℍ) : Continuous (segmentPoint τ₀ τ₁) :=
  ((continuous_const.sub continuous_clamp01).smul continuous_const).add
    (continuous_clamp01.smul continuous_const)

def segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) : ℍ :=
  UpperHalfPlane.mk (segmentPoint τ₀ τ₁ t) (segmentPoint_im_pos τ₀ τ₁ t)

@[simp] theorem coe_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    ((segmentPath τ₀ τ₁ t : ℍ) : ℂ) = segmentPoint τ₀ τ₁ t := rfl

theorem continuous_segmentPath (τ₀ τ₁ : ℍ) : Continuous (segmentPath τ₀ τ₁) :=
  (continuous_segmentPoint τ₀ τ₁).upperHalfPlaneMk _

variable (N : ℕ)

def periodIntegrand (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

theorem continuous_periodIntegrand (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    Continuous (periodIntegrand N τ₀ τ₁ f) :=
  ((f.holo'.continuous).comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const

theorem intervalIntegrable_periodIntegrand (τ₀ τ₁ : ℍ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (a b : ℝ) :
    IntervalIntegrable (periodIntegrand N τ₀ τ₁ f) MeasureTheory.volume a b :=
  (continuous_periodIntegrand N τ₀ τ₁ f).intervalIntegrable a b

theorem periodIntegrand_add (τ₀ τ₁ : ℍ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodIntegrand N τ₀ τ₁ (f + g) = periodIntegrand N τ₀ τ₁ f + periodIntegrand N τ₀ τ₁ g := by
  funext t
  simp [periodIntegrand, add_mul]

theorem periodIntegrand_smul (τ₀ τ₁ : ℍ) (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodIntegrand N τ₀ τ₁ (c • f) = fun t => c * periodIntegrand N τ₀ τ₁ f t := by
  funext t
  simp [periodIntegrand, mul_assoc]

def periodAlong (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrand N τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrand_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrand N τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrand N τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrand_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

theorem periodAlong_apply (τ₀ τ₁ : ℍ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodAlong N τ₀ τ₁ f = ∫ t in (0 : ℝ)..1, f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) :=
  rfl

def period (γ : CongruenceSubgroup.Gamma0 N) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  periodAlong N UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

theorem period_apply (γ : CongruenceSubgroup.Gamma0 N) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    period N γ f =
      ∫ t in (0 : ℝ)..1, f (segmentPath UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) t) *
        ((((γ : SL(2, ℤ)) • UpperHalfPlane.I : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)) :=
  rfl

def periodLattice : Submodule ℤ (Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)) :=
  Submodule.span ℤ (Set.range (period N))

theorem period_mem_periodLattice (γ : CongruenceSubgroup.Gamma0 N) : period N γ ∈ periodLattice N :=
  Submodule.subset_span (Set.mem_range_self γ)

end Period

end ModularCurve

end
