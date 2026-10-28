/-
  Periods of an equivariant primitive: the general-level API.

  For a subgroup `Γ ≤ SL(2, ℤ)`, `periodOf` is the period of an equivariant
  primitive along `I → γ • I`, `periodLatticeOf` its `ℤ`-span,
  `HasEquivariantPrimitiveOf` the bundled predicate (primitive, vanishing at
  `∞`, equivariant, bounded at every cusp), and `periodMapOf` the resulting
  period homomorphism, chosen from the predicate by `Classical.choose` and `0`
  when no primitive exists. These generalise the `Γ₀(N)` definitions of
  `PeriodIntegral.lean` by the `_gamma0` `rfl` lemmas.

  Transcribed verbatim from `Definitions/Def_ModularCurve_PeriodOf.lean` (pinned
  `aa2d8b3`, 132 lines), the pin's `Period` section. The pin's `CuspForm`
  section of the same file (the Petersson inner product,
  `peterssonIntegrandOf`/`peterssonOf`) is **not** in this module: none of the 28
  consumers of `ModularCurve.exists_hasEquivariantPrimitiveOf` reaches it. The
  leaves' definition wave hosts it, with the pin's `Def_CuspForm_Petersson`, in
  `ModularForms/EichlerShimura/Petersson.lean` (`topics/modularCurve/SET-LEAVESDEF.md`
  LD2) — its `_gamma0` `rfl` lemmas are the leaves' entry point.

  This module also hosts the pin's cross-file prelude (`hasDerivAt_affine`,
  `segmentPoint_eq_of_mem`, `periodAlongOf_eq_sub`, moved here from
  `ModularCurve/Period/PeriodLatticeSpan.lean` where they were first ported) and
  the headline `periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf`.

  The sibling headline `periodMapOf_apply_eq_periodOf` is **not** here, although
  the plan homes it here: its only proof is
  `ModularCurve.exists_hasEquivariantPrimitiveOf`, which lives in
  `EichlerShimura/ExistsEquivariantPrimitive.lean` — a module that imports this
  one, so proving it here would close an import cycle. It is stated in that
  module instead (see its header), with the pin's statement unchanged.

  spec-pin: Theorems/Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul.lean
  spec-pin: P2M/Sol/S_ModularCurve_periodAlongOf_eq_neg_conj_periodAlongOf_J_smul.lean   -- comparable copy
  spec-pin: Definitions/Def_ModularCurve_PeriodOf.lean
-/
import FLTForHuman.ModularForms.EichlerShimura.PeriodPrimitive
import FLTForHuman.ModularForms.EichlerShimura.PeriodIntegral
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

noncomputable section

open UpperHalfPlane Filter Topology

open scoped MatrixGroups ModularForm

namespace ModularCurve

section Period

variable (Γ : Subgroup SL(2, ℤ))

def periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (t : ℝ) : ℂ :=
  f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)

theorem continuous_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    Continuous (periodIntegrandOf Γ τ₀ τ₁ f) :=
  ((f.holo'.continuous).comp (continuous_segmentPath τ₀ τ₁)).mul continuous_const

theorem intervalIntegrable_periodIntegrandOf (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) (a b : ℝ) :
    IntervalIntegrable (periodIntegrandOf Γ τ₀ τ₁ f) MeasureTheory.volume a b :=
  (continuous_periodIntegrandOf Γ τ₀ τ₁ f).intervalIntegrable a b

theorem periodIntegrandOf_add (τ₀ τ₁ : ℍ) (f g : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (f + g) = periodIntegrandOf Γ τ₀ τ₁ f + periodIntegrandOf Γ τ₀ τ₁ g := by
  funext t
  simp [periodIntegrandOf, add_mul]

theorem periodIntegrandOf_smul (τ₀ τ₁ : ℍ) (c : ℂ) (f : CuspForm Γ 2) :
    periodIntegrandOf Γ τ₀ τ₁ (c • f) = fun t => c * periodIntegrandOf Γ τ₀ τ₁ f t := by
  funext t
  simp [periodIntegrandOf, mul_assoc]

def periodAlongOf (τ₀ τ₁ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := ∫ t in (0 : ℝ)..1, periodIntegrandOf Γ τ₀ τ₁ f t
  map_add' f g := by
    rw [periodIntegrandOf_add]
    exact intervalIntegral.integral_add (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1)
      (intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ g 0 1)
  map_smul' c f := by
    rw [periodIntegrandOf_smul, RingHom.id_apply, smul_eq_mul]
    exact intervalIntegral.integral_const_mul c _

theorem periodAlongOf_apply (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    periodAlongOf Γ τ₀ τ₁ f = ∫ t in (0 : ℝ)..1, f (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) :=
  rfl

/-! ### The `J`-conjugation law of the period

`J • τ = -conj τ` sends the geodesic segment `τ₀ → τ₁` to the segment
`J • τ₀ → J • τ₁`, and `periodAlongOf` of a form related by `f ↦ conj (f ∘ J)`
is the negative conjugate.  This is the leaf row
`ModularCurve.periodAlongOf_eq_neg_conj_periodAlongOf_J_smul` (LV-6); its two
helpers are the `S_` copy's `PeriodConj.J_smul_segmentPath`/`periodAlongOf_eq`. -/

private theorem J_smul_segmentPath (τ₀ τ₁ : ℍ) (t : ℝ) :
    UpperHalfPlane.J • segmentPath τ₀ τ₁ t =
      segmentPath (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) t := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_J_smul, ModularCurve.coe_segmentPath, ModularCurve.coe_segmentPath,
    ModularCurve.segmentPoint, ModularCurve.segmentPoint, UpperHalfPlane.coe_J_smul,
    UpperHalfPlane.coe_J_smul]
  simp only [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.neg_re, Complex.neg_im,
    Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im, zero_mul, sub_zero, add_zero]
  constructor <;> ring

private theorem periodAlongOf_eq (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : ℍ, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ))) (τ₀ τ₁ : ℍ) :
    periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) := by
  rw [periodAlongOf_apply, periodAlongOf_apply]
  have hint : ∀ t : ℝ, g (segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀) =
      -(starRingEnd ℂ) (f (segmentPath (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) t) *
        (((UpperHalfPlane.J • τ₁ : ℍ) : ℂ) - ((UpperHalfPlane.J • τ₀ : ℍ) : ℂ))) := by
    intro t
    rw [hg, J_smul_segmentPath, map_mul, UpperHalfPlane.coe_J_smul, UpperHalfPlane.coe_J_smul,
      map_sub, map_neg, map_neg, Complex.conj_conj, Complex.conj_conj]
    ring
  simp_rw [hint]
  rw [intervalIntegral.integral_neg]
  simp only [intervalIntegral, integral_conj, map_sub]

/-- **The `J`-conjugation law.** For cusp forms `f`, `g` of weight `2` with
`g = conj ∘ f ∘ J`, the period of `g` along `τ₀ → τ₁` is minus the conjugate of
the period of `f` along `J • τ₀ → J • τ₁`. -/
theorem periodAlongOf_eq_neg_conj_periodAlongOf_J_smul
    (Γ : Subgroup SL(2, ℤ)) (f g : CuspForm Γ 2)
    (hg : ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)))
    (τ₀ τ₁ : UpperHalfPlane) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ g =
      -(starRingEnd ℂ) (ModularCurve.periodAlongOf Γ (UpperHalfPlane.J • τ₀) (UpperHalfPlane.J • τ₁) f) :=
  periodAlongOf_eq Γ f g hg τ₀ τ₁

def periodOf (γ : Γ) : Module.Dual ℂ (CuspForm Γ 2) :=
  periodAlongOf Γ UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I)

theorem periodOf_apply (γ : Γ) (f : CuspForm Γ 2) :
    periodOf Γ γ f =
      ∫ t in (0 : ℝ)..1, f (segmentPath UpperHalfPlane.I ((γ : SL(2, ℤ)) • UpperHalfPlane.I) t) *
        ((((γ : SL(2, ℤ)) • UpperHalfPlane.I : ℍ) : ℂ) - (UpperHalfPlane.I : ℂ)) :=
  rfl

/-! ### The shared prelude: the fundamental theorem of calculus along a segment

The three lemmas below are the pin's cross-file prelude (`hasDerivAt_affine`,
`segmentPoint_eq_of_mem`, `periodAlongOf_eq_sub`). They are declared **once,
public**, here — the module that defines `periodAlongOf` — rather than in
`ModularCurve/Period/PeriodLatticeSpan.lean`, which also carries them in its
`spec-pin:` wire; that module and `PeriodLatticeBoundary.lean` see them through
the `ExistsEquivariantPrimitive.lean` import chain. -/

theorem hasDerivAt_affine (a b : ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a + (s : ℂ) * b) (b - a) t := by
  have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => (1 - (s : ℂ)) * a) (-(1 : ℂ) * a) t := by
    simpa using ((hasDerivAt_const t (1 : ℂ)).sub h1).mul_const a
  have h3 : HasDerivAt (fun s : ℝ => (s : ℂ) * b) (1 * b) t := h1.mul_const b
  have := h2.add h3
  convert this using 1; first | rfl | ring

theorem segmentPoint_eq_of_mem {τ₀ τ₁ : ℍ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ModularCurve.segmentPoint τ₀ τ₁ t = (1 - (t : ℂ)) * (τ₀ : ℂ) + (t : ℂ) * (τ₁ : ℂ) := by
  simp only [ModularCurve.segmentPoint, ModularCurve.clamp01_of_mem ht, Complex.real_smul,
    Complex.ofReal_sub, Complex.ofReal_one]

theorem periodAlongOf_eq_sub (Γ : Subgroup SL(2, ℤ)) (f : CuspForm Γ 2)
    {F : ℍ → ℂ} (hF : ∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) (τ₀ τ₁ : ℍ) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = F τ₁ - F τ₀ := by
  rw [ModularCurve.periodAlongOf_apply]
  set g : ℝ → ℂ := fun t => F (ModularCurve.segmentPath τ₀ τ₁ t) with hg
  have hgF : ∀ t, g t = (F ∘ ofComplex) (ModularCurve.segmentPoint τ₀ τ₁ t) := by
    intro t
    simp only [hg, Function.comp]
    congr 1
    rw [← ModularCurve.coe_segmentPath, ofComplex_apply]
  have hg0 : g 0 = F τ₀ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 0 = (τ₀ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨le_rfl, zero_le_one⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hg1 : g 1 = F τ₁ := by
    rw [hgF]
    have : ModularCurve.segmentPoint τ₀ τ₁ 1 = (τ₁ : ℂ) := by
      rw [segmentPoint_eq_of_mem ⟨zero_le_one, le_rfl⟩]; push_cast; ring
    simp only [Function.comp, this, ofComplex_apply]
  have hFcont : ∀ τ : ℍ, ContinuousAt (F ∘ ofComplex) (τ : ℂ) := fun τ => (hF τ).continuousAt
  have hgcont : Continuous g := by
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    refine continuous_iff_continuousAt.mpr fun t => ?_
    refine ContinuousAt.comp ?_ (ModularCurve.continuous_segmentPoint τ₀ τ₁).continuousAt
    have := hFcont (ModularCurve.segmentPath τ₀ τ₁ t)
    rwa [ModularCurve.coe_segmentPath] at this
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt g (f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) t := by
    intro t ht
    have hpath : HasDerivAt (ModularCurve.segmentPoint τ₀ τ₁) ((τ₁ : ℂ) - τ₀) t := by
      refine (hasDerivAt_affine (τ₀ : ℂ) (τ₁ : ℂ) t).congr_of_eventuallyEq ?_
      filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
      exact segmentPoint_eq_of_mem (Set.Ioo_subset_Icc_self hs)
    have hFat : HasDerivAt (F ∘ ofComplex) (f (ModularCurve.segmentPath τ₀ τ₁ t))
        (ModularCurve.segmentPoint τ₀ τ₁ t) := by
      have := hF (ModularCurve.segmentPath τ₀ τ₁ t)
      rwa [ModularCurve.coe_segmentPath] at this
    have hcomp := hFat.comp t hpath
    have : g = (F ∘ ofComplex) ∘ ModularCurve.segmentPoint τ₀ τ₁ := funext hgF
    rw [this]
    exact hcomp
  have hint : IntervalIntegrable
      (fun t => f (ModularCurve.segmentPath τ₀ τ₁ t) * ((τ₁ : ℂ) - τ₀)) MeasureTheory.volume 0 1 :=
    ModularCurve.intervalIntegrable_periodIntegrandOf Γ τ₀ τ₁ f 0 1
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one
    hgcont.continuousOn hderiv hint
  rw [key, hg0, hg1]

def periodLatticeOf : Submodule ℤ (Module.Dual ℂ (CuspForm Γ 2)) :=
  Submodule.span ℤ (Set.range (periodOf Γ))

theorem periodOf_mem_periodLatticeOf (γ : Γ) : periodOf Γ γ ∈ periodLatticeOf Γ :=
  Submodule.subset_span (Set.mem_range_self γ)

def HasEquivariantPrimitiveOf (f : CuspForm Γ 2) (F : ℍ → ℂ) : Prop :=
  (∀ τ : ℍ, HasDerivAt (F ∘ ofComplex) (f τ) ↑τ) ∧
    Tendsto F atImInfty (𝓝 0) ∧
    Period.IsEquivariantPrimitive Γ F ∧
    ∀ δ : SL(2, ℤ), ∃ L : ℂ, Tendsto (fun w : ℍ => F (δ • w)) atImInfty (𝓝 L)

open Classical in

def periodMapOf (f : CuspForm Γ 2) : Additive Γ →+ ℂ :=
  if h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F then h.choose_spec.2.2.1.periodHom else 0

theorem periodMapOf_def (f : CuspForm Γ 2) {F : ℍ → ℂ} (hF : HasEquivariantPrimitiveOf Γ f F) :
    ∃ (F₀ : ℍ → ℂ) (h₀ : HasEquivariantPrimitiveOf Γ f F₀), periodMapOf Γ f = h₀.2.2.1.periodHom := by
  classical
  have h : ∃ F : ℍ → ℂ, HasEquivariantPrimitiveOf Γ f F := ⟨F, hF⟩
  exact ⟨h.choose, h.choose_spec, dite_eq_left h⟩

/-- The value of `periodMapOf` on `γ` is `periodOf γ`: the bridge from the period
homomorphism to the period lattice. -/
theorem periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf (Γ : Subgroup SL(2, ℤ))
    (f : CuspForm Γ 2) {F : UpperHalfPlane → ℂ}
    (hF : ModularCurve.HasEquivariantPrimitiveOf Γ f F) (γ : Γ) :
    ModularCurve.periodOf Γ γ f =
      F ((γ : SL(2, ℤ)) • UpperHalfPlane.I) - F UpperHalfPlane.I :=
  periodAlongOf_eq_sub Γ f hF.1 _ _

theorem periodAlongOf_gamma0 (N : ℕ) (τ₀ τ₁ : ℍ) :
    periodAlongOf (CongruenceSubgroup.Gamma0 N) τ₀ τ₁ = periodAlong N τ₀ τ₁ := rfl

theorem periodOf_gamma0 (N : ℕ) (γ : CongruenceSubgroup.Gamma0 N) :
    periodOf (CongruenceSubgroup.Gamma0 N) γ = period N γ := rfl

theorem periodLatticeOf_gamma0 (N : ℕ) :
    periodLatticeOf (CongruenceSubgroup.Gamma0 N) = periodLattice N := rfl

theorem hasEquivariantPrimitiveOf_gamma0_iff (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2)
    (F : ℍ → ℂ) : HasEquivariantPrimitiveOf (CongruenceSubgroup.Gamma0 N) f F ↔
      HasEquivariantPrimitive N f F := Iff.rfl

theorem periodMapOf_gamma0 (N : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    periodMapOf (CongruenceSubgroup.Gamma0 N) f = periodMap N f := rfl

end Period

end ModularCurve

end
