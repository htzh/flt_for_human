/-
  The periods of `S₂(Γ)` span the whole dual: the period pairing is non-degenerate.

  For a finite-index `Γ ≤ SL(2, ℤ)`, the `ℂ`-span of the periods
  `periodAlongOf Γ τ₀ τ₁` over all pairs `(τ₀, τ₁) ∈ ℍ × ℍ` is the whole
  `AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))`. The proof integrates each cusp
  form to an equivariant primitive (`exists_hasEquivariantPrimitiveOf`), writes
  the period as a difference of two evaluations of that primitive
  (`periodAlongOf_eq_sub`), and then shows that the image of the period span
  under a dual-frame map `T` has non-empty interior in the finite-dimensional
  space `κ → ℂ`: the map `z ↦ ∑ k, periodAlongOf Γ I (z k)` is a local
  homeomorphism at the frame's points (`hasStrictFDerivAt_pi'` +
  `map_nhds_eq_of_equiv`), so the interior of the image contains `G z₀`. A clopen
  argument (`addSubgroup_eq_top_of_nonempty_interior`) then forces the image to
  be everything, and injectivity of `T` pulls the conclusion back.

  Transcribed from
  `P2M/Sol/S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.lean`
  (pinned `aa2d8b3`, 263 lines); the statement is the `Theorems/` wrapper's. All
  of the pin's internal machinery (`ev`, `prim`, the frame `exists_frame`, the
  span argument) is `private` here, so the statement checker diffs only the
  headline and the three shared prelude declarations at the top.

  The pin's `hasDerivAt_affine`, `segmentPoint_eq_of_mem` and
  `periodAlongOf_eq_sub` are declared **once, public**, here, because
  `PeriodLatticeBoundary.lean` (order 2 of the same set) reuses all three
  verbatim; everything else in the pin's file stays `private`. This is the same
  convention as `WeierstrassCurve/Automorphism/Basic.lean` (WORKORDER-W1): a
  cross-module shared prelude is written once, public, at the pin's names.

  References (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.lean>,
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_addSubgroupClosure_range_periodAlongOf_eq_top.lean>
-/
import FLTForHuman.ModularForms.EichlerShimura.ExistsEquivariantPrimitive
import FLTForHuman.ModularForms.WeightOne.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Connected.Clopen

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls in `span_range_ev`/`exists_frame` are
-- load-bearing (they register `FiniteDimensional`/`Fintype` for instance
-- search), so they stay literal.
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups

open UpperHalfPlane

namespace ModularCurve

/-! ### The shared prelude (orders 1 and 2 of the set) -/

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

namespace JacobiInversionEngineOf

private theorem addSubgroup_eq_top_of_nonempty_interior
    {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [ConnectedSpace G] (H : AddSubgroup G)
    (hne : (interior (H : Set G)).Nonempty) :
    H = ⊤ := by
  obtain ⟨a, ha⟩ := hne
  have hopen : IsOpen (H : Set G) :=
    H.isOpen_of_mem_nhds (mem_interior_iff_mem_nhds.mp ha)
  have hclosed : IsClosed (H : Set G) := H.isClosed_of_isOpen hopen
  have huniv : (H : Set G) = Set.univ :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩ ⟨0, H.zero_mem⟩
  exact SetLike.coe_injective (huniv.trans (AddSubgroup.coe_top).symm)

section Prim

variable (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]

private noncomputable def prim (f : CuspForm Γ 2) : ℍ → ℂ :=
  (ModularCurve.exists_hasEquivariantPrimitiveOf Γ f).choose

private theorem hasDerivAt_prim (f : CuspForm Γ 2) (τ : ℍ) :
    HasDerivAt (prim Γ f ∘ ofComplex) (f τ) (τ : ℂ) :=
  (ModularCurve.exists_hasEquivariantPrimitiveOf Γ f).choose_spec.1 τ

private theorem periodAlongOf_eq_prim_sub (τ₀ τ₁ : ℍ) (f : CuspForm Γ 2) :
    ModularCurve.periodAlongOf Γ τ₀ τ₁ f = prim Γ f τ₁ - prim Γ f τ₀ :=
  periodAlongOf_eq_sub Γ f (hasDerivAt_prim Γ f) τ₀ τ₁

private theorem hasStrictDerivAt_prim (f : CuspForm Γ 2) (τ : ℍ) :
    HasStrictDerivAt (prim Γ f ∘ ofComplex) (f τ) (τ : ℂ) := by
  have hd : DifferentiableOn ℂ (prim Γ f ∘ ofComplex) {z : ℂ | 0 < z.im} := fun z hz =>
    (hasDerivAt_prim Γ f ⟨z, hz⟩).differentiableAt.differentiableWithinAt
  have han : AnalyticAt ℂ (prim Γ f ∘ ofComplex) (τ : ℂ) :=
    hd.analyticAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds τ.im_pos)
  have h := han.hasStrictDerivAt
  rwa [(hasDerivAt_prim Γ f τ).deriv] at h

end Prim

section Frame

variable (Γ : Subgroup SL(2, ℤ))

private noncomputable def ev (τ : ℍ) : Module.Dual ℂ (CuspForm Γ 2) where
  toFun f := f τ
  map_add' f g := by simp
  map_smul' c f := by simp

private theorem ev_apply (τ : ℍ) (f : CuspForm Γ 2) :
    ev Γ τ f = f τ := rfl

attribute [local simp] ev_apply

variable [Γ.FiniteIndex]

private theorem finiteDimensional : FiniteDimensional ℂ (CuspForm Γ 2) :=
  CuspForm.finiteDimensional_of_isArithmetic (Γ : Subgroup (GL (Fin 2) ℝ)) 2

private theorem span_range_ev : Submodule.span ℂ (Set.range (ev Γ)) = ⊤ := by
  haveI := finiteDimensional Γ
  apply Submodule.span_eq_top_of_ne_zero
  intro f hf
  by_contra! h
  apply hf
  exact CuspForm.ext fun τ => by simpa using h (ev Γ τ) ⟨τ, rfl⟩

private theorem exists_frame :
    ∃ (κ : Type) (_ : Fintype κ) (pt : κ → ℍ)
      (vec : κ → CuspForm Γ 2),
      (∀ j, vec j (pt j) = 1) ∧
      (∀ j k, k ≠ j → vec j (pt k) = 0) ∧
      ∀ φ : Module.Dual ℂ (CuspForm Γ 2),
        (∀ j, φ (vec j) = 0) → φ = 0 := by
  classical
  haveI := finiteDimensional Γ
  obtain ⟨κ, a, -, hspan, hli⟩ := exists_linearIndependent' ℂ (ev Γ)
  rw [span_range_ev] at hspan
  haveI : Finite κ := hli.finite
  letI : Fintype κ := Fintype.ofFinite κ
  let β : Module.Basis κ ℂ (Module.Dual ℂ (CuspForm Γ 2)) :=
    Module.Basis.mk hli (by rw [hspan])
  have hβ : ∀ k, β k = ev Γ (a k) := fun k => by simp [β]
  let e := Module.evalEquiv ℂ (CuspForm Γ 2)
  let vec : κ → CuspForm Γ 2 := fun j => e.symm (β.dualBasis j)
  have hvec : ∀ j k, (vec j) (a k) = if k = j then 1 else 0 := by
    intro j k
    have h1 : (vec j) (a k) = β k (vec j) := by rw [hβ]; rfl
    rw [h1]
    simp only [vec, e, Module.apply_evalEquiv_symm_apply, Module.Basis.dualBasis_apply_self]
  refine ⟨κ, inferInstance, a, vec, fun j => by simp [hvec], fun j k hkj => by simp [hvec, hkj], ?_⟩
  intro φ hφ
  let bV : Module.Basis κ ℂ (CuspForm Γ 2) := β.dualBasis.map e.symm
  have hbV : ∀ j, bV j = vec j := fun j => by simp [bV, vec]
  exact bV.ext fun j => by rw [hbV j, hφ j, LinearMap.zero_apply]

end Frame

private theorem main (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) := by
  classical
  obtain ⟨κ, _, pt, vec, hδ1, hδ0, hext⟩ := exists_frame Γ
  set H := AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) with hH

  let T : Module.Dual ℂ (CuspForm Γ 2) →+ (κ → ℂ) :=
    { toFun := fun φ j => φ (vec j)
      map_zero' := by ext; simp
      map_add' := by intros; ext; simp }
  have hT : ∀ φ j, T φ j = φ (vec j) := fun _ _ => rfl
  have hTinj : Function.Injective T := by
    intro φ ψ h
    have h0 : ∀ j, (φ - ψ) (vec j) = 0 := fun j => by
      have := congr_fun h j
      rw [hT, hT] at this
      rw [LinearMap.sub_apply, this, sub_self]
    exact sub_eq_zero.mp (hext _ h0)

  let G : (κ → ℂ) → (κ → ℂ) := fun z => T (∑ k, ModularCurve.periodAlongOf Γ I (ofComplex (z k)))
  have hGmem : ∀ z, G z ∈ H.map T := fun z =>
    AddSubgroup.mem_map.mpr ⟨_, AddSubgroup.sum_mem _ (fun k _ =>
      AddSubgroup.subset_closure ⟨(I, ofComplex (z k)), rfl⟩), rfl⟩
  have hGj : ∀ z j, G z j = ∑ k, ((prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I) := by
    intro z j
    change (∑ k, ModularCurve.periodAlongOf Γ I (ofComplex (z k))) (vec j) = _
    rw [LinearMap.coe_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [periodAlongOf_eq_prim_sub]
    rfl
  set z₀ : κ → ℂ := fun k => ((pt k : ℍ) : ℂ) with hz₀

  have hG : HasStrictFDerivAt G (ContinuousLinearMap.id ℂ (κ → ℂ)) z₀ := by
    rw [hasStrictFDerivAt_pi']
    intro j
    have hfun : (fun z => G z j) =
        fun z => ∑ k, ((prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I) :=
      funext fun z => hGj z j
    rw [hfun]
    have hk : ∀ k ∈ (Finset.univ : Finset κ), HasStrictFDerivAt
        (fun z : κ → ℂ => (prim Γ (vec j) ∘ ofComplex) (z k) - prim Γ (vec j) I)
        ((ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ).smulRight ((vec j) (pt k))) z₀ := by
      intro k _
      have h1 : HasStrictDerivAt (prim Γ (vec j) ∘ ofComplex) ((vec j) (pt k)) (z₀ k) :=
        hasStrictDerivAt_prim Γ (vec j) (pt k)
      have h2 : HasStrictFDerivAt (fun z : κ → ℂ => z k)
          (ContinuousLinearMap.proj k : (κ → ℂ) →L[ℂ] ℂ) z₀ :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : κ => ℂ) k).hasStrictFDerivAt
      have h3 := (h1.hasStrictFDerivAt.comp z₀ h2).sub_const (prim Γ (vec j) I)
      convert h3 using 1; try rfl
    have hsum := HasStrictFDerivAt.fun_sum hk
    convert hsum using 1; try rfl
    refine ContinuousLinearMap.ext fun w => ?_
    rw [sum_apply, Finset.sum_eq_single j]
    · simp [hδ1]
    · intro k _ hkj
      simp [hδ0 j k hkj]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hnhds : Filter.map G (nhds z₀) = nhds (G z₀) :=
    hG.map_nhds_eq_of_equiv (f' := ContinuousLinearEquiv.refl ℂ (κ → ℂ))
  have hint : (interior ((H.map T : AddSubgroup (κ → ℂ)) : Set (κ → ℂ))).Nonempty := by
    refine ⟨G z₀, interior_mono (Set.range_subset_iff.mpr hGmem) ?_⟩
    rw [mem_interior_iff_mem_nhds, ← hnhds]
    exact Filter.range_mem_map
  have htop : H.map T = ⊤ := addSubgroup_eq_top_of_nonempty_interior _ hint
  rw [eq_top_iff]
  intro φ _
  have hφ : T φ ∈ H.map T := htop ▸ AddSubgroup.mem_top _
  obtain ⟨ψ, hψ, hψφ⟩ := AddSubgroup.mem_map.mp hφ
  exact hTinj hψφ ▸ hψ

end JacobiInversionEngineOf

/-- **Non-degeneracy of the period pairing.** For a finite-index `Γ ≤ SL(2, ℤ)`,
the periods of `S₂(Γ)` span the whole dual of the space of cusp forms. The pin's
`ModularCurve.addSubgroupClosure_range_periodAlongOf_eq_top`, with the statement
of the `Theorems/` wrapper. -/
theorem addSubgroupClosure_range_periodAlongOf_eq_top
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] :
    AddSubgroup.closure
        (Set.range fun p : UpperHalfPlane × UpperHalfPlane =>
          ModularCurve.periodAlongOf Γ p.1 p.2) =
      (⊤ : AddSubgroup (Module.Dual ℂ (CuspForm Γ 2))) :=
  JacobiInversionEngineOf.main Γ

end ModularCurve

end
