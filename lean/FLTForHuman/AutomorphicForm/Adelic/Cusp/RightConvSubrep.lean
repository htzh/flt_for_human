/-
  Right convolution by a factorisable test function keeps a right translate of a
  cuspidal-subrepresentation vector inside the subrepresentation.

  `IsCuspSubrep F pins ξ V` is a subrepresentation of the space of functions on
  `GL₂(𝔸_K)` that contains only cusp forms, is closed under right convolution by
  factorisable test functions, and lies in `cuspKFiniteSubmodule F pins ξ`. The
  statement here is the `RepTheory` ↔ `Cusp` bridge: for `φ ∈ V`, `h ∈ GL₂(𝔸_K)`
  and a factorisable test function `f` that is archimedean-bi-finite for the type
  family `tys`, the convolution `rightConv F (rightTranslate F h φ) f` is again in
  `V`.

  The proof moves the translate onto the test function,
  `rightConv (rightTranslate h φ) f = rightConv φ (f · h⁻¹)`, then produces a
  kernel `e` on the archimedean row-isometry product `Kprod F` that reproduces
  both `φ` and the translated convolution on an archimedean cut containing both
  (`archCutSubmodule F (archTypeFamilyJoin tφ tys)`), so that
  `rightConv φ (f · h⁻¹)` is the double convolution of `f` with that kernel.
  Membership then follows from `IsCuspSubrep.rightConv_mem`, and the two
  convolutions are identified by the `dconvWith` limit along an approximate
  identity.

  All helpers are `private`; the public declaration is the `Theorems/` wrapper's
  statement, in `namespace AutomorphicForm`.

  spec-pin: Theorems/Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CutWeightDecomposition
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.RepTheory.ConvolutionLimit

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Topology Filter
open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open ArchApproxIdentity
-- the pin's `p2m_open`/`p2m_reactivate` for `KAvArch` (the port's `ArchInfra`): the
-- compactness and Haar-measure instances on `Kprod` are scoped there.
open scoped ArchInfra

namespace AutomorphicForm

/-! ### The join of two archimedean type families

The archimedean cut `archCutSubmodule F tys` is the intersection over the places of
the sup of the type submodules of `tys`. Two of them are compared only through a
*common* family, so the join — cardinals added, representations appended placewise —
is the smallest family containing both. -/

section JoinOfFamilies

variable (F : Type) [Field F]

private def archTypeFamilyJoin (t₁ t₂ : ArchTypeFamily F) : ArchTypeFamily F where
  card := fun w => t₁.card w + t₂.card w
  rep := fun w => Fin.append (t₁.rep w) (t₂.rep w)

private theorem isContainedIn_archTypeFamilyJoin_left (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₁ (archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.castAdd (t₂.card w) i, Fin.append_left (t₁.rep w) (t₂.rep w) i⟩

private theorem isContainedIn_archTypeFamilyJoin_right (t₁ t₂ : ArchTypeFamily F) :
    ArchTypeFamily.IsContainedIn F t₂ (archTypeFamilyJoin F t₁ t₂) :=
  fun w i => ⟨Fin.natAdd (t₁.card w) i, Fin.append_right (t₁.rep w) (t₂.rep w) i⟩

end JoinOfFamilies

/-! ### One archimedean type family for a `K`-finite cusp form -/

noncomputable section OneFamily

variable (F : Type) [Field F] [NumberField F]

private theorem exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule (pins : CarrierPins F)
    (ξ : pins.Z →* ℂˣ) {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) :
    ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys := by
  refine Submodule.span_induction
    (p := fun φ _ => ∃ tys : ArchTypeFamily F, φ ∈ archCutSubmodule F tys) ?_ ?_ ?_ ?_ hφ
  · rintro ψ ⟨-, -, tys, htys⟩
    exact ⟨tys, htys⟩
  · exact ⟨⟨fun _ => 0, fun _ i => Fin.elim0 i⟩, (archCutSubmodule F _).zero_mem⟩
  · rintro u v _ _ ⟨t₁, h₁⟩ ⟨t₂, h₂⟩
    exact ⟨archTypeFamilyJoin F t₁ t₂,
      (archCutSubmodule F _).add_mem
        (archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_left F t₁ t₂) h₁)
        (archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_right F t₁ t₂) h₂)⟩
  · rintro c u _ ⟨t, ht⟩
    exact ⟨t, (archCutSubmodule F t).smul_mem c ht⟩

end OneFamily

/-! ### Convolution by a factorisable test function stays in an archimedean cut -/

noncomputable section Types

open MeasureTheory

variable (F : Type) [Field F] [NumberField F]

private theorem rightConv_mem_archCutSubmodule {tys : ArchTypeFamily F} {f : AdelicGL2 (𝓞 F) F → ℂ}
    (hfact : IsFactorizableTestFn F f) (hleft : (fun x => f x⁻¹) ∈ archCutSubmodule F tys)
    {u : AdelicGL2 (𝓞 F) F → ℂ} (hu : Continuous u) : rightConv F u f ∈ archCutSubmodule F tys := by
  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hfact
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hdom : (fun x => f x⁻¹) ∈ convDomain (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) u := by
    rw [mem_convDomain_iff]
    intro y
    simp only [inv_inv]
    exact ((hu.comp (continuous_const.mul continuous_id)).mul hfc).integrable_of_hasCompactSupport
      hfs.mul_left
  have hconv : convOpOn (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) u ⟨fun x => f x⁻¹, hdom⟩
      = rightConv F u f := by
    funext y
    rw [convOpOn_apply]
    show (∫ x, u (y * x) * (fun x => f x⁻¹) x⁻¹ ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
      ∫ x, u (y * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    simp only [inv_inv]
  rw [mem_archCutSubmodule_iff]
  intro w
  rw [← hconv]
  exact convOpOn_mem_iSup_typeSubmodule _ u (ArchEntryBall.forall_rowIsometryInclAt₀_injective F w)
    (fun i => (tys.rep w i).ρ) _ ((mem_archCutSubmodule_iff F tys _).mp hleft w)

private theorem rightConv_rightTranslate_eq (F : Type) [Field F] [NumberField F] (φ f : AdelicGL2 (𝓞 F) F → ℂ)
    (h : AdelicGL2 (𝓞 F) F) :
    rightConv F (rightTranslate F h φ) f = rightConv F φ (fun x => f (x * h⁻¹)) := by
  funext g
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  have key := integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (fun x => φ (g * x) * f (x * h⁻¹)) h
  simp only [rightConv_apply, rightTranslate_apply]
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using key

end Types

/-! ### A `C^∞` reparametrisation of the double convolution -/

noncomputable section Kernel

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

private theorem exists_contDiff_dconvWith [MeasurableSpace (ArchInfra.Kprod L)] [BorelSpace (ArchInfra.Kprod L)]
    [SecondCountableTopology (ArchInfra.Kprod L)] (μ : Measure (ArchInfra.Kprod L)) [IsFiniteMeasure μ]
    {e : ArchInfra.Kprod L → ℂ} (he : Continuous e) {β : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    (hβt : IsArchTestFactor L β) :
    ∃ Φ : ArchEntryBall.EntrySpace L → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, dconvWith μ (ArchInfra.inclArch L) e e β y = Φ (archEntries L y) := by
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hβt
  let a := ArchInfra.inclArch L
  have ha : Continuous a := ArchInfra.continuous_inclArch (F := L)
  let Φf : ArchInfra.Kprod L × ArchInfra.Kprod L → ArchEntryBall.EntrySpace L →L[ℝ] ArchEntryBall.EntrySpace L :=
    fun p =>
      LinearMap.toContinuousLinearMap (twoSided L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
        ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_twoSided_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : ArchInfra.Kprod L × ArchInfra.Kprod L => e p.1 * e p.2 :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e p.1 * e p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e p.1 * e p.2 * β ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e p.1 * e p.2 * β ((a p.1)⁻¹ * y * (a p.2)⁻¹) = e p.1 * e p.2 * Φψ (Φf p (archEntries L y))
    rw [hψΦ ((a p.1)⁻¹ * y * (a p.2)⁻¹), archEntries_mul_mul]
    rfl

variable {L}

private theorem isArchTestFactor_mul_right {fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ}
    (hfa : IsArchTestFactor L fa) (k : GL (Fin 2) (InfiniteAdeleRing L)) :
    IsArchTestFactor L fun y => fa (y * k) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (LinearMap.toContinuousLinearMap (twoSided L
      ((1 : GL (Fin 2) (InfiniteAdeleRing L)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
      (k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))) X),
    hΦ.comp (ContinuousLinearMap.contDiff _), fun y => ?_⟩,
    show HasCompactSupport fun y => fa (y * k) from hsupp.comp_homeomorph (Homeomorph.mulRight k)⟩
  beta_reduce
  rw [hfaΦ, show y * k = 1 * y * k from by rw [one_mul], archEntries_mul_mul]
  rfl

private theorem isFinTestFactor_mul_right {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ}
    (hff : IsFinTestFactor L ff) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L)) :
    IsFinTestFactor L fun z => ff (z * k) :=
  ⟨(hff.1).comp_continuous (continuous_mul_const k),
    show HasCompactSupport fun z => ff (z * k) from hff.2.comp_homeomorph (Homeomorph.mulRight k)⟩

private theorem exists_factors_mul_right {f : AdelicGL2 (𝓞 L) L → ℂ} (hf : IsFactorizableTestFn L f)
    (k : AdelicGL2 (𝓞 L) L) :
    ∃ (fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ) (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ),
      IsArchTestFactor L fa ∧ IsFinTestFactor L ff ∧
        ∀ x, f (x * k) = fa (AdelicLevel.glArch (𝓞 L) L x) * ff (AdelicLevel.glFin (𝓞 L) L x) := by
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  refine ⟨fun y => fa (y * AdelicLevel.glArch (𝓞 L) L k), fun z => ff (z * AdelicLevel.glFin (𝓞 L) L k),
    isArchTestFactor_mul_right hfa _, isFinTestFactor_mul_right hff _, fun x => ?_⟩
  show f (x * k) = fa (AdelicLevel.glArch (𝓞 L) L x * AdelicLevel.glArch (𝓞 L) L k) *
    ff (AdelicLevel.glFin (𝓞 L) L x * AdelicLevel.glFin (𝓞 L) L k)
  rw [hfeq, map_mul, map_mul]

private theorem dconvWith_tensor [MeasurableSpace (ArchInfra.Kprod L)] (μ : Measure (ArchInfra.Kprod L))
    (e : ArchInfra.Kprod L → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing L) → ℂ)
    (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) {f : AdelicGL2 (𝓞 L) L → ℂ}
    (hfeq : ∀ g, f g = fa (AdelicLevel.glArch (𝓞 L) L g) * ff (AdelicLevel.glFin (𝓞 L) L g))
    (g : AdelicGL2 (𝓞 L) L) :
    dconvWith μ (ArchInfra.inclAdelic L) e e f g =
      dconvWith μ (ArchInfra.inclArch L) e e fa (AdelicLevel.glArch (𝓞 L) L g) *
        ff (AdelicLevel.glFin (𝓞 L) L g) := by
  show (∫ p : ArchInfra.Kprod L × ArchInfra.Kprod L, e p.1 * e p.2 *
      f ((ArchInfra.inclAdelic L p.1)⁻¹ * g * (ArchInfra.inclAdelic L p.2)⁻¹) ∂(μ.prod μ)) =
    (∫ p : ArchInfra.Kprod L × ArchInfra.Kprod L, e p.1 * e p.2 *
      fa ((ArchInfra.inclArch L p.1)⁻¹ * AdelicLevel.glArch (𝓞 L) L g *
        (ArchInfra.inclArch L p.2)⁻¹) ∂(μ.prod μ)) *
        ff (AdelicLevel.glFin (𝓞 L) L g)
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  have h1 : AdelicLevel.glArch (𝓞 L) L ((ArchInfra.inclAdelic L p.1)⁻¹ * g * (ArchInfra.inclAdelic L p.2)⁻¹) =
      (ArchInfra.inclArch L p.1)⁻¹ * AdelicLevel.glArch (𝓞 L) L g * (ArchInfra.inclArch L p.2)⁻¹ := by
    rw [map_mul, map_mul, map_inv, map_inv,
      show ArchInfra.inclAdelic L p.1 = adelicArchGLIncl L (ArchInfra.inclArch L p.1) from rfl,
      show ArchInfra.inclAdelic L p.2 = adelicArchGLIncl L (ArchInfra.inclArch L p.2) from rfl,
      glArch_adelicArchGLIncl, glArch_adelicArchGLIncl]
  have h2 : AdelicLevel.glFin (𝓞 L) L ((ArchInfra.inclAdelic L p.1)⁻¹ * g * (ArchInfra.inclAdelic L p.2)⁻¹) =
      AdelicLevel.glFin (𝓞 L) L g := by
    rw [map_mul, map_mul, map_inv, map_inv,
      show ArchInfra.inclAdelic L p.1 = adelicArchGLIncl L (ArchInfra.inclArch L p.1) from rfl,
      show ArchInfra.inclAdelic L p.2 = adelicArchGLIncl L (ArchInfra.inclArch L p.2) from rfl,
      glFin_adelicArchGLIncl, glFin_adelicArchGLIncl, inv_one, one_mul, mul_one]
  show e p.1 * e p.2 * f _ = e p.1 * e p.2 * fa _ * ff _
  rw [hfeq, h1, h2]
  ring

end Kernel

/-! ### The reproducing kernel on the archimedean row-isometry product

`exists_reproducer` produces a coefficient function `c` whose matrix coefficients reproduce
every vector of a finite-dimensional archimedean-stable space `E'`; the kernel
`e κ = ∑ q, c q * Pm κ⁻¹ q.2 q.1` is the one the double convolution is taken against. -/

noncomputable section Reproducer

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

private theorem exists_convKernel (tys : ArchTypeFamily L) (φ ψ : AdelicGL2 (𝓞 L) L → ℂ)
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : φ ∈ archCutSubmodule L tys) (hψ : ψ ∈ archCutSubmodule L tys) :
    ∃ e : ArchInfra.Kprod L → ℂ, Continuous e ∧
      (∀ x, ∫ κ, e κ * φ (x * ArchInfra.inclAdelic L κ) ∂(ArchInfra.muK L) = φ x) ∧
      (∀ x, ∫ κ, e κ * ψ (x * ArchInfra.inclAdelic L κ) ∂(ArchInfra.muK L) = ψ x) ∧
      ∀ β : GL (Fin 2) (InfiniteAdeleRing L) → ℂ, Continuous β →
        letI : MeasurableSpace (ArchInfra.Kprod L) := borel _
        IsArchFactorBiFinite L tys (dconvWith (ArchInfra.muK L) (ArchInfra.inclArch L) e e β) := by
  classical

  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing L)) := borelSpace_glBorelOf (InfiniteAdeleRing L)
  haveI : (archHaarK L).IsHaarMeasure := isHaarMeasure_archHaarK L
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing L)) :=
    ArchInfraTopology.locallyCompactSpace_archGL L
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing L)) :=
    ArchInfraTopology.secondCountableTopology_archGL L
  haveI : SigmaFinite (archHaarK L) := ArchInfraTopology.sigmaFinite_archHaarK L

  letI : MeasurableSpace (ArchInfra.Kprod L) := borel _
  haveI : BorelSpace (ArchInfra.Kprod L) := ⟨rfl⟩
  haveI : SecondCountableTopology (ArchInfra.Kprod L) :=
    ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ L
  haveI : (ArchInfra.muK L).IsMulRightInvariant := ArchInfra.isMulRightInvariant_muK L

  have hcomm : ∀ (w w' : InfinitePlace L), w ≠ w' → ∀ (k : ArchInfra.Kw L w) (k' : ArchInfra.Kw L w'),
      rowIsometryInclAt₀ L w k * rowIsometryInclAt₀ L w' k' =
        rowIsometryInclAt₀ L w' k' * rowIsometryInclAt₀ L w k := by
    intro w w' hww' k k'
    show adelicArchGLIncl L (archRowIsometryInclAt₀ L w k) * adelicArchGLIncl L (archRowIsometryInclAt₀ L w' k') =
      adelicArchGLIncl L (archRowIsometryInclAt₀ L w' k') * adelicArchGLIncl L (archRowIsometryInclAt₀ L w k)
    rw [← map_mul, ← map_mul, (ArchInfra.commute_archRowIsometryInclAt₀ L hww' k k').eq]
  have harchφ : ∀ w, φ ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    (mem_archCutSubmodule_iff L tys φ).mp hφ
  have harchψ : ∀ w, ψ ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    (mem_archCutSubmodule_iff L tys ψ).mp hψ
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ({φ, ψ} : Set (AdelicGL2 (𝓞 L) L → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ ((Set.finite_singleton ψ).insert φ)
  have hV : ∀ w, Submodule.span ℂ ({φ, ψ} : Set (AdelicGL2 (𝓞 L) L → ℂ)) ≤
      ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    fun w => Submodule.span_le.mpr
      (Set.insert_subset_iff.mpr ⟨harchφ w, Set.singleton_subset_iff.mpr (harchψ w)⟩)
  obtain ⟨E, hEfd, hfE, hEcut, hEst⟩ := exists_finiteDimensional_stable (K := fun w => ArchInfra.Kw L w)
    (fun w => rowIsometryInclAt₀ L w) hcomm (fun w i => (tys.rep w i).ρ) _ hV
  let E' : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := E ⊓ contSubmodule (AdelicGL2 (𝓞 L) L)
  haveI : FiniteDimensional ℂ E' := Submodule.finiteDimensional_of_le inf_le_left
  have hφE' : φ ∈ E' := ⟨hfE (Submodule.subset_span (Set.mem_insert φ _)), hφc⟩
  have hψE' : ψ ∈ E' := ⟨hfE (Submodule.subset_span (Set.mem_insert_of_mem φ (Set.mem_singleton ψ))), hψc⟩
  have hE'cut : ∀ w, ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    fun w v hv => hEcut w hv.1
  have hE'st : ∀ (w : InfinitePlace L) (k : ArchInfra.Kw L w), ∀ v ∈ E',
      (fun x => v (x * rowIsometryInclAt₀ L w k)) ∈ E' :=
    fun w k v hv =>
      ⟨hEst w k v hv.1, (show Continuous v from hv.2).comp (continuous_id.mul continuous_const)⟩

  have hc' : Pairwise fun w w' => ∀ (k : ArchInfra.Kw L w) (k' : ArchInfra.Kw L w'),
      Commute (rowIsometryInclAt₀ L w k) (rowIsometryInclAt₀ L w' k') :=
    fun w w' hww' k k' => hcomm w w' hww' k k'
  have hhom : ArchInfra.inclAdelic L = MonoidHom.noncommPiCoprod (fun w => rowIsometryInclAt₀ L w) hc' := by
    refine MonoidHom.pi_ext fun w k => ?_
    rw [ArchInfra.inclAdelic_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
  have hE'K : ∀ κ : ArchInfra.Kprod L, ∀ v ∈ E', (fun x => v (x * ArchInfra.inclAdelic L κ)) ∈ E' := by
    intro κ
    rw [hhom]
    exact rt_noncommPiCoprod_mem (fun w => rowIsometryInclAt₀ L w) hc' hE'st κ
  have hcontE' : ∀ v ∈ E', ∀ x : AdelicGL2 (𝓞 L) L, Continuous fun κ : ArchInfra.Kprod L =>
      v (x * ArchInfra.inclAdelic L κ) :=
    fun v hv x =>
      (show Continuous v from hv.2).comp (continuous_const.mul (ArchInfra.continuous_inclAdelic (F := L)))

  obtain ⟨c, hc⟩ := exists_reproducer (ArchInfra.muK L) (ArchInfra.inclAdelic L) E' hE'K hcontE'
  obtain ⟨e, he_def⟩ : ∃ e : ArchInfra.Kprod L → ℂ,
      ∀ κ, e κ = ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 :=
    ⟨_, fun _ => rfl⟩
  have he : Continuous e := by
    rw [show e = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 from funext he_def]
    exact continuous_finsetSum _ fun q _ => continuous_const.mul
      (continuous_apply_apply_of_continuous (continuous_Pm_inv (ArchInfra.inclAdelic L) E' hE'K hcontE') _ _)
  have hrep : ∀ v ∈ E', ∀ x : AdelicGL2 (𝓞 L) L,
      ∫ κ, e κ * v (x * ArchInfra.inclAdelic L κ) ∂(ArchInfra.muK L) = v x := by
    intro v hv x
    calc (∫ κ, e κ * v (x * ArchInfra.inclAdelic L κ) ∂(ArchInfra.muK L))
        = ∫ κ, (∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1) *
            v (x * ArchInfra.inclAdelic L κ) ∂(ArchInfra.muK L) :=
          integral_congr_ae (Filter.Eventually.of_forall fun κ => by beta_reduce; rw [he_def])
      _ = v x := hc v hv x
  have hed : ∀ w : InfinitePlace L, ∀ (hinj : Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
      (hcut : ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
        ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
        (tys.rep w i).ρ),
      e ∈ ⨆ i, typeSubmodule (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) (tys.rep w i).ρ.dual := by
    intro w hinj hcut
    rw [show e = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 from funext he_def]
    exact reproducer_mem_iSup_dual (ArchInfra.inclAdelic L) E' hE'K hinj (fun i => (tys.rep w i).ρ) hcut c
  have hel : ∀ w : InfinitePlace L, ∀ (hinj : Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
      (hcut : ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
        ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
        (tys.rep w i).ρ),
      (fun κ => e κ⁻¹) ∈ ⨆ i, typeSubmodule (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w)
        (tys.rep w i).ρ := by
    intro w hinj hcut
    rw [show (fun κ => e κ⁻¹) = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ q.2 q.1 from
      funext fun κ => by rw [he_def, inv_inv]]
    exact reproducer_inv_mem_iSup (ArchInfra.inclAdelic L) E' hE'K hinj (fun i => (tys.rep w i).ρ) hcut c
  have ha : Continuous (ArchInfra.inclArch L) := ArchInfra.continuous_inclArch (F := L)

  have hjcut : ∀ w : InfinitePlace L, ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
      ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
      (tys.rep w i).ρ := by
    intro w
    have hj : (ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) =
        rowIsometryInclAt₀ L w :=
      MonoidHom.ext fun k => ArchInfra.inclAdelic_mulSingle w k
    rw [hj]
    exact hE'cut w
  have hjinj : ∀ w : InfinitePlace L, Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) :=
    fun w => Pi.mulSingle_injective (M := fun w' => ArchInfra.Kw L w') w
  have haj : ∀ (w : InfinitePlace L) (k : ArchInfra.Kw L w),
      ArchInfra.inclArch L (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w k) = archRowIsometryInclAt₀ L w k :=
    fun w k => ArchInfra.inclArch_mulSingle w k
  refine ⟨e, he, hrep φ hφE', hrep ψ hψE', fun β hβ => ⟨?_, ?_⟩⟩
  · refine (Submodule.mem_iInf _).mpr fun w => ?_
    exact dconvWith_inv_mem_iSup (ArchEntryBall.archRowIsometryInclAt₀_injective L w) (haj w)
      (fun i => (tys.rep w i).ρ) he hβ ha (hel w (hjinj w) (hjcut w))
  · refine (Submodule.mem_iInf _).mpr fun w => ?_
    exact dconvWith_mem_iSup_dual (ArchEntryBall.archRowIsometryInclAt₀_injective L w) (haj w)
      (fun i => (tys.rep w i).ρ) he hβ ha (hed w (hjinj w) (hjcut w))

end Reproducer

/-! ### The row -/

section Main

theorem rightConv_rightTranslate_mem_of_isCuspSubrep
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (tys : AutomorphicForm.ArchTypeFamily F)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F pins ξ V)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ V)
    (h : AdelicGL2 (𝓞 F) F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    rightConv F (rightTranslate F h φ) f ∈ V := by
  classical

  have hφK : φ ∈ cuspKFiniteSubmodule F pins ξ := hV.le hφ
  have hφc : Continuous φ := TSMain.continuous_of_mem_cuspKFiniteSubmodule F hφK
  obtain ⟨tφ, hφt⟩ := exists_archTypeFamily_mem_archCutSubmodule_of_mem_cuspKFiniteSubmodule F pins ξ hφK

  have hψc : Continuous (rightConv F (rightTranslate F h φ) f) :=
    (continuous_rightConv_and_contDiff_of_isFactorizableTestFn F (rightTranslate F h φ)
      (continuous_rightTranslate F hφc h) f hf).1
  have hψt : rightConv F (rightTranslate F h φ) f ∈ archCutSubmodule F tys :=
    rightConv_mem_archCutSubmodule F hf hft.1 (continuous_rightTranslate F hφc h)
  have hψdef : rightConv F (rightTranslate F h φ) f = rightConv F φ (fun x => f (x * h⁻¹)) :=
    rightConv_rightTranslate_eq F φ f h
  rw [hψdef] at hψc hψt

  have hφT : φ ∈ archCutSubmodule F (archTypeFamilyJoin F tφ tys) :=
    archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_left F tφ tys) hφt
  have hψT : rightConv F φ (fun x => f (x * h⁻¹)) ∈ archCutSubmodule F (archTypeFamilyJoin F tφ tys) :=
    archCutSubmodule_mono F (isContainedIn_archTypeFamilyJoin_right F tφ tys) hψt

  obtain ⟨e, he, hrepφ, hrepψ, hbi⟩ :=
    exists_convKernel F (archTypeFamilyJoin F tφ tys) φ (rightConv F φ (fun x => f (x * h⁻¹)))
      hφc hψc hφT hψT
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := exists_factors_mul_right hf h⁻¹
  have hfac : Continuous fa := continuous_of_isArchTestFactor F hfa
  letI : MeasurableSpace (ArchInfra.Kprod F) := borel _
  haveI : BorelSpace (ArchInfra.Kprod F) := ⟨rfl⟩
  haveI : SecondCountableTopology (ArchInfra.Kprod F) :=
    ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ F

  obtain ⟨f₂, hf₂def⟩ : ∃ f₂ : AdelicGL2 (𝓞 F) F → ℂ,
      f₂ = dconvWith (ArchInfra.muK F) (ArchInfra.inclAdelic F) e e (fun x => f (x * h⁻¹)) := ⟨_, rfl⟩
  have hf₂eq : ∀ g, f₂ g = dconvWith (ArchInfra.muK F) (ArchInfra.inclArch F) e e fa
      (AdelicLevel.glArch (𝓞 F) F g) * ff (AdelicLevel.glFin (𝓞 F) F g) := by
    intro g
    rw [hf₂def]
    exact dconvWith_tensor (ArchInfra.muK F) e fa ff (f := fun x => f (x * h⁻¹)) hfeq g
  have hf₂ : IsFactorizableTestFn F f₂ := by
    obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_dconvWith F (ArchInfra.muK F) he hfa
    exact ⟨dconvWith (ArchInfra.muK F) (ArchInfra.inclArch F) e e fa, ff,
      ⟨⟨Φ, hΦ, hΦeq⟩, hasCompactSupport_dconvWith (ArchInfra.continuous_inclArch (F := F)) hfa.2⟩,
      hff, hf₂eq⟩
  have hf₂t : IsArchBiFinite F (archTypeFamilyJoin F tφ tys) f₂ :=
    IsArchBiFinite.of_factorization F hf₂eq (hbi fa hfac)
  have hmem : rightConv F φ f₂ ∈ V := hV.rightConv_mem f₂ _ hf₂ hf₂t φ hφ

  have hid : rightConv F φ f₂ = rightConv F φ (fun x => f (x * h⁻¹)) := by
    funext x
    obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
    letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
    haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
    haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
    haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
    rw [hf₂def]
    exact integral_mul_dconvWith (μ := ArchInfra.muK F) (ν := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      (ArchInfra.continuous_inclAdelic (F := F)) he hφc (hfc.comp (continuous_mul_const h⁻¹))
      (show HasCompactSupport fun x => f (x * h⁻¹) from hfs.comp_homeomorph (Homeomorph.mulRight h⁻¹))
      (fun κ g _ _ => integral_mul_right_eq_self g (ArchInfra.inclAdelic F κ)) hrepφ hrepψ x
  rw [hψdef, ← hid]
  exact hmem

end Main

end AutomorphicForm
