/-
  The archimedean dual cut inside the K-finite carrier, and its right-convolution vanishing.

  The cut side of this subject is `ArchCutProjector`: the archimedean cut `archCutSubmodule F tys`
  inside the carrier `Ecf F` of continuous functions with finite-dimensional
  archimedean orbit span, its type-algebra module, the isotypic-component split of that module
  and the type projector on it. This module states the **dual** side, which the
  right-convolution test functions need:

  * `cutDc` is the dual cut `archDualCutSubmodule F tys` seen inside the carrier,
    `cutDM` its type-algebra module, and `goodComponentsD` /
    `CAD` / `CBD` split the isotypic components of
    that module into those inside the dual cut and those outside, with
    `isCompl_CAD_CBD` the `IsCompl`;
  * `cutDM_le_CAD` is the hard inclusion: a finite-dimensional
    type-submodule transported along an equivariant surjection stays inside the type-supremum,
    which is the type-invariance theorem of `RepTheory/TypeInvariance.lean` applied at
    `rowIsometryInclAt₀ F w`;
  * `rightConv_eq_zero_of_isIrreducible_of_le_CBD` is the vanishing on the complement: an
    irreducible type-component inside `CBD` pairs to zero against a
    cut vector `y`, by the non-degenerate invariant pairing and the dual type-supremum theorem
    of the same module; the carrier-side ingredients are `Representation.restrictRep` and the
    restriction API of `RepresentationTheory/SubrepresentationRestriction.lean`;
  * `exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq` assembles them: for `y` in the cut and a
    compactly supported `F2` in the carrier, some `F3` in `orbitSpanc F F2` lies in the dual cut
    and gives the same `rightConv F y`, and the headline
    `AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq`
    states it for a continuous compactly supported `f` with finite-dimensional archimedean orbit
    span.

  **Names.** The pin's public spellings are the port's, because the checker diffs statement
  text: a name that occurs *inside* a statement cannot be renamed without turning every mentioner
  into `MISSING`, and `cutDc`, `cutDM`, `CAD`, `CBD`, `goodComponentsD` and the engine's `Ecf`,
  `ρc`, `ℂK`, `underSub` all do. So the dual side of the split keeps the pin's short tokens
  (`cutDc`, `cutDM`, `CAD`, `CBD`) beside `ArchCutProjector`'s (`cutc`, `cutM`, `CA`, `CB`), and the
  rectification of all of them is recorded as debt — it needs a checker-side rename map applied to
  both sides of the comparison, which is not a change to make for cosmetics. The one place the
  port does rename is the pin's **private** plumbing, which is not diffed: the `c3_*` helpers
  (`c3` is the pin's `PartC3` section label) are named for what they do —
  `integrable_mul_rightConv`, `rightConv_add_right`, `rightConv_smul_right`,
  `rightConv_smul_left`, `exists_bilin_rightConv_fun`, `exists_bilin_rightConv_carrier`.

  Assumes: the definition layer `IsotypicCuspSpace` (`archDualCutSubmodule`,
  `archDualTypeSubmoduleAt`, `ArchTypeFamily`, `rowIsometryInclAt₀`), the engine
  `ArchCompactOrbit` (`Ecf`, `ρc`, `orbitSpan`, `orbitSpanc`,
  `ArchIsometryProd`), the cut module's shared type-algebra API (`ℂK`,
  `underSub`, `mem_mapSubmodule_iff`, `isCompl_biSup_isotypicComponents`,
  `exists_add_eq_of_isCompl_biSup_isotypicComponents`, `exists_eq_span_singleton_of_isSimpleModule`,
  `le_biSup_isotypicComponents_of_forall_linearEquiv_le`), `RepTheory/TypeInvariance.lean` (the two
  type-invariance theorems), `RepresentationTheory/SubrepresentationRestriction.lean`, and
  `ArchEntryBall.rowIsometryInclAt₀_injective` from `ArchApproxIdentity/EntryBall`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean:726–1325,1353–1373`
  (pinned `aa2d8b3`; the pin's `PartB7`, `PartC2`, `FarmC3G1G2`, `PartC3` and `PartC3Bridge`
  sections) and the headline's statement from
  `Theorems/Thm_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean`,
  minus the pin's `solution`-staging and the prelude already ported in `ArchCompactOrbit`.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCompactOrbit
import FLTForHuman.AutomorphicForm.Adelic.ArchCutProjector
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.EntryBall
import FLTForHuman.RepresentationTheory.InvariantPairing
import FLTForHuman.RepresentationTheory.SubrepresentationRestriction
import FLTForHuman.RepTheory.TypeInvariance
import FLTForHuman.NumberTheory.AdelicHaar.MulRightInvariant
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent
open AutomorphicForm.ArchCompactOrbit AutomorphicForm.ArchCutProjector
open scoped Pointwise BigOperators
open scoped AutomorphicForm.ArchCompactOrbit

attribute [-ext] NumberField.InfinitePlace.Completion.ext
attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext

-- The Borel/Haar instances below are `haveI`s by design: they feed instance search.
set_option linter.style.haveILetI false

namespace AutomorphicForm.ArchDualCut

variable (F : Type) [Field F] [NumberField F]

/-! ### The dual cut inside the carrier -/

theorem comp_mul_rowIsometryInclAt₀_mem_archDualCutSubmodule {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w'
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (x * rowIsometryInclAt₀ F w k)) ∈
      ⨆ i : Fin (tys.card w'), archDualTypeSubmoduleAt F w' (tys.rep w' i)) (hf w') ?_ ?_ ?_
  · intro i f hfi
    refine le_iSup (fun j => archDualTypeSubmoduleAt F w' (tys.rep w' j)) i ?_
    by_cases hw : w' = w
    · subst hw
      exact comp_mul_mem_typeSubmodule hfi k
    · exact comp_mul_mem_typeSubmodule_of_commute hfi _ fun k' =>
        commute_adelicArchGLInclAt_of_ne F (fun h => hw h.symm) _ _
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hw => Submodule.add_mem _ hu hw

/-- The dual archimedean cut, seen inside the carrier `Ecf F`. -/
def cutDc (tys : ArchTypeFamily F) : Submodule ℂ (Ecf F) :=
  (archDualCutSubmodule F tys).comap (Ecf F).subtype

theorem mem_cutDc {tys : ArchTypeFamily F} {φ : Ecf F} :
    φ ∈ cutDc F tys ↔ (φ : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys :=
  Iff.rfl

theorem cutDc_mem_invtSubmodule (tys : ArchTypeFamily F) :
    cutDc F tys ∈ (ρc F).invtSubmodule := by
  rw [Representation.mem_invtSubmodule]
  intro k φ hφ
  show ((ρc F k φ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys
  rw [ρc_apply_coe, archRep_apply]
  exact rightTranslate_mem_of_mem_iSup_range' F (archDualCutSubmodule F tys)
    (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archDualCutSubmodule F hφ w k)
    (archProdIncl_mem_iSup F k) _ hφ

/-- The dual cut as a module for the type algebra. -/
def cutDM (tys : ArchTypeFamily F) :
    Submodule (ℂK F) (ρc F).asModule :=
  (ρc F).mapSubmodule
    ⟨cutDc F tys, cutDc_mem_invtSubmodule F tys⟩

theorem mem_cutDM_iff (tys : ArchTypeFamily F) (x : (ρc F).asModule) :
    x ∈ cutDM F tys ↔
      (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈
        archDualCutSubmodule F tys :=
  mem_mapSubmodule_iff (ρc F) _ x

/-! ### The isotypic-component split -/

/-- The isotypic components that lie inside the dual cut. -/
def goodComponentsD (tys : ArchTypeFamily F) :
    Set (isotypicComponents (ℂK F) (ρc F).asModule) :=
  {c | (c : Submodule (ℂK F) (ρc F).asModule) ≤ cutDM F tys}

/-- The supremum of the components inside the dual cut. -/
def CAD (tys : ArchTypeFamily F) :
    Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ goodComponentsD F tys, (c : Submodule (ℂK F) (ρc F).asModule)

/-- The supremum of the components outside the dual cut. -/
def CBD (tys : ArchTypeFamily F) :
    Submodule (ℂK F) (ρc F).asModule :=
  ⨆ c ∈ (goodComponentsD F tys)ᶜ, (c : Submodule (ℂK F) (ρc F).asModule)

theorem isCompl_CAD_CBD (tys : ArchTypeFamily F) :
    IsCompl (CAD F tys) (CBD F tys) :=
  isCompl_biSup_isotypicComponents F (goodComponentsD F tys)

theorem CAD_le_cutDM (tys : ArchTypeFamily F) :
    CAD F tys ≤ cutDM F tys :=
  iSup₂_le fun _ hc => hc

/-! ### The carrier-side API the vanishing theorem needs -/

theorem ρc_mem_underSub (N : Submodule (ℂK F) (ρc F).asModule)
    (g : ArchIsometryProd F) {v : Ecf F} (hv : v ∈ underSub F N) :
    ρc F g v ∈ underSub F N := by
  rw [mem_underSub_iff] at hv ⊢
  rw [Representation.asModuleEquiv_symm_map_rho]
  exact N.smul_mem _ hv

open scoped Classical in
theorem coe_ρc_mulSingle (w : InfinitePlace F) (kw : rowIsometrySubgroup₀ w.Completion)
    (v : Ecf F) :
    ((ρc F (Pi.mulSingle w kw) v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) =
      rightTranslate F (rowIsometryInclAt₀ F w kw) v := by
  classical
  rw [ρc_apply_coe, archRep_apply, archProdIncl_mulSingle]

theorem rightTranslate_mem_map_subtype_of_forall (P : Submodule ℂ (Ecf F))
    (hP : ∀ (g : ArchIsometryProd F), ∀ v ∈ P, ρc F g v ∈ P) (w : InfinitePlace F)
    (kw : rowIsometrySubgroup₀ w.Completion) :
    ∀ s ∈ P.map (Ecf F).subtype,
      rightTranslate F (rowIsometryInclAt₀ F w kw) s ∈ P.map (Ecf F).subtype := by
  classical
  intro s hs
  obtain ⟨v, hv, rfl⟩ := hs
  refine ⟨ρc F (Pi.mulSingle w kw) v, hP _ v hv, ?_⟩
  exact coe_ρc_mulSingle F w kw v

/-! ### Right convolution and compact support -/

theorem hasCompactSupport_of_mem_orbitSpan {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : HasCompactSupport φ) :
    ∀ ψ ∈ orbitSpan F φ, HasCompactSupport ψ := by
  intro ψ hψ
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hψ
  · rintro _ ⟨k, rfl⟩
    exact hφ.comp_homeomorph (Homeomorph.mulRight (archProdIncl F k))
  · exact HasCompactSupport.zero
  · intro a b _ _ ha hb; exact ha.add hb
  · intro c a _ ha
    show HasCompactSupport (c • a)
    exact ha.smul_left

theorem rightConv_rightTranslate_rightTranslate' (ψ f : AdelicGL2 (𝓞 F) F → ℂ)
    (g : AdelicGL2 (𝓞 F) F) :
    rightConv F (rightTranslate F g ψ) (rightTranslate F g f) = rightConv F ψ f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  haveI := NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar F
  funext x
  show (∫ z, ψ (x * z * g) * f (z * g) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * z) * f z ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
  simp_rw [mul_assoc]
  exact MeasureTheory.integral_mul_right_eq_self (fun z => ψ (x * z) * f z) g

/-! ### The hard inclusion: the dual cut is a type-supremum -/

open Representation

theorem cutDM_le_CAD (tys : ArchTypeFamily F) :
    cutDM F tys ≤ CAD F tys := by
  classical
  haveI := isSemisimpleModule_ρc F
  refine @le_biSup_isotypicComponents_of_forall_linearEquiv_le (ℂK F) _
    (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule inferInstance (cutDM F tys) ?_
  intro m m' hm hmm' hmA
  haveI := hm
  obtain ⟨e⟩ := hmm'
  obtain ⟨hS, θ, hθ⟩ := exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m m' e
  obtain ⟨t, -, hmt⟩ := @exists_eq_span_singleton_of_isSimpleModule (ℂK F) _
    (ρc F).asModule inferInstance
    (ρc F).instModuleMonoidAlgebraAsModule m hm
  haveI : FiniteDimensional ℂ (underSub F m) :=
    finiteDimensional_underSub_of_eq_span F m t hmt
  have hS' := (exists_linearEquiv_map_asModuleEquiv_of_linearEquiv (ρc F) m' m'
    (LinearEquiv.refl _ _)).1

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m).map ι₀
  let Sf' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F m').map ι₀
  let eS : underSub F m ≃ₗ[ℂ] Sf := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  let eS' : underSub F m' ≃ₗ[ℂ] Sf' := Submodule.equivMapOfInjective ι₀ Subtype.val_injective _
  haveI : FiniteDimensional ℂ Sf := Module.Finite.map (underSub F m) ι₀
  let θf : Sf →ₗ[ℂ] Sf' := eS'.toLinearMap ∘ₗ θ.toLinearMap ∘ₗ eS.symm.toLinearMap
  have hθf_surj : Function.Surjective θf := by
    intro y
    refine ⟨eS (θ.symm (eS'.symm y)), ?_⟩
    simp [θf]
  have heS : ∀ (v : underSub F m), ((eS v : Sf) : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heS' : ∀ (v : underSub F m'), ((eS' v : Sf') : AdelicGL2 (𝓞 F) F → ℂ) = (v : Ecf F) := fun v => rfl
  have heSsymm : ∀ (s : Sf), (((eS.symm s : underSub F m) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := fun s => by
    rw [← heS (eS.symm s), eS.apply_symm_apply]

  intro x hx
  rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff]
  intro w
  have hxSf' : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ Sf' :=
    ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F m' _).mpr (by simpa using hx), rfl⟩
  show (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈
    ⨆ i : Fin (tys.card w), typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w i).ρ.dual
  refine AutomorphicForm.le_iSup_typeSubmodule_of_surjective_of_le_iSup_typeSubmodule (rowIsometryInclAt₀ F w)
    (ArchEntryBall.rowIsometryInclAt₀_injective F w)
    (fun i : Fin (tys.card w) => Module.Dual ℂ (Fin (tys.rep w i).n → ℂ))
    (fun i => (tys.rep w i).ρ.dual) Sf Sf'
    (rightTranslate_mem_map_subtype_of_forall F (underSub F m') hS' w)
    (rightTranslate_mem_map_subtype_of_forall F (underSub F m) hS w) θf hθf_surj ?_ ?_ hxSf'
  ·
    intro kw s
    have h1 : eS.symm ⟨fun x => (s : AdelicGL2 (𝓞 F) F → ℂ) (x * rowIsometryInclAt₀ F w kw),
          rightTranslate_mem_map_subtype_of_forall F (underSub F m) hS w kw s s.2⟩ =
        ⟨ρc F (Pi.mulSingle w kw) (eS.symm s : underSub F m), hS _ _ (eS.symm s).2⟩ := by
      apply eS.injective
      rw [eS.apply_symm_apply]
      apply Subtype.ext
      show rightTranslate F (rowIsometryInclAt₀ F w kw) (s : AdelicGL2 (𝓞 F) F → ℂ) = _
      rw [heS, coe_ρc_mulSingle, heSsymm]
    show ((eS' (θ (eS.symm ⟨_, _⟩)) : Sf') : AdelicGL2 (𝓞 F) F → ℂ) =
      rightTranslate F _ ((eS' (θ (eS.symm s)) : Sf') : _)
    rw [h1, heS', heS', hθ (Pi.mulSingle w kw) (eS.symm s), coe_ρc_mulSingle]
  ·
    rintro _ ⟨v, hv, rfl⟩
    have hv' := (mem_underSub_iff F m v).mp hv
    have := hmA hv'
    rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff, LinearEquiv.apply_symm_apply] at this
    exact this w

/-! ### The private right-convolution plumbing -/

private theorem integrable_mul_rightConv {ψ f : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 F) F) :
    MeasureTheory.Integrable (fun y => ψ (x * y) * f y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  exact ((hψ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfs.mul_left

private theorem rightConv_add_right {ψ f g : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) :
    rightConv F ψ (f + g) = rightConv F ψ f + rightConv F ψ g := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply,
    ← MeasureTheory.integral_add (integrable_mul_rightConv F hψ hf hfs x) (integrable_mul_rightConv F hψ hg hgs x)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (f y + g y) = ψ (x * y) * f y + ψ (x * y) * g y
  ring

private theorem rightConv_smul_right (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F ψ (c • f) = c • rightConv F ψ f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (c * f y) = c * (ψ (x * y) * f y)
  ring

private theorem rightConv_smul_left (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (c • ψ) f = c • rightConv F ψ f := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← MeasureTheory.integral_const_mul]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show c * ψ (x * y) * f y = c * (ψ (x * y) * f y)
  ring

private theorem exists_bilin_rightConv_fun (S T : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ s ∈ S, Continuous s) (hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t) (x0 : AdelicGL2 (𝓞 F) F) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ, ∀ (s : S) (t : T),
      β s t = rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) x0 := by
  refine ⟨LinearMap.mk₂ ℂ (fun (s : S) (t : T) => rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) x0)
    ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    rw [Submodule.coe_add, rightConv_add_left F (hS s s.2) (hS s' s'.2) (hT t t.2).1 (hT t t.2).2, Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, rightConv_smul_left F c, Pi.smul_apply]
  · intro s t t'
    rw [Submodule.coe_add, rightConv_add_right F (hS s s.2) (hT t t.2).1 (hT t t.2).2 (hT t' t'.2).1 (hT t' t'.2).2,
      Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, rightConv_smul_right F c, Pi.smul_apply]

private theorem exists_bilin_rightConv_carrier (S T : Submodule ℂ (Ecf F))
    (hT : ∀ t ∈ T, HasCompactSupport ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) (x0 : AdelicGL2 (𝓞 F) F) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] ℂ, ∀ (s : S) (t : T),
      β s t = rightConv F ((s : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x0 := by
  refine ⟨LinearMap.mk₂ ℂ
    (fun (s : S) (t : T) => rightConv F ((s : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ((t : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) x0)
    ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    rw [Submodule.coe_add, Submodule.coe_add,
      rightConv_add_left F (s : Ecf F).2.1 (s' : Ecf F).2.1 (t : Ecf F).2.1 (hT t t.2), Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, Submodule.coe_smul, rightConv_smul_left F c, Pi.smul_apply]
  · intro s t t'
    rw [Submodule.coe_add, Submodule.coe_add,
      rightConv_add_right F (s : Ecf F).2.1 (t : Ecf F).2.1 (hT t t.2) (t' : Ecf F).2.1 (hT t' t'.2), Pi.add_apply]
  · intro c s t
    rw [Submodule.coe_smul, Submodule.coe_smul, rightConv_smul_right F c, Pi.smul_apply]

/-! ### The vanishing on the complement -/

theorem rightConv_eq_zero_of_isIrreducible_of_le_CBD (tys : ArchTypeFamily F) (y : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys)
    (T : Submodule (ℂK F) (ρc F).asModule)
    (hTc : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F T, ρc F g v ∈ underSub F T)
    (hTirr : IsSimpleOrder (Subrepresentation (Representation.restrictRep (ρc F) (underSub F T) hTc)))
    (hTcs : ∀ v ∈ underSub F T, HasCompactSupport ((v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ))
    (hTB : T ≤ CBD F tys) :
    ∀ v ∈ underSub F T, rightConv F y v = 0 := by
  classical
  haveI := isSemisimpleModule_ρc F
  haveI := hTirr
  by_contra hcon
  push Not at hcon
  obtain ⟨v0, hv0, hne⟩ := hcon
  obtain ⟨x0, hx0⟩ : ∃ x0, rightConv F y v0 x0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)

  have hSc : ∀ (g : ArchIsometryProd F), ∀ s ∈ orbitSpanc F y, ρc F g s ∈ orbitSpanc F y := fun g s hs =>
    (Module.End.mem_invtSubmodule _).mp (((ρc F).mem_invtSubmodule).mp (orbitSpanc_mem_invtSubmodule F y) g) hs

  obtain ⟨βc, hβc⟩ := exists_bilin_rightConv_carrier F (orbitSpanc F y) (underSub F T) hTcs x0
  have hβc_inv : ∀ (g : ArchIsometryProd F) (s : orbitSpanc F y) (t : underSub F T),
      βc (Representation.restrictRep (ρc F) (orbitSpanc F y) hSc g s)
        (Representation.restrictRep (ρc F) (underSub F T) hTc g t) = βc s t := by
    intro g s t
    rw [hβc, hβc, Representation.restrictRep_apply_coe, Representation.restrictRep_apply_coe,
      ρc_apply_coe, ρc_apply_coe, archRep_apply, archRep_apply,
      rightConv_rightTranslate_rightTranslate']
  have hβc_ne : βc ≠ 0 := by
    intro h
    apply hx0
    have := hβc ⟨y, mem_orbitSpanc_self F y⟩ ⟨v0, hv0⟩
    rw [h, LinearMap.zero_apply, LinearMap.zero_apply] at this
    exact this.symm

  have hnd_c : ∀ t : underSub F T, (∀ s : orbitSpanc F y, βc s t = 0) → t = 0 := by
    intro t ht
    by_contra ht0
    exact hβc_ne (Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero _ _ βc hβc_inv
        ⟨t, ht0, ht⟩)

  let ι₀ := (Ecf F).subtype
  let Sf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (orbitSpanc F y).map ι₀
  let Tf : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := (underSub F T).map ι₀
  haveI : FiniteDimensional ℂ Sf := Module.Finite.map (orbitSpanc F y) ι₀
  obtain ⟨βf, hβf⟩ := exists_bilin_rightConv_fun F Sf Tf
    (by rintro _ ⟨v, -, rfl⟩; exact v.2.1) (by rintro _ ⟨v, hv, rfl⟩; exact ⟨v.2.1, hTcs v hv⟩) x0
  have hnd_f : ∀ t : Tf, (∀ s : Sf, βf s t = 0) → t = 0 := by
    rintro ⟨_, v, hv, rfl⟩ ht
    have hv0 : (⟨v, hv⟩ : underSub F T) = 0 := by
      apply hnd_c
      rintro ⟨s, hs⟩
      rw [hβc]
      have := ht ⟨(s : AdelicGL2 (𝓞 F) F → ℂ), s, hs, rfl⟩
      rw [hβf] at this
      exact this
    apply Subtype.ext
    have := congrArg (fun u : underSub F T => ((u : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) hv0
    exact this

  have hy_orbit : orbitSpan F (y : AdelicGL2 (𝓞 F) F → ℂ) ≤ archCutSubmodule F tys := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨k, rfl⟩
    show archRep F k (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys
    rw [archRep_apply]
    exact rightTranslate_mem_of_mem_iSup_range' F (archCutSubmodule F tys)
      (fun w k φ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) (archProdIncl_mem_iSup F k) _ hy
  have hSle : ∀ w : InfinitePlace F, Sf ≤ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i) := by
    intro w f hf
    obtain ⟨v, hv, rfl⟩ := hf
    have : ((v : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (y : AdelicGL2 (𝓞 F) F → ℂ) := by
      rw [← map_orbitSpanc]; exact ⟨v, hv, rfl⟩
    exact (mem_archCutSubmodule_iff F tys _).mp (hy_orbit this) w

  have hTf_le : ∀ w : InfinitePlace F, Tf ≤ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i) := by
    intro w
    exact AutomorphicForm.le_iSup_typeSubmodule_dual_of_invariant_pairing (rowIsometryInclAt₀ F w)
      (ArchEntryBall.rowIsometryInclAt₀_injective F w)
      (fun i : Fin (tys.card w) => Fin (tys.rep w i).n → ℂ) (fun i => (tys.rep w i).ρ) Sf Tf
      (rightTranslate_mem_map_subtype_of_forall F (orbitSpanc F y) hSc w)
      (rightTranslate_mem_map_subtype_of_forall F (underSub F T) hTc w) βf
      (fun k s t => by
        rw [hβf, hβf]
        exact congrFun (rightConv_rightTranslate_rightTranslate' F s t (rowIsometryInclAt₀ F w k)) x0)
      hnd_f (hSle w)

  have hT_cut : T ≤ cutDM F tys := by
    intro x hx
    rw [mem_cutDM_iff, mem_archDualCutSubmodule_iff]
    intro w
    exact hTf_le w ⟨(ρc F).asModuleEquiv x, (mem_underSub_iff F T _).mpr (by simpa using hx), rfl⟩
  have hT_bot : T = ⊥ := le_bot_iff.mp
    ((le_inf (hT_cut.trans (cutDM_le_CAD F tys)) hTB).trans
      (isCompl_CAD_CBD F tys).disjoint.le_bot)

  have hv0T := (mem_underSub_iff F T v0).mp hv0
  rw [hT_bot, Submodule.mem_bot (ℂK F), LinearEquiv.map_eq_zero_iff] at hv0T
  apply hne
  rw [hv0T]
  exact rightConv_zero_right F _

/-! ### Compact support and the assembly -/

theorem hasCompactSupport_of_mem_mapSubmodule_orbitSpanc (F2 : Ecf F)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) (x : (ρc F).asModule)
    (hx : x ∈ (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩) :
    HasCompactSupport (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [mem_mapSubmodule_iff] at hx
  have : (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈
      orbitSpan F (F2 : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [← map_orbitSpanc]; exact ⟨_, hx, rfl⟩
  exact hasCompactSupport_of_mem_orbitSpan F hF2s _ this

theorem rightConv_eq_zero_of_mem_inf_CBD (tys : ArchTypeFamily F) (y : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys) (F2 : Ecf F)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) (b : (ρc F).asModule)
    (hb : b ∈ (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩ ⊓
      CBD F tys) :
    rightConv F y (((ρc F).asModuleEquiv b : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = 0 := by
  classical
  haveI := isSemisimpleModule_ρc F
  set N : Submodule (ℂK F) (ρc F).asModule :=
    (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩ with hN
  have hNcs : ∀ x ∈ N, HasCompactSupport (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) :=
    fun x hx => hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s x (by rw [hN] at hx; exact hx)
  have hsup := IsSemisimpleModule.sSup_simples_le (R := ℂK F) (M := (ρc F).asModule)
    (N ⊓ CBD F tys)
  rw [← hsup, sSup_eq_iSup'] at hb
  refine (Submodule.iSup_induction _
    (motive := fun x => x ∈ N ∧ rightConv F y (((ρc F).asModuleEquiv x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = 0)
    hb ?_ ?_ ?_).2
  · rintro ⟨T, hT, hTle⟩ x hx
    haveI := hT
    refine ⟨(hTle hx).1, ?_⟩
    have hTc : ∀ (g : ArchIsometryProd F), ∀ v ∈ underSub F T, ρc F g v ∈ underSub F T :=
      fun g v hv => ρc_mem_underSub F T g hv
    have hTirr : IsSimpleOrder (Subrepresentation (Representation.restrictRep (ρc F) (underSub F T) hTc)) :=
      Representation.isIrreducible_of_isSimpleModule (ρc F) T hTc
    refine rightConv_eq_zero_of_isIrreducible_of_le_CBD F tys y hy T hTc hTirr ?_ (hTle.trans inf_le_right) _ ?_
    · intro v hv
      have hv' := (mem_underSub_iff F T v).mp hv
      have := hNcs _ (hTle hv').1
      rwa [LinearEquiv.apply_symm_apply] at this
    · exact (mem_underSub_iff F T _).mpr (by simpa using hx)
  · refine ⟨Submodule.zero_mem _, ?_⟩
    rw [map_zero]
    exact rightConv_zero_right F _
  · rintro a c ⟨haN, ha⟩ ⟨hcN, hc⟩
    refine ⟨Submodule.add_mem _ haN hcN, ?_⟩
    rw [map_add, Submodule.coe_add,
      rightConv_add_right F y.2.1 ((ρc F).asModuleEquiv a).2.1 (hNcs a haN)
        ((ρc F).asModuleEquiv c).2.1 (hNcs c hcN),
      ha, hc, add_zero]

theorem exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq (tys : ArchTypeFamily F) (y F2 : Ecf F)
    (hy : (y : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys)
    (hF2s : HasCompactSupport (F2 : AdelicGL2 (𝓞 F) F → ℂ)) :
    ∃ F3 : orbitSpanc F F2, ((F3 : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archDualCutSubmodule F tys ∧
      rightConv F y (F3 : Ecf F) = rightConv F y F2 := by
  classical
  haveI := isSemisimpleModule_ρc F
  let N : Submodule (ℂK F) (ρc F).asModule :=
    (ρc F).mapSubmodule ⟨orbitSpanc F F2, orbitSpanc_mem_invtSubmodule F F2⟩
  have hxN : (ρc F).asModuleEquiv.symm F2 ∈ N := by
    rw [mem_mapSubmodule_iff]; simpa using mem_orbitSpanc_self F F2
  obtain ⟨a, ha, b, hb, hab⟩ := exists_add_eq_of_isCompl_biSup_isotypicComponents (goodComponentsD F tys)
    (isCompl_CAD_CBD F tys) N _ hxN
  refine ⟨⟨(ρc F).asModuleEquiv a, (mem_mapSubmodule_iff (ρc F) _ a).mp ha.1⟩, ?_, ?_⟩
  · exact (mem_cutDM_iff F tys a).mp (CAD_le_cutDM F tys ha.2)
  · have hb0 := rightConv_eq_zero_of_mem_inf_CBD F tys y hy F2 hF2s b hb
    have hF2 : (F2 : AdelicGL2 (𝓞 F) F → ℂ) =
        (((ρc F).asModuleEquiv a : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) +
          ((ρc F).asModuleEquiv b : Ecf F) := by
      have := congrArg (ρc F).asModuleEquiv hab
      rw [LinearEquiv.apply_symm_apply, map_add] at this
      rw [this, Submodule.coe_add]
    show rightConv F y ((ρc F).asModuleEquiv a : Ecf F) = rightConv F y F2
    rw [hF2, rightConv_add_right F y.2.1 ((ρc F).asModuleEquiv a).2.1
      (hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s a ha.1)
      ((ρc F).asModuleEquiv b).2.1
      (hasCompactSupport_of_mem_mapSubmodule_orbitSpanc F F2 hF2s b hb.1), hb0, add_zero]

end AutomorphicForm.ArchDualCut

/-! ### The headline -/

open AutomorphicForm.ArchDualCut in
/-- For `y` in the archimedean cut and a continuous compactly supported `f` with
finite-dimensional archimedean orbit span, some `f'` in that span lies in the dual cut and
represents `y` the same way: `rightConv F y f' = rightConv F y f`. -/
theorem AutomorphicForm.exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hfc : Continuous f) (hfs : HasCompactSupport f)
    (hfK : FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f})) :
    ∃ f' ∈ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k f},
      f' ∈ archDualCutSubmodule F tys ∧ rightConv F y f' = rightConv F y f := by
  have hyE : y ∈ Ecf F := mem_Ecf_of_mem_archCutSubmodule F tys hy hyc
  have hfE : f ∈ Ecf F := by
    refine ⟨hfc, ?_⟩
    rw [orbitSpan_eq_span]
    exact hfK
  obtain ⟨F3, hF3D, hF3c⟩ :=
    exists_mem_orbitSpanc_mem_archDualCut_rightConv_eq F tys ⟨y, hyE⟩ ⟨f, hfE⟩ hy hfs
  refine ⟨((F3 : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), ?_, hF3D, hF3c⟩
  rw [← orbitSpan_eq_span]
  show _ ∈ orbitSpan F ((⟨f, hfE⟩ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)
  rw [← map_orbitSpanc]
  exact ⟨F3, F3.2, rfl⟩
