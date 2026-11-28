/-
The free-algebra lift of the differential correspondence vanishes with its `Pic0` class.

For a finite family of integral `K`-algebra maps `φ i, ψ i : F → F' i` with fundamental identities and
norm formulas, if the free-algebra lift of the `Pic0` correspondences `Pic0.correspondence (φ i) (ψ i)`
kills `p : FreeAlgebra ℤ ι`, then the free-algebra lift of the differential correspondences
`Differential.correspondence (φ i) (ψ i)` kills every regular differential of `F/K`:
`(lift (fun i => op (Differential.correspondence (φ i) (ψ i))) p) ω = 0`.

It is the differential half of the base-change dictionary whose `Pic0` half is
`Pic0/BaseChangeDescent.lean`, and the proof reduces the free-algebra statement to the traced
pull-back identity `pullbackAlong_traceAlong_eq_sum_lifts` and the vanishing of the sum of the
residues `sum_ord_smul_pullbackAlong_eq_zero`.

Assumes, from earlier modules: `Pic0/BaseChangeDescent` (the geometric-cycle consequence of the
vanishing lift), `Differential/PushPull` (the pull-back/trace dictionary), `ResidueTheorem/TraceSum`,
`IsCurveOver/ConstantFieldExtensionExists`, `Canonical/HasCanonicalDivisor`, and
`IsCurveOver/EssFiniteType`.

Transcribed from the pin below (pinned `aa2d8b3`, 444 `S_` lines).

## The rows

* `AlgebraicCurve.Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero` — 444 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero.lean>

spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero.lean

## Port deltas

The pin's `S_` surface is 32 declarations, all public. Five of them are **substituted** from modules
already public in the port, not restated (a second copy would be a name collision or a duplicate):

* `pullbackAlong_pullbackAlong`, `liftsAlong`, `mem_liftsAlong`, `liftsAlong_eq_range` —
  `AlgebraicCurve.TraceAtPoints.*` in `Differential/PushPull.lean` (the pin's own rows there);
* `separableAlong_of_charZero` — `AlgebraicCurve.separableAlong_of_charZero`, the identical
  statement, public in `WeilExchange/Transport.lean`.

The pin's `pullbackAlong_traceAlong_eq_sum` is **declared** here: the port's copy of that name
(`TraceAtPoints.pullbackAlong_traceAlong_eq_sum`) takes an explicit `S`/`hS` pair, a different
statement; the pin's `liftsFinset` specialisation sits on `Differential.pullbackAlong_traceAlong_eq_sum_lifts`.

`exists_finset_adjoin_eq_top`, `finiteAlong_of_isIntegral_of_adjoin_eq_top` and `finiteAlong_of_hfg`
are `private` in `IsCurveOver/ConstantFieldExtensionSpan.lean` (their `hfg` is the *target's*, the
pin's is the source's), so they are **not importable**; they are transcribed here at the pin's names,
as the pin states them (`finiteAlong_of_hfg` uses `ψ`'s finiteness, which is the form the headline
needs). They live in this module's `CotangentAbelSum` namespace, so no public full name is repeated
(`TraceBaseChangeProof.exists_finset_adjoin_eq_top` is a different, private, name).

Not transcribed: the pin's three `attribute [-instance]` / `[-simp]` blocks (its own hygiene for the
`Definitions/` instances; every proof here is generic `K`-algebra algebra and elaborates without
them), and its `p2m_export` / `p2m_open` / `p2m_exact_reverting` scaffolding.

The pin's proofs are walls of `letI`/`haveI` instance bindings; transcribed literally they trip
`linter.style.haveILetI` (20 hits on 7 declarations), so each of those seven carries a
declaration-scoped `set_option linter.style.haveILetI false in` — the same cure
`Pic0/BaseChangeDescent.lean` applies to its headline, and no proof is weakened by it.
-/
import FLTForHuman.AlgebraicCurve.Pic0.BaseChangeDescent
import FLTForHuman.AlgebraicCurve.Differential.PushPull
import FLTForHuman.AlgebraicCurve.ResidueTheorem.TraceSum
import FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionExists
import FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor
import FLTForHuman.AlgebraicCurve.IsCurveOver.EssFiniteType
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential TensorProduct

namespace AlgebraicCurve

namespace CotangentAbelSum

open AlgebraicCurve.TraceAtPoints

variable {K F F' E : Type*} [Field K] [Field F] [Field F'] [Field E]
  [Algebra K F] [Algebra K F'] [Algebra K E]

set_option linter.style.haveILetI false in
theorem finite_liftsAlong (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (e : F →ₐ[K] E) :
    (liftsAlong φ e).Finite := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  letI : Algebra F E := e.toRingHom.toAlgebra
  haveI : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq (fun x => (e.commutes x).symm)
  haveI : Module.Finite F F' := hfin
  haveI : Fintype (F' →ₐ[F] E) := minpoly.AlgHom.fintype F F' E
  rw [liftsAlong_eq_range φ e (fun _ => rfl) (fun _ => rfl)]
  exact Set.finite_range _

def liftsFinset (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (e : F →ₐ[K] E) :
    Finset (F' →ₐ[K] E) :=
  (finite_liftsAlong φ hfin e).toFinset

theorem mem_liftsFinset (φ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (e : F →ₐ[K] E)
    (σ : F' →ₐ[K] E) : σ ∈ liftsFinset φ hfin e ↔ σ.comp φ = e := by
  rw [liftsFinset, Set.Finite.mem_toFinset, mem_liftsAlong]

theorem pullbackAlong_traceAlong_eq_sum [IsAlgClosed E] (φ : F →ₐ[K] F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (e : F →ₐ[K] E) (ω' : Ω[F'⁄K]) :
    Differential.pullbackAlong e (Differential.traceAlong φ ω') =
      ∑ σ ∈ liftsFinset φ hfin e, Differential.pullbackAlong σ ω' :=
  AlgebraicCurve.Differential.pullbackAlong_traceAlong_eq_sum_lifts K F F' E φ hfin hsep e
    (liftsFinset φ hfin e) (mem_liftsFinset φ hfin e) ω'

theorem pullbackAlong_correspondence_eq_sum [IsAlgClosed E] (φ ψ : F →ₐ[K] F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (e : F →ₐ[K] E) (ω : Ω[F⁄K]) :
    Differential.pullbackAlong e (Differential.correspondence φ ψ ω) =
      ∑ σ ∈ liftsFinset φ hfin e, Differential.pullbackAlong (σ.comp ψ) ω := by
  rw [Differential.correspondence_apply, pullbackAlong_traceAlong_eq_sum φ hfin hsep]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [pullbackAlong_pullbackAlong]

def abelSum (ω : Ω[F⁄K]) : ((F →ₐ[K] E) →₀ ℤ) →+ Ω[E⁄K] :=
  Finsupp.liftAddHom fun y => zmultiplesHom Ω[E⁄K] (Differential.pullbackAlong y ω)

theorem abelSum_single (ω : Ω[F⁄K]) (y : F →ₐ[K] E) (n : ℤ) :
    abelSum ω (Finsupp.single y n) = n • Differential.pullbackAlong y ω := by
  rw [abelSum, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

theorem abelSum_add_left (ω₁ ω₂ : Ω[F⁄K]) (z : (F →ₐ[K] E) →₀ ℤ) :
    abelSum (ω₁ + ω₂) z = abelSum ω₁ z + abelSum ω₂ z := by
  rw [← AddMonoidHom.add_apply]
  refine DFunLike.congr_fun (Finsupp.addHom_ext fun y n => ?_) z
  simp only [AddMonoidHom.add_apply, abelSum_single, map_add, smul_add]

theorem abelSum_zsmul_left (r : ℤ) (ω : Ω[F⁄K]) (z : (F →ₐ[K] E) →₀ ℤ) :
    abelSum (r • ω) z = r • abelSum ω z := by
  have : abelSum (E := E) (r • ω) = r • abelSum ω := by
    refine Finsupp.addHom_ext fun y n => ?_
    simp only [AddMonoidHom.smul_apply, abelSum_single, LinearMap.map_smul_of_tower,
      smul_comm n r]
  rw [this, AddMonoidHom.smul_apply]

def pointAction (φ ψ : F →ₐ[K] F') (hfin : FiniteAlong K φ) :
    ((F →ₐ[K] E) →₀ ℤ) →+ ((F →ₐ[K] E) →₀ ℤ) :=
  Finsupp.liftAddHom fun e =>
    zmultiplesHom _ (∑ σ ∈ liftsFinset φ hfin e, Finsupp.single (σ.comp ψ) (1 : ℤ))

theorem pointAction_single (φ ψ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (e : F →ₐ[K] E)
    (n : ℤ) :
    pointAction φ ψ hfin (Finsupp.single e n) =
      n • ∑ σ ∈ liftsFinset φ hfin e, Finsupp.single (σ.comp ψ) (1 : ℤ) := by
  rw [pointAction, Finsupp.liftAddHom_apply_single, zmultiplesHom_apply]

theorem abelSum_correspondence [IsAlgClosed E] (φ ψ : F →ₐ[K] F')
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ) (ω : Ω[F⁄K])
    (z : (F →ₐ[K] E) →₀ ℤ) :
    abelSum (Differential.correspondence φ ψ ω) z = abelSum ω (pointAction φ ψ hfin z) := by
  rw [← AddMonoidHom.comp_apply]
  refine DFunLike.congr_fun (Finsupp.addHom_ext fun e n => ?_) z
  rw [AddMonoidHom.comp_apply, abelSum_single, pointAction_single, map_zsmul, map_sum,
    pullbackAlong_correspondence_eq_sum φ ψ hfin hsep, Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun σ _ => ?_)
  rw [abelSum_single, one_smul]

section Family

variable {ι : Type*} (Fr : ι → Type*) [∀ i, Field (Fr i)] [∀ i, Algebra K (Fr i)]
  (φ ψ : ∀ i, F →ₐ[K] Fr i) (hfin : ∀ i, FiniteAlong K (φ i))

def pointActionLift (E : Type*) [Field E] [Algebra K E] :
    FreeAlgebra ℤ ι →ₐ[ℤ] Module.End ℤ ((F →ₐ[K] E) →₀ ℤ) :=
  FreeAlgebra.lift ℤ fun i => (pointAction (E := E) (φ i) (ψ i) (hfin i)).toIntLinearMap

theorem abelSum_lift [IsAlgClosed E] (hsep : ∀ i, SeparableAlong K (φ i))
    (p : FreeAlgebra ℤ ι) (ω : Ω[F⁄K]) (z : (F →ₐ[K] E) →₀ ℤ) :
    abelSum (MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω) z =
      abelSum ω (pointActionLift Fr φ ψ hfin E p z) := by
  induction p using FreeAlgebra.induction generalizing ω z with
  | grade0 r =>
      simp only [eq_intCast, map_intCast, MulOpposite.unop_intCast, Module.End.intCast_apply,
        abelSum_zsmul_left, map_zsmul]
  | grade1 i =>
      simp only [FreeAlgebra.lift_ι_apply, MulOpposite.unop_op, pointActionLift,
        AddMonoidHom.coe_toIntLinearMap]
      exact abelSum_correspondence (φ i) (ψ i) (hfin i) (hsep i) ω z
  | mul a b ha hb =>
      simp only [map_mul, MulOpposite.unop_mul, Module.End.mul_apply]
      rw [hb, ha]
  | add a b ha hb =>
      simp only [map_add, MulOpposite.unop_add, LinearMap.add_apply]
      rw [abelSum_add_left, ha, hb]

theorem pullbackAlong_lift_eq_abelSum [IsAlgClosed E] (hsep : ∀ i, SeparableAlong K (φ i))
    (p : FreeAlgebra ℤ ι) (ω : Ω[F⁄K]) (e : F →ₐ[K] E) :
    Differential.pullbackAlong e (MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω) =
      abelSum ω (pointActionLift Fr φ ψ hfin E p (Finsupp.single e 1)) := by
  rw [← abelSum_lift Fr φ ψ hfin hsep p ω (Finsupp.single e 1), abelSum_single, one_smul]

end Family

set_option linter.style.haveILetI false in
theorem pullbackAlong_injective (η : F →ₐ[K] E) (hsep : SeparableAlong K η) :
    Function.Injective (Differential.pullbackAlong η) := by
  letI : Algebra F E := algebraAlong η
  haveI := isScalarTower_along η
  haveI : Algebra.IsSeparable F E := hsep
  haveI : Algebra.FormallyEtale F E := Algebra.FormallyEtale.of_isSeparable F E

  have hfac : ∀ ω : Ω[F⁄K], Differential.pullbackAlong η ω =
      tensorKaehlerEquivOfFormallyEtale K F E ((1 : E) ⊗ₜ ω) := by
    intro ω
    rw [tensorKaehlerEquivOfFormallyEtale_apply, mapBaseChange_tmul, one_smul]
    rfl

  have hincl : Function.Injective (fun ω : Ω[F⁄K] => (1 : E) ⊗ₜ[F] ω) := by
    have h1 : Function.Injective ((Algebra.linearMap F E).rTensor Ω[F⁄K]) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (algebraMap F E).injective
    have h2 : Function.Injective (TensorProduct.lid F Ω[F⁄K]).symm :=
      (TensorProduct.lid F Ω[F⁄K]).symm.injective
    have : (fun ω : Ω[F⁄K] => (1 : E) ⊗ₜ[F] ω) =
        (Algebra.linearMap F E).rTensor Ω[F⁄K] ∘ (TensorProduct.lid F Ω[F⁄K]).symm := by
      funext ω
      simp only [Function.comp_apply, TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul,
        Algebra.linearMap_apply, map_one]
    rw [this]
    exact h1.comp h2
  intro ω₁ ω₂ h
  rw [hfac, hfac] at h
  exact hincl ((tensorKaehlerEquivOfFormallyEtale K F E).injective h)

theorem separableAlong_of_isSeparable (η : F →ₐ[K] E) [Algebra F E] [Algebra.IsSeparable F E]
    (h : ∀ x, algebraMap F E x = η x) : SeparableAlong K η := by
  have hinst : (algebraAlong η : Algebra F E) = ‹Algebra F E› :=
    Algebra.algebra_ext _ _ (fun x => (h x).symm)
  unfold SeparableAlong
  rw [hinst]
  infer_instance

theorem separableAlong_algebraicClosure [CharZero F] :
    SeparableAlong K (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) :=
  separableAlong_of_isSeparable _ (fun _ => rfl)

section Reformulation

variable {ι : Type*} (Fr : ι → Type*) [∀ i, Field (Fr i)] [∀ i, Algebra K (Fr i)]
  (φ ψ : ∀ i, F →ₐ[K] Fr i) (hfin : ∀ i, FiniteAlong K (φ i))

theorem differential_lift_eq_zero_of_abelSum_eq_zero
    (hsep : ∀ i, SeparableAlong K (φ i)) (p : FreeAlgebra ℤ ι) (ω : Ω[F⁄K])
    {E : Type*} [Field E] [Algebra K E] [IsAlgClosed E] (η : F →ₐ[K] E)
    (hη : SeparableAlong K η)
    (h : abelSum ω (pointActionLift Fr φ ψ hfin E p (Finsupp.single η 1)) = 0) :
    MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0 := by
  apply pullbackAlong_injective η hη
  rw [map_zero, pullbackAlong_lift_eq_abelSum Fr φ ψ hfin hsep p ω η, h]

theorem forall_regular_lift_eq_zero_of_abelSum_eq_zero
    (hsep : ∀ i, SeparableAlong K (φ i)) (p : FreeAlgebra ℤ ι)
    {E : Type*} [Field E] [Algebra K E] [IsAlgClosed E] (η : F →ₐ[K] E)
    (hη : SeparableAlong K η)
    (h : ∀ ω ∈ regularDifferentials K F,
      abelSum ω (pointActionLift Fr φ ψ hfin E p (Finsupp.single η 1)) = 0) :
    ∀ ω ∈ regularDifferentials K F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0 :=
  fun ω hω => differential_lift_eq_zero_of_abelSum_eq_zero Fr φ ψ hfin hsep p ω η hη (h ω hω)

end Reformulation

set_option linter.style.haveILetI false in
theorem exists_finset_adjoin_eq_top
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ G : Finset F, IntermediateField.adjoin K (G : Set F) = ⊤ := by
  classical
  obtain ⟨x, -, hxfin⟩ := hfg
  set Kx := IntermediateField.adjoin K ({x} : Set F)
  haveI := hxfin
  let b := Module.finBasis Kx F
  refine ⟨insert x (Finset.univ.image b), ?_⟩
  have hset : ((insert x (Finset.univ.image b) : Finset F) : Set F) = {x} ∪ Set.range b := by
    ext y
    simp only [Finset.coe_insert, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_insert_iff, Set.mem_range, Set.singleton_union]
  rw [hset, ← IntermediateField.adjoin_adjoin_left]
  have htop : IntermediateField.adjoin Kx (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    have hspan : f ∈ Submodule.span Kx (Set.range b) := by
      rw [b.span_eq]; trivial
    have hle : Submodule.span Kx (Set.range b) ≤
        (IntermediateField.adjoin Kx (Set.range b)).toSubalgebra.toSubmodule :=
      Submodule.span_le.2 (fun y hy => IntermediateField.subset_adjoin Kx _ hy)
    exact hle hspan
  rw [htop]
  rfl

set_option linter.style.haveILetI false in
theorem exists_finset_adjoin_eq_top_along (ψ : F →ₐ[K] F') (hfin : FiniteAlong K ψ)
    (G : Finset F) (hG : IntermediateField.adjoin K (G : Set F) = ⊤) :
    ∃ T : Finset F', IntermediateField.adjoin K (T : Set F') = ⊤ := by
  classical
  letI : Algebra F F' := algebraAlong ψ
  haveI := isScalarTower_along ψ
  haveI : Module.Finite F F' := hfin
  let b := Module.finBasis F F'
  refine ⟨G.image ψ ∪ Finset.univ.image b, ?_⟩
  set T : Finset F' := G.image ψ ∪ Finset.univ.image b with hTdef
  have hψG : ∀ c : F, ψ c ∈ IntermediateField.adjoin K (T : Set F') := by
    intro c
    have hc : c ∈ IntermediateField.adjoin K (G : Set F) := by rw [hG]; trivial
    have hmap : ψ c ∈ (IntermediateField.adjoin K (G : Set F)).map ψ := ⟨c, hc, rfl⟩
    rw [IntermediateField.adjoin_map] at hmap
    refine IntermediateField.adjoin.mono K _ _ ?_ hmap
    rintro _ ⟨g, hg, rfl⟩
    simp only [hTdef, Finset.coe_union, Finset.coe_image, Set.mem_union, Set.mem_image,
      Finset.mem_coe]
    exact Or.inl ⟨g, hg, rfl⟩
  have hb : ∀ j, b j ∈ IntermediateField.adjoin K (T : Set F') := by
    intro j
    refine IntermediateField.subset_adjoin K _ ?_
    simp only [hTdef, Finset.coe_union, Finset.coe_image, Finset.coe_univ, Set.image_univ,
      Set.mem_union, Set.mem_range]
    exact Or.inr ⟨j, rfl⟩
  rw [eq_top_iff]
  intro f _
  rw [← b.linearCombination_repr f, Finsupp.linearCombination_apply, Finsupp.sum]
  refine sum_mem (fun j _ => ?_)
  rw [Algebra.smul_def]
  exact mul_mem (hψG _) (hb j)

set_option linter.style.haveILetI false in
theorem finiteAlong_of_isIntegral_of_adjoin_eq_top (φ : F →ₐ[K] F')
    (hφ : φ.toRingHom.IsIntegral) (T : Finset F')
    (hT : IntermediateField.adjoin K (T : Set F') = ⊤) : FiniteAlong K φ := by
  letI : Algebra F F' := algebraAlong φ
  haveI := isScalarTower_along φ
  have hT' : IntermediateField.adjoin F (T : Set F') = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hle : IntermediateField.adjoin K (T : Set F') ≤
        (IntermediateField.adjoin F (T : Set F')).restrictScalars K :=
      IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin F _)
    have hy : y ∈ IntermediateField.adjoin K (T : Set F') := by rw [hT]; trivial
    exact hle hy
  haveI : FiniteDimensional F (IntermediateField.adjoin F (T : Set F')) :=
    IntermediateField.finiteDimensional_adjoin (fun t _ => hφ t)
  have e : (IntermediateField.adjoin F (T : Set F')) ≃ₗ[F] F' :=
    ((IntermediateField.equivOfEq hT').trans IntermediateField.topEquiv).toLinearEquiv
  exact Module.Finite.equiv e

theorem finiteAlong_of_hfg
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K ψ) :
    FiniteAlong K φ := by
  obtain ⟨G, hG⟩ := exists_finset_adjoin_eq_top (K := K) (F := F) hfg
  obtain ⟨T, hT⟩ := exists_finset_adjoin_eq_top_along ψ hfin G hG
  exact finiteAlong_of_isIntegral_of_adjoin_eq_top φ hφ T hT

set_option linter.style.haveILetI false in
theorem target_of_abelSum_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral)
    (hfin : ∀ i, FiniteAlong K (ψ i))
    (p : FreeAlgebra ℤ ι)
    (h : ∀ ω ∈ regularDifferentials K F,
      abelSum ω (pointActionLift F' φ ψ (fun i => finiteAlong_of_hfg hfg (φ i) (ψ i) (hφ i) (hfin i))
        (AlgebraicClosure F) p
        (Finsupp.single (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) 1)) = 0) :
    ∀ ω ∈ regularDifferentials K F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0 := by
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  exact forall_regular_lift_eq_zero_of_abelSum_eq_zero F' φ ψ _
    (fun i => separableAlong_of_charZero (φ i) (hφ i)) p
    (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) separableAlong_algebraicClosure h

section ClosedForm

variable {ι : Type*} (Fr : ι → Type*) [∀ i, Field (Fr i)] [∀ i, Algebra K (Fr i)]
  (φ ψ : ∀ i, F →ₐ[K] Fr i) (hfin : ∀ i, FiniteAlong K (φ i))

theorem pointActionLift_eq_finsum_lift (E : Type*) [Field E] [Algebra K E] :
    pointActionLift Fr φ ψ hfin E =
      FreeAlgebra.lift ℤ (fun i => (Finsupp.liftAddHom fun e : F →ₐ[K] E =>
        zmultiplesHom ((F →ₐ[K] E) →₀ ℤ)
          (∑ᶠ σ ∈ {σ : Fr i →ₐ[K] E | σ.comp (φ i) = e},
            Finsupp.single (σ.comp (ψ i)) (1 : ℤ))).toIntLinearMap) := by
  unfold pointActionLift pointAction
  congr 1
  funext i
  congr 2
  funext e
  congr 1
  exact (finsum_mem_eq_finite_toFinset_sum _ (finite_liftsAlong (φ i) (hfin i) e)).symm

end ClosedForm

end CotangentAbelSum

set_option linter.style.haveILetI false in
open CotangentAbelSum in
/-- The wrapper's headline: the free-algebra lift of the differential correspondences kills every
regular differential when the free-algebra lift of the `Pic0` correspondences does. -/
theorem Pic0.freeAlgebra_lift_differential_eq_zero_of_lift_correspondence_eq_zero
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    {ι : Type*} (F' : ι → Type*) [∀ i, Field (F' i)] [∀ i, Algebra K (F' i)]
    [∀ i, HasPrincipalDivisors K (F' i)]
    (φ ψ : ∀ i, F →ₐ[K] F' i)
    (hφ : ∀ i, (φ i).toRingHom.IsIntegral) (hψ : ∀ i, (ψ i).toRingHom.IsIntegral)
    (hFI : ∀ i, FundamentalIdentityAlong K (φ i) (hφ i))
    (hfin : ∀ i, FiniteAlong K (ψ i)) (hN : ∀ i, NormFormulaAlong K (ψ i) (hfin i))
    (p : FreeAlgebra ℤ ι)
    (hp : FreeAlgebra.lift ℤ (fun i =>
      (Pic0.correspondence (φ i) (ψ i) (hφ i) (hψ i) (hFI i) (hfin i) (hN i)).toIntLinearMap) p = 0) :
    ∀ ω ∈ regularDifferentials K F,
      MulOpposite.unop (FreeAlgebra.lift ℤ
        (fun i => MulOpposite.op (Differential.correspondence (φ i) (ψ i))) p) ω = 0 := by
  classical

  have hfg₀ := hfg
  obtain ⟨x, hxT, hxF⟩ := hfg₀
  haveI : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hxT hxF
  haveI : HasCanonicalDivisor (K := K) (F := F) := AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver
  obtain ⟨FE, _, _, _, _, _, _, _, _, hfgE, hgen⟩ :=
    AlgebraicCurve.exists_constantFieldExtension K F (AlgebraicClosure F) hfg

  refine target_of_abelSum_eq_zero K F hfg F' φ ψ hφ hfin p ?_
  intro ω hω

  obtain ⟨g, hg, S, y, hS, hrat, hEq⟩ :=
    AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero K F hfg F'
      φ ψ hφ hψ hFI hfin hN p hp (AlgebraicClosure F) FE hfgE hgen
      (IsScalarTower.toAlgHom K F (AlgebraicClosure F))
  have hpt : pointActionLift F' φ ψ
      (fun i => finiteAlong_of_hfg hfg (φ i) (ψ i) (hφ i) (hfin i)) (AlgebraicClosure F) p
        (Finsupp.single (IsScalarTower.toAlgHom K F (AlgebraicClosure F)) 1) =
      ∑ P ∈ S, Finsupp.single (y P) (P.ord g) := by
    rw [pointActionLift_eq_finsum_lift, hEq]

  rw [hpt, map_sum]
  simp only [abelSum_single]
  exact AlgebraicCurve.Differential.sum_ord_smul_pullbackAlong_eq_zero K F (AlgebraicClosure F) FE
    hfg hfgE hgen g hg S y hS hrat ω hω

end AlgebraicCurve

end
