/-
  The S-units and the coordinates of an idèle.

  `DeepUnits S` is the product of the local unit groups away from `S`, `SUnits S`
  the product of the local groups at `S`, and
  `asm : (InfiniteAdeleRing F)ˣ × (SUnits S × DeepUnits S) →* (AdeleRing (𝓞 F) F)ˣ`
  assembles them into an idèle. `coord` is the inverse assembly on `unitsOutside S`,
  `asmHomeo` the resulting homeomorphism, `isOpenEmbedding_asm` the openness of
  the assembly, and `asmMeasure`/`setIntegral_unitsOutside_eq_integral_asmMeasure`
  the pullback of the idèlic measure. The tail ports the local coset decomposition
  of the integers (`card_residueField_eq_absNorm` … `measure_integers_eq_card_mul`).

  Transcribed from the pin's own namespace, declared lines 666–1406 of file A,
  pinned `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean`

  The idèle prelude (`unitsOutside`, `unitAtHom`, `ordAt`, `Uniformizers`,
  `expVec`, `shell`, …) is imported from
  `FLTForHuman.NumberTheory.NumberField.TateGlobal.Ideles`.

  Build notes: the pin's `p2m_*` scaffolding is dropped, and so are the
  high-heartbeat (`6400000`) / `maxSynthPendingDepth 3` wrappers the pin puts on
  `integers_eq_iUnion_image`, `pairwise_disjoint_image`, `cosetMap_image_eq` and
  `measure_integers_eq_card_mul`; all four elaborate unchanged at the port's low
  edit cap, so no instance-inference fix was needed for them. The seven
  `scoped instance`s of `SecondCountableTopology` that the pin declares
  just before this slice are re-declared in `Ideles.lean` (their pin lines
  638–660) and re-activated by `open scoped NumberField.TateGlobal`. No file-wide
  option beyond `set_option autoImplicit false`.

  Chapter-prefix rename (work order §3.1): the pin's chapter namespace
  `M4aLocalCFT.LocalHaarModulus` becomes `NumberField.TateGlobal.LocalHaarModulus`,
  i.e. `M4aLocalCFT.LocalHaarModulus.card_residueField_eq_absNorm` ≡
  `NumberField.TateGlobal.LocalHaarModulus.card_residueField_eq_absNorm`; the
  sub-namespace is kept (A declares three names twice under different
  `M4aLocalCFT.*` sub-namespaces) and the block's statements are unchanged.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Ideles

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel MeasureTheory Set Filter Topology TopologicalSpace
open scoped NNReal Pointwise NumberField.TateGlobal

section Fold_TateAssembly

noncomputable section

namespace NumberField

namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

section Assembly

variable (S : Finset (HeightOneSpectrum (𝓞 F)))


-- pin: DeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:666)
abbrev DeepUnits : Type := (v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S}) → (v.1.adicCompletionIntegers F)ˣ

-- pin: SUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:668)
abbrev SUnits : Type := (v : S) → (v.1.adicCompletion F)ˣ

set_option linter.style.haveILetI false in
-- pin: instSecondCountableDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:670)
-- The two `haveI`s are load-bearing instance arguments for the `infer_instance`s.
scoped instance instSecondCountableDeepUnits : SecondCountableTopology (DeepUnits (F := F) S) := by
  haveI : Countable {v : HeightOneSpectrum (𝓞 F) // v ∉ S} := by
    haveI := countable_heightOneSpectrum F
    infer_instance
  infer_instance

-- pin: instCompactSpaceDeepUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:676)
scoped instance instCompactSpaceDeepUnits : CompactSpace (DeepUnits (F := F) S) := by infer_instance

open scoped Classical in
-- pin: extendUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:679)
def extendUnits : DeepUnits (F := F) S →* ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ) where
  toFun o v := if h : v ∈ S then 1 else o ⟨v, h⟩
  map_one' := by
    funext v
    by_cases h : v ∈ S
    · rw [dite_eq_left h]; rfl
    · rw [dite_eq_right h]; rfl
  map_mul' o o' := by
    funext v
    by_cases h : v ∈ S
    · rw [Pi.mul_apply, dite_eq_left h, dite_eq_left h, dite_eq_left h, one_mul]
    · rw [Pi.mul_apply, dite_eq_right h, dite_eq_right h, dite_eq_right h]; rfl

open scoped Classical in
-- pin: extendUnits_apply_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:693)
theorem extendUnits_apply_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    extendUnits S o v = 1 := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = 1
  rw [dite_eq_left hv]

open scoped Classical in
-- pin: extendUnits_apply_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:699)
theorem extendUnits_apply_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    extendUnits S o v = o ⟨v, hv⟩ := by
  show (if h : v ∈ S then (1 : (v.adicCompletionIntegers F)ˣ) else o ⟨v, h⟩) = o ⟨v, hv⟩
  rw [dite_eq_right hv]

-- pin: continuous_extendUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:704)
theorem continuous_extendUnits : Continuous (extendUnits (F := F) S) := by
  refine continuous_pi fun v => ?_
  by_cases h : v ∈ S
  · have : (fun o : DeepUnits (F := F) S => extendUnits S o v) = fun _ => 1 := by
      funext o; exact extendUnits_apply_of_mem S o h
    rw [this]; exact continuous_const
  · have : (fun o : DeepUnits (F := F) S => extendUnits S o v) = fun o => o ⟨v, h⟩ := by
      funext o; exact extendUnits_apply_of_not_mem S o h
    rw [this]; exact continuous_apply _

-- pin: structureRingHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:714)
def structureRingHom : ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F) →+* FiniteAdeleRing (𝓞 F) F where
  toFun x := RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Filter.cofinite x
  map_one' := RestrictedProduct.ext _ _ fun _ => rfl
  map_mul' _ _ := RestrictedProduct.ext _ _ fun _ => rfl
  map_zero' := RestrictedProduct.ext _ _ fun _ => rfl
  map_add' _ _ := RestrictedProduct.ext _ _ fun _ => rfl

-- pin: continuous_structureRingHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:723)
theorem continuous_structureRingHom : Continuous (structureRingHom (F := F)) :=
  RestrictedProduct.isEmbedding_structureMap.continuous

-- pin: piUnitsInv (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:726)
def piUnitsInv : ((v : HeightOneSpectrum (𝓞 F)) → (v.adicCompletionIntegers F)ˣ)
    →* ((v : HeightOneSpectrum (𝓞 F)) → v.adicCompletionIntegers F)ˣ :=
  MulEquiv.piUnits.symm.toMonoidHom

-- pin: continuous_piUnitsInv (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:730)
theorem continuous_piUnitsInv : Continuous (piUnitsInv (F := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact continuous_pi fun v => Units.continuous_val.comp (continuous_apply v)
  · exact continuous_pi fun v => Units.continuous_coe_inv.comp (continuous_apply v)

-- pin: deepAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:735)
def deepAsm : DeepUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  ((Units.map ((finIncl (𝓞 F) F).comp (structureRingHom (F := F)).toMonoidHom)).comp piUnitsInv).comp (extendUnits S)

-- pin: continuous_deepAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:738)
theorem continuous_deepAsm : Continuous (deepAsm (F := F) S) :=
  ((Units.continuous_map ((continuous_const.prodMk continuous_id : Continuous fun x : FiniteAdeleRing (𝓞 F) F =>
      (((1 : InfiniteAdeleRing F), x) : AdeleRing (𝓞 F) F)).comp continuous_structureRingHom)).comp
    continuous_piUnitsInv).comp (continuous_extendUnits S)

-- pin: deepAsm_val_fst (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:743)
theorem deepAsm_val_fst (o : DeepUnits (F := F) S) : ((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).1 = 1 :=
  rfl

-- pin: deepAsm_val_snd_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:746)
theorem deepAsm_val_snd_apply (o : DeepUnits (F := F) S) (v : HeightOneSpectrum (𝓞 F)) :
    (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v
      = ((extendUnits S o v : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) :=
  rfl

-- pin: unitAtHom_deepAsm_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:751)
theorem unitAtHom_deepAsm_of_not_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (deepAsm S o) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (o ⟨v, hv⟩) := by
  refine Units.ext ?_
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_not_mem S o hv]
  rfl

-- pin: unitAtHom_deepAsm_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:758)
theorem unitAtHom_deepAsm_of_mem (o : DeepUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (deepAsm S o) = 1 := by
  refine Units.ext ?_
  show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v = _
  rw [deepAsm_val_snd_apply, extendUnits_apply_of_mem S o hv]
  rfl

-- pin: deepAsm_mem_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:765)
theorem deepAsm_mem_unitsOutside (o : DeepUnits (F := F) S) : deepAsm S o ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  constructor
  · intro v hv
    show (((deepAsm S o : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _
  · intro v hv
    rw [← map_inv]
    show (((deepAsm S o⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 : FiniteAdeleRing (𝓞 F) F) v ∈ _
    rw [deepAsm_val_snd_apply]
    exact SetLike.coe_mem _

end Assembly

end NumberField.TateGlobal

end

end Fold_TateAssembly

section Fold_TateAssembly2



noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

-- pin: idele_ext (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:807)
theorem idele_ext {x y : (AdeleRing (𝓞 F) F)ˣ} (harch : archUnits x = archUnits y)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 F), unitAtHom v x = unitAtHom v y) : x = y := by
  refine Units.ext (Prod.ext ?_ ?_)
  · exact congrArg Units.val harch
  · refine RestrictedProduct.ext (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) fun v => ?_
    exact congrArg Units.val (hfin v)

section EmbUnitContinuity

variable (v : HeightOneSpectrum (𝓞 F))

omit [NumberField F] in
-- pin: cofinite_le_principal_compl_singleton (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:820)
theorem cofinite_le_principal_compl_singleton :
    (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F))) :=
  Filter.le_principal_iff.mpr (Set.finite_singleton v).compl_mem_cofinite

open scoped Classical in
-- pin: finSinglePrincipal (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:825)
def finSinglePrincipal (c : v.adicCompletion F) :
    RestrictedProduct (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
      (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
      (𝓟 ({v}ᶜ : Set (HeightOneSpectrum (𝓞 F)))) :=
  ⟨Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c,
    Filter.eventually_principal.mpr fun w hw => by
      have hwv : w ≠ v := by simpa using hw
      show Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w ∈ _
      rw [Function.update_of_ne hwv]
      exact one_mem _⟩

open scoped Classical in
-- pin: continuous_finSinglePrincipal (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:837)
theorem continuous_finSinglePrincipal : Continuous (finSinglePrincipal (F := F) v) := by
  refine RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr fun w => ?_
  show Continuous fun c : v.adicCompletion F =>
    Function.update (1 : (w : HeightOneSpectrum (𝓞 F)) → w.adicCompletion F) v c w
  by_cases hw : w = v
  · subst hw
    simp only [Function.update_self]
    exact continuous_id
  · simp only [Function.update_of_ne hw]
    exact continuous_const

open scoped Classical in
-- pin: localUnit_val_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:849)
theorem localUnit_val_eq (t : (v.adicCompletion F)ˣ) :
    ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F)
      = RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v) (finSinglePrincipal v (t : v.adicCompletion F)) :=
  RestrictedProduct.ext (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
    (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F))) fun _ => rfl

-- pin: continuous_localUnit_val (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:857)
theorem continuous_localUnit_val :
    Continuous fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F) := by
  have h : (fun t : (v.adicCompletion F)ˣ =>
      ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
      = (RestrictedProduct.inclusion (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletion F)
          (fun w : HeightOneSpectrum (𝓞 F) => (w.adicCompletionIntegers F : Set (w.adicCompletion F)))
          (cofinite_le_principal_compl_singleton v)) ∘ (finSinglePrincipal v) ∘ Units.val :=
    funext fun t => localUnit_val_eq v t
  rw [h]
  exact (RestrictedProduct.continuous_inclusion _).comp
    ((continuous_finSinglePrincipal v).comp Units.continuous_val)

-- pin: continuous_embUnit (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:870)
theorem continuous_embUnit : Continuous (embUnit (F := F) v) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)
  · have h : (fun t : (v.adicCompletion F)ˣ => (((embUnit v t)⁻¹ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F))
        = (fun t : (v.adicCompletion F)ˣ => ((embUnit v t : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F)) ∘
            (fun t => t⁻¹) := by
      funext t
      simp only [Function.comp_apply, map_inv]
    rw [h]
    refine Continuous.comp ?_ continuous_inv
    show Continuous fun t : (v.adicCompletion F)ˣ =>
      (((1 : InfiniteAdeleRing F), ((localUnit (𝓞 F) F v t : (FiniteAdeleRing (𝓞 F) F)ˣ) : FiniteAdeleRing (𝓞 F) F))
        : AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (continuous_localUnit_val v)

end EmbUnitContinuity

section Assembly2

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

-- pin: mem_unitsOutside_of_unitAtHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:895)
theorem mem_unitsOutside_of_unitAtHom {x : (AdeleRing (𝓞 F) F)ˣ}
    (h : ∀ v ∉ S, (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    x ∈ unitsOutside S := by
  rw [mem_unitsOutside_iff]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · show (unitAtHom v x : v.adicCompletion F) ∈ _
    exact (h v hv).1
  · show (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ _
    exact (h v hv).2

-- pin: mem_unitsOutside_of_unitAtHom_eq_one (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:906)
theorem mem_unitsOutside_of_unitAtHom_eq_one {x : (AdeleRing (𝓞 F) F)ˣ} (h : ∀ v ∉ S, unitAtHom v x = 1) :
    x ∈ unitsOutside S := by
  refine mem_unitsOutside_of_unitAtHom S fun v hv => ?_
  rw [h v hv, inv_one, Units.val_one]
  exact ⟨one_mem _, one_mem _⟩

-- pin: archAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:912)
def archAsm : (InfiniteAdeleRing F)ˣ →* (AdeleRing (𝓞 F) F)ˣ where
  toFun a :=
    { val := ((a : InfiniteAdeleRing F), 1)
      inv := (((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F), 1)
      val_inv := Prod.ext a.mul_inv (one_mul 1)
      inv_val := Prod.ext a.inv_mul (one_mul 1) }
  map_one' := Units.ext rfl
  map_mul' _ _ := Units.ext (Prod.ext rfl (one_mul 1).symm)

-- pin: archUnits_archAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:921)
theorem archUnits_archAsm (a : (InfiniteAdeleRing F)ˣ) : archUnits (archAsm (F := F) a) = a := Units.ext rfl

-- pin: unitAtHom_archAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:923)
theorem unitAtHom_archAsm (a : (InfiniteAdeleRing F)ˣ) (v : HeightOneSpectrum (𝓞 F)) :
    unitAtHom v (archAsm (F := F) a) = 1 :=
  Units.ext rfl

-- pin: continuous_archAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:927)
theorem continuous_archAsm : Continuous (archAsm (F := F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · show Continuous fun a : (InfiniteAdeleRing F)ˣ => (((a : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact Units.continuous_val.prodMk continuous_const
  · show Continuous fun a : (InfiniteAdeleRing F)ˣ =>
      ((((a⁻¹ : (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F), (1 : FiniteAdeleRing (𝓞 F) F)) : AdeleRing (𝓞 F) F)
    exact Units.continuous_coe_inv.prodMk continuous_const

-- pin: archAsm_mem_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:935)
theorem archAsm_mem_unitsOutside (a : (InfiniteAdeleRing F)ˣ) : archAsm (F := F) a ∈ unitsOutside S :=
  mem_unitsOutside_of_unitAtHom_eq_one S fun v _ => unitAtHom_archAsm a v

-- pin: sAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:938)
def sAsm : SUnits (F := F) S →* (AdeleRing (𝓞 F) F)ˣ where
  toFun t := ∏ v : S, embUnit v.1 (t v)
  map_one' := by simp only [Pi.one_apply, map_one, Finset.prod_const_one]
  map_mul' t t' := by simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]

-- pin: sAsm_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:943)
theorem sAsm_apply (t : SUnits (F := F) S) : sAsm S t = ∏ v : S, embUnit v.1 (t v) := rfl

-- pin: continuous_sAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:945)
theorem continuous_sAsm : Continuous (sAsm (F := F) S) := by
  show Continuous fun t : SUnits (F := F) S => ∏ v : S, embUnit v.1 (t v)
  exact continuous_finsetProd _ fun v _ => (continuous_embUnit v.1).comp (continuous_apply v)

-- pin: archUnits_sAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:949)
theorem archUnits_sAsm (t : SUnits (F := F) S) : archUnits (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun v _ => ?_
  exact Units.ext (embUnit_val_fst v.1 (t v))

-- pin: unitAtHom_sAsm_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:954)
theorem unitAtHom_sAsm_of_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (sAsm S t) = t ⟨v, hv⟩ := by
  rw [sAsm_apply, map_prod]
  rw [Finset.prod_eq_single (⟨v, hv⟩ : S)]
  · exact unitAtHom_embUnit_self v (t ⟨v, hv⟩)
  · intro w _ hw
    have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hw (Subtype.ext h)
    exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)
  · intro h
    exact absurd (Finset.mem_univ _) h

-- pin: unitAtHom_sAsm_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:965)
theorem unitAtHom_sAsm_of_not_mem (t : SUnits (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (sAsm S t) = 1 := by
  rw [sAsm_apply, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  have hwv : (w.1 : HeightOneSpectrum (𝓞 F)) ≠ v := fun h => hv (h ▸ w.2)
  exact unitAtHom_embUnit_of_ne (Ne.symm hwv) (t w)

-- pin: sAsm_mem_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:972)
theorem sAsm_mem_unitsOutside (t : SUnits (F := F) S) : sAsm S t ∈ unitsOutside S :=
  mem_unitsOutside_of_unitAtHom_eq_one S fun _ hv => unitAtHom_sAsm_of_not_mem S t hv

-- pin: Q (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:975)
abbrev Q : Type := (InfiniteAdeleRing F)ˣ × (SUnits (F := F) S × DeepUnits (F := F) S)

-- pin: asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:977)
def asm : Q (F := F) S →* (AdeleRing (𝓞 F) F)ˣ :=
  MonoidHom.coprod archAsm (MonoidHom.coprod (sAsm S) (deepAsm S))

-- pin: asm_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:980)
theorem asm_apply (q : Q (F := F) S) : asm S q = archAsm q.1 * (sAsm S q.2.1 * deepAsm S q.2.2) := rfl

-- pin: continuous_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:982)
theorem continuous_asm : Continuous (asm (F := F) S) := by
  show Continuous fun q : Q (F := F) S => archAsm q.1 * (sAsm S q.2.1 * deepAsm S q.2.2)
  exact (continuous_archAsm.comp continuous_fst).mul
    (((continuous_sAsm S).comp (continuous_fst.comp continuous_snd)).mul
      ((continuous_deepAsm S).comp (continuous_snd.comp continuous_snd)))

-- pin: asm_mem_unitsOutside (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:988)
theorem asm_mem_unitsOutside (q : Q (F := F) S) : asm S q ∈ unitsOutside S :=
  mul_mem (archAsm_mem_unitsOutside S q.1) (mul_mem (sAsm_mem_unitsOutside S q.2.1) (deepAsm_mem_unitsOutside S q.2.2))

-- pin: archUnits_deepAsm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:991)
theorem archUnits_deepAsm (o : DeepUnits (F := F) S) : archUnits (deepAsm S o) = 1 :=
  Units.ext (deepAsm_val_fst S o)

-- pin: archUnits_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:994)
theorem archUnits_asm (q : Q (F := F) S) : archUnits (asm S q) = q.1 := by
  rw [asm_apply, map_mul, map_mul, archUnits_archAsm, archUnits_sAsm, archUnits_deepAsm, mul_one, mul_one]

-- pin: unitAtHom_asm_of_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:997)
theorem unitAtHom_asm_of_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S) :
    unitAtHom v (asm S q) = q.2.1 ⟨v, hv⟩ := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_mem S q.2.2 hv, one_mul, mul_one]

-- pin: unitAtHom_asm_of_not_mem (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1002)
theorem unitAtHom_asm_of_not_mem (q : Q (F := F) S) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    unitAtHom v (asm S q) = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (q.2.2 ⟨v, hv⟩) := by
  rw [asm_apply, map_mul, map_mul, unitAtHom_archAsm, unitAtHom_sAsm_of_not_mem S q.2.1 hv,
    unitAtHom_deepAsm_of_not_mem S q.2.2 hv, one_mul, one_mul]

open scoped Classical in
-- pin: deepCoordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1008)
def deepCoordAt (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ :=
  if h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F then
    { val := ⟨(unitAtHom v x : v.adicCompletion F), h.1⟩
      inv := ⟨(((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), h.2⟩
      val_inv := Subtype.ext (unitAtHom v x).mul_inv
      inv_val := Subtype.ext (unitAtHom v x).inv_mul }
  else 1

open scoped Classical in
-- pin: deepCoordAt_spec (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1018)
theorem deepCoordAt_spec (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ)
    (h : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F) :
    Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v x) = unitAtHom v x := by
  refine Units.ext ?_
  show (((deepCoordAt v x : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : v.adicCompletion F) = _
  rw [deepCoordAt, dite_eq_left h]

-- pin: deepCoordAt_of_map (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1026)
theorem deepCoordAt_of_map (v : HeightOneSpectrum (𝓞 F)) (x : (AdeleRing (𝓞 F) F)ˣ) (o : (v.adicCompletionIntegers F)ˣ)
    (h : unitAtHom v x = Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom o) : deepCoordAt v x = o := by
  have hmem : (unitAtHom v x : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
      (((unitAtHom v x)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    rw [h, ← map_inv]
    exact ⟨SetLike.coe_mem _, SetLike.coe_mem _⟩
  have h2 := deepCoordAt_spec v x hmem
  rw [h] at h2
  refine Units.ext (Subtype.ext ?_)
  have h3 := congrArg (fun z : (v.adicCompletion F)ˣ => (z : v.adicCompletion F)) h2
  exact h3

-- pin: coord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1038)
def coord (x : (AdeleRing (𝓞 F) F)ˣ) : Q (F := F) S :=
  (archUnits x, (fun v => unitAtHom v.1 x, fun v => deepCoordAt v.1 x))

-- pin: coord_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1041)
theorem coord_asm (q : Q (F := F) S) : coord S (asm S q) = q := by
  obtain ⟨a, t, o⟩ := q
  refine Prod.ext (archUnits_asm S _) (Prod.ext (funext fun v => ?_) (funext fun v => ?_))
  · show unitAtHom v.1 (asm S (a, t, o)) = t v
    rw [unitAtHom_asm_of_mem S (a, t, o) v.2]
  · show deepCoordAt v.1 (asm S (a, t, o)) = o v
    exact deepCoordAt_of_map v.1 _ (o v) (unitAtHom_asm_of_not_mem S (a, t, o) v.2)

-- pin: asm_coord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1049)
theorem asm_coord {u : (AdeleRing (𝓞 F) F)ˣ} (hu : u ∈ unitsOutside S) : asm S (coord S u) = u := by
  refine idele_ext (archUnits_asm S _) fun v => ?_
  by_cases hv : v ∈ S
  · exact (unitAtHom_asm_of_mem S (coord S u) hv).trans rfl
  · rw [unitAtHom_asm_of_not_mem S _ hv]
    show Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom (deepCoordAt v u) = unitAtHom v u
    rw [mem_unitsOutside_iff] at hu
    refine deepCoordAt_spec v u ⟨?_, ?_⟩
    · exact hu.1 v hv
    · rw [← map_inv]; exact hu.2 v hv

-- pin: range_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1060)
theorem range_asm : Set.range (asm (F := F) S) = unitsOutside S := by
  ext u
  constructor
  · rintro ⟨q, rfl⟩; exact asm_mem_unitsOutside S q
  · intro hu; exact ⟨coord S u, asm_coord S hu⟩

-- pin: continuous_unitAtHom (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1066)
theorem continuous_unitAtHom (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitAtHom (F := F) v) :=
  Units.continuous_map ((continuous_finAdeleEval (𝓞 F) F v).comp (continuous_adeleFin (𝓞 F) F))

-- pin: continuous_archUnits (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1069)
theorem continuous_archUnits : Continuous (archUnits (F := F)) :=
  Units.continuous_map (continuous_adeleArch (𝓞 F) F)

-- pin: continuousOn_deepCoordAt (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1072)
theorem continuousOn_deepCoordAt {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) :
    ContinuousOn (deepCoordAt (F := F) v) (unitsOutside S) := by
  classical
  have key : ∀ u ∈ (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ),
      (unitAtHom v u : v.adicCompletion F) ∈ v.adicCompletionIntegers F ∧
        (((unitAtHom v u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) ∈ v.adicCompletionIntegers F := by
    intro u hu
    have hu' := (mem_unitsOutside_iff S u).mp hu
    refine ⟨hu'.1 v hv, ?_⟩
    rw [← map_inv]; exact hu'.2 v hv
  rw [continuousOn_iff_continuous_domRestrict]
  have c1 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F), (key u u.2).1⟩ : v.adicCompletionIntegers F) :=
    (Units.continuous_val.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  have c2 : Continuous fun u : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) =>
      (⟨(((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F), (key u u.2).2⟩ :
        v.adicCompletionIntegers F) :=
    (Units.continuous_coe_inv.comp ((continuous_unitAtHom v).comp continuous_subtype_val)).subtype_mk _
  refine Units.continuous_iff.mpr ⟨c1.congr fun u => ?_, c2.congr fun u => ?_⟩
  · refine Subtype.ext ?_
    show (unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ) : v.adicCompletion F)
      = (((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ) : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dite_eq_left (key u u.2)]
  · refine Subtype.ext ?_
    have e : ((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ)
        = (deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ := rfl
    show (((unitAtHom v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      = ((((deepCoordAt v (u : (AdeleRing (𝓞 F) F)ˣ))⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F)
          : v.adicCompletion F)
    rw [deepCoordAt, dite_eq_left (key u u.2)]
    rfl

-- pin: continuousOn_coord (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1105)
theorem continuousOn_coord : ContinuousOn (coord (F := F) S) (unitsOutside S) := by
  have h1 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => archUnits x) (unitsOutside S) :=
    continuous_archUnits.continuousOn
  have h2 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : S => unitAtHom v.1 x) (unitsOutside S) :=
    (continuous_pi fun v : S => continuous_unitAtHom (F := F) v.1).continuousOn
  have h3 : ContinuousOn (fun x : (AdeleRing (𝓞 F) F)ˣ => fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ S} =>
      deepCoordAt v.1 x) (unitsOutside S) :=
    continuousOn_pi.mpr fun v => continuousOn_deepCoordAt S v.2
  exact h1.prodMk (h2.prodMk h3)

-- pin: asmHomeo (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1115)
def asmHomeo : Q (F := F) S ≃ₜ (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ) where
  toFun q := ⟨asm S q, asm_mem_unitsOutside S q⟩
  invFun u := coord S u
  left_inv q := coord_asm S q
  right_inv u := Subtype.ext (asm_coord S u.2)
  continuous_toFun := (continuous_asm S).subtype_mk _
  continuous_invFun := continuousOn_iff_continuous_domRestrict.mp (continuousOn_coord S)

-- pin: isOpenEmbedding_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1123)
theorem isOpenEmbedding_asm : IsOpenEmbedding (asm (F := F) S) := by
  have h : (⇑(asm (F := F) S) : Q (F := F) S → (AdeleRing (𝓞 F) F)ˣ)
      = fun q : Q (F := F) S => ((asmHomeo S q : (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ)) : (AdeleRing (𝓞 F) F)ˣ) :=
    funext fun _ => rfl
  rw [h]
  exact (isOpen_unitsOutside S).isOpenEmbedding_subtypeVal.comp (asmHomeo S).isOpenEmbedding

end Assembly2

end NumberField.TateGlobal

end

end Fold_TateAssembly2

section Fold_TateAssembly3



noncomputable section

namespace NumberField
namespace TateGlobal

variable {F : Type} [Field F] [NumberField F]

section Pullback

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

variable [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ]

variable [MeasurableSpace (Q (F := F) S)] [BorelSpace (Q (F := F) S)]

-- pin: measurableEmbedding_asm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1167)
theorem measurableEmbedding_asm : MeasurableEmbedding (asm (F := F) S) :=
  (isOpenEmbedding_asm S).measurableEmbedding

-- pin: asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1170)
def asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) : Measure (Q (F := F) S) := ν.comap (asm S)

-- pin: asmMeasure_apply (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1172)
theorem asmMeasure_apply (ν : Measure (AdeleRing (𝓞 F) F)ˣ) (s : Set (Q (F := F) S)) :
    asmMeasure S ν s = ν (asm S '' s) :=
  (measurableEmbedding_asm S).comap_apply ν s

omit [MeasurableSpace (AdeleRing (𝓞 F) F)ˣ] [BorelSpace (AdeleRing (𝓞 F) F)ˣ] [MeasurableSpace (Q (F := F) S)]
  [BorelSpace (Q (F := F) S)] in
-- pin: image_preimage_mul_left (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1178)
theorem image_preimage_mul_left (g : Q (F := F) S) (A : Set (Q (F := F) S)) :
    asm S '' ((fun q => g * q) ⁻¹' A) = (fun x => asm S g * x) ⁻¹' (asm S '' A) := by
  ext x
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨g * q, hq, by rw [map_mul]⟩
  · rintro ⟨q', hq', hx⟩
    refine ⟨g⁻¹ * q', ?_, ?_⟩
    · show g * (g⁻¹ * q') ∈ A
      rwa [mul_inv_cancel_left]
    · apply mul_left_cancel (a := asm S g)
      rw [← map_mul, mul_inv_cancel_left, hx]

-- pin: isMulLeftInvariant_asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1191)
scoped instance isMulLeftInvariant_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsMulLeftInvariant] :
    (asmMeasure S ν).IsMulLeftInvariant := by
  refine (forall_measure_preimage_mul_iff _).mp fun g A _ => ?_
  rw [asmMeasure_apply, asmMeasure_apply, image_preimage_mul_left]
  exact measure_preimage_mul ν (asm S g) _

-- pin: isFiniteMeasureOnCompacts_asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1197)
scoped instance isFiniteMeasureOnCompacts_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [IsFiniteMeasureOnCompacts ν] :
    IsFiniteMeasureOnCompacts (asmMeasure S ν) := by
  refine ⟨fun K hK => ?_⟩
  rw [asmMeasure_apply]
  exact (hK.image (continuous_asm S)).measure_lt_top

-- pin: isOpenPosMeasure_asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1203)
scoped instance isOpenPosMeasure_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsOpenPosMeasure] :
    (asmMeasure S ν).IsOpenPosMeasure := by
  refine ⟨fun U hU hne => ?_⟩
  rw [asmMeasure_apply]
  exact ((isOpenEmbedding_asm S).isOpenMap U hU).measure_ne_zero ν (hne.image _)

-- pin: isHaarMeasure_asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1209)
scoped instance isHaarMeasure_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ) [ν.IsHaarMeasure] :
    (asmMeasure S ν).IsHaarMeasure where

-- pin: setIntegral_unitsOutside_eq_integral_asmMeasure (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1212)
theorem setIntegral_unitsOutside_eq_integral_asmMeasure (ν : Measure (AdeleRing (𝓞 F) F)ˣ)
    (G : (AdeleRing (𝓞 F) F)ˣ → ℂ) :
    ∫ x in (unitsOutside S : Set (AdeleRing (𝓞 F) F)ˣ), G x ∂ν = ∫ q, G (asm S q) ∂(asmMeasure S ν) := by
  rw [← range_asm S, ← (measurableEmbedding_asm S).map_comap ν]
  exact (measurableEmbedding_asm S).integral_map G

end Pullback

end NumberField.TateGlobal

end

end Fold_TateAssembly3

section Fold_LocalHaarModulus



open scoped NNReal ENNReal Pointwise

-- Chapter-prefix rename from the pin's `M4aLocalCFT.LocalHaarModulus` to
-- `NumberField.TateGlobal.LocalHaarModulus` (work order §3.1); the sub-namespace is kept.
namespace NumberField.TateGlobal

namespace LocalHaarModulus

noncomputable section

variable (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

-- pin: card_residueField_eq_absNorm (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1247)
theorem card_residueField_eq_absNorm :
    Nat.card (ResidueField (v.adicCompletionIntegers F)) = Ideal.absNorm v.asIdeal := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (HeightOneSpectrum.ResidueFieldEquivCompletionResidueField F v).toEquiv.symm

section CosetStep

variable {F v}

-- pin: exists_out_add_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1256)
theorem exists_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (Y : v.adicCompletionIntegers F) :
    ∃ z : v.adicCompletionIntegers F,
      Y = Quotient.out (residue (v.adicCompletionIntegers F) Y) + ϖ * z := by
  have hout : residue (v.adicCompletionIntegers F)
      (Quotient.out (residue (v.adicCompletionIntegers F) Y))
      = residue (v.adicCompletionIntegers F) Y := Quotient.out_eq _
  have hzero : residue (v.adicCompletionIntegers F)
      (Y - Quotient.out (residue (v.adicCompletionIntegers F) Y)) = 0 := by
    rw [map_sub, hout, sub_self]
  set w : v.adicCompletionIntegers F
      := Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) with hw
  have hmem : w ∈ maximalIdeal (v.adicCompletionIntegers F) :=
    Ideal.Quotient.eq_zero_iff_mem.mp hzero
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have hsub : Y - Quotient.out (residue (v.adicCompletionIntegers F) Y) = ϖ * z := by
    rw [← hw]; exact hz
  exact sub_eq_iff_eq_add'.mp hsub

-- pin: residue_out_add_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1277)
theorem residue_out_add_mul {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ)
    (k : ResidueField (v.adicCompletionIntegers F)) (z : v.adicCompletionIntegers F) :
    residue (v.adicCompletionIntegers F) (Quotient.out k + ϖ * z) = k := by
  have hϖ0 : residue (v.adicCompletionIntegers F) ϖ = 0 := by
    refine Ideal.Quotient.eq_zero_iff_mem.mpr ?_
    rw [hϖ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self ϖ
  have hout : residue (v.adicCompletionIntegers F) (Quotient.out k) = k := Quotient.out_eq _
  rw [map_add, map_mul, hϖ0, zero_mul, add_zero, hout]

-- pin: cosetMap (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1287)
abbrev cosetMap (ϖ : v.adicCompletionIntegers F)
    (k : ResidueField (v.adicCompletionIntegers F)) (y : v.adicCompletion F) :
    v.adicCompletion F :=
  ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
    + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * y

-- pin: integers_eq_iUnion_image (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1295)
theorem integers_eq_iUnion_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F)) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz⟩ := exists_out_add_mul hϖ (⟨y, hy⟩ : v.adicCompletionIntegers F)
    refine mem_iUnion.mpr ⟨residue (v.adicCompletionIntegers F) ⟨y, hy⟩, ?_⟩
    refine ⟨(z : v.adicCompletion F), z.2, ?_⟩
    have hco := congrArg
      (fun w : v.adicCompletionIntegers F => (w : v.adicCompletion F)) hz
    push_cast at hco
    exact hco.symm
  · intro hy
    obtain ⟨k, hk⟩ := mem_iUnion.mp hy
    obtain ⟨z, hz, hzy⟩ := hk
    obtain ⟨X, hXy⟩ : ∃ X : v.adicCompletionIntegers F, (X : v.adicCompletion F) = y :=
      ⟨Quotient.out k + ϖ * ⟨z, hz⟩, by push_cast; exact hzy⟩
    rw [← hXy]
    exact X.2

-- pin: pairwise_disjoint_image (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1319)
theorem pairwise_disjoint_image {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    Pairwise (Function.onFun Disjoint fun k : ResidueField (v.adicCompletionIntegers F) =>
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  intro k k' hkk'
  refine Set.disjoint_left.mpr fun y hy hy' => hkk' ?_
  obtain ⟨z, hz, hzy⟩ := hy
  obtain ⟨z', hz', hzy'⟩ := hy'
  have hKeq : ((Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F) :
      v.adicCompletion F)
      = ((Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :
          v.adicCompletion F) := by
    push_cast
    rw [show ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z = y from hzy,
        show ((Quotient.out k' : v.adicCompletionIntegers F) : v.adicCompletion F)
          + ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) * z' = y from hzy']
  have hAeq : (Quotient.out k + ϖ * ⟨z, hz⟩ : v.adicCompletionIntegers F)
      = (Quotient.out k' + ϖ * ⟨z', hz'⟩ : v.adicCompletionIntegers F) :=
    Subtype.coe_injective hKeq
  have := congrArg (residue (v.adicCompletionIntegers F)) hAeq
  rwa [residue_out_add_mul hϖ, residue_out_add_mul hϖ] at this

-- pin: cosetMap_image_eq (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1343)
theorem cosetMap_image_eq {ϖ : v.adicCompletionIntegers F}
    (k : ResidueField (v.adicCompletionIntegers F)) :
    cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
          (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  rw [← Set.image_vadd, ← Set.image_smul, ← Set.image_comp]
  rfl

end CosetStep

section Measure

variable {F v}

set_option linter.style.haveILetI false in
-- pin: measure_integers_eq_card_mul (S_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean:1361)
-- The `haveI : Fintype …` is a load-bearing instance argument for `tsum_fintype`.
theorem measure_integers_eq_card_mul [MeasurableSpace (v.adicCompletion F)]
    [BorelSpace (v.adicCompletion F)] (μ : Measure (v.adicCompletion F))
    [μ.IsAddHaarMeasure] {ϖ : v.adicCompletionIntegers F} (hϖ : Irreducible ϖ) :
    μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
  have hϖ0 : ((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) ≠ 0 := by
    simpa using (Subtype.coe_injective.ne_iff.mpr hϖ.ne_zero)
  have hTopen : IsOpen (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
      (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    (NumberField.isOpenAdicCompletionIntegers F v).smul₀ hϖ0
  have hTmeas := hTopen.measurableSet
  have hbridge : ∀ k : ResidueField (v.adicCompletionIntegers F),
      cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))
        = ((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    fun k => cosetMap_image_eq k
  calc μ (v.adicCompletionIntegers F : Set (v.adicCompletion F))
      = μ (⋃ k : ResidueField (v.adicCompletionIntegers F),
          cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        rw [← integers_eq_iUnion_image hϖ]
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (cosetMap ϖ k '' (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine measure_iUnion ?_ fun k => ?_
        · intro k k' hkk'
          exact pairwise_disjoint_image hϖ hkk'
        · rw [hbridge k]
          exact hTmeas.const_vadd _
    _ = ∑' k : ResidueField (v.adicCompletionIntegers F),
          μ (((Quotient.out k : v.adicCompletionIntegers F) : v.adicCompletion F) +ᵥ
            (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
              (v.adicCompletionIntegers F : Set (v.adicCompletion F)))) := by
        exact tsum_congr fun k => by rw [hbridge k]
    _ = ∑' _ : ResidueField (v.adicCompletionIntegers F),
          μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        refine tsum_congr fun k => ?_
        exact measure_vadd _ _ _
    _ = (Nat.card (ResidueField (v.adicCompletionIntegers F)) : ℝ≥0∞)
        * μ (((ϖ : v.adicCompletionIntegers F) : v.adicCompletion F) •
            (v.adicCompletionIntegers F : Set (v.adicCompletion F))) := by
        haveI : Fintype (ResidueField (v.adicCompletionIntegers F)) := Fintype.ofFinite _
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Nat.card_eq_fintype_card]

end Measure

-- the pin's `noncomputable section` (line 1243) is closed here, at the dispatch
-- boundary; the next dispatch re-opens `NumberField.TateGlobal`.
end

end LocalHaarModulus

end NumberField.TateGlobal

end Fold_LocalHaarModulus

