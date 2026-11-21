/-
  The Borel set integral is the Petersson integral times the Bruhat–Eisenstein factor.

  For a function `f` on `GL₂(𝔸)`, the integral of `f` over the Borel subgroup `B(𝔸)`-orbit of a
  fundamental domain for the principal ideles — the "Borel set" of the adelic unfolding — equals
  the Petersson integral of its archimedean section against the Bruhat–Eisenstein factor. The
  content is a fundamental-domain computation: the Borel set is a disjoint union of the translates
  `g⁻¹ · D` of one fundamental domain `D` over a set of left-coset representatives, so its integral
  is the sum of the integrals over those translates, and the Bruhat representative of each coset
  turns the sum into the Petersson pairing against the Eisenstein factor.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein.lean

## Port deltas

* **Where the engines live.** The pin opens a root namespace `RS11C9A` for its engine and states the
  row at the root; here the row keeps its published name at `AutomorphicForm` and the engine is
  transcribed into `AutomorphicForm.BorelUnfolding` (the set's naming rule: the pipeline label becomes
  the subject). The nesting is required, not cosmetic: the port already publishes
  `AutomorphicForm.slab` and `AutomorphicForm.measurableSet_slab` (`PeterssonSlabPairing`,
  `PeterssonSkewAdjunction`) and `AutomorphicForm.globalPoints_injective`
  (`RationalUnipotentQuotientIntegral`), so a second public copy at `AutomorphicForm` would make the
  modules unimportable together (FR-0259). Both gates key rows by last name, so every row reads `ok`.
* **The row is inside `open BorelUnfolding`.** The pin writes `open RS11C9A in theorem solution …`, and
  the same is needed here: the pin's `scoped instance`s (`countable_numberField`, `countable_matrix`,
  `countable_gl2`, the four `SMulInvariantMeasure`s) are what make the row's
  `IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives` application elaborate. The `open`
  is a plain command before the row, not an `open … in`, so the row's statement text is the pin's.
* **`countable_range` stays a `private scoped instance` at the pin's own name and visibility**, so
  both gates skip it (FR-0242) and it is an instance, so `move_dead` reads `0/0` (FR-0243); it is also
  why the corpus parser reads 26 declarations on each side rather than 27 (FR-0243: a `private scoped
  instance` is invisible to `lean_parser.DECL_RE`). It is live only because the row is inside
  `open BorelUnfolding`.
* **One local `have` differs from the pin's.** The pin closes
  `have hScap : (S ∩ Sd) =ᵐ 𝓕` by `rwa [hS₀cap] at h`; at v4.34 the `Sd` abbreviation has been
  delta-reduced inside `ae_eq_refl`'s result, so the rewrite's pattern no longer matches syntactically.
  The module states the same identity as `h2 : ((𝓕 ∪ (D \ Sd)) ∩ Sd) =ᵐ[μG] 𝓕` and closes with
  `h.trans h2`. Body-only: no declaration statement is involved.
* **Imports added to the scaffold's list**, each because elaboration asked for it and never as a bare
  `Mathlib`: `AutomorphicForm/Adelic/GlobalPointsDomain.lean`
  (`exists_isFundamentalDomain_globalPoints_range`, which the row's `obtain` needs and which is
  declared there with a dotted `AutomorphicForm.`-qualified name, so a plain grep for the bare name
  misses it), `NumberTheory/NumberField/TateGlobalIdeleNormDet.lean`,
  `NumberTheory/NumberField/TateGlobalContinuousIdeleNorm.lean`,
  `AutomorphicForm/Adelic/IdeleNormDet.lean`.
* **The pin's `attribute [-instance]` block is not carried** (it names pin-prelude instances the port
  lacks; an `attribute` on an unknown name is a hard error). The pin's `attribute [local instance]
  ratAction` **is** carried: it names a declaration of this module.
* **Deprecation cures on the pin's body text, statement-neutral**: `Set.mem_setOf_eq`→`Set.mem_ofPred_eq`,
  `Set.diff_eq_empty`→`Set.sdiff_eq_empty`, `Set.diff_subset`→`Set.sdiff_subset`,
  `ofReal_norm_eq_enorm`→`ofReal_norm`, `Measurable.ennreal_tsum`→`Measurable.tsum`, one
  `simpa using hasSum_fintype`→`simp`.
* **One scoped linter suppression.** The row's proof installs a `MeasurableSpace`, a `MulAction` and
  two Prop-valued instances by `letI`/`haveI`; the linter's `let`/`have` drop them (FR-0262), so
  `set_option linter.style.haveILetI false in` is scoped to the row alone — the precedent of
  `RepTheory/TypeReproducer.lean`. No `maxHeartbeats` option is involved.

## Heartbeat probe (recorded, never installed — FR-0225)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/BorelFundamentalDomain.lean`
is **silent at N = 60 000** and **fails at N = 30 000** (= N/2), at `(deterministic) timeout at whnf`
on `globalPoints_mul_mem_slab_iff` / `preimage_slab`. No `set_option maxHeartbeats` is in this module.

## Gates

* `check_port --force`: **26 ok, 0 mismatch, 0 missing, 0 own**.
* `scaffold_audit.py`: **complete** (26 pin public declarations on the wire, 27 port declarations).
* silence: `lake env lean -DautoImplicit=false` prints nothing; one `lake build` of the module succeeds.
* `#print axioms` on all 33 public declarations: `[propext, Classical.choice, Quot.sound]`, all 33.
* `dedup.py --within --module BorelFundamentalDomain`: **0 clusters**.
* `move_dead.py --source … --target /dev/null --dry-run`: **0 declarations, 0 lines**.
-/


import FLTForHuman.AutomorphicForm.Adelic.BruhatRepresentative
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.DetNormSlabFundamentalDomain
import FLTForHuman.MeasureTheory.IsFundamentalDomainCosets
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.AutomorphicForm.Adelic.PeterssonSlabPairing
import FLTForHuman.AutomorphicForm.Adelic.BruhatEisenstein
import FLTForHuman.AutomorphicForm.Adelic.GlobalPointsDomain
import FLTForHuman.NumberTheory.NumberField.TateGlobalIdeleNormDet
import FLTForHuman.NumberTheory.NumberField.TateGlobalContinuousIdeleNorm
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDet

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicBox NumberField.AdelicLevel
open IsDedekindDomain NumberField.TateGlobal
open AutomorphicForm
open scoped NNReal Pointwise ENNReal
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
  NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel

namespace AutomorphicForm

namespace BorelUnfolding

open scoped Pointwise ENNReal

variable (F : Type) [Field F] [NumberField F]

scoped instance countable_numberField : Countable F :=
  (Module.finBasis ℚ F).equivFun.toEquiv.injective.countable

scoped instance countable_matrix : Countable (Matrix (Fin 2) (Fin 2) F) :=
  inferInstanceAs (Countable (Fin 2 → Fin 2 → F))

scoped instance countable_gl2 : Countable (Matrix.GeneralLinearGroup (Fin 2) F) :=
  Units.val_injective.countable

@[reducible] def mGL : MeasurableSpace (Matrix.GeneralLinearGroup (Fin 2) F) := ⊤

@[reducible] def ratAction : MulAction (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F) :=
  MulAction.compHom _ (globalPoints (𝓞 F) F)

attribute [local instance] ratAction

theorem rat_smul_def (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    γ • g = globalPoints (𝓞 F) F γ * g := rfl

set_option linter.style.haveILetI false in
theorem measurableSMul_rat : @MeasurableSMul (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F) _ (mGL F) _ := by
  letI := mGL F
  exact
    { measurable_const_smul := fun γ => by
        show Measurable fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g
        exact measurable_const_mul _
      measurable_smul_const := fun g => measurable_from_top }

scoped instance smulInvariant_rat : SMulInvariantMeasure (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F)
    (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' s) = _
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (globalPoints (𝓞 F) F γ) s

def slab (d₁ d₂ : ℝ) : Set (AdelicGL2 (𝓞 F) F) :=
  {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}

theorem measurableSet_slab (d₁ d₂ : ℝ) : MeasurableSet (slab F d₁ d₂) :=
  NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc F d₁ d₂

theorem globalPoints_mul_mem_slab_iff {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F) :
    globalPoints (𝓞 F) F γ * g ∈ slab F d₁ d₂ ↔ g ∈ slab F d₁ d₂ := by
  simp only [slab, Set.mem_ofPred_eq, map_mul, NumberField.TateGlobal.ideleNorm_mul,
    AutomorphicForm.ideleNorm_det_globalPoints, one_mul]

theorem preimage_slab {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F) :
    (fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' slab F d₁ d₂ = slab F d₁ d₂ := by
  ext g; exact globalPoints_mul_mem_slab_iff F γ g

scoped instance smulInvariant_rat_restrict (d₁ d₂ : ℝ) :
    SMulInvariantMeasure (Matrix.GeneralLinearGroup (Fin 2) F) (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  have hs' : MeasurableSet ((fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' s) :=
    (measurable_const_mul (globalPoints (𝓞 F) F γ)) hs
  show (adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂) ((fun g => globalPoints (𝓞 F) F γ * g) ⁻¹' s) = _
  rw [Measure.restrict_apply hs', Measure.restrict_apply hs]
  have hset : (fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' s ∩ slab F d₁ d₂ =
      (fun g : AdelicGL2 (𝓞 F) F => globalPoints (𝓞 F) F γ * g) ⁻¹' (s ∩ slab F d₁ d₂) := by
    rw [Set.preimage_inter, preimage_slab F γ]
  rw [hset]
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (globalPoints (𝓞 F) F γ) (s ∩ slab F d₁ d₂)

scoped instance smulInvariant_range_restrict (d₁ d₂ : ℝ) :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F)
      ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)) := by
  refine ⟨fun γ s hs => ?_⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  have := (smulInvariant_rat_restrict F d₁ d₂).measure_preimage_smul γ₀ hs
  have hγ : (fun g : AdelicGL2 (𝓞 F) F => γ • g) = fun g => γ₀ • g := by
    funext g
    show (γ : AdelicGL2 (𝓞 F) F) * g = globalPoints (𝓞 F) F γ₀ * g
    rw [hγ₀]
  rw [hγ]
  exact this

theorem globalPoints_injective : Function.Injective (globalPoints (𝓞 F) F) := by
  intro a b h
  apply Units.ext
  ext i j
  have hij := congrArg (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j) h
  simp only [globalPoints, Matrix.GeneralLinearGroup.map_apply] at hij
  exact NumberField.AdeleRing.algebraMap_injective (𝓞 F) F hij

theorem isFundamentalDomain_top_of_range {S : Set (AdelicGL2 (𝓞 F) F)} {μ : Measure (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S μ) :
    IsFundamentalDomain (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) S μ := by
  have hinj := globalPoints_injective F
  let e : (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) ≃ (globalPoints (𝓞 F) F).range :=
    Subgroup.topEquiv.toEquiv.trans (MonoidHom.ofInjective hinj).toEquiv
  have h := hS.image_of_equiv (ν := μ) (Equiv.refl _)
    (by exact (MeasurePreserving.id μ).quasiMeasurePreserving) e (fun γ g => ?_)
  · simpa using h
  · show ((MonoidHom.ofInjective hinj (Subgroup.topEquiv γ) : (globalPoints (𝓞 F) F).range) : AdelicGL2 (𝓞 F) F) * g =
      globalPoints (𝓞 F) F (γ : Matrix.GeneralLinearGroup (Fin 2) F) * g
    rw [MonoidHom.ofInjective_apply]
    rfl

theorem isFundamentalDomain_map_of {Q : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)}
    {S : Set (AdelicGL2 (𝓞 F) F)} {μ : Measure (AdelicGL2 (𝓞 F) F)}
    (hS : IsFundamentalDomain Q S μ) :
    IsFundamentalDomain (Q.map (globalPoints (𝓞 F) F)) S μ := by
  have hinj := globalPoints_injective F
  let e : Q.map (globalPoints (𝓞 F) F) ≃ Q := (Subgroup.equivMapOfInjective Q _ hinj).symm.toEquiv
  have h := hS.image_of_equiv (ν := μ) (Equiv.refl _)
    (by exact (MeasurePreserving.id μ).quasiMeasurePreserving) e (fun γ g => ?_)
  · simpa using h
  · show globalPoints (𝓞 F) F (((Subgroup.equivMapOfInjective Q _ hinj).symm γ : Q) : Matrix.GeneralLinearGroup (Fin 2) F) * g =
      (γ : AdelicGL2 (𝓞 F) F) * g
    congr 1
    have h1 := Subgroup.coe_equivMapOfInjective_apply Q (globalPoints (𝓞 F) F) hinj
      ((Subgroup.equivMapOfInjective Q _ hinj).symm γ)
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm

theorem isFundamentalDomain_restrict {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]
    {s : Set X} {μ : Measure X} (h : IsFundamentalDomain G s μ) (t : Set X) :
    IsFundamentalDomain G s (μ.restrict t) :=
  ⟨h.nullMeasurableSet.mono_ac (Measure.absolutelyContinuous_of_le Measure.restrict_le_self),
    ae_restrict_of_ae h.ae_covers,
    fun a b hab => by
      have h0 := h.aedisjoint hab
      unfold AEDisjoint at h0 ⊢
      exact le_antisymm ((Measure.le_iff'.mp Measure.restrict_le_self _).trans h0.le) bot_le⟩

private scoped instance countable_range : Countable (globalPoints (𝓞 F) F).range := by
  have h : Countable (Set.range (globalPoints (𝓞 F) F)) := (Set.countable_range _).to_subtype
  exact h


scoped instance smulInvariant_range :
    SMulInvariantMeasure (globalPoints (𝓞 F) F).range (AdelicGL2 (𝓞 F) F) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  refine ⟨fun γ s hs => ?_⟩
  show adelicGLHaar (Fin 2) (𝓞 F) F ((fun g => (γ : AdelicGL2 (𝓞 F) F) * g) ⁻¹' s) = _
  exact measure_preimage_mul (adelicGLHaar (Fin 2) (𝓞 F) F) (γ : AdelicGL2 (𝓞 F) F) s

theorem smul_slab_subset {d₁ d₂ : ℝ} (γ : (globalPoints (𝓞 F) F).range) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : A ⊆ slab F d₁ d₂) : γ • A ⊆ slab F d₁ d₂ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  show (γ : AdelicGL2 (𝓞 F) F) * a ∈ slab F d₁ d₂
  rw [← hγ₀]
  exact (globalPoints_mul_mem_slab_iff F γ₀ a).mpr (hA ha)

theorem smul_compl_slab_subset {d₁ d₂ : ℝ} (γ : (globalPoints (𝓞 F) F).range) {A : Set (AdelicGL2 (𝓞 F) F)}
    (hA : A ⊆ (slab F d₁ d₂)ᶜ) : γ • A ⊆ (slab F d₁ d₂)ᶜ := by
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨γ₀, hγ₀⟩ := γ.2
  show (γ : AdelicGL2 (𝓞 F) F) * a ∉ slab F d₁ d₂
  rw [← hγ₀, globalPoints_mul_mem_slab_iff F γ₀ a]
  exact hA ha

theorem isFundamentalDomain_union_slab {d₁ d₂ : ℝ} {𝓕 D : Set (AdelicGL2 (𝓞 F) F)}
    (h𝓕s : 𝓕 ⊆ slab F d₁ d₂)
    (h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕 ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict (slab F d₁ d₂)))
    (hD : IsFundamentalDomain (globalPoints (𝓞 F) F).range D (adelicGLHaar (Fin 2) (𝓞 F) F)) :
    IsFundamentalDomain (globalPoints (𝓞 F) F).range (𝓕 ∪ (D \ slab F d₁ d₂)) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  set μ := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  set Sd := slab F d₁ d₂ with hSd
  have hSdm : MeasurableSet Sd := measurableSet_slab F d₁ d₂

  have h𝓕nm : NullMeasurableSet 𝓕 μ := by
    obtain ⟨t, ht_sub, htm, hteq⟩ := h𝓕.nullMeasurableSet.exists_measurable_subset_ae_eq

    have h0 : μ.restrict Sd (𝓕 \ t) = 0 := (ae_eq_set.mp hteq.symm).1
    have h0' : μ (𝓕 \ t) = 0 := by
      have hsub : 𝓕 \ t ⊆ Sd := fun x hx => h𝓕s hx.1
      rwa [Measure.restrict_apply' hSdm, Set.inter_eq_self_of_subset_left hsub] at h0
    have hae : (t : Set _) =ᵐ[μ] 𝓕 := by
      rw [ae_eq_set]
      refine ⟨?_, h0'⟩
      rw [Set.sdiff_eq_empty.mpr ht_sub]; exact measure_empty
    exact htm.nullMeasurableSet.congr hae
  refine ⟨h𝓕nm.union (hD.nullMeasurableSet.diff hSdm.nullMeasurableSet), ?_, ?_⟩
  ·
    have h1 : ∀ᵐ x ∂μ, x ∈ Sd → ∃ γ : (globalPoints (𝓞 F) F).range, γ • x ∈ 𝓕 := by
      rw [← ae_restrict_iff' hSdm]
      exact h𝓕.ae_covers
    filter_upwards [h1, hD.ae_covers] with x hx1 hx2
    by_cases hx : x ∈ Sd
    · obtain ⟨γ, hγ⟩ := hx1 hx
      exact ⟨γ, Or.inl hγ⟩
    · obtain ⟨γ, hγ⟩ := hx2
      refine ⟨γ, Or.inr ⟨hγ, ?_⟩⟩
      have := smul_compl_slab_subset F γ (A := {x}) (by simpa using hx)
      exact this (Set.smul_mem_smul_set rfl)
  ·
    intro a b hab
    have hF := h𝓕.aedisjoint hab
    have hDd := hD.aedisjoint hab
    simp only [Function.onFun] at hF hDd ⊢
    rw [Set.smul_set_union, Set.smul_set_union]
    refine AEDisjoint.union_left ?_ ?_ <;> refine AEDisjoint.union_right ?_ ?_
    ·
      unfold AEDisjoint at hF ⊢
      have hsub : a • 𝓕 ∩ b • 𝓕 ⊆ Sd := fun x hx => smul_slab_subset F a h𝓕s hx.1
      rwa [Measure.restrict_apply' hSdm, Set.inter_eq_self_of_subset_left hsub] at hF
    ·
      refine (Set.disjoint_iff_inter_eq_empty.mpr ?_).aedisjoint
      ext x; constructor
      · rintro ⟨hx1, hx2⟩
        exact (smul_compl_slab_subset F b (A := D \ Sd) (fun x hx => hx.2) hx2) (smul_slab_subset F a h𝓕s hx1)
      · intro hx; exact hx.elim
    · refine (Set.disjoint_iff_inter_eq_empty.mpr ?_).aedisjoint
      ext x; constructor
      · rintro ⟨hx1, hx2⟩
        exact (smul_compl_slab_subset F a (A := D \ Sd) (fun x hx => hx.2) hx1) (smul_slab_subset F b h𝓕s hx2)
      · intro hx; exact hx.elim
    · exact measure_mono_null (Set.inter_subset_inter (Set.smul_set_mono Set.sdiff_subset) (Set.smul_set_mono Set.sdiff_subset)) hDd

theorem isFundamentalDomain_of_ae_eq {G α : Type*} [Group G] [Countable G] [MulAction G α] [MeasurableSpace α]
    [MeasurableSpace G] [MeasurableSMul G α] {μ : Measure α} [SMulInvariantMeasure G α μ] {s t : Set α}
    (hs : IsFundamentalDomain G s μ) (hst : s =ᵐ[μ] t) (ht : NullMeasurableSet t μ) :
    IsFundamentalDomain G t μ := by
  have hg : ∀ g : G, g • s =ᵐ[μ] g • t := fun g => by
    have := ((measurePreserving_smul g⁻¹ μ).quasiMeasurePreserving).preimage_ae_eq hst
    rwa [Set.preimage_smul_inv, Set.preimage_smul_inv] at this
  refine ⟨ht, ?_, ?_⟩
  · have h1 := hs.ae_covers
    have h2 : ∀ᵐ x ∂μ, ∀ g : G, x ∈ g⁻¹ • s ↔ x ∈ g⁻¹ • t := by
      rw [ae_all_iff]
      intro g
      exact (hg g⁻¹).mem_iff
    filter_upwards [h1, h2] with x hx1 hx2
    obtain ⟨g, hgx⟩ := hx1
    refine ⟨g, ?_⟩
    have := (hx2 g).1 (Set.mem_inv_smul_set_iff.mpr hgx)
    exact Set.mem_inv_smul_set_iff.mp this
  · intro a b hab
    have hs' := hs.aedisjoint hab
    exact hs'.congr (hg a).symm (hg b).symm

theorem hasSum_option {M ι : Type*} [AddCommMonoid M] [TopologicalSpace M] [ContinuousAdd M]
    (g : Option ι → M) {a : M} (h : HasSum (fun i => g (some i)) a) : HasSum g (g none + a) := by
  set e := Equiv.optionEquivSumPUnit.{0} ι with he
  have h1 : HasSum ((g ∘ e.symm) ∘ Sum.inl) a := by
    have : ((g ∘ e.symm) ∘ Sum.inl) = fun i => g (some i) := by
      funext i; simp [he]
    rw [this]; exact h
  have h2 : HasSum ((g ∘ e.symm) ∘ Sum.inr) (g none) := by
    have : ((g ∘ e.symm) ∘ Sum.inr) = fun _ => g none := by
      funext u; simp [he]
    rw [this]
    simp
  have h3 := h1.sum h2
  rw [add_comm] at h3
  exact (e.symm.hasSum_iff).mp h3

theorem tsum_option_ennreal {ι : Type*} (g : Option ι → ℝ≥0∞) : ∑' o, g o = g none + ∑' i, g (some i) :=
  (hasSum_option g ENNReal.summable.hasSum).tsum_eq

theorem globalPoints_unipotentGL2 (β : F) :
    globalPoints (𝓞 F) F (unipotentGL2 β) = unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β) := by
  apply Units.ext
  ext i j
  rw [globalPoints_apply, unipotentGL2_coe, unipotentGL2_coe]
  fin_cases i <;> fin_cases j <;> simp

theorem globalPoints_bruhat (ξ : F) :
    globalPoints (𝓞 F) F ((gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ) =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  rw [map_mul, globalPoints_unipotentGL2]; rfl

theorem enorm_coe_real_of_nonneg {r : ℝ} (hr : 0 ≤ r) : ‖(r : ℂ)‖ₑ = ENNReal.ofReal r := by
  rw [enorm_eq_nnnorm, Complex.nnnorm_real, ← enorm_eq_nnnorm, Real.enorm_eq_ofReal hr]

theorem mul_le_sq_add_sq (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := mul_le_mul_left h b
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := mul_le_mul_right h a
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem ofReal_sq_norm (z : ℂ) : ENNReal.ofReal (‖z‖ ^ 2) = ‖z‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem indicator_comp_globalPoints_mul {β : Type*} [Zero β] {d₁ d₂ : ℝ} (γ : Matrix.GeneralLinearGroup (Fin 2) F)
    (f : AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    (slab F d₁ d₂).indicator f (globalPoints (𝓞 F) F γ * g) =
      (slab F d₁ d₂).indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g := by
  by_cases hg : g ∈ slab F d₁ d₂
  · rw [Set.indicator_of_mem hg, Set.indicator_of_mem ((globalPoints_mul_mem_slab_iff F γ g).mpr hg)]
  · rw [Set.indicator_of_notMem hg,
      Set.indicator_of_notMem (fun h => hg ((globalPoints_mul_mem_slab_iff F γ g).mp h))]

theorem tsum_indicator_const_set {ι β : Type*} [AddCommMonoid β] [TopologicalSpace β] (s : Set (AdelicGL2 (𝓞 F) F))
    (f : ι → AdelicGL2 (𝓞 F) F → β) (g : AdelicGL2 (𝓞 F) F) :
    ∑' i, s.indicator (f i) g = s.indicator (fun g => ∑' i, f i g) g := by
  by_cases hg : g ∈ s
  · simp only [Set.indicator_of_mem hg]
  · simp only [Set.indicator_of_notMem hg, tsum_zero]


end BorelUnfolding

open BorelUnfolding

-- The pin installs a `MeasurableSpace`, a `MulAction` and two Prop-valued instances in the proof;
-- the linter's `let`/`have` do not register them (FR-0262), so the linter is off for this row only.
set_option linter.style.haveILetI false in
theorem exists_isFundamentalDomain_borel_setIntegral_eq_peterssonIntegral_mul_bruhatEisenstein
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμF : IsIdeleClassChar (𝓞 F) F μ) (_hνF : IsIdeleClassChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ)
      (_hφsum : ∀ g : AdelicGL2 (𝓞 F) F, Summable fun ξ : F =>
        ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖)
      (x y : AdelicGL2 (𝓞 F) F → ℂ)
      (_hxG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        x (globalPoints (𝓞 F) F γ * g) = x g)
      (_hyG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
        y (globalPoints (𝓞 F) F γ * g) = y g)
      (_hxc : Continuous x) (_hyc : Continuous y)
      (w d₁ d₂ : ℝ) (_hd₁ : 0 < d₁) (_hd : d₁ < d₂)
      (𝓕 : Set (AdelicGL2 (𝓞 F) F))
      (_h𝓕s : 𝓕 ⊆ {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂})
      (_h𝓕 : IsFundamentalDomain (globalPoints (𝓞 F) F).range 𝓕
        ((adelicGLHaar (Fin 2) (𝓞 F) F).restrict
          {g | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}))
      (_hintx : IntegrableOn (fun g => ‖x g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F))
      (_hinty : IntegrableOn (fun g => ‖y g‖ ^ 2 *
          (‖φ g‖ + ∑' ξ : F, ‖φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖) *
          ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w)) 𝓕 (adelicGLHaar (Fin 2) (𝓞 F) F)),
    ∃ 𝓕B : Set (AdelicGL2 (𝓞 F) F), MeasurableSet 𝓕B ∧
      IsFundamentalDomain ((borelSubgroup F).map (globalPoints (𝓞 F) F)) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      IntegrableOn (fun g : AdelicGL2 (𝓞 F) F =>
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) 𝓕B (adelicGLHaar (Fin 2) (𝓞 F) F) ∧
      ∫ g in 𝓕B,
        ({g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
            (fun _ => (1 : ℂ)) g) *
          (x g * φ g * (starRingEnd ℂ) (y g) *
            ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ)) ∂(adelicGLHaar (Fin 2) (𝓞 F) F) =
        peterssonIntegral F w 𝓕
          (fun g => x g * (φ g + ∑' ξ : F, φ (adelicWeyl (𝓞 F) F *
            unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g))) y ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖x g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤ ∧
      ∫⁻ g in 𝓕B,
        {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂}.indicator
          (fun g => ENNReal.ofReal (‖y g‖ ^ 2 * ‖φ g‖ * ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w))) g
          ∂(adelicGLHaar (Fin 2) (𝓞 F) F) < ⊤
  := by
  intro α hα μc νc hμF hνF s φ hφ hφc hφsum x y hxG hyG hxc hyc w d₁ d₂ hd₁ hd 𝓕 h𝓕s h𝓕 hintx hinty
  haveI := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  letI := BorelUnfolding.ratAction F
  letI := BorelUnfolding.mGL F
  haveI := BorelUnfolding.measurableSMul_rat F

  set μG := adelicGLHaar (Fin 2) (𝓞 F) F with hμG
  have hSd : {g : AdelicGL2 (𝓞 F) F | ideleNorm F (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc d₁ d₂} =
      BorelUnfolding.slab F d₁ d₂ := rfl
  rw [hSd] at h𝓕s h𝓕 ⊢
  set Sd := BorelUnfolding.slab F d₁ d₂ with hSd'
  have hSdm : MeasurableSet Sd := BorelUnfolding.measurableSet_slab F d₁ d₂

  obtain ⟨D, hD⟩ := AutomorphicForm.exists_isFundamentalDomain_globalPoints_range F
  have hS₀ := BorelUnfolding.isFundamentalDomain_union_slab F h𝓕s h𝓕 hD
  obtain ⟨S, hSsub, hSm, hSeq⟩ := hS₀.nullMeasurableSet.exists_measurable_subset_ae_eq
  have hS : IsFundamentalDomain (globalPoints (𝓞 F) F).range S μG :=
    BorelUnfolding.isFundamentalDomain_of_ae_eq hS₀ hSeq.symm hSm.nullMeasurableSet
  have hStop := BorelUnfolding.isFundamentalDomain_top_of_range F hS
  have hS₀cap : (𝓕 ∪ (D \ Sd)) ∩ Sd = 𝓕 := by
    ext g; constructor
    · rintro ⟨hg | hg, hgS⟩
      · exact hg
      · exact absurd hgS hg.2
    · intro hg; exact ⟨Or.inl hg, h𝓕s hg⟩
  have hScap : (S ∩ Sd : Set _) =ᵐ[μG] 𝓕 := by
    have h := hSeq.inter (ae_eq_refl Sd)
    have h2 : ((𝓕 ∪ (D \ Sd)) ∩ Sd : Set _) =ᵐ[μG] 𝓕 := by rw [hS₀cap]
    exact h.trans h2

  let c : Option F → Matrix.GeneralLinearGroup (Fin 2) F :=
    fun o => o.elim 1 fun ξ => (gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ
  let R : Option F → (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)) := fun o => ⟨(c o)⁻¹, trivial⟩
  have hRc : ∀ o, ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) = c o := fun o => inv_inv _
  have hR : ∀ γ : (⊤ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F)),
      ∃! o, ((R o)⁻¹ * γ : Matrix.GeneralLinearGroup (Fin 2) F) ∈ borelSubgroup F := by
    intro γ
    have h := AutomorphicForm.existsUnique_bruhatRepresentative_mul_mem_borelSubgroup F γ
    simpa only [Subgroup.coe_inv, hRc] using h
  set 𝓕B : Set (AdelicGL2 (𝓞 F) F) := ⋃ o, ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • S with h𝓕B
  have hFD : IsFundamentalDomain (borelSubgroup F) 𝓕B μG :=
    MeasureTheory.IsFundamentalDomain.iUnion_inv_smul_of_leftCosetRepresentatives
      μG ⊤ (borelSubgroup F) le_top S hStop R hR
  have hFDmap := BorelUnfolding.isFundamentalDomain_map_of F hFD
  have h𝓕Bm : MeasurableSet 𝓕B := by
    refine MeasurableSet.iUnion fun o => ?_
    rw [← Set.preimage_smul_inv]
    exact (measurable_const_smul _) hSm
  refine ⟨𝓕B, h𝓕Bm, hFDmap, ?_⟩

  set ω : AdelicGL2 (𝓞 F) F → ℝ := fun g => ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) with hω
  have hωpos : ∀ g, 0 < ω g := fun g => Real.rpow_pos_of_pos (NumberField.TateGlobal.ideleNorm_pos _) _
  have hωc : Continuous ω :=
    (NumberField.TateGlobal.continuous_ideleNorm_det F).rpow_const fun _ =>
      Or.inl (NumberField.TateGlobal.ideleNorm_pos _).ne'
  have hωG : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F),
      ω (globalPoints (𝓞 F) F γ * g) = ω g := by
    intro γ g
    simp only [hω, map_mul, NumberField.TateGlobal.ideleNorm_mul, AutomorphicForm.ideleNorm_det_globalPoints, one_mul]
  set Ew : AdelicGL2 (𝓞 F) F → ℂ := fun g => φ g + ∑' ξ : F,
    φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g) with hEw
  set Eb : AdelicGL2 (𝓞 F) F → ℝ := fun g => ‖φ g‖ + ∑' ξ : F,
    ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ with hEb
  set Ebe : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ‖φ g‖ₑ + ∑' ξ : F,
    ‖φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)‖ₑ with hEbe
  have hEbe_eq : ∀ g, Ebe g = ENNReal.ofReal (Eb g) := by
    intro g
    rw [hEbe, hEb]; dsimp only
    rw [ENNReal.ofReal_add (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _), ofReal_norm,
      ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hφsum g)]
    simp only [ofReal_norm]
  set Q : AdelicGL2 (𝓞 F) F → ℂ := fun g => x g * φ g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ) with hQ
  have hQc : Continuous Q :=
    ((hxc.mul hφc).mul (Complex.continuous_conj.comp hyc)).mul (Complex.continuous_ofReal.comp hωc)

  have hk₁ : (fun g : AdelicGL2 (𝓞 F) F => Sd.indicator (fun _ => (1 : ℂ)) g *
      (x g * φ g * (starRingEnd ℂ) (y g) * ((ideleNorm F (Matrix.GeneralLinearGroup.det g) ^ (-w) : ℝ) : ℂ))) =
      Sd.indicator Q := by
    funext g
    by_cases hg : g ∈ Sd
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, one_mul]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul]
  rw [hk₁]
  have hind : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => BorelUnfolding.indicator_comp_globalPoints_mul F γ f g
  have hind' : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (f : AdelicGL2 (𝓞 F) F → ℝ≥0∞) (g : AdelicGL2 (𝓞 F) F),
      Sd.indicator f (globalPoints (𝓞 F) F γ * g) = Sd.indicator (fun g => f (globalPoints (𝓞 F) F γ * g)) g :=
    fun γ f g => BorelUnfolding.indicator_comp_globalPoints_mul F γ f g
  have htsi : ∀ (f : Option F → AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F),
      ∑' o, Sd.indicator (f o) g = Sd.indicator (fun g => ∑' o, f o g) g :=
    fun f g => BorelUnfolding.tsum_indicator_const_set F Sd f g
  have htsi' : ∀ (f : Option F → AdelicGL2 (𝓞 F) F → ℝ≥0∞) (g : AdelicGL2 (𝓞 F) F),
      ∑' o, Sd.indicator (f o) g = Sd.indicator (fun g => ∑' o, f o g) g :=
    fun f g => BorelUnfolding.tsum_indicator_const_set F Sd f g

  have hc_none : ∀ g : AdelicGL2 (𝓞 F) F, globalPoints (𝓞 F) F (c none) * g = g := fun g => by
    show globalPoints (𝓞 F) F 1 * g = g; rw [map_one, one_mul]
  have hc_some : ∀ (ξ : F) (g : AdelicGL2 (𝓞 F) F), globalPoints (𝓞 F) F (c (some ξ)) * g =
      adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g := fun ξ g => by
    show globalPoints (𝓞 F) F ((gl2Weyl : Matrix.GeneralLinearGroup (Fin 2) F) * unipotentGL2 ξ) * g = _
    rw [BorelUnfolding.globalPoints_bruhat]
  have hsmul : ∀ (o : Option F) (g : AdelicGL2 (𝓞 F) F),
      ((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g = globalPoints (𝓞 F) F (c o) * g := fun o g => by
    rw [hRc]; rfl
  have htsum_phi : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, φ (globalPoints (𝓞 F) F (c o) * g) = Ew g := by
    intro g
    have h := BorelUnfolding.hasSum_option (fun o => φ (globalPoints (𝓞 F) F (c o) * g)) (a := ∑' ξ : F,
      φ (adelicWeyl (𝓞 F) F * unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) ξ) * g)) (by
        simp only [hc_some]
        exact (hφsum g).of_norm.hasSum)
    rw [h.tsum_eq]
    simp only [hc_none, hEw]
  have htsum_phie : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, ‖φ (globalPoints (𝓞 F) F (c o) * g)‖ₑ = Ebe g := by
    intro g
    rw [BorelUnfolding.tsum_option_ennreal]
    simp only [hc_none, hc_some, hEbe]

  obtain ⟨hL, hB⟩ :=
    MeasureTheory.IsFundamentalDomain.setLIntegral_iUnion_inv_smul_eq_and_setIntegral_eq_of_leftCosetRepresentatives
      μG ⊤ (borelSubgroup F) le_top S hStop R hR

  set Gx : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ENNReal.ofReal (‖x g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g with hGx
  set Gy : AdelicGL2 (𝓞 F) F → ℝ≥0∞ := fun g => ENNReal.ofReal (‖y g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g with hGy
  have hmaj : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), IntegrableOn (fun g => ‖z g‖ ^ 2 * Eb g * ω g) 𝓕 μG →
      ∫⁻ g in S, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) g ∂μG < ⊤ := by
    intro z hz
    rw [lintegral_indicator hSdm, Measure.restrict_restrict hSdm, Set.inter_comm, setLIntegral_congr hScap]
    have h2 := hz.2
    rw [HasFiniteIntegral] at h2
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun g => ?_)) h2
    have hEb0 : 0 ≤ Eb g := add_nonneg (norm_nonneg _) (tsum_nonneg fun _ => norm_nonneg _)
    rw [hEbe_eq, Real.enorm_eq_ofReal (mul_nonneg (mul_nonneg (sq_nonneg _) hEb0) (hωpos g).le),
      ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hEb0), ENNReal.ofReal_mul (sq_nonneg _)]
    ring
  have hGx_fin := hmaj x (by simpa only [hEb] using hintx)
  have hGy_fin := hmaj y (by simpa only [hEb] using hinty)

  have hconj : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      (∀ (γ : Matrix.GeneralLinearGroup (Fin 2) F) (g : AdelicGL2 (𝓞 F) F), z (globalPoints (𝓞 F) F γ * g) = z g) →
      ∫⁻ g in 𝓕B, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2 * ‖φ g‖ * ω g)) g ∂μG =
        ∫⁻ g in S, Sd.indicator (fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) g ∂μG := by
    intro z hz hzG
    have hmeas : Measurable (Sd.indicator fun g => ENNReal.ofReal (‖z g‖ ^ 2 * ‖φ g‖ * ω g)) :=
      (ENNReal.measurable_ofReal.comp (((hz.norm.pow 2).mul hφc.norm).mul hωc).measurable).indicator hSdm
    rw [hL _ hmeas]
    refine lintegral_congr fun g => ?_
    simp only [hsmul, hind', hzG, hωG]
    rw [htsi']
    congr 1
    funext g
    rw [← htsum_phie g, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun o => ?_
    rw [ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) (norm_nonneg _)), ENNReal.ofReal_mul (sq_nonneg _),
      ofReal_norm]
    ring

  have hEbem : Measurable Ebe :=
    (hφc.measurable.enorm).add (Measurable.tsum fun ξ =>
      (hφc.comp (continuous_const.mul continuous_id)).measurable.enorm)
  have hGm : ∀ (z : AdelicGL2 (𝓞 F) F → ℂ), Continuous z →
      Measurable (Sd.indicator fun g => ENNReal.ofReal (‖z g‖ ^ 2) * ENNReal.ofReal (ω g) * Ebe g) := fun z hz =>
    (((ENNReal.measurable_ofReal.comp (hz.norm.pow 2).measurable).mul
      (ENNReal.measurable_ofReal.comp hωc.measurable)).mul hEbem).indicator hSdm

  have hfin : ∫⁻ g in S, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ∂μG < ∞ := by
    have hpt : ∀ g : AdelicGL2 (𝓞 F) F, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ≤
        Sd.indicator Gx g + Sd.indicator Gy g := by
      intro g
      simp only [hsmul, enorm_indicator_eq_indicator_enorm, hind']
      rw [htsi']
      by_cases hg : g ∈ Sd
      swap
      · simp only [Set.indicator_of_notMem hg, add_zero]; exact le_rfl
      simp only [Set.indicator_of_mem hg]

      have hterm : ∀ o, ‖Q (globalPoints (𝓞 F) F (c o) * g)‖ₑ =
          ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * ‖φ (globalPoints (𝓞 F) F (c o) * g)‖ₑ := by
        intro o
        simp only [hQ, hxG, hyG, hωG, enorm_mul, RCLike.enorm_conj, BorelUnfolding.enorm_coe_real_of_nonneg (hωpos g).le]
        ring
      simp only [hterm]
      rw [ENNReal.tsum_mul_left, htsum_phie, hGx, hGy]
      beta_reduce
      rw [BorelUnfolding.ofReal_sq_norm, BorelUnfolding.ofReal_sq_norm]
      calc ‖x g‖ₑ * ‖y g‖ₑ * ENNReal.ofReal (ω g) * Ebe g
          ≤ (‖x g‖ₑ ^ 2 + ‖y g‖ₑ ^ 2) * ENNReal.ofReal (ω g) * Ebe g := by
            gcongr
            exact BorelUnfolding.mul_le_sq_add_sq _ _
        _ = ‖x g‖ₑ ^ 2 * ENNReal.ofReal (ω g) * Ebe g + ‖y g‖ₑ ^ 2 * ENNReal.ofReal (ω g) * Ebe g := by ring
    calc ∫⁻ g in S, ∑' o, ‖(Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g)‖ₑ ∂μG
        ≤ ∫⁻ g in S, (Sd.indicator Gx g + Sd.indicator Gy g) ∂μG := lintegral_mono hpt
      _ = (∫⁻ g in S, Sd.indicator Gx g ∂μG) + ∫⁻ g in S, Sd.indicator Gy g ∂μG :=
          lintegral_add_left (hGm x hxc) _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hGx_fin, hGy_fin⟩
  obtain ⟨hint, -, hid⟩ := hB (Sd.indicator Q) ((hQc.aestronglyMeasurable).indicator hSdm) hfin
  refine ⟨hint, ?_, ?_, ?_⟩
  ·
    rw [hid]

    set P : AdelicGL2 (𝓞 F) F → ℂ := fun g => x g * Ew g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ) with hP
    have hsumQ : ∀ g : AdelicGL2 (𝓞 F) F,
        ∑' o, (Sd.indicator Q) (((R o : Matrix.GeneralLinearGroup (Fin 2) F)⁻¹) • g) = Sd.indicator P g := by
      intro g
      simp only [hsmul, hind]
      rw [htsi]
      congr 1
      funext g
      have hterm : ∀ o, Q (globalPoints (𝓞 F) F (c o) * g) =
          (x g * (starRingEnd ℂ) (y g) * ((ω g : ℝ) : ℂ)) * φ (globalPoints (𝓞 F) F (c o) * g) := by
        intro o; simp only [hQ, hxG, hyG, hωG]; ring
      simp only [hterm]
      rw [tsum_mul_left, htsum_phi, hP]
      ring
    simp_rw [hsumQ]
    rw [setIntegral_indicator hSdm, setIntegral_congr_set hScap]
    rfl
  · rw [hconj x hxc hxG]; exact hGx_fin
  · rw [hconj y hyc hyG]; exact hGy_fin

end AutomorphicForm

end
