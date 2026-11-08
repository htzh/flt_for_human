/-
  The adelic maximal compact inside the induced-section layer: a flat family over it, and the
  Weyl/unipotent non-vanishing of an induced section.

  `flat_family_comp_mul_of_mem_adelicMaximalCompact` right-translates a family of induced,
  archimedean-`K`-finite, `K_f`-smooth sections by an element `k₀` of `adelicMaximalCompact` and
  keeps all five properties: `IsInducedSection` is closure under right translation, and the two
  finiteness properties are transported place by place — the archimedean one by moving the
  `w`-component of `k₀` to the front, where it meets the inducing datum inside the row-isometry
  subgroup and the commuting factor is absorbed by the finite part. Flatness over
  `adelicMaximalCompact` is preserved because that subgroup is closed under multiplication.

  `exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` is the
  Weyl/unipotent non-vanishing: a nonzero continuous `K_f`-smooth induced section, evaluated at
  `w⁻¹ · u(x)` for some adelic `x`, is nonzero. The proof is a `by_contra`: if it vanished at every
  `x`, then the induced-section relation writes `φ g` as a value at such a point for every `g` whose
  `(1,0)` entry is a unit — the Bruhat decomposition `g = b · w⁻¹u(x)` with `b` upper triangular.
  Reducing the finite part to the identity off a finite set of places (the `K_f`-smoothness, through
  its open stabilizer and the cofinality of the `maximalCompactAway` shape) leaves only a lower-row
  condition `a + d·y ≠ 0`, which is met one place at a time by choosing a small nonzero `y` in the
  relevant open set. The gate enters through `isCompact_adelicMaximalCompact`, which makes the
  stabilizer argument uniform.

  Transcribed from the two pin proof files
  `P2M/Sol/S_AutomorphicForm_{flat_family_comp_mul_of_mem_adelicMaximalCompact,
  exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth}.lean`
  (pinned `aa2d8b3`). Each statement is the matching `Theorems/Thm_AutomorphicForm_*.lean` wrapper
  verbatim, at the wrapper's binders and the wrapper's name inside the root `AutomorphicForm`
  namespace; both statements carry the wrapper's leading `let α := …`.

  Body-level drift, per row (no statement touched):
  * `exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth` — the pin's
    `push_neg` is written `push Not`, its `Set.mem_setOf_eq` is written `Set.mem_ofPred_eq`, and the
    `dif_pos`/`dif_neg`/`if_pos`/`if_neg` spellings are the `v4.34.0` `dite_eq_left`/`dite_eq_right`/
    `ite_eq_left`/`ite_eq_right` (all deprecated names). The pin's `attribute [-instance]` line is
    dropped. `continuous_finComponent_glFin` is proved from the port's `continuous_finComponent` and
    `continuous_glFin` rather than entry by entry, and `exists_finset_fixing`'s compactness step is
    written with `elim_directed_family_closed`'s `Disjoint` form (`v4.34.0`), as in the factors
    module.
  * `flat_family_comp_mul_of_mem_adelicMaximalCompact` — the pin's `isSmoothVector_iff_isOpen_
    stabilizer` rewrite is kept; nothing else changed.

  spec-pin: Theorems/Thm_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_flat_family_comp_mul_of_mem_adelicMaximalCompact.lean   -- comparable copy
  spec-pin: Theorems/Thm_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.LevelCompactness
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.NumberTheory.AdelicHaar.PlaceMeasure
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm WindowedSiegel Filter Topology FLT.SmoothVectors
open scoped NNReal

noncomputable section

namespace AutomorphicForm

/-! ## Right translation by an element of the maximal compact -/

section KStab

variable {F : Type} [Field F] [NumberField F]

private theorem glFin_inclAt (w : InfinitePlace F) (r : GL (Fin 2) w.Completion) :
    glFin (𝓞 F) F (adelicArchGLInclAt F w r) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glFin_adelicArchGLIncl]

private theorem archComponent_inclAt_self (w : InfinitePlace F) (r : GL (Fin 2) w.Completion) :
    archComponent F w (glArch (𝓞 F) F (adelicArchGLInclAt F w r)) = r := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self]

private theorem archComponent_inclAt_of_ne {w w' : InfinitePlace F} (h : w' ≠ w)
    (r : GL (Fin 2) w.Completion) :
    archComponent F w' (glArch (𝓞 F) F (adelicArchGLInclAt F w r)) = 1 := by
  rw [adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_of_ne F h]

private theorem commute_of_archComponent_eq_one (w : InfinitePlace F) {k : AdelicGL2 (𝓞 F) F}
    (hk : archComponent F w (glArch (𝓞 F) F k) = 1) (r : GL (Fin 2) w.Completion) :
    k * adelicArchGLInclAt F w r = adelicArchGLInclAt F w r * k := by
  apply eq_of_glArch_eq_of_glFin_eq F
  · rw [map_mul, map_mul]
    apply ext_archComponent
    intro w'
    rw [map_mul, map_mul]
    by_cases hw : w' = w
    · subst hw; rw [hk, archComponent_inclAt_self, one_mul, mul_one]
    · rw [archComponent_inclAt_of_ne hw, one_mul, mul_one]
  · rw [map_mul, map_mul, glFin_inclAt, one_mul, mul_one]

end KStab

open scoped Classical in
theorem flat_family_comp_mul_of_mem_adelicMaximalCompact
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ))
      (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : ∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (φ s))
      (_hφK : ∀ s, IsArchKFinite F (φ s))
      (_hφf : ∀ s, IsKfSmooth F (φ s))
      (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2))
      (_hφhol : ∀ g, Differentiable ℂ (fun s => φ s g))
      (_hφflat : ∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
          glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          φ s k = φ s' k)
      (k₀ : AdelicGL2 (𝓞 F) F) (_hk₀ : k₀ ∈ adelicMaximalCompact F),
    (∀ s, IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) (fun h => φ s (h * k₀))) ∧
    (∀ s, IsArchKFinite F (fun h => φ s (h * k₀))) ∧
    (∀ s, IsKfSmooth F (fun h => φ s (h * k₀))) ∧
    Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 (p.2 * k₀)) ∧
    (∀ g, Differentiable ℂ (fun s => φ s (g * k₀))) ∧
    (∀ (s s' : ℂ) (k : AdelicGL2 (𝓞 F) F),
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s (k * k₀) = φ s' (k * k₀)) := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat k₀ hk₀
  refine ⟨fun s => (hφ s).rightTranslate k₀, ?_, ?_, ?_, fun g => hφhol (g * k₀), ?_⟩
  ·
    intro s w
    obtain ⟨sset, hs⟩ := hφK s w
    set r₀ : GL (Fin 2) w.Completion := archComponent F w (glArch (𝓞 F) F k₀) with hr₀
    have hr₀mem : r₀ ∈ rowIsometrySubgroup w.Completion := (mem_adelicMaximalCompact_iff'.mp hk₀).2 w
    obtain ⟨k₁, hk₁w, hk₀eq⟩ : ∃ k₁ : AdelicGL2 (𝓞 F) F,
        archComponent F w (glArch (𝓞 F) F k₁) = 1 ∧ k₀ = adelicArchGLInclAt F w r₀ * k₁ := by
      refine ⟨(adelicArchGLInclAt F w r₀)⁻¹ * k₀, ?_, by rw [mul_inv_cancel_left]⟩
      rw [map_mul, map_inv, map_mul, map_inv, archComponent_inclAt_self, hr₀, inv_mul_cancel]
    let L : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
      LinearMap.funLeft ℂ ℂ (fun x : AdelicGL2 (𝓞 F) F => x * k₁)
    classical
    refine ⟨sset.image L, fun u hu => ?_⟩
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hu
    have hmem : (fun x => φ s (x * adelicArchGLInclAt F w (r * r₀))) ∈ Submodule.span ℂ (sset : Set _) :=
      hs _ (Subgroup.mem_map.mpr ⟨r * r₀, (rowIsometrySubgroup w.Completion).mul_mem hr hr₀mem, rfl⟩)
    have hfun : (fun x => φ s (x * adelicArchGLInclAt F w r * k₀))
        = L (fun x => φ s (x * adelicArchGLInclAt F w (r * r₀))) := by
      funext x
      simp only [L, LinearMap.funLeft_apply]
      rw [hk₀eq]
      congr 1
      calc x * adelicArchGLInclAt F w r * (adelicArchGLInclAt F w r₀ * k₁)
          = x * (adelicArchGLInclAt F w (r * r₀) * k₁) := by simp only [map_mul, mul_assoc]
        _ = x * (k₁ * adelicArchGLInclAt F w (r * r₀)) := by
            rw [commute_of_archComponent_eq_one w hk₁w (r * r₀)]
        _ = x * k₁ * adelicArchGLInclAt F w (r * r₀) := by rw [mul_assoc]
    rw [hfun, Finset.coe_image, ← Submodule.map_span]
    exact Submodule.mem_map_of_mem hmem
  ·
    intro s
    have hv := hφf s
    rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hv ⊢
    have hnorm : (finiteAdelicGL2Subgroup F).Normal := by
      unfold finiteAdelicGL2Subgroup; infer_instance
    let c : finiteAdelicGL2Subgroup F → finiteAdelicGL2Subgroup F := fun h =>
      ⟨k₀⁻¹ * (h : AdelicGL2 (𝓞 F) F) * k₀, by
        have := hnorm.conj_mem (h : AdelicGL2 (𝓞 F) F) h.2 k₀⁻¹
        rwa [inv_inv] at this⟩
    have hc : Continuous c :=
      ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
    have hset : ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
        (RightTranslationFn.mk fun h => φ s (h * k₀)) : Subgroup (finiteAdelicGL2Subgroup F)) :
          Set (finiteAdelicGL2Subgroup F))
        = c ⁻¹' ((MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ s)) :
            Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := by
      ext h
      simp only [SetLike.mem_coe, Set.mem_preimage, MulAction.mem_stabilizer_iff, Subgroup.smul_def]
      constructor
      · intro hh
        apply RightTranslationFn.ext
        intro x
        have := congrArg (fun f => RightTranslationFn.toFun f (x * k₀⁻¹)) hh
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk] at this
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, c]
        simpa [mul_assoc] using this
      · intro hh
        apply RightTranslationFn.ext
        intro x
        have := congrArg (fun f => RightTranslationFn.toFun f (x * k₀)) hh
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk, c] at this
        simp only [RightTranslationFn.toFun_smul, RightTranslationFn.toFun_mk]
        simpa [mul_assoc] using this
    rw [hset]
    exact hv.preimage hc
  ·
    exact hφjc.comp (continuous_fst.prodMk (continuous_snd.mul continuous_const))
  ·
    intro s s' k hkf hka
    have hkK : k ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkf, hka⟩
    have hkk₀ := (adelicMaximalCompact F).mul_mem hkK hk₀
    exact hφflat s s' (k * k₀) hkk₀.1 hkk₀.2

/-! ## The Weyl/unipotent non-vanishing -/

open scoped Classical

section WeylNonvanishing

open IsDedekindDomain.HeightOneSpectrum

variable (F : Type) [Field F] [NumberField F]

private theorem continuous_finComponent_glFin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => finComponent (𝓞 F) F v (glFin (𝓞 F) F g) :=
  (continuous_finComponent (𝓞 F) F v).comp (continuous_glFin (𝓞 F) F)

/-- The compact set of the witness argument: the maximal compact meet the finite level subgroup. -/
private def Cpt : Set (AdelicGL2 (𝓞 F) F) :=
  (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) ∩ (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))

private theorem isCompact_Cpt : IsCompact (Cpt F) :=
  (isCompact_adelicMaximalCompact F).inter_right (isClosed_finiteAdelicGL2Subgroup F)

private theorem mem_Cpt {k : AdelicGL2 (𝓞 F) F} (h1 : glArch (𝓞 F) F k = 1)
    (h2 : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F) : k ∈ Cpt F := by
  refine ⟨⟨h2, fun w => ?_⟩, h1⟩
  rw [h1, map_one]; exact isRowIsometry_one

private theorem exists_finset_fixing (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsKfSmooth F φ₀) :
    ∃ S₂ : Finset (HeightOneSpectrum (𝓞 F)), ∀ k : AdelicGL2 (𝓞 F) F,
      glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ v ∈ S₂, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1) → ∀ g, φ₀ (g * k) = φ₀ g := by
  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ₀ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup F)) : Set (finiteAdelicGL2Subgroup F)) := hsm
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have h1V : (1 : AdelicGL2 (𝓞 F) F) ∈ V := by
    have : (1 : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact Subgroup.one_mem _
    exact this
  set t : Finset (HeightOneSpectrum (𝓞 F)) → Set (AdelicGL2 (𝓞 F) F) :=
    fun S => {k | ∀ v ∈ S, finComponent (𝓞 F) F v (glFin (𝓞 F) F k) = 1} with ht
  have htc : ∀ S, IsClosed (t S) := by
    intro S
    have : t S = ⋂ v ∈ S, (fun k => finComponent (𝓞 F) F v (glFin (𝓞 F) F k)) ⁻¹' {1} := by
      ext k; simp [ht]
    rw [this]
    exact isClosed_biInter fun v _ => isClosed_singleton.preimage (continuous_finComponent_glFin F v)
  have hdir : Directed (· ⊇ ·) t := by
    intro S S'
    refine ⟨S ∪ S', fun k hk v hv => hk v (Finset.mem_union_left _ hv), fun k hk v hv => hk v (Finset.mem_union_right _ hv)⟩
  have hst : Disjoint (Cpt F ∩ Vᶜ) (⋂ S, t S) := by
    rw [Set.disjoint_left]
    intro k hk hall
    rw [Set.mem_iInter] at hall
    apply hk.2
    have : k = 1 := by
      refine eq_of_glArch_eq_of_glFin_eq F (by rw [map_one]; exact hk.1.2)
        (glFin_ext F fun v => ?_)
      rw [map_one, map_one]
      exact hall {v} v (Finset.mem_singleton_self v)
    rw [this]; exact h1V
  obtain ⟨S₂, hS₂⟩ := ((isCompact_Cpt F).inter_right hV.isClosed_compl).elim_directed_family_closed t htc hst hdir
  refine ⟨S₂, fun k hk1 hk2 hk3 g => ?_⟩
  have hkC : k ∈ Cpt F := mem_Cpt F hk1 hk2
  have hkV : k ∈ V := by
    by_contra hnot
    exact Set.disjoint_left.mp hS₂ ⟨hkC, hnot⟩ hk3
  have hstab : (⟨k, hk1⟩ : finiteAdelicGL2Subgroup F) ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F)
      (RightTranslationFn.mk φ₀ : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) := by
    have : (⟨k, hk1⟩ : finiteAdelicGL2Subgroup F) ∈ Subtype.val ⁻¹' V := hkV
    rw [hVeq] at this; exact this
  rw [MulAction.mem_stabilizer_iff] at hstab
  have := congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f g) hstab
  exact this

variable (S₂ : Finset (HeightOneSpectrum (𝓞 F)))

omit [NumberField F] in
private theorem compl_le : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.mpr S₂.finite_toSet.compl_mem_cofinite

/-- The section of the finite restricted product over `S₂` built from local coordinates. -/
private def secP (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) :=
  ⟨fun v => if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F), by
    rw [Filter.eventually_principal]
    intro v hv
    rw [Set.mem_compl_iff, Finset.mem_coe] at hv
    simp only [dite_eq_right hv]
    exact zero_mem _⟩

private def sec (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (compl_le F S₂) (secP F S₂ b)

private theorem sec_apply_of_mem (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S₂) :
    sec F S₂ b v = b ⟨v, hv⟩ := by
  change (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F)) = _
  rw [dite_eq_left hv]

private theorem continuous_sec : Continuous (sec F S₂) := by
  refine (RestrictedProduct.continuous_inclusion (compl_le F S₂)).comp ?_
  rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
  intro v
  change Continuous fun b : (∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) => (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F))
  by_cases hv : v ∈ S₂
  · simp only [dite_eq_left hv]; exact continuous_apply _
  · simp only [dite_eq_right hv]; exact continuous_const

private theorem sec_apply_of_not_mem (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S₂) :
    sec F S₂ b v = 0 := by
  change (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F)) = _
  rw [dite_eq_right hv]

variable (S : Finset (HeightOneSpectrum (𝓞 F)))

private def evFin (v : HeightOneSpectrum (𝓞 F)) : AdeleRing (𝓞 F) F →+* v.adicCompletion F :=
  (finAdeleEval (𝓞 F) F v).comp (adeleFin (𝓞 F) F)

private theorem evFin_apply (v : HeightOneSpectrum (𝓞 F)) (a : AdeleRing (𝓞 F) F) :
    evFin F v a = a.2 v := rfl

private theorem matrix_ext {M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)}
    (h₁ : (adeleArch (𝓞 F) F).mapMatrix M = (adeleArch (𝓞 F) F).mapMatrix N)
    (h₂ : ∀ v, (evFin F v).mapMatrix M = (evFin F v).mapMatrix N) : M = N := by
  ext i j
  apply Prod.ext
  · exact congrFun (congrFun h₁ i) j
  · refine RestrictedProduct.ext _ _ fun v => ?_
    exact congrFun (congrFun (h₂ v) i) j

/-- The matrix that agrees with `M` away from `S` and is `1` at the places in `S`. -/
private def awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (⟨fun v => if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v, by
        filter_upwards [(M i j).2.2] with v hv
        split_ifs
        · rw [Matrix.one_apply]
          split_ifs
          · exact one_mem _
          · exact zero_mem _
        · exact hv⟩ : FiniteAdeleRing (𝓞 F) F))

private theorem evArch_awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) :
    (adeleArch (𝓞 F) F).mapMatrix (awayMat F S M) = 1 := by
  ext i j; rfl

private theorem evFin_awayMat (M : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F)) :
    (evFin F v).mapMatrix (awayMat F S M) = if v ∈ S then 1 else (evFin F v).mapMatrix M := by
  split_ifs with hv
  · ext i j : 1
    show (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v) = _
    rw [ite_eq_left hv]
  · ext i j : 1
    show (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (M i j).2 v) = _
    rw [ite_eq_right hv]
    rfl

private def awayMatHom : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) →* Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) where
  toFun := awayMat F S
  map_one' := matrix_ext F (by rw [evArch_awayMat, map_one]) fun v => by
    rw [evFin_awayMat]; split_ifs <;> simp [map_one]
  map_mul' M N := matrix_ext F (by rw [evArch_awayMat, map_mul, evArch_awayMat, evArch_awayMat, one_mul]) fun v => by
    simp only [evFin_awayMat, map_mul]
    split_ifs <;> simp

private def awayPart : AdelicGL2 (𝓞 F) F →* AdelicGL2 (𝓞 F) F := Units.map (awayMatHom F S)

private theorem coe_awayPart (g : AdelicGL2 (𝓞 F) F) :
    ((awayPart F S g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = awayMat F S g := rfl

private theorem glArch_awayPart (g : AdelicGL2 (𝓞 F) F) : glArch (𝓞 F) F (awayPart F S g) = 1 := by
  refine Units.ext ?_
  change (adeleArch (𝓞 F) F).mapMatrix (awayMat F S g) = 1
  exact evArch_awayMat F S g

private theorem coe_finComponent_glFin (g : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    ((finComponent (𝓞 F) F v (glFin (𝓞 F) F g) : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) =
      (evFin F v).mapMatrix (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := rfl

private theorem finComponent_awayPart (g : AdelicGL2 (𝓞 F) F) (v : HeightOneSpectrum (𝓞 F)) :
    finComponent (𝓞 F) F v (glFin (𝓞 F) F (awayPart F S g)) =
      if v ∈ S then 1 else finComponent (𝓞 F) F v (glFin (𝓞 F) F g) := by
  split_ifs with hv
  · refine Units.ext ?_
    rw [coe_finComponent_glFin, coe_awayPart, evFin_awayMat, ite_eq_left hv]; rfl
  · refine Units.ext ?_
    rw [coe_finComponent_glFin, coe_awayPart, evFin_awayMat, ite_eq_right hv, coe_finComponent_glFin]

private theorem glFin_awayPart_mem {h : AdelicGL2 (𝓞 F) F}
    (hint : ∀ v ∉ S, ∀ i j, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F) :
    glFin (𝓞 F) F (awayPart F S h) ∈ finiteIntegralGL2 (𝓞 F) F := by
  rw [mem_finiteIntegralGL2_iff]
  constructor
  · intro i j v
    rw [glFin_apply, coe_awayPart]
    change (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∈ _
    split_ifs with hv
    · rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    · exact (hint v hv i j).1
  · intro i j v
    rw [← map_inv, ← map_inv, glFin_apply, coe_awayPart]
    change (if v ∈ S then (1 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j else (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∈ _
    split_ifs with hv
    · rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _]
    · exact (hint v hv i j).2

private theorem coe_adelicWeyl :
    ((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![0, 1; 1, 0] := by
  rw [adelicWeyl]
  ext i j
  change algebraMap F (AdeleRing (𝓞 F) F) ((!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) F) i j) = _
  fin_cases i <;> fin_cases j <;> simp

private theorem adelicWeyl_inv : (adelicWeyl (𝓞 F) F)⁻¹ = adelicWeyl (𝓞 F) F := by
  rw [adelicWeyl, ← map_inv, gl2Weyl_inv]

private theorem unipotentGL2_inv (x : AdeleRing (𝓞 F) F) :
    (unipotentGL2 x : AdelicGL2 (𝓞 F) F)⁻¹ = unipotentGL2 (-x) :=
  inv_eq_of_mul_eq_one_right (by rw [← unipotentGL2_add, add_neg_cancel, unipotentGL2_zero])

private theorem mul_apply_fst (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (w : InfinitePlace F) :
    ((M * N) i j).1 w = ∑ k : Fin 2, (M i k).1 w * (N k j).1 w := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

private theorem mul_apply_snd (M N : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) (v : HeightOneSpectrum (𝓞 F)) :
    ((M * N) i j).2 v = ∑ k : Fin 2, (M i k).2 v * (N k j).2 v := by
  rw [Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two]; rfl

private theorem mem_borel_of_unit (g : AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ)
    (hc : (c : AdeleRing (𝓞 F) F) = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) :
    g * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 (↑c⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1))⁻¹ ∈
      adelicBorel (𝓞 F) F := by
  rw [mem_borelSubgroup_iff, mul_inv_rev, inv_inv, unipotentGL2_inv, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]
  rw [← hc, ← mul_assoc, Units.mul_inv, one_mul]
  ring

private theorem entry10_mul_lower (g : AdelicGL2 (𝓞 F) F) (y : AdeleRing (𝓞 F) F) :
    ((g * (adelicWeyl (𝓞 F) F * unipotentGL2 y * adelicWeyl (𝓞 F) F) : AdelicGL2 (𝓞 F) F) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 + (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 * y := by
  simp only [Matrix.GeneralLinearGroup.coe_mul, coe_adelicWeyl, unipotentGL2_coe]
  simp [Matrix.mul_apply, Fin.sum_univ_two]

omit [NumberField F] in
private theorem exists_ne_zero_mem_arch (w : InfinitePlace F) {t : Set w.Completion} (ht : IsOpen t)
    (h0 : (0 : w.Completion) ∈ t) : ∃ x ∈ t, x ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  have hmem : ((r / 2 : ℝ) : ℂ) ∈ Set.range (InfinitePlace.Completion.extensionEmbedding w) := by
    rcases w.isReal_or_isComplex with hw | hw
    · obtain ⟨x, hx⟩ := (InfinitePlace.Completion.bijective_extensionEmbeddingOfIsReal hw).2 (r / 2)
      exact ⟨x, by rw [← InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hw x, hx]⟩
    · exact (InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw) _
  obtain ⟨x, hx⟩ := hmem
  have hnorm : ‖x‖ = r / 2 := by
    have h := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) x
    rw [← h, hx, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine ⟨x, hball ?_, ?_⟩
  · rw [Metric.mem_ball, dist_zero_right, hnorm]; linarith
  · rw [← norm_ne_zero_iff, hnorm]; positivity

private theorem exists_ne_zero_mem_fin (v : HeightOneSpectrum (𝓞 F)) {t : Set (v.adicCompletion F)}
    (ht : IsOpen t) (h0 : (0 : v.adicCompletion F) ∈ t) : ∃ x ∈ t, x ≠ 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp ht 0 h0
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
  have hvπ : Valued.v ((π : F) : v.adicCompletion F) = Multiplicative.ofAdd (-1 : ℤ) := by
    rw [valuedAdicCompletion_eq_valuation']; exact hπ
  have hπ0 : ((π : F) : v.adicCompletion F) ≠ 0 := by
    intro h
    rw [h, Valuation.map_zero] at hvπ
    exact WithZero.zero_ne_coe hvπ
  have hπ1 : ‖((π : F) : v.adicCompletion F)‖ < 1 := by
    rw [Valued.toNormedField.norm_lt_one_iff, hvπ, ← WithZero.coe_one, WithZero.coe_lt_coe, ← ofAdd_zero,
      Multiplicative.ofAdd_lt]
    norm_num
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hπ1
  refine ⟨((π : F) : v.adicCompletion F) ^ n, hball ?_, pow_ne_zero _ hπ0⟩
  rw [Metric.mem_ball, dist_zero_right, norm_pow]; exact hn

private theorem witness_main (α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ) (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
    (hφc : Continuous φ) (hφf : IsKfSmooth F φ) (hne : ∃ g, φ g ≠ 0) :
    ∃ x : AdeleRing (𝓞 F) F, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hvan : ∀ (g : AdelicGL2 (𝓞 F) F) (c : (AdeleRing (𝓞 F) F)ˣ),
      (c : AdeleRing (𝓞 F) F) = (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 → φ g = 0 := by
    intro g c hc
    set x := (↑c⁻¹ * (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1) with hx
    have hb := mem_borel_of_unit F g c hc
    have e : g = (g * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)⁻¹) * ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) := by
      rw [inv_mul_cancel_right]
    rw [e, hφ _ hb, hall x, mul_zero]
  obtain ⟨g₀, hg₀⟩ := hne
  have hT : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ ij : Fin 2 × Fin 2,
      ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2 v ∈ v.adicCompletionIntegers F ∧
      (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2 v ∈ v.adicCompletionIntegers F := by
    rw [Filter.eventually_all]
    intro ij
    exact (((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2.2).and
      ((((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ij.1 ij.2).2.2)
  rw [Filter.eventually_cofinite] at hT
  set T : Finset (HeightOneSpectrum (𝓞 F)) := hT.toFinset with hTdef
  have hgood : ∀ v ∉ T, ∀ i j, ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((g₀⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv i j
    rw [hTdef, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] at hv
    exact hv (i, j)
  obtain ⟨S₂, hS₂⟩ := exists_finset_fixing F φ hφf
  set S : Finset (HeightOneSpectrum (𝓞 F)) := S₂ ∪ T with hSdef
  set h : AdelicGL2 (𝓞 F) F := g₀⁻¹ * adelicWeyl (𝓞 F) F with hhdef
  have hWint : ∀ (v : HeightOneSpectrum (𝓞 F)) (i j : Fin 2),
      (((adelicWeyl (𝓞 F) F : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v i j
    rw [coe_adelicWeyl]
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact one_mem _
    · exact zero_mem _
  have hhint : ∀ v ∉ S, ∀ i j, ((h : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F ∧
      (((h⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv i j
    have hvT : v ∉ T := fun h' => hv (Finset.mem_union_right _ h')
    constructor
    · rw [hhdef, Matrix.GeneralLinearGroup.coe_mul, mul_apply_snd, Fin.sum_univ_two]
      exact add_mem (mul_mem (hgood v hvT _ _).2 (hWint v _ _)) (mul_mem (hgood v hvT _ _).2 (hWint v _ _))
    · rw [hhdef, mul_inv_rev, adelicWeyl_inv, inv_inv, Matrix.GeneralLinearGroup.coe_mul, mul_apply_snd,
        Fin.sum_univ_two]
      exact add_mem (mul_mem (hWint v _ _) (hgood v hvT _ _).1) (mul_mem (hWint v _ _) (hgood v hvT _ _).1)
  set m := awayPart F S h with hmdef
  set g₁ := g₀ * m with hg₁def
  have hφg₁ : φ g₁ = φ g₀ :=
    hS₂ m (glArch_awayPart F S h) (glFin_awayPart_mem F S hhint)
      (fun v hv => by rw [hmdef, finComponent_awayPart, ite_eq_left (Finset.mem_union_left _ hv)]) g₀
  set a : AdeleRing (𝓞 F) F := (g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 with hadef
  set d : AdeleRing (𝓞 F) F := (g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1 with hddef
  have hoff : ∀ v ∉ S, a.2 v = 1 ∧ d.2 v = 0 := by
    intro v hv
    have hfc : finComponent (𝓞 F) F v (glFin (𝓞 F) F g₁) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (adelicWeyl (𝓞 F) F)) := by
      rw [hg₁def, map_mul, map_mul, hmdef, finComponent_awayPart, ite_eq_right hv, hhdef, map_mul, map_mul, map_inv, map_inv,
        mul_inv_cancel_left]
    have e10 := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) => (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0) hfc
    have e11 := congrArg (fun M : GL (Fin 2) (v.adicCompletion F) => (M : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1) hfc
    simp only [finComponent_apply, glFin_apply, coe_adelicWeyl] at e10 e11
    exact ⟨by rw [hadef, e10]; rfl, by rw [hddef, e11]; rfl⟩
  have hrow_fin : ∀ v, ¬ (a.2 v = 0 ∧ d.2 v = 0) := by
    intro v ⟨ha, hd⟩
    have hdet := (Matrix.isUnits_det_units (finComponent (𝓞 F) F v (glFin (𝓞 F) F g₁))).ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp only [finComponent_apply, glFin_apply] at hdet
    apply hdet
    rw [show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 v = 0 from ha,
      show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 v = 0 from hd]
    ring
  have hrow_arch : ∀ w, ¬ (a.1 w = 0 ∧ d.1 w = 0) := by
    intro w ⟨ha, hd⟩
    have hdet := (Matrix.isUnits_det_units (archComponent F w (glArch (𝓞 F) F g₁))).ne_zero
    rw [Matrix.det_fin_two] at hdet
    simp only [archComponent_apply, glArch_apply] at hdet
    apply hdet
    rw [show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).1 w = 0 from ha,
      show ((g₁ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).1 w = 0 from hd]
    ring
  set gy : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F :=
    fun y => g₁ * (adelicWeyl (𝓞 F) F * unipotentGL2 y * adelicWeyl (𝓞 F) F) with hgydef
  have hgyc : Continuous gy :=
    continuous_const.mul ((continuous_const.mul (continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F))).mul continuous_const)
  have hWW : adelicWeyl (𝓞 F) F * adelicWeyl (𝓞 F) F = 1 := mul_eq_one_iff_eq_inv.mpr (adelicWeyl_inv F).symm
  have hgy0 : gy 0 = g₁ := by simp only [hgydef, unipotentGL2_zero, mul_one, hWW]
  set V : Set (AdeleRing (𝓞 F) F) := {y | φ (gy y) ≠ 0} with hVdef
  have hVo : IsOpen V := isOpen_compl_singleton.preimage (hφc.comp hgyc)
  have h0V : (0 : AdeleRing (𝓞 F) F) ∈ V := by
    change φ (gy 0) ≠ 0; rw [hgy0, hφg₁]; exact hg₀
  set e : InfiniteAdeleRing F × (∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) → AdeleRing (𝓞 F) F :=
    fun p => (p.1, sec F S p.2) with hedef
  have hec : Continuous e := continuous_fst.prodMk ((continuous_sec F S).comp continuous_snd)
  have hsec0 : sec F S 0 = 0 := by
    refine RestrictedProduct.ext _ _ fun v => ?_
    by_cases hv : v ∈ S
    · exact sec_apply_of_mem F S 0 hv
    · exact sec_apply_of_not_mem F S 0 hv
  have he0 : e (0, 0) = 0 := by
    change ((0 : InfiniteAdeleRing F), sec F S 0) = 0
    rw [hsec0]; rfl
  have hO : IsOpen (e ⁻¹' V) := hVo.preimage hec
  have h0O : ((0 : InfiniteAdeleRing F), (0 : ∀ v : S, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) ∈ e ⁻¹' V := by
    change e (0, 0) ∈ V; rw [he0]; exact h0V
  obtain ⟨u₁, u₂, hu₁, hu₂, h0u₁, h0u₂, hsub⟩ := isOpen_prod_iff.mp hO 0 0 h0O
  obtain ⟨t₁, ht₁, ht₁sub⟩ := isOpen_pi_iff'.mp hu₁ 0 h0u₁
  obtain ⟨t₂, ht₂, ht₂sub⟩ := isOpen_pi_iff'.mp hu₂ 0 h0u₂
  have hch₁ : ∀ w : InfinitePlace F, ∃ q : w.Completion, q ∈ t₁ w ∧ a.1 w + d.1 w * q ≠ 0 := by
    intro w
    by_cases ha : a.1 w = 0
    · have hd : d.1 w ≠ 0 := fun hd => hrow_arch w ⟨ha, hd⟩
      obtain ⟨q, hq, hq0⟩ := exists_ne_zero_mem_arch F w (ht₁ w).1 (by simpa using (ht₁ w).2)
      exact ⟨q, hq, by rw [ha, zero_add]; exact mul_ne_zero hd hq0⟩
    · exact ⟨0, by simpa using (ht₁ w).2, by rwa [mul_zero, add_zero]⟩
  have hch₂ : ∀ v : S, ∃ q : (v : HeightOneSpectrum (𝓞 F)).adicCompletion F, q ∈ t₂ v ∧ a.2 v + d.2 v * q ≠ 0 := by
    intro v
    by_cases ha : a.2 v = 0
    · have hd : d.2 v ≠ 0 := fun hd => hrow_fin v ⟨ha, hd⟩
      obtain ⟨q, hq, hq0⟩ := exists_ne_zero_mem_fin F v (ht₂ v).1 (by simpa using (ht₂ v).2)
      exact ⟨q, hq, by rw [ha, zero_add]; exact mul_ne_zero hd hq0⟩
    · exact ⟨0, by simpa using (ht₂ v).2, by rwa [mul_zero, add_zero]⟩
  choose p₁ hp₁ hp₁' using hch₁
  choose p₂ hp₂ hp₂' using hch₂
  set y : AdeleRing (𝓞 F) F := e (p₁, p₂) with hydef
  have hyV : y ∈ V := by
    have : (p₁, p₂) ∈ u₁ ×ˢ u₂ :=
      ⟨ht₁sub (Set.mem_univ_pi.mpr fun w => hp₁ w), ht₂sub (Set.mem_univ_pi.mpr fun v => hp₂ v)⟩
    exact hsub this
  set z : AdeleRing (𝓞 F) F := a + d * y with hzdef
  have hz1 : ∀ w, z.1 w ≠ 0 := fun w => by
    change a.1 w + d.1 w * p₁ w ≠ 0; exact hp₁' w
  have hz2S : ∀ v : HeightOneSpectrum (𝓞 F), ∀ hv : v ∈ S, z.2 v = a.2 v + d.2 v * p₂ ⟨v, hv⟩ := fun v hv => by
    change a.2 v + d.2 v * (sec F S p₂) v = _; rw [sec_apply_of_mem F S _ hv]
  have hz2off : ∀ v ∉ S, z.2 v = 1 := fun v hv => by
    change a.2 v + d.2 v * (sec F S p₂) v = 1
    rw [(hoff v hv).1, (hoff v hv).2, zero_mul, add_zero]
  have hz2 : ∀ v, z.2 v ≠ 0 := fun v => by
    by_cases hv : v ∈ S
    · rw [hz2S v hv]; exact hp₂' ⟨v, hv⟩
    · rw [hz2off v hv]; exact one_ne_zero
  set zinv : AdeleRing (𝓞 F) F := (fun w => (z.1 w)⁻¹, (⟨fun v => (z.2 v)⁻¹,
      Filter.eventually_of_mem S.finite_toSet.compl_mem_cofinite fun v hv => by
        rw [Set.mem_compl_iff, Finset.mem_coe] at hv
        show (z.2 v)⁻¹ ∈ v.adicCompletionIntegers F
        rw [hz2off v hv, inv_one]; exact one_mem _⟩ : FiniteAdeleRing (𝓞 F) F)) with hzinv
  have hzz : z * zinv = 1 := by
    refine Prod.ext (funext fun w => ?_) (RestrictedProduct.ext _ _ fun v => ?_)
    · exact mul_inv_cancel₀ (hz1 w)
    · exact mul_inv_cancel₀ (hz2 v)
  set c : (AdeleRing (𝓞 F) F)ˣ := ⟨z, zinv, hzz, by rw [mul_comm]; exact hzz⟩ with hcdef
  have hc : (c : AdeleRing (𝓞 F) F) = ((gy y : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0 := by
    change z = _
    rw [hzdef, hgydef]; dsimp only
    rw [entry10_mul_lower]
  exact hyV (hvan (gy y) c hc)

end WeylNonvanishing

open scoped Classical in
theorem exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)) (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ)
      (_hφc : Continuous φ) (_hφf : IsKfSmooth F φ) (_hne : ∃ g, φ g ≠ 0),
    ∃ x : AdeleRing (𝓞 F) F, φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) ≠ 0 := by
  intro α hα s φ hφ hφc hφf hne
  exact witness_main F α hα s φ hφ hφc hφf hne

end AutomorphicForm

end
