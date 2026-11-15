/-
  A two-sided eventual lower bound for the real part of the Weyl intertwining integral.

  For a continuous family `φ s` of induced sections that are archimedean-`K`-finite and
  `K_f`-smooth, nonnegative and real on the maximal compact (`hpos`), and nonzero there (`hex`),
  the Weyl intertwining integral `W(σ) = ∫ φ(σ)(w⁻¹·u(x)) dμ(x)` satisfies

    `0 < δ` and `δ ≤ ((σ - 1/2) * W(σ)).re` eventually as `σ → 1/2 +`.

  The engine is `exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one`, and the
  headline is the engine at the section variable `F`; the two carry the same statement, as in the
  pin, where the second is the `solution` that specializes the first.

  The argument, in the pin's order:

  * the `gl`-extension lemma `eq_of_glArch_eq_of_forall_finComponent_eq` and the continuity
    `continuous_finComponent_glFin` of the finite components;
  * the compact set `Cpt = adelicMaximalCompact ∩ finiteAdelicGL2Subgroup` and the fixed set
    `exists_finset_fixing`: a compactly supported `K_f`-smooth function is fixed by the finite
    integral points that are trivial at the places of a large enough finite set `S₂`;
  * the section `sec`/`secP` of the finite restricted product over `S₂` and its continuity
    `continuous_sec`, which let a neighbourhood condition at the places of `S₂` be imposed through
    a continuous section;
  * `exists_cylinder`: if `2 δ₀ < ψ x₀` at a point, there are open local conditions at the places of
    `S₂` and an open archimedean condition that force `δ₀ < ψ x` (the product form of the tube
    lemma);
  * `eventually_norm_sub_lt`: uniform continuity of a jointly continuous `φ` on a compact set as
    `σ → 1/2`, and `continuous_unipotentGL2_adeleRing`: continuity of `x ↦ u(x)`;
  * `exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one`: the height
    factorization, the cylinder where `φ(1/2)` is far from zero, the two-sided mass estimate
    `exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow`, and
    the comparison `φ(σ) ≈ φ(1/2)` for `σ` near `1/2` away from the cylinder.

  Naming. Three of the pin's declarations already exist in this port, at this namespace path, with
  a *different* statement, so the port cannot reuse the pin's spelling: the finComponent-pointwise
  `gl_ext` is `eq_of_glArch_eq_of_forall_finComponent_eq` (the port's `gl_ext`, in
  `MaximalCompactFactors`, closes on the `glFin`-equality instead); the `AdeleRing`-specialized
  `continuous_unipotentGL2` is `continuous_unipotentGL2_adeleRing` (the port's
  `continuous_unipotentGL2`, in `ConstantTerm`, is stated over an arbitrary topological ring); and
  the engine keeps its pin name `main`'s statement under
  `exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one`, since the port's
  `AutomorphicForm.main` is `HeightWeylMass`'s engine for the mass estimate. Statements are the
  pin's text verbatim; each rename matches through the checker's content tier.

  Body-level drift, per row (no statement touched):
  * `continuous_finComponent_glFin` is `(continuous_finComponent …).comp (continuous_glFin …)`
    rather than the pin's entry-by-entry `Units.continuous_val.matrix_elem` argument: the pin's
    route forces the elaborator to the *unfolded* `InfiniteAdeleRing × RestrictedProduct …` spelling
    of `AdeleRing`, where the `TopologicalSpace` instance — keyed on the non-reducible `def`s
    `AdeleRing`/`FiniteAdeleRing` — is not found (`synthInstanceFailed` on
    `TopologicalSpace (Matrix (Fin 2) (Fin 2) …)ˣ`, no search goal anywhere: §3.5's
    "instance terms" class, FR-0217's shape). The one-line composite stays inside the frozen
    spelling. `InducedSectionMaximalCompact.lean` carries the same fix.
  * `eq_of_glArch_eq_of_forall_finComponent_eq`: the pin's `ext i j` is `apply Matrix.ext; intro i j`
    (v4.34's `ext` picks a `TopologicalSpace`-rooted extensionality lemma here).
  * `dif_pos`/`dif_neg` are v4.34's `dite_eq_left`/`dite_eq_right`; `exists_finset_fixing`'s
    disjointness step is written in `Disjoint` + `Set.disjoint_left` form, as
    `elim_directed_family_closed` now takes it (the pin's `… = ∅` is the same statement).
  * The engine's three `letI`/`haveI` walls are written `let`/`have`. `linter.style.haveILetI` is a
    default linter that fires on `haveI`/`letI` in a proof of a proposition, and this port carries no
    `set_option linter.*`; `let`/`have` register local instances in Lean 4, so the terms are the same.
  * `omit [NumberField F]` before `compl_le` (the unused-section-variable linter; `F` is used only
    through `𝓞 F`).

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.IwasawaWeylUnipotent
import FLTForHuman.AutomorphicForm.Adelic.HeightWeylMass
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionMaximalCompact
import FLTForHuman.NumberTheory.AdelicHeight

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicHeight
open IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel Filter Topology FLT.SmoothVectors
open scoped NNReal

noncomputable section

namespace AutomorphicForm

open scoped Classical

section IntegralBound

variable (F : Type) [Field F] [NumberField F]

theorem eq_of_glArch_eq_of_forall_finComponent_eq {g h : AdelicGL2 (𝓞 F) F} (h₁ : glArch (𝓞 F) F g = glArch (𝓞 F) F h)
    (h₂ : ∀ v, finComponent (𝓞 F) F v (glFin (𝓞 F) F g) = finComponent (𝓞 F) F v (glFin (𝓞 F) F h)) :
    g = h := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) h₁) i) j
    rwa [glArch_apply, glArch_apply] at this
  · refine RestrictedProduct.ext _ _ fun v => ?_
    have := congrFun (congrFun (congrArg (fun m : GL (Fin 2) (v.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))) (h₂ v)) i) j
    rwa [finComponent_apply, finComponent_apply, glFin_apply, glFin_apply] at this

theorem continuous_finComponent_glFin (v : HeightOneSpectrum (𝓞 F)) :
    Continuous fun g : AdelicGL2 (𝓞 F) F => finComponent (𝓞 F) F v (glFin (𝓞 F) F g) :=
  (continuous_finComponent (𝓞 F) F v).comp (continuous_glFin (𝓞 F) F)

def Cpt : Set (AdelicGL2 (𝓞 F) F) :=
  (adelicMaximalCompact F : Set (AdelicGL2 (𝓞 F) F)) ∩ (finiteAdelicGL2Subgroup F : Set (AdelicGL2 (𝓞 F) F))

theorem isCompact_Cpt : IsCompact (Cpt F) :=
  (isCompact_adelicMaximalCompact F).inter_right (isClosed_finiteAdelicGL2Subgroup F)

theorem mem_Cpt {k : AdelicGL2 (𝓞 F) F} (h1 : glArch (𝓞 F) F k = 1) (h2 : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F) :
    k ∈ Cpt F := by
  refine ⟨⟨h2, fun w => ?_⟩, h1⟩
  rw [h1, map_one]; exact isRowIsometry_one

theorem exists_finset_fixing (φ₀ : AdelicGL2 (𝓞 F) F → ℂ) (hsm : IsKfSmooth F φ₀) :
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
      refine eq_of_glArch_eq_of_forall_finComponent_eq F (by rw [map_one]; exact hk.1.2) fun v => ?_
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
theorem compl_le : (cofinite : Filter (HeightOneSpectrum (𝓞 F))) ≤ 𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ) :=
  Filter.le_principal_iff.mpr S₂.finite_toSet.compl_mem_cofinite

def secP (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :
    RestrictedProduct (fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) (𝓟 ((↑S₂ : Set (HeightOneSpectrum (𝓞 F)))ᶜ)) :=
  ⟨fun v => if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F), by
    rw [Filter.eventually_principal]
    intro v hv
    rw [Set.mem_compl_iff, Finset.mem_coe] at hv
    simp only [dite_eq_right hv]
    exact zero_mem _⟩

def sec (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) : FiniteAdeleRing (𝓞 F) F :=
  RestrictedProduct.inclusion _ _ (compl_le F S₂) (secP F S₂ b)

theorem sec_apply_of_mem (b : ∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) {v : HeightOneSpectrum (𝓞 F)} (hv : v ∈ S₂) :
    sec F S₂ b v = b ⟨v, hv⟩ := by
  change (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F)) = _
  rw [dite_eq_left hv]

theorem continuous_sec : Continuous (sec F S₂) := by
  refine (RestrictedProduct.continuous_inclusion (compl_le F S₂)).comp ?_
  rw [RestrictedProduct.continuous_rng_of_principal_iff_forall]
  intro v
  change Continuous fun b : (∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) => (if h : v ∈ S₂ then (b ⟨v, h⟩ : v.adicCompletion F) else (0 : v.adicCompletion F))
  by_cases hv : v ∈ S₂
  · simp only [dite_eq_left hv]; exact continuous_apply _
  · simp only [dite_eq_right hv]; exact continuous_const

theorem exists_cylinder (ψ : AdeleRing (𝓞 F) F → ℝ) (hψ : Continuous ψ)
    (hloc : ∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → (∀ v ∈ S₂, x.2 v = y.2 v) → ψ x = ψ y)
    (x₀ : AdeleRing (𝓞 F) F) (δ₀ : ℝ) (hδ₀ : 0 ≤ δ₀) (hx₀ : 2 * δ₀ < ψ x₀) :
    ∃ (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (v.adicCompletion F)) (U₀ : Set (InfiniteAdeleRing F)),
      (∀ v ∈ S₂, IsOpen (U v) ∧ (U v).Nonempty) ∧ IsOpen U₀ ∧ U₀.Nonempty ∧
      ∀ x : AdeleRing (𝓞 F) F, x.1 ∈ U₀ → (∀ v ∈ S₂, x.2 v ∈ U v) → δ₀ < ψ x := by
  set e : InfiniteAdeleRing F × (∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) → AdeleRing (𝓞 F) F :=
    fun p => (p.1, sec F S₂ p.2) with he
  have hec : Continuous e := continuous_fst.prodMk ((continuous_sec F S₂).comp continuous_snd)
  set z₀ : InfiniteAdeleRing F × (∀ v : S₂, (v : HeightOneSpectrum (𝓞 F)).adicCompletion F) :=
    (x₀.1, fun v => x₀.2 v) with hz₀
  have hez₀ : ψ (e z₀) = ψ x₀ :=
    hloc _ _ rfl fun v hv => by change sec F S₂ (fun v => x₀.2 v) v = _; rw [sec_apply_of_mem F S₂ _ hv]
  have hO : IsOpen ((ψ ∘ e) ⁻¹' Set.Ioi δ₀) := (hψ.comp hec).isOpen_preimage _ isOpen_Ioi
  have hz₀mem : z₀ ∈ (ψ ∘ e) ⁻¹' Set.Ioi δ₀ := by
    change δ₀ < ψ (e z₀); rw [hez₀]; linarith

  obtain ⟨U₀, W, hU₀, hW, hz1, hz2, hsub⟩ := isOpen_prod_iff.mp hO z₀.1 z₀.2 hz₀mem
  obtain ⟨u, hu, hIsub⟩ := isOpen_pi_iff'.mp hW z₀.2 hz2
  refine ⟨fun v => if h : v ∈ S₂ then u ⟨v, h⟩ else Set.univ, U₀, ?_, hU₀, ⟨_, hz1⟩, ?_⟩
  · intro v hv
    simp only [dite_eq_left hv]
    exact ⟨(hu _).1, ⟨_, (hu _).2⟩⟩
  · intro x hx1 hx2
    have hmem : (x.1, fun v : S₂ => x.2 v) ∈ U₀ ×ˢ W := by
      refine ⟨hx1, hIsub ?_⟩
      rw [Set.mem_univ_pi]
      intro i
      have := hx2 i i.2
      simp only [dite_eq_left i.2] at this
      exact this
    have h := hsub hmem
    change δ₀ < ψ (e (x.1, fun v : S₂ => x.2 v)) at h
    rwa [hloc (e (x.1, fun v : S₂ => x.2 v)) x rfl fun v hv => by
      change sec F S₂ (fun v : S₂ => x.2 v) v = _; rw [sec_apply_of_mem F S₂ _ hv]] at h

theorem eventually_norm_sub_lt (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (hjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)
    {Kc : Set (AdelicGL2 (𝓞 F) F)} (hK : IsCompact Kc) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ σ : ℝ in 𝓝 (1 / 2 : ℝ), ∀ k ∈ Kc, ‖φ (σ : ℂ) k - φ (1 / 2) k‖ < ε := by
  set D : ℝ × AdelicGL2 (𝓞 F) F → ℝ := fun p => ‖φ (p.1 : ℂ) p.2 - φ (1 / 2) p.2‖ with hD
  have hDc : Continuous D := by
    refine Continuous.norm (Continuous.sub ?_ ?_)
    · exact hjc.comp ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)
    · exact hjc.comp (continuous_const.prodMk continuous_snd)
  have hO : IsOpen (D ⁻¹' Set.Iio ε) := hDc.isOpen_preimage _ isOpen_Iio
  have hsub : ({(1 / 2 : ℝ)} : Set ℝ) ×ˢ Kc ⊆ D ⁻¹' Set.Iio ε := by
    rintro ⟨σ, k⟩ ⟨hσ, -⟩
    rw [Set.mem_singleton_iff] at hσ
    subst hσ
    change ‖φ ((1 / 2 : ℝ) : ℂ) k - φ (1 / 2) k‖ < ε
    have : ((1 / 2 : ℝ) : ℂ) = 1 / 2 := by push_cast; ring
    rw [this, sub_self, norm_zero]; exact hε
  obtain ⟨u, v, hu, -, hmu, hKv, huv⟩ := generalized_tube_lemma isCompact_singleton hK hO hsub
  filter_upwards [hu.mem_nhds (hmu (Set.mem_singleton _))] with σ hσ k hk
  exact huv (Set.mk_mem_prod hσ (hKv hk))

theorem continuous_unipotentGL2_adeleRing :
    Continuous (fun y : AdeleRing (𝓞 F) F => (unipotentGL2 y : AdelicGL2 (𝓞 F) F)) := by
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · have : ∀ y : AdeleRing (𝓞 F) F, (↑((unipotentGL2 y : AdelicGL2 (𝓞 F) F)⁻¹) :
        Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) = !![1, -y; 0, 1] := fun y => rfl
    simp_rw [this]
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop

theorem exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one :
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
      (_hpos : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0)
      (_hex : ∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        δ ≤ (((σ : ℂ) - 1 / 2) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by
  intro α hα φ hφ hφK hφf hφjc hφhol hpos hex
  let adeleBorelF : MeasurableSpace (AdeleRing (𝓞 F) F) := adeleBorel (𝓞 F) F
  have borelSpaceAdele : BorelSpace (AdeleRing (𝓞 F) F) := borelSpace_adeleBorel (𝓞 F) F
  have isAddHaarAdele : (adelicAddHaar (𝓞 F) F).IsAddHaarMeasure := isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hφc : ∀ s, Continuous (φ s) := fun s => hφjc.comp (continuous_const.prodMk continuous_id)

  obtain ⟨-, hunit, hsph⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hint := AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half F hα 1 1 hunit hunit

  obtain ⟨κ, hκc, hκK, hκB, hκloc, hκarch, hκφ⟩ := AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent F hα
  set Hf : AdeleRing (𝓞 F) F → ℝ := fun x => adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) with hHf
  have hHpos : ∀ x, 0 < Hf x := fun x => adelicHeight_pos _
  have hwc : Continuous fun x : AdeleRing (𝓞 F) F => (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x :=
    continuous_const.mul (continuous_unipotentGL2_adeleRing F)
  have hHc : Continuous Hf := (NumberField.AdelicHeight.continuous_adelicHeight F).comp hwc

  obtain ⟨S₂, hS₂⟩ := exists_finset_fixing F (φ (1 / 2)) (hφf (1 / 2))
  set ψ₀ : AdeleRing (𝓞 F) F → ℝ := fun x => (φ (1 / 2) (κ x)).re with hψ₀
  have hψ₀c : Continuous ψ₀ := Complex.continuous_re.comp ((hφc _).comp hκc)
  have hψ₀nn : ∀ x, 0 ≤ ψ₀ x := fun x => (hpos (κ x) (hκK x).1 (hκK x).2).1
  have hψ₀loc : ∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → (∀ v ∈ S₂, x.2 v = y.2 v) → ψ₀ x = ψ₀ y := by
    intro x y h1 h2
    simp only [hψ₀]
    set k' := (κ x)⁻¹ * κ y with hk'
    have e : κ y = κ x * k' := by rw [hk', mul_inv_cancel_left]
    have hk1 : glArch (𝓞 F) F k' = 1 := by rw [hk', map_mul, map_inv, hκarch x y h1, inv_mul_cancel]
    have hk2 : glFin (𝓞 F) F k' ∈ finiteIntegralGL2 (𝓞 F) F := by
      rw [hk', map_mul, map_inv]; exact mul_mem (inv_mem (hκK x).1) (hκK y).1
    have hk3 : ∀ v ∈ S₂, finComponent (𝓞 F) F v (glFin (𝓞 F) F k') = 1 := by
      intro v hv; rw [hk', map_mul, map_inv, map_mul, map_inv, hκloc x y v (h2 v hv), inv_mul_cancel]
    rw [e, hS₂ k' hk1 hk2 hk3]

  have hhalf : ∀ x, φ (1 / 2) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) = ((Hf x : ℝ) : ℂ) * φ (1 / 2) (κ x) := by
    intro x
    have := hκφ (1 / 2) (φ (1 / 2)) (hφ _) x
    rw [this]
    congr 1
    have e : ((1 / 2 : ℂ) + 1 / 2) = ((1 : ℝ) : ℂ) := by push_cast; ring
    rw [e, ← Complex.ofReal_cpow (hHpos x).le, Real.rpow_one]

  obtain ⟨k₀, hk₀1, hk₀2, hk₀ne⟩ := hex
  obtain ⟨x₀, hx₀⟩ := AutomorphicForm.exists_apply_weylInv_mul_unipotentGL2_ne_zero_of_isInducedSection_of_isKfSmooth F hα
    (1 / 2) (φ (1 / 2)) (hφ _) (hφc _) (hφf _) ⟨k₀, hk₀ne⟩
  have hψ₀x₀ : 0 < ψ₀ x₀ := by
    have hne : φ (1 / 2) (κ x₀) ≠ 0 := by
      intro h0; apply hx₀; rw [hhalf, h0, mul_zero]
    have him : (φ (1 / 2) (κ x₀)).im = 0 := (hpos (κ x₀) (hκK x₀).1 (hκK x₀).2).2
    rcases (hψ₀nn x₀).lt_or_eq with h | h
    · exact h
    · exfalso; apply hne; exact Complex.ext (by simpa [hψ₀] using h.symm) (by simpa using him)
  set δ₀ : ℝ := ψ₀ x₀ / 4 with hδ₀
  have hδ₀pos : 0 < δ₀ := by positivity
  obtain ⟨U, U₀, hU, hU₀o, hU₀ne, hcyl⟩ := exists_cylinder F S₂ ψ₀ hψ₀c hψ₀loc x₀ δ₀ hδ₀pos.le (by rw [hδ₀]; linarith)
  set cyl : Set (AdeleRing (𝓞 F) F) := {x | x.1 ∈ U₀ ∧ ∀ v ∈ S₂, x.2 v ∈ U v} with hcyl_def
  have hcylo : IsOpen cyl := by
    have h1 : IsOpen {x : AdeleRing (𝓞 F) F | x.1 ∈ U₀} := hU₀o.preimage continuous_fst
    have h2 : IsOpen {x : AdeleRing (𝓞 F) F | ∀ v ∈ S₂, x.2 v ∈ U v} := by
      have : {x : AdeleRing (𝓞 F) F | ∀ v ∈ S₂, x.2 v ∈ U v} = ⋂ v ∈ S₂, {x : AdeleRing (𝓞 F) F | x.2 v ∈ U v} := by
        ext x; simp
      rw [this]
      exact isOpen_biInter_finset fun v hv => (hU v hv).1.preimage ((RestrictedProduct.continuous_eval v).comp continuous_snd)
    exact h1.inter h2
  have hcylm : MeasurableSet cyl := hcylo.measurableSet

  obtain ⟨m₀, m₁, hm₀, hmass⟩ :=
    AutomorphicForm.exists_pos_eventually_le_sub_one_half_mul_setIntegral_adelicHeight_weyl_unipotent_rpow F S₂ U hU U₀ ⟨hU₀o, hU₀ne⟩

  set ε : ℝ := δ₀ * m₀ / (2 * (|m₁| + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hεm : ε * |m₁| ≤ δ₀ * m₀ / 2 := by
    rw [hε]
    have h1 : 0 < |m₁| + 1 := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [abs_nonneg m₁, hδ₀pos, hm₀]
  refine ⟨δ₀ * m₀ / 2, by positivity, ?_⟩

  have hunif := eventually_norm_sub_lt F φ hφjc (isCompact_adelicMaximalCompact F) ε hεpos
  filter_upwards [hmass, nhdsWithin_le_nhds hunif, self_mem_nhdsWithin] with σ hσmass hσunif hσgt
  rw [Set.mem_Ioi] at hσgt
  have hσre : (1 / 2 : ℝ) < ((σ : ℂ)).re := by simpa using hσgt

  have hIφ : Integrable (fun x => φ (σ : ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)) (adelicAddHaar (𝓞 F) F) := by
    have := hint (σ : ℂ) hσre (φ σ) (hφ σ) (hφc σ) 1
    simpa [mul_one] using this
  set hσ : AdeleRing (𝓞 F) F → ℝ := fun x => Hf x ^ (σ + 1 / 2) with hhσ
  have hcpow : ∀ x, ((Hf x : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) = ((hσ x : ℝ) : ℂ) := by
    intro x
    rw [hhσ]; dsimp only
    rw [Complex.ofReal_cpow (hHpos x).le]; push_cast; ring_nf
  have hIh : Integrable hσ (adelicAddHaar (𝓞 F) F) := by
    have hc : Continuous fun g : AdelicGL2 (𝓞 F) F => ((adelicHeight F g : ℝ) : ℂ) ^ ((σ : ℂ) + 1 / 2) :=
      (Complex.continuous_ofReal.comp (NumberField.AdelicHeight.continuous_adelicHeight F)).cpow continuous_const
        fun g => Or.inl (by exact_mod_cast adelicHeight_pos g)
    have := hint (σ : ℂ) hσre _ (hsph hα σ) hc 1
    have h2 : Integrable (fun x => ((hσ x : ℝ) : ℂ)) (adelicAddHaar (𝓞 F) F) := by
      refine this.congr (Filter.Eventually.of_forall fun x => ?_)
      simp only [mul_one]; exact hcpow x
    simpa using h2.re

  have hψσ : ∀ x, (φ (σ : ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)).re = hσ x * (φ (σ : ℂ) (κ x)).re := by
    intro x
    rw [hκφ (σ : ℂ) (φ σ) (hφ σ) x, hcpow x, Complex.re_ofReal_mul]
  have hlow : ∀ x, δ₀ * cyl.indicator hσ x - ε * hσ x ≤ (φ (σ : ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)).re := by
    intro x
    rw [hψσ x]
    have hhx : 0 ≤ hσ x := Real.rpow_nonneg (hHpos x).le _
    have hclose : (φ (1 / 2) (κ x)).re - ε ≤ (φ (σ : ℂ) (κ x)).re := by
      have h := hσunif (κ x) (hκK x)
      have := Complex.abs_re_le_norm (φ (σ : ℂ) (κ x) - φ (1 / 2) (κ x))
      rw [Complex.sub_re] at this
      have := (abs_le.mp (this.trans h.le)).1
      linarith
    by_cases hx : x ∈ cyl
    · rw [Set.indicator_of_mem hx]
      have hge : δ₀ ≤ (φ (1 / 2) (κ x)).re := (hcyl x hx.1 hx.2).le
      nlinarith
    · rw [Set.indicator_of_notMem hx, mul_zero, zero_sub]
      have hge : 0 ≤ (φ (1 / 2) (κ x)).re := hψ₀nn x
      nlinarith

  have hIlow : Integrable (fun x => δ₀ * cyl.indicator hσ x - ε * hσ x) (adelicAddHaar (𝓞 F) F) :=
    ((hIh.indicator hcylm).const_mul δ₀).sub (hIh.const_mul ε)
  have hre : (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re =
      ∫ x, (φ (σ : ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)).re ∂(adelicAddHaar (𝓞 F) F) := by
    rw [weylIntertwiningIntegral]
    simp only [mul_one]
    exact (integral_re hIφ).symm
  have hmono := integral_mono hIlow hIφ.re hlow
  rw [integral_sub ((hIh.indicator hcylm).const_mul δ₀) (hIh.const_mul ε), integral_const_mul, integral_const_mul,
    integral_indicator hcylm] at hmono

  obtain ⟨hm0, hm1⟩ := hσmass
  have hσpos : 0 < σ - 1 / 2 := by linarith
  have key : δ₀ * m₀ / 2 ≤ (σ - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by
    rw [hre]
    have h1 : (σ - 1 / 2) * (δ₀ * ∫ x in cyl, hσ x ∂(adelicAddHaar (𝓞 F) F) - ε * ∫ x, hσ x ∂(adelicAddHaar (𝓞 F) F)) ≤
        (σ - 1 / 2) * ∫ x, (φ (σ : ℂ) ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x)).re ∂(adelicAddHaar (𝓞 F) F) :=
      mul_le_mul_of_nonneg_left hmono hσpos.le
    have h2 : δ₀ * m₀ ≤ δ₀ * ((σ - 1 / 2) * ∫ x in cyl, hσ x ∂(adelicAddHaar (𝓞 F) F)) :=
      mul_le_mul_of_nonneg_left hm0 hδ₀pos.le
    have h3 : ε * ((σ - 1 / 2) * ∫ x, hσ x ∂(adelicAddHaar (𝓞 F) F)) ≤ ε * |m₁| :=
      mul_le_mul_of_nonneg_left (hm1.trans (le_abs_self m₁)) hεpos.le
    nlinarith

  have hsc : (((σ : ℂ) - 1 / 2) * weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re =
      (σ - 1 / 2) * (weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re := by
    have : ((σ : ℂ) - 1 / 2) = ((σ - 1 / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  rw [hsc]; exact key

end IntegralBound

theorem exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family
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
      (_hpos : ∀ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
          0 ≤ (φ (1 / 2) k).re ∧ (φ (1 / 2) k).im = 0)
      (_hex : ∃ k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) ∧
          φ (1 / 2) k ≠ 0),
    letI := NumberField.AdelicHaar.adeleBorel (𝓞 F) F
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ σ : ℝ in 𝓝[>] (1 / 2 : ℝ),
        δ ≤ (((σ : ℂ) - 1 / 2) *
          weylIntertwiningIntegral (𝓞 F) F (adelicAddHaar (𝓞 F) F) (φ (σ : ℂ)) 1).re :=
  exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one F

end AutomorphicForm

end
