/-
  The `K`-dictionary of an induced section: its value, its continuity, and its height.

  An induced section of a character pair is determined, at every point, by its value at the `K`-part of
  a Borel decomposition, and its analytic properties transfer from the maximal compact to the group:
  this module carries the five statements that make that precise.

  * `IsInducedSection.eq_of_eqOn_maximalCompact` — a section that is an induced section and agrees with
    another on the maximal compact **is** that section;
  * `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` — continuity on the maximal
    compact transfers to continuity everywhere;
  * `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` — the same from the pointwise Borel form;
  * `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` — the section's norm is bounded by a
    constant times a power of the adelic height, so that only the height, not the group element, matters;
  * `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` — a flat family is invariant in
    its `k`-argument on `maximalCompactAway S`.

  The common input is the same in all five: write the point by the Borel decomposition, apply the
  induced-section law to move the Borel factor out as a character value, and read the rest off the
  maximal compact.

  Transcribed from five pin `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`):

  * `P2M/Sol/S_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact.lean`
  * `P2M/Sol/S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.lean`
  * `P2M/Sol/S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn.lean`
  * `P2M/Sol/S_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection.lean`
  * `P2M/Sol/S_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family.lean`

  The pin's file-level labels (`ICTProof`, `ICGProof`, `SphericalCollapse`) are proof-search artefacts
  and become the subject namespaces below. The pin files import `Mathlib`; this module names the modules
  they need instead.

  **Visibility follows the pin's.** Row 5 is a flat public surface, rows 4 and 6 have a small `private`
  prelude, and rows 7 and 8 are single public declarations.

  **Wiring.** `spec/check_port.py` owns every public declaration here: the five wrappers and the five
  `S_` files are the wire.
  spec-pin: Theorems/Thm_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsInducedSection_eq_of_eqOn_maximalCompact.lean
  spec-pin: Theorems/Thm_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_continuousOn_of_isInducedSection_of_continuousOn_maximalCompact.lean
  spec-pin: Theorems/Thm_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.InducedSection
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionFlat
import FLTForHuman.AutomorphicForm.Adelic.InducedSectionMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamilyTheorems
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.AdelicMaximalCompact
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Set
import FLTForHuman.AutomorphicForm.Adelic.AdelicIwasawa
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.MeasureTheory.Group.FundamentalDomain

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField MeasureTheory Matrix
open NumberField.InfinitePlace NumberField.AdelicLevel NumberField.AdelicHeight
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain.HeightOneSpectrum
open scoped NNReal

namespace AutomorphicForm

namespace LocalIntertwining

namespace SectionHeightBound

variable (F : Type) [Field F] [NumberField F]

private theorem adelicHeight_mul_of_mem (g : AdelicGL2 (𝓞 F) F) {k : AdelicGL2 (𝓞 F) F}
    (hkf : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hkinf : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, archHeight_mul_rowIsometry F _ hkinf, finHeight_mul_of_mem F _ hkf]

private theorem adelicHeight_one' : adelicHeight F (1 : AdelicGL2 (𝓞 F) F) = 1 := by
  unfold adelicHeight
  rw [map_one, map_one, archHeight_one, finHeight_eq_one_of_mem (one_mem _), mul_one]

theorem _root_.AutomorphicForm.exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ x, 0 < ((α x : ℝˣ) : ℝ))
      (μ ν : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
      (_hμ : IsUnitaryChar (𝓞 F) F μ) (_hν : IsUnitaryChar (𝓞 F) F ν)
      (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
      (_hφ : IsInducedSection (𝓞 F) F (etaFst μ α hα s) (etaSnd ν α hα s) φ)
      (_hφc : Continuous φ),
    ∃ C : ℝ, ∀ g : AdelicGL2 (𝓞 F) F, ‖φ g‖ ≤ C * adelicHeight F g ^ (s.re + 1 / 2) := by
  intro α hα μ ν hμ hν s φ hφ hφc

  obtain ⟨C₀, hC₀⟩ := (isCompact_adelicMaximalCompact F).exists_bound_of_continuousOn hφc.continuousOn
  obtain ⟨-, h1u, hind⟩ := AutomorphicForm.isInducedSection_adelicHeight_cpow F
  have hflat := hind hα s
  refine ⟨C₀, fun g => ?_⟩
  obtain ⟨b, k, hb, hkf, hkinf, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hk : k ∈ adelicMaximalCompact F := ⟨hkf, hkinf⟩

  have h1 := hφ b hb k
  have h2 := hflat b hb 1
  simp only [mul_one, adelicHeight_one' F, Complex.ofReal_one, Complex.one_cpow] at h2

  have nF : ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), IsUnitaryChar (𝓞 F) F χ → ∀ x,
      ‖((etaFst χ α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (s.re + 1 / 2) :=
    fun χ hχ x => norm_etaFst_apply_of_unitary hχ α hα s x
  have nS : ∀ (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ), IsUnitaryChar (𝓞 F) F χ → ∀ x,
      ‖((etaSnd χ α hα s x : ℂˣ) : ℂ)‖ = ((α x : ℝˣ) : ℝ) ^ (-(s + 1 / 2)).re := by
    intro χ hχ x
    rw [etaSnd_apply, Units.val_mul, norm_mul, hχ x, one_mul, norm_cpowChar_apply]
  have hnorm : ‖φ (b * k)‖ = ‖((adelicHeight F b : ℝ) : ℂ) ^ (s + 1 / 2)‖ * ‖φ k‖ := by
    rw [h1, h2, norm_mul, norm_mul, norm_mul, nF μ hμ, nS ν hν, nF 1 h1u, nS 1 h1u]
  rw [hnorm, Complex.norm_cpow_eq_rpow_re_of_pos (adelicHeight_pos b), adelicHeight_mul_of_mem F b hkf hkinf,
    mul_comm]
  have hre : (s + 1 / 2).re = s.re + 1 / 2 := by simp
  rw [hre]
  exact mul_le_mul_of_nonneg_right (hC₀ k hk) (Real.rpow_nonneg (adelicHeight_pos b).le _)

end SectionHeightBound

namespace ContinuousOnMaximalCompact

open Filter Topology

variable (F : Type) [Field F] [NumberField F]

theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F))
      = (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val).matrix_elem 1 0)

theorem tendsto_units {α M : Type*} [Monoid M] [TopologicalSpace M] {l : Filter α} {u : α → Mˣ} {u₀ : Mˣ}
    (h1 : Tendsto (fun a => ((u a : Mˣ) : M)) l (𝓝 (u₀ : M)))
    (h2 : Tendsto (fun a => (((u a)⁻¹ : Mˣ) : M)) l (𝓝 ((u₀⁻¹ : Mˣ) : M))) : Tendsto u l (𝓝 u₀) := by
  rw [Units.isEmbedding_embedProduct.tendsto_nhds_iff]
  show Tendsto (fun a => Units.embedProduct M (u a)) l (𝓝 (Units.embedProduct M u₀))
  simp only [Units.embedProduct_apply]
  exact h1.prodMk_nhds ((MulOpposite.continuous_op.tendsto _).comp h2)

theorem main
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (χ₁ χ₂ : X → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (hχ₁ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₁ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (hχ₂ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₂ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (f : X → AdelicGL2 (𝓞 F) F → ℂ)
    (hf : ∀ x ∈ U, IsInducedSection (𝓞 F) F (χ₁ x) (χ₂ x) (f x))
    (hfK : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by
  classical

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  have hKc_cpt : IsCompact Kc := isCompact_adelicMaximalCompact F
  have hkI_mem : ∀ g, kI g ∈ Kc := fun g => ⟨hkI1 g, hkI2 g⟩
  have hbI_eq : ∀ g, bI g = g * (kI g)⁻¹ := fun g => by
    rw [eq_mul_inv_iff_mul_eq]; exact (hdecI g).symm
  rw [(hU.prod isOpen_univ).continuousOn_iff]
  rintro ⟨x₀, g₀⟩ ⟨hx₀, -⟩
  rw [continuousAt_iff_ultrafilter]
  intro 𝒰 h𝒰

  obtain ⟨k₁, hk₁, hk𝒰⟩ : ∃ k₁ ∈ Kc, (↑(𝒰.map (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2)) : Filter _) ≤ 𝓝 k₁ := by
    apply hKc_cpt.ultrafilter_le_nhds
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' (fun p => hkI_mem p.2)
  have hk : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2) 𝒰 (𝓝 k₁) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hk𝒰
  have hx : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.1) 𝒰 (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, g₀)).mono_left h𝒰
  have hg : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.2) 𝒰 (𝓝 g₀) :=
    (continuous_snd.tendsto (x₀, g₀)).mono_left h𝒰

  set b₁ : AdelicGL2 (𝓞 F) F := g₀ * k₁⁻¹ with hb₁def
  have hb : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) 𝒰 (𝓝 b₁) := by
    have : (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) = fun p => p.2 * (kI p.2)⁻¹ := by
      funext p; exact hbI_eq p.2
    rw [this]
    exact hg.mul hk.inv
  have hb₁ : b₁ ∈ adelicBorel (𝓞 F) F :=
    (isClosed_adelicBorel F).mem_of_tendsto hb (Filter.Eventually.of_forall (fun p => hbI p.2))
  have hbinv : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (bI p.2)⁻¹) 𝒰 (𝓝 b₁⁻¹) := hb.inv

  have hval : ∀ (i : Fin 2), Tendsto (fun p : X × AdelicGL2 (𝓞 F) F =>
      ((bI p.2 : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i) 𝒰
        (𝓝 (((b₁ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)) :=
    fun i => (((Units.continuous_val).matrix_elem i i).tendsto b₁).comp hb
  have hinv : ∀ (i : Fin 2), Tendsto (fun p : X × AdelicGL2 (𝓞 F) F =>
      (((bI p.2)⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i) 𝒰
        (𝓝 (((b₁⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i i)) :=
    fun i => (((Units.continuous_val).matrix_elem i i).tendsto b₁⁻¹).comp hbinv
  have hFst : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => borelDiagFst ⟨bI p.2, hbI p.2⟩) 𝒰
      (𝓝 (borelDiagFst ⟨b₁, hb₁⟩)) :=
    tendsto_units (hval 0) (hinv 0)
  have hSnd : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => borelDiagSnd ⟨bI p.2, hbI p.2⟩) 𝒰
      (𝓝 (borelDiagSnd ⟨b₁, hb₁⟩)) :=
    tendsto_units (hval 1) (hinv 1)

  have hxU : ∀ᶠ p in (𝒰 : Filter (X × AdelicGL2 (𝓞 F) F)), p.1 ∈ U := hx (hU.mem_nhds hx₀)

  have hχ₁t : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => ((χ₁ p.1 (borelDiagFst ⟨bI p.2, hbI p.2⟩) : ℂˣ) : ℂ)) 𝒰
      (𝓝 ((χ₁ x₀ (borelDiagFst ⟨b₁, hb₁⟩) : ℂˣ) : ℂ)) := by
    have hq : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (p.1, borelDiagFst ⟨bI p.2, hbI p.2⟩)) 𝒰
        (𝓝[U ×ˢ Set.univ] (x₀, borelDiagFst ⟨b₁, hb₁⟩)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hx.prodMk_nhds hFst, ?_⟩
      filter_upwards [hxU] with p hp
      exact ⟨hp, Set.mem_univ _⟩
    exact (hχ₁ (x₀, borelDiagFst ⟨b₁, hb₁⟩) ⟨hx₀, Set.mem_univ _⟩).tendsto.comp hq
  have hχ₂t : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => ((χ₂ p.1 (borelDiagSnd ⟨bI p.2, hbI p.2⟩) : ℂˣ) : ℂ)) 𝒰
      (𝓝 ((χ₂ x₀ (borelDiagSnd ⟨b₁, hb₁⟩) : ℂˣ) : ℂ)) := by
    have hq : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (p.1, borelDiagSnd ⟨bI p.2, hbI p.2⟩)) 𝒰
        (𝓝[U ×ˢ Set.univ] (x₀, borelDiagSnd ⟨b₁, hb₁⟩)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hx.prodMk_nhds hSnd, ?_⟩
      filter_upwards [hxU] with p hp
      exact ⟨hp, Set.mem_univ _⟩
    exact (hχ₂ (x₀, borelDiagSnd ⟨b₁, hb₁⟩) ⟨hx₀, Set.mem_univ _⟩).tendsto.comp hq
  have hfKt : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 (kI p.2)) 𝒰 (𝓝 (f x₀ k₁)) := by
    have hq : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (p.1, kI p.2)) 𝒰 (𝓝[U ×ˢ Kc] (x₀, k₁)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hx.prodMk_nhds hk, ?_⟩
      filter_upwards [hxU] with p hp
      exact ⟨hp, hkI_mem p.2⟩
    exact (hfK (x₀, k₁) ⟨hx₀, hk₁⟩).tendsto.comp hq

  have heq : (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) =ᶠ[(𝒰 : Filter _)]
      fun p => ((χ₁ p.1 (borelDiagFst ⟨bI p.2, hbI p.2⟩) : ℂˣ) : ℂ)
        * ((χ₂ p.1 (borelDiagSnd ⟨bI p.2, hbI p.2⟩) : ℂˣ) : ℂ) * f p.1 (kI p.2) := by
    filter_upwards [hxU] with p hp
    show f p.1 p.2 = _
    conv_lhs => rw [hdecI p.2]
    exact hf p.1 hp (bI p.2) (hbI p.2) (kI p.2)
  have hlim : f x₀ g₀ = ((χ₁ x₀ (borelDiagFst ⟨b₁, hb₁⟩) : ℂˣ) : ℂ)
      * ((χ₂ x₀ (borelDiagSnd ⟨b₁, hb₁⟩) : ℂˣ) : ℂ) * f x₀ k₁ := by
    have hg₀ : g₀ = b₁ * k₁ := by rw [hb₁def, inv_mul_cancel_right]
    conv_lhs => rw [hg₀]
    exact hf x₀ hx₀ b₁ hb₁ k₁
  show Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) 𝒰 (𝓝 (f x₀ g₀))
  rw [hlim]
  exact ((hχ₁t.mul hχ₂t).mul hfKt).congr' heq.symm

theorem _root_.AutomorphicForm.continuousOn_of_isInducedSection_of_continuousOn_maximalCompact
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (χ₁ χ₂ : X → ((AdeleRing (𝓞 F) F)ˣ →* ℂˣ))
    (_hχ₁ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₁ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (_hχ₂ : ContinuousOn (fun p : X × (AdeleRing (𝓞 F) F)ˣ => ((χ₂ p.1 p.2 : ℂˣ) : ℂ)) (U ×ˢ Set.univ))
    (f : X → AdelicGL2 (𝓞 F) F → ℂ)
    (_hf : ∀ x ∈ U, IsInducedSection (𝓞 F) F (χ₁ x) (χ₂ x) (f x))
    (_hfK : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2)
      (U ×ˢ {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) :=
  main F U _hU χ₁ χ₂ _hχ₁ _hχ₂ f _hf _hfK

end ContinuousOnMaximalCompact

namespace ContinuousOnBorel

open Filter Topology

variable (F : Type) [Field F] [NumberField F]

private theorem isClosed_adelicBorel : IsClosed (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) := by
  have : (adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F))
      = (fun g : AdelicGL2 (𝓞 F) F => (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0) ⁻¹' {0} := by
    ext g; rfl
  rw [this]
  exact isClosed_singleton.preimage ((Units.continuous_val).matrix_elem 1 0)

private theorem main
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsOpen U)
    (f : X → AdelicGL2 (𝓞 F) F → ℂ) (Φ : X → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (hΦ : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.1 p.2.1 p.2.2)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (hf : ∀ x ∈ U, ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      f x (b * k) = Φ x b k) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) := by
  classical

  choose bI kI hbI hkI1 hkI2 hdecI using fun g : AdelicGL2 (𝓞 F) F => AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  set Kc : Set (AdelicGL2 (𝓞 F) F) := {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))} with hKc
  have hKc_cpt : IsCompact Kc := isCompact_adelicMaximalCompact F
  have hkI_mem : ∀ g, kI g ∈ Kc := fun g => ⟨hkI1 g, hkI2 g⟩
  have hbI_eq : ∀ g, bI g = g * (kI g)⁻¹ := fun g => by
    rw [eq_mul_inv_iff_mul_eq]; exact (hdecI g).symm
  rw [(hU.prod isOpen_univ).continuousOn_iff]
  rintro ⟨x₀, g₀⟩ ⟨hx₀, -⟩
  rw [continuousAt_iff_ultrafilter]
  intro 𝒰 h𝒰

  obtain ⟨k₁, hk₁, hk𝒰⟩ : ∃ k₁ ∈ Kc, (↑(𝒰.map (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2)) : Filter _) ≤ 𝓝 k₁ := by
    apply hKc_cpt.ultrafilter_le_nhds
    rw [Ultrafilter.coe_map, Filter.le_principal_iff, Filter.mem_map]
    exact Filter.univ_mem' (fun p => hkI_mem p.2)
  have hk : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => kI p.2) 𝒰 (𝓝 k₁) := by
    rw [Tendsto, ← Ultrafilter.coe_map]; exact hk𝒰
  have hx : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.1) 𝒰 (𝓝 x₀) :=
    (continuous_fst.tendsto (x₀, g₀)).mono_left h𝒰
  have hg : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => p.2) 𝒰 (𝓝 g₀) :=
    (continuous_snd.tendsto (x₀, g₀)).mono_left h𝒰

  set b₁ : AdelicGL2 (𝓞 F) F := g₀ * k₁⁻¹ with hb₁def
  have hb : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) 𝒰 (𝓝 b₁) := by
    have : (fun p : X × AdelicGL2 (𝓞 F) F => bI p.2) = fun p => p.2 * (kI p.2)⁻¹ := by
      funext p; exact hbI_eq p.2
    rw [this]
    exact hg.mul hk.inv
  have hb₁ : b₁ ∈ adelicBorel (𝓞 F) F :=
    (isClosed_adelicBorel F).mem_of_tendsto hb (Filter.Eventually.of_forall (fun p => hbI p.2))

  have hxU : ∀ᶠ p in (𝒰 : Filter (X × AdelicGL2 (𝓞 F) F)), p.1 ∈ U := hx (hU.mem_nhds hx₀)

  have hΦt : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => Φ p.1 (bI p.2) (kI p.2)) 𝒰 (𝓝 (Φ x₀ b₁ k₁)) := by
    have hq : Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => (p.1, bI p.2, kI p.2)) 𝒰
        (𝓝[U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ Kc)] (x₀, b₁, k₁)) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨hx.prodMk_nhds (hb.prodMk_nhds hk), ?_⟩
      filter_upwards [hxU] with p hp
      exact ⟨hp, hbI p.2, hkI_mem p.2⟩
    exact (hΦ (x₀, b₁, k₁) ⟨hx₀, hb₁, hk₁⟩).tendsto.comp hq

  have heq : (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) =ᶠ[(𝒰 : Filter _)]
      fun p => Φ p.1 (bI p.2) (kI p.2) := by
    filter_upwards [hxU] with p hp
    show f p.1 p.2 = _
    conv_lhs => rw [hdecI p.2]
    exact hf p.1 hp (bI p.2) (hbI p.2) (kI p.2) (hkI1 p.2) (hkI2 p.2)
  have hlim : f x₀ g₀ = Φ x₀ b₁ k₁ := by
    have hg₀ : g₀ = b₁ * k₁ := by rw [hb₁def, inv_mul_cancel_right]
    conv_lhs => rw [hg₀]
    exact hf x₀ hx₀ b₁ hb₁ k₁ hk₁.1 hk₁.2
  show Tendsto (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) 𝒰 (𝓝 (f x₀ g₀))
  rw [hlim]
  exact hΦt.congr' heq.symm

theorem _root_.AutomorphicForm.continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn
    (F : Type) [Field F] [NumberField F]
    {X : Type*} [TopologicalSpace X] (U : Set X) (_hU : IsOpen U)
    (f : X → AdelicGL2 (𝓞 F) F → ℂ) (Φ : X → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F → ℂ)
    (_hΦ : ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F × AdelicGL2 (𝓞 F) F => Φ p.1 p.2.1 p.2.2)
      (U ×ˢ ((adelicBorel (𝓞 F) F : Set (AdelicGL2 (𝓞 F) F)) ×ˢ
        {k | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
          ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))})))
    (_hf : ∀ x ∈ U, ∀ b ∈ adelicBorel (𝓞 F) F, ∀ k : AdelicGL2 (𝓞 F) F,
      glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
      f x (b * k) = Φ x b k) :
    ContinuousOn (fun p : X × AdelicGL2 (𝓞 F) F => f p.1 p.2) (U ×ˢ Set.univ) :=
  main F U _hU f Φ _hΦ _hf

end ContinuousOnBorel

namespace FlatFamilyKInvariance

open Filter Topology FLT.SmoothVectors in
theorem _root_.AutomorphicForm.exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family
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
          φ s k = φ s' k),
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)),
      ∀ (s : ℂ) (g k : AdelicGL2 (𝓞 F) F), k ∈ maximalCompactAway F S₀ → φ s (g * k) = φ s g := by
  intro α hα φ hφ hφK hφf hφjc hφhol hφflat

  have hv := hφf 0
  rw [isKfSmooth_iff, isSmoothVector_iff_isOpen_stabilizer] at hv
  obtain ⟨W, hWopen, hWpre⟩ := isOpen_induced_iff.mp hv
  have h1W : (1 : AdelicGL2 (𝓞 F) F) ∈ W := by
    have : (⟨1, (finiteAdelicGL2Subgroup F).one_mem⟩ : finiteAdelicGL2Subgroup F)
        ∈ (Subtype.val ⁻¹' W : Set (finiteAdelicGL2Subgroup F)) := by
      rw [hWpre]
      exact (MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ 0))).one_mem
    exact this
  obtain ⟨S₀, hS₀⟩ := AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one F W
    (hWopen.mem_nhds h1W)
  have hlevel0 : ∀ k ∈ maximalCompactAway F S₀, ∀ x : AdelicGL2 (𝓞 F) F, φ 0 (x * k) = φ 0 x := by
    intro k hk x
    have hkH : k ∈ finiteAdelicGL2Subgroup F := by
      rw [mem_finiteAdelicGL2Subgroup_iff]
      exact (mem_maximalCompactAway_iff.mp hk).2.1
    have hkstab : (⟨k, hkH⟩ : finiteAdelicGL2Subgroup F)
        ∈ MulAction.stabilizer (finiteAdelicGL2Subgroup F) (RightTranslationFn.mk (φ 0)) := by
      have : (⟨k, hkH⟩ : finiteAdelicGL2Subgroup F) ∈ (Subtype.val ⁻¹' W : Set (finiteAdelicGL2Subgroup F)) :=
        hS₀ hk
      rw [hWpre] at this
      exact this
    rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def] at hkstab
    have := congrArg (fun f => RightTranslationFn.toFun f x) hkstab
    simpa [RightTranslationFn.toFun_smul] using this

  refine ⟨S₀, fun s g k hk => ?_⟩
  have hkK : k ∈ adelicMaximalCompact F := maximalCompactAway_le F S₀ hk
  obtain ⟨b, kg, hb, hkgf, hkga, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq F g
  have hkgK : kg ∈ adelicMaximalCompact F := mem_adelicMaximalCompact_iff.mpr ⟨hkgf, hkga⟩
  have hkgk := (adelicMaximalCompact F).mul_mem hkgK hkK
  rw [mul_assoc, hφ s b hb (kg * k), hφ s b hb kg]
  congr 1
  calc φ s (kg * k) = φ 0 (kg * k) := hφflat s 0 (kg * k) hkgk.1 hkgk.2
    _ = φ 0 kg := hlevel0 k hk kg
    _ = φ s kg := hφflat 0 s kg hkgf hkga

end FlatFamilyKInvariance

end LocalIntertwining

namespace IsInducedSection

theorem eq_of_eqOn_maximalCompact
    (K : Type) [Field K] [NumberField K]
    (χ₁ χ₂ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (φ φ' : AdelicGL2 (𝓞 K) K → ℂ)
    (hφ : IsInducedSection (𝓞 K) K χ₁ χ₂ φ) (hφ' : IsInducedSection (𝓞 K) K χ₁ χ₂ φ')
    (h : ∀ k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K k ∈ finiteIntegralGL2 (𝓞 K) K →
      (∀ w : InfinitePlace K, IsRowIsometry (archComponent K w (glArch (𝓞 K) K k))) → φ k = φ' k) :
    φ = φ' := by
  funext g
  obtain ⟨b, k, hb, hkf, hkinf, rfl⟩ := AutomorphicForm.exists_mem_adelicBorel_mul_eq K g
  rw [hφ b hb k, hφ' b hb k, h k hkf hkinf]

end IsInducedSection

end AutomorphicForm
