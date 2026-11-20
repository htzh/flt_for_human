/-
The closure of the cuspidal spectrum under the constituent and isotypic constructions.

Five rows that finish the `CuspidalSpectrum`/`CuspidalConstituent` cluster AF89 readied:
the orthogonal-complement membership of an isotypic cusp form, the cyclic constituent
spanned by the translates and right convolutions of one vector, the non-vanishing of a
right convolution on a level-and-arch cut, the uniqueness of a constituent through a
shared vector, and the smooth-cusp realization attached to a nonzero isotypic form.

  Build record (AF90A).

  * Step 1 transcribed the pins' eight `private` engines at their own names, under subject
    sub-namespaces (the pins' search-stage labels `Meets` — A1 `:27` — and `S7Reduce` — A3
    `:21` — both become `AutomorphicForm.CuspidalSpectrum`): A1's six at `:32`–`:115` and
    A3's two at `:25`/`:36`, all at the pin's statements. The five `solution` rows are the
    five scaffolded rows; `check_port` reads `5 ok` and `scaffold_audit` reads `complete`,
    with all five pin publics `FOLDED` into their rows (each pin's `solution` statement *is*
    its row's statement).
  * `continuous_of_mem_cuspKFiniteSubmodule` is `private` in the A3 pin and is also `private`
    in the port (`Cusp/IrreducibleSpine.lean:123`, namespace `ArchSplit`); it is re-declared
    `private` here at the pin's own statement and re-proved.
  * One statement-neutral substitution inside one proof (the FR-0231 rename family): the
    pin's `ContinuousLinearMap.coe_sum'` (A1 `:207`) is v4.34's `FunLike.coe_sum`.
  * FR-0236: six frozen binders are dead in the pins' own proofs — A1's `hc`, `hd₁`, `hd`,
    `hcov` and A3's `hσ`, `hirr`. Each is spent with `have _ := …`; no binder is renamed and
    no linter option is installed (FR-0225, FR-0236).
  * Heartbeat probe (measured, never installed; read with
    `lake env lean -DautoImplicit=false -DmaxHeartbeats=N <module>`): **silent at `N = 60000`,
    fails at `N / 2 = 30000`** — `…SpectrumConstituentClosure.lean:234:6: (deterministic)
    timeout at whnf`. The bracket is tight: it also *fails* at `N = 50000` (`:275:18`,
    `isDefEq`), so the natural per-declaration cost of the heaviest row sits above `50000`
    and below `60000`. Silent at the edit-loop cap `200000`, where every gate below was
    read.

  ## Port deltas

  * No `import` line was added: the scaffold's ten imports carry every premise (A1's
    `isClosedCuspSubrep_orthogonal` in `Cusp/IrreducibleSpine`, `exists_isLift_rightTranslate`
    and `rightTranslate_mem_cuspMemberSubmodule` in `Cusp/SpectrumTranslation`,
    `eq_zero_of_toCarrier_eq_zero` in `Cusp/SpectrumCarrierAPI`; A2's engines in
    `Cusp/ConstituentRightConv`, `RightConvComm/Action`, `RightConvPreservation`,
    `KfSmoothTensor` and `TestFnTop`; A3's
    `exists_rightConv_injOn_of_finiteDimensional_of_le` in `Cusp/ConstituentRightConv` and
    `rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite` in
    `LeftCasimirTestFn`).
  * No pin wire line was added, and no scaffolded statement was re-spelled.

  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_isCuspSubrep_span_cyclic_and_mem_and_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalSpectrum_exists_rightConv_ne_zero_of_ne_bot.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_eq_of_isCuspConstituent_of_exists_mem_ne_zero.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsIsotypicCuspFormAt_exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ConstituentRightConv
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IrreducibleSpine
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumCarrierAPI
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SpectrumTranslation
import FLTForHuman.AutomorphicForm.Adelic.KfSmoothTensor
import FLTForHuman.AutomorphicForm.Adelic.LeftCasimirTestFn
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Action
import FLTForHuman.AutomorphicForm.Adelic.RightConvPreservation
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Matrix

namespace AutomorphicForm.CuspidalSpectrum

variable {F : Type} [Field F] [NumberField F]

private theorem proj_eq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (M : Submodule ℂ E) (S : E →L[ℂ] E)
    (hSM : M.map (S : E →ₗ[ℂ] E) ≤ M) (hSM' : Mᗮ.map (S : E →ₗ[ℂ] E) ≤ Mᗮ)
    {x y : E} (hy : y ∈ M) (hxy : x - y ∈ Mᗮ) (a : ℂ) (hx : S x = a • x) : S y = a • y := by
  have h1 : S y - a • y ∈ M := M.sub_mem (hSM ⟨y, hy, rfl⟩) (M.smul_mem a hy)
  have h2 : S y - a • y ∈ Mᗮ := by
    have : S y - a • y = a • (x - y) - S (x - y) := by
      rw [map_sub, hx, smul_sub]; abel
    rw [this]
    exact Mᗮ.sub_mem (Mᗮ.smul_mem a hxy) (hSM' ⟨x - y, hxy, rfl⟩)
  have h0 : S y - a • y = 0 := by
    have hmem : S y - a • y ∈ M ⊓ Mᗮ := ⟨h1, h2⟩
    rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp h0

private theorem eq_of_toCuspSubcarrier_eq {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ)
    (ψ₁ ψ₂ : AdelicGL2 (𝓞 F) F → ℂ) (h₁ : ψ₁ ∈ cuspMemberSubmodule F Φ₀ ξ) (h₂ : ψ₂ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (h : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ₁, h₁⟩ = toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ₂, h₂⟩) : ψ₁ = ψ₂ := by
  have hc : toCarrier F hΦ₀ σ ξ ⟨ψ₁, h₁.1.1.1⟩ = toCarrier F hΦ₀ σ ξ ⟨ψ₂, h₂.1.1.1⟩ := by
    have := congrArg Subtype.val h
    rwa [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe] at this
  have h12 : ψ₁ - ψ₂ ∈ cuspMemberSubmodule F Φ₀ ξ := Submodule.sub_mem _ h₁ h₂
  have hcont : ψ₁ - ψ₂ ∈ contMemberSubmodule F Φ₀ ξ := ⟨h12.1.1.1, h12.2⟩
  have h0 : toCarrier F hΦ₀ σ ξ ⟨ψ₁ - ψ₂, hcont.1⟩ = 0 := by
    have hsub := (toCarrier F hΦ₀ σ ξ).map_sub ⟨ψ₁, h₁.1.1.1⟩ ⟨ψ₂, h₂.1.1.1⟩
    rw [hc, sub_self] at hsub
    exact hsub
  exact sub_eq_zero.mp (AutomorphicForm.CuspidalSpectrum.eq_zero_of_toCarrier_eq_zero F hΦ₀ σ ξ (ψ₁ - ψ₂) hcont h0)

private theorem exists_cuspLift_rightTranslate {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (hσ : HasModulus F ξ σ) (g : AdelicGL2 (𝓞 F) F) :
    ∃ S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ),
      ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
          = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφ⟩ := by
  obtain ⟨T, -, hT, -, -, -⟩ := AutomorphicForm.CuspidalSpectrum.exists_isLift_rightTranslate F α β Φ₀ hΦ₀ σ ξ hσ g
  set S₀ : Submodule ℂ (Carrier F Φ₀ σ) := Submodule.map (toCarrier F hΦ₀ σ ξ)
      (Submodule.comap (memberSubmodule F Φ₀ ξ).subtype (cuspMemberSubmodule F Φ₀ ξ)) with hS₀
  have hcl : (cuspSubcarrier F hΦ₀ σ ξ : Set (Carrier F Φ₀ σ)) = closure (S₀ : Set (Carrier F Φ₀ σ)) :=
    Submodule.topologicalClosure_coe S₀
  have hmap₀ : Set.MapsTo T (S₀ : Set (Carrier F Φ₀ σ)) (S₀ : Set (Carrier F Φ₀ σ)) := by
    rintro _ ⟨⟨φ, hφm⟩, hφc, rfl⟩
    have hφc' : φ ∈ cuspMemberSubmodule F Φ₀ ξ := hφc
    have hcont : φ ∈ contMemberSubmodule F Φ₀ ξ := ⟨hφc'.1.1.1, hφc'.2⟩
    have hR := AutomorphicForm.CuspidalSpectrum.rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφc'
    refine ⟨⟨rightTranslate F g φ, hR.1.1.1⟩, hR, ?_⟩
    show toCarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, hR.1.1.1⟩ = T (toCarrier F hΦ₀ σ ξ ⟨φ, hφm⟩)
    rw [hT.comm φ hcont]
  have hmap : ∀ v : ↥(cuspSubcarrier F hΦ₀ σ ξ), T v ∈ cuspSubcarrier F hΦ₀ σ ξ := by
    intro v
    have hv : (v : Carrier F Φ₀ σ) ∈ closure (S₀ : Set (Carrier F Φ₀ σ)) := by
      rw [← hcl]; exact v.2
    rw [← SetLike.mem_coe, hcl]
    exact map_mem_closure T.continuous hv hmap₀
  refine ⟨(T.comp (cuspSubcarrier F hΦ₀ σ ξ).subtypeL).codRestrict (cuspSubcarrier F hΦ₀ σ ξ) (fun v => hmap v), ?_⟩
  intro φ hφ
  apply Subtype.ext
  show T (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩ : Carrier F Φ₀ σ)
    = (toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, _⟩ : Carrier F Φ₀ σ)
  rw [toCuspSubcarrier_apply_coe, toCuspSubcarrier_apply_coe]
  exact hT.comm φ ⟨hφ.1.1.1, hφ.2⟩

private theorem isCuspLift_of_forall {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (σ : ℝ) (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (g : AdelicGL2 (𝓞 F) F)
    (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ))
    (hS : ∀ (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : φ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφ⟩)
          = toCuspSubcarrier F hΦ₀ σ ξ ⟨rightTranslate F g φ, rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ hφ⟩) :
    IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S :=
  isCuspLift_of_forall_exists F hΦ₀ σ ξ (rightTranslate F g) S fun φ => ⟨rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ g φ φ.2, hS φ φ.2⟩

private theorem heckeGen_mem_finiteAdelicGL2Subgroup (v : HeightOneSpectrum (𝓞 F)) :
    heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply]
  exact heckeGenAt_fst _ i j

private theorem mem_finiteAdelicGL2Subgroup_of_mem_doubleCoset {U : Subgroup (AdelicGL2 (𝓞 F) F)}
    (hU : U ≤ finiteAdelicGL2Subgroup F) {g x : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F)
    (hx : x ∈ HeckePair.doubleCoset U g) : x ∈ finiteAdelicGL2Subgroup F := by
  obtain ⟨u, hu, u', hu', rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) hg) (hU hu')

end AutomorphicForm.CuspidalSpectrum

namespace AutomorphicForm.CuspidalSpectrum

theorem isIsotypicCuspFormAt_of_mem_of_sub_mem_orthogonal
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    {α β : ℝ} {Φ₀ : Set (AdelicGL2 (𝓞 F) F)} (hΦ₀ : IsSlabFundamentalDomain F α β Φ₀)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (M : Submodule ℂ ↥(cuspSubcarrier F hΦ₀ σ ξ)) (hM : IsClosedCuspSubrep F hΦ₀ σ ξ M)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφI : IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ φ)
    (hφm : φ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψK : ψ ∈ cuspKFiniteSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ)
    (hψm : ψ ∈ cuspMemberSubmodule F Φ₀ ξ)
    (hψM : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M)
    (hperp : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ - toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ Mᗮ) :
    IsIsotypicCuspFormAt F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ψ
  := by
  classical
  have _ := hc
  have _ := hd₁
  have _ := hd
  have _ := hcov
  set pins := (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) with hpins

  obtain ⟨hψc, hψsc⟩ :=
    AutomorphicForm.CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
      (fun v => heckeGen (𝓞 F) F v) ξ ψ hψK
  have hψ1 : IsSmoothCuspAutomorphicFnAt F pins ξ ψ := by
    have h := hψsc 1
    have : rightTranslate F 1 ψ = ψ := funext fun x => by rw [rightTranslate_apply, mul_one]
    rwa [this] at h
  have hMperp : IsClosedCuspSubrep F hΦ₀ σ ξ Mᗮ :=
    AutomorphicForm.CuspidalSpectrum.isClosedCuspSubrep_orthogonal F hΦ₀ σ ξ hσ M hM

  have key : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ a : ℂ,
      rightTranslate F g φ = a • φ → rightTranslate F g ψ = a • ψ := by
    intro g hg a hφeq
    obtain ⟨S, hS⟩ := exists_cuspLift_rightTranslate hΦ₀ σ ξ hσ g
    have hSl : IsCuspLift F hΦ₀ σ ξ (rightTranslate F g) S := isCuspLift_of_forall hΦ₀ σ ξ g S hS
    have hSM := hM.map_le_of_rightTranslate_fin g hg S hSl
    have hSM' := hMperp.map_le_of_rightTranslate_fin g hg S hSl

    have hx : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩) = a • toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ := by
      rw [hS φ hφm, ← map_smul]
      congr 1
      exact Subtype.ext hφeq
    have hy := proj_eq M S hSM hSM' hψM hperp a hx

    rw [hS ψ hψm, ← map_smul] at hy
    exact eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ _ _ _ ((cuspMemberSubmodule F Φ₀ ξ).smul_mem a hψm) hy

  refine ⟨hψ1, hψc, ?_, ?_, ?_⟩
  ·
    intro g u hu
    have hu' : u ∈ finiteAdelicGL2Subgroup F := hu.2
    have hφu : rightTranslate F u φ = (1 : ℂ) • φ := by
      rw [one_smul]; funext x; exact hφI.level_invariant x u hu
    have := congrFun (key u hu' 1 hφu) g
    rwa [rightTranslate_apply, one_smul] at this
  ·
    intro v hv
    obtain ⟨reps, hsys, heq⟩ := hφI.hecke_eigen v hv
    refine ⟨reps, hsys, ?_⟩

    have hUfin : pins.U N ≤ finiteAdelicGL2Subgroup F := fun x hx => hx.2
    have hreps : ∀ i, reps i ∈ finiteAdelicGL2Subgroup F := fun i =>
      mem_finiteAdelicGL2Subgroup_of_mem_doubleCoset hUfin (heckeGen_mem_finiteAdelicGL2Subgroup v) (hsys.mem_doubleCoset i)

    choose Sf hSf using fun i => exists_cuspLift_rightTranslate hΦ₀ σ ξ hσ (reps i)
    have hSfM : ∀ i, ∀ m ∈ M, Sf i m ∈ M := fun i m hm =>
      hM.map_le_of_rightTranslate_fin (reps i) (hreps i) (Sf i) (isCuspLift_of_forall hΦ₀ σ ξ (reps i) (Sf i) (hSf i))
        ⟨m, hm, rfl⟩
    have hSfM' : ∀ i, ∀ m ∈ Mᗮ, Sf i m ∈ Mᗮ := fun i m hm =>
      hMperp.map_le_of_rightTranslate_fin (reps i) (hreps i) (Sf i) (isCuspLift_of_forall hΦ₀ σ ξ (reps i) (Sf i) (hSf i))
        ⟨m, hm, rfl⟩
    set S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →L[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ) := ∑ i, Sf i with hSdef
    have hSapp : ∀ m, S m = ∑ i, Sf i m := fun m => by
      rw [hSdef, FunLike.coe_sum, Finset.sum_apply]
    have hSM : M.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ M := by
      rintro _ ⟨m, hm, rfl⟩
      show S m ∈ M
      rw [hSapp]
      exact M.sum_mem fun i _ => hSfM i m hm
    have hSM' : Mᗮ.map (S : ↥(cuspSubcarrier F hΦ₀ σ ξ) →ₗ[ℂ] ↥(cuspSubcarrier F hΦ₀ σ ξ)) ≤ Mᗮ := by
      rintro _ ⟨m, hm, rfl⟩
      show S m ∈ Mᗮ
      rw [hSapp]
      exact Mᗮ.sum_mem fun i _ => hSfM' i m hm

    have hsum_mem : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ), χ ∈ cuspMemberSubmodule F Φ₀ ξ →
        (∑ i, rightTranslate F (reps i) χ) ∈ cuspMemberSubmodule F Φ₀ ξ := fun χ hχ =>
      Submodule.sum_mem _ fun i _ => rightTranslate_mem_cuspMemberSubmodule F hΦ₀ ξ (reps i) χ hχ
    have hSclass : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ) (hχ : χ ∈ cuspMemberSubmodule F Φ₀ ξ),
        S (toCuspSubcarrier F hΦ₀ σ ξ ⟨χ, hχ⟩) = toCuspSubcarrier F hΦ₀ σ ξ ⟨∑ i, rightTranslate F (reps i) χ, hsum_mem χ hχ⟩ := by
      intro χ hχ
      rw [hSapp]
      simp_rw [hSf _ χ hχ]
      rw [← map_sum]
      congr 1
      apply Subtype.ext
      rw [Submodule.coe_sum]
    have hsum_fun : ∀ (χ : AdelicGL2 (𝓞 F) F → ℂ) (x : AdelicGL2 (𝓞 F) F),
        (∑ i, rightTranslate F (reps i) χ) x = SmoothCusp.heckeCosetSum F reps χ x := by
      intro χ x
      rw [Finset.sum_apply]
      rfl

    have hφsum : (∑ i, rightTranslate F (reps i) φ) = Ψ.a v • φ := by
      funext x
      rw [hsum_fun, heq x, Pi.smul_apply, smul_eq_mul]
    have hx : S (toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩) = Ψ.a v • toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ := by
      rw [hSclass φ hφm, ← map_smul]
      congr 1
      exact Subtype.ext hφsum
    have hy := proj_eq M S hSM hSM' hψM hperp (Ψ.a v) hx
    rw [hSclass ψ hψm, ← map_smul] at hy
    have hψsum := eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ _ _ _ ((cuspMemberSubmodule F Φ₀ ξ).smul_mem (Ψ.a v) hψm) hy
    intro x
    rw [← hsum_fun, hψsum, Pi.smul_apply, smul_eq_mul]
  ·
    intro v hv g
    have hψls := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ ψ).mp hψm.1.1.1).1
    have hφls := ((isAutomorphicFnAt_fdPins_iff F Φ₀ ξ φ).mp hφm.1.1.1).1
    have hψz := hψls.central_transform ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ g
    by_cases h0 : φ = 0
    ·
      have hφ0 : toCuspSubcarrier F hΦ₀ σ ξ ⟨φ, hφm⟩ = 0 := by
        have : (⟨φ, hφm⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext h0
        rw [this, map_zero]
      have hψ0 : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ = 0 := by
        have hmem : toCuspSubcarrier F hΦ₀ σ ξ ⟨ψ, hψm⟩ ∈ M ⊓ Mᗮ := by
          refine ⟨hψM, ?_⟩
          have := Mᗮ.neg_mem hperp
          rwa [hφ0, zero_sub, neg_neg] at this
        rwa [Submodule.inf_orthogonal_eq_bot, Submodule.mem_bot] at hmem
      have hψzero : ψ = 0 := by
        refine eq_of_toCuspSubcarrier_eq hΦ₀ σ ξ ψ 0 hψm (Submodule.zero_mem _) ?_
        rw [hψ0]
        have : (⟨0, Submodule.zero_mem _⟩ : ↥(cuspMemberSubmodule F Φ₀ ξ)) = 0 := Subtype.ext rfl
        rw [this, map_zero]
      simp only [hψzero, Pi.zero_apply, mul_zero]
    · obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp h0
      have h1 := hφI.central_eigen v hv g₀
      have h2 := hφls.central_transform ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ g₀
      have hb : Ψ.toRawCentral.b v
          = ((ξ ⟨Matrix.GeneralLinearGroup.det (pins.gen v), trivial⟩ : ℂˣ) : ℂ) :=
        mul_right_cancel₀ hg₀ (h1.symm.trans h2)
      rw [hb]
      exact hψz

end AutomorphicForm.CuspidalSpectrum

namespace AutomorphicForm.CuspidalSpectrum

private theorem continuous_of_mem_cuspKFiniteSubmodule (F : Type) [Field F] [NumberField F]
    (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hcont, -⟩
    exact hcont
  · exact continuous_const
  · intro u w _ _ hu hw
    exact hu.add hw
  · intro c u _ hu
    exact hu.const_smul c

private theorem exists_arch_mul_of_ne_zero (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F))
    (f : AdelicGL2 (𝓞 F) F → ℂ) (fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ)
    (hf : ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
      Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F))) (fun _ => (1 : ℂ))
        (AdelicLevel.glFin (𝓞 F) F g))
    (x : AdelicGL2 (𝓞 F) F) (hx : f x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ U ∧ x = a * k := by
  classical
  rw [hf] at hx
  have hmem : AdelicLevel.glFin (𝓞 F) F x ∈ (AdelicLevel.glFin (𝓞 F) F) '' (U : Set (AdelicGL2 (𝓞 F) F)) := by
    by_contra h
    rw [Set.indicator_of_notMem h, mul_zero] at hx
    exact hx rfl
  obtain ⟨k, hk, hkx⟩ := hmem
  refine ⟨x * k⁻¹, k, ?_, hk, by rw [inv_mul_cancel_right]⟩
  rw [map_mul, map_inv, ← hkx, mul_inv_cancel]

end AutomorphicForm.CuspidalSpectrum

namespace AutomorphicForm.CuspidalSpectrum

theorem exists_rightConv_ne_zero_of_ne_bot
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (⊤ : Subgroup (AdeleRing (𝓞 F) F)ˣ) →* ℂˣ) (σ : ℝ) (hσ : HasModulus F ξ σ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ V)
    (hX : V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) ≠ ⊥) :
    ∃ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f ∧
      (∃ fa : GL (Fin 2) (InfiniteAdeleRing F) → ℂ,
        IsArchTestFactor F fa ∧ IsArchFactorBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) fa ∧
        (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion) (x : GL (Fin 2) (InfiniteAdeleRing F)),
          fa (archRowIsometryInclAt₀ F w k * x * (archRowIsometryInclAt₀ F w k)⁻¹) = fa x) ∧
        ∀ g : AdelicGL2 (𝓞 F) F, f g = fa (AdelicLevel.glArch (𝓞 F) F g) *
          Set.indicator ((AdelicLevel.glFin (𝓞 F) F) '' ((productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).U N : Set (AdelicGL2 (𝓞 F) F)))
            (fun _ => (1 : ℂ)) (AdelicLevel.glFin (𝓞 F) F g)) ∧
      flat F σ f = f ∧
      (∀ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)) ∧
      ∃ φ ∈ V ⊓ levelInvariantSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) N ⊓ archCutSubmodule F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F), rightConv F φ f ≠ 0
  := by
  classical
  have _ := hσ
  have _ := hirr

  set pins := productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F) with hpins
  set tys : AutomorphicForm.ArchTypeFamily F := ⟨fun _ => 1, fun w _ => τ w⟩ with htys
  set X := V ⊓ levelInvariantSubmodule F pins N ⊓ archCutSubmodule F tys with hXdef

  obtain ⟨φ₀, hφ₀X, hφ₀ne⟩ := (Submodule.ne_bot_iff X).mp hX
  have hφ₀V : φ₀ ∈ V := hφ₀X.1.1
  have hφ₀L : φ₀ ∈ levelInvariantSubmodule F pins N := hφ₀X.1.2
  have hφ₀A : φ₀ ∈ archCutSubmodule F tys := hφ₀X.2
  have hVc : ∀ φ ∈ V, Continuous φ := fun φ hφ =>
    continuous_of_mem_cuspKFiniteSubmodule F pins ξ (hV.1.le hφ)
  set Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := ℂ ∙ φ₀ with hY
  have hYfd : FiniteDimensional ℂ ↥Y := inferInstance
  have hYc : ∀ y ∈ Y, Continuous y := by
    intro y hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact (hVc φ₀ hφ₀V).const_smul a
  have hYU : Y ≤ levelInvariantSubmodule F pins N :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hφ₀L)
  have hYt : Y ≤ archCutSubmodule F tys :=
    Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hφ₀A)

  obtain ⟨f, hf, hls, hflat, hinj⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_rightConv_injOn_of_finiteDimensional_of_le F
      (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N hN tys σ Y hYfd hYc hYU hYt
  obtain ⟨fa, hfa, hbfa, hconj, hfac⟩ := hls
  have hbf : IsArchBiFinite F tys f := IsArchBiFinite.of_factorization F hfac hbfa
  have hfs : ∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 F) F, glFin (𝓞 F) F a = 1 ∧ k ∈ pins.U N ∧ x = a * k :=
    fun x hx => exists_arch_mul_of_ne_zero F (pins.U N) f fa hfac x hx
  refine ⟨f, hf, ⟨fa, hfa, hbfa, hconj, hfac⟩, hflat, ?_, φ₀, hφ₀X, fun h => hφ₀ne (hinj φ₀ (Submodule.mem_span_singleton_self φ₀) h)⟩
  intro φ hφ
  have hφV : φ ∈ V := hφ.1.1
  have hφL : φ ∈ levelInvariantSubmodule F pins N := hφ.1.2
  have hVmem : rightConv F φ f ∈ V := hV.1.rightConv_mem f tys hf hbf φ hφV
  have hLA := AutomorphicForm.CuspidalConstituent.rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule_of_isArchBiFinite
    F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) N tys f hf hbf hfs φ (hVc φ hφV) hφL
  exact ⟨⟨hVmem, hLA.1⟩, hLA.2⟩

end AutomorphicForm.CuspidalSpectrum

namespace AutomorphicForm.CuspidalConstituent

theorem isCuspSubrep_span_cyclic_and_mem_and_le
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (ξ : (productionPinsOf F D U gen B).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hV : IsCuspSubrep F (productionPinsOf F D U gen B) ξ V)
    (Ψ : AdelicGL2 (𝓞 F) F → ℂ) (hΨ : Ψ ∈ V) :
    let C : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ
      {φ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        φ = rightTranslate F (g * k) Ψ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          φ = rightTranslate F (g * k) (rightConv F Ψ f)}
    IsCuspSubrep F (productionPinsOf F D U gen B) ξ C ∧ Ψ ∈ C ∧ C ≤ V ∧
      (IsCuspConstituent F (productionPinsOf F D U gen B) ξ V → Ψ ≠ 0 → C = V)
  := by
  intro C

  set S : Set (AdelicGL2 (𝓞 F) F → ℂ) :=
    {φ | ∃ g ∈ finiteAdelicGL2Subgroup F, ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        φ = rightTranslate F (g * k) Ψ ∨
        ∃ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys : ArchTypeFamily F), IsFactorizableTestFn F f ∧ IsArchBiFinite F tys f ∧
          φ = rightTranslate F (g * k) (rightConv F Ψ f)} with hS
  have hCdef : C = Submodule.span ℂ S := rfl
  set Karch : Subgroup (AdelicGL2 (𝓞 F) F) := ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range with hKarch

  have hcomm : ∀ g k : AdelicGL2 (𝓞 F) F, AdelicLevel.glArch (𝓞 F) F g = 1 → AdelicLevel.glFin (𝓞 F) F k = 1 →
      g * k = k * g := by
    intro g k hg hk
    have hA : AdelicLevel.glArch (𝓞 F) F (g * k) = AdelicLevel.glArch (𝓞 F) F (k * g) := by
      rw [map_mul, map_mul, hg, one_mul, mul_one]
    have hB : AdelicLevel.glFin (𝓞 F) F (g * k) = AdelicLevel.glFin (𝓞 F) F (k * g) := by
      rw [map_mul, map_mul, hk, one_mul, mul_one]
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    apply Prod.ext
    · rw [← AdelicLevel.glArch_apply, ← AdelicLevel.glArch_apply, hA]
    · rw [← AdelicLevel.glFin_apply, ← AdelicLevel.glFin_apply, hB]

  have hKfin : ∀ k ∈ Karch, AdelicLevel.glFin (𝓞 F) F k = 1 := by
    intro k hk
    refine Subgroup.iSup_induction (C := fun k => AdelicLevel.glFin (𝓞 F) F k = 1) _ hk ?_ (map_one _) ?_
    · rintro w k ⟨k₀, rfl⟩; exact glFin_rowIsometryInclAt₀ F w k₀
    · intro x y hx hy; rw [map_mul, hx, hy, one_mul]
  have hKstab : ∀ (W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ W, rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ W) →
      ∀ k ∈ Karch, ∀ φ ∈ W, rightTranslate F k φ ∈ W := by
    intro W hW k hk
    refine Subgroup.iSup_induction (C := fun k => ∀ φ ∈ W, rightTranslate F k φ ∈ W) _ hk ?_ ?_ ?_
    · rintro w k ⟨k₀, rfl⟩ φ hφ; exact hW w k₀ φ hφ
    · intro φ hφ
      have : rightTranslate F 1 φ = φ := by funext x; simp [rightTranslate]
      rw [this]; exact hφ
    · intro x y hx hy φ hφ
      rw [← rightTranslate_rightTranslate]; exact hx _ (hy φ hφ)

  have hgenV : ∀ φ ∈ S, φ ∈ V := by
    rintro φ ⟨g, hg, k, hk, hφ⟩
    have hRgk : ∀ ψ ∈ V, rightTranslate F (g * k) ψ ∈ V := fun ψ hψ => by
      rw [← rightTranslate_rightTranslate]; exact hV.rightTranslate_fin_mem g hg _ (hKstab V hV.rightTranslate_arch_mem k hk ψ hψ)
    rcases hφ with rfl | ⟨f, tys, hf, hbf, rfl⟩
    · exact hRgk Ψ hΨ
    · exact hRgk _ (hV.rightConv_mem f tys hf hbf Ψ hΨ)
  have hCV : C ≤ V := Submodule.span_le.mpr hgenV
  have hΨC : Ψ ∈ C := by
    refine Submodule.subset_span ⟨1, one_mem _, 1, one_mem _, Or.inl ?_⟩
    funext x; simp [rightTranslate]

  have hspan_stab : ∀ (h : AdelicGL2 (𝓞 F) F), (∀ φ ∈ S, rightTranslate F h φ ∈ C) → ∀ φ ∈ C, rightTranslate F h φ ∈ C := by
    intro h hgen φ hφ
    refine Submodule.span_induction (p := fun φ _ => rightTranslate F h φ ∈ C) ?_ ?_ ?_ ?_ hφ
    · exact hgen
    · show rightTranslate F h 0 ∈ C
      rw [rightTranslate_zero]; exact C.zero_mem
    · intro u w _ _ hu hw
      show rightTranslate F h (u + w) ∈ C
      rw [rightTranslate_add]; exact C.add_mem hu hw
    · intro a u _ hu
      show rightTranslate F h (a • u) ∈ C
      rw [rightTranslate_smul]; exact C.smul_mem a hu
  have hgen_form : ∀ (g' k' : AdelicGL2 (𝓞 F) F), g' ∈ finiteAdelicGL2Subgroup F → k' ∈ Karch →
      ∀ φ ∈ S, rightTranslate F (g' * k') φ ∈ C := by
    intro g' k' hg' hk' φ hφS
    obtain ⟨g, hg, k, hk, hφ⟩ := hφS

    have hprod : g' * k' * (g * k) = (g' * g) * (k' * k) := by
      have hc : k' * g = g * k' := (hcomm g k' ((mem_finiteAdelicGL2Subgroup_iff F g).mp hg) (hKfin k' hk')).symm
      rw [mul_assoc, ← mul_assoc k' g k, hc, mul_assoc, mul_assoc]
    have hmem : ∀ ψ, rightTranslate F (g' * k') (rightTranslate F (g * k) ψ) = rightTranslate F ((g' * g) * (k' * k)) ψ := by
      intro ψ; rw [rightTranslate_rightTranslate, hprod]
    rcases hφ with rfl | ⟨f, tys, hf, hbf, rfl⟩
    · rw [hmem]
      exact Submodule.subset_span ⟨g' * g, mul_mem hg' hg, k' * k, mul_mem hk' hk, Or.inl rfl⟩
    · rw [hmem]
      exact Submodule.subset_span ⟨g' * g, mul_mem hg' hg, k' * k, mul_mem hk' hk, Or.inr ⟨f, tys, hf, hbf, rfl⟩⟩
  have hfin : ∀ g ∈ finiteAdelicGL2Subgroup F, ∀ φ ∈ C, rightTranslate F g φ ∈ C := by
    intro g hg
    have := hspan_stab (g * 1) (hgen_form g 1 hg (one_mem _))
    rwa [mul_one] at this
  have harch : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion), ∀ φ ∈ C,
      rightTranslate F (rowIsometryInclAt₀ F w k) φ ∈ C := by
    intro w k
    have hk : rowIsometryInclAt₀ F w k ∈ Karch := by
      rw [hKarch]; exact Subgroup.mem_iSup_of_mem w ⟨k, rfl⟩
    have := hspan_stab (1 * rowIsometryInclAt₀ F w k) (hgen_form 1 _ (one_mem _) hk)
    rwa [one_mul] at this

  have CONJ := AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj F
  have COMM := AutomorphicForm.CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj F
  have FACT := AutomorphicForm.CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_rightConv_comp_inv F
  have ASSOC := AutomorphicForm.rightConv_rightConv_eq_rightConv_rightConv_comp_inv (F := F)

  have TESTREG : ∀ f : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f → Continuous f ∧ HasCompactSupport f :=
    fun f hf => AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf

  have hcontK : ∀ φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen B) ξ, Continuous φ := by
    intro φ hφ
    refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
    · rintro φ ⟨-, hcont, -⟩; exact hcont
    · exact continuous_const
    · intro u w _ _ hu hw; exact hu.add hw
    · intro a u _ hu; exact hu.const_smul a
  have hcontC : ∀ φ ∈ C, Continuous φ := fun φ hφ => hcontK φ (hV.le (hCV hφ))
  have hΨcont : Continuous Ψ := hcontK Ψ (hV.le hΨ)
  have hconv : ∀ (f' : AdelicGL2 (𝓞 F) F → ℂ) (tys' : ArchTypeFamily F),
      IsFactorizableTestFn F f' → IsArchBiFinite F tys' f' → ∀ φ ∈ C, rightConv F φ f' ∈ C := by
    intro f' tys' hf' hbf' φ hφ
    obtain ⟨hf'c, hf's⟩ := TESTREG f' hf'
    refine Submodule.span_induction (p := fun φ _ => rightConv F φ f' ∈ C) ?_ ?_ ?_ ?_ hφ
    · rintro φ ⟨g, hg, k, hk, hφ⟩
      obtain ⟨tys'', hfc, hbfc⟩ := CONJ g hg k hk f' tys' hf' hbf'
      obtain ⟨hcc, hcs⟩ := TESTREG _ hfc
      rcases hφ with rfl | ⟨f, tys, hf, hbf, rfl⟩
      · rw [COMM]
        exact Submodule.subset_span ⟨g, hg, k, hk, Or.inr ⟨_, tys'', hfc, hbfc, rfl⟩⟩
      · obtain ⟨hfcont, hfsupp⟩ := TESTREG f hf
        rw [COMM, ASSOC Ψ hΨcont f _ hfcont hfsupp hcc hcs]
        obtain ⟨tys₃, hf3, hbf3⟩ := FACT f _ tys tys'' hf hbf hfc hbfc
        exact Submodule.subset_span ⟨g, hg, k, hk, Or.inr ⟨_, tys₃, hf3, hbf3, rfl⟩⟩
    · show rightConv F 0 f' ∈ C
      rw [show rightConv F (0 : AdelicGL2 (𝓞 F) F → ℂ) f' = 0 from rightConv_zero_left F f']; exact C.zero_mem
    · intro u w hu_mem hw_mem hu hw
      show rightConv F (u + w) f' ∈ C
      rw [rightConv_add_left F (hcontC u hu_mem) (hcontC w hw_mem) hf'c hf's]; exact C.add_mem hu hw
    · intro a u _ hu
      show rightConv F (a • u) f' ∈ C
      have : rightConv F (a • u) f' = a • rightConv F u f' := by
        funext x
        simp only [rightConv_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact MeasureTheory.integral_const_mul a _
      rw [this]; exact C.smul_mem a hu

  have hC : IsCuspSubrep F (productionPinsOf F D U gen B) ξ C := ⟨hCV.trans hV.le, hfin, harch, hconv⟩
  refine ⟨hC, hΨC, hCV, fun hconst hΨ0 => ?_⟩
  rcases hconst.2.2 C hC hCV with h | h
  · exact absurd ((Submodule.mem_bot ℂ).mp (h ▸ hΨC)) hΨ0
  · exact h

end AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm.CuspidalConstituent

theorem eq_of_isCuspConstituent_of_exists_mem_ne_zero
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (V₁ V₂ : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (h₁ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₁)
    (h₂ : AutomorphicForm.CuspidalConstituent.IsCuspConstituent F pins ξ V₂)
    (h : ∃ φ ∈ V₁ ⊓ V₂, φ ≠ 0) : V₁ = V₂
  := by
  obtain ⟨φ, hφ, hφ0⟩ := h
  have hsub : AutomorphicForm.CuspidalConstituent.IsCuspSubrep F pins ξ (V₁ ⊓ V₂) :=
    { le := inf_le_left.trans h₁.1.le
      rightTranslate_fin_mem := fun g hg ψ hψ =>
        ⟨h₁.1.rightTranslate_fin_mem g hg ψ hψ.1, h₂.1.rightTranslate_fin_mem g hg ψ hψ.2⟩
      rightTranslate_arch_mem := fun w k ψ hψ =>
        ⟨h₁.1.rightTranslate_arch_mem w k ψ hψ.1, h₂.1.rightTranslate_arch_mem w k ψ hψ.2⟩
      rightConv_mem := fun f tys hf hbi ψ hψ =>
        ⟨h₁.1.rightConv_mem f tys hf hbi ψ hψ.1, h₂.1.rightConv_mem f tys hf hbi ψ hψ.2⟩ }
  have hne : V₁ ⊓ V₂ ≠ ⊥ := by
    intro hbot
    rw [hbot, Submodule.mem_bot] at hφ
    exact hφ0 hφ
  have e₁ : V₁ ⊓ V₂ = V₁ := (h₁.2.2 _ hsub inf_le_left).resolve_left hne
  have e₂ : V₁ ⊓ V₂ = V₂ := (h₂.2.2 _ hsub inf_le_right).resolve_left hne
  exact e₁.symm.trans e₂

end AutomorphicForm.CuspidalConstituent

namespace AutomorphicForm.IsIsotypicCuspFormAt

theorem exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot
    (F : Type) [Field F] [NumberField F] (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (hN : N ≠ ⊥) (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 F)))
    (Ψ : HeckeEigensystem F ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (h : IsIsotypicCuspFormAt F pins ξ N S Ψ φ) (h0 : φ ≠ 0) :
    ∃ (Ψ' : HeckeEigensystem F ℂ) (R : SmoothCuspRealizationAt F pins Ψ'.toRawCentral),
      Ψ'.level = N ∧ (∀ v, Ψ'.a v = Ψ.a v) ∧ (∀ v, Ψ'.b v = Ψ.b v) ∧
        R.toFun = φ ∧ R.centralChar = ξ ∧ R.exceptionalSet = S
  := by
  refine ⟨⟨N, hN, Ψ.a, Ψ.b⟩, ?_, rfl, fun _ => rfl, fun _ => rfl, ?_⟩
  · exact
      { toFun := φ
        exists_ne_zero := Function.ne_iff.mp h0
        centralChar := ξ
        smoothCusp := h.smoothCusp
        level_invariant := h.level_invariant
        exceptionalSet := S
        hecke_eigen := h.hecke_eigen
        central_eigen := h.central_eigen }
  · exact ⟨rfl, rfl, rfl⟩

end AutomorphicForm.IsIsotypicCuspFormAt

end
