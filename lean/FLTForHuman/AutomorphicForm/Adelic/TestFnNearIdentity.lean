/-
  The near-identity factorisable test function on `GL₂(𝔸_F)`.

  This is the shared prelude of the `isFactorizableTestFn` family: the archimedean
  homeomorphism `mixedHomeo` and its matrix/adjoin variants, the closed embedding `J`
  of `GL₂(K_∞)` into the mixed space, the determinant-adjugate map `Ψ` with the compact
  radius `R`, the bump functions `bumpAt`/`bump₂` and the archimedean factor `fa`, the
  finite level set `Kf` and its indicator `ff`, and the assembled test function
  `testFn`/`testFnR` with its factorisability, invariance, support and non-vanishing
  lemmas (`rightConv_ne_zero_of_bound`). It is the construction that three
  `rightConv_ne_zero_of_*` headlines otherwise copy.

  Transcribed verbatim from the `TestFnNearIdentity` block of
  `P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant.lean:19–475`
  (pinned `aa2d8b3`), promoted from pin-`private` to public and rehomed at
  `AutomorphicForm.TestFnNearIdentity`. The same block appears publicly as
  `Ws1.H2K.Scaffold` in
  `P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_hasArchCharacterAt_rightConv_ne_zero_of_hasArchCharacterAt.lean`;
  see `topics/PORTING-AutomorphicForm.md` §4.2.

  `continuous_ringEquiv_mixedSpace` is *not* re-derived here: the pin states it in
  `Definitions/Def_NumberField_AdelicBox.lean`, so it is imported from
  `NumberTheory/AdelicBox.lean` at its pin home (playbook §3.1, §5).
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicBox

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls in `rightConv_ne_zero_of_bound` feed instance search.
set_option linter.style.haveILetI false

open NumberField NumberField.AdelicLevel
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain
open NumberField.InfiniteAdeleRing AutomorphicForm Metric Topology MeasureTheory

open scoped Classical

noncomputable section

namespace AutomorphicForm

namespace TestFnNearIdentity

variable (F : Type) [Field F] [NumberField F]

abbrev E : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

def ofE (m : E F) : Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F) := m

omit [NumberField F] in
theorem continuous_ringEquiv_mixedSpace_symm : Continuous (ringEquiv_mixedSpace F).symm := by
  apply continuous_pi
  intro v
  by_cases hv : IsReal v
  · have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivRealOfIsReal hv).symm (y.1 ⟨v, hv⟩) := by
      funext y
      apply (isometryEquivRealOfIsReal hv).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.1 ⟨v, hv⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivRealOfIsReal hv).symm.continuous.comp
      ((continuous_apply _).comp continuous_fst)
  · have hc : IsComplex v := not_isReal_iff_isComplex.1 hv
    have key : (fun y : mixedEmbedding.mixedSpace F => (ringEquiv_mixedSpace F).symm y v)
        = fun y => (isometryEquivComplexOfIsComplex hc).symm (y.2 ⟨v, hc⟩) := by
      funext y
      apply (isometryEquivComplexOfIsComplex hc).injective
      rw [IsometryEquiv.apply_symm_apply]
      have h := congrArg (fun z : mixedEmbedding.mixedSpace F => z.2 ⟨v, hc⟩)
        ((ringEquiv_mixedSpace F).apply_symm_apply y)
      exact h
    rw [key]
    exact (isometryEquivComplexOfIsComplex hc).symm.continuous.comp
      ((continuous_apply _).comp continuous_snd)

def mixedHomeo : InfiniteAdeleRing F ≃ₜ mixedEmbedding.mixedSpace F where
  toEquiv := (ringEquiv_mixedSpace F).toEquiv
  continuous_toFun := NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F
  continuous_invFun := continuous_ringEquiv_mixedSpace_symm F

def matHomeo : (Fin 2 → Fin 2 → InfiniteAdeleRing F) ≃ₜ E F :=
  Homeomorph.piCongrRight fun _ => Homeomorph.piCongrRight fun _ => mixedHomeo F

def pairHomeo :
    (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) × (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ)
      ≃ₜ (E F × E F) :=
  Homeomorph.prodCongr (matHomeo F) (MulOpposite.opHomeomorph.symm.trans (matHomeo F))

def J (g : GL (Fin 2) (InfiniteAdeleRing F)) : E F × E F :=
  pairHomeo F (Units.embedProduct _ g)

omit [NumberField F] in
theorem J_apply (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    J F g = (archEntries F g, archEntries F g⁻¹) := rfl

omit [NumberField F] in
theorem isClosedEmbedding_J : IsClosedEmbedding (J F) :=
  (pairHomeo F).isClosedEmbedding.comp Units.isClosedEmbedding_embedProduct

def cE : E F := archEntries F 1

omit [NumberField F] in
theorem ofE_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    ofE F (archEntries F g)
      = (ringEquiv_mixedSpace F).toRingHom.mapMatrix (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  funext i j
  rfl

omit [NumberField F] in
theorem continuous_detE : Continuous fun m : E F => (ofE F m).det :=
  Continuous.matrix_det continuous_id

theorem isOpen_detUnit : IsOpen {m : E F | IsUnit (ofE F m).det} :=
  Units.isOpen.preimage (continuous_detE F)

omit [NumberField F] in
theorem det_cE : (ofE F (cE F)).det = 1 := by
  rw [cE, ofE_archEntries, ← RingHom.map_det, Units.val_one, Matrix.det_one, map_one]

theorem exists_ball_subset_detUnit :
    ∃ ε > 0, ball (cE F) ε ⊆ {m : E F | IsUnit (ofE F m).det} :=
  Metric.isOpen_iff.1 (isOpen_detUnit F) (cE F) (by simp [det_cE])

def ε : ℝ := Classical.choose (exists_ball_subset_detUnit F)

theorem ε_pos : 0 < ε F := (Classical.choose_spec (exists_ball_subset_detUnit F)).1

theorem ball_ε_subset : ball (cE F) (ε F) ⊆ {m : E F | IsUnit (ofE F m).det} :=
  (Classical.choose_spec (exists_ball_subset_detUnit F)).2

def Ψ (m : E F) : E F := fun i j => (Ring.inverse (ofE F m).det • (ofE F m).adjugate) i j

theorem continuousOn_Ψ : ContinuousOn (Ψ F) (closedBall (cE F) (ε F / 2)) := by
  intro m hm
  have hunit : IsUnit (ofE F m).det :=
    ball_ε_subset F (closedBall_subset_ball (by linarith [ε_pos F]) hm)
  obtain ⟨u, hu⟩ := hunit
  apply ContinuousAt.continuousWithinAt
  have h1 : ContinuousAt (fun m : E F => Ring.inverse (ofE F m).det) m := by
    have hi : ContinuousAt Ring.inverse (ofE F m).det := hu ▸ NormedRing.inverse_continuousAt u
    exact hi.comp (continuous_detE F).continuousAt
  have h2 : Continuous fun m : E F => (ofE F m).adjugate := Continuous.matrix_adjugate continuous_id
  have h3 : ContinuousAt (fun m : E F =>
      (Ring.inverse (ofE F m).det • (ofE F m).adjugate :
        Matrix (Fin 2) (Fin 2) (mixedEmbedding.mixedSpace F))) m :=
    h1.smul h2.continuousAt
  exact h3

theorem exists_R : ∃ R > 0, Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) R := by
  have hc : IsCompact (Ψ F '' closedBall (cE F) (ε F / 2)) :=
    (isCompact_closedBall _ _).image_of_continuousOn (continuousOn_Ψ F)
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (cE F)
  exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

def R : ℝ := Classical.choose (exists_R F)

theorem R_pos : 0 < R F := (Classical.choose_spec (exists_R F)).1

theorem Ψ_subset : Ψ F '' closedBall (cE F) (ε F / 2) ⊆ closedBall (cE F) (R F) :=
  (Classical.choose_spec (exists_R F)).2

def bump₂ : ContDiffBump (cE F) where
  rIn := R F
  rOut := R F + 1
  rIn_pos := R_pos F
  rIn_lt_rOut := by linarith

theorem archEntries_inv_mem (g : GL (Fin 2) (InfiniteAdeleRing F))
    (hg : archEntries F g ∈ closedBall (cE F) (ε F / 2)) :
    archEntries F g⁻¹ ∈ closedBall (cE F) (R F) := by
  apply Ψ_subset F
  refine ⟨archEntries F g, hg, ?_⟩

  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

omit [NumberField F] in
theorem Ψ_archEntries (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    Ψ F (archEntries F g) = archEntries F g⁻¹ := by
  set A := (ringEquiv_mixedSpace F).toRingHom.mapMatrix
    (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) with hA
  have hAinv : (ringEquiv_mixedSpace F).toRingHom.mapMatrix
      ((g⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) = A⁻¹ := by
    symm
    apply Matrix.inv_eq_left_inv
    rw [hA, ← map_mul, Units.inv_mul, map_one]
  funext i j
  show (Ring.inverse (ofE F (archEntries F g)).det • (ofE F (archEntries F g)).adjugate) i j
    = archEntries F g⁻¹ i j
  have h2 : archEntries F g⁻¹ i j = (ofE F (archEntries F g⁻¹)) i j := rfl
  rw [h2, ofE_archEntries, ofE_archEntries, hAinv, Matrix.inv_def]

theorem continuousAt_Ψ : ContinuousAt (Ψ F) (cE F) :=
  (continuousOn_Ψ F).continuousAt (closedBall_mem_nhds _ (half_pos (ε_pos F)))

theorem exists_radius {T : Set (GL (Fin 2) (InfiniteAdeleRing F))}
    (hT : T ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ g, dist (archEntries F g) (cE F) < ρ → g ∈ T := by
  have hJ : J F = (fun m : E F => (m, Ψ F m)) ∘ archEntries F := by
    funext g
    rw [Function.comp_apply, J_apply, Ψ_archEntries]
  have hJ1 : J F 1 = (cE F, Ψ F (cE F)) := by
    show J F 1 = (archEntries F 1, Ψ F (archEntries F 1))
    rw [J_apply, inv_one, Ψ_archEntries F 1, inv_one]
  have hcont : ContinuousAt (fun m : E F => (m, Ψ F m)) (cE F) :=
    continuousAt_id.prodMk (continuousAt_Ψ F)
  have h1 : Filter.Tendsto (fun m : E F => (m, Ψ F m)) (𝓝 (cE F)) (𝓝 (J F 1)) := by
    rw [hJ1]
    exact hcont
  have hle : Filter.comap (archEntries F) (𝓝 (cE F)) ≤ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) :=
    calc Filter.comap (archEntries F) (𝓝 (cE F))
        ≤ Filter.comap (archEntries F)
            (Filter.comap (fun m : E F => (m, Ψ F m)) (𝓝 (J F 1))) :=
          Filter.comap_mono (Filter.tendsto_iff_comap.1 h1)
      _ = Filter.comap (J F) (𝓝 (J F 1)) := by rw [Filter.comap_comap, hJ]
      _ = 𝓝 1 := ((isClosedEmbedding_J F).isInducing.nhds_eq_comap 1).symm
  obtain ⟨S, hS, hST⟩ := Filter.mem_comap.1 (hle hT)
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨min δ (ε F / 2), lt_min hδ (half_pos (ε_pos F)), min_le_right _ _, fun g hg => ?_⟩
  exact hST (show g ∈ archEntries F ⁻¹' S from
    hδS (Metric.mem_ball.2 (lt_of_lt_of_le hg (min_le_left _ _))))

theorem continuous_adelicArchGLIncl : Continuous (adelicArchGLIncl F) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      (((k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  · refine continuous_matrix fun i j => ?_
    show Continuous fun k : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) : AdeleRing (𝓞 F) F)
    exact (Units.continuous_coe_inv.matrix_elem i j).prodMk continuous_const

theorem exists_radius_of_continuous (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ ε F / 2 ∧ ∀ m : GL (Fin 2) (InfiniteAdeleRing F),
      dist (archEntries F m) (cE F) < ρ →
        ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2 := by
  have hψ : Continuous fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      φ (g₀ * adelicArchGLIncl F m) - φ g₀ :=
    (hφ.comp (continuous_const.mul (continuous_adelicArchGLIncl F))).sub continuous_const
  have h0 : φ (g₀ * adelicArchGLIncl F 1) - φ g₀ = 0 := by
    rw [map_one, mul_one, sub_self]
  have hT : {m : GL (Fin 2) (InfiniteAdeleRing F) |
      ‖φ (g₀ * adelicArchGLIncl F m) - φ g₀‖ ≤ ‖φ g₀‖ / 2} ∈
        𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) := by
    have hpre := (hψ.continuousAt (x := (1 : GL (Fin 2) (InfiniteAdeleRing F)))).preimage_mem_nhds
      (closedBall_mem_nhds (φ (g₀ * adelicArchGLIncl F 1) - φ g₀) (half_pos (norm_pos_iff.2 hg₀)))
    rw [h0] at hpre
    exact Filter.mem_of_superset hpre fun m hm =>
      mem_closedBall_zero_iff.1 (Set.mem_preimage.1 hm)
  obtain ⟨ρ, hρ, hρε, h⟩ := exists_radius F hT
  exact ⟨ρ, hρ, hρε, fun m hm => h m hm⟩

def bumpAt (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (cE F) where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := half_pos hρ
  rIn_lt_rOut := half_lt_self hρ

def Φ₂ (ρ : ℝ) (hρ : 0 < ρ) (p : E F × E F) : ℂ :=
  (((bumpAt F ρ hρ).toFun p.1 : ℝ) : ℂ) * (((bump₂ F).toFun p.2 : ℝ) : ℂ)

theorem hasCompactSupport_Φ₂ (ρ : ℝ) (hρ : 0 < ρ) : HasCompactSupport (Φ₂ F ρ hρ) := by
  refine HasCompactSupport.intro'
    ((isCompact_closedBall (cE F) (bumpAt F ρ hρ).rOut).prod
      (isCompact_closedBall (cE F) (bump₂ F).rOut))
    (isClosed_closedBall.prod isClosed_closedBall) fun p hp => ?_
  rw [Set.mem_prod, not_and_or] at hp
  rcases hp with h | h
  · have h' : (bumpAt F ρ hρ).toFun p.1 = 0 :=
      (bumpAt F ρ hρ).zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']
  · have h' : (bump₂ F).toFun p.2 = 0 :=
      (bump₂ F).zero_of_le_dist (le_of_lt (by rwa [mem_closedBall, not_le] at h))
    simp [Φ₂, h']

def fa (ρ : ℝ) (hρ : 0 < ρ) : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := Φ₂ F ρ hρ ∘ J F

theorem fa_apply (ρ : ℝ) (hρ : 0 < ρ) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F ρ hρ g = (((bumpAt F ρ hρ).toFun (archEntries F g) : ℝ) : ℂ) *
      (((bump₂ F).toFun (archEntries F g⁻¹) : ℝ) : ℂ) := rfl

theorem fa_eq (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    fa F ρ hρ g = (((bumpAt F ρ hρ).toFun (archEntries F g) : ℝ) : ℂ) := by
  rw [fa_apply]
  by_cases h : archEntries F g ∈ closedBall (cE F) (ε F / 2)
  · rw [(bump₂ F).one_of_mem_closedBall (archEntries_inv_mem F g h), Complex.ofReal_one, mul_one]
  · have h0 : (bumpAt F ρ hρ).toFun (archEntries F g) = 0 := by
      apply (bumpAt F ρ hρ).zero_of_le_dist
      rw [mem_closedBall, not_le] at h
      exact le_of_lt (lt_of_le_of_lt hρε h)
    rw [h0, Complex.ofReal_zero, zero_mul]

theorem isArchTestFactor_fa (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) :
    IsArchTestFactor F (fa F ρ hρ) := by
  refine ⟨⟨fun m => (((bumpAt F ρ hρ).toFun m : ℝ) : ℂ), ?_, fun g => fa_eq F ρ hρ hρε g⟩, ?_⟩
  · have hc : (fun m : E F => (((bumpAt F ρ hρ).toFun m : ℝ) : ℂ))
        = Complex.ofRealCLM ∘ (bumpAt F ρ hρ).toFun := by
      funext m
      simp
    rw [hc]
    exact Complex.ofRealCLM.contDiff.comp (bumpAt F ρ hρ).contDiff
  · exact (hasCompactSupport_Φ₂ F ρ hρ).comp_isClosedEmbedding (isClosedEmbedding_J F)

def Kf (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))

def ff (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Kf F N).indicator fun _ => 1

theorem isOpen_Kf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (Kf F N) :=
  AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F hN

theorem isClosed_Kf (N : Ideal (𝓞 F)) : IsClosed (Kf F N) :=
  AdelicLevel.isClosed_finiteLevelOne (𝓞 F) F N

theorem isCompact_Kf (N : Ideal (𝓞 F)) : IsCompact (Kf F N) :=
  AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N

theorem isFinTestFactor_ff {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFinTestFactor F (ff F N) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_Kf F N) (isClosed_Kf F N)
    fun x hx => Set.indicator_of_notMem hx _⟩
  intro s
  have hpre : ff F N ⁻¹' s
      = (if (1 : ℂ) ∈ s then Kf F N else ∅) ∪ (if (0 : ℂ) ∈ s then (Kf F N)ᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ Kf F N <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
      simp [ff, Set.indicator, hx, h1, h0]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact isOpen_Kf F hN
    · exact isOpen_empty
  · split_ifs
    · exact (isClosed_Kf F N).isOpen_compl
    · exact isOpen_empty

theorem ff_mul_of_mem (N : Ideal (𝓞 F)) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ff F N (k * x) = ff F N x := by
  by_cases hx : x ∈ Kf F N
  · have hx' : x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N := hx
    have hkx : k * x ∈ Kf F N := mul_mem hk hx'
    simp only [ff, Set.indicator_of_mem hx, Set.indicator_of_mem hkx]
  · have hkx : k * x ∉ Kf F N := fun h =>
      hx ((Subgroup.mul_mem_cancel_left (AdelicLevel.finiteLevelOne (𝓞 F) F N) hk).1
        (show k * x ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N from h))
    simp only [ff, Set.indicator_of_notMem hx, Set.indicator_of_notMem hkx]

def testFn (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
  fa F ρ hρ (AdelicLevel.glArch (𝓞 F) F g) * ff F N (AdelicLevel.glFin (𝓞 F) F g)

def testFnR (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
  (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F g)) *
    (Kf F N).indicator (fun _ => (1 : ℝ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isFactorizableTestFn_testFn (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2)
    {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFactorizableTestFn F (testFn F ρ hρ N) :=
  ⟨fa F ρ hρ, ff F N, isArchTestFactor_fa F ρ hρ hρε, isFinTestFactor_ff F hN, fun _ => rfl⟩

theorem testFn_mul_of_mem (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (x : AdelicGL2 (𝓞 F) F) :
    testFn F ρ hρ N (k * x) = testFn F ρ hρ N x := by
  obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_inf.1 hk
  have h1 : AdelicLevel.glArch (𝓞 F) F k = 1 := (mem_finiteAdelicGL2Subgroup_iff F k).1 hk₂
  have h2 : AdelicLevel.glFin (𝓞 F) F k ∈ AdelicLevel.finiteLevelOne (𝓞 F) F N :=
    AdelicLevel.mem_levelOne_iff.1 hk₁
  simp only [testFn, map_mul, h1, one_mul, ff_mul_of_mem F N h2]

theorem testFn_decomp (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N) :
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x ∈
      AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [AdelicLevel.mem_levelOne_iff, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hx
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_mem_of_testFn_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F))
    (x : AdelicGL2 (𝓞 F) F) (hx : testFn F ρ hρ N x ≠ 0) : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  by_contra h
  exact hx (by simp only [testFn, ff, Set.indicator_of_notMem h, mul_zero])

theorem testFn_support (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFn F ρ hρ N x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, AdelicLevel.glFin (𝓞 F) F a = 1 ∧
      k ∈ AdelicLevel.levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k :=
  ⟨adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x),
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x, glFin_adelicArchGLIncl F _,
    testFn_decomp F N x (glFin_mem_of_testFn_ne_zero F ρ hρ N x hx), (mul_inv_cancel_left _ _).symm⟩

theorem testFn_eq_ofReal (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) : testFn F ρ hρ N g = ((testFnR F ρ hρ N g : ℝ) : ℂ) := by
  simp only [testFn, testFnR, fa_eq F ρ hρ hρε, ff, Complex.ofReal_mul]
  congr 1
  by_cases h : AdelicLevel.glFin (𝓞 F) F g ∈ Kf F N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]

theorem testFnR_nonneg (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ testFnR F ρ hρ N g :=
  mul_nonneg (bumpAt F ρ hρ).nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem testFnR_one (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : testFnR F ρ hρ N 1 = 1 := by
  have h1 : (bumpAt F ρ hρ).toFun (archEntries F 1) = 1 :=
    (bumpAt F ρ hρ).one_of_mem_closedBall (mem_closedBall_self (bumpAt F ρ hρ).rIn_pos.le)
  have h2 : (Kf F N).indicator (fun _ => (1 : ℝ)) 1 = 1 :=
    Set.indicator_of_mem
      (show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ Kf F N from
        (AdelicLevel.finiteLevelOne (𝓞 F) F N).one_mem) _
  simp only [testFnR, map_one, h1, h2, mul_one]

theorem of_testFnR_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFnR F ρ hρ N x ≠ 0) :
    dist (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) (cE F) < ρ ∧
      AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have h0 : (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) = 0 :=
      (bumpAt F ρ hρ).zero_of_le_dist h
    exact hx (by simp only [testFnR, h0, zero_mul])
  · by_contra h
    exact hx (by simp only [testFnR, Set.indicator_of_notMem h, mul_zero])

theorem rightConv_ne_zero_of_bound (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (hR1 : fR 1 ≠ 0)
    (hbound : ∀ x, fR x ≠ 0 → ‖φ (g₀ * x) - φ g₀‖ ≤ ‖φ g₀‖ / 2) :
    rightConv F φ f g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  have hIpos : 0 < ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (integral_pos_iff_support_of_nonneg (fun x => hR0 x) hRi).2
      (hRc.isOpen_support.measure_pos _ ⟨1, hR1⟩)
  have hmul : Continuous fun x : AdelicGL2 (𝓞 F) F => g₀ * x := continuous_const.mul continuous_id
  have hi₁ : Integrable (fun x => φ (g₀ * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ((hφ.comp hmul).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₂ : Integrable (fun x => φ g₀ * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hfc.integrable_of_hasCompactSupport hfs).const_mul _
  have h3 : ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
    simp only [hfR]
    exact integral_complex_ofReal
  intro h0
  have h2 : ∫ x, φ (g₀ * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := h0
  have hint : ∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = -(φ g₀ * ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ)) := by
    have h1 : (fun x => (φ (g₀ * x) - φ g₀) * f x) = fun x => φ (g₀ * x) * f x - φ g₀ * f x := by
      funext x
      ring
    rw [h1, integral_sub hi₁ hi₂, h2, integral_const_mul, h3, zero_sub]
  have hle : ‖∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)‖
      ≤ ∫ x, ‖φ g₀‖ / 2 * fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine norm_integral_le_of_norm_le (hRi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hfR x, Complex.norm_real, Real.norm_of_nonneg (hR0 x)]
    by_cases hx : fR x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hbound x hx) (hR0 x)
  rw [hint, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le,
    integral_const_mul] at hle
  have hc : 0 < ‖φ g₀‖ := norm_pos_iff.2 hg₀
  nlinarith [mul_pos hc hIpos]

end TestFnNearIdentity

end AutomorphicForm

end
