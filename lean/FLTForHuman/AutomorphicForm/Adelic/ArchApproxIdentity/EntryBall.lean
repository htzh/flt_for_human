/-
  Entry balls, the determinant locus and the archimedean bump/approximate identity.

  This is the second half of the adèlic infrastructure behind
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`:
  `matrixEntries` reads the archimedean matrix coordinates in the mixed space, the
  balls `entryBall` around the identity (closed, compact and a neighbourhood basis,
  `exists_entryBall_subset`), the determinant locus `detLocus` with its inverse map
  `piInv` and the partial inverse `toGL`, the bump `exists_bump` built from a
  `ContDiffBump` on the mixed space, the approximate identity `exists_approxIdentity`
  supported in a shrinking neighbourhood of `1`, and its smoothing limit
  `tendsto_integral_mul_approxIdentity`. The closing section `Q09RowIso` records the
  archimedean row-isometry component and injectivity.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:520–923`
  (pinned `aa2d8b3`), the adèlic half `Q2`. As in `ArchInfra`, the pin's declarations
  are `private` and land here public as the shared engine, keeping the pin's
  sub-namespaces `Q09AIarchG`/`Q09RowIso`. The one local re-derivation is the
  pin-`private` proof helper `continuous_archEntries` (its port twin
  `AutomorphicForm.TestFnTop.continuous_archEntries` is `private` and a promotion is
  the manager's call), which keeps its pin name and stays `private`.
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls and the bump proof feed instance search.
set_option linter.style.haveILetI false

open NumberField NumberField.AdelicLevel AutomorphicForm IsDedekindDomain Matrix MeasureTheory
  Filter Topology TopologicalSpace

noncomputable section

namespace Q09AIarchG

attribute [local instance] Q09AIarchC.t2Space_archMatrix' Q09AIarchC.locallyCompactSpace_archMatrix
  Q09AIarchC.locallyCompactSpace_archGL Q09AIarchC.isTopologicalGroup_archGL
  Q09AIarchC.secondCountableTopology_archGL Q09AIarchC.secondCountableTopology_piRowIsometrySubgroup₀

section Gamma

variable (F : Type) [Field F] [NumberField F]

-- pin: t2Space_archMatrix (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:540)
omit [NumberField F] in
theorem t2Space_archMatrix : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

attribute [local instance] t2Space_archMatrix

-- pin: EntrySpace (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:545)
abbrev EntrySpace : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F

-- pin: matrixEntries (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:547)
def matrixEntries (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) : EntrySpace F :=
  fun i j => InfiniteAdeleRing.ringEquiv_mixedSpace F (m i j)

-- pin: archEntries_eq (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:551)
omit [NumberField F] in
theorem archEntries_eq (g : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F g = matrixEntries F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  rfl

-- pin: ringEquiv_mixedSpace_eq (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:556)
omit [NumberField F] in
theorem ringEquiv_mixedSpace_eq :
    ⇑(InfiniteAdeleRing.ringEquiv_mixedSpace F) = fun x : InfiniteAdeleRing F =>
      ((fun v : {w : InfinitePlace F // w.IsReal} =>
          InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v)),
        (fun v : {w : InfinitePlace F // w.IsComplex} =>
          InfinitePlace.Completion.extensionEmbedding v.1 (x v))) :=
  funext fun x => InfiniteAdeleRing.ringEquiv_mixedSpace_apply F x

-- pin: continuous_matrixEntries (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:565)
omit [NumberField F] in
theorem continuous_matrixEntries : Continuous (matrixEntries F) :=
  continuous_pi fun i => continuous_pi fun j =>
    (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F).comp (continuous_id.matrix_elem i j)

-- pin: continuous_archEntries (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:570)
omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) :=
  (continuous_matrixEntries F).comp Units.continuous_val

section EntryBalls

open scoped Classical

-- pin: dist_apply_le_dist_ringEquiv (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:577)
theorem dist_apply_le_dist_ringEquiv (x y : InfiniteAdeleRing F) (w : InfinitePlace F) :
    dist (x w) (y w) ≤
      dist (InfiniteAdeleRing.ringEquiv_mixedSpace F x) (InfiniteAdeleRing.ringEquiv_mixedSpace F y) := by
  rw [ringEquiv_mixedSpace_eq, Prod.dist_eq]
  rcases w.isReal_or_isComplex with hw | hw
  · refine le_trans ?_ (le_max_left _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).dist_eq (x w) (y w)]
    exact dist_le_pi_dist
      (fun v : {w : InfinitePlace F // w.IsReal} => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (x v))
      (fun v : {w : InfinitePlace F // w.IsReal} => InfinitePlace.Completion.extensionEmbeddingOfIsReal v.2 (y v))
      ⟨w, hw⟩
  · refine le_trans ?_ (le_max_right _ _)
    rw [← (InfinitePlace.Completion.isometry_extensionEmbedding w).dist_eq (x w) (y w)]
    exact dist_le_pi_dist
      (fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (x v))
      (fun v : {w : InfinitePlace F // w.IsComplex} => InfinitePlace.Completion.extensionEmbedding v.1 (y v))
      ⟨w, hw⟩

-- pin: dist_entry_le (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:595)
theorem dist_entry_le (m n : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2)
    (w : InfinitePlace F) :
    dist (m i j w) (n i j w) ≤ dist (matrixEntries F m) (matrixEntries F n) :=
  (dist_apply_le_dist_ringEquiv F (m i j) (n i j) w).trans
    ((dist_le_pi_dist (matrixEntries F m i) (matrixEntries F n i) j).trans
      (dist_le_pi_dist (matrixEntries F m) (matrixEntries F n) i))

-- pin: entryBall (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:602)
def entryBall (r : ℝ) : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  {m | dist (matrixEntries F m) (matrixEntries F 1) ≤ r}

-- pin: one_mem_entryBall (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:605)
theorem one_mem_entryBall {r : ℝ} (hr : 0 ≤ r) :
    (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F r := by
  show dist _ _ ≤ r
  rw [dist_self]
  exact hr

-- pin: entryBall_mono (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:611)
theorem entryBall_mono {r s : ℝ} (h : r ≤ s) : entryBall F r ⊆ entryBall F s := fun m hm =>
  show dist (matrixEntries F m) (matrixEntries F 1) ≤ s from
    le_trans (show dist (matrixEntries F m) (matrixEntries F 1) ≤ r from hm) h

-- pin: isClosed_entryBall (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:615)
theorem isClosed_entryBall (r : ℝ) : IsClosed (entryBall F r) :=
  isClosed_le ((continuous_matrixEntries F).dist continuous_const) continuous_const

-- pin: isCompact_entryBall (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:618)
theorem isCompact_entryBall (r : ℝ) : IsCompact (entryBall F r) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion :=
    fun w => NumberField.AdelicBox.properSpace_completion (K := F) w
  have hbox : IsCompact ((Set.pi Set.univ fun i : Fin 2 => Set.pi Set.univ fun j : Fin 2 =>
      Set.pi Set.univ fun w : InfinitePlace F =>
        Metric.closedBall ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w) r) :
          Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine hbox.of_isClosed_subset (isClosed_entryBall F r) fun m hm => ?_
  have hm' : dist (matrixEntries F m) (matrixEntries F 1) ≤ r := hm
  exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j => Set.mem_univ_pi.mpr fun w =>
    Metric.mem_closedBall.mpr ((dist_entry_le F m 1 i j w).trans hm')

-- pin: exists_entryBall_subset (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:631)
theorem exists_entryBall_subset {N : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))}
    (hN : N ∈ 𝓝 (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) : ∃ r > 0, entryBall F r ⊆ N := by

  have hN' : (id N : Set (Fin 2 → Fin 2 → ((w : InfinitePlace F) → w.Completion))) ∈
      @nhds (Fin 2 → Fin 2 → ((w : InfinitePlace F) → w.Completion)) _
        (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hN'
  refine ⟨ε / 2, by positivity, fun m hm => hball ?_⟩
  have hm' : dist (matrixEntries F m) (matrixEntries F 1) ≤ ε / 2 := hm

  have key : dist (id m : Fin 2 → Fin 2 → ((w : InfinitePlace F) → w.Completion))
      (id (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) : Fin 2 → Fin 2 → ((w : InfinitePlace F) → w.Completion))
      < ε :=
    (dist_pi_lt_iff hε).mpr fun i => (dist_pi_lt_iff hε).mpr fun j => (dist_pi_lt_iff hε).mpr fun w =>
      lt_of_le_of_lt ((dist_entry_le F m 1 i j w).trans hm') (half_lt_self hε)
  exact Metric.mem_ball.mpr key

end EntryBalls

-- pin: detLocus (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:651)
def detLocus : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  {m | ∀ w : InfinitePlace F, m.det w ≠ 0}

-- pin: continuous_det_apply (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:655)
omit [NumberField F] in
theorem continuous_det_apply (w : InfinitePlace F) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m.det w := by
  have hdet : Continuous fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m.det :=
    continuous_id.matrix_det
  exact (continuous_apply w : Continuous fun a : (∀ w : InfinitePlace F, w.Completion) => a w).comp hdet

-- pin: isOpen_detLocus (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:661)
theorem isOpen_detLocus : IsOpen (detLocus F) := by
  have h : detLocus F = ⋂ w : InfinitePlace F,
      (fun m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) => m.det w) ⁻¹' {0}ᶜ := by
    ext m
    simp [detLocus]
  rw [h]
  exact isOpen_iInter_of_finite fun w => isOpen_compl_singleton.preimage (continuous_det_apply F w)

-- pin: one_mem_detLocus (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:670)
omit [NumberField F] in
theorem one_mem_detLocus : (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ detLocus F := fun w => by
  rw [Matrix.det_one]
  exact one_ne_zero

-- pin: piInv (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:674)
def piInv (x : InfiniteAdeleRing F) : InfiniteAdeleRing F := fun w => (x w)⁻¹

-- pin: mul_piInv (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:677)
omit [NumberField F] in
theorem mul_piInv {x : InfiniteAdeleRing F} (hx : ∀ w, x w ≠ 0) : x * piInv F x = 1 :=
  funext fun w => mul_inv_cancel₀ (hx w)

-- pin: piInv_mul (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:681)
omit [NumberField F] in
theorem piInv_mul {x : InfiniteAdeleRing F} (hx : ∀ w, x w ≠ 0) : piInv F x * x = 1 :=
  funext fun w => inv_mul_cancel₀ (hx w)

-- pin: isUnit_of_forall_ne_zero (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:685)
omit [NumberField F] in
theorem isUnit_of_forall_ne_zero {x : InfiniteAdeleRing F} (hx : ∀ w, x w ≠ 0) : IsUnit x :=
  ⟨⟨x, piInv F x, mul_piInv F hx, piInv_mul F hx⟩, rfl⟩

-- pin: ringInverse_eq (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:689)
omit [NumberField F] in
theorem ringInverse_eq {x : InfiniteAdeleRing F} (hx : ∀ w, x w ≠ 0) : Ring.inverse x = piInv F x :=
  Ring.inverse_unit ⟨x, piInv F x, mul_piInv F hx, piInv_mul F hx⟩

variable {F}

-- pin: toGL (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:694)
def toGL {r₀ : ℝ} (h₀ : entryBall F r₀ ⊆ detLocus F) (m : entryBall F r₀) :
    GL (Fin 2) (InfiniteAdeleRing F) where
  val := m.1
  inv := m.1⁻¹
  val_inv := Matrix.mul_nonsing_inv _ (isUnit_of_forall_ne_zero F (h₀ m.2))
  inv_val := Matrix.nonsing_inv_mul _ (isUnit_of_forall_ne_zero F (h₀ m.2))

-- pin: toGL_eq (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:701)
theorem toGL_eq {r₀ : ℝ} (h₀ : entryBall F r₀ ⊆ detLocus F) (g : GL (Fin 2) (InfiniteAdeleRing F))
    (hg : (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F r₀) : toGL h₀ ⟨g, hg⟩ = g :=
  Units.ext rfl

-- pin: continuous_toGL (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:705)
theorem continuous_toGL {r₀ : ℝ} (h₀ : entryBall F r₀ ⊆ detLocus F) : Continuous (toGL h₀) := by
  have hdet : Continuous fun m : entryBall F r₀ => Ring.inverse (m.1.det) := by
    have heq : (fun m : entryBall F r₀ => Ring.inverse (m.1.det)) = fun m => piInv F m.1.det :=
      funext fun m => ringInverse_eq F (h₀ m.2)
    rw [heq]
    refine continuous_pi fun w => ?_
    exact ((continuous_det_apply F w).comp continuous_subtype_val).inv₀ fun m => h₀ m.2 w
  refine Units.continuous_iff.mpr ⟨continuous_subtype_val, ?_⟩
  show Continuous fun m : entryBall F r₀ => (m.1)⁻¹
  have heq : (fun m : entryBall F r₀ => (m.1)⁻¹) = fun m => Ring.inverse (m.1.det) • m.1.adjugate :=
    funext fun m => Matrix.inv_def m.1
  rw [heq]
  exact continuous_matrix fun i j => hdet.mul (continuous_subtype_val.matrix_adjugate.matrix_elem i j)

variable (F)

-- pin: archGLMeasurableSpace (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:721)
abbrev archGLMeasurableSpace : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLMeasurableSpace

-- pin: archGLBorelSpace (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:727)
omit [NumberField F] in
theorem archGLBorelSpace : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  borelSpace_glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLBorelSpace

-- pin: exists_bump (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:733)
open scoped Classical in
theorem exists_bump [(archHaarK F).IsHaarMeasure] {r₀ : ℝ} (h₀ : entryBall F r₀ ⊆ detLocus F) {ρ : ℝ}
    (hρ : 0 < ρ) (hρ₀ : ρ ≤ r₀) :
    ∃ ψ : GL (Fin 2) (InfiniteAdeleRing F) → ℝ,
      IsArchTestFactor F (fun g => (ψ g : ℂ)) ∧ Continuous ψ ∧ HasCompactSupport ψ ∧ (∀ g, 0 ≤ ψ g) ∧
        tsupport ψ ⊆ {g : GL (Fin 2) (InfiniteAdeleRing F) |
          (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ} ∧
        (∫ g, ψ g ∂archHaarK F) = 1 := by
  let b : ContDiffBump (matrixEntries F 1) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  set f₀ : GL (Fin 2) (InfiniteAdeleRing F) → ℝ := fun g => b.toFun (archEntries F g) with hf₀
  set S : Set (GL (Fin 2) (InfiniteAdeleRing F)) :=
    {g | (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ} with hS_def
  have hcont : Continuous f₀ := b.continuous.comp (continuous_archEntries F)
  have hS : IsClosed S := (isClosed_entryBall F ρ).preimage Units.continuous_val
  have hsupp : Function.support f₀ ⊆ S := by
    intro g hg
    have hg' : archEntries F g ∈ Function.support b.toFun := hg
    rw [b.support_eq] at hg'
    have hlt : dist (matrixEntries F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) (matrixEntries F 1) < ρ :=
      Metric.mem_ball.mp hg'
    show dist (matrixEntries F (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) (matrixEntries F 1) ≤ ρ
    exact hlt.le
  have htsupp : tsupport f₀ ⊆ S := closure_minimal hsupp hS

  haveI : CompactSpace (entryBall F r₀) := isCompact_iff_compactSpace.mp (isCompact_entryBall F r₀)
  have hT : IsCompact {m : entryBall F r₀ | (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ} :=
    ((isClosed_entryBall F ρ).preimage continuous_subtype_val).isCompact
  have hK : IsCompact (toGL h₀ '' {m : entryBall F r₀ |
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ}) :=
    hT.image (continuous_toGL h₀)
  have hSK : S ⊆ toGL h₀ '' {m : entryBall F r₀ |
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ} :=
    fun g hg => by
      have hg' : (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F ρ := hg
      exact ⟨⟨g, entryBall_mono F hρ₀ hg'⟩, hg', toGL_eq h₀ g _⟩
  have hcs : HasCompactSupport f₀ := hK.of_isClosed_subset (isClosed_tsupport f₀) (htsupp.trans hSK)
  have hnn : ∀ g, 0 ≤ f₀ g := fun _ => b.nonneg
  have hone : f₀ 1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
  have hI : 0 < ∫ g, f₀ g ∂archHaarK F :=
    hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 1) hcs hnn (by rw [hone]; exact one_ne_zero)
  set I : ℝ := ∫ g, f₀ g ∂archHaarK F with hI_def
  refine ⟨fun g => f₀ g / I, ?_, hcont.div_const I, ?_, fun g => div_nonneg (hnn g) hI.le, ?_, ?_⟩
  · refine ⟨⟨fun v => ((b.toFun v / I : ℝ) : ℂ), ?_, fun _ => rfl⟩, ?_⟩
    · exact Complex.ofRealCLM.contDiff.comp (b.contDiff.div_const I)
    · exact hcs.comp_left (g := fun t : ℝ => ((t / I : ℝ) : ℂ)) (by simp)
  · exact hcs.comp_left (g := fun t : ℝ => t / I) (zero_div I)
  · refine closure_minimal (fun g hg => hsupp (Function.mem_support.mpr fun h => Function.mem_support.mp hg ?_)) hS
    show f₀ g / I = 0
    rw [h, zero_div]
  · exact (integral_div I f₀).trans (div_self hI.ne')

-- pin: exists_approxIdentity (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:783)
theorem exists_approxIdentity [(archHaarK F).IsHaarMeasure] :
    ∃ ψ : ℕ → GL (Fin 2) (InfiniteAdeleRing F) → ℝ,
      (∀ n, IsArchTestFactor F (fun g => (ψ n g : ℂ)) ∧ Continuous (ψ n) ∧ HasCompactSupport (ψ n) ∧
        (∀ g, 0 ≤ ψ n g) ∧ (∫ g, ψ n g ∂archHaarK F) = 1) ∧
      ∀ U ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U := by
  obtain ⟨r₀, hr₀, h₀⟩ := exists_entryBall_subset F ((isOpen_detLocus F).mem_nhds (one_mem_detLocus F))
  have hρ : ∀ n : ℕ, 0 < min r₀ (1 / ((n : ℝ) + 1)) := fun n => lt_min hr₀ (by positivity)
  choose ψ hψ using fun n : ℕ => exists_bump F h₀ (hρ n) (min_le_left _ _)
  refine ⟨ψ, fun n => ⟨(hψ n).1, (hψ n).2.1, (hψ n).2.2.1, (hψ n).2.2.2.1, (hψ n).2.2.2.2.2⟩, ?_⟩
  intro U hU
  have hone : (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F r₀ := one_mem_entryBall F hr₀.le
  have h1 : toGL h₀ ⟨1, hone⟩ = 1 := Units.ext rfl
  have hU' : toGL h₀ ⁻¹' U ∈ 𝓝 (⟨1, hone⟩ : entryBall F r₀) := by
    refine (continuous_toGL h₀).continuousAt.preimage_mem_nhds ?_
    rwa [h1]
  obtain ⟨N, hN, hNU⟩ := (mem_nhds_subtype _ _ _).mp hU'
  obtain ⟨r₁, hr₁, hr₁N⟩ := exists_entryBall_subset F hN
  obtain ⟨n₀, hn₀⟩ := exists_nat_one_div_lt hr₁
  refine eventually_atTop.mpr ⟨n₀, fun n hn => (hψ n).2.2.2.2.1.trans fun g hg => ?_⟩
  have hle : min r₀ (1 / ((n : ℝ) + 1)) ≤ r₁ := by
    refine (min_le_right _ _).trans (le_of_lt (lt_of_le_of_lt ?_ hn₀))
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hn 1)
  have hg' : (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F (min r₀ (1 / ((n : ℝ) + 1))) := hg
  have hg₀ : (g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ entryBall F r₀ :=
    entryBall_mono F (min_le_left _ _) hg'
  have hgN : (⟨g, hg₀⟩ : entryBall F r₀) ∈ Subtype.val ⁻¹' N := hr₁N (entryBall_mono F hle hg')
  have hgU := hNU hgN
  rwa [Set.mem_preimage, toGL_eq h₀ g hg₀] at hgU

-- pin: tendsto_integral_mul_approxIdentity (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:812)
theorem tendsto_integral_mul_approxIdentity [(archHaarK F).IsHaarMeasure]
    {ψ : ℕ → GL (Fin 2) (InfiniteAdeleRing F) → ℝ} (hcont : ∀ n, Continuous (ψ n))
    (hcs : ∀ n, HasCompactSupport (ψ n)) (hnn : ∀ n g, 0 ≤ ψ n g)
    (hint : ∀ n, (∫ g, ψ n g ∂archHaarK F) = 1)
    (hsupp : ∀ U ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)), ∀ᶠ n in atTop, tsupport (ψ n) ⊆ U)
    {φ : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ g, φ g * (ψ n g : ℂ) ∂archHaarK F) atTop (𝓝 (φ 1)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hV : φ ⁻¹' Metric.ball (φ 1) (ε / 2) ∈ 𝓝 (1 : GL (Fin 2) (InfiniteAdeleRing F)) :=
    hφ.continuousAt.preimage_mem_nhds (Metric.ball_mem_nhds _ (by positivity))
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp (hsupp _ hV)
  refine ⟨n₀, fun n hn => ?_⟩
  have hsub := hn₀ n hn
  have hψc : Continuous fun g => (ψ n g : ℂ) := Complex.continuous_ofReal.comp (hcont n)

  have hψcs : HasCompactSupport fun g => (ψ n g : ℂ) :=
    (hcs n).comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hi₁ : Integrable (fun g => φ g * (ψ n g : ℂ)) (archHaarK F) :=
    (hφ.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have hi₂ : Integrable (fun g => φ 1 * (ψ n g : ℂ)) (archHaarK F) :=
    (continuous_const.mul hψc).integrable_of_hasCompactSupport hψcs.mul_left
  have h1 : (∫ g, φ 1 * (ψ n g : ℂ) ∂archHaarK F) = φ 1 := by
    calc (∫ g, φ 1 * (ψ n g : ℂ) ∂archHaarK F) = φ 1 * ∫ g, (ψ n g : ℂ) ∂archHaarK F := integral_const_mul _ _
      _ = φ 1 * ((∫ g, ψ n g ∂archHaarK F : ℝ) : ℂ) := by rw [integral_complex_ofReal]
      _ = φ 1 := by rw [hint n, Complex.ofReal_one, mul_one]
  have hdiff : (∫ g, φ g * (ψ n g : ℂ) ∂archHaarK F) - φ 1 =
      ∫ g, (φ g - φ 1) * (ψ n g : ℂ) ∂archHaarK F := by
    calc (∫ g, φ g * (ψ n g : ℂ) ∂archHaarK F) - φ 1
        = (∫ g, φ g * (ψ n g : ℂ) ∂archHaarK F) - ∫ g, φ 1 * (ψ n g : ℂ) ∂archHaarK F := by rw [h1]
      _ = ∫ g, (φ g * (ψ n g : ℂ) - φ 1 * (ψ n g : ℂ)) ∂archHaarK F := (integral_sub hi₁ hi₂).symm
      _ = ∫ g, (φ g - φ 1) * (ψ n g : ℂ) ∂archHaarK F := by simp only [sub_mul]
  have hbound : ∀ g, ‖(φ g - φ 1) * (ψ n g : ℂ)‖ ≤ ε / 2 * ψ n g := by
    intro g
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hnn n g)]
    by_cases hg : g ∈ tsupport (ψ n)
    · have hlt : ‖φ g - φ 1‖ < ε / 2 := by
        have h := Metric.mem_ball.mp (hsub hg)
        rwa [dist_eq_norm] at h
      exact mul_le_mul_of_nonneg_right hlt.le (hnn n g)
    · simp [image_eq_zero_of_notMem_tsupport hg]
  have hi₃ : Integrable (fun g => ‖(φ g - φ 1) * (ψ n g : ℂ)‖) (archHaarK F) :=
    (((hφ.sub continuous_const).mul hψc).integrable_of_hasCompactSupport hψcs.mul_left).norm
  have hi₄ : Integrable (fun g => ε / 2 * ψ n g) (archHaarK F) :=
    (continuous_const.mul (hcont n)).integrable_of_hasCompactSupport (hcs n).mul_left
  rw [dist_eq_norm, hdiff]
  calc ‖∫ g, (φ g - φ 1) * (ψ n g : ℂ) ∂archHaarK F‖
      ≤ ∫ g, ‖(φ g - φ 1) * (ψ n g : ℂ)‖ ∂archHaarK F := norm_integral_le_integral_norm _
    _ ≤ ∫ g, ε / 2 * ψ n g ∂archHaarK F := integral_mono hi₃ hi₄ hbound
    _ = ε / 2 * ∫ g, ψ n g ∂archHaarK F := integral_const_mul _ _
    _ = ε / 2 := by rw [hint n, mul_one]
    _ < ε := half_lt_self hε

end Gamma

end Q09AIarchG

namespace Q09RowIso

variable (F : Type) [Field F]

-- pin: archComponent_archRowIsometryInclAt₀ (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:885)
theorem archComponent_archRowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
  archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

-- pin: archRowIsometryInclAt₀_injective (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:890)
theorem archRowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_archRowIsometryInclAt₀ F w a
  have hb := archComponent_archRowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

variable [NumberField F]

-- pin: archComponent_glArch_rowIsometryInclAt₀ (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:899)
theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archRowIsometryInclAt₀ F w k

-- pin: rowIsometryInclAt₀_injective (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:906)
theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

-- pin: forall_rowIsometryInclAt₀_injective (S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:913)
theorem forall_rowIsometryInclAt₀_injective :
    ∀ w : InfinitePlace F, Function.Injective (rowIsometryInclAt₀ F w) :=
  rowIsometryInclAt₀_injective F

end Q09RowIso

end
