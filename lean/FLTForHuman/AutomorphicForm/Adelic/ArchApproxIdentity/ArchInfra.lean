/-
  Archimedean infrastructure for the approximate identity on `GL₂(𝔸_{K,∞})`.

  This is the first half of the adèlic infrastructure behind
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`:
  the Haar measure `archHaarK` is Haar (`isHaarMeasure_archHaarK`), the archimedean
  topology is second countable (the `SecondCountableTopology` facts on `𝔸_{K,∞}`, its
  matrix ring and `GL₂`), the row-isometry subgroup `rowIsometrySubgroup₀` is compact
  (`rowIsoSet`, `toUnit`, `isCompact_rowIsometrySubgroup₀`), the product `Kprod` of
  the local row-isometry subgroups carries the product Haar measure `muK`, the
  inclusion `inclArch`/`inclAdelic` into `GL₂(𝔸_K)` is continuous, and `archHaarK` is
  invariant under right translation by the image of `inclArch`
  (`integral_archHaarK_mul_inclArch`).

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:9–517`
  (pinned `aa2d8b3`), the adèlic half `Q1`. The pin's declarations are `private` and
  land here public as the shared engine, in three namespaces: `ArchInfra` (the pin's
  `Q09AIarch` — the product group, its Haar measure and the inclusions), `ArchInfraTopology`
  (the pin's `Q09AIarchC` — the measurable-space and locally-compact/second-countable
  instances, kept apart because three of their names coincide with the first block's) and
  `ArchApproxIdentity` (one declaration of the pin's shared `Q09` engine, which the other
  three movements re-open). Substitutions: the pin's `continuous_adelicArchGLIncl` is the
  port's public `AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl`, so
  no local copy is written. The pin's `p2m_export`/`p2m_reactivate`/`p2m_open` lines
  are not transcribed; the `scoped` instances (`compactSpace_Kw`, the `muK`
  probability/left-invariance/Haar facts) stay local to this module, as at the pin.
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchHaar
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.TestFnNearIdentity
import FLTForHuman.AutomorphicForm.Adelic.RightConvComm.Frame
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Sets.Compacts
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls feed instance search (Haar measure and inclusions).
set_option linter.style.haveILetI false

open NumberField NumberField.AdelicLevel AutomorphicForm AutomorphicForm.WindowedSiegel
  IsDedekindDomain Matrix MeasureTheory Topology TopologicalSpace

noncomputable section

namespace ArchApproxIdentity

variable (F : Type) [Field F] [NumberField F]

theorem isHaarMeasure_archHaarK :
    @Measure.IsHaarMeasure (GL (Fin 2) (InfiniteAdeleRing F)) _ _ (glBorelOf (InfiniteAdeleRing F))
      (archHaarK F) := by
  letI := glBorelOf (InfiniteAdeleRing F)
  haveI := borelSpace_glBorelOf (InfiniteAdeleRing F)
  haveI : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  exact Measure.isHaarMeasure_haarMeasure _

end ArchApproxIdentity

namespace ArchInfraTopology

variable (F : Type) [Field F] [NumberField F]

theorem secondCountableTopology_infiniteAdeleRing : SecondCountableTopology (InfiniteAdeleRing F) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion :=
    fun w => NumberField.AdelicBox.properSpace_completion (K := F) w
  exact inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))

theorem secondCountableTopology_archMatrix :
    SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_infiniteAdeleRing F
  exact inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → InfiniteAdeleRing F))

omit [NumberField F] in
theorem t2Space_archMatrix' : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

theorem secondCountableTopology_archGL : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := secondCountableTopology_archMatrix F
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

theorem locallyCompactSpace_archMatrix :
    LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))

theorem _root_.ArchInfraTopology.locallyCompactSpace_archGL :
    LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) := by
  haveI := t2Space_archMatrix' F
  haveI := locallyCompactSpace_archMatrix F
  exact Units.isClosedEmbedding_embedProduct.locallyCompactSpace

omit [NumberField F] in
theorem secondCountableTopology_placeGL (w : InfinitePlace F) :
    SecondCountableTopology (GL (Fin 2) w.Completion) := by
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion) :=
    inferInstanceAs (SecondCountableTopology (Fin 2 → Fin 2 → w.Completion))
  haveI : SecondCountableTopology (Matrix (Fin 2) (Fin 2) w.Completion)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isEmbedding_embedProduct.secondCountableTopology

omit [NumberField F] in
theorem secondCountableTopology_rowIsometrySubgroup₀ (w : InfinitePlace F) :
    SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) := by
  haveI := secondCountableTopology_placeGL F w
  exact Topology.IsEmbedding.subtypeVal.secondCountableTopology

theorem secondCountableTopology_piRowIsometrySubgroup₀ :
    SecondCountableTopology (Π w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) := by
  haveI : ∀ w : InfinitePlace F, SecondCountableTopology (rowIsometrySubgroup₀ w.Completion) :=
    secondCountableTopology_rowIsometrySubgroup₀ F
  infer_instance

abbrev archGLMeasurableSpace : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLMeasurableSpace

omit [NumberField F] in
theorem archGLBorelSpace : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  borelSpace_glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLBorelSpace

omit [NumberField F] in
theorem isTopologicalGroup_archGL : IsTopologicalGroup (GL (Fin 2) (InfiniteAdeleRing F)) := inferInstance

theorem sigmaFinite_archHaarK [(archHaarK F).IsHaarMeasure] : SigmaFinite (archHaarK F) := by
  haveI := secondCountableTopology_archGL F
  haveI := locallyCompactSpace_archGL F
  haveI : IsLocallyFiniteMeasure (archHaarK F) := isLocallyFiniteMeasure_of_isFiniteMeasureOnCompacts
  exact sigmaFinite_of_locallyFinite

end ArchInfraTopology

namespace ArchInfra

attribute [local instance] ArchInfraTopology.t2Space_archMatrix' ArchInfraTopology.locallyCompactSpace_archMatrix
  ArchInfraTopology.locallyCompactSpace_archGL ArchInfraTopology.isTopologicalGroup_archGL
  ArchInfraTopology.secondCountableTopology_archGL ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀

section Compact

variable (K : Type*) [NormedField K]

def rowIsoSet : Set (Matrix (Fin 2) (Fin 2) K) :=
  {m | m.det = 1} ∩ ({m | ‖m.det‖ = 1} ∩ ⋂ x : K, ⋂ y : K,
    {m | ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2})

theorem mem_rowIsoSet_iff (k : GL (Fin 2) K) :
    (k : Matrix (Fin 2) (Fin 2) K) ∈ rowIsoSet K ↔ k ∈ rowIsometrySubgroup₀ K := by
  simp only [rowIsoSet, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq,
    mem_rowIsometrySubgroup₀_iff, IsRowIsometry]

theorem continuous_entry (i j : Fin 2) :
    Continuous fun m : Matrix (Fin 2) (Fin 2) K => m i j :=
  continuous_id.matrix_elem i j

theorem isClosed_rowIsoSet : IsClosed (rowIsoSet K) := by
  have hdet : Continuous fun m : Matrix (Fin 2) (Fin 2) K => m.det := continuous_id.matrix_det
  refine (isClosed_eq hdet continuous_const).inter
    ((isClosed_eq hdet.norm continuous_const).inter ?_)
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  have h0 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 0 + y * m 1 0 :=
    (continuous_const.mul (continuous_entry K 0 0)).add
      (continuous_const.mul (continuous_entry K 1 0))
  have h1 : Continuous fun m : Matrix (Fin 2) (Fin 2) K => x * m 0 1 + y * m 1 1 :=
    (continuous_const.mul (continuous_entry K 0 1)).add
      (continuous_const.mul (continuous_entry K 1 1))
  exact (h0.norm.pow 2).add (h1.norm.pow 2)

theorem norm_entry_le_one {m : Matrix (Fin 2) (Fin 2) K} (hm : m ∈ rowIsoSet K) (i j : Fin 2) :
    ‖m i j‖ ≤ 1 := by
  have hrow : ∀ x y : K,
      ‖x * m 0 0 + y * m 1 0‖ ^ 2 + ‖x * m 0 1 + y * m 1 1‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
    have h := hm.2.2
    simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h
    exact h
  have hr0 : ‖m 0 0‖ ^ 2 + ‖m 0 1‖ ^ 2 = 1 := by
    have h := hrow 1 0
    simpa using h
  have hr1 : ‖m 1 0‖ ^ 2 + ‖m 1 1‖ ^ 2 = 1 := by
    have h := hrow 0 1
    simpa using h
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ^ 2 + b ^ 2 = 1 → a ≤ 1 := by
    intro a b ha hb h
    nlinarith [sq_nonneg b, sq_nonneg (a - 1)]
  fin_cases i <;> fin_cases j
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr0
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr0)
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) hr1
  · exact key _ _ (norm_nonneg _) (norm_nonneg _) (by rw [add_comm]; exact hr1)

theorem isCompact_rowIsoSet [ProperSpace K] : IsCompact (rowIsoSet K) := by
  have hbox : IsCompact ((Set.pi Set.univ fun _ : Fin 2 =>
      Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : K) 1) :
        Set (Matrix (Fin 2) (Fin 2) K)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine hbox.of_isClosed_subset (isClosed_rowIsoSet K) fun m hm => ?_
  exact Set.mem_univ_pi.mpr fun i => Set.mem_univ_pi.mpr fun j =>
    mem_closedBall_zero_iff.mpr (norm_entry_le_one K hm i j)

def toUnit (m : rowIsoSet K) : GL (Fin 2) K where
  val := m.1
  inv := m.1.adjugate
  val_inv := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.mul_adjugate, hd, one_smul]
  inv_val := by
    have hd : m.1.det = 1 := m.2.1
    rw [Matrix.adjugate_mul, hd, one_smul]

theorem continuous_toUnit : Continuous (toUnit K) :=
  Units.continuous_iff.mpr ⟨continuous_subtype_val, continuous_subtype_val.matrix_adjugate⟩

theorem range_toUnit :
    Set.range (toUnit K) = (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  ext k
  constructor
  · rintro ⟨m, rfl⟩
    exact (mem_rowIsoSet_iff K (toUnit K m)).mp m.2
  · intro hk
    exact ⟨⟨(k : Matrix (Fin 2) (Fin 2) K), (mem_rowIsoSet_iff K k).mpr hk⟩, Units.ext rfl⟩

theorem isCompact_rowIsometrySubgroup₀ [ProperSpace K] :
    IsCompact (rowIsometrySubgroup₀ K : Set (GL (Fin 2) K)) := by
  rw [← range_toUnit]
  haveI : CompactSpace (rowIsoSet K) := isCompact_iff_compactSpace.mp (isCompact_rowIsoSet K)
  exact isCompact_range (continuous_toUnit K)

end Compact

section Setting

variable (F : Type) [Field F] [NumberField F]

abbrev Kw (w : InfinitePlace F) : Type := rowIsometrySubgroup₀ w.Completion

abbrev Kprod : Type := Π w : InfinitePlace F, Kw F w

private scoped instance compactSpace_Kw (w : InfinitePlace F) : CompactSpace (Kw F w) :=
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
  isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup₀ w.Completion)

omit [NumberField F] in
theorem commute_archRowIsometryInclAt₀ {v w : InfinitePlace F} (hvw : v ≠ w) (a : Kw F v) (b : Kw F w) :
    Commute (archRowIsometryInclAt₀ F v a) (archRowIsometryInclAt₀ F w b) := by
  unfold archRowIsometryInclAt₀
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  exact commute_archGLIncl_of_ne F hvw _ _

def inclArch : Kprod F →* GL (Fin 2) (InfiniteAdeleRing F) :=
  MonoidHom.noncommPiCoprod (archRowIsometryInclAt₀ F)
    (fun _ _ hvw => commute_archRowIsometryInclAt₀ F hvw)

def inclAdelic : Kprod F →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (inclArch F)

variable {F}

theorem inclAdelic_apply (κ : Kprod F) : inclAdelic F κ = adelicArchGLIncl F (inclArch F κ) :=
  rfl

theorem inclArch_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclArch F (Pi.mulSingle w k) = archRowIsometryInclAt₀ F w k :=
  MonoidHom.noncommPiCoprod_mulSingle _ w k

theorem inclAdelic_mulSingle [DecidableEq (InfinitePlace F)] (w : InfinitePlace F) (k : Kw F w) :
    inclAdelic F (Pi.mulSingle w k) = rowIsometryInclAt₀ F w k :=
  congrArg (adelicArchGLIncl F) (inclArch_mulSingle w k)

theorem inclArch_entry (κ : Kprod F) (i j : Fin 2) (w : InfinitePlace F) :
    ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
      = ((κ w : GL (Fin 2) w.Completion) : Matrix (Fin 2) (Fin 2) w.Completion) i j := by
  classical
  let f : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    ((archMatrixPiEquiv F : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F) →*
        Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion).comp
      (Units.coeHom (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)))).comp (inclArch F)
  let g : Kprod F →* (Π v : InfinitePlace F, Matrix (Fin 2) (Fin 2) v.Completion) :=
    MonoidHom.pi fun v : InfinitePlace F =>
      ((Units.coeHom (Matrix (Fin 2) (Fin 2) v.Completion)).comp
        (rowIsometrySubgroup₀ v.Completion).subtype).comp
          (Pi.evalMonoidHom (fun u : InfinitePlace F => Kw F u) v)
  have hfg : f = g := by
    refine MonoidHom.pi_ext fun v k => ?_
    funext u
    show archMatrixPiEquiv F
        ((inclArch F (Pi.mulSingle v k) : GL (Fin 2) (InfiniteAdeleRing F)) :
          Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) u
      = ((Pi.mulSingle v k u : Kw F u) : GL (Fin 2) u.Completion)
    rw [inclArch_mulSingle]
    show archMatrixPiEquiv F (archMatrixUpdate F v ((k : GL (Fin 2) v.Completion) :
        Matrix (Fin 2) (Fin 2) v.Completion)) u = _
    rw [archMatrixPiEquiv_archMatrixUpdate]
    by_cases huv : u = v
    · subst huv
      simp
    · simp [Function.update_of_ne huv, Pi.mulSingle_eq_of_ne huv]
  have h : f κ = g κ := by rw [hfg]
  have hw := congrFun h w
  exact congrFun (congrFun hw i) j

theorem archComponent_inclArch (κ : Kprod F) (w : InfinitePlace F) :
    archComponent F w (inclArch F κ) = (κ w : GL (Fin 2) w.Completion) := by
  ext i j
  rw [AdelicLevel.archComponent_apply, inclArch_entry]

theorem continuous_inclArch : Continuous (inclArch F) := by
  have hval : Continuous fun κ : Kprod F =>
      ((inclArch F κ : GL (Fin 2) (InfiniteAdeleRing F)) :
        Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => ?_
    refine continuous_pi fun w => ?_
    simp only [inclArch_entry]
    exact (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply w))).matrix_elem
      i j
  refine Units.continuous_iff.mpr ⟨hval, ?_⟩
  simp only [← map_inv]
  exact hval.comp continuous_inv

theorem continuous_inclAdelic : Continuous (inclAdelic F) :=
  (AutomorphicForm.TestFnNearIdentity.continuous_adelicArchGLIncl F).comp continuous_inclArch

end Setting

section HaarKprod

variable (F : Type) [Field F]

abbrev KprodMeasurableSpace : MeasurableSpace (Kprod F) := borel (Kprod F)

attribute [local instance] KprodMeasurableSpace

theorem KprodBorelSpace : BorelSpace (Kprod F) := ⟨rfl⟩

attribute [local instance] KprodBorelSpace

def KprodTop : PositiveCompacts (Kprod F) where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by
    rw [interior_univ]
    exact ⟨1, Set.mem_univ 1⟩

def muK : Measure (Kprod F) := Measure.haarMeasure (KprodTop F)

theorem muK_univ : muK F Set.univ = 1 :=
  Measure.haarMeasure_self (K₀ := KprodTop F)

private scoped instance isProbabilityMeasure_muK : IsProbabilityMeasure (muK F) := ⟨muK_univ F⟩

private scoped instance isMulLeftInvariant_muK : (muK F).IsMulLeftInvariant := by
  unfold muK
  infer_instance

private scoped instance isHaarMeasure_muK : (muK F).IsHaarMeasure := by
  unfold muK
  infer_instance

theorem isMulRightInvariant_muK : (muK F).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have hg : Measurable fun κ : Kprod F => κ * g := (continuous_mul_const g).measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * g) (muK F)) := ⟨fun _ _ => measure_lt_top _ _⟩
  have hfac : (Measure.map (· * g) (muK F)).haarScalarFactor (muK F) = 1 := by
    have h := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F))
      (muK F) (s := Set.univ) isClosed_closure.isCompact
    rw [Measure.map_apply hg MeasurableSet.univ, Set.preimage_univ, muK_univ, ENNReal.smul_def, smul_eq_mul,
      mul_one] at h
    exact ENNReal.coe_eq_one.mp h.symm
  ext s _
  rw [Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * g) (muK F)) (muK F)
    isClosed_closure.isCompact, hfac, one_smul]

theorem integral_mul_right_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (κ * k) ∂muK F = ∫ κ, h κ ∂muK F :=
  haveI := isMulRightInvariant_muK F
  integral_mul_right_eq_self h k

theorem integral_mul_left_muK (h : Kprod F → ℂ) (k : Kprod F) :
    ∫ κ, h (k * κ) ∂muK F = ∫ κ, h κ ∂muK F :=
  integral_mul_left_eq_self h k

end HaarKprod

section Alpha4

variable (F : Type) [Field F] [NumberField F]

-- private re-derivation: the public copy is `ArchInfraTopology.archGLMeasurableSpace`
private abbrev archGLMeasurableSpace : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLMeasurableSpace

-- private re-derivation: the public copy is `ArchInfraTopology.archGLBorelSpace`
omit [NumberField F] in
private theorem archGLBorelSpace : BorelSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  borelSpace_glBorelOf (InfiniteAdeleRing F)

attribute [local instance] archGLBorelSpace

omit [NumberField F] in
theorem t2Space_archMatrix : T2Space (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  inferInstanceAs (T2Space (Fin 2 → Fin 2 → InfiniteAdeleRing F))

attribute [local instance] t2Space_archMatrix

-- private re-derivation: the public copy is `ArchInfraTopology.locallyCompactSpace_archGL`
private theorem _root_.ArchInfra.locallyCompactSpace_archGL :
    LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing F)) :=
  haveI : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → InfiniteAdeleRing F))
  Units.isClosedEmbedding_embedProduct.locallyCompactSpace

attribute [local instance] locallyCompactSpace_archGL

variable {F}

theorem exists_isCompact_preimage_mul_inclArch_eq (κ : Kprod F) :
    ∃ C : Set (GL (Fin 2) (InfiniteAdeleRing F)), IsCompact C ∧ (1 : GL (Fin 2) (InfiniteAdeleRing F)) ∈ interior C ∧
      (fun x => x * inclArch F κ) ⁻¹' C = C := by
  obtain ⟨C₀, hC₀c, hC₀n⟩ := exists_compact_mem_nhds (1 : GL (Fin 2) (InfiniteAdeleRing F))
  refine ⟨(fun p : GL (Fin 2) (InfiniteAdeleRing F) × Kprod F => p.1 * inclArch F p.2) '' (C₀ ×ˢ Set.univ),
    (hC₀c.prod isCompact_univ).image (continuous_fst.mul (continuous_inclArch.comp continuous_snd)), ?_, ?_⟩
  · have hsub : C₀ ⊆ (fun p : GL (Fin 2) (InfiniteAdeleRing F) × Kprod F => p.1 * inclArch F p.2) ''
        (C₀ ×ˢ Set.univ) :=
      fun x hx => ⟨(x, 1), ⟨hx, Set.mem_univ _⟩, by simp⟩
    exact interior_mono hsub (mem_interior_iff_mem_nhds.mpr hC₀n)
  · ext x
    constructor
    · rintro ⟨⟨c, κ'⟩, ⟨hc, -⟩, hx⟩
      refine ⟨(c, κ' * κ⁻¹), ⟨hc, Set.mem_univ _⟩, ?_⟩
      have hx' : c * inclArch F κ' = x * inclArch F κ := hx
      simp only [map_mul, map_inv, ← mul_assoc, hx', mul_inv_cancel_right]
    · rintro ⟨⟨c, κ'⟩, ⟨hc, -⟩, rfl⟩
      refine ⟨(c, κ' * κ), ⟨hc, Set.mem_univ _⟩, ?_⟩
      simp only [map_mul, mul_assoc]

theorem haarScalarFactor_map_mul_inclArch [(archHaarK F).IsHaarMeasure] (κ : Kprod F) :
    (Measure.map (· * inclArch F κ) (archHaarK F)).haarScalarFactor (archHaarK F) = 1 := by
  have hg : Measurable fun x : GL (Fin 2) (InfiniteAdeleRing F) => x * inclArch F κ :=
    (continuous_mul_const _).measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * inclArch F κ) (archHaarK F)) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hg hC.isClosed.measurableSet]
    exact ((Homeomorph.mulRight (inclArch F κ)).isCompact_preimage.mpr hC).measure_lt_top
  obtain ⟨C, hCc, hC1, hCstab⟩ := exists_isCompact_preimage_mul_inclArch_eq κ
  have h1 := Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure
    (Measure.map (· * inclArch F κ) (archHaarK F)) (archHaarK F) (s := C) (by rwa [hCc.isClosed.closure_eq])
  rw [Measure.map_apply hg hCc.isClosed.measurableSet, hCstab, ENNReal.smul_def, smul_eq_mul] at h1
  have hpos : archHaarK F C ≠ 0 := (Measure.measure_pos_of_nonempty_interior (archHaarK F) ⟨1, hC1⟩).ne'
  have hfin : archHaarK F C ≠ ⊤ := hCc.measure_lt_top.ne
  have h2 : (1 : ENNReal) * archHaarK F C =
      ((Measure.map (· * inclArch F κ) (archHaarK F)).haarScalarFactor (archHaarK F) : ENNReal) * archHaarK F C := by
    rw [one_mul]
    exact h1
  exact ENNReal.coe_eq_one.mp ((ENNReal.mul_left_inj hpos hfin).mp h2).symm

theorem integral_archHaarK_mul_inclArch [(archHaarK F).IsHaarMeasure] (κ : Kprod F)
    {h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ} (hc : Continuous h) (hcs : HasCompactSupport h) :
    ∫ x, h (x * inclArch F κ) ∂archHaarK F = ∫ x, h x ∂archHaarK F := by
  have hg : Measurable fun x : GL (Fin 2) (InfiniteAdeleRing F) => x * inclArch F κ :=
    (continuous_mul_const _).measurable
  haveI : IsFiniteMeasureOnCompacts (Measure.map (· * inclArch F κ) (archHaarK F)) := by
    refine ⟨fun C hC => ?_⟩
    rw [Measure.map_apply hg hC.isClosed.measurableSet]
    exact ((Homeomorph.mulRight (inclArch F κ)).isCompact_preimage.mpr hC).measure_lt_top
  have hfac := haarScalarFactor_map_mul_inclArch κ

  have hS : IsCompact (tsupport h) := hcs
  have hrestrict : (Measure.map (· * inclArch F κ) (archHaarK F)).restrict (tsupport h)
      = (archHaarK F).restrict (tsupport h) := by
    ext t ht
    rw [Measure.restrict_apply ht, Measure.restrict_apply ht,
      Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure (Measure.map (· * inclArch F κ) (archHaarK F))
        (archHaarK F) (hS.of_isClosed_subset isClosed_closure
          ((closure_mono Set.inter_subset_right).trans (isClosed_tsupport h).closure_eq.subset)),
      hfac, one_smul]
  have hzero : ∀ x, x ∉ tsupport h → h x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  calc ∫ x, h (x * inclArch F κ) ∂archHaarK F
      = ∫ x, h x ∂(Measure.map (· * inclArch F κ) (archHaarK F)) :=
        (integral_map hg.aemeasurable hc.aestronglyMeasurable).symm
    _ = ∫ x in tsupport h, h x ∂(Measure.map (· * inclArch F κ) (archHaarK F)) :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
    _ = ∫ x in tsupport h, h x ∂archHaarK F := by rw [hrestrict]
    _ = ∫ x, h x ∂archHaarK F := setIntegral_eq_integral_of_forall_compl_eq_zero hzero

end Alpha4

end ArchInfra

end
