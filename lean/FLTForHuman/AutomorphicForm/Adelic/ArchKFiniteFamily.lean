/-
  The archimedean- and level-invariance layers of the `K`-finite-family theorem.

  This is the adèlic instantiation half of
  `AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous`:
  the compact archimedean isometry group `Kinf` with its probability Haar measure
  `haarProb`, the continuous inclusion `incl` into `GL₂(𝔸_F)`, the level-congruence
  sets `congrSet`, the finite-adelic integrality layer `liftFin`/`finIncl`/
  `entryBall` over `IdealBall`, and the closing kernel on a small open `U`.

  The generic engine it consumes is `FLTForHuman/RepTheory/TranslateSpan.lean`; this
  module keeps the pin's own sub-namespaces `ArchimedeanIsometryGroup` and
  `LevelInvariance` under `AutomorphicForm.ArchKFiniteFamily`, and the pin's
  declarations stay `private` at the pin's names. The one public kernel lives in
  `AutomorphicForm.ArchKFiniteFamily.Engine`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean:492–789`,
  `:1084–1449` and the `solution` at `:1454` (pinned `aa2d8b3`). The pin's
  `p2m_reactivate` plumbing, its `P2M.Util` preludes and its `#print` diagnostics
  are not transcribed. Five `private scoped
  instance`s (`instCompactSpaceKinf`, `instMeasurableSpaceKinf`, `instBorelSpaceKinf`,
  `instIsProbabilityMeasureHaarProb`, `instIsMulLeftInvariantHaarProb`) stay in
  `ArchimedeanIsometryGroup`; the kernel activates them through
  `open ArchimedeanIsometryGroup in`.

  Drift, all statement-preserving: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`;
  `continuousOn_iff_continuous_restrict` → `continuousOn_iff_continuous_domRestrict`;
  `IsCompact.elim_finite_subfamily_closed` now takes `Disjoint s (⋂ i, t i)` rather
  than `s ∩ ⋂ i, t i = ∅` (adapted through `Set.disjoint_iff_inter_eq_empty` and
  `Set.disjoint_left`). The pin's
  `norm_entry_le_one` is kept in its local (unit / `IsRowIsometry`) form: the port's
  `ArchInfra.norm_entry_le_one` is stated for the *matrix* `rowIsoSet`, whose
  `m.det = 1` conjunct is not implied by `IsRowIsometry`'s `‖m.det‖ = 1`; the
  bridge through `ArchInfra.mem_rowIsoSet_iff` therefore does not typecheck, and the
  pair is a reported near-duplicate. The pin's `box` is transcribed privately and is
  **not** the port's `ArchEntryBall.detLocus` (a bare-type-only `port_advise` false
  match: `box = {m | ∀ i j w, ‖m i j w‖ ≤ 1}` against `detLocus = {m | ∀ w, m.det w ≠ 0}`).

  spec-pin: Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean
-/
import FLTForHuman.RepTheory.TranslateSpan
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Level
import Mathlib.Data.Set.Disjoint
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Sets.Compacts
import Mathlib.Tactic

set_option autoImplicit false

-- The pin's `haveI`/`letI` walls feed instance search (Haar measure, compactness,
-- finite-dimensionality); they are instances, so the style linter is suppressed.
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel
open AutomorphicForm AutomorphicForm.WindowedSiegel IsDedekindDomain
open Topology

namespace AutomorphicForm

namespace ArchKFiniteFamily

namespace ArchimedeanIsometryGroup

private theorem norm_entry_le_one {K : Type*} [NormedField K] {k : GL (Fin 2) K} (hk : IsRowIsometry k)
    (i j : Fin 2) : ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1 := by
  obtain ⟨-, hrow⟩ := hk
  have h0 := hrow 1 0
  have h1 := hrow 0 1
  simp only [one_mul, zero_mul, add_zero, zero_add, norm_one, norm_zero, one_pow] at h0 h1
  have n00 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 0 0)
  have n01 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 0 1)
  have n10 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 1 0)
  have n11 := norm_nonneg ((k : Matrix (Fin 2) (Fin 2) K) 1 1)
  fin_cases i <;> fin_cases j <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue] <;> nlinarith

private theorem isClosed_setOf_isRowIsometry {K : Type*} [NormedField K] :
    IsClosed {k : GL (Fin 2) K | IsRowIsometry k} := by
  have hc : ∀ i j : Fin 2, Continuous fun k : GL (Fin 2) K => (k : Matrix (Fin 2) (Fin 2) K) i j :=
    fun i j => Units.continuous_val.matrix_elem i j
  have hset : {k : GL (Fin 2) K | IsRowIsometry k}
      = {k : GL (Fin 2) K | ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1}
        ∩ ⋂ (x : K) (y : K), {k : GL (Fin 2) K |
            ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 0 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 0‖ ^ 2
              + ‖x * (k : Matrix (Fin 2) (Fin 2) K) 0 1 + y * (k : Matrix (Fin 2) (Fin 2) K) 1 1‖ ^ 2
              = ‖x‖ ^ 2 + ‖y‖ ^ 2} := by
    ext k
    simp only [IsRowIsometry, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [hset]
  refine (isClosed_eq Units.continuous_val.matrix_det.norm continuous_const).inter ?_
  refine isClosed_iInter fun x => isClosed_iInter fun y => isClosed_eq ?_ continuous_const
  exact (((continuous_const.mul (hc 0 0)).add (continuous_const.mul (hc 1 0))).norm.pow 2).add
    (((continuous_const.mul (hc 0 1)).add (continuous_const.mul (hc 1 1))).norm.pow 2)

private theorem isClosed_range_embedProduct {M : Type*} [Monoid M] [TopologicalSpace M] [ContinuousMul M]
    [T2Space M] : IsClosed (Set.range (Units.embedProduct M)) := by
  have hr : Set.range (Units.embedProduct M)
      = {p : M × Mᵐᵒᵖ | p.1 * p.2.unop = 1 ∧ p.2.unop * p.1 = 1} := by
    ext ⟨a, b⟩
    constructor
    · rintro ⟨u, hu⟩
      simp only [Units.embedProduct_apply, Prod.mk.injEq] at hu
      obtain ⟨rfl, rfl⟩ := hu
      simp
    · rintro ⟨h1, h2⟩
      exact ⟨⟨a, b.unop, h1, h2⟩, by simp [Units.embedProduct_apply]⟩
  rw [hr]
  exact (isClosed_eq (continuous_fst.mul (MulOpposite.continuous_unop.comp continuous_snd)) continuous_const).inter
    (isClosed_eq ((MulOpposite.continuous_unop.comp continuous_snd).mul continuous_fst) continuous_const)

variable (F : Type) [Field F]

private noncomputable def Kinf : Subgroup (GL (Fin 2) (InfiniteAdeleRing F)) :=
  ⨅ w : InfinitePlace F, (rowIsometrySubgroup w.Completion).comap (archComponent F w)

variable {F}

private theorem mem_Kinf_iff (k : GL (Fin 2) (InfiniteAdeleRing F)) :
    k ∈ Kinf F ↔ ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w k) := by
  simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_rowIsometrySubgroup_iff]

variable (F)

private theorem isClosed_Kinf : IsClosed (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F))) := by
  have hset : (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F)))
      = ⋂ w : InfinitePlace F, archComponent F w ⁻¹' {k | IsRowIsometry k} := by
    ext k
    simp only [SetLike.mem_coe, mem_Kinf_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hset]
  exact isClosed_iInter fun w => isClosed_setOf_isRowIsometry.preimage (continuous_archComponent F w)

private def box : Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :=
  {m | ∀ (i j : Fin 2) (w : InfinitePlace F), ‖m i j w‖ ≤ 1}

private theorem properSpace_completion_w (w : InfinitePlace F) : ProperSpace w.Completion :=
  NumberField.AdelicBox.properSpace_completion F w

private theorem isCompact_box : IsCompact (box F) := by
  haveI : ∀ w : InfinitePlace F, ProperSpace w.Completion := properSpace_completion_w F
  have hset : box F = Set.pi Set.univ (fun _ : Fin 2 => Set.pi Set.univ (fun _ : Fin 2 =>
      Set.pi Set.univ (fun w : InfinitePlace F => Metric.closedBall (0 : w.Completion) 1))) := by
    ext m
    constructor
    · intro h i _ j _ w _
      exact mem_closedBall_zero_iff.2 (h i j w)
    · intro h i j w
      exact mem_closedBall_zero_iff.1 (h i (Set.mem_univ i) j (Set.mem_univ j) w (Set.mem_univ w))
  rw [hset]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun w => isCompact_closedBall _ _

private theorem coe_mem_box {k : GL (Fin 2) (InfiniteAdeleRing F)} (hk : k ∈ Kinf F) :
    (k : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) ∈ box F :=
  fun i j w => norm_entry_le_one ((mem_Kinf_iff k).1 hk w) i j

private theorem isCompact_Kinf : IsCompact (Kinf F : Set (GL (Fin 2) (InfiniteAdeleRing F))) := by
  rw [Units.isInducing_embedProduct.isCompact_iff]
  refine ((isCompact_box F).prod ((isCompact_box F).image MulOpposite.continuous_op)).of_isClosed_subset ?_ ?_
  · exact (Topology.IsClosedEmbedding.mk Units.isEmbedding_embedProduct isClosed_range_embedProduct).isClosedMap _
      (isClosed_Kinf F)
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨coe_mem_box F hk, ⟨((k⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)),
      coe_mem_box F ((Kinf F).inv_mem hk), rfl⟩⟩

private scoped instance instCompactSpaceKinf : CompactSpace (Kinf F) :=
  isCompact_iff_compactSpace.mp (isCompact_Kinf F)

private noncomputable scoped instance instMeasurableSpaceKinf : MeasurableSpace (Kinf F) := borel _

private scoped instance instBorelSpaceKinf : BorelSpace (Kinf F) := ⟨rfl⟩

private noncomputable def haarProb : Measure (Kinf F) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (Kinf F))

private scoped instance instIsProbabilityMeasureHaarProb : IsProbabilityMeasure (haarProb F) :=
  ⟨by
    have h := Measure.haarMeasure_self (G := Kinf F) (K₀ := ⊤)
    simpa [haarProb] using h⟩

private scoped instance instIsMulLeftInvariantHaarProb : (haarProb F).IsMulLeftInvariant := by
  unfold haarProb
  infer_instance

end ArchimedeanIsometryGroup

namespace ArchimedeanIsometryGroup

variable (F : Type) [Field F] [NumberField F]

private noncomputable def incl : Kinf F →* AdelicGL2 (𝓞 F) F :=
  (adelicArchGLIncl F).comp (Kinf F).subtype

private theorem translatesFinite_archRowIsometrySubgroup (w : InfinitePlace F) (φ : AdelicGL2 (𝓞 F) F → ℂ)
    (hφ : IsArchKFiniteAt F w φ) :
    UniformRank.TranslatesFinite (archRowIsometrySubgroup F w : Set (AdelicGL2 (𝓞 F) F)) φ := by
  obtain ⟨s, hs⟩ := hφ
  exact Exists.intro s fun k hk => hs k hk

private theorem eq_of_forall_archComponent_eq {k k' : GL (Fin 2) (InfiniteAdeleRing F)}
    (h : ∀ w : InfinitePlace F, archComponent F w k = archComponent F w k') : k = k' := by
  have _ := ‹NumberField F›
  refine Units.ext ((archMatrixPiEquiv F).injective (funext fun w => Matrix.ext fun i j => ?_))
  exact congrArg (fun m : GL (Fin 2) w.Completion => (m : Matrix (Fin 2) (Fin 2) w.Completion) i j) (h w)

private theorem adelicArchGLInclAt_mul_comm {v w : InfinitePlace F} (hvw : v ≠ w) (a : GL (Fin 2) v.Completion)
    (b : GL (Fin 2) w.Completion) :
    adelicArchGLInclAt F v a * adelicArchGLInclAt F w b = adelicArchGLInclAt F w b * adelicArchGLInclAt F v a := by
  have hcomm : archGLIncl F v a * archGLIncl F w b = archGLIncl F w b * archGLIncl F v a := by
    refine eq_of_forall_archComponent_eq F fun u => ?_
    rw [map_mul, map_mul]
    by_cases huv : u = v
    · subst huv
      rw [archComponent_archGLIncl_self, archComponent_archGLIncl_of_ne F hvw, mul_one, one_mul]
    · rw [archComponent_archGLIncl_of_ne F huv]
      by_cases huw : u = w
      · subst huw
        rw [archComponent_archGLIncl_self, one_mul, mul_one]
      · rw [archComponent_archGLIncl_of_ne F huw]
  show adelicArchGLIncl F (archGLIncl F v a) * adelicArchGLIncl F (archGLIncl F w b) =
    adelicArchGLIncl F (archGLIncl F w b) * adelicArchGLIncl F (archGLIncl F v a)
  rw [← map_mul, ← map_mul, hcomm]

private theorem exists_mem_Kinf_eq_archGLIncl_mul (w : InfinitePlace F) {k : GL (Fin 2) (InfiniteAdeleRing F)}
    (hk : k ∈ Kinf F) :
    ∃ k' ∈ Kinf F, archComponent F w k' = 1 ∧ (∀ v : InfinitePlace F, v ≠ w → archComponent F v k' = archComponent F v k) ∧
      k = archGLIncl F w (archComponent F w k) * k' := by
  have _ := ‹NumberField F›
  have hrow : ∀ u : InfinitePlace F, archComponent F u k ∈ rowIsometrySubgroup u.Completion := by
    simpa only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap] using hk
  refine ⟨(archGLIncl F w (archComponent F w k))⁻¹ * k, ?_, ?_, ?_, (mul_inv_cancel_left _ _).symm⟩
  · simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro u
    rw [map_mul, map_inv]
    by_cases huw : u = w
    · subst huw
      rw [archComponent_archGLIncl_self, inv_mul_cancel]
      exact one_mem _
    · rw [archComponent_archGLIncl_of_ne F huw, inv_one, one_mul]
      exact hrow u
  · rw [map_mul, map_inv, archComponent_archGLIncl_self, inv_mul_cancel]
  · intro v hvw
    rw [map_mul, map_inv, archComponent_archGLIncl_of_ne F hvw, inv_one, one_mul]

private theorem translatesFinite_range_incl (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsArchKFinite F φ) :
    UniformRank.TranslatesFinite (Set.range (incl F)) φ := by
  classical
  have hmono : ∀ {Q Q' : Set (AdelicGL2 (𝓞 F) F)}, Q' ⊆ Q →
      UniformRank.TranslatesFinite Q φ → UniformRank.TranslatesFinite Q' φ :=
    fun hQ h => Exists.imp (fun _t ht k hk => ht k (hQ hk)) h
  let P : Finset (InfinitePlace F) → Set (AdelicGL2 (𝓞 F) F) := fun S =>
    {g | ∃ k ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ S → archComponent F v k = 1) ∧ g = adelicArchGLIncl F k}
  have hP : ∀ S : Finset (InfinitePlace F), UniformRank.TranslatesFinite (P S) φ := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · refine hmono (Q := {1}) ?_ (Exists.intro {φ} fun k hk => ?_)
      · rintro g ⟨k, -, hk1, rfl⟩
        have hk : k = 1 := eq_of_forall_archComponent_eq F fun v => by rw [hk1 v (by simp), map_one]
        rw [hk, map_one]
        exact Set.mem_singleton 1
      · rw [Set.mem_singleton_iff] at hk
        subst hk
        simp only [mul_one]
        exact Submodule.subset_span (by simp)
    · intro w S hw ih
      refine hmono ?_
        (UniformRank.translatesFinite_mul _ _ ?_ φ (translatesFinite_archRowIsometrySubgroup F w φ (hφ w)) ih)
      · rintro g ⟨k, hk, hk1, rfl⟩
        obtain ⟨k', hk'mem, hk'w, hk'v, hkeq⟩ := exists_mem_Kinf_eq_archGLIncl_mul F w hk
        have hrow : archComponent F w k ∈ rowIsometrySubgroup w.Completion := by
          have hk2 := hk
          simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap] at hk2
          exact hk2 w
        have h₁ : adelicArchGLIncl F (archGLIncl F w (archComponent F w k)) ∈
            (archRowIsometrySubgroup F w : Set (AdelicGL2 (𝓞 F) F)) :=
          Subgroup.mem_map_of_mem (adelicArchGLInclAt F w) hrow
        have h₂ : adelicArchGLIncl F k' ∈ P S := by
          show ∃ k₀ ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ S → archComponent F v k₀ = 1) ∧
            adelicArchGLIncl F k' = adelicArchGLIncl F k₀
          refine ⟨k', hk'mem, fun v hv => ?_, rfl⟩
          by_cases hvw : v = w
          · subst hvw
            exact hk'w
          · rw [hk'v v hvw]
            exact hk1 v fun h => hv (Finset.mem_of_mem_insert_of_ne h hvw)
        rw [hkeq, map_mul]
        exact Set.mul_mem_mul h₁ h₂
      · intro a ha g hg
        obtain ⟨k', -, hk'1, rfl⟩ := hg
        simp only [archRowIsometrySubgroup, SetLike.mem_coe, Subgroup.mem_map] at ha
        obtain ⟨a₀, -, rfl⟩ := ha
        have hcomm : archGLIncl F w a₀ * k' = k' * archGLIncl F w a₀ := by
          refine eq_of_forall_archComponent_eq F fun u => ?_
          rw [map_mul, map_mul]
          by_cases huw : u = w
          · subst huw
            rw [archComponent_archGLIncl_self, hk'1 u hw, mul_one, one_mul]
          · rw [archComponent_archGLIncl_of_ne F huw, one_mul, mul_one]
        show adelicArchGLIncl F (archGLIncl F w a₀) * adelicArchGLIncl F k' =
          adelicArchGLIncl F k' * adelicArchGLIncl F (archGLIncl F w a₀)
        rw [← map_mul, ← map_mul, hcomm]
  have hrange : Set.range (incl F) ⊆ P Finset.univ := by
    rintro g ⟨⟨k, hk⟩, rfl⟩
    show ∃ k₀ ∈ Kinf F, (∀ v : InfinitePlace F, v ∉ Finset.univ → archComponent F v k₀ = 1) ∧
      incl F ⟨k, hk⟩ = adelicArchGLIncl F k₀
    exact ⟨k, hk, fun v hv => (hv (Finset.mem_univ v)).elim, rfl⟩
  exact hmono hrange (hP Finset.univ)

private theorem continuous_incl : Continuous (incl F) :=
  Units.continuous_iff.mpr
    ⟨continuous_matrix fun i j => by
        show Continuous fun q : Kinf F =>
          ((⟨((q : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j⟩ : AdeleRing (𝓞 F) F))
        exact ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i j).prodMk continuous_const,
      continuous_matrix fun i j => by
        show Continuous fun q : Kinf F =>
          ((⟨(((q : GL (Fin 2) (InfiniteAdeleRing F))⁻¹ : GL (Fin 2) (InfiniteAdeleRing F)) :
              Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
            (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j⟩ : AdeleRing (𝓞 F) F))
        exact ((Units.continuous_coe_inv.comp continuous_subtype_val).matrix_elem i j).prodMk continuous_const⟩

private theorem incl_mul_comm_of_glArch_eq_one (q : Kinf F) (c : AdelicGL2 (𝓞 F) F)
    (hc : glArch (𝓞 F) F c = 1) : incl F q * c = c * incl F q := by
  have hA : glArch (𝓞 F) F (incl F q * c) = glArch (𝓞 F) F (c * incl F q) := by
    rw [map_mul, map_mul, hc, mul_one, one_mul]
  have hF : glFin (𝓞 F) F (incl F q * c) = glFin (𝓞 F) F (c * incl F q) := by
    have h1 : glFin (𝓞 F) F (incl F q) = 1 := glFin_adelicArchGLIncl F _
    rw [map_mul, map_mul, h1, mul_one, one_mul]
  have hA' : (glArch (𝓞 F) F (incl F q * c) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) =
      glArch (𝓞 F) F (c * incl F q) := by
    rw [hA]
  have hF' : (glFin (𝓞 F) F (incl F q * c) :
        Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) =
      glFin (𝓞 F) F (c * incl F q) := by
    rw [hF]
  ext i j
  exact Prod.ext (congrFun (congrFun hA' i) j) (congrFun (congrFun hF' i) j)

private theorem exists_exists_mem_exists_mem_eq_incl_mul_mul (T : Finset (AdelicGL2 (𝓞 F) F))
    (H : Set (AdelicGL2 (𝓞 F) F))
    (hT : ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
      ∃ g ∈ T, ∃ h ∈ H, k = g * h)
    (k : AdelicGL2 (𝓞 F) F) (hk₁ : glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F)
    (hk₂ : ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) :
    ∃ q : Kinf F, ∃ c ∈ T, ∃ h ∈ H, k = incl F q * c * h := by
  have hq : glArch (𝓞 F) F k ∈ Kinf F := by
    simp only [Kinf, Subgroup.mem_iInf, Subgroup.mem_comap, mem_rowIsometrySubgroup_iff]
    exact hk₂
  have h1 : glArch (𝓞 F) F ((adelicArchGLIncl F (glArch (𝓞 F) F k))⁻¹ * k) = 1 := by
    rw [map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]
  have h2 : glFin (𝓞 F) F ((adelicArchGLIncl F (glArch (𝓞 F) F k))⁻¹ * k) ∈ finiteIntegralGL2 (𝓞 F) F := by
    rw [map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hk₁
  obtain ⟨c, hc, h, hh, hk'⟩ := hT _ h1 h2
  refine ⟨⟨glArch (𝓞 F) F k, hq⟩, c, hc, h, hh, ?_⟩
  show k = adelicArchGLIncl F (glArch (𝓞 F) F k) * c * h
  rw [mul_assoc, ← hk', mul_inv_cancel_left]

end ArchimedeanIsometryGroup

namespace LevelInvariance

variable {G : Type*} [Mul G]

private def RightInvariantOn (S : Set G) (f : G → ℂ) : Prop :=
  ∀ g : G, ∀ k ∈ S, f (g * k) = f g

private theorem exists_isOpen_subset_exists_forall_rightInvariantOn (S : ℕ → Set G) (u : ℂ → G → ℂ)
    (hc : ∀ g, Continuous fun s => u s g) (hfix : ∀ s, ∃ n, RightInvariantOn (S n) (u s))
    (U₀ : Set ℂ) (hU₀ : IsOpen U₀) (hne : U₀.Nonempty) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧ U ⊆ U₀ ∧ ∃ n, ∀ s ∈ U, RightInvariantOn (S n) (u s) := by
  classical

  set C : ℕ → Set ℂ := fun n => ⋂ g, ⋂ k ∈ S n, {s : ℂ | u s (g * k) = u s g} with hC
  have hmemC : ∀ n s, s ∈ C n ↔ RightInvariantOn (S n) (u s) := by
    intro n s
    simp only [hC, Set.mem_iInter, Set.mem_ofPred_eq, RightInvariantOn]
  have hCclosed : ∀ n, IsClosed (C n) := by
    intro n
    refine isClosed_iInter fun g => isClosed_iInter fun k => isClosed_iInter fun _ => ?_
    exact isClosed_eq (hc (g * k)) (hc g)

  have hFclosed : ∀ n, IsClosed (C n ∪ U₀ᶜ) := fun n => (hCclosed n).union hU₀.isClosed_compl
  have hcover : ⋃ n, (C n ∪ U₀ᶜ) = Set.univ := by
    refine Set.eq_univ_iff_forall.2 fun s => Set.mem_iUnion.2 ?_
    by_cases hs : s ∈ U₀
    · obtain ⟨n, hn⟩ := hfix s
      exact ⟨n, Or.inl ((hmemC n s).2 hn)⟩
    · exact ⟨0, Or.inr hs⟩

  obtain ⟨x, hx, hxU₀⟩ :=
    (dense_iUnion_interior_of_closed hFclosed hcover).exists_mem_open hU₀ hne
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.1 hx
  refine ⟨U₀ ∩ interior (C n ∪ U₀ᶜ), hU₀.inter isOpen_interior, ⟨x, hxU₀, hxn⟩,
    Set.inter_subset_left, n, ?_⟩
  intro s hs
  rcases interior_subset hs.2 with hsC | hsU₀
  · exact (hmemC n s).1 hsC
  · exact absurd hs.1 hsU₀

variable (F : Type) [Field F] [NumberField F]

private def congrSet (n : ℕ) : Set (AdelicGL2 (𝓞 F) F) :=
  {u | glArch (𝓞 F) F u = 1 ∧ ∀ i j : Fin 2,
    (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}) ∧
    (((glFin (𝓞 F) F u)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
      idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})}

private theorem idealBound_span_singleton {r : 𝓞 F} (hr : r ≠ 0) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    idealBound (𝓞 F) (Ideal.span {r}) v = v.intValuation r := by
  rw [idealBound_of_ne_bot (by rwa [Ne, Ideal.span_singleton_eq_bot]) v, v.intValuation_if_neg hr]

private theorem idealBall_span_mul_subset {a b : 𝓞 F} (ha : a ≠ 0) (hb : b ≠ 0) :
    idealBall (𝓞 F) F (Ideal.span {a * b}) ⊆ idealBall (𝓞 F) F (Ideal.span {a}) := by
  intro x hx v
  have h := hx v
  rw [idealBound_span_singleton F (mul_ne_zero ha hb)] at h
  rw [idealBound_span_singleton F ha]
  refine h.trans ?_
  rw [map_mul]
  exact mul_le_of_le_one_right' (v.intValuation_le_one b)

private theorem eq_zero_of_forall_mem_idealBall (x : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)
    (hx : ∀ m : ℕ, m ≠ 0 → x ∈ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) : x = 0 := by
  refine IsDedekindDomain.FiniteAdeleRing.ext F fun v => ?_
  rw [coe_zero_apply]
  by_contra h0
  have hv0 : Valued.v (x v) ≠ 0 := (Valuation.ne_zero_iff _).mpr h0
  set e : ℤ := WithZero.log (Valued.v (x v)) with he_def
  have he : Valued.v (x v) = WithZero.exp e := (WithZero.exp_log hv0).symm
  set M : ℕ := Ideal.absNorm v.asIdeal ^ (e.natAbs + 1) with hM_def
  have hM0 : M ≠ 0 :=
    pow_ne_zero _ (fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h))
  have hmem : ((M : ℕ) : 𝓞 F) ∈ v.asIdeal ^ (e.natAbs + 1) := by
    rw [hM_def, Nat.cast_pow]
    exact Ideal.pow_mem_pow (Ideal.absNorm_mem _) _
  have h1 : Valued.v (x v) ≤ v.intValuation ((M : ℕ) : 𝓞 F) := by
    rw [← idealBound_span_singleton F (Nat.cast_ne_zero.mpr hM0) v]
    exact hx M hM0 v
  have h2 : v.intValuation ((M : ℕ) : 𝓞 F) ≤ WithZero.exp (-((e.natAbs + 1 : ℕ) : ℤ)) :=
    (v.intValuation_le_pow_iff_mem _ _).mpr hmem
  have h3 := (he ▸ h1).trans h2
  rw [WithZero.exp_le_exp] at h3
  omega

private theorem exists_idealBall_subset {O : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)} (hO : IsOpen O)
    (h0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ O) :
    ∃ m : ℕ, m ≠ 0 ∧ idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)}) ⊆ O := by
  have hS := isCompact_integralFiniteAdeles (𝓞 F) F
  let t : ℕ → Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) := fun k =>
    idealBall (𝓞 F) F (Ideal.span {((k + 1 : ℕ) : 𝓞 F)}) ∩ Oᶜ
  have htc : ∀ k, IsClosed (t k) := fun k =>
    (isClosed_idealBall (𝓞 F) F _).inter hO.isClosed_compl
  have hst : Disjoint (integralFiniteAdeles (𝓞 F) F) (⋂ k, t k) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    have hxI := Set.mem_iInter.mp hx.2
    have hx0 : x = 0 := by
      refine eq_zero_of_forall_mem_idealBall F x fun m hm => ?_
      have h := (hxI (m - 1)).1
      rwa [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm)] at h
    exact (hxI 0).2 (hx0 ▸ h0)
  obtain ⟨u, hu⟩ := hS.elim_finite_subfamily_closed t htc hst
  refine ⟨∏ k ∈ u, (k + 1), Finset.prod_ne_zero_iff.mpr fun k _ => Nat.succ_ne_zero k,
    fun x hx => ?_⟩
  by_contra hxO
  have hxall : x ∈ integralFiniteAdeles (𝓞 F) F ∩ ⋂ k ∈ u, t k := by
    refine ⟨idealBall_subset_integralFiniteAdeles _ hx, Set.mem_iInter₂.mpr fun k hk => ⟨?_, hxO⟩⟩
    have hsplit : (∏ i ∈ u, (i + 1) : ℕ) = (k + 1) * ∏ i ∈ u.erase k, (i + 1) :=
      (Finset.mul_prod_erase u (fun i => i + 1) hk).symm
    rw [hsplit, Nat.cast_mul] at hx
    exact idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero k))
      (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun i _ => Nat.succ_ne_zero i)) hx
  exact (Set.disjoint_left.mp hu hxall.1) hxall.2

private noncomputable def liftFin (X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F) :=
  Matrix.of fun i j => ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, X i j)

private theorem one_apply_eq (i j : Fin 2) :
    (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j =
      ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) := by
  rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

private theorem coe_eq_liftFin {u : AdelicGL2 (𝓞 F) F} (hu : glArch (𝓞 F) F u = 1) :
    (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) =
      liftFin F (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) := by
  refine Matrix.ext fun i j => Prod.ext ?_ ?_
  · show ((u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).1 =
      (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j
    rw [← glArch_apply, hu, Units.val_one]
  · rfl

private theorem exists_forall_liftFin_mem {W : Set (Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))}
    (hW : IsOpen W) (h1 : (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ W) :
    ∃ m : ℕ, m ≠ 0 ∧ ∀ X : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      (∀ i j, X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈
        idealBall (𝓞 F) F (Ideal.span {(m : 𝓞 F)})) → liftFin F X ∈ W := by
  obtain ⟨r, hr, hrW⟩ := isOpen_pi_iff'.mp hW _ h1
  have hc : ∀ i, ∃ c : Fin 2 → Set (AdeleRing (𝓞 F) F),
      (∀ j, IsOpen (c j) ∧ (1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j ∈ c j) ∧
        Set.univ.pi c ⊆ r i := fun i => isOpen_pi_iff'.mp (hr i).1 _ (hr i).2
  choose c hc hcr using hc
  have hAB : ∀ i j, ∃ A : Set (InfiniteAdeleRing F), ∃ B : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F),
      IsOpen A ∧ IsOpen B ∧ (1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j ∈ A ∧
        (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j ∈ B ∧ A ×ˢ B ⊆ c i j := by
    intro i j
    have h := (hc i j).2
    rw [one_apply_eq] at h
    exact isOpen_prod_iff.mp (hc i j).1 _ _ h
  choose A B hA hB hA1 hB1 hABc using hAB
  let T : Set (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) :=
    ⋂ i, ⋂ j, (fun y => (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + y) ⁻¹' B i j
  have hT : IsOpen T :=
    isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      (hB i j).preimage (continuous_const.add continuous_id)
  have hT0 : (0 : IsDedekindDomain.FiniteAdeleRing (𝓞 F) F) ∈ T := by
    refine Set.mem_iInter.mpr fun i => Set.mem_iInter.mpr fun j => ?_
    show (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j + 0 ∈ B i j
    rw [add_zero]
    exact hB1 i j
  obtain ⟨m, hm, hmT⟩ := exists_idealBall_subset F hT hT0
  refine ⟨m, hm, fun X hX => hrW (Set.mem_univ_pi.mpr fun i => hcr i (Set.mem_univ_pi.mpr fun j => ?_))⟩
  refine hABc i j (Set.mk_mem_prod (hA1 i j) ?_)
  have h := Set.mem_iInter.mp (Set.mem_iInter.mp (hmT (hX i j)) i) j
  have h' : (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j +
      (X i j - (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ∈ B i j := h
  rwa [add_sub_cancel] at h'

private theorem exists_congrSet_subset {V : Set (AdelicGL2 (𝓞 F) F)} (hV : IsOpen V)
    (h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V) : ∃ n : ℕ, congrSet F n ⊆ V := by
  obtain ⟨O, hO, hOV⟩ := Units.isInducing_embedProduct.isOpen_iff.mp hV
  have h1O : Units.embedProduct _ (1 : AdelicGL2 (𝓞 F) F) ∈ O := by
    rw [← Set.mem_preimage, hOV]
    exact h1
  rw [map_one, Prod.one_eq_mk] at h1O
  obtain ⟨O₁, O₂, hO₁, hO₂, h1O₁, h1O₂, hprod⟩ := isOpen_prod_iff.mp hO _ _ h1O
  obtain ⟨m₁, hm₁, hW₁⟩ := exists_forall_liftFin_mem F hO₁ h1O₁
  obtain ⟨m₂, hm₂, hW₂⟩ := exists_forall_liftFin_mem F (hO₂.preimage MulOpposite.continuous_op)
    (by rw [Set.mem_preimage, MulOpposite.op_one]; exact h1O₂)
  refine ⟨m₁ * m₂ - 1, fun u hu => ?_⟩
  have hn : m₁ * m₂ - 1 + 1 = m₁ * m₂ :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hm₁ hm₂))
  obtain ⟨harch, hent⟩ := hu
  simp only [hn, Nat.cast_mul] at hent
  have harch' : glArch (𝓞 F) F u⁻¹ = 1 := by rw [map_inv, harch, inv_one]
  have hval : (u : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) ∈ O₁ := by
    rw [coe_eq_liftFin F harch]
    exact hW₁ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₁)
      (Nat.cast_ne_zero.mpr hm₂) (hent i j).1
  have hinv : MulOpposite.op ((u⁻¹ : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2)
      (AdeleRing (𝓞 F) F)) ∈ O₂ := by
    have h := hW₂ _ fun i j => idealBall_span_mul_subset F (Nat.cast_ne_zero.mpr hm₂)
      (Nat.cast_ne_zero.mpr hm₁) (mul_comm (m₁ : 𝓞 F) (m₂ : 𝓞 F) ▸ (hent i j).2)
    rw [Set.mem_preimage, ← map_inv, ← coe_eq_liftFin F harch'] at h
    exact h
  rw [← hOV, Set.mem_preimage, Units.embedProduct_apply]
  exact hprod (Set.mk_mem_prod hval hinv)

private theorem exists_rightInvariantOn_congrSet_of_isKfSmooth (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsKfSmooth F f) : ∃ n : ℕ, RightInvariantOn (congrSet F n) f := by
  have hopen : IsOpen ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
      (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
        Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := hf
  obtain ⟨V, hV, hVeq⟩ := isOpen_induced_iff.mp hopen
  have h1 : (1 : AdelicGL2 (𝓞 F) F) ∈ V := by
    have h : (1 : ↥(finiteAdelicGL2Subgroup F)) ∈ Subtype.val ⁻¹' V := by
      rw [hVeq]; exact Subgroup.one_mem _
    exact h
  obtain ⟨n, hn⟩ := exists_congrSet_subset F hV h1
  refine ⟨n, fun g k hk => ?_⟩
  have hkK : k ∈ finiteAdelicGL2Subgroup F := (mem_finiteAdelicGL2Subgroup_iff F k).mpr hk.1
  have hst : (⟨k, hkK⟩ : ↥(finiteAdelicGL2Subgroup F)) ∈
      ((MulAction.stabilizer (↥(finiteAdelicGL2Subgroup F))
        (FLT.SmoothVectors.RightTranslationFn.mk f :
        FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ) :
          Subgroup (↥(finiteAdelicGL2Subgroup F))) : Set (↥(finiteAdelicGL2Subgroup F))) := by
    rw [← hVeq]; exact hn hk
  have heq := MulAction.mem_stabilizer_iff.mp (SetLike.mem_coe.mp hst)
  exact congrArg (fun φ => FLT.SmoothVectors.RightTranslationFn.toFun φ g) heq

private noncomputable def finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : AdelicGL2 (𝓞 F) F where
  val := Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j)
  inv := Matrix.of fun i j =>
    ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
      ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j)
  val_inv := by
    apply (adelicMatrixProdEquiv F).injective
    rw [map_mul, map_one]
    have h1 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    have h2 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    rw [h1, h2]
    exact Prod.ext (one_mul _) (Units.mul_inv x)
  inv_val := by
    apply (adelicMatrixProdEquiv F).injective
    rw [map_mul, map_one]
    have h1 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, (x : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    have h2 : adelicMatrixProdEquiv F (Matrix.of fun i j =>
        ((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j,
          ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j))
        = (1, ((x⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
      Prod.ext (by ext i j; rfl) (by ext i j; rfl)
    rw [h1, h2]
    exact Prod.ext (one_mul _) (Units.inv_mul x)

private theorem continuous_finIncl : Continuous (finIncl F) :=
  Units.continuous_iff.mpr
    ⟨continuous_matrix fun i j => continuous_const.prodMk (Units.continuous_val.matrix_elem i j),
      continuous_matrix fun i j => continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)⟩

private theorem glArch_finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glArch (𝓞 F) F (finIncl F x) = 1 := by
  ext i j
  rfl

private theorem glFin_finIncl (x : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
    glFin (𝓞 F) F (finIncl F x) = x := by
  ext i j
  rfl

private theorem eq_finIncl_glFin (k : AdelicGL2 (𝓞 F) F) (hk : glArch (𝓞 F) F k = 1) :
    k = finIncl F (glFin (𝓞 F) F k) := by
  refine Units.ext (Matrix.ext fun i j => Prod.ext ?_ rfl)
  exact congrArg (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
    (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) hk

private def entryBall (n : ℕ) : Set (AdelicGL2 (𝓞 F) F) :=
  ⋂ i : Fin 2, ⋂ j : Fin 2,
    ((fun u : AdelicGL2 (𝓞 F) F =>
        (glFin (𝓞 F) F u : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
        idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)})) ∩
    ((fun u : AdelicGL2 (𝓞 F) F =>
        (((glFin (𝓞 F) F u)⁻¹ : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) :
            Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j -
          (1 : Matrix (Fin 2) (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)) i j) ⁻¹'
        idealBall (𝓞 F) F (Ideal.span {((n + 1 : ℕ) : 𝓞 F)}))

private theorem isOpen_entryBall (n : ℕ) : IsOpen (entryBall F n) := by
  have hN : (Ideal.span {((n + 1 : ℕ) : 𝓞 F)} : Ideal (𝓞 F)) ≠ ⊥ :=
    Ideal.span_singleton_eq_bot.not.mpr (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n))
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => IsOpen.inter ?_ ?_
  · exact (isOpen_idealBall (𝓞 F) F hN).preimage
      (((Units.continuous_val.comp (continuous_glFin (𝓞 F) F)).matrix_elem i j).sub continuous_const)
  · exact (isOpen_idealBall (𝓞 F) F hN).preimage
      (((Units.continuous_coe_inv.comp (continuous_glFin (𝓞 F) F)).matrix_elem i j).sub continuous_const)

private theorem one_mem_entryBall (n : ℕ) : (1 : AdelicGL2 (𝓞 F) F) ∈ entryBall F n := by
  refine Set.mem_iInter₂.mpr fun i j => ⟨?_, ?_⟩
  · rw [Set.mem_preimage, map_one, Units.val_one, sub_self]
    exact zero_mem_idealBall _
  · rw [Set.mem_preimage, map_one, inv_one, Units.val_one, sub_self]
    exact zero_mem_idealBall _

private theorem mem_congrSet_of_mem_entryBall {n : ℕ} {u : AdelicGL2 (𝓞 F) F}
    (harch : glArch (𝓞 F) F u = 1) (hu : u ∈ entryBall F n) : u ∈ congrSet F n :=
  ⟨harch, fun i j => Set.mem_iInter₂.mp hu i j⟩

private theorem exists_finset_eq_mul_mem_closure_congrSet (n : ℕ) :
    ∃ T : Finset (AdelicGL2 (𝓞 F) F),
      (∀ g ∈ T, glArch (𝓞 F) F g = 1 ∧ glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F) ∧
      ∀ k : AdelicGL2 (𝓞 F) F, glArch (𝓞 F) F k = 1 → glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        ∃ g ∈ T, ∃ h ∈ Subgroup.closure (congrSet F n), k = g * h := by

  have hC : IsCompact (finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)))) :=
    (isCompact_finiteLevelZero (𝓞 F) F ⊤).image (continuous_finIncl F)

  have hU : ∀ g ∈ finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))),
      (fun k : AdelicGL2 (𝓞 F) F => g⁻¹ * k) ⁻¹' entryBall F n ∈ nhds g := by
    intro g _
    refine IsOpen.mem_nhds ((isOpen_entryBall F n).preimage (continuous_const.mul continuous_id)) ?_
    show g⁻¹ * g ∈ entryBall F n
    rw [inv_mul_cancel]
    exact one_mem_entryBall F n
  obtain ⟨T, hTC, hsub⟩ := hC.elim_nhds_subcover (fun g => (fun k : AdelicGL2 (𝓞 F) F => g⁻¹ * k) ⁻¹' entryBall F n) hU
  have hT : ∀ g ∈ T, glArch (𝓞 F) F g = 1 ∧ glFin (𝓞 F) F g ∈ finiteIntegralGL2 (𝓞 F) F := by
    intro g hg
    obtain ⟨x, hx, rfl⟩ := hTC g hg
    exact ⟨glArch_finIncl F x, by rw [glFin_finIncl]; exact hx⟩
  refine ⟨T, hT, fun k harch hint => ?_⟩
  have hkC : k ∈ finIncl F '' (finiteIntegralGL2 (𝓞 F) F : Set (GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F))) :=
    ⟨glFin (𝓞 F) F k, hint, (eq_finIncl_glFin F k harch).symm⟩
  obtain ⟨g, hgT, hkg⟩ := Set.mem_iUnion₂.mp (hsub hkC)
  refine ⟨g, hgT, g⁻¹ * k, Subgroup.subset_closure (mem_congrSet_of_mem_entryBall F ?_ hkg),
    (mul_inv_cancel_left g k).symm⟩
  rw [map_mul, map_inv, (hT g hgT).1, harch, inv_one, one_mul]

private theorem forall_mem_closure_congrSet_apply_mul_eq (n : ℕ) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : RightInvariantOn (congrSet F n) f) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∀ h ∈ Subgroup.closure (congrSet F n), f (g * h) = f g := by
  intro g h hh
  induction hh using Subgroup.closure_induction generalizing g with
  | mem x hx => exact hf g x hx
  | one => rw [mul_one]
  | mul x y _ _ ihx ihy => rw [← mul_assoc, ihy, ihx]
  | inv x _ ihx =>
    have h := ihx (g * x⁻¹)
    rw [inv_mul_cancel_right] at h
    exact h.symm

end LevelInvariance

namespace Engine

open ArchimedeanIsometryGroup in
theorem exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : ∀ s, IsArchKFinite F (φ s))
    (_hφf : ∀ s, IsKfSmooth F (φ s))
    (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∃ (n : ℕ) (σ : Fin n → ℂ), ∀ s ∈ U, ∃ c : Fin n → ℂ, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s k = ∑ i, c i * φ (σ i) k := by
  classical

  obtain ⟨U₁, hU₁, hne₁, -, n, hinv₁⟩ :=
    LevelInvariance.exists_isOpen_subset_exists_forall_rightInvariantOn (LevelInvariance.congrSet F) φ
      (fun g => _hφjc.comp (continuous_id.prodMk continuous_const))
      (fun s => LevelInvariance.exists_rightInvariantOn_congrSet_of_isKfSmooth F (φ s) (_hφf s))
      Set.univ isOpen_univ Set.univ_nonempty

  obtain ⟨T, hT₁, hT₂⟩ := LevelInvariance.exists_finset_eq_mul_mem_closure_congrSet F n

  obtain ⟨U₂, hU₂, hne₂, hU₂₁, r, κ₀, x, hκ₀, hdet₀, hspan₀⟩ :=
    UniformRank.exists_isOpen_subset_forall_det_ne_zero_and_mem_span (Set.range (incl F)) φ
      (fun s => translatesFinite_range_incl F (φ s) (_hφK s))
      (fun g => _hφjc.comp (continuous_id.prodMk continuous_const)) U₁ hU₁ hne₁

  have hκ₀' : ∀ j, ∃ q : Kinf F, incl F q = κ₀ j := fun j => Set.mem_range.1 (hκ₀ j)
  choose κ hκ using hκ₀'
  have hdet : ∀ s ∈ U₂, (Matrix.of fun i j => φ s (x i * incl F (κ j))).det ≠ 0 := by
    intro s hs
    simpa only [hκ] using hdet₀ s hs
  have hspan : ∀ s ∈ U₂, ∀ q : Kinf F, (fun g => φ s (g * incl F q)) ∈
      Submodule.span ℂ (Set.range fun j => fun g => φ s (g * incl F (κ j))) := by
    intro s hs q
    simpa only [hκ] using hspan₀ s hs (incl F q) ⟨q, rfl⟩

  obtain ⟨ρ, hρ₁, hρ₂, hρ₃, hlaw⟩ :=
    TranslationCoordinates.exists_forall_one_and_mul_and_continuousOn_and_eq_sum (incl F) (continuous_incl F) φ
      _hφjc U₂ r κ x hdet hspan

  obtain ⟨s₀, hs₀⟩ := hne₂
  obtain ⟨U₃, hU₃, hs₀₃, hU₃₂, hT⟩ :=
    AveragedIntertwiner.exists_isOpen_forall_exists_isUnit_mul_eq_mul (haarProb F) r U₂ hU₂ ρ hρ₁ hρ₂ hρ₃ s₀ hs₀

  have hcomm : ∀ (q : Kinf F), ∀ c ∈ T, incl F q * c = c * incl F q :=
    fun q c hc => incl_mul_comm_of_glArch_eq_one F q c (hT₁ c hc).1
  have hV := SliceCoefficients.slices_mem_pi_coeffSpan (incl F) T hcomm φ κ ρ (ρ s₀) U₂ U₃ hU₃₂ hspan hlaw hT

  have hinv : ∀ s ∈ U₃, ∀ (g : AdelicGL2 (𝓞 F) F),
      ∀ h ∈ ((Subgroup.closure (LevelInvariance.congrSet F n) : Subgroup (AdelicGL2 (𝓞 F) F)) :
        Set (AdelicGL2 (𝓞 F) F)), φ s (g * h) = φ s g :=
    fun s hs g h hh =>
      LevelInvariance.forall_mem_closure_congrSet_apply_mul_eq F n (φ s) (hinv₁ s (hU₂₁ (hU₃₂ hs))) g h hh
  have hcover : ∀ k ∈ {k : AdelicGL2 (𝓞 F) F | glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))},
      ∃ q : Kinf F, ∃ c ∈ T, ∃ h ∈ ((Subgroup.closure (LevelInvariance.congrSet F n) :
        Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)), k = incl F q * c * h :=
    fun k hk => exists_exists_mem_exists_mem_eq_incl_mul_mul F T _ hT₂ k hk.1 hk.2
  haveI : FiniteDimensional ℂ (CoefficientSpan.coeffSpan (ρ s₀)) := CoefficientSpan.finiteDimensional_coeffSpan (ρ s₀)
  haveI : FiniteDimensional ℂ (Submodule.pi Set.univ fun _ : T => CoefficientSpan.coeffSpan (ρ s₀)) :=
    SliceSpan.finiteDimensional_pi_const _
  obtain ⟨m, σ, -, hσ⟩ :=
    SliceSpan.exists_forall_mem_exists_forall_eq_sum (⇑(incl F)) T _ _ hcover φ U₃ hinv
      (Submodule.pi Set.univ fun _ : T => CoefficientSpan.coeffSpan (ρ s₀)) hV
  exact ⟨U₃, hU₃, ⟨s₀, hs₀₃⟩, m, σ, fun s hs => (hσ s hs).imp fun a ha k hk₁ hk₂ => ha k ⟨hk₁, hk₂⟩⟩

end Engine

end ArchKFiniteFamily

end AutomorphicForm

end
