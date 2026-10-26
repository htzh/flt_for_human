/- 
  The adèlic instantiation of the archimedean approximate identity (movement `Q5a`).

  This is the assembly behind the headline
  `AutomorphicForm.exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule`:
  the stable submodule `rtStabilizer`/`rt_noncommPiCoprod_mem`, the archimedean entry
  map `Ent`/`twoSided` and its continuity, the smooth double-convolution witness
  `exists_contDiff_dconvWith`, and `exists_tendsto_integral_of_mem_archCutSubmodule`. The façade
  `AutomorphicForm/Adelic/ArchApproxIdentity.lean` carries the headline alone and
  proves it from `exists_tendsto_integral_of_mem_archCutSubmodule`.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean:2861–3131`
  (pinned `aa2d8b3`), the `Instantiate` section. Substitutions: the pin's private
  `ArchInfraTopology.locallyCompactSpace_archGL` is the port's public
  `ArchInfraTopology.locallyCompactSpace_archGL` (statement-identical); the pin's private
  `ArchEntryBall.continuous_archEntries` is re-derived locally as `private` from the port's
  public `ArchEntryBall.continuous_matrixEntries`, exactly as the pin does. The pin's
  `p2m_reactivate` lines are not transcribed.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isArchTestFactor_isArchFactorBiFinite_tendsto_integral_of_mem_archCutSubmodule.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.EntryBall
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.RepTheory.ConvolutionLimit
import FLTForHuman.RepTheory.TypeReproducer
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel AutomorphicForm MeasureTheory Filter Topology

open scoped ArchInfra

namespace ArchEntryBall

variable (F : Type) [Field F] [NumberField F]

-- Local `private` re-derivation of the pin's `continuous_archEntries` (`:570`), which is
-- `private` in `EntryBall`; the port's public `ArchEntryBall.continuous_matrixEntries`
-- carries the substance and no promotion is wanted.
omit [NumberField F] in
private theorem continuous_archEntries : Continuous (archEntries F) :=
  (continuous_matrixEntries F).comp Units.continuous_val

end ArchEntryBall

namespace ArchApproxIdentity

section Instantiate

section Stable

variable {G : Type*} [Group G] {Pl : Type*} [Fintype Pl] {K : Pl → Type*} [∀ w, Group (K w)]

def rtStabilizer (E' : Submodule ℂ (G → ℂ)) : Submonoid G where
  carrier := {g | ∀ v ∈ E', (fun x => v (x * g)) ∈ E'}
  one_mem' v hv := by simpa only [mul_one] using hv
  mul_mem' {g} {h} hg hh v hv := by
    have h1 : (fun x => v (x * (g * h))) = fun x => (fun y => v (y * h)) (x * g) := by
      funext x
      simp only [mul_assoc]
    rw [h1]
    exact hg _ (hh v hv)

theorem mem_rtStabilizer {E' : Submodule ℂ (G → ℂ)} {g : G} :
    g ∈ rtStabilizer E' ↔ ∀ v ∈ E', (fun x => v (x * g)) ∈ E' :=
  Iff.rfl

theorem rt_noncommPiCoprod_mem {E' : Submodule ℂ (G → ℂ)} (ι : ∀ w, K w →* G)
    (hcomm : Pairwise fun w w' => ∀ (k : K w) (k' : K w'), Commute (ι w k) (ι w' k'))
    (hst : ∀ (w : Pl) (k : K w), ∀ v ∈ E', (fun x => v (x * ι w k)) ∈ E') (κ : ∀ w, K w) :
    ∀ v ∈ E', (fun x => v (x * MonoidHom.noncommPiCoprod ι hcomm κ)) ∈ E' := by
  have hmem : MonoidHom.noncommPiCoprod ι hcomm κ ∈ rtStabilizer E' := by
    rw [MonoidHom.noncommPiCoprod_apply]
    exact Submonoid.noncommProd_mem _ _ _ _ fun w _ => (mem_rtStabilizer.mpr (hst w (κ w)))
  exact mem_rtStabilizer.mp hmem

end Stable

section Entries

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

abbrev Ent : Type := Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L

def twoSided (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) : Ent L →ₗ[ℝ] Ent L where
  toFun X i j := ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L (A i k) * X k l *
    InfiniteAdeleRing.ringEquiv_mixedSpace L (B l j)
  map_add' X Y := by
    funext i j
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    funext i j
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

omit [NumberField L] in
theorem twoSided_apply (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) (X : Ent L) (i j : Fin 2) :
    twoSided L A B X i j = ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L (A i k) * X k l *
      InfiniteAdeleRing.ringEquiv_mixedSpace L (B l j) :=
  rfl

omit [NumberField L] in
theorem archEntries_mul_mul (A y B : GL (Fin 2) (InfiniteAdeleRing L)) :
    archEntries L (A * y * B) =
      twoSided L (A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) (B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
        (archEntries L y) := by
  funext i j
  rw [twoSided_apply]
  show InfiniteAdeleRing.ringEquiv_mixedSpace L (((A * y * B : GL (Fin 2) (InfiniteAdeleRing L)) :
      Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L)) i j) = _
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply]
  simp only [Matrix.mul_apply, Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]
  rfl

theorem continuous_twoSided_family {T : Type*} [TopologicalSpace T]
    {A B : T → GL (Fin 2) (InfiniteAdeleRing L)} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t => LinearMap.toContinuousLinearMap
      (twoSided L (A t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
        (B t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))) := by
  refine (continuous_clm_apply (𝕜 := ℝ)).mpr fun X => ?_
  have hεA : ∀ i k, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) :=
    fun i k => (continuous_apply k).comp ((continuous_apply i).comp ((ArchEntryBall.continuous_archEntries L).comp hA))
  have hεB : ∀ l j, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j) :=
    fun l j => (continuous_apply j).comp ((continuous_apply l).comp ((ArchEntryBall.continuous_archEntries L).comp hB))
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun t => ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) * X k l *
    InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j)
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (((hεA i k).mul continuous_const).mul (hεB l j))

end Entries

section Main

open scoped Classical

variable (L : Type) [Field L] [NumberField L]

theorem exists_contDiff_dconvWith [MeasurableSpace (ArchInfra.Kprod L)] [BorelSpace (ArchInfra.Kprod L)]
    [SecondCountableTopology (ArchInfra.Kprod L)] (μ : Measure (ArchInfra.Kprod L)) [IsFiniteMeasure μ]
    {e : ArchInfra.Kprod L → ℂ} (he : Continuous e) {ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℝ}
    (hψt : IsArchTestFactor L fun g => (ψ g : ℂ)) :
    ∃ Φ : Ent L → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, dconvWith μ (ArchInfra.inclArch L) e e (fun z => (ψ z : ℂ)) y = Φ (archEntries L y) := by
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hψt
  let a := ArchInfra.inclArch L
  have ha : Continuous a := ArchInfra.continuous_inclArch (F := L)
  let Φf : ArchInfra.Kprod L × ArchInfra.Kprod L → Ent L →L[ℝ] Ent L := fun p =>
    LinearMap.toContinuousLinearMap (twoSided L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
      ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_twoSided_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : ArchInfra.Kprod L × ArchInfra.Kprod L => e p.1 * e p.2 :=
    (he.comp continuous_fst).mul (he.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e p.1 * e p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e p.1 * e p.2 * (fun z => (ψ z : ℂ)) ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e p.1 * e p.2 * (ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℂ) = e p.1 * e p.2 * Φψ (Φf p (archEntries L y))
    rw [show ((ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) : ℝ) : ℂ) = Φψ (archEntries L ((a p.1)⁻¹ * y * (a p.2)⁻¹)) from
      hψΦ _, archEntries_mul_mul]
    rfl

-- The pin's load-bearing `letI`/`haveI` instances feed instance search; the linter's `have` would drop them.
set_option linter.style.haveILetI false in
theorem exists_tendsto_integral_of_mem_archCutSubmodule (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ),
      (∀ n, IsArchTestFactor L (fa n) ∧ IsArchFactorBiFinite L tys (fa n)) ∧
      ∀ g, Filter.Tendsto
        (fun n => letI := glBorelOf (InfiniteAdeleRing L)
          ∫ y, f (g * adelicArchGLIncl L y) * fa n y ∂(archHaarK L))
        Filter.atTop (nhds (f g)) := by
  classical

  letI : MeasurableSpace (GL (Fin 2) (InfiniteAdeleRing L)) := glBorelOf (InfiniteAdeleRing L)
  haveI : BorelSpace (GL (Fin 2) (InfiniteAdeleRing L)) := borelSpace_glBorelOf (InfiniteAdeleRing L)
  haveI : (archHaarK L).IsHaarMeasure := isHaarMeasure_archHaarK L
  haveI : LocallyCompactSpace (GL (Fin 2) (InfiniteAdeleRing L)) := ArchInfraTopology.locallyCompactSpace_archGL L
  haveI : SecondCountableTopology (GL (Fin 2) (InfiniteAdeleRing L)) := ArchInfraTopology.secondCountableTopology_archGL L
  haveI : SigmaFinite (archHaarK L) := ArchInfraTopology.sigmaFinite_archHaarK L

  letI : MeasurableSpace (ArchInfra.Kprod L) := borel _
  haveI : BorelSpace (ArchInfra.Kprod L) := ⟨rfl⟩
  haveI : SecondCountableTopology (ArchInfra.Kprod L) := ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ L
  haveI : (ArchInfra.muK L).IsMulRightInvariant := ArchInfra.isMulRightInvariant_muK L

  have hcomm : ∀ (w w' : InfinitePlace L), w ≠ w' → ∀ (k : ArchInfra.Kw L w) (k' : ArchInfra.Kw L w'),
      rowIsometryInclAt₀ L w k * rowIsometryInclAt₀ L w' k' =
        rowIsometryInclAt₀ L w' k' * rowIsometryInclAt₀ L w k := by
    intro w w' hww' k k'
    show adelicArchGLIncl L (archRowIsometryInclAt₀ L w k) * adelicArchGLIncl L (archRowIsometryInclAt₀ L w' k') =
      adelicArchGLIncl L (archRowIsometryInclAt₀ L w' k') * adelicArchGLIncl L (archRowIsometryInclAt₀ L w k)
    rw [← map_mul, ← map_mul, (ArchInfra.commute_archRowIsometryInclAt₀ L hww' k k').eq]
  have harch' : ∀ w, f ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    (mem_archCutSubmodule_iff L tys f).mp harch
  haveI : FiniteDimensional ℂ (Submodule.span ℂ ({f} : Set (AdelicGL2 (𝓞 L) L → ℂ))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_singleton f)
  have hV : ∀ w, Submodule.span ℂ ({f} : Set (AdelicGL2 (𝓞 L) L → ℂ)) ≤
      ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    fun w => Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (harch' w))
  obtain ⟨E, hEfd, hfE, hEcut, hEst⟩ := exists_finiteDimensional_stable (K := fun w => ArchInfra.Kw L w)
    (fun w => rowIsometryInclAt₀ L w) hcomm (fun w i => (tys.rep w i).ρ) _ hV
  let E' : Submodule ℂ (AdelicGL2 (𝓞 L) L → ℂ) := E ⊓ contSubmodule (AdelicGL2 (𝓞 L) L)
  haveI : FiniteDimensional ℂ E' := Submodule.finiteDimensional_of_le inf_le_left
  have hfE' : f ∈ E' := ⟨hfE (Submodule.subset_span (Set.mem_singleton f)), hf⟩
  have hE'cut : ∀ w, ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ L w) (tys.rep w i).ρ :=
    fun w v hv => hEcut w hv.1
  have hE'st : ∀ (w : InfinitePlace L) (k : ArchInfra.Kw L w), ∀ v ∈ E',
      (fun x => v (x * rowIsometryInclAt₀ L w k)) ∈ E' :=
    fun w k v hv => ⟨hEst w k v hv.1, (show Continuous v from hv.2).comp (continuous_id.mul continuous_const)⟩

  have hc' : Pairwise fun w w' => ∀ (k : ArchInfra.Kw L w) (k' : ArchInfra.Kw L w'),
      Commute (rowIsometryInclAt₀ L w k) (rowIsometryInclAt₀ L w' k') :=
    fun w w' hww' k k' => hcomm w w' hww' k k'
  have hhom : ArchInfra.inclAdelic L = MonoidHom.noncommPiCoprod (fun w => rowIsometryInclAt₀ L w) hc' := by
    refine MonoidHom.pi_ext fun w k => ?_
    rw [ArchInfra.inclAdelic_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
  have hE'K : ∀ κ : ArchInfra.Kprod L, ∀ v ∈ E', (fun x => v (x * ArchInfra.inclAdelic L κ)) ∈ E' := by
    intro κ
    rw [hhom]
    exact rt_noncommPiCoprod_mem (fun w => rowIsometryInclAt₀ L w) hc' hE'st κ
  have hcontE' : ∀ v ∈ E', ∀ x : AdelicGL2 (𝓞 L) L, Continuous fun κ : ArchInfra.Kprod L =>
      v (x * ArchInfra.inclAdelic L κ) :=
    fun v hv x => (show Continuous v from hv.2).comp (continuous_const.mul (ArchInfra.continuous_inclAdelic (F := L)))

  obtain ⟨c, hc⟩ := exists_reproducer (ArchInfra.muK L) (ArchInfra.inclAdelic L) E' hE'K hcontE'
  obtain ⟨e, he_def⟩ : ∃ e : ArchInfra.Kprod L → ℂ,
      ∀ κ, e κ = ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 :=
    ⟨_, fun _ => rfl⟩
  have he : Continuous e := by
    rw [show e = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 from funext he_def]
    exact continuous_finsetSum _ fun q _ => continuous_const.mul
      (continuous_apply_apply_of_continuous (continuous_Pm_inv (ArchInfra.inclAdelic L) E' hE'K hcontE') _ _)
  have hrep : ∀ x : AdelicGL2 (𝓞 L) L,
      ∫ κ, e κ * f (x * adelicArchGLIncl L (ArchInfra.inclArch L κ)) ∂(ArchInfra.muK L) = f x := by
    intro x
    calc (∫ κ, e κ * f (x * adelicArchGLIncl L (ArchInfra.inclArch L κ)) ∂(ArchInfra.muK L))
        = ∫ κ, (∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1) * f (x * ArchInfra.inclAdelic L κ)
            ∂(ArchInfra.muK L) :=
          integral_congr_ae (Filter.Eventually.of_forall fun κ => by beta_reduce; rw [he_def]; rfl)
      _ = f x := hc f hfE' x
  have hed : ∀ w : InfinitePlace L, ∀ (hinj : Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
      (hcut : ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
        ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w)) (tys.rep w i).ρ),
      e ∈ ⨆ i, typeSubmodule (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) (tys.rep w i).ρ.dual := by
    intro w hinj hcut
    rw [show e = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ⁻¹ q.2 q.1 from funext he_def]
    exact reproducer_mem_iSup_dual (ArchInfra.inclAdelic L) E' hE'K hinj (fun i => (tys.rep w i).ρ) hcut c
  have hel : ∀ w : InfinitePlace L, ∀ (hinj : Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w))
      (hcut : ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
        ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w)) (tys.rep w i).ρ),
      (fun κ => e κ⁻¹) ∈ ⨆ i, typeSubmodule (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) (tys.rep w i).ρ := by
    intro w hinj hcut
    rw [show (fun κ => e κ⁻¹) = fun κ => ∑ q, c q * Pm (ArchInfra.inclAdelic L) E' hE'K κ q.2 q.1 from
      funext fun κ => by rw [he_def, inv_inv]]
    exact reproducer_inv_mem_iSup (ArchInfra.inclAdelic L) E' hE'K hinj (fun i => (tys.rep w i).ρ) hcut c
  have ha : Continuous (ArchInfra.inclArch L) := ArchInfra.continuous_inclArch (F := L)

  obtain ⟨ψ, hψ, hsupp⟩ := ArchEntryBall.exists_approxIdentity L
  have hψC : ∀ n, Continuous fun z => (ψ n z : ℂ) := fun n => Complex.continuous_ofReal.comp (hψ n).2.1
  have hψCs : ∀ n, HasCompactSupport fun z => (ψ n z : ℂ) := fun n =>
    (hψ n).2.2.1.comp_left (g := Complex.ofReal) Complex.ofReal_zero

  have hjcut : ∀ w : InfinitePlace L, ∀ v ∈ E', v ∈ ⨆ i, typeSubmodule
      ((ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w)) (tys.rep w i).ρ := by
    intro w
    have hj : (ArchInfra.inclAdelic L).comp (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) =
        rowIsometryInclAt₀ L w :=
      MonoidHom.ext fun k => ArchInfra.inclAdelic_mulSingle w k
    rw [hj]
    exact hE'cut w
  have hjinj : ∀ w : InfinitePlace L, Function.Injective (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w) :=
    fun w => Pi.mulSingle_injective (M := fun w' => ArchInfra.Kw L w') w
  have haj : ∀ (w : InfinitePlace L) (k : ArchInfra.Kw L w),
      ArchInfra.inclArch L (MonoidHom.mulSingle (fun w => ArchInfra.Kw L w) w k) = archRowIsometryInclAt₀ L w k :=
    fun w k => ArchInfra.inclArch_mulSingle w k

  refine ⟨fun n => dconvWith (ArchInfra.muK L) (ArchInfra.inclArch L) e e (fun z => (ψ n z : ℂ)),
    fun n => ⟨⟨?_, ?_⟩, ?_, ?_⟩, fun g => ?_⟩
  · exact exists_contDiff_dconvWith L (ArchInfra.muK L) he (hψ n).1
  · exact hasCompactSupport_dconvWith ha (hψCs n)
  · refine (Submodule.mem_iInf _).mpr fun w => ?_
    exact dconvWith_inv_mem_iSup (ArchEntryBall.archRowIsometryInclAt₀_injective L w) (haj w) (fun i => (tys.rep w i).ρ)
      he (hψC n) ha (hel w (hjinj w) (hjcut w))
  · refine (Submodule.mem_iInf _).mpr fun w => ?_
    exact dconvWith_mem_iSup_dual (ArchEntryBall.archRowIsometryInclAt₀_injective L w) (haj w) (fun i => (tys.rep w i).ρ)
      he (hψC n) ha (hed w (hjinj w) (hjcut w))
  · exact tendsto_integral_mul_dconvWith (ιA := adelicArchGLIncl L) (ν := archHaarK L) ha he f
      (fun x => hf.comp (continuous_const.mul (TestFnNearIdentity.continuous_adelicArchGLIncl L))) hrep
      (fun κ h hh hhs => ArchInfra.integral_archHaarK_mul_inclArch κ hh hhs) ψ (fun n => (hψ n).2.1)
      (fun n => (hψ n).2.2.1)
      (fun φ hφ => ArchEntryBall.tendsto_integral_mul_approxIdentity L (fun n => (hψ n).2.1) (fun n => (hψ n).2.2.1)
        (fun n => (hψ n).2.2.2.1) (fun n => (hψ n).2.2.2.2) hsupp hφ) g

end Main

end Instantiate

end ArchApproxIdentity

end
