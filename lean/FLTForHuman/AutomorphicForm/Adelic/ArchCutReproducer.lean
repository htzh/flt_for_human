/-
  The archimedean cut carries a continuous reproducing kernel.

  Let `E` be a finite-dimensional subspace of `archCutSubmodule F tys` consisting of continuous
  functions and stable under the right translates by the archimedean product `ι` of the
  row-isometry subgroups.  This module proves that `E` carries a *continuous reproducing kernel*:
  a continuous `e` on the product `∏_w K_w` which is conjugation-invariant
  (`e (κ' κ κ'⁻¹) = e κ`), reality-inverting (`e κ⁻¹ = conj (e κ)`), lies in the dual archimedean
  type modules with `κ ↦ e κ⁻¹` in the type modules themselves, and reproduces every `v ∈ E` by

    `∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x`

  against the Haar probability `μ`.  This is the admissibility statement of the archimedean cut
  (`ArchCutSpan`) read as the existence of an integral kernel.

  What is assumed: the coefficient engine of the port's `RepTheory/TypeReproducer`
  (`coeffFun_transRep_mem_iSup`, `dualCoeffFun_transRep_mem_iSup`, the `transRep` machinery), the
  archimedean compactness `isCompact_rowIsometrySubgroup_detOne` of `Adelic/MaximalCompactFactors`
  (SET-AF2's landing), and the two dictionary lemmas of the ground module
  `ArchComponentDictionary`.  The kernel itself is built by the Gram matrix of a basis of the
  orbit span `V` of `E`: an averaging over the compact group by Haar, invertible by positivity, and
  identified as the unique reproducing element by an `L²` argument — the pin's route, transcribed.

  Transcribed from
  `P2M/Sol/S_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean`
  (`solution`, pinned `aa2d8b3`), whose statement is the `Theorems/` wrapper's.  The pin's
  `maxHeartbeats` overrides are not transcribed; the pin's `TypedCoeff` engine is the port's
  `ArchApproxIdentity.*`, and only its private `TypeIdem.typedCoeff` (the two-line dictionary at the
  one-place inclusion) is written here, private.

  spec-pin: Theorems/Thm_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchComponentDictionary
import FLTForHuman.RepTheory.TypeReproducer
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.IsotypicCuspSpace
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import Mathlib.LinearAlgebra.Matrix.Hermitian

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
  IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel

namespace AutomorphicForm

/-- The two coefficient memberships at a one-place inclusion: the coefficients of a vector of a
finite-dimensional stable `E` against a linear functional on `E`, read once as a function of the
translate `κ` and once of the inverse translate `κ⁻¹`, lie in the type modules of `incl` and of its
dual.  This is `coeffFun_transRep_mem_iSup` and `dualCoeffFun_transRep_mem_iSup` composed at the
translate representation of `E`. -/
private theorem typedCoeff
    {H Kc G : Type*} [Group H] [Group Kc] [Group G]
    (incl : H →* Kc) (hincl : Function.Injective incl) (ι : Kc →* G)
    {J : Type*} {W : J → Type*} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    (ρ : ∀ j, Representation ℂ H (W j))
    (E : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ ↥E]
    (hE : ∀ κ : Kc, ∀ v ∈ E, (fun x => v (x * ι κ)) ∈ E)
    (hEt : E ≤ ⨆ j, typeSubmodule (ι.comp incl) (ρ j))
    (lam : ↥E →ₗ[ℂ] ℂ) (v : G → ℂ) (hv : v ∈ E) :
    (fun κ : Kc => lam ⟨fun x => v (x * ι κ), hE κ v hv⟩) ∈ ⨆ j, typeSubmodule incl (ρ j) ∧
    (fun κ : Kc => lam ⟨fun x => v (x * ι κ⁻¹), hE κ⁻¹ v hv⟩) ∈
      ⨆ j, typeSubmodule incl (ρ j).dual := by
  have hEcut : ∀ u ∈ E, u ∈ ⨆ j, typeSubmodule (ι.comp incl) (ρ j) := fun u hu => hEt hu
  exact ⟨ArchApproxIdentity.coeffFun_transRep_mem_iSup hincl ι ρ E hE hEcut lam ⟨v, hv⟩,
    ArchApproxIdentity.dualCoeffFun_transRep_mem_iSup hincl ι ρ E hE hEcut ⟨v, hv⟩ lam⟩

/-- **The reproducing kernel of a finite-dimensional invariant subspace of the archimedean cut.**
There is a continuous `e` on `∏_w K_w`, conjugation-invariant and reality-inverting, lying in the
dual archimedean type modules with `κ ↦ e κ⁻¹` in the type modules, that reproduces every `v ∈ E`
against the Haar probability by `∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x`. -/
theorem exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hE : FiniteDimensional ℂ ↥E)
    (hEc : ∀ v ∈ E, Continuous v) (hEt : E ≤ archCutSubmodule F tys)
    (hEK : ∀ v ∈ E, ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun x => v (x * adelicArchGLIncl F (ι κ))) ∈ E) :
    ∃ e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ,
      Continuous e ∧
      (∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ) ∧
      (∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ)) ∧
      (∀ w : InfinitePlace F,
        e ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) ∧
      (∀ w : InfinitePlace F,
        (fun κ => e κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) ∧
      ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F,
        ∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x := by
  classical
  have hnormsq : ∀ z : ℂ, (((‖z‖ ^ 2 : ℝ)) : ℂ) = conj z * z := fun z => by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]

  obtain ⟨J, hJdef⟩ : ∃ J : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F, J = (adelicArchGLIncl F).comp ι := ⟨_, rfl⟩
  have hJ : ∀ κ, adelicArchGLIncl F (ι κ) = J κ := fun κ => by rw [hJdef]; rfl
  have : ∀ w : InfinitePlace F, CompactSpace (rowIsometrySubgroup₀ w.Completion) := fun w =>
    isCompact_iff_compactSpace.mp (isCompact_rowIsometrySubgroup_detOne F w)

  have hιmat : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (i j : Fin 2) (w : InfinitePlace F),
      ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w
        = (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j := fun κ i j w =>
    congrArg (fun g : GL (Fin 2) w.Completion => (g : Matrix (Fin 2) (Fin 2) w.Completion) i j) (hι κ w)
  have hιval : Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
      ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) := by
    refine continuous_matrix fun i j => continuous_pi fun w => ?_
    have : (fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) =>
        ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j w)
        = fun κ => (((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion) :
            Matrix (Fin 2) (Fin 2) w.Completion) i j := funext fun κ => hιmat κ i j w
    rw [this]
    exact (Units.continuous_val.matrix_elem i j).comp (continuous_subtype_val.comp (continuous_apply w))
  have hιC : Continuous ι := by
    refine Units.continuous_iff.2 ⟨hιval, ?_⟩
    have : (fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => ((↑((ι κ)⁻¹) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))))
        = (fun κ => ((ι κ : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))) ∘
            fun κ => κ⁻¹ := by
      funext κ; simp only [Function.comp_apply, map_inv]
    rw [this]
    exact hιval.comp continuous_inv
  have hAval : ∀ (g : GL (Fin 2) (InfiniteAdeleRing F)) (i j : Fin 2),
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j
        = (((g : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j),
            ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)) := fun g i j => rfl
  have hAcontval : Continuous fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
      ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) := by
    refine continuous_matrix fun i j => ?_
    have : (fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j)
        = fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
            ((((g : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j),
            ((1 : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j)) := funext fun g => hAval g i j
    rw [this]
    exact (Units.continuous_val.matrix_elem i j).prodMk continuous_const
  have hAC : Continuous (adelicArchGLIncl F) := by
    refine Units.continuous_iff.2 ⟨hAcontval, ?_⟩
    have : (fun g : GL (Fin 2) (InfiniteAdeleRing F) =>
        ((↑((adelicArchGLIncl F g)⁻¹) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))))
        = (fun g => ((adelicArchGLIncl F g : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F))) ∘
            fun g => g⁻¹ := by
      funext g; simp only [Function.comp_apply, map_inv]
    rw [this]
    exact hAcontval.comp continuous_inv
  have hJC : Continuous J := by rw [hJdef]; exact hAC.comp hιC

  have hint : ∀ {g : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ}, Continuous g → Integrable g μ := by
    intro g hg
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
    exact Integrable.mono' (integrable_const C) hg.aestronglyMeasurable
      (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))

  have hopen : ∀ U : Set (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), IsOpen U → U.Nonempty → 0 < μ U := by
    intro U hU hne
    obtain ⟨u₀, hu₀⟩ := hne
    by_contra h0
    have hU0 : μ U = 0 := nonpos_iff_eq_zero.1 (not_lt.1 h0)

    have hcover : (Set.univ : Set (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) ⊆ ⋃ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun x => κ * x) ⁻¹' U := by
      intro x _
      refine Set.mem_iUnion.2 ⟨u₀ * x⁻¹, ?_⟩
      show u₀ * x⁻¹ * x ∈ U
      rwa [inv_mul_cancel_right]
    obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => (fun x => κ * x) ⁻¹' U)
      (fun κ => hU.preimage (continuous_const.mul continuous_id)) hcover
    have hle : μ Set.univ ≤ ∑ κ ∈ s, μ ((fun x => κ * x) ⁻¹' U) :=
      (measure_mono hs).trans (measure_biUnion_finset_le s _)
    have hzero : ∀ κ ∈ s, μ ((fun x => κ * x) ⁻¹' U) = 0 := fun κ _ => by
      rw [measure_preimage_mul, hU0]
    rw [Finset.sum_eq_zero hzero, measure_univ] at hle
    exact absurd hle (by norm_num)

  have hL2zero : ∀ {g : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ}, Continuous g → ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ = 0 → g = 0 := by
    intro g hg h0
    by_contra hne
    obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀, g κ₀ ≠ 0 := Function.ne_iff.1 hne
    have hcont : Continuous fun κ => (‖g κ‖ ^ 2 : ℝ) := (continuous_norm.comp hg).pow 2
    have hnn : 0 ≤ fun κ => (‖g κ‖ ^ 2 : ℝ) := fun κ => sq_nonneg _
    have hintg : Integrable (fun κ => (‖g κ‖ ^ 2 : ℝ)) μ := by
      obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
      exact Integrable.mono' (integrable_const C) hcont.aestronglyMeasurable
        (Filter.Eventually.of_forall fun κ => hC κ (Set.mem_univ κ))
    have hpos : 0 < ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ := by
      rw [integral_pos_iff_support_of_nonneg hnn hintg]
      refine hopen _ (hcont.isOpen_support) ⟨κ₀, ?_⟩
      rw [Function.mem_support]
      exact pow_ne_zero 2 (norm_ne_zero_iff.2 hκ₀)
    exact absurd h0 hpos.ne'

  have : FiniteDimensional ℂ ↥E := hE

  have hRmem : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (v : ↥E), (fun x => (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ)) ∈ E := by
    intro κ v
    have := hEK v v.2 κ
    simpa only [hJ] using this
  let R : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → (↥E →ₗ[ℂ] ↥E) := fun κ =>
    { toFun := fun v => ⟨fun x => (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ), hRmem κ v⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hRapply : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (v : ↥E) (x : AdelicGL2 (𝓞 F) F),
      ((R κ v : ↥E) : AdelicGL2 (𝓞 F) F → ℂ) x = (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ) := fun _ _ _ => rfl
  have hRmul : ∀ κ₁ κ₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), R (κ₁ * κ₂) = R κ₁ ∘ₗ R κ₂ := by
    intro κ₁ κ₂
    refine LinearMap.ext fun v => Subtype.ext (funext fun x => ?_)
    show (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J (κ₁ * κ₂)) = (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ₁ * J κ₂)
    rw [map_mul, mul_assoc]
  have hRone : R 1 = LinearMap.id := by
    refine LinearMap.ext fun v => Subtype.ext (funext fun x => ?_)
    show (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J 1) = (v : AdelicGL2 (𝓞 F) F → ℂ) x
    rw [map_one, mul_one]

  obtain ⟨n, bE⟩ : Σ n : ℕ, Module.Basis (Fin n) ℂ ↥E := ⟨_, Module.finBasis ℂ ↥E⟩
  let coef : Fin n → Fin n → (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun i j κ => bE.repr (R κ (bE i)) j
  have hRbasis : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (i : Fin n), R κ (bE i) = ∑ j, coef i j κ • bE j := by
    intro κ i
    exact (bE.sum_repr (R κ (bE i))).symm

  have hcoefC : ∀ i j, Continuous (coef i j) := by
    intro i j
    have hℓ : Continuous (fun v : ↥E => ((Finsupp.lapply j).comp bE.repr.toLinearMap) v) :=
      LinearMap.continuous_of_finiteDimensional _
    have hR : Continuous fun κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) => R κ (bE i) := by
      refine Continuous.subtype_mk (continuous_pi fun x => ?_) _
      exact (hEc _ (bE i).2).comp (continuous_const.mul hJC)
    exact hℓ.comp hR

  let V : Submodule ℂ ((∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) := Submodule.span ℂ (Set.range fun p : Fin n × Fin n => coef p.1 p.2)
  have hVcont : ∀ a ∈ V, Continuous a := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => Continuous a) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩; exact hcoefC p.1 p.2
    · exact continuous_const
    · exact fun _ _ _ _ h1 h2 => h1.add h2
    · exact fun c _ _ h => h.const_smul c
  have horbit : ∀ (v : ↥E) (x : AdelicGL2 (𝓞 F) F),
      (fun κ => (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ)) ∈ V := by
    intro v x
    have hv : ∀ κ, (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ)
        = ∑ i, bE.repr v i * ∑ j, coef i j κ * ((bE j : ↥E) : AdelicGL2 (𝓞 F) F → ℂ) x := by
      intro κ
      have h1 : R κ v = ∑ i, bE.repr v i • R κ (bE i) := by
        conv_lhs => rw [← bE.sum_repr v]
        rw [map_sum]
        simp only [map_smul]
      have h2 := congrArg (fun w : ↥E => (w : AdelicGL2 (𝓞 F) F → ℂ) x) h1
      simp only [hRapply] at h2
      rw [h2]
      simp only [hRbasis, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    have : (fun κ => (v : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ))
        = ∑ i, ∑ j, (bE.repr v i * ((bE j : ↥E) : AdelicGL2 (𝓞 F) F → ℂ) x) • coef i j := by
      funext κ
      rw [hv]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [this]
    refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨(i, j), rfl⟩

  have hrep : ∃ e : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ, Continuous e ∧ (fun κ => conj (e κ)) ∈ V ∧
      ∀ a ∈ V, ∫ κ, e κ * a κ ∂μ = a 1 := by
    have : FiniteDimensional ℂ ↥V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    obtain ⟨m, bV⟩ : Σ m : ℕ, Module.Basis (Fin m) ℂ ↥V := ⟨_, Module.finBasis ℂ ↥V⟩
    let w : Fin m → (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ := fun k => ((bV k : ↥V) : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)
    have hwV : ∀ k, w k ∈ V := fun k => (bV k).2
    have hwC : ∀ k, Continuous (w k) := fun k => hVcont _ (hwV k)
    let G : Matrix (Fin m) (Fin m) ℂ := fun k l => ∫ κ, w k κ * conj (w l κ) ∂μ
    have hGint : ∀ k l, Integrable (fun κ => w k κ * conj (w l κ)) μ := fun k l =>
      hint ((hwC k).mul (Complex.continuous_conj.comp (hwC l)))
    have hGH : Matrix.IsHermitian G := by
      refine Matrix.IsHermitian.ext fun k l => ?_
      show conj (∫ κ, w l κ * conj (w k κ) ∂μ) = ∫ κ, w k κ * conj (w l κ) ∂μ
      rw [← integral_conj]
      refine integral_congr_ae (Filter.Eventually.of_forall fun κ => ?_)
      show conj (w l κ * conj (w k κ)) = w k κ * conj (w l κ)
      rw [map_mul, Complex.conj_conj, mul_comm]

    have hquad : ∀ c : Fin m → ℂ, star c ⬝ᵥ G.mulVec c
        = ∫ κ, (((‖∑ l, c l * conj (w l κ)‖ ^ 2 : ℝ)) : ℂ) ∂μ := by
      intro c
      have h1 : ∀ κ, (((‖∑ l, c l * conj (w l κ)‖ ^ 2 : ℝ)) : ℂ)
          = ∑ k, ∑ l, (conj (c k) * c l) * (w k κ * conj (w l κ)) := by
        intro κ
        rw [hnormsq, map_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [map_mul, Complex.conj_conj]
        ring
      simp_rw [h1]
      rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => (hGint k l).const_mul _]
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun l _ => (hGint k l).const_mul _]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul]
      ring
    have hinj : Function.Injective G.mulVec := by
      intro c₁ c₂ h12
      rw [← sub_eq_zero]
      have hc0 : G.mulVec (c₁ - c₂) = 0 := by rw [Matrix.mulVec_sub, h12, sub_self]
      have hq : star (c₁ - c₂) ⬝ᵥ G.mulVec (c₁ - c₂) = 0 := by rw [hc0, dotProduct_zero]
      rw [hquad, integral_complex_ofReal, Complex.ofReal_eq_zero] at hq
      obtain ⟨g, hgdef⟩ : ∃ g : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ, ∀ κ, g κ = ∑ l, (c₁ - c₂) l * conj (w l κ) := ⟨_, fun _ => rfl⟩
      have hgC : Continuous g := by
        have : g = fun κ => ∑ l, (c₁ - c₂) l * conj (w l κ) := funext hgdef
        rw [this]
        exact continuous_finsetSum _ fun l _ => continuous_const.mul (Complex.continuous_conj.comp (hwC l))
      have hq' : ∫ κ, (‖g κ‖ ^ 2 : ℝ) ∂μ = 0 := by
        have : (fun κ => (‖g κ‖ ^ 2 : ℝ)) = fun κ => (‖∑ l, (c₁ - c₂) l * conj (w l κ)‖ ^ 2 : ℝ) := funext fun κ => by rw [hgdef]
        rw [this]; exact hq
      have hg0 := hL2zero hgC hq'

      have hsum : (∑ l, (conj ((c₁ - c₂) l)) • (bV l : ↥V)) = 0 := by
        refine Subtype.ext (funext fun κ => ?_)
        have h0 := congrArg conj ((hgdef κ).symm.trans (congrFun hg0 κ))
        simp only [Pi.zero_apply, map_zero, map_sum, map_mul, Complex.conj_conj] at h0
        rw [Submodule.coe_sum]
        simp only [Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h0 ⊢
        exact h0
      have hli := Fintype.linearIndependent_iff.1 bV.linearIndependent (fun l => conj ((c₁ - c₂) l)) hsum
      funext l
      have := congrArg conj (hli l)
      simpa using this
    have hGdet : IsUnit G.det := (Matrix.isUnit_iff_isUnit_det G).1 (Matrix.mulVec_injective_iff_isUnit.1 hinj)

    let y : Fin m → ℂ := fun k => w k 1
    let d : Fin m → ℂ := G⁻¹.mulVec y
    have hGd : G.mulVec d = y := by
      show G.mulVec (G⁻¹.mulVec y) = y
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hGdet, Matrix.one_mulVec]
    refine ⟨fun κ => ∑ l, d l * conj (w l κ), ?_, ?_, ?_⟩
    · exact continuous_finsetSum _ fun l _ => continuous_const.mul (Complex.continuous_conj.comp (hwC l))
    · have : (fun κ => conj (∑ l, d l * conj (w l κ))) = ∑ l, conj (d l) • w l := by
        funext κ
        simp only [map_sum, map_mul, Complex.conj_conj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (hwV l)
    ·
      have hbasis : ∀ k, ∫ κ, (∑ l, d l * conj (w l κ)) * w k κ ∂μ = w k 1 := by
        intro k
        have : (fun κ => (∑ l, d l * conj (w l κ)) * w k κ) = fun κ => ∑ l, d l * (w k κ * conj (w l κ)) := by
          funext κ; rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun l _ => ?_; ring
        rw [this, integral_finsetSum _ fun l _ => (hGint k l).const_mul _]
        simp_rw [integral_const_mul]
        have := congrFun hGd k
        simp only [Matrix.mulVec, dotProduct] at this
        refine Eq.trans ?_ this
        exact Finset.sum_congr rfl fun l _ => mul_comm _ _
      intro a ha

      have hexp : a = ∑ k, bV.repr ⟨a, ha⟩ k • w k := by
        have h := congrArg (fun v : ↥V => (v : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ)) (bV.sum_repr ⟨a, ha⟩).symm
        simpa only [Submodule.coe_sum, Submodule.coe_smul] using h
      have hintk : ∀ k, Integrable (fun κ => (∑ l, d l * conj (w l κ)) * w k κ) μ := fun k =>
        hint ((continuous_finsetSum _ fun l _ =>
          continuous_const.mul (Complex.continuous_conj.comp (hwC l))).mul (hwC k))
      rw [hexp]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [integral_finsetSum _ fun k _ => ?_]
      · refine Finset.sum_congr rfl fun k _ => ?_
        have : (fun κ => (∑ l, d l * conj (w l κ)) * (bV.repr ⟨a, ha⟩ k * w k κ))
            = fun κ => bV.repr ⟨a, ha⟩ k * ((∑ l, d l * conj (w l κ)) * w k κ) := by
          funext κ; ring
        rw [this, integral_const_mul, hbasis]
      · have : (fun κ => (∑ l, d l * conj (w l κ)) * (bV.repr ⟨a, ha⟩ k * w k κ))
            = fun κ => bV.repr ⟨a, ha⟩ k * ((∑ l, d l * conj (w l κ)) * w k κ) := by
          funext κ; ring
        rw [this]
        exact (hintk k).const_mul _
  obtain ⟨e, heC, heV, he⟩ := hrep

  have hreproduce : ∀ v ∈ E, ∀ x : AdelicGL2 (𝓞 F) F, ∫ κ, e κ * v (x * adelicArchGLIncl F (ι κ)) ∂μ = v x := by
    intro v hv x
    have h := he _ (horbit ⟨v, hv⟩ x)
    simp only [map_one, mul_one] at h
    simpa only [hJ] using h

  have hcoef_mul : ∀ (κ₁ κ₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (i j : Fin n), coef i j (κ₁ * κ₂) = ∑ k, coef i k κ₂ * coef k j κ₁ := by
    intro κ₁ κ₂ i j
    have h : R (κ₁ * κ₂) (bE i) = ∑ k, coef i k κ₂ • R κ₁ (bE k) := by
      rw [hRmul, LinearMap.comp_apply, hRbasis κ₂ i, map_sum]
      simp only [map_smul]
    show bE.repr (R (κ₁ * κ₂) (bE i)) j = ∑ k, coef i k κ₂ * coef k j κ₁
    rw [h, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul]

  have hVright : ∀ a ∈ V, ∀ t : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun κ => a (κ * t)) ∈ V := by
    intro a ha t
    refine Submodule.span_induction (p := fun a _ => (fun κ => a (κ * t)) ∈ V) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩
      have : (fun κ => coef p.1 p.2 (κ * t)) = ∑ k, coef p.1 k t • coef k p.2 := by
        funext κ
        rw [hcoef_mul]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [this]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(k, p.2), rfl⟩)
    · exact V.zero_mem
    · intro a b _ _ ha hb; exact V.add_mem ha hb
    · intro c a _ ha; exact V.smul_mem c ha
  have hVleft : ∀ a ∈ V, ∀ t : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun κ => a (t * κ)) ∈ V := by
    intro a ha t
    refine Submodule.span_induction (p := fun a _ => (fun κ => a (t * κ)) ∈ V) ?_ ?_ ?_ ?_ ha
    · rintro _ ⟨p, rfl⟩
      have : (fun κ => coef p.1 p.2 (t * κ)) = ∑ k, coef k p.2 t • coef p.1 k := by
        funext κ
        rw [hcoef_mul]
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        refine Finset.sum_congr rfl fun k _ => mul_comm _ _
      rw [this]
      exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨(p.1, k), rfl⟩)
    · exact V.zero_mem
    · intro a b _ _ ha hb; exact V.add_mem ha hb
    · intro c a _ ha; exact V.smul_mem c ha
  have hVconj : ∀ a ∈ V, ∀ t : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), (fun κ => a (t * κ * t⁻¹)) ∈ V := by
    intro a ha t
    have h1 := hVright a ha t⁻¹
    have h2 := hVleft _ h1 t
    exact h2

  have huniq : ∀ e₁ e₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ, Continuous e₁ → Continuous e₂ →
      (fun κ => conj (e₁ κ)) ∈ V → (fun κ => conj (e₂ κ)) ∈ V →
      (∀ a ∈ V, ∫ κ, e₁ κ * a κ ∂μ = a 1) → (∀ a ∈ V, ∫ κ, e₂ κ * a κ ∂μ = a 1) → e₁ = e₂ := by
    intro e₁ e₂ h1 h2 hV1 hV2 hr1 hr2
    obtain ⟨d, hddef⟩ : ∃ d : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ, ∀ κ, d κ = e₁ κ - e₂ κ := ⟨_, fun _ => rfl⟩
    have hdC : Continuous d := by
      have : d = fun κ => e₁ κ - e₂ κ := funext hddef
      rw [this]; exact h1.sub h2
    have hdV : (fun κ => conj (d κ)) ∈ V := by
      have : (fun κ => conj (d κ)) = (fun κ => conj (e₁ κ)) - fun κ => conj (e₂ κ) := by
        funext κ; simp only [hddef, map_sub, Pi.sub_apply]
      rw [this]; exact V.sub_mem hV1 hV2
    have hzero : ∫ κ, d κ * conj (d κ) ∂μ = 0 := by
      have ha1 := hr1 _ hdV
      have ha2 := hr2 _ hdV
      have hi1 : Integrable (fun κ => e₁ κ * conj (d κ)) μ :=
        hint (h1.mul (Complex.continuous_conj.comp hdC))
      have hi2 : Integrable (fun κ => e₂ κ * conj (d κ)) μ :=
        hint (h2.mul (Complex.continuous_conj.comp hdC))
      have : (fun κ => d κ * conj (d κ)) = fun κ => e₁ κ * conj (d κ) - e₂ κ * conj (d κ) := by
        funext κ; rw [hddef κ]; ring
      rw [this, integral_sub hi1 hi2, ha1, ha2, sub_self]
    have hsq : ∫ κ, (‖d κ‖ ^ 2 : ℝ) ∂μ = 0 := by
      have : (fun κ => d κ * conj (d κ)) = fun κ => (((‖d κ‖ ^ 2 : ℝ)) : ℂ) := by
        funext κ; rw [hnormsq, mul_comm]
      rw [this, integral_complex_ofReal] at hzero
      exact_mod_cast hzero
    have hd0 := hL2zero hdC hsq
    funext κ
    have hκ := congrFun hd0 κ
    rw [hddef κ, Pi.zero_apply] at hκ
    exact sub_eq_zero.1 hκ

  have hclass : ∀ κ κ' : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e (κ' * κ * κ'⁻¹) = e κ := by
    intro κ κ'
    have key : (fun κ => e (κ' * κ * κ'⁻¹)) = e := by
      refine huniq _ _ (heC.comp ((continuous_const.mul continuous_id).mul continuous_const)) heC ?_ heV ?_ he
      · exact hVconj _ heV κ'
      · intro a ha

        have haV := hVconj a ha κ'⁻¹
        simp only [inv_inv] at haV
        have h1 := he _ haV
        simp only [mul_one, inv_mul_cancel] at h1

        rw [← h1]
        have hsubR := integral_mul_right_eq_self (μ := μ) (fun x => e (κ' * x) * a (x * κ')) κ'⁻¹
        have hsubL := integral_mul_left_eq_self (μ := μ) (fun x => e x * a (κ'⁻¹ * x * κ')) κ'

        have step1 : (fun κ => e (κ' * κ * κ'⁻¹) * a κ) = fun κ => (fun x => e (κ' * x) * a (x * κ')) (κ * κ'⁻¹) := by
          funext κ; simp only [mul_assoc, inv_mul_cancel, mul_one]
        have step2 : (fun x => e (κ' * x) * a (x * κ')) = fun x => (fun y => e y * a (κ'⁻¹ * y * κ')) (κ' * x) := by
          funext x; simp only [← mul_assoc, inv_mul_cancel, one_mul]
        rw [step1, hsubR, step2, hsubL]
    exact congrFun key κ

  have hflat : ∀ κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), e κ⁻¹ = conj (e κ) := by
    intro s

    have star : ∀ t : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion), ∫ κ, e κ * conj (e (κ * t)) ∂μ = conj (e t) := by
      intro t
      have h := he _ (hVright _ heV t)
      simpa only [one_mul] using h

    have h1 : e s⁻¹ = conj (∫ κ, e κ * conj (e (κ * s⁻¹)) ∂μ) := by rw [star, Complex.conj_conj]
    rw [h1, ← integral_conj]
    have h2 : (fun κ => (starRingEnd ℂ) (e κ * conj (e (κ * s⁻¹)))) = fun κ => (fun x => e x * conj (e (x * s))) (κ * s⁻¹) := by
      funext κ
      simp only [map_mul, Complex.conj_conj, inv_mul_cancel_right, mul_comm]
    rw [h2, integral_mul_right_eq_self (μ := μ) (fun x => e x * conj (e (x * s))) s⁻¹, star]

  have hJw : ∀ w : InfinitePlace F,
      J.comp (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w)
        = rowIsometryInclAt₀ F w := by
    intro w
    ext1 k
    rw [hJdef]
    exact adelicArchGLIncl_iota_mulSingle ι hι w k
  have hinclw : ∀ w : InfinitePlace F, Function.Injective
      (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w) :=
    fun w a b h => Pi.mulSingle_injective (M := fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w h
  have hRmem' : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)), ∀ v ∈ E, (fun x => v (x * J κ)) ∈ E := fun κ v hv => hRmem κ ⟨v, hv⟩
  have hEtw : ∀ w : InfinitePlace F, E ≤ ⨆ i : Fin (tys.card w),
      typeSubmodule (J.comp (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w))
        (tys.rep w i).ρ := by
    intro w v hv
    rw [hJw]
    exact (mem_archCutSubmodule_iff F tys v).mp (hEt hv) w
  have hTC := fun (w : InfinitePlace F) (p : Fin n × Fin n) =>
    typedCoeff
      (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w) (hinclw w) J
      (fun i : Fin (tys.card w) => (tys.rep w i).ρ) E hRmem' (hEtw w) (bE.coord p.2) (bE p.1) (bE p.1).2
  have hcoef_eq : ∀ p : Fin n × Fin n, coef p.1 p.2
      = fun κ => bE.coord p.2 ⟨fun x => ((bE p.1 : ↥E) : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ), hRmem' κ _ (bE p.1).2⟩ :=
    fun p => rfl
  have hcoefinv_eq : ∀ p : Fin n × Fin n, (fun κ => coef p.1 p.2 κ⁻¹)
      = fun κ => bE.coord p.2 ⟨fun x => ((bE p.1 : ↥E) : AdelicGL2 (𝓞 F) F → ℂ) (x * J κ⁻¹), hRmem' κ⁻¹ _ (bE p.1).2⟩ :=
    fun p => rfl
  refine ⟨e, heC, hclass, hflat, ?_, ?_, hreproduce⟩
  ·
    intro w
    have he4 : e = fun κ => (fun κ' => conj (e κ')) κ⁻¹ := by
      funext κ
      show e κ = conj (e κ⁻¹)
      rw [← hflat κ⁻¹, inv_inv]
    rw [he4]
    refine Submodule.span_induction
      (p := fun g _ => (fun κ => g κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
        typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w)
          (tys.rep w i).ρ.dual) ?_ ?_ ?_ ?_ heV
    · rintro _ ⟨p, rfl⟩
      rw [hcoefinv_eq]
      exact (hTC w p).2
    · exact Submodule.zero_mem _
    · intro a b _ _ ha hb
      exact Submodule.add_mem _ ha hb
    · intro c a _ ha
      exact Submodule.smul_mem _ c ha
  ·
    intro w
    have he5 : (fun κ => e κ⁻¹) = fun κ => conj (e κ) := funext hflat
    rw [he5]
    refine (Submodule.span_le.mpr ?_) heV
    rintro _ ⟨p, rfl⟩
    show coef p.1 p.2 ∈ (⨆ i : Fin (tys.card w),
      typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => ↥(rowIsometrySubgroup₀ w.Completion)) w)
        (tys.rep w i).ρ)
    rw [hcoef_eq]
    exact (hTC w p).1
end AutomorphicForm
