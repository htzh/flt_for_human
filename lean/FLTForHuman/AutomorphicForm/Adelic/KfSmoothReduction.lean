/-
  The `Kf`-smooth predicate, and what it lets a function ignore.

  Two rows, one subject -- the class `IsKfSmooth` of functions that are smooth in the finite
  variable and right-invariant under an open compact:

  * `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway`: for `f` smooth in
    the finite variable and invariant under the finite maximal compact, multiplying its argument by
    an element of a small enough neighbourhood of `1` inside `maximalCompactAway` does not change the
    value -- `exists_maximalCompactAway_subset_of_mem_nhds_one` supplies the neighbourhood.
  * `IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq`: a `Kf`-smooth function is a
    function of the finite variable times an invariant one on the archimedean component, i.e. it
    factors as `x ↦ f (glFin x)` on a compact-open set of the form `K_f * K_∞` intersected with the
    level subgroup -- `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` is the compactness.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway.lean`
  (209 lines: twelve public prelude rows in `namespace RS22` and the headline) and
  `P2M/Sol/S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.lean`
  (108 lines: five public prelude rows in `namespace AutomorphicForm` and the headline), with the
  statements from the wrappers of the same names.  The first file's label namespace is a machine token
  and is rectified to the word namespace `KfSmoothReduction`; the second's `AutomorphicForm` is the
  real namespace and is kept.  Both preludes are **public in the pin** and stay public here, which is
  why this module is checker-visible beyond the two headlines.

  Assumes from earlier modules: `AutomorphicForm/Adelic/MaximalCompactFactors.lean`
  (`exists_maximalCompactAway_subset_of_mem_nhds_one`), `AutomorphicForm/Adelic/ArchKFinite.lean`
  (`IsKfSmooth`'s definition layer) and `AutomorphicForm/Adelic/LevelCompactness.lean:150`
  (`isCompact_levelOne_inf_finiteAdelicGL2Subgroup`, reached transitively through `MaximalCompactFactors`).

  spec-pin: Theorems/Thm_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway.lean
  spec-pin: Theorems/Thm_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsKfSmooth_exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.ArchKFinite
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Topology ProbabilityTheory
open scoped NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace KfSmoothReduction

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel
open AdelicDock FLT.SmoothVectors Topology

variable {K : Type} [Field K] [NumberField K]

def atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) : AdelicGL2 (𝓞 K) K :=
  finEmbed (𝓞 K) K (localEmbed (𝓞 K) K v g)

theorem placeEmbed_eq_atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    UnramifiedWhittaker.placeEmbed K v g = atPlace v g := rfl

theorem glArch_atPlace (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    glArch (𝓞 K) K (atPlace v g) = 1 := glArch_finEmbed _ _ _

theorem finComponent_atPlace_self (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K)) :
    finComponent (𝓞 K) K v (glFin (𝓞 K) K (atPlace v g)) = g := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_self]

theorem finComponent_atPlace_of_ne (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K))
    {w : HeightOneSpectrum (𝓞 K)} (hw : w ≠ v) :
    finComponent (𝓞 K) K w (glFin (𝓞 K) K (atPlace v g)) = 1 := by
  rw [atPlace, glFin_finEmbed, finComponent_localEmbed_of_ne _ _ _ _ hw]

theorem localEmbed_entries_integral (v : HeightOneSpectrum (𝓞 K)) (g : GL (Fin 2) (v.adicCompletion K))
    (hg : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (i j : Fin 2) :
    ((localEmbed (𝓞 K) K v g : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) :
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 K) K)) i j ∈ integralFiniteAdeles (𝓞 K) K := by
  intro w
  rw [coe_localEmbed]
  by_cases hw : w = v
  · subst hw
    rw [localMat_apply_self]
    exact hg i j
  · rw [localMat_apply_of_ne _ _ _ _ i j hw, Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem atPlace_mem (v : HeightOneSpectrum (𝓞 K)) {k : AdelicGL2 (𝓞 K) K} (hk : k ∈ adelicMaximalCompact K) :
    atPlace v (finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ∈ adelicMaximalCompact K := by
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hgdef
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hgdef, finComponent_apply]
    exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hgdef, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact K).inv_mem hk).1).1 i j v
  refine ⟨?_, fun w => ?_⟩
  · rw [atPlace, glFin_finEmbed, mem_finiteIntegralGL2_iff]
    refine ⟨localEmbed_entries_integral v g hint, ?_⟩
    intro i j
    rw [← map_inv]
    exact localEmbed_entries_integral v g⁻¹ hint' i j
  · rw [glArch_atPlace, map_one]
    exact isRowIsometry_one

theorem exists_map_eq_finComponent (v : HeightOneSpectrum (𝓞 K)) {k : AdelicGL2 (𝓞 K) K}
    (hk : k ∈ adelicMaximalCompact K) :
    ∃ kv : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv =
        finComponent (𝓞 K) K v (glFin (𝓞 K) K k) := by
  have hkf := mem_finiteIntegralGL2_iff.mp hk.1
  set g := finComponent (𝓞 K) K v (glFin (𝓞 K) K k) with hg
  have hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j; rw [hg, finComponent_apply]; exact hkf.1 i j v
  have hint' : ∀ i j, ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j
      ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [hg, ← map_inv, ← map_inv, finComponent_apply]
    exact (mem_finiteIntegralGL2_iff.mp ((adelicMaximalCompact K).inv_mem hk).1).1 i j v
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint i j⟩
  let Minv : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint' i j⟩
  have hinj : Function.Injective (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) :=
    Subtype.val_injective
  have hM : M.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by ext i j; rfl
  have hMinv : Minv.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) =
      ((g⁻¹ : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by ext i j; rfl
  have h1 : M * Minv = 1 := by
    apply Matrix.map_injective hinj
    change (M * Minv).map (algebraMap _ _) = (1 : Matrix (Fin 2) (Fin 2) _).map (algebraMap _ _)
    rw [Matrix.map_mul, hM, hMinv, Matrix.map_one (algebraMap _ _) (map_zero _) (map_one _)]
    exact g.val_inv
  have h2 : Minv * M = 1 := by
    apply Matrix.map_injective hinj
    change (Minv * M).map (algebraMap _ _) = (1 : Matrix (Fin 2) (Fin 2) _).map (algebraMap _ _)
    rw [Matrix.map_mul, hM, hMinv, Matrix.map_one (algebraMap _ _) (map_zero _) (map_one _)]
    exact g.inv_val
  refine ⟨⟨M, Minv, h1, h2⟩, ?_⟩
  apply Units.ext
  exact hM

theorem exists_fixing_away (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 K)), ∀ k ∈ maximalCompactAway K S₀, ∀ g : AdelicGL2 (𝓞 K) K,
      φ (g * k) = φ g := by
  have hopen : IsOpen ((MulAction.stabilizer (finiteAdelicGL2Subgroup K)
      (RightTranslationFn.mk φ : RightTranslationFn (AdelicGL2 (𝓞 K) K) ℂ) :
        Subgroup (finiteAdelicGL2Subgroup K)) : Set (finiteAdelicGL2Subgroup K)) := hφ
  obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hopen
  have h1O : (1 : AdelicGL2 (𝓞 K) K) ∈ O := by
    have : (1 : finiteAdelicGL2Subgroup K) ∈ (Subtype.val ⁻¹' O : Set (finiteAdelicGL2Subgroup K)) := by
      rw [hOpre]; exact Subgroup.one_mem _
    exact this
  obtain ⟨S₀, hS₀⟩ := AutomorphicForm.exists_maximalCompactAway_subset_of_mem_nhds_one K O (hO.mem_nhds h1O)
  refine ⟨S₀, fun k hk g => ?_⟩
  have hka : glArch (𝓞 K) K k = 1 := (mem_maximalCompactAway_iff.mp hk).2.1
  have hkO : (⟨k, hka⟩ : finiteAdelicGL2Subgroup K) ∈
      (Subtype.val ⁻¹' O : Set (finiteAdelicGL2Subgroup K)) := hS₀ hk
  rw [hOpre] at hkO
  have hstab := MulAction.mem_stabilizer_iff.mp hkO
  have := congrArg (fun f => RightTranslationFn.toFun f g) hstab
  simp at this
  exact this

theorem exists_truncation_fixing (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K))
      (g : AdelicGL2 (𝓞 K) K), φ (g * UnramifiedWhittaker.placeEmbed K v
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g)
    (k : AdelicGL2 (𝓞 K) K) (hk : k ∈ adelicMaximalCompact K)
    (T : Finset (HeightOneSpectrum (𝓞 K))) (hT : ∀ v ∈ T, v ∉ S) :
    ∃ m : AdelicGL2 (𝓞 K) K, m ∈ adelicMaximalCompact K ∧ glArch (𝓞 K) K m = 1 ∧
      (∀ v ∈ T, finComponent (𝓞 K) K v (glFin (𝓞 K) K m) = finComponent (𝓞 K) K v (glFin (𝓞 K) K k)) ∧
      (∀ v ∉ T, finComponent (𝓞 K) K v (glFin (𝓞 K) K m) = 1) ∧
      (∀ g : AdelicGL2 (𝓞 K) K, φ (g * m) = φ g) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨1, one_mem _, map_one _, fun v hv => absurd hv (Finset.notMem_empty v),
      fun v _ => by rw [map_one, map_one], fun g => by rw [mul_one]⟩
  | insert u T hu ih =>
    obtain ⟨m, hmK, hma, hmon, hmoff, hmfix⟩ := ih (fun v hv => hT v (Finset.mem_insert_of_mem hv))
    have huS : u ∉ S := hT u (Finset.mem_insert_self u T)
    obtain ⟨ku, hku⟩ := exists_map_eq_finComponent u hk
    have hmemu : atPlace u (finComponent (𝓞 K) K u (glFin (𝓞 K) K k)) ∈ adelicMaximalCompact K :=
      atPlace_mem u hk
    refine ⟨m * atPlace u (finComponent (𝓞 K) K u (glFin (𝓞 K) K k)), mul_mem hmK hmemu, ?_, ?_, ?_, ?_⟩
    · rw [map_mul, hma, glArch_atPlace, one_mul]
    · intro v hv
      rw [map_mul, map_mul]
      rcases Finset.mem_insert.1 hv with rfl | hvT
      · rw [hmoff v hu, finComponent_atPlace_self, one_mul]
      · have hvu : v ≠ u := fun h => hu (h ▸ hvT)
        rw [hmon v hvT, finComponent_atPlace_of_ne _ _ hvu, mul_one]
    · intro v hv
      have hvu : v ≠ u := fun h => hv (h ▸ Finset.mem_insert_self u T)
      have hvT : v ∉ T := fun h => hv (Finset.mem_insert_of_mem h)
      rw [map_mul, map_mul, hmoff v hvT, finComponent_atPlace_of_ne _ _ hvu, one_mul]
    · intro g
      rw [← mul_assoc, ← hku, ← placeEmbed_eq_atPlace, hsph u huS ku (g * m), hmfix g]

theorem apply_mul_eq_of_mem_maximalCompactAway (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (hφ : IsKfSmooth K φ)
    (hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K))
      (g : AdelicGL2 (𝓞 K) K), φ (g * UnramifiedWhittaker.placeEmbed K v
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) :
    ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g := by
  classical
  obtain ⟨S₀, hS₀⟩ := exists_fixing_away φ hφ
  intro k hk g
  obtain ⟨hkK, hka, hkS⟩ := mem_maximalCompactAway_iff.mp hk
  obtain ⟨m, hmK, hma, hmon, hmoff, hmfix⟩ :=
    exists_truncation_fixing S φ hsph k hkK (S₀ \ S) (fun v hv => (Finset.mem_sdiff.mp hv).2)
  have hkm : k * m⁻¹ ∈ maximalCompactAway K S₀ := by
    rw [mem_maximalCompactAway_iff]
    refine ⟨mul_mem hkK (inv_mem hmK), by rw [map_mul, map_inv, hka, hma, inv_one, mul_one], fun v hv => ?_⟩
    rw [map_mul, map_inv, map_mul, map_inv]
    by_cases hvS : v ∈ S
    · have hvT : v ∉ S₀ \ S := fun h => (Finset.mem_sdiff.mp h).2 hvS
      rw [hkS v hvS, hmoff v hvT, inv_one, mul_one]
    · rw [hmon v (Finset.mem_sdiff.mpr ⟨hv, hvS⟩), mul_inv_cancel]
  calc φ (g * k) = φ (g * (k * m⁻¹) * m) := by rw [mul_assoc, inv_mul_cancel_right]
    _ = φ (g * (k * m⁻¹)) := hmfix _
    _ = φ g := hS₀ _ hkm g

end KfSmoothReduction

theorem AutomorphicForm.apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway
    (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (φ : AdelicGL2 (𝓞 K) K → ℂ) (_hφ : IsKfSmooth K φ)
    (_hsph : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : AdelicGL2 (𝓞 K) K),
        φ (g * UnramifiedWhittaker.placeEmbed K v
          (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = φ g) :
    ∀ k ∈ maximalCompactAway K S, ∀ g : AdelicGL2 (𝓞 K) K, φ (g * k) = φ g := by
  exact KfSmoothReduction.apply_mul_eq_of_mem_maximalCompactAway K S φ _hφ _hsph

namespace AutomorphicForm
open AutomorphicForm
variable (F : Type) [Field F] [NumberField F]

theorem adelicArchGLIncl_glArch_mul_finEmbed_glFin' (y : AdelicGL2 (𝓞 F) F) :
    adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y) = y := by
  apply Units.ext
  refine AdelicDock.matrix_eq_of_mapMatrix_arch_fin_eq (𝓞 F) F ?_ ?_
  · show ((glArch (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (InfiniteAdeleRing F)) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
        = ((glArch (𝓞 F) F y : GL (Fin 2) (InfiniteAdeleRing F)) : Matrix _ _ _)
    rw [map_mul, glArch_adelicArchGLIncl, AdelicDock.glArch_finEmbed, mul_one]
  · show ((glFin (𝓞 F) F (adelicArchGLIncl F (glArch (𝓞 F) F y) * AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F y)) :
        GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F))
        = ((glFin (𝓞 F) F y : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _)
    rw [map_mul, glFin_adelicArchGLIncl, AdelicDock.glFin_finEmbed, one_mul]

theorem finEmbed_glFin_of_mem {g : AdelicGL2 (𝓞 F) F} (hg : g ∈ finiteAdelicGL2Subgroup F) :
    AdelicDock.finEmbed (𝓞 F) F (glFin (𝓞 F) F g) = g := by
  conv_rhs => rw [← adelicArchGLIncl_glArch_mul_finEmbed_glFin' F g]
  rw [(mem_finiteAdelicGL2Subgroup_iff F g).mp hg, map_one, one_mul]

theorem continuous_finEmbed' : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  refine Units.continuous_iff.mpr ⟨continuous_matrix fun i j => ?_, continuous_matrix fun i j => ?_⟩
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => AdelicDock.finMat (𝓞 F) F g i j
    exact continuous_const.prodMk (Units.continuous_val.matrix_elem i j)
  · show Continuous fun g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) => AdelicDock.finMat (𝓞 F) F ((g⁻¹ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix _ _ _) i j
    exact continuous_const.prodMk (Units.continuous_coe_inv.matrix_elem i j)

theorem exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq_of_isKfSmooth
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) (hψ : IsKfSmooth F ψ) :
    ∃ (U O : Subgroup (AdelicGL2 (𝓞 F) F)), IsCompact (U : Set (AdelicGL2 (𝓞 F) F)) ∧ IsOpen (O : Set (AdelicGL2 (𝓞 F) F)) ∧
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, ψ (g * k) = ψ g := by
  classical

  have hex : ∃ K : Subgroup ↥(finiteAdelicGL2Subgroup F), IsCompact (K : Set ↥(finiteAdelicGL2Subgroup F)) ∧ IsOpen (K : Set ↥(finiteAdelicGL2Subgroup F)) := by
    refine ⟨(levelOne (𝓞 F) F ⊤).comap (finiteAdelicGL2Subgroup F).subtype, ?_, ?_⟩
    · refine Topology.IsInducing.subtypeVal.isCompact_iff.mpr ?_
      have : ((↑) : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) '' ((levelOne (𝓞 F) F ⊤).comap (finiteAdelicGL2Subgroup F).subtype : Set ↥(finiteAdelicGL2Subgroup F))
          = ((levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := by
        ext g
        simp only [Set.mem_image, SetLike.mem_coe, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_inf]
        constructor
        · rintro ⟨k, hk, rfl⟩; exact ⟨hk, k.2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨g, h2⟩, h1, rfl⟩
      exact Eq.mpr (congrArg IsCompact this)
        (AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup F ⊤)
    · exact (isOpen_levelOne (𝓞 F) F (N := ⊤) (by simp)).preimage continuous_subtype_val
  obtain ⟨K', hK'c, hK'o, hfix⟩ :=
    (FLT.SmoothVectors.isSmoothVector_iff_exists_isCompact_isOpen_subgroup hex).mp hψ

  let e : ↥(finiteAdelicGL2Subgroup F) ≃ₜ GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    { toFun := fun k => glFin (𝓞 F) F k
      invFun := fun b => ⟨AdelicDock.finEmbed (𝓞 F) F b,
        (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F b)⟩
      left_inv := fun k => Subtype.ext (finEmbed_glFin_of_mem F k.2)
      right_inv := fun b => AdelicDock.glFin_finEmbed (𝓞 F) F b
      continuous_toFun := (continuous_glFin (𝓞 F) F).comp continuous_subtype_val
      continuous_invFun := (continuous_finEmbed' F).subtype_mk _ }

  set K'' : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) := K'.map ((glFin (𝓞 F) F).comp (finiteAdelicGL2Subgroup F).subtype) with hK''
  have hK''o : IsOpen (K'' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
    have : (K'' : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) = e '' (K' : Set ↥(finiteAdelicGL2Subgroup F)) := by
      ext b; simp [hK'', e]
    rw [this]; exact e.isOpenMap _ hK'o
  set O : Subgroup (AdelicGL2 (𝓞 F) F) := K''.comap (glFin (𝓞 F) F) with hO
  have hOo : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)) := hK''o.preimage (continuous_glFin (𝓞 F) F)
  have hUset : ((O ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) = ((↑) : ↥(finiteAdelicGL2Subgroup F) → AdelicGL2 (𝓞 F) F) '' (K' : Set ↥(finiteAdelicGL2Subgroup F)) := by
    ext g
    simp only [SetLike.mem_coe, Subgroup.mem_inf, Set.mem_image]
    constructor
    · rintro ⟨hgO, hgK⟩
      obtain ⟨k', hk', hk'g⟩ := Subgroup.mem_map.mp (Subgroup.mem_comap.mp hgO)
      refine ⟨k', hk', ?_⟩
      have h1 : glFin (𝓞 F) F (k' : AdelicGL2 (𝓞 F) F) = glFin (𝓞 F) F g := hk'g
      rw [← finEmbed_glFin_of_mem F k'.2, h1, finEmbed_glFin_of_mem F hgK]
    · rintro ⟨k', hk', rfl⟩
      exact ⟨Subgroup.mem_comap.mpr (Subgroup.mem_map.mpr ⟨k', hk', rfl⟩), k'.2⟩
  refine ⟨O ⊓ finiteAdelicGL2Subgroup F, O, ?_, hOo, rfl, ?_⟩
  · rw [hUset]; exact hK'c.image continuous_subtype_val
  · intro g k hk
    have hk' : k ∈ ((O ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) : Set (AdelicGL2 (𝓞 F) F)) := hk
    rw [hUset] at hk'
    obtain ⟨k', hk'K, rfl⟩ := hk'
    have := hfix k' hk'K
    exact congrArg (fun f : FLT.SmoothVectors.RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ =>
      FLT.SmoothVectors.RightTranslationFn.toFun f g) this

end AutomorphicForm

theorem AutomorphicForm.IsKfSmooth.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq
    (F : Type) [Field F] [NumberField F] (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : IsKfSmooth F φ) :
    ∃ (U : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
      (O : Subgroup (AdelicGL2 (𝓞 F) F)) (_ : IsOpen (O : Set (AdelicGL2 (𝓞 F) F))),
      U = O ⊓ finiteAdelicGL2Subgroup F ∧ ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, φ (g * k) = φ g := by
  obtain ⟨U, O, hU, hO, hUO, h⟩ := AutomorphicForm.exists_isCompact_isOpen_eq_inf_forall_apply_mul_eq_of_isKfSmooth F φ hφ
  exact ⟨U, hU, O, hO, hUO, h⟩
