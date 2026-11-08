/-
  Smooth vectors have a finite orbit under a compact, and the level subgroups are compact.

  Two rows, one theme — the compactness that the `K_f`-smooth and level-invariant carriers are
  built on:

  * `IsKfSmooth.finite_smul_image_of_isCompact`: a `K_f`-smooth function's right translates by a
    **compact** set of the finite adelic maximal compact subgroup form a finite set — the smooth
    vector's stabiliser is open, so a compact set is covered by finitely many of its translates;
  * `isCompact_levelOne_inf_finiteAdelicGL2Subgroup`: `levelOne ⊓ finiteAdelicGL2Subgroup` is
    **compact** in `GL₂(𝔸_K)` — the level-one congruence subgroup inside the maximal compact is the
    image of the compact `finiteLevelOne` under the closed embedding `AdelicDock.finEmbed`.

  The first is stated generically (`IsSmoothVector.finite_smul_image_of_isCompact`) and then
  specialised, as the pin does; the specialisation is what the `IsLevelSphericalOfType` and
  isotypic-carrier blocks consume (it readies `apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_…`
  260 and, with the lift of right convolution, `exists_commute_lift_cosetSum_…` 665 and
  `exists_forall_rightTranslate_eq_sum_mul_of_isArchKFinite_of_isKfSmooth` 552).

  Transcribed from the pin's two `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  40 + 62 lines). The level-compactness proof needs `AdelicDock`'s `finEmbed`/`glArch_finEmbed`/
  `glFin_finEmbed` API and `isCompact_finiteLevelOne`; the smooth-vector proof is
  `IsCompact.elim_finite_subcover_image` at the stabiliser.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isCompact_levelOne_inf_finiteAdelicGL2Subgroup.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.RepTheory.SmoothVectors

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm FLT.SmoothVectors
open scoped ENNReal Pointwise

noncomputable section

namespace FLT.SmoothVectors

/-- A smooth vector's orbit under a compact set of the group is finite: the stabiliser is open,
so the compact set is covered by finitely many of its translates.

Transcribed from the pin's `Rho7aSol.IsSmoothVector.finite_smul_image_of_isCompact`
(`P2M/Sol/S_AutomorphicForm_IsKfSmooth_finite_smul_image_of_isCompact.lean:10-30`); only the
`Rho7aSol` label is dropped. -/
theorem IsSmoothVector.finite_smul_image_of_isCompact {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type*} [MulAction G M] {v : M} (hv : IsSmoothVector G v)
    {K : Set G} (hK : IsCompact K) : Set.Finite ((· • v) '' K) := by
  set U := MulAction.stabilizer G v
  have hUo : IsOpen (U : Set G) := hv

  have hcov : K ⊆ ⋃ k ∈ K, (fun g => k * g) '' (U : Set G) := by
    intro k hk
    simp only [Set.mem_iUnion]
    exact ⟨k, hk, 1, Subgroup.one_mem U, mul_one k⟩
  have hopen : ∀ k ∈ K, IsOpen ((fun g => k * g) '' (U : Set G)) := by
    intro k _
    exact (Homeomorph.mulLeft k).isOpenMap _ hUo
  obtain ⟨t, _htK, htF, htcov⟩ := hK.elim_finite_subcover_image hopen hcov
  refine (htF.image (· • v)).subset (fun w hw => ?_)
  simp only [Set.mem_image] at hw ⊢
  obtain ⟨k, hkK, rfl⟩ := hw
  have hk := htcov hkK
  simp only [Set.mem_iUnion, Set.mem_image] at hk
  obtain ⟨j, hjT, u, huU, hju⟩ := hk
  exact ⟨j, hjT, by rw [← hju, mul_smul, MulAction.mem_stabilizer_iff.mp huU]⟩

end FLT.SmoothVectors

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-- A `K_f`-smooth function's right translates by a compact set are finite. -/
theorem IsKfSmooth.finite_smul_image_of_isCompact
    {F : Type} [Field F] [NumberField F] {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsKfSmooth F φ) {K : Set ↥(finiteAdelicGL2Subgroup F)} (hK : IsCompact K) :
    Set.Finite ((· • (RightTranslationFn.mk φ :
      RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ)) '' K) :=
  IsSmoothVector.finite_smul_image_of_isCompact hφ hK

section Helpers

variable (F : Type) [Field F] [NumberField F]

/-- `AdelicDock.finEmbed` is continuous. -/
theorem continuous_finEmbed : Continuous (AdelicDock.finEmbed (𝓞 F) F) := by
  have hval : ∀ {φ : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) →
      Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)},
      Continuous φ → Continuous fun g => AdelicDock.finMat (𝓞 F) F (φ g) := by
    intro φ hφ
    refine continuous_matrix fun i j => ?_
    show Continuous fun g => (((1 : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j, φ g i j) :
      AdeleRing (𝓞 F) F)
    exact continuous_const.prodMk (hφ.matrix_elem i j)
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact hval Units.continuous_val
  · exact hval Units.continuous_coe_inv

/-- The two projections `glArch`/`glFin` jointly separate points of `GL₂(𝔸_F)`. -/
theorem eq_of_glArch_eq_of_glFin_eq {x y : AdelicGL2 (𝓞 F) F}
    (h₁ : glArch (𝓞 F) F x = glArch (𝓞 F) F y) (h₂ : glFin (𝓞 F) F x = glFin (𝓞 F) F y) :
    x = y := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  have h₁' := congrArg
    (fun m : GL (Fin 2) (InfiniteAdeleRing F) =>
      (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) h₁
  have h₂' := congrArg
    (fun m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) =>
      (m : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) i j) h₂
  exact Prod.ext h₁' h₂'

/-- `levelOne ⊓ finiteAdelicGL2Subgroup` is the image of `finiteLevelOne` under `finEmbed`. -/
theorem coe_levelOne_inf_finiteAdelicGL2Subgroup (N : Ideal (𝓞 F)) :
    ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) =
      AdelicDock.finEmbed (𝓞 F) F ''
        (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  ext g
  simp only [Subgroup.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_image]
  constructor
  · rintro ⟨hl, hf⟩
    refine ⟨glFin (𝓞 F) F g, mem_levelOne_iff.mp hl, ?_⟩
    refine eq_of_glArch_eq_of_glFin_eq F ?_ ?_
    · rw [AdelicDock.glArch_finEmbed, (mem_finiteAdelicGL2Subgroup_iff F g).mp hf]
    · rw [AdelicDock.glFin_finEmbed]
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(AdelicDock.finEmbed_mem_levelOne_iff (𝓞 F) F k).mpr hk,
      (mem_finiteAdelicGL2Subgroup_iff F _).mpr (AdelicDock.glArch_finEmbed (𝓞 F) F k)⟩

end Helpers

/-- The level-one congruence subgroup inside the finite maximal compact is compact. -/
theorem isCompact_levelOne_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) :
    IsCompact ((levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F : Subgroup (AdelicGL2 (𝓞 F) F)) :
      Set (AdelicGL2 (𝓞 F) F)) := by
  rw [coe_levelOne_inf_finiteAdelicGL2Subgroup]
  exact (isCompact_finiteLevelOne (𝓞 F) F N).image (continuous_finEmbed F)

end AutomorphicForm

end
