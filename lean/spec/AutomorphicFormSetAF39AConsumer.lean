/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/RightConvIntegral.lean`.

  The headline is exercised in composition, never by `#check`. Everything below is stated at the
  *concrete* level subgroup `U = levelOne N ⊓ K_f` of the headline's shape `O ⊓ K_f`, with `O =
  levelOne N` and a genuinely constructed probability Haar measure on it:

  * `levelU`/`isCompact_levelU`: the subgroup `levelOne N ⊓ finiteAdelicGL2Subgroup F` is compact,
    because it is the image of the compact finite lattice `finiteLevelOne N` under
    `AdelicDock.finEmbed` (`AutomorphicForm.coe_levelOne_inf_finiteAdelicGL2Subgroup`, the port's
    `FiniteLevelOne` receipt) and `finEmbed` is continuous (`AutomorphicForm.continuous_finEmbed`);
  * `probHaar`: the probability Haar measure `Measure.haarMeasure ⊤` on that compact group — the
    measure the headline quantifies over, so the headline is *applied*, not assumed;
  * `exists_biInvariant_rightConv_levelU`: the headline instantiated at that `U`, `O`, `μ`, with the
    `hUO` slot discharged by `rfl` and `hU`/`hO` by the receipts above;
  * `integral_comp_inv_mul_eq_rightConv_one`: the averaged convolution read at `x = 1` — composing
    the headline's integral identity with the *ported* right-translation law
    `AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply`
    (`AutomorphicForm/Adelic/RightConvolution.lean`), which turns each `rightConv y f (1 * u)` into
    `rightConv y (fun z => f (u⁻¹ * z)) 1`;
  * `biInvariant_at_one`: the `U`-bi-invariance conjunct specialized to `x = 1`, where it reads
    `f' u = f' 1` for every `u ∈ U` — the form the Hecke-coset arguments consume.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF39AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.RightConvIntegral

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped Pointwise

namespace AutomorphicFormSetAF39AConsumer

variable (F : Type) [Field F] [NumberField F]

/-! ### The concrete compact level subgroup `U = levelOne N ⊓ K_f` -/

/-- The headline's `U` at the principal level `N`: `O ⊓ K_f` with `O = levelOne N`. -/
abbrev levelU (N : Ideal (𝓞 F)) : Subgroup (AdelicGL2 (𝓞 F) F) :=
  levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F

/-- `U` is the image of the compact finite lattice `finiteLevelOne N` under `finEmbed`. -/
theorem levelU_coe_eq (N : Ideal (𝓞 F)) :
    (levelU F N : Set (AdelicGL2 (𝓞 F) F)) =
      AdelicDock.finEmbed (𝓞 F) F ''
        (finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  coe_levelOne_inf_finiteAdelicGL2Subgroup F N

/-- Hence `U` is compact — the headline's `hU` at this level. -/
theorem isCompact_levelU (N : Ideal (𝓞 F)) :
    IsCompact (levelU F N : Set (AdelicGL2 (𝓞 F) F)) := by
  rw [levelU_coe_eq F N]
  exact (isCompact_finiteLevelOne (𝓞 F) F N).image (continuous_finEmbed F)

instance compactSpace_levelU (N : Ideal (𝓞 F)) : CompactSpace (levelU F N) :=
  isCompact_iff_compactSpace.mp (isCompact_levelU F N)

instance measurableSpace_levelU (N : Ideal (𝓞 F)) : MeasurableSpace (levelU F N) :=
  borel _

instance borelSpace_levelU (N : Ideal (𝓞 F)) : BorelSpace (levelU F N) :=
  ⟨rfl⟩

/-! ### A probability Haar measure on `U` -/

/-- The probability Haar measure on the compact group `U`. -/
abbrev probHaar (N : Ideal (𝓞 F)) : Measure (levelU F N) :=
  Measure.haarMeasure (⊤ : TopologicalSpace.PositiveCompacts (levelU F N))

instance isHaarMeasure_probHaar (N : Ideal (𝓞 F)) : (probHaar F N).IsHaarMeasure :=
  MeasureTheory.Measure.isHaarMeasure_haarMeasure (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (levelU F N)))

instance isProbabilityMeasure_probHaar (N : Ideal (𝓞 F)) : IsProbabilityMeasure (probHaar F N) :=
  ⟨by
    have h := Measure.haarMeasure_self (G := levelU F N) (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (levelU F N)))
    simpa [probHaar] using h⟩

/-! ### The headline applied at that level -/

/-- The headline at `U = levelOne N ⊓ K_f`, `O = levelOne N` and the probability Haar measure: every
factorizable, arch-`bi`-finite `f` has a `U`-bi-invariant replacement `f'` with the same averaged
right convolution. -/
theorem exists_biInvariant_rightConv_levelU {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y)
    (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelU F N, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelU F N, f' (u * x) = f' x ∧ f' (x * u) = f' x) ∧
      ∀ x : AdelicGL2 (𝓞 F) F,
        ∫ u, rightConv F y f (x * (u : AdelicGL2 (𝓞 F) F)) ∂(probHaar F N) = rightConv F y f' x :=
  exists_integral_rightConv_eq_rightConv F (levelU F N) (isCompact_levelU F N)
    (levelOne (𝓞 F) F N) (isOpen_levelOne (𝓞 F) F hN) rfl (probHaar F N) tys hyc hyU hf hbf

/-- The averaged convolution at `x = 1`, with the average pushed onto the *test function* by the
ported right-translation law: the headline's `x`-identity composed with
`rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` reads
`∫ u, rightConv y (f ∘ (u⁻¹ * ·)) 1 ∂μ = rightConv y f' 1`. -/
theorem integral_comp_inv_mul_eq_rightConv_one {N : Ideal (𝓞 F)} (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F) {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y)
    (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelU F N, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      (∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelU F N, f' (u * x) = f' x ∧ f' (x * u) = f' x) ∧
      (∫ u : levelU F N,
          rightConv F y (fun z => f ((u : AdelicGL2 (𝓞 F) F)⁻¹ * z)) 1 ∂(probHaar F N)) =
        rightConv F y f' 1 := by
  obtain ⟨f', h1, h2, hv, hx⟩ := exists_biInvariant_rightConv_levelU F hN tys hyc hyU hf hbf
  refine ⟨f', h1, h2, hv, ?_⟩
  rw [← hx 1]
  refine integral_congr_ae (ae_of_all _ fun u => ?_)
  exact (rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply F y f 1 u).symm

/-- The `U`-bi-invariance conjunct at `x = 1`: the replacement `f'` is constant along `U` at the
identity, `f' u = f' 1` — the form the Hecke coset system reads it in. -/
theorem biInvariant_at_one {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) (tys : ArchTypeFamily F)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y)
    (hyU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ levelU F N, y (x * u) = y x)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      ∀ u ∈ levelU F N, f' (u : AdelicGL2 (𝓞 F) F) = f' 1 := by
  obtain ⟨f', h1, h2, hv, -⟩ := exists_biInvariant_rightConv_levelU F hN tys hyc hyU hf hbf
  exact ⟨f', h1, h2, fun u hu => by
    have h := (hv 1 u hu).1
    rwa [mul_one] at h⟩

end AutomorphicFormSetAF39AConsumer
