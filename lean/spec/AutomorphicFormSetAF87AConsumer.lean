/-
  SET-AF87A consumer: the level-spherical approximate identity, read pointwise.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelSphericalLimit.lean` carries
  `AutomorphicForm.exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional{,_of_isCompact}`:
  for a finite-dimensional, uniformly continuous space `Y` invariant under a level subgroup and inside an
  archimedean cut, there is a sequence `f` of flat, level-spherical, factorizable test functions whose right
  convolutions converge pointwise to the identity on `Y`.

  **The readings.** Both rows quantify `∀ y ∈ Y, ∀ g`; the form a call site uses is the *single point*
  one. The two zones below are exactly that: at a fixed `y ∈ Y` and a fixed `g`, the sequence's convolution
  tends to `y g` — once for the level `levelOne N ⊓ finiteAdelicGL2Subgroup`, once for a level written as
  `U = O ⊓ finiteAdelicGL2Subgroup`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF87AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelSphericalLimit

set_option autoImplicit false

noncomputable section

open Filter Topology
open NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm
open AutomorphicForm.CuspidalSpectrum
open scoped Classical ENNReal NNReal ComplexConjugate InnerProductSpace BigOperators

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace AutomorphicFormSetAF87AConsumer

/-- **Zone 1 (finite level).** At one point: for a finite-dimensional uniformly continuous space `Y`
invariant under `levelOne N ⊓ finiteAdelicGL2Subgroup` and inside `archCutSubmodule tys`, there is a
sequence of flat level-spherical factorizable test functions whose right convolutions converge to the
identity at every `y ∈ Y` and every `g`. -/
theorem exists_flat_levelSpherical_tendsto_rightConv_at
    (F : Type) [Field F] [NumberField F] (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (tys : ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F,
      y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (y : AdelicGL2 (𝓞 F) F → ℂ) (hy : y ∈ Y) (g : AdelicGL2 (𝓞 F) F) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧
        IsLevelSphericalOfType F tys (levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (f n) ∧
        flat F σ (f n) = f n) ∧
      Tendsto (fun n => rightConv F y (f n) g) atTop (nhds (y g)) := by
  obtain ⟨f, hf, hlim⟩ :=
    exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional F N hN tys σ Y hY hYc hYU hYt
  exact ⟨f, hf, hlim y hy g⟩

/-- **Zone 2 (compact level).** The same at a level written as `U = O ⊓ finiteAdelicGL2Subgroup` with `U`
compact and `O` open. -/
theorem exists_flat_levelSpherical_tendsto_rightConv_at_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (tys : ArchTypeFamily F) (σ : ℝ)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) (hY : FiniteDimensional ℂ ↥Y)
    (hYc : ∀ y ∈ Y, Continuous y)
    (hYU : ∀ y ∈ Y, ∀ g : AdelicGL2 (𝓞 F) F, ∀ k ∈ U, y (g * k) = y g)
    (hYt : Y ≤ archCutSubmodule F tys)
    (y : AdelicGL2 (𝓞 F) F → ℂ) (hy : y ∈ Y) (g : AdelicGL2 (𝓞 F) F) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ n, IsFactorizableTestFn F (f n) ∧ IsLevelSphericalOfType F tys U (f n) ∧ flat F σ (f n) = f n) ∧
      Tendsto (fun n => rightConv F y (f n) g) atTop (nhds (y g)) := by
  obtain ⟨f, hf, hlim⟩ :=
    exists_isLevelSphericalOfType_flat_tendsto_rightConv_of_finiteDimensional_of_isCompact
      F U hU O hO hUO tys σ Y hY hYc hYU hYt
  exact ⟨f, hf, hlim y hy g⟩

end AutomorphicFormSetAF87AConsumer
