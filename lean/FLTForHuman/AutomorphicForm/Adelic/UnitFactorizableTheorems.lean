/-
  The tier-1 façade for WORKORDER-TO4
  (`topics/automorphicForm/WORKORDER-TO4-unit-factorizable-trio.md`): the unit-factorizable trio
  of `AutomorphicForm` ready-shelf nodes.

  Each headline is stated verbatim from its pin `Theorems/` wrapper (pinned `aa2d8b3`) and
  delegates to the corresponding tier-3 kernel
  `AutomorphicForm.UnitFactorizable.Engine.<name>` in
  `FLTForHuman/AutomorphicForm/Adelic/UnitFactorizableEngine.lean`. The engine stays tier 3 and
  unlisted; the triples of wrappers and `S_` files are appended to `SOURCES` last.
-/
import FLTForHuman.AutomorphicForm.Adelic.UnitFactorizableEngine

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

-- pin: exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule (Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean:10)
theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch

-- pin: exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule (Theorems/Thm_AutomorphicForm_exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule.lean:9)
theorem AutomorphicForm.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ (ff : GL (Fin 2) (FiniteAdeleRing (𝓞 L) L) → ℂ) (fa : ℕ → (GL (Fin 2) (InfiniteAdeleRing L) → ℂ)),
      IsFinTestFactor L ff ∧
      (∀ x : AdelicGL2 (𝓞 L) L, ff (glFin (𝓞 L) L x) ≠ 0 → ∃ a k : AdelicGL2 (𝓞 L) L,
        glFin (𝓞 L) L a = 1 ∧
        k ∈ levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L ∧ x = a * k) ∧
      (∀ n, IsArchTestFactor L (fa n)) ∧
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (levelOne (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK
        (fun g => fa n (glArch (𝓞 L) L g) * ff (glFin (𝓞 L) L g))) ∧
      ∀ g, Filter.Tendsto
        (fun n => rightConv L f (fun x => fa n (glArch (𝓞 L) L x) * ff (glFin (𝓞 L) L x)) g)
        Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_finTestFactor_isUnitFactorizableAboveOfType_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch

-- pin: exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule (Theorems/Thm_AutomorphicForm_exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule.lean:10)
theorem AutomorphicForm.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (NK : Ideal (𝓞 K)) (SK : Finset (HeightOneSpectrum (𝓞 K)))
    (hNS : ∀ p : HeightOneSpectrum (𝓞 K), p.asIdeal ∣ NK → p ∈ SK)
    (tys : ArchTypeFamily L) (f : AdelicGL2 (𝓞 L) L → ℂ) (hf : Continuous f)
    (hlev : ∀ g : AdelicGL2 (𝓞 L) L,
      ∀ k ∈ principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L,
        f (g * k) = f g)
    (harch : f ∈ archCutSubmodule L tys) :
    ∃ φ : ℕ → (AdelicGL2 (𝓞 L) L → ℂ),
      (∀ n, IsUnitFactorizableAboveOfType K L tys
        (principalLevel (𝓞 L) L (Ideal.map (algebraMap (𝓞 K) (𝓞 L)) NK) ⊓ finiteAdelicGL2Subgroup L) SK (φ n)) ∧
      ∀ g, Filter.Tendsto (fun n => rightConv L f (φ n) g) Filter.atTop (nhds (f g)) :=
  AutomorphicForm.UnitFactorizable.Engine.exists_isUnitFactorizableAboveOfType_principalLevel_tendsto_rightConv_of_mem_archCutSubmodule
    K L NK SK hNS tys f hf hlev harch
