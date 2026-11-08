/-
  Cross-module wire test for SET-AF22B (smooth vectors under a compact, and the compact level
  subgroup).

  A `spec/` probe, not a library module. **One zone**, over `F = ℚ` at level `1`: it reads the
  compactness of `levelOne ⊓ finiteAdelicGL2Subgroup` from
  `AutomorphicForm.isCompact_levelOne_inf_finiteAdelicGL2Subgroup`, transports it into the finite
  maximal compact `↥(finiteAdelicGL2Subgroup ℚ)` (where the smooth-vector row lives), feeds it to
  `AutomorphicForm.IsKfSmooth.finite_smul_image_of_isCompact` to get a **finite** set of right
  translates of a `K_f`-smooth function, and reads `IsCompact.measure_lt_top` on the same subgroup
  for the Haar measure `adelicGLHaar`.

  The middle conjunct is the composition the work order asks for: the compact set `K` fed to the
  smooth-vector row *is* the level subgroup, so the finiteness claim dies if the level-compactness
  headline, the `Subtype.isCompact_iff` transport or the `IsKfSmooth`/`IsSmoothVector` bridge
  changes. `levelSet` is `Set.univ`'s stand-in: it is the level subgroup as a subset of the finite
  maximal compact, which is exactly the compact set of the compact-group case.

  It imports only the module it composes.
-/
import FLTForHuman.AutomorphicForm.Adelic.LevelCompactness

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel
open AutomorphicForm FLT.SmoothVectors
open scoped ENNReal

noncomputable section

namespace SetAF22BLevelCompactnessConsumer

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-- The level-one congruence subgroup at level `1` over `ℚ`, inside `GL₂(𝔸_ℚ)` — the subgroup the
headline proves compact. -/
def levelSubgroup : Subgroup (AdelicGL2 (𝓞 ℚ) ℚ) :=
  levelOne (𝓞 ℚ) ℚ (1 : Ideal (𝓞 ℚ)) ⊓ finiteAdelicGL2Subgroup ℚ

/-- The same subgroup, seen inside the finite maximal compact `finiteAdelicGL2Subgroup ℚ` — the
compact group a `K_f`-smooth vector is acted on by. -/
def levelSet : Set ↥(finiteAdelicGL2Subgroup ℚ) :=
  {g | (g : AdelicGL2 (𝓞 ℚ) ℚ) ∈ levelSubgroup}

/-- **The compactness read through the subtype.** `levelSet` is compact because its image in
`GL₂(𝔸_ℚ)` is `levelSubgroup`, which is the headline's compact set. -/
theorem levelSet_isCompact : IsCompact levelSet := by
  rw [Subtype.isCompact_iff]
  have h : ((↑) '' levelSet : Set (AdelicGL2 (𝓞 ℚ) ℚ)) =
      (levelSubgroup : Set (AdelicGL2 (𝓞 ℚ) ℚ)) := by
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact hg'
    · intro hg
      exact ⟨⟨g, hg.2⟩, hg, rfl⟩
  rw [h]
  exact isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ (1 : Ideal (𝓞 ℚ))

/-- **The zone.** The level subgroup is compact, the right translates of a `K_f`-smooth function
by it form a finite set, and its Haar measure is finite.

The `IsHaarMeasure` fact is not an instance in the port (`isHaarMeasure_adelicGLHaar` is a
theorem), so the third conjunct is the first one fed to `IsCompact.measure_lt_top` under a local
`have` of that theorem (a `have`, not a `haveI`: the hypothesis is a proposition). -/
theorem levelSubgroup_compact_orbits_finite_measure_lt_top
    (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ) (hφ : IsKfSmooth ℚ φ) :
    IsCompact (levelSubgroup : Set (AdelicGL2 (𝓞 ℚ) ℚ)) ∧
      Set.Finite ((· • (RightTranslationFn.mk φ :
        RightTranslationFn (AdelicGL2 (𝓞 ℚ) ℚ) ℂ)) '' levelSet) ∧
      adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ (levelSubgroup : Set (AdelicGL2 (𝓞 ℚ) ℚ)) < ⊤ := by
  have hμ : (adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 ℚ) ℚ
  exact ⟨isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ (1 : Ideal (𝓞 ℚ)),
    IsKfSmooth.finite_smul_image_of_isCompact hφ levelSet_isCompact,
    (isCompact_levelOne_inf_finiteAdelicGL2Subgroup ℚ (1 : Ideal (𝓞 ℚ))).measure_lt_top⟩

end SetAF22BLevelCompactnessConsumer
