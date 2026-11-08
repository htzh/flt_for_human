/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelOneObstruction.lean`.

  A `spec/` probe, not a library module: it *consumes* the general headline (the level-one Hecke
  obstruction) in composition, never by `#check` and never by restating it.

  * **Zone 1 — the headline is uniform in the domain.** The general headline quantifies over an
    arbitrary `D : Set (AdelicGL2 (𝓞 F) F)`; instantiating it at the class-representative Siegel set
    `classRepSiegelSet F c u d₁ d₂` gives the statement at every `productionPinsGeneralOf` parameter
    tuple, not only at the production choice `(1/2) 1 (1/2) 2`. Since `productionPinsGeneral F` *is*
    `productionPinsGeneralOf F (1/2) 1 (1/2) 2` by definitional unfolding (the pin's
    `productionPinsGeneral_D` is a `rfl` lemma), the `K = ℚ` row of the module is the `(1/2) 1 (1/2) 2`
    instance of this zone (Zone 4).

  * **Zone 2 — the obstruction read constructively.** `¬ ∃ c, ∀ g` is `∀ c, ∃ g, ¬`: for every candidate
    eigenvalue the eigen-relation fails at *some* `g`. This is the form a contradiction argument (e.g.
    the Satake/`a² = b` comparison) wants, and it is where `R.exists_ne_zero` is no longer needed.

  * **Zone 3 — the level dichotomy.** The contrapositive of the headline: a genuine realization can be a
    *pointwise* Hecke eigenfunction at `v` only when `v` divides the level. Composing that with
    `SmoothCuspRealizationAt.hecke_eigen` — which furnishes an eigen-relation at every place outside
    `R.exceptionalSet` — gives the dichotomy `v ∈ R.exceptionalSet ∨ v.asIdeal ∣ Ψ.level`.
    The composition needs the eigen-relation in the *pointwise* form `∀ g, φ (g * gen v) = c * φ g`; the
    port's `hecke_eigen` states the **coset-sum** form `heckeCosetSum reps φ g = c * φ g` over an
    `IsHeckeCosetSystem`, whose representatives range over the right-`U` orbits of the double coset
    `U gen v U` (`absNorm + 1` of them), so the bridge is carried as the explicit hypothesis
    `hpointwise` of `mem_exceptionalSet_or_dvd_level` rather than silently assumed.

  * **Zone 4 — the `ℚ` row.** The module derives the `K = ℚ` headline from the general one at
    `D = classRepSiegelSet ℚ (1/2) 1 (1/2) 2`; Zone 1 recovers exactly that instance, which is what the
    derivation's `rfl`-unfolding of `productionPinsGeneral` is worth.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF34CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelOneObstruction

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm MeasureTheory Matrix

namespace AutomorphicFormSetAF34CConsumer

variable {F : Type} [Field F] [NumberField F]

/-- The pins the general headline is stated at, at an arbitrary domain `D`. -/
abbrev pinsOf (D : Set (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

/-- **Zone 1.** The obstruction at an arbitrary class-representative Siegel set: the headline is
uniform in `D`, so it lands on every `productionPinsGeneralOf` parameter tuple. -/
theorem not_exists_forall_apply_mul_heckeGen_eq_classRepSiegelSet
    (c u d₁ d₂ : ℝ) (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf (classRepSiegelSet F c u d₁ d₂)) Ψ)
    (hR : IsGenuineCuspRealizationAt F (pinsOf (classRepSiegelSet F c u d₁ d₂)) Ψ R)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ Ψ.level) :
    ¬ ∃ c : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (g * heckeGen (𝓞 F) F v) = c * R.toFun g :=
  SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt F
    (classRepSiegelSet F c u d₁ d₂) Ψ R hR v hv

/-- **Zone 2.** The obstruction in the `∀ c, ∃ g` reading: no candidate eigenvalue survives at every
point of the group. -/
theorem exists_apply_mul_heckeGen_ne
    (D : Set (AdelicGL2 (𝓞 F) F)) (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf (F := F) D) Ψ)
    (hR : IsGenuineCuspRealizationAt F (pinsOf (F := F) D) Ψ R)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ¬ v.asIdeal ∣ Ψ.level) (c : ℂ) :
    ∃ g : AdelicGL2 (𝓞 F) F, R.toFun (g * heckeGen (𝓞 F) F v) ≠ c * R.toFun g := by
  have h := SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
    F D Ψ R hR v hv
  push Not at h
  exact h c

/-- **Zone 3 (contrapositive).** A genuine realization is a pointwise Hecke eigenfunction for
`heckeGen v` only at a place `v` dividing the level. -/
theorem dvd_level_of_forall_apply_mul_heckeGen_eq
    (D : Set (AdelicGL2 (𝓞 F) F)) (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf (F := F) D) Ψ)
    (hR : IsGenuineCuspRealizationAt F (pinsOf (F := F) D) Ψ R)
    {v : HeightOneSpectrum (𝓞 F)} {c : ℂ}
    (hgen : ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (g * heckeGen (𝓞 F) F v) = c * R.toFun g) :
    v.asIdeal ∣ Ψ.level := by
  by_contra hv
  exact SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
    F D Ψ R hR v hv ⟨c, hgen⟩

/-- **Zone 3 (dichotomy).** Reading `hecke_eigen` pointwise — `hpointwise`, the bridge this zone
isolates — every place is either exceptional or divides the level. -/
theorem mem_exceptionalSet_or_dvd_level
    (D : Set (AdelicGL2 (𝓞 F) F)) (Ψ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf (F := F) D) Ψ)
    (hR : IsGenuineCuspRealizationAt F (pinsOf (F := F) D) Ψ R)
    (hpointwise : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ R.exceptionalSet →
      ∃ c : ℂ, ∀ g : AdelicGL2 (𝓞 F) F,
        R.toFun (g * heckeGen (𝓞 F) F v) = c * R.toFun g)
    (v : HeightOneSpectrum (𝓞 F)) : v ∈ R.exceptionalSet ∨ v.asIdeal ∣ Ψ.level := by
  by_cases hv : v ∈ R.exceptionalSet
  · exact Or.inl hv
  · obtain ⟨c, hc⟩ := hpointwise v hv
    exact Or.inr (dvd_level_of_forall_apply_mul_heckeGen_eq D Ψ R hR hc)

/-- **Zone 4.** The `K = ℚ` row: the module's derivation is the `(1/2) 1 (1/2) 2` instance of Zone 1,
which is exactly the definitional unfolding of `productionPinsGeneral` the derivation spends. -/
theorem not_exists_forall_apply_mul_heckeGen_eq_rat_of_continuous
    (Ψ : HeckeEigensystem ℚ ℂ)
    (R : SmoothCuspRealizationAt ℚ (pinsOf (F := ℚ) (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)) Ψ)
    (hR : IsGenuineCuspRealizationAt ℚ
      (pinsOf (F := ℚ) (classRepSiegelSet ℚ (1/2 : ℝ) 1 (1/2) 2)) Ψ R)
    (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ¬ v.asIdeal ∣ Ψ.level) :
    ¬ ∃ c : ℂ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ, R.toFun (g * heckeGen (𝓞 ℚ) ℚ v) = c * R.toFun g :=
  not_exists_forall_apply_mul_heckeGen_eq_classRepSiegelSet (F := ℚ) (1/2) 1 (1/2) 2 Ψ R hR v hv

end AutomorphicFormSetAF34CConsumer
