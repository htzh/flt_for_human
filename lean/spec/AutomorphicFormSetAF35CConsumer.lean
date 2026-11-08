/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Cusp/SatakeConsequence.lean` (order AF35C).

  A `spec/` probe, not a library module: it *consumes* the headline in composition, never by
  `#check`.

  The headline is a *conditional* statement about the pair `(a v, b v)` of the raw-central
  eigensystem `Θ.toRawCentral` of a genuine smooth cusp realization `R` of the level-one family over
  a centre-cut Siegel cover: at every place `v` outside the level `Θ.level` and the exceptional set
  `R.exceptionalSet`, the `θ`-trivial assignment `b v = a v ^ 2` is impossible in the form
  `a v ^ 2 ≠ b v · (N + 2 + N⁻¹)`. The zones below read that in composition:

  * **Zone 1** is the headline at its own pins (`pinsOf`), the shape every later zone consumes.

  * **Zone 2** composes the headline with the level-one obstruction
    `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt`
    (`Cusp/LevelOneObstruction.lean`) at the same place: the place is *simultaneously* not a Hecke
    eigenplace of `R` (no `c` with `R (g · T v) = c · R g`) and not a Satake-trivial place. The two
    conclusions are about the same `R`, `Θ`, `v` and the same two hypotheses, so they hold jointly:
    a weight-one lifting cannot pick up a trivial (θ-like) eigenvalue at such a place.

  * **Zone 3** draws the mathematical content of the headline out of it. If the `a`-eigenvalue
    vanishes at an admissible place, then the trivial assignment `b v = a v ^ 2` fails: the pair
    `(0, 0)` is excluded. This is where the headline is used *strictly*: the instantiation
    `a v = 0`, `b v = a v ^ 2` turns it into `0 ≠ 0 · (N + 2 + N⁻¹)`, and it does so without any
    arithmetic on the modulus — which is exactly why the statement carries the factor
    `N + 2 + N⁻¹` rather than a bare `1`.

  * **Zone 4** observes that the non-vanishing is homogeneous of degree two under
    `HeckeEigensystem.twist` (`a v ↦ χ v · a v`, `b v ↦ (χ v)² · b v`), so it transfers to every
    twist character with `χ v ≠ 0` — the form in which the twisted data of
    `Cusp/RealizationTwist.lean` carry the bound.

  A note on the degenerate place `N = 1`: `Ideal.absNorm v.asIdeal = 1` is impossible for a
  height-one prime (`Ideal.absNorm_eq_one_iff` against `v.isPrime.ne_top`), so the conjunction
  `N = 1` is empty and every zone above is vacuous there — the bound is only about `N ≥ 2`, where
  `N + 2 + N⁻¹ > 1` is honestly a bound.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF35CConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SatakeConsequence
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelOneObstruction

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering

namespace AutomorphicFormSetAF35CConsumer

variable {F : Type} [Field F] [NumberField F]

/-- The carrier pins the headline is stated at: the level-one family over the centre-cut cover. -/
abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

/-- The headline's Ramanujan factor `N + 2 + N⁻¹` in `ℂ`, as its statement spells it. -/
abbrev ramanujanFactorC (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹

/-- **Zone 1.** The headline at one admissible place: the trivial Satake assignment
`b v = a v ^ 2` is excluded, in the shape `a v ^ 2 ≠ b v · (N + 2 + N⁻¹)`. -/
theorem satake_nontrivial (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R)
    (v : HeightOneSpectrum (𝓞 F)) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    Θ.a v ^ 2 ≠ Θ.b v * ramanujanFactorC v :=
  SmoothCuspRealizationAt.a_sq_ne_b_mul_of_not_dvd_level_of_not_mem_exceptionalSet
    F c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlev hexc

/-- **Zone 2.** At an admissible place the realization is neither a Hecke eigenfunction (the
level-one obstruction at `hR`) nor Satake-trivial (the headline): the two conclusions hold of the
same `R`, `Θ`, `v` under the same two hypotheses. -/
theorem not_eigen_and_satake_nontrivial (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R)
    (v : HeightOneSpectrum (𝓞 F)) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    (¬ ∃ cc : ℂ, ∀ g : AdelicGL2 (𝓞 F) F, R.toFun (g * heckeGen (𝓞 F) F v) = cc * R.toFun g) ∧
      Θ.a v ^ 2 ≠ Θ.b v * ramanujanFactorC v :=
  ⟨SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt
      F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂) Θ.toRawCentral R hR v hlev,
    satake_nontrivial c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlev hexc⟩

/-- **Zone 3.** If the `a`-eigenvalue vanishes at an admissible place, the trivial assignment
`b v = a v ^ 2` fails there: the pair `(0, 0)` is excluded. -/
theorem b_ne_a_sq_of_a_eq_zero (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R)
    (v : HeightOneSpectrum (𝓞 F)) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet)
    (ha : Θ.a v = 0) :
    Θ.b v ≠ Θ.a v ^ 2 := by
  intro hb
  refine satake_nontrivial c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlev hexc ?_
  rw [hb, ha]
  ring

/-- **Zone 4.** The non-vanishing is homogeneous of degree two under `HeckeEigensystem.twist`, so
it transfers to every twist character that does not vanish at `v`. -/
theorem sq_ne_ramanujan_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R)
    (χ : HeightOneSpectrum (𝓞 F) → ℂ) (v : HeightOneSpectrum (𝓞 F)) (hχ : χ v ≠ 0)
    (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    (Θ.twist χ).a v ^ 2 ≠ (Θ.twist χ).b v * ramanujanFactorC v := by
  intro h
  refine satake_nontrivial c u d₁ d₂ T hc hd₁ hd hcov Θ R hR v hlev hexc ?_
  have h2 : (χ v * Θ.a v) ^ 2 = (χ v ^ 2 * Θ.b v) * ramanujanFactorC v := h
  have h' : χ v ^ 2 * Θ.a v ^ 2 = χ v ^ 2 * (Θ.b v * ramanujanFactorC v) := by
    rw [show χ v ^ 2 * Θ.a v ^ 2 = (χ v * Θ.a v) ^ 2 by ring, h2, mul_assoc]
  exact mul_left_cancel₀ (pow_ne_zero 2 hχ) h'

end AutomorphicFormSetAF35CConsumer
