/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Cusp/SatakeBound.lean` (order AF35B).

  A `spec/` probe, not a library module: it *consumes* the headline in composition, never by
  `#check`.

  The headline is read as a statement about the Satake *pair*, not about the single identity
  `a² ≠ b · (N + 2 + N⁻¹)`:

  * **Zone 1 — twisting scales both roots by `χ v`.** `HeckeEigensystem.twist` sends
    `a v ↦ χ v · a v` and `b v ↦ (χ v)² · b v`. So a Satake pair `(α, β)` of `(a v, b v)` becomes
    the pair `(χ v · α, χ v · β)` of the twisted datum — the polynomial identities
    `α + β = a v`, `α · β = b v` are homogeneous of degree one and two respectively — and the
    headline's strict norm bound `‖α‖, ‖β‖ < √N` rescales to `‖χ v‖ · √N`. This is the direction
    in which the bound "persists with the twisted constants".

  * **Zone 2 — the scale-invariant `‖a‖²`-`‖b‖` form of the bound also survives.** The headline's
    companion inequality `‖a v‖² < ‖b v‖ · (N + 2 + N⁻¹)` (the second conjunct of
    `bounds_of_realization`) is quadratic in the roots on both sides, so twisting multiplies both
    sides by `‖χ v‖²`: the inequality is *twist-invariant*, with no hypothesis on `χ v` beyond
    non-vanishing. That is the form the capstone of SET-AF35 consumes.

  * **Zone 3 — the non-vanishing transfers.** The headline's first conjunct
    (`a v² ≠ b v · (N + 2 + N⁻¹)`) is homogeneous of degree two under `twist`, so it transfers to
    the twisted datum whenever `χ v ≠ 0`.

  The character used for the instantiation is the AF34D one,
  `χ_t v = (|absNorm v| ^ (-t) : ℂ)` — the value of `TwistRpow.nchar F t` on the uniformizer idèle
  (`TwistRpow.coe_nchar_uniformizerIdele`), which is the twist character of
  `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul`.
  So `satakeBound_of_rpow_twist` reads: *the realization the AF34D headline attaches to the
  `|absNorm| ^ (-t)` twist carries Satake roots of modulus `< |absNorm v| ^ (-t) · √|absNorm v|`* —
  exactly the input the weight-one lifting (SET-AF35C) needs at `t = 1`.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/LanglandsTunnellSetAF35BConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.SatakeBound
import FLTForHuman.AutomorphicForm.Adelic.Cusp.RealizationTwist

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open NumberField.TateGlobal
open AutomorphicForm AutomorphicForm.PeterssonHeckeBoundF
open AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open MeasureTheory Matrix

namespace LanglandsTunnellSetAF35BConsumer

variable {F : Type} [Field F] [NumberField F]

/-- The carrier pins the headline is stated at: the level-one family over the centre-cut cover. -/
abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F)) : CarrierPins F :=
  productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
    (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
    (fun v => heckeGen (𝓞 F) F v) (adelicBox F)

/-- The Ramanujan constant of the headline at `v`, `N + 2 + N⁻¹` as a real number. -/
abbrev ramanujanFactor (v : HeightOneSpectrum (𝓞 F)) : ℝ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℝ))⁻¹

/-- The same constant in `ℂ`, as the headline's first conjunct spells it. -/
abbrev ramanujanFactorC (v : HeightOneSpectrum (𝓞 F)) : ℂ :=
  ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) + 2 + (((Ideal.absNorm v.asIdeal : ℕ) : ℂ))⁻¹

theorem ramanujanFactorC_eq (v : HeightOneSpectrum (𝓞 F)) :
    ramanujanFactorC v = ((ramanujanFactor v : ℝ) : ℂ) := by
  simp only [ramanujanFactorC, ramanujanFactor]
  push_cast
  ring

/-- The twist character AF34D uses, `v ↦ (|absNorm v| ^ (-t) : ℂ)`. -/
abbrev rpowChar (t : ℝ) : HeightOneSpectrum (𝓞 F) → ℂ :=
  fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)

/-- **Zone 0.** The headline at one admissible place: the Satake pair exists and both roots are
strictly inside the critical circle. This is the shape every later zone consumes. -/
theorem exists_satake_pair (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    ∃ α β : ℂ, α + β = Θ.a v ∧ α * β = Θ.b v ∧
      ‖α‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
      ‖β‖ < Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
  (LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
    F c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb v hlev hexc).2

/-- **Zone 0.** The headline's first conjunct at one admissible place. -/
theorem sqrt_absNorm_ne_ramanujan (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (v : HeightOneSpectrum (𝓞 F)) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    Θ.a v ^ 2 ≠ Θ.b v * ramanujanFactorC v :=
  (LanglandsTunnell.satake_norm_lt_sqrt_absNorm_of_not_dvd_level_of_not_mem_exceptionalSet
    F c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb v hlev hexc).1

/-- **Zone 1.** Twisting scales both roots of the Satake pair by `χ v`: the pair of `Θ` at `v`
becomes a pair of `Θ.twist χ` at `v`, and the headline's bound rescales to `‖χ v‖ · √N`. -/
theorem exists_satake_pair_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (χ : HeightOneSpectrum (𝓞 F) → ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ v ≠ 0) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    ∃ α β : ℂ, α + β = (Θ.twist χ).a v ∧ α * β = (Θ.twist χ).b v ∧
      ‖α‖ < ‖χ v‖ * Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
      ‖β‖ < ‖χ v‖ * Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  classical
  obtain ⟨α, β, hsum, hprod, hα, hβ⟩ :=
    exists_satake_pair c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb v hlev hexc
  have hχpos : 0 < ‖χ v‖ := norm_pos_iff.mpr hχ
  refine ⟨χ v * α, χ v * β, ?_, ?_, ?_, ?_⟩
  · rw [HeckeEigensystem.twist_a, ← hsum]; ring
  · rw [HeckeEigensystem.twist_b, ← hprod]; ring
  · rw [norm_mul]; exact mul_lt_mul_of_pos_left hα hχpos
  · rw [norm_mul]; exact mul_lt_mul_of_pos_left hβ hχpos

/-- **Zone 2.** The `‖a‖²`-`‖b‖` form of the headline's bound is twist-invariant: both sides are
quadratic in the roots, so twisting multiplies them by `‖χ v‖²`. -/
theorem normSq_lt_ramanujan_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R)
    (χ : HeightOneSpectrum (𝓞 F) → ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ v ≠ 0) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    ‖(Θ.twist χ).a v‖ ^ 2 < ‖(Θ.twist χ).b v‖ * ramanujanFactor v := by
  classical
  have _ := hc
  have _ := hd₁
  have hmain := (bounds_of_realization c u d₁ d₂ T hd hcov Θ R hR v hlev hexc).2
  have hχpos : 0 < ‖χ v‖ := norm_pos_iff.mpr hχ
  have ha : ‖(Θ.twist χ).a v‖ ^ 2 = ‖χ v‖ ^ 2 * ‖Θ.a v‖ ^ 2 := by
    rw [HeckeEigensystem.twist_a, norm_mul, mul_pow]
  have hb : ‖(Θ.twist χ).b v‖ = ‖χ v‖ ^ 2 * ‖Θ.b v‖ := by
    rw [HeckeEigensystem.twist_b, norm_mul, norm_pow, pow_two]
  rw [ha, hb, mul_assoc]
  exact mul_lt_mul_of_pos_left hmain (pow_pos hχpos 2)

/-- **Zone 3.** The headline's non-vanishing is homogeneous of degree two under `twist`, so it
transfers to every non-vanishing twist character. -/
theorem sq_ne_ramanujan_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (χ : HeightOneSpectrum (𝓞 F) → ℂ) (v : HeightOneSpectrum (𝓞 F))
    (hχ : χ v ≠ 0) (hlev : ¬ v.asIdeal ∣ Θ.level) (hexc : v ∉ R.exceptionalSet) :
    (Θ.twist χ).a v ^ 2 ≠ (Θ.twist χ).b v * ramanujanFactorC v ∧
      (∃ t : ℝ, 0 ≤ t ∧ (Θ.twist χ).a v ^ 2 = (t : ℂ) * (Θ.twist χ).b v) := by
  classical
  refine ⟨?_, ?_⟩
  · intro h
    refine sqrt_absNorm_ne_ramanujan c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb v hlev hexc ?_
    have h2 : (χ v * Θ.a v) ^ 2 = (χ v ^ 2 * Θ.b v) * ramanujanFactorC v := h
    have h' : χ v ^ 2 * Θ.a v ^ 2 = χ v ^ 2 * (Θ.b v * ramanujanFactorC v) := by
      rw [show χ v ^ 2 * Θ.a v ^ 2 = (χ v * Θ.a v) ^ 2 by ring, h2, mul_assoc]
    exact mul_left_cancel₀ (pow_ne_zero 2 hχ) h'
  · obtain ⟨t, ht, hat⟩ :=
      (bounds_of_realization c u d₁ d₂ T hd hcov Θ R
        (show IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R from hR)
        v hlev hexc).1
    refine ⟨t, ht, ?_⟩
    rw [HeckeEigensystem.twist_a, HeckeEigensystem.twist_b]
    rw [show (χ v * Θ.a v) ^ 2 = χ v ^ 2 * Θ.a v ^ 2 by ring, hat]
    ring

/-- **The capstone.** For any twist character `χ` that does not vanish at `v`, the twisted
eigensystem inherits the whole headline at `v`: a Satake pair with both roots strictly inside the
scaled circle `‖χ v‖ · √N`, the scale-invariant `‖a‖²`-`‖b‖` bound, and the non-vanishing of
`a² - b · (N + 2 + N⁻¹)`. -/
theorem satakeBound_of_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (χ : HeightOneSpectrum (𝓞 F) → ℂ)
    (hχ : ∀ v : HeightOneSpectrum (𝓞 F), χ v ≠ 0) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ (Θ.twist χ).level → v ∉ R.exceptionalSet →
      (Θ.twist χ).a v ^ 2 ≠ (Θ.twist χ).b v * ramanujanFactorC v ∧
      ‖(Θ.twist χ).a v‖ ^ 2 < ‖(Θ.twist χ).b v‖ * ramanujanFactor v ∧
      ∃ α β : ℂ, α + β = (Θ.twist χ).a v ∧ α * β = (Θ.twist χ).b v ∧
        ‖α‖ < ‖χ v‖ * Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ∧
        ‖β‖ < ‖χ v‖ * Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by
  intro v hlev hexc
  have hlev' : ¬ v.asIdeal ∣ Θ.level := hlev
  obtain ⟨hne, -⟩ :=
    sq_ne_ramanujan_twist c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb χ v (hχ v) hlev' hexc
  exact ⟨hne,
    normSq_lt_ramanujan_twist c u d₁ d₂ T hc hd₁ hd hcov Θ R
      (show IsGenuineCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral R from hR) χ v
      (hχ v) hlev' hexc,
    exists_satake_pair_twist c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb χ v (hχ v) hlev' hexc⟩

/-- The twist character AF34D's headline `…_exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_…`
uses is `TwistRpow.nchar F t` read on the uniformizer idèle; `rpowChar t` is that character
spelled as a family of complex numbers on places. -/
theorem rpowChar_eq_nchar (t : ℝ) :
    (rpowChar (F := F) t)
      = fun v => ((TwistRpow.nchar F t (uniformizerIdele F v) : ℂˣ) : ℂ) := by
  funext v
  exact (TwistRpow.coe_nchar_uniformizerIdele t v).symm

/-- The instantiations's `χ v` is nonzero, by positivity of `|absNorm v| ^ (-t)`. -/
theorem rpowChar_ne_zero (t : ℝ) (v : HeightOneSpectrum (𝓞 F)) :
    rpowChar (F := F) t v ≠ 0 := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hpos : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) :=
    by exact_mod_cast Nat.pos_of_ne_zero h0
  simpa only [rpowChar] using
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos hpos (-t)).ne'

/-- **The capstone at the AF34D twist.** At `χ_t v = (|absNorm v| ^ (-t) : ℂ)` — the character of
the `t`-twist `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul`
— every admissible place carries a Satake pair with both roots of modulus `< |absNorm v| ^ (-t) · √|absNorm v|`,
and the `‖a‖²`-`‖b‖` and `a² ≠ b (N + 2 + N⁻¹)` forms of the bound persist with the twisted
constants. -/
theorem satakeBound_of_rpow_twist (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂))
    (Θ : HeckeEigensystem F ℂ)
    (R : SmoothCuspRealizationAt F (pinsOf c u d₁ d₂ T) Θ.toRawCentral)
    (hR : Continuous R.toFun)
    (hb : ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Θ.level → v ∉ R.exceptionalSet → ‖Θ.b v‖ = 1)
    (t : ℝ) :
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ (Θ.twist (rpowChar t)).level →
      v ∉ R.exceptionalSet →
      (Θ.twist (rpowChar t)).a v ^ 2 ≠ (Θ.twist (rpowChar t)).b v * ramanujanFactorC v ∧
      ‖(Θ.twist (rpowChar t)).a v‖ ^ 2 <
        ‖(Θ.twist (rpowChar t)).b v‖ * ramanujanFactor v ∧
      ∃ α β : ℂ, α + β = (Θ.twist (rpowChar t)).a v ∧ α * β = (Θ.twist (rpowChar t)).b v ∧
        ‖α‖ < (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t)) *
          Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) ∧
        ‖β‖ < (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t)) *
          Real.sqrt ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)) := by
  intro v hlev hexc
  have h := satakeBound_of_twist c u d₁ d₂ T hc hd₁ hd hcov Θ R hR hb (rpowChar t)
    (rpowChar_ne_zero t) v hlev hexc
  obtain ⟨hne, hnorm, α, β, hsum, hprod, hα, hβ⟩ := h
  refine ⟨hne, hnorm, α, β, hsum, hprod, ?_, ?_⟩
  · have : ‖rpowChar (F := F) t v‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-t)) := by
      simp only [rpowChar, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    rwa [this] at hα
  · have : ‖rpowChar (F := F) t v‖ = ((Ideal.absNorm v.asIdeal : ℝ) ^ (-t)) := by
      simp only [rpowChar, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    rwa [this] at hβ

end LanglandsTunnellSetAF35BConsumer
