/-
  Consumer zone for `FLTForHuman/AutomorphicForm/Adelic/Cusp/RealizationTwist.lean`.

  A `spec/` probe, not a library module: it *consumes* the headline (the existence of the
  idèle-norm-twisted realization) in composition, never by `#check`.

  * **Zone 1 — the `s = -t` bookkeeping.** The construction's character is `TwistRpow.nchar K t`,
  i.e. `x ↦ ‖x‖ ^ t` on the idèle group; on uniformizers `coe_nchar_uniformizerIdele` computes it as
  `|absNorm v| ^ (-t)`. That is exactly the character the headline's twisted eigensystem
  `Θ.twist (v ↦ ‖v‖ ^ (-t))` carries, so `chi_eq_absNorm_rpow_neg` is the bridge between the two
  spellings. Without it the negative exponent in the statement and the positive exponent in the value
  formula look inconsistent.

  * **Zone 2 — nonzero, same exceptional set, and the value formula at `g = 1`.** The headline's
  `R'` is consumed three ways: `SmoothCuspRealizationAt.toFun_ne_zero` turns `exists_ne_zero` into
  `R'.toFun ≠ 0`, the exceptional-set equality is a genuine transport (`R'` loses no place that `R`
  did not lose), and the value formula at `g = 1` collapses to `R'.toFun 1 = R.toFun 1` because
  `det 1 = 1`, `ideleNorm K 1 = 1` (`TwistRpow.ideleNorm_one'`) and `1 ^ t = 1`. So the twist does not
  move the value at the identity, even though it rescales every other one by `‖det g‖ ^ t`.

  * **Zone 3 — the transported spectrum.** The exceptional-set equality read *backwards*
  (`v ∉ R.exceptionalSet ↦ v ∉ R'.exceptionalSet`) makes `R'.hecke_eigen` available exactly where
  `R.hecke_eigen` is, at the twisted eigenvalue `(Θ.twist χ).a v`. This is the direction the
  Satake/`a² = b` comparison uses.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF34DConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.RealizationTwist

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SmoothCusp
open MeasureTheory Matrix

namespace AutomorphicFormSetAF34DConsumer

variable {K : Type} [Field K] [NumberField K]

/-- The pins the headline is stated at. -/
abbrev pinsOf (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) : CarrierPins K :=
  productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
    (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
    (fun v => heckeGen (𝓞 K) K v) (adelicBox K)

/-- The character the headline's twisted eigensystem carries, `v ↦ ‖v‖ ^ (-t)`. -/
abbrev twistChar (t : ℝ) : HeightOneSpectrum (𝓞 K) → ℂ :=
  fun v => (((Ideal.absNorm v.asIdeal : ℝ) ^ (-t) : ℝ) : ℂ)

/-- **Zone 1.** The construction's norm character `TwistRpow.nchar K t` (the positive exponent `t`)
is, on uniformizers, the headline's `v ↦ ‖v‖ ^ (-t)`: the `s = -t` bookkeeping. -/
theorem chi_eq_absNorm_rpow_neg (t : ℝ) :
    (fun v : HeightOneSpectrum (𝓞 K) =>
        ((TwistRpow.nchar K t (uniformizerIdele K v) : ℂˣ) : ℂ))
      = twistChar (K := K) t :=
  funext (TwistRpow.coe_nchar_uniformizerIdele t)

/-- **Zone 2.** The headline's `R'` is nonzero, has `R`'s exceptional set, and takes at `g = 1` the
same value as `R`: the idèle-norm factor is `‖det 1‖ ^ t = 1`. -/
theorem exists_twist_nonzero_exceptionalSet_toFun_one
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T) Θ.toRawCentral R) (t : ℝ) :
    ∃ R' : SmoothCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T)
        (Θ.twist (twistChar (K := K) t)).toRawCentral,
      IsGenuineCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T)
          (Θ.twist (twistChar (K := K) t)).toRawCentral R' ∧
        R'.exceptionalSet = R.exceptionalSet ∧
        R'.toFun ≠ 0 ∧
        R'.toFun 1 = R.toFun 1 := by
  obtain ⟨R', hgen, hset, hval⟩ :=
    SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
      K c u d₁ d₂ T hd₁ Θ R hR t
  refine ⟨R', hgen, hset, SmoothCuspRealizationAt.toFun_ne_zero R', ?_⟩
  rw [hval 1, map_one, TwistRpow.ideleNorm_one', Real.one_rpow, Complex.ofReal_one, one_mul]

/-- **Zone 3.** The exceptional-set equality read backwards makes `R'` a Hecke eigenfunction at the
twisted eigenvalue wherever `R` is one: `v ∉ R.exceptionalSet ↦ v ∉ R'.exceptionalSet`, then
`R'.hecke_eigen`. -/
theorem exists_twist_hecke_eigen_of_notMem_exceptionalSet
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K)) (hd₁ : 0 < d₁)
    (Θ : HeckeEigensystem K ℂ)
    (R : SmoothCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T) Θ.toRawCentral)
    (hR : IsGenuineCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T) Θ.toRawCentral R) (t : ℝ) :
    ∃ R' : SmoothCuspRealizationAt K (pinsOf (K := K) c u d₁ d₂ T)
        (Θ.twist (twistChar (K := K) t)).toRawCentral,
      R'.exceptionalSet = R.exceptionalSet ∧
        (∀ v : HeightOneSpectrum (𝓞 K), v ∉ R.exceptionalSet →
          IsHeckeCosetEigenfunctionAt K ((pinsOf (K := K) c u d₁ d₂ T).U Θ.level)
            (heckeGen (𝓞 K) K v) v R'.toFun ((Θ.twist (twistChar (K := K) t)).a v)) := by
  obtain ⟨R', -, hset, -⟩ :=
    SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul
      K c u d₁ d₂ T hd₁ Θ R hR t
  refine ⟨R', hset, fun v hv => R'.hecke_eigen v ?_⟩
  rw [hset]
  exact hv

end AutomorphicFormSetAF34DConsumer
