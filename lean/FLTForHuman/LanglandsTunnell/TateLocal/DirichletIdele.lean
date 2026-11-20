/-
  The Dirichlet character read on the idèle class character at an unramified place: the value at the
  uniformizer is `χ (|𝔭|) * |𝔭|⁻¹`.

  spec-pin: P2M/Sol/S_LanglandsTunnell_dirichletIdeleChar_mul_modulus_det_gen.lean

  ## Port deltas

  * The import `FLTForHuman.HeckeCharacter.Dirichlet` named a file that does not exist (FR-0244), so
    this module had no `.olean` and `DirichletCharacter.dirichletIdeleChar` was unusable. Repointed
    at `FLTForHuman.NumberTheory.RatIdele.UnitResidue`, which now carries the pin
    `Definitions/Def_DirichletCharacter_DirichletIdeleChar.lean` (order AF95B). Import and header
    only: the statement below is the pin's, not re-spelled.
  * Added `import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact` and `open
    AutomorphicForm`: the row's statement writes `productionPinsCompact` unqualified (the pin's own
    prelude carries that `open` and imports the definition module), and the scaffold had neither,
    the name having been (wrongly) expected from the deleted import.  Statement-neutral.
  * Added `import FLTForHuman.NumberTheory.AdelicModulus`: the row's proof uses the pin's
    `hprod`, the `distribHaarChar` product formula, which the port states as
    `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` there (the pin
    imports its `Theorems/` wrapper of the same name). Statement-neutral.
  * The row's body is the pin's `solution` (pin `:116`), which applies the pin's own private engine
    `value_at_det_gen_of_prod`; the four private engines of the pin's `P2GProbe.C2prime` block
    (pin `:19`–`:108`, `det_diagOne_eq`, `det_gen_eq_uniformizerIdele`,
    `toNNReal_exp_neg_one_eq_inv`, `absNorm_asIdeal_eq_natGenerator`,
    `coe_distribHaarChar_uniformizerIdele`, `coe_modulusChar_uniformizerIdele`,
    `value_at_det_gen_of_prod`) are transcribed above the row at the same names, `private` as in
    the pin (FR-0242: the checker and `scaffold_audit` skip them). `NumberField.AdeleRing.…` is
    the pin's spelling of the port's `AdeleRing (𝓞 ℚ) ℚ`, kept verbatim.
  * The row stays the last declaration of the module (FR-0239: a row cannot precede the engine it
    applies).
-/
import FLTForHuman.LanglandsTunnell.TateLocalConstantsAt
import FLTForHuman.NumberTheory.RatIdele.UnitResidue
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.NumberTheory.AdelicModulus
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum AutomorphicForm
open NumberField.AdelicLevel RatIdele Rat.HeightOneSpectrum
open scoped NNReal ENNReal Pointwise

namespace LanglandsTunnell

private theorem det_diagOne_eq {A : Type*} [CommRing A] (a : Aˣ) :
    Matrix.GeneralLinearGroup.det (diagOne a) = a := by
  refine Units.ext ?_
  rw [Matrix.GeneralLinearGroup.val_det_apply]
  show Matrix.det (Matrix.diagonal ![(a : A), 1]) = (a : A)
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp

private theorem det_gen_eq_uniformizerIdele (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)
      = Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v)) := by
  rw [productionPinsCompact_gen]
  show Matrix.GeneralLinearGroup.det
      (diagOne (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))))
    = Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))
  exact det_diagOne_eq _

private theorem toNNReal_exp_neg_one_eq_inv {e : ℝ≥0} (he : e ≠ 0) :
    WithZeroMulInt.toNNReal he (WithZero.exp (-1 : ℤ)) = e⁻¹ := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]
  have h1 : WithZero.unzero (WithZero.exp_ne_zero (a := (-1 : ℤ))) = Multiplicative.ofAdd (-1 : ℤ) :=
    WithZero.coe_inj.mp (WithZero.coe_unzero _)
  rw [h1, toAdd_ofAdd, zpow_neg_one]

private theorem absNorm_asIdeal_eq_natGenerator (v : HeightOneSpectrum (𝓞 ℚ)) :
    Ideal.absNorm v.asIdeal = natGenerator v := by
  rw [asIdeal_eq_span_natGenerator v, Ideal.absNorm_span_singleton,
    ← map_natCast (algebraMap ℤ (𝓞 ℚ)) (natGenerator v), Algebra.norm_algebraMap,
    RingOfIntegers.rank, Module.finrank_self, pow_one, Int.natAbs_natCast]

private theorem coe_distribHaarChar_uniformizerIdele
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℝ)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [hprod, Finset.prod_eq_one, one_mul, finprod_eq_single _ v]
  · rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_self, FinitePlace.norm_def,
      valued_uniformizerUnit, toNNReal_exp_neg_one_eq_inv, NNReal.coe_inv, NNReal.coe_natCast]
  · intro w hw
    rw [Units.coe_map, finIncl_apply_snd, localUnit_apply_of_ne (𝓞 ℚ) ℚ v _ hw, norm_one]
  · intro w _
    rw [Units.coe_map, finIncl_apply_fst]
    simp only [show (1 : InfiniteAdeleRing ℚ) w = 1 from rfl, norm_one, one_pow]

private theorem coe_modulusChar_uniformizerIdele
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖)
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    ((((Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
          (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits)
        (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℂˣ) : ℂ)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  show ((MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)
      (Units.map (finIncl (𝓞 ℚ) ℚ) (localUnit (𝓞 ℚ) ℚ v (uniformizerUnit ℚ v))) : ℝ) : ℂ)
    = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹
  rw [coe_distribHaarChar_uniformizerIdele hprod v, Complex.ofReal_inv, Complex.ofReal_natCast]

private theorem value_at_det_gen_of_prod {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)})
    (hprod : ∀ a : (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)ˣ,
      (MeasureTheory.distribHaarChar (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ) a : ℝ)
        = (∏ w : NumberField.InfinitePlace ℚ,
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).1 w‖ ^ w.mult)
          * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
              ‖(a : NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ).2 v‖) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  intro v hv
  have hvn : ¬ natGenerator v ∣ n := fun h =>
    hS v hv (Ideal.dvd_span_singleton.mpr ((natCast_mem_asIdeal_iff v n).mpr h))
  rw [MonoidHom.comp_apply, det_gen_eq_uniformizerIdele v, MonoidHom.mul_apply, Units.val_mul,
    DirichletCharacter.coe_dirichletIdeleChar_finIncl_localUnit_of_valued_exp_neg_one χ hvn
      (uniformizerUnit ℚ v) (valued_uniformizerUnit ℚ v),
    coe_modulusChar_uniformizerIdele hprod v, absNorm_asIdeal_eq_natGenerator v]

theorem dirichletIdeleChar_mul_modulus_det_gen
    {n : ℕ} [NeZero n]
    (χ : DirichletCharacter ℂ n)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → ¬ v.asIdeal ∣ Ideal.span {(n : 𝓞 ℚ)}) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)
        = χ ((Ideal.absNorm v.asIdeal : ℕ) : ZMod n) * ((Ideal.absNorm v.asIdeal : ℕ) : ℂ)⁻¹ := by
  have hprod := NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm ℚ
  exact value_at_det_gen_of_prod χ S hS hprod

end LanglandsTunnell

end
