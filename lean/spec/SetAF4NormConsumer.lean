/-
  Cross-module wire test for SET-AF4 (the norm side of the adèle ring).

  A `spec/` probe, not a library module. Two zones:

  * zone A composes the three norm *values*: the unit-idèle evaluation (N1), the uniformizer
    idèle (N2) and the determinant (N3) are multiplied together through `ideleNorm_mul`, so the
    probe fails if any of the three modules is deleted;
  * zone B composes the two norm *estimates*: the height's continuity (N4) and the
    finite-support norm product's summability (N5), read through the height's own continuity
    (`continuous_archHeight`) and through `ENNReal.mul_lt_top`.

  Every zone is a real composition — no `#check`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues
import FLTForHuman.AutomorphicForm.Adelic.IdeleNormDetGlue
import FLTForHuman.NumberTheory.AdelicHeight
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.NormProdSum

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.AdelicHeight NumberField.AdeleRing
open NumberField.AdelicLevel NumberField.TateGlobal NumberField.AdelicVolume
open AutomorphicForm AutomorphicForm.WindowedSiegel
open scoped ENNReal

namespace SetAF4NormConsumer

variable {F : Type} [Field F] [NumberField F]

/-- Zone A: the unit-idèle value composed with the uniformizer value. -/
example (u : (AdeleRing (𝓞 F) F)ˣ) (v : HeightOneSpectrum (𝓞 F))
    (harch : (u : AdeleRing (𝓞 F) F).1 = 1)
    (hfin : finitePartUnits (𝓞 F) F u ∈
      IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 F) F) :
    ideleNorm F (u * uniformizerIdele F v) = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  rw [ideleNorm_mul,
    NumberField.TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles
      F u harch hfin,
    one_mul, NumberField.TateGlobal.ideleNorm_uniformizerIdele F v]

/-- Zone A: the uniformizer value composed with the determinant value. -/
example (v : HeightOneSpectrum (𝓞 F)) (X : AdelicGL2 (𝓞 F) F)
    (hX : glFin (𝓞 F) F X ∈ finiteIntegralGL2 (𝓞 F) F) :
    ideleNorm F (uniformizerIdele F v * Matrix.GeneralLinearGroup.det X)
      = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹
        * ∏ w : InfinitePlace F, archDetNorm w X ^ w.mult := by
  rw [ideleNorm_mul, NumberField.TateGlobal.ideleNorm_uniformizerIdele F v,
    NumberField.TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult X hX]

/-- Zone B: the height's continuity, read against the archimedean height. -/
example :
    Continuous (fun g : AdelicGL2 (𝓞 F) F => adelicHeight F g + archHeight F (glArch (𝓞 F) F g)) :=
  (continuous_adelicHeight F).add
    ((continuous_archHeight F).comp (continuous_glArch (𝓞 F) F))

/-- Zone B: the norm product's summability, read as a bounded multiplicity. -/
example {t : ℝ} (ht : 1 < t) :
    (∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t))) * 2 < ⊤ :=
  ENNReal.mul_lt_top
    (NumberField.tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top F ht)
    ENNReal.coe_lt_top

end SetAF4NormConsumer
