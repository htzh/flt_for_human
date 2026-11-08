/-
  SET-AF19C consumer: the idèle norm at trivial finite part, read on a concrete idèle.

  **Zone 1 — `r = 1`, then the landed uniformizer row.** Row 2
  (`exists_ideleNorm_eq_and_snd_eq_one`) hands out an idèle `z` with trivial finite part and
  `ideleNorm K z = 1`; row 1 (`ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`)
  reads that norm as the archimedean product `∏ w, ‖z.1 w‖ ^ w.mult`, because the finite
  `finprod` collapses at `.2 = 1`. Chained, the two rows say the archimedean product of *that*
  idèle is `1` — the normalisation exists with no side condition, which is what the `diagOne`
  family consumes. The second theorem is the same chain at a general `r`, pushed through the
  multiplicativity of the norm (`ideleNorm_mul`) and the landed
  `ideleNorm_uniformizerIdele`: the archimedean product stays `r` while the single finite
  factor `|absNorm v|⁻¹` moves the norm to `r / |absNorm v|` — i.e. the two landed values of
  the previous headlines and the two new ones are the same product formula read at `.2 = 1`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.IdeleNormValues

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField NumberField.TateGlobal AutomorphicForm

namespace NumberField.TateGlobal
namespace SetAF19C

/-- **Zone 1a.** At `r = 1`: an idèle with trivial finite part whose norm is `1`, *and* whose
archimedean product is `1` — row 2's witness read through row 1. -/
theorem consumer_norm_one_and_arch_product
    (K : Type) [Field K] [NumberField K] :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧ ideleNorm K z = 1 ∧
      (∏ w : InfinitePlace K, ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult) = 1 := by
  obtain ⟨z, hz2, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one K 1 one_pos
  refine ⟨z, hz2, hz, ?_⟩
  rw [← ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K z hz2, hz]

/-- **Zone 1b.** At a general `r`, composed with the landed `ideleNorm_uniformizerIdele`: the same
row 2 witness has archimedean product `r`, and multiplying it by the uniformizer idèle at `v`
multiplies the norm by the single non-trivial finite factor `|absNorm v|⁻¹`
(`ideleNorm_mul` + `ideleNorm_uniformizerIdele`), leaving the archimedean side untouched. -/
theorem consumer_norm_mul_uniformizer
    (K : Type) [Field K] [NumberField K] (r : ℝ) (hr : 0 < r) (v : HeightOneSpectrum (𝓞 K)) :
    ∃ z : (AdeleRing (𝓞 K) K)ˣ, ((z : AdeleRing (𝓞 K) K)).2 = 1 ∧
      (∏ w : InfinitePlace K, ‖((z : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult) = r ∧
      ideleNorm K (z * uniformizerIdele K v) = r * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ)⁻¹ := by
  obtain ⟨z, hz2, hz⟩ := exists_ideleNorm_eq_and_snd_eq_one K r hr
  refine ⟨z, hz2, ?_, ?_⟩
  · rw [← ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one K z hz2, hz]
  · rw [ideleNorm_mul, hz, ideleNorm_uniformizerIdele]

end SetAF19C
end NumberField.TateGlobal
