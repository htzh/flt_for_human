/-
  The finite-support norm product is summable for `t > 1`.

  `∑' k : HeightOneSpectrum →₀ ℕ, (∏_v absNorm(v)^{k v} : ℝ≥0∞)^{-t} < ⊤` — the geometric
  series that bounds every ideal-count sum. The development is the `Fin` block of
  `FLTForHuman/AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean`
  (`normProd`, `idealOf`, `absNorm_idealOf`, `idealCount`, `zetaTerm`, `summable_zetaTerm`,
  `tsum_fibre_card_mul`, `card_fibre_le`, `tsum_normProd_rpow_neg_lt_top`), transcribed there
  from the pin's `bruhatTransversal` file; this module states the pin's separate leaf at the
  `Theorems/` wrapper and applies it.

  The statement's namespace is `NumberField` (it is a counting statement, not an automorphic
  one), but the module is on the `AutomorphicForm` side because the engine is: the import
  direction is `AutomorphicForm → NumberTheory`, never back.

  Transcribed from
  `P2M/Sol/S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.lean:177`
  (pinned `aa2d8b3`), where the statement is the root-level `solution`; the pin's
  `import Mathlib` and `set_option Elab.async false` are not carried.

  spec-pin: Theorems/Thm_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.lean
  spec-pin: P2M/Sol/S_NumberField_tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top.lean   -- comparable copy
-/
import FLTForHuman.AutomorphicForm.Adelic.WeylIntegrable.LatticeEstimates

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped ENNReal

namespace NumberField

theorem tsum_prod_absNorm_heightOneSpectrum_pow_rpow_neg_lt_top
    (F : Type) [Field F] [NumberField F] {t : ℝ} (ht : 1 < t) :
    ∑' k : HeightOneSpectrum (𝓞 F) →₀ ℕ,
        (((k.prod fun v n => Ideal.absNorm v.asIdeal ^ n : ℕ) : ℝ≥0∞) ^ (-t)) < ⊤ :=
  AutomorphicForm.WeylIntegrable.tsum_normProd_rpow_neg_lt_top F ht

end NumberField
