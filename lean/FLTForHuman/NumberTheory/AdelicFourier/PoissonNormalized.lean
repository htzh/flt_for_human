/-
Poisson summation for a character with no normalized archimedean part.

`NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one`
(64 pin lines): the pure-tensor Poisson summation of SET-AF110B, *without* the hypothesis that the
archimedean part is `fourierChar ∘ trace` — it holds for any global character, at the cost of normalizing
the Haar measure (`μ (adelicBox) = 1`).

Its two premises are SET-AF110B's `NonzeroTrace` and `PureTensorPoisson`, and neither is above the other, so
the home is a small new module above both.

## The rows

* `NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one` — 64 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one.lean

## Landing (SET-AF111, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** One public declaration, 64 lines of code (the pin's `S_` block is 64 lines and one
  `solution` row, which is the headline here). `check_port`: **1 ok / 0 mismatch / 0 missing / 0 own /
  0 kw**; `port_omissions`: 2 pin publics — 1 declared, 1 folded, 0 MISSING.
* **Substitutions**: none. Both premises are the port's already
  (`NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar` from
  `NonzeroTrace.lean`, imported; `…tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_
  fourierChar_trace` from `PureTensorPoisson.lean`, imported), and the pin's proof ran unchanged but
  for the two drifts below. `Equiv.mulLeft₀` and `AddChar.one_apply` were already reachable from the
  scaffold's import list; that list is the one the scaffold chose and it is unchanged.
* **Drift (proof-level only, none a statement change).** (i) `rw [hψ'_apply, ← ha x]` on the literal
  tuple `(x, 0)` fails in this port: `AdeleRing` is a mathlib `def`, not an `abbrev`, so `rw`'s
  keyed matcher re-checks the tuple against `AdeleRing` at implicit transparency and reports it as
  `InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F`. Written
  `refine (hψ'_apply ((x, 0) : AdeleRing (𝓞 F) F)).trans ?_` — the same idiom `NonzeroTrace.lean`
  uses for this tuple. (ii) The pin's `hψ'_apply`-based `hFI` block is unchanged.
* **Axioms**: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; this module carries no `set_option`): downward
  ladder 40000 / 20000 / 10000 / 5000 / 1000 — **silent at 20000 and 5000, fails at 1000** (`isDefEq`
  at `:51`, inside the `IsGlobalAddChar F ψ'` construction). Module floor (the headline's proof
  `sorry`, statement verbatim): **passes at 1000**, so at the 1000 cap the cost is in the proof, not in
  the types.
-/
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.AdelicFourier.NonzeroTrace
import FLTForHuman.NumberTheory.AdelicFourier.PureTensorPoisson
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import Mathlib.Tactic

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm

theorem NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_measure_adelicBox_eq_one
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : MeasureTheory.Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    (hμB : μ (AdelicBox.adelicBox F) = 1)
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    {f : AdeleRing (𝓞 F) F → ℂ} (hf : f ∈ pureTensorSet F) :
    ∑' ξ : F, f (algebraMap F (AdeleRing (𝓞 F) F) ξ)
      = ∑' ξ : F, fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ) := by
  obtain ⟨a, ha0, ha⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  let ψ' : AddChar (AdeleRing (𝓞 F) F) ℂ :=
    ψ.compAddMonoidHom (AddMonoidHom.mulLeft (algebraMap F (AdeleRing (𝓞 F) F) a))
  have hψ'_apply : ∀ y, ψ' y = ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) := fun y => rfl

  have hψ' : IsGlobalAddChar F ψ' := by
    refine ⟨?_, ?_, ?_⟩
    · intro ξ
      show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * algebraMap F (AdeleRing (𝓞 F) F) ξ) = 1
      rw [← map_mul]
      exact hψ.principalInvariant (a * ξ)
    · show Continuous fun y => ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y)
      exact hψ.continuous.comp (continuous_const.mul continuous_id)
    · intro h1
      apply hψ.nontrivial
      ext z
      have hz := DFunLike.congr_fun h1 (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * z)
      rw [hψ'_apply, ← mul_assoc, ← map_mul, mul_inv_cancel₀ ha0, map_one, one_mul] at hz
      rw [hz, AddChar.one_apply, AddChar.one_apply]

  have hψ'_inf : ∀ x : InfiniteAdeleRing F,
      ψ' (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by
    intro x
    refine (hψ'_apply ((x, 0) : AdeleRing (𝓞 F) F)).trans ?_
    rw [← ha x]
    congr 1
    exact Prod.ext rfl (mul_zero _)

  have hB :=
    NumberField.AdelicFourier.tsum_eq_tsum_fourierIntegral_of_mem_pureTensorSet_of_apply_eq_fourierChar_trace
      F μ hμB hψ' hψ'_inf hf
  rw [hB]

  have hFI : ∀ w, fourierIntegral ψ' μ f w
      = fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) a * w) := by
    intro w
    simp only [fourierIntegral_def, hψ'_apply]
    congr 1 with v
    congr 2
    ring
  simp_rw [hFI, ← map_mul]

  exact (Equiv.mulLeft₀ a ha0).tsum_eq
    (fun ξ => fourierIntegral ψ μ f (algebraMap F (AdeleRing (𝓞 F) F) ξ))

