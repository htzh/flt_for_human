/-
The trace-dual of the integer lattice is the finite part of the character's vanishing set.

`NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual` (85 pin lines): for a
global additive character `ψ` whose archimedean part is `fourierChar ∘ trace` and `ξ : F`, the finite
adelic character `z ↦ ψ (0, ξ z)` is trivial on the integral finite adeles **iff** `ξ` lies in the trace
dual `FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)`.

The proof is the finiteness computation `integralFiniteAdeles ⊆ closure (range (algebraMap F …))`
(`AdelicBox/Measure.lean`) glued to the archimedean trace formula
(`NumberField/StandardAddCharTrace.lean`, SET-AF108H). The home is new because both premises are above
`NumberTheory/AdelicFourier.lean` — the box module reaches the Fourier development through
`AdelicFourier/Transform.lean`, so inserting there would be a cycle. `PureTensorSummable.lean` is the
sibling module of the same kind (one consumer of the box measure above the Fourier API).

## The rows

* `NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual` — 85 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean

## Landing (AF109G, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** One public declaration, 139 lines (107 of them the module the scaffold left, the rest
  this note) against the pin's 85. `check_port`:
  **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* **Substitutions**: none. Both premises are the port's
  (`NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers`,
  `NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace`), and the
  pin's proof ran unchanged but for the four drifts below.
* **Drift (four sites, none a statement change).**
  - `algebraMap_mem_adicCompletionIntegers` is `NumberField.AdelicLevel.…` in the port, not
    `NumberField.AdelicBox.…` as in the pin; opening `NumberField.AdelicLevel` for it is **not**
    allowed here — that namespace declares a second `integralFiniteAdeles` (identical type
    `Set (FiniteAdeleRing (𝓞 F) F)`), and opening both makes every applied occurrence of the bare
    name an *ambiguous term* (`AdelicBox.integralFiniteAdeles` vs `AdelicLevel.integralFiniteAdeles`).
    `open`-order does not fix it (measured, both orders ambiguous), so the **lemma** is spelled
    qualified and the pin's bare `integralFiniteAdeles` stays bare in the statement.
  - `Circle.exp_eq_one` moved to `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` in
    `v4.34.0`; that single module is the one import added (its `.olean` exists).
  - the pin's `(𝓞 F) F` explicit instance args to `algebraMap_mem_adicCompletionIntegers` are
    implicit here, so the call is `… v α`.
  - `Mathlib.Analysis.SpecialFunctions.Complex.Circle` is the *only* import added; `Mathlib.Tactic`
    was already there.
* **Engine gate**: pin sources 2, pin decls 2, module decls 1; **1 by hash** (`ecf63fe9dd8c820ada2b`),
  0 by name, 0 unaccounted.
* **Axioms**: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; the module carries no `set_option`):
  downward ladder 40000 / 20000 / 10000 / 5000 / 1000 — **silent at 10000, fails at 5000**
  (`isDefEq`, in the `push_cast; linarith` step of the forward direction). Module floor (the row's
  proof `sorry`, statement verbatim): **passes at 5000, fails at 1000** (`isDefEq`, reported at the
  statement's `FractionalIdeal.dual` subterm), so at the 1000 cap the cost is in the types.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.NumberField.StandardAddCharTrace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (ξ : F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
        ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * z) = 1)
      ↔ ξ ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
  set ιξ := algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ
  have hιO : ∀ α : 𝓞 F, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α
      ∈ integralFiniteAdeles (𝓞 F) F := fun α v =>
    NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v α
  have hιcompat : ∀ α : 𝓞 F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (α : F)
        = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α := fun α =>
    (IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) α).symm

  have hfc : ∀ t : ℝ, (↑(Real.fourierChar t) : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
    intro t
    rw [show ((1 : ℂ) = ((1 : Circle) : ℂ)) from rfl, Circle.coe_inj,
      Real.fourierChar_apply', Circle.exp_eq_one]
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, mul_left_cancel₀ h2π ?_⟩
      linarith [hn]
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
  have h1ne : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  constructor
  · intro h
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    subst hα
    rw [Algebra.traceForm_apply]
    have hval : ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1 := h _ (hιO α)
    rw [← hιcompat, ← map_mul,
      NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
        F hψ hψ_inf (ξ * (α : F))] at hval
    obtain ⟨n, hn⟩ := (hfc _).mp hval
    refine ⟨-n, ?_⟩
    have : ((Algebra.trace ℚ F (ξ * (α : F)) : ℚ) : ℝ) = ((-n : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this.symm
  · intro hξ z hz
    have hχ_cont : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ψ (0, ιξ * w)) := by
      have : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ((0, ιξ * w) : AdeleRing (𝓞 F) F)) :=
        continuous_const.prodMk (continuous_const.mul continuous_id)
      exact hψ.continuous.comp this
    set K : Set (FiniteAdeleRing (𝓞 F) F) := {w | ψ (0, ιξ * w) = 1}
    have hK_closed : IsClosed K := isClosed_eq hχ_cont continuous_const
    have hιO_K : Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) ⊆ K := by
      rintro _ ⟨α, rfl⟩
      show ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1
      rw [← hιcompat, ← map_mul,
        NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
          F hψ hψ_inf (ξ * (α : F))]
      have htr : Algebra.trace ℚ F (ξ * (α : F)) ∈ (algebraMap ℤ ℚ).range := by
        have := (FractionalIdeal.mem_dual h1ne).mp hξ (α : F)
          ((FractionalIdeal.mem_one_iff _).mpr ⟨α, rfl⟩)
        rwa [Algebra.traceForm_apply] at this
      obtain ⟨n, hn⟩ := htr
      refine (hfc _).mpr ⟨-n, ?_⟩
      have : (algebraMap ℤ ℚ) n = (n : ℚ) := by simp [eq_intCast]
      rw [← hn, this]; push_cast; ring
    have hdense := integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers F
    exact hK_closed.closure_subset_iff.mpr hιO_K (hdense hz)

