/-
The standard additive character's value at a rational point is the Fourier character of the trace.

`NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace` (48 pin lines): for an
`AdelicTraceData F` and an infinite adele `x`, `T.psiK (x, 0)` is `Real.fourierChar` of the trace of `x`
through `InfiniteAdeleRing.ringEquiv_mixedSpace`.  It is the archimedean computation every
Poisson-summation argument starts from, and its home is **new** because the module that declares
`AdelicTraceData` (`NumberTheory/NumberField/StandardGlobalAddChar.lean`) carries no `spec-pin:` wire, so a
declaration inserted there would never be diffed (FR-0316).

## The rows

* `NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace` — 48 pin `S_` lines.
* `NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace` — 48 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace.lean>

spec-pin: Theorems/Thm_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace.lean
spec-pin: P2M/Sol/S_NumberField_StandardAddChar_AdelicTraceData_psiK_apply_mk_zero_eq_fourierChar_trace.lean
spec-pin: Theorems/Thm_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace.lean
spec-pin: Theorems/Thm_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace.lean
spec-pin: P2M/Sol/S_NumberField_StandardAddChar_stdAddChar_apply_mk_zero_eq_fourierChar_trace.lean

## Landing (AF108H, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** Two public declarations, one per pin row, at the wrappers' names; 129 lines
  against the pin's 96. Both rows live here deliberately (the `psiK` row cannot be inserted in
  `StandardGlobalAddChar.lean`, which carries no `spec-pin:` wire — FR-0316), and the module is
  the one `AdeleRing`-level home above `AdelicFourier/Transform` that both statements need.
* **Substitutions**: none. Every premise is the port's — `AdelicTraceData.psiK_apply`,
  `adelicTrace_apply`, `psiQ_apply`, `psiArch_algebraMap`,
  `NumberField.mixedEmbedding.trace_mixedEmbedding`,
  `NumberField.AdelicBox.continuous_ringEquiv_mixedSpace`,
  `InfiniteAdeleRing.denseRange_algebraMap`, `IsGlobalAddChar.principalInvariant` — and the
  scaffold's import list carried them; **no import was added**.
* **Drift — FR-0255 twice, body only.** `AdeleRing`/`InfiniteAdeleRing` are plain `def`s here,
  so `rw` (which matches at `implicit` transparency) cannot substitute a `Prod.mk`/`HAdd` term
  for the `AdeleRing` argument under `ψ`: the failure is "the target expression is not
  type-correct under the `implicit` transparency level". Both sites became term-mode `rfl`
  ground equations, as the port's `NumberTheory/StandardAddChar/GlobalAndInfinite.lean`
  records:
  - `psiK_apply_mk_zero_eq_fourierChar_trace`: the pin's
    `rw [psiK_apply, adelicTrace_apply, psiQ_apply]` plus its two `show … from rfl` projections
    are one `show T.psiK (…) = psiArch (…) * psiFin (…) from rfl`, then the pin's own rewrites.
  - `addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace`: the pin's
    `rw [hιq, ← AddChar.map_add_eq_mul]` is a `calc` over two `AdeleRing`-typed `set`
    variables (`u`, `v`, equations `hu`/`hv` from `set`), with `Prod.ext`/`add_zero`/`zero_add`
    for the decomposition and `simp only [hu, hv]` for the last step.
  `LinearMap.continuous_of_finite_dimensional` is `continuous_of_finiteDimensional` at this pin.
* **`check_port`**: **2 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* **Engine gate**: pin sources 4, pin decls 4, module decls 2; **2 by hash**, 0 by name (hash
  differs), 0 unaccounted.
* **Axioms**: both `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**): **silent at 10000, timeout at 5000**
  (`whnf`, reported at the first declaration's *header*) — at that cap the cost is in the
  statement, not the proof.

## Landing (AF109G) — `stdAddChar`'s archimedean value

A third declaration joins the two: `stdAddChar_apply_mk_zero_eq_fourierChar_trace`,
`stdAddChar F (x, 0) = fourierChar (trace (mixedEmbedding x))` (13 pin `S_` lines). 205 lines now
(183 before; the row is a one-line proof term, the rest is this note); `check_port`
**3 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.

* **Surface.** The row is the `StandardAddChar` form of this module's own `AdelicTraceData.psiK` row,
  and it is *exactly* that row at `T := adelicTraceData F`: the port's
  `stdAddChar` is the `abbrev` `(adelicTraceData F).psiK` (`AdelicTraceFin.lean:222`), so the pin's
  one-line proof term applies unchanged (a definitional unfold, not a rewrite). No `sorry`, no
  `simp`, no lemma invented.
* **Substitutions**: none; **no import added** (the scaffold's `…NumberField.AdelicTraceFin` carries
  the `abbrev`).
* **Engine gate**: pin sources 2, pin decls 2, module decls 3; **1 by hash**
  (`d0e90220b289c1bb0fd5`), 0 by name, 0 unaccounted.
* **Axioms**: all 3 public declarations, `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**): unchanged by this row — **silent at 10000,
  fails at 5000 and at 1000** (`whnf`, reported at the declaration *header* line 77, i.e. the first
  row's statement), the same pair AF108H recorded. No `set_option` is installed.
-/

import FLTForHuman.NumberTheory.NumberField.StandardGlobalAddChar
import FLTForHuman.NumberTheory.NumberField.MixedEmbedding
import FLTForHuman.NumberTheory.NumberField.GlobalAddChar
import FLTForHuman.NumberTheory.AdelicFourier.Transform
import FLTForHuman.NumberTheory.AdelicBox
import Mathlib.Analysis.Complex.Circle
import Mathlib.Tactic
import FLTForHuman.NumberTheory.NumberField.AdelicTraceFin

open NumberField NumberField.StandardAddChar IsDedekindDomain MeasureTheory AutomorphicForm
open scoped Classical FourierTransform nonZeroDivisors

set_option autoImplicit false

theorem NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F] (T : AdelicTraceData F) (x : InfiniteAdeleRing F) :
    T.psiK (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) := by

  set f : InfiniteAdeleRing F → ℂ := fun x => T.psiK (x, 0) with hf
  set g : InfiniteAdeleRing F → ℂ := fun x => (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) with hg
  suffices hfg : f = g from congrFun hfg x
  have hfc : Continuous f :=
    T.continuous_psiK.comp (continuous_id.prodMk continuous_const :
      Continuous (fun x : InfiniteAdeleRing F => ((x, 0) : AdeleRing (𝓞 F) F)))
  have htr : Continuous (fun x : InfiniteAdeleRing F => Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) :=
    (LinearMap.continuous_of_finiteDimensional _).comp
      (NumberField.AdelicBox.continuous_ringEquiv_mixedSpace F)
  have hgc : Continuous g := by
    have hg' : g = fun x => Complex.exp (((2 * Real.pi * Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (InfiniteAdeleRing.ringEquiv_mixedSpace F x) : ℝ) : ℂ) * Complex.I) :=
      funext fun x => Real.fourierChar_apply _
    rw [hg']
    exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_const.mul htr)).mul
      continuous_const)
  refine Continuous.ext_on (InfiniteAdeleRing.denseRange_algebraMap F) hfc hgc ?_
  rintro _ ⟨q, rfl⟩
  simp only [hf, hg]

  -- `AdeleRing`/`InfiniteAdeleRing` are `def`s in this port (FR-0255), so `rw` at `implicit`
  -- transparency cannot see through them: the pin's `rw [psiK_apply, adelicTrace_apply, psiQ_apply]`
  -- and its two `show … from rfl` projections become the single `rfl` ground equation below.
  rw [show T.psiK (((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F)) :
        AdeleRing (𝓞 F) F))
      = psiArch (T.traceInf (algebraMap F (InfiniteAdeleRing F) q))
        * psiFin (T.traceFin (0 : FiniteAdeleRing (𝓞 F) F)) from rfl]
  rw [map_zero, AddChar.map_zero_eq_one, mul_one, T.traceInf_algebraMap, psiArch_algebraMap]

  rw [← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp, NumberField.mixedEmbedding.trace_mixedEmbedding,
    Real.fourierChar_apply]
  push_cast
  ring_nf

theorem NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (q : F) :
    ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar (-((Algebra.trace ℚ F q : ℚ) : ℝ)) : ℂ) := by

  -- `AdeleRing` is a plain `def` in this port, so `rw` (which matches at `implicit`
  -- transparency) cannot substitute a `Prod.mk` term for the `AdeleRing` argument under `ψ`
  -- (FR-0255).  The pin's `rw [hιq, ← AddChar.map_add_eq_mul]` therefore becomes the `calc`
  -- below, over `AdeleRing`-typed `set` variables whose equations `hu`/`hv` are `rfl`.
  set u : AdeleRing (𝓞 F) F :=
    (((algebraMap F (InfiniteAdeleRing F) q, (0 : FiniteAdeleRing (𝓞 F) F))) : AdeleRing (𝓞 F) F) with hu
  set v : AdeleRing (𝓞 F) F :=
    ((((0 : InfiniteAdeleRing F), algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) : AdeleRing (𝓞 F) F) with hv
  have hdec : (((algebraMap F (InfiniteAdeleRing F) q,
        algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) : AdeleRing (𝓞 F) F) = u + v := by
    rw [hu, hv]
    refine Prod.ext ?_ ?_
    · exact (add_zero _).symm
    · exact (zero_add _).symm

  have hsplit : ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
      = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
        * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := by
    calc ψ (algebraMap F (AdeleRing (𝓞 F) F) q)
        = ψ (((algebraMap F (InfiniteAdeleRing F) q,
              algebraMap F (FiniteAdeleRing (𝓞 F) F) q)) : AdeleRing (𝓞 F) F) := rfl
      _ = ψ (u + v) := by rw [hdec]
      _ = ψ u * ψ v := AddChar.map_add_eq_mul ψ u v
      _ = ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
            * ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q) := by simp only [hu, hv]

  have hPI : ψ (algebraMap F (AdeleRing (𝓞 F) F) q) = 1 := hψ.principalInvariant q

  have harch : ψ (algebraMap F (InfiniteAdeleRing F) q, 0)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) := by
    rw [hψ_inf, ← InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp,
      NumberField.mixedEmbedding.trace_mixedEmbedding]
  rw [hPI, harch] at hsplit

  have hne : (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ) ≠ 0 :=
    Circle.coe_ne_zero _
  have hx : ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q)
      = (Real.fourierChar ((Algebra.trace ℚ F q : ℚ) : ℝ) : ℂ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hsplit.symm
  rw [hx, ← Circle.coe_inv, ← AddChar.map_neg_eq_inv]
/-
## SET-AF109 insertion: NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace

The standard additive character on the infinite places is `fourierChar ∘ trace`.

`NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace` (13 pin lines): the
`stdAddChar`'s value at `(x, 0)` is `fourierChar (trace (mixedEmbedding x))`. It is the
`StandardAddChar` form of the archimedean trace computation this module's `AdelicTraceData.psiK` row
proves for a general global character.
-/
theorem NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace
    (F : Type) [Field F] [NumberField F] (x : InfiniteAdeleRing F) :
    stdAddChar F (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
      (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ) :=
  NumberField.StandardAddChar.AdelicTraceData.psiK_apply_mk_zero_eq_fourierChar_trace F
    (adelicTraceData F) x

