/-
  The `ℚ` instance of the slot product.

  The theory's headline specializes at `κ = ℚ`, `κ' = K`, `ε = coeffEmb K`, `jg = jq`: the base
  field is `ℚ⟮jq⟯`, the level series is `jqN M`, the nome map is
  `(coeffEmb K ∘ qExpand ℚ M) ∘ ℚ⟮jq⟯ ↪ ℚ((q))`, and the package is `Hall M`.

  One theorem and two transcription certificates:

  * `minpoly_eq_prod_slotValues` — the `ℚ` headline: the pushed minimal polynomial of `jqN M` is
    the slot polynomial;
  * `pushedMinpoly_rat` — `pushedMinpoly` at the `ℚ` instance *is* the inline composite it names,
    proved by `rfl`, so the naming is a transcription and not a change of statement. Its consumer is
    the pinned statement's delegation: rewriting along it turns the pinned text into the headline's
    left-hand side.
  * `pushedMinpolyAt_rat` — the same transcription for the off-diagonal object `pushedMinpolyAt`,
    read at a level-`N` nome of `jqN m`; its consumer is the level step `map_qExpand_minpoly_eq`,
    which holds the off-diagonal spelling.

  The pin's iterated-product spelling of the slot product is the general
  `slotPolynomial_eq_prod`, applied there and not restated here.

  The theory's strong induction is consumed at the `ℚ` instance by the headline's proof; there is no
  `ℚ` copy of it, and no copy of the `ℚ` `SlotProductAt` either — the surface names the theorem, the
  theory names the induction.

  Everything is data and instantiation: the carrier, the generator, and the package-spelling
  conversion (`hall_pkgAt`). Nothing `ℚ`-specific leaks upward — the theory's hypotheses are met
  definitionally, which is the check that the abstraction is honest.

  Both proofs are one-line instantiations; the two carrier premises come from `coeffEmb_jq` and
  `coeffEmb_qExpand`.
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Rat.LevelPackage

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- **The named `ℚ` object is the inline composite**: `pushedMinpoly` at the `ℚ` instance is the
minimal polynomial of `jqN M` over `ℚ⟮jq⟯` read along `(coeffEmb K).comp (qExpand ℚ M)`. -/
theorem pushedMinpoly_rat {K : Type*} [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M] :
    pushedMinpoly (coeffEmb K) jq M
      = (minpoly ℚ⟮jq⟯ (jqN M)).map
          (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) :=
  rfl

/-- **The named `ℚ` object at an off-diagonal nome**: `pushedMinpolyAt` at the `ℚ` instance is the
minimal polynomial of `jqN m` over `ℚ⟮jq⟯`, read along the level-`N` nome
`(coeffEmb K ∘ qExpand ℚ N) ∘ ℚ⟮jq⟯ → ℚ((q))`. The diagonal case `N = m` is `pushedMinpoly_rat`;
this is the same transcription for the two-level object the level step holds. -/
theorem pushedMinpolyAt_rat {K : Type*} [Field K] [Algebra ℚ K] (m : ℕ) [NeZero m] (N : ℕ)
    [NeZero N] :
    pushedMinpolyAt (coeffEmb K) jq m N
      = (minpoly ℚ⟮jq⟯ (jqN m)).map
          (((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) :=
  rfl

/-- **The slot product at `ℚ`**: for a primitive `M`-th root and `Hall M`, the pushed minimal
polynomial of `jqN M` is the slot polynomial. -/
theorem minpoly_eq_prod_slotValues {K : Type*} [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M) (hM : Hall M) :
    pushedMinpoly (coeffEmb K) jq M = slotPolynomial (coeffEmb K) jq M ζ :=
  pushedMinpoly_eq_slotPolynomial (coeffEmb K) jq (coeffEmb_jq K)
    (fun N _ x => coeffEmb_qExpand K N x) M hζ (hall_pkgAt M hM)

end ModularCurve
