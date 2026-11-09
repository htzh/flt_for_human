/-
  The slot product over an arbitrary field: the `C` layer's instance of the generic headline.

  At `κ = κ' = K` (the identity algebra, so `σ = RingHom.id`) and `jg = jqModC K`, the theory's
  objects read: the base field
  is `K⟮jqModC K⟯`, the level series is `jqNModC K M`, the nome map is
  `(qExpand K M) ∘ algebraMap` (the identity carrier drops out), and the package is the pin's
  `Pkg K M`, converted by `pkg_pkgAt`.

  One theorem and one transcription certificate:

  * `minpoly_jqNModC_map_eq_prod_slots` — the pin's headline, in its own spelling: the `hall`
    conjunction written out (which is `Pkg K M` definitionally) and the explicit `if`-form slot
    value. Its proof is the theory's headline plus `prod_slotValues`; no step of the induction is
    re-proved here.
  * `pushedMinpoly_anyField` — `pushedMinpoly` at this instance *is* the inline composite the pin
    writes, so the naming is a transcription and not a change of statement. Its
    consumer is the delegation above, and it is the counterpart of the `ℚ` layer's
    `pushedMinpoly_rat`.

  The iterated product in the conclusion is the general `slotPolynomial_eq_prod` applied to the
  theory's `slotPolynomial`, not restated here; `slotPolynomial` is a multiset product and the
  pin's `if`-form is `slotValue`'s body, so the last step `prod_slotValues` runs on those slots.
  spec-pin: Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
  spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.CharP.LevelPackage

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-- **The named object is the inline composite**: `pushedMinpoly` at `κ = κ' = K` (so
`σ = RingHom.id`) and `jg = jqModC K` is the minimal polynomial of `jqNModC K M` over
`K⟮jqModC K⟯`, read in `LaurentSeries K` along `(qExpand K M) ∘ algebraMap`. The identity algebra
collapses by `coeffMap_id_ringHom`. -/
theorem pushedMinpoly_anyField {K : Type*} [Field K] (M : ℕ) [NeZero M] :
    pushedMinpoly (κ' := K) (jqModC K) M
      = (minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (jqNModC K M)).map
          ((qExpand K M).comp
            (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
              (LaurentSeries K))) := by
  unfold pushedMinpoly nomeMap
  rw [show algebraMap K K = RingHom.id K from rfl, coeffMap_id_ringHom, RingHom.id_comp]
  rfl

/-- **The slot product over an arbitrary field**: the mapped minimal polynomial of `jqNModC K M` is
the product of `(X - C (if a = 0 then 0 else …))` over the slots. The pin's wrapper verbatim —
explicit `hall` conjunction, explicit `if`-form slot value — delegated to the theory's
`pushedMinpoly_eq_slotPolynomial` at `(jg := jqModC K)`, whose source condition holds by `rfl`. -/
theorem minpoly_jqNModC_map_eq_prod_slots {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    (minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M)).map
        ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))) := by
  refine (pushedMinpoly_anyField M).symm.trans ?_
  rw [pushedMinpoly_eq_slotPolynomial (κ' := K) (jqModC K) M rfl hζ (pkg_pkgAt M hall)]
  have hσ : coeffMap (algebraMap K K) (jqModC K) = jqModC K := by
    rw [show algebraMap K K = RingHom.id K from rfl, coeffMap_id_ringHom]
    rfl
  rw [hσ]
  exact prod_slotValues M (fun a b => slotValue (jqModC K) ζ a b)

end ModularCurve
