/-
  SET-AF47A consumer: the composite of a valuation subring with a valuation subring of its
  residue field, and the residue field of an algebraically closed one.

  **The zone.** Two rows, hence two compositions.

  Row A1 (`exists_le_forall_mem_iff_apply_mem`) is read on `ℚ`. The order's suggestion
  (`O' = O` for `W = ⊤` and `O' = ⊥` for `W = ⊥`) is typeable only halfway: `ValuationSubring`
  carries `OrderTop` but **no** `OrderBot`. There is no bottom valuation subring on a nontrivial
  field — `mem_or_inv_mem'` fails at `x = 1` for `{0}` — so neither `W = ⊥` nor `O' = ⊥` can be
  written, and the two substitutions are recorded here:

  * `W = ⊤` read at the rank-one instance `ℤ_(2) = (Rat.padicValuation 2).valuationSubring ⊂ ℚ`,
    with `res` the residue map `IsLocalRing.residue ℤ_(2)` (its residue field is `ZMod 2`): the
    composite is `O` again, `O' = ℤ_(2)`.
  * the "cuts `O` down" reading in place of `O' = ⊥`: at `O = ⊤ ⊂ ℚ` (the whole field) with `res`
    the identity, `W = ℤ_(2)` cuts `⊤` down to `W` itself, `O' = ℤ_(2)`. This is the honest
    content of the `W = ⊥` reading: the composite is the preimage `{x ∈ O | res x ∈ W}`, and with
    `W = ⊤` that preimage is always `O` itself (`consumer_zoneA_top`), so an `O'` strictly below
    `O` needs a `W` strictly below the whole residue field — which is what `⊥` would have been,
    had `ValuationSubring` had one.

  Reading 1 uses the residue map, so the kernel hypothesis is the real one
  (`maximalIdeal O ≤ ker (residue O)`); reading 2 uses the coefficient inclusion `O ↪ ℚ`, whose
  kernel is `⊥`, so the hypothesis is `bot_le`.

  Row D1/D2 (`exists_root_mem_of_monic`, `isAlgClosed_residueField`) are read over `ℂ`. The monic
  `X ^ 2 - 2` over `O = ⊤ : ValuationSubring ℂ` has a root inside `O` (D1), the residue of that
  root is a root of the same polynomial over the residue field (D2, via `Polynomial.eval_map`),
  and `isAlgClosed_residueField` supplies the `IsAlgClosed` instance from which the same residue
  root is recovered independently through `IsAlgClosed.exists_root`.

  This module is outside every library: it is a spec-side composition check, not part of the
  port's import graph.
-/
import FLTForHuman.FieldTheory.ValuationSubringComposite
import FLTForHuman.FieldTheory.ValuationSubringResidueField
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false

noncomputable section

open Polynomial

namespace ValuationSubring

/-! ### Row A1 — the composite criterion, read on `ℚ` -/

/-- `ℤ_(2)`, the 2-adic valuation subring of `ℚ` (the order's rank-one instance). -/
abbrev padicIntsRat : ValuationSubring ℚ := (Rat.padicValuation 2).valuationSubring

/-- The kernel hypothesis is automatic for the residue map: `residue` kills the maximal ideal. -/
theorem maximalIdeal_le_ker_residue {F : Type*} [Field F] (O : ValuationSubring F) :
    IsLocalRing.maximalIdeal O ≤ RingHom.ker (IsLocalRing.residue O) :=
  fun x hx => RingHom.mem_ker.mp ((IsLocalRing.residue_eq_zero_iff x).mpr hx)

/-- **Zone A, reading 1.** At the rank-one `O = ℤ_(2) ⊂ ℚ`, `res` the residue map and `W = ⊤`,
the composite is `O` itself: `O' = O`. -/
theorem consumer_zoneA_top :
    Composite.composite padicIntsRat (IsLocalRing.residue padicIntsRat)
        (maximalIdeal_le_ker_residue padicIntsRat) ⊤ = padicIntsRat := by
  ext x
  rw [Composite.mem_composite_iff]
  exact ⟨fun h => h.1, fun hx => ⟨hx, Subring.mem_top _⟩⟩

/-- **Zone A, reading 2** (the substitute for `W = ⊥`, see the header). At `O = ⊤ ⊂ ℚ` with `res`
the coefficient inclusion and `W = ℤ_(2)`, the composite criterion returns `O' = ℤ_(2)`: the
witness of `exists_le_forall_mem_iff_apply_mem` is `W` itself. -/
theorem consumer_zoneA_cut_down :
    ∃ O' : ValuationSubring ℚ, O' ≤ ⊤ ∧
      (∀ x : (⊤ : ValuationSubring ℚ),
        (x : ℚ) ∈ O' ↔ (SubringClass.subtype (⊤ : ValuationSubring ℚ)) x ∈ padicIntsRat) ∧
      (∀ x : (⊤ : ValuationSubring ℚ),
        (x : ℚ) ∈ O'.nonunits ↔
          (SubringClass.subtype (⊤ : ValuationSubring ℚ)) x ∈ padicIntsRat.nonunits) ∧
      O' = padicIntsRat := by
  obtain ⟨O', hle, hiff, hnu⟩ :=
    exists_le_forall_mem_iff_apply_mem (⊤ : ValuationSubring ℚ)
      (SubringClass.subtype (⊤ : ValuationSubring ℚ))
      (by rw [IsLocalRing.maximalIdeal_eq_bot]; exact bot_le) padicIntsRat
  refine ⟨O', hle, hiff, hnu, ?_⟩
  ext y
  rw [hiff ⟨y, Subring.mem_top y⟩]
  rfl

/-! ### Row D1/D2 — a monic polynomial over a valuation subring of `ℂ`, and its residue root -/

/-- `X ^ 2 - 2`, the order's concrete monic polynomial, over `⊤ : ValuationSubring ℂ`. -/
abbrev sqSubTwo : Polynomial (⊤ : ValuationSubring ℂ) := X ^ 2 - C 2

theorem sqSubTwo_monic : sqSubTwo.Monic :=
  monic_X_pow_sub_C (2 : (⊤ : ValuationSubring ℂ)) (by norm_num)

theorem sqSubTwo_natDegree : sqSubTwo.natDegree = 2 :=
  natDegree_X_pow_sub_C

/-- **Zone B, first leg.** `X ^ 2 - 2` has its root inside `O = ⊤ : ValuationSubring ℂ`. -/
theorem consumer_zoneB_root :
    ∃ x : (⊤ : ValuationSubring ℂ), aeval (x : ℂ) sqSubTwo = 0 :=
  exists_root_mem_of_monic ⊤ sqSubTwo sqSubTwo_monic (by rw [sqSubTwo_natDegree]; norm_num)

/-- **Zone B, second leg.** The residue of that root is a root of `X ^ 2 - 2` over the residue
field of `O`. -/
theorem consumer_zoneB_residue_root :
    ∃ z : IsLocalRing.ResidueField (⊤ : ValuationSubring ℂ),
      Polynomial.eval z (sqSubTwo.map (IsLocalRing.residue (⊤ : ValuationSubring ℂ))) = 0 := by
  obtain ⟨x, hx⟩ := consumer_zoneB_root
  refine ⟨IsLocalRing.residue (⊤ : ValuationSubring ℂ) x, ?_⟩
  have hx0 : sqSubTwo.eval x = 0 := by
    have h1 : (algebraMap (⊤ : ValuationSubring ℂ) ℂ) (sqSubTwo.eval x) = 0 := by
      rw [← hx, Polynomial.aeval_def]
      exact (Polynomial.eval₂_at_apply (algebraMap (⊤ : ValuationSubring ℂ) ℂ) x).symm
    exact Subtype.coe_injective (by simpa using h1)
  rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hx0, map_zero]

/-- **Zone B, closing leg.** The residue field of `O` is algebraically closed
(`isAlgClosed_residueField`), and `IsAlgClosed.exists_root` at the image of `X ^ 2 - 2` produces a
residue root directly from that instance. -/
theorem consumer_zoneB_exists_root :
    ∃ z : IsLocalRing.ResidueField (⊤ : ValuationSubring ℂ),
      Polynomial.eval z (sqSubTwo.map (IsLocalRing.residue (⊤ : ValuationSubring ℂ))) = 0 := by
  have hdeg : (sqSubTwo.map (IsLocalRing.residue (⊤ : ValuationSubring ℂ))).degree ≠ 0 := by
    rw [sqSubTwo_monic.degree_map,
      Polynomial.degree_eq_natDegree sqSubTwo_monic.ne_zero, sqSubTwo_natDegree]
    norm_num
  obtain ⟨z, hz⟩ := @IsAlgClosed.exists_root (IsLocalRing.ResidueField (⊤ : ValuationSubring ℂ)) _
    (isAlgClosed_residueField ⊤) (sqSubTwo.map (IsLocalRing.residue (⊤ : ValuationSubring ℂ))) hdeg
  exact ⟨z, hz⟩

end ValuationSubring
