/-
  Cross-module wire test for SET-1 (the two Mazur gateways).

  A `spec/` probe, not a library module. It exists separately from
  `spec/WeierstrassCurveConsumer.lean` because SET-1's modules import the
  `IsogenyEndDatum/Engine.lean` cone, and
  `WeierstrassCurve.Affine.normFormulaAlong_of_elliptic` is declared both there and
  in `Velu/RestrictAlong.lean`; no single environment can import both cones (see the
  V2 topic §2.1).

  Executed zones (each a real composition, no `#check`, no `sorry`; deleting any one
  SET-1 module makes this file fail):

  * zone 1 — the shared coordinate-ring pair (`Place/CoordinateRingDedekind.lean`) at
    the concrete curve `y² = x³ + 1` over `AlgebraicClosure ℚ`: the Dedekind-domain
    statement and an `exists_eq_XYIdeal`-produced nonzero prime fed back through the
    dictionary's `XYIdeal_isMaximal`;
  * zone 2 — the two light torsion aliases (`Elliptic/TorsionCardLight.lean`) at the
    curve `y² = x³ + 1` over `ℚ`, with the numeric check `n = 3 ↦ 9` and one
    composition with
    `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`;
  * zone 3 — gateway 1 (`IsogenyEndDatum/PointEndSubring.lean`), first at a variable
    curve and then at `W1`, with `hNs` discharged from
    `IsogenyEndDatum.normFormulaAlong_auto` and `ψ = 1` realised through the ported
    `idDatum` (its nonzero-ness comes from `CharPolySquare.lean`'s
    `intCast_addMonoidEnd_point_injective`).  The three gate instances are taken as
    hypotheses: the ported producer
    `exists_genusOnePlaceGate_isCentred_and_abelTheorem` lives in
    `WeierstrassCurve/GenusOnePlaceGateCentred.lean`, which imports
    `WeierstrassCurve/Place/RRSpace.lean`; that module's
    `scoped instance instInfinitePlace` collides with `Engine.lean`'s
    `WeierstrassCurve.Affine.instInfinitePlace`, so the two cones cannot be imported
    together (the same collision family as §2.1 — recorded in the module report);
  * zone 4 — gateway 2 (`IsogenyEndDatum/CharPolySquare.lean`) in hypothesis form
    (the non-integrality hypothesis has no concrete witness in the port), plus
    non-vacuity instances of the `Ws13S7` pure-algebra prelude at concrete integers;
  * zone 5 — the V3 translation headline (`IsogenyEndDatum/TranslationAlgEquiv.lean`)
    at `W1`, at the concrete nonzero point `R₁ = (0, 1)` and at `0`, and the resulting
    `restrictAlong` identity fed through the ported `placeOfPoint` and
    `Place.ord_restrictAlong` calculus.  Its module imports `DualEndData` (hence the
    same `Engine` cone as zones 1–4), so the three gate instances are hypotheses
    exactly as in zone 3.
  * zone 6 — the SET-V4 H5 vocabulary tail (`IsogenyEndDatum/Vocabulary.lean`): the
    rigidity node applied at `W1` to the `R = 0` translation and the identity, and the
    kernel-to-range headline in hypothesis form with its `χ` fed through the ported
    `IsogenyHomDatum.pointHom_apply_eq_sub` / `restrictAlong` API.  Gate instances are
    hypotheses, as everywhere in the `DualEndData` cone.
-/
import FLTForHuman.WeierstrassCurve.Place.CoordinateRingDedekind
import FLTForHuman.Elliptic.TorsionCardLight
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.PointEndSubring
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.CharPolySquare
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.TranslationAlgEquiv
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Analysis.Complex.Polynomial.Basic

set_option autoImplicit false
-- The pin-style `haveI` instance walls in the zones below are intentional.
set_option linter.style.haveILetI false

noncomputable section

-- The concrete curve over `AlgebraicClosure ℚ` has no `DecidableEq` instance in the
-- port (the pin's `instDecEqAlgebraicClosureRat` lives in the Galois-rep cone, which
-- this spec file must not import); `Mathlib`'s `Point` `AddCommGroup` instance needs
-- it, so the classical instance is opened locally.
attribute [local instance] Classical.decEq

open Polynomial WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open scoped WeierstrassCurve.Affine

universe u

namespace IsogenyEndDatumConsumer

/-- The curve `y² = x³ + 1` over `ℚ` (`a₁ = a₂ = a₃ = a₄ = 0`, `a₆ = 1`). -/
abbrev W0 : WeierstrassCurve ℚ := WeierstrassCurve.mk (0 : ℚ) 0 0 0 1

/-- The same curve over `AlgebraicClosure ℚ`, the concrete-curve idiom of the other
spec consumer. -/
abbrev W1 : WeierstrassCurve (AlgebraicClosure ℚ) :=
  WeierstrassCurve.mk (0 : AlgebraicClosure ℚ) 0 0 0 1

/-- `Δ = -432 ≠ 0`, so `W0` is elliptic. -/
instance : W0.IsElliptic :=
  ⟨IsUnit.mk0 _
    (by norm_num [W0, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

/-- `Δ = -432 ≠ 0`, so `W1` is elliptic. -/
instance : W1.IsElliptic :=
  ⟨IsUnit.mk0 _
    (by norm_num [W1, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈])⟩

-- Zone 1: the shared coordinate-ring pair. The Dedekind statement is the module's
-- headline; the `XYIdeal` normal form turns a nonzero prime into an `XYIdeal` prime,
-- which the dictionary's maximality lemma then closes.
example : IsDedekindDomain W1.toAffine.CoordinateRing :=
  WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain W1

example {P : Ideal W1.toAffine.CoordinateRing} (hP : P ≠ ⊥) [P.IsPrime] :
    P.IsMaximal := by
  obtain ⟨a, b, hab, hPab⟩ :=
    WeierstrassCurve.Affine.CoordinateRing.exists_eq_XYIdeal (W := W1.toAffine) hP
  rw [hPab]
  exact WeierstrassCurve.Affine.CoordinateRing.XYIdeal_isMaximal hab

-- Zone 2: the two light torsion aliases. `n = 3` gives `9`, and the count feeds the
-- `ZMod n × ZMod n` classification.
example : Nat.card (Submodule.torsionBy ℤ (W0⁄(AlgebraicClosure ℚ)).Point 3) = 9 :=
  (WeierstrassCurve.card_torsion_of_isAlgClosed_light (F := ℚ) (K := AlgebraicClosure ℚ)
    W0 (n := 3) (by norm_num)).trans (by norm_num)

example : Nat.card (Submodule.torsionBy ℤ W1.toAffine.Point 3) = 9 :=
  (WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W1 (n := 3) (by norm_num)
    (by norm_num)).trans (by norm_num)

example (n : ℕ) (hn : (n : AlgebraicClosure ℚ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W0⁄(AlgebraicClosure ℚ)).Point n) = n ^ 2 ∧
      Nonempty (ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ (W0⁄(AlgebraicClosure ℚ)).Point n) :=
  ⟨WeierstrassCurve.card_torsion_of_isAlgClosed_light W0 hn,
    WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed W0 hn⟩

-- Zone 3: gateway 1, `hNs` discharged and `ψ = 1`. At a variable curve first (the
-- gate instances are hypotheses), then at `W1`, where the coordinate-ring pair of
-- zone 1 supplies the curve-specific input.
example {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W]
    [GenusOnePlaceGate.IsCentred W] [AbelTheorem W] :
    ∃ D : IsogenyEndDatum W, D.pointEnd D.normFormulaAlong_auto = 1 := by
  have hψ : (1 : AddMonoid.End W.Point) ∈
      isogenyEndSubring W (fun D => D.normFormulaAlong_auto) :=
    (mem_isogenyEndSubring_iff_mem_addSubgroup_closure W).mpr
      (AddSubgroup.subset_closure (IsogenyEndDatum.one_mem_range_pointEnd (W := W)))
  have hne : (1 : AddMonoid.End W.Point) ≠ 0 := by
    intro h
    have h1 : (1 : ℤ) = (0 : ℤ) :=
      Ws13S7.intCast_addMonoidEnd_point_injective W (by
        rw [Int.cast_one, Int.cast_zero]; exact h)
    exact one_ne_zero h1
  exact IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring (W := W)
    (hNs := fun D => D.normFormulaAlong_auto) 1 hψ hne

example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] :
    ∃ D : WeierstrassCurve.Affine.IsogenyEndDatum W1.toAffine,
      D.pointEnd D.normFormulaAlong_auto = 1 := by
  haveI : IsDedekindDomain W1.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain W1
  have hψ : (1 : AddMonoid.End W1.toAffine.Point) ∈
      WeierstrassCurve.Affine.isogenyEndSubring W1.toAffine
        (fun D => D.normFormulaAlong_auto) :=
    (WeierstrassCurve.Affine.mem_isogenyEndSubring_iff_mem_addSubgroup_closure
        W1.toAffine).mpr
      (AddSubgroup.subset_closure
        (WeierstrassCurve.Affine.IsogenyEndDatum.one_mem_range_pointEnd (W := W1.toAffine)))
  have hne : (1 : AddMonoid.End W1.toAffine.Point) ≠ 0 := by
    intro h
    have h1 : (1 : ℤ) = (0 : ℤ) :=
      Ws13S7.intCast_addMonoidEnd_point_injective W1.toAffine (by
        rw [Int.cast_one, Int.cast_zero]; exact h)
    exact one_ne_zero h1
  exact WeierstrassCurve.Affine.IsogenyEndDatum.exists_pointEnd_eq_of_mem_isogenyEndSubring
    (W := W1.toAffine) (hNs := fun D => D.normFormulaAlong_auto) 1 hψ hne

-- Zone 4: gateway 2, hypothesis form (the port has no concrete witness of the
-- non-integrality hypothesis), and the two `Ws13S7` prelude declarations at concrete
-- integers, which need no gate instances at all.
example {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve.Affine F) [W.IsElliptic] [GenusOnePlaceGate W] [AbelTheorem W]
    [GenusOnePlaceGate.IsCentred W]
    (hNs : ∀ D : IsogenyEndDatum W, NormFormulaAlong F D.ι D.hfin)
    (D₀ : IsogenyEndDatum W)
    (hD₀ : ¬ ∃ m : ℤ, ∀ P : W.Point, D₀.pointEnd (hNs D₀) P = m • P) :
    ∃ t n : ℤ, t ^ 2 < 4 * n ∧
      ∀ a b : ℤ, b ≠ 0 → ∃ D : IsogenyEndDatum W,
        (finrankAlong F D.ι : ℤ) = a ^ 2 + t * a * b + n * b ^ 2 :=
  WeierstrassCurve.Affine.IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq
    W hNs D₀ hD₀

example : (3 : AddMonoid.End ℤ) ∈ (⊥ : Subring (AddMonoid.End ℤ)) ↔
    ∃ n : ℤ, ∀ x : ℤ, (3 : AddMonoid.End ℤ) x = n • x :=
  Ws13S7.mem_bot_addMonoidEnd_iff (3 : AddMonoid.End ℤ)

example : ¬ ∃ a b : ℤ, b ≠ 0 ∧ a ^ 2 + 0 * a * b + 1 * b ^ 2 = 0 := by
  rintro ⟨a, b, hb, h⟩
  exact hb (Ws13S7.binaryQuadForm_pos_of_neg_disc (t := 0) (n := 1) (by norm_num) h).2

-- Zone 5 (V3): the translation automorphism of `W.FunctionField` by a point and its
-- action `placeOfPoint Q ↦ placeOfPoint (Q + R)` on the places
-- (`WeierstrassCurve/IsogenyEndDatum/TranslationAlgEquiv.lean`). That module imports
-- `DualEndData` (hence the `Engine` cone of zones 1–4), so the three gate instances
-- are hypotheses exactly as in zone 3, and no zone may import the `RRSpace` cone.
-- `Point.translateFF` and `Point.translateFF_zero` are `private` inside the module
-- (pin-local, §3.2), so the zero case is exercised through the headline at `R = 0`
-- rather than by name.

/-- The point `(0, 1)` of `y² = x³ + 1` over `AlgebraicClosure ℚ`; it satisfies the
equation (`1 = 0 + 1`) and has `2·1 ≠ 0`, hence is nonsingular, hence nonzero. -/
abbrev R₁ : W1.toAffine.Point :=
  WeierstrassCurve.Affine.Point.some 0 1 (by
    rw [WeierstrassCurve.Affine.nonsingular_iff']
    exact ⟨by rw [WeierstrassCurve.Affine.equation_iff']; norm_num [W1],
      Or.inr (by norm_num [W1])⟩)

example : R₁ ≠ 0 := WeierstrassCurve.Affine.Point.some_ne_zero _

-- The characteristic-free headline at `W1`, at the concrete nonzero point `R₁`.
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] (Q : W1.toAffine.Point) :
    ∃ (τ : W1.toAffine.FunctionField ≃ₐ[AlgebraicClosure ℚ] W1.toAffine.FunctionField)
      (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R₁) := by
  obtain ⟨τ, hτ, h⟩ :=
    WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add R₁
  exact ⟨τ, hτ, h Q⟩

-- The `R = 0` case: the restricted place is the place itself, which is
-- `restrictAlong_algHomId` at the identity algebra equivalence (this is the content of
-- the module's `private Point.translateFF_zero`).
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] (Q : W1.toAffine.Point) :
    ∃ (τ : W1.toAffine.FunctionField ≃ₐ[AlgebraicClosure ℚ] W1.toAffine.FunctionField)
      (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint Q := by
  obtain ⟨τ, hτ, h⟩ :=
    WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add
      (0 : W1.toAffine.Point)
  exact ⟨τ, hτ, by simpa using h Q⟩

-- The `[CharZero F]` sibling, derived from the general headline (both pin names must
-- exist; `AlgebraicClosure ℚ` is characteristic zero).
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] :
    ∃ (τ : W1.toAffine.FunctionField ≃ₐ[AlgebraicClosure ℚ] W1.toAffine.FunctionField)
      (hτ : τ.toAlgHom.toRingHom.IsIntegral),
      ∀ Q : W1.toAffine.Point,
        (placeOfPoint Q).restrictAlong τ.toAlgHom hτ = placeOfPoint (Q + R₁) :=
  WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add R₁

-- The identity fed into the ported place calculus: `Place.ord_restrictAlong` transports
-- the `ord`-at-`placeOfPoint Q` of `τ f` to the `ord`-at-`placeOfPoint (Q + R₁)` of `f`,
-- up to the ramification index of `τ`. Deleting the new module breaks this rewrite.
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] (Q : W1.toAffine.Point) (f : W1.toAffine.FunctionField) :
    ∃ (τ : W1.toAffine.FunctionField ≃ₐ[AlgebraicClosure ℚ] W1.toAffine.FunctionField)
      (_hτ : τ.toAlgHom.toRingHom.IsIntegral),
      (placeOfPoint Q).ord (τ.toAlgHom f)
        = AlgebraicCurve.Place.ramificationIndexAlong τ.toAlgHom (placeOfPoint Q)
            * (placeOfPoint (Q + R₁)).ord f := by
  obtain ⟨τ, hτ, h⟩ :=
    WeierstrassCurve.Affine.exists_algEquiv_forall_restrictAlong_placeOfPoint_eq_add R₁
  exact ⟨τ, hτ,
    (AlgebraicCurve.Place.ord_restrictAlong (φ := τ.toAlgHom) (hφ := hτ)
      (w := placeOfPoint Q) (f := f)).trans (by rw [h Q])⟩

-- Zone 6 (SET-V4): the H5 vocabulary tail landed in
-- `IsogenyEndDatum/Vocabulary.lean` — the function-field rigidity node and the
-- kernel-to-range node. Both examples stay inside the `DualEndData` cone (the
-- consumer already imports `Vocabulary` through `PointEndSubring`), so the three
-- gate instances are hypotheses exactly as in zones 3 and 5. Deleting either new
-- declaration (or the SET-3 `pointHom_apply_eq_sub` zone 6b composes with) makes the
-- file fail.

-- Zone 6a: rigidity at `W1`. The V3 translation headline at `R = 0` supplies an
-- `AlgEquiv` `τ` acting on every `placeOfPoint Q` as `Q ↦ Q + 0`; its `toAlgHom` and
-- the identity therefore agree on every `placeOfPoint`, and the rigidity node forces
-- `τ.toAlgHom = AlgHom.id`.
example [GenusOnePlaceGate W1.toAffine] [GenusOnePlaceGate.IsCentred W1.toAffine]
    [AbelTheorem W1.toAffine] :
    ∃ (τ : W1.toAffine.FunctionField ≃ₐ[AlgebraicClosure ℚ] W1.toAffine.FunctionField)
      (_hτ : τ.toAlgHom.toRingHom.IsIntegral),
      τ.toAlgHom = AlgHom.id (AlgebraicClosure ℚ) W1.toAffine.FunctionField := by
  obtain ⟨τ, hτ, h⟩ :=
    WeierstrassCurve.Affine.exists_algEquiv_restrictAlong_placeOfPoint_eq_add
      (0 : W1.toAffine.Point)
  refine ⟨τ, hτ, ?_⟩
  refine WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
    (V := W1.toAffine)
    (fun w => AlgebraicCurve.Place.isRational_of_deg_eq_one w
      (GenusOnePlaceGate.deg_eq_one w))
    τ.toAlgHom (AlgHom.id (AlgebraicClosure ℚ) W1.toAffine.FunctionField) hτ
    (IsogenyEndDatum.isIntegral_algHomId W1.toAffine) (fun P => ?_)
  rw [h P, add_zero, IsogenyEndDatum.restrictAlong_algHomId]

-- Zone 6b: the kernel-to-range headline in hypothesis form. The produced `χ` is fed
-- through the ported `IsogenyHomDatum.pointHom_apply_eq_sub`, so the second conjunct
-- is a real composition of the new headline with the SET-3 `placeOfPoint` /
-- `restrictAlong` API rather than a restatement.
example {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F}
    [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁]
    [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (ψ : IsogenyHomDatum V₀ V₂) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0) :
    ∃ (χ : IsogenyHomDatum V₁ V₂) (hNχ : NormFormulaAlong F χ.ι χ.hfin),
      (∀ P : V₀.Point, χ.pointHom hNχ (φ.pointHom hNφ P) = ψ.pointHom hNψ P) ∧
      ∀ P : V₀.Point, ψ.pointHom hNψ P
        = (pointEquivPlace (W := V₂)).symm
            ((placeOfPoint (φ.pointHom hNφ P)).restrictAlong χ.ι χ.hι)
          - (pointEquivPlace (W := V₂)).symm
            ((placeOfPoint (0 : V₁.Point)).restrictAlong χ.ι χ.hι) := by
  obtain ⟨χ, hNχ, hχ⟩ :=
    IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred φ hNφ ψ hNψ hker
  refine ⟨χ, hNχ, hχ, fun P => ?_⟩
  rw [← hχ P]
  exact IsogenyHomDatum.pointHom_apply_eq_sub χ hNχ (φ.pointHom hNφ P)

end IsogenyEndDatumConsumer
