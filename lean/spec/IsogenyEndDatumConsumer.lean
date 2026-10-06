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
    non-vacuity instances of the `Ws13S7` pure-algebra prelude at concrete integers.
-/
import FLTForHuman.WeierstrassCurve.Place.CoordinateRingDedekind
import FLTForHuman.Elliptic.TorsionCardLight
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.PointEndSubring
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.CharPolySquare
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

end IsogenyEndDatumConsumer
