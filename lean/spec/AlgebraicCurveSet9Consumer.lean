/-
  Consumer specification for SET 9 of the `AlgebraicCurve` layer.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the set's headlines, composed across modules, expressed in Lean so
  that each is either bound or not.  It is a deliverable measure, not a proof obligation.  It
  is **not part of any library** (`lake build` does not see `spec/`); run it by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/AlgebraicCurveSet9Consumer.lean 2>&1 | grep -c error

  The error count is the metric.

  ZONES
  -----
    [rat]  ZONE A — the general rationality theorem `Place.isRational_of_isAlgClosed`
               (`Place/DegreeOne.lean`) at the generic `F`, composed with
               `Place.isRational_iff_deg_eq_one` (`Defs/PlaceEvaluation.lean`): every place of a
               finite `RatFunc K`-model has degree one, with **no** `IsCurveOver` hypothesis.
    [rec]  ZONE B — `weilReciprocity` (`WeilExchange/WeilReciprocity.lean`) read in product form
               by `Divisor.evalFun_def` (`Defs/PlaceEvaluation.lean`), with its two rationality
               hypotheses discharged by ZONE A's theorem: the reciprocity identity as a product
               of place evaluations over the two supports.
    [pair] ZONE C — `DivisorialWeilPairingData.toHom_injective_of_divisible`
               (`Pic0/DivisorialPairing.lean`) composed with the carrier's
               `toHom_apply_apply` and `pair_ne_zero` (`Pic0/WeilPairing.lean`): injectivity read
               as "a class whose character is trivial pairs trivially with everything".
-/
import FLTForHuman.AlgebraicCurve.Place.DegreeOne
import FLTForHuman.AlgebraicCurve.WeilExchange.WeilReciprocity
import FLTForHuman.AlgebraicCurve.Pic0.DivisorialPairing

open AlgebraicCurve

noncomputable section

universe u

/-! ## ZONE A — [rat] the rationality theorem at the generic field, read as `deg = 1` -/

section ZoneRat

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]

/-- Every place of a finite `RatFunc K`-model has rational residue field, and hence degree one —
the second conjunct is `Place.isRational_iff_deg_eq_one` applied to the first. -/
theorem zone_rat (v : Place K F) : v.IsRational ∧ v.deg = 1 :=
  ⟨Place.isRational_of_isAlgClosed v,
    (Place.isRational_iff_deg_eq_one v).mp (Place.isRational_of_isAlgClosed v)⟩

end ZoneRat

/-! ## ZONE B — [rec] the reciprocity identity in product form, rationality from ZONE A -/

section ZoneRec

variable {K F : Type*} [Field K] [IsAlgClosed K] [CharZero K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [HasPrincipalDivisors K F]

/-- The general reciprocity law (`WeilExchange/WeilReciprocity.lean`), with its two rationality
hypotheses discharged by `Place.isRational_of_isAlgClosed` (`Place/DegreeOne.lean`) and its
conclusion rewritten as the product identity of `Divisor.evalFun_def`. -/
theorem zone_rec (f g : F) (Df Dg : Divisor K F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hDf : ∀ v : Place K F, Df v = v.ord f) (hDg : ∀ v : Place K F, Dg v = v.ord g)
    (hdisj : ∀ v : Place K F, v.ord f = 0 ∨ v.ord g = 0) :
    ∏ v ∈ Dg.support, Place.evalAt v f ^ Dg v
      = ∏ v ∈ Df.support, Place.evalAt v g ^ Df v := by
  have hrat : ∀ v : Place K F, Place.IsRational v := fun v => Place.isRational_of_isAlgClosed v
  have h := weilReciprocity K F f g Df Dg hf hg hDf hDg hdisj
    (fun v _ => hrat v) (fun v _ => hrat v)
  simpa [Divisor.evalFun_def] using h

end ZoneRec

/-! ## ZONE C — [pair] injectivity of `toHom` read through the carrier's own laws -/

section ZonePair

variable {K : Type u} {F : Type u} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]

/-- Given divisibility of `Pic⁰` on every finite extension, a torsion class whose character is
trivial is zero: injectivity of `toHom` (`Pic0/DivisorialPairing.lean`) applied at `0`, read by
`toHom_apply_apply` and `pair_ne_zero` (`Pic0/WeilPairing.lean`). -/
theorem zone_pair (hdiv : ∀ (L' : Type u) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (m : ℤ), m ≠ 0 → ∀ x : Pic0 K L', ∃ y, m • y = x)
    (e : DivisorialWeilPairingData K F n) {x : Pic0.torsion K F n}
    (hx : e.toHom x = 0) : x = 0 := by
  have hinj : Function.Injective e.toHom :=
    DivisorialWeilPairingData.toHom_injective_of_divisible hdiv e
  refine hinj ?_
  rw [hx]
  exact (map_zero e.toHom).symm

end ZonePair

end
