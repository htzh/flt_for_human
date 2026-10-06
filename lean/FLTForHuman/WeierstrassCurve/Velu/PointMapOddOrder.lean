/-
The odd-order Vélu point map: the descended function-field homomorphism's kernel
and the explicit `veluX`/`veluY` point map.

Canonical sources: the pinned FLT `aa2d8b3` wrappers

* `Theorems/Thm_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean`,
* `Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean`,

with their `S_` files
`P2M/Sol/S_WeierstrassCurve_exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples.lean`
(34 lines) and
`P2M/Sol/S_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean`
(185 lines).  The statements are the wrappers' verbatim text; the proofs are the
`S_` files' bodies adapted to mathlib `v4.34.0`.

The first headline destructures the already-ported
`WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq`
(`Velu/RestrictAlong.lean`) and drops its three extra conjuncts; net cost is a few
lines.  The second constructs the point map through the ported char-free seam lemma
`WeierstrassCurve.Affine.pointMapOfPushforward_eq_of_seam_cf`
(`Velu/RestrictAlong.lean`), the two characteristic-free function-field
principal-divisor instances (`PrincipalDivisorsSeparable.lean`), the genus-one gate
from `GenusOnePlaceGateCentred.lean`, and `SeparableAlong` from
`Algebra.IsSeparable.of_coprime_finrank_expChar` (`FieldTheory/SeparableOfCoprime.lean`)
together with the `normFormulaAlong_of_separableAlong` promotion in
`Velu/RestrictAlong.lean`.

The pin `S_` file's three primed helpers
(`pushforwardAlongDegZero_pointDivisor'`, `pushforwardAlongHom_pointClass'`,
`pointMapOfPushforward_eq_of_seam'`) are not redeclared: their content is already
public in the port as `pushforwardAlongDegZero_pointDivisor_cf`,
`pushforwardAlongHom_pointClass_cf` and `pointMapOfPushforward_eq_of_seam_cf`
(`Velu/RestrictAlong.lean`); the module uses those names.

Assumes from lower modules: `Velu/RestrictAlong.lean`, `GenusOnePlaceGateCentred.lean`,
`WeierstrassCurve/PrincipalDivisorsSeparable.lean`, `FieldTheory/SeparableOfCoprime.lean`,
`Velu/Discriminant.lean` (the quotient discriminant) and
`Place/CoordinateRingDedekind.lean` (the coordinate-ring Dedekind instance the
genus-one gate construction consumes).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean>
-/
import FLTForHuman.WeierstrassCurve.Velu.RestrictAlong
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred
import FLTForHuman.WeierstrassCurve.PrincipalDivisorsSeparable
import FLTForHuman.FieldTheory.SeparableOfCoprime
import FLTForHuman.WeierstrassCurve.Place.CoordinateRingDedekind
import FLTForHuman.WeierstrassCurve.Velu.Discriminant

set_option autoImplicit false
-- The pin's `haveI` instance walls are transcribed literally.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point AlgebraicCurve

universe u

namespace WeierstrassCurve

/-- **The descended function-field homomorphism's kernel is `zmultiples Q`.**  The
pin's `S_` `solution` destructures
`WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq`. -/
theorem exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    {W : WeierstrassCurve F} [W.toAffine.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hord : addOrderOf Q = 2 * n + 1)
    (hΔ' : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    [(W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.IsElliptic]
    [WeierstrassCurve.Affine.GenusOnePlaceGate W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred W.toAffine]
    [WeierstrassCurve.Affine.AbelTheorem W.toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine]
    [WeierstrassCurve.Affine.AbelTheorem
      (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine] :
    ∃ (ι : (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
            →ₐ[F] W.toAffine.FunctionField)
      (hι : ι.toRingHom.IsIntegral) (hfin : AlgebraicCurve.FiniteAlong F ι),
      AlgebraicCurve.finrankAlong F ι = 2 * n + 1
        ∧ ∀ hN : AlgebraicCurve.NormFormulaAlong F ι hfin,
            (WeierstrassCurve.Affine.pointMapOfPushforward ι hι hfin hN).ker
              = AddSubgroup.zmultiples Q := by
  obtain ⟨ι, hι, hfin, hrank, hker, _, _⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq hord hΔ'
  exact ⟨ι, hι, hfin, hrank, hker⟩

/-- **The explicit odd-order Vélu point map with `veluX`/`veluY` coordinates.**
Verbatim from
`Theorems/Thm_WeierstrassCurve_exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed.lean`;
the proof is the pin's `S_` `solution` (185 lines). -/
theorem exists_veluPointHom_oddOrderSummingSet_of_isAlgClosed
    {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] (W : WeierstrassCurve F) [W.IsElliptic]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : (p : F) ≠ 0)
    (Q : W.toAffine.Point) (hQord : addOrderOf Q = p) :
    let S := W.oddOrderSummingSet Q (p / 2)
    ∃ φ : W.toAffine.Point →+ (W.veluQuotient S).toAffine.Point,
      φ.ker = AddSubgroup.zmultiples Q ∧
      (∀ (x y : F) (h : W.toAffine.Nonsingular x y),
        (.some x y h : W.toAffine.Point) ∉ AddSubgroup.zmultiples Q →
          ∃ h', φ (.some x y h) = .some (W.veluX S x) (W.veluY S x y) h') := by
  intro S
  classical
  have hodd : p = 2 * (p / 2) + 1 := by
    rcases hp.eq_two_or_odd' with h | h
    · exact absurd h hp2
    · obtain ⟨k, hk⟩ := h
      omega
  have hord : addOrderOf Q = 2 * (p / 2) + 1 := hQord.trans hodd
  have hnF : ((2 * (p / 2) + 1 : ℕ) : F) ≠ 0 := by rw [← hodd]; exact hpF
  have hΔ' : (W.veluQuotient S).Δ ≠ 0 :=
    veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq W (p / 2) Q hord
  haveI hVell : (W.veluQuotient S).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ'⟩
  haveI : (W.veluQuotient S).toAffine.IsElliptic := hVell
  haveI : W.toAffine.IsElliptic := ‹W.IsElliptic›

  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : IsDedekindDomain (W.veluQuotient S).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient S)
  haveI : HasPrincipalDivisors F W.toAffine.FunctionField :=
    WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic W
  haveI : HasPrincipalDivisors F (W.veluQuotient S).toAffine.FunctionField :=
    WeierstrassCurve.hasPrincipalDivisors_functionField_of_isElliptic (W.veluQuotient S)
  obtain ⟨gW, cW, aW⟩ := exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := W.toAffine)
  obtain ⟨gV, cV, aV⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (W := (W.veluQuotient S).toAffine)
  letI : GenusOnePlaceGate W.toAffine := gW
  haveI : GenusOnePlaceGate.IsCentred W.toAffine := cW
  haveI : AbelTheorem W.toAffine := aW
  letI : GenusOnePlaceGate (W.veluQuotient S).toAffine := gV
  haveI : GenusOnePlaceGate.IsCentred (W.veluQuotient S).toAffine := cV
  haveI : AbelTheorem (W.veluQuotient S).toAffine := aV

  obtain ⟨ι, hι, hfin, hdeg, hker, hzero, haff⟩ :=
    exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed (W := W) hord hΔ'

  have hsep : SeparableAlong F ι := by
    letI := algebraAlong ι
    haveI : Module.Finite (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField := hfin
    obtain ⟨q, hq⟩ := ExpChar.exists F
    haveI : ExpChar (W.veluQuotient S).toAffine.FunctionField q :=
      expChar_of_injective_algebraMap (algebraMap F _).injective q
    have hcop : Nat.Coprime (Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField) q := by
      have hfr : Module.finrank (W.veluQuotient S).toAffine.FunctionField W.toAffine.FunctionField = 2 * (p / 2) + 1 :=
        hdeg
      rw [hfr]
      rcases hq with _ | ⟨hqprime⟩
      · exact Nat.coprime_one_right _
      · refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hqprime).mpr fun hdvd => hnF ?_))
        exact (CharP.cast_eq_zero_iff F q _).mpr hdvd
    exact Algebra.IsSeparable.of_coprime_finrank_expChar _ _ q hcop

  have hN : NormFormulaAlong F ι hfin := normFormulaAlong_of_separableAlong ι hfin hsep

  let g : W.toAffine.Point → (W.veluQuotient S).toAffine.Point := fun P =>
    match P with
    | 0 => 0
    | .some a b hab =>
        if hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q then 0
        else .some _ _ (Classical.choose (haff a b hab hm))
  have hg0 : g 0 = 0 := rfl
  have hgseam : ∀ P : W.toAffine.Point, (placeOfPoint P).restrictAlong ι hι = placeOfPoint (g P) := by
    intro P
    cases P with
    | zero => exact hzero _ (AddSubgroup.zero_mem _)
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · have : g (.some a b hab) = 0 := by simp only [g, dif_pos hm]
          rw [this]; exact hzero _ hm
        · have : g (.some a b hab) = .some _ _ (Classical.choose (haff a b hab hm)) := by
            simp only [g, dif_neg hm]
          rw [this]; exact Classical.choose_spec (haff a b hab hm)

  refine ⟨pointMapOfPushforward ι hι hfin hN, ?_, ?_⟩
  · ext P
    rw [AddMonoidHom.mem_ker, pointMapOfPushforward_eq_of_seam_cf ι hι hfin hN g hg0 hgseam P]
    cases P with
    | zero => exact ⟨fun _ => AddSubgroup.zero_mem _, fun _ => rfl⟩
    | some a b hab =>
        by_cases hm : (Point.some a b hab : W.toAffine.Point) ∈ AddSubgroup.zmultiples Q
        · simp only [g, dif_pos hm]; exact ⟨fun _ => hm, fun _ => trivial⟩
        · simp only [g, dif_neg hm]
          exact ⟨fun h0 => (Point.some_ne_zero _ h0).elim, fun h0 => absurd h0 hm⟩
  · intro x y h hP
    obtain ⟨h', _⟩ := haff x y h hP
    refine ⟨h', ?_⟩
    rw [pointMapOfPushforward_eq_of_seam_cf ι hι hfin hN g hg0 hgseam (.some x y h)]
    simp only [g, dif_neg hP]
    rfl

end WeierstrassCurve

end
