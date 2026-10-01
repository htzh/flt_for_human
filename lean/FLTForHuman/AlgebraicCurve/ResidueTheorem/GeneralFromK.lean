/-
The two K-route producers of the general `ResidueTheorem`.

`ResidueTheorem K F` (the `weilOfKaehler` functional) follows from the K-side
`ResidueTheoremK K F` (`weilOfKaehlerK`) across
`weilOfKaehler = weilOfKaehlerK` at `HasCanonicalLocalResidueKStar.dataKStar`
(`kaehlerResidueTermKFam_dataKStar` is `rfl`). The pin's bridge
`residueTheorem_of_residueTheoremK` is 21 lines; `residueTheorem_of_isAlgClosed` is
then `residueTheorem_of_residueTheoremK residueTheoremK_of_isAlgClosed`, so the
general Residue theorem over an **algebraically closed** field follows from row 3.6
(`ResidueTheorem/KFamily.lean`). The **perfect-field** producer
`residueTheorem_of_perfectField` is the separate, larger row 3.5 and is not here.

Sources:
`P2M/Sol/S_AlgebraicCurve_residueTheorem_of_residueTheoremK.lean` (21 ln) and
`P2M/Sol/S_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean` (40 ln); wrappers
`Theorems/Thm_AlgebraicCurve_residueTheorem_of_residueTheoremK.lean` and
`Theorems/Thm_AlgebraicCurve_residueTheorem_of_isAlgClosed.lean`.
-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.KFamily

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace AlgebraicCurve

/-- Pin `residueTheorem_of_residueTheoremK`: the general `ResidueTheorem` follows
from the K-side `ResidueTheoremK`, because `weilOfKaehler` and `weilOfKaehlerK` agree
at `dataKStar`. -/
theorem residueTheorem_of_residueTheoremK
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (h : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.ResidueTheorem K F := by
  intro _hPD ω hω f
  have key := h (fun v => HasCanonicalLocalResidueKStar.dataKStar v) hω f
  rw [weilOfKaehlerK_apply] at key
  rw [weilOfKaehler_apply]
  exact key

/-- Pin `residueTheorem_of_isAlgClosed`: the general Residue theorem over an
algebraically closed field, from the row-3.6 K ending. -/
theorem residueTheorem_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates] :
    AlgebraicCurve.ResidueTheorem K F :=
  residueTheorem_of_residueTheoremK residueTheoremK_of_isAlgClosed

end AlgebraicCurve
