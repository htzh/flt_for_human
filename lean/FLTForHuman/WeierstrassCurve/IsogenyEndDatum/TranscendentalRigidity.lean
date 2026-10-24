/-
  Transcendental rigidity: a curve whose `j`-invariant is transcendental over `ℚ`
  has only scalar endomorphisms.

  Over an algebraically closed field `F` of characteristic `0`, let `W/F` be
  elliptic and suppose every `IsogenyEndDatum` of `W` carries the norm formula
  (`hNs`).  If `j(W)` is transcendental over `ℚ`, then every endomorphism datum
  `D₀` is multiplication by an integer:

  `∃ m : ℤ, ∀ P, D₀.pointEnd (hNs D₀) P = m • P`.

  The two declarations here are one ladder.  The first is the diagonal leading
  coefficient of the modular polynomial: for `N` not a square, the `Y`-leading
  coefficient of `Φ_N(j, Y)` is a unit of `ℤ` (it is `±1`).  The second is the
  rigidity itself, proved by contradiction: a non-scalar `D₀` produces, through
  the characteristic-polynomial/degree count
  `exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq` and the squarefree
  values of the binary quadratic form `a² + t a b + n b²`, an endomorphism of some
  degree `N ≥ 2` that is not a square.  Its diagonal vanishing
  `aeval_j_diag_eq_zero_of_finrankAlong_eq` then exhibits `W.j` as a root of a
  monic integral polynomial of degree `N` — since that leading coefficient is a
  unit, `W.j` is integral over `ℤ` — and no transcendental element is.

  ## Reuse

  Every premise is in the port: the diagonal leading coefficient
  (`ModularCurve/ModularPolynomialLeadingCoeff.lean`), the characteristic-polynomial
  count (`IsogenyEndDatum/CharPolySquare.lean`), the squarefree-values theorem
  (`NumberTheory/SquarefreeValues.lean`), the `Φ_N` datum at every level
  (`ModularCurve/FunctionFieldGeneration/Capstone.lean`) and the diagonal vanishing
  capstone (`IsogenyEndDatum/DiagonalPhi.lean`).

  Pin `anthropics/fermats-last-theorem@aa2d8b3`:
  `Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag.lean` (10 lines)
  and `Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j.lean`
  (21 lines); proofs from the matching `P2M/Sol/S_*.lean` files (14 and 62 lines).

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag.lean
  spec-pin: Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.ModularPolynomialLeadingCoeff
import FLTForHuman.NumberTheory.SquarefreeValues
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.CharPolySquare
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.DiagonalPhi
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

universe u

/-- For `N ≥ 2` not a square, the `Y`-leading coefficient of `Φ_N(j, Y)` is a
unit of `ℤ`.  Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_ModularPolynomialData_isUnit_leadingCoeff_diag.lean`. -/
theorem ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag
    (N : ℕ) [NeZero N] (h2 : 2 ≤ N) (hN : ¬ IsSquare N)
    (data : ModularCurve.ModularPolynomialData N) :
    IsUnit (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X).leadingCoeff :=
  (fun _ => ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag_of_not_isSquare N hN data) h2

-- the proof's two `haveI`s introduce instance locals (`NeZero N`, and the elliptic
-- structure on the degree-`N` datum) that typeclass search consumes later, so the
-- style linter's `have` suggestion does not apply.
set_option linter.style.haveILetI false in
/-- **Transcendental `j` forces scalar endomorphisms.**  A curve over an
algebraically closed characteristic-`0` field whose `j`-invariant is transcendental
over `ℚ` has `End(W) = ℤ` at the level of `IsogenyEndDatum`: every endomorphism
datum is multiplication by an integer.  Verbatim from the pin wrapper
`Theorems/Thm_WeierstrassCurve_Affine_IsogenyEndDatum_exists_forall_pointEnd_eq_zsmul_of_transcendental_j.lean`. -/
theorem WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (W : WeierstrassCurve F) [W.IsElliptic]
    [GenusOnePlaceGate W.toAffine] [GenusOnePlaceGate.IsCentred W.toAffine] [AbelTheorem W.toAffine]
    (hNs : ∀ D : IsogenyEndDatum W.toAffine, NormFormulaAlong F D.ι D.hfin)
    (ht : Transcendental ℚ W.j) (D₀ : IsogenyEndDatum W.toAffine) :
    ∃ m : ℤ, ∀ P : W.toAffine.Point, D₀.pointEnd (hNs D₀) P = m • P := by
  by_contra hD₀
  obtain ⟨t, n, hdisc, hlift⟩ :=
    IsogenyEndDatum.exists_sq_lt_four_mul_and_forall_exists_finrankAlong_eq W.toAffine hNs D₀ hD₀
  obtain ⟨a, b, hb, hsf, h2⟩ :=
    Int.exists_squarefree_sq_add_mul_add_mul_sq_of_sq_lt_four_mul t n hdisc
  obtain ⟨D, hDdeg⟩ := hlift a b hb
  set N : ℕ := (a ^ 2 + t * a * b + n * b ^ 2).toNat with hNdef
  have hdegN : finrankAlong F D.ι = N := by
    have h := congrArg Int.toNat hDdeg
    rwa [Int.toNat_natCast] at h
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨data⟩ := ModularCurve.nonempty_modularPolynomialData N
  have hjroot : Polynomial.aeval W.j (data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X) = 0 :=
    IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq W hsf data D hdegN
  have hNns : ¬ IsSquare N := by
    rintro ⟨m, hm⟩
    have hunit := Nat.isUnit_iff.mp (hsf m (hm ▸ dvd_refl N))
    subst hunit
    omega
  have hint : IsIntegral ℤ W.j := by
    rcases Int.isUnit_iff.mp
        (ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag N h2 hNns data) with h1 | h1
    · exact ⟨data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X, h1, hjroot⟩
    · refine ⟨-(data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X), ?_, ?_⟩
      · show (-(data.Φ.eval₂ (RingHom.id (Polynomial ℤ)) Polynomial.X)).leadingCoeff = 1
        rw [Polynomial.leadingCoeff_neg, h1]; ring
      · rw [Polynomial.eval₂_neg, neg_eq_zero]; exact hjroot
  obtain ⟨p, hpm, hpe⟩ := hint
  exact ht ⟨p.map (Int.castRingHom ℚ), (hpm.map _).ne_zero, by
    rw [Polynomial.aeval_def, Polynomial.eval₂_map,
      show (algebraMap ℚ F).comp (Int.castRingHom ℚ) = algebraMap ℤ F from Subsingleton.elim _ _]
    exact hpe⟩

end
