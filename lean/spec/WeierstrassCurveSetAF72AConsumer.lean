/-
  Cross-module wire test for SET-AF72A (the Legendre normal form and the finite automorphism
  group).

  A `spec/` probe, not a library module. Two zones, one executed composition per headline: the
  headlines are *fired* at concrete data and their conclusions read in the shape the downstream
  cone reads them, rather than restated.

  * **Zone A**, `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two` over
    `M = ℚ`, at the Legendre curve `legendreCurve 2` — the curve `y² = x(x-1)(x-2)` — in the
    valuation ring `⊤ : ValuationSubring ℚ`. The two-torsion cubic of that curve is
    `4X(X-1)(X-2)`, so its roots are `{0, 1, 2}` and the change of variables is read with
    `e₁ = 0`, `e₂ = 1`, `e₃ = 2`, `w = 1` (`w² = e₂ - e₁`). The conclusion is read with `t = 2`
    for the Legendre parameter: `(l : ℚ) = (2 - 0) / (1 - 0) = 2`, which is the normal form the
    route to `j`-invariants consumes.
  * **Zone B**, `WeierstrassCurve.finite_stabilizer_variableChange` over `F = ℚ` on the same
    concrete curve `legendreCurve 2`, with `IsElliptic` carried: the stabilizer of
    `y² = x(x-1)(x-2)` in the group of variable changes over `ℚ` is finite. The ellipticity of
    `legendreCurve 2` itself is discharged here from the discriminant lemma of the module,
    `Δ = 16 · 2² · (2-1)² = 64`.

  The file contains no `#check`s, no `sorry`s and no placeholder proofs.
-/
import FLTForHuman.WeierstrassCurve.Automorphism.NormalForm

set_option autoImplicit false

noncomputable section

open WeierstrassCurve Polynomial

namespace WeierstrassCurveSetAF72AConsumer

/-- The two-torsion cubic of `y² = x(x-1)(x-2)` is `4X(X-1)(X-2)`, hence has roots `{0, 1, 2}`. -/
theorem roots_legendreCurve_two :
    (legendreCurve (2 : ℚ)).twoTorsionPolynomial.roots = {0, 1, 2} := by
  have hpoly : (legendreCurve (2 : ℚ)).twoTorsionPolynomial.toPoly
      = (4 : ℚ[X]) * (X - 2) * (X - 1) * (X - 0) := by
    simp only [WeierstrassCurve.twoTorsionPolynomial, legendreCurve, Cubic.toPoly,
      WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    rw [show (0 : ℚ) ^ 2 + 4 * -(1 + 2) = -12 by norm_num,
      show (2 : ℚ) * (2 * 2 + 0 * 0) = 8 by norm_num,
      show (0 : ℚ) ^ 2 + 4 * 0 = 0 by norm_num]
    simp only [Polynomial.C_neg, Polynomial.C_0, Polynomial.C_ofNat]
    ring
  have h4 : (4 : ℚ[X]) = C (4 : ℚ) := (Polynomial.C_ofNat 4).symm
  have h2 : (X - (2 : ℚ[X])) = (X - C 2) := by rw [Polynomial.C_ofNat]
  have h1 : (X - (1 : ℚ[X])) = (X - C 1) := by rw [Polynomial.C_1]
  have h0 : (X - (0 : ℚ[X])) = (X - C 0) := by rw [Polynomial.C_0]
  have hn4 : (C (4 : ℚ) : ℚ[X]) ≠ 0 := Polynomial.C_ne_zero.mpr (by norm_num)
  have hn2 : (X - C (2 : ℚ)) ≠ 0 := Polynomial.X_sub_C_ne_zero 2
  have hn1 : (X - C (1 : ℚ)) ≠ 0 := Polynomial.X_sub_C_ne_zero 1
  have hn0 : (X - C (0 : ℚ)) ≠ 0 := Polynomial.X_sub_C_ne_zero 0
  rw [Cubic.roots, hpoly, h4, h2, h1, h0]
  rw [Polynomial.roots_mul (p := C (4 : ℚ) * (X - C 2) * (X - C 1)) (q := (X - C 0))
      (mul_ne_zero (mul_ne_zero (mul_ne_zero hn4 hn2) hn1) hn0),
    Polynomial.roots_mul (p := C (4 : ℚ) * (X - C 2)) (q := (X - C 1))
      (mul_ne_zero (mul_ne_zero hn4 hn2) hn1),
    Polynomial.roots_mul (p := C (4 : ℚ)) (q := (X - C 2)) (mul_ne_zero hn4 hn2),
    Polynomial.roots_C, Polynomial.roots_X_sub_C, Polynomial.roots_X_sub_C,
    Polynomial.roots_X_sub_C]
  decide

/-- `legendreCurve 2` is elliptic: its discriminant is `16 · 2² · (2-1)² = 64`, a unit of `ℚ`. -/
theorem legendreCurve_two_isElliptic : (legendreCurve (2 : ℚ)).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, LegendreNormalForm.legendre_Δ]
  norm_num

/-- Zone A: the Legendre normal form at `t = 2` over `ℚ`, in the valuation ring `⊤`. The curve
`y² = x(x-1)(x-2)` is carried to `legendreCurve 2` by the variable change with `u = 1`, `r = 0`,
`s = 0`, `t = 0`, and the normal-form parameter is read as `(l : ℚ) = 2`. -/
theorem zoneA :
    ∃ (l : ↥(⊤ : ValuationSubring ℚ)) (κ : WeierstrassCurve.VariableChange ℚ),
      IsUnit l ∧ IsUnit (1 - l) ∧ IsUnit (legendreCurve l).Δ ∧ (l : ℚ) = 2 ∧
      (κ.u : ℚ) = 1 ∧ κ.r = 0 ∧ κ.s = 0 ∧ κ.t = 0 ∧
      κ • legendreCurve (2 : ℚ) = (legendreCurve l).map (⊤ : ValuationSubring ℚ).subtype := by
  have hE : (legendreCurve (2 : ℚ)).IsElliptic := legendreCurve_two_isElliptic
  obtain ⟨l, κ, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two
      (A := ⊤) (M := ℚ) (E := legendreCurve (2 : ℚ)) (e₁ := 0) (e₂ := 1) (e₃ := 2) (w := 1)
      (isUnit_iff_ne_zero.mpr (by
        intro h
        have h' := congrArg Subtype.val h
        norm_num at h'))
      (Subring.mem_top _) roots_legendreCurve_two (by norm_num)
  exact ⟨l, κ, h1, h2, h3, by simpa using h4, h5, h6, by simpa [legendreCurve] using h7,
    by simpa [legendreCurve] using h8, h9⟩

/-- Zone B: the stabilizer of `y² = x(x-1)(x-2)` in the variable-change group over `ℚ` is finite,
with `IsElliptic` for the concrete curve carried as a local instance. -/
theorem zoneB [hE : (legendreCurve (2 : ℚ)).IsElliptic] :
    Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange ℚ) (legendreCurve (2 : ℚ))) :=
  WeierstrassCurve.finite_stabilizer_variableChange ℚ (legendreCurve (2 : ℚ))

end WeierstrassCurveSetAF72AConsumer
