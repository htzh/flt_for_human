/-
  The normal form and the finite automorphism group of a Weierstrass curve.

  * `WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two`: over a ring in which `2` is a
    unit, every elliptic curve is isomorphic to the Legendre curve `y² = x(x - 1)(x - t)` — the local
    computation that puts the curve in Legendre form over a valuation ring.
  * `WeierstrassCurve.finite_stabilizer_variableChange`: the stabilizer of an elliptic curve in the group
    of variable changes is finite: the unipotent part is cut out by polynomial identities and the
    diagonal part satisfies `u ^ 12 = 1`.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two.lean` (274 lines) and
  `S_WeierstrassCurve_finite_stabilizer_variableChange.lean` (285), with the statements from the wrappers
  of the same names.  The pin label namespaces `P2MKcLegendreLocal` and `AutFinitePort` are rectified to
  `LegendreNormalForm` and `AutomorphismFiniteness`.

  spec-pin: Theorems/Thm_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_exists_variableChange_eq_legendreCurve_of_isUnit_two.lean
  spec-pin: Theorems/Thm_WeierstrassCurve_finite_stabilizer_variableChange.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_finite_stabilizer_variableChange.lean
-/
import FLTForHuman.WeierstrassCurve.Defs.HasseInvariant
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open WeierstrassCurve

namespace LegendreNormalForm

variable {M : Type*} [Field M]

section Val

variable (A : ValuationSubring M)

lemma val_lambda {j l : M} (hj : A.valuation j ≤ 1) (h2 : A.valuation (2 : M) = 1)
    (hjl : j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3) :
    A.valuation l = 1 ∧ A.valuation (l - 1) = 1 := by
  have h256 : A.valuation (256 : M) = 1 := by
    rw [show (256 : M) = 2 ^ 8 by norm_num, Valuation.map_pow, h2, one_pow]
  have hv1 : A.valuation (1 : M) = 1 := Valuation.map_one _
  have hvneg1 : A.valuation (-1 : M) = 1 := by rw [Valuation.map_neg, hv1]

  have hle : A.valuation l ≤ 1 := by
    by_contra h
    push Not at h
    have hl0 : 0 < A.valuation l := lt_trans zero_lt_one h
    have hlm1 : A.valuation (l - 1) = A.valuation l := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left]
      rwa [hvneg1]
    have hquad : A.valuation (l ^ 2 - l + 1) = A.valuation l ^ 2 := by
      have h1 : A.valuation (-l + 1) < A.valuation (l ^ 2) := by
        rw [Valuation.map_pow]
        refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
        · rw [Valuation.map_neg]
          calc A.valuation l = A.valuation l * 1 := (mul_one _).symm
            _ < A.valuation l * A.valuation l := mul_lt_mul_of_pos_left h hl0
            _ = A.valuation l ^ 2 := (sq _).symm
        · rw [hv1]; exact one_lt_pow₀ h (by norm_num)
      rw [show l ^ 2 - l + 1 = l ^ 2 + (-l + 1) by ring, A.valuation.map_add_eq_of_lt_left h1,
        Valuation.map_pow]
    have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) ≤ A.valuation l ^ 4 := by
      rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hlm1]
      calc A.valuation j * (A.valuation l ^ 2 * A.valuation l ^ 2)
          ≤ 1 * (A.valuation l ^ 2 * A.valuation l ^ 2) := mul_le_mul_left hj _
        _ = A.valuation l ^ 4 := by rw [one_mul, ← pow_add]
    have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = A.valuation l ^ 6 := by
      rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, ← pow_mul]
    rw [hjl, hR] at hL
    have : A.valuation l ^ 4 < A.valuation l ^ 6 := pow_lt_pow_right₀ h (by norm_num)
    exact absurd (lt_of_le_of_lt hL this) (lt_irrefl _)
  have hle1 : A.valuation (l - 1) ≤ 1 := by
    rw [sub_eq_add_neg]
    exact le_trans (Valuation.map_add _ _ _) (max_le hle (le_of_eq hvneg1))

  have hl : A.valuation l = 1 := by
    rcases lt_or_eq_of_le hle with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation (l ^ 2 - l) < A.valuation (1 : M) := by
          rw [hv1, sub_eq_add_neg]
          refine Valuation.map_add_lt _ ?_ ?_
          · rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le h (by norm_num)
          · rw [Valuation.map_neg]; exact h
        rw [A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
        calc A.valuation j * (A.valuation l ^ 2 * A.valuation (l - 1) ^ 2)
            ≤ 1 * (A.valuation l ^ 2 * 1) := by
              apply mul_le_mul' hj
              exact mul_le_mul_right (pow_le_one₀ zero_le hle1) _
          _ = A.valuation l ^ 2 := by rw [one_mul, mul_one]
          _ < 1 := pow_lt_one₀ zero_le h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h

  have hl1 : A.valuation (l - 1) = 1 := by
    rcases lt_or_eq_of_le hle1 with h | h
    · exfalso
      have hquad : A.valuation (l ^ 2 - l + 1) = 1 := by
        have h1 : A.valuation ((l - 1) ^ 2 + (l - 1)) < A.valuation (1 : M) := by
          rw [hv1]
          refine Valuation.map_add_lt _ ?_ h
          rw [Valuation.map_pow]; exact pow_lt_one₀ zero_le h (by norm_num)
        rw [show l ^ 2 - l + 1 = ((l - 1) ^ 2 + (l - 1)) + 1 by ring,
          A.valuation.map_add_eq_of_lt_right h1, hv1]
      have hL : A.valuation (j * (l ^ 2 * (l - 1) ^ 2)) < 1 := by
        rw [Valuation.map_mul, Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hl, one_pow,
          one_mul]
        calc A.valuation j * A.valuation (l - 1) ^ 2 ≤ 1 * A.valuation (l - 1) ^ 2 :=
              mul_le_mul_left hj _
          _ = A.valuation (l - 1) ^ 2 := one_mul _
          _ < 1 := pow_lt_one₀ zero_le h (by norm_num)
      have hR : A.valuation (256 * (l ^ 2 - l + 1) ^ 3) = 1 := by
        rw [Valuation.map_mul, h256, one_mul, Valuation.map_pow, hquad, one_pow]
      rw [hjl, hR] at hL
      exact lt_irrefl _ hL
    · exact h
  exact ⟨hl, hl1⟩

end Val

section Model

variable (E : WeierstrassCurve M) [E.IsElliptic]

lemma legendre_Δ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).Δ = 16 * l ^ 2 * (l - 1) ^ 2 := by
  simp only [legendreCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

lemma legendre_c₄ {R : Type*} [CommRing R] (l : R) : (legendreCurve l).c₄ = 16 * (l ^ 2 - l + 1) := by
  simp only [legendreCurve, WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma legendre_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (l : R) :
    (legendreCurve l).map φ = legendreCurve (φ l) := by
  simp only [legendreCurve, WeierstrassCurve.map]
  ext <;> simp

theorem variableChange_eq_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M) • E =
      legendreCurve ((e₃ - e₁) / (e₂ - e₁)) := by
  -- The pin silences its unused-section-variable check file-wide; the port gives
  -- the section's ellipticity hypothesis a use instead.
  have hΔ : IsUnit E.Δ := E.isUnit_Δ
  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hV1 := Cubic.b_eq_three_roots ha he'
  have hV2 := Cubic.c_eq_three_roots ha he'
  have hV3 := Cubic.d_eq_three_roots ha he'
  simp only [RingHom.id_apply, twoTorsionPolynomial] at hV1 hV2 hV3

  simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hV1 hV2 hV3
  have hw2 : e₂ - e₁ ≠ 0 := by rw [← hw]; exact pow_ne_zero 2 hw0
  ext
  ·
    simp only [legendreCurve, variableChange_a₁, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₂, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    field_simp
    linear_combination hV1 + 4 * hw
  ·
    simp only [legendreCurve, variableChange_a₃, Units.val_inv_eq_inv_val, Units.val_mk0]
    field_simp
    ring
  ·
    simp only [legendreCurve, variableChange_a₄, Units.val_inv_eq_inv_val, Units.val_mk0]
    rw [← hw]
    have hV2' : 2 * E.a₄ + E.a₁ * E.a₃ = 2 * (e₁ * e₂ + e₁ * e₃ + e₂ * e₃) := by
      apply mul_left_cancel₀ h2
      linear_combination hV2
    field_simp
    linear_combination hV2' + e₁ * hV1 + 2 * (e₁ - e₃) * hw
  ·
    simp only [legendreCurve, variableChange_a₆, Units.val_inv_eq_inv_val, Units.val_mk0]

    have hroot : 4 * e₁ ^ 3 + E.b₂ * e₁ ^ 2 + 2 * E.b₄ * e₁ + E.b₆ = 0 := by
      have hmem : e₁ ∈ E.twoTorsionPolynomial.roots := by rw [he]; simp
      have hne : E.twoTorsionPolynomial.toPoly ≠ 0 := Cubic.ne_zero_of_a_ne_zero ha
      have := (Cubic.mem_roots_iff hne e₁).mp hmem
      simpa [twoTorsionPolynomial] using this
    simp only [WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆] at hroot
    field_simp
    linear_combination hroot

lemma j_legendre_mul (l : M) [(legendreCurve l).IsElliptic] :
    (legendreCurve l).j * (l ^ 2 * (l - 1) ^ 2) = 256 * (l ^ 2 - l + 1) ^ 3 := by
  have hjΔ : (legendreCurve l).j * (legendreCurve l).Δ = (legendreCurve l).c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← coe_Δ', Units.mul_inv, one_mul]
  rw [legendre_Δ, legendre_c₄] at hjΔ
  have h16 : (16 : M) ≠ 0 := by
    intro h
    apply (legendreCurve l).isUnit_Δ.ne_zero
    rw [legendre_Δ, h]; ring
  apply mul_left_cancel₀ h16
  linear_combination hjΔ

lemma j_mul_of_legendre (h2 : (2 : M) ≠ 0)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁)
    (hw0 : w ≠ 0) :
    E.j * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 * ((e₃ - e₁) / (e₂ - e₁) - 1) ^ 2) =
      256 * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 - (e₃ - e₁) / (e₂ - e₁) + 1) ^ 3 := by
  have hκ := variableChange_eq_legendre E h2 he hw hw0
  have hj : ∀ (V : WeierstrassCurve M) [V.IsElliptic],
      V = legendreCurve ((e₃ - e₁) / (e₂ - e₁)) →
      V.j * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 * ((e₃ - e₁) / (e₂ - e₁) - 1) ^ 2) =
        256 * (((e₃ - e₁) / (e₂ - e₁)) ^ 2 - (e₃ - e₁) / (e₂ - e₁) + 1) ^ 3 := by
    rintro V _ rfl
    exact j_legendre_mul _
  have h1 := variableChange_j E
    (⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M)
  exact h1 ▸ hj ((⟨Units.mk0 w hw0, e₁, -E.a₁ / 2,
    -(E.a₃ + e₁ * E.a₁) / 2⟩ : VariableChange M) • E) hκ

end Model

theorem main (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by
  have h2M : (2 : M) ≠ 0 := by
    have : ((2 : A) : M) ≠ 0 := fun h => h2.ne_zero (Subtype.ext h)
    exact this
  have h2v : A.valuation (2 : M) = 1 := by
    have := (A.valuation_eq_one_iff (2 : A)).mp h2
    exact this

  have ha : E.twoTorsionPolynomial.a ≠ 0 := by
    show (4 : M) ≠ 0
    rw [show (4 : M) = 2 * 2 by norm_num]; exact mul_ne_zero h2M h2M
  have hmap : Cubic.map (RingHom.id M) E.twoTorsionPolynomial = E.twoTorsionPolynomial := by
    cases hP : E.twoTorsionPolynomial; rfl
  have he' : (Cubic.map (RingHom.id M) E.twoTorsionPolynomial).roots = {e₁, e₂, e₃} := by
    rw [hmap]; exact he
  have hdisc : E.twoTorsionPolynomial.discr ≠ 0 :=
    E.twoTorsionPolynomial_discr_ne_zero (isUnit_iff_ne_zero.mpr h2M) E.isUnit_Δ
  obtain ⟨h12, h13, h23⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha he').mp hdisc
  have hw2 : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr (Ne.symm h12)
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; exact hw2 (by rw [← hw]; ring)

  set l₀ : M := (e₃ - e₁) / (e₂ - e₁) with hl₀
  have hjl := j_mul_of_legendre E h2M he hw hw0
  obtain ⟨hvl, hvl1⟩ := val_lambda A ((A.valuation_le_one_iff _).mpr hj) h2v hjl
  have hlA : l₀ ∈ A := (A.valuation_le_one_iff _).mp hvl.le
  set l : A := ⟨l₀, hlA⟩ with hl
  have hlu : IsUnit l := (A.valuation_eq_one_iff l).mpr hvl
  have hl1u : IsUnit (1 - l) := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 : M) - l₀) = 1
    rw [← neg_sub, Valuation.map_neg]; exact hvl1
  refine ⟨l, ⟨Units.mk0 w hw0, e₁, -E.a₁ / 2, -(E.a₃ + e₁ * E.a₁) / 2⟩, hlu, hl1u, ?_, rfl,
    rfl, rfl, rfl, rfl, ?_⟩
  ·
    rw [legendre_Δ]
    have h16 : IsUnit (16 : A) := by
      rw [show (16 : A) = 2 ^ 4 by norm_num]; exact h2.pow 4
    have hlm1 : IsUnit (l - 1) := by
      rw [show l - 1 = -(1 - l) by ring]; exact hl1u.neg
    exact ((h16.mul (hlu.pow 2)).mul (hlm1.pow 2))
  · rw [legendre_map, variableChange_eq_legendre E h2M he hw hw0]
    rfl

end LegendreNormalForm


open WeierstrassCurve

universe u in

theorem WeierstrassCurve.exists_variableChange_eq_legendreCurve_of_isUnit_two
    {M : Type u} [Field M] (A : ValuationSubring M) (h2 : IsUnit (2 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {e₁ e₂ e₃ w : M} (he : E.twoTorsionPolynomial.roots = {e₁, e₂, e₃}) (hw : w ^ 2 = e₂ - e₁) :
    ∃ (l : A) (κ : VariableChange M), IsUnit l ∧ IsUnit (1 - l) ∧
      IsUnit (legendreCurve l).Δ ∧ (l : M) = (e₃ - e₁) / (e₂ - e₁) ∧
      (κ.u : M) = w ∧ κ.r = e₁ ∧ κ.s = -E.a₁ / 2 ∧ κ.t = -(E.a₃ + e₁ * E.a₁) / 2 ∧
      κ • E = (legendreCurve l).map A.subtype := by
  exact LegendreNormalForm.main A h2 E hj he hw

open WeierstrassCurve Polynomial MulAction

namespace AutomorphismFiniteness

section PolyTools

variable {F : Type*} [Field F]

theorem ccgaf_quad_ne_zero (b c : F) : (X ^ 2 + C b * X - C c : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 2 + C b * X - C c : F[X]).coeff 2 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_quad_eval (b c t : F) :
    (X ^ 2 + C b * X - C c : F[X]).eval t = t ^ 2 + b * t - c := by
  simp

theorem ccgaf_cubic_ne_zero (b c : F) : (X ^ 3 + C b * X ^ 2 + C c * X : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 3 + C b * X ^ 2 + C c * X : F[X]).coeff 3 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_cubic_eval (b c r : F) :
    (X ^ 3 + C b * X ^ 2 + C c * X : F[X]).eval r = r ^ 3 + b * r ^ 2 + c * r := by
  simp

theorem ccgaf_quart_ne_zero (a : F) : (X ^ 4 + C a * X : F[X]) ≠ 0 := by
  intro h
  have hc : (X ^ 4 + C a * X : F[X]).coeff 4 = 1 := by simp
  rw [h, coeff_zero] at hc
  exact one_ne_zero hc.symm

theorem ccgaf_quart_eval (a s : F) : (X ^ 4 + C a * X : F[X]).eval s = s ^ 4 + a * s := by
  simp

end PolyTools

section CoefficientIdentities

variable {F : Type*} [Field F]

theorem ccgaf_coeff_eqs (E : WeierstrassCurve F) (γ : VariableChange F)
    (hst : γ • E = E) (hu : γ.u = 1) :
    2 * γ.s = 0
    ∧ (- γ.s * E.a₁ + 3 * γ.r - γ.s ^ 2 = 0)
    ∧ (γ.r * E.a₁ + 2 * γ.t = 0)
    ∧ (- γ.s * E.a₃ + 2 * γ.r * E.a₂ - (γ.t + γ.r * γ.s) * E.a₁ + 3 * γ.r ^ 2
        - 2 * γ.s * γ.t = 0)
    ∧ (γ.r * E.a₄ + γ.r ^ 2 * E.a₂ + γ.r ^ 3 - γ.t * E.a₃ - γ.t ^ 2
        - γ.r * γ.t * E.a₁ = 0) := by
  have hu' : ((γ.u⁻¹ : Fˣ) : F) = 1 := by rw [hu]; simp
  have h1 := congrArg WeierstrassCurve.a₁ hst
  rw [variableChange_a₁, hu', one_mul] at h1
  have h2 := congrArg WeierstrassCurve.a₂ hst
  rw [variableChange_a₂, hu', one_pow, one_mul] at h2
  have h3 := congrArg WeierstrassCurve.a₃ hst
  rw [variableChange_a₃, hu', one_pow, one_mul] at h3
  have h4 := congrArg WeierstrassCurve.a₄ hst
  rw [variableChange_a₄, hu', one_pow, one_mul] at h4
  have h6 := congrArg WeierstrassCurve.a₆ hst
  rw [variableChange_a₆, hu', one_pow, one_mul] at h6
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · linear_combination h1
  · linear_combination h2
  · linear_combination h3
  · linear_combination h4
  · linear_combination h6

end CoefficientIdentities

section KernelFiniteness

variable {F : Type*} [Field F]

theorem ccgaf_finite_unipotentStabilizer (E : WeierstrassCurve F) :
    Finite {γ : VariableChange F // γ • E = E ∧ γ.u = 1} := by
  classical
  by_cases hchar2 : (2 : F) = 0
  ·
    have h31 : (3 : F) = 1 := by linear_combination hchar2
    by_cases ha1 : E.a₁ = 0
    ·

      let P : F[X] := X ^ 4 + C E.a₃ * X
      have hP : P ≠ 0 := ccgaf_quart_ne_zero E.a₃
      let κ : F → F := fun s => (s ^ 2) * E.a₄ + (s ^ 2) ^ 2 * E.a₂ + (s ^ 2) ^ 3
      let Q : F → F[X] := fun s => X ^ 2 + C E.a₃ * X - C (κ s)
      have hQ : ∀ s, Q s ≠ 0 := fun s => ccgaf_quad_ne_zero E.a₃ (κ s)
      let T : Finset (F × F) :=
        (P.roots.toFinset).biUnion (fun s => ((Q s).roots.toFinset).image (fun t => (s, t)))
      refine Finite.of_injective
        (fun γ => (⟨(γ.1.s, γ.1.t), ?_⟩ : {p : F × F // p ∈ T})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, e2, -, e4, e6⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [ha1, h31] at e2
        have hr : γ.r = γ.s ^ 2 := by linear_combination e2
        rw [ha1, hchar2, h31, hr] at e4
        have hs : P.IsRoot γ.s := by
          rw [IsRoot.def, ccgaf_quart_eval]
          linear_combination e4 + (E.a₃ * γ.s) * hchar2
        rw [ha1, hr] at e6
        have ht : (Q γ.s).IsRoot γ.t := by
          rw [IsRoot.def, ccgaf_quad_eval]
          linear_combination -e6
        simp only [T, Finset.mem_biUnion, Multiset.mem_toFinset, Finset.mem_image]
        exact ⟨γ.s, (mem_roots hP).mpr hs, γ.t, (mem_roots (hQ _)).mpr ht, rfl⟩
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq, Prod.mk.injEq] at heq
        obtain ⟨hs, ht⟩ := heq
        obtain ⟨-, e2, -, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        obtain ⟨-, e2', -, -, -⟩ := ccgaf_coeff_eqs E γ' hst' hu'
        rw [ha1, h31] at e2 e2'
        have hr : γ.r = γ.s ^ 2 := by linear_combination e2
        have hr' : γ'.r = γ'.s ^ 2 := by linear_combination e2'
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · rw [hr, hr', hs]
        · exact hs
        · exact ht
    ·
      refine Finite.of_injective
        (fun γ => (⟨γ.1.s, ?_⟩ : {x : F // x ∈ ({0, -E.a₁} : Finset F)})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, e2, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [hchar2, zero_mul, add_zero] at e3
        have hr : γ.r = 0 := (mul_eq_zero.mp e3).resolve_right ha1
        rw [h31, hr] at e2
        have hss : γ.s * (E.a₁ + γ.s) = 0 := by linear_combination -e2
        rcases mul_eq_zero.mp hss with h0 | h0
        · simp [h0]
        · have hsa : γ.s = -E.a₁ := by linear_combination h0
          simp [hsa]
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq] at heq
        obtain ⟨-, -, e3, e4, -⟩ := ccgaf_coeff_eqs E γ hst hu
        obtain ⟨-, -, e3', e4', -⟩ := ccgaf_coeff_eqs E γ' hst' hu'
        rw [hchar2, zero_mul, add_zero] at e3 e3'
        have hr : γ.r = 0 := (mul_eq_zero.mp e3).resolve_right ha1
        have hr' : γ'.r = 0 := (mul_eq_zero.mp e3').resolve_right ha1
        rw [hchar2, h31, hr] at e4
        rw [hchar2, h31, hr'] at e4'
        have ht : γ.t * E.a₁ = γ'.t * E.a₁ := by
          rw [heq] at e4
          linear_combination e4' - e4
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · rw [hr, hr']
        · exact heq
        · exact mul_right_cancel₀ ha1 ht
  ·
    have hs0 : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ.s = 0 := by
      intro γ hst hu
      obtain ⟨e1, -, -, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
      exact (mul_eq_zero.mp e1).resolve_left hchar2
    by_cases hchar3 : (3 : F) = 0
    ·
      set τ : F := -E.a₁ / 2 with hτ
      let C₃ : F[X] :=
        X ^ 3 + C (E.a₂ - τ ^ 2 - τ * E.a₁) * X ^ 2 + C (E.a₄ - τ * E.a₃) * X
      have hC₃ : C₃ ≠ 0 := ccgaf_cubic_ne_zero _ _
      have ht : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ.t = τ * γ.r := by
        intro γ hst hu
        obtain ⟨-, -, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [hτ]
        field_simp
        linear_combination e3
      refine Finite.of_injective
        (fun γ => (⟨γ.1.r, ?_⟩ : {x : F // x ∈ C₃.roots.toFinset})) ?_
      · obtain ⟨γ, hst, hu⟩ := γ
        obtain ⟨-, -, -, -, e6⟩ := ccgaf_coeff_eqs E γ hst hu
        rw [ht γ hst hu] at e6
        have hr : C₃.IsRoot γ.r := by
          rw [IsRoot.def, ccgaf_cubic_eval]
          linear_combination e6
        rw [Multiset.mem_toFinset]
        exact (mem_roots hC₃).mpr hr
      · rintro ⟨γ, hst, hu⟩ ⟨γ', hst', hu'⟩ heq
        simp only [Subtype.mk.injEq] at heq
        apply Subtype.ext
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu, hu']
        · exact heq
        · rw [hs0 γ hst hu, hs0 γ' hst' hu']
        · rw [ht γ hst hu, ht γ' hst' hu', heq]
    ·
      have hone : ∀ γ : VariableChange F, γ • E = E → γ.u = 1 → γ = 1 := by
        intro γ hst hu
        obtain ⟨-, e2, e3, -, -⟩ := ccgaf_coeff_eqs E γ hst hu
        have hs : γ.s = 0 := hs0 γ hst hu
        rw [hs] at e2
        have hr : γ.r = 0 := by
          have h3r : 3 * γ.r = 0 := by linear_combination e2
          exact (mul_eq_zero.mp h3r).resolve_left hchar3
        rw [hr] at e3
        have ht : γ.t = 0 := by
          have h2t : 2 * γ.t = 0 := by linear_combination e3
          exact (mul_eq_zero.mp h2t).resolve_left hchar2
        apply WeierstrassCurve.VariableChange.ext
        · rw [hu]; rfl
        · rw [hr]; rfl
        · rw [hs]; rfl
        · rw [ht]; rfl
      have : Subsingleton {γ : VariableChange F // γ • E = E ∧ γ.u = 1} :=
        ⟨fun ⟨γ, hγ⟩ ⟨γ', hγ'⟩ => Subtype.ext
          ((hone γ hγ.1 hγ.2).trans (hone γ' hγ'.1 hγ'.2).symm)⟩
      infer_instance

end KernelFiniteness

section StabilizerFiniteness

variable {F : Type*} [Field F]

def ccgaf_uHom : VariableChange F →* Fˣ where
  toFun γ := γ.u
  map_one' := rfl
  map_mul' _ _ := rfl

@[scoped simp] theorem ccgaf_uHom_apply (γ : VariableChange F) : ccgaf_uHom γ = γ.u := by
  rfl

theorem ccgaf_u_pow_twelve (E : WeierstrassCurve F) [E.IsElliptic] (γ : VariableChange F)
    (hst : γ • E = E) : γ.u ^ 12 = 1 := by
  have hΔ : E.Δ ≠ 0 := E.isUnit_Δ.ne_zero
  have h := congrArg WeierstrassCurve.Δ hst
  rw [variableChange_Δ] at h
  have h1 : ((γ.u⁻¹ : Fˣ) : F) ^ 12 = 1 :=
    mul_right_cancel₀ hΔ (h.trans (one_mul E.Δ).symm)
  have h2 : ((γ.u ^ 12)⁻¹ : Fˣ) = 1 := by
    rw [← inv_pow, ← Units.val_inj, Units.val_pow_eq_pow_val, Units.val_one]
    exact h1
  simpa using h2

theorem ccgaf_stabilizer_finite (E : WeierstrassCurve F) [E.IsElliptic] :
    Finite ↥(MulAction.stabilizer (VariableChange F) E) := by
  classical
  let St := MulAction.stabilizer (VariableChange F) E
  let φ : ↥St →* Fˣ := (ccgaf_uHom (F := F)).comp St.subtype

  have hrange : φ.range ≤ rootsOfUnity 12 F := by
    rintro _ ⟨⟨γ, hγ⟩, rfl⟩
    rw [mem_rootsOfUnity]
    exact ccgaf_u_pow_twelve E γ (MulAction.mem_stabilizer_iff.mp hγ)
  have : Finite ↥(rootsOfUnity 12 F) := inferInstance
  have hR : Finite ↥φ.range :=
    Finite.of_injective (Subgroup.inclusion hrange) (Subgroup.inclusion_injective hrange)

  have hKtype : Finite {γ : VariableChange F // γ • E = E ∧ γ.u = 1} :=
    ccgaf_finite_unipotentStabilizer E
  have hK : Finite ↥φ.ker := by
    refine Finite.of_injective
      (fun γ => (⟨γ.1.1, ⟨MulAction.mem_stabilizer_iff.mp γ.1.2, ?_⟩⟩ :
        {γ : VariableChange F // γ • E = E ∧ γ.u = 1})) ?_
    · have h := γ.2
      rw [MonoidHom.mem_ker] at h
      exact h
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun (z : {γ : VariableChange F // γ • E = E ∧ γ.u = 1}) => z.1) h

  have : Finite (↥St ⧸ φ.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange φ).symm.toEquiv
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := φ.ker)).symm

end StabilizerFiniteness

end AutomorphismFiniteness

theorem WeierstrassCurve.finite_stabilizer_variableChange (F : Type*) [Field F] (E : WeierstrassCurve F) [E.IsElliptic] : Finite (MulAction.stabilizer (WeierstrassCurve.VariableChange F) E) := by
  exact AutomorphismFiniteness.ccgaf_stabilizer_finite E


end
