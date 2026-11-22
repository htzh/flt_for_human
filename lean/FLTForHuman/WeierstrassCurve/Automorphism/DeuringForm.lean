/-
  The Deuring normal form of a curve with 3-torsion, in characteristic `≠ 2, 3` and in characteristic 2.

  At a 3-torsion point whose `y`-derivative is a cube, a curve over a valuation ring is carried by a
  variable change to the Deuring form `y² = x³ + αx` — with the change's parameters `u`, `r`, `s`, `t`
  pinned down (`κ.u = c`, `κ.r = x₀`, `κ.t = y₀`, `κ.s` an explicit rational function) and the
  discriminant a unit.  In characteristic `2`, where the `j = 0` curve is `y² + y = x³` and the
  3-torsion point behaves differently, the same argument yields the arithmetic form
  `t = u * μ ^ 8` (the `j = 0` curve's `a₆ = t⁵`), and the two diagonal automorphisms
  `u ↦ (u, 0, 0, 0)` with `u³ = 1` (resp. `u² = -1`) act trivially on `y² = x³ + B` (resp.
  `y² = x³ + Ax`).

  Transcribed from the four pins below (pinned `aa2d8b3`, 213 + 215 + 26 + 26 lines), all public,
  each with its own short proof; no shared engine.

  Assumes mathlib's `ValuationSubring`, `WeierstrassCurve.Affine.Point.some`/`Nonsingular`, the
  variable-change action, and the port's `Automorphism/NormalForm.lean` (the normal-form layer this
  module sits beside).

  The pins' generated label namespaces are rectified to subject namespaces: `P2MKcDeuringLocal` →
  `WeierstrassCurve.DeuringLocal` and `P2MKcWildEight` → `WeierstrassCurve.DeuringCharTwo`, so the
  engine declarations of the two big pins sit beside their headlines; each pin's `solution` is the
  headline theorem of this module.  Deviations from the pins' proof text, all forced by the port's
  linter-free requirement and none statement-level: the deprecated `zero_le'` is spelled `zero_le`
  (three sites), and `DeuringLocal.main` carries a declaration-scoped
  `linter.style.haveILetI false` because its load-bearing `haveI` registers the `IsElliptic`
  instance that `j_deuring_mul` consumes (the linter's `have` would drop it; FR-0263-style escape).

  `dedup.py --within` reports two `shape` clusters and both are the pins' own: each headline's
  statement is byte-identical to the pin's engine row `main` (the pin's `solution` is a one-line
  wrapper `P2MKc….main …`), so the pair is *statement* duplication inherited with the pin — the
  headline keeps the published name and `main` keeps the pin's engine name, as the order requires;
  neither is deleted.

  Heartbeat probe (FR-0225, recorded not installed): the module is silent at
  `-DmaxHeartbeats=8000` and fails at `-DmaxHeartbeats=7000` (deterministic timeout at `whnf`);
  i.e. it costs ≈7–8 k heartbeats, ~4 % of the default 200 k gate.  No `set_option maxHeartbeats`
  is installed.

  spec-pin: P2M/Sol/S_WeierstrassCurve_exists_variableChange_eq_deuring_of_isUnit_three.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_exists_isUnit_mul_pow_eight_eq_of_charTwo.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_pow_three_eq_one.lean
  spec-pin: P2M/Sol/S_WeierstrassCurve_variableChange_mk_smul_eq_self_of_sq_eq_neg_one.lean
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine

universe u

namespace WeierstrassCurve

namespace DeuringLocal

variable {M : Type*} [Field M]

section Deuring

variable {R : Type*} [CommRing R] (α : R)

lemma deuring_Δ : (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).Δ = α ^ 3 - 27 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

lemma deuring_c₄ : (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).c₄ = α * (α ^ 3 - 24) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
  ring

lemma deuring_map {S : Type*} [CommRing S] (φ : R →+* S) :
    (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve R).map φ = ⟨φ α, 0, 1, 0, 0⟩ := by
  simp only [WeierstrassCurve.map, map_zero, map_one]

lemma j_deuring_mul {F : Type*} [Field F] (α : F) [(⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve F).IsElliptic] :
    (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve F).j * (α ^ 3 - 27) = α ^ 3 * (α ^ 3 - 24) ^ 3 := by
  set V : WeierstrassCurve F := ⟨α, 0, 1, 0, 0⟩ with hV
  have hjΔ : V.j * V.Δ = V.c₄ ^ 3 := by
    rw [WeierstrassCurve.j, mul_comm, ← mul_assoc, ← coe_Δ', Units.mul_inv, one_mul]
  rw [deuring_Δ, deuring_c₄] at hjΔ
  linear_combination hjΔ

end Deuring

section Val

variable (A : ValuationSubring M)

lemma val_natCast_le (n : ℕ) : A.valuation (n : M) ≤ 1 := by
  rw [show (n : M) = ((n : A) : M) by simp]
  exact A.valuation_le_one _

lemma val_alpha {j α : M} (hj : A.valuation j ≤ 1) (h3 : A.valuation (3 : M) = 1)
    (hjα : j * (α ^ 3 - 27) = α ^ 3 * (α ^ 3 - 24) ^ 3) :
    A.valuation α ≤ 1 ∧ A.valuation (α ^ 3 - 27) = 1 := by
  have h27 : A.valuation (27 : M) = 1 := by
    rw [show (27 : M) = 3 ^ 3 by norm_num, Valuation.map_pow, h3, one_pow]
  have h24 : A.valuation (24 : M) ≤ 1 := val_natCast_le A 24

  have hle : A.valuation α ≤ 1 := by
    by_contra h
    push Not at h
    have h3α : 1 < A.valuation α ^ 3 := one_lt_pow₀ h (by norm_num)
    have hα27 : A.valuation (α ^ 3 - 27) = A.valuation α ^ 3 := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, Valuation.map_pow]
      rw [Valuation.map_neg, h27, Valuation.map_pow]; exact h3α
    have hα24 : A.valuation (α ^ 3 - 24) = A.valuation α ^ 3 := by
      rw [sub_eq_add_neg, Valuation.map_add_eq_of_lt_left, Valuation.map_pow]
      rw [Valuation.map_neg, Valuation.map_pow]; exact lt_of_le_of_lt h24 h3α
    have hL : A.valuation (j * (α ^ 3 - 27)) ≤ A.valuation α ^ 3 := by
      rw [Valuation.map_mul, hα27]
      calc A.valuation j * A.valuation α ^ 3 ≤ 1 * A.valuation α ^ 3 := mul_le_mul_left hj _
        _ = A.valuation α ^ 3 := one_mul _
    have hR : A.valuation (α ^ 3 * (α ^ 3 - 24) ^ 3) = A.valuation α ^ 12 := by
      rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_pow, hα24, ← pow_mul, ← pow_add]
    rw [hjα, hR] at hL
    have : A.valuation α ^ 3 < A.valuation α ^ 12 := pow_lt_pow_right₀ h (by norm_num)
    exact absurd (lt_of_le_of_lt hL this) (lt_irrefl _)
  refine ⟨hle, ?_⟩

  have hle27 : A.valuation (α ^ 3 - 27) ≤ 1 := by
    rw [sub_eq_add_neg]
    refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hle
    · rw [Valuation.map_neg, h27]
  rcases lt_or_eq_of_le hle27 with h | h
  · exfalso

    set m : M := α ^ 3 - 27 with hm
    have hα3 : α ^ 3 = 27 + m := by rw [hm]; ring
    have h1 : A.valuation (27 + m) = 1 := by
      rw [Valuation.map_add_eq_of_lt_left, h27]; rw [h27]; exact h
    have h2 : A.valuation (3 + m) = 1 := by
      rw [Valuation.map_add_eq_of_lt_left, h3]; rw [h3]; exact h
    have hR : A.valuation (α ^ 3 * (α ^ 3 - 24) ^ 3) = 1 := by
      rw [hα3, show (27 : M) + m - 24 = 3 + m by ring, Valuation.map_mul, Valuation.map_pow, h1, h2,
        one_pow, one_mul]
    have hL : A.valuation (j * (α ^ 3 - 27)) < 1 := by
      rw [Valuation.map_mul]
      calc A.valuation j * A.valuation (α ^ 3 - 27) ≤ 1 * A.valuation (α ^ 3 - 27) :=
            mul_le_mul_left hj _
        _ = A.valuation (α ^ 3 - 27) := one_mul _
        _ < 1 := h
    rw [hjα, hR] at hL
    exact lt_irrefl _ hL
  · exact h

end Val

section Flex

variable [DecidableEq M] (E : WeierstrassCurve M) [E.IsElliptic]

lemma flex_of_order_three {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 ∧
      ((3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃)) ^ 2 +
        E.a₁ * ((3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃)) -
        E.a₂ = 3 * x₀ := by
  have h3 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := by
    rw [← h3P, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  have h2P : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = -Point.some x₀ y₀ hP :=
    eq_neg_of_add_eq_zero_left h3
  have hnegY : E.toAffine.negY x₀ y₀ = -y₀ - E.a₁ * x₀ - E.a₃ := rfl
  have hy : y₀ ≠ E.toAffine.negY x₀ y₀ := by
    intro hy
    have h0 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  have hD : y₀ - E.toAffine.negY x₀ y₀ = 2 * y₀ + E.a₁ * x₀ + E.a₃ := by rw [hnegY]; ring
  have hd : 2 * y₀ + E.a₁ * x₀ + E.a₃ ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy
  refine ⟨hd, ?_⟩
  rw [Point.add_self_of_Y_ne hy, Affine.Point.neg_some] at h2P
  have hX := (Point.some.inj h2P).1
  rw [Affine.slope_of_Y_ne rfl hy, hD, Affine.addX] at hX
  have e1 : E.toAffine.a₁ = E.a₁ := rfl
  have e2 : E.toAffine.a₂ = E.a₂ := rfl
  have e4 : E.toAffine.a₄ = E.a₄ := rfl
  rw [e1, e2, e4] at hX
  linear_combination hX

end Flex

-- The pin's `haveI` registers the `IsElliptic` instance of `⟨α₀, 0, 1, 0, 0⟩` that
-- `j_deuring_mul` needs; the linter's `have` would drop it.
set_option linter.style.haveILetI false in
theorem main [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype := by
  obtain ⟨hd, hflex⟩ := flex_of_order_three E hP h3P
  set d : M := 2 * y₀ + E.a₁ * x₀ + E.a₃ with hd_def
  set n : M := 3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀ with hn_def
  set m : M := n / d with hm_def
  have hmd : m * d = n := div_mul_cancel₀ _ hd
  have hc0 : c ≠ 0 := by
    intro h; apply hd; rw [← hc, h]; ring
  have heq : y₀ ^ 2 + E.a₁ * x₀ * y₀ + E.a₃ * y₀ = x₀ ^ 3 + E.a₂ * x₀ ^ 2 + E.a₄ * x₀ + E.a₆ :=
    (equation_iff x₀ y₀).mp hP.1

  set α₀ : M := (E.a₁ + 2 * m) / c with hα₀
  set κ : VariableChange M := ⟨Units.mk0 c hc0, x₀, m, y₀⟩ with hκ
  have hκE : κ • E = (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M) := by
    ext
    · simp only [variableChange_a₁, hκ, Units.val_inv_eq_inv_val, Units.val_mk0, hα₀]
      field_simp
    · simp only [variableChange_a₂, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₂ - m * E.a₁ + 3 * x₀ - m ^ 2 = 0 by linear_combination -hflex, mul_zero]
    · simp only [variableChange_a₃, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₃ + x₀ * E.a₁ + 2 * y₀ = c ^ 3 by rw [hc]; ring, inv_pow,
        inv_mul_cancel₀ (pow_ne_zero 3 hc0)]
    · simp only [variableChange_a₄, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₄ - m * E.a₃ + 2 * x₀ * E.a₂ - (y₀ + x₀ * m) * E.a₁ + 3 * x₀ ^ 2 - 2 * m * y₀
        = n - m * d by rw [hn_def, hd_def]; ring, hmd, sub_self, mul_zero]
    · simp only [variableChange_a₆, hκ, Units.val_inv_eq_inv_val, Units.val_mk0]
      rw [show E.a₆ + x₀ * E.a₄ + x₀ ^ 2 * E.a₂ + x₀ ^ 3 - y₀ * E.a₃ - y₀ ^ 2 - x₀ * y₀ * E.a₁ = 0 by
        linear_combination -heq, mul_zero]

  have h3M : A.valuation (3 : M) = 1 := by
    have := (A.valuation_eq_one_iff (3 : A)).mp h3; exact this
  haveI : (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M).IsElliptic := by rw [← hκE]; infer_instance
  have hjE : E.j = (⟨α₀, 0, 1, 0, 0⟩ : WeierstrassCurve M).j := by
    have h1 : (κ • E).j = E.j := variableChange_j E κ
    have h2' : ∀ (V₁ V₂ : WeierstrassCurve M) [V₁.IsElliptic] [V₂.IsElliptic], V₁ = V₂ → V₁.j = V₂.j := by
      rintro V₁ V₂ _ _ rfl; rfl
    rw [← h1]; exact h2' _ _ hκE
  have hjα : E.j * (α₀ ^ 3 - 27) = α₀ ^ 3 * (α₀ ^ 3 - 24) ^ 3 := by
    rw [hjE]; exact j_deuring_mul α₀
  obtain ⟨hvα, hvΔ⟩ := val_alpha A ((A.valuation_le_one_iff _).mpr hj) h3M hjα
  have hαA : α₀ ∈ A := (A.valuation_le_one_iff _).mp hvα
  set α : A := ⟨α₀, hαA⟩ with hα
  refine ⟨α, κ, ?_, rfl, rfl, rfl, rfl, ?_⟩
  · rw [deuring_Δ, A.valuation_eq_one_iff]
    show A.valuation ((α₀) ^ 3 - 27) = 1
    exact hvΔ
  · rw [hκE, deuring_map]; rfl

end DeuringLocal

/-- At a 3-torsion point with a cube `y`-derivative, a variable change over the valuation ring puts
the curve in Deuring form `y² = x³ + αx` with unit discriminant. -/
theorem exists_variableChange_eq_deuring_of_isUnit_three
    {M : Type u} [Field M] [DecidableEq M] (A : ValuationSubring M) (h3 : IsUnit (3 : A))
    (E : WeierstrassCurve M) [E.IsElliptic] (hj : E.j ∈ A)
    {x₀ y₀ : M} (hP : E.toAffine.Nonsingular x₀ y₀) (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0)
    {c : M} (hc : c ^ 3 = 2 * y₀ + E.a₁ * x₀ + E.a₃) :
    ∃ (α : A) (κ : VariableChange M),
      IsUnit (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).Δ ∧
      (κ.u : M) = c ∧ κ.r = x₀ ∧
      κ.s = (3 * x₀ ^ 2 + 2 * E.a₂ * x₀ + E.a₄ - E.a₁ * y₀) / (2 * y₀ + E.a₁ * x₀ + E.a₃) ∧
      κ.t = y₀ ∧
      κ • E = (⟨α, 0, 1, 0, 0⟩ : WeierstrassCurve A).map A.subtype :=
  DeuringLocal.main A h3 E hj hP h3P hc

namespace DeuringCharTwo

variable {M : Type*} [Field M]

section Val

variable (A : ValuationSubring M)

lemma val_lt_one_of_z {t z : M} (ht : A.valuation t < 1) (hz : z ^ 4 = t * z + t) :
    A.valuation z < 1 := by
  by_contra h
  push Not at h

  have h1 : A.valuation (t * z + t) < A.valuation z := by
    apply Valuation.map_add_lt
    · rw [Valuation.map_mul]
      calc A.valuation t * A.valuation z < 1 * A.valuation z :=
            mul_lt_mul_of_pos_right ht (lt_of_lt_of_le zero_lt_one h)
        _ = A.valuation z := one_mul _
    · exact lt_of_lt_of_le ht h
  have h2 : A.valuation z ≤ A.valuation (z ^ 4) := by
    rw [Valuation.map_pow]
    calc A.valuation z = A.valuation z * 1 := (mul_one _).symm
      _ ≤ A.valuation z * A.valuation z ^ 3 :=
          mul_le_mul_right (one_le_pow₀ h) _
      _ = A.valuation z ^ 4 := (pow_succ' _ 3).symm
  rw [hz] at h2
  exact absurd (lt_of_le_of_lt h2 h1) (lt_irrefl _)

lemma val_eq_one_of_eta {z η : M} (hz : A.valuation z ≤ 1) (hη : η ^ 2 + z * η + 1 = 0) :
    A.valuation η = 1 := by
  rcases lt_trichotomy (A.valuation η) 1 with h | h | h
  ·
    exfalso
    have h1 : (1 : M) = -(η ^ 2 + z * η) := by linear_combination hη
    have h2 : A.valuation (η ^ 2 + z * η) < 1 := by
      apply Valuation.map_add_lt
      · rw [Valuation.map_pow]
        exact pow_lt_one₀ zero_le h (by norm_num)
      · rw [Valuation.map_mul]
        calc A.valuation z * A.valuation η ≤ 1 * A.valuation η := mul_le_mul_left hz _
          _ = A.valuation η := one_mul _
          _ < 1 := h
    have h3 : A.valuation (1 : M) < 1 := by rw [h1, Valuation.map_neg]; exact h2
    rw [Valuation.map_one] at h3
    exact lt_irrefl _ h3
  · exact h
  ·
    exfalso
    have h1 : η ^ 2 = -(z * η + 1) := by linear_combination hη
    have hη0 : 0 < A.valuation η := lt_trans zero_lt_one h
    have h2 : A.valuation (z * η + 1) < A.valuation η ^ 2 := by
      apply Valuation.map_add_lt
      · rw [Valuation.map_mul]
        calc A.valuation z * A.valuation η ≤ 1 * A.valuation η := mul_le_mul_left hz _
          _ = A.valuation η := one_mul _
          _ = A.valuation η * 1 := (mul_one _).symm
          _ < A.valuation η * A.valuation η := mul_lt_mul_of_pos_left h hη0
          _ = A.valuation η ^ 2 := (sq _).symm
      · rw [Valuation.map_one]
        exact one_lt_pow₀ h (by norm_num)
    have h3 : A.valuation (η ^ 2) < A.valuation η ^ 2 := by
      rw [h1, Valuation.map_neg]; exact h2
    rw [Valuation.map_pow] at h3
    exact lt_irrefl _ h3

end Val

section Group

variable [CharP M 2] [DecidableEq M]

lemma psi3_of_order_three {t x₀ y₀ : M}
    (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    t * x₀ ≠ 0 ∧ x₀ ^ 4 + t ^ 2 * x₀ ^ 3 + t ^ 7 = 0 ∧ y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  have heq : y₀ ^ 2 + t * x₀ * y₀ = x₀ ^ 3 + t ^ 5 := by
    have h := (equation_iff x₀ y₀).mp hP.1
    have e1 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ = t := rfl
    have e2 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ = 0 := rfl
    have e3 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₃ = 0 := rfl
    have e4 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₄ = 0 := rfl
    have e6 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₆ = t ^ 5 := rfl
    rw [e1, e2, e3, e4, e6] at h
    linear_combination h

  have h3 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := by
    rw [← h3P, show (3 : ℕ) = 2 + 1 from rfl, succ_nsmul, two_nsmul]
  have h2P : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = -Point.some x₀ y₀ hP :=
    eq_neg_of_add_eq_zero_left h3
  have hnegY : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ = -y₀ - t * x₀ := by
    rw [Affine.negY]
    show -y₀ - t * x₀ - 0 = -y₀ - t * x₀
    rw [sub_zero]

  have hy : y₀ ≠ (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ := by
    intro hy
    have h0 : Point.some x₀ y₀ hP + Point.some x₀ y₀ hP = 0 := Point.add_self_of_Y_eq hy
    rw [h0] at h2P
    exact Point.some_ne_zero _ (neg_eq_zero.mp h2P.symm)
  have hD : y₀ - (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.negY x₀ y₀ = t * x₀ := by
    rw [hnegY]; linear_combination y₀ * h2
  have htx : t * x₀ ≠ 0 := by rw [← hD]; exact sub_ne_zero.mpr hy

  rw [Point.add_self_of_Y_ne hy, Affine.Point.neg_some] at h2P
  have hX := (Point.some.inj h2P).1
  set L := (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.slope x₀ x₀ y₀ y₀ with hL
  have hLD : L * (t * x₀) = 3 * x₀ ^ 2 - t * y₀ := by
    rw [hL, Affine.slope_of_Y_ne rfl hy, hD]
    have : (3 * x₀ ^ 2 + 2 * (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ * x₀ +
        (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₄ -
        (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ * y₀) = 3 * x₀ ^ 2 - t * y₀ := by
      show 3 * x₀ ^ 2 + 2 * 0 * x₀ + 0 - t * y₀ = 3 * x₀ ^ 2 - t * y₀
      ring
    rw [this, div_mul_cancel₀ _ htx]
  have hX' : L ^ 2 + t * L - 2 * x₀ = x₀ := by
    have h := hX
    rw [Affine.addX] at h
    have e1 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₁ = t := rfl
    have e2 : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.a₂ = 0 := rfl
    rw [e1, e2] at h
    linear_combination h
  refine ⟨htx, ?_, heq⟩

  have key : (L * (t * x₀)) ^ 2 + t * (t * x₀) * (L * (t * x₀)) - 2 * x₀ * (t * x₀) ^ 2 =
      x₀ * (t * x₀) ^ 2 := by
    have := congrArg (fun w => w * (t * x₀) ^ 2) hX'
    linear_combination this
  rw [hLD] at key

  linear_combination key - t ^ 2 * heq +
    (4 * x₀ ^ 4 - 3 * t * x₀ ^ 2 * y₀ + t ^ 2 * x₀ ^ 3 - t ^ 3 * x₀ * y₀ - t ^ 2 * x₀ ^ 3
      + 2 * x₀ * t ^ 3 * y₀ + 6 * x₀ ^ 2 * t * y₀ - 8 * x₀ ^ 4) * h2

end Group

theorem main [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 := by
  have h2 : (2 : M) = 0 := CharP.cast_eq_zero M 2
  obtain ⟨htx, hpsi, heq⟩ := psi3_of_order_three hP h3P
  have hx0 : x₀ ≠ 0 := fun h => htx (by rw [h, mul_zero])

  have hvt : A.valuation t < 1 := by
    have : (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr htu
    exact (A.valuation_lt_one_iff ⟨t, ht⟩).mp this

  set z : M := t ^ 2 / x₀ with hz_def
  set η : M := t * y₀ / x₀ ^ 2 with hη_def
  have hzx : z * x₀ = t ^ 2 := by rw [hz_def]; exact div_mul_cancel₀ _ hx0
  have hηx : η * x₀ ^ 2 = t * y₀ := by rw [hη_def]; exact div_mul_cancel₀ _ (pow_ne_zero 2 hx0)
  have hz : z ^ 4 = t * z + t := by
    apply mul_right_cancel₀ (pow_ne_zero 4 hx0)
    linear_combination (z ^ 3 * x₀ ^ 3 + t ^ 2 * z ^ 2 * x₀ ^ 2 + t ^ 4 * z * x₀ + t ^ 6 - t * x₀ ^ 3) * hzx
      - t * hpsi + t ^ 8 * h2
  have hη : η ^ 2 + z * η + 1 = 0 := by
    have h1 : (η ^ 2 + z * η + 1) * x₀ ^ 4 = 0 := by
      linear_combination (η * x₀ ^ 2 + t * y₀ + x₀ * t ^ 2) * hηx + (x₀ * η * x₀ ^ 2) * hzx +
        hpsi + t ^ 2 * heq
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd h (pow_ne_zero 4 hx0)
  have hvz : A.valuation z < 1 := val_lt_one_of_z A hvt hz
  have hvη : A.valuation η = 1 := val_eq_one_of_eta A hvz.le hη
  have hzA : z ∈ A := (A.valuation_le_one_iff z).mp hvz.le
  have hηA : η ∈ A := (A.valuation_le_one_iff η).mp hvη.le

  have hv1z : A.valuation (1 + z) = 1 := by
    rw [Valuation.map_add_eq_of_lt_left]
    · exact Valuation.map_one _
    · rw [Valuation.map_one]; exact hvz
  have h1zA : 1 + z ∈ A := add_mem A.one_mem hzA
  let w : A := ⟨(1 + z) * η ^ 4, mul_mem h1zA (pow_mem hηA 4)⟩
  have hw : IsUnit w := by
    rw [A.valuation_eq_one_iff]
    show A.valuation ((1 + z) * η ^ 4) = 1
    rw [Valuation.map_mul, Valuation.map_pow, hv1z, hvη, one_pow, one_mul]

  refine ⟨η + 1, (hw.unit⁻¹ : Aˣ), (hw.unit⁻¹).isUnit, ?_⟩
  have hμ2 : (η + 1) ^ 2 = z * η := by
    linear_combination hη + (η - z * η) * h2
  have hμ8 : (η + 1) ^ 8 = t * ((1 + z) * η ^ 4) := by
    calc (η + 1) ^ 8 = ((η + 1) ^ 2) ^ 4 := by ring
      _ = z ^ 4 * η ^ 4 := by rw [hμ2]; ring
      _ = t * ((1 + z) * η ^ 4) := by rw [hz]; ring
  have hwM : ((hw.unit⁻¹ : Aˣ) : A) * w = 1 := hw.unit.inv_mul
  have hwM' : (((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4) = 1 :=
    congrArg Subtype.val hwM
  calc t = t * ((((hw.unit⁻¹ : Aˣ) : A) : M) * ((1 + z) * η ^ 4)) := by rw [hwM', mul_one]
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (t * ((1 + z) * η ^ 4)) := by ring
    _ = (((hw.unit⁻¹ : Aˣ) : A) : M) * (η + 1) ^ 8 := by rw [hμ8]

end DeuringCharTwo

/-- The characteristic-2 `j = 0` case of the same normal form: `t = u * μ ^ 8`. -/
theorem exists_isUnit_mul_pow_eight_eq_of_charTwo
    {M : Type u} [Field M] [CharP M 2] [DecidableEq M] (A : ValuationSubring M)
    {t : M} (ht : t ∈ A) (htu : ¬ IsUnit (⟨t, ht⟩ : A)) (ht0 : t ≠ 0)
    {x₀ y₀ : M} (hP : (⟨t, 0, 0, 0, t ^ 5⟩ : WeierstrassCurve M).toAffine.Nonsingular x₀ y₀)
    (h3P : (3 : ℕ) • Point.some x₀ y₀ hP = 0) :
    ∃ (μ : M) (u : A), IsUnit u ∧ t = u * μ ^ 8 :=
  DeuringCharTwo.main A ht htu ht0 hP h3P

/-- A cube root of unity acts trivially on `y² = x³ + B`. -/
theorem variableChange_mk_smul_eq_self_of_pow_three_eq_one
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 3 = 1) (B : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, 0, B⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, 0, B⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have h3 : ((u⁻¹ : Rˣ) : R) ^ 3 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 3 = ((u⁻¹ : Rˣ) : R) ^ 3 * (u : R) ^ 3 := by rw [hu, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 3 := by ring
      _ = 1 := by rw [h1, one_pow]
  have h6 : ((u⁻¹ : Rˣ) : R) ^ 6 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 6 = (((u⁻¹ : Rˣ) : R) ^ 3) ^ 2 := by ring
      _ = 1 := by rw [h3, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · ring
  · linear_combination B * h6

/-- A square root of `-1` acts trivially on `y² = x³ + Ax`. -/
theorem variableChange_mk_smul_eq_self_of_sq_eq_neg_one
    {R : Type*} [CommRing R] (u : Rˣ) (hu : (u : R) ^ 2 = -1) (A : R) :
    (⟨u, 0, 0, 0⟩ : WeierstrassCurve.VariableChange R) • (⟨0, 0, 0, A, 0⟩ : WeierstrassCurve R) =
      ⟨0, 0, 0, A, 0⟩ := by
  have h1 : ((u⁻¹ : Rˣ) : R) * (u : R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu4 : (u : R) ^ 4 = 1 := by
    calc (u : R) ^ 4 = ((u : R) ^ 2) ^ 2 := by ring
      _ = 1 := by rw [hu]; ring
  have h4 : ((u⁻¹ : Rˣ) : R) ^ 4 = 1 := by
    calc ((u⁻¹ : Rˣ) : R) ^ 4 = ((u⁻¹ : Rˣ) : R) ^ 4 * (u : R) ^ 4 := by rw [hu4, mul_one]
      _ = (((u⁻¹ : Rˣ) : R) * (u : R)) ^ 4 := by ring
      _ = 1 := by rw [h1, one_pow]
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  · ring
  · ring
  · ring
  · linear_combination A * h4
  · ring

end WeierstrassCurve
