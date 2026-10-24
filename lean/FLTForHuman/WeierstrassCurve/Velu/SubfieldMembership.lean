/-
  Subfield membership of the `j`-invariant.

  Two facts, both pure polynomial closure:

  * `j_mem_of_a_mem`: `j(W) ∈ K` for any subfield `K` of the base field containing the
    five coefficients `a₁, a₂, a₃, a₄, a₆` of `W`.  `j = Δ'⁻¹ * c₄³`, and the
    `b`-invariants and `Δ` are integral polynomials in the `a`'s, so `Δ` is a unit of
    `K` and `j` stays in it.

  * `veluQuotient_j_mem_of_mem`: if in addition the summing set `T` has both
    coordinates in `K`, then `j(W/T) ∈ K`.  The Vélu quotient's coefficients are
    `a₄ - 5·ΣT` and `a₆ - b₂·ΣT - 7·ΣU`, so this reduces to the coordinate
    polynomials `veluGx`, `veluGy`, `veluT`, `veluU`, `veluW` preserving `K` and hence
    to the two sum-membership helpers `veluTSum_mem`/`veluWSum_mem`.

  The helpers are `private` (the pin keeps them `private` too, and re-exports them only
  into its own proof namespace); the two headlines are public at the pin's names.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`:
  `Theorems/Thm_WeierstrassCurve_j_mem_of_a_mem.lean` (7 lines) and
  `Theorems/Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem.lean` (11 lines); proofs
  from `P2M/Sol/S_WeierstrassCurve_j_mem_of_a_mem.lean` (32 lines) and
  `P2M/Sol/S_WeierstrassCurve_veluQuotient_j_mem_of_mem.lean` (91 lines).
  The Vélu vocabulary is the port's `WeierstrassCurve/Velu/Defs.lean`.

  spec-pin: Theorems/Thm_WeierstrassCurve_j_mem_of_a_mem.lean
  spec-pin: Theorems/Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem.lean
-/
import FLTForHuman.WeierstrassCurve.Velu.Defs

set_option autoImplicit false

noncomputable section

open WeierstrassCurve

/-- A subfield containing the five coefficients of `W` contains `j(W)`: `j = Δ'⁻¹ * c₄³`,
and `c₄`, `Δ` are integral polynomials in the `a`'s.  Verbatim from
`Theorems/Thm_WeierstrassCurve_j_mem_of_a_mem.lean`. -/
theorem WeierstrassCurve.j_mem_of_a_mem {F : Type*} [Field F] {S : Type*} [SetLike S F]
    [SubfieldClass S F] (W : WeierstrassCurve F) [W.IsElliptic] (K : S)
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K) :
    W.j ∈ K := by
  have hb₂ : W.b₂ ∈ K := by
    rw [b₂]; exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem K 4) h₂)
  have hb₄ : W.b₄ ∈ K := by
    rw [b₄]; exact add_mem (mul_mem (ofNat_mem K 2) h₄) (mul_mem h₁ h₃)
  have hb₆ : W.b₆ ∈ K := by
    rw [b₆]; exact add_mem (pow_mem h₃ 2) (mul_mem (ofNat_mem K 4) h₆)
  have hb₈ : W.b₈ ∈ K := by
    rw [b₈]
    exact sub_mem (add_mem (sub_mem (add_mem (mul_mem (pow_mem h₁ 2) h₆)
      (mul_mem (mul_mem (ofNat_mem K 4) h₂) h₆)) (mul_mem (mul_mem h₁ h₃) h₄))
      (mul_mem h₂ (pow_mem h₃ 2))) (pow_mem h₄ 2)
  have hc₄ : W.c₄ ∈ K := by
    rw [c₄]; exact sub_mem (pow_mem hb₂ 2) (mul_mem (ofNat_mem K 24) hb₄)
  have hΔ : W.Δ ∈ K := by
    rw [Δ]
    exact add_mem (sub_mem (sub_mem (mul_mem (neg_mem (pow_mem hb₂ 2)) hb₈)
      (mul_mem (ofNat_mem K 8) (pow_mem hb₄ 3))) (mul_mem (ofNat_mem K 27) (pow_mem hb₆ 2)))
      (mul_mem (mul_mem (mul_mem (ofNat_mem K 9) hb₂) hb₄) hb₆)
  rw [WeierstrassCurve.j]
  refine mul_mem ?_ (pow_mem hc₄ 3)
  rw [Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ']
  exact inv_mem hΔ

/-! ### Coordinate and sum membership for the Vélu formulas -/

namespace WeierstrassCurve

variable {L : Type*} [CommRing L] {S : Type*} [SetLike S L] [SubringClass S L]
variable (V : WeierstrassCurve L) (A : S)

private theorem veluGx_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluGx x y ∈ A := by
  rw [veluGx]
  exact sub_mem (add_mem (add_mem (mul_mem (ofNat_mem A 3) (pow_mem hx 2))
    (mul_mem (mul_mem (ofNat_mem A 2) h₂) hx)) h₄) (mul_mem h₁ hy)

private theorem veluGy_mem (h₁ : V.a₁ ∈ A) (h₃ : V.a₃ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluGy x y ∈ A := by
  rw [veluGy]
  exact neg_mem (add_mem (add_mem (mul_mem (ofNat_mem A 2) hy) (mul_mem h₁ hx)) h₃)

private theorem veluT_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluT x y ∈ A := by
  rw [veluT]
  exact sub_mem (mul_mem (ofNat_mem A 2) (V.veluGx_mem A h₁ h₂ h₄ hx hy))
    (mul_mem h₁ (V.veluGy_mem A h₁ h₃ hx hy))

private theorem veluU_mem (h₁ : V.a₁ ∈ A) (h₃ : V.a₃ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluU x y ∈ A := by
  rw [veluU]
  exact pow_mem (V.veluGy_mem A h₁ h₃ hx hy) 2

private theorem veluW_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A) (h₄ : V.a₄ ∈ A)
    {x y : L} (hx : x ∈ A) (hy : y ∈ A) : V.veluW x y ∈ A := by
  rw [veluW]
  exact add_mem (V.veluU_mem A h₁ h₃ hx hy)
    (mul_mem hx (V.veluT_mem A h₁ h₂ h₃ h₄ hx hy))

private theorem veluTSum_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A)
    (h₄ : V.a₄ ∈ A) {K : Finset (L × L)} (hK : ∀ P ∈ K, P.1 ∈ A ∧ P.2 ∈ A) :
    V.veluTSum K ∈ A := by
  rw [veluTSum]
  exact sum_mem fun P hP => V.veluT_mem A h₁ h₂ h₃ h₄ (hK P hP).1 (hK P hP).2

private theorem veluWSum_mem (h₁ : V.a₁ ∈ A) (h₂ : V.a₂ ∈ A) (h₃ : V.a₃ ∈ A)
    (h₄ : V.a₄ ∈ A) {K : Finset (L × L)} (hK : ∀ P ∈ K, P.1 ∈ A ∧ P.2 ∈ A) :
    V.veluWSum K ∈ A := by
  rw [veluWSum]
  exact sum_mem fun P hP => V.veluW_mem A h₁ h₂ h₃ h₄ (hK P hP).1 (hK P hP).2

end WeierstrassCurve

-- the proof's `haveI` binds the quotient's elliptic structure as an instance local,
-- which the membership argument consumes through `j_mem_of_a_mem`; the style linter's
-- `have` suggestion does not apply.
set_option linter.style.haveILetI false in
/-- A subfield containing the five coefficients of `W` and both coordinates of every
point of the summing set `T` contains `j(W/T)`.  Verbatim from
`Theorems/Thm_WeierstrassCurve_veluQuotient_j_mem_of_mem.lean`. -/
theorem WeierstrassCurve.veluQuotient_j_mem_of_mem {F : Type*} [Field F] {S : Type*}
    [SetLike S F] [SubfieldClass S F]
    (W : WeierstrassCurve F) (K : S) (T : Finset (F × F))
    (h₁ : W.a₁ ∈ K) (h₂ : W.a₂ ∈ K) (h₃ : W.a₃ ∈ K) (h₄ : W.a₄ ∈ K) (h₆ : W.a₆ ∈ K)
    (hT : ∀ P ∈ T, P.1 ∈ K ∧ P.2 ∈ K) (hΔ : (W.veluQuotient T).Δ ≠ 0) :
    haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (W.veluQuotient T).j ∈ K := by
  haveI : (W.veluQuotient T).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  have ht : W.veluTSum T ∈ K := W.veluTSum_mem K h₁ h₂ h₃ h₄ hT
  have hw : W.veluWSum T ∈ K := W.veluWSum_mem K h₁ h₂ h₃ h₄ hT
  have hb₂ : W.b₂ ∈ K := by
    rw [b₂]; exact add_mem (pow_mem h₁ 2) (mul_mem (ofNat_mem K 4) h₂)
  refine (W.veluQuotient T).j_mem_of_a_mem K ?_ ?_ ?_ ?_ ?_
  · rw [veluQuotient_a₁]; exact h₁
  · rw [veluQuotient_a₂]; exact h₂
  · rw [veluQuotient_a₃]; exact h₃
  · rw [veluQuotient_a₄]; exact sub_mem h₄ (mul_mem (ofNat_mem K 5) ht)
  · rw [veluQuotient_a₆]
    exact sub_mem (sub_mem h₆ (mul_mem hb₂ ht)) (mul_mem (ofNat_mem K 7) hw)

end
