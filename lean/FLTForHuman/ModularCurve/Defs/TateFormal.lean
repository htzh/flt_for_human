/-
  The formal Tate curve: `tateB`, the integral `q`-expansions `tateA4` / `tateA6`
  and `eisenstein6`, the Weierstrass curves `tatePowerSeries` (over
  `PowerSeries ℤ`) and `tateLaurent` (over `LaurentSeries K`), the coefficient
  ring map `laurentOfInt`, and the ellipticity instance
  `instIsElliptic_tateLaurent`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_TateFormal.lean` (160 lines).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_TateFormal.lean

  Transcribed whole and verbatim (playbook §2.3): the cluster's `S_` files reach
  this module transitively through `Def_ModularCurve_TateSlots`, but the pin's
  other consumers (`Def_ModularCurve_TatePoint`, `Def_ModularCurve_TateVeluRing`,
  `Theorems/Thm_ModularCurve_Delta_tatePowerSeries`) name `tateA4`, `tateA6`
  and `tatePowerSeries` directly, so the whole node is homed rather than the
  `S_`-visible block. The pin's import of `Def_ModularCurve_JqCoeff` is kept as
  the already-ported `Defs/JqCoeff.lean`.

  Names are FLT's verbatim; `PowerSeries`, `HahnSeries`, `WeierstrassCurve`,
  `LaurentSeries` are mathlib's. No pin declaration in this module is `private`,
  so no promotion is owed here.

  ## The `c₄` of the formal Tate curve (`c4_tateLaurent`)

  `tateLaurent K = tatePowerSeries.map (laurentOfInt K)`, `c₄` is natural under a
  change of coefficient ring (`WeierstrassCurve.map_c₄`) and
  `tatePowerSeries.c₄ = 1 - 48 · tateA4 = eisenstein4` on the nose, so the
  Laurent formal Tate curve's `c₄` is the integral `q`-expansion `eisenstein4`
  pushed along `Int.castRingHom K`. The two ingredients are proven `have`
  locally: they have no consumer outside this headline.

  FLT provenance, pinned `aa2d8b3`:
  `Theorems/Thm_ModularCurve_c4_tateLaurent.lean` and
  `P2M/Sol/S_ModularCurve_c4_tateLaurent.lean`.

  spec-pin: Definitions/Def_ModularCurve_TateFormal.lean
  spec-pin: Theorems/Thm_ModularCurve_c4_tateLaurent.lean
  spec-pin: P2M/Sol/S_ModularCurve_c4_tateLaurent.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

def tateB (d : ℕ) : ℤ := (5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5) / 12

theorem twelve_mul_tateB (d : ℕ) : 12 * tateB d = 5 * (d : ℤ) ^ 3 + 7 * (d : ℤ) ^ 5 := by
  have key : ∀ c : ℤ, (12 : ℤ) ∣ 5 * c ^ 3 + 7 * c ^ 5 := by
    intro c
    have hr : c % 12 ≡ c [ZMOD 12] := Int.mod_modEq c 12
    have hcong : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡ 5 * c ^ 3 + 7 * c ^ 5 [ZMOD 12] :=
      ((hr.pow 3).mul_left 5).add ((hr.pow 5).mul_left 7)
    have h12 : c % 12 = 0 ∨ c % 12 = 1 ∨ c % 12 = 2 ∨ c % 12 = 3 ∨ c % 12 = 4 ∨ c % 12 = 5 ∨
        c % 12 = 6 ∨ c % 12 = 7 ∨ c % 12 = 8 ∨ c % 12 = 9 ∨ c % 12 = 10 ∨ c % 12 = 11 := by
      omega
    have hres : 5 * (c % 12) ^ 3 + 7 * (c % 12) ^ 5 ≡ 0 [ZMOD 12] := by
      rcases h12 with h | h | h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
    exact Int.modEq_zero_iff_dvd.mp (hcong.symm.trans hres)
  rw [tateB]
  exact Int.mul_ediv_cancel' (key _)

def tateA4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3)

def tateA6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => -∑ d ∈ n.divisors, tateB d

def eisenstein6 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5

theorem coeff_tateA4 (n : ℕ) :
    PowerSeries.coeff n tateA4 = -∑ d ∈ n.divisors, (5 * (d : ℤ) ^ 3) :=
  PowerSeries.coeff_mk n _

theorem coeff_tateA6 (n : ℕ) :
    PowerSeries.coeff n tateA6 = -∑ d ∈ n.divisors, tateB d :=
  PowerSeries.coeff_mk n _

theorem coeff_zero_tateA4 : PowerSeries.coeff 0 tateA4 = 0 := by
  rw [coeff_tateA4, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem coeff_zero_tateA6 : PowerSeries.coeff 0 tateA6 = 0 := by
  rw [coeff_tateA6, Nat.divisors_zero, Finset.sum_empty, neg_zero]

theorem constantCoeff_tateA4 : PowerSeries.constantCoeff tateA4 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA4

theorem constantCoeff_tateA6 : PowerSeries.constantCoeff tateA6 = 0 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact coeff_zero_tateA6

theorem constantCoeff_eisenstein6 : PowerSeries.constantCoeff eisenstein6 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein6]

theorem coeff_one_tateA4 : PowerSeries.coeff 1 tateA4 = -5 := by
  rw [coeff_tateA4, Nat.divisors_one, Finset.sum_singleton]
  norm_num

theorem coeff_one_tateA6 : PowerSeries.coeff 1 tateA6 = -1 := by
  have h : tateB 1 = 1 := by norm_num [tateB]
  rw [coeff_tateA6, Nat.divisors_one, Finset.sum_singleton, h]

def tatePowerSeries : WeierstrassCurve (PowerSeries ℤ) := ⟨1, 0, 0, tateA4, tateA6⟩

@[simp] theorem tatePowerSeries_a₁ : tatePowerSeries.a₁ = 1 := rfl
@[simp] theorem tatePowerSeries_a₂ : tatePowerSeries.a₂ = 0 := rfl
@[simp] theorem tatePowerSeries_a₃ : tatePowerSeries.a₃ = 0 := rfl
@[simp] theorem tatePowerSeries_a₄ : tatePowerSeries.a₄ = tateA4 := rfl
@[simp] theorem tatePowerSeries_a₆ : tatePowerSeries.a₆ = tateA6 := rfl

def laurentOfInt (K : Type*) [CommRing K] : PowerSeries ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp (PowerSeries.map (Int.castRingHom K))

theorem laurentOfInt_apply (K : Type*) [CommRing K] (f : PowerSeries ℤ) :
    laurentOfInt K f = HahnSeries.ofPowerSeries ℤ K (f.map (Int.castRingHom K)) := rfl

def tateLaurent (K : Type*) [CommRing K] : WeierstrassCurve (LaurentSeries K) :=
  tatePowerSeries.map (laurentOfInt K)

@[simp] theorem tateLaurent_a₄ (K : Type*) [CommRing K] :
    (tateLaurent K).a₄ = laurentOfInt K tateA4 := rfl

@[simp] theorem tateLaurent_a₆ (K : Type*) [CommRing K] :
    (tateLaurent K).a₆ = laurentOfInt K tateA6 := rfl

instance instIsElliptic_tateLaurent (K : Type*) [CommRing K] : (tateLaurent K).IsElliptic := by
  constructor
  have hΔeq : tatePowerSeries.Δ =
      -tateA6 + tateA4 ^ 2 - PowerSeries.C 64 * tateA4 ^ 3 - PowerSeries.C 432 * tateA6 ^ 2
        + PowerSeries.C 72 * (tateA4 * tateA6) := by
    rw [show (PowerSeries.C (64 : ℤ)) = (64 : PowerSeries ℤ) from map_ofNat _ 64,
      show (PowerSeries.C (432 : ℤ)) = (432 : PowerSeries ℤ) from map_ofNat _ 432,
      show (PowerSeries.C (72 : ℤ)) = (72 : PowerSeries ℤ) from map_ofNat _ 72]
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈, tatePowerSeries_a₁, tatePowerSeries_a₂, tatePowerSeries_a₃,
      tatePowerSeries_a₄, tatePowerSeries_a₆]
    ring
  have hc0 : PowerSeries.constantCoeff tatePowerSeries.Δ = 0 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, map_mul, map_pow, PowerSeries.constantCoeff_C,
      constantCoeff_tateA4, constantCoeff_tateA6]
    ring
  have hmul1 : ∀ f g : PowerSeries ℤ, PowerSeries.coeff 1 (f * g) =
      PowerSeries.coeff 0 f * PowerSeries.coeff 1 g +
        PowerSeries.coeff 1 f * PowerSeries.coeff 0 g := by
    intro f g
    rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    norm_num
  have h420 : PowerSeries.coeff 0 (tateA4 ^ 2) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_pow, constantCoeff_tateA4]
    norm_num
  have hsq4 : PowerSeries.coeff 1 (tateA4 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA4]
    norm_num
  have hsq6 : PowerSeries.coeff 1 (tateA6 ^ 2) = 0 := by
    rw [pow_two, hmul1, coeff_zero_tateA6]
    norm_num
  have hcb4 : PowerSeries.coeff 1 (tateA4 ^ 3) = 0 := by
    rw [show tateA4 ^ 3 = tateA4 ^ 2 * tateA4 from pow_succ tateA4 2, hmul1, h420, hsq4,
      coeff_zero_tateA4]
    norm_num
  have hprod : PowerSeries.coeff 1 (tateA4 * tateA6) = 0 := by
    rw [hmul1, coeff_zero_tateA4, coeff_zero_tateA6]
    norm_num
  have hc1 : PowerSeries.coeff 1 tatePowerSeries.Δ = 1 := by
    rw [hΔeq]
    simp only [map_add, map_sub, map_neg, PowerSeries.coeff_C_mul, hsq4, hsq6, hcb4, hprod,
      coeff_one_tateA6]
    norm_num
  obtain ⟨u, hXu⟩ : (PowerSeries.X : PowerSeries ℤ) ∣ tatePowerSeries.Δ :=
    PowerSeries.X_dvd_iff.mpr hc0
  have h1u : PowerSeries.coeff 1 tatePowerSeries.Δ = PowerSeries.constantCoeff u := by
    rw [hXu, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      show (1 : ℕ) = 0 + 1 from rfl, PowerSeries.coeff_succ_X_mul]
  have hu : IsUnit u := by
    rw [PowerSeries.isUnit_iff_constantCoeff, ← h1u, hc1]
    exact isUnit_one
  have hΔL : (tateLaurent K).Δ = laurentOfInt K tatePowerSeries.Δ := by
    rw [tateLaurent, WeierstrassCurve.map_Δ]
  rw [hΔL, hXu, map_mul]
  refine IsUnit.mul ?_ (hu.map (laurentOfInt K))
  have hX : laurentOfInt K PowerSeries.X = HahnSeries.single (1 : ℤ) 1 := by
    rw [laurentOfInt_apply, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
  rw [hX]
  exact ⟨⟨HahnSeries.single (1 : ℤ) 1, HahnSeries.single (-1 : ℤ) 1,
    by simp [HahnSeries.single_mul_single], by simp [HahnSeries.single_mul_single]⟩, rfl⟩

theorem c4_tateLaurent (K : Type*) [CommRing K] :
    (tateLaurent K).c₄ = HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) eisenstein4) := by
  have hc4 : tatePowerSeries.c₄ = 1 - 48 * tateA4 := by
    rw [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, tatePowerSeries_a₁,
      tatePowerSeries_a₂, tatePowerSeries_a₃, tatePowerSeries_a₄]
    ring
  have hone : (1 - 48 * tateA4 : PowerSeries ℤ) = eisenstein4 := by
    ext n
    have h48 : (48 : PowerSeries ℤ) * tateA4 = (48 : ℕ) • tateA4 := by
      rw [nsmul_eq_mul, Nat.cast_ofNat]
    rw [map_sub, PowerSeries.coeff_one, eisenstein4, PowerSeries.coeff_mk, h48, map_nsmul,
      coeff_tateA4, nsmul_eq_mul, Nat.cast_ofNat]
    split_ifs with h
    · subst h; simp
    · simp only [zero_sub, mul_neg, neg_neg, Finset.mul_sum]
      exact Finset.sum_congr rfl fun d _ => by ring
  rw [tateLaurent, WeierstrassCurve.map_c₄, hc4, hone, laurentOfInt_apply]

end ModularCurve

end
