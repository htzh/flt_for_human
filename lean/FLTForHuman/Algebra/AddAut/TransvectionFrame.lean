/-
  The frame argument for subgroups of `AddAut (ZMod M × ZMod M)`:

      if `H` acts transitively up to integer multiples on the elements of additive order
      `M`, and contains a "transvection-like" `t` with
      `t (1,0) = ε • (1,0)`, `t (0,1) = ε • (1,1)`, `ε = ±1`, then `H` acts transitively
      on those elements: `∃ h ∈ H, h v = w`.

  The port of the pin leaf
  `AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem`
  (`Theorems/Thm_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean`
  and `P2M/Sol/S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean`,
  pinned `aa2d8b3`; 370 pin lines). The statement is the wrapper's verbatim, the proof
  the `S_` file's `solution` body (`main M H htrans ht v w hv hw`); the
  pin's `solution` wrapper is not ported and the pin's inner namespace
  `P2MKcIgusaGroup` is kept verbatim.

  The mathematics is a two-generator normal form: `frame` records a pair
  `(t, ℓ) ∈ H` with `t (x,y) = (e (x+y), e y)` and `ℓ (x,y) = (e x, e (z x + y))`,
  `gS = t^k ℓ t^k` (`k z = -1`) is an involution sending `(1,0) ↦ (0, e z)` and
  `(0,1) ↦ (e k, 0)`, and the reachable set `R H x` is closed under `+`, under unit
  scaling, and under negation — enough to move any element of additive order `M` to any
  other.

  Assumes: mathlib `v4.34.0`, plus the port's own gate module
  `Algebra/AddAut/Compat.lean`. The pin's statement cannot even be *stated* without a
  `Group (AddAut A)` instance: `Subgroup (AddAut (ZMod M × ZMod M))` needs it, and from
  mathlib `v4.33.0` on `AddAut` carries only an **additive** group structure ("We give
  `AddAut M` the structure of an additive group rather than a multiplicative group",
  `Mathlib/Algebra/Group/End.lean`); `#check @AddAut.instGroup` fails on `v4.34.0`. The
  pin restores the multiplicative structure in `Definitions/Def_Compat_Mathlib430.lean`
  block D, which is why its wrapper imports that file — an `rg` over the `S_` file's
  *symbols* cannot see a typeclass instance, so the import is anything but dead. Block D
  is homed verbatim in `Algebra/AddAut/Compat.lean` (17 declarations, 17 ok
  against the pin definition module) and is the only declaration the node consumes from
  it: the proof's three `AddAut.inv_def'` rewrites and the wrapper's `Subgroup` shape.
  The pin's blocks A–C (`Representation`/`Rep` API) and E are not needed by this node and
  are not homed.

  Mathlib-first check (2026-10-20): `rg "addOrderOf.*transvection|IsTransvection" Mathlib/`
  and `rg "exists_mem_apply_eq_of_addOrderOf" Mathlib/` are empty; mathlib has
  `AddAut`/`AddEquiv` and `addOrderOf` but nothing about the reachable-set closure used
  here, so this is a supplement.

  spec-pin: Theorems/Thm_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean
  spec-pin: P2M/Sol/S_AddAut_exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem.lean
-/

import FLTForHuman.Algebra.AddAut.Compat
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.AddAut
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

set_option autoImplicit false

namespace AddAut

variable {M : ℕ} [NeZero M]

theorem smul_eq_val_nsmul (a : ZMod M) (v : ZMod M × ZMod M) : a • v = a.val • v := by
  ext <;> simp [nsmul_eq_mul]

theorem map_smul' (h : AddAut (ZMod M × ZMod M)) (a : ZMod M) (v : ZMod M × ZMod M) :
    h (a • v) = a • h v := by
  rw [smul_eq_val_nsmul, map_nsmul, ← smul_eq_val_nsmul]
omit [NeZero M] in

theorem decomp (v : ZMod M × ZMod M) :
    v = v.1 • ((1, 0) : ZMod M × ZMod M) + v.2 • ((0, 1) : ZMod M × ZMod M) := by
  ext <;> simp

theorem apply_eq (h : AddAut (ZMod M × ZMod M)) (v : ZMod M × ZMod M) :
    h v = v.1 • h (1, 0) + v.2 • h (0, 1) := by
  conv_lhs => rw [decomp v]
  rw [map_add, map_smul', map_smul']

theorem apply_mk (h : AddAut (ZMod M × ZMod M)) (x y : ZMod M) :
    h (x, y) = (x * (h (1, 0)).1 + y * (h (0, 1)).1, x * (h (1, 0)).2 + y * (h (0, 1)).2) := by
  rw [apply_eq]
  ext <;> simp
omit [NeZero M] in

theorem intCast_smul (n : ℤ) (v : ZMod M × ZMod M) : (n : ZMod M) • v = n • v :=
  Int.cast_smul_eq_zsmul (ZMod M) n v
omit [NeZero M] in

theorem natCast_nsmul_eq_zero (v : ZMod M × ZMod M) : M • v = 0 := by
  ext <;> simp [nsmul_eq_mul]
omit [NeZero M] in

theorem addOrderOf_one_zero : addOrderOf ((1, 0) : ZMod M × ZMod M) = M := by
  rw [Prod.addOrderOf]
  simp [ZMod.addOrderOf_one]
omit [NeZero M] in

theorem addOrderOf_zero_one : addOrderOf ((0, 1) : ZMod M × ZMod M) = M := by
  rw [Prod.addOrderOf]
  simp [ZMod.addOrderOf_one]

theorem isUnit_of_addOrderOf_smul (c : ZMod M) (v : ZMod M × ZMod M)
    (h : addOrderOf (c • v) = M) : IsUnit c := by
  have hM : M ≠ 0 := NeZero.ne M
  rw [← ZMod.natCast_zmod_val c, ZMod.isUnit_iff_coprime]
  by_contra hcop
  set g := Nat.gcd c.val M with hg
  have hg1 : g ≠ 1 := hcop
  have hgM : g ∣ M := Nat.gcd_dvd_right _ _
  have hgc : g ∣ c.val := Nat.gcd_dvd_left _ _
  have hgpos : 0 < g := Nat.pos_of_ne_zero (by
    intro h0
    rw [hg, Nat.gcd_eq_zero_iff] at h0
    exact hM h0.2)
  obtain ⟨m, hm⟩ := hgM
  obtain ⟨d, hd⟩ := hgc
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, mul_zero] at hm; exact absurd hm hM
    · exact h0
  have hmlt : m < M := by
    have h2 : 2 ≤ g := by omega
    calc m < 2 * m := by omega
      _ ≤ g * m := Nat.mul_le_mul_right m h2
      _ = M := hm.symm

  have hkill : m • (c • v) = 0 := by
    rw [smul_eq_val_nsmul, ← mul_nsmul', hd, show m * (g * d) = d * (g * m) by ring, ← hm,
      mul_nsmul', natCast_nsmul_eq_zero, nsmul_zero]
  have hle : addOrderOf (c • v) ≤ m := addOrderOf_le_of_nsmul_eq_zero hmpos hkill
  omega

section Main

variable (H : Subgroup (AddAut (ZMod M × ZMod M)))

def R (x : ZMod M × ZMod M) : Prop := ∃ g ∈ H, g (1, 0) = x

variable {H}
omit [NeZero M] in

theorem R_one : R H (1, 0) := ⟨1, one_mem H, rfl⟩
omit [NeZero M] in

theorem R_apply {x : ZMod M × ZMod M} (hx : R H x) {g : AddAut (ZMod M × ZMod M)} (hg : g ∈ H) :
    R H (g x) := by
  obtain ⟨g', hg', rfl⟩ := hx
  exact ⟨g * g', mul_mem hg hg', rfl⟩
omit [NeZero M] in

theorem exists_of_R {v w : ZMod M × ZMod M} (hv : R H v) (hw : R H w) : ∃ h ∈ H, h v = w := by
  obtain ⟨g, hg, rfl⟩ := hv
  obtain ⟨g', hg', rfl⟩ := hw
  refine ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), ?_⟩
  rw [mul_apply', AddAut.inv_def', AddEquiv.symm_apply_apply]

structure Frame (H : Subgroup (AddAut (ZMod M × ZMod M))) where
  t : AddAut (ZMod M × ZMod M)
  ht : t ∈ H
  e : ZMod M
  he : e = 1 ∨ e = -1
  t_apply : ∀ x y : ZMod M, t (x, y) = (e * (x + y), e * y)
  ℓ : AddAut (ZMod M × ZMod M)
  hℓ : ℓ ∈ H
  z : ZMod M
  hz : IsUnit z
  ℓ_apply : ∀ x y : ZMod M, ℓ (x, y) = (e * x, e * (z * x + y))

theorem exists_frame
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M)) :
    Nonempty (Frame H) := by
  obtain ⟨t, htH, ε, hε, ht1, ht2⟩ := ht
  set e : ZMod M := (ε : ZMod M) with he_def
  have he : e = 1 ∨ e = -1 := by
    rcases hε with h | h
    · left; rw [he_def, h, Int.cast_one]
    · right; rw [he_def, h, Int.cast_neg, Int.cast_one]
  have ht1' : t (1, 0) = (e, 0) := by
    rw [ht1, ← intCast_smul]; ext <;> simp [he_def]
  have ht2' : t (0, 1) = (e, e) := by
    rw [ht2, ← intCast_smul]; ext <;> simp [he_def]
  have t_apply : ∀ x y : ZMod M, t (x, y) = (e * (x + y), e * y) := by
    intro x y
    rw [apply_mk, ht1', ht2']
    ext <;> simp <;> ring

  obtain ⟨h₀, hh₀, n₀, hn₀⟩ := htrans (1, 0) (0, 1) addOrderOf_one_zero addOrderOf_zero_one
  set a : ZMod M := (n₀ : ZMod M) with ha_def
  have h01 : h₀ (1, 0) = (0, a) := by
    rw [hn₀, ← intCast_smul]; ext <;> simp [ha_def]
  set β : ZMod M := (h₀ (0, 1)).1 with hβ
  set γ : ZMod M := (h₀ (0, 1)).2 with hγ
  have h02 : h₀ (0, 1) = (β, γ) := Prod.ext rfl rfl
  have h0_apply : ∀ x y : ZMod M, h₀ (x, y) = (y * β, x * a + y * γ) := by
    intro x y
    rw [apply_mk, h01, h02]
    ext <;> simp

  set x₀ := (h₀.symm (1, 0)).1
  set y₀ := (h₀.symm (1, 0)).2
  set x₁ := (h₀.symm (0, 1)).1
  set y₁ := (h₀.symm (0, 1)).2
  have hs1 : h₀.symm (1, 0) = (x₀, y₀) := Prod.ext rfl rfl
  have hs2 : h₀.symm (0, 1) = (x₁, y₁) := Prod.ext rfl rfl
  have E1 : ((1, 0) : ZMod M × ZMod M) = (y₀ * β, x₀ * a + y₀ * γ) := by
    rw [← h0_apply, ← hs1, AddEquiv.apply_symm_apply]
  have E2 : ((0, 1) : ZMod M × ZMod M) = (y₁ * β, x₁ * a + y₁ * γ) := by
    rw [← h0_apply, ← hs2, AddEquiv.apply_symm_apply]
  have hy₀β : y₀ * β = 1 := ((Prod.ext_iff.mp E1).1).symm
  have hx₀ : x₀ * a + y₀ * γ = 0 := ((Prod.ext_iff.mp E1).2).symm
  have hy₁β : y₁ * β = 0 := ((Prod.ext_iff.mp E2).1).symm
  have hx₁' : x₁ * a + y₁ * γ = 1 := ((Prod.ext_iff.mp E2).2).symm
  have hy₁ : y₁ = 0 := by
    calc y₁ = y₁ * (y₀ * β) := by rw [hy₀β, mul_one]
      _ = y₀ * (y₁ * β) := by ring
      _ = 0 := by rw [hy₁β, mul_zero]
  have hx₁ : x₁ * a = 1 := by rw [hy₁, zero_mul, add_zero] at hx₁'; exact hx₁'

  set ℓ := h₀ * t * h₀⁻¹ with hℓ_def
  have hℓH : ℓ ∈ H := mul_mem (mul_mem hh₀ htH) (inv_mem hh₀)
  have hℓ1 : ℓ (1, 0) = (e, e * (y₀ * a)) := by
    rw [hℓ_def, mul_apply', mul_apply', AddAut.inv_def', hs1, t_apply, h0_apply]
    ext
    · show e * y₀ * β = e
      rw [mul_assoc, hy₀β, mul_one]
    · show e * (x₀ + y₀) * a + e * y₀ * γ = e * (y₀ * a)
      linear_combination e * hx₀
  have hℓ2 : ℓ (0, 1) = (0, e) := by
    rw [hℓ_def, mul_apply', mul_apply', AddAut.inv_def', hs2, t_apply, h0_apply, hy₁]
    ext
    · show e * 0 * β = 0
      ring
    · show e * (x₁ + 0) * a + e * 0 * γ = e
      linear_combination e * hx₁
  have ℓ_apply : ∀ x y : ZMod M, ℓ (x, y) = (e * x, e * (y₀ * a * x + y)) := by
    intro x y
    rw [apply_mk, hℓ1, hℓ2]
    ext <;> simp <;> ring
  have hz : IsUnit (y₀ * a) :=
    (IsUnit.of_mul_eq_one β hy₀β).mul (IsUnit.of_mul_eq_one_right x₁ hx₁)
  exact ⟨⟨t, htH, e, he, t_apply, ℓ, hℓH, y₀ * a, hz, ℓ_apply⟩⟩

namespace Frame

variable (Fr : Frame H)
omit [NeZero M] in

theorem e_sq : Fr.e * Fr.e = 1 := by
  rcases Fr.he with h | h <;> rw [h] <;> ring
omit [NeZero M] in

theorem e_pow_two_mul (n : ℕ) : Fr.e ^ (2 * n) = 1 := by
  rw [pow_mul, sq, e_sq, one_pow]
omit [NeZero M] in

theorem t_pow_apply (n : ℕ) (x y : ZMod M) :
    (Fr.t ^ n) (x, y) = (Fr.e ^ n * (x + n * y), Fr.e ^ n * y) := by
  induction n generalizing x y with
  | zero => ext <;> simp
  | succ n ih =>
    rw [pow_succ, mul_apply', Fr.t_apply, ih]
    ext <;> push_cast <;> ring

def kk : ℕ := (-(Fr.z⁻¹) : ZMod M).val

theorem kk_mul_z : (Fr.kk : ZMod M) * Fr.z = -1 := by
  rw [kk, ZMod.natCast_zmod_val, neg_mul, ZMod.inv_mul_of_unit _ Fr.hz]

def gS : AddAut (ZMod M × ZMod M) := Fr.t ^ Fr.kk * Fr.ℓ * Fr.t ^ Fr.kk
omit [NeZero M] in

theorem gS_mem : Fr.gS ∈ H :=
  mul_mem (mul_mem (pow_mem Fr.ht _) Fr.hℓ) (pow_mem Fr.ht _)

theorem gS_apply_one_zero : Fr.gS (1, 0) = (0, Fr.e * Fr.z) := by
  rw [gS, mul_apply', mul_apply', t_pow_apply, Fr.ℓ_apply, t_pow_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_pow_two_mul Fr.kk
  ext
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) + Fr.e ^ Fr.kk * 0))) = 0
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + Fr.kk * 0)) + Fr.e ^ Fr.kk * 0))) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * (1 + Fr.kk * Fr.z) := by ring
    rw [this, h1]; ring
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + ↑Fr.kk * 0)) + Fr.e ^ Fr.kk * 0)) =
        Fr.e * Fr.z
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (1 + ↑Fr.kk * 0)) + Fr.e ^ Fr.kk * 0)) =
        Fr.e ^ (2 * Fr.kk) * (Fr.e * Fr.z) := by ring
    rw [this, h2, one_mul]

theorem gS_apply_zero_one : Fr.gS (0, 1) = (Fr.e * Fr.kk, 0) := by
  rw [gS, mul_apply', mul_apply', t_pow_apply, Fr.ℓ_apply, t_pow_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_pow_two_mul Fr.kk
  ext
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) + Fr.e ^ Fr.kk * 1))) =
        Fr.e * Fr.kk
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) +
        Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + Fr.kk * 1)) + Fr.e ^ Fr.kk * 1))) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * Fr.kk * (1 + (Fr.kk * Fr.z + 1)) := by ring
    rw [this, h1, h2]; ring
  · show Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + ↑Fr.kk * 1)) + Fr.e ^ Fr.kk * 1)) = 0
    have : Fr.e ^ Fr.kk * (Fr.e * (Fr.z * (Fr.e ^ Fr.kk * (0 + ↑Fr.kk * 1)) + Fr.e ^ Fr.kk * 1)) =
        Fr.e ^ (2 * Fr.kk) * Fr.e * (Fr.kk * Fr.z + 1) := by ring
    rw [this, h1]; ring

theorem gS_apply (x y : ZMod M) : Fr.gS (x, y) = (Fr.e * Fr.kk * y, Fr.e * Fr.z * x) := by
  rw [apply_mk, gS_apply_one_zero, gS_apply_zero_one]
  ext <;> simp <;> ring

theorem gS_sq_apply (v : ZMod M × ZMod M) : (Fr.gS * Fr.gS) v = -v := by
  obtain ⟨x, y⟩ := v
  rw [mul_apply', gS_apply, gS_apply]
  have h1 := Fr.kk_mul_z
  have h2 := Fr.e_sq
  ext
  · show Fr.e * Fr.kk * (Fr.e * Fr.z * x) = -x
    have : Fr.e * Fr.kk * (Fr.e * Fr.z * x) = (Fr.e * Fr.e) * (Fr.kk * Fr.z) * x := by ring
    rw [this, h1, h2]; ring
  · show Fr.e * Fr.z * (Fr.e * Fr.kk * y) = -y
    have : Fr.e * Fr.z * (Fr.e * Fr.kk * y) = (Fr.e * Fr.e) * (Fr.kk * Fr.z) * y := by ring
    rw [this, h1, h2]; ring

include Fr

theorem R_neg {x : ZMod M × ZMod M} (hx : R H x) : R H (-x) := by
  have := R_apply hx (mul_mem Fr.gS_mem Fr.gS_mem)
  rwa [gS_sq_apply] at this

theorem R_of_R_e {x y : ZMod M} (h : R H (Fr.e * x, Fr.e * y)) : R H (x, y) := by
  rcases Fr.he with h1 | h1
  · rw [h1, one_mul, one_mul] at h; exact h
  · have := Fr.R_neg h
    rw [h1] at this
    convert this using 1
    ext <;> simp

theorem R_tstep {x y : ZMod M} (h : R H (x, y)) : R H (x + y, y) := by
  have h' := R_apply h Fr.ht
  rw [Fr.t_apply] at h'
  exact Fr.R_of_R_e h'

theorem R_lstep {x y : ZMod M} (h : R H (x, y)) : R H (x, Fr.z * x + y) := by
  have h' := R_apply h Fr.hℓ
  rw [Fr.ℓ_apply] at h'
  exact Fr.R_of_R_e h'

theorem R_one_nat (n : ℕ) : R H (1, n * Fr.z) := by
  induction n with
  | zero => simpa using (R_one (H := H))
  | succ n ih =>
    have := Fr.R_lstep ih
    convert this using 2
    push_cast; ring

theorem R_one_all (y : ZMod M) : R H (1, y) := by
  have h := Fr.R_one_nat (y * Fr.z⁻¹).val
  rw [ZMod.natCast_zmod_val, mul_assoc, ZMod.inv_mul_of_unit _ Fr.hz, mul_one] at h
  exact h

theorem R_unit_aux (u : ZMod M) (n : ℕ) : R H (u, n * (Fr.z * u) + (u - 1)) := by
  induction n with
  | zero =>
    have := Fr.R_tstep (Fr.R_one_all (u - 1))
    convert this using 2 <;> push_cast <;> ring
  | succ n ih =>
    have := Fr.R_lstep ih
    convert this using 2
    push_cast; ring

theorem R_unit {u : ZMod M} (hu : IsUnit u) : R H (u, 0) := by
  have hzu : IsUnit (Fr.z * u) := Fr.hz.mul hu
  have h := Fr.R_unit_aux u ((1 - u) * (Fr.z * u)⁻¹).val
  rw [ZMod.natCast_zmod_val, mul_assoc, ZMod.inv_mul_of_unit _ hzu, mul_one] at h
  convert h using 2
  ring

theorem R_smul {x : ZMod M × ZMod M} (hx : R H x) {u : ZMod M} (hu : IsUnit u) : R H (u • x) := by
  obtain ⟨g, hg, rfl⟩ := hx
  obtain ⟨g', hg', hg'1⟩ := Fr.R_unit hu
  refine ⟨g * g', mul_mem hg hg', ?_⟩
  rw [mul_apply', hg'1, ← map_smul']
  congr 1
  ext <;> simp

theorem R_of_addOrderOf_eq
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    {v : ZMod M × ZMod M} (hv : addOrderOf v = M) : R H v := by
  obtain ⟨h, hh, n, hn⟩ := htrans (1, 0) v addOrderOf_one_zero hv
  rw [← intCast_smul] at hn
  have hord : addOrderOf ((n : ZMod M) • v) = M := by
    rw [← hn, AddEquiv.addOrderOf_eq, addOrderOf_one_zero]
  have hu : IsUnit (n : ZMod M) := isUnit_of_addOrderOf_smul _ _ hord
  have hR : R H ((n : ZMod M) • v) := ⟨h, hh, hn⟩
  have hR' := Fr.R_smul hR (u := (n : ZMod M)⁻¹) (IsUnit.of_mul_eq_one _ (ZMod.inv_mul_of_unit _ hu))
  rwa [smul_smul, ZMod.inv_mul_of_unit _ hu, one_smul] at hR'

end Frame

end Main

private theorem main (M : ℕ) [NeZero M] (H : Subgroup (AddAut (ZMod M × ZMod M)))
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M))
    (v w : ZMod M × ZMod M) (hv : addOrderOf v = M) (hw : addOrderOf w = M) :
    ∃ h ∈ H, h v = w := by
  obtain ⟨Fr⟩ := exists_frame htrans ht
  exact exists_of_R (Fr.R_of_addOrderOf_eq htrans hv) (Fr.R_of_addOrderOf_eq htrans hw)

end AddAut

theorem AddAut.exists_mem_apply_eq_of_addOrderOf_eq_of_transvection_mem (M : ℕ) [NeZero M] (H : Subgroup (AddAut (ZMod M × ZMod M)))
    (htrans : ∀ v w : ZMod M × ZMod M, addOrderOf v = M → addOrderOf w = M →
      ∃ h ∈ H, ∃ n : ℤ, h v = n • w)
    (ht : ∃ t ∈ H, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      t (1, 0) = ε • ((1, 0) : ZMod M × ZMod M) ∧ t (0, 1) = ε • ((1, 1) : ZMod M × ZMod M))
    (v w : ZMod M × ZMod M) (hv : addOrderOf v = M) (hw : addOrderOf w = M) :
    ∃ h ∈ H, h v = w :=
  main M H htrans ht v w hv hw
