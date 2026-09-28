/-
  The Frey package: the arithmetic data `(a, b, c, p)` of a counterexample to
  Fermat, together with the associated Frey curves.

  A `FreyPackage` is integers `a, b, c ≠ 0` and a prime `p ≥ 5` with
  `a^p + b^p = c^p`, `gcd a b = 1`, `a ≡ 3 (mod 4)` and `b ≡ 0 (mod 2)`;
  `freyCurveInt`/`freyCurve` are the Frey curves over `ℤ` and `ℚ`.

  Transcribed verbatim from `Definitions/Def_FLTPrelim_FreyPackage.lean`
  (pinned `aa2d8b3`, 97 lines); mathlib-only, exactly as the pin. The
  mathematics is math/018 §1.6.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Int.Basic

set_option autoImplicit false

structure FreyPackage where

  a : ℤ

  b : ℤ

  c : ℤ
  ha0 : a ≠ 0
  hb0 : b ≠ 0
  hc0 : c ≠ 0

  p : ℕ
  pp : Nat.Prime p
  hp5 : 5 ≤ p

  hFLT : a ^ p + b ^ p = c ^ p

  hgcdab : gcd a b = 1

  ha4 : (a : ZMod 4) = 3

  hb2 : (b : ZMod 2) = 0

namespace FreyPackage

lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

lemma hp_odd (P : FreyPackage) : Odd P.p :=
  P.pp.odd_of_ne_two (by have := P.hp5; omega)

lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']; exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]; exact P.hFLT

lemma habc0 (P : FreyPackage) : P.a * P.b * P.c ≠ 0 :=
  mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0

lemma two_dvd_abc (P : FreyPackage) : (2 : ℤ) ∣ P.a * P.b * P.c :=
  dvd_mul_of_dvd_left (dvd_mul_of_dvd_right
    ((ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2) _) _

def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

end FreyPackage
