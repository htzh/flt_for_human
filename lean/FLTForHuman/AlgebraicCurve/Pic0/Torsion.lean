/-
The torsion of `Pic0`: finiteness from the prime-power ranks, and the divisor
representatives of torsion classes, after three `P2M/Sol/S_` files of the pinned FLT
(`anthropics/fermats-last-theorem`, `aa2d8b3`):

* `S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean`,
* `S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean`,
* `S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean`
  (<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean>).

**A torsion class is `n` times its divisor's orders.** If `x` is killed by `n`, a
representative `D` of `x` has `n • D` principal (`Pic0` is the quotient of degree-zero
divisors by the principal ones), so `n • D = div f` for some `f ≠ 0` and
`v.ord f = n * D v` at every place. The same hypothesis also gives the sharper statement:
`f` is not the `n`-th power of anything up to a constant, since a class whose
representative is `c * h ^ n` is zero.

**The finiteness of the torsion.** The `n`-torsion of the class group is finite whenever it
is finite at every prime power: `Submodule.torsionBy` is multiplicative in coprime
factors, `torsionBy ℤ M (a * b) ↪ torsionBy ℤ M a × torsionBy ℤ M b` when `a`, `b` are
coprime (via a Bézout combination), and `n` is built up from `0`, `1`, prime powers and
coprime products by `Nat.recOnPosPrimePosCoprime`.

**Moving a torsion class.** The divisor representative of a torsion class may be chosen
with rational support avoiding a prescribed finite set of places.

`Pic0`, `Pic0.torsion` and `Pic0.mk` live in `Defs/Divisor.lean`, a hub; the three rows
here are a subject of their own, so they sit in this module above it. The pin's six
private prelude helpers are two importable facts (`Place.ord_algebraMap` for the order of a
constant, and the quotient bookkeeping `Pic0.mk D = 0 ↔ D` principal, inlined here at its
single use) and four lemmas written below at the pin's names.

Wire: `spec/check_port.py` diffs every public declaration of this module against the pin
files named by the `spec-pin:` lines below.

spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean
spec-pin: Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean
-/
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.RingTheory.Coprime.Lemmas

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing (each one is an instance the following proof
-- needs); keep them literal rather than rewriting them as `have`.
set_option linter.style.haveILetI false

noncomputable section

namespace AlgebraicCurve

namespace Pic0

/-! ## The private prelude: orders of powers, and the class of a `n`-th power -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem ord_pow_aux (v : Place K F) (h : F) (n : ℕ) : v.ord (h ^ n) = n * v.ord h := by
  rw [← zpow_natCast]
  exact v.ord_zpow h n

/-- A class whose representative is `c * h ^ n` is zero: dividing the order identity
`v.ord f = n * D v` by `n` after reading off `v.ord (c * h ^ n) = n * v.ord h`. -/
private theorem mk_eq_zero_of_eq_algebraMap_mul_pow {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0)
    {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (c : K) (h : F)
    (hfch : f = algebraMap K F c * h ^ n) : Pic0.mk D = 0 := by
  have hne : algebraMap K F c ≠ 0 ∧ h ^ n ≠ 0 := mul_ne_zero_iff.mp (hfch ▸ hf)
  have hh : h ≠ 0 := fun h0 => hne.2 (by rw [h0]; exact zero_pow hn)
  rw [show Pic0.mk D = QuotientAddGroup.mk D from rfl, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, Divisor.mem_principal]
  refine ⟨h, hh, fun v => ?_⟩
  have h1 : v.ord f = n * v.ord h := by
    rw [hfch, v.ord_mul hne.1 hne.2, Place.ord_algebraMap, zero_add, ord_pow_aux]
  have h2 : (n : ℤ) * (D : Divisor K F) v = n * v.ord h := (hfD v).symm.trans h1
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) h2

private theorem ne_algebraMap_mul_pow_of_mk_ne_zero {n : ℕ} (hn : n ≠ 0) {f : F} (hf : f ≠ 0)
    {D : Divisor.degZero (K := K) (F := F)}
    (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) (hx : Pic0.mk D ≠ 0)
    (c : K) (h : F) : f ≠ algebraMap K F c * h ^ n :=
  fun hfch => hx (mk_eq_zero_of_eq_algebraMap_mul_pow hn hf hfD c h hfch)

/-- The engine of the three rows: an `n`-torsion class, represented by `D`, has a function
whose orders are `n` times `D`'s. -/
private theorem exists_ord_eq_mul_of_mk_mem_torsion {n : ℕ} {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) {D : Divisor.degZero (K := K) (F := F)}
    (hD : Pic0.mk D = x) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v := by
  have hx' : (n : ℤ) • x = 0 := Pic0.mem_torsion.mp hx
  have h1 : Pic0.mk ((n : ℤ) • D) = 0 := by
    have h2 : Pic0.mk ((n : ℤ) • D) = (n : ℤ) • Pic0.mk D := by
      show QuotientAddGroup.mk ((n : ℤ) • D) = (n : ℤ) • (QuotientAddGroup.mk D)
      exact QuotientAddGroup.mk_zsmul
        ((Divisor.principal (K := K) (F := F)).addSubgroupOf
          (Divisor.degZero (K := K) (F := F))) D (n : ℤ)
    rw [h2, hD, hx']
  have h3 : ((n : ℤ) • D : Divisor.degZero (K := K) (F := F)) ∈
      (Divisor.principal (K := K) (F := F)).addSubgroupOf
        (Divisor.degZero (K := K) (F := F)) :=
    (QuotientAddGroup.eq_zero_iff _).mp h1
  rw [AddSubgroup.mem_addSubgroupOf] at h3
  have h4 : Divisor.IsPrincipal ((n : ℤ) • (D : Divisor K F)) := Divisor.mem_principal.mp h3
  obtain ⟨f, hf0, hford⟩ := h4
  refine ⟨f, hf0, fun v => ?_⟩
  have := hford v
  rw [Finsupp.smul_apply, smul_eq_mul] at this
  exact this.symm

/-! ## The three rows -/

/-- **A torsion class has a divisor representative `n` times which is an order, and no
`n`-th power up to a constant.** Statement from
`Theorems/Thm_AlgebraicCurve_Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero.lean`;
proof after the pin's `S_` file. -/
theorem exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n : ℕ} (hn : n ≠ 0) {x : Pic0 K F}
    (hx : x ∈ Pic0.torsion K F n) (hx0 : x ≠ 0) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (f : F),
      Pic0.mk D = x ∧ f ≠ 0 ∧ (∀ v : Place K F, v.ord f = n * (D : Divisor K F) v) ∧
        ∀ b : F, b ^ n ≠ f := by
  obtain ⟨D, hD⟩ := Pic0.mk_surjective x
  obtain ⟨f, hf0, hfD⟩ := exists_ord_eq_mul_of_mk_mem_torsion hx hD
  refine ⟨D, f, hD, hf0, hfD, fun b hb => ?_⟩
  exact ne_algebraMap_mul_pow_of_mk_ne_zero hn hf0 hfD (hD ▸ hx0) 1 b
    (by rw [map_one, one_mul, hb])

/-- **The torsion of `Pic0` is finite if it is finite at every prime power.** Statement
from `Theorems/Thm_AlgebraicCurve_Pic0_finite_torsion_of_forall_primePow.lean`; proof
after the pin's `S_` file (via `torsionBy`'s multiplicativity in coprime factors). -/
theorem finite_torsion_of_forall_primePow {K F : Type*} [Field K] [Field F] [Algebra K F]
    (h : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), Finite (Pic0.torsion K F (p ^ k))) (n : ℕ)
    (hn : 0 < n) : Finite (Pic0.torsion K F n) := by
  suffices H : ∀ m : ℕ, 0 < m → Finite (Submodule.torsionBy ℤ (Pic0 K F) (m : ℤ)) by
    exact H n hn
  intro m
  induction m using Nat.recOnPosPrimePosCoprime
  ·
    rename_i p k hp hk
    intro _
    haveI : Fact p.Prime := ⟨hp⟩
    exact h p k
  ·
    intro h0
    exact absurd h0 (lt_irrefl 0)
  ·
    intro _
    haveI : Subsingleton (Submodule.torsionBy ℤ (Pic0 K F) ((1 : ℕ) : ℤ)) := by
      refine ⟨fun x y => Subtype.ext ?_⟩
      have hx := x.2
      have hy := y.2
      rw [Submodule.mem_torsionBy_iff] at hx hy
      simp only [Nat.cast_one, one_smul] at hx hy
      rw [hx, hy]
    infer_instance
  ·
    rename_i a b ha hb hab iha ihb
    intro _
    haveI := iha (by omega)
    haveI := ihb (by omega)
    obtain ⟨u, v, huv⟩ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hab
    have key : ∀ x : Pic0 K F, x = u • ((a : ℤ) • x) + v • ((b : ℤ) • x) := fun x => by
      have hx := congrArg (fun r : ℤ => r • x) huv
      simp only [add_zsmul, mul_smul, one_smul] at hx
      exact hx.symm
    let f : Submodule.torsionBy ℤ (Pic0 K F) ((a * b : ℕ) : ℤ) →
        Submodule.torsionBy ℤ (Pic0 K F) (a : ℤ) × Submodule.torsionBy ℤ (Pic0 K F) (b : ℤ) :=
      fun x =>
        (⟨(b : ℤ) • (x : Pic0 K F), by
            have hx := x.2
            rw [Submodule.mem_torsionBy_iff] at hx ⊢
            rw [smul_smul]
            push_cast at hx
            exact hx⟩,
         ⟨(a : ℤ) • (x : Pic0 K F), by
            have hx := x.2
            rw [Submodule.mem_torsionBy_iff] at hx ⊢
            rw [smul_smul, mul_comm]
            push_cast at hx
            exact hx⟩)
    refine Finite.of_injective f ?_
    intro x y hxy
    simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at hxy
    obtain ⟨h1, h2⟩ := hxy
    apply Subtype.ext
    calc (x : Pic0 K F) = u • ((a : ℤ) • (x : Pic0 K F)) + v • ((b : ℤ) • (x : Pic0 K F)) := key _
      _ = u • ((a : ℤ) • (y : Pic0 K F)) + v • ((b : ℤ) • (y : Pic0 K F)) := by rw [h2, h1]
      _ = (y : Pic0 K F) := (key _).symm

/-- **A torsion class has a divisor representative whose orders are `n` times its own.**
Statement from `Theorems/Thm_AlgebraicCurve_Pic0_torsion_exists_forall_ord_eq_mul.lean`;
proof after the pin's `S_` file, the body of the private engine above. -/
theorem torsion.exists_forall_ord_eq_mul {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (x : Pic0.torsion K F n) (D : Divisor.degZero (K := K) (F := F))
    (hD : Pic0.mk D = (x : Pic0 K F)) :
    ∃ f : F, f ≠ 0 ∧ ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v :=
  exists_ord_eq_mul_of_mk_mem_torsion x.2 hD

end Pic0

end AlgebraicCurve
