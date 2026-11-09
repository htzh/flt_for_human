/-
  The descent by one prime, as the `ℚ` instance of the theory's prime step, and the one-prime
  reduction of `Gen`.

  `jqN_div_mem_modularFunctionField` is the descent by one prime: under `Hall M`, `j(q ^ M)` lies
  in `ℚ(j(q), j(q ^ (M * p)))`. The comparison that proves it — the level-`p` equation `A` and the
  transported minimal polynomial `B` of `j(q ^ M)` read at the level-`M * p` nome, their root
  descriptions, and the case split that leaves the untwisted twist as the only common root — is
  `Generic/PrimeStep.lean`'s `levelSeries_mem_levelField_mul_prime`, ported from this module's
  former proof after it was refactored into two producers and named index arithmetic. Nothing of
  it is re-proved here.

  ## The second field is chosen here, and only here

  The theory's prime step leaves the second field `κ'` free, because at `ℚ` the slots cannot be read
  in `ℚ` itself: they need a primitive `(M * p)`-th root. So this layer supplies
  `CyclotomicField (M * p) ℚ` with `cycUnit (M * p)` as the section variable's instantiation (the
  coefficient extension `coeffEmb` is then `σ`); `Tight M` is the first projection of `Hall M`, spent
  inside the generic certificate. No statement here carries a type parameter.

  ## What is left in this module

  The conversion between the theory's `levelField` (a field over `baseField`, i.e. `ℚ⟮jq⟯`) and the
  named `modularFunctionField` — the two adjoins differ only in how the pair `{jq, jq(q ^ N)}` is
  written, which is `coe_adjoin_baseField` plus a set identity — and the `Gen` reduction below,
  which is `ℚ`-only mathematics.

  ## Layers, in dependency order

  * `jqN_div_mem_modularFunctionField`: the descent, a delegation to the theory's prime step
    (`Generic/PrimeStep.lean`) at the `ℚ` instance, whose second field is
    `CyclotomicField (M * p) ℚ`. The conversion
    between the theory's `levelField` and the named `modularFunctionField` is the only `ℚ`-side
    content in it;
  * `exists_mul_prime_lt_of_dvd_of_ne`: the arithmetic of the one-prime reduction below.

  The module's second subject is the one-prime reduction of `Gen`, in the same `Hall` form:
  `modularFunctionField_eq_full_of` takes the strong induction hypothesis itself
  (`∀ m < N, m ≠ 0 → Hall m`) and derives what it consumes — the level `m < N` that a
  proper divisor `d` divides with `N = m * p`, `Hall m`, `jqN m ∈ F_N` from the descent
  above, and `Gen m` from `Hall m`. The caller passes `ih` unchanged.

  ## Verification tier

  No `spec-pin:` header: the public statements are the port's own — the descent takes `Hall M`
  (the certificate is the theory's), and the reduction is stated in the `Hall` form — so a wire
  would diff nothing. Registered by `spec/unwired_register.py`.

  If a future public declaration in this module transcribes a pinned statement, it needs a
  `spec-pin:` line, and this note is then wrong.

  ## Assumptions

  `Generic/PrimeStep.lean`'s `levelSeries_mem_levelField_mul_prime`, `Defs/LevelPackage`'s
  `levelField`/`coe_adjoin_baseField`, `Rat/LevelPackage`'s `hall_pkgAt`, `cycUnit`/`cycUnit_spec`,
  `coeffEmb_jq`/`coeffEmb_qExpand`, `modularFunctionField`, `jqN_mem`, `jqd_mem_full`, and the
  arithmetic `lt_of_mul_prime_eq` for the reduction.
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.NumberTheory.DedekindPsi
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.PhiSlotRoots
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generic.PrimeStep
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Rat.LevelPackage

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

/-! ## The descent by one prime — delegated

The comparison itself — the two polynomials, their root descriptions, and the case split that
leaves one common root — is `Generic/PrimeStep.lean`'s `levelSeries_mem_levelField_mul_prime`. What
the `ℚ` layer supplies is the second field the general statement leaves free: `CyclotomicField (M * p) ℚ`
with `cycUnit (M * p)`, i.e. the instantiation of `[Algebra ℚ κ']` at `coeffEmb`. What it
keeps is the conversion between the theory's `levelField` and the named `modularFunctionField`: the
two adjoins differ only in how the pair `{jq, jq(q ^ N)}` is written. -/

/-- **Descent by one prime**: under `Hall M` and `p` prime, `j(q ^ M)` lies in
`ℚ(j(q), j(q ^ (M * p)))`. -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hallM : Hall M) :
    jqN M ∈ modularFunctionField (M * p) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hmem : levelSeries jq M ∈ levelField jq (M * p) :=
    levelSeries_mem_levelField_mul_prime (κ' := CyclotomicField (M * p) ℚ) jq rfl
      (M := M) (p := p) (ζ := cycUnit (M * p)) (hζ := cycUnit_spec (M * p))
      (hall_pkgAt M hallM)
  have hpair : ({jq} ∪ {qExpand ℚ (M * p) jq} : Set (LaurentSeries ℚ))
      = {jq, qExpand ℚ (M * p) jq} := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  have hset : ((levelField jq (M * p) : Set (LaurentSeries ℚ)))
      = (modularFunctionField (M * p) : Set (LaurentSeries ℚ)) := by
    rw [coe_adjoin_baseField, modularFunctionField]
    simp only [levelSeries]
    rw [hpair]
  show levelSeries jq M ∈ (modularFunctionField (M * p) : Set (LaurentSeries ℚ))
  rw [← hset]
  exact hmem

/-! ## The one-prime reduction -/

/-- **The step down the divisor lattice.** A proper divisor `d` of `N` divides a level `m`
that is properly below `N`, and `N / m` is prime: writing `N = d * m'` and taking
`p := m'.minFac`, that level is `m = d * (m' / p)`.

This is the arithmetic that opens any prime-by-prime strong induction over the divisors of a
level. It stays private here because it is arithmetic about this reduction's own data: `m` is
the level the induction hypothesis is taken at, and `p` the prime its step is taken by. -/
private theorem exists_mul_prime_lt_of_dvd_of_ne {N : ℕ} [NeZero N] {d : ℕ} [NeZero d]
    (hdN : d ∣ N) (hd : d ≠ N) :
    ∃ m p : ℕ, p.Prime ∧ NeZero m ∧ d ∣ m ∧ N = m * p ∧ m < N := by
  obtain ⟨m', hm'⟩ := hdN
  have hm'1 : m' ≠ 1 := fun h1 => hd (by rw [hm', h1, Nat.mul_one])
  have hm'0 : m' ≠ 0 := fun h0 => NeZero.ne N (by rw [hm', h0, Nat.mul_zero])
  obtain ⟨m, hm⟩ := Nat.minFac_dvd m'
  have hp : m'.minFac.Prime := Nat.minFac_prime hm'1
  have hm0 : m ≠ 0 := fun h0 => hm'0 (by rw [hm, h0, Nat.mul_zero])
  have hdm : d * m ≠ 0 := Nat.mul_ne_zero (NeZero.ne d) hm0
  have hNm : N = (d * m) * m'.minFac := by
    conv_lhs => rw [hm', hm]
    ring
  exact ⟨d * m, m'.minFac, hp, ⟨hdm⟩, dvd_mul_right d m, hNm,
    lt_of_mul_prime_eq hdm hp hNm.symm⟩

/-- **The one-prime reduction of `Gen`**: if the invariants hold at every level below
`N`, then `modularFunctionField N` is the full divisor field.

The hypothesis is the strong induction hypothesis *in the shape the induction gives it*
(`∀ m < N, m ≠ 0 → Hall m`), so the caller passes it unchanged. Everything the reduction
consumes for a proper divisor `d` is derived here: a level `m < N` divisible by `d` with
`N = m * p` (the private `exists_mul_prime_lt_of_dvd_of_ne`), `Hall m`, `jqN m ∈ F_N` from
the Hall-level descent, and `Gen m` from `Hall m`. The pin instead passes two facts per
factorization, with `Gen` unfolded; the port's earlier text conjoined them; both shapes made
the caller assemble what this statement can derive.

The statement is the port's; this module carries no `spec-pin:` wire, and the header
records why. -/
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (h : ∀ m : ℕ, m < N → m ≠ 0 → Hall m) :
    modularFunctionField N = modularFunctionFieldFull N := by
  refine le_antisymm (modularFunctionField_le_full N) ?_
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hd0, hdN, rfl⟩
  rcases eq_or_ne d N with hd | hd
  · subst d
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  · obtain ⟨m, p, hp, hm0, hdm, hNm, hmlt⟩ := exists_mul_prime_lt_of_dvd_of_ne hdN hd
    have : Fact (Nat.Prime p) := ⟨hp⟩
    have hallm : Hall m := h m hmlt (NeZero.ne m)
    have hmem : jqN m ∈ modularFunctionField N := by
      rw [mff_congr hNm]
      exact jqN_div_mem_modularFunctionField m p hallm
    have hle : modularFunctionFieldFull m ≤ modularFunctionField N := by
      rw [← (hallm m dvd_rfl).2, modularFunctionField, IntermediateField.adjoin_le_iff,
        Set.insert_subset_iff, Set.singleton_subset_iff]
      exact ⟨IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _), hmem⟩
    exact hle (jqd_mem_full m hdm)

end ModularCurve

end
