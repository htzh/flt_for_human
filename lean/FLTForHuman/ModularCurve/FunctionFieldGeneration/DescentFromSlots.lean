/-
  The descent with its slot hypotheses discharged: `Hall M → j(q ^ M) ∈ F_{M * p}`.

  `FunctionFieldGeneration/Descent.lean` (T15) proves the descent *given* two facts
  about the roots of `pushedMinpoly K M (M * p)`: one pinning the only root at
  nome-level `(M * p) * M` to the untwisted one, one excluding the extra conjugate
  of the level-`p` equation. This module *derives* those two facts from T19's slot
  product (`minpoly_jqN_map_eq_prod_slots`) plus `Hall M`, so that a caller — the
  capstone's strong induction — never has to see `K`, `ζ`, or a root predicate:

  * `root_shape`: every root of `pushedMinpoly K M (M * p)` is a slot value
    `j(ζ ^ (b * a) q ^ (a * a))` with `a ∣ M`, `b < M / a` (the slot list of the
    level-`M` minimal polynomial, read at the level-`M * p` nome);
  * `htw_of` / `hsp_of`: the two slot facts, by index arithmetic on that shape and
    `TS_injective`;
  * `jqN_mem_modularFunctionField_of_hall`: the interface, over `ℚ` only.

  The module's second interface is the one-prime reduction of `Gen`, in the same
  `Hall` form: `modularFunctionField_eq_full_of` takes, for every factorization
  `N = M * p`, only `Hall M`, and derives both facts the reduction consumes — `Gen M`
  from `Hall M` and `jqN M ∈ F_N` from the descent above. Its former text (in
  `Descent`, where the descent is) took the conjunction the caller had to assemble
  from the induction hypothesis plus `jqN_mem_modularFunctionField_of_hall`; that is
  the inversion this module exists to remove.

  Its proof is then the induction step and nothing else: the case split at `d = N`, one
  `obtain` of the level `m < N` that the hypothesis is taken at (the private
  `exists_mul_prime_lt_of_dvd_of_ne`), `Hall m`, the descent transported to the level `N`,
  and the inclusion of the level's full divisor field (the private
  `full_le_of_gen_of_mem`). The level and the prime are this reduction's own data, so the
  two helpers are private here rather than upstream.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` lines 541–613 — `root_shape`,
  `htw_of` and `hsp_of`, `private` in the pin and consumed only by the pin's
  `hall_all`. The port had transcribed them into
  `FunctionFieldGeneration/Capstone.lean` (its `Shapes` section, lines 141–215) for
  the same purpose; they live here now, downstream of both T15 and T19, because
  that is the layer where the two topics meet.

  The reduction's own pin text is
  `P2M/Sol/S_ModularCurve_modularFunctionField_eq_full_of.lean` lines 694–727: the same
  proof spine, with its two hypothesis applications (`hstep`, `hgen'`) replaced by the
  derivation of what they carry.

  ## Verification tier

  No `spec-pin:` header, deliberately: every public declaration here is the port's
  own — `jqN_mem_modularFunctionField_of_hall` has no pin counterpart (the pin keeps
  this argument inline inside `hall_all`), and `modularFunctionField_eq_full_of`'s
  text was retired to the `Hall` form above, so a wire would diff nothing. The pin's
  `private` helpers are transcribed above at the pin's own privacy. Same tier as
  `SlotValues.lean`; registered by `spec/unwired_register.py`.

  If a future public declaration in this module transcribes a pin statement, it
  needs a `spec-pin:` line, and this note is then wrong.

  ## Assumptions

  T15's `jqN_div_mem_modularFunctionField`, T19's `minpoly_jqN_map_eq_prod_slots`,
  `Defs/Nome`'s `pushedMinpoly` (`Defs/PhiAtSlot.lean`), `Defs/TS`'s `TS` and
  `TS_injective`, and `Defs/Cyclotomic`'s `cycUnit`.
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import FLTForHuman.ModularCurve.Defs.Invariants
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField
open ModularCurve.Nome

namespace ModularCurve

variable {K : Type} [Field K] [Algebra ℚ K]

/-! ## The shape of a root of the pushed minimal polynomial -/

/-- **Every root is a slot value.** A root `x` of `pushedMinpoly K M (M * p)` is
`j(ζ ^ (b * a) q ^ (a * a))` for some `a ∣ M` and `b < M / a`: the slot description
of the level-`M` minimal polynomial (T19), read at the level-`M * p` nome. -/
private theorem root_shape (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (x : LaurentSeries K)
    (hx : (pushedMinpoly K M (M * p)).IsRoot x) :
    ∃ a : ℕ, ∃ _ : NeZero a, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
      x = TS K (p * (a * a)) (ζ ^ (b * a)) := by
  have hid := minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ hallM
  have hcomp : (qExpand K p).comp (((coeffEmb K).comp (qExpand ℚ M)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    simpa only [nomeMap] using nomeMap_qExpand K M p
  have hx' : Polynomial.eval x ((minpoly ℚ⟮jq⟯ (jqN M)).map
      (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
        (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0 := hx
  rw [← hcomp, ← Polynomial.map_map, hid, Polynomial.eval_map,
    Polynomial.eval₂_finsetProd] at hx'
  obtain ⟨a, ha, hx'⟩ := Finset.prod_eq_zero_iff.mp hx'
  rw [Polynomial.eval₂_finsetProd] at hx'
  obtain ⟨b, hb, hx'⟩ := Finset.prod_eq_zero_iff.mp hx'
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hx'
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dite_eq_right ha0] at hx'
  have : NeZero a := ⟨ha0⟩
  refine ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b,
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1), ?_⟩
  rw [hx', coeffEmb_jq]
  exact qExpand_TS p (a * a) (ζ ^ (b * a))

/-! ## The two slot facts -/

/-- **`htw`.** At nome-level `(M * p) * M` the only root of the pushed minimal
polynomial is the untwisted one: comparing the level in `root_shape` with `M²p`
forces `a = M`, and the twist index `b < M / a = 1` forces `b = 0`. -/
private theorem htw_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (w : Kˣ)
    (hw : (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * M) w)) : w = 1 := by
  obtain ⟨a, _, haM, b, hb, heq⟩ := root_shape M p ζ hζ hallM _ hw
  obtain ⟨he, hu⟩ := TS_injective heq
  have he' : p * (a * a) = p * (M * M) := by rw [← he]; ring
  have haM' : a = M := Nat.mul_self_inj.mp (Nat.eq_of_mul_eq_mul_left hp.out.pos he')
  subst haM'
  have hb0 : b = 0 := by
    rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne a))] at hb
    omega
  subst hb0
  rw [zero_mul, pow_zero] at hu
  exact hu

/-- **`hsp`.** The extra conjugate `j(q ^ ((M * p) * (M * p * p)))` of the level-`p`
equation is not a root: a root at that level would have `a² = (M p)²` by the same
comparison, hence `a = M p > M`, contradicting `a ∣ M`. -/
private theorem hsp_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) :
    ¬ (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * (M * p * p)) 1) := by
  intro hx
  obtain ⟨a, _, haM, b, _, heq⟩ := root_shape M p ζ hζ hallM _ hx
  obtain ⟨he, _⟩ := TS_injective heq
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have ha : a ≤ M := Nat.le_of_dvd hM haM
  have h1 : a * a = (M * p) * (M * p) := by
    have h2 : p * (a * a) = p * ((M * p) * (M * p)) := by rw [← he]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos h2
  have h2 : a = M * p := Nat.mul_self_inj.mp h1
  have : M * p ≤ M := h2 ▸ ha
  have : M * 2 ≤ M * p := Nat.mul_le_mul_left M hp2
  omega

/-! ## The interface -/

/-- **The descent, with its slot hypotheses discharged**: for a prime `p` and any
`M` with `Hall M`, `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M * p)))`.

This is the form the capstone's strong induction consumes. The splitting field, the
root of unity and the two root conditions of
`jqN_div_mem_modularFunctionField` are all discharged here — the former two by
`CyclotomicField (M * p) ℚ`, the latter two by `htw_of`/`hsp_of` from the slot
product and `Hall M`. -/
theorem jqN_mem_modularFunctionField_of_hall (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hallM : Hall M) :
    jqN M ∈ modularFunctionField (M * p) :=
  jqN_div_mem_modularFunctionField M p (cycUnit (M * p)) (cycUnit_spec (M * p))
    (fun w hw => htw_of M p (cycUnit (M * p) ^ (M * p / M))
      (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM w hw)
    (hsp_of M p (cycUnit (M * p) ^ (M * p / M))
      (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM)

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

/-- **A level's divisor field inside the containing one.** If `m` generates its own divisor
field (`Gen m`) and the single further generator `j(q ^ m)` lies in `modularFunctionField N`,
then `modularFunctionFieldFull m` is contained in `modularFunctionField N`: the divisor
substitutions at `m` are generated by `j(q)` and `j(q ^ m)`. -/
private theorem full_le_of_gen_of_mem {N m : ℕ} [NeZero N] [NeZero m] (hgen : Gen m)
    (hmem : jqN m ∈ modularFunctionField N) :
    modularFunctionFieldFull m ≤ modularFunctionField N := by
  rw [← hgen, modularFunctionField, IntermediateField.adjoin_le_iff]
  rintro y (rfl | rfl)
  · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)
  · exact hmem

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
      exact jqN_mem_modularFunctionField_of_hall m p hallm
    exact full_le_of_gen_of_mem (hallm m dvd_rfl).2 hmem (jqd_mem_full m hdm)

end ModularCurve

end
