/-
  The capstone of `functionFieldGeneration`: the unconditional theorem.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` —
  lines 106–109 (`iota_jqN`, over the interface's `coeffEmb_qExpand`);
  199–240 (the cyclotomic root, `cycUnit`, `isPrimitiveRoot_pow_div`);
  413–435 (`Tight`/`Gen`/`Hall` and the congruence plumbing);
  436–466 (the `ψ` arithmetic); 467–613 (`tight_one` through `hsp_of`);
  614–700 (`hall_all`).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_functionFieldGeneration.lean

  `hall_all` is the strong induction of math/010 §7 carrying the two invariants
  `Tight` (the relative degree of `ℚ⟮jq⟯(jqN d)` over `ℚ⟮jq⟯` is `ψ(d)`) and `Gen`
  (the two-generator field is already the full divisor field) over the divisor
  lattice; the block above it is glue. It is private because it is an internal
  induction with no consumer of its own; `functionFieldGeneration` and the three
  corollaries below are the public surface, stated as in the pin. The induction
  consumes the seven significant statements directly, as FLT's does.

  spec-pin: Theorems/Thm_ModularCurve_functionFieldGeneration.lean
  spec-pin: Theorems/Thm_ModularCurve_modularFunctionField_eq_full.lean
  spec-pin: Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean
  spec-pin: Theorems/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean

  Assumes the seven significant statements (descent, the prime-power degree step,
  the non-membership tower, one new generator per prime power, the slot product
  and the prime non-membership), the `Tight`/`Gen`/`Hall` vocabulary with
  `tight_one`/`gen_one`, the cyclotomic roots, `TS` and its lemmas, and the §2
  collapse.
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.Data.Nat.Factorization.Basic
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
import FLTForHuman.ModularCurve.FunctionFieldGeneration.DegreeStep
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-! ## Transport

`coeffMap_qExpand` and `coeffEmb_qExpand` are part of the cone's outbound
interface and now live beside `coeffMap`/`coeffEmb` in `Defs/Laurent.lean`; this
module imports them rather than redeclaring them. T14 promoted `iota_jqN` to
`Defs/TS.lean` beside `TS`, and `Defs/TS` is imported below, so the private twin
that used to sit here is gone. -/

/-! ## Cyclotomic roots

`exists_isPrimitiveRoot_cyclotomicField`, `cycUnit`, `cycUnit_spec` and
`isPrimitiveRoot_pow_div` are public in `Defs/Cyclotomic.lean`, promoted by T13
from this module's private copies (the pin repeats them in the two
`splits_*` files as well); they are imported rather than declared here. -/

/-! ## Congruence plumbing and `ψ` arithmetic

`jqN_congr` was promoted by T14 to `Defs/Jq.lean` beside `jqN`; `Defs/TS`
imports `Defs/Jq`, so it is in scope here and the private twin is gone. -/

private theorem full_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionFieldFull n = modularFunctionFieldFull m := by
  subst h; rfl

private theorem mff_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionField n = modularFunctionField m := by
  subst h; rfl

/-! ## The invariants

`Tight`/`Gen`/`Hall` and the one-step facts `tight_one`/`gen_one` were promoted by
T13 and moved by T18 to `Defs/Fields.lean` beside the two fields they concern;
`Defs/TS`/`Collapse` import that module, so they are in scope here without a
local copy. `gen_prime` (T19's substitution) lives there too. -/

/-! ## The auxiliary block -/

-- The two prime-step case splits `dedekindPsi_mul_prime_{dvd,not_dvd}` were
-- private here and duplicated verbatim in `SlotProduct.lean`; both now live
-- once, publicly, in `FLTForHuman/NumberTheory/DedekindPsi.lean`.

private theorem relfinrank_full_of (N : ℕ) [NeZero N] (ht : Tight N) (hg : Gen N) :
    IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull N) = dedekindPsi N := by
  unfold Gen at hg
  unfold Tight at ht
  rw [← hg, relfinrank_modularFunctionField N, ht]

private theorem F0_le_full (N : ℕ) [NeZero N] : ℚ⟮jq⟯ ≤ modularFunctionFieldFull N := by
  rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff]
  have h := jqd_mem_full N (one_dvd N)
  rw [qExpand_one_apply] at h
  exact h

private theorem full_le_adjoin_chain (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) : ∀ a : ℕ,
    modularFunctionFieldFull (M * p ^ a) ≤ IntermediateField.adjoin ℚ
      ((modularFunctionFieldFull M : Set (LaurentSeries ℚ))
        ∪ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a ∧ x = jqN (p ^ i)}) := by
  intro a
  induction a with
  | zero =>
      rw [full_congr (show M * p ^ 0 = M by rw [pow_zero, mul_one])]
      exact fun x hx => IntermediateField.subset_adjoin ℚ _ (Set.mem_union_left _ hx)
  | succ k ih =>
      rw [full_eq_adjoin_full_div_prime M p k hpM, IntermediateField.adjoin_le_iff,
        Set.insert_subset_iff]
      refine ⟨IntermediateField.subset_adjoin ℚ _ (Set.mem_union_right _
        (show jqN (p ^ (k + 1)) ∈ {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ k + 1 ∧ x = jqN (p ^ i)}
          from ⟨k + 1, le_rfl, rfl⟩)), ?_⟩
      intro x hx
      have hx' := ih hx
      refine IntermediateField.adjoin.mono ℚ _ _ (Set.union_subset_union le_rfl ?_) hx'
      intro y hy
      obtain ⟨i, hi, hy⟩ := hy
      exact ⟨i, Nat.le_succ_of_le hi, hy⟩

private theorem jqN_pow_not_mem_full (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) (hallM : Hall M) (a : ℕ) :
    jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a) := by
  have h0 : jqN p ∉ modularFunctionFieldFull M := jqN_prime_not_mem_full M p hpM hallM
  rcases a with - | k
  · rw [jqN_congr (show p ^ (0 + 1) = p by rw [zero_add, pow_one]),
      full_congr (show M * p ^ 0 = M by rw [pow_zero, mul_one])]
    exact h0
  · intro hmem
    have h1 := jqN_pow_not_mem_adjoin_full M p k h0
    exact h1 (full_le_adjoin_chain M p hpM (k + 1) hmem)

section Shapes

variable {K : Type} [Field K] [Algebra ℚ K]

private theorem root_shape (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0) :
    ∃ a : ℕ, ∃ _ : NeZero a, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
      y = TS K (p * (a * a)) (ζ ^ (b * a)) := by
  have hid := minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ hallM
  have hcomp : (qExpand K p).comp (((coeffEmb K).comp (qExpand ℚ M)).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    refine RingHom.ext fun z => ?_
    simp only [RingHom.comp_apply]
    rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
    exact qExpand_congr (mul_comm p M) _
  rw [← hcomp, ← Polynomial.map_map, hid, Polynomial.eval_map, Polynomial.eval₂_finsetProd] at hy
  obtain ⟨a, ha, hy⟩ := Finset.prod_eq_zero_iff.mp hy
  rw [Polynomial.eval₂_finsetProd] at hy
  obtain ⟨b, hb, hy⟩ := Finset.prod_eq_zero_iff.mp hy
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, sub_eq_zero] at hy
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dite_eq_right ha0] at hy
  have : NeZero a := ⟨ha0⟩
  refine ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b, (Finset.mem_range.mp (Finset.mem_filter.mp hb).1),
    ?_⟩
  rw [hy, coeffEmb_jq]
  exact qExpand_TS p (a * a) (ζ ^ (b * a))

private theorem htw_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0)
    (w : Kˣ) (hw : y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq))) : w = 1 := by
  obtain ⟨a, _, haM, b, hb, rfl⟩ := root_shape M p ζ hζ hallM y hy
  rw [coeffEmb_jq] at hw
  change TS K (p * (a * a)) (ζ ^ (b * a)) = TS K (M * p * M) w at hw
  obtain ⟨he, hu⟩ := TS_injective hw
  have haM' : a = M := by
    have h2 : a * a = M * M := by
      have hp0 : 0 < p := hp.out.pos
      have : p * (a * a) = p * (M * M) := by rw [he]; ring
      exact Nat.eq_of_mul_eq_mul_left hp0 this
    exact Nat.mul_self_inj.mp h2
  subst haM'
  have hb0 : b = 0 := by
    rw [Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne a))] at hb
    omega
  subst hb0
  rw [zero_mul, pow_zero] at hu
  exact hu.symm

private theorem hsp_of (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0) :
    y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p))) := by
  obtain ⟨a, _, haM, b, _, rfl⟩ := root_shape M p ζ hζ hallM y hy
  rw [iota_jqN]
  intro hh
  obtain ⟨he, _⟩ := TS_injective hh
  have hp2 : 2 ≤ p := hp.out.two_le
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have ha : a ≤ M := Nat.le_of_dvd hM haM
  have h1 : a * a = (M * p) * (M * p) := by
    have : p * (a * a) = p * ((M * p) * (M * p)) := by rw [he]; ring
    exact Nat.eq_of_mul_eq_mul_left hp.out.pos this
  have h2 : a = M * p := Nat.mul_self_inj.mp h1
  have : M * p ≤ M := h2 ▸ ha
  have : M * 2 ≤ M * p := Nat.mul_le_mul_left M hp2
  omega

end Shapes

/-! ## The strong induction and the capstone -/

/-- **The strong induction of math/010 §7.** From the seven significant
statements, `Tight` and `Gen` hold at every divisor of every `N ≠ 0`. It is the
source of the capstone's corollary layer (`modularFunctionField_eq_full`,
`finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi`), so it is
kept in this module; `functionFieldGeneration` consumes it just below. -/
private theorem hall_all : ∀ N : ℕ, N ≠ 0 → Hall N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro hN d hdN hd
  by_cases hdlt : d < N
  · exact ih d hdlt (NeZero.ne d) d dvd_rfl
  have hdN' : d = N := le_antisymm (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) hdN) (not_lt.mp hdlt)
  subst hdN'
  have hprop : ∀ m : ℕ, m ∣ d → m < d → Hall m := fun m _ hlt => ih m hlt (by
    rintro rfl; exact absurd hlt (by have := Nat.pos_of_ne_zero hN; omega))
  by_cases h1 : d = 1
  · subst h1; exact ⟨tight_one, gen_one⟩
  have hgen : Gen d := by
    unfold Gen
    refine modularFunctionField_eq_full_of d ?_ ?_
    · intro M _ p hp hMp
      have : Fact (Nat.Prime p) := ⟨hp⟩
      have hMlt : M < d := by
        rw [← hMp]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
      have hallM : Hall M := hprop M ⟨p, hMp.symm⟩ hMlt
      have hmem := jqN_div_mem_modularFunctionField M p (K := CyclotomicField (M * p) ℚ)
        (cycUnit (M * p)) (cycUnit_spec (M * p))
        (fun y hy w hw => htw_of M p (cycUnit (M * p) ^ (M * p / M))
          (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM y hy w hw)
        (fun y hy => hsp_of M p (cycUnit (M * p) ^ (M * p / M))
          (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM y hy)
      rw [mff_congr hMp] at hmem
      exact hmem
    · intro M _ p hp hMp
      have hMlt : M < d := by
        rw [← hMp]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
      exact (hprop M ⟨p, hMp.symm⟩ hMlt M dvd_rfl).2
  refine ⟨?_, hgen⟩
  unfold Tight
  set p := d.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime h1
  have : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨k, M, hpM, hdM⟩ := Nat.exists_eq_pow_mul_and_not_dvd hN p hp.ne_one
  have hM0 : M ≠ 0 := by rintro rfl; rw [mul_zero] at hdM; exact hN hdM
  have : NeZero M := ⟨hM0⟩
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := by
    rcases k with - | a
    · exfalso
      have : p ∣ d := Nat.minFac_dvd d
      rw [hdM, pow_zero, one_mul] at this
      exact hpM this
    · exact ⟨a, rfl⟩
  have hdM' : d = M * p ^ (a + 1) := by rw [hdM, mul_comm]
  have hlow_dvd : M * p ^ a ∣ d := ⟨p, by rw [hdM', pow_succ, mul_assoc]⟩
  have hlow_lt : M * p ^ a < d := by
    rw [hdM', pow_succ, ← mul_assoc]
    exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (mul_ne_zero hM0 (pow_ne_zero _ hp.ne_zero)))
      hp.one_lt
  have hall_low : Hall (M * p ^ a) := hprop _ hlow_dvd hlow_lt
  have hallM : Hall M := fun e he _ => hall_low e (he.trans ⟨p ^ a, rfl⟩)
  have hlowdeg : IntermediateField.relfinrank ℚ⟮jq⟯ (modularFunctionFieldFull (M * p ^ a)) =
      dedekindPsi (M * p ^ a) := by
    have hh := hall_low (M * p ^ a) dvd_rfl
    exact relfinrank_full_of _ hh.1 hh.2
  have hstep := relfinrank_full_eq_mul M p a
    (full_eq_adjoin_full_div_prime M p a hpM) (jqN_pow_not_mem_full M p hpM hallM a)
  have htower := IntermediateField.relfinrank_mul_relfinrank (F0_le_full (M * p ^ a))
    (full_degeneracy_le (N := M * p ^ a) (M := M * p ^ (a + 1)) ⟨p, by rw [pow_succ, mul_assoc]⟩)
  rw [← relfinrank_modularFunctionField d]
  unfold Gen at hgen
  rw [hgen, full_congr hdM', ← htower, hlowdeg, hstep]
  have hpsi : dedekindPsi d = dedekindPsi (M * p ^ a) * (if a = 0 then p + 1 else p) := by
    rw [hdM']
    split_ifs with ha
    · subst ha
      rw [pow_zero, mul_one, zero_add, pow_one]
      exact dedekindPsi_mul_prime_not_dvd hp hpM
    · have h2 : M * p ^ (a + 1) = M * p ^ a * p := by rw [pow_succ, mul_assoc]
      rw [h2]
      refine @dedekindPsi_mul_prime_dvd (M * p ^ a) p
        ⟨mul_ne_zero hM0 (pow_ne_zero _ hp.ne_zero)⟩ hp ⟨M * p ^ (a - 1), ?_⟩
      obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
      rw [Nat.succ_sub_one, pow_succ]; ring
  rw [hpsi]

/-- **The theorem.** For every `N ≠ 0`, every `j(q ^ d)` with `d ∣ N` lies in
`ℚ(j(q), j(q ^ N))`: the function field of `X₀(N)` is generated by `j` and `j_N`.
Unconditional. Verbatim from
`Theorems/Thm_ModularCurve_functionFieldGeneration.lean`. -/
theorem functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  (functionFieldGeneration_iff_full_eq N).mpr (hall_all N (NeZero.ne N) N dvd_rfl).2.symm

/-- The two-generator field is the full divisor field. Verbatim from
`Theorems/Thm_ModularCurve_modularFunctionField_eq_full.lean`. -/
theorem modularFunctionField_eq_full (N : ℕ) [NeZero N] :
    modularFunctionField N = modularFunctionFieldFull N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).2

/-- The modular equation at level `N` has full degree `ψ(N)`. Verbatim from
`Theorems/Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi.lean`. -/
theorem finrank_adjoin_jqN_eq_dedekindPsi (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).1

/-- The full field has degree `ψ(N)` over `ℚ(j)`. Verbatim from
`Theorems/Thm_ModularCurve_relfinrank_full_eq_dedekindPsi.lean`. -/
theorem relfinrank_full_eq_dedekindPsi (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull N) = dedekindPsi N := by
  rw [← modularFunctionField_eq_full N, relfinrank_modularFunctionField N]
  exact finrank_adjoin_jqN_eq_dedekindPsi N

end ModularCurve

end

