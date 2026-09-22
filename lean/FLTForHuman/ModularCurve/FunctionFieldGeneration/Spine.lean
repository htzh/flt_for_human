/-
  The spine of `functionFieldGeneration`: a proved conditional capstone.

  FLT provenance, pinned `aa2d8b3`:
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` —
  lines 106–109 (`iota_jqN`, over the interface's `coeffEmb_qExpand`);
  199–240 (the cyclotomic root, `cycUnit`, `isPrimitiveRoot_pow_div`);
  413–435 (`Tight`/`Gen`/`Hall` and the congruence plumbing);
  436–466 (the `ψ` arithmetic); 467–613 (`tight_one` through `hsp_of`);
  614–700 (`hall_all`).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_functionFieldGeneration.lean

  This is the artifact `PORTING-FFG.md` §7.4 prescribes: a **conditional**
  capstone whose hypotheses are FLT's significant remaining statements, proved
  outright so that it contains no `sorryAx`. `hall_all` is the strong induction
  of math/010 §7 carrying the two invariants `Tight` (the relative degree of
  `ℚ⟮jq⟯(jqN d)` over `ℚ⟮jq⟯` is `ψ(d)`) and `Gen` (the two-generator field is
  already the full divisor field) over the divisor lattice; the block above it is
  glue. `functionFieldGeneration_of` applies Layer 0's
  `functionFieldGeneration_iff_full_eq` to `hall_all`.

  `Inputs` collects the significant statements the spine consumes, stated as in
  the pin so that discharging one is a drop-in replacement. Three of the original
  ten have since been discharged — `dedekindPsi_mul_of_coprime` and
  `dedekindPsi_prime_pow`, now public lemmas in `Defs/Jq.lean` beside
  `dedekindPsi`, and `relfinrank_modularFunctionField`, now a public lemma in
  `Defs/Fields.lean` beside `adjoin_jq_le` — so the structure has **seven**
  fields. Nothing else is discharged: the unconditional capstone stays the
  consumer's deferred `sorry`. The auxiliary block is `private`; the public
  surface is `Tight`, `Gen`, `Hall`, `Inputs` and `functionFieldGeneration_of`.

  Two of the seven fields state FLT's `hall` hypothesis as `Hall M →` rather than
  writing the conjunction out. `Hall` is an `abbrev` for exactly that conjunction
  (`Tight`-and-`Gen` at every divisor), so the two are definitionally the pin's;
  the abbreviation is what the induction actually consumes. FLT's `iota_jq`
  (110–112) and `cycUnit_pow` (213) are not ported: nothing here consumes them.

  Assumes `coeffMap`/`coeffEmb`/`qExpand` (`Defs/Laurent`), `qTwist`
  (`Defs/Twist`), `jq`/`jqN`/`dedekindPsi`/`jGen` (`Defs/Jq`), the two function
  fields and `jqd_mem_full`/`full_degeneracy_le`/`relfinrank_modularFunctionField`
  (`Defs/Fields`), `TS` and its lemmas (`Defs/TS`), and the §2 collapse
  (`Collapse.lean`).
-/
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.FieldTheory.Relrank
import Mathlib.Data.Nat.Factorization.Basic
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import FLTForHuman.ModularCurve.Defs.TS

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField
open scoped IntermediateField

namespace ModularCurve

/-! ## Transport

`coeffMap_qExpand` and `coeffEmb_qExpand` are part of the cone's outbound
interface and now live beside `coeffMap`/`coeffEmb` in `Defs/Laurent.lean`; this
module imports them rather than redeclaring them. -/

section FieldTransport

variable {K : Type*} [Field K] [Algebra ℚ K]

private theorem iota_jqN (N d : ℕ) [NeZero N] [NeZero d] :
    coeffEmb K (qExpand ℚ N (jqN d)) = TS K (N * d) 1 := by
  rw [jqN, coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand, TS, qTwist_one_apply]

end FieldTransport

/-! ## Cyclotomic roots -/

private theorem exists_isPrimitiveRoot_cyclotomicField (N : ℕ) [NeZero N] :
    ∃ z : CyclotomicField N ℚ, IsPrimitiveRoot z N := by
  have : NeZero ((N : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr (NeZero.ne N)⟩
  have : IsCyclotomicExtension {N} ℚ (CyclotomicField N ℚ) :=
    CyclotomicField.isCyclotomicExtension N ℚ
  exact IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField N ℚ)
    (Set.mem_singleton N) (NeZero.ne N)

private def cycUnit (N : ℕ) [NeZero N] : (CyclotomicField N ℚ)ˣ :=
  ((exists_isPrimitiveRoot_cyclotomicField N).choose_spec.isUnit (NeZero.ne N)).unit

private theorem cycUnit_spec (N : ℕ) [NeZero N] :
    IsPrimitiveRoot ((cycUnit N : (CyclotomicField N ℚ)ˣ) : CyclotomicField N ℚ) N := by
  rw [cycUnit, IsUnit.unit_spec]
  exact (exists_isPrimitiveRoot_cyclotomicField N).choose_spec

section PropDiv

variable {K : Type*} [Field K] [Algebra ℚ K]

omit [Algebra ℚ K] in
private theorem isPrimitiveRoot_pow_div {N : ℕ} [NeZero N] {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) N)
    {p : ℕ} (hpN : p ∣ N) : IsPrimitiveRoot ((ζ ^ (N / p) : Kˣ) : K) p := by
  have hN : N ≠ 0 := NeZero.ne N
  have hd0 : N / p ≠ 0 := by
    intro h0
    have hc := Nat.div_mul_cancel hpN
    rw [h0, zero_mul] at hc
    exact hN hc.symm
  have h := hζ.pow_of_dvd hd0 (Nat.div_dvd_of_dvd hpN)
  rw [Nat.div_div_self hpN hN] at h
  rwa [← Units.val_pow_eq_pow_val] at h

end PropDiv

/-! ## Congruence plumbing and `ψ` arithmetic -/

private theorem jqN_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) : jqN n = jqN m := by
  subst h; rfl

private theorem full_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionFieldFull n = modularFunctionFieldFull m := by
  subst h; rfl

private theorem mff_congr {n m : ℕ} [NeZero n] [NeZero m] (h : n = m) :
    modularFunctionField n = modularFunctionField m := by
  subst h; rfl

/-! ## The invariants -/

/-- The two invariants of the strong induction, bundled. `Tight d` says the
relative degree of `ℚ⟮jq⟯(jqN d)` over `ℚ⟮jq⟯` is exactly `ψ(d)`. -/
abbrev Tight (d : ℕ) [NeZero d] : Prop :=
  Module.finrank ℚ⟮jq⟯ (IntermediateField.adjoin ℚ⟮jq⟯ ({jqN d} : Set (LaurentSeries ℚ))) =
    dedekindPsi d

/-- `Gen d` says the two-generator field already contains every `j(q ^ e)`, `e ∣ d`. -/
abbrev Gen (d : ℕ) [NeZero d] : Prop := modularFunctionField d = modularFunctionFieldFull d

/-- `Hall N` is the strong-induction hypothesis: `Tight` and `Gen` hold at every
divisor of `N`. -/
abbrev Hall (N : ℕ) : Prop := ∀ d : ℕ, d ∣ N → ∀ [NeZero d], Tight d ∧ Gen d

/-! ## `Inputs`: the significant statements

Each field is one of the 24 nodes of `PORTING-FFG.md` §7.3 that the spine
consumes but does not prove, stated as in the pin. The docstring on each says why
it survives pruning. The three fields the spine originally carried for
`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow` and
`relfinrank_modularFunctionField` have since been discharged, into `Defs/Jq.lean`
and `Defs/Fields.lean`; the `ψ` helpers below now use the real lemmas, and
`relfinrank_full_of` calls the real `relfinrank_modularFunctionField`. -/

structure Inputs where
  /-- The tower step for `Gen`: `jqN (p ^ (a+1))` generates `modularFunctionFieldFull`
  over `modularFunctionFieldFull (M * p ^ a)` when `p ∤ M`. -/
  full_eq_adjoin_full_div_prime :
    ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ), ¬ p ∣ M →
      modularFunctionFieldFull (M * p ^ (a + 1)) =
        IntermediateField.adjoin ℚ (insert (jqN (p ^ (a + 1)))
          (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ)))
  /-- `jqN p ∉ modularFunctionFieldFull M` for `p ∤ M`: the non-membership the
  prime-power tower needs. -/
  jqN_prime_not_mem_full :
    ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact (Nat.Prime p)], ¬ p ∣ M → Hall M →
      jqN p ∉ modularFunctionFieldFull M
  /-- The prime-power non-membership, propagated up the tower of `jqN (p ^ i)`. -/
  jqN_pow_not_mem_adjoin_full :
    ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ),
      jqN p ∉ modularFunctionFieldFull M →
        jqN (p ^ (a + 2)) ∉ IntermediateField.adjoin ℚ
          ((modularFunctionFieldFull M : Set (LaurentSeries ℚ)) ∪
            {x : LaurentSeries ℚ | ∃ i : ℕ, i ≤ a + 1 ∧ x = jqN (p ^ i)})
  /-- The explicit minimal polynomial of `jqN M` over `ℚ⟮jq⟯`, mapped into `K`: the
  slot description `root_shape` reads its roots off. -/
  minpoly_jqN_map_eq_prod_slots :
    ∀ {K : Type} [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M] (ζ : Kˣ)
      (_hζ : IsPrimitiveRoot (ζ : K) M), Hall M →
      (minpoly ℚ⟮jq⟯ (jqN M)).map
          (((coeffEmb K).comp (qExpand ℚ M)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) =
        ∏ a ∈ M.divisors,
          ∏ b ∈ (Finset.range (M / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
            (Polynomial.X - Polynomial.C (if h : a = 0 then 0
              else letI : NeZero a := ⟨h⟩
                qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))))
  /-- The `Gen` step of the induction: if every proper divisor `M` of `N` with
  `M * p = N` satisfies both step conditions, then `modularFunctionField N` is full. -/
  modularFunctionField_eq_full_of :
    ∀ (N : ℕ) [NeZero N],
      (∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N → jqN M ∈ modularFunctionField N) →
      (∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
        modularFunctionField M = modularFunctionFieldFull M) →
      modularFunctionField N = modularFunctionFieldFull N
  /-- The slot-analysis input feeding `Gen`: `jqN M ∈ modularFunctionField (M * p)`
  from the twist and slot hypotheses `htw_of`/`hsp_of` discharge. -/
  jqN_div_mem_modularFunctionField :
    ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact (Nat.Prime p)] {K : Type} [Field K] [Algebra ℚ K]
      (ζ : Kˣ) (_hζ : IsPrimitiveRoot (ζ : K) (M * p))
      (_htw : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0 →
        ∀ w : Kˣ, y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq)) → w = 1)
      (_hsp : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map
        (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0 →
        y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))),
      jqN M ∈ modularFunctionField (M * p)
  /-- The degree-multiplication step for `Tight`: each prime-power tower step has
  relative degree `p + 1` (first step) or `p` (later steps). -/
  relfinrank_full_eq_mul :
    ∀ (M : ℕ) [NeZero M] (p : ℕ) [Fact (Nat.Prime p)] (a : ℕ),
      modularFunctionFieldFull (M * p ^ (a + 1)) = IntermediateField.adjoin ℚ (insert
        (jqN (p ^ (a + 1))) (modularFunctionFieldFull (M * p ^ a) : Set (LaurentSeries ℚ))) →
      jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a) →
      IntermediateField.relfinrank (modularFunctionFieldFull (M * p ^ a))
        (modularFunctionFieldFull (M * p ^ (a + 1))) = if a = 0 then p + 1 else p

/-! ## The auxiliary block -/

private theorem dedekindPsi_mul_prime_not_dvd {m p : ℕ} (hp : p.Prime) (hpm : ¬ p ∣ m) :
    dedekindPsi (m * p) = dedekindPsi m * (p + 1) := by
  have hco : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  rw [dedekindPsi_mul_of_coprime m p hco, dedekindPsi_prime hp]

private theorem dedekindPsi_mul_prime_dvd {m p : ℕ} (hm : m ≠ 0) (hp : p.Prime)
    (hpm : p ∣ m) : dedekindPsi (m * p) = dedekindPsi m * p := by
  obtain ⟨k, u, hpu, hmu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp.ne_one
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with - | k'
    · exfalso
      rw [hmu, pow_zero, one_mul] at hpm
      exact hpu hpm
    · exact ⟨k', rfl⟩
  subst hmu
  have hcou : ∀ j : ℕ, j ≠ 0 → Nat.Coprime (p ^ j) u :=
    fun j _ => Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpu)
  have h1 : p ^ (k' + 1) * u * p = p ^ (k' + 2) * u := by ring
  rw [h1, dedekindPsi_mul_of_coprime _ u (hcou _ (Nat.succ_ne_zero _)),
    dedekindPsi_mul_of_coprime _ u (hcou _ (Nat.succ_ne_zero _)),
    dedekindPsi_prime_pow p (k' + 2) hp (Nat.succ_ne_zero _),
    dedekindPsi_prime_pow p (k' + 1) hp (Nat.succ_ne_zero _)]
  have h2 : k' + 2 - 1 = k' + 1 := rfl
  have h3 : k' + 1 - 1 = k' := rfl
  rw [h2, h3]
  ring

private theorem tight_one : Tight 1 := by
  unfold Tight
  have h1 : jqN 1 = jq := by rw [jqN, qExpand_one_apply]
  rw [h1, dedekindPsi_one]
  have h2 : IntermediateField.adjoin ℚ⟮jq⟯ ({jq} : Set (LaurentSeries ℚ)) =
      (⊥ : IntermediateField ℚ⟮jq⟯ (LaurentSeries ℚ)) := by
    rw [IntermediateField.adjoin_simple_eq_bot_iff, IntermediateField.mem_bot]
    exact ⟨jGen, rfl⟩
  rw [h2]
  exact IntermediateField.finrank_bot

private theorem gen_one : Gen 1 := by
  unfold Gen
  refine le_antisymm (modularFunctionField_le_full 1) ?_
  rw [modularFunctionFieldFull, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  have hd1 : d = 1 := Nat.dvd_one.mp hdvd
  subst hd1
  rw [qExpand_one_apply]
  exact jq_mem 1

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

private theorem full_le_adjoin_chain (h : Inputs) (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
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
      rw [h.full_eq_adjoin_full_div_prime M p k hpM, IntermediateField.adjoin_le_iff,
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

private theorem jqN_pow_not_mem_full (h : Inputs) (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (hpM : ¬ p ∣ M) (hallM : Hall M) (a : ℕ) :
    jqN (p ^ (a + 1)) ∉ modularFunctionFieldFull (M * p ^ a) := by
  have h0 : jqN p ∉ modularFunctionFieldFull M := h.jqN_prime_not_mem_full M p hpM hallM
  rcases a with - | k
  · rw [jqN_congr (show p ^ (0 + 1) = p by rw [zero_add, pow_one]),
      full_congr (show M * p ^ 0 = M by rw [pow_zero, mul_one])]
    exact h0
  · intro hmem
    have h1 := h.jqN_pow_not_mem_adjoin_full M p k h0
    exact h1 (full_le_adjoin_chain h M p hpM (k + 1) hmem)

section Shapes

variable {K : Type} [Field K] [Algebra ℚ K]

private theorem root_shape (h : Inputs) (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0) :
    ∃ a : ℕ, ∃ _ : NeZero a, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
      y = TS K (p * (a * a)) (ζ ^ (b * a)) := by
  have hid := h.minpoly_jqN_map_eq_prod_slots (K := K) M ζ hζ hallM
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
  rw [hy]
  change qExpand K p (TS K (a * a) (ζ ^ (b * a))) = _
  rw [qExpand_TS]

private theorem htw_of (h : Inputs) (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0)
    (w : Kˣ) (hw : y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq))) : w = 1 := by
  obtain ⟨a, _, haM, b, hb, rfl⟩ := root_shape h M p ζ hζ hallM y hy
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

private theorem hsp_of (h : Inputs) (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) M) (hallM : Hall M) (y : LaurentSeries K)
    (hy : Polynomial.eval y ((minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ (M * p))).comp
      (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)))) = 0) :
    y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p))) := by
  obtain ⟨a, _, haM, b, _, rfl⟩ := root_shape h M p ζ hζ hallM y hy
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

/-! ## The strong induction and the conditional capstone -/

private theorem hall_all (h : Inputs) : ∀ N : ℕ, N ≠ 0 → Hall N := by
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
    refine h.modularFunctionField_eq_full_of d ?_ ?_
    · intro M _ p hp hMp
      have : Fact (Nat.Prime p) := ⟨hp⟩
      have hMlt : M < d := by
        rw [← hMp]; exact lt_mul_of_one_lt_right (Nat.pos_of_ne_zero (NeZero.ne M)) hp.one_lt
      have hallM : Hall M := hprop M ⟨p, hMp.symm⟩ hMlt
      have hmem := h.jqN_div_mem_modularFunctionField M p (K := CyclotomicField (M * p) ℚ)
        (cycUnit (M * p)) (cycUnit_spec (M * p))
        (fun y hy w hw => htw_of h M p (cycUnit (M * p) ^ (M * p / M))
          (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM y hy w hw)
        (fun y hy => hsp_of h M p (cycUnit (M * p) ^ (M * p / M))
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
  have hstep := h.relfinrank_full_eq_mul M p a
    (h.full_eq_adjoin_full_div_prime M p a hpM) (jqN_pow_not_mem_full h M p hpM hallM a)
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
      refine dedekindPsi_mul_prime_dvd (mul_ne_zero hM0 (pow_ne_zero _ hp.ne_zero)) hp
        ⟨M * p ^ (a - 1), ?_⟩
      obtain ⟨a', rfl⟩ := Nat.exists_eq_succ_of_ne_zero ha
      rw [Nat.succ_sub_one, pow_succ]; ring
  rw [hpsi]

theorem functionFieldGeneration_of (h : Inputs) (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  (functionFieldGeneration_iff_full_eq N).mpr (hall_all h N (NeZero.ne N) N dvd_rfl).2.symm

end ModularCurve

end

