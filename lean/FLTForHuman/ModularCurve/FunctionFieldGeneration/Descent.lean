/-
  The descent by one prime, with its slot hypotheses discharged, and the one-prime
  reduction of `Gen`.

  `jqN_div_mem_modularFunctionField` is the descent by one prime: under `Hall M`,
  `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M * p)))`. The mathematics is a *comparison of two
  polynomials* over the level-`M * p` field, both read at the level-`M * p` nome:

  * `exists_phiAtSeed_roots` states, about the level-`p` equation `A`, what its roots are:
    the conjugate `j(q ^ (conjLevel M p))` and the `p` twists
    `j(ζ ^ (b * M) q ^ (twistLevel M p))`;
  * `exists_transported_minpoly` states, about the certificate `B` — the conjugate equation
    of `j(q ^ M)` — that it is monic, split, squarefree, has `x₀` as a root, and that its
    roots are the slot values `j(ζ ^ (p * b * a) q ^ (slotLevel p a))` for `a ∣ M`,
    `b < M / a`;
  * the theorem makes the two descriptions face each other, in one place and one place
    only. A common root is then the untwisted twist, which is `x₀`.

  Every step of index arithmetic that comparison needs is a named fact rather than a
  tactic incantation in the mainline: `slotLevel_ne_conjLevel` (no divisor of `M` is the
  conjugate's slot index), `slotUnit_eq_one_of_twistLevel` (the twist's level is the slot
  `(M, 0)`, whose unit is `1`), `eq_zero_of_pow_eq_one` (`ζ`'s order kills a twist index
  below `p`). The descent's body therefore reads as the argument: two producers, one case
  split, one helper per branch.

  ## The field is chosen, not passed

  The descent reads in `CyclotomicField (M * p) ℚ`, at `cycUnit (M * p)`: a splitting
  field and a root of unity are chosen data of the proof, not parameters of the theorem.
  They are definitions here (`Lc`, `slotUnit`), so no statement carries a type parameter
  and no call site writes `(K := …)`. `Tight M` is likewise the first projection of the
  `Hall M` hypothesis, consumed inside `exists_transported_minpoly`.

  ## Layers, in dependency order

  * `Lc`, `nomeMap`, `nomeAlgebra`, `x₀`: the field, the nome readings and the element the
    theorem is about. `nomeMap` keeps a field parameter because `nomeMap_qExpand` composes
    two levels over one field; everything the statements name is read at `Lc`;
  * `slotLevel` / `conjLevel` / `twistLevel`: the three levels the statements name, as
    `abbrev`s so that instance search finds `NeZero` for `TS`'s level argument;
  * `slotLevel_ne_conjLevel`, `slotUnit_eq_one_of_twistLevel`, `eq_zero_of_pow_eq_one`:
    the arithmetic of the comparison, one claim per branch;
  * `slotUnit`, `isPrimitiveRoot_slotUnit`: the `M`-th root the certificate is read at;
  * `qExpand_qTwist_coeffEmb`: the translation between the `qExpand`/`qTwist` spelling of a
    slot and the `TS` spelling;
  * `slotTS`, `slotTS_eq`, `exists_slotValue_of_mem_slotValues`: the certificate's
    slot values, their spelling as `SlotProduct`'s `sv` read at `p`, and the index shape
    of a slot;
  * `exists_phiAtSeed_roots`, `exists_transported_minpoly`: the two producers, each stating
    facts about one polynomial. The certificate's proof carries its own root theory — the
    slot product, its splitting, and the distinctness `sv_inj_slot` gives;
  * `mem_of_mem_range_nome`: the transport that undoes the nome reading;
  * `jqN_div_mem_modularFunctionField`: the descent.

  Its second subject is the one-prime reduction of `Gen`, in the same `Hall` form:
  `modularFunctionField_eq_full_of` takes the strong induction hypothesis itself
  (`∀ m < N, m ≠ 0 → Hall m`) and derives what it consumes — the level `m < N` that a
  proper divisor `d` divides with `N = m * p`, `Hall m`, `jqN m ∈ F_N` from the descent
  above, and `Gen m` from `Hall m`. The caller passes `ih` unchanged.

  ## Verification tier

  No `spec-pin:` header: the public statements are the port's own — the descent takes
  `Hall M` with its certificate private, and the reduction is stated in the `Hall` form —
  so a wire would diff nothing. Registered by `spec/unwired_register.py`.

  If a future public declaration in this module transcribes a pinned statement, it needs a
  `spec-pin:` line, and this note is then wrong.

  ## Assumptions

  `Polynomial.mem_range_of_unique_common_root`, `exists_phiIrreducible_evalSymm`,
  `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `isRoot_prime_at_slot_iff`,
  `iota_jqN`, `minpoly_jqN_map_eq_prod_slots`, `isIntegral_adjoin_jqN`,
  `modularFunctionField`, `adjoin_jq_le`, `jqN_mem`, `jqd_mem_full`, `cycUnit`,
  `coeffMap_injective`, `coeffEmb_qExpand`, `qExpand_injective`, `TS`, `TS_injective`,
  `TS_congr`, `qExpand_TS`, `sv`, `sv_eq_TS`, `sv_inj_slot`, `slotValues`, `prod_slotValues`,
  `nodup_slotValues` and `lt_of_mul_prime_eq`.
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

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

/-! ## The field, fixed once

The descent only ever reads in `CyclotomicField (M * p) ℚ`. Making that a definition
rather than a section variable is what removes `K` from every statement below. -/

/-- The field the descent reads everything in: the `(M * p)`-th cyclotomic field, as the
coefficients of the nome expansions. -/
private abbrev Lc (M p : ℕ) : Type := LaurentSeries (CyclotomicField (M * p) ℚ)

/-- Read the `j`-line at the level-`N` nome, with coefficients in `K`. The field stays a
parameter here: `nomeMap_qExpand` composes two levels over one field. -/
private def nomeMap (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    ℚ⟮jq⟯ →+* LaurentSeries K :=
  ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

/-- Read the level-`N` function field at the level-`N` nome, inside the cyclotomic field.
This is the map the descent's `Algebra` structure on `Lc` is built from. -/
private def nomeAlgebra (N : ℕ) [NeZero N] :
    ↥(modularFunctionField N) →+* LaurentSeries (CyclotomicField N ℚ) :=
  ((coeffEmb (CyclotomicField N ℚ)).comp (qExpand ℚ N)).comp
    (algebraMap ↥(modularFunctionField N) (LaurentSeries ℚ))

/-- The element whose membership in the function field is the whole theorem: `j(q ^ M)`
read at the level-`M * p` nome. -/
private abbrev x₀ (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] : Lc M p :=
  coeffEmb (CyclotomicField (M * p) ℚ) (qExpand ℚ (M * p) (jqN M))

/-- Reading the `j`-line at the level `M` and then at the level `e` is reading it at the
level `M * e`. -/
private theorem nomeMap_qExpand (K : Type*) [Field K] [Algebra ℚ K] (M e : ℕ) [NeZero M]
    [NeZero e] : (qExpand K e).comp (nomeMap K M) = nomeMap K (M * e) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply, nomeMap]
  rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
  exact qExpand_congr (mul_comm e M) _

/-! ## The three levels the two equations are read at

Each is the exponent of a `TS`, i.e. the `e` in `j(u q ^ e)`, so naming them is what lets
the statements say *which* slot an index denotes instead of repeating the arithmetic. They
are `abbrev`s, not `def`s: instance search unfolds `abbrev`, so `NeZero (conjLevel M p)` is
found for `TS`'s level argument, where a `def` would leave every such `TS` unelaboratable. -/

/-- The level of the certificate's slot `a`: `p * a ^ 2`. -/
private abbrev slotLevel (p a : ℕ) : ℕ := p * (a * a)

/-- The level of the conjugate root of the level-`p` equation: `p` times the twist's level.
It is the certificate's slot level at `a = M * p`. -/
private abbrev conjLevel (M p : ℕ) : ℕ := p * (p * (M * p * M))

/-- The level of the `p` twists of the level-`p` equation: the certificate's slot level at
`a = M`. -/
private abbrev twistLevel (M p : ℕ) : ℕ := (M * p) * M

/-- The `M`-th root of unity the certificate's slots are read at: the `(M * p)`-th
cyclotomic unit raised to the `p`. -/
private abbrev slotUnit (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] :
    (CyclotomicField (M * p) ℚ)ˣ :=
  cycUnit (M * p) ^ p

/-- The slot root is primitive of order `M`. -/
private theorem isPrimitiveRoot_slotUnit (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] :
    IsPrimitiveRoot ((slotUnit M p : (CyclotomicField (M * p) ℚ)ˣ) : CyclotomicField (M * p) ℚ)
      M := by
  have h := isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) (dvd_mul_right M p)
  rwa [show M * p / M = p from Nat.mul_div_right p (NeZero.pos M)] at h

/-! ## The arithmetic of the comparison

Three claims, one per step the comparison needs. Each is what a comment would otherwise
carry about the levels above. -/

/-- No divisor of `M` is the conjugate's slot index: the conjugate sits at the slot level
`a = M * p`, and `M * p > M`. -/
private theorem slotLevel_ne_conjLevel {M p a : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    (haM : a ∣ M) : conjLevel M p ≠ slotLevel p a := by
  simp only [conjLevel, slotLevel]
  intro he
  have h1 : p * (M * p * M) = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
  have h2 : a * a = (M * p) * (M * p) := by rw [← h1]; ring
  have h3 : a = M * p := Nat.mul_self_inj.mp h2
  have h4 : p ≤ 1 := Nat.le_of_mul_le_mul_left
    (by rw [← h3, mul_one]; exact Nat.le_of_dvd (NeZero.pos M) haM) (NeZero.pos M)
  have hp2 : 2 ≤ p := hp.out.two_le
  omega

/-- The twist's level is the slot at `a = M`, and there the slot index range is `1`: a twist
that is also a slot value carries the certificate's unit at `(M, 0)`, which is `1`. -/
private theorem slotUnit_eq_one_of_twistLevel {M p a b : ℕ} [NeZero M]
    [hp : Fact (Nat.Prime p)] (haM : a ∣ M) (hb : b < M / a)
    (he : twistLevel M p = slotLevel p a) : slotUnit M p ^ (b * a) = 1 := by
  simp only [twistLevel, slotLevel] at he
  have h1 : a * a = M * M := Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← he]; ring)
  have h2 : a = M := Nat.mul_self_inj.mp h1
  subst a
  rw [Nat.div_self (NeZero.pos M)] at hb
  have hb0 : b = 0 := by omega
  subst b
  rw [zero_mul, pow_zero]

/-- `ζ ^ (b * M) = 1` with `b < p` forces `b = 0`: `ζ` has order `M * p`, and `b < p` keeps
the exponent `b * M` inside the order. -/
private theorem eq_zero_of_pow_eq_one {M p b : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    (hb : b < p) (h : (cycUnit (M * p) : (CyclotomicField (M * p) ℚ)ˣ) ^ (b * M) = 1) :
    b = 0 := by
  have hM : 0 < M := NeZero.pos M
  have hbM : b * M < M * p := by
    rw [mul_comm M p]
    exact Nat.mul_lt_mul_of_pos_right hb hM
  have huK : ((cycUnit (M * p) : (CyclotomicField (M * p) ℚ)ˣ) : CyclotomicField (M * p) ℚ)
      ^ (b * M) = 1 := by
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  have hbM0 : b * M = 0 :=
    (cycUnit_spec (M * p)).pow_inj hbM (NeZero.pos (M * p)) (by rw [huK, pow_zero])
  rcases Nat.mul_eq_zero.mp hbM0 with h0 | h0
  · exact h0
  · exact absurd h0 (NeZero.ne M)

/-! ## The slot spellings

The certificate's roots are read as `TS` values, while the slot product writes the same
values as `qExpand`/`qTwist` of `coeffEmb jq`. This lemma is that translation. -/

/-- A twisted `j`-slice read over a `ℚ`-algebra is the `TS` value at the same level: `TS` is
this very expression with `jqModC` in place of `coeffEmb jq`. -/
private theorem qExpand_qTwist_coeffEmb {K : Type*} [Field K] [Algebra ℚ K] (e : ℕ)
    [NeZero e] (u : Kˣ) : qExpand K e (qTwist u (coeffEmb K jq)) = TS K e u := by
  rw [TS, coeffEmb_jq]

/-! ## Fact about `A`: the level-`p` equation at the seed -/

/-- Over the level-`M * p` field there is a monic `A` — `Φ_p` seeded at the level-`M * p`
invariant — whose roots, read at that nome, are the conjugate
`j(q ^ (conjLevel M p))` and the `p` twists `j(ζ ^ (b * M) q ^ (twistLevel M p))`. `x₀` is
the untwisted twist, so it is a root of `A`; that is a reading of this `↔` at `b = 0`, not
a conjunct of it. -/
private theorem exists_phiAtSeed_roots {M p : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)] :
    ∃ A : Polynomial ↥(modularFunctionField (M * p)),
      A.Monic ∧
        ∀ y : Lc M p, A.eval₂ (nomeAlgebra (M * p)) y = 0 ↔
          y = TS _ (conjLevel M p) 1 ∨
            ∃ b < p, y = TS _ (twistLevel M p) (cycUnit (M * p) ^ (b * M)) := by
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  refine ⟨phiAtSeed data (⟨jqN (M * p), jqN_mem (M * p)⟩ : modularFunctionField (M * p)),
    phiAtSeed_monic data _, ?_⟩
  intro y
  have hx : (nomeAlgebra (M * p)) ⟨jqN (M * p), jqN_mem (M * p)⟩
      = coeffEmb (CyclotomicField (M * p) ℚ) (qExpand ℚ (M * p) (jqN (M * p))) := rfl
  rw [Polynomial.eval₂_eq_eval_map, phiAtSeed_map, hx]
  rw [show coeffEmb (CyclotomicField (M * p) ℚ) (qExpand ℚ (M * p) (jqN (M * p)))
      = qExpand (CyclotomicField (M * p) ℚ) (p * (M * p * M))
          (qTwist ((1 : (CyclotomicField (M * p) ℚ)ˣ) ^ p)
            (coeffEmb (CyclotomicField (M * p) ℚ) jq)) from by
    rw [one_pow, iota_jqN, qExpand_qTwist_coeffEmb]
    exact TS_congr (by ring) 1]
  refine (isRoot_prime_at_slot_iff (M * p) (cycUnit (M * p)) (cycUnit_spec (M * p)) p
    (dvd_mul_left p M) data (M * p * M) 1 y).trans ?_
  simp only [qExpand_qTwist_coeffEmb, one_pow, one_mul]
  rw [Nat.mul_div_left M hp.out.pos]

/-! ## Facts about `B`: the conjugate equation of `j(q ^ M)` -/

/-- The slot values of the conjugate equation at the level-`M * p` nome, with the `a = 0`
guard the slot product carries. -/
private abbrev slotTS (M p : ℕ) [NeZero M] [hp : Fact (Nat.Prime p)] (a b : ℕ) : Lc M p :=
  if h : a = 0 then 0 else letI : NeZero a := ⟨h⟩;
    TS _ (slotLevel p a) (slotUnit M p ^ (b * a))

/-- The certificate's slot is `sv`, read at the level `p`: `qExpand K p` raises the slot
level `a * a` to `p * (a * a)`, and the `a = 0` guard is the one `sv` carries. -/
private theorem slotTS_eq {M p : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)] (a b : ℕ) :
    slotTS M p a b = qExpand (CyclotomicField (M * p) ℚ) p
      (sv (CyclotomicField (M * p) ℚ) (slotUnit M p) a b) := by
  by_cases ha : a = 0
  · subst ha
    rw [slotTS, dite_eq_left rfl, sv, dite_eq_left rfl, map_zero]
  · have : NeZero a := ⟨ha⟩
    rw [slotTS, dite_eq_right ha, sv_eq_TS, qExpand_TS]

/-- **A slot value is an index.** A value in the slot multiset is
`j(ζ ^ (p * b * a) q ^ (slotLevel p a))` for some `a ∣ M` and `b < M / a`: the index
shape of the level-`M` minimal polynomial's slots, with the `a = 0` guard `slotTS` carries
discharged on the indices that occur. -/
private theorem exists_slotValue_of_mem_slotValues {M p : ℕ} [NeZero M]
    [hp : Fact (Nat.Prime p)] {y : Lc M p}
    (h : y ∈ slotValues M (slotTS (M := M) (p := p))) :
    ∃ (a : ℕ) (_ : NeZero a), a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
      y = TS _ (slotLevel p a) (slotUnit M p ^ (b * a)) := by
  obtain ⟨a, b, ha, hb, h⟩ := mem_slotValues.mp h
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  refine ⟨a, ⟨ha0⟩, Nat.dvd_of_mem_divisors ha, b,
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1), ?_⟩
  rw [h, slotTS, dite_eq_right ha0]

/-- **The certificate.** The conjugate equation of `jqN M` read at the level-`M * p` nome:
monic, split, squarefree, with `x₀` a root, and every root a slot value. One hypothesis,
`Hall M`; `Tight M` and the slot product are consumed here, so neither crosses.

The slot product (`hprod`), its splitting and the distinctness of the slots are this
proof's own, because it is their only reader; what a root of that product looks like is
`exists_slotValue_of_mem_slotValues`, which names no polynomial. -/
private theorem exists_transported_minpoly {M p : ℕ} [NeZero M] [hp : Fact (Nat.Prime p)]
    (hallM : Hall M) :
    ∃ B : Polynomial ↥(modularFunctionField (M * p)),
      B.Monic ∧ (B.map (nomeAlgebra (M * p))).Splits ∧
        (B.map (nomeAlgebra (M * p))).roots.Nodup ∧
        B.eval₂ (nomeAlgebra (M * p)) (x₀ M p) = 0 ∧
        ∀ y : Lc M p, B.eval₂ (nomeAlgebra (M * p)) y = 0 →
          ∃ (a : ℕ) (_ : NeZero a), a ∣ M ∧ ∃ b : ℕ, b < M / a ∧
            y = TS _ (slotLevel p a) (slotUnit M p ^ (b * a)) := by
  classical
  have hmonic : (minpoly ℚ⟮jq⟯ (jqN M)).Monic :=
    minpoly.monic (isIntegral_adjoin_jqN (hallM M dvd_rfl).1)
  have hcomp : (nomeAlgebra (M * p)).comp (IntermediateField.inclusion (adjoin_jq_le (M * p)))
      = nomeMap (CyclotomicField (M * p) ℚ) (M * p) := by
    refine RingHom.ext fun _ => ?_
    simp only [nomeAlgebra, RingHom.comp_apply, nomeMap]
    rfl
  set B : Polynomial ↥(modularFunctionField (M * p)) :=
    (minpoly ℚ⟮jq⟯ (jqN M)).map (IntermediateField.inclusion (adjoin_jq_le (M * p))) with hBdef
  have hBmonic : B.Monic := by
    rw [hBdef]
    exact hmonic.map _
  have hprod : B.map (nomeAlgebra (M * p))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (slotTS M p a b)) := by
    rw [hBdef, Polynomial.map_map, hcomp,
      ← nomeMap_qExpand (K := CyclotomicField (M * p) ℚ) M p,
      ← Polynomial.map_map, nomeMap,
      minpoly_jqN_map_eq_prod_slots (K := CyclotomicField (M * p) ℚ) M (slotUnit M p)
        (isPrimitiveRoot_slotUnit M p) hallM, Polynomial.map_prod]
    refine Finset.prod_congr rfl fun a ha => ?_
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
    simp only [slotTS, dite_eq_right ha0, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
      qExpand_qTwist_coeffEmb, qExpand_TS]
  refine ⟨B, hBmonic, ?_, ?_, ?_, ?_⟩
  · rw [hprod]
    exact Polynomial.Splits.prod fun _ _ =>
      Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _
  · rw [hprod, ← prod_slotValues M (slotTS (M := M) (p := p)), roots_multiset_prod_X_sub_C]
    exact nodup_slotValues fun a b a' b' ha ha' hb hb' h =>
      sv_inj_slot (isPrimitiveRoot_slotUnit M p) (NeZero.ne M)
        (Nat.dvd_of_mem_divisors ha) (Nat.dvd_of_mem_divisors ha')
        (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
        (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
        (qExpand_injective p (by rw [← slotTS_eq a b, ← slotTS_eq a' b']; exact h))
  · have hx : x₀ M p
        = ((coeffEmb (CyclotomicField (M * p) ℚ)).comp (qExpand ℚ (M * p))) (jqN M) := rfl
    rw [Polynomial.eval₂_map, hcomp, nomeMap, ← Polynomial.eval₂_map, hx, Polynomial.eval₂_hom,
      Polynomial.eval_map, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  · intro y hy
    have hne : B.map (nomeAlgebra (M * p)) ≠ 0 := (hBmonic.map _).ne_zero
    have hroots : y ∈ (B.map (nomeAlgebra (M * p))).roots :=
      (Polynomial.mem_roots hne).mpr (by rwa [Polynomial.eval₂_eq_eval_map] at hy)
    rw [hprod, ← prod_slotValues M (slotTS (M := M) (p := p)),
      roots_multiset_prod_X_sub_C] at hroots
    exact exists_slotValue_of_mem_slotValues hroots

/-- **Undoing the nome reading.** If the level-`N` nome image of `y` is rational over the
level-`N` function field, then `y` itself is an element of it: reading the field at a nome
is injective on it. This is the descent's last step. -/
private theorem mem_of_mem_range_nome {N : ℕ} [NeZero N] {y : LaurentSeries ℚ}
    (hy : coeffEmb (CyclotomicField N ℚ) (qExpand ℚ N y) ∈ (nomeAlgebra N).range) :
    y ∈ modularFunctionField N := by
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hy
  have hf' : coeffEmb (CyclotomicField N ℚ) (qExpand ℚ N ((f : LaurentSeries ℚ)))
      = coeffEmb (CyclotomicField N ℚ) (qExpand ℚ N y) := by
    rw [← hf, nomeAlgebra]
    rfl
  have hemb : Function.Injective (coeffEmb (CyclotomicField N ℚ)) :=
    coeffMap_injective ((algebraMap ℚ (CyclotomicField N ℚ)).injective)
  have hval : (f : LaurentSeries ℚ) = y := qExpand_injective N (hemb hf')
  rw [← hval]
  exact f.2

/-! ## The descent -/

/-- **Descent by one prime**: under `Hall M` and `p` prime, `j(q ^ M)` lies in
`ℚ(j(q), j(q ^ (M * p)))`.

The proof is the comparison of the two polynomials the two producers above describe: a
common root is a root of the level-`p` equation at the seed and a slot value of the
certificate, so the conjugate's slot index would have to divide `M` (it does not), and a
twist's slot index is `(M, 0)` with unit `1` (so the twist index vanishes). That is the
whole input, and `Hall M` is the whole hypothesis. -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hallM : Hall M) :
    jqN M ∈ modularFunctionField (M * p) := by
  obtain ⟨A, -, hA⟩ := exists_phiAtSeed_roots (M := M) (p := p)
  have hxA : A.eval₂ (nomeAlgebra (M * p)) (x₀ M p) = 0 :=
    (hA (x₀ M p)).mpr (Or.inr ⟨0, hp.out.pos, by
      simpa using iota_jqN (K := CyclotomicField (M * p) ℚ) (M * p) M⟩)
  obtain ⟨B, hBmonic, hBs, hBnd, hxB, hB⟩ :=
    exists_transported_minpoly (M := M) (p := p) hallM
  let : Algebra ↥(modularFunctionField (M * p)) (Lc M p) := (nomeAlgebra (M * p)).toAlgebra
  have huniq : ∀ y : Lc M p, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 →
      y = x₀ M p := by
    intro y hyA hyB
    obtain ⟨a, _, haM, b', hb', hyB⟩ := hB y hyB
    rcases (hA y).mp hyA with hyA | ⟨b, hb, hyA⟩
    · rw [hyA] at hyB
      exact absurd (TS_injective hyB).1 (slotLevel_ne_conjLevel haM)
    · rw [hyA] at hyB
      obtain ⟨he, hu⟩ := TS_injective hyB
      have hb0 : b = 0 :=
        eq_zero_of_pow_eq_one hb (by rw [hu, slotUnit_eq_one_of_twistLevel haM hb' he])
      subst b
      simpa [x₀, iota_jqN] using hyA
  exact mem_of_mem_range_nome (Polynomial.mem_range_of_unique_common_root B A hBmonic.ne_zero
    hBs hBnd (x₀ M p) hxB hxA fun y hyB hyA => huniq y hyA hyB)

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
