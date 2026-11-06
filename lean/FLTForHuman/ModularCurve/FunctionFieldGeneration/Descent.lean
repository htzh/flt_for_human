/-
  The descent by one prime, with its slot hypotheses discharged, and the one-prime
  reduction of `Gen`.

  `jqN_div_mem_modularFunctionField` is the descent of math/010 §4: under `Hall M`,
  `j(q ^ M)` lies in `ℚ(j(q), j(q ^ (M * p)))`. Its engine is the unique-common-root
  argument on the level-`p` modular equation and the pushed minimal polynomial of
  `j(q ^ M)`; the two root conditions that argument needs are *derived* here, from
  T19's slot product (`minpoly_jqN_map_eq_prod_slots`) plus `Hall M`, at the root of
  unity `cycUnit (M * p)`. So the statement names no splitting field, no root of unity
  and no root predicate: a caller supplies `Hall M` and nothing else. The engine, which
  does name them, has no statement of its own: its proof is the body of that theorem,
  after four lines that fix the certificate. Nothing in the port exposes it.

  The layers, in dependency order:

  * the pushed minimal polynomial `pushedMinpoly` and the nome map it is read through,
    private here because only the certificate uses them;
  * `root_shape`: every root of `pushedMinpoly K M (M * p)` is a slot value
    `j(ζ ^ (b * a) q ^ (a * a))` with `a ∣ M`, `b < M / a` (the slot list of the
    level-`M` minimal polynomial, read at the level-`M * p` nome);
  * `htw_of` / `hsp_of`: the two root conditions, by index arithmetic on that shape and
    `TS_injective`;
  * `jqN_div_mem_modularFunctionField`: the descent — its certificate, its engine, and
    a statement over `ℚ` only.

  Its second subject is the one-prime reduction of `Gen`, in the same `Hall` form:
  `modularFunctionField_eq_full_of` takes the strong induction hypothesis itself
  (`∀ m < N, m ≠ 0 → Hall m`) and derives what it consumes — the level `m < N` that a
  proper divisor `d` divides with `N = m * p`, `Hall m`, `jqN m ∈ F_N` from the descent
  above, and `Gen m` from `Hall m`. The pin instead passes two facts per factorization;
  the caller passes `ih` unchanged.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  * `P2M/Sol/S_ModularCurve_modularFunctionField_eq_full_of.lean` lines 553–690 — the
    descent, `private` in the pin and stated with `ζ`, `hζ` and the two root conditions.
    That text is the body of the descent here, at `ζ = cycUnit (M * p)`; the pin's
    hypotheses are discharged in its first four lines and the statement takes `Hall M`;
  * the same file, lines 694–727 — the one-prime reduction, whose two hypothesis
    applications (`hstep`, `hgen'`) become the derivation of what they carry;
  * `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean` lines 541–613 — `root_shape`,
    `htw_of` and `hsp_of`, `private` in the pin and consumed only by the pin's
    `hall_all`. They live here because this is the layer where T15 and T19 meet: the
    discharge needs T19's slot product, and the descent does not (the pin proves it
    without).

  ## Verification tier

  No `spec-pin:` header, deliberately: the public statements are the port's own. The
  descent's engine is the pin's text with its hypotheses folded into the statement, and
  the reduction's text was retired to the `Hall` form, so a wire would diff nothing.
  Registered by `spec/unwired_register.py`.

  If a future public declaration in this module transcribes a pin statement, it needs a
  `spec-pin:` line, and this note is then wrong.

  ## Assumptions

  T4's `Polynomial.mem_range_of_unique_common_root`; T12's
  `exists_phiIrreducible_evalSymm`; T13's `splits_prime_at_slot`; T14's
  `phiAtSeed`/`phiAtSeed_map`/`phiAtSeed_monic`, `isRoot_prime_at_slot_iff`,
  `roots_prime_at_slot_roots_nodup`, `iota_jqN`, `TS_congr`; `Defs/Laurent`'s
  `coeffMap_injective` and `qExpand_injective`; `Defs/PhiAtSlot`'s `pushedMinpoly`,
  `Defs/TS`'s `TS` and `TS_injective`, `Defs/Cyclotomic`'s `cycUnit`,
  `Defs/Fields`'s `modularFunctionField`, `adjoin_jq_le` and `jqd_mem_full`; T19's
  `minpoly_jqN_map_eq_prod_slots`; `NumberTheory/DedekindPsi`'s `lt_of_mul_prime_eq`.
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
import FLTForHuman.ModularCurve.PhiGenSplits
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct

set_option autoImplicit false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type} [Field K] [Algebra ℚ K]

/-! ## The pushed minimal polynomial, private to this module

The two names the descent's engine is stated in. Both are spellings of expressions the pin
writes inline at every use: `nomeMap K N` is the composite `coeffEmb K ∘ qExpand ℚ N ∘
(ℚ⟮jq⟯ ↪ ℚ((q)))`, which *reads a function of `ℚ(j(q))` at the level-`N` nome*, and
`pushedMinpoly K M N` is the minimal polynomial of `j(q ^ M)` read through it. They are
private here because the public statement below names neither: the certificate stays inside
the module, and nothing outside reads these terms. -/

/-- Read a function of `ℚ(j(q))` at the level-`N` nome `q ↦ q ^ N`, with coefficients
extended to `K`. -/
private def nomeMap (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    ℚ⟮jq⟯ →+* LaurentSeries K :=
  ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

/-- The minimal polynomial of `j(q ^ M)` over `ℚ(j(q))`, pushed to the level-`N` nome: the
polynomial whose roots the descent compares with those of the level-`p` modular equation. -/
private def pushedMinpoly (K : Type*) [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M] (N : ℕ) [NeZero N] :
    Polynomial (LaurentSeries K) :=
  (minpoly ℚ⟮jq⟯ (jqN M)).map (nomeMap K N)

/-- Reading at the level `M` and then at the level `e` is reading at the level `M * e`. -/
private theorem nomeMap_qExpand (K : Type*) [Field K] [Algebra ℚ K] (M e : ℕ) [NeZero M] [NeZero e] :
    (qExpand K e).comp (nomeMap K M) = nomeMap K (M * e) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply, nomeMap]
  rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
  exact qExpand_congr (mul_comm e M) _

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

/-! ## The descent -/



/-- **Descent by one prime**: under `Hall M` and `p` prime, `j(q ^ M)` lies in
`ℚ(j(q), j(q ^ (M * p)))`.

The unique-common-root argument it runs needs two conditions on the roots of the
pushed minimal polynomial of `j(q ^ M)` read at the level-`M * p` nome; `htw_of` and
`hsp_of` derive both from T19's slot product at the root of unity `cycUnit (M * p) ^
((M * p) / M)`. That is why the statement names neither a splitting field nor a root
predicate: `Hall M` is the whole input, and the certificate stays inside. -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hallM : Hall M) :
    jqN M ∈ modularFunctionField (M * p) := by
  set K := CyclotomicField (M * p) ℚ
  set ζ : Kˣ := cycUnit (M * p)
  have hζ : IsPrimitiveRoot (ζ : K) (M * p) :=
    cycUnit_spec (M * p)
  have hζM : IsPrimitiveRoot ((ζ ^ ((M * p) / M) : Kˣ) : K) M :=
    isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)
  have htw : ∀ w : Kˣ, (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * M) w) → w = 1 :=
    htw_of M p (ζ ^ ((M * p) / M)) hζM hallM
  have hsp : ¬ (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * (M * p * p)) 1) :=
    hsp_of M p (ζ ^ ((M * p) / M)) hζM hallM
  classical
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hpN : p ∣ M * p := dvd_mul_left p M

  set F := modularFunctionField (M * p) with hF
  have hjNmem : jqN (M * p) ∈ F :=
    IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)
  have hle : IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)) ≤ F :=
    adjoin_jq_le (M * p)
  let : Algebra F (LaurentSeries K) :=
    (((coeffEmb K).comp (qExpand ℚ (M * p))).comp (algebraMap F (LaurentSeries ℚ))).toAlgebra

  set A : Polynomial F := phiAtSeed data (⟨jqN (M * p), hjNmem⟩ : F) with hA

  let ι₀ : (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* F :=
    { toFun := fun x => ⟨(x : LaurentSeries ℚ), hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  set B : Polynomial F :=
    (minpoly (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)).map ι₀
    with hB

  have hmapA : A.map (algebraMap F (LaurentSeries K))
      = phiAtSeed data (coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))) :=
    phiAtSeed_map data _ _
  have hseed : coeffEmb K (qExpand ℚ (M * p) (jqN (M * p)))
      = qExpand K (p * (M * p * M)) (qTwist ((1 : Kˣ) ^ p) (coeffEmb K jq)) := by
    rw [coeffEmb_jq]
    have h2 : TS K ((M * p) * (M * p)) 1 = TS K (p * (M * p * M)) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (iota_jqN (M * p) (M * p)).trans h2
  have hdist : coeffEmb K (qExpand ℚ (M * p) (jqN M))
      = qExpand K (M * p * M) (qTwist (1 * ζ ^ (0 * (M * p / p))) (coeffEmb K jq)) := by
    rw [coeffEmb_jq]
    have h2 : TS K ((M * p) * M) 1 = TS K (M * p * M) (1 * ζ ^ (0 * (M * p / p))) := by
      rw [Nat.zero_mul, pow_zero, mul_one]
    exact (iota_jqN (M * p) M).trans h2
  have hspread : coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))
      = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) := by
    rw [coeffEmb_jq]
    have h2 : TS K ((M * p) * (M * p * p)) 1
        = TS K (p * (p * (M * p * M))) ((1 : Kˣ) ^ (p * p)) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (iota_jqN (M * p) (M * p * p)).trans h2

  have hrootA : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 ↔
        (y = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (coeffEmb K jq)) ∨
          ∃ b < p, y = qExpand K (M * p * M)
            (qTwist (1 * ζ ^ (b * (M * p / p))) (coeffEmb K jq))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hseed]
    exact isRoot_prime_at_slot_iff (M * p) ζ hζ p hpN data (M * p * M) 1 y

  have hcomp : (algebraMap F (LaurentSeries K)).comp ι₀
      = ((coeffEmb K).comp (qExpand ℚ (M * p))).comp
          (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
            (LaurentSeries ℚ)) := RingHom.ext fun x => rfl

  have hBev : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      (pushedMinpoly K M (M * p)).IsRoot y := by
    intro y hy
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map] at hy
    rw [hcomp] at hy
    exact hy

  have hA0 : A ≠ 0 := (phiAtSeed_monic data _).ne_zero
  have hAs : (A.map (algebraMap F (LaurentSeries K))).Splits := by
    rw [hmapA, hseed, phiAtSeed,
      PhiGen.splits_prime_at_slot (M * p) ζ hζ p hpN data (M * p * M) 1]
    exact (Polynomial.Splits.X_sub_C _).mul
      (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hAnd : (A.map (algebraMap F (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hseed, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup (M * p) ζ hζ p hpN data (M * p * M) 1

  set x₀ : LaurentSeries K := coeffEmb K (qExpand ℚ (M * p) (jqN M)) with hx₀
  have hxA : Polynomial.aeval x₀ A = 0 :=
    (hrootA x₀).mpr (Or.inr ⟨0, hp.out.pos, hdist⟩)
  have hxB : Polynomial.aeval x₀ B = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp,
      ← Polynomial.map_map, Polynomial.eval_map]
    have hx₀ψ : x₀ = ((coeffEmb K).comp (qExpand ℚ (M * p))) (jqN M) := rfl
    rw [hx₀ψ, Polynomial.eval₂_hom]
    have hmp := minpoly.aeval
      (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (jqN M)
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at hmp
    rw [hmp, map_zero]

  have huniq : ∀ y : LaurentSeries K,
      Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 → y = x₀ := by
    intro y hyA hyB
    rcases (hrootA y).mp hyA with hy1 | ⟨b, hb, hy1⟩
    · -- the extra conjugate of the level-`p` equation is a root of `B`: excluded outright
      have hTS : y = TS K ((M * p) * (M * p * p)) 1 := by
        rw [← iota_jqN]
        exact hy1.trans hspread.symm
      exact (hsp (hTS ▸ hBev y hyB)).elim
    · -- a twisted root at nome-level `(M * p) * M`: `htw` forces the unit to be `1`
      have hB := hBev y hyB
      rw [hy1, coeffEmb_jq] at hB
      have hw := htw (1 * ζ ^ (b * (M * p / p))) hB
      rw [one_mul] at hw
      have hb0 : b = 0 := by
        have hord : (M * p) ∣ b * M := by
          have hval : (ζ : K) ^ (b * (M * p / p)) = 1 := by
            have := congrArg Units.val hw
            simpa using this
          rw [Nat.mul_div_cancel M hp.out.pos] at hval
          exact (hζ.pow_eq_one_iff_dvd _).mp hval
        have hpb : p ∣ b := by
          have h2 : M * p ∣ M * b := by rwa [Nat.mul_comm b M] at hord
          exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero (NeZero.ne M))).mp h2
        exact Nat.eq_zero_of_dvd_of_lt hpb hb
      rw [hb0] at hy1
      exact hy1.trans hdist.symm

  have hrange := Polynomial.mem_range_of_unique_common_root A B hA0 hAs hAnd x₀ hxA hxB huniq
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
  have hf' : coeffEmb K (qExpand ℚ (M * p) ((f : LaurentSeries ℚ)))
      = coeffEmb K (qExpand ℚ (M * p) (jqN M)) := hf
  have hemb : Function.Injective (coeffEmb K) :=
    coeffMap_injective ((algebraMap ℚ K).injective)
  have hval : (f : LaurentSeries ℚ) = jqN M := qExpand_injective (M * p) (hemb hf')
  rw [← hval]
  exact f.2
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
