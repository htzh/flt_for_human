/-
  Layer JQ2 — `j(q ^ M)` lies in the level-`M * p` field.

  The node `ModularCurve.jqNModC_mem_modularFunctionFieldC_mul_prime`: for `F` the
  level-`M * p` field `K⟮j(q), j(q ^ (M * p))⟯`, show `j(q ^ M) ∈ F`. This is the
  `C`-layer twin of the prime step `jqNModC_mem_of_div_prime_of_mul_prime` (CL2),
  with the two-prime peeling replaced by "the `minpoly` slot product of CL1 plus
  the level-`p` slot", and it is the last member of the `C`-layer degree group.
  Its only consumer is `package_of_socket` (CL4), which takes it as `hKG1`.

  ## The mathematics

  Two polynomials over `F` vanish at the same point `x := qExpand K (M * p)
  (jqNModC K M)`:

  * `A := phiAtSeed data ⟨jqNModC K (M * p)⟩`, the modular relation at the
    level-`M * p` seed. Its roots are the `p + 1` slot values at slot `M * p`
    (the `p` finite conjugates `TS((M*p)*M, ζ₂ ^ c)`, `c < p`, and the cusp
    `TS(p*(p*(M*p*M)), 1)`), read off the ported `isRoot_prime_at_slot_iff`.
    `x` is the `c = 0` conjugate.
  * `B := m.map ι₀`, where `m := minpoly K⟮j(q)⟯ (jqNModC K M)`. The hypothesis
    `hprod` — the port's statement of the CL1 slot product — says the image of
    `B` in `LaurentSeries K` is the product over `a ∣ M`, `b < M / a`,
    `gcd (gcd a b) (M / a) = 1` of `X - qExpand K (a * a) (qTwist (ζ₁ ^ (b * a))
    (jqModC K))`. Hence every root of `B` is `TS(p*(a*a), ζ₁ ^ (b*a))`, and `x`
    is the root with `a = M`, `b = 0`.

  `TS_injective`, `2 ≤ p` and `omega` then kill every other common root: the cusp
  branch would need `p * (M * p * M) = a * a`, while `a ∣ M` gives
  `a * a ≤ M * M` and the left side is `p ^ 2 * M ^ 2`; the finite branch forces
  `a = M`, then `b = 0`, then `ζ₂ ^ c = 1` with `c < p` forces `c = 0`. So `x` is
  the *unique* common root, and `Polynomial.mem_range_of_unique_common_root` puts
  it in the range of `algebraMap F (LaurentSeries K)` — i.e. `j(q ^ M) ∈ F` after
  `qExpand_injective`.

  ## What is imported rather than restated

  The whole pin prelude (`TS` and its API, `qTwist`, `phiAtSeed` and its
  naturality/monicity, the at-slot roots API, `isPrimitiveRoot_pow_div`,
  `exists_phiIrreducible_evalSymm`, `mem_range_of_unique_common_root`, and the
  CL1 slot product `minpoly_jqNModC_map_eq_prod_slots`) is imported transitively
  from `FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProductAnyField`.
  This module contains no definition: its two declarations are the engine
  (`S_:358–505`, the only genuinely new proof in the pin file) and the headline.

  `prod_form_ne_zero` stays `private` in `PhiGenSplitsAnyField.lean` by design (its
  public home is the `ℚ`/`coeffEmb` spelling `PhiSlotRoots.prod_form_ne_zero`), and
  this module does not need it.

  ## Statement provenance

  The engine's statement is the pin's `S_` text verbatim; the headline is the
  `Theorems/` wrapper's binder block verbatim (the pin also states it as a
  `private` copy at `S_:514`, byte-identical to the wrapper — ported once, here).

  FLT `anthropics/fermats-last-theorem@aa2d8b3`.

  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean
  spec-pin: Theorems/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean
-/
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProductAnyField

-- The engine installs the `Algebra (modularFunctionFieldC K (M * p)) (LaurentSeries K)`
-- instance and a `NeZero a` instance inside the proof; both are consumed by
-- typeclass search, so the style linter's `let`/`have` preference does not apply.
-- Same local disable as `SlotProductAnyField.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

namespace ModularCurve

variable {K : Type*} [Field K]

/-- **The engine**: if the pushed minimal polynomial of `jqNModC K M` over
`K⟮j(q)⟯` is the CL1 slot product, then `jqNModC K M` lies in the level-`M * p`
field. Verbatim from
`P2M/Sol/S_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean:358`
(the `hprod` `if h : a = 0` guard is the pin's text; `a ∣ M` and `M ≠ 0` make it
dead, but the statement is diffed as text). -/
theorem jqNModC_mem_mffC_mul_prime_of_prod (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)]
    (ζ₁ : Kˣ) (ζ₂ : Kˣ) (hζ₂ : IsPrimitiveRoot (ζ₂ : K) p)
    (hprod : (minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M)).map
        ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩
            qExpand K (a * a) (qTwist (ζ₁ ^ (b * a)) (jqModC K))))) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) := by
  classical
  obtain ⟨data, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hM0 : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hp2 : 2 ≤ p := hp.out.two_le

  have hjNmem : jqNModC K (M * p) ∈ modularFunctionFieldC K (M * p) := jqNModC_mem K (M * p)
  have hle : IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)) ≤ modularFunctionFieldC K (M * p) :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqModC_mem K (M * p)))
  letI : Algebra (modularFunctionFieldC K (M * p)) (LaurentSeries K) :=
    ((qExpand K (M * p)).comp (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).toAlgebra

  set A : Polynomial (modularFunctionFieldC K (M * p)) :=
    phiAtSeed data (⟨jqNModC K (M * p), hjNmem⟩ : modularFunctionFieldC K (M * p)) with hA

  let ι₀ : (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) →+* modularFunctionFieldC K (M * p) :=
    { toFun := fun x => ⟨(x : LaurentSeries K), hle x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }

  set m : Polynomial (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :=
    minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M) with hm
  have hm0 : Polynomial.aeval (jqNModC K M) m = 0 := minpoly.aeval _ _
  set B : Polynomial (modularFunctionFieldC K (M * p)) := m.map ι₀ with hB

  have hmapA : A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))
      = phiAtSeed data (qExpand K (M * p) (jqNModC K (M * p))) :=
    phiAtSeed_map data _ _
  have hseed : qExpand K (M * p) (jqNModC K (M * p))
      = qExpand K (p * (M * p * M)) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) := by
    have h2 : TS K (M * p * (M * p)) 1 = TS K (p * (M * p * M)) ((1 : Kˣ) ^ p) := by
      rw [one_pow]
      exact TS_congr (by ring) 1
    exact (qExpand_jqNModC (M * p) (M * p)).trans h2
  have hdist : qExpand K (M * p) (jqNModC K M)
      = qExpand K (M * p * M) (qTwist (1 * ζ₂ ^ 0) (jqModC K)) := by
    rw [pow_zero, mul_one]
    exact qExpand_jqNModC (M * p) M

  have hrootA : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 ↔
      (y = qExpand K (p * (p * (M * p * M))) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K)) ∨
        ∃ c < p, y = qExpand K (M * p * M) (qTwist (1 * ζ₂ ^ c) (jqModC K))) := by
    intro y
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hmapA, hseed]
    exact isRoot_prime_at_slot_iff_of_isPrimitiveRoot p ζ₂ hζ₂ data (M * p * M) 1 y

  have hcomp : (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K)).comp ι₀
      = (qExpand K (M * p)).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K)) :=
    RingHom.ext fun _ => rfl

  have hbig : (qExpand K (M * p)).comp
        (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K))
      = (qExpand K p).comp ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (LaurentSeries K))) := by
    refine RingHom.ext fun x => ?_
    simp only [RingHom.comp_apply]
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm M p) _

  have hBroot : ∀ y : LaurentSeries K, Polynomial.aeval y B = 0 →
      ∃ a : ℕ, a ∣ M ∧ ∃ b : ℕ, b < M / a ∧ ∃ (_ : NeZero a), y = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
    intro y hy
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp, hbig, ← Polynomial.map_map,
      hprod] at hy
    simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Polynomial.eval_prod,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_filter,
      Finset.mem_range, Nat.mem_divisors, sub_eq_zero] at hy
    obtain ⟨a, ⟨haM, -⟩, b, ⟨hb, -⟩, hy⟩ := hy
    have ha0 : a ≠ 0 := fun h0 => NeZero.ne M (Nat.eq_zero_of_zero_dvd (h0 ▸ haM))
    haveI : NeZero a := ⟨ha0⟩
    refine ⟨a, haM, b, hb, inferInstance, ?_⟩
    rw [hy, dite_eq_right ha0]
    show qExpand K p (qExpand K (a * a) (qTwist (ζ₁ ^ (b * a)) (jqModC K)))
      = qExpand K (p * (a * a)) (qTwist (ζ₁ ^ (b * a)) (jqModC K))
    rw [qExpand_qExpand]

  have hA0 : A ≠ 0 := (phiAtSeed_monic data _).ne_zero
  have hAs : (A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).Splits := by
    rw [hmapA, hseed, phiAtSeed,
      PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p ζ₂ hζ₂ data (M * p * M) 1]
    exact (Polynomial.Splits.X_sub_C _).mul (Polynomial.Splits.prod fun b _ => Polynomial.Splits.X_sub_C _)
  have hAnd : (A.map (algebraMap (modularFunctionFieldC K (M * p)) (LaurentSeries K))).roots.Nodup := by
    rw [hmapA, hseed, phiAtSeed]
    exact roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot p ζ₂ hζ₂ data (M * p * M) 1

  have hxA : Polynomial.aeval (qExpand K (M * p) (jqNModC K M)) A = 0 :=
    (hrootA _).mpr (Or.inr ⟨0, hp.out.pos, hdist⟩)
  have hxB : Polynomial.aeval (qExpand K (M * p) (jqNModC K M)) B = 0 := by
    have hm0' := hm0
    rw [Polynomial.aeval_def] at hm0'
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, hB, Polynomial.map_map, hcomp, Polynomial.eval_map,
      ← Polynomial.hom_eval₂, hm0', map_zero]

  have huniq : ∀ y : LaurentSeries K, Polynomial.aeval y A = 0 → Polynomial.aeval y B = 0 →
      y = qExpand K (M * p) (jqNModC K M) := by
    intro y hyA hyB
    obtain ⟨a, haM, b, hb, ha, hy⟩ := hBroot y hyB
    have haM' : a ≤ M := Nat.le_of_dvd hM0 haM
    have h3 : a * a ≤ M * M := Nat.mul_le_mul haM' haM'
    have hMM : 0 < M * M := Nat.mul_pos hM0 hM0
    have h5 : M * p * M = p * (M * M) := by ring
    rcases (hrootA y).mp hyA with hy1 | ⟨c, hc, hy1⟩
    · exfalso
      have hTS : TS K (p * (p * (M * p * M))) ((1 : Kˣ) ^ (p * p)) = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
        rw [← hy]
        exact hy1.symm
      have he : p * (p * (M * p * M)) = p * (a * a) := (TS_injective hTS).1
      have h6 : p * (M * p * M) = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
      rw [h5] at h6
      have h7 : 2 * (2 * (M * M)) ≤ p * (p * (M * M)) := Nat.mul_le_mul hp2 (Nat.mul_le_mul hp2 le_rfl)
      omega
    · have hTS : TS K (M * p * M) (1 * ζ₂ ^ c) = TS K (p * (a * a)) (ζ₁ ^ (b * a)) := by
        rw [← hy]
        exact hy1.symm
      obtain ⟨he, hu⟩ := TS_injective hTS
      rw [h5] at he
      have h6 : M * M = a * a := Nat.eq_of_mul_eq_mul_left hp.out.pos he
      have haM2 : a = M := (Nat.mul_self_inj.mp h6).symm
      rw [haM2, Nat.div_self hM0] at hb
      have hb0 : b = 0 := Nat.lt_one_iff.mp hb
      rw [hb0, Nat.zero_mul, pow_zero, one_mul] at hu
      have hval : ((ζ₂ : Kˣ) : K) ^ c = 1 := by
        have h := congrArg Units.val hu
        rwa [Units.val_pow_eq_pow_val, Units.val_one] at h
      have hc0 : c = 0 := Nat.eq_zero_of_dvd_of_lt ((hζ₂.pow_eq_one_iff_dvd c).mp hval) hc
      rw [hc0] at hy1
      exact hy1.trans hdist.symm

  have hrange := Polynomial.mem_range_of_unique_common_root A B hA0 hAs hAnd _ hxA hxB huniq
  obtain ⟨f, hf⟩ := RingHom.mem_range.mp hrange
  have hf' : qExpand K (M * p) (f : LaurentSeries K) = qExpand K (M * p) (jqNModC K M) := hf
  have hval : (f : LaurentSeries K) = jqNModC K M := qExpand_injective (M * p) hf'
  rw [← hval]
  exact f.2

/-- **The headline**: `j(q ^ M)` is in the level-`M * p` field. Verbatim from
`Theorems/Thm_ModularCurve_jqNModC_mem_modularFunctionFieldC_mul_prime.lean:9`
(the `S_` file's `private` copy at `:514` is byte-identical; ported once). -/
theorem jqNModC_mem_modularFunctionFieldC_mul_prime {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (p : ℕ) [hp : Fact (Nat.Prime p)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    jqNModC K M ∈ modularFunctionFieldC K (M * p) :=
  jqNModC_mem_mffC_mul_prime_of_prod M p (ζ ^ (M * p / M)) (ζ ^ (M * p / p))
    (isPrimitiveRoot_pow_div hζ (dvd_mul_left p M))
    (minpoly_jqNModC_map_eq_prod_slots M (ζ ^ (M * p / M))
      (isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)) hall)

end ModularCurve
