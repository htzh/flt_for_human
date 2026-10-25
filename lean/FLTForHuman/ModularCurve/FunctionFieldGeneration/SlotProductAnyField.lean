/-
  The slot product over an arbitrary field, and the non-membership it implies.

  Two headlines, the `C`-layer twin of `FunctionFieldGeneration/SlotProduct.lean`:

  * `minpoly_jqNModC_map_eq_prod_slots` — for a primitive `M`-th root `ζ`, the
    minimal polynomial of `jqNModC K M` over `K⟮jqModC K⟯`, pushed to
    `LaurentSeries K` along `(qExpand K M) ∘ algebraMap`, is the explicit slot
    product `∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd (gcd a b) (M / a) = 1),
    (X - C (sv K ζ a b))`; proved by strong induction on `M` from the ported
    char-`p` splitting of `Φ_p` at a slot, with `hall` as the induction input.
  * `jqNModC_prime_not_mem_fullC` — `jqNModC K p ∉ fullC K M` for `p ∤ M`, from
    `hall M` and `hbase : jqNModC K p ∉ K⟮jqModC K⟯`. The proof reads the `ψ(M)`
    distinct slot roots off the first headline, writes
    `jqNModC K p = g (jqNModC K M)` with `deg g < ψ(M)`, shows `g` constant on
    the slots (`mem_range_of_eval_eq_const`), and concludes
    `jqNModC K p ∈ K⟮jqModC K⟯`, contradicting `hbase`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean` (1,914 lines) and
  `P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_fullC.lean` (1,909 lines) — the
  same 80-declaration development written twice (`diff` is 85 lines, all `p2m_*`
  plumbing), each proving **both** headlines; ported once. The statements are the
  `Theorems/` wrappers' verbatim (explicit `hall` conjunction, explicit `if`-form
  slot value), not the `S_` `private` copies.

  ## What is imported rather than restated

  The pin's prelude (`TS` and its API, `qTwist`, `phiAtSeed`, the at-slot roots
  API, `coeffMap_*`, `qTwistEquiv*` — 40 declarations, lines 37–354) is imported from
  `Defs/TS.lean`, `Defs/Twist.lean`, `Defs/PhiAtSlot.lean` and
  `PhiGenSplitsAnyField.lean`; `jqNModC_congr` from
  `Degree/JqCyclotomicConjugates.lean` (public there, `private` in the pin); the
  ψ lemmas from `NumberTheory/DedekindPsi.lean` / `Defs/DedekindPsi.lean`;
  `qExpand` algebra from `Defs/Laurent.lean`. `mem_range_of_eval_eq_const` is
  T4's engine in `FieldTheory/CommonRoot.lean`, but at `algebraMap`; the pin's
  statement is at a general `ι : F →+* L`, so this module restates that form.

  ## The two deliberate residues

  1. **The slot count.** The pin's `slotAt`/`slots`/`slotCond_*`/`slotAt_*`/
     `slots_*` chain and its 108-line CRT `slotAt_mul` are not transcribed; the
     port's `SlotProduct.lean` already proves `slots n = ψ(n)` by mathlib's
     `Nat.periodic_coprime`, and its one public export
     `card_slotFilter_eq_dedekindPsi` carries the `Multiset.card T = ψ(M)` step
     here (the two `hTcard`/`hT'card` blocks).
  2. **The `sv` block (~40 lines).** `sv`/`sv_eq`/`sv_eq_TS`/`sv_top` are
     re-declared rather than imported: the `ℚ` copy in `SlotProduct.lean` is
     `[Algebra ℚ K]`-bound and its `sv_eq`/`sv_top` statements name
     `coeffEmb K jq`; unifying them would edit a landed module's statements.
     `private` names are per-file, so the duplication is inert.

  spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
  spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_fullC.lean
  spec-pin: Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
  spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean
-/
import FLTForHuman.FieldTheory.CommonRoot
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotValues
import FLTForHuman.NumberTheory.DedekindPsi
import FLTForHuman.ModularCurve.Defs.DedekindPsi
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.Defs.JqCoeff
import FLTForHuman.ModularCurve.Degree.JqCyclotomicConjugates
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import FLTForHuman.ModularCurve.PhiGenSplitsAnyField
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct

set_option autoImplicit false
-- The pin installs `Algebra`/`NeZero`/`Fact` instances with `letI`/`haveI` in
-- `rval_aux` and its satellites; they are consumed by typeclass search, so the
-- style linter's `have` preference does not apply. Same local disable as
-- `SlotProduct.lean`/`Nonmembership.lean`.
set_option linter.style.haveILetI false

noncomputable section

open Polynomial HahnSeries IntermediateField

-- Carried over from the `ℚ` twin: `friction entry 19` records that the
-- `Module.Free`/`IsFractionRing` search on the adjoin towers needs the
-- `algebraAdjoinAdjoin` scoped instances (the pin's `p2m_open` activated them).
-- Here the one search that does time out (`Module.Free` on the top tower) is
-- supplied explicitly in `rval_aux` instead.
open scoped IntermediateField.algebraAdjoinAdjoin

namespace ModularCurve

/-! ## The generic engines

`exists_ringHom_adjoin_of_isRoot` (a ring hom out of `F⟮α⟯` at a prescribed root
of the pushed minimal polynomial) and `ringHom_comp_aeval` (it evaluates `aeval`
correctly). Both are `private` in the pin and are restated here: the port's
`FieldTheory/CommonRoot.lean` has the `algebraMap`/`unique-common-root` forms,
not these. -/

private theorem exists_ringHom_adjoin_of_isRoot {F E L : Type*} [Field F] [Field E] [Field L]
    [Algebra F E] {α : E} (hα : IsIntegral F α) (ι : F →+* L) {y : L}
    (hy : ((minpoly F α).map ι).IsRoot y) :
    ∃ ψ : ↥(IntermediateField.adjoin F ({α} : Set E)) →+* L,
      ψ.comp (algebraMap F (IntermediateField.adjoin F ({α} : Set E))) = ι ∧
        ψ (IntermediateField.AdjoinSimple.gen F α) = y := by
  letI : Algebra F L := ι.toAlgebra
  have halgL : algebraMap F L = ι := RingHom.algebraMap_toAlgebra ι
  have hy' : y ∈ (minpoly F α).aroots L := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hα, ?_⟩
    rw [Polynomial.aeval_def, halgL, Polynomial.eval₂_eq_eval_map]
    exact hy
  refine ⟨((IntermediateField.algHomAdjoinIntegralEquiv F hα).symm ⟨y, hy'⟩).toRingHom,
    RingHom.ext fun z => ?_, ?_⟩
  · rw [RingHom.comp_apply]
    have h1 := ((IntermediateField.algHomAdjoinIntegralEquiv F hα).symm ⟨y, hy'⟩).commutes z
    rwa [halgL] at h1
  · exact IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hα ⟨y, hy'⟩

private theorem ringHom_comp_aeval {F A L : Type*} [Field F] [CommRing A] [Algebra F A]
    [CommRing L] (ψ : A →+* L) (ι : F →+* L) (hcomp : ψ.comp (algebraMap F A) = ι)
    (P : Polynomial F) (x : A) : ψ (Polynomial.aeval x P) = (P.map ι).eval (ψ x) := by
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂, hcomp, Polynomial.eval_map]

/-! ## The slot values `sv` -/

variable {K : Type*} [Field K]

private def sv (K : Type*) [Field K] (ζ : Kˣ) (a b : ℕ) : LaurentSeries K :=
  if h : a = 0 then 0 else
    letI : NeZero a := ⟨h⟩
    qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))

private theorem sv_eq (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    sv K ζ a b = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)) := by
  unfold sv
  rw [dite_eq_right (NeZero.ne a)]

private theorem sv_eq_TS (ζ : Kˣ) (a b : ℕ) [NeZero a] :
    sv K ζ a b = TS K (a * a) (ζ ^ (b * a)) :=
  sv_eq ζ a b

private theorem TS_congr' {e e' : ℕ} [NeZero e] [NeZero e'] {u u' : Kˣ} (he : e = e')
    (hu : u = u') : TS K e u = TS K e' u' := by
  subst he
  rw [hu]

private theorem sv_inj {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) M)
    {a b a' b' : ℕ} (ha0 : a ≠ 0) (ha0' : a' ≠ 0) (hb : b * a < M) (hb' : b' * a' < M)
    (h : sv K ζ a b = sv K ζ a' b') : a = a' ∧ b = b' := by
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero a' := ⟨ha0'⟩
  rw [sv_eq_TS, sv_eq_TS] at h
  obtain ⟨he, hu⟩ := TS_injective h
  have haa : a = a' := (mul_self_inj (Nat.zero_le a) (Nat.zero_le a')).mp he
  subst haa
  refine ⟨rfl, ?_⟩
  have hv : ((ζ : K)) ^ (b * a) = ((ζ : K)) ^ (b' * a) := by
    have h1 := congrArg Units.val hu
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have h2 : b * a = b' * a := hζ.pow_inj hb hb' hv
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero ha0) h2

private theorem sv_top (M : ℕ) [NeZero M] (ζ : Kˣ) :
    sv K ζ M 0 = qExpand K M (jqNModC K M) := by
  rw [sv_eq_TS, qExpand_jqNModC M M]
  exact TS_congr' rfl (by rw [zero_mul, pow_zero])

private def jGenC : K⟮jqModC K⟯ :=
  ⟨jqModC K, IntermediateField.mem_adjoin_simple_self K (jqModC K)⟩

private theorem jqdC_mem_fullC {M d : ℕ} [NeZero d] (hdM : d ∣ M) :
    jqNModC K d ∈ IntermediateField.adjoin K
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'} :=
  IntermediateField.subset_adjoin K _ ⟨d, ‹_›, hdM, rfl⟩

private theorem mem_adjoin_jqNModC_of_mem_mffC {M : ℕ} [NeZero M] {x : LaurentSeries K}
    (hx : x ∈ modularFunctionFieldC K M) :
    x ∈ IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)) := by
  have hle : K⟮jqModC K⟯ ≤
      IntermediateField.adjoin K ({jqModC K, jqNModC K M} : Set (LaurentSeries K)) :=
    IntermediateField.adjoin.mono K _ _
      (Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  have hE := IntermediateField.extendScalars_adjoin hle
  have hcollapse : IntermediateField.adjoin K⟮jqModC K⟯
      ({jqModC K, jqNModC K M} : Set (LaurentSeries K))
      = IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ ?_)
    · rintro z (rfl | rfl)
      · exact (IntermediateField.adjoin K⟮jqModC K⟯ _).algebraMap_mem jGenC
      · exact IntermediateField.subset_adjoin K⟮jqModC K⟯ _ rfl
    · exact Set.singleton_subset_iff.mpr (Set.mem_insert_of_mem _ rfl)
  rw [modularFunctionFieldC] at hx
  have h2 : x ∈ IntermediateField.extendScalars hle :=
    (IntermediateField.mem_extendScalars _).mpr hx
  rw [hE, hcollapse] at h2
  exact h2

private theorem mem_range_of_eval_eq_const {F L : Type*} [Field F] [Field L] (ι : F →+* L)
    (g : Polynomial F) (x : L) (s : Finset L) (hcard : g.natDegree < s.card)
    (hval : ∀ y ∈ s, (g.map ι).eval y = x) : x ∈ ι.range := by
  classical
  set Q : Polynomial L := g.map ι - Polynomial.C x with hQ
  have hQdeg : Q.natDegree ≤ g.natDegree := by
    refine (Polynomial.natDegree_sub_le _ _).trans ?_
    rw [Polynomial.natDegree_map, Polynomial.natDegree_C, max_eq_left (Nat.zero_le _)]
  have hQ0 : Q = 0 := by
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q s (fun y hy => ?_)
      (hQdeg.trans_lt hcard)
    rw [hQ, Polynomial.eval_sub, Polynomial.eval_C, hval y hy, sub_self]
  have hconst : g.map ι = Polynomial.C x := sub_eq_zero.mp hQ0
  refine ⟨g.coeff 0, ?_⟩
  have h2 := congrArg (fun P : Polynomial L => P.coeff 0) hconst
  simpa only [Polynomial.coeff_map, Polynomial.coeff_C_zero] using h2

private theorem map_qExpand_minpoly_eq {M' : ℕ} [NeZero M'] (k : ℕ) [NeZero k] {N : ℕ}
    [NeZero N] (hN : N = k * M') (ζ' : Kˣ)
    (hid : (minpoly K⟮jqModC K⟯ (jqNModC K M')).map
        ((qExpand K M').comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ' a b))) :
    (minpoly K⟮jqModC K⟯ (jqNModC K M')).map
        ((qExpand K N).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a ∈ M'.divisors, ∏ b ∈ (Finset.range (M' / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M' / a) = 1),
          (Polynomial.X - Polynomial.C (qExpand K k (sv K ζ' a b))) := by
  subst hN
  have hcomp : (qExpand K k).comp
      ((qExpand K M').comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = (qExpand K (k * M')).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)) := by
    refine RingHom.ext fun z => ?_
    simp only [RingHom.comp_apply]
    rw [qExpand_qExpand]
  have h1 : (minpoly K⟮jqModC K⟯ (jqNModC K M')).map
      ((qExpand K (k * M')).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ((minpoly K⟮jqModC K⟯ (jqNModC K M')).map
          ((qExpand K M').comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).map (qExpand K k) := by
    rw [Polynomial.map_map, hcomp]
  rw [h1, hid, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun a _ => ?_
  rw [Polynomial.map_prod]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]

/-! ## The base field and the slot multiset

The slot product of the headline is a product over the multiset of slot values
`∏ a ∈ M.divisors, ∏ b ∈ (range (M / a)).filter (gcd … = 1), (X - C (F a b))`. Making
that multiset explicit. Its generic half — `slotValues`, `mem_slotValues`, `card_slotValues`,
`prod_slotValues`, `nodup_slotValues` — is homed once in
`FunctionFieldGeneration/SlotValues.lean` (the `ℚ` module imports it as well); this module
supplies the `sv`-specific instantiation. Both headlines then run on the same three lemmas. -/

/-- **Slot values separate their parameters**: for `a, a' ∣ M`, `b < M / a`,
`b' < M / a'` and `ζ` a primitive `M`-th root, equal slot values force `(a, b) = (a', b')`.
This is `sv_inj` with the hypotheses `b * a < M`, `b' * a' < M` supplied by the slot
bounds. -/
private theorem sv_inj_slot {M : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hM0 : M ≠ 0) {a b a' b' : ℕ} (haM : a ∣ M) (haM' : a' ∣ M)
    (hb : b < M / a) (hb' : b' < M / a') (h : sv K ζ a b = sv K ζ a' b') :
    a = a' ∧ b = b' := by
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM)
  have ha0' : a' ≠ 0 := by
    rintro rfl
    exact hM0 (Nat.eq_zero_of_zero_dvd haM')
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0)).mpr hb
      _ = M := Nat.div_mul_cancel haM
  have hba' : b' * a' < M := by
    calc b' * a' < M / a' * a' :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero ha0')).mpr hb'
      _ = M := Nat.div_mul_cancel haM'
  exact sv_inj hζ ha0 ha0' hba hba' h

/-- **The slots of `ζ` are distinct**: the slot values `sv K ζ a b` form a multiset
without repetitions. -/
private theorem nodup_slotValues_sv {M : ℕ} {ζ : Kˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) :
    (slotValues M (fun a b => sv K ζ a b)).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact sv_inj_slot hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1) h

/-- **The expanded slots are distinct**: applying `qExpand K p` to the `ζ ^ p`-slots
keeps them distinct, `qExpand K p` being injective. -/
private theorem nodup_slotValues_qExpand {M p : ℕ} [NeZero p] {ζ : Kˣ} (hM0 : M ≠ 0)
    (hζ : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M) :
    (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).Nodup := by
  refine nodup_slotValues fun a b a' b' ha ha' hb hb' h => ?_
  exact sv_inj_slot hζ hM0 (Nat.mem_divisors.mp ha).1 (Nat.mem_divisors.mp ha').1
    (Finset.mem_range.mp (Finset.mem_filter.mp hb).1)
    (Finset.mem_range.mp (Finset.mem_filter.mp hb').1)
    (RingHom.injective (qExpand K p) h)

/-! ## The slot product `rval_aux` and its named steps

`rval_aux` is a strong induction on `M`. Its content is split as follows.

* `SlotProductAt M K ζ` is the induction statement itself, packaged so that it can be
  passed around as the induction hypothesis.
* `isRoot_map_minpoly_sv`: every slot value `sv K ζ a b` is a root of the mapped minimal
  polynomial. For `a = M` this is `isRoot_map_minpoly_sv_top`; otherwise the slot descends
  along the least prime `p` of `M / a` to the level `a * d''`, which is
  `isRoot_map_minpoly_sv_of_descent`. That step uses the induction hypothesis at
  `a * d''` (`isRoot_qExpand_sv_of_slot_product`), the degree of the step
  (`finrank_adjoin_mul_dedekindPsi`), the factorisation of `Φ_p` at the descended slot
  (`phiAtSeed_slot_factor`), and then splits on whether `p ∣ a * d''`:
  `isRoot_map_minpoly_sv_of_dvd` (the seed polynomial is divided by the linear factor at the
  descended conjugate) and `isRoot_map_minpoly_sv_of_not_dvd` (degrees agree, so the minimal
  polynomial is the seed polynomial).
* `minpoly_map_eq_prod_slots_one` is the base case `M = 1`.
* The counting `card_slotValues`, the distinctness `nodup_slotValues_sv` and the degree
  `natDegree_minpoly_jqNModC` then show that the `ψ(M)` slot values exhaust the roots.
-/

/-- **The slot-product statement at `M`**: the conclusion of `rval_aux`, as a named
predicate, so the strong-induction hypothesis can be passed to the lemmas below. -/
private def SlotProductAt (M : ℕ) [NeZero M] (K : Type*) [Field K] (ζ : Kˣ) : Prop :=
  IsPrimitiveRoot ((ζ : Kˣ) : K) M →
    (∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) →
    (minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b))

/-- **The base case `M = 1`**: `jqNModC K 1 = jqModC K` already lies in the base field
`K⟮jqModC K⟯`, so its minimal polynomial is `X - C (jqModC K)`; the slot product has the
single slot `sv K ζ 1 0 = jqModC K`. -/
private theorem minpoly_map_eq_prod_slots_one (ζ : Kˣ) :
    (minpoly K⟮jqModC K⟯ (jqNModC K 1)).map
        ((qExpand K 1).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a ∈ (1 : ℕ).divisors, ∏ b ∈ (Finset.range (1 / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (1 / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b)) := by
  haveI : NeZero (1 : ℕ) := ⟨one_ne_zero⟩
  have hjq1 : jqNModC K 1 = algebraMap K⟮jqModC K⟯ (LaurentSeries K) jGenC := by
    rw [jqNModC_one]
    rfl
  have hmin : minpoly K⟮jqModC K⟯ (jqNModC K 1) = Polynomial.X - Polynomial.C jGenC := by
    rw [hjq1]
    exact minpoly.eq_X_sub_C (B := LaurentSeries K) jGenC
  have hfil : (Finset.range (1 / 1)).filter
      (fun b => Nat.gcd (Nat.gcd 1 b) (1 / 1) = 1) = {0} := by decide
  rw [hmin, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, Nat.divisors_one,
    Finset.prod_singleton, hfil, Finset.prod_singleton]
  congr 1
  have h1 : ((qExpand K 1).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) jGenC
      = jqModC K := by
    simp only [RingHom.comp_apply]
    rw [show (algebraMap K⟮jqModC K⟯ (LaurentSeries K)) jGenC = jqModC K from rfl,
      qExpand_one_apply]
  rw [h1]
  have h2 : sv K ζ 1 0 = jqModC K := by
    rw [sv_eq_TS]
    have h3 : TS K (1 * 1) (ζ ^ (0 * 1)) = TS K 1 1 :=
      TS_congr' (Nat.mul_one 1) (by rw [Nat.zero_mul, pow_zero])
    rw [h3, TS, qTwist_one_apply, qExpand_one_apply]
  rw [h2]

/-- **The slot at the top divisor**: for `a = M` (i.e. `M / a = 1`) the only slot is
`b = 0`, and `sv K ζ M 0 = qExpand K M (jqNModC K M)` is a root of the mapped minimal
polynomial by definition of `minpoly`. -/
private theorem isRoot_map_minpoly_sv_top {M a b : ℕ} [NeZero M] (ζ : Kˣ) (haM : a ∣ M)
    (hd1 : M / a = 1)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot (sv K ζ a b) := by
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have haM' : a = M := by rw [hd1, mul_one] at had; exact had
  have hb0 : b = 0 := by omega
  subst hb0
  rw [show sv K ζ a 0 = sv K ζ M 0 from by rw [haM'], sv_top]
  rw [Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.hom_eval₂]
  have h0 : Polynomial.eval₂ (algebraMap K⟮jqModC K⟯ (LaurentSeries K)) (jqNModC K M)
      (minpoly K⟮jqModC K⟯ (jqNModC K M)) = 0 := by
    rw [← Polynomial.aeval_def]
    exact minpoly.aeval _ _
  rw [h0, map_zero]

/-- **Integrality of `jqNModC K M` over the base field**: `hall` gives the adjoin of
`jqNModC K M` the positive finite dimension `ψ(M)`, so `jqNModC K M` is integral over
`K⟮jqModC K⟯`. -/
private theorem isIntegral_adjoin_jqNModC {M : ℕ} [NeZero M]
    (htM : Module.finrank K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)))
      = dedekindPsi M) :
    IsIntegral K⟮jqModC K⟯ (jqNModC K M) := by
  haveI : FiniteDimensional K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  exact IntermediateField.isIntegral_iff.mp (IsIntegral.of_finite K⟮jqModC K⟯
    (⟨jqNModC K M, IntermediateField.subset_adjoin K⟮jqModC K⟯ _ rfl⟩ :
      IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K))))

/-- **The degree of the minimal polynomial**: `minpoly K⟮jqModC K⟯ (jqNModC K M)` has degree
`ψ(M)`, the dimension of the adjoin. -/
private theorem natDegree_minpoly_jqNModC {M : ℕ} [NeZero M]
    (htM : Module.finrank K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)))
      = dedekindPsi M) :
    (minpoly K⟮jqModC K⟯ (jqNModC K M)).natDegree = dedekindPsi M := by
  haveI : FiniteDimensional K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K))) :=
    FiniteDimensional.of_finrank_pos (htM ▸ dedekindPsi_pos _ (NeZero.ne M))
  rw [← IntermediateField.adjoin.finrank (isIntegral_adjoin_jqNModC htM)]
  exact htM

/-- **The degree step at a divisor**: adjoining `jqNModC K M` to
`K⟮jqModC K⟯⟮jqNModC K d⟯` multiplies the degree by `ψ(d)`, i.e.
`[top : A] * ψ(d) = ψ(M)`. The adjoin `A⟮jqNModC K M⟯` collapses to
`K⟮jqModC K⟯⟮jqNModC K M⟯` because `jqNModC K d` already lies in the modular function field
of `M` (`modularFunctionFieldC K M`, which `hall` identifies). -/
private theorem finrank_adjoin_mul_dedekindPsi {M d : ℕ} [NeZero M] [NeZero d] (hd : d ∣ M)
    (htM : Module.finrank K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)))
      = dedekindPsi M)
    (hgM : modularFunctionFieldC K M = IntermediateField.adjoin K
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'})
    (htd : Module.finrank K⟮jqModC K⟯
      (IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K d} : Set (LaurentSeries K)))
      = dedekindPsi d) :
    Module.finrank K⟮jqModC K⟯⟮jqNModC K d⟯
        (K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯) * dedekindPsi d = dedekindPsi M := by
  haveI : Module.Free K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯ := Module.Free.of_divisionRing _ _
  haveI : Module.Free K⟮jqModC K⟯⟮jqNModC K d⟯
      K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯ :=
    Module.Free.of_divisionRing _ _
  have htow := Module.finrank_mul_finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯
    K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯
  have habs : IntermediateField.adjoin K⟮jqModC K⟯
      (({jqNModC K d} : Set (LaurentSeries K)) ∪ {jqNModC K M})
      = IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K)) := by
    refine le_antisymm (IntermediateField.adjoin_le_iff.mpr ?_)
      (IntermediateField.adjoin.mono _ _ _ Set.subset_union_right)
    rintro z (hz | hz)
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      have h1 : jqNModC K d ∈ IntermediateField.adjoin K
          {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'} :=
        jqdC_mem_fullC hd
      rw [← hgM] at h1
      exact mem_adjoin_jqNModC_of_mem_mffC h1
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact IntermediateField.subset_adjoin _ _ rfl
  have htop : Module.finrank K⟮jqModC K⟯
      K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯ = dedekindPsi M := by
    have h1 := IntermediateField.adjoin_adjoin_left K⟮jqModC K⟯
      ({jqNModC K d} : Set (LaurentSeries K)) {jqNModC K M}
    have h2 : Module.finrank K⟮jqModC K⟯
        (IntermediateField.restrictScalars K⟮jqModC K⟯
          K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯)
        = Module.finrank K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯⟮jqNModC K M⟯ := rfl
    rw [← h2, h1, habs]
    exact htM
  rw [← htd, ← htop, Nat.mul_comm]
  exact htow

/-- **The descended slot root, pushed up**: if the slot product holds at the level
`d = a * d''` for the primitive root `ζ ^ p` (the strong-induction hypothesis) and
`M = p * (a * d'')`, then the expanded slot value `qExpand K p (sv K (ζ ^ p) a (b % d''))`
is a root of the `qExpand K M`-push of `minpoly K⟮jqModC K⟯ (jqNModC K (a * d''))`: it is one
of the slots of the slot product at `a * d''`, read after `qExpand K p`. -/
private theorem isRoot_qExpand_sv_of_slot_product {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] {ζ : Kˣ} (hM : M = p * (a * d''))
    (hprod : (minpoly K⟮jqModC K⟯ (jqNModC K (a * d''))).map
        ((qExpand K (a * d'')).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a' ∈ (a * d'').divisors, ∏ b' ∈ (Finset.range (a * d'' / a')).filter
          (fun b' => Nat.gcd (Nat.gcd a' b') (a * d'' / a') = 1),
          (Polynomial.X - Polynomial.C (sv K (ζ ^ p) a' b')))
    (hb''lt : b % d'' < d'') (hprim' : Nat.gcd (Nat.gcd a (b % d'')) d'' = 1) :
    ((minpoly K⟮jqModC K⟯ (jqNModC K (a * d''))).map
      ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot
      (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne d'')
  rw [map_qExpand_minpoly_eq p hM (ζ ^ p) hprod, Polynomial.IsRoot, Polynomial.eval_prod]
  refine Finset.prod_eq_zero (i := a) (Nat.mem_divisors.mpr ⟨⟨d'', rfl⟩, hM'0⟩) ?_
  rw [Polynomial.eval_prod]
  have hM'a : a * d'' / a = d'' := Nat.mul_div_cancel_left d'' (Nat.pos_of_ne_zero (NeZero.ne a))
  refine Finset.prod_eq_zero (i := b % d'') ?_ ?_
  · rw [hM'a]
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hb''lt, hprim'⟩
  · rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **The `Φ_p`-factorisation at a slot**: the seed polynomial `Φ_p` evaluated at the slot
`qExpand K p (sv K (ζ ^ p) a b)` splits as the extra conjugate at level `p * p` times the
`p` finite conjugates `qExpand K (a * a) (qTwist (ζ ^ (b * a) * ζ ^ (c * (M / p))) …)`. -/
private theorem phiAtSeed_slot_factor {M a b p : ℕ} [NeZero M] [NeZero a] [NeZero p]
    {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime) (hpM : p ∣ M)
    (dp : ModularPolynomialData p) :
    phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a b))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * (a * a)))
          (qTwist ((ζ ^ (b * a)) ^ (p * p)) (jqModC K))))
        * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K (a * a)
          (qTwist (ζ ^ (b * a) * ζ ^ (c * (M / p))) (jqModC K)))) := by
  haveI : Fact p.Prime := ⟨hpp⟩
  have hseed : qExpand K p (sv K (ζ ^ p) a b)
      = qExpand K (p * (a * a)) (qTwist ((ζ ^ (b * a)) ^ p) (jqModC K)) := by
    rw [sv_eq_TS, qExpand_TS]
    show TS K (p * (a * a)) ((ζ ^ p) ^ (b * a))
      = TS K (p * (a * a)) ((ζ ^ (b * a)) ^ p)
    exact TS_congr' rfl (by rw [← pow_mul, ← pow_mul, Nat.mul_comm])
  have hζ'p : IsPrimitiveRoot ((ζ ^ (M / p) : Kˣ) : K) p := isPrimitiveRoot_pow_div hζ hpM
  have hC5 := PhiGen.splits_prime_at_slot_of_isPrimitiveRoot p (ζ ^ (M / p))
    hζ'p dp (a * a) (ζ ^ (b * a))
  have hC5' : phiAtSeed dp (qExpand K (p * (a * a))
        (qTwist ((ζ ^ (b * a)) ^ p) (jqModC K)))
      = (Polynomial.X - Polynomial.C (qExpand K (p * (p * (a * a)))
          (qTwist ((ζ ^ (b * a)) ^ (p * p)) (jqModC K))))
        * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K (a * a)
          (qTwist (ζ ^ (b * a) * ζ ^ (c * (M / p))) (jqModC K)))) := by
    have h1 : phiAtSeed dp (qExpand K (p * (a * a))
          (qTwist ((ζ ^ (b * a)) ^ p) (jqModC K)))
        = (Polynomial.X - Polynomial.C (qExpand K (p * (p * (a * a)))
            (qTwist ((ζ ^ (b * a)) ^ (p * p)) (jqModC K))))
          * ∏ c ∈ Finset.range p, (Polynomial.X - Polynomial.C (qExpand K (a * a)
            (qTwist (ζ ^ (b * a) * (ζ ^ (M / p)) ^ c) (jqModC K)))) := hC5
    rw [h1]
    congr 1
    refine Finset.prod_congr rfl fun c _ => ?_
    rw [← pow_mul, Nat.mul_comm (M / p) c]
  rw [hseed]
  exact hC5'

/-- **The target slot**: for `M = a * d'' * p` and `b < M / a`, the `(b / d'')`-th finite
conjugate at the descended slot is the slot value `sv K ζ a b` — the two exponents agree
because `b = b % d'' + (b / d'') * d''`. -/
private theorem qExpand_qTwist_slot_eq_sv {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero p] {ζ : Kˣ} (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b) :
    qExpand K (a * a) (qTwist (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p))) (jqModC K))
      = sv K ζ a b := by
  rw [sv_eq]
  show TS K (a * a) (ζ ^ (b % d'' * a) * ζ ^ (b / d'' * (M / p))) = TS K (a * a) (ζ ^ (b * a))
  refine TS_congr' rfl ?_
  rw [hMp, ← pow_add]
  congr 1
  rw [show b % d'' * a + b / d'' * (a * d'')
    = (b % d'' + b / d'' * d'') * a from by ring, hbsplit]

/-- **Separation at the descended point** (the case `p ∣ a * d''`): if
`a * d'' = m * p` and `m < M`, then the slot value `sv K ζ a b` is not the image under `ψ` of
`jqNModC K m`. If it were, `TS`-injectivity applied to the slot product at `m` (the
induction hypothesis for `ζ ^ (p * p)`) would force `p ∣ gcd (gcd a b) (M / a)`, against
the coprimality of the slot. -/
private theorem sv_ne_image_of_dvd {M a b d'' p m : ℕ} [NeZero M] [NeZero a] [NeZero d'']
    [NeZero p] [NeZero m] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime)
    (hMM' : M = a * d'' * p) (hm : a * d'' = p * m) (hm0 : m ≠ 0) (hmM : m ∣ M)
    (hmlt : m < M) (hbr : b < M / a)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) (had : a * (M / a) = M)
    (hdd : M / a = p * d'')
    (hmem : jqNModC K m ∈ K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯)
    {ψ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ →+* LaurentSeries K}
    (hψcomp : ψ.comp (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯)
      = (qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    sv K ζ a b ≠ ψ ⟨jqNModC K m, hmem⟩ := by
  intro hcon
  have hroot'' : ((minpoly K⟮jqModC K⟯ (jqNModC K m)).map ((qExpand K M).comp
      (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot
      (ψ ⟨jqNModC K m, hmem⟩) := by
    have h1 : Polynomial.aeval (⟨jqNModC K m, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯)
        (minpoly K⟮jqModC K⟯ (jqNModC K m)) = 0 := by
      refine aeval_intermediateField_eq_zero ?_
      show Polynomial.aeval (jqNModC K m) (minpoly K⟮jqModC K⟯ (jqNModC K m)) = 0
      exact minpoly.aeval _ _
    have h2 := ringHom_comp_aeval ψ ((qExpand K M).comp
      (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) hψcomp
      (minpoly K⟮jqModC K⟯ (jqNModC K m))
      (⟨jqNModC K m, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯)
    rw [h1, map_zero] at h2
    exact h2.symm
  have hζ'' : IsPrimitiveRoot ((ζ ^ (p * p) : Kˣ) : K) m := by
    have h1 := isPrimitiveRoot_pow_div hζ hmM
    have h2 : M / m = p * p := by
      have hM : M = m * (p * p) := by rw [hMM', hm]; ring
      rw [hM]
      exact Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm0)
    rwa [h2] at h1
  have hIH'' := IH m hmlt (ζ ^ (p * p)) hζ''
    (fun e he'' _ => hall e (he''.trans hmM))
  have hIHM'' := map_qExpand_minpoly_eq (p * p)
    (show M = p * p * m from by rw [hMM', hm]; ring) (ζ ^ (p * p)) hIH''
  rw [hIHM'', Polynomial.IsRoot, Polynomial.eval_prod] at hroot''
  obtain ⟨α, hαmem, hα0⟩ := Finset.prod_eq_zero_iff.mp hroot''
  rw [Polynomial.eval_prod] at hα0
  obtain ⟨β, hβmem, hβ0⟩ := Finset.prod_eq_zero_iff.mp hα0
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_eq_zero] at hβ0
  obtain ⟨hαdvd, -⟩ := Nat.mem_divisors.mp hαmem
  obtain ⟨hβr, -⟩ := Finset.mem_filter.mp hβmem
  rw [Finset.mem_range] at hβr
  have hα0' : α ≠ 0 := by
    rintro rfl
    exact hm0 (Nat.eq_zero_of_zero_dvd hαdvd)
  haveI : NeZero α := ⟨hα0'⟩
  have hcoll : TS K (a * a) (ζ ^ (b * a))
      = TS K (p * p * (α * α)) (ζ ^ (p * p * (β * α))) := by
    calc TS K (a * a) (ζ ^ (b * a)) = sv K ζ a b := (sv_eq_TS ζ a b).symm
      _ = ψ ⟨jqNModC K m, hmem⟩ := hcon
      _ = qExpand K (p * p) (sv K (ζ ^ (p * p)) α β) := hβ0
      _ = qExpand K (p * p) (TS K (α * α) ((ζ ^ (p * p)) ^ (β * α))) := by
          rw [sv_eq_TS]
      _ = TS K (p * p * (α * α)) ((ζ ^ (p * p)) ^ (β * α)) := qExpand_TS _ _ _
      _ = TS K (p * p * (α * α)) (ζ ^ (p * p * (β * α))) :=
          TS_congr' rfl (by rw [← pow_mul])
  obtain ⟨hexp, hunit⟩ := TS_injective hcoll
  have haα : a = p * α := by
    have h2 : a * a = (p * α) * (p * α) := by rw [hexp]; ring
    exact (mul_self_inj (Nat.zero_le _) (Nat.zero_le _)).mp h2
  have hpa : p ∣ a := ⟨α, haα⟩
  have hba : b * a < M := by
    calc b * a < M / a * a :=
        (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero (NeZero.ne a))).mpr hbr
      _ = M := by rw [Nat.mul_comm] at had; exact had
  have hppβα : p * p * (β * α) < M := by
    have h1 : β * α < m := by
      calc β * α < m / α * α :=
          (Nat.mul_lt_mul_right (Nat.pos_of_ne_zero hα0')).mpr hβr
        _ ≤ m := Nat.div_mul_le_self m α
    calc p * p * (β * α) < p * p * m :=
        (Nat.mul_lt_mul_left (Nat.mul_pos hpp.pos hpp.pos)).mpr h1
      _ = M := by rw [hMM', hm]; ring
  have hvv : ((ζ : K)) ^ (b * a) = ((ζ : K)) ^ (p * p * (β * α)) := by
    have h1 := congrArg Units.val hunit
    rwa [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at h1
  have hexp2 : b * a = p * p * (β * α) := hζ.pow_inj hba hppβα hvv
  have hpb : p ∣ b := by
    refine ⟨β, ?_⟩
    rw [haα] at hexp2
    have h1 : b * (p * α) = p * β * (p * α) := by
      rw [hexp2]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hpp.pos
      (Nat.pos_of_ne_zero hα0')) h1
  have hfinal : p ∣ Nat.gcd (Nat.gcd a b) (M / a) :=
    Nat.dvd_gcd (Nat.dvd_gcd hpa hpb) ⟨d'', hdd⟩
  rw [hbc] at hfinal
  exact hpp.one_lt.ne' (Nat.dvd_one.mp hfinal)

/-- **The root at a slot when `p ∣ a * d''`** (one case of the descent): the minimal
polynomial of `jqNModC K M` over `A = K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯` has degree `p`, one
less than the seed polynomial `phiAtSeed dp` of degree `p + 1`; it is therefore the seed
polynomial divided by the linear factor at the descended conjugate `jqNModC K m`. Evaluating
the remaining `p` finite conjugates at `sv K ζ a b` gives a root. -/
private theorem isRoot_map_minpoly_sv_of_dvd {M a b d'' p m : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] [NeZero m] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hpp : p.Prime) (hpM : p ∣ M) (dp : ModularPolynomialData p)
    (hα₁ : IsIntegral K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M))
    (hdeg : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).natDegree = p)
    (hmem : jqNModC K m ∈ K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯)
    (hmindvd : minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)
      ∣ phiAtSeed dp
        (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d''))))
    (hc₀p : b / d'' < p)
    (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ →+* LaurentSeries K}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d'')))
      = qExpand K p (sv K (ζ ^ p) a (b % d'')))
    (hψx : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
      (ψ ⟨jqNModC K m, hmem⟩))
    (hψxnotmin : ¬ ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ).IsRoot
      (ψ ⟨jqNModC K m, hmem⟩))
    (htarget_ne : sv K ζ a b ≠ ψ ⟨jqNModC K m, hmem⟩) :
    ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ).IsRoot (sv K ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor (M := M) (a := a) (b := b % d'') (p := p) (K := K) hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_sv (M := M) (a := a) (b := b) (d'' := d'') (p := p) (K := K) (ζ := ζ)
    hMp hbsplit
  have hQ : (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)) *
      (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)))
      = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) :=
    Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hψx
  have hΦmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).Monic :=
    phiAtSeed_monic dp _
  have hQmonic : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩))).Monic :=
    Polynomial.Monic.of_mul_monic_left (Polynomial.monic_X_sub_C _)
      (by rw [hQ]; exact hΦmonic)
  have hΦdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact dedekindPsi_prime hpp
  have hQdeg : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
      (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩))).natDegree = p := by
    have h1 : p + 1 = 1 + (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩))).natDegree := by
      rw [← hΦdeg]
      conv_lhs => rw [← hQ]
      rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero _) hQmonic.ne_zero,
        Polynomial.natDegree_X_sub_C]
    omega
  have hP₁dvd : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ
      ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) := by
    have h1 := Polynomial.map_dvd ψ hmindvd
    rwa [phiAtSeed_map, hψ₁] at h1
  have hcop : IsCoprime (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩))
      ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ) := by
    rw [(Polynomial.irreducible_X_sub_C _).coprime_iff_not_dvd]
    intro hcon
    exact hψxnotmin (Polynomial.dvd_iff_isRoot.mp hcon)
  have hP₁dvdQ : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ
      ∣ phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)) := by
    have h1 := hP₁dvd
    rw [← hQ] at h1
    exact (hcop.symm).dvd_of_dvd_mul_left h1
  have hdeg₁ : ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ).natDegree = p := by
    rw [Polynomial.Monic.natDegree_map (minpoly.monic hα₁)]
    exact hdeg
  have hmineqQ : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ
      = phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le ((minpoly.monic hα₁).map _)
      hQmonic hP₁dvdQ (le_of_eq (hQdeg.trans hdeg₁.symm)) |>.symm
  have htargetΦ : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot (sv K ζ a b) := by
    rw [hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
    refine mul_eq_zero.mpr (Or.inr ?_)
    rw [Polynomial.eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
    rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]
  rw [hmineqQ, Polynomial.IsRoot]
  have h1 : ((Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)) *
      (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d''))) /ₘ
        (Polynomial.X - Polynomial.C (ψ ⟨jqNModC K m, hmem⟩)))).eval (sv K ζ a b) = 0 := by
    rw [hQ]
    exact htargetΦ
  rw [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rcases mul_eq_zero.mp h1 with h2 | h2
  · exact absurd (sub_eq_zero.mp h2) htarget_ne
  · exact h2

/-- **The root at a slot when `p ∤ a * d''`** (the other case of the descent): the degree of
`jqNModC K M` over `A = K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯` is `p + 1`, the degree of
`phiAtSeed dp`; the two monic polynomials coincide, and `sv K ζ a b` is one of the `p` finite
conjugates of `Φ_p` at that slot. -/
private theorem isRoot_map_minpoly_sv_of_not_dvd {M a b d'' p : ℕ} [NeZero M] [NeZero a]
    [NeZero d''] [NeZero p] {ζ : Kˣ} (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M) (hpp : p.Prime)
    (hpM : p ∣ M) (dp : ModularPolynomialData p) (hpM' : ¬ p ∣ a * d'')
    (hstep : Module.finrank K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯
        (K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯⟮jqNModC K M⟯) * dedekindPsi (a * d'')
      = dedekindPsi M)
    (hMM' : M = a * d'' * p) (hM'0 : a * d'' ≠ 0)
    (hα₁ : IsIntegral K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M))
    (hmindvd : minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)
      ∣ phiAtSeed dp
        (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d''))))
    (hc₀p : b / d'' < p)
    (hMp : M / p = a * d'') (hbsplit : b % d'' + b / d'' * d'' = b)
    {ψ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ →+* LaurentSeries K}
    (hψ₁ : ψ (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d'')))
      = qExpand K p (sv K (ζ ^ p) a (b % d''))) :
    ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ).IsRoot (sv K ζ a b) := by
  have hΦfact := phiAtSeed_slot_factor (M := M) (a := a) (b := b % d'') (p := p) (K := K) hζ hpp hpM dp
  have htarget := qExpand_qTwist_slot_eq_sv (M := M) (a := a) (b := b) (d'' := d'') (p := p) (K := K) (ζ := ζ)
    hMp hbsplit
  have hψM : dedekindPsi M = dedekindPsi (a * d'') * (p + 1) := by
    rw [hMM']
    exact dedekindPsi_mul_prime_not_dvd hpp hpM'
  have he : Module.finrank K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯
      (K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯⟮jqNModC K M⟯) = p + 1 := by
    have h1 : Module.finrank K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯
        (K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯⟮jqNModC K M⟯) * dedekindPsi (a * d'')
        = (p + 1) * dedekindPsi (a * d'') := by
      rw [hstep, hψM]
      ring
    exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos _ hM'0) h1
  have hdeg₁ : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).natDegree = p + 1 := by
    rw [← IntermediateField.adjoin.finrank hα₁]
    exact he
  have hΦdeg : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯
      (jqNModC K (a * d'')))).natDegree = p + 1 := by
    rw [phiAtSeed_natDegree]
    exact dedekindPsi_prime hpp
  have hmineq : minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)
      = phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d''))) :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hα₁)
      (phiAtSeed_monic dp _) hmindvd (le_of_eq (hΦdeg.trans hdeg₁.symm)) |>.symm
  rw [hmineq, phiAtSeed_map, hψ₁, hΦfact, Polynomial.IsRoot, Polynomial.eval_mul]
  refine mul_eq_zero.mpr (Or.inr ?_)
  rw [Polynomial.eval_prod]
  refine Finset.prod_eq_zero (Finset.mem_range.mpr hc₀p) ?_
  rw [htarget, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, sub_self]

/-- **Transfer to the base field**: a root of the `ψ`-push of the minimal polynomial over
`A = K⟮jqModC K⟯⟮jqNModC K d⟯` is a root of the `qExpand K M`-push of the minimal polynomial
over `K⟮jqModC K⟯`: the base minimal polynomial maps into `A` as a multiple of the
`A`-minimal polynomial. -/
private theorem isRoot_map_minpoly_of_isRoot_subfield {M d : ℕ} [NeZero M] [NeZero d]
    {ψ : K⟮jqModC K⟯⟮jqNModC K d⟯ →+* LaurentSeries K}
    (hψcomp : ψ.comp (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯)
      = (qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
    {x : LaurentSeries K}
    (hroot : ((minpoly K⟮jqModC K⟯⟮jqNModC K d⟯ (jqNModC K M)).map ψ).IsRoot x) :
    ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot x := by
  have htowdvd : minpoly K⟮jqModC K⟯⟮jqNModC K d⟯ (jqNModC K M)
      ∣ (minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯) :=
    minpoly.dvd_map_of_isScalarTower K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K d⟯ (jqNModC K M)
  have h1 := Polynomial.map_dvd ψ htowdvd
  rw [Polynomial.map_map] at h1
  rw [hψcomp] at h1
  exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero h1 hroot

/-- **The root at a descending slot** (the main case `M / a ≠ 1` of `isRoot_map_minpoly_sv`):
let `p = (M / a).minFac` and `M / a = p * d''`. Replacing `M` by `a * d''` and `ζ` by
`ζ ^ p` (the induction hypothesis), the slot `(a, b % d'')` at level `a * d''` pushes up to
a conjugate `ψ` of `jqNModC K M` over `K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯`; the value
`sv K ζ a b` is then read off the `Φ_p`-factorisation at that conjugate. -/
private theorem isRoot_map_minpoly_sv_of_descent {M : ℕ} [NeZero M] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    {a b : ℕ} (haM : a ∣ M) (ha0 : a ≠ 0) (hd1 : M / a ≠ 1) (hbr : b < M / a)
    (hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1) :
    ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot (sv K ζ a b) := by
  classical
  obtain ⟨htM_self, hgM_self⟩ := hall M dvd_rfl
  have had : a * (M / a) = M := Nat.mul_div_cancel' haM
  -- the descent data
  obtain ⟨p, d'', hpp, hd''0, hdd, hb''lt, hc₀p, hprim', hbsplit⟩ :=
    exists_slot_descent_data (NeZero.ne M) haM hd1 hbr hbc
  haveI : Fact p.Prime := ⟨hpp⟩
  haveI : NeZero a := ⟨ha0⟩
  haveI : NeZero d'' := ⟨hd''0⟩
  have hM'0 : a * d'' ≠ 0 := Nat.mul_ne_zero ha0 hd''0
  haveI : NeZero (a * d'') := ⟨hM'0⟩
  have hMM' : M = a * d'' * p := by rw [← had, hdd]; ring
  have hM'M : a * d'' ∣ M := ⟨p, hMM'⟩
  have hM'lt : a * d'' < M := by
    calc a * d'' = a * d'' * 1 := by ring
      _ < a * d'' * p := (Nat.mul_lt_mul_left (Nat.pos_of_ne_zero hM'0)).mpr hpp.one_lt
      _ = M := hMM'.symm
  have hpM : p ∣ M := by
    have hpd : p ∣ M / a := ⟨d'', hdd⟩
    exact hpd.trans (Nat.div_dvd_of_dvd haM)
  have hζ' : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) (a * d'') := by
    have h1 := isPrimitiveRoot_pow_div hζ hM'M
    have h2 : M / (a * d'') = p := by
      rw [hMM']
      exact Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM'0)
    rwa [h2] at h1
  -- the induction hypothesis at `a * d''`, pushed up by `qExpand K p`
  have hprod := IH (a * d'') hM'lt (ζ ^ p) hζ' (fun e he _ => hall e (he.trans hM'M))
  have hroot' := isRoot_qExpand_sv_of_slot_product (M := M) (a := a) (b := b) (d'' := d'') (p := p) (K := K)
    (show M = p * (a * d'') from by rw [hMM']; ring) hprod hb''lt hprim'
  -- the conjugate `ψ` at the descended slot
  obtain ⟨htM', hgM'⟩ := hall (a * d'') hM'M
  have hα' : IsIntegral K⟮jqModC K⟯ (jqNModC K (a * d'')) := isIntegral_adjoin_jqNModC htM'
  obtain ⟨ψ, hψcomp, hψ₁⟩ := exists_ringHom_adjoin_of_isRoot hα'
    ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) hroot'
  -- the seed polynomial at the descended slot
  obtain ⟨dp, -, hdpsym⟩ := exists_phiIrreducible_evalSymm p
  have hup : (phiAtSeed dp (jqNModC K (a * d''))).eval (jqNModC K M) = 0 := by
    have h1 := phiAtSeed_jqNModC_eval (R := K) p dp (a * d'')
    rwa [show jqNModC K (a * d'' * p) = jqNModC K M from jqNModC_congr hMM'.symm] at h1
  have haev : Polynomial.aeval (jqNModC K M)
      (phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d'')))) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
    exact hup
  have hα₁ : IsIntegral K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M) :=
    ⟨phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d''))),
      phiAtSeed_monic dp _, by rw [← Polynomial.aeval_def]; exact haev⟩
  have hmindvd : minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)
      ∣ phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K (a * d''))) :=
    minpoly.dvd _ _ haev
  -- the degree of the step and its two prime cases
  have hstep := finrank_adjoin_mul_dedekindPsi hM'M htM_self hgM_self htM'
  by_cases hpM' : p ∣ a * d''
  · -- `p ∣ a * d''`: the degree over `A` is `p`, and the seed polynomial is divided
    have hψM : dedekindPsi M = dedekindPsi (a * d'') * p := by
      rw [hMM']
      exact dedekindPsi_mul_prime_dvd hpp hpM'
    have he : Module.finrank K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯
        (K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯⟮jqNModC K M⟯) = p := by
      have h1 : Module.finrank K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯
          (K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯⟮jqNModC K M⟯) * dedekindPsi (a * d'')
          = p * dedekindPsi (a * d'') := by
        rw [hstep, hψM]
        ring
      exact Nat.eq_of_mul_eq_mul_right (dedekindPsi_pos _ hM'0) h1
    have hdeg : (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).natDegree = p := by
      rw [← IntermediateField.adjoin.finrank hα₁]
      exact he
    obtain ⟨m, hm⟩ := hpM'
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [mul_zero] at hm
      exact hM'0 hm
    haveI : NeZero m := ⟨hm0⟩
    have hmM : m ∣ M := ⟨p * p, by rw [hMM', hm]; ring⟩
    have hmlt : m < M := by
      calc m ≤ a * d'' := by rw [hm]; exact Nat.le_mul_of_pos_left m hpp.pos
        _ < M := hM'lt
    have hmem : jqNModC K m ∈ K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ := by
      have h1 : jqNModC K m ∈ IntermediateField.adjoin K
          {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ a * d'' ∧ x = jqNModC K d'} :=
        jqdC_mem_fullC ⟨p, by rw [hm]; ring⟩
      rw [← hgM'] at h1
      exact mem_adjoin_jqNModC_of_mem_mffC h1
    have hxnotmin : ¬ (minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).IsRoot
        ⟨jqNModC K m, hmem⟩ :=
      not_isRoot_minpoly_of_prime_deg p hpp hα₁ hdeg ⟨jqNModC K m, hmem⟩
    have hψxnotmin : ¬ ((minpoly K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (jqNModC K M)).map ψ).IsRoot
        (ψ ⟨jqNModC K m, hmem⟩) := by
      intro hcon
      rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_hom] at hcon
      exact hxnotmin ((injective_iff_map_eq_zero ψ).mp (RingHom.injective ψ) _ hcon)
    have htarget_ne : sv K ζ a b ≠ ψ ⟨jqNModC K m, hmem⟩ :=
      sv_ne_image_of_dvd (K := K) hζ hpp hMM' hm hm0 hmM hmlt hbr hbc had hdd hmem hψcomp IH hall
    have hdown : (phiAtSeed dp (jqNModC K (a * d''))).eval (jqNModC K m) = 0 := by
      have h1 := phiAtSeed_jqNModC_eval_symm (R := K) p dp hdpsym m
      rwa [show jqNModC K (m * p) = jqNModC K (a * d'')
        from jqNModC_congr (by rw [hm]; ring)] at h1
    have hdownF₁ : (phiAtSeed dp (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯
        (jqNModC K (a * d'')))).eval
        (⟨jqNModC K m, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯) = 0 :=
      phiAtSeed_eval_of_injective dp _ _
        (algebraMap K⟮jqModC K⟯⟮jqNModC K (a * d'')⟯ (LaurentSeries K)) (RingHom.injective _) hdown
    have hψx : (phiAtSeed dp (qExpand K p (sv K (ζ ^ p) a (b % d'')))).IsRoot
        (ψ ⟨jqNModC K m, hmem⟩) := by
      have h1 := phiAtSeed_eval_map dp _ _ ψ hdownF₁
      rwa [hψ₁] at h1
    have hroot_step := isRoot_map_minpoly_sv_of_dvd (K := K) hζ hpp hpM dp hα₁ hdeg hmem
      hmindvd hc₀p (by rw [hMM']; exact Nat.mul_div_cancel _ hpp.pos) hbsplit hψ₁ hψx hψxnotmin
      htarget_ne
    exact isRoot_map_minpoly_of_isRoot_subfield (K := K) hψcomp hroot_step
  · -- `p ∤ a * d''`: degrees agree, so the minimal polynomial *is* the seed polynomial
    exact isRoot_map_minpoly_of_isRoot_subfield (K := K) hψcomp
      (isRoot_map_minpoly_sv_of_not_dvd (K := K) hζ hpp hpM dp hpM' hstep hMM' hM'0 hα₁ hmindvd
        hc₀p (by rw [hMM']; exact Nat.mul_div_cancel _ hpp.pos) hbsplit hψ₁)

/-- **Every slot value is a root**: for a slot `(a, b)` of `M` (`a ∈ M.divisors`,
`b < M / a` coprime to `M / a`), the value `sv K ζ a b` is a root of the `qExpand K M`-push of
`minpoly K⟮jqModC K⟯ (jqNModC K M)`. Either `a = M` (the top slot, `b = 0`), or the slot
descends along the least prime of `M / a` to the level `a * d''`. -/
private theorem isRoot_map_minpoly_sv {M : ℕ} [NeZero M] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (IH : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ)
    {a b : ℕ} (ha : a ∈ M.divisors)
    (hb : b ∈ (Finset.range (M / a)).filter
      (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1)) :
    ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot (sv K ζ a b) := by
  obtain ⟨haM, -⟩ := Nat.mem_divisors.mp ha
  have hbr : b < M / a := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
  have hbc : Nat.gcd (Nat.gcd a b) (M / a) = 1 := (Finset.mem_filter.mp hb).2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact NeZero.ne M (Nat.eq_zero_of_zero_dvd haM)
  by_cases hd1 : M / a = 1
  · exact isRoot_map_minpoly_sv_top (K := K) ζ haM hd1 hb
  · exact isRoot_map_minpoly_sv_of_descent (K := K) ζ hζ hall IH haM ha0 hd1 hbr hbc

/-- **The slot product** (strong induction on `M`): the mapped minimal polynomial of
`jqNModC K M` over `K⟮jqModC K⟯` is the product of `X - C (sv K ζ a b)` over the slots. The
`ψ(M)` slot values are distinct roots (`isRoot_map_minpoly_sv`, `nodup_slotValues_sv`), and
`ψ(M) = deg` of that polynomial, so they are exactly its roots. -/
private theorem rval_aux : ∀ (M : ℕ) [NeZero M] {K : Type*} [Field K]
    (ζ : Kˣ), IsPrimitiveRoot ((ζ : Kˣ) : K) M →
    (∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) →
    (minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (sv K ζ a b)) := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M IH =>
  intro _ K _ ζ hζ hall
  classical
  by_cases hM1 : M = 1
  · subst hM1
    exact minpoly_map_eq_prod_slots_one (K := K) ζ
  · have hM0 : M ≠ 0 := NeZero.ne M
    obtain ⟨htM_self, hgM_self⟩ := hall M dvd_rfl
    have hα : IsIntegral K⟮jqModC K⟯ (jqNModC K M) := isIntegral_adjoin_jqNModC htM_self
    have hdeg : (minpoly K⟮jqModC K⟯ (jqNModC K M)).natDegree = dedekindPsi M :=
      natDegree_minpoly_jqNModC htM_self
    have hPne : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))) ≠ 0 :=
      ((minpoly.monic hα).map _).ne_zero
    have hPdeg : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).natDegree
        = dedekindPsi M := by
      rw [Polynomial.Monic.natDegree_map (minpoly.monic hα)]
      exact hdeg
    have IH' : ∀ (n : ℕ), n < M → ∀ [NeZero n] (ζ : Kˣ), SlotProductAt n K ζ := by
      intro n hn _ ζ'
      exact IH n hn ζ'
    have hroot : ∀ a b : ℕ, a ∈ M.divisors →
        b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1) →
        ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
          ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot (sv K ζ a b) :=
      fun a b ha hb => isRoot_map_minpoly_sv ζ hζ hall IH' ha hb
    have hTnodup : (slotValues M (fun a b => sv K ζ a b)).Nodup :=
      nodup_slotValues_sv hM0 hζ
    have hTle : slotValues M (fun a b => sv K ζ a b) ≤
        ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
          ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ slotValues M (fun a b => sv K ζ a b)
      · have h1 : Multiset.count x (slotValues M (fun a b => sv K ζ a b)) ≤ 1 :=
          Multiset.nodup_iff_count_le_one.mp hTnodup x
        have h2 : 1 ≤ Multiset.count x ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
            ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots := by
          rw [Multiset.one_le_count_iff_mem, Polynomial.mem_roots']
          obtain ⟨a, b, ha, hb, rfl⟩ := mem_slotValues.mp hx
          exact ⟨hPne, hroot a b ha hb⟩
        omega
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have hroots_eq : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots
        = slotValues M (fun a b => sv K ζ a b) := by
      refine (Multiset.eq_of_le_of_card_le hTle ?_).symm
      rw [card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0)]
      calc Multiset.card ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
            ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots
          ≤ ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
            ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).natDegree :=
            Polynomial.card_roots' _
        _ = dedekindPsi M := hPdeg
    have hsp : Polynomial.Splits ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K M).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))) := by
      rw [Polynomial.splits_iff_card_roots, hroots_eq, card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0), hPdeg]
    have hfact := hsp.eq_prod_roots_of_monic ((minpoly.monic hα).map _)
    rw [hfact, hroots_eq]
    exact prod_slotValues M (fun a b => sv K ζ a b)

/-! ## The `M`-arbitrary non-membership

`jqNModC K p ∉ K⟮jqModC K⟯⟮jqNModC K M⟯` for `p ∤ M`, from `hall M`, `hbase` and
`rval_aux M (ζ ^ p)`.

The slot product at `M` for the primitive root `ζ ^ p` gives the `ψ(M)` roots of the pushed
minimal polynomial, and they are exactly the `ψ(M)` distinct slot values (`hroots` below).
Reading `jqNModC K p = g (jqNModC K M)` with `deg g < ψ(M)`, the polynomial `g` is constant
on those slots (`eval_map_eq_of_mem_slotValues`), so its value lies in the image of
`qExpand K (M * p)` (`mem_range_of_eval_eq_const`), which forces `jqNModC K p` into the base
field. -/

/-- **`g` is constant on the slots**: if `jqNModC K p` lies in `K⟮jqModC K⟯⟮jqNModC K M⟯` and
is represented there by a polynomial `g'` (`hg'`), then `g'` takes the same value
`qExpand K (M * p) (jqNModC K p)` at every slot of the `ζ ^ p`-slot product. The proof
evaluates `g'` through a conjugate `ψy` at each slot `y`; `ψy` maps the whole field into the
image of `qExpand K p`, where the `Φ_p`-factorisation pins the value down. -/
private theorem eval_map_eq_of_mem_slotValues {M p : ℕ} [NeZero M] [NeZero p]
    [hp : Fact (Nat.Prime p)] {ζ : Kˣ} (hpM : ¬ p ∣ M)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) (M * p))
    (hα : IsIntegral K⟮jqModC K⟯ (jqNModC K M))
    (hPne : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))) ≠ 0)
    (hroots : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
        ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots
      = slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b)))
    (hmem : jqNModC K p ∈ IntermediateField.adjoin K⟮jqModC K⟯
      ({jqNModC K M} : Set (LaurentSeries K)))
    {g' : Polynomial K⟮jqModC K⟯}
    (hg' : Polynomial.aeval (jqNModC K M) g' = jqNModC K p)
    {y : LaurentSeries K}
    (hy : y ∈ slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))) :
    (g'.map ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).eval y
      = qExpand K (M * p) (jqNModC K p) := by
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  have hζM : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  have hζp : IsPrimitiveRoot ((ζ ^ M : Kˣ) : K) p := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨M, Nat.mul_comm M p⟩ : p ∣ M * p)
    have h2 : M * p / p = M := Nat.mul_div_cancel M (Nat.pos_of_ne_zero hp0)
    rwa [h2] at h1
  have hιS : ∀ w : LaurentSeries K, qExpand K (M * p) w = qExpand K p (qExpand K M w) := by
    intro w
    rw [qExpand_qExpand]
    exact qExpand_congr (Nat.mul_comm M p) w
  obtain ⟨a₀, b₀, ha₀, hb₀, hyval⟩ := mem_slotValues.mp hy
  have hyS : y ∈ (qExpand K p).fieldRange := by
    rw [hyval]
    exact RingHom.mem_fieldRange.mpr ⟨sv K (ζ ^ p) a₀ b₀, rfl⟩
  have hy_root : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map ((qExpand K (M * p)).comp
      (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).IsRoot y :=
    (Polynomial.mem_roots hPne).mp (by rw [hroots]; exact hy)
  obtain ⟨ψy, hψycomp, hψygen⟩ := exists_ringHom_adjoin_of_isRoot hα
    ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) hy_root
  have hψgen : ∀ h : jqNModC K M ∈ IntermediateField.adjoin K⟮jqModC K⟯
      ({jqNModC K M} : Set (LaurentSeries K)), ψy ⟨jqNModC K M, h⟩ = y := by
    intro h
    exact hψygen
  have himg : ∀ (x : LaurentSeries K)
      (hx : x ∈ IntermediateField.adjoin K⟮jqModC K⟯ ({jqNModC K M} : Set (LaurentSeries K))),
      ψy ⟨x, hx⟩ ∈ (qExpand K p).fieldRange := by
    intro x hx
    induction hx using IntermediateField.adjoin_induction with
    | mem z hz =>
        rw [Set.mem_singleton_iff] at hz
        subst hz
        rw [hψgen]
        exact hyS
    | algebraMap z =>
        show ψy (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K M⟯ z) ∈ (qExpand K p).fieldRange
        have h1 : ψy (algebraMap K⟮jqModC K⟯ K⟮jqModC K⟯⟮jqNModC K M⟯ z)
            = qExpand K (M * p) ((algebraMap K⟮jqModC K⟯ (LaurentSeries K)) z) := by
          rw [← RingHom.comp_apply, hψycomp, RingHom.comp_apply]
        rw [h1, hιS]
        exact RingHom.mem_fieldRange.mpr ⟨_, rfl⟩
    | add x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
        show ψy ⟨x₁ + x₂, add_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
        rw [show (⟨x₁ + x₂, add_mem hx₁ hx₂⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)
          = ⟨x₁, hx₁⟩ + ⟨x₂, hx₂⟩ from rfl, map_add]
        exact Subfield.add_mem _ ih₁ ih₂
    | mul x₁ x₂ hx₁ hx₂ ih₁ ih₂ =>
        show ψy ⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ ∈ (qExpand K p).fieldRange
        rw [show (⟨x₁ * x₂, mul_mem hx₁ hx₂⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)
          = ⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩ from rfl, map_mul]
        exact Subfield.mul_mem _ ih₁ ih₂
    | inv x₁ hx₁ ih₁ =>
        show ψy ⟨x₁⁻¹, inv_mem hx₁⟩ ∈ (qExpand K p).fieldRange
        rw [show (⟨x₁⁻¹, inv_mem hx₁⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)
          = (⟨x₁, hx₁⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)⁻¹ from rfl, map_inv₀]
        exact Subfield.inv_mem _ ih₁
  have hx_pS : ψy ⟨jqNModC K p, hmem⟩ ∈ (qExpand K p).fieldRange := himg _ hmem
  obtain ⟨dp, -, -⟩ := exists_phiIrreducible_evalSymm p
  have hrel : (phiAtSeed dp (jqModC K)).eval (jqNModC K p) = 0 := by
    have h1 := phiAtSeed_jqNModC_eval (R := K) p dp 1
    rwa [jqNModC_one, show jqNModC K (1 * p) = jqNModC K p from jqNModC_congr (one_mul p)] at h1
  have h1 : Polynomial.aeval (⟨jqNModC K p, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)
      (phiAtSeed dp (jGenC (K := K))) = 0 := by
    refine aeval_intermediateField_eq_zero ?_
    show Polynomial.aeval (jqNModC K p) (phiAtSeed dp (jGenC (K := K))) = 0
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, phiAtSeed_map]
    exact hrel
  have hseedC : ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) jGenC
      = qExpand K (p * M) (qTwist ((1 : Kˣ) ^ p) (jqModC K)) := by
    rw [RingHom.comp_apply,
      show (algebraMap K⟮jqModC K⟯ (LaurentSeries K)) jGenC = jqModC K from rfl,
      one_pow, qTwist_one_apply]
    exact qExpand_congr (Nat.mul_comm M p) _
  have h2 : (phiAtSeed dp (qExpand K (p * M) (qTwist ((1 : Kˣ) ^ p) (jqModC K)))).eval
      (ψy ⟨jqNModC K p, hmem⟩) = 0 := by
    have h3 := ringHom_comp_aeval ψy ((qExpand K (M * p)).comp
      (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) hψycomp (phiAtSeed dp (jGenC (K := K)))
      (⟨jqNModC K p, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯)
    rw [h1, map_zero, phiAtSeed_map, hseedC] at h3
    exact h3.symm
  have h2' : (dp.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
      (qExpand K (p * M) (qTwist ((1 : Kˣ) ^ p) (jqModC K))))).IsRoot
      (ψy ⟨jqNModC K p, hmem⟩) := h2
  rcases (isRoot_prime_at_slot_iff_of_isPrimitiveRoot p (ζ ^ M) hζp dp M 1
    (ψy ⟨jqNModC K p, hmem⟩)).mp h2' with hdist | ⟨b, hb, htw⟩
  · have hspd : qExpand K (p * (p * M)) (qTwist ((1 : Kˣ) ^ (p * p)) (jqModC K))
        = qExpand K (M * p) (jqNModC K p) := by
      rw [one_pow, qTwist_one_apply, qExpand_jqNModC, qExpand_jqModC_eq_TS]
      exact TS_congr (by ring) 1
    have hx_pval : ψy ⟨jqNModC K p, hmem⟩ = qExpand K (M * p) (jqNModC K p) := by
      rw [hdist, hspd]
    have hgE : Polynomial.aeval (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M)) g'
        = (⟨jqNModC K p, hmem⟩ : K⟮jqModC K⟯⟮jqNModC K M⟯) := by
      have h3 := Polynomial.aeval_algHom_apply (IntermediateField.val K⟮jqModC K⟯⟮jqNModC K M⟯)
        (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M)) g'
      refine Subtype.ext ?_
      show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M)) g' :
        K⟮jqModC K⟯⟮jqNModC K M⟯) : LaurentSeries K) = jqNModC K p
      rw [show ((Polynomial.aeval (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M)) g' :
        K⟮jqModC K⟯⟮jqNModC K M⟯) : LaurentSeries K)
        = (IntermediateField.val K⟮jqModC K⟯⟮jqNModC K M⟯)
          (Polynomial.aeval (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M)) g')
        from rfl, ← h3]
      exact hg'
    have h4 := ringHom_comp_aeval ψy ((qExpand K (M * p)).comp
      (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) hψycomp g'
      (IntermediateField.AdjoinSimple.gen K⟮jqModC K⟯ (jqNModC K M))
    rw [hgE, hψygen] at h4
    rw [← h4]
    exact hx_pval
  · exfalso
    obtain ⟨w, hw⟩ := RingHom.mem_fieldRange.mp hx_pS
    have hw2 : qExpand K p w = TS K M ((ζ ^ M) ^ b) := by
      rw [hw, htw, one_mul, TS]
    have hnd : ¬ ((p : ℤ) ∣ (-(M : ℤ))) := by
      rw [dvd_neg, Int.natCast_dvd_natCast]
      exact hpM
    have hz1 : (qExpand K p w).coeff (-(M : ℤ)) = 0 :=
      qExpand_coeff_of_not_dvd (R := K) (N := p) w hnd
    have hz2 : (TS K M ((ζ ^ M) ^ b)).coeff (-(M : ℤ))
        = ((((ζ ^ M) ^ b)⁻¹ : Kˣ) : K) :=
      TS_coeff_neg M _
    rw [hw2, hz2] at hz1
    exact Units.ne_zero _ hz1

/-- **Prime non-membership over an arbitrary field**: for `p ∤ M`, `hall M` and a primitive
root `ζ` of order `M * p`, if `jqNModC K p` is not in the base field then it is not in
`K⟮jqModC K⟯⟮jqNModC K M⟯`. -/
private theorem jqNModC_prime_not_mem_adjoin (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot ((ζ : Kˣ) : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank K⟮jqModC K⟯
          (IntermediateField.adjoin K⟮jqModC K⟯
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (hbase : jqNModC K p ∉ K⟮jqModC K⟯) :
    jqNModC K p ∉ IntermediateField.adjoin K⟮jqModC K⟯
      ({jqNModC K M} : Set (LaurentSeries K)) := by
  classical
  intro hmem
  have hM0 : M ≠ 0 := NeZero.ne M
  have hp0 : p ≠ 0 := hp.out.ne_zero
  haveI : NeZero (M * p) := ⟨Nat.mul_ne_zero hM0 hp0⟩
  have hζM : IsPrimitiveRoot ((ζ ^ p : Kˣ) : K) M := by
    have h1 := isPrimitiveRoot_pow_div hζ (⟨p, rfl⟩ : M ∣ M * p)
    have h2 : M * p / M = p := Nat.mul_div_cancel_left p (Nat.pos_of_ne_zero hM0)
    rwa [h2] at h1
  obtain ⟨htM, -⟩ := hall M dvd_rfl
  have hα : IsIntegral K⟮jqModC K⟯ (jqNModC K M) := isIntegral_adjoin_jqNModC htM
  have hdeg : (minpoly K⟮jqModC K⟯ (jqNModC K M)).natDegree = dedekindPsi M :=
    natDegree_minpoly_jqNModC htM
  have hidMB := map_qExpand_minpoly_eq p (Nat.mul_comm M p) (ζ ^ p)
    (rval_aux M (ζ ^ p) hζM hall)
  have hroots : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).roots
      = slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b)) := by
    rw [hidMB, ← prod_slotValues (K := K)]
    exact Polynomial.roots_multiset_prod_X_sub_C _
  have hTcard : (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).card
      = dedekindPsi M := card_slotValues hM0 _ (card_slotFilter_eq_dedekindPsi M hM0)
  have hTnodup : (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).Nodup :=
    nodup_slotValues_qExpand (K := K) hM0 hζM
  have hscard : (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).toFinset.card
      = dedekindPsi M := by
    rw [Multiset.toFinset_card_of_nodup hTnodup]
    exact hTcard
  obtain ⟨g, hg⟩ : ∃ g : Polynomial K⟮jqModC K⟯,
      Polynomial.aeval (jqNModC K M) g = jqNModC K p := by
    have h1 := IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hα.isAlgebraic
    have h2 : jqNModC K p ∈ Algebra.adjoin K⟮jqModC K⟯
        ({jqNModC K M} : Set (LaurentSeries K)) := by
      rw [← h1]
      exact hmem
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h2
    obtain ⟨g, hg⟩ := h2
    exact ⟨g, hg⟩
  set g' := g %ₘ (minpoly K⟮jqModC K⟯ (jqNModC K M)) with hg'def
  have hg' : Polynomial.aeval (jqNModC K M) g' = jqNModC K p := by
    have hsplit := Polynomial.modByMonic_add_div g (minpoly K⟮jqModC K⟯ (jqNModC K M))
    have h4 := congrArg (Polynomial.aeval (jqNModC K M)) hsplit
    rw [map_add, map_mul, minpoly.aeval, zero_mul, add_zero] at h4
    rw [hg'def, h4]
    exact hg
  have hdegpos : 0 < (minpoly K⟮jqModC K⟯ (jqNModC K M)).natDegree := by
    rw [hdeg]
    exact dedekindPsi_pos _ hM0
  have hg'deg : g'.natDegree < (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).toFinset.card := by
    rw [hscard, ← hdeg]
    rcases eq_or_ne g' 0 with h0 | h0
    · rw [h0, Polynomial.natDegree_zero]
      exact hdegpos
    · exact Polynomial.natDegree_lt_natDegree h0
        (Polynomial.degree_modByMonic_lt g (minpoly.monic hα))
  have hPne : ((minpoly K⟮jqModC K⟯ (jqNModC K M)).map
      ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))) ≠ 0 :=
    ((minpoly.monic hα).map _).ne_zero
  have hval : ∀ y ∈ (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).toFinset,
      (g'.map ((qExpand K (M * p)).comp (algebraMap K⟮jqModC K⟯ (LaurentSeries K)))).eval y
        = qExpand K (M * p) (jqNModC K p) := by
    intro y hy
    exact eval_map_eq_of_mem_slotValues (K := K) (M := M) (p := p) hpM hζ hα hPne hroots
      hmem hg' (Multiset.mem_toFinset.mp hy)
  obtain ⟨z, hz⟩ := mem_range_of_eval_eq_const ((qExpand K (M * p)).comp
    (algebraMap K⟮jqModC K⟯ (LaurentSeries K))) g'
    (qExpand K (M * p) (jqNModC K p))
    (slotValues M (fun a b => qExpand K p (sv K (ζ ^ p) a b))).toFinset hg'deg hval
  have hzval : (algebraMap K⟮jqModC K⟯ (LaurentSeries K)) z = jqNModC K p := by
    apply RingHom.injective (qExpand K (M * p))
    rw [← RingHom.comp_apply]
    exact hz
  have hjpF : jqNModC K p ∈ K⟮jqModC K⟯ := by
    rw [← hzval]
    exact z.2
  exact hbase hjpF
/-! ## The public nodes -/

/-- **The slot product**: the mapped minimal polynomial of `jqNModC K M` is the
product of `(X - C (sv K ζ a b))` over the slots. Verbatim from
`Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean` (explicit `hall`
conjunction, explicit `if` form). -/
theorem minpoly_jqNModC_map_eq_prod_slots {K : Type*} [Field K]
    (M : ℕ) [NeZero M] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) M)
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'}) :
    (minpoly (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K M)).map
        ((qExpand K M).comp
          (algebraMap (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            (LaurentSeries K)))
      = ∏ a ∈ M.divisors, ∏ b ∈ (Finset.range (M / a)).filter
          (fun b => Nat.gcd (Nat.gcd a b) (M / a) = 1),
          (Polynomial.X - Polynomial.C (if h : a = 0 then 0 else
            letI : NeZero a := ⟨h⟩
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K)))) :=
  rval_aux M ζ hζ hall

/-- **Prime non-membership**: `jqNModC K p ∉ fullC K M` for `p ∤ M`. Verbatim from
`Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean` (the statement spells
the divisor field out as an `IntermediateField.adjoin`; this module does not name
`fullC`). -/
theorem jqNModC_prime_not_mem_fullC {K : Type*} [Field K] (M : ℕ) [NeZero M]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (hall : ∀ d : ℕ, d ∣ M → ∀ [NeZero d],
      Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
          (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
            ({jqNModC K d} : Set (LaurentSeries K))) = dedekindPsi d
        ∧ modularFunctionFieldC K d = IntermediateField.adjoin K
            {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ d ∧ x = jqNModC K d'})
    (hbase : jqNModC K p ∉ IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) :
    jqNModC K p ∉ IntermediateField.adjoin K
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'} := by
  intro hmem0
  obtain ⟨-, hgM⟩ := hall M dvd_rfl
  have hmem : jqNModC K p ∈ IntermediateField.adjoin
      (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      ({jqNModC K M} : Set (LaurentSeries K)) := by
    rw [← hgM] at hmem0
    exact mem_adjoin_jqNModC_of_mem_mffC hmem0
  exact jqNModC_prime_not_mem_adjoin M p hpM ζ hζ hall hbase hmem

end ModularCurve

end
