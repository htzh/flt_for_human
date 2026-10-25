# WORKORDER-CL1 — the slot product over an arbitrary field, and the non-membership it implies

Status: **open, ready for dispatch** (2026-10-25). Manager: nothing to land first — every
premise of §2 is already homed and statement-checked. Worker: the two headlines in §3.2 with the
engine in §3.1.

Two D-S nodes, one module, one `S_` development written twice in the pin:

| node | pin wrapper | pin `S_` | raw lines | citers | frontier |
|---|---|---|---:|---:|---|
| `ModularCurve.minpoly_jqNModC_map_eq_prod_slots` | `Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean` | `P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean` | 1,914 | 6 | needed 1 |
| `ModularCurve.jqNModC_prime_not_mem_fullC` | `Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean` | `P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_fullC.lean` | 1,909 | 1 | needed 1 |

`needed 1` means **every premise is already ported**: this is a transcription, not a re-derivation.
Pinned at `anthropics/fermats-last-theorem@aa2d8b3`.

The two `S_` files declare the same 80 declarations; `diff` is 85 lines, all `p2m_*` namespace
plumbing plus the final `solution` tail. Each file proves **both** headlines. Port once.

## 1. What the mathematics is

Both headlines are about the field `K⟮jqModC K⟯ = IntermediateField.adjoin K {jqModC K}` inside
`LaurentSeries K`, at a primitive `M`-th root `ζ`, under the hypothesis (`hall`) that for every
`d ∣ M` the degree of `K⟮jqModC K⟯⟮jqNModC K d⟯` is `ψ(d)` and the two-generator field
`modularFunctionFieldC K d` is the full divisor field.

1. **`minpoly_jqNModC_map_eq_prod_slots`** — the minimal polynomial of `jqNModC K M` over
   `K⟮jqModC K⟯`, pushed to `LaurentSeries K` along `qExpand K M`, is the explicit slot product
   over `a ∈ M.divisors`, `b < M / a` coprime to `M / a`, of `X - C (sv K ζ a b)`, where
   `sv K ζ a b = qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))`.
2. **`jqNModC_prime_not_mem_fullC`** — for `p ∤ M`, `jqNModC K p` is not in the divisor field
   `fullC K M` (the statement spells that field out as an `IntermediateField.adjoin`, because this
   pin file does not name `fullC`), given additionally `hbase : jqNModC K p ∉ K⟮jqModC K⟯`.

The proof of (1) is the pin's monolithic `rval_aux` (`S_:832`, 663 lines of proof), a strong
induction on `M` from the ported char-`p` splitting of `Φ_p` at a slot. The proof of (2) is
`mem_adjoin_jqNModC_of_mem_mffC` + `jqNModC_prime_not_mem_adjoin` (`S_:1515`, 334 lines), which
itself calls `rval_aux` at `ζ ^ p` (`S_:1556`): it reads the `ψ(M)` distinct slot roots off (1),
writes `jqNModC K p = g (jqNModC K M)` with `deg g < ψ(M)`, and concludes that `g` is constant on
the slots, hence `jqNModC K p ∈ K⟮jqModC K⟯`, contradicting `hbase`.

This is the **`C` layer** (arbitrary `[Field K]`) of the port's `ℚ` module
`FunctionFieldGeneration/SlotProduct.lean`, which proves the `[Algebra ℚ K]` versions
`minpoly_jqN_map_eq_prod_slots` and `jqN_prime_not_mem_full` (`jq`/`jqN`/`coeffEmb K jq` in place
of `jqModC`/`jqNModC`). It is not an instance of them: the base field is `K`, not `ℚ`. Read
`SlotProduct.lean` side by side with the pin — it is the proof template, and the pin's `C` text is
the authority wherever they differ.

## 2. Ground — import, do not restate

All public and statement-checked unless marked `private`:

| block | home | names |
|---|---|---|
| `TS` and its API | `ModularCurve/Defs/TS.lean` | `TS`, `TS_coeff_mul`, `TS_coeff_of_not_dvd`, `TS_coeff_neg`, `TS_coeff_of_lt`, `TS_ne_zero`, `TS_injective`, `TS_congr`, `qTwist_TS`, `qExpand_TS`, `qExpand_qTwist_TS`, `qTwist_TS_one_cycle`, `coeffMap_TS`, `jqModC_eq_TS`, `jqNModC_eq_TS`, `qExpand_jqNModC`, `qExpand_jqModC_eq_TS` |
| `qTwist` | `Defs/Twist.lean` | `qTwist`, `qTwist_coeff`, `qTwist_one_apply`, `qTwist_qExpand`, `qTwist_qTwist`, `qTwistEquiv`, `qTwistEquiv_apply`, `coe_qTwistEquiv`, `coeffMap_qTwist` |
| `phiAtSeed` | `Defs/PhiAtSlot.lean` | `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `phiAtSeed_natDegree`, `phiAtSeed_eval_map`, `phiAtSeed_eval_of_injective`, `aeval_intermediateField_eq_zero` |
| at-slot roots (char `p`) | `ModularCurve/PhiGenSplitsAnyField.lean` | `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot_nodup_of_isPrimitiveRoot`, `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot`, `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`, `roots_phiAtSeed_TS` |
| `jqModC`/`jqNModC` | `Defs/JqCoeff.lean` | `jqModC`, `jqNModC`, `jqModC_rat`, `coeff_jqModC_of_lt`, `coeff_jqModC_neg_one`, `order_jqModC`, `coeffEmb_jq`, `modularFunctionFieldC`, `jqModC_mem`, `jqNModC_mem` |
| conjugates | `Degree/JqCyclotomicConjugates.lean` | `units_pow_eq_one_of_isPrimitiveRoot`, `phiAtSeed_jqNModC_eval`, `phiAtSeed_jqNModC_eval_symm`, `phiAtSeed_TS_eval`, `phiAtSeed_TS_eval_symm`, **`jqNModC_congr`** (public here — the pin's `private` copy at `S_:714` is not ported) |
| `ψ` | `NumberTheory/DedekindPsi.lean`, `ModularCurve/Defs/DedekindPsi.lean` | `dedekindPsi_prime`, `dedekindPsi_prime_pow` (the pin's private `dedekindPsi_prime_pow'` at `k+1` is its instantiation, one line — do not write it), `dedekindPsi_mul_prime_dvd`, `dedekindPsi_mul_prime_not_dvd`, `dedekindPsi_mul_of_coprime`, `dedekindPsi_pos` |
| the slot count | `FunctionFieldGeneration/SlotProduct.lean` | **`card_slotFilter_eq_dedekindPsi`** — the one public counting export; `slotAt`/`slots`/`slots_eq_dedekindPsi` are `private` there and stay `private` |
| `qExpand` algebra | `Defs/Laurent.lean` | `qExpand`, `qExpand_qExpand`, `qExpand_congr`, `qExpand_one_apply`, `qExpand_injective`, `qExpandAlg` |
| generic engines | `FieldTheory/CommonRoot.lean` | `Polynomial.mem_range_of_unique_common_root` (and the algebraMap-form `mem_range_of_eval_eq_const`, which is **not** the form needed here — see §3.1) |

Mathlib: `IntermediateField.extendScalars_adjoin`, `IntermediateField.adjoin.finrank`,
`IntermediateField.mem_extendScalars`, `IntermediateField.adjoin_simple_eq_map`,
`Polynomial.aeval_algHom_apply`, `minpoly.aeval`, `Polynomial.hom_eval₂`,
`Polynomial.mem_roots`, `Polynomial.card_roots'`, `IsPrimitiveRoot.pow_inj`,
`Units.ext`, `Nat.divisors`, `Finset.card_image_of_injOn`.

## 3. The module

`FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean` (new, wired). It is
the arbitrary-field twin of `FunctionFieldGeneration/SlotProduct.lean`: **do not edit** that
module (or `PhiGenSplitsAnyField.lean`, or any other).

Header (docstring + wire):

```
spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
spec-pin: P2M/Sol/S_ModularCurve_jqNModC_prime_not_mem_fullC.lean
spec-pin: Theorems/Thm_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean
spec-pin: Theorems/Thm_ModularCurve_jqNModC_prime_not_mem_fullC.lean
```

(`TS`, `PhiAtSlot`, `JqCoeff`, `JqCyclotomicConjugates`, `PhiGenSplitsAnyField`,
`FieldTheory/CommonRoot` carry their own `spec-pin:` lines — add no others.)

The docstring states: the subject (the two headlines, one sentence each); the provenance (the two
pin URLs at `aa2d8b3`, noting they are the same 80-declaration development written twice); what
is imported rather than restated (§2); and the two deliberate residues (§3.3). Imports: the
modules of §2, plus `Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra` and
`Mathlib.RingTheory.Polynomial.RationalRoot` if the pin's `Polynomial.map_sub`/`coeff` steps need
them. Then `set_option autoImplicit false`, `noncomputable section`, `namespace ModularCurve`.
No chapter tokens (`W1`), no `p2m_*` lines. `set_option linter.style.haveILetI false` is
permitted with the same one-line justification the sibling modules carry.

### 3.1 The engine — `private`, transcribed from the pin

Pin spans are in `S_ModularCurve_minpoly_jqNModC_map_eq_prod_slots.lean`.

| port name | pin | lines | note |
|---|---|---:|---|
| `sv` | 679 | 5 | the pin's `C` def; a `private` re-declaration is legal (Lean mangles `private` names per file) and deliberate — see §3.3 |
| `sv_eq`, `sv_eq_TS` | 684, 689 | 5 + 4 | |
| `TS_congr'` | 693 | 5 | |
| `sv_inj` | 698 | 16 | `TS_injective` + `IsPrimitiveRoot.pow_inj` |
| `sv_top` | 719 | 5 | `sv K ζ M 0 = qExpand K M (jqNModC K M)` |
| `jqdC_mem_fullC` | 742 | 5 | |
| `jGenC` | 739 | 3 | `⟨jqModC K, mem_adjoin_simple_self …⟩` |
| `mem_adjoin_jqNModC_of_mem_mffC` | 747 | 23 | the pin's `extendScalars_adjoin` collapse |
| `mem_range_of_eval_eq_const` | 770 | 30 | **the `ι : F →+* L` form**, not the homed `algebraMap` form: the pin's statement has a general ring hom, so restate it (it is `private` in the pin and the port's copy at `FieldTheory/CommonRoot.lean:111` is a different statement) |
| `map_qExpand_minpoly_eq` | 800 | 32 | |
| `exists_ringHom_adjoin_of_isRoot` | 652 | 20 | |
| `ringHom_comp_aeval` | 672 | 7 | |
| `rval_aux` | 832 | 663 | the minpoly product, `M`-general; **no** `set_option maxHeartbeats` |
| `jqNModC_prime_not_mem_adjoin` | 1515 | 334 | the separation; **no** `set_option maxHeartbeats` |

`rval_aux`'s statement (the pin's, `S_:838`): for every `M` and every primitive `M`-th root `ζ`,
under `hall`, the pushed minimal polynomial equals the slot product over `sv`. The public headline
is `rval_aux`'s `if`-form (§3.2), so keep the two texts exactly as the pin has them: the private
one over `sv`, the public one over `if h : a = 0 then 0 else …` (`sv`'s body *is* that `dite`, so
`unfold sv` relates them).

**The cardinality step.** `rval_aux` and `jqNModC_prime_not_mem_adjoin` both need
`Multiset.card T = dedekindPsi M` for the multiset of slot values built from
`M.divisors` and the `gcd` filter. The pin proves it by unfolding its own `slotAt`. The port's
`slotAt`/`slots` are `private` in `SlotProduct.lean` **by design** (the slot-counting audit), and
`card_slotFilter_eq_dedekindPsi M hM` is the public export for exactly this consumer: rewrite the
multiset's cardinality into a sum of `((Finset.range (M / a)).filter …).card` and apply it.
**Stop-early**: if that reshaping costs more than ~30 lines, report — the manager will promote
`slotAt`/`slotAt_eq` rather than have you edit a landed module.

### 3.2 The two headlines — public, at the **wrapper** binders, verbatim

```lean
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
            qExpand K (a * a) (qTwist (ζ ^ (b * a)) (jqModC K))))

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
      {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}
```

These are the `Theorems/` wrappers verbatim: copy them from those files, not from the `S_` text
(the wrappers spell the `hall` conjunction out; the `S_` `private` copies agree with them, diffed).
The first is `rval_aux M ζ hζ hall`; the second is `mem_adjoin_jqNModC_of_mem_mffC` on
`hall M dvd_rfl`'s second component plus `jqNModC_prime_not_mem_adjoin`.

### 3.3 Dropped, with the reason in the header

- The whole prelude of the pin files, lines 20–354 (`TS`, `qTwist`, `phiAtSeed`, the at-slot roots
  API, `prod_form_ne_zero`, `coeffMap_*`, `qTwistEquiv*`): 130 declarations, ≈330 lines per file —
  **imported** (§2). This is 396 of this module's 1,858 once-cost lines.
- The slot-counting chain (`slotAt`, `slots`, `slotCond_*`, `slotAt_*`, `slots_*`,
  `dedekindPsi_prime_pow'`, `gcd_mul_*_of_dvd`, `gcd_eq_of_modEq`, `slotAt_mul` 108 lines): the
  port's `SlotProduct.lean` already routes around it (`slotAt_eq` + `dedekindPsiFibre_mul` +
  mathlib `Nat.Coprime.divisors_mul`), and `card_slotFilter_eq_dedekindPsi` is the export. Do not
  transcribe the pin's CRT proof.
- `jqNModC_congr` (`S_:714`): public home `Degree/JqCyclotomicConjugates.lean`.
- The `solution`/`#print axioms` tail and every `p2m_*` line.
- The private `sv` block is **re-declared**, not imported (§3.1): the `ℚ` copy in
  `SlotProduct.lean` is `[Algebra ℚ K]`-bound and its `sv_eq`/`sv_top` statements name
  `coeffEmb K jq`; unifying them would edit a landed module's statements for ~40 lines. Record it
  in the header as the module's one deliberate duplication, with that count.

## 4. Build and verification discipline

- Edit loop: `cd lean && flock .lake/flt_build.lock timeout 110 lake env lean
  -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean`,
  log to `lean/tmp/`. Every tool call is bounded — nothing over ~2 minutes; if a build needs
  longer, split the work instead of extending it.
- Then one `lake build`: `flock .lake/flt_build.lock timeout 110 lake build
  FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProductAnyField`. **Never** a tree
  `lake build`. Green = **0 errors, 0 warnings**, no `sorry`/`admit`.
- `#print axioms` on both headlines → `[propext, Classical.choice, Quot.sound]`.
- `python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean`
  → **0 mismatch / 0 missing / 0 own**. Expected `ok`: 2 headlines + `rval_aux` +
  `jqNModC_prime_not_mem_adjoin` + `map_qExpand_minpoly_eq` + `mem_adjoin_jqNModC_of_mem_mffC` +
  `sv`/`sv_eq`/`sv_eq_TS`/`sv_inj`/`sv_top`/`TS_congr'`/`jqdC_mem_fullC`/`jGenC` +
  `mem_range_of_eval_eq_const` + `exists_ringHom_adjoin_of_isRoot` + `ringHom_comp_aeval` ≈ 18
  (`private` declarations are checked too; the pin's copies are in the wire). A `MISMATCH` on
  either headline means the binder block is wrong — take the wrapper's.
- `python3 tools/deps/dedup.py --module '*SlotProductAnyField*'` → 0 clusters (a `private` `sv`
  twin in `SlotProduct.lean` is expected and is not a cluster: the tiers compare statements and
  the binders differ).
- **Do not edit any other module.** If an import is missing, add it to this module. If a ground
  module needs a change (a promotion, a missing bridge), **stop and report** — the manager owns
  ground edits (§9.3 of the topic).

## 5. Known friction, in order of likelihood

1. **`letI : Algebra F (LaurentSeries K)`.** The pin installs
   `((qExpand K N).comp (algebraMap F (LaurentSeries K))).toAlgebra` in `rval_aux` and its
   satellites, and reads `algebraMap F (LaurentSeries K) x = qExpand K N x` back by `rfl`. This is
   the one idiom that differs most from the `ℚ` twin (which has the `coeffEmb` composition); keep
   the pin's shape and do not let typeclass search unfold `qExpand`.
2. **Heartbeats.** The pin caps `rval_aux` and `jqNModC_prime_not_mem_adjoin` at 6,400,000. The
   port must carry **no** `set_option maxHeartbeats`: the `ℚ` twin fits at 200,000. A 200k
   timeout is a diagnostic — name the lemmas, split the step, report the declaration.
3. **`haveI : NeZero a := ⟨ha⟩`.** The port's linter prefers `have` for `Prop`-classes; use
   `have` where the pin writes `haveI` (the sibling modules set `linter.style.haveILetI false`
   instead — either is accepted, be consistent within the file).
4. **`Multiset.range p` vs `Finset.range p`.** `roots_prime_at_slot` returns a `Multiset`,
   `roots_phiAtSeed_TS` a `Multiset` of roots; the products are `Finset`. Use the ported
   statements' shapes and `Fin.prod_univ_eq_prod_range` where the pin converts.
5. **The `sv` `if`-form.** The public headline's product is over the `if h : a = 0 then 0 else …`
   dite; `rval_aux`'s is over `sv`. Both texts are in the wire, so keep both; relate them by
   `unfold sv` (or a 1-line `sv`-unfolding `simp only [sv, dif_neg]`).
6. **`Polynomial.map` bookkeeping.** `map_qExpand_minpoly_eq` is `Polynomial.map_map` + the
   `qExpand` composition (`qExpand_qExpand`) + `Polynomial.map_prod`/`map_sub`/`map_X`/`map_C`;
   the `ℚ` twin does it with `coeffEmb_qExpand`, this one with `qExpand_qExpand` directly.
7. **`zeta` powers.** Where the `ℚ` twin writes `coeffEmb K (qExpand ℚ M (jqN M))`, write
   `qExpand K M (jqNModC K M)`; `iota_jqN` has no `C` analogue and is not needed.

## 6. Report

Report: the module written and its written-line count vs the ~1,400 content / 1,550–1,820 written
bound; the build readings; the checker reading (with every `own:` row if any); the axioms;
`dedup.py`/`move_dead.py`; the frontier reading for both nodes (`needed 0`, "target is ported");
and every pin declaration dropped with its pin lines and reason. Friction goes to
`lean/instance-friction.md` only when instance search is the cause. Do not add a "landed" entry to
`CARRY-FORWARD.md`.

## 7. Result

Landed 2026-10-25 (worker; reviewed by the manager). Both nodes read `needed 0`, "target is
ported".

**The module.** `ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean`, **1,283 lines**
(72 blank) — 17 declarations: the two public headlines and 15 `private` (the pin's private engine,
transcribed). Under the 1,550–1,820 written bound for the reasons the order priced: nothing
restated, no `p2m_*` scaffolding, no `coeffEmb` plumbing in the `sv` block, and the counting step
at 23 lines instead of the pin's 40.

**Gates.** `lake build` green (4,193 jobs together with CL2; 60 s for this module), **0 warnings**,
no `sorry`; `#print axioms` on both headlines `[propext, Classical.choice, Quot.sound]`;
`check_port.py --force` reads

    2 ok, 0 mismatch, 0 missing, 0 own, 0 kw — 1 module(s), 1 checked, 0 cached; corpus aa2d8b3

with both headlines `ok` at the twin's `S_` copies (`:1849`, `:1869`, which are the wrappers'
statements) — no `own:` row, no marker; `dedup.py` over both C-layer modules reads
`62 declarations, 0 duplicate clusters, 0 removable`; `move_dead.py --select dead` reads
`0 declarations, 0 lines`; `frontier.py --ds` reads `needed 0` for both nodes.

**The finding: the 200k edit loop is too tight here, and it was already too tight for the `ℚ`
twin — so it is the proof shape, not the `C` layer.** Profiled with `-Dprofiler=true` (v4.34.0,
this tree). The module's ~65 s splits, by truncation profiling, into `import` 3.2 s, the 11
prelude declarations ~2 s, **`rval_aux` ≈46 s**, and the separation + two headlines ≈15 s. Inside
`rval_aux` (66 events over 100 ms):

| share | what |
|---:|---|
| **19.3 s** | **one single `type checking` event** — the check of the finished 661-line proof term against its statement (the statement itself elaborates in 0.1 s, so this is term size, not type size) |
| ~14 s | tactics: `rewriteSeq` 6.7 s over 26 events, `refine` 3.0, `congr` 1.8, `obtain`/`rcases` 1.2 |
| ~10 s | typeclass search, largest single searches `Algebra` 1.5 s, `AddHomClass` 0.7, `AddMonoidHomClass` 0.6, `Module` 0.6 |

The decisive datum is the **landed `ℚ` twin** (`FunctionFieldGeneration/SlotProduct.lean`,
692-line `rval_aux`): type checking 20.3 s *with the same single 18.9 s event*, tactics 12.6 s,
typeclass 16.4 s. The `C` layer is therefore within ~15 % of the `ℚ` layer, and the 19 s final
check is inherent to "one 660-line strong induction" — it is *not* caused by the wrapper's
spelled-out `hall` (the twin states that hypothesis with the opaque `modularFunctionFieldFull` and
pays the same 19 s). Thresholds: 200k and 300k both fail (`SlotProductAnyField.lean:758` at 200k,
inside the induction), 350k is clean; the `ℚ` twin also fails 200k (`whnf`, `SlotProduct.lean:992`).
Both are 11–13× under the project's global `maxHeartbeats = 4_000_000`, and neither module carries
an override. Mitigations actually applied: `hall M dvd_rfl` taken once, an explicit `Module.Free`
on the top adjoin tower, `dite_eq_right` for the deprecated `dif_neg`.

**If someone wants it materially cheaper, the lever is splitting `rval_aux` into 2–3 lemmas**
(one 19 s check becomes several smaller ones; the check is superlinear in term size), not a
restatement of the hypothesis — that would buy single-digit seconds for a 661-line refactor on a
green module. **Do not treat a 200k timeout in this file as a defect signal; the gate is
`lake build`.**

**The counting step: the public export carries it.** `card_slotFilter_eq_dedekindPsi` replaces the
pin's 40 lines (`Multiset.card_bind` + a `Multiset.map_congr` fibre-card identity + the export;
the `Multiset.sum`/`Finset.sum` conversion is definitional), so `slotAt`/`slotAt_eq`/`slots_eq_dedekindPsi`
stay `private` in `SlotProduct.lean` and no landed module was touched. The stop-early trigger
(~30 lines) never fired.

**Route taken.** The pin's `exists_ringHom_adjoin_of_isRoot` + `ringHom_comp_aeval` ring-hom route,
not the `ℚ` twin's `algHomAdjoinIntegralEquiv`/`letI : Algebra` route — so the order's friction
entry 1 never arose. Both engines are `private` (the `FieldTheory/CommonRoot.lean` copies are
different statements). The `sv` block (~40 lines) is re-declared as sanctioned; `check_port` and
`dedup.py` see no cluster.

**Manager's two corrections.** (i) The header's prelude count: the pin's prelude is **40**
declarations (lines 37–354), not "~130" (that figure is the three-file substitution count from the
scoping pass); corrected in both new headers. (ii) The consumer: see the wave record.

### 7.1 Refactor pass (2026-10-25, second dispatch) — clarity and speed

The module was cut for readability: 1,283 → 1,512 lines, **43 declarations** (2 public headlines
+ 41 `private`), every statement byte-identical (checker 2 ok / 0 own; `rval_aux`'s statement
diffed against the pre-split copy, identical).

| declaration | body before | body after |
|---|---:|---:|
| `rval_aux` | 661 | **96** |
| `jqNModC_prime_not_mem_adjoin` | 322 | **94** |
| longest body in the file | 661 | **148** |

The structure that made it work: a shared slot-multiset API (`slotValues`, `mem_slotValues`,
`card_slotValues`, `prod_slotValues`, `nodup_slotValues`, `sv_inj_slot`, …) that **both** headlines
run on — the second monolith's own `T'`/counting/nodup/glue (~90 lines) disappeared — then the
induction as a named predicate `SlotProductAt` with the per-slot dispatch split into
`isRoot_map_minpoly_sv_top` / `…_of_dvd` / `…_of_not_dvd` / `…_of_descent`. `hslot_root` could not
become one lemma (it needs the hypothesis at a smaller `M`, at a different `ζ` and general `K`), so
`SlotProductAt` is a `def` (A/B'd: `def` 31–35 s vs `abbrev` 34 s — an `abbrev` re-unfolds the slot
product at every use) and `rval_aux` instantiates the polymorphic induction hypothesis once to a
monomorphic-in-`K` `IH'`.

**Both gains are real, and the speed one is the larger.** This module was the *slow* member of the
pair — **54 s wall** (manager's interleaved A/B: 54.12 s / 54.47 s) against its sibling
`PrimePowerStepAnyField`'s 13–15 s, and it needed **350k heartbeats** (200k/250k/300k all failed)
where the sibling needed 45k. After the split: **35.98 s / 33.55 s wall (−36 %)** and **100k
heartbeats pass, 75k fails** — a ~3.5× lower peak for the same proof. So the two monoliths were
most of this module's build cost, and cutting them cut it.

Footnote for accuracy: **user CPU rose 60.6 s → 73.4 s**. Many smaller declarations parallelise
better in codegen, so part of the wall gain is parallelism rather than less work; wall is what the
edit loop and the build actually pay, so the gain stands, but the module does not do less total
computation. The one 19–20 s type check did **not** shrink, and the worker bisected it: it appears
exactly when `finrank_adjoin_mul_dedekindPsi` is added, and its proof is the pin's own
`finrank_mul_finrank`/`adjoin_adjoin_left`/`restrictScalars` block — i.e. it was always that
sub-proof, previously buried in `rval_aux`, now isolated and named.

So the pass is scored on clarity: the two proofs anyone must read went 661 + 322 → 96 + 94 over
named sub-goals, and the profile's largest single event is now attributable to one lemma.
