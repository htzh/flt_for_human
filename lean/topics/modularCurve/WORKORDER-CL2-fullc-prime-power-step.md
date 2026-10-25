# WORKORDER-CL2 — the prime-power step of the divisor field over an arbitrary field

Status: **dispatched 2026-10-25**; §2.0 (the manager's hub edit) **is landed** — record:
[logs/x0-function-field-general-index.md](../../logs/x0-function-field-general-index.md). Worker:
the module of §3.

One D-S node:

| node | pin wrapper | pin `S_` | raw lines | citers | frontier |
|---|---|---|---:|---:|---|
| `ModularCurve.relfinrank_fullC_mul_prime_pow` | `Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean` | `P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean` | 1,175 | 1 (`package_of_socket`) | needed 1 |

`needed 1` means every premise is ported: this is a transcription with the field general, not a
re-derivation. Pinned at `anthropics/fermats-last-theorem@aa2d8b3`.

## 1. What the mathematics is

For a field `K`, write `fullC K L` for the intermediate field of `LaurentSeries K` generated over
`K` by all `jqNModC K d` with `d ∣ L`, and `eFull K p L` for its image under `qExpand K p`. The
theorem is the prime-power step of the tower `fullC K (M * p ^ a)` (the `q`-expansion model of the
function fields of `X₀(n)`, whose total degree over `K(j)` is `ψ(n)`):

```lean
theorem ModularCurve.relfinrank_fullC_mul_prime_pow {K : Type*} [Field K] (M : ℕ) [NeZero M]
    (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℕ) (hpM : ¬ p ∣ M) (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p ^ (a + 1)))
    (hprev : ∀ b : ℕ, a = b + 1 → IntermediateField.relfinrank
        (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ b ∧ x = jqNModC K d'})
        (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (b + 1) ∧ x = jqNModC K d'})
      = if b = 0 then p + 1 else p)
    (hnm : a = 0 → jqNModC K p ∉ IntermediateField.adjoin K
        {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M ∧ x = jqNModC K d'}) :
    IntermediateField.relfinrank
      (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ a ∧ x = jqNModC K d'})
      (IntermediateField.adjoin K {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ M * p ^ (a + 1) ∧ x = jqNModC K d'})
    = if a = 0 then p + 1 else p
```

**The proof, in five moves** (pin `S_`, in this order):

1. **Vocabulary.** `fullC`, its divisor set `divSet`, and the pushed field
   `eFull K p L = (fullC K L).map (qExpandAlg K p)`; `eFull` is the field in which the `p` copies
   of `jqModC K` under `qTwist` are conjugate, which is what makes the degree computable.
2. **Generation.** `jqNModC_mem_of_div_primes` (two-prime descent: if `jqNModC K (d/p)` and
   `jqNModC K (d/q)` lie in `F`, so does `jqNModC K d`, by the unique-common-root principle applied
   to `Φ_p` and `Φ_q`), then `jqNModC_mem_adjoin_top_insert` walks the divisors of
   `M * p ^ (a+1)`, and `fullC_succ_eq_adjoin_insert_divSet` /
   `fullC_mul_prime_eq_adjoin_insert_image` turn that into
   `fullC K (M * p ^ (a+1)) = adjoin K (insert (jqNModC K (p ^ (a+1))) (divSet K (M * p ^ a)))`
   resp. `fullC K (L₀ * p) = adjoin K (insert (jqModC K) ((qExpandAlg K p) '' divSet K L₀))`.
3. **Integrality and degree bounds.** `phiAtSeed data (jqModC K)` is monic of degree `p + 1` and
   annihilates `jqNModC K p`; its `natDegree` bounds `minpoly` from above
   (`natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem`).
4. **The `eFull` degree block.** `le_natDegree_minpoly_jqModC_eFull`: the `p` elements
   `qTwist (ζ ^ b) (jqModC K)` are fixed by `eFull`'s scalars (`qTwist_eq_self_of_mem_eFull`),
   hence `p` distinct roots of the pushed minimal polynomial, hence `p ≤ natDegree`; combined with
   step 3 it gives `finrank_adjoin_jqNModC_prime_of_not_mem'` = `p + 1`, and
   `relfinrank_eFull_fullC_eq_natDegree` transfers it to `[fullC K (L₀ * p) : eFull K p L₀]`.
5. **The step.** `relfinrank_fullC_step` assembles the tower: `a = 0` is `p + 1` and the induction
   hypothesis `hprev` supplies the rest.

This is the `C`-layer counterpart of two already-ported `ℚ` modules:
`FunctionFieldGeneration/Generation.lean` (`jqN_mem_of_div_primes`,
`w1_jqN_mem_adjoin_top_insert`, `full_eq_adjoin_full_div_prime`) and
`FunctionFieldGeneration/DegreeStep.lean` (`finrank_adjoin_jqN_prime_of_not_mem`,
`relfinrank_full_eq_mul`). Those are **the proof templates, not substitutes**: their base field is
`ℚ` (or an `[Algebra ℚ K]`-algebra with `coeffEmb`), the base here is arbitrary `K`. Read them side
by side; the pin's text is the authority.

## 2. Ground

### 2.0 The one hub edit — **landed 2026-10-25**

`ModularCurve/X0/FunctionFieldFull.lean`: **drop the vestigial `[NeZero N]`** from
`divisorExpansionsC` and `modularFunctionFieldFullC` (and from the two `variable` lines, and the
five `omit [NeZero N] in` lines that then become illegal). Reason: the pin states its lemmas about
these fields at `L`, `L * n`, `M * p ^ a` with no `NeZero` on the index, and `[NeZero (L * n)]`
is not synthesizable from the module's hypotheses. The binder is unused in both bodies — 5 of the
section's 7 lemmas already `omit` it. 52 references to `modularFunctionFieldFullC` in 7 modules (7 to `divisorExpansionsC` in 2), all
of which supply `NeZero` today, so the call sites only lose an implicit argument. Re-run that module's `spec-pin:` check
afterwards (its statements are unchanged).
**Landed:** elaboration clean (0 warnings), checker **13 ok / 0 mismatch / 0 missing / 1 own**
(the `own` row is pre-existing), `lake build` green (4,135 jobs) and the five dependents green
(4,460 jobs). Details and the two `MISMATCH` probes: [logs/x0-function-field-general-index.md](../../logs/x0-function-field-general-index.md).

Probed 2026-10-25 in a throwaway file importing `X0/FunctionFieldFull` (exit 0, no output), at
`[NeZero L]`:

```lean
example (L : ℕ) [NeZero L] :
    divisorExpansionsC K L
      = {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (L : ℕ) [NeZero L] :
    modularFunctionFieldFullC K L
      = IntermediateField.adjoin K
          {x : LaurentSeries K | ∃ (d' : ℕ) (_ : NeZero d'), d' ∣ L ∧ x = jqNModC K d'} := rfl
example (n : ℕ) [NeZero n] (f : LaurentSeries K) : qExpandAlg K n f = qExpand K n f := rfl
```

### 2.1 The three respellings — `abbrev`s in the module, not new mathematics

The pin's `S_` file re-declares, locally, three objects the port already homes (and it re-declares
them a second time in `S_..._package_of_socket.lean`, `diff` = 4 lines). Write them as one-line
`abbrev`s in this module so that every statement below is the pin's text **verbatim**:

```lean
abbrev divSet (K : Type*) [Field K] (L : ℕ) : Set (LaurentSeries K) := divisorExpansionsC K L
abbrev fullC (K : Type*) [Field K] (L : ℕ) : IntermediateField K (LaurentSeries K) :=
  modularFunctionFieldFullC K L
abbrev qExpandₐK (K : Type*) [Field K] (n : ℕ) [NeZero n] : LaurentSeries K →ₐ[K] LaurentSeries K :=
  qExpandAlg K n
```

The docstrings say so ("the pin's local `S_` spelling of `modularFunctionFieldFullC`"). Nothing
else may import them; a second consumer is a **promotion for the manager**, not a copy
(playbook §3.7). The alternative — stating the module over the homed names — costs ~10 `own:` rows
in `spec/decl_markers.tsv` and is the recorded fallback; take it only if the `abbrev` route
misfires (report which and why).

### 2.2 Imported — do not restate

| block | home | names |
|---|---|---|
| `fullC` vocabulary | `X0/FunctionFieldFull.lean` | `divisorExpansionsC`, `modularFunctionFieldFullC`, `mem_divisorExpansionsC`, `jqModCd_mem_full`, `jqModC_mem_full`, `full_degeneracyC_le` |
| `qExpand` algebra | `Defs/Laurent.lean` | `qExpand`, `qExpandAlg`, `qExpandAlg_apply`, `qExpand_qExpand`, `qExpand_congr`, `qExpand_one_apply`, `qExpand_injective` |
| `jqModC`/`jqNModC` | `Defs/JqCoeff.lean` | `jqModC`, `jqNModC`, `jqNModC_eq_TS`, `jqNModC_one`, `coeff_jqModC_of_lt`, `modularFunctionFieldC` |
| `TS` API | `Defs/TS.lean` | `TS`, `TS_injective`, `TS_congr`, `qExpand_jqNModC`, `qTwist_TS_one_cycle` |
| `qTwist` | `Defs/Twist.lean` | `qTwist`, `qTwist_one_apply`, `qTwist_qExpand`, `qTwist_qTwist`, `qTwistEquiv`, `qTwistEquiv_apply`, `coe_qTwistEquiv` |
| `qTwist` fixes a twisted expansion | `Defs/KatzLevelPCusps.lean` | `qTwist_qExpand_of_pow_eq_one` |
| `phiAtSeed` | `Defs/PhiAtSlot.lean` | `phiAtSeed`, `phiAtSeed_map`, `phiAtSeed_monic`, `phiAtSeed_natDegree`, `phiAtSeed_jqNModC_eval_symm` |
| at-slot splitting + roots | `PhiGenSplitsAnyField.lean` | `PhiGen.splits_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot_nodup_of_isPrimitiveRoot`, `roots_prime_at_slot_roots_nodup_of_isPrimitiveRoot`, `isRoot_prime_at_slot_iff_of_isPrimitiveRoot`, `roots_phiAtSeed_TS` |
| conjugates | `Degree/JqCyclotomicConjugates.lean` | `units_pow_eq_one_of_isPrimitiveRoot`, `jqNModC_congr` (**the pin's private `S_:360` copy is not ported**) |
| `ψ` | `NumberTheory/DedekindPsi.lean`, `ModularCurve/Defs/DedekindPsi.lean` | `dedekindPsi_one`, `dedekindPsi_prime`, `dedekindPsi_prime_pow`, `dedekindPsi_mul_prime_dvd`, `dedekindPsi_pos` |
| irreducible `Φ` | `ModularPolynomialProperties.lean` | `exists_phiIrreducible_evalSymm` |
| generic engines | `FieldTheory/CommonRoot.lean` | `Polynomial.mem_range_of_unique_common_root`, `Polynomial.irreducible_of_transitive_ringAut` |

Mathlib: `IntermediateField.relfinrank_eq_finrank_of_le`, `IntermediateField.extendScalars_adjoin`,
`IntermediateField.adjoin.finrank`, `IntermediateField.adjoin_map`, `IntermediateField.adjoin_le_iff`,
`IntermediateField.adjoin.mono`, `IntermediateField.mem_map`, `minpoly.aeval`, `minpoly.monic`,
`minpoly.eq_of_irreducible_of_monic`, `Polynomial.hom_eval₂`, `Polynomial.card_roots'`,
`Polynomial.natDegree_map`, `Nat.minFac_prime`, `Nat.sum_div_divisors`, `Nat.Coprime.dvd_of_dvd_mul_right`.

## 3. The module

`FLTForHuman/ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean` (new, wired).
Header wire:

```
spec-pin: P2M/Sol/S_ModularCurve_relfinrank_fullC_mul_prime_pow.lean
spec-pin: Theorems/Thm_ModularCurve_relfinrank_fullC_mul_prime_pow.lean
```

Docstring: subject; provenance (pin URL at `aa2d8b3`, and that the pin writes the `divSet`/`fullC`/
`eFull`/`qExpandₐK` block twice — here it is homed once, once the manager retires the `[NeZero]`);
the layering (imports of §2.2); the `abbrev` decision of §2.1; and the statement that `eFull` is
the vocabulary the next `C`-layer node (`package_of_socket`) will import. Then
`set_option autoImplicit false`, `noncomputable section`, `namespace ModularCurve`, no chapter
tokens.

Sections, in this order (declaration, pin line, pin lines):

**3.1 Vocabulary — public** (`S_:354–436`)

| declaration | pin | disposition |
|---|---|---|
| `divSet`, `fullC`, `qExpandₐK` | 354, 357, 396 | `abbrev`s (§2.1) |
| `qExpandₐK_apply` | 403 | the pin's `@[scoped simp]` `rfl` lemma |
| `jqNModC_mem_divSet` | 363 | 3 lines (`mem_divisorExpansionsC`) |
| `divSet_mono` | 366 | 4 |
| `jqNModC_mem_fullC` | 370 | 3 |
| `jqModC_mem_fullC` | 373 | 4 |
| `fullC_mono` | 377 | 3 |
| `fullC_le_iff` | 380 | 9 |
| `jqNModC_injective` | 389 | 4 (`TS_injective`) |
| `qTwist_jqModC_eq_TS` | 393 | 3 |
| `qExpandₐK_jqNModC` | 405 | 3 |
| `eFull` (**new object**) | 408 | `def eFull (K) [Field K] (n) [NeZero n] (L) : IntermediateField K (LaurentSeries K) := IntermediateField.adjoin K ((qExpandₐK K n) '' divSet K L)` |
| `eFull_eq_map` | 411 | 3 (`IntermediateField.adjoin_map`) |
| `eFull_mono` | 414 | 3 |
| `jqNModC_mul_mem_eFull` | 417 | 4 |
| `exists_eq_qExpand_of_mem_eFull` | 421 | 6 |
| `qTwist_eq_self_of_mem_eFull` | 427 | 5 (`qTwist_qExpand_of_pow_eq_one`) |
| `eFull_le_fullC` | 432 | 8 |

**3.2 Insertion algebra — public** (`S_:440–479`): `mem_adjoin_of_mem` (4),
`relfinrank_adjoin_insert` (16), `relfinrank_adjoin_insert_eq_natDegree` (6),
`relfinrank_fullC_insert_eq_natDegree` (5), `relfinrank_eFull_insert_eq_natDegree` (10). These are
`IntermediateField` bookkeeping (`extendScalars_adjoin`, `relfinrank_eq_finrank_of_le`,
`adjoin.finrank`); transcribe as written.

**3.3 Integrality of `jqModC` — public** (`S_:481–537`): `phiAtSeed_map_algebraMap` (4),
`aeval_phiAtSeed_eq_zero` (6), `isIntegral_of_phiAtSeed_root` (5),
`natDegree_minpoly_le_dedekindPsi_of_phiAtSeed_root` (8),
`natDegree_minpoly_le_of_phiAtSeed_root_of_root_mem` (34).

**3.4 Generation — public** (`S_:538–888`): `jqNModC_mem_of_div_primes` (113),
`jqNModC_mem_of_div_prime_of_mul_prime` (119), `jqNModC_mem_adjoin_top_insert` (53),
`fullC_succ_eq_adjoin_insert_divSet` (13), `fullC_mul_prime_eq_adjoin_insert_image` (53).
The first is the two-prime descent (`exists_phiIrreducible_evalSymm` +
`Polynomial.mem_range_of_unique_common_root`); the 119-line second is the single-prime induction
step with `Nat.minFac`. The `ℚ` template is `Generation.lean` — but note that file's
`jqN_mem_of_div_primes` is *not* field-general (its `F` is over `ℚ`), so it cannot be called; the
`C` proof is a replay.

**3.5 The `eFull` degree block — public** (`S_:889–982`): `jqNModC_prime_mem_eFull` (6),
`phiAtSeed_jqNModC_prime_eval_jqModC` (5), `isIntegral_jqModC_eFull` (5),
`natDegree_minpoly_jqModC_eFull_le` (6), `natDegree_minpoly_jqModC_eFull_le_of_dvd` (13),
`le_natDegree_minpoly_jqModC_eFull` (51), `relfinrank_eFull_fullC_eq_natDegree` (8). This is the
node's genuinely new mathematics (no `ℚ` counterpart anywhere): the `p` `qTwist`-conjugates of
`jqModC K` are distinct roots of the pushed minimal polynomial because `eFull` is `qTwist`-fixed.

**3.6 The step and the headline** (`S_:983–1175`):
`finrank_adjoin_jqNModC_prime_of_not_mem'` (60, public — this is the pin's general-field replay of
`DegreeStep.lean`'s `finrank_adjoin_jqN_prime_of_not_mem`), `relfinrank_fullC_step` (110, public),
`fullC_mul_prime_pow_eq_adjoin` (6, `private`, the pin keeps it `private`),
`finrank_adjoin_jqNModC_prime_of_not_mem` (5, `private`, the discharge wrapper), then the
**public headline** at the wrapper's binders verbatim (§1; the pin's own copy is `private` at
`S_:1164` and is the same statement, diffed).

**Dropped, with the reason in the header:** `jqNModC_congr` (`S_:360`; public home
`Degree/JqCyclotomicConjugates.lean`); the pin's prelude lines 20–350 (`TS`, `qTwist`, `phiAtSeed`,
the at-slot roots API, `coeffMap_*`, `qTwistEquiv*` — 32 declarations already in the port, 264
lines); the pin's `solution`/`#print axioms`/`p2m_*` tail. Nothing else is dropped: all 44 of the
`divSet`/`eFull`-layer declarations have a consumer inside the module (checked with `grep -c`).

## 4. Build and verification discipline

- Edit loop: `cd lean && flock .lake/flt_build.lock timeout 110 lake env lean
  -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean`,
  log to `lean/tmp/`. Every tool call is bounded — nothing over ~2 minutes; split the work rather
  than extend a bound.
- Then `flock .lake/flt_build.lock timeout 110 lake build
  FLTForHuman.ModularCurve.FunctionFieldGeneration.PrimePowerStepAnyField`. **Never** a tree
  `lake build`. Green = **0 errors, 0 warnings**, no `sorry`/`admit`.
- `#print axioms` on the headline → `[propext, Classical.choice, Quot.sound]`.
- `python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean`
  → **0 mismatch / 0 missing / 0 own** (the `abbrev` route of §2.1). Expected `ok` = 47: the 47
  declarations of §3.1–§3.6 (the three respellings included — a `def`'s statement is its type),
  with the pin's `jqNModC_congr` dropped. A `MISMATCH` on a `fullC`/`divSet` statement means the
  `abbrev` is not being read as the pin's text — report rather than rename.
- `python3 tools/deps/dedup.py --module '*PrimePowerStepAnyField*'` → 0 clusters (the `abbrev`s are
  `rfl`-aliases, not copies; `dedup.py`'s `body` tier may flag them — if it does, report the row
  before changing anything).
- `python3 tools/deps/frontier.py --ds --target ModularCurve.relfinrank_fullC_mul_prime_pow --list`
  → `needed 0`, "target is ported".
- **Do not edit any other module** — in particular not `X0/FunctionFieldFull.lean` (§2.0 is the
  manager's) and not `Generation.lean`/`DegreeStep.lean`. If a ground module needs a change, **stop
  and report** at first belief.

## 5. Known friction, in order of likelihood

1. **`fullC` at a product index.** `fullC K (M * p ^ a)`, `fullC K (L₀ * p)`, `fullC K (d * n)`
   are all nonzero but Lean does not synthesize `NeZero (M * p ^ a)` — that is precisely what §2.0
   removes. If §2.0 is not landed, every such statement gains a hypothesis and the checker reports
   `own:`; do not proceed on that basis, report instead.
2. **`eFull`'s `IntermediateField.adjoin` over a set image.** `eFull_eq_map` is
   `IntermediateField.adjoin_map`; the rewrite direction matters (`eFull K n L` vs
   `(fullC K L).map (qExpandₐK K n)`) and the pin uses both. Keep the pin's `abbrev`-free body if
   the `qExpandₐK`-in-`adjoin` shape trips `adjoin_map`.
3. **`qTwist` on `LaurentSeries K` as a `RingEquiv`.** `qTwistEquiv ζ` and its `_apply` are
   homed; `hσ`/`hcycle` in the pin's `finrank_adjoin_jqNModC_prime_of_not_mem'` are the
   `qTwistEquiv_apply` + `qTwist_TS_one_cycle` pair, exactly as in the ported `ℚ` proof.
4. **`Nat.minFac` induction.** `fullC_mul_prime_eq_adjoin_insert_image`'s 53 lines are a
   `Nat.strong_induction_on` with `Nat.minFac_prime` / `Nat.minFac_dvd`; the pin's
   `haveI : NeZero (d / l)` idiom is a `have` in the port's linter settings.
5. **`IntermediateField` instance shape.** `relfinrank` needs both sides as `IntermediateField K
   (LaurentSeries K)`; the pin installs `letI : Algebra F (LaurentSeries K)` in several places to
   make `adjoin F _` elaborate. Keep the pin's `letI`s; they are the reason the proofs close at
   the project cap.
6. **`qExpandₐK` abbreviation unfolding in `simp`.** `@[scoped simp] qExpandₐK_apply` must be
   registered like the pin's; `open scoped` it or `rw [qExpandₐK_apply]` explicitly, and prefer
   `qExpandAlg_apply` where the statement does not need the pin's name.
7. **No heartbeat bumps.** This pin file sets none; the port's 200k cap is the budget. A timeout is
   a diagnostic — split the declaration, name the lemmas, report it.

## 6. Report

Report: the module written and its written-line count vs the 874 content / 960–1,140 written
bound; whether the `abbrev` route held the checker at 0 `own:` (and if not, the exact rows); the
build readings; the axioms; `dedup.py`/`move_dead.py`; the frontier reading (`needed 0`); every
pin declaration dropped with its line and reason; and the measured split between "transcribed" and
"reshaped" declarations (the `C` substitutions that bit). Friction goes to
`lean/instance-friction.md` only when instance search is the cause. Do not add a "landed" entry to
`CARRY-FORWARD.md`.

## 7. Result

Landed 2026-10-25 (worker; reviewed and finished by the manager). The node reads `needed 0`,
"target is ported".

**The module.** `ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean`, **1,108
lines** — 45 declarations (3 `abbrev`s, `eFull`, 41 theorems), all public; the 960–1,140 bound
held. It closed at the 200k heartbeat cap on the first clean pass: **no split and no cap bump**,
and the file carries no `set_option maxHeartbeats`.

**The `abbrev` route held: 0 `own:` rows.** `spec/check_port.py --force` reads

    45 ok, 0 mismatch, 0 missing, 0 own, 0 kw — 1 module(s), 1 checked, 0 cached; corpus aa2d8b3

(45, not this order's 47: the checker skips `private` and the order keeps no private declaration
after the manager's cleanup below — 45 is every declaration in the file.) The three respellings
match by type, as predicted, and no `fullC`/`divSet` statement needed a marker.

**Gates.** `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.PrimePowerStepAnyField`
green (4,189 jobs, 11 s), **0 warnings**, no `sorry`; `#print axioms` on the headline,
`relfinrank_fullC_step` and `finrank_adjoin_jqNModC_prime_of_not_mem'` all
`[propext, Classical.choice, Quot.sound]`; `dedup.py --module '*PrimePowerStepAnyField*'` reads
`45 declarations, 0 duplicate clusters, 0 removable lines`; `frontier.py --ds --target
ModularCurve.relfinrank_fullC_mul_prime_pow` reads `needed 0 / target is ported`, the cone 52
nodes / 11,723 lines.

**Manager's cleanup (2 declarations, 31 lines).** The worker kept the pin's two `private`
re-exports at `S_:1153`/`S_:1159` (`fullC_mul_prime_pow_eq_adjoin`,
`finrank_adjoin_jqNModC_prime_of_not_mem`) as the order asked. They are **dead in the pin**: a
`grep` over the whole pin tree returns one occurrence of each — its own declaration — and each
restates a public declaration above it (the first is `fullC_succ_eq_adjoin_insert_divSet` past one
`IntermediateField.adjoin_insert_adjoin`, the second is
`finrank_adjoin_jqNModC_prime_of_not_mem'` verbatim). They are the pin's namespace-re-export
idiom, not mathematics, so they are dropped (playbook §2.3's dead-residue rule); the header
records both with their lines and reasons, and the `dedup.py` cluster they formed (12 removable
lines) is gone. Nothing else was dropped: the pin's prelude (41 declarations) and `jqNModC_congr`
are imports.

**Reshaping, statement-invariant (5 declarations).** All 45 statements are the pin's text
verbatim; the proofs needed (i) one extra `modularFunctionFieldFullC` unfolding in
`fullC_le_iff`/`eFull_eq_map` — the `abbrev` boundary; (ii) `qExpandₐK_jqNModC` does not fire
syntactically in `eFull_le_fullC` and in `fullC_mul_prime_eq_adjoin_insert_image`'s second half,
because `divSet`'s membership predicate is already `qExpand`-shaped (`rw [qExpandₐK_apply,
qExpand_qExpand]` plus a `Nat.mul_comm` divisibility restatement); (iii) the pin's
`if_pos`/`if_neg` are `ite_eq_left`/`ite_eq_right` (4 sites, the same deprecation
`DegreeStep.lean` takes). Call sites of the at-slot roots API use the port's
`_of_isPrimitiveRoot` names.

**Friction worth keeping.** None for `instance-friction.md` (no instance-search failure). The
`eFull` block — `eFull`, `eFull_eq_map`, `eFull_mono`, `jqNModC_mul_mem_eFull`,
`exists_eq_qExpand_of_mem_eFull`, `qTwist_eq_self_of_mem_eFull`, `eFull_le_fullC` and the
`p ≤ natDegree` root count — is the vocabulary the next `C`-layer node (`package_of_socket`)
imports from here rather than re-deriving, which is why it is public.

### 7.1 Refactor pass (2026-10-25, second dispatch)

The module was then cut for clarity: 1,108 → 1,296 lines, 45 public / **20 new `private` lemmas**
(max private body 34 lines), every public statement byte-identical (checker 45 ok / 0 own).

| declaration | body before | body after |
|---|---:|---:|
| `jqNModC_mem_of_div_primes` | 118 | **59** |
| `jqNModC_mem_of_div_prime_of_mul_prime` | 114 | **60** |
| `relfinrank_fullC_step` | 104 | **23** |
| `fullC_mul_prime_eq_adjoin_insert_image` | 57 | **19** |
| `jqNModC_mem_adjoin_top_insert` | 50 | **12** |

**Build time: no measurable change.** The worker's alternating A/B builds read 13.40 s baseline vs
13–15 s after (`lake` prints 10 s; the tree was noisy from the concurrent worker). The manager's
independent A/B, `lake env lean` twice interleaved on the two copies, reads **orig 13.25 s /
10.99 s vs split 9.04 s / 11.56 s** — the within-version spread swamps any difference, so the
module is ~11–13 s either way. The worker's profiler split (tactic 9.53 → 8.69 s, typeclass 5.67 →
6.11 s, type checking 1.93 → 1.86 s) could not be re-read afterwards: the two concurrent workers
shared `lean/tmp`, and `tmp/prof_before.txt` now holds the *other* module's profile (a 21.6 s
tactic run). The A/B wall times above are the durable evidence; the profiler figures are as
reported. The minimum `maxHeartbeats` is unchanged at
**45,000** (both versions fail at 40,000, in the untouched §3 lemma). So the pass is a clarity win
with no regression — the decision rule's "restore the original" branch was reached and avoided with
numbers, not assumed.

**The reusable finding: do not `set` a large subterm.** An intermediate version named the two
pushed slot polynomials with `set P` / `set Q`; `rw`/unification then unfolds that local definition
at every occurrence, and tactic execution went 9.5 → **15–17 s**. Reverting to the pin's literal
terms restored it. The same effect showed up for a `rw [phiAtSeed]` inside a repeated step
(≈1.5 s per use: stating the sub-lemmas on the at-slot API's own form avoids it), and for
`rw … at hyA` on a root disjunction (≈1.5 s each: taking the disjunctions as hypotheses avoids it).
A *small* `set` (`set g := Nat.gcd d M`, a `ℕ`) is free. The rule: `set` pays when the term is
small and the rewrite is frequent; for big terms it is a pessimisation.

The rest of the pass was mechanical: the descents keep the pin's `hroot`/`hsplit`/`huniq` cut;
`fullC_mul_prime_eq_adjoin_insert_image` became `le_antisymm` of two named inequalities with the
walk's `p ∣ d` / `p ∤ d` cases as symmetric privates; `relfinrank_fullC_step` became `rcases a` plus
`relfinrank_fullC_zero_step` and a succ case that reads as five named bounds (`hδ`, `hδpos`,
`p ≤ …`, `≤ p`) squeezed by `relfinrank_fullC_succ_eq_of_bounds`. One `have` did not lift cleanly —
the induction-hypothesis-taking cases state `ih` as `∀ (d' : ℕ), d' < d → ∀ [NeZero d'], …`
because `jqNModC K d'` needs the instance inside the same telescope; it is defeq to
`Nat.strong_induction_on`'s hypothesis, so the proof passes `ih` unchanged.
