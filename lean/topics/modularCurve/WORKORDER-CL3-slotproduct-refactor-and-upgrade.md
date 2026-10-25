# WORKORDER-CL3 — `SlotProduct` refactored and brought up to standards

Status: **open; ready to dispatch once WORKORDER-CL1 has landed its refactor** (2026-10-25).
Dependency: `SlotProductAnyField.lean` imports this module, so CL1 must be finished (and its
worker stopped) before any edit here — otherwise its builds read a half-edited dependency.

`FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean` — the `ℚ` layer's slot
product and prime non-membership (T19), 1,457 lines, 25 declarations (3 public: the two
headlines and `card_slotFilter_eq_dedekindPsi`; 22 `private`). It holds **the two longest proofs
in the port**:

| declaration | lines | why it is here |
|---|---:|---|
| `rval_aux` | **692** | the strong induction for the slot product |
| `jqN_prime_not_mem_adjoin` | **369** | the `M`-arbitrary non-membership (calls `rval_aux` at `ζ ^ p`) |

**The two monoliths are most of this module's build cost, and the same cut has just removed most of
it in the `C` twin.** Measured: `SlotProductAnyField` was **54 s wall / 350k heartbeats** before its
split and **34–36 s / 100k** after — while its sibling `PrimePowerStepAnyField`, whose proofs were
already ≤119 lines, sits at 13–15 s / 45k for a similar line count. So here the wall time and the
heartbeat peak are legitimate secondary targets alongside readability, and the expectation is a
comparable drop (the `ℚ` proofs are the *same* development, slightly larger: 692 + 369 against
661 + 322). A regression on the A/B is a real loss, not an acceptable price for clarity.

and it is the reason both it and CL1 are slow to build: the profiler (`-Dprofiler=true`) reads
tactic 12.6 s, type checking 20.3 s — **of which one single event is 18.9 s, the final check of
the 692-line `rval_aux` term** — typeclass inference 16.4 s, import 6.7 s (≈56 s of elaboration,
`lake build` ≈60 s). The file needs more than 200k heartbeats (≈250k is clean).

## Step 0 — wire it first (the refactor must be statement-protected)

The module is **legacy**: it carries no `spec-pin:` line, so it is only in the frozen registry
(`spec/old_check_stmts.py` `PORT_FILES:3555`) and **its statements are not diffed at all** — a
refactor could silently move a headline and nothing would notice. Wire it before touching proofs.

Measured trial wire (a copy of the module with only the header lines added, run through the
checker): the four lines below read **2 ok, 0 mismatch, 1 missing, 0 own** — the missing
declaration being the port's own counting lemma.

```
spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean
spec-pin: P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean
spec-pin: Theorems/Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean
spec-pin: Theorems/Thm_ModularCurve_jqN_prime_not_mem_full.lean
```

`card_slotFilter_eq_dedekindPsi` then needs **one `own:` row** in `spec/decl_markers.tsv` (keyed
`FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean`, declaration
`ModularCurve.card_slotFilter_eq_dedekindPsi`) whose reason is: *the port's replacement for the
pin's private `slotAt`/`slots` chain — the closed-form slot count of
`logs/audit-slot-counting-mathlib.md`, which the pin proves by its 108-line CRT `slotAt_mul`; no
pin statement is being restated.* Then the module reads **2 ok / 0 mismatch / 0 missing / 1 own**.

Two headline declarations must read `ok` from then on — that is the safety net under Step 1.

## Step 1 — refactor the two monoliths (the priority)

Cut `rval_aux` (692) and `jqN_prime_not_mem_adjoin` (369) into a documented sequence of `private`
lemmas with **descriptive, rectified names and a docstring stating the mathematical statement**,
leaving each as a readable assembly (its induction, its named steps, a short final combination).
Target: **no proof body over ~200 lines**. Do not invent a different proof: the seams are the
existing `have`s and `by_cases` branches.

**Read the landed `SlotProductAnyField.lean` first** — CL1's refactor (WORKORDER-CL1) does exactly
this for the `C` twin of the same proof, and its sub-goal names transfer: the slot-root lemma, the
product/cardinality lemma, the degree computation, the `M = 1` base case, the divisibility-and-
degree squeeze. Mirror its naming where the sub-goal is the same, and keep the two layers
comparable; where the `ℚ` proof genuinely differs (`coeffEmb` composition, the `letI : Algebra`
blocks, `Hall M`), keep the difference visible rather than forcing the shape.

**A measured caution from the sibling pass** (`PrimePowerStepAnyField`, CL2): naming a *large*
subterm with `set` and rewriting with it is a pessimisation — `rw`/unification unfolds the local
definition at every occurrence and tactic time went 9.5 → 15–17 s there. Revert to the pin's literal
terms, state sub-lemmas on the API's own form rather than rewriting the definition in each use, and
A/B every split before believing it. A *small* `set` (a `ℕ`) is free.

Hard constraints: the **three public statements stay byte-identical** (the checker now diffs them);
new lemmas are `private`; no `set_option maxHeartbeats`; 0 warnings; no `sorry`; `rval_aux`'s
statement and name stay (the separation calls it); no hypothesis weakened.

## Step 2 — finish the legacy upgrade

Per `lean/topics/instructions.md`, a touched legacy module is brought up to standards. Status
measured 2026-10-25, before this order:

| criterion | status |
|---|---|
| `spec_pin` | **absent** → Step 0 |
| deletion from the old checker | listed at `spec/old_check_stmts.py:3555` → **delete that line** once the module is wired (the registry must shrink, never grow) |
| silent build | to establish: `lake env lean` on the file must print **nothing** (0 warnings) |
| no build-time blow-up | to establish after Step 1: report the module's `lake build` wall time, the profiler split, and the minimum `maxHeartbeats` that elaborates it (bisect 100k/150k/200k/250k) |
| no random tokens in names | clean (`grep` for `kw_`/`W1`/`p2m_` finds one provenance mention of `p2m_open` in a comment, which is fine) |
| `dedup.py` | **0 clusters, 0 removable** in isolation; over all 11 `FunctionFieldGeneration` modules: **3 clusters, 25 removable lines**, all `private`-vs-`private` with `SlotProductAnyField.lean` — see the residue below |
| `move_dead.py` | **0 declarations, 0 lines** (`--select dead`, dry run) |

Re-run both tools at the end and report the readings.

## Known residue, deliberately not cut (record, do not fix here)

The three cross-module clusters are the slot-value block CL1 re-declared on purpose, because
`SlotProduct`'s copy is `[Algebra ℚ K]`-bound and its `sv_eq`/`sv_top` statements name
`coeffEmb K jq`:

| cluster | lines | what |
|---|---:|---|
| `sv_inj` | 16 | `ℚ` copy vs `C` copy, both `private` |
| `TS_congr'` | 5–7 | ditto (the `ℚ` copy already `omit`s the algebra binder) |
| `sv_eq_TS` | 4–6 | ditto |

Total 25 lines, inert (`private` names do not clash across files).

### How to close the residue — measured 2026-10-25, one atomic three-file edit

The two copies are *not* interchangeable, so "delete one" does not work: the `ℚ` `sv` is
`[Algebra ℚ K]`-bound with body `qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))`, and
**`coeffEmb K jq` is not `rfl`-equal to `jqModC K`** (probed: `example : … (coeffEmb K jq) = …
(jqModC K) := rfl` fails; `coeffEmb_jq` is a propositional theorem), and the two `sv_top`s have
different statements. The plan that does work, with the probe behind each step:

1. **New home** — `Defs/TS.lean` (general field, already the `TS` home; `sv` is `TS K (a*a)
   (ζ^(b*a))` by `sv_eq_TS`): add `sv`, `sv_eq`, `sv_eq_TS`, `TS_congr'`, `sv_top`, `sv_inj` as
   **public** at the pin's `C` text, with docstrings (~45 lines). The names are kept as the pin
   has them: `sv` is the pin's abbreviation for **slot value** — `sv K ζ a b = j(ζ^{ab} q^{a²})`,
   the slot values of `base/006-the-modular-equation.md` §1–§5, and `sv_` is the usual
   prefix-by-subject lemma tag (`TS_coeff_mul`, `phiAtSeed_monic`). It is a meaningful
   abbreviation, not a generated token, so the rectification rule does not apply; the docstring
   states the expansion so that the definition carries its own gloss. Probed: the six compile in that
   context verbatim (only the `haveI` linter, which the siblings already disable). It needs **one
   new `spec-pin:` line** (the `C` slot-product `S_` file, where the pin's general-field copies
   live) and its checker reading goes 15 ok → ~21 ok.
2. **`SlotProduct.lean`** — delete its six copies (~50 lines); keep **two `private` derivations**
   for the spellings its proof cites (`sv_eq_coeffEmb`, `sv_top_coeffEmb`, ~8 lines); **two proof
   lines** change (`rw [sv_eq, coeffEmb_jq]` → `rw [sv_eq]` at `:555`; `sv_top` → the coeffEmb
   variant at `:383`). Its `rval_aux`/`jqN_prime_not_mem_adjoin` citation sites are untouched —
   they cite the lemmas by name and the general statements are strictly more general.
3. **`SlotProductAnyField.lean`** — delete its six copies (~50 lines); **no proof-site change**
   (its texts *are* the general ones) and it already imports `Defs/TS`.

Net **≈ −90 lines** and three duplicate names gone; `dedup.py` over `*FunctionFieldGeneration/*`
then reads **0 clusters**. It is **checker-invisible**: no public statement in either module
mentions `sv` (verified by `grep` over both headlines), so only the new public declarations need
wire rows.

**Cost/benefit.** It is a clarity/dedup win, **not a build-time one** (the six copies are cheap).
It is a single atomic edit across three files (half of it does not compile), it edits both
slot-product modules, and the manager performs it **after** this order lands (step 1 of it is
rehearsed already: the block inserted into `Defs/TS.lean`'s actual text compiles **silently** and
the checker reads **25 ok / 0 mismatch / 0 missing / 0 own**, the six new declarations matching the
pin's `C` file at `:679`, `:684`, `:689`, `:693`, `:719`, `:698`).

Two facts for whoever reviews that edit: `Defs/TS.lean` needs **one** new `spec-pin:` line (the `C`
slot-product `S_`), and inside `SlotProduct.lean` every citation of `sv_eq` and `sv_top` must be
retargeted at the two `coeffEmb`-flavoured privates — after the move those are the only
`coeffEmb`-spelled statements left, and the rest of that module's citations (`sv_eq_TS`, `sv_inj`,
`TS_congr'`) work unchanged because the general statements are strictly more general. Unifying them means
generalizing `sv` to `[Field K]` at `jqModC K` — the `Defs/TS.lean` precedent — and then editing
`SlotProductAnyField.lean`'s three copies too; that is a **manager-side promotion across two
modules**, not part of this order. Leave them, and say so in the module header.

## Step 3 — gates

- `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct` green, **0 warnings**,
  no `sorry`; the two headlines and `relfinrank`-free surface unchanged.
- `python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean`
  → **2 ok / 0 mismatch / 0 missing / 1 own** (the `own` row of Step 0).
- `python3 spec/check_port.py --changed --strict-markers` → still green tree-wide (this also proves
  the `PORT_FILES` deletion did not orphan anything).
- `#print axioms` on both headlines → `[propext, Classical.choice, Quot.sound]`.
- `python3 tools/deps/dedup.py --module '*FunctionFieldGeneration/*'` → the same 3 clusters (25
  lines) and nothing new; `python3 tools/deps/move_dead.py --source <file> --target /tmp/shelf.lean`
  → 0 declarations.
- `python3 tools/deps/frontier.py --ds --target ModularCurve.minpoly_jqN_map_eq_prod_slots` and
  `… jqN_prime_not_mem_full` → `needed 0` (they are ported; the refactor must not change that).
- The downstream chain still builds: `FunctionFieldGeneration/Nonmembership.lean`,
  `FunctionFieldGeneration/Capstone.lean` and `spec/ModularCurveConsumer.lean` (the consumer is not
  in any build — compile it by hand, 0 errors).

## Report

The new declaration list with line counts (old two for comparison), the wall-time and profiler
readings before/after, the minimum heartbeat cap before/after, all gates, the `PORT_FILES`
deletion, and any place where the pin's proof shape had to be reorganised. If the split does not
reduce the single big type check, say so with the numbers — the clarity win stands on its own, but
a slower module is a regression and must be reverted (`lean/tmp/` copy first).

## 4. Result (2026-10-25) — landed; the dedup residue is retired with a measured reason

**The module.** `SlotProduct.lean` 1,457 → 1,748 lines, 25 → **55 declarations** (3 public, 52
`private`), 0 warnings:

| declaration | body before | body after |
|---|---:|---:|
| `rval_aux` | 692 | **91** |
| `jqN_prime_not_mem_adjoin` | 369 | **110** |
| longest body in the file | 692 | **152** (`isRoot_map_minpoly_sv_of_descent`) |

The sub-goal names are the `C` twin's (`slotValues`/`mem_slotValues`/`card_slotValues`/
`prod_slotValues`/`nodup_slotValues`, `SlotProductAt` as a `def`, `minpoly_map_eq_prod_slots_one`,
`isRoot_map_minpoly_sv_top`/`_of_dvd`/`_of_not_dvd`/`_of_descent`, `IH'`,
`eval_map_eq_of_mem_slotValues`); the `ℚ`-only seams it needed are
`exists_algHom_adjoin_of_isRoot`, `map_mem_fieldRange`, `isRoot_phiAtSeed_slot_apply`,
`hall_prime`. The three public statements, `rval_aux`'s statement and the six `sv`-block privates
are byte-identical (diffed).

**Speed (the corrected secondary goal).** Interleaved A/B, `lake env lean -DmaxHeartbeats=400000`,
four pairs, new faster in all four: wall **41.0 → 32.1 s (−22 %)**, user CPU 46.8 → 56.6 s (the same
parallel-codegen signature as the `C` twin); `lake build` 34–39 s against the ≈60 s baseline.
Heartbeat peak **≈220k → ≈65k**. The single ~20 s type check did not shrink and is now isolated in
`finrank_adjoin_mul_dedekindPsi` (the pin's `finrank_mul_finrank`/`adjoin_adjoin_left` tower block).

**Legacy upgrade.** Wired first (4 `spec-pin:` lines + one `own:` row → 2 ok / 0 missing / 1 own),
then the `PORT_FILES` line deleted (522 → 521 exempt); tree-wide
`check_port --changed --strict-markers` reads **5,457 ok / 0 mismatch / 0 missing / 31 own**;
`#print axioms` clean on both headlines; `Nonmembership`, `Capstone` and
`spec/ModularCurveConsumer.lean` all green; `move_dead` 0; both frontier targets `needed 0`.

**The one gate that does not read as specified: `dedup` 3 clusters / 25 lines → 11 / 192.** Mirroring
the twin's API re-declares ten `private` lemmas (the eight new clusters — `exists_slot_descent_data`
40, `nodup_slotValues_qExpand` 32, `sv_inj_slot` 22, `not_isRoot_minpoly_of_prime_deg` 22,
`card_slotValues` 17, `mem_slotValues` 13, `prod_slotValues` 11, `nodup_slotValues_sv` 10 — plus the
three kept `sv`-block ones, 16/5/4). Accepted as documented residue: inlining them back would put
three bodies over 150 lines again, and the shared home needs public declarations of *port-invented*
lemmas (the pin has no declaration for `slotValues`), which a wired module cannot take.

### 4.1 The `sv`-block dedup was attempted and **retired** — it is not free

The manager performed the rehearsed move (six declarations into `Defs/TS.lean`, −6 from each module,
two `coeffEmb`-flavoured privates kept) and then **reverted it**. The reason is structural, not
effort:

- the `sv` block compiles and statement-checks fine in the home (silent, checker **25 ok / 0 own**),
  and `Defs/TS.lean` gains one wire line;
- but the **pinned ℚ headline states its product in the `coeffEmb` spelling** —
  `∏ … (X - C (if h : a = 0 then 0 else … qExpand K (a * a) (qTwist … (coeffEmb K jq))))` — and
  `sv`'s body is *definitionally* that `ite` today. Generalizing `sv` to the pin's general-field
  body (`jqModC K`) makes the headline's RHS **not** definitionally equal to `rval_aux`'s
  conclusion, because `coeffEmb K jq = jqModC K` is propositional (`coeffEmb_jq`), not `rfl`
  (probed). Consequences measured: `rval_aux`/the headline needs a `Polynomial.map`/`Finset.prod`
  conversion step, and the declaration that closes at **≤70k heartbeats today times out at 400k**;
  at 4,000,000 it surfaces as a genuine `Type mismatch` at the headline's proof term.
- So the 25-line duplication is the **price of keeping the ℚ proof definitional**. It is `private`
  in both modules, costs nothing but text, and is now recorded as irreducible at this layer. The
  eight API clusters are a separate question (their statements are generic over
  `F : ℕ → ℕ → LaurentSeries K` and mention neither `Algebra ℚ K` nor `coeffEmb`); sharing them
  needs a home for port-invented lemmas and, for `card_slotValues`, the counting export's core — a
  decision for a future pass, not a repair.

### 4.2 The API half *was* shared — new module `FunctionFieldGeneration/SlotValues.lean`

The eight API clusters were a different matter: their statements are generic over
`F : ℕ → ℕ → LaurentSeries K` and mention neither `Algebra ℚ K` nor `coeffEmb`, so they cross the
two `sv` spellings freely. They now have **one home**, `FunctionFieldGeneration/SlotValues.lean`
(198 lines, 7 declarations): `slotValues` (def), `mem_slotValues`, `card_slotValues`,
`prod_slotValues`, `nodup_slotValues`, `exists_slot_descent_data`,
`not_isRoot_minpoly_of_prime_deg`. Both slot-product modules import it and their copies are gone
(`SlotProduct` 1,748 → 1,609 lines, 55 → 48 declarations; `SlotProductAnyField` 1,512 → 1,375,
43 → 36).

Two statement adaptations, both to keep the module **upstream** of the counting core:

* `card_slotValues` takes the slot-count identity as a hypothesis `hcount`; each module passes its
  own `card_slotFilter_eq_dedekindPsi M hM0` at its three call sites. So the ψ count keeps one home
  (`SlotProduct.lean`, where the arithmetic core lives) and `SlotValues.lean` stays independent
  of it.
* `nodup_slotValues` already took the distinguishability of slot parameters as a hypothesis; the
  `sv`-side discharge (`sv_inj_slot`) stays with `sv` in each module.

**It is deliberately tier 3 — no wire, no markers.** Every declaration is the port's own (the pin
has no counterpart to diff), so a `spec-pin:` line plus seven `own:` rows would record "ours" seven
times and diff nothing; the first pass did exactly that and it was removed. The module is registered
instead: `spec/unwired_register.py` lists its seven declarations as *"the port's own, no pin
source. Imported by 2 port module(s)"*, and `--check` keeps that fresh. The checker now reports the
module as `no spec-pin: directive — not wired (tier 3)` and the tree-wide reading is unchanged
(5,457 ok / 0 mismatch / 0 missing / 31 own); what pins the statements is **use** — both slot-product
modules cite every one of them at specific arguments, so any drift breaks their builds. Wire it only
if a pin-derived statement is ever added here.

**Residue after both passes: `dedup` 11 clusters / 192 lines → 6 / 89**, and the six are the
`sv`-instantiation layer, which cannot cross the two spellings for the reason of §4.1:
`nodup_slotValues_qExpand` 32, `sv_inj_slot` 22, `sv_inj` 16, `nodup_slotValues_sv` 10,
`TS_congr'` 5, `sv_eq_TS` 4. Four are `sv` re-statements; the other two are three-line corollaries
of the shared `nodup_slotValues` whose value is the *documentation* of the instantiation, and are
kept deliberately.

Gates after both passes: both modules and the FFG chain (`Nonmembership`, `Capstone`) build with
**0 warnings**; checker on the three modules **4 ok / 0 mismatch / 0 missing / 8 own**; tree-wide
**5,457 ok / 0 mismatch / 0 missing / 38 own**, exit 0 (245 modules); `spec/ModularCurveConsumer.lean`
**0 errors**; `move_dead` 0 on all three; all four frontier targets `needed 0`; the four
headlines' axioms `[propext, Classical.choice, Quot.sound]`.
