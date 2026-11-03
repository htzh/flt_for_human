# Topic: the FFG capstone refactor and the `spec-pin` upgrade

**Status: in progress (2026-11-03).** Waves 1–3 are landed and green: the
`Inputs` bundle is gone, `hall_all` is private and FLT's, the capstone is in the
new `Capstone.lean`, the tail is in `ModularPolynomialExistence.lean`, and every
FFG module except `SlotValues` is `spec-pin:`-wired. Waves 4–6 (consumers and
presentation) are deliberately held pending the build-time check; see §10.

**Naming, read this first.** The two module names swap roles, so the plan is
explicit about "old" and "new":

| role | before the refactor | after the refactor |
|---|---|---|
| the capstone | `Spine.lean` (the conditional spine) plus the capstone half of `Capstone.lean` | **`Capstone.lean`** — the renamed `Spine.lean`, now unconditional |
| the interface tail | the tail half of `Capstone.lean` | **`ModularPolynomialExistence.lean`** — the tail only |

"Old `Capstone.lean`" always means the pre-refactor file; "new `Capstone.lean`"
always means the renamed `Spine.lean`. The old name is reused because the role it
names is finally the role the file has.

**Audience.** A fresh session executing the refactor, or a reviewer checking that
the plan is complete. Read [PORTING-FFG.md](../PORTING-FFG.md) §7.8 and
[ffg-retrospective.md](../ffg-retrospective.md) §1–§2 first: they record what was
built and why. This plan supersedes their description of `Inputs`, `hall_all` and
the old `Capstone.lean` layout; it does not rewrite the historical record.

**Why now.** `Inputs` was one of the first porting experiments. It was useful
while T15–T19 were outstanding — it made the remaining debt a seven-field
structure — but every field is now a proved theorem, so the bundle only adds an
indirection, a public structure with no mathematical content, and a second
statement of each theorem. FLT's proof never had it: the pin's

```lean
private theorem hall_all : ∀ N : ℕ, N ≠ 0 → Hall N
```

calls the seven statements directly
(`P2M/Sol/S_ModularCurve_functionFieldGeneration.lean:614–700` at `aa2d8b3`).
The original development was fine; this restores it.

**The changes, in one list.**

1. Rename `Spine.lean` to `Capstone.lean`, delete `Inputs`, de-parameterize its
   five private helpers, make `hall_all` private, and keep the unconditional
   theorem plus the three corollaries as its public surface. It imports the five
   modules that own the seven statements.
2. Move the tail half of the old `Capstone.lean` to
   `ModularPolynomialExistence.lean` and delete the old file. The tail keeps only
   the integrality statement and the irreducible datum.
3. Add `spec-pin:` wires to the eight unwired FFG modules; delete them from the
   frozen checker's `PORT_FILES`; leave `SlotValues` tier 3 with its recorded
   reason.
4. Update the Lean/`spec/` consumers. This is cheaper than it looks: every file
   that imported the old `Capstone.lean` for the capstone declarations imports the
   new `Capstone.lean` with the same module path, so only the tail consumers move
   to `ModularPolynomialExistence.lean`.
5. Retarget the presentation to `Capstone` and delete its `Inputs`/assembly and
   tail sections. No second presentation is needed: the old capstone is gone, and
   the tail is not part of that narrative.

---

## 1. The diagnosis, precisely

The line numbers in the table are the pre-refactor ones. `Spine.lean` is renamed
to `Capstone.lean`; its content and line numbers are otherwise unchanged.

| symptom | where | why it is a problem |
|---|---|---|
| `Inputs` is ours | `Spine.lean:112–172` | No pin counterpart. Each field duplicates a theorem already public in `Descent`/`DegreeStep`/`Nonmembership`/`Generation`/`SlotProduct`; the capstone has to project the fields back out. |
| `hall_all` is public | `Spine.lean:311` | It was made public only so the old `Capstone.lean` could prove the three corollaries. The pin's is `private`; nothing outside the capstone should name it. |
| `functionFieldGeneration_of` is ours | `Spine.lean:392` | A packaging theorem whose only purpose was the `Inputs` indirection. Nothing outside the capstone/tail split uses it. |
| the old `Capstone.lean` is two modules | old `Capstone.lean:46–92` and `94–290` | The first half is the FFG capstone (assembly, theorem, corollaries); the second is an interface tail for other modules (`exists_monic_evalAtJ_jqN_eq_zero`, the irreducible datum). The file name names neither role. |
| the eight FFG modules are not self-checked | `Target`, `Collapse`, `Spine`, `Descent`, `DegreeStep`, `Nonmembership`, `Generation`, `Capstone` | They are still owned by the frozen `spec/old_check_stmts.py` lists; they carry no `spec-pin:` header. The current standard is the per-module wire (`lean/topics/instructions.md`, `porting-playbook.md` §4). |

The seven significant statements themselves are fine and stay exactly as they
are. In particular the two that take `Hall M →` (`jqN_prime_not_mem_full`,
`jqN_pow_not_mem_adjoin_full`) are definitionally the pin's explicit
`hall`-conjunction statements, because `Hall` is an `abbrev` for that conjunction;
`spec/check_port.py` already reports them identical to their wrappers.

---

## 2. Target shape

**Before** (`Spine` is upstream; the old `Capstone.lean` is the top):

```text
Target ── Collapse ──┐
                     ├── Spine  (Inputs, hall_all, functionFieldGeneration_of)
Descent ─────────────┤
DegreeStep ──────────┤
Nonmembership ───────┤
Generation ──────────┤
SlotProduct ─────────┘
                     └── Capstone (old)  (inputs, functionFieldGeneration,
                                         corollaries, interface tail)
```

**After** (`Capstone.lean` is the capstone, downstream of the seven; the tail is
separate):

```text
Target ── Collapse ──┐
Descent ─────────────┤
DegreeStep ──────────┤
Nonmembership ───────┤
Generation ──────────┤
SlotProduct ─────────┘
                     └── Capstone  (private hall_all,
                          public functionFieldGeneration + 3 corollaries)
                                 └── ModularPolynomialExistence
                                     (integrality + irreducible datum)
```

This is FLT's own shape: the seven statements are available before `hall_all`, and
`hall_all` is the last step before the headline. The one structural cost is that
the capstone module moves from the top of the dependency order to the bottom; see
§10.

---

## 3. `Capstone.lean` (the renamed `Spine.lean`) — the exact edit

### 3.1 Imports

Add the five modules that own the seven statements. `Descent` supplies two,
`DegreeStep` one, `Nonmembership` one, `Generation` one, `SlotProduct` two.
`Collapse`, `Defs.TS`, `Defs.Cyclotomic` and the three mathlib imports stay.

```lean
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent
import FLTForHuman.ModularCurve.FunctionFieldGeneration.DegreeStep
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Generation
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Nonmembership
import FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProduct
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.Defs.Cyclotomic
```

No cycle: none of those five imports `Spine` today (checked 2026-11-03).

### 3.2 Delete `Inputs`

Delete the whole block from the section header `/-! ## Inputs: the significant
statements` through the end of `structure Inputs where` (the pre-refactor
`Spine.lean:102–172`, now the same lines of `Capstone.lean`). This is the only
removal; the seven statements themselves are imported, not restated.

### 3.3 De-parameterize the five private helpers

Delete the `(h : Inputs) ` binder from the signatures and replace each field
projection with the theorem name. The table is exhaustive; a `grep -n 'Inputs'`
after the edit must be empty.

| line (pre-refactor `Spine.lean`) | declaration | replacements in its body |
|---|---|---|
| 192 | `full_le_adjoin_chain` | `h.full_eq_adjoin_full_div_prime` → `full_eq_adjoin_full_div_prime` |
| 215 | `jqN_pow_not_mem_full` | `h.jqN_prime_not_mem_full` → `jqN_prime_not_mem_full`; `h.jqN_pow_not_mem_adjoin_full` → `jqN_pow_not_mem_adjoin_full`; `full_le_adjoin_chain h M p` → `full_le_adjoin_chain M p` |
| 231 | `root_shape` | `h.minpoly_jqN_map_eq_prod_slots` → `minpoly_jqN_map_eq_prod_slots` |
| 258 | `htw_of` | `root_shape h M p` → `root_shape M p` |
| 281 | `hsp_of` | `root_shape h M p` → `root_shape M p` |

The signatures lose `(h : Inputs)`; the call sites lose `h`. This is exactly the
pin's helper block (`S_ModularCurve_functionFieldGeneration.lean:501–605`).

### 3.4 Make `hall_all` private

```lean
/-- **The strong induction of math/010 §7.** From the seven significant
statements, `Tight` and `Gen` hold at every divisor of every `N ≠ 0`. It is the
source of the capstone's corollary layer (`modularFunctionField_eq_full`,
`finrank_adjoin_jqN_eq_dedekindPsi`, `relfinrank_full_eq_dedekindPsi`), so it is
kept in this module; `functionFieldGeneration` consumes it just below. -/
private theorem hall_all : ∀ N : ℕ, N ≠ 0 → Hall N := by
  ...
```

Inside the body, replace the three field projections:

| current | new |
|---|---|
| `h.modularFunctionField_eq_full_of d` | `modularFunctionField_eq_full_of d` |
| `h.jqN_div_mem_modularFunctionField M p ...` | `jqN_div_mem_modularFunctionField M p ...` |
| `h.relfinrank_full_eq_mul M p a ...` | `relfinrank_full_eq_mul M p a ...` |
| `jqN_pow_not_mem_full h M p hpM hallM a` | `jqN_pow_not_mem_full M p hpM hallM a` |

Nothing else changes: the induction, the `d.minFac` decomposition, the tower law,
the `ψ` arithmetic and the two `htw_of`/`hsp_of` lambdas are the pin's, and the
scratch refactor of §3.6 compiled unchanged.

### 3.5 Replace `functionFieldGeneration_of` with the public surface

Delete `theorem functionFieldGeneration_of (h : Inputs) ...` (pre-refactor lines
392–393). Add the four declarations moved verbatim from the old
`Capstone.lean:63–92`:

```lean
theorem functionFieldGeneration (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  (functionFieldGeneration_iff_full_eq N).mpr (hall_all N (NeZero.ne N) N dvd_rfl).2.symm

theorem modularFunctionField_eq_full (N : ℕ) [NeZero N] :
    modularFunctionField N = modularFunctionFieldFull N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).2

theorem finrank_adjoin_jqN_eq_dedekindPsi (N : ℕ) [NeZero N] :
    Module.finrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
        ({jqN N} : Set (LaurentSeries ℚ))) = dedekindPsi N :=
  (hall_all N (NeZero.ne N) N dvd_rfl).1

theorem relfinrank_full_eq_dedekindPsi (N : ℕ) [NeZero N] :
    IntermediateField.relfinrank (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ)))
      (modularFunctionFieldFull N) = dedekindPsi N := by
  rw [← modularFunctionField_eq_full N, relfinrank_modularFunctionField N]
  exact finrank_adjoin_jqN_eq_dedekindPsi N
```

Their docstrings are the pin's `Theorems/` wrappers' one-liners, as in the old
`Capstone.lean` today.

### 3.6 The header

Rewrite the leading block. It should say, in this order:

1. the subject: the unconditional capstone, `hall_all` plus the two invariants;
2. FLT provenance, pinned `aa2d8b3`, with the line ranges already in the current
   header (106–109, 199–240, 413–435, 436–466, 467–613, 614–700);
3. that `hall_all` is private and why (it is an internal induction; the public
   surface is the four declarations below);
4. the `spec-pin:` wire (see §5);
5. what is imported, without cross-referencing port modules by file name where a
   phrase will do (the current standard discourages gratuitous module cross-refs).

Section heading `/-! ## The strong induction and the conditional capstone -/`
becomes `/-! ## The strong induction and the capstone -/`.

### 3.7 Validated on a scratch copy

The exact edit above was applied to a copy at `lean/tmp/CapstoneRefactor.lean`
(untracked, ephemeral) and checked on 2026-11-03:

```text
lake env lean tmp/CapstoneRefactor.lean       exit 0, 30–43 s, no warnings
spec/check_port.py tmp/CapstoneRefactor.lean  4 ok, 0 mismatch, 0 missing, 0 own
```

`lean/tmp` is not persistent; the scratch files are evidence, not deliverables.

---

## 4. The tail module — rename and contents

### 4.1 The cut

The old `Capstone.lean` currently holds two independent things:

* **capstone** (`46–92`): `inputs`, `functionFieldGeneration`, the three
  corollaries. These move to the new `Capstone.lean` (the renamed `Spine`) in
  §3.5.
* **interface tail** (`94–290`): `exists_monic_evalAtJ_jqN_eq_zero`,
  `exists_phiIrreducible_of_finrank_eq`, `exists_phiIrreducible`,
  `nonempty_modularPolynomialData`, plus the three private evaluation bridges
  `coe_evalAtJGen`, `aeval_map_intCast`, `evalAtJ_C`.

After the move, the old `Capstone.lean` path is gone; the tail becomes
`ModularPolynomialExistence.lean`, and the name `Capstone.lean` is taken by the
refactored `Spine.lean`.

**The name swap is atomic.** Use `git mv` twice, in this order: old
`Capstone.lean` → `ModularPolynomialExistence.lean` (then drop the capstone half
from the moved file), then `Spine.lean` → `Capstone.lean` (then apply §3). The old
`Capstone.lean` must be freed before `Spine.lean` can take the name, so the move,
the content cut and the second rename are one edit with no build in between. The
first green state is after all three; §12 waves 1–2 are the two halves of that
single change. Renaming in this order makes git history follow the capstone
(`Spine` → `Capstone`) and the tail (`Capstone` → `ModularPolynomialExistence`),
which is what each file's surviving content is.

### 4.2 Recommended name: `ModularPolynomialExistence.lean`

Path:
`FLTForHuman/ModularCurve/FunctionFieldGeneration/ModularPolynomialExistence.lean`.

Why: the module's mathematical product is the existence of the modular-polynomial
datum — the monic annihilator (integrality) is the input, and
`exists_phiIrreducible` / `nonempty_modularPolynomialData` are the output. It sits
naturally beside `ModularPolynomialProperties`, `ModularPolynomialUniqueness`,
`ModularPolynomialIrreducible`. Alternatives considered:

* `Interface.lean` — rejected: `TOPIC-interface-tier.md` already rejected a
  dedicated interface module because it separates lemmas from the objects they
  concern.
* `Tail.lean` / `CapstoneTail.lean` — taxonomy, not a mathematical role; the
  current standard says a module is named for its role.
* `ModularPolynomialDatum.lean` — accurate but easy to confuse with
  `Defs/Polynomial.lean`, which defines `ModularPolynomialData`.

If the user prefers another name, only the path/import/module strings below
change; the content and wire do not.

### 4.3 Contents and imports

Take the old `Capstone.lean` from
`/-! ## The interface tail: the monic integrality input` through `end` and keep
it verbatim. New header:

* subject: the modular-polynomial interface tail (integrality, irreducible datum);
* provenance: the four `Theorems/` wrappers and their `P2M/Sol/` copies at
  `aa2d8b3`;
* the `spec-pin:` wire (§5);
* assumptions: the capstone's degree count from `Capstone`, `phiAtSeed` from
  `Defs/PhiAtSlot`, `ModularPolynomialData`/`PhiIrreducible` from
  `Defs/Polynomial`.

Imports shrink to what the tail uses directly:

```lean
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.ModularPolynomialProperties
import Mathlib.Data.Nat.Factorization.Induction
```

`Descent`, `DegreeStep`, `Nonmembership`, `Generation`, `SlotProduct` are no
longer imported directly; they come through `Capstone`. `Mathlib.Data.Nat.Factorization.Induction`
is still needed for `induction_on_primes` in the integrality proof. Keep
`set_option autoImplicit false` and `set_option linter.style.haveILetI false`.

The only cross-module name the tail uses from the capstone is
`finrank_adjoin_jqN_eq_dedekindPsi` (in `exists_phiIrreducible`); it is now in
`Capstone`, which the tail imports. `grep -n 'functionFieldGeneration\|modularFunctionField_eq_full\|relfinrank_full_eq_dedekindPsi\|Inputs\|hall_all'`
on the new module must be empty except for prose.

### 4.4 Validated on a scratch copy

`lean/tmp/TailRefactor.lean` (the same cut) was checked on 2026-11-03:

```text
spec/check_port.py tmp/TailRefactor.lean   4 ok, 0 mismatch, 0 missing, 0 own
```

Its compile is gated on the new `Capstone` (the scratch imported the old `Spine`),
but the change is subtractive: the kept code is byte-identical to the old
`Capstone.lean` 94–290, and the one moved name is now in the new `Capstone`.

---

## 5. The `spec-pin` upgrade

### 5.1 What the current standard requires

From `lean/topics/instructions.md` §"Legacy Modules" and
`porting-playbook.md` §4:

* one `spec-pin: <pin file>` line per pin source, in the **leading** `/- … -/`
  block (never a `--` comment; the checker reads the leading block);
* list the `Theorems/` wrapper whose statement text the port transcribes, not the
  `S_` file;
* every public declaration either diffs to a pin statement or carries a recorded
  exception in `spec/decl_markers.tsv`; private declarations are skipped;
* delete the module from the frozen `spec/old_check_stmts.py` `PORT_FILES` list;
* run the checker to `0 mismatch / 0 missing`, keep the build silent, and run
  `dedup.py` / `move_dead.py` / `unwired_register.py --check`.

The `spec-pin:` line has two spaces of indentation in the existing FFG modules;
either zero or two is accepted (`^\s*spec-pin:`), but use two for consistency
with `SlotProduct.lean`.

### 5.2 The wires, with measured results

These are the minimal wire sets; each was tested on a scratch copy on 2026-11-03
with `spec/check_port.py --force`. The `ok` count is the number of public
declarations diffed; all are `0 mismatch / 0 missing / 0 own`. In the table, `…`
stands for `Theorems/Thm_ModularCurve_`.

| module | `spec-pin:` files | expected |
|---|---|---|
| `Target.lean` | `Definitions/Def_ModularCurve_X0.lean` | 2 ok |
| `Collapse.lean` | `Theorems/Thm_ModularCurve_functionFieldGeneration_iff_full_eq.lean` | 1 ok |
| `Capstone.lean` (new; the renamed `Spine`) | `Theorems/Thm_ModularCurve_functionFieldGeneration.lean`; `…_modularFunctionField_eq_full.lean`; `…_finrank_adjoin_jqN_eq_dedekindPsi.lean`; `…_relfinrank_full_eq_dedekindPsi.lean` | 4 ok |
| `Descent.lean` | `Theorems/Thm_ModularCurve_modularFunctionField_eq_full_of.lean`; `Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean` | 2 ok |
| `DegreeStep.lean` | `Theorems/Thm_ModularCurve_finrank_adjoin_jqN_prime_of_not_mem.lean`; `…_finrank_adjoin_jqN_pow_succ_of_not_mem.lean`; `…_relfinrank_full_eq_mul.lean` | 3 ok |
| `Nonmembership.lean` | `Theorems/Thm_ModularCurve_jqN_pow_not_mem_adjoin_full.lean`; `Theorems/Thm_ModularCurve_jqN_prime_not_mem_adjoin.lean` | 2 ok |
| `Generation.lean` | `Theorems/Thm_ModularCurve_full_eq_adjoin_full_div_prime.lean` | 1 ok |
| `ModularPolynomialExistence.lean` (new) | `Theorems/Thm_ModularCurve_exists_monic_evalAtJ_jqN_eq_zero.lean`; `…_exists_phiIrreducible_of_finrank_eq.lean`; `…_exists_phiIrreducible.lean`; `…_nonempty_modularPolynomialData.lean` | 4 ok |
| `MffCMulPrime.lean` | already wired | 2 ok |
| `PrimePowerStepAnyField.lean` | already wired | 50 ok |
| `SlotProduct.lean` | already wired | 2 ok + 1 own (`card_slotFilter_eq_dedekindPsi`) |
| `SlotProductAnyField.lean` | already wired | 2 ok |
| `SlotValues.lean` | none — deliberate tier 3 | n/a |

No new `spec/decl_markers.tsv` row is needed. The one existing FFG row
(`SlotProduct.card_slotFilter_eq_dedekindPsi`, `own:`) stays. The four modules
already on `spec-pin:` (`MffCMulPrime`, `PrimePowerStepAnyField`, `SlotProduct`,
`SlotProductAnyField`) carry no legacy `-- pin:`/`-- own:` markers and report
0 mismatch / 0 missing today, so they need only the re-check in §9, not a header
edit.

`Capstone.lean`'s private `hall_all` is not diffed; the pin's is private too. The
frontier name scan still sees the port's declaration, so no work is lost.

### 5.3 `SlotValues.lean` stays tier 3

**What tier 3 means.** It is the register's name
(`spec/unwired_register.py`) for a module that has neither a `spec-pin:` header
nor an entry in the frozen `PORT_FILES`, so `spec/check_port.py` does not diff its
public declarations against the pin. "Tier 3" is about *statement verification*,
not proof checking: the module is in the library, `lake build` elaborates and
checks every proof, and it is imported by `SlotProduct.lean` and
`SlotProductAnyField.lean`. What is missing is only the mechanical diff of each
statement's text against a pinned FLT statement. Keeping `SlotValues` at tier 3
means leaving it in that state rather than inventing a wire.

Its header documents why: every declaration is the port's own (the pin has no
counterpart to diff against; they are named sub-goals of the monolithic
`rval_aux`), so a wire plus seven `own:` rows would record "ours" seven times and
diff nothing. It is registered by `spec/unwired_register.py` instead. This is the
one literal exception to "all FFG modules"; if the user wants it wired anyway,
add `spec-pin: P2M/Sol/S_ModularCurve_minpoly_jqN_map_eq_prod_slots.lean` and
seven `own:` rows, but that is verification theatre, not verification. The
alternative that would actually buy a diff is to restate the seven declarations
as the pin's `rval_aux` sub-goals — a different, much larger refactor, and not
wanted here.

### 5.4 Delete from the old checker

In `spec/old_check_stmts.py`:

* remove these eight pre-refactor entries from `PORT_FILES`:
  `FunctionFieldGeneration/{Target,Collapse,Spine,Descent,DegreeStep,Nonmembership,Generation,Capstone}.lean`;
  the new `Capstone.lean` is the renamed `Spine.lean`, so it has no separate entry,
  and the tail module was never listed;
* remove the FFG-specific `OWN_PROOFS` entries `"Inputs"`,
  `"functionFieldGeneration_of"`, `"hall_all"`, `"inputs"`, and rewrite the comment
  block above them. Keep `"Tight"`, `"Gen"`, `"Hall"` and `"gen_prime"`: they are
  still public in `Defs/Fields.lean`, which remains listed. `tight_one`/`gen_one`
  are not `OWN_PROOFS` entries — they verify through the `S_` dotted fallback —
  so there is nothing to remove for them;
* leave `SOURCES` alone. Those pin files are read by other listed modules; the
  entries are harmless and removing them is a separate audit.

The old checker ignores `spec-pin:` lines, so the order of §5.2 and §5.4 does not
matter for correctness; do both in the same change so a module is never in the
"neither checker" tier.

### 5.5 Other spec tooling

* `python3 spec/check_port.py --force <module>` after each edit; `--changed` before
  handing over.
* `python3 spec/unwired_register.py --check` (the register is git-ignored; rebuild
  it with `--rebuild` if the import graph changed).
* `cd tools/deps && python3 dedup.py --module FLTForHuman/ModularCurve/FunctionFieldGeneration --no-json`
  — the known cross-module duplicates (`sv`, `sv_inj`, `sv_inj_slot`,
  `nodup_slotValues_*`, `TS_congr'`, `sv_eq_TS` between `SlotProduct` and
  `SlotProductAnyField`) are the deliberate `C`-layer residue documented in the
  latter's header. Do not "fix" them in this refactor.
* `python3 move_dead.py --source <module> --target <shelf> --dry-run` only if a
  declaration becomes unreachable. Expected: none. `functionFieldGeneration_of`
  is deleted, not shelved: it is a port device, not mathematics.
* `python3 tools/check_math_delimiters.py lean/topics/functionFieldGeneration/TOPIC-ffg-refactor.md`
  if the plan ends up containing math; this one uses no math delimiters at all.

---

## 6. Consumers of the moved/renamed declarations

### 6.1 Lean modules

Update the import to the module that actually declares the name used. Where a
module uses both halves, import both. The capstone import path is unchanged for
the five capstone consumers (the new `Capstone.lean` took the old name); only the
tail consumers move to `ModularPolynomialExistence.lean`. In the two special
consumers, the current `…Spine` import becomes `…Capstone` and the current
`…Capstone` import becomes `…ModularPolynomialExistence`:
`spec/ModularCurveConsumer.lean` has both, and `spec/ModularCurveReady2Consumer`
has only the tail one.

| file | uses | new import |
|---|---|---|
| `FLTForHuman/ModularCurve/HeckeCommuteBar.lean` | `functionFieldGeneration` | `…FunctionFieldGeneration.Capstone` |
| `FLTForHuman/ModularCurve/Degree/Relfinrank.lean` | `finrank_adjoin_jqN_eq_dedekindPsi`, `modularFunctionField_eq_full` | `…Capstone` |
| `FLTForHuman/ModularCurve/ModularPolynomialLeadingCoeff.lean` | `finrank_adjoin_jqN_eq_dedekindPsi`, `modularFunctionField_eq_full` | `…Capstone` |
| `FLTForHuman/ModularCurve/ModularPolynomialUniquenessIrreducible.lean` | `finrank_adjoin_jqN_eq_dedekindPsi` | `…Capstone` |
| `FLTForHuman/ModularCurve/X1/FunctionFieldInclusion.lean` | `functionFieldGeneration` | `…Capstone` |
| `FLTForHuman/ModularCurve/Degree/FinrankAdjoinJqNModC.lean` | `exists_phiIrreducible` | `…ModularPolynomialExistence` |
| `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` | `nonempty_modularPolynomialData` | `…ModularPolynomialExistence` |
| `spec/ModularCurveReady2Consumer.lean` | `nonempty_modularPolynomialData` | `…ModularPolynomialExistence` |
| `spec/ModularCurveConsumer.lean` | both halves | `…Capstone` and `…ModularPolynomialExistence` |

Also update the header prose in these files that names the old
`FunctionFieldGeneration/Capstone.lean` (at least the four files in the table whose
headers mention it), and the `exists_phiIrreducible` line in
`Degree/FinrankAdjoinJqNModC.lean:60`. Keep edits to comments local: do not
rewrite unrelated headers, and do not touch `Defs/Fields.lean` /
`NumberTheory/DedekindPsi.lean` just to fix a stale mention of `Spine`/`Inputs` —
that forces a rebuild of their whole dependent cone for no mathematical change.

### 6.2 `spec/ModularCurveConsumer.lean`

This is the one substantive consumer edit. It imports both modules, and its
Zones M–Q construct partially discharged `Inputs` values with `sorry` fields to
show the debt falling. That device is what is being removed. Required changes:

* remove `example (h : Inputs) (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  functionFieldGeneration_of h N` in Zone B;
* remove the five `example : ModularCurve.Inputs := { … }` blocks in Zones M, N,
  O, P and Q (the `Inputs` literals are the only code `sorry`s in the file; the
  Zone Q literal is the total assembly and has no `sorry`);
* remove `#check @ModularCurve.inputs`;
* keep every `#check @ModularCurve.<seven theorems>`: those remain the API wires,
  and they now test the theorems the capstone calls directly;
* rewrite the Zone B, M, N, O, P, Q and R prose to say that the seven statements
  are consumed directly by `hall_all` (private) and that the debt counter is
  history; in particular the final "deliberate `sorry`s" paragraph becomes "no
  `sorry` in this file";
* update the import comment and the old `Capstone.lean` mentions in Zones A/R and
  the trailing notes: the capstone half now points at the new `Capstone.lean`, the
  tail half at `ModularPolynomialExistence.lean`. The consumer currently imports
  both `…Spine` and the old `…Capstone`; the first becomes the new `…Capstone`, the
  second becomes `…ModularPolynomialExistence`.

Expected after the edit: `lake env lean spec/ModularCurveConsumer.lean` reports
**0 errors** and the file contains no `:= sorry`. This is the consumer metric the
effort is judged on; do not hand over with a nonzero count.

### 6.3 `spec/ModularCurveReady2Consumer.lean`

Import update only (table above); its prose at lines 14/67/88/92 names
`nonempty_modularPolynomialData`, which is unchanged, so only the module path in
the import needs to move.

---

## 7. The presentation

`presentation/function-field-generation/capstone.json` is the tracked source; the
generated `lean/presentation/FunctionFieldGenerationCapstone.lean` is git-ignored.
The JSON currently presents both halves of the old `Capstone.lean`, including
`Inputs`, `inputs`, `functionFieldGeneration_of`, and the interface tail
(sections D/E).

**The presentation does not need to split.** Its subject is the capstone, and the
capstone is now `Capstone`. The right edit is to retarget the one JSON to `Capstone`,
remove the `Inputs`/assembly material, and remove the tail sections D/E: the old
capstone module is gone, and the tail is not part of the capstone's mathematical
narrative. `hall_all` stays in the sheet as a `private` declaration with its
proof, so the original induction is still exhibited.

The only reason a split was on the table is the presentation format's one-module
rule: a sheet has one `worksheet.import`, and the dependency now runs
tail → Capstone, so a sheet importing `Capstone` cannot name the tail declarations. If
we later want a human-readable account of the tail, it has to be a second JSON
(or a hub import, which is a hack). That is an optional follow-up, not part of
this refactor. Section 7.2 records it as deferred.

### 7.1 `capstone.json` → the new `Capstone.lean`

The three path strings — `module`, `presentation_of`/`source.port_file`, and
`worksheet.import` — are already
`FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone` and do **not** change:
the file at that path is now the refactored former `Spine`, and the old content
of `Capstone.lean` has moved to the tail module. What changes is the content:

* `source.flt_files` → the four capstone `Theorems/` wrappers plus
  `P2M/Sol/S_ModularCurve_functionFieldGeneration.lean`; drop the four tail
  wrappers;
* `worksheet.reads`, `worksheet.pin`, `worksheet.title/tagline/subject` → the
  capstone, not the assembly/tail;
* delete the `inputs` definition (JSON `definitions`) and the `inputs`
  declaration (JSON `declarations`);
* delete the `ffg_of` premise (`functionFieldGeneration_of`);
* move `hall_all` from `premises` to `declarations`, with
  `"private": true`, `"lean": "private theorem hall_all : ∀ N : ℕ, N ≠ 0 → Hall N"`,
  and
  `"lean_goal": "(∀ N : ℕ, N ≠ 0 → Hall N) : Prop"` (the renderer emits
  `#check ((∀ N : ℕ, N ≠ 0 → Hall N) : Prop)`);
* give `hall_all` the proof narrative. Reuse the old `inputs` proof's seven
  field steps as the opening block ("the seven significant statements are
  available"), then add the induction steps:

  1. strong induction on `N`; at a level `d`, the proper-divisor case is the
     induction hypothesis;
  2. `d = 1`: `tight_one` and `gen_one`;
  3. `Gen d` from `modularFunctionField_eq_full_of`, the one-prime step
     `jqN_div_mem_modularFunctionField` with the slot hypotheses discharged by
     `htw_of`/`hsp_of` (which use the slot product and the cyclotomic root);
  4. `Tight d` from `d = M · p^(a+1)`, `relfinrank_full_eq_mul`,
     `full_eq_adjoin_full_div_prime`, `jqN_pow_not_mem_adjoin_full`, the tower
     law, and `dedekindPsi_mul_prime_{dvd,not_dvd}`;
  5. close: `Hall d`.

  This is the pin's proof and the mathematics already in math/010 §7; the point
  of the entry is to exhibit it even though the Lean name is private.
* rewire the four public declarations' proof steps: replace
  `{"kind":"premise","ref":"hall_all"}` with
  `{"kind":"declaration","ref":"hall_all"}`, remove the
  `{"kind":"declaration","ref":"inputs"}` cites, and remove `ffg_of` from
  `functionFieldGeneration`'s step s3. Update the regeneration notes that say
  "`functionFieldGeneration_of inputs N`" to the direct composition
  `(functionFieldGeneration_iff_full_eq N).mpr (hall_all N (NeZero.ne N) N dvd_rfl).2.symm`.
* keep the seven port premises (`full_eq_adjoin`, `prime_not_mem`, `pow_not_mem`,
  `slot_product`, `gen_reduction`, `one_prime_descent`, `degree_step`) — they are
  cited by the new `hall_all` proof steps, so they stay in the reference zone.
  Add `dedekindPsi_mul_prime_not_dvd` and `dedekindPsi_mul_prime_dvd` (public in
  `NumberTheory/DedekindPsi.lean`) as port premises if the `Tight` step cites
  them explicitly; the old `inputs` proof only cited `dedekindPsi_prime`, which
  is not enough to exhibit the `ψ` arithmetic faithfully;
* update the `file`/`line` fields of every entry that pointed at
  `Capstone.lean`/`ModularPolynomialExistence.lean` to the post-refactor locations (grep the final
  files; do not guess).

The renderer already supports private declarations (`presentation/render.py:436`),
so no tooling change is needed.

### 7.2 Delete the tail sections from `capstone.json`

Remove sections D and E (integrality and the irreducible datum), together with
the definitions and premises cited only by them. This is the bulk of the JSON
deletion and is mechanical: the renderer errors on an uncited premise or an
unreachable definition, so the validation tells you what is left over.

The four tail declarations are not lost from the port — they are in
`ModularPolynomialExistence.lean` and checked there — they are simply not part of
the capstone presentation. A future tail presentation is out of scope here; if
someone wants one, the recipe is: copy the deleted D/E entries into a new
`tail.json`, point `module`/`worksheet.import` at `ModularPolynomialExistence`,
and set `worksheet.output` to a new sheet name. No production code depends on it.

### 7.3 Regenerate and check

```bash
python3 presentation/render.py presentation/function-field-generation/capstone.json
cd lean
lake env lean presentation/FunctionFieldGenerationCapstone.lean
```

The sheet must report 0 errors. The generated sheet is git-ignored; the JSON is
the deliverable.

### 7.4 `presentation/README.md`

Keep "One instance is worked out end to end: the function-field generation
capstone" (there is still one instance, now `Capstone`), and note that the capstone
sheet exhibits a private `hall_all` through `lean_goal` / `#check` while its proof
is semi-formal. Do not advertise a second sheet.

---

## 8. Documentation

* This file is the live plan. Add a one-paragraph **postscript** at the top of
  `PORTING-FFG.md` (which is otherwise retired) saying the `Inputs` bundle was
  removed, `Spine.lean` was renamed `Capstone.lean` and now carries FLT's direct
  `hall_all`, `hall_all` is private, and the old `Capstone.lean`'s interface tail
  moved to `ModularPolynomialExistence.lean`; point here.
* Add the same one-line postscript to `ffg-retrospective.md` §1 or its header:
  the retrospective's "`inputs`/`hall_all`/`gen_prime` are the only port-authored
  declarations" is now "`gen_prime` is", because `hall_all` is the pin's and
  `inputs` is gone. Do not rewrite the historical body.
* `TOPIC-conditional-capstone.md` and `TOPIC-unconditional-capstone.md` are
  historical work orders. A one-line "superseded by TOPIC-ffg-refactor.md" at the
  top of each is enough; do not edit their contents.
* Do not update `math/010-function-field-generation.md`: it already describes the
  pin's private `hall_all` and never mentions `Inputs`.
* Do not update `lean/logs/ffg-port.md` or the audit logs; they are measurements
  of the old layout.

---

## 9. Verification protocol

Run in this order; stop at the first failure and report it with the command and
the log path. All commands from `lean/` unless stated. Keep each tool call under
two minutes; `lake env lean` on one module is allowed, a tree `lake build` is not
without user permission (AGENTS.md).

**Refresh the olean after every edit.** `lake env lean <file>` typechecks but does
not write an `.olean`, so a later check that *imports* the edited module would
silently use the stale one. Between waves, run a single-target build — this is
not the default-target tree build:

```bash
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence
```

These are cheap because the dependency closure is already built; if either starts
building hundreds of jobs, stop and report the dependency change before
continuing.

```bash
# 1. the refactored capstone
lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean
# expected: 4 ok, 0 mismatch, 0 missing, 0 own

# refresh the olean before anything imports it
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone

# 2. the tail
lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/ModularPolynomialExistence.lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/ModularPolynomialExistence.lean
# expected: 4 ok, 0 mismatch, 0 missing, 0 own

# refresh the olean before consumers and sheets import it
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence

# 3. the newly wired legacy modules
for f in Target Collapse Descent DegreeStep Nonmembership Generation; do
  python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/$f.lean
  lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.$f
done
# expected counts from §5.2; all 0 mismatch / 0 missing
# rebuild the dependents last, after their dependencies' oleans are fresh
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence

# 4. the already-wired modules are unchanged
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProduct.lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/SlotProductAnyField.lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/MffCMulPrime.lean
python3 spec/check_port.py --force FLTForHuman/ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean

# 5. spec tooling
python3 spec/check_port.py --changed
python3 spec/unwired_register.py --check
cd ../tools/deps && python3 dedup.py --module FLTForHuman/ModularCurve/FunctionFieldGeneration --no-json
cd ../../lean

# 6. consumers
lake env lean spec/ModularCurveConsumer.lean 2>&1 | tee tmp/consumer.log | grep -c error
lake env lean spec/ModularCurveReady2Consumer.lean 2>&1 | tee tmp/ready2.log | grep -c error
# expected: 0 each

# 7. presentation
python3 ../presentation/render.py ../presentation/function-field-generation/capstone.json
lake env lean presentation/FunctionFieldGenerationCapstone.lean
# expected: 0 errors

# 8. no stale Inputs, no deleted packaging theorem, no sorry in FFG
grep -rn 'Inputs' FLTForHuman/ModularCurve/FunctionFieldGeneration/
grep -rn 'theorem functionFieldGeneration_of ' FLTForHuman/ModularCurve/FunctionFieldGeneration/
grep -rn 'sorry' FLTForHuman/ModularCurve/FunctionFieldGeneration/
# expected: empty. (`functionFieldGeneration_of_squarefree` is a pin name and
# stays in the historical notes of Generation/SlotProduct; do not match it.)
```

Axioms probe (write in `lean/tmp/`, untracked):

```lean
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone
import FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence
#print axioms ModularCurve.functionFieldGeneration
#print axioms ModularCurve.modularFunctionField_eq_full
#print axioms ModularCurve.finrank_adjoin_jqN_eq_dedekindPsi
#print axioms ModularCurve.relfinrank_full_eq_dedekindPsi
#print axioms ModularCurve.exists_monic_evalAtJ_jqN_eq_zero
#print axioms ModularCurve.exists_phiIrreducible
```

Expected: `[propext, Classical.choice, Quot.sound]` for every line.

Full tree build: ask the user first. The measured targeted cost is in §10; if a
tree build is approved, log it to `lean/tmp/ffg-refactor-build.log` and check
warnings, not just success.

---

## 10. Risks, measurements, and decisions

### Measured

**Pre-refactor baseline and scratch.** `lake env lean` on the pre-refactor
`Spine.lean` (now `Capstone.lean`): **10.05 s**. The scratch refactored
`Capstone.lean` (seven imports, private `hall_all`, four public declarations):
**30.10 s and 42.64 s** in two runs, exit 0, no output.

**Landed measurements (2026-11-03).** These are all targeted builds on the warm
tree, not a default-target `lake build`:

| check | time |
|---|---|
| `lake env lean Capstone.lean` | 28.30 s |
| `lake build …Capstone` after deps | 5.1 s (single module) |
| `lake env lean ModularPolynomialExistence.lean` | 7.52 s |
| `lake build …ModularPolynomialExistence` | 6.7–6.8 s |
| six newly wired modules (`Target` … `Generation`) | 51.63 s total, 2.3–11 s each |
| `SlotProduct` rebuild (prose change), triggered by `Capstone` | 31 s |
| `Capstone` + tail rebuild after that | 44.62 s total |

`spec/check_port.py` on the refactored and newly wired modules: Capstone 4 ok,
tail 4 ok, Target 2, Collapse 1, Descent 2, DegreeStep 3, Nonmembership 2,
Generation 1 — all `0 mismatch / 0 missing / 0 own`. `#print axioms` on the six
headlines is `[propext, Classical.choice, Quot.sound]`. No `sorry` and no
`Inputs` remain in the directory.

**No consumer cone grew.** The five capstone consumers
(`HeckeCommuteBar`, `Degree/Relfinrank`, `ModularPolynomialLeadingCoeff`,
`ModularPolynomialUniquenessIrreducible`, `X1/FunctionFieldInclusion`) imported
the old `Capstone`, which already pulled the same seven-module cone; they now
import the new `Capstone` with the same path and cone. The only module that
imported `Spine` was `spec/ModularCurveConsumer.lean`, which also imported the old
`Capstone`, so its cone was already the union. The tail consumers will import
`ModularPolynomialExistence`, whose cone is `Capstone` plus the tail's own
imports — the same set the old `Capstone` pulled. No library consumer gains a new
dependency. The five consumers are *not* built yet; that is the pending check.

### Decisions (recommended; confirm before executing)

1. **Tail name**: `ModularPolynomialExistence.lean` (§4.2). Alternatives listed
   there.
2. **Presentation**: one sheet, retargeted to `Capstone`; delete the tail sections
   rather than splitting. The old capstone is gone and the tail is interface for
   other modules, not capstone mathematics. A tail sheet is an optional
   follow-up; if it is wanted, it must be a second JSON because a sheet has one
   `worksheet.import` and the tail now depends on `Capstone`.
3. **Consumer history**: delete the partial-`Inputs` examples and rewrite the
   debt prose. Keeping a local `Inputs` structure in `spec/` to preserve the old
   wire tests would reintroduce the device the refactor removes.
4. **`SlotValues`**: keep tier 3 (§5.3).
5. **Do not touch `Defs/Fields.lean`** for its stale `Inputs`/`Spine` comments
   unless a rebuild is already needed; the comments are historical, and editing
   them rebuilds the whole dependent cone.

### Risks

* **Dependency inversion.** `Capstone` now imports the seven; any module importing
  `Capstone` pulls the full FFG cone. Most of the affected consumers already
  imported the old `Capstone.lean` (which pulled the same cone), so the practical
  change is small; the measured `Capstone` cost is 30–43 s. A consumer that only
  needs the collapse should import `Collapse`, not `Capstone`.
* **Private `hall_all`.** It cannot be `#check`ed from another module. The
  presentation handles this via `private` + `lean_goal`; the public surface is
  `functionFieldGeneration`. If an external consumer is found, that is a signal
  to add a public corollary, not to make `hall_all` public again.
* **Spec-pin false confidence.** The checker diffs statements, not proofs. The
  refactor does not change the seven statements; if a `mismatch` appears, stop —
  it means the port's statement drifted, and the cure is a `pin:`/`own:` row, not
  a statement edit.
* **Build budget.** The refactor deletes declarations and adds imports; it should
  not add proof work. If the targeted `Capstone` check approaches two minutes, stop
  and report before touching the tree build.

---

## 11. Definition of done

- [x] `Capstone.lean` contains no `Inputs`, no `functionFieldGeneration_of`, and no
      public `hall_all`; `grep` for `Inputs` is empty.
- [x] `Capstone.lean` declares `private hall_all` and the four public capstone
      declarations; it imports `Descent`, `DegreeStep`, `Generation`,
      `Nonmembership`, `SlotProduct`.
- [x] The old `Capstone.lean` is gone; `ModularPolynomialExistence.lean` has the
      four tail declarations and four `spec-pin:` lines.
- [x] Every FFG module except `SlotValues` carries a `spec-pin:` header; the
      expected `check_port` counts in §5.2 hold, all `0 mismatch / 0 missing`.
- [x] The eight FFG entries are out of `PORT_FILES`; the four dead `OWN_PROOFS`
      entries are out; `SOURCES` is untouched.
- [ ] `spec/ModularCurveConsumer.lean` and `spec/ModularCurveReady2Consumer.lean`
      compile with **0 errors**; the consumer has no code `sorry`.
- [ ] `capstone.json` presents `Capstone`; `hall_all` is a `private` declaration with
      `lean_goal` and its proof steps; `inputs`, `functionFieldGeneration_of` and
      the tail sections D/E are gone. The capstone sheet compiles.
- [x] `unwired_register.py --check` is clean.
- [ ] `dedup.py` reports only the known, documented `C`-layer duplicates;
      `move_dead.py` has nothing to move.
- [x] `#print axioms` on the five headlines is
      `[propext, Classical.choice, Quot.sound]`.
- [x] Targeted builds are silent (0 warnings), no `sorry` in FFG, and the
      `Capstone` cost is recorded. A full `lake build` only if the user approves.
- [ ] The plan's postscripts are in `PORTING-FFG.md` and `ffg-retrospective.md`.

---

## 12. Execution order (one wave at a time, each green before the next)

**Wave 0 — confirm decisions.** Tail name, consumer policy, `SlotValues`
exception (§10). No edits.

**Wave 1 — capstone (first half of the atomic name swap). ✅ done 2026-11-03.**
Add the imports, delete `Inputs`, de-parameterize helpers, make `hall_all` private,
move the four declarations in from the old `Capstone.lean`, rewrite the header +
`spec-pin`. Checked on the scratch (`lean/tmp/CapstoneRefactor.lean`) and then on
the real file; `check_port` 4/0/0. Logs: `lean/tmp/ffg-capstone-typecheck.log`,
`ffg-capstone-build.log`.

**Wave 2 — tail (second half). ✅ done 2026-11-03.** Move the old `Capstone.lean`
to `ModularPolynomialExistence.lean` and keep only its tail, header + `spec-pin`,
then rename `Spine.lean` to `Capstone.lean`. Both modules compile; `check_port`
4/0/0. The touched consumers were deliberately **not** built, per the build-time
check; their import lines are the next wave. Logs:
`lean/tmp/ffg-tail-typecheck.log`, `ffg-tail-build.log`.

**Wave 3 — `spec-pin` for the six legacy modules. ✅ done 2026-11-03.** Wires
added, prose de-`Inputs`-ed, old checker entries removed, `check_port --force`
run: 2/1/2/3/2/1 ok, all `0 mismatch / 0 missing`. Logs:
`lean/tmp/ffg-six-build.log`, `ffg-specpin.log`.

**Wave 4 — consumers.** `spec/ModularCurveConsumer.lean` (the substantive edit),
`spec/ModularCurveReady2Consumer.lean` (import), the header prose in §6.1. Check:
0 errors, 0 code `sorry`. Log to `lean/tmp/ffg-consumers.log`.

**Wave 5 — presentation.** Retarget `capstone.json` to `Capstone`, delete the
`Inputs`/assembly and tail sections, update `presentation/README.md`, render and
compile the capstone sheet. Log to `lean/tmp/ffg-presentation.log`.

**Wave 6 — verification and docs.** Run §9 in full, add the postscripts, update
this file's status to done with the measured numbers. Report the final
`check_port` table, consumer error counts, axiom probe, and whether a tree build
is still needed.
