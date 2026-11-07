# Topic: the FFG capstone refactor and the `spec-pin` upgrade

**Status: in progress (2026-11-03).** Waves 1–5 are landed and green: the
`Inputs` bundle is gone, `hall_all` is private and FLT's, the capstone is in
`Capstone.lean`, the tail is in `ModularPolynomialExistence.lean`, every FFG module
except `SlotValues` is `spec-pin:`-wired, the Lean/spec consumers are rewired, and
the presentation is retargeted. Wave 6 (final verification and docs) remains.

**The arc, as a reusable case study: [../CASE-hall-all.md](../CASE-hall-all.md).** It is
written as the node's state against its state before the refactor, with the 2026-11-04 detour
recorded as a lesson (§4: what was done, what it cost, the three rules and the tell). Read it
before starting the next assembler, and read §13–§17 below when you need the date-stamped
reasoning.

**Wave 7 (landed 2026-11-04): the assembler interfaces.** The
structure the refactor produced is right, but the three FFG *assemblers* still
carry the pin's proof script in their signatures —
`jqN_div_mem_modularFunctionField` states 16 lines to say
`jqN M ∈ modularFunctionField (M * p)`, and the caller writes 75 lines of glue
(`Capstone.lean:141–215`) to speak it. Wave 7 named the vocabulary, gave the pinned
names readable statements (both of them: §13 and §14), and moved the glue to a
module whose subject it is. It **retired both of `Descent.lean`'s verbatim
statements**, kept their names, and — because no declaration in the module then
mirrored the pin — retired that module's `spec-pin:` wire with it (§14.4). The
verbatim text stays in [TOPIC-descent.md](TOPIC-descent.md) §2 and in git history,
which is where a fidelity record belongs. The port-wide generalisation is
[../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md).

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
6. **(wave 7, §13)** Give the assemblers back: name the pushed minimal polynomial
   and the nome map, rewrite the descent's statement in place (the pin's name, a
   readable signature, the pin's proof script with two hypothesis applications
   retyped), record the retirement as an `own:` row, and move `Capstone.lean`'s
   `Shapes` glue into `DescentFromSlots.lean` behind one `Hall M`-level statement.
   One statement is retired, no wire is.

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

The counts above are the wave 1–6 values. **Wave 7 (§13–§14) took
`Descent.lean` off the wire entirely**: both of its public statements are now
deliberate deviations, so its two `spec-pin:` lines were removed and the module is
tier 3 (built, statements not diffed, like `SlotValues`), re-registered by
`spec/unwired_register.py --rebuild` — 106 unwired modules, 3100 public
declarations. One module was added at tier 3 (`DescentFromSlots.lean`). The only
`own:`-eligible declarations are the two `def`s in `Defs/PhiAtSlot.lean`, which are
public and wired, so they carry `own:` rows (§13.7); that is now the wave's last
checker step, deliberately deferred.

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
dependency.

**Consumer verification (2026-11-03).** The two rewired library consumers build:
`FinrankAdjoinJqNModC` 8.6 s (after `SlotProductAnyField` 34 s, `MffCMulPrime`
9.5 s, `PrimePowerStepAnyField` 10 s), and `TranscendentalRigidity` 3.4 s after
the one-time cascade (`Isogeny.IntermediateField` 58 s, `TwoCurveDescent` 54 s).
The five capstone consumers typecheck unchanged (0 errors). The spec consumers
report 0 errors; the presentation sheet compiles with 0 errors. The cascade is a
one-time effect of the changed `Capstone`/`SlotProduct` sources, not a new edge.

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
- [x] `spec/ModularCurveConsumer.lean` and `spec/ModularCurveReady2Consumer.lean`
      compile with **0 errors**; the consumer has no code `sorry`.
- [x] `capstone.json` presents `Capstone`; `hall_all` is a `private` declaration with
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

**Wave 4 — consumers. ✅ done 2026-11-03.** Imported the tail in
`Degree/FinrankAdjoinJqNModC` and `TranscendentalRigidity` (both `spec-pin:`-clean:
24 and 2 ok), rewired `spec/ModularCurveConsumer.lean` (removed the five
partial-`Inputs` examples and the `inputs` checks, updated the zone prose) and
`spec/ModularCurveReady2Consumer`. The two spec consumers report 0 errors; the
five capstone consumers typecheck unchanged. Logs: `lean/tmp/ffg-consumer*.log`,
`ffg-build-finrank.log`, `ffg-build-transcendental*.log`.

**Wave 5 — presentation. ✅ done 2026-11-03.** Retargeted `capstone.json` to the
new `Capstone`: removed `Inputs`/`inputs`/`functionFieldGeneration_of` and the
tail sections D/E, added the private `hall_all` with `lean_goal` and its proof,
and updated the metadata. The sheet renders and compiles with 0 errors. Logs:
`lean/tmp/ffg-presentation-compile-3.log`, backup
`tmp/ffg-warm/capstone.before-presentation.json`.

**Wave 6 — verification and docs.** Run §9 in full, add the postscripts, update
this file's status to done with the measured numbers. Report the final
`check_port` table, consumer error counts, axiom probe, and whether a tree build
is still needed.

**Wave 7 — the assembler interfaces (§13–§14). ✅ done 2026-11-04.** Five steps,
each green before the next: 7a the vocabulary (`Defs/PhiAtSlot.lean`: `nomeMap`,
`pushedMinpoly`, `nomeMap_qExpand`, in `ModularCurve.Nome`); 7b the descent's
statement rewritten in place under the pin's name (16 → 6 lines; the pin's proof
kept, with `hBev` retyped and the two hypothesis applications changed — §13.3);
7c `FunctionFieldGeneration/DescentFromSlots.lean` (156 lines, 75 of them the glue
moved out of `Capstone`, now behind `jqN_mem_modularFunctionField_of_hall`); 7d
`Capstone.lean`'s `Shapes` section deleted and its call site reduced to
`jqN_mem_modularFunctionField_of_hall M p hallM` (337 → 250 lines); 7e the second
assembler (§14), which retired the module's wire. Builds and axioms in §14.5.
Remaining: the two `own:` rows for `Defs/PhiAtSlot.lean` and the presentation
JSON (§13.5a) — checker bookkeeping, deliberately last.

---

## 13. Wave 7 — the assembler interfaces

**Status (2026-11-04): executed, green.** The vocabulary of 7a and the replacement
statements of 7b were first elaborated against the pre-wave build
(`lean/tmp/probe_descent_interface.lean`), then landed and rebuilt module by module.
Everything below is the plan as written; §14 records what the execution changed
(the wire move, which this section's §13.6(b) did not anticipate) and §14.5 the
measured numbers.

The general statement of the problem — what a transcribed signature records, how
to audit one, and the mechanism table — is
[../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md). This section
is the FFG instance: the exact edits, the decisions behind them, and the gates.

### 13.1 The diagnosis, in this directory

The refactor above fixed the *structure* (no `Inputs`, private `hall_all`, one
capstone). It left the three assemblers stating the pin's proof script. The
sharpest instance:

```lean
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (htw : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly …).map …) = 0 →
      ∀ w : Kˣ, y = qExpand K (M * p * M) (qTwist w (coeffEmb K jq)) → w = 1)
    (hsp : ∀ y : LaurentSeries K, Polynomial.eval y ((minpoly …).map …) = 0 →
      y ≠ coeffEmb K (qExpand ℚ (M * p) (jqN (M * p * p)))) :
    jqN M ∈ modularFunctionField (M * p)
```

16 lines for `jqN M ∈ modularFunctionField (M * p)`, with five binders the
conclusion never mentions. Decoded, it says:

> Let `p` be prime, let `K` carry a primitive `(M * p)`-th root of unity, and let
> `P` be the minimal polynomial of `j(q ^ M)` pushed to the level-`M * p` nome.
> If every root of `P` of the shape `j(w q ^ (M * p * M))` has `w = 1`, and
> `j(q ^ ((M * p) * (M * p * p)))` is not a root of `P`, then
> `j(q ^ M) ∈ ℚ(j(q), j(q ^ (M * p)))`.

Four defects, all instances of the general list:

1. **The hypotheses are the proof's `rcases`.** `Descent.lean:189` splits the
   Φ-side root description into two branches and dispatches them with `hsp` and
   `htw`. The mathematics is one fact: `P` and the level-`p` equation have the
   unique common root `x₀`.
2. **The pushed minimal polynomial is anonymous**, and the term is written out in
   full in the signature twice, in the proof once, and in `Capstone`'s three glue
   lemmas. Six root-predicate hypotheses in two files.
3. **A binder the conclusion never mentions** (`K`, `ζ`, `hζ`) is a base change:
   the proof passes to `CyclotomicField (M * p) ℚ` and its last ten lines are the
   descent back.
4. **The theorem `obtain`s its own datum** (`Descent.lean:92`), so no hypothesis
   can mention the Φ-side polynomial. That is why `htw`/`hsp` constrain only the
   minimal-polynomial side, and why the caller must re-derive the Φ-side root
   shape: `Capstone.lean:141–215`, 75 lines of glue (`root_shape`, `htw_of`,
   `hsp_of`) plus a 7-line call site that builds the cyclotomic field, the root of
   unity, and two lambdas.

### 13.2 7a — the vocabulary

Home: `Defs/PhiAtSlot.lean` (already imported by `Descent.lean` and
`SlotProduct.lean`, and already the module for "polynomials at a slot" —
`phiAtSeed` is its other half). Namespace: **`ModularCurve.Nome`**.

```lean
/-- The level-`N` nome map: read a function of `ℚ(j(q))` at `q ↦ q ^ N`,
coefficients extended to `K`. -/
def nomeMap (K : Type*) [Field K] [Algebra ℚ K] (N : ℕ) [NeZero N] :
    ℚ⟮jq⟯ →+* LaurentSeries K :=
  ((coeffEmb K).comp (qExpand ℚ N)).comp (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))

/-- The pushed minimal polynomial of `j(q ^ M)` at the level-`N` nome. -/
def pushedMinpoly (K : Type*) [Field K] [Algebra ℚ K] (M : ℕ) [NeZero M]
    (N : ℕ) [NeZero N] : Polynomial (LaurentSeries K) :=
  (minpoly ℚ⟮jq⟯ (jqN M)).map (nomeMap K N)

/-- The pin's inline spelling, definitionally. Nothing downstream rewrites. -/
theorem pushedMinpoly_def (M N : ℕ) [NeZero M] [NeZero N] :
    pushedMinpoly K M N
      = (minpoly ℚ⟮jq⟯ (jqN M)).map (((coeffEmb K).comp (qExpand ℚ N)).comp
          (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ))) := rfl
```

Plus the one shared bridge. The same equation is proved twice today, in the two
multiplication orders — `Capstone.lean:152–156` (`p` on the right, five lines
with a `mul_comm`) and `SlotProduct.lean:356–362` (`k` on the left, three lines
under `subst hN`). One statement covers both:

```lean
theorem nomeMap_qExpand (M e : ℕ) [NeZero M] [NeZero e] :
    (qExpand K e).comp (nomeMap K M) = nomeMap K (M * e) := by
  refine RingHom.ext fun z => ?_
  simp only [RingHom.comp_apply]
  rw [coeffEmb_qExpand, coeffEmb_qExpand, qExpand_qExpand]
  exact qExpand_congr (mul_comm e M) _
```

`nomeMap_qExpand` is not decoration: it is the step that turns the level-`M`
datum into the level-`M * e` datum, and writing it once removes the
re-association blocks in the glue. The `SlotProduct` site uses the other order,
so it becomes this lemma followed by `qExpand_congr (mul_comm k M')`; that is a
one-line call site, not a second proof.

### 13.3 7b — retire the text, keep the name

**The decision (2026-11-04, the user's): the verbatim statement goes.** The
question is what "go" means, and the answer is *the text, not the name*: the pin's
declaration name stays and carries the readable statement. The name is the pin
linkage — it is what a reader arriving from
`Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean` types, what the
`spec/` consumer `#check`s, and what the presentation labels — so the name is the
one part that is not the problem. The 16-line text is.

Keeping both was the previous recommendation and it is wrong, for a reason I
missed: the readable declaration would be a 9-line adapter, so the **proof** — the
60 lines a reader actually wants — would stay under the inscrutable statement. The
reader following the pin name would land on the unreadable text and have to be
told to look elsewhere. Two declarations of one theorem, with the mathematics
under the wrong one, is a comprehension cost paid by every reader; the checker's
convenience is not worth it.

New signature under the same name:

```lean
/-- **Descent by one prime**: `j(q ^ M) ∈ ℚ(j(q), j(q ^ (M * p)))`.

`K` is only a certificate: it is a field carrying a primitive `(M * p)`-th root of
unity, chosen so that every `ψ(M)` conjugate of `j(q ^ M)` is visible after the
pushed minimal polynomial is read at the level-`M * p` nome. `htw` says the only
root at nome-level `(M * p) * M` is the untwisted one, `hsp` says the extra
conjugate of the level-`p` equation at that slot is not a root; together they are
"the pushed minimal polynomial and `Φ_p` have the unique common root `x₀`". -/
theorem jqN_div_mem_modularFunctionField (M : ℕ) [NeZero M] (p : ℕ)
    [hp : Fact (Nat.Prime p)] {K : Type*} [Field K] [Algebra ℚ K] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) (M * p))
    (htw : ∀ w : Kˣ, (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * M) w) → w = 1)
    (hsp : ¬ (pushedMinpoly K M (M * p)).IsRoot (TS K ((M * p) * (M * p * p)) 1)) :
    jqN M ∈ modularFunctionField (M * p)
```

**How much of the proof moves.** Not much, and the point matters because an
earlier version of this plan called the rewrite a redesign and used that to
justify keeping both. The pin's script is untouched except at the two places where
the hypotheses are *applied*:

* `hBev` (lines 154–161) is retyped: its conclusion becomes
  `(pushedMinpoly K M (M * p)).IsRoot y` instead of the spelled-out
  `Polynomial.eval y ((minpoly …).map …) = 0` (defeq via `IsRoot` and
  `pushedMinpoly_def`, so the body is unchanged);
* branch 1 of the `rcases` (line 190) currently applies `hsp` to `y` and an
  equation; the new `hsp` takes the *slot value*, so the proof first transports
  `hB := hBev y hyB` along `hy1.trans hspread.symm`, then along
  `iota_jqN (M * p) (M * p * p)` — which reads
  `y = TS K ((M * p) * (M * p * p)) 1` — and applies `hsp` there;
* branch 2 (line 191) currently passes `y` and the equation to `htw`; the new
  `htw` takes the unit, so it becomes `htw (1 * ζ ^ (b * (M * p / p))) (by rw [← hy1, coeffEmb_jq]; exact hB)`.

Everything else stays: the `obtain`ed datum, `hseed`/`hdist`/`hspread`,
`hrootA`/`hBev`/`hA0`/`hAs`/`hAnd`, the `mem_range_of_unique_common_root`
application, and the injectivity strip. That is why the transcription policy
([TOPIC-descent.md](TOPIC-descent.md) §2.1) is *satisfied*, not violated: the
script is the pin's, and only the hypothesis types at two application sites are
retyped. What the wave does **not** do is extract the `huniq`-shaped core — that
would restructure the proof, and it is the deeper fix listed as open in
[../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md) §9.

**The record, in two places.** The module's `## Source` block gains a line
naming the wrapper whose text was retired and the date; and
`spec/decl_markers.tsv` gains

```text
FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean<TAB>ModularCurve.jqN_div_mem_modularFunctionField<TAB>own: readable respelling of Theorems/Thm_ModularCurve_jqN_div_mem_modularFunctionField.lean:8 -- verbatim text retired 2026-11-04 (TOPIC-ffg-refactor.md §13); htw/hsp one-lined, conclusion unchanged
```

**What is given up, stated plainly.** The wire stops diffing this statement. The
port's own statement becomes the spec, so there is no transcription left to drift;
what is lost is the mechanical check that the port still *states the pin's
theorem*, and that becomes an editorial assertion carried by the `own:` reason and
the pinned text quoted in [TOPIC-descent.md](TOPIC-descent.md) §2. Accepting that
is the point of the wave: the port exists to be comprehended, and a statement kept
only to satisfy a text diff is a statement kept for the tool.

### 13.4 7c — the glue module

New module `FLTForHuman/ModularCurve/FunctionFieldGeneration/DescentFromSlots.lean`,
importing `Descent`, `SlotProduct`, `Defs/PhiAtSlot` (the vocabulary of 7a),
`Defs/TS`, `Defs/Cyclotomic`, `Mathlib.NumberTheory.Cyclotomic.Basic`:

* `private root_shape`, `private htw_of`, `private hsp_of` — moved verbatim from
  `Capstone.lean:145–214`, with their `hy : Polynomial.eval y ((minpoly …).map …)
  = 0` hypothesis replaced by `(pushedMinpoly K M (M * p)).IsRoot y`
  (definitionally the same, one line instead of three);
* `theorem jqN_mem_modularFunctionField_of_hall (M : ℕ) [NeZero M] (p : ℕ)
  [Fact (Nat.Prime p)] (hall : Hall M) : jqN M ∈ modularFunctionField (M * p)` —
  the interface the capstone actually wants: no `K`, no `ζ`, no hypothesis about
  roots. It is `jqN_div_mem_modularFunctionField` (as rewritten in 7b) at
  `K := CyclotomicField (M * p) ℚ`, `ζ := cycUnit (M * p) ^ (M * p / M)`, with
  `htw_of`/`hsp_of` supplying the two slot facts.

Why a separate module and not inside `Descent.lean`: `Descent` is T15, whose only
input is the `Φ_p` cone; `DescentFromSlots` is T15 **plus** T19's slot product. The
pin keeps this glue inside `S_ModularCurve_functionFieldGeneration.lean`'s proof
(lines 541–613, private). Making `Descent` import `SlotProduct` would drag T19's
development into every consumer of the descent to save one file, and the playbook
(§5) makes a module a subject decision, not a scheduling one. Today no consumer
cone grows either way: `Capstone` — the only consumer — already imports both.

**Tier 3**, no `spec-pin:` header, on the `SlotValues` precedent (§5.3): every
public declaration in the module is the port's own (`_of_hall` has no pin
counterpart), so a wire would diff nothing and an `own:` row would record "ours"
once. The header must say this, and `spec/unwired_register.py --rebuild` must be
re-run so the module appears in the register.

### 13.5 7d — the caller

In `Capstone.lean`:

* delete `section Shapes … end Shapes` (lines 141–215, **75 lines**);
* replace the 7-line call site in `hall_all` with
  ```lean
  have hmem := jqN_mem_modularFunctionField_of_hall M p hallM
  rw [mff_congr hMp] at hmem
  exact hmem
  ```
  (the surrounding `have : Fact (Nat.Prime p) := ⟨hp⟩` and `hallM` stay as they
  are);
* add `import …FunctionFieldGeneration.DescentFromSlots`; **verify by build**
  whether `Mathlib.NumberTheory.Cyclotomic.Basic` and `Defs/Cyclotomic` become
  droppable — their only remaining uses in this module are the call site being
  replaced (`cycUnit`, `CyclotomicField` appear nowhere else), and so is
  `Defs/TS`.
* update the header: the provenance ranges `199–240` (the cyclotomic root) and
  `467–613` (`tight_one` through `hsp_of`) at `Capstone.lean:3–10` move to the new
  module's provenance block, and the `## Cyclotomic roots` note
  (`Capstone.lean:61–66`) moves with the imports it describes.

### 13.5a The downstream record of a retired statement

**The renderer does not read Lean.** `presentation/render.py` takes the JSON as the
source of truth: it emits `#check <name>` (and `#print` for definitions), so the
*checked* type is always Lean's, but every quoted statement (`premises[].lean`), the
`math`/`note` prose, the `file:line` and the headings are the JSON's own text.
`--check-only` validates the schema plus the cross-references (ids unique, every
definition and declaration reachable from a section, every premise cited by a step,
narrative backticks balanced) — never the `lean` field against the declaration. So a
stale JSON regenerates into a sheet that **still compiles** while describing the old
statement; the mismatch is invisible unless you read it. The `file:line` fields rot
silently for the same reason (the descent went from `Descent.lean:74` to `:111`).

Three places state what the theorem says. None of them is a Lean dependency, and
all three must move in the same wave or the tree contradicts itself:

1. **`spec/ModularCurveConsumer.lean`, zone M** (`:692–706`, live prose): it says
   the `htw`/`hsp` "stay arguments, exactly as the pin's node has them and as T19
   will later discharge them". Still true in substance, wrong in detail — one-lined
   now, and T19 discharges them in `DescentFromSlots`. Its two `#check`s (`:707`,
   `:708`) are signature-agnostic and keep working.
2. **`presentation/function-field-generation/capstone.json`** — the tracked source
   of the generated sheet. **Done 2026-11-04** (+34/−12): `premises[6]` and
   `premises[7]` got their new `lean` text, `math`, `note` and line numbers
   (`:220 → :260`, `:74 → :111`); `steps[5].math` and `steps[8].why` were reworded
   for the discharged slot hypotheses and the `DescentFromSlots` home; section G's
   "private helpers" paragraph moved `root_shape`/`htw_of`/`hsp_of` to
   `DescentFromSlots`; and two definitions were **added** — `ModularCurve.Nome.nomeMap`
   and `ModularCurve.Nome.pushedMinpoly` — because the statements now name them and
   a sheet should `#print` the vocabulary it quotes. Regenerated with
   `python3 presentation/render.py presentation/function-field-generation/capstone.json`
   and elaborated: `lake env lean presentation/FunctionFieldGenerationCapstone.lean`,
   exit 0, 0 errors (the generated sheet is git-ignored; the JSON is the edit).
3. **[TOPIC-descent.md](TOPIC-descent.md) §1–§2** quotes the pin's statement
   verbatim under the heading "the statements, from the `Theorems/` wrappers,
   verbatim". That is now the *retirement record* — the place the pinned text
   lives — so it stays, and **gained the note (done 2026-11-04)** saying that the
   block is the record, not the API, and where the port's statements are.

What is *not* touched: the dated log entries in `spec/ModularCurveConsumer.lean`
(`:1410–1418`, "Descent result (2026-09-22)") and in `lean/logs/` are history and
are not rewritten — the refactor's own rule.

### 13.6 The two decisions, with their measured basis

**(a) `private`, or a namespace?** Both, in their own layer — and the two
questions are independent, which is the part that is easy to get wrong:

* the checker is **blind to namespaces** (matching keys on the last name
  component and the statement's content hash), so a sub-namespace neither creates
  nor removes a `missing`/`mismatch`;
* a **new public declaration** in a wired module is not invisible: measured on a
  copy of `Descent.lean` (before 7b, when both of its statements were diffable),
  adding one public `def` yields `2 ok, 0 mismatch, 1 missing` — a **FAIL**; the
  same `def` as `private` yields `2 ok`; the same `def` with an `own:` row yields
  `2 ok, 1 own` — a pass.

So: the two `def`s are **public**. They cannot be `private`: `private` is not
reachable across modules (playbook §6), and the glue module's `root_shape`,
`htw_of`, `hsp_of` — `private` themselves — must still *state*
`pushedMinpoly` in their hypotheses. They are public **in a sub-namespace**,
because the port's `ModularCurve` is otherwise exactly the pin's namespace and a
bare port-invented name there is a collision waiting for a re-pin. Cost of the
namespace: one `open` per consumer. Cost of the `own:` rows: three lines in
`spec/decl_markers.tsv` — two for the `def`s, one for the retired statement of
7b. The three glue lemmas and everything else new stays `private`, which costs
nothing.

The `own:` row's declaration column must be the name **the checker parses**, not
the name Lean prints: read it from `spec/check_port.py --json`. A name the parser
did not produce is reported as `STALE MARKER` *and* leaves the declaration
`missing`, so the module still fails and the marker did nothing (observed while
probing this wave).

**(b) `spec-pin`: keep the wire; retire the statement, not the wire.** The
temptation, once 7b removes the text, is to remove the corresponding `spec-pin:`
line as well. That is the wrong granularity, three times over:

1. **The wire is per module and lists pin *files*.** `Descent.lean`'s wire is
   `modularFunctionField_eq_full_of` **and** `jqN_div_mem_modularFunctionField`.
   Retiring one declaration's text says nothing about the other, which still
   mirrors its wrapper exactly and must keep being diffed. Removing the wire to
   "clean up" after 7b would silently unverify it.
2. **The retirement is recorded per declaration, by `own:`.** What is measured is
   the verdict: on a wired copy of `Descent.lean`, a declaration with an `own:`
   row reports `own` (pass) and the same declaration without one reports
   `missing` (FAIL). The row is both the mechanism and the audit trail, because
   its reason names the wrapper file and says what was retired. The count after
   7b is `1 ok + 1 own` (§13.7) — arithmetic on how many statements the module
   still mirrors, not a measurement.
3. **A module with no wire is not diffed at all** (`check_module` returns `None`),
   so dropping it would also stop verifying any statement transcribed into the
   module later, and would hide the module from `check_port --all`.

So the rule the wave establishes, and which the port-wide note states generally
([../TOPIC-assembler-interfaces.md](../TOPIC-assembler-interfaces.md) §6):

> **Retire the *text*, keep the *name* and the *wire*.** The name carries the pin
> linkage, the `own:` reason carries the provenance, the notes carry the verbatim
> text, and the wire keeps every *other* declaration in the module under the diff.
> Drop a wire only when a whole module stops mirroring a pin file.

This is not a policy the user wanted debated further — it is the mechanism that
was already in the tooling (`own:` = tier 2, "not diffed", with a recorded
reason), used at declaration granularity instead of module granularity.

**Superseded during execution (2026-11-04).** The paragraph above assumes that one
statement is retired and the other still mirrors its wrapper. §14 retired the
second as well, at which point `Descent.lean`'s wire diffed nothing and was removed
— the module is tier 3 now. The rule is refined there and in the port-wide note:
*retire the text, keep the name; retire the wire when no declaration in the module
mirrors the pin any more.*

### 13.7 Post-wave-7 `check_port` table

| module | wire | expected |
|---|---|---|
| `Defs/PhiAtSlot.lean` | unchanged | current count + **2 own** (`ModularCurve.Nome.nomeMap`, `.pushedMinpoly`) |
| `Descent.lean` | **removed** (7e, §14.4) | not diffed (tier 3) — both statements are deliberate deviations |
| `DescentFromSlots.lean` (new) | none (tier 3) | not diffed; in the `unwired_register` |
| `Capstone.lean` | unchanged | **4 ok**, unchanged |
| every other FFG module | unchanged | unchanged (§5.2) |

### 13.8 Gates

```bash
cd lean
# 7a, 7b, 7c: each module silent, then its own diff
timeout 110 lake env lean FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean
timeout 110 lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean
timeout 110 lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/DescentFromSlots.lean
python3 spec/check_port.py FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean --force --json | head -40
python3 spec/check_port.py FLTForHuman/ModularCurve/FunctionFieldGeneration/Descent.lean --force
# 7d: the caller, then the capstone cone (the only consumer)
timeout 110 lake env lean FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean
python3 spec/check_port.py FLTForHuman/ModularCurve/FunctionFieldGeneration/Capstone.lean --force
# the register and the duplicates
python3 spec/unwired_register.py --rebuild && python3 spec/unwired_register.py --check
cd ../tools/deps && python3 dedup.py --module FLTForHuman/ModularCurve/FunctionFieldGeneration --no-json
```

### 13.9 Definition of done

- [x] `grep -c "minpoly ℚ⟮jq⟯"` is 0 in `Capstone.lean` and
      `DescentFromSlots.lean`; in `Descent.lean` the surviving occurrences are only
      the `minpoly` that defines the pushed polynomial `B` inside the proof.
- [x] `Capstone.lean` has no `section Shapes`, no `CyclotomicField`, and no
      two-lambda call site (`337 → 250` lines).
- [x] `DescentFromSlots.lean` carries the moved glue, the `Hall M` interface, a
      header that justifies tier 3, and no `sorry`.
- [x] `#print axioms` on `jqN_div_mem_modularFunctionField`,
      `modularFunctionField_eq_full_of`, `jqN_mem_modularFunctionField_of_hall` and
      `functionFieldGeneration` is `[propext, Classical.choice, Quot.sound]`.
- [x] The retired verbatim statements are quoted in
      [TOPIC-descent.md](TOPIC-descent.md) §2 and the module header names both
      wrappers and what deviates, so the drop is auditable without the wire.
- [x] `Descent.lean` is tier 3 and in the rebuilt `unwired_register`
      (106 modules, 3100 public declarations).
- [ ] The two `own:` rows for `Defs/PhiAtSlot.lean` (`ModularCurve.Nome.nomeMap`,
      `.pushedMinpoly`) are in `spec/decl_markers.tsv` with the parser's names and
      `--strict-markers` is clean — the one piece of checker bookkeeping left,
      deliberately deferred at the user's direction.
- [x] The presentation `capstone.json` is updated and regenerates to a sheet that
      elaborates with 0 errors (§13.5a), and `spec/ModularCurveConsumer.lean` zone M
      carries the new prose plus four `#check`s (0 errors). [TOPIC-descent.md](TOPIC-descent.md)
      §2 marks itself the retirement record.

### 13.10 Risks

* **The retired statement no longer drifts against anything.** After 7b the port's
  statement *is* the spec: if it is later edited, no diff will notice that it no
  longer says what the pin says. The two mitigations are the `own:` reason (which
  names the wrapper) and the verbatim quote in
  [TOPIC-descent.md](TOPIC-descent.md) §2; when either is edited, the other must be
  visited in the same change. This is the deliberate price of the retirement, not
  an oversight — do not "restore" the verbatim statement to get the diff back.
* **The proof edit is small but not trivial.** 7b retypes two hypothesis
  applications and `hBev`; if the `rw [← hy1, coeffEmb_jq]` step does not close
  against `TS`, the fallback is to keep the old hypothesis *shape* and state the
  readable one as an `iff`-lemma beside it — which reopens the two-declaration
  question and should be reported before proceeding, not decided silently.
* **Tier 3 is a discoverability cost.** The glue module's public theorem is
  invisible to anyone grepping for a diff. The register is the mitigation; the
  header must name the pin lines it transcribes.
* **The namespace is a consumer-visible decision.** `ModularCurve.Nome` is
  reachable only with an `open`; if a reviewer objects, moving the two `def`s to
  bare `ModularCurve` is a rename plus two `own:` row edits, and the checker
  counts do not move — but the collision exposure returns.
* **Build budget.** 7a–7d rebuild `PhiAtSlot`, `Descent`, the glue, `Capstone`
  and then the capstone cone. Per AGENTS, no tree `lake build`; take the targeted
  checks in §13.8 and stop if a single `lake env lean` approaches two minutes.

---

## 14. Wave 7e — the second assembler, and the wire

**Status: landed 2026-11-04**, after §13's four steps. `modularFunctionField_eq_full_of`
did need a refactor, but a much smaller one, and for a different reason: it has
**none** of the descent's pathologies — no splitting field, no root predicate, no
auxiliary datum, no base change, no case split. It had two of the six symptoms in
the port-wide note plus one defect the list does not name.

### 14.1 Before and after

Before (5 lines, two hypotheses with the same five-binder prefix):

```lean
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      jqN M ∈ modularFunctionField N)
    (hgen' : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      modularFunctionField M = modularFunctionFieldFull M) :
    modularFunctionField N = modularFunctionFieldFull N
```

After (3 lines, one hypothesis):

```lean
theorem modularFunctionField_eq_full_of (N : ℕ) [NeZero N]
    (hstep : ∀ (M : ℕ) [NeZero M] (p : ℕ), p.Prime → M * p = N →
      Gen M ∧ jqN M ∈ modularFunctionField N) :
    modularFunctionField N = modularFunctionFieldFull N
```

Three defects, in decreasing order of cost:

1. **`Gen M` was stated unfolded** — and under the pin's `hgen'` name. `Gen` is the
   module's own `abbrev` for exactly that field equality (`Defs/Fields.lean:229`),
   so the hypothesis re-derived vocabulary the port had already built for it.
2. **The five-binder prefix was written twice** (`∀ (M : ℕ) [NeZero M] (p : ℕ),
   p.Prime → M * p = N →`). Symptom 3 of the port-wide note at binder granularity.
3. **The two facts are consumed together and were passed apart.** Both come from one
   source — `Hall M` — at the only call site, so no caller can supply one without the
   other; conjoining them makes the hypothesis one sentence, "the induction step at
   level `N`".

The `[NeZero M]` binder inside the quantifier is **not** a defect and stays: `jqN M`
is ill-typed without the instance, so it cannot be hoisted out of the `∀`. This is
the one place where the "binder noise" heuristic must not be applied.

### 14.2 What it bought at the call site

`Capstone.lean`'s `hall_all` carried two lambdas with the same header — `intro M _
p hp hMp` and the `hMlt` derivation written twice, 12 lines. It is now one lambda
(8 lines), and the second fact is `hallM`'s own second component:

```lean
    refine modularFunctionField_eq_full_of d ?_
    intro M _ p hp hMp
    ...
    have hallM : Hall M := hprop M ⟨p, hMp.symm⟩ hMlt
    have hmem := jqN_mem_modularFunctionField_of_hall M p hallM
    rw [mff_congr hMp] at hmem
    exact ⟨(hallM M dvd_rfl).2, hmem⟩
```

The proof body changed in two lines: `hstep …` / `hgen' …` became
`hstep' := hstep …` with `hstep'.2` / `hstep'.1`.

### 14.3 Verdict

Yes, it needed refactoring — but the question worth recording is *which* refactor.
The §13 recipe would have been overkill: there is no case split to name and no seam
to seal. What it needed was (a) the module's existing vocabulary (`Gen`) and (b) one
hypothesis per mathematical fact. That is the cheap end of the same recipe, and it
was worth doing because the duplication had migrated to the *call site*: a symptom
the statement alone does not show, and the reason to read the caller before deciding
an assembler is fine.

### 14.4 The wire, as predicted

With both of `Descent.lean`'s public statements now deliberate deviations, its
`spec-pin:` wire diffed nothing. Left in place it would have reported two
`MISMATCH`es — a red module that says "the port drifted" when the port chose. So:

* the two `spec-pin:` lines are removed from the header and replaced by a
  `## Source, and the two retired statements` paragraph that names both wrappers
  (`Theorems/Thm_…_jqN_div_mem_modularFunctionField.lean:8` and
  `Theorems/Thm_…_modularFunctionField_eq_full_of.lean:8`) and states what deviates;
* the module is **tier 3**: built, elaborated, statements not diffed — the same tier
  as `SlotValues.lean`, with the same documented reason;
* `spec/check_port.py` on the module now says
  `no spec-pin: directive — not wired (tier 3)`, and `spec/unwired_register.py
  --rebuild` reports 106 unwired modules / 3100 public declarations / 2522 with a pin
  original;
* the verbatim statements stay readable in [TOPIC-descent.md](TOPIC-descent.md) §2,
  and the pin's proof scripts are still the proofs below (`Descent.lean` lost no
  mathematics: the retyped `hBev` and the two hypothesis applications are the whole
  diff of the descent's body).

**This refines §13.6(b), and the port-wide note with it:** *retire the text and keep
the name; retire the wire when no declaration in the module mirrors the pin any
more.* §13.6(b)'s "keep the wire" was correct only while
`modularFunctionField_eq_full_of` still matched its wrapper — which is exactly the
distinction now written into the note.

### 14.5 Measurements

| item | before | after |
|---|---|---|
| statement lines, descent | 16 | 6 |
| statement lines, one-prime reduction | 5 | 3 |
| `Capstone.lean` | 337 lines | 250 (−87) |
| the `Shapes` glue | 75 lines in `Capstone` | moved to `DescentFromSlots` (156-line module) |
| `Descent.lean` | 256 lines | 293 (both statements shorter; the growth is the docstrings that now explain `K`, `htw`, `hsp` and the retirements) |
| `Defs/PhiAtSlot.lean` | 243 lines | 286 (+43: the vocabulary) |
| `#print axioms` on the four headlines | clean | clean |

Targeted `lake build` with warm deps, one module each: `PhiAtSlot` 20 s (the new
declarations), `Descent` 8–10 s, `DescentFromSlots` 7.3 s, `Capstone` 4.0 s. The
`PhiAtSlot` change forces one `SlotProduct` rebuild (39 s), because it imports the
vocabulary; no other module's *source* changed. No tree build was run.

### 14.6 What is left

One item: the two `own:` rows for `ModularCurve.Nome.nomeMap` and
`.pushedMinpoly` in `spec/decl_markers.tsv`, with the names read from
`spec/check_port.py --json` (§13.6a's trap). Everything else is done:

* **presentation** — `capstone.json` updated (+34/−12, two premises, two proof
  steps, section G, and two new `definition` entries for the vocabulary), the sheet
  regenerated and elaborated at exit 0 / 0 errors (§13.5a). Note for next time: the
  renderer does **not** derive statement text from Lean, and `--check-only` does not
  either, so a stale JSON still produces a compiling sheet;
* **`spec/ModularCurveConsumer.lean` zone M** — prose rewritten (the `Inputs`-era
  sentence and the "htw/hsp stay arguments" sentence were both false) and four
  `#check`s added, including `jqN_mem_modularFunctionField_of_hall` and
  `Nome.pushedMinpoly`; the file elaborates with 0 errors;
* **`TOPIC-descent.md` §2** marks itself the retirement record for both statements.

The library and both spec/presentation files are green without that last row; it is
the only piece of checker bookkeeping the wave leaves open, by your instruction to
leave the checker until last.

---

## 15. Wave 7f — the level bounds go to `NumberTheory/`, and a legacy module is regularised

**Status: landed 2026-11-04.** `hall_all`'s most-repeated step — "a positive factor is
below its prime multiple" — was factored out inside `Capstone.lean` as a `private`
helper. It is the *same* step in the C-layer twin (`PrimePowerStepAnyField.lean:1490`,
`:1500`) and the same `p ^ k * M` case split recurs there (`:1515`), and a private
helper cannot be shared. So the two bounds moved to their subject home, and the home
had a standard to meet.

### 15.1 The two shared bounds

`FLTForHuman/NumberTheory/DedekindPsi.lean`, new section `### The proper-divisor bound`
(+23 lines):

```lean
theorem lt_of_mul_prime_eq {m p N : ℕ} (hm : m ≠ 0) (hp : p.Prime) (h : m * p = N) : m < N
theorem exists_eq_succ_of_eq_pow_mul {d M p k : ℕ} (h : d = p ^ k * M) (hpd : p ∣ d)
    (hpM : ¬ p ∣ M) : ∃ a, k = a + 1
```

The second is the *statement the callers want*: both sites write
`obtain ⟨a, rfl⟩ := …` and then use `a`, so exporting `k ≠ 0` (the first draft) would
have left the `Nat.exists_eq_succ_of_ne_zero` call at every site. The module's own
`dedekindPsi_mul_prime` already uses `Nat.exists_eq_pow_mul_and_not_dvd` in this shape,
so the bound is stated the way the module thinks.

Three module-local helpers carry the induction's arithmetic, all `private` in
`Capstone.lean` because each has one consumer and the C-layer twin's block is a different
statement:

| helper | home | what it replaces |
|---|---|---|
| `exists_eq_mul_pow_succ_of_ne_one` | `Capstone` (private) | the nine-line setup: `set p := d.minFac`, `Nat.minFac_prime`, `exists_eq_pow_mul_and_not_dvd`, the nonzero derivation, the `p ^ k * M → p ^ (a + 1) * M` successor step and the re-oriented equation |
| `lt_of_eq_mul_pow_succ` | `Capstone` (private) | the step down `M * p ^ a < d`, previously three lines plus a divisibility witness `⟨p, …⟩` |
| `mul_pow_succ_eq` | `NumberTheory/DedekindPsi` | `M * p ^ (a + 1) = M * p ^ a * p`, previously two `by rw [pow_succ, mul_assoc]` clauses |
| `dedekindPsi_mul_prime_pow_succ` | `NumberTheory/DedekindPsi` | the five-line `hpsi` case split over `a = 0` / `a ≠ 0` |

The dividing line between the two homes is the subject, not the consumer count: a statement
about this proof's own data (`d`'s decomposition, the bound below it) stays `private` in the
consumer; standard arithmetic on the objects an upstream module already owns (`ψ`'s
recurrence, the prime-power shape) goes upstream. The module's own `dedup` reports 0
clusters either way.

The wrapper `hprop` went too: it packaged `ih` at a lower level behind a divisibility
hypothesis, and both of its call sites can produce `m ≠ 0` themselves. `hall_all` is
**71 → 40 lines** across the pass; no inline arithmetic proof is left in it, and the `ψ`
step is one `rw` plus one `exact`.

Mathlib: the ingredient is `lt_mul_of_one_lt_right` (`Algebra.Order.GroupWithZero.Basic`);
the composite does not exist (`grep lt_of_dvd` over `Mathlib/Data/Nat` finds nothing),
and the divisibility form `Nat.le_of_dvd` + `lt_of_le_of_ne` does not fit — call sites
hold an equation `d = p ^ k * M`, not `M ∣ d`, so they would pay a `⟨p, …⟩` witness each
time.

### 15.2 The consumers

* `Capstone.lean`: the two `private` copies deleted (−16 lines, 255 → 239); `hall_all`
  uses the shared bounds at its two sites and stays 57 lines.
* `PrimePowerStepAnyField.lean`: four blocks collapsed to one line each — the two
  identical `have hMd : M < d` derivations and the `∃ a, e = a + 1` case split.
  `check_port` still reports **50 ok**, unchanged (proofs only).

### 15.3 Two legacy modules were regularised

Both `NumberTheory/DedekindPsi.lean` and `Defs/PhiAtSlot.lean` had no `spec-pin:`
header: they were owned by the frozen `spec/old_check_stmts.py`. Touching either
triggers the standard in [../instructions.md](../instructions.md) §"Legacy Modules",
so both were done in this pass.

| requirement | what was done |
|---|---|
| `spec_pin` | **7 wires**: `Definitions/Def_ModularCurve_X0.lean` (the def and `_one`), `P2M/Sol/S_ModularCurve_card_primCosetReps_eq_dedekindPsi.lean` (`Psi`, `Psi_apply`, `isMultiplicative_Psi`, `card_filter_coprime_range_mul`, `dedekindPsiFibre`), five `Theorems/Thm_ModularCurve_dedekindPsi_*` wrappers |
| deletion from old checker | `PORT_FILES` entry removed; its four `OWN_PROOFS` names removed, with the block rewritten to point at the marker table (the shim `ModularCurve/Defs/DedekindPsi.lean` stays listed, and its comment was corrected: it said "both files are listed") |
| silent build | `lake build` 3.6 s, no warnings |
| no build-time blow-up | unchanged: it is a leaf for the ψ arithmetic (its own deps only) |
| no random tokens in names | the two new names are descriptive snake_case; the module predates the check |
| `dedup.py` | 21 declarations, **0 duplicate clusters** |
| `move_dead.py` | nothing to move: the two deleted helpers were `private` and their content now lives in a live module, so no public declaration became unreachable |

Result: **12 ok, 0 mismatch, 0 missing, 5 own** (`dedekindPsi_mul_prime_dvd`,
`dedekindPsi_mul_prime_not_dvd`, `card_fibre`, and the two new bounds — five `own:` rows
in `spec/decl_markers.tsv`, each with its reason). The module left the unwired register.

`Defs/PhiAtSlot.lean` got the same treatment, from its own provenance block:

| requirement | what was done |
|---|---|
| `spec_pin` | **2 wires**, both `S_` files the header names: `S_ModularCurve_jqN_prime_not_mem_full.lean` (14 `ok`, lines 106–391 and 748–756) and `S_ModularCurve_jqN_pow_not_mem_adjoin_full.lean` (2 `ok`, lines 414, 426) |
| deletion from old checker | `PORT_FILES` entry removed, with the topic-14 comment rewritten to say what remains owned there (`PhiSlotRoots.lean`) |
| silent build | `lake build` 4.0 s, no warnings |
| `dedup.py` | 22 declarations, **0 duplicate clusters** |
| `move_dead.py` | nothing to move |

Result: **18 ok, 0 mismatch, 0 missing, 4 own** — the four `ModularCurve.Nome`
declarations (`nomeMap`, `pushedMinpoly`, `pushedMinpoly_def`, `nomeMap_qExpand`), which
is exactly the §14.6 item that had been parked. Both modules are out of the unwired
register.

A naming note: `check_port --json` reports these four as `ModularCurve.Nome.nomeMap`
etc. — fully qualified — whereas the probe in §13.6a had produced an unqualified name
for a declaration at a module's end. The rule that survives is the operational one: read
the name out of `--json`, do not type it.

Two things worth recording about the wiring, both found by trying:

* the `missing` notes' "identical statement at … (not in this wire)" hints are
  actionable: `Psi`/`Psi_apply`/`isMultiplicative_Psi` wanted the `S_` file, and one
  attempt to wire `S_ModularCurve_exists_phiIrreducible.lean` for
  `dedekindPsi_mul_prime_not_dvd` turned its sibling `_dvd` into a **mismatch** (that
  file has a same-named declaration with a different statement). Net: 14 ok became 13
  ok + 1 mismatch, so the extra wire was dropped and both case splits went to `own:`.
* a port-own declaration in a *wired* module costs an `own:` row; there is no
  "tier 2 by default".

### 15.4 The friction note, and doc cross-references removed

The technical hazards the wave cost build rounds on — the `Fact`/`NeZero` instance chain,
the `p ^ k * M` orientation, `one_mul` versus `mul_one`, `▸` rewriting too much, the
cascade from a `Defs/` edit, the checker's parsed names — are catalogued in
[TOPIC-refactor-friction.md](TOPIC-refactor-friction.md), and the instance one is pinned
down by a re-runnable example in the shelf,
[`Reserve/Example/FactPrimeNeZero.lean`](../../Reserve/Example/FactPrimeNeZero.lean). They
live there rather than in the Lean sources: comments of that length in a proof hurt more
than they help, and a `fail_if_success` guard is a claim the build checks.

`instructions.md` also says: no cross-references to docs or ported modules in headers
and comments. The wave-7 edits had put four `TOPIC-…md §` references into
`Descent.lean` (header and two theorem docstrings). They are gone; the header now
records the retirement in its own words. `grep -c "TOPIC-"` on the module: 0.

### 15.5 State of the wave

Nothing is parked. Every module the wave edited is now green, silent and at standard:

| module | tier | `check_port` |
|---|---|---|
| `NumberTheory/DedekindPsi.lean` | 1 (wired) | 12 ok + 7 own |
| `Defs/PhiAtSlot.lean` | 1 (wired) | 18 ok + 4 own |
| `FunctionFieldGeneration/PrimePowerStepAnyField.lean` | 1 (wired) | 50 ok, unchanged |
| `FunctionFieldGeneration/Descent.lean` | 3 | not diffed (both statements port-own) |
| `FunctionFieldGeneration/Capstone.lean` | 1 (wired) | 4 ok, unchanged |
| `FunctionFieldGeneration/DescentFromSlots.lean` | 3 | not diffed (new module) |

The tree build the user schedules at the end of the wave is the first thing that
rebuilds the consumers of the two regularised modules; nothing here needs one.

---

## 16. Wave 7g — the reduction's proof body, and `subst`'s direction

**Status: landed 2026-11-04.** §14 fixed the *statement* of
`modularFunctionField_eq_full_of`; the body was still the pin's, carrying its
arithmetic inline and one substitution pointing the wrong way. The two repairs
are the treatment in the case note §4.5, one level below the statement, and both were
user-named at the node: `N` should substitute `d` at `d = N`, and the setup for
`hall`/`hmem` should not be the proof.

1. **`subst` eliminated the theorem's subject.** `rcases eq_or_ne d N with rfl` is
   a `subst`, and `subst` eliminates the *right-hand* side, so at `d = N` it
   eliminated `N`: the `d = N` branch's goal became
   `(qExpand ℚ d) jq ∈ modularFunctionField d`, with `hdN : d ∣ d`. Provable, and
   read backwards. The branch now names the equation and writes `subst d`.
2. **The arithmetic is one `obtain`, in one `private` helper.** Fifteen lines of
   `minFac` bookkeeping (the decomposition `N = (d * m') * p`, `m' ≠ 0`, its
   `NeZero`, the bound `d * m' < N`) became `exists_mul_prime_lt_of_dvd_of_ne`,
   `private` in the consumer: the level `m` the induction hypothesis is taken at
   and the prime `p` its step is taken by are this reduction's own data — §2
   step 5's dividing line, the same one `hall_all`'s helpers were placed by.
   The branch's other step (`Gen m` and `jqN m ∈ F_N` give `F_m^full ≤ F_N`) was
   factored too in the first cut and then put back: its whole content is
   `adjoin_le_iff` applied to the two generators of `F_m`, so it is four lines
   inline, where a reader sees the generators named. A helper with no content of
   its own is a name to look up, not a lemma.

### 16.1 Measurements

| item | before | after |
|---|---|---|
| the reduction's proof body | 34 lines | 17 |
| the node's private helpers | 0 | 1 (15 lines of statement and proof) |
| statement | `∀ m < N, m ≠ 0 → Hall m` | unchanged |
| `Capstone.lean`, `spec/ModularCurveConsumer.lean` | green | unchanged (`0` errors) |

The body now reads: the case split, the level (`obtain`), `Hall m` (the
induction hypothesis), the descent transported along `N = m * p`, the inclusion,
the conclusion.

**The inlining costs no build time** — the helper was factored for readability,
not to keep the module fast. Measured on the module, `lake env lean` (warm
oleans, nothing else running): 6.3 s wall / 3.4 s user inlined, 5.1 s / 3.3 s
with the helper restored; a clean `lake build` of the module 5.9 s. Elaboration
cost tracks the tactics, not whether four lines sit in a `private` block.

### 16.2 Gates

```bash
cd lean
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.DescentFromSlots  # silent, 5.9 s
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone           # silent, 4 s
python3 spec/check_port.py FLTForHuman/ModularCurve/FunctionFieldGeneration/DescentFromSlots.lean --force  # tier 3
python3 spec/unwired_register.py --rebuild   # `UNWIRED-PUBLIC.md` unchanged: 2 public declarations
cd ../tools/deps && python3 dedup.py --module DescentFromSlots --no-json   # 0 duplicate clusters
```

`#print axioms ModularCurve.modularFunctionField_eq_full_of` and on
`ModularCurve.functionFieldGeneration`: `[propext, Classical.choice, Quot.sound]`,
before and after.

### 16.3 The trap, recorded

Both repairs are in the friction note (§3): the `subst` orientation, with the
goal state it produced, and the second instance of `rw` rewriting inside
`m'.minFac` (the idiom is `conv_lhs => rw [hm', hm]` then `ring`).

### 16.4 `jqN_mem_modularFunctionField_of_hall` after §14: an inner seam, not the capstone's interface

§14's statement refactor moved the capstone's `Gen` half up one level, to
`modularFunctionField_eq_full_of N ih`. The consequence was not followed through:
`jqN_mem_modularFunctionField_of_hall`'s docstring still said "the form the
capstone's strong induction consumes", and the layer-0 consumer spec's prose said
"the form the capstone calls". Both became false in that move, and a reader who
checks the claim finds a theorem whose only code consumer is the reduction in its
own module — hence "it doesn't seem to do anything".

What it does, stated precisely:

* **mathematically**, it is T15's descent, not the generator membership: the two
  generators of `modularFunctionField (M * p)` are `j(q)` and `j(q ^ (M * p))`, and
  `j(q ^ M)` is neither, so `Hall M → jqN M ∈ F_{M * p}` is the content, not a
  definitional fact;
* **mechanically**, it adds no proof — it is `jqN_div_mem_modularFunctionField` at
  `K = CyclotomicField (M * p) ℚ`, `ζ = cycUnit (M * p)`, with `htw`/`hsp`
  discharged by `htw_of`/`hsp_of`. It is the only declaration in the port where this
  step names `K`, `ζ` or an `IsRoot` predicate.

So the honest sentence is "the seam one level below the reduction": a caller of
`modularFunctionField_eq_full_of` never names a certificate, and this theorem is
where the certificate is named once. Both docstrings now say that.

**Measured, should it be deleted instead.** Removing it and inlining its single
call site compiles: the module goes 235 → 222 lines, and the call site grows by
five (`cycUnit (m * p)`, `cycUnit_spec (m * p)` and two
`isPrimitiveRoot_pow_div … ⟨p, rfl⟩` witnesses). It stays because it is the
module's public statement of the descent and the layer-0 consumer spec checks it
(`#check` at `spec/ModularCurveConsumer.lean`); if that surface is ever narrowed,
this is the line to cut, and the spec's `#check` goes with it.

**Its proof, rewritten so the specialization is visible.** The old body was a single
function-style term:

```lean
  jqN_div_mem_modularFunctionField M p (cycUnit (M * p)) (cycUnit_spec (M * p))
    (fun w hw => htw_of M p (cycUnit (M * p) ^ (M * p / M))
      (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM w hw)
    (hsp_of M p (cycUnit (M * p) ^ (M * p / M))
      (isPrimitiveRoot_pow_div (cycUnit_spec (M * p)) ⟨p, rfl⟩) hallM)
```

Three things a reader had to decode, each now named on its own line:

* **`K`** — inferred as `CyclotomicField (M * p) ℚ` and therefore invisible. It is now
  in `hζ`'s type and again in `htw`/`hsp`'s, so the two `IsRoot` predicates the
  descent consumes can be read at all;
* **`isPrimitiveRoot_pow_div hζ ⟨p, rfl⟩`** — the `⟨p, rfl⟩` is a `Dvd` *witness*, not
  the order: the lemma's implicit `{p}` (its target order) binds to `M`, and the outer
  `p` is the cofactor. `isPrimitiveRoot_pow_div hζ (dvd_mul_right M p)` says it;
* **`fun w hw => htw_of … w hw`** — an eta-expansion of `htw_of`'s last two binders;
  `htw_of M p ζ hζM hallM` already *is* the `∀ w, … → w = 1` the descent asks for.

The body is now four `have`s (`hζ`, `hζM`, `htw`, `hsp`) and one application with the
descent's six explicit arguments: 15 lines instead of 6, and no inline comment — each
`have`'s type *is* one of the descent's hypotheses, so a comment would only repeat it. It is
longer than the old term and it reads, which for the one
declaration that names the certificate is the right trade.

---

## 17. Wave 7h — one descent, one statement: the certificate goes inside

**Status: landed 2026-11-05.** This section is the wave's record; the module's shape is stated
in `Descent.lean`'s header, [TOPIC-descent.md](TOPIC-descent.md) §2.1 and case note §2. §16 left
the node with two public statements of one theorem:
`Descent.lean`'s `jqN_div_mem_modularFunctionField` (taking `K`, `ζ`, `hζ`, `htw`, `hsp`) and
`DescentFromSlots.lean`'s `jqN_mem_modularFunctionField_of_hall` (`Hall M` only), the second
discharging the first. The record's verdict is now the case note's §4: the wave-7 trigger was a
*bad signature*, and the fix for a bad signature is to push the invariant in, not to invent
names for the certificate or to state the theorem a second time one module down.

### 17.1 What changed

1. **One theorem.** `jqN_div_mem_modularFunctionField` now takes
   `(M) [NeZero M] (p) [Fact p.Prime] (hallM : Hall M)` and concludes
   `jqN M ∈ modularFunctionField (M * p)`. Its proof is the certificate, in four lines
   (`cycUnit (M * p)`, its `((M * p) / M)`-th power, and the two slot facts from `htw_of`/
   `hsp_of`), and one application of the engine. `jqN_mem_modularFunctionField_of_hall` is
   gone.
2. **The engine has no statement.** The pin's T15 text — the unique-common-root argument given
   `ζ`, `hζ`, `htw`, `hsp` — is the body of the one public theorem, after four lines that fix
   `K := CyclotomicField (M * p) ℚ`, `ζ := cycUnit (M * p)` and the two root conditions at
   `ζ ^ ((M * p) / M)`. An intermediate cut had it as a `private theorem
   jqN_mem_of_root_conditions` taking those four arguments; that is the same interface one
   visibility level down, and it was withdrawn — the point of the merge is that the bad
   signature has no home left.
3. **The two modules merge back into `Descent.lean`.** The refactor had created
   `DescentFromSlots.lean` in the same commit that introduced the second statement
   (`2d3fa8c`, 2026-11-04), so the duplicate and the extra module were one mistake. With one
   statement the seam module holds nothing of its own; the descent, its slot facts, the engine
   and the one-prime reduction all live in `Descent.lean`, which is the pin's node name and was
   the module that carried both statements before the refactor. The pin's own file has them
   together too (`S_ModularCurve_modularFunctionField_eq_full_of.lean`: descent 553–690,
   reduction 694–727).
4. **The invented vocabulary went private with its consumer.** `nomeMap`, `pushedMinpoly` and
   `nomeMap_qExpand` moved from `Defs/PhiAtSlot.lean` into `Descent.lean` as `private`;
   `pushedMinpoly_def` had no consumers left and was deleted. The four `own:` rows in
   `spec/decl_markers.tsv` went with them.

The `Hall` statement's proof needs T19's slot product, so `Descent.lean` now imports
`SlotProduct` — it did not before the wave. That is the honest dependency of the theorem the
port states; the certificate-taking engine, which needs no T19, is private and could move
upstream again if a second consumer ever appeared. The dependency order is the interface (case
note §7.5), so the module that *states* the friendly theorem is the module that can prove it.

### 17.2 Measurements

| item | before | after |
|---|---|---|
| modules for the node | 2 (`Descent` 249 + `DescentFromSlots` 236) | 1 (`Descent`, 412) |
| public statements of the descent | 2 | 1 |
| `ModularCurve/Defs/PhiAtSlot.lean` | 289 | 247 |
| `check_port` on `Defs/PhiAtSlot.lean` | 18 ok + 4 own | **18 ok + 0 own** |
| `spec/decl_markers.tsv` rows for the vocabulary | 4 | 0 |
| the descent's statement | 6 lines, `K`/`ζ`/`htw`/`hsp` | 3 lines, `Hall M` |
| unwired register | 108 modules | 107 |

Consumers touched: `Capstone.lean` (its import and two sentences), the layer-0 consumer spec
(import, one `#check` removed, zone M and the descent note rewritten), the presentation JSON
(statement, `math`/`note`, file/line, the two vocabulary `definition` entries and the section-A
list), and the sheet, regenerated.

### 17.3 Gates

```bash
cd lean
timeout 110 lake build FLTForHuman.ModularCurve.Defs.PhiAtSlot                            # silent
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Descent             # silent
timeout 110 lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.Capstone          # silent
python3 spec/check_port.py FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean --force   # 18 ok, 0 own
python3 spec/check_port.py <Descent> --force                                      # tier 3, not wired
lake env lean spec/ModularCurveConsumer.lean    # 0 errors
python3 presentation/render.py presentation/function-field-generation/capstone.json
lake env lean presentation/FunctionFieldGenerationCapstone.lean   # 0 errors
python3 spec/unwired_register.py --rebuild
```

`#print axioms` on `ModularCurve.jqN_div_mem_modularFunctionField`,
`ModularCurve.modularFunctionField_eq_full_of` and `ModularCurve.functionFieldGeneration`:
`[propext, Classical.choice, Quot.sound]` — unchanged, as it must be: this wave changes no
mathematics, only where the certificate lives.
