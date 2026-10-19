# WORKORDER-AC1 — the archimedean Casimir definition layer (landing record)

**Status: landed.** This order was executed by the manager as the column's §4(a) ground for the
arch-Casimir subject; it is recorded here because
[TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) §4–§5 cites it, and because
[WORKORDER-AC2-cascore-trio.md](WORKORDER-AC2-cascore-trio.md)'s set has it as its only premise.

## 1. Scope

Home, whole node (playbook §2.3), the two pin `Definitions/` modules the arch-derivative subject is
phrased against:

| pin module | lines | declarations | `private` | pin importers |
|---|---:|---:|---:|---:|
| `Definitions/Def_LanglandsTunnell_ArchParam.lean` | 139 | 33 | 0 | 74 |
| `Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean` | 445 | 58 | 0 | 339 |

**Not this order:** the Complex pair (`…ArchDerivCasimirComplex` 196, `…ComplexAPI` 381) and
`Def_LanglandsTunnell_ArchCasimirCompanion` (61, dragging the unported
`Def_LanglandsTunnell_JLConverse`); any proof file; any edit to an existing module; the checker
wiring beyond appending four lines.

## 2. Deliverables

| port module | pin source | shape |
|---|---|---|
| `FLTForHuman/LanglandsTunnell/ArchParam.lean` | `Def_LanglandsTunnell_ArchParam.lean` | verbatim; the pin's single mathlib import kept |
| `FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimir.lean` | `Def_AutomorphicForm_ArchDerivCasimir.lean` | verbatim; the four `Definitions/` imports replaced by the four port modules |

Both are **all public** in the pin, so no promotion is owed and no `private` re-derivation was
allowed: every declaration is transcribed at the pin's name, and the checker verifies each by dotted
name. Theory homes, not `Def_`-named files, per playbook §3.1: `LanglandsTunnell/ArchParam.lean`
sits beside the port's other `LanglandsTunnell` module (`TateLocalZeta.lean`), and
`AutomorphicForm/Adelic/ArchDerivCasimir.lean` beside `ArchType.lean` and
`ArchWeightCharTransport.lean`, whose declarations it composes.

**Import narrowing.** `Def_AutomorphicForm_ConstantTerm.lean` has the pin's `import Mathlib`; the
port had already replaced it with five specific modules, and this order keeps that narrowing rather
than re-widening it. `ArchParam.lean` needs exactly `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne`.

**One drift fixed.** `archRealLiftAt_of_det_ne_zero`'s proof was `dif_pos h` at the pin; mathlib
`v4.34.0` deprecates it in favour of `dite_eq_left h`. The statement is unchanged — only the proof
term — and the warning-free build is what forced the change.

## 3. Build and checker record

| step | command | result |
|---|---|---|
| tier-1 loop, `ArchParam` | `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 …` | exit 0, 0 warnings, 21.6 s |
| tier-2 build, `ArchParam` | `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.LanglandsTunnell.ArchParam` | green, 2,847 jobs, 3.5 s |
| tier-1 loop, `ArchDerivCasimir` | as above | exit 0, 0 warnings, 7.3 s (one `dif_pos` deprecation fixed first) |
| tier-2 build, `ArchDerivCasimir` | `… lake build FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir` | green, 3,533 jobs, 9.5 s |
| checker, before (HEAD spec, same tree) | `python3 spec/check_flt_statements.py` from `git show HEAD:lean/spec/check_flt_statements.py` | 10,013 identical (667 promoted, 83 renamed), 0 / 0, 42 own (10,055 checked) |
| checker, after | `python3 spec/check_flt_statements.py` | **10,104 identical (676 promoted, 83 renamed), 0 mismatched, 0 missing, 42 own (10,146 checked)** |
| register | `python3 tools/deps/unwired_register.py --check` | `register is current` — correct, nothing here is tier 3 |

**The delta is +91** and it is per module exactly the pin's declaration count: +33 for `ArchParam`
(measured alone: 10,013 → 10,046) and +58 for `ArchDerivCasimir` (alone: 10,013 → 10,071). Nothing
else in the tree moved: `git status` showed only the two new modules and the four spec lines.

**A note on the promoted counter.** It moved 667 → 676 (+9) although neither pin file has a
`private` declaration. The nine are the short dotted names of `IsArchSmoothAt`'s method lemmas
(`add`, `smul`, `neg`, `sub`, `comp_mul_left`, `comp_mul_right`, `differentiableAt_flow` and their
kin): the instrument keys by last name, and those last names are also carried by pin-`private`
declarations elsewhere. The pairing is still correct here — the pin's own last-name map for
`Def_AutomorphicForm_ArchDerivCasimir.lean` resolves `add`, `smul`, `neg`, `sub`,
`comp_mul_left`, `comp_mul_right`, `differentiableAt_flow` to the `IsArchSmoothAt.*` statements —
but a *later* consumer of this layer must not read the promoted counter as evidence of promotion.
This is the column's documented last-name blindness (PORTING-DeligneSerre §6, §9) appearing in the
promoted column rather than the exempted one.

## 4. Wiring

Appended last to both lists, with the comment block naming this order and the topic note:

* `SOURCES`: `Definitions/Def_LanglandsTunnell_ArchParam.lean`,
  `Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean` — a definition module has no `Theorems/`
  wrapper, so both verify by name against their `Definitions/` files (the same convention as the
  `TateFormal`/`TateSlots` pair).
* `PORT_FILES`: `FLTForHuman/LanglandsTunnell/ArchParam.lean`,
  `FLTForHuman/AutomorphicForm/Adelic/ArchDerivCasimir.lean`.

## 5. What this unblocks

The whole arch-derivative subject: 78 pin `S_` files in the D-S `needed` set (43 real-place /
17,361 raw lines, 35 complex / 16,365 raw lines — 24,111 net new after dedup) phrase against these
declarations. The first proof set,
[WORKORDER-AC2-cascore-trio.md](WORKORDER-AC2-cascore-trio.md) (the real-place `CasCore` trio), has
**landed** on top of this ground: checker `10,104 → 10,107` (+3 for the three headlines), with the
rest of that module's public surface registered tier 3. The complex half additionally needs the
Complex pair homed (§1, not this order).
