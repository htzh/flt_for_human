# WORKORDER Z1 — the completed Dedekind zeta package

**Status (2026-10-12): order written; dispatch 1 (waves 1–2) running.** One dispatch =
two waves = two modules, ≈1.5k pin lines; the five dispatches run in series with the
manager's review between, and the manager re-issues each against the tree that exists
after that review. §4 holds the dispatch table.

**Audience.** A fresh session with no memory of the reconnaissance. Read §3 twice:
it is the protocol, and it is the part of this order that is new. The method is
[porting-playbook.md](../../porting-playbook.md) §2.3–§2.6, §3.3–§3.5, §4, §5.

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is
`v4.34.0`. The silo is
[`P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean)
(7,555 lines) and its
[`Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean`](https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_exists_completedDedekindZeta_package.lean)
wrapper.

**Companions.** [PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §7 (the
ray-class interface this package feeds);
[studies/deligne-serre-weight-one-scout.md](../../../studies/deligne-serre-weight-one-scout.md)
§3.1 (the shared ray-class input);
[spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md) (the register this order
feeds); [CARRY-FORWARD.md](../../CARRY-FORWARD.md).

## 1. Scope

Port the pin node `NumberField.exists_completedDedekindZeta_package` — the classical
theta/Poisson-summation proof of the analytic continuation, functional equation and
growth bounds of the completed Dedekind zeta function — as a **mathlib-shaped theory
with natural names**, in themed modules, with the one consumed theorem exposed
through a thin façade. 388 public declarations, 7,555 pin lines, no `private`
declaration in the pin, no `Definitions/` dependency.

**Explicitly not this set**

* the two sibling silos that re-declare the same obligation vocabulary —
  `S_NumberField_exists_hadamard_logDeriv_expansion_of_completedZeta_package.lean`
  (5,932 lines, bodies routed through its own `S18.HADPkg` class) and
  `S_NumberField_archTermDerived_le_log_abs_discr.lean` (7,676 lines, imports this
  package *and* re-declares the vocabulary). Of the 81 names they share with this
  silo, 27 are the same name with a **different proposition**; they are separate
  developments, not copies, and are not ported here;
* the ten consumers of the headline (§2) — each is its own node;
* the two definitions the pin's own `import` block names are `Mathlib` and a
  127-line tactic file; there is no definition layer to port.

## 2. What the reconnaissance measured

| quantity | value |
|---|---|
| silo | 7,555 lines, 388 public declarations, **zero `private`** |
| imports | `Mathlib` + `P2M.Util` (a `p2m_exact_reverting` tactic file) — no pin module |
| metadata | `stmt_defs` and `proof_defs` both empty |
| external consumers | **one declaration** — the headline, cited by 10 pin files, all importing the wrapper |
| same-file closure of the headline | 359/388 declarations, 6,773/7,281 lines (**93%**) |
| `port_advise` substitutions | 0 real (63 "hits", all the binder-less `def … : Prop` artifact) |
| prefixed names | 305 of 389 carry `gapsw80_tN_` / `kwDyf2_`; stripping leaves 303 distinct tails and **2 collisions** |
| mathlib | has `NumberField.dedekindZeta` (definition and residue) only — no continuation, no functional equation |

The package is therefore **all-or-nothing**: the headline is the composition of the
whole `t1…t70` obligation skeleton, so there is nothing to trim and everything to
transcribe. The register exists so that the reused-but-unwired part stays findable.

The ten consumers of the headline, for orientation: the three
`NumberField.TateGlobal.*` nodes, `NumberField.archTermDerived_le_log_abs_discr`, the
ray-class functional-equation node
`NumberField.exists_completedRayL_functionalEquation_of_primitive`, and the five
`NumberField.exists_*dedekindZeta*` analytic nodes. The last two of the five —
`exists_differentiableOn_eq_tprod_inv_one_sub_absNorm_cpow_neg_and_tendsto_sub_one_mul`
and `exists_differentiable_eq_sub_one_mul_dedekindZeta_and_apply_neg_two_mul_add_one_eq_zero`
— are the ones the Deligne–Serre cone needs.

## 3. The protocol

### 3.1 Natural names, no obligation prefixes

The pin's names are proof-skeleton numbering inherited from the pin's source
(`gapsw80_t9_…`, `kwDyf2_…`; the file even namespaces them `Gapsw80T10DedekindZetaBridgeA1Discharge`).
**Nothing in the port may carry them.** The rule:

1. strip the prefix; the tail is the name (`gapsw80_t9_completedDedekindZeta_FE` →
   `completedDedekindZeta_FE`);
2. expand mechanical abbreviations into words (`_FE` → `_functionalEquation`,
   `_DE` → `_differentiableOn` where that is what the tail means);
3. a reader who knows only mathlib must be able to guess what the declaration
   states. If a tail does not carry that (`A1_closed`, `t43_L₀`, `P`, `xi`), rename
   it to describe the mathematics;
4. two collisions must be resolved by hand: `completedDedekindZeta` occurs twice
   (a `(K) (s : ℂ) : ℂ` form and a `(s : ℂ) : ℂ` form — the second has `K` as a
   section variable) and `summable_thetaTerm` twice. Use distinct descriptive names.

Namespaces: use one natural theory namespace, `NumberField.CompletedDedekindZeta`,
for the development. Do **not** reproduce the pin's per-obligation `namespace
FLT.Gapsw80T…` / `end` blocks (they exist to drive `p2m_export` visibility) and do
**not** transcribe any `p2m_export` / `p2m_open` / `p2m_reactivate` line.

### 3.2 Provenance comments — the translation lives in the register

Every transcribed declaration carries, on the line immediately above it, the pin
original:

```lean
-- pin: gapsw80_t9_completedDedekindZeta_FE (S_NumberField_exists_completedDedekindZeta_package.lean:279)
theorem completedDedekindZeta_functionalEquation … := …
```

Both the name and the `file:line` are required; the register
(`spec/UNWIRED-PUBLIC.md`, generated by `tools/deps/unwired_register.py`) reads this
comment to fill its `pin original` column, so the mapping survives renaming and the
register needs no hand-editing. The register is the *only* place the pin's names
appear — the Lean side is natural throughout.

### 3.3 Statements verbatim modulo the name; proofs adapted

* A **statement** is the pin's, character for character after the checker's
  normalisation — the name itself and references to renamed siblings being the only
  permitted differences. Recover the pin's own text from §10's extraction commands
  rather than retyping it.
* A **proof** is adapted to the port's mathlib freely. If a proof needs a statement
  to change, that is a stop condition (§8), not a judgement call.
* The `def … : Prop` obligations are the pin's goals written as propositions. Keep
  them, name them for what they assert, and keep the proposition as the body — they
  are the skeleton the assembly composes, and their bodies are the mathematics.

### 3.4 The tier-3 home and the tier-1 façade

* The development modules are **public and not listed in `PORT_FILES`** — tier 3.
  That is deliberate: the checker's contract is the exposed API, and a whole
  development wired without a consumer is verification nobody asked for. They build,
  they are importable, and `spec/UNWIRED-PUBLIC.md` lists what they hold. Re-run
  `tools/deps/unwired_register.py` at the end of every wave, and never hand-edit the
  register.
* The **façade** `FLTForHuman/NumberTheory/NumberField/CompletedDedekindZeta.lean`
  imports the last module and states the consumed headline at the pin wrapper's
  name, `NumberField.exists_completedDedekindZeta_package`, taking the statement text
  from the `Theorems/` wrapper (playbook §4: the wrapper's binders, the `S_` file's
  body). It is the **only** module added to `PORT_FILES`.
* A future consumer that wants one of the development's declarations imports it
  directly — no edit, no cascade — and the manager wires it (or renames it) then.

### 3.5 What not to do

* Do not add a second copy of a declaration to make a proof easier.
* Do not add file-wide `set_option maxHeartbeats` / `synthInstance.maxHeartbeats`.
  The pin sets 6,400,000 / 800,000 for the whole file; the port's global cap is
  4,000,000. If a proof genuinely needs more, use a per-declaration
  `set_option … in` with a `-- pin: …`-style note and **report it** in the wave's
  hand-off; do not touch the lakefile.
* Do not touch any other module: not the siblings, not the consumers, not the
  checker beyond this order's own wiring in the last wave.
* Do not port `P2M.Util`; `p2m_exact_reverting` is a transcription device, not
  mathematics.

## 4. Deliverables and the wave plan

One wave = one module = one dispatch. Waves are consecutive prefixes of the pin file,
which is in dependency order, so every wave compiles when appended after its
predecessors. Boundaries are pin line ranges.

| wave | pin lines | decls | module (proposed) | theme |
|---:|---|---:|---|---|
| 1 | 1–540 | 34 | `NumberTheory/NumberField/CompletedDedekindZeta/Lattice.lean` | inner products and quadratic forms; `nK`, the ideal lattice, `coordMatrix`, `thetaTerm`; the two headline obligations (`t1`, `t3`, `t15`) |
| 2 | 541–1542 | 17 | `…/Poisson.lean` | positivity and summability of the theta terms, Schur complements, the Poisson transformation law |
| 3 | 1543–1964 | 43 | `…/Places.lean` | archimedean places, `Dscale`, `scaledGram`, the ideal Gram matrix and its determinant |
| 4 | 1965–3148 | 84 | `…/ThetaKernel.lean` | the multiplication sign, `Phi`, `idealBasisK`, the bivariate theta kernel |
| 5 | 3149–4300 | 59 | `…/Mellin.lean` | the Mellin transform, `placeParam`, the archimedean Gamma factors |
| 6 | 4301–5418 | 22 | `…/Unfolding.lean` | the orbit integral: unfolding the theta integral to the completed partial zeta (`heckeLambda_eq_completedPartialZeta`) |
| 7 | 5419–6025 | 49 | `…/CompletedZeta.lean` | `constK`, class representatives and covolumes, the completed zeta, its functional equation, the `T1` bridge, the `t11`/`t32`/`t42` obligations |
| 8 | 6026–6900 | 51 | `…/Hadamard.lean` | `xi`, its Hadamard product and the order/strip bounds (`kwDyf2`), `nK` casts, contour steps |
| 9 | 6901–7555 | 31 | `…/Bounds.lean` | the effective Gamma/Discriminant bounds (`t16`, `t36`, `t43`) and the assembly |
| 9b | — | 1 | `NumberTheory/NumberField/CompletedDedekindZeta.lean` (façade) | the consumed headline at the wrapper's name; **listed** in `PORT_FILES` |

**A dispatch is two consecutive waves** — two modules, ≈1.5k pin lines — which is the
unit one subagent runs. Dispatches run **in series**, one at a time, with the manager's
review between; never two at once.

| dispatch | waves | pin lines | decls | modules |
|---:|---|---:|---:|---|
| 1 | 1–2 | 1–1542 | 51 | `Lattice`, `Poisson` |
| 2 | 3–4 | 1543–3148 | 127 | `Places`, `ThetaKernel` |
| 3 | 5–6 | 3149–5418 | 81 | `Mellin`, `Unfolding` (the heavy pair: 2,270 lines) |
| 4 | 7–8 | 5419–6900 | 100 | `CompletedZeta`, `Hadamard` |
| 5 | 9 + façade | 6901–7555 | 32 | `Bounds`, then the façade (the only checker wiring) |

Dispatch 1 is the order in §5; each later dispatch is the same order with the next
line range and module names. The manager re-issues it against the tree that exists
after review, and may re-cut a module boundary if a wave's theme turns out to straddle
two modules.

## 5. Dispatch 1 — waves 1 and 2

1. **Extract the pin text.** Lines 1–1542 of the silo contain the `p2m_*` scaffolding
   and the first 51 declarations, split 34 / 17 across the two modules (`Lattice` is
   the ideal lattice and the headline obligations, `Poisson` the theta transformation
   law). Take each declaration's **source lines** from the
   command in §10 — not from the checker's raw name, which carries the pin's
   `p2m_open` namespace nesting
   (`…FLT.FLT.…NumberField.mixedEmbedding.FLT.GaussianFourierPosDef.dotProduct_ofLp_eq_inner`)
   and is unusable as a name and misleading as text.
2. **Read the obligations first.** `gapsw80_t1_completedDedekindZeta`,
   `gapsw80_t1_DedekindCompletedFE`, `gapsw80_t3_idealGram` and the `t15` pair are
   `def … : Prop` goals naming what the package will prove; they fix the shape the
   rest of the development must have.
3. **Write the first module** (`Lattice`) with natural names, one `-- pin:` comment
   per declaration, statements verbatim, proofs adapted. Get it green (step 4) before
   starting the second — a module that does not elaborate is not a base for the next.
4. **Tier-0 loop** (`lake env lean`) until green with 0 warnings; then **tier 1**
   (`flock … lake build <module>`) for the module just finished.
5. **Write the second module** (`Poisson`) the same way, importing the first, and take
   it through steps 3–4.
6. **Regenerate the register** and report both waves; do not hand-edit the register.
7. **Stop.** Dispatch 2 is a separate run against the tree you leave behind.

## 6. Build discipline

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
  (writes no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done
  (writes the `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone;
* every `lake build` serialized and bounded; never raise the heartbeat cap.

Modules are sized so that this holds: the largest is ~1,200 pin lines, comfortably
inside the 300 s tier-0 bound (the port's 2,500-line modules take ~80 s). If a wave's
module does approach the bound, stop and report rather than splitting a declaration.

**Hub prohibition.** A subagent that needs a `private` helper re-derives it locally
and reports it; one that believes a promotion or a hub edit is genuinely required
**stops and reports** with the declaration, host and `build_ladder.py --edit` price.
The manager decides. Nothing in this order requires an edit to an existing module
until the last wave's checker wiring.

## 7. Verification

Per wave:

* tier-0 `lake env lean` exit 0 and **0 warnings**;
* tier-1 `flock .lake/flt_build.lock timeout 300 lake build <module>` green;
* `python3 tools/deps/unwired_register.py` regenerates cleanly, and the new module's
  rows appear with their `pin original` from the provenance comments — a row showing
  `—` where the pin has a source means a missing or malformed `-- pin:` comment;
* `git status` showing only the wave's module (plus the regenerated register).

Final wave only:

* the façade on `PORT_FILES` (one entry) and the wrapper plus the silo on `SOURCES`
  (two entries), appended last;
* `timeout 300 python3 spec/check_flt_statements.py` — **0 mismatched / 0 missing**,
  and the `identical` delta equal to the façade's public surface (the headline; plus
  whatever else the façade exposes, one row each);
* a one-token mutation on the headline moves exactly one `mismatched`, then revert;
* `#print axioms` on the headline `[propext, Classical.choice, Quot.sound]`;
* `grep` sweep: no `sorry`/`admit`/`axiom`/`native_decide`, no bare `import Mathlib`,
  no file-wide heartbeat override.

## 8. Risks and stop conditions

1. **mathlib drift.** The pin is Lean `v4.33.1`; the port is `v4.34.0`. Adapt proofs,
   never statements. A statement that will not typecheck as written is a stop.
2. **The obligation skeleton.** 63 `def … : Prop` declarations are matched *by type
   only* by the checker — but this module is not checked, so the risk is human, not
   mechanical: their bodies are the real statements and must be transcribed exactly.
3. **The `K` as a section variable.** Several declarations (`gapsw80_t9_*`) take `K`
   from a section variable while their siblings take it explicitly; keep each
   declaration's own binder shape, derived from its own pin text.
4. **Heartbeats.** If a transcribed proof exceeds the port's cap, report it with the
   declaration and its pin line rather than adding a file-wide option.
5. **Scope creep into the siblings.** `hadam` and `archT` share 81 names with this
   silo; 27 of them are different propositions. Do not import, merge or "reuse" them.
6. **Register drift.** If a `-- pin:` comment is missing, the register silently loses
   provenance. The wave's register check is not optional.

## 9. Report shape

Per dispatch, and per module within it: the module path and line count; the count of
declarations and the pin line range consumed; the provenance comments' completeness
(`N/N`); tier-0 and tier-1 results; the register's diff (rows added); anything
deferred, with the pin line; and any stop condition hit. Keep it short — the manager
reads the tree.

## 10. Reproduce the reconnaissance

```bash
cd tools/deps

# the API, its real consumers and the proof closure (the 93% figure)
python3 api_survey.py --node NumberField.exists_completedDedekindZeta_package --top 30

# the substitution check: 0 real, 63 type-only `def : Prop` artifacts
python3 port_advise.py --nodes NumberField.exists_completedDedekindZeta_package --no-drags

# what is already public but unwired, and how the register is generated
python3 unwired_register.py && python3 unwired_register.py --check

# the exact pin declarations of a wave, with their statements (lines 1-540 here)
python3 - <<'EOF'
import importlib.util, sys
from pathlib import Path
sys.path.insert(0, ".")
import port_graph as pg
spec = importlib.util.spec_from_file_location("ck", "../../lean/spec/check_flt_statements.py")
ck = importlib.util.module_from_spec(spec); sys.modules["ck"] = ck; spec.loader.exec_module(ck)
PIN = Path.home() / "proj" / "fermats-last-theorem"
F = PIN / "P2M/Sol/S_NumberField_exists_completedDedekindZeta_package.lean"
lo, hi = 1, 540
text = F.read_text(encoding="utf-8")
meta = {d["name"]: d for d in pg.scan_declarations(text)}
lines = text.split("\n")
for raw, kind, stmt in ck.raw_declarations(text):
    nm = raw.rsplit(".", 1)[-1]
    m = meta.get(nm)
    if m and lo <= (m["line"] or 0) <= hi:
        print(f"===== {m['line']}-{m['end_line']}  {kind}  {nm}")
        print("\n".join(lines[m["line"] - 1:(m["end_line"] or m["line"])]))
EOF
```

## 11. Dispatch log, and the rulings that bind later dispatches

**Dispatch 1 (waves 1–2) — landed 2026-10-12, reviewed by the manager.**
`Lattice.lean` (346 lines, 34 declarations, pin 233–540) and `Poisson.lean` (1,111
lines, 17 declarations, pin 541–1599). Tier 0 exit 0 with 0 warnings on both, tier 1
green (3,725 jobs), **51/51 statements identical** to the pin once a rename map is
applied to the references to renamed siblings, provenance comments 51/51, the register
regenerated and current, no other file touched. No heartbeat override was needed: the
pin's two (`3200000` on the `t15` pair, `25600000` on `poisson_step`) are dropped, and
the ~525-line `poissonLawBlock_of_poissonLaw` compiles inside the port's cap.

* **Boundaries are declaration-start based.** Wave 2's last declaration starts at pin
  1542 and runs to 1599, so wave 3's declarations begin at 1600. Extract by start line;
  the script prints each declaration's whole span.
* **`stdBasis` (mathlib `v4.34.0`).** v4.34.0 added `Matrix.stdBasis`, so a bare
  `stdBasis` is ambiguous with `NumberField.mixedEmbedding.stdBasis`. Verified: **none
  of the 337 remaining statements spells it bare** — it occurs only in proof bodies,
  where qualifying it (`mixedEmbedding.stdBasis`) is a permitted proof adaptation. A
  *statement* that would need qualising is a stop condition; report it.
* **Names taken in dispatch 1 — do not reuse.** `completedDedekindZeta` is pin
  `gapsw80_t1_completedDedekindZeta` (356), the closed form; the pin's
  `gapsw80_t9_completedDedekindZeta` (5491) needs a distinct name (e.g.
  `completedDedekindZeta_classSum`). `summable_thetaTerm` is pin
  `gapsw80_t2_summable_thetaTerm` (664), the generic `Fin n` statement; the pin's
  `gapsw80_t8_summable_thetaTerm` (3879) never mentions `thetaTerm` and is free as e.g.
  `summable_thetaTerm_scaledGram`. Everything already in `Lattice`/`Poisson` is listed
  in `spec/UNWIRED-PUBLIC.md`; keep new names distinct.
**Dispatch 2 (waves 3–4) — landed 2026-10-12, reviewed by the manager.**
`Places.lean` (490 lines, 43 declarations, pin 1543–1964, first declaration at 1600)
and `ThetaKernel.lean` (1,309 lines, 84 declarations, pin 1965–3148, first at 2012).
Tier 0 exit 0 with 0 warnings on both, tier 1 green, **178/178 statements identical**
across the four landed modules once the rename map is applied, provenance 127/127 for
this dispatch, register current, no other file touched. Both of the pin's heartbeat
overrides on this range are dropped (the file-wide `6400000`, and the `12800000 in` at
pin 3147 before `gapsw80_t7_heckeWeakFEPair`), and `heckeWeakFEPair` fits the port's cap.
Linter noise was cleared with proof-level repairs only — `omit [NumberField K] in` on
the 11 declarations whose statements never mention the instance (the line placed above
the `-- pin:` comment, so provenance stays immediately above the declaration), the
`v4.34.0` deprecation renames (`if_pos` → `ite_eq_left`, `continuous_finset_prod` →
`continuous_finsetProd`, …), and dropped unused `simp` arguments.

****Dispatch 5 (wave 9 + the façade) — landed 2026-10-12. The port is complete.**
`Bounds.lean` (684 lines, 31 declarations, pin 6934–7555) and the façade
`CompletedDedekindZeta.lean` (44 lines, exactly one public declaration). Tier 0 exit 0
with 0 warnings on both, tier 1 green, and the pin's last heartbeat override
(`16000000 in` before the 106-line `gapsw80_t43_SL_closed`) dropped — it was not needed.

**Final state, all re-run by the manager.** 388/388 pin declarations transcribed across
the nine development modules (7,865 lines) plus the 44-line façade; the independent
statement diff finds 387 textually exact and one differing only in that the pin writes a
referenced obligation with its own namespace prefix; provenance complete (no `—`); the
register current at 24 unlisted modules / 683 public declarations / 397 with a pin
original. Checker **9,231 identical (648 promoted, 83 renamed), 0 mismatched, 0
missing**, 38 own-proof exempted, 9,269 checked — the delta is +1, exactly the façade's
single declaration. The one-token mutation on the headline moved exactly one `mismatched`
and was reverted. `#print axioms` on the headline (and on the development's package
theorem) is `[propext, Classical.choice, Quot.sound]`. The sweep is clean.

**What remains, by design:** the ten pin consumers of the headline (each its own node),
the five of them the Deligne–Serre cone's analytic side, and the two sibling silos
(their own orders). The development's other results are public and importable; a
consumer that needs one *checked* gets it wired then, not now.

**Dispatch 4 (waves 7–8) — landed 2026-10-12, reviewed by the manager.**
`CompletedZeta.lean` (591 lines, 49 declarations including the pin's one `scoped
instance`, pin 5460–6052) and `Hadamard.lean` (837 lines, 51 declarations, pin
6053–6933). Tier 0 exit 0 with 0 warnings on both, tier 1 green, **357/357 statements
faithful** across the eight landed modules (356 textually exact; the one difference is
that the pin writes the obligation it references as
`FLT.Gapsw80T1OdlyzkoFoundationAtomDecomposition.gapsw80_t1_DedekindCompletedFE` where
the port writes its own renamed obligation bare — the same proposition). Provenance
complete, register current, no other file touched, and no heartbeat override: the pin's
`3200000`, file-wide `6400000` and two `12800000 in` overrides are all dropped. This
dispatch discharges the `t10`/`t11`/`t32` obligations
(`completedDedekindZeta_functionalEquation_exists`, `xi_endpointNonvanishing_holds`) and
leaves the two `Prop`s `xiOrderOneHadamard` and `completedDedekindZeta_realSuperlinear`
for wave 9.

**Boundary correction.** By the declaration-start rule the `t42` Prop that starts at
6025 is wave 7's last declaration, so **wave 9's first declaration starts at 6934**, not
6901.

**Façade guidance (dispatch 5).** Expose **only** the consumed headline,
`NumberField.exists_completedDedekindZeta_package` — its pin name needs no rename, so the
checker verifies it by name. Any further façade declaration with a natural name has no
pin counterpart and would be `MISSING IN FLT` unless exempted; the nominated extras
(`completedDedekindZeta`, `completedDedekindZeta_functionalEquation_exists`,
`xi_endpointNonvanishing_holds`, `xiResidueVal`, `tendsto_xi_at_one`,
`completedDedekindZeta_classSum_eq_completedDedekindZeta`,
`sum_partialDedekindZeta_eq_dedekindZeta`) stay public in the unlisted development
modules, where they are importable without a checker row. A consumer that later needs one
*checked* is wired then, not now.

Dispatch 3 (waves 5–6) — landed 2026-10-12, reviewed by the manager.**
`Mellin.lean` (1,267 lines, 58 visible declarations plus the pin's one `scoped
instance`, pin 3149–4300) and `Unfolding.lean` (1,230 lines, 22 declarations, pin
4301–5418). Tier 0 exit 0 with 0 warnings on both, tier 1 green, **258/258 statements
identical** across the six landed modules, provenance complete, register current, no
other file touched, no heartbeat override needed. Recorded friction: v4.34.0's `Set` is
no longer a predicate, so one `Subtype … .subtype` argument is respelled in a proof;
`ENNReal.le_tsum`'s implicit `f` is supplied explicitly three times; and the pin's five
file-scoped `local instance`s (pin 4210–4237) are **re-declared `local` in `Unfolding`**
because the module split crosses them — invisible to the checker and the register,
deliberately not promoted, and not something a later reviewer should "fix".
`gammaFactor` is pin 5497 and belongs to wave 7, not wave 5.

Dispatch 2's hand-off, for the façade dispatch: the public entry points the theory now
offers are `placeOf`, `Dscale`, `scaledGram`, `multiIdealTheta`, `heckeKernel`,
`multSign`, `Phi`, `idealBasisK`, `biTerm`, `traceDualIdeal`, `bridgeMatZ`,
`bridgeEquiv`, `unitPart`, `multHeckeKernel`, `heckeWeakFEPair`, with the trace identity
`stdBasis_Phi_bilinear_eq_trace` and `heckeKernel_closed_functionalEquation`. The
façade carries the consumed headline; anything else it exposes is one checker row each
and should be chosen deliberately, not by default.

* **Worker aids.** `tools/deps/extract_wave.py <lo> <hi>` prints each pin declaration
  whose start line lies in the range, with its full source text (§10's command,
  parameterised); `tmp/diff_stmts.py` is the statement diff with a rename map.
