# WORKORDER-AF8 — the cusp-subrepresentation bridge: a composition set (~840 lines)

**Status as issued (2026-11-02): queued, ready to dispatch.** Scope: [SET-AF8.md](SET-AF8.md) — read
§1 first (this is **not** a mechanical transcription set, and §1 says why with the numbers), then §2,
§3 and the two appendices.

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md) §2.4
(dedup before coding), §3, §5; wire: the per-module protocol — a `spec-pin:` header,
`spec/check_port.py`, no in-source per-declaration marker. Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`.

**The row.** `AutomorphicForm.rightConv_rightTranslate_mem_of_isCuspSubrep`, 3,833 silo, **757 net**.
Of its 224 declarations, **174 (2,974 lines) are already in the port**, byte-identical and public;
**50 declarations / 837 lines are new**, and the headline is 68 of those.

## 1. What you write, and what you import

**You import.** SET-AF8 Appendix A is the map for all 174: pin name → port declaration → module →
pin lines. The engine arrives from

```lean
import FLTForHuman.RepTheory.TypeReproducer            -- 67 declarations
import FLTForHuman.RepTheory.ConvolutionLimit          -- 24
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra     -- 50
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.EntryBall     -- 31
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.Instantiate   --  8
```

plus the row's premise `AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn`
(`Adelic/RightConvRegularity.lean`, SET-AF5) and the cusp vocabulary
(`Cusp/Constituent.lean`'s `IsCuspSubrep`, `Cusp/SpectrumSubrep.lean`'s lift/closure datum).

**You write** the 50 new declarations (Appendix B, largest first): the `dconvWith`
dominated-convergence core, the kernel's existence, the tensor form, the `convOpOn`/`convDomain`
glue, the row-isometry quantifier, and the headline at its `Theorems/` wrapper.

**Two things to check before relying on an import** (Appendix A's caveats):

* `main` (158 pin lines) is `ArchApproxIdentity.exists_tendsto_integral_of_mem_archCutSubmodule` and
  `tendsto_integral_mul_dconvWith` (158) is `ArchApproxIdentity.tendsto_integral_mul_dconvWith` — a
  third of the file arrives by two names; read both statements.
* two of the matched copies are `private` in `Adelic/TestFnTop.lean`. Promote them (same statement ⇒
  promote and delete the local copy, FR-0101) or re-state them locally; decide by reading.

## 2. The module

`FLTForHuman/AutomorphicForm/Adelic/Cusp/RightConvSubrep.lean` — **new**, 0 importers, cascade-free.
Header: a `/- … -/` block with the subject sentence and exactly two wires

```
spec-pin: Theorems/Thm_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.lean
spec-pin: P2M/Sol/S_AutomorphicForm_rightConv_rightTranslate_mem_of_isCuspSubrep.lean
```

The pin's 49 other private declarations stay `private`; the headline goes public at the wrapper's
statement in `namespace AutomorphicForm`.

## 3. Traps

1. **The pin's names are not the port's.** 174 of its declarations exist in the port under other names
   (`main`, `aux_*`, `tendsto_integral_mul_dconvWith`) — Appendix A is the only reliable map. Do not
   grep for a pin name and conclude it is missing.
2. **`dconvWith`/`convOpOn` are new** (not in the port): their *definitions* come with the 50. If a new
   `aux_*` lemma's proof needs a ported engine lemma that the substitution list does not name, look for
   its statement in `RepTheory/TypeReproducer` and `ArchApproxIdentity/*` before proving it.
3. **The `p2m_open` translation**: the pin uses `p2m_open "A B~h"` (open + scoped activation). Translate
   it as SET-AF7's script did (`open A` / `open B (h)` + `open scoped`) — see SET-AF7 §1.
4. **`set_option linter.style.haveILetI false in`** where the pin keeps a `letI := glBorel` /
   `haveI := borelSpace_…` wall.
5. No `set_option maxHeartbeats`; no `sorry`/`admit`/`axiom`/`native_decide`.

## 4. Gates

1. `lake env lean <module>` silent, then `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.Cusp.RightConvSubrep`; **no tree build**, no dependents.
2. `spec/check_port.py --force <module>` → **1 ok / 0 mismatch / 0 missing**; the `gate_scan` on the
   wrapper's `Def_` closure → **0 missing** (FR-0099 census: wrapper ∪ premises).
3. `#print axioms` on the headline → `[propext, Classical.choice, Quot.sound]`.
4. `dedup --within` (expect ~0 — the 3,000 ported lines were *imported*, not copied) and `--cross`;
   `move_dead` triaged by the rule: **dead mathematics → `Reserve/`**, duplicate or plumbing → delete.
5. Zero warnings.
6. `spec/AutomorphicFormSetAF8Consumer.lean` — one zone, a real composition (no `#check`): compose the
   headline with SET-AF5's continuity, e.g. `Continuous (rightConv F φ α)` at the translate and the
   membership it implies.

## 5. Report

Report: the module's line count; the checker's three numbers; the axioms line; build time and silence;
`dedup`'s clusters and `move_dead`'s report with each disposition; the consumer zone's error count;
**how many of Appendix A's 174 imports you actually used and how many needed a re-statement**; and
every deviation from the pin. **A blocker goes back immediately**, with the pin line and the error.
