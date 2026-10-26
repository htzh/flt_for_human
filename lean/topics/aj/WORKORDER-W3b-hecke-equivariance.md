# WORKORDER W3b — the Hecke-equivariance layer

Execution order for [PLAN-W3b-hecke-equivariance.md](PLAN-W3b-hecke-equivariance.md), whose §1–§12 are
the specification: this file only fixes ownership, the pin references, and the discipline. Pin
`anthropics/fermats-last-theorem@aa2d8b34`, local clone `/home/haitao/proj/fermats-last-theorem`; port
mathlib `v4.34.0`. Parent
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) §10.4.

The port is ordered **A-only**: W1, W2 landed; W3 (the honest integral) is shelved in `Reserve/` and
will not be imported. Do not open it.

## 1. Already landed — do not re-do

`CuspForm.StableD`, `StableU`, `StableT` are in `FLTForHuman/ModularForms/Defs/GammaH.lean`
(§"Hecke stability"), transcribed from
`Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:72–105`. That module is **wired and green**:
four `spec-pin:` lines, `check_port` 28 ok / 0 mismatch / 0 missing, removed from
`spec/old_check_stmts.py`, build 6 s. The predicates are hypotheses — they have no proof body; the
theorems that *establish* them are yours (nodes 4–6 below).

They are in the pin's namespace **`CuspForm`**, not `CohCarrier`: the pin declares them at
`Def_CuspForm_HeckeOperatorFormsGammaH.lean:12` inside `namespace CuspForm`, and the pinned headlines
state `CuspForm.StableD M H k`. `check_port` matches declarations by unqualified name, so the original
`CohCarrier` homing passed the checker and was still wrong; checkpoint F moved the three `def`s (bodies
untouched) and `GammaH.lean` is 28 ok / 0 mismatch again, now under the pin's full names. Namespace
fidelity is therefore a manual check on this wire, not a checker verdict.

## 2. What this wave owns: twelve headlines

| # | headline | pin wrapper (`Theorems/`) | pin proof (`P2M/Sol/`) | pin lines | target module |
|---|---|---|---:|---|
| 10 | `HeckeEis.coresHom_eq_transfer` | `Thm_HeckeEis_coresHom_eq_transfer.lean` | `S_HeckeEis_coresHom_eq_transfer.lean` | 59 | `GroupTheory/Corestriction.lean` (new) |
| 11 | `ModularCurve.Period.IsEquivariantPrimitive.periodHom_eq_of_hasDerivAt` | `Thm_ModularCurve_Period_IsEquivariantPrimitive_periodHom_eq_of_hasDerivAt.lean` | `S_…periodHom_eq_of_hasDerivAt.lean` | 63 | `ModularForms/EichlerShimura/PeriodPrimitive.lean` (+1) |
| 12 | `ModularCurve.periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf` | `Thm_ModularCurve_periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean` | `S_…periodOf_apply_eq_sub_of_hasEquivariantPrimitiveOf.lean` | 93 | `ModularForms/EichlerShimura/PeriodOf.lean` (+1) |
| 7 | `ModularCurve.periodMapOf_apply_eq_periodOf` | `Thm_ModularCurve_periodMapOf_apply_eq_periodOf.lean` | `S_…periodMapOf_apply_eq_periodOf.lean` | 19 | `ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` (+1) |
| 6 | `CuspForm.stableD` | `Thm_CuspForm_stableD.lean` | `S_CuspForm_stableD.lean` | 13 | `ModularCurve/Period/HeckeStability.lean` (new) |
| 5 | `CuspForm.stableU` | `Thm_CuspForm_stableU.lean` | `S_CuspForm_stableU.lean` | 19 | same |
| 4 | `CuspForm.stableT` | `Thm_CuspForm_stableT.lean` | `S_CuspForm_stableT.lean` | 24 | same |
| 8 | `ModularForm.heckeU_slash_eq_self_of_mem_GammaH` | `Thm_ModularForm_heckeU_slash_eq_self_of_mem_GammaH.lean` | `S_…_of_mem_GammaH.lean` | 481 | `ModularForms/HeckeInvariance.lean` (+2) |
| 9 | `ModularForm.heckeU_add_slash_slash_eq_self_of_mem_GammaH` | `Thm_ModularForm_heckeU_add_slash_slash_eq_self_of_mem_GammaH.lean` | `S_…_of_mem_GammaH.lean` | 489 | same |
| 1 | `ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU` | `Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU.lean` | `S_…_of_coe_eq_heckeU.lean` | 357 | `ModularCurve/Period/PeriodMapHecke.lean` (new) |
| 3 | `ModularCurve.periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash` | `Thm_ModularCurve_periodMapOf_gammaH_eq_diamondRaw_of_coe_eq_slash.lean` | `S_…_of_coe_eq_slash.lean` | 158 | same |
| 2 | `ModularCurve.periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash` | `Thm_ModularCurve_periodMapOf_gammaH_eq_heckeT_of_coe_eq_heckeU_add_slash.lean` | `S_…_add_slash.lean` | 591 | same |

Optional, take at the end (plan D6, +105): `Thm_ModularCurve_periodMapOf_gammaH_eq_comp_of_coe_eq_slash`
into `PeriodMapHecke.lean`. It is outside the 653 cone; include it unless it starts costing time.

**Definition tails, and they are yours** (they are body work, not manager statements):

* `HeckeEis.resHom`/`transferAux`/`coe_transferAux`/`transferAux_mul`/`coresHom`/`coresHom_apply` —
  `Definitions/Def_Gamma0HeckeOperatorHom.lean:205–263`, ~48 lines, in `GroupTheory/Corestriction.lean`
  under `namespace HeckeEis`.
* The coset decomposition (§5 of the plan): `FLTForHuman/ModularForms/HeckeCosetDecomposition.lean`
  (moved down from `ModularCurve/Period/` — see §4 of the plan; the namespace is the pin's
  `HeckeCoset`), written **once** from the 19 duplicated private names, ~511 lines. Unwired: it has no
  pin statement, and record the pin line range in its header instead of a `spec-pin:`. Nodes 8, 9 use the `sum_slash_beta_*` half; 1 and 2 use the
  `GammaHUpper` half.

## 3. Order, checkpoints, one writer

One implementer, in this order — the halves are logically independent but they share
`HeckeCosetDecomposition.lean`, so two writers would collide on the seam:

```
A  done    Stable* definitions (landed, §1)
B  done    Corestriction.lean + node 10                     → build green
C  done    11, then 12, then 7                              → build green
D          HeckeCosetDecomposition.lean (shared, once)
E          8, then 9            (the two 480-line proofs)   → build green
F          6, then 5, then 4                                → build green
G          1, then 3, then 2                               → build green
H          optional fourth sibling; dedup; move_dead; re-measure
```

Report after **B, C, E, G** (four short reports), and immediately on any blocker (§6).

## 4. Decisions that are already taken — do not re-litigate

* **D1** pin statements verbatim; headlines public at the pin's names; helpers `private` unless two
  modules need them.
* **D2** transcribe the coset sum; keep node 10 as the comparison with `MonoidHom.transfer`. The port
  *already has* the transfer spelling as `CohCarrier.coresAdd` (`ModularForms/Defs/CohCarrierLevel.lean`),
  so there are deliberately two spellings and node 10 is the named bridge. **Do not add a third.**
  `GroupTheory/Corestriction.lean` must not import any `FLTForHuman` module — assert it with
  `grep -c '^import FLTForHuman'` = 0.
* **D3** the pin's `haveI : NeZero q := ⟨hq.ne_zero⟩` before the conclusion is part of the statement.
  Inside a namespace, statements still spell the pin's qualified names (`ModularCurve.periodMapOf`,
  `CohCarrier.heckeT`, `CohCarrier.GammaH`).
* **D4** drop the pin's `attribute [-instance]`/`attribute [-simp]` walls (nodes 1 and 2 open with
  fifteen of them, all about `heckeUpper`, which the port does not define). If a proof will not go
  through without one, prefer a local `include`/`omit` or an explicit instance argument, and record
  which.
* **D5** `Stable*` are `def … : Prop`, so the checker sees only `Prop`: their bodies are already
  hand-diffed (landed). No further body diff is needed unless you change them.
* **D6** the optional fourth sibling at the end.

## 5. Build discipline

* Work from `lean/`. Never a tree build. One module at a time:
  `timeout 110 lake build FLTForHuman.<Module> > tmp/w3b-<module>.log 2>&1; tail -20 tmp/w3b-<module>.log`
* Fix warnings, do not suppress them (`set_option linter.style.haveILetI false` is allowed where the
  pin's `haveI`/`letI` walls are kept literal, as `HeckeInvariance.lean` and `Corestriction.lean`
  already do — in the transfer engine the `letI` is load-bearing, since `letI` inlines and that is what
  makes the coset sum definitionally the transfer).
* No `sorry`, no `axiom`, no `native_decide`, no `attribute [-instance]`/`[-simp]` walls.
* Import, do not transcribe — these twelve declarations already exist in the port: `transl` is
  `CohCarrier.uElt`; `periodAlongOf_eq_sub`, `hasDerivAt_affine`, `segmentPoint_eq_of_mem` are public in
  `ModularCurve/Period/PeriodOf.lean` (moved down from `PeriodLatticeSpan`, which is above it);
  `apply_eq_apply_of_hasDerivAt_zero` in
  `ModularForms/Analytic/CuspBoundedness.lean`; `hasDerivAt_comp_smul` in
  `ModularForms/EichlerShimura/ExistsEquivariantPrimitive.lean` (same name, different binder skeleton —
  read both texts); `sub_eq_const_of_forall_hasDerivAt` exists there only as a **`private`**
  declaration in a module *above* `PeriodPrimitive`, so promotion would be a cycle: re-prove it privately
  in `PeriodPrimitive.lean` over the public `apply_eq_apply_of_hasDerivAt_zero` (six lines — do not
  transcribe the pin's copy).
* If a build exceeds ~110 s, stop and report; do not raise the timeout.

## 6. Blocker protocol

Report immediately, do not work around silently, when:

* a pin statement does not elaborate against mathlib `v4.34.0` after two attempts (name changes, e.g.
  `QuotientGroup.eq`/`out_eq'` in the transfer engine, are the expected friction — check the port's own
  `MonoidHom.transfer_def` usage in `ModularForms/Defs/CohCarrierLevel.lean` first, it is already
  adapted);
* a statement needs a hypothesis the pin does not have;
* a proof needs one of D4's dropped attributes;
* a target module's build time grows past about 40 s.

A blocker report is: the headline, the exact goal state, the two things tried, and the options. Never
weaken or re-spell a pinned statement to get past a blocker; the `spec-pin:` wire is the contract.

## 7. Verification before calling the wave green

* `spec-pin:` header per new/touched module, naming the `Theorems/` wrapper **and** the `P2M/Sol/S_`
  file, with `-- comparable copy` on the second (the path is segmented as the pin spells it — trust the
  file names in §2, not a pattern);
* `python3 spec/check_port.py FLTForHuman/<path> --force` → `0 mismatch / 0 missing`;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all twelve: write
  `tmp/AxiomsW3b.lean` and build it;
* any module you touch that appears in `spec/old_check_stmts.py` loses its `PORT_FILES` line there
  (`GammaH.lean` is already done);
* no mutation sweep — one spot check was made on node 2 and reverted, which is enough: the wire compares
  declaration **names unqualified** and statement **text verbatim**, so a wrong statement is a mismatch
  by construction while a re-homed declaration is invisible to it (both observed; see §1);
* `tools/deps/dedup.py` on `HeckeCosetDecomposition.lean` and `tools/deps/move_dead.py` afterwards, not
  before, then `tools/deps/port_graph.py` once the modules close;
* re-measure the mouth: `needed(653)` should read 156 nodes and **two** unported direct premises
  (302 and 267).

## 8. Out of scope

A's row-2 reciprocity (≈4,025), the smoothed-fundamental cluster (W4a), the `ComplexPlaceDictionary`,
the `Γ_H` cusp-form ↔ differential identification, and anything in `Reserve/`. The merged A–B theory is
deferred: do not build the translation layer's `TranslationData` structure, and do not port
`pathIntegral` or any B-side node.
