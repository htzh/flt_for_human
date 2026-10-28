# WORKORDER-MC2a — `qTwist` on non-toric points

Status: **landed 2026-10-27** (SET [MC-2](SET-MC2.md), order MC-2a). Inserted into the migrated
`lean/FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` (131 → 322 lines).
Manager-verified: `check_port --force` **15 ok / 0 mismatch / 0 missing / 0 own** — the 14
migrated verdicts still `ok`, the new row `ok` at its `Them_` wrapper; axioms
`[propext, Classical.choice, Quot.sound]`; build 7 s silent; `dedup` 0 clusters; zero warnings, no
options.  `qTwist` is the ported `ModularCurve.qTwist`/`qTwistFun` (imported, not restated); the
proof is the pin's over the module's own `coeff_slotSubst_tateUniv{X,Y}` — real mathematics, not a
facade.  Nine `private` engine lemmas stay local (their natural home is the tier-3
`TateSlots/SlotCoeff.lean`, which the order forbids editing), so the public surface grows by
exactly one declaration.  One forced deviation worth keeping: the statement needs
`universe u in` + `(K : Type u)` to match the wrapper's hash — `Type*` is a `MISMATCH`.

| node | pin `S_` | lines | declares | frontier |
|---|---|---:|---|---|
| `ModularCurve.qTwist_nonToricPoint_of_pow_eq_one` | `P2M/Sol/S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean` | 185 | — | ready, silo 185, lev 1 / 1 |

Read [SET-MC2.md](SET-MC2.md) (§1, §2, §3, §4). **Pin** `/home/haitao/proj/fermats-last-theorem`
at `aa2d8b3`; **port** `/home/haitao/proj/reasonix-sandbox/flt_for_human/lean`.

**Insert into the migrated module** `lean/FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean`
(no new module). Add to its leading `spec-pin:` block:

```
spec-pin: Theorems/Thm_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean
spec-pin: P2M/Sol/S_ModularCurve_qTwist_nonToricPoint_of_pow_eq_one.lean
```

and the row's declarations at the pin's names (statement authority: the `Them_` wrapper). The
`qTwist` of the pin is the ported `ModularCurve.qTwistFun` (`ModularCurve/Defs/Twist.lean`) —
import/use it, do not restate it (the `46-suspect` list's `twistFun` entry is this row; the port's
statement is the authority).

Rules: no duplicated mathematics, no facades; no `set_option maxHeartbeats`/`synthInstance`;
**no linter suppressions** (fix the warning: `haveI → have`; `omit` only on a private declaration);
no `sorry`/`admit`/`axiom`/`native_decide`; no edits outside this module; no git.

Gates (from `lean/`): edit loop silent at `-DautoImplicit=false -DmaxHeartbeats=200000`;
`python3 spec/check_port.py --force FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` →
**0 mismatch / 0 missing** and the 14 migrated `ok`s still `ok`; axioms clean on the headline;
`flock lake build FLTForHuman.ModularCurve.TateSlots.CoefficientFormulas` silent; `dedup.py` no new
cluster; zero warnings.

Report: checker summary + the 14 pre-existing verdicts, axioms, build tail, line count, private
declarations and why, deviations.
