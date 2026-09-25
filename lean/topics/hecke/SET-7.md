# SET 7 — the three Hauptmodul/fricke packages

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4319 jobs, 0 warnings; checker
1278/70/0/0; consumer exit 0; no untranscribed cap in code); the review record is
[SET-8.md](SET-8.md) §0. Third coding set of the route-C′ effort, authorized
after the SET-6 review (§0). Two orders. Route plan:
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md);
mathematics and scout as in [SET-6.md](SET-6.md) §1.

| order | module | declarations | pin `S_` lines | depends on |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/LevelOneHauptmodul.lean` (**extend**) | `WLight.levelOne_hauptmodul_package`, `WLight.weierstrassP_qExpansion_package` | 1,186 + 858 | SET-6 order 1 |
| 2 | `ModularForms/WeightOne/WeierstrassPTorsion.lean` | `ModularForm.weierstrassP_torsion_qExpansion_package` | 1,317 | order 1 (graph premise) |

Order 2 cites order 1's `WLight.weierstrassP_qExpansion_package` (graph direct
premise), so run them in series, order 1 first. `levelOne_hauptmodul_package` and
`weierstrassP_qExpansion_package` are independent closure-1 leaves.

**Reserved for the manager (do not start):** `WeightOne/IntegralStructure.lean`
(trace lemma + corollaries) and later sets. A helper belonging to a later module
becomes a local `private` helper here and is recorded. The SET-6 order-1 module
already carries an *unused* local `private`
`IsBoundedAtImInfty.mul_discPow_mono`; if order 1 needs it, use that copy rather
than adding a second.

## 0. SET-6 review (verified by the manager)

- `WeightOne/LevelOneHauptmodul.lean` (1,084 lines, 4 headlines) and
  `WeightOne/EisensteinChiNegThree.lean` (3,828 lines, 1 headline + 459 `private`),
  statements binder-verbatim; all helpers `private`.
- Independent re-run: full `timeout 240 lake build` **4318 jobs, exit 0, 0
  warnings**; checker **1275 identical / 70 promoted / 0 mismatched / 0 missing /
  14 own (1289 checked)**; consumer exit 0; `#print axioms` clean.
- The pin's local `maxHeartbeats 1600000`, `maxRecDepth 16384` and
  `synthInstance.maxHeartbeats` were **not** transcribed (the one `by decide`
  guarded by `maxRecDepth` was re-proved); no cap was raised.
- The 4:37 wall / 0.39 s user-CPU timeout seen mid-run was I/O contention on the
  `import Mathlib` probe, not a blow-up; the χ₋₃ module's own builds ran 27–39 s
  wall / 67–80 s user.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3` at
  `~/proj/fermats-last-theorem`; read-only. Statement =
  `Theorems/Thm_<dotted, `.` → `_`>.lean` (the authority); proof =
  `P2M/Sol/S_<same>.lean`.
- v4.34 drift: [porting-playbook.md](../../porting-playbook.md) §4 plus the SET-6
  report (`if_*`→`ite_*`, `Set.mem_setOf_eq`→`Set.mem_ofPred_eq`, `coe_*`
  aliases, `BoundedAtFilter.smul`, `Prime.not_unit`→`Prime.not_isUnit`, scoped
  `simp`/`ext`/`instance` flattening, `p2m_*` removal). Adapt proofs, never
  statements.

## 2. Build discipline — read and obey first

- **Fixed bounds, never raised, never bypassed:** `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`. A non-return is a
  blow-up, not patience. Never raise `maxHeartbeats`/`maxRecDepth` (project cap
  4,000,000); never bump a bound.
- `lake env lean <file>` runs at the default 200,000 cap and may false-alarm on a
  heavy proof that `lake build` compiles green; the acceptance gate is `lake build`
  + checker + consumer. This is **not** licence to raise anything.
- **Check CPU when in doubt:** `/usr/bin/time -v`. High user CPU + timeout = real
  blow-up (quarantine/bisect); near-zero user CPU + long wall = I/O / lock
  contention (re-run when idle, do not bisect). Build serially.
- **Likely stall points:** the `monicRel`/`frickeQuotient` normalisations in
  `levelOne_hauptmodul_package` and the `weierstrassP` `q`-expansion recurrences in
  order 2. Keep the pin's `private` helpers `private`; state over concrete types.

## 3. Shared conventions

1. Statements verbatim from the wrappers, binders included.
2. Specific imports; no `import Mathlib`.
3. Only the headlines public.
4. Checker: append the three wrappers to `SOURCES` (the two order-1 packages and
  the order-2 package) and the order-2 module to `PORT_FILES`; the extended
  order-1 module is already listed. Target **0 mismatched, 0 missing**.
5. **No commits**; the pin is never modified. FFG/Sturm/capstone untouched
   (Sturm import only).
6. `README.md` row for the order-2 module (and an update to the existing
   `LevelOneHauptmodul` row).

## 4. Definition of done

- Modules at the named paths; statements verbatim; specific imports.
- `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the three headlines clean.
- Checker **0 mismatched, 0 missing**.
- `README.md` rows updated.
- No statement weakened; on a mismatch, quote both and stop.

## 5. The orders

### 5.1 — order 1: extend `WeightOne/LevelOneHauptmodul.lean`

| declaration | `S_` file (lines) | role |
|---|---|---|
| `WLight.levelOne_hauptmodul_package` | `S_WLight_levelOne_hauptmodul_package.lean` (1,186) | the level-one Hauptmodul/`j`/`q`-expansion-principle bundle |
| `WLight.weierstrassP_qExpansion_package` | `S_WLight_weierstrassP_qExpansion_package.lean` (858) | the `℘` `q`-expansion bundle |

Both are closure-1 (no FLT theorem premises): the `S_` files are self-contained
mathlib developments, not wrappers. Transcribe their `private` helpers as
`private` and append the two headlines to the existing module.

### 5.2 — order 2: `FLTForHuman/ModularForms/WeightOne/WeierstrassPTorsion.lean`

| declaration | `S_` file (lines) | role |
|---|---|---|
| `ModularForm.weierstrassP_torsion_qExpansion_package` | `S_ModularForm_weierstrassP_torsion_qExpansion_package.lean` (1,317) | the torsion `℘` `q`-expansion bundle, on top of order 1 |

Import the extended `LevelOneHauptmodul.lean`; all helpers `private`.

Do **not** port anything beyond these three headlines; `WLight.frickeFunction_*`,
`levelN_structure_package` and the Γ₀-rationality nodes are SET 8.

## 6. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` with `#check`s of the three headlines and one
executed application per order (e.g. consume `levelOne_hauptmodul_package`'s
`j`-surjectivity/polynomial statement, and the order-2 bundle's torsion
`q`-expansion). `timeout 120 lake env lean spec/WeightOneConsumer.lean` exits 0
with no warnings; if an honest application is impossible, say so.

## 7. What to report back

SET-6 §7's seven items, verbatim in scope: per-order table; wrapper mismatches
(quoted); v4.34 drifts; promoted/later-module helpers; whether order 2 finished
and where its proof mass sat; any build that hit its bound (declaration, CPU,
outcome); and confirmation the capstone, FFG, Sturm and pin are untouched.

## 8. Later sets (manager's view; not authorized)

| set | orders |
|---|---|
| 8 | `FrickePackage` (≈7,500; likely two orders) |
| 9 | `Gamma0Rationality` (≈5,000) |
| 10 | `Gamma1Basis` (≈4,900) |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) |
