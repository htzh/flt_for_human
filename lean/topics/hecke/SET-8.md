# SET 8 — the monic-relation leaves and the fricke function

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4325 jobs, 0 warnings; checker
1285/70/0/0; consumer exit 0; no cap or `sorry` in code); the review record and
the bound-hit root cause (missing opens → error-recovery churn) are in
[SET-9.md](SET-9.md) §0. Fourth coding set of the route-C′ effort, authorized
after the SET-7 review (§0). Two orders. Route plan:
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md);
mathematics and scout as in [SET-6.md](SET-6.md) §1.

| order | module | declarations | pin `S_` lines | depends on |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/MonicRel.lean` (new) | the four monic-relation leaves (§5.1) | 964 | SET-5 `Basic` |
| 2 | `ModularForms/WeightOne/FrickeFunction.lean` (new) | the three `frickeFunction_*` packages (§5.2) | 3,717 | order 1, SET-7 `WeierstrassPTorsion` + `LevelOneHauptmodul` |

Run in series, order 1 first: order 2's `frickeFunction_intBaseChange` cites
order 1's `WLight.exists_mdifferentiable_div_of_monicRel` and SET-5's
`IsIntegral.mem_span_of_adjoin_simple_constants{,_transcendental}`; its other two
packages cite SET-7's `weierstrassP_torsion_qExpansion_package` and SET-6/7's
`levelOne_hauptmodul_package` (all ported). All five nodes in this set are
closure ≤ 3 apart from `intBaseChange` (closure 10, all premises already ported or
in this set).

**Reserved for the manager (do not start):** `WeightOne/IntegralStructure.lean`
(trace lemma + corollaries) and later sets. A helper belonging to a later module
becomes a local `private` helper here and is recorded.

## 0. SET-7 review (verified by the manager)

- `LevelOneHauptmodul.lean` extended to 2,937 lines (6 headlines) and
  `WeierstrassPTorsion.lean` created (1,317 lines, 1 headline); every helper
  `private`; statements binder-verbatim.
- Independent re-run: full `timeout 240 lake build` **4319 jobs, exit 0, 0
  warnings**; checker **1278 identical / 70 promoted / 0 mismatched / 0 missing /
  14 own (1292 checked)**; consumer exit 0; `#print axioms` clean.
- No `set_option maxHeartbeats`/`maxRecDepth` and no `sorry`/`admit` in code (the
  three files that match the grep are docstring prose noting the pin's caps were
  **not** transcribed).
- The pin's unused `PoleBounded` was dropped; the unused private
  `IsBoundedAtImInfty.mul_discPow_mono` from SET-6 is now reused by
  `KPoleAt.pad`, and SET-6's private `discPowForm`/`qExpansion_one_discPow`/… are
  reused rather than duplicated.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3` at
  `~/proj/fermats-last-theorem`; read-only. Statement =
  `Theorems/Thm_<dotted, `.` → `_`>.lean` (the authority); proof =
  `P2M/Sol/S_<same>.lean`.
- v4.34 drift: [porting-playbook.md](../../porting-playbook.md) §4 plus the SET-6/7
  reports (`if_*`→`ite_*`, `dif_pos`→`dite_eq_left`, `Set.mem_setOf_eq`→
  `Set.mem_ofPred_eq`, `coe_*` aliases, `BoundedAtFilter.smul`,
  `SlashInvariantForm.slash_action_eqn`, `EisensteinSeries.E_qExpansion_coeff`,
  `_root_.bernoulli`, `Matrix.SpecialLinearGroup.mapGL`, scoped
  `simp`/`ext`/`instance` flattening, `p2m_*` removal). Adapt proofs, never
  statements.

## 2. Build discipline — read and obey first

- **Fixed bounds, never raised, never bypassed:** `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`. A non-return is a
  blow-up, not patience. Never raise `maxHeartbeats`/`maxRecDepth` (project cap
  4,000,000); never bump a bound.
- `lake env lean <file>` runs at the default 200,000 cap and may false-alarm on a
  proof `lake build` compiles green; the acceptance gate is `lake build` + checker
  + consumer. Not licence to raise anything.
- **Check CPU when in doubt:** `/usr/bin/time -v`. High user CPU + timeout = real
  blow-up (quarantine/bisect); near-zero user CPU + long wall = I/O / lock
  contention (re-run when idle, do not bisect). Build serially.
- **Likely stall points:** `frickeFunction_intBaseChange`'s base-change and
  `monicRel` transfers, and the `tprod`/`Periodic` normalisations in the orbit
  package. Keep the pin's `private` helpers `private`; state over concrete types;
  reuse SET-6/7's private disc/width helpers rather than duplicating.

## 3. Shared conventions

1. Statements verbatim from the wrappers, binders included.
2. Specific imports; no `import Mathlib`.
3. Only the headlines public.
4. Checker: append the seven wrappers to `SOURCES` and the two modules to
   `PORT_FILES`; target **0 mismatched, 0 missing**.
5. **No commits**; the pin is never modified. FFG/Sturm/capstone untouched
   (Sturm import only if needed).
6. `README.md` gains both rows.

## 4. Definition of done

- Modules at the named paths; statements verbatim; specific imports.
- `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the seven headlines clean.
- Checker **0 mismatched, 0 missing**.
- `README.md` rows added.
- No statement weakened; on a mismatch, quote both and stop.

## 5. The orders

### 5.1 — order 1: `FLTForHuman/ModularForms/WeightOne/MonicRel.lean`

| declaration | `S_` file (lines) | graph closure |
|---|---|---|
| `WLight.exists_analyticOnNhd_div_of_monicRel` | `S_WLight_exists_analyticOnNhd_div_of_monicRel.lean` (164) | 1 |
| `WLight.exists_mdifferentiable_div_of_monicRel` | `S_WLight_exists_mdifferentiable_div_of_monicRel.lean` (183) | 2 (cites the above) |
| `WLight.exists_twist_of_flat` | `S_WLight_exists_twist_of_flat.lean` (199) | 1 |
| `WLight.span_inter_rational_of_twist_stable` | `S_WLight_span_inter_rational_of_twist_stable.lean` (418) | 1 |

### 5.2 — order 2: `FLTForHuman/ModularForms/WeightOne/FrickeFunction.lean`

| declaration | `S_` file (lines) | graph closure |
|---|---|---|
| `WLight.frickeFunction_modularity_package` | `S_WLight_frickeFunction_modularity_package.lean` (1,180) | 3 |
| `WLight.frickeFunction_orbit_package` | `S_WLight_frickeFunction_orbit_package.lean` (1,037) | 5 |
| `WLight.frickeFunction_intBaseChange` | `S_WLight_frickeFunction_intBaseChange.lean` (1,500) | 10 |

All are self-contained (closure-1) analytic/combinatorial `S_` files; transcribe
their `private` helpers as `private`.

Do **not** port `levelN_structure_package`,
`exists_levelFraction_of_stable_family`, the two `exists_monicRel_j_*`,
`exists_qExpansion_coeff_mem_*`, `qExpansion_sigmaTransport_package` or
`ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient`; they are
SET 9.

## 6. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` with `#check`s of the seven headlines and one
executed application per order (e.g. an `mdifferentiable`/analyticity statement
from order 1, and the `intBaseChange`/orbit statement from order 2).
`timeout 120 lake env lean spec/WeightOneConsumer.lean` exits 0 with no warnings;
if an honest application is impossible, say so.

## 7. What to report back

SET-6 §7's seven items, in scope: per-order table; wrapper mismatches (quoted);
v4.34 drifts; promoted/later-module helpers and any **duplication avoided** by
reusing SET-6/7 private helpers; whether order 2 finished and where its proof mass
sat; any build that hit its bound (declaration, CPU, outcome); and confirmation
the capstone, FFG, Sturm and the pin are untouched.

## 8. Later sets (manager's view; not authorized)

| set | orders |
|---|---|
| 9 | `LevelFraction` cluster: `levelN_structure_package`, `exists_levelFraction_of_stable_family`, the two `exists_monicRel_j_*`, `exists_qExpansion_coeff_mem_*`, `qExpansion_sigmaTransport_package`, `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient` (≈7,200; two orders) |
| 10 | `Gamma0Rationality` (≈5,400) |
| 11 | `Gamma1Basis` (≈5,200) |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) |
