# SET 9 — the levelFraction, levelN and sigmaTransport cluster

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4327 jobs, 0 warnings; checker
1292/70/0/0; consumer exit 0; no caps/`sorry`/bare `import Mathlib`); the review
record and the namespace-closing/SET-9 lessons are in [SET-10.md](SET-10.md) §0.
Fifth coding set of the route-C′ effort, authorized after the SET-8 review (§0).
Two orders. Route plan:
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md).

| order | module | declarations | pin `S_` lines | depends on |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/LevelFraction.lean` (new) | `qExpansion_sigmaTransport_package`, `exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction`, `exists_levelFraction_of_stable_family`, `exists_monicRel_j_of_mdifferentiable_levelFraction` | 786+1,069+1,331+667 | SET-7 `LevelOneHauptmodul`, SET-8 `FrickeFunction`, SET-5 `Basic` |
| 2 | `ModularForms/WeightOne/LevelN.lean` (new) | `levelN_structure_package`, `exists_monicRel_j_K_of_mdifferentiable_frickeQuotient`, `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient` | 1,239+1,388+739 | order 1; SET-7/8 |

Run in series. Order 1 needs only already-ported modules: `levelN_structure_package`
and `exists_levelFraction_of_stable_family` cite `levelOne_hauptmodul_package` +
`frickeFunction_modularity_package` + `frickeFunction_orbit_package`;
`exists_monicRel_j_K_…` additionally cites order 1's
`exists_monicRel_j_of_mdifferentiable_levelFraction` and SET-5's
`UpperHalfPlane.linearIndependent_complex_of_qExpansion_coeff_mem`; the
`ModularFunction.…sigmaTransport` node cites order 1's `qExpansion_sigmaTransport_package`
and `exists_qExpansion_coeff_mem_…` plus SET-8's `exists_mdifferentiable_div_of_monicRel`.

**Reserved for the manager (do not start):** `WeightOne/IntegralStructure.lean`
(trace lemma + corollaries) and SET 10+. A helper belonging to a later module
becomes a local `private` helper here and is recorded.

## 0. SET-8 review (verified by the manager)

- `MonicRel.lean` (624 lines, 4 headlines) and `FrickeFunction.lean` (3,702 lines,
  3 headlines): green, statements binder-verbatim, every helper `private`.
- Independent re-run: `timeout 180 lake build` of each module green (2.5 s / 2.0 s
  cached; 41 s first compile for `FrickeFunction`); full `timeout 240 lake build`
  **4325 jobs, exit 0, 0 warnings**; checker **1285 identical / 70 promoted / 0
  mismatched / 0 missing / 14 own (1299 checked)**; consumer exit 0.
- No `set_option maxHeartbeats`/`maxRecDepth` and no `sorry`/`admit` in code; the
  pin's local caps (1.6M/3.2M, `synthInstance`) were not transcribed.
- **Root cause of the transient 180/240 kill, worth carrying forward:** the intBC
  chunk was assembled without the pin's file-level
  `open Complex Real UpperHalfPlane ModularForm Polynomial Real.Polynomial` and
  scoped opens, and unknown-identifier error recovery churned for minutes at
  ~200 % CPU / 4.1 GB RSS. **A build that hits a bound with high CPU is not
  automatically proof mass — check first for unknown-identifier errors and
  missing opens in the assembled slice** before bisecting declarations (see §2).
- **CPU measurement caveat:** `/usr/bin/time -v` under-attributes lake's `lean`
  child (User 2.08 s for a run that used minutes). Use PID polling (`ps`/`top` on
  the `lean` process) when a build hits a bound.
- **Cross-module `private` is file-scoped**, so SET-6/7 private helpers are not
  importable; each `FrickeFunction` package carries its own `private` copy of the
  shared vocabulary (`periodPairOfTau`, `zetaN`, `wpNorm`, `KPoleAt`, …) in its own
  `WLight*` namespace, reusing only the public headlines. Expect and accept the
  same per-package duplication here; do not promote helpers just to dedup.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3` at
  `~/proj/fermats-last-theorem`; read-only. Statement =
  `Theorems/Thm_<dotted, `.` → `_`>.lean` (the authority); proof =
  `P2M/Sol/S_<same>.lean`. **Copy the pin file's `open`/`open scoped` lines first**
  (SET-8's lesson), then adapt.
- v4.34 drift: [porting-playbook.md](../../porting-playbook.md) §4 plus the SET-6/7/8
  reports.

## 2. Build discipline — read and obey first

- **Fixed bounds, never raised, never bypassed:** `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`. Never raise
  `maxHeartbeats`/`maxRecDepth` (project cap 4,000,000); never bump a bound.
- **On a bound-hitting build, diagnose before bisecting**, in this order:
  1. read the log for `unknown identifier`/parse errors and missing `open`s
     (SET-8's cause — error recovery churns CPU);
  2. poll the `lean` PID for CPU/RSS (`/usr/bin/time -v` under-attributes it);
  3. only if CPU is high *and* there are no error-recovery symptoms, bisect by
     declaration with a low cap in scratch.
- A non-return with no errors and high CPU is a real blow-up: quarantine and
  report; do not raise anything.
- Build serially; check for I/O contention (near-zero CPU + long wall) before
  bisecting.
- **Likely stall points:** the `frickeQuotient`/`levelFraction` transfers and the
  `sigmaTransport` normalisations. State over concrete types.

## 3. Shared conventions

1. Statements verbatim from the wrappers, binders included.
2. Specific imports; no `import Mathlib`; copy the pin's opens.
3. Only the headlines public; per-package helpers `private` in their own namespace.
4. Checker: append the seven wrappers to `SOURCES` and both modules to
   `PORT_FILES`; target **0 mismatched, 0 missing**.
5. No commits; pin untouched. FFG/Sturm/capstone untouched.
6. `README.md` gains both rows.

## 4. Definition of done

- Modules at the named paths; statements verbatim; specific imports.
- `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` clean on all seven headlines.
- Checker **0 mismatched, 0 missing**.
- `README.md` rows; temp files removed.
- No statement weakened; on a mismatch quote both and stop.

## 5. The orders

### 5.1 — order 1: `FLTForHuman/ModularForms/WeightOne/LevelFraction.lean`

| declaration | `S_` file (lines) | closure |
|---|---|---|
| `WLight.qExpansion_sigmaTransport_package` | `S_WLight_qExpansion_sigmaTransport_package.lean` (786) | 1 |
| `WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction` | `…_exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction.lean` (1,069) | 4 |
| `WLight.exists_levelFraction_of_stable_family` | `…_exists_levelFraction_of_stable_family.lean` (1,331) | 6 |
| `WLight.exists_monicRel_j_of_mdifferentiable_levelFraction` | `…_exists_monicRel_j_of_mdifferentiable_levelFraction.lean` (667) | 5 |

### 5.2 — order 2: `FLTForHuman/ModularForms/WeightOne/LevelN.lean`

| declaration | `S_` file (lines) | closure |
|---|---|---|
| `WLight.levelN_structure_package` | `S_WLight_levelN_structure_package.lean` (1,239) | 6 |
| `WLight.exists_monicRel_j_K_of_mdifferentiable_frickeQuotient` | `…_exists_monicRel_j_K_of_mdifferentiable_frickeQuotient.lean` (1,388) | 8 |
| `ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient` | `S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.lean` (739) | 13 |

Do **not** port the six `ModularCurve.*` Γ₀-rationality nodes or the `ModularForm.*`
/ `CuspForm.*` Γ₁-basis nodes; they are SET 10–11. Do **not** create the capstone.

## 6. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` with `#check`s of the seven headlines and one
executed application per order. `timeout 120 lake env lean spec/WeightOneConsumer.lean`
exits 0 with no warnings; if an honest application is impossible, say so.

## 7. What to report back

SET-6 §7's seven items, plus: whether any bound was hit and, if so, the diagnosis
order used in §2 (errors/open first, then CPU, then bisect) with the evidence.
Confirm the capstone, FFG, Sturm and the pin are untouched.

## 8. Later sets (manager's view; not authorized)

| set | orders |
|---|---|
| 10 | `Gamma0Rationality`: `exists_ratCast_qExpansion_{comp_smul,slash}_of_mem_Gamma0`, `exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`, `exists_isIntegralQExp_smul_of_ratCast_qExpansion`, `exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin`, `exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem`, `ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational` (≈5,400) |
| 11 | `Gamma1Basis` (≈5,200) |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) |
