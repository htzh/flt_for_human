# Work order — row 3.7: the RR assembly against the K ending

**Status: ready to dispatch.** Row 3.7 of [../PORTING-RR.md](../PORTING-RR.md) §3; method
[../porting-playbook.md](../porting-playbook.md) §2–§5; build economy
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3. Read
[WORKFLOW.md](WORKFLOW.md) first.

Baseline: checker **4144 identical / 0 mismatched / 0 missing / 30 own-proof**
(4174 checked); row 3.6 (the K ending) is landed
([WORKORDER-P3-6-kend.md](WORKORDER-P3-6-kend.md) §8). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`.

## 0. Scope

The RR assembly: from `(hRTK : ResidueTheoremK K F)` produce the pin's
`FunctionFieldRiemannRoch K F`.

| target | wrapper (statement authority) | body |
|---|---|---|
| `AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` | `Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean` | `P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean` (6,257 ln; `solution` at the tail) |

The pin's `solution` is a two-line call:

```lean
intro _ _ _
exact ModularCurve.p0n25_wkc_functionFieldRiemannRoch_of_residueTheoremK K F
    (hRTK := hRTK) (hC := ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed K F)
```

so the port lands `p0n20_rr_constantsAreBase_of_isAlgClosed` (pin 5931), the
`p0n25_wkc_*` `MirrorAssembly` block (pin 5971–6257) and the K-route chain that block
reaches.

**Measured residual (port_advise, reproduce in §5):** 278 declarations; 212
substitutions (≈4,548 ln). Residual **66 declarations / 1,511 ln raw — 38 genuinely
new / 955 ln, 28 adapters / 556 ln**. The plan's ≈400 counted only the final
`MirrorAssembly` block; the assembly also reaches the pin's K-route chain
(`riemannIndexFormula_of_genusReached`, `weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK`,
`residuePairingSurjective_{of_riemannIndexFormula,of_weilDifferentialRankOne,surjective}`,
`genus_eq_degree_div`, `stichtenothGenus_nonneg`, `constantsAreBase_of_{deg_eq_one,exists_isRational}`,
`eq_algebraMap_of_forall_ord_nonneg`, `ord_sub_evalAt_pos`,
`mem_lSpace_of_weilSmul_mem_omegaSpace`, `exists_weilSmul_eq_of_riemannIndexFormula`,
`weilDifferentialRankOne_of_riemannIndexFormula`, `omegaSpace_finite_of_riemannIndexFormula`,
`lSpace_finite_of_riemannIndexFormula`, `degree_add_one_sub_genus_le_ell_of_riemannIndexFormula`,
`not_isField_integralClosureAt'`, `instSumRamificationInertia`), which the port has
only under **phase-1 names**. So the plan's estimate was a lower bound (the recurring
measurement lesson); the set is still **one-worker small**.

**Out of scope:** row 3.5 (the perfect-field ending), the `_v2` twins, and the pin's
inlined engine (pin 1–5970) — the port already has it as phase 1 + rows 3.1–3.6.

## 1. Deliverables

New module; **no existing module edited**:

`FLTForHuman/AlgebraicCurve/ResidueTheorem/RRAssembly.lean` — the residual
declarations (the 38 new + the adapters the proof reaches), `p0n20_rr_constantsAreBase_of_isAlgClosed`,
the `p0n25_wkc_*` `MirrorAssembly`, and the public headline. A second module is allowed
only at a clean namespace boundary with a linear import chain.

## 2. Statement

Spell the headline **verbatim from its `Thm_` wrapper** (copy the file; the checker
diffs the declaration text after the name):

```lean
theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [AlgebraicCurve.HasLocalResidue K F]
    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K (RatFunc K)]
    [∀ u : AlgebraicCurve.Place K (RatFunc K), u.FiniteResidue]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K F]
    [AlgebraicCurve.HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : AlgebraicCurve.Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [AlgebraicCurve.HasSeparableResidue K F]
    (hRTK : AlgebraicCurve.ResidueTheoremK K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F
```

`hRTK` stays a hypothesis (the wrapper keeps it). The row-6 headline
`AlgebraicCurve.residueTheoremK_of_isAlgClosed` (`ResidueTheorem/KFamily.lean`) is the
producer if a consumer wants the unconditional form — do **not** discharge `hRTK` in
this statement.

## 3. Reuse and the mathlib audit

**Do the mathlib audit first** (playbook §2.2), write `AUDIT-mathlib-p3-7.md`, and
record the negatives. Leads, all already in the port:

- `Defs/RiemannRochRows.lean`: the predicates `FunctionFieldRiemannRoch`,
  `WeilDuality`, `WeilDualityAdelic`, `RiemannIndexFormula`, `WeilOmegaEllAgrees`,
  `RiemannInequality`, and the bridges
  `functionFieldRiemannRoch_of_riemann_and_duality`,
  `weilDuality_of_riemannIndex_of_adelic`.
- `RiemannRoch/Assembly.lean`: `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists`,
  `weilDifferentialRankOne_of_stichtenothGenusExists`,
  `indexOfSpecialty_eq_ell_sub_of_rankOne_max`, the `lSpace`/`ell`/`degree` lemmas.
- `Genus/Index.lean`: `indexOfSpecialty_eq_of_genusReached`,
  `indexOfSpecialty_eq_zero_of_genusReached`, `omegaSpace_finite_of_genusReached`,
  `finrank_omegaSpace_eq_indexOfSpecialty`, `RiemannGenusReachedAt.eq_of_ge`.
- `Genus/Stichtenoth.lean`: `RationalFunctionField.stichtenothGenusExists`,
  `nonempty_place_of_ratFunc_tower`, `finiteDimensional_lSpace_zero_of_constantsAreBase`.
- `Canonical/WeilDifferential.lean` / `Defs/WeilOfKaehler.lean`:
  `weilOfKaehler_mem_omegaSpace_of_residueTheorem` is the **PF twin** of the needed
  `weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK` — `#check` whether the K version
  can be adapted or must be transcribed (the K predicate `ResidueTheoremK` differs).
- row 6: `ResidueTheorem/KFamily.lean` (`ResidueTheoremK` producer, the `hRTK` source).
- The `residuePairing` API (`residuePairing_injective`, …) and the
  `CanonicalLocalResidueDataK`/`weilOfKaehlerK` layer.

**Statement-shape trap (seen in row 6).** The checker diffs the declaration text after
the name; auto-omitted section variables and section-variable explicitness bite. Spell
each public declaration as the pin does, and re-read the checker's MISMATCH output
rather than guessing.

**Stop-early protocol.** If a proof reaches a declaration outside the measured files,
resolve it locally `private` with the statement verbatim, report the pin `file:line` as
promotion debt, and **do not edit a frozen module**.

## 4. Build discipline (verbatim, [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3)

- the set lands in a **NEW** file; nothing imports it yet, so it cannot cascade;
- edit loop: `timeout 120 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
- `flock /tmp/flt_for_human.lock timeout 240 lake build <module>` when done;
- **no whole-tree build** during the set; one at the milestone;
- never raise the heartbeat cap; no `sorry`/`admit`/`axiom`; no bare `import Mathlib`.

## 5. Checker wiring and verification

Append **last**:

- `SOURCES +=` `Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`,
  then `P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean`.
- `PORT_FILES +=` the new module.

```bash
cd lean
python3 spec/check_flt_statements.py                    # 0 mismatched / 0 missing
flock /tmp/flt_for_human.lock timeout 900 lake build FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/RiemannRochConsumer.lean
# #print axioms on the headline; hygiene grep; .olean mtimes
```

Reproduce the measurement:

```bash
cd tools/deps
python3 port_advise.py --target P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean \
        --json build/row37_rr_advise.json > build/row37_rr_advise.log 2>&1
```

The 66 residual declarations (38 `NEW`, 28 adapters) with pin line and span are in
`tools/deps/build/row37_new.tsv` (generated by the manager; regenerate and take
`--drags-full` yourself).

## 6. Report shape

Modules + line counts; checker delta; per-module build results and `.olean` mtimes;
`#print axioms`; hygiene; promotion debt with pin `file:line`; boundary/gaps; and any
deviation reported mid-flight.

## 7. Closeout — ACCEPTED (manager, 2026-09-30)

One new library module, 694 ln, **no existing library module edited**:
`FLTForHuman/AlgebraicCurve/ResidueTheorem/RRAssembly.lean` (36 public + 2 `private`)
— the public headline `functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`
(wrapper verbatim, `hRTK` kept), `ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed`,
the 17-decl `p0n25_wkc_*` `MirrorAssembly`, and the K-route chain as adapters over the
port's phase-1 engine. The mathlib audit is `AUDIT-mathlib-p3-7.md`.

Independently re-verified by the manager:

- checker **4144 → 4182 identical / 0 mismatched / 0 missing / 30 own-proof**
  (4212 checked) — the +38 is the worker's 36 public declarations plus the concurrent
  P3.7b `GeneralFromK.lean` (+2); measured with only this set's wiring it is 4180.
- forced per-module `lake build` green (deleted the `.olean` and rebuilt, 2,822 jobs);
  only `RRAssembly.olean` moved; direct deps untouched.
- `#print axioms` on the headline, `p0n20_*`, `p0n25_wkc_*`, and the K-route nodes
  (`weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK`,
  `residuePairingSurjective_of_riemannIndexFormula`, `genus_eq_degree_div`) →
  `[propext, Classical.choice, Quot.sound]`.
- hygiene clean; statements read against the wrapper (verbatim).

**Accepted dispositions (not open debt).** Two of the 38 measured-NEW declarations were
not landed because the reached proofs never use them: `instSumRamificationInertia` (pin
2615 — the class is never invoked, and the port already has
`Place.sum_ramificationIndex_mul_inertiaDeg` plus two private copies, so a global
scoped instance would be dead code) and `not_isField_integralClosureAt'` (pin 5779,
pin-private — already inlined in the port's `Place.exists_restrict_eq`, reached via the
imported public `RationalFunctionField.nonempty_place_of_ratFunc_tower`).

**Promotion debt (refactor round).** `Place.exists_trace_residue_ne_zero`
(pin 4863) is `private` in the frozen `Defs/WeilOfKaehler.lean:274`; re-provisioned
`private` at the pin name in `RRAssembly`. A later round can promote the `WeilOfKaehler`
copy and drop the re-provision.

**Consumer zone added by the manager.** Rows 3.6/3.7 and the P3.7b bridges were on the
interface with no consumer zone; Zone G of `spec/RiemannRochConsumer.lean` now exercises
`residueTheorem_of_residueTheoremK`, `residueTheorem_of_isAlgClosed`, and
`functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed` (consumer exits 0).

Row 3.7 is complete. With it, the K route produces `FunctionFieldRiemannRoch`; only
row 3.5 (the perfect-field ending) and the deferred R2 `Defs/` audit remain in phase 3.
