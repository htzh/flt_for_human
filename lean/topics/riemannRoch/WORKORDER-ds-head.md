# Work order — `ds-head`: the `AlgebraicCurve` differential / ramification tail

**Status: drafted 2026-10-07, ready to dispatch.** Topic (measurements, dedup, route):
[ds-head-recon.md](ds-head-recon.md). Method:
[../porting-playbook.md](../porting-playbook.md) §2.1–§2.6, §3.1–§3.5, §4–§5.
Boilerplate/build clauses: [WORKORDER-H1a-index.md](WORKORDER-H1a-index.md) §4 (same
checker-wiring/`flock`/cap rules). Pin `anthropics/fermats-last-theorem@aa2d8b3`, mathlib
`v4.34.0`.

## 0. Scope

Land the four nodes at the head of the post-row-S ready shelf — the differential/ramification
layer above the ported Riemann–Roch core — as **one set, three modules**:

| target | pin lines | role |
|---|---:|---|
| `AlgebraicCurve.map_ne_zero_of_tame` | 1,223 | `KaehlerDifferential.map K K F F' ω₀ ≠ 0` for `ω₀ ≠ 0`, under regularity + tameness |
| `AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical` | 1,229 | the Hurwitz degree formula, **given** the two canonical-degree facts as hypotheses |
| `AlgebraicCurve.exists_mem_D_eq_smul_D_of_isCurveOver` | 1,422 | at `v` with `v.ord π = 1` and `x ∈ v.toValuationSubring`, `D x = c • D π` with `c` integral at `v` |
| `AlgebraicCurve.genus_ratFunc_eq_zero_of_perfectField` | 1,461 | the projective line has genus zero |

**`map_ne_zero_of_tame` and `two_mul_genus_sub_two_eq_of_degree_canonical` are the same pin
file** (0.977 similarity, the same 80 declarations at the same line numbers). Port them into
**one** module, once.

**Explicitly not this set:** the two downstream variants `AlgebraicCurve.genus_ratFunc_eq_zero`
and `genusFF_ratFunc_eq_zero_of_isAlgClosed` (they cite the head and become ready only after it
lands); `KaehlerDifferential.exists_unique_smul_D_of_transcendental` (23 ln — out, or a rider at
the end if cheap); the `ModularCurve` / `CuspForm` / `WeierstrassCurve` clusters.

## 1. Deliverables

All three modules are new leaves. Namespace `AlgebraicCurve` (keep the pin's names verbatim);
helpers stay `private` exactly where the pin keeps them `private`. Specific mathlib imports only
(**never `import Mathlib`**).

1. **`FLTForHuman/AlgebraicCurve/Differential/Hurwitz.lean`** — the shared engine **once** plus
   the two headlines. Contents: the four pin Prop classes `CanonicalDifferentDegree`,
   `HurwitzCanonicalDecomposition`, `LocalHurwitzExponent`,
   `CanonicalDivisorVariationPrincipal`; the engine lemmas
   (`ord_differentialCoeff_D_of_unit_mul_uniformizer_pow`,
   `hurwitzCanonicalDecomposition_of_tameLocalDifferent`,
   `localHurwitzExponent_tameDifferent_of_universal`,
   `tameLocalDifferentExponent_of_localUnitDerivativeRegular_charZero`,
   `exists_finset_unramified_off`,
   `degree_canonicalDivisor_relation_of_hurwitzCanonicalDecomposition`, …); then
   `map_ne_zero_of_tame` and `two_mul_genus_sub_two_eq_of_degree_canonical` at their wrapper
   statements. Imports: `AlgebraicCurve/Defs/{Place,PlaceCalculus,CanonicalDivisor,IsCurveOver}`,
   `AlgebraicCurve/Canonical/{HasCanonicalDivisor,WeilDifferential}`,
   `AlgebraicCurve/Genus/Stichtenoth`, plus mathlib
   `Mathlib.RingTheory.Kaehler.{Basic,TensorProduct}`.
2. **`FLTForHuman/AlgebraicCurve/Differential/Generation.lean`** —
   `exists_mem_D_eq_smul_D_of_isCurveOver` and the (mostly pre-ported) `s12` prelude it names
   publicly. Its 61 same-file drags are **all `[in-port]`**: import
   `AlgebraicCurve/Canonical/HasCanonicalDivisor.lean` (which already holds
   `exists_unit_D_eq_smul_dCoord_s12`, `dCoordGenerates_of_valSubringKaehlerSpanTop`,
   `isLocalization_centerIdeal_of_isDedekindDomain`) rather than re-proving them.
3. **`FLTForHuman/AlgebraicCurve/Genus/RatFunc.lean`** —
   `genus_ratFunc_eq_zero_of_perfectField` (its 3 drags are `[in-port]`), importing
   `AlgebraicCurve/{P1/Dictionary,P1/UnitNormalForm,P1/KaehlerIntegral,Genus/Stichtenoth}` and
   `AlgebraicCurve/Defs/RatFuncPlaces`. The pin's `solution_inst` (the `HasCanonicalDivisor`
   instance for `RatFunc K`) and `solution_degree` are the proof's two halves; keep them as
   local steps if the wrapper is not a one-liner.

**Sources (wrapper = statement authority, `S_` = proof), with the pin body positions:**

| target | `Theorems/Thm_AlgebraicCurve_<n>.lean` | `P2M/Sol/S_AlgebraicCurve_<n>.lean` |
|---|---|---|
| `genus_ratFunc_eq_zero_of_perfectField` | wrapper | `:1459` `solution` (with `solution_inst` `:1452`, `solution_degree` `:1455`, `…_s17` `:1425`) |
| `exists_mem_D_eq_smul_D_of_isCurveOver` | wrapper | `:1417` `solution` (`…_s12` `:1392`) |
| `map_ne_zero_of_tame` | wrapper | `:1215` `solution` (`…_port` `:1112`) |
| `two_mul_genus_sub_two_eq_of_degree_canonical` | wrapper | `:1215` `solution` (`…_port` `:1192`) |

## 2. The union — collapsing the pin's duplicate copies

`port_advise` on the eight pin files finds **80 names proved in ≥2 target files (≈1,137
removable lines)**. Collapse these before writing; they are one engine, not two:

* the whole `map_ne_zero_of_tame` body ≡ the whole `two_mul_genus…` body (the pair above);
* `ord_differentialCoeff_D_of_unit_mul_uniformizer_pow` (54),
  `hurwitzCanonicalDecomposition_of_tameLocalDifferent` (50),
  `localHurwitzExponent_tameDifferent_of_universal` (50),
  `tameLocalDifferentExponent_of_localUnitDerivativeRegular_charZero` (37),
  `exists_finset_unramified_off` (31),
  `degree_canonicalDivisor_relation_of_hurwitzCanonicalDecomposition` (28),
  `hurwitzCanonicalDecomposition_of_localHurwitzExponent_of_isCurveOver` (27),
  `canonicalDivisorVariationPrincipal_cover_of_hurwitzCanonicalDecomposition` (25),
  `sum_eq_of_hurwitz_tameDifferent` (25), `canonicalDifferentDegree_unique` (24),
  `degree_canonicalDivisorOf_map` (24), `kaehlerMap_eq_smul_dCoordImage` (20), `…`.

**Binder-spelling rows to fix before writing** (`port_advise` §3): 11 names share a conclusion
but not their binders — take the **wrapper's** spelling; headed by
`ordDifferential_dX_of_ne_placeInfty_of_perfectField`, `ordDifferentialWellDefined_ratFunc_of_perfectField`,
`genus_eq_degree_div`, and the two self-pairs `map_ne_zero_of_tame` /
`two_mul_genus_sub_two_eq_of_degree_canonical`. 14 names share a name but not the statement
(`ordDifferential_placeInfty_D_ratFuncX`, `differentialCoeff_placeInfty_D_X_eq`,
`ord_placeInfty_X`, …) — these are the ported `P1` place-infty tails; resolve each by reading
both statements (generalise, or keep the pin's spelling), never by the similarity ratio.

## 3. Route (mathlib first), with recorded negatives

**Reuse, do not re-prove.** The ported surface is the base:
`AlgebraicCurve.Place.{DCoordGenerates,differentialCoeff,ordDifferential,ramificationIndex}`,
`AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg` (the fundamental identity — already
ported), `AlgebraicCurve.canonicalDivisorOf`, `HasCanonicalDivisor`, and the
`P1`/`Canonical` dictionary the substitutions live in. **173 declarations ≈2,579 lines of the
union are already statement-identical in the port** (118/1,354 in `exists_mem_D`, 35/989 in
`genus`, 10/118 in each of the pair; 13 of them port-`private`, so promote or import — see the
topic's §2 for the homes). Mathlib supplies `KaehlerDifferential.D` / `KaehlerDifferential.map`
(`Mathlib/RingTheory/Kaehler/Basic.lean`, `…/TensorProduct.lean`), `PerfectField`
(`Mathlib/FieldTheory/Perfect.lean`), `Module.Free`/`finrank`, `IsScalarTower`,
`Algebra.IsSeparable`.

**Recorded negatives.** No mathlib Hurwitz formula for function fields; no abstract-place
ramification index (the pin's `Place.ramificationIndex` is its own); no "`Ω` generated by `dπ` at
a place" statement; no canonical-different / `LocalHurwitzExponent` vocabulary. The pin's four
Prop classes, the Hurwitz engine and the `ℙ¹` genus computation are the set's new mathematics.

**Worker's first step** (playbook §2.2): run `port_advise --targets build/readyHead_targets.txt`
against the landed tree, `#check` each mathlib name above, and write
`AUDIT-mathlib-ds-head.md` beside the port recording every negative. Do not spend budget looking
for a mathlib Hurwitz formula.

## 4. Checker wiring, build discipline, verification

**Checker wiring** (append last, so a bare last-name match cannot flip):
- `SOURCES` +=, each wrapper **immediately above** its `S_` file:
  `Theorems/Thm_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean`,
  `P2M/Sol/S_AlgebraicCurve_genus_ratFunc_eq_zero_of_perfectField.lean`,
  `Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean`,
  `P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean`,
  `Theorems/Thm_AlgebraicCurve_map_ne_zero_of_tame.lean`,
  `P2M/Sol/S_AlgebraicCurve_map_ne_zero_of_tame.lean`,
  `Theorems/Thm_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean`,
  `P2M/Sol/S_AlgebraicCurve_two_mul_genus_sub_two_eq_of_degree_canonical.lean`.
  None of the eight is in the list today (checked).
- `PORT_FILES` += `FLTForHuman/AlgebraicCurve/Differential/Hurwitz.lean`,
  `FLTForHuman/AlgebraicCurve/Differential/Generation.lean`,
  `FLTForHuman/AlgebraicCurve/Genus/RatFunc.lean` (appended last).
- Baseline: `6235 (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6271 checked)`.
  Expected: `identical` rises by the number of new public declarations, `0 mismatched /
  0 missing`, `promoted`/`renamed`/`own` unmoved. Reconcile every delta.

**Build discipline (copy in).** Edit loop
`timeout N lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`, iterating
individual declarations in a gitignored `Scratch*.lean` (the Hurwitz engine is heavy — the
`ModularForm`-class cone is not involved, but the `P1`/RR cone is); `lake build <module>` only
when a file is done; **one `lake build` per wave**, every build bounded by `timeout` and
serialized with `flock .lake/flt_build.lock`; time each build (high user CPU + timeout = a real
blow-up, ~0 CPU = contention). **Never raise `maxHeartbeats`**; the pin's
`attribute [-instance]`/`[-simp]` blocks and heartbeat bumps are not transcribed. No
`sorry`/`admit`/`axiom`; no `import Mathlib`. Price a cascade with
`python3 tools/deps/build_ladder.py --edit <module>` before a wave. **Do not run any git
command.**

**Verification.**
- `python3 spec/check_flt_statements.py` → 0 mismatched / 0 missing.
- One flocked wave `lake build` of the three modules, then a whole-tree `lake build`.
- `#print axioms` on the four headlines and on the four Prop classes:
  `[propext, Classical.choice, Quot.sound]`; `grep -c sorry` = 0.
- `spec/RiemannRochConsumer.lean` (or a new `spec/DsHeadConsumer.lean`) with real executed
  zones — the pair's two headlines, the Ω-generation headline at a concrete `P1` place, and the
  `ℙ¹` genus headline — no `#check`, no `sorry`, exit 0; deleting a module must make it fail.

## 5. Report shape

Per the H1a template: written lines per module; the by-statement audit of the 173 substitutions
and the 80 once-only names with `grep -c`; the resolved `generalise` rows; the checker
before → after with the reconciliation; the consumer exit and wall time; `#print axioms`; build
wall/user/sys; and the friction findings — in particular how much of the Hurwitz engine the port
already had and whether the pair really is one file. Then update `ds-head-recon.md` §2/§5
(close the answered questions) and fold the generalizable part into
[../porting-playbook.md](../porting-playbook.md) and
[../logs/riemann-roch-friction.md](../logs/riemann-roch-friction.md).
