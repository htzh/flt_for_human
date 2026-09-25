# The Hecke-operator port — status and remaining work

> **IN PROGRESS (paused 2026-09-23).** SETs 1–4 landed: the survey's Stages A, B
> and C are complete, Stage D is half done, and the finiteness half is ruled out
> of scope. Nothing is broken or half-written. To resume, read §5 first, then the
> work orders in [hecke/](hecke/) and the record in
> [../logs/hecke-port.md](../logs/hecke-port.md).

**Status (2026-09-23).** The effort ports the *automorphic* Hecke-operator face of
`Definitions/Def_ModularForm_HeckeOperator.lean` and its consumers — `heckeU` /
`heckeT`, the invariance and analytic layers, the `q`-coefficient action, the
bundled `heckeTLin` / `heckeULin`, the Hecke algebra, the eigenform dictionary
and the integral-lattice vocabulary.

- **18 modules, 3,920 lines**, ~155 new public declarations.
- **Statement checker: 802 identical (53 promoted), 0 mismatched, 0 missing, 14
  own-proof** — up from 618 at the effort's start, with 0 mismatched at every
  checkpoint.
- **`lake build` green: 4,054 jobs, 0 warnings, no `sorry`/`admit`.** No
  `maxHeartbeats` was added or raised anywhere.
- **`#print axioms` clean** on every headline: `propext, Classical.choice,
  Quot.sound`.
- **Commits:** SETs 1–3 in `c7d668b "Hecke operators"`; **SET 4 is uncommitted**
  in the working tree.
- The FFG modules were never touched; a separate effort owns them.

Companion records:

- [studies/hecke-operator-survey.md](../../studies/hecke-operator-survey.md) —
  the inventory of where FLT defines the operators and what it proves (§§1–12),
  and the stage reading (§13, now annotated with status).
- [../logs/hecke-port.md](../logs/hecke-port.md) — the measured record, per set,
  with the SET-2/3/4 reviews.
- [hecke/](hecke/) — the work orders: [TOPIC-slash-invariance.md](hecke/TOPIC-slash-invariance.md)
  (T1), [SET-2.md](hecke/SET-2.md) (T2–T4), [SET-3.md](hecke/SET-3.md) (T5–T7),
  [SET-4.md](hecke/SET-4.md) (T8–T10).
- [studies/hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md)
  — the *other* Hecke face (the divisor correspondence of `math/009`), and why
  this port does not move it (§9 there).
- [../README.md](../README.md) — the module table, kept current per topic.

## 0. What this effort is, and is not

**Is.** The operator that FLT builds as an average of slash actions over the
`ℓ+1` cosets: `heckeU`, `heckeT`, their level-`Γ₀`/`Γ_H`/`Γ₁` invariance, their
`q`-coefficient action, the bundled linear maps, and the algebra they generate.
This is the face other FLT mathematics is *stated against* — eigenforms,
modularity lifting, Taylor–Wiles.

**Is not.** The divisor-correspondence face of `math/009` (`heckeAlphaBar`,
`heckeBetaBar`, `heckeOperatorBar`, `heckeOperatorsCommuteBar`). The two meet
only at the period-map comparison (`periodMap_heckeTLin`/`periodMap_heckeULin`),
which is outside this effort. The coverage report above measures that other face;
this port does not reduce it.

## 1. What shipped, by set

| set | topics | modules | lines | checker |
|---|---|---|---|---|
| SET 1 | T0/T1 — the operator block and the Γ₀ slash-invariance | `Defs/HeckeOperator`, `Defs/HeckeRepresentatives`, `HeckeInvariance` | 710 | 618 → 682 |
| SET 2 | T2 Fricke dedup, T3 analytic regularity, T4 cusp-class | `HeckeFricke`, `HeckeAnalytic`, `HeckeCusps` | 823 | 682 → 696 |
| SET 3 | T5 `q`-coefficient, T6 bundling, T7 commutation + algebra | `Defs/FormalHeckeOperators`, `HeckeQCoeff`, `HeckeOperatorForms`, `ModularCurve/Defs/LaurentSeriesHecke`, `HeckeCommute`, `HeckeAlgebra` | 1,401 | 696 → 772 |
| SET 4 | T8 eigenform interface, T9 integral lattice, T10 **blocked** | `Defs/Eigenform`, `HeckeEigenform`, `Defs/IntegralStructure`, `HeckeLattice`, `Defs/EisensteinChiNegThree`, `Defs/IntegralLattice` | 986 | 772 → 802 |
| SET 5–11 + capstone | route C′ — the integral structure from an integral `Γ₁`-basis (successor effort, §3.2) | `ModularForms/WeightOne/*` (11 modules) | ~33,600 | 1260 → 1312 |

The SET 5–11 row is a **successor effort**, not a Hecke set: it discharges T10's
blocked premise (`HasIntegralStructure`) and is recorded here because it is what
unblocks the finiteness half. Its orders are
[hecke/SET-5.md](hecke/SET-5.md) … [hecke/SET-11.md](hecke/SET-11.md) and
[hecke/TOPIC-capstone-integral-structure.md](hecke/TOPIC-capstone-integral-structure.md).

Module inventory (pin lines in brackets where the module mirrors one):

| module | lines | role |
|---|---|---|
| `ModularForms/Defs/HeckeOperator.lean` | 247 | the matrices **and** the operator block, pin 11–200 |
| `ModularForms/Defs/HeckeRepresentatives.lean` | 353 | the Γ₀ representative block, public once (pin `Def_CuspForm_Gamma1HeckeOperators` 82–455) |
| `ModularForms/HeckeInvariance.lean` | 110 | the three Γ₀ invariance statements |
| `ModularForms/HeckeFricke.lean` | 380 | the Fricke pair, one development (pin 531) |
| `ModularForms/HeckeAnalytic.lean` | 227 | `mdifferentiable`/`periodic`/`isBoundedAtImInfty` (six pin files to one) |
| `ModularForms/HeckeCusps.lean` | 216 | `ModularFormClass.isBoundedAt_*`, `CuspFormClass.isZeroAt_*` (four to one) |
| `ModularForms/Defs/FormalHeckeOperators.lean` | 76 | `PowerSeries.heckeU/V/T` |
| `ModularForms/HeckeQCoeff.lean` | 618 | the `qCoeff`/`qExpansion` layer and the coefficient algebra (four 353-line files to one) |
| `ModularForms/HeckeOperatorForms.lean` | 184 | `heckeTLin`/`heckeULin` on `ModularForm`/`CuspForm` |
| `ModularCurve/Defs/LaurentSeriesHecke.lean` | 135 | `LaurentSeries.heckeU/V/T` |
| `ModularForms/HeckeCommute.lean` | 271 | the 12 commutations (function, bundled, formal) |
| `ModularForms/HeckeAlgebra.lean` | 117 | `heckeGenerators`, `heckeAlgebra`, the three instances, `T`/`U` |
| `ModularForms/Defs/Eigenform.lean` | 45 | `CuspForm.IsNormalizedEigenform` |
| `ModularForms/HeckeEigenform.lean` | 675 | the eigenform dictionary (§8) and the multiplicity statement |
| `ModularForms/Defs/IntegralStructure.lean` | 36 | `intLattice`, `HasIntegralStructure` |
| `ModularForms/HeckeLattice.lean` | 134 | the lattice action (`mem_intLattice_*`) |
| `ModularForms/Defs/EisensteinChiNegThree.lean` | 46 | parked (see §3.2) |
| `ModularForms/Defs/IntegralLattice.lean` | 50 | parked (see §3.2) |

## 2. The survey's stages, mapped

| stage | content | state |
|---|---|---|
| A | the operator block (pin 72–200) | **done** |
| B | the analytic lemmas (survey §5) | **done** |
| C | bundling + commutation + the algebra structure (§3, §7, §9's algebra half) | **done** |
| D | the formal `PowerSeries`/`LaurentSeries` operators | **done** |
| D | Γ_H / Γ₁ / level lowering | **remaining** (§3.1) |
| — | the coefficient action (§6) | **done** (not a lettered stage) |
| — | the eigenform dictionary (§8) | **done** (not a lettered stage) |
| — | the Hecke algebra's finite/free half (§9) | **integral-structure half delivered** (route C′, §3.2); `Module.Finite`/`Free` remaining |
| §12 | the boundary faces | **out of scope** |

## 3. What remains

### 3.1 Stage D — the group/level variants (survey Tiers 2–4)

Measured against the pin at `aa2d8b3`. "Consumers" = theorem nodes whose
statement or proof imports the definition module; "in statements" is the subset
where the dependency is visible in the statement.

| pin module (lines) | consumers | in stmts | inbound prerequisite |
|---|---|---|---|
| `Def_CuspForm_HeckeOperatorFormsGammaH` (262) | **80** | 36 | `Def_CohCarrier_Inst` (**not ported**) + `Def_ModularForm_HeckeOperator` (ported) |
| `Def_ModularForm_AtkinLehnerDatum` (157) | **57** | 44 | none (mathlib only) |
| `Def_CuspForm_Gamma1HeckeOperators` (680) | **24** | 10 | `Def_ModularForm_HeckeOperator` (ported) |
| `Def_CuspForm_HeckeULower` (46) | **1** | 0 | `Def_ModularForm_HeckeOperatorForms` (ported) |

Consumers by subsystem:

- **Γ_H** — `ModularCurve.*` 42 (11 in statements), `CuspForm.*` 30 (23),
  `CohCarrier.*` 7 (1). Top consumers: `CuspForm.stableD` (57), `stableU` (28),
  `stableT` (24), `CuspForm.exists_GammaH_coe_eq_alSlash` (22),
  `ModularCurve.qExpFunctionFieldC_gammaH_le_qExpFunctionFieldC_gammaH_infSubgroup`
  (16).
- **Atkin–Lehner** — `CuspForm.*` 29 (20), `ModularForm.*` 22 (22),
  `ModularCurve.*` 2. Top: `nonempty_of_prime_of_dvd_of_not_sq_dvd` (22),
  `exists_GammaH_coe_eq_alSlash` (22), `exists_mem_Gamma0_alGL_mul_eq` (13),
  `alSlash_alSlash` (10), `alSlash_heckeT_comm` (6).
- **Γ₁** — `CuspForm.*` 13 (5), `ModularCurve.*` 8 (5), `DeligneSerre.*` 2,
  `DihedralWeightOne.*` 1. Top: `qCoeff_heckeTLinOne` (15),
  `HasNebentypus.diamondLinOne_apply_eq_smul` (11),
  `IsEigenformWith.exists_ringHom_rationalHeckeAlgebraOne_mul_eq` (8).
- **`HeckeULower`** — only `qCoeff_eq_zero_of_isNewform_of_sq_dvd` (10),
  proof-only.

**Recommended order, demand over cost: Atkin–Lehner → Γ_H → Γ₁ → `HeckeULower`.**
Atkin–Lehner is self-contained and blocks the most statements; Γ_H has the widest
demand but is gated on porting `CohCarrier.GammaH` (`Def_CohCarrier_Level:133` +
`Def_CohCarrier_Inst`); Γ₁ is the largest file for the least outbound demand, its
bulk being its own `heckeMatrixQ`/`heckeRep` matrix layer; `HeckeULower` is nearly
dead and can be skipped unless a route demands it. Note the two faces are
entangled — `exists_GammaH_coe_eq_alSlash` consumes both Γ_H and Atkin–Lehner.

Confirmed absent from `FLTForHuman/` (`grep -c` = 0): `heckeULowerLin`,
`heckeTLinH`, `heckeULinH`, `diamondLinH`, `heckeTLinOne`, `diamondLinOne`,
`slashOfMemGamma0`.

### 3.2 The finiteness — the integral structure delivered via C′; the `Module.Finite` half remains

`Module.Finite`/`Free ℤ (heckeAlgebra N k S)`, `HasIntegralStructure` and the
eigenbasis-span family were scoped as SET 4's T10 and deliberately stopped. The
measurements (2026-09-23):

- The **general** targets need the Eichler–Shimura / cohomology comparison:
  `hasIntegralStructure_of_two_le` has a **657-node / 263,720 raw-S-line** cone,
  `moduleFinite_heckeAlgebra` 669 / 264,296, and even the 329-line
  `linearIndependent_complex_of_linearIndependent_int` 582 / 241,702. That is
  most of the remaining FLT arithmetic tower, not a topic.
- The only cheap route is the **standalone 4,308-line**
  `moduleFinite_heckeAlgebra_two` at `k = 2` (graph closure = 1: it imports no
  theorem, only three already-ported definition modules). It builds
  `heckeAlgebraIntFull` / `heckeTripleAlgebraFull` from scratch; ~68 lines of its
  tail duplicate the port's operator API, ~4,200 do not.
- So the two "one-liners" (`moduleFinite_heckeAlgebra_two =
  moduleFinite_heckeAlgebra N 2 S`, `hasIntegralStructure_two =
  hasIntegralStructure_of_two_le N 2 le_rfl`) are only one-liners *after* paying
  the 263k-line programme — the wrong trade.

Full detail, including the corrected two-route analysis:
[hecke/TOPIC-t10-finite-algebra.md](hecke/TOPIC-t10-finite-algebra.md) §7. The
endgame version of the decision — the general forms are unavoidable for
`FLT.fermatLastTheorem`, the standalone `k = 2` proof is not reusable by them,
and the Sturm-bound sub-cone is a small mandatory prerequisite — is measured in
[../../studies/hecke-finiteness-coverage.md](../../studies/hecke-finiteness-coverage.md).

**Outcome (2026-09-24): `HasIntegralStructure` is ported without the
Eichler–Shimura tower.** The cheap route was scouted
([route-c-prime-scout.md](../../studies/route-c-prime-scout.md)) and executed as
SET 5–11 plus a capstone: eleven modules under
`ModularForms/WeightOne/` (~33.6k lines, the 53-node cone) and
`WeightOne/IntegralStructure.lean` (374 lines). Checker **1312 identical / 0
mismatched / 0 missing**; full build green; `IntegralStructure.lean` contains
**zero** occurrences of `HeckeEis`, `ModPForms`, `PeriodPair` or the route-A
criterion. So `hasIntegralStructure_of_two_le`/`_two` cost ≈1/8 of route A's raw
`S_`-line cone instead of 263,720 lines.

**The insight worth keeping: the trace lemma.** The brief's proposed ingredient
`exists_basis_gamma1_qCoeff_mem_range_intCast` does not exist in the pin, and the
"small Sturm bound" it was paired with is irrelevant. The real statement is the
*slash* form `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` — a
`ℂ`-basis of `S_k(Γ₁(N))` whose every **`Γ₀(N)`-translate** has integral
`q`-expansion — and the step FLT never takes is a **trace**: summing over the
finite quotient `Γ₀ ⧸ Γ₁` carries an integral `Γ₁`-slash-basis to a spanning
family of integral `Γ₀`-forms, because the trace is `[Γ₀ : Γ₁] •` the identity on
`S_k(Γ₀(N))`. It is elementary but decisive: `Γ₁` is where integrality is proved
(Deligne–Serre's Proposition 2.7, via bounded denominators), and `Γ₀` is where the
Hecke algebra needs it, and the finite-index transfer between the two is the
whole gap. Mathlib's `CuspForm.trace` supplies the bundled map; the port adds an
`IsFiniteRelIndex` instance, a restriction `CuspForm Γ₀ → CuspForm Γ₁`, trace
linearity, and the `qCoeff`-of-trace transport. The route is not throwaway: its
cone is shared with the endgame's weight-one modularity branch (`frey_isModular`),
so only the lemma is route-specific, whereas route B's 4,308-line standalone proof
is a duplicate of a specialisation and is written to be deleted.

**Parked modules, re-classified.** `Defs/EisensteinChiNegThree.lean` and
`Defs/IntegralLattice.lean` (SET 4's T10) were recorded here as unused by either
route. That is now known to be wrong for the first: the weight-one `χ₋₃`
Eisenstein modularity (`EisensteinWeightOne.e1Chi3IsModular`) is the analytic heart
of the C′ ingredient, so keep it. `Defs/IntegralLattice.lean` (the weight-2
`HasIntegralBasis` vocabulary) is still unused by this route.

**Residual work (deferred to a fresh session).** The `Module.Finite`/`Free` half
is untouched: `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` /
`moduleFree_heckeAlgebra` (closures 18–19) now have their hypothesis, `intLattice_fg`
and `moduleFinite_heckeAlgebra` follow on the finiteness side, and the
eigenbasis-span family still needs the Petersson inner product and
`finiteDimensional_Gamma0`. Separately, the C′ payoff should be written up as a
**redundancy-reduction record**: a short note quantifying what route C′ avoided
(route A's 657 nodes / 263,720 lines vs the 53-node cone / ~33.6k lines plus the
374-line capstone) and naming the reusable pattern — *prove integrality on the
smaller (index-finite) subgroup and transfer by the trace* — as the first entry in
a standing "redundancy reduction" line of work.

### 3.3 The boundary (survey §12) — not this effort

The J₀(N) correspondences (`math/009`, measured in the coverage report), the
group-cohomology `CohCarrier.heckeT`, the Eichler–Shimura comparison, the
mod-`p` forms, the Taylor–Wiles machinery, and the adelic/quaternionic/local
Langlands Hecke operators are separate faces with their own consumers.

## 4. Findings worth keeping

- **The trace lemma — the insight that made route C′ work.** Prove integrality on
  the *smaller* subgroup and transfer it up by the trace. Concretely: FLT proves
  the integral-slash basis for `S_k(Γ₁(N))` (Deligne–Serre Prop. 2.7: rational
  structure + bounded denominators, no cohomology), but the Hecke algebra needs
  integrality for `S_k(Γ₀(N))`. `Γ₁ ⊴ Γ₀` has finite index, and the trace
  `Σ_{q : Γ₀ ⧸ Γ₁} (−) ∣[k] q` is `[Γ₀ : Γ₁] •` the identity on `Γ₀`-forms, so the
  traces of the basis **span** `S_k(Γ₀(N))` and stay integral. One lemma, no Sturm
  bound, every weight, and it replaces a 657-node / 263,720-line Eichler–Shimura
  comparison with a 53-node cone plus 374 lines
  (`ModularForms/WeightOne/IntegralStructure.lean`). The scout had the ingredient
  name wrong (`…mem_range_intCast` does not exist; the working one is the *slash*
  form `…qCoeff_slash_mem_range_intCast`) and paired it with the wrong crutch (the
  Sturm bound) — but the *shape* of the proposal was right, and the missing step
  was not in FLT at all. Full record:
  [../../studies/route-c-prime-scout.md](../../studies/route-c-prime-scout.md),
  [../../math/013-integral-structure-gamma1-basis.md](../../math/013-integral-structure-gamma1-basis.md),
  [hecke/TOPIC-capstone-integral-structure.md](hecke/TOPIC-capstone-integral-structure.md).
  **This is the first entry in a standing redundancy-reduction line of work** (§3.2
  residual).
- **FLT duplicates whole proof blocks per `S_` file, and the port's job is to
  write each once.** Measured dedups: the Γ₀ representative block (3 files), the
  analytic head (six 353-line files), the `q`-coefficient tail (four more of the
  same 353-line block), the cusp-class block (four 132-line files), the Fricke
  pair's hand-rolled trace (mathlib's `ModularForm.trace` replaces it). Set total
  for SETs 2–4: **3,177 pin → 823 port lines (0.26)**.
- **A private copy in the port was a weakening.** The old `PhiGenDescends.lean`
  `_mul_of_eq` lemmas had dropped the pin's `g' 1 0 = …` conjunct; the Γ₀(N/p)
  lowering needs it. Restored in SET 1. Lesson: promote from the pin, not from
  the private copy.
- **The statement checker was extended once, audited, and is sound.** SET 3 added
  an enclosing-namespace-qualified lookup key (plus `noncomputable` in the decl
  regex). Both acceptance paths require exact normalized-statement equality; a
  deliberate corruption of one token was caught (1 MISMATCH) and reverted
  byte-identically. Public dotted matches now count as "promoted" (34 → 53);
  `OWN_PROOFS` is unchanged.
- **A work order mis-scouted its blocker.** T10's premise (the χ₋₃ Eisenstein
  route) was false; the real dependency is the Eichler–Shimura tower. Lesson
  recorded at the corrected §7: **measure the dependency cone before scoping a
  topic** — the graph reader makes it cheap.
- **Deliberate route divergences, statements unchanged:** the Fricke trace
  (mathlib `ModularForm.trace` + a `coe_trace` bridge), and
  `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne` proved
  coefficientwise because the pin's `exists_degeneracy_Gamma0` is not ported.

## 5. How to resume

**Read order.** §0–§3 above; then the work order for the piece you are taking;
then `logs/hecke-port.md` for the measured record; then the survey for the pin
inventory. The work orders contain the exact statements, route notes and build
discipline.

**The commands.**

```bash
cd lean
timeout 180 lake build                       # green, 4,054 jobs
python3 spec/check_flt_statements.py         # 802 identical, 0 mismatched, 0 missing
```

`#print axioms <name>` on any headline; probes go in the gitignored
`Scratch*.lean`. Never add or raise `maxHeartbeats` (the lakefile's global cap is
4,000,000); on a stall, quarantine and restate over the concrete type.

**Finding consumers for a pin module** (the outbound map of §3.1) uses the graph
reader in `tools/deps`:

```python
from fltdata import FltData
d = FltData(); stem = 'CuspForm_HeckeOperatorFormsGammaH'
di = d.def_index[stem]
cons = [i for i in range(len(d.names))
        if di in d.stmt_defs(i) or di in d.proof_defs(i)]
```

**The conventions that bind** (SET-2/3/4 §3): statements verbatim from the
`Theorems/` wrappers with their binders; each shared block written once; new
wrappers appended to `SOURCES` and modules to `PORT_FILES`; no commits (the user
commits); do not touch the FFG modules.

**If you take Stage D**, start with Atkin–Lehner (self-contained, 57 consumers),
and write its work order with the §3.1 numbers. **If you take the finiteness**,
`HasIntegralStructure` is already ported via route C′ (§3.2) — the scouting this
paragraph used to ask for was done and succeeded, and the route's numbers and the
trace-lemma lesson are §3.2 and §4. What remains is the `Module.Finite`/`Free`
half (`HasIntegralStructure.moduleFinite/Free_heckeAlgebra`), `intLattice_fg`,
`moduleFinite_heckeAlgebra`, and the eigenbasis-span family — plus the
redundancy-reduction write-up §3.2 names as residual.

## 6. Pointers

- [hecke-operator-survey.md](../../studies/hecke-operator-survey.md) — the pin
  inventory and the stage reading.
- [route-c-prime-scout.md](../../studies/route-c-prime-scout.md) — the C′ scout:
  the trace lemma, the corrected ingredient, the measured cones.
- [../math/013-integral-structure-gamma1-basis.md](../../math/013-integral-structure-gamma1-basis.md)
  — the mathematics of §3.2/§4 (rational structure, bounded denominators, trace).
- [hecke/](hecke/) — this effort's work orders, including
  [SET-5](hecke/SET-5.md) … [SET-11](hecke/SET-11.md) and the capstone
  [TOPIC-capstone-integral-structure.md](hecke/TOPIC-capstone-integral-structure.md).
- [hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md) —
  the other Hecke face and its measured coverage.
- [../logs/hecke-port.md](../logs/hecke-port.md) — the per-set record and reviews.
- [hecke/](hecke/) — this effort's work orders.
- [../README.md](../README.md) — the module table.
- [PORTING-FFG.md](PORTING-FFG.md), [PORTING-AC.md](PORTING-AC.md) — the two
  closed efforts this one is layered on, and the format this file follows.
