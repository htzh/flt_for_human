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
| — | the Hecke algebra's finite/free half (§9) | **out of scope** (§3.2) |
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

### 3.2 The finiteness — out of scope (decided 2026-09-23)

`Module.Finite`/`Free ℤ (heckeAlgebra N k S)`, `HasIntegralStructure` and the
eigenbasis-span family were scoped as SET 4's T10 and deliberately stopped. The
measurements:

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

**Parked modules.** `Defs/EisensteinChiNegThree.lean` and
`Defs/IntegralLattice.lean` (SET 4's T10) are the mod-3 / `HasIntegralBasis`
vocabulary. Neither route above uses them; they are green and harmless. Keep them
for a future congruence topic or revert them — they are not prerequisites of
anything ported.

### 3.3 The boundary (survey §12) — not this effort

The J₀(N) correspondences (`math/009`, measured in the coverage report), the
group-cohomology `CohCarrier.heckeT`, the Eichler–Shimura comparison, the
mod-`p` forms, the Taylor–Wiles machinery, and the adelic/quaternionic/local
Langlands Hecke operators are separate faces with their own consumers.

## 4. Findings worth keeping

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
do not reach for the Eichler–Shimura route without first scouting a cheaper
`HasIntegralStructure` proof (an explicit integral spanning family via
`exists_basis_gamma1_qCoeff_mem_range_intCast` plus the small Sturm bound,
`sturm_bound_of_isArithmetic` 29 lines / 287-line cone) — the two-route analysis
is in `TOPIC-t10-finite-algebra.md` §7.

## 6. Pointers

- [hecke-operator-survey.md](../../studies/hecke-operator-survey.md) — the pin
  inventory and the stage reading.
- [hecke-commute-bar-coverage.md](../../studies/hecke-commute-bar-coverage.md) —
  the other Hecke face and its measured coverage.
- [../logs/hecke-port.md](../logs/hecke-port.md) — the per-set record and reviews.
- [hecke/](hecke/) — this effort's work orders.
- [../README.md](../README.md) — the module table.
- [PORTING-FFG.md](PORTING-FFG.md), [PORTING-AC.md](PORTING-AC.md) — the two
  closed efforts this one is layered on, and the format this file follows.
