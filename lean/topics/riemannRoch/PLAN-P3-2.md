# Phase 3.2 scoping — the ℙ¹ residue core (row 2)

**Status: EXECUTING (2026-09-30).** The measurement is done, the boundaries below
are adopted, and **3.2a is scoped and dispatched**
([WORKORDER-P3-2a-p1-dictionary.md](WORKORDER-P3-2a-p1-dictionary.md)). The P3.1
carried debt was closed first (see `../../logs/riemann-roch-friction.md`). Build
economy for 3.2 follows [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3:
every set lands in a new file, per-module builds, no whole-tree build until the
phase milestone.

Method: [../porting-playbook.md](../porting-playbook.md) §2.1–§2.4 (measure the
cone, dedup before coding, drop by count). Inputs are the planning-session
`port_advise` outputs, re-read and re-derived here:
`tools/deps/build/{pf_core,pf_agreement,pf_commute,pf_transfer}_advise.json` and
`pf_core.txt` (the row-2 node list).

## 1. What `port_advise` says

```bash
python3 port_advise.py --nodes "$(cat build/pf_core.txt)" --json build/pf_core_advise.json
```

→ 34 target files (16 `S_` + 18 `Theorems/` wrappers), 1,175 target declarations,
port corpus 7,020, pin pool 11,696.

| quantity | value | note |
|---|---:|---|
| raw (`S_` files only) | **29,118** | exactly the 16 files |
| substitutions | 199 decls / **3,378 ln** | "identical statement already in the port" |
| — of which false positives | 32 / 731 ln | `def … : Prop` matched to `E1Chi3IsModular` with "42 copies"; do not bank |
| port-once (`in_target_pair`) | 197 names / **9,526 removable** | the shared prelude |
| once-each union of that prelude | ≈5,105 | 14,631 shared-span total − 9,526 removable |
| per-file unique content | **14,531** | declaration spans of names not in ≥2 target files |
| projected written | **≈16,214** | 29,118 − 3,378 − 9,526 (≈16,945 if the 731 false-positive lines are not banked) |

So the strategy's ≈17,300 is in range: **row 2 really is ≈16–17k written**, about
10× the largest set ported so far (H1a, ≈1.6k). It cannot be one phase.

**Raw is dominated by four files (87%)**:

| pin `S_` file | raw | shared | unique |
|---|---:|---:|---:|
| `…_trace_localResidue_placeInfty_X_pow_eq_zero` (master ℙ¹) | 13,173 | 4,549 | 8,918 |
| `…_trace_localResidue_finitePlace_add_trace_localResidue_placeInfty_eq_zero` | 5,776 | 4,557 | 1,153 |
| `…_residueTheorem_ratFunc_of_perfectField` (PF base case) | 4,340 | 3,352 | 810 |
| `…_trace_localResidue_finitePlace_div_pow_eq_zero` | 2,150 | 1,200 | 1,006 |
| `…_ord_placeOfPoint_algebraMap` | 1,263 | 197 | 1,078 |
| `…_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_…` | 1,244 | 351 | 899 |
| `…_Place_sum_ramificationIndex_mul_inertiaDeg` | 976 | 425 | 566 |
| eight small `evalAt_*` / `ord_placeInfty` / `deg_placeInfty` / `isRational` files | 196 | 0 | 101 |
| **total** | **29,118** | 14,631 | 14,531 |

## 2. The structural finding: rows 2 and 6 are one development

The master ℙ¹ file and the **K base file** (`…_residueTheoremK_ratFunc_of_isAlgClosed`,
row 6, 13,170 ln / 579 decls) share **572 of 580 declaration names (99%)**. The
master's remaining 8 names are exactly the renamed twins:

```
PF master:  p1PlaceInfty, p1PlaceInfty_ne_ofHeightOneSpectrum,
            p1PlaceInfty_toValuationSubring, placeInfty_eq_p1PlaceInfty,
            higherPoleCorrection{,Aux,'}{,_apply_of_mem,_uniformizer_pow_inv}
K base:     placeInfty, placeInfty_ne_ofHeightOneSpectrum,
            placeInfty_toValuationSubring, higherPoleCorrection{,Aux,…}
```

The other three big files share 97% (atom 2), 49% (atom 3) and 69% (base case)
with the K base. The pin literally shipped the same ℙ¹ engine twice, once per
ending, under the `p1`-prefixed and un-prefixed names.

Consequences for scoping:

- **The engine is not row-2-specific.** It is written **once** and serves both the
  PF ending (row 2/3.5) and the K ending (row 6); PORTING-RR §3 already names the
  home `Defs/P1ResidueCore.lean`. The two "endings" are marginals (row 6's
  marginal over the shared core is ≈2,000 written; the PF side's is the handful of
  renamed declarations above).
- **Splitting row 2 by its four files is wrong** — it re-writes the shared core
  four times. Measured: pricing the four files as independent groups gives
  ≈25,700 written (the shared prelude counted 4×), against ≈16,200 for the union.
- **The hidden renaming duplication is small.** Of the 33 in-target binder-only
  near-duplicates (`near_duplicates`, `binder_only`), the once-each saving is only
  ≈625 lines; the 14,531 "unique" content is genuinely distinct proof, not an
  accounting artifact.

## 3. Proposed boundaries

**Step 0 — dedup and home the engine once (prerequisite, not a sub-phase).**
Union the four big files **plus the K base file** (they are the same development),
extract the exact-shared 197-name prelude and the renamed twins into
`Defs/P1ResidueCore.lean`, and re-run `port_advise` on the union before writing
any module. This is the biggest single lever (9,526 removable inside row 2 alone,
more across row 6) and it must be measured, not eyeballed.

**Every 3.2 block also gets a mathlib audit before it is ported** (playbook §2.2),
as 3.1 did — the dictionary's `RatFunc.inftyValuation`/`RatFunc.intDegree` leads
alone may remove much of the ord/degree re-derivation, and the same question is
open for the engine's `p1PlaceInfty` and the `p0n22`/`ag9b` computation. The audit
note is `AUDIT-mathlib-p3-2a.md` for the dictionary, and the worker's brief carries
the leads; later blocks get `AUDIT-mathlib-p3-2b…`.

**Then split by mathematical object (playbook §3.3), not by source file.** From
the union of the four big files (687 declarations / 14,709 once-each lines,
grouped by the pin's own name prefixes):

| phase | content (pin prefixes) | once-each | note |
|---|---|---:|---|
| **3.2a — ℙ¹ dictionary / ord layer** | the **standalone node files**: `ord_placeOfPoint_algebraMap` (1,263), `ord_placeInfty{,_algebraMap}`, `deg_placeInfty`, `isRational_iff_deg_eq_one`, the `evalAt_*` family, the `PlaceEvaluation` interface, and (audit gaps) the dropped `placeOfPoint` block + `PlaceEvaluationAlgebra` | ≈1,445 + ≈200 gaps | **dispatched 3.2a**, three new modules; the master file's `p1PlaceInfty`/`P1Tower` extraction is deferred to 3.2b–d |
| **3.2b — ord / valuation algebra prelude** | `ord_*`, `exists_*`, `valSubring*`, `gate_*`, `inst*`, `mem_*`, `kaehlerResid*`, `canonicalLocal*` | ≈2,600 | **much already substitution** — phase 1/2 landed `valSubringKaehler*`, `isLocalization_centerIdeal*`, `gate_adjoin_subset_valuationSubring_of_mem`, `mem_valuationSubring_of_isIntegral*`; price the glue, not the leaves |
| **3.2c — local residue-at-∞ calculus** | `P1PlaceInftySimplePoleResidueEulerValue*`, `OrdDifferentialWellDefined`, `ordDifferent*`, `p1DifferentialCoeff*`, `simplePole*`, `higherPole*` | ≈1,700 | the simple-pole residue values and the differential-coefficient interface |
| **3.2d — principal parts + differential coefficients** | `p0n22_cpf_res_*`, `mp72a10*`, `ag9b*`, `ratFuncDXCoe`, `not_dvd_derivative*`, `res_differentialCoeff*` | ≈2,700 | the two residue atoms' shared computation (`p0n22` 882, `ag9b` 820, `mp72` 666) |
| **3.2e — the PF atoms + base case** | the three `trace_localResidue_*` uniquenesses + `residueTheorem_ratFunc_of_perfectField` | ≈1,000 | the PF side's marginal over 3.2a–d |
| **row 6 — the K ending** | `residueTheoremK_ratFunc_of_isAlgClosed` marginal + `residueTheoremK_of_isAlgClosed` | ≈2,000 | PORTING-RR §3 already prices it as a marginal; it consumes 3.2a–d |

Each proposed phase is ≈1–3k written — within the ≈1k-per-worker staffing rule,
which row 2 as a whole violates by ~16×.

**Recommended sequencing.** Do step 0 first (it shrinks every later phase), then
3.2a → 3.2b (mostly import) → 3.2c → 3.2d, then the two endings 3.2e and row 6
together — they are the same code with different names.

### 3.1 Closeout — 3.2a ACCEPTED (2026-09-30)

Three **new** modules, 1,633 written lines, no cascade:

| module | ln | content |
|---|---:|---|
| `Defs/PlaceEvaluation.lean` | 104 | the pin's `Def_AlgebraicCurve_PlaceEvaluation` interface |
| `Defs/PlaceEvaluationAlgebra.lean` | 185 | gap B: the `Divisor.evalFun_*` law layer |
| `Defs/P1Dictionary.lean` | 1,344 | the 11-node union + gap A's `placeOfPoint` block |

Independently re-verified by the manager: checker **3212 → 3316 identical / 0
mismatched / 0 missing / 30 own-proof** (3346 checked); per-module builds green
(2.0 / 2.6 / 5.3 s, deps only, **no whole-tree build**); `#print axioms` on the
eleven public nodes plus `placeOfPoint`/`deg_placeOfPoint`/`principalDivisor_isPrincipal`
all `[propext, Classical.choice, Quot.sound]`; hygiene clean.

The **measurement-gap lesson** (playbook §2.1): the 91-declaration `port_advise`
reading was a lower bound — it missed the dropped `placeOfPoint` block (5 decls)
and the entire `PlaceEvaluationAlgebra` law layer (6 nodes / 160 ln). The §2.2
audit caught both. **Every later block is audited before it is dispatched.**

**Refactor debt carried (cascade-avoidance, no statement moves):** `P1Dictionary`
transcribes public copies of `PrincipalDivisors/RatFuncDegree.lean`'s
`private` `exists_sub_algebraMap_intDegree_neg`, `single_add_single_apply_eq_ord`,
`degree_single_add_single` (the port copies are more general; the public copies are
the pin's specializations). A later promotion round can make the `RatFuncDegree`
copies public and drop the transcriptions. The audit note is
`AUDIT-mathlib-p3-2a.md`.

## 4. Reproduce

```bash
cd tools/deps
# the row-2 node list is the planning session's "core" group
python3 port_advise.py --nodes "$(cat build/pf_core.txt)" --json build/pf_core_advise.json

# the union that the boundary proposal is built on (row 2's four big files)
python3 - <<'PY'
import json, os, re
d=json.load(open('build/pf_core_advise.json'))
pin=os.path.expanduser('~/proj/fermats-last-theorem')
DECL=re.compile(r"^(?:(?:private|noncomputable|protected|scoped)\s+)*(?:def|theorem|lemma|abbrev|structure|instance)\s+([\w.'ₐ]+)", re.M)
big=[t for t in (x.replace('/home/haitao/proj/fermats-last-theorem/','') for x in d['targets'])
     if 'P2M/Sol/S_' in t and any(k in t for k in
     ('placeInfty_X_pow_eq_zero','finitePlace_add','finitePlace_div_pow','residueTheorem_ratFunc_of_perfectField'))]
u={}
for t in big:
    txt=open(f'{pin}/{t}',errors='replace').read(); ms=list(DECL.finditer(txt))
    for i,m in enumerate(ms):
        s=m.start(); e=ms[i+1].start() if i+1<len(ms) else len(txt)
        u[m.group(1).rsplit('.',1)[-1]]=min(u.get(m.group(1).rsplit('.',1)[-1],10**9), txt[s:e].count('\n')+1)
print(len(big),'files;',len(u),'union decls;',sum(u.values()),'once-each lines')
PY

# the 99% engine overlap with row 6's K base file
python3 - <<'PY'
import os, re
pin=os.path.expanduser('~/proj/fermats-last-theorem')
DECL=re.compile(r"^(?:(?:private|noncomputable|protected|scoped)\s+)*(?:def|theorem|lemma|abbrev|structure|instance)\s+([\w.'ₐ]+)", re.M)
def names(p): return {m.group(1).rsplit('.',1)[-1] for m in DECL.finditer(open(p,errors='replace').read())}
A=names(f'{pin}/P2M/Sol/S_AlgebraicCurve_RationalFunctionField_trace_localResidue_placeInfty_X_pow_eq_zero.lean')
B=names(f'{pin}/P2M/Sol/S_AlgebraicCurve_residueTheoremK_ratFunc_of_isAlgClosed.lean')
print(len(A), len(B), 'shared', len(A&B))
PY
```

## 5. Decision needed

The cut above is a proposal. The open choices for the human:

1. **Confirm the engine-vs-endings merge** (rows 2 and 6 planned together on one
   `Defs/P1ResidueCore.lean`) rather than the table's separate rows.
2. **Confirm or re-cut the four engine blocks** (3.2a–d) — the prefix grouping is
   the pin's own naming, not a proof-dependency measurement; the step-0
   `port_advise` on the union will sharpen it.
3. Whether the small generic-residue files (`Place.evalAt_*`,
   `isRational_iff_deg_eq_one`, `sum_ramificationIndex_mul_inertiaDeg`,
   `CanonicalLocalResidueDataK_res_…`) belong in 3.2a/3.2b or in an existing
   `Defs/` home.
