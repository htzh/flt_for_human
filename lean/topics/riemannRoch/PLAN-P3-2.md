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
| **3.2b — ord / valuation algebra prelude** | `ord_*`, `exists_*`, `valSubring*`, `gate_*`, `inst*`, `mem_*`, `kaehlerResid*`, `canonicalLocal*` | 848 (chunk 1) | **chunk 1 ACCEPTED** (decls #0–#144, pin 295–3387, → `Defs/P1ResidueCore.lean`); ~100/145 rows import-discharged. **3.2c dispatched** (rows #145–#289) |
| **3.2c — local residue-at-∞ calculus** | `ord_placeInfty*`, `principalDivisor*`, `degree_*`, `D_ratFuncX*`, `ordDifferential_*`, `p1PrincipalPartAtom`, `ag9b*`, `mp72*` | 1,581 (chunk 2) | **chunk 2 ACCEPTED** (decls #145–#289, pin 3388–6744); 70/145 rows import-discharged |
| **3.2d′ — generic local residue calculus** | the whole `CanonicalLocalResidueDataK.res_differentialCoeff_*` + `p0n22_cpf_res_*` file (1,244 ln) | 1,229 | **ACCEPTED** — NEW `Defs/LocalResidueCalculus.lean`, its own natural subject home; runs **before** 3.2d so the ℙ¹ core imports these names |
| **3.2d — principal parts + differential coefficients** | `p0n22_cpf_res_*`, `mp72a10*`, `ag9b*`, `ratFuncDXCoe`, `not_dvd_derivative*`, `res_differentialCoeff*` | ≈2,700 | the two residue atoms' shared computation; master chunk 3 = decls #290–#434 |
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

### 3.2 Closeout — 3.2b chunk 1 ACCEPTED (2026-09-30)

`Defs/P1ResidueCore.lean` (new, **848 ln**) = master declarations #0–#144 (pin
295–3387). Manager re-verified: checker **3316 → 3356 identical / 0 mismatched / 0
missing / 30 own-proof** (3386 checked); forced `lake build` green (2.1 s warm /
7.4 s cold, 2842 jobs, **no cascade**); `#print axioms` on the sampled public
surface all `[propext, Classical.choice, Quot.sound]`; hygiene clean.

The engine split works because the general machinery is **already ported**:
~100 of the 145 rows are import-discharged to phase 3.1b-ii
(`CanonicalLocalResidueInstanceV2.lean`), phase 1/2 (`PushPull`,
`HasCanonicalDivisor`), phase 3.2a (`P1Dictionary`) and `Genus/Index`. The audit
(`AUDIT-mathlib-p3-2b.md`, 631 ln; **108 SUBSTITUTE / 30 PROOF-INGREDIENT / 7
BESPOKE**) machine-checked the mathlib route (`Module.Basis.traceDual_powerBasis_eq`,
`minpolyDiv_*`, `AdjoinRoot.*`, `Valuation.map_add_of_distinct_val`,
`IsDiscreteValuationRing.*`, `AdicCompletion.*`) and corrected the plan's chunk
boundary (`ord_ofHeightOneSpectrum_of_span` is row #145, so it opens 3.2c).

One structural call to keep: the pin's `p1PlaceInfty` is the port's `placeInfty`
(the same `Place.mk`), so chunk 1 lands `@[reducible] def p1PlaceInfty := placeInfty K`
and the five same-name ℙ¹ lemmas stay imported; downstream keeps the `p1PlaceInfty`
spelling. **3.2c** (rows #145–#289, pin 3388–6744) is dispatched.

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

## 5. Decisions recorded

1. **Rows 2 and 6 are largely duplicates, and row 6 stays residual — no merge now
   (human, 2026-09-30).** Row 6's work item is already priced as the *residual*
   over the shared engine (PORTING-RR §3), which is why it only talks about
   marginal work. The engine `Defs/P1ResidueCore.lean` is written **once** and
   serves row 6 as well, but pulling row 6 forward is out of scope for 3.2.
2. **The four engine blocks are executed as ordered chunks of the master file**
   (3.2b = #0–#144, 3.2c = #145–#289, 3.2d = #290–#434, 3.2e = #435–#579 + the
   atom/base tails), into one module. The prefix grouping guided the block labels;
   the chunk boundaries are the pin's declaration order, because reordering an
   intricate dependency chain costs more than it buys. The step-0 `port_advise` on
   the union (`build/p32_engine_advise.log`) confirmed the scale (279 substitutions,
   8,251 removable).
3. **The small generic-residue files — measured dispositions (2026-09-30).** These
   are generic over `Place`, not ℙ¹-specific, so they should not live in the ℙ¹
   dictionary module:

| pin file(s) | pin ln | what it is | port status | disposition |
|---|---:|---|---|---|
| `Place_evalAt_{algebraMap,congr,inv,mul,ne_zero,zpow}` (6 nodes) + `Place_isRational_iff_deg_eq_one` | ≈156 | the generic `evalAt`/`IsRational` evaluation lemmas | **ported by 3.2a**, but into `Defs/P1Dictionary.lean` | **layer mismatch** — move to `Defs/PlaceEvaluation.lean` beside the `evalAt` definition; refactor round, statements unchanged, checker unaffected |
| the six larger `evalAt_*` (`…_algebraMap_eq_evalAt_restrict`, `…_eq_zero_iff_one_le_ord`, `…_map_eq_of_comap_eq`, `…_norm_eq_prod_fiber` 672, `…_smul_smul_eq_baseAut_evalAt`, `…_trace_eq_sum_fiber` 938) | ≈1,803 | the `evalAt` trace/norm/fiber API | **not ported** | not in row 2's core (forward-cone nodes); decide when the forward cone reaches them, home beside `PlaceEvaluation` |
| `Place_sum_ramificationIndex_mul_inertiaDeg` | 976 (53 decls) | the fibre ramification–inertia identity | **already in the port**: `SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg` (`Defs/PushPull.lean:678`) plus `…_fiberOver`/`…_le_finrank` (`WeilExchange/FiberOverCount.lean`) | **substitute** — import; no new home; row 2's `RamificationInertiaIdentity` (#236) is its thin wrapper |
| `Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap` | 1,244 (38 decls, the `p0n22_cpf_res_*` block) | the generic local-residue statement: `res` of `differentialCoeff · D · (uniformizer^n)⁻¹` under `Surjective algebraMap` | **not ported** (grep 0) | the one row-2 target not covered by the master chunks: its own small set into a new `Defs/LocalResidueCalculus.lean` (or folded into `Defs/LocalResidue.lean`), generic and independent of the ℙ¹ engine |

So the only outstanding small generic file is the last row: **it needs its own
mini-set** (call it 3.2d′, dispatched after the engine chunks, or with 3.2d), because
the `p0n22_cpf_res_*` names it defines sit under the ℙ¹ computation.

4. **Subject homes, not lumping (human, 2026-09-30: "large enough to deserve
   natural subject homes").** Adopted:
   - **`Defs/` is for definitions only; a theory file must not live there (human,
     2026-09-30).** The 1,244-line generic local-residue calculus moves out of
     `Defs/` to a **new subject theory directory `AlgebraicCurve/LocalResidue/`**
     (file `Calculus.lean`); its companion definitions (`Defs/PlaceEvaluation.lean`)
     stay in `Defs/`. **The move is executed at the 3.2e gate** (renaming now would
     race the running chunk-4 worker, which appends to a module that imports it).
     `AlgebraicCurve/` has no top-level `.lean` files today, so a dir is the
     idiomatic choice; `LocalResidue/` is the human-suggested "Local … or something
     else descriptive".
   - the same rule applies to the ℙ¹ core: `Defs/P1ResidueCore.lean` is the ℙ¹
     residue **theory**, so it should follow into `AlgebraicCurve/LocalResidue/`
     (e.g. `P1Core.lean`) once the 3.2 closeout refactor round collapses the
     `private`-helper duplication; `Defs/P1Dictionary.lean` (the ℙ¹ place/ord
     dictionary) is definitional and stays in `Defs/`.
   - the ~1,803-line `evalAt` trace/norm/fiber API → a `PlaceEvaluation`-adjacent
     home when the forward cone reaches it, not folded into the ℙ¹ dictionary;
   - the seven `evalAt`/`IsRational` leaves now in `Defs/P1Dictionary.lean` → move to
     `Defs/PlaceEvaluation.lean` in the next refactor round;
   - if the core passes ~4k lines, its subject sections become modules inside
     `LocalResidue/` (`P1PlaceOrd`, `P1DifferentialCoeff`, `P1PrincipalParts`, `P1Atoms`).

### 3.3 Closeout — 3.2c chunk 2 ACCEPTED (2026-09-30)

`P1ResidueCore.lean` 848 → **2,429 ln** (rows #145–#289, pin 3388–6744). Manager
re-verified: checker **3356 → 3422 identical / 0 mismatched / 0 missing / 30
own-proof** (3452 checked); forced build green (1.9 s warm / 11.6 s cold, 2842 jobs,
only this module's `.olean` moved); `#print axioms` on the sampled surface clean;
hygiene clean. 70 of 145 rows import-discharged. Carried **promotion debt**: rows
#240/#241/#243/#244 need the `F ≃ₐ[K] F` divisor-action layer that
`Defs/SemilinearAut.lean` deferred, transcribed `private` from
`Def_AlgebraicCurve_DivisorClassGroup.lean` (`Place.ord_smul`, `Place.deg_smul`,
`MulAction`/`DistribMulAction` instances, `smul_*`, `degree_smul`); a later round
promotes it. `AUDIT-mathlib-p3-2c.md` (668 ln; 72/67/6) folded into its work order.

### 3.4 Closeout — 3.2d′ ACCEPTED (2026-09-30)

**`Defs/LocalResidueCalculus.lean`** (new, **1,229 ln**; 26 public + 9 private) =
the whole generic `CanonicalLocalResidueDataK.res_differentialCoeff_*` /
`p0n22_cpf_res_*` file. Manager re-verified: checker **3422 → 3448 identical / 0
mismatched / 0 missing / 30 own-proof** (3478 checked); forced build green (2.0 s
warm / 9.0 s cold, 2689 jobs, no cascade); axioms clean; hygiene clean.

The audit (`AUDIT-mathlib-p3-2dprime.md`, 448 ln; **9 SUBSTITUTE / 29
PROOF-INGREDIENT / 0 BESPOKE** — the first phase-3 block with no new vocabulary)
corrected this set's lead: the char-0 `ag9b13t_*`/`ag9b14c_*` engine is **not** in
the port, so rows 10/15 and the headline's `ringChar = 0` branch are new
transcriptions. Mathlib supplies every derivation/Frobenius leaf.

**Carried debt (for the 3.2 closeout refactor round, cascade-free — nothing imports
either module yet):** five helpers are duplicated `private` in both
`LocalResidueCalculus.lean` and `P1ResidueCore.lean` — `Place.ord_add_eq_min` and
the four `ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*` — because
the generic module must precede the core's later chunks and cannot import them. The
fix: make the five public in `LocalResidueCalculus`, import it from `P1ResidueCore`,
drop the core's copies. **3.2d (chunk 3, rows #290–#434) is dispatched** with
`AUDIT-mathlib-p3-2d.md`.

### 3.5 Closeout — 3.2d chunk 3 ACCEPTED, and the dedup refactor (2026-09-30)

`P1ResidueCore.lean` 2,429 → **3,971 ln** (rows #290–#434). Manager re-verified:
checker **3448 → 3530** before the refactor, build green (16.7 s, no cascade),
axioms clean. The audit found that **98 of the chunk's 145 rows re-prove the phase-2
canonical-divisor file**; the manager steered the worker before it hit the block, so
47 rows were omitted as exact public copies and 9 landed as `_s12` aliases. Ten
pin-private `_s12` rows were re-landed `private` (promotion debt).

**Dedup refactor (bounded, one pass).** The chunk-3 order's
`import Defs/LocalResidueCalculus` was blocked because both modules declared
`gate_canonicalLocalResidueDataK_uniformizer_inv` publicly. Fix: remove the core's
unused copy and add the import, leaving the five `private` helpers duplicated
(mangled names, no clash). A first scripted bulk removal mangled section structure
and was reverted from backups — **do declaration surgery by hand**, not by line
range. Post-refactor: checker **3529 / 0 / 0 / 30** (3559 checked), builds green.

**3.2e (chunk 4, rows #435–#579, the ℙ¹ residue computation and the atom-1 headline)
is dispatched** with `AUDIT-mathlib-p3-2e.md`. Its `residueTheoremK_ratFunc_of_isAlgClosed_*`
rows are the shared K-base engine (row 6 stays residual).

### 3.6 Closeout — 3.2e chunk 4 ACCEPTED; master ℙ¹ file COMPLETE (2026-09-30)

`P1ResidueCore.lean` 3,971 → **6,470 ln** (rows #435–#579, pin 9500–13173). Manager
re-verified: checker **3529 → 3642 identical / 0 mismatched / 0 missing / 30
own-proof** (3672 checked); build green (26.9 s, 2844 jobs, no cascade); axioms clean
on the headline + 20 representative rows; hygiene clean. The file region has **147**
declarations, not the inventory's 145 (two `scoped instance`s missed and landed).
The `AUDIT-mathlib-p3-2e.md` corrections were applied by the worker (#459 omitted;
the two instances added).

**The master ℙ¹ file is fully ported.** Row 2's remaining work is the three sibling
atom/base files' unique tails (~1k) plus the closeout refactor. **This session stops
here by human instruction**, with [HANDOFF-P3-2.md](HANDOFF-P3-2.md) carrying the
state, the `Defs/` theory-move audit (human directive: `Defs/` is definitions only),
the recorded debts, and the remaining rows 3.3–3.7.

### 3.7 Closeout — 3.2f ACCEPTED (partial); the two row-2 headlines gated (2026-09-30)

The R1 definitions round had already moved the master ℙ¹ file into the `P1/` chain
([PLAN-RECTIFY-DEFS.md](PLAN-RECTIFY-DEFS.md) §5.1). Set 3.2f ported the three
sibling files' unique tails ([WORKORDER-P3-2f-tails.md](WORKORDER-P3-2f-tails.md)):

| module | ln | content | status |
|---|---:|---|---|
| `P1/TwoPlace.lean` | 122 | atom-2 two-place-cancellation tail + headline | complete |
| `P1/DivPow.lean` | 713 | atom-3 `P1Tower` (`substPoly`…`trace_mul_inv_derivative`, `D_ratFuncX_ne_zero`, `kwHgfV352_localResidueCompletion_*`) | partial |

Manager-verified: checker **3645 → 3701 identical / 0 mismatched / 0 missing / 30
own-proof** (3675 → 3731 checked); both modules build green, `.olean` mtimes confirm
only they moved; `#print axioms` clean on all 56 public nodes; hygiene clean.

**Two headlines are gated, not ported** (no `sorry` left behind): atom 3's
`RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero` and the PF base
`residueTheorem_ratFunc_of_perfectField`. Their proofs call
`AlgebraicCurve.residueTraceCompletionCommute_v2` and
`completionTraceSum_of_isSeparable`, which need the **Tate agreement** (row 3.3) and
the **trace-completion commutation** (row 3.4). The work order's "3 new helpers" price
was a measurement gap (`port_advise` sees only same-file closure);
[AUDIT-mathlib-p3-2f.md](AUDIT-mathlib-p3-2f.md) corrects it to 229 substitute / 87
import-adapt / 98 new over the 414 rows. Promotion debt recorded in
[../../logs/riemann-roch-friction.md](../../logs/riemann-roch-friction.md) § Set
P3.2f.

**Update — set 3.2g; row 2 complete (2026-09-30).** The gating rows — 3.3 (Tate
agreement) and 3.4 (trace-completion commutation), ported under `Tate/` — unblocked
the two headlines, which then landed as `P1/DivPowEnding.lean` (atom 3, 254 ln) and
`P1/PerfectBase.lean` (PF base, 528 ln). Manager-verified: checker **4049 identical /
0 mismatched / 0 missing / 30 own-proof** (4079 checked); whole-tree build green
(4,900 jobs); both headlines `#print axioms` clean; hygiene clean. **Row 2 (3.2) is
therefore mathematically complete.** Rows 3.5 (PF ending), 3.6 (K ending) and 3.7 (RR
assembly) remain.
