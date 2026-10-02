# Topic — the X₁ Hecke/diamond inputs: `ModularCurve.heckeDiamondInputsAll`

**Status: COMPLETE (2026-10-02).** The port of `ModularCurve.heckeDiamondInputsAll`
landed in three sets plus the manager's capstone; the cone recipe now prints
`remaining 0 nodes / 0 raw / 0 content`, the checker is
`4436 identical (150 promoted), 0 mismatched, 0 missing, 30 own`, the consumer
(`spec/ModularCurveHeckeConsumer.lean`, Zones X1-A/B/C/CAP) is 0 errors /
0 warnings, `#print axioms ModularCurve.heckeDiamondInputsAll` is
`[propext, Classical.choice, Quot.sound]`, and the whole-tree build is green
(4,961 jobs); every X₁ module is warning-free. Plan for the port
of `ModularCurve.heckeDiamondInputsAll`, measured against the FLT pin
`aa2d8b3` and the port's mathlib `v4.34.0`. It follows
[porting-playbook.md](../../porting-playbook.md) (§2 planning, §3.4 sets, §3.5
build discipline, §4 faithfulness). This is the X₁ sibling of the level-H Hecke
layer that already landed as `ModularCurve.heckeOperatorsCommuteBar`
([mc-retrospective.md](../mc-retrospective.md)); it is **not** that layer and does
not reuse its `HeckeInputsAlong`.

**Why here and not `topics/eichlerShimura/`.** Every pin file is
`*_ModularCurve_X1*`, every headline is `ModularCurve.*`, and the work is the
Hecke/diamond face of `J₁(M)`: the `X1HeckeOperator`/`X1Diamond` vocabulary, the
`q ↦ q^ℓ` ratio lemma, the diamond automorphism, and the input bundle itself. The
Hecke-layer orders already live in this directory. Two of the nodes
(`JOneES.exists_transcendental_finiteDimensional_*`) are analytic
function-field facts that the Eichler–Shimura period work could also claim; §2.4
records that, and the module is placed so that either effort can import it.

## 0. Target and verdict

**Target.** One theorem, the pinned statement verbatim:

```lean
theorem ModularCurve.heckeDiamondInputsAll (M : ℕ) [NeZero M] :
    ModularCurve.HeckeDiamondInputsAll M
```

whose predicate (pin `Definitions/Def_ModularCurve_X1HeckeModule.lean:58-65`,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1HeckeModule.lean#L58-L65>)
is the conjunction of

- for every prime `ℓ`, `HeckeInputsOneAlong (AlgebraicClosure ℚ) M ℓ` — the X₁
  degeneracy/Hecke inputs (`HeckeBetaOneDefined`, `HeckeAlphaOneBarIntegral`,
  `HeckeBetaOneBarIntegral`, `HasPrincipalDivisors` at the target field,
  `FiniteAlong (heckeAlphaOneBar …)`, `FundamentalIdentityAlong (heckeBetaOneBar
  …)`, `NormFormulaAlong (heckeAlphaOneBar …)`);
- for every `d` coprime to `M`, a `ℚ`-algebra automorphism `σ` of
  `x1FunctionField M` with `IsDiamondAut M d σ`, and a base change `σ'` of
  `diamondAut M d` to `x1FunctionFieldBar M`.

**Verdict.** Port, in three sets. The name-based remaining figure is
**10 nodes / 4,339 raw / 3,239 content lines**, but three of the ten are
already-paid-for mathematics (one private proof promoted, one assembly over two
ported SET-10 headlines, one promotion), so the honest written estimate is
**≈2,100–2,700 content lines**, of which **≈280 are the X₁ definition modules**.
The only genuinely new mathematics is analytic: two function-field
transcendence nodes and the diamond automorphism of the ratio field. It is
**not** on the port's frontier today (`heckeDiamondInputsAll` has no ported
consumer), so the effort is a deliberate branch taken to keep the λ-adic
Galois-representation targets faithful rather than an unblocking step.

## 1. The measured cone

Everything below reproduces from `tools/deps` at the pin. The target's transitive
citation closure is **67 nodes / 32,941 raw / 25,746 content**; 57 of the 67 are
already ported (the whole `AlgebraicCurve` correspondence/place/principal-divisor
cone plus the `ModularCurve` Laurent/Jq/analytic vocabulary). The remaining set,
by the name-based "not ported" test, is:

| node | raw | content | pin `S_` |
|---|---:|---:|---|
| `AlgebraicCurve.Divisor.pushforwardNormFormula` | 1,251 | 903 | `S_AlgebraicCurve_Divisor_pushforwardNormFormula.lean` |
| `ModularCurve.JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC` | 1,050 | 846 | `S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean` |
| `ModularCurve.exists_isDiamondAut` | 675 | 525 | `S_ModularCurve_exists_isDiamondAut.lean` |
| `ModularCurve.exists_algEquiv_laurentBaseChange_cover` | 423 | 281 | `S_ModularCurve_exists_algEquiv_laurentBaseChange_cover.lean` |
| `ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange` | 316 | 261 | `S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean` |
| `ModularCurve.heckeDiamondInputsAll` | 290 | 197 | `S_ModularCurve_heckeDiamondInputsAll.lean` |
| `ModularCurve.qExpand_image_intFormRatiosC_subset` | 198 | 145 | `S_ModularCurve_qExpand_image_intFormRatiosC_subset.lean` |
| `ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0` | 92 | 65 | `S_ModularCurve_exists_isIntegralQExp_smul_slash_of_mem_Gamma0.lean` |
| `AlgebraicCurve.fundamentalIdentityAlong` | 23 | 9 | `S_AlgebraicCurve_fundamentalIdentityAlong.lean` |
| `AlgebraicCurve.normFormulaAlong` | 21 | 7 | `S_AlgebraicCurve_normFormulaAlong.lean` |
| **total** | **4,339** | **3,239** | |

**Re-measured after SET-X1-A + SET-X1-B (2026-10-02): 4 nodes / 1,388 raw /
1,016 content** — `exists_isDiamondAut` (525), `exists_algEquiv_laurentBaseChange_cover`
(281), `qExpand_image_intFormRatiosC_subset` (145), `exists_isIntegralQExp_smul_slash_of_mem_Gamma0`
(65). Two caveats: the recipe now reads `ModularCurve.heckeDiamondInputsAll` as
"ported" because SET-X1-A landed the *definition*, while the S_ assembly (the
*theorem*) is SET-X1-C's — the documented name-based bias; and the 65-content
row is ≈12 written lines (SET-10 headlines + the promoted `diamondSlash`).

**Final (2026-10-02, after the capstone): `remaining 0 nodes / 0 raw / 0 content`.**
The cone is closed.

**Bias of the metric.** The "already ported" test is name-based over the port
tree plus the checker's `SOURCES`: it is an *upper bound* on what is left and
misses renamed/already-private copies. Three of the ten rows are exactly that
case (§2). It also does **not** see the definitional prerequisites the citation
graph omits (playbook §2.1): the target's own `Definitions/` imports.

**Definition modules, measured separately** (content = raw minus
`import`/`attribute`/`namespace`/`section`/`variable`/`open`/`p2m_*`/comments/blanks):

| pin module | raw | content | referenced by this cone |
|---|---:|---:|---|
| `Definitions/Def_ModularCurve_X1.lean` | 218 | 129 | the `LevelOne`/`Jacobian` block; `intSeriesC`/`intFormRatiosC`/`qExpFunctionFieldC` already ported |
| `Definitions/Def_ModularCurve_X1HeckeOperator.lean` | 246 | 151 | all 27 declarations (the `HeckeInputsOneAlong` layer) |
| `Definitions/Def_ModularCurve_X1Diamond.lean` | 109 | 60 | the `IsDiamondAut`/`diamondAut`/`baseChangeAut` block |
| `Definitions/Def_ModularCurve_X1HeckeModule.lean` | 264 | 158 | only `HeckeDiamondInputsAll` (lines 58–65); the other 41 declarations are for the successor targets — **deferred**, §2.4 |

So the X₁ definitions are **≈280 content lines net** after the already-ported
`X1.lean` function-field block (≈45) and the `X1HeckeOperator` supply prelude
(≈25) are deducted, and the `X1HeckeModule` operator/module/reptheory block is a
counted optional tail for the *next* topic, not this one.

**Gain test (playbook §2.3).** The target is not yet on the frontier, but its
neighbours are load-bearing: `frontier.py` puts
`ModularCurve.heckeDiamondCommuteBar` at `needed 23 / 8,081`, and
`qExpand_image_intFormRatiosC_subset` and
`exists_isIntegralQExp_smul_slash_of_mem_Gamma0` are needed by *both* it and this
target — porting them here pays twice. `heckeDiamondInputsAll` itself is one of
the 34 pin consumers' prerequisites, including
`ModularCurve.rationalRankTwoNebentypus_family`,
`ModularCurve.frobeniusQuadratic_tateModule_jOne` and the
`CuspForm.IsEigenformWith.exists_galoisRepAdic_*` family.

### 1.1 Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import re, sys
from pathlib import Path
sys.path.insert(0, '.')
from fltdata import FltData
d = FltData(); FLT = Path.home()/'proj'/'fermats-last-theorem'
LEAN = Path('../../lean')
def closure(i):
    seen, stack = set(), [i]
    while stack:
        j = stack.pop()
        if j in seen: continue
        seen.add(j); stack.extend(d.cites(j))
    return seen
cl = closure(d.index['ModularCurve.heckeDiamondInputsAll'])
sc = re.compile(r'^\s*(import |attribute |namespace |end\b|open |p2m_open|p2m_export|p2m_alias|p2m_reactivate|section\b|variable\b|#|/-|--|\s*$)')
raw = lambda i: sum(1 for _ in open(FLT/f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8'))
cont = lambda i: sum(1 for l in open(FLT/f"P2M/Sol/S_{d.stem_of[i]}.lean", encoding='utf-8') if not sc.match(l))
port = "\n".join(p.read_text(encoding='utf-8') for p in (LEAN/'FLTForHuman').rglob('*.lean'))
src = re.search(r'SOURCES = \[(.*?)\n\]', (LEAN/'spec/check_flt_statements.py').read_text(), re.S).group(1)
srcs = set(re.findall(r'"([^"]+)"', src))
def ported(q):
    if any(s.endswith('Thm_'+q.replace('.','_')+'.lean') for s in srcs): return True
    return re.search(r'(?<![\w.])'+re.escape(q.rsplit('.',1)[-1])+r'(?![\w])', port) is not None
new = sorted([n for n in cl if not ported(d.qual(n))], key=lambda n:-cont(n))
print(f"closure {len(cl)} nodes, {sum(raw(n) for n in cl)} raw, {sum(cont(n) for n in cl)} content")
print(f"remaining {len(new)} nodes, {sum(raw(n) for n in new)} raw, {sum(cont(n) for n in new)} content")
for n in new: print(f"  {raw(n):5d} raw {cont(n):5d} c  {d.qual(n)}")
def dcont(m):
    p = FLT/'Definitions'/(m+'.lean'); return sum(1 for l in open(p,encoding='utf-8') if not sc.match(l))
for m in ["Def_ModularCurve_X1","Def_ModularCurve_X1HeckeOperator","Def_ModularCurve_X1Diamond","Def_ModularCurve_X1HeckeModule"]:
    print(f"  def {m:40s} {dcont(m):5d} content")
PY
# at planning: closure 67 / remaining 10 4339 3239 ; after SET-X1-A+B: remaining 4 1388 1016
# def module contents 129/151/60/158
```

and the frontier reading:

```bash
cd tools/deps && python3 frontier.py --target ModularCurve.heckeDiamondInputsAll
# needed 10 nodes / 4339 lines; hops_to_frontier 1; 3 nodes unreachable to F
cd tools/deps && python3 port_advise.py -t ModularCurve.heckeDiamondInputsAll
# 22 target declarations; substitute: none; port-once within the target: none
```

## 2. Route audit: what the port already has

Tested for definitional reuse, not merely mathematical agreement. The rows marked
**reuse** mean the port pays nothing new for the node.

| pin item | port home (exact name) | disposition |
|---|---|---|
| `ModularCurve.separableAlong_of_charZero` (the S_ file's local copy) | `AlgebraicCurve.separableAlong_of_charZero`, `AlgebraicCurve/WeilExchange/Transport.lean:268` | **reuse** — the pin duplicates it into `X1HDIGeneric` |
| `X1HDIGeneric.isAlgebraic_adjoin_of_transcendental` | `AlgebraicCurve.isAlgebraic_adjoin_of_transcendental`, `AlgebraicCurve/Place/DegreeOne.lean:54` | **reuse** (same statement, instance-form hypotheses) |
| `X1HDIGeneric.finiteDimensional_adjoin_of_transcendental` | `AlgebraicCurve.SeparatingTranscendentalOfPerfectField.finiteDimensional_adjoin_of_transcendental`, `AlgebraicCurve/IsCurveOver/PerfectField.lean:71` (`private`) | **promote**; the port's proof is the same `adjoin`/`finrank` argument as the pin's |
| `X1HDIGeneric.isAlgebraic_algebraAdjoin` | — | new, 3 lines (`Algebra.IsAlgebraic.trans`) |
| `AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg` | the statement is at `AlgebraicCurve/ResidueTheorem/KFamily.lean:49`, but `KFamily` transitively imports `Transport`, so the importable copy is its acyclic sibling `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver` (`AlgebraicCurve/WeilExchange/FiberOverCount.lean:33`), bridged `fiber = fiberOver` privately | **reuse** (statement unchanged; the sibling is the route) |
| `AlgebraicCurve.SumRamificationInertia` / `instFundamentalIdentityOfSumRamificationInertia` | `AlgebraicCurve/Defs/PushPull.lean:677,682` | **reuse** |
| `ModularCurve.exists_ratCast_qExpansion_slash_of_mem_Gamma0` | `ModularForms/WeightOne/Gamma0Integral.lean:1905` | **reuse** (SET-10) |
| `ModularCurve.exists_isIntegralQExp_smul_of_ratCast_qExpansion` | `ModularForms/WeightOne/Gamma0Integral.lean:2339` | **reuse** (SET-10) |
| `X1DiamondIntegral.diamondSlash`, `conj_mem_Gamma1`, `coe_diamondSlash` | `private` copies in `ModularForms/WeightOne/Gamma0Integral.lean:1415,1425,1449`; public `ModularForm.Level.conj_mem_Gamma1` in `ModularForms/Level/Diamond.lean:166` | **reuse `conj_mem_Gamma1`; promote one `diamondSlash`** |
| `ModularCurve.IsIntegralQExp` block | `ModularForms/WeightOne/Gamma0Integral.lean:98` | **reuse** |
| `ModularCurve.intSeriesC`/`intFormRatiosC`/`qExpFunctionFieldC`/`mem_intFormRatiosC`/`div_mem_qExpFunctionFieldC`/`intFormRatiosC_subset` | `ModularCurve/JqIntegralRatios.lean:53-96` | **reuse**; only `one_mem_intFormRatiosC`, `intFormRatiosC_mono`, `qExpFunctionFieldC_mono` are new |
| `ModularCurve.coeffEmb_injective`/`laurentBaseChange`/`laurentBaseChange_mono`/`qExpand_mem_laurentBaseChange` | `ModularCurve/Defs/Laurent.lean:326,252,413,422` | **reuse** (the pin's `X1HeckeOperator` private prelude dedups here) |
| `S4A.linearIndependent_coeffEmb` | `ModularCurve.linearIndependent_coeffEmb`, `ModularCurve/Defs/GeometricBaseChange.lean:37` | **reuse** |
| `IsFractionRing (Algebra.adjoin F S) (adjoin F S)` | mathlib `Mathlib/FieldTheory/IntermediateField/Adjoin/Algebra.lean:58` (scoped) | **reuse** — the S3d extension's missing glue |
| `ModularCurve.T_mem_Gamma1` (S_ local) | `X1DiamondRational.T_mem_Gamma1`, `ModularForms/WeightOne/Defs/GammaRational.lean:262` | **reuse** (binder `N` vs `M`) |

**The three large "remaining" rows that are nearly free:**

- **`AlgebraicCurve.Divisor.pushforwardNormFormula` (903 content) becomes ≈0.**
  The port already proves it as
  `private AlgebraicCurve.Divisor.pushforwardNormFormula_of_finiteDimensional`
  (`AlgebraicCurve/PrincipalDivisors/Transcendence.lean:345`), under exactly the
  pin's section variables. The promotion is: drop `private`, drop the
  `_of_finiteDimensional` suffix, and add the pinned `[HasPrincipalDivisors K F']`
  binder (unused by the port's proof, present in the wrapper). The 1,251-line
  figure is the upper bound the playbook warns about; the marginal cost is a
  rename.
- **`ModularCurve.exists_isIntegralQExp_smul_slash_of_mem_Gamma0` (65 → ≈12).**
  The pin's `S_` file is the assembly
  `exists_ratCast_qExpansion_slash_of_mem_Gamma0` ∘
  `exists_isIntegralQExp_smul_of_ratCast_qExpansion` plus `diamondSlash` — and
  both headlines, plus a private `diamondSlash`, already live in
  `Gamma0Integral.lean`. The residue is `rat_of_isIntegralQExp` and the wiring.
- **The `X1HDIGeneric` prelude of `heckeDiamondInputsAll` (197 → ≈110).** Three
  of its six generic lemmas are ported (§2 above); `finiteAlong_of_transcendental`
  and `isIntegral_of_finiteAlong` are the only new generic facts and they are
  short.

**Recorded negatives** (searched, found nothing — do not repeat):

- The port's `ModularCurve.geomAut`/`baseChangeEquiv`
  (`Defs/GeometricBaseChange.lean`) **cannot** replace
  `exists_algEquiv_laurentBaseChange_cover`: they are stated under
  `[Algebra.IsAlgebraic ℚ L]` (they need `isField_tensorProduct`), while the pin's
  statement is for an arbitrary `[Field L] [Algebra ℚ L]`. Its consumers here use
  `L = AlgebraicClosure ℚ`, but the checker diffs the general statement, so the
  general proof must exist. See §5 SET-X1-C for the two route options.
- No ported declaration states `exists_transcendental_finiteDimensional_*` for any
  Laurent-series function field (`grep -c` over `FLTForHuman/`: 0), so the
  `JOneES` block is not shadowed by the `AlgebraicCurve` transcendence cone
  (`hasPrincipalDivisors_of_transcendental` is a different statement).
- `diamondAut`/`IsDiamondAut`/`slashQExpC`/`ratioField`/`IsRatio`/`stretch`/
  `expandPS` do not occur in the port (0 files each): the diamond face is new.
  The ported `ModularForm.Level.IsDiamondLift` (`Level/Diamond.lean:143`) is the
  group-side diamond lift with the **lower-right** character `γ 1 1 ≡ d`, while
  `IsDiamondAut` is stated with the **upper-left** `γ 0 0 ≡ d`; they are inverse
  conventions, not the same predicate.
- **The pin's `Integral` block is unported** (`Def_ModularCurve_X1.lean:40-61`:
  `IsIntegralQExp.coeff`, `isIntegralQExp_iff`, `IsIntegralQExp.unique`,
  `isIntegralQExp_one`, `isIntegralQExp_zero`); only the `IsIntegralQExp` `def`
  lives at `ModularForms/WeightOne/Gamma0Integral.lean:98`. SET-X1-A's
  `one_mem_intFormRatiosC` inlines `isIntegralQExp_one`. Sets B/C must port the
  ones their proofs need (into the `IsIntegralQExp` home or `X1/Defs.lean`) —
  `qExpand_image_intFormRatiosC_subset` and the `P4`/`P6` `IsIntegralQExp`
  witnesses are the likely consumers.
- **`ResidueTheorem/KFamily.lean` cannot be imported from
  `WeilExchange/Transport.lean`** — `KFamily → … → WeilExchange/Bifibre →
  Transport` is a cycle (verified mechanically). The `Along` lemmas use the
  acyclic `FiberOverCount` sibling instead.
- The port's `heckeAlphaBar`/`HeckeInputsAlong` (level H,
  `modularFunctionFieldFull`) are **not** the pin's `heckeAlphaOneBar`/
  `HeckeInputsOneAlong` (X₁, `x1FunctionField`). Do not try to substitute one for
  the other; the statements differ.

## 3. Deduplication before coding

`port_advise.py` finds no name proved twice inside the 22 target declarations, so
the target set has no internal prelude to hoist. The copies are external:

1. **The `X1HeckeOperator` private supply block** — `coeffMap_qExpand₁`,
   `coeffEmb_qExpand₁`, `laurentBaseChange_mono₁`,
   `qExpand_mem_laurentBaseChange₁` (pin lines 18–55) — is byte-for-byte the
   level-H `Def_ModularCurve_HeckeOperator.lean` prelude, already public at
   `ModularCurve/Defs/Laurent.lean` (`coeffMap_qExpand`, `coeffEmb_qExpand`,
   `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`). **Write the X₁
   module against the `Laurent.lean` names; do not restate the four helpers.**
   Saving ≈25 content lines.
2. **`diamondSlash`/`coe_diamondSlash`/`conj_mem_Gamma1`** are `private` copies in
   `Gamma0Integral.lean` and are needed again by `exists_isIntegralQExp_smul_slash_of_mem_Gamma0`
   (and `diamondSlash` again inside `exists_isDiamondAut`). `conj_mem_Gamma1` already
   has a public home at `ModularForm.Level.conj_mem_Gamma1`
   (`ModularForms/Level/Diamond.lean:166`) — import it, do not restate it.
   `diamondSlash` (the `ModularForm`-carrier slash) is the same construction as the
   public `ModularForm.Level.slashOfMemGamma0` (`Level/Diamond.lean:209`, on
   `CuspForm`); either generalise `slashOfMemGamma0` to `ModularForm` in its home
   or promote one `diamondSlash` copy — do not write a third. Per playbook §2.4
   this is an out-of-cone duplicate, so expose one copy rather than rewrite.
3. **`separableAlong_of_charZero`, `isAlgebraic_adjoin_of_transcendental`,
   `finiteDimensional_adjoin_of_transcendental`, `T_mem_Gamma1`** — dedup to the
   ported homes in §2.
4. **`X1HeckeModule`'s operator/module/reptheory block** (41 of its 42
   declarations: `heckeOperatorOneBar`, `HeckeDiamondCommuteBar`,
   `heckeModuleOneBar`, `tateHeckeRepOne`, `rationalHeckeRepOne`,
   `RationalRankTwoNebentypusOf`, …) is **deliberately not this topic**. It is
   the successor targets' surface; port it when `heckeDiamondCommuteBar` or
   `rationalRankTwoNebentypus_family` is taken, and add a `CARRY-FORWARD.md`
   entry then (playbook §2.1, file-granular shadowing).
5. **`X1.lean`'s `restrictForm`** is `private` in `ModularCurve/JqIntegralRatios.lean:40`
   and public in the pin, and `intFormRatiosC_mono` needs it — **promote it to
   public** in place (it then verifies against the already-listed
   `Definitions/Def_ModularCurve_X1.lean`) rather than writing a second private
   copy in `X1/Defs.lean`. Its `@[simp] coe_restrictForm` and
   `restrictForm_apply` come with it.
6. **The `Pic0` action/torsion block** (`Pic0.torsion`, the `SemilinearAut`
   `SMul`/`DistribMulAction`/`torsionRep` actions, `ModularCurve.PicAction`) is a
   separate definitions-first mini-set, not this effort; it is the prerequisite of
   the five declarations SET-X1-A omits and is carried in
   [CARRY-FORWARD.md](../../CARRY-FORWARD.md).

## 4. Module layout

One new theory directory, `FLTForHuman/ModularCurve/X1/`, plus two tiny edits to
`AlgebraicCurve`. The X₁ function field is a *second* object beside the X₀
vocabulary in `ModularCurve/Defs/`, which is what triggers the directory
(playbook §3.2). Namespaces stay `ModularCurve` (the pin's), so the checker's
last-name match is unchanged.

| module | pin source | role |
|---|---|---|
| `ModularCurve/X1/Defs.lean` | `Def_ModularCurve_X1.lean` (remainder) | `x1FunctionFieldC`, `x1FunctionField`, `x1x0FunctionFieldC`, the mono/`Gamma1_le_of_dvd` lemmas, `x1FunctionFieldBar`, the `JOne`/`JOneC` abbrevs; **not** the `JOne.torsionGaloisRep` block (deferred, §5 SET-X1-A) |
| `ModularCurve/X1/HeckeOperator.lean` | `Def_ModularCurve_X1HeckeOperator.lean` | the `heckeAlphaOneBar`/`heckeBetaOneBar` degeneracy maps and `HeckeInputsOneAlong` |
| `ModularCurve/X1/Diamond.lean` | `Def_ModularCurve_X1Diamond.lean` | `IsBaseChangeAutOf`/`baseChangeAut`, `slashQExpC`, `IsDiamondAut`/`diamondAut`, `diamondAutBar`; **not** `diamondOneBar` (deferred, §5 SET-X1-A) |
| `ModularCurve/X1/HeckeModule.lean` | `Def_ModularCurve_X1HeckeModule.lean:58-65` | `HeckeDiamondInputsAll` only |
| `ModularCurve/X1/Integral.lean` | `Def_ModularCurve_X1.lean:37-63` (`Integral` block) | `IsIntegralQExp.coeff`/`isIntegralQExp_iff`/`IsIntegralQExp.unique`/`isIntegralQExp_one`/`isIntegralQExp_zero` (the `IsIntegralQExp` `def` itself stays in `WeightOne/Gamma0Integral.lean`) |
| `ModularCurve/X1/FunctionField.lean` | `S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC.lean` | the `qExpFunctionFieldC` transcendence (helpers `private`, in the pin's `JOneES*` inner namespaces) |
| `ModularCurve/X1/FunctionFieldBaseChange.lean` | `S_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange.lean` | the Laurent base-change transfer of the node above |
| `ModularCurve/X1/QExpandStretch.lean` | `S_ModularCurve_qExpand_image_intFormRatiosC_subset.lean` | `qExpand K ℓ '' intFormRatiosC K Γ ⊆ intFormRatiosC K Γ'` |
| `ModularCurve/X1/DiamondAut.lean` | the two diamond `S_` files | the integral-slash assembly and `exists_isDiamondAut` |
| `ModularCurve/X1/BaseChangeCover.lean` | `S_ModularCurve_exists_algEquiv_laurentBaseChange_cover.lean` | automorphism lifting to the compositum |
| `ModularCurve/X1/Inputs.lean` | `S_ModularCurve_heckeDiamondInputsAll.lean` | the input bundle and the headline (manager capstone) |
| `AlgebraicCurve/PrincipalDivisors/Transcendence.lean` | `S_AlgebraicCurve_Divisor_pushforwardNormFormula.lean` | **edit**: promote the private norm formula |
| `AlgebraicCurve/WeilExchange/Transport.lean` | the two `Along` `S_` files | **edit**: add `fundamentalIdentityAlong`, `normFormulaAlong` |

The mathematics is visible as three statements plus concretisation: the
function-field transcendence, the diamond automorphism, and the bundle; the
`Along` lemmas are the generic AC adapter they share.

## 5. Sets and work orders

Three sets, one subagent each, reviewed between sets (playbook §3.4). Their
orders follow the template of §3.3: scope, source, deliverable, route, dedup,
build discipline, verification.

**Execution order is definitions first, then theorems** (playbook §3.7):
SET-X1-A introduces every declaration the later sets state anything about, and it
touches only new files (plus two tiny `AlgebraicCurve` edits), so it cannot
cascade; SET-X1-B is analytic and imports SET-X1-A only; SET-X1-C is the
Hecke/diamond face and imports both. Each set is dispatched only after the
previous set's tree is reviewed (build, checker, consumer, code), and the next
set's order is written against the modules that actually exist.

**Build discipline (shared by all three sets; copy into each order).**
`lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit
loop and **must** carry the options (without them it runs at the default cap and
lies about heavy modules); `timeout 90 lake build <module>` when a file is done;
**one** `timeout 300 lake build` per set at its boundary; never a bare whole-tree
build inside a set; serialize every `lake build` with `flock`; bound every command
with `timeout`; never raise `maxHeartbeats` (the project's global cap is already
4,000,000, so the wall bound is the protection); time builds with wall **and**
user/sys (high user CPU with a timeout is a real blow-up, ~0 CPU is contention).
On a bound-hitting build, diagnose in order: log for `unknown identifier`/parse
errors and missing `open`s; then poll the `lean` process; only then bisect.

**Dedup discipline (shared).** Before writing any helper, `grep` the port for its
pin name and its near-names; the §2 table and §3 list are the measured copies.
The rules that bind here: a pin `private` block re-exported by name mangling is a
**promotion** (write once, publicly, at the pinned names); an out-of-cone
byte-identical duplicate is resolved by **exposing one copy**, not rewriting;
count before dropping (`grep -c`); and a helper whose only consumer is another set
stays `private` in the consumer set's module rather than being promoted early.

### SET-X1-A — the X₁ definitions and the AC along-lemmas (dispatchable now)

**Scope.** Land the X₁ vocabulary and the two generic `Along` lemmas. No headline
proofs; only definitional/coercion facts. Explicitly *not* this set: the
`X1HeckeModule` operator block (§3 item 4), and every statement node of §1.

**Source.** Pin `aa2d8b3`: `Definitions/Def_ModularCurve_X1.lean` lines 95–218;
`Definitions/Def_ModularCurve_X1Diamond.lean`; `Definitions/Def_ModularCurve_X1HeckeOperator.lean`
lines 66–228; `Definitions/Def_ModularCurve_X1HeckeModule.lean` lines 58–65;
`P2M/Sol/S_AlgebraicCurve_{Divisor_pushforwardNormFormula,fundamentalIdentityAlong,normFormulaAlong}.lean`
plus their `Theorems/` wrappers for the statements.

**Deliverable.** The four modules above and the two `AlgebraicCurve` edits. Public
surface: every pin declaration of those files, except the promoted-from-private
helpers which follow the pin's privacy, and the **deferred torsion-rep block**
below. Build order is the import order in §4.

**Boundary found at dispatch, and the trim (2026-10-02).** Faithfully
transcribing the whole pin definition files over-scoped the set: the declarations
`JOne.torsionGaloisRep`, `JOne.torsionGaloisRep_apply`,
`JOne.coe_torsionGaloisRep_apply` (pin `Def_ModularCurve_X1.lean:189-207`) and
`diamondOneBar`, `diamondOneBar_apply` (pin `Def_ModularCurve_X1Diamond.lean:98-103`)
depend on a deliberately unported prerequisite:

- `Pic0.torsion`/`mem_torsion`/`instModuleZModTorsion` and the `SMul`/
  `DistribMulAction (SemilinearAut K F)` actions on `Divisor`/`Pic0`, plus
  `SemilinearAut.torsionRep` (pin `Def_AlgebraicCurve_BaseChangeGalois.lean:206-356`,
  ≈150 lines), whose port home is decided (`AlgebraicCurve/Defs/SemilinearAut.lean`,
  `AlgebraicCurve/Defs/Divisor.lean`);
- `ModularCurve.PicAction` (pin `Def_ModularCurve_ArithmeticGalois.lean:85-105`),
  home `ModularCurve/Defs/ArithmeticGalois.lean`.

None of these five declarations is on the `heckeDiamondInputsAll` cone: its
statement needs only `x1FunctionField`, `x1FunctionFieldBar`,
`heckeAlphaOneBar`/`heckeBetaOneBar`, `HeckeInputsOneAlong`, `IsDiamondAut`,
`diamondAut`, `IsBaseChangeAutOf`, and its proof needs the two `JOneES` nodes and
`exists_isDiamondAut`. They belong to the successor targets
(`heckeDiamondCommuteBar`, `rationalRankTwoNebentypus_family`) and are carried in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md) as the **Pic0 action/torsion
mini-set**, to be ported as that successor's first order (definitions first)
before its Hecke-module block. SET-X1-A therefore lands the modules with those
five declarations omitted; the checker iterates `PORT_FILES`, so their absence is
not a "missing" and the set still closes `0 mismatched / 0 missing`.
`JOne`/`JOneC` (pure abbrevs) stay.

**Route.** Verbatim transcription, with the §2 reuse table applied first:
`IsIntegralQExp` comes from `ModularForms/WeightOne/Gamma0Integral.lean:98`;
`intSeriesC`, `intFormRatiosC`, `qExpFunctionFieldC` and their lemmas come from
`ModularCurve/JqIntegralRatios.lean`; `coeffEmb`,
`laurentBaseChange`, `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`
from `Defs/Laurent.lean`; `JOne = Pic0 (AlgebraicClosure ℚ) (x1FunctionFieldBar M)`
via `AlgebraicCurve.Pic0` and `SemilinearAut.ofAlgAut`. The AC promotion: rename
the private `Transcendence.lean:345` lemma, then the two wrappers are the pin's
proofs (`fundamentalIdentityAlong` builds the `SumRamificationInertia` instance).

**Dedup (do these before writing a line).**
- Import `coeffMap_qExpand`, `coeffEmb_qExpand`, `laurentBaseChange_mono`,
  `qExpand_mem_laurentBaseChange` from `ModularCurve/Defs/Laurent.lean`; **do not**
  restate the pin's four `X1HeckeOperator` supply lemmas (`…₁` names).
- Import `ModularForm.Level.conj_mem_Gamma1` (`ModularForms/Level/Diamond.lean:166`)
  and `ModularCurve.linearIndependent_coeffEmb`
  (`ModularCurve/Defs/GeometricBaseChange.lean:37`); do not restate either.
- `T_mem_Gamma1` already exists as `X1DiamondRational.T_mem_Gamma1`
  (`ModularForms/WeightOne/Defs/GammaRational.lean:262`, binder `N`); if the pin's
  `(M : ℕ)` form is needed, alias it rather than re-prove it.
- `separableAlong_of_charZero` (S_ local) is the ported
  `AlgebraicCurve.separableAlong_of_charZero`
  (`AlgebraicCurve/WeilExchange/Transport.lean:268`) — do not copy it into
  `X1HDIGeneric`.
- **Promote `restrictForm`/`coe_restrictForm`** in
  `ModularCurve/JqIntegralRatios.lean` (drop `private`) and add the pin's
  `restrictForm_apply`; `intFormRatiosC_mono` consumes it and a second private
  copy is forbidden.
- Keep the pin's `private` helpers `private`. This set's only promotions are
  `Divisor.pushforwardNormFormula` (the AC slice, below) and `restrictForm`;
  `finiteDimensional_adjoin_of_transcendental` is promoted in SET-X1-C when
  `X1HDIGeneric` needs it.

**Checker-binder warnings (the two places the textual diff bites).**
- The promoted `Divisor.pushforwardNormFormula` must be a **public declaration
  whose explicit binders are the `Theorems/` wrapper's** (the wrapper adds
  `[HasPrincipalDivisors K F']`). Keep the existing hypothesis-free private
  `pushforwardNormFormula_of_finiteDimensional` and have the public wrapper call
  it — the internal caller
  `hasPrincipalDivisors_of_finiteDimensional_ratFunc` (`Transcendence.lean:416`)
  cannot supply `[HasPrincipalDivisors K F']`. If the explicit binders collide
  with the file-level `variable {K F F'}`, close that variable scope in a
  `section`/`end` before the wrapper; do not rename the binders.
- `fundamentalIdentityAlong` and `normFormulaAlong` are new public declarations:
  spell the wrapper's binders explicitly (do **not** leave them to a `variable`)
  and add their `Theorems/Thm_AlgebraicCurve_*.lean` wrappers to `SOURCES`,
  appended last.

**Stop-early risks.** (a) `JOne`'s `DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ]
AlgebraicClosure ℚ)` instance (the pin's `example` at `X1.lean:189`) is an
instance diamond candidate — record it in `instance-friction.md` if it needs
explicit provision. (b) `x1FunctionFieldBar` is an `abbrev`; keep it an `abbrev`
(the pin's `rfl` bridges depend on unfolding, cf. `Correspondence.lean`'s
`algebraAlong` note). (c) If `IsDiamondAut`'s `Subfield`-coercion shape fights the
port's `IntermediateField` API, stop and report rather than restating it.

**Build discipline (copy in).** `timeout 60 lake env lean -DmaxHeartbeats=4000000
-DautoImplicit=false <file>` per edit; `timeout 90 lake build <module>` per
module; **one** `timeout 300 lake build` at the set boundary, serialized with
`flock`; never raise `maxHeartbeats`; bound everything with `timeout`.

**Verification.** Checker delta reported as
`<N> identical / 0 mismatched / 0 missing` (baseline today is
`4368 identical / 150 promoted / 0 mismatched / 0 missing / 30 own`), with the
new `SOURCES` entries appended last and the new modules appended to
`PORT_FILES`; `#print axioms` on the three AC headlines; consumer zone X1-DEF
(concrete `x1FunctionFieldBar 2` inhabited, `JOne 2` an `AddCommGroup`, the
`heckeAlphaOneBar`/`heckeBetaOneBar` definitional bridges at `M = 2`).

**Set record (reviewed 2026-10-02; log [x1-hecke-set-a.md](../../logs/x1-hecke-set-a.md)).**
4 new modules / 523 lines (`X1/Defs` 144, `X1/HeckeOperator` 209, `X1/Diamond`
127, `X1/HeckeModule` 43); checker `4368 → 4424 identical (150 promoted), 0
mismatched, 0 missing, 30 own`, delta +56 reconciled by the per-module table in
the log; one-token mutation gave `4423/1/0` then reverted; consumer 0 errors /
0 warnings (the zone's one `haveI`-linter warning fixed at review); axioms on the
three AC headlines `[propext, Classical.choice, Quot.sound]`; whole-tree build
green (4952 jobs). Review found no defects; two reconciliation decisions are
recorded: `restrictForm` had to be promoted inside the pin's `section Restrict`
(the textual checker reads the pin's `variable` structure), and the promotion
forced the deletion of a third `private restrictForm` copy in
`ModularForms/WeightOne/IntegralWeightOneForm.lean` (it imports
`JqIntegralRatios`; its one use now resolves to the public copy).

### SET-X1-B — the X₁ function-field transcendence (analytic core)

**Scope.** The two `JOneES` nodes (1,050 + 316 raw; ≈1,100 content). Not the
Hecke/diamond face.

**Deliverable.** `ModularCurve/X1/FunctionField.lean` with
`JOneES.exists_transcendental_finiteDimensional_qExpFunctionFieldC`,
`ModularCurve/X1/FunctionFieldBaseChange.lean` with
`JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`, and
`ModularCurve/X1/Integral.lean` with the pin's `Integral` block (needed by the
`P4`/`P6` witnesses; the `IsIntegralQExp` `def` is imported from
`Gamma0Integral.lean`). SET-X1-A's modules are frozen: do not edit
`X1/Defs.lean`, `X1/HeckeOperator.lean`, `X1/Diamond.lean` or
`X1/HeckeModule.lean`; put shared vocabulary in the new `X1/Integral.lean`.

**Route.** Transcribe the pin's five inner blocks (`JOneESAlg` — the
`LaurentSeries` algebraic-element/valuation lemmas; `JOneESLevelOne` —
`monomialSpan` and `qExpansion_mem_monomialSpan`; `JOneESNorm` — the
`Cos`-indexed norm `charPolyAt` and the `Nice` analyticity; `JOneESRat` — `xq`,
its transcendence, the `intFormRatiosC` closure and `exists_rat_relation`;
`JOneESAlgBC`/`JOneESBC` — the base-change transfer). Reuse the ported
`ModularForm.norm`, `cuspFunction`, `qExpansion_E4_eq_map_eisenstein4`,
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`,
`qCoeff_comp_heckeDiagMatrix_smul`, `one_mem_strictPeriods`,
`coeffEmb_mem_laurentBaseChange`, `linearIndependent_coeffEmb`. `port_advise.py`
reports the pin's whole set shares no name with the port, so expect a
transcription, not a reduction.

**Stop-early risks.** The pin's `Nice`/`qExpansion_sum'`/`norm` block is the
api-drift surface (`cuspFunction`, `AnalyticAt`, `ModularForm.norm`); scout it in
`Scratch.lean` before writing the module (playbook §2.6). If the monomial-span
argument needs a `PowerSeries` lemma mathlib no longer has, stop and report the
exact missing statement.

**Reuse reconnaissance for this set (text-only; to confirm at dispatch).** The
port already has `ModularForm.norm`/`coe_norm`, `cuspFunction`, `AnalyticAt`,
`qExpansion_pow`/`qExpansion_sum`, `qExpansion_E4_eq_map_eisenstein4` and
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`. The pin's `JOneESNorm`
block (`Cos Γ`, `quotientFunc`, `charPolyAt`, `coeffForm`, the `Nice` predicate)
is a **generalisation** of the port's private block in
`ModularForms/Gamma1Vanishing.lean:519-560` (`CosetQ`/`normCusp`/`quotientFunc`,
specialised to `Γ₁(M) ≤ Γ₀(M)` and cusp forms); prefer generalising that block
in its home over copying the pin's, but do not force it if the carriers differ
(`ModularForm` vs `CuspForm`). `Cos`, `eval_homogenize_*`, `JOneESRat.P4`/`P6`
look new. `port_advise.py` sees no name shared between the whole `JOneES` set and
the port, so budget the block as transcription plus this one generalisation.

**Set record (reviewed 2026-10-02; log [x1-hecke-set-b.md](../../logs/x1-hecke-set-b.md)).**
3 new modules / 1,551 lines (`X1/Integral` 53, `X1/FunctionField` 1,141,
`X1/FunctionFieldBaseChange` 357); every helper in the two `JOneES` modules is
`private`, so the checker delta is +7 (five `Integral` lemmas + two headlines);
checker `4424 → 4431 identical (150 promoted), 0 mismatched, 0 missing, 30 own`;
one-token mutation `4430/1/0` then reverted; consumer 0 errors / 0 warnings;
whole-tree build green (4957 jobs); axioms on both headlines
`[propext, Classical.choice, Quot.sound]`. The scout gate cleared with no
structural drift: the general-`Γ` `norm`/`Cos` route and the monomial-span
argument elaborate as the pin writes them. Three near-duplicates are recorded for
the final refactor round rather than cut now: the pin's `P4` folded into the
ported `eisenstein4` (only the local `coeff_one_P4` copy is private), the four
`JOneESAlg`/`JOneESAlgBC` A1 `LaurentSeries` lemmas duplicated `private` across
the two modules (the pin duplicates them too), and `Gamma1Basis.lean:810`'s
private `isIntegralQExp_iff` now shadowed by the public copy in `X1/Integral.lean`.

### SET-X1-C — the Hecke/diamond face and the capstone

**Scope.** `qExpand_image_intFormRatiosC_subset`; the integral-slash assembly and
`exists_isDiamondAut`; `exists_algEquiv_laurentBaseChange_cover`; the input
bundle `heckeDiamondInputsAll`. The capstone (`X1/Inputs.lean` and
`ModularCurve.heckeDiamondInputsAll`) and the final wire test are **reserved for
the manager** (playbook §3.4): the dispatched order covers only
`QExpandStretch`, `DiamondAut` and `BaseChangeCover`.

**Deliverable.** The four modules `QExpandStretch`, `DiamondAut`,
`BaseChangeCover`, `Inputs`, and the consumer zone.

**Hand-off from SET-X1-B (frozen inputs, do not re-derive).**
`ModularCurve.isIntegralQExp_iff` and `IsIntegralQExp.coeff/_unique`,
`isIntegralQExp_one/_zero` are public in `X1/Integral.lean`; the pin's
`S_…qExpand_image_intFormRatiosC_subset.lean:135` calls `isIntegralQExp_iff`
directly, so that node needs no `P4`/`P6`. There is **no name `P4`**: the integral
`E₄` series is `ModularCurve.eisenstein4` (`coeff 1 = 240`); `P6` is `private` in
`X1/FunctionField.lean`. The two `JOneES` headlines are importable at their
wrapper binders. The four `JOneESAlg`/`JOneESAlgBC` A1 lemmas stay `private`; if
this set needs one, promote one copy rather than writing a third. `X1/Defs`,
`X1/HeckeOperator`, `X1/Diamond`, `X1/HeckeModule`, `X1/Integral`,
`X1/FunctionField`, `X1/FunctionFieldBaseChange` and the `SET-X1-A` `AlgebraicCurve`
edits are frozen.

**Route.**
- `qExpand_image_intFormRatiosC_subset`: the pin's `stretchSlash`/`stretch`/
  `expandPS` construction over `X1QExpandStretch`, using the public
  `isIntegralQExp_iff`; the `cocycle`/`T_mem_Gamma1` helpers (pin `S_` file) are
  the assembly set's, below.
- `exists_isDiamondAut`: the pin's `X1DiamondPullback` (`qC`, `ratioField`,
  `IsRatio` closure, `pull`, the `Subfield` model, `sigma`/`eC`/`jC`, then
  `toC`/`iota` back to `x1FunctionField M`). Reuse `ModularForm.Level.conj_mem_Gamma1`
  and the promoted `diamondSlash`; the ported `ModularForm.Level.IsDiamondLift` /
  `exists_isDiamondLift_of_coprime` (`Level/Diamond.lean:143,148`) is the same
  diamond vocabulary on the group side, but its character is the *lower-right*
  entry (`γ 1 1 ≡ d`) while `IsDiamondAut` reads the *upper-left* (`γ 0 0 ≡ d`);
  they are inverse conventions, so it is a route input (`exists_gamma0_apply_eq`),
  not a drop-in substitute — check the orientation before reaching for it.
- `exists_algEquiv_laurentBaseChange_cover`: **two options, scout first.** (i)
  the pin's `S3d`/`S4H` route — an abstract `Algebra.adjoin K (range φ)`
  automorphism from a `ℚ`-basis, extended by
  `IsFractionRing.algEquivOfAlgEquiv` under the scoped mathlib instance
  `IsFractionRing (Algebra.adjoin F S) (adjoin F S)`, reusing
  `linearIndependent_coeffEmb`; ≈240 content. (ii) A tensor-product variant of
  `geomAut` on the domain `(baseChangeHom L F₀).range` (no algebraicity), then
  the same fraction-ring extension; expected much shorter, **unproven** — spend a
  `Scratch.lean` probe on it and record the pre/post-scout numbers.
- `Inputs.lean`: transcribe `S_ModularCurve_heckeDiamondInputsAll.lean` with the
  §2/§3 dedups applied; the `diamond_inputs` field composes
  `exists_isDiamondAut` with `exists_algEquiv_laurentBaseChange_cover`, and the
  `heckeInputsOneAlong` field is
  `heckeInputsOneAlong_intro (heckeBetaOneDefined …) (alphaIntegral …)
  (betaIntegral …) (fundamentalIdentityAlong …) (finiteAlong_alpha …)
  (normFormulaAlong …)`.

**Verification.** `#print axioms ModularCurve.heckeDiamondInputsAll` =
`[propext, Classical.choice, Quot.sound]`; the capstone compiles first try
(that is the review instrument); a consumer zone X1 composing
`heckeDiamondInputsAll 1` into a concrete `HeckeInputsOneAlong (AlgebraicClosure ℚ)
1 2` and thence `heckeOperatorOneAlong_eq`, plus the diamond branch at
`(M, d) = (1, 2)` producing a real `AlgEquiv` and `IsBaseChangeAutOf`; no zone
may contain a `#check`, a `sorry`, or a hypothesis not discharged from ported
material.

**Set record (statements reviewed 2026-10-02; log [x1-hecke-set-c.md](../../logs/x1-hecke-set-c.md)).**
3 new modules / 1,143 lines (`QExpandStretch` 218, `DiamondAut` 739,
`BaseChangeCover` 186); checker `4431 → 4435 identical (150 promoted), 0
mismatched, 0 missing, 30 own`, +4 = the four headlines; mutation check
`4434/1/0` then reverted; consumer 0/0 with delete-fail 4; axioms all four
headlines `[propext, Classical.choice, Quot.sound]`; whole-tree build green
(4,960 jobs). **The cover scout paid:** option (ii) won, 423 raw / 281 content in
the pin down to 186 raw / 135 content in the port — `baseChangeHom` codRestrict to
`L ⊗[ℚ] F₀ ≃ₐ[L] Algebra.adjoin L (Set.range φ₀)`, `Algebra.TensorProduct.congr`
transports `σ₀`, and the scoped `IsFractionRing (Algebra.adjoin F S) (adjoin F S)`
extends it; no `[Algebra.IsAlgebraic ℚ L]`, and the pin's `S3d`/`S4H`/`S4A`/`S4C`
shim was not transcribed. One duplicate left for the refactor round: a third
private `diamondSlash`/`coe_diamondSlash` pair (`Gamma0Integral.lean` +
`X1/DiamondAut.lean`). Two proofs needed the port's
`backward.isDefEq.respectTransparency.types false` fix.

**Capstone record (manager, 2026-10-02).** `X1/Inputs.lean` (≈330 lines) with the
pin's `X1HDIGeneric`/`X1HDIInputs` assembly; every helper `private`, so the
checker delta is +1 (the headline). Reuse applied: the pin's
`isAlgebraic_algebraAdjoin`/`isAlgebraic_adjoin_of_transcendental` collapse to the
ported `AlgebraicCurve.isAlgebraic_adjoin_of_transcendental`, and its local
`separableAlong_of_charZero` to `AlgebraicCurve.separableAlong_of_charZero`; only
`finiteDimensional_adjoin_of_transcendental`, `finiteAlong_of_transcendental` and
`isIntegral_of_finiteAlong` are new. Three port idioms were needed to make the pin
proof elaborate: `Set.Finite.to_subtype` (v4.34 name), `T_mem_Gamma1` by bare
`simp`, and `set_option backward.isDefEq.respectTransparency.types false` on
`cocycle` (the `!![…]`–`SL(2, ℤ)` coercion under the membership goal). Checker
`4435 → 4436`, 0/0; consumer Zone X1-CAP consumes both halves of the bundle;
axioms `[propext, Classical.choice, Quot.sound]`; whole-tree build green
(4,961 jobs). The effort record is [x1-hecke-port.md](../../logs/x1-hecke-port.md).

## 6. Budget and risk register

**Correction ledger, content lines.**

| row | content |
|---|---:|
| name-based remaining (10 nodes) | 3,239 |
| − `Divisor.pushforwardNormFormula` (private proof already in the port) | −900 |
| − `exists_isIntegralQExp_smul_slash_of_mem_Gamma0` (SET-10 headlines + private `diamondSlash`) | −53 |
| − `heckeDiamondInputsAll` prelude (3 of 6 generic lemmas ported) | −87 |
| **theorem-side written** | **2,199** |
| + X₁ definitions, written: `X1.lean` 129−45, `X1HeckeOperator` 151−25 (prelude in `Laurent.lean`), `X1Diamond` 60, `HeckeDiamondInputsAll` 8 | +278 |
| **estimate** | **≈2,480** |
| range (written ÷ content 1.0–1.2; AC/MC calibration) | **2,100–2,700** |

**Re-measured after SET-X1-A + SET-X1-B (2026-10-02).** SET-A wrote 523 new
module lines + ~80 edit lines and SET-B wrote 1,551 new lines, against a combined
plan of ≈300 (definitions) + ≈1,150 (the two `JOneES` nodes). The remaining
statement work is SET-C's four nodes (1,016 content, of which 65 is ≈12 written)
plus the manager's capstone: **≈1,000 content, range 900–1,200**, subject to the
cover scout choosing between the ≈281-content pin route and the tensor-product
route.

**Actual (2026-10-02).** SET-C wrote 1,143 lines; the capstone ≈330. The effort
totals ≈3,550 new module lines against the 2,100–2,700 range — the overage is
transcribed `private` helpers plus module docs, which the content metric does not
count; the mathematical budget held, and the cover route came in at 135 content
against the budgeted 281. The cone recipe prints `0 / 0 / 0`; the record is
[x1-hecke-port.md](../../logs/x1-hecke-port.md).

**Named shape risks, in the order they will bite.**

1. **General-`L` automorphism lifting.** `geomAut` is algebraic-only; the general
   statement must be proved. Mitigation: scout route (ii) in `Scratch.lean`, else
   port `S3d`/`S4H`. *Open; the only route decision left.*
2. **Analytic API drift in `JOneESNorm`.** `Nice`, `cuspFunction`, `ModularForm.norm`,
   the `qExpansion` sum lemmas. Mitigation: `Scratch.lean` probe in SET-X1-B before
   the module. *Open.*
3. **`Subfield` vs `IntermediateField` at the ratio field.** `IsDiamondAut` is
   stated on `x1FunctionField M : IntermediateField` while the pin's construction
   lives in `Subfield (LaurentSeries ℂ)`. Mitigation: keep the pin's carrier and
   close with `IntermediateField` coercions; if the coercion is not `rfl`,
   register a helper. *Predicted low — the same shape closed in the MC layer.*
4. **Instance diamonds for `x1FunctionFieldBar`/`JOne`.** The MC port already hit
   these (`instance-friction.md`). Mitigation: explicit local instances, no
   `synthInstance.maxHeartbeats` bumps. *Predicted low.*
5. **Checker wiring after the promotion.** `Divisor.pushforwardNormFormula` enters
   the diffed set with the pin's `[HasPrincipalDivisors K F']` binder; the
   `X1`/`X1HeckeOperator`/`X1HeckeModule` private preludes must stay `private`.
   Mitigation: append `SOURCES`/`PORT_FILES` last, run the one-token mutation
   check (expect `N identical / 1 mismatched`) before trusting the count.
6. **`X1HeckeModule` shadowing.** If the operator block stays unported while
   `HeckeDiamondInputsAll` lands, its citers read as unblocked though the
   `heckeOperatorOneBar`/`HeckeDiamondCommuteBar` API is absent. Mitigation: the
   `CARRY-FORWARD.md` entry of §3 item 4 at port time.

**Predicted non-events** (do not budget them again): the `Pic0`/`Divisor`
correspondence API, `HasPrincipalDivisors`, and the `Along` predicates are all
ported; there is no mathlib gap in the AC slice; and the pin's `X1.lean`
function-field block is already paid for.

## 7. Faithfulness and verification recipe (per set)

1. **Checker.** Append the set's `Theorems/Thm_<stem>.lean` wrapper(s) to
   `SOURCES` last and the new module(s) to `PORT_FILES`; run
   `python3 spec/check_flt_statements.py`. Target `0 mismatched / 0 missing`.
   Verify the checker with a one-token mutation (expect exactly one more
   `mismatched`) and revert. Helpers that are ours go on `OWN_PROOFS` with the
   reason (the X1 modules should need very few: the `X1HDIGeneric` dedups are
   pin-private or pin-public at ported names).
2. **Consumer.** Extend `spec/ModularCurveHeckeConsumer.lean` with the zone
   named in each set order (or add `spec/X1Consumer.lean` if the file grows past
   readability); the error count is the deliverable. Each zone must delete-fail.
3. **Axioms.** `#print axioms` on `ModularCurve.heckeDiamondInputsAll` and every
   X₁ headline; expect `[propext, Classical.choice, Quot.sound]`.
4. **Build ladder.** Per §5 SET-X1-A; no bare whole-tree build inside a set.
5. **Coverage.** Re-run §1.1 and record the remaining figure moving
   `10 / 3,239 → …` per set; reconcile every drop against the ported surface.

## 8. What this topic is not

- Not the level-H Hecke layer (`heckeOperatorsCommuteBar`, m1–m13); that is
  ported and disjoint.
- Not the `X1HeckeModule` Hecke-module/Tate-representation block
  (`heckeOperatorOneBar`, `HeckeDiamondCommuteBar`, `heckeModuleOneBar`,
  `tateHeckeRepOne`, `RationalRankTwoNebentypus*`); that is the successor topic
  and is registered in §3 item 4.
- Not the `Pic0` action/torsion prerequisite (`Pic0.torsion`,
  `SemilinearAut.torsionRep`, `ModularCurve.PicAction`) that the omitted
  `JOne.torsionGaloisRep`/`diamondOneBar` need; that is a separate
  definitions-first mini-set, carried in
  [CARRY-FORWARD.md](../../CARRY-FORWARD.md) and §5 SET-X1-A.
- Not the Eichler–Shimura period map; the two `JOneES` nodes are shared
  infrastructure, not the period isomorphism.
- Not a `Reserve/` narrative route: the statements are the pin's, and the
  checker diffs them.
