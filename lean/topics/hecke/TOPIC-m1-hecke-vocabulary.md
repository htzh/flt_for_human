# Topic m1 — the Hecke correspondence vocabulary (M1)

**Status: work order written, not started.** First topic of
[SET-M1](SET-M1.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** Five modules, all definitions plus their own structural lemmas, with
statements verified by name against the pin's definition files:

- `FLTForHuman/ModularCurve/Defs/HeckeOperator.lean` — the two degeneracy maps
  and the correspondence.
- `FLTForHuman/ModularCurve/Defs/DegeneracyTower.lean` — the degeneracy tower,
  its composite square, and `HeckeExchangeAt`.
- `FLTForHuman/ModularCurve/Defs/HeckeTotal.lean` — the total operator with its
  junk branch (`HeckeOperatorTotal` + `HeckeInputsAll`).
- `FLTForHuman/ModularCurve/Defs/HeckeModule.lean` — the operators and the target
  proposition (and, optionally, the `HeckeAlg` payoff).
- `FLTForHuman/ModularCurve/Defs/ArithmeticGalois.lean` — the `bar` field and
  `JZero` (the `bar` layer of the pin's `ArithmeticGalois`).

**Why this topic.** Every remaining node names one of these declarations:
`heckeAlphaBar`/`heckeBetaBar`, `towerInclBar`/`towerSubstBar`, `HeckeExchangeAt`,
`heckeOperatorBar`, `HeckeOperatorsCommuteBar`, `JZero`, `modularFunctionFieldBar`.
The declarations are the effort's whole interface; a wrong `HeckeExchangeAt`
shape or a non-`rfl` `heckeAlphaBar = towerInclBar` would redo everything. Write
them first, with the pin's definitional equalities preserved.

## 1. The pin sources

| pin module | lines | port home |
|---|---|---|
| `Definitions/Def_ModularCurve_HeckeOperator.lean` | 191 | `Defs/HeckeOperator.lean` |
| `Definitions/Def_ModularCurve_DegeneracyTower.lean` | 138 | `Defs/DegeneracyTower.lean` |
| `Definitions/Def_ModularCurve_HeckeOperatorTotal.lean` | 65 | `Defs/HeckeTotal.lean` |
| `Definitions/Def_ModularCurve_HeckeInputsAll.lean` | 20 | `Defs/HeckeTotal.lean` |
| `Definitions/Def_ModularCurve_HeckeModule.lean` | 122 | `Defs/HeckeModule.lean` |
| `Definitions/Def_ModularCurve_ArithmeticGalois.lean` | 140 | `Defs/ArithmeticGalois.lean` |

Order: `HeckeOperator` → `DegeneracyTower` → `HeckeTotal` → `HeckeModule`;
`ArithmeticGalois` is independent (it needs only `Laurent`/`X0` and the AC
`SemilinearAut`) and should be written first or second so `HeckeModule` can use
`JZero`.

## 2. What to write, declaration by declaration

### 2.1 `Defs/HeckeOperator.lean`

The pin's private prelude (`Def_ModularCurve_HeckeOperator.lean:16–57`) is four
private supply lemmas. Two are already ported public; two are not (the port has
only the specialized analogue `full_degeneracy_map_le`):

| pin private | port status |
|---|---|
| `coeffMap_qExpand'` | **ported**: `Defs/Laurent.lean` `coeffMap_qExpand` |
| `coeffEmb_qExpand'` | **ported**: `Defs/Laurent.lean` `coeffEmb_qExpand` |
| `laurentBaseChange_mono'` | **not ported**; write it **public** here — it is itself the wrapper target `ModularCurve.laurentBaseChange_mono` (an M4 degree/glue node) |
| `qExpand_mem_laurentBaseChange'` | **not ported**; write it **public** here — it is itself the wrapper target `ModularCurve.qExpand_mem_laurentBaseChange` (an M4 node) |

**Do not re-derive the two ported ones.** `grep -n` each name in `FLTForHuman/`
and import the module that has it. The two generic ones are **public**: they are
remaining wrapper targets (`Thm_ModularCurve_laurentBaseChange_mono`,
`Thm_ModularCurve_qExpand_mem_laurentBaseChange`), register their wrappers in
`SOURCES`, and let `DegeneracyTower` import them rather than repeating the pin's
`laurentBaseChange_mono''`. That is one public home for a lemma the pin writes
twice `private`, and it delivers two M4 nodes early.

Public declarations, verbatim:

- `heckeAlphaBar` (the `IntermediateField.inclusion` of
  `full_degeneracy_le (dvd_mul_right N ℓ)`), `@[simp] coe_heckeAlphaBar`,
  `heckeAlphaBar_eq_inclusion`;
- `heckeBetaBarRingHom`, `@[simp] coe_heckeBetaBarRingHom`, `heckeBetaBar`,
  `@[simp] coe_heckeBetaBar` (`qExpand L ℓ` on the underlying series);
- `HeckeAlphaBarIntegral`, `HeckeBetaBarIntegral`;
- `heckeDivBar` (`Divisor.correspondence (heckeBetaBar …) (heckeAlphaBar …) hβ hα`);
- `heckePic0Bar` (`Pic0.correspondence …`);
- `heckeDivBarTranspose`, `heckePic0BarTranspose`.

The pin's `section ModularInstance` holds two `example`s (typechecks only, no
declaration); **drop them** (they are not API).

**Keep the definitional shape:** `heckeAlphaBar L N ℓ` must reduce to
`towerInclBar L (dvd_mul_right N ℓ)` and `heckeBetaBar` to
`towerSubstBar L N ℓ dvd_rfl`, so that the `rfl` bridges in
`Defs/DegeneracyTower.lean` and the pin's `S_` files still work. Do not insert an
extra `AlgHom.ext`.

### 2.2 `Defs/DegeneracyTower.lean`

- **no** `laurentBaseChange_mono''`: §2.1 writes the public
  `ModularCurve.laurentBaseChange_mono`; import it and write nothing here;
- `towerInclBar`, `@[simp] coe_towerInclBar`, `towerInclBar_eq_inclusion`,
  `towerInclBar_comp_towerInclBar`, `towerInclBar_self`;
- `towerSubstBar` (`= (towerInclBar L h).comp (heckeBetaBar L N ℓ)`),
  `@[simp] coe_towerSubstBar` (must be `rfl` to `qExpand L ℓ`),
  `towerSubstBar_congr`;
- the six composites `heckeAlphaBar_eq_towerInclBar` (`rfl`),
  `heckeBetaBar_eq_towerSubstBar` (`Subtype.ext` + `coe_*`),
  `towerInclBar_comp_heckeAlphaBar`, `towerInclBar_comp_heckeBetaBar` (`rfl`),
  `towerSubstBar_comp_heckeAlphaBar`, `towerSubstBar_comp_heckeBetaBar` (uses
  `qExpand_qExpand`);
- `heckeSquareBar_commutes`;
- `dvd_of_eq_roof`;
- `HeckeExchangeAt` — the predicate. Copy the binder block exactly; it mentions
  `HasPrincipalDivisors`, `(heckeBetaBar …).toRingHom.IsIntegral`,
  `Divisor.pullbackAlong`/`pushforwardAlong`. This shape is the contract the
  whole effort targets; a binder change here is maximally expensive.

### 2.3 `Defs/HeckeTotal.lean`

`HeckeInputsAlong`, `heckeOperatorAlong` (the `if h : HeckeInputsAlong … then … else 0`
with `open Classical`), `heckeInputsAlong_intro`, `heckeOperatorAlong_eq`,
`heckeOperatorAlong_of_not`, and `HeckeInputsAll`. These are the pin's
`HeckeOperatorTotal` + `HeckeInputsAll`.

### 2.4 `Defs/HeckeModule.lean`

In-cone (required): `heckeOperatorBar`, `heckeOperatorBar_apply`,
`HeckeOperatorsCommuteBar`, `isMulCommutative_adjoin_heckeOperatorBar`.

Out-of-cone payoff (optional tail): `heckeEvalBarAux`, `heckeEvalBar`,
`heckeEvalBar_apply`, `heckeEvalBarAux_heckeGen`, `heckeEvalBar_heckeGen`,
`heckeEvalBar_C`, `heckeModuleBar`, `heckeModuleBar_smul_def`,
`heckeModuleBar_heckeGen_smul`, `heckeModuleBar_smul_of_not`,
`heckeModuleBar_heckeGen_smul_of_not`, `heckeModuleBar_C_smul`. These need
`HeckeAlg`/`heckeGen` from `Definitions/Def_HeckeGalois_EichlerShimura.lean:14–16`
(`abbrev HeckeAlg := MvPolynomial Nat.Primes ℤ`; `def heckeGen`). **Try the tail
only after the in-cone part is green and the checker is clean.** If the import
cone of that pin file is large, restate the two definitions locally in
`Defs/HeckeModule.lean` (they are 3 lines), add
`Definitions/Def_HeckeGalois_EichlerShimura.lean` to `SOURCES`, and record the
decision. If it bites, defer the tail with a count and move on — it is not the
target.

### 2.5 `Defs/ArithmeticGalois.lean`

In-cone (required): `modularFunctionFieldBar` (`abbrev`), `JZero` (`abbrev`).

Out-of-cone (port if cheap, else defer with a count): `arithmeticRingAut`,
`coe_arithmeticRingAut_apply`, `arithmeticRingAut_algebraMap`, `arithmeticGalois`,
`toRingAut_arithmeticGalois`, `baseAut_arithmeticGalois`, `coe_arithmeticGalois_smul`,
the `Pic0` `SMul`/`DistribMulAction` instances and `galois_smul_pic0_def`, and
`JZero.torsionGaloisRep` (+ its two lemmas). These serve the modular
Galois-representation layer. Decide per declaration by `grep -c` in the corpus.

## 3. Verification

- Append `Definitions/Def_ModularCurve_Hecke{Operator,OperatorTotal,HeckeInputsAll?}`,
  `Def_ModularCurve_DegeneracyTower`, `Def_ModularCurve_HeckeModule`,
  `Def_ModularCurve_ArithmeticGalois` to the checker's `SOURCES` (the pin file for
  `HeckeInputsAll` is named `Def_ModularCurve_HeckeInputsAll.lean`), and the five
  port modules to `PORT_FILES`.
- Definition declarations verify by name. Some last names collide (`heckeU` etc.
  belong to the paused face; `heckeAlphaBar`/`towerInclBar` are yours). Run the
  checker and fix collisions by source ordering, not by renaming.
- `#print axioms` on `heckeSquareBar_commutes`, `heckeExchangeAt`'s two
  composite lemmas and `HeckeOperatorsCommuteBar`'s unfolding lemmas.
- Consumer Zone A: `#check` each headline at the pinned signature; state one
  `HeckeExchangeAt` and one `heckeOperatorBar N ℓ` term; assert the two
  definitional bridges (`heckeAlphaBar_eq_towerInclBar`,
  `heckeBetaBar_eq_towerSubstBar`) by `rfl`/`exact`.

## 4. Budget

**2 goal rounds, checkpoint at 1.** Round 1: `HeckeOperator`,
`DegeneracyTower`, `ArithmeticGalois`, checker clean. Round 2: `HeckeTotal`,
`HeckeModule` (in-cone), the optional payoff tail, log/README/consumer.

**Stop early on**: a private prelude lemma that is genuinely absent from the port
(prove it `private`, record it); a `HeckeExchangeAt`/`towerSubstBar` shape that
will not reduce definitionally (report, do not contort); or the `HeckeAlg` payoff
dragging a large import cone (defer with a count).

## 5. Reporting back

1. Module/line/decl table and checker before/after.
2. The four `'`-prelude counts (ported vs. pin) and where each ported lemma lives.
3. Whether `heckeBetaBar_eq_towerSubstBar` and `heckeSquareBar_commutes` closed by
   `rfl`-level reasoning or needed a `Subtype.ext`; quote the final proof shape.
4. The `HeckeAlg` decision (ported/deferred) with its count.
5. Anything SET-M2's Fricke/degree topics must import from here.
