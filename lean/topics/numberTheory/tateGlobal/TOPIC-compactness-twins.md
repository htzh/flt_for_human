# The Fujisaki compactness twins — `normOneIdeles`, its compactness and the idele class group

**Status: landed 2026-10-13.** The ready shelf's new head is a pair of 3,600-line `S_`
files that were opened by the adelic-modulus round
([TOPIC-adelic-modulus.md](../adelicModulus/TOPIC-adelic-modulus.md)): both cite exactly one
premise, `NumberField.AdeleRing.distribHaarChar_algebraMap`, the headline that round landed.
This note is the pair's home: §1 the mathematics, §2 the twin measurement, §3 the definition
gate (landed), §4 the port structure, §5 risks and recorded negatives, §6 reproduce.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

Companions:

- [TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md) — the T1 `FujisakiC3` engine
  and the nine-file family this pair belongs to; §5 the build-cost ladder and §7 the recorded
  `ValuationOrd` decision this note reuses.
- [../adelicModulus/TOPIC-adelic-modulus.md](../adelicModulus/TOPIC-adelic-modulus.md) — the
  round that opened the pair, and the product formula both headlines consume.
- [../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3 — the workflow.
- Work order: [WORKORDER-T3-fujisaki-compactness.md](WORKORDER-T3-fujisaki-compactness.md).

## 1. The mathematics

Fujisaki's compactness theorem, in the two forms the development consumes.

Write $`\mathbb{A}_F`$ for the adele ring, $`\mathbb{A}_F^\times`$ for the ideles, and
$`\mathbb{A}_F^1 = \mathrm{normOneIdeles}(F) = \ker(\operatorname{distribHaarChar})`$ for the
norm-one ideles. The two headlines are:

1. **Compact representatives.** There is a compact
   $`K \subseteq \mathbb{A}_F^1`$ such that every $`x \in \mathbb{A}_F^1`$ factors as
   $`x = \eta \cdot \kappa`$ with $`\eta \in F^\times`$ (diagonally embedded) and
   $`\kappa \in K`$. Uniqueness is not claimed. Proof: choose one representative per ideal
   class of $`\mathcal{O}_F`$ (`fracIdealAtUnit`, `fracIdealProd`, `count_fracIdealProd`), take
   the product of the local unit balls, and use that only finitely many places are
   uncontrolled; the resulting set is a product of `adicCompletionIntegers` and hence compact
   (`isCompactAdicCompletionIntegers`).
2. **The norm-one idele class group is compact.** By the product formula,
   $`F^\times \subseteq \mathbb{A}_F^1`$ (that is
   `NumberField.AdeleRing.distribHaarChar_algebraMap`), so
   $`\mathbb{A}_F^1 / \overline{F^\times}`$ — the statement's
   `normOneIdeles F ⧸ (principalIdeles …).subgroupOf …` — is compact.

Statement 2 is the compactness behind the finiteness and covering statements for Siegel sets
and slabs modulo the centre; statement 1 is its representative-set counterpart, used to reduce
integrals over $`\mathbb{A}_F^1`$ to integrals over a compact set.

## 2. The twin measurement

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
```

Both rows are at the head of the shelf, and both were unschedulable before the modulus round
(their three ported cone nodes, 211 lines, are exactly the three A2 pin files):

| node | silo | `used_by` (cone / project) |
|---|---:|---|
| `NumberField.TateGlobal.exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul` | 3,683 | 1 / 34 |
| `NumberField.TateGlobal.compactSpace_normOneIdeleClass` | 3,615 | 5 / 18 |

```bash
printf '%s\n' \
  P2M/Sol/S_NumberField_TateGlobal_exists_isCompact_subset_normOneIdeles_forall_mem_exists_eq_map_algebraMap_mul.lean \
  P2M/Sol/S_NumberField_TateGlobal_compactSpace_normOneIdeleClass.lean > build/compactness_pair.txt
python3 port_advise.py --targets build/compactness_pair.txt --json build/compactness_advise.json
python3 port_plan.py --json build/compactness_advise.json
```

| quantity | file A (`exists_isCompact_…`) | file B (`compactSpace_…`) | **the pair** |
|---|---:|---:|---:|
| raw `S_` lines | 3,683 | 3,615 | 7,298 |
| declarations | 285 | 284 | 286 groups |
| net new **alone** | 1,017 | 949 | — |
| **net new together** | — | — | **1,023** |
| already in the port (all tier 3) | 2,638 | 2,638 | 2,638 |
| shared block | — | — | once 3,664 / in port 2,764 / **268 decls** |

The pair is one development. Porting them separately costs 1,966; together **1,023**. The
normalized `diff` between the two files is ~1,178 lines and the namespace spines differ by
exactly four lines — file A carries an `M4aLocalCFT.FujisakiR1` section (its own cap) that
file B lacks. Everything else, including the `FujisakiC2c` section that file B's headline
calls, is shared.

**The new mathematics** is ~102 declarations per file: `ord`, `unitAtHom_embUnit_self`,
`ordAt_one`, `coe_ne_zero_of_irreducible` in the early blocks, and then the Fujisaki count —
`fracIdealAtUnit`, `fracIdealProd`, `fracIdealProdHom`, `count_fracIdealProd`,
`fracIdealProd_eq_one_iff`, … — assembling `M4aLocalCFT.FujisakiR1.exists_isCompact_impl` and
`M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl`.

**The 8 suspect substitutions are the known false positives** (`archBox` →
`NumberField.TateGlobal.archSlab`, `box` → `NumberField.TateGlobal.slab`, `SUnits`/`DeepUnits`
→ `FLTForHuman.Elliptic.Univ.Poly`): the parser's type-only `def` artifact, the same rows the
T1 topic recorded. None is a `def` of this pair's statement surface. Do not apply any of them.

## 3. The definition gate — landed

The pair's three pin `Def_*` imports are all already homed, so **no definition work was owed**;
the manager wired the one that was still unlisted:

| pin module | port home | status |
|---|---|---|
| `Def_NumberField_TateGlobalZeta` | `NumberTheory/NumberField/TateGlobal/Defs.lean` | tier 3, registered (15 public) |
| `Def_M4aHerbrand_IdeleClassVocab` | `NumberTheory/M4aHerbrand/IdeleClassVocab.lean` | listed |
| `Def_NumberField_Completion_Finite` | `NumberTheory/NumberField/Completion/Finite.lean` | **wired** — tier 3 → tier 1 |

`Def_NumberField_Completion_Finite` had no consumer until now; the pair uses
`NumberField.isCompactAdicCompletionIntegers` at its lines 595 and 638. It was homed whole
already (5 public declarations, all with pin provenance), so the manager's edit was the
`SOURCES`/`PORT_FILES` pair: the checker moved **9577 → 9582 identical (+5)**, 0 mismatched,
0 missing. No existing module was edited, so no hub wave was owed.

## 4. The port structure

| module | role | tier |
|---|---|---|
| `FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiCompact.lean` | engine: the shared development, at the pin namespaces `M4aLocalCFT.*` | 3 |
| `FLTForHuman/NumberTheory/NumberField/TateGlobalCompactness.lean` | façade: the two headlines | **1** |

**File A is the representative source.** It is a superset of file B: transcribing file A whole
(except its final `solution`) gives the shared block *and* the `FujisakiR1` cap, and file B's
headline is a one-line call to the shared
`M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl`, which is already in that text.
So the engine is **one module**, not two, and the second file contributes no declaration of its
own.

The façade states the two `Theorems/` wrappers verbatim and proves them by
`M4aLocalCFT.FujisakiR1.exists_isCompact_impl F` and
`M4aLocalCFT.FujisakiC2c.compactSpace_normOneIdeleClass_impl F`. Note the wrapper-spelling rule
the modulus round learned the hard way: **the checker diffs the wrapper's text**, so the
headline that mentions `(AdeleRing (𝓞 F) F)ˣ` must be spelled as that wrapper spells it, not
reformatted into the port's idiom.

Wiring (appended last, per the friction log): the two wrappers then their two `S_` files to
`SOURCES`; the façade to `PORT_FILES`; the engine stays unlisted and enters
`spec/UNWIRED-PUBLIC.md`.

## 5. Risks and recorded negatives

1. **The `ValuationOrd` prelude is dead in this node — do not transcribe it and do not
   promote it.** Both files re-carry the pin's `M4aLocalCFT.ValuationOrd` block (lines 85–284),
   whose 11 declarations `port_advise` matches to *port-`private`* declarations in
   `TateGlobal/Ideles.lean` (`NumberField.TateGlobal.ValuationOrd.*`). That is the block the T1
   topic kept private. **Verified mechanically:** in both files every occurrence of the eleven
   names (`ordA`, `ordZ`, `ordA_span`, `ordA_mul`, `ordA_unique`, `ordZ_spec`, `coe_mk_ne_zero`,
   `exists_rep`, `exists_span_eq_pow`, `pow_maximalIdeal_ne_of_lt`,
   `pow_maximalIdeal_injective`) lies between lines 93 and 248, i.e. **inside the block
   itself**; nothing after line 284 names any of them. So no new proof term reaches a
   port-`private` name, the block is substituted by its existing home, and **no promotion is
   owed**. (Had it been live, the promotion would have been a hub edit on
   `TateGlobal/Ideles.lean` priced by `build_ladder.py --edit` at 27 modules / 8,389 lines
   ≈ 110 s.)
2. **The 2,638 in-port lines are tier 3.** The engine imports the T1 modules
   (`TateGlobal/{Defs,Coordinates,Ideles,FiniteSlab,ArchSlab,DistribHaarChar,ZetaIntegrand,
   LocalZetaUnramified,ArchMulHaar,ValuedOrdBridge,…}`); they are importable but unlisted, so
   their statements are *registered*, not statement-diffed. That is the tier-3 economy, not a
   gap to close in this order.
3. **The two `solution`s are the façade's.** Neither engine transcribes them.
4. **Build risk.** The named risk is `count_fracIdealProd` and the ideal-class count around
   it. The 200,000 cap is not to be raised; a low-cap failure is diagnosed, not capped around.
5. **Recorded negative — the third name.** The request listed
   `compactSpace_normOneIdeleClass` twice; the round exposed no third silo in this family, so
   the pair is the whole cut. The smaller rows the round also exposed
   (`TateGlobal.ideleNorm_det_eq_prod_archDetNorm_pow_mult` 115,
   `AdelicHaar.adelicAddHaar_setOf_{fst,snd}_apply_eq_eq_zero` 128/119,
   `AdelicBox.setLIntegral_adelicBox_comp_mul_add_eq_of_periodic` 129,
   `AdelicBox.integral_cond_adelicBox_comp_mul_algebraMap` 122,
   `TateGlobal.ideleNorm_eq_one_of_fst_eq_one_of_finitePartUnits_mem_unitIdeles` 49,
   `TateGlobal.ideleNorm_uniformizerIdele` 39, `RatIdele.exists_norm_apply_eq_ideleNorm_rpow`
   312) are **not** in this order.

## 6. Reproduce

```bash
cd tools/deps
python3 port_advise.py --targets build/compactness_pair.txt --json build/compactness_advise.json
python3 port_plan.py --json build/compactness_advise.json
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/Ideles.lean
cd ../lean
timeout 300 python3 spec/check_flt_statements.py
```

## 7. The set

| set | order | nodes | net new | tier |
|---|---|---|---:|---|
| gate | **landed** — `Def_NumberField_Completion_Finite` wired, checker 9577 → 9582 (+5) | 1 definition node | 0 | 1 |
| T3 | **landed** — [WORKORDER-T3-fujisaki-compactness.md](WORKORDER-T3-fujisaki-compactness.md): engine `TateGlobal/FujisakiCompact.lean` (966 lines, 95 declarations, 2 public) + the two headlines in `TateGlobalCompactness.lean`, checker 9582 → 9584 (+2) | the twin pair | 1,023 | engine 3, façade 1 |

**Checker ledger.** 9577 (before the gate wiring) → 9582 (gate, +5) → **9584** (T3's two
headlines, +2), 0 mismatched / 0 missing / 38 own. The engine is tier 3 and registered:
`TateGlobal/FujisakiCompact.lean` 2 public declarations, both kernels, each with a pin
original (register: 84 modules / 2,057 public / 1,769 pin).

**Recorded negative — the `port_advise` self-reference.** Re-running `port_advise` on file A
*after* its engine exists reports 272 substitutions instead of 178: the 94 extra are the pin
declarations matched against the worker's own transcription in the new module. So a name-parity
check must use the advise file generated **before** the module is written, or exclude the new
module — read literally, the order's §7 "name parity against `port_advise`" invites a worker to
see its own output as pre-existing mathematics. The T3 order's results section carries the
detail; this wants a line in `tools/deps/README.md` or the playbook §3.5.
