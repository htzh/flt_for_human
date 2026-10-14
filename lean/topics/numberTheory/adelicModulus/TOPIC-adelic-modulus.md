# The adelic modulus family — the `distribHaarChar` product formula, place by place

**Status: planned.** The ready shelf's largest silo is
`NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`; it is not
one node but the middle of a four-node family that computes the **modulus character of the
adele ring** and derives the **product formula** from it. This note is that family's home:
§1 the mathematics, §2 the shelf and the measurement, §3 what the port already pays for,
§4 the new mathematics block by block, §5 the port structure, §6 risks and recorded
negatives, §7 reproduce, §8 the round.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
port mathlib `v4.34.0`.

Companions:

- [../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §2 — the shelf this
  family's headline sits at the head of, and §3 the workflow the sets below follow.
- [../../math/027-the-continuity-of-the-idele-norm.md](../../../math/027-the-continuity-of-the-idele-norm.md)
  — the mathematics of the modulus (`ideleNorm` *is* `distribHaarChar`), the local
  normalisations and the product formula.
- [../tateGlobal/TOPIC-continuous-ideleNorm.md](../tateGlobal/TOPIC-continuous-ideleNorm.md)
  — the T1 `FujisakiC3` engine this family's finite-place block is the companion of, and
  the record of the `M4aS4`/`AdelicCountability` homing.
- [../../automorphicForm/TOPIC-bruhat-transversal-trio.md](../../automorphicForm/TOPIC-bruhat-transversal-trio.md)
  §3 — where `M4aS4` and `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` were homed
  (`NumberTheory/AdelicHaar/PlaceMeasure.lean`), the module this family imports.
- Work orders: [WORKORDER-A1-adelic-modulus.md](WORKORDER-A1-adelic-modulus.md) (the
  modulus engines) and [WORKORDER-A2-product-formula.md](WORKORDER-A2-product-formula.md)
  (the principal-idele corollary).

## 1. The mathematics

Write $`F`$ for a number field, $`\mathbb{A}_F`$ for its adele ring and
$`\mathbb{A}_F^\times`$ for the ideles. The **modulus character** is the positive real
scalar by which an idele dilates additive Haar measure:

$$\mu(a \cdot S) = \mathrm{distribHaarChar}(\mathbb{A}_F, a) \cdot \mu(S),
\qquad a \in \mathbb{A}_F^\times .$$

The family proves that this character is the product of the local normalised absolute
values. The normalisation is the one of mathlib's `distribHaarChar` on the completions,
read through the two bridge lemmas the port already owns
(`FujisakiC3.distribHaarChar_completion_eq_pow_mult`,
`coe_distribHaarChar_adicCompletion_eq_norm`), and the statement splits into three
independent pieces:

1. **Archimedean, trivial finite part.** For $`a`$ with $`a_2 = 1`$,
   $`\mathrm{distribHaarChar}(\mathbb{A}_F, a) = \prod_{w \mid \infty} \lVert a_w
   \rVert^{n_w}`$, the multiplicity $`n_w = [F_w : \mathbb{R}]`$. This is
   `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` — **already ported**.
2. **Finite part.** $`\mathrm{distribHaarChar}(\mathbb{A}_F, u) = \prod_v \lVert u_v
   \rVert_v`$ for $`u`$ with trivial archimedean component, a `finprod` over the height-one
   primes. The proof is measure-theoretic: the integral lattice $`\widehat{\mathcal{O}}_F
   = \prod_v \mathfrak{o}_v`$ is a compact open with a transversal for the
   multiplication action, and the index of $`y \cdot \widehat{\mathcal{O}}_F`$ in
   $`\widehat{\mathcal{O}}_F`$ is the absolute norm of the ideal $`\prod_v
   \mathfrak{p}_v^{\mathrm{ord}_v(y)}`$ — so the modulus is computed by counting a finite
   quotient, `card_zhat_quot_eq_absNorm`, and then unfolded into the `finprod`,
   `card_zhat_quot_mul_finprod_norm`.
3. **Multiplication.** The two combine by splitting an idele into
   $`x = \mathrm{archUnit}(x) \cdot \mathrm{finUnit}(\mathrm{finPartUnit}(x))`$:
   `distribHaarChar_eq_placeModulus`. The headline
   `distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` is that statement with the
   product expression named.

The **product formula** is the family's corollary: a principal idele $`a \in
F^\times \hookrightarrow \mathbb{A}_F^\times`$ has modulus $`1`$, because multiplication by
it is an automorphism of the additive group that preserves the integral lattice
(`isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox`), hence is measure preserving
(`measurePreserving_mul_algebraMap`), hence has scalar factor $`1`$
(`distribHaarChar_algebraMap`).

The archimedean half also has a life of its own: $`K_\infty = \prod_{w} F_w`$ is itself a
locally compact ring, and its modulus character
`NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult` supplies the Jacobian
factor for $`x \mapsto ax`$ in the archimedean orbital integrals. It is the same
computation as (1), on the other carrier.

**A definitional trap.** The port's `NumberField.TateGlobal.ideleNorm` is *not* the product:
it is `((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)`, the modulus coerced. The
family's `placeModulus` is the *explicit product*,
$`\prod_w \lVert x_1 w \rVert^{n_w} \cdot \prod_v \lVert x_2 v \rVert`$. The two are the two
sides of the theorem, not a definition and its abbreviation. `port_advise` reports
`placeModulus → NumberField.TateGlobal.ideleNorm` as a substitution; that row is the
parser's type-only `def` artifact (§4(b) of the column note) and **must not be applied**.
The port's genuine relative is `NumberField.TateGlobal.FujisakiC3.normQ`, the same product
on the shell coordinates `Q (F := F) S` — a docstring cross-reference, not a
substitution, because the domains differ.

## 2. The shelf and the measurement

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
```

On the current tree the family's headline is the **largest silo on the ready shelf**, ahead
of `ModularCurve.phiIrreducible_all`:

| node | silo | `used_by` (cone / project) |
|---|---:|---|
| `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm` | 1,362 | **21 / 77** |
| `NumberField.TateGlobal.ideleNorm_det_eq_one_of_isCompact_of_mem` | 54 | 2 / 9 |
| `NumberField.TateGlobal.measurableSet_setOf_ideleNorm_det_mem_Icc` | 19 | 17 / 86 |
| `NumberField.AdeleRing.secondCountableTopology_generalLinearGroup_finTwo` | 32 | 22 / 217 |
| `NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult` | 418 | leaf — only under `--include-leaves` |

`frontier.py` on the headline: cone 2 nodes / 2,050; $`F`$ inside the cone 1 / 688 (the
already-ported `…_of_snd_eq_one`); **needed 1 / 1,362**.

```bash
python3 port_advise.py --target NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm \
  --json build/mulfinprod_advise.json
python3 port_plan.py --json build/mulfinprod_advise.json
```

| quantity | target alone | the family (6 files) |
|---|---:|---:|
| raw `S_` lines | 1,362 | 2,019 |
| declaration lines | 1,336 | 1,912 |
| duplicate copies | 0 | 305 |
| once-cost after dedup | 1,336 | 1,607 |
| already in the port (vetted, all tier 3) | 514 | 515 |
| substitutions | 32 trusted / 1 suspect | 52 trusted / 1 suspect |
| declaration groups | 90 | 111 |
| **net new math lines** | **822** | **1,092** |

The family's marginal cost is **270 lines for five more headlines**, and every one of them
reads a home that is already in the tree (below). The suspect substitution is the
`placeModulus` row of §1 in both readings.

## 3. What the port already pays for

**The `S4Base` half is homed and frozen.** The headline's pin file re-carries the whole
`M4aS4` place-measure block (its lines 589–1101) and the `AdelicCountability` block; both
were homed by the Bruhat-transversal trio into
`FLTForHuman/NumberTheory/AdelicHaar/PlaceMeasure.lean` (622 lines) and
`FLTForHuman/NumberTheory/AdelicLevel/Countability.lean`, and the premise headline
`distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one` sits in `PlaceMeasure.lean:537`
(pin `S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean:573`).
33 of the headline's 90 declarations are therefore import-only; the archimedean sibling is
21 of 28. **No promotion and no hub edit is owed**: every one of those rows is public, and
the only port-`private` names in reach (`TateGlobal/Ideles.lean`'s `ValuationOrd` block)
are reached only through public helpers.

**The definition layer is complete — the gate was closed by the manager before dispatch.**
`Def_NumberField_AdelicBox` is homed at `NumberTheory/AdelicBox.lean`
(`integralFiniteAdeles` and its compactness/openness), `Def_NumberField_AdelicHaar` at the
`NumberTheory/AdelicHaar/` directory, `Def_Mathlib_LinearAlgebra_Countable` at
`LinearAlgebra/Countable.lean`, and `Def_AutomorphicForm_SiegelReduction` at
`AutomorphicForm/Adelic/Siegel/Reduction.lean`.

The headline's fourth pin import, **`Def_NumberField_AdelicHeight`**, was the one node the
cluster imports that the port had not homed. It is a **definition node with no `Theorems/`
wrapper and 525 pin citers**, so by playbook §2.3 it is ported whole whether or not this
proof reaches it — and it does, by exactly one declaration: the pin's
`norm_finComp_eventually_eq_one` uses `norm_le_one_of_mem_adicCompletionIntegers` at its
lines 51 and 53, and that lemma is `Def_NumberField_AdelicHeight.lean:163`. Homed by the
manager at `FLTForHuman/NumberTheory/AdelicHeight.lean` (28 declarations, 27 public), wired
`Definitions/Def_NumberField_AdelicHeight.lean` into `SOURCES` and the module into
`PORT_FILES`, and built tier-1 green: the checker moved **9542 → 9569 identical (+27), 0
mismatched, 0 missing**, exactly the node's public surface. Nothing else it names is a port
declaration: `NumberField.FinitePlace.{embedding,equivHeightOneSpectrum,hasFiniteMulSupport,pos_iff}`,
`NumberField.prod_abs_eq_one` and `NumberField.InfinitePlace.prod_eq_abs_norm` are all
mathlib `v4.34.0`. Three proof adaptations were needed (`mul_le_one₀` and the two
`mul_lt_one_of_nonneg_of_lt_one_*` are deprecated in `v4.34.0`, and `finprod_le_finprod` lost
its nonnegativity argument); statements are the pin's verbatim.

**A recorded error of mine.** The first version of this paragraph claimed the pin's proof
used *no* declaration of `Def_NumberField_AdelicHeight`, on the strength of a `grep` for
`AdelicHeight` (2 hits, both in `p2m_open`) and for
`rowMaxNorm`/`finLocalHeight`/`finHeight`/`adelicHeight` (0 hits). The lemma the proof actually
uses does not carry the module's name, so the sweep missed it. WORKORDER-A1's
§2 was written on that false premise; the worker found the use, re-derived the lemma
`private`, and reported it. The manager's decision — the node is homed, so import it — was
applied, and the engine now imports `NumberTheory/AdelicHeight.lean` with no `private` copy.
The lesson for §3's checklist is the column's own §6 rule: search the *declarations* of a
`Def_*` module, not the module's name.

Because the node is homed and used, the A1 engine imports it. The A2 engine does not: its
four files never name it.

**No twin.** `twin_scan.py --node …` reports `new=1`, prelude 33/90 — every one of the 50
new declarations is new mathematics, not a renamed copy.

## 4. The new mathematics, block by block

The headline's 50 new declarations (817 transcribed lines) sit in five pin sections:

| pin section | new decls | lines | content |
|---|---:|---:|---|
| `P6B.JE2aFlat` (27–68) | 4 | 53 | `placeModulus`, the finite-component norm bookkeeping |
| `P6B.JE2aHMod` (86–439) | 29 | 417 | `zhatAddSubgroup`, `ySmulZhat`, `globalIdeal`, `ordNat`, `card_zhat_quot_eq_absNorm`, `absNorm_globalIdeal_mul_finprod_norm`, `card_zhat_quot_mul_finprod_norm` |
| `P6B.JE2aHMod` (1017–1101) | 4 | 105 | `HasTransversal`, `measurableSet_smul_zhat`, `finMeasure_smul_zhat`, `distribHaarChar_of_fst_eq_one` |
| `P6B.JE2aHMod` (1122–1129) | 2 | 107 | `coe_ySmulZhat_eq_smul`, `hasTransversal` |
| `P6B.JE2aHMod` (1229–1342) | 15 | 123 | `finUnit`/`finPartUnit`/`archUnit`, `distribHaarChar_finUnit`, `distribHaarChar_eq_placeModulus`, `solution` |

The archimedean sibling's eight new declarations (94 lines) are
`refBox`, `isCompact_refBox`, `interior_refBox_nonempty`, `infMeasure_refBox_{ne_top,ne_zero}`,
`arch_unit_ne_zero`, `distribHaarChar_infiniteAdeleRing` and `solution`, at
`S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean:326–418`.

The product-formula chain's 177 lines are four chained nodes:

| pin file | raw | net new | declaration |
|---|---:|---:|---|
| `S_NumberField_AdelicBox_isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox.lean` | 53 | 36 | `isAddFundamentalDomain_preimage_mul_algebraMap_adelicBox` |
| `S_NumberField_AdeleRing_measurePreserving_mul_algebraMap.lean` | 89 | 71 | `measurePreserving_mul_algebraMap` |
| `S_NumberField_AdelicHaar_measurePreserving_mul_algebraMap_adelicAddHaar.lean` | 28 | 16 | `measurePreserving_mul_algebraMap_adelicAddHaar` |
| `S_NumberField_AdeleRing_distribHaarChar_algebraMap.lean` | 69 | 54 | `distribHaarChar_algebraMap` |

They form a dependency chain in that order.

**Out of the family.** `NumberField.distribHaarChar_idelicNorm_genuineBaseChange`
(277 lines) is the same character in a base-change setting; it imports
`Def_M4aHerbrand_GenuineDescent` and is a separate subject. The two Dedekind-zeta shelf
rows (580 / 105) turn on `exists_completedDedekindZeta_package` and are the zeta column's.

## 5. The port structure

The pin keeps every declaration public — no `S_` file in the family has a `private`
helper — so the whole family is transcription, with the tier split doing the work:

| module | role | tier | pin |
|---|---|---|---|
| `FLTForHuman/NumberTheory/AdelicHeight.lean` | **definition gate: landed** — the local and adèlic heights | **1** | `Definitions/Def_NumberField_AdelicHeight.lean` |
| `FLTForHuman/NumberTheory/AdelicHaar/AdelicModulus.lean` | engine: the finite-place computation and the assembly | 3 | `S_NumberField_AdeleRing_…_mul_finprod_norm.lean` |
| `FLTForHuman/NumberTheory/AdelicHaar/ArchModulus.lean` | engine: the archimedean modulus on `InfiniteAdeleRing` | 3 | `S_NumberField_InfiniteAdeleRing_…_pow_mult.lean` |
| `FLTForHuman/NumberTheory/AdelicHaar/ProductFormula.lean` | engine: principal ideles preserve Haar | 3 | the four-file chain |
| `FLTForHuman/NumberTheory/AdelicModulus.lean` | façade: the six headlines (four landed with A2, two with A1) | **1** | the six `Theorems/` wrappers |

The pin namespaces `P6B.JE2aFlat`, `P6B.JE2aHMod`, `ArchModS44`,
`FltWs24.AdelicModulusOne` and `FltWs24.AdelicModulusOneChar` are kept verbatim (as
`M4aS4` was), so statement text matches the pin. The façade declares the four headline
statements from their `Theorems/` wrappers and proves each by its engine's pin lemma.

Wiring (appended last, per the friction log): the four wrappers and their four `S_` files
to `SOURCES`; the façade module to `PORT_FILES`; the three engines stay unlisted and enter
`spec/UNWIRED-PUBLIC.md` after `unwired_register.py --check` is regenerated.

## 6. Risks and recorded negatives

1. **The `placeModulus` substitution is a false positive.** Applying it would delete the
   statement's own left-hand name. Read `TateGlobal/Defs.lean:41` and
   `TateGlobal/FujisakiC3.lean:70` before touching that row.
2. **`P6B.JE2aFlat.placeModulus` vs `P6B.JE2aHMod`.** The pin declares `placeModulus` in
   the `JE2aFlat` block and uses it from `JE2aHMod`; the two engines are one module apart if
   `ArchModulus` is split out. Keep `placeModulus` beside the finite-place computation, not
   in `ArchModulus`.
3. **The `AdelicHeight` import is live, not dead — the order's §2 was wrong.** The pin's
   `norm_finComp_eventually_eq_one` uses `norm_le_one_of_mem_adicCompletionIntegers`
   (`Def_NumberField_AdelicHeight.lean:163`) at the pin's lines 51 and 53, so the A1 engine
   imports `NumberTheory/AdelicHeight.lean` (the node is homed; no `private` copy). The A2
   engine does not import it. Do not re-home it and do not re-derive it.
4. **`card_zhat_quot_mul_finprod_norm` is 72 lines and measure-heavy.** It is the one
   build-time risk; diagnose a low-cap failure with `set_option diagnostics true`, never by
   raising `maxHeartbeats`.
5. **`NumberField.AdeleRing.secondCountableTopology` is a last-name artifact.** The shelf's
   two high-leverage topology rows
   (`…generalLinearGroup_finTwo`, `AdelicHaar.exists_map_adelicGLHaar_eq_smul_prod`) are
   priced ready because the port declares `RestrictedProduct.secondCountableTopology`
   (`Topology/Algebra/RestrictedProduct/TopologicalSpace.lean:569`) — a different
   statement. The pin node's *substance* is in the port as the scoped instance
   `M4aS4.secondCountable_adeleRing` (`PlaceMeasure.lean:402`), so the consumers are
   portable, but the proofs must be written against the scoped instance. They are a
   different subject (adelic topology, not the modulus) and are **not** in this round.
6. **Recorded negative.** `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`
   has its own 688-line pin file, distinct from the Bruhat file's copy the port transcribed.
   Since the statement is identical and the port's copy is built and registered, the node is
   covered; the standalone file is not a separate order.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
python3 frontier.py --target NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm --top 0
python3 port_advise.py --target NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm \
  --json build/mulfinprod_advise.json
python3 port_plan.py --json build/mulfinprod_advise.json
python3 port_advise.py --targets build/modulus_cluster.txt --json build/modulus_advise.json
python3 port_plan.py --json build/modulus_advise.json
python3 twin_scan.py --node NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
```

`build/modulus_cluster.txt` is the six-file Cut A list of §2.

## 8. The round

| set | order | nodes | net new | tier |
|---|---|---|---:|---|
| gate | **landed** — `Def_NumberField_AdelicHeight` homed whole, wired, checker 9542 → 9569 (+27) | 1 definition node | 0 | 1 |
| A2 | **landed** — [WORKORDER-A2-product-formula.md](WORKORDER-A2-product-formula.md): engine `AdelicHaar/ProductFormula.lean` (216 lines, 9 declarations) + the four headlines in the façade, checker 9571 → 9575 (+4) | the four-node principal-idele chain | 177 | engine 3, façade 1 |
| A1 | **landed** — [WORKORDER-A1-adelic-modulus.md](WORKORDER-A1-adelic-modulus.md): `AdelicHaar/AdelicModulus.lean` (825 lines, 57 declarations) + `AdelicHaar/ArchModulus.lean` (142 lines, 7) + the two headlines in the façade, checker 9575 → 9577 (+2) | the headline + the archimedean sibling | 915 | engines 3, façade 1 |
| B | **landed** — [../tateGlobal/WORKORDER-T2-ideleNorm-det-slab.md](../tateGlobal/WORKORDER-T2-ideleNorm-det-slab.md): `NumberField/TateGlobalIdeleNormDet.lean`, checker 9569 → 9571 (+2) | the two `GL₂` idele-norm rows | 51 | 1 |

**Checker ledger for the round.** 9542 (before) → 9569 (definition gate, +27) → 9571 (Set B,
+2) → 9575 (A2's four headlines, +4) → **9577** (A1's two headlines, +2), 0 mismatched / 0
missing / 38 own throughout. The façade `NumberTheory/AdelicModulus.lean` holds all six
headlines from their `Theorems/` wrappers; the three engines are tier 3 and registered:
`AdelicHaar/AdelicModulus.lean` 57 public, `AdelicHaar/ArchModulus.lean` 7,
`AdelicHaar/ProductFormula.lean` 9, each row with its pin original (register: 81 → 84
modules, 1,987 → 2,060 public declarations). No existing module was edited, so no hub wave
was owed.

**Closed out.** The definition gate is homed and used by the A1 engine; all six headlines are
landed and diffed; the register is current. What is *not* in this round: the two
`NumberField.AdeleRing.secondCountableTopology`-gated topology rows (§6.5 — a different
subject, and their readiness is a last-name artifact), and the Dedekind-zeta shelf rows.

A1 and A2 have disjoint pin namespaces and disjoint modules and may be written in
parallel; every build is serialized through `flock .lake/flt_build.lock` and the checker
wiring stays with the manager. B is a two-headline module on the landed
`continuous_ideleNorm_det` wire and is independent of both. Sets are reviewed one at a
time, in that order.
