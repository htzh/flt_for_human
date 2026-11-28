# SET-AF113 — the partial Euler product: the diagOne identity, its entire and meromorphic forms, and the Schwartz closure

**Status: landed (2026-11-27).** The next set of the AF column in the D–S cone, scoped
per [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md) with
`--include-leaves`. SET-AF112 left a ready shelf of **11 rows / 6,204 silo**; this set cuts **seven of
them, 4,869 silo**, in five orders — and it is a **consumer set**: 103 of the rows' declarations are
already in the port (±1,968 lines), and 71 more sit in the port `private` and are promoted here.

| # | order | rows | silo | module(s) |
|---|---|---:|---:|---|
| A | the `diagOne` Whittaker coefficient is a character times an Euler product | 1 | 2,695 | `AutomorphicForm/Adelic/WhittakerDiagOneEulerProduct.lean` (new) |
| B | the entire partial Euler product | 1 | 595 | `AutomorphicForm/Adelic/EulerProductEntire.lean` (new) |
| C | the meromorphic partial Euler product | 1 | 995 | `AutomorphicForm/Adelic/EulerProductMeromorphic.lean` (new) |
| D | the `diagOne` coefficient at `1`: level vanishing and the principal-idèle expansion | 2 | 341 | `AutomorphicForm/Adelic/WhittakerDiagOneExpansion.lean` (new) |
| E | the Bruhat–Eisenstein decomposition, and the Schwartz–Bruhat closure | 2 | 243 | `AutomorphicForm/Adelic/BruhatEisensteinDecomposition.lean` (new); `NumberTheory/AdelicFourier/SchwartzClosure.lean` (new) |
| **total** | | **7** | **4,869** | 6 new modules + 71 promotions |

§0 the read; §1 the stories; §2 the scaffolds; §3 homes; §4 ground prep (the promotions); §5 what is
**not** cut, and why; §6 traps; §7 gates; §8 reproduce and the forecast.

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf12.json
python3 frontier.py --selfcheck
```

The 20-name unport correction list of SET-AF109 is **again identical** on this shelf (no false marker
touches an AF node), so there is one set of figures:

| figure | value |
|---|---:|
| `needed [F terminal]` | **202 / 130,951** |
| frontier (union) | 2,232 / 1,000,681 |
| ready rows, all namespaces | **11 / 6,204** |
| leaves, all namespaces | **5 / 13,761** |
| withheld by the FR-0044 guard | 6 / 1,970 |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

**`--selfcheck` is INCONSISTENT**: the live MD-005 phi-family inventory (`ModularCurve.PhiGen.*`,
`ModularCurve.{exists_phiIrreducible*, phiIrreducible_*}`, `isInftySide_cuspInftyBar`), MD-007
(`ModularForm.heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0`) and
`WeierstrassCurve.Affine.ncard_fibSet`. Unchanged from SET-AF112's read; no AF shelf row is affected.

**The AF ready shelf, quoted whole** (rank by silo; `prem` = graph premises, `lev` = leverage
cone/project):

| row (prefixes dropped) | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `AutomorphicForm.whittakerCoefficient_bruhatEisenstein_diagOne_eq_cpowChar_mul_sum_eulerProduct_of_flat_family` | 2,695 | 20 | 1 / 1 | **A**: the `diagOne` coefficient is `cpowChar` times an Euler product |
| `WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` | 1,133 | 20 | 1 / 5 | deferred (§5) |
| `AutomorphicForm.exists_meromorphicOn_partialEulerProduct_mul_weylIntertwiningIntegral_eq_mul` | 995 | 17 | 7 / 10 | **C**: the meromorphic partial Euler product |
| `AutomorphicForm.exists_unitaryChar_entire_partialEulerProduct_mul_eq_tsum_whittakerCoefficient_bruhatEisenstein` | 595 | 9 | 1 / 1 | **B**: the entire partial Euler product |
| `AutomorphicForm.exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation` | 211 | 3 | 1 / 3 | **D**: vanishing beyond the level box |
| `TateCurve.lineCoeff_eq_zero` | 142 | 3 | 1 / 1 | deferred (§5) |
| `NumberField.AdelicFourier.fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace` | 141 | 6 | 2 / 6 | **E**: the transform preserves Schwartz–Bruhat |
| `AutomorphicForm.hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul` | 130 | 4 | 2 / 3 | **D**: the principal-idèle HasSum |
| `AutomorphicForm.bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary` | 102 | 4 | 2 / 5 | **E**: the constant term plus the Whittaker sum |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` | 36 | 2 | 1 / 3 | deferred (§5) |
| `ModularCurve.rep_tateModule_jOne_comm` | 24 | 1 | 1 / 6 | deferred (§5) |

**The premise audit was run before the cut** (FR-0338): all seven cut rows' premises read `ported`
except five `SHADOW` entries — `norm_apply_eq_one_of_isGlobalAddChar` (×3, the known notation artefact),
and for the Schwartz row `fourierIntegral_pureTensor_eq` and `integrable_of_mem_schwartzBruhat`, whose
port copies are **generalised** statements (any function in place of a `SchwartzMap`; a general
`[MeasurableSpace 𝔸]` carrier), so the pin's proof applies them at the site — a proof adaptation, not
a statement obstacle. The def layer is `ok` everywhere; `FactorizationDatum`'s "15 absent" are its
structure fields and `M4aHerbrand`'s "2 absent" are projection fields, not gates.

## 1. The stories

### A — the `diagOne` Whittaker coefficient is a character times an Euler product (2,695)

The set's headline. For a **flat family** `φ` of induced sections (`φ s` depends on the finite idèle
only through the level subgroup, and on the archimedean component), a global character `ψ` with its
local data (`ψv`, `nψ`, `θr`, `θc`), a uniformiser family `ϖ` and `Re s` in the convergence range, the
`diagOne` Whittaker coefficient at `1` factors as a character times a sum over an Euler product — the
identity that makes the Bruhat–Eisenstein `L`-function an Euler product.

**This is a consumer row**: of its 107 helpers (≈1,875 lines) **85 are already in the port** —
68 of them `private` in `EisensteinGeneral/PiecePartialEulerProduct.lean` (SET-AF110A's engine) and its
neighbours — and only **22 (≈310 lines) are new**, beside the headline's own proof.

### B — the entire partial Euler product (595)

There is a **unitary idele-class character** `χ` and an **entire** `Nc` with
`(∏'_{v ∉ S} (1 - χ_v(ϖ_v)|Nv|^{-(2s+1)})) · Nc s = ∑'_{ξ≠0} w(ξ) g` for `Re s > 1`. Nine helpers, 3 in
the port (`Glue`/`Piece`), 6 new (≈253 lines).

### C — the meromorphic partial Euler product (995)

There are `S`, `ϖ` and an `R` meromorphic on `ℂ`, differentiable on `Re s > 0`, with
`(∏'_{v ∉ S}(1 - χ_v(ϖ_v)|Nv|^{-2s})) · W(φ s, g) = (∏'_{v∉S}(1 - χ_v(ϖ_v)|Nv|^{-(2s+1)})) · R s` for
`Re s > 1/2`. Forty-four helpers, 39 new (≈760 lines): the `per_datum_identity` (185 lines) and the
`placeVal`/`good_place` dictionary are the order's own engine.

### D — the `diagOne` coefficient at `1` (341)

Two flat rows of the cusp-form Fourier expansion at the `diagOne` torus: the coefficient vanishes
outside a level box (`exists_whittakerCoefficient_one_diagOne_eq_zero_of_exp_lt_valuation`, 211, 9 public
declarations) and, for cuspidal `φ`, the coefficients at `1` along the **principal idèles** sum to
`φ g` (`hasSum_whittakerCoefficient_one_diagOne_principalIdeles_mul`, 130, 4 public). Both consume
SET-AF112's `WhittakerSmoothSummability` row (`Integrable`/`Summable`).

### E — the decomposition and the Schwartz closure (243)

* `bruhatEisenstein_eq_constantTerm_add_whittakerSum_of_one_lt_re_of_unitary` (102): the series is its
  constant term plus its Whittaker sum — inserted into `BruhatEisenstein.lean`, beside the constant-term
  row it consumes, with SET-AF112B's summability row as the well-definedness input.
* `fourierIntegral_mem_schwartzBruhat_of_apply_eq_fourierChar_trace` (141): the Fourier transform
  preserves `schwartzBruhat F`. Four flat public declarations; its two premises are the port's
  **generalised** copies (§0), applied at the site.

## 2. The scaffolds

Six new modules are scaffolded before any order starts. All elaborate at the 200 k edit-loop cap with
only their `sorry`s.

| order | module | new | scaffold `check_port` |
|---|---|---|---:|
| A | `AutomorphicForm/Adelic/WhittakerDiagOneEulerProduct.lean` | 1 | **1 ok** |
| B | `AutomorphicForm/Adelic/EulerProductEntire.lean` | 1 | **1 ok** |
| C | `AutomorphicForm/Adelic/EulerProductMeromorphic.lean` | 1 | **1 ok** |
| D | `AutomorphicForm/Adelic/WhittakerDiagOneExpansion.lean` | 2 | **2 ok** |
| E | `AutomorphicForm/Adelic/BruhatEisensteinDecomposition.lean` | 1 | **1 ok** |
| E | `NumberTheory/AdelicFourier/SchwartzClosure.lean` | 1 | **1 ok** |
| **total** | **6 files** | **7 rows** | **7 ok / 0 / 0 / 0 / 0** |

## 3. Homes

| row | premises' homes | why this home |
|---|---|---|
| A | `EisensteinGeneral/{PiecePartialEulerProduct,PieceFactorizationDatum,PieceWeylIntegrability,ArchIntegralBound,LocalRam,LocalUnr}`, `AutomorphicForm/Adelic/{AddCharLocalComponents,BruhatEisensteinWhittakerSummability}`, `NumberTheory/NumberField/{HeightOneSpectrumSummable,GlobalAddChar/Circle}`, `LanglandsTunnell/*` | new, above the whole `EisensteinGeneral` engine; the subject is the Whittaker `diagOne` coefficient, which is the `AutomorphicForm/Adelic/` theory's |
| B | `PiecePartialEulerProduct` (its entire-product row), `PieceWeylIntegrability`, `ArchIntegralBound`, `PieceFactorizationDatum` | new, above the same engine |
| C | `AutomorphicForm/Adelic/{InducedSectionSpan,WeylIntegrable,ArchAtomGeneral,LocalAtomIntegrable,HeightWeylMass,BigCellExpansion}`, `EisensteinGeneral/{Factorization,LocalRam,LocalUnr,ArchIntegralBound}`, `NumberField/TateGlobal*` | new, above the local-integral and Tate-global machinery |
| D | `WhittakerCoefficient`, `WhittakerSum`, `WhittakerSystem`, SET-AF112's `WhittakerSmoothSummability`, `RankinSelbergShellIndicator`, `BorelFundamentalDomain`, `TateGlobal/FiniteSlab` | new, above `WhittakerSmoothSummability` and the Borel-unfolding dictionary |
| E (102) | `BruhatEisenstein` (the constant-term row) + SET-AF112B | **new module above both**: the natural home was an insertion into `BruhatEisenstein.lean`, but `EisensteinGeneral/Unfolding.lean` imports that module and AF112B imports `Unfolding`, so the insertion is an import cycle (measured on the scaffold, re-homed before dispatch) |
| E (141) | `NumberTheory/AdelicFourier/{Transform,Space}`, `AdelicBox`, `NumberField/GlobalAddChar` | new, above `Transform` and `Space` (the module that inserts *into* one of them would be a cycle) |

## 4. Ground prep — 71 promotions

Of the seven rows' 93 in-port helpers, 21 are already public and **71 exist only as `private`**:

| module | promoted | `check_port` before → after |
|---|---|---:|
| `EisensteinGeneral/PiecePartialEulerProduct.lean` | **70** (the `pc_*` partial-Euler-product engine, including the two `@[reducible]` Borel structures `pc_locBorel`/`pc_finBorel`) | 1 ok → **71 ok** |
| `EisensteinGeneral/PieceFactorizationDatum.lean` | 1 | 1 ok → **2 ok** |

Both `0 mismatch / 0 missing` and silent. The promotion is the AF112-B pattern at scale: the pin states
the engine in more than one `S_` file, the port wrote it once privately, and the consuming set imports
it rather than re-deriving it. `ch_norm_pow_le` is the one in-port name in neither state under its pin
name: the port holds it as `AutomorphicForm.LocalIntertwining.ComplexAtomLimit.norm_pow_le` (binder
spelling), to be applied at the site.

## 5. What is not cut, and why

* **`WeierstrassCurve.bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` (1,133)** —
  still false ready: its premise `ModularCurve.ModularPolynomialData.dvd_resultant_of_mul` has no port
  declaration and its own premise `phiIrreducible_all` is an MD-005 false marker (CARRY-FORWARD, SET-AF112).
* **`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (36)** — false ready (shadow premise);
  CARRY-FORWARD since SET-AF102.
* **`ModularCurve.rep_tateModule_jOne_comm` (24)** and **`TateCurve.lineCoeff_eq_zero` (142)** —
  definition-layer gates (89 of 100 and 43+128 of 48+128 declarations absent); registered in
  CARRY-FORWARD.
* **The five leaves** (13,761 silo) — all definition-layer gates, unchanged from SET-AF112.

## 6. Traps for this set

1. **A is a promotion consumer, not a transcription.** 85 of its 107 helpers are in the port; the
   order must import them (the 71 promoted names live in `EisensteinGeneral.Piece` /
   `EisensteinGeneral.FiniteAdelicFactorization` / `EisensteinGeneral.TwistedSmoothLocal` /
   `EisensteinGeneral.WeylGlue` namespaces) and write only the 22 new ones.
2. **The port's `integrable_weyl_unipotent_mul_of_factorization` takes the *local* characters `ψv`,
   the pin's takes `ψ`.** The advise flags it as a binder variant; it is a different statement. Order B's
   proof must pass through the port's form (the pin's is the same identity with `ψ` reconstructed by
   `∏ᶠ` — read both texts before substituting).
3. **`fourierIntegral_pureTensor_eq` and `integrable_of_mem_schwartzBruhat`** (order E) are port
   **generalisations** (§0). Apply the port's statement at the pin's arguments; do not restate the
   pin's narrower form.
4. **Order A's statement has a `let α` and two nested `∀` blocks after it** (`∀ (hα …) …`,
   `∀ (S : Finset …), S₀ ⊆ S → ∃ …`). Keep the wrapper's text verbatim; the `_`-prefixed binders are
   the pin's and the flat-family hypothesis `_hφflat` must stay exactly as written.
5. **Order B's `ψ` is the global character while the port's helper takes `ψv`**: when the pin's proof
   builds `∏ᶠ v, ψv v (x v)`, keep the `∏ᶠ` (finite product over a cofinite support) and the
   `Function.support nψ` finiteness.
6. **Order D's `M4aHerbrand.principalIdeles`** is the port's `IdeleClassVocab` block; `finSingle` is
   `NumberField.TateGlobal.finSingle` at the port's binder names.
7. **Order E's insertion** is into a 1,158-line module with 6 checked declarations: add the two
   `spec-pin:` lines, the two imports (`WhittakerSum`, `BruhatEisensteinWhittakerSummability`) and the
   row before `end AutomorphicForm`; nothing else in the file moves.
8. **The promotions are done**; do not edit `PiecePartialEulerProduct.lean` or
   `PieceFactorizationDatum.lean` — if a name is still private, report it.

## 7. Gates

Per order: `check_port` **0 mismatch / 0 missing** with every added declaration `ok`; the module's own
`lake build` under `flock`/`timeout`, silent but for its `sorry`s (removed); `#print axioms` on every
headline → `[propext, Classical.choice, Quot.sound]`; `dedup.py` / `move_dead.py`; a consumer zone in
`spec/` (the set-end one is the manager's). No tree build.

## 8. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf12.json
python3 port_advise.py $(sed 's/^/--nodes /' ../../lean/tmp/af113/rows.txt | tr '\n' ' ') \
  --json build/af113_advise.json
```

The measured substitutions: **103 declarations already in the port (≈1,968 lines)**, 8 binder
variants, 8 named statement variants, and 71 promotions. The forecast read (with the seven rows
treated as landed) goes in when the set lands.

## 9. The landing, measured

**Status: landed (2026-11-27).** Five orders, seven rows, six new modules.

| order | module | lines | declarations | `check_port` |
|---|---|---:|---|---|
| A | `AutomorphicForm/Adelic/WhittakerDiagOneEulerProduct.lean` | **705** | 1 public + 16 `private` | **1 ok** |
| B | `AutomorphicForm/Adelic/EulerProductEntire.lean` | **301** | 1 public + 4 `private` | **1 ok** |
| C | `AutomorphicForm/Adelic/EulerProductMeromorphic.lean` | **1,020** | 1 public + 40 `private` | **1 ok** |
| D | `AutomorphicForm/Adelic/WhittakerDiagOneExpansion.lean` | **365** | 8 public | **8 ok** |
| E | `AutomorphicForm/Adelic/BruhatEisensteinDecomposition.lean` | **157** | 1 public + 1 `private` | **1 ok** |
| E | `NumberTheory/AdelicFourier/SchwartzClosure.lean` | **196** | 4 public | **4 ok** |
| — | promotions: `PiecePartialEulerProduct` / `PieceFactorizationDatum` | 0 new | +70 / +1 public | **71 ok · 2 ok** |
| — | `spec/SetAF113Consumer.lean` (2 zones) | **154** | consumer, not wired | **silent** |

6,918 lines of new module code for 4,869 pin lines (1.42×), every file `0 mismatch / 0 missing`, its own
`lake build` exit 0 under `flock`, its edit loop silent at the 200 k cap, `dedup` 0 clusters and
`move_dead` 0 declarations per module. The seven headlines' `#print axioms`: exactly
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`.

**The consumer zone** (two zones, no `#check`s): (1) **AF113A with the finite-place data discharged** —
SET-AF113A's row assumes `ψv`, `nψ` and their four properties, and SET-AF112D's
`exists_localComponents_of_isGlobalAddChar` produces them, so the `diagOne` identity holds from `hψ`
alone (the archimedean phases stay the caller's data); (2) SET-AF112B's `Summable` over `F` restricted
to `{ξ : F // ξ ≠ 0}` by `Summable.comp_injective`, which is the convergence of the Whittaker sum in
order E's decomposition.

**Plan vs actual.**

* **The measured saving is exactly the set's silo.** `needed [F terminal]` **202 / 130,951 →
  195 / 126,082**: seven nodes and **4,869 lines**, the cut's own figure — every row was cut whole and
  none dragged an out-of-scope premise. The measured substitutions landed at **103 declarations
  (≈1,968 lines)** already in the port and **71 promotions**, as priced; order A wrote only the 17
  declarations its pin's flat-family dictionary needed.
* **One gate text was a scaffold number.** Order D was written with "2 ok"; measured **8 ok** (the two
  headlines plus the six public helper transcriptions). Same class as SET-AF112's A/E: the *size* was
  mis-stated, the gate (`0 mismatch / 0 missing`) met.
* **A namespace drift was found and fixed by the manager.** The promoted
  `integrable_weyl_unipotent_mul_of_factorization` had been declared at the **root** name (the
  declaration sits after `end EisensteinGeneral.Piece`), while the pin's own name and the module's
  header both say `EisensteinGeneral.Piece.…`. It is now declared with the pin's dotted name and the
  three call sites (`EulerProductEntire`, `WhittakerDiagOneEulerProduct`, `PiecePartialEulerProduct`)
  were updated; `PieceWeylIntegrability` reads **15 ok**, all four modules rebuilt and green.
* **The scaffold's import lists were one to five modules short in five of six modules** — the
  generator derives imports from the `S_` file's `Definitions/` imports and the premises' homes, and
  the pin's `Theorems/` wrappers reach further. Each worker fixed it in one edit-loop round; the
  generator should read the wrapper's `Theorems/` imports too.
* **Preamble errata (FR-0343).** The substitute list mixed `port_advise`'s *importable* block with its
  *binder-variant pointers*, so a `private` name (`Assembly.finprod_eq_prod_mul_finprod_subtype`) was
  listed as usable and two names were mis-homed. Workers B and C found their way in one round.
* **Style options**: order C carries one file-scope `linter.style.haveILetI false` for the pin's
  load-bearing `letI`/`haveI` (precedent `EisensteinGeneral/Factorization.lean`); order A carries the
  same option on its headline. Neither is a heartbeat option.

**Post-landing read.** `needed [F terminal]` **195 / 126,082**; ready **10 / 6,918** (was 11 / 6,204);
leaves 5 / 13,761 and withheld 6 / 1,970 unchanged. **Six rows / 5,083 silo became ready because of
this set** — the largest `AutomorphicForm.exists_whittakerCoefficient_diagOne_continuation_of_flat_family`
(1,993, the analytic continuation of the `diagOne` coefficient), then
`tendsto_sub_one_half_mul_weylIntertwiningIntegral_sub_nhds_zero_of_flat_family_of_archSupportedAt`
(1,218), `…_localWeyl…` (1,062), `SmoothCuspRealizationAt.exists_mem_maximalCompactAt_whittakerCoefficient_
rightConv_diagOne_mul_ne_zero` (635), `exists_analyticOnNhd_sub_one_half_mul_weylIntertwiningIntegral_
isInducedSection_of_isArchKFinite_family` (574), and `fourierIntegral_mem_schwartzBruhat` (101, the
unrestricted Schwartz–Bruhat closure, which order E's `…_of_apply_eq_fourierChar_trace` had as its
premise).
