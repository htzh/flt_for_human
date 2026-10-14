# The valuation-subring / place-realisation prelude (tier 3, two modules)

**What this is.** The prelude that
[WORKORDER-P1](WORKORDER-P1-isPrimeOverValuationSubring.md) ported `private` inside
`AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean` is split by subject into two
**public, unwired** (tier-3) modules, with the wired headline module importing the
upper one:

| module | declarations | lines | content |
|---|---:|---:|---|
| `FLTForHuman/NumberTheory/ValuationSubring/Domination.lean` | **54** | 898 | the `Place`-free generic layer: domination, `centreOver`/`valuationSubringAtPrime`, the residue/constants/`CharP` block, integral closure, `RingHom.imagePrime` |
| `FLTForHuman/AlgebraicCurve/Place/ValueDictionary.lean` | **70** | 989 | the `AlgebraicCurve.Place.*` value/centre dictionary (`HasValueAt`, `compSubring`, `value`, `centre`, `compValuationSubring`) and the realisation core (`exists_unique_valueHom`, `exists_place_centre_comap_eq`) |
| `FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean` (tier 1) | **1** | 104 | the public headline, importing `ValueDictionary` |

`ValueDictionary` imports `Domination`; the dependency is one-way. Names and
namespaces are the pin's, so a consumer calls `ValuationSubring.centreOver`,
`AlgebraicCurve.Place.exists_unique_valueHom`, etc.

**Why split, and why two modules.** The prelude is generic valuation theory, not
`Place`-specific, and it is copied near-verbatim into a 19-file `ModularCurve` cluster
(table below). But it is not one subject: **70** of its 124 declarations are
`AlgebraicCurve.Place.*` theorems *about a `Place`* — bound by the pin's single
`variable (w : Place K F)` at line 151 — while **54** never mention `Place` at all.
Only the first stratum needs the `Place` API, so the second gets a `Place`-free
generic home.

They are two files, not one, because of the checker's tier mechanics: **a module is
wired as a whole**. The checker iterates `PORT_FILES` and diffs *every* public
declaration in a listed module (only `OWN_PROOFS` skips one); a module not listed is
diffed for none. Since the headline module must be listed, its public surface is
exactly the one headline. "Public but unwired" therefore requires A to be in a
module outside `PORT_FILES` — hence `ValueDictionary.lean`. The alternative
(merging A into the listed headline module) would make the checker diff 70 more
declarations (9743 → 9813); keeping A `private` there would hide it from the future
consumers, which is the point of the exercise.

**Why it exists.** A statement-level scan of all 29,511 pin `S_` files (the
checker's own parser, normalized statements) found the prelude copied into a 19-file
cluster, all in `ModularCurve`:

| pin `S_` file | shared decls | statements identical | bodies identical |
|---|---:|---:|---:|
| `ModularCurve_CharPModel_FibreModel_spPlace_surjective` (4,118 ln) | 120 | 120 | 111 |
| `ModularCurve_CharPModel_exists_unique_valueHom` | 106 | 106 | 103 |
| `ModularCurve_CharPModel_FibreModel_spPlace_d7_dictZero` (`_of_prime`) | 68 ea | 68 | 64 |
| `ModularCurve_CharPModel_chart_dichotomy_jBar` | 65 | 65 | 62 |
| `ModularCurve_CharPModel_FibreModel_spPlace_d0_jN` (`_pole`) | 55 ea | 55 | 52 |
| `ModularCurve_exists_ord_sub_pos_of_integral_affineBaseFin` / `…_sub_mem_nonunits_…affineBaseInf` | 49 ea | 49 | 46 |
| `spPlace_d0_j` (30), `spPlace_d0_j_pole` (22), `place_eq_of_forall_infChart_mem_nonunits_iff` (18), `spPlace_d7_dictInfty` (`_of_level`) (15 ea), `isDedekindDomain_integralClosure_adjoin_jGeomGen_of_separable` (7), 4 more at 2 | | | |

Those files are on the **Mazur / Frey level-lowering branch**, *not* in the
Deligne–Serre cone: porting them separately would re-prove ~8,367 lines of the
prelude. It is therefore written once, public, and unwired.

## To reuse (do not re-prove)

```lean
import FLTForHuman.AlgebraicCurve.Place.ValueDictionary   -- A, and (transitively) B
import FLTForHuman.NumberTheory.ValuationSubring.Domination -- B alone, if no Place is involved
```

Then grep `spec/UNWIRED-PUBLIC.md` for the mathematics you want; each row gives the
port name and the pin original to read for the signature. Every declaration the
ModularCurve cluster shares is present — in particular
`AlgebraicCurve.Place.exists_place_centre_comap_eq` (144 ln, the mathematical core),
`exists_sub_constants_mem` (94), `algebraMap_bijective_of_isIntegral_of_isAlgClosed`
(41), `ValuationSubring.isPrincipalIdealRing_of_dedekind_le`, the
`centreOver`/`centreHeightOneSpectrum` block, and the `HasValueAt` dictionary.

**Do not make a private copy and do not re-derive.** If a declaration is missing,
add it to A or B (publicly, with its `-- pin:` comment), not to the consumer. Every
declaration in both modules is public by design, precisely so that a consumer never
needs a visibility switch (which would edit the module and trigger a build wave).

## To wire (only if a consumer's statement is diffed)

Add the module to `PORT_FILES` and the pin `S_` file to `SOURCES` — both appended
last in `spec/check_flt_statements.py` — run
`python3 spec/check_flt_statements.py`, and reconcile the `identical` delta against
the new public surface (expect roughly +70 for A and +54 for B, all
promoted-from-pin-private). Then re-run `tools/deps/unwired_register.py` (from the
repo root) to drop the module's rows from `spec/UNWIRED-PUBLIC.md`. Do not wire a
module merely to "check" it — that is what tier 3 avoids.

## Prices (measured 2026-10-14)

* split: 124 declarations / ~1,887 lines public across A + B; the headline module
  reduced to its one declaration; `build_ladder.py --edit` on either new module = a
  leaf (**0 dependents**), ≈21 s to re-elaborate;
* checker **unchanged** at `9743 identical (671 promoted, 83 renamed), 0 mismatched,
  0 missing, 38 own-proof exempted (9781 checked)` — the prelude is tier 3;
* if both were wired, delta ≈ **+124** (9743 → ≈9867);
* payoff: ~**8,367** prelude-copy lines removable across the 19 consumers; the whole
  20-file cluster is 24,388 declaration lines, 15,977 duplicate, net new 6,295 with
  the sharing.

## Known tool caveat

The checker's `DECL_RE` admits only `private`/`noncomputable` modifiers, so the three
`scoped instance`s (`AlgebraicCurve.Place.centre_isPrime`, `…centre_isMaximal`,
`ValuationSubring.centreOver_isPrime`) are invisible to `raw_declarations`: the
register counts 121 of the 124 (A 68/70, B 53/54) and, if a module were wired, those
three would not be statement-diffed. They are present, public and pinned in the
modules. Fixing it means teaching the tracked checker to see `scoped` (and re-running
its selftest), which would change the global checked surface; it is a deliberate
separate pass.

## Provenance

Pin `anthropics/fermats-last-theorem@aa2d8b3`:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean>
(the whole file, 1,886 lines). The headline wrapper:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean>.
Checklists: `tools/deps/build/vs_core_split_A.tsv` (70), `vs_core_split_B.tsv` (54).
Measurement artifacts: `tools/deps/build/vs_stmt_scan.txt`, `promo_plan.txt`.
