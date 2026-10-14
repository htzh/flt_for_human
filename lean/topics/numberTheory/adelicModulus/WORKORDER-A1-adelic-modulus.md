# WORKORDER-A1 — the adelic modulus engines (tier 3)

**Status: landed 2026-10-13** — results in §11.

Read [TOPIC-adelic-modulus.md](TOPIC-adelic-modulus.md) first; §1 carries the mathematics,
§2–§4 the measurement and the block split, §5 the port structure. This order is the two
engine modules and nothing else.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. Scope

Write **two tier-3 engine modules**:

| module | pin source | new decls | net new |
|---|---|---:|---:|
| `FLTForHuman/NumberTheory/AdelicHaar/AdelicModulus.lean` | `P2M/Sol/S_NumberField_AdeleRing_distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm.lean` | 50 | 822 |
| `FLTForHuman/NumberTheory/AdelicHaar/ArchModulus.lean` | `P2M/Sol/S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean` | 8 | 93 |

**Explicitly not this order.** The tier-1 façade, `SOURCES`/`PORT_FILES` wiring,
`spec/UNWIRED-PUBLIC.md`, `spec/check_flt_statements.py`, the product-formula chain
(WORKORDER-A2), and every pin section listed in §2 as already ported. No promotion, no edit
to any existing module.

## 2. What is already in the port and must be imported, never re-transcribed

`FLTForHuman/NumberTheory/AdelicHaar/PlaceMeasure.lean` (622 lines, tier 3) holds, from the
Bruhat-transversal trio:

* the whole `M4aS4` place-measure block: `placeBorel`, `placeMeasureReal`,
  `placeMeasureComplex`, `placeMeasure` and their `_image_mul` lemmas, `archMeasure`,
  `image_mul_pi`, `archMeasure_image_mul_pi`, `placeMeasure_pos_closedBall`,
  `placeMeasure_closedBall_lt_top`, `infMS`, `infBorelSpace`, `finBorel`, `finBorelSpace`,
  `adeleMS`, `adeleBorelSpaceProd`, `secondCountable_infiniteAdeles`,
  `secondCountable_adeleRing`, `zhatCompacts`, `finMeasure`, `infMeasure`, `adelicMeasure`,
  `refSet`, `isCompact_refSet`, `interior_refSet_nonempty`, `adelicMeasure_refSet_ne_top`,
  `adelicMeasure_refSet_ne_zero`, `finMeasure_zhat`, `finiteMeasure_zhat`, …
* `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`
  (line 537) and `…_of_snd_eq_one_impl` (line 610) — the archimedean, trivial-finite-part
  premise.

`FLTForHuman/NumberTheory/AdelicLevel/Countability.lean` holds the `NumberField.AdelicCountability`
block (`isCountablyGenerated_uniformity_of_valued`, `secondCountableTopology_restrictedProduct`).
`FLTForHuman/NumberTheory/AdelicBox.lean` holds `AdelicBox.integralFiniteAdeles` and its
openness/compactness/non-emptiness. `FLTForHuman/LinearAlgebra/Countable.lean` holds the
`Def_Mathlib_LinearAlgebra_Countable` block.

`port_advise` reports 33 of the headline's 90 declarations and 20 of the archimedean
sibling's 28 as already in the port. **The substitution table's one suspect row is wrong**:
`placeModulus → NumberField.TateGlobal.ideleNorm` is a type-only `def` artifact. The port's
`ideleNorm` is `((distribHaarChar (AdeleRing (𝓞 F) F) x : ℝ≥0) : ℝ)`
(`NumberField/TateGlobal/Defs.lean:41`); `placeModulus` is the explicit product. **Define
`placeModulus`; do not substitute it.** The genuine relative to cross-reference in a
comment is `NumberField.TateGlobal.FujisakiC3.normQ`
(`NumberField/TateGlobal/FujisakiC3.lean:70`), the same product on the shell coordinates
`Q (F := F) S`.

**`Def_NumberField_AdelicHeight` / `NumberTheory/AdelicHeight.lean` is used — import it.**
This order was first written on the false premise that the pin's proof uses no declaration
of that node; the pin's `norm_finComp_eventually_eq_one` uses
`norm_le_one_of_mem_adicCompletionIntegers` at its lines 51 and 53, and that lemma is
`Def_NumberField_AdelicHeight.lean:163`. The node is **already homed whole** by the manager at
`FLTForHuman/NumberTheory/AdelicHeight.lean` (tier 1, checker +27; see the topic §3), so
`AdelicModulus.lean` imports it:
`import FLTForHuman.NumberTheory.AdelicHeight`, with `open NumberField.AdelicHeight`. Do not
re-derive the lemma `private` and do not home the node again.

## 3. `AdelicModulus.lean` — the transcription

Pin section spine (all line numbers in the headline's `S_` file):

| pin lines | namespace | action |
|---|---|---|
| 14–72 | `P6B.JE2aFlat` | **transcribe** `placeModulus` (27), `finComp_mul_finComp_inv` (33), `finComp_ne_zero` (39), `norm_finComp_eventually_eq_one` (46), `hasFiniteMulSupport_norm_finComp` (64) |
| 74–447 | `P6B.JE2aHMod` | **transcribe** `zhatAddSubgroup` (86) … `card_zhat_quot_mul_finprod_norm` (431) — 29 new declarations |
| 449–585 | `NumberField.AdelicCountability` | **skip** — in `AdelicLevel/Countability.lean`; import it |
| 587–1101 | `M4aS4` (first block) | **skip** — in `PlaceMeasure.lean`; import it |
| 1011–1101 | `M4aS4` (second block) | **transcribe** `HasTransversal` (1017), `measurableSet_smul_zhat` (1026), `finMeasure_smul_zhat` (1031), `distribHaarChar_of_fst_eq_one` (1052) |
| 1103–1211 | `P6B.JE2aHMod` | **transcribe** `coe_ySmulZhat_eq_smul` (1122), `hasTransversal` (1129) |
| 1213–1349 | `P6B.JE2aHMod` | **transcribe** `finUnit` (1229) … `distribHaarChar_eq_placeModulus` (1329) |
| 1352–1362 | — | **do not transcribe** `solution`; the façade owns the wrapped headline |

The pin's second `M4aS4` block re-opens a namespace `PlaceMeasure.lean` already declares
in; that is legal in Lean and the port keeps the namespace. The block's
`attribute [local instance] placeBorel infMS finBorel adeleMS` line is **file-local** and
must be re-established at the top of that section (the port's `PlaceMeasure.lean` uses the
same idiom).

The archimedean, trivial-finite-part half is `distribHaarChar_eq_prod_norm_pow_mult_of_snd_eq_one`
from `PlaceMeasure.lean`; `distribHaarChar_eq_placeModulus` consumes it and
`distribHaarChar_finUnit`.

## 4. `ArchModulus.lean` — the transcription

Pin `S_NumberField_InfiniteAdeleRing_distribHaarChar_eq_prod_norm_pow_mult.lean`, namespace
`ArchModS44`:

| pin lines | action |
|---|---|
| 20–323 | **skip** — `map_mul_left_volume_real` … `sigmaFinite_infMeasure` are statement-identical to `M4aS4` declarations in `PlaceMeasure.lean`; import and qualify them (the skip runs to 323, not 316: `isAddHaarMeasure_infMeasure` and `sigmaFinite_infMeasure` at 318/321 are `M4aS4`'s and are activated by `open M4aS4`) |
| 326–375 | **transcribe** `refBox` (326), `isCompact_refBox` (331), `interior_refBox_nonempty` (335), `infMeasure_refBox_ne_top` (348), `infMeasure_refBox_ne_zero` (355), `arch_unit_ne_zero` (367) |
| 375–411 | **transcribe** `distribHaarChar_infiniteAdeleRing` (375) |
| 413–418 | **do not transcribe** `solution`; the façade owns the wrapped headline |

The skipped block's names are pin-`ArchModS44` names mapping onto the port's `M4aS4`
names; use the `M4aS4` qualification in proofs. `ArchModS44.refBox` is genuinely new.

## 5. The engine's interface (the manager's façade will call these)

* `M4aS4`/`P6B.JE2aFlat`/`P6B.JE2aHMod` declarations: **public, at the pin names**.
* `P6B.JE2aHMod.distribHaarChar_eq_placeModulus`: public, statement as the pin, with its
  `hT` argument.
* `P6B.JE2aHMod.hasTransversal (F)`: public — the manager's façade proves the headline by
  `P6B.JE2aHMod.distribHaarChar_eq_placeModulus (P6B.JE2aHMod.hasTransversal F) a`.
* `ArchModS44.distribHaarChar_infiniteAdeleRing`: public — the façade's archimedean
  headline is `ArchModS44.distribHaarChar_infiniteAdeleRing a`.

## 6. Transcription rules

* Keep the pin's namespaces (`P6B`, `P6B.JE2aFlat`, `P6B.JE2aHMod`, `M4aS4`, `ArchModS44`),
  declaration names and statements **verbatim**. Drop the outer
  `P2MW.S_…` namespace and every `p2m_*` line; keep `set_option autoImplicit false`,
  `noncomputable section` and the pin's `open` lines (minus any that named a dropped
  import).
* No declaration in either pin file is `private`; everything stays public.
* Every transcribed declaration carries, immediately above it (above any `@[...]`), a
  provenance comment `-- pin: <name> (<S_ basename>:<line>)`. `tools/deps/unwired_register.py`
  reads it; a missing comment shows as `—` and is a defect.
* Replace the pin's bare `import Mathlib` with the specific imports actually used.

## 7. Route, mathlib map, and stop conditions

* **Statements are the pin's**; a documented `v4.34.0` drift is the only permitted
  difference. Proofs are adapted freely. **If a proof needs a statement to change, stop and
  report.**
* Expected drift surface: `MeasureTheory.Measure.addHaarScalarFactor` /
  `Measure.Haar.Unique` API names, `TopologicalSpace.PositiveCompacts`,
  `MeasureTheory.Measure.IsAddHaarMeasure` instance names, `Finset`/`Finsupp` support
  lemmas on `HeightOneSpectrum`, `Ideal.absNorm` and `Ideal` quotient arithmetic,
  `Set.Finite`/`Filter.eventually_cofinite`, `Units` coercion lemmas on
  `InfiniteAdeleRing`/`FiniteAdeleRing` (the non-reducible `def` head loses instances when
  unfolded — see `FujisakiC3.lean`'s `continuous_normQ` adaptation), and `finprod` API.
* **No new helpers beyond the pin's.** If a proof needs glue the pin does not have,
  re-derive it `private` in the same module and report it. **No promotion and no edit to any
  existing module.** If you believe a promotion is genuinely required, **stop and report**
  the declaration, host and `tools/deps/build_ladder.py --edit` price — the manager decides.
* **Stop and report** if a `P6B`/`ArchModS44` block cannot be kept self-contained against
  `PlaceMeasure.lean` + `Countability.lean` + `AdelicBox.lean` + mathlib, or if re-opening
  `M4aS4` in a second module collides.

## 8. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with
> `flock` and bounded with `timeout`. Per wave, build only the wave's affected targets —
> **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the
> session's end, and only with the user's permission.

Concretely: iterate at the low cap until each module is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Build only these two modules
and their dependencies.

**Build-time blow-up protocol.** The named risk is
`card_zhat_quot_mul_finprod_norm` (pin 72 lines, measure- and ideal-heavy); also watch
`card_zhat_quot_eq_absNorm` and `hasTransversal` (100 lines). If one exceeds the low cap,
diagnose with `set_option diagnostics true` / `trace.Meta.synthInstance true` in a scratch
copy (never commit it), fix the inference, and re-run. Report the declaration and the fix.

## 9. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `AdelicModulus.lean` then `ArchModulus.lean` | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.NumberTheory.AdelicHaar.{AdelicModulus,ArchModulus}` | both green; record jobs and wall/user time |
| name parity against `port_advise` on the two pin files | 50 + 8 new names present once each; the 33 + 20 substituted names **absent** (imported); none invented |
| `placeModulus` | declared, not substituted by `ideleNorm` |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

Do **not** run `spec/check_flt_statements.py` and do **not** edit the register. No wiring
for this order: the engines are tier 3.

## 10. Report shape

1. The two module paths, final line counts, and the pin section → module map as built.
2. Declaration counts per module, public / `private`; confirm §5's four interface names.
3. Which pin declarations were skipped as already ported, and which `M4aS4`/`ArchModS44`
   names were qualified in proofs.
4. Tier-0 and tier-1 results, with wall/user/sys times and jobs.
5. Every build-time blow-up, the declaration, the diagnosis, and the fix.
6. Any statement that could not be transcribed verbatim, and why (stop condition).
7. Any helper re-derived `private`, and any promotion you stopped on.

## 11. Results as landed (2026-10-13)

| | |
|---|---|
| engine 1 | `FLTForHuman/NumberTheory/AdelicHaar/AdelicModulus.lean` — 825 lines, **57 public declarations, 0 `private`** |
| engine 2 | `FLTForHuman/NumberTheory/AdelicHaar/ArchModulus.lean` — 142 lines, **7 public, 0 `private`** |
| tier 0 | both exit 0, **0 warnings** at the 200,000 cap |
| tier 1 | `AdelicModulus` 3,454 jobs, wall 8.431 s / user 10.201 s / sys 3.316 s; `ArchModulus` 3,454 jobs, wall 5.385 s / user 3.491 s / sys 3.006 s |
| façade | `NumberTheory/AdelicModulus.lean` extended to all six headlines; checker **9575 → 9577 (+2)** |
| mutation | one token on `NumberField.InfiniteAdeleRing.distribHaarChar_eq_prod_norm_pow_mult` (`w.mult` → `w.mult + 1`) → exactly **1 mismatched** (9,576), reverted |
| axioms | both headlines `[propext, Classical.choice, Quot.sound]` |
| register | regenerated once the round froze: 81 → 84 modules, 1,987 → 2,060 public, all three engines' rows with pin originals |
| existing modules edited | **none** — no promotion, no hub wave |

**The manager's decision on the reported stop-condition-adjacent fact.** The worker correctly
found that my §2 was wrong: the pin **does** use one `Def_NumberField_AdelicHeight`
declaration, so it had re-derived `norm_le_one_of_mem_adicCompletionIntegers` `private`. Since
the node is homed at its pin name, the right answer is to import it, not duplicate it — the
private copy was deleted, `import FLTForHuman.NumberTheory.AdelicHeight` and
`open NumberField.AdelicHeight` added, and the engine re-verified. The engine now has no
`private` declaration at all.

**Two statement mismatches, both spelling, both found by the checker and fixed.** The two
A1 `Theorems/` wrappers are older than the A2 ones and spell names long
(`NumberField.AdeleRing (NumberField.RingOfIntegers F) F` for `AdeleRing (𝓞 F) F`) and leave
`distribHaarChar` unqualified. The façade first used the port's shorthand and the checker
reported **2 mismatched**. Mirroring the wrapper text verbatim cleared both. Recorded because
it is a general rule for this project: the statement authority is the wrapper's *text*, not
the port's idiom — do not reformat a wrapper statement into the port's spelling.

**Deliberately skipped.** The archimedean pin's `regular_infMeasure` (pin 361–364): in
`v4.34` `Regular (infMeasure F)` is found by instance search, and the pin's proof of it
carried a `set_option synthInstance.maxHeartbeats 640000` this order forbids. It is an
instance, not a statement, so its absence is invisible to consumers.

**Out-of-scope confirmation.** 32 of the headline's 33 substitution rows and all 20 of the
archimedean ones are absent from both engines; only `placeModulus` appears, and it is
declared, not substituted. No pin declaration outside the transcribed ranges was
re-transcribed (57/57 new present; 0/67 and 0/35 skipped-range declarations re-transcribed).
