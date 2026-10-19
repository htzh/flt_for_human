# TOPIC — the finite-adelic integral as an Euler product

**Status: landed 2026-10-18.** The order is
[WORKORDER-E3-factorization.md](WORKORDER-E3-factorization.md). The landing record is §6.

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is `v4.34.0`.

**Method.** The six-step loop of
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3–§4 and
[porting-playbook.md](../../../porting-playbook.md) §2–§5.

**Companions.** [TOPIC-local-twisted-integral.md](TOPIC-local-twisted-integral.md) — the *local*
half of the same construction (the twisted local integral at a ramified and an unramified place,
landed); this note is its global counterpart, the passage from `∏ᶠ v, h v (x v)` to `∏' v, …`.
The definition layer is [../../PORTING-AutomorphicForm.md](../../PORTING-AutomorphicForm.md)
(`AdelicBox`, `integralFiniteAdeles`) and `NumberTheory/AdelicLevel/{IdealBall,Level}`.

## 1. The node

| | |
|---|---|
| pin statement | `Theorems/Thm_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean` (10 lines) |
| pin proof | `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean` (864 lines, 58 declarations) |
| statement | for local Haar measures `μ v`, local functions `h v` that are integrable, are `1` on `𝒪 v` outside a finite `S`, and whose normalized deviations from `1` are summable: the global product function is `ν`-integrable on the finite adèles and `(ν 𝒪)⁻¹ ∫ ∏ᶠ h v (x v) ∂ν = ∏' v, (μ v 𝒪 v)⁻¹ ∫ h v ∂(μ v)` |
| graph position | a leaf: the whole demand is the node (`frontier.py → needed 1 / 864 lines`) |
| fan-in | 0 in-cone, **13 whole-project** direct dependents |

**The mathematics.** The finite adèles are the restricted product of the completions at the
finite places, with the product measure `ν` (a Haar measure), and `∏ᶠ v, h v (x v)` is the
`finprod` of the local factors. The theorem says the integral of that product over the restricted
product is the infinite product of the normalized local integrals — the Euler product — and that
it is integrable, under exactly the convergence hypothesis that makes the infinite product
converge: the deviations of the local integrals from the normalized measure of the unit ball are
summable.

The proof is an exhaustion argument, and its engine is a measure-theoretic lemma worth
separating: **a measure on `G × Y` that is invariant under translation in `G` is a product
`μ × σ`** (`exists_eq_prod_of_forall_map_add_left`). With the finite set `S` fixed, the stratum
`{x | ∀ v ∉ S, x v ∈ 𝒪 v}` — a restricted product at the level `𝓟 (Sᶜ)` — is open and maps homeomorphically
onto `∏_{v ∈ S} K v × ∏_{v ∉ S} 𝒪 v`; pushing `ν` across that splitting gives the measure `rhoT`, and
the invariance lemma identifies `rhoT` with the product of the local `μ v`. Truncating at an
exhaustion of `S` and passing to the limit gives the statement.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod \
  --json build/eg_fact_advise.json
python3 port_plan.py --json build/eg_fact_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines | 864 |
| declaration lines / groups | 839 / 58 |
| duplicate copies | 0 |
| **substitutions** | **1** (`integralOffSet` ≡ `NumberField.TateGlobal.ShellSupport.integralOff`) |
| **net new math lines** | **839** |

The only substitution is a *definition*: the pin's `private def integralOffSet` is the port's
`ShellSupport.integralOff` (`{x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}`, verbatim). The
port uses the existing name rather than declaring a second copy, so the register sees one
declaration where the pin has one per file. `port_advise` flagged it as "suspect" because the
parser matches `def`s by type only; the two bodies were compared by hand.

**Not a dedup case.** No name of the 58 is re-proved anywhere else in the pin; the silo is
unique, self-contained, and its only consumer is the headline — the same shape as
WORKORDER-T5's GL₂ strong approximation, but larger.

## 3. The port structure

Five engines and one listed façade, cut along the pin's own sections:

| module | pin lines | decls | contents |
|---|---|---:|---|
| `EisensteinGeneral/Factorization/ProductMeasure.lean` | 26–98 | 1 | `exists_eq_prod_of_forall_map_add_left` — a `G`-translation-invariant measure on `G × Y` is `μ.prod σ` (73 lines) |
| `…/Factorization/Stratum.lean` | 99–283 | 32 | `countable_heightOneSpectrum`, `Stratum` (the `Πʳ` at level `𝓟 (Sᶜ)`), `incl`/`stratumSet`/`glue`, the splitting `split : Stratum ≃ₜ GT × YT`, its continuity and additivity |
| `…/Factorization/Measure.lean` | 287–438 | 10 | `measurableEmbedding_incl`, `rhoT`, the stratum integral identity, `rhoT_map_add_left`, `exists_rhoT_eq_prod`, the non-vanishing of `ν.real 𝒪` |
| `…/Factorization/Integrability.lean` | 442–600 | 7 | `integrable_of_forall_setIntegral_norm_le`, the exhaustion `exists_exhaustion` and `iUnion_stratumSet_eq_univ`, `finprod_incl_split_symm`, `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` |
| `…/Factorization/Tprod.lean` | 601–749 | 5 | `integrableOn_finprod_stratumSet`, the norm identity on strata, `measureReal_integers_le_integral_norm`, `norm_normalized_integral_sub_one_le`, `multipliable_normalized_integral` |
| `EisensteinGeneral/Factorization.lean` — **listed** | 750–864 | 1 | the headline |

**All six are listed**, unlike WORKORDER-T5's engine/façade split: every declaration is new,
unique to this subject, and has no other consumer, so there is no future importer that would
justify leaving 55 statements unchecked in tier-3 engines. Putting the pin `S_` file in `SOURCES`
and every module in `PORT_FILES` costs one `SOURCES` entry and buys a full statement diff — the
same argument WORKORDER-E2 used, at ten times the size.

## 4. Recorded negatives

* `integralOffSet` is **not** ported (see §2).
* The pin's `solution` (its proof alias at 842) is not ported; the façade states the wrapper's
  headline and uses the pin's proof body.
* No definition gate: the silo's only `Definitions/` import is `Def_NumberField_AdelicBox`, whose
  `integralFiniteAdeles` / `isOpen_…` / `isCompact_…` are already homed
  (`NumberTheory/AdelicLevel/IdealBall.lean`, `NumberTheory/AdelicBox.lean`).
* No promotion and no hub edit: nothing in the tree declares any of the 56 names, and the one
  existing declaration it uses is already public.

## 5. Reproduce

```bash
cd tools/deps
python3 port_advise.py --target EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod \
  --json build/eg_fact_advise.json
python3 port_plan.py --json build/eg_fact_advise.json
python3 frontier.py --target EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod \
  --include-leaves --top 5

cd ../lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/EisensteinGeneral/Factorization.lean
```

## 6. Landing record

| | |
|---|---|
| engines | `EisensteinGeneral/Factorization/{ProductMeasure,Stratum,Measure,Integrability,Tprod}.lean` — 113 / 269 / 220 / 224 / 209 lines, 1 / 32 / 10 / 8 / 5 declarations |
| façade | `EisensteinGeneral/Factorization.lean` — 145 lines, 1 headline |
| checker | **10,445 identical** (was 10,388), 0 mismatched / 0 missing, 10,781 checked — delta **+57**, every public declaration of the six modules |
| promoted-from-pin-private | 718 → 774 (the silo's machinery is `private` in the pin) |
| axioms | headline `[propext, Classical.choice, Quot.sound]` |
| build | tier-0 0 warnings on all six; tier-1 3,943 jobs |
| register | unchanged: all six modules are listed, so there is no tier-3 surface here |
| existing modules edited | none |

**The shape held, with two corrections at review.** The first checker run gave 3 mismatches, both
textual and both the manager's to fix: two statements had lost the pin's `AdelicBox.` prefix on
`integralFinteAdeles` (the port has that spelling as a port-only `@[reducible]` alias in
`NumberTheory/AdelicHaar/PlaceMeasure.lean:48`, which the module simply had not imported), and the
headline was being matched against the pin's *private engine copy* instead of the wrapper because
the wrapper was not listed before the `S_` file in `SOURCES`. The general lesson, now recorded in
the column note: **a listed `S_` file shadows its own wrapper for last-name matching unless the
wrapper comes first**, and **a pin spelling that a port module lacks may already exist as an alias
elsewhere — grep for the alias before declaring the name unspellable.**

The full record is [logs/eisenstein-factorization.md](../../../logs/eisenstein-factorization.md);
results in [WORKORDER-E3-factorization.md](WORKORDER-E3-factorization.md) §8.

The next row of this subject is
`EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` (185 pin
lines), which is **not** ready: it needs two unported `NumberField` rows (420 raw `S_` lines).
