# The finite-adelic integral as an Euler product — five engines, one headline, all listed

**Status: landed 2026-10-18.** Six new modules, green with 0 errors and 0 warnings:

| module | lines | declarations |
|---|---:|---:|
| `EisensteinGeneral/Factorization/ProductMeasure.lean` | 113 | 1 |
| `EisensteinGeneral/Factorization/Stratum.lean` | 269 | 32 |
| `EisensteinGeneral/Factorization/Measure.lean` | 220 | 10 |
| `EisensteinGeneral/Factorization/Integrability.lean` | 224 | 8 |
| `EisensteinGeneral/Factorization/Tprod.lean` | 209 | 5 |
| `EisensteinGeneral/Factorization.lean` — **listed façade** | 145 | 1 |

**57 public declarations, all statement-checked.** Checker **10,388 → 10,445 identical**, 0
mismatched / 0 missing (10,781 port declarations checked); 774 of the identical are now promoted
from pin-private (was 718) — this silo's machinery is `private` in the pin. `#print axioms` on
the headline is `[propext, Classical.choice, Quot.sound]`. No existing module was edited.

| | |
|---|---|
| headline | `EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod` |
| pin proof | `P2M/Sol/S_EisensteinGeneral_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean` (864 lines, 58 declarations) |
| statement authority | `Theorems/Thm_…_Factorization_integrable_finprod_and_inv_measure_mul_integral_eq_tprod.lean` (10 lines) |
| net new | **839 of 864** lines — 0 substitutions except one 3-line `def`, the column's second pure transcription |
| structure | five engines + one façade, **all six listed** (no tier-3 engine) |
| build | tier-0 0 warnings on all six (3.6–5.7 s); tier-1 chain 3,943 jobs |
| register | unchanged (136 modules / 4,134 public): every declaration here is tier 1 |

## 1. What the theorem says

For a number field `F`, a Haar measure `ν` on the finite adèles, local Haar measures `μ v` on the
completions, and local functions `h v` that are integrable and are `1` on the unit ball `𝒪 v`
outside a finite set `S`, with `∑_{v ∉ S} |(μ v 𝒪 v)⁻¹ ∫ ‖h v‖ − 1| < ∞`:

```
Integrable (fun x : FiniteAdeleRing (𝓞 F) F => ∏ᶠ v, h v (x v)) ν
  ∧ (ν.real (integralFiniteAdeles) : ℂ)⁻¹ * ∫ x, ∏ᶠ v, h v (x v) ∂ν
      = ∏' v, ((μ v).real (𝒪 v) : ℂ)⁻¹ * ∫ y, h v y ∂(μ v)
```

i.e. **the integral of the local factors over the restricted product is their Euler product**,
with the convergence hypothesis exactly the one that makes the infinite product converge.

## 2. The development

Five subjects, cut along the pin's own sections:

1. **`ProductMeasure.lean`** (pin 26–98) — `exists_eq_prod_of_forall_map_add_left`: a measure on
   `G × Y` invariant under translation in `G` is `μ.prod σ` for a finite `σ`. The engine of the
   whole argument, 73 lines, proved from Haar uniqueness.
2. **`Stratum.lean`** (pin 99–283) — the stratum `Stratum F T = Πʳ_v [K v, 𝒪 v]_[𝓟 (Tᶜ)]`, its
   open embedding `incl` into the finite adèles, `stratumSet = range incl`, the glueing
   `glue`/`splitFun`/`splitInv` and the homeomorphism `split : Stratum ≃ₜ (∏_{v∈T} K v) × (∏_{v∉T} 𝒪 v)`,
   with continuity and additivity. Plus the pin's two `scoped instance`s giving `Stratum` its
   Borel structure.
3. **`Measure.lean`** (pin 287–438) — `rhoT` (the push-forward of `ν` across `split`), the stratum
   integral identity and its integrability form, translation invariance of `rhoT` in the first
   coordinate, and `exists_rhoT_eq_prod`: `rhoT` **is** the product of the local `μ v` and a finite
   `σ`, with `ν (integralFiniteAdeles) = ∏_{v∈T} μ v (𝒪 v) · σ univ`.
4. **`Integrability.lean`** (pin 442–600) — `integrable_of_forall_setIntegral_norm_le` (a uniform
   bound on the truncated integrals gives integrability), the exhaustion of the places
   (`exists_exhaustion`, `iUnion_stratumSet_eq_univ`), the product splitting on a stratum, and the
   stratum form of the statement.
5. **`Tprod.lean`** (pin 601–749) — the norm identity on strata, `measureReal_integers_le_integral_norm`,
   `norm_normalized_integral_sub_one_le` and `multipliable_normalized_integral`: the summability
   hypothesis turns into multipliability of the normalized local integrals.
6. **façade** — the headline, stated from the wrapper and proved by the pin's 92-line body.

## 3. The shape: everything listed

The column's usual shape is a tier-3 engine plus a thin listed façade. This set is the opposite
extreme: **all six modules are in `PORT_FILES` and the pin `S_` file is in `SOURCES`**, so every
one of the 57 declarations is statement-diffed. The trade-off was made deliberately (the same
argument as WORKORDER-E2, at ten times the size):

* the silo is **new in its entirety** (0 substitutions, 1 alias) and **unique** in the pin — no
  name of it is re-proved anywhere else, so no future importer will ever justify a tier-3
  exemption;
* leaving 55 statements unchecked would mean the only thing verified about the analytic heart of
  the Godement–Eisenstein construction is its headline — the least informative choice available;
* the cost is one `SOURCES` entry and six `PORT_FILES` entries, and the checker's
  promoted-from-pin-private fallback carries the 56 private machinery rows (718 → 774).

The one declaration that is **not** new: the pin's `private def integralOffSet` is the port's
`NumberField.TateGlobal.ShellSupport.integralOff` (the same set; the pin even proves
`integralOffSet = stratumSet` by `rfl`). It is declared here as a **one-line alias**
`def integralOffSet S := NumberField.TateGlobal.ShellSupport.integralOff S` rather than dropped:
the pin's statement of `inv_measure_mul_setIntegral_integralOffSet_finprod_eq` (line 562) spells
`∫ x in integralOffSet F S, …`, and the checker compares statement *text*, so dropping the name
would have turned a correct port into a MISMATCH. The checker only compares a `def`'s *type*, so
the alias passes, no mathematics is duplicated, and the downstream `rfl` still closes.

## 4. Verification, and the two mismatches of the first run

The first checker run reported **3 mismatches**, both triaged and fixed by the manager (the
subagent does not run the checker):

1. and 2. `exists_rhoT_eq_prod`, `measureReal_box_ne_zero`: the pin writes
   `AdelicBox.integralFiniteAdeles (𝓞 F) F`, the port had written the bare name. The port **does**
   have the pin's spelling — a port-only `@[reducible] def integralFiniteAdeles` inside
   `namespace NumberField.AdelicBox` at `NumberTheory/AdelicHaar/PlaceMeasure.lean:48`, added by an
   earlier landing for exactly this pin name — it was simply not on this module's import path.
   Fixed by importing `PlaceMeasure` and restoring the pin's spelling in the two statements (and in
   the `hbox` local of the first proof, where `rw` needs the syntactic form).
3. The headline: matched against the pin's **private engine copy** (which inherits `F` from a
   section variable) instead of the **wrapper** (which spells `(F : Type) [Field F] [NumberField F]`).
   Fixed by listing the wrapper **before** the `S_` file in `SOURCES` — the ordering convention the
   earlier landings state ("the wrapper is the statement authority, the `S_` file follows").

| check | result |
|---|---|
| tier-0 all six modules | exit 0, **0 warnings** (3.6–5.7 s each) |
| tier-1 `flock … lake build FLTForHuman.EisensteinGeneral.Factorization` | green, 3,943 jobs |
| checker | **10,445 identical** (was 10,388), 0 mismatched / 0 missing, 10,781 checked: delta **+57** = every public declaration of the six modules |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` |
| register | unchanged — all six modules are tier 1 |
| `git status` | the six new modules, `spec/check_flt_statements.py`, the notes |

## 5. Proof adaptations (pin → v4.34.0), statements verbatim

1. `dif_pos` / `dif_neg` → `dite_eq_left` / `dite_eq_right` (pin 178, 184, 232, 234).
2. `Finset.prod_le_prod (h₀) (h)` → `Finset.prod_le_prod₀ (h₀) (h)` (pin 798): in `v4.34.0`
   `prod_le_prod` lost its `0 ≤` argument and needs `[MulLeftMono N]`, which `ℝ` does not have.
3. `open scoped RestrictedProduct ENNReal NNReal` kept: v4.34 makes `∞` and `ℝ≥0∞` scoped
   notations, so dropping the pin's line breaks parsing.
4. A file-level `set_option linter.style.haveILetI false` in each of the six modules (24 `haveI`
   sites, all load-bearing instances: `SigmaCompactSpace G`, `FiniteMeasure σ`, …). This is the
   port's established convention for that lint (267 other modules), but it is *file-level* where the
   column's preference is declaration-scoped — recorded as the set's one style residual.

## 6. Residuals

* The `set_option linter.style.haveILetI false` is file-level in six modules (24 `haveI` sites); a
  later cleanup could narrow it to the ~15 declarations that need it.
* The two anonymous `scoped instance`s in `Stratum.lean` (the pin's `private scoped instance` pair,
  pin 280/281) are public in the port but cannot carry a `-- pin:` marker (no name); they are the
  only declarations of the set the checker does not see.
* **The successor is not ready**: `EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq`
  (185 pin lines) needs two unported `NumberField` rows (420 raw `S_` lines).

## 7. Reproduce

```bash
cd lean
for m in ProductMeasure Stratum Measure Integrability Tprod; do
  timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/EisensteinGeneral/Factorization/$m.lean || break
done
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.EisensteinGeneral.Factorization
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10445 identical
python3 tools/deps/unwired_register.py --check               # current
```
