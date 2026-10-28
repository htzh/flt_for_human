# WORKORDER TL2 — the tails: the Laurent realisation, `ell` growth, the `evalFun` pushforward law, the correspondence's semilinearity

Scope: **four insertions**, one per node, into
`Place/LaurentSeriesModel.lean`, `Defs/AdelicIndex.lean`, `Place/EvalAtNorm.lean` and
`WeilExchange/GaloisRamification.lean`. Nothing else may be edited (no `spec/`, no
`spec/decl_markers.tsv`, no hub other than those four). Part of SET 6, [SET-6.md](SET-6.md) §1 (TL)
and §5.

## Nodes

| node | pin stem | silo | home | what to add |
|---|---|---:|---|---|
| `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries` | `S_AlgebraicCurve_Place_exists_ord_mul_eq_order_of_algHom_laurentSeries` | 146 | append to `Place/LaurentSeriesModel.lean` | 6 public + 1 private + the headline |
| `AlgebraicCurve.lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` | `S_AlgebraicCurve_lSpace_nsmul_succ_poleDivisor_le_sup_map_mulLeft_of_ell_eq` | 95 | append to `Defs/AdelicIndex.lean` | 1 public |
| `AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward` | `S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward` | 59 | append to `Place/EvalAtNorm.lean` | 1 private + 1 public |
| `AlgebraicCurve.SemilinearAut.correspondence_smul` | `S_AlgebraicCurve_SemilinearAut_correspondence_smul` | 16 | append to `WeilExchange/GaloisRamification.lean` | 1 public |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`; for each row read
`P2M/Sol/S_AlgebraicCurve_<stem>.lean` and `Theorems/Thm_AlgebraicCurve_<stem>.lean`.

## Per-node notes

### Laurent (`Place/LaurentSeriesModel.lean`)

Add `import FLTForHuman.AlgebraicCurve.Place.ValueDictionary` (for
`Place.exists_ord_mul_eq_order_of_hasRamBound`; acyclic — `ValueDictionary` imports only
`Defs/Place`, `Defs/PlacesOverDVR`, `Defs/HahnSeriesRamificationBound` and
`NumberTheory/ValuationSubring/Domination`) and, explicitly, `import
FLTForHuman.AlgebraicCurve.Defs.HahnSeriesRamificationBound` (for `HahnSeries.puiseuxRamEmb`,
`HasRamBound`, `ramScale_apply`). Transcribe the `S_` file's `CD` block: `hasRamBound_puiseuxRamEmb`,
`order_puiseuxRamEmb`, `laurentAlgebraMap_eq_C`, `hahnQAlgebraMap_eq_C`, `liftToHahn` (a `def`),
`order_liftToHahn`, the pin's **private** headline
(`_root_.AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`) and the public
wrapper at `AlgebraicCurve.Place.exists_ord_mul_eq_order_of_algHom_laurentSeries`.

- Take the **wrapper's** binders (`(K : Type*) [Field K]` explicit, `{F}` implicit), not the `S_`
  copy's section-variable spelling.
- **Drop `cd2_control`** (it computes an instance against `laurentBaseChange`/`coeffEmb` from
  `ModularCurve/XH/*`, which would invert the import direction; it is the pin's downstream control,
  not part of the headline) and the `#check`/`#print axioms` tail.

### `ell` growth (`Defs/AdelicIndex.lean`)

One declaration, the wrapper's statement, proof from the `S_` file. It imports only the SET 5
engine `mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor`, which is this module's own last
public theorem — import it (same module), do not restate. The proof is a `Finset`/`Submodule`
computation over `ell (N • D)`; `LSpace`/`ell` are the module's own abbreviations.

### `evalFun` pushforward (`Place/EvalAtNorm.lean`)

One private helper `zpow_finset_sum'` (7 lines) and the wrapper's headline
`AlgebraicCurve.Divisor.evalFun_algebraMap_pushforward` (37 lines). This module already imports
`Defs/PushPull` and `Place/ConstantFieldExtension`, so `Place.inertiaDeg_eq_one_of_isRational`,
`Place.evalAt_algebraMap_eq_evalAt_restrict`, `Place.mem_of_ord_nonneg`,
`Place.evalAt_ne_zero` and `Divisor.support_pushforward_subset` are all in scope. The proof is a
three-`Finset`-step product over the fibre; transcribe it.

### Semilinearity (`WeilExchange/GaloisRamification.lean`)

One declaration, the wrapper's statement, five lines: unfold `Divisor.correspondence` (its
`correspondence_apply` is `rfl`), rewrite with `SemilinearAut.pullbackAlong_smul` and
`SemilinearAut.pushforwardAlong_smul`. The latter is **in this module**; the pullback half is the
port's `Divisor.pullbackAlong_smul` in `Defs/Correspondence.lean` (the two-map `CrossIntertwines`
form — at `ψ = φ` it is the same proposition as the pin's `IntertwinesAlong`), which this module
already imports. `[HasPrincipalDivisors K F']` is a hypothesis of the statement.

## Wires

Each module appends the node's wrapper **and** `S_` file to its existing `spec-pin:` block:
`Theorems/Thm_AlgebraicCurve_<stem>.lean` and `P2M/Sol/S_AlgebraicCurve_<stem>.lean   -- comparable
copy`. No other wire changes.

## Rules

- Statements are the wrappers' character for character; proofs are the `S_` files', adapted to
  mathlib `v4.34.0` and the port's names. If a proof needs a `private` port declaration or one
  below the home, **stop and report** — do not promote, do not restate, do not edit a hub.
- Specific imports only (`import Mathlib` forbidden); no `set_option maxHeartbeats`; no
  `sorry`/`admit`/`axiom`; no commit.
- Edit loop from `lean/`: `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
  FLTForHuman/…/X.lean`; finished: `flock .lake/flt_build.lock timeout 110 lake build
  FLTForHuman.AlgebraicCurve.…X`. **No tree build, no dependents**; every command under two
  minutes, its own `timeout`; log under `lean/tmp/tl2-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** for each of the four
  modules; `#print axioms` on the four headlines → `[propext, Classical.choice, Quot.sound]`;
  **0 warnings** (read the edit loop's output; `lake build` alone hides linters);
  `dedup.py --module … --within` on each module afterwards and report the clusters.

## Report (one message)

Per module: build line and warnings, `check_port` summary, axioms line, and what was appended
(public/private counts). Note explicitly whether `cd2_control` was dropped, and any blocker or
deviation.
