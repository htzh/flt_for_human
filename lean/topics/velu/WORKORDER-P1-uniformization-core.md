# P-SET-1 work order — the `PeriodPair` uniformization core

**Status: open, 2026-10-06.** The first set of the V5 `PeriodPair` port; the decision and
the measurements are in [TOPIC-V5-periodpair-uniformization.md](TOPIC-V5-periodpair-uniformization.md)
§2.1 and §7. Three new modules, ~2,179 raw pin lines, new-file-only. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.4 (dedup), §3.1–§3.2 (role,
layout), §3.5 (build ladder), §3.7 (order and boundary), §4 (faithfulness). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

## 1. Scope

Port three things:

1. **the dictionary** — `Definitions/Def_PeriodPair_Uniformization.lean` (144 lines,
   §3.2 below): the lattice-to-curve dictionary and the `IsUniformization` statement;
2. **`PeriodPair.discriminant_ne_zero`** (542) — the discriminant of `L.weierstrassCurve`
   is nonzero;
3. **`PeriodPair.isUniformization_toPoint`** (1,493) — `ℂ/Λ ≅ E(ℂ)` through the ℘-map:
   `toPoint` is additive, surjective, with kernel `L.lattice`.

`discriminant_ne_zero` and `isUniformization_toPoint` are the subject's two hubs (9 and 6
in-subject consumers, V5 §2.1), and this set is the head of the whole `PeriodPair` port.

**Not this set:** the `j`-line (`jLattice_ofTau`, `jLattice_surjective`,
`exists_variableChange_smul_weierstrassCurve_eq`), the isogeny/index arithmetic
(`exists_differentiable_toPoint_comp_eq_pointMapOfPushforward_toPoint`, the two
`exists_scale_lattice_…`, `exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`), the
`rationalHomSet` and torsion columns, and the field-descent nodes
(`exists_intermediateField_countable…`, `exists_algHom_functionField_baseChange…`,
`nonempty_functionField_algEquiv_of_variableChange`). A worker that reaches an unported
prerequisite outside this set **stops at the boundary and reports** rather than editing a
closed module or weakening a statement (playbook §3.7).

**One route freedom, taken:** `isUniformization_toPoint` is stated with
`h : L.DiscriminantNeZero`. The pin's own proof is parametric in `h` (its components are
`kw_toPoint_add h`, `kw_toPoint_surjective h`, `kw_toPoint_eq_zero_iff h`); only the pin's
internal packaging calls the theorem `discriminant_ne_zero`. Prove the public statement
from `h` directly and **do not** add a `discriminant_ne_zero` citation to its proof.
`discriminant_ne_zero` is in the set because its consumers need the unconditional
statement, not because `isUniformization_toPoint` needs it.

## 2. Module DAG, namespaces, checker wiring

```
FLTForHuman/Elliptic/PeriodPair/Basic.lean                 the dictionary        (new)
  ├─ FLTForHuman/Elliptic/PeriodPair/Discriminant.lean        discriminant_ne_zero  (new)
  └─ FLTForHuman/Elliptic/PeriodPair/Uniformization.lean      isUniformization_toPoint (new,
        imports Basic and Discriminant)
```

Namespaces: every declaration keeps the pin's name and namespace (`PeriodPair.…`,
`PeriodPair.DiscriminantNeZero.…`), so the checker's last-name match keeps working. Each
module header states its subject, the pin source with its raw URL, and what it assumes
from lower modules.

Checker wiring, at the two spec files only — never a library module:

- `spec/check_flt_statements.py`: append the three modules to `PORT_FILES` **last**, and
  these to `SOURCES` **last**, wrappers before their `S_` files:

  ```
      "Definitions/Def_PeriodPair_Uniformization.lean",
      "Theorems/Thm_PeriodPair_discriminant_ne_zero.lean",
      "P2M/Sol/S_PeriodPair_discriminant_ne_zero.lean",
      "Theorems/Thm_PeriodPair_isUniformization_toPoint.lean",
      "P2M/Sol/S_PeriodPair_isUniformization_toPoint.lean",
  ```

  The wrapper is the statement authority (playbook §4.1); the `S_` file carries the
  helper declarations the wrapper does not carry; the `Definitions/` entry gives the
  dictionary its by-name coverage.
- `spec/PeriodPairConsumer.lean` — **new** file (no `PeriodPair` consumer exists yet).
  Zones in §6.

### 2.1 The prefix-strip promotion path (checker)

Promotions are written at the prefix-stripped pin name and verified through a new
fallback in `check_flt_statements.py`. The pin's `private` declarations are additionally
indexed under their prefix-stripped last name (`kw_G_ofTau_eq` → `G_ofTau_eq`); after
every name lookup fails, the checker tries that index, still requiring the `kind` and the
normalised statement to match, counts the hit separately as `renamed`, and prints
`RENAMED  <port>  ->  <pin> (<source>)`. The strip is applied to the **pin** side only,
so a pin public name is never shadowed; `OWN_PROOFS` is still consulted first. The token
list starts minimal, `PIN_PREFIXES = ("kw",)`.

Concretely, in `check_flt_statements.py`: add `PIN_PREFIXES` and `strip_pin_prefix` after
`promoted_key`; add a `stripped_source: dict[str, list]` in `main()` and fill it in the
`SOURCES` loop when the declaration is `private` and `strip_pin_prefix(last)` is not
`None`; after the existing `hit = find(dotted_source…)` block in the main loop, add

```python
            hit = find(stripped_source.get(name), kind, stmt)
            if hit:
                ok += 1
                renamed += 1
                print(f"RENAMED  {rel}: {raw}  ->  {hit[3]} ({hit[2]})")
                continue
```

add `renamed = 0` to the counters, and add `{renamed} renamed` to the summary line.
(`stripped_source` entries are `(kind, stmt, rel, pin_raw)`.)

Measurements and the honesty argument:
[`../../../studies/pin-name-prefixes-and-the-checker.md`](../../../studies/pin-name-prefixes-and-the-checker.md)
§5–§6 (320 `kw_` private declarations → 248 stripped names, 3 with more than one
statement, 1 shadowed by a public name). Verify the change with a rename probe: name one
promoted helper at its stripped name, run the checker, expect a `RENAMED` row and no
`MISSING`, then keep it (it is the policy).

## 3. Source (pin)

Every path is relative to the pin root
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/>). Statements come
verbatim from the `Theorems/` wrappers and the `Definitions/` module; proofs come from the
`S_` files, adapted to mathlib `v4.34.0`.

### 3.1 The two headlines

```
Theorems/Thm_PeriodPair_discriminant_ne_zero.lean
  theorem PeriodPair.discriminant_ne_zero (L : PeriodPair) : L.DiscriminantNeZero

Theorems/Thm_PeriodPair_isUniformization_toPoint.lean
  theorem PeriodPair.isUniformization_toPoint (L : PeriodPair) (h : L.DiscriminantNeZero) :
    L.IsUniformization h
```

Spell the binders exactly as the wrappers, not as the `S_` files (playbook §4.1).

### 3.2 The dictionary — `Definitions/Def_PeriodPair_Uniformization.lean`

All 20 declarations, at the pin's names and in the pin's `PeriodPair` namespace:

| pin line | declaration |
|---|---|
| 13 | `def weierstrassCurve : WeierstrassCurve ℂ` (`a₄ = -g₂/4`, `a₆ = -g₃/4`) |
| 20–24 | `weierstrassCurve_a₁`, `…_a₂`, `…_a₃`, `…_a₄`, `…_a₆` (`@[simp]`) |
| 26 | `theorem weierstrassCurve_Δ` |
| 32 | `theorem weierstrassCurve_c₄` |
| 37 | `theorem equation_weierstrassP` |
| 48 | `def DiscriminantNeZero : Prop` |
| 51 | `theorem DiscriminantNeZero.weierstrassCurve_Δ_ne_zero` |
| 57 | `def toPoint (h) (z) : L.weierstrassCurve.toAffine.Point` |
| 63, 67, 70 | `toPoint_of_mem` (`@[simp]`), `toPoint_zero` (`@[simp]`), `toPoint_of_notMem` |
| 75 | `def IsUniformization (h) : Prop` (add + surjective + kernel) |
| 80 | `def jLattice : ℂ` |
| 82 | `theorem jLattice_eq_c₄_pow_three_div_Δ` |
| 90 | `def JSurjective : Prop` |
| 93 | `theorem linearIndependent_coe_upperHalfPlane_one` |
| 104 | `def ofTau (τ : ℍ) : PeriodPair` |
| 109, 110, 112 | `ofTau_ω₁` (`@[simp]`), `ofTau_ω₂` (`@[simp]`), `ofTau_lattice` (`@[simp]`) |
| 119 | `theorem scale_indep` |
| 126 | `def scale` (section variable `α : ℂˣ`) |
| 131, 132 | `scale_ω₁` (`@[simp]`), `scale_ω₂` (`@[simp]`) |
| 136 | `def sublatticeIndex (L L' : PeriodPair) : ℕ` |
| 139 | `abbrev sublatticeQuotient (L L' : PeriodPair)` |

The pin file is `import Mathlib` only. The port lists specific imports (never `import
Mathlib` in a library module).

### 3.3 `S_PeriodPair_discriminant_ne_zero.lean` (542)

Route: `E₄³ − E₆²` is a cusp form of weight 12 whose `q`-expansion has constant term `0`
and coefficient `1` a multiple of Δ's, hence `E₄³ − E₆² = c·Δ`; then `g₂`/`g₃` of
`ofTau τ`, `Δ(ofTau τ) ≠ 0`, and `discriminant_ne_zero` for a general `L` by rescaling.
The pin's helpers are `kw_*` (`kw_E4cube`, `kw_qExpansion_E4cube`, `kw_E4cube_ne_E6sq`,
`kw_G_ofTau_eq`, `kw_riemannZeta_six`, `kw_g₂_ofTau`, `G_scale`, `g₂_scale`, …).

### 3.4 `S_PeriodPair_isUniformization_toPoint.lean` (1,493)

Route, in the pin's own order:

- `kw_countable_lattice`, `kw_isPreconnected_compl_lattice`,
  `kw_compl_lattice_mem_nhdsNE_zero` — topology of `ℂ \ Λ`;
- `kw_weierstrassP_surjective` — surjectivity of ℘ by a Liouville/order argument;
- `kw_toPoint_surjective`, `kw_toPoint_eq_zero_iff` — the corresponding `toPoint` facts;
- `kw_elliptic_Liouville_zero` — the Liouville lemma for elliptic functions;
- `kw_addΦ_eq_zero`, `kw_weierstrassP_add_eq_addX`, `kw_derivWeierstrassP_add_eq_addY` —
  the addition theorem via the chord-tangent law (`Affine.addX`/`addY`/`slope`);
- `kw_toPoint_add_generic`, `kw_exists_generic_perturbation`, `kw_toPoint_add` — the
  group law for all `z w`, by a generic-perturbation countability argument;
- `kw_isUniformization` — the three conjuncts.

## 4. Deliverable

Three new modules, all `new-file-only` (no library module is edited):

1. **`FLTForHuman/Elliptic/PeriodPair/Basic.lean`** — the §3.2 dictionary. Public, at the
   pin's names. It may be mathlib-only; import specifically
   (`Mathlib.Analysis.SpecialFunctions.Elliptic.Weierstrass`,
   `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic`,
   `Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point`,
   `Mathlib.Analysis.Complex.UpperHalfPlane.Basic`,
   `Mathlib.LinearAlgebra.LinearIndependent.Basic`, and whatever the index/quotient needs).
2. **`FLTForHuman/Elliptic/PeriodPair/Discriminant.lean`** — the headline
   `PeriodPair.discriminant_ne_zero`; every helper is `private`.
3. **`FLTForHuman/Elliptic/PeriodPair/Uniformization.lean`** — the headline
   `PeriodPair.isUniformization_toPoint`; every helper is `private`. Imports `Basic` and
   `Discriminant`.

**Naming and promotion.** A helper another theory could need is **promoted public at the
prefix-stripped pin name** (`kw_g₂_ofTau` → `g₂_ofTau`); a helper local to its module
stays `private` and is named for content. A stripped-name promotion is verified through
the new checker fallback of §2.1, so its statement is still diffed against the pin's
original. Record the pin↔port mapping in the module header.

Worth promoting (the `j`-line set needs them again): `riemannZeta_six`, `G_ofTau_eq`,
`g₂_ofTau`, `g₃_ofTau`, `G_scale`, `g₂_scale`, `g₃_scale`, `scale_lattice`,
`scaleLatticeEquiv`, and the lattice-equality lemmas. Stay `private`: `mulLeftR`,
`mulLeftZ`, `im_div_ne_zero`, `span_neg_fst`, and the local `scale`/`discriminant`
scaffolding nothing outside the module needs.

Register the three modules in `PORT_FILES` and the §2 entries in `SOURCES` (append last,
wrappers before `S_` files), and add `spec/PeriodPairConsumer.lean`.

## 5. Route, with recorded negatives

- **mathlib has the whole Affine API the pin uses.** Verified in the port's mathlib
  `v4.34.0`: `WeierstrassCurve.Affine.addX`/`addY`/`negAddY`/`slope`
  (`AlgebraicGeometry/EllipticCurve/Affine/Formula.lean`),
  `Affine.Point.add_of_X_ne` and `AddCommGroup W.Point`
  (`…/Affine/Point.lean`), `equation_iff_nonsingular_of_Δ_ne_zero`
  (`…/Affine/Basic.lean`), and the ℘ API (`weierstrassP`, `weierstrassPExcept`,
  `derivWeierstrassP`, `derivWeierstrassP_sq`, `analyticOnNhd_weierstrassP`,
  `order_weierstrassP`, `meromorphic_weierstrassP`, `latticeBasis`). Do **not**
  re-derive any of it.
- **mathlib has no Riemann-surface theory, no Riemann existence/mapping and no
  uniformization theorem**, and none is needed: the pin's proof is ℘-analysis
  (Liouville, removable singularities, order) plus the chord-tangent law. The one piece
  of topology is the covering map in the *seam* node, which is **not in this set**.
- **Check the port before transcribing the `discriminant` argument.**
  `FLTForHuman/ModularForms/JqAnalyticModel.lean` already carries
  `E4_cube_div_discriminant_smul`, `qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`,
  `qExpansion_E4_eq_map_eisenstein4`; `ModularForms/Hauptmodul.lean` and
  `ModularForms/EisensteinSeries.lean` carry the level-one layer. Diff the pin's
  `kw_E4cube`/`kw_E6sq`/`kw_qExpansion_*` against these before writing anything; prefer
  importing the port's public statements over re-proving them (playbook §2.4).
- **Dedup with the WeightOne prelude.** `FLTForHuman/ModularForms/WeightOne/Defs/PeriodPair.lean`
  (`periodPairOfTau`, `smulPeriodPair`, `weierstrassP_smulPeriodPair`) is the pin's
  *per-package private* prelude, not `Def_PeriodPair_Uniformization`; the pin has both.
  Define the dictionary's `ofTau`/`scale` at the pin names **inside `Basic.lean`** (do not
  import the WeightOne module), and record the overlap; if the two are literally equal,
  state the equality once rather than copying.
- **Binder shapes.** `PeriodPair.scale` is the pin's `α : ℂˣ` section-variable form;
  the WeightOne `smulPeriodPair` is the `a : ℂ, ha : a ≠ 0` form. They are different
  statements — keep the pin's `scale` shape.
- **The pin's heartbeat bumps are dropped.** The `S_` files set `maxHeartbeats` up to
  25,600,000; the port's frozen cap is 4,000,000. If a declaration blows it, supply the
  explicit instance / restructure the proof; never raise the cap (playbook §6).

## 6. Verification

- `lake env lean` clean per module; `lake build` per module; then **one** wave
  `lake build` over the three modules, bounded and `flock`ed (§8).
- `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`; record the
  `identical` before → after delta against the baseline
  **`5809 identical (311 promoted), 0 mismatched, 0 missing, 36 own, 5845 checked`**
  (2026-10-06) and reconcile it against the new public surface. A mismatch is a bug.
- The checker's one-token mutation probe: mutate one token in a transcribed statement,
  expect exactly `N identical / 1 mismatched / 0 missing`, revert (playbook §4).
- `spec/PeriodPairConsumer.lean` exit 0. Zones must be real, executed cross-module
  compositions — no `#check`, no `sorry`; deleting any one module must make the file
  fail. Suggested:
  - the dictionary at a concrete lattice — `PeriodPair.ofTau ⟨Complex.I, by simp⟩`
    (or a `τ` from the ported `WeightOne` layer) with `weierstrassCurve_a₄`,
    `jLattice` and `sublatticeIndex`/`sublatticeQuotient` used in a composition;
  - `PeriodPair.discriminant_ne_zero` at the same `τ`, feeding
    `DiscriminantNeZero.weierstrassCurve_Δ_ne_zero`;
  - `PeriodPair.isUniformization_toPoint` with `h` discharged from
    `discriminant_ne_zero`, using one conjunct (e.g. additivity) to prove a concrete
    `toPoint` identity, plus a non-vacuity `example` for the kernel conjunct.
- `#print axioms` on `PeriodPair.discriminant_ne_zero` and
  `PeriodPair.isUniformization_toPoint`: `[propext, Classical.choice, Quot.sound]`; no
  `sorry`.
- `grep -c` of every declaration dropped as already-present or binder-only, with the
  reason, in the friction log.

## 7. Stop-early risks (stop and report, do not push)

- **Any pull toward `AlgebraicCurve.*`, `ModularCurve.*`, the place dictionary, or the
  field-descent nodes** — that is the boundary (§1). Stop and report.
- **A pin helper whose statement does not transcribe to `v4.34.0`** (binder changes,
  renamed mathlib lemmas in the ℘/Affine API): report the two statements rather than
  weakening or silently adjusting.
- **The addition theorem** (`kw_weierstrassP_add_eq_addX`): the one genuinely hard block.
  Scout `kw_elliptic_Liouville_zero` and the smallest `kw_add*` lemma in a
  `tmp/scratch*.lean` first and report the `lake env lean` time before writing the whole
  module.
- **Any `discriminant` block that turns out to need an unported modular-forms node**:
  stop and report — the set assumes the ported `ModularForms` layer suffices.

## 8. Build discipline (binding)

> `lake env lean <opts> <file>` is the edit loop, with `<opts>` =
> `-DmaxHeartbeats=4000000 -DautoImplicit=false`; `lake build <module>` when a file is
> done; **one** `lake build` per wave; the full build at the milestone. Bound every build
> (`timeout 60` / `90` / `300` / `180`), serialize every `lake build` with `flock` (the
> lock is `lean/.lake/flt_build.lock`, never `/tmp`), and time it. Never raise
> `maxHeartbeats`. Import specifically — never `import Mathlib` in a library module.
> Iterate in bounded blocks, not per declaration: a module checked once costs seconds on
> top of the fixed cone load; checked fifty times it costs hours.

Baseline commands (warm tree):

```bash
cd lean
timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <module>
python3 spec/check_flt_statements.py
flock .lake/flt_build.lock bash -c 'time lake build'
```

## 9. Close-out (fill on landing)

Records: written lines per module; checker `5809 → N` and the reconciliation; promoted
count; consumer exit and time; whole-tree build jobs and seconds; `#print axioms`;
friction findings; any statement whose binder spelling had to follow the wrapper rather
than the `S_` file.
