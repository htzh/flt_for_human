# P-1b work order — consolidate the `PeriodPair` lattice prelude

**Status: open, 2026-10-06.** A consolidation set, not new mathematics: the
lattice/scale/discriminant prelude that P-SET-1 landed in `Elliptic/PeriodPair/` is
already proved — twice — inside `ModularForms/WeightOne/`, once publicly and once as a
53-line `private` block. This set gives it one home and reduces the copies to derivations.
Statements do not change; the checker verdicts do not change except for deliberate
demotions. Method: [../../porting-playbook.md](../../porting-playbook.md) §2.4 (dedup
before coding), §3.1–§3.2, §5 (real mathematics is written once; fix text *and* binders),
§3.5, §4. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Supersedes nothing; P-SET-1
([WORKORDER-P1-uniformization-core.md](WORKORDER-P1-uniformization-core.md)) stays as
landed.

## 1. Scope

Eliminate the duplicate implementations of the `PeriodPair` lattice prelude. **No
statement changes, no new pin sources, no new mathematics.** The deliverable is one
public implementation plus derivations.

Out of scope: the dictionary itself (`Basic.lean`), the `Uniformization.lean` helpers
(they are complex analysis and have no WeightOne counterpart), and the `j`-line set.

## 2. The duplication, measured

Three copies of the `ofTau` construction:

| file | declaration | visibility |
|---|---|---|
| `ModularForms/WeightOne/Defs/PeriodPair.lean:29` | `periodPairOfTau` | public, root namespace |
| `ModularForms/WeightOne/FrickeFunction.lean:967` | `periodPairOfTau` (`WLight.WLightFriOrbit`) | `private` |
| `Elliptic/PeriodPair/Basic.lean:139` | `PeriodPair.ofTau` | public |

Two shapes of the same scale law and lattice invariance:

| `FrickeFunction.lean` private block, lines 196–248 | `Elliptic/PeriodPair/Discriminant.lean` public |
|---|---|
| `latticeEquivOfEq` | `latticeEquivOfEq` (private) |
| `latticeEquivOfEq_coe` | `scaleLatticeEquiv_apply` (private) |
| `G_of_lattice_eq` | `G_eq_of_lattice_eq` |
| `g₂_of_lattice_eq` / `g₃_of_lattice_eq` | `g₂_eq_of_lattice_eq` / `g₃_eq_of_lattice_eq` |
| `G_smulPeriodPair` / `g₂_smulPeriodPair` / `g₃_smulPeriodPair` | `G_scale` / `g₂_scale` / `g₃_scale` |
| `latticeDisc := L.g₂^3 - 27*L.g₃^2` | unnamed; inline in `discriminant_scale`, and equal to `L.weierstrassCurve.Δ` |
| `latticeDisc_smulPeriodPair` | `discriminant_scale` (private) |
| `latticeDisc_of_lattice_eq` | `discriminantNeZero_of_lattice_eq` (private) |
| `weierstrassP_of_lattice_eq` | *no counterpart — keep, do not delete* |

and at the prelude level:

| `WeightOne/Defs/PeriodPair.lean` | `Elliptic/PeriodPair/` |
|---|---|
| `smulPeriodPair (a : ℂ) (ha : a ≠ 0)` | `PeriodPair.scale (α : ℂˣ)` |
| `smulLatticeEquiv` | `scaleLatticeEquiv` |
| `mem_smulPeriodPair_lattice` | (from `scale_lattice`) |
| `weierstrassP_smulPeriodPair` | (no counterpart yet) |
| `periodPair_eq_of_ω` | keep — the bridging lemma |

Why the checker did not see it: the `private` copies are invisible, and the surviving
near-duplicates differ only in binder spelling (`{L L'}` vs section variables,
`smulPeriodPair a ha` vs `L.scale α`) — exactly the case playbook §5 says to fix in both
places.

## 3. Target module graph, namespaces, binder rules

```
Elliptic/PeriodPair/Basic.lean                    (P-SET-1, unchanged: the dictionary)
Elliptic/PeriodPair/Lattice.lean                  NEW — the single home
  ├─ Elliptic/PeriodPair/Discriminant.lean            imports Lattice; keeps the discriminant
  ├─ ModularForms/WeightOne/Defs/PeriodPair.lean      shim/aliases over Lattice
  └─ ModularForms/WeightOne/FrickeFunction.lean       drops its private block
```

Rules:

- **One proof per fact.** The scale law is proved once, for `L.scale α`; the
  `smulPeriodPair a ha` form is `L.scale ⟨a, ha⟩` and its law follows by rewriting
  (`periodPair_eq_of_ω` bridges the `ω₁`/`ω₂` fields; `PeriodPair.indep` is a `Prop`, so
  the structures are equal by `Subsingleton.elim` or `PeriodPair.ext`). Same for
  `G_smulPeriodPair` → `G_scale` and for the lattice-equality names.
- **Keep every pin name the port already declares.** The checker matches by last name, so
  the home declares the union of names (both `G_scale` and `G_smulPeriodPair`, etc.), each
  derived from the single implementation; nothing that is currently declared disappears
  from the public surface except the deletions listed in §4.
- **Namespaces.** The home is `namespace PeriodPair` (pin names). The WeightOne files keep
  their existing root-level/`WLight` names as `abbrev`/`def` aliases (`abbrev
  smulPeriodPair (a : ℂ) (ha : a ≠ 0) (L : PeriodPair) := L.scale ⟨a, ha⟩`), so their
  importers compile unchanged.
- **`weierstrassP_of_lattice_eq`** has no counterpart: move it to the home (public) or
  keep it `private` in `FrickeFunction.lean`. Record which.

## 4. Deliverable

1. **`FLTForHuman/Elliptic/PeriodPair/Lattice.lean`** (new) — imports `Basic.lean`. Carries
   the union of §2's declarations, one proof each, at the pin names. Its public surface is
   the union of `Defs/PeriodPair.lean`'s public names and `Discriminant.lean`'s public
   ones; internal helpers stay `private` with content names (`kw_` stripped via the §2.1
   checker path where a pin `kw_` name is involved).
2. **`Elliptic/PeriodPair/Discriminant.lean`** — imports `Lattice`; the lattice block of
   §2 moves out (or becomes one-line references), leaving the discriminant-specific
   development: `ofTau_latticeEquivProd_symm_apply`, `G_ofTau_eq`, `riemannZeta_six`,
   `g₂_ofTau`, `g₃_ofTau`, `eCubeSubESq_apply`, `E4cube_ne_E6sq`, `ofTau_discriminant_eq`,
   `ofTau_discriminantNeZero`, `discriminantNeZero*`, `discriminant_ne_zero`,
   `im_div_ne_zero`, `span_neg_fst`.
3. **`ModularForms/WeightOne/Defs/PeriodPair.lean`** — imports `Lattice`; its declarations
   become one-line aliases/derivations of the home's (same names, same statements), so its
   ~10 importers are untouched.
4. **`ModularForms/WeightOne/FrickeFunction.lean`** — delete the private block (lines
   196–248) and the private `periodPairOfTau` (line 967); rewrite the ~30 use sites to the
   home's names. `latticeDisc`'s consumer `frickePrefactor` (line 250) and everything below
   it must still compile.

Register `Lattice.lean` in `PORT_FILES` (append last, before `Discriminant.lean` if the
list is ordered) and add its pin sources to `SOURCES` only if it needs a new source; the
pin sources are already listed (P-SET-1's `Def_PeriodPair_Uniformization` plus the two
`S_` files, and the WeightOne `S_` file that backs `Defs/PeriodPair.lean` is already in
`SOURCES`). Do not duplicate a `SOURCES` entry.

## 5. Route, with recorded negatives

- `Defs/PeriodPair.lean` is at the **root namespace** (`periodPairOfTau`, `smulPeriodPair`,
  `smulLatticeEquiv`, …); `FrickeFunction.lean`'s private block is at the root namespace
  inside `section B3_fricke` (lines 191–248) except for the private `periodPairOfTau` at
  967, which is inside `WLight.WLightFriOrbit`. Confirm both before aliasing.
- The home must **not** import anything under `ModularForms/WeightOne/` — the direction is
  `WeightOne → Elliptic/PeriodPair`. If a proof currently lives in `Defs/PeriodPair.lean`
  and the home needs it, the proof **moves**, the old name stays as an alias.
- `Discriminant.lean`'s `scaleLatticeEquiv` is built from `scale_lattice` via
  `LinearEquiv.ofEq`; `smulLatticeEquiv` in `Defs/PeriodPair.lean` is built from the
  `mem_smulPeriodPair_lattice` membership. Pick the `scale`-side proof as the single one;
  the other side derives through `L.scale ⟨a, ha⟩ = smulPeriodPair a ha L`.
- `latticeDisc` should be related to the dictionary's `weierstrassCurve_Δ` (it equals
  `L.weierstrassCurve.Δ`); state the equality once and record where the pin's inline
  `g₂^3 - 27*g₃^2` spelling is kept (the checker's statement diff is textual).
- The pin's deprecated aliases (`if_pos`, `if_neg`, `zero_le'`, `mem_diff`) are already
  handled in the landed modules; do not disturb them.

## 6. Stop-early risks (stop and report, do not push)

- **A WeightOne importer that breaks because an alias changed qualification.** The alias
  must keep the *root-level* names; if a name cannot stay at the root, stop and report the
  importer.
- **A binder bridge that needs a statement change.** Derivations must keep the pin
  statement's text exactly; if `L.scale ⟨a, ha⟩` and `smulPeriodPair a ha L` cannot be
  related without changing a statement, stop and report the two statements.
- **A checker verdict move that is not explained by a demotion.** Any `mismatch` or
  `missing` is a bug, not a drift.

## 7. Verification

- `lake env lean` clean per edited file; `lake build` per module; one wave `lake build`;
  then the whole-tree `flock`ed build.
- `python3 spec/check_flt_statements.py` → `0 mismatched / 0 missing`. Baseline (P-SET-1
  landed): **`5853 identical (313 promoted, 4 renamed), 0 mismatched, 0 missing, 36 own,
  5889 checked`**. Reconcile every delta: a deleted duplicate is an expected −1; an alias
  is a new compared declaration.
- `spec/WeightOneConsumer.lean` and `spec/PeriodPairConsumer.lean` both exit 0.
- `#print axioms` on `PeriodPair.discriminant_ne_zero` and
  `PeriodPair.isUniformization_toPoint` unchanged: `[propext, Classical.choice, Quot.sound]`.
- Measure and record the cascade of the two edited WeightOne modules (`FrickeFunction.lean`
  has 8 library importers, `Defs/PeriodPair.lean` 10) with the build timer.
- `grep -c` of every declaration deleted as a duplicate, with the survivor's name, in the
  friction log.

## 8. Build discipline (binding)

> `lake env lean <opts> <file>` is the edit loop, with `<opts>` =
> `-DmaxHeartbeats=4000000 -DautoImplicit=false`; `lake build <module>` when a file is
> done; **one** `lake build` per wave; the full build at the milestone. Bound every build
> (`timeout 60` / `90` / `300`), serialize every `lake build` with `flock` (the lock is
> `lean/.lake/flt_build.lock`, never `/tmp`), and time it. Never raise `maxHeartbeats`.
> Import specifically — never `import Mathlib` in a library module.

## 9. Close-out (landed 2026-10-06)

`FLTForHuman/Elliptic/PeriodPair/Lattice.lean` (new, 260 lines, 30 public + 9
`private`); `Discriminant.lean` 326 → 248; `Defs/PeriodPair.lean` 98 → 23;
`FrickeFunction.lean` 2926 → 2869 (private block 196–248 and private
`periodPairOfTau` deleted, no use-site rewrite needed).

- **Deleted duplicates and survivors:** the full table is in
  [../../../logs/velu-port.md](../../../logs/velu-port.md) §P-1b. The
  `FrickeFunction` block's 12 declarations survive as the home's public
  `latticeDisc*`/`G_smulPeriodPair`/`g₂`/`g₃`/`weierstrassP_of_lattice_eq` names
  (`latticeEquivOfEq`/`_coe` stay `private`), and its private `periodPairOfTau` is
  the home's `PeriodPair.periodPairOfTau` = `ofTau`. `Discriminant.lean`'s
  scale/lattice block and the 11 root names of `Defs/PeriodPair.lean` move to the
  home (the latter re-exported by `export`).
- **Checker:** `5853 → 5864 identical (313 promoted, 4 renamed), 0 mismatched, 0
  missing, 36 own, 5889 → 5900 checked`. The **+11** is exactly the ten
  `FrickeFunction` promotions plus `discriminant_scale`; the moves net to zero and
  there is no public deletion.
- **Consumer exits:** `spec/PeriodPairConsumer.lean` 0 (4.1 s),
  `spec/WeightOneConsumer.lean` 0 (6.1 s). `#print axioms` on
  `PeriodPair.discriminant_ne_zero` and `PeriodPair.isUniformization_toPoint`:
  `[propext, Classical.choice, Quot.sound]`.
- **Builds:** wave whole-tree `flock .lake/flt_build.lock lake build` **9308 jobs,
  green, 5 m 00.5 s**; cached milestone **9308 jobs, 7.4 s**. Cascade: 34 modules /
  28,531 lines for `Defs/PeriodPair.lean` (13 direct importers) and 27 modules /
  21,730 lines for `FrickeFunction.lean` (8 direct importers).
- **Deliberate deviations:** (1) `Defs/PeriodPair.lean` is an `export` shim, not
  literal `def` aliases — the alias shape is `Ambiguous term` in any file that
  `open PeriodPair`s, while `export` re-uses the home's constants; (2)
  `discriminant_scale` is public in the home because `discriminantNeZero_scale_iff`
  stays in `Discriminant.lean` and consumes it across the module boundary; (3)
  `latticeEquivOfEq`/`_coe` stay `private` (internal helpers); (4) the pin's
  `⟨a, ha⟩` unit literal does not elaborate (`Units.mk0` is required). No binder
  bridge needed a statement change; nothing was stopped at.
