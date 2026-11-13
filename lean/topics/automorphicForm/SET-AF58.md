# SET-AF58 — the cuspidality bound, and the global points' fundamental domain

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF57. The
fifty-eighth set of the column, and it takes the row AF57 readied (the cuspidality bound, the direct
consumer of that set's unfolding) together with the two rows of the story beside it — the global
points' fundamental domain and the Petersson self-pairing built on it.

**3 rows / 567 silo / ≈520 net** in **three new modules**, two orders, disjoint files.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn` | 210 | **4/4** | new `Adelic/CuspidalityBound` |
| **B** | `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | **5/8** | new `Adelic/PeterssonSelfPairing` |
| **C** | `exists_isFundamentalDomain_globalPoints_range` | 165 | 1/11 | new `Adelic/GlobalPointsDomain` |

## 0. The read

| figure | value |
|---|---:|
| `needed [F terminal]` | **673 / 288,239** |
| frontier F | 1,744 / 839,313 |
| ready rows, all namespaces | **32 / 6,634** |
| leaves, all namespaces | **183 / 46,068** |
| `AutomorphicForm` demand | 242 / 111,019 |

`--selfcheck` unchanged (MD-005's ten + MD-006's one, both open, neither cited here).

## 1. What the set says

- **A** — the cuspidality bound: a bound `|∑' β f(x⁻¹ n(β) y) − μ(box)⁻¹ ∫ f(x⁻¹ n(t) y)| ≤ ε` on the
  unipotent average bounds `‖∫ φ y f(x⁻¹y)‖` by `ε ∫ ‖φ‖` over the unipotent image of the box and the
  support of `f`. It is what SET-AF57's unfolding exists for: the unfolding's weight `w` is `1` on the
  support, the subtracted average dies against `φ` (cuspidality), and what remains is bounded pointwise.
  Its two premises are AF57's unfolding (in the tree since yesterday) and
  `AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`.
- **B** — the Petersson self-pairing of a continuous element on a fundamental domain is positive: the
  pairing's own toolkit (`smulInvariantMeasure_restrict`, `setIntegral_pos_of_isFundamentalDomain`, the
  determinant norm `dn` with its multiplicativity and its invariance under the global points, and the
  slab `slab F a b`), then the positivity. **14 public prelude rows**, so this is the set's API module.
- **C** — the global points have a fundamental domain: the dyadic determinant-norm slabs are measurable,
  `Γ_p`-invariant, pairwise disjoint and cover, and `IsFundamentalDomain` follows from the two
  restriction lemmas. Its premise is
  `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc` (`DetNormSlabFundamentalDomain`).

B and C are the pair: C's fundamental domain is the hypothesis B is stated under, and both rest on
`ideleNorm_det_globalPoints`. A is the chain row the previous set opened.

### 1.1 What the set does not cut

- The **content/height row** (333) and the **level-one obstruction** (229): the two remaining
  `AutomorphicForm` rows of independent subjects.
- The **`Kf`-smooth pair** (209 + 108 = 317), a coherent story left for a later set.
- `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` (30) and
  `rationalCentreUnipotent` (179), `SmoothCuspRealizationAt.centralChar_eq_…` (113): other subjects.
- `EisensteinGeneral.Piece` (890): definition-gated (six unported `Def_` modules).

## 2. The price

| figure | SET-AF58 |
|---|---:|
| raw `S_` lines | 567 |
| declaration lines | **489** |
| distinct declaration groups | 42 |
| duplicate copies inside the set | 0 |
| boilerplate dropped | 78 |
| **net new math lines** | **≈489** |
| `twin_scan` | `new` for all three |

`port_plan` run *after* the scaffolds reads "487 already in the port / net 2" — the FR-0184
tree-dependence, since the statement-only scaffolds are what it counts. The tree-independent figures
above are the ones to quote; the set's own net is the 489 declaration lines, and B's `haveI` fix and
each file's dropped `p2m`/attribute shims are inside the 78 boilerplate.

## 3. The homes and the manager's landed layer

| module | rows | lines | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `Adelic/CuspidalityBound.lean` (new) | A | **141** | 14 | 14 | **1 ok / 0 / 0** |
| `Adelic/PeterssonSelfPairing.lean` (new) | B | **175** | 17 | 14 | **17 ok / 0 / 0** |
| `Adelic/GlobalPointsDomain.lean` (new) | C | **109** | 10 | 9 | **1 ok / 0 / 0** |

All three elaborate at the low cap, all build (3,697 / 4,066 / 4,065 jobs, silent), all checker-green
before dispatch. The pin's label token `PetNe17` is rectified to the word namespace
`PeterssonSelfPairing`; `CuspidalUnfoldingWeight` is already words and is kept; C's helpers, written at
the pin's own namespace level, go into the word namespace `GlobalPointsDomain`. No token survives.

**Two scaffold findings**, both recorded (FR-0197):

1. **A `where`-bodied declaration must be stubbed at its `where`.** The pin writes the structure
   literals of C's restriction lemmas as `… μ where` followed by `nullMeasurableSet := …`,
   `ae_covers := …`, `aedisjoint := …`. Cutting at the first `:=` keeps `nullMeasurableSet` and *drops
   the other two fields*, which Lean 4.34 rejects with `Fields missing: ae_covers, aedisjoint` — a
   failure that looks like a statement drift and is not. The generator now cuts at ` where`.
2. **The `IsFundamentalDomain` field set differs**: `ae_covers`/`aedisjoint` at v4.34 are exactly the
   pin's, but they are only reachable through a `where` literal, not through a default — so the two
   lemmas' bodies are transcribed verbatim (`:= by sorry` in the scaffold) rather than split.

Also: `PeterssonSelfPairing` needs `open NumberField.TateGlobal` for `ideleNorm` (the pin opens it at
file level), and the pin's two `haveI`s in `instCountableΓ` are `have` at v4.34 (the style linter).

## 4. The orders and the gates

Two dispatches, disjoint files, concurrent:

- `tmp/af58/WORKORDER-AF58A-cuspidality-bound.md` — order A (210 silo, one module);
- `tmp/af58/WORKORDER-AF58B-petersson-and-domain.md` — order B (357 silo, two modules: B, then C).

The gates are the recipe's §6 for each module: no tree build; the edit loop at
`-DmaxHeartbeats=200000`; `lake build <module>` under `flock`/`timeout` per finished file; `check_port`
unchanged; `#print axioms` on the three headlines `[propext, Classical.choice, Quot.sound]`; zero
warnings; no `sorry`; no `set_option` beyond `autoImplicit false`; no silencer; `dedup`/`move_dead`
clean; one consumer zone per order with an executed composition per headline.

## 5. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 673 / 288,239 | **670 / 287,672** | 670 / 287,672 ✓ |
| frontier F | 1,744 / 839,313 | **1,747 / 839,880** | +567 ✓ |
| ready rows | 32 / 6,634 | **29 / 6,067** | — |
| `AutomorphicForm` demand | 242 / 111,019 | **239 / 110,452** | 239 / 110,452 ✓ |

The three rows left the ready shelf and **none entered**: the `AutomorphicForm` block is down to nine
rows, two of them the `Kf`-smooth pair (317) and one the content/height row (333).

## 6. The landing record

### 6.1 Order A — the cuspidality bound (landed 2026-11-13)

One row, one module, **103 written proof lines** (141 → 244), 14 `sorry`s → **0**, no imports and no
`set_option` added, statements untouched (every one of the 13 helper statements and the headline
verified byte-identical to the pin after whitespace normalisation).

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Adelic/CuspidalityBound.lean` | 141 → **244** | 14 | 14 → **0** | 3,697 jobs, 4.2 s, silent | **1 ok / 0 / 0** | clean |

`dedup --within` (all tiers): 0 clusters, 0 removable. `move_dead --dry-run`: 0 declarations, 0 lines —
all thirteen helpers are reachable from the headline. Consumer zone
`spec/AutomorphicFormSetAF58AConsumer.lean` (95 lines, two executed compositions: the bound at `ε = 0`,
and the zero-mass end for arbitrary `ε`): **0 errors**, silent.

**Heartbeats**: silent at 200,000 *and* at 10,000 — >20× headroom, no instance-inference pressure.
Three deviations, all prelude-driven: the pin's three term-bodied helpers are `:= by exact …` (the
frozen statement slot is `:= by`); the pin's `open CuspidalUnfoldingWeight in` prefix is not in the
frozen prelude, so the headline calls `CuspidalUnfoldingWeight.exists_weight` qualified (private names
do resolve qualified within the file at v4.34); and the pin's `haveI : OpensMeasurableSpace` is dropped
as redundant under the module's own `attribute [local instance] … glBorel` block — which is exactly
FR-0194/FR-0196's per-module instance policy, and the `haveI` would also trip the style linter.

### 6.2 Order B — the fundamental domain and the Petersson self-pairing (landed 2026-11-13)

Two rows, two modules, **146 written proof lines** (101 + 45), 23 `sorry`s → **0**, no imports and no
`set_option` added (the one duplicate `autoImplicit false` the generator carried from the pin's prelude
was removed at review), statements untouched.

| file | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Adelic/GlobalPointsDomain.lean` | 109 → **210** | 10 | 9 → **0** | 4,065 jobs, silent | **1 ok / 0 / 0** | clean |
| `Adelic/PeterssonSelfPairing.lean` | 175 → **220** | 19 | 14 → **0** | 4,066 jobs, 4.2 s, silent | **17 ok / 0 / 0** | clean |

`dedup --within` (all tiers): 0 clusters, 0 removable, on both. `move_dead --dry-run`: 0 declarations,
0 lines, on both. Consumer zone `spec/AutomorphicFormSetAF58BConsumer.lean` (92 lines, two executed
compositions: C's `D` spent on `IsFundamentalDomain.measure_eq_tsum`, B's headline on
`0 < (peterssonIntegral …).re`): **0 errors**, no `#check`, no `sorry`.

**FR-0197 paid off**: C's two restriction lemmas are the pin's `where` structure literals with all three
fields — the field set had not drifted, exactly as the friction entry says.

Five body-level deviations, all recorded by the worker: the pin's term-mode proofs written as `:= by …`;
`mem_setOf_eq`/`diff_*`/`mem_diff` → `Set.mem_ofPred_eq`/`Set.sdiff_*`/`Set.mem_sdiff` (v4.34
deprecations that would otherwise break the zero-warning gate); C's headline referring to the private
helpers as `GlobalPointsDomain.<name>` (it sits outside their namespace and no `open` may be added);
B's positivity row supplying the slab `SMulInvariantMeasure` **positionally** through `@` because the
pin's `haveI` trips the style linter and the instance binder is anonymous (a silencer is forbidden); and
B's four genuinely unused frozen binders referenced by `have _ := …` to keep `unusedVariables` silent.

**Cross-check worth noting**: the worker found that the port's existing
`AutomorphicForm/Adelic/PeterssonSlabPairing.lean` already carries port-shaped proofs of the same
`dn_*`/`slab` rows — so `PeterssonSelfPairing`'s prelude duplicates a ported block. That is the **pin's**
duplication (its file restates the toolkit), and the two modules were kept as landed;
`dedup.py`'s cross-module scan reports 0 clusters because the statements differ by the `dn`/`slab`
abbreviations' binder spelling. Registered as a dedup candidate rather than cut here.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf14.json
python3 ../tmp/af58/gen.py
cd .. && for m in CuspidalityBound PeterssonSelfPairing GlobalPointsDomain; do
  python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/$m.lean; done
```
