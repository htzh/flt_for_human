# SET-AF57 — the cuspidal unfolding and the constant term's unipotent invariance

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF56. The
fifty-seventh set of the column, and the **deferral SET-AF56 recorded gets paid**: the cuspidal
unfolding (635), cut at that set's scaffold because its statement layer needed the adele ring's
instance layer, is now in the tree — the manager's definition-layer work (§3) is what unlocked it.
Its leaf neighbour comes with it, and the set readies its own consumer.

**2 rows / 779 silo / ≈700 net** in **two new modules**, one order.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **U** | `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn` | 635 | 1/1 | new `Adelic/CuspidalUnfolding` |
| **V** | `constantTerm_adelicBox_unipotentGL2_mul` *(leaf)* | 144 | **1/14** | new `Adelic/ConstantTermUnipotent` |

## 0. The read

Same command and marker set as SET-AF55/56:

| figure | value |
|---|---:|
| `needed [F terminal]` | **675 / 289,018** |
| `needed [literal]` | 690 / 293,278 |
| frontier F | 1,742 / 838,534 |
| ready rows, all namespaces | **32 / 7,059** |
| leaves, all namespaces | **184 / 46,068** |
| `AutomorphicForm` demand | 244 / 111,798 |
| withheld by the FR-0044 guard | 4 / 831 |

`--selfcheck` is unchanged (MD-005's ten + MD-006's one, both open, neither cited here).

## 1. What the set says

- **U** — the unfolding: for `φ` invariant under the rational unipotents `n(β)` and cuspidal for the
  `adelicBox`-conditioned Haar measure, `∫ φ y f(x⁻¹y)` equals the same integral with a
  partition-of-unity weight `w` and the unipotent average subtracted. Thirty `private` helpers
  (unipotent calculus, compactness of translates, the `boxAvg` family, the weighted `tsum`/integral
  exchanges, four integrability rows) and then the headline. Its statement's one premise,
  `AdeleRing.finite_setOf_algebraMap_mem_of_isCompact`, is ported.
- **V** — the constant term is invariant under the rational unipotent flow:
  `constantTerm (n(x₀) · g) = constantTerm g` for `φ` invariant under the global unipotents. A leaf
  with **14 project consumers**, and the row that states the invariance U's proof spends. Its
  statement names `adeleBorel` explicitly, so it needs no instance layer.

Together they are the constant-term half of the cuspidality route: V is the invariance, U the
unfolding that consumes it.

### 1.1 What the set does not cut

- The **content/height row** (333, `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq`),
  the **level-one obstruction** (229) and the **`K`/`f`-smooth factorization** (209): the remaining
  `AutomorphicForm` rows of other subjects, unchanged from SET-AF55 §1.
- `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` (890) — its six `Def_` modules
  are unported; a definition wave, not a proof wave.
- The rest of the shelf as SET-AF55 §1 lists it.

## 2. The price

| figure | SET-AF57 |
|---|---:|
| raw `S_` lines | 779 |
| declarations | 37 (U: 30 `private` helpers + headline; V: 5 public prelude rows + headline) |
| `port_plan` net new math lines | **≈700** (U's helpers are short; the lines are in the two headlines and the four integrability rows) |
| substitutes | none needed |
| `twin_scan` | `new` for both |

## 3. The manager's definition-layer work — what unlocked U

U's pin file opens with eight `private scoped instance`s (`Countable K`, `Countable (𝓞 K)`, the
second-countability of the finite and infinite adeles, of the adele ring and of `GL₂(𝔸)`). Two have
**no v4.34 counterpart** (`RestrictedProduct.secondCountableTopology` is gone) and the port does not
carry the adele ring's measurability as a global instance — it pins it **per module** as a
`local instance`, which is what `NumberTheory/AdelicBox.lean:350` and
`NumberTheory/AdelicModulus.lean:107` each do.

So the block is **dropped**, and the module carries instead:

```lean
variable (K : Type) [Field K] [NumberField K]

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
```

with `open scoped ProbabilityTheory` (for `μ[|s]`) and `open scoped NumberField.AdelicHaar` (for the
port's scoped second-countability instances). The pin's `regular_adelicAddHaar` and its
`attribute [local instance] regular_adelicAddHaar` are kept verbatim. **This is a prelude
substitution, recorded**, not a statement change: every statement is the pin's, and `check_port`
certifies the public surface. The same three-step check is now in
[../../logs/frictions.md](../../logs/frictions.md) FR-0194/FR-0196, so the next row that needs the
adele ring's instance layer pays minutes rather than a cut.

## 4. The homes and the manager's landed layer

| module | rows | lines | decls | `sorry` | `check_port` |
|---|---|---:|---:|---:|---|
| `Adelic/CuspidalUnfolding.lean` (new) | U | **274** | 31 | 31 | **1 ok / 0 / 0** (the 30 helpers are `private` in the pin) |
| `Adelic/ConstantTermUnipotent.lean` (new) | V | **110** | 6 | 6 | **6 ok / 0 / 0** (the pin states its five prelude rows publicly) |

Both elaborate at the low cap, both build (3,696 / 3,692 jobs, silent), both checker-green before
dispatch. V's pin label is a machine token and is rectified to the word namespace
`UnipotentInvariance` (the pin writes it as two `namespace` lines, so the rectification drops the
inner `Rows` level); U's `CuspidalUnfolding` is already a word namespace and is kept. The pin's `_impl`
staging row of V is dropped (it is the pin's own staging of the headline's proof).

## 5. The order and the gates

One dispatch: `tmp/af57/WORKORDER-AF57A-cuspidal-unfolding.md` (V first — 144 lines, high leverage —
then U's thirty helpers, then U's headline). The gates are the recipe's §6, written into the order:
no tree build; the edit loop at `-DmaxHeartbeats=200000`; `lake build <module>` under `flock`/`timeout`
per finished file; `check_port` unchanged; `#print axioms` on both headlines
`[propext, Classical.choice, Quot.sound]`; zero warnings; no `sorry`; no `set_option` beyond
`autoImplicit false`; no silencer; `dedup`/`move_dead` clean; one consumer zone with an executed
composition per headline.

## 6. The shelf effect, measured (statements in)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 675 / 289,018 | **673 / 288,239** | 673 / 288,239 ✓ |
| frontier F | 1,742 / 838,534 | **1,744 / 839,313** | +779 ✓ |
| ready rows | 32 / 7,059 | **32 / 6,634** | — |
| leaves | 184 / 46,068 | **183 / 46,068** | — |
| `AutomorphicForm` demand | 244 / 111,798 | **242 / 111,019** | 242 / 111,019 ✓ |

**One row readied — the set's own consumer**:
`AutomorphicForm.norm_integral_mul_le_mul_setIntegral_norm_of_isCuspidalFn` (210, two premises,
lev **4/4**), the cuspidality bound that U feeds. It is the natural next cut of this chain, and it
becomes the head of the `AutomorphicForm` block once this set lands.

## 7. The landing record (2026-11-13)

Two rows, two modules, **406 written proof lines** (35 + 371) over the 384 scaffold lines,
**37 `sorry`s → 0**, no imports added, no `set_option` added, and every statement, import, namespace,
`open`, `attribute`, `spec-pin:` line and docstring untouched — the worker verified all 31 U headers
and the 5 V prelude headers byte-identical to the pin (modulo `:=` vs `:= by`), and `check_port` reads
the dispatch figures unchanged.

| module | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Adelic/CuspidalUnfolding.lean` | 274 → **645** | 31 | 31 → **0** | 3,696 jobs, 5.8 s, silent | **1 ok / 0 / 0** | clean |
| `Adelic/ConstantTermUnipotent.lean` | 110 → **145** | 6 | 6 → **0** | 3,692 jobs, 3.2 s, silent | **6 ok / 0 / 0** | clean |
| | **384 → 790** | **37** | **37 → 0** | | **7 ok, 0 mismatch, 0 missing** | **2/2** |

`#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`; `#check` at both fully
qualified names resolves with the frozen statements. `dedup --within` (tiers `name,shape,body`): 0
clusters, 0 removable, on both. `move_dead --dry-run`: 0 on V; on U one declaration,
`regular_adelicAddHaar` (12 lines), which is a **tool false positive** — it is live through
`attribute [local instance] regular_adelicAddHaar` (line 75), a reference form `move_dead` does not
model, and the pin keeps it too; nothing was moved. Consumer zone
`spec/AutomorphicFormSetAF57AConsumer.lean` (137 lines, two executed compositions, no `#check`, no
`sorry`): V spent as the invariance it states (cuspidality moved along `n(x₀)`), U read off at its
`tsum`/integral shape. **0 errors**, silent.

**The dropped prelude block cost three body-local `have`s, in two proofs only** — the substitution
working as designed: `SecondCountableTopology G₂` (from the ported
`AdeleRing.secondCountableTopology_generalLinearGroup_finTwo`), `SFinite μG`, and
`IsFiniteMeasure (μA.restrict (adelicBox K))` appear where `stronglyMeasurable_boxAvg` and
`integral_mul_boxAvg_eq_zero` reach for the pin's derived instances. The pin's eight-instance block is
**not** re-added, and no attribute, statement or import changed.

**Heartbeats**: both files are silent at 200,000 and still at **10,000** — the whole set is far below
the gate, and there is no instance-inference defect anywhere in it.

Four further deviations, all body-local: three pin bodies that are term-mode get `exact` (the frozen
port signatures end `:= by`); two Prop-valued `haveI` → `have`; two `beta_reduce` no-ops dropped (the
unused-tactic linter). The remaining 28 U bodies and all V bodies are the pin's text verbatim.

## 8. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf13.json
python3 ../tmp/af57/gen.py
cd .. && python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/CuspidalUnfolding.lean
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/ConstantTermUnipotent.lean
```
