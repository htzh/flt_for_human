# The degree identity `deg (x)_∞ = [F : K(x)]` — four nodes, 1,204 pin lines, all landed

**Landed 2026-10-23, one set.** The theory is scoped in
[../topics/algebraicCurve/TOPIC-degree-finrank-adjoin.md](../topics/algebraicCurve/TOPIC-degree-finrank-adjoin.md)
(the mathematics, the four nodes, the reuse map, the order). This record covers the
port: two new modules, one shelf, one consumer zone.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (`git -C ~/proj/fermats-last-theorem
rev-parse HEAD` = `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`), port Lean `v4.34.0` /
mathlib `v4.34.0`.

## 1. The nodes

Every statement is transcribed verbatim from the pin's `Theorems/` wrapper; the proof is
adapted from the matching `P2M/Sol/S_*.lean`. `U` consumes `A`; `E` is `le_antisymm` of
`L` and `U`.

| id | declaration | pin `S_` | wrapper | port lines | home |
|---|---|---:|---:|---:|---|
| A | `AlgebraicCurve.Place.exists_forall_ord_eq` | 407 | 8 | 281 | new `AlgebraicCurve/Place/Approximation.lean` |
| L | `AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord` | 230 | 21 | 200 | new `AlgebraicCurve/Genus/DegreeIdentity.lean` |
| U | `AlgebraicCurve.Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord` | 546 | 21 | 516 | same module |
| E | `AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord` | 21 | 21 | 11 | same module |
| | **total** | **1,204** | 71 | **1,123 Lean lines** | 2 new modules |

The per-node port figures are each node's span in the landed file (`A` includes its eight
private helpers; `L`/`U` are one declaration each; `E` is its 11-line body); the module
totals — 330 and 793 — add headers, imports and namespace lines (49 + 66). The
topic note's pre-port estimate of ≈1,100 lines was accurate to 2 %.

Homes are the note's (new modules, appends to the legacy `PORT_FILES` modules would have
reopened 700–1,000-line files); the order executed was `A`, `L`, `U`, `E`.

## 2. Modules and their public declarations

### `FLTForHuman/AlgebraicCurve/Place/Approximation.lean` (new, 330 lines)

Public: `AlgebraicCurve.Place.exists_forall_ord_eq` only. Eight `private` helpers, at the
pin's names: `exists_ord_neg_and_ord_pos`, `adicValuation_lt_one_iff_ord_pos`,
`one_lt_adicValuation_iff_ord_neg`, `one_add_ne_zero_and_ord_eq_of_ord_neg`,
`ord_one_add_of_ord_pos`, `exists_ord_neg_forall_ord_pos`, `exists_indicator`,
`exists_forall_ord_eq_of_sep`. The pin has these in `namespace AlgebraicCurve.Place` as
`theorem`s and re-exports them with `p2m_export`; **no consumer outside the `S_` file
exists in either direction** (`grep` over the pin finds each name only in
`S_AlgebraicCurve_Place_exists_forall_ord_eq.lean`, and over the port only in this
module), so they are private here — the public surface the next theory imports is the
headline.

The mathematics: separate two places by an element integral at one and not the other,
turn the pair into an element negative at one and positive at the other, induce over `T`
with the `z ^ m` correction to get an element negative at `v` and positive at the rest of
`T`, bend it into an indicator `e` (`1` at `v`, `0` at the other places of `T`, to the
precision `B` that dominates every `n v - v.ord (t w) + 1`) by `z ^ k / (1 + z ^ k)`, and
sum `t v * e v` with `t v = π v ^ (n v)`: the `v`-term dominates the error at `v`, so the
sum has order exactly `n v` at every `v ∈ T`.

### `FLTForHuman/AlgebraicCurve/Genus/DegreeIdentity.lean` (new, 793 lines)

Public: the three headlines, at the wrappers' statements. **No private helper** — `L` and
`U` are transcribed as single proofs, as the pin has them, and everything they use is a
public premise of the port (`linearIndependent_pow_of_transcendental`,
`linearIndependent_pow_mul`, `ell_le_degree_add_ellZero`, `finiteDimensional_lSpace`,
`mem_lSpace_iff_ord`, `ell`, `Place.mem_toValuationSubring_of_isIntegral_adjoin`,
`Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`,
`Place.exists_forall_ord_eq`).

The mathematics: `L` takes a `K[x]`-integral `E`-basis `u` of `F`, bounds the `u i` at
the poles of `x` by a constant `c`, exhibits `n (m - c + 1)` independent elements of
`L(mD)` and runs Riemann's inequality against `m → ∞`. `U` counts residues: a lifted
`K`-basis of each `κ(v)` (`Fin v.deg`-indexed, regular on the whole support), an
indicator `c` and a `t v` from weak approximation give the `K(x)`-independent family
`z k * t v ^ (-(a + 1))` of cardinality `deg D`, which cannot exceed `[F : K(x)]`.

### `Reserve/AlgebraicCurve/Place/ApproximationDead.lean` (new, 52 lines)

One unreachable helper, `private` as in the pin: `Place.ord_coe_unit_eq_zero_of_le`. Its
only pin consumer is the `S_` file's own `exists_mem_and_not_mem`, which the port already
carries publicly in `Place/OrdCalculus.lean` with a different proof, so nothing reaches it
here. No `spec-pin:` wire (built, not diffed); a row in
[Reserve/README.md](../Reserve/README.md).

### `spec/DegreeIdentityConsumer.lean` (new, 81 lines)

The set's cross-module composition — see §7.

## 3. Build and verification

Built with `flock .lake/flt_build.lock timeout 100 lake build <Module>` from `lean/`; the
edit loop is `timeout 130 lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000 <file>`, and **every declaration of the four nodes elaborates at
that 200,000-heartbeat cap** — no heartbeat bump anywhere, scoped or not, although the
pin's `S_` files carry `set_option maxHeartbeats 3200000` (`L`) and `8000000` (`U`), both
above this project's 4,000,000 cap and therefore not transcribable as they stand. The
whole `DegreeIdentity` module elaborates in 12 s at the low cap.

| module | build jobs | module time | warnings from the module |
|---|---:|---:|---|
| `…Place.Approximation` | 2,533 | 3.3 s | 0 |
| `Reserve.…Place.ApproximationDead` | 2,534 | 2.6 s | 0 |
| `…Genus.DegreeIdentity` | 2,730 | 11 s | 0 |

The warning blocks in `DegreeIdentity`'s build log all name the pre-existing
`AlgebraicCurve/Genus/Stichtenoth.lean` (`linter.overlappingInstances` on eight
tower-shaped declarations there), replayed from the dependency; none names a module of
this set, and `Approximation`'s build log is empty.

**Checker** — `python3 spec/check_port.py --force <module>`, corpus `aa2d8b3`:

| module | verdict |
|---|---|
| `…/Place/Approximation.lean` | 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw |
| `…/Genus/DegreeIdentity.lean` | 3 ok, 0 mismatch, 0 missing, 0 own, 0 kw |

No `spec/decl_markers.tsv` row was needed: every public declaration is the pin's name at
the pin's statement. No module was added to `spec/old_check_stmts.py`.

Whole wired set after this set (`spec/check_port.py --changed`, everything else cached):
**4954 ok, 0 mismatch, 0 missing, 19 own, 0 kw over 219 modules**, 534 exempt
(`PORT_FILES`), corpus `aa2d8b3` — 4,950 ok / 217 modules before the set plus its four
declarations in two modules.

**Axioms** — `lean/tmp/AxiomsDegreeIdentity.lean` (a probe, not a module; the modules carry
no `#print`):

```
'AlgebraicCurve.Place.exists_forall_ord_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicCurve.Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
'AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `sorryAx`, no `set_option maxHeartbeats`.

## 4. Substitutions and deviations from the pin

1. **`L`'s inline independence proof — the two mandated substitutions.** The pin proves
   `LinearIndependent K (fun j : ℕ => xE ^ j)` inline (12 lines, through
   `Polynomial.basisMonomials` and `transcendental_iff_injective`) and then closes `hli`
   with a `simpa` over `linearIndependent_pow_mul`. The port writes
   `linearIndependent_pow_of_transcendental (K := K) (A := E) hxE_trans` (needing only the
   `Transcendental K xE` the pin already establishes) and keeps the `simpa only [show
   algebraMap E F xE = x from hxE_coe]`. Nothing else in `hli` changed.
2. **`A`'s separation and dictionary lemmas are imported, not re-proved.** The pin's
   `S_` file proves its own `exists_mem_and_not_mem`, `mem_iff_ord_nonneg'`,
   `not_mem_iff_ord_neg`, `mem_iff_adicValuation_le_one'` and `adicValuation_eq_exp_neg_ord`.
   The port carries these publicly — `Place.exists_mem_and_not_mem`
   (`Place/OrdCalculus.lean`), and `Place.mem_iff_ord_nonneg` (`Defs/PushPull.lean`),
   `Place.not_mem_iff_ord_neg` (`Place/OrdCalculus.lean`),
   `Place.mem_iff_adicValuation_le_one` (`Defs/Place.lean`),
   `Place.adicValuation_eq_exp_neg_ord` (`Defs/Repartitions.lean`) for the four dictionary
   lemmas — so the transcription uses them instead of re-proving the pin's block; the only
   statement-level difference is that the port's `not_mem_iff_ord_neg` takes `f ≠ 0`, which
   the pin's call sites already have. Consequence: `ord_coe_unit_eq_zero_of_le`, whose only consumer was
   the pin's copy of the separation lemma, is unreachable — shelved, §5.
3. **`A`'s `adicValuation_le_exp_neg_iff_le_ord` is dropped.** Dead in the pin as well
   (`grep -c` over the pin finds it only at `S_AlgebraicCurve_Place_exists_forall_ord_eq.lean:81`),
   and it is one `rw` from the port's public `Place.adicValuation_le_exp_iff`
   (`Defs/Repartitions.lean`), so it is a duplicate rather than ported text — the sweep
   deleted it, §5.
4. **`U`'s three local dictionary `have`s.** `hdegD` is `Divisor.degree_eq_sum_support`
   (the pin unfolds the `Finsupp.liftAddHom` by `simp`/`rfl`); `hres_K` is the port's
   `Place.residue_algebraMap` (`Place/OrdCalculus.lean`); `hord_K` is the port's
   `Place.ord_algebraMap`, which drops the pin's `c ≠ 0` hypothesis (it holds for `c = 0`
   too) — the `have` keeps the pin's binder so the call sites are unchanged. `hunit_iff`
   and `hmem_max` are transcribed as the pin writes them.
5. **Tactic respellings for the current linters**, all the same proof term: `push_neg` →
   `push Not` (`L`); `if_pos` → `ite_eq_left`, `dif_pos` → `dite_eq_left`, `dif_neg` →
   `dite_eq_right` (`U`'s indicator and min-image steps); `AddSubmonoidClass.coe_finset_sum`
   → `coe_finsetSum`; and `smul_eq_mul` is dropped from three `simp only` lists where
   `v4.34.0` reports it unused.
6. **Two scoped linter suppressions, no heartbeat bumps.** `L`'s `haveI : IsFractionRing A E`
   (used as the instance of `FiniteDimensional.exists_is_basis_integral`) and `U`'s
   `haveI : Module.Finite K v.ResidueField` are load-bearing instance locals, so
   `set_option linter.style.haveILetI false in` is scoped to those two declarations with a
   comment in the module header's terms. Nothing else is suppressed.
7. **Not transcribed**, as the project requires: the pin's `attribute [-instance]` /
   `attribute [-simp]` prologues, `p2m_export`/`p2m_open`, the `P2MW.S_` namespace, the
   `solution` wrapper (the headline is stated directly at the wrapper's statement), and
   the heartbeat bumps of §3.

## 5. Dead code, dedup, promotions

- `python3 tools/deps/dedup.py --module <M> --within --min-cost 0`:
  `Place.Approximation` 9 declarations, **0 duplicate clusters, 0 removable lines**;
  `Genus.DegreeIdentity` 3 declarations, **0 duplicate clusters, 0 removable lines**.
- `python3 tools/deps/move_dead.py … --select dead --dry-run` on both modules:
  `Approximation.lean` first reported **2 declarations / 26 lines**, `DegreeIdentity.lean`
  **0 declarations / 0 lines**. The two were `adicValuation_le_exp_neg_iff_le_ord`
  (deleted, §4.3) and `ord_coe_unit_eq_zero_of_le` (shelved).
- The shelf was written by the tool, not by hand:
  `move_dead.py --select names --names ord_coe_unit_eq_zero_of_le --copy --apply` cut the
  helper (20 lines) out of `Approximation.lean` and into
  `Reserve/AlgebraicCurve/Place/ApproximationDead.lean`, closed under its premises (it
  needed none), keeping the declaration `private` and importing only
  `Defs.PushPull` — never the module it came from. Its header carries the pin provenance
  (`S_…:85–101`) and why nothing reaches it; `Reserve/README.md` has the row.
- The shelf carries **no `spec-pin:` wire** by the shelf convention (`check_port.py` does
  not diff it; its one declaration is `private` anyway), which is the one place this set
  departs from "every new module names its pin sources": the two live modules each carry
  their wrappers' lines.
- Re-run after the sweep: `Approximation.lean` **0 declarations / 0 lines** dead,
  `DegreeIdentity.lean` **0 / 0**; the shelf itself reports its one declaration, which is
  what a shelf is. Nothing was promoted: every premise was already public.

## 6. What was not done, and what a reader should not conclude

- Nothing in the four nodes is `sorry`, weakened or left half-wired. The one deletion
  (§4.3) is a duplicate of a public port lemma, and the one shelf (§5) is a reading copy,
  not lost mathematics.
- `E` is `le_antisymm` of the two inequalities **as the port proves them**, so it inherits
  their hypotheses exactly: `[IsCurveOver K F]`, `[FiniteDimensional K (LSpace 0)]`,
  `hx : Transcendental K x` and `[FiniteDimensional (IntermediateField.adjoin K {x}) F]`.
  No separability hypothesis was added or needed (`L`'s route is separable-free, and the
  port's `linearIndependent_pow_mul` carries none).
- `A` is **weak** approximation at finitely many places. It says nothing about a bound on
  `f` away from `T`, and it does not give `f` inside any prescribed `L(D)`.
- `D` is exactly the pole divisor of `x`: `hD` is a pointwise hypothesis, not a
  divisor-class statement.
- The topic note asks for `frontier.py` re-measurement after the set (§1's frontier column
  is the pre-port reading). It was not re-run: the four nodes are landed, so the reading
  they carried is historical.
- No whole-tree `lake build` was run (project rule); the modules were built individually
  and the checker's `--changed` sweep over the wired set is the regression gate.

## 7. Consumer zone

`lean/spec/DegreeIdentityConsumer.lean` (a `spec/` probe, not a library module) composes
the set at a hypothesis-form `IsCurveOver` package:

- zone 1 reads `A` at the indicator `n w = if w = v then 1 else 0`, producing the element
  which is a uniformizer at `v` and a unit at every other place of `T` — the object `U`
  consumes;
- zone 2 applies `L`, `U` and `E` from the same hypotheses and reads off both inequalities
  plus the equality;
- zone 3 substitutes the identity into the landed `AlgebraicCurve.ell_le_degree_add_ellZero`
  to get `ℓ(D) ≤ [F : K(x)] + ℓ(0)` for the pole divisor of `x`.

It elaborates clean in ~3.2 s with `lake env lean spec/DegreeIdentityConsumer.lean`;
deleting either module breaks it.
