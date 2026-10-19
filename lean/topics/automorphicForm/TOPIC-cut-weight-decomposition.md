# The cut-vector weight decomposition — mathematics, definition wave and plan

`AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent`
(906 raw `S_` lines, docs node 5468, "Weight decomposition of cut vectors at real places") is the
statement that a level-and-type cut vector in a cuspidal constituent splits, at the real places,
into a finite sum of vectors of pure archimedean weight. It is the adelic form of "a `K`-finite
vector for a compact torus is a finite sum of weight vectors", and it is what the Casimir-eigenvalue
and trichotomy lemmas downstream consume. This note is the set's home: §1 the mathematics, §2 the
measurement, §3 the definition closure it needs, §4 the definition wave, §5 the proof set and its
order, §6 risks and recorded negatives, §7 reproduce, §8 residuals.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

Companions: the column note [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2 (the leaf
shelf) and §7; the playbook [../porting-playbook.md](../porting-playbook.md) §2.3 (whole nodes),
§3.3–§3.4 (work orders, sets), §4.1 (the wire and tier 3), §5 (sharing); the neighbouring
archimedean subject [TOPIC-arch-casimir.md](TOPIC-arch-casimir.md) (the `𝔰𝔩₂` calculus this set's
consumers use); the pin's own `Theorems/` wrapper is the statement authority.

## 1. The mathematics

Let `K` be a number field, `c u d₁ d₂` reals with `c > 0` and `0 < d₁ < d₂`, and `T` a finite set
of adelic points; write `D = centreCutSiegelSet K c u d₁ d₂` and `D_T = ⋃ x ∈ T, (· * x) '' D`.
Assume `CoversModCentre K D_T`: every adelic point is a principal point times a central scalar times
an element of `D_T`. Attach the carrier data `productionPinsOf` (level groups `levelOne ⊓
finiteAdelicGL2Subgroup`, Hecke generators `heckeGen`, full centre, measure from `adelicBox`), a
character `ξ` of its centre, an ideal `N ≠ 0`, and a family `tys : ArchTypeFamily K` assigning
finitely many archimedean types to each infinite place. Let `V` be a cuspidal constituent
(`IsCuspConstituent`, i.e. the cusp subrepresentations of `V` are `0` or `V`) and let

`y ∈ V ⊓ levelInvariantSubmodule … N ⊓ archCutSubmodule K tys`,

so `y` is level-`N` invariant and lies in the archimedean cut: the intersection over infinite places
`w` of the sum of the type submodules for the types listed at `w`. Then there are `m` and
`y₁ … y_m`, each again in the same triple intersection and summing to `y`, such that at every real
place `w` each `y_j` has a pure weight:

`∃ n : ℤ, HasArchCharacterAt₀ K w (archWeightCharAt hw n) (ys j)`

— right translation by the row-isometry subgroup acts on `y_j` by the `n`-th power of the basic
weight character `archWeightOneAt hw`. Complex places are untouched by the decomposition; the
statement quantifies over real places only.

The shape of the proof is the classical one: the cut is a finite sum of `K`-finite pieces (that is
what `archCutSubmodule` is), each piece is finite-dimensional under the compact torus, and a
finite-dimensional representation of a torus over `ℂ` splits into characters (weight vectors). What
the pin has to do by hand is carry that through the adelic bookkeeping: the level module, the
cusp-constituent irreducibility, and the archimedean character predicate.

## 2. The measurement

| quantity | value |
|---|---:|
| pin `Theorems/` wrapper | 39 lines (statement authority) |
| pin `P2M/Sol/S_` file | 906 |
| duplicate copies removable | 0 |
| boilerplate (imports/attrs) | 21 |
| **net new math lines** | **882** |
| declaration groups | 77 (76 declarations in the `S_` file) |
| already in the port | 3 (all tier 3) |
| substitutions | 1 |

It is a **single-headline, single-file set**: one public theorem, 76 declarations, no shared
prelude with any other pin file (`port_advise` reports 0 shared names). On the D-S
`--include-leaves` shelf it reads 906 silo lines.

## 3. The definition closure

The `S_` file's import block names six pin `Definitions/` modules; hand-walking their own imports
(playbook §4(a)) gives a **19-module closure**, of which 13 are already in the port — 11 listed in
`SOURCES` and two that the port carries **tier 3** (`NumberTheory/AdelicFourier.lean` is
`Def_NumberField_AdelicFourier`; `Def_NumberField_TateGlobalZeta` is registered the same way).

**Six are unported** — this set's definition wave:

| pin module | lines | declarations | of which `private` | public | pin importers |
|---|---:|---:|---:|---:|---:|
| `Def_AutomorphicForm_WhittakerCoefficient` | 61 | 8 | 0 | 8 | 653 |
| `Def_NumberField_AdelicTraceFin` | 204 | 24 | 18 | 6 | 193 |
| `Def_NumberField_AdelicTraceProducer` | 224 | 21 | 0 | 21 | 24 |
| `Def_NumberField_IntegralAdelicTrace` | 395 | 45 | 10 | 35 | 4 |
| `Def_NumberField_StandardGlobalAddChar` | 116 | 14 | 0 | 14 | 11 |
| `Def_NumberField_StandardGlobalAddCharRat` | 724 | 44 | 0 | 44 | 760 |
| **total** | **1,724** | **156** | **28** | **128** | — |

They are infrastructure, not this leaf's private business: `WhittakerCoefficient` has 653 pin
importers and `StandardGlobalAddCharRat` 760, so they are homed whole (§2.3) rather than cut to the
leaf's needs.

**Promotions owed: none.** All 28 pin-`private` declarations were checked against the leaf's `S_`
file by name; the only textual hit was the `S` of a local `Finset` variable, not the pin's private
`def S`. So the wave transcribes them as the pin has them (`private` where the pin is `private`) and
the checker's delta is the public surface: **+128**, in six appends.

## 4. The definition wave

Wave 0 (manager), one module at a time, each tier-1 loop then tier-2 build then wired. **Complete:**
checker `10,107 → 10,235` (**+128**, exactly the six modules' public surface), 0 mismatched /
0 missing, every module tier-1 clean and tier-2 green, declaration parity exact under the checker's
parser (14 / 21 / 45 / 24, private 0 / 0 / 10 / 18).

| port home | pin module | status |
|---|---|---|
| `FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean` | `Def_AutomorphicForm_WhittakerCoefficient` | **landed**, checker +8 (10,107 → 10,115) |
| `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddCharRat.lean` | `Def_NumberField_StandardGlobalAddCharRat` | **landed**, checker +44 (10,115 → 10,159) — 724 lines, one drift repaired |
| `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddChar.lean` | `Def_NumberField_StandardGlobalAddChar` | **landed**, +14 |
| `FLTForHuman/NumberTheory/NumberField/AdelicTraceProducer.lean` | `Def_NumberField_AdelicTraceProducer` | **landed**, +21 |
| `FLTForHuman/NumberTheory/NumberField/IntegralAdelicTrace.lean` | `Def_NumberField_IntegralAdelicTrace` | **landed**, +35 (+10 private) |
| `FLTForHuman/NumberTheory/NumberField/AdelicTraceFin.lean` | `Def_NumberField_AdelicTraceFin` | **landed**, +6 (+18 private) |
| `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddCharRat.lean` | `Def_NumberField_StandardGlobalAddCharRat` | planned |
| `FLTForHuman/NumberTheory/NumberField/AdelicTraceProducer.lean` | `Def_NumberField_AdelicTraceProducer` | planned |
| `FLTForHuman/NumberTheory/NumberField/IntegralAdelicTrace.lean` | `Def_NumberField_IntegralAdelicTrace` | planned |
| `FLTForHuman/NumberTheory/NumberField/AdelicTraceFin.lean` | `Def_NumberField_AdelicTraceFin` | planned |

Order is by dependency, not size: the additive character first (both trace modules are stated
against `AddChar`-valued pairings), then the trace producer, then its integral form, then the
finiteness wrapper. `WhittakerCoefficient` came first only because it is independent of the other
five and validates the route.

Each is a new leaf module: no edit to an existing module, so `build_ladder.py --edit` has nothing to
price and the cascade is its own `.olean` plus the checker row. The pin's `import Mathlib` appears in
the closure only through already-narrowed port modules; each new module imports the specific mathlib
modules it needs (`Mathlib.Algebra.Group.AddChar` for the character type, as
`WhittakerCoefficient.lean` does).

## 5. The proof set and its order

Set A, one dispatch, ~882 content lines (playbook §0.2: one set, one story, one module):
`FLTForHuman/AutomorphicForm/Adelic/Cusp/CutWeightDecomposition.lean`, one public theorem at the
wrapper's exact statement, everything else `private`, and the three substitutions the port already
carries imported rather than re-proved — `rotMat`/`rotGL` are `AutomorphicForm.RealIwasawa.rot`/
`rotGL` in `FLTForHuman/AutomorphicForm/Iwasawa/Real/Core.lean`. Order:
[WORKORDER-CD2-cut-weight-proof.md](WORKORDER-CD2-cut-weight-proof.md).

**Landed.** `CutWeightDecomposition.lean`, 948 lines, 78 declaration sites (the pin's 76 under the
checker's parser plus the `scoped instance` that parser does not read): one wired headline, **68
public declarations registered tier 3** behind `-- pin:` markers, 5 `private` (`ker`, the four
`ContinuousOrbits` structure lemmas), and every shared declaration's statement text verified equal
to the pin's. Checker `10,235 → 10,237` (**+2**: the headline, and one declaration whose name and
statement a listed pin file already provides, so it is verified rather than registered), 0
mismatched / 0 missing, register current.

Three decisions worth keeping:

* **The reuse table in the order was wrong, and the worker caught it.** `rotMat`/`rotGL` are not
  statement-identical substitutions: the port's `RealIwasawa.rot θ` is the **transpose** of the
  pin's `rotMat θ`, i.e. `rot (-θ)`. Substituting at `+θ` compiles and silently flips
  `archWeightOneℝ_rotSO` and `archWeightCharAt_rotAt` against `P_act`; the port therefore keeps the
  pin's local names as one-line abbrevs onto `rot (-θ)` and every downstream statement stays
  verbatim. Recorded in the playbook §7.
* **Four pin-public declarations stay `private`.** `PeriodicFlow.ContinuousOrbits.{add, smul, zero,
  sum}` have last names that listed modular-curve files also carry; the checker's marker is a
  fallthrough, so registering them produces four spurious `MISMATCH`es. They are structure lemmas
  of a local namespace and are kept `private` instead (playbook §7).
* **The pin's `scoped instance instFactTwoPi` becomes `private instance`.** The two modifiers do not
  combine; the instance is invisible to the checker either way, and a file-local copy avoids
  exporting a global `Fact (0 < 2π)` that could collide with mathlib's. Body `⟨by positivity⟩` →
  `⟨Real.two_pi_pos⟩`.

## 6. Risks and recorded negatives

* **The statement is one line and enormous.** Every hypothesis (`productionPinsOf … (fun N =>
  levelOne … ⊓ …) …`, `archCutSubmodule K tys`, `IsCuspConstituent`) is a long applied term; the
  checker diffs it textually, so it is copied from the wrapper binder for binder. A "cleaned-up"
  statement is a mismatch.
* **The two already-ported closure modules are tier 3, not listed.** `AdelicFourier` and
  `TateGlobalZeta` are found through the register, not `SOURCES`; a port check that greps `SOURCES`
  alone reports them unported (it did, on the first pass).
* **`StandardGlobalAddCharRat` is 724 lines with 44 public declarations and 760 importers.** It is
  the largest piece of the wave and is a hub in its own right; it is homed whole, not cut to this
  leaf.
* **`AdeleRing` is a `def`, not an `abbrev`.** A literal pair is an adele only at default
  transparency, so the pin's proofs — which pass pairs straight into `rw`/`simp` and take `.1`/`.2`
  of them by `rfl` — stop matching at *implicit* transparency in mathlib `v4.34.0`. The recorded fix
  (used twice in `StandardGlobalAddCharRat`, and written into the wave's work order) is to bind the
  point once as a typed local (`set x : AdeleRing (𝓞 ℚ) ℚ := … with hx`) and rewrite on `x.1`/`x.2`
  via `show … from by rw [hx]`. `erw` looks like a fix and is not: it unfolds far enough to also
  unfold the definition under study, after which the pin's projection rewrites find nothing.
* **No promotion is owed, and that is checkable.** The 28 `private` declarations were compared by
  name against the leaf's `S_` file; re-run that check if the set's scope widens.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --include-leaves --rank-by silo --top 0    # the shelf row
python3 explore.py AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent
python3 port_advise.py --target S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent --json build/cutsum_advise.json
python3 port_plan.py --json build/cutsum_advise.json --section budget
```

The closure walk is a five-line script over the `S_` file's `import Definitions.` lines, repeated
until closed, testing each module against `SOURCES` **and** `spec/UNWIRED-PUBLIC.md` (the register's
pin-original column is the tier-3 half of the test).

## 8. Residuals

* **Wave 0 is five modules in.** The remaining 1,663 lines are pure transcription with no promotion
  decision open, so the route is settled; the risk is only drift between mathlib `v4.33.1` and
  `v4.34.0` in the trace and additive-character APIs, which the per-module edit loop finds.
* **The proof set is not yet scoped against the new modules.** Once wave 0 lands, `port_advise` runs
  again on the `S_` file to confirm the 3 substitutions and price the set against the ports that
  now exist.
* **The leaf's consumers** (`casimir_im_eq_zero_and_nonneg…`, `exists_ne_zero_forall_linearCombination…`)
  are downstream rows; this note does not price them.
