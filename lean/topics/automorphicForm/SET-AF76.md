# SET-AF76 — the four rows SET-AF75 readied

**Status: SCAFFOLDED, DISPATCHED (2026-11-14).** Read off the D–S shelf after SET-AF75 with the recipe
in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). The
seventy-sixth set of the column, and the column's rule in force: **the next cut is the rows the last set
readied**. All four were one unported premise away before SET-AF75 and are `premises_unported = 0` now.

**4 rows / 929 silo / ≈774 net** in **four new modules**, four orders.

| # | row | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `EisensteinGeneral.Unfolding.whittakerCoefficient_bruhatSeries_eq_of_isInducedSection` | 275 | 2/4 | new `EisensteinGeneral/Unfolding` |
| **B** | `NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq` | 241 | 2/6 | new `NumberTheory/AdelicBox/Normalization` |
| **C** | `AutomorphicForm.sum_norm_whittakerCoefficient_sq_le_integral_norm_sq` | 214 | 2/6 | new `AutomorphicForm/Adelic/BesselInequality` |
| **D** | `EisensteinGeneral.Glue.integrable_mul_of_integrable_of_integrable` | 199 | 6/12 | new `NumberTheory/AdelicFourier/IntegrableTensor` |

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf_af76.json
```

| figure | value |
|---|---:|
| `needed [F terminal]` | **596 / 267,011** |
| ready rows, all namespaces | **26 / 5,719** |
| leaves, all namespaces | **143 / 37,308** |
| withheld by the FR-0044 guard | 4 / 831 |

`needed` is exactly SET-AF75 §4's post-landing figure, and the ready block is the 22 rows of SET-AF73 §1.1
plus AF75's four. `--selfcheck` still FAILS on the fifteen `ModularCurve.PhiGen`/`ModularPolynomialData`
markers (MD-005); no row cut here cites any of them. One row of the read is the *repair* of a scaffolding
omission (SET-AF75's `comp_mul_mem_schwartzBruhat`, restored and checker-green in the same touch, FR-0217).

## 1. What the set says

- **A** — for a global additive character `ψ` and an induced section `φ` (`IsInducedSection`), the
  Whittaker coefficient of the Bruhat-series summand of `φ` unfolds to the invariant integral
  `(𝓞̂-measure)⁻¹ • ∫ y, φ (w · u(y) · g) * ψ (-(ξ · y))` against the adelic Haar measure. The whole
  21-declaration `WhittakerUnfolding` engine is the pin's private prelude (fundamental-domain averaging,
  `tsum`/`lintegral` interchange, the `1 - c` argument) and is ported **private**, as in the pin.
- **B** — the box normalization: `μ (adelicBox F)⁻¹ * ∫ x, f x.1 * g x.2 ∂μ = (2 ^ nrComplexPlaces F /
  √|disc F|) * (∫ f) * (ν (𝓞̂)⁻¹ * ∫ g ∂ν)`. This is the constant of the adelic Fourier transform of a
  pure tensor (SET-AF75's `fourierIntegral_pureTensor_eq`), and the module also carries its seven
  ingredients: the compactness of `{y | s * y ∈ 𝓞̂}`, `σ`-compactness of the finite adèles, second
  countability of the completions and of the infinite adèles, and the two coordinate formulas for the
  mixed-space transport plus its continuity.
- **C** — the Bessel inequality for the Whittaker coefficient: `∑_{α ∈ A} ‖W_ψ φ α g‖² ≤ ∫ ‖φ (u · g)‖²`
  against the box-normalized measure, from the orthonormality of the characters `ech ψ α u = ψ (α · u)`
  in `L²`.
- **D** — the pure tensor of two *integrable* functions is integrable on `𝔸_F` (no Schwartz or
  locally-constant hypotheses): the general form of SET-AF75's `integrable_pureTensor`.

### 1.1 The shelf, quoted whole — every row cut or deferred

**The ready block: 26 rows / 5,719 silo — 4 cut (A–D), 22 deferred.** The 22 are SET-AF73 §1.1's block
verbatim (`EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` 890, the two
`WeierstrassCurve` rows 697 / 599, `GaloisRep.exists_isSemisimpleRepresentation…` 495, … the
`ModularCurve.rep_tateModule_jOne_comm` 24 tail), and every one of them is deferred for a stated reason
in that table: the `EisensteinGeneral.Piece` pair and the `WeierstrassCurve` stabilizer rows need
definition layers the port does not have (`AutomorphicForm/Adelic/WeilIntertwining`, the
`IsCharTwoJNeZeroNF`/`IsCharThreeJNeZeroNF` classes), and the rest are larger than this set's rows.

**The leaves block: 143 rows / 37,308 silo — none cut, all deferred** (SET-AF75 §1.1's block, unchanged
apart from the twelve rows that set landed). Its top row is still `M4aTorus.completedRayL_fe` (12,126,
deferred: its `Def_` layer is not ported).

## 2. The price and the home

```bash
python3 port_advise.py --nodes <the 4> --with-defs --json build/af76_advise.json
python3 port_plan.py --json build/af76_advise.json
```

| figure | value |
|---|---:|
| raw `S_` lines | 929 |
| declaration lines | 819 |
| duplicate copies | 0 (the pin's own duplication is by *name*, see below) |
| **net new math lines** | **774** |
| already in the port | 45 declarations |
| substitutions | 159 trusted / 6 suspect (the parser's type-only `def` matches: `classRepSiegelSet ↔ centreCutSiegelSet`, `productionPinsGeneral ↔ productionPins`, … — read, not applied) |

**The set's one real dedup is not in `port_plan`'s "duplicate copies" column, because the pin spells the
two copies differently.** B's file carries seven *public* declarations
(`isCompact_setOf_mul_mem_integralFiniteAdeles`, `sigmaCompactSpace_finiteAdeleRing`,
`secondCountableTopology_completion`, `secondCountableTopology_infiniteAdeleRing`,
`ringEquiv_mixedSpace_symm_apply_of_isReal/_of_isComplex`, `continuous_ringEquiv_mixedSpace_symm`), and
D's file re-proves the same seven as `private theorem ch3_…` with explicit `(F : Type)` binders. The port
writes them **once**, publicly, in B's module, and D's module imports it — D's 200-line pin file drops to
a one-declaration module. (`secondCountableTopology_infiniteAdeleRing` also exists in
`AutomorphicForm/Adelic/ArchApproxIdentity/ArchInfra.lean`; that is the pin's own duplicate too, and the
port keeps both because the normalization module sits *below* that hub — recorded, not merged.)

| module | rows | scaffold | `sorry` | `check_port` |
|---|---|---:|---:|---|
| `EisensteinGeneral/Unfolding.lean` (new) | A | **71** lines | 1 | **1 ok / 0 / 0** |
| `NumberTheory/AdelicBox/Normalization.lean` (new) | B | **102** | 8 | **8 ok / 0 / 0** |
| `AutomorphicForm/Adelic/BesselInequality.lean` (new) | C | **134** | 14 | **15 ok / 0 / 0** |
| `NumberTheory/AdelicFourier/IntegrableTensor.lean` (new) | D | **52** | 1 | **1 ok / 0 / 0** |

Two statements needed a manager decision, both recorded: C's `main` is folded into the headline at the
graph node's name (its statement is the wrapper's), and C's section variable `F` is spelled
`variable {F}` from `ech` onward — v4.34 inserts the pin's explicit section variable into `ech`'s
telescope whereas the pin's Lean left it implicit, so the pin's text `ech ψ α` elaborates only with the
implicit annotation (`nuBox` keeps its explicit `F`, which is what `nuBox F` calls). The `Bessel17`
and `BoxNormalization` label namespaces are dropped; `ech` keeps the pin's name (the module header
glosses it).

## 3. The orders and the gates

| order | rows | file | content | scaffold `sorry`s |
|---|---|---|---:|---:|
| `WORKORDER-AF76A` | A | `EisensteinGeneral/Unfolding.lean` | ≈200 + 21 private engine decls | 1 |
| `WORKORDER-AF76B` | B | `NumberTheory/AdelicBox/Normalization.lean` | ≈180 | 8 |
| `WORKORDER-AF76C` | C | `AutomorphicForm/Adelic/BesselInequality.lean` | ≈180 | 14 |
| `WORKORDER-AF76D` | D | `NumberTheory/AdelicFourier/IntegrableTensor.lean` | ≈60 | 1 |

A, B, C touch disjoint files and run concurrently. **D imports B's module** (the seven shared
declarations): its file is scaffolded against B's public statements, so it can be written in parallel —
but its worker must not edit B's module, and if B's *statements* were to move, D would break (they are
frozen: B's checker wire is the pin's).

Gates, per order: the same six as SET-AF75 §3 — edit loop at `-DmaxHeartbeats=200000` with an empty
`error|warning` grep (no `set_option`, a blow-up is a defect to diagnose: `porting-playbook.md` §3.5,
and see FR-0217 for the delayed-coercion shape); the module's own `lake build` under `flock`/`timeout`,
silent; `check_port --force` at the counts above; `#print axioms` clean; `dedup --within` /
`move_dead --dry-run`; one consumer zone per order.

## 4. The shelf effect

*To be measured on the landed tree against §0's baseline (596 / 267,011).* The forecast is measured with
the recipe's `--port` dual, and it returns **two** rows:

| figure | §0 | forecast (4 `--port`ed) |
|---|---:|---:|
| `needed [F terminal]` | 596 / 267,011 | **592 / 266,082** |
| ready rows | 26 / 5,719 | **24 / 5,045** |
| leaves | 143 / 37,308 | 143 / 37,308 |

| row readied | silo | lev |
|---|---:|---:|
| `EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` | 185 | 3/9 |
| `AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 70 | 4/9 |

The ready block *shrinks* by four and gains two, so the net is −2 rows: the first set in the wave whose
own cut is larger than what it readies, which is what a cut of the readied tail of the block looks like.

## 5. The landing

All four rows in, **24 `sorry`s → 0**, four new modules, no hub edited.

| file | row | lines | `sorry` | checker | axioms |
|---|---|---:|---:|---|---|
| `EisensteinGeneral/Unfolding.lean` | A | 71 → **314** | 1 → 0 | **1 ok / 0 / 0** | clean |
| `NumberTheory/AdelicBox/Normalization.lean` | B | 102 → **259** | 8 → 0 | **8 ok / 0 / 0** | clean |
| `AutomorphicForm/Adelic/BesselInequality.lean` | C | 134 → **228** | 14 → 0 | **15 ok / 0 / 0** | clean |
| `NumberTheory/AdelicFourier/IntegrableTensor.lean` | D | 52 → **102** | 1 → 0 | **1 ok / 0 / 0** | clean |

903 lines written (≈1,050 net new was the estimate; the difference is B's seven shared declarations written
once instead of twice — the pin's duplication, worth ≈120 lines — and A's engine at 243 lines against the
pin's 226). Consumer zones `spec/EisensteinGeneralSetAF76AConsumer.lean` (82),
`NumberTheorySetAF76BConsumer.lean` (86), `AutomorphicFormSetAF76CConsumer.lean` (89),
`NumberTheorySetAF76DConsumer.lean` (170): **0 errors, 0 warnings** each. `dedup --within`: 0 clusters in
all four. Imports added: **one** (`Normalization` → `AdelicHaar/Uniqueness`, the home of the uniqueness
row).

**Heartbeat floors** (probed downward, no `set_option`): A 4 000, D 9 000, B 14 000, C 3 516 — 14× to 57×
under the 200 k cap. The one blow-up was *found and fixed by the worker* rather than reported: A's
`integrand_eq` sat at 80–100 k because a bare `congr 1` whnf'd the whole `∑'`-equation, whose six
`algebraMap F (AdeleRing (𝓞 F) F)` occurrences each drag the `IsLocalization'` instance defeq
(`Set ↦ 15401`, `Fin.cases ↦ 21336`); naming the congruence (`congrArg`) took it to 4 k. (`add_left_inj`
in place of `congr 1` is *worse* — over 200 k, rejected.)

### The deviations worth carrying

- **A**: the pin's `principalEquiv` is the port's `AutomorphicForm.BruhatConstantTerm.principalEquiv`
  (byte-identical, in `AutomorphicForm/Adelic/BruhatEisenstein.lean` — the *module* name is not the
  *namespace* name, which cost the worker a lookup); the pin's private `_of_isInducedSection` wrapper
  (`:247-253`) is inlined into the headline; 19 private engine declarations, as the pin has them. Two of
  them (`principalEquiv_vadd`, `productionPins_nu`) are unused **in the pin too** and are kept for
  fidelity (`move_dead` reports 2 declarations / 8 lines, recorded rather than swept — the pin's own
  unused private lemmas, AF70's precedent).
- **B**: v4.34's `AdeleRing` is a `def`, so the pin's `subst hmA` leaves `μ` with a stale instance and
  `μ (adelicBox F)` is rejected; the fix is a product-typed `let μP := μ` plus one `change`, after which
  the pin's whole lemma sequence transcribes (FR-0219). The scaffold's three `omit`s became the pin's
  four.
- **C**: the manager's `variable {F}` (v4.34 binder drift, forced — see FR-0218) re-spells the pin's
  *call sites* of same-file theorems (`foo F G hG x` → `foo G hG x`); v4.34's
  `@norm_sq_eq_re_inner ℂ` is the class projection `InnerProductSpace.norm_sq_eq_re_inner` and needs
  `𝕜` pinned under a `conv_lhs` (a bare `rw` also hits the `‖f u‖^2` on the right).
- **D**: the pin's eight `haveI`/`letI` become `have`/`let` with the instances still found (Lean 4
  registers them); the seven `ch3_…` calls redirect to B's public names; the uniqueness row is called at
  its port namespace `NumberField.AdelicHaar` (the pin spells it `AdelicFourier`).

### Orchestration: the shared prelude, and the gate that waits

B's `Normalization` is a **dependency of D**, and the two ran in parallel (sound for the statements: a
scaffold's `sorry` bodies elaborate). D's edit loop and checker were green while its `lake build` failed
with four errors *inside B's half-written file*, so its build/axioms/dedup/consumer gates could only run
once B landed (~25 min later, with no change to D's file). Recorded as FR-0220 with the rule: an order
whose module another order fills either goes second, or is told at dispatch that its build-side gates
close after the dependency lands — never to hand-make an `.olean` or edit the dependency.

### The set's numbers, and the plan-vs-actual

| figure | before (§0) | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 596 / 267,011 | **592 / 266,082** | −4 / −929 ✓ exact |
| ready rows | 26 / 5,719 | **24 / 5,045** | −2 / −674 ✓ exact |
| leaves | 143 / 37,308 | **143 / 37,308** | unchanged ✓ exact |

The two rows readied by the set are the two named in §4 before dispatch
(`EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq`, 185, and
`AutomorphicForm.LocalIntertwining.integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`,
70) — and `inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` is B's own subject one step further
(the Fourier-tensor form of the box normalization), so the next cut is again forced by the read.
