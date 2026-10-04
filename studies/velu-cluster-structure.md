# The Vélu cluster: theory structure, and a method for planning a redundant port

**Status (snapshot, 2026-10-04).** Companion to
[../lean/topics/velu/TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md)
(the operative plan: budget, homes, order) and to
[elliptic-weierstrass-tate-scout.md](elliptic-weierstrass-tate-scout.md) §2/§4
(where the block was measured and ordered as a subject). Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

This note deliberately does **not** repeat the topic's numbers, block table or
phase list. It answers the two questions a topic file is the wrong shape for:

* **What is the mathematics of the 47-node slice, and why does it have the shape
  it has** (§1–§3) — the pin's proof architecture, the two proof spines and the
  substrate they share;
* **How the plan was derived, as a reusable method** (§4–§5) — the redundancy-first
  reading of `port_advise`, and where it sits among the project's other graph
  instruments.

The object-form taxonomy of the wider elliptic-curve subject is in
[basic-objects-ec-modular.md](basic-objects-ec-modular.md) §1, which records the
isogeny side (Vélu, `IsogenyEndDatum`, dual isogenies, Drinfeld, Tate module) as
pin-only; this note is about the internal structure of that pin-only side.

## 1. The pin's proof architecture (why the slice looks the way it does)

Every node in the slice has the same three-layer pin shape:

| layer | file | size | role |
|---|---|---|---|
| statement | `Theorems/Thm_<stem>.lean` | ~14 lines | the public theorem, proved by `p2m_exact_reverting @P2MW.S_<stem>.solution` |
| proof body | `P2M/Sol/S_<stem>.lean` | 11–12,012 lines | every helper the pin used, plus `solution`; carries a `p2m_*`/`attribute [-instance] [-simp]` prologue |
| vocabulary | `Definitions/Def_*.lean` | small | the shared definitions |

Three consequences drive the whole plan.

**The deliverable is one public theorem per node.** The `S_` file is a transcript
of how the pin proved it, not the interface. The port may reorganise the body
freely as long as the `Thm_` statement lands; this is what makes a *factoring*
plan possible at all.

**Most of the mass is the re-developed substrate, not the theorem.** Each `S_`
file opens with a large copied prologue (the `p2m_open` lists, the function-field
dictionary, the `ord`/`evalAt` calculus) before reaching its own mathematics.
That prologue is why four files of 10–12 k lines share 373 declarations.

**Some declarations are `Prop`-valued bundles, not content.** A pin idiom writes a
long intermediate goal as `def KwD5BetweenCurvesHoloLift : Prop := ∀ …, ∃ …` and
then proves it. These are goal-shaping aliases; the statement checker sees only
their type (`Prop`) and therefore confuses them with each other. The topic §4
turns that into a vetting rule.

Finally, the `p2m_*` directives (`p2m_open`, `p2m_reactivate`, `p2m_export`) are the
mechanism that flattens the pin's namespaces so the `S_` body can be checked
against the `Thm_` statement; they are port scaffolding, not mathematics.

## 2. The mathematics: two spines over one substrate

The 47 nodes are not one argument. They are **two largely separate proof spines**
that share a common algebraic substrate and meet only near the top. The extracted
`import` DAG confirms the split: each spine is a chain of its own, and the handful
of nodes that import across spines (`zmultiples_eq_of_veluQuotient_j_eq_of_forall_isogenyEndDatum_exists_int`
is the clearest) are exactly the join points.

```
                 mathlib EC: group law, division polynomials ψn, Ψn, j, Δ
                                    │
        ┌───────────────────────────┴───────────────────────────┐
        │                                                        │
   SPINE V (explicit Vélu)                            SPINE E (isogeny data)
        │                                                        │
   veluQuotient2 / veluQuotient                        curve FunctionField
   veluX / veluY / veluU                               Place, Divisor, Pic0
        │                                                        │
   velu_map_equation                            pushforwardAlong / restrictAlong
        │                                                        │
   exists_veluPointHom  (ker = ⟨Q⟩)             IsogenyEndDatum / IsogenyHomDatum
        │                                                        │
   discriminant identity                        pointEnd, isogenyEndSubring
        │                                                        │
   cyclicQuotientJ ↔ ΦN  (modular polynomial)   dual-end / add classification
        │                                                        │
        └──────────────────── SUBSTRATE ────────────────────────┘
             ord · evalAt · XYIdeal · placeOfPoint · finite places
```

### 2.1 The substrate

The shared vocabulary is the `AlgebraicCurve` place/divisor calculus applied to
the Weierstrass function field: `Place K F`, `ord`, `evalAt`, `toValuationSubring`,
`restrictAlong`, `Divisor`, `Pic0`, `IsPrincipal`, `degree`, together with
`CoordinateRing.XYIdeal`, `exists_eq_XYIdeal`, `XYIdeal_isMaximal`,
`isDedekindDomain`, and the quadratic presentation of the function field
([`Def_WeierstrassCurve_FunctionFieldQuadratic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_FunctionFieldQuadratic.lean)).
Both spines must show that their construction is a morphism, and both do it by
computing orders and evaluations at the places over a point — hence the shared
prologue. The port already has most of this substrate in
`lean/FLTForHuman/AlgebraicCurve/**` and `WeierstrassCurve/FunctionFieldQuadratic.lean`
(see the topic §2).

### 2.2 Spine V — explicit Vélu formulas and the modular polynomial

The pin develops Vélu's formulas from scratch on top of mathlib's division
polynomials.

*Local data at a point* `Q = (x₀, y₀)`
([`Def_WeierstrassCurve_Velu.lean:10–18`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean#L10-L18)):
`veluGx = 3x₀² + 2a₂x₀ + a₄ − a₁y₀` (the tangent numerator),
`veluGy = −(2y₀ + a₁x₀ + a₃)` (the vertical derivative),
`veluT = 2·veluGx − a₁·veluGy`, `veluU = veluGy²`, `veluW = veluU + x₀·veluT`.
On the curve `veluU` is exactly `Ψ₂Sq.eval x₀`, so the formulas are pinned to
mathlib's `Ψ₂Sq`.

*The order-two quotient*
([`veluQuotient2`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluOrderTwo.lean#L12)):
keep `a₁,a₂,a₃`, replace `a₄ ↦ a₄ − 5·veluGx`, `a₆ ↦ a₆ − b₂·veluGx − 7·x₀·veluGx`.
The order-two nodes (`veluQuotient2_{Delta_eq,cFour,j}`, `velu2QuadDisc`,
`veluGx_ne_zero`, the `velu2_*_cleared_identity` trio) verify that this curve is
the quotient by `⟨(x₀,y₀)⟩`; `exists_addMonoidHom_coe_eq_veluPointMap2` produces
the induced `W.Point →+ (veluQuotient2 x₀ y₀).Point` and identifies it with the
explicit rational map `veluPointMap2`.

*The odd-order quotient.* For `Q` of order `2n+1`, the summing set
([`oddOrderSummingSet`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_OddOrderSummingSet.lean#L24))
is `S = {(k • Q).coordsOrZero : 1 ≤ k ≤ n}` — one representative from each pair
`±kQ` of the nontrivial kernel. The quotient curve
([`veluQuotient`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_Velu.lean#L59))
shifts `a₄` by `−5·Σ_{P∈S} veluT(P)` and `a₆` by `−b₂·Σ veluT − 7·Σ veluW`, and
[`veluX`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluQuotientMap.lean#L47)
/
[`veluY`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_VeluPointMap.lean#L51)
are the summed rational corrections. The computational core is
`velu_singleton_equation_cleared`: a single enormous `linear_combination`
polynomial identity proving that the singleton map lands on the quotient curve.
`velu_map_equation_of_oddOrderSummingSet` is the summation of that identity over
`S`; `exists_veluPointHom_oddOrderSummingSet` is the resulting isogeny with
`ker φ = ⟨Q⟩`.

*The discriminant identity*
(`veluQuotient_oddOrderSummingSet_discriminant_prod_veluU_pow`):
`Δ(veluQuotient S) · (∏_{P∈S} veluU(P))⁴ = Δ^(2n+1)`. This is the arithmetic
content of "an ℓ-isogeny multiplies the discriminant by an ℓ-th-power factor",
and it is the bridge to the modular polynomial.

*The modular-polynomial end*
([`cyclicQuotientJ`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_CyclicQuotientJ.lean#L144),
[`ModularPolynomialData`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X0.lean#L215)):
`bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j` states the
classical bijection, for transcendental `j`,
`{H ≤ E : IsAddCyclic H, card H = N} ≃ {y : Φ_N(j(E), y) = 0}`,
sending a cyclic subgroup to the `j`-invariant of its quotient;
`exists_equiv_addSubgroup_isAddCyclic_…` is the Galois-equivariant refinement.

### 2.3 Spine E — function-field isogeny data and the endomorphism ring

The second spine never writes a Vélu formula. It works entirely with an
`F`-algebra map of function fields and the divisors it pushes forward.

*Along-hom vocabulary*
([`Def_AlgebraicCurve_Correspondence.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Correspondence.lean#L37-L51)):
`FiniteAlong K φ` (`F'` is finite over `F` along `φ`, via `algebraAlong φ`),
`NormFormulaAlong K φ hfin` (the divisor pushforward respects degrees/norms),
`finrankAlong K φ` (`Module.finrank F F'`), and `SeparableAlong K φ`.
`Divisor.pushforwardAlong`, `Pic0.pushforwardAlongHom` and `Place.restrictAlong`
move divisors, classes and places along `φ`.

*The place gate* is the hypothesis bundle that keeps the two spines honest
([`GenusOnePlaceGate`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L18)):
a chosen equivalence `W.Point ≃ Place F W.FunctionField` with every place of
degree one, plus `IsCentred` (the classes of `X` and `Y` are non-units at the
point's place). [`AbelTheorem`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L95)
is Abel's theorem in the form "a degree-zero divisor is principal iff its sum is
zero", giving the isomorphism
[`genusOnePic0Equiv : Pic0 ≃+ W.Point`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_GenusOnePic0.lean#L149).
This is the seam where the group law and the function field are identified.

*Isogeny data.*
[`pointMapOfPushforward`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L102)
is `genusOnePic0Equiv ∘ pushforwardAlongHom ∘ pointClass`; its defining property is
the "seam" lemma `pointMapOfPushforward_eq_of_seam`: if `placeOfPoint (g P) =
(placeOfPoint P).restrictAlong ι` and `g 0 = 0`, then the pushforward is `g`.
[`IsogenyEndDatum W`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L149)
is the data `(ι : W.FunctionField →ₐ[F] W.FunctionField, hι, hfin)`; `pointEnd` is
the induced endomorphism of `W.Point`; `isogenyEndSubring` is the subring of
`AddMonoid.End W.Point` generated by them.
[`IsogenyHomDatum V₀ V₁`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_Isogeny_ConditionalCurrency.lean#L189)
is the between-curves version.

*The classification.*
`IsogenyEndDatum.exists_dualEndData_dual_mem_and_norm_eq_finrankAlong` produces,
for an endomorphism `D.pointEnd hN`, a
[`DualEndData`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L83)
whose dual lies in `isogenyEndSubring` and whose norm is `finrankAlong F ι` —
i.e. a dual isogeny with the degree predicted by the function-field extension.
`exists_restrictAlong_placeOfPoint_eq_add` says that for two endomorphism data
with nonzero sum there is a third whose place restriction at every point is the
sum of the two restrictions (transported through the point–place equivalence).
Together these are what the endomorphism-ring and Frobenius-trace consumers rest
on — the abstract module supplies `DualEndData.ofCharPoly`, the dual of a
`φ` satisfying `φ² − tφ + n = 0` — and `IsDualPair φ ψ n`
([`Def_DualIsogenyAPI.lean:9`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DualIsogenyAPI.lean#L9))
is where the algebra of dual pairs lives.

### 2.4 The bridge: kernel cardinality and base change

The two spines are joined by the cardinality of the kernel of the pushforward:
`natCard_ker_pointMapOfPushforward_eq_finrankAlong` states
`Nat.card (pointMapOfPushforward ι hι hfin hN).ker = finrankAlong F ι`.
The `…_of_separableAlong` variant replaces `[CharZero F]` by an explicit
`SeparableAlong` plus `HasPrincipalDivisors` hypotheses — the one "sibling" in the
slice that is a genuine variant rather than an implication (the topic §3 shows
why). On top sit the base-change nodes
(`exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward` and the
`isAddCyclic_…_of_baseChange_algHom` / `…_of_algEquiv_conj` relatives), which is
also where the already-ported WeightOne modularity/lattice material enters.

## 3. Why the public surface is fixed

The scout §3 records 401 out-of-D-S-cone consumers for the cluster, and the
`Theorems/Thm_*` wrappers are the only interface they see. So every one of the 47
public statements must land; the port has no freedom to simplify, merge or drop
statements. All of the freedom is in the *proof architecture*: which declarations
are shared, which are copied, and which implication the plain member of a pair
follows from. That is why the plan is a factoring plan and not a scope plan — the
contrast with the `prune.py` route decisions, where statements *are* dropped.

One consumer detail matters for the sibling rule: the plain and general members
of both `X`/`X_of_isAlgClosed` pairs have *different* consumer sets (the plain
`restrictAlong` feeds `exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples`
and `…_of_oddOrder`; the general one feeds the `fullKernelHom` chain), so both
must exist — but only one needs a proof.

## 4. The planning method: redundancy-first advice

The playbook's §2.4 says "deduplicate before coding". For a slice this redundant
that instruction needs an instrument, and `port_advise.py` is it; but its unit is
the declaration, which is the wrong unit for a *plan*. The method used here adds
one aggregation layer:

1. **Price the slice.** Resolve the subject's nodes to pin files
   (`frontier.py`/`fltdata.py`), take the raw `S_` line count.
2. **Advise per declaration.** `port_advise.py --nodes … --json …` reads the pin
   including `private`, matches statements with the checker's own normalisation,
   and reports substitutions, duplicates, binder-variants and per-target drags.
3. **Aggregate to statement groups.** Key every declaration across the target
   files: theorems by normalised statement, defs by name *and* type. This is the
   step that turns 4,607 declaration rows into ~1,930 distinct obligations and
   exposes the real budget.
4. **Factor into blocks.** Regroup the duplicate entries by *identical
   target-file set*. A block is a home: one file that every listed target imports.
   This replaces the pairwise "strongest factoring units" figure, which counts a
   four-file declaration six times.
5. **Collapse siblings.** For every target stem `<X>_of_<Y>` whose sibling `<X>`
   is also a target, compare the two declaration sets and the two public binders.
   Sub-multiset of binders with an identical conclusion means the specialisation
   is a free corollary; different hypotheses both ways means a genuine variant.
   The suffix alone is not evidence.
6. **Order by layers.** Build the DAG from the `S_` files' own `import` lines and
   topologically sort; homes (step 4) land before their consumers.

Steps 3–6 are implemented by the private companion `tools/deps/port_plan.py`
(`--selftest` covers the group key and the vetting rule); the topic file is its
output for this slice.

**Where this sits among the instruments.** The project now has four graph tools,
each answering a different question at a different time:

| tool | unit | question | direction |
|---|---|---|---|
| `prune.py` | node | which nodes can be dropped if machinery `R` is replaced | scope, before |
| `frontier.py` | node | what a target still needs from the pin | distance, before |
| `port_advise.py` | declaration | what to reuse/share/rename, per target | redundancy, before |
| `port_graph.py` | declaration | what got re-proved, per port module | redundancy, after |

`port_plan.py` is the aggregation over `port_advise`'s output — the plan layer. It
does not read the pin's proofs itself beyond the checker's statement split, so it
cannot disagree with `port_advise` about a single declaration; it only changes the
unit of account.

## 5. What would change the plan

* **A mathlib Vélu or place-dictionary development.** H2/H3 and the substrate
  blocks shrink. Check mathlib first (playbook §2.2) before each home.
* **A checker that compares `def` bodies.** The 70 suspect substitutions collapse
  and the already-in-port figure moves; the plan's shape is unaffected. The
  checker now has an advisory `--prop-bodies` pass for the `def … : Prop` case;
  it currently reports 183 identical / 1 textual difference (dot notation, an
  elaboration-spelling item) on the whole port, so it neither helps nor hurts this
  slice today.
* **A re-pin.** Both the line counts and the sibling overlap ratios are recomputed
  from the pin at `aa2d8b3`; re-measure before trusting them.
* **A dropped consumer.** Would let a public statement be pruned; §3 says none of
  the 47 is currently droppable. The `IsogenyEndDatum` classification in
  particular is substrate for the Frobenius-charpoly / rational-endomorphism
  consumers, not an end in itself.

## 6. Reproduce

The slice, the advice JSON and the plan report are produced by the exact commands
in [../lean/topics/velu/TOPIC-port-plan.md](../lean/topics/velu/TOPIC-port-plan.md)
§6; this note adds no separate measurement. The two-spine split in §2 is the
`import` edges the report extracts (very few Vélu nodes import an `IsogenyEndDatum`
node — the join points), and the shared-substrate claim is the set of
*cross-spine* blocks in its block table: the four explicit-Vélu files share 373
declarations among themselves, and the `IsogenyEndDatum` files share further
blocks with them — the place/ramification dictionary, the `ord`/`evalAt` block,
`pointEnd'_eq_of_seam`, `isFinitePlace_*`, `two_mul_ord_Y_eq_three_mul_ord_X` —
which is precisely the substrate that both spines' prologues re-develop.
