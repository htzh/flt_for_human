# W3 — the honest integral on a charted surface (the one-uniformization bridge)

Third wave of the aj subject, 2026-10-26. Parent note:
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) (§10.2, §10.4, §12.2, §13).
Predecessors: [PLAN-W1-stokes.md](PLAN-W1-stokes.md) (landed), [PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md)
(landed). Companion, dispatchable in parallel: [PLAN-W3b-hecke-equivariance.md](PLAN-W3b-hecke-equivariance.md).
Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

**Decision.** W3 is a *definitional* wave, and it is chosen by the criterion the subject actually runs on:
[§10.4](../TOPIC-abel-jacobi-port-structure.md#104-the-criterion-is-simplicity-not-verification)'s
**simplicity** — one definition per object, one proof per statement, fewest boundaries — not by distance
to A's mouth. It builds the missing survivor of the subject's two definitional decisions: an **honest
line integral of a 1-form on a charted complex surface**, and the transport that makes the pin's
`pathIntegral` a *theorem about it* rather than a definition of it.

The first draft of the wave plan ordered the waves by the mouth's premise list. That is a
verification-race criterion and it is the wrong one here. Under simplicity the ordering relation is
**"the survivor definition exists before anything is written against a loser spelling"**, which is a
relation between definitions and their consumers — *not* an edge in the citation graph, and not
"cheap premise of the target first".

**Status, 2026-10-26: round 2 is green and the first modules have landed — in `Reserve/`.** Two modules
build with no warnings, `check_port.py --all` is unchanged at **5927 ok / 0 mismatch / 0 missing, 271
modules**, and `#print axioms` is `[propext, Classical.choice, Quot.sound]` on all five headlines.

They are **shelved in `Reserve/`, not in the port** (2026-10-26): whether the port retains an honest
integral depends on the open question of §4b–§4c, `FLTForHuman` imports neither module, and the tree can
be checked in without the port carrying a speculation. `Reserve` is a default build target and walks by
`submodules`, so both stay green and the register lists them; the mathematics is preserved, which is the
point of the shelf rather than a deletion.

| module (in `Reserve/`) | what it contains |
|---|---|
| `Reserve/Analysis/Complex/ChartedCurveIntegral.lean` | `formOf`, `chartAt`, `chartedPath` (via `Path.map'`), `chartedCurveIntegral`, `eventually_sub_eq_of_eventually_hasDerivAt` (two local primitives differ by a constant), `chartedCurveIntegral_eq_sub` (the exact-form value theorem on a charted piece) |
| `Reserve/AlgebraicCurve/ChartIntegral.lean` | `placeForm`, `placeCurveIntegral`, `endpoint_sub_eq_of_isPrimitiveAlong`, **`pathIntegral_eq_sub_of_isPrimitiveAlong`**, `placeCurveIntegral_eq_sub` |

**The D1 answer, measured.** The transport splits, and only half of it needs path regularity:

* **the primitive half needs nothing.** `pathIntegral` is a `Classical.choose` over primitives, and
  *every* primitive gives the same endpoint difference, because two local primitives of one form differ
  by a constant (`eventually_sub_eq_of_eventually_hasDerivAt`), the difference is transported along the
  chart, `g - g'` is locally constant, and `unitInterval` is preconnected. No differentiability of `γ`
  is used: `pathIntegral ω γ = g 1 - g 0` for any `g` with `IsPrimitiveAlong ω γ g`. This lemma is what
  a consumer needs in order to *compute* a path integral, and the pin does not have it.
* **the charted half does.** `chartedCurveIntegral_eq_sub` takes the charted path's derivative, because
  an integral against `dz` is an integral. One glue item remains and is stated as a hypothesis
  `hcomp`: the chain-rule instance for a holomorphic `Ψ` composed with a real-differentiable charted
  path (it needs `fderiv ℝ Ψ z = (f z) • 1` from the ℂ-derivative). Everything else in the theorem is
  proved.

## 1. The four survivor decisions, and which of them are still missing

[§10.4](../TOPIC-abel-jacobi-port-structure.md#104-the-criterion-is-simplicity-not-verification)'s table
names a survivor for each duplicated notion. Measured against the port:

| # | one notion, two definitions | survivor | in the port? |
|---|---|---|---|
| 1 | the path integral: `periodAlongOf` (interval integral) vs `pathIntegral` (`if ∃ primitive …`) | A's honest integral | A's instance **is** ported (`periodAlongOf`); the **general charted-surface form is not** |
| 2 | the period lattice: `periodLatticeOf` vs `pathPeriodLattice` | A's, basis-free | **yes** (`ModularForms/EichlerShimura/PeriodOf.lean`, `ModularCurve/Period/`) |
| 3 | reciprocity / H₁ generation: A's ≈4,025 vs B's ≈3,628 | B's general form | no — and it must be written *on* survivor 1 |
| 4 | the genus: the two-route count vs RR | RR via `IsCurveOver` | **yes** — and the mouth's rank premise (267) already takes the RR route |

So the subject's definitional debt is **one object**, not four: survivors 2 and 4 are already the port's
shape, survivor 3 is a statement that cannot be written before survivor 1, and survivor 1's general
half is missing. That object is this wave. Everything else in the subject — A's dictionary, Abel's
theorem, the Hecke layer, the Tate identification, B's combinatorics — is a consumer whose spelling is
decided by it.

## 2. What the wave produces

Measured on mathlib `v4.34.0` **and checked by a scratch file** (`lean/ScratchW3Integral.lean`,
gitignored; compiles clean under `lake env lean -DautoImplicit=false`), which is what changes the price
and corrects three of this plan's first-draft citations:

* mathlib **has** the honest curve integral: `curveIntegral` for a 1-form `ω : E → E →L[𝕜] F` along a
  `Path a b`, with `curveIntegral_trans` (concatenation additivity), `curveIntegral_eq_intervalIntegral_deriv`,
  `curveIntegral_segment`, `CurveIntegrable`, and the primitive-existence lemma.
* the closed-form/homotopy cancellation exists but is a **method of `ContinuousMap.Homotopy`**
  (`φ.curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt`), not the free-standing name this plan
  first gave; the primitive-existence lemma is `Convex.exists_forall_hasFDerivWithinAt_of_fderivWithin_symmetric`.
* **`Path.map'` is the missing piece the plan wanted and did not know about**: it charts a path with
  only `ContinuousOn f (range γ)` — no global continuity of the chart — which is exactly the hypothesis
  a chart subdivision delivers. Item 2 is therefore nearer 250 lines than 400.
* **mathlib does *not* have the exact-form value theorem** (`∫ᶜ ω = g b − g a` when `ω = dg`); none of
  the `curveIntegral` lemmas is that, so item 4 is genuinely ours — but it is ~40 lines once
  `intervalIntegral.integral_eq_sub_of_hasDerivAt` is imported (`IntervalIntegral.FundThmCalculus`,
  which is *not* in `CurveIntegral`'s import closure — the scratch's first compile failed on exactly
  that).
* the **type discipline** the plan had understated: `curveIntegral` takes the form and the path in the
  *same* space, so a `ℂ`-valued chart form cannot be integrated along a path in `Place ℂ F` at all. The
  chart conjugation is not an implementation detail; it is the definition.
* `lebesgue_number_lemma_of_emetric` exists, so the subdivision is composition rather than new API.

**The port uses none of it** (`grep -rl curveIntegral FLTForHuman/` → 0 files), and the port's own
`pathIntegral`/`IsPrimitiveAlong`/`readDifferential` are available to state the bridge against
(`AlgebraicCurve/Defs/ComplexLineIntegral.lean`, 132 lines). So the wave is adoption plus chart glue,
not the ≈1–1.5k of new analysis §10.2 budgeted.

Four items, in dependency order:

1. **The 1-form read in a chart.** The pin's 101-line
   [`Def_AlgebraicCurve_ComplexLineIntegral.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_ComplexLineIntegral.lean)
   already has `chartRead` (evaluate through the inverse chart) and `readDifferential` (the differential
   read as a function `ℂ → ℂ`). Turn the latter into mathlib's shape,
   `curveForm v ω : ℂ → ℂ →L[ℂ] ℂ := fun z => smulRight 1 (readDifferential v ω z)` — three lines.
2. **The honest integral on a charted surface.** `Place.curveIntegral ω γ := ∑ over a chart subdivision
   of ∫ᶜ along the charted piece`, defined through `curveIntegral_trans`. The content is
   *well-definedness*: independence of the subdivision and of the chart, from the transition cocycle
   (`chartRead_apply` composes the two chart sources) — this is the wave's real proof.
3. **The subdivision exists.** Every path in a charted space is a finite concatenation of pieces each
   with image inside one chart source: finite subcover of the compact image `γ '' [0,1]` by chart
   sources, then `lebesgue_number_lemma_of_emetric` on `[0,1]` to get the partition, then
   `curveIntegral_trans` to add the pieces up. Each piece is charted by `Path.map'`.
4. **The primitive transport — the lemma that makes `pathIntegral` a theorem.** For a piecewise-`C¹`
   path and `IsPrimitiveAlong ω γ g` (the pin's definition: at each `t₀` a local holomorphic `Φ` with
   `Φ' = readDifferential ω` and `g = Φ ∘ chart ∘ γ` near `t₀`),
   `curveIntegral` of the charted piece `= g 1 − g 0 = pathIntegral ω γ`. Composition:
   `curveIntegral_eq_intervalIntegral_deriv`, the chain rule into
   `intervalIntegral.integral_eq_sub_of_hasDerivAt`, and a local-primitive gluing over the piece's
   compact image. This is the one item mathlib does not give (the exact-form theorem), and the scratch
   states it in the port's own vocabulary as `ScratchW3.TransportClaim`.

**Not in this wave**: the cell-wise residue theorem (it needs the dissection, and mathlib's
`curveIntegral_add_curveIntegral_eq_of_hasFDerivWithinAt` is *exactly* the interior-edge-cancellation
lemma §10.2 says that restructure needs), the **charted Stokes lemma that the residue restatement
consumes — which is bridge work and needs its own home, see §3.1/S3**, and the A↔B reconciliation (§6).

## 3. The scout, and what it can decide

Playbook §2.6 triggers on "genuinely new mathematics". With mathlib's `curveIntegral` in place, item 2–4
is *not* that: it is chart glue. **Both scout rounds have been run** — `lean/ScratchW3Integral.lean` (the inventory, the three misnamed
citations, `Path.map'`, and `TransportClaim` elaborating in the port's vocabulary) and
`lean/ScratchW3Round2.lean` (`endpoint_sub_eq_of_isPrimitiveAlong` proved, before it moved into
`AlgebraicCurve/ChartIntegral.lean`), both gitignored, both compiling clean under
`lake env lean -DautoImplicit=false` well inside the 2-minute cap. What is **still open** is one glue
item and one bookkeeping item:

* **~~Does the transport need a regularity hypothesis on the path?~~ Answered, and it splits** (see the
  status block): the primitive half needs none — landed — and the charted half needs the charted path's
  derivative, which is what D1 already assumes for B's proofs. So D1 stands as written and no longer
  has an open question behind it.
* **The chain-rule glue** (`hcomp` in both value theorems): from `HasDerivAt Ψ (f z) z` (ℂ) and
  `DifferentiableAt ℝ γc.extend t`, derive `HasDerivAt (Ψ ∘ γc.extend) (γ' t * f (γc.extend t)) t`. The
  missing step is `fderiv ℝ Ψ z = (f z) • (1 : ℂ →L[ℝ] ℂ)` from the ℂ-derivative, plus
  `HasFDerivAt.comp_hasDerivAt`. ~25 lines, no mathematics, and it is the only hypothesis in the two
  value theorems that is not discharged.
* **The subdivision's bookkeeping** (still the wave's own work): the finite chart cover of `range γ`,
  the induced partition of `[0,1]`, and the `CurveIntegrable` side conditions each piece carries
  (`curveIntegral_trans` demands them, and mathlib has no "continuous ⇒ `CurveIntegrable`").
* **~~Does the subdivision need an API mathlib lacks?~~ Settled by the scratch:** `lebesgue_number_lemma_of_emetric`
  is there and `Path.map'` supplies the charted pieces, so the subdivision is composition. The residual
  work is the bookkeeping (a finite chart cover of `range γ`, the induced partition of `[0,1]`, and the
  `CurveIntegrable` side conditions `curveIntegral_trans` demands — mathlib has **no**
  "continuous ⇒ `CurveIntegrable`" lemma, so each piece carries its own integrability hypothesis and
  the plan must budget for that).
* **Kill/correct criteria.** If item 4 cannot be proved for piecewise-`C¹` paths, the restructure of
  §10.2 is not available in that form and the parent's item 1 must be re-priced ("port `pathIntegral`'s
  machinery after all"). Record it rather than working around it. If it goes through, the outcome is a
  *corrected estimate*: items 1–4 below ≈800 written, i.e. §10.2's 1–1.5k was an overestimate.

### 3.1 Is the honest integral *sufficient for the purpose*? — not tested, and probing found a gap

Landed is not sufficient, and the distinction matters enough to be stated as criteria. "Sufficient" here
means one thing only: **B's statements can be proved without the primitive/jump/cotree bookkeeping**
(§10.2's deletion). Four criteria, of which one is met:

| # | criterion | status |
|---|---|---|
| S1 | the integral exists **along a path**, not per chart piece | **open** — needs the subdivision and additivity over `Path.trans` |
| S2 | the two spellings agree: `pathIntegral = placeCurveIntegral` | **open** — and it is not the bookkeeping this plan assumed; see below |
| S3 | the honest integral can carry the residue restatement (boundary = Σ edge integrals, interior edges cancelling) | **scoped out of W3, and that was a mistake** — see below |
| S4 | a consumer proves something with it | **impossible yet: the port has *zero* theorems about `pathIntegral`** — `AlgebraicCurve/Defs/ComplexLineIntegral.lean` is the definition layer and nothing cites it |

What *is* tested, and can be relied on: the mathlib inventory (§2), the D1 split — the primitive half
needs no path regularity and is proved, the charted half needs the derivative — and the exact-form value
theorem modulo the chain-rule glue.

**S2 is where the real difficulty is, and it is not integration.** The pin's `pathIntegral` is
chart-free *by construction* (a choice over primitives, each local, each in the chart at the *moving*
point `γ t₀`), while `placeCurveIntegral` is anchored at a fixed chart `v`. Relating them therefore
requires crossing charts, and that needs two things neither the pin nor mathlib has:

* **chart agreement**: `extChartAt 𝓘(ℂ,ℂ) x = extChartAt 𝓘(ℂ,ℂ) y` when `x` and `y` lie in one chart
  domain. Mathlib has no `chartAt`/`extChartAt` agreement lemma (searched `Geometry/Manifold/`); it is
  derivable from `extChartAt_source`, but it has to be written.
* **the chart-change law of `readDifferential`**: `readDifferential v ω` at the charted point equals
  `readDifferential v' ω` at the corresponding point times the transition factor. The good news is that
  the *coefficient* half is chart-free for free — `readDifferential v ω z = evalAt x (differentialCoeff ω)
  * deriv (chartRead v dCoordFn) z`, and `chartRead v f (c_v x) = evalAt x f` by `(extChartAt v).symm
  (c_v x) = x` — so only the `dz_v/dz_{v'}` factor has to be reconciled. The bad news is that this *is*
  the cocycle, it is the actual gate on the whole one-uniformization plan, and it appears **nowhere** in
  the pin (`Def_AlgebraicCurve_ComplexLineIntegral.lean` never compares two charts — it does not have
  to, since `pathIntegral` is built by choice). It is new mathematics, not bookkeeping, and it was
  priced as if it were inside item 2's 250–400 lines.

**S3 is a scope error this plan should correct.** §10.2's bridge price is two ingredients — "Stokes on
a bounded charted domain, plus 'path integral = sum of chart integrals'". This wave is the second
ingredient and the transport; the **charted Stokes lemma is not in it**, and calling the residue
restatement "B's" does not work, because the residue theorem is the thing the deletion is *for*. Since
the bridge must precede B, the Stokes half needs a home: a `W3c` (or the first item of B's own wave),
scheduled before B's residue theorem, never inside it.

**So the estimate stands only for what landed.** 249 written against 350–650 is not evidence that the
bridge is cheap: it is evidence that the *definitional* half is cheap. S1–S3 are unpriced, and S2's
cocycle is the only genuinely new mathematics in the subject's analytic spine.

**The decisive test is a pilot consumer, and it is not (a) but (b):** (a) the composite
`pathIntegral = placeCurveIntegral` for one chart, which is now known to need the chart-agreement lemma
first; (b) port **one small B-side pin node whose proof uses the primitive machinery** on the honest
integral and count what it still needs. (b) is the only test that answers the question, because the
purpose is a B proof, not an interface. Candidates, in increasing cost: the two 193-line Abel lemmas
(`abelJacobiDiv_mem_pathPeriodLattice_of_isPrincipal`,
`Divisor.isPrincipal_of_abelJacobiDiv_mem_pathPeriodLattice`), then the 677-line engine
`exists_regular_pathIntegral_sub_eq_of_abelJacobiDiv_mem_pathPeriodLattice`. Until one of them is done,
the ≈8.9k deletion of §10.4 item 1 and B's 61k re-price are unvalidated numbers.

## 4. D1 revised — the definition moves under the name; the API is built on the honest integral

The first draft of this section said D1 was "B's pinned statements keep `pathIntegral`; only its proofs
change", i.e. keep the pin's choice-definition and *relate* the honest integral to it. That is the wrong
shape, for the parent's own reason: §10.4 says one definition per object, and the survivor is the honest
integral. Keeping both and proving an equality between them is exactly the "two definitions plus bridge"
pattern the criterion forbids — and the bridge is where the cocycle bites (§3.1/S2).

**D1 (revised).** The port defines `pathIntegral` **as** the honest integral. The pin's definition

  `pathIntegral ω γ = if ∃ g, IsPrimitiveAlong ω γ g then g.choose 1 - g.choose 0 else 0`

is then recovered as a **theorem**, not a definition. Three things make the move sound:

* **statement fidelity is untouched.** The checker compares a declaration's *type*, not its body, so
  `pathIntegral` keeps its name, its type and its place in every pinned statement; `spec-pin` sees
  nothing. What changes is which function those statements are about — and by §10.5 that is the port's
  business, since the pin's mouths are the specification and the interior is not.
* **the fidelity bridge is the lemma round 2 already landed.**
  `pathIntegral_eq_sub_of_isPrimitiveAlong` says the honest definition agrees with the pin's choice
  wherever the pin's choice is meaningful. That lemma is what licenses the move; written against the
  honest definition it becomes the exact-form value theorem, and its current proof (the
  choice-independence argument) becomes unnecessary — there is no choice to be independent of.
* **it deletes `IsPrimitiveAlong` from the API.** B's proofs then never mention a primitive, which is
  the deletion §10.2 asks for.

**What the move does *not* buy.** It does not dodge the cocycle: the honest integral still has to be
*well defined*, i.e. independent of the chart chosen for each piece of the path, and that is the same
chart-change law of `readDifferential` (§3.1/S2). The cocycle is intrinsic to "integral of a 1-form on a
charted space", not an artifact of comparing two definitions. What the move changes is only what the
cocycle is *for*: one definition's well-definedness instead of an equality of two.

**The risk it introduces, which must be checked headline by headline.** Under the honest definition,
`pathIntegral`'s value on a wild path is whatever `curveIntegral` gives (it is total, but not the
primitive difference, and for non-rectifiable paths it carries no geometric meaning). B's statements
quantify over *arbitrary* paths, so each must be checked against the class its proof actually uses —
smooth arcs and cell boundaries. A statement that is false for wild paths under the redefinition is a
fidelity break, and it has to be found before the wave that ports it, not during.

## 4a. Sufficiency, measured on the deletion set instead of on one pilot

A single Abel lemma would show that B's *Abel* layer works and nothing about the rest, so the right
instrument is a node-by-node audit of the deletion set. The central node already shows why the audit is
tractable — the pin's statements there are **already honest-integral equations**, with primitives
appearing only as the choice mechanism:

`CellDissection.exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt` (1,240) states: there is a loop `γ` in
the skeleton such that for every `θ` with `0 ≤ ordDifferential θ` on the skeleton,

  `(∃ g, IsPrimitiveAlong θ γ g) ∧ pathIntegral θ γ = ∑ e, (Z j e : ℂ) * 𝒟.edgeInt θ e`

and `edgeInt` is *already* an honest interval integral (§10.2). So under the honest definition this node
is **"the integral along the subdivided loop is the ℤ-combination of the edge integrals"** — the
subdivision theorem, S1 — and the primitive-existence conjunct simply disappears. Its Kirchhoff/cotree
hypotheses (`𝒯`, `Z`, `hZk`, `hZd`, `hZ0`, `h𝒯path`, `hwalk`) are combinatorics about the dissection,
which survives whether or not primitives do.

That suggests the deletion set's 8,869 lines (5,495 + 3,374) split three ways, and the audit's job is to
assign every node:

| class | what it is | what it costs under the honest definition |
|---|---|---|
| **A — primitive bookkeeping** | primitives on cells, their jumps across edges, the cotree that kills the jumps (`exists_primitives_jump_eq_zero_of_dualTree` 1,395) | **nothing: it disappears** |
| **B — already an honest-integral equation** | loop integral = Σ cycle multiplicity · edge integral (`exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt` 1,240, and the rest of that family) | **S1** — subdivision + additivity over `Path.trans`, plus the dissection combinatorics |
| **C — genuine analytic content** | the residue theorem and the jump formula in residue form (`exists_int_pathIntegral_eq_sum_periods_add_sum_residues` 3,374, `two_pi_I_mul_sum_residue_mul_primitive_eq_sum_jump_mul_edgeInt` 1,209, `kirchhoff_and_jump_formula_of_arc_values` 665) | **S3** — the charted Stokes lemma, which is bridge work and must be scheduled before B |

So sufficiency is not one number and not one pilot: it is "class A vanishes, class B is S1, class C is
S3", plus "every remaining node's statement survives the redefinition" (D1's path-class check). The
audit is cheap — the statements are in `spec/statement_db.py` — and it should be done *before* the first
B module, because it is what the ≈8.9k deletion and B's 61k re-price rest on.


This is the decision that makes the wave safe, and it follows from §3. B's statements are pinned
(`ExistsAddEquivQuotientSubmodule…`, the reciprocity lemmas) and quantify over **arbitrary** `Path P Q`
with an `IsPrimitiveAlong` hypothesis. Those statements are transcribed verbatim (parent §10.5: the pin's
mouths are the specification and the interior is not). So the honest integral is **port-side and
unpinned**: it enters B's *proofs*, where every path is a concrete smooth one, and the bridge lemma of
item 4 is stated for piecewise-`C¹` paths. What §10.2 deletes is therefore the *interior* of B — the
5,495 lines of primitive/jump/cotree/Kirchhoff bookkeeping and the 3,374-line residue theorem written in
that language — not the `pathIntegral` spelling in B's headline statements.

That distinction is the difference between a wave and a research programme, and it is worth stating
because §10.2's phrasing ("replace `pathIntegral`") reads as if the definition itself were replaceable.

## 4b. The saving, priced — because `pathIntegral` and the honest integral are **not** the same object

The two are different functions, and that is the point: `pathIntegral` is *total and chart-free by fiat*
(it is `0` where no primitive exists, and `g 1 - g 0` where one does), while the honest integral is
*conditional* (it needs charted, integrable pieces and a chart-change law to be well defined). They agree
on regular paths carrying a primitive — which is every path B's proofs actually use — and they differ
elsewhere. So the honest integral is not a better spelling of `pathIntegral`; **it is the replacement of
the primitive**, and the saving is exactly the cost of everything whose only job was to produce primitives
and control their jumps.

That the pin needed such machinery is visible in the pin itself: `CellDissection.edgeInt` (`:145`) is
*already* an honest interval integral — `∫ s in φs(i)..φs(i+1), bdryIntegrand θ s` — while `pathIntegral`
is choice-based. B therefore runs on **two integral notions**, and the jump / cotree / Kirchhoff block is
the translator between them. The residue theorem's own conclusion mixes them
(`pathIntegral θ γ = Σ periods + Σ residues`, with the periods given as `edgeInt`-style data).

So the decision is binary, and it should be priced as one:

| | keep both (port the pin's proofs) | absorb `pathIntegral` into the honest integral |
|---|---|---|
| **deleted** | nothing | ~8,869 pin lines (§10.2: 5,495 translator + 3,374 residue theorem) |
| **also enabled** | nothing — A's row-2 (≈4,025, §10.4 item 3) stays uninstantiable, because A's periods are honest integrals and B's would not be | the item-3 deletion, because both halves then speak one language |
| **added** | 0 | honest integral: 249 landed + ≈250 owed (chain-rule glue ≈25, subdivision ≈150, `Path.trans` additivity ≈40, chart agreement ≈60); **the cocycle** (unknown); charted Stokes S3 ≈300–600; residue theorem re-derived ≈500–800; class-B re-proofs ≈300–600 |
| **spend** | ≈8,869 pin lines transcribed at ratio 1.0–1.3, low risk | ≈1,700–2,900 written + the two unknowns, design risk |
| **net** | 0 | **≈6,000–7,200 pin lines on B, ≈10,000–11,000 if item 3 comes with it**, plus one definition instead of two and a second consumer for W1's landed 2,768 |

**The two unknowns are the whole question,** and neither is line-countable yet:

1. **the cocycle** — the chart-change law of `readDifferential`. If it lands at a few hundred lines, the
   option is comfortable; if the chart structure on `Place ℂ F` does not connect to `readDifferential`'s
   definition cleanly, nothing here can be built and Option 1 is the port. It is *binary*.
2. **S3, the charted Stokes lemma** — applying W1's Pompeiu identity on a charted cell with the boundary
   expressed as honest edge integrals. W1 is already landed (2,768 written) and this is its second
   consumer, so the cost is smaller than it looks, but it is where the residue theorem's 3,374 lines are
   re-earned.

**Decision rule, and the parent's own caveat.** §10.4 says at 3k instead of 1.5k the later duplications
stop paying. The analogous threshold here: if cocycle + S3 together exceed ≈3,000 lines, the saving on B
alone (≈6,000) still pays but the margin is thin; if they exceed ≈6,000, Option 1 is right and the honest
integral should stay a *supplement* (useful for the §9.2 prelude and for A, not as B's foundation). The next scout
was therefore the **cocycle alone**, before any of the remaining items (a)–(d) of §10 — it has been run,
and §4c is its outcome.

## 4c. Scout round 3 — the cocycle, and what it turned out to be

The cocycle was the binary in §4b. Scouting it (`ScratchW3Cocycle.lean`, gitignored) resolved it **against**
the cheap reading, and in a way that also weakens §10.2's premise. Three findings, in order of importance.

**F1 — the coefficient half is free, and proved.** `chartRead_chartAt`
(`chartRead v f (chart_v x) = evalAt x f` for `x ∈ (extChartAt v).source`) compiles: the *coefficient* of
`ω` read in a chart is chart-free at the point, because `chart_v.symm (chart_v x) = x`. That half is ~6
lines and needs nothing.

**F2 — the coordinate half is NOT a chain rule, because `dCoordFn` is chosen per place.** The pin's chart
construction (B0's `exists_chartedSpace_…`, 482 lines, `needed(653) = False`) builds
`chart v w = evalAt w (t v)` with `t` from `choose t ht using fun v => Place.exists_ord_eq_one v`, while
`readDifferential` uses `dCoordFn v`, which is `Classical.choose` of the *different* theorem
`exists_ord_eq_one_and_dCoord_eq`. Two independent choices of "a uniformizer at `v`". So
`chartRead v dCoordFn` is a holomorphic function with a simple zero and `≠ id` in general, and the two
readings `readDifferential v ω`, `readDifferential v' ω` are the chart expressions of *one* `ω` only after
using the global Kähler identity `differentialCoeff_v ω • d(dCoordFn_v) = ω = differentialCoeff_v' ω •
d(dCoordFn_v')`. What the cocycle therefore needs is the **chart-expansion/differential dictionary**:

  `(d(g)/d(h))` read in a chart `=` `(g's chart expansion)' / (h's chart expansion)'`,

plus the chain rule for the analytic transition. The transition's analyticity *is* in the pin
(`analyticAt_transition`), so that ingredient is free — but the dictionary is **absent from the pin and
from the port**, because the pin never compares two charts (it never has to: `pathIntegral` is built by
choice, and `IsPrimitiveAlong` uses the chart at the moving point only). So the cocycle is a real,
**unbounded** lemma, not the 100–150 lines §4b allowed for.

**F3 — B's honest integral already exists, and it is not the one this wave would build.** The pin's
`CellDissection.edgeInt` is an honest interval integral *in one fixed chart per cell*, because the
dissection carries its own parametrized boundary (`(𝒟.cell C).R.φs`, the polygon word). So B never needed a
chart-*invariant* global integral: it needed per-cell parametrized integrals (which it has) plus a way to
compare them with `pathIntegral` (which is the jump/cotree machinery). The wave's deliverable would be a
global chart-invariant integral that no B statement asks for directly.

**The consequence for §4b's arithmetic.** The absorption's premise was "the primitive machinery is
replaceable by an honest integral". F3 says the machinery is not the price of *having* an integral — an
integral was always there, per cell — it is the price of comparing it with the choice-based `pathIntegral`
that B's **statements** are written in. F2 says that comparison is exactly the unbounded cocycle. So the
saving is not "free once the integral exists"; it is "free once the comparison exists", and the comparison
is the hard part. Under §4b's own decision rule — above ≈3k the B saving is thin, above ≈6k keep both —
**the honest reading of the current evidence is: keep both, port the pin's proofs, and keep the honest
integral as a supplement** (it is landed, upstreamable, and it is the natural home for A's
`periodAlongOf`-side facts and for the §9.2 prelude).

**Which object is needed for which question** — the scope table this wave's writing kept blurring, so
it is stated once:

| question | needs `pathIntegral` (choice-based) | needs the honest integral | needs the cocycle |
|---|---|---|---|
| B's own theorems, as the pin states them | **yes** — it is in their statements | no | no |
| computing a `pathIntegral` value in a proof | yes, plus `IsPrimitiveAlong` | only as a *shortcut*, and then yes | yes |
| B's analytic layer rewritten (§10.2's 8.9k) | no (it would be replaced) | **yes** | **yes** |
| the A↔B translation (§9.5 item 3, `TOPIC-translation-a-b.md` field 5) | **yes** (it is B's side of the comparison) | **no** — both integrals are chart-free | **no** |
| A's own period facts, and the A∩B prelude | no | useful, not required | no |

So the two claims, separated: **`pathIntegral` is needed and stays; the honest integral is needed for
nothing except the 8.9k rewrite, and that rewrite needs the cocycle.** "Both sides are chart-free" is a
statement about the *comparison* the translation layer needs — A's explicit integral and B's primitive
difference are compared pointwise, so the comparison never goes through charts and never meets the
cocycle. It is not a claim that the honest integral is worthless: what it buys that nothing else buys is
the 8.9k, and that is the one purchase currently priced as unbounded.

**What would reopen it** is one lemma, and it is worth stating precisely: the chart-expansion/differential
dictionary of F2. If it lands at a few hundred lines, the comparison `pathIntegral = ∫` becomes reachable
and §4b's ≈10k is back on the table; if it is a thousand lines of Kähler bookkeeping, the absorption is
dead and the 8,869 pin lines should be ported as they stand. That is the next scout to run, and it should
be attempted *before* the four small items of §10, because it is the only one of them that can change the
verdict.

## 5. Homing

The wave's two modules are **shelved at `Reserve/Analysis/Complex/ChartedCurveIntegral.lean` and
`Reserve/AlgebraicCurve/ChartIntegral.lean`** while §4b–§4c's question is open; the table below is the
home each takes *if the absorption decision flips*, kept because that is what a later reader needs.

| module | items | why |
|---|---|---|
| `FLTForHuman/Analysis/Complex/ChartedCurveIntegral.lean` (if retained) | 1, 2, 3 | it quantifies over an arbitrary `ChartedSpace ℂ X`, a path and a differential read in charts — no curve, no place, no modular vocabulary. It is a mathlib supplement to `MeasureTheory/Integral/CurveIntegral/`, and it joins W1's supplements (`Dbar`, `Pompeiu`, `MeromorphicResidue`, `CircleIntegralResidue`) in the directory that already holds exactly this kind of module. |
| `FLTForHuman/AlgebraicCurve/ChartIntegral.lean` (if retained) | 4 | the transport is stated with `Place`, `extChartAt`, `IsPrimitiveAlong` and `pathIntegral` in it, so it is curve-side glue and must not sit in `Analysis/`. This module is the seam, and it is the one place the wave knowingly crosses from analysis into the pin's vocabulary. |

If a reviewer prefers to keep the whole thing analysis-shaped, items 1–3 are independently upstreamable
and mathlib would home them under `Mathlib/Geometry/Manifold/` or beside `CurveIntegral/`. The port has
no `Geometry/` directory and should not grow one for one module.

## 6. What it unlocks, and the ordering constraint it imposes

* **Item 1 of §10.4 (≈8.9k of B)** becomes a *rewrite on this definition* instead of a port: the
  deletion is B's 5,495 primitive/jump lines and the 3,374-line residue theorem in that idiom, minus
  what this wave and the residue restatement cost. That is the biggest single line item in the subject,
  and it is now gated only on this wave.
* **Item 3 of §10.4 (A's ≈4,025)** becomes an *instantiation*, but only after two further pieces that
  this wave does **not** contain, and the sequencing is where my earlier reading was wrong:
  1. **the reconciliation** — "A's `periodOf γ` is the loop integral at `pt I`" (parent §9.5 item 3: the
     gate with no node in the pin). It needs A's `ComplexPlaceDictionary{,Of}` (45 nodes / 16.9k, in
     `needed(653)` anyway) **and** the `Γ_H` cusp-form ↔ `regularDifferentials` identification, which the
     pin has only at `Γ₀(N)` (`exists_linearEquiv_tensor_regularDifferentialsBar_cuspForm`, 323);
  2. **B's general reciprocity**, rewritten on this wave's integral.
* So the constraint is: **A's row-2 family must not be written before this wave + the dictionary + the
  `Γ_H` identification + the reconciliation.** Otherwise the port pays the 4,025 twice — once now, once
  at the rewire — which is precisely §10.5's "a definition transcribed against cannot be deleted later",
  applied one level up, at proofs. My earlier conclusion ("the bridge is pre-B, not pre-A, because A's
  cone contains no `pathIntegral`") was a citation-graph reading of a writing-order question, and it is
  withdrawn: A's row-2 proofs are the thing the bridge rewrites, so the bridge is prior to them even
  though no edge points at it.

**The trade, stated as it will be paid.** Item 3 saves A's 4,025; against that, B's 3,628 comes back as
B (it is the survivor's proof, not a saving), the bridge costs what this wave costs plus the residue
restatement, and the remainder is the rewire of A's consumers. The saving is therefore real but it is
the *A-side* 4,025, and it is only collectable if the sequencing above holds — which is why the number
in §10.4's table (74k → 61k, i.e. 13k) is right at the subject level and wrong at the P1 level. The
measured cone facts behind that: A's five row-2 nodes are all `needed(653) = True`; B's two
(`exists_loops_pathIntegral_reciprocity_raw` 2,388, `exists_loop_pathIntegral_eq_sum_cycle_mul_edgeInt`
1,240) are both `False`, as are B's mouth, B's hub and the two-route count's three nodes (80, 81, 144).
So of §10.4's four duplications, only item 3 names a survivor that lies inside A's cone — and that is
exactly why it is the only one that constrains the order.

## 7. What this does to W4 (and to "P1 then B")

The smoothed-fundamental cluster is re-cut, and only one part of it is a wave yet:

* **W4a — the modular computation (survives every decision, 13 nodes / 6,308 lines minus the row-2
  fifth = ≈3,931, plus `Def_ModularCurve_SmoothedFundamental.lean` 187):** `smoothedFundamental`'s
  definition module, the ∂̄-over-the-fundamental-domain pair, the smoothed bump
  (`contDiff_and_finsum_smoothedFundamental_eq_one` 509, `tendsto_integral_mul_smoothedFundamental`
  478, `exists_invariant_localModel_dbarLogDeriv_eq_sum_finsum_translate_of_finiteIndex` 1215), the
  side pairing (`integral_dbar_mul_cuspForm_gammaFundamentalSet_eq_sidePairing` 841) and the orbit-rep /
  stabiliser leaves. These compute the modular instance whatever the survivor is: they are the "A can
  lend analysis to B" half of §10.3, and W1's ∂̄ layer is consumed here.
* **W4b — A's row-2 reciprocity (810, 874, 693 inside the cluster; 1052, 596 outside = 4,025):** **not
  scheduled.** Its status is decided by §6's sequence: instantiation if the bridge + reconciliation +
  B's reciprocity are scheduled ahead of it, otherwise a ported duplication with its price recorded in
  [CARRY-FORWARD.md](../../CARRY-FORWARD.md). Do not open it "because it is ready".

And the larger consequence, which belongs to the parent note rather than to a wave: under the simplicity
goal **"P1 then B" is not a free ordering for the pieces in items 1 and 3.** Those pieces are written
once, after the bridge — B's analytic layer and A's row-2. What stays freely orderable is everything
else: A's dictionary, Abel, Hecke, Tate; B's cell-dissection combinatorics; the cardinality packaging.
That is a smaller reordering than it sounds, because the dictionary (16.9k) and the dissection (≈10k)
have to be written anyway and in either order.

## 8. Budget

| item | estimate | basis (scratch-checked where marked) |
|---|---:|---|
| 1 + 2 (form + honest integral + cocycle) | 200–350 | form + charted path **checked**; `curveIntegral_trans`/`Path.map'` do the algebra; the cocycle is the work |
| 3 (subdivision) | 100–200 | `lebesgue_number_lemma_of_emetric` **checked**; the growth risk, but it is composition now |
| 4 (primitive transport) | 50–100 | FTC **checked**; the exact-form theorem is ours (**checked absent** from mathlib) |
| **total** | **≈350–650 written** | against §10.2's 1–1.5k for the whole bridge |

Small in lines and large in consequence: it is the gate on ≈12.9k of deletion (§10.4's 74k → 61k). If
the scout returns 1.2k instead of 800, the wave is still right; if it returns "no equality without a
regularity hypothesis that B's statements do not have", then D1 is already the answer (proofs, not
statements) and only the cell-wise residue restatement needs re-pricing.

## 9. Verification

Unlike W1/W2 there is no `spec-pin` for most of this — items 1–3 are new port-side statements with no
pin node (the pin never had an honest charted integral), so:

* a header note saying so, and a `spec-pin` wire only for item 4 if its statement is the pin's
  `pathIntegral` equation (check `spec/statement_db.py show` before guessing — the pin has
  `pathIntegral` and `IsPrimitiveAlong` as *definitions*, so any wire is to a definition module, which
  `spec/old_check_stmts.py`'s `SOURCES` covers for the def modules already transcribed);
* the definition modules touched (`Def_AlgebraicCurve_ComplexLineIntegral.lean`'s `chartRead`/
  `readDifferential`) must not have their statements changed — this wave adds, it does not edit;
* `#print axioms` clean; no `sorry`; `grep '^import FLTForHuman'` on the new `Analysis/` module must be
  empty (the layering assertion W2b established);
* `lake build` green on the two new modules; every command under 2 minutes with the
  `flock .lake/flt_build.lock timeout 110 lake env lean -DautoImplicit=false` loop;
* a mutation test on the two headline statements (item 2's well-definedness, item 4's transport).

## 10. First moves

1. ~~Scout round 1~~ — **done** (`ScratchW3Integral.lean`): the inventory, the three citation
   corrections, `Path.map'`, the absent exact-form theorem.
2. ~~Scout round 2~~ — **done** (`ScratchW3Round2.lean`), and it answered D1: the primitive half needs no
   path regularity and is landed; the charted half needs the charted path's derivative.
3. ~~`Analysis/Complex/ChartedCurveIntegral.lean`~~ — **landed in `Reserve/`**, 6 declarations, 0 warnings.
4. ~~`AlgebraicCurve/ChartIntegral.lean`~~ — **landed in `Reserve/`**, 6 declarations incl.
   `pathIntegral_eq_sub_of_isPrimitiveAlong`, 0 warnings. `check_port.py --all` unchanged
   (5927 / 0 / 0, 271 modules); `#print axioms` clean on all five headlines.
5. **What is still owed, in order:** (a) the chain-rule glue `hcomp` (§3) — ~25 lines, no mathematics;
   (b) the chart subdivision with its `CurveIntegrable` bookkeeping (§3) — the one item with real
   growth risk; (c) `placeCurveIntegral` additivity over `Path.trans`, which is what turns the pieces
   into one integral and needs a `Path.map'`-respects-`Path.trans` lemma that mathlib lacks; (d) then
   re-price item 1 of §10.4 (B's analytic layer) with the measured ratio and hand the number to whoever
   schedules B — that re-price is still this wave's real deliverable.
