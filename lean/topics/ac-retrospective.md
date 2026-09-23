# The `AlgebraicCurve` effort — closing review

**Status (2026-09-23): the effort is complete.** This is the retrospective on the
`AlgebraicCurve` port for `ModularCurve.heckeOperatorsCommuteBar`, written after the
reviewer's T7 made the divisor exchange unconditional. It reviews the decisions, the
mathematical clarity, the redundancies cut, and what was *not* cut, and records the
first experiment in running a port as **two coding sets dispatched to two agents, with
the capstone reserved for the human**. The retired blueprint is
[PORTING-AC.md](PORTING-AC.md) (the planning record); the measured costs are
[../logs/ac-port.md](../logs/ac-port.md); the mathematics is
[../../math/009-hecke-jacobian-commute.md](../../math/009-hecke-jacobian-commute.md).

FLT is pinned at `aa2d8b3`; mathlib at `v4.34.0`.

## 1. What was delivered

The whole `AlgebraicCurve` cone of `ModularCurve.heckeOperatorsCommuteBar`: **65
theorem nodes** (63 `AlgebraicCurve.*` in 5,210 raw `S_` lines, plus the two generic
group-theory nodes), **7 definition modules**, and the **capstone** — as 17 modules
with no schemes, no curve axiom, and mathlib as the only dependency.

| check | result |
|---|---|
| `lake build` | **4,034 jobs, 0 warnings, no `sorry`** in `FLTForHuman/` |
| `spec/check_flt_statements.py` | **618 identical (34 promoted from pin-`private`), 0 mismatched, 0 missing**, 14 exemptions (632 port declarations) |
| `spec/AlgebraicCurveConsumer.lean` | **0 errors**, Zones A–J, with a real cross-module composition per zone |
| `#print axioms` on the capstone, the local exchange, the bifibre count, `hasPrincipalDivisors_of_transcendental`, the two generic engine lemmas, the interface leaves | `[propext, Classical.choice, Quot.sound]` |
| commits | none — the working tree is the hand-off |
| size | **5,559 lines, 328 public declarations** |

The modules, in dependency order:

| module | role | lines |
|---|---|---|
| `Defs/{Place, Divisor, PushPull, PlacesOverDVR, Correspondence, SemilinearAut, RatFuncPlaces, IntegralAdjoin}` | AC0 + T1: the vocabulary and the outbound ord/valuation interface | 2,617 |
| `Defs/PlaceDictionary` | T2: the fibre-centre dictionary, written once | 398 |
| `WeilExchange/FiberOverCount` | T2: `fiberOver`, `le_finrank`, `inertiaDeg_pos` | 122 |
| `WeilExchange/GaloisRamification` | T3: Galois invariance of restriction/ramification/inertia | 195 |
| `WeilExchange/Transport` | T4 + the shared prelude | 304 |
| `FieldTheory/FiniteGroupAction` | T5: the two generic orbit/index statements | 264 |
| `WeilExchange/Bifibre` | T5: the bifibre count | 361 |
| `WeilExchange/LocalExchange` | T6: the local exchange via the normal closure | 206 |
| `PrincipalDivisors/RatFuncDegree` | T8: the `P¹` places and degree | 435 |
| `PrincipalDivisors/Transcendence` | T9: `HasPrincipalDivisors` by norms | 514 |
| `WeilExchange/DivisorExchange` | T7: the capstone | 143 |

**The three generic inputs of `math/009`'s exchange reduction are now ported
theorems, not references:** the Weil exchange
(`Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`),
`separableAlong_of_charZero`, and `HasPrincipalDivisors` for the modular function
field. `finiteAlong_comp` and the `Pic0` descent sit beside them in
`WeilExchange/Transport.lean`.

## 2. The decisions that shaped it

| decision | why | outcome |
|---|---|---|
| **Definitions first, AC0 as its own topic** | the cone's interface is its definitions; a broken `Place` shape would redo everything | the `Place` shape held from AC0 to the capstone; the four instances needed no help and set every downstream `rfl` bridge |
| **Adopt `Place` *as* a `ValuationSubring`, not a parallel vocabulary** | mathlib alignment is real here: `HeightOneSpectrum`, `Ideal.relNorm`, `IsDiscreteValuationRing` are the interface | the bridge is built inside the structure; no restatements of mathlib's ramification API |
| **One home for the four-copy fibre dictionary** | the pin copies 17 declarations byte-for-byte into four files | `Defs/PlaceDictionary.lean`, 398 lines instead of ≈737 content lines; T2, T5 and T9 all consume it |
| **One home for the three-copy `BifibreDev` prelude** | the pin repeats `restrict_restrict` and five tower rows in `bifiber`/`exchange`/`divisor_exchange` | T4's `WeilExchange/Transport.lean` owns them; T5/T6/T7 import — the capstone's off-diagonal case is a rewrite by the imported lemma |
| **The interface lives with its objects** | the FFG interface-tier precedent: the interface is a *usage* property and modules are named for *mathematical roles* | no `OrdInterface.lean`; T1's leaves are in `Defs/Place.lean`/`Defs/RatFuncPlaces.lean`/`Defs/IntegralAdjoin.lean`, and the interface is a table in the log |
| **Statements from the `Theorems/` wrappers, diffed mechanically** | a wrong statement is maximally expensive; a wrong proof cheap | 618 statements verified; two *work orders* had wrong `S_`-file binders and the wrapper rule caught both |
| **Drop by `grep -c`, never by inspection** | "redundant" is a claim about the graph, not about prose | every dropped definition-module declaration has a corpus count in the log; the one checker collision (`correspondence`) is an explicit reasoned exemption |
| **Two coding sets, one agent each, human capstone** | context is the binding constraint; route cost dominates line count | see §6 — the split kept each agent's context on one story, and the capstone consumed SET 2's output as its review |
| **The consumer is the definition of done** | a green library can still fail to compose | the consumer caught the interface early and its Zone J is a real composition of T7 with T4 |
| **No `Spine.lean`** | FFG's conditional capstone existed because its theorem had seven unported premises | here every T7 premise is an argument or a `T9`-*proved* instance; the AC layer is unconditional, and the device would have been ceremony |

## 3. Math clarity achieved

**The mathematics is three abstract statements, not 5.5k lines.**

- the **fibre-over identity** `∑_{w ∣ v} e(w) f(w) = [F' : F]` — mathlib's
  `Ideal.sum_ramification_inertia_eq_finrank` read through the fibre-centre
  dictionary (`Defs/PlaceDictionary.lean`, `WeilExchange/FiberOverCount.lean`);
- the **orbit-intersection count** `|H₁x₁ ∩ H₂x₂| · |X| = |H₁x₁| · |H₂x₂|` and the
  **index product** `H₁H₂ = G` — the two statements mathlib does not have, in
  `FieldTheory/FiniteGroupAction.lean` beside `CommonRoot.lean`;
- the **norm formula** `ord_v(N_{F'/F} f) = ∑_{w ∣ v} e(w) f(w) ord_w(f)` — T9's
  `Defs/PlaceDictionary` consumers, in `PrincipalDivisors/Transcendence.lean`.

Everything else is concretisation: places, divisors, and the transports that state
these for the modular function fields. The port's contribution to clarity is to have
said so once, in three small modules, instead of discovering it inside 800-line files.

**The two-route structure is visible in the file tree.** After T2 the exchange route
(`WeilExchange/Ord`-free: `GaloisRamification → Transport → Bifibre → LocalExchange →
DivisorExchange`) and the principal-divisors route (`PrincipalDivisors/RatFuncDegree →
Transcendence`) share nothing but `Defs/`. A reader can see that the AC layer is
`Defs/` plus two independent theories, which is exactly `math/009`'s decomposition.

**The Galois-to-separable reduction is a theorem, not a remark.** `LocalExchange.lean`
exposes `BifibreW2.exchange_of_isGalois` and
`Place.sum_ramificationIndex_mul_inertiaDeg_bifiber_of_isSeparable`; the normal
closure `Env F E` and its six tower instances are `private` plumbing. The blueprint's
"prove it in the Galois case, then reduce" is now checkable in two declarations.

**The `P¹` base case is visibly the base case.** `PrincipalDivisors/RatFuncDegree.lean`
classifies the places of `K(t)` and proves `degree_eq_zero_of_forall_eq_ord`; T9 then
transfers it by norms. `deg_ofHeightOneSpectrum` needed no new code at all — AC0 had
already written it — which is the sharpest evidence that AC0 chose the right
vocabulary.

## 4. Redundancies cut, measured

| redundancy | pin | port |
|---|---|---|
| the fibre dictionary, repeated per file | 4 copies, ≈737 content lines | **once**, 398 lines (`Defs/PlaceDictionary.lean`) |
| the `P¹` classification prelude | ≈90 raw private lines × 3 files | AC0 publishes every piece but the dichotomy; one private dichotomy in T8 |
| the `BifibreDev` prelude (`restrict_restrict` ×3, five tower rows ×2) | 3 files, 3 namespaces | **once**, public, in `WeilExchange/Transport.lean` |
| `hasPrincipalDivisors_of_finiteDimensional_ratFunc` | 2 byte-identical copies | **once**, public, verified against both wrappers |
| `deg_ofHeightOneSpectrum` / its `WFf` residue block | `S_` copy + `Def_RatFuncPlaces` copy | AC0's single copy; T8 wrote **10 of 11** nodes |
| `p2m_*`/`attribute` scaffolding | ≈1,888 of 5,423 raw `S_` lines (35%) | never written |
| definition-module declarations off the cone | ≈45% of 2,867 lines | dropped, each with a corpus `grep -c 0` |

Two secondary cuts the pin's own structure made easy: the chart block of
`PlacesOverDVR` survives only as far as `Place.center` needs it (`private`), and the
`RatFuncPlaces` `placeOfPoint`/`Place.Congr` section is not written at all (measured
unused — the cone mentions it only inside `attribute [-simp]` noise).

## 5. What was deliberately not cut

- **T9's `relNorm`/`normalizedFactors` norm block.** The blueprint asked for an audit;
  the measured answer is that **none of the ten declarations is reducible** to a
  mathlib `relNorm` lemma — mathlib has `Ideal.relNorm`,
  `Ideal.relNorm_eq_pow_of_isMaximal` and `Ideal.relNorm_singleton`, but not the
  fibre-centre inertia computation nor the `normalizedFactors` factorisation. It is
  the irreducible core and was transcribed as written.
- **The parts of the pin definition modules other consumers need.** The Galois
  `≃ₐ`-action on `Place`/`Divisor`/`Pic0`, `Pic`/`torsion`/`AbelJacobiCard`,
  `SemilinearAut`'s `Pic0`-torsion action, `Place.card_fiberOver_eq`/
  `fiber_eq_fiberOver`, `Place.finite_setOf_forall_mem_and_ord_pos` and
  `placeOfPoint`/`Place.Congr` are outside this cone but are real API for the modular
  Hecke/Galois-rep and Riemann–Roch layers. Deferred, not judged worthless, each with
  a count.
- **Three statements keep the pin's deprecated `Ideal` text** under a reasoned
  `set_option linter.deprecated false`, because the v4.34 replacements changed
  argument order or shape and migrating them would have been a shape adaptation of
  T2's Assembly, not a rename.
- **`Place.FiniteResidue`**, a 3-line class the cone does not exercise, is kept as
  real API.
- **Repo-wide prelude dedup.** The port writes the dictionary and the prelude once
  *for its own cone*; deduplicating the whole `AlgebraicCurve` layer across FLT is a
  larger, separate effort.

## 6. Predictions vs measurements

**Cost is shape risk, not line count — and this time the line budget was the accurate
instrument and the risk register was the pessimistic one.**

The blueprint budgeted ≈5.1k–5.9k written lines. Measured: **5,559 module lines**
(plus 456 for the consumer), at the lower-middle. SET 2 was priced at 1,800–2,140 and
measured 1,780 module / 2,029 including the consumer. The two structural savings the
plan predicted are real and measured (the dictionary, the prelude).

The risk register, by contrast, over-warned:

- **T5's Galois-orbit count did not need the route it was budgeted for.** The two
  statements mathlib does not have — the orbit-intersection count and the index
  product — were **transcribed unchanged** from the pin against mathlib v4.34's
  orbit–stabiliser API. The scout that established this cost **3.2 s** and preceded
  any port module. This is the strongest instance yet of the playbook's rule that
  *statements dictated ⇒ cheap*, even for generic mathematics mathlib lacks.
- **T6's normal-closure instance block did not materialize.** The four
  `isScalarTower_env_*` tower instances transcribed literally; the module built first
  try. `Env`/`algebraEnv`/the six instances are `private`, and `algebraEnv` stayed
  `@[reducible]`.
- **T8's `P¹` instance diamonds did not materialize.** One instance set, no `'`-copies,
  no `synthInstance` help; Ostrowski (`RatFunc.valuation_isEquiv_infty_or_adic`) was
  consumed directly.
- **T9's `PerfectField` risk fired without help** — a private
  `CharZero v.toValuationSubring` instance and `IsFractionRing.charZero` were enough.
  No statement was weakened.
- **The predicted non-events were non-events**: the `p2m_*` scaffolding could not
  bite, and the rewrite-search gap needed only one named workaround (the deprecated-
  module import trap), not a systematic bridge library.
- **One prediction was wrong in the blueprint's favour and one against.** Risk 4
  ("write against the new API") assumed the `Ideal` deprecations were drop-in
  renames; they are not — `Ideal.inertiaDeg'` moved argument order, and the old
  `Ideal.sum_ramification_inertia` lives in a deprecated *module* whose replacement
  changed the sum's shape. Conversely, risk 2 (the `Place` bridge) and risk 3 (the
  `letI` walls) were real decisions but not costs.
- **The real recurring cost was API drift, not mathematics**: `Set.mem_setOf_eq`,
  `zero_le'`, `if_pos`/`if_neg`, `RatFunc.inftyValuation`'s new `DecidableEq`,
  `Polynomial.degree_sub_lt`, `prime_of_normalized_factor`,
  `finiteDimensional_adjoin`, and the `Ideal` ramification API. None changed a
  statement; each is in the log's friction section.

**The process experiment.** Running the port as two sets — SET 1 (AC0, T1–T4) and
SET 2 (T5, T6, T8, T9), each a single coding agent, with the T7 capstone reserved for
the human — worked, and the reasons are recorded because they are not obvious:

- **The sets were split on the mathematical fork, not on size.** T2 is the shared
  prerequisite of both routes, so SET 1 ended there-plus-transport and SET 2 began
  with the two routes' independent halves. Each agent therefore carried one coherent
  story, and neither needed the other's context.
- **SET 2's work orders were written after SET 1 was reviewed**, against the modules
  that actually existed. That is why the T4 prelude and the T2 dictionary are
  *imported* in every SET-2 topic rather than re-derived: the work orders name the
  real declarations. It also let the manager's recon hand SET 2 the exact v4.34
  bridges (`IsFractionRing.finrank_eq`, `coe_primesOverFinset`) before its agent hit
  T2's one shape adaptation.
- **The capstone is a genuine review instrument.** Writing
  `DivisorExchange.lean` consumed T6's exchange, T4's prelude and AC0's along-API; a
  wrong binder, a missing lemma or a mis-stated hypothesis in any of them would have
  surfaced as a compile failure in the reviewer's own file. The consumer's Zone J
  then composed the capstone with T4's `correspondence_correspondence` by
  discharging that theorem's `hex` hypothesis — the two halves of route A meeting in
  one term.
- **A scout gate is worth its cost.** T5 was the only topic with genuinely new
  mathematics; prototyping it first cost one `Scratch.lean` build and converted the
  biggest risk into a known quantity before any module was written.

## 7. Residual items

1. **The `ModularCurve` Hecke layer** (`DegeneracyTower`, `HeckeOperatorTotal`,
   `HeckeModule`, the roof square) — out of this port's scope and named in
   `PORTING-AC.md` §0's table. Every generic input of `heckeOperatorsCommuteBar` is
   now ported; only that layer separates the port from the headline.
2. **The deprecated-`Ideal` statement migration.** Three statements keep the pin's
   primed text under a reasoned `set_option linter.deprecated false`. The next pin
   should migrate them and teach the checker the rename.
3. **The deferred definition-module API** listed in §5, each with a count.
4. **The irreducible blocks** — T9's norm block and T8's `WFg`/`WFj` helpers — need
   no cleanup by the measured audit.
5. **The friction log** — the twelve-plus v4.34 entries at the tail of
   [../logs/ac-port.md](../logs/ac-port.md) §3 and §11.2; the playbook calls it the
   highest-value artifact because it is not derivable from the code.

## 8. Pointers

- [PORTING-AC.md](PORTING-AC.md) — the retired blueprint (planning record).
- [../logs/ac-port.md](../logs/ac-port.md) — measured costs, per topic, and the
  closeout.
- [SET-1.md](algebraicCurve/SET-1.md), [SET-2.md](algebraicCurve/SET-2.md) — the run
  briefs; [algebraicCurve/](algebraicCurve/) — the ten work orders.
- [../porting-playbook.md](../porting-playbook.md) — the reusable method.
- [ffg-retrospective.md](ffg-retrospective.md) — the previous effort's review; the
  two are deliberately parallel.
- [../../math/009-hecke-jacobian-commute.md](../../math/009-hecke-jacobian-commute.md)
  — the mathematics.
- [../spec/AlgebraicCurveConsumer.lean](../spec/AlgebraicCurveConsumer.lean) — the
  definition of done, Zones A–J.
