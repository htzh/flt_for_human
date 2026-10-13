# TOPIC — the TateGlobal analytic core: a one-set, three-node port

**Status (2026-10-13): executed.** The order this note scopes,
[WORKORDER-T1-tateglobal-core.md](WORKORDER-T1-tateglobal-core.md), was issued and run
to completion by six subagents: 24 development modules under
`FLTForHuman/NumberTheory/NumberField/TateGlobal/` plus the three-headline façade, the
checker at 0 mismatched / 0 missing, and one declaration deferred
(`integrable_refMeasure_mul`, WORKORDER-T1 §8.8/§11 and
[CARRY-FORWARD.md](../../../CARRY-FORWARD.md)). The body below remains the
reconnaissance that fixed the set, the module map and the measurement. It is the
upstream neighbour of
[WORKORDER-Z1-completed-dedekind-zeta.md](../WORKORDER-Z1-completed-dedekind-zeta.md).

**Method.** [porting-playbook.md](../../../porting-playbook.md) §2.3–§2.4 (whole
nodes, deduplicate before coding), §3.1–§3.5 (module roles, work order, build
discipline), §4 (faithfulness, made mechanical).

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is
`v4.34.0`.

## 0. The recommendation

Port **three** pin nodes as one set, not two:

| | pin node | role |
|---|---|---|
| **A** | [`NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_zetaIntegral_mul_eulerFactors_eq.lean) | the Euler-factor identity for a factorizable test function |
| **B** | [`NumberField.TateGlobal.integrable_zetaIntegrand`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_integrable_zetaIntegrand.lean) | integrability of the zeta integrand for `Re s \gt 1` |
| **C** | [`NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator.lean) | the same identity for a jointly-factorizable/indicator test function |

The two nodes in question (A, B) are one factoring unit; C is a third
near-clone of the same prelude that costs ≈450 net lines inside the same set
against 5,434 lines transcribed alone. The tool's own grouping agrees: on the
pair it reports one block of `4215 lines / 317 decls / 2 files`, and on the triple
it reports the 3-file block of `4102 lines / 316 decls` plus two more.

The set is **not** the whole `S_NumberField_TateGlobal_*` family (96 `S_` files,
1,085 names re-proved in ≥2 of them, ≈71,600 removable lines). But the shared
block of this set is the *core layer of that family*: its statements appear
identically in 12–15 sibling files, so the home built here is the home the rest of
the family will import. Build it family-first; port the rest in later orders.

## 1. The mathematics

Fix a number field `F` with ring of integers `𝓞 F`, adele ring
`AdeleRing (𝓞 F) F`, and ideles (its unit group). The vocabulary is the 91-line
pin module [`Definitions/Def_NumberField_TateGlobalZeta.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_TateGlobalZeta.lean):

* `ideleNorm F x : ℝ` — the idele norm, multiplicative (`ideleNorm_mul`);
* `zetaIntegral ν f χ s` — the Tate zeta integral
  `∫ f(x) · χ(x) · |x|^s dν` over the ideles;
* `localChar χ v` and `archLocalChar χ w` — the components of a Hecke character
  `χ` at a finite place `v` and an infinite place `w`, with `IsUnramifiedCharAt χ v`
  the triviality of `χ_v` on the local units;
* `integralOutside S` and `IsFactorizableStandardOutside f S g h` — the test
  functions: an archimedean factor, local factors at `S`, and the unit indicator
  outside `S`.

The three headlines are then three facets of one computation.

**(B) Integrability.** For `f ∈ schwartzBruhat F` (the Schwartz–Bruhat space of
[`Def_NumberField_AdelicFourier.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_NumberField_AdelicFourier.lean)),
`χ` continuous and unitary, and `1 \lt s.re`, the function
`x ↦ f x · χ x · (ideleNorm F x)^s` is `ν`-integrable. This is the analytic
prerequisite: unitarity kills the growth of `χ`, and `f` is Schwartz, so the
integral converges in the half-plane `Re s \gt 1`.

**(A) The Euler-factor identity.** For a factorizable `f` standard outside `S`
there is `c \gt 0` with

$$\zeta(f,\chi,s)\cdot\prod_{v\notin S}{}'\left(1-\chi_v(\varpi_v)\\,N(v)^{-s}\right) = c\cdot\prod_w \zeta_w(g_w,\chi_w,s)\cdot\prod_{v\in S}\zeta_v(h_v,\chi_v,s).$$

The left factor is the Euler product over the places outside `S` — exactly the
places where the test function is the unit indicator and `χ` is unramified, so the
local integral collapses to `1 − χ_v(ϖ_v) N(v)^{−s}`. The right side is a product
of local zetas `LanglandsTunnell.TateLocal.localZeta μ φ χ s`. This is Tate's
unfolding: the global integral factors into local ones. It is the step that makes
the zeta integral an Euler product and so feeds the analytic continuation and the
functional equation of the completed zeta function, hence the Z1 headline.

**(C) The indicator/jointly-factorizable form.** When `f` is the indicator of
`integralOutside S` times a pure tensor `G ⊗ ∏_{v∈S} h_v`, the archimedean side is
abstracted: the pin produces a function
`A : (InfiniteAdeleRing F → ℂ) → (A^× →* ℂ^×) → ℂ → ℂ` and states the same identity
with `A G χ s` in place of the explicit local-zeta product. This is the shape the
twisted-unipotent / Rankin–Selberg unfolding consumes.

The three are the same mathematics: the same adelic Haar measures, the same
shell/slab decomposition of the ideles, the same `distribHaarChar`, the same
`ordZ`/valuation prelude, and the same bridge from `schwartzBruhat` (B) to
factorizability (A, C).

## 2. Why they are one set

The pin writes each `S_` file self-contained (`p2m` re-proves the prelude per
file), and these three files are near-clones of one another rather than three
independent developments:

* **They share a large identical core.** Of the three files' 17,318 declaration
  lines, 9,318 are statement-identical duplicates (54%); a direct
  name+kind+statement recount finds **330 declarations present in all three** with
  the same statement. The only shared name whose statement differs is `solution` —
  i.e. the three headlines themselves.
* **Neither is a special case of another.** `port_plan`'s `siblings` section is
  empty for the triple: the `_of_eq_indicator` name reads like a `_of_`
  specialisation of A, but C is a separate proof body over a shared core (and C's
  hypothesis really is *joint* factorizability, `IsJointFactorizableOutside`, not a
  weakening of `IsFactorizableStandardOutside`).
* **They have no import relation.** All three sit in `port_plan` layer 0; the pin
  files import only `Definitions/` and `P2M.Util`. So the only correct structure is
  a shared home imported by three caps — no cap can be the base for another.
* **The duplication is real, not a parser artifact.** `port_advise` vets 0 trusted
  substitutions in the port for the pair (its 4 rows — `DeepUnits`, `SUnits` — are
  the binder-less-`abbrev : Type` false positive, which "matches"
  `FLTForHuman.Elliptic.Univ.Poly` because the checker compares only `Type`; Z1
  recorded the same class). So none of this is already paid for.

Porting A and B as separate orders would reproduce the WeightOne failure mode the
tool exists to prevent: ≈4,100–4,400 lines re-proved in the second order.

## 3. The measurement

```
cd tools/deps
python3 port_advise.py --nodes \
  NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq,\
  NumberField.TateGlobal.integrable_zetaIntegrand,\
  NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
python3 port_plan.py --json build/port_advise.json
```

`port_plan` on the triple (all three `S_` files):

| quantity | value |
|---|---:|
| raw `S_` lines | 17,409 |
| declaration lines | 17,318 |
| duplicate copies | 9,318 |
| **once-cost after dedup** | **8,000** |
| distinct declaration groups | 495 |
| trusted substitutions in the port | 0 (6 suspect, the `Type` artifact) |
| `siblings` | none |
| `layers` | 0 (3 files) |

The factoring blocks it reports, and the module structure that follows from them:

| block | files | decls | once lines | proposed module |
|---|---|---:|---:|---|
| the common core | A, B, C | 316 | 4,102 | `TateGlobal/Core.lean` |
| the Euler unfolding | A, C | 69 | 914 | `TateGlobal/EulerUnfolding.lean` |
| the factorizability bridge | A, B | 1 | 113 | `TateGlobal/Core.lean` |

A direct checker-only partition (statement-identical grouping) sizes the caps and
the home's layers:

| partition | decls | once lines |
|---|---:|---:|
| `A∩B∩C` | 330 | 4,260 |
| `A∩C` only | 70 | 911 |
| `A∩B` only | 1 | 113 |
| A only | 16 | 422 |
| B only | 60 | 1,602 |
| C only | 19 | 448 |
| **total once** | 496 | **7,756** |

Two caveats on the tool's arithmetic, both in the conservative direction:
`port_advise`'s name-anchored `factor` drops adapter-shaped and short glue names,
so the real overlap is slightly larger than 316; and `port_plan` keeps the *longer*
of two statement-identical proofs (`sum(max span)`), so its 8,000 is an upper
bound — keeping the cheaper copy per declaration gives 7,756.

The pair alone, for comparison: `port_plan` reports `11,735` declaration lines →
`4,182` duplicate → `7,553` once-cost. Adding C costs `8,000 − 7,553 ≈ 447` net
lines, against `5,434` if C is transcribed in its own order.

## 4. The port structure

**Directory.** `FLTForHuman/NumberTheory/NumberField/TateGlobal/`, with the tier-1
façade `FLTForHuman/NumberTheory/NumberField/TateGlobal.lean` beside it — the same
layout Z1 used for `…/CompletedDedekindZeta/{…}` + `…/CompletedDedekindZeta.lean`.

**Modules and roles.**

| module | tier | content |
|---|---|---|
| `TateGlobal/Core.lean` | 3, unlisted | the 316-decl common block + its 13 pin-`private` helpers promoted here, plus the one A∩B bridge |
| `TateGlobal/EulerUnfolding.lean` | 3 | the 69-decl A∩C block (`sigmaT`, `hasSum_setIntegral_unitsOutside`, `integral_archRef_prod`, `setIntegral_unitsOutside_eq_integral_asmMeasure`, …) |
| `TateGlobal/EulerFactors.lean` | 3 | A's 16 unique declarations + `NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq` |
| `TateGlobal/IntegrableZetaIntegrand.lean` | 3 | B's 60 unique declarations + `NumberField.TateGlobal.integrable_zetaIntegrand` |
| `TateGlobal/IndicatorEulerFactors.lean` | 3 | C's 19 unique declarations + `NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator` |
| `NumberField/TateGlobal.lean` | **1, listed** | façade re-stating the three consumed headlines at the pin wrapper's names |

**The core is a merge, not a prefix.** This is the one genuinely new structural
task, and the main risk to the estimate. Each pin file lists its declarations in
its own dependency order; the home must be a topological *merge* of three orders.
A is a good spine: every declaration shared by any two of the three files is
present in A (the union of the pairwise intersections is contained in A), so take
A's order, mark its 330-decl core, and splice in B's and C's declarations by
dependency. The pin's interleaved `section`/`variable` blocks, its `local
instance`s (three in A and C, two in B), and its many `scoped instance`s must be
carried with the declarations they bind; they are invisible to the checker and to
the register and will need the same treatment Z1's `Unfolding` gave its local
instances.

**Naming.** The pin's prelude names are already natural (`mem_shellSet_iff_ord_eq`,
`valued_coe_units_eq_exp_neg_ord`, `apply_asm_of_isFactorizableStandardOutside`);
no `gapsw80`-style prefixes occur in these three files. Keep the statement text
verbatim modulo the name; the three headlines already carry their final names
(`NumberField.TateGlobal.*`), so the façade needs no rename and the checker matches
by name.

**Provenance.** One `-- pin: <name> (<file>:<line>)` comment immediately above each
declaration, so `tools/deps/unwired_register.py` fills the `pin original` column
without hand editing. Regenerate the register at the end of every wave.

**Façades and the checker.** All three headlines have real outbound consumers in
the pin (A: 8 files, including `S_LanglandsTunnell_HeckeTate_isNicePinned_heckeDatum.lean`;
B: 7, including the whole `zetaIntegral_*continuation*` chain; C: 1,
`S_TwistedUnipotentTerm_…_of_eq_indicator.lean`). Their statements are the
`Theorems/Thm_*` wrappers, which are the comparable copies. The façade re-states
all three; each is one `PORT_FILES` row and one `identical` row of the delta.
`NumberField.TateGlobal.…` is a genuine namespace in the pin, so the façade
introduces no second namespace.

## 5. Definition prerequisites

Unlike Z1 this set has a definition layer, but most of it is already paid for. The
transitive `Definitions/` closure of the three `S_` files is **18 files, 3,654
lines, 379 declarations**:

```
Definitions/Def_AutomorphicForm_AdelicLsXi.lean        Definitions/Def_AutomorphicForm_CarrierPins.lean
Definitions/Def_AutomorphicForm_WindowedSiegelSet.lean Definitions/Def_AutomorphicForm_WindowedSiegelTopology.lean
Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean
Definitions/Def_LanglandsTunnell_TateLocalZeta.lean    Definitions/Def_MeasureTheory_ScalingDichotomy.lean
Definitions/Def_NumberField_AdelicBox.lean             Definitions/Def_NumberField_AdelicCentre.lean
Definitions/Def_NumberField_AdelicFourier.lean         Definitions/Def_NumberField_AdelicHaar.lean
Definitions/Def_NumberField_AdelicLevel.lean           Definitions/Def_NumberField_AdelicVolume.lean
Definitions/Def_NumberField_Completion_Finite.lean     Definitions/Def_NumberField_TateGlobalZeta.lean
Definitions/Def_Mathlib_LinearAlgebra_Countable.lean   Definitions/Def_Mathlib_RingTheory_Ideal_Quotient_Basic.lean
Definitions/Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt.lean
```

A `port_advise --targets` run over exactly that closure
finds 272 statement-identical rows (≈2,483 lines), which `port_plan` vets into
**263 trusted / 9 suspect** — i.e. ≈2,444 lines genuinely already in the port:

```
FLTForHuman/NumberTheory/AdelicBox.lean          FLTForHuman/NumberTheory/AdelicLevel/{Level,HeckeGen}.lean
FLTForHuman/NumberTheory/AdelicVolume.lean       FLTForHuman/NumberTheory/AdelicHaar/Local.lean
FLTForHuman/MeasureTheory/ScalingDichotomy.lean  FLTForHuman/AlgebraicCurve/Place/Completion.lean
FLTForHuman/AutomorphicForm/Adelic/WindowedSiegel/{Set,Topology}.lean
```

The residual is at most **107 declarations / 868 lines** (unmatched declaration
lines per module), concentrated in:

* `Definitions/Def_NumberField_TateGlobalZeta.lean` (77 lines) — the set's own
  vocabulary (`ideleNorm`, `zetaIntegral`, `localChar`, `archLocalChar`,
  `IsUnramifiedCharAt`, `integralOutside`, `IsFactorizableStandardOutside`);
* `Definitions/Def_LanglandsTunnell_TateLocalZeta.lean` (130 lines) — `localZeta`
  and its `modulus`/`charExt`/`tateFourier` support;
* `Definitions/Def_NumberField_AdelicFourier.lean` (101 lines) — `schwartzBruhat`;
* `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (353 lines)
  and three small `Def_Mathlib_*` shims;
* scattered singles in `Def_NumberField_{AdelicLevel,AdelicBox,AdelicVolume,Completion_Finite}.lean`.

**The nine suspect rows need a human eye** — the checker compares only the type of
a `def`, so every `def … : Prop` is a candidate for every other. The lesson is to
look the port up *by name*: the run shows `IsUnitaryChar` "matching"
`AutomorphicForm.IsIdeleClassChar`, but the port in fact holds a
statement-identical `AutomorphicForm.IsUnitaryChar` in
`FLTForHuman/AutomorphicForm/Adelic/LsXi.lean`, whose header records that it is the
second half of the pin's `Def_AutomorphicForm_AdelicLsXi.lean`, split per playbook
§3.1. So this row is covered; the other eight are unverified and the 868-line
residual is a lower bound until each is checked by name.

### 5.1 Status of the port (2026-10-13)

The layer is ported as far as the S_ set's statements and proofs need, in natural
homes; each module is tier-0 exit 0 with 0 warnings and tier-1 green.

| module | tier | pin node | declarations |
|---|---|---|---|
| `FLTForHuman/LanglandsTunnell/TateLocalZeta.lean` | 3, unlisted | `Def_LanglandsTunnell_TateLocalZeta` | 23 |
| `FLTForHuman/NumberTheory/AdelicFourier.lean` | 3, unlisted | `Def_NumberField_AdelicFourier` | 15 |
| `FLTForHuman/NumberTheory/NumberField/TateGlobal/Defs.lean` | 3, unlisted | `Def_NumberField_TateGlobalZeta` | 15 |
| `FLTForHuman/AlgebraicCurve/Place/AdicCompletion.lean` | 3, unlisted | `Def_DedekindDomain_AdicValuation_InlineSpecific` (second slice) | 17 |
| `FLTForHuman/LinearAlgebra/Countable.lean` | 3, unlisted | `Def_Mathlib_LinearAlgebra_Countable` | 2 |
| `FLTForHuman/RingTheory/Ideal/Quotient/Basic.lean` | 3, unlisted | `Def_Mathlib_RingTheory_Ideal_Quotient_Basic` | 1 |
| `FLTForHuman/Topology/Algebra/Valued/WithZeroMulInt.lean` | 3, unlisted | `Def_Mathlib_Topology_Algebra_Valued_WithZeroMulInt` | 6 |
| `FLTForHuman/NumberTheory/AdelicBox.lean` (3 added) | 3, unlisted | `Def_NumberField_AdelicBox` | 3 |
| `FLTForHuman/NumberTheory/NumberField/Completion/Finite.lean` | 3, unlisted | `Def_NumberField_Completion_Finite` | 5 |

The three `Def_Mathlib_*` shims are homed at their mathlib paths under
`FLTForHuman/`, and `v4.34.0` supersedes parts of them: `Countable.of_module_finite`
is `Finsupp.Countable.of_moduleFinite` and `finite_quotient_maximalIdeal_pow_of_finite_residueField`
is a deprecated `Valued.integer` alias; the pin's names are kept as thin wrappers.
Two further drift items are recorded in `AdicCompletion.lean`: `Ideal.inertiaDeg'`
is now `Ideal.inertiaDeg` (proof re-routed through `Ideal.inertiaDeg_eq_of_isMaximal`),
and `InfiniteAdeleRing` is a `def`, so the pin's `Function.update (1 : InfiniteAdeleRing F)`
is spelled as the Pi type in `TateGlobal/Defs.lean`.

Of the 105 public residual names, 24 turned out to be the checker's context false
negatives and are statement-identical in the port already: the 17 `_apply`
adapters in `NumberField.AdelicLevel`, plus `norm_two_completion`,
`not_pos_and_lt_top_of_eq_zero_or_top` and `mem_completionIdeal_iff`; the three
`isClosed/isCompact/isOpen_integralFiniteAdeles` were genuine `𝓞 K`
specialisations of the port's general-`R` versions and are now stated at the pin's
names. The layer is closed: a re-run of `port_advise --targets` over the 18-file
closure now finds 351 statement-identical declarations, and every one of the 26
remaining public residual names has a port counterpart — 25 statement-identical
under the same name (the tool's adapter/glue filter hides them: the 17 `_apply`
adapters, `charExt_coe_units`, `modulus_coe_units`, `IsSchwartzBruhat.zero`,
`archUnitHom_apply`, `localChar_apply`, `valued_apply_le_one`,
`norm_two_completion`, `not_pos_and_lt_top_of_eq_zero_or_top`,
`mem_completionIdeal_iff`) and one — `inertiaDeg_asIdeal_completionIdeal` —
ported with its statement adapted to `v4.34.0`'s `Ideal.inertiaDeg`. The pin's
four `Def_NumberField_Completion_Finite` names are now stated in
`NumberField/Completion/Finite.lean`, delegating to the port's
`NumberField.AdelicHaar` instances, so the S_ set's `attribute [-instance]` lines
will find them. The two remaining residuals are the pin's `private` helpers
`intValuation_eq_coe_neg_multiplicity` (mathlib's
`intValuation_eq_exp_neg_multiplicity`) and `ValuationSubring.subtype_inj`
(trivial).

## 6. What is deliberately not in this set

* **The rest of the `S_NumberField_TateGlobal_*` family** (93 further `S_` files).
  Family-wide, `port_advise --pool targets` over the 96 `S_` files reports 1,085
  names proved in ≥2 files, ≈71,623 removable lines; the core layer here is itself
  re-proved 12–15 times (`valued_coe_units_eq_exp_neg_ord` 14 copies,
  `distribHaarChar_eq_of_ringEquiv` 15, `continuous_archUnitHom` 12). Those nodes
  are later orders; they should import this home, not copy it.
* **The three Z1 consumers that are `NumberField.TateGlobal.*`.** They are
  different nodes: none of A, B, C mentions `dedekindZeta` or the Z1 headline, and
  none is among Z1's ten consumers. This set is *upstream* of them.
* **The other Z1 consumers** (the completed-RayL functional equation, the
  `dedekindZeta` analytic nodes, `archTermDerived_le_log_abs_discr`) — each its own
  node.
* **The pin's `P2M.Util` / `p2m_*` scaffolding** — a transcription device, not
  mathematics, as in Z1.

## 7. Risks and open questions

1. **The merge order (§4).** The largest structural cost. If the home cannot be
   ordered as a merge of the three spines without a declaration moving, that is a
   stop-and-report, not a reason to keep two copies.
2. **Binder/section drift.** Several shared declarations are small and live under
   file-local `section`/`variable` context; the "same statement" verdict is the
   checker's, but the merge must reproduce the binder shape from each declaration's
   own pin text (Z1 risk §8.3).
3. **`local instance`s at module splits.** The pin's file-scoped `local instance`s
   will have to be re-declared in each module the split crosses (as Z1 did for
   `Unfolding`); invisible to the checker, deliberately not promoted.
4. **Suspect substitutions (§5).** Treat every `def : Prop` / structure-shaped row
   from `port_plan`'s suspect list as a human decision, looked up in the port *by
   name* — the displayed target may be the wrong one of several type-identical
   candidates.
5. **mathlib drift.** Pin Lean `v4.33.1` vs port `v4.34.0`: adapt proofs, never
   statements. Statements are the contract shared with the checker.
6. **Heartbeats — never raise the limit.** `maxHeartbeats` is not raised, file-wide or
   per declaration: the global cap stays as it is, and a ported module that exceeds
   it has a *defect*, not a budget shortfall. Since the development is homed in
   natural modules, file size is not a reason for a long build — a build-time
   blow-up is almost always **instance inference** (a `def` that blocks
   unification, an instance that is searched through an unfolding coercion, an
   `Algebra`/`SMul` diamond). Locate it by recompiling with a *low* cap and a
   wall-clock timeout (`timeout 120 lake env lean -DmaxHeartbeats=200000 …`): the
   first declaration to fail is the one to fix. Fix the inference — supply the
   instance explicitly (`letI`/`haveI`, an `@`-application, a local `instance`, an
   `inferInstanceAs` with the elaborated type), or avoid the unfolding that hides
   it — and report the fix in the hand-off. If a fix genuinely is not found, stop
   and report the declaration with a `set_option diagnostics true` trace; do not
   paper over it with a heartbeat override.
7. **Scope creep in the core.** The home must be family-first, but do not port the
   other 93 files' variants into it now: `port_advise` §3 reports binder variants
   across the family. A later "generalise" pass decides which variants the home
   absorbs.
8. **Open:** whether the home should be one module or two (`Core` for the 3-file
   block and `EulerUnfolding` for the A∩C block is the proposal; the seam is at the
   `sigmaT`/unfolding boundary, which is mathematically clean).

## 8. Reproduce

```bash
cd tools/deps

# the pair, as asked
python3 port_advise.py --nodes \
  NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq,\
  NumberField.TateGlobal.integrable_zetaIntegrand

# the recommended set: three nodes, blocks, budget
python3 port_advise.py --nodes \
  NumberField.TateGlobal.zetaIntegral_mul_eulerFactors_eq,\
  NumberField.TateGlobal.integrable_zetaIntegrand,\
  NumberField.TateGlobal.exists_forall_zetaIntegral_mul_eulerFactors_eq_of_eq_indicator
python3 port_plan.py --json build/port_advise.json

# the family context (94 S_ files; ~71.6k removable)
python3 port_advise.py --target 'P2M/Sol/S_NumberField_TateGlobal_*.lean' --pool targets --no-drags

# the definition closure and its port coverage (§5 lists the 18 files)
python3 port_advise.py --targets <closure-list.txt> --no-drags
python3 port_plan.py --json build/tate_defs.json --section budget
```
