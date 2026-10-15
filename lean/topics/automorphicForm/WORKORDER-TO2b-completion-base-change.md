# WORKORDER-TO2b — `Def_DedekindDomain_Completion_BaseChange` (W2b, the cap-risk core)

Wave 2b of the twisted-orbital definition program
([TOPIC-twisted-orbital-defs.md](TOPIC-twisted-orbital-defs.md) §2). This is the module the pin
papered over with `set_option maxHeartbeats 1200000` / `synthInstance.maxHeartbeats 400000` /
`maxSynthPendingDepth 3` / `Elab.async false` — the one real risk of the program. It owns
`tensorAdicCompletionIntegersTo` (`:649`) and `baseChangeAlgEquiv` (`:1058`), the two declarations
`TwistedOrbital.semiLocalIntegers`/`semiLocalEval` name, hence the two the trio cannot be stated
without. W1 and W2a are landed ([WORKORDER-TO1](WORKORDER-TO1-mathlib-supplements.md) §9,
[WORKORDER-TO2a](WORKORDER-TO2a-dedekind-integral-closure.md)): 112 modules / 3,140 public
registered, checker **9790 / 0 / 0 / 38 own**.

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Tier 3, wires nothing:
checker delta **0**.

## 1. Scope

The pin node whole (playbook §2.3): `Definitions/Def_DedekindDomain_Completion_BaseChange.lean`,
**1,160 lines / 73 declarations**, in the pin's namespaces (root `Subring`/`Pi`/`LinearEquiv`/
`Module.Basis` additions; `TensorProduct` and `IsDedekindDomain.HeightOneSpectrum` sections; a
`shortcut_instances` block). The public surface:

* the generic preamble (:17–243): `Subring.toSubmodule`, `Pi.semialgHom(+_apply)`,
  `Pi.semialgHomPi(+_apply)`, `AlgEquiv.piCongrFiberwise`, `SemialgHom.baseChange_of_algebraMap(+_tmul,
  _tmul_right, _tmul_left)`, the `SemialgHom`/`CommSemiring` instance,
  `SemialgHom.baseChangeRightOfAlgebraMap(+_apply, _coe)`, `LinearEquiv.mulLeft(+coe)`,
  `LinearEquiv.mulRight(+coe)`, `Module.Basis.rightBaseChange(+_repr, _apply)`,
  `finrank_rightAlgebra`;
* the completion core (:245–1160): `closureAlgebraMapIntegers_eq_prodIntegers`,
  `denseRange_of_prodAlgebraMap`, the `WithVal` continuity lemmas,
  `adicCompletionSemialgHomCompletion`, `adicCompletionSemialgHom(+_apply, _coe,
  toCompletion_, valued_, _image_adicCompletionIntegers, _continuous)`, the `Extension`
  block's `Algebra`/`ContinuousSMul` instances, `semialgHomPi`, `baseChange(+_tmul_apply)`,
  `baseChangeRight(+_surjective, _isOpenQuotientMap)`, the `Module.Finite`/`IsModuleTopology`
  instances, **`tensorAdicCompletionIntegersTo(+_tmul)`**, `tensorAdicCompletionIntegersToPiRight`,
  `tensorAdicCompletionIntegersToAdicCompletion`, `range_baseChange_comp_tensorAdicCompletionTo_eq_pi`,
  `baseChange_bijective`, **`baseChangeAlgEquiv`** (:1058), `baseChangeContinuousAlgEquiv` (:1083),
  and the remaining tail.

**The `shortcut_instances` block (:504–538) is the pin's workaround, not part of the API.** It is
~30 `private noncomputable instance : … := inferInstance` bricks whose only purpose is to keep
instance search from unfolding. You may reproduce it `private` if a declaration genuinely needs it
(it is not a cap and not a public surface), but prefer supplying the instance at the use site and
say which you did. Do **not** transcribe any `set_option`.

**Not this wave.** `TwistedOrbital`/`LocalOrbitalBase` (W3), the `SemiLocal`/`UnitFactorizable`
gate (W4), the trio (W5).

## 2. Sources, deliverable, and the InlineSpecific residual

Pin:
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_DedekindDomain_Completion_BaseChange.lean`.
Local clone `~/proj/fermats-last-theorem` is the working copy.

**Deliverables (two new tier-3 modules):**

* `FLTForHuman/RingTheory/DedekindDomain/CompletionBaseChange.lean` — the node above, pin
  namespaces, public at the pin's names, `-- pin:` provenance on each.
* `FLTForHuman/RingTheory/DedekindDomain/AdicValuationSupplement.lean` — **only** the residual of
  `Def_DedekindDomain_AdicValuation_InlineSpecific` that this module actually reaches and mathlib
  lacks. Do **not** transcribe that 565-line inlining whole: `Completion_BaseChange` names just
  three of its declarations — `Valuation.IsRankOneDiscrete` (mathlib has the class and the
  `FinitePlace` instance), `denseRange_of_integerAlgebraMap` (mathlib has `denseRange_algebraMap`,
  `AdicValuation.lean:886`) and `ValuationSubring.algebraMap_apply` (re-derivable) — so substitute
  the first two and transcribe only what a proof genuinely needs, each with a
  `-- pin:` comment for the InlineSpecific line. **Report the residual's rows explicitly**, or say
  "empty" and prove it.

## 3. Substitute first, then transcribe

For **every** declaration check mathlib `v4.34.0` before transcribing. Since the pin's
`db584cd6`, mathlib added `Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean:519–540`
(`Module.Finite Kv Lw` from a dense base-change map `Kv ⊗[K] L →ₗ[Kv] Lw`) — build on it rather
than re-deriving its foundation, and check each of the preamble declarations
(`Pi.semialgHom`, `SemialgHom.baseChange*`, `LinearEquiv.mulLeft/Right`,
`Module.Basis.rightBaseChange`, `finrank_rightAlgebra`) for a mathlib home. Where mathlib has the
pin's statement, import it and do not re-declare; transcribe only what is genuinely absent, at the
pin's name. **Report the substitution table** for both modules. Replace any bare
`import Mathlib` with explicit imports. Use the mathlib names the W1 hand-off names
(`Algebra.TensorProduct.commRight*`, `IsModuleTopology.isTopologicalRing`, `AlgHom.domRestrict`).

## 4. Named risks and the cap method (this is the wave that tests it)

Risks, in the order they will bite: the `Extension` instance block (:490–535, where the pin
bricked); `closureAlgebraMapIntegers_eq_prodIntegers` / `denseRange_of_prodAlgebraMap` (:252, :285);
`adicCompletionSemialgHomCompletion` (:420) and its continuity; `baseChangeRight_surjective` /
`baseChange_bijective`; and `tensorAdicCompletionIntegersTo` / `range_baseChange_comp_…` /
`baseChangeAlgEquiv`.

**The method is fixed: keep the 200k cap and iterate fast to find the actual instance.** A
declaration that will not fit is under-determined, not long. Isolate it in a scratch copy; run
`set_option diagnostics true in` / `set_option trace.Meta.synthInstance true in` on it alone at the
low cap; read which search fails or unfolds a coercion; supply the instance (`letI`/`haveI` with
the elaborated type, `inferInstanceAs`, explicit `@`-application, or the pin's `private`
`inferInstance` brick) or restructure so the search is not needed; re-run. **Never** raise
`maxHeartbeats` and never add `synthInstance.maxHeartbeats`/`maxSynthPendingDepth`/`Elab.async`.

**Stop and report** (do not force it) if a declaration still exceeds the cap after that diagnosis,
with the declaration, the trace, and what you tried — the manager takes a genuine non-fit to the
user. Also stop if a substitute has a different statement, or if the module cannot compile
without editing an existing one.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock`
> and bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after the
> user agrees to it, and never on the agent's own initiative.

Do `AdicValuationSupplement.lean` first (tiny), then `CompletionBaseChange.lean`.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on both modules | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) and **no** `synthInstance.maxHeartbeats`/`maxSynthPendingDepth`/`Elab.async` |
| tier-1 build of each | green; record jobs and wall/user/sys |
| substitution tables | one row per pin declaration of both modules (and of the InlineSpecific residual); every `transcribed` row present once at the pin's name |
| the two trio-critical declarations | `tensorAdicCompletionIntegersTo` and `baseChangeAlgEquiv` present, public, at the pin names |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite) |

No checker run, no register edit, no wiring.

## 7. Report shape

Per module: path, lines, public/`private`, tier-0 and tier-1 times, substitution table. Then: the
InlineSpecific residual (rows or "empty"); every instance fix with the offending declaration and
the trace finding; the `shortcut_instances` decision (reproduced `private`, or supplied at use
sites); any declaration you stopped on with the trace; `git status --porcelain` showing only the
two new files.

## 8. The manager's half (not this order)

Register both modules (and record the InlineSpecific substitution in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md)); then cut **W3** — `InfiniteAdeleRing_BaseChangeData`,
`M4aHerbrand_ArchSemilocal`, `SigmaCentralizer`, `UnitFactorizableOfType`, and the whole
`LocalOrbitalBase` and `TwistedOrbital` nodes.

## 9. Results as landed (2026-10-14)

`FLTForHuman/RingTheory/DedekindDomain/CompletionBaseChange.lean` — **1,392 lines** (pin 1,159; the
delta is the folded residual table, `-- pin:` provenance on every declaration and adapted proofs),
**76 named declarations (71 public + 5 `private`) + 8 anonymous instances**, tier-0 exit 0 /
**0 warnings**, tier-1 green (3,442 jobs, 14 s). `AdicValuationSupplement.lean` **deleted**; its
residual table is folded into the header, which imports `FLTForHuman.AlgebraicCurve.Place.AdicCompletion`
directly. Both trio-critical declarations at the pin's names: `tensorAdicCompletionIntegersTo`
(`:785`) and `adicCompletion.baseChangeAlgEquiv` (`:1300`).

**One hub edit was needed and was the manager's** (see §4): the W1 module
`FLTForHuman/Algebra/RightActionInstances.lean` delegated its scoped `Algebra S (B ⊗[R] S)` to
mathlib's `Algebra.TensorProduct.rightAlgebra`, whose `SMul` is not definitionally the pin's scoped
`SMul`, so `Algebra.toModule` was not the scoped `Module` and `IsModuleTopology.t2Space'` (pin
`:630`) failed. Fixed by transcribing the pin's **explicit** instance body and re-transcribing
`algebraMap_eval` (`rfl` under it); `AlgebraMap.baseChange`'s `commutes'` then closes by
`simp [Algebra.TensorProduct.map_tmul]`. Cost measured at 1 module / 731 lines / ≈11 s.
**This reverts one W1 substitution** — `algebraMap_eval` is transcribed, not
`Algebra.TensorProduct.right_algebraMap_apply` (that lemma belongs to `rightAlgebra`); the W1 order
§9 row is superseded.

**No `set_option` of any kind anywhere** — not the pin's `maxHeartbeats 1200000`,
`synthInstance.maxHeartbeats 400000`, `maxSynthPendingDepth 3` or `Elab.async false`. The pin's
~30-brick `shortcut_instances` block was **not** reproduced; every instance defect was fixed at the
use site by the low-cap method (`Module.Finite` term-mode `letI`, a named
`SemialgHom.instIsBiscalarBaseChangeOfAlgebraMap`, `simp only [adicCompletion.valued_coe]`, an
explicit `change` for `strictMono'`). **No declaration was stopped on.**

**The `:1013` escalation, answered by route (a).** `Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing`
is deprecated in v4.34 and its replacement `Ideal.sum_ramification_inertia_eq_finrank` needs
`[Module.Flat R S] [Fintype (p.primesOver S)]`. The pin's statement is over arbitrary Dedekind
`A B`, so specializing (route (b)) was rejected; the worker kept the statement verbatim and
supplied `Module.Flat` via `Module.free_of_finite_type_torsion_free'` + `Module.Flat.of_free`,
`Subsingleton`/`Fintype` for `p.primesOver` via `Ring.DimensionLEOne.maximalOfPrime` +
`IsLocalRing.eq_maximalIdeal` + `Fintype.ofSubsingleton`, then collapsed the sum. `Module.Flat R S`
is not found by search; it is hand-derived.

Checker **9790 / 0 / 0 / 38 own** — unchanged (tier 3). Register **112 → 113 modules, 3,140 → 3,210
public, 2,852 → 2,920 with a pin original**. Files changed: `CompletionBaseChange.lean` (new),
`RightActionInstances.lean` (manager hub edit), `AdicValuationSupplement.lean` (deleted).
