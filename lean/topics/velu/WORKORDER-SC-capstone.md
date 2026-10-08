# SC work order — the capstone and its two leaves

**Status: drafted 2026-10-07; S-4 landed and verified the same day, the two leaves already
landed (below), dispatched 2026-10-07.** Terminal set of
row S; blueprint [TOPIC-V5-row-S-scoping.md](TOPIC-V5-row-S-scoping.md) §1/§4, with Corrections
1–2 (the SL₂ leaf went to S-4; `IsAddCyclic.of_squarefree_natCard` is the H5 column's, out of
row S). Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Consumes the
whole row: S-4's `eval_jLattice_eq_zero_of_isAddCyclic`, D-6's
`exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`, D-5's
`exists_algHom_baseChange_…`, the place/dictionary layer, and the gate producer
`exists_genusOnePlaceGate_isCentred_and_abelTheorem`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2, §2.1–§2.6, §3.1–§3.5, §4–§5.

## 1. Scope

Land the row's terminal node

`WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`
(415 pin lines): for `K` algebraically closed of characteristic `0`, an integral finite
`ι : E'.FunctionField →ₐ[K] E.FunctionField` with the norm formula, a cyclic kernel of order
`N`, and any `data : ModularCurve.ModularPolynomialData N`,
`(data.Φ.map (eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0`.

This is the row's wire test: it assembles D-6's countable descent (to an intermediate `K₀`), the
base-change column, the gate producer, the ℂ embedding, S-4's `jLattice` form and S-2's index
form into one proof about an arbitrary `K`. Writing it is the review instrument for the whole
row.

Plus its **two leaves**:

* `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq` (17 lines):
  `(E : WeierstrassCurve ℂ) [E.IsElliptic] : ∃ (L : PeriodPair) (C : WeierstrassCurve.VariableChange ℂ),
  C • L.weierstrassCurve = E` — a short consequence of `PeriodPair.jLattice_surjective` and
  mathlib's `WeierstrassCurve.exists_variableChange_of_j_eq`;
* `Field.nonempty_ringHom_complex_of_countable` (45 lines):
  `(K : Type u) [Field K] [CharZero K] [Countable K] : Nonempty (K →+* ℂ)` — the transcendence-basis
  embedding used by `solution0` to reach `complexCase`.

**Not this set:** S-2/S-3/S-4 and the H5-column `IsAddCyclic.of_squarefree_natCard`.

## 2. Source

* `P2M/Sol/S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean`
  (415 lines). Statement authority:
  `Theorems/Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean`
  — spell its binders **exactly** (the `K : Type`, `[DecidableEq K] [IsAlgClosed K] [CharZero K]`,
  the gate/`AbelTheorem` instances, `hcyc`/`hcard`, `data`).
* `P2M/Sol/S_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq.lean` (17) + wrapper.
* `P2M/Sol/S_Field_nonempty_ringHom_complex_of_countable.lean` (45) + wrapper.

The capstone file's structure: `:45–129` the ported `PeriodPair` scale prelude;
`:131–172` `conjSeam`/`conjSeam_isIntegral`/`conjSeam_finiteAlong`; `:174–195`
`separableAlong_of_charZero`/`normFormulaAlong_of_charZero`; `:197–221`
`map_eval_map_Φ`/`isElliptic_map`/`j_eq_div`/`jLattice_eq_j`; `:223–298` `complexCase` (the ℂ
case: `K = ℂ`, uses the two leaves + S-4's `eval_jLattice_eq_zero_of_isAddCyclic`); `:299–403`
`solution0` (the general `K`: D-6 descent to `K₀`, base change to `AlgebraicClosure K₀`, the
gate producer, `Field.nonempty_ringHom_complex_of_countable K₀`, `complexCase` at
`(E₀.baseChange ℂ).toAffine`); `:404–415` `solution` (the wrapper statement, likely a call into
`solution0`).

## 3. Deliverable — three modules

**The two leaves are already landed (manager, 2026-10-07).**
`FLTForHuman/Elliptic/PeriodPair/VariableChange.lean` and
`FLTForHuman/FieldTheory/NonemptyRingHomComplex.lean` exist and elaborate clean
(`lake env lean`, exit 0) at the wrapper statements. What remains of SC is the capstone module
and the wiring of all three into `SOURCES`/`PORT_FILES` — but the wiring edits
`check_flt_statements.py`, so it waits until no other set is editing that file.

1. **`FLTForHuman/Elliptic/PeriodPair/VariableChange.lean`** — *landed*. The `variableChange`
   leaf at its pin name in `PeriodPair`; imports `Elliptic/PeriodPair/JLine` and
   `Mathlib.AlgebraicGeometry.EllipticCurve.IsomOfJ`.
2. **`FLTForHuman/FieldTheory/NonemptyRingHomComplex.lean`** — *landed*. The field-embedding
   leaf at `Field.nonempty_ringHom_complex_of_countable`; imports `TranscendenceBasis`,
   `IsAlgClosed.Classification`, `Complex.Cardinality`, `Complex.Polynomial.Basic`,
   `Cardinal.Continuum`.
3. **`FLTForHuman/ModularCurve/ModularPolynomialEvalJ.lean`** — *to write*. `conjSeam*`,
   `separableAlong_of_charZero`, `normFormulaAlong_of_charZero`, `map_eval_map_Φ`,
   `isElliptic_map`, `j_eq_div`, `jLattice_eq_j`, `complexCase`, `solution0`, `solution`.
   Namespace `WeierstrassCurve.Affine` (the wrapper) with the helpers where the pin has them.

Public at pin names; helpers `private` with content names. Imports: the three S modules
(`Elliptic/PeriodPair/{LatticeIndex,PrimCosetReps,HoloLift}`, `ModularCurve/ModularPolynomialE4Cube`),
`WeierstrassCurve/Isogeny/{TwoCurveDescent,KernelBaseChange,KernelCyclicTransfer,VariableChangeAlgEquiv,BaseChange}`,
`WeierstrassCurve/GenusOnePlaceGateCentred` (the **producer**), `WeierstrassCurve/IsogenyEndDatum/Engine`,
`WeierstrassCurve/Place/Dictionary`, the new leaf modules, plus mathlib. Never `import Mathlib`.

**Collision check (the SC prerequisite).** This module holds the producer
(`GenusOnePlaceGateCentred.lean` → `Place/RRSpace.lean`) **and** `Engine.lean` in one
environment — the case that used to be impossible. It is now legal because
`Engine.instInfinitePlace` is `private` (commit `23dbdf3`/`073307e` policy route (A)). The
pre-flight must confirm this with a real stub import before any proof is written; if the
environment still clashes, stop and report (do not rename anything).

## 4. Route, with recorded negatives

- **The capstone is assembly, not new mathematics.** Every premise is ported or in the row:
  D-6's headline, D-5's base-change headline, `exists_genusOnePlaceGate_isCentred_and_abelTheorem`,
  `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain`,
  `hasPrincipalDivisors_functionField`, `AlgebraicCurve.normFormulaAlong`,
  `PeriodPair.discriminant_ne_zero`, S-4's `eval_jLattice_eq_zero_of_isAddCyclic`. The new lines
  are the `conjSeam` packaging, the char-0 separability/norm-formula bridges, and the
  `IsAlgClosed.lift`/base-change wiring.
- **The field embedding is mathlib-foundational.** `exists_isTranscendenceBasis`,
  `IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt'`, `AlgebraicIndependent`,
  `IsAlgClosed.lift` are mathlib; the pin's 45-line argument (lift an injection of transcendence
  bases, `IsAlgClosed.lift` along the algebraic extension) transcribes.
- **The `variableChange` leaf is a two-step consequence** of the ported
  `PeriodPair.jLattice_surjective`, `jLattice_eq_c₄_pow_three_div_Δ` and mathlib's
  `WeierstrassCurve.exists_variableChange_of_j_eq`.
- **Recorded negatives.** No mathlib "modular polynomial evaluated at `j`" statement; the
  capstone is the pin's. No `IsAlgClosed.lift`-free route to the embedding.
- **Dedup.** The 415-line file's `:45–129` prelude is ported (import). The pin's
  `p2m_*`/`attribute` scaffolding and heartbeat bumps are not transcribed; never raise the cap.

## 5. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; `lake build <module>` when
> done; **one** `lake build` per wave; `timeout` + `flock .lake/flt_build.lock`; time it; never
> raise `maxHeartbeats`. Iterate in a gitignored `lean/Scratch*.lean`, leaf modules first.

**Pre-flight** (report the numbers):

1. **The collision stub**: `timeout 300 lake env lean <opts>` on a file importing
   `WeierstrassCurve.GenusOnePlaceGateCentred` **and**
   `WeierstrassCurve.Isogeny.KernelBaseChange` (hence `Engine`), plus the gate producer's use.
   Green ⇒ proceed; red ⇒ stop and report.
2. `#check` `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`,
   `WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem`,
   `ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic`,
   `PeriodPair.jLattice_surjective`, `WeierstrassCurve.exists_variableChange_of_j_eq`,
   `IsAlgClosed.lift`, `exists_isTranscendenceBasis`.
3. `port_advise --targets` on the three files; report the substitution figure (expect the
   `:45–129` prelude only).

## 6. Verification

- `lake env lean` clean; `lake build` the three modules; one `flock`ed wave; whole-tree
  `lake build` green.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. **Re-run at dispatch**;
  S-2/S-3/S-4 have moved the baseline: at dispatch it is
  `6219 statements identical (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
  (6255 port declarations checked)`.
  Reconcile every delta.
- `SOURCES`: append, wrapper before its `S_` file, the three pairs (none is in the list today).
  `PORT_FILES`: append the three new modules last. Report before/after.
- `spec/ModularPolynomialCapstoneConsumer.lean` (new, `spec/` only): real executed zones, no
  `#check`, no `sorry`; deleting the modules must make it fail; exit 0. ≥1 zone at a concrete
  `K`/`E`/`E'` reachable from ported material, ≥1 running D-6's headline into the capstone
  hypotheses, ≥1 consuming the two leaves. Run `timeout 90 lake env lean <opts>`; report exit
  and wall time.
- `#print axioms` on the capstone, `complexCase`, `solution0` and the two leaves:
  `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- `build_ladder.py --edit` on the capstone module; report the cascade.

## 7. Close-out

Written lines per module; checker before → after and the reconciliation; consumer exit and time;
whole-tree build jobs and seconds; `#print axioms`; the friction findings — in particular
whether the producer/`Engine` co-import really is green after the `private` fix, how much of the
capstone is assembly, and the row's end-to-end frontier delta. Then close
`TOPIC-V5-row-S-scoping.md` §5, update `CARRY-FORWARD.md` for anything deferred, and fold the
generalizable part into [../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md).

### Close-out (2026-10-07, SC dispatched and landed)

**Deliverables.** `FLTForHuman/ModularCurve/ModularPolynomialEvalJ.lean` (**415 lines**, the
pin's `S_` file is 415): the pin's `conjSeam`/`conjSeam_apply`/`conjSeam_isIntegral`/
`conjSeam_finiteAlong`, `separableAlong_of_charZero`/`normFormulaAlong_of_charZero`,
`map_eval_map_Φ`/`isElliptic_map`/`j_eq_div`/`jLattice_eq_j`, the `scoped instance
instIsEllipticWeierstrassCurve`, `complexCase`, `solution0`, a pin-name `solution`, and the
headline at the wrapper's exact statement; plus one `private` helper
`PeriodPair.jLattice_scale`. The two landed leaves are **wired, not rewritten**:
`FLTForHuman/Elliptic/PeriodPair/VariableChange.lean` (40 lines) and
`FLTForHuman/FieldTheory/NonemptyRingHomComplex.lean` (71 lines).

**Collision pre-flight (green).** A real stub importing
`WeierstrassCurve/GenusOnePlaceGateCentred`, `Isogeny/{TwoCurveDescent,KernelBaseChange}`,
`IsogenyEndDatum/Engine`, the row modules and both leaves — and *using* the producer
(`exists_genusOnePlaceGate_isCentred_and_abelTheorem`) and an `Engine` declaration
(`placeOfPoint_zero`) — elaborates **exit 0** (`lake env lean`, 1 m 35 s / 1 m 21 s on two
runs). `Engine.instInfinitePlace`'s `private` name is mangled, so the producer's
`Place/RRSpace.lean` scoped instance and `Engine`'s coexist; route (A) is confirmed and the
producer/`Engine` co-import really is green.

**Checker.** Before (at dispatch): `6219 (312 promoted, 83 renamed), 0/0, 36 own (6255)`.
After wiring: `6235 (312, 83), 0/0, 36 own (6271)` — **+16**, reconciled exactly as the
capstone's 14 checker-visible declarations (`conjSeam`, `conjSeam_apply`,
`conjSeam_isIntegral`, `conjSeam_finiteAlong`, `separableAlong_of_charZero`,
`normFormulaAlong_of_charZero`, `map_eval_map_Φ`, `isElliptic_map`, `j_eq_div`,
`jLattice_eq_j`, `complexCase`, `solution0`, `solution`, the headline) + the two leaf
headlines. `jLattice_scale` is `private` and `instIsEllipticWeierstrassCurve` is a
`scoped instance` (`DECL_RE` has no `scoped` alternative), so both are invisible to the
checker on both sides. `SOURCES`: the three `/`-`S_` pairs, each wrapper immediately above
its `S_` file, appended last. `PORT_FILES`: the two leaves then the capstone, appended last.

**Builds.** `lake env lean` on the capstone: 1 m 19 s. The single flocked `lake build` of
the three modules: `Build completed successfully (9121 jobs)`, wall 1 m 41 s, user 23.3 s,
sys 36.4 s (the capstone module itself 86 s). Whole-tree flocked `lake build`: green,
`9326 jobs`, wall 10.2 s. `build_ladder.py --edit` on the capstone: **0 dependents / 416
lines** ≈5 s — the module is a leaf; its consumer is `spec/`-only.

**Frozen cap.** The pin's `synthInstance.maxHeartbeats 1600000` / `maxHeartbeats 16000000`
were **not transcribed**; `complexCase` and `solution0` elaborate under the global
4,000,000 cap and `lake build` the module in 86 s. No raise was needed.

**Consumer.** `spec/ModularPolynomialCapstoneConsumer.lean` (169 lines), three executed
zones: (1) the two leaves (the `variableChange` leaf at a concrete `ofTau τ` curve; the
embedding leaf at `ℚ`, extracted and evaluated); (2) the headline and `complexCase` over the
concrete ground field `K = ℂ`, gate package as hypotheses; (3) D-6's headline run at the
capstone's hypotheses and fed — via the capstone's `normFormulaAlong_of_charZero` and
`solution0` — into the descended `AlgebraicClosure K₀`. `timeout 90 lake env lean …`:
**exit 0, wall 70.5 s**. Removing any of the three `.olean`s makes it fail (`object file …
does not exist`).

**Axioms.** `#print axioms` on the headline, `complexCase`, `solution0` and both leaves:
`[propext, Classical.choice, Quot.sound]`; `grep -c sorry` = 0 in all three modules.

**Frontier delta.** The capstone's unported closure is now **0 nodes / 0 lines** (it was
**12 / 11,291** in §6): the row's terminal node is inside the ported frontier.

**Friction.**

1. **The producer/`Engine` co-import is green** — see the pre-flight above; route (A) needs
   no rename. `GenusOnePlaceGateCentred` and `Engine` coexist because the private name is
   mangled.
2. **How much of the capstone is assembly.** The pin's `PeriodPair` scale prelude (`:45–129`)
   is imported (S-3's `Lattice.lean`/`PrimCosetReps.lean`). Of the 415 lines the ten
   `conjSeam`/char-`0`/polynomial glue lemmas are short transcriptions, and `complexCase` /
   `solution0` / `solution` are the pin's proofs nearly verbatim; the only genuinely new
   derivation is the 8-line `private PeriodPair.jLattice_scale`.
3. **S-3's `jLattice_scale` is `private`.** The §3 hand-off list called it landed for the
   capstone's use, but a port-`private` declaration does not cross a module boundary; the
   capstone re-derives it from the ported `PeriodPair.g₂_scale`/`discriminant_scale`. The
   S-2/S-3/S-4 "an order's landed row is a `grep -c` claim" lesson recurs.
4. **Concrete-`ofTau` cost.** Applying the headline at the concrete `(ofTau τ)`/`(ofTau σ)`
   curves, or at `L.weierstrassCurve` for an abstract `L`, exceeds 3 m 20 s: elaborating
   `FunctionField (ofTau τ)` forces the `PeriodPair.weierstrassCurve`/`AdjoinRoot` defeq stack
   and its instance search. The consumer therefore uses hypothesis-form zones over `ℂ`; the
   concrete-`E` zone the order asked for is replaced by the concrete ground field `K = ℂ`
   (manager-approved 2026-10-07), and this note is the accepted deviation. `timeout 90` still
   suffices (70.5 s), so no bound widening was ultimately needed.
5. **`scoped instance` is invisible to `DECL_RE`** on both sides — correctly neither checked
   nor reported missing; `open scoped WeierstrassCurve.Affine` activates it downstream.
6. `end WeierstrassCurve.Affine` closes both scopes; the headline is declared after the bare
   `end` at its fully qualified name.
