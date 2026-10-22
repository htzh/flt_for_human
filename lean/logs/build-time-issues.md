# Build-time issues — the D-S column's register, 2026-10-20

The build-cost state this column leaves behind, so the next session does not rediscover it. Companion
registers: [../instance-friction.md](../instance-friction.md) (instance-search *friction*, with re-runnable
probes), [porting-playbook.md](../porting-playbook.md) §5–§6 (the rules), and
[../../notes/lean-build-cost.md](../../notes/lean-build-cost.md) (the measurement method).

**The policy these entries sit under** (column note §5): the 200,000 edit-loop cap is a **diagnostic**, not
the build budget — the library's own setting is the lakefile's `maxHeartbeats 4000000`. A declaration that
exceeds the diagnostic is either (i) instance synthesis, in which case pin the argument the search is
guessing, or (ii) arithmetic defeq, in which case record the pin's own bump, the bisection and the diagnosis
in the module header and land it. Deferral is reserved for a proof that no longer **closes** at any budget.

## 1. Landed, but over the edit-loop budget — the rework is owed

`EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow`
(`ModularForms/Eisenstein/ResidueSumQExpansion.lean`):

* needs **300,000–400,000** hearts (bisected: 300,000 fails inside `h6`, 400,000 passes); the pin sets
  **4,000,000** on that one declaration;
* the diagnosis is **arithmetic defeq**, not instance synthesis: `Add.add` 304,515 unfoldings,
  `HAdd.hAdd` 266,601, `HMul.hMul` 208,538, `Nat.rec` 193,653, and no class-instance counter of note;
* cost at the library cap: **36.0 s wall / 33.7 s user** for a 277-pin-line module — 6× its siblings;
* landed because the library builds at 4M (tier-1 3,764 jobs / 31 s), with **no `set_option`**, the pin's
  bump and the bisection in the module header;
* **the 40-minute shape rework was never spent** (only a `have hsigma` dedup that moved the file from
  failing at 400k to passing at 400k). Rework: cut the `h6`/`hfin` computation into `private` helpers at the
  seams the pin already has, so no declaration needs the bump. Recorded in
  [ds-leaf-families-wave2.md](ds-leaf-families-wave2.md) §4 as owed.

## 2. Resolved — the `ZLattice` pair: landed at 20k hearts with a registered deviation

Landed 2026-10-20 as `FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean` (613 lines) and
`PoissonSummationZLattice.lean` (293 lines). Record and bisection:
[poisson-summation-statements.md](poisson-summation-statements.md).

* what the 429 s was: exactly **three** declarations — `periodizeCM_apply`,
  `periodizeLiftFun_toUnitAddTorus`, `periodizeLift_toUnitAddTorus` — over the diagnostic **in
  their statements**, not their proofs. A locally bound `hf : ∀ K : Compacts (d → ℝ), Summable fun
  n : d → ℤ => ‖(f.comp (ContinuousMap.addRight (intVec n))).restrict K‖` made `isDefEq` unable to
  close `restrict (↑K)` against `restrict ?m`, so it unfolded `Norm C(↥K, ℂ)` (`= dist x 0`, the
  `BoundedContinuousFunction` distance, `sInf`, `Finset.sum`). The profiler counted that as
  "typeclass inference"; it is instance *terms*, not instance *search*, so no argument could be
  pinned;
* fix: name the hypothesis type once (`def LocSum (f) : Prop := …`) and use `(hf : LocSum f)` in the
  three defs and three theorems. No `set_option` anywhere: the module builds at the library's 4M
  default in **5.5 s** (3,189 jobs), 0 warnings (the pin's 16M on the section was precaution);
* registered deviations: 7 `own:` rows in `spec/decl_markers.tsv` (the 6 binders + `LocSum`), the
  statements remaining defeq to the pin's. The module reads **31 ok / 0 mismatch / 0 missing /
  7 own**; the ZLattice module reads **2 ok** and builds in 5.4 s (3,202 jobs); `--all` reads
  **2,884 ok / 11 own over 109 wired modules**;
* the second module had never been elaborated and carried two hard name errors (a bare `open
  PiPoissonSummation`, the engine lives under `P2MW.S_….PiPoissonSummation`, and one qualified
  helper use); both are fixed, and its only declaration over 20,000 hearts is the first headline's
  proof (passes at 21,000).

## 3. The tree's oleans are incomplete — treat a "missing declaration" as possibly a stale build

Oleans that had to be rebuilt during this session (some were absent with only `.olean.hash`/`.trace`
left): `FLTForHuman/ModularForms/Level/Degeneracy`, `FLTForHuman/ModularForms/Eisenstein/ConstTermCubeIntegral`,
`FLTForHuman/Algebra/Module/Torsion/Coordinates`, `FLTForHuman/ModularForms/CohCarrier/TorsionOrbit`. In
addition, two **mathlib** modules have no olean in this tree — `Mathlib.Tactic.Omega` and
`Mathlib.LinearAlgebra.Quotient` — although neither import turned out to be needed (`omega` ships in the
core toolchain; the `Quotient` API arrives transitively). Symptom: `unknown identifier` or `object file …
does not exist` where the source looks fine. Fix: `flock .lake/flt_build.lock timeout 300 lake build <module>`
on the module that should own the olean.

## 3b. A dependent wave is owed, deliberately unbuilt — the `EisensteinChiNegThree` refactor

`FLTForHuman/ModularForms/WeightOne/EisensteinChiNegThree.lean` was edited on 2026-10-20 (two private
blocks lifted into `NumberTheory/ModularForms/Gamma0Three.lean` and
`ModularCurve/Numerics/NuThree.lean`, two headlines made public, its wire migrated off `PORT_FILES`;
record: [phantom-landings.md](phantom-landings.md)). The edited module and the two new ones are green
at tier 0/1, but its **51-module / 30,597-line** dependent cascade is stale — ≈413 s to re-elaborate
per `build_ladder.py --edit`.

It was **not** built, by the user's instruction: more old modules are expected to be refactored the
same way (the 23 orphan phantoms in [CARRY-FORWARD.md](../CARRY-FORWARD.md)), and each such refactor
forces the same wave, so they should share one. Nothing is red in the meantime: every removed
declaration was `private` (file-local), and the module's interface only gained two public names, so no
importer can be affected — only its olean is stale, which the next build of any dependent will fix.

**Rule for the batch:** collect the refactors, then run one wave (`build_ladder.py --edit` per host,
union the module sets) at the end, with the user's agreement, and record it here.

## 4. One compile at a time — the lock and the box

* A single `lake build` may hold `.lake/flt_build.lock` for **40+ minutes**; a queued build waits silently,
  which looks like a hang. Check with `flock -n .lake/flt_build.lock true` (exit 1 = held) before blaming
  the compiler.
* The box is **memory-tight**: 7.9 GB total with swap in use during parallel compiles. Concurrent
  elaborations thrash and inflate everybody's wall time, so serialise both builds and edit loops.

## 5. Measurement pitfall

`/usr/bin/time -f "%e %U" timeout … lake env lean file.lean` reports the **wrapper's** CPU, not the
grandchild's: a 110 s, 110 %-CPU elaboration showed `user 0.4 s` and looked like a lock wait. To measure
CPU, watch the `lean` process (`ps -o time,pcpu`) or invoke it directly; to measure wall, `time` the shell
job. This cost one wrong diagnosis this session (a "blocked" module that was in fact computing).

## 6. The head of the distribution (not defects, but watch these)

Measured this session at the library cap: `ResidueSumQExpansion` **36 s**, `LogBranchAndPrimitiveRoot`
**20 s**, `HexagonalLattice` **16–18 s**, `PeriodPair/InvariantsTorsion` **14 s**, `GroupTheory/GroupAction/OrbitCounts`
9.5 s build; everything else in the ~60 new modules is **2–13 s**. No module in the wave needed more than
200k hearts except the two in §1–§2.

## 7. Resolved — `TwoCurveDescent`: one zeta-blind `isDefEq`, behind two hidden overrides

Found 2026-10-21 while building the wave of [logs/qexp-definition-layer-homes.md](qexp-definition-layer-homes.md)
(the module was a stale *dependency* of `ModularCurve.ModularPolynomialEvalJ`), bisected and fixed the
same day; it is not part of that refactor's cascade.

**The culprit was not the declaration carrying the pin's heartbeat bump.** It was
`private theorem descentBCIota_compat`, and the probe ladder was: (1) the whole module with all 48
theorem proofs `sorry`-stubbed elaborates fine — the *statements* are cheap; (2) prefix bisection put
the cost between two declarations; (3) `one:<line>` with every earlier proof stubbed reproduced the
overrun, and `keepafter:` (whole module minus that one proof) cleared it — so one declaration, no
cascade; (4) `diagnostics` on that declaration aborted **at `whnf`** with typeclass search negligible
(max 31 instance uses) and reduction heavy — `CoordinateRing ↦ 592` (855 at `threshold 1`),
`inferInstance ↦ 120` (644), `FunctionField ↦ 143`, `FractionRing`/`Localization ↦ 137` — so a
defeq-class defect, not an instance-search one.

**Mechanism.** The pin's four local `let`s (`ψE`, `ψE'`, `χE`, `χE'`) make every `show`/`exact` in
that proof differ from the goal *only by zeta*, so `isDefEq` abandons the cheap path and unfolds
`FunctionField = FractionRing (CoordinateRing ·)` (through `Affine.baseChange`/`Localization`/
`AdjoinRoot`) instead of matching syntactically.

**Fix (proof-only; the statement is byte-identical).** State every intermediate at the explicit terms
and replace the four `show …; rfl` steps by `rw` with the `rfl`-level projection lemmas
(`AlgHom.comp_apply`, `AlgHom.restrictScalars_apply`, `IsScalarTower.toAlgHom_apply`,
`Algebra.TensorProduct.includeLeft_apply`) plus the generator lemmas already in use, closing with
`simpa only [functionFieldTensorFracEquivGeneralNoAC, AlgEquiv.ofBijective_apply, …]`. Nothing had to
be *named* — this is §8's cure in the opposite direction: there a complex type is named once, here
the names (`let`s) that block syntactic matching are removed.

**The two overrides were the reason this survived.** `section GateDescent` carried
`set_option maxHeartbeats 48000000` and `set_option synthInstance.maxHeartbeats 8000000`, transcribed
from the pin, and the P-3 record read them as "a fidelity fix, not a cap exception" and attributed
the module's multi-minute elaboration to the declaration that carries them. Both were masking a
different declaration's zeta defect. They are **removed**: the module now elaborates under
`timeout 120` at the project cap, silently, `lake build` 55 s, a dependent 6.5 s. The three
deprecations in it were fixed in the same pass (`TensorProduct.induction_on` → `inductionOn`, whose
`zero` branches disappear with the old eliminator; `if_true` → `ite_true`). The module left
`PORT_FILES` for its own `spec-pin:` wire in the same round (7 ok, 1 `own:` — the port's
`exists_twoCurveDescent`, which the pin does not state).

Rules this case adds: a `show`/`exact` that differs from its goal only by zeta is a defeq trap —
spell the terms; a cap override inside a file is a **bug report, not a budget**, and a large one (12×)
must be treated as evidence that something in that file is wrong; and before trusting "the time goes
into the declaration that carries the bump", bisect.

**The floor, measured: the statements, not the proofs.** A whole-module probe (every theorem proof
`sorry`, statements, `def`s and instances verbatim) fails a 20 s bound and passes 40 s, so no proof
edit can get the module under 20 s. The cause is the section variables: Lean re-elaborates a variable's
*frozen type* for every command in scope, and here two `IsDomain ((E₀⁄↥K₀).toAffine.FunctionField ⊗[↥K₀] K)`
hypotheses cost ~1.25 s each per command although no statement mentions them. The ruling that follows:
the module **meets the project bound** (silent at `timeout 120`), and **`timeout 30` is accepted for it**
if the statement-neutral work does not go further. The statement-neutral levers, in order, are: those
two variables moved into the two proofs that use them, then the five expensive `private def` bodies in
the `rw`-with-projection-lemmas style; the remaining lever — re-pinning the statements with type
aliases — is a **wire decision**, not an agent's (it changes public statement text and needs `own:` rows
and a spec re-pin), so it stays unopened. A 20 s gate was the stretch and is **withdrawn**: it is not a
requirement of this register, and a module at 30 s is not an open build-time issue.

**Final state (accepted, 2026-10-21).** With the statement-neutral levers taken, the module's *floor*
(all 48 theorem proofs `sorry`-stubbed) is now **under `timeout 20`** — it was over `timeout 10` before —
and the whole file passes **`timeout 60`**, fails `timeout 30`. Everything above the floor is the ~90
proof terms (top items ~2.1 s `twoCurveDescentInstance`, ~1.7 s `gateDescent_of_descent`, ~1.66/1.64 s
`twoCurve_bcIota_eq_ι` / `twoCurve_finrankEq`, then a flat ~0.1–0.2 s tail), i.e. no single lever; the
public statements are frozen, so the only remaining moves are proof-by-proof or a statement re-pin (a
wire decision). Two levers were taken and one was *impossible*: (i) the two proof-only `IsDomain (… ⊗ K)`
section variables became `haveI` in the two theorems that use them; (ii) three `private abbrev` aliases
(`ffBC`, `tensorBC`, `fracTensorBC`) replaced the 36 private occurrences of the base-changed
function-field/tensor spelling; (iii) *not* done — aliasing the `ι`/`ι'` `AlgHom` types, because the
`K₀ ≤ K` sections spell the curve `W.map f` while the engine spells it `W⁄A`, and instance search at
`.instances` transparency cannot unfold the semireducible `baseChange`, so the alias *breaks* synthesis
(`failed to synthesize Algebra (CoordinateRing …)`) and rewrites. The module is accepted at the 60 s
bound: under the project bound, silent, 0 warnings, public surface byte-identical
(`7 ok / 0 mismatch / 0 missing / 1 own`).

The worked write-up, with the probe table, the counters and the gain, is
"a fourth unit" in [../../notes/instance-friction-case-study.md](../../notes/instance-friction-case-study.md);
the policy it changed is [porting-playbook.md](../porting-playbook.md) §3.5 (bound, do not measure; a
cap override is a defect marker) and §6 (the zeta cure, beside the naming cure).

## 8. Resolved — a `≤`-lemma applied inside a large statement: one `isDefEq`, over the bound

Found and cured 2026-10-21 in the Gauss-prolongation set
([logs/qexp-regular-prolongation.md](qexp-regular-prolongation.md) §3a). The line

```lean
have hfF : (f : LaurentSeries L) ∈ qExpFunctionFieldC L Γ := laurentBaseChange_le Γ f.2
```

timed out deterministically at the 200k cap, **in the application, not the statement** (stubbing the
proof showed the statement elaborates in a second): applying a `FF ≤ qExpFunctionFieldC L Γ` proof to
an element makes `isDefEq` unfold `SetLike.le`, and inside a four-conjunct statement that costs more
than the whole edit-loop budget. The cure: state the element form once (`mem_qExp_of_mem_FF`, proved
by `SetLike.le_def.mp`) and apply that at the site — the declaration then closes in about a second.
Same class as §2's `LocSum`: name the shape, and the elaborator stops unfolding it; no heartbeat, no
statement change. The general lesson for orders: a `≤`/`⊆`-shaped lemma whose *result* is a
membership should be applied in element form inside any declaration whose statement is large.

§7 is the same family with the opposite cure: there the fix is to *name* a complex type once; here it
is to *remove* the `let`s that stop `rw` from matching syntactically.
