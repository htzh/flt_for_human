# WORKORDER-CD1 — the cut-weight definition wave, remaining four modules

**Set 0 of [TOPIC-cut-weight-decomposition.md](TOPIC-cut-weight-decomposition.md)**, the
transcription half. The manager has already landed the two base modules of the wave; this order
takes the four that build on them. The proof set (882 lines) is a separate order and is **not**
here.

## 1. Scope

Transcribe four pin `Definitions/` modules, whole, in this dependency order:

| # | pin module | lines | declarations (`private`) | port home |
|---|---|---:|---:|---|
| 1 | `Definitions/Def_NumberField_StandardGlobalAddChar.lean` | 116 | 14 (0) | `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddChar.lean` |
| 2 | `Definitions/Def_NumberField_AdelicTraceProducer.lean` | 224 | 21 (0) | `FLTForHuman/NumberTheory/NumberField/AdelicTraceProducer.lean` |
| 3 | `Definitions/Def_NumberField_IntegralAdelicTrace.lean` | 395 | 45 (10) | `FLTForHuman/NumberTheory/NumberField/IntegralAdelicTrace.lean` |
| 4 | `Definitions/Def_NumberField_AdelicTraceFin.lean` | 204 | 24 (18) | `FLTForHuman/NumberTheory/NumberField/AdelicTraceFin.lean` |

**Not this order:** the proof set (`S_AutomorphicForm_CuspidalConstituent_exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent`,
882 net lines); the two base modules (already landed — do not edit them); the checker wiring (the
manager's); any edit to an existing port module.

## 2. The landed ground

| pin module | port module | state |
|---|---|---|
| `Def_AutomorphicForm_WhittakerCoefficient` | `FLTForHuman/AutomorphicForm/Adelic/WhittakerCoefficient.lean` | landed, wired, checker +8 |
| `Def_NumberField_StandardGlobalAddCharRat` | `FLTForHuman/NumberTheory/NumberField/StandardGlobalAddCharRat.lean` | landed, wired, checker +44 |

The remaining closure is ported already and must be imported, not re-proved:
`Def_NumberField_AdelicBox` → `FLTForHuman/NumberTheory/AdelicBox.lean` (and its neighbours),
`Def_NumberField_AdelicFourier` → `FLTForHuman/NumberTheory/AdelicFourier.lean`,
`Def_NumberField_TateGlobalZeta` → registered tier 3.

**No promotion is owed.** The 28 pin-`private` declarations in this table were checked against the
only consumer in scope (the cut-weight `S_` file) and none of them is used by it. Transcribe them
`private`, exactly as the pin has them.

## 3. Import rewriting

Each pin file's `import Definitions.Def_X` becomes the port module path above; each
`import Mathlib.A < B < C` stays **verbatim** (the pin already names specific modules in these four
files — there is no `import Mathlib` to narrow). Add the docstring header described in §6.

## 4. Known mathlib `v4.34.0` drift, and how the manager fixed it

The pin was written against `v4.33.1`. The manager hit all of the following on
`StandardGlobalAddCharRat` and they will recur here — apply the recorded fix, do not invent a new
one, and report any *new* drift at first belief rather than grinding.

* **`AdeleRing` is a `def`, not an `abbrev`** (`def AdeleRing := InfiniteAdeleRing K × FiniteAdeleRing R K`).
  A literal pair is an adele only at default transparency, so `rw`/`simp` on a term that passes a
  bare pair fails with "not type-correct under the `implicit` transparency level". **Fix: bind the
  point once as a typed local and work on that** —
  ```
  set x : AdeleRing (𝓞 ℚ) ℚ := ((algebraMap ℚ (InfiniteAdeleRing ℚ) (1/2), 0)) with hx
  ...
  rw [show x.1 = algebraMap ℚ (InfiniteAdeleRing ℚ) (1/2) from by rw [hx]] at h
  ```
  Note `by rw [hx]` closes it; appending `; rfl` gives "No goals to be solved". `set` needs the
  explicit `with hx` — the default hypothesis name is not `hx`.
* **`erw` is a trap here**: it unfolds `AdeleRing` far enough to also unfold the definition under
  study, after which the pin's `show … from rfl` projection rewrites find nothing. Prefer the typed
  local over `erw`.
* Deprecations, renamed mechanically: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `if_neg` →
  `ite_eq_right`, `if_pos` → `ite_eq_left`; `dif_pos` → `dite_eq_left`, `dif_neg` →
  `dite_eq_right`; `ContinuousLinearMap.neg_apply` → `_root_.neg_apply`.
* `linter.style.haveILetI`: where the goal is a proposition, the linter wants `have`/`let`; a
  proof-level `letI := …` / `haveI : Fact … := …` is often **droppable entirely** (try removing it
  first, then `have`/`let`).
* A `simp only [AddChar.one_apply]` on a hypothesis whose term contains `1 (pair)` may report
  "made no progress"; `simp at h` reduces it (the typed-local fix usually removes the problem).

**Additions recorded from modules 1–3 of this wave** (§8 reports, all in the playbook's §7 table):

* `exists_subset_nhds_of_isCompact'` changed shape: `v4.33.1` had the pointwise
  `(hU : ∀ x ∈ ⋂ i, V i, U ∈ 𝓝 x)`, `v4.34.0` the set-relative `(hU : U ∈ 𝓝ˢ (⋂ i, V i))`. Wrap the
  pin's lambda in `mem_nhdsSet_iff_forall.mpr`; the proof content is unchanged
  (`Def_NumberField_IntegralAdelicTrace.lean:190-194`).
* `zero_le'` → `zero_le`, `not_lt_zero'` → `not_lt_zero` (deprecated aliases).
* An unused `[NumberField F]` (a lemma whose proof never uses the number-field structure) is kept
  by `omit [NumberField F] in` above it, not by weakening the signature.
* **Port-layout difference, not drift**: `integralFiniteAdeles` is homed in
  `NumberField.AdelicLevel` in the port (the pin has it in `Def_NumberField_AdelicBox`), so add
  `NumberField.AdelicLevel` to the `open` list rather than moving the declaration.
* **The pin's `set_option maxHeartbeats N in` lines are dropped**, not transcribed (§5 forbids
  raising the cap): `trace_eq_sum_mult_embedding_re` carries one at pin line 87 and elaborates at
  the 200,000 cap unchanged. Report any that do *not*.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap
> is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and the low
> cap is what finds it. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`.
> `lake build <module>` per finished file, serialized with `flock` and bounded with `timeout`. Per
> wave, build only the wave's affected targets — **never a bare whole-tree `lake build`**. A
> whole-tree build happens once, at the session's end, and only with the user's permission.

Concretely: one module at a time, in the §1 order — tier-0 loop to exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build <module>`. A module must be green before you
start the next one: the later files import the earlier ones.

**Build-time blow-up protocol.** The named risks are `Def_NumberField_IntegralAdelicTrace` (395
lines, trace/sum manipulations over `HeightOneSpectrum` and `Finset` products) and
`AdelicTraceFin` (the finiteness argument over restricted products). If a declaration hits the cap,
reproduce it alone at the low cap with `set_option diagnostics true` in a scratch file under
`lean/tmp/`, fix the inference, re-run; never raise the cap.

## 6. Deliverable shape

Each port module:

* a docstring header that states what the mathematics is (in the register's style: what the module
  defines and why), and says "transcribed verbatim from `Definitions/<pin>.lean` (pinned `aa2d8b3`,
  N lines, M declarations)";
* the pin's body verbatim except for the import rewriting of §3 and the drift fixes of §4;
* the pin's namespaces and names unchanged — the checker matches by name;
* public/`private` exactly as the pin has it (§2: no promotion).

## 7. Verification the worker runs before stopping

| check | expected |
|---|---|
| tier-0 loop on each of the four | exit 0, **0 warnings** |
| tier-1 build of each | green; record jobs and wall/user time |
| `grep -n "sorry\|admit\|^axiom\|native_decide\|import Mathlib\|maxHeartbeats\|set_option linter"` on each | no hits |
| declaration counts per module | 14 / 21 / 45 (10 private) / 24 (18 private), matching the pin |
| `git status` | only the four new modules (+ anything under `tmp/`) |

Do **not** run the statement checker and do **not** edit `spec/old_check_stmts.py`.

## 8. Stop conditions (report, do not work around)

* A pin statement will not elaborate against the port's mathlib → report the declaration, the pin
  line and the error; do not weaken or re-spell the statement.
* Drift beyond §4 → report it at first belief, with the file and line.
* A declaration the proof needs is `private` in the pin but must be public for a consumer → stop and
  report; promotion is the manager's decision.
* A module's pin text uses a declaration that is missing in the port beyond those listed in §2 →
  report it; do not stub it.

## 9. Report shape

Per module: line count, declaration count against the pin's, private count, tier-0 result (warnings
must be 0), tier-1 build (jobs, wall/user), every drift fix applied (file:line → what), anything
re-derived locally, and `git status`.
