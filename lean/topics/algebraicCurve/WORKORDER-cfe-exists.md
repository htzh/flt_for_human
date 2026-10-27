# WORKORDER — `exists_constantFieldExtension` (base change of a function field)

Scope: port **one** pin node (26 declarations, 314 pin lines) into a **new** module. Do not touch
any other file.

## The target

New module `lean/FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtensionExists.lean`,
containing

- the pin node `AlgebraicCurve.exists_constantFieldExtension` at its `Theorems/` wrapper's
  statement, **verbatim**;
- the pin file's 25 other declarations (the construction `CFQ`/`CFExt`, its instances, the
  `Abstract` transport lemmas, the generic prelude), transcribed at their pin names.

Pin sources (pinned at `aa2d8b3`, clone at `~/proj/fermats-last-theorem`):

- `Theorems/Thm_AlgebraicCurve_exists_constantFieldExtension.lean` — the statement authority
  (read it; it starts with `universe u v w`, then a single `theorem` with a nine-instance
  existential conclusion).
- `P2M/Sol/S_AlgebraicCurve_exists_constantFieldExtension.lean` (314 lines) — the proof. Its
  structure: `namespace W4B` → four generic prelude lemmas (`aeval_ofFinsupp_eq`,
  `transcendental_iff_linearIndependent_pow`, `transcendental_one_tmul`, `essFiniteType_of_fg`) →
  `section Abstract` (the transport lemmas over `incl τ`, lines 59–174) → `section Concrete`
  (`CFQ`, `CFExt`, four scoped instances, `tau`, `tau_gen`, `tau_eq_zero_iff`,
  `exists_constantFieldExtension_core`, lines 176–263) → `hasCanonicalDivisor_of_charZero`
  (line 273) → the headline (line 287).

Nothing here is `private` in the pin and nothing is already in the port (`port_advise` reports 0
substitutions; the four generic prelude names do not exist in the port or in mathlib), so this is
a straight transcription.

## Names, namespaces, homes

- Put the whole development in one module, in `namespace AlgebraicCurve` (the pin's `W4B` is a
  machine token — **do not** transcribe it). Keep `CFQ`, `CFExt`, `tau`, `incl`, and the transport
  lemmas under `AlgebraicCurve` (or a `ConstantFieldExtension` sub-namespace if that reads better);
  the headline must end up as `AlgebraicCurve.exists_constantFieldExtension`.
- Keep the pin's declaration names otherwise (they are human names, no `_s<n>`, no `_impl`).
- The pin's `p2m_export` / `p2m_open` / `p2m_reactivate` lines are not transcribed. Drop them;
  they exist only so the pin file compiles in isolation.

## Known traps (they cost the pin its `set_option`s; take them seriously)

1. **Universes.** The headline quantifies `(K₀ : Type u) (F₀ : Type v) (K' : Type w)` and produces
   `F' : Type (max v w)`. Start the module with `universe u v w` and keep the binders exactly.
2. **`scoped instance`s.** The pin's four instances on `CFExt P` are `scoped instance` (one is
   `noncomputable scoped instance`), each under `set_option synthInstance.maxHeartbeats 1600000 in`.
   Keep them scoped and keep the `set_option` — the `Algebra K' (CFExt P)` / `Algebra K₀ (CFExt P)` /
   two `IsScalarTower` instances are found by `inferInstance` inside the file and are *meant* to stay
   out of the global instance pool. If `scoped instance` with `inferInstance` does not elaborate,
   report the goal rather than making them global.
3. **The existential conclusion.** The headline's statement is nine instances in one `∃`, with the
   two `IsScalarTower`s and the two curve instances. Copy the binder block and conclusion from the
   `Theorems/` wrapper character for character; the checker compares the text after the name.
4. **Instance hunting on `CFExt P`.** `FractionRing (CFQ P)` is a field only for prime `P`; much of
   the `Concrete` section runs under `variable [P.IsPrime]`. Keep that ordering; do not restate it
   as an explicit argument.

## Wire and header

The module's leading `/- … -/` block carries

```
spec-pin: Theorems/Thm_AlgebraicCurve_exists_constantFieldExtension.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_constantFieldExtension.lean   -- comparable copy
```

plus 6–10 lines of prose on the mathematics: `F'` is the fraction field of `K' ⊗[K₀] F₀` modulo a
prime, the `Abstract` block transports transcendence/integrality/finiteness along
`F₀ → F'`, and the two curve instances are transferred (`IsCurveOver` from essential finite type
plus the inherited transcendence data, `HasCanonicalDivisor` from `hasCanonicalDivisor_of_charZero`).
No links to other port modules (project rule).

## Build and check discipline

- **Never** a tree build. Build only:
  `lake build FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtensionExists`, from `lean/`.
- Every command under 2 minutes; no loops around that. Log to `lean/tmp/build-cfe.log`.
- Module must build **silent**: `set_option autoImplicit false` at the top, plus whatever `haveI`
  /`have`-style options the pin's instance walls need (`linter.style.haveILetI false`,
  `set_option synthInstance.maxHeartbeats` where the pin has it).
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtensionExists.lean`
  from `lean/`. Target: **26 ok / 0 mismatch / 0 missing** (all 26 declarations are public and in the
  pin `S_` file). The diff is textual: on `MISMATCH`, fix the spelling to the pin's (e.g. the pin
  writes `IntermediateField.adjoin K' (Set.range (algebraMap F₀ F'))`, `CFExt P`, `K' ⊗[K₀] F₀`),
  never the mathematics. Scoped instances are compared like any other declaration.
- Axioms: in `lean/tmp/axioms-cfe.lean`,
  `#print axioms AlgebraicCurve.exists_constantFieldExtension` must print
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`/`admit` anywhere. Do not edit other files, do not add `spec/decl_markers.tsv` rows, do
  not commit.

## Report back (one message, do not poll)

1. build: ok/fail, wall time, warnings from your module (want 0);
2. the `check_port` summary line;
3. the axioms line;
4. **blockers early**: if a step does not transcribe (a missing port instance-supply lemma, a
   universe mismatch, a `scoped instance` that will not elaborate), stop after two attempts at the
   same step and report the goal state plus what you believe is missing. Do not burn rounds, and
   never deliver a file with `sorry`.
