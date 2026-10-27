# WORKORDER BC6 — the reduction-correspondence tail and two cheap leaves

Scope: **one new module** and **two insertions**. Nothing else may be edited.

## Nodes

| node | pin `S_` / `Theorems/` stem | silo | home |
|---|---|---:|---|
| `AlgebraicCurve.Divisor.mapDomain_placeReduction_correspondence` | `S_AlgebraicCurve_Divisor_mapDomain_placeReduction_correspondence` | 925 | **new** `FLTForHuman/AlgebraicCurve/ConstantReductionCorrespondence.lean` |
| `AlgebraicCurve.Pic0.exists_mk_eq_forall_notMem_support` | `S_AlgebraicCurve_Pic0_exists_mk_eq_forall_notMem_support` | 60 | insert into `FLTForHuman/AlgebraicCurve/Place/OrderArithmetic.lean` |
| `AlgebraicCurve.SemilinearAut.pushforward_smul` | `S_AlgebraicCurve_SemilinearAut_pushforward_smul` | 21 | insert into `FLTForHuman/AlgebraicCurve/WeilExchange/GaloisRamification.lean` |

Pin at `aa2d8b3`, clone `~/proj/fermats-last-theorem`. **Statements come from each node's
`Theorems/Thm_<stem>.lean` wrapper**, proofs from the `S_` file.

**The mathematics.** `mapDomain_placeReduction_correspondence`: constant reduction of a curve
commutes with a correspondence and with its base change — a map-domain statement on divisors,
which is why the new module imports the place/constant-field-extension layer. The other two are
leaves: the moving lemma for degree-zero divisor classes (every class has a representative whose
support avoids a prescribed finite set) and the commutation of `Divisor.pushforward` with an
intertwined semilinear automorphism.

## Why these homes (do not re-home them)

The manager checked the dependency direction: the new module's premises live in
`IsCurveOver/Transcendental`, `Place/ConstantFieldExtension`, `Place/ConstantFieldExtensionRamification`
and `Place/FromValuationSubring`, and **no existing module is above all four** — hence a new module
that imports those (add whatever else the proof needs). `WeilExchange/GaloisRamification.lean` is
where the semilinear action on places and orders lives, and it is now wired (**7 ok / 0 / 0**), so
the insertion is diffed.

**The moving lemma's home is `Place/OrderArithmetic.lean`, not `Defs/Divisor.lean`** (re-homed
after the worker's report): its pin proof needs `Place.exists_forall_ord_eq_finset`, i.e. weak
approximation, and `Defs/Divisor.lean` is below every module that carries approximation — the
import would be a cycle. `Place/OrderArithmetic.lean` is the module that proves the approximation
theorem, imports `Defs/PushPull` (hence `HasPrincipalDivisors.exists_divisor`), and is wired
(8 `spec-pin:` lines, green). Append the leaf's wrapper and `S_` file to its wire.

`SemilinearAut.pushforward_smul`'s pin proof also uses `SemilinearAut.restrict_smul`, which the
port does not have: port it **public** into the same module at the pin's name (it is a pin
declaration in a pin `S_` file, so it is diffed, not hidden) and add its wrapper and `S_` file to
the wire too.

## Rules

- The new module: header `/- … -/` with prose on the mathematics and `spec-pin:` lines for both
  the wrapper and the `S_` file, no cross-references to port modules or notes;
  `set_option autoImplicit false`, `noncomputable section`. Universe and binder spelling from the
  wrapper, character for character (section variables where the wrapper has them, inline binders
  where it writes them inline — the checker compares text).
- Each insertion: append the wrapper **and** the `S_` file to the module's existing `spec-pin:`
  block; keep every existing declaration untouched.
- **No tree build, no dependents.** Edit loop `timeout 110 lake env lean -DautoImplicit=false
  -DmaxHeartbeats=200000 <file>` from `lean/`; finished module
  `flock .lake/flt_build.lock timeout 110 lake build <module>`. Every command under 2 minutes, its
  own `timeout`, no loops; logs under `lean/tmp/bc6-*.log`.
- `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing** per module, the new
  declaration `ok`; `#print axioms` on the three headlines → `[propext, Classical.choice, Quot.sound]`;
  0 warnings; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`; no commit; no
  `spec/decl_markers.tsv` row.
- If a proof needs a `private` port helper or a declaration below its home, **stop and report** —
  do not promote, do not restate, do not edit a hub.

## Report (one message)

per module: build + warnings, the checker summary line; then the three axioms lines, the
deviations beyond a tactic rename (one line each), and any blocker.
