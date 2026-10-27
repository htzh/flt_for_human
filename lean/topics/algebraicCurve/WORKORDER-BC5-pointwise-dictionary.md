# WORKORDER BC5 — the pointwise dictionary: `ord`, integrality, derivative regularity, `evalFun`

Scope: port **ten** small pin nodes into the **existing** modules that own each subject, adding
one declaration block per module. Eleven modules are touched; the ground is already prepared
for nine of them.

**The ground is done — read this before you start.** These modules now carry their own
`spec-pin:` wires and are already green on `spec/check_port.py`; each is an *edit*, not a new
file:

| module | wire state | what you add |
|---|---|---|
| `IsCurveOver/Transcendental.lean` | 4 ok / 0 / 0 | `isCurveOver_iff_exists_transcendental_finiteDimensional` |
| `Differential/Coefficient.lean` | 38 ok / 0 / 0, 1 own | `localUnitDerivativeRegular_of_isCurveOver` |
| `Defs/PoleDivisorPackage.lean` | 10 ok / 0 / 0 | `exists_poleDivisor_of_transcendental` |
| `Defs/PlacesOverDVR.lean` | 36 ok / 0 / 0 | `Place.exists_integralClosureAt_of_ord_fiber_nonneg` |
| `Place/OrdCalculus.lean` | 6 pins | `Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg`, `isIntegral_adjoin_of_forall_ord_nonneg` |
| `RegularProlongation.lean` | 7 ok / 0 / 0 | `RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue` |
| `Defs/PlaceEvaluation.lean` | 21 ok / 0 / 0 | `Divisor.evalFun_mul`, `Divisor.evalFun_zpow_left` |
| `Defs/PushPull.lean` | 63 ok / 0 / 0 | `Divisor.pushforward_div` |

Pin sources (pinned `aa2d8b3`, clone at `~/proj/fermats-last-theorem`): for each node, the
`Theorems/Thm_<stem>.lean` wrapper is the statement authority and `P2M/Sol/S_<stem>.lean` the
proof, where `<stem>` is the node's name without the namespace prefix.

## The ten nodes

| node | pin proof | home |
|---|---|---|
| `isCurveOver_iff_exists_transcendental_finiteDimensional` | 1 declaration | `IsCurveOver/Transcendental.lean` |
| `localUnitDerivativeRegular_of_isCurveOver` | 5 | `Differential/Coefficient.lean` |
| `exists_poleDivisor_of_transcendental` | 1 | `Defs/PoleDivisorPackage.lean` |
| `Place.exists_integralClosureAt_of_ord_fiber_nonneg` | 1 | `Defs/PlacesOverDVR.lean` |
| `Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg` | 2 | `Place/OrdCalculus.lean` |
| `isIntegral_adjoin_of_forall_ord_nonneg` | 3 | `Place/OrdCalculus.lean` |
| `RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue` | 2 | `RegularProlongation.lean` |
| `Divisor.evalFun_mul` | 1 | `Defs/PlaceEvaluation.lean` |
| `Divisor.evalFun_zpow_left` | 1 | `Defs/PlaceEvaluation.lean` |
| `Divisor.pushforward_div` | 1 | `Defs/PushPull.lean` |

## Use the port, do not re-derive

`port_advise --nodes <the ten>` reports the importable declarations: `Place.ord_nonneg_of_mem_vs`
/ `Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`, `Place.mem_iff_ord_nonneg`,
`Place.ord_pos_of_mem_maximalIdeal`, `Place.evalAt_*`, `Place.exists_restrict_eq`,
`Place.isRational_of_isCurveOver`, `Place.ord_add_eq_of_lt`, `essFiniteType_of_fg`,
`hasCanonicalDivisor_of_charZero`, and the two `exists_…` helpers of the pin's file. Import them;
do not declare a second copy.

## Statement traps (copy the wrapper, not the `S_` file)

- `isCurveOver_iff_exists_transcendental_finiteDimensional`: `[PerfectField K] [Algebra.EssFiniteType K F]`,
  conclusion `IsCurveOver K F ↔ ∃ t, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F`.
- `localUnitDerivativeRegular_of_isCurveOver`: the hypothesis is the **instance**
  `[∀ w : Place K F', w.DCoordGenerates]`; the conclusion is a `∀ w u, u ≠ 0 → w.ord u = 0 →
  w.differentialCoeff (KaehlerDifferential.D K F' u) = 0 ∨ 0 ≤ w.ord (w.differentialCoeff …)`.
- `exists_poleDivisor_of_transcendental`: `∃ D : Divisor K F, ∀ v, D v = max 0 (-v.ord x)` —
  note `max 0` on `ℤ`.
- `Place.exists_integralClosureAt_of_ord_fiber_nonneg`: the conclusion is an `∃ c :
  Place.integralClosureAt F' v, algebraMap (Place.integralClosureAt F' v) F' c = f`.
- `Divisor.pushforward_div`: `E` and `D` are related by the hypotheses (not an equality of
  divisors with a `norm` term on the left) — copy the binder block exactly.
- `RegularProlongation.mem_adjoin_iff_mem_integers_iff_of_transcendental_residue` has **two**
  `RegularProlongation` arguments and four `ResidueField`-algebra variables; universes are
  `Type*`.

## Per-module discipline

1. Read the module's existing `spec-pin:` block. **Append** the wrapper and the `S_` file of the
   node you add — the checker needs them to diff the new declaration (run it and it will tell
   you which source carries the identical statement).
2. Put the declaration where the module's subject puts it (the table above is the decision);
   keep the module's namespace, and take the wrapper's binder spelling.
3. **Do not touch any other declaration** of the module, and do not restructure it: the point of
   this set is that ten small leaves land without disturbing their hosts.
4. If a needed source declaration is `private` in the port, stop and report — do not promote it
   yourself and do not restate it.

## Build and check discipline

- **Never a tree build.** Edit loop:
  `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` from `lean/`.
  Finished module: `flock .lake/flt_build.lock timeout 110 lake build <module>`.
- Every command under 2 minutes with its own `timeout`; no loops. Logs under `lean/tmp/`.
  **No tree build, and do not build a module's dependents**: the gate is the eight edited
  modules themselves, each `lake build`-ed under `flock`; the manager runs the set's single
  targeted build at the end.
- `python3 spec/check_port.py --force <module>` for **each** of the eight modules: the count must
  not move from its starting value except by the declarations you add — i.e. `0 mismatch,
  0 missing` after your edit, with the new declaration listed `ok` (or `own:` if the manager
  records it).
- `#print axioms` on the ten headlines → `[propext, Classical.choice, Quot.sound]`; every module
  must stay at **0 warnings**; no `sorry`/`admit`/`axiom`; no `set_option maxHeartbeats`.
- Do not commit; do not add `spec/decl_markers.tsv` rows (the manager adds them if a statement
  has to be restated).

## Report (one message)

per module: whether the build and the checker are unchanged except for the added declaration;
then the axioms lines, the deviations from the pin beyond a tactic rename, and any blocker at
first belief. Never weaken a statement, never promote a `private` helper to make a proof go
through, and never deliver a `sorry`.
