# WORKORDER-DC1 — a correspondence preserves regular differentials

**Status (closed 2026-10-19): landed and reviewed green.** One set, one module, one
public headline over two internal blocks. Measured:
`FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegular.lean`, **653 lines**,
**19 public declarations** (18 internal + the headline — the order's 18 was an off-by-one:
the `S_` file has 26 rows, not 25, and `solution` is one of them);
`spec/check_port.py` **19 ok / 0 mismatch / 0 missing**; tier-1 build 2,740 jobs,
**0 warnings from the module**; axioms `[propext, Classical.choice, Quot.sound]`; frozen
checker unchanged at **10473**; the frontier reads `needed 0` for the node. Drift: one
`Ideal.le_pow_ramificationIdx` → `…Idx'`, one `dif_pos` → `dite_eq_left`, and the pin's
two local `maxHeartbeats` raises on `essFiniteType_of_mem` are gone (it elaborates under
the set's 200k cap). The `-- pin:` marker cites the wrapper's `theorem` line, `:12`. The set's row is
`AlgebraicCurve.Differential.correspondence_mem_regularDifferentials`, the 829-line
leaf `P2M/Sol/S_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean`
(pinned `aa2d8b3`) — `frontier.py --ds` prices it `needed 1 node / 829 lines`, i.e.
**ready**, with no premises of its own beyond the definitions, and gives it 9 project
dependents (the Riemann–Roch / canonical-divisor row of the AC column consumes it).

**Audience.** A fresh coding session. Method: [porting-playbook.md](../../porting-playbook.md)
§3–§5; wire: the per-module protocol (`spec-pin:` header, `spec/check_port.py`). The
house style is `AlgebraicCurve/Place/{OrdCalculus,BranchUniqueness,MeroRealize}.lean`.

## 1. Scope

Port the pin `S_` file **whole** — 829 lines, 25 declarations, **all public** — except
the seven the port already has (§2). Three blocks plus the headline:

| block | pin lines | the mathematics |
|---|---|---|
| `Place.TraceDifferentBound` | 28–326 | the trace-different bound at one place: `ord`/`mem` bridges (`mem_iff_ord_nonneg'`), the fibre-centre dictionary re-derived (`neg_log_valuation_fiberCenter_eq_ord`, `le_ord_iff_mem_pow_fiberCenter`, `ramificationIndex_eq_ramificationIdx_fiberCenter` — all imported), the **different ideal** bound `differentIdeal_le_pow` and `trace_mem_of_le_ord`: the trace of an element of the integral closure, when its order is large enough, lands in the trace-different ideal |
| `Place.LocalDerivation` | 328–636 | a derivation `D` on the function field read at a place: it kills algebraic elements (`exists_mem_finiteDimensional`, `essFiniteType_*`, `exists_eq_algebraMap_add_mul`), spans the place's derivation space (`span_D_eq_top`), is unique up to a unit (`exists_D_eq_smul_D`, `…_of_ord_pos`), and its value at a uniformiser is nonzero (`D_ne_zero_of_ord_eq_one`), with `isUnit_add_of_mem_maximalIdeal` as the ring step |
| `Place.exists_restrict_eq` | 638–660 | restriction of places is surjective along the finite separable extension `F ⊆ F'` — **imported, not restated** (§2) |
| `Differential.CorrespondenceRegular` | 662–813 | `hfg_along` (the transcendence hypothesis transports along the finite integral `ψ`), `pullbackAlong_mem` (pulling a regular differential back along φ is regular) and `traceAlong_mem` (its trace down along ψ is regular), i.e. the two halves of the correspondence |
| — | 815 | `solution` → **the headline** `Differential.correspondence φ ψ ω ∈ regularDifferentials K F` |

**Not this set:** the definition modules (all homed, §2); the AC column's Riemann–Roch
consumers; any edit to an existing module.

Measured (`port_advise` shape tier + `port_plan`, on the tree LP1–LP4 leave):

| quantity | value |
|---|---:|
| pin `S_` lines | 829 |
| declaration lines | 800 |
| **net new math lines** | **581** |
| declaration groups | 26 (25 in the `S_` file + the wrapper) |
| port-importable (vetted, all **byte-identical**) | **7** (219 lines) |
| declarations this module adds | **19** (18 internal + the headline) |

## 2. Pre-round: none is owed, and seven declarations are imports

**(a) The definition layer is homed.** The pin imports
`Def_AlgebraicCurve_{DifferentialPushPull,RegularDifferentials,IsCurveOver,PlacesOverDVR}`,
all in the port (`AlgebraicCurve/Differential/{PushPull,TraceDiff}.lean`,
`Defs/RegularDifferentials.lean`, `Defs/IsCurveOver.lean`, `Defs/PlacesOverDVR.lean`).
Every name the two `p2m_export` lists carry was checked against the tree — the
`Differential.*` API (`pullbackAlong`, `pullbackAlong_D`, `pullbackAlong_smul`,
`traceAlong`, `traceAlong_smul_pullbackAlong`, `traceAlong_of_not`, `correspondence`,
`correspondence_apply`, `regularDifferentials`, `mem_regularDifferentials_iff`), the
along-layer (`algebraAlong`, `isScalarTower_along`, `isIntegral_along`, `FiniteAlong`,
`SeparableAlong`) and the place dictionary (`ramificationIndex`, `ramificationIndex_pos`,
`restrict`, `mem_restrict_iff`, `ord_restrict`, `exists_ord_eq_one_and_dCoord_eq`,
`mem_of_eval_monic_eq_zero`, `mem_center_iff`, `centerHeightOneSpectrum`,
`toValuationSubring_eq_of_forall_mem`, `integralClosureAt`,
`algebraMap_integralClosureAt_injective`, `maximalIdeal_ne_bot`, `fiberCenter`,
`toValuationSubring_eq_of_restrict_eq`, `algebraMap_integralClosureAt_ne_zero`,
`ord_algebraMap_integralClosureAt`, `placeOfPrime`, `restrict_placeOfPrime`,
`fiberCenter_placeOfPrime`, `dCoord`) — **all present**, no gap.

**(b) Seven declarations are already in the port and are byte-identical** (the first
set of this column where the byte tier fires: the AC column homed this prelude when it
ported the fibre dictionary and the Riemann–Roch row). Import them:

| pin line | lemma | port home |
|---:|---|---|
| 30 | `ord_nonneg_of_mem'` | `Place.ord_nonneg_of_mem_vs` (`AlgebraicCurve/Canonical/WeilDifferential.lean`) |
| 45 | `mem_of_ord_nonneg'` | `Place.mem_toValuationSubring_of_ord_nonneg_alt` (`Defs/PlaceEvaluationAlgebra.lean`) |
| 63 | `eq_ord_of_addHom_of_nonneg_iff` | `Place.eq_ord_of_addHom_of_nonneg_iff` (`AlgebraicCurve/P1/Differential.lean`) |
| 138 | `neg_log_valuation_fiberCenter_eq_ord` | `Place.neg_log_valuation_fiberCenter_eq_ord` (`Defs/PlaceDictionary.lean`) |
| 177 | `le_ord_iff_mem_pow_fiberCenter` | `Place.le_ord_iff_mem_pow_fiberCenter` (`Defs/PlaceDictionary.lean`) |
| 200 | `ramificationIndex_eq_ramificationIdx_fiberCenter` | same name (`Defs/PlaceDictionary.lean`) |
| 640 | `exists_restrict_eq` | **`Place.exists_restrict_eq`** (`WeilExchange/Bifibre.lean:64`) — the *general* lemma (`{K F' M}`, `[Algebra F' M] [IsScalarTower] [FiniteDimensional] [Algebra.IsSeparable]`); the pin's is its instance at `M := F'`, and the section contexts agree. Use it as `Place.exists_restrict_eq (M := F') …`; do not restate the 25 lines |

Note the first two are *renamed* copies: the pin's primed names (`ord_nonneg_of_mem'`)
are the port's descriptive ones. Import and use the port's names; the checker never
sees the pin's row.

**One pre-existing duplication, not this set's to fix.** `WeierstrassCurve/IsogenyEndDatum/DualEndData.lean:1537`
carries `Place.exists_restrict_eq_of_separable` with the same statement as the pin's 640
row (a second copy of what `Bifibre.lean` has in general form). Do **not** import it
from this Differential module — that would invert the layering. Recorded for the
WeierstrassCurve column.

**(c) No hub edit, no promotion.** Nothing in this set changes an existing module.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement: `Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean`
  (20 lines; `spec-pin:` source for the headline). Its two `attribute` lines —
  `attribute [-instance]` on five `Place` instances and `attribute [-simp]` on five
  lemmas — exist because the pin's `S_` files re-declare them. **Do not copy them**:
  the port carries each once. If a proof needs a simp set narrowed, narrow it on the
  single declaration and report it;
* proof: `P2M/Sol/S_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean`
  (829 lines; `spec-pin:` source for the 17 internal declarations). Its own import list
  adds `Def_AlgebraicCurve_PlacesOverDVR`, whose names are in the `Defs/` module.

Rendered:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean>.

## 4. Deliverable

**4.1 Home.** `FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegular.lean`
(the directory holds `Generation.lean`, `Hurwitz.lean`, `PushPull.lean`,
`TraceDiff.lean`). Keep the pin's namespaces: `AlgebraicCurve.Place.TraceDifferentBound`,
`AlgebraicCurve.Place.LocalDerivation`, `AlgebraicCurve.Differential.CorrespondenceRegular`,
and the headline in `AlgebraicCurve.Differential`.

**4.2 Imports.** Start from

```lean
import FLTForHuman.AlgebraicCurve.Differential.TraceDiff
import FLTForHuman.AlgebraicCurve.Defs.PlaceDictionary
import FLTForHuman.AlgebraicCurve.WeilExchange.Bifibre
```

(the first reaches `Differential/PushPull.lean` and the `pullbackAlong`/`traceAlong`
API — note `Differential/TraceDiff.lean` is 36 lines and does *not* reach `PushPull`, so
import `Differential/PushPull` explicitly; the second the fibre-centre dictionary, the
third `Place.exists_restrict_eq`), and
add only what the edit loop demands — `P1/Differential.lean`,
`Defs/PlaceEvaluationAlgebra.lean`, `Canonical/WeilDifferential.lean` for the three
renamed imports of §2(b) if they are not already reached. **Never `import Mathlib`.**

**4.3 The headline**, verbatim from the wrapper (keep the `-- pin:` marker, citing the
wrapper's `theorem` line — `:12`, which is what the corpus and `check_port` record):

```lean
-- pin: AlgebraicCurve.Differential.correspondence_mem_regularDifferentials (Theorems/Thm_AlgebraicCurve_Differential_correspondence_mem_regularDifferentials.lean:13)
theorem AlgebraicCurve.Differential.correspondence_mem_regularDifferentials
    (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [IsAlgClosed K] [CharZero K] [IsCurveOver K F] [IsCurveOver K F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hψfin : FiniteAlong K ψ)
    {ω : Ω[F⁄K]} (hω : ω ∈ regularDifferentials K F) :
    Differential.correspondence φ ψ ω ∈ regularDifferentials K F
```

The pin's `solution` body is the last block's `traceAlong_mem` applied to
`pullbackAlong_mem`; keep its shape.

**4.4 Module header.** One `/- … -/` paragraph (what the module is, the seven imports
of §2(b) with their homes, the not-copied `attribute` prelude) plus exactly two
`spec-pin:` lines (wrapper, `S_` file).

## 5. Route

**5.1 Reuse.** The seven of §2(b) are imports; the two `_vs`/`_alt` spellings and the
`M := F'` instantiation of `exists_restrict_eq` are the only places where the port's
names differ from the pin's. Everything else is new transcription.

**5.2 Faithfulness.** Statements and proofs transcribed; adapt only what mathlib
`v4.34.0` forces (the ordinary deprecations: `if_pos`/`if_neg`/`dif_pos`/`dif_neg` →
`ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right`; `Ideal` API drift in the
different-ideal block; `Derivation.leibniz`/`leibniz_pow` names). A statement change is
a stop condition.

**5.3 Stop-early risks.**

* The `trace_mem_of_le_ord` / `differentIdeal_le_pow` pair (pin 234–330) is the set's
  mathematical core and the only place where the `Ideal`/`Trace` API is likely to have
  drifted; adapt the proof.
* If a proof needs a `private` helper of an existing module, **stop and report** with
  the declaration, host and `build_ladder.py --edit` price; re-derive it locally
  `private` if cheap.
* Do not copy the wrapper's `attribute` prelude (§3).

## 6. Build discipline (copy, do not paraphrase)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`.
> Never raise `maxHeartbeats`, never a module-level `set_option maxHeartbeats`.
> `flock .lake/flt_build.lock timeout 300 lake build <module>` once the file is done.
> Never a bare whole-tree `lake build`. Every tool call within 2 minutes, no loops.

## 7. Hub prohibition

One new module, no existing file edited, no `PORT_FILES`/`SOURCES` entry, no commit, no
promotion. Anything that seems to need one: stop and report with the price.

## 8. Verification

```bash
cd lean
python3 spec/check_port.py FLTForHuman/AlgebraicCurve/Differential/CorrespondenceRegular.lean  # expect 19 ok
python3 spec/check_port.py --changed                                                          # none failing
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Differential.CorrespondenceRegular
```

plus `#print axioms AlgebraicCurve.Differential.correspondence_mem_regularDifferentials`
(`[propext, Classical.choice, Quot.sound]`), the grep sweep (`sorry`/`admit`/`axiom`/
`native_decide`/`import Mathlib`/`maxHeartbeats`), 0 warnings, `git status --short`
showing only the new module, the frozen checker unchanged at 10473, and
`frontier.py --ds --target AlgebraicCurve.Differential.correspondence_mem_regularDifferentials --top 3`
reading `needed 0`.

## 9. Report shape

Module path, lines, declaration count (19 expected: 18 internal + the headline) and the
7/19 split as realized; the `check_port` output with the pin line each declaration
matched; build and warnings; the axioms line; the grep sweep; `git status`; the frozen
checker line; every deviation, with the `Ideal`/`Trace`/`Derivation` API drift named;
and confirmation that `exists_restrict_eq` was instantiated from `Bifibre.lean` rather
than restated.
