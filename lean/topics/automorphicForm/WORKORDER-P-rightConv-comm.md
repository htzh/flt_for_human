# WORKORDER-P — the right-convolution commutation headline: the proof half (P0–P3)

**Status: LANDED (2026-10-11/12), in two rounds.** This was the proof half of
[TOPIC-rightConv-comm.md](TOPIC-rightConv-comm.md) (§4.9); the definition gate it waited on is closed
(W1–W12, §4.7). The phase ran as a **phase order**: three sets in series, round 1 = P0 + P1 (the
generic engine), round 2 = P2 + P3 (the adelic instantiation, the three headlines, the consumer,
the verification). No blockers, no promotions, no pre-existing module edited.

**Outcome.** Eleven new modules, 3,866 written lines (headers included) against the 3,824 measured
net new math lines:
`RepTheory/{TypeSpan 165, AntiInvolutionHaar 454, ProjectedHaar 702, BiIsotypic 1,026}` and
`AutomorphicForm/Adelic/RightConvComm/{Frame 283, PlaceClassData 501, SliceCentrality 261,
MeasureAssembly 234, Compact 80, Level 73, Principal 87}`. **P0 answered yes for both
instantiations**, so `Compact.lean` transcribes the compact `solution` while `Level.lean` and
`Principal.lean` are derivations (`hUO := rfl` via `CarrierPins.productionPinsOf_U`, `hO` from
`AdelicLevel.isOpen_levelOne` / `TestFnPrincipalLevel.isOpen_finitePrincipalLevel`, `hU` from
`IsCompact.image` over the landed finite-level compactness plus the frame separation landed in P2).
The two-bodies trap (work order §1) is closed by one public body per pin name; `continuous_finEmbed`
lands `private` in `Frame.lean` (no pin declaration to promote against). Verification, all
manager-run: checker **9205 identical (648 promoted, 83 renamed), 0 mismatched, 0 missing**, 38 own
(9243 checked) — the +106 is exactly +103 P2 declarations (all promoted) and the three headlines;
**0 warnings** on all eleven modules; milestone whole-tree `lake build` **9,467 jobs, exit 0**;
consumer Zone P green at the 4,000,000 cap; `#print axioms` on the three headlines all
`[propext, Classical.choice, Quot.sound]`; a one-token mutation on each headline caught as exactly
one `mismatched`, reverted. One pre-existing deprecation warning sits outside this phase
(`WeierstrassCurve/Isogeny/TwoCurveDescent.lean:298`, `if_true` → `ite_true`).

It was a **phase order**: three
sets, executed **in series, one at a time**, each with its own gate (§7). The sets are recorded
below as written.

The phase covers **three headlines** — the level-`N` one, its compact/general parent, and the
`principalLevel` sibling. The third silo was measured separately and folded in (§1): it is the same
engine with `principalLevel` in place of `levelOne` in a handful of places, so it costs **+109 net
new lines** here against ≈3.5k if it were ever cut on its own, and writing it while the engine is
being homed is the only way to keep the general-`U` spelling honest.

**New files only. No existing Lean module is edited; no promotion is authorised; no new definition
layer is needed.** Every definition the three headlines name is already landed and
checker-registered (W11 `IsotypicCuspSpace`, W12 `CuspidalConstituent`/`ArchSpherical`, the W1–W10
foundation, and — for the principal spelling — `AutomorphicForm/Adelic/RightConvNeZeroPrincipal.lean`).
The subagent that believes an edit to an existing module is required **stops and reports** (§8).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Checker baseline **8926 identical (372 promoted, 83 renamed), 0 mismatched, 0 missing,
38 own (8964 checked)**. Target: `identical` **+3** (the three headlines) and `promoted` **+≈300**
(the shared engine is `private` at the pin, so it lands as promoted — §6), `0 mismatched / 0 missing`.

## 1. The phase, measured (2026-10-11, `tools/deps` against the closed gate)

`port_advise` over the three proof silos, then `port_plan`:

| quantity | the twin (plain + compact) | **the trio** (+ principal) |
|---|---:|---:|
| raw `S_` lines (47-node slice) | 6,865 | 10,363 |
| declaration lines | 6,813 | 10,284 |
| of which duplicate copies | 3,098 | 6,454 |
| distinct declaration groups | 291 | 304 |
| **net new math lines** | **3,715** | **3,824** |
| one **shared block** | 2,923 lines / 235 decls (2 files) | **3,178 lines / 248 decls (3 files)** |
| names proved in ≥2 target files | — | 252 (≈6,160 removable lines) |
| substitutions already in the port | 0 | 1 (`mem_map_conj_iff`, 6 lines) |
| port name clashes | 0 | 0 |

**The dedup is the point, and the third silo is nearly free.** The three silos are 3,440 / 3,425 /
3,498 lines (277 / 270 / 284 declarations by the checker's parser); **269 declarations are shared
by all three**, 7 more by plain and principal only, and the genuinely principal-only surface is
**8 declarations**, of which `solution` is the headline and `mem_map_conj_iff` is already in the port
(`AutomorphicForm.TestFnPrincipalLevel.mem_map_conj_iff`). Written separately the trio is ≈10.3k
lines for one theorem plus two specializations; written once it is **3,824 net new**, i.e. **+109
lines** over the twin for the whole principal headline.

**The dedup is not a free corollary.** `port_advise` says `VARIANT: hypotheses differ both ways`:
the level/principal files carry `(N : Ideal) (hN : N ≠ ⊥)` and the level-spherical hypothesis at
`(productionPinsOf …).U N`, the compact file carries abstract `U`, `O`, `IsCompact U`, `IsOpen O`,
`hUO : U = O ⊓ finiteAdelicGL2Subgroup F`. So the port writes the **general `U` spelling once** and
derives both specializations (P0, P3).

**Hand-checked, and the parser cannot see it: four private names carry two different bodies.** The
checker compares statement text only, and `port_advise`'s suspect scan reports nothing, yet:
`MeasureAssembly.levelSubgroup` is `levelOne N ⊓ finiteAdelicGL2Subgroup F` in the twin and
`principalLevel N ⊓ …` in the principal silo; `MeasureGlue.pins_U` and `MeasureGlue.glFin_image_level`
likewise spell the two levels; and `MeasureAssembly.archNu` exists in the `N` spelling (level and
principal) and in the compact file's `U` spelling. Write **one** declaration per pin *name*: the
general `U` form where the engine is concerned (`archNu`, `levelSpherical_eq_*`, `adelicKernel_comm`),
and where a name exists only in the level/principal spellings (`levelSubgroup`,
`isOpen`/`isClosed`/`isCompact_level_image`, `glFin_image_level`, `pins_U`) the spelling the module's
public surface needs — the level-`N` one, matching the pin's plain copies. The other body is written
`private` with its own name inside the specialization that needs it — the checker skips private port
declarations, so it costs nothing and cannot show as `MISSING`.

**Explicitly not this order.** The other `AutomorphicForm` siblings are separate subjects on
separate def closures and must not be started here: `cosetSum_rightConv_of_isLevelSphericalOfType`
and the `exists_isFactorizableTestFn_rightConv_ne_zero_of_*` family. Also not here: any
`Definitions/` edit, any promotion, and the `attribute [-simp]` / `attribute [-instance]` preludes at
the head of the three wrappers (pin-side suppression plumbing;
[TOPIC-rightConv-comm.md](TOPIC-rightConv-comm.md) §3.2).

## 2. Pin sources

Statement authority is the `Theorems/` wrapper; proof authority is the `P2M/Sol/S_` file. Pin
`aa2d8b3`.

| target | wrapper (statement) | proof |
|---|---|---|
| level-N headline | `Theorems/Thm_AutomorphicForm_rightConv_rightConv_comm_of_isLevelSphericalOfType.lean` (26 lines) | `P2M/Sol/S_…_isLevelSphericalOfType.lean` (3,440; `solution` at :3420) |
| compact headline | `Theorems/Thm_…_isLevelSphericalOfType_of_isCompact.lean` (27 lines) | `P2M/Sol/S_…_of_isCompact.lean` (3,425; `solution` at :3377) |
| principal headline | `Theorems/Thm_…_isLevelSphericalOfType_principal.lean` (27 lines) | `P2M/Sol/S_…_principal.lean` (3,498; `solution` at :3478) |

The three statements, verbatim (binders, order and spellings are the checker's contract); the
principal one differs from the level one in exactly the two `levelOne` → `principalLevel`
occurrences, and the compact one replaces the level hypothesis by an abstract carrier:

```lean
theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
        ((productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h)
    (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact
    (F : Type) [Field F] [NumberField F]
    (U : Subgroup (AdelicGL2 (𝓞 F) F)) (hU : IsCompact (U : Set (AdelicGL2 (𝓞 F) F)))
    (O : Subgroup (AdelicGL2 (𝓞 F) F)) (hO : IsOpen (O : Set (AdelicGL2 (𝓞 F) F)))
    (hUO : U = O ⊓ finiteAdelicGL2Subgroup F)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) U f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h)
    (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ U, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f

theorem AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal
    (F : Type) [Field F] [NumberField F] (D : Set (AdelicGL2 (𝓞 F) F)) (N : Ideal (𝓞 F)) (hN : N ≠ ⊥)
    (τ : ∀ w : InfinitePlace F, ArchRepAt F w) (hirr : ∀ w, (τ w).ρ.IsIrreducible)
    (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsLevelSphericalOfType F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F)
        ((productionPinsOf F D (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
          (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N) f)
    (h : AdelicGL2 (𝓞 F) F → ℂ) (hh : IsFactorizableTestFn F h)
    (hht : IsArchBiFinite F (⟨fun _ => 1, fun w _ => τ w⟩ : AutomorphicForm.ArchTypeFamily F) h)
    (hhU : ∀ x : AdelicGL2 (𝓞 F) F, ∀ u ∈ (productionPinsOf F D
        (fun N => principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F)
        (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N, h (u * x) = h x ∧ h (x * u) = h x)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ) :
    rightConv F (rightConv F φ f) h = rightConv F (rightConv F φ h) f
```

`hf` must keep the wrapper's `(productionPinsOf …).U N` spelling, **not** its
`MeasureAssembly.levelSubgroup F N` unfolding, or the checker reports `MISMATCH` (the two are
definitionally equal, not syntactically).

## 3. The sets

Layer line ranges are the plain `S_` file's; the other two are offset by a few dozen lines (their
layer maps are in [TOPIC-rightConv-comm.md](TOPIC-rightConv-comm.md) §3.1).

### P0 — the scout (before P3; ≈50 lines, untracked `lean/tmp/P-scout.lean`)

Answer, with a compiling probe and the quotation, **for both instantiations**:

> With `O := levelOne (𝓞 F) F N` and `U := (productionPinsOf F D (fun N => levelOne (𝓞 F) F N ⊓
> finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v) (adelicBox F)).U N` — and again with
> `principalLevel` for `levelOne` — does the specialization follow from the compact headline by
> `hUO := rfl` (that is, is `.U N` the level subgroup by `rfl`), `hO` from the level's open-image
> lemma, and `hU` from the level's compact lemma (`isCompact_level_image'` plus injectivity of
> `glFin` on `ker glArch`, `eq_of_glArch_eq_of_glFin_eq`)?

If yes, `Level.lean` and `Principal.lean` are a few dozen lines each. If no, say which hypothesis
fails and in which direction, and P3 transcribes the failing `solution` behind the same shared home.
The scout also settles two `def`-level questions and must report both: whether `MeasureAssembly.archNu`
may be mathlib's Haar measure on the archimedean group rather than the pin's pushed-forward measure,
and whether the `BiIsotypic` engine stays stated over `Representation ℂ G V` (as the pin writes it)
rather than over functions on the archimedean adeles. **Neither answer may change a statement text.**

### P1 — the generic engines (new files; ≈2.3k lines)

| module | pin contents (plain `S_` line ranges; namespaces are the pin's) |
|---|---|
| `FLTForHuman/RepTheory/ProjectedHaar.lean` | `ProjectedHaar` frame and engine 25–447 (`Frame`, `slab`, `level`, `slice`, `cut`, `nu`, `nu_isHaarMeasure`, `convKer`, `convKer_cut_comm`, the algebra/equiv-kernel blocks); `KernelReduction` 675–777 (`rc`, `rc_rc`); `KernelSides` 1122–1287 (factors, indicators, linearity of `convKer`) |
| `FLTForHuman/RepTheory/AntiInvolutionHaar.lean` | `AntiInvolutionHaar` 461–669; `RotationConjugacy` 1383–1460, `HalfTurnConjugacy` 1460–1554, `HalfTurnAxis` 1554–1591 (2×2 normal forms over `ℝ`/`ℂ`) |
| `FLTForHuman/RepTheory/TypeSpan.lean` | `TypeTransfer` 2067–2205 (pullback along a hom, the type submodule, slice bi-finiteness) |
| `FLTForHuman/RepTheory/BiIsotypic.lean` | `BiIsotypic` 2210–3200 (the multiplicity-one engine of [TOPIC-rightConv-comm.md](TOPIC-rightConv-comm.md) §2.4: density, contraction, `span_translates_invariants_eq_top'`, `isIrreducible_dual`, `le_span_translates_invariants`, the pairing, `leftRep`/`rightRep`/`invMap`, `mem_typeSpan_leftRep_of_inv_mem`) |

### P2 — the adelic instantiation (new files; ≈1.1k lines)

| module | pin contents |
|---|---|
| `FLTForHuman/AutomorphicForm/Adelic/RightConvComm/Frame.lean` | `SecondCountableAdelic` 786–877; the adelic `ProjectedHaar` block 885–940 (`adelicFrame`, its continuity, separation `eq_of_glArch_eq_of_glFin_eq`); `MeasureGlue` 949–1011 (`glBorel`, `haar_facts`, `glArch_eq_one_of_mem`, `glFin_image_level`) |
| `…/RightConvComm/MeasureAssembly.lean` | `MeasureAssembly` 1020–1119 and 1290–1380: `archNu`, `adelicKernel`, `rightConv_rightConv`, test-factor continuity/support and `levelSpherical_eq_*` at the **`U` spelling** (the compact file's forms — it assumes, rather than proves, the carrier facts); **plus** the level-`N` side facts both derivations need (`levelSubgroup`, `isOpen`/`isClosed`/`isCompact_level_image`, `isOpen_glFin_preimage_image_level`, `isCompact_glFin_image_level`, `glFin_image_level`, `pins_U`), one public copy each at the pin's names. The `principalLevel` twins of the two-bodied ones go `private` in `Principal.lean` (§1) |
| `…/RightConvComm/PlaceClassData.lean` | `PlaceClassData` 1594–2062: place data, `thetaArch`, `convKer_comm_of_place_invariant` |
| `…/RightConvComm/SliceCentrality.lean` | `SliceCentrality` 3203–3417: `convKer_comm_of_types`, `convKer_comm_slice`, `adelicKernel_comm` |

### P3 — the three headlines (new files; ≈0.5k, or a few dozen lines each if P0 says yes)

| module | row |
|---|---|
| `…/RightConvComm/Compact.lean` | `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact`, proved from the compact `solution` |
| `…/RightConvComm/Level.lean` | `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType`, derived per P0 (or transcribed) |
| `…/RightConvComm/Principal.lean` | `AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal`, derived per P0 (or transcribed) |

## 4. Naming, namespaces and the public/`private` split

* **Keep the pin's top-level namespaces verbatim** (`ProjectedHaar`, `AntiInvolutionHaar`,
  `KernelReduction`, `KernelSides`, `RotationConjugacy`, `HalfTurnConjugacy`, `HalfTurnAxis`,
  `TypeTransfer`, `BiIsotypic`, `SecondCountableAdelic`, `MeasureGlue`, `MeasureAssembly`,
  `PlaceClassData`, `SliceCentrality`) and declare in them. The pin escapes its `S_`-file namespace
  with `private def _root_.ProjectedHaar.convKer …`, so the helpers' *visible* qualified spelling is
  `ProjectedHaar.convKer`; reproducing it is what keeps every cross-namespace **statement text**
  identical. A port prefix would move that text and show up as `MISMATCH`.
* **The engines are public; the one-sided leftovers are `private`.** The three headlines are public
  at the wrappers' names. Nothing else needs a promotion.
* The checker iterates only a port module's non-`private` declarations, so the level and principal
  private copies are simply **not written**: the general `U` spelling is written once and
  `Level.lean`/`Principal.lean` instantiate it, carrying any second-body helper as a `private`
  declaration with its own name.
* `P2M.Util` (`p2m_exact_reverting`) is not ported. State each wrapper's statement and transcribe
  the `solution` proof body — the house precedent is
  [`FLTForHuman/AutomorphicForm/Adelic/RightConvNeZero.lean`](../../FLTForHuman/AutomorphicForm/Adelic/RightConvNeZero.lean),
  and its principal twin `…/RightConvNeZeroPrincipal.lean` shows the same shape.
* Do **not** transcribe the wrappers' `attribute [-simp]`/`[-instance]` preludes. If a `simp` call
  relies on one, write the explicit rewrite instead.

## 5. What is already in the port — import, never re-prove

* The definition layer: W11 `IsotypicCuspSpace` (`ArchRepAt`, `ArchTypeFamily`,
  `IsArchFactorBiFinite`, `archRowIsometryInclAt₀`, `rowIsometryInclAt₀`, `archCutSubmodule`,
  `typeSubmodule`, `charRep`, `mem_typeSubmodule_charRep_iff`, …), W12 `CuspidalConstituent` /
  `ArchSpherical` (`IsLevelSphericalOfType`, `IsArchSphericalOfType`, `IsCuspSubrep`, …), and W1–W10
  (`rightConv`, `IsFactorizableTestFn`, `AdelicLevel.*`, `adelicBox`, `heckeGen`, `productionPinsOf`,
  `AdelicHaar.*`, `AdelicHaar/MulRightInvariant`).
* **The principal spelling's side facts are already landed**, in
  `AutomorphicForm/Adelic/RightConvNeZeroPrincipal.lean` under
  `AutomorphicForm.TestFnPrincipalLevel`: `weylFin`, `finitePrincipalLevel`, `mem_map_conj_iff`
  (the trio's one measured substitution), `mem_principalLevel_iff_glFin`,
  `isOpen/isClosed/isCompact_finitePrincipalLevel`. Import them; do not re-derive them in
  `MeasureAssembly.lean`, and do not restate `mem_map_conj_iff`.
* `port_advise` reports **0 name clashes** for the slice, so nothing the silos declare is already
  public under the same name in the port. If a helper's statement *is* one of the landed ones, delete
  the local copy and quote the port module in the report.

## 6. Verification, per set

* **Checker.** `timeout 300 python3 spec/check_flt_statements.py`, `0 mismatched / 0 missing`.
  Reconcile the delta before building: this phase adds the three headlines as `identical` (+3) and
  the promoted engine as `promoted` (+≈300, the pin's private declarations); `promoted` rising is the
  expected signal, and a `MISSING IN FLT` line means a public helper has no pin counterpart under its
  last name — fix the name, do not exempt it.
* **Build.** Tier 0 the edit loop; tier 1 `lake build <module>` per finished module; **0 warnings**.
* **Consumer.** `spec/AutomorphicFormConsumer.lean` gains one zone per set: for P1 a concrete
  non-vacuous instance of the generic `convKer_cut_comm` on a finite group frame; for P2 the adelic
  frame's separation and `levelSpherical_eq_cut`; for P3 all three headlines at a concrete `N = ⊤`
  (`levelOne`), at a compact `U`, and at `principalLevel`. Deleting any one module it imports must
  break the zone.
* **Axioms.** `#print axioms` on all three headlines → `[propext, Classical.choice, Quot.sound]`; no
  `sorry`/`admit`/`native_decide`, in `def`s included; no bare `import Mathlib`; no heartbeat
  override anywhere.
* **Mutation test.** One-token mutation on each headline → exactly one more `mismatched`, reverted.
* **Faithfulness.** Statements verbatim from the wrappers, binder names included; a `def`/`abbrev`
  taking type arguments keeps the pin's `variable … in` form; header prose in `/- … -/`.

## 7. Build discipline (verbatim)

* edit loop `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` (writes
  no `.olean`, builds no dependent);
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done;
* **no whole-tree `lake build`** while a set is in flight; the manager runs the milestone build;
* every `lake build` serialized and bounded; **never raise the heartbeat cap**.

**Diagnostic bound before believing a timeout.** For a red or slow module run the low-cap form first
— `timeout 120 lake env lean -DmaxHeartbeats=200000 -DautoImplicit=false <file>` — which finishes in
seconds to a minute and still prints the target lines. It separates genuine compute from an
impossible unification, an instance diamond, or a dropped import (the W11 `Representation` case;
[../../../studies/d6-two-curve-descent-review.md](../../../studies/d6-two-curve-descent-review.md) §5).
The pin carries **no** heartbeat budget here, so a site that needs the cap raised is a site whose
proof shape is wrong. A genuine blow-up is bisected, never re-run with a bigger cap.

## 8. Stop and report

Stop and report, with the quotation and the pin line, if: a statement cannot be matched without
moving the pin's text (the `hf` spelling of §2 is the known trap); a proof needs an unported
`Definitions/` module — report the `import` verbatim; a helper is genuinely needed publicly and is
`private` in a hub (**a promotion is the manager's; this includes anything under `Definitions/`,
`RepTheory/` and `AutomorphicForm/Adelic/`**); the P0 scout contradicts the general-`U` route for
either specialization; or a build exceeds its bound and bisecting does not settle it. Do **not** open
the other `AutomorphicForm` siblings, do not edit the definition modules, and do not reach past this
phase into the Deligne–Serre gates.

## 9. Completion report

Per set: module paths and line counts; public/`private` counts; tier-0 wall/CPU and warnings (target
**0**); tier-1 result; every local `private` re-derivation with its host; the checker before → after
with the `identical` and `promoted` deltas reconciled against the new surface; the P0 verdict with
its quotation; the consumer zone and its build; `#print axioms` on all three headlines; the mutation
tests, caught and reverted; `git status --porcelain` showing only this phase's files; anything you
could not match, quoted.

## 10. Reproduce

```bash
cd tools/deps
python3 port_advise.py \
  --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType \
  --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_of_isCompact \
  --nodes AutomorphicForm.rightConv_rightConv_comm_of_isLevelSphericalOfType_principal \
  --json build/ds-trio.json       # the 3,178-line / 248-declaration shared block and the drags
python3 port_plan.py --json build/ds-trio.json --section all    # 3,824 net new math lines
python3 port_plan.py --json build/ds-twin.json --section all    # 3,715 for the twin alone
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --top 0
cd ../lean
python3 spec/check_flt_statements.py                            # 8926 / 0 / 0 / 38 own
```
