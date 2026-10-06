# V4 — the isogeny kernel controls the range: `exists_pointHom_comp_eq_of_ker_le_of_isCentred`

**Status: landed and reviewed 2026-10-06** — one set, one agent turn, no route
amendment; checker `5807 → 5809`; see §9 for the close-out and the Phase D
hand-off. Second Phase D set of the H5 column, after
[TOPIC-V3-translation-place-action.md](TOPIC-V3-translation-place-action.md) §9.
[TOPIC-H5-engine.md](TOPIC-H5-engine.md) §7 and
[TOPIC-port-plan.md](TOPIC-port-plan.md) §5 Phase D carry the node as H5's last
unfinished vocabulary item; V3 supplied one of its two prerequisites. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §0.2 (staffing), §2 (plan,
dedup, scout), §3.3–§3.5 (order, sets, build ladder), §3.7 (boundary), §4
(faithfulness). Record: [../../logs/velu-port.md](../../logs/velu-port.md).

## 0. The two nodes

**Headline.** `Theorems/Thm_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred.lean`:

```lean
theorem WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred
    {F : Type u} [Field F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    {V₀ V₁ V₂ : WeierstrassCurve.Affine F} [V₀.IsElliptic] [GenusOnePlaceGate V₀] [AbelTheorem V₀]
    [V₁.IsElliptic] [GenusOnePlaceGate V₁] [AbelTheorem V₁] [V₂.IsElliptic] [GenusOnePlaceGate V₂] [AbelTheorem V₂]
    [GenusOnePlaceGate.IsCentred V₀]
    (φ : IsogenyHomDatum V₀ V₁) (hNφ : NormFormulaAlong F φ.ι φ.hfin)
    (ψ : IsogenyHomDatum V₀ V₂) (hNψ : NormFormulaAlong F ψ.ι ψ.hfin)
    (hker : ∀ P : V₀.Point, φ.pointHom hNφ P = 0 → ψ.pointHom hNψ P = 0) :
    ∃ (χ : IsogenyHomDatum V₁ V₂) (hNχ : NormFormulaAlong F χ.ι χ.hfin),
      ∀ P : V₀.Point, χ.pointHom hNχ (φ.pointHom hNφ P) = ψ.pointHom hNψ P
```

**Prerequisite.** `Theorems/Thm_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq.lean`:

```lean
theorem WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    {V : WeierstrassCurve.Affine K} [V.IsElliptic]
    [GenusOnePlaceGate V] [GenusOnePlaceGate.IsCentred V] [AbelTheorem V]
    {F' : Type*} [Field F'] [Algebra K F'] (hrat : ∀ w : AlgebraicCurve.Place K F', w.IsRational)
    (φ₁ φ₂ : F' →ₐ[K] V.FunctionField)
    (hφ₁ : φ₁.toRingHom.IsIntegral) (hφ₂ : φ₂.toRingHom.IsIntegral)
    (hres : ∀ P : V.Point,
      (placeOfPoint P).restrictAlong φ₁ hφ₁ = (placeOfPoint P).restrictAlong φ₂ hφ₂) :
    φ₁ = φ₂
```

The headline's `S_` file imports the prerequisite; `port_plan`'s `layers` section
puts them in dependency order (`algHom_ext` layer 0, the headline layer 1). The other
V3-sibling prerequisite, `exists_algEquiv_restrictAlong_placeOfPoint_eq_add`, is
**landed** (`TranslationAlgEquiv.lean`), as is the `Thm_..._pointHom_apply_eq_sub` and
plain `natCard_ker_...` material the headline imports.

## 1. What is new, measured 2026-10-06

`tools/deps/port_advise.py` + `port_plan.py` on both nodes (§8):

```
raw S_ lines (both files: 988 + 361)                   1,349
  − duplicate copies (none: the two files share nothing by name)  0
  − boilerplate (imports / attributes / p2m_* / blank)  −79
  = distinct declaration groups (83)                   1,270
  − already in the port (vetted)                       −717
  = NET NEW MATH LINES                                   553
```

`port_advise` reports **33 declarations with an identical statement already in the
port (≈699 lines not to re-prove)**, all importable. An independent sweep gives 20
unsubstituted in the prerequisite file (262 nominal lines) and 33 in the headline
file (326 nominal); the rest of both files is the inlined, already-ported cone.

Of the unsubstituted, these are **not** new and must not be written: the scoped
`instFactNatPrime*` instances, `S13_instIsDedekindDomainCoordinateRing`,
`instHasPrincipalDivisorsFunctionField_s13`, and the `InfinitePlace` class fields
(`not_isFinitePlace`, `eq_of_not_isFinitePlace`) — the same drop list as V2 §9
finding 4 and V3 §1.2.

**Budget: ≈550 net new content lines, ×1.0–1.2 (transcription) = 550–700 written.**
That is below the playbook's ~1,000-line subagent threshold; the set is dispatched
anyway because the manager's context is the binding constraint (§0.2), not because
the size demands it.

## 2. Route, reuse map, and the V3 lesson

### 2.1 The mathematics, briefly

The headline is a **kernel-to-range** statement: if the kernel of `φ.pointHom` is
killed by `ψ.pointHom`, then `ψ.ι` factors through `φ.ι` — there is a `χ` with
`χ.pointHom (φ.pointHom P) = ψ.pointHom P`. The `S_` file's route:

1. `psi_range_le` reduces `ψ.ι.range ≤ φ.ι.range` to `fieldRange_eq_fixedPoints`, a
   **fixed-points** argument: the translation automorphism `τ R` of `V₀.FunctionField`
   (V3's headline!) acts on `φ.ι.fieldRange`, and the subgroup of translations that
   fix a given element is exactly the kernel of `φ.pointHom` — so the field range is
   the fixed field of the kernel and `kerActHom` is injective;
2. `exists_factor_of_range_le` (a general field-theory factoring lemma) then produces
   `ξ` with `φ.ι.comp ξ = ψ.ι`, and `finiteAlong_factor` + `isIntegral_of_finiteAlong`
   turn it into an `IsogenyHomDatum`.

The prerequisite is the **rigidity** lemma: an integral `K`-algebra hom into
`V.FunctionField` is determined by what it does to the degree-one places of `V`. Its
route is the `no3ahbad_riqsucr_a1a_*` chain: reduce `φ₁ f = φ₂ f` at every place to a
finite vanishing statement (`no3ahbad_…_finite_ord_ne_zero`), then compare the two
homs through residues at a rational place (`isUnit_mk_of_ord_eq_zero`,
`residue_ne_zero_of_ord_eq_zero`, `no3ahbad_…_exists_residue`,
`no3ahbad_…_ord_sub_pos_of_pos`).

### 2.2 Reuse — import, never redeclare

- **`finite_setOf_ord_ne_zero_of_finiteDimensional`** — **amended at the review
  gate: the pointer below was wrong.** The public copy at
  `FLTForHuman/AlgebraicCurve/P1/EnginePrelude.lean:652` (and the private copy at
  `PrincipalDivisors/Transcendence.lean:387`) is the *minpoly/`RatFunc`* statement
  (`[FiniteDimensional (RatFunc K) F'] [Algebra.IsSeparable]`), **not** the pin `S_`
  file's `[HasPrincipalDivisors K F']` form. The statement-identical public copy in
  the cone is `WeierstrassCurve/Isogeny/NatCard.lean:73`,
  `finite_setOf_ord_ne_zero_of_hasPrincipalDivisors`. The worker caught this by
  statement comparison — the §2.3 lesson firing on the order's own text.
- **`ord_sub_evalAt_pos`** — `AlgebraicCurve/Defs/PlaceCalculus.lean`
  (`AlgebraicCurve.Place.ord_sub_evalAt_pos`); **`evalAt_ne_zero`** —
  `AlgebraicCurve/Defs/PlaceEvaluationAlgebra.lean`
  (`AlgebraicCurve.Place.evalAt_ne_zero_of_ord_eq_zero`).
- **`isRational_of_deg_eq_one`** — `WeierstrassCurve/Velu/Discharge.lean:38`
  (and `AlgebraicCurve/P1/Dictionary.lean:59`).
- **`restrictAlong_algHomId`** — `AlgebraicCurve/Defs/RestrictAlongAPI.lean:71`;
  **`restrictAlong_congr`** — `AlgebraicCurve/Defs/Correspondence.lean:318`
  (the pin's `restrictAlong_congr_proof` is a different, instance-level helper and
  *is* new).
- **`placeOfPoint_injective`** — `WeierstrassCurve/Isogeny/NatCard.lean:410`;
  **`point_infinite`**, **`pointEnd'_eq_of_seam`** — `IsogenyEndDatum/Engine.lean`.
- **`exists_equation`**, **`isFinitePlace_iff_exists_placeOfEquation`**,
  **`mem_of_ord_nonneg`**/**`ord_nonneg_of_mem`** — `WeierstrassCurve/Place/*`.
- **`normFormulaAlong_of_finiteAlong`** (headline `S_` file L103) is the module's own
  `private normFormulaAlong_of_finiteAlong_aux` at
  `WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean:106`, specialised from a general
  `A →ₐ[K] B` to function fields. The headline uses it at
  `ξ : V₁.FunctionField →ₐ[F] V₂.FunctionField`, so the aux suffices: **call it, do
  not write the pin's generic version**.
- The whole inlined cone — the `CoordinateRing` dictionary, the `Place` calculus,
  the `IsogenyEndDatum` engine, the `_of_seam` idioms — is ported (717 vetted lines).

### 2.3 The V3 lesson, binding

**`port_advise`'s substitution test is name-anchored** (`by_name` on the last name
component of the port declaration), so "already in the port" is a **lower bound**,
and a pin `S_` file that re-proves a prelude under its own local names will look new
when it is not. Before transcribing anything, check the **statement**; and before
committing to a route, compute the **closure** of the declarations the chain
actually reaches across the pin (V3's amendment came from exactly that check, and
saved ≈130 duplicated lines). If the closure reaches a port declaration that the
chosen import does not supply, **stop and report** rather than duplicating it.

## 3. Deliverable

### 3.1 Home: append to `IsogenyEndDatum/Vocabulary.lean`

**Append both nodes to `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean`**
(177 → ≈750 lines). This is the file's own designated role: its header lists exactly
these as the H5 vocabulary tail, and it already carries the private
`normFormulaAlong_of_finiteAlong_aux` the headline needs. No new import is required —
Vocabulary's 101-module closure already contains `Engine`, `DualEndData`,
`P1/EnginePrelude`, `PlaceCalculus`, `PlaceEvaluationAlgebra` and `Transport`
(verified) — and the `TranslationAlgEquiv.lean` import is **not** needed by this set
(the headline `S_` file uses the V3 *statement* only through imports we already have;
check before adding it, and if it is needed, add it — it is in the same cone).

Measured cost of the alternatives (2026-10-06):

| home | size | cascade of a later edit | fixed edit-loop cost |
|---|---:|---|---|
| **append to `Vocabulary.lean` (chosen)** | 177 → ≈750 | 2 modules / 998 lines ≈14 s | **≈1 m 21 s** (101-module closure) |
| new `IsogenyEndDatum/AlgHomExt.lean` + `Vocabulary` | 0 → ≈450 | 0 + 2 modules | ≈24 s (Engine-only) + ≈1 m 21 s |
| new single module importing `DualEndData` | 0 → ≈750 | 0 modules | ≈1 m 21 s |

The append wins on the build ladder (one file, one cascade) and on role: the file
already exists for this tail, the private helper is in it, and one wave edits it once.

### 3.2 Declarations

**Public, at the pin names, statements verbatim from the wrappers:**

- `WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq`;
- `WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred`.

**Everything else `private`**: the `no3ahbad_riqsucr_a1a_*` chain,
`isUnit_mk_of_ord_eq_zero`, `residue_ne_zero_of_ord_eq_zero`, and the headline's
local helpers (`exists_factor_of_range_le`, `finiteAlong_factor`,
`isIntegral_of_finiteAlong`, `finrankAlong_eq_finrank_fieldRange`,
`finrank_toSubfield_eq`, `restrictAlong_congr_proof`, `hmap`, `hmap_seam`,
`pointHom_eq_hmap_sub`, `hmap_add_of_ker`, `placeOfPoint_inj`, `hrat_of_gate`,
`algEquiv_isIntegral`, `τ`, `τ_isIntegral`, `τ_seam`, `τ_add`, `τ_zero`,
`τ_eq_one_imp`, `kerActHom`, `kerActHom_apply`, `kerActHom_injective`,
`ker_smul_def`, `mem_fixedPoints_iff`, `fieldRange_le_fixedPoints`,
`finrankAlong_pos`, `fieldRange_eq_fixedPoints`, `psi_range_le`). Neither pin
`solution` is declared — the headline *is* the solution.

### 3.3 Checker wiring and consumer

- `spec/check_flt_statements.py`: `Vocabulary.lean` is **already** in `PORT_FILES`, so
  no entry is added; append the two wrappers to `SOURCES` **last**. The `S_` files are
  **not** added (the helpers are `private`). Expected: `5807 → 5809 identical`,
  `promoted` unchanged at 311, `0 mismatched / 0 missing`.
- `spec/IsogenyEndDatumConsumer.lean` (**append one zone; the only existing file this
  topic edits**): the module is in the `DualEndData` cone, so it can never be imported
  beside `Velu/RestrictAlong.lean` or `GenusOnePlaceGateCentred.lean`; the gate
  instances stay hypotheses exactly as in zones 3 and 5. Two real executed
  compositions, no `#check`, no `sorry`:
  - the rigidity node applied at the consumer's `W1` to two integral homs that agree
    on `placeOfPoint` (e.g. an `AlgEquiv` and its inverse composed, or two
    `translationAlgEquivOf`s at points with equal action), concluding the homs are
    equal;
  - the headline with `φ`, `ψ`, `hker` supplied as hypotheses and the produced `χ`
    fed through the ported `IsogenyHomDatum.pointHom_apply_eq_sub` /
    `placeOfPoint` / `restrictAlong` API so that deleting the new declarations makes
    the file fail.

## 4. Work order

### 4.1 Scope

Port the two nodes of §0 — the function-field rigidity lemma and the kernel-to-range
factoring theorem — into `Vocabulary.lean`, reusing the ported cone and the V3
headline, and extend the consumer.

**Not this topic:** the sibling nodes
`IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_separableAlong`,
`WeierstrassCurve.Affine.algHom_eq_of_forall_restrictAlong_placeOfPoint_eq`,
`AlgebraicCurve.algHom_eq_of_forall_restrictAlong_eq_of_charZero` (all unported, all
*outside* this chain — the prerequisite `S_` file inlines its own copy of
`no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq` at L907, so this
set does not need them); `IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`;
the collision refactor. A worker who reaches an unported prerequisite outside this
scope **stops at the boundary and reports**.

### 4.2 Reconnaissance (bounded, before writing; report the outcome)

1. Confirm the checker baseline: `python3 spec/check_flt_statements.py` →
   `5807 identical / 311 promoted / 0 mismatched / 0 missing / 36 own`.
2. Statement-check every unsubstituted declaration of the two `S_` files against the
   port (§2.2's list plus anything the name sweep misses), and report the drops with
   `grep -c`. In particular confirm `finite_setOf_ord_ne_zero_of_finiteDimensional`
   is `P1/EnginePrelude.lean:652` and that the module reaches it.
3. Compute, in the pin, the closure of the two `solution`s' same-file references and
   confirm it stays inside Vocabulary's closure; report anything that does not.
4. Scout `no3ahbad_riqsucr_a1a_algHom_ext_of_restrictAlong_placeOfPoint_eq` (the 70-line
   core) in a gitignored `tmp/` scratch file before writing the module; report its
   `lake env lean` time.

### 4.3 Source (pin)

Paths relative to the pin root
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/>):

- the two wrappers of §0 (statement authority);
- `P2M/Sol/S_WeierstrassCurve_Affine_algHom_ext_of_forall_restrictAlong_placeOfPoint_eq.lean`
  (988 lines) — the new block is `isUnit_mk_of_ord_eq_zero` L682, `residue_ne_zero_of_ord_eq_zero` L693,
  `finite_setOf_ord_ne_zero_of_finiteDimensional` L806 (reuse), and the
  `no3ahbad_riqsucr_a1a_*` chain L840–976, then `solution` L977;
- `P2M/Sol/S_WeierstrassCurve_Affine_IsogenyHomDatum_exists_pointHom_comp_eq_of_ker_le_of_isCentred.lean`
  (361 lines) — L37–332 are the helpers of §3.2, `solution` at L333;
- ignore the `p2m_export` / `p2m_open` / `p2m_reactivate` scaffolding and the empty
  `section … end` stubs (V3 friction 3: dropping them can cost an explicit
  `variable`, so check each lemma's free variables).

### 4.4 Route, with recorded negatives

- **`hrat` at the consumer.** `algHom_ext_…` takes `hrat : ∀ w, w.IsRational`; the
  headline supplies it through its local `hrat_of_gate` (the gate plus
  `isRational_of_deg_eq_one`). Keep that split.
- **`algEquiv_isIntegral` is trivial**: an `AlgEquiv`'s `toAlgHom` is surjective, so
  integrality is `RingHom.isIntegral_of_surjective` (the V3 module uses the same
  idiom). The pin proves it as a separate lemma; keep it `private` and short.
- **`restrictAlong_congr` is ported at `Correspondence.lean:318`** but the pin's
  `restrictAlong_congr_proof` is an *instance-level* helper with a different
  statement — diff the two before assuming.
- **`Fintype.card`/`Nat.card` and `Multiplicative.toAdd`** appear in
  `fieldRange_eq_fixedPoints`; these are mathlib and should transcribe, but the
  `FixedPoints.finrank_eq_card` API is the load-bearing one — `#check` it first.
- **`τ_add` / `τ_zero` / `τ_eq_one_imp`** build a monoid hom `V₀.Point →*
  (V₀.FunctionField ≃ₐ[F] V₀.FunctionField)` out of V3's headline and then prove it
  injective by `algHom_ext_…`; this is the one genuinely new mathematical idea in the
  set and should be written as the pin writes it.

### 4.5 Stop-early risks (stop and report, do not push)

- **A `no3ahbad_*` step that does not transpose**, or the 70-line core over the build
  bound. Report the two statements.
- **A statement in a wrapper that differs from the `S_` file's copy: the wrapper wins**;
  report the difference.
- **Any pull toward `RRSpace`/`GenusOnePlaceGateCentred`** to discharge the gate
  instances — the collision boundary. Stop and report.
- **Any unported name the closure reaches**: report it rather than duplicating it
  (§2.3).

## 5. Build discipline (copy into the work order)

`lake env lean <opts> <file>` is the edit loop, with `<opts>` =
`-DmaxHeartbeats=4000000 -DautoImplicit=false`; `lake build <module>` when a file is
done; **one** `lake build` per wave; the full build at the milestone. Bound every
build (`timeout 60` / `90` / `300` / `180`), serialize every `lake build` with
`flock` (the lock lives at `lean/.lake/flt_build.lock`, never `/tmp`), and time it.
Never raise `maxHeartbeats`; the project's global cap is already 4,000,000. Never
`import Mathlib` in a library module.

Measured: the `Vocabulary` cone (101 modules) costs **≈1 m 21 s** fixed per
`lake env lean`; the `lake build` of the edited module is the wave's only library
build, and editing `Vocabulary.lean` cascades **2 modules / 998 lines ≈14 s**.
**Batch** — the edit loop re-elaborates the whole file, so land a bounded block per
check.

## 6. Verification

- `lake env lean` clean; `lake build FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Vocabulary`;
  then the one wave build (`Vocabulary` + its two dependents).
- `python3 spec/check_flt_statements.py` → `5809 identical`, `promoted` 311,
  `0 mismatched / 0 missing`, 36 own-proof exempted.
- The manager's one-token probe at the milestone (mutate `φ₁ = φ₂` or the headline's
  conclusion, expect exactly one `mismatched`, revert).
- `spec/IsogenyEndDatumConsumer.lean` exit 0.
- `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`; no
  `sorry`.
- `grep -c` of every declaration dropped or reused, with the reason.

## 7. Risk register

| risk | mitigation | status |
|---|---|---|
| the 1,349-line figure prices a silo | `port_advise`/`port_plan` first: net new 553 | **measured**; §1 |
| a differently-named port copy is missed | statement check, not name (§2.3) | open — the tool is name-anchored |
| the closure reaches outside the chosen import | closure check before writing (§2.3, §4.2.3) | open |
| the rigidity core does not transpose | scout the 70-line core (§4.2.4) | open — the one real unknown |
| the consumer cannot discharge the gates | hypothesis form, as zones 3 and 5 | settled (collision, V2 §2.1) |
| appending to `Vocabulary.lean` cascades | 2 modules / 998 lines ≈14 s, one wave | **measured** |
| the pin's empty section skeleton is dropped | re-add explicit `variable`s where needed (V3 friction 3) | expected |

## 8. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes \
  WeierstrassCurve.Affine.IsogenyHomDatum.exists_pointHom_comp_eq_of_ker_le_of_isCentred,\
WeierstrassCurve.Affine.algHom_ext_of_forall_restrictAlong_placeOfPoint_eq \
  --json build/v4_advise2.json
python3 port_plan.py --json build/v4_advise2.json --json-out build/v4_plan2.json

python3 build_ladder.py --edit lean/FLTForHuman/WeierstrassCurve/IsogenyEndDatum/Vocabulary.lean
python3 build_ladder.py --edit lean/FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DualEndData.lean
```

The 2026-10-06 run is in `tools/deps/build/v4_{advise2,plan2}.{txt,json}` (untracked).

## 9. Close-out

**Landed and reviewed 2026-10-06**, one set and one subagent turn, no route
amendment.

| artifact | lines | notes |
|---|---:|---|
| `IsogenyEndDatum/Vocabulary.lean` | 177 → 643 | one added import (`…TranslationAlgEquiv`, the case §4.2.3 anticipated); appended block L184–643; **2** new public headlines + 40 `private`; 0 `sorry` |
| `spec/check_flt_statements.py` | +7 | the two wrappers last in `SOURCES` (L2164–2165); `PORT_FILES` untouched; no `S_` files |
| `spec/IsogenyEndDatumConsumer.lean` | 253 → 313 | zone 6 (60 lines), the only existing spec edited |

**Measured.** Scout of the 70-line rigidity core: 1 m 44.7 s (contended) for a
197-line scratch; full scratch 499 lines / 54.4 s; edit loop on `Vocabulary.lean`
56 s → 75 s; wave `flock lake build Vocabulary && lake build CharPolySquare` 245 s
(3 modules; incremental re-run 11 s — against the ≈14 s predicted for the 2-module
cascade); consumer 62 s agent, **1 m 25 s re-run by the manager**, exit 0,
warning-free; axioms probe clean.

**Checker.** `5807 → 5809 identical` (311 promoted unchanged), `0 mismatched /
0 missing`, 36 own-proof exempted, 5,845 checked, exit 0. The manager's one-token
probe — `φ₁ = φ₂` → `φ₂ = φ₁` on the **public** prerequisite conclusion — gave
exactly `5808 / 1 / 0`, reverted byte-identically to `5809 / 0 / 0`. (Both the worker
and the manager first mutated the *private* `no3ahbad_*` copy, which the checker
correctly never reads; that is a good property of the instrument and a warning for
whoever writes the next probe.) Axioms on both headlines:
`[propext, Classical.choice, Quot.sound]`.

**Reuse that landed under other names** (the §2.3 lesson, three times): the pin's
`isUnit_mk_of_ord_eq_zero` / `residue_ne_zero_of_ord_eq_zero` / `evalAt_ne_zero` are
already public in `Defs/PlaceEvaluationAlgebra.lean`; the pin's
`finite_setOf_ord_ne_zero_of_finiteDimensional` is
`finite_setOf_ord_ne_zero_of_hasPrincipalDivisors` (`NatCard.lean:73`) — see the §2.2
amendment; the pin's generic `normFormulaAlong_of_finiteAlong` is the module's own
pre-existing private aux; the pin's `natCard_ker` is the module's own
`natCard_ker_pointMapOfPushforward_eq_finrankAlong`. One private local proof was
written where the only port copy is outside the cone (`finrankAlong_pos`, 3 lines).

**Closure.** Both `solution`s' same-file closure stays inside Vocabulary's cone
except the V3 headline, which is why `TranslationAlgEquiv` was imported — same
`DualEndData` cone, no cycle, no name collision. No unported prerequisite was
reached, so no duplication was created.

**Deviations, all recorded in [../../logs/velu-port.md](../../logs/velu-port.md).**
`no3ahbad_…_ord_pos_of_restrictAlong_ord_pos` calls the ported
`Place.ramificationIndexAlong_pos` instead of the pin's inline `unfold …`; the pin's
scoped `instHasPrincipalDivisorsFunctionField_s13` disappeared with the section
stubs and `…_finite_ord_ne_zero` supplies the instance from
`hasPrincipalDivisors_functionField`; `Set.mem_setOf_eq` is deprecated on v4.34.0
and became `Set.mem_ofPred_eq`, so both files are warning-free.

**Phase D after V4.** The H5 vocabulary tail is closed: both nodes
`TOPIC-H5-engine.md` §7 stopped are now landed, and the only Phase D item left is
`IsogenyEndDatum.aeval_j_diag_eq_zero_of_finrankAlong_eq`, still gated on the
`PeriodPair` uniformization ladder. That item is scoped, and it is **not a tail**:
[TOPIC-V5-periodpair-uniformization.md](TOPIC-V5-periodpair-uniformization.md) measures
its unported closure at 17 nodes / 15,179 pin lines, with the two classical theorems
(complex uniformization, surjectivity of `j`) on the path, and recommends a math scout
before any work order. A pre-existing duplicate — not a collision —
was found and registered: `isRational_of_deg_eq_one` is public at the same FQN in
`AlgebraicCurve/P1/Dictionary.lean:59` and `WeierstrassCurve/Velu/Discharge.lean:38`;
the two copies are byte-identical, so the co-import succeeds silently and the two
modules are *not* unimportable together (verified).
