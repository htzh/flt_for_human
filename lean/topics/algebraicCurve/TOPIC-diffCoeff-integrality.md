# TOPIC — the `diffCoeff` layer: the coefficient against a uniformiser, and its integrality

**Status (2026-10-24): landed and green; this note is both the cut plan and the
landing record.** The three `AlgebraicCurve.Place.diffCoeff` rows were absorbed into
`AlgebraicCurve/Differential/Generation.lean` (40 → 202 ln), which the new checker
now owns. Measured on the landing: `check_port` **7 ok / 0 mismatch / 0 missing / 1
own** (the bridge, §3.3); the module's `lake build` green; the consumer
`spec/DsHeadConsumer.lean` at **0 errors** with its new `[diffcoeff]` zone;
`#print axioms` of all four new declarations `[propext, Classical.choice,
Quot.sound]`; `dedup.py` no cluster on the module; `unwired_register.py --check`
current; and `frontier.py --ds --ready` **1,206 → 1,203** needed nodes with
**459,653 → 459,023** raw `S_` lines (§8). The pin is
`anthropics/fermats-last-theorem` `aa2d8b3`; the port's mathlib is `v4.34.0`.

**Subject, in one sentence.** `Ω[F⁄K]` is one-dimensional over `F`, so a
uniformiser `t` at a place `v` turns every differential into a unique coefficient
`diffCoeff t ω` with `diffCoeff t ω • Dt = ω`; the cut proves that this coefficient
exists and is the two-sided inverse of `ω ↦ ω • Dt` (`span_D_eq_top_of_transcendental`,
`D_ne_zero_of_transcendental`), and that for `f` in the valuation ring the
coefficient of `Df` is again in the ring — the derivation `d/dt` preserves `𝒪ᵥ`,
i.e. the local different is effective.

## 0. Provenance and the measurement

`frontier.py --ds --ready --sort-by silo` puts these three at the top of the shelf,
all ready (every premise ported):

| node | `S_` | used_by cone/project | premises | frontier |
|---|---:|---|---:|---|
| `Place.ord_diffCoeff_D_nonneg_of_isSeparable` | 576 | 2 / 7 | 5 | ready, `needed 1` |
| `Place.diffCoeff_smul_D_of_ord_eq_one` | 28 | 6 / 15 | 3 | ready, `needed 1` |
| `Place.diffCoeff_smul_D_eq_of_ord_eq_one` | 26 | 4 / 10 | 3 | ready, `needed 1` |

Pin: [wrapper](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean#L9) /
[`S_` 576 ln](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean),
and the two small ones at
[wrapper `…diffCoeff_smul_D_of_ord_eq_one`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean#L7),
[`S_` 28 ln](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean),
[wrapper `…diffCoeff_smul_D_eq_of_ord_eq_one`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean#L7),
[`S_` 26 ln](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean).
The vocabulary is the coefficient block of
[`Definitions/Def_AlgebraicCurve_Differentials.lean#L27-L37`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Differentials.lean#L27-L37).

Measured:

- `twin_scan.py --node …ord_diffCoeff_D_nonneg_of_isSeparable` — `new`, prelude
  5/12: no port declaration carries the statement, but five of the pin file's
  twelve declarations already have public homes.
- `port_advise.py` over the six pin files (20 declarations) — **substitute 4**
  (≈88 lines not to re-prove, all tier 1, all the pin's `Dict` block):
  `toValuationSubringOfRestrictEq`, `coe_toValuationSubringOfRestrictEq`,
  `residueOfCenter`, `surjective_residueOfCenter`, public in
  `AlgebraicCurve/Defs/PlaceDictionary.lean`; **port once 1** (the headline itself,
  written in both the wrapper and its `S_`); **generalise** none.
- all three premises of the two small nodes are ported (§2), so the pair needs no
  prerequisite row.
- `build_ladder.py --edit …Differential/Generation.lean` — dependent cascade **0
  modules / 0 lines**; and with the two `spec-pin:` lines for the headline that
  module already carries, `check_port --force` reports **1 ok, 0 mismatch, 0
  missing**. That is what makes absorbing the module free (§3.1).

The fourth row of the same SU1 landing, `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable`
(20 ln), is **not** a prerequisite of this cut (§6.6).

## 1. The mathematics

Write `diffCoeff t ω` for the pin's coefficient (`Def_…Differentials.lean:27`):
`if h : (∃ g : F, ω = g • D K F t) then h.choose else 0`. The three statements are the three faces
of `Ω` being free of rank one on the set where `Dt ≠ 0`:

| # | statement | pin |
|---|---|---|
| 1 | `v.ord t = 1 → diffCoeff t ω • Dt = ω` | wrapper `…smul_D_of_ord_eq_one:7` |
| 2 | `v.ord t = 1 → diffCoeff t (g • Dt) = g` | wrapper `…smul_D_eq_of_ord_eq_one:7` |
| 3 | `0 ≤ v.ord f → 0 ≤ v.ord (diffCoeff t (D f))`, for `t` a **separating** uniformiser | wrapper `…D_nonneg_of_isSeparable:9` |

(1) is existence of the coordinate and follows from `Dt` spanning `Ω`, which a
transcendental `t` gives once `F/K(t)` is separable; (2) is uniqueness of the
coordinate, i.e. `Dt ≠ 0`. Together they say `diffCoeff t` is the inverse of
multiplication by `Dt` — the coefficient is canonical, so a statement proved for one
uniformiser transfers to another only through the unit relating the two differentials
(§5.2). (3) is the arithmetic content: `d/dt` maps the valuation ring into itself,
equivalently the local different at `v` is effective (Stichtenoth, *Algebraic
Function Fields and Codes*, III.9 and IV; the pin's own reference line for this
node). (3) is what the `ordDiff` computations consume — it is the "different
exponent ≥ 0" half of the differential layer, and the two `diffCoeff` coordinate
rows are what those consumers rewrite with.

## 2. What the port already has

Nothing named `diffCoeff`/`diffCoeff_smul_D`/`diffCoeff_of_not_exists` exists — the
port's coefficient is the `dCoord`-specialised `Place.differentialCoeff`
(`AlgebraicCurve/Defs/CanonicalDivisor.lean:70`, `dCoord = D v.uniformizer` at :57,
`ordDifferential` at :109). Everything else the two small proofs and the headline's
skeleton need is ported:

| lemma | home | role here |
|---|---|---|
| `Place.transcendental_of_ord_ne_zero` | `Place/TranscendentalOfOrdNeZero.lean:71` | `ord t = 1` makes `t` transcendental |
| `Place.isSeparable_adjoin_of_ord_eq_one` | `Place/SeparableUniformiser.lean:129` | the SU1 landing; supplies the separability instance |
| `KaehlerDifferential.span_D_eq_top_of_transcendental` | `Defs/KaehlerTranscendental.lean:81` | `Dt` spans `Ω` — statement 1 |
| `KaehlerDifferential.D_ne_zero_of_transcendental` | `Defs/KaehlerTranscendental.lean:88` | `Dt ≠ 0` — statement 2 |
| `Place.ord_nonneg_of_mem` / `Place.mem_of_ord_nonneg` | `Defs/PushPull.lean:43` / `:60` | `𝒪ᵥ ↔ ord ≥ 0` |
| `AlgebraicCurve.finiteDimensional_adjoin_of_transcendental` | `IsCurveOver/FinitenessTransfer.lean:117` | `F/K(x)` finite ⇒ `F/K(t)` finite |
| `AlgebraicCurve.isCurveOver_of_transcendental` | `IsCurveOver/Transcendental.lean:42` | `IsCurveOver K F` from `t`, finiteness, separability |
| `AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional` | `IsCurveOver/EssFiniteType.lean:41` | `EssFiniteType K F` for the `_of_isCurveOver` wrappers |
| `valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12` | `Canonical/HasCanonicalDivisor.lean:1139` | span-top at **every** place, from `IsCurveOver` + perfect |
| `Place.dCoordGenerates_of_valSubringKaehlerSpanTop` | `Canonical/HasCanonicalDivisor.lean:988` | the per-place instance |
| `Place.exists_mem_D_eq_smul_D_of_isCurveOver` | `Differential/Generation.lean:33` | **`∃ c ∈ 𝒪ᵥ, Df = c • Dπ`** — the pin's engine, already a theorem, in the module this cut absorbs |
| `Place.exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12` | `Canonical/HasCanonicalDivisor.lean:1243` | two uniformisers: `Dt = u • Dπ` with `ord u = 0` |

## 3. The cut: absorb `Differential/Generation.lean`

### 3.1 Settled: the three layers go into the module that already has the fourth

`Differential/Generation.lean` already carries the coefficient's *existence* half:
"at a place `v`, `x ∈ 𝒪ᵥ` gives `Dx = c • Dπ` with `c ∈ 𝒪ᵥ`" is exactly
`∃ c, diffCoeff π (Dx) = c` in the `∃ c ∈ 𝒪ᵥ` spelling, and the pair then says the
coefficient is the inverse of `ω ↦ ω • Dt` and is canonical. One subject, one
module: the file's role widens from "Ω is generated by `dπ` at a place" to "Ω is
generated by `dπ` at a place, and the coefficient in that generator". The name still
describes the content, so there is no rename, and the spec consumer's `[generation]`
zone keeps its import.

The cut needs four imports the module does not have —
`Place/SeparableUniformiser.lean` (which brings `TranscendentalOfOrdNeZero` with it),
`IsCurveOver/FinitenessTransfer.lean`, `IsCurveOver/Transcendental.lean` and
`IsCurveOver/EssFiniteType.lean` — plus what it already imports
(`Canonical/HasCanonicalDivisor` carries steps 5–7 of §5.2, `Defs/KaehlerTranscendental`
statements 1–2, `Defs/PushPull` the `𝒪ᵥ ↔ ord ≥ 0` pair). They are edges *into* the
module, so they cannot cascade: the dependent count stays 0.

Legacy modules are not frozen. The port's rule is the one the checker's own header
states: a legacy module is migrated when it is edited for another reason — give it a
`spec-pin:` wire and delete it from `spec/old_check_stmts.py`'s `PORT_FILES`, so the
new checker owns it. Absorbing this module is therefore two edits to the wiring, and
both are measured on this tree:

- **the handover is clean.** With

  ```
  spec-pin: Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean
  spec-pin: P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean   -- comparable copy
  ```

  in the header, `check_port --force` reports **1 ok, 0 mismatch, 0 missing** for the
  headline the module already carries (only the `Theorems/` wrapper is needed; the
  `S_` line is the comparable copy, as in `Place/SeparableUniformiser.lean`). So the
  legacy registration retires with nothing to reconcile.
- **there is no wave.** `build_ladder.py --edit …Differential/Generation.lean` prices
  the dependent cascade at **0 modules / 0 lines**: nothing in the library imports the
  module, its only importer being the spec consumer `spec/DsHeadConsumer.lean`, which
  is outside the library build (§8). So the cost is one tier-1 module build and one
  manual consumer run.

The `PORT_FILES` edit is the deletion of the line
`"FLTForHuman/AlgebraicCurve/Differential/Generation.lean",` from the `ds-head` block;
that block's comment keeps `Differential/Hurwitz.lean` listed and gains one handover
sentence in the shape of the `Genus/RatFunc.lean` note that follows it ("handed over to
`spec/check_port.py`: its wire checks N ok / 0 mismatch / 0 missing. Do not re-list it
here."). `SOURCES` is left alone — it is shared with the modules still on the legacy
checker, and the new wire reads the pin files directly.

Two alternatives are rejected:

- **A new `Differential/DiffCoeff.lean`**: it would split the existence theorem from
  the coefficient that theorem produces — the coefficient *is* the theorem's witness —
  and buy an import edge and a second role for ~130 lines.
- **`Defs/CanonicalDivisor.lean`** (where `differentialCoeff` lives): that is the
  canonical-divisor definition layer, and its coefficient is the `dCoord` case of
  this one; the general-`t` vocabulary belongs with the generation statement it comes
  from. §3.3 keeps the two connected, so nothing is lost by not homing them together.

The wire after the cut (the definition file first, then the three wrappers and their
comparable copies, appended to the two lines above):

```
spec-pin: Definitions/Def_AlgebraicCurve_Differentials.lean
spec-pin: Theorems/Thm_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_exists_mem_D_eq_smul_D_of_isCurveOver.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_diffCoeff_smul_D_eq_of_ord_eq_one.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_ord_diffCoeff_D_nonneg_of_isSeparable.lean   -- comparable copy
```

The definition wire is one-directional: the pin file's other declarations are homed
from *other* pin files (`regularDifferentials` in `Defs/RegularDifferentials.lean`,
`IsRegularAt` in `Defs/PolarDifferentials.lean`, `pullbackAlong` in
`Differential/PushPull.lean`), or are not taken (§6). The checker only asks that
every *port* declaration be found in the wire.

### 3.2 Settled: the declaration list and the budget

| layer | declaration | pin source | est. |
|---|---|---|---:|
| L0 vocabulary | `Place.diffCoeff` (def, body verbatim) | `Def_…Differentials.lean:27` | 10 |
| L0 | `Place.diffCoeff_smul_D` | `:30` | 6 |
| L0 | `Place.diffCoeff_of_not_exists` | `:35` | 4 |
| L0 bridge | `Place.diffCoeff_uniformizer_eq_differentialCoeff` | — (port glue, §3.3) | 8 |
| L1 | `Place.diffCoeff_smul_D_of_ord_eq_one` | `S_` 28 ln | 12 |
| L1 | `Place.diffCoeff_smul_D_eq_of_ord_eq_one` | `S_` 26 ln | 10 |
| L2 | `Place.ord_diffCoeff_D_nonneg_of_isSeparable` | `S_` 576 ln | 45 |
| — | header role paragraph + the new `spec-pin:` lines | | 20 |
| (pre-existing) | `exists_mem_D_eq_smul_D_of_isCurveOver` | its own wrapper | 0 |

**162 added lines** to a 40-line module (202 ln landed), of which ≈67 are the three
headlines and the rest the header's role/provenance prose and the seven `spec-pin:`
lines — against 630 raw `S_` lines. The module already has `noncomputable section` and
`set_option autoImplicit false`; `Classical.choose` in the definition (as in the pin)
keeps the former necessary.

The header's role paragraph is the only prose that has to be rewritten (its `s12`
paragraph, which explains why the module imports `HasCanonicalDivisor` instead of
re-proving the prelude, stays): Ω is one-dimensional over `F` at a place, so `dπ`
generates it (existence), `diffCoeff π` is the coordinate in that generator
(uniqueness), and for a separating uniformiser the coordinate of an integral element
is integral. The provenance list gains the three `S_` files and their wrappers; the
module's name still says the first half of that sentence.

### 3.3 Settled: keep one coefficient, with a public bridge

The port would otherwise carry two coefficients: the pin's `diffCoeff t` (arbitrary
uniformiser) and the port's `differentialCoeff` (the chosen `dCoord`). They are
related by the pair plus `dCoord = D v.uniformizer` (`rfl`), so the module states

```
theorem Place.diffCoeff_uniformizer_eq_differentialCoeff [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω : Ω[F⁄K]) : v.diffCoeff v.uniformizer ω = v.differentialCoeff ω
```

(`diffCoeff_smul_D` gives one multiple of `dCoord`, `differentialCoeff_smul_dCoord`
the other, `dCoord_ne_zero` cancels). It is port glue, not in the pin: it goes into
`spec/decl_markers.tsv` as `own: canonical-coefficient bridge`, and it is what keeps
the rest of the tree on *one* coefficient — consumers state the pin's theorems with
`diffCoeff` (the checker is a statement diff, so they must), and use this lemma once
at the boundary. Without it the alternative is a second copy of the coefficient API
in every consumer, which is the duplicate the port's `dedup.py` would flag.

### 3.4 Dispatch

The cut is ~115 added lines: below one dispatch. By the playbook's division of labour
the manager owns the definition layer and every wiring question, so the manager: adds
the two `spec-pin:` lines for the existing headline and the `Definitions/` line, runs
the checker to confirm the handover (§3.1), deletes the module from `PORT_FILES`,
writes L0 and the bridge. One dispatch then writes L1–L2 against it. One tier-1
module build at the end; no wave (measured 0 dependents), and the consumer run of
§8 once.

## 4. The pair, in the port's terms

Both proofs are the pin's `solution`, re-pointed at the port's lemmas.

**Statement 1** (`diffCoeff_smul_D_of_ord_eq_one`). `t` transcendental
(`transcendental_of_ord_ne_zero`, from `ord t = 1`); the separability instance comes
from `isSeparable_adjoin_of_ord_eq_one x v ht`, exactly as in the pin. Then
`Dt` spans `Ω` by `span_D_eq_top_of_transcendental`, so `ω ∈ span {Dt}`, and
`Submodule.mem_span_singleton` gives `∃ g, ω = g • Dt`; `diffCoeff_smul_D` closes it.
The pin's private `exists_eq_smul_D` helper disappears — it is this proof inline.

**Statement 2** (`diffCoeff_smul_D_eq_of_ord_eq_one`). `Dt ≠ 0` by
`D_ne_zero_of_transcendental`, then cancel it against
`diffCoeff t (g • Dt) • Dt = g • Dt` (`diffCoeff_smul_D` at `⟨g, rfl⟩`) with
`smul_eq_zero` and `sub_eq_zero` — the same cancellation `Place.differentialCoeff_unique`
uses, and the reason no helper is needed (the pin's `P2M.Util` supplies a
`smul_left_injective` that mathlib v4.34 does not have in that shape). The pin's
private `D_ne_zero` helper likewise disappears into the main proof.

Both keep the pin's **weaker** hypothesis `[Algebra.IsAlgebraic (adjoin K {x}) F]`
(not `FiniteDimensional`), because the checker diffs binders (§7, R1).

## 5. The headline: proof plan

### 5.1 Replace the pin's engine, do not port it

`S_:263-514` is a private `engine` (≈250 lines) that builds, by hand and in the
`RatFunc K` tower, the conclusion "`Df = g • Dt` with `g` integral"; `S_:163-261` is
a `Dict` section supplying the residue/valuation dictionary it needs. In the port
both are already theorems:

- the four declarations the proof states are public in `Defs/PlaceDictionary.lean`
  (§0);
- the engine's conclusion is `Place.exists_mem_D_eq_smul_D_of_isCurveOver`
  (`≈∃ c ∈ 𝒪ᵥ, Df = c • Dπ`), and the `RatFunc` transport that puts the pin's
  hypotheses into that theorem's shape is `finiteDimensional_adjoin_of_transcendental`
  plus `isCurveOver_of_transcendental`.

So the proof is a wrapper: get `IsCurveOver`, get the per-place instance, apply the
two port theorems, convert `Dπ` to `Dt` by the unit between them, read off the
coefficient with statement 2, and read the sign off `𝒪ᵥ`.

### 5.2 The steps

Inputs: `[PerfectField K]`, `x` with `[FiniteDimensional K⟮x⟯ F]`, `v : Place K F`,
`ht : v.ord t = 1`, `[Algebra.IsSeparable K⟮t⟯ F]`, `hf : 0 ≤ v.ord f`.

| step | fact | from |
|---|---|---|
| 1 | `Transcendental K t` | `transcendental_of_ord_ne_zero v (by rw [ht]; exact one_ne_zero)` |
| 2 | `FiniteDimensional K⟮t⟯ F` | `finiteDimensional_adjoin_of_transcendental x htr` |
| 3 | `IsCurveOver K F` | `isCurveOver_of_transcendental htr hfd ‹IsSeparable K⟮t⟯ F›` |
| 4 | `EssFiniteType K F` | `essFiniteType_of_transcendental_of_finiteDimensional htr hfd` |
| 5 | `[v.DCoordGenerates]` | `dCoordGenerates_of_valSubringKaehlerSpanTop (valSubringKaehlerSpanTop_of_isCurveOver_of_perfectField_s12) v` |
| 6 | `∃ c ∈ 𝒪ᵥ, Df = c • Dπ` (`π := v.uniformizer`) | `exists_mem_D_eq_smul_D_of_isCurveOver v v.ord_uniformizer (v.mem_vs_of_ord_nonneg hf)` |
| 7 | `∃ u, v.ord u = 0 ∧ Dt = u • Dπ` | `exists_ord_eq_zero_D_eq_smul_D_of_isCurveOver_s12 v v.uniformizer t v.ord_uniformizer ht` |
| 8 | `Df = (c / u) • Dt` | 6, 7 and `mul_smul` |
| 9 | `diffCoeff t (Df) = c / u` | statement 2 at `c / u` |
| 10 | `0 ≤ v.ord (c / u)` | `c ∈ 𝒪ᵥ` ⇒ `ord c ≥ 0` (`ord_nonneg_of_mem`), `ord u = 0` ⇒ `ord (c/u) = ord c` |

Step 6 uses `Place.mem_vs_of_ord_nonneg` (`Canonical/WeilDifferential.lean:95`), the
general form of `mem_of_ord_nonneg` that does not ask `f ≠ 0`; the `f = 0` corner then
needs no case split at all — `0 ∈ 𝒪ᵥ`, `c = 0`, and the `c = 0` branch of step 10 gives
`0 ≤ v.ord 0 = 0`. (Landed that way; the pin also treats `f = 0` by the same
`ord_zero` convention.)

### 5.3 What is left of the 576 lines

630 raw `S_` lines across the three nodes; ≈67 written, of which ≈45 is this proof.
The saving is §5.1 plus the fact that the two small nodes were already 5-line proofs
in the pin — their 28/26 lines are the `attribute [-instance]`/`[-simp]` preludes and
the `p2m_*` scaffolding, which the port does not transcribe.

## 6. Deliberately not transcribed

1. **The `engine` and the `Dict` section** (`S_:163-514`): both are already in the
   port (§5.1). Transcribing them would re-prove `Defs/PlaceDictionary.lean` and
   `exists_mem_D_eq_smul_D_of_isCurveOver` under a private name.
2. **The `RatFunc` tower setup** (`S_:515-560`): subsumed by steps 2–3.
3. **`uniformizer_alt`, `ord_uniformizer_alt`, `ordDiff`, `ordDiff_def`**
   (`Def_…Differentials.lean:18-42`): no ready row states them, and the port's
   `Place.ordDifferential` (`Defs/CanonicalDivisor.lean:109`) is the canonical home;
   homing the pin's would give the tree two `ordDiff`s differing only in the choice
   of uniformiser. Take them when a pin statement names them — that statement will
   then be the reason, not this one.
4. **`IsRegularDiff`, `isRegularDiff_iff`, `regularDiffs`,
   `mem_regularDiffs_of_isRegularDiff`, `regularDiffs_eq_span`**
   (`Def_…Differentials.lean:45-66`): the port's `IsRegularAt` / `regularDifferentials`
   are homed from the pin's *Polar/Regular-differentials* definition files, so these
   are a second spelling of definitions already at home; and `regularDiffs` in
   particular is `Submodule.span` of a predicate — nothing in this cut needs it.
5. **`pullbackDiff`, `pullbackDiff_D`** (`:70-85`): the port's
   `Differential/PushPull.lean` (`pullbackAlong`, wired to
   `Def_AlgebraicCurve_DifferentialPushPull`).
6. **`AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable`** (20 ln, still on
   the shelf): not needed here. `isCurveOver_of_transcendental` already takes `t`
   itself as the transcendental generator, and statement 3's hypotheses give exactly
   `Transcendental K t` + `FiniteDimensional K⟮t⟯ F` + `IsSeparable K⟮t⟯ F`. Landing
   that row first would not shorten this cut.

## 7. Risks and statement-fidelity notes

- **R1 — binders differ between the three nodes, and that is the pin's.** The two
  small ones assume `[Algebra.IsAlgebraic K⟮x⟯ F]`, the headline
  `[FiniteDimensional K⟮x⟯ F]`. The checker is a statement diff: transcribe both as
  they are, do not "unify" them downward or upward.
- **R2 — one coefficient, two names.** Any pin statement that says `diffCoeff` must
  be stated with `diffCoeff`, and the port's internal lemmas with
  `differentialCoeff`; the bridge (§3.3) is the only place they meet. Stating a pin
  node with the port's coefficient is a hash mismatch, not a stylistic choice.
- **R3 — `diffCoeff` is a `Classical.choose`.** `noncomputable section`; and the
  degenerate branch (`diffCoeff t ω = 0` when no coordinate exists) is never taken in
  the three proofs — statement 1 always produces the witness — but
  `diffCoeff_of_not_exists` stays because it is part of the definition's API and a
  consumer may need it.
- **R4 — `mem_of_ord_nonneg` wants `f ≠ 0`; use `mem_vs_of_ord_nonneg` instead** (its
  general form, `Canonical/WeilDifferential.lean:95`), so the `f = 0` corner stays inside
  the theorem: `c = 0`, `diffCoeff t 0 = 0 / u = 0`, `v.ord 0 = 0` (`Defs/Place.lean:140`).
  Keep the `c = 0` branch anyway — `ord_mul` wants `c ≠ 0`.
- **R5 — the instance walls.** Steps 3–5 build instances locally in the
  `isCurveOver_of_transcendental` / `_s12` style (`letI`/`haveI`, literal per the
  port's SET-1 §3 convention). Do not weaken them into a `variable` block; the
  towers are not `IsScalarTower`-compatible by default.
- **R6 — `0 ≤ v.ord (c/u)` when `c = 0`.** `c = 0` makes `diffCoeff t (Df) = 0` and
  the conclusion `0 ≤ 0`; keep that as the first branch rather than letting
  `ord_mul`/`ord_div` demand `c ≠ 0`.
- **R7 — naming.** The pin's `diffCoeff` keeps its name (it is the statement);
  `def` bodies are transcribed verbatim, including the `if h : ∃ g, …` shape, so the
  definition's own hash is the pin's.

## 8. Verification

The module edits in place, so the ladder is the normal one (`build_ladder.py --edit`
prices the cascade at 0 modules, §3.1):

```
cd lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/AlgebraicCurve/Differential/Generation.lean         # tier 0 edit loop
flock .lake/flt_build.lock timeout 300 lake build \
    FLTForHuman.AlgebraicCurve.Differential.Generation              # tier 1, once
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Differential/Generation.lean
#   [ok] 7 ok, 0 mismatch, 0 missing, 1 own
#   7 diffed = the pre-existing headline + the 3 vocabulary + the 2 coordinate rows
#   + the integrality headline; the `own` is the bridge (§3.3), recorded in
#   spec/decl_markers.tsv
python3 spec/unwired_register.py --check                            # register is current
```

and, because the module was handed over, the legacy side must agree that it has left:

```
grep -n "Differential/Generation" spec/old_check_stmts.py            # expect: the comment only
```

The consumer is outside the library build and is run by hand; the error count is the
metric. Landed at 0, and warning-free:

```
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DsHeadConsumer.lean 2>&1 | grep -c error
#   0
```

The `[diffcoeff]` zone was added for exactly this: the three headlines applied with
their own binder walls (which are the function-field hypotheses, not `IsCurveOver` —
the two small rows ask `Algebra.IsAlgebraic` where the integrality row asks
`FiniteDimensional`), plus the concrete half at `placeInfty K` — the place satisfies
`DCoordGenerates` by `dCoordGenerates_of_isCurveOver`, and with it the general
`diffCoeff` is the canonical `differentialCoeff`. That zone is the "update the
consumers" half of the handover: it makes the new API exercised, not merely checked.

The dedup scan, from `tools/deps`:

```
cd tools/deps
python3 dedup.py --module '*Generation*'
#   expect: no cluster against `differentialCoeff` on the `diffCoeff` declarations —
#   the general coefficient carries the extra argument `t`, so the hypothesis lists
#   differ at both the name and the shape tier
```

Acceptance: the three headlines green with no warning; `#print axioms` on each
`[propext, Classical.choice, Quot.sound]`; no `sorry`; the definitions' bodies
verbatim; `check_port` and the consumer as above; `old_check_stmts.py` free of the
module.

Then the frontier re-read, which is the step-6 record for this cut:

```
cd tools/deps
python3 frontier.py --ds --ready --nexus --fanin-min 5
```

Measured: `needed 1,206 → 1,203` nodes and `459,653 → 459,023` raw `S_` lines
(exactly minus 576 + 28 + 26), the three rows gone from the shelf, and — one hop up —
`Place.ord_diffCoeff_D_nonneg_of_perfectField` (17 ln, `used_by` 7 cone / 20 project)
at its head, the first consumer of the headline. `F` grew 1,176 → 1,179 and the
`AlgebraicCurve.` unported demand fell 189 → 186.

## 9. What this unblocks

- The headline's seven consumers (`explore.py`), of which the ready-adjacent ones are
  `Place.ord_diffCoeff_D_nonneg_of_perfectField`,
  `Place.ordDiff_D_eq_ord_sub_algebraMap_sub_one_of_cast_natAbs_ne_zero`,
  `Place.ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero`,
  `Place.exists_finset_forall_ord_sub_algebraMap_eq_one_of_ord_pos` and the two
  `ModularCurve.ordDifferential_D_jGeomGen…` rows — the genus rows of
  `ModularCurve/Frobenius/`. Re-read the shelf after landing rather than assuming
  readiness: several of them carry other unported premises.
- `Differential/Hurwitz.lean`'s `LocalUnitDerivativeRegular` (:770) is the port's own
  predicate — "the derivative of a unit is regular" — and is currently **assumed**
  where the tame different exponent is derived. This cut supplies it in the
  perfect/`IsCurveOver` world (`f` with `0 ≤ ord f` covers units of `𝒪ᵥ`, and the
  bridge plus step 7 converts to the `dCoord`-based coefficient), so a later round
  can either discharge the hypothesis at its users or record that it is a deliberate
  port-side strengthening. Not part of this cut: no pin node states it, so it is a
  port decision, and it belongs with the consumer that wants it.
