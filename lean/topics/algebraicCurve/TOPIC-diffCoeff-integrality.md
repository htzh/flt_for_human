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

*(2026-10-25: the cancellation above turned out to be unnecessary — `v.dCoord` is
`D K F v.uniformizer` by definition, so the two spellings are the same term and the
statement is `rfl`; the proof is now that one line. See §10, which also settles why
the two homes are not merged.)*

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
#   (this cut's count: §10 adds one row, so the same command now reads 8 ok)
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

## 10. Sequel (2026-10-25): the perfect-field wrapper, and why it stays in this module

The row §8/§9 predicted as the next shelf head,
`Place.ord_diffCoeff_D_nonneg_of_perfectField` (17 ln, `used_by` 7 cone / 20
project), is landed in the **same** module (then called `Generation.lean`, renamed to
`Coefficient.lean` at the end of this section) as its last declaration — directly
after the `ord_diffCoeff_D_nonneg_of_isSeparable` headline it instantiates, inside
the same `/-! ### The coefficient of an integral element is integral -/` section:

```lean
theorem AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_perfectField ... := by
  haveI : Algebra.IsAlgebraic K⟮x⟯ F := Algebra.IsAlgebraic.of_finite _ _
  haveI := AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one x v ht
  exact AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable x v ht hf
```

**The placement is forced by the import DAG, not chosen by taste.** The pin's
`S_` is a corollary of two statements, `Place.isSeparable_adjoin_of_ord_eq_one`
(`Place/SeparableUniformiser.lean:129`) and the headline (this module) — and this
module imports the former. So the five homes a reader might look in are all barred:

| candidate home | why not |
|---|---|
| `Place/SeparableUniformiser.lean` (owns the separability lemma) | imports `diffCoeff`'s module ⇒ cycle |
| `IsCurveOver/{Transcendental,FinitenessTransfer,EssFiniteType}.lean` | imported *by* this module ⇒ cycle |
| `IsCurveOver/PerfectField.lean` | reached from here via `IsCurveOver/Transcendental` ⇒ cycle |
| `Differential/Hurwitz.lean` (`ordDiff`, the different) | a consumer of the row, not its subject; would invert the edge |
| new `Differential/DiffCoeffPerfectField.lean` | 17 lines, and it would split a corollary from the theorem it is proved from (§3.1's "module is a role") |

What is left is the module that states the coefficient, which is also the one home
that needs no new import: the port's `isSeparable_adjoin_of_ord_eq_one` is already
in scope, so the row is 17 lines of statement and proof against 2 `spec-pin:`
lines (`Theorems/` + the `S_` comparable copy) and ≈8 lines of header prose.
Precedent for two heads in one module: `IsCurveOver/Transcendental.lean:42` / `:82`
(the same general-plus-`_of_perfectField` pair) and
`Place/SeparableUniformiser.lean:129` / `:138` (twin heads, one body, two
hypothesis sets).

Measured on the landing (`aa2d8b3`): tier-0 `lake env lean` clean; tier-1 module
build green with no warning on this module; `check_port --force` **8 ok / 0
mismatch / 0 missing / 1 own** (nothing added to `spec/decl_markers.tsv` — the name
and statement are the pin's); `unwired_register.py --check` current; the consumer
`spec/DsHeadConsumer.lean` at **0 errors / 0 warnings** with a fourth `[diffcoeff]`
example — the same application as the `_of_isSeparable` one with the
`[Algebra.IsSeparable K⟮t⟯ F]` line dropped, which is exactly what the wrapper buys
a consumer; `#print axioms` `[propext, Classical.choice, Quot.sound]`; and
`frontier.py --ds` **1,203 → 1,202** needed nodes with **459,023 → 459,006** raw
`S_` lines (`F` 1,179 → 1,180, `AlgebraicCurve.` unported demand 186 → 185).

**The dedup caveat, recorded so it is not "fixed" later.** `dedup.py --module
'*Coefficient*'` now reports one intra-module cluster:
`ord_diffCoeff_D_nonneg_of_isSeparable` (41 L) with its perfect-field twin (8 L),
8 "removable" lines. That is the playbook's own documented false positive
(§"Real mathematics is written once": *`dedup.py --tier shape` ignores instance
arguments*, so a pair differing only in the instance hypothesis its section supplies
reports one cluster and no difference). Here the 8 lines **are** the instance
plumbing, and the twin cannot be deleted: it is a distinct pin statement that the
checker diffs binder for binder (§7 R1), and without it each of the row's 7 cone
consumers repeats the two `haveI` lines. Verify at the call sites and keep both.

**What is still not ready.** The nearest consumer,
`Place.ord_sub_one_le_ordDiff_D_of_perfectField`, has all of its premises ported
except `Place.exists_ord_eq_one` (the port has only the `dCoord`-shaped
`Place.exists_ord_eq_one_and_dCoord_eq`, `Defs/RegularDifferentials.lean:26`), so
that row — and the `ordDiff`/genus rows above it — is the next cut's floor, not this
one's. It belongs with `ordDiff`, i.e. `Differential/Hurwitz.lean` or a successor
`ordDiff` module, and not here: this module owns the *coefficient*, that one the
*order of the differential*.

**Post-cut rename (2026-10-25).** The module is now
`AlgebraicCurve/Differential/Coefficient.lean` (module
`FLTForHuman.AlgebraicCurve.Differential.Coefficient`), renamed from
`Differential/Generation.lean`. `Generation` named it exactly when it was the
40-line / 1-declaration wrapper of `exists_mem_D_eq_smul_D_of_isCurveOver`
(2026-10-07, ds-head): after this cut that declaration is 9 of 229 lines and has no
proof of its own — a one-line call to
`exists_mem_D_eq_smul_D_of_isCurveOver_s12`
(`Canonical/HasCanonicalDivisor.lean:1251`) — while the other 8 declarations are the
`diffCoeff` layer. No move: `Differential/` is the theory directory and no second
theory has appeared, so no `Defs/` split or subdirectory is triggered.

The declarations are unchanged and the wire moves with the file, so `check_port`
reads the same **8 ok / 0 mismatch / 0 missing / 1 own** at the new path. Updated in
the same change: the module header (its opening now says this is the *general*
coefficient and points at the `dCoord` case `differentialCoeff` in
`Defs/CanonicalDivisor.lean`, so the two do not read as duplicates), the consumer's
import and its `HOW TO READ IT` line (`spec/DsHeadConsumer.lean`), the bridge's path
column in `spec/decl_markers.tsv`, and the handover comment in
`spec/old_check_stmts.py`. No `PORT_FILES` edit (the module is handed over) and no
lakefile edit (globs `.submodules`); nothing in the library imports it — the only
importer is the spec consumer, outside the library build — so the cascade is 0. The
declarations were not touched, which is the m13 precedent (`Capstone.lean` →
`HeckeCommuteBar.lean`, `topics/mc-retrospective.md:55`).

Ladder at the new path:

```
cd lean
lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/AlgebraicCurve/Differential/Coefficient.lean            # tier 0
flock .lake/flt_build.lock lake build \
    FLTForHuman.AlgebraicCurve.Differential.Coefficient                 # tier 1, once
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Differential/Coefficient.lean
#   8 ok, 0 mismatch, 0 missing, 1 own
```

Mentions of `Differential/Generation.lean` in §3, §8 and in
`topics/deligneSerre/ds-head-recon.md`, `topics/riemannRoch/WORKORDER-ds-head.md`,
`topics/PORTING-DeligneSerre.md` and `logs/riemann-roch-friction.md` are the
pre-rename ones and are left as written: they record what was dispatched and measured
under the old name. This paragraph is the mapping.

**Not a merge with `Defs/CanonicalDivisor.lean` (asked 2026-10-25).** That module
owns `v.uniformizer` (:39), `v.dCoord` (:57), `DCoordGenerates` (:59) and
`Place.differentialCoeff` (:70); the coefficient in this module is the general one.
Folding the two together is barred, not merely expensive:

- **The theorems cannot move upstream.** The three groups here need
  `exists_mem_D_eq_smul_D_of_isCurveOver_s12`
  (`Canonical/HasCanonicalDivisor.lean:1251`), `IsCurveOver` and
  `Algebra.IsSeparable`, and `HasCanonicalDivisor` imports the Defs module — so a
  theorem of this module placed there is a cycle. Only the ~14 lines of vocabulary
  (`diffCoeff`, `diffCoeff_smul_D`, `diffCoeff_of_not_exists`) could move, and §3.1
  keeps them with the generation statement they come from; the
  `Def_AlgebraicCurve_Differentials.lean` wire would also have to split across two
  modules.
- **The price is asymmetric.** `build_ladder.py --edit …Defs/CanonicalDivisor.lean`
  prices an edit there at **104 modules / 68,626 lines, ≈825 s** of re-elaboration,
  and the module is still on the legacy checker (`PORT_FILES`), so an edit owes a
  handover as well. This module has **0** dependents (its only importer is the spec
  consumer).
- **There is no duplication to remove.** The two spellings are *the same term*:
  `v.dCoord` is `D K F v.uniformizer` by definition, so
  `diffCoeff v.uniformizer ω = v.differentialCoeff ω` holds by `rfl`, and the bridge
  is now proved that way — the file states the identity structurally instead of
  deriving it from `differentialCoeff_unique`. `dedup.py` over both homes reports no
  cluster between them (its only cross-module hit there is the unrelated
  `uniformizerSubring'` / `''` / `'''` triple). The port's *working* coefficient is
  `differentialCoeff` (717 mentions: `LocalResidue/Calculus`, `P1/TraceEngine`,
  `Differential/Hurwitz`, …); the general `diffCoeff` is the pin's spelling for
  statement diffing (24 mentions: this module and the consumer).

**Deferred to whoever next edits `Defs/CanonicalDivisor.lean`** — neither is worth a
wave of its own: (a) the `uniformizerSubring'` / `''` / `'''` triple is a real 6-line
duplicate (`dedup.py`, `body` tier, cross-module) to fold into one — **done in §11,
which also handed that module to the new checker**; (b) with the general definition
upstreamed, `differentialCoeff` could be *defined* as `diffCoeff v.uniformizer`, which
keeps this module's bridge at `rfl` and leaves the `if h : …` shape in a single place.
Item (b) rides on an edit that has to happen for another reason, which is the port's
rule for migrating a legacy module.

## 11. The definition layer: dedup and handover (2026-10-25)

`Defs/CanonicalDivisor.lean` was deduped and handed to the new checker in one change,
because a later edit would only be dearer: `build_ladder.py --edit` prices an edit there
at **104 modules / 68,626 lines, ≈825 s** of re-elaboration, and the module still sat on
the frozen checker.

**The dedup.** `dedup.py --module '*CanonicalDivisor*'` reported one cross-module `body`
cluster: `Place.uniformizerSubring'` (the definition layer, :46) against
`Place.uniformizerSubring''` (`Canonical/HasCanonicalDivisor.lean:96`) and
`Place.uniformizerSubring'''` (:188) — three copies of the same `Classical.choose`. The
docstring already named the definition layer as the home, so the two engine copies are
gone and all 12 uses point at `v.uniformizerSubring'`. `irreducible_uniformizerSubring'''`
(a `choose_spec` application, one use) went with them, inlined into
`maximalIdeal_eq_span_uniformizer`; the same fact is stated as
`LocalResidue/Instance.lean:105` and is not worth a second public name. Both deleted names
were file-local (grep over `FLTForHuman`, `spec/`, `Reserve/`), so no importer's *source*
moves, and their bodies were `rfl`-equal to the home, so every dependent proof stays valid
without rewriting.

`uniformizerSubring'` keeps its prime: the pin's name `uniformizerSubring` is spelled at
that name in `LocalResidue/Instance.lean`, which aliases this definition for the pin
statements that use it. Renaming the home to the pin name would delete that alias but
would touch 26 sites in three files and 104 dependents — a separate decision, not a
dedup.

What dedup still reports on these modules is two *artifacts*, recorded so that nobody
deletes real theorems:

- `⊢ letI`, 12 copies, 140 "removable": the shape key truncates at the `letI` that the
  s12 engine's `letI := v.polynomialAlgebra` opens, so twelve **different** statements
  (`polynomialAlgebra_algebraMap_X`, `subsingleton_polynomialKaehler_…`, …) hash alike.
  The key is literally `"⊢ letI"` in `build/dedup.json`.
- `dCoordGenerates_of_valSubringKaehlerFinite_of_isSeparable` against
  `…_of_perfectField`: the instance-discharge pair of §10.

**The handover.** The header wires
`Definitions/Def_ModularCurve_CanonicalDivisor.lean`,
`Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean` and
`Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean` (the re-export that states
`uniformizer` publicly; the first file keeps it `private`), and the module is out of
`PORT_FILES`. `check_port --force` reads **21 ok / 0 mismatch / 0 missing / 1 own**. The
`own` is `Place.uniformizerSubring'`: the pin's own copy is
`Definitions/Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean:199` (identical
body), and since `LocalResidue/Instance.lean` already diffs it against that file at the
pin name, this module records an `own:` row in `spec/decl_markers.tsv` instead of growing
a 2,173-line pin file into its wire. The header prose now states the subject rather than
the moves that produced it (`Set D`, "the refactor round", "phase-3.1" are gone).

**Verified, and what is stale.** Tier-0 on both edited modules; tier-1
`lake build FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor` (2,773 jobs, 15 s,
no warning on either module); consumer `spec/DsHeadConsumer.lean` **0 errors / 0 warnings**;
`P1/Differential.lean`, the module that reads `v.polynomialAlgebra`, re-elaborated green as
a spot-check of the dependents. No tree build was run, so the 104 dependents' oleans are
stale until the next wave — nothing in them references a name this change deleted.

## 12. The engine module, brought up to date (2026-10-25)

`Canonical/HasCanonicalDivisor.lean` (1,566 ln, 111 checked declarations, 104 dependent
modules) now sits on the new checker: **102 ok / 0 mismatch / 0 missing / 9 own**, wired
to `Theorems/Thm_…hasCanonicalDivisor_of_isCurveOver.lean` with its `S_` comparable copy
and to `Theorems/Thm_…dCoordGenerates_of_isCurveOver.lean` likewise. It is out of
`PORT_FILES`.

**The hosting fix — which is where the duplication came from.** The pin states
`Place.uniformizerSubring` (the uniformizer as an element of the valuation subring) in
`Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean:199`, a *definition* file. The
port had homed that name in `LocalResidue/Instance.lean`, downstream of the cotangent and
residue engines that need it, so those engines could not spell it and this module carried
its own copies — the `uniformizerSubring''`/`'''` pair deduped in §11. After §11 pointed
them at the definition layer's primed copy, the checker reported **six mismatches**: the
measurement that the copies were not stylistic, because the pin's *statements* name the
pin's definition. Now:

- `Defs/CanonicalDivisor.lean` declares `Place.uniformizerSubring` at the pin's name and
  wires the V2 file: **22 ok / 0 mismatch / 0 missing / 0 own** (the `own:` row of §11 is
  gone — the definition is diffed, not excepted);
- `LocalResidue/Instance.lean`'s one-line alias is deleted and the module reads the
  definition layer: **120 ok / 0 own**;
- this module has one name to spell, in all 21 places.

**What the 9 `own:` rows are.** Six engine statements, `kaehlerMap_subring_D_uniformizer`
and the two `…Subring_s12` lemmas are the pin's text with its *private* synonym replaced by
the one public definition; they carry one shared reason in `spec/decl_markers.tsv`.
Restoring the synonyms as aliases would buy 105 ok / 6 own here, at the price of the
duplication and prime-tokens this pass exists to remove — and of leaving the definition
itself an `own:` row under a primed name. The one-definition side is taken.

**Also cleaned, no semantics touched.** 48 redundant `_root_.AlgebraicCurve.Place.`
prefixes (they made the checker read `AlgebraicCurve.Place._root_.AlgebraicCurve.Place.X`,
so the name tiers could not match); six private helpers that were declared inside
mathlib's `Transcendental` and `Algebra.FiniteType` namespaces now live in this module's
(`isPrincipalIdealRing_adjoin`, `isDedekindDomain_adjoin`, `isIntegrallyClosed_adjoin`,
`isNoetherianRing_adjoin`, `finiteType_adjoin_singleton`, `transcendental_inv`).

Measured: no warning for this module (tier-1 build 2,773 jobs / 15 s); `move_dead.py
--select dead` reports **0 declarations, 0 lines** (nothing to shelf); `dedup.py` over the
three touched modules reports **0 cross-module** clusters and the two intra-module
artifacts of §11 (`⊢ letI`, 12 copies; the instance-discharge pair); consumer
`spec/DsHeadConsumer.lean` **0 errors / 0 warnings**; `unwired_register.py --check`
current.

**Not done, and why it is a set of its own.**

- **26 public `_s12` names remain.** They are the pin's own names, and two of them
  (`hasCanonicalDivisor_of_isCurveOver_s12`, `exists_mem_D_eq_smul_D_of_isCurveOver_s12`)
  exist because the pin sets its `S_` copy beside the `Theorems/` wrapper: the base names
  are taken by the wrapper, homed in this module and in `Differential/Coefficient.lean`.
  Rectifying the suffix therefore means collapsing each S_-copy/wrapper pair into one
  declaration at the wrapper's name — a cross-module move with proof relocation, not a
  rename — and doing it for 24 names while keeping 2 would be the worse half-measure.
- **The subject split.** The module covers the `ValSubring*` model chain (seven Prop
  predicates and their engines, ≈55 declarations), the centre-ideal / Dedekind-localization
  machinery, the `RatFunc`-chart transport, and the `dCoordGenerates`/`hasCanonicalDivisor`
  assembly. The natural cut is after `valSubringDedekindModel_of_dedekindFractionModel`
  (:665): the model chain becomes `Canonical/ValSubringKaehler.lean`, this module imports it
  and keeps the curve/chart chain, so the 104 dependents need no import edit. It is a wave
  of its own (new module + its wire + the moved `own:` rows), and it changes no statement.

## 13. The subject split (2026-10-25)

`Canonical/HasCanonicalDivisor.lean` was four subjects under one name — 1,566 lines that
the pin keeps in a single `S_` file because that file is a proof-search artifact. Split by
the mathematics, with each module's header stating its subject and what it assumes from the
earlier ones (`Differential/Generation.lean`-style reading order is dependency order):

| module | lines | subject | checker |
|---|---:|---|---|
| `Canonical/ValSubringKaehler.lean` | 670 | `D π` spans `Ω[𝒪ᵥ⁄K]`: the model-predicate chain (`ValSubringPolynomialFormallyUnramified`, `…KaehlerFinite`, `…EssFiniteType`, `…FiniteTypeModel`, `…DedekindModel`, `…DedekindFractionModel`), the centre-ideal localisation it runs on, and the generic `ValuationSubring.idealOfLE` facts | 48 ok / 7 own |
| `Canonical/AffineChart.lean` | 360 | affine charts of a place (`IsAffineChart`, `ValSubringTwoAffineCharts`), `K⟮t⟯`'s Dedekind/Noetherian/integrally-closed/principal-ideal-ring properties, the reciprocal transport `K⟮t⁻¹⟯ = K⟮t⟯`, and `HasSeparatingTranscendental` | 37 ok / 0 own |
| `Canonical/DCoordGenerates.lean` | 197 | every place of a curve over a perfect field has a generating `dCoord`, one step per model predicate, ending in the pin headline `dCoordGenerates_of_isCurveOver` (its own `Theorems/` file) | 10 ok / 0 own |
| `Canonical/HasCanonicalDivisor.lean` | 478 | the canonical divisor: the span hypothesis from `IsCurveOver`, the coordinate against two uniformisers, finite support of the negative orders, and the headline `hasCanonicalDivisor_of_isCurveOver` (its own `Theorems/` file) | 13 ok / 2 own |

**Dependency order is the reading order**: `HasCanonicalDivisor` imports `DCoordGenerates`
imports `AffineChart` imports `ValSubringKaehler`. Every one of the 104 dependents imports
`HasCanonicalDivisor`, so it still sees every name through that single import — **no
dependent's source changed**, and the four `spec-pin:` wires are the pin files each module
homes:

```
ValSubringKaehler   spec-pin: P2M/Sol/S_…hasCanonicalDivisor_of_isCurveOver.lean
AffineChart         spec-pin: P2M/Sol/S_…hasCanonicalDivisor_of_isCurveOver.lean
DCoordGenerates     spec-pin: Theorems/Thm_…dCoordGenerates_of_isCurveOver.lean
                    spec-pin: P2M/Sol/S_…dCoordGenerates_of_isCurveOver.lean
                    spec-pin: P2M/Sol/S_…hasCanonicalDivisor_of_isCurveOver.lean
HasCanonicalDivisor spec-pin: Theorems/Thm_…hasCanonicalDivisor_of_isCurveOver.lean
                    spec-pin: P2M/Sol/S_…hasCanonicalDivisor_of_isCurveOver.lean
```

**Two private helpers had to be promoted, and that is the measurement that the split is
real.** Eight declarations that the pin keeps `private` were used across the new
boundaries: the six `AdjoinRingProperties` facts about `K⟮t⟯`
(`isPrincipalIdealRing_adjoin`, `isDedekindDomain_adjoin`, `isIntegrallyClosed_adjoin`,
`isNoetherianRing_adjoin`, `finiteType_adjoin_singleton`, `transcendental_inv`, all used by
`HasCanonicalDivisor` too) and the two centre-ideal facts
(`inv_mem_of_not_mem_centerIdeal`, `div_mem_of_not_mem_centerIdeal`, used by
`HasCanonicalDivisor`'s `eq_of_centerIdeal_eq_s12`). They are now public with docstrings —
real mathematics, and the port's rule is that it does not stay `private` (§4) — which is
also why the checked surface grew from 111 to 117 declarations.

Also: the 7 `own:` rows moved to `ValSubringKaehler.lean` in `spec/decl_markers.tsv` (the
2 remaining ones stay on `HasCanonicalDivisor.lean`), and `old_check_stmts.py`'s handover
comment names all four modules with their verdicts.

**Verified.** `lake build` of the four modules (2,776 jobs; no warning in any of them); each
module's `check_port --force` above, every wire 0 mismatch / 0 missing; `dedup.py` over
`Canonical/*` unchanged in kind — the `⊢ letI` shape artifact (now 12 copies across
`ValSubringKaehler` and `AffineChart`) and the instance-discharge pair in `DCoordGenerates`,
both documented in §11–§12; `unwired_register.py --check` current; and the three dependents
that reach the split pieces directly (`Differential/Coefficient.lean` for the `dCoord`
existentials, `P1/Separating.lean` for the reciprocal transport, `P1/FinitePlaceResidue.lean`
for `ValuationSubring.idealOfLE`) rebuilt green as spot checks. Still no tree build, so the
104 dependents' oleans are stale until the next wave.

## 14. The checker's stage-label tier (2026-10-25)

The `_s12` suffix is the pin's *stage* label, not part of the name: the corpus uses
`_s0` … `_s19` (2,146 `_s17`, 319 `_s12`), and the port's naming policy drops it exactly
as it drops the `p0n\d+_` part *prefix*. `spec/check_port.py` now has the matching tier,
placed with the other label tier:

```
marker name → exact last name → part label dropped → stage label dropped
            → promoted key → kw_ strip → content hash anywhere in the wire
            → mismatch / missing
```

`STAGE_LABEL` (a trailing `_s\d+`), `strip_stage_label`, and a `Wire.by_stage` index built from the
pin side — the same shape as `strip_part_label` / `by_part`, so the port may spell
`exists_ord_eq_zero_D_eq_smul_D` where the pin writes `…_s12`, and the report says **which
pin declaration** it matched (`how: stage label dropped`) instead of the bare `content` hit
that a statement hash anywhere in the wire gives.

**Why it is safe, in three parts.**

1. *It cannot accept a drifted statement.* Every tier after the exact name is hash-gated
   (`pick` requires `nhash` equality), so a stripped-name candidate is only taken when its
   statement is the port declaration's. The fixture `lean/tmp/probe_stage.lean` pins both
   halves: one declaration with the pin's statement under the stripped name (**ok**, `how:
   stage label dropped`) and one with a *deliberately different* statement under the same
   stripped name (**missing**, never `ok`).
2. *It cannot change an existing verdict.* The tier sits after every hash-gated name tier,
   so a declaration that is `ok` today has already returned from an earlier tier; an
   `own`-marked one short-circuits on its marker. Measured: with the tier disabled in a
   throwaway copy of the checker, `ValSubringKaehler` 50/7, `AffineChart` 37/0,
   `DCoordGenerates` 10/0, `HasCanonicalDivisor` 13/2 and `Differential/Coefficient` 8/1
   (`ok`/`own`) — identical to the tiered run. The only modules in the cached corpus with
   `mismatch`/`missing` are two untracked `tmp/` probes, and neither is a library module.
3. *It does not fire when the port keeps the label.* The lookup is skipped when the port's
   own name carries a stage suffix, so a port declaration spelled `…_s12` still matches its
   pin twin by exact name, and the tier never reinterprets a name the pin did not label.

What it does **not** do: it changes no verdict today, because the content tier already
verified faithful renames. Its value is the naming policy made mechanical — the 26 remaining
`_s12` names in the four canonical-divisor modules can be rectified without a marker row,
and the report will attribute each to the pin declaration of the same name family. Note the
two names whose stripped form is already taken *in the port* (`hasCanonicalDivisor_of_isCurveOver_s12`,
`exists_mem_D_eq_smul_D_of_isCurveOver_s12`): those are Lean name collisions, not checker
ones, and were the reason §12 left the suffix in place.

Also updated: the checker's header (tier list and the label paragraph) and the playbook's
matching paragraph (§4), so the policy and the implementation say the same thing.

## 15. The `_s12` names rectified (2026-10-25)

All 26 remaining stage-labelled names in the canonical-divisor layer are gone; `grep _s12
FLTForHuman` is empty. 15 were plain renames (`hasCanonicalDivisor_of_generator_finiteSupport`,
`mem_span_D_adjoin`, `finite_ordDifferential_D_ne_zero`, `dCoord_eq_D_uniformizerSubring`,
…), and the checker verifies each through the §14 tier — `how: stage label dropped`, no
`decl_markers.tsv` row. The other 11 were **S_-copy/wrapper pairs**, where the base name was
already held by the port: rectifying the name means keeping one declaration, so each pair
collapsed:

| pair | surviving declaration | where |
|---|---|---|
| `hasCanonicalDivisor_of_isCurveOver_s12` / `hasCanonicalDivisor_of_isCurveOver` | the wrapper's name, the `S_` copy's proof | `Canonical/HasCanonicalDivisor.lean` |
| `exists_mem_D_eq_smul_D_of_isCurveOver_s12` / … | the `Theorems/` wrapper's name, the `S_` copy's proof | `Differential/Coefficient.lean` |
| six `IntermediateField.*_s12` / `P1/Separating.lean`'s delegators | the base name, in the **upstream** module | `Canonical/AffineChart.lean` |
| three `ValuationSubring.*_s12` / `P1/FinitePlaceResidue.lean`'s delegators | the base name, in the **upstream** module | `Canonical/ValSubringKaehler.lean` |

The direction of each collapse is forced by the DAG: the six `IntermediateField` facts and
the three `ValuationSubring` ones are used *upstream* (by the chart engine and by
`DCoordGenerates`), so they cannot move down to the module that holds their pin-public
name — the declaration stays where the mathematics is, takes the base name, and the
downstream delegator disappears. The two headlines are the opposite case: nothing upstream
uses them, so the proof travels to the module that homes the pin's `Theorems/` wrapper.
Nine pairs therefore also removed nine cross-module duplicates: `dedup.py` over
`*Canonical*` + `*P1*` no longer reports `adjoin_simple_inv`, `eq_top_of_idealOfLE_eq_bot`,
`idealOfLE_ne_bot_of_ne_top`, `eq_of_isDiscreteValuationRing_of_le`,
`exists_mem_D_eq_smul_D_of_isCurveOver` or `hasCanonicalDivisor_of_isCurveOver` as
clustered, and the checked surface is 26 declarations smaller by construction.

Measured after the change: `lake build` of the seven touched modules green (2,872 jobs, no
warning in any of the five wired ones); `check_port --force` — `ValSubringKaehler` 50 ok /
7 own, `AffineChart` 37 / 0, `DCoordGenerates` 10 / 0, `HasCanonicalDivisor` **11 / 2**
(two fewer declarations: the merges), `Differential/Coefficient` 8 / 1, every wire 0
mismatch / 0 missing; the `how` column reads `stage label dropped` for every renamed
declaration and `direct name` for the two merged headlines; consumer
`spec/DsHeadConsumer.lean` 0 errors / 0 warnings; `unwired_register.py --check` current.
The two `own:` rows that survive on `HasCanonicalDivisor.lean` are the two declarations
whose *statements* name the pin's private `uniformizerSubring''`/`'''` — that is a name in
the statement, not in the declaration name, so §14's tier does not apply to them.

`P1/Separating.lean` and `P1/FinitePlaceResidue.lean` keep three pre-existing
`linter.unusedSectionVars` warnings about theorems unrelated to this change; they are on
the frozen checker and were not brought up to date here.

## 16. Sequel (2026-10-27): the nonzero-order family — six nodes, one text

### 16.1 The measurement, and why the frontier overcounts

`frontier.py --ds --include-leaves --ready` priced five nodes at 79 raw lines each —
`AlgebraicCurve.Place.diffCoeff_smul_D_eq`, `…diffCoeff_smul_D_of_ord_ne_zero`,
`…D_ne_zero_of_ord_ne_zero`, `…exists_eq_smul_D_of_ord_ne_zero`, `…ordDiff_zero` — all
`silo 79 / needed 1 / hops 1`, i.e. all ready with every premise already ported. Read
with `diff`, the five `S_` files are **one text**: any pair differs only in the
`namespace P2MW.…` line and the three-line `solution` tail. So 5 × 79 = 395 raw lines are
a 76-line body plus five 3-line wrappers, and the frontier was counting the same file
five times.

`port_advise.py --nodes` on the five said so directly: **0 substitutions**, 8 names
proved in ≥2 target files (≈200 removable lines), strongest factoring unit 50 lines / 8
proofs shared by *every* pair. `port_plan.py` then priced the set: raw 395 → declaration
270 → minus 200 duplicates → **once-cost 70 → net new mathematics 70**.

Why this family and not its neighbours: the `_of_ord_eq_one` siblings of the same two
coefficient headlines are 19–31-line files with no prelude, which is why the port already
had them. The `_of_ord_ne_zero` files each embed the whole eight-declaration prelude
(`isSeparable_adjoin`, `D_ne_zero_of_ord_ne_zero`, `exists_eq_smul_D_of_ord_ne_zero`,
`diffCoeff_smul_D_of_ord_ne_zero`, `diffCoeff_smul_of_ord_ne_zero`,
`ordDiff_smul_D_uniformizer`, `ordDiff_zero`, `ordDiff_D_uniformizer`), so a per-node
price is five times the per-file price. A sixth node of the same headline,
`…ordDiff_zero_of_perfectField` (31 lines, `needed 1`), was ready alongside them; it is
the characteristic-`p` flavour of the same statement and came in the same wave.

### 16.2 The mathematics is zero — it is a transcription

Every ingredient was already in the port: `diffCoeff`, `diffCoeff_smul_D`, `Place.ordDiff`
+ `ordDiff_def`, `Place.uniformizer_alt` + `ord_uniformizer_alt` (this module),
`span_D_eq_top_of_transcendental`, `D_ne_zero_of_transcendental`
(`Defs/KaehlerTranscendental.lean`), `transcendental_of_ord_ne_zero`,
`isAlgebraic_adjoin_of_transcendental`, and `smul_left_injective` from mathlib. The one
non-obvious saving: the pin's private `isSeparable_adjoin` gets separability from
`[CharZero K]` alone — `charZero_of_injective_algebraMap` then `infer_instance` — so the
455-line separable-uniformiser engine (`Place/SeparableUniformiser.lean`) is **not on this
path**, and the `p`-th-power machinery of the uniformiser case is not replayed.

### 16.3 Incomparable, not redundant

The two hypothesis sets are `[PerfectField K]` with `ord t = 1` and `[CharZero K]` with
`ord t ≠ 0`. Neither implies the other — a finite field is perfect of characteristic `p` —
so both are pinned statements and the port keeps both. `dedup.py` reports exactly two
`shape` clusters in the module, `ordDiff_zero` / `ordDiff_zero_of_perfectField` and the
pre-existing `ord_diffCoeff_D_nonneg_of_isSeparable` / `…_of_perfectField`; in both, the
copies differ in their hypotheses, so nothing is removable.

### 16.4 What landed

`FLTForHuman/AlgebraicCurve/Differential/Coefficient.lean`, +147 lines: ten declarations
totalling 65 lines, the rest documentation, two small `variable` sections and the
`spec-pin:` wire. No new module, no new import.

The declarations are split 7 nodes + 3 helpers:

| declaration | pin |
|---|---|
| `Place.D_ne_zero_of_ord_ne_zero` | `Theorems/Thm_…_D_ne_zero_of_ord_ne_zero.lean` |
| `Place.exists_eq_smul_D_of_ord_ne_zero` | `Theorems/Thm_…_exists_eq_smul_D_of_ord_ne_zero.lean` |
| `Place.diffCoeff_smul_D_of_ord_ne_zero` | `Theorems/Thm_…_diffCoeff_smul_D_of_ord_ne_zero.lean` |
| `Place.diffCoeff_smul_D_eq` (the pin's `diffCoeff_smul_of_ord_ne_zero`) | `Theorems/Thm_…_diffCoeff_smul_D_eq.lean` |
| `Place.ordDiff_zero` | `Theorems/Thm_…_ordDiff_zero.lean` |
| `Place.ordDiff_zero_of_perfectField` | `Theorems/Thm_…_ordDiff_zero_of_perfectField.lean` |
| `Place.isSeparable_adjoin_of_ord_ne_zero` (promoted private) | `S_…_D_ne_zero_of_ord_ne_zero.lean:26` |
| `Place.ordDiff_smul_D_uniformizer` | `S_…_D_ne_zero_of_ord_ne_zero.lean:59` |
| `Place.ordDiff_D_uniformizer` | `S_…_D_ne_zero_of_ord_ne_zero.lean:69` |
| `Place.ordDiff_smul_D_uniformizer_of_perfectField` (the perfect-field private copy of the same) | `S_…_ordDiff_zero_of_perfectField.lean:14` |

`ordDiff_smul_D_uniformizer` is written publicly although the pin keeps it as prelude: it
is the computation of `v.ordDiff` on the generator, `ordDiff_zero` and
`ordDiff_D_uniformizer` are its `g = 0` / `g = 1` cases, and the pin's next node in this
ring (`Place.ordDiff_smul`) is its generalisation, so hiding it would only make the next
wave re-derive it.

### 16.5 The one round lost: the diff is textual

Three of these declarations come from the pin's *section* (`variable` block plus
`include x in`), and the pin's prelude text reads `D`, not `KaehlerDifferential.D`. Both
points are load-bearing for `check_port.py`, whose comparison is textual:

* spelling the section's variables inline **builds** but reports `MISMATCH` (§4 of the
  playbook, stated there for `def`s — it is equally true of a prelude theorem);
  `isSeparable_adjoin_of_ord_ne_zero` and the two `ordDiff` generator lemmas are therefore
  written in two small sections (`SeparableAdjoin`, `OrdDiffGenerator`), which reproduce
  the pin's binder block exactly;
* `KaehlerDifferential.D` in place of the pin's opened `D` also reports `MISMATCH`, even
  though the two terms are the same at this file's `open KaehlerDifferential`. The port
  keeps the pin's spelling in those two declarations only; everywhere else the file writes
  the qualified form, as its `Theorems/`-derived neighbours do.

### 16.6 Verification

* build: `lake build FLTForHuman.AlgebraicCurve.Differential.Coefficient` — green,
  2,869 jobs, 4.0 s, **no warning** (`lean/tmp/build-coefficient.log`).
* `check_port --force` — **22 ok / 0 mismatch / 0 missing / 1 own / 0 kw**, the single
  `own` being the pre-existing `diffCoeff_uniformizer_eq_differentialCoeff`. **No
  `spec/decl_markers.tsv` rows were needed**: the promoted separable lemma and both
  `ordDiff` prelude lemmas resolve through the content tier against the pin's *private*
  copies (`[pin name …]`), which is the behaviour the private-copy tier was built for.
* `#print axioms` on all ten: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* `dedup.py --module …`: two `shape` clusters, both the deliberate flavour pairs (§16.3).
* `move_dead.py` was **not** applied. The module is a mathlib-like API layer, exempt under
  `topics/instructions.md`, and every new declaration is a pin node or its prelude: their
  consumers (`Place.ordDiff_smul`, `ordDiff_D_eq_ord_sub_one`, `ordDiff_eq_ordDifferential`,
  `ordDiff_D_nonneg`, `AlgebraicCurve.mem_regularDiffs_iff`, and the `ModularCurve.coeffMap`
  pair) are unported, so they have 0 references elsewhere in the port today.

### 16.7 Effect on the cone, and the next wave

`frontier.py --ds --include-leaves` after the wave: F 1,283 → 1,289 nodes, `needed
[F terminal]` 1,120 → 1,114 nodes and 424,617 → **424,191** lines — a 426-line drop for 65
written declaration lines, i.e. the frontier's exact six silo prices, and none of the five
rows remains on the ready shelf. Two nodes of the same ring became ready:
`AlgebraicCurve.Place.ordDiff_smul` (44 lines) and `…ordDiff_smul_of_perfectField` (40),
the two-flavour shape again. They are the natural next wave: after them
`ordDiff_D_eq_ord_sub_one`, `ordDiff_D_nonneg` and `mem_regularDiffs_iff` come into view,
and those are the nodes the `ModularCurve` genus route actually cites.

## 17. Sequel (2026-10-27): the multiplication law, and the 508-line engine that is one line

### 17.1 The measurement

After §16 the D-S shelf held three ready nodes of this corner. `port_advise.py --nodes`
on them (`ord_diffCoeff_D_nonneg`, `ordDiff_smul`, `ordDiff_smul_of_perfectField`) — 6
target files, 18 declarations — reported **10 declarations whose statement the port
already has** (≈175 lines not to re-prove), 7 of them importable public and **3 only as a
port-private declaration**: `H1_impl` and the two `solution`s, "private in
`FLTForHuman/AlgebraicCurve/Differential/Different.lean`". That is the instrument naming
the job: the perfect-field node was already proved, as a private helper of the different's
effectivity bound.

### 17.2 `ord_diffCoeff_D_nonneg`: 508 pin lines, one port line

The pin's file is 508 lines — `polyMem`, `isLocalization_valuationSubring`,
`isAlgebraic_residue`, the fibre-centre dictionary, a `RatFunc` tower and an
`Algebra.Unramified`/`FormallyUnramified` chain — all to conclude an integrality bound
that the port obtained, in an earlier wave, from
`exists_mem_D_eq_smul_D_of_isCurveOver` plus the `IsCurveOver` supply. Its 508 lines have
**no content the port needs**: the headline is

```
ord_diffCoeff_D_nonneg_of_perfectField x v ht hf
```

because a field of characteristic zero is perfect (`PerfectField.ofCharZero`,
`Mathlib/FieldTheory/Perfect.lean:306`), and the pin's node is the perfect-field statement
with `[CharZero K]` in place of `[PerfectField K]` and nothing else changed. This is the
second time this corner's hand-built engine has been replaced rather than transcribed; the
first is §10's, recorded in the module's own header.

### 17.3 `ordDiff_smul_of_perfectField`: a promotion, not a port

The pin states `H1_impl` privately in one file and publicly in another (the node); the
port had transcribed it as `private theorem ordDiff_smul_impl` inside
`Differential/Different.lean`, where it is a helper of the different's bound. Promoting it
is the §2.4 case — "a pin-`private` block re-exported by name mangling is a promotion: ...
'which side stays' is the pin-public wrapper" — so the copy moved to the coefficient layer
at the pin's node name and statement, and `Different.lean` now imports it and keeps no
second copy. `dedup.py` over the two modules reports **0 across-module clusters** (it
reported the pair before).

### 17.4 What landed

`Differential/Coefficient.lean`, +217 lines: three declarations totalling 41 lines (15, 21
and 5, the last a one-liner with its docstring), a section header, three pin URLs and six
`spec-pin:` lines. `Differential/Different.lean`, −28/+10: the private theorem deleted, its
single use retargeted, three comment references brought up to date.

| declaration | pin | cost |
|---|---|---|
| `Place.ordDiff_smul` | `Theorems/Thm_…_ordDiff_smul.lean` (44-line file) | 15 lines, pin's proof |
| `Place.ordDiff_smul_of_perfectField` | `Theorems/Thm_…_ordDiff_smul_of_perfectField.lean` (40) | 21 lines, promoted from `Different.lean` |
| `Place.ord_diffCoeff_D_nonneg` | `Theorems/Thm_…_ord_diffCoeff_D_nonneg.lean` (508) | 5 lines, `_of_perfectField` + `ofCharZero` |

### 17.5 Verification

* `lake build FLTForHuman.AlgebraicCurve.Differential.Different` (which rebuilds
  `Coefficient`) — green, 2,873 jobs, no warning in either module.
* `check_port --force`: `Coefficient` **25 ok / 0 mismatch / 0 missing / 1 own** (was 22
  ok: the three new nodes), `Different` **5 ok / 0 / 0 / 0** (unchanged — its private
  declaration was never on the wire).
* `#print axioms` on the three, and on `ord_sub_one_le_ordDiff_D_of_perfectField` whose
  proof changed: `[propext, Classical.choice, Quot.sound]`.
* `dedup.py` over both modules: 5 `shape` clusters, all deliberate flavour pairs (the
  `ord_diffCoeff_D_nonneg` triple, the `ordDiff_smul` pair, `ordDiff_zero`'s pair, and two
  pre-existing ones inside `Different.lean`); none across modules.
* `unwired_register.py --check`: current.

### 17.6 Effect on the cone

`needed [F terminal]` 1,114 → 1,111 nodes and 424,191 → **423,599** lines — a 592-line
drop, exactly the three silo prices (508 + 44 + 40), for 41 written declaration lines and
one deleted duplicate. `AlgebraicCurve.mem_regularDiffs_iff` is now **ready** (`needed 1`,
93 lines) — it cites three of §16's six nodes; `ordDiff_D_eq_ord_sub_one` and
`ordDiff_eq_ord_diffCoeff` are at `needed 2` with their silos collapsed from 713 to 205,
which is the measure of how much of their price was this family rather than their own
files.

### 17.7 Recorded negative

`ord_diffCoeff_D_nonneg`'s engine is not ported, and should not be: nothing in the port's
route to the D-S head needs a `RatFunc`-tower proof of integrality, because
`IsCurveOver`/`exists_mem_D_eq_smul_D_of_isCurveOver` already supplies it at every place.
The 508 lines are the third-worst overcount measured in this corner, after §16's five-fold
copy of one file.

## 18. Sequel (2026-10-27): the regular differentials are a subspace

### 18.1 The measurement

`AlgebraicCurve.mem_regularDiffs_iff` was the first node of the previous ring that the
frontier called ready (`needed 1`, 93 lines, `used_by cone 1`). `port_advise.py --nodes`
said **0 substitutions** and no name proved twice: nothing of it existed anywhere in the
port.

### 18.2 The definition layer had not landed

The node's statement names `regularDiffs K F` and `IsRegularDiff K F`, which the pin
defines in `Definitions/Def_AlgebraicCurve_Differentials.lean:46-64` — the same definition
module §3 absorbed into `Differential/Coefficient.lean`. The port had taken that module's
coefficient and `ordDiff` vocabulary (lines 1-44) and stopped; the five declarations of its
second half were missing. They are now in `Coefficient.lean`, at the pin's own position
(after `Place.ordDiff_def`, before the section that uses the vocabulary):

| declaration | pin |
|---|---|
| `IsRegularDiff` | `Definitions/Def_AlgebraicCurve_Differentials.lean:48` |
| `isRegularDiff_iff` | `:51` |
| `regularDiffs` | `:56` |
| `mem_regularDiffs_of_isRegularDiff` | `:59` |
| `regularDiffs_eq_span` | `:63` |

No new `spec-pin:` line was needed — the definition file is already the module's first pin,
and the checker diffs the five by name. `Coefficient` is now **30 ok / 0 mismatch / 0
missing / 1 own**.

### 18.3 The node, and its prelude as its own home

`Differential/RegularDiffs.lean` (113 lines, 6 declarations) carries the pin's five
prelude lemmas and the headline. The prelude is the mathematics and is not private in the
pin: `diffCoeff_add` (the coefficient is additive in the differential at nonzero order),
`min_ordDiff_le_ordDiff_add` (the ultrametric inequality for `ordDiff`, through `ord` of
the coefficient) and the three closure cases `isRegularDiff_zero/add/smul`. Every
ingredient had already been ported for its own sake — §16's `diffCoeff_smul_D_of_ord_ne_zero`
and `diffCoeff_smul_D_eq`, `ordDiff_zero`, §17's `ordDiff_smul`, and
`Place.min_ord_le_ord_add` — which is why the proofs are transcriptions.

The module's role is one statement: **membership in `regularDiffs` is the pointwise
condition**, so the span adds nothing and "regular" is a `Submodule` membership. Its header
also records the pin's *other* spelling of regularity (`regularDifferentials`: locally a
multiple of `dCoord` by an integral element) so the two are not mistaken for one another
when the comparison node comes.

Two mechanical points paid for before:

* the prelude is written in the pin's **section** (its signature text is `(v : Place K F)`,
  with `K F x` invisible); §16.5's finding applies unchanged, and the checker resolves all
  five against the `S_` copy;
* the headline is written at the **`Theorems/` wrapper's** shape, which is what the checker
  matched (`-> Theorems/Thm_AlgebraicCurve_mem_regularDiffs_iff.lean:7`).

One proof adaptation: the pin's `Place.min_ord_le_ord_add` requires the two nonzero facts
of the summands, the port's ported node only the nonzero fact of the sum, so the call drops
two arguments. Nothing else in the file differs from the pin.

### 18.4 Verification

* `lake build FLTForHuman.AlgebraicCurve.Differential.Coefficient` and `…RegularDiffs` —
  green, no warning in either module.
* `check_port --force`: `Coefficient` 30 ok / 0 / 0 / 1 own, `RegularDiffs` **6 ok / 0
  mismatch / 0 missing / 0 own**.
* `#print axioms` on the headline and on `diffCoeff_add`, `min_ordDiff_le_ordDiff_add`,
  `isRegularDiff_smul`: `[propext, Classical.choice, Quot.sound]`.
* `dedup.py` over the two modules: 3 `shape` clusters, all the deliberate flavour pairs of
  §16 and §17; nothing from the new module. `unwired_register.py --check`: current.

### 18.5 Effect on the cone

`needed [F terminal]` 1,111 → 1,110 nodes and 423,599 → **423,506** lines (the node's own
93). The next ring did not move, and the reason is one small node rather than a block:
`ordDiff_D_eq_ord_sub_one` and `ordDiff_eq_ord_diffCoeff` are both at `needed 2` with
silos of 205 and 178 lines each, and every premise they cite except one is ported —
`Place.ord_add_eq_of_lt`, ready, **27 lines**, `used_by cone 5`. Porting it makes both
ready; they are the two nodes the `ModularCurve` genus route cites through
`ordDiff_D_eq_ord_sub_one`.

## 19. Sequel (2026-10-27): the order of `D f`, and a two-file cluster again

### 19.1 The measurement

The three nodes of the previous ring were `ord_add_eq_of_lt` (27 lines, ready) and the two
headlines `ordDiff_D_eq_ord_sub_one` / `ordDiff_eq_ord_diffCoeff` (178 lines each,
`needed 2`, silos 205). `port_advise.py --nodes` on them reported two things at once:

* `ord_add_eq_of_lt` **already exists in the port** — as `private theorem
  ord_add_eq_left'` in `P1/DivisorAction.lean:21` and as `private theorem ord_add_eq_left`
  in `P1/EnginePrelude.lean:201`, both transcribed from the pin's *private* `ord_add_eq_left`
  of the ℙ¹ chunk. The node's statement is the same statement;
* the two 178-line files are **one text**: `diff` differs only in the `namespace` line and
  the last `solution`, and 7 declarations are shared between them (≈144 removable lines).

So 27 + 178 + 178 = 383 frontier lines are one 27-line node already present privately, and
one 175-line body written twice.

### 19.2 What landed

`Place/OrdCalculus.lean`, +1 declaration: `Place.ord_add_eq_of_lt`, at the pin's node
statement, with its two `spec-pin:` lines. This is the place-calculus home; the two ℙ¹
private copies were **not** touched — `P1/EnginePrelude.lean` and `P1/DivisorAction.lean`
are on the frozen checker's list and carry no `spec-pin` wire, so editing them is the
"legacy module brought up to standard" job (§ Legacy Modules, `topics/instructions.md`) and
not part of this wave. They are recorded here as deliberate residue: after that job, two
private copies disappear and two call sites change (`DivisorAction.lean:309` and the copy in
`EnginePrelude.lean`).

`Differential/Coefficient.lean`, +6 declarations: the shared body of the two 178-line files,
written once, at the end of the module (it needs the integrality headline above it):

| declaration | pin | node |
|---|---|---|
| `ord_diffCoeff_D_eq_zero` | `S_…_ordDiff_D_nonneg.lean:49` | prelude |
| `ordDiff_eq_ord_diffCoeff` | `S_…_ordDiff_D_nonneg.lean:70` | **node** |
| `ordDiff_D_nonneg` | `S_…_ordDiff_D_nonneg.lean:89` | **node** (came along) |
| `ordDiff_D_of_ord_pos` | `S_…_ordDiff_D_nonneg.lean:96` | prelude |
| `ordDiff_D_eq_ord_sub_one` | `S_…_ordDiff_D_nonneg.lean:142` | **node** |
| `ordDiff_D_eq_ord_sub_algebraMap_sub_one` | `S_…_ordDiff_D_nonneg.lean:162` | prelude |

`ordDiff_D_nonneg` is a node with its own `Theorems/` wrapper and was not in the approved
set; it is inside the shared body, so it lands too. The cluster's `ordDiff_smul` — the two
files' first declaration — is **not** copied: it is §17's public node, imported.

Mathematically this is the sharp form of what `Differential/Different.lean` proves as an
inequality over a perfect base field: over a field of characteristic zero,
`ord (D f) = ord f - 1` at every place where `f` has nonzero order, with the `f = u π ^ n`
expansion and the strict ultrametric equality `ord_add_eq_of_lt` doing the work.

### 19.3 The one round lost, again the same two causes

Both mismatches on the first check were textual, and both are the §16.5 lesson in a new
guise: the pin's prelude writes `Place.diffCoeff` **qualified** (the port, inside `namespace
Place`, writes the bare `diffCoeff`), so `ord_diffCoeff_D_eq_zero` and
`ordDiff_eq_ord_diffCoeff` reported `MISMATCH` until the qualification was restored. Two
declarations, two lines. No marker rows, no section reshaping.

One proof adaptation: the port has no public `Place.ord_natCast` (only the private copies in
`Hurwitz.lean` and `Genus/ConstantFieldExtension.lean`), so the single use in
`ordDiff_D_of_ord_pos` is an inline
`rw [← map_natCast (algebraMap K F) n]; exact v.ord_algebraMap (n : K)`. Promoting that
lemma publicly is a follow-up of the same kind as §17's; it is not on this wave's path.

### 19.4 Verification

* `lake build FLTForHuman.AlgebraicCurve.Differential.Coefficient` (which rebuilds
  `OrdCalculus`) — green, no warning in either module.
* `check_port --force`: `OrdCalculus` **21 ok / 0 / 0 / 0**,
  `Coefficient` **36 ok / 0 mismatch / 0 missing / 1 own** (was 30).
* `#print axioms` on all seven new declarations: `[propext, Classical.choice, Quot.sound]`.
* `dedup.py` over the two modules: 3 clusters, all the deliberate flavour pairs; nothing
  from this wave. `unwired_register.py --check`: current.

### 19.5 Effect on the cone

`needed [F terminal]` 1,110 → 1,107 nodes and 423,506 → **423,123** lines — 383 lines, exactly
the three approved silo prices; F grew by 4 nodes (the bonus `ordDiff_D_nonneg`).
`AlgebraicCurve.exists_constantFieldExtension` dropped from `needed 2` to **`needed 1`**
(silo 314, `used_by cone 5`): the constant-field-extension route through
`ordDiff_D_eq_ord_sub_one`. The rest of the ready shelf in this namespace is now small
pieces — `localUnitDerivativeRegular_of_isCurveOver` (79), `Place.ord_nonneg_of_isIntegral_adjoin_of_ord_nonneg`
(31), `exists_poleDivisor_of_transcendental` (26), and three `Divisor.evalFun_*` lemmas of
12–15 lines — so the differential corner of the D-S cone is essentially closed above this
line.

## 20. The `ord_add_eq_of_lt` duplicate retired (2026-10-27)

§19.2 left the two private copies in place because `P1/EnginePrelude.lean` and
`P1/DivisorAction.lean` were on the frozen checker's list with no `spec-pin` wire. That
residue is now discharged, and with it the two modules are brought up to the standard
`topics/instructions.md` sets for a touched legacy module.

**The duplicate.** `private theorem ord_add_eq_left` in `P1/EnginePrelude.lean` and
`private theorem ord_add_eq_left'` in `P1/DivisorAction.lean` were both the pin's private
`ord_add_eq_left`, i.e. the statement of the node `Place.ord_add_eq_of_lt` ported in §19.
The `DivisorAction` one was used once (its Wronskian-bound consumer, now
`rw [Place.ord_add_eq_of_lt (p1PlaceInfty K) hg0 hXe0 hlt]`); the `EnginePrelude` one had
**no consumer at all**. Both are gone: 20 lines and 24 lines.

**Dead plumbing, binned.** `move_dead.py --select dead` then reported 2 declarations in 21
lines inside `EnginePrelude` — `section Chart`'s `chartHom` and `inv_algebraMap_mem`, a
local copy of the private helpers `Defs/PlacesOverDVR.lean` keeps *where they are consumed*.
Unreachable here, and `--apply` refuses a block that is not unique in the tree, so the §3.8
answer applies: the plumbing is deleted (`section Chart`, 26 lines with its variables), not
shelved. `move_dead.py` now reports 0 declarations / 0 lines for both modules.

**The upgrade, item by item** (`topics/instructions.md`, "Legacy Modules"):

| item | state |
|---|---|
| `spec_pin` | both modules carry the two `spec-pin:` lines of the ℙ¹ residue core (`Theorems/` + `P2M/Sol/`), and their headers say what the wire does |
| deletion from old checker | both removed from `PORT_FILES` in `spec/old_check_stmts.py`, with the handover recorded inline |
| silent build | green, no warning in either module |
| no build time blow up | `EnginePrelude` 5.2 s, `DivisorAction` 4.3 s; the one new import is `Place/OrdCalculus` (a `Defs`-only module, 3.1 s) |
| no random tokens in names | checked: no `_s<n>`, `kw_`, `_impl`, or prime-suffixed declaration names in either module (the primes are on bound variables, as in the pin) |
| `dedup.py` | 0 duplicate clusters over the two modules (67 declarations), 0 removable lines |
| `move_dead.py` | 0 dead declarations |

**Measured.**
`spec/check_port.py --force`: `P1/EnginePrelude` **40 ok / 0 mismatch / 0 missing / 0 own**,
`P1/DivisorAction` **19 ok / 0 / 0 / 0** — the statements were transcribed verbatim from the
same `S_` file, so the wire closed on the first run. The frozen checker over the whole tree:
**0 mismatched, 0 missing** (7,523 identical statements, 35 own-proof and 294
registered-unwired exemptions), i.e. dropping the two modules from `PORT_FILES` created no
coverage hole. `unwired_register.py --check`: current.

**Recorded, not done.** Two things in this neighbourhood stay as they are, deliberately:
`ord_add_eq_min` (the pin keeps it *private*, there is no node and no `Theorems/` wrapper, so
promoting it would be a port decision without a pin name to land at), and
`Place.ord_natCast` (§19.3's inline step: it is a node, but a small one on no current path).
The dated audits under `topics/riemannRoch/` still describe the pre-cleanup state — they are
records of their date and were not rewritten.

## 21. Sequel (2026-10-27): the discriminant shape, and the pullback formula

The two ready nodes of this wave are the last two leaves of the differential corner that the
`ModularCurve` layer cites. They are unrelated in subject but share a home question, and one of
them needed a missing definition first.

### 21.1 The definition the pullback node needed

`ordDiff_pullbackDiff_of_natCast_ramificationIndexAlong_ne_zero` states its conclusion with
`pullbackDiff`, which the pin defines in `Definitions/Def_AlgebraicCurve_Differentials.lean:70`
— the definition module §3 absorbed into `Differential/Coefficient.lean` and §18 finished for
its regular-differentials half. The pullback section (lines 66–79: `pullbackDiff`,
`pullbackDiff_D`) was still untaken, so it is now in `Coefficient.lean` at the pin's own place,
body verbatim: **38 ok / 0 mismatch / 0 missing / 1 own**.

The pin defines the same map a second time in a *different* definition module as
`pullbackAlong` (which the port already carries, with `traceAlong`/`correspondence` on top).
Both are kept, because the pin's statements name both spellings; the module docstring says so.
`dedup.py` does not flag the pair (their `def` bodies differ in shape), and it should not be
merged without a pin statement to land at.

### 21.2 `ordDiff_smul_D_nonneg_of_ord_pow_six_…` — the discriminant shape

113 pin lines, homed in `Differential/Different.lean` because it *is* the different's
effectivity bound applied to one element shape: for `g J : F` and
`0 ≤ ord (g ^ 6 * J ^ 4 * (J - 1728) ^ 3)` (a discriminant-shaped product, `1728` the
degenerate `j`-value) the differential `g • D J` is regular. The proof is the pin's case
analysis on `ord J` against `0`, and it is the first consumer of §20's public
`Place.ord_add_eq_of_lt`. Two adaptations: the pin's private `ord_pow_of_ne_zero` is the port's
public `v.ord_pow`, and its `ordDiff_D_nonneg_pf_bridge` is inlined (the port's
`ordDiff_D_nonneg` is the `[CharZero K]` node, which is not available under `[PerfectField K]`).
One import added: `Place/OrdCalculus` (for `ord_add_eq_of_lt` and `exists_ord_eq_one`).
`Different.lean`: **6 ok / 0 mismatch / 0 missing**.

### 21.3 `ordDiff_pullbackDiff_of_natCast_…` — the ramification bookkeeping

283 pin lines, the largest node of this corner. New module
`Differential/PullbackOrd.lean` (288 lines): the pin's twelve private helpers transcribed
`private`, plus the headline at its `Theorems/` wrapper. The mathematics is
`ordDiff (pullbackDiff φ ω) = e * ordDiff (restrictAlong w' ω) + (e - 1)` with
`e = ramificationIndexAlong φ w'`, under tameness (`((e : ℕ) : K) ≠ 0`) — the ramification index
times the order, plus one different exponent.

`port_advise` had already said what was reusable (`ramificationIndexAlong_pos` is public in
`Defs/RestrictAlongAPI.lean`, and is *not* re-proved here), and the port body was dispatched to
a subagent under `topics/algebraicCurve/WORKORDER-ordDiff-pullbackDiff.md` — the prelude is
twelve helpers of real proof work, which is the case §0.2 of the playbook reserves for a
workorder. Adaptations, both mechanical: `ramificationIndexAlong_pos` imported rather than
copied, and the pin's `FtameBuild.hadd w' x` call reproduced without the `φ hφ` arguments Lean
drops from that binder block. Verified here, not taken on the report: build
`lake build …PullbackOrd` green in 7.3 s with **no warning** from the module,
`check_port --force` **1 ok / 0 mismatch / 0 missing / 0 own**, `#print axioms`
`[propext, Classical.choice, Quot.sound]`, `dedup.py` 0 clusters, no `sorry`.

### 21.4 Effect on the cone

`needed [F terminal]` 1,107 → **1,105** nodes and 423,123 → **422,727** lines: 396 lines, exactly
the two silo prices (113 + 283). The ready shelf went 109 → 107, i.e. these two leaves were the
whole shelf movement: neither consumer came free. Both are large:
`ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion`
now needs 14 nodes (was 15; 163 lines, silo 3,125), and
`ModularCurve.two_mul_index_le_sum_ordDiff_D_add_natCard_doubleCoset_of_lt_five` needs 134
(was 135; 789 lines, silo 47,865). So the differential corner above the `ordDiff` vocabulary is
now empty of cheap leaves: what is left of it is ModularCurve's own theorems, and the
`AlgebraicCurve` shelf holds only the small divisors/`evalFun` pieces and the 314-line
constant-field-extension node.

### 21.5 Found on the way: a pre-existing build break in `ResidueTheorem/RRAssembly.lean`

Building the one downstream consumer of `Differential/Different.lean`
(`Genus/HurwitzBound.lean`) failed in a module this wave never touched:

```
error: FLTForHuman/AlgebraicCurve/ResidueTheorem/RRAssembly.lean:100:16:
  a non-private declaration `AlgebraicCurve.Place.ord_sub_evalAt_pos` has already been declared
```

Root cause, and it is the §20 pattern again: `Defs/PlaceCalculus.lean:209` declares the
**public** `AlgebraicCurve.Place.ord_sub_evalAt_pos` (since `18c24b7`, 2026-10-04), and
`ResidueTheorem/RRAssembly.lean:100` declares a **`private`** theorem of the same name in the
same namespace (since `26aeae0`, 2026-10-23), with the same statement and the same proof. Lean
refuses a `private` declaration whose name is already a public constant, so `RRAssembly.lean`
has not elaborated since 2026-10-23 — the tree simply has not built that target.

It is **not** caused by this wave: a probe that imports only `RRAssembly`'s own import list
(none of this wave's modules) and then declares `private theorem ord_sub_evalAt_pos` reproduces
the error verbatim. The fix is the §20 one — delete the private copy and point its uses at the
public lemma — and it requires the same legacy-module upgrade of `RRAssembly.lean`
(`spec-pin`, deletion from `PORT_FILES`), so it is recorded here and not done in this wave.

## 22. The `RRAssembly` break, fixed (2026-10-27)

§21.5 recorded a pre-existing compile error and left it; it is now fixed, because it was the
same defect as §20's and it blocked the tree.

**The defect.** `ResidueTheorem/RRAssembly.lean:100` declared a `private theorem
ord_sub_evalAt_pos` inside `namespace AlgebraicCurve.Place`, shadowing the public
`AlgebraicCurve.Place.ord_sub_evalAt_pos` that `Defs/PlaceCalculus.lean:209` has carried since
2026-10-04. Lean refuses that — a private declaration may not take a name that is already a
public constant — so the module had not elaborated since 2026-10-23, when the private copy was
written (`26aeae0`). Nothing caught it: the module's statement wire is `spec/check_port.py`'s,
which reads text and never invokes Lean, so it kept reporting its cached
42 ok / 0 mismatch / 0 missing over a module that no longer compiled.

**The fix.** The private copy is deleted (28 lines, including its docstring) and its single use
keeps its spelling: `v₀.ord_sub_evalAt_pos hrat hg₀ htne` now resolves to the public lemma,
whose explicit arguments are the same modulo the section variable. The now-empty `namespace
Place … end Place` went with it, and the module header records why the pin's private helper
(pin 1973) is not copied here.

**Legacy-module standard.** This module had already been handed over (nine `spec-pin:` lines,
absent from `PORT_FILES`), so only the remaining items applied: silent build ✓ (8.8 s, no
warning), no build-time blow-up ✓, no machine tokens in declaration names ✓ (the pin's own
`rr_`/`wkc_` subject tags stay, as the header explains), `dedup.py` 0 clusters over 43
declarations ✓, `move_dead.py` 0 dead declarations ✓, no `sorry` ✓,
`check_port --force` **42 ok / 0 mismatch / 0 missing / 0 own** ✓.

**Verified downstream, which is how it was found.** `Genus/HurwitzBound.lean` — the module whose
build surfaced the error — now builds (3.8 s), and so do `RRAssembly`'s two importers
(`Canonical/PolarDifferentials.lean`, `Genus/RatFunc.lean`).

**Recorded negative.** The private copy's proof was byte-for-byte the public lemma's, so no
mathematics was lost; and the clash was invisible to the statement checker by construction, which
is the one hole in the "checked, not trusted" story: a module can pass the text wire and still not
compile. Only a build of the module (or of a target above it) closes that hole.
