# SET MC-7 — M1, the constant reduction on X₁/X_H and its two Hecke correspondences

**Status: scoped (2026-10-27); the definition wave is landed; three worker orders are
dispatched.** This is the `ModularCurve` ready shelf's story **M1** taken out of
[TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) and scoped to the row, with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). It was
the shelf's **MC-7**, the largest and last-gated of the seven orders (2,755 silo / ≈2,570 net);
after the work below it is **three independent orders of ~150–850 lines each**, because the
definition gate is landed and the pin's shared engine is already in the port, private, behind a
binder mismatch (§3).

The shelf figures it starts from are the corrected ones; the only instrument defect left in the
MC block was MD-001, and **MD-001 is closed by this brief** (§0). Three findings changed the
shelf's plan and are the reason this brief exists:

1. the `ModularCurve_QExpReductionModL` definition gate (26 decls / 295 lines) is **landed**
   as a new wired module, `ModularCurve/Defs/QExpReductionModL.lean` (§2);
2. the second half of the gate — `CuspForm_Gamma1HeckeOperators`' `mdifferentiable_heckeU`,
   `mapGL_apply`, `isUnit_wt`, `det_mod` (32 lines) — is **already in the port** under the H2
   reconciliation namespaces, so **M1's gate was 295 lines, not 327**, and 934 has no gate at
   all (§0.2);
3. the pin's `Forms`…`end Gauss` block of the 953 row is **byte-identical** to the same block of
   `S_…_regularProlongation_…`, which the port already transcribes (privately) in
   `ModularCurve/X1/QExpRegularProlongation.lean` — so 953 is not a 953-line row either (§3).

| figure | this read (instrument) | this read (corrected, §0.1) |
|---|---:|---:|
| `ModularCurve` ready rows | 26 / 8,704 | **25 / 8,668** |
| `ModularCurve` leaves | 34 / 7,331 | 34 / 7,331 |
| `ModularCurve` demand | 185 / 81,780 | 185 / 81,780 |
| `ModularCurve` withheld (FR-0044) | 2 / 610 | 2 / 610 |
| ready, all namespaces | 86 / 20,230 | 86 / 20,059 |
| leaves, all namespaces | 296 / 72,205 | 296 / 72,205 |
| `needed [F terminal]` | 1,019 / 404,826 | **1,021 / 405,187** |
| frontier F | 1,389 / 721,606 | 1,387 / 721,245 |
| `--selfcheck` | **PASS** (MD-001 closed) | — |
| **M1 rows** | **3 / 2,755** | 3 / 2,755 |

## 0. The read, and the MD-001 close

Canonical, as the recipe requires:

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc7.json
python3 frontier.py --selfcheck
# the corrected read: the two live markers left in the MC block's neighbourhood
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mc7-corrected.json
```

**MD-001 was closed before the read.** `ModularCurve/X1/IntegralityJqNModC.lean` carried two
`spec-pin:` lines (64, 68) for `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` — a row
the module's own prose says is *not ported there*. The two lines are deleted (the pin citations
stay as the deferral record), which is the correction
[spec/METADATA-ISSUES.md](../../spec/METADATA-ISSUES.md) MD-001 prescribes, and the registry
entry is marked resolved. The edit is a header edit: the module's `check_port` is still
**3 ok / 0 / 0**, and no Lean was rebuilt for it.

What the close moves, measured on the same tree:

- `--selfcheck` goes from one live source claim to **PASS** (`source tier covered by name
  tier`), and the frontier drops the node: **1,390 → 1,389 nodes, 721,642 → 721,606 raw**;
- `needed [F terminal]` **1,018 / 404,790 → 1,019 / 404,826** (+1 node / +36 lines: the row's
  own `S_` file);
- the instrument's MC shelf goes **26 / 8,748 → 26 / 8,704**: the false-ready 80 row
  (`exists_sum_smul_eq_of_qExpansion_coeff_mem`) leaves because its premise 36 is no longer read
  ported, and the 36 row (`exists_sum_smul_eq_of_isIntegralQExp_gamma1`, 36) enters as a plain
  ready row;
- the **corrected** MC shelf is unchanged at **25 / 8,668** — the 36 was never in the corrected
  shelf, and the 80 row leaves it in both readings.

**The three M1 rows are unchanged, and they are the three largest rows of the MC block**:

| row (`ModularCurve.` dropped) | silo | prem | lev (cone / project) |
|---|---:|---:|---:|
| `exists_constantReduction_pic0Map_eq_reductionQExpModL` | 953 | 3 | 1 / 4 |
| `coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne` | 934 | 3 | 1 / 2 |
| `coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd` | 868 | 2 | 1 / 2 |

All three are `needed = 1`, `premises_pruned = 0`, `leaf = false`, and each cites the other two
nowhere: **the three orders are independent** (§5).

**The withheld block is the same two MC rows / 610 silo** (`moduleFinite_and_free_padicInt_tateModule_jH`
327, `moduleFinite_padicInt_tateModule_jOne` 283, both on `Pic0.abelJacobiCard_genus`): the prunable
subject's consumers, deferred to [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md). The MC
block has no leaf in this set; the 34 leaves / 7,331 are the shelf's second programme and are not
cut here.

### 0.1 The corrected read, and one figure that does not reproduce

The correction set is now **two** markers — MD-001's node is out of `F` by the wire close:

| node | silo | marker | treatment |
|---|---:|---|---|
| `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` | 261 | last-name shadow (`CuspForm` twin in `ModularForms/WeightOne/Gamma1IntegralBasis.lean`) | unport for the read; the `ModularForm` chain is the C2 §9 subject |
| `AlgebraicCurve.weilReciprocity` | 100 | name shadow (FR-0047) | unport for the read; SET 9's general row |

**An instrument note, recorded because a brief must say which read produced its figure.** The
shelf's corrected `needed` line reads 1,020 / 404,926. The documented three-`--unport` command
does **not** produce it on the tree the shelf read (verified by restoring the MD-001 wire and
rerunning): it produces **1,021 / 405,187**, i.e. the 261-line shadow's own node is in `needed`
when it is unported, and the shelf's figure counted it as already unported. Every other shelf
line reproduces exactly — ready 86, leaves 296 / 72,205, MC ready 25 / 8,668, MC demand
185 / 81,780, frontier 1,387 / 721,245. The figures in this brief's table are the reproduced
ones; the MC block is unaffected in either reading.

### 0.2 The definition-vocabulary audit, corrected twice

The shelf's §0.2 priced the gate as `QExpReductionModL` 295 + `Gamma1HeckeOperators` 32 = **327**.
Two corrections:

- **`QExpReductionModL`: landed.** The whole pin `Def_` module is now
  `ModularCurve/Defs/QExpReductionModL.lean`, wired, built and checked (§2). 338 pin lines, 29
  declarations, `29 ok / 0 / 0`.
- **`Gamma1HeckeOperators`: not a gate.** The four "missing" declarations are the H2
  reconciliation pair, all present and public in the port:

  | pin `Def_` declaration | port declaration | note |
  |---|---|---|
  | `mdifferentiable_heckeU (hf) (k) (p)` | `ModularForm.HeckeGamma1.mdifferentiable_heckeU` (`ModularForms/HeckeAnalytic.lean`) | the pin's *section-variable* shape, beside the wrapper copy |
  | `mapGL_apply (g) (i) (j)` | `ModularForm.HeckeRepresentatives.mapGL_apply` (`ModularForms/Defs/HeckeRepresentatives.lean`) | `@[simp]`, same statement |
  | `isUnit_wt (hp) (hpN) (x)` | `ModularForm.Level.isUnit_wt` (`ModularForms/Level/Diamond.lean`) | **weaker**: `hp : p.Prime` dropped (it is a `Fact p.Prime` instance there), so it applies |
  | `det_mod (γ) (hγ)` | `ModularForm.Level.det_mod` | Γ₀-membership form |

  `ModularForms/Defs/Gamma1HeckeOperators.lean`'s own header records the deferral ("their
  reconciliation is phase H2"); H2 has landed. **So M1's definition gate is 295 lines, and the
  934 row — the one that imports `Def_CuspForm_Gamma1HeckeOperators` — needs no new definition.**

**What the 953 row still needs from the definition layer is only what §2 landed**: the headline's
statement names `ReductionInputsQExpModL`, `placeReductionQExpModL`, `reductionQExpModL`
(`Defs/QExpReductionModL.lean`), and `ConstantReduction` (`AlgebraicCurve/ConstantReduction.lean`,
ported whole).

### 0.3 The pricing, per row

`port_advise` per row (single-row runs; the aggregate `port_plan` figure of the shelf — M1
2,243 net rows + 327 gate — is superseded by the per-row numbers below because the gate is
landed and 953's engine is reused):

| row | target decls | already in the port | prelude lines | `port_advise` note |
|---|---:|---:|---:|---|
| 953 | 92 | 23 | ≈160 | the `gaussRing`/`IsInt` block (`X1/FunctionFieldResidue.lean`, `QExpDeuring`), `coeffEmb_intSeriesC`, `coeffEmb_injective`; `laurentBaseChange_le` is **private** in `X1/QExpRegularProlongation.lean` and is not needed by this row (§3) |
| 934 | 92 | 16 | ≈139 | `mem_intFormRatiosC_of_mem` (`X1/AtkinLehnerExchange`, 48 lines), `conj_mem_Gamma1`, `D12top`/`N12top`, the `P4`/`P6` block, `coeffMap_injective` |
| 868 | 99 | 13 | ≈78 | `A12`/`B12`/`isIntegralQExp_E4`/`_E6`/`xq_mem`/`intSeriesC_ne_zero_of_constantCoeff` (`X1/FunctionField`, `XH/Relrank`), `twistFun` = `ModularCurve.qTwistFun` (`Defs/Twist.lean`, binder spelling) |

**The 934/868 shared block is 14 names.** The pin proves it twice; **the port writes it once**:
the five generic differential lemmas (`pullbackAlong_id`, `separableAlong_algEquiv`,
`trace_one_along_algEquiv`, `traceAlong_algEquiv`, `correspondence_algEquiv_id`) are landed in
`AlgebraicCurve/Differential/AutTrace.lean` (97 lines, real proofs, deliberately tier 3 until the
934 row lands — [WORKORDER-MC7d](WORKORDER-MC7d-rectify-engine-homes.md) D3 re-wires it), the
sixth (`pullbackAlong_pullbackAlong`) was already in the port, and the `P4`/`P6`/E₄-E₆ block is
imported from `XH/Relrank.lean` / `X1/FunctionField.lean`. **The set's rule: we do not duplicate
mathematics.** Packaging duplication (a re-export, an `open`, a notation) is fine; a second proof
of the same lemma is not; and a *facade* — a pin-shaped re-declaration delegating to a
differently-spelled port declaration — is not packaging either. Where the port's spelling of a
theorem is weaker than the pin's (a hypothesis the pin's proof does not use), the port keeps the
one declaration and the wire records the difference with an `own:` row (manager-written), instead
of growing a second declaration to match the pin's words. MC-7d is the audit that keeps this
true; the port's pre-existing `P4`/`P6` double spelling is its D4.

Three documented false negatives to carry (recipe §3): `port_advise` is name-anchored (a port
copy under another name reads as new), it does not read mathlib, and it is statement-anchored
(a port theorem with *weaker* hypotheses is invisible). The third is live here: `Level.isUnit_wt`
is weaker than the pin's, and `qTwistFun` is `twistFun` under another name.

## 1. The three rows, and what each is

**953 — `exists_constantReduction_pic0Map_eq_reductionQExpModL`.** Construct the
`ConstantReduction A FF Fb` for `FF = laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ Γ)`
from the reduction input `h : ReductionInputsQExpModL A Γ`: its `placeMap` is
`placeReductionQExpModL h`, its `pic0Map` is `reductionQExpModL A Γ`, and its residue is the
coefficientwise `coeffMap (IsLocalRing.residue A)`. The proof is the pin's `PlaceMap` section
(`S_:788–930`, ~145 lines): a Gauss valuation ring on `FF`, its residue map onto
`qExpFunctionFieldC kk Γ`, and the place-map/`Pic0` compatibility through the closure of
integral principal divisors. Pin `S_` 953 lines, 92 declarations; the `Forms`…`Gauss` block
(131–786) is the *shared* engine of §3.

**934 — `coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne`.** For
`f : CuspForm Γ₁(M) 2` with `coeffMap ι₀ (diffQExp ω) = qExpansion f`: the q-expansion of the
diamond correspondence `correspondence (diamondAutBar M d).toAlgHom id ω` is
`qExpansion (CuspForm.diamondLinOne M 2 d f)`. The proof (pin `R1G1Hd`) builds the differential
`ω = w · D x₀` (`x₀ = E₆²/E₄³`), transports `diamondAutBar` along the base change, uses the
Rankin–Cohen `exists_RCtop` to replace `qEuler (qB/qA)` by `qEuler`-free data, and cancels
`QQ ⇑H * (qA*qA)`. The assembly is `main` (`S_:790–906`), 95 declarations.

**868 — `coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_not_dvd`.** The
coefficient identity for the β-correspondence at `ℓ ∤ M`: `diffQExp (correspondence heckeBetaOneBar
heckeAlphaOneBar ω).coeff n = diffQExp ω.coeff (n*ℓ) + ℓ * (if ℓ ∣ n then diffQExp
(correspondence diamondAutBar id ω).coeff (n/ℓ) else 0)`. The proof (pin `R1G1H1`) is the trace
computation over the `ℓ` embeddings `emb`, with `rootSum`/`twist` on the coefficient side and the
`key_identity`/`coeff_identity` assembly at the end; 105 declarations, **no definition gate**.

## 2. The definition wave (landed)

**`ModularCurve/Defs/QExpReductionModL.lean`** (new, 365 lines) transcribes
`Definitions/Def_ModularCurve_QExpReductionModL.lean` whole — the `Spec` vocabulary
(`IsLaurentPlaceReduction`, `laurentIntegralPrincipalDivisors`,
`LaurentPrincipalGeneratedByIntegral`, `LaurentReductionInputs`), its `SpecLemmas`, the `Descent`
block (`laurentReductionDiv`, `laurentReductionDegZero`, `laurentReductionPic0`), the `Total`
block (`laurentReduction`, `laurentReduction_eq/_mk/_of_not`), the `Uniqueness` block
(`IsLaurentPlaceReduction.eq_or_const_of_agree`, `eq_of_agree`, and the pin's **private**
`int_eq_zero_of_forall_dvd'` — the "private helper" the shelf priced separately, written here
with its row as the recipe asks), and the character-ℓ specialisation
(`IsPlaceReductionQExpModL`, `ReductionInputsQExpModL`, `placeReductionQExpModL`,
`isPlaceReductionQExpModL_placeReductionQExpModL`, `reductionQExpModL`,
`reductionQExpModL_mk/_of_not`).

Its own wire is one line, `spec-pin: Definitions/Def_ModularCurve_QExpReductionModL.lean`; it
imports `ModularCurve.X1.Defs`, `AlgebraicCurve.Defs.Place`, `AlgebraicCurve.Defs.Divisor`. Gates:

- `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` → **silent** (the pin's
  `dif_pos`/`dif_neg`/`if_neg` spellings were replaced by `dite_eq_left`/`dite_eq_right`/
  `ite_eq_right`; zero warnings);
- `lake build` under `flock` → **34 s**, `.olean` present;
- `python3 spec/check_port.py --force FLTForHuman/ModularCurve/Defs/QExpReductionModL.lean` →
  **29 ok, 0 mismatch, 0 missing, 0 own, 0 kw**;
- the pin's `set_option synthInstance.maxHeartbeats 400000` is **not** transcribed; the pin's
  trailing `example` is kept as a non-declaration check.

The home is `Defs/` rather than the shelf's "both the defs and the row in one new
`ModularCurve/QExpReduction.lean`" because the module is one `Def_` transcription and its
vocabulary (`ReductionInputsQExpModL`) is read by other pin files of the column
(`S_…_isGood_isPlaceReductionModL`, `S_…_exists_constantReduction_pic0Map_surjective`); a `Defs/`
home is the import-direction-correct place for shared definition surface, and the row's home is
then free to be the subject module (§4). The wire does **not** name those other pin files — a
`spec-pin:` for a source this module does not transcribe is exactly MD-001's failure mode.

**No promotion, no migration** was needed for the definition wave. The two private helpers the
shelf listed (17 lines) are inside the transcription: `int_eq_zero_of_forall_dvd'` (4 lines,
private, as in the pin) and `span_stable` (13 lines) — the latter belongs to `PeriodOf`, is **not**
M1's, and stays with MC-4.

## 3. The 953 engine: one copy, and the pin's two spellings of it

This is the finding that reprices 953, and the one that produced the set's no-facade rule. The
pin's 953 `S_` file, lines **131–786** (`section Forms` … `end Gauss`), is **byte-identical** to
the same block of `S_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC.lean`
(`diff` = 0 lines). The port already has that block, twice, at two different spellings:

- `ModularCurve/X1/FunctionFieldResidue.lean` (`QExpDeuring`, public): the `Coeff` layer and the
  `gaussRing`/`exists_witness`/`wit`/`resL`/`resHom`/`exists_frac_form` engine, stated for an
  arbitrary `Γ` — **without** the pin's `hT`. That is not a deviation: the pin's *sibling* file
  `S_…_transcendental_finiteDimensional_qExpFunctionFieldC_residueField` defines `gaussRing`
  without `hT` too, so the pin itself spells this engine two ways;
- `ModularCurve/X1/QExpRegularProlongation.lean` (681 lines, 47 `private` declarations): the
  `Lam`/`homSpan`/`IsFrac` fractional-form layer, and the `resF` assembly
  (`resF`, `coe_resF`, `resF_ne_zero_iff`, `ker_resF`, `resF_surjective`, `resF_algebraMap`,
  `exists_smul_mem_resF`, `resHom_mem`, `resHom_ι`, `ι_mem_gaussRing`,
  `inv_mem_gaussRing_of_resHom_ne_zero`, `coe_smul'`, `exists_smul_mem_gaussRing`) — again at the
  port's `Γ` spelling. The pin's `hT` is an **unused parameter of the definition**
  (`gaussRing A hT`'s carrier does not mention it); in the port's proof it is genuinely
  unnecessary, so the port's statement is the *weaker* form, which is the allowed direction.

**Why no facade.** The first plan for this set was a `ModularCurve.GaussQExp` module re-declaring
the pin's `hT`-shaped statements as one-line delegations to the `Γ`-shaped engine, so that the
953 wire would diff cleanly. That is a facade, and it is withdrawn: it adds 13 declarations to the
port whose only content is a spelling, and it would silently become the de-facto interface. The
rectified plan is one copy of the mathematics at the port's spelling plus wire metadata:

| piece | home | copies |
|---|---|---|
| `Coeff` + `gaussRing`/`resL`/`resHom`/`exists_frac_form` | `X1/FunctionFieldResidue.lean` (public) | 1 |
| `resF` assembly | **new** `X1/GaussResidue.lean` (public, tier 3), moved out of `QExpRegularProlongation.lean` | 1 (MC-7a moves it; MC-7d D1 verifies) |
| `Lam`/`homSpan`/`IsFrac`/`ofPS`/`exists_frac_form_mem` | **the same new module** (private: the pin's 4th-conjunct argument), moved out of `QExpRegularProlongation.lean` | 1 |
| the 953 row's `PlaceMap` section | **new** `ModularCurve/ConstantReductionQExp.lean` | 1 |

**Why the chain moves too.** `resHom_mem` — and therefore `resF`'s codomain restriction — needs
the *fourth conjunct* of the pin's `exists_frac_form` (`ϖ u₀ / ϖ w₀ ∈ qExpFunctionFieldC kk Γ`),
which the public `QExpDeuring.exists_frac_form` (the sibling file's 3-conjunct spelling) does not
have. `exists_resHom_eq` proves the *opposite* containment (`Fb ≤ range resHom`), so it cannot
substitute for it. The port's proof of the 4th conjunct is `exists_frac_form_mem`, built on the
`Lam`/`homSpan`/`IsFrac` chain — so the chain and the assembly are one dependency block and move
together; splitting them would either duplicate the chain or put the assembly below its own proof.
(Found by MC-7a's worker while the order ran; it is the reason the shared module is bigger than
this brief first priced.)

**The surface-gate experiment, for the record.** Dropping `private` on the 47 declarations and
running `check_port --force` gives **13 ok / 37 mismatch**; all 37 are `gaussRing A Γ` (port)
against `gaussRing A hT` (pin). The recipe classifies that as "the pin's own prelude copy
re-spelled in the module" → keep private, which is why the block stayed private and is now being
*moved* (not promoted in place).

**What the 953 module declares and what the wire says.** The `PlaceMap` section's four
intermediate declarations mention `gaussRing A hT` in the pin's text
(`coe_ne_zero_of_resHom_ne_zero`, `resF_inv`, `exists_unit_of_mem_closure`, `mapDomain_placeMap`);
the port states them with `gaussRing A`, so the 953 wire reports `MISMATCH` and the manager
records four `own:` rows with the reason (the pin's `hT` is unused). The `gaussReduction`
structure, `pic0Map_gaussReduction`, `residue_gaussReduction` and `main` are typed through
`ConstantReduction`/`placeReductionQExpModL` and should be `ok`; the headline is the wrapper's
verbatim.

**Two pin declarations the port does not have and the order does not need.** `resRange`,
`div_intSeriesC_mem`, `qExpFunctionFieldC_le_resRange` (pin `S_:715–771`, ≈57 lines) are the
pin's *alternative* route to `resF_surjective`; the port proves it directly from
`exists_resHom_eq`. They are not ported, and the substitution is recorded here rather than
re-derived.

**The wire trap.** `QExpRegularProlongation`'s wire names the three regular-prolongation
`S_`/`Thm_` files. The 953 `S_` file contains the same block, but adding its `spec-pin:` to that
module would read the **953 headline** as ported — a new MD-001. `GaussResidue.lean` is
therefore unwired, with the reason in its header; MC-7d D3 re-wires `AutTrace` (not
`GaussResidue`) once the corresponding row has landed.

## 4. Homes and the import direction

The recipe's three-step check (premises → their port modules → a module above all of them),
confirmed against each pin proof's subject:

| order | premise modules the home must be above | home | why |
|---|---|---|---|
| **953** | `RingTheory/PowerSeries/Saturation.lean`, `AlgebraicCurve/Place/ConstantFieldExtension.lean`, `ModularCurve/X1/FunctionFieldBaseChange.lean`; plus the def module, `AlgebraicCurve/ConstantReduction.lean`, `ModularCurve/X1/FunctionFieldResidue.lean`, the moved `X1/GaussResidue.lean` | **new** `ModularCurve/ConstantReductionQExp.lean` (the row) + **new** `X1/GaussResidue.lean` (the shared assembly, moved) | the subject is the Gauss residue dictionary and its place reduction on `FF`; no existing module is above `Place/ConstantFieldExtension` *and* imports the engine |
| **934** | `ModularForms/QCoeffLevelOne.lean`, `ModularCurve/X1/FunctionFieldBaseChange.lean`, `AlgebraicCurve/IsCurveOver/Transcendental.lean`; plus `ModularForms/Defs/Gamma1HeckeOperators.lean`, `ModularForms/Level/Diamond.lean`, `ModularCurve/X1/{Defs,DiamondAut,DiamondLift,AtkinLehnerExchange}.lean`, `ModularCurve/Defs/HeckeDifferential.lean`, `AlgebraicCurve/Differential/{PushPull,CorrespondenceRegular}.lean` | **new** `ModularCurve/X1/DiamondCorrespondence.lean` | the diamond correspondence on `x1FunctionFieldBar`; `X1/` is its subject and nothing there is above `QCoeffLevelOne` |
| **868** | `ModularCurve/X1/HeckeDegree.lean`, `ModularCurve/X1/AtkinLehnerExchange.lean`; plus `ModularCurve/X1/{Defs,FunctionField}.lean`, `ModularCurve/Defs/{Twist,HeckeDifferential}.lean`, `AlgebraicCurve/Defs/Correspondence.lean`, `AlgebraicCurve/Differential/{PushPull,TraceDiff}.lean`, `AlgebraicCurve/Differential/ConstantFieldExtension.lean` | **new** `ModularCurve/X1/HeckeCorrespondence.lean` | the β/α correspondence at `ℓ ∤ M`; the two premise modules are leaves of `X1/`, and the home is the `X1/` correspondence subject |

All three homes are new modules: cascade-free, one file each, **disjoint**, so the three orders
run concurrently (only the build lock is shared). No legacy `PORT_FILES` module is touched — the
shelf's two M1-adjacent legacy migrations belong to M3-185 (`TateSlots/CoefficientFormulas.lean`)
and M8-22 (`X1/Structure.lean`), not to M1. No promotion and no migration in any order.

## 5. The three orders

| order | row | home | silo | est. new lines | gate |
|---|---|---:|---:|---:|---|
| **MC-7a** | 953 | `ModularCurve/ConstantReductionQExp.lean` + the moved `X1/GaussResidue.lean` | 953 | **≈350–450** (`PlaceMap` ≈145 + the moved assembly ≈150 + headline) | def wave landed (§2) |
| **MC-7b** | 934 | `ModularCurve/X1/DiamondCorrespondence.lean` | 934 | **≈800–900** | none (§0.2) |
| **MC-7c** | 868 | `ModularCurve/X1/HeckeCorrespondence.lean` | 868 | **≈750–850** | none |

Each order's workorder is beside this file:
[WORKORDER-MC7a-constant-reduction.md](WORKORDER-MC7a-constant-reduction.md),
[WORKORDER-MC7b-diamond-correspondence.md](WORKORDER-MC7b-diamond-correspondence.md),
[WORKORDER-MC7c-hecke-correspondence.md](WORKORDER-MC7c-hecke-correspondence.md).

**MC-7a traps.** (i) The pin's `PlaceMap` section uses `gaussRing A hT`/`resHom A hT`/`resF A hT`
throughout; the port's engine is `Γ`-shaped. Transcribe against the port's spelling (drop the
unused `hT` argument), **not** by re-declaring pin-shaped statements — the no-facade rule of §3.
(ii) The `resF` assembly must be *moved* out of `QExpRegularProlongation.lean` into
`X1/GaussResidue.lean` and the old module must import it in the same touch: two copies of that
block is exactly what MC-7d D1 will fail. (ii) Do **not** copy the
`Forms` block or the `resRange` block (§3); do **not** add a `spec-pin:` for the 953 `S_` file to
`QExpRegularProlongation`. (iii) `exists_unit_of_mem_closure` and `mapDomain_placeMap` are the
real content: the closure induction is over `laurentIntegralPrincipalDivisors`, and the
`exists_transcendental_finiteDimensional_laurentBaseChange` + `Place.mem_range_algebraMap_…`
pair is what turns an ord-0 element of `FF` into an `A`-constant. (iv) `mapDomain_placeMap` in the
pin carries `set_option maxHeartbeats 1600000 in`; the project cap is 4,000,000 and **no module
carries `set_option maxHeartbeats`** — read the probe ladder before touching it. (v) The
`example` tail of the def module is not to be copied.

**MC-7b traps.** (i) The pin sets `synthInstance.maxHeartbeats 1600000` and `maxHeartbeats
3200000`; neither is transcribed. (ii) `P4`/`P6`/`D12top`/`N12top`/the `P4`-coefficient block and
`isIntegralQExp_E4`/`E6` are in the port (`X1/FunctionField`, `XH/Relrank`); `port_advise` says
which by name, and the local copies must only be written where the port's binder differs.
(iii) `x1FunctionFieldBar`'s `IsCurveOver`/`CharZero` instances are *local* in the pin
(`isCurveOver_bar`, `charZero_bar`, `haveI` in `main`); keep that discipline. (iv) The two
`AutTrace` sextets of 934 and 868 are the same 84 lines; each module keeps its own copy (§0.3).
(v) `CuspForm.diamondLinOne`/`exists_isDiamondLift_of_coprime`/`coe_diamondLinOne_apply` are in
`ModularForms/Defs/Gamma1HeckeOperators.lean` / `ModularForms/HeckeNebentypus.lean`; the
`diamondAutBar`/`isBaseChangeAutOf_baseChangeAut` API is `X1/DiamondLift.lean`.

**MC-7c traps.** (i) `twistFun` is the ported `ModularCurve.qTwistFun` (binder spelling);
`twist` is not (`LaurentSeries R →ₐ[R]`); check the two before restating. (ii) The pin's
`emb_injective` name collides with `AutomorphicForm.IwasawaWeyl.emb_injective` — a different
statement (`port_advise` reports it as a binder-skeleton pointer); keep it in the order's own
namespace. (iii) `A12`/`B12`/`xq_mem` are `JOneES.JOneESRat`'s in `X1/FunctionField.lean` —
*ported*, so import, do not restate, unless the order's `Γ`-binder is the pin's explicit one.
(iv) The `EE`/`ιE`/`ALData`/`sigmaTwist`/`emb` block is new mathematics, not a port copy; it is
the trace over the `ℓ` embeddings and the part to give wall time. (v) `rootSum`/`sum_zpow_pow`
need `IsPrimitiveRoot`; the pin's `zu`/`zu_pow` are the units bridge.

## 6. Gates, per order

As the recipe §6, and the two orders that are *not* the manager lane get the full list in their
workorder:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every added public
   declaration `ok` (private helpers are exempt and stay private where the wire has no statement
   for them);
2. `#print axioms` on the headline → `[propext, Classical.choice, Quot.sound]`;
3. the module's own `lake build` under `flock` and `timeout`, silent at the project cap; no
   `set_option maxHeartbeats`, no `synthInstance.maxHeartbeats` transcribed;
4. `dedup.py` / `move_dead.py` on the module; the 934↔868 84-line cluster is the recorded
   exception (§0.3);
5. zero warnings, no `sorry`/`admit`/`axiom`/`native_decide`, no `spec/decl_markers.tsv` row
   written by a worker;
6. the module's `spec-pin:` block gains exactly its own `Thm_` wrapper and `S_` copy — and
   nothing else (§3's wire trap).

**The consumer zone for the set** (`spec/` zone, real cross-module composition, no `#check`s):
the 953 `gaussReduction` composed with the ported `ConstantReduction` API (`pic0Map_mk`,
`ord_algebraMap`, `mapDomain_mem_principal`), and the 868 coefficient identity composed with the
934 differential correspondence at `d = 1` (`diamondLinOne M 2 1` and the `ℓ = 1` specialisation
of the β identity). Its error count is the deliverable metric.

## 7. Reproduce, and the measured numbers

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc7.json
python3 frontier.py --selfcheck
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json \
  --unport ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast \
  --unport AlgebraicCurve.weilReciprocity > build/mc7-corrected.json
python3 port_advise.py --nodes ModularCurve.<row> --json build/mc7-<row>.json && python3 port_plan.py --json …
python3 twin_scan.py --node ModularCurve.<row>
cd ../lean && python3 spec/check_port.py --force FLTForHuman/ModularCurve/Defs/QExpReductionModL.lean
```

1. **What the set consumes**: the shelf's corrected 25 rows / 8,668 is unchanged; M1 is 3
   rows / 2,755 silo. The definition wave actually landed is **338 pin lines** (365 port lines,
   29 declarations); the shelf's 327-line gate was 295 + 32, and the 32 is **already ported**, so
   the set's gate is 295 and 934/868 have none. The row work is re-estimated at ≈2,000–2,300
   lines over three orders (the shelf priced M1 at 2,243 net + 327 gate).
2. **The read it starts from** (measured, after MD-001's close): instrument `needed`
   **1,019 / 404,826**, 86 ready / 20,230, 296 leaves / 72,205, MC **26 / 8,704**, MC demand
   **185 / 81,780**, frontier **1,389 / 721,606**, `--selfcheck` **PASS**; corrected `needed`
   **1,021 / 405,187**, 86 / 20,059, MC **25 / 8,668**, frontier **1,387 / 721,245**.
3. **What the three orders left — measured (2026-10-27, after all three landed).** The set
   consumed exactly its own rows and nothing else:

   | figure | before | after | delta |
   |---|---:|---:|---:|
   | instrument `needed` | 1,019 / 404,826 | **1,016 / 402,071** | −3 / −2,755 |
   | corrected `needed` | 1,021 / 405,187 | **1,018 / 402,432** | −3 / −2,755 |
   | ready, all namespaces (instrument) | 86 / 20,230 | **83 / 17,475** | −3 / −2,755 |
   | corrected ready | 86 / 20,059 | **83 / 17,304** | −3 / −2,755 |
   | `ModularCurve` ready shelf | 26 / 8,704 | **23 / 5,949** | −3 / −2,755 |
   | corrected MC shelf | 25 / 8,668 | **22 / 5,913** | −3 / −2,755 |
   | `ModularCurve` demand | 185 / 81,780 | **182 / 79,025** | −3 / −2,755 |
   | frontier F | 1,389 / 721,606 | **1,392 / 724,361** | +3 / +2,755 |
   | leaves | 296 / 72,205 | 296 / 72,205 | 0 |

   The three rows that left are exactly the three this set cut (`exists_constantReduction_…`,
   `coeffMap_diffQExp_correspondence_…`, `coeff_diffQExp_correspondence_…`); the frontier gained
   the same three nodes / 2,755 lines, i.e. **the three are now ported** and their demand is now
   the port's.  **No new row became ready because of the set** — the forecast's successors
   (the `…pic0Map_surjective` / `…_isGood_isPlaceReductionModL` pair behind 953, and the `_of_dvd`
   twin of 868) are still not ready on that graph; the next pass reads them.

   The set's own deliverables: **four new modules** (`AlgebraicCurve/Differential/AutTrace.lean`
   97 lines; `ModularCurve/Defs/QExpReductionModL.lean` 365; `ModularCurve/X1/GaussResidue.lean`
   533; `ModularCurve/X1/DiamondCorrespondence.lean` 778; `ModularCurve/X1/HeckeCorrespondence.lean`
   738; `ModularCurve/ConstantReductionQExp.lean` 274 — six files, the def wave and five row/engine
   modules), **one landed module shrunk** (`X1/QExpRegularProlongation.lean` 681 → 228 after the
   single-copy move), **one wire closed** (MD-001), and a `spec/` consumer zone
   (`spec/ModularCurveMC7DefConsumer.lean`, 0 errors).  Checker verdicts: 29 ok (def), 71 ok
   (934), 74 ok (868), 5 ok + 4 `own` (953), 3 ok (`QExpRegularProlongation`); every module
   silent, zero warnings, **no heartbeat and no linter option anywhere** (the three worker
   suppressions were removed and the 14 warnings they hid fixed: FR-0054).

## 8. What this set does not do

- **The 80/36/261 chain.** MD-001 is closed (the wire is gone, the 36 is a plain ready row); the
  80 row and the 261 `ModularForm` basis theorem are not cut — the 261 is the C2 §9 subject
  (≈4.8k raw) and the 80 sits behind it.
- **The withheld Tate-module pair (610 silo)** — `abelJacobiCard_genus` + the `TateModule`
  definition layer; the T1/T2 plan of [TOPIC-padic-tate-module.md](TOPIC-padic-tate-module.md).
- **The leaves block (34 / 7,331)** and its definition gates (`PeriodHomPair`, `Pic0Congr`,
  `ComplexPlaceDictionaryOf`, `X0ModL`) — the shelf's second programme.
- **No promotion, no legacy migration, no tree build.** The one promotion experiment (§3) was
  reverted; the only tree edits of the set are the new def module, the three row modules, and
  MD-001's two deleted `spec-pin:` lines.
