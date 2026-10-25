# The `TS` field generality — a definition-layer refactor, and the ground for the any-field `Φ_p` splitting

Record of the refactor that landed on 2026-10-25 as the **ground** for WORKORDER-GS1
([modularCurve/WORKORDER-GS1-phigen-splits-any-field.md](../topics/modularCurve/WORKORDER-GS1-phigen-splits-any-field.md)),
i.e. for the two remaining char-`p` splitting nodes. No new mathematics: the whole point was to
stop the port from carrying two spellings of one object, so that the char-`p` module would be an
import rather than a 90-line duplicate.

## 1. The defect

The pin states `TS` **twice**:

| spelling | pin locus | binders |
|---|---|---|
| `qExpand K e (qTwist u (coeffEmb K jq))` | `S_ModularCurve_functionFieldGeneration.lean` 39–101 and the FFG carriers | `[Field K] [Algebra ℚ K]` |
| `qExpand K e (qTwist u (jqModC K))` | `S_ModularCurve_PhiGen_splits_prime_of_isPrimitiveRoot.lean` 33–122 (and its at-slot twin) | `[Field K]` |

The port had only the narrow one (`Defs/TS.lean`), and the narrowing showed up as recorded drift:
`Degree/JqCyclotomicConjugates.lean`'s `phiAtSeed_TS_eval`/`_symm` carried two `own:` rows in
`spec/decl_markers.tsv` whose reason was exactly "the port's `TS` carries an `Algebra ℚ K` binder
the pin's does not". Worse, the char-`p` roots API's `roots_prime_at_slot_nodup` needs
`TS_injective` at `[Field K]`, which the port could not offer — so a faithful port of those nodes
would have had to re-copy the whole `TS` block (the pin's lines 33–192, ≈90 lines).

`coeffEmb K jq = jqModC K` (`Defs/JqCoeff.lean`) is the bridge between the two spellings, so the
general statement is strictly better: every narrow use is its instance.

## 2. What changed

1. **`Defs/TS.lean` generalised.** `TS K e u := qExpand K e (qTwist u (jqModC K))` over
   `[Field K]`, with `TS_coeff_mul`'s RHS now `(jqModC K).coeff n` — i.e. the pin's char-`p` text
   verbatim. The three declarations whose *statement* mentions `coeffEmb`
   (`iota_jqN`, `qExpand_qTwist_notMem_range_qExpand`, `coeffMap_TS`) keep their `Algebra ℚ K`
   binder and their FFG pin text, in a `section AlgHom` / `section CoeffMapTS`. The module gained
   4 `spec-pin:` lines and **left `PORT_FILES`** (522 entries now), so its whole public surface is
   statement-diffed for the first time: `check_port.py` reads **15 ok / 0 mismatch / 0 missing /
   0 own**, every `TS` declaration matched to the pin's general field text at
   `S_..._splits_prime_of_isPrimitiveRoot.lean` lines 33–169 and the `ℚ`-algebra members to the FFG
   files. Build 4.3 s, silent.
2. **`coeffEmb_jq` moved down to the definition layer**, `Defs/JqCoeff.lean` (same name, same
   statement, statement-checked against `Theorems/Thm_ModularCurve_coeffEmb_jq.lean:7` — the
   wrapper's binder block, which the checker needs spelled *in the declaration*, not as section
   variables: the parser reads the text, so a section-variable binder block leaves the ported
   statement without binders and the diff fails). The copies this retired:
   `Degree/LaurentGlue.lean`'s public copy (its `spec-pin` line moved too; it keeps
   `coeffEmb_jqN`), `private` twins in `Analytic/CuspDichotomy.lean` and
   `Degree/JqCyclotomicConjugates.lean`, and the proofs of `Analytic/ANb.lean`'s `coeffEmb_jq`
   and `X1/FunctionFieldDegree.lean`'s `FIdxBC.coeffEmb_jqModC` (both now one-line instances).
   `dedup.py --tier name,shape` had confirmed the CuspDichotomy twin as a 5-line shape twin of
   the public lemma; the other three were name variants of the same statement.
3. **The two `own:` rows deleted.** With `TS` general, `phiAtSeed_TS_eval` and
   `phiAtSeed_TS_eval_symm` are stated at the pin's general binders (no `Algebra ℚ K`), so they
   are pinned, not exempt — `Degree/JqCyclotomicConjugates.lean` now reads **23 ok / 0 own**, with
   the char-`p` pin file added to its wire as the statement's source. That module also lost the
   now-definitional private helper `TS_one_eq_qExpand` (its four call sites are
   `rw [TS, qTwist_one_apply]`).

## 3. The cascade — 15 proof sites, and what they teach

Changing a definition's *body* is propositionally invisible and definitionally expensive: 15 sites
in 11 modules had relied on `TS` unfolding to a `coeffEmb`-shaped `qExpand`, and each needed
explicitly one of

- `rw [coeffEmb_jq]` where a hypothesis or goal was in the `coeffEmb` spelling and the `TS`
  lemma expected the `jqModC` one (the majority: `PhiGenSplits`, `FunctionFieldGeneration/{Spine,
  Generation, Descent, DegreeStep, SlotProduct, Nonmembership}`, `PhiSlotRoots`,
  `ModularPolynomialLeadingCoeff`, `Degree/Relfinrank`);
- `exact qExpand_TS …` where a `change` had asserted definitional equality of
  `qExpand K m (TS K n u)` with `TS K (m * n) u` (`Spine`);
- `omit [Algebra ℚ K] in` on three declarations whose statements mention only `TS`
  (`Defs/PhiAtSlot.roots_phiProd_conj_nodup`, `DegreeStep.range_map_eq_rUnit`,
  `SlotProduct.TS_congr'`) — the section instance became unused, and the port's silent-build rule
  has no other exit. `omit` must precede the docstring, not follow it.

Every module in the touched set was rebuilt individually: **0 errors, 0 warnings, no build-time
blow-up** (`Defs/TS` 4.3 s, `PhiGenSplits` 6.3 s, `Spine` 7.4 s, `SlotProduct` 47 s including its
own `#print axioms`, `Nonmembership` 23 s, `Relfinrank` 17 s). Two heartbeat timeouts appeared
mid-refactor in `SlotProduct` (462/986) and both vanished once a real error above them was fixed —
they were collateral, not new cost. No `maxHeartbeats` was raised anywhere.

## 4. What it buys

The char-`p` module's price (measured with `port_advise` + `port_plan` before the refactor:
**397 net new**) loses the `TS` prelude share (≈90 lines of the pin's 33–192) and gains
`TS_injective` at `[Field K]` for free. The remaining new content is the transport engine alone
(`ksplit_comp_evalAtJ`, `iota`/`_injective`, `integral`, `lift`), which is WORKORDER-GS1's work.
The `Defs/TS.lean` docstring now carries the two-spelling table, so the next agent meets the
history instead of re-deriving it.
