# WORKORDER — `exists_baseChange_correspondence_of_constantFieldExtension` (proof bodies)

Scope: fill the **eleven `sorry` proofs** of one existing module. Every statement,
import, section and `variable` block in that module is already in place and is
**frozen**: the statement check is green and must stay green. Do not add, remove or
restate a declaration, do not touch any other file.

## The target

`lean/FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean`
(currently 11 `sorry`s, elaborates clean otherwise).

The statements are pinned to `anthropics/fermats-last-theorem` `aa2d8b3` (local clone at
`~/proj/fermats-last-theorem`):

- `Theorems/Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.lean`
  — the headline statement (already transcribed, do not retype it);
- `P2M/Sol/S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.lean`
  (743 lines) — **the proof text**. Transcribe it; adapt only what the port's mathlib
  (`v4.34.0`) forces.

## The eleven holes, in file order

| port declaration | pin proof | what it is |
|---|---|---|
| `exists_extension` | `S_…:183–235` | extend `χ : F →ₐ[K] F'` to `FE →ₐ[E] F'E` via `liftMap` into `E ⊗[K] F`, `AlgEquiv.ofInjective`, `IsFractionRing` |
| `isIntegral_extension` | `:239–269` | integrality of `χE` from the generating set `F'` |
| `finite_extension` | `:271–303` | `Module.Finite FE F'E` by a spanning family, with the finrank bound |
| `finiteAlong_of_isIntegral` | `:322–335` | essential finite type + integral ⇒ finite |
| `fg_of_finiteAlong` | `:337–361` | transcendence and finiteness transfer along a finite roof map |
| `centred_restrictAlong` | `:369–380` | the restricted place stays centred at `σ ∘ χ` |
| `inertiaDegAlong_eq_one` | `:382–391` | `deg = 1` over an algebraically closed base kills the inertia degree |
| `exists_of_correspondence_single_ne_zero` | `:393–406` | a nonzero coefficient comes from a place of the fibre |
| `fibre_centred` | `:420–557` | the counting core: ramification one, centres bijective with `{σ | σ ∘ χ = e}`, finite |
| `correspondence_single_apply_centred` | `:559–624` | the fibre formula, `Finset.sum_bij` against the `finsum` over `σ` |
| `exists_baseChange_correspondence_of_constantFieldExtension` | `:633–743` (`solution`) | the headline: assemble the extension of the roof and the three divisor clauses |

## Use the port, do not re-derive (these are already public)

- `AlgebraicCurve.CentredPlaceRigidity.mem_of_valuation_lt_one`,
  `.eq_zero_of_valuation_algebraMap_lt_one`, `.centre_unique`,
  `.span_eq_top_of_adjoin_eq_top` — the pin's opening general block, imported by the
  module. The pin declares them locally; here they are one public copy in
  `FLTForHuman/AlgebraicCurve/Place/ConstantFieldExtension.lean`. Qualify them or
  `open AlgebraicCurve.CentredPlaceRigidity`. `algebraMap_mem_of_centred` (in this
  module) is written against them already.
- `AlgebraicCurve.essFiniteType_of_fg` (`IsCurveOver/ConstantFieldExtensionExists.lean`)
  — the pin's `essFiniteType_of_fg`; the module imports it and does **not** declare it.
- `AlgebraicCurve.linearIndependent_of_constantFieldExtension`
  (`IsCurveOver/ConstantFieldExtension.lean`), `AlgebraicCurve.exists_constantFieldExtension`
  (`IsCurveOver/ConstantFieldExtensionExists.lean`),
  `AlgebraicCurve.Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension`
  (`Place/ConstantFieldExtension.lean`), `AlgebraicCurve.fundamentalIdentityAlong`,
  `AlgebraicCurve.normFormulaAlong`, `AlgebraicCurve.separableAlong_of_charZero`
  (`WeilExchange/Transport.lean`), `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable`
  (`IsCurveOver/Transcendental.lean`), `AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver`
  (`Canonical/HasCanonicalDivisor.lean`).

Near-twins worth reading before writing `exists_extension` and `fibre_centred`: in
`Place/ConstantFieldExtension.lean`, `CentredPlaceRigidity.mulMap` / `mulMap_injective`
(the `liftMap` pair specialised to one roof) and `exists_centred` (the same
fraction-ring construction as `exists_extension`, for the identity roof), and
`AlgebraicCurve.Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension`
(the `span_eq_top_of_adjoin_eq_top` + `finrank_range_le_card` argument that
`finite_extension` also uses).

## Traps

1. **Statements are frozen.** `python3 spec/check_port.py` reports
   `18 ok, 0 mismatch, 0 missing` right now. If a proof compiles only after changing a
   statement, stop and report — do not adapt the statement.
2. `haveI` / `letI` are used deliberately for the pin's instance walls; the module sets
   `linter.style.haveILetI false`. Do not rewrite them to `have` / `let`.
3. The pin's `solution` clears its unused hypotheses with
   `have _hFI := hFI; have _hN := hN; clear hFI hN _hFI _hN` — keep that (it silences the
   unused-variable linter without changing the statement).
4. `push Not at hcon` in the pin's `fibre_centred` is `v4.34.0`'s **current** spelling —
   `push_neg` is the deprecated alias and warns — so keep the pin's text. Likewise
   `Algebra.TensorProduct.induction_on` and the pin's `if_neg` (now `ite_eq_right`) are
   `v4.34` deprecations: adapt the tactic, never the statement. Check the deprecation
   direction in the tree before "modernising" a pin tactic.
5. The pin's `solution` calls `exists_constantFieldExtension K F' E hfg'`; the port's
   version additionally takes the base's `[IsCurveOver K F']` and
   `[HasCanonicalDivisor (K := K) (F := F')]` as instances, both of which the pin
   supplies as `haveI`s there. Keep those.
6. `omega` closes the two integer-cardinality steps of `fibre_centred`; do not replace it
   with a manual chain unless it fails.

## Build and check discipline

- **Never a tree build.** Only
  `flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence`
  from `lean/`, and only when the file is done.
- Edit loop:
  `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean`
  (from `lean/`). The low cap is on purpose: a declaration that will not fit is an
  instance-inference defect, not a budget. Never raise `maxHeartbeats`, never add a
  module `set_option maxHeartbeats`.
- Every command under 2 minutes, `timeout` on each, no shell loops around the cap.
  Redirect long output to `lean/tmp/bc-build.log` and read the log.
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean`
  from `lean/` at the end: it must print `18 ok, 0 mismatch, 0 missing`.
- Axioms: write `lean/tmp/axioms-bc.lean` with
  `import FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence` and
  `#print axioms AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension`
  (also on `AlgebraicCurve.BaseChangeCorrespondence.fibre_centred` and
  `…correspondence_single_apply_centred`), then
  `timeout 110 lake env lean -DmaxHeartbeats=4000000 lean/tmp/axioms-bc.lean` from
  `lean/`. Each must print `[propext, Classical.choice, Quot.sound]`.
- Warnings: the module must build with **0** warnings once the `sorry`s are gone.
- No `sorry` / `admit` / `axiom` / `native_decide` anywhere; no other file edited; no
  `spec/decl_markers.tsv` row; no commit.

## Report back (one message, do not poll)

1. build: ok/fail, warnings (want 0), the log path;
2. the `check_port` summary line;
3. the three `#print axioms` lines;
4. the declarations, if any, whose port proof differs from the pin's beyond a tactic
   rename — one line each (this is a faithfulness record, not a diff);
5. **blockers early**: on first belief that a proof cannot be transcribed (a missing port
   lemma, an instance that will not synthesize, an import that must be added to another
   module), send a short message — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`"
   — and keep working on the rest. Never weaken a statement, never edit a hub module,
   never deliver a file with a `sorry`.
