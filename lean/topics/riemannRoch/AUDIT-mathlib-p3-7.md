# Audit — mathlib first, row 3.7 (the RR assembly against the K ending)

Worker's audit, written as the front of the port (playbook §2.2). Pin
`anthropics/fermats-last-theorem@aa2d8b3`, port mathlib `v4.34.0`. Scope: the
public headline `AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed`,
`ModularCurve.p0n20_rr_constantsAreBase_of_isAlgClosed` (pin 5931), and the
`p0n25_wkc_*` `MirrorAssembly` block (pin 5971–6257) with the K-route chain it
reaches (pin 1973–5931).

Method: every name a transcribed proof reaches was `#check`ed against the port
closure first; the port's phase-1 engine (rows 3.1–3.6) supplies essentially all
of the mathematics, so the audit is mostly a **reuse map**, with the genuinely
absent names listed as negatives. The `#check` probes were run in a gitignored
`ScratchRR.lean` (deleted at closeout) against
`Defs/WeilOfKaehler`, `Defs/PushPull`, `Defs/PlaceEvaluation{,Algebra}`,
`Genus/Index`, `Genus/Stichtenoth`, `RiemannRoch/Assembly`, `LocalResidue/Instance`,
`ResidueTheorem/KFamily`.

## 1. Reuse wins — the phase-1 engine subsumes the pin's K-route

The pin's `solution` is a two-line call reaching `ModularCurve.p0n25_wkc_*`, whose
proofs reach a K-route chain of 38 genuinely-new pin declarations. **Every piece of
mathematics in that chain already exists in the port** under a phase-1 name; the
work is adapter-shaped. The measured reuse:

| pin declaration (pin line) | port substitute | note |
|---|---|---|
| `indexOfSpecialty_eq_of_genusReached` (3538) | `Genus/Index.lean:975` | already public, same name |
| `RiemannGenusReachedAt.eq_of_ge` (3504) | `Genus/Index.lean:934` | already public, same name |
| `omegaSpace_finite_of_genusReached` (3916) | `Genus/Index.lean:1184` | already public, same name |
| `weilDifferentialRankOne_of_genusReached` (3929) | `Genus/Index.lean:1240` | already public, same name |
| `exists_weilSmul_eq_of_genusReached` (3809) | `Genus/Index.lean:1198` | the pin's `_of_riemannIndexFormula` variant differs only in using `genus K F` for the Stichtenoth witness `γ` |
| `gate_riemannInequality_of_genusReached` (3628) | `Genus/Index.lean:1039` | the pin's `degree_add_one_sub_genus_le_ell_of_riemannIndexFormula` is its `hRI`-form |
| `two_mul_ell_le_indexOfSpecialty` (4670) | `Genus/Index.lean:1159` | already public, same name |
| `residuePairing_surjective_of_rankOne_max` (1253/4687) | `Genus/Index.lean:1253` | already public, same name |
| `Place.eq_algebraMap_of_forall_ord_nonneg` (2827) | new — port lacks the `∀ v, 0 ≤ v.ord g` constant-field bridge | proved from `Place.ord_sub_evalAt_pos` + `Divisor.degree_eq_sum_support` |
| `constantsAreBase_of_{exists_isRational,deg_eq_one}` (2865/2887) | new — thin adapters | proof transcribed (3 + 2 lines) |
| `weilDualityAdelic_of_residueRows` (3262) | new — one `rw` | `rw [← finrank_omegaSpace_eq_indexOfSpecialty]` |
| `riemannIndexFormula_of_genusReached` (3592) | new — 5-line adapter over `indexOfSpecialty_eq_of_genusReached` | |
| `omegaSpace_finite_of_riemannIndexFormula` (3755) | new — `hRI`-form of `omegaSpace_finite_of_genusReached` | |
| `lSpace_finite_of_riemannIndexFormula` (3770) | new — `FiniteDimensional.of_finrank_pos` | |
| `weilDifferentialRankOne_of_riemannIndexFormula` (3833) | new — same proof as `…_of_genusReached` with `hRI` | |
| `stichtenothGenus_nonneg` (4031) | new — 6 lines over `indexOfSpecialty_eq_of_genusReached` | |
| `genus_eq_degree_div` (4042) | new — definitional unfolding of `Defs/CanonicalDivisor.genus` | |
| `instSumRamificationInertia` (2615) | `Genus/Stichtenoth.lean:254` + `Tate/CompletionTraceSum.lean:211` have private copies; the phase-1 proofs of the reached material do not need the class | **dropped (subsumed)**, see §3 |
| `not_isField_integralClosureAt'` (5779) | inlined in the port's `Place.exists_restrict_eq` (`Genus/Stichtenoth.lean`), itself reached through the already-public `RationalFunctionField.nonempty_place_of_ratFunc_tower` | **dropped (subsumed)**, see §3 |
| `RationalFunctionField.{nonempty_place_of_ratFunc_tower,stichtenothGenusExists,finiteDimensional_lSpace_zero_of_constantsAreBase}` (5869/5895) | `Genus/Stichtenoth.lean:899/910/904` | already public, identical statements |
| `weilOfKaehlerK_mem_omegaSpace_of_residueTheoremK` (4758) | **PF twin** `Defs/WeilOfKaehler.lean:336` `weilOfKaehler_mem_omegaSpace_of_residueTheorem` | the K predicate differs (`ResidueTheoremK` takes `Rfam` explicitly), so transcribe the 8-line proof over the K layer |
| `ord_sub_evalAt_pos` (1973) | new, pin-private | transcribed private at the pin name |
| `Place.exists_trace_residue_ne_zero` (4863) | `Defs/WeilOfKaehler.lean:274` is **private** in a frozen module | re-provisioned `private` locally in this module at the pin name (promotion debt) |

The `p0n25_wkc_*` block itself is the exact K analogue of the port's
`Defs/WeilOfKaehler.lean` PF block (`kaehlerResidueTerm_single_of_ne`,
`localResidue_mul_uniformizer_inv`, `weilOfKaehler_single_s6`,
`weilOfKaehler_simplePoleProbe`, `weilOfKaehler_ne_zero_s6`,
`trace_residueField_eq_zero_of_weilOfKaehler_mem`,
`weilOfKaehler_omegaSpace_le_canonical_s6`), with `weilOfKaehler K F hω` replaced by
`weilOfKaehlerK Rfam hω` and `v.localResidue` by `(Rfam v).res`. The K layer
(`kaehlerResidueTermKFam`, `weilOfKaehlerK`, `weilOfKaehlerK_apply`,
`weilOfKaehlerK_vanish_adeleBdd_canonical`, `ResidueTheoremK`) is already public in
`Defs/LocalResidue.lean:205–327`. So the block transcribes against the port's own
definitions, not the pin's.

## 2. Recorded negatives (searches that found nothing)

- No mathlib lemma gives any part of the function-field Riemann–Roch theorem over a
  general curve; mathlib's `RiemannRoch` API is for number fields / Dedekind
  domains, not the adelic function-field form. The whole assembly is the pin's.
- `HasPrincipalDivisors` has **no generic instance** in mathlib or in the port for a
  general function field; the only source is `IsCurveOver.toHasPrincipalDivisors`
  (generated by `class IsCurveOver extends HasPrincipalDivisors`, port
  `Defs/IsCurveOver.lean:23`). The pin's `MirrorAssembly` section relies on exactly
  this instance (the many pin `attribute [-instance]` lists disable it explicitly).
  Consequence for this port: every `p0n25_wkc_*` proof that calls a
  `[HasPrincipalDivisors]`-dependent lemma needs `[IsCurveOver K F]` in scope; the
  pin's section supplies it at `MirrorAssembly` but **not** at
  `MirrorIdentification`/`CanonicalSupply`, where `[HasPrincipalDivisors]` is an
  explicit binder of the one declaration that needs it.
- `dif_pos` on the port's `genus` `if h : … then … else …`: the port's `genus`
  (`Defs/CanonicalDivisor.lean:143`) uses `letI := Classical.propDecidable` and a
  dependent `if`, i.e. `dite`; `dif_pos hne` applies (`v4.34.0` keeps `dif_pos`).
- No mathlib substitute for `WeilOmegaEllAgrees`, `WeilDuality`,
  `WeilDualityAdelic`, `FunctionFieldRiemannRoch`, `RiemannIndexFormula`,
  `ResiduePairingSurjective`: all are the pin's `Prop` rows, already ported in
  `Defs/RiemannRochRows.lean` and `Defs/WeilOfKaehler.lean`.
- `finsum_eq_single` (mathlib `Algebra.BigOperators.Finprod`) exists and is used by
  the pin's `p0n25_wkc_weilOfKaehlerK_single`; no port-local replacement needed.
- `Submodule.finrank_quotient_chain` (mathlib) is available; used only inside the
  already-ported `indexOfSpecialty_eq_of_genusReached`.

## 3. Dispositions (deliberately not re-landed)

- `instSumRamificationInertia` (pin 2615, `scoped instance … : SumRamificationInertia K F F'`).
  The port already carries the class and `Place.sum_ramificationIndex_mul_inertiaDeg`
  (`ResidueTheorem/KFamily.lean:49`), and two `private` copies of the *finite-dimensional*
  instance (`Genus/Stichtenoth.lean:254`, `Tate/CompletionTraceSum.lean:211`). The K-route
  assembly reached here (pin 1973–6257) never invokes the `SumRamificationInertia` class
  by name: `IsCurveOver.deg_eq_one_of_isAlgClosed` (used by `p0n20`) is proved directly in
  the port. Re-landing a global scoped instance for a class no proof in this module uses
  would be dead code and an instance-search hazard; dropped as **subsumed**, no promotion debt.
- `not_isField_integralClosureAt'` (pin 5779, pin-private). It is the private helper of the
  pin's `Place.exists_restrict_eq`; the port's `Place.exists_restrict_eq` already inlines an
  equivalent argument, and the public `RationalFunctionField.nonempty_place_of_ratFunc_tower`
  (`Genus/Stichtenoth.lean:899`) is imported and used directly. Dropped as **subsumed**.
- `Place.isRational_of_deg_eq_one` (pin 2026, pin-private, used by the pin's
  `constantsAreBase_of_deg_eq_one`). The port's public copy lives in `P1/Dictionary.lean`
  (`AlgebraicCurve.Place.isRational_of_deg_eq_one`), which is not on this module's import
  path; the imported `Defs/PlaceEvaluation.lean:178` carries the equivalent
  `Place.isRational_iff_deg_eq_one`, and this module proves the adapter from that `iff`.
  No statement is affected (the pin declaration is private).
- The pin's `Place.exists_trace_residue_ne_zero` (pin 4863) is `private` in the port's
  frozen `Defs/WeilOfKaehler.lean`; this module re-provisions it `private` at the pin name
  and records the pin `S_…:274` as **promotion debt** (a refactor round can promote it).

## 4. Boundary / verification notes

- The `Thm_` wrapper's binder block carries hypotheses that are redundant in the port
  (`[HasPrincipalDivisors]`, `[Module.Finite]` versus `[FiniteDimensional]`, `[IsIntegral]`
  versus `[FiniteDimensional]`); they stay verbatim, and the two linter
  `overlappingInstances` warnings on the headline are the expected price of the verbatim
  wrapper statement (the same shape as row 6's K headline).
- `Nontrivial Ω[F⁄K]` is added as a section variable to the `CanonicalNonvanishingMaximality`
  and `CanonicalSupply` sections because the imported `simplePoleProbe_mem_adeleBdd`
  (`Defs/WeilOfKaehler.lean:248`) carries it; the pin's inlined copy does not. This is an
  *elaborated-signature* difference only (the checker diffs source text and the pin's
  instances are section variables there too), and every caller inside the module supplies
  it, either directly or from `[IsCurveOver]` (`IsCurveOver.instNontrivialKaehler`).
