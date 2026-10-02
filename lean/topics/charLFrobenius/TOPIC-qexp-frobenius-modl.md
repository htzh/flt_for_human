# Topic: characteristic-ℓ Frobenius on the `q`-expansion model (`Fr*Fr_* = ℓ`)

**Status: measured, not started (2026-10-02).** Cone **43 nodes / 4,172 raw `S_`
lines**, 31 of them already ported; **11 needed / 1,669 raw `S_` lines**, plus an
unported definition layer (§4). This file is the measurement and the work-order
cut for
`ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental`.
Re-measure before dispatching (§10) — the numbers are a snapshot.

**Why this directory, not `deligneSerre/`.** This node is *foundational*, not
Deligne–Serre-specific: the D–S cone only *consumes* it, through
`frobeniusQuadratic_tateModule_jOne` → `…charpoly_frobenius_of_heckeDiamondChar`
→ `CuspForm.IsEigenformWith.exists_galoisRepAdic_charpoly_frobenius_eq_and_isUnramifiedAt`
(see [../../studies/frobenius-charpoly-scout.md](../../studies/frobenius-charpoly-scout.md) §6).
Its needed set is 9 `AlgebraicCurve.*` nodes plus one `Algebra.*` node; only the
568-line target is `ModularCurve.*`. It is also not the subject of
[../functionFieldGeneration/TOPIC-qexp-function-field-c.md](../functionFieldGeneration/TOPIC-qexp-function-field-c.md),
which is the *field-of-ratios* target and explicitly excludes this cone. The
subject — the char-ℓ Frobenius congruence on the modular curve's `q`-expansion
model, and the generic perfect-field function-field Frobenius under it — will
recur (the `J₀`/divisorial route, the `W54` forms, the mod-ℓ reduction maps), so
it gets its own directory: `topics/charLFrobenius/`.

**Audience.** A session taking the q-expansion route of the geometric
Eichler–Shimura congruence. Read [porting-playbook.md](../../porting-playbook.md)
§0.2 (staffing), §2.1 (measure the cone), §2.2 (route audit), §3.1–§3.5 (module
roles, sets, build ladder) and §4 (faithfulness); [instance-friction.md](../../instance-friction.md)
before the Frobenius-subfield files.

**Goal** (the pin wrapper's statement, verbatim; pin `aa2d8b3`):

```lean
theorem ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
    (K : Type*) [Field K] [IsAlgClosed K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (y : AlgebraicCurve.Pic0 K (ModularCurve.qExpFunctionFieldC K Γ)) :
    ModularCurve.qExpFrobeniusPullbackModL K Γ ℓ (ModularCurve.qExpFrobeniusPushforwardModL K Γ ℓ y) =
      ℓ • y
```

Pull-back after push-forward along the ℓ-power Frobenius of the `q`-expansion
function field acts as multiplication by ℓ on `Pic⁰`. This is the input to the
quadratic relation `Frob² − T_ℓ Frob + ℓ = 0` on the Tate module — the q-expansion
route of the geometric Eichler–Shimura congruence.

A binder trap to take from the wrapper, not the `S_` file: the `S_` proof runs
under `[PerfectRing K ℓ]`, but the wrapper omits it because `IsAlgClosed K` and
`[CharP K ℓ]` supply it by instance. Spell the wrapper's binders exactly
(playbook §4).

## 1. What is pinned

Every statement comes from the pin:

- wrapper:
  [Theorems/Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean)
- proof:
  [P2M/Sol/S_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean)
  (568 lines, 49 declarations — inventory in the appendix)
- definitions:
  [Definitions/Def_ModularCurve_QExpFrobeniusModL.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_QExpFrobeniusModL.lean)
  (`qExpFrobeniusPullbackModL` line 250, `…PushforwardModL` line 243,
  `QExpFrobeniusInputsModL` line 165, `qExpFrobeniusModL` line 76),
  [Definitions/Def_ModularCurve_FrobeniusModL.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_FrobeniusModL.lean)
  (the same API one level down, on `modularFunctionFieldFullC`),
  [Definitions/Def_ModularCurve_X1.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_X1.lean)
  (`qExpFunctionFieldC` line 101, `x1FunctionFieldC` line 134), and
  [Definitions/Def_AlgebraicCurve_IsCurveOver.lean](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean)
  (`class IsCurveOver`, already ported as `AlgebraicCurve/Defs/IsCurveOver.lean`).

The port keeps FLT's names, so the checker diffs every statement by name; only
genuinely own declarations need `OWN_PROOFS`.

## 2. The measured cone

```bash
cd tools/deps
python3 frontier.py --target ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental --top 0 --list
```

| reading | nodes | raw `S_` lines |
|---|---:|---:|
| port cone (target closure) | 43 | 4,172 |
| frontier `F` inside the cone | 31 | 2,485 |
| **needed (`F` terminal)** | **11** | **1,669** |
| needed (literal) | 12 | 1,687 |

The 11 needed nodes, by cost:

| node | raw `S_` lines |
|---|---:|
| `ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental` | 568 |
| `AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental` | 399 |
| `AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` | 192 |
| `AlgebraicCurve.exists_separating_transcendental_of_perfectField` | 148 |
| `AlgebraicCurve.Place.finite_residueField_of_finiteDimensional` | 89 |
| `AlgebraicCurve.kaehlerRankOne_of_transcendental` | 73 |
| `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq` | 71 |
| `AlgebraicCurve.isCurveOver_of_transcendental` | 57 |
| `AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable` | 39 |
| `AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField` | 19 |
| `AlgebraicCurve.Divisor.degree_eq_sum` | 14 |
| **total** | **1,669** |

By namespace: `AlgebraicCurve.` 9 / 1,030, `ModularCurve.` 1 / 568, `Algebra.` 1 / 71.
The two premises the target cites directly are
`AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField` (19) and
`AlgebraicCurve.exists_separating_transcendental_of_perfectField` (148) — both are
needed, so the generic perfect-field engine is on the critical path, not a
convenience.

**Content vs raw.** These `S_` files are dense proof text; budget content at
roughly 80–85 % of raw (the sibling q-expansion topic measured 81 %), i.e.
~1,350–1,420 content lines.

## 3. What is already paid (do not re-derive)

The 31 ported nodes inside the cone are the port's `ℙ¹` / place vocabulary, and
they are the reason the target's own proof is mostly assembly:

- `AlgebraicCurve.RationalFunctionField.*` (18 nodes): `hasPrincipalDivisors`,
  `degree_eq_zero_of_forall_eq_ord`, the `ord_ofHeightOneSpectrum` block, and the
  finite-support lemmas `finite_setOf_ord_ne_zero`, `…_of_finiteDimensional`.
- `AlgebraicCurve.Place.*` (12 nodes): `ord_*`, `mem_*`, `adicValuation_*`,
  `sum_ramificationIndex_mul_inertiaDeg_fiberOver`.
- `AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional`,
  `AlgebraicCurve.instIsCurveOverRatFunc`.

The port also has the vocabulary the definition layer sits on:
`intFormRatiosC` / `IsIntegralQExp` / `intSeriesC`
(`ModularForms/WeightOne/Gamma0Integral.lean`,
`ModularCurve/JqIntegralRatios.lean`) — but **not** `qExpFunctionFieldC` itself
(§4), which is the FFG topic's Set A.

## 4. The definition layer (unported, measure first)

The target's `S_` file imports `Definitions.Def_ModularCurve_QExpFrobeniusModL`,
which imports `Definitions.Def_ModularCurve_X1` and
`Definitions.Def_ModularCurve_FrobeniusModL`. None of the three is ported (the
port has no `qExpFrobeniusModL`, no `QExpFrobeniusInputsModL`, no
`frobeniusPushforwardModL`, no `qExpFunctionFieldC`):

| definition module | pin lines | what is needed |
|---|---:|---|
| `Def_ModularCurve_QExpFrobeniusModL.lean` | 311 | the whole `qExpFrobenius*` API: `RingHom`, `ModL`, `PlaceModL`, `DivPushforward/PullbackModL`, `QExpFrobeniusInputsModL`, `DegZero*`, `Pic0*`, and the two `Pic0` maps the target names |
| `Def_ModularCurve_FrobeniusModL.lean` | 342 | the same API on `modularFunctionFieldFullC` (`frobeniusModL`, `frobeniusPlaceModL`, `frobeniusDivPushforward/PullbackModL`, `FrobeniusInputsModL`, `frobeniusDegZero*`, `frobeniusPic0*`) |
| `Def_ModularCurve_X1.lean` | 218 | `qExpFunctionFieldC` (line 101), `x1FunctionFieldC` (line 134); the `intFormRatiosC` vocabulary below them is already ported |
| `Def_AlgebraicCurve_IsCurveOver.lean` | 76 | `class IsCurveOver` only — already ported |

**Dedup to check before writing (playbook §2.4).** The two `*FrobeniusModL`
modules are the same API twice, once on `qExpFunctionFieldC K Γ` and once on
`modularFunctionFieldFullC K N` (`RingHom`, `ModL`, `PlaceModL`,
`DivPushforward/PullbackModL`, `InputsModL`, `DegZero*`, `Pic0*`,
`Pushforward/PullbackModL`; the `qExp` copy adds a `coeff_*` prelude and the
`…_eq`/`…_mk`/`…_of_not` unfolding lemmas). Decide
per declaration whether the `qExp` copy can be the generic construction
specialised (a `*_of_transcendental`-style transport or one generic
`FrobeniusModL` module with two carriers), or whether the pin's two definitions
must both be written to keep the checker's statements verbatim. Measure by
diffing the two files' declaration bodies before dispatching Set B; this is the
single largest possible saving in the definition layer.

## 5. Route and set decomposition

Three sets, dispatched one at a time with a review between (playbook §3.4). The
sets follow the import order, not the pin's file order: definitions and generic
engine first (they are leaves), the target last as the wire test.

### Set A — the generic perfect-field engine (5 nodes, ~730 raw)

`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`,
`AlgebraicCurve.isCurveOver_of_transcendental`,
`AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField`,
`AlgebraicCurve.exists_separating_transcendental_of_perfectField`,
`AlgebraicCurve.Divisor.degree_eq_sum`.

Note `AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean` already exists —
`#check` it first; `exists_separating_transcendental_of_perfectField` may be a
shorter corollary of what is on disk than its 148 raw lines suggest. New files
are leaf modules, so this set cannot cascade.

### Set B — the definition layer and the Frobenius-subfield engine (3 nodes + 2–3 def modules, ~660 raw + defs)

`AlgebraicCurve.finrank_frobeniusSubfield_eq_of_transcendental` (399 — the
heartbeat risk, §8),
`AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` (192),
`AlgebraicCurve.hasPrincipalDivisors_of_transcendental_of_isSeparable` (39),
`AlgebraicCurve.kaehlerRankOne_of_transcendental` (73),
`AlgebraicCurve.Place.finite_residueField_of_finiteDimensional` (89), plus the
`qExpFunctionFieldC` / `x1FunctionFieldC` definitions and the `qExpFrobenius*` API
(§4). This is where the dedup decision of §4 is made.

### Set C — the target (1 node, 568 raw) and the wire test

The `QExpFrobRel` helper block (§appendix, lines 22–552: `sigma`, the Frobenius
place/`ord`/ramification algebra, `PP`/`MM`, `isoPP`, the `finrank`/`norm` block,
the `fiberAlong`/`fundamentalIdentityAlong`/`normFormulaAlong` inputs) and the
24-line `main` + `solution`. Keep the whole `QExpFrobRel` block `private`; only
`ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental`
is public (the pin wraps it in `P2MW.S_…`, so the checker matches by last name).
This set is the wire test: a wrong binder in Set A or B surfaces here.

## 6. Module homes

Match the pin's namespaces, not the effort (playbook §3.1, §5):

| declaration(s) | home |
|---|---|
| `AlgebraicCurve.*` engine (Set A/B, 9 nodes) | `FLTForHuman/AlgebraicCurve/IsCurveOver/` (extend `SeparatingTranscendental.lean` or add `PerfectField.lean`), `…/Defs/IsCurveOver.lean`, `…/PrincipalDivisors/` (the `hasPrincipalDivisors_*` pair), `…/Place/` (`finite_residueField_of_finiteDimensional`), `…/Defs/Divisor.lean` (`degree_eq_sum`) |
| `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq` | `FLTForHuman/Algebra/` (generic; the port already has a `Frobenius`-free home for such leaves) |
| `qExpFunctionFieldC`, `x1FunctionFieldC` | with the `intFormRatiosC` vocabulary (`ModularCurve/JqIntegralRatios.lean` or `ModularCurve/Defs/`) |
| the `qExpFrobenius*` API | new `FLTForHuman/ModularCurve/Frobenius/` (a theory directory: `Defs.lean` for the API, `QExpModL.lean` for the target) |
| the generic `frobenius*` API if written | same `ModularCurve/Frobenius/` directory, one module per carrier |

One directory holds one theory; the `ModularCurve/Frobenius/` split is warranted
because the J₀/divisorial route (a future topic in this directory) is a second
theory sharing only the `Defs/`.

## 7. Budget (correction ledger)

| row | lines |
|---|---:|
| needed theorem content (~83 % of 1,669 raw) | ~1,385 |
| − substitution reuse in Set A (`SeparatingTranscendental` is on disk) | −100 … −250 |
| + definition layer, if both `*FrobeniusModL` copies are written (311 + 342 + ~10) | +660 |
| − definition-layer dedup, if the generic module backs the `qExp` API | −250 … −550 |
| **content to write** | **≈ 1,700 … 2,250** |
| × written ÷ content (1.1–1.3) | **≈ 1,900 … 2,900 written lines** |

Sets: **3**, one per §5 set, with Set A's measurement deciding Set B's dedup
route. The budget unit that has been predictive is the number of *pin-private
helper blocks* promoted versus replayed, not rounds.

## 8. Risks, and the stop-early protocol

1. **`finrank_frobeniusSubfield_eq_of_transcendental` (399 raw).** Frobenius
   subfields, inseparability and `Module.finrank` over a perfect field — the
   instance/defeq risk of this cone. Scout it in a gitignored `Scratch.lean`
   before dispatching Set B (playbook §2.6). Stop-early: if the subfield degree
   does not reproduce in one round, re-scope rather than push.
2. **The `PerfectRing` instance gap.** The `S_` proof assumes `[PerfectRing K ℓ]`;
   the wrapper gets it from `IsAlgClosed`/`CharP`. If mathlib's instance search
   does not derive it at the port's spelling, supply it explicitly and record it
   in [instance-friction.md](../../instance-friction.md) — do not add it to the
   statement.
3. **Definition-layer duplication.** Writing both `*FrobeniusModL` modules is
   ~660 lines of near-duplicate API. Measure the diff first (§4); if the pin's
   statements force both, say so in the record.
4. **Heartbeat walls.** The `S_` file's `QExpFrobRel` block (`normFormulaAlong`,
   `fiberAlong`) is dense relative-degree algebra; bound every check and record a
   blow-up per [notes/lean-build-cost.md](../../../notes/lean-build-cost.md)
   rather than raising `maxHeartbeats`.

## 9. Definition of done

- [ ] The target in a library module, statement verbatim from the wrapper, in the
      default build target.
- [ ] `spec/check_flt_statements.py`: 0 mismatched / 0 missing, with `SOURCES`
      gaining the two `Thm_AlgebraicCurve_*` wrappers the target's `S_` imports
      plus the Set A/B wrappers and the definition modules; any own declaration on
      an explicit `OWN_PROOFS` entry with a reason.
- [ ] A consumer zone that **uses** the target: a `spec/` example applying it to
      a concrete `K`, `Γ` and `y` (or stated in hypothesis form with the reason,
      if `qExpFunctionFieldC K Γ` cannot be instantiated concretely without the
      unported Set A of the FFG topic — record which).
- [ ] `frontier.py --target …` reports `needed 0`.
- [ ] `#print axioms` clean, no `sorry`/`admit`/`axiom`, no `import Mathlib` in a
      library module.
- [ ] A short record: written vs budgeted lines, whether the definition-layer
      dedup was available, and the `PerfectRing` answer.

## 10. Verification recipe

```bash
cd lean
flock /tmp/flt_for_human.lock timeout 60 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false <file>          # tier 0, per edit
flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.<Dotted.Path>   # tier 1
python3 spec/check_flt_statements.py                            # 0/0
flock /tmp/flt_for_human.lock timeout 300 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false spec/<X>Consumer.lean
cd ../tools/deps && python3 frontier.py --target \
  ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental --top 0
```

One `lake build` per wave, serialized under `flock` and bounded with `timeout`;
the whole-tree build only at the milestone (playbook §3.5).

## 11. Out of scope

- **The consumers.** `ModularCurve.frobeniusQuadratic_tateModule_jOne` / `_jH`,
  `reductionQExpModL_gamma1_heckeOperatorOneBar`,
  `reductionQExpModL_gammaH_heckeOperatorHAlong`, and the whole Deligne–Serre
  cone. This topic lands the relation; the route above it is the D–S port's.
- **The `J₀`/divisorial route.**
  `ModularCurve.frobenius_frobenius_sub_heckeOperatorModL_frobenius_add_smul_eq_zero`
  is a *different proof of the same relation* on the divisorial model
  ([studies/frobenius-charpoly-scout.md](../../studies/frobenius-charpoly-scout.md) §3).
  A future topic in this directory.
- **The field-of-ratios target.**
  `qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull` is
  [../functionFieldGeneration/TOPIC-qexp-function-field-c.md](../functionFieldGeneration/TOPIC-qexp-function-field-c.md).
  `qExpFunctionFieldC` is in scope here only as a definition.
- Any re-derivation of the 31 ported cone nodes. If a proof can call a ported
  theorem, call it.

## 12. Reporting back

Two questions are wanted in the record whatever their answer:

1. **Was the definition-layer dedup available** — can one generic `FrobeniusModL`
   module back both the `qExpFunctionFieldC` and `modularFunctionFieldFullC` APIs,
   or did the pin's statements force two copies? It sets the price of every later
   char-ℓ Frobenius topic.
2. **Did `AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean` already carry
   `exists_separating_transcendental_of_perfectField`** in usable form, or was it
   a re-proof? It calibrates Set A.

---

## Appendix — pin declaration inventory

`P2M/Sol/S_ModularCurve_qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental.lean`
(568 lines, 49 declarations; no declaration is `private` in the pin, but the whole
`ModularCurve.QExpFrobRel` block is conceptually private and should be kept
`private` in the port).

| decl | kind | line | lines to next |
|---|---|---:|---:|
| `FF` | abbrev | 32 | 4 |
| `coeffMap_intSeriesC` | theorem | 36 | 10 |
| `coeffMap_mem` | theorem | 46 | 18 |
| `coeffMap_qExpand'` | theorem | 64 | 11 |
| `sigmaRingHom` | def | 75 | 7 |
| `sigmaInvRingHom` | def | 82 | 13 |
| `sigma` | def | 95 | 16 |
| `frobenius_sigma` | theorem | 111 | 6 |
| `frobenius_eq_pow` | theorem | 117 | 4 |
| `mem_range_frobenius_iff` | theorem | 121 | 8 |
| `sigma_algebraMap` | theorem | 129 | 5 |
| `sigmaSL` | def | 134 | 7 |
| `sigmaSL_inv_smul` | theorem | 141 | 9 |
| `pow_mem_valuationSubring_iff` | theorem | 150 | 5 |
| `frobeniusPlace_eq_smul` | theorem | 155 | 8 |
| `restrictAlong_frobenius_eq_smul` | theorem | 163 | 4 |
| `ord_frobenius` | theorem | 167 | 4 |
| `ramificationIndexAlong_frobenius` | theorem | 171 | 34 |
| `fiberAlong_frobenius` | theorem | 205 | 12 |
| `PP` | abbrev | 217 | 2 |
| `mem_PP_iff` | theorem | 219 | 3 |
| `isoPP` | def | 222 | 12 |
| `charP_FF` | theorem | 234 | 3 |
| `minpoly_PP_of_not_mem` | theorem | 237 | 21 |
| `finrank_PP_adjoin` | theorem | 258 | 6 |
| `MM` | def | 264 | 2 |
| `mem_MM_iff` | theorem | 266 | 2 |
| `PP_le_MM` | theorem | 268 | 3 |
| `mem_MM_self` | theorem | 271 | 3 |
| `mem_MM` | theorem | 274 | 25 |
| `PP_adjoin_eq_top` | theorem | 299 | 5 |
| `forall_exists_pow_eq_of_mem` | theorem | 304 | 10 |
| `finrank_PP` | theorem | 314 | 4 |
| `finite_PP` | theorem | 318 | 4 |
| `isoPP_compat` | theorem | 322 | 6 |
| `finrankAlong_frobenius` | theorem | 328 | 6 |
| `finiteAlong_frobenius` | theorem | 334 | 19 |
| `coe_norm_PP` | theorem | 353 | 31 |
| `frobenius_normAlong` | theorem | 384 | 22 |
| `subsingleton_kaehler_of_forall_exists_pow_eq` | theorem | 406 | 19 |
| `not_mem_PP` | theorem | 425 | 6 |
| `deg_eq_one` | theorem | 431 | 2 |
| `inertiaDegAlong_frobenius` | theorem | 433 | 9 |
| `fundamentalIdentityAlong_frobenius` | theorem | 442 | 12 |
| `normFormulaAlong_frobenius` | theorem | 454 | 37 |
| `pullback_pushforward_frobenius` | theorem | 491 | 29 |
| `pullback_pushforward_pic0` | theorem | 520 | 19 |
| `main` | theorem | 539 | 20 |
| `solution` | theorem | 559 | 10 |
