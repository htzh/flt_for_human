# SET-AF6 — differentiating the right-convolution operator along an archimedean flow

**Status: landed 2026-11-02 — manager's layer and both proof bodies (one worker dispatch).** Read off
the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), and it is the
sixth `AutomorphicForm`-serving set. It is the set SET-AF5 made ready: its two rows are the ones
`rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply` was written for.

The set is **two rows / 2,494 silo**, each a **triple conjunction** — the archimedean derivative of a
right convolution, the tensor form of that derivative's test function, and the integration-by-parts
identity that moves the derivative onto `φ`:

| step | row (`AutomorphicForm.` dropped) | silo | tool net | **net after the promotion** | who |
|---|---|---:|---:|---:|---|
| **R1** | `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,246 | 940 | **≈720** | worker — landed |
| **R2** | `archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,248 | 940 | **≈730** | worker — landed |
| | **2** | **2,494** | **1,871** | **≈985 net new math, 1,398 live + 345 shelved source lines** | |

The manager's layer is a **promotion**, and it is the largest one the column has made: the port held
the pin's **left-derivative half of the archimedean chart** on the `Reserve` shelf, `private`, because
no row needed it — and these two rows are exactly the consumer its own header predicted. It is now two
live public modules, with the nine declarations an earlier cut had lost restored from the pin (§1.5).
Measured effect: **72 of each file's 113 prelude declarations (491 of its 1,246 lines) become
imports** instead of transcription (Appendix A), leaving **42 declarations** to write (Appendix B, whose
47-row list was corrected by five at the landing — §1.6).

§0 the read and the gate; §1 the cut, the pricing and the two landings (§1.5 the manager's promotion,
§1.6 the worker's modules); §2 what the two rows say; §3 homes; §4 ground prep (done); §5 the traps the
worker carried; §6 gates (and the two whose *expectation* this landing corrected); §7 calls; §8
reproduce and the measured re-read; §9 what this set does not do. **Appendix A** is the import list,
**Appendix B** the transcription list, both corrected by §1.6.

## 0. The read

### 0.1 The canonical read — unchanged by this set's manager layer

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af6.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF5 §8 |
|---|---:|---:|
| `needed [F terminal]` | **898 / 370,450** | 898 / 370,450 |
| `needed [literal]` | 911 / 373,925 | 911 / 373,925 |
| frontier F | 1,517 / 756,916 | 1,517 / 756,916 |
| ready rows, all namespaces | 71 / 29,663 | 71 / 29,663 |
| leaves, all namespaces | 249 / 62,588 | 249 / 62,588 |
| `AutomorphicForm` ready rows | **42 / 24,319** | 42 / 24,319 |
| `AutomorphicForm` leaves | **80 / 16,549** | 80 / 16,549 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| `--selfcheck` | PASS (1,352 `Thm_` / 1,517 names) | PASS |

**No `--unport` and no correction**: SET-AF5 closed the FR-0095 shadow at the root, so this brief opens
on the instrument's own read and the read is SET-AF5's §8 to the line.

**The manager's layer does not move this table, and that is a finding, not a bug.** The promotion's
declarations are at the **port's** content names (`lift_*`, `chart_*`), so the frontier's last-name
tier matches no pin node: `needed` is identical before and after. A promotion's payoff is the *order's*
size (Appendix A), never the shelf figure — worth recording because the recipe's §7 re-read is the
wrong instrument for this kind of manager work.

### 0.2 The family, quoted whole

The archimedean-derivative family is **10 rows / 4,004 silo**; this set takes the two that are ready
and defers the eight leaves (their own subject, §9):

| row | silo | shelf status | this set? |
|---|---:|---|---|
| `archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,246 | **ready** | **R1** |
| `archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn` | 1,248 | **ready** | **R2** |
| `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` | 401 | leaf, return 1,443 | deferred |
| `archDerivAtComplex_iH_eq_zero_and_Fm_eq_E_and_iFm_eq_neg_iE_of_hasArchCharacterAtZero_one` | 250 | leaf | deferred |
| `archDerivAt_commutator_of_isArchSmoothAt` | 208 | leaf | deferred |
| `archDerivAt_E_sub_archDerivAt_Fm_eq_smul_of_hasArchCharacterAt` | 184 | leaf | deferred |
| `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` | 133 | leaf | deferred |
| `archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne` | 110 | leaf | deferred |
| `apply_mul_archComplexGLAt_eq_of_forall_archDerivAtComplex_eq_zero` | 117 | leaf | deferred |
| `apply_mul_archRealGLAt_eq_of_archDerivAt_E_eq_zero_of_archDerivAt_Fm_eq_zero` | 107 | leaf | deferred |
| **10 rows** | **4,004** | 2 ready + 8 leaves (1,510 silo → **1,001 net**) | |

**The eight leaves are a different subject** — the *algebra* of the archimedean derivative (the Casimir
element, the `[E, Fm]` commutator, the character identities, the row-isometry invariance), not the
differentiation of an integral. They stay SET-AF7's; taking them here would be 2,881 net in one order.

**Both blocks of the shelf are quoted and every row is accounted for**: 42 ready rows / 24,319 and 80
leaves / 16,549, listed in full with their readiness returns in
[SET-AF5.md](SET-AF5.md) Appendix A and B; this set's two rows are the largest of the ready block, the
rest are deferred in §9 with the same reasons SET-AF5 gave (each is a *consumer* of something unported,
not the next cut), and the withheld 4 / 831 is the prunable complex-analytic subject throughout.

### 0.3 The instrument: return is not what chose this cut

`return(R1)` is **214** (one row: `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar`)
and `return(R2)` is **0**. By the metric SET-AF4/AF5 used, this pair is a *poor* set. It is chosen
because it is the **largest ready block on the shelf** (2,494 of 24,319 = 10% in two rows), it is one
subject, and SET-AF5 was cut specifically to make it ready. The recipe's silo reading — "a large,
self-contained development, the kind of proof that tends to establish an important theorem" — is the one
that applies here, and it is why this brief reports both readings rather than only the fashionable one.

### 0.4 The gate: empty, at the declaration level, twice over

`spec/gate_scan.py` over each row's `Def_` closure, then the FR-0099 census (wrapper ∪ premises):

| row | `Def_` modules (wrapper ∪ premises) | used / **missing** |
|---|---|---|
| R1 | `AutomorphicForm_ArchDerivCasimir`, `…_FactorizableTestFn`, `…_RightConvolution`, `NumberField_AdelicHaar` | 4 / **0** |
| R2 | `AutomorphicForm_ArchDerivCasimirComplex`, `…_FactorizableTestFn`, `…_RightConvolution`, `NumberField_AdelicHaar` | 4 / **0** |

So the definition layer is complete, as it has been for every AF set since AF3. **The gate here is not a
`Def_` module but a corpus**: the pin re-copies the whole archimedean chart into each of the two `S_`
files (113 `private` declarations each, 460 of them a duplicate pair), and the port must *have* that
chart before the two headlines can be stated. That is what §1.5 promotes.

### 0.5 The pricing, two readings

```bash
python3 port_advise.py --nodes <both rows> --json build/af6.json
python3 port_plan.py --json build/af6.json
```

| reading | net new math lines |
|---|---:|
| `port_advise` (name-anchored) | **1,871** — 2,494 raw − 69 boilerplate − 460 twin duplicates − 94 already in the port |
| **by the rename map** (this brief) | **≈985** — 72 of 113 declarations per file are in the port at `lift_*`/`chart_*` names (491 of 1,246 pins lines), and the tool cannot see them |

The second number is the recipe §3's documented false negative, measured: the promotion renamed the
engine at promotion time (playbook §5: "name a promoted helper at the prefix-stripped pin name"), so the
`l5*`/`tc_*` pin names no longer match anything by name and the tool prices 491 lines per file as new.
**Appendix A is the corrected list; the worker's first act is to check each entry's statement before
skipping it** (the same discipline that caught SET-AF5's three copies).

## 1. The cut

### 1.1 The story

The pin's archimedean derivative `archDerivAt hw d φ` is the derivative of `φ` along the one-parameter
flow `t ↦ φ (· * archFlowAt hw d t)`; `rightConv K φ α` integrates `α` against `φ`. The two rows say
that **the derivative of the integral is the integral of the derivative** — three times over:

1. **the headline**: for a factorisable test function `α`, `rightConv K φ α` is archimedean-smooth and
   `archDerivAt hw d (rightConv K φ α) = rightConv K φ (fun y => deriv (fun t => α (archFlowAt hw d (-t) * y)) 0)`
   — the derivative moved onto the test function, along the **negative** flow because the integration
   variable is on the left;
2. **the test-function half**: the right-hand side is *again* a tensor with the same finite factor —
   `∃ fa', IsArchTestFactor fa' ∧ (fun y => deriv (…) 0) = fun y => fa' (glArch y) * ff (glFin y)`.
   This is the pin's `e8l5`/`e8r5` chart, which `FactorizableTestFnArchSmooth{,Complex}` already proves
   on the *right*;
3. **the integration-by-parts identity**: for `γ` compactly supported and `ω` right-flow invariant,
   `rightConv K φ (fun y => archDerivAt hw d γ y * ω y) = -rightConv K (archDerivAt hw d φ) (fun y => γ y * ω y)`
   — the adjointness that makes the archimedean derivative skew-symmetric against the Haar measure.
   This is the identity the Casimir/commutator family (SET-AF7) builds on.

R2 is the same triple at a **complex** place: `archDerivAtComplex`, `ArchDirComplex`, the `ℂ`-chart, and
`IsArchSmoothAtComplex`. The port's own precedent for this exact pair is
`FactorizableTestFnArchSmooth{,Complex}` — two modules, the second the first by the vocabulary map — and
this set follows it (§3).

### 1.2 The steps

| step | what | who | state |
|---|---|---|---|
| **M1** | `Adelic/FactorizableTestFnArchSmoothLeft.lean` — the promoted **left** half of the arch chart (public), + the 4 declarations lost in an earlier cut, restored from the pin | manager | **done** |
| **M2** | `Adelic/FactorizableTestFnArchSmoothComplexLeft.lean` — the complex mirror, + 5 restored | manager | **done** |
| **M3** | the two `Reserve/…Dead.lean` shelves deleted; the two live modules' headers repointed; `CARRY-FORWARD.md`'s nine-declaration entry resolved; the register regenerated | manager | **done** |
| **R1** | the real headline, 1,246 silo → 35 `private` + 1 headline, **696** lines (§1.7) | worker | **landed** |
| **R2** | the complex headline, 1,248 silo → the same by the vocabulary map, **702** lines | worker | **landed** |

### 1.3 The pricing after the promotion, per file

| | raw | prelude declarations | importable | to transcribe | boilerplate | net new |
|---|---:|---:|---:|---:|---:|---:|
| R1 | 1,246 | 113 | **72 declarations / 491 lines** | **41 + the headline** (Appendix B, corrected) | 35 | **≈700** |
| R2 | 1,248 | 113 | the same 72, `Complex` namespace | 41 + the headline | 35 | **≈700** |

The two files' preludes are the same 113 declarations (the 460-line twin duplicate `port_advise` found);
the *new* content is the same 42 declarations in both, so **R2 is R1 by substitution** — the port's
precedent, and exactly how the worker wrote it (it compiled first try).

### 1.4 The lanes

One worker order, two modules, in either order (they share nothing but the promoted engine and the
already-landed `RightConvRegularity`). One manager lane, already closed. The order is
[WORKORDER-AF6-archderiv-rightconv.md](WORKORDER-AF6-archderiv-rightconv.md).

### 1.5 The landing — the manager's layer

**The finding.** `Reserve/AutomorphicForm/Adelic/FactorizableTestFnArchSmooth{,Complex}Dead.lean` held
the pin's **left**-derivative half — 68 and 67 declarations, all `private`, cut there on 2026-10-23
because the *right* headline never reaches a left derivative. The shelf's own header says what to do:

> "A consumer that needs the left action (`archDerivAt` under left translation) has to promote the
> declaration it wants here; nothing else has to change."

SET-AF6's rows are that consumer: differentiating `rightConv` in the **group** variable is a left
action. So the promotion is not a convenience, it is the condition for the rows to be statable at the
port's names at all.

| step | module | Δ | checker | build |
|---|---|---|---:|---|
| M1 | `Adelic/FactorizableTestFnArchSmoothLeft.lean` (**new, 593**) | 68 declarations `private` → **public**; 4 restored → **72** | tier 3 (no wire, §1.5.1) | silent, **7.5 s** |
| M2 | `Adelic/FactorizableTestFnArchSmoothComplexLeft.lean` (**new, 594**) | 67 → public; 5 restored, 1 already present → **72** | tier 3 | silent, **6.6 s** |
| M3 | `Reserve/…/FactorizableTestFnArchSmooth{,Complex}Dead.lean` | **deleted** (1,138 lines moved out of the shelf) | — | — |
| M3 | `FactorizableTestFnArchSmooth{,Complex}.lean` (headers only) | repointed at the new modules | **2 ok** / 0 / 0 | silent, 6.0 / 5.0 s |
| M3 | `CARRY-FORWARD.md` | the "FTF1 left half's nine pre-cut declarations" entry marked **resolved** (all nine restored) | — | — |
| M3 | `spec/UNWIRED-PUBLIC.md` | regenerated: **112 → 114 modules, 3,474 → 3,618 public declarations** | — | — |

**The nine restored declarations** (four real, five complex) — the ones `CARRY-FORWARD.md` recorded as
having no home in the port at all:

| real (`FactorizableTestFnArchSmoothLeft`) | complex (`…ComplexLeft`) |
|---|---|
| `lift_archFlowAt_inv` | `lift_archFlowAtComplex_inv` (already on the shelf) |
| `lift_continuous_cD` | `lift_continuous_cD` |
| `lift_glFin_archFlowAt` | `lift_glFin_archFlowAtComplex` (already on the shelf) |
| `lift_isFactorizableTestFn_leftDeriv` | `lift_isFactorizableTestFn_leftDeriv` |
| — | `lift_exists_compact_support`, `lift_continuous_LD`, `lift_leftDeriv_tensor` (the three the complex shelf had lost) |

All nine were transcribed from the pin's two `S_` files under the rename map the shelf headers carry
(`e8l5*` → `lift*`, `e8tc_*` → `chart_*`, `e8r5*` → `flow*`, `e8leftDeriv` → `leftDerivFactor`), each
with its pin proof, and all nine `#check` green from a fresh probe.

**What the manager's layer consumed**: 1,190 source lines promoted (1,138 moved out of `Reserve` + two
new headers), **9 declarations / ≈50 lines written**, 0 declarations deleted, 2 header sentences
repointed, 1 register entry resolved, 1 shelf emptied. No `Def_` node, no marker, no `spec-pin` wire
(§1.6), no migration of a legacy module, no tree build.

### 1.5.1 Why the promoted modules carry no `spec-pin:` wire

The checker matches a port declaration to a pin source **by last name**. These 72 declarations are
renamed at promotion (the port's content names, playbook §5), so each would need its own `pin:` marker
to be diffed — 68 markers per module for zero verification beyond what the two `S_` files already
give. The surface is therefore **tier 3**: public, built, importable, and listed in
`spec/UNWIRED-PUBLIC.md` (the register grew by 144 declarations). This is the same economy the live
modules' 55 `private` declarations represented, made **visible** instead of hidden — and the two
headlines that consume it *are* wired, so the set's checked surface is its two statements.

### 1.6 The worker's landing — two modules, one dispatch

[WORKORDER-AF6-archderiv-rightconv.md](WORKORDER-AF6-archderiv-rightconv.md) was dispatched as one
fresh session and closed clean: no blocker, nothing left unwritten, R2 compiled **first try** by the
pin's own vocabulary map.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| R1 | `Adelic/ArchDerivRightConv.lean` (**new, 802 → 696** after §1.7's triage: the pin's 35 remaining private declarations + 1 public headline) | **1 ok** / 0 / 0 | silent, **7.6 s** fresh | clean |
| R2 | `Adelic/ArchDerivRightConvComplex.lean` (**new, 808 → 702** after §1.7) | **1 ok** / 0 / 0 | silent, **16 s** fresh | clean |
| — | consumer probe `spec/AutomorphicFormSetAF6Consumer.lean` (**new, 144**, 4 zones, 9 examples) | — | 0 errors | — |

`dedup --within`: 36 declarations per module, **0 clusters**. The 802/808 as first written against the forecast ≈720 is
the pin's own line-breaking plus 11 `set_option linter.style.haveILetI false in` per module (§5 trap 5);
the *declaration* count is exactly the priced 42.

**What the promotion bought, measured.** The worker's act 1 was the statement check §0.5 demanded, and
it came back clean three ways: a full read of `FactorizableTestFnArchSmoothLeft` (593 lines) against pin
`:35`–`:557`; a name-keyed signature comparison of the two port engines under the rename map
(`72 / 72, 0 mismatches`); and the decisive one — **the pin's own proof text elaborates against every
imported statement**, which a differing statement would not accept. Appendix A's "66 rows" are **72
declarations** (its grouped rows expand), and **72 are imported, 0 needed a local re-statement**, 25 of
them named directly in the new code. So the transcription was **41 private + 1 headline per module** —
Appendix B's 47 over-counted by five (§1.6 correction below) and the true per-file total is **42**.

**Appendix B's correction.** `tc_isOpen_detSet`, `tc_of_tcInv`, `tc_det_tcInv`,
`tc_contDiffOn_tcInv` and `tc_tcInv_mem` are *also* Appendix-A imports — at the port names
`chart_isOpen_nonsingEntries`, `chart_of_invEntries`, `chart_det_invEntries`,
`chart_contDiffOn_invEntries`, `chart_invEntries_mem`, which the brief's rename map missed because the
port renamed the *subject* (`detSet` → `nonsingEntries`) and not only the prefix. So 114 pin
declarations − 72 imported = **42 to write**, which is what the modules hold.

**Deviations, all measured, none a statement change:**

1. **One import the workorder's list omitted**: `NumberTheory/AdelicHaar/MulRightInvariant`.
   `l5_integral_E_eq` needs `AdelicHaar.isMulRightInvariant_adelicGLHaar`, which the pin reaches
   through `Theorems/Thm_NumberField_AdelicHaar_isMulRightInvariant_adelicGLHaar` (pin line 23); the
   worker verified it is required (deleting it gives `Unknown identifier`). **The order's import list
   was built from the `Def_` closure and missed a `Thm_` premise of the proof** — FR-0099's class, one
   layer over.
2. **Two v4.34 drifted spellings** (§5 trap 8, new): `if_pos`/`if_neg` inside a `by_cases … rw` are
   `ite_eq_left`/`ite_eq_right`; and `hasFDerivAt_integral_of_dominated_of_fderiv_le`'s `(x₀ := e₀)` no
   longer names a binder, so it goes positionally with `(𝕜 := ℝ)`. Two occurrences of each per module.
3. **`liftM` is ambiguous with Mathlib's `_root_.liftM`** inside a `simp only` list, so it is qualified
   `IsFactorizableTestFn.liftM` — a consequence of the *promotion's* naming (`liftM` for the pin's
   `e8l5M`) that will hit the next consumer: FR-0107.
4. **The 41 new declarations keep the pin's file-local names** (`l5F`, `l5E`, `l5E'`, `TcFamily`,
   `tc_*`, `af_*`): the port has never carried them at another name, they are `private`, and keeping
   them makes the pin↔port diff mechanical. Of §5's seven traps, three were non-issues on v4.34 (the
   `ContDiff ℝ ⊤ = ∞` coercion, `fun_prop` after `fin_cases`, `exact_mod_cast`).
5. **Conjunct 2 uses the imported `lift_leftDeriv_tensor`** where the pin re-proves its inline copy —
   the promotion's entire point. Each of the nine restored declarations is consumed.

**The dead tail: triaged, shelved and deleted (§1.7).** `move_dead --dry-run` reported 6 declarations /
109 lines per module — the one gate that did not read 0, because a whole-node transcription carries the
pin's own unreachable mathematics (playbook §3.8: *"Port it… the porting-time pass is dedup only"*).
They are now triaged and disposed of: **one deleted** (a duplicate of something the port already has
publicly) and **five shelved** into `Reserve/`. Both modules read **0 declarations / 0 lines** afterwards.

### 1.7 The dead tail's disposition — the triage rule applied

The rule: **dead mathematics goes to `Reserve`; anything that is not mathematics — or is a duplicate of
something the port already states — is deleted.** `move_dead`'s report is triaged, never applied blindly.

| declaration | lines | verdict | why |
|---|---:|---|---|
| `l5_continuous_rightConv` | 56 | **deleted** | `Continuous (rightConv K φ α)` for factorisable `α` **is the first conjunct** of SET-AF5's public, checked, imported `AutomorphicForm.continuous_rightConv_and_contDiff_of_isFactorizableTestFn`. Not dead content — a *duplicate* of a stronger port statement, and playbook §2.4's answer to a duplicate is deletion, not a shelf |
| `l5_isArchSmoothAt_comp_inv` | 22 | **shelved** | real mathematics: `IsArchSmoothAt hw (α ∘ (·)⁻¹)` from the chart of `α` — the port's own objects, nowhere else |
| `l5_rightConv_add_right` | 13 | **shelved** | real mathematics: `rightConv` is additive in its test function |
| `l5_rightConv_smul_right` | 12 | **shelved** | real mathematics: the scalar version |
| `l5_leftDeriv_inv` | 7 | **shelved** | real mathematics: the bridge `leftDerivFactor hw d α y⁻¹ = archDerivAt hw d (α ∘ (·)⁻¹) y` |
| `tc_integrable_zero` | 7 | **shelved** | real mathematics: the `n = 0` case of the `TcFamily` integral engine |

`move_dead --select dead --copy` executed the five, taking their three live premises (`TcFamily`,
`l5_integrable_conv_integrand`, `tc_aesm_of_zero`) along so each shelf imports the port's public API
only:

| file | lines | declarations | build | dedup |
|---|---:|---:|---|---|
| `Reserve/AutomorphicForm/Adelic/ArchDerivRightConvDead.lean` | **172** | 8 (5 dead + 3 premises) | silent | 0 clusters |
| `Reserve/AutomorphicForm/Adelic/ArchDerivRightConvComplexDead.lean` | **173** | 8 | silent | 0 clusters |

The live modules went **802 → 696** and **808 → 702** (−56 deleted, −63 moved out, +12 structural lines
restored after the first hand cut, +1 linter option each), and every gate is now green with **0**, not
"0 expected":

| gate | R1 | R2 |
|---|---|---|
| `check_port` | **1 ok / 0 / 0** | **1 ok / 0 / 0** |
| `move_dead --dry-run` | **0 declarations / 0 lines** | **0 / 0** |
| warnings | **0** | **0** |
| axioms | clean | clean |

**The repair worth recording (FR-0108).** The first cut was made by hand from the declaration's start
line to the *next declaration's* start line — which swallowed `end TestData`, `section EngineBridge`,
`open MeasureTheory Metric Set`, `section Engine` and the two `variable` lines that sat between
`l5_continuous_rightConv` and `private structure TcFamily`. The module stopped elaborating with
`Unknown identifier X / Y / ν` 60 lines away from the cut. `move_dead`'s own docstring is the rule
("**span ≠ text** … cut by `body_end`, and never let a moved block contain a column-0
`namespace`/`section`/`end`"); a hand cut must stop at the end of the *body*, not at the next
declaration.

## 2. What the two rows say

**R1 (1,246).** Bindered `(K) [Field K] [NumberField K] {w : InfinitePlace K} (hw : w.IsReal) (d : ArchDir)`;
the three conjuncts are §1.1's. The proof is the pin's five sections: `LiftAnalysis` (the chart of the
test factor), `AffineData` (the affine family `af_family` — the "closed form" of the chart along the
flow), `TestData`, `EngineBridge` (the engine `l5_archDerivAt_rightConv` and the affine slice
`l5_continuous_rightConv`), `Conv` (the `ε`-estimate and the `E`/`E'`/`F` family that turns the
`deriv` into an integral), and `LeftDerivFactor` (the tensor form). The headline is the pin's
`solution`, 27 lines.

**R2 (1,248).** The same, at `hw : w.IsComplex`, `d : ArchDirComplex`, `archDerivAtComplex`,
`IsArchSmoothAtComplex`, `archFlowAtComplex`, and the `ℂ`-valued chart. Every declaration is the real
one under the vocabulary map; the two proofs that are *not* a pure map in the pin are the
`ContDiffOn`-`div`-vs-`inv`-`mul` step (the same one the ArchSmooth pair has, already recorded in that
module's header) and the `ringEquivComplexOfIsComplex` chart identification.

## 3. Homes — two new modules, above the engine

| step | home | why not the alternative |
|---|---|---|
| R1 | **new** `AutomorphicForm/Adelic/ArchDerivRightConv.lean` | the row is *above* `FactorizableTestFnArchSmooth{Left}` (its premise engine), `RightConvolution` and `RightConvRegularity`, and *above* the definition modules `ArchDerivCasimir`. No existing module is above all of them, and `ArchDerivCasimir` itself is below them (it is a `Def_` transcription). 0 importers → cascade-free |
| R2 | **new** `AutomorphicForm/Adelic/ArchDerivRightConvComplex.lean` | **must be a separate module**: the two engines share 52 last names, so a module importing both cannot exist (the port's own `FactorizableTestFnArchSmooth` vs `…Complex` precedent, and its header records exactly this clash) |

Both modules import the *same* two engine modules plus the AF5/earlier ones:

```lean
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft      -- R1 (Complex for R2)
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir                    -- (…Complex for R2)
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplexAPI
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear
```

**Import direction, checked by hand**: every one of those is at or below the new module, and neither
new module is imported by anything (0 importers). The one thing to *not* do is put R1 and R2 in one
module (name clash) or inside `FactorizableTestFnArchSmoothLeft` (a `Def_`-level subject whose module
would then import `RightConvolution` — a cycle).

## 4. Ground prep (the manager's) — done

1. **M1/M2** the two promoted left-half modules (§1.5), public, with the nine restored declarations.
2. **M3** the two `Reserve` shelves deleted, the two live modules' headers repointed,
   `CARRY-FORWARD.md`'s entry resolved, the register regenerated.
3. **Nothing else**: no `Def_` node (the layer is complete), no marker row, no `PORT_FILES` change, no
   new `spec-pin` wire, no migration — the two `Def_` modules this set transcribes (`ArchDerivCasimir`,
   `ArchDerivCasimirComplex`) are already `spec-pin:`-wired and checked.

## 5. The traps (for the worker)

**Measured from the pin, in the order they bite.**

1. **The two files are the same proof, and the port's `port once` block is the *prelude*, not the
   content.** Write R1 first, completely; then R2 is the vocabulary map plus the two exceptions §2
   names. Do **not** try to share the 47 new declarations between the two modules: they differ in the
   flow (`archFlowAt` vs `archFlowAtComplex`), the chart (`ArchEntry = Fin 2 → Fin 2 → ℝ` vs `… → ℂ`)
   and the derivative (`archDerivAt` vs `archDerivAtComplex`) — that is precisely why the pin wrote the
   pair twice and why the port's ArchSmooth pair is two modules.
2. **`leftDerivFactor`, not `archDerivAt`, on the moving side.** The derivative of `y ↦ α (archFlowAt hw d (-t) * y)`
   at `t = 0` is the **left** derivative; `archDerivAt` is the right one. Conflating them is the one
   error that produces a *false* statement rather than a failed proof: `lift_leftDeriv_eq` (importable)
   is the bridge.
3. **The `ε`-estimate is on `E`/`E'`/`F`, not on `φ`.** The `Conv` section's whole point is that
   `deriv (fun t => α (…) * ff (…)) 0` is a limit of an integral family whose domination is the
   *chart's* compact support (`lift_exists_compact_support`, importable), not `α`'s.
4. **`af_family` (57 lines) is new and is the set's real mathematical content**: the closed form of the
   chart along the flow (`af_iteratedFDeriv`, `af_continuous_closedForm`). It has no port twin — write
   it, do not look for one.
5. **`IsArchSmoothAt` is a `def` over the chart, so `archDerivAt`'s defining property is only available
   through the port's `ArchDerivCasimirComplexAPI` lemmas** (`IsArchSmoothAtComplex.archDerivAtComplex`
   and friends) — check the API module before re-deriving anything about the derivative.
6. **`set_option linter.style.haveILetI false in`** on any declaration whose proof is the pin's
   `letI := glBorel` / `haveI := borelSpace_…` wall (the AF5 precedent, four warnings otherwise).
7. **`exact_mod_cast` / `Nat.cast`**: `ContDiff ℝ (⊤ : ℕ∞)` still lands as `∞` in v4.34 (AF5 measured
   it), and the pin's `(⊤ : ℕ∞)` arguments need no edit.

## 6. The gates, per module

1. `python3 spec/check_port.py --force <module>` → **1 ok / 0 mismatch / 0 missing** (the headline is
   the module's only public declaration; the prelude stays `private`).
2. `#print axioms` on the two headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout 280`, silent, **zero warnings**; no tree build.
4. `dedup.py --within` (report, do not refactor) and `move_dead.py` — **triage, then drive it to 0**:
   dead *mathematics* goes to `Reserve` (`--select dead --copy`), a *duplicate* of a port statement is
   deleted, and a `local instance` report is FR-0104's false positive. §1.7 is the worked instance
   (six declarations in, one deleted + five shelved out).
5. No `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats` unless reported as a
   finding.
6. A **zone per row** appended to `spec/AutomorphicFormSetAF5Consumer.lean`? **No** — a new probe
   `spec/AutomorphicFormSetAF6Consumer.lean`, two zones (one per row), each a real composition: read
   the headline's first conjunct at a concrete `g` and compose it with `RightConvRegularity`'s
   continuity (so the zone dies if either module goes), and compose the third conjunct with the second
   for the adjointness at `ω ≡ 1`.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. **the cut** | **the two ready rows only** (2,494 silo ≈ 985 net) | the eight leaves (1,510 silo / 1,001 net) are a different subject and would treble the order |
| 2. **the promotion** | **promote the left half out of `Reserve` to two public modules**, restore the nine lost declarations | 491 of each file's 1,246 lines become imports; it is what the shelf's own header prescribed, and the rows cannot be stated at the port's names otherwise |
| 3. **no `spec-pin` wire on the promoted modules** | **tier 3, registered** | 68 markers per module for no verification the two wired headlines do not already give |
| 4. **homes** | **two new modules**, `ArchDerivRightConv{,Complex}` | name clash forbids one; the `Def_` module is below the premises |
| 5. **the dispatch** | **one worker order, R1 then R2** | R2 is R1 by substitution; one order is right for a 1,450-line transcription |
| 6. **the eight leaves** | **SET-AF7** | they are the Casimir/commutator algebra, and `archDerivAtComplex_commutator_…` alone readies four rows (return 1,443) |

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af6.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes <both rows> --json build/af6.json && python3 port_plan.py --json build/af6.json
python3 twin_scan.py --node <each row>          # new, new
cd ../lean
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_ArchDerivCasimir.lean \
    --rows S_AutomorphicForm_archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn
timeout 300 python3 spec/old_check_stmts.py     # corpus unchanged: 6,949 / 3 / 18
```

**What the set consumes**: 2 rows / 2,494 silo; **≈985 net new math lines** (≈1,450 transcribed, of
which the prelude's 491 per file is imported); 2 new modules, 2 wire lines each; 1 promotion of 1,190
lines out of the `Reserve` shelf with 9 declarations restored; 0 `Def_` nodes; 0 markers; 0
migrations; 0 tree builds.

**The measured re-read, and the one figure the forecast got wrong.** The forecast below was written
before the order was dispatched; the measured column is `frontier.py` re-run on the landed tree,
without `--unport` or any correction:

| figure | before | forecast | **measured** |
|---|---:|---:|---:|
| `needed [F terminal]` | 898 / 370,450 | 896 / 367,956 | **896 / 367,956** ✓ |
| `needed [literal]` | 911 / 373,925 | 909 / 371,431 | **909 / 371,431** ✓ |
| frontier F | 1,517 / 756,916 | 1,519 / 759,410 | **1,519 / 759,410** ✓ |
| ready rows, all namespaces | 71 / 29,663 | 70 / 27,383 | **71 / 28,162** ✗ |
| `AutomorphicForm` ready rows | 42 / 24,319 | 41 / 22,039 | **42 / 22,818** ✗ |
| `AutomorphicForm` leaves | 80 / 16,549 | 80 / 16,549 | **80 / 16,549** ✓ |
| withheld | 4 / 831 | 4 / 831 | **4 / 831** ✓ |
| `--selfcheck` | PASS | PASS | **PASS** (1,354 `Thm_` / 1,519 names) |

**Why the ready block missed by one row / 779 silo — a measured instrument limitation.** The set readied
**two** rows, not one: besides the 214-line
`isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar` (return 214), it readied
`AutomorphicForm.archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt` (**779**),
whose unported premise set was **both** rows — so neither row's *per-row* readiness return could see it
and the brief's arithmetic summed two single-row returns instead of taking the set's closure return. This
is the *same* blindness SET-AF4 §8 recorded after its landing ("a thirteenth row was waiting on the
determinant row too and was missed by the §0.3 instrument — it had no *single* unported premise, it had
several, all inside the set"), and it is now the rule: **a set's forecast is
`return(set) = Σ silo of the unported cone rows whose unported premise set ⊆ the set`, never the sum of
its rows' `return`** (FR-0106).

## 9. What this set does not do

- **The eight leaves of the family** (1,510 silo / 1,001 net): deferred to SET-AF7, which is the
  archimedean-derivative *algebra* — Casimir, the `[E, Fm]` commutator, the character identities, the
  row-isometry invariance. `archDerivAtComplex_commutator_of_isArchSmoothAtComplex` (401, return 1,443)
  is that set's key.
- **The two rows it readied, unwritten**: `archCasimirAt_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAt`
  (**779**, the one the forecast missed) and `isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite_ofChar`
  (214). Both are Casimir rows, so they belong to SET-AF7 rather than to a set of their own — and the
  779-line one *is* the archDeriv↔Casimir bridge, i.e. the natural headline of that set.
- **The dead tail is disposed of, not carried** (§1.7): one deletion (`l5_continuous_rightConv`, a
  duplicate of SET-AF5's public headline) and five shelved declarations per module, so both live modules
  read 0 dead. Nothing of the pin's is lost and nothing dead stays in the tree.
- **The leftCasimir family behind the commutator leaf** (`leftCasimirComplex_eq_archCasimirAtComplex_…`
  1,227): that is SET-AF7's own headline.
- **No `Def_` node, no marker row, no `spec-pin` wire on the promoted modules, no migration, no tree
  build.** The promotion and the nine restorations are the whole metadata surface of the set.

## Appendix A — the promoted engine: what R1 imports instead of transcribing

Measured by the rename map on the pin's `S_` file (the complex file's 113 declarations are the same set,
so R2 imports the same declarations from `…ComplexLeft`). **The list's 66 rows are 72 actual pin
declarations** (the grouped rows expand: `l5Curve` = 4 names, `l5M`/`l5cD`/`l5LD`/`l5Phi'` = 2 each,
`Ent`/`tcDetSet`/`l5Ent`/`leftDeriv` = 1 each) **/ 491 of 1,246 pin lines** — and the landing imported
**all 72, 0 restated** (§1.6). The worker must confirm each statement before skipping it (the tool
cannot see renamed copies).

| pin declaration | importable port declaration | pin lines |
|---|---|---:|
| `l5AddHom` | `IsFactorizableTestFn.liftAddHom` | 13 |
| `l5Theta` | `IsFactorizableTestFn.liftTheta` | 12 |
| `l5Lin` | `IsFactorizableTestFn.liftLin` | 7 |
| `l5LinMat` | `IsFactorizableTestFn.liftLinMat` | 11 |
| `l5LinMat_apply` | `IsFactorizableTestFn.liftLinMat_apply` | 4 |
| `l5MulR` | `IsFactorizableTestFn.liftMulR` | 3 |
| `l5MulR_apply` | `IsFactorizableTestFn.liftMulR_apply` | 3 |
| `l5MulRL` | `IsFactorizableTestFn.liftMulRL` | 9 |
| `l5MulL` | `IsFactorizableTestFn.liftMulL` | 3 |
| `l5MulL_apply` | `IsFactorizableTestFn.liftMulL_apply` | 3 |
| `l5MulR_eq_mulL` | `IsFactorizableTestFn.liftMulR_eq_mulL` | 2 |
| `l5single` | `IsFactorizableTestFn.liftSingle` | 3 |
| `l5Const` | `IsFactorizableTestFn.liftConst` | 4 |
| `l5Ent` | `IsFactorizableTestFn.liftEntry` | 2 |
| `l5Curve` *(+ `l5_curve_mem`, `l5_hasDerivAt_curve`, `l5_curve_det`)* | `liftCurve`, `lift_curve_mem`, `lift_hasDerivAt_curve`, `lift_curve_det` | 12 + 6 + 4 + 2 |
| `l5_archFlowAt_eq_lift` | `IsFactorizableTestFn.lift_archFlowAt_eq_lift` | 8 |
| `l5_archFlowAt_inv` | `IsFactorizableTestFn.lift_archFlowAt_inv` (restored) | 3 |
| `l5_glFin_archFlowAt` | `IsFactorizableTestFn.lift_glFin_archFlowAt` (restored) | 4 |
| `l5M` *(+ `l5_continuous_M`)* | `liftM`, `lift_continuous_M` | 2 + 4 |
| `l5cD` *(+ `_continuous_cD`)* | `liftCD`, `lift_continuous_cD` (restored) | 2 + 4 |
| `l5LD` *(+ `_continuous_LD`)* | `liftLD`, `lift_continuous_LD` | 2 + 4 |
| `l5Phi'` *(+ `l5_contDiff_Phi'`, `l5_hasDerivAt_Phi_curve`, `l5_hasCompactSupport_Phi'`)* | `liftPhi'` and its three lemmas | 5 + 4 + 6 + 12 |
| `l5_fa_lift_mul`, `l5_factor_lift_mul`, `l5_glFin_lift`, `l5_glFin_archRealGLAt`, `l5_lift_inv`, `l5_of_archEntries`, `l5_continuous(On)_*` (Theta, lift, addHom, ringEquiv, archEntries, mulR), `l5_archEntries_*` (5), `Ent`, `tcDetSet`, `tcInv`, `tc_*` (chart) | the `lift*`/`chart_*` twins of the same names | (the rest of 491) |

## Appendix B — what the worker transcribes (47 rows / 694 pin lines, **42 declarations**)

**Corrected at the landing (§1.6):** the first five rows of the list below — `tc_isOpen_detSet`,
`tc_of_tcInv`, `tc_det_tcInv`, `tc_contDiffOn_tcInv`, `tc_tcInv_mem` — are *also* Appendix-A imports, at
the port names `chart_isOpen_nonsingEntries`, `chart_of_invEntries`, `chart_det_invEntries`,
`chart_contDiffOn_invEntries`, `chart_invEntries_mem` (the brief's rename map missed them because the
port renamed the subject, not just the prefix). So **114 pin declarations − 72 imported = 42 written**
(41 `private` + the headline), which is exactly what the two modules hold. The row list is kept as
issued, since it is the record of the order.

| pin declaration | lines | note |
|---|---:|---|
| `l5_archDerivAt_rightConv` | 62 | **the engine**: the derivative of the integral |
| `af_family` | 57 | the affine family / closed form along the flow |
| `l5_continuous_rightConv` | 56 | continuity of `rightConv` in the chart |
| `l5_rightConv_archDerivAt_mul` | 44 | the integration-by-parts identity (conjunct 3) |
| `l5_hasDerivAt_integral_E` | 37 | the `E`-family derivative under the integral |
| `l5_hasDerivAt_orbit` | 28 | the orbit derivative |
| `solution` | 27 | the headline itself |
| `l5_isArchSmoothAt_rightConv` | 26 | **conjunct 1's smoothness half** |
| `l5_isArchSmoothAt_comp_inv` | 22 | |
| `l5_continuous_archFlowAt` | 22 | |
| `tc_contDiffOn_integral_nat` | 20 | the `tc_*` integral engine |
| `tc_deriv_integral_comp` | 18 | |
| `l5_tcFamily` | 18 | |
| `tc_hasFDerivAt_integral` | 17 | |
| `af_continuous_closedForm` | 15 | |
| `l5_rightConv_lift_eq` | 15 | |
| `l5_integral_E_eq` | 14 | |
| `l5_integrable_conv_integrand` | 13 | |
| `l5_rightConv_add_right` | 13 | |
| `l5_archDerivAt_eq_zero_of_notMem` | 13 | |
| `l5_rightConv_smul_right` | 12 | |
| `l5_exists_segment_compact` | 12 | |
| `tc_aesm_of_zero`, `tc_aesm_fderiv_order` | 11 + 11 | |
| `af_iteratedFDeriv` | 10 | |
| `l5F_eq`, `TcFamily`, `tc_integrable_fderiv`, `l5_continuous_E'`, `tc_integrable_zero`, `l5_leftDeriv_inv`, `l5_hasCompactSupport_mul`, `l5_continuous_E`, `tc_isOpen_detSet`, `l5_hasCompactSupport_archDerivAt`, `l5_E'_eq_zero`, `tc_of_tcInv`, `l5E'`, `l5_hasDerivAt_E`, `tc_det_tcInv`, `tc_contDiffOn_tcInv`, `tc_tcInv_mem`, `tc_differentiableAt`, `tc_contDiffOn_integral`, `l5F`, `l5E`, `tc_norm_fderiv_eq` | 3–8 each | |
| **47 rows (42 declarations, §1.6)** | **694** | plus the 35 boilerplate lines |
