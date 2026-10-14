# WORKORDER-KF1 — the local-finite-type engine for K-finite continuous families (tier 3)

Port the self-contained proof body behind the Deligne–Serre leaf

`AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous` —

the adelic `AutomorphicForm` graph leaf that `frontier.py --ds --include-leaves --rank-by silo`
shows as **rank #2 of 470** (1,523 silo lines; behind only `M4aTorus.completedRayL_fe`), and
**rank #1 of the 102 `AutomorphicForm` leaves**. It is a leaf (`cites 0`), so `--ready` and
`--hops` hide it; it appears only under `--include-leaves`. Its one consumer is
`AutomorphicForm.exists_flat_isInducedSection_sum_eq_of_differentiable_family`, on the
Rankin–Selberg chain to `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
(§7 Gate 1 of [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md)) — i.e. this is the
automorphic-gate layer, **not** a `ModularCurve` ready-shelf row.

The scoping this order executes is `tools/deps/build/isOpen_advise.json` (its `port_advise`
output and its `port_plan` budget); the worker re-runs both at the end for parity (§6).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`. Checker baseline (measured on this tree, 2026-10-14): **9789 identical
(671 promoted, 83 renamed), 0 mismatched, 0 missing, 38 own (9827 checked)**. Target after the
manager's wire: `identical` **+1** (the headline) and `0 mismatched / 0 missing`; the worker's
two tier-3 engines are registered, not diffed (§8).

## 1. Scope

Port **whole** (playbook §2.3) the one self-contained pin `S_` file —
`P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean`,
**1,523 raw / 1,492 net new math lines**, **89 declarations in 89 groups**, **0 duplicates**,
**0 vetted substitutions** (the one the parser reports is a false match — §3), **1 public
headline** and 88 `private` declarations, of which **74 are the headline's own proof closure**
(≈1,259 lines) and 14 sit outside it (bundled instances and injectivity/glue lemmas, transcribed
whole per playbook §2.3).

The file is nine namespaces in one chapter, and it splits on a real mathematical fork — the
generic representation-theoretic engine (no adèles, no `GL₂`) versus the adelic instantiation:

| pin lines | namespace | role | module |
|---|---|---|---|
| 28–110 | `EvalMatrix` | a finite matrix of evaluations: `linearIndependent` ⟺ a nonzero minor | M1 |
| 112–329 | `UniformRank` | `TranslatesFinite`, the translate linear map `rt`, and the Baire/finite-rank **core** `exists_isOpen_subset_forall_det_ne_zero_and_mem_span` | M1 |
| 331–392 | `CoefficientSpan` | the coefficient span of a matrix-valued family and its finite dimensionality | M1 |
| 394–452 | `SliceSpan` | slices of a family and the finite expansion of a `π`-span-valued slice | M1 |
| 454–490 | `SliceCoefficients` | the slice coefficients lie in the coefficient span | M1 |
| 792–932 | `AveragedIntertwiner` | averaging an intertwiner law against probability Haar on a compact group | M1 |
| 935–1081 | `TranslationCoordinates` | matrix coordinates `Mm`/`Nm`, the multiplication law, continuity, and the finite-coordinate conclusion | M1 |
| 492–789 | `ArchimedeanIsometryGroup` (two blocks) | `Kinf`, `box`, `isCompact_Kinf`, `haarProb`, `incl`, `translatesFinite_range_incl`, the covering helpers | M2 |
| 1084–1449 | `LevelInvariance` | `congrSet`, the ideal-ball layer, `liftFin`/`finIncl`, `entryBall`, the `closure congrSet` covering | M2 |
| 1452–1521 | (chapter level) | `solution` → the public kernel | M2 |

M1 is the generic engine that the sibling silos re-derive under other names (the archTestFactor
family — [TOPIC-archTestFactor-family.md](TOPIC-archTestFactor-family.md) — homed its own
movements 3–4 the same way, as `RepTheory/TypeReproducer.lean` and `RepTheory/ConvolutionLimit.lean`).
M2 is the adelic instantiation plus the headline.

**Explicitly not this order.** The tier-1 façade and all checker wiring (§8); the
`ArchInfra`/`EntryBall` reconciliation and any other `private` → public promotion (a manager
generalisation round, §3); the four consumer silos of the archTestFactor note; the Deligne–Serre
gates; any `Definitions/` edit; the pin's `p2m_reactivate` / `#print axioms` / `P2M.Util`
plumbing and its `attribute`/`set_option` preludes.

## 2. Sources and deliverable

Statements come from the pin `Theorems/` wrapper; proofs from the `P2M/Sol/S_` file:

* statement — `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean`
* proof — `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean`

The local clone `~/proj/fermats-last-theorem` is the working copy. The wrapper is one
`p2m_exact_reverting` line and is the authority for the statement, never the `S_` file's
`solution` spelling. The statement, verbatim (binders, order and spellings are the checker's
contract — copy it, do not retype it):

```lean
theorem AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
    (F : Type) [Field F] [NumberField F]
    (φ : ℂ → AdelicGL2 (𝓞 F) F → ℂ)
    (_hφK : ∀ s, IsArchKFinite F (φ s))
    (_hφf : ∀ s, IsKfSmooth F (φ s))
    (_hφjc : Continuous (fun p : ℂ × AdelicGL2 (𝓞 F) F => φ p.1 p.2)) :
    ∃ U : Set ℂ, IsOpen U ∧ U.Nonempty ∧
      ∃ (n : ℕ) (σ : Fin n → ℂ), ∀ s ∈ U, ∃ c : Fin n → ℂ, ∀ k : AdelicGL2 (𝓞 F) F,
        glFin (𝓞 F) F k ∈ finiteIntegralGL2 (𝓞 F) F →
        (∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F k))) →
        φ s k = ∑ i, c i * φ (σ i) k
```

**Deliverable — two new tier-3 worker modules, in import order.**

* **M1** `FLTForHuman/RepTheory/TranslateSpan.lean` — the generic engine; the seven generic
  namespaces of §1, **public at the pin's names** (the `RepTheory/TypeReproducer.lean`
  precedent: a real cross-theory engine stays public and is registered, not `private`), with a
  header stating the subject, the pin and the two landed reuse edges.
* **M2** `FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamily.lean` — namespace
  `AutomorphicForm.ArchKFiniteFamily`, holding the pin's `ArchimedeanIsometryGroup` and
  `LevelInvariance` namespaces; the adelic helpers `private` at the pin's names; **one public
  kernel** at the wrapper's statement:

  `AutomorphicForm.ArchKFiniteFamily.Engine.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous`

`-- pin: <name> (S_<stem>.lean:<line>)` above every **public** declaration (the tier-3 register
reads it there; on `private` helpers it is optional, for traceability only). No other file is
created or edited; neither module is wired (`PORT_FILES`) in this order.

## 3. Transcription rules, reuse, and the hub prohibition

* Replace the pin's mangled chapter (`P2MW.S_<stem>`) by the port's namespaces; **keep every
  declaration name and every sub-namespace verbatim** (`EvalMatrix`, `UniformRank`,
  `CoefficientSpan`, `SliceSpan`, `SliceCoefficients`, `AveragedIntertwiner`,
  `TranslationCoordinates`, `ArchimedeanIsometryGroup`, `LevelInvariance`). The helpers are
  referenced across namespaces (`UniformRank.TranslatesFinite`, `LevelInvariance.congrSet F`,
  `TranslationCoordinates.exists_forall_one_and_mul_and_continuousOn_and_eq_sum`), and the
  pin's text of those references is what the port must reproduce. A port prefix would move it.
* Proof bodies are transcribed and adapted, never restated. **The definition gate is closed** —
  all three imports are landed and were hand-checked declaration by declaration:
  `Definitions/Def_AutomorphicForm_ArchKFinite` → `AutomorphicForm/Adelic/ArchKFinite.lean`
  (9/9 declarations), `…Def_AutomorphicForm_SmoothAutomorphicFnAt` →
  `AutomorphicForm/Adelic/SmoothAutomorphicFn.lean` (16/16), `…Def_NumberField_AdelicBox` →
  `NumberTheory/AdelicBox.lean`. The three pin declarations absent from the `AdelicBox` module
  are already in the port under their pin names in `NumberTheory/AdelicLevel/IdealBall.lean`:
  `integralFiniteAdeles`, `algebraMap_mem_adicCompletionIntegers`, `valued_algebraMap`. The
  proof's own definition uses (`IsRowIsometry`, `archComponent`, `glArch`, `glFin`,
  `finiteIntegralGL2`, `finiteAdelicGL2Subgroup`, `archRowIsometrySubgroup`, `idealBall`,
  `idealBound`) all resolve through those modules; `IsRowIsometry` reaches the engine via
  `ArchKFinite.lean → ArchType.lean → WindowedSiegel/RowIsometry.lean`. Nothing needs an import
  outside the landed cone; a module the editor needs is added explicitly and reported.
* **The one `port_advise` "substitution" is a false match — do not apply it.** It pairs the pin's
  `box` with `AutomorphicForm/Adelic/ArchApproxIdentity/EntryBall.lean`'s `detLocus` on the bare
  type `Set (Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))` (the parser's type-only `def` match,
  playbook §4(b)). The bodies are different: pin `box = {m | ∀ i j w, ‖m i j w‖ ≤ 1}` (norm-≤1
  entries) against port `detLocus = {m | ∀ w, m.det w ≠ 0}`. Transcribe `box` privately in M2.
  This is the note's §4(b) counterexample; record it in the report.
* **Reuse that is real, with an adapter.** `ArchInfra.norm_entry_le_one`
  (`ArchApproxIdentity/ArchInfra.lean:197`) is the *matrix* / `rowIsoSet` form of the pin's
  *unit* / `IsRowIsometry` lemma (`ArchimedeanIsometryGroup.norm_entry_le_one`); bridge via
  `ArchInfra.mem_rowIsoSet_iff`, or keep the pin's 5-line private form and report the
  near-duplicate. Do not edit `ArchInfra.lean`.
* **Reconciliation candidates — report, do not resolve.** Four of the pin's `private` objects
  are mathematical neighbours of `private` objects already in the port but are **not statement
  twins**, because the carriers differ: `UniformRank.TranslatesFinite` (set-indexed) against the
  public `AutomorphicForm.RightTranslatesSpanFinite` (subgroup-indexed, `ArchKFinite.lean`);
  `UniformRank.rt`/`rt_apply` against `RepTheory/TypeReproducer.lean` and
  `AutomorphicForm/Adelic/PeterssonSlabPairing.lean`'s binder variants; and the whole
  `Kinf`/`incl`/`haarProb`/`box`/`entryBall` layer against `ArchInfra.Kw`/`Kprod`/`inclArch`/
  `inclAdelic`/`muK`/`rowIsoSet` and `EntryBall.entryBall` (subgroup of `GL` versus `Π w, K_w`
  carrier; adelic `GL₂`, `ℕ`-indexed versus archimedean `Matrix`, `ℝ`-indexed). Transcribe the
  pin's private forms; a generalisation/dedup of any of these is the manager's own round, never
  this order's.
* Apply the `v4.34.0` drift checklist (playbook §7) as it appears. Known sites:
  `mem_setOf_eq` → `mem_ofPred_eq` (the landed `ArchInfra.mem_rowIsoSet_iff` already uses it),
  `ite_eq_left`/`ite_eq_right` for `if_pos`/`if_neg`, `Matrix.of_apply`, and the
  `Units.isInducing_embedProduct` / `Units.isEmbedding_embedProduct` / `isOpen_ne_fun` /
  `Submodule.mem_span_finite_of_mem_span` / `nonempty_interior_of_iUnion_of_closed` interfaces of
  the Baire core. Do not transcribe the pin's `set_option`/`attribute` preludes; if a `simp`
  call relied on one, write the rewrite.
* Keep the five `private scoped instance`s (`instCompactSpaceKinf`, `instMeasurableSpaceKinf`,
  `instBorelSpaceKinf`, `instIsProbabilityMeasureHaarProb`, `instIsMulLeftInvariantHaarProb`) in
  M2's `ArchimedeanIsometryGroup` namespace. The kernel activates them through
  `open ArchimedeanIsometryGroup in`; a global (unscoped) instance is a build-cost and
  collision risk and is not authorised.
* **Hub prohibition.** A helper you need stays `private` here and is reported; you never promote,
  rename, or edit an existing module. If you believe a promotion is genuinely required, **stop
  and report** the declaration, the intended host and the `build_ladder.py --edit` price
  (`python3 tools/deps/build_ladder.py --edit FLTForHuman/<host>.lean`); the manager decides.

## 4. Named risks and stop conditions

Named risks, in the order they will bite — the large helpers from `port_advise`'s drags:

| helper | pin line | lines |
|---|---:|---:|
| `exists_isOpen_subset_forall_det_ne_zero_and_mem_span` | 227 | 108 |
| `translatesFinite_range_incl` | 674 | 64 |
| `exists_forall_mem_exists_forall_eq_sum` | 406 | 52 |
| `exists_finset_subset_forall_mem_span` | 134 | 49 |
| `exists_forall_one_and_mul_and_continuousOn_and_eq_sum` | 1042 | 46 |
| `exists_det_evalMatrix_ne_zero` | 39 | 44 |
| `translatesFinite_mul` | 183 | 44 |
| `finIncl` | 1312 | 42 |
| `slices_mem_pi_coeffSpan` | 458 | 36 |
| `exists_forall_liftFin_mem` | 1223 | 36 |

The 108-line core is the Baire-measure step (`BaireSpace U₀`, `nonempty_interior_of_iUnion_of_closed`,
`Subtype.val '' interior`, `isOpenMap_subtype_val`), the rank bound
(`LinearIndependent.fintype_card_le_finrank`, `finrank_span_finset_le_card`) and the
`Nat.findGreatest` maximal-rank argument; the 64-line `translatesFinite_range_incl` is where the
`IsArchKFinite → TranslatesFinite (Set.range (incl F))` conversion meets `Kinf`/`incl`/the
archimedean compactness. `finIncl` (42 lines) and `exists_forall_liftFin_mem`/`exists_idealBall_subset`/
`exists_congrSet_subset` are the finite-adelic integrality layer over `IdealBall`. Diagnose at
the low cap (playbook §3.5), fix the inference, report — never raise `maxHeartbeats`.

**Stop and report** if: a wrapper statement must change; a kernel cannot be stated without
editing an existing module or promoting a name; the `scoped instance` layer cannot be
reproduced locally (quote the instance and the failure); an import inversion appears; or a
premise outside the one `S_` file is needed (`port_advise`/`port_plan` never walk imports).
Do **not** open the archTestFactor consumers, do not edit the definition modules, and do not
reach past this leaf into the Deligne–Serre gates.

## 5. Build discipline (copy in, verbatim)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
> cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
> the low cap is what finds it. Never raise `maxHeartbeats`, never add a module
> `set_option maxHeartbeats`. `lake build <module>` per finished file, serialized with `flock`
> and bounded with `timeout`. Per wave, build only the wave's affected targets — **never a bare
> whole-tree `lake build`**. A whole-tree build happens once, at the session's end, only after
> the user agrees to it, and never on the agent's own initiative.

Concretely: tier-0 loop until each module is exit 0 with **0 warnings**, then
`flock .lake/flt_build.lock timeout 300 lake build <module>` per finished module, M1 before M2.
No bare `lake build`, no dependent, no façade.

## 6. Verification (the worker's, before stopping)

| check | expected |
|---|---|
| tier-0 loop on `TranslateSpan.lean`, then `ArchKFiniteFamily.lean` | exit 0, **0 warnings**, no forbidden token (`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/`maxHeartbeats`) |
| tier-1 build of each module | green; record jobs and wall/user/sys time |
| `port_advise.py` + `port_plan.py` on the node | 89 declaration groups, 1,492 once-cost, 0 trusted substitutions, the `box`/`detLocus` row still **suspect** and unused; every pin declaration present **once**; none invented |
| the engine kernel | present, public, byte-equal to its `Theorems/` wrapper under the checker's own parser |
| the five `private scoped instance`s | present in M2's `ArchimedeanIsometryGroup`, none globalised |
| `python3 tools/deps/unwired_register.py --check` | report only (do **not** rewrite the register) |

No checker run, no register edit, no wiring. (The checker's mutation sensitivity is its own
`--selftest`, run when the checker changes — not here.)

## 7. Report shape

Module paths and line counts; public vs `private` declaration counts; tier-0 and tier-1
wall/user/sys times; the parity table of §6; the false `box`/`detLocus` substitution, quoted;
the `norm_entry_le_one` adapter (or the local form and why); the four reconciliation candidates
with their pin lines; the named risks that bit and how; any statement that had to change (there
must be none); any promotion you stopped on with its `build_ladder.py --edit` price; `git status
--porcelain` showing only the two new modules.

## 8. The manager's half (not this order)

After review: the tier-1 façade `FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamilyTheorems.lean`
(namespace `AutomorphicForm`) stating the wrapper's headline verbatim and delegating to the
engine kernel; the checker wiring (the `Theorems/` wrapper and the `S_` file appended last to
`SOURCES`, the façade appended last to `PORT_FILES`); the `UNWIRED-PUBLIC.md` refresh for the two
tier-3 engines (checker **9789 → 9790**, delta **+1**, exactly the headline; the register grows
by M1's public surface plus M2's one kernel, each row carrying a `pin original`);
`#print axioms` on the headline; the one-token mutation test; and the step-6 frontier re-read
(the leaf leaves the shelf and its successors appear).

## 9. Reproduce

```bash
cd tools/deps
python3 port_advise.py --target AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous \
  --json build/isOpen_advise.json      # 89 groups, 74-helper drags, the suspect box/detLocus row
python3 port_plan.py --json build/isOpen_advise.json --section all   # 1,492 net new math lines
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --ds --include-leaves --rank-by silo --top 0                        # the 470-leaf shelf
python3 twin_scan.py --node AutomorphicForm.exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous
cd ../lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/RepTheory/TranslateSpan.lean
timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamily.lean
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.RepTheory.TranslateSpan
flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AutomorphicForm.Adelic.ArchKFiniteFamily
```

The pin sources are public at
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean`
(the `solution` is at line 1454) and its
[wrapper](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_isOpen_forall_exists_apply_eq_sum_of_isArchKFinite_of_continuous.lean#L10).

## 10. Results as landed (2026-10-14)

Worker report, then manager review and wire. **No statement changed; no promotion; no existing
module edited.**

| module | lines | public | private | tier-0 (wall/user/sys) | tier-1 |
|---|---:|---:|---:|---|---|
| `RepTheory/TranslateSpan.lean` (worker, tier 3) | 869 | 43 | 0 | exit 0, 0 warnings (5.11/6.87/1.97 s) | 4.5 s build |
| `AutomorphicForm/Adelic/ArchKFiniteFamily.lean` (worker, tier 3) | 852 | 1 | 50 | exit 0, 0 warnings (6.75/10.33/2.18 s) | 6.6 s build |
| `AutomorphicForm/Adelic/ArchKFiniteFamilyTheorems.lean` (manager, tier 1) | 32 | 1 | 0 | exit 0, 0 warnings | 3,699 jobs, 3.0 s build |

**Parity.** All 89 pin declarations present **exactly once**, 0 duplicates, nothing invented; the
only extra base name is the kernel (pin `solution` renamed to the wrapper's name). Kernel
statement byte-equal to the `Theorems/` wrapper under `check_flt_statements.raw_declarations`.
`port_advise` reads 89 groups and **0 tier-1 substitutions**; `port_plan` once-cost 1,492. The
`box → Q09AIarchG.detLocus` row stayed **suspect and unused**; `box` is transcribed privately.
The five `private scoped instance`s are in `ArchimedeanIsometryGroup`, none globalised.

**Manager's half.**

| check | result |
|---|---|
| checker | **9790** identical (671 promoted, 83 renamed), 0 mismatched, 0 missing, 38 own (9828 checked) — baseline 9789, delta **+1**, exactly the headline |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| one-token mutation on the headline | **1 mismatched**, reverted byte-identically (`sha256 d9a4e382…` unchanged) |
| forbidden-token sweep on the three new files | none |
| `unwired_register.py --check` | current after regen |

Wiring: the `Thm_` wrapper and the `S_` file appended last to `SOURCES`; the façade appended last
to `PORT_FILES`. The two engines stay tier 3 and are registered: `spec/UNWIRED-PUBLIC.md`
**102 → 104 modules, 2,954 → 2,998 public declarations, 2,666 → 2,710 with a pin original**
(the +44 is exactly 43 + 1).

**Step-6 re-read (successors).** The leaf has left the shelf: the `--ds --include-leaves` reading
now shows **469** leaves (was 470); `F` 959 → **960**, `needed` [F terminal] 1,402 → **1,401
nodes**, 532,720 → **531,197 `S_` lines** (−1,523, exactly the leaf). Its #2 slot is taken by the
next-largest leaf, `CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus` (1,230); the
`AutomorphicForm` subset's new head is `exists_sum_prod_mul_of_rightTranslatesSpanFinite` (576),
in the same subject cluster. The one consumer,
`exists_flat_isInducedSection_sum_eq_of_differentiable_family`, is **not** ready — its other two
premises (`exists_flat_isInducedSection_family_eq_of_isInducedSection`,
`exists_mem_adelicBorel_mul_eq`) remain unported. The ready shelf reads **87** candidates, headed
by `EisensteinGeneral.LocalRam.integral_twisted_smooth_eq` (864).

**Files changed by this order.** New: `FLTForHuman/RepTheory/TranslateSpan.lean`,
`FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamily.lean`,
`FLTForHuman/AutomorphicForm/Adelic/ArchKFiniteFamilyTheorems.lean`,
`topics/automorphicForm/WORKORDER-KF1-kfinite-family-span.md`. Edited:
`spec/check_flt_statements.py`, `spec/UNWIRED-PUBLIC.md`. (`topics/PORTING-DeligneSerre.md` shows
as modified in `git status` but is a pre-existing edit, not this order's.)
