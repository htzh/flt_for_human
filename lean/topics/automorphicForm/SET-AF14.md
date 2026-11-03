# SET-AF14 — the local atom at a place: integrability, the two evaluations, and the limit at `s = 1/2`

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, all eight rows, all gates green;
**§5.1 records the landing and the re-read**, which is exact on every figure and readies the predicted
pair. The order is [WORKORDER-AF14-local-atom.md](WORKORDER-AF14-local-atom.md). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF13 left (unchanged — see §0.1). It is the **fourteenth** `AutomorphicForm`-serving set, and the
one the `LocalIntertwining` topic note has been pointing at since it closed out: sets (1) and (2) of
its four-set plan are the landed LI-1/LI-2, and this is **set (3), the layer-0 integral family**
([TOPIC-local-intertwining-weyl-integrand.md](TOPIC-local-intertwining-weyl-integrand.md) §7).

The set is **8 rows / 1,578 silo / 1,403 lines to write in 78 declarations** (`build/af-worklist.py`),
1,393 net by `port_plan`, in **two orders and two new modules**. It is the first cut in four scoping passes whose landing is
measured, before the work, to ready rows — and it readies **+2 rows / +729 silo** (§0.3).

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the atom and its shift are integrable | 3 | 681 | 627 | new `AutomorphicForm/Adelic/LocalAtomIntegrable.lean` |
| B — the two evaluations, the two limits, the mixed-space bound | 5 | 897 | 776 | new `AutomorphicForm/Adelic/ArchAtomValues.lean` |
| | **8** | **1,578** | **1,403** | two files, one dispatch |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af13-landed.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF13 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **861 / 350,288** | 861 / 350,288 |
| `needed [literal]` | 874 / 353,763 | 874 / 353,763 |
| frontier F | **1,554 / 777,078** | 1,554 / 777,078 |
| ready rows, all namespaces | 62 / 16,259 | 62 / 16,259 |
| ready rows, `AutomorphicForm` | **33 / 10,915** | 33 / 10,915 |
| leaves, all namespaces | 232 / 58,795 | 232 / 58,795 |
| leaves, `AutomorphicForm` | **63 / 12,756** | 63 / 12,756 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (4 checks; 1,373 `Thm_` sources, 1,554 declared names) | PASS |
| correction | **none needed** | none needed |

**The delta is zero on every row, and that is the finding, not a missing measurement.** SET-AF13's
landing figure *is* this read: the tree has not moved since, no `--unport` correction is owed
(`--selfcheck` passes clean, so no false ported marker moved the frontier between the two reads and
they sit on the same marker set), and every figure the last brief forecast is the figure measured
here. Both blocks are quoted
whole and every row is accounted for in Appendix A: 33 ready / 10,915 and 63 leaves / 12,756
(29 / 5,344 and 169 / 46,039 are other namespaces' and are not this column's work), of which
**8 rows / 1,578 are this set's** and 88 are deferred (§7 groups them). The withheld block is the same
four rows — two `ModularCurve` Tate-module rows (`moduleFinite_and_free_padicInt_tateModule_jH` 327,
`…_jOne` 283, both blocked on `Pic0.abelJacobiCard_genus`), and two `AlgebraicCurve` `Pic₀` rows
(`Place.exists_natCast_dvd_ord_sub_single_sub_single_complex` 126,
`Pic0.finite_torsion_of_isAlgClosed_of_charZero` 95).

### 0.2 Why the atom family, and not the three bigger cuts

The other candidates, each priced on this shelf and each **forecast** by simulating the landing
(`build/af14-forecast.py`, §0.3 — the tool reads the ported frontier, the `--ds` avoid set and the
cutter set exactly as the shelf read does, then re-runs `analyze` with the candidates marked ported):

| candidate block | rows | silo | dispatches | rows readied | silo readied |
|---|---:|---:|---:|---:|---:|
| **the atom family (this set)** | 8 | 1,578 | 1 | **+2** | **+729** |
| the Weyl pair (§7) | 2 | 2,640 | 2 | 0 | 0 |
| the flat-section indicator row (§7) | 1 | 1,043 | 1 | 0 | 0 |
| the Iwasawa/Borel seed, `exists_mem_adelicBorel_mul_eq` (§7) | 1 | 372 | ¼ | **+9** | **+2,168** |
| the `diagOne` family (§7) | 4 | 2,098 | 2 | — | blocked, not on the shelf |

Four reasons for the cut.

- **It is the one ready block whose landing is measured to ready rows.** AF13 §5.1 closed on three
  consecutive sets with at most one readied row and named three moves to choose between. The
  measurement says the Weyl pair and the indicator row — the two large AF blocks AF13 §5.1(a) put
  forward — each ready **nothing** (both are terminal for the rows that cite them: each of their
  consumers needs one more unported premise of its own). The atom family readies two, and they are
  big (§0.3): `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (465) and
  `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` (264).
- **It is one story, eight faces, and the story is the pin's own `atom`.** Every row is about one
  function and its shift: the smooth atom `a = A·1_O + modulus^-(2s+1)·B(·⁻¹)` at a finite place
  (row 1); `((x - i)/√(1+x²))^k · (1+x²)^-(σ+1/2)` at a real place (rows 3, 7);
  `z^a z̄^b · (1+‖z‖²)^-(2σ+1)-m/2` at a complex place (rows 2, 6). Four facts about it: it and its
  shift are integrable (1, 2, 3); its integral evaluates, to `Γ_ℝ (2s) / Γ_ℝ (2s+1)` and to `π/(2s)`
  (4, 5); the σ-dependent Möbius factor `(‖c'z+d'‖²)^(2σ-1) - 1` against it has vanishing integral as
  `σ ↓ 1/2` (6, 7); and the product of the archimedean atoms over all infinite places is uniformly
  bounded on the strip `1/2 < σ ≤ 1` (8). This is the analytic core of the local intertwining
  operator — the atom integrals the unfolding and the local functional equation consume — and it is
  **set (3) of the topic note's own four-set plan** for the cluster.
- **Seven of the eight rows are graph leaves.** Their `premises` is **0** (row 1 has two, both
  ported), so a plain `--ready` read does not see them at all: they are on the shelf only because the
  read carried `--include-leaves`. This is the recipe's §0 warning, met head-on: **7 of this column's rows
  and 1,295 of the 1,578 silo sit in the leaves block**, and a brief that quotes only `ready_rank`
  would have priced this set at **283 silo**. It is also why the recipe's "never drop the
  leaves" is a size rule and not a tidiness rule.
- **The definition layer is free and the price is honest** (§3): two `Def_` modules in the whole set's
  closure, **0 missing** in both, one declaration actually used (`LanglandsTunnell.TateLocal.modulus`,
  in the port), and no `Def_` node. The work is 1,403 lines of transcription in 78 declarations and
  nothing else: no promotion is *needed* (§2), no migration, no
  legacy edit.

### 0.3 What a landing would change — the forecast, and how it was made

`frontier.py` has no reading for "what does this landing ready"; the recipe's §7 asks for that number
*after* the fact, and the three previous passes could only compare two shelves taken a set apart. The
scoping pass therefore simulates the landing (`build/af14-forecast.py`, 4.9 s):

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 861 / 350,288 | **853 / 348,710** | −8 / −1,578 ✓ (the eight rows' silo, exact) |
| `needed [literal]` | 874 / 353,763 | 866 / 352,185 | −8 / −1,578 |
| frontier F | 1,554 / 777,078 | 1,562 / 778,656 | +8 / +1,578 |
| ready rows, all namespaces | 62 / 16,259 | **63 / 16,705** | +1 row, +446 silo |
| leaves, all namespaces | 232 / 58,795 | 225 / 57,500 | −7 / −1,295 (the seven leaf rows leave) |

**Rows readied (2 / 729 silo).** Both are the *general* statements of this set's rows 4 and 5, one
premise each:

| row | silo | prem | lev | what it states |
|---|---:|---:|---:|---|
| `LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` | 465 | 1 | 1/6 | `∫ x, ((x - I)/√(1+x²))^k · (1+x²)^-(s+1/2) = (-I)^k · Γ_ℝ(2s)·Γ_ℝ(2s+1) / (Γ_ℝ(2s+1+k)·Γ_ℝ(2s+1-k))` |
| `LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` | 264 | 1 | 1/6 | `∫ z, z^a z̄^b (1+‖z‖²)^-t = if a = b then π·a!·Γ(t-1-a)/Γ t else 0` |

**They subsume rows 4 and 5, and this is the one place the shelf order is the wrong order for the
port.** At `k = 0` the first reduces to row 4's `Γ_ℝ(2s)/Γ_ℝ(2s+1)`; at `a = b = 0, t = 2s+1` the
second reduces to row 5's `π/(2s)`. The pin proves the special case first and the general one on top
of it, which is why `port_plan`'s *siblings* block is empty here (its sibling test only looks
*inside* the slice). Two consequences the order must carry: **(i)** rows 4 and 5 are not "the
mathematics", they are the `k = 0` / `a = b = 0` cases of two rows that are one premise away — write
them at the pin's proofs, but do not *invest* in them; **(ii)** ~~when AF15 takes the pair, the port may
derive rows 4 and 5 from them in a line each instead of keeping two analytic proofs~~ — **withdrawn at
the next pass**: the inversion is not available, because each general row takes its special case as a
**premise** (the 465 row calls `integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs` at pin `:318`, the
264 row calls `integral_one_add_norm_sq_cpow_neg_eq_pi_div ((t-1)/2) hs` at pin `:171`, each with
`needed = 1`). The pin proves special → general, so deriving the special from the general would be
circular: AF15 writes the two general rows on top of these, and both analytic proofs here stay
([SET-AF15.md](SET-AF15.md) §1).

### 0.4 An ingredient block, not an organizer

`leverage` on this shelf is 1–2 for all eight rows (row 1 is 2/2, the rest 1/1) while the Iwasawa seed
§7 defers carries **14/63**. That is the recipe's §1 inversion of demand and size, and it says what
this set is: an ingredient block, cheap per line, consumed by a handful of large statements. The
organizer reading of the shelf — one small lemma that readies nine rows — is the other candidate, and
it is deliberately left to AF15 (§7).

## 1. The eight rows

| row (`AutomorphicForm.LocalIntertwining.` dropped) | silo | work | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---:|---|
| `integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | **257** | 16 | 2 | 2/2 | at a finite place: for `A`, `B` locally constant at depth `m`, the atom `A·1_O + modulus^-(2s+1)·B(·⁻¹)` is integrable, and so is its Weyl shift `modulus^-(2s+1)·a(·⁻¹)`, for `re s > 0` |
| `integrable_complexAtom_and_integrable_moebiusShift` | 219 | **205** | 6 | 0 | 1/1 | at a complex place: `z^a₀ z̄^b₀ (1+‖z‖²)^-(2σ+1)-m/2` is integrable for `a₀+b₀ ≤ m`, `σ > 0`, and so is its Möbius transform with the Jacobian factor, for any `a b c d : ℂ` with `ad - bc ≠ 0` |
| `integrable_realAtom_and_integrable_moebiusShift` | 179 | **165** | 9 | 0 | 1/1 | the same at a real place: `((x - i)/√(1+x²))^k (1+x²)^-(σ+1/2)` and its Möbius transform |
| `integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | **298** | 11 | 0 | 1/1 | `∫ x, ((1+x²) : ℂ)^-(s+1/2) = Γ_ℝ(2s)/Γ_ℝ(2s+1)` for `re s > 0` |
| `integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | **88** | 5 | 0 | 1/1 | `∫ z, ((1+‖z‖²) : ℂ)^-(2s+1) = π/(2s)` for `re s > 0` |
| `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | **157** | 13 | 0 | 1/1 | `∫ z, ((‖c'z+d'‖²)^(2σ-1) - 1) · (z^a z̄^b (1+‖z‖²)^-(2σ+1)-m/2) → 0` as `σ ↓ 1/2` |
| `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | **134** | 11 | 0 | 1/1 | the real-place version of the same limit |
| `exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | **99** | 7 | 0 | 1/1 | a `C` with `‖∫ y : mixedSpace F, ∏_real (atom) · ∏_complex (atom)‖ ≤ C` for every `σ` in `(1/2, 1]`, uniformly in the data |

The eight rows are pairwise independent (none cites another: `port_plan`'s *layers* block puts all
eight at layer 0), so the two orders may run concurrently.

**Visibility follows the pin's — and here that is nearly everything.** Six of the eight `S_` files
carry **no `private` declaration at all**: rows 2–7 are flat public surfaces, and `port_advise`'s
drags block confirms it (row 2: "public surface 6 declarations; same-file closure adds 0 helpers";
likewise 9, 12, 5, 14, 12). Only two files have a private prelude: row 1 (15 private helpers, ≈133
lines) and row 8 (6 private helpers, ≈61 lines). So the checked surface of this set is large and
cheap to get right — every helper of rows 2–7 is a pin-public declaration that `check_port` will diff —
and the two private preludes stay private, at the pin's visibility, for AF13 §1's reason (a pin-private
helper made public is a `MISMATCH` on the pin's `section`-variable spelling, FR-0123).

**Names.** The eight headlines keep their pin names at `AutomorphicForm` level. The helpers go in one
subject namespace per pin file, replacing the pin's proof-search labels (`IntArchC`, `IntArchR`,
`M4aP2DGK.ArchReal`, `M4aP2DGK.ArchComplex`, `ARCHA4C`, `ARCHA4R`, `W4ARCH`), which is also what makes
the three same-name pairs legal (§2): `ComplexAtom` (row 2), `RealAtom` (row 3), `GammaReal` (row 4),
`PiDiv` (row 5), `ComplexAtomLimit` (row 6), `RealAtomLimit` (row 7), `MixedSpaceBound` (row 8). Row 1's
helpers are already in the pin's `AutomorphicForm.LocalIntertwining.IntV` — a subject name, kept as is.

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion \
  --nodes AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift \
  --nodes AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift \
  --nodes AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div \
  --nodes AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div \
  --nodes AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half \
  --nodes AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half \
  --nodes AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod \
  --json build/af14-li0-advise.json
python3 port_plan.py --json build/af14-li0-advise.json     # 1,578 raw / 1,457 decl / 58 in port / 1,393 net
python3 build/af-worklist.py LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion \
  LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift \
  LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift \
  LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div \
  LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div \
  LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half \
  LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half \
  LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod
```

`port_plan`: raw **1,578** → declaration lines **1,457** → −6 duplicate copies → 1,451 once-cost →
**−58 already in the port** → **NET NEW 1,393**; boilerplate 121; 82 distinct declaration groups.
The worklist (Appendix B): **1,465 declaration lines, 62 imported, 1,403 to write in 78 declarations**.
The two figures differ by 8 lines and one parse convention (`port_plan` counts `solution` bodies as
one group; the worklist counts them per file); both are quoted because the order spends against the
worklist and the brief reports against the plan.

### 2.1 The substitution block, and the 55 lines in it that are not importable

`port_advise` finds **5 substitutions, ≈62 lines**: 3 byte-identical, 2 identical up to binder
spelling. Read row by row, they split four ways — and one of the five is a false positive:

| pin declaration | lines | claimed port copy | reading |
|---|---:|---|---|
| `isCompact_integers` (row 1) | 3 | `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers` | public, tier 3: **imported** |
| `maj` (row 8, a `def`) | 4 | `` `AutomorphicForm.TestFnArchProfile.sqSize` `` | **struck — the substitution does not hold** (§5.1): `sqSize x` is a *sum* of squares, the pin's `maj` a *product* of `(1+‖·‖²)^{-1}`/`(1+‖·‖²)^{-2}` factors, so importing it would make `integrable_maj` false as stated. Written at the pin's text, `private` (FR-0134) |
| `integrable_one_add_sq_rpow_neg` (row 4) | **51** | `Iwasawa/Real/Continuation.lean:71` — **`private`**, under another name (`integrable_dom`) | statement-identical, proved in 8 lines there through `Real.rpow` tail estimates instead of the pin's 51. **Not importable**; see below |
| `one_add_sq_pos` (rows 6, 7) | 2 + 2 | `Iwasawa/{Complex,Real}/Continuation.lean:37` — both **`private`** | 2 lines each; **not importable** |
| (nothing else) | — | — | — |

**So the honest reuse is 3 lines, not 62**: one import that holds, one that does not, and 55 lines that
are statement-identical copies the port holds `private` — which `port_plan`'s "already in the port
(vetted)" and the worklist's "imported" column both count as in-port, though they are not (FR-0133).
Two ways to take those 55 lines, and the brief recommends the second:

- **promote** `integrable_dom` (one word: drop `private`; the module is tier 3 and edits are free) and
  import it. Cheap, but it puts the pin's `integrable_one_add_sq_rpow_neg` in the port under a name the
  pin does not use, and a later reader asking for the pin's name finds nothing.
- **write the pin's declarations, reusing the port's short proofs.** `integrable_one_add_sq_rpow_neg`
  gets the port's 8-line `integrable_dom` proof at the pin's name (not the pin's 51 lines), and
  `one_add_sq_pos` is written once, publicly, in order B's module. Cost in new lines: **≈10**, against
  55 for a literal transcription; the pin's names and the checked surface both survive.

### 2.2 Port once, generalise — three same-name decisions the order must state

- **Port once.** `rpow_le_max` (6 lines) is proved in both Tendsto files, and `one_add_sq_pos` (2 lines)
  in three pin files of which two are this set's: write each **once, publicly, at the pin's name**, in
  order B's module.
- **A same-name pair with two statements is a namespace split, never a rename** (recipe §2). Three
  pairs here, all inside the set: `floor` (`ℂ` in row 2, `ℝ` in row 3 — the determinant inequality),
  `entries_pos` (`ℂ`/`ℝ` — `0 < ‖a‖²+‖b‖²+‖c‖²+‖d‖²`), and `atom` (a 3-line `def`, `ℂ` in row 6, `ℝ`
  in row 7). Both copies are written, in the two sub-namespaces; the topic note already recorded the
  first two as "to generalise or rename" (§8), and with both members of each pair in one set the
  answer is the pin's own precedent: a sub-namespace per place.
- **Binder variants are not duplication.** `two_le_absNorm` (row 1, 7 lines) is a binder spelling of
  the port's public `NumberTheory/FrobeniusDensity/PrimeSumAsymptotic.lean:33` (`(v : HeightOneSpectrum
  (𝓞 K))` against the pin's section variable), and `norm_sub_I` (row 3, 7 lines) is statement-identical
  to the port's `private` copy at `Iwasawa/Real/Continuation.lean:49`. Default: import the first if
  `check_port` reads it clean, otherwise declare it at the pin's 7 lines; write the second (its port
  copy is `private`, and 3 of its 7 lines are the proof).

**No port-once block across the eight target files beyond those two, and no siblings block**: the
`S_` files share the three pairs above and nothing else — they share the *subject*, which is what the
set is.

## 3. The definition gate

`spec/gate_scan.py` over the two `Def_` modules of the eight wrappers' closure, all eight rows
(`--rows` takes one list — repeating the flag silently keeps only the last, AF13's Appendix C):

| pin `Def_` module | port home | used (max) | missing |
|---|---|---:|---:|
| `Def_NumberField_AdelicHaar` | `…/NumberTheory/AdelicHaar/Adele.lean` | 0/25 | **0** |
| `Def_LanglandsTunnell_TateLocalZeta` | `…/LanglandsTunnell/TateLocalZeta.lean` | 1/23 | **0** |

**One declaration of one module is used, and it is ported**: `LanglandsTunnell.TateLocal.modulus`, in
row 1 only (`pin:15 +2`). Six of the eight wrappers import **no** `Def_` module at all — rows 2–7 are
pure mathlib analysis, and row 8 needs mathlib's `mixedEmbedding.mixedSpace`
(`Mathlib.NumberTheory.NumberField.CanonicalEmbedding`), not a port module. **No `Def_` node, no
promotion, no migration** — and no definition work of any kind. The two `Def_` port homes are legacy (`NumberTheory/AdelicHaar/Adele.lean` is in
`PORT_FILES`) and are only imported, so no migration is owed.

## 4. The homes

**Two new modules, one per order.**

- **Order A — `FLTForHuman/AutomorphicForm/Adelic/LocalAtomIntegrable.lean`.** Subject: the atom at
  one place is integrable, and so is its shift. Imports
  `FLTForHuman.EisensteinGeneral.LocalRam` (`integrable_twisted_smooth`, row 1's premise),
  `FLTForHuman.NumberTheory.NumberField.TateGlobal.NormIntegrable`
  (`modulus_adicCompletion_eq_nnnorm`), `FLTForHuman.LanglandsTunnell.TateLocalZeta` (`modulus`,
  `charExt`), `FLTForHuman.NumberTheory.NumberField.TateGlobal.LocalZetaUnramified`
  (`isCompact_integers`), and the mathlib modules its three `S_` files name
  (`Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`,
  `Mathlib.MeasureTheory.Measure.Lebesgue.Complex`, `Mathlib.Analysis.SpecialFunctions.Pow.Complex`).
- **Order B — `FLTForHuman/AutomorphicForm/Adelic/ArchAtomValues.lean`.** Subject: the archimedean
  atom's integral, its limit at `s = 1/2`, and the uniform bound on the strip. Imports
  `Mathlib.Analysis.SpecialFunctions.Gamma.Deligne` (`Complex.Gammaℝ`),
  `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `Mathlib.Analysis.SpecialFunctions.Pow.Complex`,
  `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Integral.Pi`
  (`Integrable.fintype_prod`, the engine of row 8's `integrable_maj`),
  `Mathlib.MeasureTheory.Measure.Lebesgue.Complex`,
  `Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic` (`mixedEmbedding.mixedSpace`). It does
  **not** import order A, and it does **not** import `RightConvNeZeroArch` (the only reason to would have
  been the withdrawn `sqSize` substitution, §2.1).

**Import direction, measured.** The premise modules are `EisensteinGeneral/*`, `TateGlobal/*` and
`LanglandsTunnell/*`; **no module of any of those three branches imports an `AutomorphicForm` module**
(`grep -rl '^import FLTForHuman.AutomorphicForm' FLTForHuman/EisensteinGeneral FLTForHuman/LanglandsTunnell`
is empty, and the only two hits under `TateGlobal/` are `NormExponent.lean` and `ShellTranslate.lean`,
which neither order imports). So both homes are above every premise, and — because the pin's own
`S_` file cites `EisensteinGeneral.LocalRam` as a premise of an `AutomorphicForm.LocalIntertwining`
theorem — the new `AutomorphicForm/Adelic → EisensteinGeneral` edge **mirrors the pin's direction** and
is not a cycle. Both modules are new and nothing imports them: cascade-free.

The alternative home, if the reviewer prefers it, is `NumberTheory/NumberField/TateGlobal/` next to
`WeylPrelude`/`WeylShell`/`WeylUnramified`/`WeylSmooth` — that is where LI-1/LI-2 homed the two
`LocalIntertwining` headlines. It is a naming preference, not an import constraint; the subject
(the atom that the local intertwining operator integrates) names `AutomorphicForm/Adelic`, next to
`WeylIntertwining.lean`, and that is the recommendation.

## 5. The cut

**Two orders, two workers, one dispatch. 1,403 lines in 78 declarations.**

| order | rows | silo | lines | decls | module |
|---|---:|---:|---:|---:|---|
| A — the atom and its shift are integrable | 3 | 681 | 627 | 31 | `LocalAtomIntegrable.lean` |
| B — evaluations, limits, the mixed-space bound | 5 | 897 | 776 | 47 | `ArchAtomValues.lean` |

**Disjoint files, so the two orders are safe concurrently** (recipe §5): eight distinct `S_` files, two
distinct new modules, no declaration of one order cited by the other (all eight rows are layer 0), so
only the build lock is shared. Order B is the larger and the more delicate (row 4's `Γ_ℝ` evaluation is
a scaled-Γ/Fubini argument, 298 lines) — give it the earlier start, not the earlier gate.

**The manager's layer** is: the two module skeletons with their `spec-pin:` wires (order A: the three
`Theorems/` wrappers plus the three `S_` files; order B: the five plus the five), imports and opens; a
**statements probe of all eight headlines** against the skeleton before dispatch — three of them carry
a top-level `let` (§6.1) and only a probe tells you the module can state them; and the §2.1 decision on
`integrable_one_add_sq_rpow_neg` (recommended: the pin's name, the port's 8-line proof) and on
`two_le_absNorm` (import, or declare at the pin's 7 lines if `check_port` objects).

**Gates, per order** (recipe §6):

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every added declaration
   `ok`. Expect a *large* ok count here — rows 2–7 alone are 55 declarations of flat public surface, and
   only two of the eight files have a private prelude — so measure it rather than guess it, and read a
   `MISSING` as a port-side helper to keep private, not as a gap.
2. `#print axioms` on all eight headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` silent (the wrappers
   set `autoImplicit false`), and its own `flock`/`timeout 280 lake build`. No tree build, no
   dependents.
4. `dedup.py` / `move_dead.py` per module; the `rpow_le_max`/`one_add_sq_pos` port-once rows are the
   intended duplicates and are written once.
5. `spec/AutomorphicFormSetAF14Consumer.lean`: **two real zones, one per place**, each composing an
   order-A row with an order-B row — at a real place, `(integrable_realAtom_…_moebiusShift 1 0 0 1 0 σ hσ).1`
   at `k = 0` with `integral_one_add_sq_cpow_neg_eq_GammaReal_div (σ) hσ` to read `∫ atom = Γ_ℝ(2σ)/Γ_ℝ(2σ+1)`;
   at a complex place, the same with `(integrable_complexAtom_… 1 0 0 1 0 0 0 σ hσ).1` and
   `integral_one_add_norm_sq_cpow_neg_eq_pi_div` to read `∫ atom = π/(2σ)`. No `#check`, no `sorry`;
   the error count is the deliverable metric.
6. Zero warnings, no `sorry`, no `native_decide`, no `set_option` beyond `autoImplicit false` and the
   linter options the port's own modules already carry.

### 5.0 The manager's layer (landed 2026-11-02)

Both modules exist as skeletons — `LocalAtomIntegrable.lean` 67 lines with six `spec-pin:` lines and
eight imports, `ArchAtomValues.lean` 74 lines with ten `spec-pin:` lines and seven imports — and each
elaborates silent and builds green (`flock`/`lake build <module>`, 3,840 jobs for the closure);
`check_port --force` reads **0 ok / 0 mismatch / 0 missing** on both, so the wire is correct before a
line of mathematics exists. The statements probe
(`lean/tmp/probe-af14-statements.lean`) states all eight headlines verbatim from their wrappers and
elaborates with **exactly eight `declaration uses 'sorry'` warnings**; it settled that **row 8 needs
`open scoped Classical in` on its declaration** (otherwise the two `Fintype` subtypes and
`MeasureSpace (mixedEmbedding.mixedSpace F)` do not resolve — the wrapper carries the same line), and
that `integrable_rpow_neg_one_add_norm_sq` and `Complex.Gammaℝ` are already in scope while
`Complex.Gammaℝ_two_mul`/`…_add_one` are not (they are the pin's own helpers). Two port names differ
from the pin's and the worker must use the port's: `NumberField.TateGlobal.modulus_adicCompletion_eq_nnnorm`
and `NumberField.TateGlobal.LocalZetaUnramified.isCompact_integers`. The §2.1 decision is taken: row 4's
`integrable_one_add_sq_rpow_neg` is written at the pin's name with the port's 8-line proof, `one_add_sq_pos`
and `rpow_le_max` are written once publicly (port-once), and the two 7-line binder variants
(`two_le_absNorm`, `norm_sub_I`) are written at the pin's text rather than imported.

### 5.1 The landing (2026-11-02)

**Files.** `AutomorphicForm/Adelic/LocalAtomIntegrable.lean` 67 (skeleton) → **705**; 
`AutomorphicForm/Adelic/ArchAtomValues.lean` 74 → **875**; `spec/AutomorphicFormSetAF14Consumer.lean`
(59, new). **80 declarations: 60 public, 20 `private`** — order A 31 (14 private + 17 public), order B 49
(6 private + 43 public), the eight headlines public at the pin's names, and the pin's own `private`
preludes (`IntV`'s fourteen, `MixedSpaceBound`'s six) private. Every helper sits in the row's subject
namespace (§1); the port-once pair `one_add_sq_pos`/`rpow_le_max` is written once, publicly, at flat
level.

**Gates, re-run by the manager.** Edit loop at `-DmaxHeartbeats=200000` **silent** (A 6.7 s, B 5.6 s);
own `flock`/`timeout 280 lake build` green and silent (A 3,840 jobs, B 3,128 after the §2.1 import
removal); `check_port --force` **17 ok / 0 mismatch / 0 missing** (order A) and **43 ok / 0 / 0** (order
B) at the pin's visibility; the recipe's surface gate (all 20 `private` dropped) **31 ok** and **49 ok**,
`0 mismatch / 0 missing` — so every pin-private helper is byte-faithful to its pin statement too;
`#print axioms` on all eight headlines `[propext, Classical.choice, Quot.sound]`; the statements probe
still exactly eight `sorry` warnings; the consumer zone **0 errors, 0 warnings**; `dedup --within`
order A **0 clusters**, order B **3 shape clusters, all headline-vs-its-helper** (`main` vs the row-8
headline, `integral_value_gammaR` vs row 4's, `integral_value` vs row 5's) and kept, because that is the
pin's own `solution`-calls-helper structure and the headline's statement is the wrapper's;
`move_dead --dry-run` **0 declarations / 0 lines** on both. Zero warnings anywhere.

**The `Γ_ℝ` row transcribed verbatim, with no restructuring**: `scaledGammaIntegral` is the pin's
substitution `t ↦ r t` on `Ioi 0` (continuity, image inclusion, and `IntegrableOn` via
`Complex.GammaIntegral_convergent`), `integrable_uncurry_kernel` is `integrable_prod_iff`, and
`integral_cpow_neg_one_add_sq` the pin's four-step `integral_integral_swap`/Gaussian/`Gamma_eq_integral`
chain. Rows 4 and 5 both compiled on the first attempt.

**The §2.1 decision held, and the eight-line route is confirmed by the checker:**
`integrable_one_add_sq_rpow_neg` is written at the pin's name and statement with the port's
`integrable_dom` proof (8 lines against the pin's 51) and `check_port` matches it at the pin's `:116`;
`two_le_absNorm` and `norm_sub_I` are written at the pin's text (7 lines each, private); the
`floor`/`entries_pos`/`atom` pairs are two declarations each, in the two sub-namespaces. The
`maj → TestFnArchProfile.sqSize` substitution **does not hold** — `sqSize` is a sum of squares and the
pin's `maj` a product of `(1+‖·‖²)^{-1}`/`(1+‖·‖²)^{-2}` factors — so `maj` is written at the pin's text
(private, 4 lines) and the checker matches it at the pin's `:61`; §2.1 is corrected and the import that
substitution justified (`RightConvNeZeroArch`) is removed (it had no other use, and order B's closure
drops from 3,561 to 3,128 jobs).

**One new import, accepted.** `Mathlib.MeasureTheory.Integral.Pi` supplies `Integrable.fintype_prod`,
the pin's own engine in row 8's `integrable_maj` (pin `:68–71`); `#check` confirms no other module of
order B's import list provides it, so it is the minimal fix rather than a workaround. The alternative
(a private re-proof of the product-integrability lemma) would have been new mathematics the pin does not
have.

**v4.34 drift, all recorded** (FR-0130's class): `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`
(row 1, pin `:187, :194, :232, :239`), `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (row 1 pin `:257`,
rows 6/7 pin `:141`/`:119`), `Finset.prod_le_prod` → `prod_le_prod₀` (row 8, pin `:94–95`), `haveI :=
nhdsNE_zero_neBot …` → `have` (style linter, row 1 pin `:251`), `simp <;> ring` → `simp; ring` (row 8
pin `:24`), and `Filter Topology` added to row 1's `open` line.

**The re-read is exact, and it readies the predicted pair.** 

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 861 / 350,288 | **853 / 348,710** | −8 / −1,578 ✓ (the eight rows' silo, exact) |
| `needed [literal]` | 874 / 353,763 | **866 / 352,185** | −8 / −1,578 ✓ |
| frontier F | 1,554 / 777,078 | **1,562 / 778,656** | +8 / +1,578 ✓ |
| ready rows, all namespaces | 62 / 16,259 | **63 / 16,705** | +1 / +446 |
| ready rows, `AutomorphicForm` | 33 / 10,915 | **34 / 11,361** | +1 / +446 |
| leaves, all namespaces | 232 / 58,795 | 225 / 57,500 | −7 / −1,295 |
| leaves, `AutomorphicForm` | 63 / 12,756 | **56 / 11,461** | −7 / −1,295 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,373 / 1,554) | **PASS** (1,381 `Thm_` sources, 1,562 declared names) | — |

**The two rows readied are the ones §0.3 predicted, at the predicted sizes**:
`integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (465, 1 premise, 1/6) and
`integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` (264, 1 premise, 1/6). The `283` row left
ready as itself and the seven leaf rows left the leaves block; nothing else moved — so this is the
**fourth** set in a row whose shelf effect is entirely its own consumption, and the first in four whose
consumption *creates* ready work instead of only removing it (the two rows are 729 silo, roughly half
the set).

**Plan against actual.** Lines: **1,439 written** (order A 638 = 705 − 67, order B 801 = 875 − 74)
against the worklist's 1,403 and `port_plan`'s 1,393 net — **+2.6 %**, the tightest landing the column has
had (AF13 +12 %, AF12 +0.6 %). The causes are identifiable and small: the pin's `maj` `def` (4 lines the
§2.1 substitution had priced as imported), the flat port-once pair written once where the worklist counts
it per file, and the two `private` preludes' section comments. Declarations: **80** against the
worklist's 78 (+2: the port-once pair, counted as one declaration each). Checker: 60 at the pin's
visibility (17 + 43), 80 at the dropped surface — so every declaration in the set is a pin statement,
none is a port-side helper.

**What the two `moebiusShift` rows need now.** §7 half-readied them; the re-read confirms it: each is
**one** unported premise short (`MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex` /
`integral_abs_det_div_sq_mul_comp_moebius_real`, another column's). They did not become ready, and the
next re-read should check whether that premise has landed rather than trusting this note.

## 6. Risk register

1. **Three of the eight statements carry a top-level `let`** — rows 1, 2 and 3 all open their
   conclusion with one (`let a := …` in row 1, `let atom := …` in rows 2 and 3) and then state
   `Integrable atom ∧ Integrable …`. The
   checker's `top_level_cut` stops at the first top-level `:=`, so its diff for those three is
   **degenerate** (FR-0056, the AF13 constant-term failure): `check_port` will report them `ok` on a
   truncated signature. The check that counts is a **token comparison against the wrapper**, and the
   probe. Read those three statements by eye.
2. **`import Mathlib` in five of the eight `S_` files** (rows 2, 3, 6, 7, 8). The port never imports
   `Mathlib`; name the modules in §4 and expect to add one at the first blocker, as AF13 did
   (`Mathlib.Analysis.Complex.LocallyUniformLimit`) — record which.
3. **The two `Γ_ℝ` rows are the set's real cost** (row 4: 298 lines, 11 declarations;
   `integral_cpow_neg_one_add_sq` 77, `scaledGammaIntegral` 64, `integrable_uncurry_kernel` 49). It is
   a scaled-Γ/Fubini computation with an `ℝ≥0`-valued intermediate; read the pin's section in order and
   do not attempt to unify it with row 5's `π/(2s)` argument before the last declaration.
4. **The three same-name pairs must not be renamed** (§2.2): two copies of `floor`, `entries_pos` and
   `atom`, in two sub-namespaces. A single copy with a widened binder is *not* the pin's statement and
   the checker will say `MISMATCH` on the one that lost.
5. **Binder spelling is the statement.** Rows 2 and 3 spell their hypotheses `_hdet`, `_hσ`, `_habm`;
   row 1 spells `_hm`, `_hA`, `_hB` and carries instance binders
   `[MeasurableSpace (v.adicCompletion F)] [BorelSpace …]` plus `[μ.IsAddHaarMeasure]`. Transcribe the
   wrapper's text, underscores included (FR-0123).
6. **`s = 1/2` is a limit from above** in rows 6 and 7: the filter is `𝓝[>] (1/2 : ℝ)`, not `𝓝`, and
   the two rows' `atom` defs differ by place — do not "simplify" them into one.
7. **The row-8 statement is uniform in the data**: `kdat : {w // w.IsReal} → ℤ` and
   `abm : {w // w.IsComplex} → ℕ × ℕ × ℕ` with `(abm w).1 + (abm w).2.1 ≤ (abm w).2.2` — the bound `C`
   does not depend on `σ`, only on the data. Its 6 private helpers (61 lines) stay private.
8. **No `set_option`** beyond `autoImplicit false`; the pin's `letI`/`haveI` walls, where they appear,
   become `have`/`let` (FR-0126).

## 7. What this set does not do

- **It does not take the Weyl pair** — `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349) and `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291): **2,640 silo, two dispatches, and a measured return of zero rows.** AF13 §0.2 named it the
  next set after itself; the measurement says otherwise, and the reason it was held back has partly
  gone: its definition gate is now clean too (0 missing over both rows on
  `Def_LanglandsTunnell_TateLocalZeta`, `charExt` and `modulus` both in the port), so what remains is
  its size and its return. It is AF15's second candidate, after the pair this set readies.
- **It does not take the flat-section indicator row** — `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow`
  (1,043, 3 premises, 1/3): measured return zero, and it is AF13's own subject (the height of the
  bottom-row indicator section) rather than the atom's. It stays the largest ready row on the shelf.
- **It does not take the Iwasawa/Borel seed** — `exists_mem_adelicBorel_mul_eq` (372, 1 premise,
  **14/63**): the cheapest unblock on the shelf, measured to ready **9 rows / 2,168 silo** (an 890-line
  `EisensteinGeneral.Piece` row, `exists_flat_isInducedSection_sum_eq_of_differentiable_family` 264,
  `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` 245,
  `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_…` 227, three continuity/height rows at
  161/155/116, and two at 81/29) — 2,168 silo, of which 1,278 is `AutomorphicForm` and 890 is
  `EisensteinGeneral`, another column. It is not this set because it is a different story (the
  decomposition of `g`, not the atom) and because it is a *seed*: the nine rows it readies are two
  dispatches, not one, and the larger of the two is not this column's. **It is AF15's first candidate,
  and the next scoping should take it before the pair.**
- **It does not finish the `LocalIntertwining` layer-0 family.** Three layer-0 rows stay off the shelf
  and each is **exactly one premise short**: `bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom`
  (206) and `…_realAtom` (175) each need a `MeasureTheory` row (`integral_normSq_det_div_mul_comp_moebius_complex`,
  `integral_abs_det_div_sq_mul_comp_moebius_real` — another column's) *in addition to* the Tendsto row
  this set lands, and `bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion`
  (472) needs `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion`
  (its other two premises, `EisensteinGeneral.LocalRam.integrable_twisted_smooth` and
  `LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm`, are ported). **This set half-readies
  the first two** — worth stating in the re-read, because after it they are one row away, and a reader
  who only diffs the two shelves will read "still not ready" as "this set failed".
- **It does not take the `diagOne` family** (2,098 in four rows) — still blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one`, the `AdelicLevel.diagOne`
  central-scalar row and the `LanglandsTunnell` `moderateGrowth`/`rpow_bound` rows.
- **It does not take the API tail** — `exists_mem_adelicBorel_mul_eq` above is the head of it;
  `isKfSmooth_rightConv` (70, 7/21), `exists_isFundamentalDomain_globalPoints_range` (165, 1/11) and
  `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` (192, 5/8) follow it.
- **No `Def_` node, no promotion is owed, no migration**; two new modules, both cascade-free.

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af13-landed.json` by `build/af14-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **33 rows / 10,915 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | **14/63** | deferred (§7, AF15's first candidate) |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 283 | 2 | 2/2 | **SET-AF14** |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | deferred (§7) |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | deferred (§7) |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | deferred (§7) |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | deferred (§7) |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | deferred (§7) |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | deferred (§7) |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | deferred (§7) |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | deferred (§7) |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | deferred (§7) |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | deferred (§7) |
| `isKfSmooth_rightConv` | 70 | 1 | 7/21 | deferred (§7) |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | deferred (§7) |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | deferred (§7) |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | deferred (§7) |
| `CuspidalConstituent.rightConv_rightTranslate_eq_rightTranslate_rightConv_conj` | 35 | 1 | 2/3 | deferred (§7) |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | deferred (§7) |

### The leaves block — **63 leaves / 12,756 silo**

| leaf | silo | lev | disposition |
|---|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 3/4 | deferred (§7) |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 2/4 | deferred (§7) |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 1/1 | deferred (§7) |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 2/2 | deferred (§7) |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 1/3 | deferred (§7) |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 2/15 | deferred (§7) |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 2/7 | deferred (§7) |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 3/4 | deferred (§7) |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 1/2 | deferred (§7) |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 362 | 1/1 | **SET-AF14** |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift` | 219 | 1/1 | **SET-AF14** |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift` | 179 | 1/1 | **SET-AF14** |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 170 | 1/1 | **SET-AF14** |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 147 | 1/1 | **SET-AF14** |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod` | 116 | 1/1 | **SET-AF14** |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
| `LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 102 | 1/1 | **SET-AF14** |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 1/1 | deferred (§7) |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 2/2 | deferred (§7) |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 2/4 | deferred (§7) |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 3/22 | deferred (§7) |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 3/8 | deferred (§7) |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 1/1 | deferred (§7) |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 1/1 | deferred (§7) |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 2/3 | deferred (§7) |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 2/14 | deferred (§7) |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 2/2 | deferred (§7) |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 1/2 | deferred (§7) |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 1/1 | deferred (§7) |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 5/18 | deferred (§7) |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 2/2 | deferred (§7) |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 3/4 | deferred (§7) |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 1/2 | deferred (§7) |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 2/10 | deferred (§7) |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 1/1 | deferred (§7) |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 1/1 | deferred (§7) |
| `constantTerm_add` | 13 | 1/2 | deferred (§7) |
| `constantTerm_smul` | 11 | 1/1 | deferred (§7) |

**Of the 96 rows above, 8 are this set's (1 / 283 ready, 7 / 1,295 leaves) and 88 are deferred by §7.**
The other namespaces' 29 ready / 5,344 and 169 leaves / 46,039 are not this column's; the four
withheld rows are named in §0.1.

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py` from the port's statement index: per row, every declaration whose
statement is not in the port, with its pin line and span. **62 "imported" lines overstate the reuse by
55** (§2.1: the private-only copies).

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `integrable_smoothAtom_and_integrable_weylShift_adicCompletion` | 260 | 3 | 257 | 16 |
| `integrable_complexAtom_and_integrable_moebiusShift` | 205 | 0 | 205 | 6 |
| `integrable_realAtom_and_integrable_moebiusShift` | 165 | 0 | 165 | 9 |
| `integral_one_add_sq_cpow_neg_eq_GammaReal_div` | 349 | 51 | 298 | 11 |
| `integral_one_add_norm_sq_cpow_neg_eq_pi_div` | 88 | 0 | 88 | 5 |
| `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` | 159 | 2 | 157 | 13 |
| `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` | 136 | 2 | 134 | 11 |
| `exists_bound_norm_integral_mixedSpace_archAtom_prod` | 103 | 4 | 99 | 7 |
| **8 rows** | **1465** | **62** | **1403** | **78** |

### `integrable_smoothAtom_and_integrable_weylShift_adicCompletion` (order A)

260 declaration lines, 3 imported, **257 to write** in 16 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 108 | 158 | theorem |
| `integrable_atom` | 36 | 75 | theorem |
| `integrableOn_of_locallyConstantOn` | 20 | 55 | theorem |
| `solution` | 19 | 266 | theorem |
| `nhdsNE_zero_neBot` | 14 | 144 | theorem |
| `exists_uniformizer` | 11 | 25 | theorem |
| `isOpen_ball` | 9 | 46 | theorem |
| `two_le_absNorm` | 7 | 36 | theorem |
| `v_lt_one_of_close` | 6 | 129 | theorem |
| `v_le_one_of_close` | 6 | 135 | theorem |
| `modulus_eq_one_of_v_eq_one` | 5 | 115 | theorem |
| `ofAdd_neg_lt_one` | 5 | 124 | theorem |
| `modulus_mul_modulus_inv` | 4 | 120 | theorem |
| `v_sub_comm` | 3 | 141 | theorem |
| `mem_O_iff` | 2 | 111 | theorem |
| `mem_O_iff'` | 2 | 113 | theorem |

### `integrable_complexAtom_and_integrable_moebiusShift` (order A)

205 declaration lines, 0 imported, **205 to write** in 6 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 90 | 119 | theorem |
| `integrable_complexFactor` | 34 | 16 | theorem |
| `floor` | 33 | 78 | theorem |
| `norm_complexFactor_le` | 28 | 50 | theorem |
| `solution` | 12 | 209 | theorem |
| `entries_pos` | 8 | 111 | theorem |

### `integrable_realAtom_and_integrable_moebiusShift` (order A)

165 declaration lines, 0 imported, **165 to write** in 9 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 85 | 84 | theorem |
| `integrable_realFactor` | 21 | 34 | theorem |
| `floor` | 14 | 62 | theorem |
| `solution` | 12 | 169 | theorem |
| `entries_pos` | 8 | 76 | theorem |
| `norm_sub_I` | 7 | 16 | theorem |
| `norm_realFactor_eq` | 7 | 55 | theorem |
| `unit_ne_zero` | 6 | 28 | theorem |
| `norm_unit` | 5 | 23 | theorem |

### `integral_one_add_sq_cpow_neg_eq_GammaReal_div` (order B)

349 declaration lines, 51 imported, **298 to write** in 11 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `integral_cpow_neg_one_add_sq` | 77 | 216 | theorem |
| `scaledGammaIntegral` | 64 | 15 | theorem |
| `integrable_uncurry_kernel` | 49 | 167 | theorem |
| `integrableOn_scaledGamma` | 28 | 88 | theorem |
| `integral_value_gammaR` | 21 | 337 | theorem |
| `sqrtpi_gamma_mul_gammaR` | 20 | 317 | theorem |
| `arch_integral_value` | 10 | 293 | theorem |
| `cpow_neg_eq_gamma_inv_mul_integral` | 9 | 79 | theorem |
| `gammaR_two_mul` | 7 | 303 | theorem |
| `gammaR_two_mul_add_one` | 7 | 310 | theorem |
| `solution` | 6 | 358 | theorem |

(The row's 51 imported lines are `integrable_one_add_sq_rpow_neg`, §2.1 — private-only in the port, so
the worklist's 298 is optimistic by 51 and honest only after the §2.1 decision.)

### `integral_one_add_norm_sq_cpow_neg_eq_pi_div` (order B)

88 declaration lines, 0 imported, **88 to write** in 5 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `integral_value` | 40 | 57 | theorem |
| `setIntegral_Ioi_comp_one_add` | 17 | 16 | theorem |
| `integral_radial` | 17 | 40 | theorem |
| `integral_one_add_cpow_neg` | 7 | 33 | theorem |
| `solution` | 7 | 97 | theorem |

### `tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half` (order B)

159 declaration lines, 2 imported, **157 to write** in 13 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 33 | 130 | theorem |
| `norm_F_le` | 32 | 68 | theorem |
| `tendsto_F` | 24 | 100 | theorem |
| `norm_atom_le` | 15 | 34 | theorem |
| `solution` | 9 | 163 | theorem |
| `norm_pow_le` | 7 | 27 | theorem |
| `normSq_le` | 7 | 55 | theorem |
| `continuous_atom` | 6 | 49 | theorem |
| `rpow_le_max` | 6 | 62 | theorem |
| `integrable_bound` | 6 | 124 | theorem |
| `norm_atom` | 5 | 22 | theorem |
| `exponent_cast` | 4 | 18 | theorem |
| `atom` | 3 | 13 | def |

### `tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half` (order B)

136 declaration lines, 2 imported, **134 to write** in 11 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `norm_F_le` | 32 | 53 | theorem |
| `main` | 32 | 108 | theorem |
| `tendsto_F` | 23 | 85 | theorem |
| `continuous_atom` | 10 | 34 | theorem |
| `solution` | 9 | 140 | theorem |
| `norm_phase` | 6 | 18 | theorem |
| `norm_atom` | 6 | 24 | theorem |
| `rpow_le_max` | 6 | 47 | theorem |
| `continuous_phase` | 4 | 30 | theorem |
| `atom` | 3 | 13 | def |
| `sq_le` | 3 | 44 | theorem |

### `exists_bound_norm_integral_mixedSpace_archAtom_prod` (order B)

103 declaration lines, 4 imported, **99 to write** in 7 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `main` | 27 | 76 | theorem |
| `cx_bound` | 23 | 32 | theorem |
| `real_bound` | 17 | 15 | theorem |
| `solution` | 15 | 103 | theorem |
| `integrable_maj` | 11 | 65 | theorem |
| `int_real` | 3 | 55 | theorem |
| `int_cx` | 3 | 58 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af13-landed.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion \
  --nodes AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift \
  --nodes AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift \
  --nodes AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div \
  --nodes AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div \
  --nodes AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half \
  --nodes AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half \
  --nodes AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod \
  --json build/af14-li0-advise.json
python3 port_plan.py --json build/af14-li0-advise.json     # 1,578 raw / 1,457 decl / 58 in port / 1,393 net
python3 build/af-worklist.py LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion \
  LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift \
  LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift \
  LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div \
  LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div \
  LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half \
  LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half \
  LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod
python3 build/af14-forecast.py \
  AutomorphicForm.LocalIntertwining.integrable_smoothAtom_and_integrable_weylShift_adicCompletion \
  AutomorphicForm.LocalIntertwining.integrable_complexAtom_and_integrable_moebiusShift \
  AutomorphicForm.LocalIntertwining.integrable_realAtom_and_integrable_moebiusShift \
  AutomorphicForm.LocalIntertwining.integral_one_add_sq_cpow_neg_eq_GammaReal_div \
  AutomorphicForm.LocalIntertwining.integral_one_add_norm_sq_cpow_neg_eq_pi_div \
  AutomorphicForm.LocalIntertwining.tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half \
  AutomorphicForm.LocalIntertwining.tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half \
  AutomorphicForm.LocalIntertwining.exists_bound_norm_integral_mixedSpace_archAtom_prod   # the §0.3 forecast
python3 build/af14-shelf-appendix.py                                                      # Appendix A
cd ../../lean
ROWS="Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_smoothAtom_and_integrable_weylShift_adicCompletion.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_complexAtom_and_integrable_moebiusShift.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_integrable_realAtom_and_integrable_moebiusShift.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_sq_cpow_neg_eq_GammaReal_div.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_one_add_norm_sq_cpow_neg_eq_pi_div.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_normSq_rpow_sub_one_mul_complexAtom_nhdsGT_one_half.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_tendsto_integral_sq_rpow_sub_one_mul_realAtom_nhdsGT_one_half.lean \
  Theorems/Thm_AutomorphicForm_LocalIntertwining_exists_bound_norm_integral_mixedSpace_archAtom_prod.lean"
for pin in Def_LanglandsTunnell_TateLocalZeta Def_NumberField_AdelicHaar; do
  python3 spec/gate_scan.py --pin Definitions/$pin.lean --rows $ROWS
done
```

`--rows` takes a **list** in one flag; repeating it silently keeps only the last one (AF13's finding,
re-hit here on the first attempt).

**Forecast on landing** (read at §0.3): `needed` **861 / 350,288 → 853 / 348,710**, literal
**874 / 353,763 → 866 / 352,185**, frontier **1,554 / 777,078 → 1,562 / 778,656**, ready
**62 / 16,259 → 63 / 16,705**, leaves **232 / 58,795 → 225 / 57,500**, and **2 rows readied / 729
silo**. The re-read must confirm every one of those figures, and must say what happened to the two
`moebiusShift` rows §7 leaves one premise short: if the `MeasureTheory` premise lands in another column
before the re-read, this set readies four rows, not two.
