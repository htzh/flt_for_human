# SET-AF15 — the Borel decomposition of an adelic point, and the two general archimedean atom integrals

**Status: LANDED 2026-11-02** — the manager's layer plus one dispatch, all three rows, all gates green;
**§5.1 records the landing and the re-read**, which is exact on every figure and readies the predicted
nine. The order is
[WORKORDER-AF15-adelic-iwasawa-atom-general.md](WORKORDER-AF15-adelic-iwasawa-atom-general.md): both
module skeletons exist, build and wire clean (`check_port --force` 0 / 0 / 0 on each), and
`lean/tmp/probe-af15-statements.lean` states all three headlines with exactly three `sorry` warnings.
Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF14 left. It is the **fifteenth** `AutomorphicForm`-serving set, and it is **two subjects in one
set on purpose**: the block SET-AF14's own re-read readied (two rows, 729 silo) and the **seed** SET-AF14
§7 deferred as the cheapest unblock on the shelf (`exists_mem_adelicBorel_mul_eq`, 372, measured to
ready **nine** rows). Together they are 1,101 silo — a third of a dispatch by the recipe's own band —
and they are independent, so the dispatch splits into two orders over two new modules.

The set is **3 rows / 1,101 silo / 1,031 lines to write in 91 declarations** — `port_plan`'s once-cost on
1,044 declaration lines after its 13 duplicate pin copies. `build/af-worklist.py` reads 1,047 declaration
lines (three more: a parse convention) and calls **51 of them "imported", which not one of them is**
(§2.1), so its "996 to write" is the same 1,031 with the private copies counted as reuse. `port_plan`'s
net is consequently **1,006; the honest one is 1,031**. Two orders. Its landing is forecast to ready
**nine rows / 2,168 silo** (§0.3), eight of them this column's.

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| A — the Borel decomposition of an adelic point | 1 | 372 | 353 | new `AutomorphicForm/Adelic/AdelicIwasawa.lean` |
| B — the two general archimedean atom integrals | 2 | 729 | 694 | new `AutomorphicForm/Adelic/ArchAtomGeneral.lean` |
| | **3** | **1,101** | **1,047** | two files, one dispatch |

## 0. The read

### 0.1 The figures

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af15-scope.json
python3 frontier.py --selfcheck
```

| figure | value | SET-AF14 §5.1 (at its landing) |
|---|---:|---:|
| `needed [F terminal]` | **853 / 348,710** | 853 / 348,710 |
| `needed [literal]` | 866 / 352,185 | 866 / 352,185 |
| frontier F | **1,562 / 778,656** | 1,562 / 778,656 |
| ready rows, all namespaces | 63 / 16,705 | 63 / 16,705 |
| ready rows, `AutomorphicForm` | **34 / 11,361** | 34 / 11,361 |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 |
| leaves, `AutomorphicForm` | **56 / 11,461** | 56 / 11,461 |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 | 140 / 74,620 |
| `--selfcheck` | **PASS** (1,381 `Thm_` sources, 1,562 declared names) | PASS (1,381 / 1,562) |
| correction | **none needed** | none needed |

Same tree, same read as SET-AF14's landing: the delta is zero on every row and no correction is owed.
Both blocks are quoted whole and every row is accounted for in Appendix A — 34 ready / 11,361 and 56
leaves / 11,461, of which **3 rows / 1,101 are this set's** and 87 are deferred (§7 groups them). The
withheld block is the same four rows (two `ModularCurve` Tate-module rows, two `AlgebraicCurve` `Pic₀`
rows, 831 lines).

### 0.2 Why the two subjects are one set

- **The pair is what AF14's re-read created; the seed is what AF14's scoping identified.** AF14 §0.3
  forecast that its landing would ready `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal`
  (465) and `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` (264), and §5.1 measured exactly
  that. AF14 §7 measured `exists_mem_adelicBorel_mul_eq` (372) as readying nine rows / 2,168 silo. Both
  are ready on *this* shelf; neither was available when the previous briefs were written.
- **They are 1,101 silo, which is one dispatch, not two.** Splitting them would leave a 729-silo pair as
  a set of its own against the recipe's 1,100–1,600-line band, and would spend a whole manager's layer
  and a whole gate cycle on it.
- **They are independent, so bundling costs no ordering.** All three rows are layer 0 of the slice
  (`port_plan`'s layers block), none cites another, and the two orders touch disjoint pin files and
  disjoint new modules — the recipe's §5 test for parallel dispatch passes.
- **The pair is the last piece of the `LocalIntertwining` cluster's *own* story on the shelf.** Its two
  rows are the general statements whose `k = 0` / `a = b = 0` cases AF14 landed; taking them leaves the
  cluster with **one** ready row (1,291, the Weyl pair's half), **three** rows one premise away, one row
  two premises away, and two rows outside the D–S cone altogether (§7). Leaving them would leave the
  column holding the special cases of theorems it had not ported — the worst of both readings for the
  next scoping.

### 0.3 What a landing would change — the forecast

`frontier.py` has no "what does this landing ready" reading; the landing is simulated with the same
`analyze` call the shelf read uses (`build/af14-forecast.py`, 4.9 s):

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 853 / 348,710 | **850 / 347,609** | −3 / −1,101 ✓ (the three rows' silo, exact) |
| `needed [literal]` | 866 / 352,185 | **863 / 351,084** | −3 / −1,101 ✓ |
| frontier F | 1,562 / 778,656 | **1,565 / 779,757** | +3 / +1,101 ✓ |
| ready rows, all namespaces | 63 / 16,705 | **69 / 17,772** | +6 rows, +1,067 silo |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — (no leaf is taken, none readied) |

**Rows readied (9 / 2,168 silo)** — the seed's eight-plus-one, unchanged by the pair:

| row | silo | prem | lev | what it is |
|---|---:|---:|---:|---|
| `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum` | 890 | 2 | 3/5 | another column's — the reason the nine are two dispatches |
| `exists_flat_isInducedSection_sum_eq_of_differentiable_family` | 264 | 3 | 5/11 | the span lemma: a differentiable family of flat sections spans finitely many flat sections |
| `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_of_apply_ne_zero` | 245 | 1 | 2/2 | the `diagOne` value of a Whittaker function is non-zero on the maximal compact |
| `exists_isCompact_forall_mul_eq_borel_mul_archHeight_le_of_glFin_mem_finiteIntegralGL2` | 227 | 3 | 1/2 | the centre-cut Siegel set is compact at bounded height |
| `exists_norm_le_mul_adelicHeight_rpow_of_isInducedSection` | 161 | 2 | 1/4 | a section is bounded by a power of the height |
| `continuousOn_of_isInducedSection_of_continuousOn_maximalCompact` | 155 | 1 | 1/6 | continuity on the maximal compact transfers to the section |
| `continuousOn_of_forall_apply_borel_mul_eq_of_continuousOn` | 116 | 1 | 1/4 | the same, from the pointwise Borel form |
| `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_of_flat_family` | 81 | 2 | 1/1 | a flat family is invariant in its `K`-argument |
| `IsInducedSection.eq_of_eqOn_maximalCompact` | 29 | 1 | 1/5 | a section is determined by its values on the maximal compact |

Eight of the nine are this column's (1,278 silo) and they are **one subject**: *an induced section is
determined by, and inherits the regularity of, its restriction to the maximal compact* — the pointwise
consequence of the Borel decomposition that order A ports. That block is AF16's obvious subject. The
ninth (890, `EisensteinGeneral.Piece.…`) is another column's, and is the reason the nine cannot be one
dispatch here.

Note what the pair does **not** do: it readies nothing (the same measurement as AF14's Weyl pair and
indicator row). Its value is that it *closes* the evaluation story and removes 729 silo of ready shelf,
not that it opens work.

## 1. The three rows

| row (`AutomorphicForm.` dropped) | silo | decls | prem | lev | what it states |
|---|---:|---:|---:|---:|---|
| `exists_mem_adelicBorel_mul_eq` | 372 | 31 | 1 | **14/63** | every `g : AdelicGL2` is `b * k` with `b` in the adelic Borel, `glFin k` in `finiteIntegralGL2`, and every archimedean component of `glArch k` a `WindowedSiegel.IsRowIsometry` — the **Borel/Iwasawa decomposition** of an adelic point |
| `LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` | 465 | 44 | 1 | 1/6 | `∫ x, ((x - I)/√(1+x²))^k · (1+x²)^-(s+1/2) = (-I)^k · Γ_ℝ(2s)·Γ_ℝ(2s+1) / (Γ_ℝ(2s+1+k)·Γ_ℝ(2s+1-k))` for `re s > 0` — the real atom's integral with its weight `((x-I)/√(1+x²))^k`, by a recursion on `k` |
| `LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` | 264 | 16 | 4 | 1/6 | `∫ z, z^a z̄^b (1+‖z‖²)^-t = π·a!·Γ(t-1-a)/Γ t` if `a = b`, else `0`, for `((a:ℝ)+b)/2 + 1 < re t` — the complex atom's general moment integral |

**The two pair rows are proved *from* their special cases, and that is not invertible.** Each has
`prem = 1` and the premise is the row SET-AF14 landed: the 465 row calls
`integral_one_add_sq_cpow_neg_eq_GammaReal_div s hs` at pin `:318`, the 264 row calls
`integral_one_add_norm_sq_cpow_neg_eq_pi_div ((t-1)/2) hs` at pin `:171`. So AF14 §0.3(ii)'s suggestion
that the port "may derive rows 4 and 5 from them" is **withdrawn here**: the pin proves special →
general, and inverting it would be circular. The special rows stay as they are, and the general ones are
written on top of them. What is *not* true either is that the general row's proof is a short rider: the
465 row is a 44-declaration recursion on `k` (`hasDerivAt_phase`, `hasDerivAt_phase_zpow`,
`recursion_raw` 24, `closed_form_nat` 21, `RHS_step` 74), and the 264 row is a 16-declaration moment
recursion (`angular_eq_zero`, `integral_eq_zero_of_ne`, `moment_succ`, `closed_form` 66).

**Visibility: all three are private preludes with one public headline each.** The pin files carry 35, 47
and 17 `private` declarations and exactly **one** public theorem apiece; so the checked surface at the
pin's visibility is **three declarations**, and the recipe's dropped-`private` **surface gate is this
set's real statement check** (§5) — at AF14 the flat public surfaces made it a formality, here it is
what tells you the 99 helpers are the pin's.

**Namespaces.** The three pin labels are already subject names and are kept, minus the pin's file
prefix: `AutomorphicForm.LocalIntertwining.IwasawaArch` (the seed), `…LocalIntertwining.ArchRealWeight`
(the 465 row, pin `M4aP2DGK.ArchRealWeight`) and `…LocalIntertwining.ArchComplexMoments` (the 264 row,
pin `M4aP2DGK.ArchComplexMoments`). The three headlines stay public at their pin names under
`AutomorphicForm.` / `AutomorphicForm.LocalIntertwining.`.

## 2. The price

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.exists_mem_adelicBorel_mul_eq \
  --nodes AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  --nodes AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg \
  --json build/af15-advise.json
python3 port_plan.py --json build/af15-advise.json     # 1,101 raw / 1,044 decl / 25 in port / 1,006 net
python3 build/af-worklist.py exists_mem_adelicBorel_mul_eq \
  LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
```

`port_plan`: raw **1,101** → declaration lines **1,044** → −13 duplicate copies → 1,031 once-cost →
**−25 already in the port** → **NET NEW 1,006**; boilerplate 57; 100 distinct declaration groups.
The worklist (Appendix B): **1,047 declaration lines, 51 imported, 996 to write in 91 declarations**.

### 2.1 The reuse is zero, and every claimed line of it is a private copy

`port_advise`'s substitution block reports **7 declarations, ≈43 lines "not to re-prove"**; the worklist
counts 51 imported lines across 11 declarations. Row by row, read against the pin and against the port's
visibility, **not one of them is importable**:

| pin declaration | row | lines | claimed port copy | reading |
|---|---|---:|---|---|
| `map_ringEquiv` | seed `:101` | 21 | `BigCellExpansion.Transport.IsRowIsometry.map_ringEquiv` | statement-identical, but **`private`** (`BigCellExpansion.lean:165`; the `Reserve/` copy the advise names is `private` too) — re-state 21 lines, `private` |
| `norm_ringEquivComplexOfIsComplex` | seed `:145` | 4 | `BigCellExpansion.RealPlaces.norm_ringEquivComplexOfIsComplex` | **`private`** (`:192`) — re-state, `private` |
| `projV` | seed `:171` | 3 | `AutomorphicForm.evFin` (identical definition) | **`private`** (`InducedSectionMaximalCompact.lean:364`) — re-state, `private` |
| `projW` | seed `:168` | 3 | `BigCellExpansion.RealPlaces.projArch` | **`private`**, and a different *definition* of the same function (structure-projection against `(archEval w).comp adeleArch`) — re-state, `private` |
| `mkUnit` | seed `:261` | 8 | `AutomorphicForm.kOne` | **FR-0134 again**: same *type* `AdelicGL2`, different function (`kOne` includes one archimedean component and is `1` elsewhere; the pin's `mkUnit` assembles arbitrary local data) — **write it**, `private` |
| `rad`, `base`, `phase`, `Q` | 465 row | 2+2+2+2 | `HARCHR.c00`, `RealIwasawa.botRow`, `RealIwasawa.logLine`, `HARCHR.q` | **all `def`s matched by shape only** — `botRow` is a `2×2` row matrix, `base`/`phase` are the pin's complex scalars; **write them** (FR-0134) |
| `W`, `M` | 264 row | 2+2 | `PeriodPair.addCoreE`, `WLight.qN` | **`def`s matched by shape only** — unrelated; **write them** (FR-0134) |

**So the honest net new is 1,031 lines (once-cost), and the worklist's 996 is optimistic by exactly the
51 lines it calls imported.** This is the third appearance of FR-0133 (`port_plan` and the worklist
count statement-identical `private` port copies as in-port) and the second of FR-0134 (a `def` matched
by type, not body) — and it is the first set where the two together make the *whole* substitution block
illusory. The instruction is therefore simple: **write all 102 declarations the pin files contain**
(99 private + 3 headlines), and where a private port copy of the same statement exists, copy its *text*
rather than re-derive it, citing the file and line.

**No port-once block and no siblings block**: the three pin files share no declaration, and the sibling
relation they *do* have with SET-AF14's rows is one-directional (§1) — `port_plan`'s siblings block is
empty because it only looks inside the slice.

## 3. The definition gate

`spec/gate_scan.py` over the four `Def_` modules in the three rows' closure — the seed's three wrapper
imports plus the one its `S_` file imports and its wrapper does not
(`Def_AutomorphicForm_ArchWeightCharTransport`, the FR-0129 class of gap, scanned against the `S_` file
rather than the wrapper):

| pin `Def_` module | port home | used | missing |
|---|---|---:|---:|
| `Def_AutomorphicForm_BorelSubgroup` | `…/AutomorphicForm/Adelic/BorelSubgroup.lean` | 2/19 | **0** |
| `Def_AutomorphicForm_RowIsometryInvariance` | `…/Adelic/WindowedSiegel/RowIsometry.lean` | 1/12 | **0** |
| `Def_NumberField_AdelicLevel` | `…/NumberTheory/AdelicLevel/{Level,Projections}.lean` | 9/114 | **0** |
| `Def_AutomorphicForm_ArchWeightCharTransport` | `…/Adelic/ArchWeightCharTransport.lean` | 3/14 | **0** |

**Every used declaration is ported and public** (`adelicBorel`, `borelSubgroup`, `IsRowIsometry`,
`glFin`, `glArch`, `archComponent`, `archEval`, `adeleArch`, `adeleFin`, `finiteIntegralGL2`,
`glEquivOfRingEquiv`, `norm_ringEquivRealOfIsReal`, …), and the two pair rows import **no** `Def_`
module at all: their wrappers name only mathlib. **No `Def_` node, no promotion, no migration**; the
seed's one graph premise `LocalGL2.iwasawa_decomposition` is ported
(`RepTheory/LocalLanglands/IwasawaDecomposition.lean:257`, wired) — the *local* decomposition the adelic
one assembles place by place. All four port homes are wired, non-legacy modules that are only imported.

## 4. The homes

**Two new modules.**

- **Order A — `FLTForHuman/AutomorphicForm/Adelic/AdelicIwasawa.lean`.** Subject: the Borel/Iwasawa
  decomposition of an adelic point, assembled from the local decompositions at the archimedean places
  and the integrality of the finite part. Imports `AutomorphicForm/Adelic/BorelSubgroup.lean`
  (`adelicBorel`), `…/Adelic/WindowedSiegel/RowIsometry.lean` (`IsRowIsometry`),
  `…/NumberTheory/AdelicLevel/{Level,Projections}.lean` (`glFin`, `glArch`, `archComponent`, `archEval`,
  `adeleArch`, `adeleFin`, `finiteIntegralGL2`), `…/Adelic/ArchWeightCharTransport.lean`
  (`glEquivOfRingEquiv`, `norm_ringEquivRealOfIsReal`),
  `…/RepTheory/LocalLanglands/IwasawaDecomposition.lean` (`LocalGL2.iwasawa_decomposition`), and the
  mathlib modules the wrappers name. **Not** `IwasawaWeylUnipotent.lean`, which is the *continuous*
  K-factor and a later subject. Nothing above that list imports the new module, so it is cascade-free.
  (The name is `AdelicIwasawa`, not `IwasawaDecomposition`, because the port already has
  `RepTheory/LocalLanglands/IwasawaDecomposition.lean` for the local statement.)
- **Order B — `FLTForHuman/AutomorphicForm/Adelic/ArchAtomGeneral.lean`.** Subject: the general
  archimedean atom integrals — the weight recursion at a real place and the moment recursion at a
  complex place — each closed onto its Γ- and π-value. Imports
  `FLTForHuman.AutomorphicForm.Adelic.ArchAtomValues` (the two special rows, which are its premises) and
  the mathlib modules the pin files name (`Analysis.SpecialFunctions.Gamma.Deligne`,
  `Analysis.SpecialFunctions.Gaussian.GaussianIntegral`, `MeasureTheory.Measure.Lebesgue.Complex`,
  `MeasureTheory.Integral.Bochner.Basic`). It does **not** import order A, and nothing imports it:
  cascade-free.

**Import direction, measured.** Order A's premise modules sit in `AutomorphicForm/Adelic`,
`NumberTheory/AdelicLevel` and `RepTheory/LocalLanglands`; order B's is the module SET-AF14 landed. No
premise is above its home and the two new modules are imported by nothing, so both are acyclic. The one
direction worth stating: **the two pair rows must sit above `ArchAtomValues.lean`**, because their proofs
consume its two headlines — which is why a new module is the import-correct home rather than an
insertion into AF14's module.

## 5. The cut

**Two orders, one dispatch, two workers.**

| order | rows | silo | lines | decls | module |
|---|---:|---:|---:|---:|---|
| A — the Borel decomposition | 1 | 372 | 353 | 31 | `AdelicIwasawa.lean` |
| B — the two general atom integrals | 2 | 729 | 694 | 63 | `ArchAtomGeneral.lean` |

**Disjoint files, so the two orders are safe concurrently** (recipe §5): three distinct `S_` files, two
distinct new modules, and no row of one order cited by the other. Order B carries the set's cost (63
declarations) and order A the set's fan-in (14 in-cone / 63 project consumers) — give B the earlier
start, A the earlier review.

**The manager's layer** is the two skeletons with their `spec-pin:` wires (A: one wrapper + one `S_`
file; B: two + two — five lines in all), their imports and opens; a **statements probe of all three
headlines** before dispatch; and the §2.1 instruction written into the order ("write all 102, copy the
private texts, do not import the eleven"). No `Def_` node, no promotion, no migration, no legacy edit.

**Gates, per order** (recipe §6):

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, and the ok count
   **measured**: it will be **1 per row** here (the headline) at the pin's visibility, and **~102** at
   the dropped-`private` surface. That second reading is this set's real statement check (§1): read
   every `MISMATCH` and `MISSING` it produces — a `MISSING` is a port-side helper (keep it private), a
   `MISMATCH` is a mis-transcription to fix.
2. `#print axioms` on the three headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` silent, and its own
   `flock`/`timeout 280 lake build`. No tree build, no dependents.
4. `dedup.py --within` / `move_dead.py --dry-run` per module; a `shape` cluster of a headline against
   its own helper is the pin's `solution`-calls-`main` structure and stays, with the reason recorded.
5. `spec/AutomorphicFormSetAF15Consumer.lean` — **two zones**, real compositions, no `#check`, no
   `sorry`:
   - **the decomposition meets the induced-section law.** From
     `exists_mem_adelicBorel_mul_eq g` take `b, k` with `b ∈ adelicBorel`, `glFin k ∈ finiteIntegralGL2`
     and `g = b * k`, and apply `IsInducedSection`'s defining law (`InducedSection.lean:28`) to read
     `φ g = χ₁ (borelDiagFst b) * χ₂ (borelDiagSnd b) * φ k`: an induced section is determined by its
     `k`-part, with the character factor explicit. That is the statement the eight rows of §0.3 build
     on, and it is proved, not asserted.
   - **the general evaluations return the special ones.** At `k = 0` (the 465 row) and at
     `a = b = 0, t = 2s + 1` (the 264 row), prove the identity between the general row's value and
     AF14's special row's value — `Γ_ℝ(2s)·Γ_ℝ(2s+1)/(Γ_ℝ(2s+1)·Γ_ℝ(2s+1)) = Γ_ℝ(2s)/Γ_ℝ(2s+1)` and
     `π·0!·Γ(2s+1-1-0)/Γ(2s+1) = π/(2s)` — a real, executed composition of the two modules.
   It imports only the two new modules (and their premises). The error count is the deliverable metric.
6. Zero warnings, no `sorry`/`admit`/`axiom`/`native_decide`, no `set_option` beyond `autoImplicit false`,
   no new import without a report.

### 5.0 The manager's layer (landed 2026-11-02)

Both skeletons exist — `AdelicIwasawa.lean` 66 lines with two `spec-pin:` lines and ten imports,
`ArchAtomGeneral.lean` 71 lines with four `spec-pin:` lines and six imports — and each elaborates silent
and builds green (`flock`/`lake build <module>`, 3,549 jobs for the closure, which included building the
premise module `RepTheory/LocalLanglands/IwasawaDecomposition` for the first time);
`check_port --force` reads **0 ok / 0 mismatch / 0 missing** on both, so the wire is correct before a
line of mathematics exists. The statements probe (`lean/tmp/probe-af15-statements.lean`) states all
three headlines verbatim from their wrappers and elaborates with **exactly three `declaration uses
'sorry'` warnings**; it settled that the probe needs `open AutomorphicForm` in its file-level opens,
because the port nests `AdelicGL2` under `AutomorphicForm` where the pin reaches it through
`NumberField.AdelicLevel` (an `open` does not touch a statement's text, so this is probe-side only).
The §2.1 decision is written into the order: write all 102 declarations, copy the text of the four
`private` port copies (`map_ringEquiv`, `norm_ringEquivComplexOfIsComplex`, `projV`→`evFin`,
`projW`→`projArch`), and **write** `mkUnit` and the six `def`s the advise matched by shape
(`kOne`, `HARCHR.c00`/`q`, `RealIwasawa.botRow`/`logLine`, `PeriodPair.addCoreE`, `WLight.qN`), because
those matches are type-only.

### 5.1 The landing (2026-11-02)

**Files.** `AutomorphicForm/Adelic/AdelicIwasawa.lean` 66 (skeleton) → **427**;
`AutomorphicForm/Adelic/ArchAtomGeneral.lean` 71 → **762**; `spec/AutomorphicFormSetAF15Consumer.lean`
(144, new). **102 declarations: 3 public, 99 `private`** — the three headlines at the pin's names, the
rest in the three row namespaces (`IwasawaArch` 35, `ArchRealWeight` 47, `ArchComplexMoments` 17), at the
pin's visibility exactly.

**Gates, re-run by the manager.** Edit loops silent (4.7 s / 4.4 s); own `flock`/`timeout 280 lake build`
green and silent (3,488 / 3,129 jobs); `check_port --force` **1 ok / 0 mismatch / 0 missing** (order A)
and **2 ok / 0 / 0** (order B) at the pin's visibility — the three declarations the pin makes public;
**the surface gate (all 99 `private` dropped) 36 ok and 66 ok, `0 mismatch / 0 missing`** — so all 99
helpers, *including the eleven the advise called imported*, are byte-faithful to their pin statements;
`#print axioms` on all three headlines `[propext, Classical.choice, Quot.sound]`; the statements probe
still exactly three `sorry` warnings; the consumer zone **0 errors, 0 warnings**; `dedup --within` order A
**0 clusters**, order B **2 shape clusters**, each a headline against its own `main` (the pin's
`solution`-calls-`main` structure) and kept; `move_dead --dry-run` **0 declarations / 0 lines** on both.
Zero warnings anywhere.

**Plan against actual.** Lines: **1,052 appended** (order A 361, order B 691) against `port_plan`'s
once-cost 1,031 — **+2.0 %**; declarations **102** against the pins' 102 (the worklist's 91 plus the
eleven it counted as imported). Checker: 3 at the pin's visibility, 102 at the dropped surface — every
declaration in the set is a pin statement, and none is a port-side helper.

**The seed's assembly and the 465 row's recursion both transcribed clean, first compile.** The rotation
block kept the pin's `RCLike` generality (`rotMat` … `exists_iwasawa_rclike` at `{L} [RCLike L]`,
`bottomRow_normSq_pos` at `{K} [NormedField K]`, no `ℝ`/`ℂ` split); `mkUnit` was written, not `kOne`; and
the `k`-recursion bottoms out in `closed_form_zero` on the ported
`integral_one_add_sq_cpow_neg_eq_GammaReal_div` (pin `:318`) exactly where §1 said it would, with
`RHS_step` using `Complex.Gammaℝ_add_two`/`Gammaℝ_eq_zero_iff` for the pole case.

**Manager's edits, all recorded.** (1) The order's gate 6 said the consumer could reach `IsInducedSection`
through the two new modules; it cannot — neither imports `AutomorphicForm/Adelic/InducedSection` — so the
consumer names that import itself (no port module's import list touched), and the work order is corrected
below. (2) Three file-level `open`s the skeleton lacked, all present in the pin: `open
NumberField.AdelicLevel` (pin `:162`, needed for `archEval`, `finAdeleEval`, `finiteIntegralGL2`,
`mem_finiteIntegralGL2_iff`), `open Complex` in `ArchRealWeight` (pin `:16`), and `open Set Complex
Filter` + `open scoped ComplexConjugate` in `ArchComplexMoments` (pin `:18–19`). An `open` is not part of
a statement. (3) One v4.34 textual fix: `mul_inv_rev` → `_root_.mul_inv_rev` (pin `:338`), because
`Matrix.mul_inv_rev` is ambiguous under the pin's `open Matrix`; and `if_pos` → `ite_eq_left` in the
consumer (pin `:264`). No import was added to either port module.

**The re-read is exact, and the nine readied rows are the predicted ones.**

| figure | before | **after** | Δ |
|---|---:|---:|---:|
| `needed [F terminal]` | 853 / 348,710 | **850 / 347,609** | −3 / −1,101 ✓ (the three rows' silo, exact) |
| `needed [literal]` | 866 / 352,185 | **863 / 351,084** | −3 / −1,101 ✓ |
| frontier F | 1,562 / 778,656 | **1,565 / 779,757** | +3 / +1,101 ✓ |
| ready rows, all namespaces | 63 / 16,705 | **69 / 17,772** | +6 / +1,067 |
| ready rows, `AutomorphicForm` | 34 / 11,361 | **39 / 11,538** | +5 / +177 (= −1,101 + 1,278) |
| leaves, all namespaces | 225 / 57,500 | 225 / 57,500 | — |
| withheld by the FR-0044 guard | 4 / 831 | 4 / 831 | — |
| `--selfcheck` | PASS (1,381 / 1,562) | **PASS** (1,384 `Thm_` sources, 1,565 declared names) | — |

**Nine rows readied, 2,168 silo** — the eight `AutomorphicForm` rows of §0.3 (`exists_flat_isInducedSection_sum_eq_…`
264, `exists_mem_maximalCompactAt_apply_diagOne_mul_ne_zero_…` 245, `exists_isCompact_forall_mul_eq_borel_…`
227, `exists_norm_le_mul_adelicHeight_rpow_…` 161, `continuousOn_of_isInducedSection_…` 155,
`continuousOn_of_forall_apply_borel_mul_eq_…` 116, `exists_forall_apply_mul_eq_of_mem_maximalCompactAway_…`
81, `IsInducedSection.eq_of_eqOn_maximalCompact` 29 = 1,278) plus `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum`
(890). Nothing else moved: no leaf entered or left. **AF16's cut is those eight rows** — one subject, one
dispatch, and the first time in five sets that a landing opens more work than it consumes.

## 6. Risk register

1. **The seed is an assembly argument, not a transcription of one lemma.** It builds an adelic matrix
   from its archimedean and finite components (`assemble`, with a cofinite integrality condition), proves
   the two projections read it back (`projW_assemble`/`projV_assemble`), builds the local rotation matrices
   place by place (`rotMat`/`rotMatN`, `isRowIsometry_rotMatN`, `bottomRow_normSq_pos`), and then glues.
   Read the pin in its own order: `rotMat*` → `exists_iwasawa_rclike` →
   `exists_iwasawa_of_ringEquiv` → `exists_iwasawa_infinitePlace` → `assemble`/`projV`/`projW` →
   `entry_mem_of_mem_integralSubgroup`/`mul_entry_mem`/`eventually_entries_mem` → `mkUnit` →
   `glFin_mkUnit_mem`/`mkUnit_mem_adelicBorel` → `adelicGL2_ext`/`arch_mul`/`fin_mul` → `solution`.
2. **The 465 row is the set's cost** (44 declarations, 441 lines, a 74-line `RHS_step`): a recursion on
   `k` through the weight `((x-I)/√(1+x²))^k`, with the `k = 0` case the ported special row. Read the
   pin's sections in order and do not try to short-circuit the recursion.
3. **The checked surface is three declarations.** A private helper that is *not* the pin's statement is
   invisible to `check_port` at the pin's visibility. The surface gate (§5.1) is mandatory here, and a
   `MISMATCH` in it is a real defect, not a spelling quibble.
4. **`mkUnit` is not `kOne`, and `base`/`phase`/`Q` are not `botRow`/`logLine`/`HARCHR.q`** (§2.1): the
   port has private copies of *types* that look like these; write the pin's functions.
5. **Binder spelling is the statement** (FR-0123). The seed's headline has four binders and a nested
   `∃`; the 465 row's `(-Complex.I) ^ k` and the 264 row's `if a = b then … else 0` are part of the
   statements. Transcribe the wrappers' text.
6. **The two side conditions are different**: the 465 row needs `0 < s.re` only and its RHS carries
   `Γ_ℝ(2s+1±k)` in the denominator; the 264 row needs `((a:ℝ)+b)/2 + 1 < t.re`. The consumer zone
   (§5.5) checks that the `k = 0` / `a = b = 0` cases reduce to AF14's two values.
7. **No `set_option`**, no `letI` walls in these three files (none of the three statements carries a
   top-level `let`, unlike AF14's rows 1–3), and no `import Mathlib` in a port module.

## 7. What this set does not do

- **It does not take the Weyl pair** — `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half`
  (1,349) and `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`
  (1,291): **2,640 silo, two dispatches, measured return zero** — now the largest ready block on the
  shelf and deferred for the third set in a row. The honest statement is that it is a *transcription* set
  with no readiness return: the column should take it when it wants bulk landed, not when it wants work
  opened.
- **It does not take the flat-section indicator row** — `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow`
  (1,043, 3 premises, 1/3), AF13's own subject, measured return zero.
- **It does not take the eight rows the seed readies** (1,278 silo): they are one subject — *a section is
  determined by, and inherits the regularity of, its restriction to the maximal compact* — and they are
  ready only once order A lands, so they cannot be transcribed before it exists. They are **AF16's
  subject**.
- **It does not take the ninth readied row**, `EisensteinGeneral.Piece.exists_forall_nonempty_factorizationDatum`
  (890): another column's, and not this brief's to cut.
- **It does not finish the `LocalIntertwining` cluster** (19 nodes; 9 are in the port after this set).
  What remains on the shelf is **one ready row and four rows short of it, and two rows that are not this
  column's business at all** — counted from the premise lists on this tree, not from memory:

  | node | silo | state |
  |---|---:|---|
  | `integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1,291 | **ready** (the Weyl pair's half, §7) |
  | `bounded_and_tendsto_integral_moebiusShift_sub_integral_complexAtom` | 206 | one premise short: `MeasureTheory.integral_normSq_det_div_mul_comp_moebius_complex` |
  | `bounded_and_tendsto_integral_moebiusShift_sub_integral_realAtom` | 175 | one premise short: `MeasureTheory.integral_abs_det_div_sq_mul_comp_moebius_real` |
  | `bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion` | 472 | one premise short: `LanglandsTunnell.TateLocal.integral_comp_inv_eq_integral_modulus_inv_sq_mul_adicCompletion` |
  | `integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 70 | two short: the 1,291 row and `NumberField.AdelicBox.inv_measure_adelicBox_mul_integral_pureTensor_eq` |
  | `exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion` | — | **outside the D–S cone** (premises all ported; the target does not demand it) |
  | `exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum` | — | **outside the D–S cone** likewise |

  So the three one-premise-short rows and the two-premise one are **column-boundary work**: they become
  ready when the neighbouring columns land their `MeasureTheory` / `LanglandsTunnell` / `AdelicBox` rows,
  not when this column writes more. The two out-of-cone rows are not shelf business at all.
- **It does not take the `diagOne` family** (2,098 in four rows), still blocked on the unported
  `TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one` and the two `LanglandsTunnell`
  rows.
- **The 4 withheld rows / 831 remain** the prunable complex-analytic subject.
- **No `Def_` node, no promotion, no migration**; two new modules, both cascade-free.

## Appendix A — the shelf, every row accounted for

Generated from `build/shelf-af15-scope.json` by `build/af15-shelf-appendix.py` (silo, premises,
leverage, disposition).

### The ready block — **34 rows / 11,361 silo**

| row | silo | prem | lev | disposition |
|---|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | deferred (§7) |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | deferred (§7) |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | deferred (§7) |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | deferred (§7) |
| `LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` | 465 | 1 | 1/6 | **SET-AF15** |
| `rightTranslate_adjoint_weightedPairing_of_isLsXiFunction` | 433 | 4 | 4/10 | deferred (§7) |
| `hasDerivAt_rightConv_mul_unipotentGL2_and_isFactorizableTestFn_leftDeriv_and_linear` | 390 | 2 | 1/2 | deferred (§7) |
| `exists_mem_adelicBorel_mul_eq` | 372 | 1 | 14/63 | **SET-AF15** |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | deferred (§7) |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | deferred (§7) |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | deferred (§7) |
| `archCasimirAtComplex_rightConv_of_isFactorizableTestFn_of_continuous_archDerivAtComplex` | 321 | 6 | 1/1 | deferred (§7) |
| `isCuspidalFn_isKfSmooth_levelInvariant_isHeckeCosetEigenfunctionAt_rightConv_of_isFactorizableTestFn_of_support_subset` | 290 | 2 | 2/11 | deferred (§7) |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | deferred (§7) |
| `LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` | 264 | 1 | 1/6 | **SET-AF15** |
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

of which **3 rows / 1,101 silo** are this set's.

### The leaves block — **56 rows / 11,461 silo**

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
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 1/2 | deferred (§7) |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 2/3 | deferred (§7) |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 3/4 | deferred (§7) |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 1/1 | deferred (§7) |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 1/1 | deferred (§7) |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 5/10 | deferred (§7) |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 1/1 | deferred (§7) |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 7/20 | deferred (§7) |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 4/5 | deferred (§7) |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 1/1 | deferred (§7) |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 1/4 | deferred (§7) |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 1/1 | deferred (§7) |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 1/1 | deferred (§7) |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 1/5 | deferred (§7) |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 1/1 | deferred (§7) |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 8/19 | deferred (§7) |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 1/2 | deferred (§7) |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 4/8 | deferred (§7) |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 2/2 | deferred (§7) |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 1/14 | deferred (§7) |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 1/3 | deferred (§7) |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 1/1 | deferred (§7) |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 2/3 | deferred (§7) |
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

of which **0 rows / 0 silo** are this set's.

## Appendix B — the per-row worklist

Generated by `build/af-worklist.py`. **The 51 "imported" lines overstate the reuse by all 51** (§2.1).

| row | decl lines | imported | to write | decls |
|---|---:|---:|---:|---:|
| `exists_mem_adelicBorel_mul_eq` | 353 | 39 | 314 | 31 |
| `LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` | 449 | 8 | 441 | 44 |
| `LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` | 245 | 4 | 241 | 16 |
| **3 rows** | **1047** | **51** | **996** | **91** |

### `exists_mem_adelicBorel_mul_eq` (order A)

353 declaration lines, 39 imported, **314 to write** in 31 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `solution` | 61 | 313 | theorem |
| `exists_iwasawa_rclike` | 20 | 81 | theorem |
| `exists_iwasawa_infinitePlace` | 19 | 149 | theorem |
| `eventually_entries_mem_inv` | 19 | 242 | theorem |
| `exists_iwasawa_of_ringEquiv` | 18 | 127 | theorem |
| `isRowIsometry_rotMatN` | 17 | 49 | theorem |
| `bottomRow_normSq_pos` | 15 | 66 | theorem |
| `assemble_mul_assemble` | 10 | 211 | theorem |
| `adelicGL2_ext` | 10 | 293 | theorem |
| `glFin_mkUnit_mem` | 9 | 284 | theorem |
| `eventually_entries_mem` | 8 | 234 | theorem |
| `norm_sq_rot_identity` | 7 | 28 | theorem |
| `rotMatN_det` | 7 | 42 | theorem |
| `adeleMatrix_ext` | 7 | 185 | theorem |
| `assemble` | 7 | 192 | def |
| `entry_mem_of_mem_integralSubgroup` | 7 | 221 | theorem |
| `mkUnit_mem_adelicBorel` | 7 | 277 | theorem |
| `finComponent_glFin_eq` | 6 | 179 | theorem |
| `projW_assemble` | 6 | 199 | theorem |
| `projV_assemble` | 6 | 205 | theorem |
| `mul_entry_mem` | 6 | 228 | theorem |
| `rotMat_det` | 5 | 23 | theorem |
| `glEquivOfRingEquiv_symm_apply` | 5 | 122 | theorem |
| `archComponent_glArch_eq` | 5 | 174 | theorem |
| `arch_mul` | 5 | 303 | theorem |
| `fin_mul` | 5 | 308 | theorem |
| `rotMatN_apply` | 4 | 38 | theorem |
| `arch_mkUnit` | 4 | 269 | theorem |
| `fin_mkUnit` | 4 | 273 | theorem |
| `rotMatN` | 3 | 35 | def |
| `rotMat` | 2 | 21 | def |

### `LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (order B)

449 declaration lines, 8 imported, **441 to write** in 44 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `RHS_step` | 74 | 324 | theorem |
| `hasDerivAt_phase` | 33 | 195 | theorem |
| `recursion_raw` | 24 | 274 | theorem |
| `hasDerivAt_G` | 22 | 252 | theorem |
| `closed_form_nat` | 21 | 398 | theorem |
| `hasDerivAt_Q` | 14 | 238 | theorem |
| `recursion` | 14 | 298 | theorem |
| `RHS_neg` | 14 | 429 | theorem |
| `tendsto_phase_zpow_mul_Q_atBot` | 13 | 182 | theorem |
| `integrable_phase_zpow_mul_Q` | 12 | 159 | theorem |
| `closed_form_zero` | 12 | 312 | theorem |
| `tendsto_phase_zpow_mul_Q_atTop` | 11 | 171 | theorem |
| `main` | 11 | 448 | theorem |
| `phase_mul_phase_neg` | 10 | 118 | theorem |
| `hasDerivAt_phase_zpow` | 10 | 228 | theorem |
| `J_neg` | 10 | 419 | theorem |
| `norm_sub_I` | 9 | 66 | theorem |
| `continuous_Q` | 9 | 146 | theorem |
| `solution` | 8 | 459 | theorem |
| `radC_eq_base_cpow_half` | 7 | 100 | theorem |
| `phase_neg` | 7 | 128 | theorem |
| `continuous_phase` | 7 | 139 | theorem |
| `radC_sq'` | 6 | 44 | theorem |
| `Q_div_base` | 6 | 89 | theorem |
| `rad_mul_Q` | 6 | 107 | theorem |
| `sub_I_ne_zero` | 5 | 58 | theorem |
| `norm_phase` | 5 | 75 | theorem |
| `norm_Q` | 5 | 80 | theorem |
| `base_cpow_neg_sub_one` | 5 | 95 | theorem |
| `ofReal_eq_rad_mul_phase_add_I` | 5 | 113 | theorem |
| `closed_form` | 5 | 443 | theorem |
| `radC_sq` | 4 | 40 | theorem |
| `base_ne_zero` | 4 | 50 | theorem |
| `base_mem_slitPlane` | 4 | 54 | theorem |
| `norm_phase_zpow_mul_Q` | 4 | 85 | theorem |
| `Q_neg` | 4 | 135 | theorem |
| `continuous_phase_zpow_mul_Q` | 4 | 155 | theorem |
| `RHS` | 3 | 28 | def |
| `radC_ne_zero` | 3 | 37 | theorem |
| `phase_ne_zero` | 3 | 63 | theorem |
| `J` | 2 | 26 | def |
| `one_add_sq_pos` | 2 | 31 | theorem |
| `rad_pos` | 2 | 33 | theorem |
| `rad_sq` | 2 | 35 | theorem |

### `LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg` (order B)

245 declaration lines, 4 imported, **241 to write** in 16 declarations.

| declaration | lines | pin line | kind |
|---|---:|---|---|
| `closed_form` | 66 | 179 | theorem |
| `integral_eq_zero_of_ne` | 37 | 73 | theorem |
| `angular_eq_zero` | 26 | 47 | theorem |
| `integrable_moment` | 20 | 119 | theorem |
| `moment_succ_pointwise` | 15 | 139 | theorem |
| `moment_zero` | 15 | 164 | theorem |
| `main` | 14 | 245 | theorem |
| `moment_succ` | 10 | 154 | theorem |
| `continuous_W` | 7 | 30 | theorem |
| `solution` | 7 | 259 | theorem |
| `norm_moment` | 6 | 110 | theorem |
| `norm_W` | 5 | 37 | theorem |
| `conj_ofReal_mul_exp` | 5 | 42 | theorem |
| `baseC_ne_zero` | 3 | 27 | theorem |
| `continuous_moment` | 3 | 116 | theorem |
| `one_add_norm_sq_pos` | 2 | 25 | theorem |

## Appendix C — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af15-scope.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes AutomorphicForm.exists_mem_adelicBorel_mul_eq \
  --nodes AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  --nodes AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg \
  --json build/af15-advise.json
python3 port_plan.py --json build/af15-advise.json     # 1,101 raw / 1,044 decl / 25 in port / 1,006 net
python3 build/af-worklist.py exists_mem_adelicBorel_mul_eq \
  LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg
python3 build/af14-forecast.py \
  AutomorphicForm.exists_mem_adelicBorel_mul_eq \
  AutomorphicForm.LocalIntertwining.integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  AutomorphicForm.LocalIntertwining.integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg   # the §0.3 forecast
python3 build/af15-shelf-appendix.py                                                         # Appendix A
python3 build/af15-imported.py exists_mem_adelicBorel_mul_eq \
  LocalIntertwining_integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal \
  LocalIntertwining_integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg   # §2.1: the 11 "imported" declarations
cd ../../lean
ROWS="Theorems/Thm_AutomorphicForm_exists_mem_adelicBorel_mul_eq.lean"
for pin in Def_AutomorphicForm_BorelSubgroup Def_AutomorphicForm_RowIsometryInvariance Def_NumberField_AdelicLevel; do
  python3 spec/gate_scan.py --pin Definitions/$pin.lean --rows $ROWS
done
python3 spec/gate_scan.py --pin Definitions/Def_AutomorphicForm_ArchWeightCharTransport.lean \
  --rows $HOME/proj/fermats-last-theorem/P2M/Sol/S_AutomorphicForm_exists_mem_adelicBorel_mul_eq.lean
```

`--rows` takes a **list** in one flag; repeating it silently keeps only the last (AF13's finding, re-hit
twice since). The gate's reading is in §3.

**Forecast on landing** (§0.3): `needed` **853 / 348,710 → 850 / 347,609**, literal
**866 / 352,185 → 863 / 351,084**, frontier **1,562 / 778,656 → 1,565 / 779,757**, ready
**63 / 16,705 → 69 / 17,772**, leaves untouched, and **nine rows readied / 2,168 silo**. The re-read must
confirm every figure, and must check the short rows of §7's table by their premises rather than by this
note.
