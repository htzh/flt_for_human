# SET-AF20 — the rational unipotent Haar measures: the discreteness lemma and the four quotient headlines

**Status: LANDED 2026-11-07** — the definition layer, the scaffolding, and all three orders; §5.1
records the landing and the re-read (exact against §9's forecast, with one accounting correction:
four of the five rows were never on the shelf — they are one edge behind the leaf, §1.0). Read
off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the tree
SET-AF19 left. It is the **twentieth** `AutomorphicForm`-serving set and it is the block
`SET-AF4 §9` measured, `SET-AF5 §7` call 7 deferred to "SET-AF6", and AF6–AF19 then all walked past:
**the rational centre-unipotent and torus-unipotent subgroups of `GL₂(𝔸_K)`, their Haar measures
and their closedness.** The deferral reason was always the same — the block's own read had to price
the `RationalCentreUnipotentQuotient` definition gate — and this read prices it: four pin `Def_`
role modules, 19 declarations, **no proof at all**, now landed (§4).

The set is **5 rows / 1,154 silo / 990 net new math lines in 95 declarations**, one story, three
orders. The leaf is the whole point: **123 silo buys 2,113** — it is the cheapest high-return row on
the AF shelf (§1).

| order | rows | silo | work | home |
|---|---:|---:|---:|---|
| **A** — the diagonal image of `K` in `𝔸_K` meets compacts finitely | 1 | 123 | 106 | new `NumberTheory/AdelicDiscreteness.lean` |
| **B** — the two closedness headlines | 2 | 308 | 251 | new `AutomorphicForm/Adelic/RationalUnipotentClosed.lean` |
| **C** — the two Haar/-invariance headlines | 2 | 723 | 633 | new `AutomorphicForm/Adelic/RationalUnipotentHaar.lean` |
| | **5** | **1,154** | **990** | three new modules, no insertion, no legacy module |

The work orders are `lean/tmp/WORKORDER-AF20A-adele-discreteness.md`,
`…-AF20B-rational-unipotent-closed.md` and `…-AF20C-rational-unipotent-haar.md` (tmp is not
published).

## 0. The read

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af20.json
python3 frontier.py --selfcheck
```

**No `--unport` correction**: AF18 repaired the last three false ported markers and AF19 confirmed
the shelf needs none. `--selfcheck` **PASS** (1,417 `Thm_` sources, 1,598 names).

| figure | value |
|---|---:|
| `needed [F terminal]` | **818 / 341,853** |
| `needed [literal]` | 830 / 345,318 |
| frontier F | 1,598 / 785,523 |
| ready rows, all namespaces | **60 / 19,250** |
| leaves, all namespaces | 225 / 57,500 |
| ready rows, `AutomorphicForm` | **32 / 13,111** |
| leaves, `AutomorphicForm` | **56 / 11,461** |
| withheld by the FR-0044 guard | 4 / 831 |
| avoided by `--ds` (the prunable set R) | 140 / 74,620 |
| cone | 2,103 / 982,173 |

These are the figures SET-AF19 §5.1 closed on, exactly: nothing has landed since, so this read is
also the baseline the set's own landing will be measured against (§9).

**The two blocks, quoted whole.** Appendix A tabulates all **32** AF ready rows (13,111 silo) and
Appendix B all **56** AF leaf rows (11,461) plus the one `NumberField` leaf this set takes; every
row carries its return and a disposition, and every row not taken is deferred here, by name. That
is the recipe's FR-0040 accounting and it is the reason the cut below can be trusted.

**One correction to the ordinary reading of that accounting, and it is the set's shape.** Only
**one** of the five rows this set takes is on the shelf: the `NumberField` leaf. The other four —
the two `isClosed` and the two `isHaarMeasure` rows — are each **one edge behind it** (`needed = 2`,
their only unported premise being the leaf), so they appear in neither block: they are the rows in
§1's gateway table, and the set is the recipe's SET-10 shape ("the pair plus the capstone one edge
behind them"), at four times the size. That is why the re-read below shows the ready shelf gaining
rows rather than losing five.

## 1. Why this block — return, not silo

The recipe's §1 signal: *"Demand is inverted relative to size on this shelf … the leaves are also
the cheapest declarations in the set."* Measured over the current shelf (return = the silo of the
in-cone rows whose **every** unported premise is the row itself, so landing it readies them):

| candidate | silo | return | what it opens |
|---|---:|---:|---|
| **`finite_setOf_algebraMap_mem_of_isCompact` (leaf)** | **123** | **2,113** | **this set**: 446 + 277 + 174 + 134, then 635 + 447 |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` (leaf) | 70 | 1,445 | 1,175 + 190 + 80, the arch-approximation block |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` (leaf) | 71 | 1,361 | the `SmoothCuspRealizationAt` chain |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` (leaf) | 98 | 1,131 | `exists_rightConv_eq_of_archCutProjector` |
| `su2Derivs_stable_…` (leaf) | 755 | 1,077 | 908 + 169, the circle-weight string |
| `CuspidalSpectrum.exists_isLift_rightConv` (ready) | 199 | 215 | the lift algebra (2 rows now, 1,179 one edge away) |
| the four `diagOne` rows (ready) | 3,248 | **0** | nothing: each consumer needs 2–6 more rows |

Two readings decide the cut, and both are measurements rather than preferences.

- **The `diagOne` family is not AF20's subject.** SET-AF19 §8 named it ("4 rows / 3,248 silo"),
  chosen on silo. Its measured return is **zero** — the pin's four rows feed consumers
  (`exists_forall_whittakerCoefficient_diagOne_eq_mul_of_isComplex_of_su2String` 473,
  `CuspidalConstituent.exists_norm_whittakerCoefficient_diagOne_mul_le_…` 427/440,
  `RankinSelberg.exists_testData_sPartIntegral_self_analyticOnNhd_re_pos` 1,441) that each still
  need two to six further rows of 300–1,400 silo. It is a **transcription** block: 3,248 silo of
  work that readies nothing, and the column's largest single unblocking row (1,175) is not behind
  it. It stays deferred (§10), with the number recorded.
- **This block's leaf is the best buy on the shelf** (2,113 for 123, and its return is a *story*:
  the four rows it readies are one subject). It is also the only candidate whose landing pays for a
  **definition subtree** rather than a single row: `Def_HaarQuotient` and the three quotient modules
  are unported, and the `HaarQuotient` namespace has 7 in-cone nodes / 2,245 silo behind them.

## 2. The rows

| order | row | silo | work | decls | prem | lev | what it states |
|---|---|---:|---:|---:|---:|---:|---|
| A | `NumberField.AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` | 123 | 106 | 7 | 0 | 14/41 | for compact `C ⊆ 𝔸_K`, `{ξ : K ∣ ξ ∈ C}` is finite |
| B | `isClosed_rationalCentreUnipotent` | 134 | 118 | 9 | 1 | 1/1 | `Z(𝔸)·Kˣ·U(𝔸)` is closed in `GL₂(𝔸)` |
| B | `isClosed_rationalTorusUnipotent` | 174 | 152 | 11 | 1 | 1/1 | `Z(𝔸)·T(K)·U(𝔸)` is closed |
| C | `isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant` | 277 | 186 | 24 | 1 | 1/1 | the centre-unipotent measure is Haar and right-invariant |
| C | `isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant` | 446 | 335 | 44 | 1 | 1/1 | … the same for the torus-unipotent measure |
| | **5** | **1,154** | **990** | **95** | | | |

**The premise audit, by hand.** The five rows have exactly **one** graph premise each and it is the
same one, the leaf of order A; every other import of the four `S_` files is a `Def_` module (the
§4 gate) or an already-ported declaration:

| import of the `S_` files | port home |
|---|---|
| `Theorems/Thm_NumberField_AdeleRing_finite_setOf_algebraMap_mem_of_isCompact` | **order A** (scaffolded, statement `ok`) |
| `Definitions/Def_AutomorphicForm_Rational{Torus,Centre}UnipotentQuotient` | `Adelic/UnipotentQuotient.lean` (§4, landed) |
| `Definitions/Def_AutomorphicForm_BorelSubgroup` | `Adelic/BorelSubgroup.lean` (0 declarations used, `gate_scan`) |
| `Definitions/Def_NumberField_AdelicBox` | `NumberTheory/AdelicBox.lean` |
| `NumberField.AdeleRing.distribHaarChar_algebraMap` (not used by these rows; used by the `HaarQuotient` layer's siblings) | `NumberTheory/AdelicModulus.lean` |
| `AutomorphicForm.continuous_unipotentGL2` (the pin's 12-line copy in both C files) | `Adelic/ConstantTerm.lean` — the **general** statement (SET-AF5's promotion), imported |

**`twin_scan` on the five, before the scaffolding: `new` five times** — no statement twin in the
port, so the FR-0041 check (a port theorem with weaker hypotheses to rebuild on) passes by
inspection. Re-run after the scaffolding it reports `TWIN-public` against the skeletons themselves,
which is what a frozen statement is for; the prelude columns (`0/24` for the centre Haar row, `1/43`
for the torus one) confirm the pricing: almost nothing of these files is already in the port.

## 3. The price

`port_advise` / `port_plan` over the five rows:

```
raw S_ lines (47-node slice)          1154
  declaration lines                   1046
    duplicate copies                    56   (removable by porting once)
    boilerplate (imports/attrs/p2m)    108
  distinct declaration groups           88
    already in the port (vetted)         0
  NET NEW MATH LINES                   990
```

- **substitute**: `continuous_unipotentGL2` (12 lines in each C file) → the port's general
  `AutomorphicForm.continuous_unipotentGL2` in `Adelic/ConstantTerm.lean`. Nothing else: every
  other declaration of the slice is new (0 already in the port).
- **port once**: six names, 57 lines —
  `isClosed_range_algebraMap_adeleRing` (19, both B files: **written once, public, in
  `RationalUnipotentClosed.lean`**, and the module carries both files' wires),
  `ratCentralHom` (3), `ratCentralHom_apply_entry` (7), `ratCentralHom_comm` (13) and
  `continuous_toAdelicUnipotent` (3) (both C files: written once in `RationalUnipotentHaar.lean`).
- **generalise**: six same-name/different-statement pairs, all *within* the set and all the pin's
  own `K`/`F` binder variants (`isUnit_of_forall_ne_zero`, `piInv`, `ringInverse_eq`,
  `mul_centralScalar_comm`, `archIdele`, …) — none of them is a declaration of the five rows. The
  one that matters is `archIdele` (a `private` helper of `TateGlobal/IdeleNormValues.lean`, SET-AF19
  order C): **not needed here**.
- **drags**: no row has a private prelude beyond the two port-once blocks; both `isClosed` files are
  a flat public surface, and the two `isHaarMeasure` files are one 26-line prelude each.

## 4. Ground prep — the definition layer (landed, the manager's)

Four pin role modules were in the five wrappers' closure and **none was ported**
(`rg "unipotentHaar|HaarQuotient" FLTForHuman/` was empty before this set). The gate is
declaration-level and it is all definitions:

| pin module | declarations | port home |
|---|---:|---|
| `Definitions/Def_HaarQuotient.lean` (35 lines) | 3 | new `MeasureTheory/HaarQuotient.lean` |
| `Definitions/Def_AutomorphicForm_UnipotentQuotient.lean` | 5 | new `AutomorphicForm/Adelic/UnipotentQuotient.lean` |
| `Definitions/Def_AutomorphicForm_RationalCentreUnipotentQuotient.lean` | 5 | same module |
| `Definitions/Def_AutomorphicForm_RationalTorusUnipotentQuotient.lean` | 6 | same module |

Landed and checker-green: `HaarQuotient.lean` **3 ok**, `UnipotentQuotient.lean` **16 ok**, both
`0 mismatch / 0 missing / 0 own`, both silent, both built. The three `Def_` modules are one module
because the pin chains them by import and they are one subject (the unipotent radical and its
rational centre-/torus-enlargements), and `HaarQuotient` is separate because it is a **mathlib
supplement** (generic measure theory over an arbitrary group, mathlib has only the
fundamental-domain quotient measure — the negative is in the header).

The three proof modules' **scaffolding** is also landed: headers, imports, wires, and the five
headlines stated verbatim from their wrappers with `sorry` bodies, so each worker's statements are
frozen before it starts:

| module | statements | checker now |
|---|---|---:|
| `NumberTheory/AdelicDiscreteness.lean` | the leaf | **1 ok** |
| `AutomorphicForm/Adelic/RationalUnipotentClosed.lean` | the two `isClosed` rows + the shared engine (proved) | **3 ok** |
| `AutomorphicForm/Adelic/RationalUnipotentHaar.lean` | the two `isHaarMeasure` rows | **2 ok** |

### 4.1 The landing of orders A and B

| order | module (Δ source lines) | decls | checker | build | axioms |
|---|---|---:|---|---|---|
| A | `NumberTheory/AdelicDiscreteness.lean` 44 → **153** (+109) | 7 | **7 ok** / 0 / 0 / 0 own | silent, 3.3 s | clean |
| B | `AutomorphicForm/Adelic/RationalUnipotentClosed.lean` 79 → **308** (+229) | 17 | **17 ok** / 0 / 0 / 0 own | silent, 5.1 s | clean |

`dedup --within` / `move_dead --dry-run`: **1 cluster / 0 dead** (A), **0 / 0** (B). Consumers
`spec/AdelicDiscretenessConsumer.lean` and `spec/AutomorphicFormSetAF20BConsumer.lean`: **0 errors,
0 warnings**, no `#check`s.

**A's one `dedup` cluster stays, and this is why.** `finite_setOf_algebraMap_mem_of_isCompact_impl`
(`S_:96`) and the headline (`Thm_:6`) are *byte-identical pin statements* — the pin's generated
`solution` delegates through the former. Dropping either would drop a pin declaration from the
checked surface; the cluster is the pin's own wrapper-over-engine pattern and the recipe's
`shape`-tier rule ("the pin's own pattern: keep it, record the reason"). The engine
`finite_setOf_algebraMap_mem` is a third copy under a different spelling (`𝓞 F`), so the tool does
not see it.

**A's drift (4 spots, instance plumbing only; the three-move route transcribed unchanged).** v4.34
does not synthesise `DiscreteTopology ↥(mixedEmbedding.integerLattice F).toAddSubgroup` nor the
`Submodule` coercion (only `↥L` itself), so the pin's `haveI` + `DiscreteTopology.isDiscrete` is
replaced by `isDiscrete_iff_discreteTopology.mpr (inferInstanceAs …)` passed explicitly to
`Metric.finite_isBounded_inter_isClosed`; `AddSubgroup.isClosed_of_discrete` is *deprecated* on
v4.34 (warns) and is `AddSubgroup.isClosed_of_isDiscrete`; `isOpen_integralFiniteAdeles` exists in
**two** port namespaces and needs the `NumberField.AdelicBox` qualification; `Set.setOf_true` is
`Set.ofPred_true`. No `set_option` was added, so the `AdelicBox.lean` escape is not available here.

**B's drift (7 items, all measured).** `Set.setOf_and` → `Set.ofPred_and`; a no-op `change` dropped
(`linter.unusedTactic`); `haveI : Nontrivial …` → `have …` (`linter.style.haveILetI` — `have` still
registers the local instance, so no global instance is added); the pin's pipeline scaffolding
(`p2m_open`/`p2m_export`, the `TKNClosed` label, the trailing `solution` theorems) dropped; and one
structural decision: the pin's two primed helpers `isClosed_rational{,Torus}Unipotent'` have exactly
the wrappers' statements, so each **folds into its headline** (the checker maps each headline onto
the primed pin name), which is why the module has 17 declarations against the pin slice's 19.

**The one landing item the checker cannot resolve by itself**: the pin writes eight of C's
declarations as `scoped instance`, and `spec/statement_db.py` indexes no statement for an
`instance`, so the port's public `theorem` spelling is `MISSING` with nothing to diff against. The
manager writes the eight `own:` rows in `spec/decl_markers.tsv` (tier 2): the pin's `scoped
instance` spelling is not carried because the port does not use `scoped instance`s
(work order §4 trap 1), and the port states the same propositions as public theorems.

### 4.2 Order C, and the whole set's gates

`AutomorphicForm/Adelic/RationalUnipotentHaar.lean` 69 → **799** lines, **70 declarations** — 5 of the
shared prelude, 21 in `AutomorphicForm.CentreUnipotent`, 42 in `AutomorphicForm.TorusUnipotent`, and
the two frozen headlines. The pin's two files share 19 last names with **different** statements
(`sheet`, `chart`, `exists_eq`, `isHaarMeasure`, …), and a rename is not available (a statement
mentioning a renamed helper cannot hash-match), so the two families keep the pin's last names in two
sub-namespaces — that is what the checker reads as `2 ok / 0 ambiguity`.

| order | module (skeleton → landed) | decls | checker | build | axioms |
|---|---|---:|---|---|---|
| A | `NumberTheory/AdelicDiscreteness.lean` 44 → **153** | 7 | **7 ok** / 0 / 0 / 0 own | silent, 3.3 s | clean |
| B | `…/RationalUnipotentClosed.lean` 79 → **308** | 17 | **17 ok** / 0 / 0 / 0 own | silent, 5.1 s | clean |
| C | `…/RationalUnipotentHaar.lean` 69 → **799** | 70 | **62 ok** / 0 / 0 / **8 own** | silent, 5.9 s | clean |
| | plus the definition layer | 19 | **3 ok** + **16 ok** | silent | — |

**All five headlines** are on `[propext, Classical.choice, Quot.sound]` (one `#print axioms` block
over the three modules, `lean/tmp/ax_af20.lean`) — no `sorryAx` anywhere.

`dedup --within` / `move_dead --dry-run`: **1 cluster / 0 dead** (A — the `_impl` ≡ headline pair of
§4.1, kept), **0 / 0** (B), **0 / 0** (C). Three consumer zones — `spec/AdelicDiscretenessConsumer.lean`,
`spec/AutomorphicFormSetAF20BConsumer.lean`, `spec/AutomorphicFormSetAF20CConsumer.lean` — elaborate
with **0 errors, 0 warnings**, no `#check`, no `sorry`.

**The eight `own:` rows** are in `spec/decl_markers.tsv` with the reason (the pin's `scoped
instance` spelling has no corpus row; the port states the same propositions as public theorems and
carries no `scoped instance`s), which is what turns C's `8 missing` into `8 own` and the module's
gate into `62 ok / 0 mismatch / 0 missing / 8 own`.

**C's deviations (measured).** `continuous_unipotentGL2` imported rather than restated (the order's
one expected substitution, 11 lines ×2); `map_mul_left_principal_adelicAddHaar` (pin `:182`) proved
in **one line** from the port's landed `NumberField.AdelicHaar.measurePreserving_mul_algebraMap_adelicAddHaar`
+ `.map_eq` instead of the pin's 14-line `distribHaarChar` route — an *unplanned* second substitution,
and the module's one new import (`NumberTheory/AdelicModulus`); `Measure.map_smul` now takes
`AEMeasurable` (5 sites); `haveI` → `have` at every Prop-valued instance (10 sites, and it is what
makes `IsHaarMeasure` assemble with `⟨⟩` and leave nothing behind); `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq`.

**The one structural question the order asked** — is the `Kˣ × Kˣ` file the `Kˣ` file under a
substitution? — is answered no, in exactly three places, and it is worth carrying: the measure
algebra half transcribes literally, but (i) the diagonal does *not* commute with the unipotent, it
rescales the coordinate (`u_y · diag a = diag a · u_{a⁻¹y}`), which is the sole reason `scaleN`
exists; (ii) right invariance in the `Kˣ` file is **just commutativity**, and `rationalTorusUnipotent`
is not commutative (`T(K)` is not central in `GL₂`), so the torus file needs the genuinely new ~60-line
block `map_mul_left_principal_adelicAddHaar` → `map_scaleN_unipotentHaar` → `map_mul_right_unipotentHaar`
→ `map_mul_right_torus` → `map_mul_right_unipotent`; (iii) finiteness on compacts needs a *second*
matrix entry, because the index is two-dimensional and is recovered by `p ↦ (p.2, p.2⁻¹ * p.1)`.

### 4.3 The re-read (exact against §9)

```bash
cd tools/deps && python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf11-post.json
python3 frontier.py --selfcheck     # PASS (1,422 Thm_ sources, 1,603 names)
```

| figure | before | after | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 818 / 341,853 | **813 / 340,699** | 813 / 340,699 ✓ |
| `needed [literal]` | 830 / 345,318 | **825 / 344,164** | 825 / 344,164 ✓ |
| frontier F | 1,598 / 785,523 | **1,603 / 786,677** | 1,603 / 786,677 ✓ |
| ready rows | 60 / 19,250 | **62 / 20,332** | 0 out, 2 in ✓ |
| leaves | 225 / 57,500 | **224 / 57,377** | 1 out ✓ |
| `AutomorphicForm` ready | 32 / 13,111 | **34 / 14,193** | +2 ✓ |
| `AutomorphicForm` leaves | 56 / 11,461 | **56 / 11,461** | — ✓ |
| `AutomorphicForm` demand | 322 / 140,337 | **318 / 139,306** | −4 / −1,031 ✓ |
| withheld (FR-0044) | 4 / 831 | 4 / 831 | — ✓ |

**The two rows readied are the two forecast**, and no row left the ready shelf — the four AF rows the
set ported were never on it (§1.0). The set consumed **5 rows / 1,154 silo**, and wrote **1,068
source lines / 94 declarations** in three new modules plus the 19-declaration definition layer.

**What the landing leaves as AF21**: the box-sheet pair + the quotient identity, priced while the
orders ran — **3 rows / 1,146 silo / 931 net in 78 declaration groups**, 71 lines of which are
already in the port *because* this set's module supplies them (`ratCentralHom`, `ratCentralHom_comm`,
`sheet`, `sheet_entries`, `continuous_toAdelicUnipotent`, `CentreUnipotent.exists_eq`), i.e. a
composition set on top of this one, with one promotion falling out of the scan
(`countable_numberField`, 4 lines, `private` in `Adelic/RightTranslateAdjoint.lean`).

## 5. Homes, and the import direction

Nothing is legacy: all three proof modules are new, 0-importer, cascade-free. The import direction
is the constraint, and it is satisfied by construction:

```
AutomorphicForm/Adelic/UnipotentQuotient.lean   (the Def_ layer)
        ▲                        ▲
        │                        │
RationalUnipotentClosed     RationalUnipotentHaar        (orders B and C: disjoint, neither imports the other)
        ▲                        ▲
        └────── NumberTheory/AdelicDiscreteness.lean ────┘   (order A: the leaf)
```

- the leaf's home is a module **above** `NumberTheory/AdelicBox.lean` (whose `integralFiniteAdeles`,
  `isOpen_integralFiniteAdeles` and `mixedEmbedding`-side API the proof consumes) rather than an
  insertion into it, because the box is a hub with many in-tree importers and the subject is one
  self-contained statement;
- the closedness and the Haar-ness rows are **two subjects** (a topological statement about a
  subgroup, a measure-theoretic statement about a measure on it) and they do not import each other,
  which is what lets B and C run concurrently;
- `NumberTheory` never imports `AutomorphicForm` (the rule SET-AF19 order C ran into), and it does
  not have to: the leaf lives on the `NumberTheory` side and the two consumers (B and C) import it.

## 6. The cut

**5 rows / 1,154 silo / 990 net, three orders, three new modules, disjoint files.** One dispatch.

| order | rows | work order | module | writes |
|---|---|---|---:|---|
| A | 1 | `WORKORDER-AF20A-adele-discreteness.md` | 106 | the 70-line engine, 6 helpers |
| B | 2 | `WORKORDER-AF20B-rational-unipotent-closed.md` | 251 | 19 declarations (2 sets of 8 helpers + 1 engine, shared) |
| C | 2 | `WORKORDER-AF20C-rational-unipotent-haar.md` | 633 | ~66 declarations (two sheets over `Kˣ` / `Kˣ × Kˣ`) |

The three modules touch no file another order writes, and no existing module at all. Only the build
lock is shared.

**Why three orders and not one.** B and C are different subjects and their pin files share exactly
one 19-line engine; the module split keeps the checked surface of each equal to its two pin files.
The leaf (A) is `NumberTheory` and is a premise of both, so it is its own order — and it is the
one that reads as a graph leaf, which is why the recipe's `--include-leaves` matters here.

## 7. Traps, per order

**A (the leaf, pin `S_…:26`).** The pin's proof is one 70-line argument in three moves:
(i) `elim_nhds_subcover` over the compact finite half with the open subgroup `∫_fin` of integral
finite adèles (the cover is built from `(fun z => z - y) ⁻¹' ∫_fin`, not from a ball);
(ii) the infinite half: two points of the same coset differ by an element of the **integer lattice**
`mixedEmbedding.integerLattice` under `InfiniteAdeleRing.ringEquiv_mixedSpace`, and
`Metric.finite_isBounded_inter_isClosed` at the lattice's `DiscreteTopology` bounds the differences
(`AddSubgroup.isClosed_of_discrete` for closedness);
(iii) `HeightOneSpectrum.mem_integers_of_valuation_le_one` turns "all valuations `≤ 1`" into lattice
membership. The pin's `M4aP3B.Rows.DiscreteAdele` namespace and the `gate_empty` /
`gate_univ_infinite` test lemmas are the pin's own scaffolding: keep the two gate lemmas (they are
public pin declarations) but in the module's own namespace, drop the pipeline label.

**B (the two closedness rows).** The shared engine `isClosed_range_algebraMap_adeleRing` is already
proved in the skeleton; do not re-prove or restate it. Each row is: define the entry-wise set
(`scalarUnipotentSet` / `torusUnipotentSet`) as a set of **matrices**, prove it closed from
continuity of the entries plus `isClosed_range_algebraMap_adeleRing`, prove it closed under
multiplication, prove the two generators land in it, then `Subgroup.closure_induction` for one
inclusion and an explicit matrix decomposition (`g = diag(ξ) * unipotentGL2 (ξ⁻¹ * g₀₁)` for the
centre row; the two-entry version for the torus row) for the other. The pin's `Nontrivial (AdeleRing
…)` instance comes from `algebraMap_injective` — do not add it to the module header.

**C (the two Haar rows).** One argument, two indices (`Kˣ` and `Kˣ × Kˣ`). The pin's shape is worth
following exactly: `sheet` and `chart` (the chart is the sheet composed with the unipotent
coordinate), `exists_leftInverse_chart` (the left inverse is `ξ⁻¹ * (·)₀₁`), `measure_sheet_preimage`
(which reads the sheet's image measure off the additive Haar measure of the chart), then **left
invariance on the two generators** (`map_mul_left_ratCentral` by reindexing the sum with
`Measure.sum_comp_equiv` at `Equiv.mulLeft`, `map_mul_left_unipotent` by `map_add_left_eq_self` of
the additive Haar measure), **right invariance from commutativity** of the subgroup, and finiteness
on compacts / positivity on open sets by the chart, with the finite index set supplied by
`finite_setOf_algebraMap_mem_of_isCompact` at the compact set of `(0,0)`-entries. The pin's five
`scoped instance` declarations must be written as **public theorems** (the same statements) with
`attribute [local instance]` where the `IsHaarMeasure` assembly needs them — the port does not
carry `scoped instance`s.

## 8. The gates, per order

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**; every declaration the
   pin states publicly is `ok` at the pin's name (the surface gate of the recipe §5 — the module's
   helper declarations **are** the pin's, so they stay public; do not leave them `private`).
2. `#print axioms` on each headline → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout`, silent, zero warnings; no tree build, no
   dependents.
4. `dedup.py --within` on the module: report clusters (expect none within a module; the cross-module
   preludes are already written once) and `move_dead.py --dry-run`: expect 0 dead (every helper has
   the headline as a consumer).
5. No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option maxHeartbeats`, no bare
   `import Mathlib`.
6. A `spec/` consumer zone per order with a real composition (no `#check`s); its error count is the
   deliverable metric.

## 9. What the set consumes, and the forecast

**Consumes**: 5 rows / 1,154 silo; **990 net new math lines** in 95 declarations, plus the 19
declarations of the definition layer; three new modules, ten wire lines.

**The forecast, and the re-read (§5.1 measured it exact to the line):**

| figure | before | forecast | measured after |
|---|---:|---:|---:|
| `needed [F terminal]` | 818 / 341,853 | 813 / 340,699 | **813 / 340,699** ✓ |
| `needed [literal]` | 830 / 345,318 | 825 / 344,164 | **825 / 344,164** ✓ |
| frontier F | 1,598 / 785,523 | 1,603 / 786,677 | **1,603 / 786,677** ✓ |
| ready rows | 60 / 19,250 | 0 out, 2 in | **62 / 20,332** (+2 / +1,082) |
| leaves | 225 / 57,500 | 1 out (the leaf) | **224 / 57,377** (−1 / −123) |
| `AutomorphicForm` demand | 322 / 140,337 | −4 / −1,031 | **318 / 139,306** ✓ |

**Rows this set readies** (measured, §1, and the read confirms it): `integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`
(635) and `exists_forall_setLIntegral_nnnorm_sq_le_mul_setLIntegral_of_isLsXiFunction_of_isCompact_of_isFundamentalDomain`
(447) — 1,082 silo, two different subjects, and they are AF21's or AF22's business, not this set's. The block's
own continuation is the **box-sheet fundamental-domain pair**,
`isFundamentalDomain_boxSheet_rationalTorusUnipotent` (440) and
`…_rationalCentreUnipotent` (340): they are the two leaves the quotient identity
`integral_rationalTorusUnipotentQuotient_tsum_units_eq_integral_rationalCentreUnipotentQuotient`
(366) still needs, and landing them readies it (plus, with `HaarQuotient.setLIntegral_…` 302, the
`HaarQuotient` layer). That pair + the quotient identity is the natural **AF21**; it is 780 silo of
work and it is the headline of the story this set opens.

## 10. What this set does not do

- **The `diagOne` family** (913 + 905 + 716 + 714 = 3,248): SET-AF19 §8 named it AF20's subject.
  This read measures its return at **zero** and defers it by name (§1); the arch-approximation
  block (`exists_isRightEquivariant_comp_subtype_eq_of_injective` 70 → 1,445) and the test-function
  algebra (`isFactorizableTestFn_sum_mul_comp_mul_mul` 98 → 1,131) are the better cuts when the
  column wants the largest readiness event.
- **The box-sheet pair and the quotient identity** (440 + 340 + 366): AF21, above.
- **The six `HaarQuotient` nodes** (2,245 silo): they need the quotient-measure API this set's
  `HaarQuotient` module now supplies, but their own statements are a separate subject
  (`setLIntegral`/`lintegral` composition), deferred.
- **The 4 withheld rows / 831** remain the prunable complex-analytic subject.
- **No insertion into an existing module, no legacy migration, no promotion, no tree build.**

## Appendix A — the AF ready shelf, every row

Return = silo of the in-cone rows this row would ready on its own landing.

### READY — 32 rows / 13,111 silo

| row (`AutomorphicForm.` / `NumberField.` dropped) | silo | prem | lev | return | disposition |
|---|---:|---:|---:|---:|---|
| `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` | 1349 | 1 | 1/1 | 0 | deferred |
| `LocalIntertwining.integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` | 1291 | 2 | 1/1 | 0 | deferred |
| `isInducedSection_indicator_bottomRow_mul_adelicHeight_cpow` | 1043 | 3 | 1/3 | 0 | deferred |
| `exists_whittakerCoefficient_diagOne_eq_mul_whittakerCoefficient_splitTorusGL2Complex_of_hasCircleWeightAt` | 913 | 1 | 1/1 | 0 | deferred |
| `exists_isArchTestFactor_nonneg_and_tsupport_subset_and_conj_invariant_and_flat` | 905 | 1 | 4/7 | 0 | deferred |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_norm_infinitePlace_eq_one_of_isCuspConstituent` | 716 | 2 | 2/2 | 0 | deferred |
| `CuspidalConstituent.exists_forall_whittakerCoefficient_mul_eq_sum_mul_whittakerCoefficient_mul_diagOne_of_isCuspConstituent` | 714 | 2 | 1/2 | 0 | deferred |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_isGenuineCuspRealizationAt` | 527 | 2 | 1/2 | 0 | deferred |
| `exists_integral_rightConv_eq_rightConv` | 514 | 3 | 2/3 | 0 | deferred |
| `SmoothCuspRealizationAt.not_exists_forall_apply_mul_heckeGen_eq_of_continuous` | 513 | 2 | 1/1 | 0 | deferred |
| `a_mul_conj_b_eq_and_norm_b_eq_of_sesqForm_covariant_of_ne_zero` | 468 | 2 | 2/4 | 0 | deferred |
| `exists_lintegral_adelicBorel_eq_mul_lintegral_coord_of_isMulLeftInvariant` | 429 | 3 | 1/1 | 0 | deferred |
| `SmoothCuspRealizationAt.exists_twist_rpow_absNorm_exceptionalSet_eq_toFun_eq_ideleNorm_det_rpow_mul` | 367 | 4 | 1/6 | 0 | deferred |
| `apply_weylInv_unipotent_mul_archSupportedAt_eq_norm_cpow_mul_apply` | 360 | 1 | 1/1 | 0 | deferred |
| `exists_finset_forall_exists_mem_valued_eq_max_and_contentHomFin_mul_sq_eq` | 333 | 1 | 1/1 | 0 | deferred |
| `CuspidalSpectrum.isArchTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 282 | 1 | 1/1 | 0 | deferred |
| `isIsotypicCuspFormAt_of_mem_isotypicCuspSubmodule` | 242 | 1 | 2/27 | 0 | deferred |
| `SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup` | 229 | 1 | 1/1 | 56 | deferred |
| `apply_weylInv_unipotent_mul_localWeyl_eq_modulus_cpow_mul_apply` | 217 | 2 | 1/1 | 0 | deferred |
| `CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous` | 214 | 3 | 2/4 | 0 | deferred |
| `apply_mul_eq_of_isKfSmooth_of_forall_placeEmbed_of_mem_maximalCompactAway` | 209 | 1 | 1/3 | 0 | deferred |
| `CuspidalSpectrum.exists_isLift_rightConv` | 199 | 4 | 11/13 | 215 | deferred |
| `peterssonIntegral_self_ne_zero_of_isFundamentalDomain_of_continuous` | 192 | 2 | 5/8 | 0 | deferred |
| `lintegral_rationalCentreUnipotentHaar_comp_heckeGen_mul_centralScalar_conj` | 179 | 1 | 1/1 | 0 | deferred |
| `cosetSum_rightConv_of_isLevelSphericalOfType` | 173 | 1 | 2/2 | 0 | deferred |
| `exists_isFundamentalDomain_globalPoints_range` | 165 | 3 | 1/11 | 0 | deferred |
| `heckeCosetSum_sum_rightConv_translate_eq_of_pure_reps` | 138 | 1 | 2/5 | 0 | deferred |
| `CuspidalSpectrum.isFinTestFactor_conj_inv_mul_ideleNorm_det_rpow` | 59 | 1 | 1/1 | 0 | deferred |
| `CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot` | 56 | 1 | 1/1 | 0 | deferred |
| `isFinTestFactor_integral_mul_of_isFinTestFactor_of_hasCompactSupport` | 48 | 1 | 1/1 | 0 | deferred |
| `CuspidalSpectrum.exists_hasModulus_of_isCuspConstituent` | 37 | 1 | 3/8 | 0 | deferred |
| `SiegelCovering.centreCutSiegelSet_coversModCentre_rat` | 30 | 1 | 1/6 | 23 | deferred |

### LEAVES — 56 rows / 11,461 silo, plus the one `NumberField` leaf this set takes

The leaf block is one family per line; none of it enters this set except the row marked **order A**.
Grouped for the deferral record: the **centre-cut / Siegel-covering** family (`exists_coversModCentre_…`
520, `exists_depth_…` 445, `memLp_iUnion_…` 432, `not_coversModCentre_…` 346,
`isCompact_centreCutSiegelSet_inter_heightCap` 282, `coversModCentre_…` 150/136,
`exists_iUnion_centreCutSiegelSet_mem_nhds` 25); the **archimedean approximation / flat test-factor**
family (70, 98, 196, 177, 165, 189, 317, 304, 384, 432); the **cusp carrier** family (40, 62, 75,
154, 199, 328); the **Hecke/Petersson tail** (148, 119, 108, 65, 46, 66, 78); the **`su2` /
circle-weight string** (755, 646); and the **rational quotient continuation** (440, 340).

| row (`AutomorphicForm.` / `NumberField.` dropped) | silo | prem | lev | return | disposition |
|---|---:|---:|---:|---:|---|
| `su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional` | 755 | 0 | 3/4 | 1077 | deferred |
| `CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup` | 646 | 0 | 2/4 | 0 | deferred |
| `exists_upperTriangular_globalPoints_mul_mul_scalar_mul_finIdeleDiag_inv_mem_finiteIntegralGL2` | 587 | 0 | 1/1 | 0 | deferred |
| `exists_sum_prod_mul_of_rightTranslatesSpanFinite` | 576 | 0 | 2/2 | 0 | deferred |
| `exists_coversModCentre_centreCutSiegelSetAmple` | 520 | 0 | 1/3 | 0 | deferred |
| `exists_depth_forall_apply_mul_lowerUnipotentGL2_eq_of_sum_translate` | 445 | 0 | 1/2 | 0 | deferred |
| `isFundamentalDomain_boxSheet_rationalTorusUnipotent` | 440 | 0 | 2/15 | 0 | deferred |
| `memLp_iUnion_centreCutSiegelSet_of_detWindow_le` | 432 | 0 | 2/7 | 0 | deferred |
| `WindowedSiegel.exists_forall_apply_one_zero_eq_zero_of_inv_mul_globalPoints_mul_mul_centralScalar_mem` | 386 | 0 | 3/4 | 0 | deferred |
| `exists_norm_a_le_absNorm_rpow_and_norm_b_le_of_smoothCuspRealizationAt_of_peterssonPairing` | 384 | 0 | 1/2 | 0 | deferred |
| `exists_isArchBiFinite_rightConv_comp_inv` | 376 | 0 | 1/1 | 0 | deferred |
| `not_coversModCentre_iUnion_centreCutSiegelSet_of_eq_zero` | 346 | 0 | 1/2 | 0 | deferred |
| `isFundamentalDomain_boxSheet_rationalCentreUnipotent` | 340 | 0 | 2/3 | 0 | deferred |
| `IsKfSmooth.exists_ideal_forall_apply_mul_conj_unipotentGL2_eq` | 328 | 0 | 3/4 | 0 | deferred |
| `exists_forall_adelicGLHaar_image2_unipotentGL2_mul_mul_le_of_isCompact` | 317 | 0 | 1/1 | 0 | deferred |
| `CuspidalSpectrum.exists_isArchBiFinite_flat` | 304 | 0 | 1/1 | 0 | deferred |
| `WindowedSiegel.isCompact_centreCutSiegelSet_inter_heightCap` | 282 | 0 | 5/10 | 0 | deferred |
| `CuspidalConstituent.exists_isFactorizableTestFn_isArchBiFinite_conj` | 245 | 0 | 1/1 | 0 | deferred |
| `SmoothCuspRealizationAt.isIdeleClassChar_and_admitsModulus_level_and_continuous_of_genuine` | 199 | 0 | 7/20 | 113 | deferred |
| `integral_prod_conj_eq_and_eq_conj_mul_of_conj_invariant_of_flat` | 196 | 0 | 4/5 | 0 | deferred |
| `exists_eq_mul_mem_levelOne_inf_finiteAdelicGL2Subgroup_commute_placeEmbed_of_forall_mem_localIntegralSet` | 192 | 0 | 1/1 | 0 | deferred |
| `IsFactorizableTestFn.comp_mul_unipotentGL2_mul_mem_pureTensorSet` | 189 | 0 | 1/4 | 0 | deferred |
| `exists_coordMatrix_rightTranslate_rot_of_linearIndependent_of_span_stable` | 184 | 0 | 1/1 | 0 | deferred |
| `isArchTestFactor_integral_mul_of_isArchTestFactor_of_hasCompactSupport` | 177 | 0 | 1/1 | 0 | deferred |
| `isArchTestFactor_of_contDiff_of_hasCompactSupport_of_tsupport_subset_isUnit_det` | 165 | 0 | 1/5 | 0 | deferred |
| `exists_borel_mul_gl2Weyl_mul_unipotentGL2_eq_of_integral` | 156 | 0 | 1/1 | 0 | deferred |
| `CuspidalConstituent.continuous_and_isSmoothCuspAutomorphicFnAt_rightTranslate_of_mem_cuspKFiniteSubmodule` | 154 | 0 | 8/19 | 0 | deferred |
| `typeSubmodule_inf_typeSubmodule_eq_bot` | 152 | 0 | 1/2 | 0 | deferred |
| `coversModCentre_of_le_of_lt_of_coversModCentre` | 150 | 0 | 4/8 | 0 | deferred |
| `CuspidalConstituent.forall_apply_mul_archRealGLAt_eq_of_isCuspConstituent_of_exists` | 148 | 0 | 2/2 | 0 | deferred |
| `constantTerm_adelicBox_unipotentGL2_mul` | 144 | 0 | 1/14 | 0 | deferred |
| `coversModCentre_iUnion_centreCutSiegelSet_of_detWindow` | 136 | 0 | 1/3 | 0 | deferred |
| `AdeleRing.finite_setOf_algebraMap_mem_of_isCompact` | 123 | 0 | 14/41 | 1082 | **order A** |
| `mem_rationalCentreUnipotent_iff_heckeGen_mul_centralScalar_conj_mem` | 119 | 0 | 1/1 | 0 | deferred |
| `existsUnique_diagOne_inv_mul_mem_scalar_sup_unipotent_of_mem_borelSubgroup` | 108 | 0 | 2/3 | 0 | deferred |
| `isFactorizableTestFn_sum_mul_comp_mul_mul` | 98 | 0 | 1/1 | 1131 | deferred |
| `norm_rightConv_le_eLpNorm_mul_eLpNorm_restrict_image_mul` | 78 | 0 | 2/2 | 0 | deferred |
| `IsUnitFactorizableAbove.finComponent_glFin_mem_localIntegralSet_of_apply_ne_zero` | 78 | 0 | 1/1 | 0 | deferred |
| `CuspidalSpectrum.isClosedCuspSubrep_topologicalClosure_map_toCuspSubcarrier_of_isCuspSubrep` | 75 | 0 | 2/4 | 0 | deferred |
| `isIdeleClassChar_and_continuous_of_isLsXiFunction_of_continuous` | 71 | 0 | 3/22 | 1361 | deferred |
| `exists_isRightEquivariant_comp_subtype_eq_of_injective` | 70 | 0 | 3/8 | 1445 | deferred |
| `exists_smoothCuspRealizationAt_productionPinsOf_toFun_eq_of_isBoundedOnSiegelWindows_of_coversModCentre` | 69 | 0 | 1/1 | 0 | deferred |
| `RankinSelberg.section_diagOne_mul_eq_ideleNorm_cpow_mul_of_isInducedSection_etaFst_etaSnd` | 66 | 0 | 1/1 | 0 | deferred |
| `existsUnique_bruhatRepresentative_mul_mem_borelSubgroup` | 65 | 0 | 2/3 | 0 | deferred |
| `isCompact_levelOne_inf_finiteAdelicGL2Subgroup` | 62 | 0 | 2/14 | 108 | deferred |
| `isLocallyConstant_iwasawaShellIndex_and_measurable` | 62 | 0 | 2/2 | 0 | deferred |
| `CuspidalConstituent.isCuspConstituent_productionPinsOf_mono` | 62 | 0 | 1/2 | 0 | deferred |
| `exists_continuous_monoidHom_matrix_apply_ne_one_of_ne_one` | 55 | 0 | 1/1 | 0 | deferred |
| `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn` | 51 | 0 | 5/18 | 133 | deferred |
| `iwasawaShellIndex_mul_of_mem_rationalCentreUnipotent` | 46 | 0 | 2/2 | 0 | deferred |
| `IsKfSmooth.finite_smul_image_of_isCompact` | 40 | 0 | 3/4 | 260 | deferred |
| `CuspidalConstituent.eq_of_isCuspConstituent_of_exists_mem_ne_zero` | 33 | 0 | 1/2 | 0 | deferred |
| `IsIsotypicCuspFormAt.exists_smoothCuspRealizationAt_toFun_eq_of_ne_bot` | 30 | 0 | 2/10 | 0 | deferred |
| `exists_iUnion_centreCutSiegelSet_mem_nhds` | 25 | 0 | 1/1 | 0 | deferred |
| `eq_zero_of_isLsXiFunction_of_coversModCentre_of_forall_mem_eq_zero` | 23 | 0 | 1/1 | 25 | deferred |
| `constantTerm_add` | 13 | 0 | 1/2 | 14 | deferred |
| `constantTerm_smul` | 11 | 0 | 1/1 | 11 | deferred |

## Appendix B — reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf-af20.json
python3 frontier.py --selfcheck
python3 port_advise.py --nodes <each of the five rows> --json build/af20-advise.json
python3 port_plan.py --json build/af20-advise.json
python3 build/af20-return3.py                      # the return column of §1 and the appendices
python3 build/af-worklist.py --prefix S_NumberField_ AdeleRing_finite_setOf_algebraMap_mem_of_isCompact
python3 build/af-worklist.py isHaarMeasure_rationalTorusUnipotentHaar_and_isMulRightInvariant \
  isHaarMeasure_rationalCentreUnipotentHaar_and_isMulRightInvariant isClosed_rationalTorusUnipotent \
  isClosed_rationalCentreUnipotent
cd ../.. && for m in FLTForHuman/MeasureTheory/HaarQuotient.lean \
  FLTForHuman/AutomorphicForm/Adelic/UnipotentQuotient.lean; do python3 lean/spec/check_port.py --force $m; done
```
