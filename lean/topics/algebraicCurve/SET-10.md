# SET 10 — the genus-preservation trio: `le`, `ge` and `eq` under an algebraically closed constant extension

**Status: landed (2026-10-31).** Read off the D–S shelf after SET 9 with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md). This is the
`AlgebraicCurve` ready set as it now stands: **two rows / 299 silo** (`le_genusFF_…` 151,
`genusFF_le_…` 148), plus the third row of the same story one edge behind them
(`genusFF_eq_…` 27).  The set is those three rows: **326 silo / 186 net**, one story, one manager
lane, **no definition gate, no promotion, no migration, no new module**.

| step | row (`AlgebraicCurve.` dropped) | silo | net | prem | lev |
|---|---|---:|---:|---:|---:|
| **LE** | `le_genusFF_of_constantFieldExtension_of_isAlgClosed` | 151 | 87 | 10 | 1 / 1 |
| **GE** | `genusFF_le_of_constantFieldExtension_of_isAlgClosed` | 148 | 86 | 11 | 1 / 1 |
| **EQ** | `genusFF_eq_of_constantFieldExtension_of_isAlgClosed` | 27 | 13 | 2 | — |
| | **3** | **326** | **186** | | |

§0 the read and its state; §1 the cut; §2 what the three rows say; §3 homes; §4 ground prep;
§5 traps; §6 gates; §7 calls; §8 reproduce and the forecast; §9 what this set does not do.

No Lean was run while scoping; the read is `frontier.py`'s cached graph, the pricing
`port_advise`/`port_plan`, `twin_scan` statement-level, and the home checks the port's own import
lines.

## 0. The read

Canonical, and — for the first time since SET 7 — **the instrument and the corrected read are the
same read**: SET 9 retired both FR-0047 name shadows (`weilReciprocity` and
`Place.isRational_of_isAlgClosed` are now ported at the general statements), so there is no marker
to subtract.

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf10.json
python3 frontier.py --selfcheck
```

**`--selfcheck` passes clean.**  This is worth one line of history because the SET 9 landing first
broke it: the PAIR headline was declared at the pin's spelling `…toHom_injective_of_divisible.{u, v}`,
which the frontier's own name scan reads as `…divisible.` (empty last name), so the source-tier node
was not covered by the name tier.  Dropping the explicit suffix (the universes come from
`universe u v`) fixed the frontier and cost one `own:` marker in the checker (FR-0076).  A landing can
be green in `check_port` and still leave the *read* inconsistent — the two instruments must both be
re-run.

| figure | value |
|---|---:|
| `needed [F terminal]` | 940 / 380,062 |
| frontier F | 1,475 / 747,304 |
| ready rows, all namespaces | 68 / 12,946 |
| leaves, all namespaces | 262 / 64,874 |
| `AlgebraicCurve` ready rows | **2 / 299** |
| `AlgebraicCurve` leaves | 0 |
| `AlgebraicCurve` demand | 51 / 19,717 |
| withheld by the FR-0044 guard | 4 / 831 (unchanged) |
| cone / avoided | 2,103 / 982,173 · 140 / 74,620 |

**The AC shelf, quoted whole.**  There is nothing else in the family:

| row | silo | prem | prem pruned | lev | what it is |
|---|---:|---:|---:|---:|---|
| `le_genusFF_of_constantFieldExtension_of_isAlgClosed` | 151 | 10 | 0 | 1 / 1 | `genusFF K F ≤ genusFF K' F'` |
| `genusFF_le_of_constantFieldExtension_of_isAlgClosed` | 148 | 11 | 0 | 1 / 1 | `genusFF K' F' ≤ genusFF K F` |

**…and one row behind them, which is the third row of the story**:
`genusFF_eq_of_constantFieldExtension_of_isAlgClosed` (27), whose only two premises are exactly the
two rows above.  It is not on the shelf because it is not yet transcribable; it is 9 lines of
`Nat.le_antisymm` once they are.  The set is the pair plus this capstone — the recipe's "one story
is 3–5 nodes".

**The premise audit, by hand (the SET 9 lesson).**  All eleven premise nodes are in the port at the
right statements — checked by reading each port declaration against its `Theorems/` wrapper, not by
last name:

| premise | port home |
|---|---|
| `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed` | `Place/ConstantFieldExtension.lean:723` |
| `ell_mapDomain_eq_of_constantFieldExtension_of_isAlgClosed` | `IsCurveOver/ConstantFieldExtensionSpan.lean` (**SET 9's row**) |
| `exists_genus_riemannIndex_of_isCurveOver` | `RiemannRoch/Assembly.lean:395` |
| `stichtenothGenusExists_of_isCurveOver` | `RiemannRoch/Assembly.lean` |
| `indexOfSpecialty_eq_finrank_H1` | `RiemannRoch/Assembly.lean:146` |
| `indexOfSpecialty_eq_zero_of_genusReached` | `Genus/Index.lean` |
| `exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed` | `Genus/ConstantFieldExtension.lean` |
| `essFiniteType_of_transcendental_of_finiteDimensional` | `IsCurveOver/EssFiniteType.lean` |
| `Place.deg_eq_one_of_isAlgClosed_of_finite` | `Defs/IsCurveOver.lean:58` |
| `Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed` | `Place/ConstantFieldExtension.lean:1262` |
| `Divisor.degree_eq_sum_support` (+ `finiteDimensional_lSpace`, for GE) | `Genus/Index.lean:70` / `:788` |

No shadow this time, and the audit says why: each of the two `Place.*_of_isAlgClosed` premises is a
single port declaration whose `spec-pin:` wire is its own pin file
(`Place/ConstantFieldExtension.lean:1262` is the only `mem_range_algebraMap_of_forall_ord_eq_zero*`
in the tree), and where a ℙ¹ relative exists it is named `RationalFunctionField.<same last name>`
(`deg_eq_one_of_isAlgClosed`), i.e. one namespace apart, so the last-name tier cannot fire.  SET 9's
shadow was exactly the case where the port had *dropped* that namespace distinction
(`Place.isRational_of_isAlgClosed` at the ℙ¹ statement) — hence the rule: a premise is audited by
reading its statement, and the shadow shows up as a port declaration whose *statement* is a
specialisation.

**`twin_scan` on the three rows: `new`, `new`, `new`** — no statement twin, so the FR-0041 check
(no port theorem with weaker hypotheses to rebuild on) passes by inspection: LE and GE are the two
halves of the Stichtenoth/riemann-index comparison under a constant extension, and EQ is their
`le_antisymm`.

**The pricing (§0.3 of the recipe), and the one thing to reuse.**  `port_plan`: 326 raw / 253
declaration lines / **32 duplicate copies** / 73 boilerplate / **35 already in the port** → **186
net new math lines** (LE 87, GE 86, EQ 13).  The 32+35 is the whole trap of this set: both `S_`
files open with the **same 35- and 32-line `constantsAreBase`** (the pin's two copies of one
prelude, at identical statements), and the port already has that theorem — as a **private**
`W7XChildE.constantsAreBase` in `Genus/ConstantFieldExtension.lean:1055`, itself a 9-line delegation
to the public `TorsionDescentDeriv.constantsAreBase_of_isAlgClosed`.  So:

* do **not** re-prove it (35 lines twice);
* do **not** write it in the home module — the home is *above* `Genus/ConstantFieldExtension`
  (§3), so the private copy is not importable;
* use the public engine it delegates to, in the shape the pin's prelude has:
  `TorsionDescentDeriv.constantsAreBase_of_isAlgClosed` (or `constantsAreBase_of_isAlgClosed` in the
  same module, which is also private — check which is reachable before writing).

**The definition layer: none.**  `port_advise --with-defs` puts only
`Def_AlgebraicCurve_IsCurveOver` (10 declarations) and `Def_AlgebraicCurve_Repartitions` (19) in the
statement closure, and **29 of those 37 declarations are already in the port byte-identically**; the
proof also uses `ell_zero_eq_one_of_constantsAreBase` (`Def_AlgebraicCurve_AdelicIndex`, ported at
`Defs/AdelicIndex.lean`, used already by `RiemannRoch/Assembly.lean`).  Nothing to create, nothing to
promote.

## 1. The cut

**Three rows, 326 silo, 186 net, one lane.**  This is a manager lane, not a dispatch: SET 8's
precedent was 265 net, and the recipe's smallest dispatch is ~1,100.  There is one story —
*the genus of a function field is preserved by an algebraically closed constant extension, and the
two inequalities are the two halves of the proof* — and the order is forced by the capstone:
LE and GE are independent of each other; EQ consumes both.

| step | rows | silo | net | home |
|---|---|---:|---:|---|
| LE + GE | 151 + 148 | 299 | 173 | insert `Genus/ConstantFieldExtensionConsequences.lean` |
| EQ | 27 | 27 | 13 | same module, after the pair |
| | **3** | **326** | **186** | 1 module, 6 wire lines |

**Wires.**  Two `spec-pin:` lines per row (`Theorems/Thm_…` + `P2M/Sol/S_…`, the second marked
`-- comparable copy`), six lines, in the home module's header.

**The gates** are §6's; the per-module build is the home module's own (`Genus/ConstantFieldExtensionConsequences.lean`,
0 in-tree importers, so the edit is cascade-free).

### 1.1 The landing — one manager session

The set is 186 net lines, so it was taken by the manager in one session (no worker order), in the
order the recipe asks for: wires and header first, then the prelude, then LE and GE, then EQ.

| step | module (Δ source lines) | checker | build | axioms |
|---|---|---|---:|---|
| wires + header sentence | `Genus/ConstantFieldExtensionConsequences.lean` (+12) | — | — | — |
| the prelude adapter + LE + GE + EQ | same module (304 → **541**, +237) | 6 → **9 ok** / 0 / 0 / 0 own | silent, 4.6 s (module; 3,664 jobs cold), **zero warnings from this module** | all three clean |

**What the set consumed**: 3 rows / 326 silo / **247 net new math lines** as written (186 net from
the `S_` files — the 32-line second copy of the prelude is not written, the 35-line first copy is a
3-line adapter — plus the statements' docstrings and the private adapter); one insert, six wire
lines; 0 new modules, 0 imports, 0 promotions, 0 migrations, 0 markers.  `dedup.py --within`: 10
declarations, **0 clusters**.  `spec/AlgebraicCurveSet10Consumer.lean` (Zones A/B): **0 errors**.

**The read it leaves** — the forecast of §8 was exact to the line:

| figure | before | after | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 940 / 380,062 | **937 / 379,736** | 937 / 379,736 ✓ |
| frontier F | 1,475 / 747,304 | **1,478 / 747,630** | 1,478 / 747,630 ✓ |
| `AlgebraicCurve` demand | 51 / 19,717 | **48 / 19,391** | 48 / 19,391 ✓ |
| `AlgebraicCurve` ready | 2 / 299 | **0** | 0 ✓ |
| ready rows, all namespaces | 68 / 12,946 | 67 / 12,912 | — |
| `--selfcheck` | PASS | **PASS** | — |

And the row it makes ready is the MC one, as forecast:
`ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom` (**265**) is now the fourth row of the MC
shelf (8 rows / 1,538), which is the MC column's to cut.

**Deviations held for review** (no statement changed; every `check_port` hash matched):

- **The pin's `id hfg` is load-bearing.**  `obtain ⟨x, hxt, hxfd⟩ := hfg` *clears* `hfg`, and both
  proofs need `hfg`/`hfg'` again for the lift (`Place.exists_comap_algebraMap_eq_…`), so the pin's
  `:= id hfg` is what keeps the existential around.  Written without the `id`, the module fails at
  the lift with `Unknown identifier hfg` — exactly the trap §5.1 recorded, now measured.
- **One v4.34 rename**: the pin's `Finsupp.mapDomain_apply hlift_inj` is
  `Finsupp.mapDomain_apply_of_injective hlift_inj` in mathlib v4.34 (`mapDomain_apply` is now the
  `sum`-form).  Two occurrences, in the two `hdegEq` blocks.
- **The prelude is a 3-line private adapter** at the pin's `∃ x` shape over the public
  `constantsAreBase_of_isAlgClosed_of_transcendental` (§7 call 3 taken): neither the pin's 35-line
  proof nor a promotion of the private `W7XChildE.constantsAreBase` (which §3 showed is
  unreachable from the home anyway).
- **No `maxHeartbeats`.**  The pin sets 4M on both files; the module builds at the project cap, and
  the edit loop needed only the default 200k for the *statement* pass and `-DmaxHeartbeats=1000000`
  for the whole file (the LE/GE `choose`/`linarith` blocks).  No `set_option` was added.

## 2. What the three rows say

All three are at the same binders (the wrappers', verbatim): `K ⊆ F ⊆ F'`, `K ⊆ K' ⊆ F'` with
`F'` generated over `K'` by the image of `F`, both constants algebraically closed, both curves over
their constants, and the two finite-model hypotheses `hfg`/`hfg'`.

* **LE (151)** — `genusFF K F ≤ genusFF K' F'`.  Both sides are read as the `γ` of
  `exists_genus_riemannIndex_of_isCurveOver`; on the `K`-side take the Stichtenoth divisor `D₀` at
  which the genus is reached (`indexOfSpecialty D₀ = 0`, hence
  `degree D₀ - ell D₀ = γ - 1`), lift it along the unique lift
  `Place.exists_comap_algebraMap_eq_of_constantFieldExtension_of_isAlgClosed`, use
  `degree (mapDomain lift D₀) = degree D₀` (all places have degree one) and SET 9's
  `ell_mapDomain_eq_…`, and the non-negativity of the index of specialty on the `K'`-side gives
  `γ ≤ γ'`.
* **GE (148)** — `genusFF K' F' ≤ genusFF K F`, the mirror: this time the Riemann–Roch side is a
  *dimension* count (`finiteDimensional_lSpace`) and the key input is
  `exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed`, which
  transports the vanishing of the index of specialty the other way; the genus inequality follows from
  the degree identity at `D₀` again.
* **EQ (27)** — `genusFF K' F' = genusFF K F` by `Nat.le_antisymm` of GE and LE, in that order (the
  pin's `solution` is 9 lines).

## 3. Home — one insert, no new module

The nine premise modules are `Place/ConstantFieldExtension`, `RiemannRoch/Assembly`, `Genus/Index`,
`IsCurveOver/EssFiniteType`, `Defs/IsCurveOver`, `IsCurveOver/ConstantFieldExtensionSpan`,
`Genus/ConstantFieldExtension`, `Defs/AdelicIndex`, `Defs/Repartitions`.  The
"module above all of them" search over the port's import closure returns **exactly one**:

| candidate | above all nine? | importers |
|---|---|---|
| `Genus/ConstantFieldExtensionConsequences.lean` | **yes** (closure 107) | **0** |
| `Genus/ConstantFieldExtension.lean` | no — it is *below* `…Consequences` (which SET 8 built on top of it) | 3 |
| `RiemannRoch/Assembly.lean` | no — misses five | 6 |
| `Genus/Index.lean` | no — misses six | 8 |

So: **insert into `Genus/ConstantFieldExtensionConsequences.lean`**, the module SET 8 created for the
isAlgClosed/transcendental consequences (the pole bound and the pole-sum degree identity), which
already imports everything these three rows need.  It is 0-importer, so cascade-free; the subject is
the same ("what an algebraically closed constant extension does to the genus-side invariants"); and
the alternative — a new `Genus/ConstantFieldExtensionGenus.lean` above it — buys nothing but a header.

**Import-direction check.** No new import is needed (verified: the module is above all nine).  If the
worker finds one missing, it is an edge *into* the home from a module the home already dominates, so
it is either already there or a genuine cycle to report — do not add it blindly.

**No legacy module, no migration, no promotion, no new `Def_` module.**

## 4. Ground prep (the manager's)

1. `Genus/ConstantFieldExtensionConsequences.lean`: add the six `spec-pin:` lines (two per row) to
   the header, and extend the header's subject sentence to name the genus invariance as the module's
   third subject (it currently names the pole bound and the support-sum degree identity).
2. Nothing else: no import, no marker, no `decl_markers.tsv` row, no `PORT_FILES` change.  (Check the
   module is not in `spec/old_check_stmts.py`'s `PORT_FILES` — it is not: SET 8 created it wired.)

## 5. Per-row traps

**LE (151).** (i) The pin sets `maxHeartbeats 4000000` — forbidden; the module must build at the cap
and the edit loop may need `-DmaxHeartbeats=2000000` (the same as the span module's, FR-0048-adjacent;
record it if so).  (ii) `obtain ⟨x, hxt, hxfd⟩ := id hfg` — the `id` is the pin's (it keeps the
`∃` from being eliminated by instance search); keep it.  (iii) The lift is a *four-way* `choose`:
`have hX := fun P => Place.exists_comap_algebraMap_eq_… K F K' F' hfg hfg' hgen P` then
`choose lift hlift_comap hlift_ord hlift_uniq using hX` — the comap theorem's conclusion is a
4-tuple (`∃ P', comap = … ∧ ord = … ∧ unique`), so a `choose` with four names is what consumes it.
(iv) `hlift_inj` comes from `Place.ext` on the comap identities, not from injectivity of the map
itself.  (v) The `γ = genusFF` identification is a `linarith` after
`ell_zero_eq_one_of_constantsAreBase` and `indexOfSpecialty_eq_finrank_H1` at `D = 0`, with
`unfold genusFF; push_cast` — the `push_cast` placement matters (`genusFF` is a `ℕ`).
(vi) `haveI : FiniteDimensional K ↥(riemannRochSpace D₀) := hD₀.finite` before calling SET 9's
`ell_mapDomain_eq`, whose last argument carries `[FiniteDimensional K ↥(riemannRochSpace D)]`.
(vii) `push_neg` in the pin's `hdiv` block is the deprecated spelling (FR-0036: `push Not`).

**GE (148).** (i) The mirror argument needs `finiteDimensional_lSpace` (`Genus/Index.lean:788`,
whose `[IsCurveOver K F]` and `hL0` come from the section's variables and `hfd0`); the pin opens it
with `obtain ⟨hne, hfd0, γ₀, D₀, hD₀⟩ := stichtenothGenusExists_of_isCurveOver …` and installs
`haveI : Nonempty (Place K F)` / `haveI : FiniteDimensional K ↥(LSpace 0)` from it.  (ii) The key
input is `exists_indexOfSpecialty_mapDomain_eq_zero_of_constantFieldExtension_of_isAlgClosed`, whose
statement is at the pin's binders (already ported; check its argument order before writing the call).
(iii) Same `maxHeartbeats` and `push Not` notes as LE.

**EQ (27).**  Nine lines: `Nat.le_antisymm (GE …) (LE …)` with the arguments in the wrapper's order;
the pin applies GE first, LE second.  `hfg`/`hfg'`/`hgen` pass through unchanged; the two `IsCurveOver`
instances are in scope.  Its `S_` file imports only the two wrappers plus two `Def_` modules, so no
new import.

## 6. The gates, per step

As in SET 6–9 and the recipe §6, unchanged:

1. `python3 spec/check_port.py --force <module>` → **0 mismatch, 0 missing**, three new `ok` rows
   (the module currently checks `6 ok / 0 / 0`; see §8).
2. `#print axioms` on the three headlines → `[propext, Classical.choice, Quot.sound]`.
3. The module's own `lake build` under `flock`/`timeout`; silent; no tree build, no dependents.
4. `dedup.py --within --module <module>`: report clusters, do not refactor (expect nothing new — the
   three headlines are distinct statements).
5. Zero warnings; no `sorry`/`admit`/`axiom`/`native_decide`; no `set_option maxHeartbeats`.
6. A `spec/` consumer zone with a real composition: `spec/AlgebraicCurveSet10Consumer.lean` —
   compose EQ with SET 9's `ell_mapDomain_eq` at `D = 0` (genus invariance read as
   `ell 0` invariance is *not* what holds — use `genusFF` at the *pole divisor* instead), or compose
   LE with `stichtenothGenusExists_of_isCurveOver` to read `γ ≤ γ'` at a concrete curve, and GE with
   `indexOfSpecialty_eq_zero_of_genusReached`; error count is the metric.

## 7. The calls

| call | recommendation | what it changes |
|---|---|---|
| 1. the cut | **the three rows / 326 silo / 186 net** (the pair + the 27 capstone), one manager lane, no worker order | 186 net is below the recipe's smallest dispatch; the pair alone would leave the capstone for a later one-row set |
| 2. the home | **insert `Genus/ConstantFieldExtensionConsequences.lean`** (+0 imports, +6 wires) rather than a new `Genus/ConstantFieldExtensionGenus.lean` | it is the only module above all nine premise modules and it is 0-importer |
| 3. the prelude | **use the public `TorsionDescentDeriv.constantsAreBase_of_isAlgClosed`** in the pin's `hfg` shape; do not re-prove the 35/32-line `constantsAreBase`, do not promote the private copy in `Genus/ConstantFieldExtension.lean` | a promotion would publish a `W7X`-named declaration (the port's naming rule) for a prelude the pin keeps private in both files |
| 4. the dispatch | **one manager session**: LE + GE (independent) then EQ | the chain is two-then-one; no file conflict |
| 5. the EQ row | include it: 13 net lines and it *is* the story's headline (`genusFF K' F' = genusFF K F`) | without it the set leaves a 27-line row one edge away |

All five were taken as recommended; §1.1 records the landing, the two v4.34/pin deviations and the
measured numbers.

## 8. Reproduce, and the forecast

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json   # §0, no markers now
python3 frontier.py --selfcheck                                                    # PASS (it was not, before SET 9's fix)
python3 port_advise.py --with-defs --nodes <each row> --json build/set10-defs.json # §0.2
python3 port_advise.py --nodes <each row> --json build/set10.json                  # 186 net
python3 port_plan.py --json build/set10.json
python3 twin_scan.py --node <each row>                                             # new, new, new
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/Genus/ConstantFieldExtensionConsequences.lean
```

**What the set consumes**: 3 rows / 326 silo; **186 net new math lines**; one insert, six wire lines;
0 new modules, 0 imports, 0 promotions, 0 migrations, 0 markers.

**What it leaves** (measured in §1.1 — the forecast was exact): `needed` **937 / 379,736**
(−3 / −326); `AlgebraicCurve` demand **48 / 19,391**; frontier **1,478 / 747,630**; and the family's
ready shelf **0 rows** — the constant-field-extension story is complete with this set.

**The row this set makes ready is not in the family**: `ModularCurve.genusFF_qExpFunctionFieldC_eq_of_ringHom`
(**265 silo**) becomes ready the moment EQ lands — the MC column's genus comparison for the
`q`-expansion function field of `X₀(N)`, which has been waiting on exactly this equality.  That is the
recipe §7 answer, and it is the MC column's to cut.

**Where the `AlgebraicCurve` column goes after this.**  The family's remaining demand is **48 nodes
/ 19,391** (`--list`), and reading the list is the whole answer — it is *two* stories, neither on a
ready shelf:

* **the regular-prolongation / constant-reduction block (≈34 of the 48 nodes)**: the chain
  `exists_constantReduction_of_constantFieldExtension` → `exists_valuationSubring_section_of_…` →
  `exists_regularProlongation_retraction_of_…` → the `Divisor.mapDomain_placeReduction_*` /
  `finrank_riemannRochSpace_…_placeReduction_*` rows → `Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension`
  → `Place.exists_natCast_dvd_ord_sub_single_sub_single` (**267**) → `Pic0.exists_nsmul_eq` (130),
  which is what the pairing family (`Pic0.exists_antisymmWeilPairing` 656, the `freeAlgebra_lift_*`
  correspondence rows) and SET 9's PAIR row are waiting on.  The `RegularProlongation.*` rows are
  ~30 nodes with 15+ premises each, and the block's own topic is
  [TOPIC-basechange-correspondence.md](TOPIC-basechange-correspondence.md) /
  [TOPIC-t6-local-exchange.md](TOPIC-t6-local-exchange.md) — this is a **recon pass, not a ready
  cut**;
* **the two withheld rows** (`…_complex` 126, `Pic0.finite_torsion_…` 95), the prunable subject's.

Nothing else is near: the big unported AC nodes in the *cone* (the 7,954-line
`fibreResidueIdentityAlong_…`, the 7,889-line `residueTheorem_of_residueTheorem_ratFunc_…`, the
4,816-line `tateAgreement_v2`) are **not in the target's demand** — they sit below ported nodes or
are leaves whose consumer is ported, which is why `needed` does not count them.  So after SET 10 the
column is either the regular-prolongation recon, or a hand-off to the MC column, which EQ unblocks.

## 9. What this set does not do

- **The one row it makes ready (265, MC).**  It is the MC column's; this set only unblocks it.
- **Anything behind the prunable complex-analytic subject.**  `Place.exists_natCast_dvd_ord_sub_single_sub_single_complex`
  (126) and `Pic0.finite_torsion_of_isAlgClosed_of_charZero` (95) stay withheld (RR column's phase 3),
  and the two `ModularCurve` Tate-module rows with them.
- **The `Def_` Galois block and `WeilPairingData`** — SET 9's carry-forwards, untouched here.
- **No new module, no promotion, no migration, no tree build.**  The one legacy question
  (`Genus/ConstantFieldExtensionConsequences.lean`'s status) is settled in §4: it is already wired.
