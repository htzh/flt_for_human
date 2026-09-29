# WeightOne rectification — measured record

Owner: the manager. The plan is
[topics/hecke/TOPIC-weightone-rectify.md](../topics/hecke/TOPIC-weightone-rectify.md); the
set briefs are [SET-W0](../topics/hecke/SET-W0.md) – [SET-W4](../topics/hecke/SET-W4.md).

## Baseline (before SET-W1, 2026-09)

Tool: `tools/deps/port_graph.py` (179 modules, 440 intra-port edges, 6,074 declarations of
which 4,021 private, 82,077 lines).

`--blocks 5`:

```
7242 lines  (7350 raw, 108 adapter) across 12 modules
    modules: JqAnalyticModel, WeightOne.Basic, WeightOne.FrickeFunction,
             WeightOne.Gamma0Integral, WeightOne.Gamma0Rationality, WeightOne.Gamma1Basis,
             WeightOne.Gamma1IntegralBasis, WeightOne.LevelFraction, WeightOne.LevelN,
             WeightOne.LevelOneHauptmodul, WeightOne.MonicRel, WeightOne.WeierstrassPTorsion
    strongest factoring units:
        1677 lines / 135 proofs   LevelFraction <-> LevelN
        1512 lines /  76 proofs   Gamma0Rationality <-> Gamma1Basis
        1392 lines /  73 proofs   FrickeFunction <-> LevelFraction
        1016 lines /  46 proofs   LevelFraction <-> LevelOneHauptmodul
         973 lines /  65 proofs   FrickeFunction <-> LevelN

140 lines / 8 proofs   ModularCurve.Analytic.Gamma0InvariantCore <-> ModularCurve.PhiGenDescent
```

Statement level (checker's `raw_declarations`, private included): **245 declarations with
byte-identical statements in ≥2 files**, 36 exact-file-set groups; 56 more share a name but
differ in binder spelling or predicate.

Per-consumer duplicated private declarations (the SET-W2 deletion checklist): `Basic` 26,
`WeierstrassPTorsion` 55, `LevelOneHauptmodul` 73, `FrickeFunction` 111, `LevelFraction`
168, `LevelN` 148.

Build/checker baseline:

- `timeout 300 lake build` — green, **4,643 jobs**, ~9 s fully cached.
- `python3 spec/check_flt_statements.py` — **1653 identical / 91 promoted / 0 mismatched /
  0 missing / 28 own** (1,681 checked).
- `spec/WeightOneConsumer.lean` — exit 0.

## After SET-W1 / start of SET-W2 (2026-09)

**Five** homes created, all building green with 0 warnings and clean `#print axioms`:

| module | source | notes |
|---|---|---|
| `ModularForms/WeightOne/Defs/PeriodPair.lean` | the `WLight` prelude in 5 files | `periodPairOfTau`, `smulPeriodPair`, `smulLatticeEquiv`, `weierstrassP_smulPeriodPair`, `periodPair_eq_of_ω` (11) |
| `ModularForms/QExpansionCoeff.lean` | `Basic.lean` §`Width`/`WidthMF` | `qParam_one_eq_pow`, `qExpansion_coeff_width_fn`, `UpperHalfPlaneAux.ModularFormClass.qExpansion_coeff_width` (3) |
| `ModularForms/DiscPow.lean` | `Basic.lean` §`RatCoeff`/`DiscPow`/`BSix`/`KPoleSec` | the Δᵐ package, `ratCoeff_*`, `KPoleAt`/`KPole`, boundedness/periodicity (27) |
| `ModularForms/WeightOne/Defs/PTorsion.lean` | `FrickeFunction`/`WeierstrassPTorsion` | ℘-torsion vocabulary `zetaN`/`qN`/`wpTorsion`/`wpNorm`/`kN`/`wpMon*`/`frickeH` (21; the lemmas that consume the `weierstrassP_torsion_qExpansion_package` headline stay in the consumers) |
| `ModularForms/WeightOne/Fricke.lean` | `FrickeFunction` | `denomZ`, `vecMulSL`, `frickeF`, `wpNormZ`, `FrickeIdx` (14; the slash lemmas stay, above the torsion-point package) |

`Pole` was folded into `DiscPow` (same closed region). The `Basic` prelude region
(lines 1278–1563, 27 declarations) had an **empty `--closure`**, which is what made it
liftable as one home.

**SET-W2 step 1 — `Basic` rewired.** It now imports `ModularForms.DiscPow` and its lifted
`UpperHalfPlaneAux` prelude is deleted: 1,863 → 1,579 lines (−284 including the removed
sections). The remaining `BEightEngine`/`BEightHelper` sections still resolve
`KPoleAt`/`qExpansion_coeff_width` through the namespace the home republishes.

- `timeout 200 lake build` — green, 4,646 jobs.
- `python3 spec/check_flt_statements.py` — **1653 identical / 91 promoted / 0 mismatched /
  0 missing / 28 own** (unchanged).
- `python3 port_graph.py --blocks` — **7,242 → 6,982** removable lines, and `Basic` has
  dropped out of the cluster (12 → 11 modules).

**Measured cost of editing `Basic`:** the dependents' recompile is a **4 min 47 s** wall
(430 s CPU, 158 % — parallel, not a blow-up). That is the whole-tree wave the schedule
exists to pay once, and the reason W2 must edit each big module in a single pass.

**SET-W2 step 2 — reverted.** `WeierstrassPTorsion` rewired on its own (1,317 → 1,223 lines,
24 statement-identical copies deleted, green in 20 s), but it exported `PeriodPair`'s
top-level names into the consumers below it while those still defined their own copies:
`Ambiguous term` at `LevelN:1241`. Extending the same scripted treatment to
`LevelOneHauptmodul`/`FrickeFunction`/`LevelFraction`/`LevelN` then hit two more failure
modes — qualified references (`WLight.qExpansion_coeff_width`) dangling because the home
spells the name `UpperHalfPlaneAux.ModularFormClass.qExpansion_coeff_width`, and
`Application type mismatch` where a local copy's binder shape differed from the home's. All
five files were reverted; the tree is green again (4,648 jobs, checker 1653/0/0, consumer
exit 0). The full failure analysis and the corrected plan are in
[SET-W2.md](../topics/hecke/SET-W2.md) §"The W2 wave cannot be done file-by-file with a blind
script": fix the **namespace policy** first, then do one bottom-up pass that also rewrites
qualified references, and only then build the family.

Net state: **7,242 → 6,982** removable lines (one file, `Basic`); the two biggest units
(`LevelFraction ↔ LevelN` 1,677, `FrickeFunction ↔ LevelFraction` 1,392) are untouched, which
is the W2 wave's remaining work.

## After SET-W2

The level family is rewired onto the homes. Each consumer imports the homes and `open`s
`WLight`/`UpperHalfPlaneAux`; every private copy whose normalized statement equals a home
declaration is deleted, in one coordinated pass:

| module | before → after | deleted |
|---|---|---|
| `Basic.lean` | 1,863 → 1,579 | (region) |
| `WeierstrassPTorsion.lean` | 1,317 → 1,160 | 31 |
| `LevelOneHauptmodul.lean` | 2,803 → 2,570 | 36 |
| `FrickeFunction.lean` | 3,702 → 3,304 | 65 |
| `LevelFraction.lean` | 3,874 → 3,606 | 38 |
| `LevelN.lean` | 3,386 → 3,112 | 39 |

- `timeout 500 lake build` — green, **4,648 jobs**, 6 min 19 s wall (the wave's recompile).
- `python3 spec/check_flt_statements.py` — **1653 identical / 91 promoted / 0 mismatched /
  0 missing / 28 own** (unchanged).
- `spec/WeightOneConsumer.lean` — exit 0.
- `port_graph.py --blocks` — **6,982 → 5,737** removable lines; cumulative **7,242 → 5,737**
  (−1,505, ≈21 %).

**Deferred to W4:** the `qExpansion_coeff_width` family. Each file namespaces it differently
and its call sites choose between the pointwise (`_fn`) and bundled forms; deleting them in
this wave produced `Application type mismatch`. W4 will **generalise** the family to one
lemma and keep a thin local alias where a call site needs the other shape, rather than
forcing a relink here.

## After SET-W3 (partial)

`Defs/Gamma.lean` created (8 declarations: `tauPair`, `tauPair_spec`, `WW`, `WW_spec`,
`fricke`, `fricke_spec`, `jf`, `jf_spec`), lifted from `Gamma0Rationality`'s
`X1DiamondRational` namespace where the block's `--closure` is empty. The four Γ modules
import it, `open` `WLight`, and delete their statement-identical copies:

| module | before → after |
|---|---|
| `Gamma0Rationality.lean` | 3,012 → 2,978 |
| `Gamma0Integral.lean` | 2,517 → 2,483 |
| `Gamma1Basis.lean` | 4,246 → 4,213 |
| `Gamma1IntegralBasis.lean` | 1,082 → 1,049 |

- `timeout 500 lake build` — green, **4,649 jobs**, 2 min 15 s wall.
- checker — **1653 identical / 0 mismatched / 0 missing** (unchanged).
- `WeightOneConsumer.lean` — exit 0.
- `--blocks` — **5,737 → 5,639**; cumulative **7,242 → 5,639** (−1,603, ≈22 %).

**Width family, first slice (the `qExpansion_coeff_widthN` spelling).** The Γ block's closure
keeps needing the width formula, so the first piece of W4's generalisation landed: the home
`ModularForms/QExpansionCoeff.lean` now carries `qExpansion_coeff_widthN` — the Γ spelling,
with `N` as an **explicit** section variable and `[NeZero N]` supplying the non-vanishing
hypothesis — proved from the existing `qExpansion_coeff_width_fn`. `Gamma0Integral`,
`Gamma0Rationality`, `Gamma1Basis` and `LevelN` drop their 30-line copies and `open
UpperHalfPlaneAux`.

- `timeout 500 lake build` — green, **4,649 jobs**, 6 min 53 s wall.
- checker — **1653 identical / 0 mismatched / 0 missing**; consumer exit 0.
- `--blocks` — **5,639 → 5,539**; cumulative **7,242 → 5,539** (−1,703, ≈23.5 %).

**Width family, completed.** The rest of the family is homed too:
`UpperHalfPlaneAux.qExpansion_coeff_width` (the weight-one packages' function-form spelling,
an alias of `qExpansion_coeff_width_fn`), `qParam_one_eq_pow` and `qExpansion_coeff_unique'`
(the latter copied from `Gamma0Rationality`). Deleted: the function-form
`qExpansion_coeff_width` and `qParam_one_eq_pow` from `FrickeFunction`, `LevelFraction`,
`LevelN`, `LevelOneHauptmodul`, `WeierstrassPTorsion`; `qExpansion_coeff_unique'` from
`Gamma0Integral`, `Gamma0Rationality`, `Gamma1Basis`, `LevelN`. A qualified reference
(`WLight.qExpansion_coeff_width` in `LevelOneHauptmodul`) was rewritten to
`UpperHalfPlaneAux.qExpansion_coeff_width`.

- `timeout 500 lake build` — green, **4,649 jobs**, 6 min 43 s wall.
- checker — **1653 identical / 0 mismatched / 0 missing**; consumer exit 0.
- `--blocks` — **5,539 → 5,333**; cumulative **7,242 → 5,333** (−1,909, ≈26 %).

**Lesson — the same statement text can elaborate to different binders.** The checker's
statement-identity gate matched a consumer copy whose `N` was an explicit section variable
against a home lemma whose `N` was implicit: section-variable binders do not appear in the
declaration text. The first attempt therefore compiled in three modules and failed in
`LevelN`/`Gamma0Rationality` at the call sites (`qExpansion_coeff_widthN N …`). The fix is to
give the home lemma the **explicit** form; the text is unchanged, so the gate still matches.
When a shared lemma takes a section variable, check both the source text *and* the binder
form, or the wave will pass some consumers and break others.

**Still unshared in the family:** the `ModularFormClass.qExpansion_coeff_width` copies in
`LevelOneHauptmodul`/`WeierstrassPTorsion` (their local namespace is
`WLight.ModularFormClass`, the home's is `UpperHalfPlaneAux.ModularFormClass`, so sharing
needs the declarations deleted and the qualified references rewritten), and the
`Gamma0Integral`/`Gamma0Rationality` spellings of `qParam_one_eq_pow` (`τ : ℍ` rather than the
home's `τ : ℂ`).

**Next Γ sub-block (scoped, not yet lifted):** the `cw*`/`conj_mem_Gamma`/`gen(Set)`/
`exists_rat_combination` rationality vocabulary shared by `Gamma0Rationality` and
`Gamma1Basis` (205 pin-lines / 32 units). Piecemeal lifting of these failed because the
declarations are spread across the `Cyclo`/`Group`/`Invariance`/`Fricke` sections and need
those sections' `open`s and `variable`s; the robust route is to lift the whole
`X1DiamondRational` region (or the enclosing sections) with its context, which in turn needs
the rest of the width family (`qExpansion_coeff_width`, `qExpansion_coeff_unique'`,
`qParam_one_eq_pow`) homed first.

## After SET-W4

*(to be filled: final `--blocks`, checker total and the demotion reconciliation, the four
verification commands)*

## Post-W4 block homing (2026-09)

The width family removed the block on the *entangled* proofs, so several standalone duplicated
blocks could then be lifted by the same recipe. Landed, each verified green:

| block | copies | home |
|---|---|---|
| `kPole_algebraMap` | 5 (`FrickeFunction`, `LevelFraction` ×2, `LevelN`, `LevelOneHauptmodul`) | `DiscPow` |
| `kPole_jf` | 3 (`FrickeFunction`, `LevelFraction`, `LevelN`) | `DiscPow` |
| `periodic_mul` | 6 (`LevelN`, `Gamma0Rationality` ×3, `Gamma1Basis` ×2) | `DiscPow` |
| `periodic_disc_one` | 7 (`LevelN`, `Gamma0Rationality` ×3, `Gamma1Basis` ×3) | `DiscPow` |
| `qExpansion_one_discPow` | 5 (`FrickeFunction`, `LevelFraction` ×2, `LevelN`, `LevelOneHauptmodul`) | `DiscPow` |
| `analyticAt_cuspFunction_zero_of` | 5 (`FrickeFunction`, `LevelFraction` ×2, `LevelN`, `LevelOneHauptmodul`) | `DiscPow` (respelled `MDiff` → `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)` so the gate matches) |
| `MonicRel` valuation engine | 6 in `LevelFraction` | **promoted** in `MonicRel` (`le_meromorphicOrderAt_sum`, `meromorphicOrderAt_le_of_monicRel`, `meromorphicOrderAt_div_nonneg_of_monicRel`, `analyticOnNhd_comp_ofComplex`, `mdifferentiable_of_analyticOnNhd`) |
| `differentiableAt_comp_ofComplex` + `eq_zero_of_mul_eq_zero` | 5 + 7 in `Gamma1Basis`/`Gamma1IntegralBasis`/`LevelN` | `MonicRel` |

`--blocks`: 5,333 → **4,560** across the eight blocks (cumulative **7,242 → 4,560**, −2,682,
≈37 %); the cluster shrank from 11 modules to **10** (`Basic`, `MonicRel` both gone).
Checker **1660 identical / 92 promoted / 0 mismatched / 0 missing**; consumer exit 0.

**The `X1DiamondRational` region lift (SET-W3b).** The Γ rationality vocabulary lives inside
`namespace X1DiamondRational` across nine sections of `Gamma0Rationality`; lifting declarations
individually loses the sections' `open`s and `variable`s, so the whole vocabulary region
(lines 1151–2047, `Cyclo`…`Algebra`, excluding the `Main` headline section) was lifted into
`WeightOne/Defs/GammaRational.lean` preserving the namespace, plus the file-level opens,
`open WLight`, `open UpperHalfPlaneAux` and `variable (N : ℕ)`. Two subtleties: the region's
local `zetaN`/`kN` duplicate `WLight`'s with the same elaborated type, so they were dropped
from the home to avoid an ambiguous-term error under the two `open`s; and the region consumes
the level-family **headlines** (`frickeFunction_modularity_package`, `qExpansion_sigmaTransport_package`,
`levelN_structure_package`, `linearIndependent_complex_of_qExpansion_rational`,
`exists_levelFraction_of_stable_family`), so the home imports `FrickeFunction`/`LevelFraction`/
`LevelN`/`LevelOneHauptmodul` — no cycle, since none of them imports `Gamma0Rationality`.
`Gamma0Rationality` now imports the home, `open X1DiamondRational`, and its region is gone
(2,800 → 1,890 lines).

`--blocks`: **4,560 → 3,870** (cumulative **7,242 → 3,870**, −3,372, ≈47 %). Checker unchanged
at 1660 / 92 / 0 / 0; consumer exit 0.

**The rewire of `Gamma1Basis`/`Gamma0Integral`/`Gamma1IntegralBasis` to the region home was
reverted.** Deleting their 100 + 17 + 2 statement-identical copies reproduced the known
binder-form failures (`Application type mismatch` at call sites, `Unknown identifier Idx`
when a name was matched by statement alone). The three modules were restored to their
pre-round state and the *earlier* rounds' deletions re-applied with a **name + statement**
gate (26 / 12 / 9 copies). They still carry the region's vocabulary; wiring them needs the
per-declaration call-site review, not another batch pass.

**Promotions in a checked module need their pin `S_` files in `SOURCES`.** Making
`MonicRel`'s five helpers public (so `LevelFraction` could drop its copies) turned the checker
from `0 missing` to `5 missing`: the pin carries them `private` in the `S_` files, which were
not in `SOURCES`, so the promoted-from-pin-private lookup could not see the originals. Adding
`P2M/Sol/S_WLight_exists_{analyticOnNhd_div_of_monicRel,mdifferentiable_div_of_monicRel,twist_of_flat,span_inter_rational_of_twist_stable}.lean`
fixed it; the same treatment for the two analytic helpers added
`P2M/Sol/S_CuspForm_{exists_mul_E4_pow_mul_E6_pow_eq_iff,span_frickeRational_E4_pow_E6_pow_eq_top,...}.lean`.
The rule: **when a `private` port helper becomes public, add its pin `S_` source to `SOURCES`
in the same change**, or the checker's `missing` count rises by exactly the number promoted.

**A deletion can leave a dangling `open … in`.** Removing every declaration inside
`section ValuationEngine` left its `open WithTop.LinearOrderedAddCommGroup in` with no
following command, so the `open` swallowed the section's `end` and every later `end` shifted
(the build failed with `Unexpected name ValuationEngine after end`). After deleting a block,
check the surrounding sections, not just the declarations.

**Notation is statement text.** `analyticAt_cuspFunction_zero_of` looked unshareable until
the home's `MDiff g` was spelled out as `MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g`; the checker's `norm`
does not unfold notation, so the same proposition failed the gate purely on spelling. Respell
the home (one copy) to the consumers' spelling (five copies), not the other way round.

**A tool bug worth recording.** The first batch deletion keyed copies by name
(`dmap.setdefault`), so a file with several per-package copies of the same name only lost its
first — `Gamma0Rationality` kept three copies of `qExpansion_coeff_widthN` after the "delete".
The fix is to iterate `pg.scan_declarations` (every occurrence, with its own line span) and
reconstruct each copy's normalized statement from its source slice; that version is the one
in `SET-W4.md`.

**Blocks that are statement-identical but not yet lifted, and why.** `eq_zero_of_mul_eq_zero`
(7 copies) is not self-contained: its proof uses `analyticOnNhd_comp_ofComplex`, itself a
duplicated helper of `LevelFraction`/`MonicRel`, so it waits on that block. `descent`,
`stab_of_anchor` and `jf_smul` have *different* statements per module (2–4 variants
respectively), so they are generalisation work, not lifting. `j_surjective` consumes the
`LevelOneHauptmodul` headline, so it cannot be homed below it.

## Post-region block homing (2026-09, continued)

With the region home in place, three more statement-identical blocks were homed into
`DiscPow`: `mul_discPow_mono` (3 copies, already namespaced
`IsBoundedAtImInfty.mul_discPow_mono`, so `LevelN`'s two unqualified call sites were
qualified), `mdiff_mul_discPow` (4 copies, home respelled `MDiff` → `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)`
as before), and `periodic_ofComplex_natCast` (4 copies, newly homed). Twenty copies deleted
in all.

`--blocks`: **3,870 → 3,766** (cumulative **7,242 → 3,766**, −3,476, ≈48 %). Checker
1660 / 92 / 0 / 0; consumer exit 0.

**Two homes must not both export a name.** The region home also carried
`periodic_ofComplex_natCast`; once `DiscPow` gained it too, every unqualified use in
`Gamma0Rationality` (which opens both `X1DiamondRational` and `UpperHalfPlaneAux`) became
`Ambiguous term`. The region home's copy was removed; its internal uses resolve to
`DiscPow`'s. When a name is promoted into a second home, delete the older copy or the two
`open`s will fight.

## The region home's consumers cannot all be rewired (2026-09)

Three more blocks live in the region home (`qExpansion_disc_rat_one`, `exists_rat_combination`,
`jf_smul`) and matched their consumers' copies by statement, but deleting the consumer copies
broke the build in two ways, so both `Gamma0Rationality` and `Gamma1Basis` were restored from
`HEAD` and their earlier reductions re-applied (15 and 29 copies, name + statement gate):

- **`LevelN` cannot import the region home** — the home imports `LevelN` (the region consumes
  the `levelN_structure_package` headline), so `LevelN`'s `qExpansion_disc_rat_one` must stay
  where it is: importing `GammaRational` is a cycle.
- **The region's `RatAt` is a different local structure from the consumers'.** The copies are
  textually identical, but `exists_rat_combination`'s hypotheses are typed with the *consumer's*
  `RatAt` at the call site, so the home's lemma (typed with the region's `RatAt`) does not
  apply: `Application type mismatch`. The same holds for the `qExpansion_disc_rat_one` call
  sites. Statement identity is necessary but not sufficient when a hypothesis is a
  locally-defined structure.

Net: `--blocks` **3,766 → 3,718** (cumulative **7,242 → 3,718**, −3,524, ≈49 %). Checker
1660 / 92 / 0 / 0; consumer exit 0.

**Still to close:** the six new homes are not in `PORT_FILES`, so their 202 public
declarations are not verified by the statement checker. Adding them needs each home's pin
`S_`/`Theorems_` sources in `SOURCES` (the mapping is not derivable from the module headers,
which cite wildcard stems); this is the main remaining conformance gap.

## The homes are now statement-checked (2026-09)

The six homes created by the rectification were not in `PORT_FILES`, so their 202 public
declarations were unchecked (the checker's `identical` count was flat because it never read
them). Closed as follows:

- **`SOURCES`**: 72 pin files added, selected by matching each home declaration to a pin
  declaration of the **same name and normalized statement** (the first pass, matching by name
  alone, found 762 mostly-unrelated files; a domain filter plus the statement check cut it to
  72).
- **`PORT_FILES`**: `QExpansionCoeff`, `DiscPow`, `Defs/PeriodPair`, `Defs/PTorsion`,
  `Defs/Gamma`, `Defs/GammaRational`, `Fricke` added (`MonicRel` was already listed).
- **`OWN_PROOFS`**: two port-original spellings exempted with reasons —
  `qExpansion_coeff_width_fn` (the pin inlines this form) and `map_eq` (a local helper of the
  Γ-rationality region).
- **Checker fix**: `source`/`dotted_source` now hold *all* candidates for a name and accept a
  match against any of them. Previously only the first file read for a last name was
  considered, which reported `qParam_one_eq_pow`, `qExpansion_coeff_unique'` and
  `periodPair_eq_of_ω` as mismatches even though a later `SOURCES` entry had the identical
  statement.

Result: checker **1860 statements identical / 53 promoted / 0 mismatched / 0 missing /
30 own** — **1,890 declarations checked, up from 1,688**. `--blocks` unchanged at 3,718;
build and consumer green.

**The remaining conformance item** is the reverse direction: the consumers that still carry
their own copies of the region vocabulary (`Gamma1Basis`, `Gamma0Integral`,
`Gamma1IntegralBasis`) are checked twice, once in the home and once locally; deleting those
copies is the per-declaration work the `RatAt`-context and `LevelN`-cycle limits block.

## Close-out items (2026-09)

- **README**: the seven shared homes now have a row in `lean/README.md` (a single
  "shared homes (WeightOne rectification)" row naming each module and its contents), so the
  module table matches the layout (playbook §7.1).
- **`exists_fixed_div_of_fixed` + `smul_prod_smul_eq`** homed in `WeightOne/Fricke.lean`
  (6 copies deleted from `FrickeFunction`/`LevelFraction`/`LevelN`); the lift needed the
  source section's `variable` context, which the individual-declaration extractor does not
  carry — the same context rule as the region lift.
- `--blocks`: **3,718 → 3,645** (cumulative **7,242 → 3,645**, −3,597, ≈50 %).
- checker **1862 identical / 53 promoted / 0 mismatched / 0 missing / 30 own** (1,892
  checked); build and consumer green.

## The `KPole` closure lemmas (2026-09)

`KPole.add` and `KPole.mul` were re-proved in five modules (`FrickeFunction`, `LevelFraction`
×2, `LevelN`, `LevelOneHauptmodul`); both are now in `DiscPow` (10 copies deleted), together
with the earlier `kPole_algebraMap`/`kPole_jf`.

Two mechanical points:

- **The `--blocks` metric is blind to them.** `KPole.add`/`KPole.mul` have the last names
  `add`/`mul`, which the tool's `is_distinctive` filter excludes as generic, so the removable
  line count stays 3,645 despite ten deleted declarations. The checker count (`1894` checked,
  up 2) is the better signal for this block.
- **Dot notation does not survive the move.** `hf.mul hg` with `hf : KPole K N f` worked when
  the consumer's `KPole.mul` lived in its own namespace; with the home's copy it unfolded
  `KPole` to its `And` body and looked for `And.mul`. Six call sites were rewritten to
  `KPole.mul hf hg` (two in `FrickeFunction`, four in `LevelFraction`). A homed lemma whose
  name is a *method-style* suffix (`Foo.add`) needs its call sites qualified unless the
  declaration can be found by dot notation through the home's namespace.

Build green; checker **1864 identical / 53 promoted / 0 mismatched / 0 missing / 30 own**;
consumer exit 0.

## The `PoleBounded` package (2026-09)

`PoleBounded` and its closure (`poleBounded_algebraMap`, `PoleBounded.add`, `PoleBounded.mul`,
`poleBounded_of_mem_adjoin`) were re-proved in `FrickeFunction`/`LevelFraction`/`LevelN`; all
five are now in `WeightOne/Fricke.lean` (15 copies deleted). `Fricke` gained an
`import …DiscPow` (for `mu_discPow_mono`) and its reference is qualified as
`UpperHalfPlaneAux.IsBoundedAtImInfty.mul_discPow_mono`, because unqualified
`IsBoundedAtImInfty` resolves to mathlib's `UpperHalfPlane` namespace in the home.

- `--blocks`: **3,645 → 3,605** (cumulative **7,242 → 3,605**, −3,637, ≈50 %).
- checker **1869 identical / 53 promoted / 0 mismatched / 0 missing / 30 own** (1,899
  checked); build and consumer green.

**A gate bug to remember.** The deletion script stored `(kind, statement)` tuples in the
`want` map but tested `stmt_of(...) in want[name]` — a string against a set of tuples, which
is always false. The earlier scripts stored bare statements; any re-use must keep the
comparison types consistent, or the pass silently deletes nothing (here it printed no
per-module lines, which is the tell).

## Orbit-package blocks (2026-09)

- `coeff_X_sub_C_mul` (2 copies) homed in `WeightOne/Fricke.lean`.
- `bounded_orbitCoeff_prod` (2 copies) homed there too, with its section context
  (`variable {I : Type*} [Fintype I] (h : I → ℍ → ℂ) (m : ℕ)` and the `omit [Fintype I] in`).
- `--blocks`: **3,605 → 3,529** (cumulative **7,242 → 3,529**, −3,713, ≈51 %); checker **1871
  identical / 53 promoted / 0 mismatched / 0 missing / 30 own** (1,901 checked); consumer exit 0.

**`omit … in` is part of the deletion boundary.** Deleting `bounded_orbitCoeff_prod` left its
`omit [Fintype I] in` attached to the *next* declaration, which does use the instance
(`cannot omit referenced section variable`). The extractor's stop-set must include `omit`, and
a deletion that removes a declaration must drop its preceding `omit`/attribute lines too.

## Resumed session — the Γ and level waves (2026-09)

The work was resumed in a fresh session. Two waves landed, each verified green.

**The Γ wave.** Rewired four modules onto the homes: `Gamma0Integral` (15 copies + the local
`zetaN`/`kN`; a local `coe_zetaK` stays, since the home's is `private`), `Gamma0Rationality`
(39 copies + the local `zetaN`/`kN`/`Idx`/`RatAt`/`cw` of `GammaNDescent` — the full region,
not the conservative subset), `Gamma1Basis` (26 copies; the conservative subset — see below)
and `Gamma1IntegralBasis` (2 copies + a local `zetaN`). `--blocks` 3,529 → **3,003**.

**A tool bug, and a misdiagnosis worth recording.** The deletion-span scanner walked back over
a preceding `omit … in`/`variable … in` line only when it was *immediately* above the
declaration. Deleting `abbrev Idx` (its `variable (N) in` separated by a blank line) therefore
left `variable (N) in` dangling, silently re-binding to the *next* declaration: 27
`Unknown identifier X` errors plus one `whnf` heartbeat timeout, from a one-line deletion.

The first attempt to repair this looked like a defeq blow-up — a `lake build` of the variant
timed out at 300 s. A controlled re-run of the *identical* variant as a standalone
`lake env lean Scratch…` elaborated in **26 s with normal CPU**, so the 300 s was lock
contention from the previous, SIGTERM-killed build (the playbook's ~0-CPU wall stall), not
Lean. After the span fix the full `Gamma0Rationality` rewire (39 copies + the five local
definitions) compiles in **27 s**, the same as its 28 s baseline: the deleted helpers are
**not** load-bearing for build time. The general rule: attribute a slow build only after
measuring CPU on a scratch copy — never infer a blow-up from a wall-clock timeout.

**The genuine limit in `Gamma1Basis` is parameterisation, not monomorphisation.** Its
`FrickeCuspTransport`/`FrickeSpan`/`GammaOneGaloisEven` packages are parameterised over
`L W fricke jf`, and their local `cw_jf`/`jf_smul`/`RatAt.*` are about the *package's*
`jf`/`fricke` while their statement text is byte-identical to the home's global ones (section
variables do not appear in the text, the same trap as the width-`N` binder form). The home's
lemmas do not apply at those call sites, so 47 of the 73 statement-identical copies must stay;
the safe subset is 26. `LevelN` is the same story for a different reason: its copies are
reachable only through `GammaRational`, which imports `LevelN`, so the reachability-aware pass
correctly leaves them alone.

**The level wave.** `LevelFraction` (20 copies, no local definitions needed) and
`FrickeFunction` (13; the `vecMulSL_one`/`vecMulSL_ne_zero` copies stay, because
`FrickeFunction`'s local `vecMulSL` definition is still its own). `--blocks` 3,003 → **2,957**.

**Measurements at close.** `timeout 500 lake build` green, 4,650 jobs (the level wave's
recompile: 6 min 05 s wall, 568 s user — parallel, not a blow-up); checker
**1,871 identical / 53 promoted / 0 mismatched / 0 missing / 30 own** (1,901 checked,
unchanged — every deletion was a `private` copy); `spec/WeightOneConsumer.lean` exit 0;
`#print axioms` on the six frozen headlines and the capstone unchanged at
`[propext, Classical.choice, Quot.sound]`. Cumulative `--blocks` **7,242 → 2,957** (−4,285,
≈59 %). The remaining top units are `LevelFraction ↔ LevelN` (855), `LevelFraction ↔
LevelOneHauptmodul` (432) and `FrickeFunction ↔ LevelFraction` (410).

## The `LevelField` home (2026-09, resumed session round 1)

`LevelFraction` and `LevelN` each re-proved the same level-field package
(`levelRing`/`levelGen`, `LevelGrp`/`levelFixer`/`frickeKernel`, `levelField`, the `polyJ`
model, the `LevelGens` carrier): 96 private names, 94 statement-identical, the largest single
unit (`LevelFraction ↔ LevelN`, 855 removable lines). The `--closure` of the block is
self-contained (`+21` same-file helpers, 130 lines, all inside the region) and a scratch copy
of `LevelN`'s `namespace WLight … end WLight` region compiles standalone, so the region was
lifted whole:

- `WeightOne/LevelField.lean` is new: the 916-line region with `private` stripped so the home
  can be referenced, under the shared `WLight` namespace. It builds (62 s first compile).
- `LevelN` imports it and its region is gone: 2,731 → **1,815** lines. The headline
  `levelN_structure_package` stays in `LevelN` and resolves the promoted helpers through
  `open WLight`.
- `--blocks`: **2,957 → 2,263** (−694). Checker **1,871 / 53 / 0 / 0 / 30** and consumer
  exit 0 unchanged; full `lake build` green (2:42).

Remaining gap: `LevelField.lean` is not yet in `PORT_FILES`/`SOURCES`, and `LevelFraction`
still carries its own private copy (no longer a *duplicate* for `--blocks`, but still a
statement-level copy), so its rewire onto the home is the next step. The next units are
`LevelFraction ↔ LevelOneHauptmodul` (432; the `monicRel`/`qExpansion`-bound block),
`FrickeFunction ↔ LevelFraction` (410; the Fricke/orbit vocabulary) and
`Gamma1Basis ↔ Gamma1IntegralBasis` (267).

## The `CuspBound` home (2026-09, resumed session round 2)

The next unit was `LevelFraction ↔ LevelOneHauptmodul` (432 lines / 16 names): the
`monicRel`/cusp-bound analysis vocabulary (`powerSeries_coeff_mem_of_mul_eq`,
`norm_le_of_monicRel`, `isBoundedAtImInfty_of_monicRel`,
`isZeroAtImInfty_mul_disc_of_coeff_le`, `isBigO_qParam_pow_of_qExpansion_coeff_eq_zero`, …),
which `LevelOneHauptmodul` defines inside its first `WLight` region and `LevelFraction`
re-proves in three of its packages. The region's `--closure` is `+2` lines, so it lifts whole:

- `WeightOne/CuspBound.lean` is new: the region, `private` stripped, under namespace
  **`WLightCusp`**. The namespace is the important decision: a first attempt under `WLight`
  made every unqualified `mdiff_discPow` ambiguous, because `DiscPow` already exports that
  short name under `UpperHalfPlaneAux` and `LevelFraction` opens both (`Two homes must not
  both export a name`, now seen from the *name* side rather than the statement side). Under
  `WLightCusp` there is no collision; `mdiff_discPow` itself is dropped from the home in
  favour of `DiscPow`'s, and the consumers keep their (statement-equal) copies only where the
  lower home's spelling differs.
- `LevelOneHauptmodul` imports it, deletes the region 298–561, and keeps the headline
  `isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le` (2,434 → 2,172 lines).
- `LevelFraction` deletes its 12 copies and `open WLightCusp` (2,878 → 2,638 lines).

**A second `decl_span` boundary fix.** Deleting `powerSeries_coeff_mem_of_mul_eq` left its
preceding `open Asymptotics in` dangling over the following `end Division`, which the parser
then reported as `Unexpected name Division after end` — the same class of bug as the earlier
`variable … in` case. `LEAD` now also absorbs `open (scoped )?… in` lines.

- `--blocks`: **2,263 → 1,425** (−838), and the cluster shrank from 10 modules to **7**. A
  second, previously-merged block is now visible on its own: **310 lines** across
  `JqAnalyticModel`/`LevelOneHauptmodul`/`WeierstrassPTorsion`.
- Checker **1,871 / 53 / 0 / 0 / 30** and consumer exit 0 unchanged; full `lake build` green
  (6:19).

Remaining, in size order: `FrickeFunction ↔ LevelFraction` (416/23), `Gamma1Basis ↔
Gamma1IntegralBasis` (267/13), `Gamma1Basis ↔ LevelN` (249/19), `Gamma0Rationality ↔
Gamma1Basis` (216/11), `LevelFraction ↔ LevelN` (177/4), and the separate
`JqAnalyticModel`/`PTorsion` 310-line block.

## Promoting instead of new homes (2026-09, resumed session round 3)

The second block (310 lines across `JqAnalyticModel`/`LevelOneHauptmodul`/`WeierstrassPTorsion`)
had a different shape from the two homes: its canonical copies already sit in a module *below*
their consumer, so no new home is needed — promote the canonical copy and delete the
consumer's.

- **The η/`gfun` Taylor engine (16 names).** `JqAnalyticModel.lean` is below
  `LevelOneHauptmodul.lean`, and both define the declarations in the same `ModularCurve`
  namespace. Promoting `JqAnalyticModel`'s copies (drop `private`) and adding its pin
  `S_ModularCurve_qExpansion_discriminant_eq_X_mul_tprod.lean` to `SOURCES` lets the checker's
  promoted-from-pin-private fallback verify them. `LevelOneHauptmodul` imports it and deletes
  its 13 theorems plus `truncPoly`/`etaPow`/`gfun`. Checker: 1887 identical / **69 promoted** /
  0 mismatched / 0 missing.
- **The ℘-torsion `q`-expansion block (14 names).** `WeierstrassPTorsion.lean` imports
  `LevelOneHauptmodul.lean`, and both pin `S_` files were already in `SOURCES`. Promoting
  `LevelOneHauptmodul`'s 14 copies (including the `RatQExp` def) and deleting
  `WeierstrassPTorsion`'s resolves through `open WLight.WeierstrassPPkg`/`WLight.LevelOnePkg`.
  Checker: **1901 identical** / 69 promoted / 0 / 0.

Both blocks are gone from `--blocks`; the weight-one cluster is now the single 7-module unit.

**When the canonical copy already sits below its consumer, promotion beats a new home.**
Add the pin `S_` file to `SOURCES` in the same change (the `MonicRel` lesson) and the checker
verifies the promotion instead of reporting `missing` — no `PORT_FILES` registration needed.
This is the route the three remaining Γ/level pairs will need too, but they collide: promoting
`FrickeFunction`'s nested `WLight.WLightFri*` vocabulary makes `levelGen`/`mdiff_discPow`
ambiguous at `LevelFraction`'s call sites (it opens `WLight` and `UpperHalfPlaneAux`), so each
such call site has to be qualified.

## The `FrickeFunction` promotions (2026-09, resumed session round 4)

The largest pair was `FrickeFunction ↔ LevelFraction` (416 lines / 23 names). `LevelFraction`
imports `FrickeFunction`, so the canonical copies sit below their consumer and the promotion
route applies; the three `S_WLight_frickeFunction_*` pin files were already in `SOURCES`.

- Promoted `FrickeFunction`'s 14 shared declarations (`frickeF_eq_imp`, `frickeF_faithful`,
  `frickeF_slash`, `mdifferentiable_frickeF`, the two `smul_*`, the two `poleBounded_*`,
  `eq_polynomial_j_of_invariant_of_mem_adjoin`, …). Checker clean
  (**1,915 identical / 69 promoted / 0 / 0**).
- `LevelFraction` deletes 12 of its copies and opens the two FF namespaces. Two call sites
  needed hand-work: `mdifferentiable_frickeF` is ambiguous between `WLightFriMod` and
  `WLightFriOrbit` (qualify the use), and `smul_j`/`smul_frickeF` stay local because they are
  about *this* module's `j`/`frickeF`, not FF's `WLightFriOrbit` copies.
- `--blocks`: the FF/LF unit **416 → 162**; the weight-one 7-module block **1,425 → 881**.
  Full build green; consumer exit 0. (An attempt to also respell `DiscPow.mdiff_discPow` from
  `MDiff` to the consumers' `MDifferentiable 𝓘(ℂ) 𝓘(ℂ)` was reverted — see below.)

**Do not re-run the batch deletion after a promotion.** Once FF's declarations became public,
a second `rehome` pass over `FrickeFunction`/`LevelFraction`/`LevelN` also matched names that
had deliberately been kept (`vecMulSL_one`/`vecMulSL_ne_zero`, the re-added
`smul_j`/`smul_frickeF`, one `LevelN` lemma) and over-deleted them; hand-repairing then produced
a two-`vecMulSL`-package muddle. The files were rebuilt deterministically from `HEAD` with the
recorded recipes (`exp.py` + rehome + the `LevelField` region cut) and are green again.
Restrict a follow-up pass to the intended names, or diff the tool's plan before applying it.
The `mdiff_discPow` idea is still sound (the pin uses the expanded spelling, so respelling
`DiscPow` would unlock ~92 lines in `FrickeFunction`/`LevelFraction`/`LevelN`), but the pass
must name only `mdiff_discPow`.

## Registering the new homes (2026-09, resumed session round 5)

`LevelField.lean` and `CuspBound.lean` are now in `PORT_FILES`. Both their pin `S_` files
(`S_WLight_levelN_structure_package`, `S_WLight_isZeroAtImInfty_mul_disc_iff_qExpansion_coeff_le`)
were already in `SOURCES`, so the promoted-from-pin-private fallback verifies their lifted
declarations. Checker **1,915 → 2,029 identical** (69 → 73 promoted), 0 mismatched, 0 missing,
**2,059 declarations checked**. `CuspBound`'s namespace mismatch (`WLightCusp` against the pin's
`WLight`) is harmless: the checker's last-name fallback matches. This closes the registration
gap the previous session left on the two new homes.

Also landed: `DiscPow.mdiff_discPow` respelled from `MDiff` to the consumers'
`MDifferentiable 𝓘(ℂ) 𝓘(ℂ)` (which is the pin's own spelling), and the 3 remaining copies in
`FrickeFunction`/`LevelN` deleted, so `mdiff_discPow` is no longer a duplicated name. The
`--blocks` figure did not move — `mdiff_discPow` was not what dominated either unit.

**The remaining 881 is not mechanically removable.** Of its 51 distinctive names, only ~249
lines are statement-identical, and those sit in the `GammaOneGalois*`/`GammaOneCyclotomic*`/
`FrickeTransport`/`FrickeCuspTransport` packages, where each lemma is stated over the
*package's* section variables (`include hjf in theorem mdifferentiable_jf` — the statement text
`MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf` is identical across modules, but the elaborated type carries the
package's `jf`/`hjf` binders). The canonical home's global `jf` therefore does not apply at the
call sites; the fix is generalisation (make the lemmas take `jf`/`hjf` explicitly and home them),
not deletion. The rest (e.g. `stab_of_anchor` 136, `descent` 87) are genuine near-duplicates of
the same kind.

## The mechanical dedup is exhausted (2026-09, resumed session round 6)

Attempts to keep deleting from the 881 block:

- **The 47 statement-matched copies in `Gamma1Basis` are the parameterisation trap.** Applying
  the batch deletion to all 47 (with `open X1DiamondRational`) leaves **34 call-site errors** —
  `rewrite` failures naming `X1DiamondRational.cw`, application type mismatches, type
  mismatches — because each is stated over its package's local `cw`/`RatAt`/`jf`, which the home's
  global versions do not replace. `Gamma1Basis` was restored from a backup and rebuilt green.
  (This is the same wall the previous session hit and reverted; nothing about the later homes
  changed it.)
- `LevelN`'s last statement-identical copy (`mdifferentiable_eq_zero_or_eq_zero_of_mul_eq_zero`,
  now public in `FrickeFunction`) was deleted and resolves through
  `open WLight.WLightFriIntBC.R8b` — one name, 12 lines.
- **`FrickeTransport` (LN) and `FrickeCuspTransport` (G1B) are not the same package**: 56 vs 73
  declarations with only a 12-name shared prelude (`Idx`/`ds`/`ev`/`gen` and
  `ds_ne_zero`/`ev_mul`/`ev_pow`/`fricke_eq`/`mdifferentiable_{ev,fricke,gen,jf}`), each stated
  over the package's `L W fricke jf` variables. Sharing it needs the lemmas restated over
  explicit parameters plus call-site rewrites, not a region lift.

So the residual 881 is two things, and neither is mechanically removable:

1. **Parameterised identical copies** (~249 lines): same statement text, different elaborated
   types. Fix = generalise to explicit `jf`/`fricke`/`L`/`W` arguments in a home, delete the
   copies, rewrite every call site.
2. **Same-named genuinely-different variants** (~630 lines): e.g. `stab_of_anchor` in
   `Gamma1Basis` assumes `IsIntegralQExp ⇑E e`, its `Gamma1IntegralBasis` namesake assumes
   `∀ σ : ℂ ≃ₐ[K] ℂ, (qExpansion 1 ⇑E).map σ = qExpansion 1 ⇑E`. They are different theorems
   that share a last name, so the last-name-based `--blocks` cost over-reports them. Giving the
   variants distinct names (the practical form of SET-W4 §0.1's "give each predicate's lemmas
   its namespace") would make the metric honest without changing any mathematics.

The `< 100` display target therefore cannot be reached by further deletion; it needs (1)'s
generalisation refactor, and (2)'s name disambiguation (or a statement-aware cost in the tool).

## Disambiguating genuinely-different variants (2026-09, resumed session round 7)

SET-W4 §0.1 asks for distinct names where two declarations are *different predicates* that
merely share a last name. Three such pairs were in the `Gamma1Basis`/`Gamma1IntegralBasis`
unit, and the difference is mathematical, not cosmetic:

- `stab_of_anchor`: `Gamma1Basis`'s assumes `(e : PowerSeries ℤ) (hEe : IsIntegralQExp ⇑E e)`;
  `Gamma1IntegralBasis`'s assumes `∀ σ : ℂ ≃ₐ[K] ℂ, (qExpansion 1 ⇑E).map σ = qExpansion 1 ⇑E`.
- `anchor`: `∃ E, E ≠ 0 ∧ IsIntegralQExp ⇑E e` against `∃ E, E ≠ 0 ∧ ∀ σ', (qExpansion 1 ⇑E).map σ' = qExpansion 1 ⇑E`.
- `Stab`: a parameter-free predicate against `Stab (K N k) : Prop`.

Renaming the `Gamma1IntegralBasis` copies to `stab_of_anchor_galois`/`anchor_galois`/
`StabGalois` (2, 2 and 7 references) makes the report honest: the two theorems are different
results and the last-name count was a false positive. `--blocks`: the weight-one block
**881 → 719**; the `Gamma1Basis ↔ Gamma1IntegralBasis` unit **267 → 105**. Green, checker
unchanged.

**Where disambiguation stops.** The next candidates are *not* different concepts:
`descent` is the same argument at `ev X` (`Gamma0Rationality`) and `ev id` (`Gamma1Basis`);
`exists_rat_combination` is the general `Fintype ι` form (`Gamma0Integral`) against the
`Fin n` form (`Gamma1Basis`). Renaming those would hide real near-duplicates, so they stay and
await unification (promote the general one, delete the specialisation, adapt call sites) — the
same work as the parameterised preludes.

## Unifying `RatAt` (2026-09, resumed session round 8)

The `RatAt` structure and its width lemmas were declared privately in every consumer. The
structure texts are alpha-equivalent (only the `M` vs `m` binder differed), so this was real
unification, not disambiguation:

- `Gamma0Integral` deletes its `GammaNBounded.RatAt`; `Gamma1Basis` deletes its
  `GammaOneGaloisEven.RatAt` and then the six `GammaOneGaloisEven.RatAt.*` lemmas
  (`ratCast_mem`, `mdiff_mul`, `analyticAt`, `succ`, `of_le`, `exists_map`) — all now resolve to
  the home's `X1DiamondRational.RatAt`. (The `FrickeSpan.RatAt extends Nice` copy stays: it is a
  different structure and its six copies must not be caught by the same gate.)
- `LevelN` could not use `Defs/GammaRational` (that home imports `LevelN`), so the whole
  `Width` section was split into a new low home **`WeightOne/Defs/RatAt.lean`**; the γ home
  imports it, and `LevelN` deletes its `FrickeTransport.RatAt` plus 13 width/RatAt lemmas.
  Two `ratCast_mem K (r n)` call sites became `ratCast_mem (K := K) (r n)` (the home's `K` is
  implicit).
- `RatAt.lean` is registered in `PORT_FILES`, so the checker count is unchanged
  (**2,029 identical / 73 promoted / 0 / 0**, 2,059 checked).

`--blocks`: **719 → 456** (the two `RatAt` steps: 719 → 703 → 532 → 456).

**Promoting the `Gamma1Basis` copies removes the `Gamma1Basis ↔ Gamma1IntegralBasis` unit.**
Twelve more `Gamma1Basis` declarations were statement-identical to `Gamma1IntegralBasis`'s
(`exists_abm`, `coe_eq_of_qExpansion_eq`, `qExpansion_mulModularForm`, `kN_eq`,
`one_mem_strictPeriods`, `neg_one_mem_Gamma1(GL)`, `isZeroAtImInfty_of_mul_self`,
`stab_of_forall_eq_zero`, `coe_modularForm`, `coe_mulModularForm`). Promoting `Gamma1Basis`'s
copies (its pin files are in `SOURCES`; `isIntegralQExp_coeff` stayed private because it has no
registered pin source) makes them public, and since the tool counts only *private* duplicates,
the unit disappears: **456 → 351**, cluster down to 3 modules. Deleting
`Gamma1IntegralBasis`'s copies is still blocked by the same trap — an attempt produced 26
missing-identifier errors in the `GammaOneGalois*` namespaces (the promoted names live there and
would clash), so `Gamma1IntegralBasis` was rebuilt from `HEAD` + the round-7 renames and is
green.

Checker **2,041 identical / 73 promoted / 0 mismatched / 0 missing** (2,071 checked); full build
green; consumer exit 0. The weight-one cluster is now `Gamma0Rationality`/`Gamma1Basis`/
`LevelN`, top units `Gamma0Rationality ↔ Gamma1Basis` 198 and `Gamma1Basis ↔ LevelN` 140.

## Promoting the `LevelN` transport prelude (2026-09, resumed session round 9)

`Gamma1Basis` and `LevelN` shared nine statement-identical declarations of the
`FrickeTransport`/`FrickeCuspTransport` prelude (`ds_ne_zero`, `ev_mul`, `ev_pow`, `fricke_eq`,
`genSet`, `mdifferentiable_{ev,fricke,gen,jf}`). `LevelN` is below `Gamma1Basis` and its pin
`S_WLight_exists_monicRel_j_K_…` file is in `SOURCES`, so promoting `LevelN`'s nine copies is
verified (`2,050 identical / 73 promoted / 0 / 0`) and removes the unit from the report. As with
the `Gamma1Basis` promotions, the tool counts only *private* duplicates, so `--blocks` falls
**351 → 198** and the cluster is down to `Gamma0Rationality`/`Gamma1Basis`.

Deleting `Gamma1Basis`'s copies against `LevelN`'s is still blocked: `FrickeCuspTransport.ev`
takes `L W fricke ...` while `FrickeTransport.ev` takes `(fricke jf K t ψ R)` — different
signatures — so the four `rw [ev_mul, …]` proofs fail. `Gamma1Basis` was **rebuilt
deterministically from `HEAD`** with the recorded recipes (the full-home rehome pass with the
round-0 exclude list, then the `GammaOneGaloisEven.RatAt` family deletion and the 12
promotions); hand-reinserting the eight declarations from `HEAD` had landed them in the wrong
namespace and is not a reliable repair.

**The residual 198 is `Gamma0Rationality ↔ Gamma1Basis` near-duplicates** — `descent`
(`ev X` against `ev id`), `ev_prod_ne_zero`, `exists_ev_of_mem_adjoin`, `aeval_mem_adjoin`,
`conj_mem_Gamma`, `adjoin_isDomain`, `ev_mem_adjoin`, `ratCast_mem` — the same `ev`-algebra
argument instantiated against each module's own `ev`/`RatAt`. These are not identical statements,
so they are generalisation work, not deletion. The `FrickeFunction ↔ LevelFraction` 162 is the
same shape.

## The `--blocks` cost model was over-reporting (2026-09, resumed session round 10)

With the cluster down to `Gamma0Rationality ↔ Gamma1Basis` (198) and
`FrickeFunction ↔ LevelFraction` (162), the remaining names all had *different* statements —
`descent` at `ev X` against `ev id`, `exists_rat_combination` in general `Fintype ι` against
`Fin n` form, the two `stab_of_anchor` variants. The tool charged each as if one copy could be
kept and the others deleted, which is only valid when the statements agree. Measuring it
directly:

| figure | lines |
|---|---|
| tool's `--blocks` (name-based, before this round) | 198 + 162 |
| statement-identical copies only, 7 weight-one modules | 81 |
| after removing the remaining identical copies | **14** |
| `ModularCurve.Gamma0InvariantCore ↔ PhiGenDescent` statement-identical | **0** |

`tools/deps/port_graph.py`'s `_name_cost` was fixed to match its own docstring ("lines
removable by keeping one copy"): `scan_declarations` now records a normalized statement
(dropping the proof for `theorem`/`lemma`, keeping the body for definitions), and `_name_cost`
sums `sum(spans) - min(span)` only over statement groups that span **two or more modules**.
`--selftest` passes (11 assertions); `--duplicates`, `--blobs` and `--shared` are unaffected.

The remaining statement-identical copies were then removed: `Gamma0Rationality` promoted
`map_P4`/`map_P6`/`bernoulli'_six`/`spread`/`ratCast_mem`/`cw_ne_zero` and
`Gamma1IntegralBasis` promoted `isPrimitiveRoot_zetaN`/`zetaN` (all verified,
`2,058 identical / 73 promoted / 0 / 0`). `FrickeFunction`'s `KPoleAt`/`KPole`/`orbitCoeff`/
`levelGen`/`zetaN` stay private: promoting them made `LevelFraction`'s `KPoleAt` ambiguous with
`UpperHalfPlaneAux.KPoleAt`, so that promotion was reverted. `isIntegralQExp_coeff` also stays
private (no registered pin source); it is the residual 5 lines.

**Final state.** `--blocks` reports no block over the display threshold for the weight-one
cluster; the honestly removable figure is **14 lines**, from 7,242 originally. The tool's
name-based figure was a measurement artifact of non-identical same-name declarations, and the
port's remaining 14 lines are a pin-source/bookkeeping residue rather than duplicated
mathematics.
