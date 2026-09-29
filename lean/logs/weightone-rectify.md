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
