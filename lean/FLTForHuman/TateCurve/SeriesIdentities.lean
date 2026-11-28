/-
  The convergence and `q`-multiplication identities of the Tate curve's point series.

  Twelve identities of the `q`-series layer of the Tate curve (seven landed by AF106, three more by
  AF107H — the three `*_zpow_mul`/`sOne_*` rows — and two more by AF108E, the two `*_normalForm` rows
  at the end of this list):

  * `hasSum_xfun`, `hasSum_yfun`: the two rational functions `xfun w = w / (1 - w)²` and
    `yfun w = w² / (1 - w)³` are the sums of their geometric-type expansions in `w`;
  * `nodal_xfun_yfun`: `yfun² + xfun · yfun = xfun³` — the two series lie on the nodal cubic
    `y² + xy = x³`;
  * `pointX_q_mul`, `pointY_q_mul`: the point coordinates are invariant under `u ↦ q * u`, which is
    the Tate curve's own `q`-periodicity;
  * `tsum_succ_prod_eq_tsum_divisors`: the double `tsum` over `ℕ × ℕ` collapses to a single `tsum`
    over the divisor sums (`N + 1`'s divisors), the Lambert-type regrouping the `coeffSum` layer
    uses;
  * `exists_zpow_mul_mem_annulus`: every `u ≠ 0` is carried into the norm-`< 1` annulus
    (`‖q * (q ^ n * u)‖ < 1` and the same for the inverse) by a power of `q`;
  * `sOne_eq_tsum_xfun`: `s₁ q = ∑' n, xfun (q ^ (n + 1))` — the Lambert series `s₁` is the row sum
    of the `xfun` expansion, by the `ℕ × ℕ` double-sum regrouping;
  * `pointX_zpow_mul`, `pointY_zpow_mul`: the `q`-periodicity of `pointX`/`pointY` for every integer
    power, `pointX q (q ^ n * u) = pointX q u` — the stated input of the deferred
    torsion-parametrisation layer (CARRY-FORWARD), statements kept exactly;
  * `pointX_normalForm`, `pointY_normalForm`: the two coordinates as one `u`-term plus a `tsum` over the
    positive powers of `q`,
    `pointX q u = xfun u + ∑' n, (xfun (q ^ (n+1) * u) + xfun (q ^ (n+1) * u⁻¹) - 2 * xfun (q ^ (n+1)))`
    (and the `y`-analogue) — the normal forms the point-arithmetic layer starts from, the first step of
    SET-AF101's torsion-parametrisation dossier (CARRY-FORWARD).

  Transcribed from the ten pins below (pinned `aa2d8b3`, 157 + 69 + 22 + 19 + 19 + 17 + 17 lines for
  AF106's seven, then 101 + 22 + 22 for AF107H's three), whose names and statements are the pins' (no
  shared engine).

  Assumes `TateCurve/QSeries.lean` and `TateCurve/PointSeries.lean` (`xfun`, `yfun`, `pointX`,
  `pointY`, the term series and their summability).

  Engine notes (the pin's `private` rows, 30 `S_` rows in all: 10 public + 20 private):

  * the `ℕ × ℕ` regrouping is `section GeneralRegrouping` (pin `S_TateCurve_tsum_succ_prod_eq_tsum_divisors`,
    nine private rows); the pin's private `tsum_succ_prod_main` is kept as the pin has it, so its
    statement is the headline's — the pin's own pair, recorded here per the `dedup` gate;
  * the annulus pin's private engine is `nnnorm_lt_one_iff_norm` + `exists_zpow_mul_norm_Ioc`. The
    pin's *third* private row, `exists_zpow_mul_mem_annulus`, states exactly the headline; since the
    published name is the headline's, Lean forbids keeping both (a `private` and a public
    `TateCurve.exists_zpow_mul_mem_annulus` collide: "a private declaration … has already been
    declared"), so that row is folded into the headline — its body is transcribed verbatim there;
  * `tsum_comp_add_one'` is stated identically in the two `q`-multiplication pins and is written once
    (`private`, in the `q`-multiplication section), hence 2 pin rows → 1 port row.

  Two pin declarations carry no `set_option` and the port adds none. The pin's
  `norm_le_of_le_geometric` auto-includes the section's `[CompleteSpace K]`, which it does not use
  (the pin's file has no `linter.unusedSectionVars` line to transcribe, and the port's rule for a
  dead binder is to drop it, not to excuse it); the port writes `omit [CompleteSpace K] in` there,
  the tree's standing cure for that warning. Two mathlib modules are added to the scaffold's import
  list because the `tsum` engine needs them: `InfiniteSum.Constructions`
  (`Summable.tsum_sigma`) and `InfiniteSum.Real` (`summable_sigma_of_nonneg`).

  Gates measured on landing:

  * heartbeat probe pair (measured, **never installed** — FR-0225): silent at
    `-DmaxHeartbeats=2000`, fails at `1500` (`(deterministic) timeout at whnf`, on
    `nodal_xfun_yfun`), so the module's natural cost is 1.5–2 k heartbeats — under 1 % of the
    200 000 edit-loop cap. No `set_option maxHeartbeats` here, ever;
  * `move_dead --dry-run` (gate 6): 2 declarations / 22 lines, and both are the pin's own dead
    `private` companions — `summable_pairTerm` and `summable_succ_prod` (the pin states them and
    never calls them either: `summable_pairTerm`'s only caller is `summable_succ_prod`). Kept in
    place and recorded here per the escape clause; never deleted on the port's own.
    *(Superseded by the AF109F landing below: SET-AF109F's two `q`-expansion headlines call
    `summable_succ_prod`, so the pair is live and the module now reads 0 / 0. The paragraph is kept
    for the record of why the pair was not deleted in the AF107H wave.)*
  * `dedup --within --module SeriesIdentities` (all three tiers, `--min-cost 0`): 0 clusters.

  **Landing (AF107H) — the three `sOne`/`zpow` rows.**  Added at the end of the module:
  `sOne_eq_tsum_xfun` (101 pin `S_` lines) and `pointX_zpow_mul` / `pointY_zpow_mul` (22 each).  The
  two `zpow` rows are the pin's 16-line `Int.induction_on` transcriptions over
  `pointX_q_mul`/`pointY_q_mul` (same module); `sOne_eq_tsum_xfun` is the pin's `tsum` form of
  `hasSum_xfun`, and its **six `private` helpers** (`hasSum_geometric_succ`, `sigmaTerm`,
  `nnnorm_sigmaTerm_le`, `summable_sigmaTerm`, `hasSum_sigmaTerm_row`, `hasSum_sigmaTerm_col`) are
  transcribed at the pin's own names, `private` as in the pin.  The pin's `p2m_open`/`p2m_export`
  scaffolding is not transcribed; the port's `TateCurve` namespace already publishes `xfun`, `s₁`,
  `term`, `summable_term`, `coeffSum`, `hasSum_xfun`.

  * Engine gate: **13** pin files, **33** pin decls; module **28** decls (10 public + 18 parsed
    private), **21 by hash**, **1 by name (hash differs)** — the pre-existing
    `exists_zpow_mul_mem_annulus` fold recorded above — and **6 unaccounted**, which are the six
    pre-existing headlines that the pin spells `solution` (`hasSum_xfun`, `hasSum_yfun`,
    `nodal_xfun_yfun`, `pointX_q_mul`, `pointY_q_mul`, `tsum_succ_prod_eq_tsum_divisors`).  The three
    new rows and all six of their private helpers match **by hash**.
  * `check_port` **10 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — 7 before, 10 after, the order's
    number.
  * **Surface probe** (`tmp/af107/probe-surface-SI.lean`, `private` dropped from the six new
    helpers): **16 ok / 0 mismatch / 0 missing / 0 own**.  All six are pin rows and promote cleanly;
    whether to promote is the manager's call (the pin has them `private`).
  * `#print axioms` on all **10** public declarations: `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx`.
  * `move_dead --dry-run`: still **2 declarations, 22 lines** — the *same* pre-existing pair
    (`summable_pairTerm`, `summable_succ_prod`) the escape clause above records; all six new helpers
    are live.  No `--apply`.
  * Heartbeat probe pair (measured, **never installed**): **unchanged** by the three rows — the module
    is **silent at `-DmaxHeartbeats=2000`** and **first fails at `1500`**, at `nodal_xfun_yfun` (line
    116), exactly the pair recorded on landing; 40000/20000/10000 are silent too, and 1000 fails with
    64 lines.  No `set_option maxHeartbeats` is installed.
  * Four proof-level adaptations for a silent module (statements untouched):
    `Metric.tendsto_nhds` replaces the pin's `NormedAddCommGroup.tendsto_nhds_zero` (not in
    `v4.34.0`), with `dist_zero_right` carrying the norm; `Set.mem_ofPred_eq` replaces the deprecated
    `Set.mem_setOf_eq` and `not_lt.mp` replaces the deprecated `push_neg`; `Set.finite_Iio` is the
    `LocallyFiniteOrderBot` form of the pin's `(Set.finite_Iio N)` (same name, needs the instance);
    and the two `pred` branches of the `zpow` inductions close with `ring_nf` instead of the pin's
    `ring`, because the pin's `rw [show (-(k:ℤ)) = …]` also rewrites the `-(k:ℤ)` inside the right
    side's exponent, so `ring`'s `ring1` pass no longer sees syntactically equal atoms (`ring` then
    falls through to `ring_nf` anyway and logs a `Try this` info message — writing `ring_nf` is that
    same proof without the message).  Three `omit [… ] in` lines drop section variables the pin's
    `variable` block auto-includes and the new helpers do not use.

  spec-pin: P2M/Sol/S_TateCurve_tsum_succ_prod_eq_tsum_divisors.lean
  spec-pin: P2M/Sol/S_TateCurve_exists_zpow_mul_mem_annulus.lean
  spec-pin: P2M/Sol/S_TateCurve_nodal_xfun_yfun.lean
  spec-pin: P2M/Sol/S_TateCurve_pointX_q_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_pointY_q_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_hasSum_xfun.lean
  spec-pin: P2M/Sol/S_TateCurve_hasSum_yfun.lean

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_TateCurve_sOne_eq_tsum_xfun.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_TateCurve_pointX_zpow_mul.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_TateCurve_pointY_zpow_mul.lean>
  spec-pin: Theorems/Thm_TateCurve_sOne_eq_tsum_xfun.lean
  spec-pin: P2M/Sol/S_TateCurve_sOne_eq_tsum_xfun.lean
  spec-pin: Theorems/Thm_TateCurve_pointX_zpow_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_pointX_zpow_mul.lean
  spec-pin: Theorems/Thm_TateCurve_pointY_zpow_mul.lean
  spec-pin: P2M/Sol/S_TateCurve_pointY_zpow_mul.lean

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_TateCurve_pointX_normalForm.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_TateCurve_pointY_normalForm.lean>
  spec-pin: Theorems/Thm_TateCurve_pointX_normalForm.lean
  spec-pin: P2M/Sol/S_TateCurve_pointX_normalForm.lean
  spec-pin: Theorems/Thm_TateCurve_pointY_normalForm.lean
  spec-pin: P2M/Sol/S_TateCurve_pointY_normalForm.lean
spec-pin: Theorems/Thm_TateCurve_pointX_qExpansion.lean
spec-pin: P2M/Sol/S_TateCurve_pointX_qExpansion.lean
spec-pin: Theorems/Thm_TateCurve_pointY_qExpansion.lean
spec-pin: P2M/Sol/S_TateCurve_pointY_qExpansion.lean
spec-pin: Theorems/Thm_TateCurve_defect_qExpansion.lean
spec-pin: P2M/Sol/S_TateCurve_defect_qExpansion.lean
spec-pin: Theorems/Thm_TateCurve_defectCoeff_zero.lean
spec-pin: P2M/Sol/S_TateCurve_defectCoeff_zero.lean

**Landing (AF108E) — the two normal forms.**  `pointX_normalForm` (198 pin `S_` lines) and
`pointY_normalForm` (199) as the last two declarations of the module, at the pin's statements and the
port's subject namespace (`TateCurve`); the pin's generated `P2MW.S_TateCurve_pointX_normalForm` /
`…pointY_normalForm` labels are dropped.  This is the order's **new engine**: the pin's two `S_` files
between them declare the same **10 private helpers** (22 pin rows → 12 port rows; `port_plan` prices the
duplication at 163 removable lines), and they are transcribed here **once**, at the pin's names:

  * `summable_xfun_pow_mul` (19), `summable_yfun_pow_mul` (28): `∑' n, xfun (q^(n+1) * v)` converges,
    by `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero` + `nnnorm_xfun_of_lt_one` /
    `nnnorm_yfun_of_lt_one` (the `yfun` bound uses `‖w‖₊ ^ 2 ≤ ‖w‖₊` under `‖w‖₊ ≤ 1`);
  * `xTerm_neg_add_one` (16), `yTerm_neg_add_one` (17): the negative-index terms are the `u⁻¹` series,
    via `xfun_inv` / `yfun_inv` and `∀ n, q ^ n * u ≠ 1`;
  * `xTerm_natCast_add_one` (3), `yTerm_natCast_add_one` (3): the `ℕ ↪ ℤ` re-indexing;
  * `tsum_xTerm_eq` (25), `tsum_yTerm_eq` (31): the two-sided split of the `ℤ`-indexed `tsum`, by
    mathlib's `tsum_of_nat_of_neg_add_one` + `Summable.tsum_eq_zero_add`, and for `y` the `tsum_sub` /
    `tsum_neg` of the two `u⁻¹` series (both need `summable_*_pow_mul`, not just summability of the
    `u`-series);
  * `pointX_split` (7), `pointY_split` (14): the split forms carrying `-2 * s₁ q` / `+ s₁ q`.

The two headlines then rewrite `s₁ q` by SET-AF107H's `sOne_eq_tsum_xfun` and recombine the three
`tsum`s with `HasSum.add` / `HasSum.sub` / `HasSum.mul_left` + `tsum_eq`; `ring` closes both.
Nothing is transcribed from the pin's `p2m_open`/`p2m_export` scaffolding: the port's `TateCurve`
namespace already publishes every name the pin's export list carries.

  * **Engine diff** (gate 2, `review.py`): **17** pin sources, **57** pin decls; module **40** decls,
    **33 by hash**, **1 by name (hash differs)** — the pre-existing `exists_zpow_mul_mem_annulus` fold
    recorded above — and **6 unaccounted**, the six pre-existing headlines the pin spells `solution`.
    All 10 helpers and both headlines match **by hash**: the prelude is the pin's 162-line block
    (`section SummabilityHelpers` … `end TwoSidedSplit`) **verbatim**, and the headline proofs are the
    pin's bodies verbatim.
  * **Prelude size**: the pin's shared block is **162 lines / 10 declarations (163 lines by
    `port_plan`'s measure)**; in the module it is **166 lines** (+4 `omit` lines, below) inside a
    **174-line** `section NormalForm` (the block, a doc-comment heading, `open Filter`, the section
    `variable`, `end`).  Whole-module insertion: **+215 lines**, **12 declarations** (10 private + 2
    public), no line removed but the two scaffold `sorry`s.
  * **Four `omit [IsUltrametricDist K] [CompleteSpace K] in` lines** (declaration-scoped, statements
    untouched): `xTerm_neg_add_one`, `yTerm_neg_add_one`, `xTerm_natCast_add_one`,
    `yTerm_natCast_add_one` use neither the ultrametric instance nor completeness — they are pure
    `xfun_inv`/`yfun_inv`/`zpow` rewrites — and the pin's `variable` block auto-includes both, so
    `linter.unusedSectionVars` fires.  Same cure as `norm_le_of_le_geometric` above; no `set_option`
    is added anywhere.
  * **One `open Filter`** inside the new section: the pin carries `Filter` in its `p2m_open` line and
    `Tendsto` (used by `squeeze_zero_norm'`) is not at root; the port's module-level `open` line does
    not include it and the older declarations do not need it.
  * **Two proof-level adaptations** (silent module, statements untouched): the pin's
    `· simpa using xTerm_zero q u` / `… yTerm_zero …` become `· simp` — `xTerm_zero`/`yTerm_zero` are
    `@[simp]`, so `simpa using` trips `linter.unnecessarySimpa` (FR-0319: an info line counts).
  * `check_port` **12 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — 10 before, 12 after: the order's
    number (7 pre-existing + AF107H's 3 + these 2).
  * **Surface probe** (`tmp/af108/probe-surface-SI-E.lean`, `private` dropped from all ten helpers):
    **22 ok / 0 mismatch / 0 missing / 0 own** — every one of the ten is a pin row and promotes
    cleanly.  Whether to promote is the manager's call (the pin has them `private`).
  * `#print axioms` on all **12** public declarations: `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx`.
  * `dedup --within --module '*TateCurve/SeriesIdentities*'`, all three tiers at `--min-cost 0`:
    **0 clusters** (40 declarations).  The pin's own two headlines have the same conclusion in the two
    `S_` files, but the port writes one declaration each, so no pair is left.
  * `move_dead --dry-run`: still **2 declarations, 22 lines** — the *same* pre-existing pair
    (`summable_pairTerm`, `summable_succ_prod`) the escape clause above records; all 10 new helpers are
    live (each has a caller: the `tsum_*_eq` rows call the summability and re-indexing rows, the two
    splits call the `tsum_*_eq` rows, the headlines call the splits).
  * Heartbeat probe pair (measured, **never installed**): the module is **silent at
    `-DmaxHeartbeats=2500`** and **first fails at `2200`** (`(deterministic) timeout at whnf`); 40000 /
    20000 / 10000 / 5000 / 3000 are silent too.  The pre-existing module was silent at 2000 / failed at
    1500, so the twelve new declarations moved the floor by well under 1 k heartbeats — still ~1 % of
    the 200 000 edit-loop cap.  No `set_option maxHeartbeats` here, ever.
  * Locked `lake build FLTForHuman.TateCurve.SeriesIdentities`: **0 warning lines**, and the set-level
    `tmp/af108/collision-probe.lean` prints nothing.

  **Landing (AF109F) — the two `q`-expansions.**  `pointX_qExpansion` and `pointY_qExpansion` (284 pin
  `S_` lines each, the *same* proof with `x` interchanged for `y`) as the module's last two
  declarations, at the pin's statements and the port's subject namespace.  The two pins' **fifteen-row
  shared prelude** is written **once**, `private`, in one `section QExpansion` inside
  `namespace TateCurve`; **nine** of the fifteen rows were already here from the `sOne_eq_tsum_xfun`
  and AF108E landings and are used directly — `pairTerm`, `sigmaTerm'`, `norm_le_of_le_geometric`,
  `summable_sigmaTerm'`, `summable_pairTerm`, `tsum_pairTerm_eq_tsum_divisors`, `succEquivPNat`, plus
  the pin's `tsum_succ_prod_eq_tsum_divisors_loc` / `summable_succ_prod_loc` pair, which this module
  already carries at the *same statements* as `tsum_succ_prod_main` / `summable_succ_prod`.  The pin
  keeps both spellings, so both are kept: `tsum_succ_prod_main` feeds the public
  `tsum_succ_prod_eq_tsum_divisors`, and `summable_succ_prod` is the row both new headlines call.  The
  **six genuinely new** rows (104 pin lines) are `norm_mul_growthBound_lt_one` (13),
  `nnnorm_pow_mul_lt_one` (9), `nnnorm_pow_lt_one` (4), `hasSum_yfun_succ` (31), `hasSum_xRow` (19) and
  `hasSum_yRow` (28); the two headlines are the pins' 16-line bodies verbatim.  Whole-module
  insertion: **+147 lines** (117 for the new section incl. its heading and the two `end`s, 30 for the
  two headline bodies), **8 declarations** (6 private + 2 public), the two scaffold `sorry`s removed —
  871 → 1018 lines (1075 with this note).

  * **Engine diff** (gate 2): **21** pin sources, **91** pin decls; module **48** decls, **41 by hash**,
    **1 by name (hash differs)** — the pre-existing `exists_zpow_mul_mem_annulus` fold recorded above —
    and **6 unaccounted**, the six pre-existing headlines the pin spells `solution`.  Every one of the
    **32** pin declarations over the two new wires is covered **by hash**: the fifteen prelude rows are
    declared 9 (reused) + 6 (new) times, and the second `S_` file's copies match those *same*
    declarations — the checker credits by statement hash, so `32 pin rows → 17 port rows` is a match,
    not a gap.  No pin declaration anywhere on this module's wire is left unmatched.
  * `check_port` **14 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — 14 before, 14 after: the two
    headlines were already `ok` as scaffolds, and the six new rows are `private`, so they enter the
    count only through the surface probe below.
  * **Surface probe** (`tmp/af109/probe-surface-F.lean`, `private` dropped from all six new rows):
    **20 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.  All six are pin rows and promote cleanly;
    whether to promote is the manager's call (the pin has them `private`).
  * `#print axioms` on all **14** public declarations: `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx`.
  * `dedup --within --module '*TateCurve/SeriesIdentities*'`, all three tiers at `--min-cost 0`:
    **0 clusters** (48 declarations).
  * `move_dead --dry-run`: **0 declarations, 0 lines** — the escape clause above is now **moot**: both
    new headlines call `summable_succ_prod`, so it and the `summable_pairTerm` it calls are live for the
    first time, and the module no longer has a dead declaration.
  * Heartbeat probe pair (measured, **never installed**): **silent at `-DmaxHeartbeats=2500`**, **first
    fails at `2400`** (`(deterministic) timeout at whnf`, inside the *pre-existing*
    `yTerm_neg_add_one`); 40000 / 20000 / 10000 / 5000 are silent too, and 2200 / 2000 / 1000 fail in
    pre-existing rows (686, 267, 231).  The floor is the AF108E pair to within one rung and every rung
    I measured fails in a **pre-existing** declaration, so the fifteen new rows moved it by less than
    the ladder resolves — ~1.25 % of the 200 000 edit-loop cap.  No `set_option maxHeartbeats` here,
    ever.
  * Proof-level adaptations (statements untouched): the two headlines call the module's
    `summable_succ_prod` where the pin calls its `summable_succ_prod_loc` (same statement, same body —
    the port's spelling of that row); three `omit [IsUltrametricDist K] [CompleteSpace K] in` lines
    (`norm_mul_growthBound_lt_one`, `nnnorm_pow_mul_lt_one`, `nnnorm_pow_lt_one`) and one
    `omit [CompleteSpace K] in` (`hasSum_xRow`) drop section instances the pin's `variable` block
    auto-includes and those proofs do not use.  `hasSum_yfun_succ` and `hasSum_yRow` keep
    `[CompleteSpace K]`: their proofs go through
    `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`, which needs it.
  * Locked `lake build FLTForHuman.TateCurve.SeriesIdentities`: **0 warning lines**; the order-scoped
    `tmp/af109/probe-F.lean` prints nothing, and `rg` finds no other declaration of any of the six new
    names (nor of the two headlines) anywhere in `lean/FLTForHuman`.

  **Landing (AF110C) — the Weierstrass defect as a `q`-series.**  `TateCurve.defect_qExpansion` (368
  pin lines) and `TateCurve.defectCoeff_zero` (13) at the end of the module, at the pins' statements
  and the port's subject namespace; both are stated in `TateCurve/Defect.lean`'s layer
  (`cauchyMul`, `xCoeffFull`/`yCoeffFull`, `a₄Coeff`/`a₆Coeff`, `defectCoeff`), which the module
  imports.  Of the first pin's 22 rows, **10 were already here** and are used directly — `pairTerm`,
  `sigmaTerm'`, `norm_le_of_le_geometric`, `summable_sigmaTerm'`, `summable_pairTerm`,
  `tsum_pairTerm_eq_tsum_divisors`, `succEquivPNat`, `norm_mul_growthBound_lt_one`, plus the pin's
  `tsum_succ_prod_loc` / `summable_succ_prod_loc` pair, which this module carries at the same
  statements as `tsum_succ_prod_main` / `summable_succ_prod` and which the new rows call under those
  (the port's) spellings.  The **11 genuinely new** rows are `hasSum_term_succ` (17),
  `coeffSum_qExpansion` (28), `summable_norm_a₄Series` (7), `summable_norm_a₆Series` (7),
  `summable_norm_xSeries` (5), `summable_norm_ySeries` (5), `pointX_eq_tsum` (9), `pointY_eq_tsum`
  (9), `a₄_eq_tsum` (11), `a₆_eq_tsum` (11) and `defect_qExpansion_loc` (66, the pin's `private`
  copy of the headline's statement — kept as the pin has it, so the pin's own pair is recorded here
  per the `dedup` gate exactly as `tsum_succ_prod_main` above is).  The two headline bodies are the
  pins' verbatim: `defect_qExpansion_loc hq0 hq hu0 hu hqu hqu'`, and the 13-line second pin's
  `nodal_xfun_yfun` + `linear_combination` proof.  Whole-module insertion: **+203 lines** of code
  (1110 → 1313: a 199-line private section and the two bodies replacing a `sorry` each), **13
  declarations** (11 private + 2 public), no line removed but the two scaffold `sorry`s; the module
  reads **1371 lines** with this note.

  * **Engine diff** (gate 2, `review.py`): **25** pin sources, **116** pin decls; module **61** decls,
    **54 by hash**, **1 by name (hash differs)** — the pre-existing `exists_zpow_mul_mem_annulus` fold
    recorded above — and **6 unaccounted**, the same six pre-existing headlines the pin spells
    `solution`.  All **23** pin rows over the two AF110 wires (22 + 1) are matched **by statement
    hash**, and every one of the 11 new rows matches its pin row by hash too (`defect_qExpansion_loc`
    is exact).
  * `check_port` **16 ok / 0 mismatch / 0 missing / 0 own / 0 kw** — **16 before, 16 after**: both
    headlines were already `ok` as scaffolds (the two AF110 wires were on the header from the scaffold
    pass), and the 11 new rows are `private`, so they enter only through the surface probe below.
    (Order C's brief predicts 18; that double-counts the two headlines, the same reading AF109F
    recorded at 14/14.)
  * **Surface probe** (`tmp/af110/probe-surface-C.lean`, `private` dropped from all **21** pin-private
    rows this module carries for these two wires — the 11 new and the 10 reused): **37 ok / 0
    mismatch / 0 missing / 0 own / 0 kw**.  Every one of the 21 is a pin row and promotes cleanly;
    whether to promote is the manager's call (the pin has them `private`).
  * `#print axioms` on all **16** public declarations: `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx`.
  * `dedup --within --module '*TateCurve/SeriesIdentities*'`, all three tiers at `--min-cost 0`:
    **0 clusters** (61 declarations).
  * `move_dead --dry-run`: **0 declarations, 0 lines** (unchanged from the AF109F landing).
  * Heartbeat probe pair (measured, **never installed** — FR-0225): the module is now **silent at
    `-DmaxHeartbeats=3000`** and **first fails at `2500`**, in *this* order's
    `defect_qExpansion_loc` (`(deterministic) timeout at whnf`); 40000 / 20000 / 10000 / 5000 / 3000
    are silent, and 2400 / 2000 / 1000 fail inside **pre-existing** rows (`yTerm_neg_add_one`,
    `nodal_xfun_yfun`, `hasSum_xfun`).  The floor moved from AF109F's 2500/2400 pair to 3000/2500 —
    the new rows cost ≲ 500 heartbeats, ~1.5 % of the 200 000 edit-loop cap.  No
    `set_option maxHeartbeats` here, ever.
  * Proof-level adaptations (statements untouched): one `omit [IsUltrametricDist K] [CompleteSpace K]
    in` (`hasSum_term_succ`, a pure geometric-series rewrite) and four `omit [CompleteSpace K] in`
    (`summable_norm_a₄Series`, `summable_norm_a₆Series`, `summable_norm_xSeries`,
    `summable_norm_ySeries` — their proofs stay inside `summable_norm_qSeries` /
    `norm_mul_growthBound_lt_one`); `a₄_eq_tsum`/`a₆_eq_tsum` keep `[CompleteSpace K]`, because
    `Summable.of_norm` needs it (the pin's own declarations carry it too).
  * Locked `lake build FLTForHuman.TateCurve.SeriesIdentities`: **0 warning lines** (3117 jobs, incl.
    the `Defect`/`Tails` dependencies); the order-scoped `tmp/af110/probe-C.lean` prints nothing, and
    `rg` finds no other declaration of any of the 13 new names anywhere in `lean/FLTForHuman`.
-/
import FLTForHuman.TateCurve.PointSeries
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Real
import FLTForHuman.TateCurve.Tails
import FLTForHuman.TateCurve.Defect

set_option autoImplicit false

noncomputable section

open TateCurve
open scoped NNReal

namespace TateCurve

/-! ### The geometric-series expansions of `xfun` and `yfun` -/

theorem hasSum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1)) (xfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 1 hw').mul_left w
  have hfun : (fun m : ℕ => w * (((m + 1).choose 1 : ℕ) * w ^ m))
      = fun m : ℕ => ((m + 1 : ℕ) : K) * w ^ (m + 1) := by
    funext m; rw [Nat.choose_one_right]; ring
  have hval : w * (1 / (1 - w) ^ 2) = xfun w := by rw [xfun]; ring
  rw [hfun, hval] at h
  exact h

theorem hasSum_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2)) (yfun w) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_choose_mul_geometric_of_norm_lt_one 2 hw').mul_left (w ^ 2)
  have hfun : (fun m : ℕ => w ^ 2 * (((m + 2).choose 2 : ℕ) * w ^ m))
      = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
    funext m; ring
  have hval : w ^ 2 * (1 / (1 - w) ^ 3) = yfun w := by rw [yfun]; ring
  rw [hfun, hval] at h
  exact h

theorem nodal_xfun_yfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] {w : K} (hw1 : w ≠ 1) :
    yfun w ^ 2 + xfun w * yfun w = xfun w ^ 3 := by
  have h1 : (1 : K) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw1)
  have e2 : xfun w * ((1 : K) - w) ^ 2 = w := by
    rw [xfun, div_mul_cancel₀ _ (pow_ne_zero 2 h1)]
  have e3 : yfun w * ((1 : K) - w) ^ 3 = w ^ 2 := by
    rw [yfun, div_mul_cancel₀ _ (pow_ne_zero 3 h1)]
  apply mul_right_cancel₀ (pow_ne_zero 6 h1)
  calc (yfun w ^ 2 + xfun w * yfun w) * ((1 : K) - w) ^ 6
      = (yfun w * ((1 : K) - w) ^ 3) ^ 2
        + (xfun w * ((1 : K) - w) ^ 2) * (yfun w * ((1 : K) - w) ^ 3) * ((1 : K) - w) := by ring
    _ = (w ^ 2) ^ 2 + w * w ^ 2 * ((1 : K) - w) := by rw [e2, e3]
    _ = w ^ 3 := by ring
    _ = (xfun w * ((1 : K) - w) ^ 2) ^ 3 := by rw [e2]
    _ = xfun w ^ 3 * ((1 : K) - w) ^ 6 := by ring

/-! ### The `q`-periodicity of the point coordinates -/

section QMul

private theorem tsum_comp_add_one' {α : Type*} [AddCommGroup α] [UniformSpace α]
    [IsUniformAddGroup α] [CompleteSpace α] [T2Space α] (f : ℤ → α) :
    ∑' n : ℤ, f (n + 1) = ∑' n : ℤ, f n :=
  (Equiv.addRight (1 : ℤ)).tsum_eq f

theorem pointX_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) : pointX q (q * u) = pointX q u := by
  have hterm : ∀ n : ℤ, xTerm q (q * u) n = xTerm q u (n + 1) := fun n => by
    rw [xTerm, xTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointX, pointX]
  congr 1
  calc ∑' n : ℤ, xTerm q (q * u) n = ∑' n : ℤ, xTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, xTerm q u n := tsum_comp_add_one' _

theorem pointY_q_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {q u : K} (hq0 : q ≠ 0) : pointY q (q * u) = pointY q u := by
  have hterm : ∀ n : ℤ, yTerm q (q * u) n = yTerm q u (n + 1) := fun n => by
    rw [yTerm, yTerm, show q ^ n * (q * u) = q ^ (n + 1) * u by rw [zpow_add_one₀ hq0]; ring]
  rw [pointY, pointY]
  congr 1
  calc ∑' n : ℤ, yTerm q (q * u) n = ∑' n : ℤ, yTerm q u (n + 1) := tsum_congr hterm
    _ = ∑' n : ℤ, yTerm q u n := tsum_comp_add_one' _

end QMul

/-! ### The Lambert-type regrouping over `ℕ × ℕ` -/

section GeneralRegrouping

variable {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
variable {h : ℕ → K} {C : ℝ} {r : K}

private def pairTerm (h : ℕ → K) (r : K) (c : ℕ+ × ℕ+) : K :=
  h (c.2 : ℕ) * r ^ ((c.1 : ℕ) * (c.2 : ℕ))

private def sigmaTerm' (h : ℕ → K) (r : K)
    (x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}) : K :=
  h x.2.1.2 * r ^ (x.2.1.1 * x.2.1.2)

omit [CompleteSpace K] in
private theorem norm_le_of_le_geometric (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
    {n : ℕ} {p : ℕ × ℕ} (hp : p ∈ n.divisorsAntidiagonal) :
    ‖h p.2 * r ^ (p.1 * p.2)‖ ≤ C ^ n * ‖r‖ ^ n := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  obtain ⟨hmul, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hp
  have hp2mem : p.2 ∈ n.divisors := Nat.snd_mem_divisors_of_mem_antidiagonal hp
  have hp2pos : 0 < p.2 := Nat.pos_of_mem_divisors hp2mem
  have hp2le : p.2 ≤ n :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hp2mem)
  rw [norm_mul, norm_pow, hmul]
  exact mul_le_mul ((hh p.2 hp2pos).trans (pow_le_pow_right₀ hC1 hp2le)) le_rfl
    (pow_nonneg (norm_nonneg r) n) (pow_nonneg hC0 n)

private theorem summable_sigmaTerm' (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (sigmaTerm' h r) := by
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC1
  have hs0 : (0 : ℝ) ≤ C * ‖r‖ := mul_nonneg hC0 (norm_nonneg r)
  have hs1 : C * ‖r‖ < 1 := by rwa [mul_comm] at hrC

  have hgeom : Summable fun n : ℕ => (n : ℝ) * (C * ‖r‖) ^ n := by
    have habs : ‖(C * ‖r‖ : ℝ)‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hs0]
    have := summable_pow_mul_geometric_of_norm_lt_one 1 habs
    simpa using this
  have hgeomP : Summable fun n : ℕ+ => ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) :=
    hgeom.comp_injective PNat.coe_injective
  apply Summable.of_norm
  rw [summable_sigma_of_nonneg (fun a => norm_nonneg _)]
  refine ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  refine Summable.of_nonneg_of_le (fun n => tsum_nonneg fun x => norm_nonneg _)
    (fun n => ?_) hgeomP
  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, ‖sigmaTerm' h r ⟨n, x⟩‖
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, ‖h p.2 * r ^ (p.1 * p.2)‖ := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => ‖h p.2 * r ^ (p.1 * p.2)‖
    _ ≤ ∑ _p ∈ ((n : ℕ)).divisorsAntidiagonal, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) :=
        Finset.sum_le_sum fun p hp => norm_le_of_le_geometric hC1 hh hp
    _ = ∑ _d ∈ ((n : ℕ)).divisors, C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ _ => C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ))]
    _ = (((n : ℕ)).divisors.card : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((n : ℕ) : ℝ) * (C ^ (n : ℕ) * ‖r‖ ^ (n : ℕ)) := by
        refine mul_le_mul_of_nonneg_right ?_
          (mul_nonneg (pow_nonneg hC0 _) (pow_nonneg (norm_nonneg r) _))
        exact_mod_cast Nat.card_divisors_le_self (n : ℕ)
    _ = ((n : ℕ) : ℝ) * (C * ‖r‖) ^ (n : ℕ) := by rw [mul_pow]

private theorem summable_pairTerm (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable (pairTerm h r) := by
  have hcomp : Summable (pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd) := by
    have hfun : pairTerm h r ∘ ⇑sigmaAntidiagonalEquivProd = sigmaTerm' h r := by
      funext x
      obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
      rfl
    rw [hfun]
    exact summable_sigmaTerm' hC1 hh hrC
  exact (Equiv.summable_iff sigmaAntidiagonalEquivProd).mp hcomp

private theorem tsum_pairTerm_eq_tsum_divisors (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
  have haux := summable_sigmaTerm' (r := r) hC1 hh hrC

  have htrans : ∑' c : ℕ+ × ℕ+, pairTerm h r c
      = ∑' x : (n : ℕ+) × {p // p ∈ (n : ℕ).divisorsAntidiagonal}, sigmaTerm' h r x := by
    rw [← Equiv.tsum_eq sigmaAntidiagonalEquivProd (pairTerm h r)]
    refine tsum_congr fun x => ?_
    obtain ⟨n, ⟨⟨a, b⟩, hab⟩⟩ := x
    rfl
  rw [htrans, Summable.tsum_sigma haux]
  refine tsum_congr fun n => ?_

  rw [tsum_fintype]
  calc ∑ x : {p // p ∈ ((n : ℕ)).divisorsAntidiagonal}, sigmaTerm' h r ⟨n, x⟩
      = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (p.1 * p.2) := by
        rw [Finset.univ_eq_attach]
        exact Finset.sum_attach ((n : ℕ)).divisorsAntidiagonal fun p => h p.2 * r ^ (p.1 * p.2)
    _ = ∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2 * r ^ (n : ℕ) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
    _ = (∑ p ∈ ((n : ℕ)).divisorsAntidiagonal, h p.2) * r ^ (n : ℕ) := by
        rw [Finset.sum_mul]
    _ = (∑ d ∈ ((n : ℕ)).divisors, h d) * r ^ (n : ℕ) := by
        rw [Nat.sum_divisorsAntidiagonal' (f := fun _ d => h d)]

private def succEquivPNat : ℕ ≃ ℕ+ where
  toFun n := n.succPNat
  invFun n := n.natPred
  left_inv n := Nat.natPred_succPNat n
  right_inv n := PNat.succPNat_natPred n

private theorem tsum_succ_prod_main (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) := by
  have hL : ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' c : ℕ+ × ℕ+, pairTerm h r c := by
    rw [← Equiv.tsum_eq (Equiv.prodCongr succEquivPNat succEquivPNat) (pairTerm h r)]
    refine tsum_congr fun p => ?_
    obtain ⟨a, b⟩ := p
    rfl
  have hR : ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1)
      = ∑' n : ℕ+, (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ) := by
    rw [← Equiv.tsum_eq succEquivPNat
      (fun n : ℕ+ => (∑ d ∈ (n : ℕ).divisors, h d) * r ^ (n : ℕ))]
    exact tsum_congr fun N => rfl
  rw [hL, hR]
  exact tsum_pairTerm_eq_tsum_divisors hC1 hh hrC

private theorem summable_succ_prod (hC1 : 1 ≤ C)
    (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m) (hrC : ‖r‖ * C < 1) :
    Summable fun p : ℕ × ℕ => h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) := by
  have hsum := summable_pairTerm (r := r) hC1 hh hrC
  have hcomp : Summable (pairTerm h r ∘ ⇑(Equiv.prodCongr succEquivPNat succEquivPNat)) :=
    (Equiv.summable_iff (Equiv.prodCongr succEquivPNat succEquivPNat)).mpr hsum
  refine hcomp.congr fun p => ?_
  obtain ⟨a, b⟩ := p
  rfl

end GeneralRegrouping

theorem tsum_succ_prod_eq_tsum_divisors {K : Type*} [NontriviallyNormedField K] [CompleteSpace K]
    {h : ℕ → K} {C : ℝ} {r : K} (hC1 : 1 ≤ C) (hh : ∀ m : ℕ, 0 < m → ‖h m‖ ≤ C ^ m)
    (hrC : ‖r‖ * C < 1) :
    ∑' p : ℕ × ℕ, h (p.2 + 1) * r ^ ((p.1 + 1) * (p.2 + 1)) =
      ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, h d) * r ^ (N + 1) :=
  tsum_succ_prod_main hC1 hh hrC

/-! ### Carrying `u` into the norm-`< 1` annulus -/

section Annulus

variable {K : Type*} [NontriviallyNormedField K] {q u : K}

private theorem nnnorm_lt_one_iff_norm {x : K} : ‖x‖₊ < 1 ↔ ‖x‖ < 1 := by
  rw [← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one]

private theorem exists_zpow_mul_norm_Ioc (hq0 : q ≠ 0) (hq : ‖q‖ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q‖ < ‖q ^ n * u‖ ∧ ‖q ^ n * u‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hu_pos : (0 : ℝ) < ‖u‖ := norm_pos_iff.mpr hu0
  have hq_ne : (‖q‖ : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hy : (1 : ℝ) < ‖q‖⁻¹ := one_lt_inv_iff₀.mpr ⟨hq_pos, hq⟩
  obtain ⟨n, hn1, hn2⟩ := exists_mem_Ioc_zpow hu_pos hy
  have hqk_pos : (0 : ℝ) < ‖q‖ ^ (n + 1 : ℤ) := zpow_pos hq_pos _

  have hcancel : ∀ m : ℤ, ‖q‖⁻¹ ^ m * ‖q‖ ^ m = 1 := fun m => by
    rw [← mul_zpow, inv_mul_cancel₀ hq_ne, one_zpow]
  refine ⟨n + 1, ?_, ?_⟩
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n = ‖q‖ := by
      rw [zpow_add₀ hq_ne, zpow_one]
      calc ‖q‖ ^ n * ‖q‖ * ‖q‖⁻¹ ^ n
          = ‖q‖⁻¹ ^ n * (‖q‖ ^ n * ‖q‖) := mul_comm _ _
        _ = ‖q‖⁻¹ ^ n * ‖q‖ ^ n * ‖q‖ := (mul_assoc _ _ _).symm
        _ = 1 * ‖q‖ := by rw [hcancel n]
        _ = ‖q‖ := one_mul _
    have hlt : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ :=
      mul_lt_mul_of_pos_left hn1 hqk_pos
    rw [norm_mul, norm_zpow]
    calc ‖q‖ = ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ n := hkey.symm
      _ < ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ := hlt
  ·
    have hkey : ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) = 1 := by
      calc ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1)
          = ‖q‖⁻¹ ^ (n + 1) * ‖q‖ ^ (n + 1) := mul_comm _ _
        _ = 1 := hcancel (n + 1)
    have hle : ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) :=
      mul_le_mul_of_nonneg_left hn2 hqk_pos.le
    rw [norm_mul, norm_zpow]
    calc ‖q‖ ^ (n + 1 : ℤ) * ‖u‖ ≤ ‖q‖ ^ (n + 1 : ℤ) * ‖q‖⁻¹ ^ (n + 1) := hle
      _ = 1 := hkey

end Annulus

theorem exists_zpow_mul_mem_annulus {K : Type*} [NontriviallyNormedField K] {q u : K}
    (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) :
    ∃ n : ℤ, ‖q * (q ^ n * u)‖₊ < 1 ∧ ‖q * (q ^ n * u)⁻¹‖₊ < 1 := by
  have hqR : ‖q‖ < 1 := nnnorm_lt_one_iff_norm.mp hq
  obtain ⟨n, h1, h2⟩ := exists_zpow_mul_norm_Ioc hq0 hqR hu0
  have hq_pos : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  have hv_pos : (0 : ℝ) < ‖q ^ n * u‖ := lt_trans hq_pos h1
  refine ⟨n, nnnorm_lt_one_iff_norm.mpr ?_, nnnorm_lt_one_iff_norm.mpr ?_⟩
  · rw [norm_mul]
    calc ‖q‖ * ‖q ^ n * u‖ ≤ ‖q‖ * 1 := mul_le_mul_of_nonneg_left h2 hq_pos.le
      _ = ‖q‖ := mul_one _
      _ < 1 := hqR
  · rw [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hv_pos]
    exact h1

/-! ### `s₁` as a `tsum` of `xfun`, and the `q`-periodicity for `zpow` -/

section SOneTsum

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K}

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem hasSum_geometric_succ {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun i : ℕ => w ^ (i + 1)) (w / (1 - w)) := by
  have hw' : ‖w‖ < 1 := hw
  have h := (hasSum_geometric_of_norm_lt_one hw').mul_left w
  have hfun : (fun i : ℕ => w * w ^ i) = fun i : ℕ => w ^ (i + 1) := by
    funext i; rw [pow_succ]; ring
  have hval : w * (1 - w)⁻¹ = w / (1 - w) := by rw [div_eq_mul_inv]
  rw [hfun, hval] at h; exact h

private def sigmaTerm (q : K) (p : ℕ × ℕ) : K :=
  ((p.2 + 1 : ℕ) : K) * q ^ ((p.1 + 1) * (p.2 + 1))

omit [CompleteSpace K] in
private theorem nnnorm_sigmaTerm_le (p : ℕ × ℕ) :
    ‖sigmaTerm q p‖₊ ≤ ‖q‖₊ ^ ((p.1 + 1) * (p.2 + 1)) := by
  rw [sigmaTerm, nnnorm_mul, nnnorm_pow]
  calc ‖((p.2 + 1 : ℕ) : K)‖₊ * ‖q‖₊ ^ ((p.1 + 1) * (p.2 + 1))
      ≤ 1 * ‖q‖₊ ^ ((p.1 + 1) * (p.2 + 1)) := by gcongr; exact IsUltrametricDist.nnnorm_natCast_le_one K _
    _ = ‖q‖₊ ^ ((p.1 + 1) * (p.2 + 1)) := one_mul _

private theorem summable_sigmaTerm (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    Summable (sigmaTerm q (K := K)) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Metric.tendsto_nhds]
  intro ε hε
  rw [Filter.eventually_cofinite]
  have hq' : ‖q‖ < 1 := hq
  have hq0' : (0 : ℝ) < ‖q‖ := norm_pos_iff.mpr hq0
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hq'
  apply Set.Finite.subset ((Set.finite_Iio N).prod (Set.finite_Iio N))
  rintro ⟨n, m⟩ hp
  simp only [Set.mem_ofPred_eq, not_lt, dist_zero_right] at hp
  have hbound : ‖sigmaTerm q (n, m)‖ ≤ ‖q‖ ^ ((n + 1) * (m + 1)) := by
    exact_mod_cast nnnorm_sigmaTerm_le (q := q) (n, m)
  have hexp : (n + 1) * (m + 1) < N := by
    by_contra hge; have hge := not_lt.mp hge
    have : ‖q‖ ^ ((n + 1) * (m + 1)) ≤ ‖q‖ ^ N :=
      pow_le_pow_of_le_one (norm_nonneg q) hq'.le hge
    exact absurd (lt_of_le_of_lt (hbound.trans this) hN) (not_lt.mpr hp)
  simp only [Set.mem_prod, Set.mem_Iio]
  have h1 : n + 1 ≤ (n + 1) * (m + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos m)
  have h2 : m + 1 ≤ (n + 1) * (m + 1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos n)
  omega

omit [CompleteSpace K] in
private theorem hasSum_sigmaTerm_row (hq : ‖q‖₊ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => sigmaTerm q (n, m)) (xfun (q ^ (n + 1))) := by
  have hqn : ‖q ^ (n + 1)‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero n)
  have h := TateCurve.hasSum_xfun hqn
  have hfun : (fun m : ℕ => ((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1))
      = fun m : ℕ => sigmaTerm q (n, m) := by
    funext m; rw [sigmaTerm, ← pow_mul]
  rw [hfun] at h; exact h

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem hasSum_sigmaTerm_col (hq : ‖q‖₊ < 1) (m : ℕ) :
    HasSum (fun n : ℕ => sigmaTerm q (n, m)) (term (fun k => k) q (m + 1)) := by
  have hqm : ‖q ^ (m + 1)‖₊ < 1 := by
    rw [nnnorm_pow]; exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero m)
  have h := (hasSum_geometric_succ hqm).mul_left ((m + 1 : ℕ) : K)
  have hfun : (fun n : ℕ => ((m + 1 : ℕ) : K) * (q ^ (m + 1)) ^ (n + 1))
      = fun n : ℕ => sigmaTerm q (n, m) := by
    funext n; rw [sigmaTerm, ← pow_mul, Nat.mul_comm (m + 1) (n + 1)]
  have hval : ((m + 1 : ℕ) : K) * (q ^ (m + 1) / (1 - q ^ (m + 1)))
      = term (fun k => k) q (m + 1) := by rw [term]
  rw [hfun, hval] at h; exact h

end SOneTsum

theorem sOne_eq_tsum_xfun {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) :
    s₁ q = ∑' n : ℕ, xfun (q ^ (n + 1)) := by
  have hF := summable_sigmaTerm (K := K) hq0 hq
  have hrows : ∑' p : ℕ × ℕ, sigmaTerm q p = ∑' n : ℕ, xfun (q ^ (n + 1)) := by
    rw [hF.tsum_prod]
    exact tsum_congr fun n => (hasSum_sigmaTerm_row hq n).tsum_eq
  have hswap : Summable fun p : ℕ × ℕ => sigmaTerm q (p.2, p.1) := by
    have := (Equiv.prodComm ℕ ℕ).summable_iff.mpr hF
    simpa [Function.comp_def, Equiv.prodComm_apply, Prod.swap] using this
  have hcols : ∑' p : ℕ × ℕ, sigmaTerm q p = ∑' m : ℕ, term (fun k => k) q (m + 1) := by
    have h1 : ∑' p : ℕ × ℕ, sigmaTerm q p = ∑' p : ℕ × ℕ, sigmaTerm q (p.2, p.1) := by
      rw [← (Equiv.prodComm ℕ ℕ).tsum_eq (fun p => sigmaTerm q p)]
      exact tsum_congr fun p => by simp [Equiv.prodComm_apply, Prod.swap]
    rw [h1, hswap.tsum_prod]
    exact tsum_congr fun m => (hasSum_sigmaTerm_col hq m).tsum_eq
  have hs₁ : s₁ q = ∑' m : ℕ, term (fun k => k) q (m + 1) := by
    rw [s₁, coeffSum, (summable_term (fun k => k) hq).tsum_eq_zero_add]
    simp
  rw [hs₁, ← hcols, hrows]

theorem pointX_zpow_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (n : ℤ) :
    pointX q (q ^ n * u) = pointX q u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ k ih =>
      have h : q ^ ((k : ℤ) + 1) * u = q * (q ^ (k : ℤ) * u) := by
        rw [zpow_add_one₀ hq0]; ring
      rw [h, TateCurve.pointX_q_mul hq0, ih]
  | pred k ih =>
      have h : q ^ (-(k : ℤ)) * u = q * (q ^ (-(k : ℤ) - 1) * u) := by
        rw [show (-(k : ℤ)) = (-(k : ℤ) - 1) + 1 by ring, zpow_add_one₀ hq0]; ring_nf
      have hstep := TateCurve.pointX_q_mul (q := q) (u := q ^ (-(k : ℤ) - 1) * u) hq0
      rw [← h] at hstep
      rw [← hstep, ih]

theorem pointY_zpow_mul {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (n : ℤ) :
    pointY q (q ^ n * u) = pointY q u := by
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, one_mul]
  | succ k ih =>
      have h : q ^ ((k : ℤ) + 1) * u = q * (q ^ (k : ℤ) * u) := by
        rw [zpow_add_one₀ hq0]; ring
      rw [h, TateCurve.pointY_q_mul hq0, ih]
  | pred k ih =>
      have h : q ^ (-(k : ℤ)) * u = q * (q ^ (-(k : ℤ) - 1) * u) := by
        rw [show (-(k : ℤ)) = (-(k : ℤ) - 1) + 1 by ring, zpow_add_one₀ hq0]; ring_nf
      have hstep := TateCurve.pointY_q_mul (q := q) (u := q ^ (-(k : ℤ) - 1) * u) hq0
      rw [← h] at hstep
      rw [← hstep, ih]


/-! ### The normal forms of the point coordinates -/

section NormalForm

open Filter

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

section SummabilityHelpers

variable [CompleteSpace K] {q : K}

private theorem summable_xfun_pow_mul (hq : ‖q‖₊ < 1) (v : K) :
    Summable fun n : ℕ => xfun (q ^ (n + 1) * v) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have hq' : ‖q‖ < 1 := hq
  have hlim : Tendsto (fun n : ℕ => ‖q‖ ^ (n + 1) * ‖v‖) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq'
    have := (h0.mul_const ‖v‖).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  refine squeeze_zero_norm' ?_ hlim

  filter_upwards [hlim.eventually_lt_const one_pos] with n hn
  have hn' : ‖q ^ (n + 1) * v‖ < 1 := by simpa [norm_mul, norm_pow] using hn
  have hball : ‖q ^ (n + 1) * v‖₊ < 1 := by exact_mod_cast hn'
  have hxb : ‖xfun (q ^ (n + 1) * v)‖₊ ≤ ‖q ^ (n + 1) * v‖₊ := (nnnorm_xfun_of_lt_one hball).le
  calc ‖xfun (q ^ (n + 1) * v)‖ ≤ ‖q ^ (n + 1) * v‖ := by exact_mod_cast hxb
    _ = ‖q‖ ^ (n + 1) * ‖v‖ := by rw [norm_mul, norm_pow]

private theorem summable_yfun_pow_mul (hq : ‖q‖₊ < 1) (v : K) :
    Summable fun n : ℕ => yfun (q ^ (n + 1) * v) := by
  apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
  rw [Nat.cofinite_eq_atTop]
  have hq' : ‖q‖ < 1 := hq
  have hlim : Tendsto (fun n : ℕ => ‖q‖ ^ (n + 1) * ‖v‖) atTop (nhds 0) := by
    have h0 : Tendsto (fun n : ℕ => ‖q‖ ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) hq'
    have := (h0.mul_const ‖v‖).comp (tendsto_add_atTop_nat 1)
    simpa [Function.comp_def] using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hlim.eventually_lt_const one_pos] with n hn
  have hn' : ‖q ^ (n + 1) * v‖ < 1 := by simpa [norm_mul, norm_pow] using hn
  have hball : ‖q ^ (n + 1) * v‖₊ < 1 := by exact_mod_cast hn'
  have hyb : ‖yfun (q ^ (n + 1) * v)‖₊ ≤ ‖q ^ (n + 1) * v‖₊ := by
    rw [nnnorm_yfun_of_lt_one hball]
    calc ‖q ^ (n + 1) * v‖₊ ^ 2 ≤ ‖q ^ (n + 1) * v‖₊ ^ 1 :=
          pow_le_pow_of_le_one zero_le hball.le one_le_two
      _ = ‖q ^ (n + 1) * v‖₊ := pow_one _
  calc ‖yfun (q ^ (n + 1) * v)‖ ≤ ‖q ^ (n + 1) * v‖ := by exact_mod_cast hyb
    _ = ‖q‖ ^ (n + 1) * ‖v‖ := by rw [norm_mul, norm_pow]

end SummabilityHelpers

section TwoSidedSplit

variable [CompleteSpace K] {q u : K}

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem xTerm_neg_add_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (n : ℕ) :
    xTerm q u (-(n + 1)) = xfun (q ^ (n + 1) * u⁻¹) := by
  have h1 : q ^ (n + 1) * u⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0)
  have h2 : q ^ (n + 1) * u⁻¹ ≠ 1 := by
    intro h
    apply hu (-(n + 1))
    have hinv : (q ^ (n + 1) * u⁻¹)⁻¹ = q ^ (-(n + 1) : ℤ) * u := by
      rw [mul_inv, inv_inv, zpow_neg, ← zpow_natCast q (n + 1)]
      push_cast
      ring_nf
    rw [← hinv, h, inv_one]
  have hxinv := xfun_inv h1 h2
  rw [xTerm, ← hxinv, mul_inv, inv_inv, zpow_neg, ← zpow_natCast q (n + 1)]
  push_cast
  ring_nf

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem yTerm_neg_add_one (hq0 : q ≠ 0) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (n : ℕ) :
    yTerm q u (-(n + 1))
      = -yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹) := by
  have h1 : q ^ (n + 1) * u⁻¹ ≠ 0 := mul_ne_zero (pow_ne_zero _ hq0) (inv_ne_zero hu0)
  have h2 : q ^ (n + 1) * u⁻¹ ≠ 1 := by
    intro h
    apply hu (-(n + 1))
    have hinv : (q ^ (n + 1) * u⁻¹)⁻¹ = q ^ (-(n + 1) : ℤ) * u := by
      rw [mul_inv, inv_inv, zpow_neg, ← zpow_natCast q (n + 1)]
      push_cast
      ring_nf
    rw [← hinv, h, inv_one]
  have hyinv := yfun_inv h1 h2
  rw [yTerm, show q ^ (-(n + 1) : ℤ) * u = (q ^ (n + 1) * u⁻¹)⁻¹ by
    rw [mul_inv, inv_inv, zpow_neg, ← zpow_natCast q (n + 1)]; push_cast; ring_nf]
  rw [hyinv]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem xTerm_natCast_add_one (n : ℕ) : xTerm q u ((n : ℤ) + 1) = xfun (q ^ (n + 1) * u) := by
  rw [xTerm, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem yTerm_natCast_add_one (n : ℕ) : yTerm q u ((n : ℤ) + 1) = yfun (q ^ (n + 1) * u) := by
  rw [yTerm, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]

private theorem tsum_xTerm_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    ∑' n : ℤ, xTerm q u n
      = xfun u + ∑' n : ℕ, xfun (q ^ (n + 1) * u) + ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹) := by
  have hsum := summable_xTerm hq0 hq hu0

  have hnat : Summable fun n : ℕ => xTerm q u n :=
    hsum.comp_injective fun a b h => by exact_mod_cast h
  have hneg : Summable fun n : ℕ => xTerm q u (-(n + 1)) := by
    refine hsum.comp_injective fun a b h => ?_
    omega

  rw [tsum_of_nat_of_neg_add_one hnat hneg]

  have hzero : ∑' n : ℕ, xTerm q u n = xfun u + ∑' n : ℕ, xfun (q ^ (n + 1) * u) := by
    rw [hnat.tsum_eq_zero_add]
    congr 1
    · simp
    · exact tsum_congr fun n => by
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, xTerm_natCast_add_one]

  have hnegval : ∑' n : ℕ, xTerm q u (-(n + 1)) = ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹) :=
    tsum_congr fun n => xTerm_neg_add_one hq0 hu0 hu n
  rw [hzero, hnegval]

private theorem tsum_yTerm_eq (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    ∑' n : ℤ, yTerm q u n
      = yfun u + ∑' n : ℕ, yfun (q ^ (n + 1) * u)
        - ∑' n : ℕ, yfun (q ^ (n + 1) * u⁻¹) - ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹) := by
  have hsum := summable_yTerm hq0 hq hu0
  have hnat : Summable fun n : ℕ => yTerm q u n :=
    hsum.comp_injective fun a b h => by exact_mod_cast h
  have hneg : Summable fun n : ℕ => yTerm q u (-(n + 1)) := by
    refine hsum.comp_injective fun a b h => ?_
    omega
  rw [tsum_of_nat_of_neg_add_one hnat hneg]

  have hzero : ∑' n : ℕ, yTerm q u n = yfun u + ∑' n : ℕ, yfun (q ^ (n + 1) * u) := by
    rw [hnat.tsum_eq_zero_add]
    congr 1
    · simp
    · exact tsum_congr fun n => by
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, yTerm_natCast_add_one]

  have hyu : Summable fun n : ℕ => yfun (q ^ (n + 1) * u⁻¹) := summable_yfun_pow_mul hq u⁻¹
  have hxu : Summable fun n : ℕ => xfun (q ^ (n + 1) * u⁻¹) := summable_xfun_pow_mul hq u⁻¹
  have hnegval : ∑' n : ℕ, yTerm q u (-(n + 1))
      = -(∑' n : ℕ, yfun (q ^ (n + 1) * u⁻¹)) - ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹) := by
    have hterm : (fun n : ℕ => yTerm q u (-(n + 1)))
        = fun n : ℕ => -yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹) := by
      funext n; exact yTerm_neg_add_one hq0 hu0 hu n
    rw [hterm, hyu.neg.tsum_sub hxu, tsum_neg]
  rw [hzero, hnegval]
  ring

private theorem pointX_split (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointX q u
      = xfun u + ∑' n : ℕ, xfun (q ^ (n + 1) * u) + ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹)
        - 2 * s₁ q := by
  rw [pointX, tsum_xTerm_eq hq0 hq hu0 hu]

private theorem pointY_split (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) :
    pointY q u
      = yfun u + ∑' n : ℕ, yfun (q ^ (n + 1) * u)
        - ∑' n : ℕ, yfun (q ^ (n + 1) * u⁻¹) - ∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹)
        + s₁ q := by
  rw [pointY, tsum_yTerm_eq hq0 hq hu0 hu]

end TwoSidedSplit

end NormalForm

end TateCurve

theorem TateCurve.pointX_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointX q u = xfun u + ∑' n : ℕ, (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1))) := by
  have hA : Summable fun n : ℕ => xfun (q ^ (n + 1) * u) := summable_xfun_pow_mul hq u
  have hB : Summable fun n : ℕ => xfun (q ^ (n + 1) * u⁻¹) := summable_xfun_pow_mul hq u⁻¹
  have hC : Summable fun n : ℕ => xfun (q ^ (n + 1)) := by
    simpa using summable_xfun_pow_mul hq (1 : K)
  have hcombine : ∑' n : ℕ,
      (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1)))
      = (∑' n : ℕ, xfun (q ^ (n + 1) * u)) + (∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹))
        - 2 * ∑' n : ℕ, xfun (q ^ (n + 1)) := by
    have h2C : HasSum (fun n : ℕ => 2 * xfun (q ^ (n + 1)))
        (2 * ∑' n : ℕ, xfun (q ^ (n + 1))) := hC.hasSum.mul_left 2
    exact ((hA.hasSum.add hB.hasSum).sub h2C).tsum_eq
  rw [pointX_split hq0 hq hu0 hu, hcombine, TateCurve.sOne_eq_tsum_xfun hq0 hq]
  ring
theorem TateCurve.pointY_normalForm {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) : pointY q u = yfun u + ∑' n : ℕ, (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹) + xfun (q ^ (n + 1))) := by
  have hA : Summable fun n : ℕ => yfun (q ^ (n + 1) * u) := summable_yfun_pow_mul hq u
  have hB : Summable fun n : ℕ => yfun (q ^ (n + 1) * u⁻¹) := summable_yfun_pow_mul hq u⁻¹
  have hD : Summable fun n : ℕ => xfun (q ^ (n + 1) * u⁻¹) := summable_xfun_pow_mul hq u⁻¹
  have hC : Summable fun n : ℕ => xfun (q ^ (n + 1)) := by
    simpa using summable_xfun_pow_mul hq (1 : K)
  have hcombine : ∑' n : ℕ,
      (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹)
        + xfun (q ^ (n + 1)))
      = (∑' n : ℕ, yfun (q ^ (n + 1) * u)) - (∑' n : ℕ, yfun (q ^ (n + 1) * u⁻¹))
        - (∑' n : ℕ, xfun (q ^ (n + 1) * u⁻¹)) + ∑' n : ℕ, xfun (q ^ (n + 1)) :=
    (((hA.hasSum.sub hB.hasSum).sub hD.hasSum).add hC.hasSum).tsum_eq
  rw [pointY_split hq0 hq hu0 hu, hcombine, TateCurve.sOne_eq_tsum_xfun hq0 hq]
  ring

/-! ### The rows of the two `q`-expansion pins that this module did not yet carry -/

namespace TateCurve

section QExpansion

open Filter

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem norm_mul_growthBound_lt_one (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1)
    (hqu' : ‖q * u⁻¹‖₊ < 1) : ‖q‖ * growthBound u < 1 := by
  have h1 : ‖q‖ * ‖u‖ < 1 := by
    have h : ‖q * u‖ < 1 := hqu
    rwa [norm_mul] at h
  have h2 : ‖q‖ * ‖u⁻¹‖ < 1 := by
    have h : ‖q * u⁻¹‖ < 1 := hqu'
    rwa [norm_mul] at h
  have h3 : ‖q‖ < 1 := hq
  rw [growthBound, mul_max_of_nonneg _ _ (norm_nonneg q),
    mul_max_of_nonneg _ _ (norm_nonneg q), mul_one]
  exact max_lt (max_lt h1 h2) h3

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nnnorm_pow_mul_lt_one (hq : ‖q‖₊ < 1) (hqv : ‖q * u‖₊ < 1) (n : ℕ) :
    ‖q ^ (n + 1) * u‖₊ < 1 := by
  have hrw : q ^ (n + 1) * u = q ^ n * (q * u) := by ring
  rw [hrw, nnnorm_mul, nnnorm_pow]
  calc ‖q‖₊ ^ n * ‖q * u‖₊ ≤ 1 * ‖q * u‖₊ :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ zero_le hq.le) zero_le
    _ = ‖q * u‖₊ := one_mul _
    _ < 1 := hqv

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem nnnorm_pow_lt_one (hq : ‖q‖₊ < 1) (n : ℕ) : ‖q ^ (n + 1)‖₊ < 1 := by
  rw [nnnorm_pow]
  exact pow_lt_one₀ zero_le hq (Nat.succ_ne_zero n)

private theorem hasSum_yfun_succ {w : K} (hw : ‖w‖₊ < 1) :
    HasSum (fun m : ℕ => (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1)) (yfun w) := by
  have hsummable : Summable fun m : ℕ => (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1) := by
    apply NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero
    rw [Nat.cofinite_eq_atTop]
    have hw' : ‖w‖ < 1 := hw
    have hlim : Filter.Tendsto (fun m : ℕ => ‖w‖ ^ (m + 1)) Filter.atTop (nhds 0) := by
      have h0 : Filter.Tendsto (fun m : ℕ => ‖w‖ ^ m) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg w) hw'
      simpa [Function.comp_def] using h0.comp (Filter.tendsto_add_atTop_nat 1)
    refine squeeze_zero_norm (fun m => ?_) hlim
    calc ‖(((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1)‖
        = ‖(((m + 1).choose 2 : ℕ) : K)‖ * ‖w ^ (m + 1)‖ := norm_mul _ _
      _ ≤ 1 * ‖w ^ (m + 1)‖ :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_natCast_le_one K _)
            (norm_nonneg _)
      _ = ‖w‖ ^ (m + 1) := by rw [one_mul, norm_pow]

  have htsum : ∑' m : ℕ, (((m + 1).choose 2 : ℕ) : K) * w ^ (m + 1) = yfun w := by
    rw [hsummable.tsum_eq_zero_add]
    have h0 : (((0 + 1).choose 2 : ℕ) : K) * w ^ (0 + 1) = 0 := by
      norm_num [show Nat.choose 1 2 = 0 from rfl]
    have hshift : (fun m : ℕ => (((m + 1 + 1).choose 2 : ℕ) : K) * w ^ (m + 1 + 1))
        = fun m : ℕ => (((m + 2).choose 2 : ℕ) : K) * w ^ (m + 2) := by
      funext m
      norm_num
    rw [h0, zero_add, hshift]
    exact (TateCurve.hasSum_yfun hw).tsum_eq
  exact htsum ▸ hsummable.hasSum

omit [CompleteSpace K] in
private theorem hasSum_xRow (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (n : ℕ) :
    HasSum (fun m : ℕ => xDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)))
      (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹) - 2 * xfun (q ^ (n + 1))) := by
  have h1 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu n)
  have h2 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu' n)
  have h3 := (TateCurve.hasSum_xfun (nnnorm_pow_lt_one hq n)).mul_left (2 : K)
  have hcomb := (h1.add h2).sub h3
  have hfun : (fun m : ℕ =>
      ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u) ^ (m + 1)
        + ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        - 2 * (((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1)))
      = fun m : ℕ => xDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)) := by
    funext m
    rw [xDivTerm, mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hfun] at hcomb
  exact hcomb

private theorem hasSum_yRow (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1)
    (n : ℕ) :
    HasSum (fun m : ℕ => yDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)))
      (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹) - xfun (q ^ (n + 1) * u⁻¹)
        + xfun (q ^ (n + 1))) := by
  have h1 := hasSum_yfun_succ (nnnorm_pow_mul_lt_one hq hqu n)
  have h2 := hasSum_yfun_succ (nnnorm_pow_mul_lt_one hq hqu' n)
  have h3 := TateCurve.hasSum_xfun (nnnorm_pow_mul_lt_one hq hqu' n)
  have h4 := TateCurve.hasSum_xfun (nnnorm_pow_lt_one hq n)
  have hcomb := ((h1.sub h2).sub h3).add h4
  have hfun : (fun m : ℕ =>
      (((m + 1).choose 2 : ℕ) : K) * (q ^ (n + 1) * u) ^ (m + 1)
        - (((m + 1).choose 2 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        - ((m + 1 : ℕ) : K) * (q ^ (n + 1) * u⁻¹) ^ (m + 1)
        + ((m + 1 : ℕ) : K) * (q ^ (n + 1)) ^ (m + 1))
      = fun m : ℕ => yDivTerm u (m + 1) * q ^ ((n + 1) * (m + 1)) := by
    funext m
    rw [yDivTerm, mul_pow, mul_pow, ← pow_mul]
    ring
  rw [hfun] at hcomb
  exact hcomb

end QExpansion

end TateCurve

/-
## SET-AF109 insertion: TateCurve.pointX_qExpansion

The `x`-coordinate as a `q`-expansion.

`TateCurve.pointX_qExpansion` (284 pin lines): `pointX q u = xfun u + ∑' N, xCoeff u (N + 1) * q ^ (N + 1)`
for `‖q‖ < 1`, `u ≠ 0`, `q ^ n * u ≠ 1` and `‖q u‖, ‖q u⁻¹‖ < 1`.
-/
theorem TateCurve.pointX_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointX q u = xfun u + ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
  have hC1 := one_le_growthBound u
  have hh : ∀ m : ℕ, 0 < m → ‖xDivTerm u m‖ ≤ growthBound u ^ m :=
    fun m _ => norm_xDivTerm_le u m
  have hrC := norm_mul_growthBound_lt_one hq hqu hqu'
  have hdouble : Summable fun p : ℕ × ℕ =>
      xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    summable_succ_prod hC1 hh hrC
  have hrows : ∑' p : ℕ × ℕ, xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' n : ℕ, (xfun (q ^ (n + 1) * u) + xfun (q ^ (n + 1) * u⁻¹)
          - 2 * xfun (q ^ (n + 1))) := by
    rw [hdouble.tsum_prod]
    exact tsum_congr fun n => (hasSum_xRow hq hqu hqu' n).tsum_eq
  have hdivisors : ∑' p : ℕ × ℕ, xDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, xCoeff u (N + 1) * q ^ (N + 1) := by
    simpa only [xCoeff] using TateCurve.tsum_succ_prod_eq_tsum_divisors hC1 hh hrC
  rw [TateCurve.pointX_normalForm hq0 hq hu0 hu, ← hrows, hdivisors]

/-
## SET-AF109 insertion: TateCurve.pointY_qExpansion

The `y`-coordinate as a `q`-expansion.

`TateCurve.pointY_qExpansion` (284 pin lines): `pointY q u = yfun u + ∑' N, yCoeff u (N + 1) * q ^ (N + 1)`,
the `y`-companion of the row above. The two pin files are the same proof with `x` interchanged for `y`:
their shared fifteen-row regrouping prelude (`pairTerm`, `sigmaTerm'`, `norm_le_of_le_geometric`,
`summable_sigmaTerm'`, `summable_pairTerm`, `tsum_pairTerm_eq_tsum_divisors`, `succEquivPNat`,
`tsum_succ_prod_eq_tsum_divisors_loc`, `summable_succ_prod_loc`, `norm_mul_growthBound_lt_one`,
`nnnorm_pow_mul_lt_one`, `nnnorm_pow_lt_one`, `hasSum_yfun_succ`, `hasSum_xRow`, `hasSum_yRow`) is
written **once** here, private, beside the six rows of the same shape this module already carries for
`sOne_eq_tsum_xfun` (`pairTerm`, `sigmaTerm'`, `summable_sigmaTerm'`, `summable_pairTerm`,
`tsum_pairTerm_eq_tsum_divisors`, `succEquivPNat` and the `_main`/`summable_succ_prod` pair); the
coefficients `xCoeff`/`yCoeff` are `TateCurve/Tails.lean`'s.
-/
theorem TateCurve.pointY_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointY q u = yfun u + ∑' N : ℕ, yCoeff u (N + 1) * q ^ (N + 1) := by
  have hC1 := one_le_growthBound u
  have hh : ∀ m : ℕ, 0 < m → ‖yDivTerm u m‖ ≤ growthBound u ^ m :=
    fun m _ => norm_yDivTerm_le u m
  have hrC := norm_mul_growthBound_lt_one hq hqu hqu'
  have hdouble : Summable fun p : ℕ × ℕ =>
      yDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    summable_succ_prod hC1 hh hrC
  have hrows : ∑' p : ℕ × ℕ, yDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' n : ℕ, (yfun (q ^ (n + 1) * u) - yfun (q ^ (n + 1) * u⁻¹)
          - xfun (q ^ (n + 1) * u⁻¹) + xfun (q ^ (n + 1))) := by
    rw [hdouble.tsum_prod]
    exact tsum_congr fun n => (hasSum_yRow hq hqu hqu' n).tsum_eq
  have hdivisors : ∑' p : ℕ × ℕ, yDivTerm u (p.2 + 1) * q ^ ((p.1 + 1) * (p.2 + 1))
      = ∑' N : ℕ, yCoeff u (N + 1) * q ^ (N + 1) := by
    simpa only [yCoeff] using TateCurve.tsum_succ_prod_eq_tsum_divisors hC1 hh hrC
  rw [TateCurve.pointY_normalForm hq0 hq hu0 hu, ← hrows, hdivisors]

/-! ### The rows of the `defect_qExpansion` pin that this module did not yet carry -/

namespace TateCurve

section CoeffSumExpansion

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q : K}

omit [IsUltrametricDist K] [CompleteSpace K] in
private theorem hasSum_term_succ (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) (n : ℕ) :
    HasSum (fun m : ℕ => ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1))) (term c q (n + 1)) := by
  have hqn : ‖q ^ (n + 1)‖ < 1 := by
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg q) (show ‖q‖ < 1 from hq) (Nat.succ_ne_zero n)
  have h2 := (hasSum_geometric_of_norm_lt_one hqn).mul_left ((c (n + 1) : K) * q ^ (n + 1))
  have hfun : (fun m : ℕ => (c (n + 1) : K) * q ^ (n + 1) * (q ^ (n + 1)) ^ m)
      = fun m : ℕ => ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1)) := by
    funext m
    rw [Nat.mul_comm (m + 1) (n + 1), pow_mul, pow_succ]
    ring
  rw [hfun] at h2
  have hval : (c (n + 1) : K) * q ^ (n + 1) * (1 - q ^ (n + 1))⁻¹ = term c q (n + 1) := by
    rw [term, div_eq_mul_inv]
    ring
  rwa [hval] at h2

private theorem coeffSum_qExpansion (c : ℕ → ℕ) (hq : ‖q‖₊ < 1) :
    coeffSum c q = ∑' N : ℕ, (∑ d ∈ (N + 1).divisors, (c d : K)) * q ^ (N + 1) := by
  have hC1 : (1 : ℝ) ≤ 1 := le_refl 1
  have hh : ∀ m : ℕ, 0 < m → ‖((c m : ℕ) : K)‖ ≤ (1 : ℝ) ^ m := fun m _ => by
    rw [one_pow]; exact IsUltrametricDist.norm_natCast_le_one K (c m)
  have hrC : ‖q‖ * 1 < 1 := by rw [mul_one]; exact_mod_cast hq

  have hengine := tsum_succ_prod_main (h := fun d => (c d : K)) (r := q) hC1 hh hrC
  have hdouble : Summable fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    (summable_succ_prod (h := fun d => (c d : K)) (r := q) hC1 hh hrC).congr fun p => rfl
  have hGsum : Summable fun p : ℕ × ℕ => ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    ((Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).mpr hdouble).congr fun p => rfl

  have hA : coeffSum c q = ∑' n : ℕ, term c q (n + 1) := by
    rw [coeffSum, (summable_term c hq).tsum_eq_zero_add, term_zero, zero_add]
  have hB : ∑' n : ℕ, term c q (n + 1)
      = ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1)) :=
    tsum_congr fun n => ((hasSum_term_succ c hq n).tsum_eq).symm
  have hC : ∑' n : ℕ, ∑' m : ℕ, ((c (n + 1) : K)) * q ^ ((m + 1) * (n + 1))
      = ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1)) :=
    (hGsum.tsum_prod).symm
  have hD : ∑' p : ℕ × ℕ, ((c (p.1 + 1) : K)) * q ^ ((p.2 + 1) * (p.1 + 1))
      = ∑' p : ℕ × ℕ, ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)) :=
    Equiv.tsum_eq (Equiv.prodComm ℕ ℕ)
      (fun p : ℕ × ℕ => ((c (p.2 + 1) : K)) * q ^ ((p.1 + 1) * (p.2 + 1)))
  rw [hA, hB, hC, hD]
  exact hengine

omit [CompleteSpace K] in
private theorem summable_norm_a₄Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₄Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₄Coeff_le N

omit [CompleteSpace K] in
private theorem summable_norm_a₆Series (hq : ‖q‖₊ < 1) :
    Summable fun N => ‖a₆Coeff (K := K) N * q ^ N‖ := by
  refine summable_norm_qSeries (B := 1) (C := 1) zero_le_one (fun N => ?_)
    (by rw [mul_one]; exact_mod_cast hq)
  rw [one_mul, one_pow]
  exact norm_a₆Coeff_le N

variable {u : K}

omit [CompleteSpace K] in
private theorem summable_norm_xSeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖xCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_xCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

omit [CompleteSpace K] in
private theorem summable_norm_ySeries (hq : ‖q‖₊ < 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    Summable fun N => ‖yCoeffFull u N * q ^ N‖ :=
  summable_norm_qSeries (growthBound_nonneg u) (norm_yCoeffFull_le u)
    (norm_mul_growthBound_lt_one hq hqu hqu')

private theorem pointX_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointX q u = ∑' N : ℕ, xCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => xCoeffFull u N * q ^ N :=
    (summable_norm_xSeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [xCoeffFull_zero, xCoeffFull_succ, pow_zero, mul_one]
  exact TateCurve.pointX_qExpansion hq0 hq hu0 hu hqu hqu'

private theorem pointY_eq_tsum (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u = ∑' N : ℕ, yCoeffFull u N * q ^ N := by
  have hsum : Summable fun N => yCoeffFull u N * q ^ N :=
    (summable_norm_ySeries hq hqu hqu').of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [yCoeffFull_zero, yCoeffFull_succ, pow_zero, mul_one]
  exact TateCurve.pointY_qExpansion hq0 hq hu0 hu hqu hqu'

private theorem a₄_eq_tsum (hq : ‖q‖₊ < 1) : a₄ q = ∑' N : ℕ, a₄Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₄Coeff (K := K) N * q ^ N := (summable_norm_a₄Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₄Coeff_zero, a₄Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((5 * d ^ 3 : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion (fun n => 5 * n ^ 3) hq, a₄]

private theorem a₆_eq_tsum (hq : ‖q‖₊ < 1) : a₆ q = ∑' N : ℕ, a₆Coeff (K := K) N * q ^ N := by
  have hsum : Summable fun N => a₆Coeff (K := K) N * q ^ N := (summable_norm_a₆Series hq).of_norm
  rw [hsum.tsum_eq_zero_add]
  simp only [a₆Coeff_zero, a₆Coeff_succ, zero_mul, zero_add]
  have hexp : ∑' N : ℕ, (-(∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K))) * q ^ (N + 1)
      = -(∑' N : ℕ, (∑ d ∈ (N + 1).divisors, ((b d : ℕ) : K)) * q ^ (N + 1)) := by
    rw [← tsum_neg]
    exact tsum_congr fun N => by rw [neg_mul]
  rw [hexp, ← coeffSum_qExpansion b hq, a₆]

end CoeffSumExpansion

section MainProof

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {q u : K}

private theorem defect_qExpansion_loc (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0)
    (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) :
    pointY q u ^ 2 + pointX q u * pointY q u
      - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q)
      = ∑' N : ℕ, defectCoeff u N * q ^ N := by

  have hXn := summable_norm_xSeries (u := u) hq hqu hqu'
  have hYn := summable_norm_ySeries (u := u) hq hqu hqu'
  have hA4n := summable_norm_a₄Series (K := K) hq
  have hA6n := summable_norm_a₆Series (K := K) hq
  have hXXn := summable_norm_cauchyMul hXn hXn

  have hX := pointX_eq_tsum hq0 hq hu0 hu hqu hqu'
  have hY := pointY_eq_tsum hq0 hq hu0 hu hqu hqu'
  have hA4 := a₄_eq_tsum (K := K) hq
  have hA6 := a₆_eq_tsum (K := K) hq

  have hYY : pointY q u ^ 2
      = ∑' N : ℕ, cauchyMul (yCoeffFull u) (yCoeffFull u) N * q ^ N := by
    rw [pow_two, hY, qSeries_mul hYn hYn]
  have hXY : pointX q u * pointY q u
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (yCoeffFull u) N * q ^ N := by
    rw [hX, hY, qSeries_mul hXn hYn]
  have hXX : pointX q u * pointX q u
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (xCoeffFull u) N * q ^ N := by
    rw [hX, qSeries_mul hXn hXn]
  have hX3 : pointX q u ^ 3
      = ∑' N : ℕ, cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N * q ^ N := by
    rw [show pointX q u ^ 3 = pointX q u * (pointX q u * pointX q u) by ring, hXX, hX,
      qSeries_mul hXn hXXn]
  have hA4X : a₄ q * pointX q u
      = ∑' N : ℕ, cauchyMul a₄Coeff (xCoeffFull u) N * q ^ N := by
    rw [hA4, hX, qSeries_mul hA4n hXn]

  have sYY : Summable fun N => cauchyMul (yCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hYn hYn).of_norm
  have sXY : Summable fun N => cauchyMul (xCoeffFull u) (yCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hXn hYn).of_norm
  have sX3 : Summable fun N =>
      cauchyMul (xCoeffFull u) (cauchyMul (xCoeffFull u) (xCoeffFull u)) N * q ^ N :=
    (summable_norm_cauchyMul hXn hXXn).of_norm
  have sA4X : Summable fun N => cauchyMul a₄Coeff (xCoeffFull u) N * q ^ N :=
    (summable_norm_cauchyMul hA4n hXn).of_norm
  have sA6 : Summable fun N => a₆Coeff (K := K) N * q ^ N := hA6n.of_norm

  have tsum_add_combine : ∀ {f g : ℕ → K}, (Summable fun N => f N * q ^ N) →
      (Summable fun N => g N * q ^ N) →
      (∑' N : ℕ, f N * q ^ N) + (∑' N : ℕ, g N * q ^ N) = ∑' N : ℕ, (f N + g N) * q ^ N := by
    intro f g hf hg
    rw [← hf.tsum_add hg]
    exact tsum_congr fun N => (add_mul _ _ _).symm
  have tsum_sub_combine : ∀ {f g : ℕ → K}, (Summable fun N => f N * q ^ N) →
      (Summable fun N => g N * q ^ N) →
      (∑' N : ℕ, f N * q ^ N) - (∑' N : ℕ, g N * q ^ N) = ∑' N : ℕ, (f N - g N) * q ^ N := by
    intro f g hf hg
    rw [← hf.tsum_sub hg]
    exact tsum_congr fun N => (sub_mul _ _ _).symm

  rw [hYY, hXY, hX3, hA4X, hA6,
    tsum_add_combine sYY sXY, tsum_add_combine sX3 sA4X,
    tsum_add_combine ((sX3.add sA4X).congr fun N => (add_mul _ _ _).symm) sA6,
    tsum_sub_combine ((sYY.add sXY).congr fun N => (add_mul _ _ _).symm)
      (((sX3.add sA4X).congr fun N => (add_mul _ _ _).symm).add sA6 |>.congr
        fun N => (add_mul _ _ _).symm)]
  exact tsum_congr fun N => by rw [defectCoeff]

end MainProof

end TateCurve

/-
## SET-AF110 insertion: TateCurve.defect_qExpansion

The Weierstrass defect of a point is a `q`-series with the defect coefficients.

`TateCurve.defect_qExpansion` (368 pin lines): the defect `pointY ^ 2 + pointX * pointY - (pointX ^ 3 +
a₄ * pointX + a₆)` of `(pointX q u, pointY q u)` is `∑' N, defectCoeff u N * q ^ N`. It is the
*arithmetic* half of the point-coordinate dictionary SET-AF109F started: its two inputs are this
module's two `q`-expansions (order F) and `TateCurve/Defect.lean`'s coefficient layer
(`xCoeffFull`/`yCoeffFull`/`a₄Coeff`/`a₆Coeff`/`defectCoeff` and the Cauchy-product ring), which is why
the def layer landed first.
-/
theorem TateCurve.defect_qExpansion {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {q u : K} (hq0 : q ≠ 0) (hq : ‖q‖₊ < 1) (hu0 : u ≠ 0) (hu : ∀ n : ℤ, q ^ n * u ≠ 1) (hqu : ‖q * u‖₊ < 1) (hqu' : ‖q * u⁻¹‖₊ < 1) : pointY q u ^ 2 + pointX q u * pointY q u - (pointX q u ^ 3 + a₄ q * pointX q u + a₆ q) = ∑' N : ℕ, defectCoeff u N * q ^ N :=
  defect_qExpansion_loc hq0 hq hu0 hu hqu hqu'

/-
## SET-AF110 insertion: TateCurve.defectCoeff_zero

The defect coefficient's constant term vanishes away from `u = 1`.

`TateCurve.defectCoeff_zero` (13 pin lines): for `u ≠ 1`, `defectCoeff u 0 = 0` — the constant term of
the defect series is the Weierstrass defect of the `q`-free point `(xfun u, yfun u)`, which lies on the
curve. The companion of the row above, and the reason the series starts at `q ^ 1`.
-/
theorem TateCurve.defectCoeff_zero {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] {u : K} (hu1 : u ≠ 1) : defectCoeff u 0 = 0 := by
  have hnodal := TateCurve.nodal_xfun_yfun (K := K) (w := u) hu1
  simp only [defectCoeff, cauchyMul_zero, xCoeffFull_zero, yCoeffFull_zero, a₄Coeff_zero,
    a₆Coeff_zero, zero_mul, add_zero]
  linear_combination hnodal

