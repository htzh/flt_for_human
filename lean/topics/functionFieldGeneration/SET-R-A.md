# SET-R-A — the Γ₀-rationality pair, engine written once

**Status: done and verified (2026-10-08).** First coding set of the qexp head.
Authorizes exactly **one new module**. Planning record:
[TOPIC-qexp-rationality-degree-head.md](TOPIC-qexp-rationality-degree-head.md) —
read §1 (the two statements), §3 (audited reuse), §4 (dedup), §5 (module layout),
§7 item 2 (the hub prohibition), §8 (verification) before touching Lean.

**Deliverable.** `FLTForHuman/ModularForms/WeightOne/RationalityDvd.lean`: the
shared engine of targets 1 and 3 together with the two headline theorems.

| headline | wrapper (statement authority) | proof source |
|---|---|---|
| `ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd` | `Theorems/Thm_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean` | `P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean` (1,388) |
| `ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion` | `Theorems/Thm_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean` | `P2M/Sol/S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean` (1,196) |

**Reserved for the manager (do not start).** SET-R-B (`XH/Relrank.lean`),
SET-R-C (`X1/FunctionFieldDegree.lean`, `X1/FunctionFieldResidue.lean`). If a
proof seems to need one of them, prove a local `private` helper and report; do
not open a second module.

## 0. What earlier sets handed over (verified)

* The **C′ cone** (`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`
  and its 53 nodes) is 53/53 ported, and the four WeightOne hub promotions below
  are public.
* **The hub promotions already made**: `Gamma0Rationality.lean` —
  `tσ_lift`, `exists_discSeries`, `aeval_relPoly`, `map_phiOf_eq_of_rat`;
  `Gamma1Basis.lean` — `qExpansion_disc_rat_one`,
  `qExpansion_widthN_rat_of_levelOne`. Import them; do not re-prove.
* The `X1DiamondRational` engine in
  `Defs/GammaRational.lean` (102 public rows), the `RatAt` predicate in
  `Defs/RatAt.lean` (33), and `Defs/Gamma.lean` are the reuse base. Import.
* Checker baseline at dispatch: **6602 identical (312 promoted, 83 renamed),
  0 mismatched, 0 missing, 36 own (6638 checked)**.

## 1. Source of truth

* Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem`.
  Read it; never modify it.
* **Statement = the `Theorems/Thm_<stem>.lean` wrapper.** Take the binders from
  it, verbatim. Proof = the matching `P2M/Sol/S_<stem>.lean`.
* The two `S_` files are already in `SOURCES` (their helpers are pin copies);
  the two wrappers are **not** — append them (§5).
* Dedup (`tools/deps/build/next5_advise.txt` §2, `next5_plan.txt` §blocks): the
  pair shares a **683-line / 65-declaration block, 661 lines of which are already
  in the port**. Write that block **once** in `RationalityDvd.lean` and keep the
  two headlines as its consumers. The largest duplicated names are
  `exists_rat_combination`, `qExpansion_coeff_widthN`, `tauPair`, `exists_map`,
  `qExpansion_coeff_unique'`, `Gamma_le_Gamma1`,
  `intSeriesC_ne_zero_of_constantCoeff`.
* Reuse (do not re-port): the substitution table of
  `tools/deps/build/next5_advise.txt` §1 lists 264 rows already statement-identical
  in the port, 185 of them public.

## 2. Build discipline — read and obey first

`lake env lean <file>` is the edit loop; `lake build <module>` when the file is
done; **one** build at the set boundary; the whole-tree build is the manager's,
not this set's.

* Bound every build: `timeout 300 lake env lean -DmaxHeartbeats=4000000
  -DautoImplicit=false <file>` (this module imports the big WeightOne oleans),
  `flock .lake/flt_build.lock timeout 300 lake build <module>`.
* **Never raise `maxHeartbeats`/`maxRecDepth`** (lakefile cap is `4000000`) and
  never re-run past a bound. On a timeout, quarantine the declaration and bisect
  in the gitignored `Scratch.lean`; then report.
* Tell a blow-up from contention with CPU time: high user CPU + timeout is real;
  ~0 CPU wall is another agent's build lock.
* Build serially. Do not start a whole-tree `lake build`. Do not commit.

## 3. The hub prohibition (manager instruction, 2026-10-08)

**Do not edit any existing module.** In particular do not touch
`ModularForms/WeightOne/Defs/GammaRational.lean`,
`Defs/RatAt.lean`, `Defs/Gamma.lean`, `Gamma0Rationality.lean`,
`Gamma0Integral.lean`, `Gamma1Basis.lean`, `Gamma1IntegralBasis.lean`,
`JqIntegralRatios.lean`, `DeligneSerre/Lifting.lean`, or any other file already
in the tree — not even to remove a `private`.

If a needed helper is `private` in one of those modules, **re-derive it locally
as a `private` helper in `RationalityDvd.lean`** (they are 2–14 lines each) and
list it in the completion report. If you believe a promotion is genuinely
required (the helper carries real mathematics and a later set will need it by
name), **stop and report** with the declaration, its host, the reason, and the
priced cascade from `python3 tools/deps/build_ladder.py --edit <host>`; the
manager decides.

## 4. Conventions

1. Statements verbatim from the wrappers; binders included; namespace
   `ModularCurve`/`ModularForm` as the pin has them.
2. Specific imports; no `import Mathlib`.
3. Public surface: the two headlines plus any declaration the pin makes public
   and the engine genuinely exports. Pin-private helpers the port needs become
   `private`.
4. No `sorry`/`admit`; 0 warnings.
5. `#print axioms` on both headlines must be
   `[propext, Classical.choice, Quot.sound]`.

## 5. Wiring

In `lean/spec/check_flt_statements.py`:

* append the two wrappers to `SOURCES` **last**, with a comment (the two `S_`
  files are already listed; the wrappers are the comparable copies of the
  headlines, whose `S_` copies are named `solution`);
* append `"FLTForHuman/ModularForms/WeightOne/RationalityDvd.lean"` to
  `PORT_FILES`, **last**.
* Target **0 mismatched, 0 missing**. Verify with a one-token mutation on one
  headline (expect exactly one more `mismatched`) and revert.

## 6. Stop and report

* a wrapper/`S_` statement disagreement (quote both; do not weaken a statement);
* a needed helper that is `private` in a hub **and is real mathematics** — stop
  before promoting;
* a declaration that needs `tσ_lift`-adjacent machinery not already in the port;
* a build past its bound (report the declaration and the CPU time);
* any reason to touch a file other than the new module and the checker lists.

## 7. Completion report

1. the module path and the declaration count (public / `private`);
2. the local `private` re-derivations you made, with their hosts;
3. the tier 0 / tier 1 results and wall/CPU times;
4. the checker counts before → after, and the mutation-test result;
5. `#print axioms` output for the two headlines;
6. anything you could not match, quoted.

## 8. Outcome (2026-10-08, landed and manager-verified)

`ModularForms/WeightOne/RationalityDvd.lean`, 1,204 lines: **50 public** (48 new
pin declarations + the 2 headlines) and **14 `private`**. Both headlines verbatim;
checker **6602 → 6652 identical, 0 mismatched, 0 missing** (+50); mutation test on
headline 2 gave exactly `1 mismatched` and was reverted. Tier 0 green
(23.7 s wall), tier 1 green (29.9 s, 4,127 jobs); `#print axioms` clean on both.
No hub was edited; the 14 private re-derivations are listed in the dispatch
report. **Manager ruling (2026-10-08): use the public declarations where they
exist.** Three of the 14 *are* public, only under deep `WLightS*` namespaces
(`Gamma1Basis.lean:2835`, `LevelN.lean:1266`, `Gamma0Rationality.lean:1137`);
the cleanup is carried as SET-R-B §0a (consumer-side only; no hub edit).
**Outcome:** `cw_ne_zero` deleted (both sites use the public declaration);
`kN_eq` and `mdifferentiable_jf` stay as local declarations whose bodies delegate
to the public theorems, since the hub forms are not drop-ins (a private `kN`; an
extra `hjf` binder). Module now **50 public / 13 private**; checker unchanged.

Working tree at hand-off: `spec/check_flt_statements.py` modified (+12) and
`RationalityDvd.lean` added. Nothing committed.
