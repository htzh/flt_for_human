# The `AutomorphicForm.LocalIntertwining` Weyl-integrand cluster

The D-S cone's local-intertwining column: the pin's `AutomorphicForm.LocalIntertwining.*` nodes, 19
`S_` files, none of them ported. The two named entries
`AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion` and
`AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion` are the head of the
cluster and the subject of this note; the other seventeen are scheduled after them (§7).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`. Method: [porting-playbook.md](../../porting-playbook.md) §2.3, §3.3–§3.5, §4.

**Status.** **Both named nodes are LANDED; this topic is closed out** (§11).

* Set 0 — the definition layer: `TateGlobal/WeylPrelude.lean`, 21 declarations, tier-1 green.
* Set LI-1 ([WORKORDER-LI1-weyl-unramified.md](WORKORDER-LI1-weyl-unramified.md)): the residual
  prelude in `TateGlobal/WeylShell.lean` (29 public + 1 private) and the unramified headline in
  `TateGlobal/WeylUnramified.lean` (2 public).
* Set LI-2 ([WORKORDER-LI2-weyl-smooth.md](WORKORDER-LI2-weyl-smooth.md)): the smooth headline in
  `TateGlobal/WeylSmooth.lean` (2 public + 27 private). Its hypothesis names
  `LanglandsTunnell.TateLocal.higherUnitsAt`, a pin `Definitions/` declaration with no other port
  home; it was transcribed with the headline and is wired against
  `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`.

All five modules are in `PORT_FILES` with both nodes' `Theorems/` wrappers and `S_` files in
`SOURCES`, and the checker reads **9654 identical / 670 promoted / 0 mismatched / 0 missing / 38 own
(9692 checked)**. `spec/LocalIntertwiningConsumer.lean` elaborates (exit 0) with a zone per set. The
other seventeen nodes are open and carry forward (§11). Every number in §2 is from
`tools/deps/port_advise.py` + `port_plan.py` on the cluster (§10).

## 1. What the two nodes are

They are **not twins in content**, only in the prelude they re-carry and in their names. Both pin
files open with the same four-section T1 prelude — `FinGKFold_ValuationOrd` (the DVR order block),
`FinGKFold_LocalHaarModulus`, `FinGKFold_LocalZetaUnramified`, `FinGKFold_MulHaarFromAdditive`,
`FinGKFold_ValuedOrdBridge` — and differ from each other only at the end:

| | `…_unramified…` | `…_smooth…` |
|---|---:|---:|
| pin lines | 2,110 | 2,044 |
| declarations (public / private) | 128 (114 / 14) | 114 (1 / 113) |
| public surface the checker would see | **114** | **1** |
| same-file closure of the headline | 13 helpers (~128 lines) | 94 helpers (~1,676 lines) |
| of those new | 2 | 47 |

So `unramified` is a **public theory** of the unramified local intertwining integral — the new
content is its public API, and only `map_maximalIdeal_ringEquiv` (18 lines) and `ordA_ringEquiv`
(11) are new private helpers. `smooth` is **one heavy theorem with a private development**:
`integral_smoothWeylIntegrand_impl` (125 lines) plus `mem_shellSet_iff_ord_eq` (86),
`measurableSet_negShell` (63), `continuousOn_charExt_inv` (55), `setIntegral_units_smul` (51),
`ofReal_pow_cpow` (46) and 41 more.

The shared prelude is the pin re-carrying the whole T1 cluster into both files. The port already
has it, module for module: `TateGlobal/Ideles.lean` and `RingTheory/DiscreteValuationRing/Order.lean`
for the order block, `TateGlobal/{Coordinates,DistribHaarChar}.lean` for `LocalHaarModulus`,
`TateGlobal/LocalZetaUnramified.lean`, `TateGlobal/MulHaar.lean`,
`TateGlobal/ValuedOrdBridge.lean`. What the port lacks is the minority of prelude declarations the
T1 port did not need — and the definitions, which Set 0 has now supplied.

## 2. Measurements

Two-file slice (the two named nodes and their `Theorems/` wrappers):

| | value |
|---|---:|
| raw `S_` lines | 4,154 |
| duplicate copies removable by porting once | 1,317 |
| distinct declaration groups | 152 |
| once-cost after dedup | 2,802 |
| already in the port | 940 (185 tier 1, 755 tier 3) |
| **net new math lines** | **1,862** |
| substitutions | 127 trusted / 0 suspect |

Shared block between the two files: **84 declarations, 1,644 lines once, 1,008 of them already in
the port.** Its top members are `mem_shellSet_iff_ord_eq` (96), `valued_coe_units_eq_exp_neg_ord`
(76), `exists_irreducible_valued` (73), `ord_eq_zero_iff` (67), `ord_piUnit` (66),
`measurableSet_negShell` (63). The pin proves `exists_irreducible_valued` 8× and `ord_eq_zero_iff`
8× across the cluster.

Whole cluster (all 19 nodes): 9,202 raw lines; 1,580 duplicate copies; once-cost 7,287; 951 already
in the port; **net new 6,336 lines / 423 groups**; 132 substitutions (30 tier 1, 102 tier 3). Three
shared blocks: the 84 above, a 5-declaration block in the `finiteAdeleRing` file (111 once, 11 in
port), a 13-declaration block across `weylShift`/`integrable_smoothAtom` (94 once, 0 in port). The
cluster's own import order is three layers: 11 files at layer 0 (both named nodes among them), 7 at
layer 1, and `integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` at
layer 2.

## 3. Set 0 — the definition layer (**LANDED**)

`FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylPrelude.lean`, namespace
`NumberField.TateGlobal.WeylPrelude`, 21 declarations, every one carrying its pin provenance in a
`-- pin:` comment:

* `normQ` and the modulus bridge — `normQ`, `one_le_normQ`, `modulus_coe_units_adicCompletion`,
  `modulus_of_ne_zero_adicCompletion`, `modulus_of_mem_shellSet`, `modulus_of_mem_negShell`;
* the shell API the T1 port did not need — `shellSet_subset_compl_zero`, `shellSet_disjoint`;
* the integers/order bridge — `coe_mem_integers_iff_ord_nonneg`;
* the character block — `valued_eq_one_of_ord_eq_zero`, `ord_eq_one_of_valued`,
  `char_eq_one_of_ord_eq_zero`, `char_eq_zpow_of_ord`, `char_eq_char_piUnit`;
* the negative shell — `negShell`, `ne_zero_of_mem_negShell`, `ord_of_mem_negShell`,
  `compl_integers_eq_iUnion_negShell`, `negShell_disjoint`, `measurableSet_negShell`;
* `eulerVar`.

These are exactly the definitions and immediate support that both named files (and the rest of the
cluster) need; with them, **every `def`/`abbrev` in the two pin files has a port counterpart**:
`ordA`/`ordZ`/`ord` are `IsDiscreteValuationRing.{ordA,ordZ,ord}`, `cosetMap` is in
`TateGlobal/Coordinates.lean`, `normQ`/`piUnit`/`shellSet`/`genShell`/`mulHaar`/`negShell`/`eulerVar`
are in the port or in this module.

One recorded deviation: `one_le_normQ` is proved through `FrobeniusDensity.one_le_absNorm` instead
of the pin's `card_residueField_eq_absNorm` chain, so `card_residueField_eq_absNorm` /
`card_residueField_pos` are **not** ported. The statement is the pin's; only the proof route
differs, which the statement checker does not see.

The module was tier 3 until Set LI-1 wired it: with it in `PORT_FILES` its 21 declarations diff
clean, once `norm()` learned the recorded rename (§8).

## 4. Set 0b — the residual prelude

The lemmas the `WeylGK` section needs and the port still lacks, all in the two files' prelude
sections and none of them a definition. Grouped by the pin section they come from:

* from `FinGKFold_LocalZetaUnramified` / `Measures` / `Integrand` / `Zeta`:
  `integers_diff_zero_eq_iUnion`, `measure_shellSet`, `measure_smul_integers_pow`,
  `setIntegral_shellSet_const`, `mulMeasure_restrict_shellSet`, `mulMeasure_shellSet_lt_top`,
  `charExt_of_mem_shellSet`, `charExt_inv_of_mem_negShell`, `integrableOn_negShell`,
  `setIntegral_negShell`, `setIntegral_norm_negShell`, `measure_negShell` /
  `measure_negShell_lt_top` / `measureReal_negShell`, `integrand_eqOn_negShell`,
  `eqOn_integrand_shellSet`, `indicator_integrand`, `localZeta_indicator_integers`,
  `hasSum_localZeta_indicator`, `smul_integers_subset`/`smul_integers_succ_subset`;
* from `FinGKFold_ValuedOrdBridge`: `valued_coe_ne_zero`, `valued_zpow_piUnit`;
* from `FinGKFold_WeylGK`: `cpow_qpow_bridge` (the `(q ^ -k) ^ s` bridge the smooth side needs);
* the unramified-only `ord` refinement — `ordA_ringEquiv`, `map_maximalIdeal_ringEquiv`,
  `ordA_unit`, `ord_surjective`, `ord_units_map_of_mem_decompositionSubgroup`;
* the smooth-only tail — `genShell_neg_eq_smul`, `genShell_zero_eq`, `genShell_subset_compl_zero`,
  `modulus_of_mem_genShell`, `isCompact_genShell`, `isCompact_shellSet_zero`, `normQ_pos`,
  `ord_inv_pow`, `modulus_inv_pow_mul`, `setOf_valued_eq_genShell`,
  `setOf_valued_eq_one_eq_genShell`, `smul_shellSet_zero_of_ord_eq_zero`, `zero_notMem_genShell`,
  `distribHaarChar_inv_pow`, `integrableOn_genShell`, `integrand_inv_pow_mul`, `apply_inv_eq_apply_zero_of_depth`,
  `continuous_of_depth`, `continuousOn_charExt_inv`.

Home: extend `WeylPrelude.lean` if a declaration is shared by more than one set, otherwise the set's
own module. Do not open a set that needs a member of this list before that member lands — the wave
is cheaper once, here.

**One promotion is owed before either set imports its prelude:**
`NumberField.TateGlobal.MulHaarFromAdditive.isOpenEmbedding_val` is `private` in
`TateGlobal/MulHaar.lean` and both files need it (11 lines). Promote it or move it next to its
siblings in `WeylPrelude.lean`.

## 5. Set 1 — `integral_unramifiedWeylIntegrand_adicCompletion` (public theory)

114 public declarations, 2 new private helpers, all prelude already in the port or in §4. This is a
**definitions-first theory set**: home the public block in one or two modules under
`NumberTheory/NumberField/TateGlobal/` (the pin's own `Weil`/`Unramified` naming, natural-named, no
`M4aP2DGK`/`FinGK`/`WeylGK` prefixes), declare the headline at the pin wrapper's binders, and let the
private helpers stay `private` in the file that uses them.

Work order shape: scope the 114 declarations by subject (the `char*`/`valued*` API, the negative-shell
measure theory, the `setIntegral`/`hasSum` Euler-factor evaluation, the headline); pin sources are
`S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean` for the
proofs and `Theorems/Thm_…_unramified…lean` for the statement; route: every prelude name already has
a port home (§1, §3, §4); deliverable: the module(s) plus `SOURCES`/`PORT_FILES` entries.

Wiring: append the `Theorems/` wrapper and the `S_` file to `SOURCES`, the new module(s) **and**
`TateGlobal/WeylPrelude.lean` to `PORT_FILES`, both last. Expect the checker delta to equal the new
public surface, and expect the 22 name clashes listed in §8 to resolve as substitutions once the
rewritten `SOURCES` normalises them.

## 6. Set 2 — `integral_smoothWeylIntegrand_adicCompletion` (one heavy theorem) — **LANDED**

`FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylSmooth.lean`: 2 public + 27 private, 721 lines,
tier-1 green and warning-free. The headline is the only checker wire (plus `higherUnitsAt`, §11).

The estimate below held: 67 of the file's 94 helpers were imports, not re-proofs, and the work was
the genuine tail. The private helpers stayed `private`; the one deliberate re-proof is
`ofReal_pow_cpow`, whose `WeylShell` copy is `private` and therefore not importable. The pin's
implementation lemma is private here too (in its twin, LI-1's, it was public), so the port exposes
only the headline.

The estimates as planned: 1 public declaration, 94 private helpers (~1,676 lines; 47 new, 67 shared
with LI-1's file), the new tail being `integral_smoothWeylIntegrand_impl` (125),
`continuousOn_charExt_inv` (55), `setIntegral_units_smul` (51) and the
`setIntegral_{lowShell,tailShell,norm_tailShell}` family.

## 7. The rest of the cluster

After Sets 1–2 land, cut the remaining 17 nodes by layer and by shared block:

* **Layer 0, unrelated to the two** — `integral_one_add_norm_sq_cpow_neg_eq_pi_div`,
  `integral_one_add_sq_cpow_neg_eq_GammaReal_div`,
  `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `exists_bound_norm_integral_mixedSpace_archAtom_prod`,
  `integrable_{complex,real}Atom_and_integrable_moebiusShift`,
  `bounded_and_tendsto_integral_weylShift_sub_integral_smoothAtom_adicCompletion`,
  `integrable_smoothAtom_and_integrable_weylShift_adicCompletion`,
  `tendsto_integral_{normSq_rpow_sub_one_mul_complexAtom,sq_rpow_sub_one_mul_realAtom}_nhdsGT_one_half`.
  These are small (5–25 declarations each) and carry the 13-declaration `weylShift` block.
* **Layer 1** — the two `moebiusShift` rows, `exists_meromorphicOn_eq_integral_smoothWeylIntegrand_adicCompletion`,
  `exists_one_sub_mul_integral_smoothWeylIntegrand_eq_sum`,
  `integral_finiteAdeleRing_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod` (1,291 lines, its own
  5-declaration block), `integral_pow_mul_conj_pow_mul_one_add_norm_sq_cpow_neg`,
  `integral_sub_I_div_sqrt_one_add_sq_zpow_mul_cpow_neg_eq_GammaReal` (465 lines).
* **Layer 2** — `integral_adeleRing_pureTensor_prod_mul_finprod_unramifiedWeylIntegrand_mul_tprod`.

Total for the cluster: **6,336 net-new lines / 423 groups**, so roughly four sets of the ~1,500-line
size the playbook asks for, cut as: (1) unramified, (2) smooth, (3) the layer-0 integral family,
(4) the layer-1/2 product and finiteAdeleRing rows.

## 8. Risks and recorded deviations

* **The 22 "already in the port under a different statement" rows are mostly not new mathematics.**
  `countable_heightOneSpectrum` and `two_le_absNorm` differ from their port copies by **binder
  spelling** only (`: Countable …` versus `(F : Type) [Field F] [NumberField F] : …`), and the rest
  differ by the **`ValuationOrd.ord` → `IsDiscreteValuationRing.ord` rename** (statement ratios
  0.92–0.98). Treat them as reuse; do not re-prove them.
* **The three in-target binder variants to generalise**: `countable_heightOneSpectrum` (4 files),
  `two_le_absNorm` (3), and the `atom`/`atom` pair (`…_complexAtom…` versus `…_realAtom…`, ℂ against
  ℝ) — one lemma each, not two copies.
* **The two same-name-different-statement pairs**: `entries_pos` (ℂ against ℝ) and
  `summable_absNorm_rpow_neg` (against the ported `TateGlobal/PlaceSum.lean` statement). Generalise
  or rename; do not transcribe the second under the first's name.
* **102 of the 132 substitutions are tier 3** — public in unlisted `TateGlobal` modules, registered
  in `spec/UNWIRED-PUBLIC.md`, not statement-diffed. Importing them is fine; they are not
  checker-verified, so the set's own `SOURCES`/`PORT_FILES` wiring is the only diff those names get.
* **`isOpenEmbedding_val` is `private`** in `TateGlobal/MulHaar.lean` and needed by both files —
  promote or move it before Set 1 (§4).
* **The pin's `set_option synthInstance.maxHeartbeats 320000 in`** on
  `integers_diff_zero_eq_iUnion` is a claim to re-measure, not a fact: re-run it at the low cap when
  porting it (§4), and record the outcome.

## 9. Verification

Per set, at the end:

```bash
cd lean
flock .lake/flt_build.lock timeout 900 lake build FLTForHuman.<new modules>
timeout 300 python3 spec/old_check_stmts.py        # 0 mismatched / 0 missing
timeout 180 python3 spec/check_instance_probes.py
```

plus a consumer zone in `spec/` for each set (a real, executed cross-module composition over the
headline), `#print axioms` on the headline, a `grep` sweep for `sorry`/`admit`/`import Mathlib`/
heartbeat overrides, and the checker delta reconciled against the new public surface. The whole
cluster's `S_` files are not in `SOURCES` yet, so the checker sees none of this until Set 1 wires
them.

## 10. Reproduce

```bash
cd tools/deps
# the two named nodes: advise, then the budget and the shared block
python3 port_advise.py --nodes "AutomorphicForm.LocalIntertwining.integral_unramifiedWeylIntegrand_adicCompletion,AutomorphicForm.LocalIntertwining.integral_smoothWeylIntegrand_adicCompletion" --json build/weyl_advise.json
python3 port_plan.py --json build/weyl_advise.json
# the whole cluster (19 nodes)
NODES=$(python3 -c "import fltdata;d=fltdata.FltData();print(','.join(n for n in d.names if n.startswith('AutomorphicForm.LocalIntertwining')))")
python3 port_advise.py --nodes "$NODES" --json build/li_advise.json && python3 port_plan.py --json build/li_advise.json --json-out build/li_plan.json
```

The set's own numbers are re-measured on the tree it leaves; the figures above are the plan's, as
of the Set-0 landing.

## 11. Close-out

**The two named nodes are done.** The work, in the order it ran:

| set | module(s) | shape | checker |
|---|---|---|---|
| 0 | `TateGlobal/WeylPrelude.lean` | definition layer, 21 decls | —
| LI-1 | `TateGlobal/WeylShell.lean`, `WeylUnramified.lean` | residual prelude (29+1) and the unramified headline (2) | +52 |
| LI-2 | `TateGlobal/WeylSmooth.lean` | the smooth headline (2 public + 27 private) | +2 |

Checker after LI-2: **9654 identical / 670 promoted / 0 mismatched / 0 missing / 38 own (9692
checked)**. `spec/LocalIntertwiningConsumer.lean` has one zone per set and elaborates; `#print
axioms` on both headlines is `[propext, Classical.choice, Quot.sound]`.

Two things a future session must not re-derive:

* **`norm()` in `spec/old_check_stmts.py` now erases the recorded `ValuationOrd` →
  `IsDiscreteValuationRing` rename inside statements** (frictions FR-0014/FR-0018). Without it,
  `WeylPrelude.lean` wires at 8 MISMATCH. A future rename that touches a *signature* needs the same
  treatment.
* **`WeylShell.ofReal_pow_cpow` and `WeylSmooth.ofReal_pow_cpow` are two `private` re-proofs** of a
  helper the port also carries publicly in `TateGlobal/EulerFactors.lean:80` with different binder
  spellings (FR-0015/FR-0017). A `private` copy is not importable, hence the duplication; it is
  deliberate, not an oversight.

**What carries forward** (all of it in [CARRY-FORWARD.md](../../CARRY-FORWARD.md)): the other
seventeen `LocalIntertwining` nodes, still 6,336 net-new lines / 423 groups as a cluster minus what
LI-1/LI-2 took; the rest of the pin `Definitions/Def_LanglandsTunnell_TateLocalConstantsAt.lean`
(`HasConductorExponentAt`, `conductorExponentAt`, …), of which only `higherUnitsAt` is ported; and
the three in-target binder variants and two same-name-different-statement pairs of §8, which the
later sets will meet.
