# WORKORDER LI-1 — the `LocalIntertwining` prelude residual and `integral_unramifiedWeylIntegrand_adicCompletion`

Set **LI-1** of the `AutomorphicForm.LocalIntertwining` column. Plan and measurements:
[TOPIC-local-intertwining-weyl-integrand.md](TOPIC-local-intertwining-weyl-integrand.md) §1–§5.
Playbook: [porting-playbook.md](../../porting-playbook.md) §2.3, §3.3–§3.5, §4. Frictions log:
[logs/frictions.md](../../logs/frictions.md) — read the entries, append yours.

Pin `anthropics/fermats-last-theorem@aa2d8b3`. Port mathlib `v4.34.0`.

## 1. Scope

Port **the residual prelude** that the two `LocalIntertwining` files re-carry and the port still
lacks, and then **the unramified headline with its public block**. Two new modules. This is one
job: the headline cannot be stated before the prelude is homed.

**In scope**

* the prelude declarations listed in §3 below, from the pin file's sections
  `FinGKFold_LocalHaarModulus`, `FinGKFold_LocalZetaUnramified`, `FinGKFold_MulHaarFromAdditive`,
  `FinGKFold_ValuedOrdBridge` and `FinGKFold_WeylGK`;
* the pin's `FinGKFold_Main` section: the public block of
  `S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
  (114 public declarations) and its headline.

**Not this set**

* `S_AutomorphicForm_LocalIntertwining_integral_smoothWeylIntegrand_adicCompletion.lean` (Set LI-2)
  and the other seventeen `LocalIntertwining` nodes. Their prelude is the same text — when a
  prelude declaration is shared, home it in the prelude module so LI-2 imports it;
* **any edit to an existing module.** `TateGlobal/WeylPrelude.lean`, `TateGlobal/MulHaar.lean` (whose
  `isOpenEmbedding_val` is now public) and every other existing file are **frozen**;
* the checker wiring (`spec/old_check_stmts.py`): the manager appends to `SOURCES`/`PORT_FILES`
  after you report.

## 2. Sources

* **Proof**: `P2M/Sol/S_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`
  (2,110 lines). Prelude sections 278–1719; the new `FinGKFold_WeylGK` section 1722–1942; `FinGKFold_Main`
  1945–2089.
* **Statement**: `Theorems/Thm_AutomorphicForm_LocalIntertwining_integral_unramifiedWeylIntegrand_adicCompletion.lean`.
  The binders of the headline and of every public declaration come **from the wrapper**, not from the `S_`
  file: the checker diffs the text, and a section-`variable` form that is inline in the `S_` file reports
  MISMATCH.
* **The pin writes `ValuationOrd.ord`; the port's name is `IsDiscreteValuationRing.ord (v.adicCompletionIntegers F)`**,
  and `ValuationOrd.ord_ofMul_of_mem` is `IsDiscreteValuationRing.ord_ofMul_of_mem`. Everything else keeps the
  pin's names.
* Provenance: put `-- pin: <name> (<full pin filename>:<line>)` above every declaration. **Write the pin
  filename in full** — an abbreviated one is silently accepted by the register and emits a broken link
  ([logs/frictions.md](../../logs/frictions.md) FR-0011).

## 3. What is already in the port — import it, do not re-prove it

132 of the cluster's declarations have an identical statement in the port (≈1,871 lines). Homes:

| pin names | port home |
|---|---|
| `ord`, `ordA`, `ordZ`, `exists_span_eq_pow`, `pow_maximalIdeal_*`, `ord_spec`, `ord_ofMul_*`, `ord_eq_zero_iff` | `RingTheory/DiscreteValuationRing/Order.lean` |
| `cosetMap`, `integers_eq_iUnion_image`, `pairwise_disjoint_image`, `measure_integers_eq_card_mul` | `TateGlobal/Coordinates.lean` |
| `distribHaarChar*`, `measure_smul_integers` | `TateGlobal/DistribHaarChar.lean` |
| `piUnit`, `shellSet`, `measurableSet_shellSet`, `mem_shellSet_iff_ord_eq`, `zero_notMem_shellSet`, `shellSet_subset_integers`, `measure_integers_lt_top` | `TateGlobal/LocalZetaUnramified.lean` |
| `genShell`, `mem_genShell_iff`, `genShell_disjoint`, `iUnion_genShell`, `measurableSet_genShell`, `mulHaar`, `isOpenEmbedding_val`, `image_val_subset_compl_zero`, `mulMeasure_*` | `TateGlobal/MulHaar.lean` |
| `exists_irreducible_valued`, `valued_coe_of_irreducible`, `valued_coe_units_eq_exp_neg_ord`, `coe_mem_integers_iff_ord_nonneg` | `TateGlobal/ValuedOrdBridge.lean`, `TateGlobal/WeylPrelude.lean` |
| `modulus`, `charExt`, `mulMeasure`, `localZeta` | `LanglandsTunnell/TateLocalZeta.lean` |
| `normQ`, `one_le_normQ`, `modulus_of_ne_zero_adicCompletion`, `modulus_of_mem_shellSet`, `modulus_of_mem_negShell`, `shellSet_subset_compl_zero`, `shellSet_disjoint`, the `char_eq_*`/`valued_*` block, `negShell` and its six lemmas, `eulerVar` | `TateGlobal/WeylPrelude.lean` (Set 0) |

The **residual prelude** (the part to port here):

* `integers_diff_zero_eq_iUnion`, `measure_shellSet`, `measure_smul_integers_pow`,
  `setIntegral_shellSet_const`, `mulMeasure_restrict_shellSet`, `mulMeasure_shellSet_lt_top`;
* `charExt_of_mem_shellSet`, `charExt_inv_of_mem_negShell`;
* `integrableOn_negShell`, `setIntegral_negShell`, `setIntegral_norm_negShell`, `measure_negShell`,
  `measure_negShell_lt_top`, `measureReal_negShell`;
* `integrand_eqOn_negShell`, `eqOn_integrand_shellSet`, `indicator_integrand`,
  `localZeta_indicator_integers`, `hasSum_localZeta_indicator`;
* `smul_integers_subset`/`smul_integers_succ_subset`, `valued_coe_ne_zero`, `valued_zpow_piUnit`,
  `cpow_qpow_bridge`;
* the unramified `ord` refinements `ordA_ringEquiv`, `map_maximalIdeal_ringEquiv`, `ordA_unit`,
  `ord_surjective`, `ord_units_map_of_mem_decompositionSubgroup`.

`card_residueField_eq_absNorm` / `card_residueField_pos` are **not** needed: Set 0 proves `one_le_normQ`
through `FrobeniusDensity.one_le_absNorm`.

## 4. Deliverables

* A new prelude module, e.g. `FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylShell.lean`, holding
  the residual prelude — public at the pin's names, since LI-2 will import it. Home shared declarations
  here, not in the set's own module.
* A new set module, e.g. `FLTForHuman/NumberTheory/NumberField/TateGlobal/WeylUnramified.lean`, holding
  the headline and the unramified public block.
* A genuinely file-local helper stays `private` **with a content name**; anything the pin exposes
  publicly — or that LI-2 will need — is public at the pin's name (prefix-stripped if it was promoted
  out of a pin-`private` prelude).
* Append your friction entries to `logs/frictions.md` in the template there (newest at the bottom).

## 5. Route and risks

The mathematics is local: `shellSet`/`genShell`/`negShell` are the p-adic shells, `mulMeasure` the
multiplicative measure, `mulMeasure_restrict_shellSet` and `setIntegral_shellSet_const` evaluate it on a
shell, and the headline is the resulting Euler-factor/integral identity. Everything reduces to the
`ord`/`modulus`/`distribHaarChar` API already in the port.

* **`integers_diff_zero_eq_iUnion` carries the pin's `set_option synthInstance.maxHeartbeats 320000 in`.**
  Do not transcribe it: run it at the low cap and report the outcome.
* The pin's shells are indexed by `ℕ` (`shellSet`) and `ℤ` (`genShell`); the `negShell` side is
  `genShell hπ (-(m+1))`. Watch the `ℤ`/`ℕ` casts in `modulus_of_mem_negShell`-style statements.
* Expect the `ValuationOrd.ord` → `IsDiscreteValuationRing.ord` rename at every `ord` site.
* A large slow module is usually cumulative, not one blow-up: bisect by milestone.

## 6. Build discipline (copy verbatim into the report)

> Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build <module>` per finished
> file, serialized with `flock` and bounded with `timeout`. Per wave, build only the wave's affected
> targets — **never a bare whole-tree `lake build`**. A whole-tree build happens once, at the session's
> end, only after the user agrees to it, and never on the agent's own initiative.

## 7. Stop conditions

**Stop and report** (do not work around) when:

* a needed declaration is `private` in a frozen module (name it — the manager promotes it);
* a fix needs an edit to any existing module (name the host and the `build_ladder.py --edit` price);
* a declaration cannot fit the low cap after a genuine instance-inference fix;
* a statement's binders cannot be taken from the wrapper.

Do not touch `spec/old_check_stmts.py`, do not add to `SOURCES`/`PORT_FILES`, do not edit
`TateGlobal/WeylPrelude.lean`.

## 8. Report shape

* the modules written, their declaration counts, and the tier-1 build line;
* the **exact list of public declarations** (fully-qualified names) for the checker wiring, split into
  "already in the port" and "new";
* the checker delta you expect, or why it cannot be stated yet;
* what was left unported and why;
* the friction entries you appended, by id; and the build-discipline block above.
