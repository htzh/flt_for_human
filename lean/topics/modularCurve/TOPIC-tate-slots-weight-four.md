# The Tate-slot weight-4 package — the fourteen-leaf cluster, its mathematics and its port

The `ModularCurve` frontier's `--include-leaves` view puts fourteen leaves in a band at 1649–1652
silo lines: `tsum_lambertTerm_eq`, `single_div_one_sub_sq`, `single_sq_div_one_sub_cube`,
`slotSubst_gen_injective`, `coeff_slotSubst_tateUnivX`, `coeff_slotSubst_tateUnivY`,
`equation_tateBase_iff`, `toricPoint_fst_coeff_mul`, `toricPoint_fst_coeff_of_not_dvd`,
`toricPoint_fst_coeff_zero`, `toricPoint_snd_coeff_mul_eq_sum_divisors`,
`toricPoint_snd_coeff_of_not_dvd`, `toricPoint_snd_coeff_zero`, `tsum_of_coeff_lt_eq_zero`. This
note is the group's home: §1 the mathematics, §2 the measurement and the dedup, §3 the port
structure, §4 the fourteen headlines, §5 risks and recorded negatives, §6 registers.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

Companions: the column note [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §1 (the
definition layer, already landed), [WORKORDER-F1-tate-slots-engine.md](WORKORDER-F1-tate-slots-engine.md)
(the worker order), and the playbook's §2.3 (whole node), §3.5 (build ladder) and §4(b)
(`private` is a build tool).

## 1. The mathematics

The package computes the `q`-expansion of the **universal Tate curve's coordinates after the
`Γ₀(ℓ)`-slot substitution**, and the `q`-expansions of the **toric** and **non-toric `ℓ`-torsion
points**. It is the coefficient engine the weight-one column's Hecke/Frobenius layer reads off.

**The universal curve.** `tateUnivX`, `tateUnivY`, `tateUnivA4`, `tateUnivA6` are the two-variable
power series (`MvPowerSeries (Fin 2) ℤ`) whose variables track the two `Γ₀(ℓ)` orbits of `ℓ`-torsion;
`tateUnivCurve` is `⟨1, 0, 0, tateUnivA4, tateUnivA6⟩`. All four are in the definition layer
(`Defs/TateSlots.lean`, §PORTING-DeligneSerre §1).

**The slot substitution.** `slotFamily K p c j` is the pair
`(c X ^ j, c⁻¹ X ^ (p - j))`, and `slotSubst K p c j = MvPowerSeries.subst (slotFamily …)`: the
`Γ₀(p)`-slot pullback of a universal series. `tateBase K p = (tateLaurent K).map (qExpand K p)`
is the Tate curve over `LaurentSeries K` base-changed along `q ↦ q ^ p`.

**The two torsion species.** `nonToricPoint K p c j` is
`(ofPowerSeries (slotSubst … tateUnivX), ofPowerSeries (slotSubst … tateUnivY))` — an `ℓ`-torsion
point living in a slot; `toricPoint K p c` is the point over the Tate parameter, given by the
closed `PowerSeries.mk` forms with the `c / (1 - c) ^ 2` and `c ^ 2 / (1 - c) ^ 3` heads.

**The weight-4 (`W4B`) layer.** Three blocks, in dependency order:

* `W4B` — the convergence criterion: if `f N`'s coefficients vanish below `N * δ` and `g` is the
  coefficientwise limit, then `∑' N, f N = g` (`tsum_of_coeff_lt_eq_zero`), with the `hasSum` /
  `summable` forms. The platform is the rank-one discrete valuation on `LaurentSeries K`
  (`rankOneLaurent`, `w4bNormed`, `tateQ`, the `nnnorm`/`valued` lemmas).
* `W4B.B2.GeomPS` / `GeomLS` — the geometric series `geomPS d = ∑_{d ∣ m} X ^ m`, its `Qp` powers
  (`Qp = single p 1`), and the coefficient lemma `coeff_Qp_pow_div_one_sub`.
* `W4B.B2.Lambert` — `lambertTerm` and `tsum_lambertTerm_eq`:
  `∑' n, c n • (Qp ^ n / (1 - Qp ^ n)) = qExpand K p (laurentOfInt (mk (∑_{d ∣ m} c d)))`.

**The slot-coefficient engine (`W4Bdev`).** The heart. `coeff_slotSubst_eq_boxSum` rewrites
`coeff n (slotSubst …)` as a box sum over the `(a, b)` with `a + b ≤ n`; the 252-line
`boxSum_eq_head_add_doubleSum` splits it into a head term plus a double sum over divisors;
`coeff_slotSubst_tateUnivX` / `_tateUnivY` are the resulting closed coefficient formulas. On the
way, `slotSubst_gen_injective` (the substitution with `genR = single 1 1` is injective) and the
`SpecS*` blocks (`coeff_subst_pair`, `prod_pow_fin_two`) carry the elementary combinatorics.

**The head and Laurent closed forms.** `headX`/`headY` with `headX_mul_eq` / `headY_mul_eq` (the
head series' multiplication), and `single_div_one_sub_sq` / `single_sq_div_one_sub_cube`:
`single j c / (1 - single j c) ^ 2` and its cube, expanded as `ofPowerSeries (mk (… choose 2 …))`.

## 2. The measurement and the dedup

The fourteen leaves are **fourteen near-clones of one file**. All fourteen `S_` files import the
same five modules (`Def_ModularCurve_TateSlots` + four mathlib); a normalized `diff` of any two
differs only in the `P2MW.S_<stem>` namespace string and the final public `solution` theorem.
Every one of the 115 distinct declaration names occurs in **all fourteen** files.

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --ready --include-leaves --top 0
python3 port_advise.py --nodes "$(paste -sd, build/cluster_leaves_names.txt)" \
  --json build/cluster_advise.json
python3 port_plan.py --json build/cluster_advise.json
```

`port_advise` reports **0 substitutions** (nothing is in the port), **112 names proved in ≥2 target
files**, ≈**20,810 removable lines** if each is written once, and a strongest factoring pair of
1,622 lines / 112 proofs. `port_plan` gives the budget:

| quantity | value |
|---|---:|
| raw `S_` lines (the 14 files) | 23,094 |
| declaration lines | 22,786 |
| duplicate copies (removable) | 21,115 |
| distinct declaration groups | 134 |
| once-cost after dedup | **1,671** |
| already in the port | 0 |
| **net new math lines** | **1,671** |

So the band's fourteen 1650-line leaves are **one ~1,670-line development written fourteen
times**. The frontier prices each leaf at its whole file because the citation graph records no
intra-package edges; the leaf view is a pricing artefact, not fourteen subjects.

The **definition layer** is already ported whole (`Defs/TateFormal.lean`, 26 declarations;
`Defs/TateSlots.lean`, 37), listed in the checker, +63 identical. Nothing else is in the port.

## 3. The port structure

Two tiers, by the port's usual economy:

**Tier 3 — the engine**, two new modules, both importing only
`FLTForHuman.ModularCurve.Defs.TateSlots` and mathlib. They are independent of each other (the
slot-substitution coefficients do not use the `tsum` convergence), so either can be built first.

| module | content | lines |
|---|---|---:|
| `FLTForHuman/ModularCurve/TateSlots/Convergence.lean` | the valued platform (`Seam`/`Kit`/`Platform`), `W4B`, `GeomPS`/`GeomLS`, `Lambert` | 537 |
| `FLTForHuman/ModularCurve/TateSlots/SlotCoeff.lean` | `BaseFaces`, `SlotSubstAPI`, `SpecS0`–`S4`, `W4Bdev.*`, `GeomHeads`, `Laurent`, `ToricFaces`/`ToricCoeffs` | 1,293 |

Both built green at the low cap with **no heartbeat blow-up** (Convergence 3,155 jobs / module 5.3 s;
SlotCoeff 3,149 jobs / module 8.2 s); the named `boxSum_eq_head_add_doubleSum` and
`coeff_slotSubst_tateUnivX/Y` risks fit. The only proof adaptations were four mathlib v4.34
deprecation renames (`if_pos`→`ite_eq_left`, `if_neg`→`ite_eq_right`,
`Set.mem_setOf_eq`→`Set.mem_ofPred_eq`, `HahnSeries.embDomain_notin_range`→
`HahnSeries.embDomain_of_notMem_range`) and one `change` in `slotSubst_gen_eq_zero_iff`.

The pin's namespaces (`ModularCurve`, `ModularCurve.W4B`, `ModularCurve.W4B.B2`,
`ModularCurve.W4Bdev`) and pin names are kept verbatim; `-- pin:` comments carry provenance for the
register. Every pin-`private` helper that no headline needs stays `private` (playbook §4(b)); the
pin's public API lemmas stay public and land in `UNWIRED-PUBLIC.md` (they have no consumer in the
port yet). The pin's duplicate `ofPowerSeries_coeff_neg`/`_int` (declared in both `GeomLS` and the
second `ModularCurve` block) is written **once**, in `Convergence.lean`.

**Tier 1 — the headline façade** (the manager's):

| module | content |
|---|---|
| `FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` | the fourteen public `ModularCurve.<name>` statements, verbatim from the pin's `Theorems/Thm_ModularCurve_*` wrappers, each proved from the engine's kernel lemma |

**The interface between the tiers.** The pin writes each headline as a `solution` theorem
forwarding to a **`private`** kernel. The port promotes the fourteen kernels to **public** in the
engine, under the uniform namespace `ModularCurve.TateSlots.<name>` (a port-chosen name; the pin's
`private` name is not available publicly, and for eleven of the fourteen it *is* the public
wrapper name, so it cannot be reused). Each kernel is stated with the pin `Theorems/` wrapper's
binders, so the façade in `QPow.lean` is a one-line application. This is exactly the pin's own
`solution := kernel` shape, one namespace deeper.

## 4. The fourteen headlines

Kernel `ModularCurve.TateSlots.<name>` (engine) → façade `ModularCurve.<name>` (tier 1). All
statements are the pin wrappers' verbatim.

| headline | engine module | pin `S_` kernel |
|---|---|---|
| `tsum_of_coeff_lt_eq_zero` | Convergence | `W4B.tsum_of_coeff_lt_eq_zero` (private, :475) |
| `tsum_lambertTerm_eq` | Convergence | `W4B.B2.tsum_lambertTerm_eq` (private, :666) |
| `equation_tateBase_iff` | SlotCoeff | `ModularCurve.equation_tateBase_iff` (private, :38) |
| `slotSubst_gen_injective` | SlotCoeff | `ModularCurve.slotSubst_gen_injective` (private, :985) |
| `coeff_slotSubst_tateUnivX` | SlotCoeff | `ModularCurve.coeff_slotSubst_tateUnivX` (private, :1383) |
| `coeff_slotSubst_tateUnivY` | SlotCoeff | `ModularCurve.coeff_slotSubst_tateUnivY` (private, :1401) |
| `single_div_one_sub_sq` | SlotCoeff | `ModularCurve.single_div_one_sub_sq` (private, :1613) |
| `single_sq_div_one_sub_cube` | SlotCoeff | `ModularCurve.single_sq_div_one_sub_cube` (private, :1619) |
| `toricPoint_fst_coeff_zero` | SlotCoeff | `ModularCurve.toricPoint_fst_coeff_zero` (private, :771) |
| `toricPoint_snd_coeff_zero` | SlotCoeff | `ModularCurve.toricPoint_snd_coeff_zero` (private, :776) |
| `toricPoint_fst_coeff_of_not_dvd` | SlotCoeff | `ModularCurve.toricPoint_fst_coeff_of_not_dvd` (private, :801) |
| `toricPoint_snd_coeff_of_not_dvd` | SlotCoeff | `ModularCurve.toricPoint_snd_coeff_of_not_dvd` (private, :809) |
| `toricPoint_fst_coeff_mul` | SlotCoeff | `ModularCurve.toricPoint_fst_coeff_mul` (private, :832) |
| `toricPoint_snd_coeff_mul_eq_sum_divisors` | SlotCoeff | `ModularCurve.toricPoint_snd_coeff_mul'` (private, :852) |

Line numbers are the representative `S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean`; every one of the
fourteen files carries the same kernel at the same line.

## 5. Risks and recorded negatives

* **No hub edit.** The whole group is two new engine modules plus one new façade module. No existing
  Lean module is touched, so there is no wave and no cascade. The checker file is the only edit
  outside the new modules.
* **Build-time blow-up is the named risk.** The pin's `boxSum_eq_head_add_doubleSum` is 252 lines of
  `Finset`/`Nat` arithmetic and `coeff_slotSubst_tateUnivX/Y` are long `split_ifs <;> ring` proofs;
  the low `maxHeartbeats=200000` cap is the instrument. A declaration that will not fit is fixed by
  instance inference, never by raising the cap (playbook §3.5).
* **The `W4B` platform is a valuation instance.** `rankOneLaurent`/`w4bNormed` build a `NormedField`
  instance on `LaurentSeries K`; if instance search is slow, that is the culprit and it is solved
  with `letI`/`inferInstanceAs`, not a cap.
* **Statements are the wrappers'.** The checker's statement authority is the `Theorems/Thm_*`
  wrapper, not the `S_` file's section-implicit binder shape; the façade uses the wrapper binders.
  (This is the 9-row "same conclusion, different binders" list `port_advise` reports — all of it is
  the `S_`-private kernel vs its wrapper, resolved by taking the wrapper's binders, playbook §7.4.)
* **Recorded negative: the 14 `S_` files are not ported.** Their only non-shared content is the
  final `solution` theorem, which is the façade. Porting the `S_` files themselves would re-write
  the 1,671 lines fourteen times; `SOURCES` lists them only to supply the pin's public prelude rows
  and the kernel statements, exactly as `WORKORDER-E` did for its twin `S_` files.

## 6. Registers and next steps

* **Landed.** WORKORDER-F1's engine is in, the tier-1 façade
  `FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` carries the fourteen public
  `ModularCurve.<name>` headlines, and the checker reads **9318 identical (648 promoted, 83
  renamed), 0 mismatched, 0 missing, 38 own (9356 checked)** — a measured **+14** on the
  pre-F1 tree's 9304, exactly the façade surface. All fourteen headlines are
  `[propext, Classical.choice, Quot.sound]`; a one-token statement mutation gives exactly 1
  mismatched (reverted); the forbidden-token sweep is clean.
* The engine modules are tier 3 (not in `PORT_FILES`), so their public surface — the fourteen
  kernels plus the pin's public API lemmas — is emitted to
  [../../spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md) by
  `python3 tools/deps/unwired_register.py`: **78 modules / 1,906 public declarations / 1,618 with
  a pin original** (38 rows for `Convergence`, 81 for `SlotCoeff`, none missing a pin original).
  The kernels are consumed by the façade (they are wired in spirit) but the engine module stays
  unlisted until a consumer needs its whole surface.
* The façade is tier 1: `Theorems/Thm_ModularCurve_<name>.lean` (statement authority) and
  `P2M/Sol/S_ModularCurve_<name>.lean` appended to `SOURCES`, and
  `FLTForHuman/ModularCurve/TateSlots/CoefficientFormulas.lean` to `PORT_FILES` — all appended last.
* **Reproduce the measurement** (the two frontier readings and the dedup):

```bash
cd tools/deps
python3 port_advise.py --nodes ModularCurve.tsum_lambertTerm_eq,ModularCurve.single_div_one_sub_sq,\
ModularCurve.single_sq_div_one_sub_cube,ModularCurve.slotSubst_gen_injective,\
ModularCurve.coeff_slotSubst_tateUnivX,ModularCurve.coeff_slotSubst_tateUnivY,\
ModularCurve.equation_tateBase_iff,ModularCurve.toricPoint_fst_coeff_mul,\
ModularCurve.toricPoint_fst_coeff_of_not_dvd,ModularCurve.toricPoint_fst_coeff_zero,\
ModularCurve.toricPoint_snd_coeff_mul_eq_sum_divisors,ModularCurve.toricPoint_snd_coeff_of_not_dvd,\
ModularCurve.toricPoint_snd_coeff_zero,ModularCurve.tsum_of_coeff_lt_eq_zero \
  --json build/cluster_advise.json
python3 port_plan.py --json build/cluster_advise.json
```

FLT provenance, pinned `aa2d8b3`: the fourteen `S_` files are
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_<name>.lean`,
the wrappers `…/Theorems/Thm_ModularCurve_<name>.lean`, and the engine's home module
`…/P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean` (1,649 lines) is the representative
transcription source.
