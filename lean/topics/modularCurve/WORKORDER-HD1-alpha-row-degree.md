# WORKORDER-HD1 — the degree of the α-row: the Γ_H engine, and the X₁ specialisation

**Status: landed (2026-10-22)** — see §8. One dispatch, two modules: the engine is written once and is public, the X₁ assembly is private. The leaf of this set
(`ModularCurve.map_jqNModC`) was already promoted into `ModularCurve/Defs/JqCoeff.lean` in the
same pass that deleted its three port copies, so this order is the two headlines and the engine
they share.

> **The set, as `frontier.py --ds --ready --nexus` reads it (2026-10-22, after the leaf landed):**
> `ModularCurve.finrankAlong_heckeAlphaOneBar` is the head of the nexus shelf — `needed 1` now,
> 495 lines — and `ModularCurve.finrankAlong_heckeAlphaHBar` (384 lines, `used_by(project) 10`) is
> ready beside it. The two pin `S_` files both carry a ~340-line `FinrankAlphaHSol` block, identical
> up to the prime's name (`ℓ` vs `q`): **the pin pays for that engine twice, and this order pays
> once.**

## 0. The two headlines

| node | pin `S_` | public statement |
|---|---:|---|
| `ModularCurve.finrankAlong_heckeAlphaHBar` | 384 | `finrankAlong L (heckeAlphaHBar L M H ℓ) = ℓ + 1`, for `ℓ ∤ M` |
| `ModularCurve.finrankAlong_heckeAlphaOneBar` | 495 | `finrankAlong L (heckeAlphaOneBar L M q) = if q ∣ M then q else q + 1` |

Both are degrees over the base-changed `q`-expansion function fields: the first is the classical
$[\Gamma_H(M)\cap\Gamma_0(M\ell) : \Gamma_H(M)] = \ell+1$ for $\ell \nmid M$; the second is the same
pair at $H = \bot$, where the `q ∣ M` case collapses to the index `q` (the map is then
$\Gamma_1(M)\cap\Gamma_0(Mq) = \Gamma_1(M)$-level) and the `q ∤ M` case is the engine.

**Demand.** Headline 2 is cited by `ModularCurve.heckeOperatorOneBar_comm` and the rest of the
`X1` Hecke-row column (the frontier's next ready rows); headline 1 by the `X_H` row column
(`heckeOperatorHAlong_comm`, …). Neither has a landed consumer yet: this is the degree layer the
Hecke-row commutativity lemmas are stated against. Say so in the record.

## 1. Deliverable — two modules

### (a) `FLTForHuman/ModularCurve/XH/HeckeDegree.lean` — the engine, public, and the Γ_H headline

The pin's `FinrankAlphaHSol` block, transcribed **once** at its declarations' pin names, and
**public** — the Γ₁ module (§1b) imports it, and so will every later row that needs the degree of a
level-raising pair. Public surface: the engine's declarations plus

```lean
theorem ModularCurve.finrankAlong_heckeAlphaHBar (L : Type*) [Field L] [Algebra ℚ L] (M : ℕ)
    [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaHBar L M H ℓ) = ℓ + 1
```

**Do not re-declare what already has a public home** (§2 below): `Gam`, `Gam'`, `Gam'_le`,
`T_mem_Gam'` are `ModularCurve.RelrankSol.*` in `XH/Relrank.lean`; `anSet` is
`ModularCurve.RelIndex.ratioSet` (`RelIndex/RatioField.lean`, tier 3); `coeffEmb_intSeriesC` is in
`JqIntegralRatios.lean`; `laurentBaseChange_mono'` is `Defs/Laurent.lean`'s
`laurentBaseChange_mono`; `map_jqNModC` is `Defs/JqCoeff.lean`'s (just landed). Import them, and
where the pin's *text* uses the abbreviation (`Gam M H`, `An …`), keep that spelling in the
statements so the checker's textual diff still matches.

Namespace: `ModularCurve` (headline), engine in a sub-namespace mirroring the pin's
(`FinrankAlphaHSol` → `ModularCurve.HeckeDegree` or keep the pin's inner names; the port's §3.1 rule
is that a pin-public statement keeps its name, private machinery may be restructured — here it is
*public*, so keep the pin's names).

### (b) `FLTForHuman/ModularCurve/X1/HeckeDegree.lean` — the X₁ assembly

The pin's `FinrankAlphaOneSol` block (~120 lines) plus the headline

```lean
theorem ModularCurve.finrankAlong_heckeAlphaOneBar (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (q : ℕ) [Fact q.Prime] :
    AlgebraicCurve.finrankAlong L (ModularCurve.heckeAlphaOneBar L M q) =
      if q ∣ M then q else q + 1
```

The assembly's helpers (`FF_bot`, `FF'_bot`, `finrankAlong_alphaOne`, `relIndex_Gam'_bot_of_dvd`,
`jqNModC_mem_EL`, `relrank_C_ge_of_dvd`, `relrank_C_le_of_dvd`, `relfinrank_FF_FF'_of_dvd`) stay
`private`; the headline is the module's only public declaration. Namespace `ModularCurve`.

## 2. Source, and what is imported

Pin `anthropics/fermats-last-theorem@aa2d8b3`:

* `Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean`
* `P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean` (384; the engine)
* `Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean`
* `P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean` (495; engine again + the assembly)

Wires: module (a)

```
  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar.lean
```

module (b)

```
  spec-pin: Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
  spec-pin: P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaOneBar.lean
```

No `decl_markers.tsv` rows are expected: every public declaration of both modules is in its own
wire, and the assembly's helpers are `private`.

Imports (specific, no `import Mathlib` in the library modules):

```lean
import FLTForHuman.ModularCurve.XH.Relrank        -- Gam, Gam', Gam'_le, T_mem_Gam', the q-exp field prelude
import FLTForHuman.ModularCurve.XH.FunctionField  -- xHFunctionField, xHTopFunctionFieldC
import FLTForHuman.ModularCurve.XH.HeckeOperator  -- heckeAlphaHBar
import FLTForHuman.ModularCurve.X1.HeckeOperator  -- heckeAlphaOneBar, heckeAlphaOneBar_eq_inclusion
import FLTForHuman.ModularCurve.X1.FunctionField
import FLTForHuman.ModularCurve.RelIndex.LeRelrank -- relIndex_gamma0_le_relrank_adjoin_insert_jqNModC
import FLTForHuman.ModularCurve.X1.FunctionFieldInclusion
import FLTForHuman.ModularCurve.Defs.Laurent      -- coeffMap, laurentBaseChange_mono
import FLTForHuman.ModularCurve.Defs.JqCoeff      -- map_jqNModC
import FLTForHuman.ModularForms.Defs.GammaH       -- GammaH_bot, translation_mem_GammaH
import FLTForHuman.AlgebraicCurve.Defs.Correspondence -- finrankAlong_eq_relfinrank_fieldRange
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice
                                                  -- relIndex_gamma1_inf_gamma0_mul_of_dvd
```

(Trim to what elaborates; the two `X1`/`XH` function-field modules are the ones the pin's `S_`
imports stand for.) All thirteen premises of headline 2 and all nine of headline 1 are already
ported — `port_advise` on the four pin files lists the eight statements it can substitute, and the
rest are the `xHFunctionField`/`relrank`/`relfinrank` API of the port.

## 3. Route

**The engine (module (a))**, $H$ arbitrary, `ℓ ∤ M`, in four blocks — the pin's sections:

1. **Groups.** `Gam = Γ_H(M)`, `Gam' = Γ_H(M) ∩ Γ₀(Mℓ)` (both `RelrankSol.*`), `Gam'_eq`
   (`Gam' = Γ₀(ℓ) ⊓ Gam` for `ℓ ∤ M`), `index_Gamma0_prime` (`(Γ₀ ℓ).index = ℓ + 1`, via
   `ModularCurve.Gamma0_index` + `Nat.divisors_prime`-style arithmetic), `relIndex_Gam'_le`.
2. **Rational fields.** `FF = qExpFunctionFieldC ℚ (Gam M H)`, `FF' = qExpFunctionFieldC ℚ (Gam' M H ℓ)`
   with `FF_eq : FF M H = xHFunctionField M H` (rfl) and `FF'_eq` (rfl) — these `rfl`s are what lets
   the headline be stated over `laurentBaseChange L (xHFunctionField M H)`; `FF_le` from
   `qExpFunctionFieldC_mono`; the generic field lemmas (`relfinrank_adjoin_eq_finrank`,
   `relfinrank_adjoin_ne_zero`, the `Subsingleton ℚ F` trio and `exists_good_x`).
3. **Base change.** `KL = laurentBaseChange L (FF M H)`, `EL = … (FF' M H ℓ)`, `laurentBaseChange_mono'`
   (import `laurentBaseChange_mono`), `KL_le_EL`, `relfinrank_KL_EL` (degree survives constant-field
   extension: from the ported `relfinrank_laurentBaseChange`), `fieldRange_val_comp_inclusion` and
   `finrankAlong_inclusion` (degree along an `IntermediateField.inclusion` is the relative degree —
   `finrankAlong_eq_relfinrank_fieldRange` + `IntermediateField.fieldRange`).
4. **Complex side and assembly.** `An (Δ) = adjoin ℂ (anSet Δ)`, `coeffEmb_image_subset`,
   `laurentBaseChange_le_An`, `An_Gam_le`, `laurentBaseChange_FF_eq_An`, `relrank_mono_right`,
   `relrank_C_le` (the `≤ ℓ+1` direction through `relrank_adjoin_qExpansion_div_le_relIndex` and the
   ported `le_relrank_…` for the other), then `relfinrank_FF_FF' = ℓ+1` by `le_antisymm`.

**The X₁ assembly (module (b)).** At `H = ⊥`: `FF_bot`/`FF'_bot` are `GammaH_bot`;
`finrankAlong_alphaOne` rewrites `heckeAlphaOneBar` through `heckeAlphaOneBar_eq_inclusion` and
`finrankAlong_inclusion`; the `q ∣ M` case is `relIndex_Gam'_bot_of_dvd`
(`CongruenceSubgroup.relIndex_gamma1_inf_gamma0_mul_of_dvd`), `relrank_C_ge_of_dvd` (the `≥ q`
direction through `relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` and `jqNModC_mem_EL` — this is
where the just-landed `map_jqNModC` is used), `relrank_C_le_of_dvd` (the `≤ q` direction through
`relrank_adjoin_qExpansion_div_le_relIndex`), and `relfinrank_FF_FF'_of_dvd`; the `q ∤ M` case is the
engine at `H = ⊥`.

**The pin's scaffolding.** Drop `p2m_export`/`p2m_open`/`p2m_reactivate`/`solution` and the `M4*`/
`FinrankAlphaHOne` inner namespaces; use `namespace`/`open`. The pin's long
`attribute [-instance]` / `attribute [-simp]` walls are **not** transcribed by default (the port's
convention): try without them, and if instance search or `simp` diverges, add only the minimal
needed lines, file-scoped, with a header sentence saying which and why (the port does this in a
handful of modules, e.g. `AlgebraicCurve/RadialRegion/IsOpenStarConvex.lean`).

## 4. Build discipline

* Edit loop: `cd lean && flock .lake/flt_build.lock timeout 110 lake env lean -DmaxHeartbeats=4000000 FLTForHuman/ModularCurve/XH/HeckeDegree.lean`.
* Module build: `cd lean && flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.ModularCurve.XH.HeckeDegree` (then the `X1` one). Build **(a) and check it before starting (b)**, so a wrong engine name is caught once.
* Every command under two minutes; never a whole-tree `lake build`.
* Zero `warning:` lines in both modules. If a declaration genuinely needs more than 20,000 hearts,
  record the pin's own bump and the bisection in the header (none of the four pin files sets one).

## 5. Verification

* `python3 lean/spec/check_port.py --force lean/FLTForHuman/ModularCurve/XH/HeckeDegree.lean` and
  the same for the `X1` module: `0 mismatch, 0 missing`. Module (a) will read one `ok` per public
  engine declaration plus the headline; module (b) exactly **1 ok**. That is the evidence that the
  engine is public on purpose and the assembly is private.
* `#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`.
* `grep -c "sorry\|admit"` on both: 0.
* `python3 tools/deps/dedup.py 'ModularCurve/XH/HeckeDegree' 'ModularCurve/X1/HeckeDegree' --tier name`:
  no cluster between the two modules (the engine must appear **once**), and
  `python3 tools/deps/dedup.py 'ModularCurve' --tier name --min-cost 0`: the two new modules must not
  add a cluster naming `relfinrank_FF_FF'`, `KL`, `EL`, `An`, `Gam'`.
* `python3 tools/deps/frontier.py --ds --ready --nexus --fanin-min 10 --top 5`: neither headline on
  the shelf; quote the new head.

## 6. Stop-early conditions

* If the engine's `Gam`/`Gam'`/`anSet` can be neither reused nor stated in the pin's text, stop and
  report: that is a home question for `XH/Relrank.lean`, not a proof problem.
* If `finrankAlong_inclusion` cannot be derived from
  `AlgebraicCurve.finrankAlong_eq_relfinrank_fieldRange` in a few lines, stop and report the goal
  (the pin proves it as a 5-line `relfinrank` computation; the port may need
  `IntermediateField.fieldRange` API that mathlib spells differently).
* If the `attribute [-]` walls turn out to be necessary, say which line of the pin's block is
  load-bearing and how you scoped it.
* Do not touch any existing module, `lean/spec/`, or `tools/`.

## 7. What this buys

The degree layer of the Hecke-row column on both sides of the Γ_H/Γ₁ split, with the shared
~340-line engine written **once**; it retires the pin's own duplicated `FinrankAlphaHSol` block, and
it is the last prerequisite before the `X1`/`XH` Hecke-operator commutativity rows become one-hop
statements.

## 8. The record

| module | lines | public | `check_port --force` |
|---|---:|---:|---|
| `ModularCurve/XH/HeckeDegree.lean` | 403 | 31 (the engine + the headline) | **31 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |
| `ModularCurve/X1/HeckeDegree.lean` | 189 | 1 (the headline) | **1 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |

Both build green with **0 warnings**, no `set_option maxHeartbeats` (clean at the default 20,000
hearts), no `sorry`; `#print axioms` on both headlines `[propext, Classical.choice, Quot.sound]`.
`dedup.py` over the two modules: **0 clusters**, and the `ModularCurve` name tier gains no cluster
naming `relfinrank_FF_FF'`, `KL`, `EL`, `An`, `Gam'`, `anSet`, `index_Gamma0_prime`.

`frontier.py --ds --ready --nexus --fanin-min 10 --top 5` now reports
`ModularCurve.finrankAlong_heckeBetaOneBar` (334 lines) as the head of the shelf, with both α-rows
gone, and `frontier.py --ds --target ModularCurve.finrankAlong_heckeAlphaHBar --ready --list` reads
`needed 0 — target is ported`.

**The pin's scaffolding was not needed.** The `attribute [-instance]` / `attribute [-simp]` walls
did not have to be transcribed (both modules elaborate without them) and neither did any
`p2m_*`/`solution`/`main` device. One *instance* line was added for elaboration — the private
`isTorsionFree_extendScalars`, which `Module.finrank_pos` needs inside this instance environment and
which the generic search misses at 20,000 `synthInstance.maxHeartbeats`; supplying it directly is
what keeps the module at the default budget (its `adjoin`-shaped twin is inline in
`relfinrank_adjoin_ne_zero`). Recorded in the module (a) header.

**Three substitutions were made at the statement-text level**, all proof-side: `if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right` (deprecated in v4.34.0), `dedekindPsi` root-qualified in
`index_Gamma0_prime`'s unfold, and one trailing `rfl` in `coeffEmb_image_subset` because the port
spells the ratio through `DiamondLift.qC`. No statement moved: the checker's `ok` on all 32 rows is
the evidence.

**What the pair cost, and what it saved.** The pin writes the `FinrankAlphaHSol` engine (≈340 lines)
in *both* `S_` files; the port writes it once, in the `XH` module, and the `X1` module is 189 lines.
The engine is now also the home of the `roof`/`KL` base-changed field that the next Hecke-row
modules need — `port_advise` already resolves the `heckeOperator{OneBar,HAlong}_comm` pair's `roof`
abbreviation to `ModularCurve.HeckeDegree.KL` (3 pin copies), which is exactly what this order was
for.
