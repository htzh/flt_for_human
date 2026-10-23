# WORKORDER-HD1b — the β-row degrees, and the `ℓ ∣ M` branch of the α row

**Status: landed (2026-10-22)** — see §7. One dispatch, two modules extended; three headlines. The direct continuation of
`WORKORDER-HD1`: after HD1 the nexus shelf’s head is `ModularCurve.finrankAlong_heckeBetaOneBar`
(334 lines), and the frontier reads the three headlines of this order as **ready** — each needs only
the engine HD1 landed. This is the rest of the α/β degree layer, before the Hecke-row commutativity
pair (`WORKORDER-HD3`, blueprint in [TOPIC-hecke-row-commutativity.md](TOPIC-hecke-row-commutativity.md)
§"the degree layer" below).

## 0. The three headlines

| node | pin `S_` | needed for | statement |
|---|---:|---|---|
| `ModularCurve.finrankAlong_heckeBetaOneBar` | 334 | shelf head; consumed by the `X₁` Hecke rows | `finrankAlong L (heckeBetaOneBar L M ℓ) = if ℓ ∣ M then ℓ else ℓ + 1`, under `h : HeckeBetaOneDefined M ℓ` |
| `ModularCurve.finrankAlong_heckeAlphaHBar_of_dvd` | 418 | `β-HBar` | `finrankAlong L (heckeAlphaHBar L M H p) = p`, for `p ∣ M` |
| `ModularCurve.finrankAlong_heckeBetaHBar` | 349 | the `X_H` Hecke rows | `finrankAlong L (heckeBetaHBar L M H ℓ) = if ℓ ∣ M then ℓ else ℓ + 1` (no `Defined` hypothesis: on the H side `heckeBetaHBar` is total) |

`frontier.py --ds --ready --nexus`: `BetaOneBar` is `needed 1` (334 lines); `AlphaHBar_of_dvd` is
`needed 1` (418); `BetaHBar` is `needed 2` (itself + `AlphaHBar_of_dvd`). With HD1 landed, the whole
remaining α/β degree layer is therefore one dispatch.

**Why they belong together.** All three are the *same computation* as HD1's two headlines, on the
same four nested fields (`x1FunctionField M ⊆ x1x0FunctionFieldC ℚ M (Mℓ) ⊆ modularFunctionFieldFull (Mℓ)`,
resp. the `X_H` tower) and the same full-level degree facts (`relfinrank_qExpand_full`,
`relfinrank_full_eq_dedekindPsi`, `dedekindPsi_mul_prime`). Twenty declarations of each pin file are
already public in `ModularCurve.HeckeDegree` (HD1's engine): `relfinrank_adjoin_eq_finrank`,
`relfinrank_adjoin_ne_zero`, `isAlgebraic_of_subsingleton_ratAlgebra`,
`finiteDimensional_adjoin_of_subsingleton_ratAlgebra`, `finrankAlong_inclusion`,
`fieldRange_val_comp_inclusion`, … (`port_advise` prints the mapping for each file).

## 1. Deliverable — extend the two HD1 modules

Do **not** create new modules: these are the same subject as the modules HD1 created ("the degrees
of the α/β degeneracy rows over X₁(M) / X_H(M)").

* `FLTForHuman/ModularCurve/X1/HeckeDegree.lean` (189 lines after HD1) += the β-One proof
  (`DBeta`), public surface = the existing α headline **plus**
  `ModularCurve.finrankAlong_heckeBetaOneBar` (verbatim from
  `Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean`; its hypothesis
  `h : HeckeBetaOneDefined M ℓ` is part of the statement).
* `FLTForHuman/ModularCurve/XH/HeckeDegree.lean` (403 after HD1) += `finrankAlong_heckeAlphaHBar_of_dvd`
  (the `ℓ ∣ M` branch of the α row, same statement family as the module's α headline — put it beside
  that headline, not in the engine block) and the β-H proof (`DBetaH`), public surface = the engine
  + the α headline + these two, all verbatim from their wrappers.

Everything the pin proves privately in the three `S_` files is `private` here, except the three
headlines. In particular the `DBeta`/`DBetaH` tower block (`FF`, `F0`, `B0`, `BB`, `dd`, the
`relfinrank_*` steps, `fieldRange_heckeBetaOneBar`, `qExpandAlg`, `laurentBaseChange_map_qExpand`) is
machinery.

Wires: add one `spec-pin:` pair (wrapper + `S_` file) per headline to the module it lands in.

## 2. Source

Pin `anthropics/fermats-last-theorem@aa2d8b3`:

* `Theorems/Thm_ModularCurve_finrankAlong_heckeBetaOneBar.lean` +
  `P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaOneBar.lean` (334; its section `DBeta`)
* `Theorems/Thm_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean` +
  `P2M/Sol/S_ModularCurve_finrankAlong_heckeAlphaHBar_of_dvd.lean` (418)
* `Theorems/Thm_ModularCurve_finrankAlong_heckeBetaHBar.lean` +
  `P2M/Sol/S_ModularCurve_finrankAlong_heckeBetaHBar.lean` (349; its section `DBetaH`)

The three `S_` files import only `Theorems/` wrappers plus `Definitions/Def_ModularCurve_X1HeckeOperator`
/ `Def_ModularCurve_XHHeckeOperator` / `Def_ModularCurve_X0ModL` — all ported. The One file imports
`Thm_ModularCurve_finrankAlong_heckeAlphaOneBar`, whose port is `X1/HeckeDegree` **in the same
module** — so the β-One proof is a direct `exact`/`rw` on the α headline, not an import.

## 3. Route

**β-One (`DBeta`).** With `FF = x1FunctionField M`, `FF' = x1x0FunctionFieldC ℚ M (M*ℓ)`,
`F0 = modularFunctionFieldFull M`, `F0' = modularFunctionFieldFull (M*ℓ)`,
`B0 = F0.map (qExpandₐ ℓ)`, `BB = FF.map (qExpandₐ ℓ)` and `dd = if ℓ ∣ M then ℓ else ℓ+1`:

1. the inclusions `FF ≤ FF'`, `F0 ≤ FF`, `F0' ≤ FF'`, `B0 ≤ F0'` (`full_degeneracy_map_le`),
   `B0 ≤ BB`, and `BB ≤ FF'` **under `HeckeBetaOneDefined M ℓ`** (this is where the hypothesis
   enters — it says the `q ↦ q^ℓ` image of the X₁ field lands in the X₁∩X₀ field);
2. `relfinrank F0 F0' = dd` — the full-level computation, from the ported
   `relfinrank_qExpand_full` + `relfinrank_full_eq_dedekindPsi` + `dedekindPsi_mul_prime`;
3. `relfinrank B0 F0' = dd` (the `q ↦ q^ℓ` map does not change the relative degree over `F0'`) and
   `relfinrank B0 BB = relfinrank F0 FF`;
4. base change: `relfinrank` is preserved by `laurentBaseChange` (`relfinrank_lbc_lbc`), and the
   ported `laurentBaseChange_adjoin`/`relfinrank_laurentBaseChange` do the rewriting;
5. `fieldRange (heckeBetaOneBar) = BB` (`fieldRange_heckeBetaOneBar`), then
   `finrankAlong β = relfinrank BB FF'` (`finrankAlong_eq_relfinrank_fieldRange`) `= dd` by the
   tower `BB ⊆ FF'` and the α-headline identity `relfinrank FF FF' = dd`.

**α-H `_of_dvd` (`p ∣ M`).** The companion of HD1's `ℓ ∤ M` case: for `p ∣ M` the level-`p` cover is
`Γ_H(M) = Γ_H(M) ⊓ Γ₀(Mp)` up to the `p`-part, so `Γ_H(M) ⊆ Γ₀(Mp)` already at level `M`
(`Gamma0_le_of_dvd`), and the degree collapses to the index `p` (the ported
`CongruenceSubgroup`-side index results + `Gamma0_index` at the prime). Follow the pin's own route;
the `Nice` machinery of HD1's engine is available but this branch is the *degenerate* one and should
be short (the pin's file is 418 lines mainly because it re-establishes the tower vocabulary).

**β-H (`DBetaH`).** The same as β-One over `Γ_H(M)`/`xHFunctionField`, with `heckeBetaHBar` total
(its `if h : HeckeBetaHDefined … then … else` fallback is the α map, so no hypothesis is needed);
the `ℓ ∣ M` case is `finrankAlong α_H = p` (the `_of_dvd` headline just landed in the same module).

## 4. Build discipline

* `cd lean && flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.ModularCurve.X1.HeckeDegree`
  (then the `XH` one). Edit loop with `lake env lean -DmaxHeartbeats=4000000 <file>`.
* Every command under two minutes; never a whole-tree `lake build`; no commit.
* Zero `warning:` lines. The two modules already carry `set_option autoImplicit false`; do not add a
  heartbeat bump (HD1 proved the engine needs none).

## 5. Verification

* `python3 lean/spec/check_port.py --force` on both modules: `0 mismatch, 0 missing`; the `X1` module
  should read **2 ok** (+1 per new public declaration) and the `XH` module its engine count + 3.
  Any other public declaration is a bug: report it.
* `#print axioms` on the three headlines: `[propext, Classical.choice, Quot.sound]`.
* `grep -c "sorry\|admit"` on both: 0.
* `python3 tools/deps/dedup.py 'ModularCurve/X1/HeckeDegree' 'ModularCurve/XH/HeckeDegree' --tier name`:
  no cluster between the two modules, and none naming `FF`, `F0`, `B0`, `BB`, `relfinrank_F0_F0'`,
  `fieldRange_heckeBetaOneBar` (the two β proofs must not both end up public).
* `python3 tools/deps/frontier.py --ds --ready --nexus --fanin-min 10 --top 5`: none of the three
  nodes on the shelf (nor in `--list`); quote the new head.

## 6. Stop-early conditions

* If `BB ≤ FF'` cannot be obtained from `HeckeBetaOneDefined` by unfolding the predicate, stop and
  report the goal — that is the one place the hypothesis enters, and a workaround that weakens the
  statement is not acceptable.
* If the `p ∣ M` branch of the α-H row needs a `CongruenceSubgroup` index fact the port does not
  have, report it as a missing premise with the exact `#check`; do not re-derive it inside the module.
* Do not touch `XH/Relrank.lean`, `X1/HeckeOperator.lean`, `XH/HeckeOperator.lean`, or the engine
  block of `XH/HeckeDegree.lean` (the part HD1 wrote); only append the new proofs and their
  `spec-pin:` lines.

## 7. The record

| module | lines | public | `check_port --force` |
|---|---:|---:|---|
| `ModularCurve/X1/HeckeDegree.lean` | 189 → **451** | 2 (the α-One and β-One headlines) | **2 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |
| `ModularCurve/XH/HeckeDegree.lean` | 403 → **790** | 33 (engine + the α-H, `_of_dvd` and β-H headlines) | **33 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |

Both green with **0 warnings**, no heartbeat bump, no `sorry`; `#print axioms` on all three headlines
`[propext, Classical.choice, Quot.sound]`. All three nodes are gone from the shelf and from the
`needed` list — the new head is `ModularCurve.heckeOperatorHAlong_comm` (993 lines), i.e. the
commutativity pair of `TOPIC-hecke-row-commutativity.md` §0. No statement was adapted; no stop-early
condition fired (`BB ≤ FF'` comes straight from `HeckeBetaOneDefined`, and the `p ∣ M` branch needed
only the already-public `relIndex_gamma1_inf_gamma0_mul_of_dvd` and `Gamma0_le_of_dvd`).

**One residue, reported rather than hidden.** `dedup.py --tier name` over the two modules reads **6
clusters / 34 lines**, all of them `private` on both sides — the β tower's shared vocabulary
(`relfinrank_F0_F0'`, `relfinrank_ne_zero_of_tower`, `jq_mem_F0`, `adjoin_jq_le_F0`, `jqN_mem_B0`,
`laurentBaseChange_map_qExpand`). There is **no public duplication**: this order kept both β proofs
private, as §1 says, and the ten other clusters the pin's files invite were already absorbed into
public homes (`qExpandAlgHomC`, `relfinrank_laurentBaseChange_eq`, `relfinrank_qExpand_full`,
`full_degeneracy_le`, `full_degeneracy_map_le`, `dedekindPsi_pos`). Promoting the residual six into
the engine block — the move HD1 made for the α prelude — is the natural follow-up order (six
declarations, both modules' sites rewired, no new module), and it is what would take the pair from
"34 removable private lines" to zero.
