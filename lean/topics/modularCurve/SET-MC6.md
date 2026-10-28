# SET MC-6 — M9: Fricke, and the q-expansion norm of the β-operator

**Status: scoped (2026-10-27); the definition gate is landed by the MC definition wave (D3, D5); no
manager lane; two worker orders.** This is the `ModularCurve` ready shelf's **MC-6**
([TOPIC-ready-shelf.md](TOPIC-ready-shelf.md) §1), story **M9**, the last of the ready block's seven
orders. It follows the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md); MC-4
([SET-MC4.md](SET-MC4.md)) is the immediately preceding wave.

The shelf priced MC-6 at 2 rows / 706 silo / ≈815 net with a **279-line** gate (`XH` 35 +
`CohCarrier_Inst` 80 + `CohCarrier_Fricke` 164). Three corrections:

1. **the gate is landed and was 164 + 60 + 0**, not 279: D5 (`CohCarrier/Fricke.lean`, 28
   declarations) and D4 (`CohCarrier/Inst.lean`, 6) are the definitions the two rows name, and
   `ModularCurve_XH`'s 35 lines are **not** M9's at all (the def wave's audit: no MC-4/5/6 row names
   `torsionGaloisRep`/`tateGaloisRep`/`tateEnd`, §0.2 there);
2. **384's price collapsed**: `port_advise` now reads **108 lines already in the port** — D3's
   `genOpH`/`diamondHBar` and D5's Fricke material — against the shelf's "0";
3. **no manager lane**: both homes are new modules and neither is on `PORT_FILES`.

| figure | value |
|---|---:|
| MC-6 rows | 2 / 706 silo |
| net new math lines | **≈477** (261 + 216) |
| definition gate | **landed** (D3, D4, D5) |
| manager lane | **none** |
| worker orders | **2** |

## 0. The two rows

Read from the shelf after MC-4 (2026-10-27): `needed` **998 / 397,567**, MC ready **10 / 2,782**.
The MC-6 block:

| row (`ModularCurve.` dropped) | silo | prem | home | order | net |
|---|---|---:|---|---|---:|
| `exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` | 322 | 3 | **new** `ModularCurve/XH/FrickeSlash.lean` | **MC-6a** | 261 |
| `qExpand_norm_heckeBetaHBar` | 384 | 2 | **new** `ModularCurve/XH/QExpandNorm.lean` | **MC-6b** | 216 |

### 0.1 The premises, verified in the port

| row | premise (`Thm_` wrapper) | port module |
|---|---|---|
| 322 | `exists_qExpansion_slash_fricke_eq_and_conj_eq_slash_gamma0` | `ModularForms/FrickeReciprocity.lean` |
| 322 | `PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem` | `RingTheory/PowerSeries/GaloisDescent.lean` |
| 322 | `exists_isIntegralQExp_smul_of_ratCast_qExpansion` | `ModularForms/WeightOne/Gamma0Integral.lean` |
| 384 | `exists_algEquiv_atkinLehner_heckeAlphaHBar_heckeBetaHBar` | `ModularCurve/X1/AtkinLehnerExchange.lean` |
| 384 | `finrankAlong_heckeAlphaHBar` | `ModularCurve/XH/HeckeDegree.lean` |

### 0.2 The pricing, per row

| order | row | raw `S_` | decl lines | boilerplate | in port | **net** |
|---|---|---:|---:|---:|---:|---:|
| MC-6a | 322 | 322 | 298 | 24 | 13 | **261** |
| MC-6b | 384 | 384 | 354 | 30 | 108 | **216** |
| | **total** | **706** | | | | **≈477** |

## 1. What each row is

**322 — `exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion`.** For a `Γ_H(M)`-modular form `f`
whose q-coefficients are rational, and any `W` with `W = !![0, -1; M, 0]` (the Fricke matrix up to
`signed permutation`), there are `n`, `c : Fin n → ℚ̄`, `g : Fin n → ModularForm (Γ_H) k` and
`p : Fin n → PowerSeries ℤ` with `IsIntegralQExp (g i) (p i)` and
`f ∣[k] W = ∑ i, ι (c i) • g i`. The pin's proof: define `frickeGL`/`frickeForm` (the Fricke
translate), show that a `Γ_H`-invariant form's Fricke translate has the same q-expansion up to the
`S`-slash (`fricke_eq_and_conj_eq_slash_gamma0`), then the `PowerSeries` Galois descent
(`exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem`) applied to the rational q-expansion, with
`exists_isIntegralQExp_smul_of_ratCast_qExpansion` supplying the integrality of each summand.

**384 — `qExpand_norm_heckeBetaHBar`.** For `u ∈ xHFunctionFieldBar`,
`qExpand (ℚ̄) ℓ (norm_{xHFunctionFieldBar} (heckeBetaHBar u)) = (∏ b < ℓ, qTwist (ζ^b)
(diamondAutHBar (unitOfCoprime ℓ …) u)) * qExpand …` — the q-expansion of the β-operator's
`Algebra.norm` is the product of the `ℓ` twists of the diamond conjugates. The proof uses
`finrankAlong_heckeAlphaHBar` (the degree of the α-operator is `ℓ`), the
`atkinLehner`/`heckeAlphaHBar`/`heckeBetaHBar` intertwining, and the norm's q-expansion formula.

## 2. Homes

Both are **new modules**, cascade-free and disjoint, not on `PORT_FILES` — no migration, and the two
orders run concurrently.

| order | home | above every premise? | why |
|---|---|---|---|
| a | `ModularCurve/XH/FrickeSlash.lean` | yes — `FrickeReciprocity`, `GaloisDescent`, `Gamma0Integral` are below it | the Fricke slash on `Γ_H`; the pin's `S_` file is the whole subject and it has no module in the port |
| b | `ModularCurve/XH/QExpandNorm.lean` | yes — `AtkinLehnerExchange` and `XH/HeckeDegree` are below it | the `qExpand` norm of the β-operator, whose subject is the `X_H` norm map; D3's `diamondHBar`/`genOpH` are imported |

**One import note for MC-6b**: the row's `S_` file imports `Def_ModularCurve_PhiGen` and
`Def_ModularCurve_XHOperators`; the port's `PhiGen` is `ModularCurve/Defs/PhiGen.lean` (landed) and
`XHOperators` is `XH/Operators.lean` (D3 + MC-4d). Both are below the new module.

## 3. The two orders

| order | row | home | silo | net | workorder |
|---|---|---|---:|---:|---|
| **MC-6a** | 322 | `ModularCurve/XH/FrickeSlash.lean` | 322 | 261 | [WORKORDER-MC6a-fricke-slash.md](WORKORDER-MC6a-fricke-slash.md) |
| **MC-6b** | 384 | `ModularCurve/XH/QExpandNorm.lean` | 384 | 216 | [WORKORDER-MC6b-qexpand-norm.md](WORKORDER-MC6b-qexpand-norm.md) |

## 4. Traps, per order

**MC-6a.** (i) The pin defines `frickeGL` and `frickeForm` **inside the `S_` file** (they are not in
a `Def_` module): transcribe them, they are the row's engine. `frickeGL` is `!![0, -1; M, 0]` as a
`GL (Fin 2) ℝ` and `frickeForm f = restrictForm … (translate f (frickeGL M))`; the port has
`ModularCurve.restrictForm` (`X1/Defs.lean`) and `ModularForm.translate`. (ii) The wrapper's
statement has `W : GL (Fin 2) ℝ` with `hW : (W : Matrix …) = !![0, -1; M, 0]` — the proof first
identifies `W` with the pin's `frickeGL`, so `eq_frickeGL` is needed. (iii) The pin's `S_` file
carries a large `attribute [-simp]` prelude — **not** reproduced. (iv) The `ι : ℚ̄ →+* ℂ` is the
coefficient embedding and must not be specialised.

**MC-6b.** (i) The statement is the pin's product identity; transcribe it verbatim, including the
`letI := AlgebraicCurve.algebraAlong (heckeAlphaHBar …)` in the `Algebra.norm` argument.
(ii) `qTwist` is the port's `ModularCurve.qTwistFun`/`qTwist` (`Defs/Twist.lean`) — check the
spelling before restating (the shelf's 46-suspect list names `twistFun`; it is `qTwistFun`).
(iii) `diamondAutHBar` is D3's; `unitOfCoprime` is mathlib's. (iv) The pin's `S_` file imports
`PhiGen`; the port's `Defs/PhiGen.lean` is below. (v) `Algebra.norm` over `xHFunctionFieldBar` is a
field norm — the port's `finrankAlong_heckeAlphaHBar` gives the degree; do not re-derive it.

## 5. Gates, per order

As MC-5 §5 (checker 0/0; axioms; module build under `flock` via the background channel, FR-0060;
silent; `dedup.py --within --tier shape`; exactly the two `spec-pin:` lines per headline; no
`set_option`, no suppression, no marker row, no git, no tree build).

**The consumer zone for the set** (`spec/ModularCurveMC6Consumer.lean`, manager-written): 322
instantiated at `k = 1` and a rational-q-expansion form, its `∑ ι (c i) • g i` fed to
`qExpansion`'s linearity; 384 applied at `ℓ = 2` and composed with `qExpand`'s multiplicativity and
`heckeBetaHBar`'s definition.

## 6. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/mc6.json
for row in exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion qExpand_norm_heckeBetaHBar; do
  python3 port_advise.py --nodes ModularCurve.$row --json build/mc6-$row.json
  python3 port_plan.py --json build/mc6-$row.json
done
cd ../lean
python3 spec/gate_scan.py --pin Definitions/Def_ModularCurve_XHOperators.lean \
  --rows S_ModularCurve_qExpand_norm_heckeBetaHBar
python3 spec/gate_scan.py --pin Definitions/Def_CohCarrier_Fricke.lean \
  --rows S_ModularCurve_exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion
```

## 7. What this set does not do

- **`ModularCurve_XH`'s Jacobian block** (`torsionGaloisRep` and the Tate pair) — the M9
  **successors'** surface, and the Tate half is blocked on `TateModule`. The shelf's 35-line gate
  line for MC-6 is therefore not this set's (§0).
- **The leaves block's `L-x1coeff` / `L-other` rows** (`existsUnique_algEquiv_qExpFunctionFieldC_coe_apply_eq_coeffMap`
  468, `diamondOneBar_comm` 468, `periodAlongOf_eq_neg_conj_…` 98, `realizeOf_eq_div` 57): the
  natural companions of MC-6a/6b, cut by the leaves programme.
- **No promotion, no migration, no tree build.**

## 8. The landing — measured (2026-10-27, both rows in)

Read with MC-5 (both waves landed in the same pass): `needed` **998 / 397,567 → 992 / 395,624**
(−6 / −1,943 = the six rows of MC-5+MC-6), frontier **1,415 / 729,584 → 1,421 / 731,527**,
`--selfcheck` **PASS**. This set's own verdicts: **2 checked declarations `ok`** (`XH/FrickeSlash.lean`
and `XH/QExpandNorm.lean`), axioms `[propext, Classical.choice, Quot.sound]`, both modules silent
with no `set_option` beyond `autoImplicit false`, 0 dedup clusters, consumer zone
`spec/ModularCurveMC6Consumer.lean` at **0 errors**.

Deliverables: two new modules, 424 + 355 lines, 31 + 34 private engine declarations, three new
`mapGL` adapters (MC-6a), no promotion, no migration, no new module beyond the two.

**Deviations worth the shelf's record.**
- **MC-6a substitutes two ported promotions** for pin-local re-declarations: `ΓGL` is
  `ModularForm.Level.ΓGL` (`Level/Gamma1Slash.lean`) and `frickeGL`'s body delegates to
  `ALTraceIdentity.frickeGL` (`HeckeFrickeTrace.lean`) — statements kept at the pin's spelling, so
  `val_frickeGL` is still `rfl`. Six pin-unreachable private lemmas (`det_frickeGL`,
  `det_frickeGL_pos`, `mapGL_eq_coe`, `pow_eq_pow_mod`, `qExpSubmodule`, `mem_qExpSubmodule_iff`)
  are transcribed as the pin has them; they are dead code in this module and are the first
  candidates of the next `move_dead.py` pass (the pin has them dead too).
- **MC-6b's separating element** (§7) is `jq` rather than the pin's `E₄`/`E₆`/`xq` block.

**Successor.** The row `exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul` (1,176)
became ready with this set — it is the M9 successor and the largest row in the MC block; it needs
`xHFunctionFieldBar`'s `slash`-equivariance and the Galois action on the Fricke translate, both of
which MC-6a's module now supplies in private form. Its own definition vocabulary must be audited
(`spec/gate_scan.py`) before it is cut, since 1,176-line rows are where a module-level read drifts.
