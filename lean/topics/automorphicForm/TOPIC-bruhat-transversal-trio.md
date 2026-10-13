# The Bruhat-transversal / Weyl-integrand trio

**Status: LANDED (2026-10-13).** The gate, both turns and the three-headline façade are in
the port; the checker reads +3 and the milestone build is green. This is the planning note
for the three graph-leaf headlines

* `AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half` (summability),
* `AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half` (continuity),
* `AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half` (integrability),

which rest on one shared `AutomorphicForm.WeylIntegrable` development. It follows the
recent large-silo efforts — [WORKORDER-P-rightConv-comm.md](WORKORDER-P-rightConv-comm.md)
and its definition gate, [WORKORDER-Q-archTestFactor.md](WORKORDER-Q-archTestFactor.md),
[../numberTheory/tateGlobal/TOPIC-tateglobal-analytic-core.md](../numberTheory/tateGlobal/TOPIC-tateglobal-analytic-core.md).
The method is [porting-playbook.md](../../porting-playbook.md) §2.1–§2.6, §3.1–§3.5, §4.
Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`);
port mathlib `v4.34.0`.

## 1. The measurement

### 1.1 Why the family test was run

The first two headlines looked like a twin pair — identical imports, identical section
spine through line ~2,689, 2,792 and 2,763 lines — and the pair alone measures
**2,767 net new** against 5,555 raw (a 2,393-line / 252-declaration shared block). The
family test then found the third member, `weylIntertwiningIntegrand_integrable_of_re_gt_half`
(2,420 lines, same imports, same spine ending at `Served`).

| quantity | the pair | **the trio** |
|---|---:|---:|
| raw `S_` lines | 5,555 | 7,975 |
| declaration lines | 5,427 | 7,783 |
| duplicate copies | 2,660 | 5,003 |
| distinct declaration groups | 285 | 285 |
| **net new math lines** | **2,767** | **2,780** |
| all-three block | — | **2,066 lines / 222 declarations** |
| pair-only block | 2,393 / 252 | **297 lines / 30 declarations** |
| substitutions | 0 | 0 |

**The third headline costs +13 lines.** It is a one-line invocation of the shared
`AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half_impl`
(declared in the all-three block). This is the `WORKORDER-P` "third silo is nearly
free" pattern (+109 there), here almost entirely so. **The cut is the trio.** Porting
the pair first and the cousin later would revisit the shared home for no reason.

### 1.2 The block structure

Both `S_` files (and the cousin) lay out the same sections; the blocks map cleanly:

| section | all-three block | pair-only |
|---|---|---|
| `S4Base/AdelicCountability` | 2 decls / 40 lines | — |
| `S4Base/M4aS4` | 32 / 371 | — |
| `S4Base/AdeleRing` | 1 / 39 | — |
| `WeylIntegrable/Coset` | 8 / 95 | — |
| `WeylIntegrable/ModFin` | 5 / 88 | — |
| `WeylIntegrable/{Generic,Adelic,Generic2,Adelic2}` | 44 / 234 | — |
| `WeylIntegrable/{EntryBox,NormBounds,AdelicBoxSec}` | 24 / 210 | — |
| `WeylIntegrable/{PositiveChar,Pointwise,Lattices,R2,Fin,Place,Arch}` | 97 / 716 | — |
| `WeylIntegrable/{Asm,Served}` | 24 / 273 | — |
| `WeylIntegrable/{LatticeSum,Uniform}` | — | 30 / 297 |

The pair-only block is the **uniform M-bound** (`bruhatTransversal_norm_le_summable_uniform`)
and the lattice-sum bookkeeping that the two Bruhat headlines need; the cousin stops at
`Served` and never reaches it. The ~377 remaining lines are the three per-file caps:

* `bruhatTransversal_summand_norm_summable_of_re_gt_half` — `_impl` is a one-line
  invocation of the shared `WeylIntegrable.bruhatTransversal_summand_norm_summable`;
* `continuous_bruhatTransversal_tsum_of_re_gt_half` — adds a **22-line**
  `RhSContinuity.rhs_hole`: `continuousOn_tsum` on the termwise-continuous terms under
  the shared uniform bound (Weierstrass M-test), then `continuousAt`;
* `weylIntertwiningIntegrand_integrable_of_re_gt_half` — one line on the shared `_impl`.

### 1.3 The graph position

All three are graph leaves (`cites 0`), all in the Deligne–Serre cone, and all hidden
from `--ready` (a leaf with `needed == 1` cannot reach `F`). They surface only under
`--include-leaves`, high in the 560-leaf list at 2,792 / 2,763 / 2,420 silo lines. Their
consumer chain runs through `exists_whittakerCoefficient_bruhatEisenstein_*`,
`bruhatEisenstein_eq_constantTerm_add_whittakerSum_*` and the Rankin–Selberg /
Maass–Selberg rows — the Eisenstein-analytic layer, not the weight-one column.

**Adjacent, not folded.** The six small `S_AutomorphicForm_WeylIntegrable_*` silos
(`Dy_eq_prod_mul_relIndex`, `Dy_pos`, `dilate_finPart_of_snd_eq`,
`finprod_norm_eq_relIndex_dilate`, `norm_apply_weyl_unipotent_le_uniform`,
`rpow_Dy_le_translate_of_le`) name declarations this block already proves
(`norm_apply_weyl_unipotent_le_uniform`, `Dy_*`); they are descendants. The
`LocalIntertwining_integral_*WeylIntegrand_adicCompletion` pair imports
`TateLocalZeta`/`Completion_Finite` and is a different subject (finite-place Tate).

## 2. The mathematics

The three statements are the analytic core of the big-cell Bruhat/Eisenstein series.
Write `α` for the pin's positive distributive-Haar character on `𝔸_F^×`, `η₁ = μ·α^{s+1/2}`,
`η₂ = ν·α^{-(s+1/2)}` with `μ`, `ν` unitary, and `w`, `n(ξ)` the Weyl and unipotent
elements.

1. **Summability** (`bruhatTransversal_summand_norm_summable`): for `Re s > 1/2`, every
   `g`, `∑' ξ : F, ‖φ(w n(ξ) g)‖` is summable (Godement's estimate).
2. **Continuity** (`continuous_bruhatTransversal_tsum`): `g ↦ ∑' ξ, φ(w n(ξ) g)` is
   continuous — the M-test corollary of (1) with the uniform bound.
3. **Integrability** (`weylIntertwiningIntegrand_integrable`): `x ↦ φ(w⁻¹ n(x) g)` is
   integrable against adèlic additive Haar.

The shared engine is the `WeylIntegrable` development: coset transversal and its finite
modulus (`Coset`, `ModFin`); the transfer from the generic projected-Haar framing to the
adèlic group (`Generic`…`Adelic2`); the entry-box/norm bounds (`EntryBox`, `NormBounds`,
`AdelicBoxSec`); the lattice/place/archimedean estimates (`PositiveChar`, `Pointwise`,
`Lattices`, `R2`, `Fin`, `Place`, `Arch`); the assembly (`Asm`, `Served`); and the uniform
bound and lattice sum (`LatticeSum`, `Uniform`). The `S4Base` half is generic adèlic
measure theory (countability, place measures, the `distribHaarChar` product formula) and
mentions no Eisenstein data at all.

## 3. The layer map and the natural homes

All three `S_` files declare in the pin namespace `AutomorphicForm` (and its
`WeylIntegrable` sub-namespace); the port keeps those namespaces and carries the
organization in the directories.

**The definition gate** (§4) homes four small `Definitions/` modules:

| module | lines / decls | home |
|---|---:|---|
| `Def_AutomorphicForm_BorelSubgroup` | 216 / 16 | `AutomorphicForm/Adelic/BorelSubgroup.lean` |
| `Def_AutomorphicForm_EtaFamily` | 112 / 14 | `AutomorphicForm/Adelic/EtaFamily.lean` |
| `Def_AutomorphicForm_InducedSection` | 93 / 9 | `AutomorphicForm/Adelic/InducedSection.lean` |
| `Def_AutomorphicForm_WeylIntertwining` | 55 / 6 | `AutomorphicForm/Adelic/WeylIntertwining.lean` |

**The proof half** (indicative; the manager re-cuts a boundary, never moves a
declaration across a dependency):

| module | pin contents | ≈ lines |
|---|---|---:|
| `NumberTheory/AdelicLevel/Countability.lean` (**landed**) | `S4Base/AdelicCountability` (`isCountablyGenerated_uniformity_of_valued`, `secondCountableTopology_restrictedProduct`, `intLattice`'s home is `Coset`; `idealCount`/`zetaTerm` are `Fin`/`Place`) | 167 |
| `NumberTheory/AdelicHaar/PlaceMeasure.lean` | `S4Base/M4aS4` (`placeBorel`, `placeMeasure*`, `map_mul_left_volume_*`, `volume_image_mul_left_*`) and `S4Base/AdeleRing` (`distribHaarChar_eq_prod_norm_pow_mult_*`) | 500 |
| `AutomorphicForm/Adelic/WeylIntegrable/Coset.lean` | `Coset`, `ModFin` | 200 |
| `…/WeylIntegrable/Transfer.lean` | `Generic`, `Adelic`, `Generic2`, `Adelic2` | 250 |
| `…/WeylIntegrable/BoxBounds.lean` | `EntryBox`, `NormBounds`, `AdelicBoxSec` | 220 |
| `…/WeylIntegrable/LatticeEstimates.lean` | `PositiveChar`, `Pointwise`, `Lattices`, `R2`, `Fin`, `Place`, `Arch` | 730 |
| `…/WeylIntegrable/Assembly.lean` | `Asm`, `Served` (incl. the shared `…_impl`s) | 290 |
| `…/WeylIntegrable/UniformBound.lean` | `LatticeSum`, `Uniform` (the pair-only block) | 310 |
| `AutomorphicForm/Adelic/WeylIntegrable.lean` | the **façade**: the three headlines only; **tier 1** | 60 |

`S4Base` and the `S4Base`-only declarations are generic number theory / measure theory,
so by the mathematical-role cut they open `NumberTheory/` rather than living under
`AutomorphicForm/`; the `WeylIntegrable` sections are automorphic analysis.

## 4. The definition gate

The transitive `Definitions/` closure of the three `S_` files is 9 modules; 5 are
unwired, of which `Def_Mathlib_LinearAlgebra_Countable` (15 lines) is **already
transcribed** in the port as `FLTForHuman/LinearAlgebra/Countable.lean` (tier 3). The
genuine gate is **4 modules / 476 pin lines / 45 declarations**, and every one imports
only `AdelicLsXi` and `ConstantTerm`, both landed:

* `BorelSubgroup`: `borelSubgroup`, `mem_borelSubgroup_iff`, `borel_entry_one_zero`,
  `borelDiagFst`/`borelDiagSnd` and their `_apply_val`, `det_borel_eq_diag_mul`,
  `unipotentGL2_mem_borelSubgroup`, `borelDiagFst/Snd_unipotentGL2`, `adelicBorel`,
  `globalPoints_apply`/`_mem_adelicBorel`, `borelDiagFst/Snd_globalPoints`,
  `centralScalar_mem_adelicBorel`, `borelDiagFst/Snd_centralScalar`;
* `EtaFamily`: `re_add_half`, `cpowChar`, `cpowChar_apply_val`,
  `norm_cpowChar_apply`, `IsPrincipalTrivial`, `cpowChar_isIdeleClassChar`,
  `cpowChar_isUnitaryChar_of_re_eq_zero`, `etaFst`/`etaSnd` and `_apply`,
  `etaFst/Snd_isIdeleClassChar`, `etaFst_mul_etaSnd`, `norm_etaFst_apply_of_unitary`;
* `InducedSection`: `IsInducedSection`, `isInducedSection_zero`, `chiDet_mul`,
  `isInducedSection_chiDet`, `inducedSectionSubmodule`,
  `mem_inducedSectionSubmodule_iff`, `IsInducedSection.rightTranslate`,
  `rightTranslate_mem_inducedSectionSubmodule`, `isInducedSection_unipotent_mul`,
  `isInducedSection_centralScalar_mul`;
* `WeylIntertwining`: `gl2Weyl`, `gl2Weyl_val`, `gl2Weyl_inv`, `adelicWeyl`,
  `weylIntertwiningIntegral`, `weylIntertwiningIntegral_const`,
  `weylIntertwiningIntegral_zero_measure`.

The three `S_` files import `Mathlib` bare; the port replaces that with specific imports
(the house rule). Everything else the statements name — `AdelicGL2`, `globalPoints`,
`centralScalar`, `unipotentGL2`, `IsUnitaryChar`, `IsIdeleClassChar`, `chiDet`,
`adeleBorel`, `adelicAddHaar`, `distribHaarChar` — is landed.

## 5. Public API and checker wiring

* **All declarations are public at the pin** — neither `S_` file has a single `private`
  helper (273 / 272 top-level declarations). There is no promotion question and no
  two-body spelling trap; the port keeps every development declaration public at its pin
  name in the pin's namespaces.
* **Tier 1** is the façade's three headlines; the `identical` delta must be **+3**.
* **Tier 3** is everything else — the four gate modules and the eight development
  modules — registered by `tools/deps/unwired_register.py` in
  [spec/UNWIRED-PUBLIC.md](../../spec/UNWIRED-PUBLIC.md). Every transcribed declaration
  carries `-- pin: <name> (<S_ basename>:<line>)`.
* The six `S_AutomorphicForm_WeylIntegrable_*` descendants and the
  `weylIntertwiningIntegrand_finiteAdeleSlice_integrable_of_re_gt_half` sibling are
  **out of scope**; their declarations are already in the shared home.

## 6. The plan

Two stages.

**Stage 1 — the definition gate (manager, one wave; landed).** The four modules of §4,
whole nodes, at the homes above, tier 3, no promotions, no cascade. Transcribed
mechanically with `-- pin:` provenance on every declaration; all four tier-0 green at the
200,000 cap with 0 warnings and tier-1 green; the register gained 4 modules / 51 public
declarations, all with pin originals; the checker is unchanged.

**Stage 2 — the proof trio (two subagent turns, in series).**

| turn | sets | modules | pin spine | ≈ lines | state |
|---|---|---|---|---|---:|---|
| 1 | R1, R2 | `NumberTheory/AdelicLevel/Countability`, `NumberTheory/AdelicHaar/PlaceMeasure`, `…/WeylIntegrable/{Coset,Transfer,BoxBounds}` | `S4Base` → `AdelicBoxSec` | 1,090 | **landed** (1,610 lines, 168 declarations, tier-0 0 warnings) |
| 2 | R3, R4 | `…/WeylIntegrable/{LatticeEstimates,Assembly,UniformBound,Caps}`, `AutomorphicForm/Adelic/WeylIntegrable` (façade) | `PositiveChar` → the three caps | 1,390 | **landed** (1,777 lines; checker +3, milestone build 9,533 jobs) |

Turn 1 writes the generic base and the transfer/box layers; turn 2 the estimates,
assembly and the uniform bound, then the three caps and the façade. The manager reviews
the tree between turns. The cut may be re-balanced to hold ~1.2–1.6k lines per turn.

**Out of scope.** The descendant `WeylIntegrable_*` silos; the `LocalIntertwining` Tate
pair; the consumers (the whole Eisenstein-analytic layer is a later effort); any
`Definitions/` edit beyond the four gate modules; the `p2m_*` scaffolding.

## 7. Verification

* **Checker.** `timeout 300 python3 spec/check_flt_statements.py` — **9,238 → 9,241
  identical** (+3, the façade's three headlines), 0 mismatched, 0 missing, 38 own.
* **Build.** tier-0 at the 200,000 heartbeat cap, **0 warnings**; tier-1
  `flock .lake/flt_build.lock timeout 300 lake build <module>` per module; no whole-tree
  build while a set is in flight; never a heartbeat override.
* **Register.** `python3 tools/deps/unwired_register.py`; every new module's rows carry a
  `pin original`.
* **Axioms.** `#print axioms` on the three headlines is
  `[propext, Classical.choice, Quot.sound]`.
* **Mutation.** One-token mutation on each headline moves exactly one `mismatched`,
  reverted.
* **Consumer.** `spec/AutomorphicFormConsumer.lean` gains a zone per set, executed at a
  concrete `F`/`μ`/`ν`/`φ`; deleting any imported module must break its zone.

## 8. Risks and open questions

1. **The three-way merge is shallow but not a prefix.** The trio's development is a
   near-identical block; only the two `_impl` conclusions, the `rhs_hole`, and the
   `LatticeSum`/`Uniform` tail differ. The cousin's `_impl` is `private` with a `_root_`
   escape while the pair's is public — write the public pin name once and let the
   cousin's headline invoke it.
2. **Bare `import Mathlib`.** Both `S_` files import it; replace with specific imports.
3. **The `S4Base` homing.** `AdelicCountability`/`M4aS4` are generic; confirm the
   `NumberTheory/` homes do not collide with the `AdelicLevel`/`AdelicHaar` layers
   already there, and keep the pin namespace (`NumberField.AdelicCountability`,
   `M4aS4`) so statement text matches.
4. **Instance inference.** The block is measure-heavy; `maxHeartbeats` is never raised,
   and a low-cap failure is fixed by supplying the instance.
5. **Scope creep.** The six descendant `WeylIntegrable_*` silos and the local Tate pair
   stay out; do not pull their variants into the shared home.

## 9. Reproduce

```bash
cd tools/deps
python3 port_advise.py --nodes AutomorphicForm.continuous_bruhatTransversal_tsum_of_re_gt_half \
  --nodes AutomorphicForm.bruhatTransversal_summand_norm_summable_of_re_gt_half \
  --nodes AutomorphicForm.weylIntertwiningIntegrand_integrable_of_re_gt_half \
  --json build/weyl_trio_advise.json
python3 port_plan.py --json build/weyl_trio_advise.json --section all
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --include-leaves --rank-by silo --top 0
cd ../lean
timeout 300 python3 spec/check_flt_statements.py
```

The three pin sources are public at
`https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AutomorphicForm_bruhatTransversal_summand_norm_summable_of_re_gt_half.lean`,
`…_continuous_bruhatTransversal_tsum_of_re_gt_half.lean` and
`…_weylIntertwiningIntegrand_integrable_of_re_gt_half.lean`.
