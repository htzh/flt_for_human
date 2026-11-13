# SET-AF56 — the flat level-spherical test functions

**Status: LANDED (2026-11-13).** Read off the D–S shelf after SET-AF55 with the
recipe in [../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md).
The fifty-sixth set of the column, and the **story SET-AF55 readied**: both of the rows AF55's
landing put on the ready shelf belong to it (`isFactorizableTestFn_flat`, 63, and
`exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType`, 295, whose tenth premise *is* AF55's
B5), and the third is the product-integral constant the same family consumes
(`exists_pos_forall_rightConv_integral_prod_mul_indicator_…`, 437, whose five consumers are the
flat-spherical approximate-identity rows).

**3 rows / 795 silo / ≈700 net** in **two new modules**, no append, no definition gate, no promotion,
one order.

| # | row (`AutomorphicForm.` dropped) | silo | lev | home |
|---|---|---:|---:|---|
| **A** | `exists_pos_forall_rightConv_integral_prod_mul_indicator_eq_mul_integral_of_forall_integral_mul_apply_mul_eq` | 437 | **4/5** | new `Adelic/RightConvProductIntegral` |
| **B** | `CuspidalSpectrum.isFactorizableTestFn_flat` | 63 | 1/3 | new `Cusp/LevelSphericalTestFn` |
| **C** | `CuspidalSpectrum.exists_commute_lift_heckeCosetSum_of_isLevelSphericalOfType` | 295 | 1/1 | new `Cusp/LevelSphericalTestFn` |

## 0. The read

Same command as SET-AF55 §0, run after that set's landings (the proofs move nothing, so this is the
same read on the same marker set):

| figure | value |
|---|---:|
| `needed [F terminal]` | **678 / 289,813** |
| `needed [literal]` | 690 / 293,278 |
| frontier F | 1,739 / 837,739 |
| ready rows, all namespaces | **35 / 7,854** |
| leaves, all namespaces | **184 / 46,068** |
| `AutomorphicForm` ready rows | **13 / 2,988** |
| `AutomorphicForm` demand | 247 / 112,593 |
| withheld by the FR-0044 guard | 4 / 831 |

`--selfcheck` still names MD-005's ten and MD-006's one (both open, both the phi workstream's, neither
cited by anything cut here); the corrected frontier is 1,728 / 833,212 on the same subtraction as
SET-AF55 quoted (the plain read minus 4,527 lines).

**The premise audit is closed.** All fourteen premise nodes are ported, and — the SET-AF55 lesson —
each is reachable from its row's home, which for new modules is true by construction. The one that
matters most is AF55's own: C's tenth premise
`CuspidalSpectrum.apply_eq_zero_of_mem_orthogonal_cuspLevelSubcarrier_of_isLift_rightConv_of_rightInvariant`
is `Cusp/SpectrumOrthogonality.lean`, and B's two are `Cusp/ConstituentModulus.lean` (AF55's B4) and
`Adelic/IsotypicArchType.lean` (its archimedean twin).

**The definition gate is closed**: the four `Definitions/Def_AutomorphicForm_*` modules the three
wrappers import (`CuspidalSpectrumCarrier`, `FactorizableTestFn`, `ArchSpherical`,
`CuspidalSpectrumSubrep`) are all ported.

## 1. What the set says

- **A** — the reproducing convolution's product integral: for `x` continuous and `U`-invariant
  (`U ≤ K_f`, open and compact in the finite level), `rightConv x (∫ p, e p.1 e p.2 h((ι p.1)⁻¹ y (ι p.2)⁻¹) ∂(μᴬ × μᴬ) ·
  𝟙_{K_f}(y))` is a positive multiple of the archimedean integral `∫ a, x (g * adelicArchGLIncl a) h a`.
  The archimedean/finite Haar split (`exists_map_adelicGLHaar_eq_smul_prod`, SET-AF53), the finite
  sum over coset representatives, and the volume constant are the whole proof.
- **B** — `flat F σ f` is factorizable when `f` is: the modulus twist applied to a conjugated test
  factor, i.e. AF55's B4 (finite) and its archimedean twin composed.
- **C** — a level-spherical `f` of type `tys` makes a lift `T_c` commute with the Hecke coset sum at
  `g ∈ K_f`, up to the `U N`-coset bookkeeping: the row the flat level-spherical approximate identity
  spends to move a Hecke operator past a lift.

The three are one story: the flat/level-spherical test functions and the two technical rows the
approximate-identity family (five rows, lev 4/5 at the head of A's consumers) is built from.

### 1.1 What the set does not cut

- **`integral_mul_eq_integral_mul_weight_mul_tsum_sub_average_of_isCuspidalFn`** (635, 31
  declarations) — the cuspidal unfolding, planned as this set's second order and **cut at the
  scaffold**: its statement layer needs the adele ring's `MeasurableSpace`/`SecondCountableTopology`
  instances settled. The pin's prelude derives them privately and one of the two derivations has no
  v4.34 counterpart (`RestrictedProduct.secondCountableTopology` is gone), while the port pins the
  measurable space per module as a `local instance` (`NumberField.AdelicHaar.adeleBorel`); a wave
  that re-derives them would be paying a definition-layer question inside a proof set. The row goes
  back on the shelf under SET-AF53's ruling for the adelic-box pair (the same shape of deferral, for
  the same reason), and a definition-layer set should take it.
- The other eleven `AutomorphicForm` ready rows and all 184 leaves: as listed in
  [SET-AF55.md](SET-AF55.md) §1, unchanged. The head of the remaining block is now the content/height
  row (333), the level-one obstruction (229) and the `K`/`f`-smooth factorization (209) — three
  different subjects, none sharing a premise with this set.

## 2. The price

| figure | SET-AF56 |
|---|---:|
| raw `S_` lines | 795 |
| declaration lines | 700 (A's eight helpers are private and short; C is one long proof) |
| declarations | 12 (A: 8 private helpers + headline; B: 1 private helper + headline; C: headline) |
| `port_plan` net new math lines | **≈700** |
| substitutes | none needed (no prelude row of the three files is already in the port) |
| `twin_scan` | `new` for all three |

A's and B's preludes are **`private` in the pin**, so the modules' public surface is the headline
alone — the checker checks 1 (A) and 2 (B+C) declarations, which is the whole statement gate.

## 3. The homes and the manager's landed layer

| module | rows | imports added | lines | decls | `sorry` | `check_port` |
|---|---|---|---:|---:|---:|---|
| `Adelic/RightConvProductIntegral.lean` (new) | A | `ProductMeasure`, `AdelicLevel/Countability`, `MaximalCompactFactors`, `ArchComponentDictionary`, `RightConvPreservation`, `IsotypicCuspSpace` | **159** | 9 | 9 | **1 ok / 0 / 0** |
| `Cusp/LevelSphericalTestFn.lean` (new) | B, C | `ConstituentModulus` (AF55), `IsotypicArchType`, `RightConvCosetSum`, `RightConvPreservation`, `Spectrum{Orthogonality,Lift,Translation,ConvAction,Pairing,Carrier,CarrierAPI}`, `IsotypicCuspSpace`, `ArchWeightChar` | **120** | 3 | 3 | **2 ok / 0 / 0** |

Both elaborate at the low cap, both build (`lake build`, 4,089 and 4,275 jobs, silent), and both were
`check_port`-green before dispatch — so the worker only ever fills the twelve bodies. The pin's label
namespaces are rectified to words (`ReproConvProof` → `RightConvProduct`, `FlatFactProof` →
`FlatFactorizability`); no token survives in a port name. No `set_option` beyond `autoImplicit false`.

**One scaffold deviation found and kept**: module A's prelude opens the adelic `glBorel`/`borelSpace`
local instances and the pin's own `attribute [-instance]` shims are dropped (the port's instances are
the interface); B/C's module needs the `WindowedSiegel`/`SiegelCovering` opens for
`centreCutSiegelSet`, which the generated opens list did not carry at first.

## 4. The order and the gates

One dispatch: `tmp/af56/WORKORDER-AF56A-flat-level-spherical.md`. The gates are the recipe's §6,
written into the order: no tree build; the edit loop at `-DmaxHeartbeats=200000`; `lake build
<module>` under `flock`/`timeout` per finished file; `check_port` at **0 mismatch / 0 missing**;
`#print axioms` on the three headlines `[propext, Classical.choice, Quot.sound]`; zero warnings; no
`sorry`; no `set_option` beyond `autoImplicit false`; no silencer; `dedup.py` / `move_dead.py` clean;
one consumer zone with an executed composition per headline.

## 5. Forecast and the re-read

`needed` 678 / 289,813 → **675 / 289,018**; frontier **+795**; the `AutomorphicForm` demand
247 / 112,593 → **244 / 111,798**; the block 13 / 2,988 → **10 / 2,193**. Because the shelf reads
declared statements, the forecast is measured as soon as the scaffolds are in — §6.

## 6. The shelf effect, measured (statements in, proofs in flight)

| figure | before | **after** | forecast |
|---|---:|---:|---:|
| `needed [F terminal]` | 678 / 289,813 | **675 / 289,018** | 675 / 289,018 ✓ |
| frontier F | 1,739 / 837,739 | **1,742 / 838,534** | +795 ✓ |
| ready rows | 35 / 7,854 | **32 / 7,059** | — |
| `AutomorphicForm` demand | 247 / 112,593 | **244 / 111,798** | 244 / 111,798 ✓ |

## 7. The landing record (2026-11-13)

Three rows, two modules, **584 written proof lines** (326 + 258) over the 279 scaffold lines,
**12 `sorry`s → 0**, no imports added, no `set_option` added, and no statement, import, namespace,
`open`, `spec-pin:` line or docstring touched — `check_port` reads the dispatch figures unchanged.

| module | lines | decls | `sorry` | build | `check_port` | axioms |
|---|---:|---:|---:|---|---|---|
| `Adelic/RightConvProductIntegral.lean` | 159 → **485** | 9 | 9 → **0** | 4,089 jobs, 9.4 s, silent | **1 ok / 0 / 0** | clean |
| `Cusp/LevelSphericalTestFn.lean` | 120 → **378** | 3 | 3 → **0** | 4,275 jobs, 9.0 s, silent | **2 ok / 0 / 0** | clean |
| | **279 → 863** | **12** | **12 → 0** | | **3 ok, 0 mismatch, 0 missing** | **3/3** |

`#print axioms` on all three headlines: `[propext, Classical.choice, Quot.sound]`; `#check` at each
fully qualified name resolves. `dedup --within` (all tiers): 0 clusters, 0 removable lines, on both.
`move_dead --dry-run`: 0 declarations, 0 lines, 0 live private helpers, on both. Consumer zone
`spec/AutomorphicFormSetAF56AConsumer.lean` (182 lines, three executed compositions, no `#check`, no
`sorry`): A's positive constant spent as a vanishing-iff, B iterated twice to
`flat σ₂ (flat σ₁ f)`, C composed through `hcomm` with a right convolution. **0 errors**, silent.

**Both proofs are line-for-line transcriptions**, so the row-level record is the pin's block map:
A's eight helpers at pin `:34`, `:40`, `:54`, `:80`, `:91`, `:125`, `:153`, `:180` and the headline
`:277`; B's helper `:24` and headline `:40`; C's single proof `:29–295`.

**Heartbeats**: A peaks at ≈23.5k in `repro_integral` (fails 23,000, passes 24,000); C is the file's
pole at ≈82.5k (fails 82,000, passes 83,000) and B fits 20,000. All far under the 200,000 gate and
none an instance-inference defect.

**The one real friction (FR-0195).** `Finset.map_noncommProd` cannot be used inside a `rw` at v4.34:
the rule's right-hand side is `fun _ hx _ hy _ => (comm.forall₂ hx hy).map g`, which needs
`Set.Pairwise`/`Function.onFun` unfolded, and `rw` elaborates at *implicit* transparency, so the
target is "not type-correct under the `implicit` transparency level" — nothing to do with the
subgroup `let` the pin wraps it in. The fix is not a silencer and not a cap: state the map step as a
closed `have` (which elaborates at default transparency) and `rw` with that. Recorded in
[../../logs/frictions.md](../../logs/frictions.md) and in
[../../CARRY-FORWARD.md](../../CARRY-FORWARD.md) for the next port that touches `noncommProd`.

The other six adaptations are the standard v4.34 set and were all statement-preserving: five
`omit … in` prefixes for `linter.unusedSectionVars`, `haveI`→`have` (and `letI mF`→`let mF`), 
`orthogonalProjection`→`orthogonalProjectionOnto`, `ContinuousLinearMap.coe_sum'`→`FunLike.coe_sum`,
`properSpace_completion` qualified to `WindowedSiegel`'s (ambiguous with `AdelicBox`'s), and the
pin's private helpers qualified by their label namespace where the headline stands outside it. The
manager's dropped `attribute [-instance]`/`attribute [-simp]` shims never mattered: every `simp` in
both files is `simp only` with explicit lemmas, which is also why both rows transcribed verbatim.

**SET-AF55's premises held**: `Cusp/ConstituentModulus.lean`'s finite modulus twist and
`Cusp/SpectrumOrthogonality.lean`'s orthogonality row were used as-is and behaved exactly as the pin's
argument expects — no defect to report against the previous set.

## 8. Reproduce

```bash
cd tools/deps
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/shelf12.json
python3 ../tmp/af56/gen.py                      # the two scaffolds
cd .. && python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/RightConvProductIntegral.lean
python3 spec/check_port.py --force FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelSphericalTestFn.lean
```
