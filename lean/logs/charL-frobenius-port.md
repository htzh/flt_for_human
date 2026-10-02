# charLFrobenius — the `q`-expansion `Fr* Fr_* = ℓ` relation, port record

Topic: [`topics/charLFrobenius/TOPIC-qexp-frobenius-modl.md`](../topics/charLFrobenius/TOPIC-qexp-frobenius-modl.md)
(measured, not started). Pin `aa2d8b3`; mathlib `v4.34.0`.

Landed `ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental`
(the relation `Fr* Fr_* = ℓ` on `Pic⁰` of the `q`-expansion function field in
characteristic `ℓ`), its ten prerequisite theorem nodes, the `qExpFrobenius*`
definition layer, and one extra prerequisite the pin's `hasPrincipalDivisors`
`S_` file reaches (`AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors`)
plus the last literal frontier node it drags
(`…eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum`).

## 1. Written lines vs budget

| item | pin raw | port lines |
|---|---:|---:|
| `Algebra/IsSeparableFrobenius.lean` | 71 | 102 |
| `AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean` | 399 | 428 |
| `AlgebraicCurve/IsCurveOver/PerfectField.lean` | 148 | 180 |
| `AlgebraicCurve/IsCurveOver/Transcendental.lean` | 57 + 19 | 92 |
| `AlgebraicCurve/PrincipalDivisors/IsSeparable.lean` | 192 + 39 | 248 |
| `AlgebraicCurve/Place/FiniteResidue.lean` | 89 | 126 |
| `ModularCurve/Frobenius/Defs.lean` | 311 (+ the generic pieces) | 469 |
| `ModularCurve/Frobenius/QExpModL.lean` | 568 | 575 |
| extensions: `Divisor`, `KaehlerTranscendental`, `RatFuncDegree`, `JqIntegralRatios` | ~30 | 115 |
| **total** | **≈1,900** | **≈2,335** |

The topic budget was **≈1,900 … 2,900 written lines**, so the effort landed in
band (≈1.23 × the pin's needed raw lines, in the AC 1.25–1.45 / MC 1.0–1.3
ratio). The measured cone is 11 needed nodes / 1,669 raw lines plus the
definition layer; the +1 prerequisite and its literal tail add 30 raw lines.

**Set A/B/C execution.** Set A (the generic perfect-field engine and the
`Algebra` leaf) and Set B (the definition layer and the Frobenius-subfield
engine) were written first, bottom-up; Set C (the target and its `QExpFrobRel`
block) was the wire test and compiled against the frozen Set A/B names without a
re-scope. One `lake build` per wave, serialized under `flock`.

## 2. Dedup answer — was the generic `FrobeniusModL` module needed?

**No.** FLT writes the `qExpFrobenius*` API twice:
`Def_ModularCurve_QExpFrobeniusModL.lean` (311 lines) on `qExpFunctionFieldC K Γ`
and `Def_ModularCurve_FrobeniusModL.lean` (342 lines) on
`modularFunctionFieldFullC K N`. Diffing the declaration bodies shows they are
the same construction with `qExpFunctionFieldC K Γ` substituted for
`modularFunctionFieldFullC K N`; the only carrier-dependent input is
`frobeniusModL_map_le` (that `qExpand K ℓ` maps the generators into the field),
and for the `qExp` carrier that is `qExpFrobeniusModL_map_le`, proved from the
`intSeriesC` Frobenius identity exactly as in the pin.

Neither the target nor any declaration in its `QExpFrobRel` block names anything
from the generic module. The port therefore writes **only** the `qExp` copy and
leaves `modularFunctionFieldFullC` unported. Only the pieces whose *proofs* the
`qExp` copy genuinely consumes are ported, into `Frobenius/Defs.lean`:
`intCast_pow_char_eq`, `qExpand_ofPowerSeries_eq_expand`,
`pow_char_single_one_eq`, `pow_char_ofPowerSeries_eq`,
`pow_char_eq_coeffMap_frobenius_qExpand`, `charP_laurentSeriesC` (from
`Def_ModularCurve_FrobeniusModL.lean`) and `qExpandAlgHomC`,
`qExpandAlgHomC_apply`, `coeffMap_ofPowerSeries` (from
`Def_ModularCurve_X0ModL.lean`).

**Saving: ≈342 lines of duplicated API + the unported
`modularFunctionFieldFullC`/`jqModC` theory of `Def_ModularCurve_X0ModL.lean`
(156 lines) + its two deferred wrappers**
(`Thm_ModularCurve_pow_char_eq_qExpand_of_coeff_fixed`,
`Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional`). This is the answer the
topic asked for and it sets the price of the next char-ℓ Frobenius topic: a new
carrier costs only its `map_le`/generator Frobenius identity, and the rest of the
`Place`/`Divisor`/`Pic0` packaging can be reused verbatim from
`Frobenius/Defs.lean` by substitution, not by a generic module.

A second dedup: the pin's private `coeffMap_qExpand'` in the target's `S_` file is
the already-public `ModularCurve.coeffMap_qExpand` (`Defs/Laurent.lean`), so the
port calls it rather than re-deriving it. A third: the pin's private
`principalDivisorOf` is the ported `RationalFunctionField.principalDivisorOf`
(`P1/DXCoeff.lean`). A fourth: the pin's private
`isAlgebraic_adjoin_of_transcendental` reuses the ported
`AlgebraicCurve.isAlgebraic_adjoin_of_transcendental` (`Place/DegreeOne.lean`).

## 3. Mathlib substitutions and recorded negatives

Reuse wins (a pin declaration replaced by a mathlib call):

- The whole `finrank_frobeniusSubfield_eq_of_transcendental` proof is an assembly
  of mathlib's `Subfield.relfinrank_comap_comap_eq_relfinrank_of_le`,
  `Subfield.relfinrank_mul_relfinrank`, `Subfield.relfinrank_map_map`,
  `lift_rank_eq_of_equiv_equiv`, `basisOfLinearIndependentOfCardEqFinrank`,
  `linearIndependent_pow`, `X_pow_sub_C_irreducible_of_prime`,
  `IntermediateField.adjoin.finrank` and `Polynomial.natDegree_le_of_dvd`. No
  mathlib lemma computes a Frobenius-subfield index.
- `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable` is
  `Field.exists_primitive_element` + `Polynomial.SplittingField.splits` +
  `IsGalois.of_separable_splitting_field` + `Algebra.norm_eq_prod_automorphisms` +
  `IsGalois.card_aut_eq_finrank`; the pin's `degree_eq_finrank_mul` /
  `Place.ord_prod'` / `sum_smul_apply_eq_ord_prod` / `degree_eq_zero_of_isGalois`
  are FLT's.
- `IsSeparableFrobenius` is `IntermediateField.isSimpleOrder_of_finrank_prime`
  plus the Kähler-differential subsingleton argument.
- `Place.finite_residueField_of_finiteDimensional` is `rank_le` +
  `Cardinal.natCast_lt_aleph0`.

Recorded negatives (searches that found nothing):

- No mathlib statement of `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`
  or its converse in the form the pin needs; the criterion is bespoke.
- No mathlib Frobenius-subfield index computation, hence no shortcut for
  `finrank_frobeniusSubfield_eq_of_transcendental`.
- No mathlib analogue of `exists_separating_transcendental_of_perfectField`.
- **The port's own `IsCurveOver.exists_separating_transcendental`
  (`IsCurveOver/SeparatingTranscendental.lean`) is a *different* statement** —
  `[IsCurveOver K F]` + `[Algebra.EssFiniteType K F]` rather than
  `Transcendental K x` + `FiniteDimensional K⟮x⟯ F`. It is a downstream curve-level
  corollary, not this node; `#check`-ing it first (as the topic asked) records the
  negative.
- No mathlib statement bounding the residue-field extension of a place by the
  field-extension degree.
- `RationalFunctionField.hasPrincipalDivisors` has no mathlib counterpart (the
  notion is FLT's); the port proves it from the two already-ported ingredients.

## 4. The `PerfectRing` answer

The pin's target proof runs under `[PerfectRing K ℓ]`; the wrapper omits it
because `[IsAlgClosed K]` + `[CharP K ℓ]` supply it by instance. At the port's
spelling instance search did **not** derive it (the `S_` file itself declares
`scoped instance perfectRing_of_isAlgClosed`), so the port reproduces that as a
`private instance perfectRing_of_isAlgClosed : PerfectRing K ℓ` inside the
`QExpFrobRel` namespace, from `IsAlgClosed.perfectField K` and
`PerfectField.toPerfectRing ℓ`. The public statement is therefore exactly the
wrapper's, with no added hypothesis. This is the only `PerfectRing`-shaped
instance the cone needs.

## 5. Consumer-zone decision

`spec/ModularCurveConsumer.lean` gains **Zone W**, stated in **hypothesis form**:
the two examples carry `hF` (the existence of a transcendental generator of
`qExpFunctionFieldC K Γ` with finite-dimensional extension) as a hypothesis.
Discharging `hF` concretely requires the unported `functionFieldGeneration` Set A
(the field-of-ratios content of
[`topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md`](../topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md)),
so a concrete `K`, `Γ`, `y` is not available in this topic's scope. The zone
genuinely *uses* the target: the first example composes it with `Eq.symm`, the
second applies it at `y = 0` and rewrites with `nsmul_zero`. There is no `#check`
and no `sorry` in the zone. `lake env lean spec/ModularCurveConsumer.lean`
exits `0`.

The zone is the "hypothesis form with the reason recorded" the playbook requires,
not a silently dropped zone.

## 6. The `#print axioms` result

```
ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental
  depends on axioms: [propext, Classical.choice, Quot.sound]
```

The same for `AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField`,
`exists_separating_transcendental_of_perfectField`,
`finrank_frobeniusSubfield_eq_of_transcendental`,
`hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`,
`Place.finite_residueField_of_finiteDimensional`,
`kaehlerRankOne_of_transcendental` and
`Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq`. No `sorryAx`. The
`#print axioms` probe lives in the gitignored `lean/tmp/Scratch.lean`, not in a
library module.

## 7. Checker and frontier

`spec/check_flt_statements.py`: **4,201 identical / 0 mismatched / 0 missing
before → 4,263 identical / 0 mismatched / 0 missing after**, 30 own-proof
exemptions (unchanged). The 62 new identical declarations are the 11 target
wrappers, the four definition modules' declarations, the 12th prerequisite
(`RationalFunctionField.hasPrincipalDivisors`) and its literal tail, and the
`Divisor.degree_eq_sum` extension. No `OWN_PROOFS` entry was needed: every new
public declaration is a pin transcription, and every helper in the target's
`QExpFrobRel` block is `private`.

The checker was self-tested with a one-token mutation (`Fin 2` → `Fin 3` in the
target's `Γ` binder): exactly `4,261 identical / 1 mismatched / 0 missing`, then
reverted.

`tools/deps/frontier.py --target
ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental --top 0`
now reports **`needed [F terminal] 0 nodes / 0 lines`** and
`needed [literal] 0 nodes / 0 lines`, i.e. the whole cone is ported. (Before the
effort: 11 needed / 1,669 raw.) The last literal node,
`AlgebraicCurve.RationalFunctionField.eq_placeInfty_iff_forall_ne_ofHeightOneSpectrum`,
was hidden by a name-based "ported" false positive: `RationalFunctionField.hasPrincipalDivisors`
collides with `IsCurveOver.hasPrincipalDivisors`.

## 8. Friction

1. **The frontier's name-based "ported" test is an upper bound.** It counted
   `AlgebraicCurve.RationalFunctionField.hasPrincipalDivisors` as ported (last-name
   collision with `IsCurveOver.hasPrincipalDivisors`), so the topic's 11-node
   measure omitted it even though the pin's `hasPrincipalDivisors_of_finiteDimensional_of_isSeparable`
   `S_` file imports its wrapper. The build surfaced it (`Unknown identifier
   RationalFunctionField.hasPrincipalDivisors`); it and its literal tail were
   ported and wired. Net effect on the topic's node count: 11 → 12 (plus one
   3-line corollary). Recorded so the next measure re-checks last-name collisions.
2. **`lake env lean` does not build dependency oleans.** `PerfectField.lean`
   initially failed with "object file … FrobeniusSubfield.olean does not exist"
   because Set A had only been tier-0-checked; a `lake build <dep>` fixed it.
   Not a math error, just the ladder.
3. **`synthInstance` budget, not `maxHeartbeats`.** Two `IsCurveOver`/`CharP`
   syntheses timed out at the *default* `synthInstance.maxHeartbeats` (20,000)
   inside `QExpModL.lean`; the pin's `S_` file sets `set_option
   synthInstance.maxHeartbeats 1600000`, and the port transcribes it. No
   `maxHeartbeats` was raised anywhere.
4. **v4.34 drift met and fixed**: `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`
   (in `Frobenius/Defs.lean` and the target's `coe_norm_PP`'s `if_neg` →
   `ite_eq_right`); `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`
   (`IsSeparableFrobenius.lean`); `Algebra.FormallyUnramified.isSeparable` gained
   an `Algebra.EssFiniteType` requirement, supplied by `[FiniteDimensional E F]`.
   Two declaration-shape facts: explicit binders must be spelled in the port when
   the wrapper spells them (`Divisor.degree_eq_sum` had to move off the section
   `variable {K F}`), and a redundant explicit `[CharP K ℓ]` on the private
   `charP_FF` (the section already had one) tripped the overlapping-instances
   linter and was dropped.
5. **No heartbeat wall.** The `399`-raw `finrank_frobeniusSubfield_eq_of_transcendental`
   — the topic's named heartbeat/defeq risk — elaborates in 6.9 s at the project
   cap. `frobeniusQuadratic`-style `QExpFrobRel` defeq blow-ups did not appear;
   the full target module is ~46 s of `lake build` and ~21 s of tier-0 check.

## 9. Reproduce

```bash
cd lean
flock /tmp/flt_for_human.lock timeout 60 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false \
  FLTForHuman/ModularCurve/Frobenius/QExpModL.lean
flock /tmp/flt_for_human.lock timeout 300 lake build \
  FLTForHuman.ModularCurve.Frobenius.QExpModL
python3 spec/check_flt_statements.py
flock /tmp/flt_for_human.lock timeout 300 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false spec/ModularCurveConsumer.lean
cd ../tools/deps && python3 frontier.py --target \
  ModularCurve.qExpFrobeniusPullbackModL_qExpFrobeniusPushforwardModL_of_transcendental --top 0
```
