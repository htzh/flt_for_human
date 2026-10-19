# TOPIC — the continuous norm section: one node, one tier-3 engine, one headline

**Status (landed 2026-10-18).** The order that ran this note is
[WORKORDER-T4-norm-section.md](WORKORDER-T4-norm-section.md). The landing record is §7.

**Pin.** `anthropics/fermats-last-theorem` at `aa2d8b3`; the port's mathlib is `v4.34.0`.

**Method.** The six-step loop of
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3, its §4 and
[porting-playbook.md](../../../porting-playbook.md) §2–§5.

**Companions.** [TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md) — the
sibling `M4aLocalCFT.FujisakiC3` block (`normQ`, `continuous_ideleNorm`), whose engine
`TateGlobal/FujisakiC3.lean` this note's block deliberately does *not* join. The
mathematics of the idele norm itself is [math/027](../../../../math/027-the-continuity-of-the-idele-norm.md).
The node sits on the shortest citation path from the D-S gate up to `fermatLastTheorem`
(§1) and is reached by the `LanglandsTunnell`/`AutomorphicForm` layers, so it is a
`NumberField` row the D-S column does reach — the row [../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md)
§2 lists under "the `NumberField` rows the target closure reaches", now cut.

## 1. The node

| | |
|---|---|
| pin statement | `Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean` (9 lines) |
| pin proof | `P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean` (901 lines, 68 declarations) |
| statement | there is a continuous `s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` with `ideleNorm F (s r) = r` and trivial finite part |
| proof imports | four pin `Definitions/` modules: `Def_NumberField_TateGlobalZeta`, `Def_LanglandsTunnell_TateLocalZeta`, `Def_NumberField_AdelicLevel`, `Def_M4aHerbrand_IdeleClassVocab` — all four already homed in the port |
| graph position | a leaf: the whole demand is the node (`frontier.py --target … → needed 1 node / 901 lines`) |
| fan-in | 0 direct dependents inside the D-S cone by `frontier.py`'s count, **57 whole-project**, and it is on the shortest citation path to `fermatLastTheorem` (via `NumberField.TateGlobal.exists_isFundamentalDomain_principalIdeles_forall_exists_integrableOn_min_ideleNorm_pow`) |

**The mathematics.** The idèle norm is a continuous surjection `(AdeleRing)ˣ → ℝ≥0`
(`continuous_ideleNorm`, the sibling block), and this node splits it *continuously*: it
produces a monoid hom `s` with `ideleNorm ∘ s = id`, supported entirely at one
archimedean place. At a real place the completion is `ℝ` (`IsReal`) and `e = ringEquivRealOfIsReal`
is an isometry, so `r ↦ e.symm r` works; at a complex place it is `ℂ` and `w.mult = 2`, so
`r ↦ e.symm (√r : ℂ)` has norm `r^(1/2)` and the second power gives `r`. `localSection`
merges the two by `if hv : IsReal w`, `normSectionAt = archUnitHom w ∘ localSection` pushes
it into the idèles (finite part `1` by construction), and `ideleNorm_archUnitHom`
(already in the port) computes the norm. The headline instantiates at
`Classical.arbitrary (InfinitePlace F)`.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq \
  --json build/cmh_ideleNorm_advise.json
python3 port_plan.py --json build/cmh_ideleNorm_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines | 901 |
| declaration lines / groups | 863 / 68 |
| duplicate copies inside the target | 0 |
| already in the port (vetted, all tier 3) | 684 |
| **net new math lines** | **179** |
| substitutions | 40 trusted / 2 suspect |
| new declarations | **25** |

The 2 suspect rows are the parser's type-only `def` artefact (`archBox`, `box`
"matching" `Type`-shaped port declarations) and are not needed. The 684 in-port lines are
the silo's T1 prelude — the same `archSlab`/`distribHaarChar`/`ideleNorm_archUnitHom` block
the T1 set homed — so the port is **one 130-line engine + one 30-line façade**, not a
901-line transcription.

**The new block**, pin lines 728–901 (`Fold_FujisakiC3c` and `Fold_FujisakiC3e`):

| group | declarations | pin lines |
|---|---|---:|
| continuity of `archUnitHom` | `continuous_archUnitHom_val`, `continuous_archUnitHom` | 729–745 |
| the norm hom into units | `ideleNormU`, `val_…`, `coe_val_…`, `…_eq_one_iff`, `…_of_mem` | 774–787 |
| real/complex sections | the `norm_ringEquiv*_symm` / `continuous_ringEquiv*_symm` pair, `realSectionOfIsReal`, `realSectionOfIsComplex`, their `val_` and `continuous_` lemmas | 794–842 |
| the merged section | `localSection`, `continuous_localSection`, `norm_localSection_pow_mult` | 847–864 |
| transport to the idèles | `normSectionAt`, `…_apply`, `continuous_normSectionAt`, `ideleNorm_normSectionAt`, `ideleNormU_normSectionAt` | 866–878 |
| headline | `solution` | 893–901 |

## 3. The block is shared by nine files — the reason to home it

`grep -rl` over the pin's `P2M/Sol/` finds the **same 25 declarations in nine `S_` files**:

```
S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq          <- this node
S_NumberField_TateGlobal_exists_differentiable_eq_partialEulerProduct_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_exists_eq_normPowChar_of_forall_mem_normOneIdeles
S_NumberField_TateGlobal_exists_meromorphicOn_analyticAt_one_eq_partialEulerProduct_of_ne_one
S_NumberField_TateGlobal_exists_meromorphicOn_eq_partialEulerProduct
S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_norm_le_of_re_mem_Icc_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_zetaIntegral_entire_continuation_fe_of_exists_mem_normOneIdeles_ne_one
S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe
S_NumberField_TateGlobal_zetaIntegral_meromorphic_continuation_fe_analyticAt_one_of_ne_one
```

This is the `normQ` family of [TOPIC-continuous-ideleNorm.md](TOPIC-continuous-ideleNorm.md)
§3 with one substitution: `continuous_ideleNorm` carries the `normQ` block and not this one,
this node carries this one and not `normQ`. The union is ten files; the section block is the
second shared prelude of the family, and the eight `normQ` siblings import it when their
orders come. Porting it privately inside this node's module would set up eight later orders
to re-prove 130 lines each — the failure mode §3 of the sibling note was written to prevent.

Two of the nine are in the D-S cone (`exists_meromorphicOn_eq_partialEulerProduct`,
`zetaIntegral_meromorphic_continuation_fe`); the other seven are family-column work. The
engine is justified family-wide, as `FujisakiC3.lean` was.

## 4. The port structure

* **Engine** `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean`, tier 3,
  unlisted: the 25 declarations, public, at the pin names, namespace
  `NumberField.TateGlobal.FujisakiC3`, each with a `-- pin:` marker. Import block: the two
  port modules the 25 lines actually name (`…/TateGlobal/Defs.lean` for `ideleNorm`,
  `normOneIdeles`, `archUnitHom`; `…/TateGlobal/ArchNorm.lean` for `ideleNorm_archUnitHom`
  and, transitively, `ArchMulHaarCompletion.nnnorm_ringEquivReal/Complex`) plus one mathlib
  file for `NNReal.sqrtHom` if it is not already in that cone.
* **Façade** `FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean`, listed, one
  headline.

**Why not append to `TateGlobal/FujisakiC3.lean`.** Same pin namespace, adjacent pin
sections (`Fold_FujisakiC3d` / `e`), so appending is defensible — but the `normQ` engine
drags the 11k-line T1 cone (Coordinates, ZetaIntegrand, IntLocalIntegrability,
NormIntegrable) and the section needs none of it. A consumer of the section then pays for
the T1 analytic core it does not use. The wave is also real: `build_ladder.py --edit
…/TateGlobal/FujisakiC3.lean` is 6 modules / 2,143 lines / ≈27 s, and
`…/TateGlobal/ArchNorm.lean` 7 / 3,655 / ≈45 s. **This order edits nothing**, so it owes no
wave at all.

**Why not reuse the landed façade `TateGlobalContinuousIdeleNorm.lean`.** Its subject is the
*continuity* of the idèle norm; this one is a *section* of it. Same directory, different
story, and adding it there would mis-describe the module (and force the 6-module wave). A
second listed wire for `TateGlobal/` is the trade-off the sibling note already took once
(§7 risk 1 there); the cost is one more `PORT_FILES` entry, the benefit is that the 57
project dependents of the section do not rebuild when the T1 façade changes.

## 5. Recorded negatives

* `norm_ringEquivRealOfIsReal_symm` / `norm_ringEquivComplexOfIsComplex_symm` **look**
  substitutable and are not: the pin proves the same statement inline inside
  `TateGlobal/ArchNorm.lean`'s `exists_norm_pow_mult_eq` (not as a declaration), and a public
  copy exists at `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean:691,703` under
  a different namespace — importing `AutomorphicForm` from `NumberTheory/TateGlobal` would
  invert the tower. They are re-proved in the engine (10 lines) and the docstring says why.
* The pin's two `scoped instance`s (line 16 `LocallyCompactSpace (AdeleRing …)ˣ`, line 36
  `instSecondCountableCompletion`) are prelude for the T1 half of the silo. They are **not**
  ported: a `scoped instance` in the engine would change instance search in every importer,
  and no line of the new block needs either.
* The two `exists_norm_apply_eq_ideleNorm_rpow` cousins (`NumberField.TateGlobal.…` 236
  silo lines, `RatIdele.…` 312) are on the ready shelf and share only the
  `continuous_archUnitHom` pair with this block (plus a 15-line `expUnit` block with each
  other). Priced together with this node they are **675 net new lines**, i.e. this set costs
  179 and they are 496 of real content — a separate story (a continuous idèle-class
  character's absolute value is a power of the norm) and a separate order, not a rider.

## 6. Reproduce

```bash
cd tools/deps

# the node's budget
python3 port_advise.py --target NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq \
  --json build/cmh_ideleNorm_advise.json
python3 port_plan.py --json build/cmh_ideleNorm_advise.json

# the same block across the family (nine files)
grep -rlE "^(private )?(noncomputable )?(theorem|def) normSectionAt\b" \
  ~/proj/fermats-last-theorem/P2M/Sol/

# the trio, if the cousins are ever cut together with this node
printf '%s\n' NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq \
  NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow \
  RatIdele.exists_norm_apply_eq_ideleNorm_rpow > build/normsec_targets.txt
python3 port_advise.py --targets build/normsec_targets.txt --json build/normsec_advise.json
python3 port_plan.py --json build/normsec_advise.json

# the hosts this order deliberately does not edit
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/FujisakiC3.lean
python3 build_ladder.py --edit FLTForHuman/NumberTheory/NumberField/TateGlobal/ArchNorm.lean
```

## 7. Landing record

| | |
|---|---|
| engine | `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean` — 239 lines, 25 public declarations, tier 3, unlisted |
| façade | `FLTForHuman/NumberTheory/NumberField/TateGlobalNormSection.lean` — 44 lines, 1 headline, listed |
| checker | **10,343 identical / 0 mismatched / 0 missing** / 42 own-proof exempted / 294 registered-unwired (was 10,342 / 0 / 0 / 42 / 294) |
| axioms | headline `[propext, Classical.choice, Quot.sound]` |
| build | tier-0 both modules exit 0 / 0 warnings; tier-1 façade green (3684 jobs) |
| register | 128 → 129 modules, 4030 → 4055 public declarations, all 25 with a pin counterpart |
| existing modules edited | **none** — no promotion, no hub edit, no wave |

Three proof adaptations, two drifts (`Continuous.update`'s family named in
`continuous_archUnitHom_val`; `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right` in
`continuous_localSection` and `norm_localSection_pow_mult`); every statement is the pin's.
The order's §6.1 fallback (`Units.continuous_val (M := …)`) is *not* what worked — see the
full record, [logs/norm-section.md](../../../logs/norm-section.md) §5, and the corrected
report in [WORKORDER-T4-norm-section.md](WORKORDER-T4-norm-section.md) §8.
