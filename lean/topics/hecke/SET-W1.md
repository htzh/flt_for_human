# SET W1 — create the level-family shared homes

**Status: partially executed (W1a–c landed; W1d–e remain).** Second set of the
[WeightOne rectification](TOPIC-weightone-rectify.md), and the foundation: it creates the
shared-home modules for the **level family**. The executor first tried an open-ended
subagent run, which stalled twice without producing files; the manager then executed the
closed-region homes directly and established the recipe below. SET-W2's first rewire
(`Basic`) has already landed against the homes created here.

## Execution record

| order | module | source | status |
|---|---|---|---|
| W1a | `ModularForms/WeightOne/Defs/PeriodPair.lean` | the `WLight` prelude, 5 files | **done**, green, 3 s |
| W1b | `ModularForms/QExpansionCoeff.lean` | `Basic.lean` §`Width`/`WidthMF` | **done**, green, 0 warnings |
| W1c | `ModularForms/DiscPow.lean` | `Basic.lean` §`RatCoeff`/`DiscPow`/`BSix`/`KPoleSec` | **done**, green, 0 warnings |
| W1d | `ModularForms/WeightOne/Defs/PTorsion.lean` | `FrickeFunction`/`WeierstrassPTorsion` ℘-torsion prelude | **done** — 21 self-contained declarations (defs + interface); the lemmas that consume the `weierstrassP_torsion_qExpansion_package` headline stay in the consumers, above it |
| W1e | `ModularForms/WeightOne/Fricke.lean` | `FrickeFunction` Fricke vocabulary | **done** — 14 declarations (`denomZ`, `vecMulSL`, `frickeF`, `wpNormZ`, `FrickeIdx`, …); the slash lemmas stay, as they consume the torsion-point package |
| W1f | `ModularForms/WeightOne/LevelField.lean` | `LevelFraction`/`LevelN` level-field block | **not started** — the level-field/frickeKernel block is entangled with the Fricke prelude; cut it after W2 |

`Pole` was folded into `DiscPow`: `KPoleAt`/`KPole`/`KPoleAt.pad` are part of the same
closed region as the discriminant powers, so a separate module would have split a subject.

**What the Fricke/℘ extraction taught.** A declaration can be lifted only if its *proof*
does not consume a headline from the module above it. `r2_package` calls
`ModularForm.weierstrassP_torsion_qExpansion_package`, so it and everything downstream of it
(`periodic_wpNorm`, `mdifferentiable_wpNorm`, `isBoundedAtImInfty_wpNorm`,
`qExpansion_wpNorm_coeff_mem_kN`, `wpNorm_eq_imp`, `periodic_frickeH`, …) must stay in the
consumer; only the definitions and the package-free interface move. Classify candidates by
grepping their bodies for the consumer headline before lifting them.

## 0. What this set is, and is not

It is a **refactor**: the declarations already exist, build and are verified. Every order
**lifts the canonical copy** of a block from where it lives today into a subject home.
There is no re-porting, no statement change, no new mathematics.

**Not authorized here:** editing `Basic`, `WeierstrassPTorsion`, `LevelOneHauptmodul`,
`FrickeFunction`, `LevelFraction`, `LevelN` or any Γ-module (that is SET-W2/W3);
`WeightOne/IntegralStructure.lean`; the Γ-home (`Defs/Gamma.lean`, SET-W3); the
near-duplicate generalisations (SET-W4); commits.

## 1. Source of truth

- [TOPIC-weightone-rectify.md](TOPIC-weightone-rectify.md) — the plan; §2 is the home table.
- [TOPIC-weightone-factoring-scout.md](TOPIC-weightone-factoring-scout.md) — SET-W0's
  manifest: the exact per-home declaration lists and closures. **SET-W0 was stopped without
  producing it**, so compute each home's closure yourself with the tool before creating the
  module:

  ```bash
  cd tools/deps
  python3 port_graph.py --closure FLTForHuman.ModularForms.WeightOne.Basic \
      "discPowForm,eCubeSubESq,ratCoeff_mul,KPoleAt,isBoundedAtImInfty_discPow"
  ```

  `--closure` lists the same-file declarations the named block reaches, with spans; run it
  per source file for each home, union the results, and decide include-in-home vs
  stays-private-in-consumer. `--duplicates 60` and `--blocks 8` give the cross-file view.
- [porting-playbook.md](../../porting-playbook.md) §7.1, §8, §9 — the conformance rules.
- The pin is `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem`;
  read it, never modify it.

## 2. Build discipline — read and obey first

Measured in this checkout with mathlib prebuilt: `lake env lean <module>` on a 200–350-line
green module ≈ 4 s; `lake build <module>` deps-cached ≈ 2–5 s; a full `lake build` under a
minute; a `whnf`/heartbeat stall at the default cap errors in ~15–20 s (it does not hang).

- **Bound every build, and never relax the bound.** `timeout 60 lake env lean <file>`,
  `timeout 90 lake build <module>`, `timeout 180 lake build`. A non-return at the bound is
  a blow-up, not patience.
- **On a timeout: quarantine.** Comment the declaration out and bisect, or reproduce in the
  gitignored `Scratch*.lean` with `set_option diagnostics true` and a low cap. Do not
  re-run the same file hoping for a different result.
- **Never raise `maxHeartbeats` / `maxRecDepth`** (the lakefile cap is `4000000`).
- **Tell a blow-up from contention by CPU time**: high user CPU + timeout is real (bisect);
  ~0 CPU wall-time is another agent's build (re-run when idle; never build concurrently).
- Likely stall points: the `IntermediateField.adjoin` carrier defeqs when a home is stated
  over concrete fields (playbook §3.11, second failure mode — prove the coercion lemma
  generically once), and `FunLike`-quantified lemmas at a bare function type.

## 3. The orders

Run bottom-up in this order; a later home may import an earlier one. Each order is one new
module; the *subjects* are fixed, the exact declaration lists come from the scout (extend
the lists if the closure demands it — a home is only liftable when it is closed).

| # | module | subject |
|---|---|---|
| 1 | `ModularForms/WeightOne/Defs/PeriodPair.lean` | the standard (τ,1) period pair `periodPairOfTau` + its interface, and the lattice/`smulPeriodPair` vocabulary shared by `FrickeFunction`/`LevelOneHauptmodul` |
| 2 | `ModularForms/QExpansionCoeff.lean` *(generic — may instead land under `ModularForms/Defs/`; decide in §5)* | q-expansion coefficient analysis: `qParam_one_eq_pow`, the `qExpansion_coeff_width`/`_widthN` family, `qExpansion_coeff_unique'`, the `isBigO_qParam_pow_*`/`coeff_pow_eq_zero_of_lt` block, **and the discriminant q-expansion analysis shared with the Γ modules** (`qExpansion_disc_rat`/`qExpansion_disc_rat_one`, `analyticAt_disc`, `mdifferentiable_disc`, `periodic_disc_one`, `periodic_mul`, `isBoundedAtImInfty_disc`, `ds`/`ds_ne_zero`, `disc_pow_ne_zero`, `genSet`, `RatAt`, `analyticAt`, `natCast_pos`, `periodic_ofComplex_natCast`). This is deliberate: `LevelN` is in both the level and Γ duplication clusters, and placing the shared analysis here lets SET-W2 delete `LevelN`'s copies in its one edit, instead of SET-W3 re-editing `LevelN` |
| 3 | `ModularForms/DiscPow.lean` *(generic)* | the Δᵐ package: `discPowForm`/`discPowForm_coe`, `eCubeSubESq`, `discriminant_eq_smul_eCubeSubESq`, `ratCoeff_{E,mul,sub,pow,discriminant}`, `eCubeSubESq_qExpansion`, and the modularity/boundedness/periodicity lemmas (`isBoundedAtImInfty_discPow`, `isBoundedAtImInfty_discriminant`, `mul_discPow_mono`, `mdiff_discPow`, `mdiff_mul_discPow`, `periodic_discPow_comp_ofComplex`, `periodic_one_fn`, `qExpansion_discPow_coeff_mem`, `qExpansion_one_discPowForm/{,_fn}`) |
| 4 | `ModularForms/WeightOne/Defs/Pole.lean` | the pole-order vocabulary: `KPoleAt`, `KPole`, `KPoleAt.mono`, `kPole_algebraMap`, and the `PoleBounded`/`NiceK` closure if it is shared |
| 5 | `ModularForms/WeightOne/Fricke.lean` | the Fricke function: `denomZ`/`denomZ_ne_zero`/`denom_mapGL_eq_denomZ`, `frickeF`/`frickeF_slash`/`frickeF_invariant_Gamma`/`frickeF_eq_imp`/`frickeF_faithful`/`frickeF_integral_over_j`, `vecMulSL_apply`, `mem_Gamma_or_neg_mem_of_vecMulSL`, and the ℘-normalised `W`/`frickeH`/`wpNorm` block shared with `WeierstrassPTorsion` |
| 6 | `ModularForms/WeightOne/LevelField.lean` | the level-field Galois structure: `LevelGrp`, `LevelGens`, `fixedIF`, `levelField`, `frickeKernel`/`frickeKernel_eq_pmGamma`, `aeval_j_apply`, the `finrank_*` block, the `field`-instance closure |

## 4. What is public in a home, and what is not

- **Public:** every declaration that a consumer must name after its private copy is deleted
  — i.e. the shared real mathematics, and the lifted definitions/interface lemmas. This is
  the §9 "shared real math is written once" surface.
- **Private in the home:** helpers the lifted block needs but nothing outside the home uses
  (the closure's tail). Keep them `private` so the home's public surface stays the subject.
- **Never lifted (stay in the consumer):** adapter/trivia — coercions, `_apply`, `_mono`,
  `_congr`, `_self`, one-line `rfl` restatements, and any helper that merely unfolds another
  theory's API (§9). If such a helper is *commonly* needed, it is promoted in the theory it
  adapts, not copied into this home.
- **Names.** A lifted helper was `private`, so renaming is free; give it the pin's helper
  name where the statements agree, so the statement checker's promoted-from-pin-private
  lookup still finds it. The six headline theorems are not touched by this set.

## 5. Placement judgement (§8)

The `QExpansionCoeff` and `DiscPow` subjects are **ordinary modular-forms analysis**, not
weight-one material: they use only `UpperHalfPlane.qExpansion`, `qParam`, `MDifferentiable`,
`IsBoundedAtImInfty`, `Periodic`, `ModularFormClass`. Place them under `ModularForms/`
(generic), not `WeightOne/`. The remaining four are weight-one vocabulary and go under
`WeightOne/` (`Defs/` for the vocabulary modules, top level for the two theory-shaped ones,
`Fricke` and `LevelField`). State the choice in each module header with a one-line reason.

## 6. Definition of done (per order)

- The module is created at the named path; each lifted declaration is the canonical copy
  (statement unchanged), its closure included, specific imports only (no `import Mathlib`).
- `timeout 90 lake build <module>` green, **0 warnings**, no `sorry`/`admit`.
- `#print axioms` on the module's public declarations clean
  (`[propext, Classical.choice, Quot.sound]`).
- The declaration is removed from **no** consumer in this set (that is W2), so the full
  `timeout 180 lake build` stays green and the checker count is unchanged except for the
  new module's public surface.
- Add the module to `PORT_FILES` in `spec/check_flt_statements.py`; for every new public
  declaration, ensure the checker matches it (public or promoted-from-pin-private) or add
  it to the exemption list with a reason. Run
  `python3 spec/check_flt_statements.py`; report the before/after
  `identical / promoted / mismatched / missing / own`. **`0 mismatched, 0 missing`.**
- `README.md` gains one row per module.
- Report the closure surprises: any helper that had to come along, any home that had to
  merge with another because the closure crossed the boundary.

## 7. What to report back

1. Per order: module, lines, public declarations, closure size, `lake build` time, checker
   delta.
2. Every declaration whose statement differed between its copies (binder spelling,
   `[NeZero N]` position) and which copy was chosen — these are SET-W4's generalisation
   list.
3. Every adapter/trivia candidate found and deliberately **not** lifted, with the reason.
4. Any home whose placement had to move between `WeightOne/` and `ModularForms/`, and why.
5. Any build that hit its bound: the declaration, the CPU reading, the outcome.
6. Confirmation that no existing module was edited and the capstone/FFG/T-side are untouched.
