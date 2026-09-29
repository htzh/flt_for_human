# The WeightOne rectification — plan and set schedule

**Status: planned (SET-W1 not started).** The route-C′ port (SET-5 – SET-11 plus the
capstone) transcribed FLT package-by-package, so each `S_` file's private prelude was
re-proved in the port module that consumed it. The result builds and is verified, but it
does not conform to [porting-playbook.md](../../porting-playbook.md): a module is a
mathematical role, not a source file (§7.1); shared real mathematics is written once and
promoted, while adapters stay `private` (§9); a directory holds one theory with its shared
vocabulary in `Defs/` or `Basic` (§8). This effort rectifies that. It is a **refactor**,
not a resumption of route C′: no statement changes, no new mathematics, no re-porting.

## 0. The measurements

`tools/deps/port_graph.py --blocks` (2026-09, 179 modules):

| target | removable | proofs | modules |
|---|---|---|---|
| level-family prelude | 4,276 lines | 207 | `Basic`, `FrickeFunction`, `LevelFraction`, `LevelN`, `LevelOneHauptmodul`, `WeierstrassPTorsion` |
| Γ₀/Γ₁ prelude | 2,695 lines | 116 | `Gamma0Integral`, `Gamma0Rationality`, `Gamma1Basis`, `Gamma1IntegralBasis`, `LevelN` |
| one cluster | **7,242 lines** | ~320 | 12 modules (≈8.8 % of the 82,077-line port) |

Cross-checked at the *statement* level (the checker's `raw_declarations`, private included):
**245 declarations have byte-identical statements in ≥2 files**, and 56 more share a name
but differ only in binder spelling (section variable vs explicit) or in which predicate
they belong to. The duplicated definitions are byte-identical too (spot-checked:
`discPowForm`, `periodPairOfTau`, `KPoleAt`, `denomZ`, `tauPair`, `WW`, `jf`). So the bulk
of the work is **lifting an existing copy**, not re-proving.

The duplication is also *within* files: each pin package has its own inner namespace, so
`FrickeFunction.lean` defines `periodPairOfTau`, `frickeF` and `KPoleAt` twice, and
`LevelFraction.lean` defines `discPowForm`, `eCubeSubESq` and `KPoleAt` twice.

## 1. What conformance requires here

1. **One home per subject.** `periodPairOfTau` (the standard (τ,1) pair), the Δᵐ
   package (`discPowForm`, `eCubeSubESq`, `ratCoeff_*`, their modularity/boundedness/
   q-expansion lemmas), the `KPole`/`KPoleAt` pole vocabulary, the q-expansion
   coefficient analysis (`qParam_one_eq_pow`, `qExpansion_coeff_width{,N}`,
   `qExpansion_coeff_unique'`, the `isBigO_qParam_pow_*` family), the Fricke function
   (`denomZ`, `frickeF`, `PoleBounded`), the level-field Galois structure (`LevelGrp`,
   `levelField`, `frickeKernel`), and the Γ₀/Γ₁ vocabulary (`tauPair`, `WW`, `jf`,
   `cw*`, `conj_mem_Gamma*`) each get one module.
2. **Generic subjects leave WeightOne.** The q-parameter asymptotics, the Δᵐ
   modularity/boundedness and the q-expansion coefficient-uniqueness facts are ordinary
   modular-forms analysis, not weight-one material; they are placed in `ModularForms/`
   (or `ModularForms/Defs/`) even though only the weight-one route consumes them today
   (§9: "share real math; do not re-derive it").
3. **Adapters stay private in the consumer** (§9). Coercions, `_apply`/`_mono`/`_congr`
   transports and one-line `rfl` restatements are not promoted.
4. **Near-duplicates are generalised, not copied twice.** `qExpansion_coeff_width` and
   `qExpansion_coeff_widthN`, `zetaN`/`zetaK`, `conj_mem_Gamma`/`conj_mem_Gamma1`, and the
   `[NeZero N]`-position variants become one lemma each; the generic instance-method
   names (`add`, `mul`, `pow` on `KPole`/`NiceK`/`PoleBounded`/`IsFQ`/…) get their
   predicate's namespace so they stop colliding.
5. **The public surface and the consumer are frozen.** The 1,653-declaration checker
   result must not drop (a deliberate demotion drops it by exactly the number demoted);
   `spec/WeightOneConsumer.lean` must still exit 0; no statement may be weakened.

## 2. Home design (SET-W1 confirms the exact declaration lists)

Homes sit **below** their consumers — a home may import mathlib and already-lower port
modules, never a consumer. Proposed, bottom-up:

| home | subject | may import |
|---|---|---|
| `ModularForms/QParamAsymptotics.lean` *(or fold into `QExpansionOrder.lean`)* | q-parameter asymptotics: `qParam_one_eq_pow`, `qParam_pow_isBigO_discPow`, `isBigO_qParam_pow_*` | mathlib, `QExpansionOrder` |
| `ModularForms/DiscPow.lean` | the Δᵐ package: `discPowForm`, `eCubeSubESq`, `ratCoeff_*`, boundedness/periodicity/modularity, `qExpansion_discPow_*` | mathlib, `QParamAsymptotics` |
| `ModularForms/WeightOne/Defs/PeriodPair.lean` | the standard (τ,1) period pair and its interface | mathlib |
| `ModularForms/WeightOne/Defs/Pole.lean` | `KPoleAt`, `KPole`, closure | mathlib, `QParamAsymptotics` |
| `ModularForms/WeightOne/Fricke.lean` | `denomZ`, `frickeF`, `PoleBounded`, `frickeFn`, the ℘-normalised `W` | `Defs/PeriodPair`, `DiscPow` |
| `ModularForms/WeightOne/LevelField.lean` | `LevelGrp`, `LevelGens`, `levelField`, `frickeKernel`, the finrank block | `Fricke`, `Defs/Pole` |
| `ModularForms/WeightOne/Defs/Gamma.lean` | `tauPair`, `WW`, `jf`, `cw*`, `conj_mem_Gamma*`, `gen`, `qExpansion_disc_rat*` | `DiscPow`, `Fricke`, `LevelField` |

SET-W0's scout fixes the names, the exact per-home declaration lists and each home's
**dependency closure** (the private helpers a lifted declaration needs that are not in the
list — for example the discPow block drags `qExpansion_coeff_width`,
`isBoundedAtImInfty_discriminant` and `mdiff_discPow` in some files, and the Fricke block
drags `FrickeIdx`/`frickeH`/`hppT`). A home is only liftable once its closure is included;
the closure must not reach back into a consumer's other private declarations.

### 2.1 Namespace policy — decide it before the wave (learned the hard way)

A home's public names must be reachable **under the spelling the consumers already use**, or
the W2 wave breaks even when the statements match (SET-W2.md records the reverted attempt).
Two homes (`DiscPow`, `QExpansionCoeff`) kept the source region's `UpperHalfPlaneAux`
namespace, while the `WLight` consumers spell those names (`WLight.qExpansion_coeff_width`)
or rely on `open WLight`. The mismatch produced dangling qualified references and
`Application type mismatch` errors. The policy, to be fixed as W2's first step:

- the ℘/Fricke vocabulary stays under `WLight` (as lifted) — consumers already `open WLight`;
- `DiscPow`/`QExpansionCoeff` must either re-namespace to `WLight` too, or expose a
  `WLight`-spelled **alias** for every name a consumer references (`ratCoeff_*`,
  `eCubeSubESq*`, `discriminant_eq_smul_eCubeSubESq`, `qParam_one_eq_pow`,
  `qExpansion_coeff_width_fn`, `isBoundedAtImInfty_disc*`, `mul_discPow_mono`,
  `mdiff_discPow`, `periodic_discPow_comp_ofComplex`, `KPoleAt`/`KPole`, `mem_of_rat`, …);
- a home may keep `UpperHalfPlaneAux` internally, but its **exported** name is what the
  consumers name, and the two must agree.

The `Basic` rewire worked precisely because `Basic` *is* the region's original namespace, so
`UpperHalfPlaneAux` resolved locally. Every other consumer needs the policy above.

## 3. The sets, and why in this order

The constraint is build cost. Editing `Basic.lean` (a leaf of the weight-one DAG)
recompiles the whole weight-one tree and the Γ-modules above it; editing a Γ-module
recompiles only the Γ chain. So each big module must be edited **exactly once**, and the
home creation must be a separate wave that edits no existing module.

| set | scope | big modules edited | rebuild wave |
|---|---|---|---|
| **W0** (scout) | measure, not code: the manifest, closures and home paths. **Stopped without a manifest**; its closure work is folded into W1 via `port_graph.py --closure` | none | none |
| **W1** ([brief](SET-W1.md)) | create the level-family homes (`QExpansionCoeff`, `DiscPow`, `Defs/PeriodPair`, `Defs/Pole`, `Fricke`, `LevelField`) as new modules; verify each builds and its closure is self-contained | none | none (new files only) |
| **W2** ([brief](SET-W2.md)) | **done** — rewired the level family: `Basic`, `WeierstrassPTorsion`, `LevelOneHauptmodul`, `FrickeFunction`, `LevelFraction`, `LevelN` import the homes and their private copies are deleted; the width family is deferred to W4 | all six, once each | one weight-one-wide rebuild (6:19) |
| **W3** ([brief](SET-W3.md)) | **partial** — created `Defs/Gamma.lean` (the Γ period/Fricke core) and rewired the four Γ modules onto it; the `cw*`/`conj_mem_Gamma`/`gen` and `qExpansion_disc_rat*`/`descent` sub-blocks follow W4's width generalisation | the four Γ-modules, once each | one Γ rebuild (2:15) |
| **W4** ([brief](SET-W4.md)) | **started** — the width family is homed (`qExpansion_coeff_width{,N}`, `qParam_one_eq_pow`, `qExpansion_coeff_unique'`); still to do: the `ModularFormClass` copies, adapters, checker/`PORT_FILES`/README, consumer, write-up | touched modules only | one final rebuild |

Between two sets there is a review gate: the next set starts only when the previous one is
green (full `lake build`, checker `0 mismatched / 0 missing`, consumer exit 0) and the
redundancy count has fallen. The sets are otherwise independent — a set that stalls can be
abandoned without leaving the tree broken, because W1 adds files and W2/W3 change one wave
at a time.

**Why not one set per home.** Rewiring a consumer removes *all* of its private copies at
once; splitting the homes across sets would edit `Basic` (and therefore rebuild everything)
once per home. The wave structure is what keeps the count at one.

**Why W1 is separate from W2.** W1 creates the homes unwired, so the homes are temporarily
duplicated against the still-private consumer copies. That is transient and build-green.
The playbook's `Universal.lean` warning (a module in no import chain passes until someone
uses it) is answered by W2 immediately wiring all six homes and by W1's own requirement
that each home's lifted block be the *canonical* copy, not a paraphrase.

## 4. Conventions that bind every set

1. Public statements keep their names and binder spelling (the checker diffs text, §7.4);
   only proofs and `private` helpers move.
2. Specific imports; no `import Mathlib` in a library module.
3. A new home is added to `PORT_FILES` in `spec/check_flt_statements.py` **only** for the
   public declarations it carries; a demoted helper drops out of the compared count by
   exactly the number demoted — check that the total moves as expected, never silently.
4. `README.md` rows are updated for new/renamed modules; the set/log files are the
   manager's.
5. No commits; the working tree is the hand-off. The pin is read-only.
6. Do not touch `WeightOne/IntegralStructure.lean` (the capstone), the FFG modules, or the
   T-side modules.
7. Build discipline — copied from playbook §3.11 and binding:

> **Build discipline — read this first.** Every build is bounded and a blow-up is
> quarantined, not waited on. Measured with mathlib prebuilt: a green
> `lake env lean <module>` of this size is **~4 s**, `lake build <module>` with
> deps cached **~2–5 s**, and a `whnf`/heartbeat timeout at the default cap
> **errors in ~15–20 s** — it does not hang. A healthy full `lake build` of this
> tree is **seconds to about a minute**.
>
> - Run every build under a hard bound: `timeout 60 lake env lean <file>`,
>   `timeout 90 lake build <module>`, `timeout 180 lake build`. **A multi-minute
>   build is never acceptable, not even while experimenting.**
> - **Expect ≤ 30 s.** Any single build past ~60 s must be treated as a blow-up
>   and bisected, not watched.
> - **Quarantine immediately.** On a non-return, comment the declaration out and
>   bisect, or reproduce in the gitignored `Scratch*.lean` with
>   `set_option diagnostics true` and a low cap. Do not re-run the same file
>   hoping for a different result.
> - **Never raise `maxHeartbeats` (or `maxRecDepth`).** The cap already fails in
>   under 20 s; raising it turns that into an unbounded wait.
> - **Tell a blow-up from contention by CPU time.** High user CPU + timeout is a
>   real blow-up (bisect); ~0 CPU wall-time is lock contention (re-run when idle;
>   never build concurrently with another agent).

## 5. Definition of done (whole effort)

- One home per subject; no declaration with an identical statement appears in two
  library modules (`port_graph.py --blocks` reports only the Γ block, then nothing over
  threshold).
- Generic subjects live outside `WeightOne/`.
- `timeout 180 lake build` green, 0 warnings, no `sorry`/`admit`.
- `python3 spec/check_flt_statements.py`: 0 mismatched, 0 missing (the identical count may
  fall only by deliberate demotions, which are listed).
- `lake env lean spec/WeightOneConsumer.lean` exit 0.
- `#print axioms` on the six Γ₁/Γ₀ headlines and the capstone unchanged
  (`[propext, Classical.choice, Quot.sound]`).
- The `port_graph.py --blocks` removable-line figure for the weight-one cluster drops from
  **7,242** to under the display threshold.
- A short record in `logs/` (owner: the manager) stating the before/after counts.
