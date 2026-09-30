# Deligne–Serre port — friction log

Records the deviations made during the forward port (the phase order is
[../topics/deligneSerre/TOPIC-port-order.md](../topics/deligneSerre/TOPIC-port-order.md)
§2): things resolved *locally* because promoting them would have re-opened a
**closed** file. The periodic **refactor round** reads this file, promotes the
entries into their homes, and updates the importers.

Entry format:

```text
## <date>  <file being written>
- wanted: <declaration / block>
  home it belongs in: <module>
  currently: <closed file it lives in / not ported / pin-only>
  local workaround: <private copy name / local restatement, + lines>
  why not resolved here: <closed importee / needs an existing file touched>
```

One entry per missed share. Keep it honest: the point is that the promotion
happens in a dedicated round, not mid-port.

---

## 2026-09-29  FLTForHuman/ModularForms/Defs/Gamma1HeckeOperators.lean

The seven declarations below are the phase-D share of the **22 different-statement
clashes** that phase H2 owns (`TOPIC-definitions-and-homes.md` §3; the port-private
`_11` refinements and `sum_range_eq_sum_zmod` are on H2's promotion list). They are
*not* copied here: no existing file is edited and no name is shadowed.

- wanted: `CuspForm.Gamma1Hecke.mdifferentiable_heckeU`
  home it belongs in: `FLTForHuman/ModularForms/HeckeAnalytic.lean`
  currently: `ModularForm.mdifferentiable_heckeU` exists with the same mathematics
    but the `UpperHalfPlane`/`modelWithCornersSelf` spelling rather than `ℍ`/`𝓘(ℂ)`.
  local workaround: the `heckeTOne` proof calls the port's
    `ModularForm.mdifferentiable_heckeU`; no copy written.
  why not resolved here: H2 reconciliation; editing `HeckeAnalytic.lean` is out of scope.

- wanted: `CuspForm.Gamma1Hecke.isZeroAt_heckeU`
  home it belongs in: `FLTForHuman/ModularForms/HeckeCusps.lean`
  currently: `CuspFormClass.isZeroAt_heckeU` exists with the pin's conclusion but no
    `hp : p ≠ 0` hypothesis (the port's statement is more general).
  local workaround: the `heckeTOne` proof calls the port's version directly.
  why not resolved here: H2 reconciliation (hypothesis clash).

- wanted: `CuspForm.Gamma1Hecke.heckeMatrix_mul_of_eq`, `…_of_eq'`,
    `…_DiagMatrix_mul_of_eq`, `…_DiagMatrix_mul_of_eq'`
  home it belongs in: `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`
  currently: the port's public copies carry the Γ₀ `S_`-file **two-conjunct**
    statements; the pin's public block additionally records `g' 1 1 = …`. The
    three-conjunct statements already exist there as the port-private `_11`
    refinements.
  local workaround: proofs in the new module use the port's public two-conjunct
    lemmas where possible; the port-private `_11` refinements are reached only
    through `ModularForm.HeckeRepresentatives.Gamma1Hecke.heckeRep_mul`.
  why not resolved here: H2's promotion (the `_11` refinements) and reconciliation
    (public statement) both require editing `HeckeRepresentatives.lean`.

- wanted: `CuspForm.Gamma1Hecke.sum_range_eq_sum_zmod`
  home it belongs in: `FLTForHuman/ModularForms/Defs/HeckeRepresentatives.lean`
  currently: present with the same statement up to binder names (`{M}`/`F` vs
    `{A}`/`G`); the checker is textual, so the copy does not count as identical.
  local workaround: the new module reuses the port's copy (reached from
    `sum_slash_mapGL_of_mem_Gamma0` via `heckeU_eq_sum_zmod`); no second copy.
  why not resolved here: binder-only clash; H2 renames the existing binder to the
    pin wrapper's.

---

## Progress

### D0 — 2026-09-29

- modules: new `GaloisRep/Defs/MatrixRepresentation.lean`,
  `ModularForms/Eisenstein/WeierstrassZeta.lean`,
  `FieldTheory/RatAlgClosureGalois.lean`, `ModularCurve/Defs/Gamma0Away.lean`,
  `ModularCurve/Defs/IharaIota.lean`, `Algebra/BrauerNesbitt.lean`,
  `NumberTheory/FrobeniusDensity/TaylorWilesPrimes.lean` (seven, 938 pin
  lines / **1,006 written lines**); verified-only `Def_ModularForm_HeckeOperator`,
  `Def_FLTPrelim_Ramification`, `Def_FLTPrelim_Modularity` (reverse check:
  0 pin declarations absent).
- build: one `lake build` of the seven new targets, green,
  **wall 11.8 s / user 36.1 s**.
- checker: `2058 → 2144` identical, 0 mismatched, 0 missing.
- deliberately reused: every declaration of the three verified-only modules (no
  new declaration); `Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients` split
  into `.Basic` + `.Norm` to drop a deprecation warning
  (`TaylorWilesPrimes.lean`).
- friction entries added: none (no local resolution was needed).

### D1 — 2026-09-29

- modules: new `ModularForms/Defs/Gamma1HeckeOperators.lean` (the 20 absent
  declarations of the pin's 680-line block; the 7 clashes are H2's, logged
  above), `ModularForms/Defs/PrimitiveFormGamma1.lean`,
  `NumberTheory/FrobeniusDensity/DegOneAsymptotic.lean`,
  `ModularCurve/Defs/IharaAmalgam.lean` (the three new files are 214 pin lines;
  the four D1 modules are **490 written lines**); verified-only
  `Def_EllipticCurve_FrobeniusTrace` (reverse check: 0 absent).
- build: one `lake build` of the four new targets, green,
  **wall 9.0 s / user 20.0 s**.
- checker: `2144 → 2197` identical, 0 mismatched, 0 missing.
- deliberately reused: the Γ₁/diamond half (`Level/Diamond.lean`,
  `Defs/HeckeRepresentatives.lean`); the port's `ModularForm.mdifferentiable_heckeU`
  and `CuspFormClass.isZeroAt_heckeU` in the `heckeTOne` proof; the port's
  `sum_range_eq_sum_zmod`; `ModularForm.Level.isUnit_d`.
- friction entries added: the five above (the 7 H2 clashes).

### D2 — 2026-09-29

- modules: new `NumberTheory/FrobeniusDensity/BadPrimes.lean`,
  `GaloisRep/Defs/FrobeniusPowerDense.lean`,
  `ModularCurve/Defs/IharaAmalgamMap.lean` (292 pin lines); verified-only
  `Def_GaloisRep_Residual` (reverse check: 0 absent).
- build: per-module, `flock /tmp/flt_for_human.lock timeout 120 lake build
  FLTForHuman.<Dotted.Path>` — green: `…BadPrimes` **wall 5.3 s / user 4.1 s**,
  `…FrobeniusPowerDense` **wall 3.8 s / user 2.4 s**, `…IharaAmalgamMap`
  **wall 2.4 s / user 3.7 s**.
- checker: `2197 → 2234` identical, 0 mismatched, 0 missing.
- deliberately reused: all D2 modules are verbatim transcriptions; no port copy
  was needed. `BadPrimes`'s `finite_setOf_dvd` proof was adapted for mathlib
  `v4.34.0`: `(normalizedFactors I).toFinset` is now `@[simp]`-rewritten to
  `UniqueFactorizationMonoid.primeFactors I`, so the pin's
  `simpa [Multiset.mem_toFinset]` is replaced by `mem_primeFactors.mpr`
  (statement unchanged).
- friction entries added: none.

### D3 — 2026-09-29

- module: new `NumberTheory/FrobeniusDensity/PrimeSums.lean` (95 pin lines).
- build: per-module `flock /tmp/flt_for_human.lock timeout 120 lake build
  FLTForHuman.NumberTheory.FrobeniusDensity.PrimeSums`, green,
  **wall 5.3 s / user 3.7 s**.
- checker: `2234 → 2252` identical, 0 mismatched, 0 missing.
- deliberately reused: nothing new (verbatim transcription).
- friction entries added: none.

### Phase D close (2026-09-29)

- checker: `2058 → 2252` identical (+194 new public declarations),
  0 mismatched, 0 missing, 30 own-proof declarations exempted.
- all 20 pin `Def_*` modules covered: 15 new modules/extends plus 5 verified-only
  (`Def_ModularForm_HeckeOperator`, `Def_FLTPrelim_Ramification`,
  `Def_FLTPrelim_Modularity`, `Def_EllipticCurve_FrobeniusTrace`,
  `Def_GaloisRep_Residual`), each reverse-checked to 0 absent pin declarations.
- the only unported declarations are the **7 H2 clashes** in
  `Def_CuspForm_Gamma1HeckeOperators` logged above.
- no `sorry`/`admit`/`axiom`/`native_decide` in any new module; no new module
  overrides `maxHeartbeats`/`maxRecDepth`; no `import Mathlib`; `#print axioms`
  on the headlines returns `[propext, Classical.choice, Quot.sound]`.
- build discipline note: D0/D1 were built with a single multi-target `lake build`;
  after the manager's checkpoint of 2026-09-29, D2/D3 used one `lake build` per
  module inside `flock`, each well under the 120 s bound. No bare whole-tree
  `lake build` was run in phase D.

---

## Phase H1 — the four shared prelude homes (2026-09-29)

Four new files, each a union of the pin copies of its `write once (H1)` blocks,
wired into `SOURCES`/`PORT_FILES` (appended last). Checker `2252 → 2295`
identical, **0 mismatched / 0 missing** (+43 public declarations); GR 2252→2253,
EIS 2253→2268, FD 2268→2287, HK 2287→2295.

- `FLTForHuman/GaloisRep/Prelude.lean` (namespace `GaloisRep`, 1 block
  `finite_range_of_factorsThroughFiniteLevel`); `lake build` green, wall 7.2 s /
  user 4.5 s.
- `FLTForHuman/ModularForms/Eisenstein/Cotangent.lean` (namespace
  `EisensteinSeries`, 15 public declarations: the 13 placeable listed blocks plus
  the repeated defs `om`, `ser`); `lake build` green, wall 3.4 s / user 2.8 s.
- `FLTForHuman/NumberTheory/FrobeniusDensity/Basic.lean` (namespace
  `FrobeniusDensity`, 19 public declarations); `lake build` green, wall 3.8 s /
  user 2.6 s.
- `FLTForHuman/ModularForms/HeckePrelude.lean` (namespaces `ModularForm` / `CuspForm`,
  8 public declarations); `lake build` green, wall 2.6 s / user 1.9 s.

**Repeated definitions homed (not in the tool's proof-dedup tables).** Per the
manager addendum, each home's pin copies were scanned for repeated
`def`/`abbrev`/`structure` and the union homed at the pin name: `om` (all four
EIS files) and `ser` (two EIS files), both public and statement-identical; the
FD/HK pin copies had no repeated definition beyond the listed `NormFiber` /
`normFiberEquiv`. Definitions occurring in one pin file only were left out.

**Blocks omitted (cannot be placed before phase T; no `sorry` used).** Three of
the 44 listed blocks depend on phase-T headlines that phase D did not port:

- EIS `hasSum_ser` — its pin proof is
  `EisensteinSeries.hasSum_weierstrassZeta_sub_mul_G2` (`S_EisensteinSeries_hasSum_weierstrassZeta_sub_mul_G2`),
  port-absent.
- FD `sum_moebius_mem_zpowers` — needs
  `ArithmeticFunction.sum_moebius_filter_dvd`
  (`S_ArithmeticFunction_sum_moebius_filter_dvd`), port-absent.
- FD `degOneSum_ne_top` — needs `FrobeniusDensity.idealSum_ne_top`
  (`S_FrobeniusDensity_idealSum_ne_top`), port-absent.

These are the only H1 blocks whose pin proof reaches a not-yet-ported `Thm_`
wrapper; they must be re-homed once the S1/S2/S6 theorem sets land.

**Friction for H2 (work-order table corrections).** Three declarations in the H2
promotion table do not match the post-D tree: `T_zpow_mem_Gamma1` lives
`private` in `FLTForHuman/ModularForms/WeightOne/Gamma1Basis.lean:1179` (the table
says `Gamma0Integral.lean`), and `adjoinRoot'` / `locKer` do not occur anywhere
in `FLTForHuman/` (or `Reserve/`), so they cannot be promoted at an existing
location — they are unported phase-T content.

---

## Phase H2 — promotions and clash reconciliation (2026-09-29)

Checker `2295 → 2301` identical, **0 mismatched / 0 missing**, 30 own-proof
exempted. `SOURCES` gained one pin file (the Γ₁ `HeckeGamma1` block); no
`PORT_FILES` entry and no `OWN_PROOFS` addition (every new public declaration
verifies against a pin copy under its own last name).

**Promotions (2a).**

- `T_zpow_mem_Gamma1` — promoted at its existing location
  `WeightOne/Gamma1Basis.lean:1179` (dropped `private`). The general ℤ-indexed
  lemma that `WeightOne/Defs/GammaRational.lean` had under the pin name
  `T_pow_mem_Gamma1` was renamed `T_zpow_mem_Gamma1_aux` (kept `private`, its one
  consumer `exists_twist_conj` updated).
- the four phase-D `_11` refinements — `heckeMatrix_mul_of_eq`, `…_of_eq'`,
  `heckeDiagMatrix_mul_of_eq`, `…_of_eq'` — are now the public pin
  (three-conjunct) statements; the weaker two-conjunct Γ₀ copies they replaced
  are `private …_two` (`HeckeRepresentatives.lean:76,93,110,127`). Consumers
  updated: `heckeMatrix_mul_of_dvd:277` uses `…_two`; the four `_11` calls inside
  `Gamma1Hecke.heckeRep_mul` use the promoted names.
- `adjoinRoot'` / `locKer` — **not promoted**: absent from the whole tree (grep),
  unported phase-T content.

**Reconciliations (2b).**

- `T_pow_mem_Gamma1` — the pin's ℕ-indexed statement `(N n : ℕ) : T ^ n ∈ Γ₁ N`
  is now the public declaration in `GammaRational.lean:258`; the general ℤ form
  is the promotion target above.
- `T_mem_Gamma1` — renaming-only: the `private` shadow copies in
  `Gamma0Integral.lean` take `(N : ℕ)` (the public copy in `GammaRational.lean`
  was already the pin statement); the unused private ℤ `T_pow_mem_Gamma1` shadow
  there was deleted.
- `heckeRep_mul` — the pin's Γ₁ copy (no extra `g 1 1` factor) is added under
  `HeckeRepresentatives.HeckeGamma1`; the Γ₀ + `wt` copy stays for
  `sum_slash_mapGL_of_mem_Gamma0` / `PhiGenDescends`. Both last names verify.
- `isUnit_wt` — `hp : p.Prime` dropped (pin's `Fact p.Prime` proof); the one call
  site in `Defs/Gamma1HeckeOperators.lean:136` updated.
- `det_mod` — restated `{N : ℕ} (γ) (hγ : γ ∈ Gamma0 N)` (naming-only).
- `mdifferentiable_heckeU` — the pin's section-variable (`Def_`/`S_`) copy is
  added as `ModularForm.HeckeGamma1.mdifferentiable_heckeU` beside the
  `Theorems/`-wrapper copy; both verify, no consumer touched.
- `periodic_smul` — the pin's unit-period copy is added as
  `X1DiamondRational.PeriodOne.periodic_smul`, derived from the general lemma.
- `qCoeffLin` — promoted (`Gamma1IntegralBasis.lean:682`); the pin's `S_` copy
  already spells `CuspForm (Γ₁ℝ N)`.
- `sum_range_eq_sum_zmod` — binder-only: restated `{A} … (G : ℕ → A)`.
- `mapGL_apply` — naming-only: restated with
  `Matrix.SpecialLinearGroup.mapGL`.
- `isZeroAt_heckeU` (friction row) — the pin's `hp : p ≠ 0` copy is added under
  `CuspForm.Gamma1Hecke` in `HeckeCusps.lean`; the port's more general
  `CuspFormClass.isZeroAt_heckeU` stays.
- `coe_smul_eq` (friction row) — restated at the pin's statement (`denom`,
  `γ 0 0`, `τ` a section variable) in
  `Reserve/ModularCurve/Analytic/LevelTauBridge.lean`; a private
  `denomC_eq_denom` bridge keeps the three downstream analytic consumers
  compiling. `Reserve/` is not diffed and unimported, so no home is shadowed.
- unrelated collisions `coef`, `rep` — the port's copies are already `private`
  and are different objects; the pin's single-file `S_` declarations are
  unported phase-T content, so no public name is shadowed.

**New `SOURCES` entry.** `P2M/Sol/S_ModularForm_heckeU_add_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1.lean`
appended last: it is the pin copy of the Γ₁ `heckeRep_mul` and of the no-`hp`
`isUnit_wt`.




## 2026-09-30  S1 — FLTForHuman/ModularForms/Eisenstein/{WeierstrassZetaSum,WeierstrassZetaQuasiPeriod,EisensteinG1Transform,EisensteinG1QExpansion,WeightOneMultiplier}.lean

The five-node weight-one Eisenstein set, one module per pin `S_` file in the
pin's import order. No closed file was edited and no public name was shadowed.
The entries below are the locally-resolved shares and the adaptation notes.

- wanted: the `P2M.Util` prelude the pin's `S_` files open with (`r`, `r_pos`,
    `r_mul_max_le`, `linear_inv_isBigO_right`, `linear_right_summable`,
    `summable_inv_of_isBigO_rpow_inv`, `summable_of_isBigO_rpow_norm`,
    `Complex.integerComplement`, `Complex.mem_integerComplement_iff`,
    `cotTerm`, `summable_cotTerm`, `cot_series_rep'`,
    `summable_int_iff_summable_nat_and_neg`, `tsum_of_nat_of_neg_add_one`,
    `sigmaAntidiagonalEquivProd`, `summable_prod_mul_pow`, …)
  home it belongs in: not a port module — these are mathlib's, from
    `Mathlib.NumberTheory.ModularForms.EisensteinSeries.Summable`,
    `Mathlib.Analysis.Complex.IntegerCompl`,
    `Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`,
    `Mathlib.Topology.Algebra.InfiniteSum.NatInt`,
    `Mathlib.NumberTheory.TsumDivisorsAntidiagonal`.
  currently: mathlib `v4.34.0` (the pin's mathlib `db584cd6` agrees).
  local workaround: imported directly; no `P2M.Util` analogue is written
    (playbook §1). Recorded negatives: no missing ingredient among them.
  why not resolved here: nothing to resolve — this is the route's mathlib map.

- wanted: `intComp_add_ne_zero` (pin `WZA`, `w + n ≠ 0` for `w ∈ ℂ_ℤ`)
  home it belongs in: mathlib, as `Complex.integerComplement_add_ne_zero`
  currently: mathlib `v4.34.0`; `WeierstrassZetaSum.lean` calls it directly.
  local workaround: dropped the pin-local lemma; `hasSum_inv_linear_sub` and
    `tsum_azero` call `Complex.integerComplement_add_ne_zero`. One pin-only
    declaration not ported (statement text is the same mathematics).
  why not resolved here: nothing to resolve.

- wanted: `hasSum_ser` (`HasSum (ser τ z) (pval τ z)` from `NotLat τ z`)
  home it belongs in: `FLTForHuman/ModularForms/Eisenstein/Cotangent.lean` (H1)
  currently: H1 deliberately omitted it because its pin proof calls
    `hasSum_weierstrassZeta_sub_mul_G2` (module 1).
  local workaround: ported once in `WeierstrassZetaQuasiPeriod.lean` (module 2),
    as the work order directs; `EisensteinG1QExpansion.lean` (module 4) imports
    it. Both WZB and WZD pin copies are identical, so one home verifies.
  why not resolved here: H1 is closed (work order `TOPIC-port-order.md` §2).

- wanted: `denom_eq` (the pin repeats it in `WZC` and `W1` with different binder
    spellings: `(γ)` + section `τ`, versus `(γ) (τ)`)
  home it belongs in: `FLTForHuman/ModularForms/Eisenstein/EisensteinG1Transform.lean`
  currently: that module writes the `WZC` copy publicly.
  local workaround: `WeightOneMultiplier.lean` does not repeat it; `main`'s
    `rw [denom_eq]` reaches the module-3 copy (`EisensteinG1Transform.lean`),
    whose statement is exactly the identity `main` needs. `W1`'s pin copy is
    therefore not a port declaration (no shadowing, no duplicate name).
  why not resolved here: module-as-role dedup (playbook §2.4); editing nothing.

- wanted: `notLat_of_not_dvd` (the pin repeats it in `WZC`, with
    `(N : ℕ) [NeZero N]` explicit, and in `WZD`, with both as section variables)
  home it belongs in: `FLTForHuman/ModularForms/Eisenstein/EisensteinG1Transform.lean`
  currently: that module writes the `WZC` copy publicly.
  local workaround: `EisensteinG1QExpansion.lean` imports it and calls
    `notLat_of_not_dvd τ N hv`; the `WZD` pin copy is not a port declaration.
  why not resolved here: dedup (playbook §2.4).

- wanted: the pin's two `SL(2, ℤ)`/quasi-period files flip `τ` to implicit
    (`variable {τ}`) and then apply lemmas explicitly positionally
    (`notLat_of_not_dvd N τ hv`, `weierstrassZeta_add_int τ …`)
  home it belongs in: `FLTForHuman/ModularForms/Eisenstein/EisensteinG1Transform.lean`
  currently: under mathlib `v4.34.0` Lean no longer elaborates an explicit
    positional argument against an implicit binder here, so the pin's `τ`
    application fails.
  local workaround: keep `τ` **explicit** (`variable (τ)`) through the module
    and call `weierstrassZeta_add_int τ …` / `notLat_of_not_dvd τ N hv` instead.
    The auto-bound binder is not part of the source text, so the statement
    checker is unaffected.
  why not resolved here: proof-level only; no statement change.

- wanted: `ModularFormClass.qCoeff` (in the W1 target statement)
  home it belongs in: `FLTForHuman/ModularForms/HeckeQCoeff.lean:70`
  currently: ported there, transcribed from
    `Definitions/Def_FLTPrelim_Modularity.lean:19`.
  local workaround: `WeightOneMultiplier.lean` imports `HeckeQCoeff`; no copy.
  why not resolved here: already homed; imported not re-proved.

- wanted: the pin's `WZE` helper namespace (58 declarations)
  home it belongs in: `EisensteinSeries` in `WeightOneMultiplier.lean`
  currently: the pin keeps them public in `WZE`; the port writes them public in
    `EisensteinSeries` (except `denom_eq`, above), so the checker verifies each
    against its `W1` pin copy.
  local workaround: none; `ModularForm.exists_weightOne_…` sits in
    `namespace ModularForm` exactly as the wrapper.
  why not resolved here: nothing to resolve.

**Checker wiring.** Each pin `S_` file is appended to `SOURCES` together with its
`Theorems/Thm_*` wrapper: the wrapper carries the public target's *name* (the
`S_` file calls it `solution`), so it is the comparable copy, while the `S_`
file supplies the intermediate declarations. Appended last, so no earlier
last-name match can flip. `PORT_FILES` gets the five modules in import order.

**Style warnings left in place (proof-level, not statements).** The pin's
`if_neg`/`if_pos`/`if_true` are deprecated in `v4.34.0` (`ite_eq_right`,
`ite_eq_left`, `ite_true`); a few `simp only` arguments and one
`haveI`-style linter fire. They build clean (no `error`), the project does not
set `warningAsError`, and changing them is not a statement change, so they are
transcribed as the pin wrote them.




## 2026-09-30  S2 — Hecke / Γ₁ vanishing and nebentypus (nine nodes)

Five modules, 1,893 lines: `ModularForms/HeckeTLinOneQCoeff.lean` (150),
`ModularForms/HeckeNebentypus.lean` (52), `ModularForms/Gamma1Vanishing.lean`
(683), `ModularForms/HeckeEigenNebentypus.lean` (382),
`ModularCurve/IharaSurjective.lean` (626). Checker 2444 → **2453** identical
(+9, one per public target), 0 mismatched / 0 missing. All nine `#print axioms`
give `[propext, Classical.choice, Quot.sound]`. Helpers are `private`
throughout, so the delta is exactly the nine targets. No closed file needed a
statement change; one shared home gained two aliases (below).

**Pin-statement qualification (shared alias, one home edit).** The wrappers of
`qCoeff_heckeTLinOne`, `heckeTLinOne_slashOfMemGamma0` and
`diamondLinOne_apply_eq_smul` spell the diamond operators `CuspForm.slashOfMemGamma0`
/ `CuspForm.diamondLinOne`, but this port homes them in `ModularForm.Level` (the
pin's `Def_CuspForm_Gamma1HeckeOperators.lean` declares them under
`namespace CuspForm`). The statement checker only strips `ModularCurve.` /
`AlgebraicCurve.` qualifications, so `ModularForm.Level.diamondLinOne` in a
target statement is a hard mismatch. Fixed by `export ModularForm.Level
(slashOfMemGamma0 diamondLinOne)` inside `namespace CuspForm` at the end of
`ModularForms/Level/Diamond.lean`; `export` introduces no checker-visible
declaration, and `Gamma1HeckeOperators.lean` still elaborates (the opened and
exported names are the same constant). Do not remove those two lines.

**Deduplication.** The oddness file (`S_CuspForm_slash_eq_dirichlet_smul_...`)
copies the `S_CuspForm_qCoeff_heckeTLinOne` helper block (pin lines 92–190:
`T_pow_mem_Gamma1`, `mapGL_apply`, `heckeDiagMatrix_mul_T`,
`periodic_of_slash_T`, `slash_heckeDiagMatrix_slash_T`, the two
`isBoundedAtImInfty_*`, `isBoundedAtImInfty_heckeU`, `mdifferentiable_heckeU`,
`periodic_smul`). That union is already homed in `HeckePrelude.lean`,
`HeckeAnalytic.lean` and `Defs/HeckeRepresentatives.lean`; the module imports
them and keeps only `periodic_add_smul`/`periodic_smul`/`T_mem_Gamma1`/
`T_pow_mem_Gamma1`/`dd*` private. `Gamma1Vanishing`'s target 1 is a thin
`exact` over the existing `CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash`
(the H2 promotion target), not a re-proof.

**Locally-resolved shares and mathlib drift (proof-level; no statement change).**

- `v4.34.0` retypes the anonymous subtype constructor `⟨A, h⟩ : SL(2, ℤ)` to
  the unfolded `{A // A.det = 1}`, so `rw [Gamma0_mem]` on a literal element
  misses its `Membership` instance. Both `IharaSurjective` and
  `HeckeEigenNebentypus` add a private typed constructor
  `def sl2 (A) (h : A.det = 1) : SL(2, ℤ) := ⟨A, h⟩` and route literal
  `Gamma0` elements through it. The same retyping is why `simp` does not unfold
  `sl2` in `exists_lift` (used `simp [sl2]`, `simp [dd, sl2]`).
- `obtain` cannot eliminate the `Prop` `IsCoprime` into a `Type`-valued
  `Gamma0`-witness; the pin's `(isCoprime_reducer_row …).choose_spec.choose`
  form is kept.
- `T_mem_Gamma1` proved by `simp [Gamma1_mem, ModularGroup.T]` no longer closes
  at `v4.34.0`; use the `HeckePrelude` route through `ModularGroup.T ^ (n : ℤ)`
  and `coe_T_zpow`.
- `DirichletCharacter` is not pulled in transitively by the Hecke homes;
  `HeckeEigenNebentypus` imports `Mathlib.NumberTheory.DirichletCharacter.Basic`.
- `ModularForm.norm` / `norm_ne_zero` / `coe_norm` live in
  `Mathlib.NumberTheory.ModularForms.NormTrace` and `Nat.prime_iff_prime_int` in
  `Mathlib.Data.Nat.Prime.Int`; `Gamma1Vanishing` imports both explicitly.
- The port's `diamondLinOne_apply_apply` / `exists_isDiamondLift_of_coprime` /
  `coe_slashOfMemGamma0` are `ModularForm.Level.*`; `Ihara.upperTriangularGL`
  is `ModularForm.upperTriangularGL`; no `IsBoundedAtImInfty.smul` exists
  (`BoundedAtFilter.smul _ h`); `MDifferentiable.const_smul` takes the scalar
  before the proof; `CuspForm.IsGLPos.smul_apply` is deprecated (`smul_apply`).
  `mapGL_mul_heckeDiagMatrix` needs an explicit
  `rw [Matrix.SpecialLinearGroup.map_apply_coe (algebraMap ℤ ℝ)]` on the
  subtype literal after `mapGL_coe_matrix`.
- `UpperHalfPlane.IsBoundedAtImInfty` for `Γ₁` is not an instance: the port's
  `CuspForm.cusp_bdd` (from `HeckePrelude`) supplies it instead of the pin's
  `ModularFormClass.bdd_at_infty`.

**Checker wiring.** The nine pin `S_` files are appended last, each preceded by
its `Theorems/Thm_*` wrapper (the wrapper carries the public target's name; the
`S_` file calls it `solution`) and in the port's module order:
`ModularForm_heckeU_add_slash_…`, `CuspForm_qCoeff_heckeTLinOne`,
`CuspForm_heckeTLinOne_slashOfMemGamma0`,
`CuspForm_HasNebentypus_diamondLinOne_apply_eq_smul`,
`CuspForm_vadd_inv_pow_eq_of_slash_heckeDiagMatrix_invariant`,
`CuspForm_eq_zero_of_forall_vadd_inv_pow_eq`,
`CuspForm_eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`,
`CuspForm_slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`,
`Ihara_amalgamToGamma0Away_surjective`. Three of those `S_` files
(`qCoeff_heckeTLinOne`, `slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`,
`ModularForm_heckeU_add_slash_…`) were already registered by the H1/H2 blocks
and are repeated inside their pairs so the set is self-contained; extra
candidates cannot flip an earlier match. `PORT_FILES` gets the five modules.

**Style warnings left in place (proof-level, not statements).** As in S1:
deprecated `Set.mem_setOf_eq` / `if_pos` / `tendsto_finset_prod`, unused
section variables and `haveI`-style linter warnings; no `error`.




## 2026-09-30  S3 — `DeligneSerre/{Relevement,Lifting}.lean` (relevement + weight-one lifting)

Two new modules in the new top-level `DeligneSerre/` directory: 833 + 1,292 =
**2,125 written lines** for the pin's 676 + 1,242 = 1,918 raw lines. Checker
`2453 → 2457` identical (**+4**), 0 mismatched / 0 missing: the two public
targets plus the two public coefficient-ring definitions `locKer` /
`adjoinRoot'`; every other pin declaration is a `private` helper. All four
`#print axioms` give `[propext, Classical.choice, Quot.sound]`. No
`sorry`/`admit`/`axiom`/`native_decide`; no bare `import Mathlib`. The pin's
`P2M.Util`/`p2m_*` scaffolding is not ported. The pin's per-file private
preludes are imported from the H1/H2/S2 homes rather than re-ported.

- build: `DeligneSerre/Relevement` green, wall 14.2 s / user 17.4 s (3,812
  jobs); `DeligneSerre/Lifting` green, wall 9.8 s / user 15.2 s in the edit loop
  (module build green under the 120 s bound). Edit loop uses
  `-DmaxHeartbeats=4000000 -DautoImplicit=false`; no `maxHeartbeats`/`maxRecDepth`
  override in either file.

- wanted: `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul`
  home it belongs in: `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean`
    (S4, node 5)
  currently: **not ported** (absent tree-wide; `Algebra/FaithfulLatticeEigenvector.lean`
    carries the *other* S4 eigenvector engine,
    `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom`).
  local workaround: transcribed `private` in `DeligneSerre/Relevement.lean` as
    `exists_eigenvector_minimalPrimes_aux` (113 lines), at the pin statement of
    `S_DeligneSerre_exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul.lean`;
    the relèvement proof calls it exactly where the pin calls the public name.
  why not resolved here: S4 is a later set and
    `Algebra/FaithfulLatticeEigenvector.lean` is outside the S3 edit scope. The
    refactor round should promote it (and drop the private copy) when S4 lands.

- wanted: `locKer` (the `φ`-localized coefficient ring
    `{z | ∃ s ∈ R, φ s ≠ 0 ∧ s z ∈ R}`)
  home it belongs in: the coefficient-ring home (`DeligneSerre/CoefficientRing.lean`
    in S4's plan, or a shared `DeligneSerre/Defs.lean` for S3/S4)
  currently: absent tree-wide (H2 verified it is unported phase-T content, not a
    promotion).
  local workaround: ported **public** at the pin statement in
    `DeligneSerre/Lifting.lean` (`def locKer : Subalgebra ℤ ℂ`), together with the
    `private` API (`mem_locKer_iff`, `mem_locKer_of_mem`, `le_locKer`, `locKerExt`,
    `locKerHom`, `locKerHom_of_mem`, `locKerHom_eq_of_mul_mem`). It is public
    because the work order asks for the pin's statement and the checker verifies
    it against the pin's `S_` copy; no other module consumes it yet.
  why not resolved here: no existing home; new file outside the two S3 modules is
    out of scope.

- wanted: `adjoinRoot'` (`Algebra.adjoin ℤ (insert ζ R)`)
  home it belongs in: same coefficient-ring home as `locKer`
  currently: absent tree-wide (H2).
  local workaround: ported **public** at the pin statement in
    `DeligneSerre/Lifting.lean` (`def adjoinRoot' : Subalgebra ℤ ℂ`), with the
    `private` API `le_adjoinRoot'`, `self_mem_adjoinRoot'`,
    `exists_ringHom_adjoinRoot'_extends`; used only by the `ℓ ≠ 2` branch of the
    lifting. The pin's `exists_ringHom_extends_of_pow_eq_one`,
    `isPrimitiveRoot_map_of_isPrimitiveRoot` and the whole Teichmüller block are
    `private` here.
  why not resolved here: as `locKer`.

- wanted: the pin's `attribute [-simp] CuspForm.Gamma1Hecke.*` /
    `CuspForm.coe_slashOfMemGamma0` guards (pin `S_` line 9)
  home it belongs in: proof-level only; no statement is affected.
  currently: the port homes those lemmas as `ModularForm.HeckeRepresentatives.*`
    (`redMatrix_apply_*`, `heckeRep_infty`, `heckeRep_coe`),
    `ModularForm.Level.*` (`lift_infty`, `wt_infty`, `wt_coe`, `lift_coe`,
    `coe_slashLinOfMemGamma0_apply`, `coe_slashOfMemGamma0`) and
    `CuspForm.coe_heckeTOne` / `CuspForm.coe_heckeTLinOne_apply`.
  local workaround: the `attribute [-simp]` list in `Lifting.lean` names the
    port's homes; `Ihara.instGroupIharaAmalgam` resolves to the port's anonymous
    `Ihara` instance. No proof body was weakened (the module builds without the
    guards removed; the guards are kept to match the pin's simp environment).
  why not resolved here: pin/port namespace drift; proof-level only.

- `v4.34.0` drift in the transcribed S4d engine (proof-level; no statement
  change). `Algebra.isMulCommutative_adjoin` now takes `s.Pairwise Commute`
    (the pin's `rintro`-without-inequality proof gains a `-` binder and a
    `change`); `Subring.isMulCommutative_closure` likewise takes `Set.Pairwise
    Commute` (the port passes `fun x hx y hy _ => hcomm x hx y hy`); the
    `IsMulCommutative`-derived `CommSemiring` on `Algebra.adjoin` needs
    `open scoped IsMulCommutative` (the pin has it, the first transcription
    omitted it); and the final `rw [Ideal.Quotient.lift_mk]` of
    `exists_ringHom_extends_of_pow_eq_one` does not fire under `rw` in
    `v4.34.0`, so the port finishes with
    `exact Ideal.Quotient.lift_mk (I := 𝔭) φ (fun r hr => hr)`.

- deprecated aliases kept as the pin wrote them (proof-level): `dif_pos`,
  `CuspForm.coe_add`/`coe_zero`/`IsGLPos.coe_smul`, `if_pos`/`if_neg`,
  `Set.mem_setOf_eq`, `haveI`-style linter warnings; no `error`.


## S4 — coefficient ring and Galois conjugation (six nodes), 2024 round

Wiring: `SOURCES` gained the six S4 `Theorems/` wrappers each paired with its `S_`
file (appended last); `PORT_FILES` gained
`FLTForHuman/Algebra/LatticeEigenvalues.lean` and
`FLTForHuman/DeligneSerre/CoefficientRing.lean` (the two extended `Algebra/`
homes were already listed). Checker 2457 → **2463 identical / 0 mismatched / 0
missing**; one-token mutation of the node-1 statement gives 2462/1/0 and the
revert restores 2463/0/0.

- **Refactor round — `Relevement.lean` should import node 5.** The public
  `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul` now lives
  in `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean` (the home the S3 log
  named). `FLTForHuman/DeligneSerre/Relevement.lean` still carries the `private`
  copy `exists_eigenvector_minimalPrimes_aux` (its proof is what was ported
  verbatim, with the S3 log's `-` binder and `change` drift fixes). The refactor
  round should import the algebra home and delete the private copy; nothing else
  in S4 consumes it.

- **Ordering: node 2's home must import node 4's home.** The pin's S4f imports
  `Thm_integralClosure_exists_complex_ringEquiv_apply_eq`, so
  `Algebra/LatticeEigenvalues.lean` imports
  `Algebra/IntegralExtensionCharacters.lean` (node 4). `lake env lean` on
  `LatticeEigenvalues` after adding node 2 reported
  `Unknown constant integralClosure.exists_complex_ringEquiv_apply_eq` until
  `lake build FLTForHuman.Algebra.IntegralExtensionCharacters` had written the
  olean (the stale-olean trap; the file's `private`-only surface is irrelevant).

- **Node 4 (`integralClosure.exists_complex_ringEquiv_apply_eq`) — v4.34 drift.**
  All 15 pin-internal declarations are `private` in a local `ZbarHomsConj`
  namespace; only the target is public. Extra imports the specific-import
  discipline forced: `RingTheory.IsGaloisGroup.Basic` (`IsGaloisGroup`,
  `IsGaloisGroup.of_isFractionRing`) and `FieldTheory.Galois.IsGaloisGroup` (the
  `IsGalois → IsGaloisGroup Gal(K/k)` instance), `FieldTheory.Galois.Profinite`
  (`CompactSpace Gal(K/k)`), `FieldTheory.IsAlgClosed.Classification`
  (`isAlgClosure_of_transcendence_basis`, `equivOfEquiv`), `FieldTheory.KrullTopology`,
  `RingTheory.Invariant.{Profinite,Galois}`,
  `RingTheory.Localization.Integral`, `AlgebraicIndependent.TranscendenceBasis`,
  `Algebra.Polynomial.Splits`, `Algebra.Algebra.Rat`. The pin's
  `set_option synthInstance.maxHeartbeats 320000 in` before `core` was **not**
  needed at the project's 4,000,000 cap (no heartbeat raise in the port). The
  pin's `isAlgebraic_Qbar` finishes after `convert` with no residual goal in
  v4.34 (the pin's two `rfl`s become one), so the port drops the second `rfl`.

- **Node 6 (`DeligneSerre/CoefficientRing.lean`) — reuse and proof-level drift.**
  Reused by import rather than re-ported: the H1 `CuspForm.cusp_periodic`/
  `cusp_holo`/`cusp_bdd` (`ModularForms/HeckePrelude.lean`) stand in for the pin's
  `T_pow_mem_Gamma1`/`cusp_slash_T`/`cusp_periodic` block, so the H2
  `WeightOne/Defs/GammaRational.lean` `T_pow_mem_Gamma1` is not imported and the
  pin's `cusp_slash_T` is not restated; the pin's analytic `cusp_analytic` is a
  private one-liner from the three prelude facts. `CuspForm.qCoeff_heckeTLinOne`,
  `CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`,
  `CuspForm.heckeTLinOne_slashOfMemGamma0`,
  `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast`,
  `UpperHalfPlane.eq_of_forall_qCoeff_eq`, and the `ModularForm.Level` diamond
  vocabulary (`exists_isDiamondLift_of_coprime`, `diamondLinOne`,
  `diamondLinOne_of_not_coprime`, `coe_diamondLinOne_apply`,
  `slashOfMemGamma0`, `slashLinOfMemGamma0`) are imported. `qExpansion_add`/
  `qExpansion_smul` take `AnalyticAt` hypotheses (not periodicity); the private
  `qcLin_apply` (`rfl`) is needed to rewrite `qcLin N n F` to `qCoeff (⇑F) n`
  under `rw`. Deprecated spellings the pin uses were replaced by their v4.34
  names to keep the module warning-free: `if_pos`/`if_neg` →
  `ite_eq_left`/`ite_eq_right`, `CuspForm.coe_add`/`coe_zero`/
  `IsGLPos.coe_smul` → `FunLike.coe_add`/`coe_zero`/`coe_smul`. The pin's
  `attribute [-instance]`/`attribute [-simp]` walls and the `p2m_*` scaffolding
  are not ported (the module elaborates without them). All 44 pin-internal
  declarations are `private`; only the target is public. S3's public `locKer`/
  `adjoinRoot'` (`DeligneSerre/Lifting.lean`) are not needed by node 6.

- **Private restatements (checker-invisible, no exported lemma weakened).**
  In `LatticeEigenvalues.lean`: `RatCoords.exists_sum_smul_eq_of_algebraMap`,
  `RatCoords.exists_finset_separating`, the whole `LatticeEigenInt` block, and
  `RationalEigenConj.exists_ringEquiv_apply_eq` (a thin wrapper composing
  `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed` with node 4,
  not a re-proof), `ringEquiv_ratCast`, `ringEquiv_of_mem_range`. In
  `IntegralExtensionCharacters.lean`: the 15 pin declarations of the S4b file
  above the target. In `CoefficientRing.lean`: the 44 pin declarations of S4a
  above the target. No pin statement was weakened; every public declaration is
  the wrapper verbatim.

- **Build.** Per-module `lake build` (lake-reported, real recompiles):
  `IntegralExtensionCharacters` 5.9 s, `LatticeEigenvalues` 5.5 s,
  `FaithfulLatticeEigenvector` 5.0 s, `CoefficientRing` 6.8 s module. The first
  `CoefficientRing` build paid a one-off 133.2 s wall / 168.3 s user / 22.8 s sys
  dependency cascade (`WeightOne.Gamma1IntegralBasis` and its cone, 4,164 jobs);
  re-running the S4 chain after a header edit is 19.1 s / 22.2 s / 9.0 s. Note
  `touch` alone does **not** force a rebuild (lake hashes content), so mtime-based
  per-module timings silently measure a no-op. Direct consumers still build:
  `EigenformExtraction` green (69.2 s wall including a `HeckeFiniteAlgebra`
  rebuild), `WeierstrassCurve/ModularityLifting` green (21.5 s). `#print axioms`
  on all six headlines: `[propext, Classical.choice, Quot.sound]`. No `sorry`/
  `admit`/`axiom`/`native_decide`; no `import Mathlib`.

## S5 — semisimple descent of a reducible residual representation (one node)

`FLTForHuman/GaloisRep/SemisimpleDescent.lean`, 727 lines, 63 declarations (the
pin's full inventory), namespace `DeligneSerre`. Checker **2463 → 2467 identical**
(+4), 0 mismatched / 0 missing, 30 own-proof exemptions unchanged. The +4 is
exactly the new public surface: the three shared engines plus the target; the 59
other pin declarations are `private`, so the checker never sees them and the
exemption list did not grow.

- **Dedup (three engines, public).** The pin duplicates `charpoly_fin_two`,
  `finrank_eq_one_of_ne_bot_of_ne_top` and
  `isSemisimpleRepresentation_of_forall_exists_isCompl` byte-for-byte between this
  node's `DSRed` block and the deferred sibling
  `S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.lean`
  (`DSRt`, density-dependent half, not one of the 54 nodes). The two files were
  `diff`ed over the three blocks (identical) before writing. Choice logged: they
  are homed **publicly at the pinned names in this module itself** rather than in a
  separate shared module, because the deferred half already imports the ported
  target `DeligneSerre.exists_isSemisimpleRepresentation_…` (the pin's `DSRt.main`
  does), so importing this module later is its natural single dependency and a
  second file would only add a hop. Every other pin declaration — including
  `isCompl_of_finrank_eq_one_of_ne` (the sibling lacks it, so it is *not* one of
  the shared engines), the case-A diagonal representation, and the whole `BData`
  case-B development — is `private`.
- **Statement spelling (`Theorems/` wrapper wins).** The pin has two copies of the
  target: `DSRed.main`/`solution` spell the hypotheses `(hadd : ∀ g, …)` (implicit
  `G` from the section), the `Theorems/` wrapper spells `(hadd : ∀ g : G, …)`. Per
  the standing rule the port takes the wrapper's text; the checker diffed the port
  against the wrapper and reports identical. The three engines have no wrapper, so
  they match the `S_` file's section-variable form verbatim.
- **API route walked (no empty search).** `Representation.IsSemisimpleRepresentation`
  is `ComplementedLattice (Subrepresentation ρ)`
  (`Mathlib/RepresentationTheory/Semisimple.lean`); `Subrepresentation` exposes
  `toSubmodule`, `apply_mem_toSubmodule`, `Subrepresentation.toSubmodule_{inf,sup,injective}`;
  `charpoly` lemmas `Matrix.charpoly_map`, `Matrix.eval_charpoly`,
  `Matrix.charpoly_diagonal`, `Matrix.det_eq_sign_charpoly_coeff`,
  `Matrix.trace_eq_neg_charpoly_coeff` (`Mathlib.LinearAlgebra.Charpoly.Basic`).
  The finite-field engine lives in `Mathlib.FieldTheory.Finite.Basic`
  (`FiniteField.pow_card`, `FiniteField.card`, `X_pow_card_sub_X_ne_zero`,
  `X_pow_card_sub_X_natDegree_eq`); `CharP.exists` there too;
  `charP_of_injective_ringHom` in `Mathlib.Algebra.CharP.Algebra` and
  `add_pow_char_pow` in `Mathlib.Algebra.CharP.Lemmas`.
- **Import set.** The pin's `import Mathlib` is replaced by the port's
  `GaloisRep/Defs/MatrixRepresentation` plus 12 targeted mathlib modules
  (`RepresentationTheory.Semisimple`, `LinearAlgebra.Charpoly.Basic`,
  `Matrix.ToLinearEquiv`, `Matrix.Diagonal`, `Matrix.GeneralLinearGroup.Basic`,
  `FieldTheory.Finite.Basic`, `Algebra.CharP.{Lemmas,Algebra}`,
  `LinearAlgebra.Dimension.{Constructions,FreeAndStrongRankCondition}`,
  `Data.Matrix.Basic`, `Tactic`). Nothing beyond this cone was needed.
- **Proof drift 1 — `map_pullbackChar` (`MonoidHom.ofInjective` inverse).** The
  pin's `have := MonoidHom.apply_ofInjective_symm hinj (χ.codRestrict _ (fun g => …) g);
  simpa using this` fails in v4.34: `simp` collapses the *lemma instance's* subtype
  proof by proof irrelevance to `True`, but cannot do the same for the goal's
  `χ.codRestrict _ hmem g`, so `this` arrives as `True` against an equality goal.
  Remedy: bind the membership proof once as `have hmem : ∀ g, χ g ∈ (Units.map ι).range`
  and close with `exact MonoidHom.apply_ofInjective_symm hinj (χ.codRestrict _ hmem g)`
  (the two `codRestrict` terms then agree syntactically; no `simp` needed).
  Generalizable: when a lemma's statement mentions a subtype element built from an
  inline proof, feed the *same* proof term on both sides instead of relying on
  `simpa` to identify propositionally-equal proofs.
- **Proof drift 2 — private `structure` + dot notation.** `BData` (and its 40-odd
  `BData.*` helpers) must be `private` per the work order, but the pin's proofs are
  written with dot notation `D.chi2_eq`, `D.coord_spec`, … over a `namespace BData`.
  Verified in `Scratch.lean` before transcribing that v4.34 resolves `x.foo` against
  a `private structure`'s namespace fine when the helper is `private` in the same
  file, so the pin's proof text could be kept; only the modifier changed. No
  re-spelling of the case-B development was needed.
- **Linter options.** The module sets `linter.style.haveILetI false` (the pin's
  `haveI` walls in `add_pow_char` and the target are load-bearing and kept literal)
  and `linter.unusedSectionVars false` (`chi2_mem_range_of_chi1_mem_range` inherits
  the section's `[Fintype κ]`/`hmul` that it does not use, as in the pin). With
  these, the edit-loop check is warning-free.
- **Build.** `flock /tmp/flt_for_human.lock timeout 120 lake build
  FLTForHuman.GaloisRep.SemisimpleDescent`: 7.1 s module, 7.565 s wall / 11.441 s
  user / 4.260 s sys, after a one-off dependency cascade (3,098 jobs including the
  phase-D `MatrixRepresentation` olean). Edit-loop checks were ~5.3 s each
  (5.332 s wall / 9.655 s user / 2.376 s sys; the `Mathlib.Tactic` import is
  olean-cached). `#print axioms` on all four public
  declarations: `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/
  `axiom`/`native_decide`; no `import Mathlib`. The pin's `p2m_export`/
  `p2m_reactivate` scaffolding and its `attribute [-…]` guards were not ported.
- **Checker instrumentation.** One-token mutation (`X ^ 2` → `X ^ 3` in
  `charpoly_fin_two`) gave exactly 2466 identical / 1 mismatched / 0 missing, then
  reverted to 2467/0/0, confirming the new `PORT_FILES`/`SOURCES` wiring is live.
  `SOURCES` appended the wrapper before its `S_` file, last, per the standing rule.

## S7-I — place / Frobenius vocabulary (7 of 8 nodes)

- **Delivered.** `NumberTheory/FrobeniusAtPlace.lean` (+173 lines, 349 → 522) gains
  nodes 1–4 (`isFrobeniusAt_of_forall_smul_sub_pow_mem` and the three existence
  corollaries); the three new modules are
  `NumberTheory/FrobeniusDensity/ValuationSubringLocalization.lean` (136 lines,
  node 5), `.../FrobeniusLift.lean` (257, node 6) and `.../KerRestrictNormalHom.lean`
  (92, node 7). Checker 2467 → 2471 → 2472 → 2473 → 2474 identical, 0/0
  throughout. Builds (module / wall / user / sys):
  `FrobeniusAtPlace` 6.7 s / 9.40 s / 12.25 s / 3.78 s;
  `ValuationSubringLocalization` 3.6 / 5.60 / 3.83 / 2.64;
  `FrobeniusLift` 8.7 / 11.03 / 8.54 / 3.10;
  `KerRestrictNormalHom` 3.5 / 5.35 / 3.51 / 2.47.
  `#print axioms` on all seven headlines: `[propext, Classical.choice, Quot.sound]`.
- **Reuse, not re-proof.** Node 2 is derived from the already-ported
  `ValuationSubring.exists_isFrobeniusAt_rat` (the pin re-proved the weaker
  statement from `Subring ⊥`) and node 3 is the direct call to the ported
  `ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime`; node 4 composes them.
  Node 6 reuses the ported `FrobeniusDensity.ratPrimeIdeal` /
  `ne_bot_of_liesOver_ratPrimeIdeal` and mathlib's `arithFrobAt`,
  `IsArithFrobAt.arithFrobAt`, `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.
  No cross-module duplication was found: each of the pin's four helper blocks
  (`C6PortS10T3b`, `C6P1T3a`, `C6P1T2`, `P2mWs11LV`) occurs once, so each is
  transcribed `private` in the module that uses it (the pin's public helpers
  `carrier`/`subring`/`valuationSubring`, `restrictNormal_restrictScalars`,
  `exists_numberField_ker_restrictNormalHom_le`,
  `exists_finiteDimensional_fixingSubgroup_le` are therefore demoted; only the
  eight targets are public).
- **API drift 1 — a short name re-resolves under a new enclosing namespace.**
  The pin's node-1 prelude sits in `namespace C6PortS10T3b`, where the bare
  `mem_nonunits_iff` resolves to the root lemma
  (`RingTheory/Ideal/Nonunits.lean:32`). Transcribed under `namespace
  ValuationSubring`, the same identifier resolves to
  `ValuationSubring.mem_nonunits_iff` (`x ∈ A.nonunits ↔ A.valuation x < 1`), so
  `rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]` failed on two goals.
  Remedy: `_root_.mem_nonunits_iff`. Generalizable: when a pin `private` prelude
  is moved into its subject namespace, every short name in it must be re-checked.
- **API drift 2 — `rw [← map_pow]` after a `change` on a quotient.**
  `FrobeniusLift`'s `hFbij` transcribes the pin's
  `change (Ideal.Quotient.mk Qt ⟨c, hcint⟩) ^ ℓ = _; rw [← map_pow]; congr 1`.
  In v4.34 the rewrite reports "Did not find an occurrence of the pattern `?f ?a ^
  ?n`" (Lean also notes the goal is not type-correct under `implicit`
  transparency) — the `Pow` instance used by `frobenius_def`'s power form is not
  syntactically the one `rw` builds for `map_pow`. Remedy: a `show … = … from
  (map_pow (Ideal.Quotient.mk Qt) ⟨c, hcint⟩ ℓ).symm` rewrite, plus an explicit
  `have hm : (⟨c, hcint⟩ : 𝓞 ℚ̄) ^ ℓ = b := Subtype.ext hc`; under `congrArg` the
  elaborator cannot infer `Subtype.ext`'s expected type (`↑(?m ^ ℓ) = ↑?m`), so
  the equality has to be bound with its type. The analogous step in
  `FrobeniusAtPlace.lean` (via a local `have fa_apply`) is unaffected.
- **Search results (positives).** v4.34 still has
  `IsDedekindDomain.HeightOneSpectrum.exists_primeCompl_mul_eq_or_mul_eq`,
  `IsIntegralClosure.isIntegral_algebra (R) (A := B) B` (A and B both explicit),
  `Ideal.IsMaximal.under` (now an *instance* `[P.IsMaximal] → (P.under A).IsMaximal`,
  so the pin's `haveI := Ideal.IsMaximal.under ℤ Qt` compiles),
  `NumberField.mk`, `AlgEquiv.restrictNormalHom_surjective`,
  `Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite`, and
  `Ideal.Quotient.stabilizerHom_surjective_of_profinite`.
- **Stopped item — node 8 `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`.**
  Its pin file imports `Theorems/Thm_FrobeniusDensity_degOneSum_add_log_isBigO`
  and its proof consumes `FrobeniusDensity.degOneSum_add_log_isBigO` — an S7-II
  node (292 pin lines), not ported. The target is "infinitely many rational primes
  have a degree-one prime in `Frac(R)`"; the pin's only route runs through the
  degree-one counting chain, and the recorded negative is that mathlib v4.34 has
  no Chebotarev and no splitting/degree-one-prime infinitude result
  (`grep -rn "splitsCompletely\|Chebotarev" Mathlib` → nothing; no
  `degreeOne`/splitting-completely vocabulary). No proof of the target without
  S7-II was found, so the node is stopped at the module boundary (its module was
  not created and nothing references it). The other seven S7-I nodes are complete
  and independent of S7-II.
- **Linter.** The two transcribed proof modules set
  `linter.style.haveILetI false` (the pin's `haveI` instance walls are
  load-bearing); the edit loop is warning-free.
- **Checker instrumentation.** One-token mutation
  (`A.IsFrobeniusAt σ (p : ℕ)` → `… (p : ℕ + 0)` in node 4) gave exactly
  2473 identical / 1 mismatched / 0 missing, then reverted to 2474/0/0.
  `SOURCES` appended each `Theorems/` wrapper before its `S_` file, last; the
  module `NumberTheory/FrobeniusAtPlace.lean` was already in `PORT_FILES` and was
  not re-listed.

## S7-II — zeta / coset / Möbius counting chain (13 nodes + two deferred blocks)

Result: checker 2474/0/0 → **2531/0/0** (+57). Seven new modules under
`NumberTheory/FrobeniusDensity/`: `MobiusZeta.lean` (206 lines), `IdealSum.lean`
(60), `PrimeSumSplit.lean` (115), `PrimeSumAsymptotic.lean` (472),
`DegOneSumAsymptotic.lean` (275), `DegOneAsymptoticProof.lean` (30),
`DegreeOneCount.lean` (382). `#print axioms` on all 13 headlines plus the two
promoted prelude blocks returns `[propext, Classical.choice, Quot.sound]`.

- **Checker textual rules bit twice, both predictable (playbook §4).**
  (1) *Section variables are invisible to the checker.* A headline written under
  `variable (K : Type*) [Field K] [NumberField K]` produces the statement text
  `{s : ℝ} (hs : 1 < s) : …`, while the `Theorems/` wrapper spells the binders
  out: `(K : Type*) [Field K] [NumberField K] {s : ℝ} (hs : 1 < s) : …`. Five
  headlines (`idealSum_ne_top`, `tendsto_sub_one_mul_idealSum_test`,
  `primeSum_eq_degOneSum_add`, `summable_degOne_term`, `degOneSum_add_log_isBigO`)
  reported `MISMATCH` with the two texts differing only in the explicit binders.
  Fix: spell the headline binders **explicitly, exactly as the wrapper**, even
  though a `variable` already supplies them.
  (2) *The declaration kind is matched.* The promoted `degOneSum_ne_top` was
  declared `theorem` where both pin copies say `lemma`, and the checker's `find`
  requires `kind` equality, so it reported a mismatch whose port/FLT texts were
  identical. Fix: `lemma`.
- **`variable {K}` after `variable (K : Type*)` makes `K` implicit in later
  declarations that do not list it.** The pin's `variable {K}` line means its
  `(K : Type*)` section binder is overridden, yet the pin's own calls
  (`primeSum_ne_top K hs`, `absNorm_eq_pow_inertiaDeg_ratBelow K v`) pass `K`.
  Transcribed literally the port got `Application type mismatch: The argument K
  … expected 1 < ?m`. Fix: drop the `variable {K}` line and keep `K` explicit in
  the private helpers, so the pin's `… K …` calls elaborate unchanged.
- **Dedup actually taken.** `MobiusZeta` reuses Basic's `mem_zpowers_pow_div_iff`,
  `exists_pow_coprime_eq_of_orderOf_eq`, `orderOf_pow_orderOf_div`,
  `ncard_conj_mem_eq_card_mul_ncard`, `ncard_eq_sum_indicator`; only the deferred
  `sum_moebius_mem_zpowers` is new (public at the pin name). `PrimeSumAsymptotic`
  drops the pin's redeclared public `primeSum_le_idealSum` (Basic already has it;
  a literal transcription would clash). `DegOneSumAsymptotic` reuses
  `one_le_cast_absNorm`, `primeSum_ne_top` (public, from `PrimeSumAsymptotic`),
  `degOneSum_ne_top` (public, from `PrimeSumSplit`), Basic's `primeSum_le_idealSum`
  and `toReal_term`; the pin-local `primeSum_ne_top {s} (hs : 1 < s)` has a
  different signature from the public `primeSum_ne_top (hfin)`, so it is restated
  privately as `primeSum_ne_top_of_one_lt`. `DegreeOneCount` reuses Basic's
  public `card_le_of_forall_pow_eq` (the pin repeats it privately in two files).
- **Coset engine check (workorder §2).** `Basic.ncard_conj_mem_eq_card_mul_ncard`
  is the exact quotient-fixed-point count `weight_eq` needs and is reused there.
  The S7-II degree-one coset count is *not* the generic engine: the pin's helpers
  (`restrictPrime`, `forall_smul_eq_iff_stabilizer_le`, …) are `Ideal`-specific
  and its orbit step is mathlib's `Ideal.exists_smul_eq_of_isGaloisGroup` /
  `Ideal.under_smul` / `MulAction.stabilizer_smul_eq_stabilizer_map_conj`;
  `FLTForHuman/FieldTheory/FiniteGroupAction.lean`'s
  `MulAction.ncard_orbit_inter_orbit_mul_card` /
  `Subgroup.exists_eq_mul_of_index_inf_eq` are a different (pretransitive)
  setting and `Bifibre.lean`'s `orbit_gal_eq`/`index_range_resHom` act on
  `Place`, not `Ideal`, so neither is applicable. Transcribed faithfully.
- **`ENNReal.le_tsum` implicit `f`.** In v4.34, `ENNReal.le_tsum (⟨⊤, …⟩)` in
  `one_le_idealSum`/`one_le_factoredSum` does not synthesize the implicit
  function from the expected `idealSum`/`factoredSum` (the constructor argument
  blocks the higher-order abstraction); passing `f := fun I => normRpow K s I.1`
  explicitly is the same proof. Proof-term only.
- **`ENNReal.rpow_neg_one`, `ENNReal.tsum_geometric`,
  `Ideal.card_stabilizer_eq_card_inertia_mul_finrank`,
  `Ideal.inertiaDeg_eq_of_isMaximal`, `Module.natCard_eq_pow_finrank`,
  `Ideal.card_primesOverFinset_le_finrank`** all survive at v4.34 unchanged.
- **Checker instrumentation.** One-token mutation (`idealSum_ne_top`'s `1 < s`
  → `1 ≤ s`) gave exactly 2530 identical / 1 mismatched / 0 missing, then reverted
  to 2531/0/0. `SOURCES` appended each `Theorems/` wrapper (last) plus the four
  `S_` files not already listed by H1; the nine H1-listed `S_` files were not
  repeated. `PORT_FILES` lists the seven new modules last.
- **Out of scope / handoff.** S7-III was not started. S7-II now provides
  `FrobeniusDensity.degOneSum_add_log_isBigO`, which the S7-I tail node
  `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`
  consumes — that node remains for the S7-I-tail dispatch.

## S7-III — the density statement and its applications (6 nodes) + the S7-I tail node (2026-10-01)

Scope: the six S7-III public targets
(`statement_of_degOneAsymptotic`, `statement`,
`exists_frobenius_conj_pow_of_statement`, `frobeniusPowerDense_of_le_ker`,
`ncard_conj_gen_ne_zero_iff`,
`Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`) **plus** the S7-I
tail node `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`.
Seven new modules in `FLTForHuman/NumberTheory/FrobeniusDensity/`, one per pin
`S_` subject, 702 lines total (`NcardConjGen` 32, `StatementOfDegOneAsymptotic`
181, `Statement` 26, `ExistsFrobeniusConjPow` 127, `FrobeniusPowerDense` 72,
`PrimeIsFrobeniusAtConjPow` 52, `DegreeOnePrimesInfinite` 212). Checker
**2531 → 2548 identical / 0 mismatched / 0 missing** (+17: 7 targets, the three
public `C6P1CFD` helpers, and the tail's seven helpers). All seven headlines
`#print axioms` clean `[propext, Classical.choice, Quot.sound]`; no `sorry`.

- **Reuse (no re-proof).** `statement_of_degOneAsymptotic` imports S7-II's
  `MobiusZeta.weight_eq` / `sum_moebius_mul_pos`, `DegreeOneCount.
  ncard_degreeOne_primesOver_eq_ncard_frobFixed`, and the H1/D1 vocabulary
  (`badPrimes`, `inertia_eq_bot_of_notMem_badPrimes`, `degOneCount_of_{prime,
  not_prime}`, `realizesCyclicAt_of_exists`, `Statement`, `DegOneAsymptotic`).
  `statement` imports S7-II's `degOneAsymptotic`. `exists_frobenius_conj_pow_of_statement`
  imports S7-I's `FrobeniusLift`, `ValuationSubringLocalization` and
  `FrobeniusAtPlace` (`ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem`).
  `frobeniusPowerDense_of_le_ker` imports `FrobeniusPowerDense` (D2) and the
  density statement; `exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen` imports
  S7-I's `KerRestrictNormalHom`; the tail imports S7-II's
  `degOneSum_add_log_isBigO`. No S7-II headline was restated.
- **Ideal-coset finding held.** S7-III needs no `Ideal`-orbit step of its own:
  the ideal-coset work is entirely inside S7-II's
  `ncard_degreeOne_primesOver_eq_ncard_frobFixed` / `stabilizer_eq_zpowers_arithFrobAt`,
  which this dispatch just consumes. The only `Ideal` API used directly here is
  `Ideal.nonempty_primesOver`, `Ideal.exists_maximal_ideal_liesOver_of_isIntegral`,
  `Ideal.mem_of_liesOver` and `Ideal.mem_span_singleton_self`.
- **Public vs private helpers.** The pin's
  `S_FrobeniusDensity_exists_frobenius_conj_pow_of_statement.lean` makes
  `galoisLevel`, `le_galoisLevel` and
  `exists_pow_pow_eq` public, and the tail `S_CommRing_…` makes all seven helpers
  public (`exists_int_ne_zero_eq_mul`, `charZero_fractionRing`,
  `finiteDimensional_fractionRing`, `numberField_fractionRing`,
  `nonempty_ringHom_zmod`, `tendsto_log_sub_one`,
  `infinite_setOf_degOneCount_ne_zero`). All ten are transcribed **public at the
  pinned names**, so the checker verifies them (they are not `OWN_PROOFS`
  exemptions). Only `statement_of_degOneAsymptotic`'s two helpers
  (`tendsto_log_sub_one`, `not_isBigO_one_of_tendsto_atBot`) stay `private`, as
  the pin has them.
- **Privately-restated share.** `tendsto_log_sub_one` is stated `private` in
  `StatementOfDegOneAsymptotic` (pin-private there) and *again* public in
  `DegreeOnePrimesInfinite` (pin-public there): the tail cannot import the density
  module without dragging the whole statement chain, so sharing it would invert
  the import graph. Two 7-line copies, one per pin copy; recorded, not hidden.
- **`NumberField.RingOfIntegers` structure-literal `simp` is import-fragile.**
  The pin builds `i : R →+* 𝓞 (FractionRing R)` with
  `map_mul' := … ext (by simp [NumberField.RingOfIntegers.coe_eq_algebraMap])`.
  Under our specific imports (no `import Mathlib`) `simp` makes **no progress** on
  `↑⟨(algebraMap R K) (x*y), _⟩ = ↑(⟨…x…⟩ * ⟨…y…⟩)` and the goal is left open
  (`rfl` closes `map_mul'` but *not* `map_add'`/`map_zero'`, so even `rfl` is not
  a uniform fix). Mathlib's own `mk_add_mk`/`mk_mul_mk` carry the comment
  "these lemmas don't seem to fire?". Fix: prove each field directly from the
  `algebraMap` laws, `NumberField.RingOfIntegers.ext (map_mul (algebraMap R K) x y)`
  etc. Proof-term only; statements untouched.
- **Missing module path.** `Mathlib.RingTheory.IntegralClosure.IntegralClosure`
  does not exist (it is a **directory**); `integralClosure` lives in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`. Same class of drift as the
  recorded `Mathlib.LinearAlgebra.Quotient` case.
- **Lint options transcribed.** The ported proofs introduce instances with
  `haveI`/`letI` in `Prop` goals (`statement_of_degOneAsymptotic`,
  `exists_frobenius_conj_pow_of_statement`, `frobeniusPowerDense_of_le_ker`,
  `exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen`, `DegreeOnePrimesInfinite`),
  so those four modules carry `set_option linter.style.haveILetI false` as the
  other ported proof files do. The tail also trips `linter.unusedSectionVars` on
  `charZero_fractionRing` (the pin's section binder is wider than the proof needs)
  and `linter.unnecessarySeqFocus` on the pin's
  `convert … <;> first | rfl | …`; both are left as warnings, matching the pin.
  `if_pos`/`if_neg` deprecations are unchanged from the pin proofs.
- **Tail construction is not defeq-cheap.** `𝓞 K`'s derived `Add` does not reduce
  by `rfl` to the pointwise `Subtype` addition the way its `Mul` does, which is
  what forced the explicit `map_add` field above; the rest of the tail
  (`charZero_fractionRing`, `finiteDimensional_fractionRing`,
  `numberField_fractionRing`, `nonempty_ringHom_zmod`,
  `infinite_setOf_degOneCount_ne_zero`) transcribed first try.
- **Checker instrumentation.** One-token mutation
  (`ncard_conj_gen_ne_zero_iff`'s second `orderOf σ` → `orderOf τ`) gave exactly
  2547 identical / 1 mismatched / 0 missing, then reverted to 2548/0/0.
  `SOURCES` appends each `Theorems/` wrapper immediately before its `S_` file,
  last; `PORT_FILES` lists the seven new modules last.
- **Out of scope / handoff.** With this dispatch S7 is complete: S7-I (all 8
  nodes, the tail now ported), S7-II (13 + 2 deferred), S7-III (6) — 27 nodes.
  `FrobeniusDensity.statement` is available for S6c; the density *applications*
  in S6/S8 and the Group B / ray-class continuation remain out of this set.



## S6 — representation conjugacy and lifting (3 nodes)

Checker: **2548 → 2551 identical / 0 mismatched / 0 missing** (+1 per module,
each module's only public declaration is its pin target; all pin helpers are
`private`). `#print axioms` on the three headlines gives
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`. Measured builds: `RepConj` 213 lines, 2.7 s / 4.3 s wall;
`RepLift` 772 lines, 8.3 s / 10.9 s wall; `ConjFromFrobenius` 189 lines,
6.5 s / 9.3 s wall.

- **Layout.** `RepConj.lean` (S6b, character determines a finite-image `GL₂(ℂ)`
  representation up to conjugacy), `RepLift.lean` (S6a, the mod-`ℓ` → char-0 lift
  with matching charpolys), `ConjFromFrobenius.lean` (S6c, equal Frobenius
  charpolys ⟹ global conjugacy). Each keeps the pin's `Representation.*` /
  `GaloisRep.*` target name; the pin's helper blocks (`P2mBN2C`, `BrauerLiftSqZero`,
  `BrauerLiftComplete`, `BrauerLiftEmbed`, `BrauerLiftMain`, `DeligneSerreL32`)
  are all `private`, so the checker sees exactly the three wrappers and needs no
  `OWN_PROOFS` exemption. `RepLift`'s four pin namespaces are kept for
  readability; the pin's `p2m_export`/`p2m_reactivate` scaffolding is dropped.
- **Node 3 reuses by import, not copy.** `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range`
  (node 1) and `GaloisRep.finite_range_of_factorsThroughFiniteLevel` (H1
  `Prelude.lean`) are imported, not re-proved; node 3's own helpers are only
  `isOpen_ker`, `sq_eq_trace_smul_sub`,
  `trace_pow_eq_of_trace_eq_of_det_eq`, `charpoly_pow_eq_of_charpoly_eq` and
  `charpoly_eq_of_frobenius`. `Γℚ` is restated as a file-scope `local notation`
  in `ConjFromFrobenius.lean`, matching the wrapper's spelling so the checker's
  text diff matches.
- **Privately-restated shares: none from mathlib.** Unlike S7's
  `tendsto_log_sub_one`, no unexported mathlib lemma had to be restated locally.
  The only `private` restatements are the pin's own helpers, which the work order
  requires to stay `private`.
- **Import drift (S6b/`RepConj`).** `open scoped MatrixGroups` needs
  `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`; without it the scoped
  namespace is `unknown namespace MatrixGroups` (and `GL` unknown). `ℂ` needs
  `Mathlib.Basic.Complex.Basic` — the old `Mathlib.Data.Complex.Basic` is now a
  **deprecated** import that warns. `BrauerNesbitt`'s semisimplicity `inferInstance`
  needs `Mathlib.RepresentationTheory.Maschke` (the instance is not re-exported by
  `RepresentationTheory.Basic`). The pin's `@[scoped simp] repOfGL_apply` was
  dropped and the one `simpa` that relied on it became
  `simpa [repOfGL_apply] using …`; proof-term only, statement untouched.
  `Matrix.trace_eq_neg_charpoly_coeff` now takes `[Nonempty n]`, so the
  `isEmpty_or_nonempty` branch supplies `haveI := hn` (the pin's `rw` did not).
- **Import drift (S6a/`RepLift`).** The 685 pin lines transcribed essentially
  unchanged; the only API drift was import/module shape:
  `Cardinal.mkRat` (`SetTheory.Cardinal.Rat`), `Cardinal.mk_complex`
  (`Analysis.Complex.Cardinality`), the `IsAlgClosed ℂ` instance
  (`Analysis.Complex.Polynomial.Basic`), `spectrum.pow_mem_pow`
  (`FieldTheory.IsAlgClosed.Spectrum`, not `Algebra.Algebra.Spectrum.Basic`),
  `if_neg` → `ite_eq_right`, and `dif_pos` → `dite_eq_left`
  (`simp only [e, dite_eq_left (hexp r hr)]`). `Matrix.map_sub`/`map_add` keep the
  pin's function-plus-proof form `Matrix.map_sub _ (map_sub _)`;
  `WittVector.eq_zero_of_p_mul_eq_zero` needs `PerfectRing k p`, which
  `[Finite k] [CharP k p]` synthesizes via `PerfectField.ofFinite`+`toPerfectRing`.
  `IsAdicComplete.le_jacobson_bot` takes `I` **explicitly** (probed with
  `#check`), so the pin's `IsAdicComplete.le_jacobson_bot I hmem` works verbatim.
- **`Mathlib.Tactic` umbrella used.** `RepLift` imports `Mathlib.Tactic` (five
  existing port modules already do) for `noncomm_ring`, `omega`, `abel`, `ring`,
  `linear_combination` and `push_cast`; the subject imports stay specific. This is
  not `import Mathlib`.
- **Checker wiring.** `SOURCES` appends, last, the three `Theorems/` wrappers each
  immediately before its `S_` file; `PORT_FILES` lists the three modules last, so
  no earlier last-name match can flip. The identical-count delta is exactly +3.

## S8 — the complex-trace assembly (the capstone), 2026-10-02

`FLTForHuman/DeligneSerre/Assembly.lean`, 493 lines, 10 `private` helpers plus the
one public target. Checker **2551 → 2552 identical / 0 mismatched / 0 missing**
(+1: the target is the module's only public declaration). `#print axioms
DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual` gives
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`axiom`/
`native_decide`, no `import Mathlib`. Measured build: 8.9 s kernel / 12.1 s wall
(`user 8.5 s`, `sys 6.7 s`).

- **Conditional capstone, `hfam` kept as a hypothesis.** The file builds
  unconditionally with the pin's `hfam` binder; nothing is discharged from
  ray-class analysis (`PORTING-DeligneSerre.md` §0.3). The statement is the
  `Theorems/` wrapper's, spelled with the wrapper's `Γℚ` local notation so the
  checker's text diff matches.
- **Reused by import, not re-proved.** `GaloisRep.finite_range_of_factorsThroughFiniteLevel`
  (H1 `Prelude.lean`) and `DegreeOnePrimes.exists_int_ne_zero_eq_mul` (S7-I tail,
  the S8 pin's `exists_int_ne_zero_mem_span` generalised from `IsIntegral ℤ x` to
  `[CommRing R] [IsDomain R] [Module.Finite ℤ R]`) are imported. The gluing
  targets `Representation.exists_monoidHom_complex_charpoly_map_eq_of_not_dvd_natCard`
  (S6a `RepLift`) and
  `GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`
  (S6c `ConjFromFrobenius`), plus
  `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int` (S7)
  and `ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure`
  (`NumberTheory/FrobeniusAtPlace.lean`). The `ValuationSubring.{LiesOverPrime,
  IsFrobeniusAt,inertiaSubgroupIn}` and `GaloisFactorsThroughFiniteLevel`
  vocabulary is the D0/Ramification one.
- **Privately-restated shares: ten, the pin's own helpers.** Of the pin's 13
  declarations, 10 are restated `private` (`finite_setOf_prime_exists_apply_eq_zero`,
  `eq_of_infinite_setOf_apply_eq`, `root_of_unity_of_charpoly`,
  `exists_trace_eq_add_of_pow_eq_one`, `coeff_quadratic`, `exists_lift_at`,
  `infinite_setOf_prime_nonempty`, `exists_eq_add_eq_mul`, `exists_good_lift`,
  `finite_setOf_prime_exists_apply_eq`); `solution` becomes the public target.
  None from mathlib needed restating.
- **Import drift.** `Set.Infinite.diff` is deprecated (2026-06-03) → use
  `Set.Infinite.sdiff` (same signature); three call sites moved. The
  `Subalgebra ℤ ℂ` instances needed by S7's `IsDomain`/`CharZero` requirements are
  not re-exported by `Mathlib.RingTheory.Valuation.*`: add
  `Mathlib.Algebra.Algebra.Subalgebra.Basic` (`Subalgebra.isDomain`) — `CharZero`
  comes from the `Subsemiring` instance. `spectrum.pow_mem_pow`
  (`Mathlib.FieldTheory.IsAlgClosed.Spectrum`), `spectrum.one_eq`
  (`Mathlib.Algebra.Algebra.Spectrum.Basic`), `Matrix.mem_spectrum_of_isRoot_charpoly`
  (`Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs`) and `Complex.exists_root`
  (`Mathlib.Analysis.Complex.Polynomial.Basic`) all had to be imported explicitly.
- **Parser friction (not drift).** A `simp only [...] at` whose location list is
  broken onto the next line with deeper indentation fails with
  `expected '*' or checkColGt`; keep `at h1 h2 …` on one line, or break *before*
  `at`. The linter's unused-`simp`-arg warning fired on `coeff_X` in
  `coeff_quadratic`'s first conjunct (dropped; proof-term only).
- **Checker wiring.** The pin `S_` file was already in `SOURCES` from the H1
  prelude block (for `finite_range_of_factorsThroughFiniteLevel`), so only the
  `Thm_*` wrapper was appended, last. `PORT_FILES` appends `Assembly.lean` last.
  Because every helper is `private`, the checker's `raw_declarations` skips them
  and no `OWN_PROOFS` exemption is needed.
- **Wire test outcome: no upstream gap surfaced.** Every binder, instance and
  lemma the pin's assembly reaches for exists in the port under the expected name
  and shape; the only adaptations were the `Γℚ` spelling and the two reuse-by-import
  substitutions above.

## Refactor round (2026-09-29)

Closing round of the 54-node weight-one slice. **No statement changed**: the
checker held at **2552 identical / 0 mismatched / 0 missing** before and after
every edit, and all 54 headlines keep `[propext, Classical.choice, Quot.sound]`.

### Promoted / deleted

- **S3/S4 duplication resolved.** `DeligneSerre.exists_eigenvector_of_mem_minimalPrimes_of_faithfulSMul`
  (S4 node 5, `FLTForHuman/Algebra/FaithfulLatticeEigenvector.lean`) is now
  imported by `FLTForHuman/DeligneSerre/Relevement.lean`; the S3 private
  transcription `exists_eigenvector_minimalPrimes_aux` (113 lines, the S3 log's
  entry above) is deleted and its single call site now names the public lemma.
  The two statements were checked first and are identical (same `K/V/T`
  binders, `[SMulCommClass T K V] [FaithfulSMul T V]`, hypothesis
  `h𝔭 : 𝔭 ∈ minimalPrimes T`, conclusion `∃ χ, RingHom.ker χ = 𝔭 ∧ ∃ x, x ≠ 0 ∧
  (∀ p ∈ 𝔭, p • x = 0) ∧ (∀ r, r • x = 0 → r ∈ 𝔭) ∧ ∀ t, t • x = χ t • x`).
  `lake build FLTForHuman.DeligneSerre.Relevement` green, 3,813 jobs, wall
  19.4 s. The two S4 `hφAsmul`/`hφAinj` drift fixes the S3 log recorded live in
  the public copy already; the deleted copy was the same proof text.
- **`locKer` / `adjoinRoot'` — no action needed.** Both are public in
  `DeligneSerre/Lifting.lean`; a tree-wide grep shows no other module references
  them, so `DeligneSerre/CoefficientRing.lean` and `Relevement.lean` need no
  import and no duplicate was created. Confirmed, not deferred.

### Dedup scan of the friction log

Every "privately-restated share" entry was re-read against the tree. The only
one whose public home now exists was the S3/S4 `exists_eigenvector_minimalPrimes_aux`
handled above. The remaining private restatements are deliberate and unchanged:

- S2 keeps `periodic_add_smul` / `periodic_smul` / `T_mem_Gamma1` /
  `T_pow_mem_Gamma1` / `dd*` private because their public copies live in the
  heavy `WeightOne` cone (`GammaRational`, `Gamma1Basis`, `X1DiamondRational`);
  importing them would invert the import graph (playbook §2.4/§5).
- S4's `RatCoords.exists_finset_separating` (`Algebra/LatticeEigenvalues.lean`
  and `DeligneSerre/CoefficientRing.lean`) has **no public home** anywhere
  (both copies are pin-private); left as the S4 log records.
- S7-III's `tendsto_log_sub_one` is deliberately restated (sharing would drag the
  whole density statement chain into the tail module); left.
- S5's three engines are already public in `GaloisRep/SemisimpleDescent.lean`;
  S6 reuses by import; S8 has no mathlib share.

Incidental tool finding (not from a friction entry, no action): the 4-line
private `det_eq` in `ModularForms/Gamma1Vanishing.lean` and
`ModularForms/HeckeEigenNebentypus.lean` is statement-identical to the public
`ModularForm.HeckeRepresentatives.det_eq` (and to the public `det_eq` in
`EisensteinG1Transform.lean`). It is inside the pin's `det_eq`/`det_mod`/`dd`
helper block that the S2 log deliberately privatised, so it is recorded here as
a residual candidate rather than promoted in this round.

### Consumer wire test

Created `spec/DeligneSerreConsumer.lean`, outside every library, modelled on
`spec/ModularCurveConsumer.lean`. No `#check`s, no `sorry`; every zone is an
elaborated proof term, and each headline is imported from its own module, so
deleting one module breaks its zone.

- **S1** — `ModularForm.exists_weightOne_eisenstein_qCoeff_eq_of_isPrimitive_of_odd`
  (constant-`q`-coefficient law extracted from the existential) plus the
  `EisensteinSeries.weierstrassZeta_add_one_and_add_tau_and_smul` construction
  target (its first conjunct at an arbitrary non-lattice point).
- **S2** — `CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1`
  and `CuspForm.slash_eq_dirichlet_smul_of_qCoeff_hecke_eigen`, each under its
  hypotheses (the Hecke-eigenvalue datum `heig` is not ported as an instance).
- **S3** — `DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr`
  (extracting the nonzero lifted eigenform) and
  `DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen`
  (extracting the level description `p ∣ M ↔ p ∣ N ∨ p = 0`). Both
  **hypothesis form**: the `hT` congruence datum and its `∃ r : R` witness are
  the unported Hecke-congruence input.
- **S4/S5** — `DeligneSerre.exists_subalgebra_qCoeff_mem_forall_ringHom_exists_qCoeff_eq_of_weightOne_hecke_eigen`
  (finite `ℤ`-algebra extracted) and
  `DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range`
  (the charpoly conclusion extracted), both in hypothesis form.
- **S6** — `Representation.exists_conj_eq_of_charpoly_eq_of_finite_range` and
  `GaloisRep.exists_conj_eq_of_charpoly_frobenius_eq_of_galoisFactorsThroughFiniteLevel`.
- **S7** — `FrobeniusDensity.statement` at `L = ℚ` (a prime outside `S` realising
  the identity class) and `CommRing.infinite_setOf_prime_nonempty_ringHom_zmod_of_moduleFinite_int`
  at `R = ℤ`, composed with `Set.Infinite.mono` to conclude `{ℓ | ℓ.Prime}` is
  infinite.
- **S8** — `DeligneSerre.exists_galoisRep_complex_trace_frobenius_eq_of_forall_residual`,
  **hypothesis form**: the `hfam` compatible residual family is the deliberately
  unported ray-class input (`PORTING-DeligneSerre.md` §0.3); the zone extracts
  the resulting finite-level complex representation.

Run result:

```text
flock /tmp/flt_for_human.lock timeout 180 lake env lean \
  -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
exit 0 (7.0 s wall, no diagnostics)
```

### Drift cleared (exact renames, proof bodies otherwise untouched)

69 deprecated pin-inherited identifiers replaced in the new Deligne–Serre
modules, in 17 files. `if_pos → ite_eq_left`, `if_neg → ite_eq_right`,
`dif_pos → dite_eq_left`, `dif_neg → dite_eq_right`,
`Set.mem_setOf_eq → Set.mem_ofPred_eq`; `Set.Infinite.diff → Set.Infinite.sdiff`
needed no work (S8 `Assembly.lean` had already been migrated).

| file | renames |
|---|---|
| `ModularForms/Eisenstein/WeierstrassZetaSum.lean` | 13 |
| `ModularForms/Eisenstein/WeightOneMultiplier.lean` | 2 |
| `ModularForms/Eisenstein/WeierstrassZetaQuasiPeriod.lean` | 2 |
| `ModularForms/Eisenstein/EisensteinG1QExpansion.lean` | 1 |
| `ModularForms/Gamma1Vanishing.lean` | 3 |
| `ModularCurve/IharaSurjective.lean` | 2 |
| `DeligneSerre/Relevement.lean` | 7 |
| `DeligneSerre/Lifting.lean` | 3 |
| `NumberTheory/FrobeniusDensity/Basic.lean` | 3 |
| `NumberTheory/FrobeniusDensity/PrimeSumSplit.lean` | 10 |
| `NumberTheory/FrobeniusDensity/BadPrimes.lean` | 4 |
| `NumberTheory/FrobeniusDensity/StatementOfDegOneAsymptotic.lean` | 1 |
| `NumberTheory/FrobeniusDensity/DegreeOnePrimesInfinite.lean` | 2 |
| `NumberTheory/FrobeniusDensity/DegOneSumAsymptotic.lean` | 10 |
| `NumberTheory/FrobeniusDensity/DegreeOneCount.lean` | 2 |
| `GaloisRep/Prelude.lean` | 1 |
| `ModularCurve/Defs/Gamma0Away.lean` | 3 |

`Set.mem_setOf_eq` and `if_*` inside the pin comments of non-DS modules
(`WeightOne/*`, `HeckeRepresentatives`, `AtkinLehner`, …) were left untouched.
No `linter.style.haveILetI` / `unusedSectionVars` proof was changed.

### Re-verification

- `python3 spec/check_flt_statements.py` → **2552 identical / 0 mismatched /
  0 missing** (92 promoted from pin-private, 30 own-proof exempted, 2582 port
  declarations checked) — unchanged from the S8 close.
- `flock /tmp/flt_for_human.lock timeout 400 lake build` → green, **4,805 jobs**
  (wall 1 m 20 s / user 3 m 57 s / sys 1 m 26 s), including all 17 drift files
  and the promoted `Relevement`.
- consumer → exit 0 as above.

### Residual items

- The `det_eq` private copies described above (2 files, 4 lines each); safe to
  promote to `ModularForm.HeckeRepresentatives.det_eq` in a later round, but
  outside this round's edit whitelist.
- `RatCoords.exists_finset_separating` remains a deliberate two-file private
  restatement with no public home (S4's recorded policy).
- Nothing else: the slice has no `sorry`/`admit`/`axiom`, and the two stopped
  S7/S8 items (the ray-class `hfam` and the group-B continuation) are out of
  scope by design.
