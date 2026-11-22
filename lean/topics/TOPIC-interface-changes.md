# Interface changes: the port's shape where it deliberately differs from the pin

The mathematics is always the pin's. A few *interfaces* are the port's, and a module
being ported must use the port's shape instead of re-deriving the pin's: otherwise the
same lemma lands twice, differing only in how its hypotheses are packaged, and the
second copy is pure porting cost.

This file is the registry. Every deliberate departure is an entry below, with the pin
shape, the port shape, the bridges between them, and the recipe for a file that arrives
holding the pin's shape.

## Why the module is unpinned rather than `own:`-marked

`spec/decl_markers.tsv` can declare a port declaration `own:`, which exempts it
from the statement diff. That keeps the pin claimed by the module header but records
nothing about *what* changed, and it hides the departure from the porting tooling: the
next agent sees a wired module and assumes its statements are the pin's.

Instead, when an interface departs from the pin:

1. **Unpin the module.** Remove the affected `spec-pin:` lines from the port module's
   leading comment. A module with no `spec-pin:` line is not diffed by
   `spec/check_port.py`; its declarations are port-owned from then on.
2. **Park the pins.** Add those `spec-pin:` lines to
   `Reserve/ModularForms/PortOwnedSpecPins.lean`, a header-only module that declares
   nothing and only carries pin lines. Both port roots are read by the tools —
   `check_port.py` scans `("FLTForHuman", "Reserve")` and `frontier.py`'s
   `wired_sources()` walks `DEFAULT_PORT_ROOTS = (FLTForHuman, Reserve)` — so a parked
   pin still reads as *ported* and `frontier.py` will not propose it for porting again.
3. **Record the entry here**, including which port declarations now cover that pin.

A declaration whose pin genuinely has no comparable statement (a general form of the
pin's concrete copies) keeps an `own:` row: there is nothing to park.

## Parked pins

| port module | pin source parked | covered by |
|---|---|---|
| `ModularForms/QCoeff` | `Definitions/Def_FLTPrelim_Modularity.lean` | `ModularFormClass.qCoeff` |
| `ModularForms/QCoeff` | `Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean` | `UpperHalfPlane.eq_of_forall_qCoeff_eq` |
| `ModularForms/QCoeff` | `P2M/Sol/S_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean` | `hasSum_qCoeff`, `UpperHalfPlane.eq_of_forall_qCoeff_eq` |
| `ModularForms/QCoeff` | `P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean` | `ModularFormClass.qCoeff_{add,sub,const_smul}` |
| `ModularForms/QCoeffClass` | `Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean` | `ModularFormClass.eq_of_forall_qCoeff_eq` |
| `ModularForms/QCoeffClass` | `P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean` | `ModularFormClass.hasSum_qCoeff` |
| `ModularForms/Level` + `Defs/HeckeRepresentatives` | `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean` | `Level.wt`/`lift`/`IsDiamondLift`/`det_mod`/`diamondLinOne`, `HeckeRepresentatives.heckeRep`/`redMatrix`/`heckeRep_mul` |
| `ModularForms/Analytic/PeterssonHecke` | `P2M/Sol/S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean` | `Lam`/`mem_Lam`/`dvd_01_of_mem_Lam`, `gInf`/`sigP`/`gInf_coe`/`sigP_coe`/`gInf_inv_coe`/`not_dvd_n`, `exists_rr_mul_mem`/`rr_mul_rr_inv_mem` |

Both q-coefficient modules are therefore unwired: the checker no longer diffs them, and
no `own:` row is involved. The cost is stated rather than hidden — the six statements
that do still match the pin (`qCoeff`, the two equality principles, the three
coefficient-algebra lemmas) are no longer diffed either. They are listed above so a
future re-wiring knows what to re-pin.

## Entry 1 — `hF` replaces the three regularity conditions

**Status: applied, and `QCoeff` is unpinned (pins parked, see above), so the layer is
port-owned and no `own:` row is involved.** The certificate is `HasQCoeff f` (an `abbrev`, so it unfolds at
call sites), and it is already the internal currency of `hasSum_average`, `hasSum_diag`
and `hasSum_qCoeff`.

The pin carries the regularity of a function as three separate hypotheses:

```
(hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f)
```

The port carries the same information as one certificate, the *q-expansion presentation*:

```
hF : ∀ τ : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ)
```

The two are **equivalent**:

| direction | lemma | home |
|---|---|---|
| three conditions → `hF` | `hasSum_qCoeff` (mathlib `UpperHalfPlane.hasSum_qExpansion` at `one_pos`) | `QCoeff` — applied |
| `hF` → bounded at `∞` | `isBoundedAtImInfty_of_hasSum_qCoeff` (mathlib) | `QCoeff` — applied |
| `hF` → periodic on all of `ℂ` | `periodic_of_hasSum_qCoeff` | `QCoeff` — applied |
| `hF` → `MDiff` | `mdifferentiable_of_hasSum_qCoeff`, specialising `mdifferentiable_of_hasSum` | `QCoeff` — applied |
| `hF` closed under `+`, `−`, `c • ·` | `hasSum_qCoeff_add` / `_sub` / `_const_smul` | `QCoeff` — applied |

The periodicity direction is short because `ofComplex` sends the closed lower half plane
to one fixed point (`UpperHalfPlane.ofComplex_apply_of_im_nonpos`), so only points with
`0 < im` need the expansion, and there `qParam 1 (z + 1) = qParam 1 z`.

**`hF` does imply `MDiff`, and the port already proves it.** `ModularForms/QExpansionPrinciple`
carries `mdifferentiable` — a `HasSum` presentation implies `MDiff`, general in `h` — with
four private helpers beneath it (`hasSum_cuspFunction_of_hasSum_punctured`,
`hasFPowerSeriesOnBall_update`, `apply_eq_cuspFunction`,
`differentiableAt_cuspFunction_of_hasSum`), all mathlib-only. Specialising to `h = 1` and
`c = qCoeff f` is `mdifferentiable_of_hasSum_qCoeff`.

The gate was **availability, not truth**: that lemma was `private` in
`QExpansionPrinciple`, and `QCoeff` must not import that module (everything under the
floor would inherit it). It has been relocated — the four helpers
(`hasSum_cuspFunction_of_hasSum_punctured`, `hasFPowerSeriesOnBall_update`,
`apply_eq_cuspFunction`, `differentiableAt_cuspFunction_of_hasSum`) and
`mdifferentiable_of_hasSum` now sit in `QCoeff`, `QExpansionPrinciple` imports them, and
`mdifferentiable_of_hasSum_qCoeff` is the one-line specialisation to `HasQCoeff`.

With it, the closure lemmas `hasSum_qCoeff_add` / `_sub` / `_const_smul` are three lines
each: each adds the two expansions, then identifies `qCoeff (f ± g)` (resp. `c • f`) with
the summed coefficients through the coefficient algebra, whose analyticity inputs come
from the three extractions. Without the `MDiff` extraction, Lean asks for all six
regularity facts instead (probed, `tmp/hf-algebra-probe.lean`).

This unblocks the stage-3 operator transports and the Pattern-C simplifications. Flipping
the *coefficient-level* algebra to `hF` (stage 1c) still buys little on its own and is
deferred.

**Why `hF`.** It is the only packaging closed under the operations: `hF → hF (heckeU …)`,
`(heckeT …)`, `(d ⊙ ·)`, `(c • ·)`, `(· + ·)` are one lemma each, whereas the three
conditions must be transported one fact at a time and re-assembled at every site. It is
also what every consumer consumes (a `HasSum`); the three conditions are what mathlib
needs to *manufacture* one.

**Porting recipe.** A pin file states the three conditions, and that is fine — state
them where the file states regularity, then convert **once**:

```lean
have hF : ∀ τ : ℍ, HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) :=
  hasSum_qCoeff hper hhol hbdd
```

and use the port's `hF`-shaped lemmas from there. In the other direction, when a pin
target needs a single fact, extract it with the table above.

**Do not**

* re-prove a three-condition copy of a port lemma that has an `hF` form;
* write `hper hhol hbdd` at three call sites for one function — produce `hF` once;
* re-port the pin's per-file private preludes (`hasSum_qCoeff`, `eq_of_forall_qCoeff_eq`,
  `qCoeff_add` …): the pin re-proves them in many `S_` files, the port has one of each.

## Entry 2 — the q-coefficient layer is split at the instance boundary

**Status: applied.**

`ModularForms/QCoeff` is the function-level layer and mentions no
`[ModularFormClass F Γ k]` binder: `qCoeff`, the three-condition `hasSum_qCoeff`, the
function-level equality principle and algebra. `ModularForms/QCoeffClass` is the
instance-level facade on top of it: `ModularFormClass.hasSum_qCoeff` (instance → `hF` in
one step), the bundled equality principle, and the primed algebra.

**Porting recipe.** A bundled form yields its certificate directly —
`hasSum_qCoeff f hΓ` — rather than three separate facts. A file that works with bare
functions imports `QCoeff`; a file that has a `CuspForm`/`ModularForm` in hand imports
`QCoeffClass`.

**The pinned copy of the bundled producer** lives inside a `variable` section
(`P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean:166`), so the checker's stored text omits
the section binders while the port writes them out. The statement is the pin's; the pin
is parked (see above) rather than `own:`-marked.

## Entry 3 — function-level Hecke q-coefficient statements

**Status: applied (2026-11-16).** `UpperHalfPlane.qCoeff_heckeU`, `…qCoeff_heckeT` and
`…qCoeff_comp_heckeDiagMatrix_smul` take `HasQCoeff f` in place of the three conditions;
their conclusions are unchanged. `HeckeQCoeff` is unpinned as a consequence (its 15 pins
are parked, see above), and the three hF transports `hasSum_qCoeff_heckeU`,
`…_heckeT`, `…_comp_heckeDiagMatrix_smul` are the primary statements — the coefficient
identities are now two-line corollaries of them.

`UpperHalfPlane.eq_of_forall_qCoeff_eq` takes two certificates instead of six
hypotheses, and the coefficient algebra gained certificate forms
(`qCoeff_{add,sub,const_smul}_of_hasSum`) for callers that hold an `hF` rather than the
three facts. Call sites that build the conditions locally wrap them once:
`hasSum_qCoeff hper hhol hbdd`.

**Superseded note, kept for the reasoning:** the earlier plan was to apply this where it
pays rather than repo-wide, because at a call site that produces the three conditions
locally `hF` is no shorter.

`eq_of_forall_qCoeff_eq` is a clear win (proof two lines shorter, 22 call sites from six
premises to two) and is the first candidate. The *coefficient-level* algebra
(`qCoeff_{add,sub,const_smul}`) is not: its proofs need the analyticity that the three
premises supply for free, so each would grow to re-extract it, and its 31 call sites
mostly build the conditions from an instance at the call site (see Entry 4), where `hF` is
no shorter.

Apply the flip when a call site's *proof* carries the certificate rather than producing it
— the `HeckeQCoeff` internals, `Reg` and `phi_props` (Entry 4). When applied,
`QCoeff`'s pins move to `PortOwnedSpecPins` and this entry is updated.

## Entry 4 — the three production patterns at call sites

Recorded because it decides whether an `hF` flip pays. Measured over the call sites of
these lemmas (2026-11-16):

* **A — inline accessor trio from an instance.** Six accessor calls written at the call
  site, e.g. `qCoeff_add (cusp_periodic F) (cusp_holo F) (cusp_bdd F) (cusp_periodic G) …`.
  `hF` does not help here; the *bundled* primed forms (`qCoeff_add' hΓ F G n`, one
  argument) already supersede the *proofs*. Measured, and it corrects an earlier reading
  of this entry: seven of the nine per-file "concrete-spelling copy" wrappers already
  call the primed forms, and the two in `DeligneSerre/CoefficientRing` were the last ones
  still feeding the six accessors — their proofs are re-based (six hypotheses → one), but
  their *statements* must stay, because they are rewrite-shaped: the call sites `rw` on
  `qCoeff ⇑(F + G)`, while the general primed statement is `qCoeff (⇑f + ⇑g)` (it cannot
  assume `Add F`). So the wrappers are coercion adapters, not stale copies, and only the
  proofs were the duplicate.
* **B — three parallel transport haves** re-assembled at the consumer
  (`periodic_smul` / `.const_smul` / `.const_smul_left`, then six arguments). This is
  where `hF` pays, once the certificate is carried across the proof.
* **C — the triple threaded from the enclosing binder** (the five private `_bare`s in
  `HeckeCommute` / `HeckeEigenform`). `hF` reads better — the argument is "both sides are
  presented by their expansions, compare coefficients" instead of six regularity facts —
  but it needs the operator transports of stage 3 (`HasQCoeff f → HasQCoeff (heckeU k p f)`),
  which need the `MDiff` bridge.

## Entry 5 — the ad-hoc regularity packagings are gone

**Status: applied.** Two hand-rolled packagings of the three conditions existed beside the
certificate, and both were consumed only by q-coefficient reasoning:

* `Reg` (`ModularForms/NebentypusEigenbasis`) — a structure with `per`/`hol`/`bdd`, four
  producers and `Reg.analyticAt`. Replaced by `HasQCoeff`: `reg_coe` is `hasSum_qCoeff`,
  `Reg.smul` is `hasSum_qCoeff_const_smul`, `Reg.analyticAt` is
  `ModularFormClass.analyticAt_cuspFunction_zero_of_hasSum_qCoeff`, and `reg_heckeU`'s
  thirteen-line hand-rolled periodicity is `hasSum_qCoeff_heckeU`.
* `phi_props`, three times (`Analytic/HeckeEigenvalueConj`, `WeightOne/PrimitiveQCoeffNorm`,
  `HeckeNebentypusFricke`) — a 4-conjunction of the three facts plus the coefficient
  identity. Each is now a certificate plus that identity; the two call sites that already
  discarded the triple now discard one conjunct.

Consequence for future ports: do not re-port these packagings. A file that arrives with a
`Reg`-like record or a `phi_props`-like conjunction should carry `HasQCoeff` and use the
transports (`hasSum_qCoeff_{add,sub,const_smul}`, `hasSum_qCoeff_heckeU`, `_heckeT`,
`_comp_heckeDiagMatrix_smul`, `hasSum_qCoeff_slash_heckeDiagMatrix`) to build it, and the
extractions (`periodic_`, `isBoundedAtImInfty_`, `mdifferentiable_`,
`analyticAt_cuspFunction_zero_of_hasSum_qCoeff`) only where a single fact is genuinely
wanted.

## Entry 6 — the Hecke representative block is repackaged

**Status: applied, the pin's public home parked.** The pin's public block
(`Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:82–455`) and the two `Γ₀` `S_` copies state the
`U_p`/`T_p` bookkeeping in the shape their own proofs needed. The port states it in the shape the
level argument needs. The block's public home is parked (it is split over three port modules and
cannot be a wire for any of them); the two `Γ₀` `S_` copies keep their existing wire in
`ModularForms/HeckeInvariance.lean`, and the one declaration there that departs from the pin,
`heckeMatrix_mul_of_dvd`, is the one described below.

**Pin shape.** `isUnit_wt {N} (hp : p.Prime) (hpN : ¬ p ∣ N) (x)`;
`heckeMatrix_mul_of_eq (g) (j j' : ℕ) (e : ℤ) {he}` concluding
`∃ g', g' 1 0 = p * g 1 0 ∧ g' 1 1 = g 1 1 - g 1 0 * j' ∧ …`; and
`heckeMatrix_mul_of_dvd (g) (hc : (p : ℤ) ∣ g 1 0) (x)` concluding
`∃ g', g' 1 0 = p * g 1 0 ∧ heckeMatrix p x.val * mapGL ℝ g = mapGL ℝ g' * heckeMatrix p (affinePerm g _ x).val`.
The `heckeT` `S_` copy states `heckeRep_mul` with `hg : (N : ℤ) ∣ g 1 0` and only the
multiplication conjunct.

**Port shape.** `Level.isUnit_wt {N} (hpN : ¬ p ∣ N) (x)` under `[Fact p.Prime]`;
`HeckeRepresentatives.heckeMatrix_mul_of_dvd (g) (M : ℕ) (hpM : p ∣ M) (hg : (M : ℤ) ∣ g 1 0) (x)`
concluding `∃ g', g' ∈ Γ₀ (p * M) ∧ … heckeMatrix p (affineMap g x).val`; and the public `Γ₀`
`heckeRep_mul` (`Gamma1Hecke.heckeRep_mul`) with `hg : g ∈ Γ₀ N`, which additionally records the
witness's `1 1` entry and the `wt`-equation.

The pin's other three `_mul_of_eq` corners (`_of_eq'`, `heckeDiagMatrix_mul_of_eq`, `…_of_eq'`) are
not carried: they were proof steps of the pin's own `heckeRep_mul`, and the port's `heckeRep_mul`
now reads the same two entries off `repMatrix_mul`'s fixed witness, so only `heckeMatrix_mul_of_eq`
— the shape the `Γ₀` invariance layer and `Gamma1CuspStructure` consume — stays as the facade.

**Representation.** The block is stated over `OnePoint (ZMod p)` throughout — one index type, no
lift. The four label transitions are stated once, as `dvd_conjugate` (the cocycle entry is divisible
by `p` when the target label is the image of the source label), so `heckeRep_mul` has no case split:
its level and weight conjuncts are the `1 0` and `1 1` entries of the coset identity turned into unit
cancellations (`isUnit_wt` for the weight factor, `ZMod.isUnit_prime_of_not_dvd` for the `p` the
representative carries).

The pin's `ℕ`-labelled `heckeMatrix_mul_of_eq` becomes label-stated: `(j j' : ZMod p)` and the
cocycle hypothesis is an identity in `ZMod p`, so **the pin's quotient `e` disappears** — the pin's
`p * e` term is zero there. Its consumers already held labels (`x : ZMod ℓ`,
`y := affinePerm g _ x`) and only converted with `.val` to reach the pin's signature, so they lost
their quotient and cast plumbing (see `topics/hecke/TOPIC-representation-survey.md`); the entry
conjunct reads `g' 1 1 = g 1 1 - g 1 0 * j'.val`. `heckeMatrix_mul_of_dvd` keeps the pin's argument
shape (`x : ZMod p`) and its `.val` conclusion, as does `heckeRep_mul`.

**Bridges.** Primality: `have : Fact p.Prime := ⟨hp⟩`. The level packaging: the `1 0` entry of the
witness is `p * g 1 0` and the level is `Γ₀(p * M)`, so the pin's conjunct is read off the witness
(`repMatrix_mul`'s explicit `hW`); the label is `affineMap g x`, which is `redMatrix p g • x` on
`Γ₀(p)` (`affineMap_eq_smul_redMatrix`), hence `affinePerm`'s value there. The `Γ₁` form of
`heckeRep_mul` (no extra `g 1 1` factor on the `wt` equation) is `HeckeGamma1.heckeRep_mul`, a
corollary of the `Γ₀` statement.

**Port-owned declarations with no pin counterpart** (nothing to park, and no `own:` row while the
modules are on the frozen checker): `affineMap`, `affinePerm`, `affineMap_apply`,
`affineMap_eq_smul_redMatrix`, `exists_sl2_of_isCoprime`, `exists_diamondLift`,
`unit_of_apply_one_zero_eq_zero`, and the integral coset layer `repMatrix` / `conjugate` /
`clearedWitness` / `repMatrix_mul`.

**Recipe for a file arriving with the pin's shape.** Take `heckeMatrix_mul_of_dvd`'s pin form from
`repMatrix_mul` (`Defs/HeckeRepresentatives.lean`) instead of a fresh entry chase; take the `Γ₀`
`heckeRep_mul` from `Gamma1Hecke.heckeRep_mul` and the `Γ₁` one from `HeckeGamma1.heckeRep_mul`;
build any `Γ₀`-lift with a prescribed `1 1`-entry from `Level.exists_sl2_of_isCoprime` rather than
from a local Bézout matrix.

## Entry 7 — the Hecke adjointness engine is port-owned

**Status: applied, the pin parked.** `ModularForms/Analytic/PeterssonHecke.lean` is the analytic
engine for `⟨T_p f, g⟩ = conj ε(p) ⟨f, T_p g⟩` on a nebentypus component. Its pin
(`S_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean`) states the group layer, the
Bézout lifts and two entry computations in the shape its own proof wanted; the port states them in
the shape the argument needs. None of the pin's 117 declarations is `private`, so unpinning is a
whole-module decision rather than a per-declaration one.

**Pin shape.** `def Lam (N p) : Subgroup SL(2, ℤ)` with the carrier
`{γ | γ ∈ Gamma1 N ∧ (p : ℤ) ∣ γ 0 1}` and its own `mul_mem'`/`inv_mem'`;
`def bez (hpN) : ℤ × ℤ` with `(bez hpN).1 * p - (bez hpN).2 * N = 1` and the lift matrices spelled
`!![(bez hpN).1 * p, (bez hpN).2; N, 1]` / `!![(bez hpN).1, (bez hpN).2; N, p]`;
`upperRight_T_mul`, `upperRight_gInf_mul` as named entry computations; and
`conjSL_mem_Gamma1`/`cfwd_coe` naming the divisibility witness as `hh.2` / `h.2.2`.

**Port shape.** `Lam` is `Γ₁(N) ⊓ Γ⁰(p)` — a one-line intersection of `Gamma1` and
`Level.Gamma0Upper`, so the group closure is `Subgroup.inf`'s; `mem_Lam` keeps the pin's statement
and is the single bridge to the divisibility spelling, with `dvd_01_of_mem_Lam` as the eliminator
and `Lam_le` = `inf_le_left`. The Bézout datum is `Level.BezoutPair (p : ℤ) (N : ℤ)` (one
normalization `u * p + v * N = 1`, one constructor family `mat`/`matDiag`), and the lifts are its
`matDiag`/`mat`; `bez` and `bez_spec` are gone, so `gInf_coe`/`sigP_coe` state
`!![(bezPair hpN).u * p, -(bezPair hpN).v; N, 1]` and `!![…, -(bezPair hpN).v; N, p]`,
`gInf_inv_coe` states `!![1, (bezPair hpN).v; -N, (bezPair hpN).u * p]`, and `not_dvd_n` states
`¬ (p : ℤ) ∣ (bezPair hpN).v` — the sign sits where the matrix has it instead of behind a
translation lemma. `conjSL_mem_Gamma1`/`cfwd_coe` name their witness `dvd_01_of_mem_Lam hh`, and
`upperRight_T_mul`/`upperRight_gInf_mul` are inlined as `have h01` at their single use site.

**Bridges.** `Subgroup.mem_inf` (definitional) turns `Lam`-membership into
`Γ₁ N ∧ Γ⁰(p)`; `mem_Gamma0Upper_iff_dvd` turns the `ZMod` entry condition into `(p : ℤ) ∣ γ 0 1`,
which is the whole content of `mem_Lam`. `(bezPair hpN).huv` is the Bézout relation in the port's
sign; `gInf_mem` and the `rr_mul_rr_inv_mem` branches read it with the minus of `matDiag` visible,
and `dvd_neg` moves between `p ∣ v` and `p ∣ -v` where the matrix carries the other sign.

**The duplicated layer.** The pin also wrote its admissible-function and pairing layer twice; the
port keeps one copy, in the wired `ModularForms/Analytic/PeterssonCoset.lean`. The engine's
`Adm` (identically shaped to `Nice`, field order aside), its `Adm.add/smul/neg/sub`, its own
`dens`/`dens_nonneg`/`petersson_self_eq_dens`/`continuous_dens`/`dens_smul_of_inv`, its
`unfold_sum`, and its `integral_cosum_self`/`integral_cosum_polar`/`integral_cosum_pair`
(statement-identical to the coset layer's, `Adm` vs `Nice` aside) are all gone; the engine's two
admissibility proofs now produce `Nice`, and `main` calls the coset layer's
`integral_cosum_pair`. The engine is 66 public declarations against the pin's 118.

**Recipe for a file arriving with the pin's shape.** Do not rebuild `Lam`: write
`Γ₁ N ⊓ Gamma0Upper p` and take `mem_Lam`/`dvd_01_of_mem_Lam` from this module. Do not introduce a
Bézout pair or a lift matrix: take `Level.BezoutPair` (`.huv`, `.mat`, `.matDiag`) and, for a lift
into `Γ₀` with a prescribed `1 1`-entry, `Level.exists_sl2_of_isCoprime`. Read the upper-right
entry of `gInf * γ` or `T ^ t * γ` as a local `have`, as `exists_rr_mul_mem` does.

## Entry 8 — the `ε`-eigenspace invariance is stated for the diamond-twisted `T_p`

**Status: applied, the pin parked.** `ModularForms/NebentypusEigenbasis.lean` keeps the
nebentypus eigenbasis; the invariance statement whose own pin file it used to name is proved there
for `heckeTOne`, so that pin's wire is carried by
`Reserve/ModularForms/PortOwnedSpecPins.lean` instead of the module header.

**Pin shape.** `heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0` takes a raw function
`f : ℍ → ℂ` with the pointwise nebentypus law as a hypothesis and concludes
`(heckeU k p f + ε(p) • (f ∣[k] heckeDiagMatrix p)) ∣[k] mapGL γ = ε (γ 1 1) • (…)` for
`γ ∈ Γ₀(N)`. Its proof computes the `Γ₀`-cocycle of the double coset: the `p + 1` representatives
(`sum_eq` over `OnePoint (ZMod p)`, `lift`/`redMatrix`), the reweighted sum (`sum_slash_mapGL`), and
a Bézout lift of `p` (`exists_diamondLift`).

**Port shape.** `T_p` on `Γ₁(N)` is `CuspForm.heckeTOne` (diamond-twisted, `ε`-free); its `ε`-view
is the shared `CuspForm.heckeFun = U_p + ε(p) • (· ∣[k] heckeDiagMatrix p)`. The invariance is
`SSbasis.heckeTOne_slash`:

```
⇑(heckeTOne k hp hpN f) ∣[k] mapGL γ = ε (dd γ) • ⇑(heckeTOne k hp hpN f)
```

for `f : CuspForm Γ₁(N) k` of nebentypus `ε` and `γ ∈ Γ₀(N)` — a three-line consequence of the
operator's `Γ₀`-equivariance, not a coset computation.

**Bridges.** `SSbasis.coe_heckeTOne_nebentypus : ⇑(heckeTOne k hp hpN f) = heckeFun k ε p ⇑f`
turns the port statement into the pin's, `dd γ = γ 1 1` holding definitionally. The cocycle
computation itself is not repeated: `HeckeTLinOneQCoeff.heckeTLinOne_slashOfMemGamma0` gives
`T_p (f ∣[k] γ) = (T_p f) ∣[k] γ`, and with the nebentypus law `f ∣[k] γ = ε (dd γ) • f` and
`T_p`'s `ℂ`-linearity the pin's conclusion follows. The coset layer the pin re-derives is
`CuspForm.Gamma1Hecke.sum_eq`/`sum_slash_mapGL_of_mem_Gamma0` and
`Level.exists_isDiamondLift_of_coprime`.

**A dropped pin, not a dropped statement.** The pin's declaration has no counterpart *by name*, so
`frontier.py --selfcheck` lists the node as not covered by the name scan and
`twin_scan.py --node` reads it `new` (the statement is re-spelled, not renamed). The node stays
**ported** for the frontier because its `spec-pin:` lines sit in the Reserve register; the residue
is recorded as MD-007 in `spec/METADATA-ISSUES.md`.
