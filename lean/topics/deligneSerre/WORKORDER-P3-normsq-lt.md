# WORKORDER-P3 — the nebentypus Hecke bound `‖a‖² < (p+1)² p^{k-2}` (one listed module)

**Status: issued 2026-10-18.** Read
[../../PORTING-DeligneSerre.md](../../PORTING-DeligneSerre.md) §3–§4,
[porting-playbook.md](../../../porting-playbook.md) §3–§5, and
[TOPIC-petersson-coset-and-level-prime-eigenvalue.md](TOPIC-petersson-coset-and-level-prime-eigenvalue.md)
— its §2–§7 are the sibling's record, and it says of this node: *"The sibling `norm_sq_lt` is a
third set, taken after P2: it reuses P1 and needs no new definition layer."*

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. The dedup finding — read this first

The pin has **two sibling silos** of the same development, and the port already has one of them:

| silo | pin lines | port home | status |
|---|---:|---|---|
| `S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean` | 979 | `ModularForms/Analytic/NormSqPow.lean` (namespace `CuspForm.LiNormSq`, 76 markers) | **landed 2026-10-18** |
| `S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean` | 893 | — | **this order** |

`port_advise` over this node: 57 declarations, **24 statement-identical to the port** (≈240
lines, all tier 1 in `CuspForm.LiNormSq`), **633 net new lines**. So this is *not* an 893-line
transcription: two thirds of its declaration surface is already built and must be **imported,
not re-proved**:

```
Lam0, mem_Lam0, Lam0_le_Gamma1, Gamma_le_Lam0, Gamma_le_Gamma1,
mul_apply', intCast_eq_one_iff,
dConj, dConjInv, dConjMat, dConjInvMat, det_dConjMat, det_dConjInvMat,
dvd_10_of_mem_Lam0, dvd_01_of_mem_Gamma, mapGL_dConj, mapGL_dConjInv,
heckeDiag_mul_eq, heckeDiag_mul_eq', hasSum_F, dens_slash, nice_cuspForm,
slash_eq_smul_of_hasNebentypus, one_mem_strictPeriods
```

plus the pin's four `scoped instance`s (`Lam0_finiteIndex`, `fintypeQuotLam0`,
`fintypeQuotGamma`, `fintypeQuotGamma1`), which the port also has in `CuspForm.LiNormSq`. Note
the port merged `dConjMat`/`dConjInvMat` into one declaration (`LiNormSq.dConjMat`) — they are
the same `def`.

**Two names that *look* like variants and must not be ported** — `geom_sum_root` and
`qParam_heckeDiag_smul`. This silo spells them over `p` and the sibling over `ℓ`, but the prime is
a *section variable* in both silos, so `CuspForm.LiNormSq`'s copies are the same universally
quantified statements and serve this silo at `ℓ := p`. **Do not declare them here**: the consumers
in `sum_apply_heckeMatrix_smul` call the imported lemmas (bare, through `open CuspForm.LiNormSq`;
the implicit prime unifies with `p` from the goal). This was corrected at review — the first
landing declared both, and the substitution removed 19 duplicated lines. The pin's
`-- pin:` markers for pin 391 / 397 consequently have no port counterpart, which is expected and
is recorded in the log.

## 2. Scope

One new file: `FLTForHuman/ModularForms/Analytic/NormSqLt.lean` — **listed** (the manager wires
`PORT_FILES` for it and puts the wrapper **first**, then the pin `S_` file, in `SOURCES`):

* namespace `CuspForm.HeckeBoundGamma1` (the pin's `HeckeBoundGamma1`, prefixed like the
  sibling's `CuspForm.LiNormSq`);
* the **32 new declarations** (§3), public at their pin names, each with a
  `-- pin: <name> (S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean:<line>)` marker;
* the **headline** at the wrapper's dotted name
  `CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`, declared at the root after
  `end CuspForm` (the `NormSqPow.lean` shape), with the wrapper's statement verbatim.

**Explicitly not this order.** Re-declaring any of the 24 substituted names (§1) — they are
imported. Any other `CuspForm` row. Any edit to an existing module: `NormSqPow.lean`,
`PeterssonCoset.lean`, `PeterssonHecke.lean`, `Defs/*` are frozen.

## 3. The 30 declarations to port, by pin section

Pin file: `P2M/Sol/S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean` (read-only at
`~/proj/fermats-last-theorem/P2M/Sol/`). The pin's own section structure is the module's:

| section | pin lines | new declarations (pin line) |
|---|---|---|
| `groups` | 22–354 | `Gamma1_le_of_dvd` (97), `delta_mul_eq` (230), `dInvEquiv` (260), `dInvEquiv_spec` (274), `conjEquiv` (280), `conjEquiv_spec` (292), `det_mapGL` (300), `coe_T_pow` (306), `heckeMatrix_eq_delta_mul` (311), `gam0` (327), `sig0` (330), `gam0_mem` (333), `gam0_apply_11` (338), `gam0_mul_heckeDiag` (342) |
| `qexp` | 356–490 | `qParam_heckeMatrix_smul` (374), `r_pow_mul` (383), `sum_apply_heckeMatrix_smul` (410), `heckeT_eq_smul` (477) — **not** `qParam_heckeDiag_smul` (391) nor `geom_sum_root` (397), which `CuspForm.LiNormSq` already provides |
| `nice` | 492–542 | `nice_slash_of_conj` (512) |
| `pairalg` | 544–608 | `pair_self_ofReal` (548), `pair_zero_right` (555), `pair_add_left'` (559), `pair_neg_left'` (565), `pair_sub_left'` (569), `pair_sub_right'` (573) |
| `decay` | 610–709 | `norm_pair_sq_le` (578), `im_heckeDiag_smul` (616), `heckeMatrix_smul_heckeDiag_smul` (622), `eq_zero_of_slash_delta_eq` (631) |
| `main` | 711–end | `norm_sq_lt` (717, 169 lines) |
| — | 886 | `solution` — **not ported**; its body is the headline's proof |

The pin's section variables are kept as written (`variable {M ℓ : ℕ}` in `groups`,
`{M : ℕ} {k : ℤ} {p : ℕ}` in `qexp`/`decay`, `{M : ℕ} {k : ℤ}` in `nice`, `(Λ : Subgroup SL(2, ℤ))
[Fintype …] {k : ℤ}` in `pairalg`).

**The headline**: `‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2)` under
`(M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0)
(hg : CuspForm.HasNebentypus ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (a : ℂ)` and the
Hecke-eigenrelation `ha`. Copy it from
`Theorems/Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean`; the proof is the
pin's `solution` body (`exact HeckeBoundGamma1.norm_sq_lt …`).

## 4. The header — get this right, it is where the first failures will be

```lean
import FLTForHuman.ModularForms.Analytic.NormSqPow
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import Mathlib.Algebra.Field.ZMod
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.ModularForms.Bounds
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter CongruenceSubgroup
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace CuspForm

namespace HeckeBoundGamma1

open CuspForm.PeterssonCoset
open CuspForm.LiNormSq            -- the 24 substitutions resolve from here
open scoped CuspForm.LiNormSq     -- the four `scoped instance`s live here
```

* `open CuspForm.LiNormSq` is what lets the 24 substituted names appear unqualified, as they do
  in the pin (where the prelude is in the same file). **First expected failure without it**:
  `unknown identifier 'Lam0'` / `'heckeDiag_mul_eq'`.
* `open scoped CuspForm.LiNormSq` activates the four `scoped instance`s; without it the first
  `Lam0`-index computation fails with `failed to synthesize FiniteIndex (Lam0 M ℓ)` (and
  `Fintype (SL(2, ℤ) ⧸ Lam0 M ℓ)`).
* `open scoped MatrixGroups` is in the pin's own `open scoped` line and is needed for `Γ₁(M)`.
  `SL(2, ℤ)` is a semireducible `def` in `v4.34.0` (the P2a drift) — if a `Matrix` coercion stops
  synthesizing, state the `Matrix` type explicitly in the `show`, never change the statement.

## 5. What is already in the port — import, never re-prove

The 24 names of §1 in `FLTForHuman/ModularForms/Analytic/NormSqPow.lean` (namespace
`CuspForm.LiNormSq`). Read each one there before use (they are the sibling's copies, statements
the pin's); if one is missing or differs, **stop and report** rather than re-derive it.

Also already in the tree and to be imported, not re-derived: the coset layer
`CuspForm.PeterssonCoset` (`pair`, `Nice`, `cosum`, `dens`, `unfold_sum`, …) — the pin's
`Definition` import for it.

`Gamma1_le_of_dvd` (pin 97): this order declared it locally (the pin's binders here are
`{N : ℕ} (h : M ∣ N)` with `M` a section variable, and the port's three `private` copies spelled
`{M M' : ℕ}`, so a substitution was a statement-text mismatch). **Since resolved at the source:**
the follow-up wave [logs/gamma1-le-of-dvd-home.md](../../logs/gamma1-le-of-dvd-home.md) homed the
general `CongruenceSubgroup.Gamma1_le_of_dvd` in
`NumberTheory/ModularForms/CongruenceSubgroupOrder.lean`, deleted the three `private` copies and
turned this module's declaration into a one-line wrapper at the pin's text.

Likewise `conjEquiv` exists in the port as `CuspForm.PeterssonHecke.conjEquiv` with a **different
statement** (`Lam N p ≃ Lam N p` under `hpN : Nat.Coprime p N`); this silo's `conjEquiv` is its own
and goes in `CuspForm.HeckeBoundGamma1`. The `-- pin:` markers are what keep the checker from
matching the wrong twin.

## 6. Build discipline (copy in, verbatim)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the cap is
> **low on purpose**: a declaration that exceeds it has an instance-inference defect. Diagnose
> it (`set_option diagnostics true`, `trace.Meta.synthInstance true` on that one declaration, in
> a scratch copy under `tmp/`), fix the inference, re-run. Never raise `maxHeartbeats`, never add
> a module `set_option maxHeartbeats` (the pin's `3200000` is **not** carried). When the file is
> done, `flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.ModularForms.Analytic.NormSqLt`.
> **Never a bare whole-tree `lake build`.**

**Hub prohibition.** Do not edit `NormSqPow.lean`, `PeterssonCoset.lean`, `PeterssonHecke*.lean`,
`Defs/*`, or any other existing module. If a promotion seems needed, **stop and report** with the
declaration, host and `build_ladder.py --edit` price.

**Heartbeat risk.** The pin sets `maxHeartbeats 3200000`; the expensive sites are `norm_sq_lt`
(169 lines), `eq_zero_of_slash_delta_eq` (86), `heckeT_eq_smul` (67) and
`sum_apply_heckeMatrix_smul` (67). Bisect a blow-up in a scratch file at the 200k cap; a genuine
blow-up is an instance-inference defect, not a budget problem.

## 7. Verification

| check | expected |
|---|---|
| tier-0 edit loop | exit 0, **0 warnings**, no `sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`set_option maxHeartbeats` |
| tier-1 `flock … lake build FLTForHuman.ModularForms.Analytic.NormSqLt` | green |
| checker before (the manager's) | 10445 identical / 0 mismatched / 0 missing / 42 own / 294 registered (10781) |
| checker after (the manager wires) | **10476** identical — delta **+31** = 30 new declarations + the headline |
| `#print axioms` on the headline | `[propext, Classical.choice, Quot.sound]` |
| `git status` | only the new module |

## 8. Report shape

1. The module path, line count, and every declaration it holds (32 + the headline).
2. The import block, with one clause per import.
3. Every proof adaptation (pin line → port spelling) with pin line numbers; say what failed first.
4. For each of the 24 substitutions you used: nothing to report if you simply used them — but say
   explicitly that no substituted name was re-declared, and list any that resolved differently from
   the pin's spelling.
5. Tier-0 and tier-1 results with wall times.
6. The pin line of every `-- pin:` marker.
7. Anything left undone, any deviation, and any place where you stopped rather than edit an
   existing module.

## 9. Results as landed (2026-10-18)

| | |
|---|---|
| module | `FLTForHuman/ModularForms/Analytic/NormSqLt.lean` — 716 lines, **31** public declarations (30 engine + the headline), listed |
| engine namespace | `CuspForm.HeckeBoundGamma1` (the pin's), sections `groups`/`qexp`/`nice`/`pairalg`/`decay`/`main` |
| checker | 10,445 → **10,476 identical**, 0 mismatched / 0 missing, 10,812 checked (delta **+31**) |
| axioms | headline and `norm_sq_lt`: `[propext, Classical.choice, Quot.sound]` |
| tier-0 / tier-1 | exit 0 / **0 warnings** (7.2 s at the 200k cap); `lake build FLTForHuman.ModularForms.Analytic.NormSqLt` green, 3,579 jobs |
| register | unchanged — the module is listed |
| existing modules edited | none |

**The dedup went further than the order planned.** The 24 substituted declarations were imported, none
re-declared (the subagent's `#check` probe resolved all 24 + the 4 `scoped instance`s to
`CuspForm.LiNormSq.*`, and a textual signature diff of the 24 against *this* silo's text gave 0
differences); the port therefore carries one copy of each and the checker does not diff them
twice. The two `p`/`ℓ` variants were **not** ported at all: the prime is a section variable in both
silos, so `CuspForm.LiNormSq.geom_sum_root` / `.qParam_heckeDiag_smul` are the same universally
quantified statements, and the review re-pointed the two consumers at them (`ℓ := p` by
unification) instead of keeping a second copy — 19 lines and two near-duplicate rows removed.
The landing therefore has **30** engine declarations, not 32.

Proof adaptations, all v4.34 renames, no statement touched: `if_pos`/`if_neg` →
`ite_eq_left`/`ite_eq_right` (six sites); pin 768's `simp only [sM, lt_irrefl, if_false, hδ]` →
`simp only [sM, ite_eq_right (lt_irrefl p), hδ]` (a hard error, not a warning: the residual
`if False then …` blocked the next `rw`); two declaration-scoped `linter.style.haveILetI`
suppressions on `eq_zero_of_slash_delta_eq` and `norm_sq_lt` (those `haveI : Fact …` are real
instance arguments); and the root spelling `CuspForm.HeckeBoundGamma1.norm_sq_lt` at the headline.

Notes from the landing: `norm_pair_sq_le` sits in the pin's `pairalg` section (where it physically
is at pin 578), not in `decay` as §3's table groups it; the headline's `-- pin:` marker points at
the `Theorems/` wrapper line 14 (the `NormSqPow.lean` convention) rather than the `S_` file's
`solution`.
