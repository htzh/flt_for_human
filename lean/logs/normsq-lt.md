# The nebentypus Hecke bound — one listed module, two thirds of it already in the tree

**Status: landed 2026-10-18.** One new module, green with 0 errors and 0 warnings:
`FLTForHuman/ModularForms/Analytic/NormSqLt.lean` — 716 lines, **31 public declarations**
(the 30 new ones in namespace `CuspForm.HeckeBoundGamma1` plus the headline at
`CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`), listed, all statement-checked.

Checker **10,445 → 10,476 identical**, 0 mismatched / 0 missing (10,812 port declarations
checked): the delta **+31** is exactly this module's public surface. `#print axioms` on the
headline and on the engine's `norm_sq_lt` is `[propext, Classical.choice, Quot.sound]`. **No
existing module was edited.**

| | |
|---|---|
| headline | `CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen` |
| pin proof | `P2M/Sol/S_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean` (893 lines, 57 declarations) |
| statement authority | `Theorems/Thm_CuspForm_norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen.lean` (14 lines) |
| **net new** | **≈614 lines / 30 declarations** of 870 declaration lines — 24 declarations (≈240 lines) were already in the port and 2 more are subsumed by them |
| structure | one listed module: new engine + headline, importing the sibling's silo |
| build | tier-0 exit 0 / 0 warnings (7.2 s at the 200k cap); tier-1 3,579 jobs, 7.3 s |

## 1. The theorem, and the pair of silos

For `F ∈ S_k(Γ₁(M))` with nebentypus `ε`, `F ≠ 0`, and `a_{pn} = a·a_n` for a prime `p ∤ M`
(that is `U_p F = aF`):

```
‖a‖ ^ 2 < ((p : ℝ) + 1) ^ 2 * (p : ℝ) ^ (k - 2)
```

— the *strict* Hecke bound at a prime not dividing the level, i.e. the `(p+1)²` Cauchy–Schwarz
gain over the trivial bound, and the general companion of the exact value
`‖a‖² = p^{k-1}` that the port already carries for newforms
(`CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough`, whose set record is
[topics/deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](../topics/deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md)
§5.2 and whose order is [WORKORDER-P2-normsq.md](../topics/deligneSerre/WORKORDER-P2-normsq.md)).

**The pin has two nearly-parallel silos** for these two statements (979 and 893 lines). The port
had already homed the first as `ModularForms/Analytic/NormSqPow.lean` (namespace
`CuspForm.LiNormSq`, 76 declarations). This landing is the second, and the whole point of it is
that **the two silos share their prelude**: 24 of this silo's 57 declarations are
statement-identical to declarations already in `CuspForm.LiNormSq`.

## 2. The measurement

```bash
cd tools/deps
python3 port_advise.py --target CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen \
  --json build/nsl_advise.json
python3 port_plan.py --json build/nsl_advise.json
```

| quantity | value |
|---|---:|
| raw `S_` lines | 893 |
| declaration lines / groups | 870 / 57 |
| **already in the port (tier 1, statement-identical)** | **237 lines / 24 declarations** |
| net new math lines | ≈614 (30 declarations; 24 substituted, 2 subsumed) |

The 24 substitutions, all in `CuspForm.LiNormSq`: `Lam0`, `mem_Lam0`, `Lam0_le_Gamma1`,
`Gamma_le_Lam0`, `Gamma_le_Gamma1`, `mul_apply'`, `intCast_eq_one_iff`, `dConj`, `dConjInv`,
`dConjMat`, `dConjInvMat`, `det_dConjMat`, `det_dConjInvMat`, `dvd_10_of_mem_Lam0`,
`dvd_01_of_mem_Gamma`, `mapGL_dConj`, `mapGL_dConjInv`, `heckeDiag_mul_eq`, `heckeDiag_mul_eq'`,
`hasSum_F`, `dens_slash`, `nice_cuspForm`, `slash_eq_smul_of_hasNebentypus`,
`one_mem_strictPeriods`, plus the pin's four `scoped instance`s. The port merged the pin's
`dConjMat`/`dConjInvMat` into one declaration (same `def`), so 25 pin names map to 24 port ones.

**Two names looked like variants and are not ported at all.** `geom_sum_root` and
`qParam_heckeDiag_smul` appear in both silos, over `p` here and over `ℓ` there — but the prime is a
*section variable* in both, so the ported `CuspForm.LiNormSq` declarations are the same universally
quantified statements (`∀ {ℓ}, ℓ ≠ 0 → …`) and serve this silo directly at `ℓ := p`:

```lean
example (p : ℕ) (hp : p ≠ 0) (n : ℕ) :
    ∑ u ∈ Finset.range p, (Complex.exp (2 * Real.pi * Complex.I / p) ^ u) ^ n
      = if p ∣ n then (p : ℂ) else 0 :=
  CuspForm.LiNormSq.geom_sum_root hp n          -- typechecks as stated
```

So neither is declared here: the two consumers inside `sum_apply_heckeMatrix_smul` call the
imported lemmas (bare, through `open CuspForm.LiNormSq`; the implicit prime unifies with `p` from
the goal). That removes **19 duplicated lines** and two would-be "same name, different statement"
rows from the tree. The first landing did declare them; the review replaced them with the
substitution, which is why the final delta is +31 rather than +33.

## 3. The shape, and why nothing of the prelude was re-derived

One **listed** module: the pin's 32 new declarations in `CuspForm.HeckeBoundGamma1` (the pin's
`HeckeBoundGamma1`, prefixed like the sibling's `CuspForm.LiNormSq`), plus the headline at the
wrapper's dotted name at the root. It imports `NormSqPow.lean` and opens
`CuspForm.LiNormSq` (for the 24 names) and `open scoped CuspForm.LiNormSq` (for the four scoped
instances) — that is the whole trick: the pin's silo has its prelude in the same file, so its
proofs use those names unqualified, and the port's `open`s reproduce that.

The module is listed rather than tier 3 for the same reason as the last two sets: all 32
declarations are new, unique, and have no other consumer, so a tier-3 engine would leave them
unchecked with no importer ever to justify it.

`Gamma1_le_of_dvd` (pin 97) is worth a note: **three `private` copies already exist in the tree**
(`DeligneSerre/Lifting.lean:63` as `gamma1_le_of_dvd`,
`ModularForms/WeightOne/IntegralWeightOneForm.lean:57` and `Gamma0Integral.lean:1500` as
`Gamma1_le_of_dvd`), so this is now the fourth. It is *not* substitutable: the pin's binders are
`{N : ℕ} (h : M ∣ N)` with `M` a section variable, and the port's privates spell `{M M' : ℕ}` — a
statement-text difference the checker would flag, and private declarations are unimportable
anyway. Promoting one of the three is a later hub dedup (the `det_eq` family's sibling residual,
column note §9).

## 4. Proof adaptations (pin → v4.34.0), statements verbatim

1. `if_pos` / `if_neg` → `ite_eq_left` / `ite_eq_right` (pin 453, 457, 466, 474, 775, 782).
2. pin 768: `simp only [sM, lt_irrefl, if_false, hδ]` → `simp only [sM, ite_eq_right (lt_irrefl p), hδ]`.
   The first attempt failed as a *hard* error, not a warning: the goal still read
   `if False then T ^ p else sig0 …`, so the following `rw [← gam0_mul_heckeDiag …]` had nothing
   to rewrite; and `simp only [… ite_eq_right …]` without the hypothesis is reported as an unused
   simp argument, so the `¬ p < p` proof must be passed explicitly.
3. Two declaration-scoped `set_option linter.style.haveILetI false in` guards (pin 631, 717): the
   pin's `haveI : Fact (IsCusp OnePoint.infty (Γ₁(M)))`, `Fact p.Prime`, `Fact (p ∣ M * p)` are
   real instance arguments, not the lint's target — `have` is not a substitute. Declaration-scoped,
   as the column prefers (sibling precedent: `NormSqPow.lean:604`, `:1096`).
4. At root the engine lemma must be spelled `CuspForm.HeckeBoundGamma1.norm_sq_lt` (the pin writes
   `HeckeBoundGamma1.norm_sq_lt` from inside the namespace).

Nothing else drifted: the `SL(2, ℤ)` semireducible-`def` issue that bit P2a did not resurface,
because the pin's own `Matrix (Fin 2) (Fin 2) ℤ` ascriptions already cover it.

## 5. Verification

| check | result |
|---|---|
| tier-0 `lake env lean -DautoImplicit=false -DmaxHeartbeats=200000` | exit 0, **0 warnings** (7.2 s) — the 169-line `norm_sq_lt` fits the 200k cap, so nothing relies on the pin's 3,200,000 |
| tier-1 `flock … lake build FLTForHuman.ModularForms.Analytic.NormSqLt` | green, 3,579 jobs, 7.3 s |
| checker before | 10,445 / 0 / 0 / 42 own / 294 registered (10,781) |
| checker after | **10,476** / 0 / 0 / 42 own / 294 registered (10,812) — delta **+31** |
| `#print axioms` | headline and `norm_sq_lt`: `[propext, Classical.choice, Quot.sound]` |
| forbidden tokens | none (`sorry`/`admit`/`axiom`/`native_decide`/bare `import Mathlib`/`maxHeartbeats`) |
| register | unchanged — the module is listed, so all 33 declarations are tier 1 |
| `git status` | the new module, the order, `spec/check_flt_statements.py`, the notes |

## 6. Residuals

* `Gamma1_le_of_dvd` **is now homed**: it was five copies (one public here, one in
  `ModularCurve/X1/Defs.lean`, three `private`); the wave recorded in
  [logs/gamma1-le-of-dvd-home.md](gamma1-le-of-dvd-home.md) added the mathlib supplement
  `CongruenceSubgroup.Gamma1_le_of_dvd` (`NumberTheory/ModularForms/CongruenceSubgroupOrder.lean`),
  deleted the three private copies and made this module's declaration a one-line wrapper (its
  statement must stay the pin's `{N : ℕ} (h : M ∣ N)`).
* `geom_sum_root` / `qParam_heckeDiag_smul` are **not** duplicated: the port has one copy each (in
  `CuspForm.LiNormSq`), polymorphic in the prime, and this silo's consumers instantiate at
  `ℓ := p`. A pin reader looking for `HeckeBoundGamma1.geom_sum_root` should read that as the
  port's `CuspForm.LiNormSq.geom_sum_root` — the only difference is the bound variable's name.
* The math note `math/030-petersson-adjointness-of-hecke.md` §7 states the sibling's *equality*
  only; the strict bound's Cauchy–Schwarz residue `(p+1)²` is not written there yet.
* The `used_by` of this node is 4 whole-project dependents, 0 in the D-S cone: what it buys is the
  statement the weight-one lifting column's `U_p`-bounds cite.

## 7. Reproduce

```bash
cd lean
timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
  FLTForHuman/ModularForms/Analytic/NormSqLt.lean
flock .lake/flt_build.lock timeout 280 lake build FLTForHuman.ModularForms.Analytic.NormSqLt
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10476 identical
```
