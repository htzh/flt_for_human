# Work order — P2: the level-prime eigenvalue (`CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough`)

**Status: DONE (2026-10-18).** P2 landed and wired: `NormSqPow.lean`, 1,104 lines, 72
checker-visible / 76 markers, checker **9,941 → 10,013 (+72)**, 0 mismatched / 0 missing, module
build 11 s, `#print axioms` clean. The dispatch record is §6.1; the mathematics is
[math/030](../../../math/030-petersson-adjointness-of-hecke.md) §7.

**The brief as issued (2026-10-18).** Set P1, the definition layer, is **landed and green**
([TOPIC-petersson-coset-and-level-prime-eigenvalue.md](TOPIC-petersson-coset-and-level-prime-eigenvalue.md)
§5.1, module `FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean`, checker +56). This order
ports the **proof body** of the pin's silo. Method:
[porting-playbook.md](../../porting-playbook.md) §2.3–§2.6, §3.1–§3.5, §4, §5. Pin
`anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); the port's
mathlib is `v4.34.0`.

**Read, in order.** [TOPIC-petersson-coset-and-level-prime-eigenvalue.md](TOPIC-petersson-coset-and-level-prime-eigenvalue.md)
§1 (the mathematics), §2 (the pin's sections), §4 (the `pair`/`Nice` conventions), §7 (risks);
[../../../math/030-petersson-adjointness-of-hecke.md](../../../math/030-petersson-adjointness-of-hecke.md)
§2 and §7; `FLTForHuman/ModularForms/Analytic/PeterssonCoset.lean` (the API you import — read
its declarations, do not re-derive them); `spec/old_check_stmts.py` (only to know what the
manager will wire — do not edit it).

**Two instructions that shape this order.**

1. **Iterate at a low cap to bring build time down.** The pin carries
   `set_option maxHeartbeats 3200000`; it is **not** carried. Every declaration must fit the
   default loop (`-DmaxHeartbeats=200000`, `timeout 60`). Restructure a slow proof (factor
   helpers, cut `simp`/`ring` blow-ups, name the intermediate terms) rather than raise the cap.
   Report each declaration's measured cost as you go, not only at the end.
2. **Report problems at the first belief.** If a name cannot be matched, a prerequisite is
   unported, an existing module would need an edit, or a declaration cannot be brought under
   the cap, **stop and report** — do not work around it, do not edit landed modules.

## 0. Scope

Port the pin's proof body whole:

| pin slice | lines | declarations | goes to |
|---|---:|---:|---|
| `section groups` (`P2/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean:22–498`) | 476 | 48 checker-visible (52 with the four `scoped instance`s) | `CuspForm.LiNormSq` in the new module |
| `section qexp` (`:500–599`) | 99 | 7 | idem |
| `section main` (`:601–962`) | 361 | 16 | idem, including `norm_sq_eq` |
| header + `solution` (`:1–21`, `:964–979`) | — | — | not ported |

New module `FLTForHuman/ModularForms/Analytic/NormSqPow.lean`, namespace `CuspForm.LiNormSq`
(the pin's sub-namespace, so the checker's dotted fallback keeps matching), plus the headline in
namespace `CuspForm` (§1).

Hard rules:

* **Public at the pin's names**, exactly its statements. The pin has **no `private`**
  declaration; do not demote one and do not add helpers of your own beyond `private` ones (a
  `private` helper is never diffed, so it is allowed, but the 71 pin declarations stay public).
* Every public declaration carries `-- pin: <name> (S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean:<line>)`
  on the line above it. That includes the pin's four `scoped instance`s (:97, :102, :106, :110):
  they are public API, even though the checker's `DECL_RE` cannot see a `scoped` declaration and
  the register therefore skips them (a known parser gap, `CARRY-FORWARD.md` tool hazards). The
  counts are therefore **76 `-- pin:` markers** for **72 checker-visible** declarations — the
  checker's delta is +72, and the four instances are documented by their markers alone.
* Keep binders exactly as the pin spells them (`autoImplicit` is off both sides), keep `scoped`
  where the pin has it, and do not rename anything.
* No `sorry`/`admit`/`axiom`/`native_decide`, no `import Mathlib`, no file-wide
  `set_option linter.*` / `maxHeartbeats`. A narrow `set_option linter.style.haveILetI false in`
  on a single declaration is acceptable **only** when the instance is load-bearing, with a
  comment saying why (the sibling module does this once, on `cosum_eq_relIndex_mul`).

## 1. The public target — statement verbatim

```lean
theorem CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓM : ℓ ∣ M) (hε : ¬ ε.FactorsThrough (M / ℓ)) (g : CuspForm (Gamma1 M) k) (hg0 : g ≠ 0)
    (hg : CuspForm.HasNebentypus ε g) (a : ℂ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff g (ℓ * n) = a * ModularFormClass.qCoeff g n) :
    ‖a‖ ^ 2 = (ℓ : ℝ) ^ (k - 1)
```

The pin's `solution` is the only statement of the wrapper file
(`Theorems/Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean`) and is the
diff authority; `solution` is a `p2m_reactivate` forwarder and is **not** ported. Prove the
headline as the two `haveI`s plus `LiNormSq.norm_sq_eq hℓM ε g hg hε hg0 a ha`, the way the pin
forwards.

## 2. Home and imports

`import FLTForHuman.ModularForms.Analytic.PeterssonCoset` (the `Nice`/`pair` layer),
`import FLTForHuman.AutomorphicForm.UpperHalfPlane.ModularFundamentalDomain` (`goodSet`,
`tsum_indicator_smul_fd`), `import FLTForHuman.ModularForms.Defs.HeckeOperator`
(`heckeDiagMatrix`, `slash_heckeDiagMatrix_apply`), `import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1`
(`CuspForm (Gamma1 M) k`, `HasNebentypus`), plus the specific mathlib modules the proof needs
(`Mathlib.NumberTheory.ModularForms.Bounds`, `Mathlib.Analysis.Complex.Basic`, …). Add imports
one at a time as they are needed; do not bulk-import.

Names to `#check` before writing the first wave: `CuspForm.PeterssonCoset.{pair, Nice, pair_slash,
pair_eq_relIndex_mul, pair_self_eq_lintegral, eq_zero_of_pair_self_eq_zero, dens, cosum,
card_quotient_eq_of_conj, unfold_sum, goodSet?}` — `goodSet`/`tsum_indicator_smul_fd` are in
`FLT.ModularFundamentalDomain`. Then `heckeDiagMatrix`, `slash_heckeDiagMatrix_apply`,
`CuspForm.HasNebentypus`, `qExpansion`, `Function.Periodic.qParam`, `upperTriangularGL`,
`ModularGroup.T`, `ZMod.val_cast_of_lt`, `Finset.sum_nbij'`.

## 3. Waves and order

**P2a — `groups`** (46 declarations, 476 lines; `:22–498`). `mul_apply'`, `intCast_eq_one_iff`,
the subgroup `Lam0` and its membership/lemmas, `tGL` and its additive/coset lemmas, `tConjMat`/
`tConj`/`tEquiv`, `dConjMat`/`dConj`/`dEquiv`, `lowSL`, `lowEquiv` and the `heckeDiagMatrix`
commutation lemmas. Self-contained `SL(2, ℤ)` bookkeeping; it does not need the analytic layer.
Dispatch it alone if you prefer two sittings.

**P2b — `qexp`** (7 declarations, 99 lines; `:500–599`). `one_mem_strictPeriods`, `hasSum_F`,
the `qParam` transformations under `tGL` and `heckeDiagMatrix`, `geom_sum_root`,
`sum_apply_tGL_smul`, `sum_slash_tGL` — over mathlib's `qExpansion`.

**P2c — `main`** (16 declarations, 361 lines; `:601–962`). `dens_slash`, `nice_cuspForm`/
`nice_slash_tGL`, `pair_slash_tGL_tGL`, `exists_lowCocycle`, `slash_eq_smul_of_hasNebentypus`,
`exists_unit_of_not_factorsThrough`, `charStep_arith`, `phi`, `phi_mul`, `sum_range_eq_sum_zmod`,
then `norm_sq_eq` — **this is where the pin's 3.2M heartbeats sit**, and where the low-cap
discipline matters. Math §7.4's two computations of `⟨V,V⟩` are the expensive chain; factor the
intermediate identities as `have`s and keep each `have` small.

**P2d — the headline** (§1), in namespace `CuspForm`, at the end of the module.

## 4. Build discipline

* Edit loop, per declaration or per small group:
  `timeout 60 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularForms/Analytic/NormSqPow.lean`
  (the file grows wave by wave). Measure wall time; a declaration that takes more than a few
  seconds is a warning sign, one that times out is a blow-up to bisect.
* Module: `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.ModularForms.Analytic.NormSqPow`.
  **No whole-tree build.**
* A blow-up is bisected (comment the declaration out, reproduce in a scratch file), never
  "fixed" by raising `maxHeartbeats`/`maxRecDepth`. Distinguish a real blow-up (high user CPU)
  from lock contention (~0 CPU).
* If the file becomes slow to re-check, split the waves into a temporary second file and merge
  once green — but do not leave a second module behind.

## 5. Reporting

Send a short report at each of these points, and stop if any of them is a blocker:

1. after `#check`-ing the P1 API and the ported vocabulary — list any name that is **not**
   available (that is a blocker for the manager, do not substitute silently);
2. after P2a builds (declarations done, wall time, any adaptation made);
3. after P2b builds;
4. after P2c builds, with the per-declaration costs of the expensive `main` lemmas and the
   headline;
5. at the end, with the verification numbers of §6.

Report **at first belief** that a prerequisite is unported, a name cannot be matched, an
existing module would need an edit, or a declaration cannot be brought under the 200k cap.
In those cases stop and hand the diagnosis to the manager; do not edit `spec/`, `CARRY-FORWARD.md`,
`topics/`, `math/`, or any landed module (the checker wiring and the register are the manager's).

## 6. Verification to run before reporting done

```sh
cd lean
# the module at the cap (and the module build)
timeout 60 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 \
    FLTForHuman/ModularForms/Analytic/NormSqPow.lean
flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.ModularForms.Analytic.NormSqPow
# the headline's axioms
printf 'import FLTForHuman.ModularForms.Analytic.NormSqPow\n#print axioms CuspForm.norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough\n' > /tmp/ax.lean
lake env lean /tmp/ax.lean     # expect [propext, Classical.choice, Quot.sound]
# sweep
grep -nE "sorry|admit|^axiom|native_decide|import Mathlib|maxHeartbeats" \
    FLTForHuman/ModularForms/Analytic/NormSqPow.lean
# counts: 72 checker-visible declarations + 4 scoped instances = 76 markers; no `solution`
grep -c "^-- pin:" FLTForHuman/ModularForms/Analytic/NormSqPow.lean
```

Report: the 72 checker-visible / 76-marker counts, the module build time, the axiom list, and
the sweep's result.

## 6.1 `v4.34.0` vocabulary notes (checked on dispatch)

All confirmed present; the four that need care:

* `qExpansion` is mathlib's `UpperHalfPlane.qExpansion : ℝ → (ℍ → ℂ) → PowerSeries ℂ`; the pin's
  v4.33 `ModularFormClass.qExpansion` no longer exists. The pin writes `qExpansion 1 F` inside
  `open UpperHalfPlane`, so the statement text is unchanged;
  `UpperHalfPlane.hasSum_qExpansion` keeps the pin's signature.
* `upperTriangularGL` / `val_upperTriangularGL` are **ours** (`ModularForms/Defs/HeckeOperator.lean`,
  namespace `ModularForm`), not mathlib.
* `IsCongruenceSubgroup` is a def (`∃ N, N ≠ 0 ∧ Γ(N) ≤ Γ`), so the pin's anonymous-constructor
  instances still elaborate.
* **`Matrix.SpecialLinearGroup` is a semireducible `def`** (a `Subtype`) in v4.34: an anonymous
  `⟨dConjMat ℓ γ, ⋯⟩` written inside a `Subgroup`-membership goal elaborates at
  `{A // A.det = 1}` and the next `rw [Gamma_mem]` fails ("not type-correct under the implicit
  transparency level"). Fix in `dConj`/`dConjInv`: bind it — `let x : SL(2, ℤ) := ⟨…⟩` — then
  `rw [Gamma_mem]`/`rw [mem_Lam0]` and `show` the entrywise conjunction. Recorded in
  [porting-playbook.md](../../porting-playbook.md) §7. (`tConj`, `tEquiv`, `dEquiv`, `lowEquiv`
  keep the pin's anonymous constructors: their expected type is `SL(2, ℤ)` itself.)
* Deprecations met in P2a: `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `if_pos` → `ite_eq_left`
  (same as P1). A narrow `set_option linter.unusedVariables false in` on `tConjMat` and
  `exact_divs` (the pin binds `M`/`hℓ` unused; the binders are statement text, so they cannot be
  renamed). `tGL_add`'s `<;> ring` became `all_goals ring`; `heckeDiag_mul_eq'`'s last
  `linear_combination` branch is unreachable in v4.34 and was dropped.

* `ModularGroup.T`, `Gamma1_mem`, `Gamma_mem`, `strictPeriods_Gamma1`, `IsCusp`,
  `CuspForm.holo'`, `ModularFormClass.bdd_at_infty`,
  `SlashInvariantFormClass.periodic_comp_ofComplex`, `CuspForm.HasNebentypus`,
  `DirichletCharacter.FactorsThrough`, `ZMod.val_cast_of_lt`, `Finset.sum_nbij'`,
  `Function.Periodic.qParam`, `slash_heckeDiagMatrix_apply`, `ModularForm.slash_apply`,
  `UpperHalfPlane.{coe_smul_of_det_pos, coe_vadd, σ}`, `geom_sum_eq`, `HasSum.unique`,
  `hasSum_sum`, `Function.Injective.hasSum_iff`, `Int.mul_ediv_cancel'`,
  `ZMod.intCast_eq_intCast_iff_dvd_sub` — all present.

**Landed so far.** P2a (`groups`) and P2b (`qexp`) are in: **697 lines, 59 markers** (48 + 7
checker-visible + the 4 `scoped instance`s), edit loop 0 errors / 0 warnings at 200k, module
build **7.1 s** (3,576 jobs). Slowest so far: `heckeDiag_mul_eq`/`heckeDiag_mul_eq'` ≈1 s each;
every `qexp` declaration well under a second, all seven the pin's proofs verbatim.

`qexp` added three adaptations: `hasSum_F` needs the narrow
`set_option linter.style.haveILetI false in` (its `haveI : Fact (IsCusp OnePoint.infty (Γ₁(M)))`
is the instance argument of `ModularFormClass.bdd_at_infty`); `sum_apply_tGL_smul` uses
`if_pos` → `ite_eq_left` and `if_neg` → `ite_eq_right`; the pin's `local notation "Γ₁(" M ")"`
(for the `Subgroup SL(2,ℤ)` → `Subgroup (GL (Fin 2) ℝ)` coercion through `mapGL`) elaborates
unchanged in v4.34, and `qExpansion 1 F` resolves to `UpperHalfPlane.qExpansion` as predicted.


**The one `main` blocker, resolved (option A).** `norm_sq_eq` needs
`ModularForm.det_heckeDiagMatrix{,_pos}`, public in the pin
(`Def_ModularForm_HeckeOperator.lean`:40 / :49) but `private` in the landed
`Defs/HeckeOperator.lean`. The manager promoted the whole privatized family —
`heckeMatrix_zero`, `heckeDiagMatrix_zero`, `det_heckeMatrix`, `det_heckeDiagMatrix`,
`det_heckeMatrix_pos`, `det_heckeDiagMatrix_pos`, `denom_heckeMatrix`,
`denom_heckeDiagMatrix` — which the checker diffs as **+8 identical (9,933 → 9,941, 0 mismatched /
0 missing)**, and dropped the engine's local `det_heckeMatrix` copy. Use the pin's names; no
local copies.

## 7. The pin, line ranges, and the mathematics

The pin is public at
`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean`
(and cloned at `~/proj/fermats-last-theorem`). Work section by section; do not read the whole
file at once. The wrapper is
`…/Theorems/Thm_CuspForm_norm_sq_eq_pow_of_qCoeff_mul_eq_of_not_factorsThrough.lean` (19 lines).

The mathematics — the four steps of math/030 §7 — is the map for the `main` section:

1. `Λ₀ = Lam0 M ℓ` (the `Γ₁(M)` matrices with `(M/ℓ) ∣ b`, `(Mℓ) ∣ c`), `Γ(Mℓ) ⊆ Λ₀ ⊆ Γ₁(M)`,
   and `heckeDiagMatrix ℓ` conjugates `Λ₀` onto `Γ(M)` (`dEquiv`);
2. `∑_{u<ℓ} F∣[k] tGL ℓ u = a·ℓ^{2-k}•(F∣[k] heckeDiagMatrix ℓ)` from `a_{ℓn} = a a_n` and
   the `ℓ`-th root of unity sum;
3. the character conjugate `Φ(wd) = ε(d)·Φ(w)` for `Φ w = pair Λ₀ k (F∣tGL ℓ w) F`, using
   `exists_unit_of_not_factorsThrough` and `exists_lowCocycle`; the nonzero residues sum to `0`;
4. `pair Λ₀ k V V = ℓ·P` by (3) and `pair Λ₀ k V V = |a|² ℓ^{2-k} P` by (2) with `pair_slash`
   at `heckeDiagMatrix ℓ` and the index equality (`card_quotient_eq_of_conj`); cancel `P ≠ 0`.

## 8. What not to do

* Do not re-derive `Nice`, `pair`, `pair_slash`, `pair_eq_relIndex_mul`, `cosum`, `dens`,
  `card_quotient_eq_of_conj`, `unfold_sum` — import `PeterssonCoset`. A second copy is the
  failure mode the parent topic exists to prevent.
* Do not change a statement to make a proof work (the port adapts proofs, never statements); if
  a statement seems wrong, report it.
* Do not carry the pin's `maxHeartbeats`, `p2m_reactivate`, `p2m_exact_reverting`, or its
  `attribute [-instance]` block; do not port `solution`.
* Do not touch the checker, the register, `CARRY-FORWARD.md`, the topic files, or any landed
  module. Do not commit.
