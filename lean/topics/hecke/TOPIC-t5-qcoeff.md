# Topic 5: the `q`-coefficient layer

**Status: planned (not started).** First topic of [SET-3](SET-3.md). SET 2 ported
the analytic head of the pin's 353-line block; this topic ports its **tail** once
(`qExpansion_coeff_unique'` … `qCoeff_heckeU/T_bare/class`), adds the formal
`PowerSeries` Hecke operators the `qExpansion` statements are phrased against, and
lands the `qCoeff`/`qExpansion` targets — the highest-indegree surface left
(`ModularFormClass.qCoeff_heckeU` indeg **59**,
`ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` **58**,
`UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul` **57**,
`ModularFormClass.qCoeff_heckeT` **35**).

**Audience.** A fresh session taking the first SET-3 topic. Read
[SET-3.md](SET-3.md) §0–§3; `HeckeAnalytic.lean`; the pin's
`P2M/Sol/S_ModularForm_mdifferentiable_heckeU.lean` lines 156–345 (the tail);
`Definitions/Def_PowerSeries_FormalHeckeOperators.lean`; and
[porting-playbook.md](../../porting-playbook.md) §3, §7.

**Goal.** Two new modules:

- `FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean` — the pin's
  `PowerSeries.heckeU`/`heckeV`/`heckeU_heckeV`/`heckeT`/`coeff_heckeT`
  (43 lines, 5 decls), verbatim.
- `FLTForHuman/ModularForms/HeckeQCoeff.lean` — the shared tail once, and the
  targets below verbatim from their wrappers.

## 1. Why this topic, and what is settled

- **It is the other half of the ten-file block.** SET 2 ported `HeckeAnalytic.lean`
  from the head (pin 23–154). The tail (158–345) is byte-identical across the
  four `q`-coefficient 353-line files; port it once. After this, the pin's ten
  copies become two port modules.
- **The formal operators are missing from the port.** `qExpansion_heckeU_eq_heckeU`
  is stated against `PowerSeries.heckeU`, which the port does not have; port the
  pin's 43-line definition module first. `heckeU_heckeV : heckeU ℓ (heckeV ℓ f) = f`
  is the only proof there.
- **The tail's dependencies are measured.** The SET-2 hand-off checked that the
  pin's tail references only the *public* `mdifferentiable_heckeU/T` (SET 2) and
  T1's `heckeU_apply`/`heckeT_apply` — not the private `heckeMatrix_one_zero`
  helpers or the `vadd` machinery. So no further promotion is needed from SET 2.
- **`qExpansion_coeff_unique'` is the historical stall site.** The playbook
  (§3.6) records `UpperHalfPlane.qExpansion_coeff_unique` costing 5.1M
  `DFunLike.coe` reductions at a bare `ℍ → ℂ`; the pin's primed version is stated
  over `ℍ → ℂ` with a `Continuous` hypothesis, which is the fixed shape. Keep it;
  do not restate over a `FunLike` type.
- **Two targets are their own small blocks.** `UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul`
  and `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` are 120-line files with
  a shared `if d ∣ n` dilation argument; port the argument once and let both
  wrap it.

**Settled: the coefficient algebra comes along.** `ModularForm.coeffHeckeT_comm`,
`coeffHeckeU_comm`, `coeffHeckeT_coeffHeckeU_comm`, `coeffHeckeT_int`,
`coeffHeckeU_int` depend only on `Defs/HeckeOperator` and are the algebraic face
of the coefficient maps; put them in `HeckeQCoeff.lean`. **Defer**
`coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one` and
`eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero` to SET 4 (the eigenform
interface).

**Settled: the `qCoeff`-uniqueness lemma comes along.** `UpperHalfPlane.eq_of_forall_qCoeff_eq`
(32 lines) — two periodic, holomorphic, bounded functions with equal `qCoeff` are
equal — is the function-level uniqueness T7's commutations close with. It is
`qCoeff` vocabulary, so it lives in `HeckeQCoeff.lean`; T5 lands it even though
T5's own targets do not use it, because porting it in T7 would mix the coefficient
and commutation layers.

## 2. The scouted inventory

| target | pin file (lines) | indeg | module |
|---|---|---|---|
| `PowerSeries.heckeU`, `heckeV`, `heckeU_heckeV`, `heckeT`, `coeff_heckeT` | `Def_PowerSeries_FormalHeckeOperators` (43) | — | `Defs/FormalHeckeOperators.lean` |
| `UpperHalfPlane.qCoeff_heckeU` | 353 (block) | 18 | `HeckeQCoeff.lean` |
| `UpperHalfPlane.qCoeff_heckeT` | 353 | 5 | `HeckeQCoeff.lean` |
| `ModularFormClass.qCoeff_heckeU` | 353 | **59** | `HeckeQCoeff.lean` |
| `ModularFormClass.qCoeff_heckeT` | 353 | **35** | `HeckeQCoeff.lean` |
| `UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul` | 120 | **57** | `HeckeQCoeff.lean` |
| `ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul` | 120 | **58** | `HeckeQCoeff.lean` |
| `ModularFormClass.qExpansion_heckeU_eq_heckeU` | 18 | 10 | `HeckeQCoeff.lean` |
| `ModularFormClass.qExpansion_heckeT_eq_heckeT` | 20 | 1 | `HeckeQCoeff.lean` |
| `ModularForm.qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne` | 110 | 18 | `HeckeQCoeff.lean` |
| `UpperHalfPlane.eq_of_forall_qCoeff_eq` | 32 | — | `HeckeQCoeff.lean` (T7 consumes it) |
| `ModularForm.coeffHeckeT_comm`, `coeffHeckeU_comm`, `coeffHeckeT_coeffHeckeU_comm` | 64/64/~60 | 2/2/— | `HeckeQCoeff.lean` |
| `ModularForm.coeffHeckeT_int`, `coeffHeckeU_int` | 19 each | 1/— | `HeckeQCoeff.lean` |

The tail's internal declarations (all block-private, port once): `qExpansion_coeff_unique'`,
`hasSum_qCoeff`, `eq_of_forall_qCoeff_eq`, `qParam_one`, `natCast_ne_zero'`,
`qParam_heckeMatrix_smul`, `qParam_heckeDiagMatrix_smul`, `exp_div_pow`,
`sum_rootOfUnity_pow`, `not_dvd_of_not_mem_range`, `hasSum_average`, `hasSum_diag`,
`hasSum_heckeU`, `hasSum_heckeT`, `qCoeff_heckeU_bare`, `qCoeff_heckeT_bare`,
`qCoeff_heckeU_class`, `qCoeff_heckeT_class`.

The key statements, verbatim from their wrappers:

```lean
theorem UpperHalfPlane.qCoeff_heckeU {f : UpperHalfPlane → ℂ}
    (hper : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1)
    (hhol : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f)
    (hbdd : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (ModularForm.heckeU k p f) n =
      ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n
theorem UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul {f : UpperHalfPlane → ℂ}
    (hper : …) (hhol : …) (hbdd : …) {d : ℕ} (hd : d ≠ 0) (n : ℕ) :
    ModularFormClass.qCoeff (fun τ ↦ f (ModularForm.heckeDiagMatrix d • τ)) n =
      if d ∣ n then ModularFormClass.qCoeff f (n / d) else 0
theorem ModularFormClass.qCoeff_comp_heckeDiagMatrix_smul {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {d : ℕ} (hd : d ≠ 0) (n : ℕ) : …
```

Route notes:

- **Port `Defs/FormalHeckeOperators.lean` first.** `heckeU ℓ` is the linear map
  `f ↦ ∑ n, f (nℓ) X^n` (`PowerSeries` coefficient substitution), `heckeV ℓ` the
  dilation `X^n ↦ X^{nℓ}`, `heckeT ℓ k := heckeU ℓ + ℓ^{k-1} • heckeV ℓ`, and
  `heckeU_heckeV` is the one proof. Definitions-level, no wrapper, verified by
  name.
- The tail's spine is `hasSum_average` (the root-of-unity filter:
  `∑_j f(heckeMatrix p j • τ)` is the `p`-fold average) and `hasSum_diag`; the
  `qCoeff_*_bare` lemmas read coefficients off, and the `_class` lemmas lift to
  `ModularFormClass` with `hΓ : (1:ℝ) ∈ Γ.strictPeriods`.
- `qExpansion_heckeU_eq_heckeU` then identifies `qExpansion 1 (heckeU k p f)` with
  `PowerSeries.heckeU p (qExpansion 1 f)`; `qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`
  identifies the diagonal translate with the port's `ModularCurve.qExpand ℂ N`
  (already in `ModularCurve/Defs/Laurent.lean`).
- The dilation pair (`*_comp_heckeDiagMatrix_smul`) is `if d ∣ n then a (n/d) else 0`
  and does not need the `HeckeAnalytic` head; its 120-line block is independent.
- The coefficient-algebra wrappers are `Defs/HeckeOperator`-only and short;
  `coeffHeckeT_int` needs `hk : 1 ≤ k` (`p^{k-1}` integral).

## 3. What is different about this topic

- **Four-file tail dedup plus a definitions port.** Two distinct chores in one
  topic: the tail once, and the missing `PowerSeries` module. Do the definitions
  module first so the `qExpansion` statements typecheck.
- **High indegree, so statement fidelity matters most.** These are the most-used
  Hecke declarations in the pin's cone (59/58/57/35); the checker is the guard.
- **`qExpansion_coeff_unique'` is a known blow-up shape.** Keep the pin's
  `ℍ → ℂ` statement and `Continuous` hypothesis; if it stalls, that is a
  quarantine-and-bisect, not a `maxHeartbeats` bump.
- **Do not port the eigen interface.** `coeffHecke_eigenvalue_…` and
  `IsNormalizedEigenform` are SET 4.

## 4. Budget

**2 goal rounds, checkpoint at 1.** Round 1: `Defs/FormalHeckeOperators.lean` and
the tail (`hasSum_*` → `qCoeff_*_class`) in `HeckeQCoeff.lean`. Round 2: the
`qCoeff`/`qExpansion` wrappers, the dilation pair, the coefficient algebra, and
the bookkeeping. The only shape risk is the `qExpansion_coeff_unique'` defeq.

**Stop early on**: a target that will not match its wrapper; the tail needing a
private helper from `HeckeAnalytic` (it should not — the hand-off measured this);
or `PowerSeries.heckeT`'s `ℕ`-valued `k` conflicting with the `ℤ`-valued `k` of
the surface Hecke operators (the pin's `heckeT (ℓ k : ℕ)` is a *different* `k`;
keep the pin's types and note the clash in the header).

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **772 identical (53 promoted), 0 mismatched, 0 missing, 14 own-proof**;
full `lake build` exit 0 (4048 jobs), 0 warnings, no `sorry`; `#print axioms`
clean on the T5 headlines. The reviewer also re-ran the checker with a
deliberately corrupted statement and confirmed it still reports exactly one
mismatch (the checker's own T5 extension is statement-exact, not a relaxation).

- [x] `FLTForHuman/ModularForms/Defs/FormalHeckeOperators.lean` created, verbatim.
- [x] `FLTForHuman/ModularForms/HeckeQCoeff.lean` created: the tail once (private),
      the targets above verbatim from their wrappers.
- [x] `grep -c` shows the tail exists in exactly one port module; the four
      353-line pin files are covered.
- [x] `timeout 600 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the T5 wrappers appended to `SOURCES`, both new modules to
      `PORT_FILES`, **0 mismatched, 0 missing**.
- [x] `#print axioms` on the T5 targets clean.
- [x] `logs/hecke-port.md` §T5: pin/port lines, the four-file dedup, and whether
      the `qExpansion_coeff_unique'` shape held.
- [x] `README.md` rows for both modules.

## 6. Reporting back

1. The four-file tail compression (pin lines vs port lines), measured.
2. Whether `qExpansion_coeff_unique'` held the `ℍ → ℂ` shape or stalled.
3. The `PowerSeries.heckeT` `k : ℕ` vs surface `k : ℤ` clash: how it was kept
   faithful.
4. The SET-4 hand-off: which tail helpers the eigen interface will need public.
