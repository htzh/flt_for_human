# Topic 8: the eigenform interface

**Status: planned (not started).** First topic of [SET-4](SET-4.md). It ports the
pin's `CuspForm.IsNormalizedEigenform` structure and the dictionary that says a
normalized eigenform is exactly a simultaneous eigenvector of the Hecke operators
— the survey's §8, and the interface the FLT route consumes when it speaks of
"the eigenform attached to a Galois representation".

**Audience.** A fresh session taking the first SET-4 topic. Read
[SET-4.md](SET-4.md) §0–§3; survey §8; the pin's
`Definitions/Def_FLTPrelim_Modularity.lean:26–40` (the structure) and the S files
listed below; and [porting-playbook.md](../../porting-playbook.md) §3, §7.

**Goal.** Two modules:

- `FLTForHuman/ModularForms/Defs/Eigenform.lean` — the pin's
  `CuspForm.IsNormalizedEigenform` structure (four coefficient clauses), verbatim
  from `Def_FLTPrelim_Modularity.lean:26–40`.
- `FLTForHuman/ModularForms/HeckeEigenform.lean` — the interface:
  - the three characterisations `CuspForm.isNormalizedEigenform_iff_heckeT`,
    `…_iff_heckeTLin`, `…_iff_coeffHecke`;
  - the single-operator `iff`s `CuspForm.heckeTLin_apply_eq_smul_iff`,
    `CuspForm.heckeULin_apply_eq_smul_iff`,
    `ModularFormClass.heckeU_eq_smul_iff`, `ModularFormClass.heckeT_eq_smul_iff`;
  - the forward directions
    `CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul`,
    `…heckeULin_apply_eq_qCoeff_smul`;
  - the coefficient eigenvalue/vanishing pair
    `ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one`,
    `ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero`;
  - the formal multiplicity statement
    `LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero`;
  - `PowerSeries.coeff_heckeT_pow_sub_mem_span` (the Frobenius/mod-`p` input).

## 1. Why this topic, and what is settled

- **The structure is not in the port.** `IsNormalizedEigenform` is the pin's
  four-clause predicate (`qCoeff_one`, `qCoeff_mul_of_coprime`,
  `qCoeff_prime_pow_of_not_dvd`, `qCoeff_prime_pow_of_dvd`); T5 transcribed the
  same file's `qCoeff` but not the structure. Port it first, in `Defs/`.
- **The three `iff`s are the same statement in three registers.**
  `isNormalizedEigenform_iff_heckeT` uses the surface operators,
  `…_iff_heckeTLin` the bundled maps, `…_iff_coeffHecke` the coefficient maps on
  `qCoeff`. The coefficient version is the substantial one (200 pin lines: a
  four-clause recursion `a_{p^{r+2}} = a_p a_{p^{r+1}} - p^{k-1} a_{p^r}` and
  multiplicativity); the other two are thin rewrites. Port the coefficient one
  once and derive the others — the pin proves them separately, which is another
  dedup opportunity.
- **The `apply_eq_smul_iff` pair is the q-coefficient comparison.** `T f = c f`
  iff `coeffHeckeT (qCoeff f) = c · qCoeff f`, proved by T5's
  `qCoeff_heckeT` + `eq_of_forall_qCoeff_eq`; the bundled and function-level
  versions share the argument.
- **`LaurentSeries.eq_zero_of_heckeT_eq_smul…` is multiplicity one** for a formal
  series that is a simultaneous eigenvector with nonnegative support and `a_1 = 0`;
  it is stated over `LaurentSeries R` for a general `CommRing R` and needs the
  formal operators from T7 (`LaurentSeries.hecke{U,T}`).
- **`PowerSeries.coeff_heckeT_pow_sub_mem_span`** is the one analytic-adjacent
  target: `heckeT` applied to a `p^j`-th power of a normalized eigenform's
  coefficient series, modulo `(p)`. It needs `IsNormalizedEigenform` and
  `PowerSeries.heckeT`; keep it here because its statement is about the
  eigenform, not about the congruence machinery it feeds.

**Settled: no new analytic work.** Every target's side conditions are T3/T5/T6
exports; if a proof needs a new analytic lemma, that is a finding.

## 2. The scouted inventory

| target | pin file (lines) | module |
|---|---|---|
| `CuspForm.IsNormalizedEigenform` | `Def_FLTPrelim_Modularity` 26–40 | `Defs/Eigenform.lean` |
| `CuspForm.isNormalizedEigenform_iff_coeffHecke` | 200 | `HeckeEigenform.lean` |
| `CuspForm.isNormalizedEigenform_iff_heckeT` | 26 | `HeckeEigenform.lean` |
| `CuspForm.isNormalizedEigenform_iff_heckeTLin` | 13 | `HeckeEigenform.lean` |
| `CuspForm.heckeTLin_apply_eq_smul_iff` | 12 | `HeckeEigenform.lean` |
| `CuspForm.heckeULin_apply_eq_smul_iff` | 12 | `HeckeEigenform.lean` |
| `ModularFormClass.heckeU_eq_smul_iff` | 73 | `HeckeEigenform.lean` |
| `ModularFormClass.heckeT_eq_smul_iff` | 73 | `HeckeEigenform.lean` |
| `CuspForm.IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` | 175 | `HeckeEigenform.lean` |
| `CuspForm.IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul` | 132 | `HeckeEigenform.lean` |
| `ModularForm.coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one` | 67 | `HeckeEigenform.lean` |
| `ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero` | 67 | `HeckeEigenform.lean` |
| `LaurentSeries.eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero` | 61 | `HeckeEigenform.lean` |
| `PowerSeries.coeff_heckeT_pow_sub_mem_span` | 156 | `HeckeEigenform.lean` |

The three characterisations, verbatim from their wrappers:

```lean
theorem CuspForm.isNormalizedEigenform_iff_heckeT {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔
  (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
    ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧
     (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f)))
theorem CuspForm.isNormalizedEigenform_iff_heckeTLin {N : ℕ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔
  (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
    ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
    ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f))
theorem CuspForm.isNormalizedEigenform_iff_coeffHecke {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔
  (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
    ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n =
        ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧
     (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n =
        ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)))
```

Route notes:

- The `iff_coeffHecke` forward direction is the four-clause recursion; the pin's
  file structures it as `heckeT_eigen_of_rec`, `heckeU_eigen_of_rec`,
  `rec_of_heckeT_eigen`, `rec_of_heckeU_eigen`, `pow_mul_of_heckeT_eigen`,
  `mul_of_coprime_of_pow_mul` and a final assembly. Port that skeleton; the
  reverse direction closes with T5's `coeffHeckeT_comm`/`coeffHeckeU_comm`.
- The two "thin" `iff`s should be *derived* from `iff_coeffHecke` + T6's
  `coe_heckeTLin_apply`/`coe_heckeULin_apply` + T5's `qCoeff_heckeT`/
  `qCoeff_heckeU`, not re-proved. If the pin's standalone proofs are genuinely
  shorter, port them and record why.
- The `apply_eq_smul_iff` pair is `qCoeff`-comparison + T5's
  `eq_of_forall_qCoeff_eq`; `heckeULin_apply_eq_smul_iff` has `[NeZero N]` and
  `hpN : p ∣ N`, `heckeTLin_apply_eq_smul_iff` has `hp : p.Prime`, `hpN : ¬ p ∣ N`.
- `IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul` is the forward direction
  of `iff_heckeTLin` at the prime; keep `N` explicit as the wrapper does.
- `coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one` and
  `eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero` are standalone coefficient
  facts (no `CuspForm`); they are `ℕ → ℂ` algebra.
- `PowerSeries.coeff_heckeT_pow_sub_mem_span` needs `IsNormalizedEigenform`,
  `qCoeff` integrality (`integralClosure ℤ ℂ`), `PowerSeries.heckeT` and T5's
  `coeff_heckeT`; it is the longest proof after `iff_coeffHecke`.

## 3. What is different about this topic

- **The first topic stated against the *bundled* operators and the algebra**,
  rather than about them; it is the interface SET 5 and the FLT machinery
  downstream consume.
- **Dedup inside the three `iff`s.** The pin proves the coefficient, surface and
  bundled forms separately; they are one statement in three registers. Deriving
  two from one is the topic's main reorganization.
- **`iff_coeffHecke` is the stall risk** (four-clause recursion over `ℕ`); if it
  stalls, quarantine and bisect, do not raise the cap.
- **The structure's field names are load-bearing** (`qCoeff_one`,
  `qCoeff_mul_of_coprime`, `qCoeff_prime_pow_of_not_dvd`,
  `qCoeff_prime_pow_of_dvd`); downstream code pattern-matches on them.

## 4. Budget

**2–3 goal rounds, checkpoint at 2.** Round 1: the structure and
`iff_coeffHecke`'s forward half. Round 2: the reverse direction, the three `iff`s
and the `apply_eq_smul_iff` family. Round 3: the coefficient pair, the formal
multiplicity and the `PowerSeries` target.

**Stop early on**: a statement that will not match its wrapper; `iff_coeffHecke`
needing a `qCoeff` recursion lemma the port does not have; or a target pulling in
the congruence/mod-`p` machinery (`Def_CuspForm_ModPForms`), which is out of
scope — `PowerSeries.coeff_heckeT_pow_sub_mem_span`'s statement is the boundary.

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **802 identical (53 promoted), 0 mismatched, 0 missing, 14 own-proof**;
full `lake build` exit 0 (4054 jobs), 0 warnings, no `sorry`; `#print axioms`
clean on the T8 headlines. The dedup was verified: the three `iff`s are derived
from the coefficient one, and `HeckeEigenform.lean` has no `hasSum_hecke`
*declaration* (the three `grep` hits are the header's prose — the runner's "= 0"
was a comment-count imprecision). One extra public declaration beyond the
inventory, `CuspForm.qCoeff_zero`, is a genuine dependency of the coefficient
`iff` and has its own pin wrapper; it was added to `SOURCES`.

- [x] `FLTForHuman/ModularForms/Defs/Eigenform.lean` created; the structure
      verbatim, field names unchanged.
- [x] `FLTForHuman/ModularForms/HeckeEigenform.lean` created; the 13 targets
      verbatim from their wrappers (plus the justified `qCoeff_zero`).
- [x] the two thin `iff`s derived from the coefficient one.
- [x] `timeout 600 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the wrappers appended to `SOURCES`, both modules to `PORT_FILES`,
      **0 mismatched, 0 missing**.
- [x] `#print axioms` on the three `iff`s and the two `apply_eq_smul_iff`s clean.
- [x] `logs/hecke-port.md` §T8: the eigenform dictionary, the dedup result, the
      stall point if any.
- [x] `README.md` rows for both modules.

## 6. Reporting back

1. The eigenform dictionary, with exact names and binder order.
2. Whether the three `iff`s were derived from one or re-proved (and the measured
   difference).
3. Whether `iff_coeffHecke` stalled, and where.
4. The SET-5 hand-off: what the interface leaves `private`, and the Tier-2..4
   entry cost.
