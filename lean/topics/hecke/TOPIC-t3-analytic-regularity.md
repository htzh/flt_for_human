# Topic 3: the analytic regularity layer

**Status: planned (not started).** Second topic of [SET-2](SET-2.md). The ten
`S_` files that carry the 353-line shared block all repeat the same **analytic
head** (pin lines 23–154: `heckeMatrix_one_zero`, `mdifferentiable_heckeU/T`,
`isBoundedAtImInfty_heckeU/T`, `isZeroAtImInfty_heckeU/T`, the `vadd`/periodicity
machinery, `periodic_heckeU/T_comp_ofComplex`). Six of those files are this
topic's targets; the other four are the `q`-coefficient layer, deferred to SET 3.
The topic ports the head **once** and lands the six targets plus the separate
one-line `mdifferentiable_slash_heckeDiagMatrix`.

**Audience.** A fresh session taking the second SET-2 topic. Read
[SET-2.md](SET-2.md) §0–§3; the pin's
`P2M/Sol/S_ModularForm_mdifferentiable_heckeU.lean` lines 18–154 (the block);
`Def_ModularForm_HeckeOperator.lean:72–200` for the operator block T1 ported; and
[porting-playbook.md](../../porting-playbook.md) §3, §7.

**Goal.** One new module `FLTForHuman/ModularForms/HeckeAnalytic.lean` holding the
analytic block once, and the seven public theorems verbatim from their wrappers:

- `ModularForm.mdifferentiable_heckeU`, `ModularForm.mdifferentiable_heckeT`;
- `ModularForm.mdifferentiable_slash_heckeDiagMatrix`;
- `ModularForm.periodic_heckeU_comp_ofComplex`,
  `ModularForm.periodic_heckeT_comp_ofComplex`;
- `ModularForm.isBoundedAtImInfty_heckeU`,
  `ModularForm.isBoundedAtImInfty_heckeT`.

## 1. Why this topic, and what is settled

- **The block is in ten files; six are here.** `wc -l` on the pin shows
  `mdifferentiable_heckeU/T`, `periodic_heckeU/T`, `isBoundedAtImInfty_heckeU/T`,
  `UpperHalfPlane.qCoeff_heckeU/T` and `ModularFormClass.qCoeff_heckeU/T` all at
  **353 lines**, with byte-identical declaration lists through the analytic head.
  This topic ports lines 23–154 once; SET 3 ports lines 158–345
  (`qExpansion_coeff_unique'` onward, including `hasSum_heckeU/T` and
  `qCoeff_heckeU/T_bare/class`).
- **Every target is `cites = 0`** and depends only on the Tier-0 operator block
  and mathlib's `UpperHalfPlane` analysis. Nothing here is new mathematics: the
  targets are `Finset.sum_induction` over `heckeU`/`heckeT`, `MDifferentiable.slash`
  and an `IsBoundedAtImInfty.slash`, plus a `vadd` reindex for periodicity.
- **Two non-target helpers must come along.** `heckeMatrix_one_zero` and
  `heckeDiagMatrix_one_zero` supply the `1 0 = 0` hypothesis that
  `IsBoundedAtImInfty.slash`/`MDifferentiable.slash` want; `isZeroAtImInfty_heckeU/T`
  have **no `Thm_` wrapper** and are block-internal — keep them `private` (or
  public if a later module names them; nothing does today).
- **The one-liner is separate.** `mdifferentiable_slash_heckeDiagMatrix`'s pin
  `S_` file is 9 lines: `MDifferentiable.slash hf k (ModularForm.heckeDiagMatrix d)`,
  with no shared block. Put it in the same module; its wrapper statement is
  `(d : ℕ) (k : ℤ) {f} (hf) : MDifferentiable … (SlashAction.map k (heckeDiagMatrix d) f)`.

**Settled: port the head, not the tail.** Do not port `qExpansion_coeff_unique'`,
`hasSum_qCoeff`, `qParam_hecke*`, `sum_rootOfUnity_pow`, `hasSum_average`,
`hasSum_diag`, `hasSum_heckeU/T` or `qCoeff_*_bare/class`. They are SET 3's, and
pulling them in now would open the `PowerSeries`/`qExpansion` vocabulary this
topic does not need.

**Settled: module and namespace.** New result module
`FLTForHuman/ModularForms/HeckeAnalytic.lean`, namespace `ModularForm` (the
pinned names). It imports `FLTForHuman.ModularForms.Defs.HeckeOperator` and
specific mathlib analysis/modular-forms modules — not `import Mathlib`, unless
the pin's own `S_` file does (it does: its first import is `Mathlib`; keep the
import list explicit anyway).

## 2. The scouted inventory

| pin declaration | pin line | port target | note |
|---|---|---|---|
| `heckeMatrix_one_zero` | 27 | `HeckeAnalytic` (private) | `1 0 = 0` of `!![1,j;0,p]` |
| `heckeDiagMatrix_one_zero` | 33 | `HeckeAnalytic` (private) | `1 0 = 0` of `!![p,0;0,1]` |
| `mdifferentiable_heckeU` | 45 | public target | `Finset.sum_induction` + `hf.slash` |
| `mdifferentiable_heckeT` | 49 | public target | `…heckeU` + `hf.slash` + `add` |
| `isBoundedAtImInfty_heckeU` | 52 | public target | same shape, `zero_form_isBoundedAtImInfty` |
| `isBoundedAtImInfty_heckeT` | 58 | public target | |
| `isZeroAtImInfty_heckeU` | 62 | private helper | no wrapper |
| `isZeroAtImInfty_heckeT` | 68 | private helper | no wrapper |
| `apply_eq_of_coe_eq_add_nat` | 72 | private helper | `Periodic` over `ofComplex` |
| `heckeMatrix_smul_vadd` | 84 | private helper | `(1:ℝ) +ᵥ τ` shifts `j ↦ j+1` |
| `coe_heckeMatrix_smul_self` | 93 | private helper | `j = p` wraps to `j = 0` |
| `coe_heckeDiagMatrix_smul_vadd` | 103 | private helper | diagonal shifts by `p` |
| `sum_heckeMatrix_smul_vadd` | 110 | private helper | the `range p` reindex |
| `heckeU_vadd` | 119 | private helper | uses `heckeU_apply` (T1) |
| `heckeT_vadd` | 125 | private helper | uses `heckeT_apply` (T1) |
| `periodic_comp_ofComplex_of_vadd` | 133 | private helper | `vadd`-invariant ⇒ periodic |
| `periodic_heckeU_comp_ofComplex` | 146 | public target | |
| `periodic_heckeT_comp_ofComplex` | 150 | public target | |
| `mdifferentiable_slash_heckeDiagMatrix` | — | public target | its own 9-line file |

The seven target statements, verbatim from their wrappers:

```lean
theorem ModularForm.mdifferentiable_heckeU {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeU k p f)
theorem ModularForm.mdifferentiable_heckeT {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f)
theorem ModularForm.mdifferentiable_slash_heckeDiagMatrix (d : ℕ) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f)
theorem ModularForm.periodic_heckeU_comp_ofComplex {f : UpperHalfPlane → ℂ}
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) :
    Function.Periodic (ModularForm.heckeU k p f ∘ UpperHalfPlane.ofComplex) 1
theorem ModularForm.periodic_heckeT_comp_ofComplex {f : UpperHalfPlane → ℂ}
    (hf : Function.Periodic (f ∘ UpperHalfPlane.ofComplex) 1) (k : ℤ) (p : ℕ) :
    Function.Periodic (ModularForm.heckeT k p f ∘ UpperHalfPlane.ofComplex) 1
theorem ModularForm.isBoundedAtImInfty_heckeU {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeU k p f)
theorem ModularForm.isBoundedAtImInfty_heckeT {f : UpperHalfPlane → ℂ}
    (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) :
    UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeT k p f)
```

Route notes:

- `mdifferentiable_heckeU` is `Finset.sum_induction _ (fun g => MDiff g) (·.add ·)
  mdifferentiable_const (fun _ _ => hf.slash k _)`. The goal is `heckeU k p f`,
  which is the `Finset.sum` by definition; if `Finset.sum_induction` will not fire
  on the folded form, `rw [ModularForm.heckeU_def]` first — that is the same
  defeq, and `heckeU_def` is public from T1.
- `mdifferentiable_heckeT` is `(mdifferentiable_heckeU k p hf).add (hf.slash k _)`
  through `heckeT_eq_heckeU_add`; do not unfold `heckeT` again.
- The boundedness pair uses `hf.slash k (heckeMatrix_one_zero p j)`; check
  mathlib's exact `slash` lemma for `IsBoundedAtImInfty` and supply the `1 0 = 0`
  proof the same way the pin does.
- The periodicity chain is: `heckeU_apply`/`heckeT_apply` (T1) → the `vadd`
  reindex `sum_heckeMatrix_smul_vadd` → `periodic_comp_ofComplex_of_vadd`. The
  two matrix identities (`heckeMatrix p p • τ = heckeMatrix p 0 • τ + 1`,
  `heckeDiagMatrix p • (1 +ᵥ τ) = heckeDiagMatrix p • τ + p`) are `coe_*_smul`
  (T1) + `ring`, exactly as the pin.
- `mdifferentiable_slash_heckeDiagMatrix` is `MDifferentiable.slash hf k _`; its
  pin `S_` file imports a Frey-package module for the lemma, but mathlib's
  `MDifferentiable.slash` is the source — do not port the Frey module.

## 3. What is different about this topic

- **Six-to-one dedup, and it is the whole point.** Port the head once; the six
  targets are then short. Record `grep -c` showing the block exists in exactly
  one port module.
- **`Finset.sum_induction` over a folded `def`.** `heckeU`/`heckeT` are `def`s
  from T1; the pin's proofs rely on them being reducible sums. If a rewrite
  stalls, `rw [heckeU_def]`/`heckeT_eq_heckeU_add` is the fix — not a
  `maxHeartbeats` bump.
- **No consumer.** The wire test is the checker plus `lake build`; put any
  `#check` probe in `Scratch*.lean`.
- **The tail is deliberately left behind.** A coder tempted to port the whole
  353-line block at once would open SET 3; don't.

## 4. Budget

**2 goal rounds, checkpoint at 1.** Round 1: the block head and the four
function-level targets; round 2: the two periodic targets, the one-liner, and the
bookkeeping. The only shape risk is `Finset.sum_induction` on the folded
`heckeU`/`heckeT`.

**Stop early on**: a target that will not match its wrapper; `Finset.sum_induction`
needing the sum unfolded in a way that changes the statement; or the periodicity
chain needing a helper from the deferred `q`-coefficient tail.

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **696 identical, 0 mismatched, 0 missing**; full `lake build` exit 0
(4042 jobs), 0 warnings, no `sorry`; `#print axioms` clean on the seven targets.
All items held as written.

- [x] `FLTForHuman/ModularForms/HeckeAnalytic.lean` created; the analytic head
      (pin 23–154) once, the seven public targets verbatim from their wrappers.
- [x] the two `isZeroAtImInfty_*` and the periodicity helpers `private`; the
      block appears in exactly one port module (`grep -c` recorded).
- [x] the deferred tail is **absent** — `grep -c` for `hasSum_qCoeff`,
      `hasSum_average`, `qCoeff_heckeU_bare` in the new module is 0.
- [x] `timeout 90 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the seven wrappers appended to `SOURCES`, `HeckeAnalytic.lean`
      appended to `PORT_FILES`, **0 mismatched, 0 missing**.
- [x] `#print axioms` on the seven clean.
- [x] `logs/hecke-port.md` §T3: pin/port lines, the six-file dedup count, and
      whether `Finset.sum_induction` held on the folded `def`.
- [x] `README.md` row for `HeckeAnalytic.lean`.

## 6. Reporting back

1. **The dedup**, measured: the six pin files' lines vs the one module's, and the
   `grep -c` for the block and for the deferred tail.
2. **Whether the folded `def` mattered** — did `mdifferentiable_heckeU` need
   `heckeU_def`, or did `Finset.sum_induction` fire directly?
3. **The exact mathlib lemmas** used for the `slash` steps (`MDifferentiable.slash`,
   the `IsBoundedAtImInfty` variant), since T4 and SET 3 will reuse them.
4. **The SET-3 hand-off**: what `HeckeAnalytic.lean` exposes (the matrix
   `one_zero` lemmas in particular) that the `q`-coefficient tail will need.
