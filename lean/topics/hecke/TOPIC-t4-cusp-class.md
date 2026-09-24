# Topic 4: the cusp-class layer

**Status: planned (not started).** Third topic of [SET-2](SET-2.md). The four
`S_` files `S_ModularFormClass_isBoundedAt_hecke{U,T}.lean` and
`S_CuspFormClass_isZeroAt_hecke{U,T}.lean` are **all 132 lines with an identical
declaration list**: the same ~95-line block (rational-cusp transport, the
rational model of the Hecke matrices, `Finset` extension lemmas) plus the same
four `isBoundedAt`/`isZeroAt` proofs, differing only in the final `solution`.
This topic ports that block once and lands the four public theorems.

**Audience.** A fresh session taking the third SET-2 topic. Read
[SET-2.md](SET-2.md) §0–§3; the pin's
`P2M/Sol/S_ModularFormClass_isBoundedAt_heckeU.lean` (132 lines, the block);
`Def_ModularForm_HeckeOperator.lean` for `upperTriangularGL`; and
[porting-playbook.md](../../porting-playbook.md) §3, §7.

**Goal.** One new module `FLTForHuman/ModularForms/HeckeCusps.lean` holding the
block once and the four theorems verbatim from their wrappers:

```lean
theorem ModularFormClass.isBoundedAt_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [ModularFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsBoundedAt c (ModularForm.heckeU k p ⇑f) k
theorem ModularFormClass.isBoundedAt_heckeT … (heckeT k p ⇑f) …
theorem CuspFormClass.isZeroAt_heckeU {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} [Γ.IsArithmetic] {k : ℤ}
    [CuspFormClass F Γ k] (f : F) (p : ℕ) {c : OnePoint ℝ} (hc : IsCusp c Γ) :
    OnePoint.IsZeroAt c (ModularForm.heckeU k p ⇑f) k
theorem CuspFormClass.isZeroAt_heckeT … (heckeT k p ⇑f) …
```

## 1. Why this topic, and what is settled

- **Four files, one block.** `wc -l` on the pin's four files is 132/132/132/132;
  their declaration lists through `isZeroAt_heckeT` are identical. The port writes
  the block once.
- **Everything is mathlib-class-level.** `ModularFormClass`, `CuspFormClass`,
  `IsCusp`, `OnePoint.IsBoundedAt`/`IsZeroAt`,
  `Matrix.GeneralLinearGroup.map (Rat.castHom ℝ)` are mathlib; the block's four
  new ingredients are the rational-slash transport of a cusp
  (`isBoundedAt_slash_ratCast`, `isZeroAt_slash_ratCast`), the rational model
  `ratUpperTriangularGL` of `upperTriangularGL`, and the two `Finset` extension
  lemmas `isBoundedAt_sum`/`isZeroAt_sum`.
- **One promotion is required.** The block's `upperTriangularGL_eq_map` mentions
  `upperTriangularGL`, which the port made **`private`** in
  `Defs/HeckeOperator.lean` (T1 kept it private because only `heckeMatrix`
  consumers existed). T4 must promote it to public — the same move T1 made for
  `val_heckeMatrix` — and record the promotion.
- **The four targets reduce to T1 + the block.** `isBoundedAt_heckeU` rewrites
  `heckeU_def`, applies `isBoundedAt_sum` with `exists_heckeMatrix_eq_map`, then
  `isBoundedAt_slash_ratCast`; the `T` version adds the diagonal term via
  `heckeT_eq_heckeU_add` and `exists_heckeDiagMatrix_eq_map`. The `isZeroAt`
  pair is identical with `CuspFormClass.zero_at_cusps`.

**Settled: module and namespace.** New result module
`FLTForHuman/ModularForms/HeckeCusps.lean`. Namespace `ModularForm` for the
declarations (the pinned names are `ModularFormClass.*`/`CuspFormClass.*`; put
them in the same file without a new namespace, as the pin does). Import
`Mathlib.NumberTheory.ModularForms.Basic`, `Defs.HeckeOperator`, and specific
analysis modules — not `import Mathlib` beyond what the pin uses.

**Settled: keep the block private.** `isCusp_ratCast_smul`,
`isBoundedAt_slash_ratCast`, `isZeroAt_slash_ratCast`, `ratUpperTriangularGL`,
`upperTriangularGL_eq_map`, `exists_heckeMatrix_eq_map`,
`exists_heckeDiagMatrix_eq_map`, `isBoundedAt_sum`, `isZeroAt_sum` are block
helpers with no wrappers. Keep them `private` unless a later topic names them;
`exists_heckeMatrix_eq_map`/`exists_heckeDiagMatrix_eq_map` are the likely
SET-3 needs — if so, leave a note in the log rather than making them public
speculatively.

## 2. The scouted inventory

| pin declaration | pin line | port target | note |
|---|---|---|---|
| `isCusp_ratCast_smul` | 18 | private helper | `IsCusp` is preserved by `GL₂(ℚ)`-smul |
| `isBoundedAt_slash_ratCast` | 24 | private helper | `ModularFormClass.bdd_at_cusps` + `smul_iff` |
| `isZeroAt_slash_ratCast` | 28 | private helper | `CuspFormClass.zero_at_cusps` + `smul_iff` |
| `ratUpperTriangularGL` | 36 | private helper | the `ℚ` model of `upperTriangularGL` |
| `upperTriangularGL_eq_map` | 40 | private helper | needs `upperTriangularGL` **public** |
| `exists_heckeMatrix_eq_map` | 47 | private helper | `heckeMatrix p j` is rational |
| `exists_heckeDiagMatrix_eq_map` | 56 | private helper | `heckeDiagMatrix p` is rational |
| `isBoundedAt_sum` | 71 | private helper | `Finset.induction_on` + `add` |
| `isZeroAt_sum` | 83 | private helper | same |
| `isBoundedAt_heckeU` | 95 | **public target** | |
| `isBoundedAt_heckeT` | 103 | **public target** | |
| `isZeroAt_heckeU` | 111 | **public target** | |
| `isZeroAt_heckeT` | 119 | **public target** | |

Route notes:

- **Promote `upperTriangularGL` first.** In `Defs/HeckeOperator.lean` it is
  `private def`; make it public and keep `val_upperTriangularGL` public for the
  `eq_map` proof (`Matrix.GeneralLinearGroup.mkOfDetNeZero` ext). `heckeMatrix`/
  `heckeDiagMatrix`'s `if p = 0 then 1` branches are handled by the pin's
  `rcases eq_or_ne p 0` with `heckeMatrix_zero`/`heckeDiagMatrix_zero` (T1).
- `isBoundedAt_slash_ratCast` is `OnePoint.IsBoundedAt.smul_iff.mp
  (ModularFormClass.bdd_at_cusps f (isCusp_ratCast_smul hc g))` — the `smul_iff`
  is mathlib's and carries the weight; do not try to unfold `IsBoundedAt`.
- `exists_heckeMatrix_eq_map` needs `ratUpperTriangularGL 1 j p` and the `p ≠ 0`
  case; `exists_heckeDiagMatrix_eq_map` needs `ratUpperTriangularGL p 0 1`. Both
  are `ext i j <;> fin_cases <;> simp [ratUpperTriangularGL,
  upperTriangularGL_eq_map-or-def]`.
- `isBoundedAt_sum`/`isZeroAt_sum` are `Finset.induction_on`, with the empty case
  `Filter.const_boundedAtFilter`/`Filter.zero_zeroAtFilter` and the insert case
  `add`; note the pin's `classical` and the `zero_slash` rewrite.
- The four targets are then five-line wrappers; `isBoundedAt_heckeT` uses
  `(isBoundedAt_heckeU f p hc).add …`, so keep the `heckeU` theorem above it.

## 3. What is different about this topic

- **Four-to-one dedup.** The whole topic is the block once plus four short
  wrappers; record the `grep -c`.
- **The promotion is the one cross-module edit.** T1's principle applies: a
  private helper that a later topic needs becomes public, with the header
  updated. `Defs/HeckeOperator.lean`'s header currently says the helpers are
  private; amend it.
- **Class-instantiation risk.** The block's helpers are stated over
  `[FunLike F ℍ ℂ]` and are used at `F := F` by the targets; the `ModularFormClass`
  / `CuspFormClass` instances must be inferred, not restated. This is the likely
  stall point (the `FunLike`-at-a-bare-function warning in `SET-2` §2) — if a
  helper stalls, state the monomorphic instance the target needs rather than
  raising the cap.
- **No consumer.** Checker + build is the wire test.

## 4. Budget

**1–2 goal rounds.** The block is short and mechanical; the only real work is the
`upperTriangularGL` promotion and the `Finset` induction. Round 1 should land the
block and the four targets; a second round is for the bookkeeping.

**Stop early on**: a target that will not match its wrapper; the promotion
forcing a change to `HeckeOperator.lean`'s existing statements (it must not); or
a helper needing the deferred `q`-coefficient vocabulary (it should not).

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **696 identical, 0 mismatched, 0 missing**; full `lake build` exit 0
(4042 jobs), 0 warnings, no `sorry`; `#print axioms` clean on the four targets.
All items held as written.

- [x] `FLTForHuman/ModularForms/HeckeCusps.lean` created; the block once
      (`private`), the four public targets verbatim from their wrappers.
- [x] `upperTriangularGL` (and `val_upperTriangularGL`) public in
      `Defs/HeckeOperator.lean`; header amended; `grep -c` for the private copy
      is 0.
- [x] `timeout 90 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the four wrappers appended to `SOURCES`, `HeckeCusps.lean`
      appended to `PORT_FILES`, **0 mismatched, 0 missing**.
- [x] `#print axioms` on the four clean.
- [x] `logs/hecke-port.md` §T4: the four-to-one dedup count, the promotion, and
      whether the class instantiation stalled anywhere.
- [x] `README.md` row for `HeckeCusps.lean`.

## 6. Reporting back

1. **The dedup**, measured: 4 × 132 pin lines vs the module's lines.
2. **The promotion**: what `Defs/HeckeOperator.lean` had to expose, and whether
   anything else needed it.
3. **Whether the `FunLike`/class instantiation stalled**, and if so which helper
   and how it was restated — this is the calibration for SET 3's
   `ModularFormClass.qCoeff_*` targets, which are over the same class.
4. **The SET-3 hand-off**: whether `exists_heckeMatrix_eq_map`/
   `exists_heckeDiagMatrix_eq_map` are needed downstream (and hence should be
   public), or stay private.
