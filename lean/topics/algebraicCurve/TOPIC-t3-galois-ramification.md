# T3 — Galois ramification and inertia (7 nodes)

**Status (2026-09-22): work order written, not started.** Fourth topic of SET 1;
read [SET-1.md](SET-1.md) first. Depends on **AC0** and **T1** (and consumes AC0's
`Defs/SemilinearAut.lean` and `Defs/Correspondence.lean`).

**Audience.** A fresh session continuing the port after T2's dictionary is public.
The method is [porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §3.1 and §8 (risk 3).

**Goal.** Prove that the Galois action on places preserves restriction, ramification
index and inertia degree — the input T5's bifibre count and T6's local exchange both
consume. Seven nodes, 304 raw / 160 content lines, in
`WeilExchange/GaloisRamification.lean` plus AC0's `Defs/SemilinearAut.lean` and
`Defs/Place.lean`.

## 1. Why this topic, and what is settled

- **Settled: this is the "Galois case" half of the exchange's reduction.** T6 later
  proves the bifibre identity first for a *Galois* extension `F ⊆ M` and then
  reduces the separable case to the normal closure. T3 is the Galois-case input:
  `exists_algEquiv_smul_eq_of_restrict_eq` is the statement that two places over the
  same place of `F'` are Galois-conjugate, and the `_smul` lemmas say conjugates have
  equal ramification/inertia.
- **Settled: statements are the wrappers', verbatim.** All seven have
  `Theorems/Thm_AlgebraicCurve_*.lean` wrappers.
- **Settled: the `SemilinearAut` `MulSemiringAction` on `Place` is AC0's**, from
  `Def_AlgebraicCurve_BaseChangeGalois` 104–206 (`smulValuationSubringEquiv`,
  `smul_toValuationSubring`, `ord_smul`, `smulResidueRingEquiv`,
  `smulResidueRingEquiv_algebraMap`, `deg_smul`). T3 adds only the seven nodes;
  if AC0's keep set trimmed any of that block, restore exactly what T3 needs and
  report it.
- **Settled: `def`s stay in the pin's order.** `restrictSmulValuationSubringEquiv`
  (a `private def`) is used only by `inertiaDeg_smul`; keep it `private` in the
  topic module.

## 2. The scouted inventory — all 7, with statements

| declaration | raw/c | ext | pin route |
|---|---|---|---|
| `Place.exists_algEquiv_smul_eq_of_restrict_eq` | 83/51 | 13 | `IsGaloisGroup` + `Ideal.exists_smul_eq_of_isGaloisGroup` on the two `fiberCenter` primes |
| `Place.restrict_ofAlgAut_smul` | 41/18 | 7 | `Place.ext` + `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem` + `σ.commutes` |
| `SemilinearAut.ramificationIndex_smul` | 23/12 | 2 | reduce to `ord` via `IntertwinesAlong.one`, then `ramificationIndex_eq_of_restrict_eq` |
| `SemilinearAut.inertiaDeg_smul` | 53/41 | 1 | `restrictSmulValuationSubringEquiv` + `smulResidueRingEquiv`, `Algebra.finrank_eq_of_equiv_equiv` |
| `SemilinearAut.ord_algebraMap_smul` | 16/6 | 0 | `hgg'` twist + `ord_smul` |
| `Place.ramificationIndex_eq_of_restrict_eq` | 44/16 | 3 | `exists_algEquiv_smul_eq_of_restrict_eq` + `ramificationIndex_smul` |
| `Place.inertiaDeg_eq_of_restrict_eq` | 44/16 | 1 | same with `inertiaDeg_smul` |

Statements verbatim from the wrappers:

```lean
theorem AlgebraicCurve.Place.exists_algEquiv_smul_eq_of_restrict_eq
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    ∃ σ : M ≃ₐ[F'] M, SemilinearAut.ofAlgAut (σ.restrictScalars K) • W = W'

theorem AlgebraicCurve.Place.restrict_ofAlgAut_smul
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [Algebra.IsIntegral F' M]
    (σ : M ≃ₐ[F'] M) (W : Place K M) :
    (SemilinearAut.ofAlgAut (σ.restrictScalars K) • W).restrict F' = W.restrict F'

theorem AlgebraicCurve.SemilinearAut.ramificationIndex_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (g' • w).ramificationIndex F = w.ramificationIndex F

theorem AlgebraicCurve.SemilinearAut.inertiaDeg_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') :
    (g' • w).inertiaDeg F = w.inertiaDeg F

theorem AlgebraicCurve.SemilinearAut.ord_algebraMap_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [Algebra F F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (hgg' : IntertwinesAlong (algebraMap F F') g g') (w : Place K F') (f : F) :
    (g' • w).ord (algebraMap F F' f) = w.ord (algebraMap F F' (g⁻¹ • f))

theorem AlgebraicCurve.Place.ramificationIndex_eq_of_restrict_eq
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    W'.ramificationIndex F' = W.ramificationIndex F'

theorem AlgebraicCurve.Place.inertiaDeg_eq_of_restrict_eq
    {K F' M : Type*} [Field K] [Field F'] [Field M] [Algebra K F'] [Algebra K M]
    [Algebra F' M] [IsScalarTower K F' M] [FiniteDimensional F' M] [IsGalois F' M]
    (W W' : Place K M) (h : W'.restrict F' = W.restrict F') :
    W'.inertiaDeg F' = W.inertiaDeg F'
```

## 3. Route notes, so none of this has to be rediscovered

- **`exists_algEquiv_smul_eq_of_restrict_eq` is the only mathlib-archaeology
  node.** The pin:
  1. sets `w := W.restrict F'`;
  2. builds `letI := IsIntegralClosure.MulSemiringAction w.toValuationSubring F' M
     (integralClosureAt M w)` — the `MulSemiringAction` of `Gal(M/F')` on the
     integral closure;
  3. `haveI : IsGaloisGroup Gal(M/F') w.toValuationSubring (integralClosureAt M w)`
     via `IsGaloisGroup.of_isFractionRing … F' M`;
  4. applies `Ideal.exists_smul_eq_of_isGaloisGroup` to the two `fiberCenter`
     primes and concludes by `eq_of_fiberCenter_eq` (a T2 dictionary consumer!) plus
     `mem_fiberCenter_iff_ord_pos` and an `ord_smul_eq` helper.
  `Gal(M/F')` is mathlib's notation; `IsGaloisGroup.of_isFractionRing`,
  `IsIntegralClosure.MulSemiringAction` and `Ideal.exists_smul_eq_of_isGaloisGroup`
  are the three API points to `#check` first. **This node consumes T2's
  `PlaceDictionary`** (`fiberCenter`, `mem_fiberCenter_iff_ord_pos`,
  `eq_of_fiberCenter_eq`), which is why T3 comes after T2 even though the blueprint's
  §3.1 diagram puts T3 on the same rung.
- **`Place.restrict_ofAlgAut_smul` is the same proof as the private
  `restrict_ofAlgAut_restrictScalars_smul` inside the first node's file** (the pin
  writes it twice: private in
  `S_AlgebraicCurve_Place_exists_algEquiv_smul_eq_of_restrict_eq.lean:4-25` and
  public as its own node). Write the public one once and let the first node use it.
  Same for `ord_smul_eq` vs `ord_smul` on `SemilinearAut`: the private helper
  `ord_smul_eq g W y : (g • W).ord y = W.ord (g⁻¹ • y)` is a one-line `conv` around
  AC0's `SemilinearAut.ord_smul`.
- **The `•` is `MulSemiringAction`.** `SemilinearAut.ofAlgAut (σ.restrictScalars K) • W`
  needs the AC0 instance; `smul_toValuationSubring` is
  `(g • v).toValuationSubring = g • v.toValuationSubring` (pointwise smul on
  subrings), and the key rewrite is
  `ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem`.
- **`inertiaDeg_smul` is the lengthiest proof** (53 raw): it builds
  `restrictSmulValuationSubringEquiv` (a ring equivalence of the two restricted
  valuation subrings, `private`, with the `@[scoped simp]` coefficient lemma), then
  `Algebra.finrank_eq_of_equiv_equiv` between
  `IsLocalRing.ResidueField.mapEquiv …` and `smulResidueRingEquiv g' w`, and closes
  by `ext` on the quotient with `IsLocalRing.ResidueField.map_residue` and
  `hgg'`.
- **`ramificationIndex_smul` and `inertiaDeg_smul` take
  `[Algebra.IsIntegral F F']` but not `FiniteDimensional`;** the `_eq_of_restrict_eq`
  corollaries add `FiniteDimensional`/`IsGalois` and use the `IntertwinesAlong.one`
  helper (`intertwinesAlong_one_ofAlgAut`).
- **Keep `IntertwinesAlong`'s API in AC0.** `IntertwinesAlong.one`/`.inv`/`.mul` are
  in `Def_AlgebraicCurve_Correspondence` 324–347 and AC0 keeps them; T3 uses
  `.one`, T5 uses `.inv`/`.mul`.

## 4. What is different about this topic

- **It is short but mathlib-heavy.** 160 content lines, but three of its rewrites
  are against mathlib's `IsGaloisGroup`/`IsIntegralClosure` API, which is the least
  familiar surface in SET 1. Budget the first round for `#check` probes in
  `Scratch.lean`, not for writing.
- **It couples two AC0 modules** (`SemilinearAut`, `Correspondence`) and T2's
  dictionary. That is by design: the Galois action on a place is only useful once
  places-over-a-place are classified by the fibre-centre ideal.
- **No `DecidableEq`, no `Finset` plumbing** — that is T5/T7.

## 5. Budget and stop-early

**2 goal rounds, checkpoint at 1.** Seven nodes, 160 content lines, one of them
`IsGaloisGroup`-heavy. Two is the threshold.

**Stop early, and report rather than restate, on**:
`Ideal.exists_smul_eq_of_isGaloisGroup` or `IsGaloisGroup.of_isFractionRing` having
a different signature in v4.34 (quote it); the `MulSemiringAction` instance not
firing; or `SemilinearAut`'s `smul` API missing something AC0 trimmed.

## 6. Definition of done

- [ ] The 7 declarations public in `WeilExchange/GaloisRamification.lean`, statements
      verbatim; `restrictSmulValuationSubringEquiv`,
      `coe_restrictSmulValuationSubringEquiv_apply`, `ord_smul_eq` and
      `intertwinesAlong_one_ofAlgAut` `private`.
- [ ] `Place.restrict_ofAlgAut_smul` written once (the first node's private copy
      removed).
- [ ] Consumer Zone C extended or a new check added: `exists_algEquiv_smul_eq_of_restrict_eq`
      instantiated at some concrete Galois extension (or a documented abstract
      instantiation that all hypotheses accept — this is the FFG generic-kernel
      lesson: budget the *instantiation*, not the transcription).
- [ ] `spec/check_flt_statements.py`: the 7 AC wrappers in `SOURCES`; 0 mismatched,
      0 missing.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T3 section: cost, the `IsGaloisGroup` API record, and the
      wire-test choice.

## 7. Reporting back

Beyond the shared report: (1) which of the three mathlib API points needed a
restatement, and what it was; (2) whether the pin's duplicate
`restrict_ofAlgAut_restrictScalars_smul` was in fact the public node (it is) — i.e.
whether the pin's two copies are byte-identical or only propositionally equal;
(3) the wire-test instantiation and its cost.
