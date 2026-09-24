# Topic 10: the finite/free Hecke algebra and the integral structure

**Status: BLOCKED (2026-09-23), re-scoped to SET 5.** Third topic of
[SET-4](SET-4.md). The two self-contained definition modules landed; the theorem
module was **not** created, because the general theorems the two one-liners
specialise are themselves out of SET-4 scope: `hasIntegralStructure_of_two_le`
imports `Def_CuspForm_ModPForms`, `Def_HeckeEis_BinaryFormRep`,
`Def_Gamma0CoeffCohomology`, `Def_Gamma0HeckeOperatorHom` and ten
`Thm_HeckeEis_*`/`Thm_CuspForm_*` Eichler–Shimura/period-package wrappers, none of
which the port has. This topic's §1 route note (the `χ₋₃` Eisenstein series) was
**wrong** — verified in §7 — and is superseded. T10 is now an infrastructure topic
for SET 5; the pin's 4,308- and 212-line `_two` bodies were neither transcribed
nor needed.

**Audience.** A fresh session taking up the **re-scoped** T10 (SET 5). Read
[SET-4.md](SET-4.md) §0–§3 and §7 below first — the blocker, not the original
sketch, is the specification.

**Goal.** Three modules:

- `FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean` — the pin's 27-line
  `χ₋₃` Eisenstein vocabulary (`chiNegThree`, `sigmaChi`, `e1Chi3`, `e1Chi3In`,
  `E1Chi3IsModular`).
- `FLTForHuman/ModularForms/Defs/IntegralLattice.lean` — the pin's 32-line
  weight-2 auxiliary lattice (`qIntegralSet`, `qIntegralLattice`,
  `HasIntegralBasis`, `bridgeProduct`, `IsLatticeRealized`).
- `FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean` — the targets:
  - `CuspForm.hasIntegralStructure_of_two_le` (515 pin lines) and its
    `hasIntegralStructure_two` special case;
  - `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`,
    `CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra`;
  - `CuspForm.moduleFinite_heckeAlgebra` and `CuspForm.moduleFinite_heckeAlgebra_two`;
  - `CuspForm.fg_toSubmodule_heckeAlgebra`,
    `CuspForm.span_heckeTLin_eigen_eq_top`,
    `CuspForm.finrank_span_heckeAlgebra_eq_finrank`,
    `CuspForm.heckeEvalForms_range_eq_top`,
    `CuspForm.exists_cyclic_span_heckeAlgebra`,
    `CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul`.

## 1. Why this topic, and what is settled — the headline dedup

**Two of the pin's largest files are special cases of the general theorems.**

- `CuspForm.moduleFinite_heckeAlgebra_two (N) [NeZero N] (S) : Module.Finite ℤ (heckeAlgebra N 2 S)`
  **is** `CuspForm.moduleFinite_heckeAlgebra N 2 S`. The pin's `S_` file for the
  `_two` form is **4,308 lines** and re-derives the whole Hecke analytic/`repMat`/
  `heckeSlashSum` machinery the port already has in `HeckeAnalytic.lean` and
  `HeckeOperatorForms.lean`. Do **not** transcribe it; prove `_two` from the
  general theorem (or, if a defeq step resists, `exact moduleFinite_heckeAlgebra N 2 S`).
- `CuspForm.hasIntegralStructure_two (N) [NeZero N] : HasIntegralStructure N 2`
  **is** `hasIntegralStructure_of_two_le N 2 le_rfl`. The pin's 212-line file is
  the `k = 2` instance of the 515-line general theorem.

If both one-liners hold, this topic removes ≈4,520 pin lines for ≈2 port lines —
the largest single redundancy found in the effort. Verify the statements match
(the checker will), then record the counts.

The real work is therefore:

- **`hasIntegralStructure_of_two_le`** (515 pin lines): the full-rank existence,
  via the weight-2 lattice and the `χ₋₃` Eisenstein series. It needs the
  `IntegralLattice` vocabulary, `Def_ModularForm_EisensteinChiNegThree` and
  mathlib's modular-forms analysis. Budget for it; it is the topic's one hard
  proof.
- **`HasIntegralStructure.moduleFinite/Free_heckeAlgebra`** (49 + 17): the
  lattice is full-rank, hence the Hecke algebra acting on it is finite (and free,
  over `ℤ` torsion-free) as a `ℤ`-module. This is `Submodule`/`Module.Finite`
  bookkeeping once `HasIntegralStructure` is in hand; the `latticeRestrict`/
  `latticeActionHom` constructions live in the pin's `Def_CuspForm_HeckeLocal`
  family and may need a local `private` restatement — record it.
- **`moduleFinite_heckeAlgebra`** (78): the general `Module.Finite`, from
  `hasIntegralStructure_of_two_le` (T9's hypothesis shape) plus
  `HasIntegralStructure.moduleFinite_heckeAlgebra`.
- **The eigenbasis span family** (`span_heckeTLin_eigen_eq_top` 69,
  `finrank_span_heckeAlgebra_eq_finrank` 223, `heckeEvalForms_range_eq_top` 45,
  `exists_cyclic_span_heckeAlgebra` 275, `exists_top_eq_heckeAlgebra_adjoin_smul` 22,
  `fg_toSubmodule_heckeAlgebra` 10): these use T8's eigenform interface
  (`IsNormalizedEigenform`, the simultaneous-eigenvector characterisations) and the
  finite-dimensionality of the cusp-form space. Run T8 before T10 if it is not
  already done.

**Superseded — the `χ₋₃` route was wrong (verified).** The original note here said
`hasIntegralStructure_of_two_le` is reached through the `χ₋₃` Eisenstein series and
`Def_CuspForm_IntegralLattice`. That is false: `grep -c` for
`qIntegralSet`/`bridgeProduct`/`IsLatticeRealized`/`E1Chi3` in the pin's
`S_CuspForm_hasIntegralStructure_of_two_le.lean` is **0**. The `χ₋₃` vocabulary is
real but belongs to the mod-3 congruence machinery, not to the integral-structure
existence. Both definition modules were ported anyway (they are the pin's, and a
later topic will want them), but the theorem module was correctly left unstarted.

**Settled: do not open the mod-`p`/galois machinery.** `Def_CuspForm_ModPForms`,
`Def_CuspForm_HeckeGaloisRepDatum`, `Def_CuspForm_HeckeLocal` beyond the two
lattice constructions are out of scope; if a target needs them, stop and report.

## 2. The scouted inventory

| target | pin file (lines) | note |
|---|---|---|
| `chiNegThree`, `sigmaChi`, `e1Chi3`, `e1Chi3In`, `E1Chi3IsModular` | `Def_ModularForm_EisensteinChiNegThree` (27) | definitions |
| `qIntegralSet`, `qIntegralLattice`, `HasIntegralBasis`, `bridgeProduct`, `IsLatticeRealized` | `Def_CuspForm_IntegralLattice` (32) | definitions |
| `CuspForm.hasIntegralStructure_of_two_le` | 515 | **the hard proof** |
| `CuspForm.hasIntegralStructure_two` | 212 | → one-liner from the general |
| `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra` | 49 | lattice full-rank ⇒ finite |
| `CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra` | 17 | ⇒ free over `ℤ` |
| `CuspForm.moduleFinite_heckeAlgebra` | 78 | general `Module.Finite` |
| `CuspForm.moduleFinite_heckeAlgebra_two` | **4,308** | → one-liner from the general |
| `CuspForm.fg_toSubmodule_heckeAlgebra` | 10 | f.g. submodule |
| `CuspForm.span_heckeTLin_eigen_eq_top` | 69 | eigenforms span |
| `CuspForm.finrank_span_heckeAlgebra_eq_finrank` | 223 | the span is everything |
| `CuspForm.heckeEvalForms_range_eq_top` | 45 | the abstract → concrete evaluation is onto |
| `CuspForm.exists_cyclic_span_heckeAlgebra` | 275 | cyclic vector |
| `CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul` | 22 | the `ℂ`-adjoin form |

The two statements that must be checked for the one-liners:

```lean
theorem CuspForm.moduleFinite_heckeAlgebra (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N k S)
theorem CuspForm.moduleFinite_heckeAlgebra_two (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S)          -- = … N 2 S
theorem CuspForm.hasIntegralStructure_of_two_le (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 2 ≤ k) :
    HasIntegralStructure N' k
theorem CuspForm.hasIntegralStructure_two (N : ℕ) [NeZero N] :
    CuspForm.HasIntegralStructure N 2                        -- = … N 2 le_rfl
```

Route notes:

- `hasIntegralStructure_of_two_le` is proved by exhibiting a basis (or spanning
  set) of the cusp-form space made of `q`-integral forms; the pin uses
  `qIntegralSet`/`qIntegralLattice`, `bridgeProduct` (`PowerSeries.mk a * e1Chi3In R`)
  and `IsLatticeRealized`, with the `χ₋₃` Eisenstein series supplying the
  non-cusp part. Read the pin's `S_` file in blocks; it is the one place to spend
  a scouting round.
- `HasIntegralStructure.moduleFinite_heckeAlgebra` takes
  `(hN : HasIntegralStructure N k) (hk : 1 ≤ k)` and concludes `Module.Finite ℤ`
  of the algebra; `moduleFree_heckeAlgebra` is the same with `Module.Free` and
  needs `IsAddTorsionFree`/`Module.free_of_finite_type_torsion_free'`.
- The `latticeRestrict`/`latticeActionHom`/`heckeLatticeAlgebra` definitions the
  two instances use are in the pin's `Def_CuspForm_HeckeLocal` family; if they are
  not in the port, restate the *construction* locally as `private` (the T4
  `upperTriangularGL` promotion is the alternative if a wrapper names it).
- The eigenbasis family needs T8 (the `IsNormalizedEigenform` interface) and
  T7's `heckeAlgebra`; `exists_cyclic_span_heckeAlgebra` (275) is the longest.

## 3. What is different about this topic

- **It carries the effort's largest dedup** (4,520 pin → ≈2 port lines) *and* its
  hardest remaining transcription (the 515-line integral-structure existence).
  Separate the two in the log.
- **It is the first topic stated over `ℤ`-modules and `Subalgebra`.** Expect
  `Module.Finite`/`Free` bookkeeping rather than `ℂ`-analysis, except for the one
  515-line proof.
- **The one-liners are a claim to test, not assume.** If `moduleFinite_heckeAlgebra_two`
  does not close by `exact` (a defeq or binder mismatch), do **not** fall back to
  the 4,308-line file: report the mismatch and let the reviewer decide.
- **T8 is a soft prerequisite** for the span family; if T8 has not landed, port
  the finiteness half and leave the span family with a clear note.

## 4. Budget

**3 goal rounds, checkpoint at 1.** Round 1: the two definition modules and a
scout of `hasIntegralStructure_of_two_le`'s block structure. Round 2: the integral
structure and the `Module.Finite`/`Free` family (including the two one-liners).
Round 3: the eigenbasis span family and bookkeeping.

**Stop early on**: a one-liner that will not close (report, do not transcribe the
4,308-line file); `hasIntegralStructure_of_two_le` needing the mod-`p`/galois
machinery; or a `Module.Finite` proof needing a `Private` construction that has no
public wrapper.

## 5. Definition of done

**Blocked at the scouting gate (2026-09-23); re-scoped to SET 5 (§7).** Reviewed
and verified by the reviewer: the two definition modules are green and correct,
the theorem module is absent with no `sorry` anywhere, the checker is **802
identical, 0 mismatched, 0 missing**, and the blocker (`Def_CuspForm_ModPForms` +
the HeckeEis/Eichler–Shimura/period package, plus the missing Sturm bound and
Petersson infrastructure) is confirmed against the pin's imports. Stopping was
the right call: the one-liners could not even be *stated*.

- [x] `Defs/EisensteinChiNegThree.lean` and `Defs/IntegralLattice.lean` created,
      verbatim.
- [ ] `HeckeFiniteAlgebra.lean` created; the targets verbatim. — **blocked**; do
      not attempt in SET 4. The re-scope is §7.
- [ ] `moduleFinite_heckeAlgebra_two` and `hasIntegralStructure_two` are the
      general theorems' special cases, … — **not measured**: the general theorems
      were not ported. The 4,308- and 212-line pin bodies were not transcribed
      (the correct outcome).
- [x] `timeout 180 lake build` green, 0 warnings, no `sorry`.
- [ ] checker: the wrappers appended to `SOURCES`, the three modules to
      `PORT_FILES`, **0 mismatched, 0 missing**. — only the two definition modules
      are registered; the theorem wrappers are correctly absent.
- [x] `logs/hecke-port.md` §T10: the blocker, the 515-line proof's block
      structure, and the missing-dependency list.
- [x] `README.md` rows, including the explicit "(not created) blocked" row.

## 6. Reporting back

1. **The dedup, measured**: pin lines vs port lines for the `_two` and
   `hasIntegralStructure_two` one-liners.
2. **The 515-line proof**: its block structure and where it actually bit.
3. Any `latticeRestrict`/`heckeLocal` construction that had to be restated
   locally, and whether it should be promoted instead.
4. The SET-5 hand-off: what is left (Tiers 2–4) and any `private` helper the
   eigenform/finiteness layer left behind.

## 7. The verified blocker and the re-scope (SET 5)

**Landed (committed to the tree, not to `SOURCES` for the missing module).**
`Defs/EisensteinChiNegThree.lean` (46 lines, 5 public decls) and
`Defs/IntegralLattice.lean` (50 lines, 5 public decls); `HeckeFiniteAlgebra.lean`
does not exist. Checker 792 → 802 on the two definition modules' names; the T10
theorem wrappers were **not** added to `SOURCES` because there is no port
declaration to verify.

**The blocker, verified by the reviewer against the pin.**
`P2M/Sol/S_CuspForm_hasIntegralStructure_of_two_le.lean` imports:

```
Definitions.Def_CuspForm_ModPForms
Definitions.Def_CuspForm_IntegralStructure
Definitions.Def_CuspForm_HeckeAlgebra
Definitions.Def_ModularForm_HeckeOperatorForms
Definitions.Def_HeckeEis_BinaryFormRep
Definitions.Def_Gamma0CoeffCohomology
Definitions.Def_Gamma0HeckeOperatorHom
Theorems.Thm_CuspForm_linearIndependent_complex_of_linearIndependent_int_of_periodPackage
Theorems.Thm_CuspForm_hasIntegralStructure_of_moduleFinite_of_linearIndependent
Theorems.Thm_HeckeEis_exists_coeffH1par_map_ringHom
Theorems.Thm_HeckeEis_exists_basis_coeffH1par_int_complex
Theorems.Thm_HeckeEis_span_range_coeffH1par_map_int_complex_eq_top
Theorems.Thm_HeckeEis_exists_coeffH1par_linearMap_coeffHeckeFun
Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
Theorems.Thm_HeckeEis_coeffH1par_map_heckeT_comm
Theorems.Thm_HeckeEis_exists_eichlerShimura_coeffH1par_binaryFormRepSL_forall_prime
Theorems.Thm_CuspForm_conjForm_heckeTLin_heckeULin_comm
```

None of that vocabulary is in the port (`grep -rl
coeffH1par/HeckeEis/ModPForms/Petersson/sturm_bound` = 0). The other general
targets are blocked behind the same wall: `moduleFinite_heckeAlgebra`'s `2 ≤ k`
branch calls `hasIntegralStructure_of_two_le`; `HasIntegralStructure.moduleFinite_heckeAlgebra`
needs `intLattice_fg`, i.e. the Sturm bound (`ModularForm.sturm_bound_Gamma0`),
absent from mathlib `v4.34.0`; the eigenbasis family needs the Petersson inner
product and `CuspForm.finiteDimensional_Gamma0`; `heckeEvalForms_range_eq_top`
needs `Def_CuspForm_HeckeEvalForms`, which imports
`Def_HeckeGalois_EichlerShimura`.

**Re-scope (corrected after measuring the cones).** There are **two independent
routes** and the original re-scope picked the wrong one.

- **Route A — general/`HasIntegralStructure`.** `hasIntegralStructure_of_two_le`
  (657 nodes / **263,720** S-lines), `hasIntegralStructure_two` (593 / **247,788**)
  and even `linearIndependent_complex_of_linearIndependent_int` (329 lines,
  582 nodes / **241,702**) all drag in the Eichler–Shimura/cohomology comparison
  (`AlgebraicCurve.residueTheoremK_ratFunc_of_isAlgClosed` 13,170,
  `WeierstrassCurve.velu_*` 11,992, the `HeckeEis` (12,683) and `PeriodPair`
  (9,836) packages, `Def_CuspForm_ModPForms`, the Sturm bound). This is **not a
  topic — it is most of the remaining FLT arithmetic tower** (the full cone is 657
  nodes / 263,720 S-lines across 102 definition modules). Do not attempt it.
- **Route B — the k=2 finiteness only.** `S_CuspForm_moduleFinite_heckeAlgebra_two.lean`
  is **standalone**: it imports only `Mathlib`,
  `Def_CuspForm_HeckeAlgebra`, `Def_FLTPrelim_Modularity`,
  `Def_PowerSeries_FormalHeckeOperators` (all three already ported by T5/T7/T8)
  and builds its own `heckeAlgebraIntFull` (line 1620) and
  `heckeTripleAlgebraFull` (4095) to prove
  `module_finite_heckeAlgebraIntFull_unconditional`. Its graph closure is **1
  node** — no Eichler–Shimura. Of its 4,308 lines, only the ~68-line tail
  (4240–4308: `heckeUSlashSum_eq_heckeU`, `heckeSlashSum_eq_heckeT`,
  `heckeTLin_eq_heckeHom`, `heckeULin_eq_heckeUHom`) duplicates the port's
  operator API and dedups; the `heckeAlgebraIntFull`/`heckeTripleAlgebraFull`
  core is genuinely new. **This is the route SET 5 should take**: one (large)
  topic, self-contained, giving `Module.Finite ℤ (heckeAlgebra N 2 S)` without
  the tower.

**The two one-liners are only one-liners on route A.** `moduleFinite_heckeAlgebra_two
= moduleFinite_heckeAlgebra N 2 S` holds as a Lean term, and
`hasIntegralStructure_two = hasIntegralStructure_of_two_le N 2 le_rfl` likewise —
but route A is the 263k-line programme, so paying it to dedup a 4,308-line block
is the wrong trade. On route B the block is **kept** (not deduped) and becomes the
*definition* of the k=2 finiteness. `HasIntegralStructure` itself is reachable on
neither A-as-budgeted nor B, but the shortcut **holds**: scouted 2026-09-24, the
general-weight slash form
`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` plus a short
**trace lemma** (coset sums over `Γ₁ ⊴ Γ₀`, not the Sturm bound) gives
`HasIntegralStructure N k` for all `k`; 53 nodes / 33,719 raw lines standalone,
and every node already lies inside the endgame's weight-one
`FLT.No2BridgeWiring` branch, so the marginal cost there is just the lemma. The
brief's `exists_basis_gamma1_qCoeff_mem_range_intCast` does not exist and the
`+ small Sturm` / "287-line cone" is superseded. See
[../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md).

**The two landed definition modules are prerequisites of the shortcut, not of
route B.** `Defs/EisensteinChiNegThree.lean` and `Defs/IntegralLattice.lean`
serve the mod-3 congruence / `HasIntegralBasis` route; the χ₋₃ weight-one
Eisenstein machinery (`EisensteinWeightOne.e1Chi3IsModular`) is the analytic
content of the C′ ingredient, so keep them — route B needs neither, but C′ does.
FLT's own `hasIntegralStructure_of_two_le` uses them at neither site.
