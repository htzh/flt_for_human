# Topic 10: the finite/free Hecke algebra and the integral structure

**Status: COMPLETE (2026-09-28) for its stated finiteness scope.** Third topic of
[SET-4](SET-4.md). The two self-contained definition modules landed in SET 4; the
theorem module was blocked there and is now delivered as
`FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean`. The unblocking was route C′
(`WeightOne/IntegralStructure.lean` supplies `HasIntegralStructure` for `2 ≤ k`)
plus the port's own Sturm bound (`SturmBound.lean` supplies
`ModularForm.sturm_bound_Gamma0`), exactly the two dependencies SET 4 recorded as
missing. The topic's §1 route note (the `χ₋₃` Eisenstein series) was **wrong** —
verified in §7 — and is superseded; the finiteness uses neither
`Def_CuspForm_IntegralLattice` nor the mod-`p` machinery. The pin's 4,308- and
212-line `_two` bodies were neither transcribed nor needed. The descoped
eigenbasis-span family is measured in §8: **56 theorem nodes / 25,362 `S_` lines**
plus ≈1,150 definition-module lines, of which one target is gated by the full
Eichler–Shimura isomorphism rather than by T10. **§9 decomposes that block into
three distinct blockers** — the dimensional one (Petersson/spectral),
`exists_cyclic_span_heckeAlgebra` (newform separation) and the E-S one — and
records that the dimensional block has four of its five inputs already in
place.

**Audience.** The work is done; §5 records the definition of done and §7 the
verified dependency analysis. Read [SET-4.md](SET-4.md) §0–§3 for the blocker
history and `logs/hecke-port.md` §T10 for the measured completion record.

**Goal — met.** Three modules:

- `FLTForHuman/ModularForms/Defs/EisensteinChiNegThree.lean` — the pin's 27-line
  `χ₋₃` Eisenstein vocabulary (`chiNegThree`, `sigmaChi`, `e1Chi3`, `e1Chi3In`,
  `E1Chi3IsModular`). ✅ SET 4; feeds route C′, not the finiteness.
- `FLTForHuman/ModularForms/Defs/IntegralLattice.lean` — the pin's 32-line
  weight-2 auxiliary lattice (`qIntegralSet`, `qIntegralLattice`,
  `HasIntegralBasis`, `bridgeProduct`, `IsLatticeRealized`). ✅ SET 4; still unused
  by the finiteness.
- `FLTForHuman/ModularForms/HeckeFiniteAlgebra.lean` — the targets:
  - `CuspForm.hasIntegralStructure_of_two_le` (route C′, not the pin's 515-line
    file) and its `hasIntegralStructure_two` special case; ✅
  - `CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra`,
    `CuspForm.HasIntegralStructure.moduleFree_heckeAlgebra`; ✅
  - `CuspForm.moduleFinite_heckeAlgebra` and `CuspForm.moduleFinite_heckeAlgebra_two`; ✅
  - `CuspForm.fg_toSubmodule_heckeAlgebra`,
    `CuspForm.finrank_span_heckeAlgebra_eq_finrank`; ✅
  - `CuspForm.span_heckeTLin_eigen_eq_top`,
    `CuspForm.heckeEvalForms_range_eq_top`,
    `CuspForm.exists_cyclic_span_heckeAlgebra`,
    `CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul`. ⛔ **still blocked** on the
    Petersson inner product / the newform separation / `Def_CuspForm_HeckeEvalForms`
    (see §7 and `logs/hecke-port.md` §T10).

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

**Complete (2026-09-28).** Verified by re-running the commands: the checker is
**1,418 identical (75 promoted), 0 mismatched, 0 missing, 17 own-proof** (1,435
port declarations); the full `lake build` is green, **4,341 jobs, 0 warnings**,
with no `sorry`/`admit` in any touched module; `#print axioms` on all ten
headlines is `propext, Classical.choice, Quot.sound`. The unblocking was route C′
(§7) plus the port's `SturmBound.lean`.

- [x] `Defs/EisensteinChiNegThree.lean` and `Defs/IntegralLattice.lean` created,
      verbatim (SET 4).
- [x] `HeckeFiniteAlgebra.lean` created; the targets verbatim. — the seven
      finiteness/span targets plus the weight-`k ≤ 1` subsingleton block; the
      `finrank` proof uses the `a₁` pairing, not Petersson.
- [x] `moduleFinite_heckeAlgebra_two` and `hasIntegralStructure_two` are the
      general theorems' special cases. — **measured**: `moduleFinite_heckeAlgebra_two
      = moduleFinite_heckeAlgebra N 2 S` (4,308 → 1 line) and
      `hasIntegralStructure_two = hasIntegralStructure_of_two_le N 2 le_rfl`
      (212 → 1 line). The 4,308- and 212-line pin bodies were not transcribed.
- [x] `timeout 180 lake build` green, 0 warnings, no `sorry`.
- [x] checker: the wrappers appended to `SOURCES`, the modules to `PORT_FILES`,
      **0 mismatched, 0 missing**. — ten T10 wrappers + `HeckeFiniteAlgebra.lean`.
- [x] `logs/hecke-port.md` §T10: the blocker, the 515-line proof's block
      structure, the missing-dependency list, and the completion record.
- [x] `README.md` rows, including the created `HeckeFiniteAlgebra.lean` row.
- [x] The three definition-module additions (`HeckeLattice`'s `intLattice_fg`/
      `_free_and_finite`, `HeckeQCoeff`'s `ModularFormClass.eq_of_forall_qCoeff_eq`)
      registered in `SOURCES`/`PORT_FILES`.

**Still open (out of T10's finiteness scope).** The eigenbasis-span targets
`span_heckeTLin_eigen_eq_top`, `heckeEvalForms_range_eq_top`,
`exists_cyclic_span_heckeAlgebra` and `exists_top_eq_heckeAlgebra_adjoin_smul`,
each on the prerequisite named in §7 and `logs/hecke-port.md` §T10. Their measured
price is in §8: **56 theorem nodes / 25,362 `S_` lines plus ≈1,150
definition-module lines**, and `heckeEvalForms_range_eq_top` is gated by the full
Eichler–Shimura isomorphism (the active driver), so it is not T10-specific work.

## 6. Reporting back

1. **The dedup, measured.** `moduleFinite_heckeAlgebra_two =
   moduleFinite_heckeAlgebra N 2 S`: the pin's 4,308-line standalone proof is one
   port line. `hasIntegralStructure_two = hasIntegralStructure_of_two_le N 2
   le_rfl`: 212 lines to one. `fg_toSubmodule_heckeAlgebra` is
   `Module.Finite.iff_fg.mp` of the first. Total **4,530 pin lines → 3 port
   lines**, with the finiteness itself written once from the lattice.
2. **The 515-line proof was replaced, not transcribed.** Route C′ proved
   `hasIntegralStructure_of_two_le` by the `Γ₁`-slash-basis trace (33.6k-line
   cone plus a 374-line capstone), avoiding route A's 263,720-line integral-
   structure cone and the pin's 515-line `_two`-era file entirely; the
   `χ₋₃`/`IntegralLattice` vocabulary the work order proposed is unused by it.
3. **No `latticeRestrict`/`heckeLocal` construction needed restating.** The
   lattice restriction is written inline in `moduleFinite_heckeAlgebra` (the
   `ψ` embedding, ~15 lines); it is private and has no public wrapper, so it is
   not promoted. `ModularFormClass.eq_of_forall_qCoeff_eq`, the one genuine pin
   theorem the topic consumes, *was* promoted publicly (its own wrapper exists).
4. **SET-5/Stage-D hand-off.** What is left of the Hecke port is §3.1 (Γ_H / Γ₁ /
   Atkin–Lehner) plus the eigenbasis-span family named in §5. The finiteness layer
   left no `private` helper behind: every helper in `HeckeFiniteAlgebra.lean` is
   private to it, and `HeckeLattice.lean`'s coefficient block is still private.

## 7. The verified blocker and the re-scope (SET 5)

**Landed (SET 4).** `Defs/EisensteinChiNegThree.lean` (46 lines, 5 public decls)
and `Defs/IntegralLattice.lean` (50 lines, 5 public decls); checker 792 → 802.
`HeckeFiniteAlgebra.lean` was absent in SET 4 and its theorem wrappers were not
appended to `SOURCES`. **Completed 2026-09-28**: `HeckeFiniteAlgebra.lean` exists
with the seven finiteness/span targets, the ten wrappers are in `SOURCES`, and the
checker is 1,418 / 0 / 0. The rest of this section is the SET-4 blocker analysis
that motivated route C′.

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
  (9,836) packages, `Def_CuspForm_ModPForms`, the Sturm bound). (Route A as a
  whole is not an Eichler–Shimura cone — most of the 657 nodes are endgame
  geometry; see [scout §0](../../../studies/eichler-shimura-scout.md).) This is **not a
  topic — it is most of the remaining FLT arithmetic tower** (the full cone is 657
  nodes / 263,720 S-lines across 102 definition modules). Do not attempt it.
- **Route B — the k=2 finiteness only.** (Correction 2026-09-27: route C′'s
  integrality already implies this finiteness, so route B is not needed for
  Hecke finiteness; its role is the weight-2 Eichler–Shimura map. See
  [../../../math/017-eichler-shimura-isomorphism.md](../../../math/017-eichler-shimura-isomorphism.md)
  §9.) `S_CuspForm_moduleFinite_heckeAlgebra_two.lean`
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
[../../../studies/route-c-prime-scout.md](../../../studies/route-c-prime-scout.md)
and the work order
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md).

**The two landed definition modules are prerequisites of the shortcut, not of
route B.** `Defs/EisensteinChiNegThree.lean` and `Defs/IntegralLattice.lean`
serve the mod-3 congruence / `HasIntegralBasis` route; the χ₋₃ weight-one
Eisenstein machinery (`EisensteinWeightOne.e1Chi3IsModular`) is the analytic
content of the C′ ingredient, so keep them — route B needs neither, but C′ does.
FLT's own `hasIntegralStructure_of_two_le` uses them at neither site.

## 8. Effort to finish the span family (measured 2026-09-28)

The finiteness half is complete; the four §5 eigenbasis-span targets are not.
Measured with `tools/deps/frontier.py` against the current port frontier (the
`Thm_` wrappers in `spec/check_flt_statements.py` plus the port tree's declared
names): a target's **needed** set is what its proof reaches that the port does not
yet provide.

| target | cone (nodes/lines) | needed | what the needed set is |
|---|---:|---:|---|
| `span_heckeTLin_eigen_eq_top` | 22 / 4,542 | 7 / 2,661 | the six `petersson_*` wrappers + itself |
| `heckeEvalForms_range_eq_top` | 1 / 45 | 1 / 45 | definition-gated, see below |
| `exists_cyclic_span_heckeAlgebra` | 101 / 32,046 | 54 / 25,295 | the eta-product / Atkin–Lehner / newform block |
| `exists_top_eq_heckeAlgebra_adjoin_smul` | 102 / 32,068 | 55 / 25,317 | the cyclic cone + itself |
| **union of the four** | | **56 / 25,362** | |

The union decomposes into two blocks plus the gate:

- **Petersson block — 7 nodes / 2,661 lines.** The six wrappers
  `CuspForm.petersson_{add_left, smul_left, conj_symm, self_re_nonneg,
  self_eq_zero_iff, heckeTLin}` (the last alone 1,156 lines) plus the 69-line
  target. This is the whole of `span_heckeTLin_eigen_eq_top`; it is also shared by
  the cyclic cone.
- **Cyclic block — 47 further nodes / 22,634 lines.** Led by
  `ModularForm.alSlash_add_heckeU_alSlash_alSlash` (2,388),
  `ModularForm.alSlash_heckeT_comm` (2,387) and
  `CuspForm.norm_lt_of_heckeTLin_eq_smul` (1,303), then the newform/rescale family
  (`IsNewform.rescaleLin_sub_rescaleLin_notMem_span_sup_span` 1,125,
  `mem_span_rescaleLin_prime_of_forall_coprime_qCoeff_eq_zero` 936,
  `exists_finite_separated_newform_family` 108, the Atkin–Lehner trace lemmas)
  and the eta-product / `Γ₀(11)` family (nine `etaProductEleven_*` /
  `exists_gamma0_*` / `eta_neg_one_div_sq` nodes at 875–928 lines each). By
  namespace the union is `CuspForm.` 43 / 13,418, `ModularForm.` 11 / 11,748, plus
  two small nodes.
- **`heckeEvalForms_range_eq_top` — 1 node / 45 lines.** A 45-line statement whose
  only import is `Definitions/Def_CuspForm_HeckeEvalForms` (49 lines), itself
  importing `Definitions/Def_HeckeGalois_EichlerShimura` (228 lines): the **full
  Eichler–Shimura isomorphism**, which is the active programme
  ([../../../studies/eichler-shimura-scout.md](../../../studies/eichler-shimura-scout.md)).
  This target is therefore not T10-specific; it lands with the E-S isomorphism.

**The theorem graph is not the whole price.** Ten definition modules used by these
cones are not registered in the checker (≈1,150 pin lines):

| module | pin lines | serves |
|---|---:|---|
| `Def_CuspForm_Petersson` | 30 | the Petersson block (with mathlib's `UpperHalfPlane` measure/integral) |
| `Def_CuspForm_Newforms` | 72 | the cyclic block |
| `Def_CuspForm_AtkinLehnerOperator` | 64 | the cyclic block |
| `Def_ModularForm_AtkinLehnerDatum` | 157 | the cyclic block |
| `Def_CuspForm_HeckeULower` | 46 | the cyclic block |
| `Def_CuspForm_LevelLoweringTrace` | 45 | the cyclic block |
| `Def_FreyPackage_ModMCarrier_Rescale` | 176 | the cyclic block |
| `Def_FreyPackage_ModMCarrier_OldSublattice` | 116 | the cyclic block |
| `Def_AutomorphicForm_FundamentalDomainVolume` | 178 | the cyclic block |
| `Def_AutomorphicForm_ModularFundamentalDomain` | 217 | the cyclic block |

**Reading of the measurement.** The finiteness half took the topic's three-round
budget; the span family it descoped is a second, comparable unit:
**56 theorem nodes / 25,362 `S_` lines plus ≈1,150 definition-module lines**, with
two caveats. First, the cyclic block's Atkin–Lehner / newform / eta layer belongs
to the Level / Γ_H port named in §6 (PORTING-Level), so part of those 47 nodes is
shared with that effort rather than marginal to T10. Second,
`heckeEvalForms_range_eq_top` should be struck from this topic and tracked under
the E-S programme: its 45 lines are free once the isomorphism lands.

Reproduce (the union needs all four targets, so a loop rather than four sums):

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from frontier import Frontier, needed
fr = Frontier(); pay = fr.pay
ported = fr.frontier('union')
targets = ['CuspForm.span_heckeTLin_eigen_eq_top', 'CuspForm.heckeEvalForms_range_eq_top',
           'CuspForm.exists_cyclic_span_heckeAlgebra', 'CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul']
un = set()
for t in targets:
    i = pay.pid(t)
    cone, nd = pay.closure(i), needed(pay.cites, i, ported=ported, terminal=True)
    un |= nd
    print(f"{t:<45} cone {len(cone):>4}/{pay.total_lines(cone):>6}  needed {len(nd):>3}/{pay.total_lines(nd):>6}")
print(f"UNION needed {len(un)} / {pay.total_lines(un)}")
PY
```

## 9. The block decomposed: dimensional vs cyclic vs E-S (2026-09-28)

The §5 "still open" list is three different blockers, not one. Measured with
`tools/deps/frontier.py` (frontier = the checker's verified `Thm_` wrappers
unioned with the port tree's declared names):

| target | cone (nodes/lines) | needed (unported) | what blocks it |
|---|---:|---:|---|
| `CuspForm.span_heckeTLin_eigen_eq_top` | 22 / 4,542 | 7 / 2,661 | the Petersson inner product (spectral decomposition) |
| `CuspForm.exists_cyclic_span_heckeAlgebra` | 101 / 32,046 | 54 / 25,295 | newform / Atkin–Lehner separation |
| `CuspForm.exists_top_eq_heckeAlgebra_adjoin_smul` | 102 / 32,068 | 55 / 25,317 | corollary of the cyclic target |
| `CuspForm.heckeEvalForms_range_eq_top` | 1 / 45 | 1 / 45 | `Def_CuspForm_HeckeEvalForms` → the E-S isomorphism |
| union of the four | | 56 / 25,362 | |

### 9.1 The dimensional block is a spectral decomposition

`span_heckeTLin_eigen_eq_top` (69 pin lines) is not a dimension count. It:

1. builds an `InnerProductSpace` on `S₂(Γ₀ M)` from `CuspForm.petersson`;
2. takes `CuspForm.finiteDimensional_Gamma0 M 2`;
3. notes each `T_ℓ = heckeTLin 2 ℓ` is self-adjoint (`petersson_heckeTLin`) and
   that they commute (`heckeTLin_comm`);
4. applies the joint spectral theorem
   `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute` — the simultaneous
   eigenspaces span `⊤`.

Input by input against the port:

| input | where it lives | status |
|---|---|---|
| joint spectral theorem | mathlib `Analysis/InnerProductSpace/JointEigenspace.lean` | available |
| `CuspForm.finiteDimensional_Gamma0` | `ModularForms/SturmBound.lean` (Sturm route, not the pin's sibling) | landed |
| `heckeTLin_comm` | `ModularForms/HeckeCommute.lean` | landed |
| `heckeTLin` + T8 eigenform interface | `HeckeOperatorForms.lean`, `HeckeEigenform.lean` | landed |
| `CuspForm.petersson` + five core axioms + `petersson_heckeTLin` | pin `Def_CuspForm_Petersson` + six wrappers | **missing** |
| `UpperHalfPlane.petersson`, hyperbolic measure, Bochner integral | mathlib | available |

So four of the five inputs are in place, and the only gap is the Petersson block:
`Def_CuspForm_Petersson` (30 lines; the integral of mathlib's
`UpperHalfPlane.petersson` over `ModularGroup.fd`), its five core axioms
(`petersson_{add_left,smul_left,conj_symm,self_re_nonneg,self_eq_zero_iff}`, pin
spans 290/288/288/285/285) and self-adjointness `petersson_heckeTLin` (1,156).
Measured: `needed 7 / 2,661`, none of it ported — the whole block, i.e. the
missing mathematics is the fundamental-domain integral and the change of
variables giving `⟨T_ℓ f, g⟩ = ⟨f, T_ℓ g⟩`.

### 9.2 The other two blocks are not dimensional

`exists_cyclic_span_heckeAlgebra` (275) is a separated-newform-family plus
"separating family ⇒ cyclic vector" argument (`exists_separator`,
`exists_cyclic_of_oldspan_of_separated`), importing `Def_CuspForm_Newforms` and
`Def_FreyPackage_ModMCarrier_Rescale`; `exists_top_eq_heckeAlgebra_adjoin_smul`
is its corollary. `heckeEvalForms_range_eq_top` (45) is gated by
`Def_CuspForm_HeckeEvalForms` → `Def_HeckeGalois_EichlerShimura`, i.e. the E-S
programme, and stays struck from this topic (§5, §8).

### 9.3 Why the algebraic dimension route stops here

The landed `finrank_span_heckeAlgebra_eq_finrank` gets the **dimension equality**
from the `a₁` pairing with no Petersson (an algebraic, non-positive-definite
form). The eigenbasis span cannot be obtained that way: the spectral theorem
needs a positive-definite form, so 9.1 genuinely needs the Petersson pairing.
The port therefore has the algebraic dimension half and is missing exactly the
analytic pairing for the diagonalization half.

### 9.4 Port order for the dimensional block (9.1)

1. `Def_CuspForm_Petersson` (30);
2. the five core axioms (~1,436 pin lines);
3. `petersson_heckeTLin` (1,156) — the fundamental-domain change of variables;
4. `span_heckeTLin_eigen_eq_top` (69) — the spectral assembly, engine from mathlib.

Then 9.2 is a separate effort (newform separation), and 9.3 belongs to the E-S
programme, not to T10.

Reproduce:

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from frontier import Frontier, needed
fr = Frontier(); pay = fr.pay; ported = fr.frontier('union')
for t in ['CuspForm.span_heckeTLin_eigen_eq_top',
          'CuspForm.exists_cyclic_span_heckeAlgebra',
          'CuspForm.heckeEvalForms_range_eq_top']:
    i = pay.pid(t); C = pay.closure(i)
    nd = needed(pay.cites, i, ported=ported, terminal=True)
    print(f"{t:<45} cone {len(C):>4}/{pay.total_lines(C):>6}  needed {len(nd):>3}/{pay.total_lines(nd):>6}")
PY
```
