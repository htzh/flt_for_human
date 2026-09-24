# Coverage and routes: the Hecke-algebra finiteness targets

Measured report, 2026-09-23, after the `ModularCurve` Hecke-layer effort closed
([mc-retrospective.md](../lean/topics/mc-retrospective.md)) and the `base/003`
cusp-form-vanishing port landed
([level2-cusp-port.md](../lean/logs/level2-cusp-port.md)). Companion records:
[PORTING-Hecke.md](../lean/topics/PORTING-Hecke.md) §3.2 (the decision to stop),
[hecke/TOPIC-t10-finite-algebra.md](../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
§7 (the two-route re-scope) and [hecke-port.md](../lean/logs/hecke-port.md) §T10
(the verified blocker). It answers one question with numbers:

> The finiteness half of the Hecke face was declared out of scope. If the port is
> eventually pushed to the **endgame** — at least the **T side of `R = T`** — which
> route is right, and is the "cheap" `k = 2` route ever reusable?

FLT is read from the local clone pinned at `aa2d8b3`; all citations are public
URLs at that sha. The port's mathlib is `v4.34.0`; the `base/` notes cite
`v4.33.0`, one minor version behind, and for this subject the drift is
proof-level only (e.g. `CuspForm` no longer extending `ModularForm`). Conventions
are those of [../AGENTS.md](../AGENTS.md).

"Closure" always means the number of **theorem nodes** in the FLT citation graph
reached by the declaration, not lines. §8 reproduces every number.

## 0. What "finiteness" means here

Three families were scoped as SET 4's T10 and stopped:

1. **The Hecke algebra as a `ℤ`-module.** FLT's `CuspForm.heckeAlgebra N k S` is
   an `Algebra.adjoin ℤ` of the Hecke operators; the targets are
   `Module.Finite ℤ (CuspForm.heckeAlgebra N k S)` and its `Module.Free`
   companion.
2. **The integral structure.** `CuspForm.HasIntegralStructure N k` says the
   `ℤ`-span of the cusp forms with integral `q`-coefficients spans the complex
   cusp-form space. It is the hypothesis from which (1) follows.
3. **The eigenbasis span family.** The simultaneous Hecke eigenvectors span
   `S_k(Γ₀ N)`, the abstract Hecke evaluation is onto, and there is a cyclic
   vector. These use the T8 eigenform interface (already ported) rather than the
   Eichler–Shimura tower.

The four headline statements, verbatim from their `Theorems/` wrappers:

```lean
theorem CuspForm.moduleFinite_heckeAlgebra (N : ℕ) [NeZero N] (k : ℤ) (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N k S)
theorem CuspForm.moduleFinite_heckeAlgebra_two (N : ℕ) [NeZero N] (S : Set ℕ) :
    Module.Finite ℤ (CuspForm.heckeAlgebra N 2 S)
theorem CuspForm.hasIntegralStructure_of_two_le (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 2 ≤ k) :
    HasIntegralStructure N' k
theorem CuspForm.hasIntegralStructure_two (N : ℕ) [NeZero N] :
    CuspForm.HasIntegralStructure N 2
```

The decision is **not** "which route is cheaper per node". It is "will the
Eichler–Shimura tower be ported anyway?". The rest of this note measures that.

## 1. The measured targets

| declaration | pin file | pin lines | graph closure | consumers |
|---|---|---|---|---|
| `moduleFinite_heckeAlgebra_two` | `S_CuspForm_moduleFinite_heckeAlgebra_two` | **4,308** | **1** | 44 |
| `hasIntegralStructure_two` | `S_CuspForm_hasIntegralStructure_two` | 212 | **593** | 54 |
| `hasIntegralStructure_of_two_le` | `S_CuspForm_hasIntegralStructure_of_two_le` | 515 | **657** | 13 |
| `moduleFinite_heckeAlgebra` | `S_CuspForm_moduleFinite_heckeAlgebra` | 78 | **669** | 6 |
| `HasIntegralStructure.moduleFinite_heckeAlgebra` | `S_CuspForm_HasIntegralStructure_moduleFinite_heckeAlgebra` | 49 | **18** | 22 |
| `HasIntegralStructure.moduleFree_heckeAlgebra` | `S_CuspForm_HasIntegralStructure_moduleFree_heckeAlgebra` | 17 | **19** | 2 |
| `CuspForm.intLattice_fg` | `S_CuspForm_intLattice_fg` | 116 | **9** | 13 |
| `ModularForm.sturm_bound_Gamma0` | `S_ModularForm_sturm_bound_Gamma0` | 26 | **7** | 9 |
| `ModularForm.sturm_bound_of_isArithmetic` | `S_ModularForm_sturm_bound_of_isArithmetic` | 29 | **6** | 2 |
| `CuspForm.finiteDimensional_Gamma0` | `S_CuspForm_finiteDimensional_Gamma0` | 14 | **7** | 38 |

The raw-line cones (from [PORTING-Hecke.md](../lean/topics/PORTING-Hecke.md) §3.2)
make the same split in the other unit: `hasIntegralStructure_of_two_le` is **657
nodes / 263,720 raw `S_` lines**, `moduleFinite_heckeAlgebra` **669 / 264,296**,
and even the 329-line `linearIndependent_complex_of_linearIndependent_int` is
**582 / 241,702**.

The **eigenbasis span family** is a separate, mostly cheap cluster:

| target | closure |
|---|---|
| `CuspForm.heckeEvalForms_range_eq_top` | **1** |
| `CuspForm.fg_toSubmodule_heckeAlgebra` | **2** |
| `CuspForm.finrank_span_heckeAlgebra_eq_finrank` | **15** |
| `CuspForm.span_heckeTLin_eigen_eq_top` | **22** |
| `CuspForm.exists_cyclic_span_heckeAlgebra` | **101** |

## 2. FLT proves both finiteness statements twice

The `k = 2` statements are, statement-for-statement, the `k = 2` specialisations
of the general ones: `moduleFinite_heckeAlgebra_two N S` is
`moduleFinite_heckeAlgebra N 2 S`, and `hasIntegralStructure_two N` is
`hasIntegralStructure_of_two_le N 2 le_rfl`. FLT proves each pair
**independently**:

- `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` imports only `Mathlib`,
  `Def_CuspForm_HeckeAlgebra`, `Def_FLTPrelim_Modularity` and
  `Def_PowerSeries_FormalHeckeOperators` — all already ported — and cites **no**
  theorem node (closure 1). The general 78-line file never mentions `_two`.
- `hasIntegralStructure_two` is not a one-liner in FLT: it is a separate 212-line
  proof that imports `Thm_CuspForm_linearIndependent_complex_of_linearIndependent_int`,
  `Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank`,
  `Thm_CuspForm_moduleFinite_heckeAlgebra_two` and `Thm_CuspForm_finiteDimensional_Gamma0`.
- Checked both directions in the graph: neither `moduleFinite_heckeAlgebra_two`
  nor `hasIntegralStructure_two` lies in the closure of
  `hasIntegralStructure_of_two_le` or `moduleFinite_heckeAlgebra`, and the cheap
  side does not cite the general side.
- The standalone file's bespoke constructions `heckeAlgebraIntFull` (line 1620)
  and `heckeTripleAlgebraFull` (line 4095) are referenced by **no other file in
  FLT**.

So the cheap and expensive sides are two disjoint proofs of the same statements.
The port can exploit the equality either way; FLT did not.

## 3. The endgame verdict: the expensive side is unavoidable

`FLT.fermatLastTheorem` has a closure of **29,488** nodes. All four finiteness
statements lie inside it, and **every one of their consumers** is inside it too
(44/44, 54/54, 13/13, 6/6). The consumers of the **general** forms are exactly the
general-weight nodes a T-side port needs:

| consumer of `hasIntegralStructure_of_two_le` | its closure |
|---|---|
| `CuspForm.heckeLocal.exists_patchingDatum_of_isResiduallyModular_of_level_of_inertia_moves_torsion_of_eq_three_of_not_cube_dvd_of_level_not_cube_dvd` | 22,981 |
| `CuspForm.heckeLocal.exists_patchingDatum_of_isResiduallyModular_of_level_of_not_sq_dvd_of_not_cube_dvd_of_level_not_cube_dvd` | 22,657 |
| `CuspForm.heckeLocal.bijective_and_exists_presentation_of_ordinaryCondition_of_finiteAt_of_not_cube_dvd` | 12,168 |
| `WeierstrassCurve.exists_ideal_heckeAlgebra_two_or_succ_of_ideal_heckeAlgebra_pow_mul_apOfModel_of_inertia_moves_torsion_of_katz_of_eq_three` | 5,558 |
| `GaloisRep.exists_inertia_eigenvector_tameCharacter_pow_of_theta_heckeT_eq_zero_of_det_eq_pow_of_eq_two` | 2,584 |
| `ModPForms.dimFormulaCusp_le_finrank_modPCusp` | 663 |

and for `moduleFinite_heckeAlgebra`:

| consumer | its closure |
|---|---|
| `WeierstrassCurve.isModularModelOfLevel_div_of_isGoodPrimeFor_of_dvd_of_not_sq_dvd` | 3,974 |
| `CuspForm.heckeLocal.exists_moduleFinite_dvr_isNewform_chig_iota_isUnit_of_isOrdinaryAt_of_algHom` | 2,660 |
| `GaloisRep.exists_galoisFactorsThroughFiniteLevel_trace_eq_theta_heckeT_and_det_eq_pow` | 1,486 |
| `GaloisRep.exists_finiteField_galoisRep_trace_eq_heckeT_mod_of_isMaximal` | 1,458 |

Two consequences follow, and they settle the question:

- **The general statement is needed, not only the proof.** These consumers use
  `hasIntegralStructure_of_two_le` at general `k ≥ 2` (patching/Taylor–Wiles
  datums, the `ModPForms` dimension formula), so a `k = 2` result cannot
  substitute. The tower is on the critical path.
- **The expensive side cannot use the cheap side.** Verified above: no citation
  either direction, and the cheap file's constructions are file-local. So the
  cheap side is not a component of the expensive side.

**Therefore, for an endgame-complete port, the cheap standalone proofs are
throwaway.** Once the general side lands, `moduleFinite_heckeAlgebra_two` and
`hasIntegralStructure_two` are `exact general N 2 …`. The 4,308 + 212 lines would
be written and then deleted.

This holds with one scope caveat. The paused Hecke face
([PORTING-Hecke.md](../lean/topics/PORTING-Hecke.md) §3.2) explicitly declares the
Eichler–Shimura/cohomology tower out of scope; within that bounded effort Route B
is the **only** finiteness available and is the terminal artifact, not throwaway.
The verdict above is about the endgame, not about that effort.

## 4. The Sturm bound is a small leaf, not the bottleneck

The phrase "the Sturm bound is absent from mathlib" in the T10 record needs one
correction: mathlib has the **level-one** Sturm bound
(`ModularForm.sturm_bound_levelOne`, `ModularForm.sturm_bound_levelOne_nat`, in
`Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean`). What is
absent is the **arithmetic-level** form, and FLT's is small:

- `ModularForm.sturm_bound_of_isArithmetic` — 29 lines, closure **6**. It reduces
  to `Subgroup.IsArithmetic.exists_nat_mem_strictPeriods_conj`,
  `ModularForm.eq_zero_of_lt_order_qExpansion_of_isArithmetic` (closure 3) and
  `UpperHalfPlane.qExpansion_coeff_nat_mul`.
- `ModularForm.sturm_bound_Gamma0` — 26 lines, closure **7**; it cites only the
  arithmetic form (the `(Γ₀ N).index` in its statement is `Subgroup.index`, a
  definition, not a theorem value — mathlib has only
  `instFiniteIndexGamma0 : (Gamma0 N).FiniteIndex`).

Where it enters finiteness is one short chain:
`HasIntegralStructure.moduleFinite_heckeAlgebra` (closure 18) →
`intLattice_fg` (closure 9) → `sturm_bound_Gamma0` (closure 7),
with `intLattice_fg` also needing `CongruenceSubgroup.one_mem_strictPeriods_Gamma0`
(closure 1, indeg 46 — a widely wanted leaf), and the `Module.Free` sibling at
closure 19. That whole sub-cone is about **18 nodes**.

**Status (2026-09-23): the Sturm bound half is ported.** The eight declarations of
the cone above are in `FLTForHuman/ModularForms/QExpansionOrder.lean` and
`SturmBound.lean`, verified (checker 1,256 identical, 0 mismatched, 0 missing);
`CuspForm.intLattice_fg` and the two
`HasIntegralStructure.moduleFinite/Free_heckeAlgebra` instances remain. The
mathematics is in [../math/012-sturm-bound.md](../math/012-sturm-bound.md), the
record in [../lean/logs/sturm-bound-port.md](../lean/logs/sturm-bound-port.md).

This matters because `moduleFinite_heckeAlgebra`'s own proof cites
`HasIntegralStructure.moduleFinite_heckeAlgebra`. **Sturm is therefore on the
expensive route's critical path too** — it is a small, cheap prerequisite of both
routes, not an alternative to either.

A third route exists only as a **port proposal**, not an FLT proof:
`exists_basis_gamma1_qCoeff_mem_range_intCast` plus the small
`sturm_bound_of_isArithmetic` would give an explicit integral spanning family,
reaching `hasIntegralStructure_of_two_le` without the Eichler–Shimura tower. The
T10 brief measures that cone at ~287 nodes against 657, but it has not been
scouted, so it may or may not hold. This is the only route on which Sturm is
"the next thing" rather than a step inside a larger plan.

## 5. The route decision

| route | content | cost | reusable by the endgame? |
|---|---|---|---|
| **A — general** | `hasIntegralStructure_of_two_le` (657) then `moduleFinite_heckeAlgebra` (669); `_two` statements as one-liners | 263k+ raw `S_` lines, the Eichler–Shimura/`HeckeEis`/`PeriodPair`/`ModPForms` tower | it **is** the endgame route; mandatory |
| **B — standalone `k = 2`** | transcribe `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` (4,308 lines) | closure 1, but 4,308 written lines | **no** — replaced by one-liners once A lands |
| **C — reusable sub-cone** | Sturm + `intLattice_fg` + `HasIntegralStructure.moduleFinite/Free_heckeAlgebra` (closure 18–19) | ~18 nodes | **yes** — it is on A's path |
| **C′ — proposed shortcut** | `exists_basis_gamma1_qCoeff_mem_range_intCast` + small Sturm → `hasIntegralStructure_of_two_le` | ~287 nodes (claimed) | would *replace* the 657-node tower; unscouted |

The decision rule:

- **Endgame in view** → port **C** (cheap, mandatory), then scout **C′**; only if
  C′ fails, pay **A**. Never transcribe **B**: its statements come free from A.
- **Bounded to the Hecke face** → **B** is the terminal artifact and **C** is
  still worth it (it gives `Module.Finite`/`Free` from an integral-structure
  hypothesis, and `CuspForm.finiteDimensional_Gamma0` + the span family are cheap
  at closures 7 and 1–101).
- **Sequencing only** → **B** is the single way to unblock the 44 consumers before
  A lands, but those consumers are themselves the Taylor–Wiles layer; buying an
  interim statement for 4,308 throwaway lines is a bet worth making only if that
  layer is worked out of order.

## 6. What the T side of `R = T` adds

The T side is the patching/Taylor–Wiles layer: `CuspForm.heckeLocal.*`,
`CuspForm.TWLevel.HeckeRing.*`, `Algebra.*patchingDatum*`, `GaloisRep.*`,
`WeierstrassCurve.isModularModelOfLevel_*`. Measured: **168** such nodes, all
inside `fermatLastTheorem`'s closure, with closures from tens to ~23,000
(`TWLevel.HeckeRing.exists_basis_inertia_apply_eq_diamond_smul` is 6,379).

It consumes the general finiteness forms (13 + 6 consumers above). Beyond
finiteness it also needs `Def_CuspForm_ModPForms`, the `HeckeEis`/`PeriodPair`
Eichler–Shimura comparison, the Petersson inner product and
`CuspForm.finiteDimensional_Gamma0` (closure 7). A "T-side-first" strategy
therefore has only two exits: pay route A, or make route C′ work.

## 7. Recommendations

1. **Do not transcribe `S_CuspForm_moduleFinite_heckeAlgebra_two.lean`** if the
   endgame is in view. It is unreusable (§2) and its statement is a corollary of
   route A.
2. **Port route C's sub-cone anyway** — `sturm_bound_of_isArithmetic`,
   `sturm_bound_Gamma0`, `one_mem_strictPeriods_Gamma0`, `intLattice_fg`,
   `HasIntegralStructure.moduleFinite/Free_heckeAlgebra` (~18 nodes). It is on
   route A's path and is the reusable half regardless of scope.
3. **Scout route C′ before committing to the tower.** The single decision-relevant
   unknown is whether `exists_basis_gamma1_qCoeff_mem_range_intCast` + the small
   Sturm bound actually yields `hasIntegralStructure_of_two_le` without
   `HeckeEis`/`ModPForms`. A scouting round answers it either way.
4. **The span family is cheap** (closures 1–101) and only needs T7/T8 plus
   `finiteDimensional_Gamma0`; port it with the finiteness-adjacent work rather
   than deferring it to the tower.
5. **Record the throwaway explicitly** if route B is ever taken inside a
   bounded effort: the `_two` proof is deleted, not superseded in place, once
   route A lands.

## 8. Reproduction

```bash
cd tools/deps && python3 - <<'PY'
import sys; sys.path.insert(0, '.')
from fltdata import FltData
d = FltData()
def cl(i):
    seen, st = set(), [i]
    while st:
        j = st.pop()
        if j in seen: continue
        seen.add(j); st.extend(d.cites(j))
    return seen
end = cl(d.index['FLT.fermatLastTheorem'])
print('endgame closure', len(end))
for name in ['CuspForm.moduleFinite_heckeAlgebra_two',
             'CuspForm.hasIntegralStructure_two',
             'CuspForm.hasIntegralStructure_of_two_le',
             'CuspForm.moduleFinite_heckeAlgebra',
             'CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra',
             'CuspForm.intLattice_fg',
             'ModularForm.sturm_bound_Gamma0',
             'ModularForm.sturm_bound_of_isArithmetic',
             'CuspForm.finiteDimensional_Gamma0']:
    i = d.index[name]
    print(f"{name}: closure={len(cl(i))} indeg={d.indeg(i)} in_endgame={i in end}")
# the disjointness check (§2)
gen = cl(d.index['CuspForm.hasIntegralStructure_of_two_le'])
for t in ['CuspForm.moduleFinite_heckeAlgebra_two', 'CuspForm.hasIntegralStructure_two']:
    print(t, 'in general closure:', d.index[t] in gen)
PY
```

The file-local check is plain grep:

```bash
grep -rln "heckeAlgebraIntFull\|heckeTripleAlgebraFull" ~/proj/fermats-last-theorem --include=*.lean
# only P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean
```

The pin sizes:

```bash
wc -l ~/proj/fermats-last-theorem/P2M/Sol/S_CuspForm_{moduleFinite_heckeAlgebra{,_{two}},hasIntegralStructure_{two,of_two_le},intLattice_fg}.lean
```

## 9. Open questions

1. **Does route C′ hold?** If `exists_basis_gamma1_qCoeff_mem_range_intCast` +
   `sturm_bound_of_isArithmetic` yields `hasIntegralStructure_of_two_le`, the
   657-node tower is avoidable and the whole picture changes.
2. **Is there an endgame node that needs the `k = 2` statement strictly before the
   general one?** If not, route B has no sequencing value even inside the
   endgame.
3. **Is `exists_cyclic_span_heckeAlgebra` (closure 101) on the T-side path?** If
   not, the span family's expensive node can wait.
4. **Will mathlib close the gap?** A `Γ₀(N)` dimension formula / index value /
   arithmetic Sturm bound in mathlib would shrink route A materially, as
   `CuspForm.rank_eq_zero_of_weight_lt_twelve` already shrank the level-2
   cusp-form vanishing ([level2-cusp-port.md](../lean/logs/level2-cusp-port.md)).
5. **Is FLT's `CuspForm.norm` needed at all?** Its two FLT definition sites
   (`S_ModularForm_S2_Gamma0_2_eq_zero.lean` and
   `S_CuspForm_finiteDimensional_cuspForm.lean`) both use it only to *prove the
   Sturm bound*: the second file's section is literally `section SturmBound`, its
   `eq_zero_of_qExpansion_coeff_eq_zero`/`Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`
   are the arithmetic-level and `Γ₀` bounds in coefficient form, and its
   ~300-line `normCofactor` prelude serves only that proof — the
   finite-dimensionality argument itself (`qCoeffTrunc` +
   `FiniteDimensional.of_injective`) uses only the vanishing lemma. So the ported
   `sturm_bound_of_isArithmetic`/`sturm_bound_Gamma0` should replace it when
   `CuspForm.finiteDimensional_*` is ported, which would make the reserve
   `CuspFormNorm.lean` unnecessary even for its second consumer. (It is a `def`,
   so the citation graph does not show these uses; they come from source grep.)

## 10. Pointers

- [PORTING-Hecke.md](../lean/topics/PORTING-Hecke.md) §3.2 — the stop decision and
  the raw-line measurements.
- [hecke/TOPIC-t10-finite-algebra.md](../lean/topics/hecke/TOPIC-t10-finite-algebra.md)
  §7 — the corrected two-route analysis and the C′ proposal.
- [hecke-port.md](../lean/logs/hecke-port.md) §T10 — the verified blocker against
  the pin's imports.
- [hecke-commute-bar-coverage.md](hecke-commute-bar-coverage.md) — the other
  measured Hecke cone (the divisor-correspondence face, now closed).
- [`S_CuspForm_moduleFinite_heckeAlgebra_two.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_moduleFinite_heckeAlgebra_two.lean)
  — the standalone `k = 2` proof.
- [`S_CuspForm_hasIntegralStructure_of_two_le.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_hasIntegralStructure_of_two_le.lean)
  — the general integral structure.
- [`S_ModularForm_sturm_bound_of_isArithmetic.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularForm_sturm_bound_of_isArithmetic.lean)
  — the arithmetic-level Sturm bound.
