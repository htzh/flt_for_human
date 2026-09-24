# Compressibility / mathlib-reuse audit of `rval_aux`

Source: `P2M/Sol/S_ModularCurve_jqN_prime_not_mem_full.lean`,
git HEAD `aa2d8b34` of `~/proj/fermats-last-theorem`.
mathlib at `lean/.lake/packages/mathlib` (workspace checkout).
Read-only audit: nothing in either repo was modified.

## 0. Scope correction (evidence)

The brief says `rval_aux` is "lines 887-1585 (699 lines)". The declaration and
proof actually end earlier:

- `set_option maxHeartbeats 6400000 in` at **885**, statement begins **887**,
  proof body ends at **1566** (`rfl`), blank at 1567, `end RValCore` at **1568**.
- Lines **1567-1585** are module scaffolding: `end RValCore`,
  `p2m_reactivate`, `end ModularCurve.W1`, second `p2m_reactivate`, `namespace
  ModularCurve`, `p2m_export`, `namespace W1`, `p2m_open`, `section NonMem0`,
  `open IntermediateField`, and the second `set_option maxHeartbeats` at 1584
  that belongs to `jqN_prime_not_mem_adjoin` (declared at **1586**).

So the real size of `rval_aux` is **680 lines (887-1566)**, not 699; the extra
19 lines belong to the next theorem's scaffolding. All estimates below are
against the 680-line body.

## (a) Top-level block map

`rval_aux` body = 887-1566. Category key: **(a)** genuine mathematics,
**(b)** polynomial/minpoly bookkeeping, **(c)** instance/`NeZero`/coercion
plumbing, **(a/b)/(b/c)** mixed with the first code dominant.

### Top level

| Block | Lines | Kind | Category | One-line description |
|---|---|---|---|---|
| stmt | 887-897 | signature | - | target identity plus the `hall : ∀ d ∣ M, Tight d ∧ Gen d` hypothesis |
| intro | 898-901 | `intro`+strong induction | (c) | `intro M; induction M using Nat.strong_induction_on; intro _ K _ _ ζ hζ hall` |
| disc | 902 | `classical` | (c) | decidability |
| `hM0` | 903 | `have` | (c) | `M ≠ 0` from `NeZero.ne` |
| `hslot_root` | 905-1397 | `have` (493 lines) | (a) | every admissible slot value `sv K ζ a b` is a root of the mapped minpoly |
| base case | 1399-1423 | `by_cases hM1 : M = 1` | (a/b) | `M = 1`: minpoly `= X - C jGen`, product collapses to `X - C (coeffEmb K jq)` |
| main case | 1424-1566 | `by_cases` else-branch | (a) | `T =` all slot values has card/nodup, `roots = T`, `Splits`, conclude product |

### Inside `hslot_root` (905-1397)

| Block | Lines | Category | Description |
|---|---|---|---|
| unpack | 909-917 | (c) | `ha`, `hb` unpacked; `ha0`, `haveI : NeZero a`, `had : a*(M/a)=M` |
| case `M/a=1` | 918-931 | (a) | `sv_top`, then `eval minpoly = 0` via `minpoly.aeval` |
| minFac setup | 933-958 | (a/c) | `p := (M/a).minFac`, `d''` with `hdd : p*d''=M/a`, `hMM'`, `hM'M`, `hM'lt`, `hpM`; 3 `NeZero` instances |
| mod/gcd arithmetic | 960-978 | (a) | `hb''lt`, `hbsplit`, `hc₀p`, `hprim'` (admissibility of `b % d''`) |
| `hζ'` | 980-985 | (a) | `ζ^p` is primitive of order `a*d''` |
| IH application | 987-1000 | (a/b) | `IH (a*d'')`, `map_qExpand_minpoly_eq p`, `hroot'` |
| algebra instance | 1002-1006 | (c) | `letI : Algebra ℚ⟮jq⟯ (LaurentSeries K)`, `halg` |
| ψ₁ construction | 1007-1025 | (a/c) | `hall (a*d'')`, `FiniteDimensional.of_finrank_pos`, `hα'`, `hy_mem ∈ aroots`, `ψ₁` with `ψ₁ gen = value` |
| phiAtSeed data | 1027-1040 | (a/b) | `exists_phiIrreducible_evalSymm`, `hup`, `haev`, `hα₁`, `hmindvd` |
| tower degree | 1042-1071 | (a) | `htow`, `habs`, `htop`, `hstep_deg` (`finrank` of the two-step tower) |
| factorization | 1073-1100 | (a) | `hseed`, `hC5 := splits_prime_at_slot`, `hΦfact`, `hMp`, `htarget` |
| branch `p ∣ a*d''` | 1102-1353 | mixed | see subdivision below |
| branch `¬ p ∣ a*d''` | 1354-1397 | mixed | see subdivision below |

Branch `p ∣ a*d''` (1102-1353):

| Block | Lines | Category | Description |
|---|---|---|---|
| `hψM`,`he` | 1104-1112 | (b) | `dedekindPsi M = dedekindPsi (a*d'')*p`; step degree `= p` |
| `m''` | 1114-1123 | (c) | `a*d'' = p*m''`, `NeZero m''`, `hm''M`, `hm''lt` |
| descent root | 1124-1144 | (a) | `hdown`, `hmem''`, `hdownF₁`, `hψx''` (φ-root at `ψ₁ (jqN m'')`) |
| `hx''notmin` | 1145-1163 | (a) | `jqN m''` is not a root of `minpoly(jqN M)`; irreducible + degree-1 contradiction |
| `hψx''notmin` | 1164-1175 | (b) | push non-root through `ψ₁` using `eval₂_hom` |
| `htarget_ne` | 1177-1257 | (a) | hard descent: `map_qExpand_minpoly_eq (p*p)`, `prod_eq_zero_iff`, `TS_injective`, `hζ.pow_inj` ⇒ `p ∣ gcd(...)`, contradicts `hbc` |
| `hQ`...`hQdeg` | 1259-1285 | (b) | `mul_divByMonic_eq_iff_isRoot`, monic-ness of the quotient, `natDegree` arithmetic |
| `hP₁dvd`...`hmineqQ` | 1286-1319 | (b) | divisibility, coprimality, and `eq_of_monic_of_dvd_of_natDegree_le` |
| `htargetΦ`,`hroot_step` | 1320-1340 | (a/b) | `sv K ζ a b` is a root of `phiAtSeed` and of the mapped minpoly |
| `htowdvd` block | 1342-1353 | (b) | `minpoly.dvd_map_of_isScalarTower` + `eval_eq_zero_of_dvd_of_eval_eq_zero` |

Branch `¬ p ∣ a*d''` (1354-1397):

| Block | Lines | Category | Description |
|---|---|---|---|
| `hψM`,`he` | 1355-1364 | (b) | `dedekindPsi M = dedekindPsi (a*d'')*(p+1)`; step degree `= p+1` |
| `hdeg₁`,`hΦdeg`,`hmineq` | 1365-1375 | (b) | `minpoly = phiAtSeed` via `eq_of_monic_of_dvd_of_natDegree_le` |
| `hroot_step` | 1376-1385 | (a) | same root computation as one line above, in the other factorization |
| `htowdvd` block | 1386-1397 | (b) | **byte-identical copy of 1342-1353** (verified with `diff`) |

### Inside the main case (1424-1566)

| Block | Lines | Category | Description |
|---|---|---|---|
| `htM`,`hα`,`hdeg` | 1424-1434 | (c/b) | `hall M`, `FiniteDimensional.of_finrank_pos`, `IsIntegral`, `natDegree minpoly = dedekindPsi M` |
| `T` and card | 1436-1457 | (a) | `set T`; `hTcard = dedekindPsi M` via `slotAt`, `Nat.sum_div_divisors`, `slots_eq_dedekindPsi` |
| `hmem_unpack` | 1458-1466 | (b) | every member of `T` is `sv K ζ a b` |
| `hTnodup` | 1467-1521 | (a) | injectivity of slots: within one `a` via `Multiset.Nodup.map_on`, across `a` via `pairwise`/`Disjoint`, both from `sv_inj` |
| `hPne`,`hPdeg` | 1523-1529 | (b) | mapped minpoly ≠ 0 and `natDegree = dedekindPsi M` |
| `hTle` | 1530-1544 | (a) | `T ≤ roots` by count |
| `hroots_eq` | 1545-1553 | (a) | `roots = T` from `≤` + `card ≤ natDegree` |
| `hsp` | 1554-1556 | (b) | `Splits` from `splits_iff_card_roots` |
| conclude | 1557-1566 | (a/b) | `eq_prod_roots_of_monic`, `map_bind`/`prod_bind`, `rfl` |

Category totals over the 680 lines (approximate, by summing the spans with the
mixed blocks split as annotated): **(a) ~430-450 lines / ~64%**,
**(b) ~180-190 lines / ~27%**, **(c) ~55-65 lines / ~9%**.

## (b) mathlib candidates

### Q2 - `map_qExpand_minpoly_eq` (858-886; statement 858-869, proof 870-883, then `set_option` at 885)

**There is no mathlib lemma that replaces this theorem.** Checked by name over
all of `Mathlib/`:

- `minpoly.map_eq_of_injective` - **does not exist** (`grep -rn
  "map_eq_of_injective" Mathlib/` returns only `natDegree_map_eq_of_injective`,
  `degree_map_eq_of_injective`, `Submodule.comap_map_eq_of_injective`, etc.,
  none about `minpoly`).
- The only two "map a minpoly" lemmas in `Mathlib/FieldTheory/Minpoly/`:
  - `minpoly.map_algebraMap` at
    `Mathlib/FieldTheory/Minpoly/Field.lean:111`, exact call:
    `(minpoly F a).map (algebraMap F E) = minpoly E a`, requiring
    `minpoly E a ∈ lifts (algebraMap F E)`. Not applicable: the map here is
    `qExpand K k`, not a scalar-tower `algebraMap`.
  - `minpoly.map_eq_of_equiv_equiv` at
    `Mathlib/FieldTheory/Minpoly/Field.lean:209`, exact call:
    `map f (minpoly R x) = minpoly A (g x)` for ring **equivalences**
    `f, g`. Not applicable: `qExpand K k` is not an equivalence.
- `minpoly.dvd_map_of_isScalarTower` at
  `Mathlib/FieldTheory/Minpoly/Field.lean:86` is the scalar-tower statement and
  is already used elsewhere in `rval_aux` (1344, 1388), but does not give the
  helper's conclusion.

What the proof actually uses is generic polynomial-map algebra, all already in
mathlib:

- `Polynomial.map_map` at `Mathlib/Algebra/Polynomial/Eval/Coeff.lean:85`
  (used at 878): `(p.map f).map g = p.map (g.comp f)`.
- `Polynomial.map_prod` at `Mathlib/Algebra/Polynomial/Eval/Defs.lean:725`
  (used at 879, 881): `(∏ i ∈ s, g i).map f = ∏ i ∈ s, (g i).map f`.
  Not `@[simp]`; must be named in `simp only` or `rw`.
- `Polynomial.map_prod`'s multiset/list forms at
  `Mathlib/Algebra/Polynomial/Eval/Defs.lean:722` / `:570`.
- `Polynomial.map_sub` at `Mathlib/Algebra/Polynomial/Eval/Defs.lean:738`
  (`@[simp]`), `Polynomial.map_C` at `:498` (`@[simp]`), `Polynomial.map_X` at
  `:502` (`@[simp]`). The four explicit `rw`s at 883 (`map_sub`, `map_X`,
  `map_C`) plus the two nested `Finset.prod_congr` loops at 880-882 are exactly
  what `simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
  Polynomial.map_C]` would do automatically.
- There is **no** mathlib lemma of the form
  `(∏ i, (X - C (g i))).map f = ∏ i, (X - C (f (g i)))` (grepped:
  `map_prod_X_sub_C` / `prod_X_sub_C_map` / `map.*X - C` - only
  `Polynomial.mapAlg` facts such as `Mathlib/RingTheory/Polynomial/Tower.lean:91`
  and `Splits`/`Vieta` lemmas, none for a general `RingHom`). A 2-line local
  generic helper would absorb it.

**Conclusion for Q2:** the helper is not subsumed by a mathlib call, but the
part after the ring-hom identity `hcomp` (870-883, 14 lines) is pure
`map_map` + `map_prod` + `simp`: it collapses to
`rw [← Polynomial.map_map, hcomp, hid]; simp only [...]` (~3-4 lines). `hcomp`
itself (871-876) is already minimal (it is the one genuine input:
`coeffEmb_qExpand`, `qExpand_qExpand`). **Realistic saving: ~8-12 lines of the
helper's 26 (statement+proof 858-883).**

### Other exact mathlib calls in `rval_aux`

| Call in source | mathlib path:line | Exact statement (as used) |
|---|---|---|
| 1263 `Polynomial.mul_divByMonic_eq_iff_isRoot.mpr` | `Mathlib/Algebra/Polynomial/Div.lean:616` | `(X - C a) * (p /ₘ (X - C a)) = p ↔ IsRoot p a` |
| 1269 `Polynomial.Monic.of_mul_monic_left` | `Mathlib/Algebra/Polynomial/Monic.lean:107` | `p.Monic → (p*q).Monic → q.Monic` |
| 1318, 1374 `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` | `Mathlib/Algebra/Polynomial/Div.lean:95` | `p.Monic → q.Monic → p ∣ q → q.natDegree ≤ p.natDegree → q = p` |
| 1344, 1388 `minpoly.dvd_map_of_isScalarTower` | `Mathlib/FieldTheory/Minpoly/Field.lean:86` | `minpoly K x ∣ (minpoly A x).map (algebraMap A K)` |
| 1406 `minpoly.eq_X_sub_C` | `Mathlib/FieldTheory/Minpoly/Field.lean:262` | `minpoly A (algebraMap A B a) = X - C a` |
| 1557 `Splits.eq_prod_roots_of_monic` | `Mathlib/Algebra/Polynomial/Splits.lean:307` | `f.Splits → f.Monic → f = (f.roots.map (X - C ·)).prod` |
| 1160/1311/1366/1433/1621 `IntermediateField.adjoin.finrank` | `Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:489` | `IsIntegral K x → finrank K K⟮x⟯ = (minpoly K x).natDegree` |

Note: `Polynomial.map_algebraMap`-style and `Polynomial.eval₂_hom` facts used at
1173/1187/1190 are already `simp`-level and add no weight.

## (c) Repeated-pattern occurrences

### C1. "monic + dvd + natDegree ≤ ⇒ eq"

Direct uses of `Polynomial.eq_of_monic_of_dvd_of_natDegree_le` in the whole file
(no others):

- **1313-1319** (`hmineqQ`, branch `p ∣ a*d''`): hypotheses assembled from
  `(minpoly.monic hα₁).map _` (1318), `hQmonic` (1266-1270),
  `hP₁dvdQ` (1300-1307), `le_of_eq (hQdeg.trans hdeg₁.symm)` (1319).
- **1372-1375** (`hmineq`, branch `¬ p ∣ a*d''`): `minpoly.monic hα₁`,
  `phiAtSeed_monic dp _`, `hmindvd` (1038-1040),
  `le_of_eq (hΦdeg.trans hdeg₁.symm)` (1375).

**There is no `Polynomial.Monic.eq_of_dvd_of_natDegree_le` in mathlib** (grepped
`Monic.eq_of` and `eq_of_dvd_of_natDegree_le` over `Mathlib/`: the only sibling
is `Polynomial.eq_of_dvd_of_natDegree_le_of_leadingCoeff` at
`Mathlib/Algebra/Polynomial/Div.lean:815`, which drops the monic hypothesis but
needs `leadingCoeff`, so it is not equivalent). The free function at `Div.lean:95`
is already the single shared lemma; the repetition in `rval_aux` is in *building
the ≤-hypothesis* (the `le_of_eq (...trans ...symm)` inversions) and the
`natDegree = finrank` assembly, not in the equation step.

Supporting repeated fragments:

- `natDegree = finrank`-then-`= he`/`= htM` pattern: **1156-1163, 1308-1312,
  1365-1367, 1432-1434** (and outside `rval_aux` at 1621).
- `Polynomial.Monic.natDegree_map (minpoly.monic ...)` at **1310** and **1528**.
- `minpoly.monic` used at **1318, 1374, 1428, 1432, 1525, 1528, 1557**.

### C2. Byte-identical duplicated block

`diff` confirms **1342-1353 == 1386-1397** (12 lines each): the whole
`htowdvd` / `h1` / `h2` / `rw [h2] at h1` preparation before
`Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero`. It does not depend on the
`p ∣ a*d''` case split, so it can be hoisted once above `by_cases hpM'` at 1102,
leaving one 2-line `exact ... hroot_step` per branch. **Saving ~11 lines.**

### C3. Near-duplicate `b * a < M` calculations

The same `calc b * a < M / a * a := (Nat.mul_lt_mul_right ...).mpr hbr; _ = M := ...`
appears at **1231-1233, 1481-1484, 1485-1488, 1512-1515, 1516-1519**. A one-line
local helper (or a two-line `simp`-based derivation) would remove ~3 lines per
site. **Saving ~10 lines.**

### C4. `FiniteDimensional`/`IsIntegral`/`hdeg` preamble

`obtain ⟨ht,-⟩ := hall ...; haveI := FiniteDimensional.of_finrank_pos (ht ▸
dedekindPsi_pos ...); have hα := ...IsIntegral.of_finite...; have hdeg := by
rw [← IntermediateField.adjoin.finrank hα]; exact ht` occurs at **1007-1014**
(relative to `hα'`) and **1424-1434**, and in `jqN_prime_not_mem_adjoin` at
1607-1625. A local helper bundling `(FiniteDimensional, IsIntegral, natDegree
= dedekindPsi)` saves ~4 lines per site. **Saving ~8 lines inside `rval_aux`.**

### C5. Instance / `NeZero` plumbing

10 `haveI` + 1 `letI` inside 887-1566: lines 916, 938, 939, 946, 948, 1002
(`letI`), 1008 (`haveI hfd'`), 1119 (m''), 1214 (α), 1417, 1425 (`haveI hfd`).
Most are unavoidable one-liners; bundling `NeZero (a*d'')`, `NeZero d''`,
`NeZero p` via a small `haveI` helper can shave ~4-6 lines.

### C6. Bonus, outside `rval_aux`: duplicated generic lemma

`mem_range_of_eval_eq_const` at **804-821** (18 lines) is a verbatim copy of
`Polynomial.mem_range_of_eval_eq_const` in the port's engine
`lean/FLTForHuman/FieldTheory/CommonRoot.lean:111-126` (used later at 1926).
Importing the engine deletes the 18-line private copy. The other two engine
lemmas (`mem_range_of_unique_common_root` at `CommonRoot.lean:60`,
`irreducible_of_transitive_ringAut` at `CommonRoot.lean:148`) are **not used**
anywhere in this file (only `mem_range_of_eval_eq_const` is), and they do not
match `rval_aux`'s `hx''notmin`/`htarget_ne` arguments directly, so they offer
no compression for 887-1566.

## (d) Compression estimate

Basis: 680 lines (887-1566).

| # | Item | Lines today | After | Saving |
|---|---|---|---|---|
| B1 | `map_qExpand_minpoly_eq` via `Polynomial.map_map` + `map_prod` + `simp` (no mathlib replacement lemma exists) | 26 (858-883) | ~14 | ~12 |
| B2 | hoist the byte-identical `htowdvd` block out of the `p ∣ a*d''` split | 12+12 (1342-1353, 1386-1397) | 12+2+2 | ~11 |
| B3 | local helper for `natDegree = finrank` / `Monic.natDegree_map` assembly (1156-1163, 1308-1312, 1365-1367, 1432-1434, 1526-1529) | ~23 | ~15 | ~8 |
| B4 | local helper for `b*a < M` calc (1231-1233, 1481-1488, 1512-1519) | ~14 | ~5 | ~9 |
| B5 | bundle `FiniteDimensional`+`IsIntegral`+`hdeg` preamble (1007-1014, 1424-1434) | ~22 | ~14 | ~8 |
| B6 | `NeZero`/instance bundling (916, 938-948, 1119, 1214, 1417, 1425) | ~10 | ~5 | ~5 |
| | **Realistic subtotal, inside `rval_aux`** | | | **~53** |
| B7 | factor the two case branches' shared tail (`hroot_step` shape + final `eval_eq_zero`) into one local lemma | 44+252 | - | ~15-25 (aggressive) |
| | **Aggressive subtotal, inside `rval_aux`** | | | **~70-80** |
| B8 | delete private `mem_range_of_eval_eq_const` and use engine `CommonRoot.lean:111-126` | 18 (804-821) | 0 | ~18 (outside `rval_aux`) |

**Answer to Q4:** of the 680-line body, roughly **430-450 lines (~64%) are
irreducible mathematics** (the slot/root construction in 909-1100, the
`htarget_ne` descent 1177-1257, the tower-degree computation 1042-1071, and the
cardinality/nodup/roots argument 1436-1566). Mechanically compressible material
is ~180-190 lines of polynomial/minpoly bookkeeping plus ~60 lines of plumbing.
Using mathlib as-is plus one or two local helpers, the realistic shrink is
**~50-60 lines (~8-9%)** inside `rval_aux`, rising to **~70-80 lines (~11-12%)**
if the two case branches' common tail is factored out; deleting the duplicated
generic lemma adds **~18 lines** outside the theorem. This is a
reuse/verbosity cleanup, not a structural reduction: the only place where a
single named mathlib fact nearly replaces a whole local theorem is the
`map_prod`/`map_map` part of `map_qExpand_minpoly_eq`, and even there the
minpoly-specific step is genuinely local (no `minpoly.map*` mathlib lemma
applies).

## (e) Confidence

| Finding | Confidence | Basis |
|---|---|---|
| Block map / line ranges | **High** | every line 858-1566 read directly; boundaries confirmed by `sed` |
| No `minpoly.map_eq_of_injective` / `minpoly.map` in mathlib; `map_algebraMap` and `map_eq_of_equiv_equiv` are the only minpoly-map lemmas and neither applies | **High** | exhaustive `grep -rn` over `Mathlib/` for the names |
| `Polynomial.map_map` / `map_prod` / `map_sub` / `map_C` / `map_X` paths and simp status | **High** | source lines read (`Eval/Coeff.lean:85`, `Eval/Defs.lean:498,502,722,725,738`) |
| No `map_prod_X_sub_C` mathlib lemma | **High** | grepped several name shapes over `Mathlib/` |
| `eq_of_monic_of_dvd_of_natDegree_le` occurrences (exactly 2) and absence of a `Monic.` namespaced variant | **High** | grep over source and `Mathlib/` |
| Byte-identical duplication 1342-1353 vs 1386-1397 | **High** | `diff` reported no differences |
| Category line-count split (a/b/c) | **Medium** | span-by-span manual classification; mixed blocks split by judgement |
| Line-saving estimates B1-B8 | **Medium** | reasoned from lemma availability; not compile-tested (the target project and the port mathlib build are separate, and the audit is read-only) |
| Engine lemma reuse for `rval_aux` (none) | **High** | grepped the file for all three engine names; only the local copy of `mem_range_of_eval_eq_const` at 804 is used (at 1926) |

### Note on `PhiGen.splits_prime_at_slot`

The brief places it in `Definitions/Def_ModularCurve_PhiGen.lean`; the actual
`private theorem ModularCurve.PhiGen.splits_prime_at_slot` is at
`P2M/Sol/S_ModularCurve_PhiGen_splits_prime_at_slot.lean:143` (re-exported by
`Theorems/Thm_ModularCurve_PhiGen_splits_prime_at_slot.lean`), while
`Def_ModularCurve_PhiGen.lean` holds the `Φ`/`qTwist` definitions and
`phiAtSeed` lives at `P2M/Sol/S_ModularCurve_PhiGen_splits_of_prime.lean:214`.
It is invoked once in `rval_aux` at line 1079 (`hC5`) and consumed at 1081-1087
(`hΦfact`); it is not a compression target.
