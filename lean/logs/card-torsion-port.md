# Porting `#E[n](K) = n²` — trace, decisions, order

**Status: complete.** The capstone is
`FLTForHuman.Elliptic.card_torsion_of_isAlgClosed`
(`FLTForHuman/Elliptic/Fiber.lean`); `lake build` is green with 0 warnings and no
`sorry`.

| | |
|---|---|
| modules | 13 under `FLTForHuman/Elliptic/` |
| lines written | 3362 |
| declarations | 292 |
| FLT cone (import closure) | 4 files, 3671 lines |
| of which consumed | engine 1869 lines / 304 decls; `S_…` 1335 lines / 36 decls |
| cone lines never ported | ~310 (measured spans), plus a 340-line 4.30-compat shim |
| goal rounds | 33 |

The working record for the port of `WeierstrassCurve.card_torsion_of_isAlgClosed`
(the theorem of [math/005](../../math/005-card-torsion-p-squared.md)) into
`FLTForHuman/`. Ground rules and build instructions are in
[README.md](../README.md); this file says *what* was ported, *what was dropped*,
and in *what order*. The reusable lessons — method, gotchas, v4.34.0 API drift —
are in [../porting-playbook.md](../porting-playbook.md).

FLT line numbers are against `anthropics/fermats-last-theorem@aa2d8b3`; mathlib
line numbers against `v4.34.0`.

## 1. The dependency trace

The theorem is a tower; reading it top-down, most of the height is scaffolding.

| # | FLT declaration | Where | Nature |
|---|---|---|---|
| 0 | `card_torsion_of_isAlgClosed` | `Thm_…:9` | statement only |
| 1 | `p2m_exact_reverting` | `P2M/Util.lean:4` | plumbing: reverts hypotheses, checks the term against the goal |
| 2 | `solution` | `S_…:1330` | rewrites mathlib `Submodule.torsionBy` to a local `nTorsion` |
| 3 | `nTorsion` | `S_…:308` | `AddSubgroup {P \| n • P = 0}`, the same set as mathlib `Submodule.torsionBy` |
| 4 | `card_nTorsion` | `S_…:1294` | **math**: assembly via `Nat.recOnPosPrimePosCoprime` |
| 5 | prime / two / prime-power / coprime | `1161 / 1054 / 1168 / 1217` | **math**: counting |
| 6 | fiber engine | `smul_surjective_all:955`, `card_smul_fiber_all:1035`, `finite_not_squarefree_fiber:397`, `exists_double_fiber_card:614` | **math**: `[n]` surjective, fibers of size `#E[n]` |
| 7 | division-poly engine | `isCoprime_Φ_ΨSq:213`, `isCoprime_ΨSq_succ:77`, `smul_formula_or_zero:133`, `wronskian_Φ_ΨSq_ne_zero:343` | **math**: separability via the Wronskian |
| 8 | multiplication bridge | `zsmul_eq_smulEval`, `evalEval_φ`, `evalEval_ψ_sq`, `smul_eq_zero_iff_evalEval_ψ` | `Def_WeierstrassCurve_EDSEngine.lean` |
| 9 | EDS core | `net`, `rel₄`, `addMulSub`, `invariantNum/Denom` | `Def_WeierstrassCurve_EDSEngine.lean`, 1869 lines |

`W⁄K` is the **affine** base change (`WeierstrassCurve.Affine.baseChange`, the
`Affine` version being an `abbrev` of `WeierstrassCurve`), so `(W⁄K).Point` is
the affine point group — the same type as the FLT-local `W.toAffine⟮K⟯`. The
Jacobian points appear only inside the proof, via `toAffineAddEquiv`.

### Already mathlib

- `Submodule.torsionBy` (`Algebra/Module/Torsion/Basic.lean:180`), `mem_torsionBy_iff:267`,
  and `Submodule.torsionBy.zmodModule:1013` — the last also removes the need for FLT's
  `instModuleZModTorsionBy` (`Def_FLTPrelim_GaloisRep.lean:60`), cited in math/005 §3.
- The division polynomials: `ψ`, `Ψ`, `ΨSq`, `preΨ`, `preΨ'`, `Φ`, `φ`, `ψ₂`, `Ψ₂Sq`,
  `Ψ₃`, `preΨ₄` and their `_ofNat`/`_even`/`_odd` lemmas
  (`DivisionPolynomial/Basic.lean`), plus `natDegree_Φ`, `natDegree_ΨSq`
  (`DivisionPolynomial/Degree.lean`).
- `Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed`
  (`FieldTheory/IsAlgClosed/Basic.lean:251`), `IsAlgClosed.exists_root`,
  `Jacobian.nonsingular_of_Z_ne_zero`, `Jacobian.Point.toAffineLift_of_Z_ne_zero`,
  `Nat.recOnPosPrimePosCoprime`, `Nat.card_congr`.
- `(W.map f).IsElliptic` (`Weierstrass.lean:456`), which is all our
  `instIsEllipticBaseChange` needs (`FLTForHuman/Elliptic/Basic.lean`).

### The one genuine gap

mathlib's `Affine/Point.lean` (975 lines) has **no** division-polynomial API and
no criterion for `n • P = 0`. Nothing in mathlib connects `ψ n` to the point
group. Hence math/005 §2.1 is wrong to call `smul_eq_zero_iff_evalEval_ψ`
"mathlib's": `smulEval`, `zsmul_eq_smulEval`, `evalEval_φ`, `evalEval_ψ_sq` and
`smul_eq_zero_iff_evalEval_ψ` are all FLT (`Def_WeierstrassCurve_EDSEngine.lean`
lines 1762, 1835, ~1820, 1843). mathlib *does* ship an EDS theory
(`NumberTheory/EllipticDivisibilitySequence.lean`, 809 lines: `IsEllipticNet`,
`atom`, `atomRel`, `rel`, `normEDS`), which is why the gap is bridgeable.

## 2. Clutter dropped

| Dropped | Size | Reason |
|---|---|---|
| `p2m_exact_reverting` + `Thm_`/`_light` re-exports | 44 lines across 3 files | we state and prove directly |
| `nTorsion:308` + the `solution` bridge | 20 lines | it *is* `Submodule.torsionBy` |
| `Def_Compat_Mathlib430.lean` | 340 lines (197 importers) | mathlib-4.30 renames; v4.34.0 has the unprimed names |
| `S_…` inherited import list | ~half of 21 imports | copied from the engine, unused here |
| odd-only `smul_surjective:452`, `card_smul_fiber:533` | 98 lines (452–550) | subsumed by the generalised copy below |
| `smul_surjective_all:955` + `card_smul_fiber_all:1035` | 98 lines (955–1052) | same proof as the above, and `hodd` is unused ⇒ one general lemma suffices |
| dead `ΨSq_odd_eq_sq:269` + `smul_eq_zero_iff_preΨ'_eval:273` | 38 lines (269–306) | referenced only by themselves |
| dead `evalEval_ωe:1306` + `polyEval_cusp_ωe:1329` | 10 lines | referenced only by themselves |
| `instIsEllipticBaseChange` via `inferInstanceAs`, `instModuleZModTorsionBy` | ~8 lines | one-liner; mathlib already provides the latter |

## 3. Decision: hybrid MulFormula

Agreed strategy: port **only** the genuine gap
(`PortEllSequenceZSMul` + `PortEllSequenceAffineBridge`, ~600 lines) and
re-derive its EDS inputs from mathlib's `IsEllipticNet`/`atom`/`atomRel`/`rel`
rather than copying FLT's ~950-line EDS core.

**Refined after checking v4.34.0 (round 1).** The correspondence holds, and is
tighter than expected — FLT's `compl₂EDS` is *definitionally* mathlib's
`complEDS₂`:

| FLT (`Def_WeierstrassCurve_EDSEngine.lean`) | mathlib v4.34.0 (`EllipticDivisibilitySequence.lean`) |
|---|---|
| `EllSequence.addMulSub m n` | `atom a b` (:108) |
| `EllSequence.rel₄ a b c d` | `atomRel a b c d` (:157) |
| `EllSequence.net p q r s` | `rel p q r s` (:266) |
| `IsEllSequence'` / `IsDivSequence'` | `IsEllipticSequence` / `IsEllipticDvdSequence` |
| `normEDS`, `preNormEDS` | `normEDS` (:545), `preNormEDS` (:432) |
| `EllSequence.compl₂EDS` | `complEDS₂` (:502) — `rfl`-equal |
| `EllSequence.complEDS` | `complEDS` (:691) |
| `WeierstrassCurve.ψ` | `normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)` (`DivisionPolynomial/Basic.lean:401`) |

**But the EDS core is not entirely duplicated.** mathlib dropped the `ω`
division polynomial after v4.30, and with it `redInvarNum`, `redInvarDenom`,
`compl₂EDSAux`, `invarNum`, `invarDenom`. These are genuinely FLT-specific and
must be ported. Worse, `ωe` also needs the *multiplication property* of the
general complement sequence, `normEDS m * complEDS m n = normEDS (n * m)`, which
mathlib v4.34.0 states only for the `2`-complement (`normEDS_mul_complEDS₂`) —
the general case is still a mathlib `TODO`. FLT gets it from the universal EDS
argument `IsEllSequence'.mul_compl_eq_apply_mul_of_mem_nonZeroDivisors`.

So the remaining EDS dependency chain that must be ported faithfully is roughly
`Def_WeierstrassCurve_EDSEngine.lean` lines 300–1000, ~700 lines:

| needed | FLT | mathlib status |
|---|---|---|
| `IsEllipticSequence (normEDS b c d)` | `IsEllSequence'.normEDS:728` | absent (mathlib `TODO`) |
| `rel (normEDS b c d) p q r s = 0` | `net_normEDS:949` | absent |
| `normEDS m * complEDS m n = normEDS (n*m)` | `normEDS_mul_complEDS:826`, `_div:835` | absent |
| `complEDS` recursion | `compl:626`, `compl':610` | **present** (`complEDS:691`, `complEDS_even/odd`) |
| `redInvarDenom` + `invarDenom_eq_redInvarDenom_mul` | `:856`, `:867` | absent |
| `invar₂_normEDS`, `redInvar_normEDS` | `:967`, `:988` | absent |
| universal EDS (`Param`, `universalNormEDS`, `map_invar*`) | `:680–708` | absent |

The hybrid still pays off — `atom`/`atomRel`/`rel` are *definitionally* FLT's
`addMulSub`/`rel₄`/`net`, and `complEDS` exists — but step 3a is now the bulk of
the work rather than a thin wrapper.

Risk: an API mismatch in the `normEDS`/`atom` correspondence. Mitigation: port
bottom-up, `lake build` after each module, and if a correspondence resists,
fall back to the faithful engine port for that layer only.

## 4. Port order

1. `FLTForHuman/Elliptic/Basic.lean` — base-change `IsElliptic` instance. **done**
2. `FLTForHuman/Elliptic/Universal.lean` — FLT's universal curve (`Univ.Field`,
   `Univ.Ring`, `curve`, `pointedCurve`, `polyToField`, `ringEval`, `cusp`).
   No mathlib analogue; must be ported. **Done.** `equation_point` resisted
   FLT's v4.33.0 `simp_rw` chain on v4.34.0 and was reproved via
   `Polynomial.eval₂_eval₂RingHom_apply` + `AdjoinRoot.aeval_eq`
   (`aeval (root f) f = 0`), which is the universal property FLT's chain was
   reaching for.
3a. `FLTForHuman/Elliptic/DivisionPolynomial.lean` — the `ω`-specific extras.
   **Done:** `invar`, `ψc` + `ψc_spec`; `invarNum`, `invarDenom`,
   `complEDSAux` (+ its normalisations and `complEDSAux_mul_b`), `redInvarNum`,
   `invarNum_eq_redInvarNum_mul`.
   The FLT-side EDS core that mathlib lacks — `IsEllipticSequence (normEDS b c d)`,
   `rel (normEDS b c d) = 0`, `normEDS m * complEDS m n = normEDS (n*m)`,
   `redInvarDenom` + `invarDenom_eq_redInvarDenom_mul`, `invar₂_normEDS`,
   `redInvar_normEDS`, `ωe` + `ωe_spec` + `two_mul_ωe` — was subsequently ported
   across `EllSequence`, `Complement`, `RedInvar`, `Net` and `Omega`.
3a′. `FLTForHuman/Elliptic/EDS.lean` — `map_invarNum`/`map_invarDenom`, the
   universal `Param` indices, `universalNormEDS`, `normEDS_eq_aeval`. **Done.**
3a″. `FLTForHuman/Elliptic/EllSequence.lean` — the relator layer: `addMulSub` /
   `rel₄` / `net` as aliases for mathlib's `atom` / `atomRel` / `rel`, plus
   FLT's transfer machinery (`HaveSameParity₄`, `StrictAnti₄`, `avg₄`,
   `rel₄_transf`, `transf`, `strictAnti₄_transf`) that mathlib lacks. **Done**,
   and so are `rel₆` + its identities, `rel₃_iff₄`, `OddRec`/`EvenRec`, the
   `dMin`/`cMin` helpers, `Rel₄OfValid`, `rel₄_of_anti_oddRec_evenRec`, the
   `Perm` section (`rel₄_abs`, `rel₄_swap₀₁/₁₂/₂₃`, `relFin4_perm'`,
   `rel₄_same₀₁/₁₂/₂₃`, `rel₄_of_oddRec_evenRec`), and the payoff
   **`normEDS_isEllipticSequence : IsEllipticSequence (normEDS b c d)`** —
   mathlib still lists this as a `TODO`.
   **Complete.**

3a⁶. `FLTForHuman/Elliptic/Omega.lean` — **Done.** `C_Ψ₃_eq`,
   `preΨ₄_add_Ψ₂Sq_sq`, `preΨ₄_add_ψ₂_pow_four`, `φ_mul_ψ`, and the
   `y`-coordinate numerator itself: `ωe`, `ωe_spec`
   (`2 * ωe n + a₁ φ n ψ n + a₃ ψ n³ = ψc n`, valid in every characteristic),
   `two_mul_ωe`, `ωe_zero`, `ωe_one`, `ψc_neg`.

**Step 3a is finished**: `DivisionPolynomial`, `EDS`, `EllSequence`,
`Complement`, `RedInvar`, `Net` and `Omega` together cover everything FLT's
`Def_WeierstrassCurve_EDSEngine.lean` supplies to the multiplication formula,
built on mathlib's `atom`/`atomRel`/`rel`/`normEDS`/`complEDS`/`complEDS₂`
rather than FLT's compat shim.

3a⁵. `FLTForHuman/Elliptic/Net.lean` — **Done.** The *full* net property
   `net_normEDS` (upgrading round 5's `s = 0` slice via
   `net_of_isEllipticSequence` + `rel₄_of_oddRec_evenRec` at the indices
   `(2p+s, 2q+s, 2r+s, s)`), then `invar_of_net`, `invar_normEDS`,
   `invar₂_normEDS`, and `redInvar_normEDS`. The `map_complEDSAux`,
   `map_redInvarNum` and `map_redInvarDenom` transfer lemmas live in
   `DivisionPolynomial.lean` / `RedInvar.lean`.

3a⁗. `FLTForHuman/Elliptic/RedInvar.lean` — **Done.** `normEDS_six_eq_mul`,
   `redInvarDenom` and its defining identity
   `invarDenom (normEDS b c d) 1 m = redInvarDenom b c d m * b * c`, plus
   `redInvarDenom_zero/one/two`. Ported from FLT lines ~856–905 with mathlib's
   `complEDS` in place of FLT's duplicate complement.

3a‴. `FLTForHuman/Elliptic/Complement.lean` — **Done.** The complement
   multiplication property `normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m)`
   and its divisibility form `normEDS_mul_complEDS_div`. Proved directly for the
   universal EDS by strong induction on `n` (`Int.negInduction` + `Nat` strong
   induction, `complEDS_even`/`complEDS_odd`, the EDS relation at
   `((k+2)m, (k+1)m, 1)`, cancellation of `universalNormEDS m`), then transferred
   to general `b c d` by `aeval`. No FLT `compl`/`compl'` needed.
   `redInvarDenom` + `invarDenom_eq_redInvarDenom_mul`, `invar₂_normEDS`,
   `redInvar_normEDS`, and finally `ωe` + `ωe_spec` + `two_mul_ωe`.
3b. `FLTForHuman/Elliptic/MulFormula.lean` — the multiplication formula itself.
   **Layer 1 done:** `evalEval_ψ₂`/`_Ψ₃`/`_preΨ₄`/`_ψ`/`_φ`, the `cusp`
   evaluations `polyEval_cusp_ψ`/`_φ`/`_ψc`, `ψᵤ` + `ψᵤ_eq_normEDS`,
   `isEllipticSequence_ψᵤ`, `net_ψᵤ`, `ψᵤ_ne_zero`, `polyToField_φ_ne_zero`,
   `polyToField_ψ₂Sq`.
   The rest of this step — `smulX_ne_smulX` / `smulX_eq_smulX_iff`, the `smulY`
   lemmas (`smulY_sub_negY`, `slopeOne`, `addX`/`addY` at `1,1`, `smulY_neg`,
   `smulX_add`, `smulY_add_sub_negY`), the induction `zsmul_point_eq_smulX_smulY`,
   then the Jacobian `smulPoly`/`smulField` route with its `dblXYZ`/`addXYZ`
   identities, and finally `smulEval` and `zsmul_eq_smulEval` — was done over the
   rounds that follow.
   **Done in layer 2:** `smulX`, `smulY`, `smulX_zero/one`, `smulX_eq`,
   `smulX_two`, `smulX_sub_smulX`, `smulX_sub_sub_smulX_add`, `smulX_neg`,
   `smulX_ne_zero`, `smulX_ne_smulX`, `smulX_eq_smulX_iff`, `smulY_sub_negY`,
   `smulY_one_sub_negY`, `smulY_one_ne_negY`, `slopeOne`, `slopeOne_eq_neg_div`,
   `addX_smul_one_smul_one`, `ωe_neg'`, `smulY_neg`, `smulX_add`,
   `smulY_add_sub_negY`.

   **Resolved:** `addY_smul_one_smul_one` (FLT 1460–1466). FLT's literal port
   (`simp only […]` + `exact aux`) blew the defeq budget — a 299 s deterministic
   timeout at `whnf`. The fix is to end the proof with
   `simp only [polyToField_sub, polyToField_neg, map_add, map_mul, map_pow,
   map_ofNat, polyToField_polynomial, mul_zero, pointedCurve_a₁, pointedCurve_a₃,
   ψ_two, ψ₂]` followed by an explicit `hψ2 : polyToField curve.polynomialY ≠ 0`
   (needed by `field_simp`) and then `field_simp; ring`, instead of unifying the
   whole goal against the abstract `*_aux` statement. The `ψ_two`/`ψ₂` rewrites
   are what align `polyToField (ψ 2)` with `polyToField polynomialY`; the build
   is back to ~4 s.

   **Done:** the affine induction **`zsmul_point_eq_smulX_smulY`**
   (`n • P = (smulX n, smulY n)` on the universal curve), by
   `Int.negInduction` + strong induction on `ℕ`, the `n = 1, 2` base cases and
   the `n + 3` step through `smulX_add` / `smulY_add_sub_negY` and
   `add_of_X_ne`.

   **Then the Jacobian `smulPoly`/`smulRing`/`smulField` route**, in
   `FLTForHuman/Elliptic/JacobianMulFormula.lean`: first the homogeneous
   coordinates `smulPoly`/`smulRing`/`smulField`,
   `algebraMap_comp_smulRing`, `point_point`, `zsmul_point_ne_zero`,
   `zsmul_point_ne`, `smulPoly_zero`, `smulField_zero`, `addZ_smulPoly`
   (consuming `rel₃_of_isEllipticSequence` for `curve.ψ`), `ωe_neg_eq_neg_negY`,
   `smulPoly_neg`, `smulRing_neg` and `smulField_neg`.

   **Rewrite-search gotcha (recurring).** mathlib's generic `map_sub`/`map_neg`
   *and* `Jacobian.comp_smul`/`Jacobian.map_neg` do not fire under `rw`/`simp`
   when the function argument leaves implicit instances unresolved — e.g.
   `rw [map_sub]` cannot see `polyToField (a - b)`, even though
   `exact map_sub polyToField a b` typechecks. The fix throughout is a
   *monomorphic helper lemma* proved by `exact`, used as a rewrite rule:
   ```lean
   lemma polyToField_comp_smul (P : Fin 3 → Poly) (u : Poly) :
       polyToField ∘ (u • P) = polyToField u • (polyToField ∘ P) :=
     Jacobian.comp_smul polyToField P u
   ```
   Also: `Jacobian.map` is a separate def from `WeierstrassCurve.map` (they agree
   definitionally), and `ext i` on a `Fin 3 → Poly` goal recurses into
   `MvPolynomial.ext`, so `funext i` is required.

   **Step 3b complete.** The evaluation layer `smulEval`,
   `ringEval_comp_smulRing`, `ringEval_ψ`, `dblXYZ_smulEval`,
   `addXYZ_smulEval`, `addXYZ_smulEval₁`, and the target
   **`zsmul_eq_smulEval`** (`(n • P).point = ⟦smulEval W x y n⟧`) are all
   ported.
   **Step 4 complete** (`FLTForHuman/Elliptic/Bridge.lean`): `evalEval_ψ_sq`
   (`(ψ n)² = ΨSq n` at a point of the curve), `evalEval_φ` (`φ n = Φ n`), and
   the bridge `smul_eq_zero_iff_evalEval_ψ`
   (`n • P = 0 ↔ ψ n(x, y) = 0`).

**Steps 5-6, the counting argument** (`P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean`,
1335 lines, ~35 declarations). All ported, in
`FLTForHuman/Elliptic/Fiber.lean`: `sub_negY_sq_eq_Ψ₂Sq_eval`,
`ΨSq_eval_eq_zero_of_preΨ`, `isCoprime_ΨSq_succ` (the first consumer of the
multiplication bridge — a common root of `ΨSq n` and `ΨSq (n + 1)` gives a point
killed by both `n` and `n + 1`, hence by `1`), `smul_formula_or_zero`,
`smul_x_eq`, `eval_ne_of_isCoprime`, `isCoprime_Φ_ΨSq` (the Wronskian
coprimality: the `Φ`-relation turns a common root into a root of `preΨ (n+1)` or
`preΨ (n-1)`, contradicting `isCoprime_ΨSq_succ`), and
`smul_eq_zero_of_ΨSq_eval_eq_zero`, then the root-counting layer:
`squarefree_roots_nodup`, `separable_of_splits_of_squarefree`,
`wronskian_Φ_ΨSq_ne_zero` (the degree bookkeeping at coefficient
`2n² - 2`), `finite_not_squarefree_fiber`, `smul_surjective` (multiplication by
odd `n` is onto) and `card_smul_fiber` (every fibre has the cardinality of the
`n`-torsion). **Clutter win:** FLT's local `nTorsion` wrapper is already gone
here — `card_smul_fiber` states its target as
`Submodule.torsionBy ℤ M n`, so no later reconciliation is needed.
Dropped as planned: the local `nTorsion` wrapper and `p2m_exact_reverting`.
**Ported since:** the `qpoly` block (`qpoly`, `degree_qpoly`,
`qpoly_ne_zero`, `isRoot_qpoly_iff`, `exists_equation_y`), `coords`,
`Ψ₂Sq_ne_zero_of_isElliptic`, and **`exists_double_fiber_card`** — the heart of
the count: a `Q` is found with `2 * n ^ 2` preimages of `n •` up to sign, via
the `coords` bijection onto the `2n²`-element set `R2fin` of `(x, y)` with
`p.eval x = 0` and `Equation x y`. (An earlier note here wrongly called `coords`
dead code; it is used by exactly this proof.)

**Ported since:** `card_nTorsion_odd_fibers` (odd `n` gives `#E[n] = n²`, using
`exists_double_fiber_card` plus a parity argument in the `Q = -Q` branch) and
`mem_nTorsion_two_iff`. Both are stated over mathlib's `Submodule.torsionBy`
rather than FLT's `nTorsion`; the only adaptation needed is
`AddSubgroup.addOrderOf_coe` applied to `(Submodule.torsionBy …).toAddSubgroup`.

**Duplication removed:** FLT's `smul_surjective_all` / `card_smul_fiber_all`
(955-1052) are *identical* to `smul_surjective` / `card_smul_fiber` — the
`hodd : Odd n` hypothesis is never used — so rather than port them, the two
existing lemmas were generalised (dropping `hodd`) and
`card_nTorsion_odd_fibers`'s calls updated. 98 lines never written (955–1052).

**Ported since:** `card_nTorsion_two` (`#E[2] = 4`, via mathlib's
`twoTorsionPolynomial` and `Cubic.card_roots_of_discr_ne_zero`).

**Complete.** The remaining counting lemmas are all ported:
`card_nTorsion_one` (via `Submodule.mem_bot`/`AddSubgroup.card_bot`),
`card_nTorsion_prime` (splitting on `p = 2`),
`card_nTorsion_prime_pow` (the `Σ`-fibration
`E[p^(k+1)] ≃ Σ_{Q ∈ E[p]} {P // p^k • P = Q}`),
`card_nTorsion_mul_of_coprime` (the Bézout/CRT product decomposition),
the assembly `card_nTorsion` (by `Nat.recOnPosPrimePosCoprime`), and finally
**`card_torsion_of_isAlgClosed`** — the theorem itself, `#E[n] = n²`.

Because every lemma in this file was stated over mathlib's
`Submodule.torsionBy` from the start, the theorem is a one-line alias for
`card_nTorsion`: FLT's `solution` needed a `subtypeEquivRight` reconciliation
between its local `nTorsion` and `Submodule.torsionBy`, and that step simply
does not exist here.