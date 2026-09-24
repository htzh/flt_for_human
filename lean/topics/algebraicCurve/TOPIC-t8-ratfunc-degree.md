# T8 — the `P¹` places and degree (11 nodes)

**Status (2026-09-23): work order written, not started.** Third topic of SET 2;
read [SET-2.md](SET-2.md) first. Depends on SET 1's **AC0, T1** only — it is
independent of T5/T6, which is why it sits after them in the run order and can be
done even if the T5 scout stalls.

**Audience.** A fresh session continuing SET 2. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../PORTING-AC.md) §3.2 (Route B), §5 (T8's note) and §8
(risk 6). Read the SET 1 hand-off in [SET-2.md](SET-2.md) §0 — in particular that
**AC0 already ported the `P¹` vocabulary and the `WFf` residue-field block** into
`Defs/RatFuncPlaces.lean`.

**Goal.** Classify the places of `K(t)`: the finite places are
`Place.ofHeightOneSpectrum w` for `w : HeightOneSpectrum K[X]`, the infinite one is
`Place.placeInfty`, the support `{v | v.ord f ≠ 0}` is finite, and a principal
divisor of a polynomial has degree zero — the `P¹` base case of
`HasPrincipalDivisors`. Eleven nodes in
`FLTForHuman/AlgebraicCurve/PrincipalDivisors/RatFuncDegree.lean`.

## 1. The scouted inventory — all 11

| declaration | raw/c | ext | pin route |
|---|---|---|---|
| `finite_setOf_ord_ne_zero` | 196/128 | 12 | subset of `Finite.image … ∪ Subsingleton.finite`, using the `P¹` bridge |
| `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` | 158/93 | 16 | the dichotomy `ofHeightOneSpectrum`-or-`placeInfty` |
| `exists_forall_ne_ofHeightOneSpectrum` | 138/76 | 3 | `placeInfty` is not a finite place |
| `degree_eq_zero_of_forall_eq_ord_algebraMap` | 147/102 | 1 | `UniqueFactorizationMonoid.induction_on_prime` + a local `finitePlace` + the explicit divisor |
| `deg_ofHeightOneSpectrum` | 129/92 | 2 | **AC0's `residueFieldEquivOfHeightOneSpectrum`** + `finrank_quotient_span_eq_natDegree` |
| `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` | 117/84 | 3 | `toValuationSubring_eq_of_forall_ne…` + `WFg.exists_sub_algebraMap_intDegree_neg` + `Module.finrank_self` |
| `degree_eq_zero_of_forall_eq_ord` | 46/31 | 12 | `RatFunc.num`/`denom` reduction to the polynomial case |
| `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` | 25/10 | 4 | T1's `ord_eq_neg_log_of_valuationSubring_eq` at `RatFunc.inftyValuation` |
| `ord_ofHeightOneSpectrum_of_span` | 22/9 | 16 | `HeightOneSpectrum.intValuation_singleton` |
| `ord_ofHeightOneSpectrum_eq_neg_log` | 21/8 | 1 | the previous + `ord_eq_neg_log_of_valuationSubring_eq` |
| `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` | 25/10 | 0 | **Ostrowski**: `RatFunc.valuation_isEquiv_infty_or_adic` |

Statements verbatim from the wrappers:

```lean
theorem AlgebraicCurve.RationalFunctionField.finite_setOf_ord_ne_zero {K : Type*} [Field K]
    {f : RatFunc K} (hf : f ≠ 0) : {v : Place K (RatFunc K) | v.ord f ≠ 0}.Finite

theorem AlgebraicCurve.RationalFunctionField.subsingleton_setOf_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] :
    {v : Place K (RatFunc K) | ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w}.Subsingleton

theorem AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] : ∃ v : Place K (RatFunc K),
      ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
        v ≠ Place.ofHeightOneSpectrum w

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord_algebraMap
    {K : Type*} [Field K] (q : Polynomial K) : ∀ D : Divisor K (RatFunc K),
      (∀ v : Place K (RatFunc K), D v = v.ord (algebraMap (Polynomial K) (RatFunc K) q)) →
        Divisor.degree D = 0

theorem AlgebraicCurve.RationalFunctionField.deg_ofHeightOneSpectrum
    (K : Type*) [Field K] {w : IsDedekindDomain.HeightOneSpectrum (Polynomial K)}
    {p : Polynomial K} (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).deg = p.natDegree

theorem AlgebraicCurve.RationalFunctionField.deg_eq_one_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) : v.deg = 1

theorem AlgebraicCurve.RationalFunctionField.degree_eq_zero_of_forall_eq_ord
    {K : Type*} [Field K] {f : RatFunc K} (D : Divisor K (RatFunc K))
    (hD : ∀ v : Place K (RatFunc K), D v = v.ord f) : Divisor.degree D = 0

theorem AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) {f : RatFunc K} (hf : f ≠ 0) :
    v.ord f = -f.intDegree

theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_of_span
    {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K))
    {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) :
    (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord
      (algebraMap (Polynomial K) (RatFunc K) p) = 1

theorem AlgebraicCurve.RationalFunctionField.ord_ofHeightOneSpectrum_eq_neg_log
    {K : Type*} [Field K] (w : IsDedekindDomain.HeightOneSpectrum (Polynomial K))
    {p : Polynomial K} (hp : p ≠ 0) (hw : w.asIdeal = Ideal.span {p}) {f : RatFunc K}
    (hf : f ≠ 0) : (Place.ofHeightOneSpectrum (K := K) (F := RatFunc K) w).ord f =
      -WithZero.log (w.valuation (RatFunc K) f)

theorem AlgebraicCurve.RationalFunctionField.toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum
    {K : Type*} [Field K] [DecidableEq (RatFunc K)] (v : Place K (RatFunc K))
    (hv : ∀ w : IsDedekindDomain.HeightOneSpectrum (Polynomial K),
      v ≠ Place.ofHeightOneSpectrum w) :
    v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring
```

## 2. Route notes

### 2.1 The `P¹` classification prelude is AC0's — write nothing twice

The pin's first three files (`finite_setOf_ord_ne_zero`,
`subsingleton_setOf_forall_ne_ofHeightOneSpectrum`,
`exists_forall_ne_ofHeightOneSpectrum`) each carry a **private bridge block**: `'`-copies
of `adicValuation_valuationSubring`, `mem_iff_adicValuation_le_one`,
`isEquiv_adicValuation_of_valuationSubring_eq`,
`ord_eq_zero_iff_adicValuation_eq_one`,
`isEquiv_adicValuation_ofHeightOneSpectrum`, plus `nontrivial_valueGroup_inftyValuation`,
`placeInfty'`, `placeInfty'_ne_ofHeightOneSpectrum`,
`eq_ofHeightOneSpectrum_or_eq_placeInfty'` and `finite_setOf_valuation_ne_one'`. The
blueprint §4.1 measures ≈214 content lines never written by stating them once. **AC0
already wrote the public originals** in `Defs/RatFuncPlaces.lean`
(`Place.adicValuation_valuationSubring`, `Place.mem_iff_adicValuation_le_one`,
`Place.isEquiv_adicValuation_of_valuationSubring_eq`,
`Place.ord_eq_zero_iff_adicValuation_eq_one`,
`Place.isEquiv_adicValuation_ofHeightOneSpectrum`,
`RationalFunctionField.{nontrivial_valueGroup_inftyValuation, placeInfty,
placeInfty_toValuationSubring}`). So T8 writes **no** `'`-copies: the three nodes use
AC0's names directly.

The only genuinely T8-local helper is the **dichotomy**: `[DecidableEq (RatFunc K)]`
and the private `eq_ofHeightOneSpectrum_or_eq_placeInfty`
(`∀ v, (∃ w, v = ofHeightOneSpectrum w) ∨ v = placeInfty`), which the pin derives
from `RatFunc.valuation_isEquiv_infty_or_adic` (Ostrowski) plus
`Place.isEquiv_adicValuation_ofHeightOneSpectrum` and
`Place.isEquiv_adicValuation_of_valuationSubring_eq` (T1). Write it once, private,
in `RatFuncDegree.lean`.

### 2.2 Per-node routes

- **`toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` is Ostrowski in
  mathlib's shape.** With `haveI := v.adicValuation_isRankOneDiscrete` and
  `haveI := v.adicValuation_isTrivialOn` (T1/AC0), apply
  `RatFunc.valuation_isEquiv_infty_or_adic (v := v.adicValuation)`; the `Xor`'s left
  branch gives `v.toValuationSubring = (RatFunc.inftyValuation K).valuationSubring`
  through `Valuation.isEquiv_iff_valuationSubring`, and the right branch
  (`∃! u, …`) contradicts `hv` through `Place.ext`. It needs
  `[DecidableEq (RatFunc K)]` (the wrapper's binder) — the topic's named risk.
- **`finite_setOf_ord_ne_zero`** is a subset of
  `Finite.image (Place.ofHeightOneSpectrum) (finite_setOf_valuation_ne_one) ∪
  (Subsingleton.finite subsingleton…)`. Write the private
  `finite_setOf_valuation_ne_one` (finiteness of `{w | w.valuation (RatFunc K) f ≠ 1}`
  over `HeightOneSpectrum K[X]`, via `Ideal.finite_factors`) and the private
  `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` (the dichotomy at
  `v = placeInfty`). The member rewrite is `ord = 0 ↔ adicValuation = 1`
  (`Place.ord_eq_zero_iff_adicValuation_eq_one`, AC0) through
  `isEquiv_adicValuation_ofHeightOneSpectrum`.
- **`degree_eq_zero_of_forall_eq_ord_algebraMap`** is the `P¹` base case:
  `UniqueFactorizationMonoid.induction_on_prime q` with the three cases (zero:
  `D = 0`; unit: `algebraMap C r = algebraMap K r` and T1's `Place.ord_algebraMap`;
  prime: build `Dp := single (finitePlace hp.irreducible) 1 + single vinf (-(p.natDegree : ℤ))`,
  show `Dp v = v.ord (algebraMap p)` by the private
  `single_add_single_apply_eq_ord`, show `degree Dp = 0` by the private
  `degree_single_add_single` — which is where `degree_single`, `deg_ofHeightOneSpectrum`
  and `deg_eq_one_of_forall_ne…` meet — and apply the induction hypothesis to
  `D - Dp`). Port the three private helpers (`ne_finitePlace_of_forall_ne`,
  `single_add_single_apply_eq_ord`, `degree_single_add_single`) with it.
- **`degree_eq_zero_of_forall_eq_ord`** reduces `f = num / denom`:
  `D + Dden` is the polynomial divisor of `RatFunc.num`, where `Dden` is built on
  T8's `finite_setOf_ord_ne_zero`; apply the `algebraMap` version to both and
  subtract.
- **`deg_ofHeightOneSpectrum`** is **one line after AC0**: rewrite by `Place.deg`,
  `(residueFieldEquivOfHeightOneSpectrum K w).toLinearEquiv.finrank_eq`, and
  `finrank_quotient_span_eq_natDegree`. Do not re-port the pin's `WFf` block — it
  is the copy of `Def_RatFuncPlaces:128–232` that AC0 already wrote.
- **`deg_eq_one_of_forall_ne_ofHeightOneSpectrum`** uses
  `toValuationSubring_eq_of_forall_ne…`, the private
  `exists_sub_algebraMap_intDegree_neg` (the pin's `WFg` helper: for
  `RatFunc.inftyValuation K x ≤ 1` there is `c : K` with
  `x - algebraMap K (RatFunc K) c = 0` or `intDegree < 0`), a residue-field
  bijectivity argument, and `Module.finrank_self`. Port the helper `private`.
- **`ord_eq_neg_intDegree_of_forall_ne…`** is T1's
  `Place.ord_eq_neg_log_of_valuationSubring_eq` at `(RatFunc.inftyValuation K)`
  with `hπ : RatFunc.inftyValuation K (RatFunc.X)⁻¹ = exp (-1)`, then
  `RatFunc.inftyValuation_apply`/`inftyValuation_of_nonzero`/`log_exp`.
- **`ord_ofHeightOneSpectrum_of_span` and `_eq_neg_log`** both start from
  `HeightOneSpectrum.intValuation_singleton` + `valuation_of_algebraMap` to get
  `w.valuation (RatFunc K) (algebraMap p) = exp (-1)`, then use `_eq_neg_log`
  (the first) or T1's `ord_eq_neg_log_of_valuationSubring_eq` at
  `w.valuation (RatFunc K)` (the second).

### 2.3 What is deliberately not written

`placeOfPoint` and the whole `Place.Congr` section (blueprint §3.5's measured
negative), and the `WFf`/`WFg`-style `'`-copies. `finitePlace`/`deg_finitePlace` are
AC0's and are used, not re-declared. Do not write a second `deg_ofHeightOneSpectrum`
(the pin's `P2M.Dup` duplicate); AC0's `deg_ofHeightOneSpectrum` is already in
`Defs/RatFuncPlaces.lean` — check whether T8's node is that same declaration or a
distinct one before adding anything. (SET 1's hand-off lists
`RationalFunctionField.deg_ofHeightOneSpectrum` as already public in AC0; if so, T8's
`deg_ofHeightOneSpectrum` node is already proved and the work is only the other ten.)

## 3. Named shape risks

| risk | mitigation |
|---|---|
| Ostrowski in mathlib's shape | `RatFunc.valuation_isEquiv_infty_or_adic` returns `Xor` + `∃!`; unfold both branches, do not restate |
| `DecidableEq (RatFunc K)` | the wrapper requires it on the `toValuationSubring_eq…` node; carry the instance and keep `classical` where `Finset`/`Finsupp` need it |
| the `P2M.Dup` duplicate | AC0 already wrote one `deg_ofHeightOneSpectrum`; check the checker's source before writing a second |
| the private `WFg` helper | it is T8-local; port it `private` so the checker never sees it |
| `finite_setOf_ord_ne_zero`'s union/subset argument | build the two private finiteness facts first (`finite_setOf_valuation_ne_one`, `subsingleton…`), then the subset |

## 4. Budget and stop-early

**3 goal rounds, checkpoint at 1.** 643 content lines across 11 nodes, but three of
them share the (now-free) prelude and one is a one-liner after AC0. The `WFg` helper
and the `WFf`-duplicate decision are the only places it can stall.

**Stop early, and report rather than restate, on**: the `P2M.Dup` duplicate turning
out to be a *different* statement from AC0's; Ostrowski's `∃!` branch needing a
statement mathlib does not have; or `finite_setOf_ord_ne_zero` needing a finiteness
result the AC0 `RatFuncPlaces` surface does not expose.

## 5. Definition of done

- [ ] `PrincipalDivisors/RatFuncDegree.lean` with the 11 nodes public (statements
      verbatim), all helpers private, no `'`-copies of AC0 declarations.
- [ ] Consumer **Zone H** (`[principal]`, first half) at 0 errors:
      `finite_setOf_ord_ne_zero` and `degree_eq_zero_of_forall_eq_ord` on a concrete
      rational function (e.g. `RatFunc.X` or `Polynomial.X`), plus
      `deg_ofHeightOneSpectrum`/`deg_eq_one…` on `RatFunc.X`'s place.
- [ ] `spec/check_flt_statements.py`: the 11 wrappers in `SOURCES`; 0 mismatched,
      0 missing.
- [ ] `#print axioms` on `finite_setOf_ord_ne_zero` and
      `degree_eq_zero_of_forall_eq_ord_algebraMap` clean.
- [ ] `timeout 90 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T8 section (with the real prelude saving vs the 214-line
      estimate); `README.md` row.
- [ ] The T9 hand-off: `finite_setOf_ord_ne_zero` and
      `degree_eq_zero_of_forall_eq_ord` are public and usable from
      `PrincipalDivisors/Transcendence.lean`.

## 6. Reporting back

Beyond [SET-2.md](SET-2.md) §3: (1) the real prelude saving; (2) whether
`deg_ofHeightOneSpectrum` was already AC0's (and therefore not rewritten);
(3) Ostrowski's actual shape and whether the `∃!` branch was as the blueprint
described.
