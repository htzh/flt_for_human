# The rational function field and principal divisors

**Status: OUTLINE — for review. The prose is not yet written; this file fixes the
scope, the section plan and the declaration inventory so the coverage can be
checked first.** Planned as `base/017`, the third of the three notes carrying the
mathlib-level mathematics of the `AlgebraicCurve` port
([../lean/PORTING-AC.md](../lean/PORTING-AC.md), topics **T8–T9**).

## Why this note

[008](008-divisors-and-pic0.md) §3 and §8 introduce
`HasPrincipalDivisors` — the residue theorem stated as a *hypothesis*, because it
is not automatic for an arbitrary field extension — and record that it is
discharged for `ℚ̄(X₀(N))` by
`hasPrincipalDivisors_modularFunctionFieldBar`, "conditional on the
modular-polynomial family". What 008 does not explain is **how** that discharge
works, and the FLT proof does not go through the modular polynomial for it: the
generic theorem is `hasPrincipalDivisors_of_transcendental`, and the concrete
input on the `P¹` side is the classical place theory of `K(t)`.

This note supplies both:

1. the **places of the rational function field** `K(t)` — Ostrowski's dichotomy,
   the finite places from `HeightOneSpectrum K[X]`, the infinite place, the
   residue degree `deg = p.natDegree` at a finite place and `1` at infinity;
2. the **degree-zero principal divisor** $`\mathrm{div}(p) =
   [\mathfrak{p}] - (\deg p)[\infty]`$ and the corresponding statement for a
   rational function;
3. the **transfer to a finite extension** by the norm, which is what turns the
   `P¹` case into `HasPrincipalDivisors K F` for `F` a finite separable extension
   of `K(t)` with `t` transcendental.

This is the mathematics behind `hasPrincipalDivisors_modularFunctionFieldBar` and
behind the `hP` input of the Hecke exchange in
[math/009](../math/009-hecke-jacobian-commute.md) §5. It consumes
[015](015-places-and-extensions.md) §3 (the fibre-centre dictionary) and the norm
formula stated in [016](016-correspondences-and-exchange.md) §5.

## Planned sections

### 0. Scope and placement
- Why `HasPrincipalDivisors` is a hypothesis at all (008 §3/§8): the residue
  theorem is a theorem about curves, not a formal consequence.
- The two-layer route: `P¹` explicitly, then finite extensions by norms. Contrast
  with the "conditional on `Φ_N`" remark in 008 §8 — the generic theorem does not
  need the modular polynomial; only the *modular instantiation* as stated there
  does.
- Reading order: [015](015-places-and-extensions.md) → this note;
  [016](016-correspondences-and-exchange.md) supplies `ord_norm_eq_sum_fiberOver`.

### 1. The places of `K(t)` (T8)
- `RatFunc K`, `RatFunc.inftyValuation`; the **infinite place** `placeInfty` as the
  `Place` whose valuation subring is `(RatFunc.inftyValuation K).valuationSubring`.
- The **finite places**: `HeightOneSpectrum K[X]`, `heightOneSpectrumOfIrreducible`,
  `Place.ofHeightOneSpectrum`, `finitePlace`, `algebraMap_mem_ofHeightOneSpectrum`.
- **Ostrowski's dichotomy**: any place of `K(t)` is a finite place or the infinite
  place. mathlib's `RatFunc.valuation_isEquiv_infty_or_adic` is the mathematical
  input; the FLT packaging is `eq_ofHeightOneSpectrum_or_eq_placeInfty'` plus
  `Place.ext` and `Valuation.isEquiv_iff_valuationSubring`. Consequence:
  `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` (the complement of the finite
  places has at most one point) and `exists_forall_ne_ofHeightOneSpectrum` (it is
  nonempty), hence
  `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` (a non-finite place is
  the infinite one).
- **Residue degrees**: `deg_ofHeightOneSpectrum` (at `w` with
  `w.asIdeal = span{p}`, the degree is `p.natDegree`, via
  `finrank_quotient_span_eq_natDegree` and the residue iso
  `residueFieldEquivOfHeightOneSpectrum`), `deg_eq_one_of_forall_ne_ofHeightOneSpectrum`
  (a non-finite place has degree `1`). Note the `P2M.Dup` duplication between the
  `S_` proof and `Def_AlgebraicCurve_RatFuncPlaces`: one development, shipped twice.

### 2. Orders at the two kinds of place (T8)
- At a finite place: `ord_ofHeightOneSpectrum_of_span` — the order of the generator
  `p` is `1`; `ord_ofHeightOneSpectrum_eq_neg_log` — in general
  `ord_w(f) = -log(w.valuation f)`; `ord_ofHeightOneSpectrum_ne_zero_iff`.
- At the infinite place: `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` —
  $`\mathrm{ord}_\infty(f) = -\mathrm{intDegree}(f)`$, the "pole at infinity has
  order equal to the degree" statement. `RatFunc.intDegree` and the
  `num`/`denom` normal form are the tools.
- The bridge lemmas from [015](015-places-and-extensions.md) §1 that these consume:
  `ord_eq_neg_log_of_valuationSubring_eq`, `isEquiv_adicValuation_of_valuationSubring_eq`.

### 3. The degree-zero principal divisor on $`P^1`$ (T8)
- A polynomial `q` has divisor `single(finitePlace, 1) + single(vinf, -q.natDegree)`
  when `q` is irreducible, and `degree_single_add_single` shows the degree is `0`;
  the general statement `degree_eq_zero_of_forall_eq_ord_algebraMap` reduces along
  the unique factorisation of `q`, using `UniqueFactorizationMonoid.induction_on_prime`.
- The rational-function case `degree_eq_zero_of_forall_eq_ord`: for `f = num/denom`,
  apply the polynomial case to `num` and `denom`, using
  `finite_setOf_ord_ne_zero` for the support and additivity of `degree`.
- **Finiteness of the support**: `finite_setOf_ord_ne_zero` — only the finitely many
  irreducible factors of `num` or `denom` can have order nonzero, plus at most the
  infinite place; `Ideal.finite_factors` and the subsingleton above.
- Why this is exactly the residue theorem of 008 §3 for `K(t)`.

### 4. Principal divisors for a finite extension of `K(t)` (T9)
- The reduction `hasPrincipalDivisors_of_finiteDimensional_ratFunc`: for
  `K` of characteristic zero, `t` transcendental, `F` finite over `K(t)`, and
  `f ≠ 0`, build the divisor `D = Finsupp.onFinset (finite_setOf_ord_ne_zero_of_finiteDimensional f) (ord f)`,
  then prove `degree D = 0` by pushing `D` forward to `K(t)` and applying §3.
- **The pushforward identity**: `pushforwardNormFormula_of_finiteDimensional`,
  i.e. `φ_* div f = div (Norm f)` for `φ : K(t) → F`, via
  `ord_norm_eq_sum_fiberOver`
  ($`\mathrm{ord}_v(N f) = \sum_{w \mid v} e(w) f(w) \mathrm{ord}_w(f)`$).
- **The norm computation**, the heart of the note:
  - the normalised-valuation uniqueness lemma `eq_ord_of_addHom_of_nonneg_iff`
    and `neg_log_valuation_fiberCenter_eq_ord` (from
    [015](015-places-and-extensions.md) §3);
  - `relNorm_fiberCenter`: the relative norm of the fibre-centre prime is the
    maximal ideal to the inertia degree;
  - `count_normalizedFactors_span_singleton`, `relNorm_span_singleton`: factor
    `span{c}` into `normalizedFactors` and compute `Ideal.relNorm` prime by prime;
  - `ord_norm_algebraMap_integralClosureAt`, then `ord_norm_eq_sum_fiberOver` for
    arbitrary `f` by clearing denominators.
- The two public statements: `hasPrincipalDivisors_of_transcendental`
  (`Transcendental K x` + `FiniteDimensional K⟮x⟯ F`) and
  `hasPrincipalDivisors_adjoin_of_transcendental` (the `adjoin K (insert x T)`
  form with `T` integral over `K⟮x⟯`). One sentence on the separate
  `_of_isSeparable` route and why it is not used here.

### 5. How the code says this
- Encoding choices: `HasPrincipalDivisors` is a `class`; the `P¹` route works with
  `Place K (RatFunc K)` but the transfer works with `Place K F` for a finite
  `F/K⟮x⟯`; `Ideal.relNorm` needs `PerfectField` in v4.34 (`[CharZero F]` suffices,
  but the instance must fire); the duplicate
  `hasPrincipalDivisors_of_finiteDimensional_ratFunc` development.
- Key-point → declaration map.
- Traps: `DecidableEq (RatFunc K)` for Ostrowski; the `exp`/`log` `rfl`
  identifications; the `P2M.Dup` copy of `deg_ofHeightOneSpectrum`; the
  `placeOfPoint`/`Place.Congr` machinery that this route does **not** use.

### 6. Links
- FLT sources at `aa2d8b3`: `Def_AlgebraicCurve_RatFuncPlaces`,
  `Def_AlgebraicCurve_RatFuncPlaceInfty` (for `placeInfty`),
  `Def_AlgebraicCurve_DivisorClassGroup` (`Place.ofHeightOneSpectrum`),
  `Def_AlgebraicCurve_PlacesOverDVR`, the `S_` files of T8–T9, and the
  `Theorems/` wrappers.
- mathlib at `v4.33.0`: `FieldTheory/RatFunc/{Basic,Degree,Valuation,AsPolynomial}`,
  `NumberTheory/RatFunc/Ostrowski`, `RingTheory/Ideal/Norm/RelNorm`,
  `RingTheory/DedekindDomain/{Factorization,AdicValuation}`,
  `RingTheory/AdjoinRoot` (`finrank_quotient_span_eq_natDegree`),
  `RingTheory/UniqueFactorizationDomain/Basic`.
- Companion notes: [008](008-divisors-and-pic0.md) §3,
  [015](015-places-and-extensions.md), [016](016-correspondences-and-exchange.md) §5,
  [math/009](../math/009-hecke-jacobian-commute.md) §5,
  [math/010](../math/010-function-field-generation.md) (the modular instantiation).

## Planned key-point → declaration map

| Mathematics | Lean declaration | AC topic |
|---|---|---|
| the infinite place of `K(t)` | `placeInfty`, `RatFunc.inftyValuation` | T8 |
| finite places from height-one primes | `heightOneSpectrumOfIrreducible`, `finitePlace`, `Place.ofHeightOneSpectrum` | T8 |
| Ostrowski: finite or infinite | `RatFunc.valuation_isEquiv_infty_or_adic`, `eq_ofHeightOneSpectrum_or_eq_placeInfty'` | T8 |
| the complement of the finite places | `subsingleton_setOf_forall_ne_ofHeightOneSpectrum`, `exists_forall_ne_ofHeightOneSpectrum` | T8 |
| residue degree at a finite place | `deg_ofHeightOneSpectrum` | T8 |
| residue degree at infinity | `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` | T8 |
| order at a finite place | `ord_ofHeightOneSpectrum_of_span`, `ord_ofHeightOneSpectrum_eq_neg_log` | T8 |
| order at infinity | `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` | T8 |
| degree-zero divisor of a polynomial | `degree_eq_zero_of_forall_eq_ord_algebraMap` | T8 |
| degree-zero divisor of a rational function | `degree_eq_zero_of_forall_eq_ord` | T8 |
| finite support of `div f` | `finite_setOf_ord_ne_zero` | T8 |
| norm of the fibre-centre prime | `relNorm_fiberCenter` | T9 |
| norm of a principal ideal | `relNorm_span_singleton`, `count_normalizedFactors_span_singleton` | T9 |
| local norm formula | `ord_norm_eq_sum_fiberOver` | T9 |
| norm of a principal divisor | `pushforwardNormFormula_of_finiteDimensional` | T9 |
| principal divisors of a finite extension | `hasPrincipalDivisors_of_finiteDimensional_ratFunc` | T9 |
| the public generic theorem | `hasPrincipalDivisors_of_transcendental` | T9 |
| the adjoin form | `hasPrincipalDivisors_adjoin_of_transcendental` | T9 |

## Open questions for the review

- Does the note want a small §7 with a `K = ℚ` worked example (say `p = X² + 1`
  over `ℚ` and its two conjugate places), or is the mathematics enough? The other
  base notes usually carry a `pymath/` computation; there is no existing demo for
  this, so a worked example would need a new script. Plan: **no demo** unless
  requested; note the gap.
- Should the `_of_isSeparable` route (uses `sum_ramification × inertia` and
  `Divisor.degree_eq_sum`, no `relNorm`) be documented as an alternative, or
  omitted? Plan: one paragraph in §4, no full treatment.
- Length target: ~450–600 lines.
