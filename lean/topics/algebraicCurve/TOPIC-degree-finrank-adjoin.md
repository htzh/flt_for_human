# The degree identity `deg (x)_∞ = [F : K(x)]`

**Status: landed 2026-10-23, all four nodes.** When this note was written,
`frontier.py --ds --ready --nexus --fanin-min 6` put the first inequality at the head of
its ready shelf (`AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord`,
needed 1 / 230). The whole identity is **four nodes / 1,204 pin lines**, every premise
already in the port. It is now ported whole into the two homes below: A in
`AlgebraicCurve/Place/Approximation.lean` (330 lines), L, U, E in
`AlgebraicCurve/Genus/DegreeIdentity.lean` (793 lines) — green, no `sorry`,
`spec/check_port.py` `4 ok / 0 mismatch / 0 missing / 0 own`, and
`[propext, Classical.choice, Quot.sound]` on all four headlines. This note remains the
scoping of that set: the mathematics, the port structure, and the measurement. Record:
[../../logs/degree-finrank-adjoin.md](../../logs/degree-finrank-adjoin.md).

Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.

Companions: the Riemann–Roch blueprint [../PORTING-RR.md](../PORTING-RR.md) (phase 1
built `Genus/Index.lean`, the Stichtenoth engine built `Genus/Stichtenoth.lean`);
the classical statement is Stichtenoth, *Algebraic Function Fields and Codes*
(2nd ed.), Theorem 1.4.11, and Rosen, *Number Theory in Function Fields*,
Proposition 5.1.

## 0. The theory

For a one-variable function field `F/K` in the port's `IsCurveOver` package — `F/K`
finite, `K` the exact constant field, principal divisors of degree `0`, finite
residue fields, free rank-`1` Kähler differentials, and `L(0)` finite-dimensional —
and `x ∈ F` transcendental over `K` with `[F : K(x)]` finite, the **pole divisor**
`D = (x)_∞`, given by

$$D(v) \;=\; \max\bigl(0,\, -\,\mathrm{ord}_v x\bigr),$$

has degree equal to the degree of the field extension:

$$\deg (x)_\infty \;=\; [\,F : K(x)\,].$$

The port scopes the identity as the two inequalities of Stichtenoth's proof plus the
weak-approximation lemma the upper bound consumes:

| id | node | pin `S_` lines | frontier | status |
|---|---|---:|---|---|
| A | `AlgebraicCurve.Place.exists_forall_ord_eq` | 407 | 1 / 407 | landed |
| L | `AlgebraicCurve.Divisor.finrank_adjoin_le_degree_of_eq_max_neg_ord` | 230 | 1 / 230 | landed |
| U | `AlgebraicCurve.Divisor.degree_le_finrank_adjoin_of_eq_max_neg_ord` | 546 | 2 / 953 | landed |
| E | `AlgebraicCurve.Divisor.degree_eq_finrank_adjoin_of_eq_max_neg_ord` | 21 | 4 / 1,204 | landed |

`U` needs `A`; `E` is the 21-line wrapper over `L` and `U`; `L` and `A` are
independent. All four are leaves of the frontier in the sense that only they are
unported — `L`'s six premises, `A`'s helpers and `U`'s inputs are all in the port.

## 1. The mathematics

### 1.1 The lower bound `L`: Riemann–Roch counts `[F:K(x)] ≤ deg D`

Write `E = K(x)`, `n = [F : E]`. Choose an `E`-basis `u₀, …, u_{n-1}` of `F` that is
integral over `A = K[x]` (`FiniteDimensional.exists_is_basis_integral`, valid because
`A` is a domain and `E` its fraction field). At a place `v` with `ord_v x ≥ 0`, `x` is
integral at `v` and so is every `u_i`, hence `ord_v u_i ≥ 0`; at the finitely many
places with `ord_v x < 0` one records the finitely many `ord_v u_i` in a constant `c`.
Then for every `m ≥ c` the products

$$x^{j}\, u_i \qquad (0 \le j \le m-c,\ 0 \le i < n)$$

are `K`-linearly independent (the port's `linearIndependent_pow_mul`, over the
independence of `1, x, x², …` given by `linearIndependent_pow_of_transcendental`),
lie in `L(mD)`, and number `n(m-c+1)`. Hence `n(m-c+1) ≤ ℓ(mD)`. Riemann's inequality
`ℓ(mD) ≤ m·deg D + ℓ(0)` (the port's `ell_le_degree_add_ellZero`, valid because
`0 ≤ D`) then gives `n(m-c+1) ≤ m·deg D + ℓ(0)` for all large `m`, which forces
`n ≤ deg D`.

### 1.2 The weak approximation `A`

For a finite set `T` of places and prescribed integers `n_v`, there is `f ≠ 0` with
`ord_v f = n_v` for every `v ∈ T`. The proof is the standard one: separate the places
pairwise (`exists_mem_and_not_mem`), produce for each `v ∈ T` an element negative at
`v` and positive at the other places of `T` (`exists_ord_neg_and_ord_pos`), and correct
the orders at `T` by multiplying powers with coefficients from the residue fields
(the `exists_forall_ord_eq_of_sep` form).

### 1.3 The upper bound `U`: `deg D ≤ [F:K(x)]`

The second half is the residue-field count. For each `v ∈ D.support` one chooses a
`K`-basis `z_k` of the residue field `κ(v)` (`deg v` elements), lifts it to elements
regular at every place of `D.support`, and uses the weak approximation to force the
lifts to have order `0` at the other places of the support while being units at `v`.
Multiplying by suitable powers of `x` (which has a simple pole at the places of the
support) produces, for large `m`, at least `m·deg D + O(1)` independent elements of
`L(mD)` with poles controlled at `D`; comparing with `ℓ(mD) = n·m + O(1)` from
Riemann–Roch in the other direction gives `deg D ≤ n`. The 546-line proof is the
bookkeeping of that count (residue maps, maximal ideals, `t`-elements with prescribed
orders, `Fin v.deg`-indexed bases), not new mathematics.

### 1.4 The equality `E`

`E` is `le_antisymm` of `L` and `U`: the 21-line wrapper, and the statement the rest of
the port consumes.

## 2. The port structure

### 2.1 Nodes and homes

| id | home | what is written |
|---|---|---|
| A | new `AlgebraicCurve/Place/Approximation.lean` | the headline + its own helpers (the pin's public `adicValuation_le_exp_neg_iff_le_ord`, `ord_coe_unit_eq_zero_of_le`, `exists_mem_and_not_mem`, `exists_ord_neg_and_ord_pos`, …) |
| L, U, E | new `AlgebraicCurve/Genus/DegreeIdentity.lean` | the three headlines; `L`/`U`'s proof-local helpers `private`, `E` a wrapper |

As landed: of A's helpers only the pairwise separation lemma is public — the port
already carries it as `Place.exists_mem_and_not_mem` (`Place/OrdCalculus.lean`), so it is
imported rather than re-proved; the rest have no consumer outside the `S_` file in the pin
or the port and are `private` there, one of them (`Place.ord_coe_unit_eq_zero_of_le`, whose
only pin consumer is that separation lemma) is shelved in
`Reserve/AlgebraicCurve/Place/ApproximationDead.lean`, and one
(`adicValuation_le_exp_neg_iff_le_ord`) is dropped as a rewrite from the port's public
`Place.adicValuation_le_exp_iff`. See the record.

New modules rather than appends: `Genus/Index.lean`, `Genus/Stichtenoth.lean`,
`Defs/Place.lean`, `Defs/PushPull.lean`, `Defs/AdelicIndex.lean` and
`Defs/IsCurveOver.lean` are all legacy `PORT_FILES` modules at 700–1,000 lines; they
are imported, not touched.

### 2.2 Reuse map (every input is already public)

| input | port home |
|---|---|
| `linearIndependent_pow_of_transcendental` | `Genus/Stichtenoth.lean` |
| `linearIndependent_pow_mul` | `Genus/Stichtenoth.lean` |
| `ell_le_degree_add_ellZero` | `Genus/Index.lean` |
| `finiteDimensional_lSpace` | `Genus/Index.lean` |
| `mem_lSpace_iff_ord`, `ell` | `Defs/AdelicIndex.lean` |
| `Place.mem_toValuationSubring_of_isIntegral_adjoin` | `Defs/Place.lean` |
| `Place.ord_nonneg_of_mem` | `Canonical/WeilDifferential.lean` |
| `Place.mem_of_ord_nonneg` | `Defs/PushPull.lean` |
| `Divisor`, `Divisor.degree`, `Place.deg`, `IsCurveOver` | `Defs/` |

Two substitutions in `L`'s proof: the pin proves `LinearIndependent K (fun j => xE ^
j)` inline (12 lines) and then calls `linearIndependent_pow_mul`; the port's
`linearIndependent_pow_of_transcendental` is that first lemma, so the transcribed
proof is shorter than the `S_` file. The same holds for `hli`'s inline
`simpa only [...] using this`.

### 2.3 Order and budget

`A` first (it is the only input of `U`), then `L` in parallel, then `U`, then `E`.
Sizes: `A` 407, `L` 230, `U` 546, `E` 21 pin lines; the port writes ≈1,100 Lean
lines after the two substitutions (the pin's `S_` files carry the full attribute and
heartbeat prologue, which is not transcribed). Measured on landing: **1,123 lines**
(`Approximation.lean` 330, `DegreeIdentity.lean` 793), plus the 52-line shelf.

### 2.4 Verification

Per module: `lake env lean`, `python3 spec/check_port.py <module>` (0 mismatch /
0 missing), `#print axioms` on the four headlines (`[propext, Classical.choice,
Quot.sound]`), no `sorry`, no warnings, no info prints, no machine tokens in names.
For the set: the equality `E` is itself the composition test (`L` + `U`), so a
`spec/*Consumer.lean` zone applies `E` at a hypothesis-form `IsCurveOver` package and
reads off the two inequalities — that is the set's cross-module composition.

## 3. Downstream

`E` is cited by
`AlgebraicCurve.RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq`
→ `exists_placeMap_mapDomain_eq_ord_of_good_constantReduction` →
`Divisor.exists_natCast_dvd_ord_sub_of_constantFieldExtension` →
`ModularCurve.JZero.divisible` → `mazurQuotientSpecialization_heckeModuleBar` →
Mazur step three. It is also the classical degree identity the Riemann–Roch layer
states against, so the four nodes are on both the Mazur chain and the RR interface.

## 4. What the notes must not claim

- The identity is **not** assumed to be separable: `L`'s proof works for any finite
  `F/K(x)`. Do not add a separability hypothesis to the statement.
- `A` is weak approximation at **finitely many** places, not strong approximation.
- `D` is the pole divisor of `x` and `hD` pins it pointwise (`D v = max 0 (-v.ord x)`);
  it is not an arbitrary divisor of degree `[F:K(x)]`.
- `IsCurveOver` is the port's curve package, not a bare `Algebra K F`; the statements
  must keep its instance binders verbatim.
