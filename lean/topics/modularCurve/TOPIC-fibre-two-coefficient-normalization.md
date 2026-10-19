# The `N = 2` fibre's olean hog — normalizing the three coefficient identities

**Status: landed (2026-10-16/17); the public statement is untouched.**
`FLTForHuman/ModularCurve/ModularPolynomialFibreTwo.lean` was, at **82.4 MiB**, the largest
`.olean` in the tree — 1.4× the runner-up (`Velu/OrderTwoMap`, 60.3 MiB) and ~50× the next
`ModularCurve` module. Per-declaration isolation puts essentially all of it in the three
`private` coefficient identities, each closed by `field_simp; ring` (their isolated sizes sum to
85 MiB against the module's 82.4 MiB — isolated runs share no subterms, so the sum
over-counts). Those three are
translation-invariant in the three roots, so they can be proved for a *normalized* root triple;
normalizing by `x₀` — which needs no division, hence is sound in characteristic 3 — shrinks each
cleared identity from hundreds of monomials to dozens and takes the module to **5.16 MiB** and
**6.3 s**. This note records the measurement (§1), the mechanism (§2), the normalization (§3),
the landed change (§4), verification (§5) and what to reuse (§6).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

Companions: the row that landed the module,
[WORKORDER-B2-fibre-two.md](WORKORDER-B2-fibre-two.md), and its scoping note
[TOPIC-levelN-and-modular-polynomial.md](TOPIC-levelN-and-modular-polynomial.md); the sibling
refactor note [../velu/TOPIC-order-two-tangent-direct.md](../velu/TOPIC-order-two-tangent-direct.md)
— the same "move to shifted coordinates first" move, on the Vélu certificates; the mathematics of
the order-two quotient, including the `velu2QuadDisc` it consumes, is
[../../../math/029-order-two-velu-quotient-and-its-cleared-identities.md](../../../math/029-order-two-velu-quotient-and-its-cleared-identities.md);
build-cost context is [../../../notes/lean-build-cost.md](../../../notes/lean-build-cost.md).

## 1. The measurement that found it

A `.olean` is byte-exact for a given source, so sizes are the comparison that holds; the wall
times below come from contended 4-thread tree builds (before) and one `lake build` (after), and
are magnitudes only. Before the change, the tree's top `.olean`s were:

| module | `.olean` |
|---|---:|
| `FLTForHuman.ModularCurve.ModularPolynomialFibreTwo` | **82.4 MiB** (86,436,408 B) |
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` | 60.3 MiB |
| `FLTForHuman.WeierstrassCurve.Velu.Formula` | 49.0 MiB |
| `FLTForHuman.WeierstrassCurve.Velu.Defs` | 42.5 MiB |
| next `ModularCurve` module (`Gamma0Index`) | 1.6 MiB |

The module built in **61 s** and **73 s** in two 4-thread tree builds. Attribution replaced every
theorem body by `sorry` except one, compiled the copy with
`lake env lean -DmaxHeartbeats=4000000 -o`, and subtracted the all-`sorry` baseline (0.12 MiB,
4.7 s; ≈4 s of every run is the import of `Velu/OrderTwo`):

| declaration | `.olean` | isolated wall |
|---|---:|---:|
| `coeff_zero_identity` | 40.69 MiB | 28.1 s |
| `coeff_one_identity` | 31.66 MiB | 21.9 s |
| `coeff_two_identity` | 12.67 MiB | 8.5 s |
| `main` | 1.64 MiB | 6.9 s |
| `fibrePoly_phiTwo_eq`, `cubic_expand`, `sixteen_ne_zero` | ≤ 0.07 MiB | ≤ 4.4 s |

So the three coefficient identities are the whole module. This is the same signature as the
`OrderTwo`/`OrderTwoMap` hogs (§6), in a different dress: the certificate text is small and the
cost is the *proof term* `ring` builds.

## 2. Why the three identities cost 80 MB

Write `x₀, x₁, x₂` for the three distinct `x`-coordinates (the roots of `Ψ₂Sq`), and
$`c_4, \Delta`$ for the elementary-symmetric expressions, $`g_i = (x_i-x_j)(x_i-x_k)`$ and
$`d_i = 16\,(x_j-x_k)^2`$. Comparing the coefficients of `fibrePoly phiTwo W.j` expanded with
those of $`\prod_i (X - p_i)`$, where $`p_i = (c_4+240g_i)^3/(g_i d_i^2)`$, gives three rational
identities in $`c_4/\Delta`$. They are true, and `field_simp; ring` closes them — by expanding a
3-variable polynomial of total degree 12, 24 and 36. `ring`'s proof term is essentially that
expansion, and the `.olean` serialises it: 91 + 91 monomials for the first identity, 295 + 295
for the second, more for the third. That is the whole cost.

Two facts about the algebra do not change the cost but explain everything below:

* $`\Delta = g_i^2\,d_i`$ for each $`i`$, so $`p_i = (g_i(c_4+240g_i))^3/\Delta^2`$ — one
  denominator instead of three products;
* $`\sum_i x_i^k/g_i = 1`$ for $`k = 2`$ and $`0`$ for $`k = 0, 1`$ — the partial-fraction
  identities for the derivative values of a cubic.

None of that shrinks the *raw* expansion much: `field_simp` followed by `ring` still expands
in $`x_0,x_1,x_2`$.

## 3. The normalization

Every ingredient is built from differences, so the identities are translation-invariant:
$`c_4`$, $`\Delta`$, the $`g_i`$ and the $`d_i`$ are unchanged by $`x_i \mapsto x_i + t`$. A
translate is therefore free to prove the identity for a convenient triple. The natural choice is
the centroid, $`x_i - e_1/3`$, but that divides by 3 and the module assumes only
$`(2:K) \ne 0`$ — characteristic 3 is a real case. Shifting by $`x_0`$ needs no division: state
the identity for the normalized triple $`(0, a, b)`$ with $`a = x_1-x_0`$, $`b = x_2-x_0`$, and
the general case follows by transport.

In the normalized triple the same cleared identities collapse to:

| identity | per-side monomials, raw `x₀,x₁,x₂` | per-side monomials, normalized `(0,a,b)` |
|---|---:|---:|
| `coeff_two_identity` | 91 | 13 |
| `coeff_one_identity` | 295 | 17 |
| `coeff_zero_identity` | (not expanded; larger) | 25 |

The centroid normalization would give 13 / 25 / 37, so shifting by `x₀` is not only
division-free but a little smaller: in `a, b` the ingredients are short, with
$`g_0 = ab`$, $`g_1 = a(a-b)`$, $`g_2 = b(b-a)`$, $`c_4 = 16(a^2+b^2-ab)`$,
$`\Delta = 16(0-a)^2(0-b)^2(a-b)^2`$ and $`d_0 = 16(a-b)^2`$, $`d_1 = 16(0-b)^2`$,
$`d_2 = 16(0-a)^2`$. Probes of the three normalized lemmas, compiled in isolation, are
**1.12 / 1.47 / 1.69 MiB**.

## 4. The landed change

Only the three `private` lemmas and the hypotheses `main` passes them changed; the public
headline `fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j` and its statement are untouched (its
`Theorems/` wrapper is verbatim, and the pin's other six silo declarations are `S_`-local and
already `private` here).

* the three lemmas now take $`{a\ b : K}`$ with normalized hypotheses — e.g.
  `hc4 : c₄ = 16*(a^2 + b^2 - a*b)`, `hΔ : Δ = 16*(0-a)^2*(0-b)^2*(a-b)^2`,
  `hg0 : g₀ = (0-a)*(0-b)`, `hd0 : d₀ = 16*(a-b)^2`, and so on;
* `main` (`VeluTwoSym.main`) transports its general hypotheses to that triple after the
  `set x0`/`x1`/`x2` block: `ha`, `hb`, `hab` from the distinctness hypotheses, then
  `hc4n, hΔn, hg0n, hg1n, hg2n, hd0n, hd1n, hd2n` — each a small `ring` from the original
  hypothesis. The three `rw` arguments now use those.

The normalization is recorded in the module header and in a comment above the identities, with
the characteristic-3 reason.

## 5. Verification and measurements

* **Statement faithfulness.** `spec/old_check_stmts.py`: **9792 statements identical, 0
  mismatched, 0 missing, 83 renamed, 42 own-proof declarations exempted**; the headline is still
  the pin's wrapper statement verbatim.
* **Module.** `lake build FLTForHuman.ModularCurve.ModularPolynomialFibreTwo`: **6.3 s**, 0
  errors, 0 warnings, `.olean` **5,413,568 B (5.16 MiB)** — from 86,436,408 B and a contended
  61–73 s tree wall.
* **Math.** The three normalized identities, the transport identities and the relation
  $`\Delta = g_i^2 d_i`$ were checked from scratch with `sympy` before the Lean edit
  (`cancel`/`expand` on the cleared forms, and the partial-fraction sums
  $`\sum_i x_i^k/g_i \in \{1, 0, 0\}`$ for $`k = 2, 1, 0`$).
* **The cost is the expansion, not the clearing.** After `subst` the identities need no
  hypotheses, so `field_simp` only clears denominators: the cleared `coeff_two`,
  $`c_4^6 - 1488\,c_4^3\Delta + 162000\,\Delta^2 = \sum_i (g_i(c_4+240g_i))^3`$, is closed by
  `ring` alone in 9.3 s / 11.2 MiB against 12.67 MiB for the ported `field_simp; ring`. The
  landing keeps `field_simp; ring` so that each lemma concludes the rational `p_i` form that
  `main` rewrites with.
* **Isolation recipe (reusable).** Copy the module, replace every theorem body with `sorry`
  except one, compile with
  `lake env lean -DmaxHeartbeats=4000000 -o out.olean copy.lean`, and read the declaration's
  proof term as `size(out) - size(all-sorry baseline)`. Applied front-to-back this needs the
  replacements sorted last-declaration-first (each `sorry` changes the later line numbers).

## 6. What to reuse, and what is left

**The move.** When a `.olean` is dominated by `field_simp; ring`, ask what the identity is
invariant under before touching the certificate:

1. find the change of coordinates the identity is invariant under (here translation of the
   roots; for the Vélu work, the shift of a 2-torsion point to the origin);
2. prefer the representative that needs *no division*, so no characteristic case split is
   introduced (here `x₀ = 0`, not the centroid `xᵢ - e₁/3`);
3. prove the normalized identity, and transport the general hypotheses with small `ring`s.

The sizes of the proof terms are the thing to compare: a few dozen monomials is milliseconds,
hundreds is megabytes.

**Still large.** Post-change the tree's top `.olean`s are `OrderTwoMap` (60.3 MiB), `Velu/Formula`
(49.0), `Velu/Defs` (42.5), `OrderTwo` (29.3), `Discriminant` (17.2) and `PatchingConstruction`
(15.4); the first, fourth and fifth still carry ported `.olean`-heavy certificates. The
isolation recipe of §5 is the way to attribute them before starting.
