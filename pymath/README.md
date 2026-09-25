# pymath — illustrative computations for the FLT proof

Small Python programs that make the *computable content* of the FLT proof visible. The
aim is understanding, not re-proving: each demo takes one concept the proof uses, exhibits
it on a small explicit example, and checks the mathematical laws it is supposed to
satisfy. Efficiency is irrelevant here; clarity and auditability are the point.

The only dependency is **sympy**.

```
pymath/
  README.md
  weil_pairing.py            demo 1 — the Weil pairing
  weil_pairing.expected.txt
  divisors_and_pic0.py       demo 2 — divisors, principal divisors, Pic^0
  divisors_and_pic0.expected.txt
  riemann_roch.py            demo 3 — Riemann-Roch
  riemann_roch.expected.txt
  frobenius_charpoly.py      demo 4 — Frobenius and its characteristic polynomial
  frobenius_charpoly.expected.txt
  modular_qexp.py            demo 5 — Eisenstein series, Delta, j, Hecke recursions
  modular_qexp.expected.txt
  hecke_eichler_shimura.py   demo 6 — Hecke operators and Eichler-Shimura
  hecke_eichler_shimura.expected.txt
  galois_rep.py              demo 7 — Galois representations on E[l]
  galois_rep.expected.txt
  frey_curve.py              demo 8 — the Frey curve and its invariants
  frey_curve.expected.txt
  level_lowering.py          demo 9 — Ribet level lowering and the level-2 contradiction
  level_lowering.expected.txt
  residue_theorem.py         demo 10 — residues and the residue theorem
  residue_theorem.expected.txt
  hexagonal_theta.py         demo 11 — the hexagonal theta series and chi_{-3}
  hexagonal_theta.expected.txt
  report.py                  presentation: note / data / check / finish
  ffcurve/                   the shared foundation for all demos
    __init__.py
    fields.py                FiniteField: GF(p) and GF(p^k), sympy-backed
    elliptic.py              EllipticCurve + Miller's Weil pairing
    divisors.py              divisors, principal divisors, Abel-Jacobi sum
    riemann_roch.py          Weierstrass non-gaps and Riemann-Roch dimensions
    frobenius.py             Frobenius recurrence, Hasse bound, char. polynomial roots
    qexp.py                  integer q-expansions: E_4, E_6, Delta, eta, j
    hecke.py                 Hecke operators on q-expansions, operator matrices
    galois.py                cyclotomic character, Frobenius matrices, irreducibility
    frey.py                  Weierstrass invariants and the Frey specialisations
    level.py                 conductor levels, exact division, descent chains
    residue.py               residues on P^1, logarithmic derivatives, sums
    hexagonal.py             the hexagonal form x^2 + xy + y^2 and Z[zeta_6]
```

## Foundation: what sympy gives us, and what `ffcurve` adds

`ffcurve` is deliberately thin, because most of the wheel already exists.

sympy provides:

- `Poly(f, x, modulus=p)` — arithmetic in `GF(p)[x]`: add, multiply, `rem`, `invert`,
  `**`, plus `is_irreducible` and `factor_list`. This is all the polynomial arithmetic a
  finite field needs.
- exact integer/rational arithmetic, matrices, and number theory helpers.

sympy does **not** provide:

- a field `GF(p^k)` — `sympy.GF(25)` is `Z/25`, a ring, not a field;
- elliptic curves over a finite field — `sympy.ntheory.elliptic_curve.EllipticCurve` is
  over `QQ` only;
- the Weil pairing (or torsion bases).

So `ffcurve` adds exactly two things and nothing else:

- `fields.FiniteField` — a uniform, representation-hiding wrapper over sympy for `GF(p)`
  and `GF(p^k) = GF(p)[t]/(f)`, where `f` is found with sympy's `is_irreducible`.
  Elements are opaque, hashable sympy objects; `F.key(x)` orders them, `F.format(x)`
  prints them (coefficients normalized to `[0, p)`), and `F.modulus_format()` prints the
  defining polynomial.
- `elliptic.EllipticCurve` — the group law, `points()`, `order`, `torsion_basis`,
  `miller`, and `weil_pairing`, using only the field interface.

There is no hand-rolled polynomial arithmetic and no second field backend: sympy is the
trusted implementation.

Three sympy facts the foundation absorbs:

- `sympy.GF(25)` is `Z/25`; extension fields must be built as `Poly` quotients.
- sympy prints coefficients in a symmetric range (`3` shows as `-2` mod 5), so `format`
  and `key` map to `[0, p)`.
- `sympy.polys.galoistools` stores polynomials leading-coefficient-first (descending).
  `ffcurve` uses `Poly` instead, whose `from_list`/`all_coeffs` order is documented; be
  careful not to mix the two conventions.

## Running

```sh
python3 weil_pairing.py                                # prints and checks
python3 weil_pairing.py > weil_pairing.expected.txt    # regenerate the golden output
```

Each demo exits non-zero if any check fails, so it is usable as a test.

## Verification

Every demo ends with a run of `check(label, ok)`, one per mathematical law, and exits
non-zero on any failure. Because the field arithmetic is sympy's, there is no need for a
second field implementation to cross-check against; the checks that carry weight are the
curve and pairing laws, which are the part sympy does not supply. `weil_pairing.py`
currently runs 27 checks, all passing.

## The template

Every `pymath/<concept>.py` follows the same shape.

1. **Module docstring with four headings.**
   - `CONCEPT` — the mathematical object and its defining laws, in one paragraph.
   - `FLT ANCHOR` — the declarations in the formalization this illustrates, as
     `Namespace.name (File.lean)`, with the pin `aa2d8b3`.
   - `WHY IT MATTERS FOR FLT` — where the proof uses it (math, not Lean).
   - `RUN` — the command and the expected-output file.

2. **Self-contained.** Standard library plus sympy plus `ffcurve`; no network, no files
   read by the demo itself.

3. **Fixed, small, explicit parameters.** Pick the example by hand (or by a deterministic
   search) and hard-code it. Any choice that could vary between implementations — a field
   modulus, a basis, a generator — must be pinned by a documented rule, so runs are
   reproducible.

4. **Narrate, then compute, then check.** Use `report.Report`:
   - `R.note("...")` says in prose what the example illustrates and why the next
     computation is the interesting one;
   - `R.data("...")` prints a value or a displayed formula;
   - `R.check(label, ok)` states one mathematical law, named in the label
     (`"e_n(Q,P) = e_n(P,Q)^-1"`, not `"test3"`);
   - `R.finish()` exits non-zero if any check failed.

   A reader should be able to follow the printed output as an explanation, not just a
   computation. The narrative carries the meaning: say what `E[n]` is before pairing it,
   say what nondegeneracy buys before checking it, say why `det(pi) = p mod n` is the
   cyclotomic character before asserting it. The checks are the contract; the prose is
   why they matter.

5. **A closing hook to the proof.** Name the FLT declarations the example instantiates,
   and say in one or two sentences what the proof does with the fact. `weil_pairing.py`
   ends by identifying `WeilDatum.pairing = evalFun f1 D2 / evalFun f2 D1` with Miller's
   formula, and explaining that `det rho_{E,l} = chi_l` (Galois equivariance of the
   pairing) is what makes the mod-`l` representation odd.

6. **A deterministic selection rule.** Demos that need a basis, a generator or a curve
   should choose it by an explicit canonical rule — see `canonical_basis` in
   `weil_pairing.py`, which sorts `E[n]` by `F.key`. This is what makes the golden output
   stable.

7. **New mathematics goes in `ffcurve/`.** Add to `fields.py` or a new module there rather
   than duplicating inside a demo. Keep the rule: if sympy has it, use sympy.

8. **Naming.** One concept per file, `snake_case.py`, golden output `<name>.expected.txt`.

9. **Citations.** Refer to the formalization as `path:line` relative to the pinned
   checkout, reachable at
   `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/<path>#L<line>`.
   Do not cross-reference untracked local files; quote the needed content instead.

## Demo 1: the Weil pairing

`weil_pairing.py` covers, on explicit curves:

- `e_n(P,Q)` for `E[n]` over a prime field (`GF(7)`, `n = 3`; `GF(41)`, `n = 5`):
  `e_n(P,Q)^n = 1`, primitive order `n`, alternating, bilinear (`e_n(aP,bQ) = zeta^(ab)`),
  nondegenerate, and the Gram matrix `[[1, zeta],[zeta^-1, 1]]`;
- Frobenius equivariance over `GF(25) = GF(5)[t]/(t^2+t+1)`:
  `e_n(pi P, pi Q) = e_n(P,Q)^p` with `pi` the `5`-power Frobenius, `det(pi) = p mod n`
  (the cyclotomic character), `trace(pi) = a_5 mod n`, and `pi^2` acting as the identity
  because `E[3]` is rational over `GF(25)`;
- the characteristic polynomial `T^2 - a_p T + p` of Frobenius, whose constant term `p` is
  the determinant;
- the divisorial definition `e_n(P,Q) = (-1)^n f_P(Q)/f_Q(P)` via Miller's algorithm, which
  is literally `WeilDatum.pairing` in the formalization.

## Demo 2: divisors and Pic^0

`divisors_and_pic0.py` works on `E: y^2 = x^3 - x` over `GF(7)` (`#E = 8`,
`E` isomorphic to `Z/2 x Z/4`, full 2-torsion rational) and exhibits
`Pic^0(E) = E`:

- `div(x) = 2[(0,0)] - 2[O]` and `div(y) = [(0,0)] + [(1,0)] + [(6,0)] - 3[O]`,
  both of degree 0 with Abel-Jacobi sum `O`;
- the chord-tangent divisor `[P] + [Q] - [P+Q] - [O] = div(line) - div(vertical)`
  is principal for every pair, so `[P] + [Q] = [P+Q]` in `Pic^0`;
- `phi(P) = [P] - [O]` is an isomorphism: `phi(P) + phi(Q) = phi(P+Q)`,
  `[P] - [Q]` principal iff `P = Q`, and the eight classes are distinct;
- the general criterion `[P]+[Q]-[R]-[T]` principal iff `P+Q = R+T`.

13 checks, all passing.

## Demo 3: Riemann-Roch

`riemann_roch.py` computes `ell(D) = dim L(D)` where it is elementary — for
`D = n*P` at a rational Weierstrass point of a hyperelliptic curve — and checks

    ell(D) - ell(K - D) = deg D + 1 - g,      deg K = 2g - 2,  ell(K) = g

across genera 0 to 4:

- genus 0: `ell(n*inf) = n + 1`, `K = -2*inf`;
- genus 1 (the elliptic curve `y^2 = x^3 - x` over `GF(7)`): `ell(n*O) = n` for
  `n >= 1`, `ell(0) = 1`, `K = 0`, and the single gap at `O` is pole order 1;
- genus 2, 3: a table of both sides of Riemann-Roch on `D = n*inf`, the Riemann
  inequality, and equality exactly when `deg D > 2g - 2`.

The demo also separates two counts that are easy to conflate: the monomials
`x^i y^j` with `2i + (2g+1)j <= n` **span** but are dependent (the Weierstrass
relation makes `y^2 x^i` and `x^(i+2g+1)` share a pole order), while a basis has
one function per non-gap, so `ell` counts distinct orders.

15 checks, all passing.

## Demo 4: Frobenius and its characteristic polynomial

`frobenius_charpoly.py` covers `pi^2 - a_q pi + q = 0` and the polynomial
`T^2 - a_q T + q`:

- point counts and `a_q = q + 1 - #E(F_q)` for several curves, with Hasse's
  bound `a_q^2 <= 4q`;
- the recurrence `a_{q^k} = a_q a_{q^{k-1}} - q a_{q^{k-2}}`, checked against
  brute-force point counts over `F_{q^2}` and `F_{q^3}` for curves over `F_3`,
  `F_5`, `F_7`;
- the complex roots: `alpha + beta = a_q`, `alpha beta = q`, and
  `|alpha|^2 = |beta|^2 = q` — Hasse in modulus form, the "weight 1" condition;
- the Frobenius action on `E[n]`: `E[n]` free of rank 2, and the `2x2` matrix
  over `Z/n` with trace `a_q` and determinant `q`, satisfying its own
  characteristic polynomial.

9 checks, all passing.

## Demo 5: modular q-expansions

`modular_qexp.py` works in `Z[[q]]` truncated to `q^63` with exact integer
arithmetic and checks the classical level-one identities:

- `E_4 = 1 + 240 sum sigma_3(n) q^n` and `E_6 = 1 - 504 sum sigma_5(n) q^n`;
- `Delta` defined two ways — `q prod (1-q^n)^24` and `(E_4^3 - E_6^2)/1728` —
  agree, with `E_4^3 - E_6^2 = 1728 Delta`, and `tau(n)` matching
  `1, -24, 252, -1472, 4830, ...`;
- the Hecke recursions for an eigenform: `tau(mn) = tau(m)tau(n)` for coprime
  `m, n`, and `tau(p^(r+2)) = tau(p) tau(p^(r+1)) - p^11 tau(p^r)`;
- `j = E_4^3/Delta = q^-1 + 744 + 196884 q + ...`, and the formalization's
  `jNum = E_4^3 (Delta/q)^-1` (a unit in `Z[[q]]`).

13 checks, all passing.

## Demo 6: Hecke operators and Eichler-Shimura

`hecke_eichler_shimura.py` computes `T_p` on `Z[[q]]` by
`(T_p f)_n = a_{np} + p^(k-1) a_{n/p}` and checks:

- additivity and `Z`-linearity of the operator;
- `T_p E_4 = (1+p^3)E_4` and `T_p E_6 = (1+p^5)E_6` (Eisenstein eigenforms);
- `T_p Delta = tau(p) Delta`, the eigenvalue being the `q^p` coefficient;
- the eigenform recursion `a_{p^(r+2)} = a_p a_{p^(r+1)} - p^(k-1) a_{p^r}`
  read off `T_p f = a_p f`;
- commutativity `T_p T_q = T_q T_p` on the two-dimensional `S_24`, via explicit
  `2x2` integer matrices — the numerical shadow of `HeckeOperatorsCommuteBar`.

Eichler-Shimura ties the eigenvalue to the Frobenius trace, which
`frobenius_charpoly` computes from the other side.

8 checks, all passing.

## Demo 7: Galois representations on `E[l]`

`galois_rep.py` computes `rho_{E,l}` where the Galois group is generated by
Frobenius and checks the constraints the proof relies on:

- `det rho(Frob) = p mod l = chi_l(Frob)` — the determinant is the cyclotomic
  character, from the Weil pairing; `trace rho(Frob) = a_p`;
- oddness: `Phi_n` is palindromic, so `zeta -> zeta^(-1)` is a nontrivial Galois
  automorphism for `n > 2`, its fixed field is the real subfield of degree
  `phi(n)/2`, and `chi_n(c) = -1`;
- the Frobenius polynomial `T^2 - a_p T + p` over a grid of curves;
- irreducibility: over a finite field the representation is generated by
  Frobenius, so (for `l != p`) it is irreducible exactly when that polynomial
  is irreducible over `F_l`, with the concrete `2x2` matrix and its
  eigenvectors checked against the criterion.

10 checks, all passing.

## Demo 8: the Frey curve

`frey_curve.py` verifies the invariants and semistability of the curve attached
to a putative Fermat counterexample, symbolically in `X = a^p`, `Y = b^p`:

- the naive model `y^2 = x(x-X)(x+Y)` and the integral model, with
  `Delta = X^2Y^2(X+Y)^2/2^8`, `c_4 = X^2+XY+Y^2` and
  `j = 2^8(X^2+XY+Y^2)^3/(XYZ)^2`;
- `c_4 = Z^2 - XY = c^{2p} - (ab)^p`, and `Delta * 2^8 = ((abc)^2)^p`, a `p`-th
  power;
- semistability: for `q | a`, `q | b` or `q | c` the value `c_4` reduces to a
  unit, so every bad prime is multiplicative — matching the formalization's
  `IsSemistableModel` — and the conductor `rad(abc)` is squarefree;
- a package-shaped numeric run (`a = 3`, `b = 2`, `p = 5`) since no
  counterexample exists.

13 checks, all passing.

## Demo 9: level lowering

`level_lowering.py` does the level bookkeeping of Ribet's theorem:

- the conductor level `N = rad(abc)`: squarefree, supported on the primes of
  `abc`, with `q^2 ∤ N` and `4 ∤ N`;
- the lowering step's hypotheses (`q` prime, `q ≠ 2`, `q ≠ p`, `q | N`,
  irreducible, unramified at `q`) and its conclusion (`∃ M | N` with `q ∤ M`),
  including how a squared factor would block it;
- the descent chain `330 -> 110 -> 10 -> 2` for the package-shaped example, each
  step an exact division, each intermediate level again a conductor level;
- the step at `p` (`p | N` iff `p | abc`, the peu-ramifiée condition) and the
  contradiction at level 2 with `S_2(Gamma0(2)) = 0`.

15 checks, all passing.

## Demo 10: residues and the residue theorem

`residue_theorem.py` computes residues exactly and checks `sum_P res_P(omega) = 0`:

- on `P^1`, finite residues by coefficient extraction and the residue at
  infinity via `x = 1/t`, across six examples (including double poles, which
  contribute zero);
- the degree criterion: `res_infinity = -1` exactly when `deg Q = deg P + 1`,
  and `0` when `deg Q >= deg P + 2`;
- logarithmic derivatives `d log F`, whose residues are the orders of `F`, on
  `P^1` and on the elliptic curve `y^2 = x^3 - x` over `GF(7)`, where the
  residues are the divisor coefficients for `x`, `y` and the chord-tangent
  function.

10 checks, all passing.

## Demo 11: the hexagonal theta series

`hexagonal_theta.py` computes the representation numbers of the hexagonal form
`Q(x, y) = x^2 + x y + y^2` and checks that its theta series is the weight-one
`chi_{-3}` Eisenstein series `e1Chi3 = 1 + 6 sum sigma_chi(n) q^n`:

- the ring `Z[zeta_6]` of Eisenstein integers: `Q` is the norm, multiplication
  and conjugation preserve it, the six units are exactly the norm-one elements,
  rotation by `zeta` is `(x, y) -> (-y, x + y)`, and the nearest-lattice-point
  division makes the ring Euclidean;
- the unit orbits partition the representations, each of size 6, so
  `6 | r(n)` and `r(n) / 6` counts representations up to a unit;
- the main identity `r(n) = 6 sigma_chi(n) = 6 (d_1(n) - d_2(n))` up to `q^63`,
  with `chi_{-3}` the nontrivial character mod 3;
- the three local laws: `3` ramifies (`r(3^k) = 6`, `r(3m) = r(m)`), split
  primes `p = 1 mod 3` give `r(p^k) = 6(k+1)`, inert primes `p = 2 mod 3` give
  `6` or `0` for even or odd `k`, and `6 r(m n) = r(m) r(n)` for coprime
  `m, n` (coprimality checked to be necessary);
- the analytic half at `tau = 2i`: the T, Fricke
  `theta(-1/(3 tau)) = -i sqrt(3) tau theta(tau)` and `U_3` functional
  equations, evaluated from the truncated lattice sum.

26 checks, all passing.

## Roadmap

Concepts worth a demo, roughly in dependency order. Each entry names the math and the
formalization it should instantiate.

| Demo | Content | FLT anchor |
|---|---|---|
| `weil_pairing` ✅ | perfect alternating pairing, Frobenius, `det = cyclotomic` | `AlgebraicCurve.WeilDatum`, `WeilPairingData`, `Pic0.exists_weilPairing` |
| `divisors_and_pic0` ✅ | divisors, degree, principal divisors, `Pic0`; for an elliptic curve `Div/principal ≅ E` | `AlgebraicCurve.Divisor`, `Pic`, `Pic0`, `HasPrincipalDivisors` |
| `riemann_roch` ✅ | `ell(D) = deg D + 1 - g`, canonical divisor, genus | `RiemannInequality`, `FunctionFieldRiemannRoch` |
| `frobenius_charpoly` ✅ | `#E(F_q)`, `a_q`, Hasse bound, Tate module rank `2g`, `T^2 - a_q T + q` | `Pic0.finrank_rationalTateModule_eq_two_mul_genusFF` |
| `modular_qexp` ✅ | `E_4`, `E_6`, `Delta`, eta products, Hecke recursion for `a_n` | `ModularForm`, `CuspForm` |
| `hecke_eichler_shimura` ✅ | `T_p` on `J_0(N)` matching `a_p` of an eigenform | `ModularCurve.heckeOperatorBar`, Eichler–Shimura |
| `galois_rep` ✅ | `rho_{E,l}`, determinant from the Weil pairing, irreducibility, oddness | `FreyPackage.Mazur_Frey`, `GaloisRepIsIrreducible` |
| `frey_curve` ✅ | the Frey curve, its discriminant, conductor, semistability | `FreyPackage`, `IsSemistableModel` |
| `level_lowering` ✅ | level invariants and what Ribet's theorem removes | `FreyPackage.level_lowering_to_two` |
| `residue_theorem` ✅ | `sum of residues = 0` for a differential on a curve | `AlgebraicCurve.ResidueTheorem`, `WeilOfKaehler` |
| `hexagonal_theta` ✅ | `r(n) = 6 sigma_chi(n)`, the three splitting laws, and `theta = e1Chi3` | `EisensteinWeightOne.e1Chi3IsModular`, `HexagonalLattice.summable_thetaTerm_and_tsum_neg_inv_three_mul` |

## Conventions inherited from the repo

- Math in these files is prose and code, not the note delimiters; keep any math syntax in
  comments plain ASCII.
- The FLT sources are cited at `aa2d8b3`; see [../AGENTS.md](../AGENTS.md).
- Files live under the public repo, so do not reference untracked local files.
