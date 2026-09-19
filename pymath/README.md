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
  weil_pairing.expected.txt  its golden output
  report.py                  presentation: note / data / check / finish
  ffcurve/                   the shared foundation for all demos
    __init__.py
    fields.py                FiniteField: GF(p) and GF(p^k), sympy-backed
    elliptic.py              EllipticCurve + Miller's Weil pairing
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

## Roadmap

Concepts worth a demo, roughly in dependency order. Each entry names the math and the
formalization it should instantiate.

| Demo | Content | FLT anchor |
|---|---|---|
| `weil_pairing` | perfect alternating pairing, Frobenius, `det = cyclotomic` | `AlgebraicCurve.WeilDatum`, `WeilPairingData`, `Pic0.exists_weilPairing` |
| `divisors_and_pic0` | divisors, degree, principal divisors, `Pic0`; for an elliptic curve `Div/principal ≅ E` | `AlgebraicCurve.Divisor`, `Pic`, `Pic0`, `HasPrincipalDivisors` |
| `riemann_roch` | `ell(D) = deg D + 1 - g`, canonical divisor, genus | `RiemannInequality`, `FunctionFieldRiemannRoch` |
| `frobenius_charpoly` | `#E(F_q)`, `a_q`, Hasse bound, Tate module rank `2g`, `T^2 - a_q T + q` | `Pic0.finrank_rationalTateModule_eq_two_mul_genusFF` |
| `modular_qexp` | `E_4`, `E_6`, `Delta`, eta products, Hecke recursion for `a_n` | `ModularForm`, `CuspForm` |
| `hecke_eichler_shimura` | `T_p` on `J_0(N)` matching `a_p` of an eigenform | `ModularCurve.heckeOperatorBar`, Eichler–Shimura |
| `galois_rep` | `rho_{E,l}`, determinant from the Weil pairing, irreducibility, oddness | `FreyPackage.Mazur_Frey`, `GaloisRepIsIrreducible` |
| `frey_curve` | the Frey curve, its discriminant, conductor, semistability | `FreyPackage`, `IsSemistableModel` |
| `level_lowering` | level invariants and what Ribet's theorem removes | `FreyPackage.level_lowering_to_two` |
| `residue_theorem` | `sum of residues = 0` for a differential on a curve | `AlgebraicCurve.ResidueTheorem`, `WeilOfKaehler` |

## Conventions inherited from the repo

- Math in these files is prose and code, not the note delimiters; keep any math syntax in
  comments plain ASCII.
- The FLT sources are cited at `aa2d8b3`; see [../AGENTS.md](../AGENTS.md).
- Files live under the public repo, so do not reference untracked local files.
