/-
  Layer 0b — the classical modular polynomials `Φ₂` and `Φ₃`, as integer bivariate
  polynomials.

  `phiTwo` and `phiThree` are the modular polynomials of level 2 and 3, written out
  coefficient by coefficient; `phiTwoC*`/`phiThreeC*` are their coefficient polynomials in
  the first variable, and `intFibre` is the integer fibre `Φ(n, ·)`. They are what the
  `N = 2` fibre row of the Deligne–Serre column's ready shelf names:
  `fibrePoly phiTwo W.j = ∏ i, (X - C (j (W/⟨P i⟩)))`
  (`topics/modularCurve/WORKORDER-B1-phi-rows.md` §1, `WORKORDER-B2`).

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_ClassicalModularPolynomials.lean` (45 lines), ported whole,
  statements and bodies verbatim.
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ClassicalModularPolynomials.lean
-/
import Mathlib.Algebra.Polynomial.Eval.Defs

set_option autoImplicit false

noncomputable section

namespace ModularCurve

def phiTwoC2 : Polynomial ℤ := -Polynomial.X ^ 2 + 1488 * Polynomial.X - 162000

def phiTwoC1 : Polynomial ℤ :=
  1488 * Polynomial.X ^ 2 + 40773375 * Polynomial.X + 8748000000

def phiTwoC0 : Polynomial ℤ :=
  Polynomial.X ^ 3 - 162000 * Polynomial.X ^ 2 + 8748000000 * Polynomial.X
    - 157464000000000

def phiTwo : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 3 + Polynomial.C phiTwoC2 * Polynomial.X ^ 2
    + Polynomial.C phiTwoC1 * Polynomial.X + Polynomial.C phiTwoC0

def phiThreeC3 : Polynomial ℤ :=
  -Polynomial.X ^ 3 + 2232 * Polynomial.X ^ 2 - 1069956 * Polynomial.X + 36864000

def phiThreeC2 : Polynomial ℤ :=
  2232 * Polynomial.X ^ 3 + 2587918086 * Polynomial.X ^ 2 + 8900222976000 * Polynomial.X
    + 452984832000000

def phiThreeC1 : Polynomial ℤ :=
  -1069956 * Polynomial.X ^ 3 + 8900222976000 * Polynomial.X ^ 2
    - 770845966336000000 * Polynomial.X + 1855425871872000000000

def phiThreeC0 : Polynomial ℤ :=
  Polynomial.X ^ 4 + 36864000 * Polynomial.X ^ 3 + 452984832000000 * Polynomial.X ^ 2
    + 1855425871872000000000 * Polynomial.X

def phiThree : Polynomial (Polynomial ℤ) :=
  Polynomial.X ^ 4 + Polynomial.C phiThreeC3 * Polynomial.X ^ 3
    + Polynomial.C phiThreeC2 * Polynomial.X ^ 2
    + Polynomial.C phiThreeC1 * Polynomial.X + Polynomial.C phiThreeC0

def intFibre (Φ : Polynomial (Polynomial ℤ)) (n : ℤ) : Polynomial ℤ :=
  Φ.map (Polynomial.evalRingHom n)

end ModularCurve

end
