window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_MODULES["FLTForHuman.Elliptic.RedInvar"] = {
  "module": "FLTForHuman.Elliptic.RedInvar",
  "cards": {
    "FLTForHuman.Elliptic.redInvarDenom": {
      "seed": true,
      "refs": [{"where":"type","name":"CommRing","module":"Mathlib.Algebra.Ring.Defs","kind":"inductive"},{"where":"type","name":"Int","module":"Init.Data.Int.Basic","kind":"inductive"},{"where":"body","name":"complEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"normEDS","module":"Mathlib.NumberTheory.EllipticDivisibilitySequence","kind":"def"},{"where":"body","name":"HMod.hMod","module":"Init.Prelude","kind":"abbrev"},{"where":"body","name":"Nat","module":"Init.Prelude","kind":"inductive"}],
      "range": {"start":{"line":41,"column":0},"end":{"line":54,"column":36}},
      "name": "FLTForHuman.Elliptic.redInvarDenom",
      "module": "FLTForHuman.Elliptic.RedInvar",
      "kind": "def",
      "elaborated_type": "{R : Type u_1} → [CommRing R] → R → R → R → ℤ → R",
      "doc": "FLT's `redInvarDenom`. ",
      "short": "redInvarDenom",
      "signature_source": "noncomputable def redInvarDenom (b c d : R) (m : ℤ) : R :=",
      "body_source": "if m % 6 = 0 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 (m / 6)\n      * normEDS b c d (m + 1) * normEDS b c d (m - 1) else\n  if m % 6 = 1 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m - 1) / 6)\n      * normEDS b c d (m + 1) * normEDS b c d m else\n  if m % 6 = 5 then (normEDS b c d 5 - d ^ 2) * complEDS b c d 6 ((m + 1) / 6)\n      * normEDS b c d m * normEDS b c d (m - 1) else\n  if m % 6 = 2 then complEDS b c d 3 ((m + 1) / 3) * complEDS b c d 2 (m / 2)\n      * normEDS b c d (m - 1) else\n  if m % 6 = 4 then complEDS b c d 3 ((m - 1) / 3) * complEDS b c d 2 (m / 2)\n      * normEDS b c d (m + 1) else\n  if m % 6 = 3 then complEDS b c d 3 (m / 3) * complEDS b c d 2 ((m - 1) / 2)\n      * normEDS b c d (m + 1) else 0",
      "source_file": "lean/FLTForHuman/Elliptic/RedInvar.lean",
      "has_source": true,
      "has_refs": true,
      "worksheets": [
        "DivisionPolynomials"
      ]
    }
  }
};
