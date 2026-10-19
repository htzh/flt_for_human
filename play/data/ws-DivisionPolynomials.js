window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["DivisionPolynomials"] = {
  "slug": "DivisionPolynomials",
  "file": "lean/play/DivisionPolynomials.lean",
  "title": "the division polynomials",
  "tagline": "ψ, Ψ, ΨSq, Φ, φ and the EDS under them",
  "subject": "the division polynomials of a Weierstrass curve, and the elliptic divisibility sequence (EDS) layer that generates them",
  "reads": "FLTForHuman/Elliptic/Omega.lean, the top of the EDS cone: it imports Net → RedInvar → Complement → EllSequence → EDS → DivisionPolynomial, and hence mathlib's AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean and NumberTheory/EllipticDivisibilitySequence.lean",
  "pin": "Definitions/Def_WeierstrassCurve_EDSEngine.lean · aa2d8b3 <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_EDSEngine.lean>",
  "check": "cd lean && lake env lean play/DivisionPolynomials.lean  (~3.3 s warm)",
  "status": "open",
  "date": "2026-10-15",
  "imports": ["FLTForHuman.Elliptic.Omega"],
  "opens": ["Polynomial","Polynomial.Bivariate","WeierstrassCurve","FLTForHuman.Elliptic"],
  "namespace": "Play",
  "zones": [{"id":"A","title":"the cast: eleven names over four sequences"},{"id":"B","title":"the object: normalised elliptic divisibility sequences"},{"id":"C","title":"the one relation: from the recurrences to the net property"},{"id":"D","title":"the univariate shadow: `R[X]` versus `R[X][Y]`"},{"id":"E","title":"what the layer is for: complement, invariant, `ωe`"},{"id":"F","title":"things to poke at"},{"id":"Q","title":"question log"}],
  "blocks": [
    {
      "type": "code",
      "line": 51,
      "text": "import FLTForHuman.Elliptic.Omega",
      "zone": null
    },
    {
      "type": "code",
      "line": 53,
      "text": "set_option autoImplicit false",
      "zone": null
    },
    {
      "type": "code",
      "line": 55,
      "text": "noncomputable section",
      "zone": null
    },
    {
      "type": "code",
      "line": 57,
      "text": "open scoped Polynomial Polynomial.Bivariate",
      "zone": null
    },
    {
      "type": "code",
      "line": 58,
      "text": "open Polynomial",
      "zone": null
    },
    {
      "type": "code",
      "line": 59,
      "text": "open WeierstrassCurve",
      "zone": null
    },
    {
      "type": "code",
      "line": 60,
      "text": "open FLTForHuman.Elliptic",
      "zone": null
    },
    {
      "type": "code",
      "line": 62,
      "text": "namespace Play",
      "zone": null
    },
    {
      "type": "prose",
      "md": "The first obstacle is not mathematics but naming. mathlib keeps two worlds\nstrictly apart, and the names `ψ`/`Ψ`, `φ`/`Φ`, `ΨSq` have one foot in each:\n\n  bivariate, `R[X][Y]` — honest polynomials in the coordinates `x`, `y`\n    `ψ n`     the `n`-division polynomial   (`ψ 0 = 0`, `ψ 1 = 1`, `ψ 2 = ψ₂`)\n    `Ψ n`     the same sequence, normalised so the even terms carry a `ψ₂`\n    `φ n`     the `x`-numerator, `X * (ψ n) ^ 2 - ψ (n+1) * ψ (n-1)`\n    `ψ₂`      the `2`-division polynomial `2Y + a₁X + a₃`\n\n  univariate, `R[X]` — their shadows on the curve `R[W] = R[X,Y]/(W)`\n    `preΨ n`  the auxiliary sequence, `= preNormEDS (Ψ₂Sq ^ 2) Ψ₃ preΨ₄ n`\n    `ΨSq n`   congruent to `(ψ n) ^ 2`, `= (preΨ n) ^ 2 * (if Even n then Ψ₂Sq else 1)`\n    `Φ n`     congruent to `φ n`,     `= X * ΨSq n - preΨ (n+1) * preΨ (n-1) * (if Even n then 1 else Ψ₂Sq)`\n    `Ψ₂Sq`    congruent to `ψ₂ ^ 2`,  `= 4X³ + b₂X² + 2b₄X + b₆`\n    `Ψ₃`      `= ψ 3` itself,         `= 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`\n    `preΨ₄`   `= ψ 4 / ψ₂` on curve,  `= 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + …`\n\nThe last four are *not* new polynomials. `Ψ₂Sq`, `Ψ₃`, `preΨ₄` are the three\ninitial values the recurrence is anchored at, and the `if Even` factors are the\nbookkeeping that keeps the univariate side closed under that recurrence — the\nsubject of Zones B and D.\n\nIn Lean the definitions are literally these. Every name in the table: ",
      "zone": "A",
      "line": 64
    },
    {
      "type": "check",
      "line": 90,
      "raw": "#check @WeierstrassCurve.ψ₂",
      "zone": "A",
      "name": "WeierstrassCurve.ψ₂",
      "display": "@WeierstrassCurve.ψ₂",
      "card": "WeierstrassCurve.ψ₂"
    },
    {
      "type": "check",
      "line": 91,
      "raw": "#check @WeierstrassCurve.Ψ₂Sq",
      "zone": "A",
      "name": "WeierstrassCurve.Ψ₂Sq",
      "display": "@WeierstrassCurve.Ψ₂Sq",
      "card": "WeierstrassCurve.Ψ₂Sq"
    },
    {
      "type": "check",
      "line": 92,
      "raw": "#check @WeierstrassCurve.Ψ₃",
      "zone": "A",
      "name": "WeierstrassCurve.Ψ₃",
      "display": "@WeierstrassCurve.Ψ₃",
      "card": "WeierstrassCurve.Ψ₃"
    },
    {
      "type": "check",
      "line": 93,
      "raw": "#check @WeierstrassCurve.preΨ₄",
      "zone": "A",
      "name": "WeierstrassCurve.preΨ₄",
      "display": "@WeierstrassCurve.preΨ₄",
      "card": "WeierstrassCurve.preΨ₄"
    },
    {
      "type": "check",
      "line": 94,
      "raw": "#check @WeierstrassCurve.preΨ'",
      "zone": "A",
      "name": "WeierstrassCurve.preΨ'",
      "display": "@WeierstrassCurve.preΨ'",
      "card": "WeierstrassCurve.preΨ'"
    },
    {
      "type": "check",
      "line": 95,
      "raw": "#check @WeierstrassCurve.preΨ",
      "zone": "A",
      "name": "WeierstrassCurve.preΨ",
      "display": "@WeierstrassCurve.preΨ",
      "card": "WeierstrassCurve.preΨ"
    },
    {
      "type": "check",
      "line": 96,
      "raw": "#check @WeierstrassCurve.Ψ",
      "zone": "A",
      "name": "WeierstrassCurve.Ψ",
      "display": "@WeierstrassCurve.Ψ",
      "card": "WeierstrassCurve.Ψ"
    },
    {
      "type": "check",
      "line": 97,
      "raw": "#check @WeierstrassCurve.ψ",
      "zone": "A",
      "name": "WeierstrassCurve.ψ",
      "display": "@WeierstrassCurve.ψ",
      "card": "WeierstrassCurve.ψ"
    },
    {
      "type": "check",
      "line": 98,
      "raw": "#check @WeierstrassCurve.ΨSq",
      "zone": "A",
      "name": "WeierstrassCurve.ΨSq",
      "display": "@WeierstrassCurve.ΨSq",
      "card": "WeierstrassCurve.ΨSq"
    },
    {
      "type": "check",
      "line": 99,
      "raw": "#check @WeierstrassCurve.Φ",
      "zone": "A",
      "name": "WeierstrassCurve.Φ",
      "display": "@WeierstrassCurve.Φ",
      "card": "WeierstrassCurve.Φ"
    },
    {
      "type": "check",
      "line": 100,
      "raw": "#check @WeierstrassCurve.φ",
      "zone": "A",
      "name": "WeierstrassCurve.φ",
      "display": "@WeierstrassCurve.φ",
      "card": "WeierstrassCurve.φ"
    },
    {
      "type": "prose",
      "md": " The bodies. Note that `ψ` is *definitionally* a `normEDS` and `preΨ`\ndefinitionally a `preNormEDS`; Zone B reads those two definitions, and the\n`if Even n` branches in `Φ` and `ΨSq` are the same bookkeeping seen from the\nunivariate side. ",
      "zone": "A",
      "line": 102
    },
    {
      "type": "print",
      "line": 107,
      "raw": "#print WeierstrassCurve.ψ",
      "zone": "A",
      "name": "WeierstrassCurve.ψ",
      "display": "WeierstrassCurve.ψ",
      "card": "WeierstrassCurve.ψ"
    },
    {
      "type": "print",
      "line": 108,
      "raw": "#print WeierstrassCurve.preΨ",
      "zone": "A",
      "name": "WeierstrassCurve.preΨ",
      "display": "WeierstrassCurve.preΨ",
      "card": "WeierstrassCurve.preΨ"
    },
    {
      "type": "print",
      "line": 109,
      "raw": "#print WeierstrassCurve.Φ",
      "zone": "A",
      "name": "WeierstrassCurve.Φ",
      "display": "WeierstrassCurve.Φ",
      "card": "WeierstrassCurve.Φ"
    },
    {
      "type": "print",
      "line": 110,
      "raw": "#print WeierstrassCurve.ΨSq",
      "zone": "A",
      "name": "WeierstrassCurve.ΨSq",
      "display": "WeierstrassCurve.ΨSq",
      "card": "WeierstrassCurve.ΨSq"
    },
    {
      "type": "prose",
      "md": " The two definitional equations, as `rfl` — the compiler confirms that these\nare not theorems but the definitions themselves: ",
      "zone": "A",
      "line": 112
    },
    {
      "type": "example",
      "line": 115,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 118,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    W.preΨ = preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ := rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " ### The initial values, live\n\nThe `simp` lemmas (`ψ_zero`, `ψ_one`, `ψ_two`, `ΨSq_three`, `Φ_three`, …) are\njust these definitions unfolded. ",
      "zone": "A",
      "line": 121
    },
    {
      "type": "example",
      "line": 126,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ψ 2 = W.ψ₂ := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 127,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ψ 3 = C W.Ψ₃ := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 128,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.preΨ 3 = W.Ψ₃ := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 129,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ΨSq 2 = W.Ψ₂Sq := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 130,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ΨSq 3 = W.Ψ₃ ^ 2 := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 131,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.Φ 1 = X := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 135,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by simp",
      "zone": "A",
      "doc": "`Φ 3` is the definition with the `if Even` branch taken: `3` is odd, so the\n`Ψ₂Sq` factor is present."
    },
    {
      "type": "example",
      "line": 141,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.Φ 0 = 1 := by simp",
      "zone": "A",
      "doc": "`Φ 0 = 1` while `ΨSq 0 = 0`: the `n = 0` pair is the point at infinity (the\n`n`-torsion of the zero endomorphism is everything), and it is handled by the\n`simp` branch of the induction rather than by the recursion."
    },
    {
      "type": "prose",
      "md": " ### Reading `ψ n ^ 2`: application binds tighter than `^`\n\nWorth pinning down once, because the tables above mix applications with powers —\n`X * (ψ n) ^ 2` and the like. In Lean, function application has the highest\nprecedence, so `ψ n ^ 2` is `(ψ n) ^ 2` — the square of the `n`-th polynomial,\nwhich is the mathematical reading of `ψₙ²`. To get `ψ` at the index `n ^ 2` you\nmust parenthesise: `ψ (n ^ 2)`. They are the same term only in the first case: ",
      "zone": "A",
      "line": 143
    },
    {
      "type": "example",
      "line": 151,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :\n    (W.ψ n ^ 2 : R[X][Y]) = (W.ψ n) ^ 2 := rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " The distinction is not vacuous: over `ℤ`, `normEDS b c d 2 ^ 2` is `b ^ 2`,\nwhile `normEDS b c d (2 ^ 2)` is `normEDS b c d 4 = d * b`. ",
      "zone": "A",
      "line": 154
    },
    {
      "type": "example",
      "line": 157,
      "text": "example (b c d : ℤ) : normEDS b c d 2 ^ 2 = b ^ 2 := by simp",
      "zone": "A"
    },
    {
      "type": "example",
      "line": 158,
      "text": "example (b c d : ℤ) : normEDS b c d (2 ^ 2) = d * b := by norm_num [normEDS_four]",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " `#check` is the quickest way to see which reading elaboration picked: it\nprints the two terms back with different parenthesisation — `W.ψ n ^ 2` against\n`W.ψ (n ^ 2)`. Note that the printer *drops* the redundant parentheses, so a\ndisplay copied out of a goal state inherits the ambiguity; this worksheet\ntherefore spells the exponent out, `(ψ n) ^ 2`, in prose and displays. ",
      "zone": "A",
      "line": 160
    },
    {
      "type": "check",
      "line": 166,
      "raw": "#check fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ n ^ 2 : R[X][Y])",
      "zone": "A",
      "expr": "fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ n ^ 2 : R[X][Y])"
    },
    {
      "type": "check",
      "line": 167,
      "raw": "#check fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ (n ^ 2) : R[X][Y])",
      "zone": "A",
      "expr": "fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ (n ^ 2) : R[X][Y])"
    },
    {
      "type": "prose",
      "md": " This is also why the univariate square has its own *name*, `ΨSq n`, instead\nof being written `(ψ n) ^ 2` in the univariate world. `ΨSq n` is a polynomial of\n`R[X]`, not the square of the bivariate `Ψ n`; what is true is that its image in\nthe coordinate ring *is* the square, `mk (C (ΨSq n)) = (mk (Ψ n)) ^ 2`\n(`mk_Ψ_sq`, Zone D). A distinct name costs nothing and removes the ambiguity\nfrom every statement that mentions it. ",
      "zone": "A",
      "line": 169
    },
    {
      "type": "prose",
      "md": "Every name in Zone A is generated by one sequence, mathlib's `normEDS b c d`.\nThis zone is the introduction to what that object is; `preNormEDS` is the\nauxiliary sequence mathlib actually recurses on.\n\n### B1 — what a normalised EDS is\n\nFix a commutative ring `R`. A sequence `W : ℤ → R` is an **elliptic sequence**\n(Ward) if, for all `m, n, r : ℤ`,\n\n    W (m + n) * W (m - n) * (W r) ^ 2\n      = W (m + r) * W (m - r) * (W n) ^ 2 - W (n + r) * W (n - r) * (W m) ^ 2.\n\nThat is the port's `Rel₃`; `isEllipticSequence_iff_rel₃` says the predicate\n`IsEllipticSequence` — defined by the four-index relator `rel` (Zone C) — is\nexactly this condition. Call `W` **normalised** if, for three parameters\n`b, c, d ∈ R`,\n\n    W 0 = 0,    W 1 = 1,    W 2 = b,    W 3 = c,    W 4 = d * b.\n\n`normEDS b c d` is the canonical normalised elliptic sequence with those\nparameters. Three remarks on the definition:\n\n* it is indexed by `ℤ`, and negation is free: `W (-n) = -W n` (`normEDS_neg`).\n  A textbook division polynomial is usually written only for `n ≥ 1`; the sign\n  is part of the normalisation here.\n* `W 1 = 1` is what the word \"normalised\" buys: it lets the relation be divided\n  through by `(W 1) ^ 2`, giving the familiar `W (m+n) * W (m-n) = …`.\n* the relation is **quartic**: every term is a product of four factors of `W`,\n  and it is homogeneous of that degree. Remember the `4`; it is exactly what\n  fixes the exponent in the gauge relation of B3.\n\nThe sequence is *rigid*: the relation, the first four values, and\n`W 1, W 2 ∈ R⁰` (non-zero-divisors) determine it completely\n(`isEllipticSequence_ext`, Zone C). So `normEDS` is not one example among many;\nit is *the* normalised EDS. Examples in the wild, from mathlib's own list: the\nidentity sequence (`normEDS 2 3 2 = id`, Zone C), suitable terms of Lucas\nsequences, and the division polynomials — the last being this whole worksheet.\nHere is a concrete one over `ℤ`, `normEDS 1 2 3`, whose start is\n`0, 1, 1, 2, 3, -5, -28, -67, …`: ",
      "zone": "B",
      "line": 176
    },
    {
      "type": "check",
      "line": 218,
      "raw": "#check @FLTForHuman.Elliptic.Rel₃",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.Rel₃",
      "display": "@FLTForHuman.Elliptic.Rel₃",
      "card": "FLTForHuman.Elliptic.Rel₃"
    },
    {
      "type": "check",
      "line": 219,
      "raw": "#check @FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
      "zone": "B",
      "name": "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
      "display": "@FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
      "card": "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃"
    },
    {
      "type": "check",
      "line": 220,
      "raw": "#check @normEDS_zero",
      "zone": "B",
      "name": "normEDS_zero",
      "display": "@normEDS_zero",
      "card": "normEDS_zero"
    },
    {
      "type": "check",
      "line": 221,
      "raw": "#check @normEDS_one",
      "zone": "B",
      "name": "normEDS_one",
      "display": "@normEDS_one",
      "card": "normEDS_one"
    },
    {
      "type": "check",
      "line": 222,
      "raw": "#check @normEDS_two",
      "zone": "B",
      "name": "normEDS_two",
      "display": "@normEDS_two",
      "card": "normEDS_two"
    },
    {
      "type": "check",
      "line": 223,
      "raw": "#check @normEDS_three",
      "zone": "B",
      "name": "normEDS_three",
      "display": "@normEDS_three",
      "card": "normEDS_three"
    },
    {
      "type": "check",
      "line": 224,
      "raw": "#check @normEDS_four",
      "zone": "B",
      "name": "normEDS_four",
      "display": "@normEDS_four",
      "card": "normEDS_four"
    },
    {
      "type": "check",
      "line": 225,
      "raw": "#check @normEDS_neg",
      "zone": "B",
      "name": "normEDS_neg",
      "display": "@normEDS_neg",
      "card": "normEDS_neg"
    },
    {
      "type": "example",
      "line": 227,
      "text": "example {R : Type*} [CommRing R] (W : ℤ → R) :\n    IsEllipticSequence W ↔ ∀ m n r : ℤ, Rel₃ W m n r := isEllipticSequence_iff_rel₃ W",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " (The values below are computed through `normEDS_odd`/`normEDS_even`, not by\n`decide`: `preNormEDS'` is `@[irreducible]`, so the kernel will not unfold the\n`ℕ`-indexed recursion for evaluation. The recurrences are the interface.) ",
      "zone": "B",
      "line": 230
    },
    {
      "type": "example",
      "line": 234,
      "text": "example : normEDS (1 : ℤ) 2 3 1 = 1 := by simp",
      "zone": "B"
    },
    {
      "type": "example",
      "line": 236,
      "text": "example : normEDS (1 : ℤ) 2 3 5 = -5 := by\n  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]\n  norm_num",
      "zone": "B"
    },
    {
      "type": "example",
      "line": 240,
      "text": "example : normEDS (1 : ℤ) 2 3 6 = -28 := by\n  have h5 : normEDS (1 : ℤ) 2 3 5 = -5 := by\n    rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]\n    norm_num\n  have h6 : normEDS (1 : ℤ) 2 3 6 * 1 = -28 := by\n    rw [show (6 : ℤ) = 2 * 3 by norm_num, normEDS_even]\n    norm_num\n    rw [h5]\n    norm_num\n  simpa using h6",
      "zone": "B"
    },
    {
      "type": "example",
      "line": 251,
      "text": "example : normEDS (1 : ℤ) 2 3 7 = -67 := by\n  have h5 : normEDS (1 : ℤ) 2 3 5 = -5 := by\n    rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]\n    norm_num\n  rw [show (7 : ℤ) = 2 * 3 + 1 by norm_num, normEDS_odd]\n  norm_num\n  rw [h5]\n  norm_num",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B2 — the two recurrences\n\n`normEDS` is not defined by the relation above — that would be circular. It is\ndefined by two *recurrences*, which are two of its slices (Zone C, Step 1). In\nthe form mathlib proves them for `normEDS`:\n\n    normEDS (2 * m + 1)\n      = normEDS (m + 2) * (normEDS m) ^ 3 - normEDS (m - 1) * (normEDS (m + 1)) ^ 3,\n    normEDS (2 * m) * b\n      = (normEDS (m - 1)) ^ 2 * normEDS m * normEDS (m + 2)\n          - normEDS (m - 2) * normEDS m * (normEDS (m + 1)) ^ 2.\n\nThese are Ward's recurrences; with the five initial values they compute every\nterm. The first is division-free. The second is **not**: it determines\n`normEDS (2 * m)` only after dividing by `b`, and over a general commutative\nring — or over the polynomial ring `R[X]` — that division does not exist. That\nis the single formal problem the next subsection solves. ",
      "zone": "B",
      "line": 260
    },
    {
      "type": "check",
      "line": 278,
      "raw": "#check @normEDS_odd",
      "zone": "B",
      "name": "normEDS_odd",
      "display": "@normEDS_odd",
      "card": "normEDS_odd"
    },
    {
      "type": "check",
      "line": 279,
      "raw": "#check @normEDS_even",
      "zone": "B",
      "name": "normEDS_even",
      "display": "@normEDS_even",
      "card": "normEDS_even"
    },
    {
      "type": "prose",
      "md": " ### B3 — `preNormEDS`: the same recursion in the other gauge\n\n`preNormEDS b c d` trades the problem away: it anchors at `2 ↦ 1` and `4 ↦ d`\n(instead of `2 ↦ b` and `4 ↦ d * b`), which makes the *even* recursion\ndivision-free and pushes the parameter into the *odd* one, through two\n`if Even m` factors:\n\n    preNormEDS (2 * m)\n      = (preNormEDS (m - 1)) ^ 2 * preNormEDS m * preNormEDS (m + 2)\n          - preNormEDS (m - 2) * preNormEDS m * (preNormEDS (m + 1)) ^ 2,   -- clean\n    preNormEDS (2 * m + 1)\n      = preNormEDS (m + 2) * (preNormEDS m) ^ 3 * (if Even m then b else 1)\n          - preNormEDS (m - 1) * (preNormEDS (m + 1)) ^ 3 * (if Even m then 1 else b).\n\nSo the two sequences trade which recurrence carries the `b`:\n\n    normEDS:    odd clean,     even times `b`\n    preNormEDS: even clean,    odd with `if Even m` factors\n\nand they differ by exactly one factor of `b` on the even indices:\n\n    normEDS b c d n = preNormEDS (b ^ 4) c d n * (if Even n then b else 1).\n\nThat identity is the *definition* of `normEDS` in mathlib. `normEDS` is not\ndefined by the recurrences at all — `preNormEDS` is. Concretely `preNormEDS'` is\nthe `ℕ`-indexed recursion: five base cases `0, 1, 2, 3, 4`, then a step matching\n`n + 5` that halves the index and uses one of the two recurrences above; and\n`preNormEDS` extends it to `ℤ` by `preNormEDS (-n) = -preNormEDS n`. For the\ndivision polynomials the parameters are `(b, c, d) = (ψ₂, C Ψ₃, C preΨ₄)`: that\nis Zone A's `ψ = normEDS ψ₂ (C Ψ₃) (C preΨ₄)`, and `preΨ` is the `mk`-shadow of\nthe same gauge with `ψ₂ ^ 4` replaced by `Ψ₂Sq ^ 2` (Zone D). ",
      "zone": "B",
      "line": 281
    },
    {
      "type": "check",
      "line": 313,
      "raw": "#check @preNormEDS'",
      "zone": "B",
      "name": "preNormEDS'",
      "display": "@preNormEDS'",
      "card": "preNormEDS'"
    },
    {
      "type": "check",
      "line": 314,
      "raw": "#check @preNormEDS",
      "zone": "B",
      "name": "preNormEDS",
      "display": "@preNormEDS",
      "card": "preNormEDS"
    },
    {
      "type": "check",
      "line": 315,
      "raw": "#check @preNormEDS_even",
      "zone": "B",
      "name": "preNormEDS_even",
      "display": "@preNormEDS_even",
      "card": "preNormEDS_even"
    },
    {
      "type": "check",
      "line": 316,
      "raw": "#check @preNormEDS_odd",
      "zone": "B",
      "name": "preNormEDS_odd",
      "display": "@preNormEDS_odd",
      "card": "preNormEDS_odd"
    },
    {
      "type": "print",
      "line": 318,
      "raw": "#print preNormEDS",
      "zone": "B",
      "name": "preNormEDS",
      "display": "preNormEDS",
      "card": "preNormEDS"
    },
    {
      "type": "print",
      "line": 319,
      "raw": "#print normEDS",
      "zone": "B",
      "name": "normEDS",
      "display": "normEDS",
      "card": "normEDS"
    },
    {
      "type": "example",
      "line": 323,
      "text": "example (b c d : ℤ) (m : ℤ) :\n    normEDS b c d (2 * m + 1) = preNormEDS (b ^ 4) c d (2 * m + 1) := by\n  rw [normEDS, ite_eq_right m.not_even_two_mul_add_one, mul_one]",
      "zone": "B",
      "doc": "The gauge relation, split by parity: odd indices agree with\n`preNormEDS (b ^ 4)`, even indices differ by exactly one factor of `b`."
    },
    {
      "type": "example",
      "line": 327,
      "text": "example (b c d : ℤ) (m : ℤ) :\n    normEDS b c d (2 * m) = b * preNormEDS (b ^ 4) c d (2 * m) := by\n  rw [normEDS, ite_eq_left (even_two_mul m), mul_comm]",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B4 — why `b ^ 4`, and what the bookkeeping is for\n\nThe exponent `4` is forced, and the quartic homogeneity of B1 says why.\nSubstitute the gauge `W n = b ^ [n even] * P n` into the odd recurrence\n`W (2m+1) = W (m+2) * (W m) ^ 3 - W (m-1) * (W (m+1)) ^ 3`: every index on the\nright has the parity of `m`, and each term has four factors, so the right side\npicks up `b ^ 4` when `m` is even and `1` when `m` is odd. That is precisely the\n`if Even m then b else 1` of `preNormEDS_odd`, with the parameter of `preNormEDS`\nset to `b ^ 4`. (The even recurrence is consistent with the same value: there\nboth sides pick up `b ^ 2`, and that `b ^ 2` cancels only when `b` is a\nnon-zero-divisor — the universal-ring step of Zone C, Step 4.)\n\nThe concrete consequence, computed. Same odd recursion, but `preNormEDS b c d`\ncarries one factor of `b` where `normEDS b c d` carries four. That is mathlib's\nown \"Implementation notes\" paragraph in `EllipticDivisibilitySequence.lean`: the\nrecurrence is still Ward's, only the normalisation moved. ",
      "zone": "B",
      "line": 331
    },
    {
      "type": "example",
      "line": 348,
      "text": "example (b c d : ℤ) : preNormEDS b c d 5 = d * b - c ^ 3 := by\n  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, preNormEDS_odd]\n  norm_num",
      "zone": "B"
    },
    {
      "type": "example",
      "line": 352,
      "text": "example (b c d : ℤ) : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by\n  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]\n  norm_num\n  ring",
      "zone": "B"
    },
    {
      "type": "example",
      "line": 360,
      "text": "example (b c d : ℤ) : normEDS b c d 6 = b * preNormEDS (b ^ 4) c d 6 := by\n  rw [normEDS, ite_eq_left (by decide : Even (6 : ℤ)), mul_comm]",
      "zone": "B",
      "doc": "The even step is where the division would be. Over `ℤ` the honest statement\nis the `* b` form, and the definition says where the `b` went: into the first\nargument of `preNormEDS`."
    },
    {
      "type": "example",
      "line": 365,
      "text": "example (b c d n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by simp",
      "zone": "B",
      "doc": "Oddness `W (-n) = -W n` is part of the normalisation, so the sequence is\n`ℤ`-indexed and there is no negative-index case split anywhere."
    },
    {
      "type": "prose",
      "md": " ### B5 — one relation, not two recurrences\n\n`IsEllipticSequence W` is the assertion that the *four-index* relator vanishes\non the `s = 0` slice (the `Rel₃` form of B1), and `IsEllipticNet W` — what\nmathlib calls an elliptic net — is the full relator. That relator is a single\nhomogeneous quartic identity, and Ward's two recurrences are two of its\nspecialisations; the recurrences are a *description* of a structure, not the\nstructure itself. `atom` is the half-sum/half-difference product\n`W ((a+b)/2) * W ((a-b)/2)`; `rel_eq` says the `atomRel` and `rel` forms are the\nsame statement under `(a,b,c,d) = (2p+s, 2q+s, 2r+s, s)`. The truncated halves\nare why the parity bookkeeping of the recurrences disappears from the net\nformulation: the atom is only meaningful when `a` and `b` have the same parity,\nand the substitution guarantees it. ",
      "zone": "B",
      "line": 367
    },
    {
      "type": "check",
      "line": 381,
      "raw": "#check @IsEllipticNet",
      "zone": "B",
      "name": "IsEllipticNet",
      "display": "@IsEllipticNet",
      "card": "IsEllipticNet"
    },
    {
      "type": "check",
      "line": 382,
      "raw": "#check @IsEllipticSequence",
      "zone": "B",
      "name": "IsEllipticSequence",
      "display": "@IsEllipticSequence",
      "card": "IsEllipticSequence"
    },
    {
      "type": "check",
      "line": 383,
      "raw": "#check @IsEllipticDvdSequence",
      "zone": "B",
      "name": "IsEllipticDvdSequence",
      "display": "@IsEllipticDvdSequence",
      "card": "IsEllipticDvdSequence"
    },
    {
      "type": "check",
      "line": 384,
      "raw": "#check @IsEllipticNet.atom",
      "zone": "B",
      "name": "IsEllipticNet.atom",
      "display": "@IsEllipticNet.atom",
      "card": "IsEllipticNet.atom"
    },
    {
      "type": "check",
      "line": 385,
      "raw": "#check @IsEllipticNet.atomRel",
      "zone": "B",
      "name": "IsEllipticNet.atomRel",
      "display": "@IsEllipticNet.atomRel",
      "card": "IsEllipticNet.atomRel"
    },
    {
      "type": "check",
      "line": 386,
      "raw": "#check @IsEllipticNet.rel",
      "zone": "B",
      "name": "IsEllipticNet.rel",
      "display": "@IsEllipticNet.rel",
      "card": "IsEllipticNet.rel"
    },
    {
      "type": "check",
      "line": 387,
      "raw": "#check @IsEllipticNet.rel_eq",
      "zone": "B",
      "name": "IsEllipticNet.rel_eq",
      "display": "@IsEllipticNet.rel_eq",
      "card": "IsEllipticNet.rel_eq"
    },
    {
      "type": "check",
      "line": 388,
      "raw": "#check @IsEllipticNet.atomRel_eq",
      "zone": "B",
      "name": "IsEllipticNet.atomRel_eq",
      "display": "@IsEllipticNet.atomRel_eq",
      "card": "IsEllipticNet.atomRel_eq"
    },
    {
      "type": "example",
      "line": 392,
      "text": "example (b c d m n : ℤ) :\n    normEDS b c d (m + n) * normEDS b c d (m - n) =\n      normEDS b c d (m + 1) * normEDS b c d (m - 1) * (normEDS b c d n) ^ 2 -\n        normEDS b c d (n + 1) * normEDS b c d (n - 1) * (normEDS b c d m) ^ 2 := by\n  have h := rel₃_of_isEllipticSequence (normEDS_isEllipticSequence b c d) m n 1\n  simpa [Rel₃, normEDS_one] using h",
      "zone": "B",
      "doc": "Ward's relation for any normalised EDS: `Rel₃` at `r = 1`, one slice of the\nnet relation that Zone E turns into an invariant."
    },
    {
      "type": "example",
      "line": 402,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : IsEllipticSequence W.ψ :=\n  normEDS_isEllipticSequence W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)",
      "zone": "B",
      "doc": "**The division polynomials are an elliptic sequence.** This is the fact the\nwhole layer exists to deliver, and mathlib still lists it as a `TODO` in its\nmodule doc. The proof term is Zone C."
    },
    {
      "type": "example",
      "line": 406,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (p q r s : ℤ) :\n    net W.ψ p q r s = 0 :=\n  net_normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) p q r s",
      "zone": "B",
      "doc": "Not only the `s = 0` slice: `ψ` is a full elliptic net."
    },
    {
      "type": "prose",
      "md": "mathlib *defines* `normEDS` by the two recursions (in the `preNormEDS` shadow)\nand leaves the elliptic-sequence property as a `TODO`. The port proves it. The\nproof is four moves, all of them reusable, plus the upgrade to the full net.\n\n**Step 1 — the recurrences are relator slices.** `Rel₃` is the `s = 0` relator\nspelled out, `OddRec`/`EvenRec` are Ward's two recurrences, and the first three\nport lemmas are pure `ring`: the recurrences *are* the relator at two specific\nquadruples. ",
      "zone": "C",
      "line": 410
    },
    {
      "type": "check",
      "line": 421,
      "raw": "#check @FLTForHuman.Elliptic.Rel₃",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.Rel₃",
      "display": "@FLTForHuman.Elliptic.Rel₃",
      "card": "FLTForHuman.Elliptic.Rel₃"
    },
    {
      "type": "check",
      "line": 422,
      "raw": "#check @FLTForHuman.Elliptic.OddRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.OddRec",
      "display": "@FLTForHuman.Elliptic.OddRec",
      "card": "FLTForHuman.Elliptic.OddRec"
    },
    {
      "type": "check",
      "line": 423,
      "raw": "#check @FLTForHuman.Elliptic.EvenRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.EvenRec",
      "display": "@FLTForHuman.Elliptic.EvenRec",
      "card": "FLTForHuman.Elliptic.EvenRec"
    },
    {
      "type": "check",
      "line": 424,
      "raw": "#check @FLTForHuman.Elliptic.rel₃_iff_oddRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.rel₃_iff_oddRec",
      "display": "@FLTForHuman.Elliptic.rel₃_iff_oddRec",
      "card": "FLTForHuman.Elliptic.rel₃_iff_oddRec"
    },
    {
      "type": "check",
      "line": 425,
      "raw": "#check @FLTForHuman.Elliptic.rel₃_iff_evenRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.rel₃_iff_evenRec",
      "display": "@FLTForHuman.Elliptic.rel₃_iff_evenRec",
      "card": "FLTForHuman.Elliptic.rel₃_iff_evenRec"
    },
    {
      "type": "check",
      "line": 426,
      "raw": "#check @FLTForHuman.Elliptic.rel₃_iff₄",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.rel₃_iff₄",
      "display": "@FLTForHuman.Elliptic.rel₃_iff₄",
      "card": "FLTForHuman.Elliptic.rel₃_iff₄"
    },
    {
      "type": "check",
      "line": 427,
      "raw": "#check @FLTForHuman.Elliptic.net_zero_iff_rel₃",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.net_zero_iff_rel₃",
      "display": "@FLTForHuman.Elliptic.net_zero_iff_rel₃",
      "card": "FLTForHuman.Elliptic.net_zero_iff_rel₃"
    },
    {
      "type": "example",
      "line": 429,
      "text": "example {R : Type*} [CommRing R] (W : ℤ → R) (m : ℤ) :\n    Rel₃ W (m + 1) m 1 ↔ OddRec W m := rel₃_iff_oddRec W m",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " **Step 2 — normalise a relator.** A relator is only interesting on indices of\none parity, and `rel₄_transf` rewrites the relator at `(a,b,c,d)` to the relator\nat four indices built from the midpoint `avg₄ = (a+b+c+d)/2`. Iterating that\ndescends a well-founded order on the largest index, and\n`rel₄_of_anti_oddRec_evenRec` finishes by `Int.strongRec` with the recurrences as\nbase cases. `HaveSameParity₄`/`StrictAnti₄` are the side conditions of the\ndescent. FLT's names for `atom`/`atomRel`/`rel` are `addMulSub`/`rel₄`/`net`, and\n`EllSequence.lean` keeps both spellings. ",
      "zone": "C",
      "line": 432
    },
    {
      "type": "check",
      "line": 441,
      "raw": "#check @FLTForHuman.Elliptic.HaveSameParity₄",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.HaveSameParity₄",
      "display": "@FLTForHuman.Elliptic.HaveSameParity₄",
      "card": "FLTForHuman.Elliptic.HaveSameParity₄"
    },
    {
      "type": "check",
      "line": 442,
      "raw": "#check @FLTForHuman.Elliptic.StrictAnti₄",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.StrictAnti₄",
      "display": "@FLTForHuman.Elliptic.StrictAnti₄",
      "card": "FLTForHuman.Elliptic.StrictAnti₄"
    },
    {
      "type": "check",
      "line": 443,
      "raw": "#check @FLTForHuman.Elliptic.avg₄",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.avg₄",
      "display": "@FLTForHuman.Elliptic.avg₄",
      "card": "FLTForHuman.Elliptic.avg₄"
    },
    {
      "type": "check",
      "line": 444,
      "raw": "#check @FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf",
      "display": "@FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf",
      "card": "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf"
    },
    {
      "type": "check",
      "line": 445,
      "raw": "#check @FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
      "display": "@FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
      "card": "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec"
    },
    {
      "type": "prose",
      "md": " **Step 3 — the headline.** Oddness and `W 0 = 0` are automatic for `normEDS`,\nso the two recurrences alone give the elliptic-sequence property. The\n`_of_mem_nonZeroDivisors` variant is the workhorse: it needs `b ∈ R⁰` for the\ncancellation step, and the general statement instantiates it over a ring where\nthe cancellation is free (Step 4). ",
      "zone": "C",
      "line": 447
    },
    {
      "type": "check",
      "line": 453,
      "raw": "#check @FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec",
      "display": "@FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec",
      "card": "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec"
    },
    {
      "type": "check",
      "line": 454,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_isEllipticSequence",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.normEDS_isEllipticSequence",
      "display": "@FLTForHuman.Elliptic.normEDS_isEllipticSequence",
      "card": "FLTForHuman.Elliptic.normEDS_isEllipticSequence"
    },
    {
      "type": "check",
      "line": 455,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors",
      "display": "@FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors",
      "card": "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors"
    },
    {
      "type": "prose",
      "md": " **Step 4 — the universal trick.** To get `b ∈ R⁰` for free, prove the\nstatement over the universal ring `ℤ[B,C,D]`, where `B` is a non-zero-divisor,\nand transport along `aeval (Param.rec b c d)`. This is the recurring proof\ntechnique of the whole EDS layer (`invar₂_normEDS`, `redInvar_normEDS`, the\ngeneral complement all go the same way). `normEDS_two_three_two` — the identity\nsequence is `normEDS 2 3 2` — is how the universal EDS is detected as non-zero:\nspecialise `B,C,D ↦ 2,3,2`, and a vanishing term would vanish in `id`. ",
      "zone": "C",
      "line": 457
    },
    {
      "type": "check",
      "line": 465,
      "raw": "#check @FLTForHuman.Elliptic.Param",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.Param",
      "display": "@FLTForHuman.Elliptic.Param",
      "card": "FLTForHuman.Elliptic.Param"
    },
    {
      "type": "check",
      "line": 466,
      "raw": "#check @FLTForHuman.Elliptic.universalNormEDS",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.universalNormEDS",
      "display": "@FLTForHuman.Elliptic.universalNormEDS",
      "card": "FLTForHuman.Elliptic.universalNormEDS"
    },
    {
      "type": "check",
      "line": 467,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_eq_aeval",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.normEDS_eq_aeval",
      "display": "@FLTForHuman.Elliptic.normEDS_eq_aeval",
      "card": "FLTForHuman.Elliptic.normEDS_eq_aeval"
    },
    {
      "type": "check",
      "line": 468,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_two_three_two",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.normEDS_two_three_two",
      "display": "@FLTForHuman.Elliptic.normEDS_two_three_two",
      "card": "FLTForHuman.Elliptic.normEDS_two_three_two"
    },
    {
      "type": "check",
      "line": 469,
      "raw": "#check @FLTForHuman.Elliptic.universalNormEDS_ne_zero",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.universalNormEDS_ne_zero",
      "display": "@FLTForHuman.Elliptic.universalNormEDS_ne_zero",
      "card": "FLTForHuman.Elliptic.universalNormEDS_ne_zero"
    },
    {
      "type": "check",
      "line": 470,
      "raw": "#check @FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors",
      "display": "@FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors",
      "card": "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors"
    },
    {
      "type": "example",
      "line": 473,
      "text": "example : normEDS (2 : ℤ) 3 2 = id := normEDS_two_three_two",
      "zone": "C",
      "doc": "The identity EDS, live."
    },
    {
      "type": "prose",
      "md": " **Step 5 — rigidity.** An elliptic sequence with `W 1`, `W 2` invertible is\ndetermined by its first four values, so the recurrences plus four numbers\n*characterise* the sequence rather than merely generating one. That is what\nmakes `normEDS` canonical, and it is the reason the definition of `ψ` can be\nmoved between normalisations at will. Finally `net_of_isEllipticSequence`\nupgrades the `s = 0` slice to the full net by evaluating at\n`(2p+s, 2q+s, 2r+s, s)`, a quadruple whose entries always share a parity. ",
      "zone": "C",
      "line": 475
    },
    {
      "type": "check",
      "line": 483,
      "raw": "#check @FLTForHuman.Elliptic.isEllipticSequence_ext",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.isEllipticSequence_ext",
      "display": "@FLTForHuman.Elliptic.isEllipticSequence_ext",
      "card": "FLTForHuman.Elliptic.isEllipticSequence_ext"
    },
    {
      "type": "check",
      "line": 484,
      "raw": "#check @FLTForHuman.Elliptic.net_of_isEllipticSequence",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.net_of_isEllipticSequence",
      "display": "@FLTForHuman.Elliptic.net_of_isEllipticSequence",
      "card": "FLTForHuman.Elliptic.net_of_isEllipticSequence"
    },
    {
      "type": "check",
      "line": 485,
      "raw": "#check @FLTForHuman.Elliptic.net_normEDS",
      "zone": "C",
      "name": "FLTForHuman.Elliptic.net_normEDS",
      "display": "@FLTForHuman.Elliptic.net_normEDS",
      "card": "FLTForHuman.Elliptic.net_normEDS"
    },
    {
      "type": "prose",
      "md": "Why two worlds at all? One mathematical reason and one formal one.\n\n**Mathematical.** The `x`-coordinate of `[n]P` is `Φ n (x) / ΨSq n (x)`, a\none-variable rational function: `Φ n` has degree `n²` and `ΨSq n` degree\n`n² - 1`. The fibre count of `card_torsion_of_isAlgClosed` only ever looks at\n`x`-fibres, so it only needs the univariate pair. The `y`-coordinate genuinely\nneeds the bivariate `ψ`.\n\n**Formal.** Even over a field, `R[X][Y]` is not a Euclidean domain and `Y`\ncannot be eliminated without passing to the coordinate ring; `R[X]` is Euclidean\nas soon as `R` is a field, so `gcd`, coprimality and `natDegree` are available.\nThe `if Even n` factors in `ΨSq` and `Φ` are exactly what keeps the univariate\nside closed under the EDS recurrence.\n\nThe two worlds are glued by `mk : R[X][Y] →+* R[W]`, the quotient map onto the\ncoordinate ring `R[W] = R[X,Y] / (Y² + a₁XY + a₃Y - X³ - a₂X² - a₄X - a₆)`. Four\nmathlib lemmas say the dictionary is exact on the curve: ",
      "zone": "D",
      "line": 487
    },
    {
      "type": "check",
      "line": 507,
      "raw": "#check @WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq  -- (mk ψ₂) ^ 2 = mk (C Ψ₂Sq)",
      "zone": "D",
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq",
      "display": "@WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq",
      "card": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq"
    },
    {
      "type": "check",
      "line": 508,
      "raw": "#check @WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq   -- (mk (Ψ n)) ^ 2 = mk (C (ΨSq n))",
      "zone": "D",
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq",
      "display": "@WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq",
      "card": "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq"
    },
    {
      "type": "check",
      "line": 509,
      "raw": "#check @WeierstrassCurve.Affine.CoordinateRing.mk_ψ       -- mk (ψ n) = mk (Ψ n)",
      "zone": "D",
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ",
      "display": "@WeierstrassCurve.Affine.CoordinateRing.mk_ψ",
      "card": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ"
    },
    {
      "type": "check",
      "line": 510,
      "raw": "#check @WeierstrassCurve.Affine.CoordinateRing.mk_φ       -- mk (φ n) = mk (C (Φ n))",
      "zone": "D",
      "name": "WeierstrassCurve.Affine.CoordinateRing.mk_φ",
      "display": "@WeierstrassCurve.Affine.CoordinateRing.mk_φ",
      "card": "WeierstrassCurve.Affine.CoordinateRing.mk_φ"
    },
    {
      "type": "example",
      "line": 513,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ₂ ^ 2)\n      = WeierstrassCurve.Affine.CoordinateRing.mk W (C W.Ψ₂Sq) :=\n  WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq W",
      "zone": "D",
      "doc": "The first line of the dictionary, live."
    },
    {
      "type": "example",
      "line": 522,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ₂ ^ 4)\n      = WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.Ψ₂Sq ^ 2)) := by\n  rw [show (4 : ℕ) = 2 * 2 by norm_num, map_pow, pow_mul,\n    WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq, ← map_pow, C_pow]",
      "zone": "D",
      "doc": "Squaring that explains the strange parameter of `preΨ`. In Zone B, `ψ` is\n`normEDS` run with `b = ψ₂`, so its internal `preNormEDS` sees `ψ₂ ^ 4`; on the\ncurve that is the shadow of `Ψ₂Sq ^ 2`, which is precisely the first argument of\n`preΨ = preNormEDS (Ψ₂Sq ^ 2) Ψ₃ preΨ₄`."
    },
    {
      "type": "prose",
      "md": " The univariate recurrences, and the identity that carries the curve's\ngeometry into the EDS bookkeeping. `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃` with\n`invar = 6X ^ 2 + b₂ * X + b₄` is a polynomial identity in `R[X]` valid in every\ncharacteristic; on the curve it reads `d + b ^ 4 = invar * c`, i.e. it fixes the\ninvariant `(d + b ^ 4) / c` of the division-polynomial EDS as the polynomial\n`invar`. ",
      "zone": "D",
      "line": 528
    },
    {
      "type": "check",
      "line": 535,
      "raw": "#check @WeierstrassCurve.preΨ_even",
      "zone": "D",
      "name": "WeierstrassCurve.preΨ_even",
      "display": "@WeierstrassCurve.preΨ_even",
      "card": "WeierstrassCurve.preΨ_even"
    },
    {
      "type": "check",
      "line": 536,
      "raw": "#check @WeierstrassCurve.preΨ_odd",
      "zone": "D",
      "name": "WeierstrassCurve.preΨ_odd",
      "display": "@WeierstrassCurve.preΨ_odd",
      "card": "WeierstrassCurve.preΨ_odd"
    },
    {
      "type": "check",
      "line": 537,
      "raw": "#check @WeierstrassCurve.C_Ψ₂Sq",
      "zone": "D",
      "name": "WeierstrassCurve.C_Ψ₂Sq",
      "display": "@WeierstrassCurve.C_Ψ₂Sq",
      "card": "WeierstrassCurve.C_Ψ₂Sq"
    },
    {
      "type": "check",
      "line": 538,
      "raw": "#check @WeierstrassCurve.Ψ₂Sq_eq",
      "zone": "D",
      "name": "WeierstrassCurve.Ψ₂Sq_eq",
      "display": "@WeierstrassCurve.Ψ₂Sq_eq",
      "card": "WeierstrassCurve.Ψ₂Sq_eq"
    },
    {
      "type": "check",
      "line": 539,
      "raw": "#check @WeierstrassCurve.Φ_neg",
      "zone": "D",
      "name": "WeierstrassCurve.Φ_neg",
      "display": "@WeierstrassCurve.Φ_neg",
      "card": "WeierstrassCurve.Φ_neg"
    },
    {
      "type": "check",
      "line": 540,
      "raw": "#check @FLTForHuman.Elliptic.invar",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.invar",
      "display": "@FLTForHuman.Elliptic.invar",
      "card": "FLTForHuman.Elliptic.invar"
    },
    {
      "type": "check",
      "line": 541,
      "raw": "#check @FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
      "zone": "D",
      "name": "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
      "display": "@FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
      "card": "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq"
    },
    {
      "type": "example",
      "line": 544,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :\n    W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ := preΨ₄_add_Ψ₂Sq_sq W",
      "zone": "D",
      "doc": "The invariant identity, live."
    },
    {
      "type": "prose",
      "md": " Two things this import does **not** contain, so that a `#check` failure below\nis not mistaken for a typo:\n\n* the degree facts `natDegree (Φ n) = n ^ 2` and `natDegree (ΨSq n) = n ^ 2 - 1`\n  live in mathlib's `DivisionPolynomial/Degree.lean`, one file above\n  `Basic.lean`; the port consumes them through `TorsionCard.lean`. Try\n  `#check @WeierstrassCurve.natDegree_Φ` here and it is an unknown identifier —\n  that is this, not a mistake. (`CardNTorsion.lean`, Zone B, is where they are\n  read.)\n* the point-group bridge — `evalEval_ψ_sq`, `evalEval_φ`, `smul_x_eq`,\n  `smul_eq_zero_of_ΨSq_eval_eq_zero` — is `FLTForHuman/Elliptic/Bridge.lean` and\n  `TorsionCard.lean`, the other side of this story. It is read in\n  `CardNTorsion.lean`, Zone D. ",
      "zone": "D",
      "line": 547
    },
    {
      "type": "prose",
      "md": "The EDS vocabulary is not decoration. It is what makes the multiplication\nformula `[n]P = (φ n / (ψ n) ^ 2, ω n / (ψ n) ^ 3)` hold over *every* commutative\nring — hence in every characteristic — when the textbook statement divides by\n`ψ n` and by `2`. Two constructions do the work.\n\n**The complement turns divisibility into a polynomial.** `W k ∣ W (n * k)` is\nwitnessed by a second sequence `complEDS`, with `W k * complEDS k n = W (n * k)`\nand no division; the `2`-complement is `complEDS₂`, and the port's `ψc` is its\ninstance for `ψ`. `normEDS_mul_complEDS` is the port's general multiplicativity,\nwhich mathlib only has for `n = 2`. ",
      "zone": "E",
      "line": 561
    },
    {
      "type": "check",
      "line": 574,
      "raw": "#check @complEDS₂",
      "zone": "E",
      "name": "complEDS₂",
      "display": "@complEDS₂",
      "card": "complEDS₂"
    },
    {
      "type": "check",
      "line": 575,
      "raw": "#check @normEDS_mul_complEDS₂",
      "zone": "E",
      "name": "normEDS_mul_complEDS₂",
      "display": "@normEDS_mul_complEDS₂",
      "card": "normEDS_mul_complEDS₂"
    },
    {
      "type": "check",
      "line": 576,
      "raw": "#check @normEDS_dvd_normEDS_two_mul",
      "zone": "E",
      "name": "normEDS_dvd_normEDS_two_mul",
      "display": "@normEDS_dvd_normEDS_two_mul",
      "card": "normEDS_dvd_normEDS_two_mul"
    },
    {
      "type": "check",
      "line": 577,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_mul_complEDS",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.normEDS_mul_complEDS",
      "display": "@FLTForHuman.Elliptic.normEDS_mul_complEDS",
      "card": "FLTForHuman.Elliptic.normEDS_mul_complEDS"
    },
    {
      "type": "check",
      "line": 578,
      "raw": "#check @FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
      "display": "@FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
      "card": "FLTForHuman.Elliptic.normEDS_mul_complEDS_div"
    },
    {
      "type": "check",
      "line": 579,
      "raw": "#check @FLTForHuman.Elliptic.ψc",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.ψc",
      "display": "@FLTForHuman.Elliptic.ψc",
      "card": "FLTForHuman.Elliptic.ψc"
    },
    {
      "type": "check",
      "line": 580,
      "raw": "#check @FLTForHuman.Elliptic.ψc_spec",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.ψc_spec",
      "display": "@FLTForHuman.Elliptic.ψc_spec",
      "card": "FLTForHuman.Elliptic.ψc_spec"
    },
    {
      "type": "check",
      "line": 581,
      "raw": "#check @FLTForHuman.Elliptic.complEDSAux",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.complEDSAux",
      "display": "@FLTForHuman.Elliptic.complEDSAux",
      "card": "FLTForHuman.Elliptic.complEDSAux"
    },
    {
      "type": "example",
      "line": 584,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :\n    W.ψ n ∣ W.ψ (2 * n) :=\n  normEDS_dvd_normEDS_two_mul W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n",
      "zone": "E",
      "doc": "`ψ n` divides `ψ (2 * n)`, with `ψc n` as the explicit cofactor."
    },
    {
      "type": "example",
      "line": 589,
      "text": "example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :\n    W.ψ n * ψc W n = W.ψ (2 * n) := ψc_spec W n",
      "zone": "E",
      "doc": "The cofactor, named."
    },
    {
      "type": "prose",
      "md": " **The invariant makes `ω` a polynomial.** `invarNum`/`invarDenom` are a\nnumerator/denominator pair whose ratio is independent of the running index —\n`invar_of_net`, whose only input is the net relation of Zone C. Because the pair\nis projective, the ratio can be defined without ever forming a quotient, and\n`invar₂_normEDS` computes it for `normEDS` as `(d + b ^ 4) / c`. The `red*` pair\nis the same object with the factors `b`, `c` peeled off, so that it lands in\n`R[X]` for the division polynomials. ",
      "zone": "E",
      "line": 592
    },
    {
      "type": "check",
      "line": 600,
      "raw": "#check @FLTForHuman.Elliptic.invarNum",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invarNum",
      "display": "@FLTForHuman.Elliptic.invarNum",
      "card": "FLTForHuman.Elliptic.invarNum"
    },
    {
      "type": "check",
      "line": 601,
      "raw": "#check @FLTForHuman.Elliptic.invarDenom",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invarDenom",
      "display": "@FLTForHuman.Elliptic.invarDenom",
      "card": "FLTForHuman.Elliptic.invarDenom"
    },
    {
      "type": "check",
      "line": 602,
      "raw": "#check @FLTForHuman.Elliptic.invar_of_net",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invar_of_net",
      "display": "@FLTForHuman.Elliptic.invar_of_net",
      "card": "FLTForHuman.Elliptic.invar_of_net"
    },
    {
      "type": "check",
      "line": 603,
      "raw": "#check @FLTForHuman.Elliptic.invar_normEDS",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invar_normEDS",
      "display": "@FLTForHuman.Elliptic.invar_normEDS",
      "card": "FLTForHuman.Elliptic.invar_normEDS"
    },
    {
      "type": "check",
      "line": 604,
      "raw": "#check @FLTForHuman.Elliptic.invar₂_normEDS",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invar₂_normEDS",
      "display": "@FLTForHuman.Elliptic.invar₂_normEDS",
      "card": "FLTForHuman.Elliptic.invar₂_normEDS"
    },
    {
      "type": "check",
      "line": 605,
      "raw": "#check @FLTForHuman.Elliptic.redInvarNum",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.redInvarNum",
      "display": "@FLTForHuman.Elliptic.redInvarNum",
      "card": "FLTForHuman.Elliptic.redInvarNum"
    },
    {
      "type": "check",
      "line": 606,
      "raw": "#check @FLTForHuman.Elliptic.redInvarDenom",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.redInvarDenom",
      "display": "@FLTForHuman.Elliptic.redInvarDenom",
      "card": "FLTForHuman.Elliptic.redInvarDenom"
    },
    {
      "type": "check",
      "line": 607,
      "raw": "#check @FLTForHuman.Elliptic.redInvar_normEDS",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.redInvar_normEDS",
      "display": "@FLTForHuman.Elliptic.redInvar_normEDS",
      "card": "FLTForHuman.Elliptic.redInvar_normEDS"
    },
    {
      "type": "check",
      "line": 608,
      "raw": "#check @FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
      "display": "@FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
      "card": "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul"
    },
    {
      "type": "prose",
      "md": " **`ωe`: the `y`-numerator, defined without dividing by `2`.** `ωe_spec` is\nthe theorem that it deserves the name: `2 * ωe n = ψc n - a₁ * φ n * ψ n -\na₃ * (ψ n) ^ 3`, which is the classical `ω n` with the halving left in place. Over\na ring where `2` is invertible this pins `ωe` down; in characteristic `2` the\nclassical `ω` does not exist and this polynomial formula is the replacement.\nThis is the single service the EDS layer provides to FLT, and the reason it\ncannot be simplified away (`math/025` §5). ",
      "zone": "E",
      "line": 610
    },
    {
      "type": "check",
      "line": 618,
      "raw": "#check @FLTForHuman.Elliptic.ωe",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.ωe",
      "display": "@FLTForHuman.Elliptic.ωe",
      "card": "FLTForHuman.Elliptic.ωe"
    },
    {
      "type": "check",
      "line": 619,
      "raw": "#check @FLTForHuman.Elliptic.ωe_spec",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.ωe_spec",
      "display": "@FLTForHuman.Elliptic.ωe_spec",
      "card": "FLTForHuman.Elliptic.ωe_spec"
    },
    {
      "type": "check",
      "line": 620,
      "raw": "#check @FLTForHuman.Elliptic.two_mul_ωe",
      "zone": "E",
      "name": "FLTForHuman.Elliptic.two_mul_ωe",
      "display": "@FLTForHuman.Elliptic.two_mul_ωe",
      "card": "FLTForHuman.Elliptic.two_mul_ωe"
    },
    {
      "type": "prose",
      "md": "* Compare the `#print preNormEDS` and `#print normEDS` bodies in B3:\n  `preNormEDS` is `n.sign * preNormEDS' … n.natAbs`, and `normEDS` is\n  `preNormEDS (b ^ 4) c d n * (if Even n then b else 1)` — the whole\n  normalisation in one line. The `#print` of `ψ` in Zone A shows `ψ` is the\n  `normEDS` case, and the `Φ`/`ΨSq` bodies show the same `if Even` branch on the\n  univariate side.\n* Change `5` to `7` and `9` in the two closed forms of Zone B. The odd recursion\n  only ever reads backwards, so each one is a one-line `rw`/`ring`; the monomials\n  multiply. For instance\n  `normEDS b c d 7 = d * b ^ 4 * c ^ 3 - c ^ 6 - d ^ 3 * b ^ 4`, which is\n  `normEDS_odd` at `m = 3` with `normEDS 5` substituted.\n* Try to state the analogous closed form for `normEDS b c d 6` *without* the\n  `preNormEDS` factor. In `ℤ` you cannot: the honest content of the even step is\n  `W (2n) * W 2 = …`, and the `b` has to be carried, not cancelled. That is the\n  point of Zone B, visible in a goal state.\n* Swap the import for `FLTForHuman.Elliptic.TorsionCard` (about a second more)\n  and the Zone D note becomes live: `#check @WeierstrassCurve.natDegree_Φ`,\n  `#check @FLTForHuman.Elliptic.smul_x_eq`,\n  `#check @FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero`. That is the\n  bridge from these polynomials to the point group, and the subject of the\n  companion worksheet `CardNTorsion.lean`.\n* The `#check @FLTForHuman.Elliptic.ωe_spec` output prints the port's `CC`\n  cast (`CC W.a₁`); `CC` is mathlib's `Polynomial.C` bundled as a ring\n  homomorphism into the bivariate ring. Nothing mathematical hides there.\n* Try `example : IsEllipticSequence (fun n : ℤ => n) := IsEllipticSequence.id`\n  — the identity sequence is the trivial EDS, and `normEDS_two_three_two` is the\n  statement that it is the `(b,c,d) = (2,3,2)` specialisation. ",
      "zone": "F",
      "line": 622
    },
    {
      "type": "prose",
      "md": "Oldest first. Each entry: question, one-line answer, pointer to the zone edited.\n\n* (2026-10-15) *Worksheet created.* — subject named: \"the division polynomials\n  and how the EDS works\"; split out of `CardNTorsion.lean` Zone D, which now\n  points here. No questions yet.\n* (2026-10-15) **Q1.** *The polynomial approach is not very illuminating — is it\n  only there so the count works in any characteristic?* — Half. Two answers.\n  (i) Zone D: the univariate `Φ`/`ΨSq` are what supply the **degree** `n²`, i.e.\n  the value of the count, and `R[X]` is where degree and `gcd` live — `R[X][Y]`\n  is not a Euclidean domain. (ii) The EDS view of Zones B–C is the structural\n  explanation the polynomial view hides: one quartic relator generates the whole\n  zoo, Ward's recurrences are two of its slices, and the `if Even` factors are\n  the price of doing it with no division rather than a feature of the field.\n* (2026-10-15) **Q2.** *Why does `preΨ` run on `Ψ₂Sq ^ 2` and not on `Ψ₂Sq`?* —\n  Because `preΨ` shadows `ψ = normEDS ψ₂ …`, whose internal `preNormEDS` sees\n  `ψ₂ ^ 4`; on the curve `ψ₂ ^ 4` is `Ψ₂Sq ^ 2`. See the `ψ₂ ^ 4` example in\n  Zone D.\n* (2026-10-15) **Q3.** *How should I read `ψ n ^ 2` — is it `(ψ n) ^ 2` or\n  `ψ (n ^ 2)`?* — Application binds tighter than `^`, so it is `(ψ n) ^ 2`, the\n  intended `ψₙ²`; `ψ (n ^ 2)` needs the parentheses. See the new \"Reading\n  `ψ n ^ 2`\" block at the end of Zone A, where `rfl` and a `normEDS`-at-`4`\n  example separate the two readings and `#check` shows how Lean prints them\n  back.\n* (2026-10-15) **Q4.** *Follow-up on Q3: then the display\n  `[n]P = (φ n / ψ n ^ 2, …)` in Zone E should read `(ψ n) ^ 2`.* — Agreed, and\n  the same for every application under a power in Zones A, B, D and E. The\n  parse block now also notes that Lean's printer *drops* the redundant\n  parentheses, so a display copied out of a goal state reacquires the ambiguity;\n  prose here spells the exponent out. See the corrected Zone E formula.\n* (2026-10-15) **Q5.** *We use `normEDS`/`preNormEDS` but never introduced them —\n  what are they?* — Zone B is now a five-part introduction: **B1** the object\n  (Ward's relation, the normalisation, rigidity, examples), **B2** the two\n  recurrences, **B3** `preNormEDS` as the other gauge and the identity\n  `normEDS = preNormEDS (b ^ 4) … * (if Even n then b else 1)`, **B4** why the\n  exponent is `4` (quartic homogeneity: four factors of `W` per term), **B5** the\n  net reformulation. Writing B1 also caught an error in this file: the relator\n  had been called \"cubic\"; it is *quartic*, which is exactly what makes `b ^ 4`\n  the natural gauge rather than `b`. ",
      "zone": "Q",
      "line": 652
    },
    {
      "type": "code",
      "line": 693,
      "text": "end Play",
      "zone": "Q"
    }
  ],
  "seed_cards": ["FLTForHuman.Elliptic.EvenRec","FLTForHuman.Elliptic.HaveSameParity₄","FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf","FLTForHuman.Elliptic.OddRec","FLTForHuman.Elliptic.Param","FLTForHuman.Elliptic.Rel₃","FLTForHuman.Elliptic.StrictAnti₄","FLTForHuman.Elliptic.addMulSub","FLTForHuman.Elliptic.avg₄","FLTForHuman.Elliptic.card_torsion_of_isAlgClosed","FLTForHuman.Elliptic.complEDSAux","FLTForHuman.Elliptic.evalEval_φ","FLTForHuman.Elliptic.evalEval_ψ_sq","FLTForHuman.Elliptic.invar","FLTForHuman.Elliptic.invarDenom","FLTForHuman.Elliptic.invarNum","FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul","FLTForHuman.Elliptic.invar_normEDS","FLTForHuman.Elliptic.invar_of_net","FLTForHuman.Elliptic.invar₂_normEDS","FLTForHuman.Elliptic.isEllipticSequence_ext","FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃","FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec","FLTForHuman.Elliptic.net","FLTForHuman.Elliptic.net_normEDS","FLTForHuman.Elliptic.net_of_isEllipticSequence","FLTForHuman.Elliptic.net_zero_iff_rel₃","FLTForHuman.Elliptic.normEDS_eq_aeval","FLTForHuman.Elliptic.normEDS_isEllipticSequence","FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors","FLTForHuman.Elliptic.normEDS_mul_complEDS","FLTForHuman.Elliptic.normEDS_mul_complEDS_div","FLTForHuman.Elliptic.normEDS_two_three_two","FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq","FLTForHuman.Elliptic.redInvarDenom","FLTForHuman.Elliptic.redInvarNum","FLTForHuman.Elliptic.redInvar_normEDS","FLTForHuman.Elliptic.rel₃_iff_evenRec","FLTForHuman.Elliptic.rel₃_iff_oddRec","FLTForHuman.Elliptic.rel₃_iff₄","FLTForHuman.Elliptic.rel₄","FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec","FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero","FLTForHuman.Elliptic.two_mul_ωe","FLTForHuman.Elliptic.universalNormEDS","FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors","FLTForHuman.Elliptic.universalNormEDS_ne_zero","FLTForHuman.Elliptic.ψc","FLTForHuman.Elliptic.ψc_spec","FLTForHuman.Elliptic.ωe","FLTForHuman.Elliptic.ωe_spec","Int.strongRec","IsEllipticDvdSequence","IsEllipticNet","IsEllipticNet.atom","IsEllipticNet.atomRel","IsEllipticNet.atomRel_eq","IsEllipticNet.rel","IsEllipticNet.rel_eq","IsEllipticSequence","Polynomial.C","Polynomial.CC","Polynomial.natDegree","WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq","WeierstrassCurve.Affine.CoordinateRing.mk_φ","WeierstrassCurve.Affine.CoordinateRing.mk_ψ","WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq","WeierstrassCurve.C_Ψ₂Sq","WeierstrassCurve.mk","WeierstrassCurve.preΨ","WeierstrassCurve.preΨ'","WeierstrassCurve.preΨ_even","WeierstrassCurve.preΨ_odd","WeierstrassCurve.preΨ₄","WeierstrassCurve.Φ","WeierstrassCurve.Φ_neg","WeierstrassCurve.Φ_three","WeierstrassCurve.Ψ","WeierstrassCurve.ΨSq","WeierstrassCurve.ΨSq_three","WeierstrassCurve.Ψ₂Sq","WeierstrassCurve.Ψ₂Sq_eq","WeierstrassCurve.Ψ₃","WeierstrassCurve.φ","WeierstrassCurve.ψ","WeierstrassCurve.ψ_one","WeierstrassCurve.ψ_two","WeierstrassCurve.ψ_zero","WeierstrassCurve.ψ₂","complEDS","complEDS₂","id","normEDS","normEDS_dvd_normEDS_two_mul","normEDS_even","normEDS_four","normEDS_mul_complEDS₂","normEDS_neg","normEDS_odd","normEDS_one","normEDS_three","normEDS_two","normEDS_zero","preNormEDS","preNormEDS'","preNormEDS_even","preNormEDS_odd"],
  "card_count": 182,
  "modules": ["FLTForHuman.Elliptic.Bridge","FLTForHuman.Elliptic.Complement","FLTForHuman.Elliptic.DivisionPolynomial","FLTForHuman.Elliptic.EDS","FLTForHuman.Elliptic.EllSequence","FLTForHuman.Elliptic.Net","FLTForHuman.Elliptic.Omega","FLTForHuman.Elliptic.RedInvar","FLTForHuman.Elliptic.TorsionCard","Init.Core","Init.Data.Cast","Init.Data.Int.Basic","Init.Data.Int.DivMod.Basic","Init.Data.List.Basic","Init.Prelude","Init.WF","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Algebra.Hom","Mathlib.Algebra.Divisibility.Basic","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.Group.Even","Mathlib.Algebra.Group.EvenFunction","Mathlib.Algebra.Group.Submonoid.Defs","Mathlib.Algebra.Group.Units.Defs","Mathlib.Algebra.GroupWithZero.NonZeroDivisors","Mathlib.Algebra.Module.LinearMap.Defs","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.Module.Torsion.Basic","Mathlib.Algebra.MonoidAlgebra.Basic","Mathlib.Algebra.MvPolynomial.Basic","Mathlib.Algebra.MvPolynomial.Eval","Mathlib.Algebra.Order.Group.Unbundled.Abs","Mathlib.Algebra.Polynomial.Basic","Mathlib.Algebra.Polynomial.Bivariate","Mathlib.Algebra.Polynomial.Degree.Defs","Mathlib.Algebra.Polynomial.Eval.Defs","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Algebra.Ring.NegOnePow","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula","Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point","Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic","Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass","Mathlib.Data.Finsupp.Defs","Mathlib.Data.Int.Init","Mathlib.Data.Nat.DvdSequence","Mathlib.FieldTheory.IsAlgClosed.Basic","Mathlib.NumberTheory.EllipticDivisibilitySequence","Mathlib.Order.WithBot","Mathlib.SetTheory.Cardinal.Finite"]
};
