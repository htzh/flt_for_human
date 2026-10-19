/-
  PLAY · the division polynomials — ψ, Ψ, ΨSq, Φ, φ and the EDS under them
  ============================================================================

  Subject   the division polynomials of a Weierstrass curve, and the elliptic
            divisibility sequence (EDS) layer that generates them
  Reads     FLTForHuman/Elliptic/Omega.lean, the top of the EDS cone: it imports
            Net → RedInvar → Complement → EllSequence → EDS → DivisionPolynomial,
            and hence mathlib's
            AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean and
            NumberTheory/EllipticDivisibilitySequence.lean
  Pin       Definitions/Def_WeierstrassCurve_EDSEngine.lean · aa2d8b3
            <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_WeierstrassCurve_EDSEngine.lean>
  Check     cd lean && lake env lean play/DivisionPolynomials.lean  (~3.3 s warm)
  Status    open
  Date      2026-10-15
  Intro     Companion to `CardNTorsion.lean`, which reads the *point* side of
            the same story; this worksheet reads the *polynomial* side: what
            `W.Φ`, `W.Ψ`, `W.ΨSq`, `W.ψ` are, which recurrence generates them,
            and what the EDS vocabulary buys. The mathematics is written up in
            `math/025-elliptic-nets-division-polynomials-and-the-invariant.md`.

  One import, and it is the whole cone. `Omega` is the `y`-coordinate invariant
  at the top of the EDS layer, so it contains `DivisionPolynomial.lean` (the
  definitions), `EDS.lean` (the universal sequence), `EllSequence.lean` (the net
  property), `Complement.lean` / `RedInvar.lean` / `Net.lean` (divisibility and
  the invariant), and `Omega.lean` itself. Measured on this machine: the bare
  import is 2.7 s warm, the same as importing `EllSequence` alone, so the upper
  layers are free at this scale and the subject is the whole layer. (R1:
  `play/README.md`.)

  This is a worksheet, not library code: nothing globs `lean/play/`, the sheets
  are tracked, and it exists so that the ported EDS theory can be read, poked at
  and questioned in the editor. Ground rules and workflow: `play/README.md`.

  Zones
    A  the cast — eleven names over four sequences
    B  the object — normalised EDS, `normEDS`, `preNormEDS`
    C  the one relation — from the two recurrences to the net property
    D  the univariate shadow — `R[X]` versus `R[X][Y]`
    E  what the layer is for — complement, invariant, `ωe`
    F  things to poke at
    Q  question log
-/
import FLTForHuman.Elliptic.Omega

set_option autoImplicit false

noncomputable section

open scoped Polynomial Polynomial.Bivariate
open Polynomial
open WeierstrassCurve
open FLTForHuman.Elliptic

namespace Play

/- ## Zone A — the cast: eleven names over four sequences

The first obstacle is not mathematics but naming. mathlib keeps two worlds
strictly apart, and the names `ψ`/`Ψ`, `φ`/`Φ`, `ΨSq` have one foot in each:

  bivariate, `R[X][Y]` — honest polynomials in the coordinates `x`, `y`
    `ψ n`     the `n`-division polynomial   (`ψ 0 = 0`, `ψ 1 = 1`, `ψ 2 = ψ₂`)
    `Ψ n`     the same sequence, normalised so the even terms carry a `ψ₂`
    `φ n`     the `x`-numerator, `X * (ψ n) ^ 2 - ψ (n+1) * ψ (n-1)`
    `ψ₂`      the `2`-division polynomial `2Y + a₁X + a₃`

  univariate, `R[X]` — their shadows on the curve `R[W] = R[X,Y]/(W)`
    `preΨ n`  the auxiliary sequence, `= preNormEDS (Ψ₂Sq ^ 2) Ψ₃ preΨ₄ n`
    `ΨSq n`   congruent to `(ψ n) ^ 2`, `= (preΨ n) ^ 2 * (if Even n then Ψ₂Sq else 1)`
    `Φ n`     congruent to `φ n`,     `= X * ΨSq n - preΨ (n+1) * preΨ (n-1) * (if Even n then 1 else Ψ₂Sq)`
    `Ψ₂Sq`    congruent to `ψ₂ ^ 2`,  `= 4X³ + b₂X² + 2b₄X + b₆`
    `Ψ₃`      `= ψ 3` itself,         `= 3X⁴ + b₂X³ + 3b₄X² + 3b₆X + b₈`
    `preΨ₄`   `= ψ 4 / ψ₂` on curve,  `= 2X⁶ + b₂X⁵ + 5b₄X⁴ + 10b₆X³ + 10b₈X² + …`

The last four are *not* new polynomials. `Ψ₂Sq`, `Ψ₃`, `preΨ₄` are the three
initial values the recurrence is anchored at, and the `if Even` factors are the
bookkeeping that keeps the univariate side closed under that recurrence — the
subject of Zones B and D.

In Lean the definitions are literally these. Every name in the table: -/

#check @WeierstrassCurve.ψ₂
#check @WeierstrassCurve.Ψ₂Sq
#check @WeierstrassCurve.Ψ₃
#check @WeierstrassCurve.preΨ₄
#check @WeierstrassCurve.preΨ'
#check @WeierstrassCurve.preΨ
#check @WeierstrassCurve.Ψ
#check @WeierstrassCurve.ψ
#check @WeierstrassCurve.ΨSq
#check @WeierstrassCurve.Φ
#check @WeierstrassCurve.φ

/- The bodies. Note that `ψ` is *definitionally* a `normEDS` and `preΨ`
definitionally a `preNormEDS`; Zone B reads those two definitions, and the
`if Even n` branches in `Φ` and `ΨSq` are the same bookkeeping seen from the
univariate side. -/

#print WeierstrassCurve.ψ
#print WeierstrassCurve.preΨ
#print WeierstrassCurve.Φ
#print WeierstrassCurve.ΨSq

/- The two definitional equations, as `rfl` — the compiler confirms that these
are not theorems but the definitions themselves: -/

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.ψ = normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) := rfl

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.preΨ = preNormEDS (W.Ψ₂Sq ^ 2) W.Ψ₃ W.preΨ₄ := rfl

/- ### The initial values, live

The `simp` lemmas (`ψ_zero`, `ψ_one`, `ψ_two`, `ΨSq_three`, `Φ_three`, …) are
just these definitions unfolded. -/

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ψ 2 = W.ψ₂ := by simp
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ψ 3 = C W.Ψ₃ := by simp
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.preΨ 3 = W.Ψ₃ := by simp
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ΨSq 2 = W.Ψ₂Sq := by simp
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.ΨSq 3 = W.Ψ₃ ^ 2 := by simp
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.Φ 1 = X := by simp

/-- `Φ 3` is the definition with the `if Even` branch taken: `3` is odd, so the
`Ψ₂Sq` factor is present. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq := by simp

/-- `Φ 0 = 1` while `ΨSq 0 = 0`: the `n = 0` pair is the point at infinity (the
`n`-torsion of the zero endomorphism is everything), and it is handled by the
`simp` branch of the induction rather than by the recursion. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : W.Φ 0 = 1 := by simp

/- ### Reading `ψ n ^ 2`: application binds tighter than `^`

Worth pinning down once, because the tables above mix applications with powers —
`X * (ψ n) ^ 2` and the like. In Lean, function application has the highest
precedence, so `ψ n ^ 2` is `(ψ n) ^ 2` — the square of the `n`-th polynomial,
which is the mathematical reading of `ψₙ²`. To get `ψ` at the index `n ^ 2` you
must parenthesise: `ψ (n ^ 2)`. They are the same term only in the first case: -/

example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    (W.ψ n ^ 2 : R[X][Y]) = (W.ψ n) ^ 2 := rfl

/- The distinction is not vacuous: over `ℤ`, `normEDS b c d 2 ^ 2` is `b ^ 2`,
while `normEDS b c d (2 ^ 2)` is `normEDS b c d 4 = d * b`. -/

example (b c d : ℤ) : normEDS b c d 2 ^ 2 = b ^ 2 := by simp
example (b c d : ℤ) : normEDS b c d (2 ^ 2) = d * b := by norm_num [normEDS_four]

/- `#check` is the quickest way to see which reading elaboration picked: it
prints the two terms back with different parenthesisation — `W.ψ n ^ 2` against
`W.ψ (n ^ 2)`. Note that the printer *drops* the redundant parentheses, so a
display copied out of a goal state inherits the ambiguity; this worksheet
therefore spells the exponent out, `(ψ n) ^ 2`, in prose and displays. -/

#check fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ n ^ 2 : R[X][Y])
#check fun {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) => (W.ψ (n ^ 2) : R[X][Y])

/- This is also why the univariate square has its own *name*, `ΨSq n`, instead
of being written `(ψ n) ^ 2` in the univariate world. `ΨSq n` is a polynomial of
`R[X]`, not the square of the bivariate `Ψ n`; what is true is that its image in
the coordinate ring *is* the square, `mk (C (ΨSq n)) = (mk (Ψ n)) ^ 2`
(`mk_Ψ_sq`, Zone D). A distinct name costs nothing and removes the ambiguity
from every statement that mentions it. -/

/- ## Zone B — the object: normalised elliptic divisibility sequences

Every name in Zone A is generated by one sequence, mathlib's `normEDS b c d`.
This zone is the introduction to what that object is; `preNormEDS` is the
auxiliary sequence mathlib actually recurses on.

### B1 — what a normalised EDS is

Fix a commutative ring `R`. A sequence `W : ℤ → R` is an **elliptic sequence**
(Ward) if, for all `m, n, r : ℤ`,

    W (m + n) * W (m - n) * (W r) ^ 2
      = W (m + r) * W (m - r) * (W n) ^ 2 - W (n + r) * W (n - r) * (W m) ^ 2.

That is the port's `Rel₃`; `isEllipticSequence_iff_rel₃` says the predicate
`IsEllipticSequence` — defined by the four-index relator `rel` (Zone C) — is
exactly this condition. Call `W` **normalised** if, for three parameters
`b, c, d ∈ R`,

    W 0 = 0,    W 1 = 1,    W 2 = b,    W 3 = c,    W 4 = d * b.

`normEDS b c d` is the canonical normalised elliptic sequence with those
parameters. Three remarks on the definition:

* it is indexed by `ℤ`, and negation is free: `W (-n) = -W n` (`normEDS_neg`).
  A textbook division polynomial is usually written only for `n ≥ 1`; the sign
  is part of the normalisation here.
* `W 1 = 1` is what the word "normalised" buys: it lets the relation be divided
  through by `(W 1) ^ 2`, giving the familiar `W (m+n) * W (m-n) = …`.
* the relation is **quartic**: every term is a product of four factors of `W`,
  and it is homogeneous of that degree. Remember the `4`; it is exactly what
  fixes the exponent in the gauge relation of B3.

The sequence is *rigid*: the relation, the first four values, and
`W 1, W 2 ∈ R⁰` (non-zero-divisors) determine it completely
(`isEllipticSequence_ext`, Zone C). So `normEDS` is not one example among many;
it is *the* normalised EDS. Examples in the wild, from mathlib's own list: the
identity sequence (`normEDS 2 3 2 = id`, Zone C), suitable terms of Lucas
sequences, and the division polynomials — the last being this whole worksheet.
Here is a concrete one over `ℤ`, `normEDS 1 2 3`, whose start is
`0, 1, 1, 2, 3, -5, -28, -67, …`: -/

#check @FLTForHuman.Elliptic.Rel₃
#check @FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃
#check @normEDS_zero
#check @normEDS_one
#check @normEDS_two
#check @normEDS_three
#check @normEDS_four
#check @normEDS_neg

example {R : Type*} [CommRing R] (W : ℤ → R) :
    IsEllipticSequence W ↔ ∀ m n r : ℤ, Rel₃ W m n r := isEllipticSequence_iff_rel₃ W

/- (The values below are computed through `normEDS_odd`/`normEDS_even`, not by
`decide`: `preNormEDS'` is `@[irreducible]`, so the kernel will not unfold the
`ℕ`-indexed recursion for evaluation. The recurrences are the interface.) -/

example : normEDS (1 : ℤ) 2 3 1 = 1 := by simp

example : normEDS (1 : ℤ) 2 3 5 = -5 := by
  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]
  norm_num

example : normEDS (1 : ℤ) 2 3 6 = -28 := by
  have h5 : normEDS (1 : ℤ) 2 3 5 = -5 := by
    rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]
    norm_num
  have h6 : normEDS (1 : ℤ) 2 3 6 * 1 = -28 := by
    rw [show (6 : ℤ) = 2 * 3 by norm_num, normEDS_even]
    norm_num
    rw [h5]
    norm_num
  simpa using h6

example : normEDS (1 : ℤ) 2 3 7 = -67 := by
  have h5 : normEDS (1 : ℤ) 2 3 5 = -5 := by
    rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]
    norm_num
  rw [show (7 : ℤ) = 2 * 3 + 1 by norm_num, normEDS_odd]
  norm_num
  rw [h5]
  norm_num

/- ### B2 — the two recurrences

`normEDS` is not defined by the relation above — that would be circular. It is
defined by two *recurrences*, which are two of its slices (Zone C, Step 1). In
the form mathlib proves them for `normEDS`:

    normEDS (2 * m + 1)
      = normEDS (m + 2) * (normEDS m) ^ 3 - normEDS (m - 1) * (normEDS (m + 1)) ^ 3,
    normEDS (2 * m) * b
      = (normEDS (m - 1)) ^ 2 * normEDS m * normEDS (m + 2)
          - normEDS (m - 2) * normEDS m * (normEDS (m + 1)) ^ 2.

These are Ward's recurrences; with the five initial values they compute every
term. The first is division-free. The second is **not**: it determines
`normEDS (2 * m)` only after dividing by `b`, and over a general commutative
ring — or over the polynomial ring `R[X]` — that division does not exist. That
is the single formal problem the next subsection solves. -/

#check @normEDS_odd
#check @normEDS_even

/- ### B3 — `preNormEDS`: the same recursion in the other gauge

`preNormEDS b c d` trades the problem away: it anchors at `2 ↦ 1` and `4 ↦ d`
(instead of `2 ↦ b` and `4 ↦ d * b`), which makes the *even* recursion
division-free and pushes the parameter into the *odd* one, through two
`if Even m` factors:

    preNormEDS (2 * m)
      = (preNormEDS (m - 1)) ^ 2 * preNormEDS m * preNormEDS (m + 2)
          - preNormEDS (m - 2) * preNormEDS m * (preNormEDS (m + 1)) ^ 2,   -- clean
    preNormEDS (2 * m + 1)
      = preNormEDS (m + 2) * (preNormEDS m) ^ 3 * (if Even m then b else 1)
          - preNormEDS (m - 1) * (preNormEDS (m + 1)) ^ 3 * (if Even m then 1 else b).

So the two sequences trade which recurrence carries the `b`:

    normEDS:    odd clean,     even times `b`
    preNormEDS: even clean,    odd with `if Even m` factors

and they differ by exactly one factor of `b` on the even indices:

    normEDS b c d n = preNormEDS (b ^ 4) c d n * (if Even n then b else 1).

That identity is the *definition* of `normEDS` in mathlib. `normEDS` is not
defined by the recurrences at all — `preNormEDS` is. Concretely `preNormEDS'` is
the `ℕ`-indexed recursion: five base cases `0, 1, 2, 3, 4`, then a step matching
`n + 5` that halves the index and uses one of the two recurrences above; and
`preNormEDS` extends it to `ℤ` by `preNormEDS (-n) = -preNormEDS n`. For the
division polynomials the parameters are `(b, c, d) = (ψ₂, C Ψ₃, C preΨ₄)`: that
is Zone A's `ψ = normEDS ψ₂ (C Ψ₃) (C preΨ₄)`, and `preΨ` is the `mk`-shadow of
the same gauge with `ψ₂ ^ 4` replaced by `Ψ₂Sq ^ 2` (Zone D). -/

#check @preNormEDS'
#check @preNormEDS
#check @preNormEDS_even
#check @preNormEDS_odd

#print preNormEDS
#print normEDS

/-- The gauge relation, split by parity: odd indices agree with
`preNormEDS (b ^ 4)`, even indices differ by exactly one factor of `b`. -/
example (b c d : ℤ) (m : ℤ) :
    normEDS b c d (2 * m + 1) = preNormEDS (b ^ 4) c d (2 * m + 1) := by
  rw [normEDS, ite_eq_right m.not_even_two_mul_add_one, mul_one]

example (b c d : ℤ) (m : ℤ) :
    normEDS b c d (2 * m) = b * preNormEDS (b ^ 4) c d (2 * m) := by
  rw [normEDS, ite_eq_left (even_two_mul m), mul_comm]

/- ### B4 — why `b ^ 4`, and what the bookkeeping is for

The exponent `4` is forced, and the quartic homogeneity of B1 says why.
Substitute the gauge `W n = b ^ [n even] * P n` into the odd recurrence
`W (2m+1) = W (m+2) * (W m) ^ 3 - W (m-1) * (W (m+1)) ^ 3`: every index on the
right has the parity of `m`, and each term has four factors, so the right side
picks up `b ^ 4` when `m` is even and `1` when `m` is odd. That is precisely the
`if Even m then b else 1` of `preNormEDS_odd`, with the parameter of `preNormEDS`
set to `b ^ 4`. (The even recurrence is consistent with the same value: there
both sides pick up `b ^ 2`, and that `b ^ 2` cancels only when `b` is a
non-zero-divisor — the universal-ring step of Zone C, Step 4.)

The concrete consequence, computed. Same odd recursion, but `preNormEDS b c d`
carries one factor of `b` where `normEDS b c d` carries four. That is mathlib's
own "Implementation notes" paragraph in `EllipticDivisibilitySequence.lean`: the
recurrence is still Ward's, only the normalisation moved. -/

example (b c d : ℤ) : preNormEDS b c d 5 = d * b - c ^ 3 := by
  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, preNormEDS_odd]
  norm_num

example (b c d : ℤ) : normEDS b c d 5 = d * b ^ 4 - c ^ 3 := by
  rw [show (5 : ℤ) = 2 * 2 + 1 by norm_num, normEDS_odd]
  norm_num
  ring

/-- The even step is where the division would be. Over `ℤ` the honest statement
is the `* b` form, and the definition says where the `b` went: into the first
argument of `preNormEDS`. -/
example (b c d : ℤ) : normEDS b c d 6 = b * preNormEDS (b ^ 4) c d 6 := by
  rw [normEDS, ite_eq_left (by decide : Even (6 : ℤ)), mul_comm]

/-- Oddness `W (-n) = -W n` is part of the normalisation, so the sequence is
`ℤ`-indexed and there is no negative-index case split anywhere. -/
example (b c d n : ℤ) : normEDS b c d (-n) = -normEDS b c d n := by simp

/- ### B5 — one relation, not two recurrences

`IsEllipticSequence W` is the assertion that the *four-index* relator vanishes
on the `s = 0` slice (the `Rel₃` form of B1), and `IsEllipticNet W` — what
mathlib calls an elliptic net — is the full relator. That relator is a single
homogeneous quartic identity, and Ward's two recurrences are two of its
specialisations; the recurrences are a *description* of a structure, not the
structure itself. `atom` is the half-sum/half-difference product
`W ((a+b)/2) * W ((a-b)/2)`; `rel_eq` says the `atomRel` and `rel` forms are the
same statement under `(a,b,c,d) = (2p+s, 2q+s, 2r+s, s)`. The truncated halves
are why the parity bookkeeping of the recurrences disappears from the net
formulation: the atom is only meaningful when `a` and `b` have the same parity,
and the substitution guarantees it. -/

#check @IsEllipticNet
#check @IsEllipticSequence
#check @IsEllipticDvdSequence
#check @IsEllipticNet.atom
#check @IsEllipticNet.atomRel
#check @IsEllipticNet.rel
#check @IsEllipticNet.rel_eq
#check @IsEllipticNet.atomRel_eq

/-- Ward's relation for any normalised EDS: `Rel₃` at `r = 1`, one slice of the
net relation that Zone E turns into an invariant. -/
example (b c d m n : ℤ) :
    normEDS b c d (m + n) * normEDS b c d (m - n) =
      normEDS b c d (m + 1) * normEDS b c d (m - 1) * (normEDS b c d n) ^ 2 -
        normEDS b c d (n + 1) * normEDS b c d (n - 1) * (normEDS b c d m) ^ 2 := by
  have h := rel₃_of_isEllipticSequence (normEDS_isEllipticSequence b c d) m n 1
  simpa [Rel₃, normEDS_one] using h

/-- **The division polynomials are an elliptic sequence.** This is the fact the
whole layer exists to deliver, and mathlib still lists it as a `TODO` in its
module doc. The proof term is Zone C. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) : IsEllipticSequence W.ψ :=
  normEDS_isEllipticSequence W.ψ₂ (C W.Ψ₃) (C W.preΨ₄)

/-- Not only the `s = 0` slice: `ψ` is a full elliptic net. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (p q r s : ℤ) :
    net W.ψ p q r s = 0 :=
  net_normEDS W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) p q r s

/- ## Zone C — the one relation: from the recurrences to the net property

mathlib *defines* `normEDS` by the two recursions (in the `preNormEDS` shadow)
and leaves the elliptic-sequence property as a `TODO`. The port proves it. The
proof is four moves, all of them reusable, plus the upgrade to the full net.

**Step 1 — the recurrences are relator slices.** `Rel₃` is the `s = 0` relator
spelled out, `OddRec`/`EvenRec` are Ward's two recurrences, and the first three
port lemmas are pure `ring`: the recurrences *are* the relator at two specific
quadruples. -/

#check @FLTForHuman.Elliptic.Rel₃
#check @FLTForHuman.Elliptic.OddRec
#check @FLTForHuman.Elliptic.EvenRec
#check @FLTForHuman.Elliptic.rel₃_iff_oddRec
#check @FLTForHuman.Elliptic.rel₃_iff_evenRec
#check @FLTForHuman.Elliptic.rel₃_iff₄
#check @FLTForHuman.Elliptic.net_zero_iff_rel₃

example {R : Type*} [CommRing R] (W : ℤ → R) (m : ℤ) :
    Rel₃ W (m + 1) m 1 ↔ OddRec W m := rel₃_iff_oddRec W m

/- **Step 2 — normalise a relator.** A relator is only interesting on indices of
one parity, and `rel₄_transf` rewrites the relator at `(a,b,c,d)` to the relator
at four indices built from the midpoint `avg₄ = (a+b+c+d)/2`. Iterating that
descends a well-founded order on the largest index, and
`rel₄_of_anti_oddRec_evenRec` finishes by `Int.strongRec` with the recurrences as
base cases. `HaveSameParity₄`/`StrictAnti₄` are the side conditions of the
descent. FLT's names for `atom`/`atomRel`/`rel` are `addMulSub`/`rel₄`/`net`, and
`EllSequence.lean` keeps both spellings. -/

#check @FLTForHuman.Elliptic.HaveSameParity₄
#check @FLTForHuman.Elliptic.StrictAnti₄
#check @FLTForHuman.Elliptic.avg₄
#check @FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf
#check @FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec

/- **Step 3 — the headline.** Oddness and `W 0 = 0` are automatic for `normEDS`,
so the two recurrences alone give the elliptic-sequence property. The
`_of_mem_nonZeroDivisors` variant is the workhorse: it needs `b ∈ R⁰` for the
cancellation step, and the general statement instantiates it over a ring where
the cancellation is free (Step 4). -/

#check @FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec
#check @FLTForHuman.Elliptic.normEDS_isEllipticSequence
#check @FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors

/- **Step 4 — the universal trick.** To get `b ∈ R⁰` for free, prove the
statement over the universal ring `ℤ[B,C,D]`, where `B` is a non-zero-divisor,
and transport along `aeval (Param.rec b c d)`. This is the recurring proof
technique of the whole EDS layer (`invar₂_normEDS`, `redInvar_normEDS`, the
general complement all go the same way). `normEDS_two_three_two` — the identity
sequence is `normEDS 2 3 2` — is how the universal EDS is detected as non-zero:
specialise `B,C,D ↦ 2,3,2`, and a vanishing term would vanish in `id`. -/

#check @FLTForHuman.Elliptic.Param
#check @FLTForHuman.Elliptic.universalNormEDS
#check @FLTForHuman.Elliptic.normEDS_eq_aeval
#check @FLTForHuman.Elliptic.normEDS_two_three_two
#check @FLTForHuman.Elliptic.universalNormEDS_ne_zero
#check @FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors

/-- The identity EDS, live. -/
example : normEDS (2 : ℤ) 3 2 = id := normEDS_two_three_two

/- **Step 5 — rigidity.** An elliptic sequence with `W 1`, `W 2` invertible is
determined by its first four values, so the recurrences plus four numbers
*characterise* the sequence rather than merely generating one. That is what
makes `normEDS` canonical, and it is the reason the definition of `ψ` can be
moved between normalisations at will. Finally `net_of_isEllipticSequence`
upgrades the `s = 0` slice to the full net by evaluating at
`(2p+s, 2q+s, 2r+s, s)`, a quadruple whose entries always share a parity. -/

#check @FLTForHuman.Elliptic.isEllipticSequence_ext
#check @FLTForHuman.Elliptic.net_of_isEllipticSequence
#check @FLTForHuman.Elliptic.net_normEDS

/- ## Zone D — the univariate shadow: `R[X]` versus `R[X][Y]`

Why two worlds at all? One mathematical reason and one formal one.

**Mathematical.** The `x`-coordinate of `[n]P` is `Φ n (x) / ΨSq n (x)`, a
one-variable rational function: `Φ n` has degree `n²` and `ΨSq n` degree
`n² - 1`. The fibre count of `card_torsion_of_isAlgClosed` only ever looks at
`x`-fibres, so it only needs the univariate pair. The `y`-coordinate genuinely
needs the bivariate `ψ`.

**Formal.** Even over a field, `R[X][Y]` is not a Euclidean domain and `Y`
cannot be eliminated without passing to the coordinate ring; `R[X]` is Euclidean
as soon as `R` is a field, so `gcd`, coprimality and `natDegree` are available.
The `if Even n` factors in `ΨSq` and `Φ` are exactly what keeps the univariate
side closed under the EDS recurrence.

The two worlds are glued by `mk : R[X][Y] →+* R[W]`, the quotient map onto the
coordinate ring `R[W] = R[X,Y] / (Y² + a₁XY + a₃Y - X³ - a₂X² - a₄X - a₆)`. Four
mathlib lemmas say the dictionary is exact on the curve: -/

#check @WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq  -- (mk ψ₂) ^ 2 = mk (C Ψ₂Sq)
#check @WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq   -- (mk (Ψ n)) ^ 2 = mk (C (ΨSq n))
#check @WeierstrassCurve.Affine.CoordinateRing.mk_ψ       -- mk (ψ n) = mk (Ψ n)
#check @WeierstrassCurve.Affine.CoordinateRing.mk_φ       -- mk (φ n) = mk (C (Φ n))

/-- The first line of the dictionary, live. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ₂ ^ 2)
      = WeierstrassCurve.Affine.CoordinateRing.mk W (C W.Ψ₂Sq) :=
  WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq W

/-- Squaring that explains the strange parameter of `preΨ`. In Zone B, `ψ` is
`normEDS` run with `b = ψ₂`, so its internal `preNormEDS` sees `ψ₂ ^ 4`; on the
curve that is the shadow of `Ψ₂Sq ^ 2`, which is precisely the first argument of
`preΨ = preNormEDS (Ψ₂Sq ^ 2) Ψ₃ preΨ₄`. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    WeierstrassCurve.Affine.CoordinateRing.mk W (W.ψ₂ ^ 4)
      = WeierstrassCurve.Affine.CoordinateRing.mk W (C (W.Ψ₂Sq ^ 2)) := by
  rw [show (4 : ℕ) = 2 * 2 by norm_num, map_pow, pow_mul,
    WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq, ← map_pow, C_pow]

/- The univariate recurrences, and the identity that carries the curve's
geometry into the EDS bookkeeping. `preΨ₄ + Ψ₂Sq ^ 2 = invar * Ψ₃` with
`invar = 6X ^ 2 + b₂ * X + b₄` is a polynomial identity in `R[X]` valid in every
characteristic; on the curve it reads `d + b ^ 4 = invar * c`, i.e. it fixes the
invariant `(d + b ^ 4) / c` of the division-polynomial EDS as the polynomial
`invar`. -/

#check @WeierstrassCurve.preΨ_even
#check @WeierstrassCurve.preΨ_odd
#check @WeierstrassCurve.C_Ψ₂Sq
#check @WeierstrassCurve.Ψ₂Sq_eq
#check @WeierstrassCurve.Φ_neg
#check @FLTForHuman.Elliptic.invar
#check @FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq

/-- The invariant identity, live. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) :
    W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ := preΨ₄_add_Ψ₂Sq_sq W

/- Two things this import does **not** contain, so that a `#check` failure below
is not mistaken for a typo:

* the degree facts `natDegree (Φ n) = n ^ 2` and `natDegree (ΨSq n) = n ^ 2 - 1`
  live in mathlib's `DivisionPolynomial/Degree.lean`, one file above
  `Basic.lean`; the port consumes them through `TorsionCard.lean`. Try
  `#check @WeierstrassCurve.natDegree_Φ` here and it is an unknown identifier —
  that is this, not a mistake. (`CardNTorsion.lean`, Zone B, is where they are
  read.)
* the point-group bridge — `evalEval_ψ_sq`, `evalEval_φ`, `smul_x_eq`,
  `smul_eq_zero_of_ΨSq_eval_eq_zero` — is `FLTForHuman/Elliptic/Bridge.lean` and
  `TorsionCard.lean`, the other side of this story. It is read in
  `CardNTorsion.lean`, Zone D. -/

/- ## Zone E — what the layer is for: complement, invariant, `ωe`

The EDS vocabulary is not decoration. It is what makes the multiplication
formula `[n]P = (φ n / (ψ n) ^ 2, ω n / (ψ n) ^ 3)` hold over *every* commutative
ring — hence in every characteristic — when the textbook statement divides by
`ψ n` and by `2`. Two constructions do the work.

**The complement turns divisibility into a polynomial.** `W k ∣ W (n * k)` is
witnessed by a second sequence `complEDS`, with `W k * complEDS k n = W (n * k)`
and no division; the `2`-complement is `complEDS₂`, and the port's `ψc` is its
instance for `ψ`. `normEDS_mul_complEDS` is the port's general multiplicativity,
which mathlib only has for `n = 2`. -/

#check @complEDS₂
#check @normEDS_mul_complEDS₂
#check @normEDS_dvd_normEDS_two_mul
#check @FLTForHuman.Elliptic.normEDS_mul_complEDS
#check @FLTForHuman.Elliptic.normEDS_mul_complEDS_div
#check @FLTForHuman.Elliptic.ψc
#check @FLTForHuman.Elliptic.ψc_spec
#check @FLTForHuman.Elliptic.complEDSAux

/-- `ψ n` divides `ψ (2 * n)`, with `ψc n` as the explicit cofactor. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    W.ψ n ∣ W.ψ (2 * n) :=
  normEDS_dvd_normEDS_two_mul W.ψ₂ (C W.Ψ₃) (C W.preΨ₄) n

/-- The cofactor, named. -/
example {R : Type*} [CommRing R] (W : WeierstrassCurve R) (n : ℤ) :
    W.ψ n * ψc W n = W.ψ (2 * n) := ψc_spec W n

/- **The invariant makes `ω` a polynomial.** `invarNum`/`invarDenom` are a
numerator/denominator pair whose ratio is independent of the running index —
`invar_of_net`, whose only input is the net relation of Zone C. Because the pair
is projective, the ratio can be defined without ever forming a quotient, and
`invar₂_normEDS` computes it for `normEDS` as `(d + b ^ 4) / c`. The `red*` pair
is the same object with the factors `b`, `c` peeled off, so that it lands in
`R[X]` for the division polynomials. -/

#check @FLTForHuman.Elliptic.invarNum
#check @FLTForHuman.Elliptic.invarDenom
#check @FLTForHuman.Elliptic.invar_of_net
#check @FLTForHuman.Elliptic.invar_normEDS
#check @FLTForHuman.Elliptic.invar₂_normEDS
#check @FLTForHuman.Elliptic.redInvarNum
#check @FLTForHuman.Elliptic.redInvarDenom
#check @FLTForHuman.Elliptic.redInvar_normEDS
#check @FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul

/- **`ωe`: the `y`-numerator, defined without dividing by `2`.** `ωe_spec` is
the theorem that it deserves the name: `2 * ωe n = ψc n - a₁ * φ n * ψ n -
a₃ * (ψ n) ^ 3`, which is the classical `ω n` with the halving left in place. Over
a ring where `2` is invertible this pins `ωe` down; in characteristic `2` the
classical `ω` does not exist and this polynomial formula is the replacement.
This is the single service the EDS layer provides to FLT, and the reason it
cannot be simplified away (`math/025` §5). -/

#check @FLTForHuman.Elliptic.ωe
#check @FLTForHuman.Elliptic.ωe_spec
#check @FLTForHuman.Elliptic.two_mul_ωe

/- ## Zone F — things to poke at

* Compare the `#print preNormEDS` and `#print normEDS` bodies in B3:
  `preNormEDS` is `n.sign * preNormEDS' … n.natAbs`, and `normEDS` is
  `preNormEDS (b ^ 4) c d n * (if Even n then b else 1)` — the whole
  normalisation in one line. The `#print` of `ψ` in Zone A shows `ψ` is the
  `normEDS` case, and the `Φ`/`ΨSq` bodies show the same `if Even` branch on the
  univariate side.
* Change `5` to `7` and `9` in the two closed forms of Zone B. The odd recursion
  only ever reads backwards, so each one is a one-line `rw`/`ring`; the monomials
  multiply. For instance
  `normEDS b c d 7 = d * b ^ 4 * c ^ 3 - c ^ 6 - d ^ 3 * b ^ 4`, which is
  `normEDS_odd` at `m = 3` with `normEDS 5` substituted.
* Try to state the analogous closed form for `normEDS b c d 6` *without* the
  `preNormEDS` factor. In `ℤ` you cannot: the honest content of the even step is
  `W (2n) * W 2 = …`, and the `b` has to be carried, not cancelled. That is the
  point of Zone B, visible in a goal state.
* Swap the import for `FLTForHuman.Elliptic.TorsionCard` (about a second more)
  and the Zone D note becomes live: `#check @WeierstrassCurve.natDegree_Φ`,
  `#check @FLTForHuman.Elliptic.smul_x_eq`,
  `#check @FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero`. That is the
  bridge from these polynomials to the point group, and the subject of the
  companion worksheet `CardNTorsion.lean`.
* The `#check @FLTForHuman.Elliptic.ωe_spec` output prints the port's `CC`
  cast (`CC W.a₁`); `CC` is mathlib's `Polynomial.C` bundled as a ring
  homomorphism into the bivariate ring. Nothing mathematical hides there.
* Try `example : IsEllipticSequence (fun n : ℤ => n) := IsEllipticSequence.id`
  — the identity sequence is the trivial EDS, and `normEDS_two_three_two` is the
  statement that it is the `(b,c,d) = (2,3,2)` specialisation. -/

/- ## Zone Q — question log

Oldest first. Each entry: question, one-line answer, pointer to the zone edited.

* (2026-10-15) *Worksheet created.* — subject named: "the division polynomials
  and how the EDS works"; split out of `CardNTorsion.lean` Zone D, which now
  points here. No questions yet.
* (2026-10-15) **Q1.** *The polynomial approach is not very illuminating — is it
  only there so the count works in any characteristic?* — Half. Two answers.
  (i) Zone D: the univariate `Φ`/`ΨSq` are what supply the **degree** `n²`, i.e.
  the value of the count, and `R[X]` is where degree and `gcd` live — `R[X][Y]`
  is not a Euclidean domain. (ii) The EDS view of Zones B–C is the structural
  explanation the polynomial view hides: one quartic relator generates the whole
  zoo, Ward's recurrences are two of its slices, and the `if Even` factors are
  the price of doing it with no division rather than a feature of the field.
* (2026-10-15) **Q2.** *Why does `preΨ` run on `Ψ₂Sq ^ 2` and not on `Ψ₂Sq`?* —
  Because `preΨ` shadows `ψ = normEDS ψ₂ …`, whose internal `preNormEDS` sees
  `ψ₂ ^ 4`; on the curve `ψ₂ ^ 4` is `Ψ₂Sq ^ 2`. See the `ψ₂ ^ 4` example in
  Zone D.
* (2026-10-15) **Q3.** *How should I read `ψ n ^ 2` — is it `(ψ n) ^ 2` or
  `ψ (n ^ 2)`?* — Application binds tighter than `^`, so it is `(ψ n) ^ 2`, the
  intended `ψₙ²`; `ψ (n ^ 2)` needs the parentheses. See the new "Reading
  `ψ n ^ 2`" block at the end of Zone A, where `rfl` and a `normEDS`-at-`4`
  example separate the two readings and `#check` shows how Lean prints them
  back.
* (2026-10-15) **Q4.** *Follow-up on Q3: then the display
  `[n]P = (φ n / ψ n ^ 2, …)` in Zone E should read `(ψ n) ^ 2`.* — Agreed, and
  the same for every application under a power in Zones A, B, D and E. The
  parse block now also notes that Lean's printer *drops* the redundant
  parentheses, so a display copied out of a goal state reacquires the ambiguity;
  prose here spells the exponent out. See the corrected Zone E formula.
* (2026-10-15) **Q5.** *We use `normEDS`/`preNormEDS` but never introduced them —
  what are they?* — Zone B is now a five-part introduction: **B1** the object
  (Ward's relation, the normalisation, rigidity, examples), **B2** the two
  recurrences, **B3** `preNormEDS` as the other gauge and the identity
  `normEDS = preNormEDS (b ^ 4) … * (if Even n then b else 1)`, **B4** why the
  exponent is `4` (quartic homogeneity: four factors of `W` per term), **B5** the
  net reformulation. Writing B1 also caught an error in this file: the relator
  had been called "cubic"; it is *quartic*, which is exactly what makes `b ^ 4`
  the natural gauge rather than `b`. -/

end Play
