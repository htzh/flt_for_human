/-
  PLAY · the card `n`-torsion theorem — `#E[n](K) = n²`
  ============================================================================

  Subject   the card `n`-torsion theorem: the `n`-torsion of an elliptic curve
            over an algebraically closed field has `n²` elements
  Reads     FLTForHuman/Elliptic/TorsionCard.lean, the port of the pinned FLT
            P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean,
            re-exported at
            Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean:8-9
            <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean#L8-L9>
  Check     cd lean && lake env lean play/CardNTorsion.lean   (~3 s, oleans warm)
  Status    open
  Date      2026-10-14
  Intro     The port's main theorem as the compiler sees it: over an
            algebraically closed field, the `n`-torsion of an elliptic curve
            has `n²` elements. The worksheet unpacks the statement, the fibre
            count, and the division-polynomial engine behind it.

  This is a worksheet, not library code: nothing globs `lean/play/`, the sheets
  are tracked, and it exists so that the ported statement can be read, poked at
  and questioned in the editor. Ground rules and workflow: `play/README.md`.

  Zones
    A  the statement, unpacked                                  (`#E[n] = n²`)
    B  the counting mechanism — why the count is not circular
    C  the assembly — prime powers, CRT, and the induction
    D  the engine — division polynomials and the bridge into the point group
    E  things to poke at
    Q  question log
-/
import FLTForHuman.Elliptic.TorsionCard

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

namespace Play

/- ## Zone A — the statement, unpacked -/

-- The port's main theorem as the compiler sees it. Everything below is a
-- reading of this one line.
#check @FLTForHuman.Elliptic.card_torsion_of_isAlgClosed

/-- The statement, re-spelled and closed by the port's theorem.

`W⁄K` is `Affine.baseChange W K`, so `(W⁄K).Point` is the group of `K`-points of
the base change of `W` — the pin writes it `W.toAffine⟮K⟯`, and the port's own
source spells it `(W.baseChange K).toAffine.Point`. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point n) = n ^ 2 :=
  FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W hn

/-- The two spellings of the point group are the same type. The port's internal
proofs use the long one; `rw` matches on the syntax, so a rewrite that targets
this type must be written the way the statement under use spells it. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] (W : WeierstrassCurve F) :
    (W⁄K).Point = (W.baseChange K).toAffine.Point := rfl

/- `[W.IsElliptic]` is nonsingularity of the curve: the discriminant is a unit.
This instance is the only place the geometry enters the count. -/
#check @isElliptic_iff

/- `Submodule.torsionBy ℤ M n` is the pin's local `nTorsion n`, and membership is
by definition `n • P = 0`. The port deletes the wrapper and uses mathlib's
submodule directly, which is why the pin's `solution` bridge disappears. -/
#check @Submodule.mem_torsionBy_iff

example {M : Type*} [AddCommGroup M] (n : ℕ) :
    {P : M | n • P = 0} = (Submodule.torsionBy ℤ M n : Set M) := by
  ext P
  simp

/-- The degenerate case of the induction, live: the `0`-torsion is *everything*
(`0 • P = 0` for every `P`), so the `n = 0` branch of `card_nTorsion` is not a
count at all — it is discharged because the hypothesis `(0 : K) ≠ 0` is false. -/
example {M : Type*} [AddCommGroup M] : Submodule.torsionBy ℤ M 0 = ⊤ := by
  ext P; simp

/-- The `1`-torsion is trivial, again with no algebraic-closedness needed. -/
example {M : Type*} [AddCommGroup M] : Submodule.torsionBy ℤ M 1 = ⊥ := by
  ext P; simp

/- ### Q1 — are `⊤`/`⊥` special, or just true and false?

They are *not* built into the elaborator: `⊤` and `⊥` are notation for `Top.top`
and `Bot.bot`, and ordinary typeclass resolution picks the instance from the
expected type — which is what "the UI specializes them to module" is. Same
notation, different term, decided by the type: -/
example {M : Type*} [AddCommGroup M] : (⊤ : Submodule ℤ M) = Top.top := rfl
example {M : Type*} [AddCommGroup M] : (⊥ : Submodule ℤ M) = Bot.bot := rfl

/-- The instances are not special either: `⊤`'s carrier is *defined* to be
`Set.univ` and `⊥`'s to be `{0}` (mathlib's `top_coe`/`bot_coe` are literally
`rfl`). Note `{0}`, not `∅`: a submodule must contain `0`, so the bottom of the
submodule lattice is the singleton — where for `Set M` it is the empty set. -/
example {M : Type*} [AddCommGroup M] : ((⊤ : Submodule ℤ M) : Set M) = Set.univ := rfl
example {M : Type*} [AddCommGroup M] : ((⊥ : Submodule ℤ M) : Set M) = {0} := rfl
example {M : Type*} [AddCommGroup M] : (⊥ : Set M) = ∅ := rfl

/-- Membership is definitional too, which is why `simp` gets these cheaply:
`x ∈ ⊤` *is* `True` (that is why mathlib states `Submodule.mem_top` as a bare
proposition, not an `↔`), and `x ∈ ⊥` *is* `x = 0` (`Submodule.mem_bot`). -/
example {M : Type*} [AddCommGroup M] (x : M) :
    (x ∈ (⊤ : Submodule ℤ M)) ↔ True := Iff.rfl
example {M : Type*} [AddCommGroup M] (x : M) :
    (x ∈ (⊥ : Submodule ℤ M)) ↔ x = 0 := Iff.rfl

/- But the two equations above at the *submodule* level are **not** `rfl` — and
neither is their carrier equality. `torsionBy ℤ M 0` is
`(DistribSMul.toLinearMap ℤ M 0).ker`: the kernel of the zero map, carrier
`{x | (0 : ℤ) • x = 0}`. That set is `univ` only by the `zero_smul` law of the
`Module` structure, and laws of a structure are fields and theorems, not
reductions — indeed `(0 : ℤ) • x = 0` is not `rfl` for an abstract `M`. So the
proof has to go through set extensionality and the `smul` laws: `ext x; simp`
(which is what the port's `card_nTorsion_one` does by hand, `rw [one_nsmul]`
before `AddSubgroup.card_bot`). Replace either proof term with `rfl` and it
fails; that is the whole content of this block. -/

/- The one lattice where top and bottom really are "true and false" by `rfl` is
`Prop` itself. -/
example : (⊤ : Prop) = True := rfl
example : (⊥ : Prop) = False := rfl

/- The hypothesis `(n : K) ≠ 0` is `char K ∤ n` and is *not* removable: the port
needs it separately for `n = 2`, and in characteristic `2` the `K`-points of
`E[2]` number `1` or `2`, not `4`. -/
#check @FLTForHuman.Elliptic.card_nTorsion_two

/- ## Zone B — the counting mechanism

`#E[n] = n²` looks like it should be proved by writing `E(K)` as a disjoint union
of fibres of `[n] : E(K) → E(K)` and computing `#E(K) = deg[n] · #E[n]`. That
would be circular: nothing here knows `#E(K)` is finite. The port breaks the
circle with facts about the map itself. -/

/- **`[n]` is onto** when `(n : K) ≠ 0` — separability, arithmetically: `Φ n` and
`ΨSq n` are coprime, so a root `x₀` of `Φ n − x_Q · ΨSq n` has `ΨSq n x₀ ≠ 0`, and
the multiplication formula `smul_x_eq` turns `x₀` into a preimage of `Q`.

(The pin's source lemma was stated for odd `n` only; the port generalised it,
the oddness was never used — see `logs/card-torsion-port.md` §2.) -/
#check @FLTForHuman.Elliptic.smul_surjective

/- **Every fibre has the cardinality of the torsion.** Pick one preimage `P₀` of
`Q`; translating by `P₀` is a bijection from `E[n]` to the fibre over `Q`. So the
fibre device needs a *point*, not a finite `E(K)`.

This is the covering-map picture: `[n]` is onto and every fibre is an
`E[n]`-torsor, so all fibres have the same cardinality — in the lattice model
`ℂ/Λ →^{×n} ℂ/Λ` the cover is infinite and each fibre is `(ℤ/n)²`, of size `n²`.
An infinite cover with a finite fibre is the ordinary case, and this is one; the
infinitude of `E(K)` is no obstruction. What the picture does not hand over is
the *value* of the common cardinality: that is the degree of `[n]`, the
isogeny-degree fact `deg[n] = n²`, which the port does not import. Nor, as a
formal matter, does `card_smul_fiber` give finiteness — it is an equation of
`Nat.card`s, and `Nat.card` of an infinite type is `0`; the count below is what
first makes `E[n]` finite here. So the next lemma supplies both the finiteness
and the value, by polynomial degree. -/
#check @FLTForHuman.Elliptic.card_smul_fiber

/- **The circle-breaker.** Some `Q` has `2 * n²` preimages counted over both
signs. That number is *two fibres*, not one: `{P | n • P = Q ∨ n • P = -Q}` is
the union of the fibre over `Q` and the fibre over `-Q`, so it holds `2 * #E[n]`
points. The right-hand `2 * n²` comes from the polynomial side, and the `n²` in
it is already the answer in disguise: `p := Φ n - C c · ΨSq n` has degree `n²`
(below), its `n²` roots are the admissible `x`-coordinates of preimages of `±Q`,
and each root carries exactly `2` points, the two `y`-values `y` and `negY x y`.
So `2 * #E[n] = 2 * n²` and the `2` cancels — it is the `P ↔ -P` pairing, not a
feature of `n = 2`.

(The `Odd n` hypothesis on this lemma is inherited and **unused**: the only
occurrence of `hodd` in its proof is the binder. The count is a polynomial
degree count and is true for every `n` with `n` invertible in `K`. Oddness is
consumed one step later, to exclude `Q = -Q`.) -/
#check @FLTForHuman.Elliptic.exists_double_fiber_card

/- The two degrees that supply the `n²`, so the `2` is visibly just the doubling
by the `y`-sign. -/
#check @WeierstrassCurve.natDegree_Φ    -- deg (Φ n) = n²
#check @WeierstrassCurve.natDegree_ΨSq  -- deg (ΨSq n) = n² - 1, so p has degree n²

/-- The end of the odd case, as pure arithmetic: two disjoint fibres of a
surjection, each of cardinality `c = #E[n]`, together hold `2 * n²` points, so
`c = n²`. -/
example {c n : ℕ} (h : 2 * c = 2 * n ^ 2) : c = n ^ 2 :=
  Nat.eq_of_mul_eq_mul_left (by norm_num) h

/- The other case, `Q = -Q`, is *not* killed by arithmetic but by parity: the two
fibres coincide, so `#E[n] = 2 * n²` is even, Cauchy's theorem
(`exists_prime_addOrderOf_dvd_card'`) produces an element of `E[n]` of additive
order `2`, and yet `addOrderOf_dvd_of_nsmul_eq_zero` says that order divides the
odd `n`. -/
#check @FLTForHuman.Elliptic.card_nTorsion_odd_fibers

/- ## Zone C — the assembly: prime powers and CRT

The whole argument is one induction on `n`, with the four branches that
`Nat.recOnPosPrimePosCoprime` demands: prime powers, `0`, `1`, and coprime
products. The port supplies the first and last and lets `simp` kill the middle
two. -/

#check @FLTForHuman.Elliptic.card_nTorsion      -- the assembled induction
#check @FLTForHuman.Elliptic.card_nTorsion_prime_pow  -- p ^ k
#check @FLTForHuman.Elliptic.card_nTorsion_prime  -- p, splitting out p = 2
#check @FLTForHuman.Elliptic.card_nTorsion_odd_fibers  -- odd n
#check @FLTForHuman.Elliptic.card_nTorsion_two  -- n = 2, needs (2 : K) ≠ 0
#check @FLTForHuman.Elliptic.card_nTorsion_one  -- n = 1
#check @FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime  -- CRT
#check @Nat.recOnPosPrimePosCoprime  -- the principle the four branches feed

/-- The CRT step on its own. Note what it does *not* assume: no `IsAlgClosed K`,
no `W.IsElliptic`. The Bézout identity `m * gcdA m n + n * gcdB m n = 1` splits
any `P` killed by `m * n` into its `m`- and `n`-parts, so the torsion decomposes
as a product — pure group theory. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    (W : WeierstrassCurve F) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point ((3 : ℤ) * 4)) =
      Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 3) *
        Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 4) :=
  FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime W (m := 3) (n := 4) (by norm_num)

/-- `#E[12] = 144`, assembled by hand the way `card_nTorsion`'s coprime branch
does it: split `12 = 3 · 4`, count each prime-power factor, multiply.

The char-sensitive part is real: `(3 : K) ≠ 0` and `(4 : K) ≠ 0` have to come
from somewhere, and here they come from `(12 : K) ≠ 0`, exactly as in the port's
`haK`/`hbK`. The intermediate `have`s are also where the two spellings of the
point group bite: the goal uses `(W⁄K).Point`, but the named steps use
`(W⁄K).toAffine.Point`, which is what `rw` can match. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve F) [W.IsElliptic] (hn : (12 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point 12) = 144 := by
  have h3 : (3 : K) ≠ 0 := by
    have h := hn
    rw [show (12 : K) = (3 : K) * 4 by norm_num] at h
    exact (mul_ne_zero_iff.mp h).1
  have h4 : (4 : K) ≠ 0 := by
    have h := hn
    rw [show (12 : K) = (3 : K) * 4 by norm_num] at h
    exact (mul_ne_zero_iff.mp h).2
  have hcr : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point ((3 : ℤ) * 4)) =
      Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (3 : ℤ)) *
        Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (4 : ℤ)) :=
    FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime W (m := 3) (n := 4) (by norm_num)
  have h3' : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (3 : ℤ)) = 3 ^ 2 :=
    FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W (n := 3) h3
  have h4' : Nat.card (Submodule.torsionBy ℤ (W⁄K).toAffine.Point (4 : ℤ)) = 4 ^ 2 :=
    FLTForHuman.Elliptic.card_torsion_of_isAlgClosed W (n := 4) h4
  rw [show (12 : ℤ) = (3 : ℤ) * 4 by norm_num, hcr, h3', h4']
  norm_num

/-- `n = 1` with no hypotheses at all beyond the algebra structure — the `1`
branch of the induction. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K]
    (W : WeierstrassCurve F) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point 1) = 1 :=
  FLTForHuman.Elliptic.card_nTorsion_one W

/-- A prime power: `#E[4] = 2 ^ (2 * 2) = 16`. This is the one place the
`Σ`-fibration over the `p`-torsion is consumed. -/
example {F K : Type*} [Field F] [Field K] [Algebra F K] [DecidableEq K] [IsAlgClosed K]
    (W : WeierstrassCurve F) [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (W⁄K).Point (2 ^ 2)) = 16 := by
  simpa using FLTForHuman.Elliptic.card_nTorsion_prime_pow W (p := 2) Nat.prime_two h2 2

/- ## Zone D — the engine: division polynomials and the bridge

Everything above is short; the height of the port is here. mathlib has the
division polynomials `Φ`, `ΨSq`, `ψ` and their degrees, but **no** API relating
them to the point group. The port's `FLTForHuman/Elliptic/` supplies that missing
bridge (re-derived from mathlib's elliptic-net theory), and it is the only
genuinely new mathematics in the effort (`logs/card-torsion-port.md` §1).

The polynomial side of this bridge — what `Φ`, `Ψ`, `ΨSq`, `ψ` are, the EDS
sequence `normEDS` that generates them, the net relation underneath, and the
complement/invariant/`ωe` layer — is a subject of its own and has its own
worksheet: `play/DivisionPolynomials.lean`. This zone is the point-side reading
of the same layer. -/

/- On a point, `(y − negY x y)²` is `Ψ₂Sq x` — the `2`-division polynomial
evaluated on a point of the curve. -/
#check @FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval

/- ### Q4 — what is `W.Φ`?

`Φ` is mathlib's `WeierstrassCurve.Φ`, the univariate `n`-division polynomial
`φₙ` (capital phi). It is not a primitive: it is assembled from the auxiliary
normalised-EDS sequence `preΨ` and the univariate `ΨSq`, which is the shadow of
`ψ n ^ 2` on the curve:

  `Φ n = X * ΨSq n - preΨ (n + 1) * preΨ (n - 1) * (if Even n then 1 else Ψ₂Sq)`

This is the univariate form of the classical bivariate
`φₙ = X · ψₙ² - ψₙ₊₁ · ψₙ₋₁`; `ΨSq n` is congruent to `ψ n ^ 2` in the coordinate
ring and `Φ n` to `φ n`. The `preΨ`/`if Even` bookkeeping is there so that `Φ n`
and `ΨSq n` can be defined, and their leading terms computed, without ring
division and without passing to the coordinate ring.

What it does is the `x`-coordinate of multiplication by `n`:
`x (n • P) = Φ n (x) / ΨSq n (x)`, with `ΨSq n (x) = 0` precisely when `n • P = 0`
(`smul_x_eq` and `smul_formula_or_zero` below). So `Φ / ΨSq` is the `x`-part of
`[n]`, a degree-`n²`-over-degree-`(n² - 1)` rational function on the `x`-line —
`Φ` is the degree of `[n]` made into a polynomial, and hence the source of the
`n²` in the theorem. -/
#check @WeierstrassCurve.Φ
#print WeierstrassCurve.Φ
#check @WeierstrassCurve.ΨSq
#check @WeierstrassCurve.preΨ
#check @WeierstrassCurve.ψ
#check @WeierstrassCurve.φ

/- The bridge: on a nonsingular point, `n • P = 0` implies `ΨSq n` vanishes there.
This is what turns every group-theoretic statement above into a polynomial
statement, and vice versa. -/
#check @FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero

/- Separability of `[n]`, used twice: `Φ n` and `ΨSq n` are coprime, and
consecutive `ΨSq` are coprime. The engine for both is the Wronskian. -/
#check @FLTForHuman.Elliptic.isCoprime_Φ_ΨSq
#check @FLTForHuman.Elliptic.isCoprime_ΨSq_succ
#check @FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero

/- The multiplication formula: from `(x, y)` to the `x`-coordinate of `n • P`, and
the resulting condition for `n • P = 0`. -/
#check @FLTForHuman.Elliptic.smul_x_eq
#check @FLTForHuman.Elliptic.smul_formula_or_zero

/- The finiteness input for the double-fibre trick: only finitely many `c` make
`Φ n − C c · ΨSq n` non-squarefree. -/
#check @FLTForHuman.Elliptic.finite_not_squarefree_fiber

/- The 2-torsion dictionary used by the `n = 2` branch: `P` is 2-torsion iff it
equals its own negative, i.e. iff `y = negY x y`. -/
#check @FLTForHuman.Elliptic.mem_nTorsion_two_iff

/- ## Zone E — things to poke at

* In `#E[12] = 144` above, change `12` to `6`, `9`, or a prime power. The
  coprime branch only fires when the split is actually coprime; `9 = 3 · 3` is
  the prime-power branch instead.
* Delete `hn : (12 : K) ≠ 0` and watch the `h3`/`h4` obligations become
  unprovable: that is the hypothesis doing its job.
* Delete `[IsAlgClosed K]` from `#E[12] = 144` and watch which step survives.
  The CRT step does not need it; the count does.
* Replace `[DecidableEq K]` by `Classical.decEq`'s `letI` and see that it is a
  structure on the point group, not a mathematical hypothesis.
* The next subject in this direction is the *classification*: the equivalence
  `ZMod n × ZMod n ≃+ E[n]` (`FLTForHuman/Elliptic/TorsionZMod.lean`), which
  descends from this theorem. It is a different subject, so a different
  worksheet; its module now imports in ~5.5 s warm, so asking for it is cheap
  (ground rule R1). -/

/- ## Zone Q — question log

Oldest first. Each entry: question, one-line answer, and a pointer to the zone
that was edited.

* (2026-10-14) *Worksheet created.* — no questions yet.
* (2026-10-14) **Q1.** Are `⊤`/`⊥` special (the UI specializes them to module),
  or are they just true and false, `rfl`? — They are plain notation for
  `Top.top`/`Bot.bot` resolved by the expected type; their carriers *are*
  `univ`/`{0}` by `rfl` and membership in them is definitional, but the
  submodule-level equations are not, because `torsionBy 0` is a kernel and
  `zero_smul`/`one_smul` are structure laws. See the Q1 block in Zone A.
* (2026-10-14) **Q2.** With the fibre count as a covering map, isn't `2 * n²`
  only true for `n = 2` — an even count is too low to reach `n²`? — No: `2 * n²`
  is the size of the union of *two* fibres (over `Q` and `-Q`), i.e.
  `2 * #E[n]`, and the `2` on the right is the `y`/`negY` pairing; `n²` is
  already there as `deg (Φ n)`. The oddness on the lemma is unused. See the
  circle-breaker block in Zone B.
* (2026-10-14) **Q3.** *Correction:* a covering map can have an infinite cover
  and a finite fibre — that is exactly the case here. — Conceded; the Zone B
  paragraph was wrong to blame the infinitude of `E(K)`. The covering picture
  gives constancy of the fibre (`card_smul_fiber`), while the gap is the
  *value* (`deg[n] = n²`, isogeny degree) and, formally, finiteness. See the
  corrected `card_smul_fiber` block in Zone B.
* (2026-10-14) **Q4.** What is `W.Φ`? — mathlib's univariate `n`-division
  polynomial `φₙ`, assembled from `preΨ`/`ΨSq`; it is the numerator of
  `x (n • P)`, so its degree `n²` is the degree of `[n]` and the source of the
  theorem's `n²`. See the Q4 block in Zone D. -/

end Play
