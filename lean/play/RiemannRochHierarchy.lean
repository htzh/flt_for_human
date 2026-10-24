/-
  PLAY · the Riemann–Roch statement hierarchy — places, divisors, ℓ / i / Ω
  ============================================================================

  Subject   the *shape* of the Riemann–Roch statements: rung 0 (`IsCurveOver`)
            through rung 4, the three spaces that are all called "dimension"
            (ℓ, i, Ω), the canonical divisor with its two genera, and the
            wrapper stack that shrinks the hypothesis list
  Reads     FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean,
            Defs/AdelicIndex.lean, Defs/CanonicalDivisor.lean,
            Defs/IsCurveOver.lean, Defs/RiemannRochRows.lean,
            RiemannRoch/Assembly.lean, Genus/Index.lean, Genus/Stichtenoth.lean,
            ResidueTheorem/RRAssembly.lean
  Pin       Definitions/Def_AlgebraicCurve_{Repartitions,AdelicIndex,
            DivisorClassGroup,IsCurveOver,RiemannRochRows,CanonicalDivisor}.lean
            and P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean,
            all at aa2d8b3
  Check     cd lean && lake env lean play/RiemannRochHierarchy.lean   (~5 s, oleans warm)
  Status    open
  Date      2026-10-23
  Intro     Riemann–Roch appears at half a dozen strengths — an inequality, an
            index formula, three duality forms, the identity — and they are not
            a chain but a small lattice with two directions. This sheet lays the
            rungs out as the port states them, separates the three things called
            "dimension" (ℓ(D), the adele quotient index i(D), the annihilator
            Ω(D)), pins the canonical divisor and the two genera, and ends at the
            four wrappers that carry the theorem down to a bare transcendental
            generator.

  Zone list
    A  the cast — places, divisors, and the curve axioms (rung 0)
    B  dimension, three times over — ℓ(D), i(D), Ω(D)
    C  the canonical divisor and the two genera
    D  the statement ladder — the Prop rows and the cheap arrows
    E  the wrapper stack — four headlines, and things to poke at
    Q  question log

  This is a worksheet, not library code: nothing globs `lean/play/`, the sheets
  are tracked, and it exists so that the ported statements can be read, poked at
  and questioned in the editor. Ground rules and workflow: `play/README.md`.
  The tracked note this sheet reads back is `base/023-riemann-roch-statement-hierarchy.md`.

  Provenance. The pin is `anthropics/fermats-last-theorem` at `aa2d8b3`; every
  module above is a `spec-pin:`-checked transcription of it, so a claim here can
  be traced without leaving this file:

    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_AdelicIndex.lean
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_Repartitions.lean
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_IsCurveOver.lean
    https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean

  Import cost. One import, `ResidueTheorem/RRAssembly`, the narrowest module that
  holds all five zones at once: it transitively carries `Defs/RiemannRochRows`,
  `RiemannRoch/Assembly`, `Genus/{Index,Stichtenoth}` and
  `IsCurveOver/{EssFiniteType,Transcendental}`, so the statement layer and the
  assembly arrows are read from a single olean cone.
  Warm it is ~5 s; the umbrella `Mathlib` is ~75 s, which is why R1 exists.
  Nothing here is a tree rebuild: `play/` is outside every `lean_lib` glob.
-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace Play

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/- ## Zone A — the cast

`F/K` is a field of one variable: `F` a finitely generated extension of `K` of
transcendence degree one. Nothing in the statements needs a curve that embeds
anywhere, or a smooth projective model; the geometric input is the discrete
valuation at each place, and the statements are phrased over the places. -/

/- A place is a proper valuation subring of `F` containing `K`. That is the
whole structure: the residue field, the valuation and the uniformiser are all
derived from it, in `Defs/Place.lean` and `Defs/CanonicalDivisor.lean`. -/
#print AlgebraicCurve.Place

-- `deg v = [κ(v) : K]` is the residue degree, and `ord` is the additive
-- valuation. Both are `def`s on the structure, so both reduce.
#check @AlgebraicCurve.Place.deg
#check @AlgebraicCurve.Place.ord

example (v : AlgebraicCurve.Place K F) : v.deg = Module.finrank K v.ResidueField := rfl

example (v : AlgebraicCurve.Place K F) (f : F) :
    v.ord f = -WithZero.log (v.adicValuation f) := rfl

/- `deg` is `finrank K` of the residue field — with the same junk-value caveat
as every `finrank`: if the residue extension is infinite, `deg` is `0`. That is
exactly what `FiniteResidue` rules out, and `IsCurveOver` supplies it at every
place (below). -/
#check @AlgebraicCurve.Place.ResidueField
#check @AlgebraicCurve.Place.FiniteResidue

/- A divisor is a finitely supported `Place → ℤ`. The port spells it as a
`Finsupp`, so "finite support" is by construction and `support` is available
for sums. -/
#check @AlgebraicCurve.Divisor

example : AlgebraicCurve.Divisor K F = (AlgebraicCurve.Place K F →₀ ℤ) := rfl

/- The degree is `∑_v D(v) · deg v`, packaged as an additive homomorphism — so
`deg 0 = 0` and `deg (D + E) = deg D + deg E` come for free. -/
#check @AlgebraicCurve.Divisor.degree
#check @AlgebraicCurve.Divisor.degree_single
#check @AlgebraicCurve.Divisor.degree_eq_sum

example (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=
  AlgebraicCurve.Divisor.degree_eq_sum D

example (D E : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.degree (D + E)
      = AlgebraicCurve.Divisor.degree D + AlgebraicCurve.Divisor.degree E := map_add _ _ _

/- Linear equivalence is `D` differing from `E` by a principal divisor, so the
class group and its degree-zero part are the two quotients below. -/
#check @AlgebraicCurve.Divisor.principal
#check @AlgebraicCurve.Divisor.degZero
#check @AlgebraicCurve.Pic
#check @AlgebraicCurve.Pic0

/- **Rung 0, first half.** `HasPrincipalDivisors` is the axiom that a nonzero
`f : F` has a divisor, and that this divisor has degree zero. The second
conjunct is what makes `deg` descend to divisor classes; without it `Pic0` would
be the wrong object. -/
#check @AlgebraicCurve.HasPrincipalDivisors

/- **Rung 0 — the curve.** `IsCurveOver` extends `HasPrincipalDivisors` with
the two remaining axioms: every residue extension is finite, and the Kähler
differentials are free of rank one over `F`. This is the standing hypothesis of
every rung above, and on its own it says nothing about `ℓ(D)` — the dimension
statements all need one of the inputs of E.2 as well. -/
#print AlgebraicCurve.IsCurveOver

example [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.HasPrincipalDivisors K F :=
  AlgebraicCurve.IsCurveOver.hasPrincipalDivisors

example [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) :
    Module.Finite K v.ResidueField :=
  AlgebraicCurve.IsCurveOver.finiteResidue v

example [AlgebraicCurve.IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=
  AlgebraicCurve.IsCurveOver.finrank_kaehler

/- Two consequences worth having in view, because the statements lean on them:
over an algebraically closed constant field every residue degree collapses to one
(so `deg D` is just the sum of the coefficients), and a single place of residue
degree one is then enough to make the constants the base field. -/
#check @AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed
#check @AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed

/- ### Q5 — what is `kaehler_free_rank_one`?

It is the third field of `IsCurveOver`, so it *is* part of the curve package:
`Ω ≅ F` as an `F`-vector space — the module of Kähler differentials is a *line*,
not a vector bundle of higher rank. `Free` is carried alongside the `finrank`
because on a non-free module `finrank` is junk, and because the pair is what
lets the port pick a generator and get `Nontrivial Ω` with no extra input.

Three readings, in increasing order of usefulness for this sheet:

* **the algebra.** `Ω[F⁄K]` is one-dimensional because `F/K` is one-variable and
  separably generated. The port makes that literal: under
  `[PerfectField K] [Algebra.EssFiniteType K F]`, `trdeg_le_one` bounds the
  transcendence degree using `finrank_kaehler_eq_card_of_separating'` and this
  field, and `one_le_trdeg` goes the other way (a *separable algebraic* `F/K`
  would have `Ω = 0`, contradiction). So `trdeg_eq_one_of_perfectField` is the
  translation: rank one **is** "transcendence degree one, separably generated",
  in the module language the divisor machinery can consume.

* **cotangent, not a canonical divisor.** `Ω[F⁄K]` is the cotangent space of
  `Spec F`, the *generic* point of the curve; its `F`-dual is the Zariski tangent
  space there. So yes — `finrank = 1` says the (co)tangent space at the generic
  point is one-dimensional, i.e. the curve is one-dimensional at the generic
  point, and the live example below is the dual statement. What it does **not**
  say:

  - that a differential's orders `ord_v(ω)` are finitely supported — that is
    `HasCanonicalDivisor`, and the port *derives* it for a curve over a perfect
    field (`hasCanonicalDivisor_of_isCurveOver`), not from rank one;
  - that there is a *canonical* differential — there is none: any nonzero `ω`
    will do, two of them differ by a nonzero function (`(ω)` is a line, so two
    generators are scalar multiples), and only the divisor *class* survives. The
    port chooses one with `Classical.choose` in `canonicalDivisorOf`.

* **at a place.** The local ring at `v` is a DVR, so `m_v / m_v²` is
  one-dimensional over `κ(v)` for free — that is exactly what `uniformizer` and
  `ord_uniformizer` (order one) encode, `m_v = (t_v)`. Rank one is the *global*
  statement; the local statement that matters for the divisor is
  `DCoordGenerates`, i.e. that the local cotangent vector `d t_v` generates the
  global `Ω` at this place. The two are independent: rank one is one field of
  `IsCurveOver`, `DCoordGenerates` is a hypothesis quantifier in every rung that
  mentions a canonical divisor. -/
#check @AlgebraicCurve.IsCurveOver.kaehler_free_rank_one
#check @AlgebraicCurve.IsCurveOver.finrank_kaehler
#check @AlgebraicCurve.IsCurveOver.instFreeKaehler
#check @AlgebraicCurve.IsCurveOver.instNontrivialKaehler
#check @AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField
#check @AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

/- The field itself: `Free` and `finrank = 1` as one conjunctive hypothesis. -/
example [AlgebraicCurve.IsCurveOver K F] :
    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=
  AlgebraicCurve.IsCurveOver.kaehler_free_rank_one

/- The tangent-space reading: the `F`-dual of the cotangent space at the generic
point is one-dimensional too — `Subspace.dual_finrank_eq` is the move. -/
example [AlgebraicCurve.IsCurveOver K F] :
    Module.finrank F (Module.Dual F Ω[F⁄K]) = 1 := by
  rw [Subspace.dual_finrank_eq, AlgebraicCurve.IsCurveOver.finrank_kaehler]

/- Line-ness used as such: two nonzero elements of a rank-one space are scalar
multiples. That is what makes `(ω)` insensitive to the choice of `ω` — the
divisor class, not the divisor. -/
#check @exists_smul_eq_of_finrank_eq_one

/- ## Zone B — dimension, three times over

The word "dimension" in Riemann–Roch is doing three jobs. All three are
dimensions of `K`-vector spaces attached to one divisor `D`, and the hierarchy
only makes sense once they are separated. -/

/- ### B.1 — functions with a pole bound: `ℓ(D)`

`L(D)` is the subspace of the *field* `F` cut out by local conditions: at each
place, `f` may have a pole only as far as `D` allows. -/
#check @AlgebraicCurve.riemannRochSpace
#check @AlgebraicCurve.LSpace
#check @AlgebraicCurve.ell

/- `ell` is `Module.finrank K`, hence a natural number by construction — and
`finrank` is `0` on an infinite-dimensional space. Read as a dimension, `ell D`
is honest only when `L(D)` is finite-dimensional, which for a function field is a
theorem and not part of the definition. The ladder carries that finiteness where
it needs it, and Zone E ends with the live demonstration of the junk value. -/

#check @AlgebraicCurve.mem_lSpace_iff
#check @AlgebraicCurve.mem_lSpace_iff_ord

/- The same membership, in valuation form: `-D v ≤ ord_v f`, with `f = 0`
carried separately because `ord` of zero is not a number. -/
example {D : AlgebraicCurve.Divisor K F} {f : F} :
    f ∈ AlgebraicCurve.LSpace D ↔
      f = 0 ∨ ∀ v : AlgebraicCurve.Place K F, -D v ≤ v.ord f :=
  AlgebraicCurve.mem_lSpace_iff_ord

#check @AlgebraicCurve.one_mem_lSpace_zero
#check @AlgebraicCurve.lSpace_mono

/- `L(D)` is monotone in `D`: a larger pole bound allows more functions. The
proof is one `le_trans` per place, which is why the ladder can shift divisors
around so freely. -/
example {D E : AlgebraicCurve.Divisor K F} (h : D ≤ E) :
    AlgebraicCurve.LSpace D ≤ AlgebraicCurve.LSpace E :=
  AlgebraicCurve.lSpace_mono h

/- ### B.2 — the same thing inside the adeles

This is the bridge the whole hierarchy crosses: `ℓ` is the dimension of a
subspace of the *adele space*, an intersection of a local condition with the
diagonal. -/
#check @AlgebraicCurve.adeleBdd
#check @AlgebraicCurve.adeleSpace
#check @AlgebraicCurve.globalSub
#check @AlgebraicCurve.diagonalHom

/- `A_F` is the union of the bounded pieces over all divisors — the restricted
product, in which every element is bounded below at all but finitely many
places. -/
#check @AlgebraicCurve.mem_adeleSpace_iff

/- `L(D)` is the diagonal copy of the bounded adeles at `D`, intersected with
the principal ones. This is the isomorphism quoted in the note as
`L(D) ≅ A_F(D) ∩ A⁰`. -/
#check @AlgebraicCurve.map_diagonal_lSpace

example (D : AlgebraicCurve.Divisor K F) :
    Submodule.map (AlgebraicCurve.diagonalHom K F) (AlgebraicCurve.LSpace D)
      = AlgebraicCurve.adeleBdd D ⊓ AlgebraicCurve.globalSub K F :=
  AlgebraicCurve.map_diagonal_lSpace D

/- Taking dimensions of that isomorphism: `ℓ(D) = dim_K (A_F(D) ∩ A⁰)`. The
`Nonempty (Place K F)` hypothesis is there because the diagonal is injective only
when there is a place to evaluate at. -/
#check @AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell

example [Nonempty (AlgebraicCurve.Place K F)] (D : AlgebraicCurve.Divisor K F) :
    Module.finrank K ↥(AlgebraicCurve.adeleBdd D ⊓ AlgebraicCurve.globalSub K F)
      = AlgebraicCurve.ell D :=
  AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell D

/- ### B.3 — the quotient: index of speciality and the genus

The complementary space is not another space of functions; it is a quotient,
taken *inside* the adeles. -/
#check @AlgebraicCurve.indexOfSpecialty
#check @AlgebraicCurve.adeleBddPrincipal
#check @AlgebraicCurve.indexOfSpecialty_eq

/- The same quotient, in the repartition model: `H1 D` is
`Repartitions / (A_F(D) + A⁰)`, and `i(D)` is its dimension. -/
#check @AlgebraicCurve.repartitions
#check @AlgebraicCurve.repartitionsOf
#check @AlgebraicCurve.principalRepartitions
#check @AlgebraicCurve.H1
#check @AlgebraicCurve.indexOfSpecialty_eq_finrank_H1

example [AlgebraicCurve.HasPrincipalDivisors K F] (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.indexOfSpecialty D = Module.finrank K (AlgebraicCurve.H1 D) :=
  AlgebraicCurve.indexOfSpecialty_eq_finrank_H1 D

/- The genus the adelic construction measures: `i(0)`, spelled in the repartition
model as the dimension of `H1 0`. Note what it is *not* — it is not `ell 0`, and it
does not mention differentials. -/
#check @AlgebraicCurve.genusFF

example : AlgebraicCurve.genusFF K F
    = Module.finrank K (AlgebraicCurve.H1 (0 : AlgebraicCurve.Divisor K F)) := rfl

/- ### B.4 — differentials: `Ω(D)` is the dual of that quotient

`Ω(D)` is defined by *annihilation*, not by a local condition: the functionals
on the adeles that vanish on `A_F(D) + A⁰`. The dimension equality
`dim Ω(D) = i(D)` is then the first-isomorphism-theorem duality, not a theorem
about differentials. -/
#check @AlgebraicCurve.omegaSpace
#check @AlgebraicCurve.omegaSpaceEquivIndexDual
#check @AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty

/- The annihilator of a subspace is the dual of the quotient — this is the whole
content of `dim Ω(D) = i(D)`, and it holds with no finiteness input. -/
example (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.omegaSpace D ≃ₗ[K]
      Module.Dual K (AlgebraicCurve.adeleSpace K F ⧸
        AlgebraicCurve.adeleBddPrincipal K F D) :=
  AlgebraicCurve.omegaSpaceEquivIndexDual D

example (D : AlgebraicCurve.Divisor K F) :
    Module.finrank K ↥(AlgebraicCurve.omegaSpace D)
      = AlgebraicCurve.indexOfSpecialty D :=
  AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty D

/- Two facts about the *global* space of differentials, both hypotheses of the
duality forms below rather than free gifts:

* `WeilDifferentialRankOne` — the Weil differentials (functionals vanishing on
  `A⁰`) form a one-dimensional `F`-space, generated by the functional attached
  to any nonzero `ω`. This is the "one rank-one condition" of Serre duality;
* `HasWeilCanonicalDivisor` — a differential has a *maximal* pole divisor `W`, in
  the sense that no larger divisor bounds it. Maximality is what makes the
  residue pairing hit every element of `Ω(D)`. -/
#check @AlgebraicCurve.weilDifferentialModule
#check @AlgebraicCurve.WeilDifferentialRankOne
#check @AlgebraicCurve.HasWeilCanonicalDivisor

/- The pairing that identifies the two sides of the ladder: fix `φ ∈ Ω(W)`,
multiply a function `g ∈ L(W - D)` into it, and read the result as an element of
`Ω(D)`. In the residue model this is exactly
`g ↦ (α ↦ ∑_v Res_v(α_v g ω))`. -/
#check @AlgebraicCurve.residuePairing

/- ## Zone C — the canonical divisor and the two genera

A canonical divisor is the divisor of a nonzero differential. Two differentials
differ by a nonzero function, so `K = (ω)` is well defined up to linear
equivalence — and that is all Riemann–Roch needs, since `ℓ` and `deg` are
insensitive to adding a principal divisor. -/

/- The local coordinate: a uniformiser at each place, of order exactly one. The
port has one `Place.uniformizer` (the `Classical.choose` of an irreducible of the
valuation subring), and `ord_uniformizer` is how it is ever characterised — the
definition itself is opaque. -/
#check @AlgebraicCurve.Place.uniformizer
#check @AlgebraicCurve.Place.ord_uniformizer
#check @AlgebraicCurve.Place.uniformizer_ne_zero

example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=
  v.ord_uniformizer

/- `dCoord` is `d t_v`, the Kähler differential of the uniformiser, and
`DCoordGenerates` is the hypothesis that it spans `Ω` at `v` — the local
coordinate exists. That class is what makes `ord_v(ω)` meaningful, and it is why
the rungs below carry `[∀ v, v.DCoordGenerates]` as a hypothesis rather than
deriving it. -/
#check @AlgebraicCurve.Place.dCoord
#check @AlgebraicCurve.Place.DCoordGenerates

/- The order of vanishing of a differential, read off its coefficient:
`ord_v(ω) = ord_v(ω / d t_v)`. The coefficient is `Classical.choose`-ed out of the
spanning hypothesis, and `differentialCoeff_unique` is what makes it an honest
function. -/
#check @AlgebraicCurve.Place.differentialCoeff
#check @AlgebraicCurve.Place.ordDifferential
#check @AlgebraicCurve.Place.gate_ordDifferential_dCoord

/- `HasCanonicalDivisor` is a *finiteness* statement, not a tautology:
`ord_v(ω)` must vanish at all but finitely many places, and the resulting
function on places must be a `Finsupp`. -/
#check @AlgebraicCurve.HasCanonicalDivisor
#check @AlgebraicCurve.canonicalDivisorOf
#check @AlgebraicCurve.canonicalDivisorOf_apply

example [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : AlgebraicCurve.Place K F) :
    AlgebraicCurve.canonicalDivisorOf hω v = v.ordDifferential ω :=
  AlgebraicCurve.canonicalDivisorOf_apply hω v

#check @AlgebraicCurve.canonicalClass
#check @AlgebraicCurve.genus

/- The genus the canonical divisor measures, as the port defines it:
`g = ⌊(deg K + 2) / 2⌋`, computed from a chosen differential. The `if` is honest —
if there is no nonzero differential the value is junk `0` — so the reachable form
is the `∃ ω₀` statement below. -/
#check @AlgebraicCurve.genus_eq_degree_div

/- **Two numbers follow, and they are why the genus is not an extra input.**
`deg K = 2g - 2`: take `D = K` in Riemann–Roch, use `ℓ(K) = g` and `ℓ(0) = 1`.
The port's `wkc_degree_canonicalDivisor_eq_of_weilMax` is exactly that computation.
And `ℓ(0) = 1` is the statement that the pole-free functions are the constants. -/
#check @AlgebraicCurve.ConstantsAreBase
#check @AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase
#check @ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax

/- `ConstantsAreBase` says `L(0)` *is* the image of `K`, not merely
one-dimensional — the stronger form, and the one that both identifies the two
genera and produces `deg K = 2g - 2`. -/
example (h : AlgebraicCurve.ConstantsAreBase K F) :
    AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F)
      = LinearMap.range (Algebra.linearMap K F) := h

/- The integer content of `deg K = 2g - 2`, with `ℓ(K) = g` substituted into
`ℓ(K) - ℓ(0) = deg K + 1 - g` and `ℓ(0) = 1`. -/
example {dK g : ℤ} (h : g - 1 = dK + 1 - g) : dK = 2 * g - 2 := by linarith

/- Two ways in to `ℓ(0) = 1`, either of which is a separate input: a place of
residue degree one suffices, and over an algebraically closed field every place
is one (rung 0 plus `IsAlgClosed`). -/
#check @AlgebraicCurve.constantsAreBase_of_deg_eq_one
#check @AlgebraicCurve.constantsAreBase_of_isAlgClosed

/- **The two genera agree** — a theorem, not a definition. One is read off a
single divisor, the other off the whole adelic quotient; the proof spends the
Riemann–Roch identity, the adelic duality form, and `ConstantsAreBase`. -/
#check @AlgebraicCurve.genus_eq_genusFF

example (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hWD : AlgebraicCurve.WeilDualityAdelic K F)
    (hC : AlgebraicCurve.ConstantsAreBase K F)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] :
    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F :=
  AlgebraicCurve.genus_eq_genusFF hRR hWD hC

/- The same identity from the other end: the canonical space has dimension `g`. -/
#check @AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch

/- ## Zone D — the statement ladder

Each rung is a `Prop`-valued `def` in `Defs/RiemannRochRows.lean`, printed below
in full so the instance arguments are visible. Two points about reading them:

* every rung quantifies `[IsCurveOver K F]`, `[HasCanonicalDivisor]` (and often
  `[∀ v, v.DCoordGenerates]`) *inside* itself, so a rung is a statement about a
  **class** of curves, not about one fixed `F/K`;
* the arrows between rungs are ordinary theorems about those `Prop`s, and they
  are cheap exactly where one statement is a rearrangement of another. -/

/- **Rung 1 — Riemann's inequality.** The half of Riemann–Roch that needs no
duality. It follows from the adelic description of `L(D)` and an index count. -/
#print AlgebraicCurve.RiemannInequality

/- **Rung 2 — the index formula.** Riemann–Roch with `i(D)` left as the quotient
dimension: the honest form, because it names what the second term is. -/
#print AlgebraicCurve.RiemannIndexFormula

/- **Rung 3a — the duality form, adelic.** `i(D) = ℓ(K - D)`, stated with the
canonical divisor named by a differential. -/
#print AlgebraicCurve.WeilDualityAdelic

/- **Rung 3c — the same, rearranged.** `ℓ(D) - ℓ(K - D) = deg D + 1 - g`. Given
the index formula this is exactly 3a moved across the equals sign; the port's
bridge is `weilDuality_of_riemannIndex_of_adelic`, and rung 4 then follows by
`functionFieldRiemannRoch_of_riemann_and_duality` (both in D.1). -/
#print AlgebraicCurve.WeilDuality

/- **Rung 3b — the differential version.** `dim Ω(D) = ℓ(K - D)`. This is the rung
Serre duality feeds: once the Weil differentials are one-dimensional over `F` and
the functional is maximal, the residue pairing `L(K - D) → Ω(D)` is an isomorphism
(D.2), and 3b is its dimension count. -/
#print AlgebraicCurve.WeilOmegaEllAgrees

/- **Rung 4 — Riemann–Roch.** The identity, with `K = (ω)` named by a differential
and both dimensions written as `ℓ`. -/
#print AlgebraicCurve.FunctionFieldRiemannRoch

/- ### D.1 — the cheap arrows

Two theorems, both `linarith`-shaped, and both part of the rung structure. -/
#check @AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality
#check @AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic

example (h : AlgebraicCurve.WeilDuality K F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality K F h

/- The integer shadow of `(3b) + index formula ⟹ (3a)`: the index is `dim Ω(D)`
by the annihilator duality, `dim Ω(D)` is `ℓ(K - D)` by rung 3b, hence the two
are equal. Two substitutions, no analysis. -/
example {i lk om : ℤ} (hAnn : om = i) (h3b : om = lk) : i = lk := by linarith

/- The integer shadow of `index formula ⟹ inequality`: the index is a dimension,
so it is nonnegative, and the inequality is the index formula solved for `ℓ`. -/
example {l i d g : ℤ} (hi : i = l - (d + 1 - g)) (h : 0 ≤ i) : d + 1 - g ≤ l := by
  linarith

/- The integer shadow of `(3a) + index formula ⟹ (3c)`: substitute
`i(D) = ℓ(K - D)` into `i(D) = ℓ(D) - (deg D + 1 - g)`. -/
example {l lk i d g : ℤ} (hi : i = l - (d + 1 - g)) (hd : i = lk) :
    l - lk = d + 1 - g := by
  linarith

/- Rung 2 implies rung 1, as a theorem about divisors. -/
#check @AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula

example [AlgebraicCurve.IsCurveOver K F]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (h : AlgebraicCurve.RiemannIndexFormula K F) (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.degree D + 1 - (AlgebraicCurve.genus K F : ℤ)
      ≤ (AlgebraicCurve.ell D : ℤ) :=
  AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula h D

/- ### D.2 — the duality, as a pairing

The analytic content of the ladder is the production of a *maximal* functional
and the bijectivity of the residue pairing it defines. Given rank-one-ness the
pairing is injective; given maximality it is surjective. Those two halves are
`residuePairing_injective` and `residuePairing_surjective`. -/
#check @AlgebraicCurve.residuePairing_injective
#check @AlgebraicCurve.residuePairing_surjective
#check @AlgebraicCurve.ResiduePairingSurjective
#check @AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula

example [AlgebraicCurve.HasPrincipalDivisors K F]
    (W D : AlgebraicCurve.Divisor K F)
    {φ : Module.Dual K ↥(AlgebraicCurve.adeleSpace K F)}
    (hφ : φ ∈ AlgebraicCurve.omegaSpace W) (hφ0 : φ ≠ 0) :
    Function.Injective ⇑(AlgebraicCurve.residuePairing K F W D hφ) :=
  AlgebraicCurve.residuePairing_injective W D hφ hφ0

/- Injectivity alone is the inequality direction: `ℓ(W - D) ≤ i(D)`. -/
#check @AlgebraicCurve.ell_sub_le_indexOfSpecialty

/- ### D.3 — the genus-existence axis

The rungs above all presuppose the existence of `g` in order to write it at all.
The port carries five ways of saying that one thing — finiteness of a quotient,
boundedness of `deg D - ℓ D`, attainment of the supremum at a witness, and the
Stichtenoth package (a place, `L(0)` finite, and a witness) — and proves
`StichtenothGenusExists ↔ IndexOfSpecialtyFinite` (the example below), whose two
directions are a finiteness transfer through the adele filtration and a
construction of the witness. -/
#check @AlgebraicCurve.IndexOfSpecialtyFinite
#check @AlgebraicCurve.RiemannGenusBounded
#check @AlgebraicCurve.RiemannGenusReachedAt
#check @AlgebraicCurve.RiemannGenusReached
#check @AlgebraicCurve.StichtenothGenusExists

example [AlgebraicCurve.IsCurveOver K F] [Nonempty (AlgebraicCurve.Place K F)]
    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))] :
    AlgebraicCurve.StichtenothGenusExists K F ↔ AlgebraicCurve.IndexOfSpecialtyFinite K F :=
  AlgebraicCurve.stichtenothGenusExists_iff_indexFinite

/- Rung 2 out of the genus. With a witness `D₀` in hand, `A_F` is already
`A_F(D ⊔ D₀) + A⁰` for every `D`, and a quotient chain computes the index — an
adelic computation with no differential in it. -/
#check @AlgebraicCurve.riemannIndexFormula_of_genusReached

/- The genus is nonnegative — not free, since it is `deg D₀ - ℓ(D₀) + 1` for a
witness `D₀` and `deg` can be negative. It spends `ConstantsAreBase`. -/
#check @AlgebraicCurve.stichtenothGenus_nonneg

/- ## Zone E — the wrapper stack, and things to poke at

For application the question is not which rung is true but **how few hypotheses**
the top can be stated under. Reading the four headlines in order says what each
layer of structure is worth: the content of the theorem is unchanged, but the
amount of structure the statement must be *handed* grows as the hypotheses
shrink. -/

/- **Wrapper 1 — from the K residue theorem.** The assembled statement: the
curve axioms, the canonical divisor, generation of `Ω` at every place, `F` finite
and separable over a rational function subfield, and `ResidueTheoremK`. Nothing is
derived here. -/
#check @AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed

/- **Wrapper 2 — over an algebraically closed field.** The residue theorem is
supplied rather than assumed: the hypothesis list loses it and keeps the curve
package. -/
#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed

/- **Wrapper 3 — from the curve over an algebraically closed field.** All three
residue-side hypotheses disappear, supplied unconditionally by the port's local
residue instance and by perfectness. -/
#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver

/- **Wrapper 4 — from a transcendental generator.** `K` algebraically closed,
`x ∈ F` transcendental, `F` finite over `K(x)` — everything else derived. This is
the form the theorem is actually consumed in: every FLT application has a specific
transcendental in hand and no desire to verify a curve package by hand. -/
#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental

example [IsAlgClosed K] {x : F} (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    AlgebraicCurve.FunctionFieldRiemannRoch K F :=
  AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfin

/- The genus-free form of the theorem, and the one to read next to rung 4:
Riemann–Roch with the *adelic* genus `genusFF` and an existential canonical
divisor, so no `HasCanonicalDivisor` appears in the statement at all. -/
#check @AlgebraicCurve.exists_weilCanonical_riemannRoch

/- ### E.1 — the K-route chain, in the port's own step order

Between the residue theorem and wrapper 1 sits the chain `wkc_*`: maximal
functional ⟹ `dim Ω(D) = ℓ(K - D)` ⟹ index formula ⟹ Riemann–Roch. Reading it
in this order is reading the note's §5 route diagram.

Note the namespace, because a `#check` will not find these under
`AlgebraicCurve`: the port's own section heading for this block is "The
`ModularCurve` assembly". The `wkc_` prefix is the pin's subject tag and survives
the port's rename (the pin's generated declarations carry a `p0n25_` part label in
front, which the port drops). -/
#check @ModularCurve.wkc_weilOfKaehlerK_single
#check @ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax
#check @ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax
#check @ModularCurve.wkc_riemannIndexFormula_of_weilMax
#check @ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK

/- ### E.2 — the four independent inputs

The hierarchy is a lattice rather than a chain because four of its inputs are
independent of the rest and of each other. Each has its own home, and each is
proved unconditionally in the port's setting (a curve over a perfect field,
essentially of finite type) — which is why the top of the stack is reachable at
all, and why a route that supplies one of them differently plugs in at one place.

* **the canonical divisor exists** — `HasCanonicalDivisor`, a finiteness statement
  about `ord_v(ω)`, proved from the Kähler rank and a separating transcendental;
* **the genus exists** — the axis of D.3: `StichtenothGenusExists`,
  `IndexOfSpecialtyFinite`, `RiemannGenusBounded`, `RiemannGenusReached`;
* **the constants are the base field** — `ConstantsAreBase`, needed both to
  identify `genus` with `genusFF` and to make `deg K = 2g - 2` come out; a function
  field with a larger constant field has `ℓ(0) > 1`;
* **`Ω` is generated at each place** — `DCoordGenerates`, the local-coordinate
  hypothesis that makes the divisor-valued `ord_v(ω)` meaningful. This one is
  local and per-place, unlike the other three, and it is *not* implied by
  `kaehler_free_rank_one` (Q5 in Zone A separates the two). -/

/- ### E.3 — things to poke at

* `ell` is `Module.finrank`, and `finrank` is `0` on an infinite-dimensional
  space. So `ell D` is *junk-zero* when `L(D)` is infinite-dimensional, and a row
  like `RiemannInequality` read without the finite-dimensionality supplied on the
  genus axis is then a statement about that junk value, not about dimensions.
  Live, with an infinite independent family and no `FiniteDimensional` anywhere:

    `LinearIndependent.finrank_eq_zero_of_infinite` turns the monomials of `K[X]`
    into `finrank = 0`.

* Delete `[HasCanonicalDivisor]` from an `example` above and watch which step
  survives: the `ell`-side statements survive, the ones that name `K = (ω)` do
  not. That is the sense in which the canonical divisor is a separate input.

* Replace `AlgebraicCurve.LSpace D` with `AlgebraicCurve.riemannRochSpace D` in
  any statement here: they are the same term, so nothing changes. `LSpace` is an
  `abbrev` for the repartition module's `riemannRochSpace`, and the ladder is
  written in the vocabulary of the adelic-index module (`LSpace`, `ell`).

* `genus` is defined with `(deg K + 2).toNat / 2`, so it is `0` in the unreachable
  branch. `genus_eq_degree_div` is the statement that some `ω₀` actually realises
  the `if`; without it, every `genus` lemma is conditional on a junk value.

* The rows quantify their instances, the wrappers do not. `#print` a row and a
  wrapper side by side: the row begins `∀ [IsCurveOver K F] ...`, the wrapper is
  an `example`-style statement about the `F/K` in scope with those instances
  already discharged. -/

/- The `finrank`-junk demonstration, live: an infinite-dimensional space has
`finrank` zero, because *there is* an infinite linearly independent family. This
is a property of `finrank`, not of the curve, and it is why the ladder has to
carry `FiniteDimensional` where it reads `ℓ` as a dimension. -/
example : Module.finrank K (Polynomial K) = 0 :=
  (Polynomial.basisMonomials K).linearIndependent.finrank_eq_zero_of_infinite

/- ## Zone Q — question log

Oldest first. Each entry: question, one-line answer, and a pointer to the zone
that was edited.

* (2026-10-23) *Worksheet created.* — no questions yet.
* (2026-10-23) **Q1.** In `ℓ(D) - ℓ(K - D) = deg D + 1 - g`, is the second term
  the dimension of a second space of functions? — No: it is the dimension of a
  space of *differentials*, which is the dual of a quotient of adeles, and the
  notation `ℓ(K - D)` names that dimension by the divisor it corresponds to. See
  B.4 and the `omegaSpaceEquivIndexDual` block.
* (2026-10-23) **Q2.** If `i(D)` and `dim Ω(D)` are the same number, why state
  both rungs? — Because the identification is *annihilator duality*, which holds
  with no finiteness input, while the step that identifies `dim Ω(D)` with
  `ℓ(K - D)` is the analytic content (Serre duality: rank-one plus maximality).
  Rung 3b prices the two separately. See D.2.
* (2026-10-23) **Q3.** Is `genus` a definition or a theorem on the adelic side? —
  Both are definitions: `genus` is `⌊(deg K + 2)/2⌋` from a chosen differential,
  `genusFF` is `dim H1(0)`. That they agree is `genus_eq_genusFF`, a theorem that
  spends Riemann–Roch, the duality form, and `ConstantsAreBase`. See Zone C.
* (2026-10-23) **Q4.** Why does every rung repeat `[IsCurveOver K F]` and friends
  instead of taking them as section variables? — So that the rung is a statement
  about a class of curves, portable to any `F/K`; the wrapper stack is where the
  instances are discharged for one given field. See E.2.
* (2026-10-23) **Q5.** What is `kaehler_free_rank_one` — that a canonical
  differential exists? that the tangent space is one-dimensional? Is it part of
  `IsCurveOver`? — It is the third field of `IsCurveOver` and says `Ω[F⁄K] ≅ F`:
  the differentials form a *line*. It makes a differential *available* but not
  *canonical* (only `(ω)`'s class is), it is the statement that the cotangent
  space at the generic point is one-dimensional (hence so is the tangent space),
  and it does **not** give the canonical divisor — that is `HasCanonicalDivisor`,
  derived separately over a perfect field, plus `DCoordGenerates` per place. See
  the Q5 block in Zone A.
-/


end Play
