window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["RiemannRochHierarchy"] = {
  "slug": "RiemannRochHierarchy",
  "file": "lean/play/RiemannRochHierarchy.lean",
  "title": "the Riemann–Roch statement hierarchy",
  "tagline": "places, divisors, ℓ / i / Ω",
  "subject": "the *shape* of the Riemann–Roch statements: rung 0 (`IsCurveOver`) through rung 4, the three spaces that are all called \"dimension\" (ℓ, i, Ω), the canonical divisor with its two genera, and the wrapper stack that shrinks the hypothesis list",
  "intro": "Riemann–Roch appears at half a dozen strengths — an inequality, an index formula, three duality forms, the identity — and they are not a chain but a small lattice with two directions. This sheet lays the rungs out as the port states them, separates the three things called \"dimension\" (ℓ(D), the adele quotient index i(D), the annihilator Ω(D)), pins the canonical divisor and the two genera, and ends at the four wrappers that carry the theorem down to a bare transcendental generator.",
  "reads": "FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean, Defs/AdelicIndex.lean, Defs/CanonicalDivisor.lean, Defs/IsCurveOver.lean, Defs/RiemannRochRows.lean, RiemannRoch/Assembly.lean, Genus/Index.lean, Genus/Stichtenoth.lean, ResidueTheorem/RRAssembly.lean",
  "pin": "Definitions/Def_AlgebraicCurve_{Repartitions,AdelicIndex, DivisorClassGroup,IsCurveOver,RiemannRochRows,CanonicalDivisor}.lean and P2M/Sol/S_AlgebraicCurve_functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed.lean, all at aa2d8b3",
  "check": "cd lean && lake env lean play/RiemannRochHierarchy.lean   (~5 s, oleans warm)",
  "status": "open",
  "date": "2026-10-23",
  "imports": ["FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly"],
  "opens": ["KaehlerDifferential"],
  "namespace": "Play",
  "zones": [{"id":"A","title":"the cast"},{"id":"B","title":"dimension, three times over"},{"id":"C","title":"the canonical divisor and the two genera"},{"id":"D","title":"the statement ladder"},{"id":"E","title":"the wrapper stack, and things to poke at"},{"id":"Q","title":"question log"}],
  "blocks": [
    {
      "type": "code",
      "text": "import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
      "zone": null
    },
    {
      "type": "code",
      "text": "set_option autoImplicit false",
      "zone": null
    },
    {
      "type": "code",
      "text": "noncomputable section",
      "zone": null
    },
    {
      "type": "code",
      "text": "open KaehlerDifferential",
      "zone": null
    },
    {
      "type": "code",
      "text": "namespace Play",
      "zone": null
    },
    {
      "type": "code",
      "text": "variable {K F : Type*} [Field K] [Field F] [Algebra K F]",
      "zone": null
    },
    {
      "type": "prose",
      "md": "`F/K` is a field of one variable: `F` a finitely generated extension of `K` of\ntranscendence degree one. Nothing in the statements needs a curve that embeds\nanywhere, or a smooth projective model; the geometric input is the discrete\nvaluation at each place, and the statements are phrased over the places. ",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " A place is a proper valuation subring of `F` containing `K`. That is the\nwhole structure: the residue field, the valuation and the uniformiser are all\nderived from it, in `Defs/Place.lean` and `Defs/CanonicalDivisor.lean`. ",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.Place",
      "zone": "A",
      "name": "AlgebraicCurve.Place",
      "display": "AlgebraicCurve.Place",
      "card": "AlgebraicCurve.Place"
    },
    {
      "type": "prose",
      "md": "`deg v = [κ(v) : K]` is the residue degree, and `ord` is the additive\nvaluation. Both are `def`s on the structure, so both reduce.",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.deg",
      "zone": "A",
      "name": "AlgebraicCurve.Place.deg",
      "display": "@AlgebraicCurve.Place.deg",
      "card": "AlgebraicCurve.Place.deg"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord",
      "display": "@AlgebraicCurve.Place.ord",
      "card": "AlgebraicCurve.Place.ord"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) : v.deg = Module.finrank K v.ResidueField := rfl",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (f : F) :\n    v.ord f = -WithZero.log (v.adicValuation f) := rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " `deg` is `finrank K` of the residue field — with the same junk-value caveat\nas every `finrank`: if the residue extension is infinite, `deg` is `0`. That is\nexactly what `FiniteResidue` rules out, and `IsCurveOver` supplies it at every\nplace (below). ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ResidueField",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ResidueField",
      "display": "@AlgebraicCurve.Place.ResidueField",
      "card": "AlgebraicCurve.Place.ResidueField"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.FiniteResidue",
      "zone": "A",
      "name": "AlgebraicCurve.Place.FiniteResidue",
      "display": "@AlgebraicCurve.Place.FiniteResidue",
      "card": "AlgebraicCurve.Place.FiniteResidue"
    },
    {
      "type": "prose",
      "md": " A divisor is a finitely supported `Place → ℤ`. The port spells it as a\n`Finsupp`, so \"finite support\" is by construction and `support` is available\nfor sums. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor",
      "display": "@AlgebraicCurve.Divisor",
      "card": "AlgebraicCurve.Divisor"
    },
    {
      "type": "example",
      "text": "example : AlgebraicCurve.Divisor K F = (AlgebraicCurve.Place K F →₀ ℤ) := rfl",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " The degree is `∑_v D(v) · deg v`, packaged as an additive homomorphism — so\n`deg 0 = 0` and `deg (D + E) = deg D + deg E` come for free. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor.degree",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor.degree",
      "display": "@AlgebraicCurve.Divisor.degree",
      "card": "AlgebraicCurve.Divisor.degree"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor.degree_single",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor.degree_single",
      "display": "@AlgebraicCurve.Divisor.degree_single",
      "card": "AlgebraicCurve.Divisor.degree_single"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor.degree_eq_sum",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor.degree_eq_sum",
      "display": "@AlgebraicCurve.Divisor.degree_eq_sum",
      "card": "AlgebraicCurve.Divisor.degree_eq_sum"
    },
    {
      "type": "example",
      "text": "example (D : AlgebraicCurve.Divisor K F) :\n    AlgebraicCurve.Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=\n  AlgebraicCurve.Divisor.degree_eq_sum D",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (D E : AlgebraicCurve.Divisor K F) :\n    AlgebraicCurve.Divisor.degree (D + E)\n      = AlgebraicCurve.Divisor.degree D + AlgebraicCurve.Divisor.degree E := map_add _ _ _",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " Linear equivalence is `D` differing from `E` by a principal divisor, so the\nclass group and its degree-zero part are the two quotients below. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor.principal",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor.principal",
      "display": "@AlgebraicCurve.Divisor.principal",
      "card": "AlgebraicCurve.Divisor.principal"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Divisor.degZero",
      "zone": "A",
      "name": "AlgebraicCurve.Divisor.degZero",
      "display": "@AlgebraicCurve.Divisor.degZero",
      "card": "AlgebraicCurve.Divisor.degZero"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Pic",
      "zone": "A",
      "name": "AlgebraicCurve.Pic",
      "display": "@AlgebraicCurve.Pic",
      "card": "AlgebraicCurve.Pic"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Pic0",
      "zone": "A",
      "name": "AlgebraicCurve.Pic0",
      "display": "@AlgebraicCurve.Pic0",
      "card": "AlgebraicCurve.Pic0"
    },
    {
      "type": "prose",
      "md": " **Rung 0, first half.** `HasPrincipalDivisors` is the axiom that a nonzero\n`f : F` has a divisor, and that this divisor has degree zero. The second\nconjunct is what makes `deg` descend to divisor classes; without it `Pic0` would\nbe the wrong object. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasPrincipalDivisors",
      "zone": "A",
      "name": "AlgebraicCurve.HasPrincipalDivisors",
      "display": "@AlgebraicCurve.HasPrincipalDivisors",
      "card": "AlgebraicCurve.HasPrincipalDivisors"
    },
    {
      "type": "prose",
      "md": " **Rung 0 — the curve.** `IsCurveOver` extends `HasPrincipalDivisors` with\nthe two remaining axioms: every residue extension is finite, and the Kähler\ndifferentials are free of rank one over `F`. This is the standing hypothesis of\nevery rung above, and on its own it says nothing about `ℓ(D)` — the dimension\nstatements all need one of the inputs of E.2 as well. ",
      "zone": "A"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.IsCurveOver",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver",
      "display": "AlgebraicCurve.IsCurveOver",
      "card": "AlgebraicCurve.IsCurveOver"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] :\n    AlgebraicCurve.HasPrincipalDivisors K F :=\n  AlgebraicCurve.IsCurveOver.hasPrincipalDivisors",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) :\n    Module.Finite K v.ResidueField :=\n  AlgebraicCurve.IsCurveOver.finiteResidue v",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=\n  AlgebraicCurve.IsCurveOver.finrank_kaehler",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " Two consequences worth having in view, because the statements lean on them:\nover an algebraically closed constant field every residue degree collapses to one\n(so `deg D` is just the sum of the coefficients), and a single place of residue\ndegree one is then enough to make the constants the base field. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed",
      "display": "@AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed",
      "card": "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed",
      "display": "@AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed",
      "card": "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed"
    },
    {
      "type": "prose",
      "md": " ### Q5 — what is `kaehler_free_rank_one`?\n\nIt is the third field of `IsCurveOver`, so it *is* part of the curve package:\n`Ω ≅ F` as an `F`-vector space — the module of Kähler differentials is a *line*,\nnot a vector bundle of higher rank. `Free` is carried alongside the `finrank`\nbecause on a non-free module `finrank` is junk, and because the pair is what\nlets the port pick a generator and get `Nontrivial Ω` with no extra input.\n\nThree readings, in increasing order of usefulness for this sheet:\n\n* **the algebra.** `Ω[F⁄K]` is one-dimensional because `F/K` is one-variable and\n  separably generated. The port makes that literal: under\n  `[PerfectField K] [Algebra.EssFiniteType K F]`, `trdeg_le_one` bounds the\n  transcendence degree using `finrank_kaehler_eq_card_of_separating'` and this\n  field, and `one_le_trdeg` goes the other way (a *separable algebraic* `F/K`\n  would have `Ω = 0`, contradiction). So `trdeg_eq_one_of_perfectField` is the\n  translation: rank one **is** \"transcendence degree one, separably generated\",\n  in the module language the divisor machinery can consume.\n\n* **cotangent, not a canonical divisor.** `Ω[F⁄K]` is the cotangent space of\n  `Spec F`, the *generic* point of the curve; its `F`-dual is the Zariski tangent\n  space there. So yes — `finrank = 1` says the (co)tangent space at the generic\n  point is one-dimensional, i.e. the curve is one-dimensional at the generic\n  point, and the live example below is the dual statement. What it does **not**\n  say:\n\n  - that a differential's orders `ord_v(ω)` are finitely supported — that is\n    `HasCanonicalDivisor`, and the port *derives* it for a curve over a perfect\n    field (`hasCanonicalDivisor_of_isCurveOver`), not from rank one;\n  - that there is a *canonical* differential — there is none: any nonzero `ω`\n    will do, two of them differ by a nonzero function (`(ω)` is a line, so two\n    generators are scalar multiples), and only the divisor *class* survives. The\n    port chooses one with `Classical.choose` in `canonicalDivisorOf`.\n\n* **at a place.** The local ring at `v` is a DVR, so `m_v / m_v²` is\n  one-dimensional over `κ(v)` for free — that is exactly what `uniformizer` and\n  `ord_uniformizer` (order one) encode, `m_v = (t_v)`. Rank one is the *global*\n  statement; the local statement that matters for the divisor is\n  `DCoordGenerates`, i.e. that the local cotangent vector `d t_v` generates the\n  global `Ω` at this place. The two are independent: rank one is one field of\n  `IsCurveOver`, `DCoordGenerates` is a hypothesis quantifier in every rung that\n  mentions a canonical divisor. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "display": "@AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "card": "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.finrank_kaehler",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.finrank_kaehler",
      "display": "@AlgebraicCurve.IsCurveOver.finrank_kaehler",
      "card": "AlgebraicCurve.IsCurveOver.finrank_kaehler"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.instFreeKaehler",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.instFreeKaehler",
      "display": "@AlgebraicCurve.IsCurveOver.instFreeKaehler",
      "card": "AlgebraicCurve.IsCurveOver.instFreeKaehler"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "display": "@AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "card": "AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "zone": "A",
      "name": "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "display": "@AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "card": "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "zone": "A",
      "name": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "display": "@AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "card": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver"
    },
    {
      "type": "prose",
      "md": " The field itself: `Free` and `finrank = 1` as one conjunctive hypothesis. ",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] :\n    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=\n  AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " The tangent-space reading: the `F`-dual of the cotangent space at the generic\npoint is one-dimensional too — `Subspace.dual_finrank_eq` is the move. ",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] :\n    Module.finrank F (Module.Dual F Ω[F⁄K]) = 1 := by\n  rw [Subspace.dual_finrank_eq, AlgebraicCurve.IsCurveOver.finrank_kaehler]",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " Line-ness used as such: two nonzero elements of a rank-one space are scalar\nmultiples. That is what makes `(ω)` insensitive to the choice of `ω` — the\ndivisor class, not the divisor. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @exists_smul_eq_of_finrank_eq_one",
      "zone": "A",
      "name": "exists_smul_eq_of_finrank_eq_one",
      "display": "@exists_smul_eq_of_finrank_eq_one",
      "card": "exists_smul_eq_of_finrank_eq_one"
    },
    {
      "type": "prose",
      "md": "The word \"dimension\" in Riemann–Roch is doing three jobs. All three are\ndimensions of `K`-vector spaces attached to one divisor `D`, and the hierarchy\nonly makes sense once they are separated. ",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B.1 — functions with a pole bound: `ℓ(D)`\n\n`L(D)` is the subspace of the *field* `F` cut out by local conditions: at each\nplace, `f` may have a pole only as far as `D` allows. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.riemannRochSpace",
      "zone": "B",
      "name": "AlgebraicCurve.riemannRochSpace",
      "display": "@AlgebraicCurve.riemannRochSpace",
      "card": "AlgebraicCurve.riemannRochSpace"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.LSpace",
      "zone": "B",
      "name": "AlgebraicCurve.LSpace",
      "display": "@AlgebraicCurve.LSpace",
      "card": "AlgebraicCurve.LSpace"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ell",
      "zone": "B",
      "name": "AlgebraicCurve.ell",
      "display": "@AlgebraicCurve.ell",
      "card": "AlgebraicCurve.ell"
    },
    {
      "type": "prose",
      "md": " `ell` is `Module.finrank K`, hence a natural number by construction — and\n`finrank` is `0` on an infinite-dimensional space. Read as a dimension, `ell D`\nis honest only when `L(D)` is finite-dimensional, which for a function field is a\ntheorem and not part of the definition. The ladder carries that finiteness where\nit needs it, and Zone E ends with the live demonstration of the junk value. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.mem_lSpace_iff",
      "zone": "B",
      "name": "AlgebraicCurve.mem_lSpace_iff",
      "display": "@AlgebraicCurve.mem_lSpace_iff",
      "card": "AlgebraicCurve.mem_lSpace_iff"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.mem_lSpace_iff_ord",
      "zone": "B",
      "name": "AlgebraicCurve.mem_lSpace_iff_ord",
      "display": "@AlgebraicCurve.mem_lSpace_iff_ord",
      "card": "AlgebraicCurve.mem_lSpace_iff_ord"
    },
    {
      "type": "prose",
      "md": " The same membership, in valuation form: `-D v ≤ ord_v f`, with `f = 0`\ncarried separately because `ord` of zero is not a number. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example {D : AlgebraicCurve.Divisor K F} {f : F} :\n    f ∈ AlgebraicCurve.LSpace D ↔\n      f = 0 ∨ ∀ v : AlgebraicCurve.Place K F, -D v ≤ v.ord f :=\n  AlgebraicCurve.mem_lSpace_iff_ord",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.one_mem_lSpace_zero",
      "zone": "B",
      "name": "AlgebraicCurve.one_mem_lSpace_zero",
      "display": "@AlgebraicCurve.one_mem_lSpace_zero",
      "card": "AlgebraicCurve.one_mem_lSpace_zero"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.lSpace_mono",
      "zone": "B",
      "name": "AlgebraicCurve.lSpace_mono",
      "display": "@AlgebraicCurve.lSpace_mono",
      "card": "AlgebraicCurve.lSpace_mono"
    },
    {
      "type": "prose",
      "md": " `L(D)` is monotone in `D`: a larger pole bound allows more functions. The\nproof is one `le_trans` per place, which is why the ladder can shift divisors\naround so freely. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example {D E : AlgebraicCurve.Divisor K F} (h : D ≤ E) :\n    AlgebraicCurve.LSpace D ≤ AlgebraicCurve.LSpace E :=\n  AlgebraicCurve.lSpace_mono h",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B.2 — the same thing inside the adeles\n\nThis is the bridge the whole hierarchy crosses: `ℓ` is the dimension of a\nsubspace of the *adele space*, an intersection of a local condition with the\ndiagonal. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.adeleBdd",
      "zone": "B",
      "name": "AlgebraicCurve.adeleBdd",
      "display": "@AlgebraicCurve.adeleBdd",
      "card": "AlgebraicCurve.adeleBdd"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.adeleSpace",
      "zone": "B",
      "name": "AlgebraicCurve.adeleSpace",
      "display": "@AlgebraicCurve.adeleSpace",
      "card": "AlgebraicCurve.adeleSpace"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.globalSub",
      "zone": "B",
      "name": "AlgebraicCurve.globalSub",
      "display": "@AlgebraicCurve.globalSub",
      "card": "AlgebraicCurve.globalSub"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.diagonalHom",
      "zone": "B",
      "name": "AlgebraicCurve.diagonalHom",
      "display": "@AlgebraicCurve.diagonalHom",
      "card": "AlgebraicCurve.diagonalHom"
    },
    {
      "type": "prose",
      "md": " `A_F` is the union of the bounded pieces over all divisors — the restricted\nproduct, in which every element is bounded below at all but finitely many\nplaces. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.mem_adeleSpace_iff",
      "zone": "B",
      "name": "AlgebraicCurve.mem_adeleSpace_iff",
      "display": "@AlgebraicCurve.mem_adeleSpace_iff",
      "card": "AlgebraicCurve.mem_adeleSpace_iff"
    },
    {
      "type": "prose",
      "md": " `L(D)` is the diagonal copy of the bounded adeles at `D`, intersected with\nthe principal ones. This is the isomorphism quoted in the note as\n`L(D) ≅ A_F(D) ∩ A⁰`. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.map_diagonal_lSpace",
      "zone": "B",
      "name": "AlgebraicCurve.map_diagonal_lSpace",
      "display": "@AlgebraicCurve.map_diagonal_lSpace",
      "card": "AlgebraicCurve.map_diagonal_lSpace"
    },
    {
      "type": "example",
      "text": "example (D : AlgebraicCurve.Divisor K F) :\n    Submodule.map (AlgebraicCurve.diagonalHom K F) (AlgebraicCurve.LSpace D)\n      = AlgebraicCurve.adeleBdd D ⊓ AlgebraicCurve.globalSub K F :=\n  AlgebraicCurve.map_diagonal_lSpace D",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " Taking dimensions of that isomorphism: `ℓ(D) = dim_K (A_F(D) ∩ A⁰)`. The\n`Nonempty (Place K F)` hypothesis is there because the diagonal is injective only\nwhen there is a place to evaluate at. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell",
      "zone": "B",
      "name": "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell",
      "display": "@AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell",
      "card": "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell"
    },
    {
      "type": "example",
      "text": "example [Nonempty (AlgebraicCurve.Place K F)] (D : AlgebraicCurve.Divisor K F) :\n    Module.finrank K ↥(AlgebraicCurve.adeleBdd D ⊓ AlgebraicCurve.globalSub K F)\n      = AlgebraicCurve.ell D :=\n  AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell D",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B.3 — the quotient: index of speciality and the genus\n\nThe complementary space is not another space of functions; it is a quotient,\ntaken *inside* the adeles. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.indexOfSpecialty",
      "zone": "B",
      "name": "AlgebraicCurve.indexOfSpecialty",
      "display": "@AlgebraicCurve.indexOfSpecialty",
      "card": "AlgebraicCurve.indexOfSpecialty"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.adeleBddPrincipal",
      "zone": "B",
      "name": "AlgebraicCurve.adeleBddPrincipal",
      "display": "@AlgebraicCurve.adeleBddPrincipal",
      "card": "AlgebraicCurve.adeleBddPrincipal"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.indexOfSpecialty_eq",
      "zone": "B",
      "name": "AlgebraicCurve.indexOfSpecialty_eq",
      "display": "@AlgebraicCurve.indexOfSpecialty_eq",
      "card": "AlgebraicCurve.indexOfSpecialty_eq"
    },
    {
      "type": "prose",
      "md": " The same quotient, in the repartition model: `H1 D` is\n`Repartitions / (A_F(D) + A⁰)`, and `i(D)` is its dimension. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.repartitions",
      "zone": "B",
      "name": "AlgebraicCurve.repartitions",
      "display": "@AlgebraicCurve.repartitions",
      "card": "AlgebraicCurve.repartitions"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.repartitionsOf",
      "zone": "B",
      "name": "AlgebraicCurve.repartitionsOf",
      "display": "@AlgebraicCurve.repartitionsOf",
      "card": "AlgebraicCurve.repartitionsOf"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.principalRepartitions",
      "zone": "B",
      "name": "AlgebraicCurve.principalRepartitions",
      "display": "@AlgebraicCurve.principalRepartitions",
      "card": "AlgebraicCurve.principalRepartitions"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.H1",
      "zone": "B",
      "name": "AlgebraicCurve.H1",
      "display": "@AlgebraicCurve.H1",
      "card": "AlgebraicCurve.H1"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.indexOfSpecialty_eq_finrank_H1",
      "zone": "B",
      "name": "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1",
      "display": "@AlgebraicCurve.indexOfSpecialty_eq_finrank_H1",
      "card": "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.HasPrincipalDivisors K F] (D : AlgebraicCurve.Divisor K F) :\n    AlgebraicCurve.indexOfSpecialty D = Module.finrank K (AlgebraicCurve.H1 D) :=\n  AlgebraicCurve.indexOfSpecialty_eq_finrank_H1 D",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " The genus the adelic construction measures: `i(0)`, spelled in the repartition\nmodel as the dimension of `H1 0`. Note what it is *not* — it is not `ell 0`, and it\ndoes not mention differentials. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.genusFF",
      "zone": "B",
      "name": "AlgebraicCurve.genusFF",
      "display": "@AlgebraicCurve.genusFF",
      "card": "AlgebraicCurve.genusFF"
    },
    {
      "type": "example",
      "text": "example : AlgebraicCurve.genusFF K F\n    = Module.finrank K (AlgebraicCurve.H1 (0 : AlgebraicCurve.Divisor K F)) := rfl",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " ### B.4 — differentials: `Ω(D)` is the dual of that quotient\n\n`Ω(D)` is defined by *annihilation*, not by a local condition: the functionals\non the adeles that vanish on `A_F(D) + A⁰`. The dimension equality\n`dim Ω(D) = i(D)` is then the first-isomorphism-theorem duality, not a theorem\nabout differentials. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.omegaSpace",
      "zone": "B",
      "name": "AlgebraicCurve.omegaSpace",
      "display": "@AlgebraicCurve.omegaSpace",
      "card": "AlgebraicCurve.omegaSpace"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.omegaSpaceEquivIndexDual",
      "zone": "B",
      "name": "AlgebraicCurve.omegaSpaceEquivIndexDual",
      "display": "@AlgebraicCurve.omegaSpaceEquivIndexDual",
      "card": "AlgebraicCurve.omegaSpaceEquivIndexDual"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty",
      "zone": "B",
      "name": "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty",
      "display": "@AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty",
      "card": "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty"
    },
    {
      "type": "prose",
      "md": " The annihilator of a subspace is the dual of the quotient — this is the whole\ncontent of `dim Ω(D) = i(D)`, and it holds with no finiteness input. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (D : AlgebraicCurve.Divisor K F) :\n    AlgebraicCurve.omegaSpace D ≃ₗ[K]\n      Module.Dual K (AlgebraicCurve.adeleSpace K F ⧸\n        AlgebraicCurve.adeleBddPrincipal K F D) :=\n  AlgebraicCurve.omegaSpaceEquivIndexDual D",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (D : AlgebraicCurve.Divisor K F) :\n    Module.finrank K ↥(AlgebraicCurve.omegaSpace D)\n      = AlgebraicCurve.indexOfSpecialty D :=\n  AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty D",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " Two facts about the *global* space of differentials, both hypotheses of the\nduality forms below rather than free gifts:\n\n* `WeilDifferentialRankOne` — the Weil differentials (functionals vanishing on\n  `A⁰`) form a one-dimensional `F`-space, generated by the functional attached\n  to any nonzero `ω`. This is the \"one rank-one condition\" of Serre duality;\n* `HasWeilCanonicalDivisor` — a differential has a *maximal* pole divisor `W`, in\n  the sense that no larger divisor bounds it. Maximality is what makes the\n  residue pairing hit every element of `Ω(D)`. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.weilDifferentialModule",
      "zone": "B",
      "name": "AlgebraicCurve.weilDifferentialModule",
      "display": "@AlgebraicCurve.weilDifferentialModule",
      "card": "AlgebraicCurve.weilDifferentialModule"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.WeilDifferentialRankOne",
      "zone": "B",
      "name": "AlgebraicCurve.WeilDifferentialRankOne",
      "display": "@AlgebraicCurve.WeilDifferentialRankOne",
      "card": "AlgebraicCurve.WeilDifferentialRankOne"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasWeilCanonicalDivisor",
      "zone": "B",
      "name": "AlgebraicCurve.HasWeilCanonicalDivisor",
      "display": "@AlgebraicCurve.HasWeilCanonicalDivisor",
      "card": "AlgebraicCurve.HasWeilCanonicalDivisor"
    },
    {
      "type": "prose",
      "md": " The pairing that identifies the two sides of the ladder: fix `φ ∈ Ω(W)`,\nmultiply a function `g ∈ L(W - D)` into it, and read the result as an element of\n`Ω(D)`. In the residue model this is exactly\n`g ↦ (α ↦ ∑_v Res_v(α_v g ω))`. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.residuePairing",
      "zone": "B",
      "name": "AlgebraicCurve.residuePairing",
      "display": "@AlgebraicCurve.residuePairing",
      "card": "AlgebraicCurve.residuePairing"
    },
    {
      "type": "prose",
      "md": "A canonical divisor is the divisor of a nonzero differential. Two differentials\ndiffer by a nonzero function, so `K = (ω)` is well defined up to linear\nequivalence — and that is all Riemann–Roch needs, since `ℓ` and `deg` are\ninsensitive to adding a principal divisor. ",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " The local coordinate: a uniformiser at each place, of order exactly one. The\nport has one `Place.uniformizer` (the `Classical.choose` of an irreducible of the\nvaluation subring), and `ord_uniformizer` is how it is ever characterised — the\ndefinition itself is opaque. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.uniformizer",
      "zone": "C",
      "name": "AlgebraicCurve.Place.uniformizer",
      "display": "@AlgebraicCurve.Place.uniformizer",
      "card": "AlgebraicCurve.Place.uniformizer"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_uniformizer",
      "zone": "C",
      "name": "AlgebraicCurve.Place.ord_uniformizer",
      "display": "@AlgebraicCurve.Place.ord_uniformizer",
      "card": "AlgebraicCurve.Place.ord_uniformizer"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.uniformizer_ne_zero",
      "zone": "C",
      "name": "AlgebraicCurve.Place.uniformizer_ne_zero",
      "display": "@AlgebraicCurve.Place.uniformizer_ne_zero",
      "card": "AlgebraicCurve.Place.uniformizer_ne_zero"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=\n  v.ord_uniformizer",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " `dCoord` is `d t_v`, the Kähler differential of the uniformiser, and\n`DCoordGenerates` is the hypothesis that it spans `Ω` at `v` — the local\ncoordinate exists. That class is what makes `ord_v(ω)` meaningful, and it is why\nthe rungs below carry `[∀ v, v.DCoordGenerates]` as a hypothesis rather than\nderiving it. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.dCoord",
      "zone": "C",
      "name": "AlgebraicCurve.Place.dCoord",
      "display": "@AlgebraicCurve.Place.dCoord",
      "card": "AlgebraicCurve.Place.dCoord"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.DCoordGenerates",
      "zone": "C",
      "name": "AlgebraicCurve.Place.DCoordGenerates",
      "display": "@AlgebraicCurve.Place.DCoordGenerates",
      "card": "AlgebraicCurve.Place.DCoordGenerates"
    },
    {
      "type": "prose",
      "md": " The order of vanishing of a differential, read off its coefficient:\n`ord_v(ω) = ord_v(ω / d t_v)`. The coefficient is `Classical.choose`-ed out of the\nspanning hypothesis, and `differentialCoeff_unique` is what makes it an honest\nfunction. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.differentialCoeff",
      "zone": "C",
      "name": "AlgebraicCurve.Place.differentialCoeff",
      "display": "@AlgebraicCurve.Place.differentialCoeff",
      "card": "AlgebraicCurve.Place.differentialCoeff"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ordDifferential",
      "zone": "C",
      "name": "AlgebraicCurve.Place.ordDifferential",
      "display": "@AlgebraicCurve.Place.ordDifferential",
      "card": "AlgebraicCurve.Place.ordDifferential"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.gate_ordDifferential_dCoord",
      "zone": "C",
      "name": "AlgebraicCurve.Place.gate_ordDifferential_dCoord",
      "display": "@AlgebraicCurve.Place.gate_ordDifferential_dCoord",
      "card": "AlgebraicCurve.Place.gate_ordDifferential_dCoord"
    },
    {
      "type": "prose",
      "md": " `HasCanonicalDivisor` is a *finiteness* statement, not a tautology:\n`ord_v(ω)` must vanish at all but finitely many places, and the resulting\nfunction on places must be a `Finsupp`. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasCanonicalDivisor",
      "zone": "C",
      "name": "AlgebraicCurve.HasCanonicalDivisor",
      "display": "@AlgebraicCurve.HasCanonicalDivisor",
      "card": "AlgebraicCurve.HasCanonicalDivisor"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.canonicalDivisorOf",
      "zone": "C",
      "name": "AlgebraicCurve.canonicalDivisorOf",
      "display": "@AlgebraicCurve.canonicalDivisorOf",
      "card": "AlgebraicCurve.canonicalDivisorOf"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.canonicalDivisorOf_apply",
      "zone": "C",
      "name": "AlgebraicCurve.canonicalDivisorOf_apply",
      "display": "@AlgebraicCurve.canonicalDivisorOf_apply",
      "card": "AlgebraicCurve.canonicalDivisorOf_apply"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : AlgebraicCurve.Place K F) :\n    AlgebraicCurve.canonicalDivisorOf hω v = v.ordDifferential ω :=\n  AlgebraicCurve.canonicalDivisorOf_apply hω v",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.canonicalClass",
      "zone": "C",
      "name": "AlgebraicCurve.canonicalClass",
      "display": "@AlgebraicCurve.canonicalClass",
      "card": "AlgebraicCurve.canonicalClass"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.genus",
      "zone": "C",
      "name": "AlgebraicCurve.genus",
      "display": "@AlgebraicCurve.genus",
      "card": "AlgebraicCurve.genus"
    },
    {
      "type": "prose",
      "md": " The genus the canonical divisor measures, as the port defines it:\n`g = ⌊(deg K + 2) / 2⌋`, computed from a chosen differential. The `if` is honest —\nif there is no nonzero differential the value is junk `0` — so the reachable form\nis the `∃ ω₀` statement below. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.genus_eq_degree_div",
      "zone": "C",
      "name": "AlgebraicCurve.genus_eq_degree_div",
      "display": "@AlgebraicCurve.genus_eq_degree_div",
      "card": "AlgebraicCurve.genus_eq_degree_div"
    },
    {
      "type": "prose",
      "md": " **Two numbers follow, and they are why the genus is not an extra input.**\n`deg K = 2g - 2`: take `D = K` in Riemann–Roch, use `ℓ(K) = g` and `ℓ(0) = 1`.\nThe port's `wkc_degree_canonicalDivisor_eq_of_weilMax` is exactly that computation.\nAnd `ℓ(0) = 1` is the statement that the pole-free functions are the constants. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ConstantsAreBase",
      "zone": "C",
      "name": "AlgebraicCurve.ConstantsAreBase",
      "display": "@AlgebraicCurve.ConstantsAreBase",
      "card": "AlgebraicCurve.ConstantsAreBase"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase",
      "zone": "C",
      "name": "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase",
      "display": "@AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase",
      "card": "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax",
      "zone": "C",
      "name": "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax",
      "display": "@ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax",
      "card": "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax"
    },
    {
      "type": "prose",
      "md": " `ConstantsAreBase` says `L(0)` *is* the image of `K`, not merely\none-dimensional — the stronger form, and the one that both identifies the two\ngenera and produces `deg K = 2g - 2`. ",
      "zone": "C"
    },
    {
      "type": "example",
      "text": "example (h : AlgebraicCurve.ConstantsAreBase K F) :\n    AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F)\n      = LinearMap.range (Algebra.linearMap K F) := h",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " The integer content of `deg K = 2g - 2`, with `ℓ(K) = g` substituted into\n`ℓ(K) - ℓ(0) = deg K + 1 - g` and `ℓ(0) = 1`. ",
      "zone": "C"
    },
    {
      "type": "example",
      "text": "example {dK g : ℤ} (h : g - 1 = dK + 1 - g) : dK = 2 * g - 2 := by linarith",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " Two ways in to `ℓ(0) = 1`, either of which is a separate input: a place of\nresidue degree one suffices, and over an algebraically closed field every place\nis one (rung 0 plus `IsAlgClosed`). ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.constantsAreBase_of_deg_eq_one",
      "zone": "C",
      "name": "AlgebraicCurve.constantsAreBase_of_deg_eq_one",
      "display": "@AlgebraicCurve.constantsAreBase_of_deg_eq_one",
      "card": "AlgebraicCurve.constantsAreBase_of_deg_eq_one"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.constantsAreBase_of_isAlgClosed",
      "zone": "C",
      "name": "AlgebraicCurve.constantsAreBase_of_isAlgClosed",
      "display": "@AlgebraicCurve.constantsAreBase_of_isAlgClosed",
      "card": "AlgebraicCurve.constantsAreBase_of_isAlgClosed"
    },
    {
      "type": "prose",
      "md": " **The two genera agree** — a theorem, not a definition. One is read off a\nsingle divisor, the other off the whole adelic quotient; the proof spends the\nRiemann–Roch identity, the adelic duality form, and `ConstantsAreBase`. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.genus_eq_genusFF",
      "zone": "C",
      "name": "AlgebraicCurve.genus_eq_genusFF",
      "display": "@AlgebraicCurve.genus_eq_genusFF",
      "card": "AlgebraicCurve.genus_eq_genusFF"
    },
    {
      "type": "example",
      "text": "example (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)\n    (hWD : AlgebraicCurve.WeilDualityAdelic K F)\n    (hC : AlgebraicCurve.ConstantsAreBase K F)\n    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]\n    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates] :\n    AlgebraicCurve.genus K F = AlgebraicCurve.genusFF K F :=\n  AlgebraicCurve.genus_eq_genusFF hRR hWD hC",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " The same identity from the other end: the canonical space has dimension `g`. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
      "zone": "C",
      "name": "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
      "display": "@AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
      "card": "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch"
    },
    {
      "type": "prose",
      "md": "Each rung is a `Prop`-valued `def` in `Defs/RiemannRochRows.lean`, printed below\nin full so the instance arguments are visible. Two points about reading them:\n\n* every rung quantifies `[IsCurveOver K F]`, `[HasCanonicalDivisor]` (and often\n  `[∀ v, v.DCoordGenerates]`) *inside* itself, so a rung is a statement about a\n  **class** of curves, not about one fixed `F/K`;\n* the arrows between rungs are ordinary theorems about those `Prop`s, and they\n  are cheap exactly where one statement is a rearrangement of another. ",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " **Rung 1 — Riemann's inequality.** The half of Riemann–Roch that needs no\nduality. It follows from the adelic description of `L(D)` and an index count. ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.RiemannInequality",
      "zone": "D",
      "name": "AlgebraicCurve.RiemannInequality",
      "display": "AlgebraicCurve.RiemannInequality",
      "card": "AlgebraicCurve.RiemannInequality"
    },
    {
      "type": "prose",
      "md": " **Rung 2 — the index formula.** Riemann–Roch with `i(D)` left as the quotient\ndimension: the honest form, because it names what the second term is. ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.RiemannIndexFormula",
      "zone": "D",
      "name": "AlgebraicCurve.RiemannIndexFormula",
      "display": "AlgebraicCurve.RiemannIndexFormula",
      "card": "AlgebraicCurve.RiemannIndexFormula"
    },
    {
      "type": "prose",
      "md": " **Rung 3a — the duality form, adelic.** `i(D) = ℓ(K - D)`, stated with the\ncanonical divisor named by a differential. ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.WeilDualityAdelic",
      "zone": "D",
      "name": "AlgebraicCurve.WeilDualityAdelic",
      "display": "AlgebraicCurve.WeilDualityAdelic",
      "card": "AlgebraicCurve.WeilDualityAdelic"
    },
    {
      "type": "prose",
      "md": " **Rung 3c — the same, rearranged.** `ℓ(D) - ℓ(K - D) = deg D + 1 - g`. Given\nthe index formula this is exactly 3a moved across the equals sign; the port's\nbridge is `weilDuality_of_riemannIndex_of_adelic`, and rung 4 then follows by\n`functionFieldRiemannRoch_of_riemann_and_duality` (both in D.1). ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.WeilDuality",
      "zone": "D",
      "name": "AlgebraicCurve.WeilDuality",
      "display": "AlgebraicCurve.WeilDuality",
      "card": "AlgebraicCurve.WeilDuality"
    },
    {
      "type": "prose",
      "md": " **Rung 3b — the differential version.** `dim Ω(D) = ℓ(K - D)`. This is the rung\nSerre duality feeds: once the Weil differentials are one-dimensional over `F` and\nthe functional is maximal, the residue pairing `L(K - D) → Ω(D)` is an isomorphism\n(D.2), and 3b is its dimension count. ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.WeilOmegaEllAgrees",
      "zone": "D",
      "name": "AlgebraicCurve.WeilOmegaEllAgrees",
      "display": "AlgebraicCurve.WeilOmegaEllAgrees",
      "card": "AlgebraicCurve.WeilOmegaEllAgrees"
    },
    {
      "type": "prose",
      "md": " **Rung 4 — Riemann–Roch.** The identity, with `K = (ω)` named by a differential\nand both dimensions written as `ℓ`. ",
      "zone": "D"
    },
    {
      "type": "print",
      "raw": "#print AlgebraicCurve.FunctionFieldRiemannRoch",
      "zone": "D",
      "name": "AlgebraicCurve.FunctionFieldRiemannRoch",
      "display": "AlgebraicCurve.FunctionFieldRiemannRoch",
      "card": "AlgebraicCurve.FunctionFieldRiemannRoch"
    },
    {
      "type": "prose",
      "md": " ### D.1 — the cheap arrows\n\nTwo theorems, both `linarith`-shaped, and both part of the rung structure. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality",
      "zone": "D",
      "name": "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality",
      "display": "@AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality",
      "card": "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic",
      "zone": "D",
      "name": "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic",
      "display": "@AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic",
      "card": "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic"
    },
    {
      "type": "example",
      "text": "example (h : AlgebraicCurve.WeilDuality K F) :\n    AlgebraicCurve.FunctionFieldRiemannRoch K F :=\n  AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality K F h",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " The integer shadow of `(3b) + index formula ⟹ (3a)`: the index is `dim Ω(D)`\nby the annihilator duality, `dim Ω(D)` is `ℓ(K - D)` by rung 3b, hence the two\nare equal. Two substitutions, no analysis. ",
      "zone": "D"
    },
    {
      "type": "example",
      "text": "example {i lk om : ℤ} (hAnn : om = i) (h3b : om = lk) : i = lk := by linarith",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " The integer shadow of `index formula ⟹ inequality`: the index is a dimension,\nso it is nonnegative, and the inequality is the index formula solved for `ℓ`. ",
      "zone": "D"
    },
    {
      "type": "example",
      "text": "example {l i d g : ℤ} (hi : i = l - (d + 1 - g)) (h : 0 ≤ i) : d + 1 - g ≤ l := by\n  linarith",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " The integer shadow of `(3a) + index formula ⟹ (3c)`: substitute\n`i(D) = ℓ(K - D)` into `i(D) = ℓ(D) - (deg D + 1 - g)`. ",
      "zone": "D"
    },
    {
      "type": "example",
      "text": "example {l lk i d g : ℤ} (hi : i = l - (d + 1 - g)) (hd : i = lk) :\n    l - lk = d + 1 - g := by\n  linarith",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " Rung 2 implies rung 1, as a theorem about divisors. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula",
      "zone": "D",
      "name": "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula",
      "display": "@AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula",
      "card": "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F]\n    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]\n    (h : AlgebraicCurve.RiemannIndexFormula K F) (D : AlgebraicCurve.Divisor K F) :\n    AlgebraicCurve.Divisor.degree D + 1 - (AlgebraicCurve.genus K F : ℤ)\n      ≤ (AlgebraicCurve.ell D : ℤ) :=\n  AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula h D",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " ### D.2 — the duality, as a pairing\n\nThe analytic content of the ladder is the production of a *maximal* functional\nand the bijectivity of the residue pairing it defines. Given rank-one-ness the\npairing is injective; given maximality it is surjective. Those two halves are\n`residuePairing_injective` and `residuePairing_surjective`. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.residuePairing_injective",
      "zone": "D",
      "name": "AlgebraicCurve.residuePairing_injective",
      "display": "@AlgebraicCurve.residuePairing_injective",
      "card": "AlgebraicCurve.residuePairing_injective"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.residuePairing_surjective",
      "zone": "D",
      "name": "AlgebraicCurve.residuePairing_surjective",
      "display": "@AlgebraicCurve.residuePairing_surjective",
      "card": "AlgebraicCurve.residuePairing_surjective"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ResiduePairingSurjective",
      "zone": "D",
      "name": "AlgebraicCurve.ResiduePairingSurjective",
      "display": "@AlgebraicCurve.ResiduePairingSurjective",
      "card": "AlgebraicCurve.ResiduePairingSurjective"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula",
      "zone": "D",
      "name": "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula",
      "display": "@AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula",
      "card": "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.HasPrincipalDivisors K F]\n    (W D : AlgebraicCurve.Divisor K F)\n    {φ : Module.Dual K ↥(AlgebraicCurve.adeleSpace K F)}\n    (hφ : φ ∈ AlgebraicCurve.omegaSpace W) (hφ0 : φ ≠ 0) :\n    Function.Injective ⇑(AlgebraicCurve.residuePairing K F W D hφ) :=\n  AlgebraicCurve.residuePairing_injective W D hφ hφ0",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " Injectivity alone is the inequality direction: `ℓ(W - D) ≤ i(D)`. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ell_sub_le_indexOfSpecialty",
      "zone": "D",
      "name": "AlgebraicCurve.ell_sub_le_indexOfSpecialty",
      "display": "@AlgebraicCurve.ell_sub_le_indexOfSpecialty",
      "card": "AlgebraicCurve.ell_sub_le_indexOfSpecialty"
    },
    {
      "type": "prose",
      "md": " ### D.3 — the genus-existence axis\n\nThe rungs above all presuppose the existence of `g` in order to write it at all.\nThe port carries five ways of saying that one thing — finiteness of a quotient,\nboundedness of `deg D - ℓ D`, attainment of the supremum at a witness, and the\nStichtenoth package (a place, `L(0)` finite, and a witness) — and proves\n`StichtenothGenusExists ↔ IndexOfSpecialtyFinite` (the example below), whose two\ndirections are a finiteness transfer through the adele filtration and a\nconstruction of the witness. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IndexOfSpecialtyFinite",
      "zone": "D",
      "name": "AlgebraicCurve.IndexOfSpecialtyFinite",
      "display": "@AlgebraicCurve.IndexOfSpecialtyFinite",
      "card": "AlgebraicCurve.IndexOfSpecialtyFinite"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.RiemannGenusBounded",
      "zone": "D",
      "name": "AlgebraicCurve.RiemannGenusBounded",
      "display": "@AlgebraicCurve.RiemannGenusBounded",
      "card": "AlgebraicCurve.RiemannGenusBounded"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.RiemannGenusReachedAt",
      "zone": "D",
      "name": "AlgebraicCurve.RiemannGenusReachedAt",
      "display": "@AlgebraicCurve.RiemannGenusReachedAt",
      "card": "AlgebraicCurve.RiemannGenusReachedAt"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.RiemannGenusReached",
      "zone": "D",
      "name": "AlgebraicCurve.RiemannGenusReached",
      "display": "@AlgebraicCurve.RiemannGenusReached",
      "card": "AlgebraicCurve.RiemannGenusReached"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.StichtenothGenusExists",
      "zone": "D",
      "name": "AlgebraicCurve.StichtenothGenusExists",
      "display": "@AlgebraicCurve.StichtenothGenusExists",
      "card": "AlgebraicCurve.StichtenothGenusExists"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] [Nonempty (AlgebraicCurve.Place K F)]\n    [FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K F))] :\n    AlgebraicCurve.StichtenothGenusExists K F ↔ AlgebraicCurve.IndexOfSpecialtyFinite K F :=\n  AlgebraicCurve.stichtenothGenusExists_iff_indexFinite",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " Rung 2 out of the genus. With a witness `D₀` in hand, `A_F` is already\n`A_F(D ⊔ D₀) + A⁰` for every `D`, and a quotient chain computes the index — an\nadelic computation with no differential in it. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.riemannIndexFormula_of_genusReached",
      "zone": "D",
      "name": "AlgebraicCurve.riemannIndexFormula_of_genusReached",
      "display": "@AlgebraicCurve.riemannIndexFormula_of_genusReached",
      "card": "AlgebraicCurve.riemannIndexFormula_of_genusReached"
    },
    {
      "type": "prose",
      "md": " The genus is nonnegative — not free, since it is `deg D₀ - ℓ(D₀) + 1` for a\nwitness `D₀` and `deg` can be negative. It spends `ConstantsAreBase`. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.stichtenothGenus_nonneg",
      "zone": "D",
      "name": "AlgebraicCurve.stichtenothGenus_nonneg",
      "display": "@AlgebraicCurve.stichtenothGenus_nonneg",
      "card": "AlgebraicCurve.stichtenothGenus_nonneg"
    },
    {
      "type": "prose",
      "md": "For application the question is not which rung is true but **how few hypotheses**\nthe top can be stated under. Reading the four headlines in order says what each\nlayer of structure is worth: the content of the theorem is unchanged, but the\namount of structure the statement must be *handed* grows as the hypotheses\nshrink. ",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": " **Wrapper 1 — from the K residue theorem.** The assembled statement: the\ncurve axioms, the canonical divisor, generation of `Ω` at every place, `F` finite\nand separable over a rational function subfield, and `ResidueTheoremK`. Nothing is\nderived here. ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
      "zone": "E",
      "name": "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
      "display": "@AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
      "card": "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed"
    },
    {
      "type": "prose",
      "md": " **Wrapper 2 — over an algebraically closed field.** The residue theorem is\nsupplied rather than assumed: the hypothesis list loses it and keeps the curve\npackage. ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
      "zone": "E",
      "name": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
      "display": "@AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
      "card": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed"
    },
    {
      "type": "prose",
      "md": " **Wrapper 3 — from the curve over an algebraically closed field.** All three\nresidue-side hypotheses disappear, supplied unconditionally by the port's local\nresidue instance and by perfectness. ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
      "zone": "E",
      "name": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
      "display": "@AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
      "card": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver"
    },
    {
      "type": "prose",
      "md": " **Wrapper 4 — from a transcendental generator.** `K` algebraically closed,\n`x ∈ F` transcendental, `F` finite over `K(x)` — everything else derived. This is\nthe form the theorem is actually consumed in: every FLT application has a specific\ntranscendental in hand and no desire to verify a curve package by hand. ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental",
      "zone": "E",
      "name": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental",
      "display": "@AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental",
      "card": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental"
    },
    {
      "type": "example",
      "text": "example [IsAlgClosed K] {x : F} (hx : Transcendental K x)\n    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :\n    AlgebraicCurve.FunctionFieldRiemannRoch K F :=\n  AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfin",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": " The genus-free form of the theorem, and the one to read next to rung 4:\nRiemann–Roch with the *adelic* genus `genusFF` and an existential canonical\ndivisor, so no `HasCanonicalDivisor` appears in the statement at all. ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.exists_weilCanonical_riemannRoch",
      "zone": "E",
      "name": "AlgebraicCurve.exists_weilCanonical_riemannRoch",
      "display": "@AlgebraicCurve.exists_weilCanonical_riemannRoch",
      "card": "AlgebraicCurve.exists_weilCanonical_riemannRoch"
    },
    {
      "type": "prose",
      "md": " ### E.1 — the K-route chain, in the port's own step order\n\nBetween the residue theorem and wrapper 1 sits the chain `wkc_*`: maximal\nfunctional ⟹ `dim Ω(D) = ℓ(K - D)` ⟹ index formula ⟹ Riemann–Roch. Reading it\nin this order is reading the note's §5 route diagram.\n\nNote the namespace, because a `#check` will not find these under\n`AlgebraicCurve`: the port's own section heading for this block is \"The\n`ModularCurve` assembly\". The `wkc_` prefix is the pin's subject tag and survives\nthe port's rename (the pin's generated declarations carry a `p0n25_` part label in\nfront, which the port drops). ",
      "zone": "E"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_weilOfKaehlerK_single",
      "zone": "E",
      "name": "ModularCurve.wkc_weilOfKaehlerK_single",
      "display": "@ModularCurve.wkc_weilOfKaehlerK_single",
      "card": "ModularCurve.wkc_weilOfKaehlerK_single"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax",
      "zone": "E",
      "name": "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax",
      "display": "@ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax",
      "card": "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax",
      "zone": "E",
      "name": "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax",
      "display": "@ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax",
      "card": "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_riemannIndexFormula_of_weilMax",
      "zone": "E",
      "name": "ModularCurve.wkc_riemannIndexFormula_of_weilMax",
      "display": "@ModularCurve.wkc_riemannIndexFormula_of_weilMax",
      "card": "ModularCurve.wkc_riemannIndexFormula_of_weilMax"
    },
    {
      "type": "check",
      "raw": "#check @ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK",
      "zone": "E",
      "name": "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK",
      "display": "@ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK",
      "card": "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK"
    },
    {
      "type": "prose",
      "md": " ### E.2 — the four independent inputs\n\nThe hierarchy is a lattice rather than a chain because four of its inputs are\nindependent of the rest and of each other. Each has its own home, and each is\nproved unconditionally in the port's setting (a curve over a perfect field,\nessentially of finite type) — which is why the top of the stack is reachable at\nall, and why a route that supplies one of them differently plugs in at one place.\n\n* **the canonical divisor exists** — `HasCanonicalDivisor`, a finiteness statement\n  about `ord_v(ω)`, proved from the Kähler rank and a separating transcendental;\n* **the genus exists** — the axis of D.3: `StichtenothGenusExists`,\n  `IndexOfSpecialtyFinite`, `RiemannGenusBounded`, `RiemannGenusReached`;\n* **the constants are the base field** — `ConstantsAreBase`, needed both to\n  identify `genus` with `genusFF` and to make `deg K = 2g - 2` come out; a function\n  field with a larger constant field has `ℓ(0) > 1`;\n* **`Ω` is generated at each place** — `DCoordGenerates`, the local-coordinate\n  hypothesis that makes the divisor-valued `ord_v(ω)` meaningful. This one is\n  local and per-place, unlike the other three, and it is *not* implied by\n  `kaehler_free_rank_one` (Q5 in Zone A separates the two). ",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": " ### E.3 — things to poke at\n\n* `ell` is `Module.finrank`, and `finrank` is `0` on an infinite-dimensional\n  space. So `ell D` is *junk-zero* when `L(D)` is infinite-dimensional, and a row\n  like `RiemannInequality` read without the finite-dimensionality supplied on the\n  genus axis is then a statement about that junk value, not about dimensions.\n  Live, with an infinite independent family and no `FiniteDimensional` anywhere:\n\n    `LinearIndependent.finrank_eq_zero_of_infinite` turns the monomials of `K[X]`\n    into `finrank = 0`.\n\n* Delete `[HasCanonicalDivisor]` from an `example` above and watch which step\n  survives: the `ell`-side statements survive, the ones that name `K = (ω)` do\n  not. That is the sense in which the canonical divisor is a separate input.\n\n* Replace `AlgebraicCurve.LSpace D` with `AlgebraicCurve.riemannRochSpace D` in\n  any statement here: they are the same term, so nothing changes. `LSpace` is an\n  `abbrev` for the repartition module's `riemannRochSpace`, and the ladder is\n  written in the vocabulary of the adelic-index module (`LSpace`, `ell`).\n\n* `genus` is defined with `(deg K + 2).toNat / 2`, so it is `0` in the unreachable\n  branch. `genus_eq_degree_div` is the statement that some `ω₀` actually realises\n  the `if`; without it, every `genus` lemma is conditional on a junk value.\n\n* The rows quantify their instances, the wrappers do not. `#print` a row and a\n  wrapper side by side: the row begins `∀ [IsCurveOver K F] ...`, the wrapper is\n  an `example`-style statement about the `F/K` in scope with those instances\n  already discharged. ",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": " The `finrank`-junk demonstration, live: an infinite-dimensional space has\n`finrank` zero, because *there is* an infinite linearly independent family. This\nis a property of `finrank`, not of the curve, and it is why the ladder has to\ncarry `FiniteDimensional` where it reads `ℓ` as a dimension. ",
      "zone": "E"
    },
    {
      "type": "example",
      "text": "example : Module.finrank K (Polynomial K) = 0 :=\n  (Polynomial.basisMonomials K).linearIndependent.finrank_eq_zero_of_infinite",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "Oldest first. Each entry: question, one-line answer, and a pointer to the zone\nthat was edited.\n\n* (2026-10-23) *Worksheet created.* — no questions yet.\n* (2026-10-23) **Q1.** In `ℓ(D) - ℓ(K - D) = deg D + 1 - g`, is the second term\n  the dimension of a second space of functions? — No: it is the dimension of a\n  space of *differentials*, which is the dual of a quotient of adeles, and the\n  notation `ℓ(K - D)` names that dimension by the divisor it corresponds to. See\n  B.4 and the `omegaSpaceEquivIndexDual` block.\n* (2026-10-23) **Q2.** If `i(D)` and `dim Ω(D)` are the same number, why state\n  both rungs? — Because the identification is *annihilator duality*, which holds\n  with no finiteness input, while the step that identifies `dim Ω(D)` with\n  `ℓ(K - D)` is the analytic content (Serre duality: rank-one plus maximality).\n  Rung 3b prices the two separately. See D.2.\n* (2026-10-23) **Q3.** Is `genus` a definition or a theorem on the adelic side? —\n  Both are definitions: `genus` is `⌊(deg K + 2)/2⌋` from a chosen differential,\n  `genusFF` is `dim H1(0)`. That they agree is `genus_eq_genusFF`, a theorem that\n  spends Riemann–Roch, the duality form, and `ConstantsAreBase`. See Zone C.\n* (2026-10-23) **Q4.** Why does every rung repeat `[IsCurveOver K F]` and friends\n  instead of taking them as section variables? — So that the rung is a statement\n  about a class of curves, portable to any `F/K`; the wrapper stack is where the\n  instances are discharged for one given field. See E.2.\n* (2026-10-23) **Q5.** What is `kaehler_free_rank_one` — that a canonical\n  differential exists? that the tangent space is one-dimensional? Is it part of\n  `IsCurveOver`? — It is the third field of `IsCurveOver` and says `Ω[F⁄K] ≅ F`:\n  the differentials form a *line*. It makes a differential *available* but not\n  *canonical* (only `(ω)`'s class is), it is the statement that the cotangent\n  space at the generic point is one-dimensional (hence so is the tangent space),\n  and it does **not** give the canonical divisor — that is `HasCanonicalDivisor`,\n  derived separately over a perfect field, plus `DCoordGenerates` per place. See\n  the Q5 block in Zone A.\n",
      "zone": "Q"
    },
    {
      "type": "code",
      "text": "end Play",
      "zone": "Q"
    }
  ],
  "bound": [
    "K",
    "F",
    "v",
    "f",
    "D",
    "E",
    "h",
    "ω",
    "hω",
    "dK",
    "g",
    "hRR",
    "hWD",
    "hC",
    "i",
    "lk",
    "om",
    "hAnn",
    "h3b",
    "l",
    "d",
    "hi",
    "hd",
    "W",
    "φ",
    "hφ",
    "hφ0",
    "x",
    "hx",
    "hfin"
  ],
  "seed_cards": ["AlgebraicCurve.ConstantsAreBase","AlgebraicCurve.Divisor","AlgebraicCurve.Divisor.degZero","AlgebraicCurve.Divisor.degree","AlgebraicCurve.Divisor.degree_eq_sum","AlgebraicCurve.Divisor.degree_single","AlgebraicCurve.Divisor.principal","AlgebraicCurve.FunctionFieldRiemannRoch","AlgebraicCurve.H1","AlgebraicCurve.HasCanonicalDivisor","AlgebraicCurve.HasPrincipalDivisors","AlgebraicCurve.HasWeilCanonicalDivisor","AlgebraicCurve.IndexOfSpecialtyFinite","AlgebraicCurve.IsCurveOver","AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed","AlgebraicCurve.IsCurveOver.finrank_kaehler","AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed","AlgebraicCurve.IsCurveOver.instFreeKaehler","AlgebraicCurve.IsCurveOver.instNontrivialKaehler","AlgebraicCurve.IsCurveOver.kaehler_free_rank_one","AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField","AlgebraicCurve.LSpace","AlgebraicCurve.Pic","AlgebraicCurve.Pic0","AlgebraicCurve.Place","AlgebraicCurve.Place.DCoordGenerates","AlgebraicCurve.Place.FiniteResidue","AlgebraicCurve.Place.ResidueField","AlgebraicCurve.Place.dCoord","AlgebraicCurve.Place.deg","AlgebraicCurve.Place.differentialCoeff","AlgebraicCurve.Place.gate_ordDifferential_dCoord","AlgebraicCurve.Place.ord","AlgebraicCurve.Place.ordDifferential","AlgebraicCurve.Place.ord_uniformizer","AlgebraicCurve.Place.uniformizer","AlgebraicCurve.Place.uniformizer_ne_zero","AlgebraicCurve.ResiduePairingSurjective","AlgebraicCurve.RiemannGenusBounded","AlgebraicCurve.RiemannGenusReached","AlgebraicCurve.RiemannGenusReachedAt","AlgebraicCurve.RiemannIndexFormula","AlgebraicCurve.RiemannInequality","AlgebraicCurve.StichtenothGenusExists","AlgebraicCurve.WeilDifferentialRankOne","AlgebraicCurve.WeilDuality","AlgebraicCurve.WeilDualityAdelic","AlgebraicCurve.WeilOmegaEllAgrees","AlgebraicCurve.adeleBdd","AlgebraicCurve.adeleBddPrincipal","AlgebraicCurve.adeleSpace","AlgebraicCurve.canonicalClass","AlgebraicCurve.canonicalDivisorOf","AlgebraicCurve.canonicalDivisorOf_apply","AlgebraicCurve.constantsAreBase_of_deg_eq_one","AlgebraicCurve.constantsAreBase_of_isAlgClosed","AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula","AlgebraicCurve.diagonalHom","AlgebraicCurve.ell","AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch","AlgebraicCurve.ell_sub_le_indexOfSpecialty","AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase","AlgebraicCurve.exists_weilCanonical_riemannRoch","AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell","AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty","AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed","AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver","AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental","AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed","AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality","AlgebraicCurve.genus","AlgebraicCurve.genusFF","AlgebraicCurve.genus_eq_degree_div","AlgebraicCurve.genus_eq_genusFF","AlgebraicCurve.globalSub","AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver","AlgebraicCurve.indexOfSpecialty","AlgebraicCurve.indexOfSpecialty_eq","AlgebraicCurve.indexOfSpecialty_eq_finrank_H1","AlgebraicCurve.lSpace_mono","AlgebraicCurve.map_diagonal_lSpace","AlgebraicCurve.mem_adeleSpace_iff","AlgebraicCurve.mem_lSpace_iff","AlgebraicCurve.mem_lSpace_iff_ord","AlgebraicCurve.omegaSpace","AlgebraicCurve.omegaSpaceEquivIndexDual","AlgebraicCurve.one_mem_lSpace_zero","AlgebraicCurve.principalRepartitions","AlgebraicCurve.repartitions","AlgebraicCurve.repartitionsOf","AlgebraicCurve.residuePairing","AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula","AlgebraicCurve.residuePairing_injective","AlgebraicCurve.residuePairing_surjective","AlgebraicCurve.riemannIndexFormula_of_genusReached","AlgebraicCurve.riemannRochSpace","AlgebraicCurve.stichtenothGenus_nonneg","AlgebraicCurve.weilDifferentialModule","AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic","Classical.choose","FiniteDimensional","Finsupp","IsAlgClosed","KaehlerDifferential","LinearIndependent.finrank_eq_zero_of_infinite","ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax","ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax","ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax","ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK","ModularCurve.wkc_riemannIndexFormula_of_weilMax","ModularCurve.wkc_weilOfKaehlerK_single","Module.finrank","Subspace.dual_finrank_eq","exists_smul_eq_of_finrank_eq_one","le_trans"],
  "card_count": 252,
  "modules": ["FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor","FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","FLTForHuman.AlgebraicCurve.Defs.Divisor","FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","FLTForHuman.AlgebraicCurve.Defs.LocalResidue","FLTForHuman.AlgebraicCurve.Defs.Place","FLTForHuman.AlgebraicCurve.Defs.Repartitions","FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows","FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler","FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental","FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly","FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly","Init.Classical","Init.Core","Init.Data.Cast","Init.Data.Function","Init.Data.Int.Basic","Init.Prelude","Mathlib.Algebra.Algebra.Basic","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Algebra.Operations","Mathlib.Algebra.Algebra.Pi","Mathlib.Algebra.Algebra.Subalgebra.Basic","Mathlib.Algebra.Algebra.Subalgebra.Lattice","Mathlib.Algebra.BigOperators.Finsupp.Basic","Mathlib.Algebra.BigOperators.Group.Finset.Defs","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.Group.Action.Defs","Mathlib.Algebra.Group.Action.Pi","Mathlib.Algebra.Group.Defs","Mathlib.Algebra.Group.Equiv.Defs","Mathlib.Algebra.Group.Hom.Basic","Mathlib.Algebra.Group.Hom.Defs","Mathlib.Algebra.Group.Irreducible.Defs","Mathlib.Algebra.Group.Monoid","Mathlib.Algebra.Group.Pi.Basic","Mathlib.Algebra.Group.Subgroup.Defs","Mathlib.Algebra.Group.Subgroup.Ker","Mathlib.Algebra.Group.Subgroup.Map","Mathlib.Algebra.Group.TypeTags.Basic","Mathlib.Algebra.Group.WithOne.Defs","Mathlib.Algebra.GroupWithZero.Hom","Mathlib.Algebra.GroupWithZero.NonZeroDivisors","Mathlib.Algebra.GroupWithZero.WithZero","Mathlib.Algebra.Module.Defs","Mathlib.Algebra.Module.Equiv.Defs","Mathlib.Algebra.Module.LinearMap.Defs","Mathlib.Algebra.Module.Pi","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.Module.Submodule.Lattice","Mathlib.Algebra.Module.Submodule.LinearMap","Mathlib.Algebra.Module.Submodule.Map","Mathlib.Algebra.Module.Submodule.Range","Mathlib.Algebra.Module.Submodule.RestrictScalars","Mathlib.Algebra.Order.Monoid.TypeTags","Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","Mathlib.Algebra.Polynomial.AlgebraMap","Mathlib.Algebra.Polynomial.Basic","Mathlib.Algebra.Quotient","Mathlib.Algebra.Ring.Basic","Mathlib.Algebra.Ring.CompTypeclasses","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Algebra.Ring.Pi","Mathlib.Basic.ExistsUnique","Mathlib.Basic.Finite.Defs","Mathlib.Basic.Nontrivial.Defs","Mathlib.Data.Finsupp.Defs","Mathlib.Data.Finsupp.Single","Mathlib.Data.Set.Defs","Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","Mathlib.FieldTheory.IntermediateField.Basic","Mathlib.FieldTheory.IsAlgClosed.Basic","Mathlib.FieldTheory.Perfect","Mathlib.FieldTheory.RatFunc.Defs","Mathlib.FieldTheory.Separable","Mathlib.GroupTheory.Coset.Defs","Mathlib.GroupTheory.OreLocalization.OreSet","Mathlib.GroupTheory.QuotientGroup.Defs","Mathlib.LinearAlgebra.Dimension.Basic","Mathlib.LinearAlgebra.Dimension.Finite","Mathlib.LinearAlgebra.Dimension.Finrank","Mathlib.LinearAlgebra.Dual.Defs","Mathlib.LinearAlgebra.Dual.Lemmas","Mathlib.LinearAlgebra.FiniteDimensional.Basic","Mathlib.LinearAlgebra.FiniteDimensional.Defs","Mathlib.LinearAlgebra.FreeModule.Basic","Mathlib.LinearAlgebra.LinearIndependent.Defs","Mathlib.LinearAlgebra.Quotient.Defs","Mathlib.LinearAlgebra.TensorProduct.Defs","Mathlib.Order.Defs.PartialOrder","Mathlib.Order.SetNotation","Mathlib.RingTheory.Algebraic.Defs","Mathlib.RingTheory.AlgebraicIndependent.Basic","Mathlib.RingTheory.Derivation.Basic","Mathlib.RingTheory.EssentialFiniteness","Mathlib.RingTheory.Finiteness.Defs","Mathlib.RingTheory.Ideal.Cotangent","Mathlib.RingTheory.IntegralClosure.Algebra.Defs","Mathlib.RingTheory.Kaehler.Basic","Mathlib.RingTheory.LocalRing.ResidueField.Basic","Mathlib.RingTheory.LocalRing.ResidueField.Defs","Mathlib.RingTheory.Trace.Defs","Mathlib.RingTheory.Valuation.Basic","Mathlib.RingTheory.Valuation.ValuationSubring","Mathlib.SetTheory.Cardinal.Defs"]
};
