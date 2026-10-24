window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["PlacesAndDifferentials"] = {
  "slug": "PlacesAndDifferentials",
  "file": "lean/play/PlacesAndDifferentials.lean",
  "title": "places and differentials",
  "tagline": "why a uniformiser is not a differential",
  "subject": "the two halves of the local theory and the gap between them: a place always has a uniformiser and an order, a differential is a global derivation, and nothing in the place data produces one. That gap is why `IsCurveOver` carries `kaehler_free_rank_one` as an axiom, and why every rung that names a canonical divisor carries `[∀ v, v.DCoordGenerates]` per place.",
  "intro": "A place gives an order `ord_v` and a uniformiser `t_v`; a differential lives in the Kähler module `Ω[F⁄K]`, which is an object of the whole field extension and mentions no place. This sheet separates the two, exhibits each gate the port puts between them (`dCoord`, `DCoordGenerates`, `differentialCoeff`, `ordDifferential`, `HasCanonicalDivisor`), shows that the same order admits different differentials, and lands on the axiom that no amount of place data can supply: `kaehler_free_rank_one`.",
  "reads": "FLTForHuman/AlgebraicCurve/Defs/Place.lean, Defs/CanonicalDivisor.lean, Defs/LocalResidue.lean, P1/DXCoeff.lean, IsCurveOver/SeparatingTranscendental.lean, Canonical/HasCanonicalDivisor.lean, Defs/RiemannRochRows.lean",
  "pin": "Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean (the `Place` structure and `ord`), Definitions/Def_ModularCurve_CanonicalDivisor.lean, Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean, Definitions/Def_AlgebraicCurve_IsCurveOver.lean, P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean, all at aa2d8b3",
  "check": "cd lean && lake env lean play/PlacesAndDifferentials.lean   (~5 s, oleans warm)",
  "status": "open",
  "date": "2026-10-23",
  "imports": ["FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly"],
  "opens": ["KaehlerDifferential"],
  "namespace": "Play",
  "zones": [{"id":"A","title":"the place, unconditionally"},{"id":"B","title":"the differential, globally"},{"id":"C","title":"the bridge and its gates"},{"id":"D","title":"the three gaps, and why the axiom is an axiom"},{"id":"E","title":"things to poke at"},{"id":"Q","title":"question log"}],
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
      "md": "A `Place` is a valuation subring with three side conditions. Read the field list\nand note what is *absent*: nothing in a place mentions `Ω`, a derivation, or the\nextension `F/K` beyond the `K`-algebra structure. ",
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
      "md": " The side conditions are that the constants are integral at `v`\n(`algebraMap_mem'`), that the ring is proper (`ne_top'`), and that it is a\nprincipal ideal ring. On top of being a valuation subring those give a discrete\nvaluation ring, which is what the port attaches to: ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @IsDiscreteValuationRing.exists_irreducible",
      "zone": "A",
      "name": "IsDiscreteValuationRing.exists_irreducible",
      "display": "@IsDiscreteValuationRing.exists_irreducible",
      "card": "IsDiscreteValuationRing.exists_irreducible"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.heightOneSpectrum",
      "zone": "A",
      "name": "AlgebraicCurve.Place.heightOneSpectrum",
      "display": "@AlgebraicCurve.Place.heightOneSpectrum",
      "card": "AlgebraicCurve.Place.heightOneSpectrum"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.adicValuation",
      "zone": "A",
      "name": "AlgebraicCurve.Place.adicValuation",
      "display": "@AlgebraicCurve.Place.adicValuation",
      "card": "AlgebraicCurve.Place.adicValuation"
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
      "type": "prose",
      "md": " The uniformiser: the `Classical.choose` of an irreducible of the valuation\nsubring, and all every later statement knows about it is `ord = 1`. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.uniformizer",
      "zone": "A",
      "name": "AlgebraicCurve.Place.uniformizer",
      "display": "@AlgebraicCurve.Place.uniformizer",
      "card": "AlgebraicCurve.Place.uniformizer"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.uniformizerSubring'",
      "zone": "A",
      "name": "AlgebraicCurve.Place.uniformizerSubring'",
      "display": "@AlgebraicCurve.Place.uniformizerSubring'",
      "card": "AlgebraicCurve.Place.uniformizerSubring'"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_uniformizer",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_uniformizer",
      "display": "@AlgebraicCurve.Place.ord_uniformizer",
      "card": "AlgebraicCurve.Place.ord_uniformizer"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.uniformizer_ne_zero",
      "zone": "A",
      "name": "AlgebraicCurve.Place.uniformizer_ne_zero",
      "display": "@AlgebraicCurve.Place.uniformizer_ne_zero",
      "card": "AlgebraicCurve.Place.uniformizer_ne_zero"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=\n  v.ord_uniformizer",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) : Irreducible v.uniformizerSubring' :=\n  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec",
      "zone": "A",
      "doc": "The chosen irreducible, as an element of the valuation subring — the same\nchoice `uniformizer` takes, in the place where `Irreducible` makes sense."
    },
    {
      "type": "prose",
      "md": " The order is a valuation: additive on products, anti on inverses, and it does\nnot see units or constants at all. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_mul",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_mul",
      "display": "@AlgebraicCurve.Place.ord_mul",
      "card": "AlgebraicCurve.Place.ord_mul"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_inv",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_inv",
      "display": "@AlgebraicCurve.Place.ord_inv",
      "card": "AlgebraicCurve.Place.ord_inv"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_zpow",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_zpow",
      "display": "@AlgebraicCurve.Place.ord_zpow",
      "card": "AlgebraicCurve.Place.ord_zpow"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_algebraMap",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_algebraMap",
      "display": "@AlgebraicCurve.Place.ord_algebraMap",
      "card": "AlgebraicCurve.Place.ord_algebraMap"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_coe_unit",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_coe_unit",
      "display": "@AlgebraicCurve.Place.ord_coe_unit",
      "card": "AlgebraicCurve.Place.ord_coe_unit"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_unit_smul_zpow",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_unit_smul_zpow",
      "display": "@AlgebraicCurve.Place.ord_unit_smul_zpow",
      "card": "AlgebraicCurve.Place.ord_unit_smul_zpow"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (c : K) : v.ord (algebraMap K F c) = 0 :=\n  v.ord_algebraMap c",
      "zone": "A",
      "doc": "Every constant has order `0`: it is a unit at every place."
    },
    {
      "type": "prose",
      "md": " **What a place knows about an element.** An element of `F` is a unit times the\nuniformiser raised to its order; that decomposition is *all* `ord` records, and\nthe unit part is invisible to it (`ord_coe_unit`). This is the fact that the\ndifferential will fail to respect. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.exists_unit_mul_zpow",
      "zone": "A",
      "name": "AlgebraicCurve.Place.exists_unit_mul_zpow",
      "display": "@AlgebraicCurve.Place.exists_unit_mul_zpow",
      "card": "AlgebraicCurve.Place.exists_unit_mul_zpow"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) {f : F} (hf : f ≠ 0) :\n    ∃ u : v.toValuationSubringˣ,\n      f = ((u : v.toValuationSubring) : F) * (v.uniformizerSubring' : F) ^ (v.ord f) :=\n  v.exists_unit_mul_zpow hf (IsDiscreteValuationRing.exists_irreducible _).choose_spec",
      "zone": "A"
    },
    {
      "type": "prose",
      "md": " The residue data is local too, and *here* the place is already not enough: a\nDVR does not bound the degree of `κ(v)` over `K`. Finiteness is a class, one of\n`IsCurveOver`'s three axioms, and the port keeps it as a hypothesis rather than\nderiving it from the place. ",
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
      "raw": "#check @AlgebraicCurve.Place.deg",
      "zone": "A",
      "name": "AlgebraicCurve.Place.deg",
      "display": "@AlgebraicCurve.Place.deg",
      "card": "AlgebraicCurve.Place.deg"
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
      "md": "`Ω[F⁄K]` is the module of Kähler differentials of the *algebra* `F/K`, and `D` is\nthe universal derivation into it. Both are objects of the extension; neither\nmentions a place. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.D",
      "zone": "B",
      "name": "KaehlerDifferential.D",
      "display": "@KaehlerDifferential.D",
      "card": "KaehlerDifferential.D"
    },
    {
      "type": "prose",
      "md": " `D` is a derivation, so it is `K`-linear, it satisfies Leibniz, and it kills\nconstants. Two consequences are the whole story of this sheet: ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @Derivation.leibniz",
      "zone": "B",
      "name": "Derivation.leibniz",
      "display": "@Derivation.leibniz",
      "card": "Derivation.leibniz"
    },
    {
      "type": "check",
      "raw": "#check @Derivation.leibniz_pow",
      "zone": "B",
      "name": "Derivation.leibniz_pow",
      "display": "@Derivation.leibniz_pow",
      "card": "Derivation.leibniz_pow"
    },
    {
      "type": "check",
      "raw": "#check @Derivation.map_algebraMap",
      "zone": "B",
      "name": "Derivation.map_algebraMap",
      "display": "@Derivation.map_algebraMap",
      "card": "Derivation.map_algebraMap"
    },
    {
      "type": "example",
      "text": "example (c : K) : KaehlerDifferential.D K F (algebraMap K F c) = 0 :=\n  Derivation.map_algebraMap (KaehlerDifferential.D K F) c",
      "zone": "B",
      "doc": "Constants have no differential. Compare with `v.ord_algebraMap` in Zone A:\nthe place says `ord = 0`, the differential says `d = 0` — the same conclusion by\ntwo unrelated mechanisms."
    },
    {
      "type": "example",
      "text": "example (p : ℕ) [CharP F p] (a : F) : KaehlerDifferential.D K F (a ^ p) = 0 := by\n  rw [Derivation.leibniz_pow]\n  have hp : (p : F) = 0 := CharP.cast_eq_zero F p\n  rw [← Nat.cast_smul_eq_nsmul F p, hp, zero_smul]",
      "zone": "B",
      "doc": "**In characteristic `p`, `d` cannot see p-th powers.** `d (a ^ p) = 0` for\nevery `a`. So `d` is far from injective, and no amount of information about the\n*elements* of `F` (their orders included) can be turned into `d` by arithmetic:\nthe kernel of `d` is a subfield containing all p-th powers."
    },
    {
      "type": "prose",
      "md": " **How big is `Ω`?** Its dimension over `F` is the size of a *separating*\ntranscendence basis: with `s` algebraically independent and `F` separable over\n`K(s)`, the rank is `#s`. The word \"separating\" is the whole content — the\ntranscendence degree alone does not control the rank (D.1 below), and no place\ncan supply a separating transcendental. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.finrank_kaehler_eq_card_of_separating",
      "zone": "B",
      "name": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating",
      "display": "@AlgebraicCurve.finrank_kaehler_eq_card_of_separating",
      "card": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.finrank_kaehler_eq_card_of_separating'",
      "zone": "B",
      "name": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'",
      "display": "@AlgebraicCurve.finrank_kaehler_eq_card_of_separating'",
      "card": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.kaehlerAdjoinBasis",
      "zone": "B",
      "name": "AlgebraicCurve.kaehlerAdjoinBasis",
      "display": "@AlgebraicCurve.kaehlerAdjoinBasis",
      "card": "AlgebraicCurve.kaehlerAdjoinBasis"
    },
    {
      "type": "prose",
      "md": "The port does put a differential at every place, and it does so the only way\navailable: apply `D` to the chosen uniformiser. ",
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
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) :\n    v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " Everything else in this zone is *gated*. `DCoordGenerates` is the hypothesis\nthat this particular differential spans `Ω`; `differentialCoeff` and\n`ordDifferential` are total functions (junk outside the span), and the lemmas\nthat make them honest all require the class. ",
      "zone": "C"
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
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :\n    v.ordDifferential ω = v.ord (v.differentialCoeff ω) := rfl",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " The honest versions, each carrying `[v.DCoordGenerates]`: ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.exists_eq_smul_dCoord",
      "zone": "C",
      "name": "AlgebraicCurve.Place.exists_eq_smul_dCoord",
      "display": "@AlgebraicCurve.Place.exists_eq_smul_dCoord",
      "card": "AlgebraicCurve.Place.exists_eq_smul_dCoord"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.differentialCoeff_smul_dCoord",
      "zone": "C",
      "name": "AlgebraicCurve.Place.differentialCoeff_smul_dCoord",
      "display": "@AlgebraicCurve.Place.differentialCoeff_smul_dCoord",
      "card": "AlgebraicCurve.Place.differentialCoeff_smul_dCoord"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.differentialCoeff_unique",
      "zone": "C",
      "name": "AlgebraicCurve.Place.differentialCoeff_unique",
      "display": "@AlgebraicCurve.Place.differentialCoeff_unique",
      "card": "AlgebraicCurve.Place.differentialCoeff_unique"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.differentialCoeff_dCoord",
      "zone": "C",
      "name": "AlgebraicCurve.Place.differentialCoeff_dCoord",
      "display": "@AlgebraicCurve.Place.differentialCoeff_dCoord",
      "card": "AlgebraicCurve.Place.differentialCoeff_dCoord"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.differentialCoeff_zero",
      "zone": "C",
      "name": "AlgebraicCurve.Place.differentialCoeff_zero",
      "display": "@AlgebraicCurve.Place.differentialCoeff_zero",
      "card": "AlgebraicCurve.Place.differentialCoeff_zero"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ordDifferential_smul",
      "zone": "C",
      "name": "AlgebraicCurve.Place.ordDifferential_smul",
      "display": "@AlgebraicCurve.Place.ordDifferential_smul",
      "card": "AlgebraicCurve.Place.ordDifferential_smul"
    },
    {
      "type": "prose",
      "md": " And the two that need `Nontrivial Ω` as well, i.e. a nonzero differential: the\nrank-one axiom of Zone D is what supplies that instance. ",
      "zone": "C"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.dCoord_ne_zero",
      "zone": "C",
      "name": "AlgebraicCurve.Place.dCoord_ne_zero",
      "display": "@AlgebraicCurve.Place.dCoord_ne_zero",
      "card": "AlgebraicCurve.Place.dCoord_ne_zero"
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
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K])\n    (h : ¬ ∃ f : F, ω = f • v.dCoord) : v.differentialCoeff ω = 0 := by\n  simp only [AlgebraicCurve.Place.differentialCoeff]\n  exact dite_eq_right h",
      "zone": "C",
      "doc": "The junk branch, live: when `ω` is not a multiple of `d t_v`, the coefficient\nis defined to be `0`. So `ordDifferential` silently records \"no pole, no zero\"\nthere — a value, not a truth."
    },
    {
      "type": "prose",
      "md": " **The crux.** Two elements with the same order have unrelated differentials.\n`u * t_v` is a uniformiser as soon as `u` is a unit, so the place cannot tell the\ntwo apart — while `d` differs by the Leibniz term `t_v • d u`. ",
      "zone": "C"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (u : F) (hu : u ≠ 0) (hord : v.ord u = 0) :\n    v.ord (u * v.uniformizer) = 1 := by\n  rw [v.ord_mul hu v.uniformizer_ne_zero, hord, v.ord_uniformizer]\n  ring",
      "zone": "C"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (u : F) :\n    KaehlerDifferential.D K F (u * v.uniformizer)\n      = u • KaehlerDifferential.D K F v.uniformizer\n        + v.uniformizer • KaehlerDifferential.D K F u :=\n  Derivation.leibniz (KaehlerDifferential.D K F) u v.uniformizer",
      "zone": "C",
      "doc": "The other half of the crux: the same substitution moves the differential, by a\nterm the place has no record of."
    },
    {
      "type": "prose",
      "md": " So `d t_v` is a differential *of a choice*: the choice of uniformiser is a\n`Classical.choose`, and the place's data (`ord`) is invariant under the change\nthat moves `d`. Zone A's `exists_unit_mul_zpow` says every element is\n`u · t_v^ord`, so the place's total knowledge of an element is blind to the unit\n— which is the part that `d` sees. ",
      "zone": "C"
    },
    {
      "type": "prose",
      "md": " The last piece of the bridge is the *finite support* of the order function.\n`HasCanonicalDivisor` says: for a nonzero `ω` there is a divisor `D` whose value\nat `v` is `v.ordDifferential ω`, for every place. That is a statement about the\njunk function above, and it is only meaningful when the coefficient is honest at\nevery place. ",
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
      "type": "prose",
      "md": "There are exactly three things a place does not give, and the port carries each\none separately. ",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " ### D.1 — `Ω` may not be a line\n\n`kaehler_free_rank_one` is a field of `IsCurveOver`; the pin also states it\nstandalone, and the port keeps both names. Read them as the same proposition: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.KaehlerRankOne",
      "zone": "D",
      "name": "AlgebraicCurve.KaehlerRankOne",
      "display": "@AlgebraicCurve.KaehlerRankOne",
      "card": "AlgebraicCurve.KaehlerRankOne"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "display": "@AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "card": "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.IsCurveOver K F] : AlgebraicCurve.KaehlerRankOne K F :=\n  AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " And the class is literally the three pieces, which is why the axiom is visible\nas a field: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
      "display": "@AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
      "card": "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne"
    },
    {
      "type": "example",
      "text": "example [AlgebraicCurve.HasPrincipalDivisors K F]\n    [∀ v : AlgebraicCurve.Place K F, v.FiniteResidue]\n    (h : AlgebraicCurve.KaehlerRankOne K F) : AlgebraicCurve.IsCurveOver K F :=\n  AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne h",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " Two consequences worth naming. Rank one **produces a nonzero differential**\n(the port derives `Nontrivial Ω` from it, rather than assuming it), and it\n**forces the transcendence degree to be one**: `trdeg_le_one` spends the\nseparating-basis theorem of Zone B, and `one_le_trdeg` spends `Nontrivial Ω`.\nThe converse fails: the counterexample below has `trdeg = 1` and rank two. ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "display": "@AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
      "card": "AlgebraicCurve.IsCurveOver.instNontrivialKaehler"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.one_le_trdeg",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.one_le_trdeg",
      "display": "@AlgebraicCurve.IsCurveOver.one_le_trdeg",
      "card": "AlgebraicCurve.IsCurveOver.one_le_trdeg"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.trdeg_le_one",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.trdeg_le_one",
      "display": "@AlgebraicCurve.IsCurveOver.trdeg_le_one",
      "card": "AlgebraicCurve.IsCurveOver.trdeg_le_one"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "display": "@AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
      "card": "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField"
    },
    {
      "type": "prose",
      "md": " Why it cannot be derived from place data: a place is a structure on `F` alone\n(Zone A), while the rank of `Ω` is a property of the *extension*. The standard\ncounterexample, not formalised here — take `k` of characteristic `p`,\n`K = k(X)`, and `F = K(x)(t)` with `x ^ p = X` and `t` transcendental over\n`K(x)`. Then:\n\n* `trdeg(F/K) = 1`, and every place still has a uniformiser;\n* `Ω[K(x)/K]` is free of rank one on `d x`: the defining relation `x ^ p = X`\n  differentiates to `p x ^ (p - 1) d x = 0`, which is *no* relation in\n  characteristic `p` — the p-th-power blindness of Zone B;\n* `F = K(x)(t)` splits `Ω` as `Ω[K(x)/K] ⊗ F` plus `F · d t`, so\n  `finrank_F Ω[F⁄K] = 2`.\n\nSo a one-variable function field can have a two-dimensional `Ω`, no uniformiser\nis any the wiser, and no `ω` generates. This is the field that `kaehler_free_rank_one`\nexcludes, and the reason it has to be an axiom rather than a theorem about\nplaces. The port's positive control is the rational function field: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.kaehlerRankOne_ratFunc",
      "zone": "D",
      "name": "AlgebraicCurve.kaehlerRankOne_ratFunc",
      "display": "@AlgebraicCurve.kaehlerRankOne_ratFunc",
      "card": "AlgebraicCurve.kaehlerRankOne_ratFunc"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
      "zone": "D",
      "name": "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
      "display": "@AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
      "card": "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne"
    },
    {
      "type": "prose",
      "md": " ### D.2 — even a line may not be generated by `d t_v`\n\nGrant `Ω` free of rank one. `d t_v` is *an* element of a line, so it is either a\ngenerator or zero — and which one is not a place-level fact. That is\n`DCoordGenerates`, quantified at every place in exactly the rungs that name a\ncanonical divisor.\n\nThe port's route from the axiom to the places is short, and worth reading in\norder: a *separating transcendental* exists — perfectness plus rank one, which\npins the transcendence degree to one (D.1) — the differential of that\ntranscendental is nonzero and spans `Ω`, and from a global generator the\ngeneration at every place follows. Note the direction: the transcendental\ngenerates, the places inherit: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.IsCurveOver.exists_separating_transcendental",
      "zone": "D",
      "name": "AlgebraicCurve.IsCurveOver.exists_separating_transcendental",
      "display": "@AlgebraicCurve.IsCurveOver.exists_separating_transcendental",
      "card": "AlgebraicCurve.IsCurveOver.exists_separating_transcendental"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.D_ne_zero_of_transcendental",
      "zone": "D",
      "name": "KaehlerDifferential.D_ne_zero_of_transcendental",
      "display": "@KaehlerDifferential.D_ne_zero_of_transcendental",
      "card": "KaehlerDifferential.D_ne_zero_of_transcendental"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.span_D_eq_top_of_transcendental",
      "zone": "D",
      "name": "KaehlerDifferential.span_D_eq_top_of_transcendental",
      "display": "@KaehlerDifferential.span_D_eq_top_of_transcendental",
      "card": "KaehlerDifferential.span_D_eq_top_of_transcendental"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
      "zone": "D",
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
      "display": "@AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
      "card": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "zone": "D",
      "name": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "display": "@AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
      "card": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField"
    },
    {
      "type": "prose",
      "md": " And here is the rung's own hypothesis list, printed so that the per-place\nquantifier is visible: ",
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
      "md": " ### D.3 — the order function may not have finite support\n\nThe last gap is the one `HasCanonicalDivisor` closes, and the port *derives* it\nrather than assuming it, from the curve axioms over a perfect field. Read the\nproof's opening moves: it first derives the per-place generation that D.2 left as\na hypothesis (`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`), then takes a\nseparating transcendental, and only then proves that the order function has\nfinite support. So D.1 and D.2 are not extra assumptions on this route — they are\n*theorems* once the constant field is perfect: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "zone": "D",
      "name": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "display": "@AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "card": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver"
    },
    {
      "type": "example",
      "text": "example [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :\n    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=\n  AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": " The residue side carries its own, *separate*, per-place inputs — the same\nlesson in a different coordinate. The K residue model needs a canonical local\nresidue datum at every place, on top of the canonical divisor and the generation;\nthe nonvanishing of the Weil/Kähler functional needs the trace to be nonzero at\nevery place: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasCanonicalLocalResidueKStar",
      "zone": "D",
      "name": "AlgebraicCurve.HasCanonicalLocalResidueKStar",
      "display": "@AlgebraicCurve.HasCanonicalLocalResidueKStar",
      "card": "AlgebraicCurve.HasCanonicalLocalResidueKStar"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.CanonicalLocalResidueDataK",
      "zone": "D",
      "name": "AlgebraicCurve.Place.CanonicalLocalResidueDataK",
      "display": "@AlgebraicCurve.Place.CanonicalLocalResidueDataK",
      "card": "AlgebraicCurve.Place.CanonicalLocalResidueDataK"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasSeparableResidue",
      "zone": "D",
      "name": "AlgebraicCurve.HasSeparableResidue",
      "display": "@AlgebraicCurve.HasSeparableResidue",
      "card": "AlgebraicCurve.HasSeparableResidue"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.ResidueTheoremK",
      "zone": "D",
      "name": "AlgebraicCurve.ResidueTheoremK",
      "display": "@AlgebraicCurve.ResidueTheoremK",
      "card": "AlgebraicCurve.ResidueTheoremK"
    },
    {
      "type": "prose",
      "md": " Perfectness supplies both, which is why the wrapper stack of the hierarchy\nsheet can drop them: ",
      "zone": "D"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.HasSeparableResidue.of_perfectField",
      "zone": "D",
      "name": "AlgebraicCurve.HasSeparableResidue.of_perfectField",
      "display": "@AlgebraicCurve.HasSeparableResidue.of_perfectField",
      "card": "AlgebraicCurve.HasSeparableResidue.of_perfectField"
    },
    {
      "type": "example",
      "text": "example [PerfectField K] [∀ v : AlgebraicCurve.Place K F, v.FiniteResidue] :\n    AlgebraicCurve.HasSeparableResidue K F :=\n  AlgebraicCurve.HasSeparableResidue.of_perfectField",
      "zone": "D"
    },
    {
      "type": "prose",
      "md": "* **Delete `[DCoordGenerates]`** from `exists_eq_smul_dCoord` in Zone C and the\n  statement becomes false as a universally quantified claim: there is no single\n  `f` with `ω = f • d t_v` for every `ω` unless `d t_v` spans. That is the whole\n  content of the class, and the reason it cannot be an instance.\n\n* **Delete `[Nontrivial Ω]`** from `dCoord_ne_zero`: with `Ω` subsingleton every\n  differential is zero, so `d t_v ≠ 0` needs the rank-one axiom (D.1), not just\n  generation.\n\n* **Change the uniformiser.** `u * t_v` has order `1` for every unit `u`\n  (`ord_mul`, `ord_coe_unit`), but `d (u * t_v)` picks up the Leibniz term\n  `t_v • d u`. If `u` is a constant the term dies (`Derivation.map_algebraMap`),\n  so to see a change you need a unit outside the image of `K` — which `ord`\n  cannot distinguish from a constant. Try writing the proof for\n  `u = algebraMap K F c`: it succeeds only *because* constants have no\n  differential.\n\n* **Replace `CharP F p`** in the p-th-power example by `CharZero F` and watch the\n  proof die at the step `(p : F) = 0`. In characteristic zero `d (a ^ n) =\n  n • a ^ (n - 1) • d a` is not zero for a transcendental `a`, so `d` no longer\n  has the p-th powers in its kernel. Differentials detect p-th powers only in\n  characteristic `p`, which is why the inseparable counterexample of D.1 lives\n  there.\n\n* **`differentialCoeff` is total.** It is an `if`, so it returns `0` for any `ω`\n  outside the span; `ordDifferential` then reports `0`, i.e. \"no pole, no zero\".\n  `HasCanonicalDivisor` reads that total function at every place, so the\n  generation hypothesis in D.2 is what keeps the divisor from silently losing the\n  places where the coefficient is junk. The same pattern as `genus` and `finrank`\n  in the hierarchy sheet: a total definition with a junk branch, plus the\n  hypothesis that the branch is never taken.\n\n* **One layer down.** The *local* statement — `κ(v)`-dimension of `m_v / m_v²` is\n  one, `m_v = (t_v)` — is free from the DVR structure, and `ord_uniformizer` is\n  its `F`-side shadow. What is *not* free is the passage from that local\n  one-dimensionality to a generator of the global `Ω`. Compare the two `#check`s:\n  `IsDiscreteValuationRing.exists_irreducible` (Zone A, no curve hypotheses) and\n  `DCoordGenerates` (Zone C, a hypothesis on every rung). ",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "Oldest first. Each entry: question, one-line answer, and a pointer to the zone\nthat was edited.\n\n* (2026-10-23) *Worksheet created.*\n* (2026-10-23) **Q1.** A place has a uniformiser `t_v`; why doesn't that give a\n  differential, and why is `kaehler_free_rank_one` an axiom? — It does give an\n  *element* `d t_v` (`dCoord`) and an order, but not a basis: the rank of `Ω` is\n  a property of the extension (D.1), generation at a place is a separate\n  hypothesis (D.2), and finite support of the order function is a theorem over a\n  perfect field (D.3). Zone A vs Zone C.\n* (2026-10-23) **Q2.** Is the axiom \"there exists a nonzero differential\"? — No:\n  it is \"`Ω` is a line\", which is strictly stronger. Existence is *derived*\n  (`instNontrivialKaehler`), and it would not give the coefficient, the order, or\n  the independence of the choice of `t_v`. See D.1.\n* (2026-10-23) **Q3.** The place knows `f` only as `u · t_v^ord`; doesn't\n  `ord` plus the uniformiser determine `d f`? — No: `d` is a derivation, not a\n  function of the order. `d (u · t_v)` carries `t_v · d u`, which `ord` cannot\n  see; the two examples in Zone C are that statement, one for `ord` and one for\n  `d`.\n* (2026-10-23) **Q4.** Why is `differentialCoeff` total (with a `0` branch)\n  rather than requiring `DCoordGenerates`? — So that `ordDifferential` and\n  `HasCanonicalDivisor` are definitions rather than conditional statements; the\n  hypothesis is then a class instance that the honest lemmas require. The junk\n  branch is the price, and Zone E's poke shows how it is neutralised. ",
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
    "c",
    "f",
    "hf",
    "u",
    "p",
    "a",
    "ω",
    "h",
    "hu",
    "hord"
  ],
  "seed_cards": ["AlgebraicCurve.HasCanonicalDivisor","AlgebraicCurve.HasCanonicalLocalResidueKStar","AlgebraicCurve.HasSeparableResidue","AlgebraicCurve.HasSeparableResidue.of_perfectField","AlgebraicCurve.IsCurveOver.exists_separating_transcendental","AlgebraicCurve.IsCurveOver.instNontrivialKaehler","AlgebraicCurve.IsCurveOver.kaehler_free_rank_one","AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne","AlgebraicCurve.IsCurveOver.one_le_trdeg","AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField","AlgebraicCurve.IsCurveOver.trdeg_le_one","AlgebraicCurve.KaehlerRankOne","AlgebraicCurve.Place","AlgebraicCurve.Place.CanonicalLocalResidueDataK","AlgebraicCurve.Place.DCoordGenerates","AlgebraicCurve.Place.FiniteResidue","AlgebraicCurve.Place.ResidueField","AlgebraicCurve.Place.adicValuation","AlgebraicCurve.Place.dCoord","AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField","AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop","AlgebraicCurve.Place.dCoord_ne_zero","AlgebraicCurve.Place.deg","AlgebraicCurve.Place.differentialCoeff","AlgebraicCurve.Place.differentialCoeff_dCoord","AlgebraicCurve.Place.differentialCoeff_smul_dCoord","AlgebraicCurve.Place.differentialCoeff_unique","AlgebraicCurve.Place.differentialCoeff_zero","AlgebraicCurve.Place.exists_eq_smul_dCoord","AlgebraicCurve.Place.exists_unit_mul_zpow","AlgebraicCurve.Place.gate_ordDifferential_dCoord","AlgebraicCurve.Place.heightOneSpectrum","AlgebraicCurve.Place.ord","AlgebraicCurve.Place.ordDifferential","AlgebraicCurve.Place.ordDifferential_smul","AlgebraicCurve.Place.ord_algebraMap","AlgebraicCurve.Place.ord_coe_unit","AlgebraicCurve.Place.ord_inv","AlgebraicCurve.Place.ord_mul","AlgebraicCurve.Place.ord_uniformizer","AlgebraicCurve.Place.ord_unit_smul_zpow","AlgebraicCurve.Place.ord_zpow","AlgebraicCurve.Place.uniformizer","AlgebraicCurve.Place.uniformizerSubring'","AlgebraicCurve.Place.uniformizer_ne_zero","AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne","AlgebraicCurve.ResidueTheoremK","AlgebraicCurve.WeilDualityAdelic","AlgebraicCurve.canonicalDivisorOf","AlgebraicCurve.canonicalDivisorOf_apply","AlgebraicCurve.finrank_kaehler_eq_card_of_separating","AlgebraicCurve.finrank_kaehler_eq_card_of_separating'","AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver","AlgebraicCurve.kaehlerAdjoinBasis","AlgebraicCurve.kaehlerRankOne_ratFunc","Classical.choose","Derivation.leibniz","Derivation.leibniz_pow","Derivation.map_algebraMap","Irreducible","IsDiscreteValuationRing.exists_irreducible","KaehlerDifferential.D","KaehlerDifferential.D_ne_zero_of_transcendental","KaehlerDifferential.span_D_eq_top_of_transcendental"],
  "card_count": 166,
  "modules": ["FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor","FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","FLTForHuman.AlgebraicCurve.Defs.Divisor","FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental","FLTForHuman.AlgebraicCurve.Defs.LocalResidue","FLTForHuman.AlgebraicCurve.Defs.Place","FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows","FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental","FLTForHuman.AlgebraicCurve.LocalResidue.Instance","FLTForHuman.AlgebraicCurve.P1.DXCoeff","FLTForHuman.AlgebraicCurve.P1.UnitFinite","Init.Classical","Init.Core","Init.Data.Cast","Init.Data.Int.Basic","Init.Prelude","Mathlib.Algebra.Algebra.Basic","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Algebra.Equiv","Mathlib.Algebra.Algebra.Subalgebra.Basic","Mathlib.Algebra.Algebra.Subalgebra.Lattice","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.Group.Action.Defs","Mathlib.Algebra.Group.Irreducible.Defs","Mathlib.Algebra.Group.Monoid","Mathlib.Algebra.Group.Pi.Basic","Mathlib.Algebra.Group.TypeTags.Basic","Mathlib.Algebra.Group.Units.Defs","Mathlib.Algebra.Group.WithOne.Defs","Mathlib.Algebra.GroupWithZero.WithZero","Mathlib.Algebra.Module.Defs","Mathlib.Algebra.Module.LinearMap.Defs","Mathlib.Algebra.Module.Pi","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.MonoidAlgebra.Basic","Mathlib.Algebra.MonoidAlgebra.Defs","Mathlib.Algebra.MvPolynomial.Basic","Mathlib.Algebra.Order.Monoid.TypeTags","Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","Mathlib.Algebra.Polynomial.AlgebraMap","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Basic.Nontrivial.Defs","Mathlib.Data.Finset.Card","Mathlib.Data.Finset.Defs","Mathlib.Data.Finsupp.Defs","Mathlib.Data.Set.Defs","Mathlib.Data.Set.Operations","Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","Mathlib.FieldTheory.IntermediateField.Basic","Mathlib.FieldTheory.Perfect","Mathlib.FieldTheory.RatFunc.Defs","Mathlib.FieldTheory.Separable","Mathlib.LinearAlgebra.Basis.Defs","Mathlib.LinearAlgebra.Dimension.Finrank","Mathlib.LinearAlgebra.Dual.Defs","Mathlib.LinearAlgebra.FiniteDimensional.Defs","Mathlib.LinearAlgebra.FreeModule.Basic","Mathlib.LinearAlgebra.Span.Defs","Mathlib.LinearAlgebra.TensorProduct.Basis","Mathlib.LinearAlgebra.TensorProduct.Defs","Mathlib.Order.Notation","Mathlib.RingTheory.Algebraic.Defs","Mathlib.RingTheory.AlgebraicIndependent.Basic","Mathlib.RingTheory.AlgebraicIndependent.Defs","Mathlib.RingTheory.DedekindDomain.AdicValuation","Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","Mathlib.RingTheory.Derivation.Basic","Mathlib.RingTheory.DiscreteValuationRing.Basic","Mathlib.RingTheory.EssentialFiniteness","Mathlib.RingTheory.Etale.Kaehler","Mathlib.RingTheory.Kaehler.Basic","Mathlib.RingTheory.Kaehler.Polynomial","Mathlib.RingTheory.LocalRing.ResidueField.Defs","Mathlib.RingTheory.Valuation.Basic","Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing","Mathlib.RingTheory.Valuation.ValuationSubring","Mathlib.SetTheory.Cardinal.Defs"]
};
