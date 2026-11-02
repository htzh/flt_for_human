window.PLAY_WORKSHEETS = window.PLAY_WORKSHEETS || {};
window.PLAY_WORKSHEETS["PlacesAndDifferentials"] = {
  "slug": "PlacesAndDifferentials",
  "file": "lean/play/PlacesAndDifferentials.lean",
  "title": "places and differentials",
  "tagline": "why a uniformiser is not a differential",
  "subject": "the two halves of the local theory and the gap between them: a place always has a uniformiser and an order, a differential is a global derivation, and nothing in the place data produces one. That gap is why `IsCurveOver` carries `kaehler_free_rank_one` as an axiom, and why every rung that names a canonical divisor carries `[∀ v, v.DCoordGenerates]` per place.",
  "intro": "A place gives an order `ord_v` and a uniformiser `t_v`; a differential lives in the Kähler module `Ω[F⁄K]`, which is an object of the whole field extension and mentions no place — literally so: `Ω[F⁄K]` is `I ⧸ I²` for `I` the ideal of the diagonal of `F ⊗[K] F`, so the construction sees nothing but the ring map `K → F`. This sheet separates the two, exhibits each gate the port puts between them (`dCoord`, `DCoordGenerates`, `differentialCoeff`, `ordDifferential`, `HasCanonicalDivisor`), shows that the same order admits different differentials, and lands on the axiom that no amount of place data can supply: `kaehler_free_rank_one`.",
  "reads": "FLTForHuman/AlgebraicCurve/Defs/Place.lean, Defs/CanonicalDivisor.lean, Defs/LocalResidue.lean, Defs/KaehlerTranscendental.lean, P1/DXCoeff.lean, IsCurveOver/SeparatingTranscendental.lean, Canonical/HasCanonicalDivisor.lean, Defs/RiemannRochRows.lean",
  "pin": "Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean (the `Place` structure and `ord`), Definitions/Def_ModularCurve_CanonicalDivisor.lean, Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean, Definitions/Def_AlgebraicCurve_IsCurveOver.lean, P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean, P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean, P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean, all at aa2d8b3",
  "check": "cd lean && lake env lean play/PlacesAndDifferentials.lean   (~9 s, oleans warm)",
  "status": "open",
  "date": "2026-10-23",
  "imports": ["FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly"],
  "opens": ["KaehlerDifferential","WithZero","TensorProduct","Polynomial"],
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
      "type": "prose",
      "md": "`ᵐ⁰` is *scoped* notation (`scoped notation M \"ᵐ⁰\" => WithZero (Multiplicative M)`),\nso `ℤᵐ⁰` needs the scope opened; the port's `Place` opens `WithZero` too, which is\nwhy its sources print the value group as `ℤᵐ⁰` rather than the expansion.",
      "zone": null
    },
    {
      "type": "code",
      "text": "open scoped WithZero",
      "zone": null
    },
    {
      "type": "prose",
      "md": "`⊗` and `⊗ₜ` are scoped notation for `TensorProduct`; Zone B's construction of\n`Ω` is a tensor product, so the scope is opened here rather than at each use.",
      "zone": null
    },
    {
      "type": "code",
      "text": "open scoped TensorProduct",
      "zone": null
    },
    {
      "type": "prose",
      "md": "`R[X]` is scoped notation for `Polynomial R`; the model of `Ω` in Zone B is the\npolynomial ring, `Ω[K[X]⁄K] ≅ K[X]`, so the scope is opened here too.",
      "zone": null
    },
    {
      "type": "code",
      "text": "open scoped Polynomial",
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
      "raw": "#check @AlgebraicCurve.Place.uniformizerSubring",
      "zone": "A",
      "name": "AlgebraicCurve.Place.uniformizerSubring",
      "display": "@AlgebraicCurve.Place.uniformizerSubring",
      "card": "AlgebraicCurve.Place.uniformizerSubring"
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
      "type": "prose",
      "md": " **What \"uniformiser\" means, and the rewrite that says it.** In a DVR an element is\nirreducible exactly when it generates the maximal ideal, and mathlib states the two\nspellings as one `iff`. Everything `ord` rests on is that `rw`: the `Irreducible` that\n`uniformizerSubring` *is* becomes the ideal equality `m_v = (t_v)` that the valuation\nlemmas *consume* and never undo. ",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) (ϖ : v.toValuationSubring) :\n    Irreducible ϖ ↔ IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {ϖ} :=\n  IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=\n  v.ord_uniformizer",
      "zone": "A"
    },
    {
      "type": "example",
      "text": "example (v : AlgebraicCurve.Place K F) :\n    IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {v.uniformizerSubring} := by\n  rw [← IsDiscreteValuationRing.irreducible_iff_uniformizer]\n  exact (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec",
      "zone": "A",
      "doc": "Right-to-left on the chosen irreducible: `m_v = (t_v)`. This is the direction the\nvaluation theorems want — `intValuation_singleton` takes an ideal equality, and neither\nit nor `ord` ever sees `Irreducible`."
    },
    {
      "type": "prose",
      "md": " Where the same `iff` works *inside* mathlib: `exists_irreducible` is `simp_rw` on it\nfollowed by principality, and that is the proof term the `Classical.choose` above\nconsumes. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @IsDiscreteValuationRing.irreducible_iff_uniformizer",
      "zone": "A",
      "name": "IsDiscreteValuationRing.irreducible_iff_uniformizer",
      "display": "@IsDiscreteValuationRing.irreducible_iff_uniformizer",
      "card": "IsDiscreteValuationRing.irreducible_iff_uniformizer"
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
      "raw": "#check @Irreducible.maximalIdeal_eq",
      "zone": "A",
      "name": "Irreducible.maximalIdeal_eq",
      "display": "@Irreducible.maximalIdeal_eq",
      "card": "Irreducible.maximalIdeal_eq"
    },
    {
      "type": "prose",
      "md": " The uniformiser's `F`-side order is the `ord = 1` of `ord_uniformizer`; the\nsubring-side spelling lives with the canonical-divisor layer. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_uniformizerSubring",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_uniformizerSubring",
      "display": "@AlgebraicCurve.Place.ord_uniformizerSubring",
      "card": "AlgebraicCurve.Place.ord_uniformizerSubring"
    },
    {
      "type": "prose",
      "md": " **`ord` is `log` of the adic valuation** — one bookkeeping layer, and nothing in\nthis sheet turns on anything beyond it. `v.adicValuation : F → ℤᵐ⁰` is the `v`-adic\nvaluation, its value group written multiplicatively (`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`),\nso that a value of `n` is `exp n` and `1 = exp 0` is \"unit\"; `WithZero.log` is the inverse\nof `exp` *off* `0` (junk value `log 0 = 0`); and\n\n  `v.ord f = -(WithZero.log (v.adicValuation f))`.\n\nTwo conventions are packed into that line, and neither carries content beyond notation.\nMathlib's valuation puts the ring *below* `1` (`intValuation_le_one`), so the uniformiser\nhas value `exp (-1)`, not `exp 1`. And the outer minus turns a *small* valuation into a\n**vanishing order**: `ord > 0` is a zero, `ord < 0` a pole, which is the divisor\nconvention `(f) = ∑_v ord_v(f) · v`. Everything else is `log` being additive. ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @WithZero.exp",
      "zone": "A",
      "name": "WithZero.exp",
      "display": "@WithZero.exp",
      "card": "WithZero.exp"
    },
    {
      "type": "check",
      "raw": "#check @WithZero.log",
      "zone": "A",
      "name": "WithZero.log",
      "display": "@WithZero.log",
      "card": "WithZero.log"
    },
    {
      "type": "check",
      "raw": "#check @WithZero.log_mul",
      "zone": "A",
      "name": "WithZero.log_mul",
      "display": "@WithZero.log_mul",
      "card": "WithZero.log_mul"
    },
    {
      "type": "check",
      "raw": "#check @WithZero.logEquiv",
      "zone": "A",
      "name": "WithZero.logEquiv",
      "display": "@WithZero.logEquiv",
      "card": "WithZero.logEquiv"
    },
    {
      "type": "check",
      "raw": "#check @IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
      "zone": "A",
      "name": "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
      "display": "@IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
      "card": "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one"
    },
    {
      "type": "check",
      "raw": "#check @IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
      "zone": "A",
      "name": "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
      "display": "@IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
      "card": "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem"
    },
    {
      "type": "prose",
      "md": " The rest of the API, one line each. All of it is `log` additive, `log ∘ exp = id`, and\nthe junk `log 0 = 0`; Zone C uses `ord_mul`, `ord_zpow` and `ord_uniformizer`, the rest is\nhere so the names are findable: ",
      "zone": "A"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_mul          -- additive on products",
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
      "raw": "#check @AlgebraicCurve.Place.ord_algebraMap   -- constants are units",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_algebraMap",
      "display": "@AlgebraicCurve.Place.ord_algebraMap",
      "card": "AlgebraicCurve.Place.ord_algebraMap"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.mem_iff_ord_nonneg   -- regular at `v` ⟺ `ord ≥ 0`",
      "zone": "A",
      "name": "AlgebraicCurve.Place.mem_iff_ord_nonneg",
      "display": "@AlgebraicCurve.Place.mem_iff_ord_nonneg",
      "card": "AlgebraicCurve.Place.mem_iff_ord_nonneg"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_zero",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_zero",
      "display": "@AlgebraicCurve.Place.ord_zero",
      "card": "AlgebraicCurve.Place.ord_zero"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.min_ord_le_ord_add",
      "zone": "A",
      "name": "AlgebraicCurve.Place.min_ord_le_ord_add",
      "display": "@AlgebraicCurve.Place.min_ord_le_ord_add",
      "card": "AlgebraicCurve.Place.min_ord_le_ord_add"
    },
    {
      "type": "prose",
      "md": " **What a place knows about an element**, and the one fact Zone C leans on: `f` is a\nunit times `t_v ^ ord f`, and the unit is invisible to `ord` (`ord_coe_unit`). That is\nexactly what the differential will fail to respect. ",
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
      "type": "check",
      "raw": "#check @AlgebraicCurve.Place.ord_coe_unit",
      "zone": "A",
      "name": "AlgebraicCurve.Place.ord_coe_unit",
      "display": "@AlgebraicCurve.Place.ord_coe_unit",
      "card": "AlgebraicCurve.Place.ord_coe_unit"
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
      "md": "`Ω[F⁄K]` is notation for `KaehlerDifferential K F`, the module of Kähler\ndifferentials of the *algebra* `F/K`; `D` is the universal derivation into it. Both\nare objects of the extension; neither mentions a place. The notation is definitional,\nso the equation below is `rfl` and every later statement about `Ω` is literally a\nstatement about the declaration: ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example : Ω[F⁄K] = KaehlerDifferential K F := rfl",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential",
      "zone": "B",
      "name": "KaehlerDifferential",
      "display": "@KaehlerDifferential",
      "card": "KaehlerDifferential"
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
      "md": " **What the definition actually is: the ideal of the diagonal.**\n\nThe `#check` above is silent about the construction, and the construction is the\nanswer to \"why does a differential exist at all\". `S ⊗[R] S` is the *coproduct* of\n`S` with itself in `R`-algebras: it carries two commuting copies of `S`, the left one\n`s ↦ s ⊗ₜ 1` and the right one `s ↦ 1 ⊗ₜ s` (`includeLeft`, `includeRight`), and\n`lmul'` (spelled `Algebra.TensorProduct.lmul'`: a namespace one level below the one\n`open KaehlerDifferential` reaches, so the short name is unknown) is the unique\n`R`-algebra map out of it that composes with *either* copy to the identity. Hence\n\n  `I := KaehlerDifferential.ideal R S = ker lmul'`   (`RingHom.ker`),\n\nthe ideal saying *the two copies agree*: the ideal of the diagonal, the ring-level\nform of \"vanishes on `Δ`\". Mathlib proves it is generated by the differences of the\ncopies, which is the algebraic content of the name: ",
      "zone": "B"
    },
    {
      "type": "print",
      "raw": "#print KaehlerDifferential.ideal",
      "zone": "B",
      "name": "KaehlerDifferential.ideal",
      "display": "KaehlerDifferential.ideal",
      "card": "KaehlerDifferential.ideal"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.lmul'",
      "zone": "B",
      "name": "Algebra.TensorProduct.lmul'",
      "display": "@Algebra.TensorProduct.lmul'",
      "card": "Algebra.TensorProduct.lmul'"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.lmul'_apply_tmul",
      "zone": "B",
      "name": "Algebra.TensorProduct.lmul'_apply_tmul",
      "display": "@Algebra.TensorProduct.lmul'_apply_tmul",
      "card": "Algebra.TensorProduct.lmul'_apply_tmul"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.includeLeft",
      "zone": "B",
      "name": "Algebra.TensorProduct.includeLeft",
      "display": "@Algebra.TensorProduct.includeLeft",
      "card": "Algebra.TensorProduct.includeLeft"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.includeRight",
      "zone": "B",
      "name": "Algebra.TensorProduct.includeRight",
      "display": "@Algebra.TensorProduct.includeRight",
      "card": "Algebra.TensorProduct.includeRight"
    },
    {
      "type": "check",
      "raw": "#check @RingHom.ker",
      "zone": "B",
      "name": "RingHom.ker",
      "display": "@RingHom.ker",
      "card": "RingHom.ker"
    },
    {
      "type": "check",
      "raw": "#check @RingHom.mem_ker",
      "zone": "B",
      "name": "RingHom.mem_ker",
      "display": "@RingHom.mem_ker",
      "card": "RingHom.mem_ker"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.ideal",
      "zone": "B",
      "name": "KaehlerDifferential.ideal",
      "display": "@KaehlerDifferential.ideal",
      "card": "KaehlerDifferential.ideal"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.one_smul_sub_smul_one_mem_ideal",
      "zone": "B",
      "name": "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal",
      "display": "@KaehlerDifferential.one_smul_sub_smul_one_mem_ideal",
      "card": "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.span_range_eq_ideal",
      "zone": "B",
      "name": "KaehlerDifferential.span_range_eq_ideal",
      "display": "@KaehlerDifferential.span_range_eq_ideal",
      "card": "KaehlerDifferential.span_range_eq_ideal"
    },
    {
      "type": "example",
      "text": "example : Ω[F⁄K] = (KaehlerDifferential.ideal K F).Cotangent := rfl",
      "zone": "B",
      "doc": "`Ω` *is* the cotangent module of the diagonal ideal — no lemma stands between\nthe two declarations, so `rfl` suffices. This is the definition the rest of the\nsheet's `Ω` is: `I ⧸ I²`."
    },
    {
      "type": "example",
      "text": "example (a b : F) : Algebra.TensorProduct.lmul' K (a ⊗ₜ[K] b) = a * b :=\n  Algebra.TensorProduct.lmul'_apply_tmul a b",
      "zone": "B",
      "doc": "The two copies of `F` inside `F ⊗[K] F`, and the map that sets them equal."
    },
    {
      "type": "example",
      "text": "example :\n    KaehlerDifferential.ideal K F\n      = Ideal.span (Set.range fun s : F => (1 : F) ⊗ₜ[K] s - s ⊗ₜ[K] (1 : F)) :=\n  (KaehlerDifferential.span_range_eq_ideal K F).symm",
      "zone": "B",
      "doc": "The generator statement: `I` is the ideal generated by the differences\n`1 ⊗ₜ f - f ⊗ₜ 1`. This is what makes the classical computation `I = (x - y)` in\n`R[x] ⊗ R[x] ≅ R[x, y]` a theorem rather than a picture."
    },
    {
      "type": "prose",
      "md": " **Where the multiplication comes from.** Not from this sheet: typeclass search,\nfrom `[Field K] [Field F] [Algebra K F]`, in three layers — `LinearMap.mul K F` is\n`K`-bilinear *because* `F` is a `K`-algebra, `TensorProduct.map₂` tensors the two\nbilinear maps and the universal property of `⊗` linearises the result, and\n`Algebra.TensorProduct.instMul`/`instCommRing` package it with unit `1 ⊗ₜ 1`. The\nelement rule `(a ⊗ₜ b) * (c ⊗ₜ d) = (a * c) ⊗ₜ (b * d)` is then `rfl` (`tmul_mul_tmul`):\nthe multiplication is *defined* as \"multiply in each factor\", which is why the sheet\ninherits the ring structure instead of building it. With only `[Module K F]` there\nwould be no `*` at all. A bonus from the same instances: `F ⊗[K] F` is an `F`-algebra\nthrough the left copy (`algebraMap f = f ⊗ₜ 1`), which is where `Ω`'s `F`-module\nstructure comes from. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @TensorProduct.map₂",
      "zone": "B",
      "name": "TensorProduct.map₂",
      "display": "@TensorProduct.map₂",
      "card": "TensorProduct.map₂"
    },
    {
      "type": "check",
      "raw": "#check @LinearMap.mul",
      "zone": "B",
      "name": "LinearMap.mul",
      "display": "@LinearMap.mul",
      "card": "LinearMap.mul"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.mul",
      "zone": "B",
      "name": "Algebra.TensorProduct.mul",
      "display": "@Algebra.TensorProduct.mul",
      "card": "Algebra.TensorProduct.mul"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.instMul",
      "zone": "B",
      "name": "Algebra.TensorProduct.instMul",
      "display": "@Algebra.TensorProduct.instMul",
      "card": "Algebra.TensorProduct.instMul"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.instSemiring",
      "zone": "B",
      "name": "Algebra.TensorProduct.instSemiring",
      "display": "@Algebra.TensorProduct.instSemiring",
      "card": "Algebra.TensorProduct.instSemiring"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.instCommRing",
      "zone": "B",
      "name": "Algebra.TensorProduct.instCommRing",
      "display": "@Algebra.TensorProduct.instCommRing",
      "card": "Algebra.TensorProduct.instCommRing"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.leftAlgebra",
      "zone": "B",
      "name": "Algebra.TensorProduct.leftAlgebra",
      "display": "@Algebra.TensorProduct.leftAlgebra",
      "card": "Algebra.TensorProduct.leftAlgebra"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.algebraMap_apply",
      "zone": "B",
      "name": "Algebra.TensorProduct.algebraMap_apply",
      "display": "@Algebra.TensorProduct.algebraMap_apply",
      "card": "Algebra.TensorProduct.algebraMap_apply"
    },
    {
      "type": "prose",
      "md": "The instances the sheet relies on, printed as what they are: instance search.",
      "zone": "B"
    },
    {
      "type": "code",
      "text": "#synth CommRing (F ⊗[K] F)",
      "zone": "B"
    },
    {
      "type": "code",
      "text": "#synth Algebra F (F ⊗[K] F)",
      "zone": "B"
    },
    {
      "type": "code",
      "text": "#synth IsScalarTower K F (F ⊗[K] F)",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (f : F) : algebraMap F (F ⊗[K] F) f = f ⊗ₜ[K] (1 : F) := by\n  rw [Algebra.TensorProduct.algebraMap_apply]\n  simp",
      "zone": "B",
      "doc": "The ring structure is instance search (`#synth` above), and the left copy is what\nmakes `Ω` an `F`-module: `algebraMap f = f ⊗ₜ 1`."
    },
    {
      "type": "prose",
      "md": " **Why not just `S`, then? Because `⊗ₜ` is not symmetric.**\n\nOnly scalars cross slots (`r • s ⊗ₜ t = s ⊗ₜ r • t` for `r : K`), and multiplication\n**recombines** the slots without ever **equating** them:\n`(s ⊗ₜ 1) * (1 ⊗ₜ t) = s ⊗ₜ t = (1 ⊗ₜ t) * (s ⊗ₜ 1)` is a product of two elements,\nnot an equality of `s ⊗ₜ 1` with `1 ⊗ₜ s`. So `S ⊗[K] S` is strictly bigger than `S`:\n`lmul'` is onto with kernel `I`, and `s ⊗ₜ 1 - 1 ⊗ₜ s` is generally a nonzero element of\n`I` — the obstruction to sliding `s` across the tensor symbol, and the very element\nwhose class in `I ⧸ I²` is `D s`. Impose those two copies equal for all `s` and\n`I = 0`, `Ω = 0`: an unramified extension with no differentials. `Ω` is the\n*linearisation* of the collapse `lmul'`, and `S ⊗[K] S` — the coproduct,\n`Spec S ×_{Spec K} Spec S`, generally of higher dimension than `Spec S` — is the\nuniversal way to have two copies that differ. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (s t : F) :\n    (s ⊗ₜ[K] (1 : F)) * ((1 : F) ⊗ₜ[K] t) = s ⊗ₜ[K] t := by\n  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]",
      "zone": "B",
      "doc": "Recombination, not identification: a product of the two copies is an elementary\ntensor, but the two copies themselves stay distinct."
    },
    {
      "type": "example",
      "text": "example {x : F} (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :\n    (1 : F) ⊗ₜ[K] x ≠ x ⊗ₜ[K] (1 : F) := by\n  intro h\n  have hcov : (1 : F) ⊗ₜ[K] x - x ⊗ₜ[K] (1 : F) = 0 := by rw [h, sub_self]\n  have hsub : (⟨1 ⊗ₜ[K] x - x ⊗ₜ[K] (1 : F),\n      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) x⟩ :\n      KaehlerDifferential.ideal K F) = 0 := by\n    rw [Subtype.ext_iff]\n    simpa using hcov\n  refine KaehlerDifferential.D_ne_zero_of_transcendental K x hx ?_\n  rw [KaehlerDifferential.D_apply, hsub]\n  exact map_zero _",
      "zone": "B",
      "doc": "The two copies are *not* equal, and the proof is that otherwise `d x` would\nvanish: `D_ne_zero_of_transcendental` supplies the nonvanishing, and the equality\n`1 ⊗ₜ x = x ⊗ₜ 1` would put its defining class at `0`. (Why a transcendental has a\nnonzero differential at all is the block after the p-th-power example below, where\n`d x ≠ 0` is derived rather than quoted.)"
    },
    {
      "type": "example",
      "text": "example (s : F) :\n    Algebra.TensorProduct.lmul' K ((1 : F) ⊗ₜ[K] s) =\n      Algebra.TensorProduct.lmul' K (s ⊗ₜ[K] (1 : F)) := by\n  rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul,\n    one_mul, mul_one]",
      "zone": "B",
      "doc": "And yet they are equal after the collapse: `lmul'` kills the difference, which is\nwhy `(F ⊗[K] F) ⧸ I ≅ F` is a statement about rings and not about sets."
    },
    {
      "type": "prose",
      "md": " **Why the kernel is an *ideal*, not just a submodule.** `F ⊗[K] F` is not only a\n`K`-vector space but a commutative **ring** — the coproduct of `F` with itself in\n`K`-algebras — and `lmul'` is an `AlgHom`, hence multiplicative. That is what upgrades\na kernel: a ring hom's kernel is closed under multiplication by any element of the\n*domain*, not only by the scalars from `K` —\n\n  `x ∈ I  ⇒  lmul' (y * x) = lmul' y * lmul' x = lmul' y * 0 = 0`,\n\ni.e. `y * x ∈ I` for every `y : F ⊗[K] F` (`Ideal.mul_mem_left`). And `Ideal R` *is*\n`Submodule R R` definitionally, so an ideal is not a new kind of object: it is a\nsubmodule whose extra closure comes free from multiplicativity. That is why\n`RingHom.ker` can return an `Ideal` while a merely `K`-linear map's kernel cannot.\nPayoffs: `I²` exists (so `I ⧸ I²` does), and `(F ⊗[K] F) ⧸ I ≅ F` is a ring, which is\nwhat `Ω` is a module over. ",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": "The two facts that make `F ⊗[K] F` a ring here, and that `lmul'` respects: how\nelementary tensors multiply, and what its unit is.",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.tmul_mul_tmul",
      "zone": "B",
      "name": "Algebra.TensorProduct.tmul_mul_tmul",
      "display": "@Algebra.TensorProduct.tmul_mul_tmul",
      "card": "Algebra.TensorProduct.tmul_mul_tmul"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.TensorProduct.one_def",
      "zone": "B",
      "name": "Algebra.TensorProduct.one_def",
      "display": "@Algebra.TensorProduct.one_def",
      "card": "Algebra.TensorProduct.one_def"
    },
    {
      "type": "check",
      "raw": "#check @AlgHom.toRingHom",
      "zone": "B",
      "name": "AlgHom.toRingHom",
      "display": "@AlgHom.toRingHom",
      "card": "AlgHom.toRingHom"
    },
    {
      "type": "check",
      "raw": "#check @RingHom.ker",
      "zone": "B",
      "name": "RingHom.ker",
      "display": "@RingHom.ker",
      "card": "RingHom.ker"
    },
    {
      "type": "check",
      "raw": "#check @Ideal",
      "zone": "B",
      "name": "Ideal",
      "display": "@Ideal",
      "card": "Ideal"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.mul_mem_left",
      "zone": "B",
      "name": "Ideal.mul_mem_left",
      "display": "@Ideal.mul_mem_left",
      "card": "Ideal.mul_mem_left"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.Quotient.mk",
      "zone": "B",
      "name": "Ideal.Quotient.mk",
      "display": "@Ideal.Quotient.mk",
      "card": "Ideal.Quotient.mk"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.mk_ker",
      "zone": "B",
      "name": "Ideal.mk_ker",
      "display": "@Ideal.mk_ker",
      "card": "Ideal.mk_ker"
    },
    {
      "type": "check",
      "raw": "#check @RingHom.quotientKerEquivOfRightInverse",
      "zone": "B",
      "name": "RingHom.quotientKerEquivOfRightInverse",
      "display": "@RingHom.quotientKerEquivOfRightInverse",
      "card": "RingHom.quotientKerEquivOfRightInverse"
    },
    {
      "type": "check",
      "raw": "#check @RingHom.quotientKerEquivOfSurjective",
      "zone": "B",
      "name": "RingHom.quotientKerEquivOfSurjective",
      "display": "@RingHom.quotientKerEquivOfSurjective",
      "card": "RingHom.quotientKerEquivOfSurjective"
    },
    {
      "type": "example",
      "text": "example : Submodule (F ⊗[K] F) (F ⊗[K] F) := KaehlerDifferential.ideal K F",
      "zone": "B",
      "doc": "`Ideal R` *is* `Submodule R R`, so `I` is a submodule of `F ⊗[K] F` over itself\n— not over `K`. \"Ideal\" is the submodule that is also closed under multiplication."
    },
    {
      "type": "example",
      "text": "example (x : F ⊗[K] F) (y : KaehlerDifferential.ideal K F) :\n    x * (y : F ⊗[K] F) ∈ KaehlerDifferential.ideal K F :=\n  Ideal.mul_mem_left _ x y.2",
      "zone": "B",
      "doc": "The extra closure, at an arbitrary ring element — not at a `K`-scalar. The\nmultiplicativity that supplies it is `map_mul _ _ _`, and `Ideal.mk_ker` is the same\nclosure seen from the quotient side."
    },
    {
      "type": "example",
      "text": "example :\n    (F ⊗[K] F) ⧸ RingHom.ker (Algebra.TensorProduct.lmul' (R := K) (S := F)) ≃+* F :=\n  RingHom.quotientKerEquivOfSurjective (fun x => ⟨x ⊗ₜ[K] (1 : F), by simp⟩)",
      "zone": "B",
      "doc": "The payoff: the first isomorphism theorem makes the quotient a *ring*, isomorphic\nto `F`. The ideal is written as `RingHom.ker lmul'` — which is what\n`KaehlerDifferential.ideal` *is*, by definition — because that is the shape the theorem\nconsumes; `lmul'` is onto by `fun x => ⟨x ⊗ₜ 1, by simp⟩`. That ring is what `Ω` is a\nmodule over, and it is why `I ⧸ I²` is an `F`-vector space and not only a `K`-one."
    },
    {
      "type": "prose",
      "md": " **Membership: `0`, not `1`.** `lmul'` is *multiplication*, so `x ∈ I` means \"the\nproduct of the two copies of `x` is `0`\". At an elementary tensor that reads\n`a * b = 0`; the tempting `a * b = 1` is the opposite case — the product is the\n*unit*, so that tensor is a unit of `F ⊗[K] F`. The examples below spell this out,\nand the last one is why the interesting members of `I` are *relations* between\nproducts — sums, not products. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (a b : F) : a ⊗ₜ[K] b ∈ KaehlerDifferential.ideal K F ↔ a * b = 0 := by\n  simp [KaehlerDifferential.ideal, RingHom.mem_ker,\n    Algebra.TensorProduct.lmul'_apply_tmul]",
      "zone": "B",
      "doc": "Membership at the level of one elementary tensor: `lmul'` is *multiplication*, so\n`a ⊗ₜ b` is in `I` when the product is `0` — not when it is `1`."
    },
    {
      "type": "example",
      "text": "example (a b : F) (h : a * b = 1) : a ⊗ₜ[K] b ∉ KaehlerDifferential.ideal K F := by\n  simp [KaehlerDifferential.ideal, RingHom.mem_ker,\n    Algebra.TensorProduct.lmul'_apply_tmul, h]",
      "zone": "B",
      "doc": "The `a * b = 1` case is the opposite extreme — that tensor is a *unit* of\n`F ⊗[K] F`, since `(a ⊗ₜ b) * (a⁻¹ ⊗ₜ b⁻¹) = 1` — so it lives as far from `I` as an\nelement can."
    },
    {
      "type": "example",
      "text": "example {f : F} (hf : f ≠ 0) :\n    (1 : F) ⊗ₜ[K] f ∉ KaehlerDifferential.ideal K F ∧\n      f ⊗ₜ[K] (1 : F) ∉ KaehlerDifferential.ideal K F ∧\n      (1 : F) ⊗ₜ[K] f - f ⊗ₜ[K] (1 : F) ∈ KaehlerDifferential.ideal K F := by\n  refine ⟨?_, ?_, ?_⟩\n  · simp [KaehlerDifferential.ideal, RingHom.mem_ker, hf]\n  · simp [KaehlerDifferential.ideal, RingHom.mem_ker, hf]\n  · exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) f",
      "zone": "B",
      "doc": "So the *elementary* members of `I` are the trivial ones — `a * b = 0` in the\n*field* `F`, hence `a = 0` or `b = 0` — while the elements that matter are sums:\neach summand below is outside `I` and their difference is in it. That is the shape\nthe quotient inherits: `Ω = I ⧸ I²` is spanned by the classes `d f`."
    },
    {
      "type": "prose",
      "md": " **Why `I ⧸ I²` and not `I`.** Three things happen in the quotient, and each is\nsomething the rest of the sheet needs.\n\n* It is the *first-order* piece. `I²` is second order, so `I ⧸ I²` keeps only the\n  derivative of the agreement: `(S ⊗ S) ⧸ I²` is the first infinitesimal\n  neighbourhood of the diagonal — a square-zero extension of `S` by `Ω`, and the\n  universal one.\n* Products of two elements of `I` die, and that *is* the Leibniz rule: the\n  disagreement between `D (a * b)` and `b • D a + a • D b` turns out to be the\n  product `D a · D b` — a square, hence `0` in `I ⧸ I²`. The block after the\n  `D_apply` example below computes this rather than asserting it, and it is the\n  only place where `I²` does any work.\n* `I ⧸ I²` is a module over `(S ⊗ S) ⧸ I ≅ S`, so a differential is again a\n  *function*, not merely an `R`-vector — which is what lets `finrank_F Ω` below be\n  the number it is, and what `kaehler_free_rank_one` speaks about.\n\nGeometrically, `Spec (S ⊗[R] S) = Spec S ×_{Spec R} Spec S`, `lmul'` is the diagonal\n`Δ`, `I` is the ideal of `Δ`, and `Ω` is its conormal sheaf — the cotangent sheaf,\ndual to the tangent bundle. The affine model is `S = R[x]`: then `S ⊗ S ≅ R[x, y]`\nwith the two copies `x` and `y`, `lmul'` is \"`y ↦ x`\", `I = (x - y)`, and `Ω` is free\nof rank one on `d x = [1 ⊗ₜ x - x ⊗ₜ 1]`. Note that `I` itself would be the wrong\nanswer: `(x - y)` also contains `x² - y²`, whereas `Ω` keeps only the linear part —\n`d x`, and not every relation vanishing on the diagonal. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.D_apply",
      "zone": "B",
      "name": "KaehlerDifferential.D_apply",
      "display": "@KaehlerDifferential.D_apply",
      "card": "KaehlerDifferential.D_apply"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.Cotangent",
      "zone": "B",
      "name": "Ideal.Cotangent",
      "display": "@Ideal.Cotangent",
      "card": "Ideal.Cotangent"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.toCotangent",
      "zone": "B",
      "name": "Ideal.toCotangent",
      "display": "@Ideal.toCotangent",
      "card": "Ideal.toCotangent"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.map_toCotangent_ker",
      "zone": "B",
      "name": "Ideal.map_toCotangent_ker",
      "display": "@Ideal.map_toCotangent_ker",
      "card": "Ideal.map_toCotangent_ker"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.toCotangent_eq",
      "zone": "B",
      "name": "Ideal.toCotangent_eq",
      "display": "@Ideal.toCotangent_eq",
      "card": "Ideal.toCotangent_eq"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.Cotangent.smul_eq_zero_of_mem",
      "zone": "B",
      "name": "Ideal.Cotangent.smul_eq_zero_of_mem",
      "display": "@Ideal.Cotangent.smul_eq_zero_of_mem",
      "card": "Ideal.Cotangent.smul_eq_zero_of_mem"
    },
    {
      "type": "example",
      "text": "example :\n    (LinearMap.ker (KaehlerDifferential.ideal K F).toCotangent).map\n        (KaehlerDifferential.ideal K F).subtype\n      = (KaehlerDifferential.ideal K F) ^ 2 :=\n  Ideal.map_toCotangent_ker _",
      "zone": "B",
      "doc": "The quotient map `I → Ω` is a quotient by `I ^ 2` *literally*: its kernel, mapped\nback into `S ⊗[R] S`, is `I ^ 2`. So the \"mod squares\" is not a convention imposed\nafterwards — it is the definition, and `toCotangent_eq` is the same statement at the\nlevel of elements."
    },
    {
      "type": "example",
      "text": "example (f : F) :\n    KaehlerDifferential.D K F f\n      = (KaehlerDifferential.ideal K F).toCotangent\n          ⟨1 ⊗ₜ[K] f - f ⊗ₜ[K] 1,\n            KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) f⟩ :=\n  KaehlerDifferential.D_apply K F f",
      "zone": "B",
      "doc": "**`D` is the difference of the two copies.** The universal derivation sends `f`\nto the class of `1 ⊗ₜ f - f ⊗ₜ 1`: the two ring maps `includeLeft`, `includeRight` into\n`(S ⊗ S) ⧸ I²` both split the projection to `S`, and their difference is a\nderivation. Zone C's `d t_v` is this class for `f = t_v` — the differential of the\nchosen uniformiser is the linearised disagreement of its two copies, and nothing in\nthat sentence, or in `Ω`, names a place."
    },
    {
      "type": "prose",
      "md": " **Leibniz, computed.** The `I ⧸ I²` bullet above is the whole of the Leibniz rule,\nand it is worth doing once by hand — in the ring `F ⊗[K] F`, with no derivation in\nsight. For `a : F` write `da := 1 ⊗ₜ a - a ⊗ₜ 1` (in `I`, class `D a`); the element\nwhose class is `D (a * b)` then expands by the multiplication rule to\n\n  `d (a * b) = da * (b ⊗ₜ 1) + (1 ⊗ₜ a) * db`.                            (*)\n\nNothing is quotiented yet: `(*)` is an identity of the commutative ring, and the two\ncross terms `b ⊗ₜ a` cancel — that cancellation is the entire algebra in the product\nrule. (Mathlib's `D a` is `1 ⊗ₜ a - a ⊗ₜ 1`; `a ⊗ₜ 1 - 1 ⊗ₜ a` would work as well.)\n\nNow pass to `I ⧸ I²`. The coefficient sits on the left copy in the first summand and\non the right copy in the second, but the two copies differ by `db ∈ I`, and a factor in\n`I` times a difference in `I` is in `I · I = I²`:\n\n  `da * (b ⊗ₜ 1) = da * (1 ⊗ₜ b)` and `(1 ⊗ₜ a) * db = (a ⊗ₜ 1) * db`   mod `I²`,\n\nwith corrections `∓ da * db`. **The defect is the product `da · db`, and `I²` is exactly\nwhat kills it**; reading every coefficient through the left copy leaves\n`D (a * b) = b • D a + a • D b`. So \"it does not matter which copy `a` and `b` are\" is\nprecisely those two congruences — switching copies costs a term of `I²` — and it is why\n`Ω` is `I ⧸ I²` and not `I`: in `I` the defect `da · db` survives (model: `(y - x)²`).\n\nMathlib proves the same thing in the `leibniz'` field of `def KaehlerDifferential.D`\n([`Kaehler/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/RingTheory/Kaehler/Basic.lean#L201-L213)):\nafter `Ideal.toCotangent_eq` and `pow_two`, the mathematics is the single line\n\n  `convert! Submodule.mul_mem_mul (one_smul_sub_smul_one_mem_ideal R a :) (one_smul_sub_smul_one_mem_ideal R b :)`\n\n— \"the defect is `da * db ∈ I · I`\" — and `convert!`/`ring_nf` supply the bookkeeping of\n`(*)`. The examples below are that line, in order: `(*)`, the defect in `I²`, the two\ncopies agreeing in `Ω`, and Leibniz for `D`. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @Ideal.mul_mem_mul",
      "zone": "B",
      "name": "Ideal.mul_mem_mul",
      "display": "@Ideal.mul_mem_mul",
      "card": "Ideal.mul_mem_mul"
    },
    {
      "type": "check",
      "raw": "#check @IsScalarTower.algebraMap_smul",
      "zone": "B",
      "name": "IsScalarTower.algebraMap_smul",
      "display": "@IsScalarTower.algebraMap_smul",
      "card": "IsScalarTower.algebraMap_smul"
    },
    {
      "type": "example",
      "text": "example (a b : F) :\n    (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (b ⊗ₜ[K] (1 : F))\n        + ((1 : F) ⊗ₜ[K] a) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F))\n      = 1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F) := by\n  rw [sub_mul, mul_sub]\n  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]\n  abel",
      "zone": "B",
      "doc": "`(*)`: the elementary identity, in the ring, before any quotient. Distributing and\ncancelling the two cross terms is the whole computation."
    },
    {
      "type": "example",
      "text": "example (a b : F) :\n    (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F))\n      ∈ (ideal K F) ^ 2 := by\n  rw [pow_two]\n  exact Ideal.mul_mem_mul (one_smul_sub_smul_one_mem_ideal (R := K) a)\n    (one_smul_sub_smul_one_mem_ideal (R := K) b)",
      "zone": "B",
      "doc": "The second-order defect `da * db` lies in `I²`: `Ideal.mul_mem_mul` applied to the\ntwo classes. This one membership *is* the product rule; what remains is linearity."
    },
    {
      "type": "example",
      "text": "example (c : F) (x : ideal K F) :\n    (ideal K F).toCotangent ((c ⊗ₜ[K] (1 : F)) • x)\n      = (ideal K F).toCotangent (((1 : F) ⊗ₜ[K] c) • x) := by\n  rw [Ideal.toCotangent_eq, pow_two]\n  simp only [Submodule.coe_smul, smul_eq_mul]\n  rw [← sub_mul]\n  exact Ideal.mul_mem_mul (by simp) x.2",
      "zone": "B",
      "doc": "The two copies of a scalar agree in `Ω`. This is \"`includeLeft` or `includeRight`,\nit makes no difference\", as a statement about `I ⧸ I²`, and it is what lets the\nquotient ring `(F ⊗[K] F) ⧸ I ≅ F` act on `Ω`: the ambiguity `(c ⊗ₜ 1 - 1 ⊗ₜ c)` is an\nelement of `I`, so acting with it lands in `I · I` and dies in the quotient."
    },
    {
      "type": "example",
      "text": "example (a b : F) :\n    KaehlerDifferential.D K F (a * b)\n      = b • KaehlerDifferential.D K F a + a • KaehlerDifferential.D K F b := by\n  -- the `F`-scalar acts through the left copy of `F` in `F ⊗[K] F`\n  have hsmul : ∀ (c : F) (ω : (ideal K F).Cotangent),\n      c • ω = (c ⊗ₜ[K] (1 : F)) • ω := by\n    intro c ω\n    rw [← IsScalarTower.algebraMap_smul (A := F ⊗[K] F),\n      Algebra.TensorProduct.algebraMap_apply]\n    simp\n  -- `Ω[F⁄K]` is a `def` alias of `I.Cotangent`; `change` puts both sides at the same\n  -- type, so that the linearity of `toCotangent` applies syntactically\n  change (ideal K F).toCotangent\n      ⟨1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F), _⟩\n    = b • (ideal K F).toCotangent ⟨1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F), _⟩\n      + a • (ideal K F).toCotangent ⟨1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F), _⟩\n  -- pull the scalars and the sum inside `I`, then compare in the ring\n  rw [hsmul b, hsmul a, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq,\n    pow_two]\n  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]\n  -- `(*)`, which is the only place the ring structure is used\n  have hd : 1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F)\n      = (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (b ⊗ₜ[K] (1 : F))\n        + ((1 : F) ⊗ₜ[K] a) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)) := by\n    rw [sub_mul, mul_sub]\n    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]\n    abel\n  -- the terms carrying `b ⊗ₜ 1` cancel by commutativity, leaving `((1 ⊗ₜ a) - (a ⊗ₜ 1)) * db`\n  have hkey : (1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F))\n      - ((b ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F))\n        + (a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)))\n      = (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)) := by\n    rw [hd]\n    ring\n  rw [hkey]\n  exact Ideal.mul_mem_mul (one_smul_sub_smul_one_mem_ideal (R := K) a)\n    (one_smul_sub_smul_one_mem_ideal (R := K) b)",
      "zone": "B",
      "doc": "**Leibniz for `D`, computed**: `(*)` in the ring, then the defect `da * db ∈ I²`,\nthen the linearity of `toCotangent`. No `Derivation.leibniz` in the proof — this is\nwhere the sheet's Leibniz rule comes from, and Zone C uses it as such."
    },
    {
      "type": "prose",
      "md": " **The ideal is forced, not chosen.** `Ω` corepresents derivations: `S`-linear maps\nout of it are exactly `R`-derivations, and the inverse equivalence is built by sending\n`a ⊗ b` to `a • D b`. That map kills `I²`, and the reason is the product rule of the\nblock above: on a product `x * y` of two elements of `I` it returns\n`lmul' x • (…) + lmul' y • (…) = 0`, because `lmul'` kills `I`. So it factors through\n`I → I ⧸ I²` — and vanishing on `I²` rather than on `I` is what leaves `Ω` nonzero,\nsince `I² ⊆ I`. Any other ideal whose square-zero quotient classified derivations would\ngive the same functor, hence the same module up to isomorphism. That is the precise\nsense in which `ker lmul'` is the right kernel and not an arbitrary one. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.linearMapEquivDerivation",
      "zone": "B",
      "name": "KaehlerDifferential.linearMapEquivDerivation",
      "display": "@KaehlerDifferential.linearMapEquivDerivation",
      "card": "KaehlerDifferential.linearMapEquivDerivation"
    },
    {
      "type": "check",
      "raw": "#check @Derivation.liftKaehlerDifferential",
      "zone": "B",
      "name": "Derivation.liftKaehlerDifferential",
      "display": "@Derivation.liftKaehlerDifferential",
      "card": "Derivation.liftKaehlerDifferential"
    },
    {
      "type": "check",
      "raw": "#check @Derivation.tensorProductTo",
      "zone": "B",
      "name": "Derivation.tensorProductTo",
      "display": "@Derivation.tensorProductTo",
      "card": "Derivation.tensorProductTo"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.tensorProductTo_surjective",
      "zone": "B",
      "name": "KaehlerDifferential.tensorProductTo_surjective",
      "display": "@KaehlerDifferential.tensorProductTo_surjective",
      "card": "KaehlerDifferential.tensorProductTo_surjective"
    },
    {
      "type": "example",
      "text": "example (M : Type*) [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]\n    (D : Derivation K F M) (f : F) :\n    D.liftKaehlerDifferential (KaehlerDifferential.D K F f) = D f :=\n  Derivation.liftKaehlerDifferential_comp_D D f",
      "zone": "B"
    },
    {
      "type": "prose",
      "md": " And the degenerate case, which shows what `Ω` is *measuring*: if `R → S` is\nsurjective there is no relative dimension left and every derivation dies. `Ω` is a\nstatement about the *extension*, never about `S` alone — Zone D.1's whole point. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.subsingleton_of_surjective",
      "zone": "B",
      "name": "KaehlerDifferential.subsingleton_of_surjective",
      "display": "@KaehlerDifferential.subsingleton_of_surjective",
      "card": "KaehlerDifferential.subsingleton_of_surjective"
    },
    {
      "type": "prose",
      "md": " **The packaged form.** `D` is a `Derivation`: a `K`-linear map together with two\nequations. The map is the difference of the two copies fed into `toCotangent`, and both\nequations are computations already done — `map_one_eq_zero'` is `D 1 = 0`, which\n`K`-linearity turns into `D (algebraMap c) = 0` (`Derivation.map_algebraMap`), and\n`leibniz'` is the identity of the block after `D_apply`, which is what\n`Derivation.leibniz` reads off. So nothing is added by the packaging except the right to\nstop looking; what it costs is that the `leibniz'` field of `KaehlerDifferential.D` is\nproved by `convert!` and `ring_nf`, which is why the sheet computed it. `leibniz_pow`\nis `leibniz'` iterated, and it is the one place where the exponent matters: in\ncharacteristic `p` the coefficient `p` kills the sum. ",
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
      "md": " **Why a transcendental differential cannot vanish.** `D x ≠ 0` for transcendental `x`\n(`D_ne_zero_of_transcendental`) is what Zone D.2's route to `DCoordGenerates` runs on,\nand it is easy to misread as \"`Ω` is large\". It says that **`x` is a coordinate, so its\ndifferential is `1`**: on a polynomial ring `d` *is* the formal derivative `P ↦ P'`, so\n`Ω[K[X]⁄K]` is `K[X]` itself by `d X ↦ 1`; and no change of ring alters the differential,\nonly its coefficients — provided the change is *separable*, the algebraic form of\n\"infinitesimally trivial\". An inseparable extension does alter it, and can kill a\ndifferential that was already there (last paragraph).\n\nTwo devices make that formal, each one line.\n\n**Universality.** `Ω` corepresents derivations, so `D x` is the universal witness: every\n`K`-derivation `D'` out of `F` has `D' x = D'.liftKaehlerDifferential (D x)`\n(`Derivation.liftKaehlerDifferential_comp_D`). Hence `D x = 0` iff *every* derivation kills\n`x`, and `D x ≠ 0` needs just one derivation that does not — in the model, `X' = 1 ≠ 0`.\n\n**Base change.** For an `Algebra.FormallyEtale` extension `S → T` (a localisation, or a\nseparable algebraic extension of fields) differentials only base-change:\n`Ω[T⁄R] ≅ T ⊗_S Ω[S⁄R]` (`tensorKaehlerEquivOfFormallyEtale`), and a generator goes to a\ngenerator (`_symm_D_algebraMap`; the first transport is done end to end below). So the\nargument is four rings and two transports,\n\n  `K[X]` —localise→ `K(X)` —rename→ `K(x)` —separable→ `F`,\n\nwith `d X` the generator at every stage. The renaming is the only use of\n`Transcendental K x`: `RatFunc.algEquivOfTranscendental` is `K(X) ≅ K(x)`, `X ↦ x` — \"not\na root of any polynomial\" *is* \"usable as a coordinate\". At the far end\n`Ω[F⁄K] ≅ F ⊗_{K(x)} Ω[K(x)⁄K] ≅ F`, so **`Ω[F⁄K]` is free of rank one on `d x`, hence\n`d x ≠ 0` and `span {d x} = ⊤`.**\n\n**What the proof writes down is that basis, not the intuition.** The port's `exists_basis`\n(`Defs/KaehlerTranscendental.lean`, from the pin's\n[`S_KaehlerDifferential_D_ne_zero_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean))\nproduces `b : Basis Unit F Ω[F⁄K]` with `b () = D x` by transporting the model's\n*singleton* basis (FLT's `b₀`: `Basis.singleton` pulled back along `polynomialEquiv`)\nthrough `Module.Basis.baseChange` and `Module.Basis.map` along the two formal-étale\nisomorphisms. `D x ≠ 0` is then `b.ne_zero ()` and `span = ⊤` is `b.span_eq`; the\n`letI`/`haveI` wall is the tower `K → K[X] → K(X) ≅ K(x) → F`, not mathematics.\n\n**The hypothesis is sharp, and the failure is the p-th-power blindness just above.** In\ncharacteristic `p` let `y` be transcendental and put `x = y ^ p`: then `x` is still\ntranscendental (`Transcendental.pow`), but `d x = p • y ^ (p - 1) • d y = 0`. So `K(y)` is\nan inseparable extension of `K(x)` in which `d y` — not `d x` — is the generator, and the\n`IsSeparable` in these statements is exactly its exclusion. ",
      "zone": "B"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.polynomialEquiv",
      "zone": "B",
      "name": "KaehlerDifferential.polynomialEquiv",
      "display": "@KaehlerDifferential.polynomialEquiv",
      "card": "KaehlerDifferential.polynomialEquiv"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.polynomialEquiv_D",
      "zone": "B",
      "name": "KaehlerDifferential.polynomialEquiv_D",
      "display": "@KaehlerDifferential.polynomialEquiv_D",
      "card": "KaehlerDifferential.polynomialEquiv_D"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.polynomialEquiv_symm",
      "zone": "B",
      "name": "KaehlerDifferential.polynomialEquiv_symm",
      "display": "@KaehlerDifferential.polynomialEquiv_symm",
      "card": "KaehlerDifferential.polynomialEquiv_symm"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.polynomial_D_apply",
      "zone": "B",
      "name": "KaehlerDifferential.polynomial_D_apply",
      "display": "@KaehlerDifferential.polynomial_D_apply",
      "card": "KaehlerDifferential.polynomial_D_apply"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
      "zone": "B",
      "name": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
      "display": "@KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
      "card": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
      "zone": "B",
      "name": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
      "display": "@KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
      "card": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.FormallyEtale.of_isLocalization",
      "zone": "B",
      "name": "Algebra.FormallyEtale.of_isLocalization",
      "display": "@Algebra.FormallyEtale.of_isLocalization",
      "card": "Algebra.FormallyEtale.of_isLocalization"
    },
    {
      "type": "check",
      "raw": "#check @Algebra.FormallyEtale.of_isSeparable",
      "zone": "B",
      "name": "Algebra.FormallyEtale.of_isSeparable",
      "display": "@Algebra.FormallyEtale.of_isSeparable",
      "card": "Algebra.FormallyEtale.of_isSeparable"
    },
    {
      "type": "check",
      "raw": "#check @RatFunc.algEquivOfTranscendental",
      "zone": "B",
      "name": "RatFunc.algEquivOfTranscendental",
      "display": "@RatFunc.algEquivOfTranscendental",
      "card": "RatFunc.algEquivOfTranscendental"
    },
    {
      "type": "check",
      "raw": "#check @RatFunc.algEquivOfTranscendental_X",
      "zone": "B",
      "name": "RatFunc.algEquivOfTranscendental_X",
      "display": "@RatFunc.algEquivOfTranscendental_X",
      "card": "RatFunc.algEquivOfTranscendental_X"
    },
    {
      "type": "check",
      "raw": "#check @Module.Basis.baseChange",
      "zone": "B",
      "name": "Module.Basis.baseChange",
      "display": "@Module.Basis.baseChange",
      "card": "Module.Basis.baseChange"
    },
    {
      "type": "check",
      "raw": "#check @Module.Basis.map",
      "zone": "B",
      "name": "Module.Basis.map",
      "display": "@Module.Basis.map",
      "card": "Module.Basis.map"
    },
    {
      "type": "check",
      "raw": "#check @Module.Basis.ne_zero",
      "zone": "B",
      "name": "Module.Basis.ne_zero",
      "display": "@Module.Basis.ne_zero",
      "card": "Module.Basis.ne_zero"
    },
    {
      "type": "check",
      "raw": "#check @Module.Basis.span_eq",
      "zone": "B",
      "name": "Module.Basis.span_eq",
      "display": "@Module.Basis.span_eq",
      "card": "Module.Basis.span_eq"
    },
    {
      "type": "example",
      "text": "example {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]\n    (D' : Derivation K F M) {x : F} (h : KaehlerDifferential.D K F x = 0) : D' x = 0 := by\n  rw [← Derivation.liftKaehlerDifferential_comp_D D' x, h, map_zero]",
      "zone": "B",
      "doc": "Universality, the general form: a vanishing differential is invisible to every\nderivation. Contrapositively, proving `D x ≠ 0` needs one derivation that does not kill\n`x`."
    },
    {
      "type": "example",
      "text": "example : KaehlerDifferential.D K K[X] Polynomial.X ≠ 0 := by\n  intro h\n  have h1 : Polynomial.derivative' (R := K) Polynomial.X = 0 := by\n    rw [← Derivation.liftKaehlerDifferential_comp_D (Polynomial.derivative' (R := K)) Polynomial.X,\n      h, map_zero]\n  simp at h1",
      "zone": "B",
      "doc": "In the model the witness is the formal derivative, which sees `X`: `X' = 1`. No\nbasis, no dimension."
    },
    {
      "type": "example",
      "text": "example (P : K[X]) :\n    KaehlerDifferential.polynomialEquiv K (KaehlerDifferential.D K K[X] P) = P.derivative :=\n  KaehlerDifferential.polynomialEquiv_D K P",
      "zone": "B",
      "doc": "The same statement from the module side: the model *is* `K[X]`, by `d P ↦ P'`, so\n`d X` is the image of the unit."
    },
    {
      "type": "example",
      "text": "example (P : K[X]) :\n    KaehlerDifferential.D K K[X] P\n      = P.derivative • KaehlerDifferential.D K K[X] Polynomial.X :=\n  KaehlerDifferential.polynomial_D_apply K P",
      "zone": "B",
      "doc": "The chain rule in the model, which is the rank-one statement: every differential of\n`K[X]` is its derivative times `d X`."
    },
    {
      "type": "example",
      "text": "example : ∃ b : Module.Basis Unit K[X] Ω[K[X]⁄K],\n    b () = KaehlerDifferential.D K K[X] Polynomial.X :=\n  ⟨(Module.Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm,\n    by simp [KaehlerDifferential.polynomialEquiv_symm]⟩",
      "zone": "B",
      "doc": "The model's basis and its single vector: FLT's `b₀`, the singleton basis of `K[X]`\npulled back along the derivative."
    },
    {
      "type": "example",
      "text": "example {S T : Type*} [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]\n    [Algebra S T] [IsScalarTower K S T] [Algebra.FormallyEtale S T] (s : S) :\n    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S T).symm\n        (KaehlerDifferential.D K T (algebraMap S T s))\n      = (1 : T) ⊗ₜ[S] KaehlerDifferential.D K S s :=\n  KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K S T s",
      "zone": "B",
      "doc": "A formally étale extension carries a generator to a generator — the only thing the\nlocalisation and the separable extension steps use."
    },
    {
      "type": "example",
      "text": "example :\n    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) Polynomial.X) ≠ 0 := by\n  -- localisation is formally étale, so `Ω` only base-changes\n  have hfe : Algebra.FormallyEtale K[X] (RatFunc K) :=\n    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])\n  -- the transported generator is a vector of the base-changed model basis\n  have hb : (1 : RatFunc K) ⊗ₜ[K[X]] KaehlerDifferential.D K K[X] Polynomial.X ≠ 0 := by\n    have hne := (((Module.Basis.singleton Unit K[X]).map\n      (KaehlerDifferential.polynomialEquiv K).symm).baseChange (RatFunc K)).ne_zero ()\n    simpa [KaehlerDifferential.polynomialEquiv_symm] using hne\n  -- and `d X` upstairs is the image of that vector\n  intro h\n  have h1 := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap\n    K K[X] (RatFunc K) Polynomial.X\n  rw [h, map_zero] at h1\n  exact hb h1.symm",
      "zone": "B",
      "doc": "The first transport, done end to end. `d X` in `K(X)` is the base change of the model's\nbasis vector, and base-changing a basis gives a basis, so it is still nonzero: this is\n`b.ne_zero ()`, which is all `D_ne_zero_of_transcendental` amounts to once the tower is\nbuilt."
    },
    {
      "type": "example",
      "text": "example {x : F} (hx : Transcendental K x) :\n    ((RatFunc.algEquivOfTranscendental x hx) RatFunc.X : F) = x :=\n  RatFunc.algEquivOfTranscendental_X x hx",
      "zone": "B",
      "doc": "Transcendence is used for one thing only: a transcendental names a copy of the\ncoordinate ring, `K(X) ≅ K(x)` with `X ↦ x`."
    },
    {
      "type": "example",
      "text": "example (p : ℕ) [CharP F p] {y : F} (hy : Transcendental K y) (hp : 0 < p) :\n    Transcendental K (y ^ p) ∧ KaehlerDifferential.D K F (y ^ p) = 0 := by\n  refine ⟨hy.pow hp, ?_⟩\n  rw [Derivation.leibniz_pow]\n  have h0 : (p : F) = 0 := CharP.cast_eq_zero F p\n  rw [← Nat.cast_smul_eq_nsmul F p, h0, zero_smul]",
      "zone": "B",
      "doc": "And the hypothesis is sharp: in characteristic `p`, `x = y ^ p` is transcendental with\n`d x = 0`, so no separability-free version of the statement can hold."
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.D_ne_zero_of_transcendental",
      "zone": "B",
      "name": "KaehlerDifferential.D_ne_zero_of_transcendental",
      "display": "@KaehlerDifferential.D_ne_zero_of_transcendental",
      "card": "KaehlerDifferential.D_ne_zero_of_transcendental"
    },
    {
      "type": "check",
      "raw": "#check @KaehlerDifferential.span_D_eq_top_of_transcendental",
      "zone": "B",
      "name": "KaehlerDifferential.span_D_eq_top_of_transcendental",
      "display": "@KaehlerDifferential.span_D_eq_top_of_transcendental",
      "card": "KaehlerDifferential.span_D_eq_top_of_transcendental"
    },
    {
      "type": "check",
      "raw": "#check @AlgebraicCurve.kaehlerRankOne_of_transcendental",
      "zone": "B",
      "name": "AlgebraicCurve.kaehlerRankOne_of_transcendental",
      "display": "@AlgebraicCurve.kaehlerRankOne_of_transcendental",
      "card": "AlgebraicCurve.kaehlerRankOne_of_transcendental"
    },
    {
      "type": "prose",
      "md": " **`D` and the derivative of calculus.** Over `ℝ` or `ℂ` one thinks of `f ↦ f'`. What\n`D` gives is `d f`, and `f'` is `d f` read through a *frame*: in a coordinate — `F` with\nalgebraically independent `x₁,…,xₙ` — `Ω[F⁄K]` is free of rank `n` on `d xᵢ` and\n\n  `D f = ∑ᵢ (∂f/∂xᵢ) • d xᵢ`,\n\nso the classical partial derivative is the *coefficient* of `d xᵢ` (`polynomialEquiv` above\nis the case `n = 1`: it sends `d P` to `P'`). Dually\n`Derivation K F F ≅ Hom_F(Ω[F⁄K], F)` (`KaehlerDifferential.linearMapEquivDerivation`), so\n`∂/∂x` is the dual of `d x`. That is exactly Zone C: `differentialCoeff` is `f'` in the\nframe `d t_v`, `ordDifferential` is `ord(f')`, and `gate_ordDifferential_dCoord` is the\nidentity `d t_v / d t_v = 1`.\n\nIn characteristic `0` the dictionary is exact, and both characteristic-`p` phenomena\ndisappear:\n\n* every extension is separable, so `finrank_F Ω[F⁄K] = trdeg(F/K)`\n  (`finrank_kaehler_eq_card_of_separating` applies to *any* transcendence basis): `n`\n  variables, `n` differentials — the calculus count. A curve has rank `1`, so over a\n  perfect field `kaehler_free_rank_one` is a theorem and D.1's counterexample is a\n  characteristic-`p` phenomenon;\n* nothing transcendental dies: `x ^ n` with `x` transcendental and `n > 0` keeps a nonzero\n  differential (first example below), so the kernel of `D` is exactly the elements\n  algebraic over `K`. When `K` is algebraically closed in `F` — `ℂ ⊂ ℂ(x)` — that reads\n  \"`f' = 0` ⟹ `f` constant\", the calculus statement. It is *false* in characteristic `p`,\n  where `x ^ p` is transcendental with `d (x ^ p) = 0`.\n\nTwo cautions about what `Ω` is not. It is an *algebraic* object, depending only on the ring\nstructure: for a ring such as `C^∞(ℝ)` it is not the analytic module of `1`-forms, and the\nidentity `d f = f'(x) d x` needs an algebraic coordinate. And it measures *transcendence*,\nnot size: over `ℝ`, `Ω[ℂ⁄ℝ] = 0` because `d i = 0` (`2 i • d i = 0`, and `2 i` is a unit —\nsecond example), although `ℂ` is two-dimensional over `ℝ`; while `Ω[ℂ(x)⁄ℂ]` is\none-dimensional although `ℂ(x)` is infinite-dimensional over `ℂ`. ",
      "zone": "B"
    },
    {
      "type": "example",
      "text": "example (n : ℕ) [CharZero F] {x : F} (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (hn : 0 < n) :\n    KaehlerDifferential.D K F (x ^ n) ≠ 0 := by\n  have hDx : KaehlerDifferential.D K F x ≠ 0 :=\n    KaehlerDifferential.D_ne_zero_of_transcendental K x hx\n  have hn0 : (n : F) ≠ 0 := (Nat.cast_ne_zero (R := F)).mpr hn.ne'\n  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F n]\n  intro h\n  rcases smul_eq_zero.mp h with h0 | h0\n  · exact hn0 h0\n  rcases smul_eq_zero.mp h0 with h1 | h1\n  · exact pow_ne_zero _ hx.ne_zero h1\n  · exact hDx h1",
      "zone": "B",
      "doc": "In characteristic `0` a transcendental power keeps its differential: the p-th power\ncollapse of the block above is a characteristic-`p` phenomenon."
    },
    {
      "type": "example",
      "text": "example {M : Type*} [AddCommGroup M] [Module ℝ M] [Module ℂ M] [IsScalarTower ℝ ℂ M]\n    (D : Derivation ℝ ℂ M) : D Complex.I = 0 := by\n  have h2 : D (Complex.I ^ 2) = (2 : ℂ) • Complex.I • D Complex.I := by\n    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul ℂ 2]\n    norm_num\n  rw [show Complex.I ^ 2 = -1 by norm_num, map_neg, Derivation.map_one_eq_zero, neg_zero] at h2\n  rcases smul_eq_zero.mp h2.symm with h | h\n  · norm_num at h\n  rcases smul_eq_zero.mp h with h' | h'\n  · exact absurd h' (by norm_num)\n  · exact h'",
      "zone": "B",
      "doc": "Over `ℝ` no derivation sees `i`: `2 i • d i = 0` and `2 i` is a unit. So `Ω[ℂ⁄ℝ] = 0`\n— the most familiar field extension, with no differentials at all."
    },
    {
      "type": "prose",
      "md": " **How big is `Ω`?** Its dimension over `F` is the size of a *separating*\ntranscendence basis: with `s` algebraically independent and `F` separable over\n`K(s)`, the rank is `#s`. The word \"separating\" is the whole content — the\ntranscendence degree alone does not control the rank (D.1 below), and no place\ncan supply a separating transcendental. The `#s = 1` case is the block above, whose\n`Basis` is `kaehlerAdjoinBasis` at `s = {x}`. ",
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
      "doc": "The other half of the crux: the same substitution moves the differential, by a\nterm the place has no record of. This is the Leibniz rule computed in Zone B with\n`a = u` and `b = t_v`: the first summand is `d t_v` rescaled, the second is the moving\nterm, and it is exactly the defect that `I²` discards in `Ω` but `ord` cannot see.\n`Derivation.leibniz` below is that computation, packaged — no new content."
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
      "md": " Why it cannot be derived from place data: a place is a structure on `F` alone\n(Zone A), while the rank of `Ω` is a property of the *extension*. Standard\ncounterexample, not formalised here: `k` of characteristic `p`, `K = k(X)`,\n`F = K(x)(t)` with `x ^ p = X` and `t` transcendental over `K(x)`. Then\n`trdeg(F/K) = 1` and every place still has a uniformiser; `Ω[K(x)/K]` is free of rank\none on `d x` (`x ^ p = X` differentiates to `p x ^ (p - 1) d x = 0`, which is *no*\nrelation in characteristic `p` — Zone B's p-th-power blindness); and `F = K(x)(t)`\nsplits `Ω` as `Ω[K(x)/K] ⊗ F` plus `F · d t`, so `finrank_F Ω[F⁄K] = 2`. A one-variable\nfunction field with a two-dimensional `Ω`, every uniformiser none the wiser, and no `ω`\ngenerating: exactly what `kaehler_free_rank_one` excludes, and why it must be an axiom\nrather than a theorem about places. The positive control is the rational function\nfield: ",
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
      "md": "* **Delete `[DCoordGenerates]`** from `exists_eq_smul_dCoord` (Zone C) and the claim\n  becomes false: no single `f` gives `ω = f • d t_v` for every `ω` unless `d t_v`\n  spans. That is the content of the class, and why it cannot be an instance.\n\n* **Delete `[Nontrivial Ω]`** from `dCoord_ne_zero`: with `Ω` subsingleton every\n  differential is zero, so `d t_v ≠ 0` needs the rank-one axiom (D.1), not generation.\n\n* **Change the uniformiser.** `u * t_v` has order `1` for every unit `u`, but\n  `d (u * t_v)` picks up the Leibniz term `t_v • d u` (Zone B). For `u` a constant the\n  term dies (`Derivation.map_algebraMap`), so to see a change you need a unit outside\n  the image of `K` — which `ord` cannot distinguish from a constant. Prove the case\n  `u = algebraMap K F c` to watch the mechanism: it works only *because* constants have\n  no differential.\n\n* **Replace `CharP F p`** by `CharZero F` in the p-th-power example and watch the proof\n  die at `(p : F) = 0`: in characteristic zero `d (a ^ n) = n • a ^ (n - 1) • d a` is not\n  zero for transcendental `a`, so `d` no longer contains the p-th powers. That is why\n  the inseparable counterexamples of D.1 and of the transcendental block live in\n  characteristic `p`.\n\n* **`differentialCoeff` is total**: an `if` returning `0` outside the span, so\n  `ordDifferential` reports \"no pole, no zero\" there — and `HasCanonicalDivisor` reads\n  that total function at every place. The D.2 hypothesis is what keeps the divisor from\n  silently losing those places, the same pattern as `genus` and `finrank` in the\n  hierarchy sheet: a total definition with a junk branch, plus a hypothesis that the\n  branch is never taken.\n\n* **Make `x` algebraic.** In Zone B's transcendental block, `Transcendental K x` is used\n  at exactly one point, the renaming `K(X) ≅ K(x)`, and for algebraic `x` there is no\n  such coordinate: `K[X] → K(x)` is a surjection with nonzero kernel. The conclusion\n  flips, too: for `x` algebraic and separable over `K`, `Ω[K(x)⁄K] = 0` (a finite\n  separable extension is formally étale, so `Ω` base-changes from `Ω[K⁄K] = 0`), hence\n  `d x = 0`. Nonzero differential is a property of *transcendence*.\n\n* **Drop the square.** `Ω` is `I ⧸ I²` and not `I` solely because the defect of Leibniz\n  is a *square*: `s ↦ 1 ⊗ₜ s - s ⊗ₜ 1` is not a derivation into `I` (its defect at\n  `a * b` is `da * db`), and in the model `R[x]` that defect is `(y - x)² ≠ 0`. Run\n  Zone B's last example with `Ideal.toCotangent` replaced by the inclusion\n  `I → F ⊗[K] F`, and the step `Ideal.toCotangent_eq, pow_two` is the only one that\n  fails — the only step where `I²` was used.\n\n* **One layer down.** The *local* statement — `m_v / m_v²` one-dimensional over\n  `κ(v)`, `m_v = (t_v)` — is free from the DVR structure, and `ord_uniformizer` is its\n  `F`-side shadow. What is not free is the passage from that local one-dimensionality to\n  a generator of the global `Ω`: compare `IsDiscreteValuationRing.exists_irreducible`\n  (Zone A, no curve hypotheses) with `DCoordGenerates` (Zone C, a hypothesis on every\n  rung). ",
      "zone": "E"
    },
    {
      "type": "prose",
      "md": "Oldest first. Each entry: question, one-line answer, and a pointer to the zone\nthat was edited — the answer is one line by design; the long version is the zone.\n\n* (2026-10-23) *Worksheet created.*\n* (2026-10-23) **Q1.** A uniformiser — why does it not give a differential, and why is\n  `kaehler_free_rank_one` an axiom? — `d t_v` is an *element*, not a basis: rank is a\n  property of the extension (D.1), generation at a place is a hypothesis (D.2), finite\n  support is a theorem over a perfect field (D.3). Zones A, C, D.\n* (2026-10-23) **Q2.** Is the axiom \"there is a nonzero differential\"? — No, it is\n  \"`Ω` is a line\", strictly stronger; existence is derived (`instNontrivialKaehler`) and\n  would give neither the coefficient, nor the order, nor independence of `t_v`. D.1.\n* (2026-10-23) **Q3.** Does `ord` plus `t_v` determine `d f`? — No: `d (u · t_v)` carries\n  `t_v · d u`, which `ord` cannot see; the two crux examples of Zone C are that, one for\n  `ord` and one for `d`.\n* (2026-10-23) **Q4.** Why is `differentialCoeff` total, with a `0` branch? — So that\n  `ordDifferential` and `HasCanonicalDivisor` are definitions and not conditional\n  statements; the hypothesis is a class the honest lemmas require, and the junk branch\n  is what Zone E pokes at. Zone C.\n* (2026-10-30) **Q5.** What does `irreducible_iff_uniformizer` say, and how is `ord`\n  built? — It is the two spellings `Irreducible ϖ ↔ m_v = (ϖ)`, so `rw` converts either\n  way; and `ord = -log ∘ adicValuation`, with `ℤᵐ⁰` multiplicative, junk `log 0 = 0`,\n  and the outer minus turning `exp (-1)` into order `1`. Zone A.\n* (2026-10-30) **Q6.** What is the ideal in the definition of `KaehlerDifferential`? —\n  The diagonal: two copies of `F` in `F ⊗[K] F`, `lmul'` identifies them, `I = ker lmul'`,\n  generated by `1 ⊗ₜ f - f ⊗ₜ 1`; `Ω = I ⧸ I²` keeps the first-order part, and that is\n  Leibniz and what makes `Ω` an `F`-module. Zone B.\n* (2026-10-30) **Q7.** Is an elementary tensor with `a * b = 1` in the kernel? — No:\n  `lmul' (a ⊗ₜ b) = a * b`, so `∈ I` means `a * b = 0`; the interesting members of `I`\n  are its *sums*, whose summands are not in `I`. Zone B.\n* (2026-10-30) **Q8.** Why is the kernel an *ideal*? — `F ⊗[K] F` is a commutative ring\n  and `lmul'` is multiplicative, so `I` is closed under multiplication by any ring\n  element; `Ideal R` is `Submodule R R` plus that one closure. Payoff: `I²` exists, and\n  `(F ⊗ F) ⧸ I ≅ F` is the ring `Ω` is a module over. Zone B.\n* (2026-10-30) **Q9.** Where is the multiplication on `F ⊗[K] F` defined? — Not in this\n  sheet: instance search from `[Algebra K F]` (`LinearMap.mul`, `map₂`,\n  `instCommRing`, `tmul_mul_tmul`); with only `Module K F` there is no `*`. Zone B.\n* (2026-10-30) **Q10.** Can `s` be moved between the two tensor slots? — No: only scalars\n  cross, multiplication recombines. `s ⊗ₜ 1 - 1 ⊗ₜ s` generates `I`, and its class *is*\n  `d s`; imposing `s ⊗ₜ 1 = 1 ⊗ₜ s` for all `s` gives `Ω = 0`, i.e. unramified. Zone B.\n* (2026-10-31) **Q11.** Why was Leibniz asserted and then quoted from\n  `Derivation.leibniz`? — The assertion *is* the black box: mathlib's `leibniz'` is\n  `toCotangent_eq` + `pow_two` + one `mul_mem_mul` + `convert!`/`ring_nf`, i.e. \"the\n  defect is `Da · Db ∈ I²`\". Zone B computes it, and the same computation is why `Ω` is\n  `I ⧸ I²` and what Zone C's `d (u * t_v)` cites. Zones B, C, E.\n* (2026-10-31) **Q12.** Why is `d x ≠ 0` for transcendental `x`? — Because `d` of a\n  coordinate is `1`: `Ω[K[X]⁄K] ≅ K[X]` by the formal derivative (`d X ↦ 1`), and every\n  step from `K[X]` to `F` is a base change along a formally étale map (localisation,\n  separable extension), so `d x` stays the generator. FLT's `exists_basis` is that base\n  change as an object; in characteristic `p`, `x = y ^ p` breaks it, which is exactly\n  what `IsSeparable` excludes. Zones B, E.\n* (2026-10-31) **Q13.** How does `D` relate to the derivative of calculus over `ℝ` or `ℂ`?\n  — `D f` is `d f`; `f'` is `d f` divided by a frame, `D f = ∑ᵢ (∂f/∂xᵢ) • d xᵢ`, so the\n  classical partials are the coefficients (Zone C's `differentialCoeff`, and\n  `polynomialEquiv` is `n = 1`). In characteristic `0` the dictionary is exact — rank\n  `= trdeg`, kernel `=` the algebraic elements, so \"`f' = 0` ⟹ constant\" holds as far as\n  it can, and the p-th-power collapse is unavailable; `Ω[ℂ⁄ℝ] = 0` while `Ω[ℂ(x)⁄ℂ]` is a\n  line, since rank is transcendence degree, not dimension. Zone B, new block before\n  \"How big is `Ω`\". ",
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
    "ϖ",
    "a",
    "b",
    "s",
    "f",
    "t",
    "x",
    "hx",
    "R",
    "y",
    "S",
    "h",
    "hf",
    "c",
    "ω",
    "A",
    "M",
    "D",
    "p",
    "D'",
    "P",
    "T",
    "hy",
    "hp",
    "n",
    "hn",
    "u",
    "hu",
    "hord"
  ],
  "seed_cards": ["AlgHom","AlgHom.toRingHom","Algebra.FormallyEtale","Algebra.FormallyEtale.of_isLocalization","Algebra.FormallyEtale.of_isSeparable","Algebra.TensorProduct.algebraMap_apply","Algebra.TensorProduct.includeLeft","Algebra.TensorProduct.includeRight","Algebra.TensorProduct.instCommRing","Algebra.TensorProduct.instMul","Algebra.TensorProduct.instSemiring","Algebra.TensorProduct.leftAlgebra","Algebra.TensorProduct.lmul'","Algebra.TensorProduct.lmul'_apply_tmul","Algebra.TensorProduct.mul","Algebra.TensorProduct.one_def","Algebra.TensorProduct.tmul_mul_tmul","AlgebraicCurve.HasCanonicalDivisor","AlgebraicCurve.HasCanonicalLocalResidueKStar","AlgebraicCurve.HasSeparableResidue","AlgebraicCurve.HasSeparableResidue.of_perfectField","AlgebraicCurve.IsCurveOver.exists_separating_transcendental","AlgebraicCurve.IsCurveOver.instNontrivialKaehler","AlgebraicCurve.IsCurveOver.kaehler_free_rank_one","AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne","AlgebraicCurve.IsCurveOver.one_le_trdeg","AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField","AlgebraicCurve.IsCurveOver.trdeg_le_one","AlgebraicCurve.KaehlerRankOne","AlgebraicCurve.Place","AlgebraicCurve.Place.CanonicalLocalResidueDataK","AlgebraicCurve.Place.DCoordGenerates","AlgebraicCurve.Place.FiniteResidue","AlgebraicCurve.Place.ResidueField","AlgebraicCurve.Place.adicValuation","AlgebraicCurve.Place.dCoord","AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField","AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop","AlgebraicCurve.Place.dCoord_ne_zero","AlgebraicCurve.Place.deg","AlgebraicCurve.Place.differentialCoeff","AlgebraicCurve.Place.differentialCoeff_dCoord","AlgebraicCurve.Place.differentialCoeff_smul_dCoord","AlgebraicCurve.Place.differentialCoeff_unique","AlgebraicCurve.Place.differentialCoeff_zero","AlgebraicCurve.Place.exists_eq_smul_dCoord","AlgebraicCurve.Place.exists_unit_mul_zpow","AlgebraicCurve.Place.gate_ordDifferential_dCoord","AlgebraicCurve.Place.heightOneSpectrum","AlgebraicCurve.Place.mem_iff_ord_nonneg","AlgebraicCurve.Place.min_ord_le_ord_add","AlgebraicCurve.Place.ord","AlgebraicCurve.Place.ordDifferential","AlgebraicCurve.Place.ordDifferential_smul","AlgebraicCurve.Place.ord_algebraMap","AlgebraicCurve.Place.ord_coe_unit","AlgebraicCurve.Place.ord_inv","AlgebraicCurve.Place.ord_mul","AlgebraicCurve.Place.ord_uniformizer","AlgebraicCurve.Place.ord_uniformizerSubring","AlgebraicCurve.Place.ord_zero","AlgebraicCurve.Place.ord_zpow","AlgebraicCurve.Place.uniformizer","AlgebraicCurve.Place.uniformizerSubring","AlgebraicCurve.Place.uniformizer_ne_zero","AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne","AlgebraicCurve.ResidueTheoremK","AlgebraicCurve.WeilDualityAdelic","AlgebraicCurve.canonicalDivisorOf","AlgebraicCurve.canonicalDivisorOf_apply","AlgebraicCurve.finrank_kaehler_eq_card_of_separating","AlgebraicCurve.finrank_kaehler_eq_card_of_separating'","AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver","AlgebraicCurve.kaehlerAdjoinBasis","AlgebraicCurve.kaehlerRankOne_of_transcendental","AlgebraicCurve.kaehlerRankOne_ratFunc","Classical.choose","Derivation","Derivation.leibniz","Derivation.leibniz_pow","Derivation.liftKaehlerDifferential","Derivation.liftKaehlerDifferential_comp_D","Derivation.map_algebraMap","Derivation.tensorProductTo","Ideal","Ideal.Cotangent","Ideal.Cotangent.smul_eq_zero_of_mem","Ideal.Quotient.mk","Ideal.map_toCotangent_ker","Ideal.mk_ker","Ideal.mul_mem_left","Ideal.mul_mem_mul","Ideal.toCotangent","Ideal.toCotangent_eq","Irreducible","Irreducible.maximalIdeal_eq","IsDedekindDomain.HeightOneSpectrum.intValuation_le_one","IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem","IsDiscreteValuationRing.exists_irreducible","IsDiscreteValuationRing.irreducible_iff_uniformizer","IsScalarTower.algebraMap_smul","IsSeparable","KaehlerDifferential","KaehlerDifferential.D","KaehlerDifferential.D_apply","KaehlerDifferential.D_ne_zero_of_transcendental","KaehlerDifferential.ideal","KaehlerDifferential.linearMapEquivDerivation","KaehlerDifferential.one_smul_sub_smul_one_mem_ideal","KaehlerDifferential.polynomialEquiv","KaehlerDifferential.polynomialEquiv_D","KaehlerDifferential.polynomialEquiv_symm","KaehlerDifferential.polynomial_D_apply","KaehlerDifferential.span_D_eq_top_of_transcendental","KaehlerDifferential.span_range_eq_ideal","KaehlerDifferential.subsingleton_of_surjective","KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale","KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap","KaehlerDifferential.tensorProductTo_surjective","LinearMap.mul","Module.Basis.baseChange","Module.Basis.map","Module.Basis.ne_zero","Module.Basis.span_eq","Polynomial.X","RatFunc.algEquivOfTranscendental","RatFunc.algEquivOfTranscendental_X","RingHom.ker","RingHom.mem_ker","RingHom.quotientKerEquivOfRightInverse","RingHom.quotientKerEquivOfSurjective","TensorProduct","TensorProduct.map₂","Transcendental.pow","WithZero","WithZero.exp","WithZero.log","WithZero.logEquiv","WithZero.log_mul","WithZero.map₂","pow_two"],
  "card_count": 353,
  "modules": ["FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates","FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor","FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler","FLTForHuman.AlgebraicCurve.Defs.AdelicIndex","FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor","FLTForHuman.AlgebraicCurve.Defs.Divisor","FLTForHuman.AlgebraicCurve.Defs.IsCurveOver","FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental","FLTForHuman.AlgebraicCurve.Defs.LocalResidue","FLTForHuman.AlgebraicCurve.Defs.Place","FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus","FLTForHuman.AlgebraicCurve.Defs.PushPull","FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows","FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental","FLTForHuman.AlgebraicCurve.LocalResidue.Instance","FLTForHuman.AlgebraicCurve.P1.DXCoeff","FLTForHuman.AlgebraicCurve.P1.UnitFinite","Init.Classical","Init.Core","Init.Data.Cast","Init.Data.Function","Init.Data.Int.Basic","Init.Prelude","Mathlib.Algebra.Algebra.Basic","Mathlib.Algebra.Algebra.Bilinear","Mathlib.Algebra.Algebra.Defs","Mathlib.Algebra.Algebra.Equiv","Mathlib.Algebra.Algebra.Hom","Mathlib.Algebra.Algebra.Operations","Mathlib.Algebra.Algebra.Subalgebra.Basic","Mathlib.Algebra.Algebra.Subalgebra.Lattice","Mathlib.Algebra.Algebra.Tower","Mathlib.Algebra.Field.Defs","Mathlib.Algebra.FreeMonoid.Basic","Mathlib.Algebra.Group.Action.Defs","Mathlib.Algebra.Group.Defs","Mathlib.Algebra.Group.Hom.Defs","Mathlib.Algebra.Group.Irreducible.Defs","Mathlib.Algebra.Group.Monoid","Mathlib.Algebra.Group.Pi.Basic","Mathlib.Algebra.Group.Submonoid.Defs","Mathlib.Algebra.Group.TypeTags.Basic","Mathlib.Algebra.Group.Units.Defs","Mathlib.Algebra.Group.WithOne.Defs","Mathlib.Algebra.Group.WithOne.Map","Mathlib.Algebra.GroupWithZero.WithZero","Mathlib.Algebra.Module.Defs","Mathlib.Algebra.Module.Equiv.Defs","Mathlib.Algebra.Module.LinearMap.Defs","Mathlib.Algebra.Module.LinearMap.End","Mathlib.Algebra.Module.Pi","Mathlib.Algebra.Module.Submodule.Defs","Mathlib.Algebra.Module.Submodule.Equiv","Mathlib.Algebra.Module.Submodule.Ker","Mathlib.Algebra.Module.Submodule.LinearMap","Mathlib.Algebra.Module.Submodule.Map","Mathlib.Algebra.Module.Submodule.RestrictScalars","Mathlib.Algebra.MonoidAlgebra.Basic","Mathlib.Algebra.MonoidAlgebra.Defs","Mathlib.Algebra.MvPolynomial.Basic","Mathlib.Algebra.Order.Monoid.TypeTags","Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags","Mathlib.Algebra.Polynomial.AlgebraMap","Mathlib.Algebra.Polynomial.Basic","Mathlib.Algebra.Polynomial.Derivation","Mathlib.Algebra.Polynomial.Derivative","Mathlib.Algebra.Quotient","Mathlib.Algebra.Ring.CompTypeclasses","Mathlib.Algebra.Ring.Defs","Mathlib.Algebra.Ring.Equiv","Mathlib.Algebra.Ring.Hom.Defs","Mathlib.Basic.Nontrivial.Defs","Mathlib.Data.Finset.Card","Mathlib.Data.Finset.Defs","Mathlib.Data.Finsupp.Defs","Mathlib.Data.Finsupp.SMul","Mathlib.Data.FunLike.Basic","Mathlib.Data.Nat.Cast.Defs","Mathlib.Data.Option.NAry","Mathlib.Data.Set.Defs","Mathlib.Data.Set.Operations","Mathlib.FieldTheory.IntermediateField.Adjoin.Defs","Mathlib.FieldTheory.IntermediateField.Basic","Mathlib.FieldTheory.Minpoly.Basic","Mathlib.FieldTheory.Perfect","Mathlib.FieldTheory.RatFunc.AsPolynomial","Mathlib.FieldTheory.RatFunc.Defs","Mathlib.FieldTheory.Separable","Mathlib.GroupTheory.Congruence.Defs","Mathlib.LinearAlgebra.Basis.Basic","Mathlib.LinearAlgebra.Basis.Defs","Mathlib.LinearAlgebra.BilinearMap","Mathlib.LinearAlgebra.Dimension.Finrank","Mathlib.LinearAlgebra.Dual.Defs","Mathlib.LinearAlgebra.FiniteDimensional.Defs","Mathlib.LinearAlgebra.FreeModule.Basic","Mathlib.LinearAlgebra.Quotient.Basic","Mathlib.LinearAlgebra.Quotient.Defs","Mathlib.LinearAlgebra.Span.Defs","Mathlib.LinearAlgebra.TensorProduct.Basic","Mathlib.LinearAlgebra.TensorProduct.Basis","Mathlib.LinearAlgebra.TensorProduct.Defs","Mathlib.LinearAlgebra.TensorProduct.Map","Mathlib.LinearAlgebra.TensorProduct.Tower","Mathlib.Logic.Equiv.Defs","Mathlib.Logic.Equiv.Prod","Mathlib.Order.Notation","Mathlib.RingTheory.Algebraic.Basic","Mathlib.RingTheory.Algebraic.Defs","Mathlib.RingTheory.AlgebraicIndependent.Basic","Mathlib.RingTheory.AlgebraicIndependent.Defs","Mathlib.RingTheory.DedekindDomain.AdicValuation","Mathlib.RingTheory.DedekindDomain.Basic","Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas","Mathlib.RingTheory.Derivation.Basic","Mathlib.RingTheory.DiscreteValuationRing.Basic","Mathlib.RingTheory.EssentialFiniteness","Mathlib.RingTheory.Etale.Basic","Mathlib.RingTheory.Etale.Field","Mathlib.RingTheory.Etale.Kaehler","Mathlib.RingTheory.Ideal.Cotangent","Mathlib.RingTheory.Ideal.Defs","Mathlib.RingTheory.Ideal.Maps","Mathlib.RingTheory.Ideal.Operations","Mathlib.RingTheory.Ideal.Quotient.Defs","Mathlib.RingTheory.Ideal.Quotient.Operations","Mathlib.RingTheory.Ideal.Span","Mathlib.RingTheory.Kaehler.Basic","Mathlib.RingTheory.Kaehler.Polynomial","Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs","Mathlib.RingTheory.LocalRing.ResidueField.Defs","Mathlib.RingTheory.Localization.Defs","Mathlib.RingTheory.Localization.FractionRing","Mathlib.RingTheory.TensorProduct.Basic","Mathlib.RingTheory.TensorProduct.Maps","Mathlib.RingTheory.Valuation.Basic","Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing","Mathlib.RingTheory.Valuation.ValuationSubring","Mathlib.SetTheory.Cardinal.Defs"]
};
