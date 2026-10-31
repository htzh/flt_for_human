window.PLAY_MODULES = window.PLAY_MODULES || {};
window.PLAY_INDEX = {
  "version": 3,
  "worksheets": {"CardNTorsion":{"slug":"CardNTorsion","title":"the card `n`-torsion theorem","tagline":"`#E[n](K) = n²`","subject":"the card `n`-torsion theorem: the `n`-torsion of an elliptic curve over an algebraically closed field has `n²` elements","intro":"The port's main theorem as the compiler sees it: over an algebraically closed field, the `n`-torsion of an elliptic curve has `n²` elements. The worksheet unpacks the statement, the fibre count, and the division-polynomial engine behind it.","reads":"FLTForHuman/Elliptic/TorsionCard.lean, the port of the pinned FLT P2M/Sol/S_WeierstrassCurve_card_torsion_of_isAlgClosed.lean, re-exported at Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean:8-9 <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_card_torsion_of_isAlgClosed.lean#L8-L9>","status":"open","date":"2026-10-14","file":"lean/play/CardNTorsion.lean","card_count":121,"seed_count":47},"DivisionPolynomials":{"slug":"DivisionPolynomials","title":"the division polynomials","tagline":"ψ, Ψ, ΨSq, Φ, φ and the EDS under them","subject":"the division polynomials of a Weierstrass curve, and the elliptic divisibility sequence (EDS) layer that generates them","intro":"Companion to `CardNTorsion.lean`, which reads the *point* side of the same story; this worksheet reads the *polynomial* side: what `W.Φ`, `W.Ψ`, `W.ΨSq`, `W.ψ` are, which recurrence generates them, and what the EDS vocabulary buys. The mathematics is written up in `math/025-elliptic-nets-division-polynomials-and-the-invariant.md`.","reads":"FLTForHuman/Elliptic/Omega.lean, the top of the EDS cone: it imports Net → RedInvar → Complement → EllSequence → EDS → DivisionPolynomial, and hence mathlib's AlgebraicGeometry/EllipticCurve/DivisionPolynomial/Basic.lean and NumberTheory/EllipticDivisibilitySequence.lean","status":"open","date":"2026-10-15","file":"lean/play/DivisionPolynomials.lean","card_count":182,"seed_count":107},"PlacesAndDifferentials":{"slug":"PlacesAndDifferentials","title":"places and differentials","tagline":"why a uniformiser is not a differential","subject":"the two halves of the local theory and the gap between them: a place always has a uniformiser and an order, a differential is a global derivation, and nothing in the place data produces one. That gap is why `IsCurveOver` carries `kaehler_free_rank_one` as an axiom, and why every rung that names a canonical divisor carries `[∀ v, v.DCoordGenerates]` per place.","intro":"A place gives an order `ord_v` and a uniformiser `t_v`; a differential lives in the Kähler module `Ω[F⁄K]`, which is an object of the whole field extension and mentions no place — literally so: `Ω[F⁄K]` is `I ⧸ I²` for `I` the ideal of the diagonal of `F ⊗[K] F`, so the construction sees nothing but the ring map `K → F`. This sheet separates the two, exhibits each gate the port puts between them (`dCoord`, `DCoordGenerates`, `differentialCoeff`, `ordDifferential`, `HasCanonicalDivisor`), shows that the same order admits different differentials, and lands on the axiom that no amount of place data can supply: `kaehler_free_rank_one`.","reads":"FLTForHuman/AlgebraicCurve/Defs/Place.lean, Defs/CanonicalDivisor.lean, Defs/LocalResidue.lean, Defs/KaehlerTranscendental.lean, P1/DXCoeff.lean, IsCurveOver/SeparatingTranscendental.lean, Canonical/HasCanonicalDivisor.lean, Defs/RiemannRochRows.lean","status":"open","date":"2026-10-23","file":"lean/play/PlacesAndDifferentials.lean","card_count":353,"seed_count":141},"RiemannRochHierarchy":{"slug":"RiemannRochHierarchy","title":"the Riemann–Roch statement hierarchy","tagline":"places, divisors, ℓ / i / Ω","subject":"the *shape* of the Riemann–Roch statements: rung 0 (`IsCurveOver`) through rung 4, the three spaces that are all called \"dimension\" (ℓ, i, Ω), the canonical divisor with its two genera, and the wrapper stack that shrinks the hypothesis list","intro":"Riemann–Roch appears at half a dozen strengths — an inequality, an index formula, three duality forms, the identity — and they are not a chain but a small lattice with two directions. This sheet lays the rungs out as the port states them, separates the three things called \"dimension\" (ℓ(D), the adele quotient index i(D), the annihilator Ω(D)), pins the canonical divisor and the two genera, and ends at the four wrappers that carry the theorem down to a bare transcendental generator.","reads":"FLTForHuman/AlgebraicCurve/Defs/Repartitions.lean, Defs/AdelicIndex.lean, Defs/CanonicalDivisor.lean, Defs/IsCurveOver.lean, Defs/RiemannRochRows.lean, RiemannRoch/Assembly.lean, Genus/Index.lean, Genus/Stichtenoth.lean, ResidueTheorem/RRAssembly.lean","status":"open","date":"2026-10-23","file":"lean/play/RiemannRochHierarchy.lean","card_count":252,"seed_count":115}},
  "modules": [
    "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
    "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
    "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
    "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
    "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "FLTForHuman.AlgebraicCurve.Defs.Place",
    "FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus",
    "FLTForHuman.AlgebraicCurve.Defs.PushPull",
    "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler",
    "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "FLTForHuman.AlgebraicCurve.LocalResidue.Instance",
    "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
    "FLTForHuman.AlgebraicCurve.P1.UnitFinite",
    "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly",
    "FLTForHuman.Elliptic.Bridge",
    "FLTForHuman.Elliptic.Complement",
    "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.EDS",
    "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.Net",
    "FLTForHuman.Elliptic.Omega",
    "FLTForHuman.Elliptic.RedInvar",
    "FLTForHuman.Elliptic.TorsionCard",
    "Init.Classical",
    "Init.Core",
    "Init.Data.Cast",
    "Init.Data.Function",
    "Init.Data.Int.Basic",
    "Init.Data.Int.DivMod.Basic",
    "Init.Data.List.Basic",
    "Init.Data.Nat.Coprime",
    "Init.Prelude",
    "Init.WF",
    "Mathlib.Algebra.Algebra.Basic",
    "Mathlib.Algebra.Algebra.Bilinear",
    "Mathlib.Algebra.Algebra.Defs",
    "Mathlib.Algebra.Algebra.Equiv",
    "Mathlib.Algebra.Algebra.Hom",
    "Mathlib.Algebra.Algebra.Operations",
    "Mathlib.Algebra.Algebra.Pi",
    "Mathlib.Algebra.Algebra.Subalgebra.Basic",
    "Mathlib.Algebra.Algebra.Subalgebra.Lattice",
    "Mathlib.Algebra.Algebra.Tower",
    "Mathlib.Algebra.BigOperators.Finsupp.Basic",
    "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
    "Mathlib.Algebra.Divisibility.Basic",
    "Mathlib.Algebra.Field.Defs",
    "Mathlib.Algebra.FreeMonoid.Basic",
    "Mathlib.Algebra.Group.Action.Defs",
    "Mathlib.Algebra.Group.Action.Pi",
    "Mathlib.Algebra.Group.Defs",
    "Mathlib.Algebra.Group.Equiv.Defs",
    "Mathlib.Algebra.Group.Even",
    "Mathlib.Algebra.Group.EvenFunction",
    "Mathlib.Algebra.Group.Hom.Basic",
    "Mathlib.Algebra.Group.Hom.Defs",
    "Mathlib.Algebra.Group.Irreducible.Defs",
    "Mathlib.Algebra.Group.Monoid",
    "Mathlib.Algebra.Group.Pi.Basic",
    "Mathlib.Algebra.Group.Subgroup.Defs",
    "Mathlib.Algebra.Group.Subgroup.Finite",
    "Mathlib.Algebra.Group.Subgroup.Ker",
    "Mathlib.Algebra.Group.Subgroup.Map",
    "Mathlib.Algebra.Group.Submonoid.Defs",
    "Mathlib.Algebra.Group.TypeTags.Basic",
    "Mathlib.Algebra.Group.Units.Defs",
    "Mathlib.Algebra.Group.WithOne.Defs",
    "Mathlib.Algebra.Group.WithOne.Map",
    "Mathlib.Algebra.GroupWithZero.Action.Defs",
    "Mathlib.Algebra.GroupWithZero.Defs",
    "Mathlib.Algebra.GroupWithZero.Hom",
    "Mathlib.Algebra.GroupWithZero.NonZeroDivisors",
    "Mathlib.Algebra.GroupWithZero.WithZero",
    "Mathlib.Algebra.Module.Defs",
    "Mathlib.Algebra.Module.Equiv.Defs",
    "Mathlib.Algebra.Module.LinearMap.Defs",
    "Mathlib.Algebra.Module.LinearMap.End",
    "Mathlib.Algebra.Module.Pi",
    "Mathlib.Algebra.Module.Submodule.Defs",
    "Mathlib.Algebra.Module.Submodule.Equiv",
    "Mathlib.Algebra.Module.Submodule.Ker",
    "Mathlib.Algebra.Module.Submodule.Lattice",
    "Mathlib.Algebra.Module.Submodule.LinearMap",
    "Mathlib.Algebra.Module.Submodule.Map",
    "Mathlib.Algebra.Module.Submodule.Range",
    "Mathlib.Algebra.Module.Submodule.RestrictScalars",
    "Mathlib.Algebra.Module.Torsion.Basic",
    "Mathlib.Algebra.MonoidAlgebra.Basic",
    "Mathlib.Algebra.MonoidAlgebra.Defs",
    "Mathlib.Algebra.MvPolynomial.Basic",
    "Mathlib.Algebra.MvPolynomial.Eval",
    "Mathlib.Algebra.Order.Group.Unbundled.Abs",
    "Mathlib.Algebra.Order.Monoid.TypeTags",
    "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
    "Mathlib.Algebra.Polynomial.AlgebraMap",
    "Mathlib.Algebra.Polynomial.Basic",
    "Mathlib.Algebra.Polynomial.Bivariate",
    "Mathlib.Algebra.Polynomial.Degree.Defs",
    "Mathlib.Algebra.Polynomial.Derivation",
    "Mathlib.Algebra.Polynomial.Derivative",
    "Mathlib.Algebra.Polynomial.Eval.Defs",
    "Mathlib.Algebra.Quotient",
    "Mathlib.Algebra.Ring.Basic",
    "Mathlib.Algebra.Ring.CompTypeclasses",
    "Mathlib.Algebra.Ring.Defs",
    "Mathlib.Algebra.Ring.Equiv",
    "Mathlib.Algebra.Ring.Hom.Defs",
    "Mathlib.Algebra.Ring.NegOnePow",
    "Mathlib.Algebra.Ring.Parity",
    "Mathlib.Algebra.Ring.Pi",
    "Mathlib.Algebra.Squarefree.Basic",
    "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
    "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point",
    "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
    "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "Mathlib.Basic.ExistsUnique",
    "Mathlib.Basic.Finite.Defs",
    "Mathlib.Basic.Logic.Basic",
    "Mathlib.Basic.Nontrivial.Defs",
    "Mathlib.Data.Finset.Card",
    "Mathlib.Data.Finset.Defs",
    "Mathlib.Data.Finsupp.Defs",
    "Mathlib.Data.Finsupp.SMul",
    "Mathlib.Data.Finsupp.Single",
    "Mathlib.Data.FunLike.Basic",
    "Mathlib.Data.Int.Init",
    "Mathlib.Data.Nat.Cast.Defs",
    "Mathlib.Data.Nat.DvdSequence",
    "Mathlib.Data.Nat.Factorization.Induction",
    "Mathlib.Data.Nat.Prime.Defs",
    "Mathlib.Data.Option.NAry",
    "Mathlib.Data.Set.Defs",
    "Mathlib.Data.Set.Operations",
    "Mathlib.FieldTheory.IntermediateField.Adjoin.Defs",
    "Mathlib.FieldTheory.IntermediateField.Basic",
    "Mathlib.FieldTheory.IsAlgClosed.Basic",
    "Mathlib.FieldTheory.Minpoly.Basic",
    "Mathlib.FieldTheory.Perfect",
    "Mathlib.FieldTheory.RatFunc.AsPolynomial",
    "Mathlib.FieldTheory.RatFunc.Defs",
    "Mathlib.FieldTheory.Separable",
    "Mathlib.GroupTheory.Congruence.Defs",
    "Mathlib.GroupTheory.Coset.Defs",
    "Mathlib.GroupTheory.OrderOfElement",
    "Mathlib.GroupTheory.OreLocalization.OreSet",
    "Mathlib.GroupTheory.Perm.Cycle.Type",
    "Mathlib.GroupTheory.QuotientGroup.Defs",
    "Mathlib.LinearAlgebra.Basis.Basic",
    "Mathlib.LinearAlgebra.Basis.Defs",
    "Mathlib.LinearAlgebra.BilinearMap",
    "Mathlib.LinearAlgebra.Dimension.Basic",
    "Mathlib.LinearAlgebra.Dimension.Finite",
    "Mathlib.LinearAlgebra.Dimension.Finrank",
    "Mathlib.LinearAlgebra.Dual.Defs",
    "Mathlib.LinearAlgebra.Dual.Lemmas",
    "Mathlib.LinearAlgebra.FiniteDimensional.Basic",
    "Mathlib.LinearAlgebra.FiniteDimensional.Defs",
    "Mathlib.LinearAlgebra.FreeModule.Basic",
    "Mathlib.LinearAlgebra.LinearIndependent.Defs",
    "Mathlib.LinearAlgebra.Quotient.Basic",
    "Mathlib.LinearAlgebra.Quotient.Defs",
    "Mathlib.LinearAlgebra.Span.Defs",
    "Mathlib.LinearAlgebra.TensorProduct.Basic",
    "Mathlib.LinearAlgebra.TensorProduct.Basis",
    "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "Mathlib.LinearAlgebra.TensorProduct.Map",
    "Mathlib.LinearAlgebra.TensorProduct.Tower",
    "Mathlib.Logic.Equiv.Defs",
    "Mathlib.Logic.Equiv.Prod",
    "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "Mathlib.Order.Defs.PartialOrder",
    "Mathlib.Order.Notation",
    "Mathlib.Order.SetNotation",
    "Mathlib.Order.WithBot",
    "Mathlib.RingTheory.Algebraic.Basic",
    "Mathlib.RingTheory.Algebraic.Defs",
    "Mathlib.RingTheory.AlgebraicIndependent.Basic",
    "Mathlib.RingTheory.AlgebraicIndependent.Defs",
    "Mathlib.RingTheory.Coprime.Basic",
    "Mathlib.RingTheory.DedekindDomain.AdicValuation",
    "Mathlib.RingTheory.DedekindDomain.Basic",
    "Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas",
    "Mathlib.RingTheory.Derivation.Basic",
    "Mathlib.RingTheory.DiscreteValuationRing.Basic",
    "Mathlib.RingTheory.EssentialFiniteness",
    "Mathlib.RingTheory.Etale.Basic",
    "Mathlib.RingTheory.Etale.Field",
    "Mathlib.RingTheory.Etale.Kaehler",
    "Mathlib.RingTheory.Finiteness.Defs",
    "Mathlib.RingTheory.Ideal.Cotangent",
    "Mathlib.RingTheory.Ideal.Defs",
    "Mathlib.RingTheory.Ideal.Maps",
    "Mathlib.RingTheory.Ideal.Operations",
    "Mathlib.RingTheory.Ideal.Quotient.Defs",
    "Mathlib.RingTheory.Ideal.Quotient.Operations",
    "Mathlib.RingTheory.Ideal.Span",
    "Mathlib.RingTheory.IntegralClosure.Algebra.Defs",
    "Mathlib.RingTheory.Kaehler.Basic",
    "Mathlib.RingTheory.Kaehler.Polynomial",
    "Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs",
    "Mathlib.RingTheory.LocalRing.ResidueField.Basic",
    "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
    "Mathlib.RingTheory.Localization.Defs",
    "Mathlib.RingTheory.Localization.FractionRing",
    "Mathlib.RingTheory.TensorProduct.Basic",
    "Mathlib.RingTheory.TensorProduct.Maps",
    "Mathlib.RingTheory.Trace.Defs",
    "Mathlib.RingTheory.Valuation.Basic",
    "Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing",
    "Mathlib.RingTheory.Valuation.ValuationSubring",
    "Mathlib.SetTheory.Cardinal.Defs",
    "Mathlib.SetTheory.Cardinal.Finite"
  ],
  "names": [
    "AddCommGroup",
    "AddCommMonoid",
    "AddCommMonoidWithOne",
    "AddCon.Quotient",
    "AddEquiv",
    "AddGroup",
    "AddMonoid",
    "AddMonoidAlgebra.algebra",
    "AddMonoidAlgebra.nonAssocSemiring",
    "AddMonoidHom",
    "AddMonoidHom.add",
    "AddMonoidHom.ker",
    "AddMonoidHom.mulRight",
    "AddSubgroup",
    "AddSubgroup.addSubgroupOf",
    "AddSubgroup.card_bot",
    "AlgEquiv",
    "AlgHom",
    "AlgHom.funLike",
    "AlgHom.restrictScalars",
    "AlgHom.toRingHom",
    "Algebra",
    "Algebra.EssFiniteType",
    "Algebra.FormallyEtale",
    "Algebra.FormallyEtale.of_isLocalization",
    "Algebra.FormallyEtale.of_isSeparable",
    "Algebra.IsIntegral",
    "Algebra.IsSeparable",
    "Algebra.TensorProduct.algebraMap_apply",
    "Algebra.TensorProduct.includeLeft",
    "Algebra.TensorProduct.includeLeftRingHom",
    "Algebra.TensorProduct.includeRight",
    "Algebra.TensorProduct.instCommRing",
    "Algebra.TensorProduct.instMul",
    "Algebra.TensorProduct.instSemiring",
    "Algebra.TensorProduct.leftAlgebra",
    "Algebra.TensorProduct.lmul'",
    "Algebra.TensorProduct.lmul''",
    "Algebra.TensorProduct.lmul'_apply_tmul",
    "Algebra.TensorProduct.mul",
    "Algebra.TensorProduct.one_def",
    "Algebra.TensorProduct.tmul_mul_tmul",
    "Algebra.adjoin",
    "Algebra.algebraMap",
    "Algebra.id",
    "Algebra.linearMap",
    "Algebra.lsmul",
    "Algebra.to_smulCommClass",
    "Algebra.trace",
    "Algebra.trdeg",
    "AlgebraicCurve.ConstantsAreBase",
    "AlgebraicCurve.Divisor",
    "AlgebraicCurve.Divisor.IsPrincipal",
    "AlgebraicCurve.Divisor.degZero",
    "AlgebraicCurve.Divisor.degree",
    "AlgebraicCurve.Divisor.degree_eq_sum",
    "AlgebraicCurve.Divisor.degree_single",
    "AlgebraicCurve.Divisor.principal",
    "AlgebraicCurve.FunctionFieldRiemannRoch",
    "AlgebraicCurve.H1",
    "AlgebraicCurve.HasCanonicalDivisor",
    "AlgebraicCurve.HasCanonicalDivisor.exists_divisor",
    "AlgebraicCurve.HasCanonicalLocalResidueKStar",
    "AlgebraicCurve.HasLocalResidue",
    "AlgebraicCurve.HasPrincipalDivisors",
    "AlgebraicCurve.HasSeparableResidue",
    "AlgebraicCurve.HasSeparableResidue.of_perfectField",
    "AlgebraicCurve.HasWeilCanonicalDivisor",
    "AlgebraicCurve.IndexOfSpecialtyFinite",
    "AlgebraicCurve.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed",
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental",
    "AlgebraicCurve.IsCurveOver.finrank_kaehler",
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed",
    "AlgebraicCurve.IsCurveOver.instFreeKaehler",
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
    "AlgebraicCurve.IsCurveOver.one_le_trdeg",
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
    "AlgebraicCurve.IsCurveOver.trdeg_le_one",
    "AlgebraicCurve.KaehlerRankOne",
    "AlgebraicCurve.LSpace",
    "AlgebraicCurve.Pic",
    "AlgebraicCurve.Pic0",
    "AlgebraicCurve.Place",
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK",
    "AlgebraicCurve.Place.DCoordGenerates",
    "AlgebraicCurve.Place.FiniteResidue",
    "AlgebraicCurve.Place.LocalResidueData.res",
    "AlgebraicCurve.Place.ResidueField",
    "AlgebraicCurve.Place.adicValuation",
    "AlgebraicCurve.Place.dCoord",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
    "AlgebraicCurve.Place.dCoord_ne_zero",
    "AlgebraicCurve.Place.deg",
    "AlgebraicCurve.Place.differentialCoeff",
    "AlgebraicCurve.Place.differentialCoeff_dCoord",
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord",
    "AlgebraicCurve.Place.differentialCoeff_unique",
    "AlgebraicCurve.Place.differentialCoeff_zero",
    "AlgebraicCurve.Place.exists_eq_smul_dCoord",
    "AlgebraicCurve.Place.exists_unit_mul_zpow",
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord",
    "AlgebraicCurve.Place.heightOneSpectrum",
    "AlgebraicCurve.Place.mem_iff_ord_nonneg",
    "AlgebraicCurve.Place.min_ord_le_ord_add",
    "AlgebraicCurve.Place.ord",
    "AlgebraicCurve.Place.ordDifferential",
    "AlgebraicCurve.Place.ordDifferential_smul",
    "AlgebraicCurve.Place.ord_algebraMap",
    "AlgebraicCurve.Place.ord_coe_unit",
    "AlgebraicCurve.Place.ord_inv",
    "AlgebraicCurve.Place.ord_mul",
    "AlgebraicCurve.Place.ord_uniformizer",
    "AlgebraicCurve.Place.ord_uniformizerSubring",
    "AlgebraicCurve.Place.ord_zero",
    "AlgebraicCurve.Place.ord_zpow",
    "AlgebraicCurve.Place.uniformizer",
    "AlgebraicCurve.Place.uniformizerSubring",
    "AlgebraicCurve.Place.uniformizer_ne_zero",
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
    "AlgebraicCurve.ResiduePairingSurjective",
    "AlgebraicCurve.ResidueTheoremK",
    "AlgebraicCurve.RiemannGenusBounded",
    "AlgebraicCurve.RiemannGenusReached",
    "AlgebraicCurve.RiemannGenusReachedAt",
    "AlgebraicCurve.RiemannIndexFormula",
    "AlgebraicCurve.RiemannInequality",
    "AlgebraicCurve.StichtenothGenusExists",
    "AlgebraicCurve.ValSubringKaehlerFinite",
    "AlgebraicCurve.ValSubringKaehlerSpanTop",
    "AlgebraicCurve.WeilDifferentialRankOne",
    "AlgebraicCurve.WeilDuality",
    "AlgebraicCurve.WeilDualityAdelic",
    "AlgebraicCurve.WeilOmegaEllAgrees",
    "AlgebraicCurve.adeleBdd",
    "AlgebraicCurve.adeleBddPrincipal",
    "AlgebraicCurve.adeleSingle",
    "AlgebraicCurve.adeleSpace",
    "AlgebraicCurve.canonicalClass",
    "AlgebraicCurve.canonicalDivisorOf",
    "AlgebraicCurve.canonicalDivisorOf_apply",
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one",
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed",
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula",
    "AlgebraicCurve.diagonalHom",
    "AlgebraicCurve.diagonal_mem_adeleSpace",
    "AlgebraicCurve.ell",
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty",
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase",
    "AlgebraicCurve.exists_weilCanonical_riemannRoch",
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'",
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental",
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality",
    "AlgebraicCurve.genus",
    "AlgebraicCurve.genusFF",
    "AlgebraicCurve.genus_eq_degree_div",
    "AlgebraicCurve.genus_eq_genusFF",
    "AlgebraicCurve.globalSub",
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
    "AlgebraicCurve.indexOfSpecialty",
    "AlgebraicCurve.indexOfSpecialty_eq",
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1",
    "AlgebraicCurve.kaehlerAdjoinBasis",
    "AlgebraicCurve.kaehlerRankOne_of_transcendental",
    "AlgebraicCurve.kaehlerRankOne_ratFunc",
    "AlgebraicCurve.lSpace_mono",
    "AlgebraicCurve.map_diagonal_lSpace",
    "AlgebraicCurve.mem_adeleSpace_iff",
    "AlgebraicCurve.mem_lSpace_iff",
    "AlgebraicCurve.mem_lSpace_iff_ord",
    "AlgebraicCurve.omegaSpace",
    "AlgebraicCurve.omegaSpaceEquivIndexDual",
    "AlgebraicCurve.one_mem_lSpace_zero",
    "AlgebraicCurve.principalRepartitions",
    "AlgebraicCurve.repartitions",
    "AlgebraicCurve.repartitionsOf",
    "AlgebraicCurve.residuePairing",
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula",
    "AlgebraicCurve.residuePairing_injective",
    "AlgebraicCurve.residuePairing_surjective",
    "AlgebraicCurve.riemannIndexFormula_of_genusReached",
    "AlgebraicCurve.riemannRochSpace",
    "AlgebraicCurve.stichtenothGenus_nonneg",
    "AlgebraicCurve.weilDifferentialModule",
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic",
    "AlgebraicCurve.weilOfKaehlerK",
    "AlgebraicCurve.weilSmul",
    "AlgebraicIndependent",
    "AlgebraicIndependent.aevalEquiv",
    "Bot",
    "Bot.bot",
    "Cardinal",
    "Cardinal.mk",
    "Classical.choose",
    "Classical.decEq",
    "Classical.indefiniteDescription",
    "Classical.propDecidable",
    "CommRing",
    "CommSemiring",
    "Derivation",
    "Derivation.leibniz",
    "Derivation.leibniz_pow",
    "Derivation.liftKaehlerDifferential",
    "Derivation.liftKaehlerDifferential_comp",
    "Derivation.liftKaehlerDifferential_comp_D",
    "Derivation.llcomp",
    "Derivation.map_algebraMap",
    "Derivation.tensorProductTo",
    "DivisionRing",
    "Dvd.dvd",
    "Equiv",
    "Equiv.punitProd",
    "Equiv.trans",
    "Even",
    "Exists.choose",
    "ExistsUnique",
    "FLTForHuman.Elliptic.EvenRec",
    "FLTForHuman.Elliptic.HaveSameParity₄",
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf",
    "FLTForHuman.Elliptic.OddRec",
    "FLTForHuman.Elliptic.Param",
    "FLTForHuman.Elliptic.Rel₃",
    "FLTForHuman.Elliptic.Rel₄OfValid",
    "FLTForHuman.Elliptic.StrictAnti₄",
    "FLTForHuman.Elliptic.addMulSub",
    "FLTForHuman.Elliptic.avg₄",
    "FLTForHuman.Elliptic.card_nTorsion",
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime",
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
    "FLTForHuman.Elliptic.card_nTorsion_one",
    "FLTForHuman.Elliptic.card_nTorsion_prime",
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow",
    "FLTForHuman.Elliptic.card_nTorsion_two",
    "FLTForHuman.Elliptic.card_smul_fiber",
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
    "FLTForHuman.Elliptic.complEDSAux",
    "FLTForHuman.Elliptic.evalEval_φ",
    "FLTForHuman.Elliptic.evalEval_ψ_sq",
    "FLTForHuman.Elliptic.exists_double_fiber_card",
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber",
    "FLTForHuman.Elliptic.invar",
    "FLTForHuman.Elliptic.invarDenom",
    "FLTForHuman.Elliptic.invarNum",
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
    "FLTForHuman.Elliptic.invar_normEDS",
    "FLTForHuman.Elliptic.invar_of_net",
    "FLTForHuman.Elliptic.invar₂_normEDS",
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq",
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ",
    "FLTForHuman.Elliptic.isEllipticSequence_ext",
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec",
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff",
    "FLTForHuman.Elliptic.net",
    "FLTForHuman.Elliptic.net_normEDS",
    "FLTForHuman.Elliptic.net_of_isEllipticSequence",
    "FLTForHuman.Elliptic.net_zero_iff_rel₃",
    "FLTForHuman.Elliptic.normEDS_eq_aeval",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
    "FLTForHuman.Elliptic.normEDS_two_three_two",
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
    "FLTForHuman.Elliptic.redInvarDenom",
    "FLTForHuman.Elliptic.redInvarNum",
    "FLTForHuman.Elliptic.redInvar_normEDS",
    "FLTForHuman.Elliptic.rel₃_iff_evenRec",
    "FLTForHuman.Elliptic.rel₃_iff_oddRec",
    "FLTForHuman.Elliptic.rel₃_iff₄",
    "FLTForHuman.Elliptic.rel₄",
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
    "FLTForHuman.Elliptic.smul_formula_or_zero",
    "FLTForHuman.Elliptic.smul_surjective",
    "FLTForHuman.Elliptic.smul_x_eq",
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval",
    "FLTForHuman.Elliptic.two_mul_ωe",
    "FLTForHuman.Elliptic.universalNormEDS",
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors",
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero",
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero",
    "FLTForHuman.Elliptic.ψc",
    "FLTForHuman.Elliptic.ψc_spec",
    "FLTForHuman.Elliptic.ωe",
    "FLTForHuman.Elliptic.ωe_spec",
    "Fact",
    "Field",
    "Finite",
    "FiniteDimensional",
    "Finset",
    "Finset.card",
    "Finset.sum",
    "Finsupp",
    "Finsupp.liftAddHom",
    "Finsupp.module",
    "Finsupp.single",
    "Finsupp.support",
    "FreeAddMonoid",
    "FunLike",
    "Function.Injective",
    "Function.Odd",
    "Function.RightInverse",
    "Function.Surjective",
    "Function.algebra",
    "Function.comp",
    "GE.ge",
    "HMod.hMod",
    "HSMul.hSMul",
    "HasQuotient.Quotient",
    "Ideal",
    "Ideal.Cotangent",
    "Ideal.Cotangent.smul_eq_zero_of_mem",
    "Ideal.IsTwoSided",
    "Ideal.Quotient.mk",
    "Ideal.comap",
    "Ideal.map_toCotangent_ker",
    "Ideal.mk_ker",
    "Ideal.mul_mem_left",
    "Ideal.mul_mem_mul",
    "Ideal.span",
    "Ideal.toCotangent",
    "Ideal.toCotangent_eq",
    "Infinite",
    "Int",
    "Int.cast",
    "Int.decLt",
    "Int.inductionOn'",
    "Int.natAbs",
    "Int.negOnePow",
    "Int.sign",
    "Int.strongRec",
    "Int.tdiv",
    "IntermediateField",
    "IntermediateField.adjoin",
    "IntermediateField.algebra'",
    "Inv.inv",
    "InvImage",
    "Irreducible",
    "Irreducible.maximalIdeal_eq",
    "IsAlgClosed",
    "IsCoprime",
    "IsDedekindDomain",
    "IsDedekindDomain.HeightOneSpectrum",
    "IsDedekindDomain.HeightOneSpectrum.asIdeal",
    "IsDedekindDomain.HeightOneSpectrum.intValuation",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
    "IsDedekindDomain.HeightOneSpectrum.valuation",
    "IsDiscreteValuationRing",
    "IsDiscreteValuationRing.exists_irreducible",
    "IsDiscreteValuationRing.irreducible_iff_uniformizer",
    "IsDiscreteValuationRing.maximalIdeal",
    "IsDomain",
    "IsDvdSequence",
    "IsEllipticDvdSequence",
    "IsEllipticNet",
    "IsEllipticNet.atom",
    "IsEllipticNet.atomRel",
    "IsEllipticNet.atomRel_eq",
    "IsEllipticNet.rel",
    "IsEllipticNet.rel_eq",
    "IsEllipticSequence",
    "IsFractionRing.algEquivOfAlgEquiv",
    "IsLocalRing.ResidueField",
    "IsLocalRing.ResidueField.algebra",
    "IsLocalRing.ResidueField.field",
    "IsLocalRing.maximalIdeal",
    "IsLocalization",
    "IsScalarTower",
    "IsScalarTower.algebraMap_smul",
    "IsScalarTower.left",
    "IsScalarTower.right",
    "IsScalarTower.to_smulCommClass",
    "IsSeparable",
    "IsUnit",
    "KaehlerDifferential",
    "KaehlerDifferential.D",
    "KaehlerDifferential.DLinearMap",
    "KaehlerDifferential.D_apply",
    "KaehlerDifferential.D_ne_zero_of_transcendental",
    "KaehlerDifferential.ideal",
    "KaehlerDifferential.isScalarTower_of_tower",
    "KaehlerDifferential.linearMapEquivDerivation",
    "KaehlerDifferential.mapBaseChange",
    "KaehlerDifferential.mvPolynomialBasis",
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal",
    "KaehlerDifferential.polynomialEquiv",
    "KaehlerDifferential.polynomialEquiv_D",
    "KaehlerDifferential.polynomialEquiv_symm",
    "KaehlerDifferential.polynomial_D_apply",
    "KaehlerDifferential.span_D_eq_top_of_transcendental",
    "KaehlerDifferential.span_range_eq_ideal",
    "KaehlerDifferential.subsingleton_of_surjective",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
    "KaehlerDifferential.tensorProductTo_surjective",
    "LinearEquiv",
    "LinearEquiv.ofBijective",
    "LinearEquiv.symm",
    "LinearEquiv.trans",
    "LinearIndependent",
    "LinearIndependent.finrank_eq_zero_of_infinite",
    "LinearMap",
    "LinearMap.addCommMonoid",
    "LinearMap.comp",
    "LinearMap.flip",
    "LinearMap.ker",
    "LinearMap.lsmul",
    "LinearMap.mk₂",
    "LinearMap.module",
    "LinearMap.mul",
    "LinearMap.range",
    "LinearMap.restrictScalars",
    "List.Pairwise",
    "Max.max",
    "Min.min",
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax",
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax",
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax",
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK",
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax",
    "ModularCurve.wkc_weilOfKaehlerK_single",
    "Module",
    "Module.Basis",
    "Module.Basis.baseChange",
    "Module.Basis.map",
    "Module.Basis.ne_zero",
    "Module.Basis.reindex",
    "Module.Basis.repr",
    "Module.Basis.singleton",
    "Module.Basis.span_eq",
    "Module.Basis.tensorProduct",
    "Module.Dual",
    "Module.End",
    "Module.Finite",
    "Module.Free",
    "Module.finrank",
    "Module.rank",
    "Monoid",
    "MonoidWithZeroHom",
    "MonoidWithZeroHom.funLike",
    "Mul",
    "MulAction",
    "Multiplicative",
    "Multiplicative.commMonoid",
    "Multiplicative.group",
    "Multiplicative.isOrderedCancelMonoid",
    "Multiplicative.linearOrder",
    "Multiplicative.monoid",
    "Multiplicative.mul",
    "Multiplicative.ofAdd",
    "Multiplicative.preorder",
    "MvPolynomial",
    "MvPolynomial.X",
    "MvPolynomial.aeval",
    "Nat",
    "Nat.Coprime",
    "Nat.Prime",
    "Nat.card",
    "Nat.cast",
    "Nat.recOnPosPrimePosCoprime",
    "Nat.recOnPrimePow",
    "Ne",
    "NoZeroDivisors",
    "NonUnitalNonAssocSemiring",
    "Nonempty",
    "Nontrivial",
    "Odd",
    "Option",
    "Option.map₂",
    "OreLocalization.oreSetComm",
    "PerfectField",
    "Pi.Function.module",
    "Pi.addCommGroup",
    "Pi.addCommMonoid",
    "Pi.isScalarTower",
    "Pi.nonAssocSemiring",
    "Polynomial",
    "Polynomial.C",
    "Polynomial.CC",
    "Polynomial.Separable",
    "Polynomial.X",
    "Polynomial.algEquivOfTranscendental",
    "Polynomial.algebraOfAlgebra",
    "Polynomial.degree",
    "Polynomial.derivative",
    "Polynomial.derivative'",
    "Polynomial.eval",
    "Polynomial.evalEval",
    "Polynomial.module",
    "Polynomial.monomial",
    "Polynomial.natDegree",
    "Preorder",
    "Prod",
    "QuotientAddGroup.Quotient.addCommGroup",
    "QuotientAddGroup.mk",
    "RatFunc",
    "RatFunc.X",
    "RatFunc.algEquivOfTranscendental",
    "RatFunc.algEquivOfTranscendental_X",
    "Ring",
    "RingEquiv",
    "RingHom",
    "RingHom.comp",
    "RingHom.id",
    "RingHom.ker",
    "RingHom.kerLift",
    "RingHom.mem_ker",
    "RingHom.quotientKerEquivOfRightInverse",
    "RingHom.quotientKerEquivOfSurjective",
    "RingHomClass",
    "RingHomInvPair.ids",
    "RingHomSurjective.ids",
    "SMul",
    "SMulCommClass",
    "SMulWithZero",
    "Semiring",
    "Set",
    "Set.Finite",
    "Set.ofPred",
    "Set.range",
    "Set.univ",
    "Squarefree",
    "Subalgebra",
    "Subalgebra.algebra",
    "Subalgebra.algebra'",
    "Submodule",
    "Submodule.Quotient.addCommMonoid",
    "Submodule.Quotient.mk",
    "Submodule.Quotient.module",
    "Submodule.Quotient.module'",
    "Submodule.Quotient.restrictScalarsEquiv",
    "Submodule.addCommGroup",
    "Submodule.addCommMonoid",
    "Submodule.comap",
    "Submodule.completeLattice",
    "Submodule.dualAnnihilator",
    "Submodule.dualQuotEquivDualAnnihilator",
    "Submodule.hasQuotient",
    "Submodule.idemSemiring",
    "Submodule.liftQ",
    "Submodule.map",
    "Submodule.mem_bot",
    "Submodule.mem_top",
    "Submodule.mem_torsionBy_iff",
    "Submodule.mkQ",
    "Submodule.module",
    "Submodule.module'",
    "Submodule.mul",
    "Submodule.restrictScalars",
    "Submodule.span",
    "Submodule.subtype",
    "Submodule.torsionBy",
    "Submonoid",
    "Subsingleton",
    "Subspace.dual_finrank_eq",
    "TensorProduct",
    "TensorProduct.AlgebraTensorModule.lift",
    "TensorProduct.AlgebraTensorModule.mk",
    "TensorProduct.Eqv",
    "TensorProduct.addCommGroup",
    "TensorProduct.addCommMonoid",
    "TensorProduct.homTensorHomMap",
    "TensorProduct.leftHasSMul",
    "TensorProduct.leftModule",
    "TensorProduct.map",
    "TensorProduct.map₂",
    "TensorProduct.smulCommClass_left",
    "TensorProduct.tmul",
    "Top",
    "Top.top",
    "Transcendental",
    "Transcendental.pow",
    "True",
    "Unit",
    "Units",
    "Units.val",
    "Valuation",
    "ValuationSubring",
    "WeierstrassCurve",
    "WeierstrassCurve.Affine",
    "WeierstrassCurve.Affine.CoordinateRing",
    "WeierstrassCurve.Affine.CoordinateRing.mk",
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq",
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq",
    "WeierstrassCurve.Affine.Equation",
    "WeierstrassCurve.Affine.Nonsingular",
    "WeierstrassCurve.Affine.Point",
    "WeierstrassCurve.Affine.negPolynomial",
    "WeierstrassCurve.Affine.negY",
    "WeierstrassCurve.Affine.polynomial",
    "WeierstrassCurve.Affine.polynomialX",
    "WeierstrassCurve.Affine.polynomialY",
    "WeierstrassCurve.C_Ψ₂Sq",
    "WeierstrassCurve.IsElliptic",
    "WeierstrassCurve.a₁",
    "WeierstrassCurve.a₃",
    "WeierstrassCurve.baseChange",
    "WeierstrassCurve.b₂",
    "WeierstrassCurve.b₄",
    "WeierstrassCurve.b₆",
    "WeierstrassCurve.b₈",
    "WeierstrassCurve.isElliptic_iff",
    "WeierstrassCurve.mk",
    "WeierstrassCurve.natDegree_Φ",
    "WeierstrassCurve.natDegree_ΨSq",
    "WeierstrassCurve.preΨ",
    "WeierstrassCurve.preΨ'",
    "WeierstrassCurve.preΨ_even",
    "WeierstrassCurve.preΨ_odd",
    "WeierstrassCurve.preΨ₄",
    "WeierstrassCurve.twoTorsionPolynomial",
    "WeierstrassCurve.Δ",
    "WeierstrassCurve.Φ",
    "WeierstrassCurve.Φ_neg",
    "WeierstrassCurve.Φ_three",
    "WeierstrassCurve.Ψ",
    "WeierstrassCurve.ΨSq",
    "WeierstrassCurve.ΨSq_three",
    "WeierstrassCurve.Ψ₂Sq",
    "WeierstrassCurve.Ψ₂Sq_eq",
    "WeierstrassCurve.Ψ₃",
    "WeierstrassCurve.φ",
    "WeierstrassCurve.ψ",
    "WeierstrassCurve.ψ_one",
    "WeierstrassCurve.ψ_two",
    "WeierstrassCurve.ψ_zero",
    "WeierstrassCurve.ψ₂",
    "WellFounded.Nat.fix",
    "WithBot.unbotD",
    "WithZero",
    "WithZero.exp",
    "WithZero.log",
    "WithZero.logEquiv",
    "WithZero.log_mul",
    "WithZero.map₂",
    "WithZero.one",
    "WithZero.recZeroCoe",
    "WithZero.unitsWithZeroEquiv",
    "Zero",
    "abs",
    "addConGen",
    "addOrderOf",
    "addOrderOf_dvd_of_nsmul_eq_zero",
    "complEDS",
    "complEDS'",
    "complEDS₂",
    "exists_prime_addOrderOf_dvd_card'",
    "exists_smul_eq_of_finrank_eq_one",
    "iSup",
    "id",
    "inferInstance",
    "le_trans",
    "minpoly",
    "nonZeroDivisors",
    "normEDS",
    "normEDS_dvd_normEDS_two_mul",
    "normEDS_even",
    "normEDS_four",
    "normEDS_mul_complEDS₂",
    "normEDS_neg",
    "normEDS_odd",
    "normEDS_one",
    "normEDS_three",
    "normEDS_two",
    "normEDS_zero",
    "npowRecAuto",
    "one_smul",
    "pow_two",
    "preNormEDS",
    "preNormEDS'",
    "preNormEDS_even",
    "preNormEDS_odd",
    "semigroupDvd",
    "smulCommClass_self",
    "zero_smul"
  ],
  "by_short": {"AddCommGroup":["AddCommGroup"],"AddCommMonoid":["AddCommMonoid"],"AddCommMonoidWithOne":["AddCommMonoidWithOne"],"AddEquiv":["AddEquiv"],"AddGroup":["AddGroup"],"AddMonoid":["AddMonoid"],"AddMonoidHom":["AddMonoidHom"],"AddSubgroup":["AddSubgroup"],"Affine":["WeierstrassCurve.Affine"],"AlgEquiv":["AlgEquiv"],"AlgHom":["AlgHom"],"Algebra":["Algebra"],"AlgebraicIndependent":["AlgebraicIndependent"],"Basis":["Module.Basis"],"Bot":["Bot"],"C":["Polynomial.C"],"CC":["Polynomial.CC"],"C_Ψ₂Sq":["WeierstrassCurve.C_Ψ₂Sq"],"CanonicalLocalResidueDataK":["AlgebraicCurve.Place.CanonicalLocalResidueDataK"],"Cardinal":["Cardinal"],"CommRing":["CommRing"],"CommSemiring":["CommSemiring"],"ConstantsAreBase":["AlgebraicCurve.ConstantsAreBase"],"CoordinateRing":["WeierstrassCurve.Affine.CoordinateRing"],"Coprime":["Nat.Coprime"],"Cotangent":["Ideal.Cotangent"],"D":["KaehlerDifferential.D"],"DCoordGenerates":["AlgebraicCurve.Place.DCoordGenerates"],"DLinearMap":["KaehlerDifferential.DLinearMap"],"D_apply":["KaehlerDifferential.D_apply"],"D_ne_zero_of_transcendental":["KaehlerDifferential.D_ne_zero_of_transcendental"],"Derivation":["Derivation"],"DivisionRing":["DivisionRing"],"Divisor":["AlgebraicCurve.Divisor"],"Dual":["Module.Dual"],"End":["Module.End"],"Equation":["WeierstrassCurve.Affine.Equation"],"Equiv":["Equiv"],"Eqv":["TensorProduct.Eqv"],"EssFiniteType":["Algebra.EssFiniteType"],"Even":["Even"],"EvenRec":["FLTForHuman.Elliptic.EvenRec"],"ExistsUnique":["ExistsUnique"],"Fact":["Fact"],"Field":["Field"],"Finite":["Finite","Module.Finite","Set.Finite"],"FiniteDimensional":["FiniteDimensional"],"FiniteResidue":["AlgebraicCurve.Place.FiniteResidue"],"Finset":["Finset"],"Finsupp":["Finsupp"],"FormallyEtale":["Algebra.FormallyEtale"],"Free":["Module.Free"],"FreeAddMonoid":["FreeAddMonoid"],"FunLike":["FunLike"],"FunctionFieldRiemannRoch":["AlgebraicCurve.FunctionFieldRiemannRoch"],"H1":["AlgebraicCurve.H1"],"HasCanonicalDivisor":["AlgebraicCurve.HasCanonicalDivisor"],"HasCanonicalLocalResidueKStar":["AlgebraicCurve.HasCanonicalLocalResidueKStar"],"HasLocalResidue":["AlgebraicCurve.HasLocalResidue"],"HasPrincipalDivisors":["AlgebraicCurve.HasPrincipalDivisors"],"HasSeparableResidue":["AlgebraicCurve.HasSeparableResidue"],"HasWeilCanonicalDivisor":["AlgebraicCurve.HasWeilCanonicalDivisor"],"HaveSameParity₄":["FLTForHuman.Elliptic.HaveSameParity₄"],"HeightOneSpectrum":["IsDedekindDomain.HeightOneSpectrum"],"Ideal":["Ideal"],"IndexOfSpecialtyFinite":["AlgebraicCurve.IndexOfSpecialtyFinite"],"Infinite":["Infinite"],"Injective":["Function.Injective"],"Int":["Int"],"IntermediateField":["IntermediateField"],"InvImage":["InvImage"],"Irreducible":["Irreducible"],"IsAlgClosed":["IsAlgClosed"],"IsCoprime":["IsCoprime"],"IsCurveOver":["AlgebraicCurve.IsCurveOver"],"IsDedekindDomain":["IsDedekindDomain"],"IsDiscreteValuationRing":["IsDiscreteValuationRing"],"IsDomain":["IsDomain"],"IsDvdSequence":["IsDvdSequence"],"IsElliptic":["WeierstrassCurve.IsElliptic"],"IsEllipticDvdSequence":["IsEllipticDvdSequence"],"IsEllipticNet":["IsEllipticNet"],"IsEllipticSequence":["IsEllipticSequence"],"IsIntegral":["Algebra.IsIntegral"],"IsLocalization":["IsLocalization"],"IsPrincipal":["AlgebraicCurve.Divisor.IsPrincipal"],"IsScalarTower":["IsScalarTower"],"IsSeparable":["Algebra.IsSeparable","IsSeparable"],"IsTwoSided":["Ideal.IsTwoSided"],"IsUnit":["IsUnit"],"KaehlerDifferential":["KaehlerDifferential"],"KaehlerRankOne":["AlgebraicCurve.KaehlerRankOne"],"LSpace":["AlgebraicCurve.LSpace"],"LinearEquiv":["LinearEquiv"],"LinearIndependent":["LinearIndependent"],"LinearMap":["LinearMap"],"Module":["Module"],"Monoid":["Monoid"],"MonoidWithZeroHom":["MonoidWithZeroHom"],"Mul":["Mul"],"MulAction":["MulAction"],"Multiplicative":["Multiplicative"],"MvPolynomial":["MvPolynomial"],"Nat":["Nat"],"Ne":["Ne"],"NoZeroDivisors":["NoZeroDivisors"],"NonUnitalNonAssocSemiring":["NonUnitalNonAssocSemiring"],"Nonempty":["Nonempty"],"Nonsingular":["WeierstrassCurve.Affine.Nonsingular"],"Nontrivial":["Nontrivial"],"Odd":["Function.Odd","Odd"],"OddRec":["FLTForHuman.Elliptic.OddRec"],"Option":["Option"],"Pairwise":["List.Pairwise"],"Param":["FLTForHuman.Elliptic.Param"],"PerfectField":["PerfectField"],"Pic":["AlgebraicCurve.Pic"],"Pic0":["AlgebraicCurve.Pic0"],"Place":["AlgebraicCurve.Place"],"Point":["WeierstrassCurve.Affine.Point"],"Polynomial":["Polynomial"],"Preorder":["Preorder"],"Prime":["Nat.Prime"],"Prod":["Prod"],"Quotient":["AddCon.Quotient","HasQuotient.Quotient"],"RatFunc":["RatFunc"],"Rel₃":["FLTForHuman.Elliptic.Rel₃"],"Rel₄OfValid":["FLTForHuman.Elliptic.Rel₄OfValid"],"ResidueField":["AlgebraicCurve.Place.ResidueField","IsLocalRing.ResidueField"],"ResiduePairingSurjective":["AlgebraicCurve.ResiduePairingSurjective"],"ResidueTheoremK":["AlgebraicCurve.ResidueTheoremK"],"RiemannGenusBounded":["AlgebraicCurve.RiemannGenusBounded"],"RiemannGenusReached":["AlgebraicCurve.RiemannGenusReached"],"RiemannGenusReachedAt":["AlgebraicCurve.RiemannGenusReachedAt"],"RiemannIndexFormula":["AlgebraicCurve.RiemannIndexFormula"],"RiemannInequality":["AlgebraicCurve.RiemannInequality"],"RightInverse":["Function.RightInverse"],"Ring":["Ring"],"RingEquiv":["RingEquiv"],"RingHom":["RingHom"],"RingHomClass":["RingHomClass"],"SMul":["SMul"],"SMulCommClass":["SMulCommClass"],"SMulWithZero":["SMulWithZero"],"Semiring":["Semiring"],"Separable":["Polynomial.Separable"],"Set":["Set"],"Squarefree":["Squarefree"],"StichtenothGenusExists":["AlgebraicCurve.StichtenothGenusExists"],"StrictAnti₄":["FLTForHuman.Elliptic.StrictAnti₄"],"Subalgebra":["Subalgebra"],"Submodule":["Submodule"],"Submonoid":["Submonoid"],"Subsingleton":["Subsingleton"],"Surjective":["Function.Surjective"],"TensorProduct":["TensorProduct"],"Top":["Top"],"Transcendental":["Transcendental"],"True":["True"],"Unit":["Unit"],"Units":["Units"],"ValSubringKaehlerFinite":["AlgebraicCurve.ValSubringKaehlerFinite"],"ValSubringKaehlerSpanTop":["AlgebraicCurve.ValSubringKaehlerSpanTop"],"Valuation":["Valuation"],"ValuationSubring":["ValuationSubring"],"WeierstrassCurve":["WeierstrassCurve"],"WeilDifferentialRankOne":["AlgebraicCurve.WeilDifferentialRankOne"],"WeilDuality":["AlgebraicCurve.WeilDuality"],"WeilDualityAdelic":["AlgebraicCurve.WeilDualityAdelic"],"WeilOmegaEllAgrees":["AlgebraicCurve.WeilOmegaEllAgrees"],"WithZero":["WithZero"],"X":["MvPolynomial.X","Polynomial.X","RatFunc.X"],"Zero":["Zero"],"abs":["abs"],"add":["AddMonoidHom.add"],"addCommGroup":["Pi.addCommGroup","QuotientAddGroup.Quotient.addCommGroup","Submodule.addCommGroup","TensorProduct.addCommGroup"],"addCommMonoid":["LinearMap.addCommMonoid","Pi.addCommMonoid","Submodule.Quotient.addCommMonoid","Submodule.addCommMonoid","TensorProduct.addCommMonoid"],"addConGen":["addConGen"],"addMulSub":["FLTForHuman.Elliptic.addMulSub"],"addOrderOf":["addOrderOf"],"addOrderOf_dvd_of_nsmul_eq_zero":["addOrderOf_dvd_of_nsmul_eq_zero"],"addSubgroupOf":["AddSubgroup.addSubgroupOf"],"adeleBdd":["AlgebraicCurve.adeleBdd"],"adeleBddPrincipal":["AlgebraicCurve.adeleBddPrincipal"],"adeleSingle":["AlgebraicCurve.adeleSingle"],"adeleSpace":["AlgebraicCurve.adeleSpace"],"adicValuation":["AlgebraicCurve.Place.adicValuation"],"adjoin":["Algebra.adjoin","IntermediateField.adjoin"],"aeval":["MvPolynomial.aeval"],"aevalEquiv":["AlgebraicIndependent.aevalEquiv"],"algEquivOfAlgEquiv":["IsFractionRing.algEquivOfAlgEquiv"],"algEquivOfTranscendental":["Polynomial.algEquivOfTranscendental","RatFunc.algEquivOfTranscendental"],"algEquivOfTranscendental_X":["RatFunc.algEquivOfTranscendental_X"],"algebra":["AddMonoidAlgebra.algebra","Function.algebra","IsLocalRing.ResidueField.algebra","Subalgebra.algebra"],"algebra'":["IntermediateField.algebra'","Subalgebra.algebra'"],"algebraMap":["Algebra.algebraMap"],"algebraMap_apply":["Algebra.TensorProduct.algebraMap_apply"],"algebraMap_smul":["IsScalarTower.algebraMap_smul"],"algebraOfAlgebra":["Polynomial.algebraOfAlgebra"],"asIdeal":["IsDedekindDomain.HeightOneSpectrum.asIdeal"],"atom":["IsEllipticNet.atom"],"atomRel":["IsEllipticNet.atomRel"],"atomRel_eq":["IsEllipticNet.atomRel_eq"],"avg₄":["FLTForHuman.Elliptic.avg₄"],"a₁":["WeierstrassCurve.a₁"],"a₃":["WeierstrassCurve.a₃"],"baseChange":["Module.Basis.baseChange","WeierstrassCurve.baseChange"],"bot":["Bot.bot"],"b₂":["WeierstrassCurve.b₂"],"b₄":["WeierstrassCurve.b₄"],"b₆":["WeierstrassCurve.b₆"],"b₈":["WeierstrassCurve.b₈"],"canonicalClass":["AlgebraicCurve.canonicalClass"],"canonicalDivisorOf":["AlgebraicCurve.canonicalDivisorOf"],"canonicalDivisorOf_apply":["AlgebraicCurve.canonicalDivisorOf_apply"],"card":["Finset.card","Nat.card"],"card_bot":["AddSubgroup.card_bot"],"card_nTorsion":["FLTForHuman.Elliptic.card_nTorsion"],"card_nTorsion_mul_of_coprime":["FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime"],"card_nTorsion_odd_fibers":["FLTForHuman.Elliptic.card_nTorsion_odd_fibers"],"card_nTorsion_one":["FLTForHuman.Elliptic.card_nTorsion_one"],"card_nTorsion_prime":["FLTForHuman.Elliptic.card_nTorsion_prime"],"card_nTorsion_prime_pow":["FLTForHuman.Elliptic.card_nTorsion_prime_pow"],"card_nTorsion_two":["FLTForHuman.Elliptic.card_nTorsion_two"],"card_smul_fiber":["FLTForHuman.Elliptic.card_smul_fiber"],"card_torsion_of_isAlgClosed":["FLTForHuman.Elliptic.card_torsion_of_isAlgClosed"],"cast":["Int.cast","Nat.cast"],"choose":["Classical.choose","Exists.choose"],"comap":["Ideal.comap","Submodule.comap"],"commMonoid":["Multiplicative.commMonoid"],"comp":["Function.comp","LinearMap.comp","RingHom.comp"],"complEDS":["complEDS"],"complEDS'":["complEDS'"],"complEDSAux":["FLTForHuman.Elliptic.complEDSAux"],"complEDS₂":["complEDS₂"],"completeLattice":["Submodule.completeLattice"],"constantsAreBase_of_deg_eq_one":["AlgebraicCurve.constantsAreBase_of_deg_eq_one"],"constantsAreBase_of_isAlgClosed":["AlgebraicCurve.constantsAreBase_of_isAlgClosed"],"dCoord":["AlgebraicCurve.Place.dCoord"],"dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField":["AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField"],"dCoordGenerates_of_valSubringKaehlerSpanTop":["AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop"],"dCoord_ne_zero":["AlgebraicCurve.Place.dCoord_ne_zero"],"decEq":["Classical.decEq"],"decLt":["Int.decLt"],"deg":["AlgebraicCurve.Place.deg"],"degZero":["AlgebraicCurve.Divisor.degZero"],"deg_eq_one_of_isAlgClosed":["AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed"],"degree":["AlgebraicCurve.Divisor.degree","Polynomial.degree"],"degree_add_one_sub_genus_le_ell_of_riemannIndexFormula":["AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula"],"degree_eq_sum":["AlgebraicCurve.Divisor.degree_eq_sum"],"degree_single":["AlgebraicCurve.Divisor.degree_single"],"derivative":["Polynomial.derivative"],"derivative'":["Polynomial.derivative'"],"diagonalHom":["AlgebraicCurve.diagonalHom"],"diagonal_mem_adeleSpace":["AlgebraicCurve.diagonal_mem_adeleSpace"],"differentialCoeff":["AlgebraicCurve.Place.differentialCoeff"],"differentialCoeff_dCoord":["AlgebraicCurve.Place.differentialCoeff_dCoord"],"differentialCoeff_smul_dCoord":["AlgebraicCurve.Place.differentialCoeff_smul_dCoord"],"differentialCoeff_unique":["AlgebraicCurve.Place.differentialCoeff_unique"],"differentialCoeff_zero":["AlgebraicCurve.Place.differentialCoeff_zero"],"dualAnnihilator":["Submodule.dualAnnihilator"],"dualQuotEquivDualAnnihilator":["Submodule.dualQuotEquivDualAnnihilator"],"dual_finrank_eq":["Subspace.dual_finrank_eq"],"dvd":["Dvd.dvd"],"ell":["AlgebraicCurve.ell"],"ell_canonicalDivisor_eq_genus_of_riemannRoch":["AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch"],"ell_sub_le_indexOfSpecialty":["AlgebraicCurve.ell_sub_le_indexOfSpecialty"],"ell_zero_eq_one_of_constantsAreBase":["AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase"],"eval":["Polynomial.eval"],"evalEval":["Polynomial.evalEval"],"evalEval_φ":["FLTForHuman.Elliptic.evalEval_φ"],"evalEval_ψ_sq":["FLTForHuman.Elliptic.evalEval_ψ_sq"],"exists_divisor":["AlgebraicCurve.HasCanonicalDivisor.exists_divisor"],"exists_double_fiber_card":["FLTForHuman.Elliptic.exists_double_fiber_card"],"exists_eq_smul_dCoord":["AlgebraicCurve.Place.exists_eq_smul_dCoord"],"exists_irreducible":["IsDiscreteValuationRing.exists_irreducible"],"exists_prime_addOrderOf_dvd_card'":["exists_prime_addOrderOf_dvd_card'"],"exists_separating_transcendental":["AlgebraicCurve.IsCurveOver.exists_separating_transcendental"],"exists_smul_eq_of_finrank_eq_one":["exists_smul_eq_of_finrank_eq_one"],"exists_unit_mul_zpow":["AlgebraicCurve.Place.exists_unit_mul_zpow"],"exists_weilCanonical_riemannRoch":["AlgebraicCurve.exists_weilCanonical_riemannRoch"],"exp":["WithZero.exp"],"field":["IsLocalRing.ResidueField.field"],"finite_not_squarefree_fiber":["FLTForHuman.Elliptic.finite_not_squarefree_fiber"],"finrank":["Module.finrank"],"finrank_adeleBdd_inf_global_eq_ell":["AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell"],"finrank_eq_zero_of_infinite":["LinearIndependent.finrank_eq_zero_of_infinite"],"finrank_kaehler":["AlgebraicCurve.IsCurveOver.finrank_kaehler"],"finrank_kaehler_eq_card_of_separating":["AlgebraicCurve.finrank_kaehler_eq_card_of_separating"],"finrank_kaehler_eq_card_of_separating'":["AlgebraicCurve.finrank_kaehler_eq_card_of_separating'"],"finrank_omegaSpace_eq_indexOfSpecialty":["AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty"],"fix":["WellFounded.Nat.fix"],"flip":["LinearMap.flip"],"forall_deg_eq_one_of_isAlgClosed":["AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed"],"funLike":["AlgHom.funLike","MonoidWithZeroHom.funLike"],"functionFieldRiemannRoch_of_isAlgClosed":["AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed"],"functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver":["AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver"],"functionFieldRiemannRoch_of_isAlgClosed_of_transcendental":["AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental"],"functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed":["AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed"],"functionFieldRiemannRoch_of_riemann_and_duality":["AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality"],"gate_ordDifferential_dCoord":["AlgebraicCurve.Place.gate_ordDifferential_dCoord"],"ge":["GE.ge"],"genus":["AlgebraicCurve.genus"],"genusFF":["AlgebraicCurve.genusFF"],"genus_eq_degree_div":["AlgebraicCurve.genus_eq_degree_div"],"genus_eq_genusFF":["AlgebraicCurve.genus_eq_genusFF"],"globalSub":["AlgebraicCurve.globalSub"],"group":["Multiplicative.group"],"hMod":["HMod.hMod"],"hSMul":["HSMul.hSMul"],"hasCanonicalDivisor_of_isCurveOver":["AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver"],"hasQuotient":["Submodule.hasQuotient"],"heightOneSpectrum":["AlgebraicCurve.Place.heightOneSpectrum"],"homTensorHomMap":["TensorProduct.homTensorHomMap"],"iSup":["iSup"],"id":["Algebra.id","RingHom.id","id"],"ideal":["KaehlerDifferential.ideal"],"idemSemiring":["Submodule.idemSemiring"],"ids":["RingHomInvPair.ids","RingHomSurjective.ids"],"includeLeft":["Algebra.TensorProduct.includeLeft"],"includeLeftRingHom":["Algebra.TensorProduct.includeLeftRingHom"],"includeRight":["Algebra.TensorProduct.includeRight"],"indefiniteDescription":["Classical.indefiniteDescription"],"indexOfSpecialty":["AlgebraicCurve.indexOfSpecialty"],"indexOfSpecialty_eq":["AlgebraicCurve.indexOfSpecialty_eq"],"indexOfSpecialty_eq_finrank_H1":["AlgebraicCurve.indexOfSpecialty_eq_finrank_H1"],"inductionOn'":["Int.inductionOn'"],"inferInstance":["inferInstance"],"instCommRing":["Algebra.TensorProduct.instCommRing"],"instFreeKaehler":["AlgebraicCurve.IsCurveOver.instFreeKaehler"],"instMul":["Algebra.TensorProduct.instMul"],"instNontrivialKaehler":["AlgebraicCurve.IsCurveOver.instNontrivialKaehler"],"instSemiring":["Algebra.TensorProduct.instSemiring"],"intValuation":["IsDedekindDomain.HeightOneSpectrum.intValuation"],"intValuation_le_one":["IsDedekindDomain.HeightOneSpectrum.intValuation_le_one"],"intValuation_lt_one_iff_mem":["IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem"],"inv":["Inv.inv"],"invar":["FLTForHuman.Elliptic.invar"],"invarDenom":["FLTForHuman.Elliptic.invarDenom"],"invarNum":["FLTForHuman.Elliptic.invarNum"],"invarNum_eq_redInvarNum_mul":["FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul"],"invar_normEDS":["FLTForHuman.Elliptic.invar_normEDS"],"invar_of_net":["FLTForHuman.Elliptic.invar_of_net"],"invar₂_normEDS":["FLTForHuman.Elliptic.invar₂_normEDS"],"irreducible_iff_uniformizer":["IsDiscreteValuationRing.irreducible_iff_uniformizer"],"isCoprime_Φ_ΨSq":["FLTForHuman.Elliptic.isCoprime_Φ_ΨSq"],"isCoprime_ΨSq_succ":["FLTForHuman.Elliptic.isCoprime_ΨSq_succ"],"isCurveOver_of_kaehlerRankOne":["AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne"],"isEllipticSequence_ext":["FLTForHuman.Elliptic.isEllipticSequence_ext"],"isEllipticSequence_iff_rel₃":["FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃"],"isEllipticSequence_of_oddRec_evenRec":["FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec"],"isElliptic_iff":["WeierstrassCurve.isElliptic_iff"],"isOrderedCancelMonoid":["Multiplicative.isOrderedCancelMonoid"],"isScalarTower":["Pi.isScalarTower"],"isScalarTower_of_tower":["KaehlerDifferential.isScalarTower_of_tower"],"kaehlerAdjoinBasis":["AlgebraicCurve.kaehlerAdjoinBasis"],"kaehlerRankOne_of_transcendental":["AlgebraicCurve.kaehlerRankOne_of_transcendental"],"kaehlerRankOne_ratFunc":["AlgebraicCurve.kaehlerRankOne_ratFunc"],"kaehler_free_rank_one":["AlgebraicCurve.IsCurveOver.kaehler_free_rank_one"],"ker":["AddMonoidHom.ker","LinearMap.ker","RingHom.ker"],"kerLift":["RingHom.kerLift"],"lSpace_mono":["AlgebraicCurve.lSpace_mono"],"le_trans":["le_trans"],"left":["IsScalarTower.left"],"leftAlgebra":["Algebra.TensorProduct.leftAlgebra"],"leftHasSMul":["TensorProduct.leftHasSMul"],"leftModule":["TensorProduct.leftModule"],"leibniz":["Derivation.leibniz"],"leibniz_pow":["Derivation.leibniz_pow"],"lift":["TensorProduct.AlgebraTensorModule.lift"],"liftAddHom":["Finsupp.liftAddHom"],"liftKaehlerDifferential":["Derivation.liftKaehlerDifferential"],"liftKaehlerDifferential_comp":["Derivation.liftKaehlerDifferential_comp"],"liftKaehlerDifferential_comp_D":["Derivation.liftKaehlerDifferential_comp_D"],"liftQ":["Submodule.liftQ"],"linearMap":["Algebra.linearMap"],"linearMapEquivDerivation":["KaehlerDifferential.linearMapEquivDerivation"],"linearOrder":["Multiplicative.linearOrder"],"llcomp":["Derivation.llcomp"],"lmul'":["Algebra.TensorProduct.lmul'"],"lmul''":["Algebra.TensorProduct.lmul''"],"lmul'_apply_tmul":["Algebra.TensorProduct.lmul'_apply_tmul"],"log":["WithZero.log"],"logEquiv":["WithZero.logEquiv"],"log_mul":["WithZero.log_mul"],"lsmul":["Algebra.lsmul","LinearMap.lsmul"],"map":["Module.Basis.map","Submodule.map","TensorProduct.map"],"mapBaseChange":["KaehlerDifferential.mapBaseChange"],"map_algebraMap":["Derivation.map_algebraMap"],"map_diagonal_lSpace":["AlgebraicCurve.map_diagonal_lSpace"],"map_toCotangent_ker":["Ideal.map_toCotangent_ker"],"map₂":["Option.map₂","TensorProduct.map₂","WithZero.map₂"],"max":["Max.max"],"maximalIdeal":["IsDiscreteValuationRing.maximalIdeal","IsLocalRing.maximalIdeal"],"maximalIdeal_eq":["Irreducible.maximalIdeal_eq"],"mem_adeleSpace_iff":["AlgebraicCurve.mem_adeleSpace_iff"],"mem_bot":["Submodule.mem_bot"],"mem_iff_ord_nonneg":["AlgebraicCurve.Place.mem_iff_ord_nonneg"],"mem_ker":["RingHom.mem_ker"],"mem_lSpace_iff":["AlgebraicCurve.mem_lSpace_iff"],"mem_lSpace_iff_ord":["AlgebraicCurve.mem_lSpace_iff_ord"],"mem_nTorsion_two_iff":["FLTForHuman.Elliptic.mem_nTorsion_two_iff"],"mem_top":["Submodule.mem_top"],"mem_torsionBy_iff":["Submodule.mem_torsionBy_iff"],"min":["Min.min"],"min_ord_le_ord_add":["AlgebraicCurve.Place.min_ord_le_ord_add"],"minpoly":["minpoly"],"mk":["Cardinal.mk","Ideal.Quotient.mk","QuotientAddGroup.mk","Submodule.Quotient.mk","TensorProduct.AlgebraTensorModule.mk","WeierstrassCurve.Affine.CoordinateRing.mk","WeierstrassCurve.mk"],"mkQ":["Submodule.mkQ"],"mk_ker":["Ideal.mk_ker"],"mk_Ψ_sq":["WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq"],"mk_φ":["WeierstrassCurve.Affine.CoordinateRing.mk_φ"],"mk_ψ":["WeierstrassCurve.Affine.CoordinateRing.mk_ψ"],"mk_ψ₂_sq":["WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq"],"mk₂":["LinearMap.mk₂"],"module":["Finsupp.module","LinearMap.module","Pi.Function.module","Polynomial.module","Submodule.Quotient.module","Submodule.module"],"module'":["Submodule.Quotient.module'","Submodule.module'"],"monoid":["Multiplicative.monoid"],"monomial":["Polynomial.monomial"],"mul":["Algebra.TensorProduct.mul","LinearMap.mul","Multiplicative.mul","Submodule.mul"],"mulRight":["AddMonoidHom.mulRight"],"mul_mem_left":["Ideal.mul_mem_left"],"mul_mem_mul":["Ideal.mul_mem_mul"],"mvPolynomialBasis":["KaehlerDifferential.mvPolynomialBasis"],"natAbs":["Int.natAbs"],"natDegree":["Polynomial.natDegree"],"natDegree_Φ":["WeierstrassCurve.natDegree_Φ"],"natDegree_ΨSq":["WeierstrassCurve.natDegree_ΨSq"],"ne_zero":["Module.Basis.ne_zero"],"negOnePow":["Int.negOnePow"],"negPolynomial":["WeierstrassCurve.Affine.negPolynomial"],"negY":["WeierstrassCurve.Affine.negY"],"net":["FLTForHuman.Elliptic.net"],"net_normEDS":["FLTForHuman.Elliptic.net_normEDS"],"net_of_isEllipticSequence":["FLTForHuman.Elliptic.net_of_isEllipticSequence"],"net_zero_iff_rel₃":["FLTForHuman.Elliptic.net_zero_iff_rel₃"],"nonAssocSemiring":["AddMonoidAlgebra.nonAssocSemiring","Pi.nonAssocSemiring"],"nonZeroDivisors":["nonZeroDivisors"],"normEDS":["normEDS"],"normEDS_dvd_normEDS_two_mul":["normEDS_dvd_normEDS_two_mul"],"normEDS_eq_aeval":["FLTForHuman.Elliptic.normEDS_eq_aeval"],"normEDS_even":["normEDS_even"],"normEDS_four":["normEDS_four"],"normEDS_isEllipticSequence":["FLTForHuman.Elliptic.normEDS_isEllipticSequence"],"normEDS_isEllipticSequence_of_mem_nonZeroDivisors":["FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors"],"normEDS_mul_complEDS":["FLTForHuman.Elliptic.normEDS_mul_complEDS"],"normEDS_mul_complEDS_div":["FLTForHuman.Elliptic.normEDS_mul_complEDS_div"],"normEDS_mul_complEDS₂":["normEDS_mul_complEDS₂"],"normEDS_neg":["normEDS_neg"],"normEDS_odd":["normEDS_odd"],"normEDS_one":["normEDS_one"],"normEDS_three":["normEDS_three"],"normEDS_two":["normEDS_two"],"normEDS_two_three_two":["FLTForHuman.Elliptic.normEDS_two_three_two"],"normEDS_zero":["normEDS_zero"],"npowRecAuto":["npowRecAuto"],"ofAdd":["Multiplicative.ofAdd"],"ofBijective":["LinearEquiv.ofBijective"],"ofPred":["Set.ofPred"],"of_finiteResidue_of_kaehlerRankOne":["AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne"],"of_isLocalization":["Algebra.FormallyEtale.of_isLocalization"],"of_isSeparable":["Algebra.FormallyEtale.of_isSeparable"],"of_perfectField":["AlgebraicCurve.HasSeparableResidue.of_perfectField"],"omegaSpace":["AlgebraicCurve.omegaSpace"],"omegaSpaceEquivIndexDual":["AlgebraicCurve.omegaSpaceEquivIndexDual"],"one":["WithZero.one"],"one_def":["Algebra.TensorProduct.one_def"],"one_le_trdeg":["AlgebraicCurve.IsCurveOver.one_le_trdeg"],"one_mem_lSpace_zero":["AlgebraicCurve.one_mem_lSpace_zero"],"one_smul":["one_smul"],"one_smul_sub_smul_one_mem_ideal":["KaehlerDifferential.one_smul_sub_smul_one_mem_ideal"],"ord":["AlgebraicCurve.Place.ord"],"ordDifferential":["AlgebraicCurve.Place.ordDifferential"],"ordDifferential_smul":["AlgebraicCurve.Place.ordDifferential_smul"],"ord_algebraMap":["AlgebraicCurve.Place.ord_algebraMap"],"ord_coe_unit":["AlgebraicCurve.Place.ord_coe_unit"],"ord_inv":["AlgebraicCurve.Place.ord_inv"],"ord_mul":["AlgebraicCurve.Place.ord_mul"],"ord_uniformizer":["AlgebraicCurve.Place.ord_uniformizer"],"ord_uniformizerSubring":["AlgebraicCurve.Place.ord_uniformizerSubring"],"ord_zero":["AlgebraicCurve.Place.ord_zero"],"ord_zpow":["AlgebraicCurve.Place.ord_zpow"],"oreSetComm":["OreLocalization.oreSetComm"],"polynomial":["WeierstrassCurve.Affine.polynomial"],"polynomialEquiv":["KaehlerDifferential.polynomialEquiv"],"polynomialEquiv_D":["KaehlerDifferential.polynomialEquiv_D"],"polynomialEquiv_symm":["KaehlerDifferential.polynomialEquiv_symm"],"polynomialX":["WeierstrassCurve.Affine.polynomialX"],"polynomialY":["WeierstrassCurve.Affine.polynomialY"],"polynomial_D_apply":["KaehlerDifferential.polynomial_D_apply"],"pow":["Transcendental.pow"],"pow_two":["pow_two"],"preNormEDS":["preNormEDS"],"preNormEDS'":["preNormEDS'"],"preNormEDS_even":["preNormEDS_even"],"preNormEDS_odd":["preNormEDS_odd"],"preorder":["Multiplicative.preorder"],"preΨ":["WeierstrassCurve.preΨ"],"preΨ'":["WeierstrassCurve.preΨ'"],"preΨ_even":["WeierstrassCurve.preΨ_even"],"preΨ_odd":["WeierstrassCurve.preΨ_odd"],"preΨ₄":["WeierstrassCurve.preΨ₄"],"preΨ₄_add_Ψ₂Sq_sq":["FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq"],"principal":["AlgebraicCurve.Divisor.principal"],"principalRepartitions":["AlgebraicCurve.principalRepartitions"],"propDecidable":["Classical.propDecidable"],"punitProd":["Equiv.punitProd"],"quotientKerEquivOfRightInverse":["RingHom.quotientKerEquivOfRightInverse"],"quotientKerEquivOfSurjective":["RingHom.quotientKerEquivOfSurjective"],"range":["LinearMap.range","Set.range"],"rank":["Module.rank"],"recOnPosPrimePosCoprime":["Nat.recOnPosPrimePosCoprime"],"recOnPrimePow":["Nat.recOnPrimePow"],"recZeroCoe":["WithZero.recZeroCoe"],"redInvarDenom":["FLTForHuman.Elliptic.redInvarDenom"],"redInvarNum":["FLTForHuman.Elliptic.redInvarNum"],"redInvar_normEDS":["FLTForHuman.Elliptic.redInvar_normEDS"],"reindex":["Module.Basis.reindex"],"rel":["IsEllipticNet.rel"],"rel_eq":["IsEllipticNet.rel_eq"],"rel₃_iff_evenRec":["FLTForHuman.Elliptic.rel₃_iff_evenRec"],"rel₃_iff_oddRec":["FLTForHuman.Elliptic.rel₃_iff_oddRec"],"rel₃_iff₄":["FLTForHuman.Elliptic.rel₃_iff₄"],"rel₄":["FLTForHuman.Elliptic.rel₄"],"rel₄_of_anti_oddRec_evenRec":["FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec"],"rel₄_transf":["FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf"],"repartitions":["AlgebraicCurve.repartitions"],"repartitionsOf":["AlgebraicCurve.repartitionsOf"],"repr":["Module.Basis.repr"],"res":["AlgebraicCurve.Place.LocalResidueData.res"],"residuePairing":["AlgebraicCurve.residuePairing"],"residuePairingSurjective_of_riemannIndexFormula":["AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula"],"residuePairing_injective":["AlgebraicCurve.residuePairing_injective"],"residuePairing_surjective":["AlgebraicCurve.residuePairing_surjective"],"restrictScalars":["AlgHom.restrictScalars","LinearMap.restrictScalars","Submodule.restrictScalars"],"restrictScalarsEquiv":["Submodule.Quotient.restrictScalarsEquiv"],"riemannIndexFormula_of_genusReached":["AlgebraicCurve.riemannIndexFormula_of_genusReached"],"riemannRochSpace":["AlgebraicCurve.riemannRochSpace"],"right":["IsScalarTower.right"],"semigroupDvd":["semigroupDvd"],"sign":["Int.sign"],"single":["Finsupp.single"],"singleton":["Module.Basis.singleton"],"smulCommClass_left":["TensorProduct.smulCommClass_left"],"smulCommClass_self":["smulCommClass_self"],"smul_eq_zero_of_mem":["Ideal.Cotangent.smul_eq_zero_of_mem"],"smul_eq_zero_of_ΨSq_eval_eq_zero":["FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero"],"smul_formula_or_zero":["FLTForHuman.Elliptic.smul_formula_or_zero"],"smul_surjective":["FLTForHuman.Elliptic.smul_surjective"],"smul_x_eq":["FLTForHuman.Elliptic.smul_x_eq"],"span":["Ideal.span","Submodule.span"],"span_D_eq_top_of_transcendental":["KaehlerDifferential.span_D_eq_top_of_transcendental"],"span_eq":["Module.Basis.span_eq"],"span_range_eq_ideal":["KaehlerDifferential.span_range_eq_ideal"],"stichtenothGenus_nonneg":["AlgebraicCurve.stichtenothGenus_nonneg"],"strongRec":["Int.strongRec"],"sub_negY_sq_eq_Ψ₂Sq_eval":["FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval"],"subsingleton_of_surjective":["KaehlerDifferential.subsingleton_of_surjective"],"subtype":["Submodule.subtype"],"sum":["Finset.sum"],"support":["Finsupp.support"],"symm":["LinearEquiv.symm"],"tdiv":["Int.tdiv"],"tensorKaehlerEquivOfFormallyEtale":["KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale"],"tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap":["KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap"],"tensorProduct":["Module.Basis.tensorProduct"],"tensorProductTo":["Derivation.tensorProductTo"],"tensorProductTo_surjective":["KaehlerDifferential.tensorProductTo_surjective"],"tmul":["TensorProduct.tmul"],"tmul_mul_tmul":["Algebra.TensorProduct.tmul_mul_tmul"],"toCotangent":["Ideal.toCotangent"],"toCotangent_eq":["Ideal.toCotangent_eq"],"toRingHom":["AlgHom.toRingHom"],"to_smulCommClass":["Algebra.to_smulCommClass","IsScalarTower.to_smulCommClass"],"top":["Top.top"],"torsionBy":["Submodule.torsionBy"],"trace":["Algebra.trace"],"trans":["Equiv.trans","LinearEquiv.trans"],"trdeg":["Algebra.trdeg"],"trdeg_eq_one_of_perfectField":["AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField"],"trdeg_le_one":["AlgebraicCurve.IsCurveOver.trdeg_le_one"],"twoTorsionPolynomial":["WeierstrassCurve.twoTorsionPolynomial"],"two_mul_ωe":["FLTForHuman.Elliptic.two_mul_ωe"],"unbotD":["WithBot.unbotD"],"uniformizer":["AlgebraicCurve.Place.uniformizer"],"uniformizerSubring":["AlgebraicCurve.Place.uniformizerSubring"],"uniformizer_ne_zero":["AlgebraicCurve.Place.uniformizer_ne_zero"],"unitsWithZeroEquiv":["WithZero.unitsWithZeroEquiv"],"univ":["Set.univ"],"universalNormEDS":["FLTForHuman.Elliptic.universalNormEDS"],"universalNormEDS_mem_nonZeroDivisors":["FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors"],"universalNormEDS_ne_zero":["FLTForHuman.Elliptic.universalNormEDS_ne_zero"],"val":["Units.val"],"valuation":["IsDedekindDomain.HeightOneSpectrum.valuation"],"weilDifferentialModule":["AlgebraicCurve.weilDifferentialModule"],"weilDuality_of_riemannIndex_of_adelic":["AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic"],"weilOfKaehlerK":["AlgebraicCurve.weilOfKaehlerK"],"weilSmul":["AlgebraicCurve.weilSmul"],"wkc_degree_canonicalDivisor_eq_of_weilMax":["ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax"],"wkc_ell_canonicalDivisor_eq_gamma_of_weilMax":["ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax"],"wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax":["ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax"],"wkc_functionFieldRiemannRoch_of_residueTheoremK":["ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK"],"wkc_riemannIndexFormula_of_weilMax":["ModularCurve.wkc_riemannIndexFormula_of_weilMax"],"wkc_weilOfKaehlerK_single":["ModularCurve.wkc_weilOfKaehlerK_single"],"wronskian_Φ_ΨSq_ne_zero":["FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero"],"zero_smul":["zero_smul"],"Δ":["WeierstrassCurve.Δ"],"Φ":["WeierstrassCurve.Φ"],"Φ_neg":["WeierstrassCurve.Φ_neg"],"Φ_three":["WeierstrassCurve.Φ_three"],"Ψ":["WeierstrassCurve.Ψ"],"ΨSq":["WeierstrassCurve.ΨSq"],"ΨSq_three":["WeierstrassCurve.ΨSq_three"],"Ψ₂Sq":["WeierstrassCurve.Ψ₂Sq"],"Ψ₂Sq_eq":["WeierstrassCurve.Ψ₂Sq_eq"],"Ψ₃":["WeierstrassCurve.Ψ₃"],"φ":["WeierstrassCurve.φ"],"ψ":["WeierstrassCurve.ψ"],"ψ_one":["WeierstrassCurve.ψ_one"],"ψ_two":["WeierstrassCurve.ψ_two"],"ψ_zero":["WeierstrassCurve.ψ_zero"],"ψc":["FLTForHuman.Elliptic.ψc"],"ψc_spec":["FLTForHuman.Elliptic.ψc_spec"],"ψ₂":["WeierstrassCurve.ψ₂"],"ωe":["FLTForHuman.Elliptic.ωe"],"ωe_spec":["FLTForHuman.Elliptic.ωe_spec"]},
  "aliases": {
    "AddSubgroup.card_bot": "AddSubgroup.card_bot",
    "AlgHom": "AlgHom",
    "AlgHom.toRingHom": "AlgHom.toRingHom",
    "Algebra.FormallyEtale": "Algebra.FormallyEtale",
    "Algebra.FormallyEtale.of_isLocalization": "Algebra.FormallyEtale.of_isLocalization",
    "Algebra.FormallyEtale.of_isSeparable": "Algebra.FormallyEtale.of_isSeparable",
    "Algebra.TensorProduct.algebraMap_apply": "Algebra.TensorProduct.algebraMap_apply",
    "Algebra.TensorProduct.includeLeft": "Algebra.TensorProduct.includeLeft",
    "Algebra.TensorProduct.includeRight": "Algebra.TensorProduct.includeRight",
    "Algebra.TensorProduct.instCommRing": "Algebra.TensorProduct.instCommRing",
    "Algebra.TensorProduct.instMul": "Algebra.TensorProduct.instMul",
    "Algebra.TensorProduct.instSemiring": "Algebra.TensorProduct.instSemiring",
    "Algebra.TensorProduct.leftAlgebra": "Algebra.TensorProduct.leftAlgebra",
    "Algebra.TensorProduct.lmul'": "Algebra.TensorProduct.lmul'",
    "Algebra.TensorProduct.lmul'_apply_tmul": "Algebra.TensorProduct.lmul'_apply_tmul",
    "Algebra.TensorProduct.mul": "Algebra.TensorProduct.mul",
    "Algebra.TensorProduct.one_def": "Algebra.TensorProduct.one_def",
    "Algebra.TensorProduct.tmul_mul_tmul": "Algebra.TensorProduct.tmul_mul_tmul",
    "AlgebraicCurve.ConstantsAreBase": "AlgebraicCurve.ConstantsAreBase",
    "AlgebraicCurve.Divisor": "AlgebraicCurve.Divisor",
    "AlgebraicCurve.Divisor.degZero": "AlgebraicCurve.Divisor.degZero",
    "AlgebraicCurve.Divisor.degree": "AlgebraicCurve.Divisor.degree",
    "AlgebraicCurve.Divisor.degree_eq_sum": "AlgebraicCurve.Divisor.degree_eq_sum",
    "AlgebraicCurve.Divisor.degree_single": "AlgebraicCurve.Divisor.degree_single",
    "AlgebraicCurve.Divisor.principal": "AlgebraicCurve.Divisor.principal",
    "AlgebraicCurve.FunctionFieldRiemannRoch": "AlgebraicCurve.FunctionFieldRiemannRoch",
    "AlgebraicCurve.H1": "AlgebraicCurve.H1",
    "AlgebraicCurve.HasCanonicalDivisor": "AlgebraicCurve.HasCanonicalDivisor",
    "AlgebraicCurve.HasCanonicalLocalResidueKStar": "AlgebraicCurve.HasCanonicalLocalResidueKStar",
    "AlgebraicCurve.HasPrincipalDivisors": "AlgebraicCurve.HasPrincipalDivisors",
    "AlgebraicCurve.HasSeparableResidue": "AlgebraicCurve.HasSeparableResidue",
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": "AlgebraicCurve.HasSeparableResidue.of_perfectField",
    "AlgebraicCurve.HasWeilCanonicalDivisor": "AlgebraicCurve.HasWeilCanonicalDivisor",
    "AlgebraicCurve.IndexOfSpecialtyFinite": "AlgebraicCurve.IndexOfSpecialtyFinite",
    "AlgebraicCurve.IsCurveOver": "AlgebraicCurve.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed": "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed",
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental": "AlgebraicCurve.IsCurveOver.exists_separating_transcendental",
    "AlgebraicCurve.IsCurveOver.finrank_kaehler": "AlgebraicCurve.IsCurveOver.finrank_kaehler",
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed": "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed",
    "AlgebraicCurve.IsCurveOver.instFreeKaehler": "AlgebraicCurve.IsCurveOver.instFreeKaehler",
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler": "AlgebraicCurve.IsCurveOver.instNontrivialKaehler",
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one": "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one",
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne",
    "AlgebraicCurve.IsCurveOver.one_le_trdeg": "AlgebraicCurve.IsCurveOver.one_le_trdeg",
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField": "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField",
    "AlgebraicCurve.IsCurveOver.trdeg_le_one": "AlgebraicCurve.IsCurveOver.trdeg_le_one",
    "AlgebraicCurve.KaehlerRankOne": "AlgebraicCurve.KaehlerRankOne",
    "AlgebraicCurve.LSpace": "AlgebraicCurve.LSpace",
    "AlgebraicCurve.Pic": "AlgebraicCurve.Pic",
    "AlgebraicCurve.Pic0": "AlgebraicCurve.Pic0",
    "AlgebraicCurve.Place": "AlgebraicCurve.Place",
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK": "AlgebraicCurve.Place.CanonicalLocalResidueDataK",
    "AlgebraicCurve.Place.DCoordGenerates": "AlgebraicCurve.Place.DCoordGenerates",
    "AlgebraicCurve.Place.FiniteResidue": "AlgebraicCurve.Place.FiniteResidue",
    "AlgebraicCurve.Place.ResidueField": "AlgebraicCurve.Place.ResidueField",
    "AlgebraicCurve.Place.adicValuation": "AlgebraicCurve.Place.adicValuation",
    "AlgebraicCurve.Place.dCoord": "AlgebraicCurve.Place.dCoord",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
    "AlgebraicCurve.Place.dCoord_ne_zero": "AlgebraicCurve.Place.dCoord_ne_zero",
    "AlgebraicCurve.Place.deg": "AlgebraicCurve.Place.deg",
    "AlgebraicCurve.Place.differentialCoeff": "AlgebraicCurve.Place.differentialCoeff",
    "AlgebraicCurve.Place.differentialCoeff_dCoord": "AlgebraicCurve.Place.differentialCoeff_dCoord",
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord": "AlgebraicCurve.Place.differentialCoeff_smul_dCoord",
    "AlgebraicCurve.Place.differentialCoeff_unique": "AlgebraicCurve.Place.differentialCoeff_unique",
    "AlgebraicCurve.Place.differentialCoeff_zero": "AlgebraicCurve.Place.differentialCoeff_zero",
    "AlgebraicCurve.Place.exists_eq_smul_dCoord": "AlgebraicCurve.Place.exists_eq_smul_dCoord",
    "AlgebraicCurve.Place.exists_unit_mul_zpow": "AlgebraicCurve.Place.exists_unit_mul_zpow",
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord": "AlgebraicCurve.Place.gate_ordDifferential_dCoord",
    "AlgebraicCurve.Place.heightOneSpectrum": "AlgebraicCurve.Place.heightOneSpectrum",
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": "AlgebraicCurve.Place.mem_iff_ord_nonneg",
    "AlgebraicCurve.Place.min_ord_le_ord_add": "AlgebraicCurve.Place.min_ord_le_ord_add",
    "AlgebraicCurve.Place.ord": "AlgebraicCurve.Place.ord",
    "AlgebraicCurve.Place.ordDifferential": "AlgebraicCurve.Place.ordDifferential",
    "AlgebraicCurve.Place.ordDifferential_smul": "AlgebraicCurve.Place.ordDifferential_smul",
    "AlgebraicCurve.Place.ord_algebraMap": "AlgebraicCurve.Place.ord_algebraMap",
    "AlgebraicCurve.Place.ord_coe_unit": "AlgebraicCurve.Place.ord_coe_unit",
    "AlgebraicCurve.Place.ord_inv": "AlgebraicCurve.Place.ord_inv",
    "AlgebraicCurve.Place.ord_mul": "AlgebraicCurve.Place.ord_mul",
    "AlgebraicCurve.Place.ord_uniformizer": "AlgebraicCurve.Place.ord_uniformizer",
    "AlgebraicCurve.Place.ord_uniformizerSubring": "AlgebraicCurve.Place.ord_uniformizerSubring",
    "AlgebraicCurve.Place.ord_zero": "AlgebraicCurve.Place.ord_zero",
    "AlgebraicCurve.Place.ord_zpow": "AlgebraicCurve.Place.ord_zpow",
    "AlgebraicCurve.Place.uniformizer": "AlgebraicCurve.Place.uniformizer",
    "AlgebraicCurve.Place.uniformizerSubring": "AlgebraicCurve.Place.uniformizerSubring",
    "AlgebraicCurve.Place.uniformizer_ne_zero": "AlgebraicCurve.Place.uniformizer_ne_zero",
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne",
    "AlgebraicCurve.ResiduePairingSurjective": "AlgebraicCurve.ResiduePairingSurjective",
    "AlgebraicCurve.ResidueTheoremK": "AlgebraicCurve.ResidueTheoremK",
    "AlgebraicCurve.RiemannGenusBounded": "AlgebraicCurve.RiemannGenusBounded",
    "AlgebraicCurve.RiemannGenusReached": "AlgebraicCurve.RiemannGenusReached",
    "AlgebraicCurve.RiemannGenusReachedAt": "AlgebraicCurve.RiemannGenusReachedAt",
    "AlgebraicCurve.RiemannIndexFormula": "AlgebraicCurve.RiemannIndexFormula",
    "AlgebraicCurve.RiemannInequality": "AlgebraicCurve.RiemannInequality",
    "AlgebraicCurve.StichtenothGenusExists": "AlgebraicCurve.StichtenothGenusExists",
    "AlgebraicCurve.WeilDifferentialRankOne": "AlgebraicCurve.WeilDifferentialRankOne",
    "AlgebraicCurve.WeilDuality": "AlgebraicCurve.WeilDuality",
    "AlgebraicCurve.WeilDualityAdelic": "AlgebraicCurve.WeilDualityAdelic",
    "AlgebraicCurve.WeilOmegaEllAgrees": "AlgebraicCurve.WeilOmegaEllAgrees",
    "AlgebraicCurve.adeleBdd": "AlgebraicCurve.adeleBdd",
    "AlgebraicCurve.adeleBddPrincipal": "AlgebraicCurve.adeleBddPrincipal",
    "AlgebraicCurve.adeleSpace": "AlgebraicCurve.adeleSpace",
    "AlgebraicCurve.canonicalClass": "AlgebraicCurve.canonicalClass",
    "AlgebraicCurve.canonicalDivisorOf": "AlgebraicCurve.canonicalDivisorOf",
    "AlgebraicCurve.canonicalDivisorOf_apply": "AlgebraicCurve.canonicalDivisorOf_apply",
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one": "AlgebraicCurve.constantsAreBase_of_deg_eq_one",
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed": "AlgebraicCurve.constantsAreBase_of_isAlgClosed",
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula": "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula",
    "AlgebraicCurve.diagonalHom": "AlgebraicCurve.diagonalHom",
    "AlgebraicCurve.ell": "AlgebraicCurve.ell",
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch": "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty": "AlgebraicCurve.ell_sub_le_indexOfSpecialty",
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase": "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase",
    "AlgebraicCurve.exists_weilCanonical_riemannRoch": "AlgebraicCurve.exists_weilCanonical_riemannRoch",
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell": "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'": "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'",
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty": "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental": "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental",
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed": "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality": "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality",
    "AlgebraicCurve.genus": "AlgebraicCurve.genus",
    "AlgebraicCurve.genusFF": "AlgebraicCurve.genusFF",
    "AlgebraicCurve.genus_eq_degree_div": "AlgebraicCurve.genus_eq_degree_div",
    "AlgebraicCurve.genus_eq_genusFF": "AlgebraicCurve.genus_eq_genusFF",
    "AlgebraicCurve.globalSub": "AlgebraicCurve.globalSub",
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver",
    "AlgebraicCurve.indexOfSpecialty": "AlgebraicCurve.indexOfSpecialty",
    "AlgebraicCurve.indexOfSpecialty_eq": "AlgebraicCurve.indexOfSpecialty_eq",
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1": "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1",
    "AlgebraicCurve.kaehlerAdjoinBasis": "AlgebraicCurve.kaehlerAdjoinBasis",
    "AlgebraicCurve.kaehlerRankOne_of_transcendental": "AlgebraicCurve.kaehlerRankOne_of_transcendental",
    "AlgebraicCurve.kaehlerRankOne_ratFunc": "AlgebraicCurve.kaehlerRankOne_ratFunc",
    "AlgebraicCurve.lSpace_mono": "AlgebraicCurve.lSpace_mono",
    "AlgebraicCurve.map_diagonal_lSpace": "AlgebraicCurve.map_diagonal_lSpace",
    "AlgebraicCurve.mem_adeleSpace_iff": "AlgebraicCurve.mem_adeleSpace_iff",
    "AlgebraicCurve.mem_lSpace_iff": "AlgebraicCurve.mem_lSpace_iff",
    "AlgebraicCurve.mem_lSpace_iff_ord": "AlgebraicCurve.mem_lSpace_iff_ord",
    "AlgebraicCurve.omegaSpace": "AlgebraicCurve.omegaSpace",
    "AlgebraicCurve.omegaSpaceEquivIndexDual": "AlgebraicCurve.omegaSpaceEquivIndexDual",
    "AlgebraicCurve.one_mem_lSpace_zero": "AlgebraicCurve.one_mem_lSpace_zero",
    "AlgebraicCurve.principalRepartitions": "AlgebraicCurve.principalRepartitions",
    "AlgebraicCurve.repartitions": "AlgebraicCurve.repartitions",
    "AlgebraicCurve.repartitionsOf": "AlgebraicCurve.repartitionsOf",
    "AlgebraicCurve.residuePairing": "AlgebraicCurve.residuePairing",
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula": "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula",
    "AlgebraicCurve.residuePairing_injective": "AlgebraicCurve.residuePairing_injective",
    "AlgebraicCurve.residuePairing_surjective": "AlgebraicCurve.residuePairing_surjective",
    "AlgebraicCurve.riemannIndexFormula_of_genusReached": "AlgebraicCurve.riemannIndexFormula_of_genusReached",
    "AlgebraicCurve.riemannRochSpace": "AlgebraicCurve.riemannRochSpace",
    "AlgebraicCurve.stichtenothGenus_nonneg": "AlgebraicCurve.stichtenothGenus_nonneg",
    "AlgebraicCurve.weilDifferentialModule": "AlgebraicCurve.weilDifferentialModule",
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic": "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic",
    "Bot.bot": "Bot.bot",
    "CC": "Polynomial.CC",
    "Classical.choose": "Classical.choose",
    "Classical.decEq": "Classical.decEq",
    "D": "KaehlerDifferential.D",
    "D_apply": "KaehlerDifferential.D_apply",
    "D_ne_zero_of_transcendental": "KaehlerDifferential.D_ne_zero_of_transcendental",
    "Derivation": "Derivation",
    "Derivation.leibniz": "Derivation.leibniz",
    "Derivation.leibniz_pow": "Derivation.leibniz_pow",
    "Derivation.liftKaehlerDifferential": "Derivation.liftKaehlerDifferential",
    "Derivation.liftKaehlerDifferential_comp_D": "Derivation.liftKaehlerDifferential_comp_D",
    "Derivation.map_algebraMap": "Derivation.map_algebraMap",
    "Derivation.tensorProductTo": "Derivation.tensorProductTo",
    "EvenRec": "FLTForHuman.Elliptic.EvenRec",
    "FLTForHuman.Elliptic.EvenRec": "FLTForHuman.Elliptic.EvenRec",
    "FLTForHuman.Elliptic.HaveSameParity₄": "FLTForHuman.Elliptic.HaveSameParity₄",
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf": "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf",
    "FLTForHuman.Elliptic.OddRec": "FLTForHuman.Elliptic.OddRec",
    "FLTForHuman.Elliptic.Param": "FLTForHuman.Elliptic.Param",
    "FLTForHuman.Elliptic.Rel₃": "FLTForHuman.Elliptic.Rel₃",
    "FLTForHuman.Elliptic.StrictAnti₄": "FLTForHuman.Elliptic.StrictAnti₄",
    "FLTForHuman.Elliptic.avg₄": "FLTForHuman.Elliptic.avg₄",
    "FLTForHuman.Elliptic.card_nTorsion": "FLTForHuman.Elliptic.card_nTorsion",
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime": "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime",
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers": "FLTForHuman.Elliptic.card_nTorsion_odd_fibers",
    "FLTForHuman.Elliptic.card_nTorsion_one": "FLTForHuman.Elliptic.card_nTorsion_one",
    "FLTForHuman.Elliptic.card_nTorsion_prime": "FLTForHuman.Elliptic.card_nTorsion_prime",
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow": "FLTForHuman.Elliptic.card_nTorsion_prime_pow",
    "FLTForHuman.Elliptic.card_nTorsion_two": "FLTForHuman.Elliptic.card_nTorsion_two",
    "FLTForHuman.Elliptic.card_smul_fiber": "FLTForHuman.Elliptic.card_smul_fiber",
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed": "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
    "FLTForHuman.Elliptic.complEDSAux": "FLTForHuman.Elliptic.complEDSAux",
    "FLTForHuman.Elliptic.exists_double_fiber_card": "FLTForHuman.Elliptic.exists_double_fiber_card",
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber": "FLTForHuman.Elliptic.finite_not_squarefree_fiber",
    "FLTForHuman.Elliptic.invar": "FLTForHuman.Elliptic.invar",
    "FLTForHuman.Elliptic.invarDenom": "FLTForHuman.Elliptic.invarDenom",
    "FLTForHuman.Elliptic.invarNum": "FLTForHuman.Elliptic.invarNum",
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul",
    "FLTForHuman.Elliptic.invar_normEDS": "FLTForHuman.Elliptic.invar_normEDS",
    "FLTForHuman.Elliptic.invar_of_net": "FLTForHuman.Elliptic.invar_of_net",
    "FLTForHuman.Elliptic.invar₂_normEDS": "FLTForHuman.Elliptic.invar₂_normEDS",
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq": "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq",
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ": "FLTForHuman.Elliptic.isCoprime_ΨSq_succ",
    "FLTForHuman.Elliptic.isEllipticSequence_ext": "FLTForHuman.Elliptic.isEllipticSequence_ext",
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃": "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec": "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec",
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff": "FLTForHuman.Elliptic.mem_nTorsion_two_iff",
    "FLTForHuman.Elliptic.net_normEDS": "FLTForHuman.Elliptic.net_normEDS",
    "FLTForHuman.Elliptic.net_of_isEllipticSequence": "FLTForHuman.Elliptic.net_of_isEllipticSequence",
    "FLTForHuman.Elliptic.net_zero_iff_rel₃": "FLTForHuman.Elliptic.net_zero_iff_rel₃",
    "FLTForHuman.Elliptic.normEDS_eq_aeval": "FLTForHuman.Elliptic.normEDS_eq_aeval",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence": "FLTForHuman.Elliptic.normEDS_isEllipticSequence",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors": "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": "FLTForHuman.Elliptic.normEDS_mul_complEDS",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": "FLTForHuman.Elliptic.normEDS_mul_complEDS_div",
    "FLTForHuman.Elliptic.normEDS_two_three_two": "FLTForHuman.Elliptic.normEDS_two_three_two",
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq",
    "FLTForHuman.Elliptic.redInvarDenom": "FLTForHuman.Elliptic.redInvarDenom",
    "FLTForHuman.Elliptic.redInvarNum": "FLTForHuman.Elliptic.redInvarNum",
    "FLTForHuman.Elliptic.redInvar_normEDS": "FLTForHuman.Elliptic.redInvar_normEDS",
    "FLTForHuman.Elliptic.rel₃_iff_evenRec": "FLTForHuman.Elliptic.rel₃_iff_evenRec",
    "FLTForHuman.Elliptic.rel₃_iff_oddRec": "FLTForHuman.Elliptic.rel₃_iff_oddRec",
    "FLTForHuman.Elliptic.rel₃_iff₄": "FLTForHuman.Elliptic.rel₃_iff₄",
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec": "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero": "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
    "FLTForHuman.Elliptic.smul_formula_or_zero": "FLTForHuman.Elliptic.smul_formula_or_zero",
    "FLTForHuman.Elliptic.smul_surjective": "FLTForHuman.Elliptic.smul_surjective",
    "FLTForHuman.Elliptic.smul_x_eq": "FLTForHuman.Elliptic.smul_x_eq",
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval": "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval",
    "FLTForHuman.Elliptic.two_mul_ωe": "FLTForHuman.Elliptic.two_mul_ωe",
    "FLTForHuman.Elliptic.universalNormEDS": "FLTForHuman.Elliptic.universalNormEDS",
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors": "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors",
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero": "FLTForHuman.Elliptic.universalNormEDS_ne_zero",
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero": "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero",
    "FLTForHuman.Elliptic.ψc": "FLTForHuman.Elliptic.ψc",
    "FLTForHuman.Elliptic.ψc_spec": "FLTForHuman.Elliptic.ψc_spec",
    "FLTForHuman.Elliptic.ωe": "FLTForHuman.Elliptic.ωe",
    "FLTForHuman.Elliptic.ωe_spec": "FLTForHuman.Elliptic.ωe_spec",
    "FiniteDimensional": "FiniteDimensional",
    "Finsupp": "Finsupp",
    "HaveSameParity₄": "FLTForHuman.Elliptic.HaveSameParity₄",
    "Ideal": "Ideal",
    "Ideal.Cotangent": "Ideal.Cotangent",
    "Ideal.Cotangent.smul_eq_zero_of_mem": "Ideal.Cotangent.smul_eq_zero_of_mem",
    "Ideal.Quotient.mk": "Ideal.Quotient.mk",
    "Ideal.map_toCotangent_ker": "Ideal.map_toCotangent_ker",
    "Ideal.mk_ker": "Ideal.mk_ker",
    "Ideal.mul_mem_left": "Ideal.mul_mem_left",
    "Ideal.mul_mem_mul": "Ideal.mul_mem_mul",
    "Ideal.toCotangent": "Ideal.toCotangent",
    "Ideal.toCotangent_eq": "Ideal.toCotangent_eq",
    "Int.strongRec": "Int.strongRec",
    "Irreducible": "Irreducible",
    "Irreducible.maximalIdeal_eq": "Irreducible.maximalIdeal_eq",
    "IsAlgClosed": "IsAlgClosed",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem",
    "IsDedekindDomain.HeightOneSpectrum.valuation": "IsDedekindDomain.HeightOneSpectrum.valuation",
    "IsDiscreteValuationRing.exists_irreducible": "IsDiscreteValuationRing.exists_irreducible",
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": "IsDiscreteValuationRing.irreducible_iff_uniformizer",
    "IsEllipticDvdSequence": "IsEllipticDvdSequence",
    "IsEllipticNet": "IsEllipticNet",
    "IsEllipticNet.atom": "IsEllipticNet.atom",
    "IsEllipticNet.atomRel": "IsEllipticNet.atomRel",
    "IsEllipticNet.atomRel_eq": "IsEllipticNet.atomRel_eq",
    "IsEllipticNet.rel": "IsEllipticNet.rel",
    "IsEllipticNet.rel_eq": "IsEllipticNet.rel_eq",
    "IsEllipticSequence": "IsEllipticSequence",
    "IsScalarTower.algebraMap_smul": "IsScalarTower.algebraMap_smul",
    "IsSeparable": "IsSeparable",
    "KaehlerDifferential": "KaehlerDifferential",
    "KaehlerDifferential.D": "KaehlerDifferential.D",
    "KaehlerDifferential.D_apply": "KaehlerDifferential.D_apply",
    "KaehlerDifferential.D_ne_zero_of_transcendental": "KaehlerDifferential.D_ne_zero_of_transcendental",
    "KaehlerDifferential.ideal": "KaehlerDifferential.ideal",
    "KaehlerDifferential.linearMapEquivDerivation": "KaehlerDifferential.linearMapEquivDerivation",
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal": "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal",
    "KaehlerDifferential.polynomialEquiv": "KaehlerDifferential.polynomialEquiv",
    "KaehlerDifferential.polynomialEquiv_D": "KaehlerDifferential.polynomialEquiv_D",
    "KaehlerDifferential.polynomialEquiv_symm": "KaehlerDifferential.polynomialEquiv_symm",
    "KaehlerDifferential.polynomial_D_apply": "KaehlerDifferential.polynomial_D_apply",
    "KaehlerDifferential.span_D_eq_top_of_transcendental": "KaehlerDifferential.span_D_eq_top_of_transcendental",
    "KaehlerDifferential.span_range_eq_ideal": "KaehlerDifferential.span_range_eq_ideal",
    "KaehlerDifferential.subsingleton_of_surjective": "KaehlerDifferential.subsingleton_of_surjective",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
    "KaehlerDifferential.tensorProductTo_surjective": "KaehlerDifferential.tensorProductTo_surjective",
    "LinearIndependent.finrank_eq_zero_of_infinite": "LinearIndependent.finrank_eq_zero_of_infinite",
    "LinearMap.mul": "LinearMap.mul",
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax": "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax",
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax": "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax",
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax": "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax",
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK": "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK",
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax": "ModularCurve.wkc_riemannIndexFormula_of_weilMax",
    "ModularCurve.wkc_weilOfKaehlerK_single": "ModularCurve.wkc_weilOfKaehlerK_single",
    "Module": "Module",
    "Module.Basis.baseChange": "Module.Basis.baseChange",
    "Module.Basis.map": "Module.Basis.map",
    "Module.Basis.ne_zero": "Module.Basis.ne_zero",
    "Module.Basis.span_eq": "Module.Basis.span_eq",
    "Module.finrank": "Module.finrank",
    "Multiplicative": "Multiplicative",
    "Nat.card": "Nat.card",
    "Nat.recOnPosPrimePosCoprime": "Nat.recOnPosPrimePosCoprime",
    "OddRec": "FLTForHuman.Elliptic.OddRec",
    "Polynomial.C": "Polynomial.C",
    "RatFunc.algEquivOfTranscendental": "RatFunc.algEquivOfTranscendental",
    "RatFunc.algEquivOfTranscendental_X": "RatFunc.algEquivOfTranscendental_X",
    "Rel₃": "FLTForHuman.Elliptic.Rel₃",
    "RingHom": "RingHom",
    "RingHom.ker": "RingHom.ker",
    "RingHom.mem_ker": "RingHom.mem_ker",
    "RingHom.quotientKerEquivOfRightInverse": "RingHom.quotientKerEquivOfRightInverse",
    "RingHom.quotientKerEquivOfSurjective": "RingHom.quotientKerEquivOfSurjective",
    "Set.univ": "Set.univ",
    "StrictAnti₄": "FLTForHuman.Elliptic.StrictAnti₄",
    "Submodule.mem_bot": "Submodule.mem_bot",
    "Submodule.mem_top": "Submodule.mem_top",
    "Submodule.mem_torsionBy_iff": "Submodule.mem_torsionBy_iff",
    "Subspace.dual_finrank_eq": "Subspace.dual_finrank_eq",
    "TensorProduct": "TensorProduct",
    "TensorProduct.map₂": "TensorProduct.map₂",
    "Top.top": "Top.top",
    "Transcendental.pow": "Transcendental.pow",
    "True": "True",
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq",
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": "WeierstrassCurve.Affine.CoordinateRing.mk_φ",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq",
    "WeierstrassCurve.C_Ψ₂Sq": "WeierstrassCurve.C_Ψ₂Sq",
    "WeierstrassCurve.natDegree_Φ": "WeierstrassCurve.natDegree_Φ",
    "WeierstrassCurve.natDegree_ΨSq": "WeierstrassCurve.natDegree_ΨSq",
    "WeierstrassCurve.preΨ": "WeierstrassCurve.preΨ",
    "WeierstrassCurve.preΨ'": "WeierstrassCurve.preΨ'",
    "WeierstrassCurve.preΨ_even": "WeierstrassCurve.preΨ_even",
    "WeierstrassCurve.preΨ_odd": "WeierstrassCurve.preΨ_odd",
    "WeierstrassCurve.preΨ₄": "WeierstrassCurve.preΨ₄",
    "WeierstrassCurve.Φ": "WeierstrassCurve.Φ",
    "WeierstrassCurve.Φ_neg": "WeierstrassCurve.Φ_neg",
    "WeierstrassCurve.Ψ": "WeierstrassCurve.Ψ",
    "WeierstrassCurve.ΨSq": "WeierstrassCurve.ΨSq",
    "WeierstrassCurve.Ψ₂Sq": "WeierstrassCurve.Ψ₂Sq",
    "WeierstrassCurve.Ψ₂Sq_eq": "WeierstrassCurve.Ψ₂Sq_eq",
    "WeierstrassCurve.Ψ₃": "WeierstrassCurve.Ψ₃",
    "WeierstrassCurve.φ": "WeierstrassCurve.φ",
    "WeierstrassCurve.ψ": "WeierstrassCurve.ψ",
    "WeierstrassCurve.ψ₂": "WeierstrassCurve.ψ₂",
    "WithZero": "WithZero",
    "WithZero.exp": "WithZero.exp",
    "WithZero.log": "WithZero.log",
    "WithZero.logEquiv": "WithZero.logEquiv",
    "WithZero.log_mul": "WithZero.log_mul",
    "X": "Polynomial.X",
    "addMulSub": "FLTForHuman.Elliptic.addMulSub",
    "addOrderOf_dvd_of_nsmul_eq_zero": "addOrderOf_dvd_of_nsmul_eq_zero",
    "card_torsion_of_isAlgClosed": "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed",
    "complEDS": "complEDS",
    "complEDS₂": "complEDS₂",
    "evalEval_φ": "FLTForHuman.Elliptic.evalEval_φ",
    "evalEval_ψ_sq": "FLTForHuman.Elliptic.evalEval_ψ_sq",
    "exists_prime_addOrderOf_dvd_card'": "exists_prime_addOrderOf_dvd_card'",
    "exists_smul_eq_of_finrank_eq_one": "exists_smul_eq_of_finrank_eq_one",
    "exp": "WithZero.exp",
    "id": "id",
    "invar": "FLTForHuman.Elliptic.invar",
    "invarDenom": "FLTForHuman.Elliptic.invarDenom",
    "invarNum": "FLTForHuman.Elliptic.invarNum",
    "invar_of_net": "FLTForHuman.Elliptic.invar_of_net",
    "invar₂_normEDS": "FLTForHuman.Elliptic.invar₂_normEDS",
    "isEllipticSequence_ext": "FLTForHuman.Elliptic.isEllipticSequence_ext",
    "isEllipticSequence_iff_rel₃": "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃",
    "isElliptic_iff": "WeierstrassCurve.isElliptic_iff",
    "le_trans": "le_trans",
    "linearMapEquivDerivation": "KaehlerDifferential.linearMapEquivDerivation",
    "log": "WithZero.log",
    "log_mul": "WithZero.log_mul",
    "map₂": "WithZero.map₂",
    "mk": "WeierstrassCurve.mk",
    "natDegree": "Polynomial.natDegree",
    "negY": "WeierstrassCurve.Affine.negY",
    "net": "FLTForHuman.Elliptic.net",
    "net_of_isEllipticSequence": "FLTForHuman.Elliptic.net_of_isEllipticSequence",
    "normEDS": "normEDS",
    "normEDS_dvd_normEDS_two_mul": "normEDS_dvd_normEDS_two_mul",
    "normEDS_even": "normEDS_even",
    "normEDS_four": "normEDS_four",
    "normEDS_mul_complEDS": "FLTForHuman.Elliptic.normEDS_mul_complEDS",
    "normEDS_mul_complEDS₂": "normEDS_mul_complEDS₂",
    "normEDS_neg": "normEDS_neg",
    "normEDS_odd": "normEDS_odd",
    "normEDS_one": "normEDS_one",
    "normEDS_three": "normEDS_three",
    "normEDS_two": "normEDS_two",
    "normEDS_two_three_two": "FLTForHuman.Elliptic.normEDS_two_three_two",
    "normEDS_zero": "normEDS_zero",
    "one_smul": "one_smul",
    "polynomialEquiv": "KaehlerDifferential.polynomialEquiv",
    "pow_two": "pow_two",
    "preNormEDS": "preNormEDS",
    "preNormEDS'": "preNormEDS'",
    "preNormEDS_even": "preNormEDS_even",
    "preNormEDS_odd": "preNormEDS_odd",
    "preΨ": "WeierstrassCurve.preΨ",
    "preΨ₄": "WeierstrassCurve.preΨ₄",
    "redInvar_normEDS": "FLTForHuman.Elliptic.redInvar_normEDS",
    "rel₄": "FLTForHuman.Elliptic.rel₄",
    "rel₄_of_anti_oddRec_evenRec": "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec",
    "smul_eq_zero_of_ΨSq_eval_eq_zero": "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero",
    "span_range_eq_ideal": "KaehlerDifferential.span_range_eq_ideal",
    "tensorKaehlerEquivOfFormallyEtale": "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale",
    "zero_smul": "zero_smul",
    "Φ": "WeierstrassCurve.Φ",
    "Φ_three": "WeierstrassCurve.Φ_three",
    "Ψ": "WeierstrassCurve.Ψ",
    "ΨSq": "WeierstrassCurve.ΨSq",
    "ΨSq_three": "WeierstrassCurve.ΨSq_three",
    "Ψ₂Sq": "WeierstrassCurve.Ψ₂Sq",
    "Ψ₃": "WeierstrassCurve.Ψ₃",
    "Ω": "KaehlerDifferential",
    "Ω = 0": "KaehlerDifferential",
    "Ω = I ⧸ I²": "KaehlerDifferential",
    "Ω ≅ F": "KaehlerDifferential",
    "Ω(D)": "KaehlerDifferential",
    "Ω[F⁄K]": "KaehlerDifferential",
    "Ω[F⁄K] ≅ F": "KaehlerDifferential",
    "Ω[F⁄K] ≅ F ⊗_{K(x)} Ω[K(x)⁄K] ≅ F": "KaehlerDifferential",
    "Ω[K(x)/K]": "KaehlerDifferential",
    "Ω[K(x)/K] ⊗ F": "KaehlerDifferential",
    "Ω[K(x)⁄K] = 0": "KaehlerDifferential",
    "Ω[K[X]⁄K]": "KaehlerDifferential",
    "Ω[K[X]⁄K] ≅ K[X]": "KaehlerDifferential",
    "Ω[K⁄K] = 0": "KaehlerDifferential",
    "Ω[T⁄R] ≅ T ⊗_S Ω[S⁄R]": "KaehlerDifferential",
    "Ω[ℂ(x)⁄ℂ]": "KaehlerDifferential",
    "Ω[ℂ⁄ℝ] = 0": "KaehlerDifferential",
    "φ": "WeierstrassCurve.φ",
    "ψ": "WeierstrassCurve.ψ",
    "ψ_one": "WeierstrassCurve.ψ_one",
    "ψ_two": "WeierstrassCurve.ψ_two",
    "ψ_zero": "WeierstrassCurve.ψ_zero",
    "ψc": "FLTForHuman.Elliptic.ψc",
    "ψ₂": "WeierstrassCurve.ψ₂",
    "ωe_spec": "FLTForHuman.Elliptic.ωe_spec",
    "ℤᵐ⁰": "WithZero",
    "ℤᵐ⁰ = WithZero (Multiplicative ℤ)": "WithZero"
  },
  "card_worksheets": {
    "AddCommGroup": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AddCommMonoid": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AddCommMonoidWithOne": [
      "PlacesAndDifferentials"
    ],
    "AddCon.Quotient": [
      "PlacesAndDifferentials"
    ],
    "AddEquiv": [
      "RiemannRochHierarchy"
    ],
    "AddGroup": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "AddMonoid": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "AddMonoidAlgebra.algebra": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "AddMonoidAlgebra.nonAssocSemiring": [
      "PlacesAndDifferentials"
    ],
    "AddMonoidHom": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AddMonoidHom.add": [
      "RiemannRochHierarchy"
    ],
    "AddMonoidHom.ker": [
      "RiemannRochHierarchy"
    ],
    "AddMonoidHom.mulRight": [
      "RiemannRochHierarchy"
    ],
    "AddSubgroup": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "AddSubgroup.addSubgroupOf": [
      "RiemannRochHierarchy"
    ],
    "AddSubgroup.card_bot": [
      "CardNTorsion"
    ],
    "AlgEquiv": [
      "PlacesAndDifferentials"
    ],
    "AlgHom": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "AlgHom.funLike": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "AlgHom.restrictScalars": [
      "PlacesAndDifferentials"
    ],
    "AlgHom.toRingHom": [
      "PlacesAndDifferentials"
    ],
    "Algebra": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.EssFiniteType": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.FormallyEtale": [
      "PlacesAndDifferentials"
    ],
    "Algebra.FormallyEtale.of_isLocalization": [
      "PlacesAndDifferentials"
    ],
    "Algebra.FormallyEtale.of_isSeparable": [
      "PlacesAndDifferentials"
    ],
    "Algebra.IsIntegral": [
      "RiemannRochHierarchy"
    ],
    "Algebra.IsSeparable": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.TensorProduct.algebraMap_apply": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.includeLeft": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.includeLeftRingHom": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.includeRight": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.instCommRing": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.instMul": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.instSemiring": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.leftAlgebra": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.lmul'": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.lmul''": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.lmul'_apply_tmul": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.mul": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.one_def": [
      "PlacesAndDifferentials"
    ],
    "Algebra.TensorProduct.tmul_mul_tmul": [
      "PlacesAndDifferentials"
    ],
    "Algebra.adjoin": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.algebraMap": [
      "PlacesAndDifferentials"
    ],
    "Algebra.id": [
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.linearMap": [
      "RiemannRochHierarchy"
    ],
    "Algebra.lsmul": [
      "PlacesAndDifferentials"
    ],
    "Algebra.to_smulCommClass": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Algebra.trace": [
      "RiemannRochHierarchy"
    ],
    "Algebra.trdeg": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ConstantsAreBase": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.IsPrincipal": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.degZero": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.degree": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.degree_eq_sum": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.degree_single": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Divisor.principal": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.FunctionFieldRiemannRoch": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.H1": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasCanonicalDivisor": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasCanonicalDivisor.exists_divisor": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasCanonicalLocalResidueKStar": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasLocalResidue": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasPrincipalDivisors": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasSeparableResidue": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.HasWeilCanonicalDivisor": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IndexOfSpecialtyFinite": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.IsCurveOver.finrank_kaehler": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.instFreeKaehler": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.IsCurveOver.one_le_trdeg": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.IsCurveOver.trdeg_le_one": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.KaehlerRankOne": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.LSpace": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Pic": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Pic0": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.DCoordGenerates": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.FiniteResidue": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.LocalResidueData.res": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.ResidueField": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.adicValuation": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.dCoord": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.dCoord_ne_zero": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.deg": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.differentialCoeff": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.differentialCoeff_dCoord": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.differentialCoeff_unique": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.differentialCoeff_zero": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.exists_eq_smul_dCoord": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.exists_unit_mul_zpow": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.heightOneSpectrum": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.min_ord_le_ord_add": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.ordDifferential": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.ordDifferential_smul": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_algebraMap": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_coe_unit": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_inv": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_mul": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_uniformizer": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.ord_uniformizerSubring": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_zero": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.ord_zpow": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.uniformizer": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.Place.uniformizerSubring": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.Place.uniformizer_ne_zero": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.ResiduePairingSurjective": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ResidueTheoremK": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RiemannGenusBounded": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RiemannGenusReached": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RiemannGenusReachedAt": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RiemannIndexFormula": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.RiemannInequality": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.StichtenothGenusExists": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ValSubringKaehlerFinite": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.ValSubringKaehlerSpanTop": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.WeilDifferentialRankOne": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.WeilDuality": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.WeilDualityAdelic": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.WeilOmegaEllAgrees": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.adeleBdd": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.adeleBddPrincipal": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.adeleSingle": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.adeleSpace": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.canonicalClass": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.canonicalDivisorOf": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.canonicalDivisorOf_apply": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.diagonalHom": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.diagonal_mem_adeleSpace": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.ell": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.exists_weilCanonical_riemannRoch": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.genus": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.genusFF": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.genus_eq_degree_div": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.genus_eq_genusFF": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.globalSub": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.indexOfSpecialty": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.indexOfSpecialty_eq": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.kaehlerAdjoinBasis": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.kaehlerRankOne_of_transcendental": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.kaehlerRankOne_ratFunc": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicCurve.lSpace_mono": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.map_diagonal_lSpace": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.mem_adeleSpace_iff": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.mem_lSpace_iff": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.mem_lSpace_iff_ord": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.omegaSpace": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.omegaSpaceEquivIndexDual": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.one_mem_lSpace_zero": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.principalRepartitions": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.repartitions": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.repartitionsOf": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.residuePairing": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.residuePairing_injective": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.residuePairing_surjective": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.riemannIndexFormula_of_genusReached": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.riemannRochSpace": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.stichtenothGenus_nonneg": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.weilDifferentialModule": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.weilOfKaehlerK": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "AlgebraicCurve.weilSmul": [
      "RiemannRochHierarchy"
    ],
    "AlgebraicIndependent": [
      "PlacesAndDifferentials"
    ],
    "AlgebraicIndependent.aevalEquiv": [
      "PlacesAndDifferentials"
    ],
    "Bot": [
      "CardNTorsion"
    ],
    "Bot.bot": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "Cardinal": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Cardinal.mk": [
      "CardNTorsion"
    ],
    "Classical.choose": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Classical.decEq": [
      "CardNTorsion"
    ],
    "Classical.indefiniteDescription": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Classical.propDecidable": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "CommRing": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "CommSemiring": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "Derivation": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Derivation.leibniz": [
      "PlacesAndDifferentials"
    ],
    "Derivation.leibniz_pow": [
      "PlacesAndDifferentials"
    ],
    "Derivation.liftKaehlerDifferential": [
      "PlacesAndDifferentials"
    ],
    "Derivation.liftKaehlerDifferential_comp": [
      "PlacesAndDifferentials"
    ],
    "Derivation.liftKaehlerDifferential_comp_D": [
      "PlacesAndDifferentials"
    ],
    "Derivation.llcomp": [
      "PlacesAndDifferentials"
    ],
    "Derivation.map_algebraMap": [
      "PlacesAndDifferentials"
    ],
    "Derivation.tensorProductTo": [
      "PlacesAndDifferentials"
    ],
    "DivisionRing": [
      "RiemannRochHierarchy"
    ],
    "Dvd.dvd": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Equiv": [
      "PlacesAndDifferentials"
    ],
    "Equiv.punitProd": [
      "PlacesAndDifferentials"
    ],
    "Equiv.trans": [
      "PlacesAndDifferentials"
    ],
    "Even": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Exists.choose": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "ExistsUnique": [
      "RiemannRochHierarchy"
    ],
    "FLTForHuman.Elliptic.EvenRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.HaveSameParity₄": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.OddRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.Param": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.Rel₃": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.Rel₄OfValid": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.StrictAnti₄": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.addMulSub": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.avg₄": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.card_nTorsion": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_one": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_prime": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_nTorsion_two": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_smul_fiber": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.complEDSAux": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.evalEval_φ": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.evalEval_ψ_sq": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.exists_double_fiber_card": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.invar": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invarDenom": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invarNum": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invar_normEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invar_of_net": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.invar₂_normEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.isEllipticSequence_ext": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.net": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.net_normEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.net_of_isEllipticSequence": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.net_zero_iff_rel₃": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_eq_aeval": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.normEDS_two_three_two": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.redInvarDenom": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.redInvarNum": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.redInvar_normEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.rel₃_iff_evenRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.rel₃_iff_oddRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.rel₃_iff₄": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.rel₄": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.smul_formula_or_zero": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.smul_surjective": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.smul_x_eq": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.two_mul_ωe": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.universalNormEDS": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero": [
      "CardNTorsion"
    ],
    "FLTForHuman.Elliptic.ψc": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.ψc_spec": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.ωe": [
      "DivisionPolynomials"
    ],
    "FLTForHuman.Elliptic.ωe_spec": [
      "DivisionPolynomials"
    ],
    "Fact": [
      "CardNTorsion"
    ],
    "Field": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Finite": [
      "CardNTorsion"
    ],
    "FiniteDimensional": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Finset": [
      "PlacesAndDifferentials"
    ],
    "Finset.card": [
      "PlacesAndDifferentials"
    ],
    "Finset.sum": [
      "RiemannRochHierarchy"
    ],
    "Finsupp": [
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Finsupp.liftAddHom": [
      "RiemannRochHierarchy"
    ],
    "Finsupp.module": [
      "PlacesAndDifferentials"
    ],
    "Finsupp.single": [
      "RiemannRochHierarchy"
    ],
    "Finsupp.support": [
      "RiemannRochHierarchy"
    ],
    "FreeAddMonoid": [
      "PlacesAndDifferentials"
    ],
    "FunLike": [
      "PlacesAndDifferentials"
    ],
    "Function.Injective": [
      "RiemannRochHierarchy"
    ],
    "Function.Odd": [
      "DivisionPolynomials"
    ],
    "Function.RightInverse": [
      "PlacesAndDifferentials"
    ],
    "Function.Surjective": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Function.algebra": [
      "RiemannRochHierarchy"
    ],
    "Function.comp": [
      "PlacesAndDifferentials"
    ],
    "GE.ge": [
      "DivisionPolynomials"
    ],
    "HMod.hMod": [
      "DivisionPolynomials"
    ],
    "HSMul.hSMul": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "HasQuotient.Quotient": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Ideal": [
      "PlacesAndDifferentials"
    ],
    "Ideal.Cotangent": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Ideal.Cotangent.smul_eq_zero_of_mem": [
      "PlacesAndDifferentials"
    ],
    "Ideal.IsTwoSided": [
      "PlacesAndDifferentials"
    ],
    "Ideal.Quotient.mk": [
      "PlacesAndDifferentials"
    ],
    "Ideal.comap": [
      "PlacesAndDifferentials"
    ],
    "Ideal.map_toCotangent_ker": [
      "PlacesAndDifferentials"
    ],
    "Ideal.mk_ker": [
      "PlacesAndDifferentials"
    ],
    "Ideal.mul_mem_left": [
      "PlacesAndDifferentials"
    ],
    "Ideal.mul_mem_mul": [
      "PlacesAndDifferentials"
    ],
    "Ideal.span": [
      "PlacesAndDifferentials"
    ],
    "Ideal.toCotangent": [
      "PlacesAndDifferentials"
    ],
    "Ideal.toCotangent_eq": [
      "PlacesAndDifferentials"
    ],
    "Infinite": [
      "RiemannRochHierarchy"
    ],
    "Int": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Int.cast": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Int.decLt": [
      "DivisionPolynomials"
    ],
    "Int.inductionOn'": [
      "DivisionPolynomials"
    ],
    "Int.natAbs": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Int.negOnePow": [
      "DivisionPolynomials"
    ],
    "Int.sign": [
      "DivisionPolynomials"
    ],
    "Int.strongRec": [
      "DivisionPolynomials"
    ],
    "Int.tdiv": [
      "DivisionPolynomials"
    ],
    "IntermediateField": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IntermediateField.adjoin": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IntermediateField.algebra'": [
      "PlacesAndDifferentials"
    ],
    "Inv.inv": [
      "PlacesAndDifferentials"
    ],
    "InvImage": [
      "DivisionPolynomials"
    ],
    "Irreducible": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Irreducible.maximalIdeal_eq": [
      "PlacesAndDifferentials"
    ],
    "IsAlgClosed": [
      "CardNTorsion",
      "DivisionPolynomials",
      "RiemannRochHierarchy"
    ],
    "IsCoprime": [
      "CardNTorsion"
    ],
    "IsDedekindDomain": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum.asIdeal": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum.intValuation": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": [
      "PlacesAndDifferentials"
    ],
    "IsDedekindDomain.HeightOneSpectrum.valuation": [
      "PlacesAndDifferentials"
    ],
    "IsDiscreteValuationRing": [
      "PlacesAndDifferentials"
    ],
    "IsDiscreteValuationRing.exists_irreducible": [
      "PlacesAndDifferentials"
    ],
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": [
      "PlacesAndDifferentials"
    ],
    "IsDiscreteValuationRing.maximalIdeal": [
      "PlacesAndDifferentials"
    ],
    "IsDomain": [
      "PlacesAndDifferentials"
    ],
    "IsDvdSequence": [
      "DivisionPolynomials"
    ],
    "IsEllipticDvdSequence": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet.atom": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet.atomRel": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet.atomRel_eq": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet.rel": [
      "DivisionPolynomials"
    ],
    "IsEllipticNet.rel_eq": [
      "DivisionPolynomials"
    ],
    "IsEllipticSequence": [
      "DivisionPolynomials"
    ],
    "IsFractionRing.algEquivOfAlgEquiv": [
      "PlacesAndDifferentials"
    ],
    "IsLocalRing.ResidueField": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IsLocalRing.ResidueField.algebra": [
      "RiemannRochHierarchy"
    ],
    "IsLocalRing.ResidueField.field": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IsLocalRing.maximalIdeal": [
      "PlacesAndDifferentials"
    ],
    "IsLocalization": [
      "PlacesAndDifferentials"
    ],
    "IsScalarTower": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IsScalarTower.algebraMap_smul": [
      "PlacesAndDifferentials"
    ],
    "IsScalarTower.left": [
      "PlacesAndDifferentials"
    ],
    "IsScalarTower.right": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "IsScalarTower.to_smulCommClass": [
      "PlacesAndDifferentials"
    ],
    "IsSeparable": [
      "PlacesAndDifferentials"
    ],
    "IsUnit": [
      "CardNTorsion"
    ],
    "KaehlerDifferential": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "KaehlerDifferential.D": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "KaehlerDifferential.DLinearMap": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.D_apply": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.D_ne_zero_of_transcendental": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.ideal": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "KaehlerDifferential.isScalarTower_of_tower": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.linearMapEquivDerivation": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.mapBaseChange": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.mvPolynomialBasis": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.polynomialEquiv": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.polynomialEquiv_D": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.polynomialEquiv_symm": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.polynomial_D_apply": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.span_D_eq_top_of_transcendental": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.span_range_eq_ideal": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.subsingleton_of_surjective": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap": [
      "PlacesAndDifferentials"
    ],
    "KaehlerDifferential.tensorProductTo_surjective": [
      "PlacesAndDifferentials"
    ],
    "LinearEquiv": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "LinearEquiv.ofBijective": [
      "PlacesAndDifferentials"
    ],
    "LinearEquiv.symm": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "LinearEquiv.trans": [
      "PlacesAndDifferentials"
    ],
    "LinearIndependent": [
      "RiemannRochHierarchy"
    ],
    "LinearIndependent.finrank_eq_zero_of_infinite": [
      "RiemannRochHierarchy"
    ],
    "LinearMap": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "LinearMap.addCommMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "LinearMap.comp": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.flip": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.ker": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.lsmul": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.mk₂": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.module": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "LinearMap.mul": [
      "PlacesAndDifferentials"
    ],
    "LinearMap.range": [
      "RiemannRochHierarchy"
    ],
    "LinearMap.restrictScalars": [
      "PlacesAndDifferentials"
    ],
    "List.Pairwise": [
      "DivisionPolynomials"
    ],
    "Max.max": [
      "RiemannRochHierarchy"
    ],
    "Min.min": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax": [
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax": [
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax": [
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK": [
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax": [
      "RiemannRochHierarchy"
    ],
    "ModularCurve.wkc_weilOfKaehlerK_single": [
      "RiemannRochHierarchy"
    ],
    "Module": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Module.Basis": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.baseChange": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.map": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.ne_zero": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.reindex": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.repr": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.singleton": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.span_eq": [
      "PlacesAndDifferentials"
    ],
    "Module.Basis.tensorProduct": [
      "PlacesAndDifferentials"
    ],
    "Module.Dual": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Module.End": [
      "PlacesAndDifferentials"
    ],
    "Module.Finite": [
      "RiemannRochHierarchy"
    ],
    "Module.Free": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Module.finrank": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Module.rank": [
      "RiemannRochHierarchy"
    ],
    "Monoid": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "MonoidWithZeroHom": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "MonoidWithZeroHom.funLike": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "Mul": [
      "PlacesAndDifferentials"
    ],
    "MulAction": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "Multiplicative": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Multiplicative.commMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Multiplicative.group": [
      "PlacesAndDifferentials"
    ],
    "Multiplicative.isOrderedCancelMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Multiplicative.linearOrder": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Multiplicative.monoid": [
      "PlacesAndDifferentials"
    ],
    "Multiplicative.mul": [
      "PlacesAndDifferentials"
    ],
    "Multiplicative.ofAdd": [
      "PlacesAndDifferentials"
    ],
    "Multiplicative.preorder": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "MvPolynomial": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "MvPolynomial.X": [
      "DivisionPolynomials"
    ],
    "MvPolynomial.aeval": [
      "DivisionPolynomials"
    ],
    "Nat": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Nat.Coprime": [
      "CardNTorsion"
    ],
    "Nat.Prime": [
      "CardNTorsion"
    ],
    "Nat.card": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Nat.cast": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Nat.recOnPosPrimePosCoprime": [
      "CardNTorsion"
    ],
    "Nat.recOnPrimePow": [
      "CardNTorsion"
    ],
    "Ne": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "NoZeroDivisors": [
      "CardNTorsion"
    ],
    "NonUnitalNonAssocSemiring": [
      "PlacesAndDifferentials"
    ],
    "Nonempty": [
      "RiemannRochHierarchy"
    ],
    "Nontrivial": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Odd": [
      "CardNTorsion"
    ],
    "Option": [
      "PlacesAndDifferentials"
    ],
    "Option.map₂": [
      "PlacesAndDifferentials"
    ],
    "OreLocalization.oreSetComm": [
      "RiemannRochHierarchy"
    ],
    "PerfectField": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Pi.Function.module": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Pi.addCommGroup": [
      "RiemannRochHierarchy"
    ],
    "Pi.addCommMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Pi.isScalarTower": [
      "RiemannRochHierarchy"
    ],
    "Pi.nonAssocSemiring": [
      "RiemannRochHierarchy"
    ],
    "Polynomial": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Polynomial.C": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Polynomial.CC": [
      "DivisionPolynomials"
    ],
    "Polynomial.Separable": [
      "PlacesAndDifferentials"
    ],
    "Polynomial.X": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Polynomial.algEquivOfTranscendental": [
      "PlacesAndDifferentials"
    ],
    "Polynomial.algebraOfAlgebra": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Polynomial.degree": [
      "DivisionPolynomials"
    ],
    "Polynomial.derivative": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "Polynomial.derivative'": [
      "PlacesAndDifferentials"
    ],
    "Polynomial.eval": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Polynomial.evalEval": [
      "DivisionPolynomials"
    ],
    "Polynomial.module": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Polynomial.monomial": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Polynomial.natDegree": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Preorder": [
      "RiemannRochHierarchy"
    ],
    "Prod": [
      "PlacesAndDifferentials"
    ],
    "QuotientAddGroup.Quotient.addCommGroup": [
      "RiemannRochHierarchy"
    ],
    "QuotientAddGroup.mk": [
      "RiemannRochHierarchy"
    ],
    "RatFunc": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "RatFunc.X": [
      "PlacesAndDifferentials"
    ],
    "RatFunc.algEquivOfTranscendental": [
      "PlacesAndDifferentials"
    ],
    "RatFunc.algEquivOfTranscendental_X": [
      "PlacesAndDifferentials"
    ],
    "Ring": [
      "PlacesAndDifferentials"
    ],
    "RingEquiv": [
      "PlacesAndDifferentials"
    ],
    "RingHom": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "RingHom.comp": [
      "PlacesAndDifferentials"
    ],
    "RingHom.id": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "RingHom.ker": [
      "PlacesAndDifferentials"
    ],
    "RingHom.kerLift": [
      "PlacesAndDifferentials"
    ],
    "RingHom.mem_ker": [
      "PlacesAndDifferentials"
    ],
    "RingHom.quotientKerEquivOfRightInverse": [
      "PlacesAndDifferentials"
    ],
    "RingHom.quotientKerEquivOfSurjective": [
      "PlacesAndDifferentials"
    ],
    "RingHomClass": [
      "PlacesAndDifferentials"
    ],
    "RingHomInvPair.ids": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "RingHomSurjective.ids": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "SMul": [
      "PlacesAndDifferentials"
    ],
    "SMulCommClass": [
      "PlacesAndDifferentials"
    ],
    "SMulWithZero": [
      "CardNTorsion"
    ],
    "Semiring": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Set": [
      "CardNTorsion",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Set.Finite": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "Set.ofPred": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "Set.range": [
      "PlacesAndDifferentials"
    ],
    "Set.univ": [
      "CardNTorsion"
    ],
    "Squarefree": [
      "CardNTorsion"
    ],
    "Subalgebra": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Subalgebra.algebra": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Subalgebra.algebra'": [
      "RiemannRochHierarchy"
    ],
    "Submodule": [
      "CardNTorsion",
      "DivisionPolynomials",
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.Quotient.addCommMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.Quotient.mk": [
      "PlacesAndDifferentials"
    ],
    "Submodule.Quotient.module": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.Quotient.module'": [
      "PlacesAndDifferentials"
    ],
    "Submodule.Quotient.restrictScalarsEquiv": [
      "PlacesAndDifferentials"
    ],
    "Submodule.addCommGroup": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.addCommMonoid": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.comap": [
      "RiemannRochHierarchy"
    ],
    "Submodule.completeLattice": [
      "RiemannRochHierarchy"
    ],
    "Submodule.dualAnnihilator": [
      "RiemannRochHierarchy"
    ],
    "Submodule.dualQuotEquivDualAnnihilator": [
      "RiemannRochHierarchy"
    ],
    "Submodule.hasQuotient": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.idemSemiring": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.liftQ": [
      "PlacesAndDifferentials"
    ],
    "Submodule.map": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.mem_bot": [
      "CardNTorsion"
    ],
    "Submodule.mem_top": [
      "CardNTorsion"
    ],
    "Submodule.mem_torsionBy_iff": [
      "CardNTorsion"
    ],
    "Submodule.mkQ": [
      "PlacesAndDifferentials"
    ],
    "Submodule.module": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.module'": [
      "PlacesAndDifferentials"
    ],
    "Submodule.mul": [
      "PlacesAndDifferentials"
    ],
    "Submodule.restrictScalars": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.span": [
      "PlacesAndDifferentials"
    ],
    "Submodule.subtype": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Submodule.torsionBy": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "Submonoid": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Subsingleton": [
      "PlacesAndDifferentials"
    ],
    "Subspace.dual_finrank_eq": [
      "RiemannRochHierarchy"
    ],
    "TensorProduct": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "TensorProduct.AlgebraTensorModule.lift": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.AlgebraTensorModule.mk": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.Eqv": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.addCommGroup": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.addCommMonoid": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.homTensorHomMap": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.leftHasSMul": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.leftModule": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.map": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.map₂": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.smulCommClass_left": [
      "PlacesAndDifferentials"
    ],
    "TensorProduct.tmul": [
      "PlacesAndDifferentials"
    ],
    "Top": [
      "CardNTorsion"
    ],
    "Top.top": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "Transcendental": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "Transcendental.pow": [
      "PlacesAndDifferentials"
    ],
    "True": [
      "CardNTorsion"
    ],
    "Unit": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Units": [
      "DivisionPolynomials",
      "PlacesAndDifferentials"
    ],
    "Units.val": [
      "PlacesAndDifferentials"
    ],
    "Valuation": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "ValuationSubring": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "WeierstrassCurve": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.Affine.CoordinateRing": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.CoordinateRing.mk": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.Equation": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.Nonsingular": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.Point": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.negPolynomial": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.negY": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.Affine.polynomial": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.polynomialX": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Affine.polynomialY": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.C_Ψ₂Sq": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.IsElliptic": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.a₁": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.a₃": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.baseChange": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.b₂": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.b₄": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.b₆": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.b₈": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.isElliptic_iff": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.mk": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.natDegree_Φ": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.natDegree_ΨSq": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.preΨ": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.preΨ'": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.preΨ_even": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.preΨ_odd": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.preΨ₄": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.twoTorsionPolynomial": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Δ": [
      "CardNTorsion"
    ],
    "WeierstrassCurve.Φ": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Φ_neg": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Φ_three": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Ψ": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ΨSq": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ΨSq_three": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Ψ₂Sq": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Ψ₂Sq_eq": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.Ψ₃": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.φ": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ψ": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ψ_one": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ψ_two": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ψ_zero": [
      "DivisionPolynomials"
    ],
    "WeierstrassCurve.ψ₂": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "WellFounded.Nat.fix": [
      "DivisionPolynomials"
    ],
    "WithBot.unbotD": [
      "DivisionPolynomials"
    ],
    "WithZero": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "WithZero.exp": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "WithZero.log": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "WithZero.logEquiv": [
      "PlacesAndDifferentials"
    ],
    "WithZero.log_mul": [
      "PlacesAndDifferentials"
    ],
    "WithZero.map₂": [
      "PlacesAndDifferentials"
    ],
    "WithZero.one": [
      "PlacesAndDifferentials",
      "RiemannRochHierarchy"
    ],
    "WithZero.recZeroCoe": [
      "PlacesAndDifferentials"
    ],
    "WithZero.unitsWithZeroEquiv": [
      "PlacesAndDifferentials"
    ],
    "Zero": [
      "CardNTorsion",
      "RiemannRochHierarchy"
    ],
    "abs": [
      "DivisionPolynomials"
    ],
    "addConGen": [
      "PlacesAndDifferentials"
    ],
    "addOrderOf": [
      "CardNTorsion"
    ],
    "addOrderOf_dvd_of_nsmul_eq_zero": [
      "CardNTorsion"
    ],
    "complEDS": [
      "DivisionPolynomials"
    ],
    "complEDS'": [
      "DivisionPolynomials"
    ],
    "complEDS₂": [
      "DivisionPolynomials"
    ],
    "exists_prime_addOrderOf_dvd_card'": [
      "CardNTorsion"
    ],
    "exists_smul_eq_of_finrank_eq_one": [
      "RiemannRochHierarchy"
    ],
    "iSup": [
      "RiemannRochHierarchy"
    ],
    "id": [
      "DivisionPolynomials"
    ],
    "inferInstance": [
      "CardNTorsion",
      "PlacesAndDifferentials"
    ],
    "le_trans": [
      "RiemannRochHierarchy"
    ],
    "minpoly": [
      "PlacesAndDifferentials"
    ],
    "nonZeroDivisors": [
      "DivisionPolynomials",
      "RiemannRochHierarchy"
    ],
    "normEDS": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "normEDS_dvd_normEDS_two_mul": [
      "DivisionPolynomials"
    ],
    "normEDS_even": [
      "DivisionPolynomials"
    ],
    "normEDS_four": [
      "DivisionPolynomials"
    ],
    "normEDS_mul_complEDS₂": [
      "DivisionPolynomials"
    ],
    "normEDS_neg": [
      "DivisionPolynomials"
    ],
    "normEDS_odd": [
      "DivisionPolynomials"
    ],
    "normEDS_one": [
      "DivisionPolynomials"
    ],
    "normEDS_three": [
      "DivisionPolynomials"
    ],
    "normEDS_two": [
      "DivisionPolynomials"
    ],
    "normEDS_zero": [
      "DivisionPolynomials"
    ],
    "npowRecAuto": [
      "PlacesAndDifferentials"
    ],
    "one_smul": [
      "CardNTorsion"
    ],
    "pow_two": [
      "PlacesAndDifferentials"
    ],
    "preNormEDS": [
      "CardNTorsion",
      "DivisionPolynomials"
    ],
    "preNormEDS'": [
      "DivisionPolynomials"
    ],
    "preNormEDS_even": [
      "DivisionPolynomials"
    ],
    "preNormEDS_odd": [
      "DivisionPolynomials"
    ],
    "semigroupDvd": [
      "DivisionPolynomials"
    ],
    "smulCommClass_self": [
      "PlacesAndDifferentials"
    ],
    "zero_smul": [
      "CardNTorsion"
    ]
  },
  "summaries": {
    "AddCommGroup": "inductive · Mathlib · An additive commutative group is an additive group with commutative `(+)`. ",
    "AddCommMonoid": "inductive · Mathlib · An additive commutative monoid is an additive monoid with commutative `(+)`.",
    "AddCommMonoidWithOne": "inductive · Mathlib · An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.",
    "AddCon.Quotient": "def · Mathlib · Defining the quotient by an additive congruence relation of a type with",
    "AddEquiv": "inductive · Mathlib · `AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition.",
    "AddGroup": "inductive · Mathlib · An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.",
    "AddMonoid": "inductive · Mathlib · An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`.",
    "AddMonoidAlgebra.algebra": "def · Mathlib · The instance `Algebra R R[M]` whenever we have `Algebra R R`.",
    "AddMonoidAlgebra.nonAssocSemiring": "def · Mathlib · ",
    "AddMonoidHom": "inductive · Mathlib · `M →+ N` is the type of functions `M → N` that preserve the `AddZero` structure.",
    "AddMonoidHom.add": "def · Mathlib · Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,",
    "AddMonoidHom.ker": "def · Mathlib · The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements",
    "AddMonoidHom.mulRight": "def · Mathlib · Right multiplication by an element of a (semi)ring is an `AddMonoidHom`",
    "AddSubgroup": "inductive · Mathlib · An additive subgroup of an additive group `G` is a subset containing 0, closed",
    "AddSubgroup.addSubgroupOf": "def · Mathlib · For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`.",
    "AddSubgroup.card_bot": "theorem · Mathlib · ",
    "AlgEquiv": "inductive · Mathlib · An equivalence of algebras (denoted as `A ≃ₐ[R] B`)",
    "AlgHom": "inductive · Mathlib · Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`.",
    "AlgHom.funLike": "def · Mathlib · @[macro_inline]",
    "AlgHom.restrictScalars": "def · Mathlib · R ⟶ S induces S-Alg ⥤ R-Alg",
    "AlgHom.toRingHom": "abbrev · Mathlib · Reinterpret an `AlgHom` as a `RingHom`",
    "Algebra": "inductive · Mathlib · An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.",
    "Algebra.EssFiniteType": "inductive · Mathlib · An `R`-algebra is essentially of finite type if",
    "Algebra.FormallyEtale": "inductive · Mathlib · An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.",
    "Algebra.FormallyEtale.of_isLocalization": "theorem · Mathlib · theorem of_isLocalization : FormallyEtale R Rₘ :=",
    "Algebra.FormallyEtale.of_isSeparable": "theorem · Mathlib · lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L :=",
    "Algebra.IsIntegral": "inductive · Mathlib · An algebra is integral if every element of the extension is integral over the base ring.",
    "Algebra.IsSeparable": "inductive · Mathlib · Typeclass for separable field extension: `K` is a separable field extension of `F` iff",
    "Algebra.TensorProduct.algebraMap_apply": "theorem · Mathlib · @[simp]",
    "Algebra.TensorProduct.includeLeft": "def · Mathlib · The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.",
    "Algebra.TensorProduct.includeLeftRingHom": "def · Mathlib · The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.",
    "Algebra.TensorProduct.includeRight": "def · Mathlib · The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`.",
    "Algebra.TensorProduct.instCommRing": "def · Mathlib · instance instCommRing : CommRing (A ⊗[R] B) :=",
    "Algebra.TensorProduct.instMul": "def · Mathlib · instance instMul : Mul (A ⊗[R] B) where",
    "Algebra.TensorProduct.instSemiring": "def · Mathlib · instance instSemiring : Semiring (A ⊗[R] B) where",
    "Algebra.TensorProduct.leftAlgebra": "def · Mathlib · instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=",
    "Algebra.TensorProduct.lmul'": "def · Mathlib · `LinearMap.mul'` as an `AlgHom` over the base ring.",
    "Algebra.TensorProduct.lmul''": "def · Mathlib · `LinearMap.mul'` as an `AlgHom` over the algebra.",
    "Algebra.TensorProduct.lmul'_apply_tmul": "theorem · Mathlib · @[simp]",
    "Algebra.TensorProduct.mul": "def · Mathlib · (Implementation detail)",
    "Algebra.TensorProduct.one_def": "theorem · Mathlib · theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=",
    "Algebra.TensorProduct.tmul_mul_tmul": "theorem · Mathlib · @[simp]",
    "Algebra.adjoin": "def · Mathlib · The minimal subalgebra that includes `s`.",
    "Algebra.algebraMap": "abbrev · Mathlib · Embedding `R →+* A` given by `Algebra` structure.",
    "Algebra.id": "def · Mathlib · The identity map inducing an `Algebra` structure.",
    "Algebra.linearMap": "def · Mathlib · The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `A`,",
    "Algebra.lsmul": "def · Mathlib · The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`",
    "Algebra.to_smulCommClass": "theorem · Mathlib · This has high priority because it is almost always the right instance when it applies.",
    "Algebra.trace": "def · Mathlib · The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,",
    "Algebra.trdeg": "def · Mathlib · The transcendence degree of a commutative algebra `A` over a commutative ring `R` is",
    "AlgebraicCurve.ConstantsAreBase": "def · FLTForHuman · def ConstantsAreBase (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=",
    "AlgebraicCurve.Divisor": "abbrev · FLTForHuman · abbrev Divisor : Type _ :=",
    "AlgebraicCurve.Divisor.IsPrincipal": "def · FLTForHuman · def IsPrincipal (D : Divisor K F) : Prop :=",
    "AlgebraicCurve.Divisor.degZero": "def · FLTForHuman · def degZero : AddSubgroup (Divisor K F) :=",
    "AlgebraicCurve.Divisor.degree": "def · FLTForHuman · def degree : Divisor K F →+ ℤ :=",
    "AlgebraicCurve.Divisor.degree_eq_sum": "theorem · FLTForHuman · The degree of a divisor as the finite sum `∑ v ∈ D.support, D v * deg v`.",
    "AlgebraicCurve.Divisor.degree_single": "theorem · FLTForHuman · @[simp]",
    "AlgebraicCurve.Divisor.principal": "def · FLTForHuman · def principal : AddSubgroup (Divisor K F) where",
    "AlgebraicCurve.FunctionFieldRiemannRoch": "def · FLTForHuman · def FunctionFieldRiemannRoch : Prop :=",
    "AlgebraicCurve.H1": "abbrev · FLTForHuman · abbrev H1 (D : Divisor K F) : Type _ :=",
    "AlgebraicCurve.HasCanonicalDivisor": "inductive · FLTForHuman · class HasCanonicalDivisor : Prop where",
    "AlgebraicCurve.HasCanonicalDivisor.exists_divisor": "theorem · FLTForHuman · ",
    "AlgebraicCurve.HasCanonicalLocalResidueKStar": "inductive · FLTForHuman · class HasCanonicalLocalResidueKStar where",
    "AlgebraicCurve.HasLocalResidue": "inductive · FLTForHuman · class HasLocalResidue : Prop where",
    "AlgebraicCurve.HasPrincipalDivisors": "inductive · FLTForHuman · class HasPrincipalDivisors : Prop where",
    "AlgebraicCurve.HasSeparableResidue": "inductive · FLTForHuman · class HasSeparableResidue : Prop where",
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": "theorem · FLTForHuman · instance HasSeparableResidue.of_perfectField [PerfectField K]",
    "AlgebraicCurve.HasWeilCanonicalDivisor": "def · FLTForHuman · def HasWeilCanonicalDivisor : Prop :=",
    "AlgebraicCurve.IndexOfSpecialtyFinite": "def · FLTForHuman · def IndexOfSpecialtyFinite : Prop :=",
    "AlgebraicCurve.IsCurveOver": "inductive · FLTForHuman · class IsCurveOver : Prop extends HasPrincipalDivisors K F where",
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed": "theorem · FLTForHuman · theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :",
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental": "theorem · FLTForHuman · theorem exists_separating_transcendental {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]",
    "AlgebraicCurve.IsCurveOver.finrank_kaehler": "theorem · FLTForHuman · theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=",
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed": "theorem · FLTForHuman · theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :",
    "AlgebraicCurve.IsCurveOver.instFreeKaehler": "theorem · FLTForHuman · instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=",
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler": "theorem · FLTForHuman · instance instNontrivialKaehler [IsCurveOver K F] : Nontrivial Ω[F⁄K] :=",
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one": "theorem · FLTForHuman · ",
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": "theorem · FLTForHuman · Pin row #234.",
    "AlgebraicCurve.IsCurveOver.one_le_trdeg": "theorem · FLTForHuman · theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :",
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField": "theorem · FLTForHuman · theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]",
    "AlgebraicCurve.IsCurveOver.trdeg_le_one": "theorem · FLTForHuman · theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :",
    "AlgebraicCurve.KaehlerRankOne": "def · FLTForHuman · Pin row #233.",
    "AlgebraicCurve.LSpace": "abbrev · FLTForHuman · abbrev LSpace (D : Divisor K F) : Submodule K F :=",
    "AlgebraicCurve.Pic": "abbrev · FLTForHuman · abbrev Pic : Type _ :=",
    "AlgebraicCurve.Pic0": "abbrev · FLTForHuman · abbrev Pic0 : Type _ :=",
    "AlgebraicCurve.Place": "inductive · FLTForHuman · structure Place where",
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK": "inductive · FLTForHuman · structure CanonicalLocalResidueDataK extends v.LocalResidueData where",
    "AlgebraicCurve.Place.DCoordGenerates": "inductive · FLTForHuman · class DCoordGenerates : Prop where",
    "AlgebraicCurve.Place.FiniteResidue": "inductive · FLTForHuman · class FiniteResidue : Prop where",
    "AlgebraicCurve.Place.LocalResidueData.res": "abbrev · FLTForHuman · ",
    "AlgebraicCurve.Place.ResidueField": "abbrev · FLTForHuman · abbrev ResidueField : Type _ :=",
    "AlgebraicCurve.Place.adicValuation": "def · FLTForHuman · def adicValuation : Valuation F ℤᵐ⁰ :=",
    "AlgebraicCurve.Place.dCoord": "def · FLTForHuman · def dCoord : Ω[F⁄K] :=",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": "theorem · FLTForHuman · theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": "theorem · FLTForHuman · theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop",
    "AlgebraicCurve.Place.dCoord_ne_zero": "theorem · FLTForHuman · theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 :=",
    "AlgebraicCurve.Place.deg": "def · FLTForHuman · def deg : ℕ :=",
    "AlgebraicCurve.Place.differentialCoeff": "def · FLTForHuman · def differentialCoeff (ω : Ω[F⁄K]) : F :=",
    "AlgebraicCurve.Place.differentialCoeff_dCoord": "theorem · FLTForHuman · @[simp]",
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord": "theorem · FLTForHuman · theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :",
    "AlgebraicCurve.Place.differentialCoeff_unique": "theorem · FLTForHuman · theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]",
    "AlgebraicCurve.Place.differentialCoeff_zero": "theorem · FLTForHuman · @[simp]",
    "AlgebraicCurve.Place.exists_eq_smul_dCoord": "theorem · FLTForHuman · theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :",
    "AlgebraicCurve.Place.exists_unit_mul_zpow": "theorem · FLTForHuman · theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}",
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord": "theorem · FLTForHuman · theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :",
    "AlgebraicCurve.Place.heightOneSpectrum": "def · FLTForHuman · def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=",
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": "theorem · FLTForHuman · theorem mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)",
    "AlgebraicCurve.Place.min_ord_le_ord_add": "theorem · FLTForHuman · Pin `Place.min_ord_le_ord_add`",
    "AlgebraicCurve.Place.ord": "def · FLTForHuman · def ord (f : F) : ℤ :=",
    "AlgebraicCurve.Place.ordDifferential": "def · FLTForHuman · def ordDifferential (ω : Ω[F⁄K]) : ℤ :=",
    "AlgebraicCurve.Place.ordDifferential_smul": "theorem · FLTForHuman · theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]",
    "AlgebraicCurve.Place.ord_algebraMap": "theorem · FLTForHuman · theorem ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :",
    "AlgebraicCurve.Place.ord_coe_unit": "theorem · FLTForHuman · theorem ord_coe_unit (u : v.toValuationSubringˣ) :",
    "AlgebraicCurve.Place.ord_inv": "theorem · FLTForHuman · theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f :=",
    "AlgebraicCurve.Place.ord_mul": "theorem · FLTForHuman · theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :",
    "AlgebraicCurve.Place.ord_uniformizer": "theorem · FLTForHuman · theorem ord_uniformizer : v.ord v.uniformizer = 1 :=",
    "AlgebraicCurve.Place.ord_uniformizerSubring": "theorem · FLTForHuman · theorem ord_uniformizerSubring : v.ord (uniformizerSubring v : F) = 1 :=",
    "AlgebraicCurve.Place.ord_zero": "theorem · FLTForHuman · @[simp]",
    "AlgebraicCurve.Place.ord_zpow": "theorem · FLTForHuman · theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f :=",
    "AlgebraicCurve.Place.uniformizer": "def · FLTForHuman · def uniformizer : F :=",
    "AlgebraicCurve.Place.uniformizerSubring": "def · FLTForHuman · The uniformizer as an element of the valuation subring: the single home of the",
    "AlgebraicCurve.Place.uniformizer_ne_zero": "theorem · FLTForHuman · theorem uniformizer_ne_zero : v.uniformizer ≠ 0 :=",
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": "theorem · FLTForHuman · Pin row #235.",
    "AlgebraicCurve.ResiduePairingSurjective": "def · FLTForHuman · def ResiduePairingSurjective : Prop :=",
    "AlgebraicCurve.ResidueTheoremK": "def · FLTForHuman · def ResidueTheoremK : Prop :=",
    "AlgebraicCurve.RiemannGenusBounded": "def · FLTForHuman · def RiemannGenusBounded : Prop :=",
    "AlgebraicCurve.RiemannGenusReached": "def · FLTForHuman · def RiemannGenusReached (γ : ℤ) : Prop :=",
    "AlgebraicCurve.RiemannGenusReachedAt": "inductive · FLTForHuman · structure RiemannGenusReachedAt (γ : ℤ) (D₀ : Divisor K F) : Prop where",
    "AlgebraicCurve.RiemannIndexFormula": "def · FLTForHuman · def RiemannIndexFormula : Prop :=",
    "AlgebraicCurve.RiemannInequality": "def · FLTForHuman · def RiemannInequality : Prop :=",
    "AlgebraicCurve.StichtenothGenusExists": "def · FLTForHuman · def StichtenothGenusExists : Prop :=",
    "AlgebraicCurve.ValSubringKaehlerFinite": "def · FLTForHuman · def ValSubringKaehlerFinite : Prop :=",
    "AlgebraicCurve.ValSubringKaehlerSpanTop": "def · FLTForHuman · def ValSubringKaehlerSpanTop : Prop :=",
    "AlgebraicCurve.WeilDifferentialRankOne": "def · FLTForHuman · def WeilDifferentialRankOne [HasPrincipalDivisors K F] : Prop :=",
    "AlgebraicCurve.WeilDuality": "def · FLTForHuman · def WeilDuality : Prop :=",
    "AlgebraicCurve.WeilDualityAdelic": "def · FLTForHuman · def WeilDualityAdelic : Prop :=",
    "AlgebraicCurve.WeilOmegaEllAgrees": "def · FLTForHuman · def WeilOmegaEllAgrees : Prop :=",
    "AlgebraicCurve.adeleBdd": "def · FLTForHuman · def adeleBdd (D : Divisor K F) : Submodule K (Place K F → F) where",
    "AlgebraicCurve.adeleBddPrincipal": "abbrev · FLTForHuman · abbrev adeleBddPrincipal (D : Divisor K F) : Submodule K (adeleSpace K F) :=",
    "AlgebraicCurve.adeleSingle": "def · FLTForHuman · def adeleSingle (v : Place K F) (g : F) : adeleSpace K F :=",
    "AlgebraicCurve.adeleSpace": "def · FLTForHuman · def adeleSpace : Submodule K (Place K F → F) :=",
    "AlgebraicCurve.canonicalClass": "def · FLTForHuman · def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]",
    "AlgebraicCurve.canonicalDivisorOf": "def · FLTForHuman · def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]",
    "AlgebraicCurve.canonicalDivisorOf_apply": "theorem · FLTForHuman · theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]",
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one": "theorem · FLTForHuman · The pin's `AlgebraicCurve.constantsAreBase_of_deg_eq_one` (pin 2887).",
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed": "theorem · FLTForHuman · Constants are the base field over an algebraically closed constant field (pin 5931).",
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula": "theorem · FLTForHuman · The pin's `AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula`",
    "AlgebraicCurve.diagonalHom": "def · FLTForHuman · def diagonalHom : F →ₗ[K] (Place K F → F) where",
    "AlgebraicCurve.diagonal_mem_adeleSpace": "theorem · FLTForHuman · theorem diagonal_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) :",
    "AlgebraicCurve.ell": "abbrev · FLTForHuman · abbrev ell (D : Divisor K F) : ℕ :=",
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch": "theorem · FLTForHuman · theorem AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch",
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty": "theorem · FLTForHuman · theorem ell_sub_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)",
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase": "theorem · FLTForHuman · theorem ell_zero_eq_one_of_constantsAreBase (h : ConstantsAreBase K F) :",
    "AlgebraicCurve.exists_weilCanonical_riemannRoch": "theorem · FLTForHuman · theorem exists_weilCanonical_riemannRoch",
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell": "theorem · FLTForHuman · theorem finrank_adeleBdd_inf_global_eq_ell [Nonempty (Place K F)] (D : Divisor K F) :",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating": "theorem · FLTForHuman · theorem finrank_kaehler_eq_card_of_separating {s : Finset F}",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'": "theorem · FLTForHuman · theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}",
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty": "theorem · FLTForHuman · theorem finrank_omegaSpace_eq_indexOfSpecialty (D : Divisor K F) :",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed": "theorem · FLTForHuman · theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver": "theorem · FLTForHuman · theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental": "theorem · FLTForHuman · **Riemann–Roch over an algebraically closed constant field, from a transcendental",
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed": "theorem · FLTForHuman · theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed",
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality": "theorem · FLTForHuman · theorem functionFieldRiemannRoch_of_riemann_and_duality",
    "AlgebraicCurve.genus": "def · FLTForHuman · def genus (K F : Type*) [Field K] [Field F] [Algebra K F]",
    "AlgebraicCurve.genusFF": "def · FLTForHuman · def genusFF : ℕ :=",
    "AlgebraicCurve.genus_eq_degree_div": "theorem · FLTForHuman · The pin's `AlgebraicCurve.genus_eq_degree_div` (pin 4042).",
    "AlgebraicCurve.genus_eq_genusFF": "theorem · FLTForHuman · theorem AlgebraicCurve.genus_eq_genusFF",
    "AlgebraicCurve.globalSub": "def · FLTForHuman · def globalSub : Submodule K (Place K F → F) :=",
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": "theorem · FLTForHuman · theorem hasCanonicalDivisor_of_isCurveOver",
    "AlgebraicCurve.indexOfSpecialty": "def · FLTForHuman · def indexOfSpecialty (D : Divisor K F) : ℕ :=",
    "AlgebraicCurve.indexOfSpecialty_eq": "theorem · FLTForHuman · theorem indexOfSpecialty_eq (D : Divisor K F) :",
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1": "theorem · FLTForHuman · The `H¹` identification: the adelic index of `D` is the `K`-dimension of the",
    "AlgebraicCurve.kaehlerAdjoinBasis": "def · FLTForHuman · def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :",
    "AlgebraicCurve.kaehlerRankOne_of_transcendental": "theorem · FLTForHuman · **The Kähler module of a function field is free of rank one.**",
    "AlgebraicCurve.kaehlerRankOne_ratFunc": "theorem · FLTForHuman · theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=",
    "AlgebraicCurve.lSpace_mono": "theorem · FLTForHuman · theorem lSpace_mono (hDE : D ≤ E) : LSpace D ≤ LSpace E :=",
    "AlgebraicCurve.map_diagonal_lSpace": "theorem · FLTForHuman · theorem map_diagonal_lSpace (D : Divisor K F) :",
    "AlgebraicCurve.mem_adeleSpace_iff": "theorem · FLTForHuman · theorem mem_adeleSpace_iff {α : Place K F → F} :",
    "AlgebraicCurve.mem_lSpace_iff": "theorem · FLTForHuman · theorem mem_lSpace_iff {f : F} :",
    "AlgebraicCurve.mem_lSpace_iff_ord": "theorem · FLTForHuman · theorem mem_lSpace_iff_ord {f : F} :",
    "AlgebraicCurve.omegaSpace": "def · FLTForHuman · def omegaSpace (D : Divisor K F) : Submodule K (Module.Dual K (adeleSpace K F)) :=",
    "AlgebraicCurve.omegaSpaceEquivIndexDual": "def · FLTForHuman · def omegaSpaceEquivIndexDual (D : Divisor K F) :",
    "AlgebraicCurve.one_mem_lSpace_zero": "theorem · FLTForHuman · theorem one_mem_lSpace_zero : (1 : F) ∈ LSpace (0 : Divisor K F) :=",
    "AlgebraicCurve.principalRepartitions": "def · FLTForHuman · def principalRepartitions : Submodule K ↥(repartitions K F) :=",
    "AlgebraicCurve.repartitions": "def · FLTForHuman · def repartitions : Subalgebra F (Place K F → F) :=",
    "AlgebraicCurve.repartitionsOf": "def · FLTForHuman · def repartitionsOf (D : Divisor K F) : Submodule K ↥(repartitions K F) where",
    "AlgebraicCurve.residuePairing": "def · FLTForHuman · def residuePairing [HasPrincipalDivisors K F] (W D : Divisor K F)",
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula": "theorem · FLTForHuman · The pin's `AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula`",
    "AlgebraicCurve.residuePairing_injective": "theorem · FLTForHuman · theorem residuePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)",
    "AlgebraicCurve.residuePairing_surjective": "theorem · FLTForHuman · The pin's `AlgebraicCurve.residuePairing_surjective` (pin 4682).",
    "AlgebraicCurve.riemannIndexFormula_of_genusReached": "theorem · FLTForHuman · The pin's `AlgebraicCurve.riemannIndexFormula_of_genusReached` (pin 3592).",
    "AlgebraicCurve.riemannRochSpace": "def · FLTForHuman · def riemannRochSpace (D : Divisor K F) : Submodule K F where",
    "AlgebraicCurve.stichtenothGenus_nonneg": "theorem · FLTForHuman · The pin's `AlgebraicCurve.stichtenothGenus_nonneg` (pin 4031).",
    "AlgebraicCurve.weilDifferentialModule": "def · FLTForHuman · def weilDifferentialModule : Submodule K (Module.Dual K (adeleSpace K F)) :=",
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic": "theorem · FLTForHuman · theorem weilDuality_of_riemannIndex_of_adelic",
    "AlgebraicCurve.weilOfKaehlerK": "def · FLTForHuman · def weilOfKaehlerK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)",
    "AlgebraicCurve.weilSmul": "def · FLTForHuman · def weilSmul [HasPrincipalDivisors K F] (f : F) :",
    "AlgebraicIndependent": "def · Mathlib · `AlgebraicIndependent R x` states the family of elements `x`",
    "AlgebraicIndependent.aevalEquiv": "def · Mathlib · Canonical isomorphism between polynomials and the subalgebra generated by",
    "Bot": "inductive · Mathlib · Typeclass for the `⊥` (`\\bot`) notation",
    "Bot.bot": "abbrev · Mathlib · The bot (`⊥`, `\\bot`) element ",
    "Cardinal": "def · Mathlib · `Cardinal.{u}` is the type of cardinal numbers in `Type u`,",
    "Cardinal.mk": "def · Mathlib · The cardinal number of a type",
    "Classical.choose": "def · Init · Given that there exists an element satisfying `p`, returns one such element.",
    "Classical.decEq": "def · Mathlib · Any type `α` has decidable equality classically.",
    "Classical.indefiniteDescription": "def · Init · noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=",
    "Classical.propDecidable": "def · Init · All propositions are `Decidable`.",
    "CommRing": "inductive · Mathlib · A commutative ring is a ring with commutative multiplication.",
    "CommSemiring": "inductive · Mathlib · A commutative semiring is a semiring with commutative multiplication.",
    "Derivation": "inductive · Mathlib · `D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`",
    "Derivation.leibniz": "theorem · Mathlib · @[simp]",
    "Derivation.leibniz_pow": "theorem · Mathlib · @[simp]",
    "Derivation.liftKaehlerDifferential": "def · Mathlib · The linear map from `Ω[S⁄R]`, associated with a derivation.",
    "Derivation.liftKaehlerDifferential_comp": "theorem · Mathlib · theorem Derivation.liftKaehlerDifferential_comp (D : Derivation R S M) :",
    "Derivation.liftKaehlerDifferential_comp_D": "theorem · Mathlib · @[simp]",
    "Derivation.llcomp": "def · Mathlib · The composition of a derivation with a linear map as a bilinear map",
    "Derivation.map_algebraMap": "theorem · Mathlib · @[simp]",
    "Derivation.tensorProductTo": "def · Mathlib · For an `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`.",
    "DivisionRing": "inductive · Mathlib · A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.",
    "Dvd.dvd": "abbrev · Init · Divisibility. `a ∣ b` (typed as `\\|`) means that there is some `c` such that `b = a * c`. ",
    "Equiv": "inductive · Mathlib · `α ≃ β` is the type of functions from `α → β` with a two-sided inverse.",
    "Equiv.punitProd": "def · Mathlib · `PUnit` is a left identity for type product up to an equivalence.",
    "Equiv.trans": "def · Mathlib · Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`.",
    "Even": "def · Mathlib · An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,",
    "Exists.choose": "def · Init · Extract an element from an existential statement, using `Classical.choose`.",
    "ExistsUnique": "def · Mathlib · For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`.",
    "FLTForHuman.Elliptic.EvenRec": "def · FLTForHuman · The even recursion satisfied by a normalised EDS, FLT's `EvenRec`.",
    "FLTForHuman.Elliptic.HaveSameParity₄": "def · FLTForHuman · FLT's `HaveSameParity₄`, phrased with `negOnePow`.",
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf": "theorem · FLTForHuman · theorem rel₄_transf :",
    "FLTForHuman.Elliptic.OddRec": "def · FLTForHuman · The odd recursion satisfied by a normalised EDS, FLT's `OddRec`.",
    "FLTForHuman.Elliptic.Param": "inductive · FLTForHuman · The three parameters of a normalised EDS, as indeterminates.",
    "FLTForHuman.Elliptic.Rel₃": "def · FLTForHuman · The elliptic-sequence relation, FLT's `Rel₃`.",
    "FLTForHuman.Elliptic.Rel₄OfValid": "def · FLTForHuman · FLT's `Rel₄OfValid`: the relator vanishes on same-parity, strictly decreasing",
    "FLTForHuman.Elliptic.StrictAnti₄": "def · FLTForHuman · FLT's `StrictAnti₄`: four non-negative indices in strictly decreasing order.",
    "FLTForHuman.Elliptic.addMulSub": "abbrev · FLTForHuman · FLT's `addMulSub`; definitionally mathlib's elliptic atom.",
    "FLTForHuman.Elliptic.avg₄": "def · FLTForHuman · def avg₄ : ℤ :=",
    "FLTForHuman.Elliptic.card_nTorsion": "theorem · FLTForHuman · FLT's `card_nTorsion`, and the port's main theorem: `#E[n] = n²` for `n`",
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime": "theorem · FLTForHuman · FLT's `card_nTorsion_mul_of_coprime`: the CRT decomposition of the torsion.",
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers": "theorem · FLTForHuman · FLT's `card_nTorsion_odd_fibers`: for odd `n` the `n`-torsion has exactly",
    "FLTForHuman.Elliptic.card_nTorsion_one": "theorem · FLTForHuman · theorem card_nTorsion_one :",
    "FLTForHuman.Elliptic.card_nTorsion_prime": "theorem · FLTForHuman · FLT's `card_nTorsion_prime`.",
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow": "theorem · FLTForHuman · FLT's `card_nTorsion_prime_pow`.",
    "FLTForHuman.Elliptic.card_nTorsion_two": "theorem · FLTForHuman · FLT's `card_nTorsion_two`: the 2-torsion has 4 elements when `2 ≠ 0`.",
    "FLTForHuman.Elliptic.card_smul_fiber": "theorem · FLTForHuman · FLT's `card_smul_fiber`: every fiber of `n •` has the cardinality of the",
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed": "theorem · FLTForHuman · **The theorem.** Over an algebraically closed field `K`, the `n`-torsion of",
    "FLTForHuman.Elliptic.complEDSAux": "def · FLTForHuman · FLT's `compl₂EDSAux`: the `2`-complement auxiliary sequence.",
    "FLTForHuman.Elliptic.evalEval_φ": "theorem · FLTForHuman · theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :",
    "FLTForHuman.Elliptic.evalEval_ψ_sq": "theorem · FLTForHuman · theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :",
    "FLTForHuman.Elliptic.exists_double_fiber_card": "theorem · FLTForHuman · FLT's `exists_double_fiber_card`: some `Q` has `2 * n ^ 2` preimages under",
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber": "theorem · FLTForHuman · FLT's `finite_not_squarefree_fiber`: only finitely many `c` make",
    "FLTForHuman.Elliptic.invar": "def · FLTForHuman · `6X² + b₂X + b₄`. The identity `preΨ₄ + Ψ₂Sq² = invar * Ψ₃` is what makes the",
    "FLTForHuman.Elliptic.invarDenom": "def · FLTForHuman · The denominator invariant of a sequence `u`, `invarDenom u s n`.",
    "FLTForHuman.Elliptic.invarNum": "def · FLTForHuman · The numerator invariant of a sequence `u`, `invarNum u s n`.",
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": "theorem · FLTForHuman · lemma invarNum_eq_redInvarNum_mul (m : ℤ) :",
    "FLTForHuman.Elliptic.invar_normEDS": "theorem · FLTForHuman · FLT's `invar_normEDS`.",
    "FLTForHuman.Elliptic.invar_of_net": "theorem · FLTForHuman · FLT's `invar_of_net`: the invariant ratio is independent of the index.",
    "FLTForHuman.Elliptic.invar₂_normEDS": "theorem · FLTForHuman · FLT's `invar₂_normEDS`.",
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq": "theorem · FLTForHuman · FLT's `isCoprime_Φ_ΨSq`: the `x`-numerator and the `n`-division polynomial",
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ": "theorem · FLTForHuman · `ΨSq n` and `ΨSq (n + 1)` are coprime.",
    "FLTForHuman.Elliptic.isEllipticSequence_ext": "theorem · FLTForHuman · FLT's `IsEllSequence'.ext`: two elliptic sequences agreeing at `1,2,3,4` are",
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃": "theorem · FLTForHuman · lemma isEllipticSequence_iff_rel₃ :",
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec": "theorem · FLTForHuman · FLT's `IsEllSequence'.of_oddRec_evenRec`: the odd and even recursions force",
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff": "theorem · FLTForHuman · theorem mem_nTorsion_two_iff {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :",
    "FLTForHuman.Elliptic.net": "abbrev · FLTForHuman · FLT's `net`; definitionally mathlib's `rel`.",
    "FLTForHuman.Elliptic.net_normEDS": "theorem · FLTForHuman · `normEDS` satisfies the full net property `rel = 0`.",
    "FLTForHuman.Elliptic.net_of_isEllipticSequence": "theorem · FLTForHuman · The *full* net property, from the `s = 0` slice plus non-zero-divisors: apply",
    "FLTForHuman.Elliptic.net_zero_iff_rel₃": "theorem · FLTForHuman · lemma net_zero_iff_rel₃ (m n r : ℤ) : net W m n r 0 = 0 ↔ Rel₃ W m n r :=",
    "FLTForHuman.Elliptic.normEDS_eq_aeval": "theorem · FLTForHuman · Specialising the universal EDS recovers `normEDS b c d`.",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence": "theorem · FLTForHuman · The normalised EDS satisfies the elliptic-sequence relation. In FLT this is",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors": "theorem · FLTForHuman · lemma normEDS_isEllipticSequence_of_mem_nonZeroDivisors {b c d : R} (hb : b ∈ R⁰) :",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": "theorem · FLTForHuman · The complement `complEDS` witnesses `normEDS m ∣ normEDS (n * m)`.",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": "theorem · FLTForHuman · lemma normEDS_mul_complEDS_div (b c d : R) (m : ℤ) (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :",
    "FLTForHuman.Elliptic.normEDS_two_three_two": "theorem · FLTForHuman · `normEDS 2 3 2` is the identity EDS.",
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": "theorem · FLTForHuman · lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ :=",
    "FLTForHuman.Elliptic.redInvarDenom": "def · FLTForHuman · FLT's `redInvarDenom`.",
    "FLTForHuman.Elliptic.redInvarNum": "def · FLTForHuman · FLT's `redInvarNum`, written with mathlib's `complEDS₂` in place of",
    "FLTForHuman.Elliptic.redInvar_normEDS": "theorem · FLTForHuman · FLT's `redInvar_normEDS`.",
    "FLTForHuman.Elliptic.rel₃_iff_evenRec": "theorem · FLTForHuman · lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m :=",
    "FLTForHuman.Elliptic.rel₃_iff_oddRec": "theorem · FLTForHuman · lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m :=",
    "FLTForHuman.Elliptic.rel₃_iff₄": "theorem · FLTForHuman · lemma rel₃_iff₄ (m n r : ℤ) :",
    "FLTForHuman.Elliptic.rel₄": "abbrev · FLTForHuman · FLT's `rel₄`; definitionally mathlib's `atomRel`.",
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec": "theorem · FLTForHuman · theorem rel₄_of_anti_oddRec_evenRec {W : ℤ → R} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)",
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero": "theorem · FLTForHuman · theorem smul_eq_zero_of_ΨSq_eval_eq_zero [W.IsElliptic] {n : ℕ} (hn : 0 < n)",
    "FLTForHuman.Elliptic.smul_formula_or_zero": "theorem · FLTForHuman · FLT's `smul_formula_or_zero`: away from the roots of `ΨSq n` the coordinate",
    "FLTForHuman.Elliptic.smul_surjective": "theorem · FLTForHuman · FLT's `smul_surjective`: for odd `n` invertible in `K`, multiplication by",
    "FLTForHuman.Elliptic.smul_x_eq": "theorem · FLTForHuman · theorem smul_x_eq [W.IsElliptic] {n : ℕ} (hn : 0 < n) {x₀ y₀ : K}",
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval": "theorem · FLTForHuman · On a point of the curve, `(y - negY x y)²` is the value of `Ψ₂Sq`.",
    "FLTForHuman.Elliptic.two_mul_ωe": "theorem · FLTForHuman · lemma two_mul_ωe (n : ℤ) :",
    "FLTForHuman.Elliptic.universalNormEDS": "def · FLTForHuman · The universal normalised EDS over `ℤ[B, C, D]`.",
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors": "theorem · FLTForHuman · lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :",
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero": "theorem · FLTForHuman · lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=",
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero": "theorem · FLTForHuman · FLT's `wronskian_Φ_ΨSq_ne_zero`: the Wronskian of `Φ n` and `ΨSq n` is",
    "FLTForHuman.Elliptic.ψc": "def · FLTForHuman · The `2`-complement of the division polynomials, characterised by",
    "FLTForHuman.Elliptic.ψc_spec": "theorem · FLTForHuman · The defining property of the `2`-complement. In FLT this is",
    "FLTForHuman.Elliptic.ωe": "def · FLTForHuman · FLT's `WeierstrassCurve.ωe`: the `y`-coordinate numerator of `n • P`.",
    "FLTForHuman.Elliptic.ωe_spec": "theorem · FLTForHuman · lemma ωe_spec (n : ℤ) :",
    "Fact": "inductive · Mathlib · Wrapper for adding elementary propositions to the type class systems.",
    "Field": "inductive · Mathlib · A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.",
    "Finite": "inductive · Mathlib · A type is `Finite` if it is in bijective correspondence to some `Fin n`.",
    "FiniteDimensional": "abbrev · Mathlib · `FiniteDimensional` vector spaces are defined to be finite modules.",
    "Finset": "inductive · Mathlib · `Finset α` is the type of finite sets of elements of `α`. It is implemented",
    "Finset.card": "def · Mathlib · `s.card` is the number of elements of `s`, aka its cardinality.",
    "Finset.sum": "def · Mathlib · `∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements",
    "Finsupp": "inductive · Mathlib · `Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that",
    "Finsupp.liftAddHom": "def · Mathlib · The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`",
    "Finsupp.module": "def · Mathlib · instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=",
    "Finsupp.single": "def · Mathlib · `single a b` is the finitely supported function with value `b` at `a` and zero otherwise.",
    "Finsupp.support": "abbrev · Mathlib · The support of a finitely supported function (aka `Finsupp`).",
    "FreeAddMonoid": "def · Mathlib · If `α` is a type, then `FreeAddMonoid α` is the free additive monoid generated by `α`.",
    "FunLike": "abbrev · Mathlib · The class `FunLike F α β` (`Fun`ction-`Like`) expresses that terms of type `F`",
    "Function.Injective": "def · Init · A function `f : α → β` is called injective if `f x = f y` implies `x = y`.",
    "Function.Odd": "def · Mathlib · A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`.",
    "Function.RightInverse": "def · Init · `RightInverse g f` means that `g` is a right inverse to `f`. That is, `f ∘ g = id`.",
    "Function.Surjective": "def · Init · A function `f : α → β` is called surjective if every `b : β` is equal to `f a`",
    "Function.algebra": "def · Mathlib · A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate",
    "Function.comp": "def · Init · Function composition, usually written with the infix operator `∘`. A new function is created from",
    "GE.ge": "def · Init · `a ≥ b` is an abbreviation for `b ≤ a`. ",
    "HMod.hMod": "abbrev · Init · `a % b` computes the remainder upon dividing `a` by `b`.",
    "HSMul.hSMul": "abbrev · Init · `a • b` computes the product of `a` and `b`.",
    "HasQuotient.Quotient": "abbrev · Mathlib · `HasQuotient.Quotient A b` (denoted as `A ⧸ b`) is the quotient of the type `A` by `b`.",
    "Ideal": "abbrev · Mathlib · A (left) ideal in a semiring `R` is an additive submonoid `s` such that",
    "Ideal.Cotangent": "def · Mathlib · `I ⧸ I ^ 2` as a quotient of `I`.",
    "Ideal.Cotangent.smul_eq_zero_of_mem": "theorem · Mathlib · lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}",
    "Ideal.IsTwoSided": "inductive · Mathlib · A left ideal `I : Ideal R` is two-sided if it is also a right ideal.",
    "Ideal.Quotient.mk": "def · Mathlib · The ring homomorphism from a ring `R` to a quotient ring `R/I`.",
    "Ideal.comap": "def · Mathlib · `I.comap f` is the preimage of `I` under `f`.",
    "Ideal.map_toCotangent_ker": "theorem · Mathlib · theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 :=",
    "Ideal.mk_ker": "theorem · Mathlib · @[simp]",
    "Ideal.mul_mem_left": "theorem · Mathlib · theorem mul_mem_left : b ∈ I → a * b ∈ I :=",
    "Ideal.mul_mem_mul": "theorem · Mathlib · theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=",
    "Ideal.span": "abbrev · Mathlib · The ideal generated by a subset of a ring",
    "Ideal.toCotangent": "def · Mathlib · The quotient map from `I` to `I ⧸ I ^ 2`.",
    "Ideal.toCotangent_eq": "theorem · Mathlib · theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 :=",
    "Infinite": "inductive · Mathlib · A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to",
    "Int": "inductive · Init · The integers.",
    "Int.cast": "def · Init · The canonical homomorphism `Int → R`. In most use cases, the target type will have a ring structure,",
    "Int.decLt": "def · Init · Decides whether `a < b`.",
    "Int.inductionOn'": "def · Mathlib · Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater",
    "Int.natAbs": "def · Init · The absolute value of an integer is its distance from `0`.",
    "Int.negOnePow": "def · Mathlib · The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.",
    "Int.sign": "def · Init · Returns the “sign” of the integer as another integer:",
    "Int.strongRec": "def · Mathlib · A strong recursor for `Int` that specifies explicit values for integers below a threshold,",
    "Int.tdiv": "def · Init · Integer division using the T-rounding convention.",
    "IntermediateField": "inductive · Mathlib · `S : IntermediateField K L` is a subset of `L` such that there is a field",
    "IntermediateField.adjoin": "def · Mathlib · `adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.",
    "IntermediateField.algebra'": "def · Mathlib · instance algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)",
    "Inv.inv": "abbrev · Init · `a⁻¹` computes the inverse of `a`.",
    "InvImage": "def · Init · The inverse image of `r : β → β → Prop` by a function `α → β` is the relation",
    "Irreducible": "inductive · Mathlib · `Irreducible p` states that `p` is non-unit and only factors into units.",
    "Irreducible.maximalIdeal_eq": "theorem · Mathlib · theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :",
    "IsAlgClosed": "inductive · Mathlib · An algebraically closed field is one where every polynomial splits. Equivalently, all",
    "IsCoprime": "def · Mathlib · The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such",
    "IsDedekindDomain": "inductive · Mathlib · A Dedekind domain is an integral domain that is Noetherian, integrally closed, and",
    "IsDedekindDomain.HeightOneSpectrum": "inductive · Mathlib · The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of",
    "IsDedekindDomain.HeightOneSpectrum.asIdeal": "abbrev · Mathlib · ",
    "IsDedekindDomain.HeightOneSpectrum.intValuation": "def · Mathlib · The `v`-adic valuation on `R`.",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": "theorem · Mathlib · The `v`-adic valuation on `R` is bounded above by 1.",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": "theorem · Mathlib · The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`.",
    "IsDedekindDomain.HeightOneSpectrum.valuation": "def · Mathlib · The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuation of `s`,",
    "IsDiscreteValuationRing": "inductive · Mathlib · An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which",
    "IsDiscreteValuationRing.exists_irreducible": "theorem · Mathlib · Uniformizers exist in a DVR.",
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": "theorem · Mathlib · An element of a DVR is irreducible iff it is a uniformizer, that is, generates the",
    "IsDiscreteValuationRing.maximalIdeal": "def · Mathlib · The maximal ideal of a discrete valuation ring.",
    "IsDomain": "inductive · Mathlib · A domain is a nontrivial semiring such that multiplication by a nonzero element",
    "IsDvdSequence": "def · Mathlib · A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.",
    "IsEllipticDvdSequence": "def · Mathlib · The proposition that a sequence indexed by `ℤ` is an EDS.",
    "IsEllipticNet": "def · Mathlib · The proposition that a sequence indexed by `ℤ` is an elliptic net.",
    "IsEllipticNet.atom": "def · Mathlib · The elliptic atom `Wₐ(a, b)` that defines an elliptic net. Note that this is defined in terms of",
    "IsEllipticNet.atomRel": "def · Mathlib · The elliptic relator `ERₐ(a, b, c, d)` obtained by a change of variables in `ER(p, q, r, s)`",
    "IsEllipticNet.atomRel_eq": "theorem · Mathlib · lemma atomRel_eq {a b c d : ℤ} (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) :",
    "IsEllipticNet.rel": "def · Mathlib · The elliptic relator `ER(p, q, r, s)` that defines an elliptic net.",
    "IsEllipticNet.rel_eq": "theorem · Mathlib · lemma rel_eq (p q r s : ℤ) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s :=",
    "IsEllipticSequence": "def · Mathlib · The proposition that a sequence indexed by `ℤ` is an elliptic sequence.",
    "IsFractionRing.algEquivOfAlgEquiv": "def · Mathlib · Given `R`-algebras `A, B` and localization maps to their fraction rings",
    "IsLocalRing.ResidueField": "def · Mathlib · The residue field of a local ring is the quotient of the ring by its maximal ideal.",
    "IsLocalRing.ResidueField.algebra": "def · Mathlib · instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :",
    "IsLocalRing.ResidueField.field": "def · Mathlib · noncomputable instance ResidueField.field : Field (ResidueField R) :=",
    "IsLocalRing.maximalIdeal": "def · Mathlib · The ideal of elements that are not units.",
    "IsLocalization": "abbrev · Mathlib · The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra",
    "IsScalarTower": "inductive · Mathlib · An instance of `IsScalarTower M N α` states that the multiplicative",
    "IsScalarTower.algebraMap_smul": "theorem · Mathlib · theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :",
    "IsScalarTower.left": "theorem · Mathlib · @[to_additive]",
    "IsScalarTower.right": "theorem · Mathlib · This has high priority because it is almost always the right instance when it applies.",
    "IsScalarTower.to_smulCommClass": "theorem · Mathlib · instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=",
    "IsSeparable": "def · Mathlib · An element `x` of an algebra `K` over a commutative ring `F` is said to be *separable*, if its",
    "IsUnit": "def · Mathlib · An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.",
    "KaehlerDifferential": "def · Mathlib · The module of Kähler differentials (Kahler differentials, Kaehler differentials).",
    "KaehlerDifferential.D": "def · Mathlib · The universal derivation into `Ω[S⁄R]`.",
    "KaehlerDifferential.DLinearMap": "def · Mathlib · (Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`.",
    "KaehlerDifferential.D_apply": "theorem · Mathlib · theorem KaehlerDifferential.D_apply (s : S) :",
    "KaehlerDifferential.D_ne_zero_of_transcendental": "theorem · FLTForHuman · theorem D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendent",
    "KaehlerDifferential.ideal": "abbrev · Mathlib · The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.",
    "KaehlerDifferential.isScalarTower_of_tower": "theorem · Mathlib · instance KaehlerDifferential.isScalarTower_of_tower {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]",
    "KaehlerDifferential.linearMapEquivDerivation": "def · Mathlib · The `S`-linear maps from `Ω[S⁄R]` to `M` are (`S`-linearly) equivalent to `R`-derivations",
    "KaehlerDifferential.mapBaseChange": "def · Mathlib · The lift of the map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` to the base change along `A → B`.",
    "KaehlerDifferential.mvPolynomialBasis": "def · Mathlib · `{ dx | x ∈ σ }` forms a basis of the relative differential module",
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal": "theorem · Mathlib · theorem KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (a : S) :",
    "KaehlerDifferential.polynomialEquiv": "def · Mathlib · The relative differential module of the univariate polynomial algebra `R[X]` is isomorphic to",
    "KaehlerDifferential.polynomialEquiv_D": "theorem · Mathlib · @[simp]",
    "KaehlerDifferential.polynomialEquiv_symm": "theorem · Mathlib · @[simp]",
    "KaehlerDifferential.polynomial_D_apply": "theorem · Mathlib · lemma KaehlerDifferential.polynomial_D_apply (P : R[X]) :",
    "KaehlerDifferential.span_D_eq_top_of_transcendental": "theorem · FLTForHuman · theorem span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcen",
    "KaehlerDifferential.span_range_eq_ideal": "theorem · Mathlib · theorem KaehlerDifferential.span_range_eq_ideal :",
    "KaehlerDifferential.subsingleton_of_surjective": "theorem · Mathlib · `Ω[S⁄R]` is trivial if `R → S` is surjective.",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": "def · Mathlib · The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap": "theorem · Mathlib · lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap",
    "KaehlerDifferential.tensorProductTo_surjective": "theorem · Mathlib · theorem KaehlerDifferential.tensorProductTo_surjective :",
    "LinearEquiv": "inductive · Mathlib · A linear equivalence is an invertible linear map.",
    "LinearEquiv.ofBijective": "def · Mathlib · A bijective linear map is a linear equivalence.",
    "LinearEquiv.symm": "def · Mathlib · Linear equivalences are symmetric.",
    "LinearEquiv.trans": "def · Mathlib · Linear equivalences are transitive.",
    "LinearIndependent": "def · Mathlib · `LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`.",
    "LinearIndependent.finrank_eq_zero_of_infinite": "theorem · Mathlib · lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}",
    "LinearMap": "inductive · Mathlib · A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`",
    "LinearMap.addCommMonoid": "def · Mathlib · The type of linear maps is an additive monoid.",
    "LinearMap.comp": "def · Mathlib · Composition of two linear maps is a linear map",
    "LinearMap.flip": "def · Mathlib · Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to",
    "LinearMap.ker": "def · Mathlib · The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the",
    "LinearMap.lsmul": "def · Mathlib · Scalar multiplication as a bilinear map `R → M → M`.",
    "LinearMap.mk₂": "def · Mathlib · Create a bilinear map from a function that is linear in each component.",
    "LinearMap.module": "def · Mathlib · instance module : Module S (M →ₛₗ[σ₁₂] M₂) where",
    "LinearMap.mul": "def · Mathlib · The multiplication in a non-unital non-associative algebra is a bilinear map.",
    "LinearMap.range": "def · Mathlib · The range of a linear map `f : M → M₂` is a submodule of `M₂`.",
    "LinearMap.restrictScalars": "def · Mathlib · If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures",
    "List.Pairwise": "inductive · Init · Each element of a list is related to all later elements of the list by `R`.",
    "Max.max": "abbrev · Init · Returns the greater of its two arguments. ",
    "Min.min": "abbrev · Init · Returns the lesser of its two arguments. ",
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax": "theorem · FLTForHuman · `deg((ω)) = 2γ - 2` from the same hypothesis (pin 6110).",
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax": "theorem · FLTForHuman · `ℓ((ω)) = γ` from the maximal-functional hypothesis (pin 6093).",
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax": "theorem · FLTForHuman · `dim Ω(D) = ℓ((ω) - D)` from a maximal functional and a reached genus (pin 6080).",
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK": "theorem · FLTForHuman · Riemann–Roch from the K residue theorem and `ConstantsAreBase` (pin 6208).",
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax": "theorem · FLTForHuman · The Riemann index formula from the maximal-functional hypothesis (pin 6167).",
    "ModularCurve.wkc_weilOfKaehlerK_single": "theorem · FLTForHuman · The Weil–Kähler functional on one adele: the trace of its local residue (pin 5992).",
    "Module": "inductive · Mathlib · A module is a generalization of vector spaces to a scalar semiring.",
    "Module.Basis": "inductive · Mathlib · A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.",
    "Module.Basis.baseChange": "def · Mathlib · The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`.",
    "Module.Basis.map": "def · Mathlib · Apply the linear equivalence `f` to the basis vectors.",
    "Module.Basis.ne_zero": "theorem · Mathlib · protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=",
    "Module.Basis.reindex": "def · Mathlib · `b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'`",
    "Module.Basis.repr": "abbrev · Mathlib · `repr` is the linear equivalence sending a vector `x` to its coordinates:",
    "Module.Basis.singleton": "def · Mathlib · `Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`.",
    "Module.Basis.span_eq": "theorem · Mathlib · @[simp]",
    "Module.Basis.tensorProduct": "def · Mathlib · If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`.",
    "Module.Dual": "abbrev · Mathlib · The left dual space of an R-module M is the R-module of linear maps `M → R`.",
    "Module.End": "abbrev · Mathlib · Linear endomorphisms of a module, with associated ring structure",
    "Module.Finite": "inductive · Mathlib · A module over a semiring is `Module.Finite` if it is finitely generated as a module.",
    "Module.Free": "inductive · Mathlib · `Module.Free R M` is the statement that the `R`-module `M` is free.",
    "Module.finrank": "def · Mathlib · The rank of a module as a natural number.",
    "Module.rank": "def · Mathlib · The rank of a module, defined as a term of type `Cardinal`.",
    "Monoid": "inductive · Mathlib · A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`.",
    "MonoidWithZeroHom": "inductive · Mathlib · `α →*₀ β` is the type of functions `α → β` that preserve",
    "MonoidWithZeroHom.funLike": "def · Mathlib · @[macro_inline]",
    "Mul": "inductive · Init · The homogeneous version of `HMul`: `a * b : α` where `a b : α`.",
    "MulAction": "inductive · Mathlib · Type class for monoid actions on types, with notation `g • p`.",
    "Multiplicative": "def · Mathlib · If `α` carries some additive structure, then `Multiplicative α` carries the corresponding",
    "Multiplicative.commMonoid": "def · Mathlib · instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=",
    "Multiplicative.group": "def · Mathlib · instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=",
    "Multiplicative.isOrderedCancelMonoid": "theorem · Mathlib · instance Multiplicative.isOrderedCancelMonoid",
    "Multiplicative.linearOrder": "def · Mathlib · instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=",
    "Multiplicative.monoid": "def · Mathlib · instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where",
    "Multiplicative.mul": "def · Mathlib · instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where",
    "Multiplicative.ofAdd": "def · Mathlib · Reinterpret `x : α` as an element of `Multiplicative α`.",
    "Multiplicative.preorder": "def · Mathlib · instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=",
    "MvPolynomial": "abbrev · Mathlib · Multivariate polynomial, where `σ` is the index set of the variables and",
    "MvPolynomial.X": "def · Mathlib · `X n` is the degree `1` monomial $X_n$.",
    "MvPolynomial.aeval": "def · Mathlib · A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism",
    "Nat": "inductive · Init · The natural numbers, starting at zero.",
    "Nat.Coprime": "def · Init · `m` and `n` are coprime, or relatively prime, if their `gcd` is 1.",
    "Nat.Prime": "def · Mathlib · `Nat.Prime p` means that `p` is a prime number, that is, a natural number",
    "Nat.card": "def · Mathlib · `Nat.card α` is the cardinality of `α` as a natural number.",
    "Nat.cast": "def · Init · The canonical homomorphism `Nat → R`. In most use cases, the target type will have a (semi)ring",
    "Nat.recOnPosPrimePosCoprime": "def · Mathlib · Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and",
    "Nat.recOnPrimePow": "def · Mathlib · Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,",
    "Ne": "def · Init · `a ≠ b`, or `Ne a b` is defined as `¬ (a = b)` or `a = b → False`,",
    "NoZeroDivisors": "inductive · Mathlib · Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`",
    "NonUnitalNonAssocSemiring": "inductive · Mathlib · A not-necessarily-unital, not-necessarily-associative semiring. See `CommutatorRing` and the",
    "Nonempty": "inductive · Init · `Nonempty α` is a typeclass that says that `α` is not an empty type,",
    "Nontrivial": "inductive · Mathlib · Predicate typeclass for expressing that a type is not reduced to a single element. In rings,",
    "Odd": "def · Mathlib · An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`.",
    "Option": "inductive · Init · Optional values, which are either `some` around a value from the underlying type or `none`.",
    "Option.map₂": "def · Mathlib · The image of a binary function `f : α → β → γ` as a function `Option α → Option β → Option γ`.",
    "OreLocalization.oreSetComm": "def · Mathlib · Every submonoid of a commutative monoid is an Ore set.",
    "PerfectField": "inductive · Mathlib · A perfect field.",
    "Pi.Function.module": "def · Mathlib · A special case of `Pi.module` for non-dependent types. Lean struggles to elaborate",
    "Pi.addCommGroup": "def · Mathlib · ",
    "Pi.addCommMonoid": "def · Mathlib · ",
    "Pi.isScalarTower": "theorem · Mathlib · @[to_additive]",
    "Pi.nonAssocSemiring": "def · Mathlib · instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) :=",
    "Polynomial": "inductive · Mathlib · `Polynomial R` is the type of univariate polynomials over `R`,",
    "Polynomial.C": "def · Mathlib · `C a` is the constant polynomial `a`.",
    "Polynomial.CC": "abbrev · Mathlib · A constant viewed as a polynomial in two variables.",
    "Polynomial.Separable": "def · Mathlib · A polynomial is separable iff it is coprime with its derivative.",
    "Polynomial.X": "def · Mathlib · `X` is the polynomial variable (aka indeterminate).",
    "Polynomial.algEquivOfTranscendental": "def · Mathlib · Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence",
    "Polynomial.algebraOfAlgebra": "def · Mathlib · Note that this instance also provides `Algebra R R[X]`.",
    "Polynomial.degree": "def · Mathlib · `degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.",
    "Polynomial.derivative": "def · Mathlib · `derivative p` is the formal derivative of the polynomial `p`",
    "Polynomial.derivative'": "def · Mathlib · `Polynomial.derivative` as a derivation.",
    "Polynomial.eval": "def · Mathlib · `eval x p` is the evaluation of the polynomial `p` at `x`",
    "Polynomial.evalEval": "abbrev · Mathlib · `evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[X][Y]`.",
    "Polynomial.module": "def · Mathlib · instance module {S} [Semiring S] [Module S R] : Module S R[X] :=",
    "Polynomial.monomial": "def · Mathlib · `monomial s a` is the monomial `a * X^s`",
    "Polynomial.natDegree": "def · Mathlib · `natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.",
    "Preorder": "inductive · Mathlib · A preorder is a reflexive, transitive relation `≤`.",
    "Prod": "inductive · Init · The product type, usually written `α × β`. Product types are also called pair or tuple types.",
    "QuotientAddGroup.Quotient.addCommGroup": "def · Mathlib · ",
    "QuotientAddGroup.mk": "abbrev · Mathlib · The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`.",
    "RatFunc": "inductive · Mathlib · `RatFunc K` is `K(X)`, the field of rational functions over `K`.",
    "RatFunc.X": "def · Mathlib · `RatFunc.X` is the polynomial variable (aka indeterminate).",
    "RatFunc.algEquivOfTranscendental": "def · Mathlib · Given a transcendental `f : L`, the `K`-algebra isomorphism between `RatFunc K` and `L` given",
    "RatFunc.algEquivOfTranscendental_X": "theorem · Mathlib · @[simp]",
    "Ring": "inductive · Mathlib · A `Ring` is a `Semiring` with negation making it an additive group.",
    "RingEquiv": "inductive · Mathlib · An equivalence between two (non-unital non-associative semi)rings that preserves the",
    "RingHom": "inductive · Mathlib · Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.",
    "RingHom.comp": "def · Mathlib · Composition of ring homomorphisms is a ring homomorphism.",
    "RingHom.id": "def · Mathlib · The identity ring homomorphism from a semiring to itself.",
    "RingHom.ker": "def · Mathlib · Kernel of a ring homomorphism as an ideal of the domain.",
    "RingHom.kerLift": "def · Mathlib · The induced map from the quotient by the kernel to the codomain.",
    "RingHom.mem_ker": "theorem · Mathlib · An element is in the kernel if and only if it maps to zero.",
    "RingHom.quotientKerEquivOfRightInverse": "def · Mathlib · The **first isomorphism theorem for commutative rings**, computable version.",
    "RingHom.quotientKerEquivOfSurjective": "def · Mathlib · The **first isomorphism theorem** for commutative rings, surjective case.",
    "RingHomClass": "inductive · Mathlib · `RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.",
    "RingHomInvPair.ids": "theorem · Mathlib · instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=",
    "RingHomSurjective.ids": "theorem · Mathlib · instance ids : RingHomSurjective (RingHom.id R₁) :=",
    "SMul": "inductive · Init · Typeclass for types with a scalar multiplication operation, denoted `•` (`\\bu`)",
    "SMulCommClass": "inductive · Mathlib · A typeclass mixin saying that two multiplicative actions on the same space commute.",
    "SMulWithZero": "inductive · Mathlib · `SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar multiplication",
    "Semiring": "inductive · Mathlib · A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is",
    "Set": "def · Mathlib · A set is a collection of elements of some type `α`.",
    "Set.Finite": "def · Mathlib · A set is finite if the corresponding `Subtype` is finite,",
    "Set.ofPred": "def · Mathlib · Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}`",
    "Set.range": "def · Mathlib · Range of a function.",
    "Set.univ": "def · Mathlib · The universal set on a type `α` is the set containing all elements of `α`.",
    "Squarefree": "def · Mathlib · An element of a monoid is squarefree if the only squares that",
    "Subalgebra": "inductive · Mathlib · A subalgebra is a sub(semi)ring that includes the range of `algebraMap`.",
    "Subalgebra.algebra": "def · Mathlib · instance algebra : Algebra R S :=",
    "Subalgebra.algebra'": "def · Mathlib · More general form of `Subalgebra.algebra`.",
    "Submodule": "inductive · Mathlib · A submodule of a module is one which is closed under vector operations.",
    "Submodule.Quotient.addCommMonoid": "def · Mathlib · instance addCommMonoid : AddCommMonoid (M ⧸ p) :=",
    "Submodule.Quotient.mk": "def · Mathlib · Map associating to an element of `M` the corresponding element of `M/p`,",
    "Submodule.Quotient.module": "def · Mathlib · instance module (P : Submodule R M) : Module R (M ⧸ P) :=",
    "Submodule.Quotient.module'": "def · Mathlib · instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :",
    "Submodule.Quotient.restrictScalarsEquiv": "def · Mathlib · The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,",
    "Submodule.addCommGroup": "def · Mathlib · instance addCommGroup : AddCommGroup p :=",
    "Submodule.addCommMonoid": "def · Mathlib · instance addCommMonoid : AddCommMonoid p :=",
    "Submodule.comap": "def · Mathlib · The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`",
    "Submodule.completeLattice": "def · Mathlib · instance completeLattice : CompleteLattice (Submodule R M) where",
    "Submodule.dualAnnihilator": "def · Mathlib · The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such",
    "Submodule.dualQuotEquivDualAnnihilator": "def · Mathlib · Equivalence $(M/W)^* \\cong \\operatorname{ann}(W)$. That is, there is a one-to-one",
    "Submodule.hasQuotient": "def · Mathlib · The quotient of a module `M` by a submodule `p ⊆ M`.",
    "Submodule.idemSemiring": "def · Mathlib · Sub-R-modules of an R-algebra form an idempotent semiring.",
    "Submodule.liftQ": "def · Mathlib · The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`",
    "Submodule.map": "def · Mathlib · The pushforward of a submodule `p ⊆ M` by `f : M → M₂`",
    "Submodule.mem_bot": "theorem · Mathlib · @[simp]",
    "Submodule.mem_top": "theorem · Mathlib · @[simp] lemma mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=",
    "Submodule.mem_torsionBy_iff": "theorem · Mathlib · @[simp]",
    "Submodule.mkQ": "def · Mathlib · The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map.",
    "Submodule.module": "def · Mathlib · instance module : Module R p :=",
    "Submodule.module'": "def · Mathlib · instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :",
    "Submodule.mul": "def · Mathlib · Multiplication of sub-R-modules of an R-module A that is also a semiring. The submodule `M * N`",
    "Submodule.restrictScalars": "def · Mathlib · `V.restrictScalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,",
    "Submodule.span": "def · Mathlib · The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`.",
    "Submodule.subtype": "def · Mathlib · Embedding of a submodule `p` to the ambient space `M`.",
    "Submodule.torsionBy": "def · Mathlib · The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that",
    "Submonoid": "inductive · Mathlib · A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication.",
    "Subsingleton": "inductive · Init · A _subsingleton_ is a type with at most one element. It is either empty or has a unique element.",
    "Subspace.dual_finrank_eq": "theorem · Mathlib · @[simp]",
    "TensorProduct": "def · Mathlib · The tensor product of two modules `M` and `N` over the same commutative semiring `R`.",
    "TensorProduct.AlgebraTensorModule.lift": "def · Mathlib · Heterobasic version of `TensorProduct.lift`:",
    "TensorProduct.AlgebraTensorModule.mk": "def · Mathlib · Heterobasic version of `TensorProduct.mk`:",
    "TensorProduct.Eqv": "inductive · Mathlib · The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is",
    "TensorProduct.addCommGroup": "def · Mathlib · instance addCommGroup : AddCommGroup (M ⊗[R] N) where",
    "TensorProduct.addCommMonoid": "def · Mathlib · instance addCommMonoid : AddCommMonoid (M ⊗[R] N) where",
    "TensorProduct.homTensorHomMap": "def · Mathlib · The linear map from `(M →ₛₗ[σ₁₂] M₂) ⊗ (N →ₛₗ[σ₁₂] N₂)` to `M ⊗ N →ₛₗ[σ₁₂] M₂ ⊗ N₂`",
    "TensorProduct.leftHasSMul": "def · Mathlib · Given two modules over a commutative semiring `R`, if one of the factors carries a",
    "TensorProduct.leftModule": "def · Mathlib · instance leftModule : Module R'' (M ⊗[R] N) :=",
    "TensorProduct.map": "def · Mathlib · The tensor product of a pair of linear maps between modules.",
    "TensorProduct.map₂": "def · Mathlib · This is a binary version of `TensorProduct.map`: Given a bilinear map `f : M ⟶ P ⟶ Q` and a",
    "TensorProduct.smulCommClass_left": "theorem · Mathlib · `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)`",
    "TensorProduct.tmul": "def · Mathlib · The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,",
    "Top": "inductive · Mathlib · Typeclass for the `⊤` (`\\top`) notation",
    "Top.top": "abbrev · Mathlib · The top (`⊤`, `\\top`) element ",
    "Transcendental": "def · Mathlib · An element of an R-algebra is transcendental over R if it is not algebraic over R.",
    "Transcendental.pow": "theorem · Mathlib · theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :",
    "True": "inductive · Init · `True` is a proposition and has only an introduction rule, `True.intro : True`.",
    "Unit": "abbrev · Init · The canonical type with one element. This element is written `()`.",
    "Units": "inductive · Mathlib · Units of a `Monoid`, bundled version. Notation: `αˣ`.",
    "Units.val": "abbrev · Mathlib · The underlying value in the base `Monoid`.",
    "Valuation": "inductive · Mathlib · The type of `Γ₀`-valued valuations on `R`.",
    "ValuationSubring": "inductive · Mathlib · A valuation subring of a field `K` is a subring `A` such that for every `x : K`,",
    "WeierstrassCurve": "inductive · Mathlib · A Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with parameters `aᵢ`.",
    "WeierstrassCurve.Affine": "abbrev · Mathlib · An abbreviation for a Weierstrass curve in affine coordinates.",
    "WeierstrassCurve.Affine.CoordinateRing": "abbrev · Mathlib · The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩` of a Weierstrass curve `W`.",
    "WeierstrassCurve.Affine.CoordinateRing.mk": "abbrev · Mathlib · The natural ring homomorphism mapping `R[X][Y]` to `R[W]`.",
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": "theorem · Mathlib · lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": "theorem · Mathlib · lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": "theorem · Mathlib · lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": "theorem · Mathlib · lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) :=",
    "WeierstrassCurve.Affine.Equation": "def · Mathlib · The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.",
    "WeierstrassCurve.Affine.Nonsingular": "def · Mathlib · The proposition that an affine point `(x, y)` on a Weierstrass curve `W` is nonsingular.",
    "WeierstrassCurve.Affine.Point": "inductive · Mathlib · A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is either the unique",
    "WeierstrassCurve.Affine.negPolynomial": "def · Mathlib · The negation polynomial `-Y - a₁X - a₃` associated to the negation of a nonsingular affine point",
    "WeierstrassCurve.Affine.negY": "def · Mathlib · The `Y`-coordinate of `-(x, y)` for a nonsingular affine point `(x, y)` on a Weierstrass curve",
    "WeierstrassCurve.Affine.polynomial": "def · Mathlib · The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated to a Weierstrass",
    "WeierstrassCurve.Affine.polynomialX": "def · Mathlib · The partial derivative `W_X(X, Y)` with respect to `X` of the polynomial `W(X, Y)` associated to",
    "WeierstrassCurve.Affine.polynomialY": "def · Mathlib · The partial derivative `W_Y(X, Y)` with respect to `Y` of the polynomial `W(X, Y)` associated to",
    "WeierstrassCurve.C_Ψ₂Sq": "theorem · Mathlib · lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial :=",
    "WeierstrassCurve.IsElliptic": "inductive · Mathlib · `WeierstrassCurve.IsElliptic` is a typeclass which asserts that a Weierstrass curve is an",
    "WeierstrassCurve.a₁": "abbrev · Mathlib · The `a₁` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.a₃": "abbrev · Mathlib · The `a₃` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.baseChange": "def · Mathlib · The Weierstrass curve base changed to an algebra `A` over `R`.",
    "WeierstrassCurve.b₂": "def · Mathlib · The `b₂` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.b₄": "def · Mathlib · The `b₄` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.b₆": "def · Mathlib · The `b₆` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.b₈": "def · Mathlib · The `b₈` coefficient of a Weierstrass curve.",
    "WeierstrassCurve.isElliptic_iff": "theorem · Mathlib · ",
    "WeierstrassCurve.mk": "constructor · Mathlib · structure WeierstrassCurve (R : Type u) where",
    "WeierstrassCurve.natDegree_Φ": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.natDegree_ΨSq": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.preΨ": "def · Mathlib · The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials",
    "WeierstrassCurve.preΨ'": "def · Mathlib · The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials",
    "WeierstrassCurve.preΨ_even": "theorem · Mathlib · lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =",
    "WeierstrassCurve.preΨ_odd": "theorem · Mathlib · lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =",
    "WeierstrassCurve.preΨ₄": "def · Mathlib · The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial",
    "WeierstrassCurve.twoTorsionPolynomial": "def · Mathlib · A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If",
    "WeierstrassCurve.Δ": "def · Mathlib · The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes",
    "WeierstrassCurve.Φ": "def · Mathlib · The univariate polynomials `Φₙ` congruent to `φₙ`.",
    "WeierstrassCurve.Φ_neg": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.Φ_three": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.Ψ": "def · Mathlib · The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`.",
    "WeierstrassCurve.ΨSq": "def · Mathlib · The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`.",
    "WeierstrassCurve.ΨSq_three": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.Ψ₂Sq": "def · Mathlib · The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`.",
    "WeierstrassCurve.Ψ₂Sq_eq": "theorem · Mathlib · lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=",
    "WeierstrassCurve.Ψ₃": "def · Mathlib · The `3`-division polynomial `ψ₃ = Ψ₃`.",
    "WeierstrassCurve.φ": "def · Mathlib · The bivariate polynomials `φₙ`.",
    "WeierstrassCurve.ψ": "def · Mathlib · The bivariate `n`-division polynomials `ψₙ`.",
    "WeierstrassCurve.ψ_one": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.ψ_two": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.ψ_zero": "theorem · Mathlib · @[simp]",
    "WeierstrassCurve.ψ₂": "def · Mathlib · The `2`-division polynomial `ψ₂ = Ψ₂`.",
    "WellFounded.Nat.fix": "def · Init · A well-founded fixpoint operator specialized for `Nat`-valued measures. Given a measure `h`, it expects",
    "WithBot.unbotD": "def · Mathlib · Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries.",
    "WithZero": "def · Mathlib · Add an extra element `0` to a type",
    "WithZero.exp": "def · Mathlib · The exponential map as a function `M → Mᵐ⁰`.",
    "WithZero.log": "def · Mathlib · The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`.",
    "WithZero.logEquiv": "def · Mathlib · The logarithm as an equivalence between `(Gᵐ⁰)ˣ` and `G`.",
    "WithZero.log_mul": "theorem · Mathlib · @[simp]",
    "WithZero.map₂": "def · Mathlib · The image of a binary function `f : α → β → γ` as a function",
    "WithZero.one": "def · Mathlib · instance one : One (WithZero α) where",
    "WithZero.recZeroCoe": "def · Mathlib · Recursor for `WithZero` using the preferred forms `0` and `↑a`.",
    "WithZero.unitsWithZeroEquiv": "def · Mathlib · Any group is isomorphic to the units of itself adjoined with `0`.",
    "Zero": "inductive · Init · A type with a zero element.",
    "abs": "def · Mathlib · `abs a`, denoted `|a|`, is the absolute value of `a`",
    "addConGen": "def · Mathlib · The inductively defined smallest additive congruence relation containing",
    "addOrderOf": "def · Mathlib · `addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it",
    "addOrderOf_dvd_of_nsmul_eq_zero": "theorem · Mathlib · ",
    "complEDS": "def · Mathlib · The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses",
    "complEDS'": "def · Mathlib · The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses",
    "complEDS₂": "def · Mathlib · The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses",
    "exists_prime_addOrderOf_dvd_card'": "theorem · Mathlib · For every prime `p` dividing the order of a finite additive group `G` there exists",
    "exists_smul_eq_of_finrank_eq_one": "theorem · Mathlib · In a one-dimensional space, any vector is a multiple of any nonzero vector",
    "iSup": "def · Mathlib · Indexed supremum",
    "id": "def · Init · The identity function. `id` takes an implicit argument `α : Sort u`",
    "inferInstance": "abbrev · Init · `inferInstance` synthesizes a value of any target type by typeclass",
    "le_trans": "theorem · Mathlib · The relation `≤` on a preorder is transitive.",
    "minpoly": "def · Mathlib · Suppose `x : B`, where `B` is an `A`-algebra.",
    "nonZeroDivisors": "def · Mathlib · The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`.",
    "normEDS": "def · Mathlib · The canonical example of a normalised EDS `W : ℤ → R`, with initial values",
    "normEDS_dvd_normEDS_two_mul": "theorem · Mathlib · lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=",
    "normEDS_even": "theorem · Mathlib · lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =",
    "normEDS_four": "theorem · Mathlib · @[simp]",
    "normEDS_mul_complEDS₂": "theorem · Mathlib · lemma normEDS_mul_complEDS₂ (k : ℤ) :",
    "normEDS_neg": "theorem · Mathlib · @[simp]",
    "normEDS_odd": "theorem · Mathlib · lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =",
    "normEDS_one": "theorem · Mathlib · @[simp]",
    "normEDS_three": "theorem · Mathlib · @[simp]",
    "normEDS_two": "theorem · Mathlib · @[simp]",
    "normEDS_zero": "theorem · Mathlib · @[simp]",
    "npowRecAuto": "abbrev · Mathlib · An abbreviation for `npowRec` with an additional typeclass assumption on associativity",
    "one_smul": "theorem · Mathlib · @[to_additive (attr := simp)]",
    "pow_two": "theorem · Mathlib · Note that most of the lemmas about powers of two refer to it as `sq`.",
    "preNormEDS": "def · Mathlib · The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values",
    "preNormEDS'": "def · Mathlib · The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values",
    "preNormEDS_even": "theorem · Mathlib · lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =",
    "preNormEDS_odd": "theorem · Mathlib · lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =",
    "semigroupDvd": "def · Mathlib · There are two possible conventions for divisibility, which coincide in a `CommMonoid`.",
    "smulCommClass_self": "theorem · Mathlib · @[to_additive]",
    "zero_smul": "theorem · Mathlib · @[simp]"
  },
  "search": {
    "AddCommGroup": "An additive commutative group is an additive group with commutative `(+)`. \n\n[Wikidata Q181296](https://www.wikidata.org/wiki/Q181296) class AddCommGroup (G : Type*) extends AddGroup G, AddCommMonoid G",
    "AddCommMonoid": "An additive commutative monoid is an additive monoid with commutative `(+)`.  class AddCommMonoid (M : Type*) extends AddMonoid M, AddCommSemigroup M",
    "AddCommMonoidWithOne": "An `AddCommMonoidWithOne` is an `AddMonoidWithOne` satisfying `a + b = b + a`.  class AddCommMonoidWithOne (R : Type*) extends AddMonoidWithOne R, AddCommMonoid R",
    "AddCon.Quotient": "Defining the quotient by an additive congruence relation of a type with\nan addition.  ",
    "AddEquiv": "`AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition.  structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B",
    "AddGroup": "An `AddGroup` is an `AddMonoid` with a unary `-` satisfying `-a + a = 0`.\n\nThere is also a binary operation `-` such that `a - b = a + -b`,\nwith a default so that `a - b = a + -b` holds by definition.\n\nUse `AddGroup.ofLeftAxioms` or `AddGroup.ofRightAxioms` to define an\nadditive group structure on a type with the minimum proof obligations.\n\n\n[Wikidata Q83478](https://www.wikidata.org/wiki/Q83478) class AddGroup (A : Type*) extends SubNegMonoid A where\n  protected neg_add_cancel : ∀ a : A, -a + a = 0",
    "AddMonoid": "An `AddMonoid` is an `AddSemigroup` with an element `0` such that `0 + a = a + 0 = a`.  class AddMonoid (M : Type*) extends Zero M, Add M, AddSemigroup M, AddZeroClass M, NSMul M where\n  /-- Multiplication by `(0 : ℕ)` gives `0`. -/\n  protected nsmul_zero (x : M) : 0 • x = 0 := by intros; rfl\n  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/\n  protected nsmul_succ (n : ℕ) (x : M) : (n + 1) • x = n • x + x := by intros; rfl",
    "AddMonoidAlgebra.algebra": "The instance `Algebra R R[M]` whenever we have `Algebra R R`.\n\nIn particular this provides the instance `Algebra R R[M]`.  @[to_additive (dont_translate := R A)\n/-- The instance `Algebra R R[M]` whenever we have `Algebra R R`.\n\nIn particular this provides the instance `Algebra R R[M]`. -/]",
    "AddMonoidAlgebra.nonAssocSemiring": " ",
    "AddMonoidHom": "`M →+ N` is the type of functions `M → N` that preserve the `AddZero` structure.\n\n`AddMonoidHom` is also used for group homomorphisms.\n\nWhen possible, instead of parametrizing results over `(f : M →+ N)`,\nyou should parametrize over `(F : Type*) [AddMonoidHomClass F M N] (f : F)`.\n\nWhen you extend this structure, make sure to extend `AddMonoidHomClass`.\n\n\n[Wikidata Q868169](https://www.wikidata.org/wiki/Q868169) structure AddMonoidHom (M : Type*) (N : Type*) [AddZero M] [AddZero N]\n  extends ZeroHom M N, AddHom M N",
    "AddMonoidHom.add": "Given two additive monoid morphisms `f`, `g` to an additive commutative monoid,\n`f + g` is the additive monoid morphism sending `x` to `f x + g x`.  ",
    "AddMonoidHom.ker": "The additive kernel of an `AddMonoid` homomorphism is the `AddSubgroup` of elements\nsuch that `f x = 0`  ",
    "AddMonoidHom.mulRight": "Right multiplication by an element of a (semi)ring is an `AddMonoidHom`  def mulRight (r : R) : R →+ R where\n  toFun a := a * r\n  map_zero' := zero_mul r\n  map_add' _ _ := add_mul _ _ r",
    "AddSubgroup": "An additive subgroup of an additive group `G` is a subset containing 0, closed\nunder addition and additive inverse. \n\n[Wikidata Q466109](https://www.wikidata.org/wiki/Q466109) structure AddSubgroup (G : Type*) [AddGroup G] extends AddSubmonoid G where\n  /-- `G` is closed under negation -/\n  neg_mem' {x} : x ∈ carrier → -x ∈ carrier",
    "AddSubgroup.addSubgroupOf": "For any subgroups `H` and `K`, view `H ⊓ K` as a subgroup of `K`.  ",
    "AddSubgroup.card_bot": " ",
    "AlgEquiv": "An equivalence of algebras (denoted as `A ≃ₐ[R] B`)\nis an equivalence of rings commuting with the actions of scalars.  structure AlgEquiv (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends A ≃ B, A ≃* B, A ≃+ B, A ≃+* B where\n  /-- An equivalence of algebras commutes with the action of scalars. -/\n  protected commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
    "AlgHom": "Defining the homomorphism in the category R-Alg, denoted `A →ₐ[R] B`.  structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends RingHom A B where\n  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
    "AlgHom.funLike": " @[macro_inline]\ninstance funLike : FunLike (A →ₐ[R] B) A B where\n  coe f := f.toFun\n  coe_injective f g h := by\n    rcases f with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    rcases g with ⟨⟨⟨⟨_, _⟩, _⟩, _, _⟩, _⟩\n    congr",
    "AlgHom.restrictScalars": "R ⟶ S induces S-Alg ⥤ R-Alg  def restrictScalars (f : A →ₐ[S] B) : A →ₐ[R] B :=",
    "AlgHom.toRingHom": "Reinterpret an `AlgHom` as a `RingHom`  structure AlgHom (R : Type u) (A : Type v) (B : Type w) [CommSemiring R] [Semiring A] [Semiring B]\n  [Algebra R A] [Algebra R B] extends RingHom A B where\n  commutes' : ∀ r : R, toFun (algebraMap R A r) = algebraMap R B r",
    "Algebra": "An associative unital `R`-algebra is a semiring `A` equipped with a map into its center `R → A`.\n\nSee the implementation notes in this file for discussion of the details of this definition.\n class Algebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] extends SMul R A where\n  /-- Embedding `R →+* A` given by `Algebra` structure. -/\n  algebraMap (R) (A) : R →+* A\n  commutes' : ∀ r x, algebraMap r * x = x * algebraMap r\n  smul_def' : ∀ r x, r • x = algebraMap r * x",
    "Algebra.EssFiniteType": "An `R`-algebra is essentially of finite type if\nit is the localization of an algebra of finite type.\nSee `essFiniteType_iff_exists_subalgebra`.\n\nFor field extensions, this is equivalent to being finitely generated as a field.\nSee `IntermediateField.fg_top_iff`.\n class EssFiniteType : Prop where\n  cond : ∃ s : Finset S,\n    IsLocalization ((IsUnit.submonoid S).comap (algebraMap (adjoin R (s : Set S)) S)) S",
    "Algebra.FormallyEtale": "An `R`-algebra `A` is formally etale if both `Ω[A⁄R]` and `H¹(L_{A/R})` are zero.\nFor the infinitesimal lifting definition, see `FormallyEtale.iff_comp_bijective`.  @[mk_iff, stacks 00UQ]\nclass FormallyEtale : Prop where\n  subsingleton_kaehlerDifferential : Subsingleton Ω[A⁄R]\n  subsingleton_h1Cotangent : Subsingleton (H1Cotangent R A)",
    "Algebra.FormallyEtale.of_isLocalization": " theorem of_isLocalization : FormallyEtale R Rₘ :=",
    "Algebra.FormallyEtale.of_isSeparable": " lemma of_isSeparable [Algebra.IsSeparable K L] : FormallyEtale K L :=",
    "Algebra.IsIntegral": "An algebra is integral if every element of the extension is integral over the base ring.  @[mk_iff] protected class Algebra.IsIntegral : Prop where\n  isIntegral : ∀ x : A, IsIntegral R x",
    "Algebra.IsSeparable": "Typeclass for separable field extension: `K` is a separable field extension of `F` iff\nthe minimal polynomial of every `x : K` is separable. This implies that `K/F` is an algebraic\nextension, because the minimal polynomial of a non-integral element is `0`, which is not\nseparable.\n\nWe define this for general (commutative) rings and only assume `F` and `K` are fields if this\nis needed for a proof.  @[mk_iff isSeparable_def, stacks 09H1 \"third part\"]\nprotected class Algebra.IsSeparable : Prop where\n  isSeparable' : ∀ x : K, IsSeparable F x",
    "Algebra.TensorProduct.algebraMap_apply": " @[simp]\ntheorem algebraMap_apply [SMulCommClass R S A] (r : S) :\n    algebraMap S (A ⊗[R] B) r = (algebraMap S A) r ⊗ₜ 1 :=",
    "Algebra.TensorProduct.includeLeft": "The `R`-algebra morphism `A →ₐ[R] A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.  def includeLeft [SMulCommClass R S A] : A →ₐ[S] A ⊗[R] B :=",
    "Algebra.TensorProduct.includeLeftRingHom": "The ring morphism `A →+* A ⊗[R] B` sending `a` to `a ⊗ₜ 1`.  @[simps!]\ndef includeLeftRingHom : A →+* A ⊗[R] B where\n  __ := (AlgebraTensorModule.mk R R A B).flip 1 |>.toAddMonoidHom\n  map_one' := rfl\n  map_mul' := by simp",
    "Algebra.TensorProduct.includeRight": "The algebra morphism `B →ₐ[R] A ⊗[R] B` sending `b` to `1 ⊗ₜ b`.  def includeRight : B →ₐ[R] A ⊗[R] B where\n  __ := AlgebraTensorModule.mk R R A B 1 |>.toAddMonoidHom\n  map_one' := rfl\n  map_mul' := by simp\n  commutes' r := by simp [algebraMap_eq_smul_one', smul_tmul]",
    "Algebra.TensorProduct.instCommRing": " instance instCommRing : CommRing (A ⊗[R] B) :=",
    "Algebra.TensorProduct.instMul": " instance instMul : Mul (A ⊗[R] B) where\n  mul a b := mul a b",
    "Algebra.TensorProduct.instSemiring": " instance instSemiring : Semiring (A ⊗[R] B) where\n  left_distrib a b c := by simp [HMul.hMul, Mul.mul]\n  right_distrib a b c := by simp [HMul.hMul, Mul.mul]\n  zero_mul a := by simp [HMul.hMul, Mul.mul]\n  mul_zero a := by simp [HMul.hMul, Mul.mul]\n  mul_assoc := Algebra.TensorProduct.mul_assoc\n  one_mul := Algebra.TensorProduct.one_mul\n  mul_one := Algebra.TensorProduct.mul_one\n  natCast_zero := AddMonoidWithOne.natCast_zero\n  natCast_succ := AddMonoidWithOne.natCast_succ",
    "Algebra.TensorProduct.leftAlgebra": " instance leftAlgebra [SMulCommClass R S A] : Algebra S (A ⊗[R] B) :=",
    "Algebra.TensorProduct.lmul'": "`LinearMap.mul'` as an `AlgHom` over the base ring.  def lmul' : S ⊗[R] S →ₐ[R] S :=",
    "Algebra.TensorProduct.lmul''": "`LinearMap.mul'` as an `AlgHom` over the algebra.  def lmul'' : S ⊗[R] S →ₐ[S] S :=",
    "Algebra.TensorProduct.lmul'_apply_tmul": " @[simp]\ntheorem lmul'_apply_tmul (a b : S) : lmul' (S := S) R (a ⊗ₜ[R] b) = a * b :=",
    "Algebra.TensorProduct.mul": "(Implementation detail)\nThe multiplication map on `A ⊗[R] B`,\nas an `R`-bilinear map.\n @[irreducible]\ndef mul : A ⊗[R] B →ₗ[R] A ⊗[R] B →ₗ[R] A ⊗[R] B :=",
    "Algebra.TensorProduct.one_def": " theorem one_def : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ (1 : B) :=",
    "Algebra.TensorProduct.tmul_mul_tmul": " @[simp]\ntheorem tmul_mul_tmul (a₁ a₂ : A) (b₁ b₂ : B) :\n    a₁ ⊗ₜ[R] b₁ * a₂ ⊗ₜ[R] b₂ = (a₁ * a₂) ⊗ₜ[R] (b₁ * b₂) :=",
    "Algebra.adjoin": "The minimal subalgebra that includes `s`.  @[simps -isSimp toSubsemiring]\ndef adjoin (s : Set A) : Subalgebra R A :=",
    "Algebra.algebraMap": "Embedding `R →+* A` given by `Algebra` structure.  ",
    "Algebra.id": "The identity map inducing an `Algebra` structure.  instance (priority := 1100) id : Algebra R R where\n  -- We override `toFun` and `toSMul` because `RingHom.id` is not reducible and cannot\n  -- be made so without a significant performance hit.\n  -- see library note [reducible non-instances].\n  toSMul := instSMulOfMul\n  __ := (RingHom.id R).toAlgebra",
    "Algebra.linearMap": "The canonical ring homomorphism `algebraMap R A : R →+* A` for any `R`-algebra `A`,\npackaged as an `R`-linear map.\n protected def linearMap : R →ₗ[R] A :=",
    "Algebra.lsmul": "The `R`-algebra morphism `A → End (M)` corresponding to the representation of the algebra `A`\non the `B`-module `M`.\n\nThis is a stronger version of `DistribSMul.toLinearMap`, and could also have been\ncalled `Algebra.toModuleEnd`.\n\nThe typeclasses correspond to the situation where the types act on each other as\n```\nR ----→ B\n| ⟍     |\n|   ⟍   |\n↓     ↘ ↓\nA ----→ M\n```\nwhere the diagram commutes, the action by `R` commutes with everything, and the action by `A` and\n`B` on `M` commute.\n\nTypically this is most useful with `B = R` as `Algebra.lsmul R R A : A →ₐ[R] Module.End R M`.\nHowever this can ",
    "Algebra.to_smulCommClass": "This has high priority because it is almost always the right instance when it applies.  instance (priority := high) Algebra.to_smulCommClass {R A} [CommSemiring R] [Semiring A]\n    [Algebra R A] : SMulCommClass R A A :=",
    "Algebra.trace": "The trace of an element `s` of an `R`-algebra is the trace of `(s * ·)`,\nas an `R`-linear map.  @[stacks 0BIF \"Trace\"]\nnoncomputable def trace : S →ₗ[R] R :=",
    "Algebra.trdeg": "The transcendence degree of a commutative algebra `A` over a commutative ring `R` is\ndefined to be the maximal cardinality of an `R`-algebraically independent set in `A`.  @[stacks 030G] def Algebra.trdeg : Cardinal.{v} :=",
    "AlgebraicCurve.ConstantsAreBase": " def ConstantsAreBase (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=",
    "AlgebraicCurve.Divisor": " abbrev Divisor : Type _ :=",
    "AlgebraicCurve.Divisor.IsPrincipal": " def IsPrincipal (D : Divisor K F) : Prop :=",
    "AlgebraicCurve.Divisor.degZero": " def degZero : AddSubgroup (Divisor K F) :=",
    "AlgebraicCurve.Divisor.degree": " def degree : Divisor K F →+ ℤ :=",
    "AlgebraicCurve.Divisor.degree_eq_sum": "The degree of a divisor as the finite sum `∑ v ∈ D.support, D v * deg v`.\nVerbatim from `Theorems/Thm_AlgebraicCurve_Divisor_degree_eq_sum.lean`; the pin's\nproof is the unfolding of the `Finsupp.liftAddHom` that defines `degree`.  theorem degree_eq_sum {K F : Type*} [Field K] [Field F] [Algebra K F] (D : Divisor K F) :\n    Divisor.degree D = ∑ v ∈ D.support, D v * (v.deg : ℤ) :=",
    "AlgebraicCurve.Divisor.degree_single": " @[simp]\ntheorem degree_single (v : Place K F) (n : ℤ) :\n    degree (Finsupp.single v n) = n * v.deg :=",
    "AlgebraicCurve.Divisor.principal": " def principal : AddSubgroup (Divisor K F) where\n  carrier := {D | IsPrincipal D}\n  zero_mem' := ⟨1, one_ne_zero, fun v => by simp⟩\n  add_mem' := by\n    rintro D E ⟨f, hf, hD⟩ ⟨g, hg, hE⟩\n    exact ⟨f * g, mul_ne_zero hf hg, fun v => by\n      rw [Finsupp.add_apply, hD v, hE v, v.ord_mul hf hg]⟩\n  neg_mem' := by\n    rintro D ⟨f, hf, hD⟩\n    exact ⟨f⁻¹, inv_ne_zero hf, fun v => by\n      rw [Finsupp.neg_apply, hD v, v.ord_inv]⟩",
    "AlgebraicCurve.FunctionFieldRiemannRoch": " def FunctionFieldRiemannRoch : Prop :=",
    "AlgebraicCurve.H1": " abbrev H1 (D : Divisor K F) : Type _ :=",
    "AlgebraicCurve.HasCanonicalDivisor": " class HasCanonicalDivisor : Prop where\n  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,\n    ∀ v : Place K F, D v = v.ordDifferential ω",
    "AlgebraicCurve.HasCanonicalDivisor.exists_divisor": " ",
    "AlgebraicCurve.HasCanonicalLocalResidueKStar": " class HasCanonicalLocalResidueKStar where\n\n  dataKStar : ∀ v : Place K F, v.CanonicalLocalResidueDataK",
    "AlgebraicCurve.HasLocalResidue": " class HasLocalResidue : Prop where\n  exists_data : ∀ v : Place K F, Nonempty v.LocalResidueData",
    "AlgebraicCurve.HasPrincipalDivisors": " class HasPrincipalDivisors : Prop where\n  exists_divisor : ∀ f : F, f ≠ 0 → ∃ D : Divisor K F,\n    (∀ v : Place K F, D v = v.ord f) ∧ Divisor.degree D = 0",
    "AlgebraicCurve.HasSeparableResidue": " class HasSeparableResidue : Prop where\n  trace_ne_zero : ∀ v : Place K F, (Algebra.trace K v.ResidueField : _ →ₗ[K] K) ≠ 0",
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": " instance HasSeparableResidue.of_perfectField [PerfectField K]\n    [∀ v : Place K F, v.FiniteResidue] : HasSeparableResidue K F :=",
    "AlgebraicCurve.HasWeilCanonicalDivisor": " def HasWeilCanonicalDivisor : Prop :=",
    "AlgebraicCurve.IndexOfSpecialtyFinite": " def IndexOfSpecialtyFinite : Prop :=",
    "AlgebraicCurve.IsCurveOver": " class IsCurveOver : Prop extends HasPrincipalDivisors K F where\n\n  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField\n\n  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1",
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed": " theorem deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :\n    v.deg = 1 :=",
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental": " theorem exists_separating_transcendental {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]\n    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :\n    ∃ t : F, Transcendental K t ∧ FiniteDimensional K⟮t⟯ F ∧ Algebra.IsSeparable K⟮t⟯ F :=",
    "AlgebraicCurve.IsCurveOver.finrank_kaehler": " theorem finrank_kaehler [h : IsCurveOver K F] : Module.finrank F Ω[F⁄K] = 1 :=",
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed": " theorem forall_deg_eq_one_of_isAlgClosed [IsAlgClosed K] [IsCurveOver K F] :\n    ∀ w : Place K F, w.deg = 1 :=",
    "AlgebraicCurve.IsCurveOver.instFreeKaehler": " instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=",
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler": " instance instNontrivialKaehler [IsCurveOver K F] : Nontrivial Ω[F⁄K] :=",
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one": " ",
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": "Pin row #234.  theorem of_finiteResidue_of_kaehlerRankOne\n    [HasPrincipalDivisors K F] [∀ v : Place K F, v.FiniteResidue]\n    (hΩ : KaehlerRankOne K F) : IsCurveOver K F where\n  finiteResidue v := Place.FiniteResidue.finite (v := v)\n  kaehler_free_rank_one := hΩ",
    "AlgebraicCurve.IsCurveOver.one_le_trdeg": " theorem one_le_trdeg [PerfectField K] [IsCurveOver K F] :\n    1 ≤ Algebra.trdeg K F :=",
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField": " theorem trdeg_eq_one_of_perfectField [PerfectField K] [Algebra.EssFiniteType K F]\n    [IsCurveOver K F] : Algebra.trdeg K F = 1 :=",
    "AlgebraicCurve.IsCurveOver.trdeg_le_one": " theorem trdeg_le_one [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F] :\n    Algebra.trdeg K F ≤ 1 :=",
    "AlgebraicCurve.KaehlerRankOne": "Pin row #233.  def KaehlerRankOne : Prop :=",
    "AlgebraicCurve.LSpace": " abbrev LSpace (D : Divisor K F) : Submodule K F :=",
    "AlgebraicCurve.Pic": " abbrev Pic : Type _ :=",
    "AlgebraicCurve.Pic0": " abbrev Pic0 : Type _ :=",
    "AlgebraicCurve.Place": " structure Place where\n\n  toValuationSubring : ValuationSubring F\n\n  algebraMap_mem' : ∀ a : K, algebraMap K F a ∈ toValuationSubring\n\n  ne_top' : toValuationSubring ≠ ⊤\n\n  isPrincipalIdealRing' : IsPrincipalIdealRing toValuationSubring",
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK": " structure CanonicalLocalResidueDataK extends v.LocalResidueData where\n\n  res_higherPoleMonomial : ∀ (n : ℕ), 1 ≤ n → res (v.uniformizer ^ (n + 1))⁻¹ = 0",
    "AlgebraicCurve.Place.DCoordGenerates": " class DCoordGenerates : Prop where\n  span_eq_top : Submodule.span F {v.dCoord} = ⊤",
    "AlgebraicCurve.Place.FiniteResidue": " class FiniteResidue : Prop where\n  finite : Module.Finite K v.ResidueField",
    "AlgebraicCurve.Place.LocalResidueData.res": " ",
    "AlgebraicCurve.Place.ResidueField": " abbrev ResidueField : Type _ :=",
    "AlgebraicCurve.Place.adicValuation": " def adicValuation : Valuation F ℤᵐ⁰ :=",
    "AlgebraicCurve.Place.dCoord": " def dCoord : Ω[F⁄K] :=",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": " theorem Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField\n    [PerfectField K] [∀ v : Place K F, v.FiniteResidue]\n    (hfin : ValSubringKaehlerFinite K F) (v : Place K F) :\n    v.DCoordGenerates :=",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": " theorem Place.dCoordGenerates_of_valSubringKaehlerSpanTop\n    (hspan : ValSubringKaehlerSpanTop K F) (v : Place K F) :\n    v.DCoordGenerates :=",
    "AlgebraicCurve.Place.dCoord_ne_zero": " theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 :=",
    "AlgebraicCurve.Place.deg": " def deg : ℕ :=",
    "AlgebraicCurve.Place.differentialCoeff": " def differentialCoeff (ω : Ω[F⁄K]) : F :=",
    "AlgebraicCurve.Place.differentialCoeff_dCoord": " @[simp]\ntheorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :\n    v.differentialCoeff v.dCoord = 1 :=",
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord": " theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :\n    v.differentialCoeff ω • v.dCoord = ω :=",
    "AlgebraicCurve.Place.differentialCoeff_unique": " theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]\n    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f :=",
    "AlgebraicCurve.Place.differentialCoeff_zero": " @[simp]\ntheorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :\n    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=",
    "AlgebraicCurve.Place.exists_eq_smul_dCoord": " theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :\n    ∃ f : F, ω = f • v.dCoord :=",
    "AlgebraicCurve.Place.exists_unit_mul_zpow": " theorem exists_unit_mul_zpow {f : F} (hf : f ≠ 0) {π : v.toValuationSubring}\n    (hπ : Irreducible π) :\n    ∃ u : v.toValuationSubringˣ,\n      f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (v.ord f)) :=",
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord": " theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :\n    v.ordDifferential v.dCoord = 0 :=",
    "AlgebraicCurve.Place.heightOneSpectrum": " def heightOneSpectrum : HeightOneSpectrum v.toValuationSubring :=",
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": " theorem mem_iff_ord_nonneg {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)\n    {f : F} (hf : f ≠ 0) :\n    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=",
    "AlgebraicCurve.Place.min_ord_le_ord_add": "Pin `Place.min_ord_le_ord_add`\n(`S_WeierstrassCurve_Affine_hasPrincipalDivisors_functionField.lean:1070`).  theorem min_ord_le_ord_add {f g : F} (hfg : f + g ≠ 0) :\n    min (v.ord f) (v.ord g) ≤ v.ord (f + g) :=",
    "AlgebraicCurve.Place.ord": " def ord (f : F) : ℤ :=",
    "AlgebraicCurve.Place.ordDifferential": " def ordDifferential (ω : Ω[F⁄K]) : ℤ :=",
    "AlgebraicCurve.Place.ordDifferential_smul": " theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]\n    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :\n    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω :=",
    "AlgebraicCurve.Place.ord_algebraMap": " theorem ord_algebraMap {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) (c : K) :\n    v.ord (algebraMap K F c) = 0 :=",
    "AlgebraicCurve.Place.ord_coe_unit": " theorem ord_coe_unit (u : v.toValuationSubringˣ) :\n    v.ord ((u : v.toValuationSubring) : F) = 0 :=",
    "AlgebraicCurve.Place.ord_inv": " theorem ord_inv (f : F) : v.ord f⁻¹ = -v.ord f :=",
    "AlgebraicCurve.Place.ord_mul": " theorem ord_mul {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) :\n    v.ord (f * g) = v.ord f + v.ord g :=",
    "AlgebraicCurve.Place.ord_uniformizer": " theorem ord_uniformizer : v.ord v.uniformizer = 1 :=",
    "AlgebraicCurve.Place.ord_uniformizerSubring": " theorem ord_uniformizerSubring : v.ord (uniformizerSubring v : F) = 1 :=",
    "AlgebraicCurve.Place.ord_zero": " @[simp]\ntheorem ord_zero : v.ord (0 : F) = 0 :=",
    "AlgebraicCurve.Place.ord_zpow": " theorem ord_zpow (f : F) (n : ℤ) : v.ord (f ^ n) = n * v.ord f :=",
    "AlgebraicCurve.Place.uniformizer": " def uniformizer : F :=",
    "AlgebraicCurve.Place.uniformizerSubring": "The uniformizer as an element of the valuation subring: the single home of the\n`Classical.choose`, whose coercion to `F` is `Place.uniformizer`. Everything that needs\nthe uniformizer *inside* the valuation subring reads it from here — the cotangent and\nresidue engines of `Canonical/HasCanonicalDivisor.lean` and the residue-instance layer\nalike.  noncomputable def uniformizerSubring : v.toValuationSubring :=",
    "AlgebraicCurve.Place.uniformizer_ne_zero": " theorem uniformizer_ne_zero : v.uniformizer ≠ 0 :=",
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": "Pin row #235.  theorem isCurveOver_of_kaehlerRankOne (hΩ : KaehlerRankOne K (RatFunc K)) :\n    IsCurveOver K (RatFunc K) :=",
    "AlgebraicCurve.ResiduePairingSurjective": " def ResiduePairingSurjective : Prop :=",
    "AlgebraicCurve.ResidueTheoremK": " def ResidueTheoremK : Prop :=",
    "AlgebraicCurve.RiemannGenusBounded": " def RiemannGenusBounded : Prop :=",
    "AlgebraicCurve.RiemannGenusReached": " def RiemannGenusReached (γ : ℤ) : Prop :=",
    "AlgebraicCurve.RiemannGenusReachedAt": " structure RiemannGenusReachedAt (γ : ℤ) (D₀ : Divisor K F) : Prop where\n  finite : FiniteDimensional K (LSpace D₀)\n  eq : Divisor.degree D₀ - (ell D₀ : ℤ) = γ - 1\n  isMax : ∀ D : Divisor K F, Divisor.degree D - (ell D : ℤ) ≤ γ - 1",
    "AlgebraicCurve.RiemannIndexFormula": " def RiemannIndexFormula : Prop :=",
    "AlgebraicCurve.RiemannInequality": " def RiemannInequality : Prop :=",
    "AlgebraicCurve.StichtenothGenusExists": " def StichtenothGenusExists : Prop :=",
    "AlgebraicCurve.ValSubringKaehlerFinite": " def ValSubringKaehlerFinite : Prop :=",
    "AlgebraicCurve.ValSubringKaehlerSpanTop": " def ValSubringKaehlerSpanTop : Prop :=",
    "AlgebraicCurve.WeilDifferentialRankOne": " def WeilDifferentialRankOne [HasPrincipalDivisors K F] : Prop :=",
    "AlgebraicCurve.WeilDuality": " def WeilDuality : Prop :=",
    "AlgebraicCurve.WeilDualityAdelic": " def WeilDualityAdelic : Prop :=",
    "AlgebraicCurve.WeilOmegaEllAgrees": " def WeilOmegaEllAgrees : Prop :=",
    "AlgebraicCurve.adeleBdd": " def adeleBdd (D : Divisor K F) : Submodule K (Place K F → F) where\n  carrier := {α | ∀ v : Place K F, v.adicValuation (α v) ≤ WithZero.exp (D v)}\n  add_mem' := fun {α β} hα hβ v =>\n    (v.adicValuation.map_add (α v) (β v)).trans (max_le (hα v) (hβ v))\n  zero_mem' := fun v => by rw [Pi.zero_apply, Valuation.map_zero]; exact zero_le\n  smul_mem' := fun c α hα v => by\n    rw [Pi.smul_apply, Algebra.smul_def, Valuation.map_mul]\n    calc v.adicValuation (algebraMap K F c) * v.adicValuation (α v)\n        ≤ 1 * v.adicValuation (α v) := by gcongr; exact v.adicValuation_algebraMap_le_one c\n      _ = v.",
    "AlgebraicCurve.adeleBddPrincipal": " abbrev adeleBddPrincipal (D : Divisor K F) : Submodule K (adeleSpace K F) :=",
    "AlgebraicCurve.adeleSingle": " def adeleSingle (v : Place K F) (g : F) : adeleSpace K F :=",
    "AlgebraicCurve.adeleSpace": " def adeleSpace : Submodule K (Place K F → F) :=",
    "AlgebraicCurve.canonicalClass": " def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]\n    [HasCanonicalDivisor (K := K) (F := F)] : Pic K F :=",
    "AlgebraicCurve.canonicalDivisorOf": " def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=",
    "AlgebraicCurve.canonicalDivisorOf_apply": " theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :\n    canonicalDivisorOf hω v = v.ordDifferential ω :=",
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one": "The pin's `AlgebraicCurve.constantsAreBase_of_deg_eq_one` (pin 2887).  theorem constantsAreBase_of_deg_eq_one [HasPrincipalDivisors K F]\n    (v₀ : Place K F) (hdeg : v₀.deg = 1) :\n    ConstantsAreBase K F :=",
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed": "Constants are the base field over an algebraically closed constant field (pin 5931).  theorem AlgebraicCurve.constantsAreBase_of_isAlgClosed (K F : Type*) [Field K] [Field F] [Algebra K F]\n    [DecidableEq (RatFunc K)] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]\n    [FiniteDimensional (RatFunc K) F] [Algebra.IsSeparable (RatFunc K) F]\n    [IsAlgClosed K] [IsCurveOver K F] :\n    ConstantsAreBase K F :=",
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula": "The pin's `AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula`\n(pin 3747): Riemann's inequality from the index formula.  theorem degree_add_one_sub_genus_le_ell_of_riemannIndexFormula\n    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]\n    (hRI : RiemannIndexFormula K F) (D : Divisor K F) :\n    Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ) :=",
    "AlgebraicCurve.diagonalHom": " def diagonalHom : F →ₗ[K] (Place K F → F) where\n  toFun f := fun _ => f\n  map_add' _ _ := rfl\n  map_smul' _ _ := rfl",
    "AlgebraicCurve.diagonal_mem_adeleSpace": " theorem diagonal_mem_adeleSpace [HasPrincipalDivisors K F] (f : F) :\n    diagonalHom K F f ∈ adeleSpace K F :=",
    "AlgebraicCurve.ell": " abbrev ell (D : Divisor K F) : ℕ :=",
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch": " theorem AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch\n    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]\n    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]\n    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :\n    (ell (canonicalDivisorOf hω) : ℤ) = (genus K F : ℤ) :=",
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty": " theorem ell_sub_le_indexOfSpecialty [HasPrincipalDivisors K F] (W D : Divisor K F)\n    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)\n    [Module.Finite K (omegaSpace (K := K) (F := F) D)] :\n    ell (W - D) ≤ indexOfSpecialty D :=",
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase": " theorem ell_zero_eq_one_of_constantsAreBase (h : ConstantsAreBase K F) :\n    ell (0 : Divisor K F) = 1 :=",
    "AlgebraicCurve.exists_weilCanonical_riemannRoch": " theorem exists_weilCanonical_riemannRoch\n    (K F : Type*) [Field K] [PerfectField K] [Field F] [Algebra K F]\n    [IsCurveOver K F] [Algebra.EssFiniteType K F]\n    (hC : ConstantsAreBase K F) :\n    ∃ W : Divisor K F, ∀ D : Divisor K F,\n      (ell D : ℤ) - (ell (W - D) : ℤ) =\n        Divisor.degree D + 1 - (genusFF K F : ℤ) :=",
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell": " theorem finrank_adeleBdd_inf_global_eq_ell [Nonempty (Place K F)] (D : Divisor K F) :\n    Module.finrank K (adeleBdd D ⊓ globalSub K F : Submodule K (Place K F → F)) = ell D :=",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating": " theorem finrank_kaehler_eq_card_of_separating {s : Finset F}\n    (hs : AlgebraicIndependent K ((↑) : s → F))\n    [Algebra.IsSeparable (IntermediateField.adjoin K (Set.range ((↑) : s → F))) F] :\n    Module.finrank F Ω[F⁄K] = s.card :=",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'": " theorem finrank_kaehler_eq_card_of_separating' {s : Finset F}\n    (hs : AlgebraicIndependent K ((↑) : s → F))\n    [hsep : Algebra.IsSeparable (IntermediateField.adjoin K (s : Set F)) F] :\n    Module.finrank F Ω[F⁄K] = s.card :=",
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty": " theorem finrank_omegaSpace_eq_indexOfSpecialty (D : Divisor K F) :\n    Module.finrank K (omegaSpace D) = indexOfSpecialty D :=",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed": " theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed\n    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]\n    [Field F] [Algebra K F]\n    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]\n    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]\n    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]\n    [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue]\n    [Nontrivial Ω[F⁄K]]\n    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]\n    [∀ u : Place K (RatFunc K), u.FiniteResidue]\n    [HasCanonicalLocalResidueKStar K F]\n    ",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver": " theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver\n    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]\n    [Field F] [Algebra K F]\n    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]\n    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]\n    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]\n    [∀ w : Place K F, w.FiniteResidue]\n    [Nontrivial Ω[F⁄K]]\n    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]\n    [∀ u : Place K (RatFunc K), u.FiniteResidue]\n    [HasPrincipalDivisors K F] [Algebra.IsSeparable",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental": "**Riemann–Roch over an algebraically closed constant field, from a transcendental\ngenerator.**  Verbatim from\n`Theorems/Thm_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental.lean`;\nthe proof is `S_AlgebraicCurve_functionFieldRiemannRoch_of_isAlgClosed_of_transcendental.solution`.  theorem AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental\n    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]\n    {x : F} (htr : Transcendental K x)\n    (hfd : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :\n    AlgebraicCurve.FunctionFie",
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed": " theorem AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed\n    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]\n    [Field F] [Algebra K F]\n    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]\n    [∀ w : AlgebraicCurve.Place K F, w.DCoordGenerates]\n    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]\n    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]\n    [AlgebraicCurve.HasLocalResidue K F]\n    [∀ w : AlgebraicCurve.Place K F, w.FiniteResidue]\n    [Nontrivial Ω[F⁄K]]\n    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsC",
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality": " theorem functionFieldRiemannRoch_of_riemann_and_duality\n    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F :=",
    "AlgebraicCurve.genus": " def genus (K F : Type*) [Field K] [Field F] [Algebra K F]\n    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=",
    "AlgebraicCurve.genusFF": " def genusFF : ℕ :=",
    "AlgebraicCurve.genus_eq_degree_div": "The pin's `AlgebraicCurve.genus_eq_degree_div` (pin 4042).  theorem genus_eq_degree_div :\n    ∃ (ω₀ : Ω[F⁄K]) (hω₀ : ω₀ ≠ 0),\n      genus K F = (Divisor.degree (canonicalDivisorOf hω₀) + 2).toNat / 2 :=",
    "AlgebraicCurve.genus_eq_genusFF": " theorem AlgebraicCurve.genus_eq_genusFF\n    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]\n    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]\n    (hRR : FunctionFieldRiemannRoch K F) (hWDA : WeilDualityAdelic K F)\n    (hC : ConstantsAreBase K F) :\n    genus K F = genusFF K F :=",
    "AlgebraicCurve.globalSub": " def globalSub : Submodule K (Place K F → F) :=",
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": " theorem hasCanonicalDivisor_of_isCurveOver\n    {K F : Type*} [Field K] [Field F] [Algebra K F]\n    [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :\n    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=",
    "AlgebraicCurve.indexOfSpecialty": " def indexOfSpecialty (D : Divisor K F) : ℕ :=",
    "AlgebraicCurve.indexOfSpecialty_eq": " theorem indexOfSpecialty_eq (D : Divisor K F) :\n    indexOfSpecialty D = Module.finrank K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=",
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1": "The `H¹` identification: the adelic index of `D` is the `K`-dimension of the\nrepartition quotient `H1 D`.  theorem indexOfSpecialty_eq_finrank_H1 {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (D : Divisor K F) :\n    indexOfSpecialty D = Module.finrank K (H1 D) :=",
    "AlgebraicCurve.kaehlerAdjoinBasis": " def kaehlerAdjoinBasis (hv : AlgebraicIndependent K v) :\n    Basis ι (IntermediateField.adjoin K (Set.range v))\n      Ω[(IntermediateField.adjoin K (Set.range v))⁄K] :=",
    "AlgebraicCurve.kaehlerRankOne_of_transcendental": "**The Kähler module of a function field is free of rank one.**\nVerbatim from `Theorems/Thm_AlgebraicCurve_kaehlerRankOne_of_transcendental.lean`.  theorem kaehlerRankOne_of_transcendental {K F : Type*} [Field K] [Field F] [Algebra K F]\n    {x : F} (htr : Transcendental K x)\n    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F) :\n    Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1 :=",
    "AlgebraicCurve.kaehlerRankOne_ratFunc": " theorem kaehlerRankOne_ratFunc : KaehlerRankOne K (RatFunc K) :=",
    "AlgebraicCurve.lSpace_mono": " theorem lSpace_mono (hDE : D ≤ E) : LSpace D ≤ LSpace E :=",
    "AlgebraicCurve.map_diagonal_lSpace": " theorem map_diagonal_lSpace (D : Divisor K F) :\n    (LSpace D).map (diagonalHom K F) = adeleBdd D ⊓ globalSub K F :=",
    "AlgebraicCurve.mem_adeleSpace_iff": " theorem mem_adeleSpace_iff {α : Place K F → F} :\n    α ∈ adeleSpace K F ↔ ∃ D : Divisor K F, α ∈ adeleBdd D :=",
    "AlgebraicCurve.mem_lSpace_iff": " theorem mem_lSpace_iff {f : F} :\n    f ∈ LSpace D ↔ ∀ v : Place K F, v.adicValuation f ≤ WithZero.exp (D v) :=",
    "AlgebraicCurve.mem_lSpace_iff_ord": " theorem mem_lSpace_iff_ord {f : F} :\n    f ∈ LSpace D ↔ f = 0 ∨ ∀ v : Place K F, -D v ≤ v.ord f :=",
    "AlgebraicCurve.omegaSpace": " def omegaSpace (D : Divisor K F) : Submodule K (Module.Dual K (adeleSpace K F)) :=",
    "AlgebraicCurve.omegaSpaceEquivIndexDual": " def omegaSpaceEquivIndexDual (D : Divisor K F) :\n    omegaSpace D ≃ₗ[K] Module.Dual K (adeleSpace K F ⧸ adeleBddPrincipal K F D) :=",
    "AlgebraicCurve.one_mem_lSpace_zero": " theorem one_mem_lSpace_zero : (1 : F) ∈ LSpace (0 : Divisor K F) :=",
    "AlgebraicCurve.principalRepartitions": " def principalRepartitions : Submodule K ↥(repartitions K F) :=",
    "AlgebraicCurve.repartitions": " def repartitions : Subalgebra F (Place K F → F) :=",
    "AlgebraicCurve.repartitionsOf": " def repartitionsOf (D : Divisor K F) : Submodule K ↥(repartitions K F) where\n  carrier :=\n    {α | ∀ v : Place K F, v.adicValuation ((α : Place K F → F) v) ≤ exp (D v)}\n  zero_mem' := by\n    intro v\n    show v.adicValuation (0 : F) ≤ exp (D v)\n    simp\n  add_mem' := by\n    intro α β hα hβ v\n    exact (Valuation.map_add _ _ _).trans (max_le (hα v) (hβ v))\n  smul_mem' := by\n    intro c α hα v\n    show v.adicValuation (c • (α : Place K F → F) v) ≤ exp (D v)\n    rw [Algebra.smul_def, map_mul]\n    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hα v)",
    "AlgebraicCurve.residuePairing": " def residuePairing [HasPrincipalDivisors K F] (W D : Divisor K F)\n    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) :\n    LSpace (W - D) →ₗ[K] omegaSpace D where\n  toFun g := ⟨weilSmul K F (g : F) φ, weilSmul_mem_omegaSpace_of_mem_lSpace hφ g.2⟩\n  map_add' g₁ g₂ := by\n    refine Subtype.ext ?_\n    show weilSmul K F ((g₁ : F) + (g₂ : F)) φ\n      = weilSmul K F (g₁ : F) φ + weilSmul K F (g₂ : F) φ\n    ext α; simp only [weilSmul_apply, LinearMap.add_apply]\n    rw [← map_add]; congr 1\n    exact Subtype.ext (funext fun v => by simp [add_mul])\n  map_smul' c g := by\n    refine Subtype",
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula": "The pin's `AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula`\n(pin 4726).  theorem residuePairingSurjective_of_riemannIndexFormula\n    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [Nonempty (Place K F)]\n    (hRI : RiemannIndexFormula K F) : ResiduePairingSurjective K F :=",
    "AlgebraicCurve.residuePairing_injective": " theorem residuePairing_injective [HasPrincipalDivisors K F] (W D : Divisor K F)\n    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0) :\n    Function.Injective (residuePairing K F W D hφ) :=",
    "AlgebraicCurve.residuePairing_surjective": "The pin's `AlgebraicCurve.residuePairing_surjective` (pin 4682).  theorem residuePairing_surjective [HasPrincipalDivisors K F]\n    (hRk1 : WeilDifferentialRankOne K F) (W D : Divisor K F)\n    {φ : Module.Dual K (adeleSpace K F)} (hφ : φ ∈ omegaSpace W) (hφ0 : φ ≠ 0)\n    (hWmax : ∀ E : Divisor K F, φ ∈ omegaSpace E → E ≤ W) :\n    Function.Surjective (residuePairing K F W D hφ) :=",
    "AlgebraicCurve.riemannIndexFormula_of_genusReached": "The pin's `AlgebraicCurve.riemannIndexFormula_of_genusReached` (pin 3592).  theorem riemannIndexFormula_of_genusReached\n    (hg : ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],\n      RiemannGenusReached K F (genus K F)) :\n    RiemannIndexFormula K F :=",
    "AlgebraicCurve.riemannRochSpace": " def riemannRochSpace (D : Divisor K F) : Submodule K F where\n  carrier := {f | ∀ v : Place K F, v.adicValuation f ≤ exp (D v)}\n  zero_mem' := by\n    intro v\n    simp\n  add_mem' := by\n    intro f g hf hg v\n    exact (Valuation.map_add _ _ _).trans (max_le (hf v) (hg v))\n  smul_mem' := by\n    intro c f hf v\n    show v.adicValuation (c • f) ≤ exp (D v)\n    rw [Algebra.smul_def, map_mul]\n    exact (mul_le_of_le_one_left' (v.adicValuation_algebraMap_le_one c)).trans (hf v)",
    "AlgebraicCurve.stichtenothGenus_nonneg": "The pin's `AlgebraicCurve.stichtenothGenus_nonneg` (pin 4031).  theorem stichtenothGenus_nonneg\n    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)\n    (hC : ConstantsAreBase K F) : 0 ≤ γ :=",
    "AlgebraicCurve.weilDifferentialModule": " def weilDifferentialModule : Submodule K (Module.Dual K (adeleSpace K F)) :=",
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic": " theorem weilDuality_of_riemannIndex_of_adelic\n    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :\n    WeilDuality K F :=",
    "AlgebraicCurve.weilOfKaehlerK": " def weilOfKaehlerK (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Module.Dual K (adeleSpace K F) where\n  toFun α := ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (α : Place K F → F) v\n  map_add' α β := by\n    have hsupα := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω α.2\n    have hsupβ := kaehlerResidueTermKFam_support_finite_of_adeleSpace Rfam hω β.2\n    rw [← finsum_add_distrib hsupα hsupβ]\n    refine finsum_congr fun v => ?_\n    simp only [kaehlerResidueTermKFam_apply]\n    rw [Submodule.coe_add, Pi.add_apply, add_mul, map_add, map_add]\n  map_smu",
    "AlgebraicCurve.weilSmul": " def weilSmul [HasPrincipalDivisors K F] (f : F) :\n    Module.Dual K (adeleSpace K F) →ₗ[K] Module.Dual K (adeleSpace K F) :=",
    "AlgebraicIndependent": "`AlgebraicIndependent R x` states the family of elements `x`\nis algebraically independent over `R`, meaning that the canonical\nmap out of the multivariable polynomial ring is injective.  @[stacks 030E \"(1)\"] def AlgebraicIndependent : Prop :=",
    "AlgebraicIndependent.aevalEquiv": "Canonical isomorphism between polynomials and the subalgebra generated by\nalgebraically independent elements.  @[simps! apply_coe]\ndef aevalEquiv : MvPolynomial ι R ≃ₐ[R] Algebra.adjoin R (range x) :=",
    "Bot": "Typeclass for the `⊥` (`\\bot`) notation  @[notation_class, ext, to_dual]\nclass Bot (α : Type*) where\n  /-- The bot (`⊥`, `\\bot`) element -/\n  bot : α",
    "Bot.bot": "The bot (`⊥`, `\\bot`) element \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `⊥` in identifiers is `bot`. ",
    "Cardinal": "`Cardinal.{u}` is the type of cardinal numbers in `Type u`,\ndefined as the quotient of `Type u` by existence of an equivalence\n(a bijection with explicit inverse).  @[pp_with_univ, wikidata Q163875]\ndef Cardinal : Type (u + 1) :=",
    "Cardinal.mk": "The cardinal number of a type  def mk : Type u → Cardinal :=",
    "Classical.choose": "Given that there exists an element satisfying `p`, returns one such element.\n\nThis is a straightforward consequence of, and equivalent to, `Classical.choice`.\n\nSee also `choose_spec`, which asserts that the returned value has property `p`.\n noncomputable def choose {α : Sort u} {p : α → Prop} (h : ∃ x, p x) : α :=",
    "Classical.decEq": "Any type `α` has decidable equality classically.  @[instance_reducible]\nnoncomputable def decEq (α : Sort*) : DecidableEq α :=",
    "Classical.indefiniteDescription": " noncomputable def indefiniteDescription {α : Sort u} (p : α → Prop) (h : ∃ x, p x) : {x // p x} :=",
    "Classical.propDecidable": "All propositions are `Decidable`.  noncomputable scoped instance (priority := low) propDecidable (a : Prop) : Decidable a :=",
    "CommRing": "A commutative ring is a ring with commutative multiplication.  @[wikidata Q858656]\nclass CommRing (α : Type u) extends Ring α, CommMonoid α",
    "CommSemiring": "A commutative semiring is a semiring with commutative multiplication.  class CommSemiring (R : Type u) extends Semiring R, CommMonoid R",
    "Derivation": "`D : Derivation R A M` is an `R`-linear map from `A` to `M` that satisfies the `leibniz`\nequality. We also require that `D 1 = 0`. See `Derivation.mk'` for a constructor that deduces this\nassumption from the Leibniz rule when `M` is cancellative.\n\nTODO: update this when bimodules are defined.  structure Derivation (R : Type*) (A : Type*) (M : Type*)\n    [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Algebra R A] [Module A M] [Module R M]\n    extends A →ₗ[R] M where\n  protected map_one_eq_zero' : toLinearMap 1 = 0\n  protected leibniz' (a b : A) : toLinearMap (a * b) = a • toLinearMap b + ",
    "Derivation.leibniz": " @[simp]\ntheorem leibniz : D (a * b) = a • D b + b • D a :=",
    "Derivation.leibniz_pow": " @[simp]\ntheorem leibniz_pow (n : ℕ) : D (a ^ n) = n • a ^ (n - 1) • D a :=",
    "Derivation.liftKaehlerDifferential": "The linear map from `Ω[S⁄R]`, associated with a derivation.  def Derivation.liftKaehlerDifferential (D : Derivation R S M) : Ω[S⁄R] →ₗ[S] M :=",
    "Derivation.liftKaehlerDifferential_comp": " theorem Derivation.liftKaehlerDifferential_comp (D : Derivation R S M) :\n    D.liftKaehlerDifferential.compDer (KaehlerDifferential.D R S) = D :=",
    "Derivation.liftKaehlerDifferential_comp_D": " @[simp]\ntheorem Derivation.liftKaehlerDifferential_comp_D (D' : Derivation R S M) (x : S) :\n    D'.liftKaehlerDifferential (KaehlerDifferential.D R S x) = D' x :=",
    "Derivation.llcomp": "The composition of a derivation with a linear map as a bilinear map  @[simps]\ndef llcomp : (M →ₗ[A] N) →ₗ[A] Derivation R A M →ₗ[A] Derivation R A N where\n  toFun f := f.compDer\n  map_add' f₁ f₂ := by ext; rfl\n  map_smul' r D := by ext; rfl",
    "Derivation.map_algebraMap": " @[simp]\ntheorem map_algebraMap : D (algebraMap R A r) = 0 :=",
    "Derivation.tensorProductTo": "For an `R`-derivation `S → M`, this is the map `S ⊗[R] S →ₗ[S] M` sending `s ⊗ₜ t ↦ s • D t`.  def Derivation.tensorProductTo (D : Derivation R S M) : S ⊗[R] S →ₗ[S] M :=",
    "DivisionRing": "A `DivisionRing` is a `Ring` with multiplicative inverses for nonzero elements.\n\nAn instance of `DivisionRing K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.\nThose two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need\nto control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).\nSee also note [forgetful inheritance]. Similarly, there are maps `nnratCast ℚ≥0 → K` and\n`nnqsmul : ℚ≥0 → K → K` to implement the `DivisionSemiring K → Algebra ℚ≥0 K` instance.\n\nIf the division ring has positive characteristic `p`, o",
    "Dvd.dvd": "Divisibility. `a ∣ b` (typed as `\\|`) means that there is some `c` such that `b = a * c`. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `∣` in identifiers is `dvd`. ",
    "Equiv": "`α ≃ β` is the type of functions from `α → β` with a two-sided inverse.  structure Equiv (α β : Sort*) where\n  /-- The forward map of an equivalence.\n\n  Do NOT use directly. Use the coercion instead. -/\n  protected toFun : α → β\n  /-- The backward map of an equivalence.\n\n  Do NOT use `e.invFun` directly. Use the coercion of `e.symm` instead. -/\n  protected invFun : β → α\n  protected left_inv : LeftInverse invFun toFun := by intro; first | rfl | ext <;> rfl\n  protected right_inv : RightInverse invFun toFun := by intro; first | rfl | ext <;> rfl",
    "Equiv.punitProd": "`PUnit` is a left identity for type product up to an equivalence.  @[simps! (attr := grind =)]\ndef punitProd (α) : PUnit × α ≃ α :=",
    "Equiv.trans": "Composition of equivalences `e₁ : α ≃ β` and `e₂ : β ≃ γ`.  @[trans]\nprotected def trans (e₁ : α ≃ β) (e₂ : β ≃ γ) : α ≃ γ :=",
    "Even": "An element `a` of a type `α` with addition satisfies `Even a` if `a = r + r`,\nfor some `r : α`.  ",
    "Exists.choose": "Extract an element from an existential statement, using `Classical.choose`.  -- This enables projection notation.\n@[reducible] noncomputable def Exists.choose {p : α → Prop} (P : ∃ a, p a) : α :=",
    "ExistsUnique": "For `p : α → Prop`, `ExistsUnique p` means that there exists a unique `x : α` with `p x`.  def ExistsUnique (p : α → Prop) :=",
    "FLTForHuman.Elliptic.EvenRec": "The even recursion satisfied by a normalised EDS, FLT's `EvenRec`.  def EvenRec (m : ℤ) : Prop :=",
    "FLTForHuman.Elliptic.HaveSameParity₄": "FLT's `HaveSameParity₄`, phrased with `negOnePow`.  def HaveSameParity₄ : Prop :=",
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf": " theorem rel₄_transf :\n    rel₄ W (avg₄ a b c d - d) (avg₄ a b c d - c) (avg₄ a b c d - b) |avg₄ a b c d - a| =\n      rel₄ W a b c d :=",
    "FLTForHuman.Elliptic.OddRec": "The odd recursion satisfied by a normalised EDS, FLT's `OddRec`.  def OddRec (m : ℤ) : Prop :=",
    "FLTForHuman.Elliptic.Param": "The three parameters of a normalised EDS, as indeterminates.  inductive Param : Type\n  | B : Param\n  | C : Param\n  | D : Param",
    "FLTForHuman.Elliptic.Rel₃": "The elliptic-sequence relation, FLT's `Rel₃`.  def Rel₃ (W : ℤ → R) (m n r : ℤ) : Prop :=",
    "FLTForHuman.Elliptic.Rel₄OfValid": "FLT's `Rel₄OfValid`: the relator vanishes on same-parity, strictly decreasing\nnon-negative quadruples.  def Rel₄OfValid (W : ℤ → R) (a b c d : ℤ) : Prop :=",
    "FLTForHuman.Elliptic.StrictAnti₄": "FLT's `StrictAnti₄`: four non-negative indices in strictly decreasing order.  def StrictAnti₄ : Prop :=",
    "FLTForHuman.Elliptic.addMulSub": "FLT's `addMulSub`; definitionally mathlib's elliptic atom.  abbrev addMulSub (W : ℤ → R) (m n : ℤ) : R :=",
    "FLTForHuman.Elliptic.avg₄": " def avg₄ : ℤ :=",
    "FLTForHuman.Elliptic.card_nTorsion": "FLT's `card_nTorsion`, and the port's main theorem: `#E[n] = n²` for `n`\ninvertible in `K`. Stated directly over mathlib's `Submodule.torsionBy`, so no\nreconciliation with a local `nTorsion` is needed.  theorem card_nTorsion {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed K]\n    [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] (n : ℕ) (hn : (n : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) = n ^ 2 :=",
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime": "FLT's `card_nTorsion_mul_of_coprime`: the CRT decomposition of the torsion.  theorem card_nTorsion_mul_of_coprime {m n : ℕ} (hmn : Nat.Coprime m n) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (m * n)) =\n      Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) m) *\n        Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) :=",
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers": "FLT's `card_nTorsion_odd_fibers`: for odd `n` the `n`-torsion has exactly\n`n²` elements. FLT's local `nTorsion` is replaced by `Submodule.torsionBy`.  theorem card_nTorsion_odd_fibers [W.IsElliptic] {n : ℕ} (hodd : Odd n)\n    (hn : (n : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) = n ^ 2 :=",
    "FLTForHuman.Elliptic.card_nTorsion_one": " theorem card_nTorsion_one :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 1) = 1 :=",
    "FLTForHuman.Elliptic.card_nTorsion_prime": "FLT's `card_nTorsion_prime`.  theorem card_nTorsion_prime [W.IsElliptic] {p : ℕ} (hp : p.Prime) (hn : (p : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) p) = p ^ 2 :=",
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow": "FLT's `card_nTorsion_prime_pow`.  theorem card_nTorsion_prime_pow [W.IsElliptic] {p : ℕ} (hp : p.Prime)\n    (hn : (p : K) ≠ 0) (k : ℕ) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) (p ^ k)) = p ^ (2 * k) :=",
    "FLTForHuman.Elliptic.card_nTorsion_two": "FLT's `card_nTorsion_two`: the 2-torsion has 4 elements when `2 ≠ 0`.  theorem card_nTorsion_two [W.IsElliptic] (h2 : (2 : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2) = 4 :=",
    "FLTForHuman.Elliptic.card_smul_fiber": "FLT's `card_smul_fiber`: every fiber of `n •` has the cardinality of the\n`n`-torsion. FLT's local `nTorsion` wrapper is replaced by mathlib's\n`Submodule.torsionBy`.  theorem card_smul_fiber [IsAlgClosed K] [W.IsElliptic] {n : ℕ}\n    (hn : (n : K) ≠ 0) (Q : (W.baseChange K).toAffine.Point) :\n    Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q} =\n      Nat.card (Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) n) :=",
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed": "**The theorem.** Over an algebraically closed field `K`, the `n`-torsion of\nan elliptic curve `E/K` has `n²` elements. This is\n`WeierstrassCurve.card_torsion_of_isAlgClosed` (FLT's `solution`, pinned at\n`aa2d8b3`), stated directly over mathlib's `Submodule.torsionBy`; since\n`card_nTorsion` above already uses `Submodule.torsionBy`, no reconciliation\nwrapper is needed.  theorem card_torsion_of_isAlgClosed {F K : Type*} [Field F] [Field K] [Algebra F K]\n    [IsAlgClosed K] [DecidableEq K] (W : WeierstrassCurve F) [W.IsElliptic] {n : ℕ}\n    (hn : (n : K) ≠ 0) :\n    Nat.card (Submodule.torsionBy ℤ ",
    "FLTForHuman.Elliptic.complEDSAux": "FLT's `compl₂EDSAux`: the `2`-complement auxiliary sequence.  def complEDSAux (m : ℤ) : R :=",
    "FLTForHuman.Elliptic.evalEval_φ": " theorem evalEval_φ {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :\n    (W.φ n).evalEval x y = (W.Φ n).eval x :=",
    "FLTForHuman.Elliptic.evalEval_ψ_sq": " theorem evalEval_ψ_sq {x y : F} (h : W.toAffine.Equation x y) (n : ℤ) :\n    ((W.ψ n).evalEval x y) ^ 2 = (W.ΨSq n).eval x :=",
    "FLTForHuman.Elliptic.exists_double_fiber_card": "FLT's `exists_double_fiber_card`: some `Q` has `2 * n ^ 2` preimages under\n`n •` counting both signs, which forces `#E[n] = n²`.  theorem exists_double_fiber_card [W.IsElliptic] {n : ℕ} (hodd : Odd n)\n    (hn : (n : K) ≠ 0) :\n    ∃ Q : (W.baseChange K).toAffine.Point,\n      Nat.card {P : (W.baseChange K).toAffine.Point // n • P = Q ∨ n • P = -Q} = 2 * n ^ 2 :=",
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber": "FLT's `finite_not_squarefree_fiber`: only finitely many `c` make\n`Φ n - c·ΨSq n` non-squarefree.  theorem finite_not_squarefree_fiber [IsAlgClosed K] [W.IsElliptic] {n : ℕ}\n    (hn : (n : K) ≠ 0) :\n    {c : K | ¬ Squarefree\n      ((W.baseChange K).Φ n - C c * (W.baseChange K).ΨSq n)}.Finite :=",
    "FLTForHuman.Elliptic.invar": "`6X² + b₂X + b₄`. The identity `preΨ₄ + Ψ₂Sq² = invar * Ψ₃` is what makes the\n`ω` construction go through.  def invar : R[X] :=",
    "FLTForHuman.Elliptic.invarDenom": "The denominator invariant of a sequence `u`, `invarDenom u s n`.  def invarDenom (u : ℤ → R) (s n : ℤ) : R :=",
    "FLTForHuman.Elliptic.invarNum": "The numerator invariant of a sequence `u`, `invarNum u s n`.  def invarNum (u : ℤ → R) (s n : ℤ) : R :=",
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": " lemma invarNum_eq_redInvarNum_mul (m : ℤ) :\n    invarNum (normEDS b c d) 1 m = redInvarNum b c d m * b :=",
    "FLTForHuman.Elliptic.invar_normEDS": "FLT's `invar_normEDS`.  lemma invar_normEDS (b c d : R) (s m n : ℤ) :\n    invarNum (normEDS b c d) s m * invarDenom (normEDS b c d) s n =\n      invarNum (normEDS b c d) s n * invarDenom (normEDS b c d) s m :=",
    "FLTForHuman.Elliptic.invar_of_net": "FLT's `invar_of_net`: the invariant ratio is independent of the index.  theorem invar_of_net (net_eq_zero : ∀ p q r s, net W p q r s = 0) (s m n : ℤ) :\n    invarNum W s m * invarDenom W s n = invarNum W s n * invarDenom W s m :=",
    "FLTForHuman.Elliptic.invar₂_normEDS": "FLT's `invar₂_normEDS`.  lemma invar₂_normEDS (b c d : R) (m : ℤ) :\n    invarNum (normEDS b c d) 1 m * c = invarDenom (normEDS b c d) 1 m * (d + b ^ 4) :=",
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq": "FLT's `isCoprime_Φ_ΨSq`: the `x`-numerator and the `n`-division polynomial\nare coprime, so the `n`-torsion `x`-coordinates are simple roots.  theorem isCoprime_Φ_ΨSq [IsAlgClosed K] [W.IsElliptic] {n : ℕ} (hn : 0 < n) :\n    IsCoprime ((W.baseChange K).Φ n) ((W.baseChange K).ΨSq n) :=",
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ": "`ΨSq n` and `ΨSq (n + 1)` are coprime.  theorem isCoprime_ΨSq_succ [W.IsElliptic] (n : ℕ) :\n    IsCoprime ((W.baseChange K).ΨSq n) ((W.baseChange K).ΨSq (n + 1)) :=",
    "FLTForHuman.Elliptic.isEllipticSequence_ext": "FLT's `IsEllSequence'.ext`: two elliptic sequences agreeing at `1,2,3,4` are\nequal.  theorem isEllipticSequence_ext (ellW : IsEllipticSequence W) (ellU : IsEllipticSequence U)\n    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)\n    (h1 : W 1 = U 1) (h2 : W 2 = U 2) (h3 : W 3 = U 3) (h4 : W 4 = U 4) : W = U :=",
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃": " lemma isEllipticSequence_iff_rel₃ :\n    IsEllipticSequence W ↔ ∀ m n r : ℤ, Rel₃ W m n r :=",
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec": "FLT's `IsEllSequence'.of_oddRec_evenRec`: the odd and even recursions force\nthe elliptic-sequence relation.  theorem isEllipticSequence_of_oddRec_evenRec (neg : W.Odd) (zero : W 0 = 0)\n    (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)\n    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :\n    IsEllipticSequence W :=",
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff": " theorem mem_nTorsion_two_iff {x y : K} (h : (W.baseChange K).toAffine.Nonsingular x y) :\n    (Point.some x y h : (W.baseChange K).toAffine.Point) ∈\n      Submodule.torsionBy ℤ ((W.baseChange K).toAffine.Point) 2 ↔\n      y = (W.baseChange K).toAffine.negY x y :=",
    "FLTForHuman.Elliptic.net": "FLT's `net`; definitionally mathlib's `rel`.  abbrev net (W : ℤ → R) (p q r s : ℤ) : R :=",
    "FLTForHuman.Elliptic.net_normEDS": "`normEDS` satisfies the full net property `rel = 0`.  lemma net_normEDS (b c d : R) (p q r s : ℤ) : net (normEDS b c d) p q r s = 0 :=",
    "FLTForHuman.Elliptic.net_of_isEllipticSequence": "The *full* net property, from the `s = 0` slice plus non-zero-divisors: apply\n`rel₄_of_oddRec_evenRec` at the indices `(2p+s, 2q+s, 2r+s, s)`, which always\nhave the same parity.  lemma net_of_isEllipticSequence (ell : IsEllipticSequence W) (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)\n    (p q r s : ℤ) : net W p q r s = 0 :=",
    "FLTForHuman.Elliptic.net_zero_iff_rel₃": " lemma net_zero_iff_rel₃ (m n r : ℤ) : net W m n r 0 = 0 ↔ Rel₃ W m n r :=",
    "FLTForHuman.Elliptic.normEDS_eq_aeval": "Specialising the universal EDS recovers `normEDS b c d`.  lemma normEDS_eq_aeval (b c d : R) :\n    normEDS b c d = (aeval (Param.rec b c d) <| universalNormEDS ·) :=",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence": "The normalised EDS satisfies the elliptic-sequence relation. In FLT this is\n`IsEllSequence'.normEDS`, proved by specialising to the universal EDS to get the\nnon-zero-divisor hypothesis on `b`. mathlib still lists this as a `TODO`.  theorem normEDS_isEllipticSequence (b c d : R) : IsEllipticSequence (normEDS b c d) :=",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors": " lemma normEDS_isEllipticSequence_of_mem_nonZeroDivisors {b c d : R} (hb : b ∈ R⁰) :\n    IsEllipticSequence (normEDS b c d) :=",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": "The complement `complEDS` witnesses `normEDS m ∣ normEDS (n * m)`.  theorem normEDS_mul_complEDS (b c d : R) (m n : ℤ) :\n    normEDS b c d m * complEDS b c d m n = normEDS b c d (n * m) :=",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": " lemma normEDS_mul_complEDS_div (b c d : R) (m : ℤ) (hm : m ≠ 0) (n : ℤ) (dvd : m ∣ n) :\n    normEDS b c d m * complEDS b c d m (n / m) = normEDS b c d n :=",
    "FLTForHuman.Elliptic.normEDS_two_three_two": "`normEDS 2 3 2` is the identity EDS.  lemma normEDS_two_three_two : normEDS (2 : ℤ) 3 2 = id :=",
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": " lemma preΨ₄_add_Ψ₂Sq_sq : W.preΨ₄ + W.Ψ₂Sq ^ 2 = invar W * W.Ψ₃ :=",
    "FLTForHuman.Elliptic.redInvarDenom": "FLT's `redInvarDenom`.  noncomputable def redInvarDenom (b c d : R) (m : ℤ) : R :=",
    "FLTForHuman.Elliptic.redInvarNum": "FLT's `redInvarNum`, written with mathlib's `complEDS₂` in place of\n`compl₂EDS` (they are definitionally equal).  def redInvarNum (m : ℤ) : R :=",
    "FLTForHuman.Elliptic.redInvar_normEDS": "FLT's `redInvar_normEDS`.  lemma redInvar_normEDS (b c d : R) (m : ℤ) :\n    redInvarNum b c d m = redInvarDenom b c d m * (d + b ^ 4) :=",
    "FLTForHuman.Elliptic.rel₃_iff_evenRec": " lemma rel₃_iff_evenRec (m : ℤ) : Rel₃ W (m + 1) (m - 1) 1 ↔ EvenRec W m :=",
    "FLTForHuman.Elliptic.rel₃_iff_oddRec": " lemma rel₃_iff_oddRec (m : ℤ) : Rel₃ W (m + 1) m 1 ↔ OddRec W m :=",
    "FLTForHuman.Elliptic.rel₃_iff₄": " lemma rel₃_iff₄ (m n r : ℤ) :\n    Rel₃ W m n r ↔ rel₄ W (2 * m) (2 * n) (2 * r) 0 = 0 :=",
    "FLTForHuman.Elliptic.rel₄": "FLT's `rel₄`; definitionally mathlib's `atomRel`.  abbrev rel₄ (W : ℤ → R) (a b c d : ℤ) : R :=",
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec": " theorem rel₄_of_anti_oddRec_evenRec {W : ℤ → R} (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)\n    (oddRec : ∀ m ≥ 2, OddRec W m) (evenRec : ∀ m ≥ 3, EvenRec W m) :\n    ∀ ⦃a b c d : ℤ⦄, Rel₄OfValid W a b c d :=",
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero": " theorem smul_eq_zero_of_ΨSq_eval_eq_zero [W.IsElliptic] {n : ℕ} (hn : 0 < n)\n    {x₀ y₀ : K} (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)\n    (hz : ((W.baseChange K).ΨSq n).eval x₀ = 0) :\n    n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = 0 :=",
    "FLTForHuman.Elliptic.smul_formula_or_zero": "FLT's `smul_formula_or_zero`: away from the roots of `ΨSq n` the coordinate\nformula holds, and at them `n • P = 0`.  theorem smul_formula_or_zero [W.IsElliptic] {n : ℕ} (_hn : 0 < n) {x₀ y₀ : K}\n    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀) :\n    (((W.baseChange K).ΨSq n).eval x₀ ≠ 0 →\n      ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),\n        n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧\n          x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀) ∧\n    (((W.baseChange K).ΨSq n).eval x₀ = 0 →\n      n • (Poi",
    "FLTForHuman.Elliptic.smul_surjective": "FLT's `smul_surjective`: for odd `n` invertible in `K`, multiplication by\n`n` is surjective on `E(K)`.  theorem smul_surjective [IsAlgClosed K] [W.IsElliptic] {n : ℕ}\n    (hn : (n : K) ≠ 0) :\n    Function.Surjective (fun P : (W.baseChange K).toAffine.Point => n • P) :=",
    "FLTForHuman.Elliptic.smul_x_eq": " theorem smul_x_eq [W.IsElliptic] {n : ℕ} (hn : 0 < n) {x₀ y₀ : K}\n    (h : (W.baseChange K).toAffine.Nonsingular x₀ y₀)\n    (hns : ((W.baseChange K).ΨSq n).eval x₀ ≠ 0) :\n    ∃ (x' y' : K) (h' : (W.baseChange K).toAffine.Nonsingular x' y'),\n      n • (Point.some x₀ y₀ h : (W.baseChange K).toAffine.Point) = Point.some x' y' h' ∧\n        x' * ((W.baseChange K).ΨSq n).eval x₀ = ((W.baseChange K).Φ n).eval x₀ :=",
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval": "On a point of the curve, `(y - negY x y)²` is the value of `Ψ₂Sq`.  theorem sub_negY_sq_eq_Ψ₂Sq_eval {x y : F} (e : W.Equation x y) :\n    (y - W.negY x y) ^ 2 = (WeierstrassCurve.Ψ₂Sq W).eval x :=",
    "FLTForHuman.Elliptic.two_mul_ωe": " lemma two_mul_ωe (n : ℤ) :\n    2 * ωe W n = ψc W n - CC W.a₁ * W.φ n * W.ψ n - CC W.a₃ * W.ψ n ^ 3 :=",
    "FLTForHuman.Elliptic.universalNormEDS": "The universal normalised EDS over `ℤ[B, C, D]`.  noncomputable def universalNormEDS : ℤ → MvPolynomial Param ℤ :=",
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors": " lemma universalNormEDS_mem_nonZeroDivisors {n : ℤ} (hn : n ≠ 0) :\n    universalNormEDS n ∈ (MvPolynomial Param ℤ)⁰ :=",
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero": " lemma universalNormEDS_ne_zero {n : ℤ} (hn : n ≠ 0) : universalNormEDS n ≠ 0 :=",
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero": "FLT's `wronskian_Φ_ΨSq_ne_zero`: the Wronskian of `Φ n` and `ΨSq n` is\nnonzero — the degree bookkeeping that makes `Φ n - c·ΨSq n` squarefree.  theorem wronskian_Φ_ΨSq_ne_zero [W.IsElliptic] {n : ℕ} (hn : (n : K) ≠ 0) :\n    derivative ((W.baseChange K).Φ n) * (W.baseChange K).ΨSq n -\n      (W.baseChange K).Φ n * derivative ((W.baseChange K).ΨSq n) ≠ 0 :=",
    "FLTForHuman.Elliptic.ψc": "The `2`-complement of the division polynomials, characterised by\n`ψ n * ψc n = ψ (2n)`. This is FLT's `compl₂EDS`, which is definitionally\nmathlib's `complEDS₂`.  def ψc (n : ℤ) : R[X][Y] :=",
    "FLTForHuman.Elliptic.ψc_spec": "The defining property of the `2`-complement. In FLT this is\n`ψc_spec`/`normEDS_mul_compl₂EDS`; here it is mathlib's\n`normEDS_mul_complEDS₂` read through `WeierstrassCurve.ψ`.  lemma ψc_spec (n : ℤ) : W.ψ n * ψc W n = W.ψ (2 * n) :=",
    "FLTForHuman.Elliptic.ωe": "FLT's `WeierstrassCurve.ωe`: the `y`-coordinate numerator of `n • P`.  def ωe (n : ℤ) : R[X][Y] :=",
    "FLTForHuman.Elliptic.ωe_spec": " lemma ωe_spec (n : ℤ) :\n    2 * ωe W n + CC W.a₁ * W.φ n * W.ψ n + CC W.a₃ * W.ψ n ^ 3 = ψc W n :=",
    "Fact": "Wrapper for adding elementary propositions to the type class systems.\nWarning: this can easily be abused. See the rest of this docstring for details.\n\nCertain propositions should not be treated as a class globally,\nbut sometimes it is very convenient to be able to use the type class system\nin specific circumstances.\n\nFor example, `ZMod p` is a field if and only if `p` is a prime number.\nIn order to be able to find this field instance automatically by type class search,\nwe have to turn `p.Prime` into an instance implicit assumption.\n\nOn the other hand, making `Nat.Prime` a class would require a",
    "Field": "A `Field` is a `CommRing` with multiplicative inverses for nonzero elements.\n\nAn instance of `Field K` includes maps `ratCast : ℚ → K` and `qsmul : ℚ → K → K`.\nThose two fields are needed to implement the `DivisionRing K → Algebra ℚ K` instance since we need\nto control the specific definitions for some special cases of `K` (in particular `K = ℚ` itself).\nSee also note [forgetful inheritance].\n\nIf the field has positive characteristic `p`, our division by zero convention forces\n`ratCast (1 / p) = 1 / 0 = 0`.  @[stacks 09FD \"first part\"]\nclass Field (K : Type u) extends CommRing K, DivisionRing ",
    "Finite": "A type is `Finite` if it is in bijective correspondence to some `Fin n`.\n\nThis is similar to `Fintype`, but `Finite` is a proposition rather than data.\nA particular benefit to this is that `Finite` instances are definitionally equal to one another\n(due to proof irrelevance) rather than being merely propositionally equal,\nand, furthermore, `Finite` instances generally avoid the need for `Decidable` instances.\nOne other notable difference is that `Finite` allows there to be `Finite p` instances\nfor all `p : Prop`, which is not allowed by `Fintype` due to universe constraints.\nAn application of t",
    "FiniteDimensional": "`FiniteDimensional` vector spaces are defined to be finite modules.\nUse `Module.Basis.finiteDimensional_of_finite` to prove finite dimension from another definition.  abbrev FiniteDimensional (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V] :=",
    "Finset": "`Finset α` is the type of finite sets of elements of `α`. It is implemented\nas a multiset (a list up to permutation) which has no duplicate elements.  @[use_set_notation_for_order, to_dual_dont_translate]\nstructure Finset (α : Type*) where\n  /-- The underlying multiset -/\n  val : Multiset α\n  /-- `val` contains no duplicates -/\n  nodup : Nodup val",
    "Finset.card": "`s.card` is the number of elements of `s`, aka its cardinality.\n\nThe notation `#s` can be accessed in the `Finset` locale.  def card (s : Finset α) : ℕ :=",
    "Finset.sum": "`∑ x ∈ s, f x` is the sum of `f x` as `x` ranges over the elements\nof the finite set `s`.\n\nWhen the index type is a `Fintype`, the notation `∑ x, f x`, is a shorthand for\n`∑ x ∈ Finset.univ, f x`.  ",
    "Finsupp": "`Finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that\n`f x = 0` for all but finitely many `x`.  structure Finsupp (α : Type*) (M : Type*) [Zero M] where\n  /-- The support of a finitely supported function (aka `Finsupp`). -/\n  support : Finset α\n  /-- The underlying function of a bundled finitely supported function (aka `Finsupp`). -/\n  toFun : α → M\n  /-- The witness that the support of a `Finsupp` is indeed the exact locus where its\n  underlying function is nonzero. -/\n  mem_support_toFun : ∀ a, a ∈ support ↔ toFun a ≠ 0",
    "Finsupp.liftAddHom": "The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`\nand monoid homomorphisms `(α →₀ M) →+ N`.  def liftAddHom [AddZeroClass M] [AddCommMonoid N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where\n  toFun F :=\n    { toFun f := f.sum (F ·)\n      map_zero' := Finsupp.sum_zero_index\n      map_add' f g := Finsupp.sum_hom_add_index F }\n  invFun F x := F.comp (singleAddHom x)\n  left_inv F := by ext; simp\n  right_inv F := by ext; simp\n  map_add' F G := by ext; simp",
    "Finsupp.module": " instance module [Semiring R] [AddCommMonoid M] [Module R M] : Module R (α →₀ M) :=",
    "Finsupp.single": "`single a b` is the finitely supported function with value `b` at `a` and zero otherwise.  def single (a : α) (b : M) : α →₀ M where\n  support :=\n    haveI := Classical.decEq M\n    if b = 0 then ∅ else {a}\n  toFun :=\n    haveI := Classical.decEq α\n    Pi.single a b\n  mem_support_toFun a' := by grind",
    "Finsupp.support": "The support of a finitely supported function (aka `Finsupp`).  ",
    "FreeAddMonoid": "If `α` is a type, then `FreeAddMonoid α` is the free additive monoid generated by `α`.\nThis is a monoid equipped with a function `FreeAddMonoid.of : α → FreeAddMonoid α` which has\nthe following universal property: if `M` is any monoid, and `f : α → M` is any function,\nthen this function is the composite of `FreeAddMonoid.of` and a unique monoid homomorphism\n`FreeAddMonoid.lift f : FreeAddMonoid α →+ M`.\n\nA typical element of `FreeAddMonoid α` is a formal sum of elements of `α`.\nFor example if `x` and `y` are terms of type `α` then `x + y + y + x` is a\n\"typical\" element of `FreeAddMonoid α`. In",
    "FunLike": "The class `FunLike F α β` (`Fun`ction-`Like`) expresses that terms of type `F`\nhave an injective coercion to functions from `α` to `β`.\n`FunLike` is the non-dependent version of `DFunLike`.\nThis typeclass is used in the definition of the homomorphism typeclasses,\nsuch as `ZeroHomClass`, `MulHomClass`, `MonoidHomClass`, ....\n abbrev FunLike F α β :=",
    "Function.Injective": "A function `f : α → β` is called injective if `f x = f y` implies `x = y`.  @[expose]\ndef Injective (f : α → β) : Prop :=",
    "Function.Odd": "A function `f` is _odd_ if it satisfies `f (-x) = -f x` for all `x`.  protected def Odd [Neg β] (f : α → β) : Prop :=",
    "Function.RightInverse": "`RightInverse g f` means that `g` is a right inverse to `f`. That is, `f ∘ g = id`.  @[expose, grind, implicit_reducible]\ndef RightInverse {α β} (g : β → α) (f : α → β) : Prop :=",
    "Function.Surjective": "A function `f : α → β` is called surjective if every `b : β` is equal to `f a`\nfor some `a : α`.  @[expose]\ndef Surjective (f : α → β) : Prop :=",
    "Function.algebra": "A special case of `Pi.algebra` for non-dependent types. Lean struggles to elaborate\ndefinitions elsewhere in the library without this.  instance Function.algebra {R : Type*} (ι : Type*) (A : Type*) [CommSemiring R] [Semiring A]\n    [Algebra R A] : Algebra R (ι → A) :=",
    "Function.comp": "Function composition, usually written with the infix operator `∘`. A new function is created from\ntwo existing functions, where one function's output is used as input to the other.\n\nExamples:\n * `Function.comp List.reverse (List.drop 2) [3, 2, 4, 1] = [1, 4]`\n * `(List.reverse ∘ List.drop 2) [3, 2, 4, 1] = [1, 4]`\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `∘` in identifiers is `comp`. @[inline, implicit_reducible] def Function.comp {α : Sort u} {β : Sort v} {δ : Sort w} (f : β → δ) (g : α → β) : α → δ :=",
    "GE.ge": "`a ≥ b` is an abbreviation for `b ≤ a`. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `≥` in identifiers is `ge`. @[reducible] def GE.ge {α : Type u} [LE α] (a b : α) : Prop :=",
    "HMod.hMod": "`a % b` computes the remainder upon dividing `a` by `b`.\nThe meaning of this notation is type-dependent.\n* For `Nat` and `Int` it satisfies `a % b + b * (a / b) = a`,\n  and `a % 0` is defined to be `a`. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `%` in identifiers is `mod`. ",
    "HSMul.hSMul": "`a • b` computes the product of `a` and `b`.\nThe meaning of this notation is type-dependent, but it is intended to be used for left actions. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `•` in identifiers is `smul`. ",
    "HasQuotient.Quotient": "`HasQuotient.Quotient A b` (denoted as `A ⧸ b`) is the quotient of the type `A` by `b`.  ",
    "Ideal": "A (left) ideal in a semiring `R` is an additive submonoid `s` such that\n`a * b ∈ s` whenever `b ∈ s`. If `R` is a ring, then `s` is an additive subgroup.  abbrev Ideal (R : Type u) [Semiring R] :=",
    "Ideal.Cotangent": "`I ⧸ I ^ 2` as a quotient of `I`.  def Cotangent : Type _ :=",
    "Ideal.Cotangent.smul_eq_zero_of_mem": " lemma Cotangent.smul_eq_zero_of_mem {I : Ideal R}\n    {x} (hx : x ∈ I) (m : I.Cotangent) : x • m = 0 :=",
    "Ideal.IsTwoSided": "A left ideal `I : Ideal R` is two-sided if it is also a right ideal.  @[mk_iff] class IsTwoSided : Prop where\n  mul_mem_of_left {a : α} (b : α) : a ∈ I → a * b ∈ I",
    "Ideal.Quotient.mk": "The ring homomorphism from a ring `R` to a quotient ring `R/I`.  def mk : R →+* R ⧸ I where\n  toFun a := Submodule.Quotient.mk a\n  map_zero' := rfl\n  map_one' := rfl\n  map_mul' _ _ := rfl\n  map_add' _ _ := rfl",
    "Ideal.comap": "`I.comap f` is the preimage of `I` under `f`.  def comap [RingHomClass F R S] (I : Ideal S) : Ideal R where\n  carrier := f ⁻¹' I\n  add_mem' {x y} hx hy := by\n    simp only [Set.mem_preimage, SetLike.mem_coe, map_add f] at hx hy ⊢\n    exact add_mem hx hy\n  zero_mem' := by simp only [Set.mem_preimage, map_zero, SetLike.mem_coe, Submodule.zero_mem]\n  smul_mem' c x hx := by\n    simp only [smul_eq_mul, Set.mem_preimage, map_mul, SetLike.mem_coe] at *\n    exact mul_mem_left I _ hx",
    "Ideal.map_toCotangent_ker": " theorem map_toCotangent_ker : (LinearMap.ker I.toCotangent).map I.subtype = I ^ 2 :=",
    "Ideal.mk_ker": " @[simp]\ntheorem mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) = I :=",
    "Ideal.mul_mem_left": " theorem mul_mem_left : b ∈ I → a * b ∈ I :=",
    "Ideal.mul_mem_mul": " theorem mul_mem_mul {r s} (hr : r ∈ I) (hs : s ∈ J) : r * s ∈ I * J :=",
    "Ideal.span": "The ideal generated by a subset of a ring  abbrev span (s : Set α) : Ideal α :=",
    "Ideal.toCotangent": "The quotient map from `I` to `I ⧸ I ^ 2`.  @[simps! -isSimp apply]\ndef toCotangent : I →ₗ[R] I.Cotangent :=",
    "Ideal.toCotangent_eq": " theorem toCotangent_eq {x y : I} : I.toCotangent x = I.toCotangent y ↔ (x - y : R) ∈ I ^ 2 :=",
    "Infinite": "A type is said to be infinite if it is not finite. Note that `Infinite α` is equivalent to\n`IsEmpty (Fintype α)` or `IsEmpty (Finite α)`.  class Infinite (α : Sort*) : Prop where\n  /-- assertion that `α` is `¬Finite` -/\n  not_finite : ¬Finite α",
    "Int": "The integers.\n\nThis type is special-cased by the compiler and overridden with an efficient implementation. The\nruntime has a special representation for `Int` that stores “small” signed numbers directly, while\nlarger numbers use a fast arbitrary-precision arithmetic library (usually\n[GMP](https://gmplib.org/)). A “small number” is an integer that can be encoded with one fewer bits\nthan the platform's pointer size (i.e. 63 bits on 64-bit architectures and 31 bits on 32-bit\narchitectures).\n @[suggest_for ℤ]\ninductive Int : Type where\n  /--\n  A natural number is an integer.\n\n  This constructor cov",
    "Int.cast": "The canonical homomorphism `Int → R`. In most use cases, the target type will have a ring structure,\nand this homomorphism should be a ring homomorphism.\n\n`IntCast` and `NatCast` exist to allow different libraries with their own types that can be notated\nas natural numbers to have consistent `simp` normal forms without needing to create coercion\nsimplification sets that are aware of all combinations. Libraries should make it easy to work with\n`IntCast` where possible. For instance, in Mathlib there will be such a homomorphism (and thus an\n`IntCast R` instance) whenever `R` is an additive group",
    "Int.decLt": "Decides whether `a < b`.\n\n```\n#eval `¬ ( (7 : Int) < 0 )` -- true\n#eval `¬ ( (0 : Int) < 0 )` -- true\n#eval `(7 : Int) < 10` -- true\n```\n\nImplemented by efficient native code.  @[extern \"lean_int_dec_lt\"]\ninstance decLt (a b : @& Int) : Decidable (a < b) :=",
    "Int.inductionOn'": "Inductively define a function on `ℤ` by defining it at `b`, for the `succ` of a number greater\nthan `b`, and the `pred` of a number less than `b`.  @[elab_as_elim] protected def inductionOn' : motive z :=",
    "Int.natAbs": "The absolute value of an integer is its distance from `0`.\n\nThis function is overridden by the compiler with an efficient implementation. This definition is\nthe logical model.\n\nExamples:\n * `(7 : Int).natAbs = 7`\n * `(0 : Int).natAbs = 0`\n * `(-11 : Int).natAbs = 11`\n @[extern \"lean_nat_abs\", implicit_reducible]\ndef natAbs (m : @& Int) : Nat :=",
    "Int.negOnePow": "The map `ℤ → ℤˣ` which sends `n` to `(-1 : ℤˣ) ^ n`.  def negOnePow (n : ℤ) : ℤˣ :=",
    "Int.sign": "Returns the “sign” of the integer as another integer:\n* `1` for positive numbers,\n* `-1` for negative numbers, and\n* `0` for `0`.\n\nExamples:\n* `Int.sign 34 = 1`\n* `Int.sign 2 = 1`\n* `Int.sign 0 = 0`\n* `Int.sign -1 = -1`\n* `Int.sign -362 = -1`\n def sign : Int → Int\n  | Int.ofNat (succ _) => 1\n  | Int.ofNat 0 => 0\n  | -[_+1]      => -1",
    "Int.strongRec": "A strong recursor for `Int` that specifies explicit values for integers below a threshold,\nand is analogous to `Nat.strongRec` for integers on or above the threshold.  @[elab_as_elim] protected def strongRec (n : ℤ) : motive n :=",
    "Int.tdiv": "Integer division using the T-rounding convention.\n\nIn [the T-rounding convention][t-rounding] (division with truncation), all rounding is towards zero.\nDivision by 0 is defined to be 0. In this convention, `Int.tmod a b + b * (Int.tdiv a b) = a`.\n\n[t-rounding]: https://dl.acm.org/doi/pdf/10.1145/128861.128862\n\nThis function is overridden by the compiler with an efficient implementation. This definition is the\nlogical model.\n\nExamples:\n* `(7 : Int).tdiv (0 : Int) = 0`\n* `(0 : Int).tdiv (7 : Int) = 0`\n* `(12 : Int).tdiv (6 : Int) = 2`\n* `(12 : Int).tdiv (-6 : Int) = -2`\n* `(-12 : Int).tdiv (6 : ",
    "IntermediateField": "`S : IntermediateField K L` is a subset of `L` such that there is a field\ntower `L / S / K`.  structure IntermediateField extends Subalgebra K L where\n  inv_mem' : ∀ x ∈ carrier, x⁻¹ ∈ carrier",
    "IntermediateField.adjoin": "`adjoin F S` extends a field `F` by adjoining a set `S ⊆ E`.  @[stacks 09FZ \"first part\"]\ndef adjoin : IntermediateField F E :=",
    "IntermediateField.algebra'": " instance algebra' {R' K L : Type*} [Field K] [Field L] [Algebra K L] (S : IntermediateField K L)\n    [CommSemiring R'] [SMul R' K] [Algebra R' L] [IsScalarTower R' K L] : Algebra R' S :=",
    "Inv.inv": "`a⁻¹` computes the inverse of `a`.\nThe meaning of this notation is type-dependent. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `⁻¹` in identifiers is `inv`. ",
    "InvImage": "The inverse image of `r : β → β → Prop` by a function `α → β` is the relation\n`s : α → α → Prop` defined by `s a b = r (f a) (f b)`.\n @[implicit_reducible] def InvImage {α : Sort u} {β : Sort v} (r : β → β → Prop) (f : α → β) : α → α → Prop :=",
    "Irreducible": "`Irreducible p` states that `p` is non-unit and only factors into units.\n\nWe explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a\nmonoid allows us to reuse irreducible for associated elements. \n\n[Wikidata Q2989575](https://www.wikidata.org/wiki/Q2989575) @[to_additive (attr := wikidata Q2989575)]\nstructure Irreducible (p : M) : Prop where\n  /-- An irreducible element is not a unit. -/\n  not_isUnit : ¬IsUnit p\n  /-- If an irreducible element factors, then one factor is a unit. -/\n  isUnit_or_isUnit ⦃a b : M⦄ : p = a * b → IsUnit a ∨ IsUnit b",
    "Irreducible.maximalIdeal_eq": " theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :\n    maximalIdeal R = Ideal.span {ϖ} :=",
    "IsAlgClosed": "An algebraically closed field is one where every polynomial splits. Equivalently, all\nnon-constant polynomials have a root. See `IsAlgClosed.exists_root` and\n`IsAlgClosed.of_exists_root`.  @[stacks 09GR \"The definition of `IsAlgClosed` in mathlib is 09GR (4)\"]\nclass IsAlgClosed : Prop where\n  splits : ∀ p : k[X], p.Splits",
    "IsCoprime": "The proposition that `x` and `y` are coprime, defined to be the existence of `a` and `b` such\nthat `a * x + b * y = 1`. Note that elements with no common divisors are not necessarily coprime,\ne.g., the multivariate polynomials `x₁` and `x₂` are not coprime.  @[wikidata Q104752]\ndef IsCoprime : Prop :=",
    "IsDedekindDomain": "A Dedekind domain is an integral domain that is Noetherian, integrally closed, and\nhas Krull dimension at most one.\n\nThis is definition 3.2 of [Neukirch1992].\n\nThis is exactly `IsDedekindRing` plus the `IsDomain` hypothesis.\n\nThe integral closure condition is independent of the choice of field of fractions:\nuse `isDedekindDomain_iff` to prove `IsDedekindDomain` for a given `fraction_map`.\n\nSee also `isDedekindDomain_iff_isDiscreteValuationRing_atPrime` and\n`isDedekindDomain_iff_mul_inv_cancel`.  class IsDedekindDomain : Prop\n  extends IsDomain A, IsDedekindRing A",
    "IsDedekindDomain.HeightOneSpectrum": "The height one prime spectrum of a Dedekind domain `R` is the type of nonzero prime ideals of\n`R`. Note that this equals the maximal spectrum if `R` has Krull dimension 1.  @[ext, nolint unusedArguments]\nstructure HeightOneSpectrum where\n  asIdeal : Ideal R\n  isPrime : asIdeal.IsPrime\n  ne_bot : asIdeal ≠ ⊥",
    "IsDedekindDomain.HeightOneSpectrum.asIdeal": " ",
    "IsDedekindDomain.HeightOneSpectrum.intValuation": "The `v`-adic valuation on `R`.  def intValuation : Valuation R ℤᵐ⁰ where\n  toFun := v.intValuationDef\n  map_zero' := intValuation.map_zero' v\n  map_one' := intValuation.map_one' v\n  map_mul' := intValuation.map_mul' v\n  map_add_le_max' := intValuation.map_add_le_max' v",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": "The `v`-adic valuation on `R` is bounded above by 1.  theorem intValuation_le_one (x : R) : v.intValuation x ≤ 1 :=",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": "The `v`-adic valuation of `r : R` is less than 1 if and only if `r ∈ v`.  theorem intValuation_lt_one_iff_mem (r : R) :\n    v.intValuation r < 1 ↔ r ∈ v.asIdeal :=",
    "IsDedekindDomain.HeightOneSpectrum.valuation": "The `v`-adic valuation of `x : K` is the valuation of `r` divided by the valuation of `s`,\nwhere `r` and `s` are chosen so that `x = r/s`.  @[no_expose]\ndef valuation (v : HeightOneSpectrum R) : Valuation K ℤᵐ⁰ :=",
    "IsDiscreteValuationRing": "An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which\nis not a field.  class IsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R] : Prop\n    extends IsPrincipalIdealRing R, IsLocalRing R where\n  not_a_field' : maximalIdeal R ≠ ⊥",
    "IsDiscreteValuationRing.exists_irreducible": "Uniformizers exist in a DVR.  theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ :=",
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": "An element of a DVR is irreducible iff it is a uniformizer, that is, generates the\nmaximal ideal of `R`.  theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=",
    "IsDiscreteValuationRing.maximalIdeal": "The maximal ideal of a discrete valuation ring.  def maximalIdeal : HeightOneSpectrum A where\n  asIdeal := IsLocalRing.maximalIdeal A\n  isPrime := Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal A)\n  ne_bot := by simpa [ne_eq, ← isField_iff_maximalIdeal_eq] using not_isField A",
    "IsDomain": "A domain is a nontrivial semiring such that multiplication by a nonzero element\nis cancellative on both sides. In other words, a nontrivial semiring `R` satisfying\n`∀ {a b c : R}, a ≠ 0 → a * b = a * c → b = c` and\n`∀ {a b c : R}, b ≠ 0 → a * b = c * b → a = c`.\n\nThis is implemented as a mixin for `Semiring α`.\nTo obtain an integral domain use `[CommRing α] [IsDomain α]`.  @[stacks 09FE]\nclass IsDomain (α : Type u) [Semiring α] : Prop extends IsCancelMulZero α, Nontrivial α",
    "IsDvdSequence": "A function `f : α → β` is a divisibility sequence if `a ∣ b` implies `f a ∣ f b`.  def IsDvdSequence [Dvd α] [Dvd β] (f : α → β) : Prop :=",
    "IsEllipticDvdSequence": "The proposition that a sequence indexed by `ℤ` is an EDS.  def IsEllipticDvdSequence : Prop :=",
    "IsEllipticNet": "The proposition that a sequence indexed by `ℤ` is an elliptic net.  def IsEllipticNet : Prop :=",
    "IsEllipticNet.atom": "The elliptic atom `Wₐ(a, b)` that defines an elliptic net. Note that this is defined in terms of\ntruncated integer division, and hence should only be used when `a` and `b` have the same parity.  def atom (a b : ℤ) : R :=",
    "IsEllipticNet.atomRel": "The elliptic relator `ERₐ(a, b, c, d)` obtained by a change of variables in `ER(p, q, r, s)`\n(see `IsEllipticNet.rel_eq` and `IsEllipticNet.atomRel_eq`). Note that this is defined in terms of\nelliptic atoms, and hence should only be used when `a`, `b`, `c`, and `d` have the same parity.  def atomRel (a b c d : ℤ) : R :=",
    "IsEllipticNet.atomRel_eq": " lemma atomRel_eq {a b c d : ℤ} (parity : [a, b, c, d].Pairwise (· % 2 = · % 2)) :\n    atomRel W a b c d = rel W ((a - d) / 2) ((b - d) / 2) ((c - d) / 2) d :=",
    "IsEllipticNet.rel": "The elliptic relator `ER(p, q, r, s)` that defines an elliptic net.  def rel (p q r s : ℤ) : R :=",
    "IsEllipticNet.rel_eq": " lemma rel_eq (p q r s : ℤ) : rel W p q r s = atomRel W (2 * p + s) (2 * q + s) (2 * r + s) s :=",
    "IsEllipticSequence": "The proposition that a sequence indexed by `ℤ` is an elliptic sequence.  def IsEllipticSequence : Prop :=",
    "IsFractionRing.algEquivOfAlgEquiv": "Given `R`-algebras `A, B` and localization maps to their fraction rings\n`f : A →ₐ[R] K, g : B →ₐ[R] L`, an isomorphism `h : A ≃ₐ[R] B` induces an isomorphism of\nfraction rings `K ≃ₐ[R] L`.  noncomputable def algEquivOfAlgEquiv : K ≃ₐ[R] L :=",
    "IsLocalRing.ResidueField": "The residue field of a local ring is the quotient of the ring by its maximal ideal.  @[wikidata Q7315530]\ndef ResidueField :=",
    "IsLocalRing.ResidueField.algebra": " instance ResidueField.algebra {R₀} [CommRing R₀] [Algebra R₀ R] :\n    Algebra R₀ (ResidueField R) :=",
    "IsLocalRing.ResidueField.field": " noncomputable instance ResidueField.field : Field (ResidueField R) :=",
    "IsLocalRing.maximalIdeal": "The ideal of elements that are not units.  def maximalIdeal : Ideal R where\n  __ := nonunitsAddSubmonoid R\n  smul_mem' _ _ := mul_mem_nonunits_right",
    "IsLocalization": "The typeclass `IsLocalization (M : Submonoid R) S` where `S` is an `R`-algebra\nexpresses that `S` is isomorphic to the localization of `R` at `M`.  abbrev IsLocalization :=",
    "IsScalarTower": "An instance of `IsScalarTower M N α` states that the multiplicative\naction of `M` on `α` is determined by the multiplicative actions of `M` on `N`\nand `N` on `α`.  @[to_additive]\nclass IsScalarTower (M N α : Type*) [SMul M N] [SMul N α] [SMul M α] : Prop where\n  /-- Associativity of `•` -/\n  smul_assoc : ∀ (x : M) (y : N) (z : α), (x • y) • z = x • y • z",
    "IsScalarTower.algebraMap_smul": " theorem algebraMap_smul [SMul R M] [IsScalarTower R A M] (r : R) (x : M) :\n    algebraMap R A r • x = r • x :=",
    "IsScalarTower.left": " @[to_additive]\ninstance IsScalarTower.left : IsScalarTower M M α where\n  smul_assoc x y z := mul_smul x y z",
    "IsScalarTower.right": "This has high priority because it is almost always the right instance when it applies.  instance (priority := high) _root_.IsScalarTower.right : IsScalarTower R A A :=",
    "IsScalarTower.to_smulCommClass": " instance (priority := 120) IsScalarTower.to_smulCommClass : SMulCommClass R A M :=",
    "IsSeparable": "An element `x` of an algebra `K` over a commutative ring `F` is said to be *separable*, if its\nminimal polynomial over `K` is separable. Note that the minimal polynomial of any element not\nintegral over `F` is defined to be `0`, which is not a separable polynomial.\n @[stacks 09H1 \"second part\"]\ndef IsSeparable (x : K) : Prop :=",
    "IsUnit": "An element `a : M` of a `Monoid` is a unit if it has a two-sided inverse.\nThe actual definition says that `a` is equal to some `u : Mˣ`, where\n`Mˣ` is a bundled version of `IsUnit`.  @[to_additive /-- An element `a : M` of an `AddMonoid` is an `AddUnit` if it has a two-sided\nadditive inverse. The actual definition says that `a` is equal to some `u : AddUnits M`,\nwhere `AddUnits M` is a bundled version of `IsAddUnit`. -/]\ndef IsUnit [Monoid M] (a : M) : Prop :=",
    "KaehlerDifferential": "The module of Kähler differentials (Kahler differentials, Kaehler differentials).\nThis is implemented as `I / I ^ 2` with `I` the kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.\nTo view elements as a linear combination of the form `s • D s'`, use\n`KaehlerDifferential.tensorProductTo_surjective` and `Derivation.tensorProductTo_tmul`.\n\nWe also provide the notation `Ω[S⁄R]` for `KaehlerDifferential R S`.\nNote that the slash is `\\textfractionsolidus`.\n def KaehlerDifferential : Type v :=",
    "KaehlerDifferential.D": "The universal derivation into `Ω[S⁄R]`.  def KaehlerDifferential.D : Derivation R S Ω[S⁄R] :=",
    "KaehlerDifferential.DLinearMap": "(Implementation) The underlying linear map of the derivation into `Ω[S⁄R]`.  def KaehlerDifferential.DLinearMap : S →ₗ[R] Ω[S⁄R] :=",
    "KaehlerDifferential.D_apply": " theorem KaehlerDifferential.D_apply (s : S) :\n    KaehlerDifferential.D R S s =\n      (KaehlerDifferential.ideal R S).toCotangent\n        ⟨1 ⊗ₜ s - s ⊗ₜ 1, KaehlerDifferential.one_smul_sub_smul_one_mem_ideal R s⟩ :=",
    "KaehlerDifferential.D_ne_zero_of_transcendental": " theorem D_ne_zero_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :\n    KaehlerDifferential.D K F x ≠ 0 :=",
    "KaehlerDifferential.ideal": "The kernel of the multiplication map `S ⊗[R] S →ₐ[R] S`.  abbrev KaehlerDifferential.ideal : Ideal (S ⊗[R] S) :=",
    "KaehlerDifferential.isScalarTower_of_tower": " instance KaehlerDifferential.isScalarTower_of_tower {R₁ R₂ : Type*} [CommRing R₁] [CommRing R₂]\n    [Algebra R₁ S] [Algebra R₂ S] [SMul R₁ R₂]\n    [SMulCommClass R R₁ S] [SMulCommClass R R₂ S] [IsScalarTower R₁ R₂ S] :\n    IsScalarTower R₁ R₂ Ω[S⁄R] :=",
    "KaehlerDifferential.linearMapEquivDerivation": "The `S`-linear maps from `Ω[S⁄R]` to `M` are (`S`-linearly) equivalent to `R`-derivations\nfrom `S` to `M`.  @[simps! symm_apply apply_apply]\ndef KaehlerDifferential.linearMapEquivDerivation : (Ω[S⁄R] →ₗ[S] M) ≃ₗ[S] Derivation R S M :=",
    "KaehlerDifferential.mapBaseChange": "The lift of the map `Ω[A⁄R] →ₗ[A] Ω[B⁄R]` to the base change along `A → B`.\nThis is the first map in the exact sequence `B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`.  noncomputable def KaehlerDifferential.mapBaseChange : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R] :=",
    "KaehlerDifferential.mvPolynomialBasis": "`{ dx | x ∈ σ }` forms a basis of the relative differential module\nof a polynomial algebra `R[σ]`.  def KaehlerDifferential.mvPolynomialBasis (σ) :\n    Basis σ (MvPolynomial σ R) Ω[MvPolynomial σ R⁄R] :=",
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal": " theorem KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (a : S) :\n    (1 : S) ⊗ₜ[R] a - a ⊗ₜ[R] (1 : S) ∈ KaehlerDifferential.ideal R S :=",
    "KaehlerDifferential.polynomialEquiv": "The relative differential module of the univariate polynomial algebra `R[X]` is isomorphic to\n`R[X]` as an `R[X]`-module.  def KaehlerDifferential.polynomialEquiv : Ω[R[X]⁄R] ≃ₗ[R[X]] R[X] where\n  __ := derivative'.liftKaehlerDifferential\n  invFun := (Algebra.lsmul R R _).toLinearMap.flip (D R R[X] X)\n  left_inv := by\n    intro x\n    obtain ⟨x, rfl⟩ := linearCombination_surjective _ _ x\n    induction x using Finsupp.induction_linear with\n    | zero => simp\n    | add x y hx hy =>\n      simp only [map_add, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.flip_apply,\n        AlgHom.toLinear",
    "KaehlerDifferential.polynomialEquiv_D": " @[simp]\nlemma KaehlerDifferential.polynomialEquiv_D (P) :\n    polynomialEquiv R (D R R[X] P) = derivative P :=",
    "KaehlerDifferential.polynomialEquiv_symm": " @[simp]\nlemma KaehlerDifferential.polynomialEquiv_symm (P) :\n    (polynomialEquiv R).symm P = P • D R R[X] X :=",
    "KaehlerDifferential.polynomial_D_apply": " lemma KaehlerDifferential.polynomial_D_apply (P : R[X]) :\n    D R R[X] P = derivative P • D R R[X] X :=",
    "KaehlerDifferential.span_D_eq_top_of_transcendental": " theorem span_D_eq_top_of_transcendental (K : Type*) [Field K] {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)\n    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :\n    Submodule.span F ({KaehlerDifferential.D K F x} : Set (KaehlerDifferential K F)) = ⊤ :=",
    "KaehlerDifferential.span_range_eq_ideal": " theorem KaehlerDifferential.span_range_eq_ideal :\n    Ideal.span (Set.range fun s : S => (1 : S) ⊗ₜ[R] s - s ⊗ₜ[R] (1 : S)) =\n      KaehlerDifferential.ideal R S :=",
    "KaehlerDifferential.subsingleton_of_surjective": "`Ω[S⁄R]` is trivial if `R → S` is surjective.\nAlso see `Algebra.FormallyUnramified.iff_subsingleton_kaehlerDifferential`.  lemma KaehlerDifferential.subsingleton_of_surjective (h : Function.Surjective (algebraMap R S)) :\n    Subsingleton Ω[S⁄R] :=",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": "The canonical isomorphism `T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R]` for `T` a formally étale `S`-algebra.\nAlso see `S ⊗[R] Ω[A⁄R] ≃ₗ[S] Ω[S ⊗[R] A⁄S]` at `KaehlerDifferential.tensorKaehlerEquiv`.\n @[simps! apply] noncomputable\ndef KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale [Algebra.FormallyEtale S T] :\n    T ⊗[S] Ω[S⁄R] ≃ₗ[T] Ω[T⁄R] :=",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap": " lemma KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap\n    [Algebra.FormallyEtale S T] (s : S) :\n    (tensorKaehlerEquivOfFormallyEtale R S T).symm (D R T (algebraMap S T s)) = 1 ⊗ₜ D R S s :=",
    "KaehlerDifferential.tensorProductTo_surjective": " theorem KaehlerDifferential.tensorProductTo_surjective :\n    Function.Surjective (KaehlerDifferential.D R S).tensorProductTo :=",
    "LinearEquiv": "A linear equivalence is an invertible linear map.  structure LinearEquiv {R : Type*} {S : Type*} [Semiring R] [Semiring S] (σ : R →+* S)\n  {σ' : S →+* R} [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] (M : Type*) (M₂ : Type*)\n  [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module S M₂] extends LinearMap σ M M₂, M ≃+ M₂",
    "LinearEquiv.ofBijective": "A bijective linear map is a linear equivalence.  noncomputable def ofBijective [RingHomInvPair σ₁₂ σ₂₁] [RingHomInvPair σ₂₁ σ₁₂] (hf : Bijective f) :\n    M ≃ₛₗ[σ₁₂] M₂ :=",
    "LinearEquiv.symm": "Linear equivalences are symmetric.  @[symm, implicit_reducible]\ndef symm (e : M ≃ₛₗ[σ] M₂) : M₂ ≃ₛₗ[σ'] M :=",
    "LinearEquiv.trans": "Linear equivalences are transitive.  -- Note: the `RingHomCompTriple σ₃₂ σ₂₁ σ₃₁` is unused, but is convenient to carry around\n-- implicitly for lemmas like `LinearEquiv.self_trans_symm`.\n@[trans, nolint unusedArguments]\ndef trans\n    [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] [RingHomCompTriple σ₃₂ σ₂₁ σ₃₁]\n    {re₁₂ : RingHomInvPair σ₁₂ σ₂₁} {re₂₃ : RingHomInvPair σ₂₃ σ₃₂}\n    [RingHomInvPair σ₁₃ σ₃₁] {re₂₁ : RingHomInvPair σ₂₁ σ₁₂}\n    {re₃₂ : RingHomInvPair σ₃₂ σ₂₃} [RingHomInvPair σ₃₁ σ₁₃]\n    (e₁₂ : M₁ ≃ₛₗ[σ₁₂] M₂) (e₂₃ : M₂ ≃ₛₗ[σ₂₃] M₃) : M₁ ≃ₛₗ[σ₁₃] M₃ :=",
    "LinearIndependent": "`LinearIndependent R v` states the family of vectors `v` is linearly independent over `R`.  def LinearIndependent : Prop :=",
    "LinearIndependent.finrank_eq_zero_of_infinite": " lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}\n    (hv : LinearIndependent R v) : finrank R M = 0 :=",
    "LinearMap": "A map `f` between an `R`-module and an `S`-module over a ring homomorphism `σ : R →+* S`\nis semilinear if it satisfies the two properties `f (x + y) = f x + f y` and\n`f (c • x) = (σ c) • f x`. Elements of `LinearMap σ M M₂` (available under the notation\n`M →ₛₗ[σ] M₂`) are bundled versions of such maps. For plain linear maps (i.e. for which\n`σ = RingHom.id R`), the notation `M →ₗ[R] M₂` is available. An unbundled version of plain linear\nmaps is available with the predicate `IsLinearMap`, but it should be avoided most of the time.  structure LinearMap {R S : Type*} [Semiring R] [Semiring S] (σ :",
    "LinearMap.addCommMonoid": "The type of linear maps is an additive monoid.  instance addCommMonoid : AddCommMonoid (M →ₛₗ[σ₁₂] M₂) :=",
    "LinearMap.comp": "Composition of two linear maps is a linear map  @[instance_reducible]\ndef comp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃] (f : M₂ →ₛₗ[σ₂₃] M₃) (g : M₁ →ₛₗ[σ₁₂] M₂) :\n    M₁ →ₛₗ[σ₁₃] M₃ where\n  toFun x := f (g x)\n  map_add' := by simp only [map_add, forall_const]\n  -- Note that https://github.com/leanprover-community/mathlib4/pull/8386 changed `map_smulₛₗ` to `map_smulₛₗ _`\n  map_smul' r x := by simp only [map_smulₛₗ _, RingHomCompTriple.comp_apply]",
    "LinearMap.flip": "Given a linear map from `M` to linear maps from `N` to `P`, i.e., a bilinear map from `M × N` to\n`P`, change the order of variables and get a linear map from `N` to linear maps from `M` to `P`.  def flip (f : M →ₛₗ[ρ₁₂] N →ₛₗ[σ₁₂] P) : N →ₛₗ[σ₁₂] M →ₛₗ[ρ₁₂] P :=",
    "LinearMap.ker": "The kernel of a linear map `f : M → M₂` is defined to be `comap f ⊥`. This is equivalent to the\nset of `x : M` such that `f x = 0`. The kernel is a submodule of `M`.  def ker (f : M →ₛₗ[τ₁₂] M₂) : Submodule R M :=",
    "LinearMap.lsmul": "Scalar multiplication as a bilinear map `R → M → M`.  def lsmul : R →ₗ[R] M →ₗ[R] M :=",
    "LinearMap.mk₂": "Create a bilinear map from a function that is linear in each component.\n\nThis is a shorthand for `mk₂'` for the common case when `R = S`.  def mk₂ (f : M → Nₗ → Pₗ) (H1 : ∀ m₁ m₂ n, f (m₁ + m₂) n = f m₁ n + f m₂ n)\n    (H2 : ∀ (c : R) (m n), f (c • m) n = c • f m n)\n    (H3 : ∀ m n₁ n₂, f m (n₁ + n₂) = f m n₁ + f m n₂)\n    (H4 : ∀ (c : R) (m n), f m (c • n) = c • f m n) : M →ₗ[R] Nₗ →ₗ[R] Pₗ :=",
    "LinearMap.module": " instance module : Module S (M →ₛₗ[σ₁₂] M₂) where\n  add_smul _ _ _ := ext fun _ ↦ add_smul _ _ _\n  zero_smul _ := ext fun _ ↦ zero_smul _ _",
    "LinearMap.mul": "The multiplication in a non-unital non-associative algebra is a bilinear map.\n\nA weaker version of this for semirings exists as `AddMonoidHom.mul`.  @[instance_reducible, simps!]\ndef mul : A →ₗ[R] A →ₗ[R] A :=",
    "LinearMap.range": "The range of a linear map `f : M → M₂` is a submodule of `M₂`.\nSee Note [range copy pattern].  def range [RingHomSurjective τ₁₂] (f : M →ₛₗ[τ₁₂] M₂) : Submodule R₂ M₂ :=",
    "LinearMap.restrictScalars": "If `M` and `M₂` are both `R`-modules and `S`-modules and `R`-module structures\nare defined by an action of `R` on `S` (formally, we have two scalar towers), then any `S`-linear\nmap from `M` to `M₂` is `R`-linear.\n\nSee also `LinearMap.map_smul_of_tower`.  @[coe] def restrictScalars (fₗ : M →ₗ[S] M₂) : M →ₗ[R] M₂ where\n  toFun := fₗ\n  map_add' := fₗ.map_add\n  map_smul' := fₗ.map_smul_of_tower",
    "List.Pairwise": "Each element of a list is related to all later elements of the list by `R`.\n\n`Pairwise R l` means that all the elements of `l` with earlier indexes are `R`-related to all the\nelements with later indexes.\n\nFor example, `Pairwise (· ≠ ·) l` asserts that `l` has no duplicates, and `Pairwise (· < ·) l`\nasserts that `l` is (strictly) sorted.\n\nExamples:\n * `Pairwise (· < ·) [1, 2, 3] ↔ (1 < 2 ∧ 1 < 3) ∧ 2 < 3`\n * `Pairwise (· = ·) [1, 2, 3] = False`\n * `Pairwise (· ≠ ·) [1, 2, 3] = True`\n inductive Pairwise : List α → Prop\n  /-- All elements of the empty list are vacuously pairwise related. -/\n  | n",
    "Max.max": "Returns the greater of its two arguments. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `max` in identifiers is `max`.\n\n * The recommended spelling of `⊔` in identifiers is `sup` (`⊔` is the preferred notation for `max` when the type is not linearly ordered.). ",
    "Min.min": "Returns the lesser of its two arguments. \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `min` in identifiers is `min`.\n\n * The recommended spelling of `⊓` in identifiers is `inf` (`⊓` is the preferred notation for `min` when the type is not linearly ordered.). ",
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax": "`deg((ω)) = 2γ - 2` from the same hypothesis (pin 6110).  theorem wkc_degree_canonicalDivisor_eq_of_weilMax\n    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)\n    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),\n      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧\n      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)\n    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :\n    Divisor.degree (canonicalDivisorOf hω) = 2 * γ - 2 :=",
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax": "`ℓ((ω)) = γ` from the maximal-functional hypothesis (pin 6093).  theorem wkc_ell_canonicalDivisor_eq_gamma_of_weilMax\n    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)\n    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),\n      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧\n      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)\n    (hC : ConstantsAreBase K F) {ω : Ω[F⁄K]} (hω : ω ≠ 0) :\n    (ell (canonicalDivisorOf hω) : ℤ) = γ :=",
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax": "`dim Ω(D) = ℓ((ω) - D)` from a maximal functional and a reached genus (pin 6080).  theorem wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax\n    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0)\n    {φ : Module.Dual K (adeleSpace K F)} (hne : φ ≠ 0)\n    (hmem : φ ∈ omegaSpace (canonicalDivisorOf hω))\n    (hmax : ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)\n    (D : Divisor K F) :\n    Module.finrank K (omegaSpace (K := K) (F := F) D) = ell (canonicalDivisorOf hω - D) :=",
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK": "Riemann–Roch from the K residue theorem and `ConstantsAreBase` (pin 6208).  theorem wkc_functionFieldRiemannRoch_of_residueTheoremK\n    [HasSeparableResidue K F]\n    (hRTK : ResidueTheoremK K F) (hC : ConstantsAreBase K F) :\n    FunctionFieldRiemannRoch K F :=",
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax": "The Riemann index formula from the maximal-functional hypothesis (pin 6167).  theorem wkc_riemannIndexFormula_of_weilMax\n    (hsup : ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0), ∃ φ : Module.Dual K (adeleSpace K F),\n      φ ≠ 0 ∧ φ ∈ omegaSpace (canonicalDivisorOf hω) ∧\n      ∀ D : Divisor K F, φ ∈ omegaSpace D → D ≤ canonicalDivisorOf hω)\n    (hC : ConstantsAreBase K F) :\n    RiemannIndexFormula K F :=",
    "ModularCurve.wkc_weilOfKaehlerK_single": "The Weil–Kähler functional on one adele: the trace of its local residue (pin 5992).  theorem wkc_weilOfKaehlerK_single\n    (Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK)\n    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) (g : F) :\n    weilOfKaehlerK Rfam hω (adeleSingle v g)\n      = Algebra.trace K v.ResidueField ((Rfam v).res (g * v.differentialCoeff ω)) :=",
    "Module": "A module is a generalization of vector spaces to a scalar semiring.\nIt consists of a scalar semiring `R` and an additive monoid of \"vectors\" `M`,\nconnected by a \"scalar multiplication\" operation `r • x : M`\n(where `r : R` and `x : M`) with some natural associativity and\ndistributivity axioms similar to those on a ring.  @[ext]\nclass Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends\n  DistribMulAction R M where\n  /-- Scalar multiplication distributes over addition from the right. -/\n  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x\n  /-- Scalar multip",
    "Module.Basis": "A `Basis ι R M` for a module `M` is the type of `ι`-indexed `R`-bases of `M`.\n\nThe basis vectors are available as `DFunLike.coe (b : Basis ι R M) : ι → M`.\nTo turn a linear independent family of vectors spanning `M` into a basis, use `Basis.mk`.\nThey are internally represented as linear equivs `M ≃ₗ[R] (ι →₀ R)`,\navailable as `Basis.repr`.\n @[wikidata Q189569]\nstructure Basis where\n  /-- `Basis.ofRepr` constructs a basis given an assignment of coordinates to each vector. -/\n  ofRepr ::\n    /-- `repr` is the linear equivalence sending a vector `x` to its coordinates:\n    the `c`s such that `x =",
    "Module.Basis.baseChange": "The lift of an `R`-basis of `M` to an `S`-basis of the base change `S ⊗[R] M`.  noncomputable\ndef baseChange (b : Basis ι R M) : Basis ι S (S ⊗[R] M) :=",
    "Module.Basis.map": "Apply the linear equivalence `f` to the basis vectors.  @[simps]\nprotected def map : Basis ι R M' :=",
    "Module.Basis.ne_zero": " protected theorem ne_zero [Nontrivial R] (i) : b i ≠ 0 :=",
    "Module.Basis.reindex": "`b.reindex (e : ι ≃ ι')` is a basis indexed by `ι'`  def reindex : Basis ι' R M :=",
    "Module.Basis.repr": "`repr` is the linear equivalence sending a vector `x` to its coordinates:\nthe `c`s such that `x = ∑ i, c i`.  ",
    "Module.Basis.singleton": "`Basis.singleton ι R` is the basis sending the unique element of `ι` to `1 : R`.  protected def singleton (ι R : Type*) [Unique ι] [Semiring R] : Basis ι R R :=",
    "Module.Basis.span_eq": " @[simp]\nprotected theorem span_eq : span R (range b) = ⊤ :=",
    "Module.Basis.tensorProduct": "If `b : ι → M` and `c : κ → N` are bases then so is `fun i ↦ b i.1 ⊗ₜ c i.2 : ι × κ → M ⊗ N`.  def tensorProduct (b : Basis ι S M) (c : Basis κ R N) :\n    Basis (ι × κ) S (M ⊗[R] N) :=",
    "Module.Dual": "The left dual space of an R-module M is the R-module of linear maps `M → R`.  @[wikidata Q752487]\nabbrev Dual (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M] :=",
    "Module.End": "Linear endomorphisms of a module, with associated ring structure\n`Module.End.semiring` and algebra structure `Module.End.algebra`.  abbrev Module.End (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] :=",
    "Module.Finite": "A module over a semiring is `Module.Finite` if it is finitely generated as a module.  protected class Module.Finite [Semiring R] [AddCommMonoid M] [Module R M] : Prop where\n  of_fg_top ::\n    fg_top : (⊤ : Submodule R M).FG",
    "Module.Free": "`Module.Free R M` is the statement that the `R`-module `M` is free.  class Free (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Prop where\n  exists_basis (R M) : Nonempty <| (I : Type v) × Basis I R M",
    "Module.finrank": "The rank of a module as a natural number.\n\nFor a finite-dimensional vector space `V` over a field `k`, `Module.finrank k V` is equal to\nthe dimension of `V` over `k`.\n\nFor a general module `M` over a ring `R`, `Module.finrank R M` is defined to be the supremum of the\ncardinalities of the `R`-linearly independent subsets of `M`, if this supremum is finite. It is\ndefined by convention to be `0` if this supremum is infinite. See `Module.rank` for a\ncardinal-valued version where infinite rank modules have rank an infinite cardinal.\n\nNote that if `R` is not a field then there can exist modules `M` ",
    "Module.rank": "The rank of a module, defined as a term of type `Cardinal`.\n\nWe define this as the supremum of the cardinalities of linearly independent subsets.\nThe supremum may not be attained, see https://mathoverflow.net/a/263053.\n\nFor a free module over any ring satisfying the strong rank condition\n(e.g. left-Noetherian rings, commutative rings, and in particular division rings and fields),\nthis is the same as the dimension of the space (i.e. the cardinality of any basis).\n\nIn particular this agrees with the usual notion of the dimension of a vector space.\n\nSee also `Module.finrank` for a `ℕ`-valued func",
    "Monoid": "A `Monoid` is a `Semigroup` with an element `1` such that `1 * a = a * 1 = a`.  @[to_additive]\nclass Monoid (M : Type*) extends One M, Mul M, Semigroup M, MulOneClass M, NPow M where\n  npow := npowRecAuto\n  /-- Raising to the power `(0 : ℕ)` gives `1`. -/\n  protected npow_zero (x : M) : x ^ 0 = 1 := by intros; rfl\n  /-- Raising to the power `(n + 1 : ℕ)` behaves as expected. -/\n  protected npow_succ (n : ℕ) (x : M) : x ^ (n + 1) = x ^ n * x := by intros; rfl",
    "MonoidWithZeroHom": "`α →*₀ β` is the type of functions `α → β` that preserve\nthe `MonoidWithZero` structure.\n\n`MonoidWithZeroHom` is also used for group homomorphisms.\n\nWhen possible, instead of parametrizing results over `(f : α →*₀ β)`,\nyou should parametrize over `(F : Type*) [MonoidWithZeroHomClass F α β] (f : F)`.\n\nWhen you extend this structure, make sure to extend `MonoidWithZeroHomClass`.  structure MonoidWithZeroHom (α β : Type*) [MulZeroOneClass α] [MulZeroOneClass β]\n  extends ZeroHom α β, MonoidHom α β",
    "MonoidWithZeroHom.funLike": " @[macro_inline]\ninstance funLike : FunLike (α →*₀ β) α β where\n  coe f := f.toFun\n  coe_injective f g h := by obtain ⟨⟨_, _⟩, _⟩ := f; obtain ⟨⟨_, _⟩, _⟩ := g; congr",
    "Mul": "The homogeneous version of `HMul`: `a * b : α` where `a b : α`.  class Mul (α : Type u) where\n  /-- `a * b` computes the product of `a` and `b`. See `HMul`. -/\n  mul : α → α → α",
    "MulAction": "Type class for monoid actions on types, with notation `g • p`.\n\nThe `MulAction G P` typeclass says that the monoid `G` acts multiplicatively on a type `P`.\nMore precisely this means that the action satisfies the two axioms `1 • p = p` and\n`(g₁ * g₂) • p = g₁ • (g₂ • p)`. A mathematician might simply say that the monoid `G`\nacts on `P`.\n\nFor example, if `G` is a group and `X` is a type, if a mathematician says\nsay \"let `G` act on the set `X`\" they will probably mean `[MulAction G X]`.\n\n\n[Wikidata Q288465](https://www.wikidata.org/wiki/Q288465) @[to_additive (attr := ext, wikidata Q288465)]\nclas",
    "Multiplicative": "If `α` carries some additive structure, then `Multiplicative α` carries the corresponding\nmultiplicative structure.  def Multiplicative (α : Type*) :=",
    "Multiplicative.commMonoid": " instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=",
    "Multiplicative.group": " instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=",
    "Multiplicative.isOrderedCancelMonoid": " instance Multiplicative.isOrderedCancelMonoid\n    [AddCommMonoid α] [Preorder α] [IsOrderedCancelAddMonoid α] :\n    IsOrderedCancelMonoid (Multiplicative α) :=",
    "Multiplicative.linearOrder": " instance Multiplicative.linearOrder [LinearOrder α] : LinearOrder (Multiplicative α) :=",
    "Multiplicative.monoid": " instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where\n  npow n a := ofAdd (n • a.toAdd)\n  npow_zero := h.nsmul_zero\n  npow_succ := h.nsmul_succ",
    "Multiplicative.mul": " instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where\n  mul x y := ofAdd (x.toAdd + y.toAdd)",
    "Multiplicative.ofAdd": "Reinterpret `x : α` as an element of `Multiplicative α`.  @[implicit_reducible]\ndef ofAdd : α ≃ Multiplicative α :=",
    "Multiplicative.preorder": " instance Multiplicative.preorder [Preorder α] : Preorder (Multiplicative α) :=",
    "MvPolynomial": "Multivariate polynomial, where `σ` is the index set of the variables and\n`R` is the coefficient ring  abbrev MvPolynomial (σ : Type*) (R : Type*) [CommSemiring R] :=",
    "MvPolynomial.X": "`X n` is the degree `1` monomial $X_n$.  def X (n : σ) : MvPolynomial σ R :=",
    "MvPolynomial.aeval": "A map `σ → S₁` where `S₁` is an algebra over `R` generates an `R`-algebra homomorphism\nfrom multivariate polynomials over `σ` to `S₁`.  def aeval : MvPolynomial σ R →ₐ[R] S₁ :=",
    "Nat": "The natural numbers, starting at zero.\n\nThis type is special-cased by both the kernel and the compiler, and overridden with an efficient\nimplementation. Both use a fast arbitrary-precision arithmetic library (usually\n[GMP](https://gmplib.org/)); at runtime, `Nat` values that are sufficiently small are unboxed.\n @[suggest_for ℕ]\ninductive Nat where\n  /--\n  Zero, the smallest natural number.\n\n  Using `Nat.zero` explicitly should usually be avoided in favor of the literal `0`, which is the\n  [simp normal form](lean-manual://section/simp-normal-forms).\n  -/\n  | zero : Nat\n  /--\n  The successor of ",
    "Nat.Coprime": "`m` and `n` are coprime, or relatively prime, if their `gcd` is 1.  @[reducible, expose] def Coprime (m n : Nat) : Prop :=",
    "Nat.Prime": "`Nat.Prime p` means that `p` is a prime number, that is, a natural number\nat least 2 whose only divisors are `p` and `1`.\nThe theorem `Nat.prime_def` witnesses this description of a prime number.  @[pp_nodot, wikidata Q49008]\ndef Prime (p : ℕ) :=",
    "Nat.card": "`Nat.card α` is the cardinality of `α` as a natural number.\nIf `α` is infinite, `Nat.card α = 0`.  protected def card (α : Type*) : ℕ :=",
    "Nat.cast": "The canonical homomorphism `Nat → R`. In most use cases, the target type will have a (semi)ring\nstructure, and this homomorphism should be a (semi)ring homomorphism.\n\n`NatCast` and `IntCast` exist to allow different libraries with their own types that can be notated\nas natural numbers to have consistent `simp` normal forms without needing to create coercion\nsimplification sets that are aware of all combinations. Libraries should make it easy to work with\n`NatCast` where possible. For instance, in Mathlib there will be such a homomorphism (and thus a\n`NatCast R` instance) whenever `R` is an add",
    "Nat.recOnPosPrimePosCoprime": "Given `P 0`, `P 1`, and `P (p ^ n)` for positive prime powers, and a way to extend `P a` and\n`P b` to `P (a * b)` when `a, b` are positive coprime, we can define `P` for all natural numbers.  @[elab_as_elim]\ndef recOnPosPrimePosCoprime {motive : ℕ → Sort*}\n    (prime_pow : ∀ p n : ℕ, Prime p → 0 < n → motive (p ^ n))\n    (zero : motive 0) (one : motive 1)\n    (coprime : ∀ a b, 1 < a → 1 < b → Coprime a b → motive a → motive b → motive (a * b)) :\n    ∀ a, motive a :=",
    "Nat.recOnPrimePow": "Given `P 0, P 1` and a way to extend `P a` to `P (p ^ n * a)` for prime `p` not dividing `a`,\nwe can define `P` for all natural numbers.  @[elab_as_elim]\ndef recOnPrimePow {motive : ℕ → Sort*} (zero : motive 0) (one : motive 1)\n    (prime_pow_mul : ∀ a p n : ℕ, p.Prime → ¬p ∣ a → 0 < n → motive a → motive (p ^ n * a)) :\n    ∀ a, motive a :=",
    "Ne": "`a ≠ b`, or `Ne a b` is defined as `¬ (a = b)` or `a = b → False`,\nand asserts that `a` and `b` are not equal.\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `≠` in identifiers is `ne`. @[reducible] def Ne {α : Sort u} (a b : α) :=",
    "NoZeroDivisors": "Predicate typeclass for expressing that `a * b = 0` implies `a = 0` or `b = 0`\nfor all `a` and `b` of type `M₀`. It is weaker than `IsCancelMulZero` in general,\nbut equivalent to it if `M₀` is a (not necessarily unital or associative) ring.  @[mk_iff] class NoZeroDivisors (M₀ : Type*) [Mul M₀] [Zero M₀] : Prop where\n  /-- For all `a` and `b` of `M₀`, `a * b = 0` implies `a = 0` or `b = 0`. -/\n  eq_zero_or_eq_zero_of_mul_eq_zero : ∀ {a b : M₀}, a * b = 0 → a = 0 ∨ b = 0",
    "NonUnitalNonAssocSemiring": "A not-necessarily-unital, not-necessarily-associative semiring. See `CommutatorRing` and the\ndocumentation thereof in case you need a `NonUnitalNonAssocSemiring` instance on a Lie ring\nor a Lie algebra.  class NonUnitalNonAssocSemiring (α : Type u) extends AddCommMonoid α, Distrib α, MulZeroClass α",
    "Nonempty": "`Nonempty α` is a typeclass that says that `α` is not an empty type,\nthat is, there exists an element in the type. It differs from `Inhabited α`\nin that `Nonempty α` is a `Prop`, which means that it does not actually carry\nan element of `α`, only a proof that *there exists* such an element.\nGiven `Nonempty α`, you can construct an element of `α` *nonconstructively*\nusing `Classical.choice`.\n class inductive Nonempty (α : Sort u) : Prop where\n  /-- If `val : α`, then `α` is nonempty. -/\n  | intro (val : α) : Nonempty α",
    "Nontrivial": "Predicate typeclass for expressing that a type is not reduced to a single element. In rings,\nthis is equivalent to `0 ≠ 1`. In vector spaces, this is equivalent to positive dimension.  class Nontrivial (α : Type*) : Prop where\n  /-- In a nontrivial type, there exists a pair of distinct terms. -/\n  exists_pair_ne : ∃ x y : α, x ≠ y",
    "Odd": "An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`.  def Odd (a : α) : Prop :=",
    "Option": "Optional values, which are either `some` around a value from the underlying type or `none`.\n\n`Option` can represent nullable types or computations that might fail. In the codomain of a function\ntype, it can also represent partiality.\n @[suggest_for Maybe, suggest_for Optional, suggest_for Nullable]\ninductive Option (α : Type u) where\n  /-- No value. -/\n  | none : Option α\n  /-- Some value of type `α`. -/\n  | some (val : α) : Option α",
    "Option.map₂": "The image of a binary function `f : α → β → γ` as a function `Option α → Option β → Option γ`.\nMathematically this should be thought of as the image of the corresponding function `α × β → γ`.  def map₂ (f : α → β → γ) (a : Option α) (b : Option β) : Option γ :=",
    "OreLocalization.oreSetComm": "Every submonoid of a commutative monoid is an Ore set.  @[to_additive AddOreLocalization.addOreSetComm\n/-- Every submonoid of an additive commutative monoid is an Ore set. -/]\ninstance (priority := 100) oreSetComm {R} [CommMonoid R] (S : Submonoid R) : OreSet S where\n  ore_right_cancel m n s h := ⟨s, by rw [mul_comm (s : R) n, mul_comm (s : R) m, h]⟩\n  oreNum r _ := r\n  oreDenom _ s := s\n  ore_eq r s := by rw [mul_comm]",
    "PerfectField": "A perfect field.\n\nSee also `PerfectRing` for a generalisation in positive characteristic.  class PerfectField (K : Type*) [Field K] : Prop where\n  /-- A field is perfect if every irreducible polynomial is separable. -/\n  separable_of_irreducible : ∀ {f : K[X]}, Irreducible f → f.Separable",
    "Pi.Function.module": "A special case of `Pi.module` for non-dependent types. Lean struggles to elaborate\ndefinitions elsewhere in the library without this.  instance Function.module (α β : Type*) [Semiring α] [AddCommMonoid β] [Module α β] :\n    Module α (I → β) :=",
    "Pi.addCommGroup": " ",
    "Pi.addCommMonoid": " ",
    "Pi.isScalarTower": " @[to_additive]\ninstance isScalarTower [SMul M N] [∀ i, SMul N (α i)] [∀ i, SMul M (α i)]\n    [∀ i, IsScalarTower M N (α i)] : IsScalarTower M N (∀ i, α i) where\n  smul_assoc x y z := funext fun i ↦ smul_assoc x y (z i)",
    "Pi.nonAssocSemiring": " instance nonAssocSemiring [∀ i, NonAssocSemiring <| f i] : NonAssocSemiring (∀ i : I, f i) :=",
    "Polynomial": "`Polynomial R` is the type of univariate polynomials over `R`,\ndenoted as `R[X]` within the `Polynomial` namespace.\n\nPolynomials should be seen as (semi-)rings with the additional constructor `X`.\nThe embedding from `R` is called `C`.  @[wikidata Q43260]\nstructure Polynomial (R : Type*) [Semiring R] where ofFinsupp ::\n  /-- The coefficients `ℕ →₀ R` of a polynomial in `R[X]`. -/\n  toFinsupp : AddMonoidAlgebra R ℕ",
    "Polynomial.C": "`C a` is the constant polynomial `a`.\n`C` is provided as a ring homomorphism.\n def C : R →+* R[X] :=",
    "Polynomial.CC": "A constant viewed as a polynomial in two variables.  abbrev CC (r : R) : R[X][Y] :=",
    "Polynomial.Separable": "A polynomial is separable iff it is coprime with its derivative.  @[stacks 09H1 \"first part\"]\ndef Separable (f : R[X]) : Prop :=",
    "Polynomial.X": "`X` is the polynomial variable (aka indeterminate).  def X : R[X] :=",
    "Polynomial.algEquivOfTranscendental": "Given a transcendental element `s : S` over `R`, the `R`-algebra equivalence\nbetween `R[X]` and `R[s]` given by sending `X` to `s`.  noncomputable def algEquivOfTranscendental (s : S) (h : Transcendental R s) :\n    R[X] ≃ₐ[R] R[s] :=",
    "Polynomial.algebraOfAlgebra": "Note that this instance also provides `Algebra R R[X]`.  instance algebraOfAlgebra : Algebra R A[X] where\n  smul_def' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      rw [toFinsupp_smul, toFinsupp_mul, toFinsupp_C]\n      exact Algebra.smul_def' _ _\n  commutes' r p :=\n    toFinsupp_injective <| by\n      dsimp only [RingHom.toFun_eq_coe, RingHom.comp_apply]\n      simp_rw [toFinsupp_mul, toFinsupp_C]\n      convert! Algebra.commutes' r p.toFinsupp\n  algebraMap := C.comp (algebraMap R A)",
    "Polynomial.degree": "`degree p` is the degree of the polynomial `p`, i.e. the largest `X`-exponent in `p`.\n`degree p = some n` when `p ≠ 0` and `n` is the highest power of `X` that appears in `p`, otherwise\n`degree 0 = ⊥`.  def degree (p : R[X]) : WithBot ℕ :=",
    "Polynomial.derivative": "`derivative p` is the formal derivative of the polynomial `p`  def derivative : R[X] →ₗ[R] R[X] where\n  toFun p := p.sum fun n a => C (a * n) * X ^ (n - 1)\n  map_add' p q := by\n    rw [sum_add_index] <;>\n      simp only [add_mul, forall_const, map_add, zero_mul, map_zero]\n  map_smul' a p := by\n    dsimp; rw [sum_smul_index] <;>\n      simp only [mul_sum, ← C_mul', mul_assoc, map_mul, forall_const, zero_mul, map_zero, sum]",
    "Polynomial.derivative'": "`Polynomial.derivative` as a derivation.  @[simps]\ndef derivative' : Derivation R R[X] R[X] where\n  toFun := derivative\n  map_add' _ _ := derivative_add\n  map_smul' := derivative_smul\n  map_one_eq_zero' := derivative_one\n  leibniz' f g := by simp [mul_comm, add_comm, derivative_mul]",
    "Polynomial.eval": "`eval x p` is the evaluation of the polynomial `p` at `x`  def eval (x : R) (p : R[X]) : R :=",
    "Polynomial.evalEval": "`evalEval x y p` is the evaluation `p(x,y)` of a two-variable polynomial `p : R[X][Y]`.  abbrev evalEval (x y : R) (p : R[X][Y]) : R :=",
    "Polynomial.module": " instance module {S} [Semiring S] [Module S R] : Module S R[X] :=",
    "Polynomial.monomial": "`monomial s a` is the monomial `a * X^s`  def monomial (n : ℕ) : R →ₗ[R] R[X] where\n  toFun t := ⟨.single n t⟩\n  map_add' x y := by simp [← ofFinsupp_add]\n  map_smul' r x := by simp [← ofFinsupp_smul]",
    "Polynomial.natDegree": "`natDegree p` forces `degree p` to ℕ, by defining `natDegree 0 = 0`.  def natDegree (p : R[X]) : ℕ :=",
    "Preorder": "A preorder is a reflexive, transitive relation `≤`.\nIn a preorder, `a < b` means `a ≤ b ∧ ¬b ≤ a`, and `<` is defined this way by default.\nYou can override this definition to set a better def-eq.\n class Preorder (α : Type*) extends LE α, LT α where\n  protected le_refl : ∀ a : α, a ≤ a\n  protected le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c\n  lt := fun a b => a ≤ b ∧ ¬b ≤ a\n  protected lt_iff_le_not_ge : ∀ a b : α, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl",
    "Prod": "The product type, usually written `α × β`. Product types are also called pair or tuple types.\nElements of this type are pairs in which the first element is an `α` and the second element is a\n`β`.\n\nProducts nest to the right, so `(x, y, z) : α × β × γ` is equivalent to `(x, (y, z)) : α × (β × γ)`.\n\n\nConventions for notations in identifiers:\n\n * The recommended spelling of `×` in identifiers is `Prod`. structure Prod (α : Type u) (β : Type v) where\n  /--\n  Constructs a pair. This is usually written `(x, y)` instead of `Prod.mk x y`.\n  -/\n  mk ::\n  /-- The first element of a pair. -/\n  fst : α\n  ",
    "QuotientAddGroup.Quotient.addCommGroup": " ",
    "QuotientAddGroup.mk": "The canonical map from an `AddGroup` `α` to the quotient `α ⧸ s`.  ",
    "RatFunc": "`RatFunc K` is `K(X)`, the field of rational functions over `K`.\n\nThe inclusion of polynomials into `RatFunc` is `algebraMap K[X] K⟮X⟯`,\nthe maps between `K⟮X⟯` and another field of fractions of `K[X]`,\nespecially `FractionRing K[X]`, are given by `IsLocalization.algEquiv`.\n structure RatFunc [CommRing K] : Type u where ofFractionRing ::\n/-- the coercion to the fraction ring of the polynomial ring -/\n  toFractionRing : FractionRing K[X]",
    "RatFunc.X": "`RatFunc.X` is the polynomial variable (aka indeterminate).  def X : K⟮X⟯ :=",
    "RatFunc.algEquivOfTranscendental": "Given a transcendental `f : L`, the `K`-algebra isomorphism between `RatFunc K` and `L` given\nby sending `X` to `f`.  noncomputable def algEquivOfTranscendental : RatFunc K ≃ₐ[K] K⟮f⟯ :=",
    "RatFunc.algEquivOfTranscendental_X": " @[simp]\ntheorem algEquivOfTranscendental_X :\n    algEquivOfTranscendental f h (X : RatFunc K) = f :=",
    "Ring": "A `Ring` is a `Semiring` with negation making it an additive group.  @[wikidata Q161172]\nclass Ring (R : Type u) extends Semiring R, AddCommGroup R, AddGroupWithOne R",
    "RingEquiv": "An equivalence between two (non-unital non-associative semi)rings that preserves the\nalgebraic structure.  structure RingEquiv (R S : Type*) [Mul R] [Mul S] [Add R] [Add S] extends R ≃ S, R ≃* S, R ≃+ S",
    "RingHom": "Bundled semiring homomorphisms; use this for bundled ring homomorphisms too.\n\nThis extends from both `MonoidHom` and `MonoidWithZeroHom` in order to put the fields in a\nsensible order, even though `MonoidWithZeroHom` already extends `MonoidHom`.  @[wikidata Q1194212]\nstructure RingHom (α : Type*) (β : Type*) [NonAssocSemiring α] [NonAssocSemiring β] extends\n  α →* β, α →+ β, α →ₙ+* β, α →*₀ β",
    "RingHom.comp": "Composition of ring homomorphisms is a ring homomorphism.  @[instance_reducible]\ndef comp (g : β →+* γ) (f : α →+* β) : α →+* γ :=",
    "RingHom.id": "The identity ring homomorphism from a semiring to itself.  @[instance_reducible]\ndef id (α : Type*) [NonAssocSemiring α] : α →+* α where\n  toFun x := x\n  map_zero' := rfl\n  map_one' := rfl\n  map_add' _ _ := rfl\n  map_mul' _ _ := rfl",
    "RingHom.ker": "Kernel of a ring homomorphism as an ideal of the domain.  def ker : Ideal R :=",
    "RingHom.kerLift": "The induced map from the quotient by the kernel to the codomain.\n\nThis is an isomorphism if `f` has a right inverse (`quotientKerEquivOfRightInverse`) /\nis surjective (`quotientKerEquivOfSurjective`).\n def kerLift : R ⧸ ker f →+* S :=",
    "RingHom.mem_ker": "An element is in the kernel if and only if it maps to zero.  @[simp] theorem mem_ker {r} : r ∈ ker f ↔ f r = 0 :=",
    "RingHom.quotientKerEquivOfRightInverse": "The **first isomorphism theorem for commutative rings**, computable version.  def quotientKerEquivOfRightInverse {g : S → R} (hf : Function.RightInverse g f) :\n    R ⧸ ker f ≃+* S :=",
    "RingHom.quotientKerEquivOfSurjective": "The **first isomorphism theorem** for commutative rings, surjective case.  noncomputable def quotientKerEquivOfSurjective (hf : Function.Surjective f) : R ⧸ (ker f) ≃+* S :=",
    "RingHomClass": "`RingHomClass F α β` states that `F` is a type of (semi)ring homomorphisms.\nYou should extend this class when you extend `RingHom`.\n\nThis extends from both `MonoidHomClass` and `MonoidWithZeroHomClass` in\norder to put the fields in a sensible order, even though\n`MonoidWithZeroHomClass` already extends `MonoidHomClass`.  class RingHomClass (F : Type*) (α β : outParam Type*)\n    [NonAssocSemiring α] [NonAssocSemiring β] [FunLike F α β] : Prop\n  extends MonoidHomClass F α β, AddMonoidHomClass F α β, MonoidWithZeroHomClass F α β",
    "RingHomInvPair.ids": " instance ids : RingHomInvPair (RingHom.id R₁) (RingHom.id R₁) :=",
    "RingHomSurjective.ids": " instance ids : RingHomSurjective (RingHom.id R₁) :=",
    "SMul": "Typeclass for types with a scalar multiplication operation, denoted `•` (`\\bu`)  class SMul (M : Type u) (α : Type v) where\n  /-- `m • a : α` denotes the product of `m : M` and `a : α`. The meaning of this notation is type-dependent,\n  but it is intended to be used for left actions. -/\n  smul : M → α → α",
    "SMulCommClass": "A typeclass mixin saying that two multiplicative actions on the same space commute.  @[to_additive]\nclass SMulCommClass (M N α : Type*) [SMul M α] [SMul N α] : Prop where\n  /-- `•` is left commutative -/\n  smul_comm : ∀ (m : M) (n : N) (a : α), m • n • a = n • m • a",
    "SMulWithZero": "`SMulWithZero` is a class consisting of a Type `M₀` with `0 ∈ M₀` and a scalar multiplication\nof `M₀` on a Type `A` with `0`, such that the equality `r • m = 0` holds if at least one among `r`\nor `m` equals `0`.  class SMulWithZero [Zero M₀] [Zero A] extends SMulZeroClass M₀ A where\n  /-- Scalar multiplication by the scalar `0` is `0`. -/\n  zero_smul : ∀ m : A, (0 : M₀) • m = 0",
    "Semiring": "A `Semiring` is a type with addition, multiplication, a `0` and a `1` where addition is\ncommutative and associative, multiplication is associative and left and right distributive over\naddition, and `0` and `1` are additive and multiplicative identities.  class Semiring (α : Type u) extends AddCommMonoid α, MonoidWithZero α, NonUnitalSemiring α,\n  NonAssocSemiring α",
    "Set": "A set is a collection of elements of some type `α`.\n\nAlthough `Set` is defined as `α → Prop`, this is an implementation detail which should not be\nrelied on. Instead, `Set.ofPred` (also written `{x | p x}`) and membership of a set (`∈`) should be\nused to convert between sets and predicates.\n @[use_set_notation_for_order]\ndef Set (α : Type u) :=",
    "Set.Finite": "A set is finite if the corresponding `Subtype` is finite,\ni.e., if there exists a natural `n : ℕ` and an equivalence `s ≃ Fin n`.  protected def Finite (s : Set α) : Prop :=",
    "Set.ofPred": "Turn a predicate `p : α → Prop` into a set, also written as `{x | p x}`  @[implicit_reducible]\ndef Set.ofPred {α : Type u} (p : α → Prop) : Set α :=",
    "Set.range": "Range of a function.\n\nThis function is more flexible than `f '' univ`, as the image requires that the domain is in Type\nand not an arbitrary Sort.  def range (f : ι → α) : Set α :=",
    "Set.univ": "The universal set on a type `α` is the set containing all elements of `α`.\n\nThis is conceptually the \"same as\" `α` (in set theory, it is actually the same), but type theory\nmakes the distinction that `α` is a type while `Set.univ` is a term of type `Set α`. `Set.univ` can\nitself be coerced to a type `↥Set.univ` which is in bijection with (but distinct from) `α`.  def univ : Set α :=",
    "Squarefree": "An element of a monoid is squarefree if the only squares that\ndivide it are the squares of units.  def Squarefree [Monoid R] (r : R) : Prop :=",
    "Subalgebra": "A subalgebra is a sub(semi)ring that includes the range of `algebraMap`.  structure Subalgebra (R : Type u) (A : Type v) [CommSemiring R] [Semiring A] [Algebra R A] : Type v\n    extends Subsemiring A where\n  /-- The image of `algebraMap` is contained in the underlying set of the subalgebra -/\n  algebraMap_mem' : ∀ r, algebraMap R A r ∈ carrier\n  zero_mem' := (algebraMap R A).map_zero ▸ algebraMap_mem' 0\n  one_mem' := (algebraMap R A).map_one ▸ algebraMap_mem' 1",
    "Subalgebra.algebra": " instance algebra : Algebra R S :=",
    "Subalgebra.algebra'": "More general form of `Subalgebra.algebra`.\n\nThis instance should have low priority since it is slow to fail:\nbefore failing, it will cause a search through all `SMul R' R` instances,\nwhich can quickly get expensive.\n instance (priority := 500) algebra' [CommSemiring R'] [SMul R' R] [Algebra R' A]\n    [IsScalarTower R' R A] :\n    Algebra R' S where\n  algebraMap := (algebraMap R' A).codRestrict S fun x => by\n    rw [Algebra.algebraMap_eq_smul_one, ← smul_one_smul R x (1 : A), ←\n      Algebra.algebraMap_eq_smul_one]\n    exact algebraMap_mem S _\n  commutes' := fun _ _ => Subtype.ext <| Algebra.com",
    "Submodule": "A submodule of a module is one which is closed under vector operations.\nThis is a sufficient condition for the subset of vectors in the submodule\nto themselves form a module.  structure Submodule (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] [Module R M] : Type v\n    extends AddSubmonoid M, SubMulAction R M",
    "Submodule.Quotient.addCommMonoid": " instance addCommMonoid : AddCommMonoid (M ⧸ p) :=",
    "Submodule.Quotient.mk": "Map associating to an element of `M` the corresponding element of `M/p`,\nwhen `p` is a submodule of `M`.  def mk {p : Submodule R M} : M → M ⧸ p :=",
    "Submodule.Quotient.module": " instance module (P : Submodule R M) : Module R (M ⧸ P) :=",
    "Submodule.Quotient.module'": " instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] (P : Submodule R M) :\n    Module S (M ⧸ P) :=",
    "Submodule.Quotient.restrictScalarsEquiv": "The quotient of `P` as an `S`-submodule is the same as the quotient of `P` as an `R`-submodule,\nwhere `P : Submodule R M`.\n def restrictScalarsEquiv [Ring S] [SMul S R] [Module S M] [IsScalarTower S R M]\n    (P : Submodule R M) : (M ⧸ P.restrictScalars S) ≃ₗ[S] M ⧸ P :=",
    "Submodule.addCommGroup": " instance addCommGroup : AddCommGroup p :=",
    "Submodule.addCommMonoid": " instance addCommMonoid : AddCommMonoid p :=",
    "Submodule.comap": "The pullback of a submodule `p ⊆ M₂` along `f : M → M₂`  @[implicit_reducible]\ndef comap (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R₂ M₂) : Submodule R M :=",
    "Submodule.completeLattice": " instance completeLattice : CompleteLattice (Submodule R M) where\n  sup a b := sInf { x | a ≤ x ∧ b ≤ x }\n  le_sup_left _ _ := Set.subset_iInter₂ fun _ ⟨h, _⟩ ↦ h\n  le_sup_right _ _ := Set.subset_iInter₂ fun _ ⟨_, h⟩ ↦ h\n  sup_le _ _ _ h₁ h₂ := Set.biInter_subset_of_mem ⟨h₁, h₂⟩\n  inf := (· ⊓ ·)\n  le_inf _ _ _ := Set.subset_inter\n  inf_le_left _ _ := Set.inter_subset_left\n  inf_le_right _ _ := Set.inter_subset_right\n  sSup S := sInf {sm | ∀ s ∈ S, s ≤ sm}\n  isLUB_sSup _ := isGLB_upperBounds.mp Submodule.isGLB_sInf\n  isGLB_sInf _ := Submodule.isGLB_sInf",
    "Submodule.dualAnnihilator": "The `dualAnnihilator` of a submodule `W` is the set of linear maps `φ` such\nthat `φ w = 0` for all `w ∈ W`.  def dualAnnihilator {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]\n    (W : Submodule R M) : Submodule R <| Module.Dual R M :=",
    "Submodule.dualQuotEquivDualAnnihilator": "Equivalence $(M/W)^* \\cong \\operatorname{ann}(W)$. That is, there is a one-to-one\ncorrespondence between the dual of `M ⧸ W` and those elements of the dual of `M` that\nvanish on `W`.\n\nThe inverse of this is `Submodule.dualCopairing`.  def dualQuotEquivDualAnnihilator (W : Submodule R M) :\n    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=",
    "Submodule.hasQuotient": "The quotient of a module `M` by a submodule `p ⊆ M`.  instance hasQuotient : HasQuotient M (Submodule R M) :=",
    "Submodule.idemSemiring": "Sub-R-modules of an R-algebra form an idempotent semiring.  instance idemSemiring : IdemSemiring (Submodule R A) where\n  one_mul := Submodule.one_mul\n  mul_one := Submodule.mul_one",
    "Submodule.liftQ": "The map from the quotient of `M` by a submodule `p` to `M₂` induced by a linear map `f : M → M₂`\nvanishing on `p`, as a linear map.  def liftQ (f : M →ₛₗ[τ₁₂] M₂) (h : p ≤ ker f) : M ⧸ p →ₛₗ[τ₁₂] M₂ :=",
    "Submodule.map": "The pushforward of a submodule `p ⊆ M` by `f : M → M₂`  def map (f : M →ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Submodule R₂ M₂ :=",
    "Submodule.mem_bot": " @[simp]\ntheorem mem_bot {x : M} : x ∈ (⊥ : Submodule R M) ↔ x = 0 :=",
    "Submodule.mem_top": " @[simp] lemma mem_top {x : M} : x ∈ (⊤ : Submodule R M) :=",
    "Submodule.mem_torsionBy_iff": " @[simp]\ntheorem mem_torsionBy_iff (x : M) : x ∈ torsionBy R M a ↔ a • x = 0 :=",
    "Submodule.mkQ": "The map from a module `M` to the quotient of `M` by a submodule `p` as a linear map.  def mkQ : M →ₗ[R] M ⧸ p where\n  toFun := Quotient.mk\n  map_add' := by simp\n  map_smul' := by simp",
    "Submodule.module": " instance module : Module R p :=",
    "Submodule.module'": " instance module' [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :\n    Module S p :=",
    "Submodule.mul": "Multiplication of sub-R-modules of an R-module A that is also a semiring. The submodule `M * N`\nconsists of finite sums of elements `m * n` for `m ∈ M` and `n ∈ N`.  instance mul : Mul (Submodule R A) where\n  mul := (· • ·)",
    "Submodule.restrictScalars": "`V.restrictScalars S` is the `S`-submodule of the `S`-module given by restriction of scalars,\ncorresponding to `V`, an `R`-submodule of the original `R`-module.\n def restrictScalars (V : Submodule R M) : Submodule S M where\n  carrier := V\n  zero_mem' := V.zero_mem\n  smul_mem' c _ h := V.smul_of_tower_mem c h\n  add_mem' hx hy := V.add_mem hx hy",
    "Submodule.span": "The span of a set `s ⊆ M` is the smallest submodule of M that contains `s`.  def span (s : Set M) : Submodule R M :=",
    "Submodule.subtype": "Embedding of a submodule `p` to the ambient space `M`.  protected def subtype : p →ₗ[R] M where\n  toFun := Subtype.val\n  map_add' := by simp\n  map_smul' := by simp",
    "Submodule.torsionBy": "The `a`-torsion submodule for `a` in `R`, containing all elements `x` of `M` such that\n`a • x = 0`.  @[simps!]\ndef torsionBy (a : R) : Submodule R M :=",
    "Submonoid": "A submonoid of a monoid `M` is a subset containing 1 and closed under multiplication.  structure Submonoid (M : Type*) [MulOneClass M] extends Subsemigroup M where\n  /-- A submonoid contains `1`. -/\n  one_mem' : (1 : M) ∈ carrier",
    "Subsingleton": "A _subsingleton_ is a type with at most one element. It is either empty or has a unique element.\n\nAll propositions are subsingletons because of proof irrelevance: false propositions are empty, and\nall proofs of a true proposition are equal to one another. Some non-propositional types are also\nsubsingletons.\n class Subsingleton (α : Sort u) : Prop where\n  /-- Prove that `α` is a subsingleton by showing that any two elements are equal. -/\n  intro ::\n  /-- Any two elements of a subsingleton are equal. -/\n  allEq : (a b : α) → a = b",
    "Subspace.dual_finrank_eq": " @[simp]\ntheorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V :=",
    "TensorProduct": "The tensor product of two modules `M` and `N` over the same commutative semiring `R`.\nThe localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`.  def TensorProduct : Type _ :=",
    "TensorProduct.AlgebraTensorModule.lift": "Heterobasic version of `TensorProduct.lift`:\n\nConstructing a linear map `M ⊗[R] N →[A] P` given a bilinear map `M →[A] N →[R] P` with the\nproperty that its composition with the canonical bilinear map `M →[A] N →[R] M ⊗[R] N` is\nthe given bilinear map `M →[A] N →[R] P`.  nonrec def lift (f : M →ₗ[A] N →ₗ[R] P) : M ⊗[R] N →ₗ[A] P :=",
    "TensorProduct.AlgebraTensorModule.mk": "Heterobasic version of `TensorProduct.mk`:\n\nThe canonical bilinear map `M →[A] N →[R] M ⊗[R] N`.  @[simps! apply]\nnonrec def mk (A M N : Type*) [Semiring A]\n    [AddCommMonoid M] [Module R M] [Module A M] [SMulCommClass R A M]\n    [AddCommMonoid N] [Module R N] : M →ₗ[A] N →ₗ[R] M ⊗[R] N :=",
    "TensorProduct.Eqv": "The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is\nthe tensor product.  inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop\n  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0\n  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0\n  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))\n  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))\n  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))\n  | add_comm : ∀ x y, Eqv (x + y) (y + x)",
    "TensorProduct.addCommGroup": " instance addCommGroup : AddCommGroup (M ⊗[R] N) where\n  neg_add_cancel := fun x => TensorProduct.neg_add_cancel x\n  zsmul_zero' := by simp\n  zsmul_succ' := by simp [add_comm, TensorProduct.add_smul]\n  zsmul_neg' := fun n x => by\n    change (-n.succ : ℤ) • x = -(((n : ℤ) + 1) • x)\n    rw [← zero_add (_ • x), ← TensorProduct.neg_add_cancel ((n.succ : ℤ) • x), add_assoc,\n      ← add_smul, ← sub_eq_add_neg, sub_self, zero_smul, add_zero]\n    rfl",
    "TensorProduct.addCommMonoid": " instance addCommMonoid : AddCommMonoid (M ⊗[R] N) where",
    "TensorProduct.homTensorHomMap": "The linear map from `(M →ₛₗ[σ₁₂] M₂) ⊗ (N →ₛₗ[σ₁₂] N₂)` to `M ⊗ N →ₛₗ[σ₁₂] M₂ ⊗ N₂`\nsending `f ⊗ₜ g` to `TensorProduct.map f g`, the tensor product of the two maps.  def homTensorHomMap : (M →ₛₗ[σ₁₂] M₂) ⊗[R₂] (N →ₛₗ[σ₁₂] N₂) →ₗ[R₂] M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=",
    "TensorProduct.leftHasSMul": "Given two modules over a commutative semiring `R`, if one of the factors carries a\n(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then\nthe tensor product (over `R`) carries an action of `R'`.\n\nThis instance defines this `R'` action in the case that it is the left module which has the `R'`\naction. Two natural ways in which this situation arises are:\n* Extension of scalars\n* A tensor product of a group representation with a module not carrying an action\n\nNote that in the special case that `R = R'`, since `R` is commutative, we just get the usual sc",
    "TensorProduct.leftModule": " instance leftModule : Module R'' (M ⊗[R] N) :=",
    "TensorProduct.map": "The tensor product of a pair of linear maps between modules.  def map (f : M →ₛₗ[σ₁₂] M₂) (g : N →ₛₗ[σ₁₂] N₂) : M ⊗[R] N →ₛₗ[σ₁₂] M₂ ⊗[R₂] N₂ :=",
    "TensorProduct.map₂": "This is a binary version of `TensorProduct.map`: Given a bilinear map `f : M ⟶ P ⟶ Q` and a\nbilinear map `g : N ⟶ S ⟶ T`, if we think `f` and `g` as semilinear maps with two inputs, then\n`map₂ f g` is a bilinear map taking two inputs `M ⊗ N → P ⊗ S → Q ⊗ S` defined by\n`map₂ f g (m ⊗ n) (p ⊗ s) = f m p ⊗ g n s`.\n\nMathematically, `TensorProduct.map₂` is defined as the composition\n`M ⊗ N -map→ Hom(P, Q) ⊗ Hom(S, T) -homTensorHomMap→ Hom(P ⊗ S, Q ⊗ T)`.\n def map₂ (f : M →ₛₗ[σ₁₃] M₂ →ₛₗ[σ₂₃] M₃) (g : N →ₛₗ[σ₁₃] N₂ →ₛₗ[σ₂₃] N₃) :\n    M ⊗[R] N →ₛₗ[σ₁₃] M₂ ⊗[R₂] N₂ →ₛₗ[σ₂₃] M₃ ⊗[R₃] N₃ :=",
    "TensorProduct.smulCommClass_left": "`SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)`  instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where\n  smul_comm r' r'₂ x :=\n    TensorProduct.inductionOn x\n      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by\n      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]",
    "TensorProduct.tmul": "The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,\naccessed by `open scoped TensorProduct`.  def tmul (m : M) (n : N) : M ⊗[R] N :=",
    "Top": "Typeclass for the `⊤` (`\\top`) notation  @[notation_class, ext]\nclass Top (α : Type*) where\n  /-- The top (`⊤`, `\\top`) element -/\n  top : α",
    "Top.top": "The top (`⊤`, `\\top`) element \n\nConventions for notations in identifiers:\n\n * The recommended spelling of `⊤` in identifiers is `top`. ",
    "Transcendental": "An element of an R-algebra is transcendental over R if it is not algebraic over R.  def Transcendental (x : A) : Prop :=",
    "Transcendental.pow": " theorem Transcendental.pow {r : A} (ht : Transcendental R r) {n : ℕ} (hn : 0 < n) :\n    Transcendental R (r ^ n) :=",
    "True": "`True` is a proposition and has only an introduction rule, `True.intro : True`.\nIn other words, `True` is simply true, and has a canonical proof, `True.intro`\nFor more information: [Propositional Logic](https://lean-lang.org/theorem_proving_in_lean4/propositions_and_proofs.html#propositional-logic)\n inductive True : Prop where\n  /-- `True` is true, and `True.intro` (or more commonly, `trivial`)\n  is the proof. -/\n  | intro : True",
    "Unit": "The canonical type with one element. This element is written `()`.\n\n`Unit` has a number of uses:\n* It can be used to model control flow that returns from a function call without providing other\n  information.\n* Monadic actions that return `Unit` have side effects without computing values.\n* In polymorphic types, it can be used to indicate that no data is to be stored in a particular\n  field.\n abbrev Unit : Type :=",
    "Units": "Units of a `Monoid`, bundled version. Notation: `αˣ`.\n\nAn element of a `Monoid` is a unit if it has a two-sided inverse.\nThis version bundles the inverse element so that it can be computed.\nFor a predicate see `IsUnit`.  structure Units (α : Type u) [Monoid α] where\n  /-- The underlying value in the base `Monoid`. -/\n  val : α\n  /-- The inverse value of `val` in the base `Monoid`. -/\n  inv : α\n  /-- `inv` is the right inverse of `val` in the base `Monoid`. -/\n  val_inv : val * inv = 1\n  /-- `inv` is the left inverse of `val` in the base `Monoid`. -/\n  inv_val : inv * val = 1",
    "Units.val": "The underlying value in the base `Monoid`.  ",
    "Valuation": "The type of `Γ₀`-valued valuations on `R`.\n\nWhen you extend this structure, make sure to extend `ValuationClass`.  structure Valuation extends R →*₀ Γ₀ where\n  /-- The valuation of a sum is less than or equal to the maximum of the valuations. -/\n  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)",
    "ValuationSubring": "A valuation subring of a field `K` is a subring `A` such that for every `x : K`,\neither `x ∈ A` or `x⁻¹ ∈ A`.\n\nThis is equivalent to being maximal in the domination order\nof local subrings (the stacks project definition). See `LocalSubring.isMax_iff`.\n structure ValuationSubring extends Subring K where\n  mem_or_inv_mem' : ∀ x : K, x ∈ carrier ∨ x⁻¹ ∈ carrier",
    "WeierstrassCurve": "A Weierstrass curve `Y² + a₁XY + a₃Y = X³ + a₂X² + a₄X + a₆` with parameters `aᵢ`.  @[ext]\nstructure WeierstrassCurve (R : Type u) where\n  /-- The `a₁` coefficient of a Weierstrass curve. -/\n  a₁ : R\n  /-- The `a₂` coefficient of a Weierstrass curve. -/\n  a₂ : R\n  /-- The `a₃` coefficient of a Weierstrass curve. -/\n  a₃ : R\n  /-- The `a₄` coefficient of a Weierstrass curve. -/\n  a₄ : R\n  /-- The `a₆` coefficient of a Weierstrass curve. -/\n  a₆ : R",
    "WeierstrassCurve.Affine": "An abbreviation for a Weierstrass curve in affine coordinates.  abbrev Affine : Type r :=",
    "WeierstrassCurve.Affine.CoordinateRing": "The affine coordinate ring `R[W] := R[X, Y] / ⟨W(X, Y)⟩` of a Weierstrass curve `W`.  abbrev CoordinateRing : Type r :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk": "The natural ring homomorphism mapping `R[X][Y]` to `R[W]`.  noncomputable abbrev mk : R[X][Y] →+* W'.CoordinateRing :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": " lemma Affine.CoordinateRing.mk_Ψ_sq (n : ℤ) : mk W (W.Ψ n) ^ 2 = mk W (C <| W.ΨSq n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": " lemma Affine.CoordinateRing.mk_φ (n : ℤ) : mk W (W.φ n) = mk W (C <| W.Φ n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": " lemma Affine.CoordinateRing.mk_ψ (n : ℤ) : mk W (W.ψ n) = mk W (W.Ψ n) :=",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": " lemma Affine.CoordinateRing.mk_ψ₂_sq : mk W W.ψ₂ ^ 2 = mk W (C W.Ψ₂Sq) :=",
    "WeierstrassCurve.Affine.Equation": "The proposition that an affine point `(x, y)` lies in a Weierstrass curve `W`.\n\nIn other words, it satisfies the Weierstrass equation `W(X, Y) = 0`.  def Equation (x y : R) : Prop :=",
    "WeierstrassCurve.Affine.Nonsingular": "The proposition that an affine point `(x, y)` on a Weierstrass curve `W` is nonsingular.\n\nIn other words, either `W_X(x, y) ≠ 0` or `W_Y(x, y) ≠ 0`.\n\nNote that this definition is only mathematically accurate for fields.  -- TODO: generalise this definition to be mathematically accurate for a larger class of rings.\ndef Nonsingular (x y : R) : Prop :=",
    "WeierstrassCurve.Affine.Point": "A nonsingular point on a Weierstrass curve `W` in affine coordinates. This is either the unique\npoint at infinity `WeierstrassCurve.Affine.Point.zero` or a nonsingular affine point\n`WeierstrassCurve.Affine.Point.some (x, y)` satisfying the Weierstrass equation of `W`.  inductive Point\n  | zero\n  | some (x y : R) (h : W'.Nonsingular x y)\nderiving DecidableEq",
    "WeierstrassCurve.Affine.negPolynomial": "The negation polynomial `-Y - a₁X - a₃` associated to the negation of a nonsingular affine point\non a Weierstrass curve.  noncomputable def negPolynomial : R[X][Y] :=",
    "WeierstrassCurve.Affine.negY": "The `Y`-coordinate of `-(x, y)` for a nonsingular affine point `(x, y)` on a Weierstrass curve\n`W`.\n\nThis depends on `W`, and has argument order: `x`, `y`.  @[simp, implicit_reducible]\ndef negY (x y : R) : R :=",
    "WeierstrassCurve.Affine.polynomial": "The polynomial `W(X, Y) := Y² + a₁XY + a₃Y - (X³ + a₂X² + a₄X + a₆)` associated to a Weierstrass\ncurve `W` over a ring `R` in affine coordinates.\n\nFor ease of polynomial manipulation, this is represented as a term of type `R[X][X]`, where the\ninner variable represents `X` and the outer variable represents `Y`. For clarity, the alternative\nnotations `Y` and `R[X][Y]` are provided in the `Polynomial.Bivariate` scope to represent the outer\nvariable and the bivariate polynomial ring `R[X][X]` respectively.  noncomputable def polynomial : R[X][Y] :=",
    "WeierstrassCurve.Affine.polynomialX": "The partial derivative `W_X(X, Y)` with respect to `X` of the polynomial `W(X, Y)` associated to\na Weierstrass curve `W` in affine coordinates.  -- TODO: define this in terms of `Polynomial.derivative`.\nnoncomputable def polynomialX : R[X][Y] :=",
    "WeierstrassCurve.Affine.polynomialY": "The partial derivative `W_Y(X, Y)` with respect to `Y` of the polynomial `W(X, Y)` associated to\na Weierstrass curve `W` in affine coordinates.  -- TODO: define this in terms of `Polynomial.derivative`.\nnoncomputable def polynomialY : R[X][Y] :=",
    "WeierstrassCurve.C_Ψ₂Sq": " lemma C_Ψ₂Sq : C W.Ψ₂Sq = W.ψ₂ ^ 2 - 4 * W.toAffine.polynomial :=",
    "WeierstrassCurve.IsElliptic": "`WeierstrassCurve.IsElliptic` is a typeclass which asserts that a Weierstrass curve is an\nelliptic curve: that its discriminant is a unit. Note that this definition is only mathematically\naccurate for certain rings whose Picard group has trivial 12-torsion, such as a field or a PID.  @[mk_iff]\nprotected class IsElliptic : Prop where\n  isUnit : IsUnit W.Δ",
    "WeierstrassCurve.a₁": "The `a₁` coefficient of a Weierstrass curve.  ",
    "WeierstrassCurve.a₃": "The `a₃` coefficient of a Weierstrass curve.  ",
    "WeierstrassCurve.baseChange": "The Weierstrass curve base changed to an algebra `A` over `R`.  def baseChange [Algebra R A] : WeierstrassCurve A :=",
    "WeierstrassCurve.b₂": "The `b₂` coefficient of a Weierstrass curve.  def b₂ : R :=",
    "WeierstrassCurve.b₄": "The `b₄` coefficient of a Weierstrass curve.  def b₄ : R :=",
    "WeierstrassCurve.b₆": "The `b₆` coefficient of a Weierstrass curve.  def b₆ : R :=",
    "WeierstrassCurve.b₈": "The `b₈` coefficient of a Weierstrass curve.  def b₈ : R :=",
    "WeierstrassCurve.isElliptic_iff": " ",
    "WeierstrassCurve.mk": " structure WeierstrassCurve (R : Type u) where",
    "WeierstrassCurve.natDegree_Φ": " @[simp]\nlemma natDegree_Φ [Nontrivial R] (n : ℤ) : (W.Φ n).natDegree = n.natAbs ^ 2 :=",
    "WeierstrassCurve.natDegree_ΨSq": " @[simp]\nlemma natDegree_ΨSq [NoZeroDivisors R] {n : ℤ} (h : (n : R) ≠ 0) :\n    (W.ΨSq n).natDegree = n.natAbs ^ 2 - 1 :=",
    "WeierstrassCurve.preΨ": "The univariate polynomials `preΨₙ` for `n ∈ ℤ`, which are auxiliary to the bivariate polynomials\n`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`.  noncomputable def preΨ (n : ℤ) : R[X] :=",
    "WeierstrassCurve.preΨ'": "The univariate polynomials `preΨₙ` for `n ∈ ℕ`, which are auxiliary to the bivariate polynomials\n`Ψₙ` congruent to the bivariate `n`-division polynomials `ψₙ`.  noncomputable def preΨ' (n : ℕ) : R[X] :=",
    "WeierstrassCurve.preΨ_even": " lemma preΨ_even (m : ℤ) : W.preΨ (2 * m) =\n    W.preΨ (m - 1) ^ 2 * W.preΨ m * W.preΨ (m + 2) -\n      W.preΨ (m - 2) * W.preΨ m * W.preΨ (m + 1) ^ 2 :=",
    "WeierstrassCurve.preΨ_odd": " lemma preΨ_odd (m : ℤ) : W.preΨ (2 * m + 1) =\n    W.preΨ (m + 2) * W.preΨ m ^ 3 * (if Even m then W.Ψ₂Sq ^ 2 else 1) -\n      W.preΨ (m - 1) * W.preΨ (m + 1) ^ 3 * (if Even m then 1 else W.Ψ₂Sq ^ 2) :=",
    "WeierstrassCurve.preΨ₄": "The univariate polynomial `preΨ₄`, which is auxiliary to the 4-division polynomial\n`ψ₄ = Ψ₄ = preΨ₄ψ₂`.  noncomputable def preΨ₄ : R[X] :=",
    "WeierstrassCurve.twoTorsionPolynomial": "A cubic polynomial whose discriminant is a multiple of the Weierstrass curve discriminant. If\n`W` is an elliptic curve over a field `R` of characteristic different from 2, then its roots over a\nsplitting field of `R` are precisely the `X`-coordinates of the non-zero 2-torsion points of `W`.  def twoTorsionPolynomial : Cubic R :=",
    "WeierstrassCurve.Δ": "The discriminant `Δ` of a Weierstrass curve. If `R` is a field, then this polynomial vanishes\nif and only if the cubic curve cut out by this equation is singular. Sometimes only defined up to\nsign in the literature; we choose the sign used by the LMFDB. For more discussion, see\n[the LMFDB page on discriminants](https://www.lmfdb.org/knowledge/show/ec.discriminant).  def Δ : R :=",
    "WeierstrassCurve.Φ": "The univariate polynomials `Φₙ` congruent to `φₙ`.  protected noncomputable def Φ (n : ℤ) : R[X] :=",
    "WeierstrassCurve.Φ_neg": " @[simp]\nlemma Φ_neg (n : ℤ) : W.Φ (-n) = W.Φ n :=",
    "WeierstrassCurve.Φ_three": " @[simp]\nlemma Φ_three : W.Φ 3 = X * W.Ψ₃ ^ 2 - W.preΨ₄ * W.Ψ₂Sq :=",
    "WeierstrassCurve.Ψ": "The bivariate polynomials `Ψₙ` congruent to the `n`-division polynomials `ψₙ`.  protected noncomputable def Ψ (n : ℤ) : R[X][Y] :=",
    "WeierstrassCurve.ΨSq": "The univariate polynomials `ΨSqₙ` congruent to `ψₙ²`.  noncomputable def ΨSq (n : ℤ) : R[X] :=",
    "WeierstrassCurve.ΨSq_three": " @[simp]\nlemma ΨSq_three : W.ΨSq 3 = W.Ψ₃ ^ 2 :=",
    "WeierstrassCurve.Ψ₂Sq": "The univariate polynomial `Ψ₂Sq` congruent to `ψ₂²`.  noncomputable def Ψ₂Sq : R[X] :=",
    "WeierstrassCurve.Ψ₂Sq_eq": " lemma Ψ₂Sq_eq : W.Ψ₂Sq = W.twoTorsionPolynomial.toPoly :=",
    "WeierstrassCurve.Ψ₃": "The `3`-division polynomial `ψ₃ = Ψ₃`.  noncomputable def Ψ₃ : R[X] :=",
    "WeierstrassCurve.φ": "The bivariate polynomials `φₙ`.  protected noncomputable def φ (n : ℤ) : R[X][Y] :=",
    "WeierstrassCurve.ψ": "The bivariate `n`-division polynomials `ψₙ`.  protected noncomputable def ψ (n : ℤ) : R[X][Y] :=",
    "WeierstrassCurve.ψ_one": " @[simp]\nlemma ψ_one : W.ψ 1 = 1 :=",
    "WeierstrassCurve.ψ_two": " @[simp]\nlemma ψ_two : W.ψ 2 = W.ψ₂ :=",
    "WeierstrassCurve.ψ_zero": " @[simp]\nlemma ψ_zero : W.ψ 0 = 0 :=",
    "WeierstrassCurve.ψ₂": "The `2`-division polynomial `ψ₂ = Ψ₂`.  noncomputable def ψ₂ : R[X][Y] :=",
    "WellFounded.Nat.fix": "A well-founded fixpoint operator specialized for `Nat`-valued measures. Given a measure `h`, it expects\nits higher order function argument `F` to invoke its argument only on values `y` that are smaller\nthan `x` with regard to `h`.\n\nIn contrast to `WellFounded.fix`, this fixpoint operator reduces on closed terms. (More precisely:\nwhen `h x` evaluates to a ground value)\n\n @[implicit_reducible]\ndef Nat.fix : (x : α) → motive x :=",
    "WithBot.unbotD": "Specialization of `Option.getD` to values in `WithBot α` that respects API boundaries.  @[to_dual\n/-- Specialization of `Option.getD` to values in `WithTop α` that respects API boundaries. -/]\ndef unbotD (d : α) (x : WithBot α) : α :=",
    "WithZero": "Add an extra element `0` to a type  ",
    "WithZero.exp": "The exponential map as a function `M → Mᵐ⁰`.  def exp (a : M) : Mᵐ⁰ :=",
    "WithZero.log": "The logarithm as a function `Mᵐ⁰ → M` with junk value `log 0 = 0`.  def log (x : Mᵐ⁰) : M :=",
    "WithZero.logEquiv": "The logarithm as an equivalence between `(Gᵐ⁰)ˣ` and `G`.  def logEquiv : (Gᵐ⁰)ˣ ≃ G :=",
    "WithZero.log_mul": " @[simp]\nlemma log_mul {x y : Mᵐ⁰} (hx : x ≠ 0) (hy : y ≠ 0) : log (x * y) = log x + log y :=",
    "WithZero.map₂": "The image of a binary function `f : α → β → γ` as a function\n`WithZero α → WithZero β → WithZero γ`.\n\nMathematically this should be thought of as the image of the corresponding function `α × β → γ`.  ",
    "WithZero.one": " instance one : One (WithZero α) where\n  __ := ‹One α›",
    "WithZero.recZeroCoe": "Recursor for `WithZero` using the preferred forms `0` and `↑a`.  @[elab_as_elim, induction_eliminator, cases_eliminator]\ndef _root_.WithZero.recZeroCoe {motive : WithZero α → Sort*} (zero : motive 0)\n    (coe : ∀ a : α, motive a) : ∀ n : WithZero α, motive n\n  | Option.none => zero\n  | Option.some x => coe x",
    "WithZero.unitsWithZeroEquiv": "Any group is isomorphic to the units of itself adjoined with `0`.  @[simps]\ndef unitsWithZeroEquiv : (WithZero α)ˣ ≃* α where\n  toFun a := unzero a.ne_zero\n  invFun a := Units.mk0 a coe_ne_zero\n  left_inv _ := Units.ext <| by simp only [coe_unzero, Units.mk0_val]\n  map_mul' _ _ := coe_inj.mp <| by simp only [Units.val_mul, coe_unzero, coe_mul]",
    "Zero": "A type with a zero element.  class Zero (α : Type u) where\n  /-- The zero element of the type. -/\n  zero : α",
    "abs": "`abs a`, denoted `|a|`, is the absolute value of `a`  ",
    "addConGen": "The inductively defined smallest additive congruence relation containing\na given binary relation.  ",
    "addOrderOf": "`addOrderOf a` is the order of the element `a`, i.e. the `n ≥ 1`, s.t. `n • a = 0` if it\nexists. Otherwise, i.e. if `a` is of infinite order, then `addOrderOf a` is `0` by convention.  ",
    "addOrderOf_dvd_of_nsmul_eq_zero": " ",
    "complEDS": "The complement sequence `Wᶜ : ℤ × ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.\n\nThis extends `complEDS'` by defining its values at negative integers.  def complEDS (n : ℤ) : R :=",
    "complEDS'": "The complement sequence `Wᶜ : ℤ × ℕ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(n * k)`. In other words, `W(k) * Wᶜ(k, n) = W(n * k)` for all `k, n ∈ ℤ`.\n\nThis is defined in terms of `normEDS` and agrees with `complEDS₂` when `n = 2`.  def complEDS' : ℕ → R\n  | 0 => 0\n  | 1 => 1\n  | (n + 2) => let m :=",
    "complEDS₂": "The 2-complement sequence `Wᶜ₂ : ℤ → R` for a normalised EDS `W : ℤ → R` that witnesses\n`W(k) ∣ W(2 * k)`. In other words, `W(k) * Wᶜ₂(k) = W(2 * k)` for all `k ∈ ℤ`.\n\nThis is defined in terms of `preNormEDS`.  def complEDS₂ (k : ℤ) : R :=",
    "exists_prime_addOrderOf_dvd_card'": "For every prime `p` dividing the order of a finite additive group `G` there exists\nan element of order `p` in `G`. This is the additive version of Cauchy's theorem.  @[to_additive /-- For every prime `p` dividing the order of a finite additive group `G` there exists\nan element of order `p` in `G`. This is the additive version of Cauchy's theorem. -/]",
    "exists_smul_eq_of_finrank_eq_one": "In a one-dimensional space, any vector is a multiple of any nonzero vector  lemma exists_smul_eq_of_finrank_eq_one\n    (h : finrank K V = 1) {x : V} (hx : x ≠ 0) (y : V) :\n    ∃ (c : K), c • x = y :=",
    "iSup": "Indexed supremum  @[to_dual /-- Indexed infimum -/]\ndef iSup [SupSet α] (s : ι → α) : α :=",
    "id": "The identity function. `id` takes an implicit argument `α : Sort u`\n(a type in any universe), and an argument `a : α`, and returns `a`.\n\nAlthough this may look like a useless function, one application of the identity\nfunction is to explicitly put a type on an expression. If `e` has type `T`,\nand `T'` is definitionally equal to `T`, then `@id T' e` typechecks, and Lean\nknows that this expression has type `T'` rather than `T`. This can make a\ndifference for typeclass inference, since `T` and `T'` may have different\ntypeclass instances on them. `show T' from e` is sugar for an `@id T' e`\nexpressi",
    "inferInstance": "`inferInstance` synthesizes a value of any target type by typeclass\ninference. This function has the same type signature as the identity\nfunction, but the square brackets on the `[i : α]` argument means that it will\nattempt to construct this argument by typeclass inference. (This will fail if\n`α` is not a `class`.) Example:\n```\n#check (inferInstance : Inhabited Nat) -- Inhabited Nat\n\ndef foo : Inhabited (Nat × Nat) :=\n  inferInstance\n\nexample : foo.default = (default, default) :=\n  rfl\n```\n abbrev inferInstance {α : Sort u} [i : α] : α :=",
    "le_trans": "The relation `≤` on a preorder is transitive.  lemma le_trans : a ≤ b → b ≤ c → a ≤ c :=",
    "minpoly": "Suppose `x : B`, where `B` is an `A`-algebra.\n\nThe minimal polynomial `minpoly A x` of `x`\nis a monic polynomial with coefficients in `A` of smallest degree that has `x` as its root,\nif such exists (`IsIntegral A x`) or zero otherwise.\n\nFor example, if `V` is a `𝕜`-vector space for some field `𝕜` and `f : V →ₗ[𝕜] V` then\nthe minimal polynomial of `f` is `minpoly 𝕜 f`.\n @[stacks 09GM]\nnoncomputable def minpoly (x : B) : A[X] :=",
    "nonZeroDivisors": "The submonoid of non-zero-divisors of a `MonoidWithZero` `M₀`.  def nonZeroDivisors (M₀ : Type*) [MonoidWithZero M₀] : Submonoid M₀ :=",
    "normEDS": "The canonical example of a normalised EDS `W : ℤ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = b`, `W(3) = c`, and `W(4) = d * b`.\n\nThis is defined in terms of `preNormEDS` whose even terms differ by a factor of `b`.  def normEDS (n : ℤ) : R :=",
    "normEDS_dvd_normEDS_two_mul": " lemma normEDS_dvd_normEDS_two_mul (k : ℤ) : normEDS b c d k ∣ normEDS b c d (2 * k) :=",
    "normEDS_even": " lemma normEDS_even (m : ℤ) : normEDS b c d (2 * m) * b =\n    normEDS b c d (m - 1) ^ 2 * normEDS b c d m * normEDS b c d (m + 2) -\n      normEDS b c d (m - 2) * normEDS b c d m * normEDS b c d (m + 1) ^ 2 :=",
    "normEDS_four": " @[simp]\nlemma normEDS_four : normEDS b c d 4 = d * b :=",
    "normEDS_mul_complEDS₂": " lemma normEDS_mul_complEDS₂ (k : ℤ) :\n    normEDS b c d k * complEDS₂ b c d k = normEDS b c d (2 * k) :=",
    "normEDS_neg": " @[simp]\nlemma normEDS_neg (n : ℤ) : normEDS b c d (-n) = -normEDS b c d n :=",
    "normEDS_odd": " lemma normEDS_odd (m : ℤ) : normEDS b c d (2 * m + 1) =\n    normEDS b c d (m + 2) * normEDS b c d m ^ 3 -\n      normEDS b c d (m - 1) * normEDS b c d (m + 1) ^ 3 :=",
    "normEDS_one": " @[simp]\nlemma normEDS_one : normEDS b c d 1 = 1 :=",
    "normEDS_three": " @[simp]\nlemma normEDS_three : normEDS b c d 3 = c :=",
    "normEDS_two": " @[simp]\nlemma normEDS_two : normEDS b c d 2 = b :=",
    "normEDS_zero": " @[simp]\nlemma normEDS_zero : normEDS b c d 0 = 0 :=",
    "npowRecAuto": "An abbreviation for `npowRec` with an additional typeclass assumption on associativity\nso that we can use `@[csimp]` to replace it with an implementation by repeated squaring\nin compiled code.\n @[to_additive\n/-- An abbreviation for `nsmulRec` with an additional typeclass assumptions on associativity\nso that we can use `@[csimp]` to replace it with an implementation by repeated doubling in compiled\ncode as an automatic parameter. -/]\nabbrev npowRecAuto {M : Type*} [Semigroup M] [One M] (k : ℕ) (m : M) : M :=",
    "one_smul": " @[to_additive (attr := simp)]\nlemma one_smul (b : α) : (1 : M) • b = b :=",
    "pow_two": "Note that most of the lemmas about powers of two refer to it as `sq`.  @[to_additive two_nsmul] lemma pow_two (a : M) : a ^ 2 = a * a :=",
    "preNormEDS": "The auxiliary sequence for a normalised EDS `W : ℤ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.\n\nThis extends `preNormEDS'` by defining its values at negative integers.  def preNormEDS (n : ℤ) : R :=",
    "preNormEDS'": "The auxiliary sequence for a normalised EDS `W : ℕ → R`, with initial values\n`W(0) = 0`, `W(1) = 1`, `W(2) = 1`, `W(3) = c`, and `W(4) = d` and extra parameter `b`.  def preNormEDS' : ℕ → R\n  | 0 => 0\n  | 1 => 1\n  | 2 => 1\n  | 3 => c\n  | 4 => d\n  | (n + 5) => let m :=",
    "preNormEDS_even": " lemma preNormEDS_even (m : ℤ) : preNormEDS b c d (2 * m) =\n    preNormEDS b c d (m - 1) ^ 2 * preNormEDS b c d m * preNormEDS b c d (m + 2) -\n      preNormEDS b c d (m - 2) * preNormEDS b c d m * preNormEDS b c d (m + 1) ^ 2 :=",
    "preNormEDS_odd": " lemma preNormEDS_odd (m : ℤ) : preNormEDS b c d (2 * m + 1) =\n    preNormEDS b c d (m + 2) * preNormEDS b c d m ^ 3 * (if Even m then b else 1) -\n      preNormEDS b c d (m - 1) * preNormEDS b c d (m + 1) ^ 3 * (if Even m then 1 else b) :=",
    "semigroupDvd": "There are two possible conventions for divisibility, which coincide in a `CommMonoid`.\nThis matches the convention for ordinals.  instance (priority := 100) semigroupDvd : Dvd α :=",
    "smulCommClass_self": " @[to_additive]\ninstance smulCommClass_self (M α : Type*) [CommMonoid M] [MulAction M α] : SMulCommClass M M α where\n  smul_comm a a' b := by rw [← mul_smul, mul_comm, mul_smul]",
    "zero_smul": " @[simp]\ntheorem zero_smul (m : A) : (0 : M₀) • m = 0 :="
  },
  "card_module": {
    "AddCommGroup": "Mathlib.Algebra.Group.Defs",
    "AddCommMonoid": "Mathlib.Algebra.Group.Monoid",
    "AddCommMonoidWithOne": "Mathlib.Data.Nat.Cast.Defs",
    "AddCon.Quotient": "Mathlib.GroupTheory.Congruence.Defs",
    "AddEquiv": "Mathlib.Algebra.Group.Equiv.Defs",
    "AddGroup": "Mathlib.Algebra.Group.Defs",
    "AddMonoid": "Mathlib.Algebra.Group.Monoid",
    "AddMonoidAlgebra.algebra": "Mathlib.Algebra.MonoidAlgebra.Basic",
    "AddMonoidAlgebra.nonAssocSemiring": "Mathlib.Algebra.MonoidAlgebra.Defs",
    "AddMonoidHom": "Mathlib.Algebra.Group.Hom.Defs",
    "AddMonoidHom.add": "Mathlib.Algebra.Group.Hom.Basic",
    "AddMonoidHom.ker": "Mathlib.Algebra.Group.Subgroup.Ker",
    "AddMonoidHom.mulRight": "Mathlib.Algebra.Ring.Basic",
    "AddSubgroup": "Mathlib.Algebra.Group.Subgroup.Defs",
    "AddSubgroup.addSubgroupOf": "Mathlib.Algebra.Group.Subgroup.Map",
    "AddSubgroup.card_bot": "Mathlib.Algebra.Group.Subgroup.Finite",
    "AlgEquiv": "Mathlib.Algebra.Algebra.Equiv",
    "AlgHom": "Mathlib.Algebra.Algebra.Hom",
    "AlgHom.funLike": "Mathlib.Algebra.Algebra.Hom",
    "AlgHom.restrictScalars": "Mathlib.Algebra.Algebra.Tower",
    "AlgHom.toRingHom": "Mathlib.Algebra.Algebra.Hom",
    "Algebra": "Mathlib.Algebra.Algebra.Defs",
    "Algebra.EssFiniteType": "Mathlib.RingTheory.EssentialFiniteness",
    "Algebra.FormallyEtale": "Mathlib.RingTheory.Etale.Basic",
    "Algebra.FormallyEtale.of_isLocalization": "Mathlib.RingTheory.Etale.Basic",
    "Algebra.FormallyEtale.of_isSeparable": "Mathlib.RingTheory.Etale.Field",
    "Algebra.IsIntegral": "Mathlib.RingTheory.IntegralClosure.Algebra.Defs",
    "Algebra.IsSeparable": "Mathlib.FieldTheory.Separable",
    "Algebra.TensorProduct.algebraMap_apply": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.includeLeft": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.includeLeftRingHom": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.includeRight": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.instCommRing": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.instMul": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.instSemiring": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.leftAlgebra": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.lmul'": "Mathlib.RingTheory.TensorProduct.Maps",
    "Algebra.TensorProduct.lmul''": "Mathlib.RingTheory.TensorProduct.Maps",
    "Algebra.TensorProduct.lmul'_apply_tmul": "Mathlib.RingTheory.TensorProduct.Maps",
    "Algebra.TensorProduct.mul": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.one_def": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.TensorProduct.tmul_mul_tmul": "Mathlib.RingTheory.TensorProduct.Basic",
    "Algebra.adjoin": "Mathlib.Algebra.Algebra.Subalgebra.Lattice",
    "Algebra.algebraMap": "Mathlib.Algebra.Algebra.Defs",
    "Algebra.id": "Mathlib.Algebra.Algebra.Defs",
    "Algebra.linearMap": "Mathlib.Algebra.Algebra.Defs",
    "Algebra.lsmul": "Mathlib.Algebra.Algebra.Tower",
    "Algebra.to_smulCommClass": "Mathlib.Algebra.Algebra.Basic",
    "Algebra.trace": "Mathlib.RingTheory.Trace.Defs",
    "Algebra.trdeg": "Mathlib.RingTheory.AlgebraicIndependent.Basic",
    "AlgebraicCurve.ConstantsAreBase": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.Divisor": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.IsPrincipal": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.degZero": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.degree": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.degree_eq_sum": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.degree_single": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Divisor.principal": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.FunctionFieldRiemannRoch": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.H1": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.HasCanonicalDivisor": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.HasCanonicalDivisor.exists_divisor": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.HasCanonicalLocalResidueKStar": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.HasLocalResidue": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.HasPrincipalDivisors": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.HasSeparableResidue": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.HasSeparableResidue.of_perfectField": "FLTForHuman.AlgebraicCurve.LocalResidue.Instance",
    "AlgebraicCurve.HasWeilCanonicalDivisor": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.IndexOfSpecialtyFinite": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.IsCurveOver": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.deg_eq_one_of_isAlgClosed": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.exists_separating_transcendental": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.IsCurveOver.finrank_kaehler": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.forall_deg_eq_one_of_isAlgClosed": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.instFreeKaehler": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.instNontrivialKaehler": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.kaehler_free_rank_one": "FLTForHuman.AlgebraicCurve.Defs.IsCurveOver",
    "AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
    "AlgebraicCurve.IsCurveOver.one_le_trdeg": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.IsCurveOver.trdeg_le_one": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.KaehlerRankOne": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
    "AlgebraicCurve.LSpace": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.Pic": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Pic0": "FLTForHuman.AlgebraicCurve.Defs.Divisor",
    "AlgebraicCurve.Place": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.CanonicalLocalResidueDataK": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.Place.DCoordGenerates": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.FiniteResidue": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.LocalResidueData.res": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.Place.ResidueField": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.adicValuation": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.dCoord": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField": "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
    "AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop": "FLTForHuman.AlgebraicCurve.Canonical.DCoordGenerates",
    "AlgebraicCurve.Place.dCoord_ne_zero": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.deg": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.differentialCoeff": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.differentialCoeff_dCoord": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.differentialCoeff_smul_dCoord": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.differentialCoeff_unique": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.differentialCoeff_zero": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.exists_eq_smul_dCoord": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.exists_unit_mul_zpow": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.gate_ordDifferential_dCoord": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.heightOneSpectrum": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.mem_iff_ord_nonneg": "FLTForHuman.AlgebraicCurve.Defs.PushPull",
    "AlgebraicCurve.Place.min_ord_le_ord_add": "FLTForHuman.AlgebraicCurve.Defs.PlaceCalculus",
    "AlgebraicCurve.Place.ord": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ordDifferential": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.ordDifferential_smul": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.ord_algebraMap": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ord_coe_unit": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ord_inv": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ord_mul": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ord_uniformizer": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.ord_uniformizerSubring": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
    "AlgebraicCurve.Place.ord_zero": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.ord_zpow": "FLTForHuman.AlgebraicCurve.Defs.Place",
    "AlgebraicCurve.Place.uniformizer": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.uniformizerSubring": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.Place.uniformizer_ne_zero": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne": "FLTForHuman.AlgebraicCurve.P1.DXCoeff",
    "AlgebraicCurve.ResiduePairingSurjective": "FLTForHuman.AlgebraicCurve.Defs.WeilOfKaehler",
    "AlgebraicCurve.ResidueTheoremK": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.RiemannGenusBounded": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.RiemannGenusReached": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.RiemannGenusReachedAt": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.RiemannIndexFormula": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.RiemannInequality": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.StichtenothGenusExists": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.ValSubringKaehlerFinite": "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
    "AlgebraicCurve.ValSubringKaehlerSpanTop": "FLTForHuman.AlgebraicCurve.Canonical.ValSubringKaehler",
    "AlgebraicCurve.WeilDifferentialRankOne": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.WeilDuality": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.WeilDualityAdelic": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.WeilOmegaEllAgrees": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.adeleBdd": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.adeleBddPrincipal": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.adeleSingle": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.adeleSpace": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.canonicalClass": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.canonicalDivisorOf": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.canonicalDivisorOf_apply": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.constantsAreBase_of_deg_eq_one": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.constantsAreBase_of_isAlgClosed": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.degree_add_one_sub_genus_le_ell_of_riemannIndexFormula": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.diagonalHom": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.diagonal_mem_adeleSpace": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.ell": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.ell_sub_le_indexOfSpecialty": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.ell_zero_eq_one_of_constantsAreBase": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.exists_weilCanonical_riemannRoch": "FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly",
    "AlgebraicCurve.finrank_adeleBdd_inf_global_eq_ell": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.finrank_kaehler_eq_card_of_separating'": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.finrank_omegaSpace_eq_indexOfSpecialty": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.functionFieldRiemannRoch_of_residueTheoremK_of_isAlgClosed": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.functionFieldRiemannRoch_of_riemann_and_duality": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.genus": "FLTForHuman.AlgebraicCurve.Defs.CanonicalDivisor",
    "AlgebraicCurve.genusFF": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.genus_eq_degree_div": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.genus_eq_genusFF": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.globalSub": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver": "FLTForHuman.AlgebraicCurve.Canonical.HasCanonicalDivisor",
    "AlgebraicCurve.indexOfSpecialty": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.indexOfSpecialty_eq": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.indexOfSpecialty_eq_finrank_H1": "FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly",
    "AlgebraicCurve.kaehlerAdjoinBasis": "FLTForHuman.AlgebraicCurve.IsCurveOver.SeparatingTranscendental",
    "AlgebraicCurve.kaehlerRankOne_of_transcendental": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
    "AlgebraicCurve.kaehlerRankOne_ratFunc": "FLTForHuman.AlgebraicCurve.P1.UnitFinite",
    "AlgebraicCurve.lSpace_mono": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.map_diagonal_lSpace": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.mem_adeleSpace_iff": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.mem_lSpace_iff": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.mem_lSpace_iff_ord": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.omegaSpace": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.omegaSpaceEquivIndexDual": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.one_mem_lSpace_zero": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.principalRepartitions": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.repartitions": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.repartitionsOf": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.residuePairing": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.residuePairingSurjective_of_riemannIndexFormula": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.residuePairing_injective": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.residuePairing_surjective": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.riemannIndexFormula_of_genusReached": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.riemannRochSpace": "FLTForHuman.AlgebraicCurve.Defs.Repartitions",
    "AlgebraicCurve.stichtenothGenus_nonneg": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "AlgebraicCurve.weilDifferentialModule": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicCurve.weilDuality_of_riemannIndex_of_adelic": "FLTForHuman.AlgebraicCurve.Defs.RiemannRochRows",
    "AlgebraicCurve.weilOfKaehlerK": "FLTForHuman.AlgebraicCurve.Defs.LocalResidue",
    "AlgebraicCurve.weilSmul": "FLTForHuman.AlgebraicCurve.Defs.AdelicIndex",
    "AlgebraicIndependent": "Mathlib.RingTheory.AlgebraicIndependent.Defs",
    "AlgebraicIndependent.aevalEquiv": "Mathlib.RingTheory.AlgebraicIndependent.Defs",
    "Bot": "Mathlib.Order.Notation",
    "Bot.bot": "Mathlib.Order.Notation",
    "Cardinal": "Mathlib.SetTheory.Cardinal.Defs",
    "Cardinal.mk": "Mathlib.SetTheory.Cardinal.Defs",
    "Classical.choose": "Init.Classical",
    "Classical.decEq": "Mathlib.Basic.Logic.Basic",
    "Classical.indefiniteDescription": "Init.Classical",
    "Classical.propDecidable": "Init.Classical",
    "CommRing": "Mathlib.Algebra.Ring.Defs",
    "CommSemiring": "Mathlib.Algebra.Ring.Defs",
    "Derivation": "Mathlib.RingTheory.Derivation.Basic",
    "Derivation.leibniz": "Mathlib.RingTheory.Derivation.Basic",
    "Derivation.leibniz_pow": "Mathlib.RingTheory.Derivation.Basic",
    "Derivation.liftKaehlerDifferential": "Mathlib.RingTheory.Kaehler.Basic",
    "Derivation.liftKaehlerDifferential_comp": "Mathlib.RingTheory.Kaehler.Basic",
    "Derivation.liftKaehlerDifferential_comp_D": "Mathlib.RingTheory.Kaehler.Basic",
    "Derivation.llcomp": "Mathlib.RingTheory.Derivation.Basic",
    "Derivation.map_algebraMap": "Mathlib.RingTheory.Derivation.Basic",
    "Derivation.tensorProductTo": "Mathlib.RingTheory.Kaehler.Basic",
    "DivisionRing": "Mathlib.Algebra.Field.Defs",
    "Dvd.dvd": "Init.Prelude",
    "Equiv": "Mathlib.Logic.Equiv.Defs",
    "Equiv.punitProd": "Mathlib.Logic.Equiv.Prod",
    "Equiv.trans": "Mathlib.Logic.Equiv.Defs",
    "Even": "Mathlib.Algebra.Group.Even",
    "Exists.choose": "Init.Classical",
    "ExistsUnique": "Mathlib.Basic.ExistsUnique",
    "FLTForHuman.Elliptic.EvenRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.HaveSameParity₄": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.HaveSameParity₄.rel₄_transf": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.OddRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.Param": "FLTForHuman.Elliptic.EDS",
    "FLTForHuman.Elliptic.Rel₃": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.Rel₄OfValid": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.StrictAnti₄": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.addMulSub": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.avg₄": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.card_nTorsion": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_mul_of_coprime": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_odd_fibers": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_one": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_prime": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_prime_pow": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_nTorsion_two": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_smul_fiber": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.card_torsion_of_isAlgClosed": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.complEDSAux": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.evalEval_φ": "FLTForHuman.Elliptic.Bridge",
    "FLTForHuman.Elliptic.evalEval_ψ_sq": "FLTForHuman.Elliptic.Bridge",
    "FLTForHuman.Elliptic.exists_double_fiber_card": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.finite_not_squarefree_fiber": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.invar": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.invarDenom": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.invarNum": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.invarNum_eq_redInvarNum_mul": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.invar_normEDS": "FLTForHuman.Elliptic.Net",
    "FLTForHuman.Elliptic.invar_of_net": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.invar₂_normEDS": "FLTForHuman.Elliptic.Net",
    "FLTForHuman.Elliptic.isCoprime_Φ_ΨSq": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.isCoprime_ΨSq_succ": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.isEllipticSequence_ext": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.isEllipticSequence_iff_rel₃": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.isEllipticSequence_of_oddRec_evenRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.mem_nTorsion_two_iff": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.net": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.net_normEDS": "FLTForHuman.Elliptic.Net",
    "FLTForHuman.Elliptic.net_of_isEllipticSequence": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.net_zero_iff_rel₃": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.normEDS_eq_aeval": "FLTForHuman.Elliptic.EDS",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.normEDS_isEllipticSequence_of_mem_nonZeroDivisors": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS": "FLTForHuman.Elliptic.Complement",
    "FLTForHuman.Elliptic.normEDS_mul_complEDS_div": "FLTForHuman.Elliptic.Complement",
    "FLTForHuman.Elliptic.normEDS_two_three_two": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.preΨ₄_add_Ψ₂Sq_sq": "FLTForHuman.Elliptic.Omega",
    "FLTForHuman.Elliptic.redInvarDenom": "FLTForHuman.Elliptic.RedInvar",
    "FLTForHuman.Elliptic.redInvarNum": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.redInvar_normEDS": "FLTForHuman.Elliptic.Net",
    "FLTForHuman.Elliptic.rel₃_iff_evenRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.rel₃_iff_oddRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.rel₃_iff₄": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.rel₄": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.rel₄_of_anti_oddRec_evenRec": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.smul_eq_zero_of_ΨSq_eval_eq_zero": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.smul_formula_or_zero": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.smul_surjective": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.smul_x_eq": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.two_mul_ωe": "FLTForHuman.Elliptic.Omega",
    "FLTForHuman.Elliptic.universalNormEDS": "FLTForHuman.Elliptic.EDS",
    "FLTForHuman.Elliptic.universalNormEDS_mem_nonZeroDivisors": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.universalNormEDS_ne_zero": "FLTForHuman.Elliptic.EllSequence",
    "FLTForHuman.Elliptic.wronskian_Φ_ΨSq_ne_zero": "FLTForHuman.Elliptic.TorsionCard",
    "FLTForHuman.Elliptic.ψc": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.ψc_spec": "FLTForHuman.Elliptic.DivisionPolynomial",
    "FLTForHuman.Elliptic.ωe": "FLTForHuman.Elliptic.Omega",
    "FLTForHuman.Elliptic.ωe_spec": "FLTForHuman.Elliptic.Omega",
    "Fact": "Mathlib.Basic.Logic.Basic",
    "Field": "Mathlib.Algebra.Field.Defs",
    "Finite": "Mathlib.Basic.Finite.Defs",
    "FiniteDimensional": "Mathlib.LinearAlgebra.FiniteDimensional.Defs",
    "Finset": "Mathlib.Data.Finset.Defs",
    "Finset.card": "Mathlib.Data.Finset.Card",
    "Finset.sum": "Mathlib.Algebra.BigOperators.Group.Finset.Defs",
    "Finsupp": "Mathlib.Data.Finsupp.Defs",
    "Finsupp.liftAddHom": "Mathlib.Algebra.BigOperators.Finsupp.Basic",
    "Finsupp.module": "Mathlib.Data.Finsupp.SMul",
    "Finsupp.single": "Mathlib.Data.Finsupp.Single",
    "Finsupp.support": "Mathlib.Data.Finsupp.Defs",
    "FreeAddMonoid": "Mathlib.Algebra.FreeMonoid.Basic",
    "FunLike": "Mathlib.Data.FunLike.Basic",
    "Function.Injective": "Init.Data.Function",
    "Function.Odd": "Mathlib.Algebra.Group.EvenFunction",
    "Function.RightInverse": "Init.Data.Function",
    "Function.Surjective": "Init.Data.Function",
    "Function.algebra": "Mathlib.Algebra.Algebra.Pi",
    "Function.comp": "Init.Prelude",
    "GE.ge": "Init.Prelude",
    "HMod.hMod": "Init.Prelude",
    "HSMul.hSMul": "Init.Prelude",
    "HasQuotient.Quotient": "Mathlib.Algebra.Quotient",
    "Ideal": "Mathlib.RingTheory.Ideal.Defs",
    "Ideal.Cotangent": "Mathlib.RingTheory.Ideal.Cotangent",
    "Ideal.Cotangent.smul_eq_zero_of_mem": "Mathlib.RingTheory.Ideal.Cotangent",
    "Ideal.IsTwoSided": "Mathlib.RingTheory.Ideal.Defs",
    "Ideal.Quotient.mk": "Mathlib.RingTheory.Ideal.Quotient.Defs",
    "Ideal.comap": "Mathlib.RingTheory.Ideal.Maps",
    "Ideal.map_toCotangent_ker": "Mathlib.RingTheory.Ideal.Cotangent",
    "Ideal.mk_ker": "Mathlib.RingTheory.Ideal.Quotient.Operations",
    "Ideal.mul_mem_left": "Mathlib.RingTheory.Ideal.Defs",
    "Ideal.mul_mem_mul": "Mathlib.RingTheory.Ideal.Operations",
    "Ideal.span": "Mathlib.RingTheory.Ideal.Span",
    "Ideal.toCotangent": "Mathlib.RingTheory.Ideal.Cotangent",
    "Ideal.toCotangent_eq": "Mathlib.RingTheory.Ideal.Cotangent",
    "Infinite": "Mathlib.Basic.Finite.Defs",
    "Int": "Init.Data.Int.Basic",
    "Int.cast": "Init.Data.Int.Basic",
    "Int.decLt": "Init.Data.Int.Basic",
    "Int.inductionOn'": "Mathlib.Data.Int.Init",
    "Int.natAbs": "Init.Data.Int.Basic",
    "Int.negOnePow": "Mathlib.Algebra.Ring.NegOnePow",
    "Int.sign": "Init.Data.Int.Basic",
    "Int.strongRec": "Mathlib.Data.Int.Init",
    "Int.tdiv": "Init.Data.Int.DivMod.Basic",
    "IntermediateField": "Mathlib.FieldTheory.IntermediateField.Basic",
    "IntermediateField.adjoin": "Mathlib.FieldTheory.IntermediateField.Adjoin.Defs",
    "IntermediateField.algebra'": "Mathlib.FieldTheory.IntermediateField.Basic",
    "Inv.inv": "Init.Prelude",
    "InvImage": "Init.Core",
    "Irreducible": "Mathlib.Algebra.Group.Irreducible.Defs",
    "Irreducible.maximalIdeal_eq": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
    "IsAlgClosed": "Mathlib.FieldTheory.IsAlgClosed.Basic",
    "IsCoprime": "Mathlib.RingTheory.Coprime.Basic",
    "IsDedekindDomain": "Mathlib.RingTheory.DedekindDomain.Basic",
    "IsDedekindDomain.HeightOneSpectrum": "Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas",
    "IsDedekindDomain.HeightOneSpectrum.asIdeal": "Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas",
    "IsDedekindDomain.HeightOneSpectrum.intValuation": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_le_one": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
    "IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
    "IsDedekindDomain.HeightOneSpectrum.valuation": "Mathlib.RingTheory.DedekindDomain.AdicValuation",
    "IsDiscreteValuationRing": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
    "IsDiscreteValuationRing.exists_irreducible": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
    "IsDiscreteValuationRing.irreducible_iff_uniformizer": "Mathlib.RingTheory.DiscreteValuationRing.Basic",
    "IsDiscreteValuationRing.maximalIdeal": "Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing",
    "IsDomain": "Mathlib.Algebra.Ring.Defs",
    "IsDvdSequence": "Mathlib.Data.Nat.DvdSequence",
    "IsEllipticDvdSequence": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet.atom": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet.atomRel": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet.atomRel_eq": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet.rel": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticNet.rel_eq": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsEllipticSequence": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "IsFractionRing.algEquivOfAlgEquiv": "Mathlib.RingTheory.Localization.FractionRing",
    "IsLocalRing.ResidueField": "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
    "IsLocalRing.ResidueField.algebra": "Mathlib.RingTheory.LocalRing.ResidueField.Basic",
    "IsLocalRing.ResidueField.field": "Mathlib.RingTheory.LocalRing.ResidueField.Defs",
    "IsLocalRing.maximalIdeal": "Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs",
    "IsLocalization": "Mathlib.RingTheory.Localization.Defs",
    "IsScalarTower": "Mathlib.Algebra.Group.Action.Defs",
    "IsScalarTower.algebraMap_smul": "Mathlib.Algebra.Algebra.Tower",
    "IsScalarTower.left": "Mathlib.Algebra.Group.Action.Defs",
    "IsScalarTower.right": "Mathlib.Algebra.Algebra.Defs",
    "IsScalarTower.to_smulCommClass": "Mathlib.Algebra.Algebra.Basic",
    "IsSeparable": "Mathlib.FieldTheory.Separable",
    "IsUnit": "Mathlib.Algebra.Group.Units.Defs",
    "KaehlerDifferential": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.D": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.DLinearMap": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.D_apply": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.D_ne_zero_of_transcendental": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
    "KaehlerDifferential.ideal": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.isScalarTower_of_tower": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.linearMapEquivDerivation": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.mapBaseChange": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.mvPolynomialBasis": "Mathlib.RingTheory.Kaehler.Polynomial",
    "KaehlerDifferential.one_smul_sub_smul_one_mem_ideal": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.polynomialEquiv": "Mathlib.RingTheory.Kaehler.Polynomial",
    "KaehlerDifferential.polynomialEquiv_D": "Mathlib.RingTheory.Kaehler.Polynomial",
    "KaehlerDifferential.polynomialEquiv_symm": "Mathlib.RingTheory.Kaehler.Polynomial",
    "KaehlerDifferential.polynomial_D_apply": "Mathlib.RingTheory.Kaehler.Polynomial",
    "KaehlerDifferential.span_D_eq_top_of_transcendental": "FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental",
    "KaehlerDifferential.span_range_eq_ideal": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.subsingleton_of_surjective": "Mathlib.RingTheory.Kaehler.Basic",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale": "Mathlib.RingTheory.Etale.Kaehler",
    "KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap": "Mathlib.RingTheory.Etale.Kaehler",
    "KaehlerDifferential.tensorProductTo_surjective": "Mathlib.RingTheory.Kaehler.Basic",
    "LinearEquiv": "Mathlib.Algebra.Module.Equiv.Defs",
    "LinearEquiv.ofBijective": "Mathlib.Algebra.Module.Submodule.Equiv",
    "LinearEquiv.symm": "Mathlib.Algebra.Module.Equiv.Defs",
    "LinearEquiv.trans": "Mathlib.Algebra.Module.Equiv.Defs",
    "LinearIndependent": "Mathlib.LinearAlgebra.LinearIndependent.Defs",
    "LinearIndependent.finrank_eq_zero_of_infinite": "Mathlib.LinearAlgebra.Dimension.Finite",
    "LinearMap": "Mathlib.Algebra.Module.LinearMap.Defs",
    "LinearMap.addCommMonoid": "Mathlib.Algebra.Module.LinearMap.Defs",
    "LinearMap.comp": "Mathlib.Algebra.Module.LinearMap.Defs",
    "LinearMap.flip": "Mathlib.LinearAlgebra.BilinearMap",
    "LinearMap.ker": "Mathlib.Algebra.Module.Submodule.Ker",
    "LinearMap.lsmul": "Mathlib.LinearAlgebra.BilinearMap",
    "LinearMap.mk₂": "Mathlib.LinearAlgebra.BilinearMap",
    "LinearMap.module": "Mathlib.Algebra.Module.LinearMap.Defs",
    "LinearMap.mul": "Mathlib.Algebra.Algebra.Bilinear",
    "LinearMap.range": "Mathlib.Algebra.Module.Submodule.Range",
    "LinearMap.restrictScalars": "Mathlib.Algebra.Module.LinearMap.Defs",
    "List.Pairwise": "Init.Data.List.Basic",
    "Max.max": "Init.Prelude",
    "Min.min": "Init.Prelude",
    "ModularCurve.wkc_degree_canonicalDivisor_eq_of_weilMax": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "ModularCurve.wkc_ell_canonicalDivisor_eq_gamma_of_weilMax": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "ModularCurve.wkc_finrank_omegaSpace_eq_ell_of_genusReached_of_weilMax": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "ModularCurve.wkc_functionFieldRiemannRoch_of_residueTheoremK": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "ModularCurve.wkc_riemannIndexFormula_of_weilMax": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "ModularCurve.wkc_weilOfKaehlerK_single": "FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly",
    "Module": "Mathlib.Algebra.Module.Defs",
    "Module.Basis": "Mathlib.LinearAlgebra.Basis.Defs",
    "Module.Basis.baseChange": "Mathlib.LinearAlgebra.TensorProduct.Basis",
    "Module.Basis.map": "Mathlib.LinearAlgebra.Basis.Defs",
    "Module.Basis.ne_zero": "Mathlib.LinearAlgebra.Basis.Basic",
    "Module.Basis.reindex": "Mathlib.LinearAlgebra.Basis.Defs",
    "Module.Basis.repr": "Mathlib.LinearAlgebra.Basis.Defs",
    "Module.Basis.singleton": "Mathlib.LinearAlgebra.Basis.Basic",
    "Module.Basis.span_eq": "Mathlib.LinearAlgebra.Basis.Basic",
    "Module.Basis.tensorProduct": "Mathlib.LinearAlgebra.TensorProduct.Basis",
    "Module.Dual": "Mathlib.LinearAlgebra.Dual.Defs",
    "Module.End": "Mathlib.Algebra.Module.LinearMap.End",
    "Module.Finite": "Mathlib.RingTheory.Finiteness.Defs",
    "Module.Free": "Mathlib.LinearAlgebra.FreeModule.Basic",
    "Module.finrank": "Mathlib.LinearAlgebra.Dimension.Finrank",
    "Module.rank": "Mathlib.LinearAlgebra.Dimension.Basic",
    "Monoid": "Mathlib.Algebra.Group.Monoid",
    "MonoidWithZeroHom": "Mathlib.Algebra.GroupWithZero.Hom",
    "MonoidWithZeroHom.funLike": "Mathlib.Algebra.GroupWithZero.Hom",
    "Mul": "Init.Prelude",
    "MulAction": "Mathlib.Algebra.Group.Action.Defs",
    "Multiplicative": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.commMonoid": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.group": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.isOrderedCancelMonoid": "Mathlib.Algebra.Order.Monoid.TypeTags",
    "Multiplicative.linearOrder": "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
    "Multiplicative.monoid": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.mul": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.ofAdd": "Mathlib.Algebra.Group.TypeTags.Basic",
    "Multiplicative.preorder": "Mathlib.Algebra.Order.Monoid.Unbundled.TypeTags",
    "MvPolynomial": "Mathlib.Algebra.MvPolynomial.Basic",
    "MvPolynomial.X": "Mathlib.Algebra.MvPolynomial.Basic",
    "MvPolynomial.aeval": "Mathlib.Algebra.MvPolynomial.Eval",
    "Nat": "Init.Prelude",
    "Nat.Coprime": "Init.Data.Nat.Coprime",
    "Nat.Prime": "Mathlib.Data.Nat.Prime.Defs",
    "Nat.card": "Mathlib.SetTheory.Cardinal.Finite",
    "Nat.cast": "Init.Data.Cast",
    "Nat.recOnPosPrimePosCoprime": "Mathlib.Data.Nat.Factorization.Induction",
    "Nat.recOnPrimePow": "Mathlib.Data.Nat.Factorization.Induction",
    "Ne": "Init.Core",
    "NoZeroDivisors": "Mathlib.Algebra.GroupWithZero.Defs",
    "NonUnitalNonAssocSemiring": "Mathlib.Algebra.Ring.Defs",
    "Nonempty": "Init.Prelude",
    "Nontrivial": "Mathlib.Basic.Nontrivial.Defs",
    "Odd": "Mathlib.Algebra.Ring.Parity",
    "Option": "Init.Prelude",
    "Option.map₂": "Mathlib.Data.Option.NAry",
    "OreLocalization.oreSetComm": "Mathlib.GroupTheory.OreLocalization.OreSet",
    "PerfectField": "Mathlib.FieldTheory.Perfect",
    "Pi.Function.module": "Mathlib.Algebra.Module.Pi",
    "Pi.addCommGroup": "Mathlib.Algebra.Group.Pi.Basic",
    "Pi.addCommMonoid": "Mathlib.Algebra.Group.Pi.Basic",
    "Pi.isScalarTower": "Mathlib.Algebra.Group.Action.Pi",
    "Pi.nonAssocSemiring": "Mathlib.Algebra.Ring.Pi",
    "Polynomial": "Mathlib.Algebra.Polynomial.Basic",
    "Polynomial.C": "Mathlib.Algebra.Polynomial.Basic",
    "Polynomial.CC": "Mathlib.Algebra.Polynomial.Bivariate",
    "Polynomial.Separable": "Mathlib.FieldTheory.Separable",
    "Polynomial.X": "Mathlib.Algebra.Polynomial.Basic",
    "Polynomial.algEquivOfTranscendental": "Mathlib.RingTheory.Algebraic.Basic",
    "Polynomial.algebraOfAlgebra": "Mathlib.Algebra.Polynomial.AlgebraMap",
    "Polynomial.degree": "Mathlib.Algebra.Polynomial.Degree.Defs",
    "Polynomial.derivative": "Mathlib.Algebra.Polynomial.Derivative",
    "Polynomial.derivative'": "Mathlib.Algebra.Polynomial.Derivation",
    "Polynomial.eval": "Mathlib.Algebra.Polynomial.Eval.Defs",
    "Polynomial.evalEval": "Mathlib.Algebra.Polynomial.Bivariate",
    "Polynomial.module": "Mathlib.Algebra.Polynomial.Basic",
    "Polynomial.monomial": "Mathlib.Algebra.Polynomial.Basic",
    "Polynomial.natDegree": "Mathlib.Algebra.Polynomial.Degree.Defs",
    "Preorder": "Mathlib.Order.Defs.PartialOrder",
    "Prod": "Init.Prelude",
    "QuotientAddGroup.Quotient.addCommGroup": "Mathlib.GroupTheory.QuotientGroup.Defs",
    "QuotientAddGroup.mk": "Mathlib.GroupTheory.Coset.Defs",
    "RatFunc": "Mathlib.FieldTheory.RatFunc.Defs",
    "RatFunc.X": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
    "RatFunc.algEquivOfTranscendental": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
    "RatFunc.algEquivOfTranscendental_X": "Mathlib.FieldTheory.RatFunc.AsPolynomial",
    "Ring": "Mathlib.Algebra.Ring.Defs",
    "RingEquiv": "Mathlib.Algebra.Ring.Equiv",
    "RingHom": "Mathlib.Algebra.Ring.Hom.Defs",
    "RingHom.comp": "Mathlib.Algebra.Ring.Hom.Defs",
    "RingHom.id": "Mathlib.Algebra.Ring.Hom.Defs",
    "RingHom.ker": "Mathlib.RingTheory.Ideal.Maps",
    "RingHom.kerLift": "Mathlib.RingTheory.Ideal.Quotient.Operations",
    "RingHom.mem_ker": "Mathlib.RingTheory.Ideal.Maps",
    "RingHom.quotientKerEquivOfRightInverse": "Mathlib.RingTheory.Ideal.Quotient.Operations",
    "RingHom.quotientKerEquivOfSurjective": "Mathlib.RingTheory.Ideal.Quotient.Operations",
    "RingHomClass": "Mathlib.Algebra.Ring.Hom.Defs",
    "RingHomInvPair.ids": "Mathlib.Algebra.Ring.CompTypeclasses",
    "RingHomSurjective.ids": "Mathlib.Algebra.Ring.CompTypeclasses",
    "SMul": "Init.Prelude",
    "SMulCommClass": "Mathlib.Algebra.Group.Action.Defs",
    "SMulWithZero": "Mathlib.Algebra.GroupWithZero.Action.Defs",
    "Semiring": "Mathlib.Algebra.Ring.Defs",
    "Set": "Mathlib.Data.Set.Defs",
    "Set.Finite": "Mathlib.Basic.Finite.Defs",
    "Set.ofPred": "Mathlib.Data.Set.Defs",
    "Set.range": "Mathlib.Data.Set.Operations",
    "Set.univ": "Mathlib.Data.Set.Defs",
    "Squarefree": "Mathlib.Algebra.Squarefree.Basic",
    "Subalgebra": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
    "Subalgebra.algebra": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
    "Subalgebra.algebra'": "Mathlib.Algebra.Algebra.Subalgebra.Basic",
    "Submodule": "Mathlib.Algebra.Module.Submodule.Defs",
    "Submodule.Quotient.addCommMonoid": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.Quotient.mk": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.Quotient.module": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.Quotient.module'": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.Quotient.restrictScalarsEquiv": "Mathlib.LinearAlgebra.Quotient.Basic",
    "Submodule.addCommGroup": "Mathlib.Algebra.Module.Submodule.Defs",
    "Submodule.addCommMonoid": "Mathlib.Algebra.Module.Submodule.Defs",
    "Submodule.comap": "Mathlib.Algebra.Module.Submodule.Map",
    "Submodule.completeLattice": "Mathlib.Algebra.Module.Submodule.Lattice",
    "Submodule.dualAnnihilator": "Mathlib.LinearAlgebra.Dual.Defs",
    "Submodule.dualQuotEquivDualAnnihilator": "Mathlib.LinearAlgebra.Dual.Lemmas",
    "Submodule.hasQuotient": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.idemSemiring": "Mathlib.Algebra.Algebra.Operations",
    "Submodule.liftQ": "Mathlib.LinearAlgebra.Quotient.Basic",
    "Submodule.map": "Mathlib.Algebra.Module.Submodule.Map",
    "Submodule.mem_bot": "Mathlib.Algebra.Module.Submodule.Lattice",
    "Submodule.mem_top": "Mathlib.Algebra.Module.Submodule.Lattice",
    "Submodule.mem_torsionBy_iff": "Mathlib.Algebra.Module.Torsion.Basic",
    "Submodule.mkQ": "Mathlib.LinearAlgebra.Quotient.Defs",
    "Submodule.module": "Mathlib.Algebra.Module.Submodule.Defs",
    "Submodule.module'": "Mathlib.Algebra.Module.Submodule.Defs",
    "Submodule.mul": "Mathlib.Algebra.Algebra.Operations",
    "Submodule.restrictScalars": "Mathlib.Algebra.Module.Submodule.RestrictScalars",
    "Submodule.span": "Mathlib.LinearAlgebra.Span.Defs",
    "Submodule.subtype": "Mathlib.Algebra.Module.Submodule.LinearMap",
    "Submodule.torsionBy": "Mathlib.Algebra.Module.Torsion.Basic",
    "Submonoid": "Mathlib.Algebra.Group.Submonoid.Defs",
    "Subsingleton": "Init.Core",
    "Subspace.dual_finrank_eq": "Mathlib.LinearAlgebra.Dual.Lemmas",
    "TensorProduct": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.AlgebraTensorModule.lift": "Mathlib.LinearAlgebra.TensorProduct.Tower",
    "TensorProduct.AlgebraTensorModule.mk": "Mathlib.LinearAlgebra.TensorProduct.Tower",
    "TensorProduct.Eqv": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.addCommGroup": "Mathlib.LinearAlgebra.TensorProduct.Basic",
    "TensorProduct.addCommMonoid": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.homTensorHomMap": "Mathlib.LinearAlgebra.TensorProduct.Map",
    "TensorProduct.leftHasSMul": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.leftModule": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.map": "Mathlib.LinearAlgebra.TensorProduct.Map",
    "TensorProduct.map₂": "Mathlib.LinearAlgebra.TensorProduct.Map",
    "TensorProduct.smulCommClass_left": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "TensorProduct.tmul": "Mathlib.LinearAlgebra.TensorProduct.Defs",
    "Top": "Mathlib.Order.Notation",
    "Top.top": "Mathlib.Order.Notation",
    "Transcendental": "Mathlib.RingTheory.Algebraic.Defs",
    "Transcendental.pow": "Mathlib.RingTheory.Algebraic.Basic",
    "True": "Init.Prelude",
    "Unit": "Init.Prelude",
    "Units": "Mathlib.Algebra.Group.Units.Defs",
    "Units.val": "Mathlib.Algebra.Group.Units.Defs",
    "Valuation": "Mathlib.RingTheory.Valuation.Basic",
    "ValuationSubring": "Mathlib.RingTheory.Valuation.ValuationSubring",
    "WeierstrassCurve": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.Affine": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.Affine.CoordinateRing": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point",
    "WeierstrassCurve.Affine.CoordinateRing.mk": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point",
    "WeierstrassCurve.Affine.CoordinateRing.mk_Ψ_sq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Affine.CoordinateRing.mk_φ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Affine.CoordinateRing.mk_ψ₂_sq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Affine.Equation": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.Affine.Nonsingular": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.Affine.Point": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point",
    "WeierstrassCurve.Affine.negPolynomial": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
    "WeierstrassCurve.Affine.negY": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Formula",
    "WeierstrassCurve.Affine.polynomial": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.Affine.polynomialX": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.Affine.polynomialY": "Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic",
    "WeierstrassCurve.C_Ψ₂Sq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.IsElliptic": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.a₁": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.a₃": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.baseChange": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.b₂": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.b₄": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.b₆": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.b₈": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.isElliptic_iff": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.mk": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.natDegree_Φ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
    "WeierstrassCurve.natDegree_ΨSq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree",
    "WeierstrassCurve.preΨ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.preΨ'": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.preΨ_even": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.preΨ_odd": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.preΨ₄": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.twoTorsionPolynomial": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.Δ": "Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass",
    "WeierstrassCurve.Φ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Φ_neg": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Φ_three": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Ψ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ΨSq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ΨSq_three": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Ψ₂Sq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Ψ₂Sq_eq": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.Ψ₃": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.φ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ψ": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ψ_one": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ψ_two": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ψ_zero": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WeierstrassCurve.ψ₂": "Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic",
    "WellFounded.Nat.fix": "Init.WF",
    "WithBot.unbotD": "Mathlib.Order.WithBot",
    "WithZero": "Mathlib.Algebra.Group.WithOne.Defs",
    "WithZero.exp": "Mathlib.Algebra.GroupWithZero.WithZero",
    "WithZero.log": "Mathlib.Algebra.GroupWithZero.WithZero",
    "WithZero.logEquiv": "Mathlib.Algebra.GroupWithZero.WithZero",
    "WithZero.log_mul": "Mathlib.Algebra.GroupWithZero.WithZero",
    "WithZero.map₂": "Mathlib.Algebra.Group.WithOne.Map",
    "WithZero.one": "Mathlib.Algebra.GroupWithZero.WithZero",
    "WithZero.recZeroCoe": "Mathlib.Algebra.Group.WithOne.Defs",
    "WithZero.unitsWithZeroEquiv": "Mathlib.Algebra.GroupWithZero.WithZero",
    "Zero": "Init.Prelude",
    "abs": "Mathlib.Algebra.Order.Group.Unbundled.Abs",
    "addConGen": "Mathlib.GroupTheory.Congruence.Defs",
    "addOrderOf": "Mathlib.GroupTheory.OrderOfElement",
    "addOrderOf_dvd_of_nsmul_eq_zero": "Mathlib.GroupTheory.OrderOfElement",
    "complEDS": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "complEDS'": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "complEDS₂": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "exists_prime_addOrderOf_dvd_card'": "Mathlib.GroupTheory.Perm.Cycle.Type",
    "exists_smul_eq_of_finrank_eq_one": "Mathlib.LinearAlgebra.FiniteDimensional.Basic",
    "iSup": "Mathlib.Order.SetNotation",
    "id": "Init.Prelude",
    "inferInstance": "Init.Prelude",
    "le_trans": "Mathlib.Order.Defs.PartialOrder",
    "minpoly": "Mathlib.FieldTheory.Minpoly.Basic",
    "nonZeroDivisors": "Mathlib.Algebra.GroupWithZero.NonZeroDivisors",
    "normEDS": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_dvd_normEDS_two_mul": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_even": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_four": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_mul_complEDS₂": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_neg": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_odd": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_one": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_three": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_two": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "normEDS_zero": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "npowRecAuto": "Mathlib.Algebra.Group.Monoid",
    "one_smul": "Mathlib.Algebra.Group.Action.Defs",
    "pow_two": "Mathlib.Algebra.Group.Monoid",
    "preNormEDS": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "preNormEDS'": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "preNormEDS_even": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "preNormEDS_odd": "Mathlib.NumberTheory.EllipticDivisibilitySequence",
    "semigroupDvd": "Mathlib.Algebra.Divisibility.Basic",
    "smulCommClass_self": "Mathlib.Algebra.Group.Action.Defs",
    "zero_smul": "Mathlib.Algebra.GroupWithZero.Action.Defs"
  }
};
