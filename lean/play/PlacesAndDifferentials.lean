/-
  PLAY · places and differentials — why a uniformiser is not a differential
  ============================================================================

  Subject   the two halves of the local theory and the gap between them: a place
            always has a uniformiser and an order, a differential is a global
            derivation, and nothing in the place data produces one. That gap is
            why `IsCurveOver` carries `kaehler_free_rank_one` as an axiom, and
            why every rung that names a canonical divisor carries
            `[∀ v, v.DCoordGenerates]` per place.
  Reads     FLTForHuman/AlgebraicCurve/Defs/Place.lean,
            Defs/CanonicalDivisor.lean, Defs/LocalResidue.lean,
            P1/DXCoeff.lean, IsCurveOver/SeparatingTranscendental.lean,
            Canonical/HasCanonicalDivisor.lean,
            Defs/RiemannRochRows.lean
  Pin       Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean (the `Place`
            structure and `ord`),
            Definitions/Def_ModularCurve_CanonicalDivisor.lean,
            Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean,
            Definitions/Def_AlgebraicCurve_IsCurveOver.lean,
            P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean,
            all at aa2d8b3
  Check     cd lean && lake env lean play/PlacesAndDifferentials.lean   (~5 s, oleans warm)
  Status    open
  Date      2026-10-23
  Intro     A place gives an order `ord_v` and a uniformiser `t_v`; a differential
            lives in the Kähler module `Ω[F⁄K]`, which is an object of the whole
            field extension and mentions no place. This sheet separates the two,
            exhibits each gate the port puts between them (`dCoord`,
            `DCoordGenerates`, `differentialCoeff`, `ordDifferential`,
            `HasCanonicalDivisor`), shows that the same order admits different
            differentials, and lands on the axiom that no amount of place data
            can supply: `kaehler_free_rank_one`.

  Zone list
    A  the place — unconditional: valuation ring, uniformiser, order, residue
    B  the differential — global: Ω, the universal derivation, what it sees
    C  the bridge — `d t_v`, the coefficient, the order, and their gates
    D  the three gaps — why the axiom is an axiom
    E  things to poke at
    Q  question log

  This is a worksheet, not library code: nothing globs `lean/play/`, the sheets
  are tracked, and it exists so that the ported statements can be read, poked at
  and questioned in the editor. Ground rules and workflow: `play/README.md`.
  The statement hierarchy this sits under is
  `base/023-riemann-roch-statement-hierarchy.md`; its worksheet is
  `play/RiemannRochHierarchy.lean`.

  Import cost. One import, `ResidueTheorem/RRAssembly` (the same cone as the
  hierarchy sheet), which carries `Defs/Place`, `Defs/CanonicalDivisor`,
  `Defs/LocalResidue`, `P1/DXCoeff` and `Canonical/HasCanonicalDivisor`. Warm it
  is ~5 s. Nothing here is a tree rebuild: `play/` is outside every `lean_lib`
  glob.
-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace Play

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/- ## Zone A — the place, unconditionally

A `Place` is a valuation subring with three side conditions. Read the field list
and note what is *absent*: nothing in a place mentions `Ω`, a derivation, or the
extension `F/K` beyond the `K`-algebra structure. -/
#print AlgebraicCurve.Place

/- The side conditions are that the constants are integral at `v`
(`algebraMap_mem'`), that the ring is proper (`ne_top'`), and that it is a
principal ideal ring. On top of being a valuation subring those give a discrete
valuation ring, which is what the port attaches to: -/
#check @IsDiscreteValuationRing.exists_irreducible
#check @AlgebraicCurve.Place.heightOneSpectrum
#check @AlgebraicCurve.Place.adicValuation
#check @AlgebraicCurve.Place.ord

/- The uniformiser: the `Classical.choose` of an irreducible of the valuation
subring, and all every later statement knows about it is `ord = 1`. -/
#check @AlgebraicCurve.Place.uniformizer
#check @AlgebraicCurve.Place.uniformizerSubring'
#check @AlgebraicCurve.Place.ord_uniformizer
#check @AlgebraicCurve.Place.uniformizer_ne_zero

example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=
  v.ord_uniformizer

/-- The chosen irreducible, as an element of the valuation subring — the same
choice `uniformizer` takes, in the place where `Irreducible` makes sense. -/
example (v : AlgebraicCurve.Place K F) : Irreducible v.uniformizerSubring' :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

/- The order is a valuation: additive on products, anti on inverses, and it does
not see units or constants at all. -/
#check @AlgebraicCurve.Place.ord_mul
#check @AlgebraicCurve.Place.ord_inv
#check @AlgebraicCurve.Place.ord_zpow
#check @AlgebraicCurve.Place.ord_algebraMap
#check @AlgebraicCurve.Place.ord_coe_unit
#check @AlgebraicCurve.Place.ord_unit_smul_zpow

/-- Every constant has order `0`: it is a unit at every place. -/
example (v : AlgebraicCurve.Place K F) (c : K) : v.ord (algebraMap K F c) = 0 :=
  v.ord_algebraMap c

/- **What a place knows about an element.** An element of `F` is a unit times the
uniformiser raised to its order; that decomposition is *all* `ord` records, and
the unit part is invisible to it (`ord_coe_unit`). This is the fact that the
differential will fail to respect. -/
#check @AlgebraicCurve.Place.exists_unit_mul_zpow

example (v : AlgebraicCurve.Place K F) {f : F} (hf : f ≠ 0) :
    ∃ u : v.toValuationSubringˣ,
      f = ((u : v.toValuationSubring) : F) * (v.uniformizerSubring' : F) ^ (v.ord f) :=
  v.exists_unit_mul_zpow hf (IsDiscreteValuationRing.exists_irreducible _).choose_spec

/- The residue data is local too, and *here* the place is already not enough: a
DVR does not bound the degree of `κ(v)` over `K`. Finiteness is a class, one of
`IsCurveOver`'s three axioms, and the port keeps it as a hypothesis rather than
deriving it from the place. -/
#check @AlgebraicCurve.Place.ResidueField
#check @AlgebraicCurve.Place.deg
#check @AlgebraicCurve.Place.FiniteResidue

/- ## Zone B — the differential, globally

`Ω[F⁄K]` is the module of Kähler differentials of the *algebra* `F/K`, and `D` is
the universal derivation into it. Both are objects of the extension; neither
mentions a place. -/
#check @KaehlerDifferential.D

/- `D` is a derivation, so it is `K`-linear, it satisfies Leibniz, and it kills
constants. Two consequences are the whole story of this sheet: -/
#check @Derivation.leibniz
#check @Derivation.leibniz_pow
#check @Derivation.map_algebraMap

/-- Constants have no differential. Compare with `v.ord_algebraMap` in Zone A:
the place says `ord = 0`, the differential says `d = 0` — the same conclusion by
two unrelated mechanisms. -/
example (c : K) : KaehlerDifferential.D K F (algebraMap K F c) = 0 :=
  Derivation.map_algebraMap (KaehlerDifferential.D K F) c

/-- **In characteristic `p`, `d` cannot see p-th powers.** `d (a ^ p) = 0` for
every `a`. So `d` is far from injective, and no amount of information about the
*elements* of `F` (their orders included) can be turned into `d` by arithmetic:
the kernel of `d` is a subfield containing all p-th powers. -/
example (p : ℕ) [CharP F p] (a : F) : KaehlerDifferential.D K F (a ^ p) = 0 := by
  rw [Derivation.leibniz_pow]
  have hp : (p : F) = 0 := CharP.cast_eq_zero F p
  rw [← Nat.cast_smul_eq_nsmul F p, hp, zero_smul]

/- **How big is `Ω`?** Its dimension over `F` is the size of a *separating*
transcendence basis: with `s` algebraically independent and `F` separable over
`K(s)`, the rank is `#s`. The word "separating" is the whole content — the
transcendence degree alone does not control the rank (D.1 below), and no place
can supply a separating transcendental. -/
#check @AlgebraicCurve.finrank_kaehler_eq_card_of_separating
#check @AlgebraicCurve.finrank_kaehler_eq_card_of_separating'
#check @AlgebraicCurve.kaehlerAdjoinBasis

/- ## Zone C — the bridge and its gates

The port does put a differential at every place, and it does so the only way
available: apply `D` to the chosen uniformiser. -/
#check @AlgebraicCurve.Place.dCoord

example (v : AlgebraicCurve.Place K F) :
    v.dCoord = KaehlerDifferential.D K F v.uniformizer := rfl

/- Everything else in this zone is *gated*. `DCoordGenerates` is the hypothesis
that this particular differential spans `Ω`; `differentialCoeff` and
`ordDifferential` are total functions (junk outside the span), and the lemmas
that make them honest all require the class. -/
#check @AlgebraicCurve.Place.DCoordGenerates
#check @AlgebraicCurve.Place.differentialCoeff
#check @AlgebraicCurve.Place.ordDifferential

example (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDifferential ω = v.ord (v.differentialCoeff ω) := rfl

/- The honest versions, each carrying `[v.DCoordGenerates]`: -/
#check @AlgebraicCurve.Place.exists_eq_smul_dCoord
#check @AlgebraicCurve.Place.differentialCoeff_smul_dCoord
#check @AlgebraicCurve.Place.differentialCoeff_unique
#check @AlgebraicCurve.Place.differentialCoeff_dCoord
#check @AlgebraicCurve.Place.differentialCoeff_zero
#check @AlgebraicCurve.Place.ordDifferential_smul

/- And the two that need `Nontrivial Ω` as well, i.e. a nonzero differential: the
rank-one axiom of Zone D is what supplies that instance. -/
#check @AlgebraicCurve.Place.dCoord_ne_zero
#check @AlgebraicCurve.Place.gate_ordDifferential_dCoord

/-- The junk branch, live: when `ω` is not a multiple of `d t_v`, the coefficient
is defined to be `0`. So `ordDifferential` silently records "no pole, no zero"
there — a value, not a truth. -/
example (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K])
    (h : ¬ ∃ f : F, ω = f • v.dCoord) : v.differentialCoeff ω = 0 := by
  simp only [AlgebraicCurve.Place.differentialCoeff]
  exact dite_eq_right h

/- **The crux.** Two elements with the same order have unrelated differentials.
`u * t_v` is a uniformiser as soon as `u` is a unit, so the place cannot tell the
two apart — while `d` differs by the Leibniz term `t_v • d u`. -/
example (v : AlgebraicCurve.Place K F) (u : F) (hu : u ≠ 0) (hord : v.ord u = 0) :
    v.ord (u * v.uniformizer) = 1 := by
  rw [v.ord_mul hu v.uniformizer_ne_zero, hord, v.ord_uniformizer]
  ring

/-- The other half of the crux: the same substitution moves the differential, by a
term the place has no record of. -/
example (v : AlgebraicCurve.Place K F) (u : F) :
    KaehlerDifferential.D K F (u * v.uniformizer)
      = u • KaehlerDifferential.D K F v.uniformizer
        + v.uniformizer • KaehlerDifferential.D K F u :=
  Derivation.leibniz (KaehlerDifferential.D K F) u v.uniformizer

/- So `d t_v` is a differential *of a choice*: the choice of uniformiser is a
`Classical.choose`, and the place's data (`ord`) is invariant under the change
that moves `d`. Zone A's `exists_unit_mul_zpow` says every element is
`u · t_v^ord`, so the place's total knowledge of an element is blind to the unit
— which is the part that `d` sees. -/

/- The last piece of the bridge is the *finite support* of the order function.
`HasCanonicalDivisor` says: for a nonzero `ω` there is a divisor `D` whose value
at `v` is `v.ordDifferential ω`, for every place. That is a statement about the
junk function above, and it is only meaningful when the coefficient is honest at
every place. -/
#check @AlgebraicCurve.HasCanonicalDivisor
#check @AlgebraicCurve.canonicalDivisorOf
#check @AlgebraicCurve.canonicalDivisorOf_apply

/- ## Zone D — the three gaps, and why the axiom is an axiom

There are exactly three things a place does not give, and the port carries each
one separately. -/

/- ### D.1 — `Ω` may not be a line

`kaehler_free_rank_one` is a field of `IsCurveOver`; the pin also states it
standalone, and the port keeps both names. Read them as the same proposition: -/
#check @AlgebraicCurve.KaehlerRankOne
#check @AlgebraicCurve.IsCurveOver.kaehler_free_rank_one

example [AlgebraicCurve.IsCurveOver K F] : AlgebraicCurve.KaehlerRankOne K F :=
  AlgebraicCurve.IsCurveOver.kaehler_free_rank_one

/- And the class is literally the three pieces, which is why the axiom is visible
as a field: -/
#check @AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne

example [AlgebraicCurve.HasPrincipalDivisors K F]
    [∀ v : AlgebraicCurve.Place K F, v.FiniteResidue]
    (h : AlgebraicCurve.KaehlerRankOne K F) : AlgebraicCurve.IsCurveOver K F :=
  AlgebraicCurve.IsCurveOver.of_finiteResidue_of_kaehlerRankOne h

/- Two consequences worth naming. Rank one **produces a nonzero differential**
(the port derives `Nontrivial Ω` from it, rather than assuming it), and it
**forces the transcendence degree to be one**: `trdeg_le_one` spends the
separating-basis theorem of Zone B, and `one_le_trdeg` spends `Nontrivial Ω`.
The converse fails: the counterexample below has `trdeg = 1` and rank two. -/
#check @AlgebraicCurve.IsCurveOver.instNontrivialKaehler
#check @AlgebraicCurve.IsCurveOver.one_le_trdeg
#check @AlgebraicCurve.IsCurveOver.trdeg_le_one
#check @AlgebraicCurve.IsCurveOver.trdeg_eq_one_of_perfectField

/- Why it cannot be derived from place data: a place is a structure on `F` alone
(Zone A), while the rank of `Ω` is a property of the *extension*. The standard
counterexample, not formalised here — take `k` of characteristic `p`,
`K = k(X)`, and `F = K(x)(t)` with `x ^ p = X` and `t` transcendental over
`K(x)`. Then:

* `trdeg(F/K) = 1`, and every place still has a uniformiser;
* `Ω[K(x)/K]` is free of rank one on `d x`: the defining relation `x ^ p = X`
  differentiates to `p x ^ (p - 1) d x = 0`, which is *no* relation in
  characteristic `p` — the p-th-power blindness of Zone B;
* `F = K(x)(t)` splits `Ω` as `Ω[K(x)/K] ⊗ F` plus `F · d t`, so
  `finrank_F Ω[F⁄K] = 2`.

So a one-variable function field can have a two-dimensional `Ω`, no uniformiser
is any the wiser, and no `ω` generates. This is the field that `kaehler_free_rank_one`
excludes, and the reason it has to be an axiom rather than a theorem about
places. The port's positive control is the rational function field: -/
#check @AlgebraicCurve.kaehlerRankOne_ratFunc
#check @AlgebraicCurve.RationalFunctionField.isCurveOver_of_kaehlerRankOne

/- ### D.2 — even a line may not be generated by `d t_v`

Grant `Ω` free of rank one. `d t_v` is *an* element of a line, so it is either a
generator or zero — and which one is not a place-level fact. That is
`DCoordGenerates`, quantified at every place in exactly the rungs that name a
canonical divisor.

The port's route from the axiom to the places is short, and worth reading in
order: a *separating transcendental* exists — perfectness plus rank one, which
pins the transcendence degree to one (D.1) — the differential of that
transcendental is nonzero and spans `Ω`, and from a global generator the
generation at every place follows. Note the direction: the transcendental
generates, the places inherit: -/
#check @AlgebraicCurve.IsCurveOver.exists_separating_transcendental
#check @KaehlerDifferential.D_ne_zero_of_transcendental
#check @KaehlerDifferential.span_D_eq_top_of_transcendental
#check @AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerSpanTop
#check @AlgebraicCurve.Place.dCoordGenerates_of_valSubringKaehlerFinite_of_perfectField

/- And here is the rung's own hypothesis list, printed so that the per-place
quantifier is visible: -/
#print AlgebraicCurve.WeilDualityAdelic

/- ### D.3 — the order function may not have finite support

The last gap is the one `HasCanonicalDivisor` closes, and the port *derives* it
rather than assuming it, from the curve axioms over a perfect field. Read the
proof's opening moves: it first derives the per-place generation that D.2 left as
a hypothesis (`Place.dCoordGenerates_of_valSubringKaehlerSpanTop`), then takes a
separating transcendental, and only then proves that the order function has
finite support. So D.1 and D.2 are not extra assumptions on this route — they are
*theorems* once the constant field is perfect: -/
#check @AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

example [PerfectField K] [Algebra.EssFiniteType K F] [AlgebraicCurve.IsCurveOver K F] :
    AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F) :=
  AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

/- The residue side carries its own, *separate*, per-place inputs — the same
lesson in a different coordinate. The K residue model needs a canonical local
residue datum at every place, on top of the canonical divisor and the generation;
the nonvanishing of the Weil/Kähler functional needs the trace to be nonzero at
every place: -/
#check @AlgebraicCurve.HasCanonicalLocalResidueKStar
#check @AlgebraicCurve.Place.CanonicalLocalResidueDataK
#check @AlgebraicCurve.HasSeparableResidue
#check @AlgebraicCurve.ResidueTheoremK

/- Perfectness supplies both, which is why the wrapper stack of the hierarchy
sheet can drop them: -/
#check @AlgebraicCurve.HasSeparableResidue.of_perfectField

example [PerfectField K] [∀ v : AlgebraicCurve.Place K F, v.FiniteResidue] :
    AlgebraicCurve.HasSeparableResidue K F :=
  AlgebraicCurve.HasSeparableResidue.of_perfectField

/- ## Zone E — things to poke at

* **Delete `[DCoordGenerates]`** from `exists_eq_smul_dCoord` in Zone C and the
  statement becomes false as a universally quantified claim: there is no single
  `f` with `ω = f • d t_v` for every `ω` unless `d t_v` spans. That is the whole
  content of the class, and the reason it cannot be an instance.

* **Delete `[Nontrivial Ω]`** from `dCoord_ne_zero`: with `Ω` subsingleton every
  differential is zero, so `d t_v ≠ 0` needs the rank-one axiom (D.1), not just
  generation.

* **Change the uniformiser.** `u * t_v` has order `1` for every unit `u`
  (`ord_mul`, `ord_coe_unit`), but `d (u * t_v)` picks up the Leibniz term
  `t_v • d u`. If `u` is a constant the term dies (`Derivation.map_algebraMap`),
  so to see a change you need a unit outside the image of `K` — which `ord`
  cannot distinguish from a constant. Try writing the proof for
  `u = algebraMap K F c`: it succeeds only *because* constants have no
  differential.

* **Replace `CharP F p`** in the p-th-power example by `CharZero F` and watch the
  proof die at the step `(p : F) = 0`. In characteristic zero `d (a ^ n) =
  n • a ^ (n - 1) • d a` is not zero for a transcendental `a`, so `d` no longer
  has the p-th powers in its kernel. Differentials detect p-th powers only in
  characteristic `p`, which is why the inseparable counterexample of D.1 lives
  there.

* **`differentialCoeff` is total.** It is an `if`, so it returns `0` for any `ω`
  outside the span; `ordDifferential` then reports `0`, i.e. "no pole, no zero".
  `HasCanonicalDivisor` reads that total function at every place, so the
  generation hypothesis in D.2 is what keeps the divisor from silently losing the
  places where the coefficient is junk. The same pattern as `genus` and `finrank`
  in the hierarchy sheet: a total definition with a junk branch, plus the
  hypothesis that the branch is never taken.

* **One layer down.** The *local* statement — `κ(v)`-dimension of `m_v / m_v²` is
  one, `m_v = (t_v)` — is free from the DVR structure, and `ord_uniformizer` is
  its `F`-side shadow. What is *not* free is the passage from that local
  one-dimensionality to a generator of the global `Ω`. Compare the two `#check`s:
  `IsDiscreteValuationRing.exists_irreducible` (Zone A, no curve hypotheses) and
  `DCoordGenerates` (Zone C, a hypothesis on every rung). -/

/- ## Zone Q — question log

Oldest first. Each entry: question, one-line answer, and a pointer to the zone
that was edited.

* (2026-10-23) *Worksheet created.*
* (2026-10-23) **Q1.** A place has a uniformiser `t_v`; why doesn't that give a
  differential, and why is `kaehler_free_rank_one` an axiom? — It does give an
  *element* `d t_v` (`dCoord`) and an order, but not a basis: the rank of `Ω` is
  a property of the extension (D.1), generation at a place is a separate
  hypothesis (D.2), and finite support of the order function is a theorem over a
  perfect field (D.3). Zone A vs Zone C.
* (2026-10-23) **Q2.** Is the axiom "there exists a nonzero differential"? — No:
  it is "`Ω` is a line", which is strictly stronger. Existence is *derived*
  (`instNontrivialKaehler`), and it would not give the coefficient, the order, or
  the independence of the choice of `t_v`. See D.1.
* (2026-10-23) **Q3.** The place knows `f` only as `u · t_v^ord`; doesn't
  `ord` plus the uniformiser determine `d f`? — No: `d` is a derivation, not a
  function of the order. `d (u · t_v)` carries `t_v · d u`, which `ord` cannot
  see; the two examples in Zone C are that statement, one for `ord` and one for
  `d`.
* (2026-10-23) **Q4.** Why is `differentialCoeff` total (with a `0` branch)
  rather than requiring `DCoordGenerates`? — So that `ordDifferential` and
  `HasCanonicalDivisor` are definitions rather than conditional statements; the
  hypothesis is then a class instance that the honest lemmas require. The junk
  branch is the price, and Zone E's poke shows how it is neutralised. -/

end Play
