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
            Defs/KaehlerTranscendental.lean, P1/DXCoeff.lean,
            IsCurveOver/SeparatingTranscendental.lean,
            Canonical/HasCanonicalDivisor.lean,
            Defs/RiemannRochRows.lean
  Pin       Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean (the `Place`
            structure and `ord`),
            Definitions/Def_ModularCurve_CanonicalDivisor.lean,
            Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean,
            Definitions/Def_AlgebraicCurve_IsCurveOver.lean,
            P2M/Sol/S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean,
            P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean,
            P2M/Sol/S_KaehlerDifferential_span_D_eq_top_of_transcendental.lean,
            all at aa2d8b3
  Check     cd lean && lake env lean play/PlacesAndDifferentials.lean   (~9 s, oleans warm)
  Status    open
  Date      2026-10-23
  Intro     A place gives an order `ord_v` and a uniformiser `t_v`; a differential
            lives in the Kähler module `Ω[F⁄K]`, which is an object of the whole
            field extension and mentions no place — literally so: `Ω[F⁄K]` is
            `I ⧸ I²` for `I` the ideal of the diagonal of `F ⊗[K] F`, so the
            construction sees nothing but the ring map `K → F`. This sheet
            separates the two, exhibits each gate the port puts between them
            (`dCoord`,
            `DCoordGenerates`, `differentialCoeff`, `ordDifferential`,
            `HasCanonicalDivisor`), shows that the same order admits different
            differentials, and lands on the axiom that no amount of place data
            can supply: `kaehler_free_rank_one`.

  Zone list
    A  the place — unconditional: valuation ring, uniformiser, order, residue
    B  the differential — global: Ω = `I ⧸ I²` of the diagonal, `D`, Leibniz, `d x ≠ 0`
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

  Import cost. One import, `ResidueTheorem/RRAssembly` (the cone of the hierarchy
  sheet), which carries `Defs/Place`, `Defs/CanonicalDivisor`, `Defs/LocalResidue`,
  `P1/DXCoeff` and `Canonical/HasCanonicalDivisor`; ~9 s warm. No tree rebuild:
  `play/` is outside every `lean_lib` glob.
-/
import FLTForHuman.AlgebraicCurve.ResidueTheorem.RRAssembly

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

-- `ᵐ⁰` is *scoped* notation (`scoped notation M "ᵐ⁰" => WithZero (Multiplicative M)`),
-- so `ℤᵐ⁰` needs the scope opened; the port's `Place` opens `WithZero` too, which is
-- why its sources print the value group as `ℤᵐ⁰` rather than the expansion.
open scoped WithZero

-- `⊗` and `⊗ₜ` are scoped notation for `TensorProduct`; Zone B's construction of
-- `Ω` is a tensor product, so the scope is opened here rather than at each use.
open scoped TensorProduct

-- `R[X]` is scoped notation for `Polynomial R`; the model of `Ω` in Zone B is the
-- polynomial ring, `Ω[K[X]⁄K] ≅ K[X]`, so the scope is opened here too.
open scoped Polynomial

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
#check @AlgebraicCurve.Place.uniformizerSubring
#check @AlgebraicCurve.Place.ord_uniformizer
#check @AlgebraicCurve.Place.uniformizer_ne_zero

/- **What "uniformiser" means, and the rewrite that says it.** In a DVR an element is
irreducible exactly when it generates the maximal ideal, and mathlib states the two
spellings as one `iff`. Everything `ord` rests on is that `rw`: the `Irreducible` that
`uniformizerSubring` *is* becomes the ideal equality `m_v = (t_v)` that the valuation
lemmas *consume* and never undo. -/
example (v : AlgebraicCurve.Place K F) (ϖ : v.toValuationSubring) :
    Irreducible ϖ ↔ IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {ϖ} :=
  IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ

example (v : AlgebraicCurve.Place K F) : v.ord v.uniformizer = 1 :=
  v.ord_uniformizer

/-- Right-to-left on the chosen irreducible: `m_v = (t_v)`. This is the direction the
valuation theorems want — `intValuation_singleton` takes an ideal equality, and neither
it nor `ord` ever sees `Irreducible`. -/
example (v : AlgebraicCurve.Place K F) :
    IsLocalRing.maximalIdeal v.toValuationSubring = Ideal.span {v.uniformizerSubring} := by
  rw [← IsDiscreteValuationRing.irreducible_iff_uniformizer]
  exact (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

/- Where the same `iff` works *inside* mathlib: `exists_irreducible` is `simp_rw` on it
followed by principality, and that is the proof term the `Classical.choose` above
consumes. -/
#check @IsDiscreteValuationRing.irreducible_iff_uniformizer
#check @IsDiscreteValuationRing.exists_irreducible
#check @Irreducible.maximalIdeal_eq

/- The uniformiser's `F`-side order is the `ord = 1` of `ord_uniformizer`; the
subring-side spelling lives with the canonical-divisor layer. -/
#check @AlgebraicCurve.Place.ord_uniformizerSubring

/- **`ord` is `log` of the adic valuation** — one bookkeeping layer, and nothing in
this sheet turns on anything beyond it. `v.adicValuation : F → ℤᵐ⁰` is the `v`-adic
valuation, its value group written multiplicatively (`ℤᵐ⁰ = WithZero (Multiplicative ℤ)`),
so that a value of `n` is `exp n` and `1 = exp 0` is "unit"; `WithZero.log` is the inverse
of `exp` *off* `0` (junk value `log 0 = 0`); and

  `v.ord f = -(WithZero.log (v.adicValuation f))`.

Two conventions are packed into that line, and neither carries content beyond notation.
Mathlib's valuation puts the ring *below* `1` (`intValuation_le_one`), so the uniformiser
has value `exp (-1)`, not `exp 1`. And the outer minus turns a *small* valuation into a
**vanishing order**: `ord > 0` is a zero, `ord < 0` a pole, which is the divisor
convention `(f) = ∑_v ord_v(f) · v`. Everything else is `log` being additive. -/
#check @WithZero.exp
#check @WithZero.log
#check @WithZero.log_mul
#check @WithZero.logEquiv
#check @IsDedekindDomain.HeightOneSpectrum.intValuation_le_one
#check @IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem

/- The rest of the API, one line each. All of it is `log` additive, `log ∘ exp = id`, and
the junk `log 0 = 0`; Zone C uses `ord_mul`, `ord_zpow` and `ord_uniformizer`, the rest is
here so the names are findable: -/
#check @AlgebraicCurve.Place.ord_mul          -- additive on products
#check @AlgebraicCurve.Place.ord_inv
#check @AlgebraicCurve.Place.ord_zpow
#check @AlgebraicCurve.Place.ord_algebraMap   -- constants are units
#check @AlgebraicCurve.Place.mem_iff_ord_nonneg   -- regular at `v` ⟺ `ord ≥ 0`
#check @AlgebraicCurve.Place.ord_zero
#check @AlgebraicCurve.Place.min_ord_le_ord_add

/- **What a place knows about an element**, and the one fact Zone C leans on: `f` is a
unit times `t_v ^ ord f`, and the unit is invisible to `ord` (`ord_coe_unit`). That is
exactly what the differential will fail to respect. -/
#check @AlgebraicCurve.Place.exists_unit_mul_zpow
#check @AlgebraicCurve.Place.ord_coe_unit

/- The residue data is local too, and *here* the place is already not enough: a
DVR does not bound the degree of `κ(v)` over `K`. Finiteness is a class, one of
`IsCurveOver`'s three axioms, and the port keeps it as a hypothesis rather than
deriving it from the place. -/
#check @AlgebraicCurve.Place.ResidueField
#check @AlgebraicCurve.Place.deg
#check @AlgebraicCurve.Place.FiniteResidue

/- ## Zone B — the differential, globally

`Ω[F⁄K]` is notation for `KaehlerDifferential K F`, the module of Kähler
differentials of the *algebra* `F/K`; `D` is the universal derivation into it. Both
are objects of the extension; neither mentions a place. The notation is definitional,
so the equation below is `rfl` and every later statement about `Ω` is literally a
statement about the declaration: -/
example : Ω[F⁄K] = KaehlerDifferential K F := rfl

#check @KaehlerDifferential
#check @KaehlerDifferential.D

/- **What the definition actually is: the ideal of the diagonal.**

The `#check` above is silent about the construction, and the construction is the
answer to "why does a differential exist at all". `S ⊗[R] S` is the *coproduct* of
`S` with itself in `R`-algebras: it carries two commuting copies of `S`, the left one
`s ↦ s ⊗ₜ 1` and the right one `s ↦ 1 ⊗ₜ s` (`includeLeft`, `includeRight`), and
`lmul'` (spelled `Algebra.TensorProduct.lmul'`: a namespace one level below the one
`open KaehlerDifferential` reaches, so the short name is unknown) is the unique
`R`-algebra map out of it that composes with *either* copy to the identity. Hence

  `I := KaehlerDifferential.ideal R S = ker lmul'`   (`RingHom.ker`),

the ideal saying *the two copies agree*: the ideal of the diagonal, the ring-level
form of "vanishes on `Δ`". Mathlib proves it is generated by the differences of the
copies, which is the algebraic content of the name: -/

#print KaehlerDifferential.ideal

#check @Algebra.TensorProduct.lmul'
#check @Algebra.TensorProduct.lmul'_apply_tmul
#check @Algebra.TensorProduct.includeLeft
#check @Algebra.TensorProduct.includeRight
#check @RingHom.ker
#check @RingHom.mem_ker
#check @KaehlerDifferential.ideal
#check @KaehlerDifferential.one_smul_sub_smul_one_mem_ideal
#check @KaehlerDifferential.span_range_eq_ideal

/-- `Ω` *is* the cotangent module of the diagonal ideal — no lemma stands between
the two declarations, so `rfl` suffices. This is the definition the rest of the
sheet's `Ω` is: `I ⧸ I²`. -/
example : Ω[F⁄K] = (KaehlerDifferential.ideal K F).Cotangent := rfl

/-- The two copies of `F` inside `F ⊗[K] F`, and the map that sets them equal. -/
example (a b : F) : Algebra.TensorProduct.lmul' K (a ⊗ₜ[K] b) = a * b :=
  Algebra.TensorProduct.lmul'_apply_tmul a b

/-- The generator statement: `I` is the ideal generated by the differences
`1 ⊗ₜ f - f ⊗ₜ 1`. This is what makes the classical computation `I = (x - y)` in
`R[x] ⊗ R[x] ≅ R[x, y]` a theorem rather than a picture. -/
example :
    KaehlerDifferential.ideal K F
      = Ideal.span (Set.range fun s : F => (1 : F) ⊗ₜ[K] s - s ⊗ₜ[K] (1 : F)) :=
  (KaehlerDifferential.span_range_eq_ideal K F).symm

/- **Where the multiplication comes from.** Not from this sheet: typeclass search,
from `[Field K] [Field F] [Algebra K F]`, in three layers — `LinearMap.mul K F` is
`K`-bilinear *because* `F` is a `K`-algebra, `TensorProduct.map₂` tensors the two
bilinear maps and the universal property of `⊗` linearises the result, and
`Algebra.TensorProduct.instMul`/`instCommRing` package it with unit `1 ⊗ₜ 1`. The
element rule `(a ⊗ₜ b) * (c ⊗ₜ d) = (a * c) ⊗ₜ (b * d)` is then `rfl` (`tmul_mul_tmul`):
the multiplication is *defined* as "multiply in each factor", which is why the sheet
inherits the ring structure instead of building it. With only `[Module K F]` there
would be no `*` at all. A bonus from the same instances: `F ⊗[K] F` is an `F`-algebra
through the left copy (`algebraMap f = f ⊗ₜ 1`), which is where `Ω`'s `F`-module
structure comes from. -/

#check @TensorProduct.map₂
#check @LinearMap.mul
#check @Algebra.TensorProduct.mul
#check @Algebra.TensorProduct.instMul
#check @Algebra.TensorProduct.instSemiring
#check @Algebra.TensorProduct.instCommRing
#check @Algebra.TensorProduct.leftAlgebra
#check @Algebra.TensorProduct.algebraMap_apply

-- The instances the sheet relies on, printed as what they are: instance search.
#synth CommRing (F ⊗[K] F)
#synth Algebra F (F ⊗[K] F)
#synth IsScalarTower K F (F ⊗[K] F)

/-- The ring structure is instance search (`#synth` above), and the left copy is what
makes `Ω` an `F`-module: `algebraMap f = f ⊗ₜ 1`. -/
example (f : F) : algebraMap F (F ⊗[K] F) f = f ⊗ₜ[K] (1 : F) := by
  rw [Algebra.TensorProduct.algebraMap_apply]
  simp

/- **Why not just `S`, then? Because `⊗ₜ` is not symmetric.**

Only scalars cross slots (`r • s ⊗ₜ t = s ⊗ₜ r • t` for `r : K`), and multiplication
**recombines** the slots without ever **equating** them:
`(s ⊗ₜ 1) * (1 ⊗ₜ t) = s ⊗ₜ t = (1 ⊗ₜ t) * (s ⊗ₜ 1)` is a product of two elements,
not an equality of `s ⊗ₜ 1` with `1 ⊗ₜ s`. So `S ⊗[K] S` is strictly bigger than `S`:
`lmul'` is onto with kernel `I`, and `s ⊗ₜ 1 - 1 ⊗ₜ s` is generally a nonzero element of
`I` — the obstruction to sliding `s` across the tensor symbol, and the very element
whose class in `I ⧸ I²` is `D s`. Impose those two copies equal for all `s` and
`I = 0`, `Ω = 0`: an unramified extension with no differentials. `Ω` is the
*linearisation* of the collapse `lmul'`, and `S ⊗[K] S` — the coproduct,
`Spec S ×_{Spec K} Spec S`, generally of higher dimension than `Spec S` — is the
universal way to have two copies that differ. -/

/-- Recombination, not identification: a product of the two copies is an elementary
tensor, but the two copies themselves stay distinct. -/
example (s t : F) :
    (s ⊗ₜ[K] (1 : F)) * ((1 : F) ⊗ₜ[K] t) = s ⊗ₜ[K] t := by
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The two copies are *not* equal, and the proof is that otherwise `d x` would
vanish: `D_ne_zero_of_transcendental` supplies the nonvanishing, and the equality
`1 ⊗ₜ x = x ⊗ₜ 1` would put its defining class at `0`. (Why a transcendental has a
nonzero differential at all is the block after the p-th-power example below, where
`d x ≠ 0` is derived rather than quoted.) -/
example {x : F} (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] :
    (1 : F) ⊗ₜ[K] x ≠ x ⊗ₜ[K] (1 : F) := by
  intro h
  have hcov : (1 : F) ⊗ₜ[K] x - x ⊗ₜ[K] (1 : F) = 0 := by rw [h, sub_self]
  have hsub : (⟨1 ⊗ₜ[K] x - x ⊗ₜ[K] (1 : F),
      KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) x⟩ :
      KaehlerDifferential.ideal K F) = 0 := by
    rw [Subtype.ext_iff]
    simpa using hcov
  refine KaehlerDifferential.D_ne_zero_of_transcendental K x hx ?_
  rw [KaehlerDifferential.D_apply, hsub]
  exact map_zero _

/-- And yet they are equal after the collapse: `lmul'` kills the difference, which is
why `(F ⊗[K] F) ⧸ I ≅ F` is a statement about rings and not about sets. -/
example (s : F) :
    Algebra.TensorProduct.lmul' K ((1 : F) ⊗ₜ[K] s) =
      Algebra.TensorProduct.lmul' K (s ⊗ₜ[K] (1 : F)) := by
  rw [Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    one_mul, mul_one]

/- **Why the kernel is an *ideal*, not just a submodule.** `F ⊗[K] F` is not only a
`K`-vector space but a commutative **ring** — the coproduct of `F` with itself in
`K`-algebras — and `lmul'` is an `AlgHom`, hence multiplicative. That is what upgrades
a kernel: a ring hom's kernel is closed under multiplication by any element of the
*domain*, not only by the scalars from `K` —

  `x ∈ I  ⇒  lmul' (y * x) = lmul' y * lmul' x = lmul' y * 0 = 0`,

i.e. `y * x ∈ I` for every `y : F ⊗[K] F` (`Ideal.mul_mem_left`). And `Ideal R` *is*
`Submodule R R` definitionally, so an ideal is not a new kind of object: it is a
submodule whose extra closure comes free from multiplicativity. That is why
`RingHom.ker` can return an `Ideal` while a merely `K`-linear map's kernel cannot.
Payoffs: `I²` exists (so `I ⧸ I²` does), and `(F ⊗[K] F) ⧸ I ≅ F` is a ring, which is
what `Ω` is a module over. -/

-- The two facts that make `F ⊗[K] F` a ring here, and that `lmul'` respects: how
-- elementary tensors multiply, and what its unit is.
#check @Algebra.TensorProduct.tmul_mul_tmul
#check @Algebra.TensorProduct.one_def

#check @AlgHom.toRingHom
#check @RingHom.ker
#check @Ideal
#check @Ideal.mul_mem_left
#check @Ideal.Quotient.mk
#check @Ideal.mk_ker
#check @RingHom.quotientKerEquivOfRightInverse
#check @RingHom.quotientKerEquivOfSurjective

/-- `Ideal R` *is* `Submodule R R`, so `I` is a submodule of `F ⊗[K] F` over itself
— not over `K`. "Ideal" is the submodule that is also closed under multiplication. -/
example : Submodule (F ⊗[K] F) (F ⊗[K] F) := KaehlerDifferential.ideal K F

/-- The extra closure, at an arbitrary ring element — not at a `K`-scalar. The
multiplicativity that supplies it is `map_mul _ _ _`, and `Ideal.mk_ker` is the same
closure seen from the quotient side. -/
example (x : F ⊗[K] F) (y : KaehlerDifferential.ideal K F) :
    x * (y : F ⊗[K] F) ∈ KaehlerDifferential.ideal K F :=
  Ideal.mul_mem_left _ x y.2

/-- The payoff: the first isomorphism theorem makes the quotient a *ring*, isomorphic
to `F`. The ideal is written as `RingHom.ker lmul'` — which is what
`KaehlerDifferential.ideal` *is*, by definition — because that is the shape the theorem
consumes; `lmul'` is onto by `fun x => ⟨x ⊗ₜ 1, by simp⟩`. That ring is what `Ω` is a
module over, and it is why `I ⧸ I²` is an `F`-vector space and not only a `K`-one. -/
example :
    (F ⊗[K] F) ⧸ RingHom.ker (Algebra.TensorProduct.lmul' (R := K) (S := F)) ≃+* F :=
  RingHom.quotientKerEquivOfSurjective (fun x => ⟨x ⊗ₜ[K] (1 : F), by simp⟩)

/- **Membership: `0`, not `1`.** `lmul'` is *multiplication*, so `x ∈ I` means "the
product of the two copies of `x` is `0`". At an elementary tensor that reads
`a * b = 0`; the tempting `a * b = 1` is the opposite case — the product is the
*unit*, so that tensor is a unit of `F ⊗[K] F`. The examples below spell this out,
and the last one is why the interesting members of `I` are *relations* between
products — sums, not products. -/

/-- Membership at the level of one elementary tensor: `lmul'` is *multiplication*, so
`a ⊗ₜ b` is in `I` when the product is `0` — not when it is `1`. -/
example (a b : F) : a ⊗ₜ[K] b ∈ KaehlerDifferential.ideal K F ↔ a * b = 0 := by
  simp [KaehlerDifferential.ideal, RingHom.mem_ker,
    Algebra.TensorProduct.lmul'_apply_tmul]

/-- The `a * b = 1` case is the opposite extreme — that tensor is a *unit* of
`F ⊗[K] F`, since `(a ⊗ₜ b) * (a⁻¹ ⊗ₜ b⁻¹) = 1` — so it lives as far from `I` as an
element can. -/
example (a b : F) (h : a * b = 1) : a ⊗ₜ[K] b ∉ KaehlerDifferential.ideal K F := by
  simp [KaehlerDifferential.ideal, RingHom.mem_ker,
    Algebra.TensorProduct.lmul'_apply_tmul, h]

/-- So the *elementary* members of `I` are the trivial ones — `a * b = 0` in the
*field* `F`, hence `a = 0` or `b = 0` — while the elements that matter are sums:
each summand below is outside `I` and their difference is in it. That is the shape
the quotient inherits: `Ω = I ⧸ I²` is spanned by the classes `d f`. -/
example {f : F} (hf : f ≠ 0) :
    (1 : F) ⊗ₜ[K] f ∉ KaehlerDifferential.ideal K F ∧
      f ⊗ₜ[K] (1 : F) ∉ KaehlerDifferential.ideal K F ∧
      (1 : F) ⊗ₜ[K] f - f ⊗ₜ[K] (1 : F) ∈ KaehlerDifferential.ideal K F := by
  refine ⟨?_, ?_, ?_⟩
  · simp [KaehlerDifferential.ideal, RingHom.mem_ker, hf]
  · simp [KaehlerDifferential.ideal, RingHom.mem_ker, hf]
  · exact KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) f

/- **Why `I ⧸ I²` and not `I`.** Three things happen in the quotient, and each is
something the rest of the sheet needs.

* It is the *first-order* piece. `I²` is second order, so `I ⧸ I²` keeps only the
  derivative of the agreement: `(S ⊗ S) ⧸ I²` is the first infinitesimal
  neighbourhood of the diagonal — a square-zero extension of `S` by `Ω`, and the
  universal one.
* Products of two elements of `I` die, and that *is* the Leibniz rule: the
  disagreement between `D (a * b)` and `b • D a + a • D b` turns out to be the
  product `D a · D b` — a square, hence `0` in `I ⧸ I²`. The block after the
  `D_apply` example below computes this rather than asserting it, and it is the
  only place where `I²` does any work.
* `I ⧸ I²` is a module over `(S ⊗ S) ⧸ I ≅ S`, so a differential is again a
  *function*, not merely an `R`-vector — which is what lets `finrank_F Ω` below be
  the number it is, and what `kaehler_free_rank_one` speaks about.

Geometrically, `Spec (S ⊗[R] S) = Spec S ×_{Spec R} Spec S`, `lmul'` is the diagonal
`Δ`, `I` is the ideal of `Δ`, and `Ω` is its conormal sheaf — the cotangent sheaf,
dual to the tangent bundle. The affine model is `S = R[x]`: then `S ⊗ S ≅ R[x, y]`
with the two copies `x` and `y`, `lmul'` is "`y ↦ x`", `I = (x - y)`, and `Ω` is free
of rank one on `d x = [1 ⊗ₜ x - x ⊗ₜ 1]`. Note that `I` itself would be the wrong
answer: `(x - y)` also contains `x² - y²`, whereas `Ω` keeps only the linear part —
`d x`, and not every relation vanishing on the diagonal. -/

#check @KaehlerDifferential.D_apply
#check @Ideal.Cotangent
#check @Ideal.toCotangent
#check @Ideal.map_toCotangent_ker
#check @Ideal.toCotangent_eq
#check @Ideal.Cotangent.smul_eq_zero_of_mem

/-- The quotient map `I → Ω` is a quotient by `I ^ 2` *literally*: its kernel, mapped
back into `S ⊗[R] S`, is `I ^ 2`. So the "mod squares" is not a convention imposed
afterwards — it is the definition, and `toCotangent_eq` is the same statement at the
level of elements. -/
example :
    (LinearMap.ker (KaehlerDifferential.ideal K F).toCotangent).map
        (KaehlerDifferential.ideal K F).subtype
      = (KaehlerDifferential.ideal K F) ^ 2 :=
  Ideal.map_toCotangent_ker _

/-- **`D` is the difference of the two copies.** The universal derivation sends `f`
to the class of `1 ⊗ₜ f - f ⊗ₜ 1`: the two ring maps `includeLeft`, `includeRight` into
`(S ⊗ S) ⧸ I²` both split the projection to `S`, and their difference is a
derivation. Zone C's `d t_v` is this class for `f = t_v` — the differential of the
chosen uniformiser is the linearised disagreement of its two copies, and nothing in
that sentence, or in `Ω`, names a place. -/
example (f : F) :
    KaehlerDifferential.D K F f
      = (KaehlerDifferential.ideal K F).toCotangent
          ⟨1 ⊗ₜ[K] f - f ⊗ₜ[K] 1,
            KaehlerDifferential.one_smul_sub_smul_one_mem_ideal (R := K) f⟩ :=
  KaehlerDifferential.D_apply K F f

/- **Leibniz, computed.** The `I ⧸ I²` bullet above is the whole of the Leibniz rule,
and it is worth doing once by hand — in the ring `F ⊗[K] F`, with no derivation in
sight. For `a : F` write `da := 1 ⊗ₜ a - a ⊗ₜ 1` (in `I`, class `D a`); the element
whose class is `D (a * b)` then expands by the multiplication rule to

  `d (a * b) = da * (b ⊗ₜ 1) + (1 ⊗ₜ a) * db`.                            (*)

Nothing is quotiented yet: `(*)` is an identity of the commutative ring, and the two
cross terms `b ⊗ₜ a` cancel — that cancellation is the entire algebra in the product
rule. (Mathlib's `D a` is `1 ⊗ₜ a - a ⊗ₜ 1`; `a ⊗ₜ 1 - 1 ⊗ₜ a` would work as well.)

Now pass to `I ⧸ I²`. The coefficient sits on the left copy in the first summand and
on the right copy in the second, but the two copies differ by `db ∈ I`, and a factor in
`I` times a difference in `I` is in `I · I = I²`:

  `da * (b ⊗ₜ 1) = da * (1 ⊗ₜ b)` and `(1 ⊗ₜ a) * db = (a ⊗ₜ 1) * db`   mod `I²`,

with corrections `∓ da * db`. **The defect is the product `da · db`, and `I²` is exactly
what kills it**; reading every coefficient through the left copy leaves
`D (a * b) = b • D a + a • D b`. So "it does not matter which copy `a` and `b` are" is
precisely those two congruences — switching copies costs a term of `I²` — and it is why
`Ω` is `I ⧸ I²` and not `I`: in `I` the defect `da · db` survives (model: `(y - x)²`).

Mathlib proves the same thing in the `leibniz'` field of `def KaehlerDifferential.D`
([`Kaehler/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/v4.34.0/Mathlib/RingTheory/Kaehler/Basic.lean#L201-L213)):
after `Ideal.toCotangent_eq` and `pow_two`, the mathematics is the single line

  `convert! Submodule.mul_mem_mul (one_smul_sub_smul_one_mem_ideal R a :) (one_smul_sub_smul_one_mem_ideal R b :)`

— "the defect is `da * db ∈ I · I`" — and `convert!`/`ring_nf` supply the bookkeeping of
`(*)`. The examples below are that line, in order: `(*)`, the defect in `I²`, the two
copies agreeing in `Ω`, and Leibniz for `D`. -/
#check @Ideal.mul_mem_mul
#check @IsScalarTower.algebraMap_smul

/-- `(*)`: the elementary identity, in the ring, before any quotient. Distributing and
cancelling the two cross terms is the whole computation. -/
example (a b : F) :
    (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (b ⊗ₜ[K] (1 : F))
        + ((1 : F) ⊗ₜ[K] a) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F))
      = 1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F) := by
  rw [sub_mul, mul_sub]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  abel

/-- The second-order defect `da * db` lies in `I²`: `Ideal.mul_mem_mul` applied to the
two classes. This one membership *is* the product rule; what remains is linearity. -/
example (a b : F) :
    (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F))
      ∈ (ideal K F) ^ 2 := by
  rw [pow_two]
  exact Ideal.mul_mem_mul (one_smul_sub_smul_one_mem_ideal (R := K) a)
    (one_smul_sub_smul_one_mem_ideal (R := K) b)

/-- The two copies of a scalar agree in `Ω`. This is "`includeLeft` or `includeRight`,
it makes no difference", as a statement about `I ⧸ I²`, and it is what lets the
quotient ring `(F ⊗[K] F) ⧸ I ≅ F` act on `Ω`: the ambiguity `(c ⊗ₜ 1 - 1 ⊗ₜ c)` is an
element of `I`, so acting with it lands in `I · I` and dies in the quotient. -/
example (c : F) (x : ideal K F) :
    (ideal K F).toCotangent ((c ⊗ₜ[K] (1 : F)) • x)
      = (ideal K F).toCotangent (((1 : F) ⊗ₜ[K] c) • x) := by
  rw [Ideal.toCotangent_eq, pow_two]
  simp only [Submodule.coe_smul, smul_eq_mul]
  rw [← sub_mul]
  exact Ideal.mul_mem_mul (by simp) x.2

/-- **Leibniz for `D`, computed**: `(*)` in the ring, then the defect `da * db ∈ I²`,
then the linearity of `toCotangent`. No `Derivation.leibniz` in the proof — this is
where the sheet's Leibniz rule comes from, and Zone C uses it as such. -/
example (a b : F) :
    KaehlerDifferential.D K F (a * b)
      = b • KaehlerDifferential.D K F a + a • KaehlerDifferential.D K F b := by
  -- the `F`-scalar acts through the left copy of `F` in `F ⊗[K] F`
  have hsmul : ∀ (c : F) (ω : (ideal K F).Cotangent),
      c • ω = (c ⊗ₜ[K] (1 : F)) • ω := by
    intro c ω
    rw [← IsScalarTower.algebraMap_smul (A := F ⊗[K] F),
      Algebra.TensorProduct.algebraMap_apply]
    simp
  -- `Ω[F⁄K]` is a `def` alias of `I.Cotangent`; `change` puts both sides at the same
  -- type, so that the linearity of `toCotangent` applies syntactically
  change (ideal K F).toCotangent
      ⟨1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F), _⟩
    = b • (ideal K F).toCotangent ⟨1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F), _⟩
      + a • (ideal K F).toCotangent ⟨1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F), _⟩
  -- pull the scalars and the sum inside `I`, then compare in the ring
  rw [hsmul b, hsmul a, ← map_smul, ← map_smul, ← map_add, Ideal.toCotangent_eq,
    pow_two]
  simp only [Submodule.coe_add, Submodule.coe_smul, smul_eq_mul]
  -- `(*)`, which is the only place the ring structure is used
  have hd : 1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F)
      = (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (b ⊗ₜ[K] (1 : F))
        + ((1 : F) ⊗ₜ[K] a) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)) := by
    rw [sub_mul, mul_sub]
    simp only [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    abel
  -- the terms carrying `b ⊗ₜ 1` cancel by commutativity, leaving `((1 ⊗ₜ a) - (a ⊗ₜ 1)) * db`
  have hkey : (1 ⊗ₜ[K] (a * b) - (a * b) ⊗ₜ[K] (1 : F))
      - ((b ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F))
        + (a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)))
      = (1 ⊗ₜ[K] a - a ⊗ₜ[K] (1 : F)) * (1 ⊗ₜ[K] b - b ⊗ₜ[K] (1 : F)) := by
    rw [hd]
    ring
  rw [hkey]
  exact Ideal.mul_mem_mul (one_smul_sub_smul_one_mem_ideal (R := K) a)
    (one_smul_sub_smul_one_mem_ideal (R := K) b)

/- **The ideal is forced, not chosen.** `Ω` corepresents derivations: `S`-linear maps
out of it are exactly `R`-derivations, and the inverse equivalence is built by sending
`a ⊗ b` to `a • D b`. That map kills `I²`, and the reason is the product rule of the
block above: on a product `x * y` of two elements of `I` it returns
`lmul' x • (…) + lmul' y • (…) = 0`, because `lmul'` kills `I`. So it factors through
`I → I ⧸ I²` — and vanishing on `I²` rather than on `I` is what leaves `Ω` nonzero,
since `I² ⊆ I`. Any other ideal whose square-zero quotient classified derivations would
give the same functor, hence the same module up to isomorphism. That is the precise
sense in which `ker lmul'` is the right kernel and not an arbitrary one. -/
#check @KaehlerDifferential.linearMapEquivDerivation
#check @Derivation.liftKaehlerDifferential
#check @Derivation.tensorProductTo
#check @KaehlerDifferential.tensorProductTo_surjective

example (M : Type*) [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]
    (D : Derivation K F M) (f : F) :
    D.liftKaehlerDifferential (KaehlerDifferential.D K F f) = D f :=
  Derivation.liftKaehlerDifferential_comp_D D f

/- And the degenerate case, which shows what `Ω` is *measuring*: if `R → S` is
surjective there is no relative dimension left and every derivation dies. `Ω` is a
statement about the *extension*, never about `S` alone — Zone D.1's whole point. -/
#check @KaehlerDifferential.subsingleton_of_surjective

/- **The packaged form.** `D` is a `Derivation`: a `K`-linear map together with two
equations. The map is the difference of the two copies fed into `toCotangent`, and both
equations are computations already done — `map_one_eq_zero'` is `D 1 = 0`, which
`K`-linearity turns into `D (algebraMap c) = 0` (`Derivation.map_algebraMap`), and
`leibniz'` is the identity of the block after `D_apply`, which is what
`Derivation.leibniz` reads off. So nothing is added by the packaging except the right to
stop looking; what it costs is that the `leibniz'` field of `KaehlerDifferential.D` is
proved by `convert!` and `ring_nf`, which is why the sheet computed it. `leibniz_pow`
is `leibniz'` iterated, and it is the one place where the exponent matters: in
characteristic `p` the coefficient `p` kills the sum. -/
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

/- **Why a transcendental differential cannot vanish.** `D x ≠ 0` for transcendental `x`
(`D_ne_zero_of_transcendental`) is what Zone D.2's route to `DCoordGenerates` runs on,
and it is easy to misread as "`Ω` is large". It says that **`x` is a coordinate, so its
differential is `1`**: on a polynomial ring `d` *is* the formal derivative `P ↦ P'`, so
`Ω[K[X]⁄K]` is `K[X]` itself by `d X ↦ 1`; and no change of ring alters the differential,
only its coefficients — provided the change is *separable*, the algebraic form of
"infinitesimally trivial". An inseparable extension does alter it, and can kill a
differential that was already there (last paragraph).

Two devices make that formal, each one line.

**Universality.** `Ω` corepresents derivations, so `D x` is the universal witness: every
`K`-derivation `D'` out of `F` has `D' x = D'.liftKaehlerDifferential (D x)`
(`Derivation.liftKaehlerDifferential_comp_D`). Hence `D x = 0` iff *every* derivation kills
`x`, and `D x ≠ 0` needs just one derivation that does not — in the model, `X' = 1 ≠ 0`.

**Base change.** For an `Algebra.FormallyEtale` extension `S → T` (a localisation, or a
separable algebraic extension of fields) differentials only base-change:
`Ω[T⁄R] ≅ T ⊗_S Ω[S⁄R]` (`tensorKaehlerEquivOfFormallyEtale`), and a generator goes to a
generator (`_symm_D_algebraMap`; the first transport is done end to end below). So the
argument is four rings and two transports,

  `K[X]` —localise→ `K(X)` —rename→ `K(x)` —separable→ `F`,

with `d X` the generator at every stage. The renaming is the only use of
`Transcendental K x`: `RatFunc.algEquivOfTranscendental` is `K(X) ≅ K(x)`, `X ↦ x` — "not
a root of any polynomial" *is* "usable as a coordinate". At the far end
`Ω[F⁄K] ≅ F ⊗_{K(x)} Ω[K(x)⁄K] ≅ F`, so **`Ω[F⁄K]` is free of rank one on `d x`, hence
`d x ≠ 0` and `span {d x} = ⊤`.**

**What the proof writes down is that basis, not the intuition.** The port's `exists_basis`
(`Defs/KaehlerTranscendental.lean`, from the pin's
[`S_KaehlerDifferential_D_ne_zero_of_transcendental.lean`](https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_KaehlerDifferential_D_ne_zero_of_transcendental.lean))
produces `b : Basis Unit F Ω[F⁄K]` with `b () = D x` by transporting the model's
*singleton* basis (FLT's `b₀`: `Basis.singleton` pulled back along `polynomialEquiv`)
through `Module.Basis.baseChange` and `Module.Basis.map` along the two formal-étale
isomorphisms. `D x ≠ 0` is then `b.ne_zero ()` and `span = ⊤` is `b.span_eq`; the
`letI`/`haveI` wall is the tower `K → K[X] → K(X) ≅ K(x) → F`, not mathematics.

**The hypothesis is sharp, and the failure is the p-th-power blindness just above.** In
characteristic `p` let `y` be transcendental and put `x = y ^ p`: then `x` is still
transcendental (`Transcendental.pow`), but `d x = p • y ^ (p - 1) • d y = 0`. So `K(y)` is
an inseparable extension of `K(x)` in which `d y` — not `d x` — is the generator, and the
`IsSeparable` in these statements is exactly its exclusion. -/
#check @KaehlerDifferential.polynomialEquiv
#check @KaehlerDifferential.polynomialEquiv_D
#check @KaehlerDifferential.polynomialEquiv_symm
#check @KaehlerDifferential.polynomial_D_apply
#check @KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale
#check @KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
#check @Algebra.FormallyEtale.of_isLocalization
#check @Algebra.FormallyEtale.of_isSeparable
#check @RatFunc.algEquivOfTranscendental
#check @RatFunc.algEquivOfTranscendental_X
#check @Module.Basis.baseChange
#check @Module.Basis.map
#check @Module.Basis.ne_zero
#check @Module.Basis.span_eq

/-- Universality, the general form: a vanishing differential is invisible to every
derivation. Contrapositively, proving `D x ≠ 0` needs one derivation that does not kill
`x`. -/
example {M : Type*} [AddCommGroup M] [Module K M] [Module F M] [IsScalarTower K F M]
    (D' : Derivation K F M) {x : F} (h : KaehlerDifferential.D K F x = 0) : D' x = 0 := by
  rw [← Derivation.liftKaehlerDifferential_comp_D D' x, h, map_zero]

/-- In the model the witness is the formal derivative, which sees `X`: `X' = 1`. No
basis, no dimension. -/
example : KaehlerDifferential.D K K[X] Polynomial.X ≠ 0 := by
  intro h
  have h1 : Polynomial.derivative' (R := K) Polynomial.X = 0 := by
    rw [← Derivation.liftKaehlerDifferential_comp_D (Polynomial.derivative' (R := K)) Polynomial.X,
      h, map_zero]
  simp at h1

/-- The same statement from the module side: the model *is* `K[X]`, by `d P ↦ P'`, so
`d X` is the image of the unit. -/
example (P : K[X]) :
    KaehlerDifferential.polynomialEquiv K (KaehlerDifferential.D K K[X] P) = P.derivative :=
  KaehlerDifferential.polynomialEquiv_D K P

/-- The chain rule in the model, which is the rank-one statement: every differential of
`K[X]` is its derivative times `d X`. -/
example (P : K[X]) :
    KaehlerDifferential.D K K[X] P
      = P.derivative • KaehlerDifferential.D K K[X] Polynomial.X :=
  KaehlerDifferential.polynomial_D_apply K P

/-- The model's basis and its single vector: FLT's `b₀`, the singleton basis of `K[X]`
pulled back along the derivative. -/
example : ∃ b : Module.Basis Unit K[X] Ω[K[X]⁄K],
    b () = KaehlerDifferential.D K K[X] Polynomial.X :=
  ⟨(Module.Basis.singleton Unit K[X]).map (KaehlerDifferential.polynomialEquiv K).symm,
    by simp [KaehlerDifferential.polynomialEquiv_symm]⟩

/-- A formally étale extension carries a generator to a generator — the only thing the
localisation and the separable extension steps use. -/
example {S T : Type*} [CommRing S] [CommRing T] [Algebra K S] [Algebra K T]
    [Algebra S T] [IsScalarTower K S T] [Algebra.FormallyEtale S T] (s : S) :
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K S T).symm
        (KaehlerDifferential.D K T (algebraMap S T s))
      = (1 : T) ⊗ₜ[S] KaehlerDifferential.D K S s :=
  KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap K S T s

/-- The first transport, done end to end. `d X` in `K(X)` is the base change of the model's
basis vector, and base-changing a basis gives a basis, so it is still nonzero: this is
`b.ne_zero ()`, which is all `D_ne_zero_of_transcendental` amounts to once the tower is
built. -/
example :
    KaehlerDifferential.D K (RatFunc K) (algebraMap K[X] (RatFunc K) Polynomial.X) ≠ 0 := by
  -- localisation is formally étale, so `Ω` only base-changes
  have hfe : Algebra.FormallyEtale K[X] (RatFunc K) :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors K[X])
  -- the transported generator is a vector of the base-changed model basis
  have hb : (1 : RatFunc K) ⊗ₜ[K[X]] KaehlerDifferential.D K K[X] Polynomial.X ≠ 0 := by
    have hne := (((Module.Basis.singleton Unit K[X]).map
      (KaehlerDifferential.polynomialEquiv K).symm).baseChange (RatFunc K)).ne_zero ()
    simpa [KaehlerDifferential.polynomialEquiv_symm] using hne
  -- and `d X` upstairs is the image of that vector
  intro h
  have h1 := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap
    K K[X] (RatFunc K) Polynomial.X
  rw [h, map_zero] at h1
  exact hb h1.symm

/-- Transcendence is used for one thing only: a transcendental names a copy of the
coordinate ring, `K(X) ≅ K(x)` with `X ↦ x`. -/
example {x : F} (hx : Transcendental K x) :
    ((RatFunc.algEquivOfTranscendental x hx) RatFunc.X : F) = x :=
  RatFunc.algEquivOfTranscendental_X x hx

/-- And the hypothesis is sharp: in characteristic `p`, `x = y ^ p` is transcendental with
`d x = 0`, so no separability-free version of the statement can hold. -/
example (p : ℕ) [CharP F p] {y : F} (hy : Transcendental K y) (hp : 0 < p) :
    Transcendental K (y ^ p) ∧ KaehlerDifferential.D K F (y ^ p) = 0 := by
  refine ⟨hy.pow hp, ?_⟩
  rw [Derivation.leibniz_pow]
  have h0 : (p : F) = 0 := CharP.cast_eq_zero F p
  rw [← Nat.cast_smul_eq_nsmul F p, h0, zero_smul]

#check @KaehlerDifferential.D_ne_zero_of_transcendental
#check @KaehlerDifferential.span_D_eq_top_of_transcendental
#check @AlgebraicCurve.kaehlerRankOne_of_transcendental

/- **`D` and the derivative of calculus.** Over `ℝ` or `ℂ` one thinks of `f ↦ f'`. What
`D` gives is `d f`, and `f'` is `d f` read through a *frame*: in a coordinate — `F` with
algebraically independent `x₁,…,xₙ` — `Ω[F⁄K]` is free of rank `n` on `d xᵢ` and

  `D f = ∑ᵢ (∂f/∂xᵢ) • d xᵢ`,

so the classical partial derivative is the *coefficient* of `d xᵢ` (`polynomialEquiv` above
is the case `n = 1`: it sends `d P` to `P'`). Dually
`Derivation K F F ≅ Hom_F(Ω[F⁄K], F)` (`KaehlerDifferential.linearMapEquivDerivation`), so
`∂/∂x` is the dual of `d x`. That is exactly Zone C: `differentialCoeff` is `f'` in the
frame `d t_v`, `ordDifferential` is `ord(f')`, and `gate_ordDifferential_dCoord` is the
identity `d t_v / d t_v = 1`.

In characteristic `0` the dictionary is exact, and both characteristic-`p` phenomena
disappear:

* every extension is separable, so `finrank_F Ω[F⁄K] = trdeg(F/K)`
  (`finrank_kaehler_eq_card_of_separating` applies to *any* transcendence basis): `n`
  variables, `n` differentials — the calculus count. A curve has rank `1`, so over a
  perfect field `kaehler_free_rank_one` is a theorem and D.1's counterexample is a
  characteristic-`p` phenomenon;
* nothing transcendental dies: `x ^ n` with `x` transcendental and `n > 0` keeps a nonzero
  differential (first example below), so the kernel of `D` is exactly the elements
  algebraic over `K`. When `K` is algebraically closed in `F` — `ℂ ⊂ ℂ(x)` — that reads
  "`f' = 0` ⟹ `f` constant", the calculus statement. It is *false* in characteristic `p`,
  where `x ^ p` is transcendental with `d (x ^ p) = 0`.

Two cautions about what `Ω` is not. It is an *algebraic* object, depending only on the ring
structure: for a ring such as `C^∞(ℝ)` it is not the analytic module of `1`-forms, and the
identity `d f = f'(x) d x` needs an algebraic coordinate. And it measures *transcendence*,
not size: over `ℝ`, `Ω[ℂ⁄ℝ] = 0` because `d i = 0` (`2 i • d i = 0`, and `2 i` is a unit —
second example), although `ℂ` is two-dimensional over `ℝ`; while `Ω[ℂ(x)⁄ℂ]` is
one-dimensional although `ℂ(x)` is infinite-dimensional over `ℂ`. -/

/-- In characteristic `0` a transcendental power keeps its differential: the p-th power
collapse of the block above is a characteristic-`p` phenomenon. -/
example (n : ℕ) [CharZero F] {x : F} (hx : Transcendental K x)
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F] (hn : 0 < n) :
    KaehlerDifferential.D K F (x ^ n) ≠ 0 := by
  have hDx : KaehlerDifferential.D K F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental K x hx
  have hn0 : (n : F) ≠ 0 := (Nat.cast_ne_zero (R := F)).mpr hn.ne'
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F n]
  intro h
  rcases smul_eq_zero.mp h with h0 | h0
  · exact hn0 h0
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact pow_ne_zero _ hx.ne_zero h1
  · exact hDx h1

/-- Over `ℝ` no derivation sees `i`: `2 i • d i = 0` and `2 i` is a unit. So `Ω[ℂ⁄ℝ] = 0`
— the most familiar field extension, with no differentials at all. -/
example {M : Type*} [AddCommGroup M] [Module ℝ M] [Module ℂ M] [IsScalarTower ℝ ℂ M]
    (D : Derivation ℝ ℂ M) : D Complex.I = 0 := by
  have h2 : D (Complex.I ^ 2) = (2 : ℂ) • Complex.I • D Complex.I := by
    rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul ℂ 2]
    norm_num
  rw [show Complex.I ^ 2 = -1 by norm_num, map_neg, Derivation.map_one_eq_zero, neg_zero] at h2
  rcases smul_eq_zero.mp h2.symm with h | h
  · norm_num at h
  rcases smul_eq_zero.mp h with h' | h'
  · exact absurd h' (by norm_num)
  · exact h'

/- **How big is `Ω`?** Its dimension over `F` is the size of a *separating*
transcendence basis: with `s` algebraically independent and `F` separable over
`K(s)`, the rank is `#s`. The word "separating" is the whole content — the
transcendence degree alone does not control the rank (D.1 below), and no place
can supply a separating transcendental. The `#s = 1` case is the block above, whose
`Basis` is `kaehlerAdjoinBasis` at `s = {x}`. -/
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
term the place has no record of. This is the Leibniz rule computed in Zone B with
`a = u` and `b = t_v`: the first summand is `d t_v` rescaled, the second is the moving
term, and it is exactly the defect that `I²` discards in `Ω` but `ord` cannot see.
`Derivation.leibniz` below is that computation, packaged — no new content. -/
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
(Zone A), while the rank of `Ω` is a property of the *extension*. Standard
counterexample, not formalised here: `k` of characteristic `p`, `K = k(X)`,
`F = K(x)(t)` with `x ^ p = X` and `t` transcendental over `K(x)`. Then
`trdeg(F/K) = 1` and every place still has a uniformiser; `Ω[K(x)/K]` is free of rank
one on `d x` (`x ^ p = X` differentiates to `p x ^ (p - 1) d x = 0`, which is *no*
relation in characteristic `p` — Zone B's p-th-power blindness); and `F = K(x)(t)`
splits `Ω` as `Ω[K(x)/K] ⊗ F` plus `F · d t`, so `finrank_F Ω[F⁄K] = 2`. A one-variable
function field with a two-dimensional `Ω`, every uniformiser none the wiser, and no `ω`
generating: exactly what `kaehler_free_rank_one` excludes, and why it must be an axiom
rather than a theorem about places. The positive control is the rational function
field: -/
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

* **Delete `[DCoordGenerates]`** from `exists_eq_smul_dCoord` (Zone C) and the claim
  becomes false: no single `f` gives `ω = f • d t_v` for every `ω` unless `d t_v`
  spans. That is the content of the class, and why it cannot be an instance.

* **Delete `[Nontrivial Ω]`** from `dCoord_ne_zero`: with `Ω` subsingleton every
  differential is zero, so `d t_v ≠ 0` needs the rank-one axiom (D.1), not generation.

* **Change the uniformiser.** `u * t_v` has order `1` for every unit `u`, but
  `d (u * t_v)` picks up the Leibniz term `t_v • d u` (Zone B). For `u` a constant the
  term dies (`Derivation.map_algebraMap`), so to see a change you need a unit outside
  the image of `K` — which `ord` cannot distinguish from a constant. Prove the case
  `u = algebraMap K F c` to watch the mechanism: it works only *because* constants have
  no differential.

* **Replace `CharP F p`** by `CharZero F` in the p-th-power example and watch the proof
  die at `(p : F) = 0`: in characteristic zero `d (a ^ n) = n • a ^ (n - 1) • d a` is not
  zero for transcendental `a`, so `d` no longer contains the p-th powers. That is why
  the inseparable counterexamples of D.1 and of the transcendental block live in
  characteristic `p`.

* **`differentialCoeff` is total**: an `if` returning `0` outside the span, so
  `ordDifferential` reports "no pole, no zero" there — and `HasCanonicalDivisor` reads
  that total function at every place. The D.2 hypothesis is what keeps the divisor from
  silently losing those places, the same pattern as `genus` and `finrank` in the
  hierarchy sheet: a total definition with a junk branch, plus a hypothesis that the
  branch is never taken.

* **Make `x` algebraic.** In Zone B's transcendental block, `Transcendental K x` is used
  at exactly one point, the renaming `K(X) ≅ K(x)`, and for algebraic `x` there is no
  such coordinate: `K[X] → K(x)` is a surjection with nonzero kernel. The conclusion
  flips, too: for `x` algebraic and separable over `K`, `Ω[K(x)⁄K] = 0` (a finite
  separable extension is formally étale, so `Ω` base-changes from `Ω[K⁄K] = 0`), hence
  `d x = 0`. Nonzero differential is a property of *transcendence*.

* **Drop the square.** `Ω` is `I ⧸ I²` and not `I` solely because the defect of Leibniz
  is a *square*: `s ↦ 1 ⊗ₜ s - s ⊗ₜ 1` is not a derivation into `I` (its defect at
  `a * b` is `da * db`), and in the model `R[x]` that defect is `(y - x)² ≠ 0`. Run
  Zone B's last example with `Ideal.toCotangent` replaced by the inclusion
  `I → F ⊗[K] F`, and the step `Ideal.toCotangent_eq, pow_two` is the only one that
  fails — the only step where `I²` was used.

* **One layer down.** The *local* statement — `m_v / m_v²` one-dimensional over
  `κ(v)`, `m_v = (t_v)` — is free from the DVR structure, and `ord_uniformizer` is its
  `F`-side shadow. What is not free is the passage from that local one-dimensionality to
  a generator of the global `Ω`: compare `IsDiscreteValuationRing.exists_irreducible`
  (Zone A, no curve hypotheses) with `DCoordGenerates` (Zone C, a hypothesis on every
  rung). -/

/- ## Zone Q — question log

Oldest first. Each entry: question, one-line answer, and a pointer to the zone
that was edited — the answer is one line by design; the long version is the zone.

* (2026-10-23) *Worksheet created.*
* (2026-10-23) **Q1.** A uniformiser — why does it not give a differential, and why is
  `kaehler_free_rank_one` an axiom? — `d t_v` is an *element*, not a basis: rank is a
  property of the extension (D.1), generation at a place is a hypothesis (D.2), finite
  support is a theorem over a perfect field (D.3). Zones A, C, D.
* (2026-10-23) **Q2.** Is the axiom "there is a nonzero differential"? — No, it is
  "`Ω` is a line", strictly stronger; existence is derived (`instNontrivialKaehler`) and
  would give neither the coefficient, nor the order, nor independence of `t_v`. D.1.
* (2026-10-23) **Q3.** Does `ord` plus `t_v` determine `d f`? — No: `d (u · t_v)` carries
  `t_v · d u`, which `ord` cannot see; the two crux examples of Zone C are that, one for
  `ord` and one for `d`.
* (2026-10-23) **Q4.** Why is `differentialCoeff` total, with a `0` branch? — So that
  `ordDifferential` and `HasCanonicalDivisor` are definitions and not conditional
  statements; the hypothesis is a class the honest lemmas require, and the junk branch
  is what Zone E pokes at. Zone C.
* (2026-10-30) **Q5.** What does `irreducible_iff_uniformizer` say, and how is `ord`
  built? — It is the two spellings `Irreducible ϖ ↔ m_v = (ϖ)`, so `rw` converts either
  way; and `ord = -log ∘ adicValuation`, with `ℤᵐ⁰` multiplicative, junk `log 0 = 0`,
  and the outer minus turning `exp (-1)` into order `1`. Zone A.
* (2026-10-30) **Q6.** What is the ideal in the definition of `KaehlerDifferential`? —
  The diagonal: two copies of `F` in `F ⊗[K] F`, `lmul'` identifies them, `I = ker lmul'`,
  generated by `1 ⊗ₜ f - f ⊗ₜ 1`; `Ω = I ⧸ I²` keeps the first-order part, and that is
  Leibniz and what makes `Ω` an `F`-module. Zone B.
* (2026-10-30) **Q7.** Is an elementary tensor with `a * b = 1` in the kernel? — No:
  `lmul' (a ⊗ₜ b) = a * b`, so `∈ I` means `a * b = 0`; the interesting members of `I`
  are its *sums*, whose summands are not in `I`. Zone B.
* (2026-10-30) **Q8.** Why is the kernel an *ideal*? — `F ⊗[K] F` is a commutative ring
  and `lmul'` is multiplicative, so `I` is closed under multiplication by any ring
  element; `Ideal R` is `Submodule R R` plus that one closure. Payoff: `I²` exists, and
  `(F ⊗ F) ⧸ I ≅ F` is the ring `Ω` is a module over. Zone B.
* (2026-10-30) **Q9.** Where is the multiplication on `F ⊗[K] F` defined? — Not in this
  sheet: instance search from `[Algebra K F]` (`LinearMap.mul`, `map₂`,
  `instCommRing`, `tmul_mul_tmul`); with only `Module K F` there is no `*`. Zone B.
* (2026-10-30) **Q10.** Can `s` be moved between the two tensor slots? — No: only scalars
  cross, multiplication recombines. `s ⊗ₜ 1 - 1 ⊗ₜ s` generates `I`, and its class *is*
  `d s`; imposing `s ⊗ₜ 1 = 1 ⊗ₜ s` for all `s` gives `Ω = 0`, i.e. unramified. Zone B.
* (2026-10-31) **Q11.** Why was Leibniz asserted and then quoted from
  `Derivation.leibniz`? — The assertion *is* the black box: mathlib's `leibniz'` is
  `toCotangent_eq` + `pow_two` + one `mul_mem_mul` + `convert!`/`ring_nf`, i.e. "the
  defect is `Da · Db ∈ I²`". Zone B computes it, and the same computation is why `Ω` is
  `I ⧸ I²` and what Zone C's `d (u * t_v)` cites. Zones B, C, E.
* (2026-10-31) **Q12.** Why is `d x ≠ 0` for transcendental `x`? — Because `d` of a
  coordinate is `1`: `Ω[K[X]⁄K] ≅ K[X]` by the formal derivative (`d X ↦ 1`), and every
  step from `K[X]` to `F` is a base change along a formally étale map (localisation,
  separable extension), so `d x` stays the generator. FLT's `exists_basis` is that base
  change as an object; in characteristic `p`, `x = y ^ p` breaks it, which is exactly
  what `IsSeparable` excludes. Zones B, E.
* (2026-10-31) **Q13.** How does `D` relate to the derivative of calculus over `ℝ` or `ℂ`?
  — `D f` is `d f`; `f'` is `d f` divided by a frame, `D f = ∑ᵢ (∂f/∂xᵢ) • d xᵢ`, so the
  classical partials are the coefficients (Zone C's `differentialCoeff`, and
  `polynomialEquiv` is `n = 1`). In characteristic `0` the dictionary is exact — rank
  `= trdeg`, kernel `=` the algebraic elements, so "`f' = 0` ⟹ constant" holds as far as
  it can, and the p-th-power collapse is unavailable; `Ω[ℂ⁄ℝ] = 0` while `Ω[ℂ(x)⁄ℂ]` is a
  line, since rank is transcendence degree, not dimension. Zone B, new block before
  "How big is `Ω`". -/

end Play
