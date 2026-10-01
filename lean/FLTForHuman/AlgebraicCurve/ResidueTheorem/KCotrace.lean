/-
Row 6 (the K ending), engine half — the Kähler-cotrace/fiber-localized residue
machinery that the general-curve `ResidueTheoremK` producer consumes.

Sources, pinned to `anthropics/fermats-last-theorem@aa2d8b3`:

* `P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean`
  (<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_residueTheoremK_of_isAlgClosed.lean>)

This module carries the declarations of that file that are genuinely new in the port:
the four `def … : Prop` named rows (`FiberKaehlerCotraceResidueIdentity`,
`CotraceResidueIdentityOnFiberLocalized`, `CotraceFiberLocalizedPolarApprox`,
`IsSeparatingTranscendental`), the `regularPoleSubmodule` family on `Place`, the
Kähler-cotrace/`IsSeparatingTranscendental` bridge, the DVR sandwich `Cotpk43T3.*`,
and the separator/polar-approximation `GF24a9RRDx` block.  The residue-theorem chain
and the public headline live in `KFamily.lean`, which imports this module.

The port's ℙ¹ chain spells the place `p1PlaceInfty`; here we state at the pin's
`placeInfty` spelling and adapt with `change`/`simpa [p1PlaceInfty]` where a ℙ¹ lemma
is consumed.  The pin's `private` helpers that the proofs reach and that are already
public in the port are imported, not re-proved; the three private `KwF4R1V384a*`
`Prop` rows are re-landed `private` in `KFamily.lean` (promotion debt).
-/
import FLTForHuman.AlgebraicCurve.P1.DivPowEnding
import FLTForHuman.AlgebraicCurve.LocalResidue.Instance

set_option autoImplicit false
set_option linter.unusedSectionVars false

open KaehlerDifferential LinearMap Submodule
open WithZero

noncomputable section

namespace AlgebraicCurve

/-! ## The named residue rows (pin `S_` 4278, 5024, 5034) -/

section NamedRows

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- (pin 4278) The fiber Kähler cotrace residue identity in its canonical-currency
form: the sum of the residue terms over the fiber equals the residue term of the
traced differential at the base place. -/
def FiberKaehlerCotraceResidueIdentity : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (f : F),
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F f) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F f)) v

/-- (pin 5024) The fiber-localized form of the cotrace residue identity: the sum over
the (essentially unique nontrivial) fiber place. -/
def CotraceResidueIdentityOnFiberLocalized : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (p : F),
    (∀ w₁ ∈ v.fiber F, ∀ w₂ ∈ v.fiber F,
      p ∉ w₁.regularSubmodule (kaehlerPullback K F E ωE) →
      p ∉ w₂.regularSubmodule (kaehlerPullback K F E ωE) → w₁ = w₂) →
    ∑ w ∈ v.fiber F, kaehlerResidueTerm (kaehlerPullback K F E ωE) (diagonalHom K F p) w
      = kaehlerResidueTerm ωE (diagonalHom K E (Algebra.trace E F p)) v

end NamedRows

/-! ## `IsSeparatingTranscendental` (pin 4672) -/

section SeparatingCarrier

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [Algebra (RatFunc K) F]
variable [IsScalarTower K (RatFunc K) F]

/-- (pin 4672) The separating-transcendental predicate of the row-6 file: the
Kähler differential of `X` does not vanish after base change.  This is **not** the
port's `HasSeparatingTranscendental` (the `∃`-transcendental form); it is the
differential form the Kähler-cotrace bridge is stated against. -/
def IsSeparatingTranscendental : Prop :=
  KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) ≠ 0

end SeparatingCarrier

/-! ## The `regularPoleSubmodule` family (pin 3131–3358) -/

namespace Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- (pin 3131) Membership in `regularSubmodule`, definitionally. -/
@[scoped simp]
theorem mem_regularSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (f : F) :
    f ∈ w.regularSubmodule ωF ↔ f * w.differentialCoeff ωF ∈ w.toValuationSubring := Iff.rfl

/-- (pin 3222) The submodule of `F` on which `f ↦ uniformizer ^ n * (f * dω)` is
integral at `w`. -/
def regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (n : ℕ) : Submodule K F :=
  (w.poleSubmodule n).comap (LinearMap.mulRight K (w.differentialCoeff ωF))

/-- (pin 3226) Membership in `regularPoleSubmodule`, definitionally. -/
@[scoped simp]
theorem mem_regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (n : ℕ) (f : F) :
    f ∈ w.regularPoleSubmodule ωF n
      ↔ w.uniformizer ^ n * (f * w.differentialCoeff ωF) ∈ w.toValuationSubring := Iff.rfl

/-- (pin 3232) `regularPoleSubmodule ωF 0 = regularSubmodule ωF`. -/
theorem regularPoleSubmodule_zero (w : Place K F) (ωF : Ω[F⁄K]) :
    w.regularPoleSubmodule ωF 0 = w.regularSubmodule ωF := by
  ext f
  simp only [mem_regularPoleSubmodule, pow_zero, one_mul, mem_regularSubmodule]

/-- (pin 3237) `regularPoleSubmodule ωF` is monotone in `n`. -/
theorem regularPoleSubmodule_mono (w : Place K F) (ωF : Ω[F⁄K]) :
    Monotone (w.regularPoleSubmodule ωF) :=
  fun _ _ hmn => Submodule.comap_mono (w.poleSubmodule_mono hmn)

/-- (pin 3242) The `regularPoleSubmodule` family exhausts `F`. -/
theorem iSup_regularPoleSubmodule_eq_top (w : Place K F) (ωF : Ω[F⁄K]) :
    ⨆ n, w.regularPoleSubmodule ωF n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  have hmem : f * w.differentialCoeff ωF ∈ ⨆ n, w.poleSubmodule n :=
    w.iSup_poleSubmodule_eq_top ▸ Submodule.mem_top
  obtain ⟨n, hn⟩ := (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le w.poleSubmodule_mono)).mp hmem
  exact Submodule.mem_iSup_of_mem n hn

/-- (pin 3253) Every element lies in some `regularPoleSubmodule`. -/
theorem exists_mem_regularPoleSubmodule (w : Place K F) (ωF : Ω[F⁄K]) (f : F) :
    ∃ n, f ∈ w.regularPoleSubmodule ωF n := by
  have h : f ∈ ⨆ n, w.regularPoleSubmodule ωF n :=
    (w.iSup_regularPoleSubmodule_eq_top ωF) ▸ Submodule.mem_top
  exact (Submodule.mem_iSup_of_directed _
    (Monotone.directed_le (w.regularPoleSubmodule_mono ωF))).mp h

end Place

/-! ## `CotraceFiberLocalizedPolarApprox` (pin 5034) -/

section NamedRowsB

variable (K F : Type*) [Field K] [Field F] [Algebra K F]
variable (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
variable [HasCanonicalLocalResidueKStar K E] [HasCanonicalLocalResidueKStar K F]
variable [Algebra.IsIntegral E F]

/-- (pin 5034) The polar approximation row: a function in the `(n+1)`-st regular
pole submodule at `w` is approximated modulo the `n`-th one by a function regular at
every other fiber place. -/
def CotraceFiberLocalizedPolarApprox : Prop :=
  ∀ [HasPrincipalDivisors K E] [HasPrincipalDivisors K F]
    {ωE : Ω[E⁄K]} (_ : ωE ≠ 0) (_ : kaehlerPullback K F E ωE ≠ 0)
    (v : Place K E) (w : Place K F) (_ : w ∈ v.fiber F) (n : ℕ) (f : F)
    (_ : f ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) (n + 1)),
    ∃ p : F,
      f - p ∈ w.regularPoleSubmodule (kaehlerPullback K F E ωE) n ∧
      ∀ w' ∈ v.fiber F, w' ≠ w → p ∈ w'.regularSubmodule (kaehlerPullback K F E ωE)

end NamedRowsB

/-! ## The Kähler cotrace bridge (pin 4364–5011) -/

section KaehlerCotrace

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- (pin 4364) The cotrace is the chain rule on `D`. -/
theorem kaehlerCotrace_D (e : E) :
    kaehlerCotrace K E F (KaehlerDifferential.D K E e)
      = KaehlerDifferential.D K F (algebraMap E F e) :=
  KaehlerDifferential.map_D K K E F e

/-- (pin 4369) The cotrace is `E`-semilinear. -/
theorem kaehlerCotrace_smul_algebraMap (e : E) (ωE : Ω[E⁄K]) :
    kaehlerCotrace K E F (e • ωE) = (algebraMap E F e) • kaehlerCotrace K E F ωE := by
  rw [LinearMap.map_smul, algebra_compatible_smul F e]

end KaehlerCotrace

section SeparatingWitness

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]

/-- (pin 4481) If the cotrace kills no witness, it kills no `dCoord`. -/
theorem kaehlerCotrace_dCoord_ne_zero_of_exists
    (v : Place K E) [v.DCoordGenerates]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    kaehlerCotrace K E F v.dCoord ≠ 0 := by
  intro hdc
  apply h
  rw [← v.differentialCoeff_smul_dCoord ωE₀, kaehlerCotrace_smul_algebraMap, hdc, smul_zero]

/-- (pin 4489) A nonvanishing pulled-back differential comes from a nonvanishing
cotrace. -/
theorem exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 :=
  ⟨KaehlerDifferential.D K E e, by rw [kaehlerCotrace_D]; exact he⟩

end SeparatingWitness

section CotraceInjective

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

/-- (pin 4573) Injectivity of the cotrace is detected at a `dCoord`. -/
theorem kaehlerCotrace_injective_iff_dCoord_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]] :
    Function.Injective (kaehlerCotrace K E F) ↔ kaehlerCotrace K E F v.dCoord ≠ 0 := by
  constructor
  · intro hinj h0
    exact v.dCoord_ne_zero (hinj (h0.trans (_root_.map_zero _).symm))
  · intro hne ωE ωE' heq
    obtain ⟨e, rfl⟩ := v.exists_eq_smul_dCoord ωE
    obtain ⟨e', rfl⟩ := v.exists_eq_smul_dCoord ωE'
    rw [kaehlerCotrace_smul_algebraMap, kaehlerCotrace_smul_algebraMap] at heq
    have hee' : algebraMap E F e = algebraMap E F e' :=
      smul_left_injective F hne heq
    rw [(algebraMap E F).injective hee']

variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalLocalResidueKStar K E]

/-- (pin 4589) A nonvanishing cotrace witness makes the cotrace injective. -/
theorem kaehlerCotrace_injective_of_exists_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {ωE₀ : Ω[E⁄K]} (h : kaehlerCotrace K E F ωE₀ ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  (kaehlerCotrace_injective_iff_dCoord_ne_zero v).mpr
    (kaehlerCotrace_dCoord_ne_zero_of_exists v h)

/-- (pin 4596) A nonvanishing `D (algebraMap e)` makes the cotrace injective. -/
theorem kaehlerCotrace_injective_of_D_algebraMap_ne_zero
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    {e : E} (he : KaehlerDifferential.D K F (algebraMap E F e) ≠ 0) :
    Function.Injective (kaehlerCotrace K E F) :=
  let ⟨_, hωE⟩ := exists_kaehlerCotrace_ne_zero_of_D_algebraMap_ne_zero he
  kaehlerCotrace_injective_of_exists_ne_zero v hωE

end CotraceInjective

section CotraceDX

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

/-- (pin 4659) The cotrace of `dX`. -/
theorem kaehlerCotrace_dX_eq :
    kaehlerCotrace K (RatFunc K) F (dX K)
      = KaehlerDifferential.D K F (algebraMap (RatFunc K) F RatFunc.X) :=
  kaehlerCotrace_D RatFunc.X

end CotraceDX

section SeparatingCarrierB

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

/-- (pin 4684) Separating transcendental gives a nonvanishing cotrace of `dX`. -/
theorem kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental
    (hsep : IsSeparatingTranscendental K F) :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [kaehlerCotrace_dX_eq]; exact hsep

/-- (pin 4689) `IsSeparatingTranscendental` is exactly nonvanishing of the cotrace. -/
theorem isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero :
    IsSeparatingTranscendental K F ↔ kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 := by
  rw [IsSeparatingTranscendental, kaehlerCotrace_dX_eq]

end SeparatingCarrierB

section SepIffInjective

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

/-- (pin 4773) `IsSeparatingTranscendental` is exactly injectivity of the cotrace. -/
theorem isSeparatingTranscendental_iff_kaehlerCotrace_injective
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]] :
    IsSeparatingTranscendental K F ↔ Function.Injective (kaehlerCotrace K (RatFunc K) F) := by
  constructor
  · exact fun hsep => kaehlerCotrace_injective_of_D_algebraMap_ne_zero (e := RatFunc.X) v hsep
  · intro hinj
    rw [isSeparatingTranscendental_iff_kaehlerCotrace_dX_ne_zero]
    exact fun h0 => dX_ne_zero K
      (hinj (h0.trans (map_zero (kaehlerCotrace K (RatFunc K) F)).symm))

end SepIffInjective

section MapBaseChangeSurj

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]

/-- (pin 4791) Formally unramified makes the base-change map onto the Kähler
differentials surjective. -/
theorem surjective_mapBaseChange_of_formallyUnramified [Algebra.FormallyUnramified E F] :
    Function.Surjective (KaehlerDifferential.mapBaseChange K E F) := by
  rw [← LinearMap.range_eq_top, KaehlerDifferential.range_mapBaseChange]
  exact LinearMap.ker_eq_top.mpr (Subsingleton.elim _ _)

/-- (pin 4804) Formally unramified gives a nonvanishing cotrace witness. -/
theorem exists_kaehlerCotrace_ne_zero_of_formallyUnramified
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    ∃ ωE : Ω[E⁄K], kaehlerCotrace K E F ωE ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h

  have hmap0 : ∀ t, KaehlerDifferential.mapBaseChange K E F t = 0 := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact _root_.map_zero _
    | tmul f ωE =>
        rw [KaehlerDifferential.mapBaseChange_tmul]
        show f • kaehlerCotrace K E F ωE = 0
        rw [h ωE, smul_zero]
    | add a b ha hb => rw [map_add, ha, hb, add_zero]

  obtain ⟨ωF, hωF⟩ := exists_ne (0 : Ω[F⁄K])
  obtain ⟨t, ht⟩ := surjective_mapBaseChange_of_formallyUnramified (K := K) (E := E) (F := F) ωF
  exact hωF (ht ▸ hmap0 t)

/-- (pin 4832) Formally unramified makes the cotrace injective. -/
theorem kaehlerCotrace_injective_of_formallyUnramified
    (v : Place K E) [v.DCoordGenerates] [Nontrivial Ω[E⁄K]]
    [Algebra.FormallyUnramified E F] [Nontrivial Ω[F⁄K]] :
    Function.Injective (kaehlerCotrace K E F) := by
  obtain ⟨ωE₀, hωE₀⟩ :=
    exists_kaehlerCotrace_ne_zero_of_formallyUnramified (K := K) (E := E) (F := F)
  exact kaehlerCotrace_injective_of_exists_ne_zero v hωE₀

end MapBaseChangeSurj

section SepDischarge

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

/-- (pin 4849) Formally unramified gives `IsSeparatingTranscendental`. -/
theorem isSeparatingTranscendental_of_formallyUnramified
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.FormallyUnramified (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  (isSeparatingTranscendental_iff_kaehlerCotrace_injective K F v).mpr
    (kaehlerCotrace_injective_of_formallyUnramified v)

/-- (pin 4857) Separability gives `IsSeparatingTranscendental`. -/
theorem isSeparatingTranscendental_of_isSeparable
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    IsSeparatingTranscendental K F :=
  haveI := Algebra.FormallyUnramified.of_isSeparable (RatFunc K) F
  isSeparatingTranscendental_of_formallyUnramified K F v

end SepDischarge

section CotraceDXSeparable

variable (K : Type*) [Field K]
variable (F : Type*) [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]

/-- (pin 4917) Separability makes the cotrace of `dX` nonvanishing. -/
theorem kaehlerCotrace_dX_ne_zero_of_isSeparable
    [HasCanonicalLocalResidueKStar K (RatFunc K)]
    (v : Place K (RatFunc K)) [v.DCoordGenerates] [Nontrivial Ω[(RatFunc K)⁄K]]
    [Algebra.IsSeparable (RatFunc K) F] [Nontrivial Ω[F⁄K]] :
    kaehlerCotrace K (RatFunc K) F (dX K) ≠ 0 :=
  kaehlerCotrace_dX_ne_zero_of_isSeparatingTranscendental K F
    (isSeparatingTranscendental_of_isSeparable K F v)

end CotraceDXSeparable

section CurrencyBridge

variable {K F : Type*} [Field K] [Field F] [Algebra K F] [HasCanonicalLocalResidueKStar K F]
variable {E : Type*} [Field E] [Algebra K E] [HasCanonicalLocalResidueKStar K E]
variable [Algebra E F] [IsScalarTower K E F]

/-- (pin 5011) `kaehlerPullback` is the cotrace. -/
theorem kaehlerPullback_eq_kaehlerCotrace (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E ωE = kaehlerCotrace K E F ωE := rfl

end CurrencyBridge

section KaehlerPullbackSmul

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

/-- (pin 6540) The pullback is `E`-semilinear. -/
theorem kw_mlc_hrtCharP7_kaehlerPullback_smul (g : E) (ωE : Ω[E⁄K]) :
    kaehlerPullback K F E (g • ωE) = (algebraMap E F g) • kaehlerPullback K F E ωE := by
  show (KaehlerDifferential.map K K E F) (g • ωE)
    = (algebraMap E F g) • (KaehlerDifferential.map K K E F) ωE
  rw [LinearMap.map_smul, algebra_compatible_smul F g]

end KaehlerPullbackSmul

section PlaceDifferentialCoeffPullback

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {E : Type*} [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]

variable [Nontrivial Ω[F⁄K]]

/-- (pin 6852) The differential coefficient of a pulled-back differential. -/
theorem differentialCoeff_kaehlerPullback [Nontrivial Ω[E⁄K]]
    (v : Place K E) [v.DCoordGenerates] (w : Place K F) [w.DCoordGenerates]
    (ωE : Ω[E⁄K]) :
    w.differentialCoeff (kaehlerPullback K F E ωE)
      = algebraMap E F (v.differentialCoeff ωE)
        * w.differentialCoeff (kaehlerPullback K F E v.dCoord) := by
  conv_lhs => rw [← v.differentialCoeff_smul_dCoord ωE,
    kw_mlc_hrtCharP7_kaehlerPullback_smul, w.differentialCoeff_smul]

end PlaceDifferentialCoeffPullback

end AlgebraicCurve

/-! ## The DVR sandwich (pin 5723–5813) -/

namespace Cotpk43T3

open AlgebraicCurve

section DVRSandwich

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

/-- (pin 5723) A Dedekind valuation subring sandwiched inside a place's valuation
subring is that valuation subring. -/
theorem cotpk43_t3_toValuationSubring_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v : Place k F) (hle : O ≤ v.toValuationSubring) :
    v.toValuationSubring = O := by
  haveI := hO
  have hSP : O.ofPrime (O.idealOfLE v.toValuationSubring hle) = v.toValuationSubring :=
    ValuationSubring.ofPrime_idealOfLE O v.toValuationSubring hle
  rcases eq_or_ne (O.idealOfLE v.toValuationSubring hle) ⊥ with hP | hP
  ·
    exfalso
    apply v.ne_top'
    have h2 : O.ofPrime ⊥ ≤ O.ofPrime (O.idealOfLE v.toValuationSubring hle) :=
      ValuationSubring.ofPrime_le_of_le (h := hP.le)
    rw [ValuationSubring.ofPrime_bot] at h2
    exact top_le_iff.mp (le_trans h2 hSP.le)
  ·
    have hPmax : (O.idealOfLE v.toValuationSubring hle).IsMaximal :=
      Ideal.IsPrime.isMaximal inferInstance hP
    have hPeq : O.idealOfLE v.toValuationSubring hle = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal hPmax
    have h3 : O.ofPrime (O.idealOfLE v.toValuationSubring hle)
        = O.ofPrime (IsLocalRing.maximalIdeal O) :=
      le_antisymm (ValuationSubring.ofPrime_le_of_le (h := hPeq.ge))
        (ValuationSubring.ofPrime_le_of_le (h := hPeq.le))
    rw [ValuationSubring.ofPrime_top] at h3
    rw [hSP] at h3
    exact h3

/-- (pin 5751) Two places containing a common Dedekind valuation subring coincide. -/
theorem cotpk43_t3_place_eq_of_dedekind_le
    (O : ValuationSubring F) (hO : IsDedekindDomain O)
    (v w : Place k F) (hv : O ≤ v.toValuationSubring) (hw : O ≤ w.toValuationSubring) :
    v = w :=
  Place.ext ((cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO v hv).trans
    (cotpk43_t3_toValuationSubring_eq_of_dedekind_le O hO w hw).symm)

/-- (pin 5758) A place whose valuation subring contains another's coincides with it. -/
theorem cotpk43_t3_place_eq_of_toValuationSubring_le
    (v w : Place k F) (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  cotpk43_t3_place_eq_of_dedekind_le v.toValuationSubring inferInstance v w le_rfl h

end DVRSandwich

end Cotpk43T3

/-! ## The separator and polar-approximation block (pin 5814–6110) -/

namespace ModularCurve.GF24a9RRDx

open AlgebraicCurve Cotpk43T3

section Toolkit

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- (pin 5814) `ord` is negation-invariant. -/
theorem gf24a9r_ord_neg (v : Place K F) (g : F) : v.ord (-g) = v.ord g := by
  simp only [Place.ord, Valuation.map_neg]

/-- (pin 5817) `ord` of a power. -/
theorem gf24a9r_ord_pow (v : Place K F) (g : F) (m : ℕ) :
    v.ord (g ^ m) = (m : ℤ) * v.ord g := by
  rw [show (g ^ m : F) = g ^ (m : ℤ) from (zpow_natCast g m).symm, v.ord_zpow]

/-- (pin 5821) `1 + g ≠ 0` when `g` has positive order. -/
theorem gf24a9r_one_add_ne_zero_of_ord_pos (v : Place K F) {g : F}
    (h : 0 < v.ord g) : (1 : F) + g ≠ 0 := by
  intro hcon
  have hg1 : g = -(1 : F) := by
    rw [add_comm] at hcon
    exact eq_neg_of_add_eq_zero_left hcon
  have h0 : v.ord g = 0 := by rw [hg1, gf24a9r_ord_neg, v.ord_one]
  omega

/-- (pin 5830) The order of `1 + g` vanishes for positive-order `g`. -/
theorem gf24a9r_ord_one_add_of_ord_pos (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : 0 < v.ord g) : v.ord (1 + g) = 0 := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_left h.le]

/-- (pin 5837) The order of `1 + g` is `ord g` for negative-order `g`. -/
theorem gf24a9r_ord_one_add_of_ord_neg (v : Place K F) {g : F} (hg : g ≠ 0)
    (h : v.ord g < 0) : v.ord (1 + g) = v.ord g := by
  have hmin := v.ord_add_eq_min (f := (1 : F)) one_ne_zero hg
    (by rw [v.ord_one]; omega)
  rw [v.ord_one] at hmin
  rw [hmin, min_eq_right h.le]

/-- (pin 5844) Two distinct places are separated by an element positive at one and
negative at the other. -/
theorem gf24a9r_exists_ord_pos_ord_neg {w₁ w₂ : Place K F} (h : w₁ ≠ w₂) :
    ∃ u : F, u ≠ 0 ∧ 0 < w₁.ord u ∧ w₂.ord u < 0 := by
  have h12 : ¬(w₁.toValuationSubring ≤ w₂.toValuationSubring) := fun hle =>
    h (cotpk43_t3_place_eq_of_toValuationSubring_le w₁ w₂ hle)
  have h21 : ¬(w₂.toValuationSubring ≤ w₁.toValuationSubring) := fun hle =>
    h.symm (cotpk43_t3_place_eq_of_toValuationSubring_le w₂ w₁ hle)
  obtain ⟨x, hx1, hx2⟩ := SetLike.not_le_iff_exists.mp h12
  obtain ⟨y, hy2, hy1⟩ := SetLike.not_le_iff_exists.mp h21
  have hx0 : x ≠ 0 := by rintro rfl; exact hx2 (zero_mem _)
  have hy0 : y ≠ 0 := by rintro rfl; exact hy1 (zero_mem _)
  have hx1o : 0 ≤ w₁.ord x := w₁.ord_nonneg_of_mem hx1
  have hy2o : 0 ≤ w₂.ord y := w₂.ord_nonneg_of_mem hy2
  have hx2o : w₂.ord x < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hx2 (w₂.mem_of_ord_nonneg hx0 hcon)
  have hy1o : w₁.ord y < 0 := by
    by_contra hcon
    rw [not_lt] at hcon
    exact hy1 (w₁.mem_of_ord_nonneg hy0 hcon)
  refine ⟨x * y⁻¹, mul_ne_zero hx0 (inv_ne_zero hy0), ?_, ?_⟩
  · rw [w₁.ord_mul hx0 (inv_ne_zero hy0), w₁.ord_inv]
    omega
  · rw [w₂.ord_mul hx0 (inv_ne_zero hy0), w₂.ord_inv]
    omega

/-- (pin 5870) A finite set of places other than `w` is separated from `w` by one
element positive at `w` and negative at all of them. -/
theorem gf24a9r_exists_separator (w : Place K F) (S : Finset (Place K F)) (hw : w ∉ S) :
    ∃ u : F, u ≠ 0 ∧ 0 < w.ord u ∧ ∀ w' ∈ S, w'.ord u < 0 := by
  classical
  revert hw
  induction S using Finset.induction_on with
  | empty =>
    intro _
    obtain ⟨g, hg0, hgord⟩ := w.exists_ord_pos
    exact ⟨g, hg0, hgord, fun w' hw' => absurd hw' (Finset.notMem_empty w')⟩
  | @insert a S' ha ih =>
    intro hw
    have hwa : w ≠ a := fun hcon => hw (hcon ▸ Finset.mem_insert_self a S')
    have hwS' : w ∉ S' := fun hcon => hw (Finset.mem_insert_of_mem hcon)
    obtain ⟨y, hy0, hyw, hyS'⟩ := ih hwS'
    obtain ⟨z, hz0, hzw, hza⟩ := gf24a9r_exists_ord_pos_ord_neg hwa
    rcases lt_trichotomy (a.ord y) 0 with hneg | hzero | hpos
    ·
      refine ⟨y, hy0, hyw, fun w' hw' => ?_⟩
      rcases Finset.mem_insert.mp hw' with rfl | hw'S'
      · exact hneg
      · exact hyS' w' hw'S'
    ·
      obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hordeq : ∀ p : Place K F, p.ord (y ^ r * z) = (r : ℤ) * p.ord y + p.ord z :=
        fun p => by rw [p.ord_mul hyr0 hz0, gf24a9r_ord_pow]
      refine ⟨y ^ r * z, mul_ne_zero hyr0 hz0, ?_, fun w' hw' => ?_⟩
      · rw [hordeq w]
        have hnn : 0 ≤ (r : ℤ) * w.ord y := mul_nonneg (by omega) hyw.le
        linarith
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [hordeq w', hzero, mul_zero, zero_add]
          exact hza
        · rw [hordeq w']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith
    ·
      obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ S', w'.ord z < (r : ℤ) := by
        refine ⟨S'.sup (fun w' => (w'.ord z).toNat) + 1, Nat.le_add_left 1 _,
          fun w' hw' => ?_⟩
        have hle : (w'.ord z).toNat ≤ S'.sup (fun p => (p.ord z).toNat) :=
          Finset.le_sup (f := fun p => (p.ord z).toNat) hw'
        have h1 : w'.ord z ≤ ((w'.ord z).toNat : ℤ) := Int.self_le_toNat _
        have h2 : ((w'.ord z).toNat : ℤ)
            ≤ ((S'.sup (fun p => (p.ord z).toNat) : ℕ) : ℤ) := by exact_mod_cast hle
        omega
      have hyr0 : y ^ r ≠ 0 := pow_ne_zero r hy0
      have hone : (1 : F) + y ^ r ≠ 0 :=
        gf24a9r_one_add_ne_zero_of_ord_pos a
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      have hordw : w.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos w hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hyw)
      have horda : a.ord (1 + y ^ r) = 0 :=
        gf24a9r_ord_one_add_of_ord_pos a hyr0
          (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) hpos)
      refine ⟨z * (1 + y ^ r), mul_ne_zero hz0 hone, ?_, fun w' hw' => ?_⟩
      · rw [w.ord_mul hz0 hone, hordw]
        omega
      · rcases Finset.mem_insert.mp hw' with rfl | hw'S'
        · rw [w'.ord_mul hz0 hone, horda]
          omega
        · have hyneg : w'.ord (y ^ r) < 0 := by
            rw [gf24a9r_ord_pow]
            exact mul_neg_of_pos_of_neg (by omega) (hyS' w' hw'S')
          have hordw' : w'.ord (1 + y ^ r) = (r : ℤ) * w'.ord y := by
            rw [gf24a9r_ord_one_add_of_ord_neg w' hyr0 hyneg, gf24a9r_ord_pow]
          rw [w'.ord_mul hz0 hone, hordw']
          have h1 : w'.ord y ≤ -1 := by have := hyS' w' hw'S'; omega
          have h2 : (r : ℤ) * w'.ord y ≤ (r : ℤ) * (-1) :=
            mul_le_mul_of_nonneg_left h1 (by omega)
          have h3 := hrB w' hw'S'
          linarith

end Toolkit

section RowB

/-- (pin 5960) The polar approximation row is discharged unconditionally for a
finite integral extension. -/
theorem gf24a9r_cotraceFiberLocalizedPolarApprox
    (K F : Type*) [Field K] [Field F] [Algebra K F]
    (E : Type*) [Field E] [Algebra K E] [Algebra E F] [IsScalarTower K E F]
    [HasLocalResidue K E] [HasCanonicalLocalResidueKStar K E] [HasLocalResidue K F] [HasCanonicalLocalResidueKStar K F]
    [Algebra.IsIntegral E F] :
    CotraceFiberLocalizedPolarApprox K F E := by
  intro _instE _instF ωE _hωE _hgen v w _hwfib n f hf
  classical
  set ωF := kaehlerPullback K F E ωE

  rcases eq_or_ne f 0 with rfl | hf0
  · refine ⟨0, ?_, fun w' _ _ => Submodule.zero_mem _⟩
    rw [sub_zero]
    exact Submodule.zero_mem _

  obtain ⟨u, hu0, huw, huS⟩ :=
    gf24a9r_exists_separator w ((v.fiber F).erase w) (Finset.notMem_erase w _)

  obtain ⟨r, hr1, hrB⟩ : ∃ r : ℕ, 1 ≤ r ∧ ∀ w' ∈ (v.fiber F).erase w,
      -(w'.ord (f * w'.differentialCoeff ωF)) < (r : ℤ) := by
    refine ⟨((v.fiber F).erase w).sup
        (fun w' => (-(w'.ord (f * w'.differentialCoeff ωF))).toNat) + 1,
      Nat.le_add_left 1 _, fun w' hw' => ?_⟩
    have hle : (-(w'.ord (f * w'.differentialCoeff ωF))).toNat
        ≤ ((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) :=
      Finset.le_sup (f := fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) hw'
    have h1 : -(w'.ord (f * w'.differentialCoeff ωF))
        ≤ ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ) := Int.self_le_toNat _
    have h2 : ((-(w'.ord (f * w'.differentialCoeff ωF))).toNat : ℤ)
        ≤ ((((v.fiber F).erase w).sup
          (fun p => (-(p.ord (f * p.differentialCoeff ωF))).toNat) : ℕ) : ℤ) := by
      exact_mod_cast hle
    omega
  have hr1' : (1 : ℤ) ≤ (r : ℤ) := by exact_mod_cast hr1
  have hur0 : u ^ r ≠ 0 := pow_ne_zero r hu0
  have hone : (1 : F) + u ^ r ≠ 0 :=
    gf24a9r_one_add_ne_zero_of_ord_pos w
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  have hinv0 : ((1 : F) + u ^ r)⁻¹ ≠ 0 := inv_ne_zero hone
  have hordw_one : w.ord (1 + u ^ r) = 0 :=
    gf24a9r_ord_one_add_of_ord_pos w hur0
      (by rw [gf24a9r_ord_pow]; exact mul_pos (by omega) huw)
  refine ⟨f * ((1 : F) + u ^ r)⁻¹, ?_, ?_⟩
  ·
    have hdiff : f - f * ((1 : F) + u ^ r)⁻¹ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by
      have hcancel := mul_inv_cancel₀ hone
      calc f - f * ((1 : F) + u ^ r)⁻¹
          = f * (((1 : F) + u ^ r) * ((1 : F) + u ^ r)⁻¹)
            - f * ((1 : F) + u ^ r)⁻¹ := by rw [hcancel, mul_one]
        _ = f * u ^ r * ((1 : F) + u ^ r)⁻¹ := by ring
    rw [hdiff]
    refine (w.mem_regularPoleSubmodule ωF n _).mpr ?_
    rcases eq_or_ne (w.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero, mul_zero]
      exact zero_mem _
    ·
      have hin : 0 ≤ w.ord (w.uniformizer ^ (n + 1) * (f * w.differentialCoeff ωF)) :=
        w.ord_nonneg_of_mem ((w.mem_regularPoleSubmodule ωF (n + 1) f).mp hf)
      rw [w.ord_mul (w.uniformizer_pow_ne_zero _) (mul_ne_zero hf0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hf0 hdc] at hin
      have hX0 : f * u ^ r * ((1 : F) + u ^ r)⁻¹ ≠ 0 :=
        mul_ne_zero (mul_ne_zero hf0 hur0) hinv0
      refine w.mem_of_ord_nonneg
        (mul_ne_zero (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc)) ?_
      rw [w.ord_mul (w.uniformizer_pow_ne_zero n) (mul_ne_zero hX0 hdc),
        w.ord_uniformizer_pow, w.ord_mul hX0 hdc,
        w.ord_mul (mul_ne_zero hf0 hur0) hinv0, w.ord_mul hf0 hur0,
        w.ord_inv, hordw_one, gf24a9r_ord_pow]
      have hru : (1 : ℤ) ≤ (r : ℤ) * w.ord u := by
        have huw1 : (1 : ℤ) ≤ w.ord u := by omega
        nlinarith [hr1', huw1]
      push_cast at hin ⊢
      linarith
  ·
    intro w' hw'fib hne
    have hw'S : w' ∈ (v.fiber F).erase w := Finset.mem_erase.mpr ⟨hne, hw'fib⟩
    have hu_neg : w'.ord u < 0 := huS w' hw'S
    refine (w'.mem_regularSubmodule ωF _).mpr ?_
    rcases eq_or_ne (w'.differentialCoeff ωF) 0 with hdc | hdc
    · rw [hdc, mul_zero]
      exact zero_mem _
    · have hre : f * ((1 : F) + u ^ r)⁻¹ * w'.differentialCoeff ωF
          = f * w'.differentialCoeff ωF * ((1 : F) + u ^ r)⁻¹ := by ring
      rw [hre]
      have hfdc : f * w'.differentialCoeff ωF ≠ 0 := mul_ne_zero hf0 hdc
      have hurneg : w'.ord (u ^ r) < 0 := by
        rw [gf24a9r_ord_pow]
        exact mul_neg_of_pos_of_neg (by omega) hu_neg
      have hordw' : w'.ord (1 + u ^ r) = (r : ℤ) * w'.ord u := by
        rw [gf24a9r_ord_one_add_of_ord_neg w' hur0 hurneg, gf24a9r_ord_pow]
      refine w'.mem_of_ord_nonneg (mul_ne_zero hfdc hinv0) ?_
      rw [w'.ord_mul hfdc hinv0, w'.ord_inv, hordw']
      have h1 : w'.ord u ≤ -1 := by omega
      have h2 : (r : ℤ) * w'.ord u ≤ (r : ℤ) * (-1) :=
        mul_le_mul_of_nonneg_left h1 (by omega)
      have h3 := hrB w' hw'S
      linarith

end RowB

end ModularCurve.GF24a9RRDx
