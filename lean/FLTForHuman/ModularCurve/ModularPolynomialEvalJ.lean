/-
  SC — the row-S capstone: the modular polynomial evaluated at `j`, vanishing on the
  kernel of a cyclic isogeny.

  The row's terminal node

    `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`

  for `K` algebraically closed of characteristic `0`, an integral finite
  `ι : E'.FunctionField →ₐ[K] E.FunctionField` with the norm formula, a cyclic kernel of
  order `N`, and any `data : ModularCurve.ModularPolynomialData N`:
  `(data.Φ.map (eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0`.

  This is the row's wire test: it assembles D-6's countable descent (to an intermediate
  `K₀`), the base-change column (D-5), the gate producer, the `ℂ` embedding
  (`Field.nonempty_ringHom_complex_of_countable`), S-4's `jLattice` form and S-2's index
  form into one proof about an arbitrary `K`.

  The capstone is **assembly**.  Every mathematical premise is ported or in the row:
  D-6's headline (`Isogeny/TwoCurveDescent.lean`), D-5's base-change headline
  (`Isogeny/KernelBaseChange.lean`), the gate producer
  (`WeierstrassCurve/GenusOnePlaceGateCentred.lean`),
  `WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain`,
  `hasPrincipalDivisors_functionField`, `AlgebraicCurve.normFormulaAlong`, the two SC
  leaves (`Elliptic/PeriodPair/VariableChange.lean`,
  `FieldTheory/NonemptyRingHomComplex.lean`), S-2's
  `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`,
  S-3's `PeriodPair.jLattice_scale` (pin-`private`, re-derived `private` here because a
  `private` port prelude name does not survive a module boundary), and S-4's
  `ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic`.  The new
  lines are the `conjSeam` packaging, the char-`0` separability/norm-formula bridges, and
  the `IsAlgClosed.lift`/base-change wiring.

  Pin source, `anthropics/fermats-last-theorem@aa2d8b3`:

    `P2M/Sol/S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean`
    (415 lines); statement authority
    `Theorems/Thm_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean`.

  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward.lean>

  **What is imported, not re-proved.**  The pin's inlined `PeriodPair` scale / `G_scale` /
  `discriminant_scale` / `jLattice_scale` prelude (`:45–129`) is the port's
  `Elliptic/PeriodPair/{Lattice,PrimCosetReps}.lean`; only `jLattice_scale` needs
  re-deriving here, because the port keeps it `private` in S-3's module.  The three row
  modules and the two SC leaves are imported.

  **Collision note.**  This module holds the gate producer
  (`GenusOnePlaceGateCentred.lean` → `Place/RRSpace.lean`) **and**
  `IsogenyEndDatum/Engine.lean` in one environment.  That is legal only because
  `Engine.instInfinitePlace` was made `private` (commits `23dbdf3`/`073307e`), so its name
  is mangled and cannot clash with the pin's `scoped instance instInfinitePlace` in
  `Place/RRSpace.lean`.  The collision pre-flight confirmed this green.

  **Not transcribed.**  The pin's `p2m_*` scaffolding, its `attribute [-instance]` /
  `attribute [-simp]` blocks, and its heartbeat bumps (`synthInstance.maxHeartbeats
  1600000`, `maxHeartbeats 16000000` — the port's frozen cap is 4,000,000).
-/
import FLTForHuman.Elliptic.PeriodPair.LatticeIndex
import FLTForHuman.Elliptic.PeriodPair.PrimCosetReps
import FLTForHuman.Elliptic.PeriodPair.HoloLift
import FLTForHuman.Elliptic.PeriodPair.VariableChange
import FLTForHuman.FieldTheory.NonemptyRingHomComplex
import FLTForHuman.ModularCurve.ModularPolynomialE4Cube
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred
import FLTForHuman.WeierstrassCurve.Isogeny.TwoCurveDescent
import FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange
import FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer
import FLTForHuman.WeierstrassCurve.Isogeny.VariableChangeAlgEquiv
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.Place.Dictionary

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open scoped WeierstrassCurve.Affine

namespace PeriodPair

/-- Pin `PeriodPair.jLattice_scale` (private): `jLattice` is scale-invariant.  S-3's
`PrimCosetReps.lean` carries the same lemma `private`, and a `private` declaration is not
reachable across a module boundary, so the capstone re-derives it here from the ported
`PeriodPair.g₂_scale` and `PeriodPair.discriminant_scale`. -/
private theorem jLattice_scale (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).jLattice = L.jLattice := by
  have hα : ((α : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ α.ne_zero)
  have hg₂ : (L.scale α).g₂ ^ 3 = ((α : ℂ) ^ 12)⁻¹ * L.g₂ ^ 3 := by
    rw [PeriodPair.g₂_scale, mul_pow, inv_pow, ← pow_mul]
  unfold PeriodPair.jLattice
  rw [PeriodPair.discriminant_scale, hg₂, mul_left_comm (1728 : ℂ), mul_div_mul_left _ _ hα]

end PeriodPair

namespace WeierstrassCurve.Affine

section ConjHelpers

variable {K : Type*} [Field K]
variable {E E' F F' : WeierstrassCurve.Affine K}

/-- Pin `F4Proof.conjSeam`: conjugate the along-map `ι : E' → E` by the variable-change
function-field equivalences `eE : F ≃ E` and `eE' : F' ≃ E'`. -/
def conjSeam
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) :
    F'.FunctionField →ₐ[K] F.FunctionField :=
  (eE.symm.toAlgHom.comp ι).comp eE'.toAlgHom

/-- Pin `F4Proof.conjSeam_apply`. -/
theorem conjSeam_apply (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (x : F'.FunctionField) :
    conjSeam eE eE' ι x = eE.symm (ι (eE' x)) := rfl

/-- Pin `F4Proof.conjSeam_isIntegral`. -/
theorem conjSeam_isIntegral
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) :
    (conjSeam eE eE' ι).toRingHom.IsIntegral :=
  RingHom.IsIntegral.trans eE'.toAlgHom.toRingHom (eE.symm.toAlgHom.comp ι).toRingHom
    (RingHom.isIntegral_of_surjective _ eE'.surjective)
    (RingHom.IsIntegral.trans ι.toRingHom eE.symm.toAlgHom.toRingHom hι
      (RingHom.isIntegral_of_surjective _ eE.symm.surjective))

/-- Pin `F4Proof.conjSeam_finiteAlong`. -/
theorem conjSeam_finiteAlong
    (eE : F.FunctionField ≃ₐ[K] E.FunctionField)
    (eE' : F'.FunctionField ≃ₐ[K] E'.FunctionField)
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    FiniteAlong K (conjSeam eE eE' ι) := by
  have hfin' : RingHom.Finite ι.toRingHom := hfin
  have h1 : RingHom.Finite eE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE'.surjective
  have h2 : RingHom.Finite eE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ eE.symm.surjective
  have hcomp : RingHom.Finite (conjSeam eE eE' ι).toRingHom :=
    RingHom.Finite.comp (g := (eE.symm.toAlgHom.comp ι).toRingHom)
      (RingHom.Finite.comp (g := eE.symm.toAlgHom.toRingHom) h2 hfin') h1
  exact hcomp

end ConjHelpers

section AutoNorm

variable {K : Type*} [Field K] [CharZero K]

/-- Pin `F4Proof.separableAlong_of_charZero`: over a characteristic-`0` base, a finite
along-map is separable. -/
theorem separableAlong_of_charZero {E E' : WeierstrassCurve.Affine K}
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    SeparableAlong K ι := by
  letI := algebraAlong ι
  haveI := isScalarTower_along ι
  haveI : Module.Finite E'.FunctionField E.FunctionField := hfin
  haveI : CharZero E'.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
  show Algebra.IsSeparable E'.FunctionField E.FunctionField
  infer_instance

/-- Pin `F4Proof.normFormulaAlong_of_charZero`: over a characteristic-`0` base, the norm
formula is automatic for a finite along-map. -/
theorem normFormulaAlong_of_charZero {E E' : WeierstrassCurve.Affine K}
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hfin : FiniteAlong K ι) :
    NormFormulaAlong K ι hfin := by
  haveI : HasPrincipalDivisors K E.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField E
  haveI : CharZero E'.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap K E'.FunctionField).injective
  exact AlgebraicCurve.normFormulaAlong ι hfin (separableAlong_of_charZero ι hfin)

end AutoNorm

/-- Pin `F4Proof.map_eval_map_Φ`: the modular polynomial's `Φ`-evaluation commutes with a
ring homomorphism. -/
theorem map_eval_map_Φ {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {N : ℕ} [NeZero N] (data : ModularCurve.ModularPolynomialData N) (a b : R) :
    φ ((data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom R) a)).eval b) =
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom S) (φ a))).eval (φ b) := by
  rw [Polynomial.eval_map, Polynomial.eval_map, Polynomial.hom_eval₂]
  congr 1
  refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
  simp

/-- Pin `F4Proof.isElliptic_map`: ellipticity is preserved by a ring homomorphism. -/
theorem isElliptic_map {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
    [W.IsElliptic] (f : R →+* S) : (W.map f).IsElliptic :=
  ⟨by rw [WeierstrassCurve.map_Δ]; exact (W.isUnit_Δ).map f⟩

/-- Pin `F4Proof.j_eq_div`: the `j`-invariant is `c₄³ / Δ` for an elliptic curve. -/
theorem j_eq_div {F : Type*} [Field F] (W : WeierstrassCurve F) [W.IsElliptic] :
    W.j = W.c₄ ^ 3 / W.Δ := by
  rw [WeierstrassCurve.j, ← WeierstrassCurve.coe_Δ', div_eq_inv_mul, Units.val_inv_eq_inv_val]

/-- Pin `F4Proof.instIsEllipticWeierstrassCurve`: the Weierstrass curve attached to a
period lattice is elliptic.  `scoped`, as at the pin (and the checker does not read
`scoped instance` declarations on either side). -/
scoped instance instIsEllipticWeierstrassCurve (L : PeriodPair) : L.weierstrassCurve.IsElliptic :=
  ⟨isUnit_iff_ne_zero.mpr (PeriodPair.discriminant_ne_zero L).weierstrassCurve_Δ_ne_zero⟩

/-- Pin `F4Proof.jLattice_eq_j`: the lattice `j`-invariant is the Weierstrass `j` of the
attached curve. -/
theorem jLattice_eq_j (L : PeriodPair) : L.jLattice = L.weierstrassCurve.j := by
  rw [PeriodPair.jLattice_eq_c₄_pow_three_div_Δ, j_eq_div]

/-- Pin `F4Proof.complexCase`: the `ℂ` case.  Change variables to a lattice curve, build
the gate instances from the producer, transport the cyclic-kernel hypothesis across the
variable change via `conjSeam`, and read the vanishing off S-4's `jLattice` headline. -/
theorem complexCase (E E' : WeierstrassCurve.Affine ℂ) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[ℂ] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι)
    (hN : NormFormulaAlong ℂ ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ) E.j)).eval E'.j = 0 := by
  obtain ⟨L, C, hE⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E : WeierstrassCurve ℂ)
  obtain ⟨L', C', hE'⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq (E' : WeierstrassCurve ℂ)
  subst hE hE'

  haveI : IsDedekindDomain L.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L.weierstrassCurve
  haveI : IsDedekindDomain L'.weierstrassCurve.toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain L'.weierstrassCurve
  haveI : HasPrincipalDivisors ℂ L.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField L.weierstrassCurve.toAffine
  haveI : HasPrincipalDivisors ℂ L'.weierstrassCurve.toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField L'.weierstrassCurve.toAffine
  obtain ⟨gL, hcL, haL⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
      (W := L.weierstrassCurve.toAffine)
  obtain ⟨gL', hcL', haL'⟩ :=
    WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
      (W := L'.weierstrassCurve.toAffine)
  letI := gL
  letI := gL'
  haveI := hcL
  haveI := haL
  haveI := hcL'
  haveI := haL'

  obtain ⟨eE⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L.weierstrassCurve C
  obtain ⟨eE'⟩ := WeierstrassCurve.nonempty_functionField_algEquiv_of_variableChange L'.weierstrassCurve C'

  have hι'' := conjSeam_isIntegral eE eE' ι hι
  have hfin'' := conjSeam_finiteAlong eE eE' ι hfin
  have hN'' : NormFormulaAlong ℂ (conjSeam eE eE' ι) hfin'' := normFormulaAlong_of_charZero _ hfin''

  obtain ⟨hcyc'', hcard''⟩ :=
    WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_algEquiv_conj
      (C • L.weierstrassCurve).toAffine (C' • L'.weierstrassCurve).toAffine
      L.weierstrassCurve.toAffine L'.weierstrassCurve.toAffine
      ι hι hfin hN eE eE' (conjSeam eE eE' ι) (fun x => by
        rw [conjSeam_apply, AlgEquiv.apply_symm_apply]) hι'' hfin'' hN'' hcyc
  rw [hcard] at hcard''

  obtain ⟨β, hsub, hidx, hcycq⟩ :=
    PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
      L L' (conjSeam eE eE' ι) hι'' hfin'' hN'' N hcyc'' hcard''

  have hroot := ModularCurve.ModularPolynomialData.eval_jLattice_eq_zero_of_isAddCyclic
    N data L (L'.scale β) hsub hidx hcycq
  rw [PeriodPair.jLattice_scale, jLattice_eq_j, jLattice_eq_j] at hroot

  have hj : WeierstrassCurve.j (C • L.weierstrassCurve) = L.weierstrassCurve.j :=
    WeierstrassCurve.variableChange_j _ _
  have hj' : WeierstrassCurve.j (C' • L'.weierstrassCurve) = L'.weierstrassCurve.j :=
    WeierstrassCurve.variableChange_j _ _
  have hjE : (show WeierstrassCurve.Affine ℂ from C • L.weierstrassCurve).j = L.weierstrassCurve.j := hj
  have hjE' : (show WeierstrassCurve.Affine ℂ from C' • L'.weierstrassCurve).j = L'.weierstrassCurve.j := hj'
  rw [hjE, hjE']
  exact hroot

/-- Pin `F4Proof.solution0`: the general-`K` case.  Descend to a countable intermediate
field `K₀` (D-6), base change to `AlgebraicClosure K₀` and then to `ℂ` along an embedding
`K₀ →+* ℂ` (`Field.nonempty_ringHom_complex_of_countable`), build the gate instances from
the producer at each stage, and apply `complexCase`. -/
theorem solution0
    {K : Type} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  obtain ⟨K₀, hK₀, E₀, E₀', hE₀, hE₀', hE, hE', hEb, hEb', ι₀, hι₀, hfin₀, H⟩ :=
    WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
      E E' ι hι hfin hN N hcyc hcard
  haveI := hE₀
  haveI := hE₀'
  haveI := hEb
  haveI := hEb'
  haveI : Countable K₀ := hK₀
  haveI : CharZero K₀ := (algebraMap K₀ K).charZero
  haveI : CharZero (AlgebraicClosure K₀) :=
    charZero_of_injective_algebraMap (algebraMap K₀ (AlgebraicClosure K₀)).injective
  haveI : DecidableEq (AlgebraicClosure K₀) := Classical.decEq _

  haveI : IsDedekindDomain (E₀.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : IsDedekindDomain (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀) (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  haveI : HasPrincipalDivisors (AlgebraicClosure K₀) (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g₁, c₁, a₁⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀.baseChange (AlgebraicClosure K₀)).toAffine)
  obtain ⟨g₂, c₂, a₂⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀'.baseChange (AlgebraicClosure K₀)).toAffine)
  letI := g₁
  letI := g₂
  haveI := c₁
  haveI := a₁
  haveI := c₂
  haveI := a₂
  have hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀ := normFormulaAlong_of_charZero ι₀ hfin₀
  obtain ⟨hcyc₀, hcard₀⟩ := H hN₀

  obtain ⟨φ₀⟩ := Field.nonempty_ringHom_complex_of_countable K₀
  letI : Algebra K₀ ℂ := φ₀.toAlgebra
  haveI : Module.IsTorsionFree K₀ ℂ :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr φ₀.injective
  haveI : Module.IsTorsionFree K₀ (AlgebraicClosure K₀) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (algebraMap K₀ (AlgebraicClosure K₀)).injective
  let σ : AlgebraicClosure K₀ →ₐ[K₀] ℂ := IsAlgClosed.lift
  haveI : (E₀.baseChange ℂ).IsElliptic := isElliptic_map E₀ _
  haveI : (E₀'.baseChange ℂ).IsElliptic := isElliptic_map E₀' _

  haveI : IsDedekindDomain (E₀.baseChange ℂ).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : IsDedekindDomain (E₀'.baseChange ℂ).toAffine.CoordinateRing :=
    WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain _
  haveI : HasPrincipalDivisors ℂ (E₀.baseChange ℂ).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  haveI : HasPrincipalDivisors ℂ (E₀'.baseChange ℂ).toAffine.FunctionField :=
    WeierstrassCurve.Affine.hasPrincipalDivisors_functionField _
  obtain ⟨g₃, c₃, a₃⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀.baseChange ℂ).toAffine)
  obtain ⟨g₄, c₄, a₄⟩ := WeierstrassCurve.Affine.exists_genusOnePlaceGate_isCentred_and_abelTheorem
    (W := (E₀'.baseChange ℂ).toAffine)
  letI := g₃
  letI := g₄
  haveI := c₃
  haveI := a₃
  haveI := c₄
  haveI := a₄

  obtain ⟨ι₁, hι₁, hfin₁, H₁⟩ :=
    WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
      K₀ E₀ E₀' (AlgebraicClosure K₀) ℂ σ ι₀ hι₀ hfin₀ hN₀ N hcyc₀ hcard₀
  have hN₁ : NormFormulaAlong ℂ ι₁ hfin₁ := normFormulaAlong_of_charZero ι₁ hfin₁
  obtain ⟨hcyc₁, hcard₁⟩ := H₁ hN₁

  have hC := complexCase (E₀.baseChange ℂ).toAffine (E₀'.baseChange ℂ).toAffine
    ι₁ hι₁ hfin₁ hN₁ N hcyc₁ hcard₁ data

  have hjC : WeierstrassCurve.j (E₀.baseChange ℂ).toAffine = φ₀ E₀.j := E₀.map_j φ₀
  have hjC' : WeierstrassCurve.j (E₀'.baseChange ℂ).toAffine = φ₀ E₀'.j := E₀'.map_j φ₀
  rw [hjC, hjC', ← map_eval_map_Φ] at hC
  have hK₀ : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K₀) E₀.j)).eval E₀'.j = 0 :=
    φ₀.injective (hC.trans (map_zero φ₀).symm)

  subst hE hE'
  have hjK : WeierstrassCurve.j (show WeierstrassCurve.Affine K from E₀.map (algebraMap K₀ K)) =
      algebraMap K₀ K E₀.j := E₀.map_j _
  have hjK' : WeierstrassCurve.j (show WeierstrassCurve.Affine K from E₀'.map (algebraMap K₀ K)) =
      algebraMap K₀ K E₀'.j := E₀'.map_j _
  rw [hjK, hjK', ← map_eval_map_Φ, hK₀, map_zero]

/-- Pin `solution`: the capstone statement at the pin's root name. -/
theorem solution
    (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 :=
  solution0 E E' ι hι hfin hN N hcyc hcard data

end WeierstrassCurve.Affine

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

/-- The row-S capstone at the statement authority's fully qualified name. -/
theorem WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    (K : Type) [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    (data : ModularCurve.ModularPolynomialData N) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom K) E.j)).eval E'.j = 0 :=
  WeierstrassCurve.Affine.solution K E E' ι hι hfin hN N hcyc hcard data

end
