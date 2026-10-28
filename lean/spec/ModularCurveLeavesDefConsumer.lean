/-
  Consumer specification for the **leaves' definition wave** (`SET-LEAVESDEF.md`): the deferred
  Defs that the leaves programme is written over.

  WHAT THIS FILE IS
  -----------------
  Written-down *uses* of the wave's definitions, composed across modules with a real consumer on
  the other side.  Not part of any library (`lake build` does not see `spec/`); run by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveLeavesDefConsumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [heckedata] ZONE A — the `HeckeData` tower built by `CohCarrier.hdata` from the cohomological
                Hecke family: `opAlgHom` on a generator, `toMLₒ`'s restriction and the `MLAt` type.
    [petersson] ZONE B — the Petersson inner product at `Γ₀(N)`: the two `_gamma0` `rfl` lemmas
                against the port's `PeriodOf` general-`Γ` forms.
    [phompair]  ZONE C — the period-pair dictionary: `periodHomPair` applied to a pair of cusp
                forms, and `charInvolution`'s involution law.
    [pic0]      ZONE D — the `Pic0` congruence: `Pic0.congr` on a degree-zero divisor class and the
                principal-subgroup compatibility.
    [place]     ZONE E — the complex-place dictionary: `pt_smul_of_mem` and the `Γ₀(N)` realisation.
    [x0]        ZONE F — the q-expansion algebra homomorphism `qExpandAlgHomC` and its `_apply`.
    [torsion]   ZONE G — `JH.torsionGaloisRep`'s two laws.
-/

import FLTForHuman.ModularForms.CohCarrier.HeckeData
import FLTForHuman.ModularForms.CohCarrier.Inst
import FLTForHuman.ModularForms.EichlerShimura.Petersson
import FLTForHuman.ModularCurve.PeriodHomPair
import FLTForHuman.AlgebraicCurve.Pic0Congr
import FLTForHuman.ModularCurve.ComplexPlaceDictionaryOf
import FLTForHuman.ModularCurve.X0.FunctionFieldFull
import FLTForHuman.ModularCurve.XH.FunctionField

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open scoped MatrixGroups ModularForm

namespace LeavesDefConsumer

/-! ## Zone A — `[heckedata]` the `HeckeData` tower over the cohomological Hecke family -/

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {S : Set ℕ}
variable {𝒪 : Type} [CommRing 𝒪] {k : Type} [Field k] [Algebra 𝒪 k]
variable (hcomm : ∀ g h : CohCarrier.Gen M S,
  CohCarrier.opFamily M H S 𝒪 g * CohCarrier.opFamily M H S 𝒪 h =
    CohCarrier.opFamily M H S 𝒪 h * CohCarrier.opFamily M H S 𝒪 g)

/-- The leaves' `pair_*` rows build a `CohCarrier.HeckeData` from the cohomological family.  The
construction itself is cheap; *projecting* `opAlgHom`/`toMLₒ` on a `hdata`-defined datum is not (the
`FreeAlg` field has to be unfolded through the structure literal — over 200k heartbeats, FR-0063),
so the zone below states the API over an abstract datum and keeps the construction as its own use. -/
example (θbar : CohCarrier.Gen M S → k) :
    CohCarrier.HeckeData 𝒪 (CohCarrier.H1 M H 𝒪) k :=
  CohCarrier.hdata M H S 𝒪 k hcomm θbar

variable (D : CohCarrier.HeckeData 𝒪 (CohCarrier.H1 M H 𝒪) k)

omit [NeZero M] in
theorem hdata_opAlgHom_X (g : D.Gen) :
    D.opAlgHom (MvPolynomial.X g) = D.op g :=
  CohCarrier.HeckeData.opAlgHom_X D g

omit [NeZero M] in
theorem hdata_toMLo_apply (v : CohCarrier.H1 M H 𝒪) :
    D.toMLₒ v = D.toML v :=
  CohCarrier.HeckeData.toMLₒ_apply D v

/-! ## Zone B — `[petersson]` the Petersson inner product at `Γ₀(N)` -/

theorem peterssonOf_eq_petersson {N : ℕ} {k : ℤ}
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.peterssonOf (CongruenceSubgroup.Gamma0 N) f g = CuspForm.petersson f g :=
  CuspForm.peterssonOf_gamma0 f g

/-! ## Zone C — `[phompair]` the period-pair dictionary -/

theorem periodHomPair_add {N : ℕ}
    (f f' g g' : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N)) 2) :
    ModularCurve.periodHomPair N (f + f', g + g') =
      ModularCurve.periodHomPair N (f, g) + ModularCurve.periodHomPair N (f', g') :=
  map_add (ModularCurve.periodHomPair N) (f, g) (f', g')

/-- `charInvolution` is an involution on the character group of `Γ₀(N)`. -/
theorem charInvolution_involution {N : ℕ} {R : Type*} [Semiring R] {A : Type*}
    [AddCommGroup A] [Module R A] (φ : Additive ↥(CongruenceSubgroup.Gamma0 N) →+ A) :
    ModularCurve.Period.charInvolution N R A (ModularCurve.Period.charInvolution N R A φ) = φ :=
  ModularCurve.Period.charInvolution_charInvolution N R A φ

/-! ## Zone D — `[pic0]` the `Pic0` congruence -/

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem pic0_congr_map_principal (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) :
    AddSubgroup.map (AlgebraicCurve.Pic0.degZeroCongr e he).toAddMonoidHom
        (AlgebraicCurve.Divisor.principal.addSubgroupOf AlgebraicCurve.Divisor.degZero) =
      AlgebraicCurve.Divisor.principal.addSubgroupOf AlgebraicCurve.Divisor.degZero :=
  AlgebraicCurve.Pic0.map_principal_degZeroCongr e he

theorem pic0_congr_apply_zero (e : F ≃+* F')
    (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a) :
    AlgebraicCurve.Pic0.congr e he 0 = 0 :=
  map_zero _

/-! ## Zone E — `[place]` the complex-place dictionary -/

theorem complexPlace_pt_smul {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}
    (D : ModularCurve.ComplexPlaceDictionaryOf Γ F₀) {γ : Matrix.SpecialLinearGroup (Fin 2) ℤ}
    (hγ : γ ∈ Γ) (τ : UpperHalfPlane) :
    D.pt (γ • τ) = D.pt τ :=
  D.pt_smul_of_mem hγ τ

/-! ## Zone F — `[x0]` the q-expansion algebra homomorphism -/

theorem qExpandAlgHomC_apply' (K : Type*) [Field K] (N : ℕ) [NeZero N]
    (f : LaurentSeries K) :
    ModularCurve.qExpandAlgHomC K N f = ModularCurve.qExpand K N f :=
  ModularCurve.qExpandAlgHomC_apply K N f

/-! ## Zone G — `[torsion]` the `JH` torsion Galois representation -/

theorem torsionGaloisRep_apply_eq_smul {M : ℕ} [NeZero M] (H : Subgroup (ZMod M)ˣ) {n : ℕ}
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) n) :
    ModularCurve.JH.torsionGaloisRep M H n σ x =
      (ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField M H) σ • x :
        AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) n) :=
  ModularCurve.JH.torsionGaloisRep_apply (M := M) (H := H) σ x

end LeavesDefConsumer
