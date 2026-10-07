/-
The kernel base change of an isogeny: cyclicity of the kernel descends along a base
change of the ground field, and the base-changed datum exists. This is set **D-5** of
`topics/velu/WORKORDER-P2-basechange.md`, ported as **one** module for the two pin
files

  `P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean` (5,357)
  `P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean` (5,338)

which share 163 of their 176 declarations (4,926 removable lines). The two headlines
are the `Theorems/` wrappers

  `WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom`
  `WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward`

(the wrapper is the statement authority; its binders are spelled verbatim, including the
`Type u`/`Type` asymmetry). Everything these two files share with the already-ported
prelude is **imported, not re-proved**: the point-pullback/tensor base-change block is
D-1's `Isogeny/BaseChange.lean` (at its prefix-stripped names), the `IsogenyEndDatum` /
place vocabulary is `IsogenyEndDatum/Engine.lean`, the kernel-cardinality bridge is
`Isogeny/NatCard.lean` (`kw_fdn2_qephod_hend7_pmopKerCard_proved` is *not* re-declared —
the name belongs to that module), and the `PeriodPair` uniformization prelude is
`Elliptic/PeriodPair/` (with the `kw_toPointHom` promotion set of D-5 §1.5 landed in
`Elliptic/PeriodPair/Uniformization.lean`).

What is written here is what the pin calls the *seam* and the *silo tail*:

* `ModularCurve.KwD5BetweenCurvesHoloLift` (byte-identical in all five pin copies),
* `ModularCurve.KwD5BetweenCurvesFFSeamBaseChange` and the `kw_surge_hgf4_bc*` /
  `kw_surge_hgf4_χE_*` / `kw_surge_hgf4_pmop_naturality` / `kw_surge_hgf4_hBC_proved`
  tensor transport that proves it,
* `ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed` and the
  `kw_surgehgf4_hfgkd_ktd_*` block that proves it,
* the two headlines, assembled by `hBC_s17` / `kerTransport_s17`.

Only proof bodies are adapted to mathlib `v4.34.0`; the pin's `maxHeartbeats` bumps are
not transcribed (the port's frozen cap is 4,000,000).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.BaseChange
import FLTForHuman.WeierstrassCurve.Isogeny.KernelCyclicTransfer
import FLTForHuman.WeierstrassCurve.Isogeny.NatCard
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Vocabulary
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.Elliptic.TorsionCardLight

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option linter.deprecated false
set_option linter.unnecessarySimpa false

noncomputable section

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve
open WeierstrassCurve.Affine.CoordinateRing
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct


universe u

/-! ## The `ℤ`-torsion packaging used by the `3`-torsion argument

The pin's copy of `nonempty_pointTorsionBy_zmod`; the port has no other home for it. -/


theorem WeierstrassCurve.nonempty_pointTorsionBy_zmod {K : Type*} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (W : WeierstrassCurve K) [W.IsElliptic] {n : ℕ} (hn : 1 ≤ n) :
    Nonempty (↥(Submodule.torsionBy ℤ W.toAffine.Point (n : ℤ)) ≃+ (Fin 2 → ZMod n)) := by
  obtain ⟨e⟩ := AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq
    (A := W.toAffine.Point) (n := n) (by omega)
    (fun d hd => WeierstrassCurve.card_torsionBy_eq_sq_of_isAlgClosed W (n := d)
      (by exact_mod_cast (Nat.pos_of_dvd_of_pos hd (by omega)).ne') two_ne_zero)
  exact ⟨e.symm.trans (LinearEquiv.piFinTwo ℤ (fun _ : Fin 2 => ZMod n)).toAddEquiv.symm⟩

/-! ## The `KwD5BetweenCurvesHoloLift` seam -/

namespace ModularCurve

attribute [local instance] Classical.propDecidable

def KwD5BetweenCurvesHoloLift : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι''),
    ∃ (F : ℂ → ℂ), Differentiable ℂ F ∧ F 0 ∈ L'.lattice ∧
      ∀ z, L'.toPointHom (F z)
        = (pointMapOfPushforward ι'' hι'' hfin''
            (normFormulaAlong_of_elliptic ι'' hfin'')) (L.toPointHom z)


/-! ## `KwD5BetweenCurvesFFSeamBaseChange` -/

def KwD5BetweenCurvesFFSeamBaseChange : Prop :=
  ∀ (R₀ : Type) [Field R₀]
    (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F F' : Type) [Field F] [Field F'] [Algebra R₀ F] [Algebra R₀ F']
    [DecidableEq F] [DecidableEq F'] [IsAlgClosed F] [IsAlgClosed F']
    [CharZero F] [CharZero F']
    [(E₀⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F).toAffine] [(E₀'⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F).toAffine] [(E₀⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F').toAffine] [(E₀'⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F').toAffine]
    (_σ : F →ₐ[R₀] F')
    (ι₀ : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀)
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀))) = N →
    ∃ (ι₁ : (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      IsAddCyclic (AddMonoidHom.ker
        (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) ∧
      Nat.card (AddMonoidHom.ker
        (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) = N

/-! ## The `kw_surge_hgf4_bc*` tensor transport -/

theorem kw_surge_hgf4_hBC_axiomAnchor : True := by
  have h1 : (True ∧ True) = True := propext (by simp)
  have h2 := Classical.choice ⟨()⟩
  have h3 := Quot.sound (r := fun _ _ : Unit => True) (a := ()) (b := ()) trivial
  trivial

section BetweenCurvesTensor

variable {R₀ : Type u} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F).toAffine] [(E₀'⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F).toAffine] [(E₀⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F').toAffine] [(E₀'⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F').toAffine]
variable (ι₀ : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

attribute [local instance] Algebra.TensorProduct.rightAlgebra

def kw_surge_hgf4_bcTensorIota :
    (E₀'⁄F).toAffine.FunctionField ⊗[F] F' →ₐ[F] (E₀⁄F).toAffine.FunctionField ⊗[F] F' :=
  Algebra.TensorProduct.map ι₀ (AlgHom.id F F')

theorem kw_surge_hgf4_bcTensorIota_tmul (a : (E₀'⁄F).toAffine.FunctionField) (c : F') :
    kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ (a ⊗ₜ[F] c) = (ι₀ a) ⊗ₜ[F] c := by
  simp [kw_surge_hgf4_bcTensorIota, Algebra.TensorProduct.map_tmul]

theorem kw_surge_hgf4_bcTensorIota_injective :
    Function.Injective (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι₀.toLinearMap ι₀.injective

variable [IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F')]
variable [IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')]

def kw_surge_hgf4_bcTensorFracIota :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →+* FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
    (L := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))
    (kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀)

theorem kw_surge_hgf4_bcTensorFracIota_algebraMap
    (t : (E₀'⁄F).toAffine.FunctionField ⊗[F] F') :
    kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ t)
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
          (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀ t) := by
  unfold kw_surge_hgf4_bcTensorFracIota IsFractionRing.map
  exact IsLocalization.map_eq
    (T := nonZeroDivisors ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ t

theorem kw_surge_hgf4_bcTensorIota_finite (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom.Finite :=
  RingHom.Finite.tensorProductMap (f := ι₀) hfin₀ (g := AlgHom.id F F') (RingHom.Finite.id F')

def kw_surge_hgf4_bcTensorFracIotaAlg :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →ₐ[F'] FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  { kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ with
    commutes' := fun c => by
      show kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ (algebraMap F' _ c)
          = algebraMap F' _ c
      rw [IsScalarTower.algebraMap_apply F' ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply,
        kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀,
        kw_surge_hgf4_bcTensorIota_tmul, map_one,
        IsScalarTower.algebraMap_apply F' ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply] }

def kw_surge_hgf4_bcIota₁ :
    (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField :=
  let ψE := functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneral E₀' F F'
  (ψE.symm.toAlgHom.comp (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀)).comp
    ψE'.toAlgHom

theorem kw_surge_hgf4_bcTensorFracIotaSeam (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).Finite ∧
    (letI := (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀).toAlgebra
     @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
       (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = finrankAlong F ι₀ := by
  classical
  let FF := (E₀⁄F).toAffine.FunctionField
  let FF' := (E₀'⁄F).toAffine.FunctionField
  let T := (E₀⁄F).toAffine.FunctionField ⊗[F] F'
  let T' := (E₀'⁄F).toAffine.FunctionField ⊗[F] F'
  let FrT := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
  let FrT' := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
  let ιT : T' →+* T := (kw_surge_hgf4_bcTensorIota E₀ E₀' F F' ι₀).toRingHom
  let ιFr : FrT' →+* FrT := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hιT_inj : Function.Injective ιT :=
    kw_surge_hgf4_bcTensorIota_injective E₀ E₀' F F' ι₀
  have hιT_fin : ιT.Finite := kw_surge_hgf4_bcTensorIota_finite E₀ E₀' F F' ι₀ hfin₀
  have hιFr_am : ∀ t : T', ιFr (algebraMap T' FrT' t) = algebraMap T FrT (ιT t) :=
    kw_surge_hgf4_bcTensorFracIota_algebraMap E₀ E₀' F F' ι₀

  letI algι : Algebra FF' FF := ι₀.toRingHom.toAlgebra
  letI modι : Module FF' FF := Algebra.toModule
  have hsmul_ι : ∀ (c : FF') (x : FF), c • x = ι₀ c * x := fun c x => rfl
  haveI hfinFF : Module.Finite FF' FF := hfin₀
  haveI hfreeFF : Module.Free FF' FF := Module.Free.of_divisionRing FF' FF
  let D := finrankAlong F ι₀
  let b : Module.Basis (Fin D) FF' FF := Module.finBasisOfFinrankEq FF' FF (n := D) rfl
  have hrepr_mul : ∀ (c : FF') (x : FF) (j : Fin D),
      b.repr (ι₀ c * x) j = c * b.repr x j := fun c x j => by
    rw [← hsmul_ι, map_smul, Finsupp.smul_apply, smul_eq_mul]
  let e : Fin D → T := fun i => (b i) ⊗ₜ[F] (1 : F')
  let bFr : Fin D → FrT := fun i => algebraMap T FrT (e i)

  have hspanT : ∀ t : T, ∃ c : Fin D → T', t = ∑ i, ιT (c i) * e i := by
    intro t
    induction t using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | add x y hx hy =>
      obtain ⟨cx, hx⟩ := hx; obtain ⟨cy, hy⟩ := hy
      exact ⟨cx + cy, by simp only [Pi.add_apply, map_add, add_mul,
        Finset.sum_add_distrib, ← hx, ← hy]⟩
    | tmul a c =>
      refine ⟨fun i => (b.repr a i) ⊗ₜ[F] c, ?_⟩
      have hb_sum : a = ∑ i, ι₀ (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_ι, map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_ι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι₀ (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            show (ι₀ (b.repr a i) * b i) ⊗ₜ[F] c = ιT ((b.repr a i) ⊗ₜ[F] c) * e i
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι₀ (b.repr a i)) ⊗ₜ[F] c from
                  kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]

  have hliT : ∀ c : Fin D → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF' :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF' f) x j
          rwa [ι₀.commutes] at h }
    let Ej : T →ₗ[F] T' := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T') (i : Fin D),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF') ⊗ₜ[F] c') = (ι₀ x) ⊗ₜ[F] c' from
              kw_surge_hgf4_bcTensorIota_tmul E₀ E₀' F F' ι₀ _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        show (pj (ι₀ x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF') ⊗ₜ[F] c' else 0
        rw [show pj (ι₀ x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · show b.repr (ι₀ x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp [h]
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, map_zero]
    simpa only [map_sum, hEj_key, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hc'

  have hint : ∀ s : T, s ≠ 0 → ∃ (u : T) (s₀ : T'), s₀ ≠ 0 ∧ s * u = ιT s₀ := by
    intro s hs
    obtain ⟨p, hp_monic, hp_eval⟩ : ιT.IsIntegralElem s := hιT_fin.to_isIntegral s
    obtain ⟨q, hq_eq, hq_ndvd⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p
      hp_monic.ne_zero 0
    simp only [Polynomial.C_0, sub_zero] at hq_eq hq_ndvd
    have hq0 : q.coeff 0 ≠ 0 := fun h => hq_ndvd (Polynomial.X_dvd_iff.mpr h)
    have hqs : q.eval₂ ιT s = 0 := by
      have h := hp_eval
      rw [hq_eq, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        mul_eq_zero] at h
      exact h.resolve_left (pow_ne_zero _ hs)
    have h3 : ιT (q.coeff 0) + s * (q.divX).eval₂ ιT s = 0 := by
      have h := hqs
      conv at h => lhs; rw [← Polynomial.divX_mul_X_add q]
      simpa [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X,
        Polynomial.eval₂_C, add_comm, mul_comm] using h
    exact ⟨(q.divX).eval₂ ιT s, -q.coeff 0, neg_ne_zero.mpr hq0,
      by rw [map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : Fin D → FrT', z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (map_zero ιT).symm))
    have hu_ne : u ≠ 0 := fun h => hιTs₀ (by rw [← hsu, h, mul_zero])
    obtain ⟨c, hc⟩ := hspanT (t * u)
    refine ⟨fun i => (algebraMap T' FrT' s₀)⁻¹ * algebraMap T' FrT' (c i), ?_⟩
    have hum := (map_ne_zero_iff _ (IsFractionRing.injective T FrT)).mpr hu_ne
    have hz : (algebraMap T FrT t) / (algebraMap T FrT s)
        = (algebraMap T FrT (ιT s₀))⁻¹ * algebraMap T FrT (t * u) := by
      rw [← div_eq_inv_mul, ← hsu, map_mul, map_mul,
        ← div_mul_div_comm, div_self hum, mul_one]
    rw [hz, hc, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, ← hιFr_am s₀, ← hιFr_am (c i), ← map_inv₀ ιFr, mul_assoc]

  have hliFr : ∀ d : Fin D → FrT', ∑ i, ιFr (d i) * bFr i = 0 → ∀ j, d j = 0 := by
    intro d hd j
    obtain ⟨q, hq⟩ := IsLocalization.exist_integer_multiples_of_finset
      (nonZeroDivisors T') (Finset.univ.image d)
    choose p hp using fun i => hq (d i) (Finset.mem_image_of_mem d (Finset.mem_univ i))
    have hq0 : (algebraMap T' FrT' (q : T')) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective T' FrT')).mpr (nonZeroDivisors.ne_zero q.2)
    have hp' : ∀ i, algebraMap T' FrT' (p i) = algebraMap T' FrT' (q : T') * d i := fun i => by
      rw [hp i, Algebra.smul_def]
    have hd' : algebraMap T FrT (∑ i, ιT (p i) * e i) = 0 := by
      have h1 : ∑ i, ιFr (algebraMap T' FrT' (q : T')) * (ιFr (d i) * bFr i) = 0 := by
        rw [← Finset.mul_sum, hd, mul_zero]
      rw [map_sum, ← h1]; refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, ← hιFr_am (p i), ← mul_assoc, ← map_mul, ← hp' i]
    have hpj : p j = 0 :=
      hliT p ((IsFractionRing.injective T FrT) (by simpa using hd')) j
    have hthis : algebraMap T' FrT' (q : T') * d j = 0 := by
      rw [← hp' j, hpj, map_zero]
    exact (mul_eq_zero.mp hthis).resolve_left hq0

  letI algFr : Algebra FrT' FrT := ιFr.toAlgebra
  letI modFr : Module FrT' FrT := Algebra.toModule
  have hsmul_Fr : ∀ (c : FrT') (x : FrT), c • x = ιFr c * x := fun c x => rfl
  have hli_modFr : LinearIndependent FrT' bFr := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    refine hliFr g ?_ i
    simpa only [hsmul_Fr] using hg
  have hsp_modFr : ⊤ ≤ Submodule.span FrT' (Set.range bFr) := by
    intro z _
    obtain ⟨d, hd⟩ := hspanFr z
    rw [hd]
    exact Submodule.sum_mem _ fun i _ => (hsmul_Fr (d i) (bFr i)) ▸
      Submodule.smul_mem _ (d i) (Submodule.subset_span ⟨i, rfl⟩)
  let bFr' : Module.Basis (Fin D) FrT' FrT := .mk hli_modFr hsp_modFr
  refine ⟨Module.Finite.of_basis bFr', ?_⟩
  show Module.finrank FrT' FrT = D
  rw [Module.finrank_eq_card_basis bFr', Fintype.card_fin]

theorem kw_surge_hgf4_bcIota₁_finiteAlong (hfin₀ : FiniteAlong F ι₀) :
    FiniteAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) := by
  have hFr_fin := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).1
  let ψE := functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneral E₀' F F'
  have h1 : RingHom.Finite ψE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE'.surjective
  have h2 : RingHom.Finite ψE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE.symm.surjective
  show RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
  have hcomp : (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom
      = (ψE.symm.toAlgHom.toRingHom.comp
          (kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀)).comp ψE'.toAlgHom.toRingHom := rfl
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.Finite.comp h2 hFr_fin) h1

theorem kw_surge_hgf4_bcIota₁_isIntegral (hfin₀ : FiniteAlong F ι₀) :
    (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom.IsIntegral :=
  RingHom.Finite.to_isIntegral
    (show RingHom.Finite (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀).toRingHom from
      kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀)

theorem kw_surge_hgf4_bcIota₁_finrankAlong (hfin₀ : FiniteAlong F ι₀) :
    finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀) = finrankAlong F ι₀ := by
  have _ := kw_surge_hgf4_hBC_axiomAnchor
  let ψE := functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneral E₀' F F'
  let ιFr := kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀
  have hcomm : ∀ x, ιFr (ψE' x)
      = ψE (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀ x) := fun x => by
    show ιFr (ψE' x) = ψE (ψE.symm (_))
    exact (ψE.apply_symm_apply _).symm
  calc finrankAlong F' (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀)
      = (letI := ιFr.toAlgebra
         @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
           (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule) :=
        @Algebra.finrank_eq_of_equiv_equiv
          (E₀'⁄F').toAffine.FunctionField (E₀⁄F').toAffine.FunctionField _ _
          (algebraAlong (kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀))
          _ _ _ _ ιFr.toAlgebra ψE'.toRingEquiv ψE.toRingEquiv (RingHom.ext hcomm)
    _ = finrankAlong F ι₀ := (kw_surge_hgf4_bcTensorFracIotaSeam E₀ E₀' F F' ι₀ hfin₀).2

section Naturality

variable (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀)
variable (σ : F →ₐ[R₀] F') (hσ : ∀ c, σ c = algebraMap F F' c)

local notation "χE" => functionFieldMapAlongGeneral E₀ F F'
local notation "χE'" => functionFieldMapAlongGeneral E₀' F F'
local notation "ι₁" => kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀

theorem kw_surge_hgf4_place_inv_mem_of_isUnit {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : Place K L) {z : v.toValuationSubring} (hz : IsUnit z) :
    ((z : L))⁻¹ ∈ v.toValuationSubring := by
  obtain ⟨w, hw⟩ := hz.exists_right_inv
  have hmul : (z : L) * (w : L) = 1 := by
    have h := congrArg (fun a : v.toValuationSubring => (a : L)) hw
    simpa using h
  rw [inv_eq_of_mul_eq_one_right hmul]; exact w.2

theorem kw_surge_hgf4_toAffine_map_eq (V : WeierstrassCurve R₀) :
    (V⁄F).toAffine.map (algebraMap F F') = (V⁄F').toAffine := by
  show ((V.map (algebraMap R₀ F)).map (algebraMap F F')).toAffine = (V.map (algebraMap R₀ F')).toAffine
  rw [WeierstrassCurve.map_map, ← IsScalarTower.algebraMap_eq R₀ F F']


theorem kw_surge_hgf4_χE_algebraMap_XClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (V⁄F).toAffine] [(V⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (V⁄F').toAffine] (x : F) :
    functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (XClass (V⁄F).toAffine x))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (XClass (V⁄F').toAffine (algebraMap F F' x)) := by

  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (XClass (V⁄F).toAffine x)
      = polyToFunctionField (V⁄F).toAffine X - algebraMap F (V⁄F).toAffine.FunctionField x := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (XClass (V⁄F').toAffine (algebraMap F F' x))
      = polyToFunctionField (V⁄F').toAffine X
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' x) := by
    rw [← polyToFunctionField_C, ← map_sub]; rfl
  rw [hF, hF', map_sub, functionFieldMapAlongGeneral_polyToFunctionField_X,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]


theorem kw_surge_hgf4_χE_algebraMap_YClass (V : WeierstrassCurve R₀) [V.IsElliptic]
    [(V⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (V⁄F).toAffine] [(V⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (V⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (V⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (V⁄F').toAffine] (y : F) :
    functionFieldMapAlongGeneral V F F'
        (algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
          (YClass (V⁄F).toAffine (C y)))
      = algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
          (YClass (V⁄F').toAffine (C (algebraMap F F' y))) := by
  have hF : algebraMap (V⁄F).toAffine.CoordinateRing (V⁄F).toAffine.FunctionField
      (YClass (V⁄F).toAffine (C y))
      = yGen (V⁄F).toAffine - algebraMap F (V⁄F).toAffine.FunctionField y := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  have hF' : algebraMap (V⁄F').toAffine.CoordinateRing (V⁄F').toAffine.FunctionField
      (YClass (V⁄F').toAffine (C (algebraMap F F' y)))
      = yGen (V⁄F').toAffine
          - algebraMap F' (V⁄F').toAffine.FunctionField (algebraMap F F' y) := by
    rw [YClass, map_sub, map_sub, yGen]
    congr 1
  rw [hF, hF', map_sub, functionFieldMapAlongGeneral_yGen,
    AlgHom.commutes, IsScalarTower.algebraMap_apply F F' (V⁄F').toAffine.FunctionField]

theorem kw_surge_hgf4_χE_VSR_compat {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
    (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
    (g : (E₀⁄F).toAffine.FunctionField) :
    χE g ∈ (placeOfEquation hσP.left).toValuationSubring ↔
      g ∈ (placeOfEquation hP.left).toValuationSubring := by

  have hχE_inj : Function.Injective (χE : _ →ₐ[F] _) :=
    (functionFieldMapAlongGeneral E₀ F F').injective

  classical

  have hmk (W : Affine F) : ∀ q : F[X][Y],
      algebraMap W.CoordinateRing W.FunctionField (CoordinateRing.mk W q)
        = q.eval₂ (polyToFunctionField W) (yGen W) := by
    intro q
    induction q using Polynomial.induction_on' with
    | add p r hp hr => rw [map_add, map_add, Polynomial.eval₂_add, hp, hr]
    | monomial n a =>
        simp only [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_pow,
          Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X]
        rw [← algebraMap_polynomial_eq_mk_C, ← polyToFunctionField_apply]; rfl

  have hfinσP : IsFinitePlace (placeOfEquation hσP.left) :=
    isFinitePlace_placeOfEquation hσP.left
  have hχE_polyToFF (p : F[X]) :
      χE (polyToFunctionField (E₀⁄F).toAffine p) ∈ (placeOfEquation hσP.left).toValuationSubring := by

    have h : χE (polyToFunctionField (E₀⁄F).toAffine p)
        = polyToFunctionField (E₀⁄F').toAffine (p.map (algebraMap F F')) := by
      induction p using Polynomial.induction_on' with
      | add r s hr hs => rw [map_add, map_add, Polynomial.map_add, map_add, hr, hs]
      | monomial n c =>
          rw [Polynomial.map_monomial, ← Polynomial.C_mul_X_pow_eq_monomial,
            ← Polynomial.C_mul_X_pow_eq_monomial, map_mul, map_mul, map_pow, map_pow,
            map_mul, map_pow, polyToFunctionField_C, polyToFunctionField_C,
            functionFieldMapAlongGeneral_polyToFunctionField_X, AlgHom.commutes,
            IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    rw [h, polyToFunctionField_apply]
    exact hfinσP _
  have hχE_CR_mem : ∀ a : (E₀⁄F).toAffine.CoordinateRing,
      χE (algebraMap _ _ a) ∈ (placeOfEquation hσP.left).toValuationSubring := by
    intro a
    obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [hmk (E₀⁄F).toAffine q]

    induction q using Polynomial.induction_on' with
    | add r s hr hs =>
        rw [Polynomial.eval₂_add, map_add]
        exact Subring.add_mem _ hr hs
    | monomial n p =>
        rw [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
          Polynomial.eval₂_C, Polynomial.eval₂_X, map_mul, map_pow,
          functionFieldMapAlongGeneral_yGen]
        exact Subring.mul_mem _ (hχE_polyToFF p)
          (Subring.pow_mem _ (hfinσP (CoordinateRing.mk (E₀⁄F').toAffine Y)) n)

  have hXClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.XClass (E₀⁄F').toAffine
        (algebraMap F F' x)), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.XClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.XClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert _ _))
  have hYClass_σP_mem_𝔪 : (⟨algebraMap _ _ (CoordinateRing.YClass (E₀⁄F').toAffine
        (C (algebraMap F F' y))), hfinσP _⟩ : (placeOfEquation hσP.left).toValuationSubring)
      ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    rw [Place.mem_maximalIdeal_iff_ord_pos _
      ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (CoordinateRing.YClass_ne_zero _))]
    exact (ord_placeOfEquation_pos_iff hσP.left (CoordinateRing.YClass_ne_zero _)).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hχE_mem_𝔪 : ∀ a ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y),
      (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ : (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
    intro a ha
    rw [CoordinateRing.XYIdeal, Ideal.mem_span_pair] at ha
    obtain ⟨p, q, hpq⟩ := ha
    have hdecomp : χE (algebraMap _ _ a)
        = χE (algebraMap _ _ p) * χE (algebraMap _ _ (CoordinateRing.XClass (E₀⁄F).toAffine x))
          + χE (algebraMap _ _ q)
            * χE (algebraMap _ _ (CoordinateRing.YClass (E₀⁄F).toAffine (C y))) := by
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← map_add, ← map_add, hpq]
    rw [show (⟨χE (algebraMap _ _ a), hχE_CR_mem a⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨χE (algebraMap _ _ p), hχE_CR_mem p⟩
            * ⟨_, hfinσP (CoordinateRing.XClass (E₀⁄F').toAffine (algebraMap F F' x))⟩
          + ⟨χE (algebraMap _ _ q), hχE_CR_mem q⟩
            * ⟨_, hfinσP (CoordinateRing.YClass (E₀⁄F').toAffine (C (algebraMap F F' y)))⟩ from
        Subtype.ext (by
          push_cast
          rw [hdecomp, kw_surge_hgf4_χE_algebraMap_XClass F F' E₀ x,
            kw_surge_hgf4_χE_algebraMap_YClass F F' E₀ y])]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hXClass_σP_mem_𝔪)
      (Ideal.mul_mem_left _ _ hYClass_σP_mem_𝔪)

  have hχE_unit : ∀ s : (E₀⁄F).toAffine.CoordinateRing,
      s ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) →
      IsUnit (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
    intro s hs
    obtain ⟨c, hc⟩ := CoordinateRing.exists_sub_algebraMap_mem hP.left s
    have hc_ne : c ≠ 0 := by
      intro h; apply hs; simpa [h, sub_zero] using hc
    have hσc_ne : algebraMap F F' c ≠ 0 := (map_ne_zero_iff _ (algebraMap F F').injective).mpr hc_ne

    have hχE_const : χE (algebraMap (E₀⁄F).toAffine.CoordinateRing _
          (algebraMap F (E₀⁄F).toAffine.CoordinateRing c))
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := by
      rw [← IsScalarTower.algebraMap_apply F (E₀⁄F).toAffine.CoordinateRing
        (E₀⁄F).toAffine.FunctionField, AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]
    have hsplit : (⟨χE (algebraMap _ _ s), hχE_CR_mem s⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        = ⟨algebraMap F' _ (algebraMap F F' c),
            (placeOfEquation hσP.left).algebraMap_mem' _⟩
          + ⟨χE (algebraMap _ _ (s - algebraMap F _ c)), hχE_CR_mem _⟩ := by
      refine Subtype.ext ?_
      show χE (algebraMap _ _ s)
          = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c)
            + χE (algebraMap _ _ (s - algebraMap F _ c))
      rw [← hχE_const, ← map_add, ← map_add, add_sub_cancel]
    rw [hsplit]

    have hfirst_unit : IsUnit (⟨algebraMap F' _ (algebraMap F F' c),
        (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
        (placeOfEquation hσP.left).toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap F' _ (algebraMap F F' c)⁻¹,
        (placeOfEquation hσP.left).algebraMap_mem' _⟩, Subtype.ext ?_⟩
      push_cast
      rw [← map_inv₀, ← map_mul, mul_inv_cancel₀ hσc_ne, map_one]
    have hsecond_𝔪 := hχE_mem_𝔪 (s - algebraMap F _ c) hc

    by_contra hnotunit
    have hsum_𝔪 := (IsLocalRing.mem_maximalIdeal _).mpr (mem_nonunits_iff.mpr hnotunit)
    have hfirst_𝔪 : (⟨algebraMap F' _ (algebraMap F F' c),
          (placeOfEquation hσP.left).algebraMap_mem' _⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      have hsub := Ideal.sub_mem _ hsum_𝔪 hsecond_𝔪
      rwa [add_sub_cancel_right] at hsub
    exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hfirst_𝔪)) hfirst_unit

  haveI hXY_prime : (CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)).IsPrime :=
    (CoordinateRing.XYIdeal_isMaximal hP.left).isPrime

  have hmem_P : ∀ f : (E₀⁄F).toAffine.FunctionField,
      f ∈ (placeOfEquation hP.left).toValuationSubring
        ↔ ∃ (n s : (E₀⁄F).toAffine.CoordinateRing)
            (_ : s ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)),
          f = algebraMap _ _ n * (algebraMap _ _ s)⁻¹ := by
    intro f
    have hfinP := isFinitePlace_placeOfEquation hP.left
    constructor
    · intro hf

      obtain ⟨n, s, hcase⟩ :=
        (CoordinateRing.heightOneSpectrumOfEquation hP.left).exists_primeCompl_mul_eq_or_mul_eq
          (K := (E₀⁄F).toAffine.FunctionField) f
      have hs_nin : (s : (E₀⁄F).toAffine.CoordinateRing)
          ∉ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) :=
        Ideal.mem_primeCompl_iff.mp s.2
      have hs_CR_ne : (s : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 :=
        fun h => hs_nin (h ▸ Ideal.zero_mem _)
      have hs0 : algebraMap (E₀⁄F).toAffine.CoordinateRing
          (E₀⁄F).toAffine.FunctionField (s : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hs_CR_ne
      rcases hcase with heq | heq
      ·
        refine ⟨n, s, hs_nin, ?_⟩
        field_simp at heq ⊢; linear_combination heq
      ·

        by_cases hn_nin : (n : _) ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y)
        ·

          exfalso
          have hn0 : (n : (E₀⁄F).toAffine.CoordinateRing) ≠ 0 := fun h => by
            rw [h, map_zero, mul_zero] at heq
            exact hs_CR_ne ((map_eq_zero_iff _
              (IsFractionRing.injective _ _)).mp heq.symm)
          have hord_n_pos : 0 < (placeOfEquation hP.left).ord (algebraMap _ _ (n : _)) :=
            (ord_placeOfEquation_pos_iff hP.left hn0).mpr hn_nin
          have hord_s_zero : (placeOfEquation hP.left).ord
              (algebraMap _ _ (s : (E₀⁄F).toAffine.CoordinateRing)) = 0 := by
            by_contra hne
            exact hs_nin ((ord_placeOfEquation_ne_zero_iff hP.left hs_CR_ne).mp hne)
          have hord_f_neg : (placeOfEquation hP.left).ord f < 0 := by
            have hf0 : f ≠ 0 := fun h => by
              rw [h, zero_mul] at heq
              exact hs_CR_ne ((map_eq_zero_iff _
                (IsFractionRing.injective _ _)).mp heq.symm)
            have hfn_eq : (placeOfEquation hP.left).ord f
                + (placeOfEquation hP.left).ord (algebraMap _ _ (n : _))
                = (placeOfEquation hP.left).ord
                    (algebraMap _ _ (s : (E₀⁄F).toAffine.CoordinateRing)) := by
              rw [← Place.ord_mul _ hf0
                  ((map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr hn0), heq]
            omega
          exact not_le.mpr hord_f_neg ((placeOfEquation hP.left).ord_nonneg_of_mem hf)
        · refine ⟨s, n, hn_nin, ?_⟩
          have hn0 : algebraMap _ (E₀⁄F).toAffine.FunctionField (n : _) ≠ 0 :=
            (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
              (fun h => hn_nin (h ▸ Ideal.zero_mem _))
          field_simp at heq ⊢; linear_combination heq
    · rintro ⟨n, s, hs_nin, rfl⟩
      have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      exact Subring.mul_mem _ (hfinP n) hs_inv
  constructor
  ·
    intro hχEg
    by_contra hg_notin
    have hg_ne : g ≠ 0 := fun h => hg_notin (h ▸ Subring.zero_mem _)
    have hginv_in : g⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
      ((placeOfEquation hP.left).toValuationSubring.mem_or_inv_mem g).resolve_left hg_notin
    obtain ⟨n, s, hs_notin, hginv_eq⟩ := (hmem_P g⁻¹).mp hginv_in

    have hginv_𝔪 : (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal _ := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact hg_notin (inv_inv g ▸ kw_surge_hgf4_place_inv_mem_of_isUnit _ hu)
    have hn_in : n ∈ CoordinateRing.XYIdeal (E₀⁄F).toAffine x (C y) := by
      by_contra hn_notin

      have hfinP := isFinitePlace_placeOfEquation hP.left
      have hn_inv : (algebraMap _ _ n)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hs_inv : (algebraMap _ _ s)⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring :=
        hfinP.inv_mem (by rwa [centre_placeOfEquation])
      have hginv_unit : IsUnit
          (⟨g⁻¹, hginv_in⟩ : (placeOfEquation hP.left).toValuationSubring) := by
        have hg_mem : g ∈ (placeOfEquation hP.left).toValuationSubring := by
          have : g = algebraMap _ _ s * (algebraMap _ _ n)⁻¹ := by
            rw [← inv_inv g, hginv_eq, mul_inv, inv_inv, mul_comm]
          rw [this]; exact Subring.mul_mem _ (hfinP s) hn_inv
        exact isUnit_iff_exists_inv.mpr
          ⟨(⟨g, hg_mem⟩ : (placeOfEquation hP.left).toValuationSubring),
           Subtype.ext (by push_cast; exact inv_mul_cancel₀ hg_ne)⟩
      exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hginv_𝔪) hginv_unit

    have hχEn_𝔪 := hχE_mem_𝔪 n hn_in
    have hχEs_unit := hχE_unit s hs_notin
    have hχEginv_eq : χE g⁻¹ = χE (algebraMap _ _ n) * (χE (algebraMap _ _ s))⁻¹ := by
      rw [hginv_eq, map_mul, map_inv₀]
    have hχEginv_mem : χE g⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring := by
      rw [hχEginv_eq]
      exact Subring.mul_mem _ (hχE_CR_mem n)
        (kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit)
    have hχEginv_𝔪 : (⟨χE g⁻¹, hχEginv_mem⟩ :
          (placeOfEquation hσP.left).toValuationSubring)
        ∈ IsLocalRing.maximalIdeal (placeOfEquation hσP.left).toValuationSubring := by
      have hχEs_inv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hχEs_unit
      have hrw : (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring)
          = (⟨χE (algebraMap _ _ n), hχE_CR_mem n⟩ :
              (placeOfEquation hσP.left).toValuationSubring)
            * ⟨(χE (algebraMap _ _ s))⁻¹, hχEs_inv_mem⟩ :=
        Subtype.ext (by show χE g⁻¹ = _ * _; exact hχEginv_eq)
      rw [hrw]
      exact Ideal.mul_mem_right _ _ hχEn_𝔪

    have hχEg_ne : χE g ≠ 0 := (map_ne_zero_iff _ hχE_inj).mpr hg_ne
    have hχEginv_unit : IsUnit
        (⟨χE g⁻¹, hχEginv_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
      isUnit_iff_exists_inv.mpr
        ⟨(⟨χE g, hχEg⟩ : (placeOfEquation hσP.left).toValuationSubring),
         Subtype.ext (by show χE g⁻¹ * χE g = 1; rw [map_inv₀, inv_mul_cancel₀ hχEg_ne])⟩
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp hχEginv_𝔪) hχEginv_unit
  ·
    intro hg
    obtain ⟨n, s, hs_notin, hg_eq⟩ := (hmem_P g).mp hg
    rw [hg_eq, map_mul, map_inv₀]
    exact Subring.mul_mem _ (hχE_CR_mem n)
      (kw_surge_hgf4_place_inv_mem_of_isUnit _ (hχE_unit s hs_notin))

theorem kw_surge_hgf4_bcIota₁_compat (a : (E₀'⁄F).toAffine.FunctionField) :
    (ι₁) (χE' a) = χE (ι₀ a) := by
  let ψE := functionFieldTensorFracEquivGeneral E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneral E₀' F F'

  have hκE' : ψE' (χE' a)
      = algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')) := by
    have hκ : ((functionFieldTensorFracHomGeneral E₀' F F').restrictScalars F).comp
        (functionFieldMapAlongGeneral E₀' F F')
        = (IsScalarTower.toAlgHom F ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine functionField_algHom_ext ?_ ?_
      · show functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [functionFieldMapAlongGeneral_polyToFunctionField_X,
          functionFieldTensorFracHomGeneral_X]; rfl
      · show functionFieldTensorFracHomGeneral E₀' F F' (χE' _) = _
        rw [functionFieldMapAlongGeneral_yGen, functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact DFunLike.congr_fun hκ a

  have hκE : ∀ b, ψE.symm (algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
      (b ⊗ₜ[F] (1 : F'))) = χE b := by
    intro b
    refine ψE.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have hκ : ((functionFieldTensorFracHomGeneral E₀ F F').restrictScalars F).comp
        (functionFieldMapAlongGeneral E₀ F F')
        = (IsScalarTower.toAlgHom F ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine functionField_algHom_ext ?_ ?_
      · show functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [functionFieldMapAlongGeneral_polyToFunctionField_X,
          functionFieldTensorFracHomGeneral_X]; rfl
      · show functionFieldTensorFracHomGeneral E₀ F F' (χE _) = _
        rw [functionFieldMapAlongGeneral_yGen, functionFieldTensorFracHomGeneral_yGen]
        rfl
    exact (DFunLike.congr_fun hκ b).symm

  show ψE.symm (kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀ (ψE' (χE' a)))
      = χE (ι₀ a)
  rw [hκE',
    show kw_surge_hgf4_bcTensorFracIotaAlg E₀ E₀' F F' ι₀
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')))
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _ ((ι₀ a) ⊗ₜ[F] (1 : F')) from by
        show kw_surge_hgf4_bcTensorFracIota E₀ E₀' F F' ι₀ _ = _
        rw [kw_surge_hgf4_bcTensorFracIota_algebraMap, kw_surge_hgf4_bcTensorIota_tmul],
    hκE (ι₀ a)]

include hσ in

theorem kw_surge_hgf4_pmop_naturality :
    let hι₁ := kw_surge_hgf4_bcIota₁_isIntegral E₀ E₀' F F' ι₀ hfin₀
    let hfin₁ := kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀
    let σE : (E₀⁄F).toAffine.Point →+ (E₀⁄F').toAffine.Point :=
      WeierstrassCurve.Affine.Point.map (W' := E₀.toAffine) σ
    let σE' : (E₀'⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
      WeierstrassCurve.Affine.Point.map (W' := E₀'.toAffine) σ
    let φ₀ := pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀)
    let φ₁ := pointMapOfPushforward (ι₁) hι₁ hfin₁ (normFormulaAlong_of_elliptic (ι₁) hfin₁)
    ∀ P, φ₁ (σE P) = σE' (φ₀ P) := by
  intro hι₁ hfin₁ σE σE' φ₀ φ₁

  have hgBC₀ := kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀)
  have hgBC₁ := kw_fdn2_qephod_hend7_pmop_eq_geomMorphBC_sub (ι₁) hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁)
  let g₀ := kw_fdn2_qephod_hend7_geomMorphBC ι₀ hι₀
  let g₁ := kw_fdn2_qephod_hend7_geomMorphBC (ι₁) hι₁

  have hχE_ord_pos : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y)
      (hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y))
      (h : (E₀⁄F).toAffine.FunctionField) (hh : h ≠ 0),
      0 < (placeOfEquation hσP.left).ord (χE h) ↔
        0 < (placeOfEquation hP.left).ord h := by
    intro x y hP hσP h hh
    have hχEh_ne : χE h ≠ 0 :=
      (map_ne_zero_iff _ (functionFieldMapAlongGeneral E₀ F F').injective).mpr hh
    have hVSR := kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP
    constructor <;> intro hpos
    · have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
        (placeOfEquation hσP.left).mem_of_ord_nonneg hχEh_ne hpos.le
      have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring := (hVSR h).mp hχEh_mem
      rw [← Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
      have hχEinv_mem : χE h⁻¹ ∈ (placeOfEquation hσP.left).toValuationSubring :=
        (hVSR h⁻¹).mpr hinv_mem
      rw [map_inv₀] at hχEinv_mem
      have hχEh_unit : IsUnit
          (⟨χE h, hχEh_mem⟩ : (placeOfEquation hσP.left).toValuationSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨(χE h)⁻¹, hχEinv_mem⟩,
          Subtype.ext (mul_inv_cancel₀ hχEh_ne)⟩
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
        ((Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem).mpr hpos))) hχEh_unit
    · have hh_mem : h ∈ (placeOfEquation hP.left).toValuationSubring :=
        (placeOfEquation hP.left).mem_of_ord_nonneg hh hpos.le
      have hχEh_mem : χE h ∈ (placeOfEquation hσP.left).toValuationSubring :=
        (hVSR h).mpr hh_mem
      rw [← Place.mem_maximalIdeal_iff_ord_pos _ hχEh_ne hχEh_mem,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have hinv_mem := kw_surge_hgf4_place_inv_mem_of_isUnit _ hu
      have hh_inv_mem : h⁻¹ ∈ (placeOfEquation hP.left).toValuationSubring := by
        rw [← map_inv₀] at hinv_mem; exact (hVSR h⁻¹).mp hinv_mem
      have hh_unit : IsUnit
          (⟨h, hh_mem⟩ : (placeOfEquation hP.left).toValuationSubring) :=
        isUnit_iff_exists_inv.mpr ⟨⟨h⁻¹, hh_inv_mem⟩, Subtype.ext (mul_inv_cancel₀ hh)⟩
      exact (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal _).mp
        ((Place.mem_maximalIdeal_iff_ord_pos _ hh hh_mem).mpr hpos))) hh_unit
  have hgBC_nat_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      g₁ (σE (.some x y hP)) = σE' (g₀ (.some x y hP)) := by
    intro x y hP

    have hσP : (E₀⁄F').toAffine.Nonsingular (algebraMap F F' x) (algebraMap F F' y) :=
      kw_surge_hgf4_toAffine_map_eq F F' E₀ ▸
        (((E₀⁄F).toAffine.map_nonsingular (algebraMap F F').injective x y).mpr hP)
    have hσE_some : σE (.some x y hP)
        = .some (algebraMap F F' x) (algebraMap F F' y) hσP := by
      have h := Point.map_some (W' := E₀.toAffine) (F := F) (K := F') σ hP
      rw [show σE (.some x y hP) = Point.map (W' := E₀.toAffine) σ (.some x y hP) from rfl, h]
      congr 1 <;> exact hσ _

    refine placeOfPoint_injective ?_
    rw [← kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC (ι₁) hι₁ (σE (.some x y hP)),
      hσE_some, placeOfPoint_some]

    have hseam₀ : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
        = placeOfPoint (g₀ (.some x y hP)) := by
      rw [← placeOfPoint_some hP,
        kw_fdn2_qephod_hend7_placeOfPoint_geomMorphBC ι₀ hι₀]

    have hι₁X : (ι₁) (polyToFunctionField (E₀'⁄F').toAffine X)
        = χE (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)) := by
      rw [← functionFieldMapAlongGeneral_polyToFunctionField_X E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _
    have hι₁Y : (ι₁) (yGen (E₀'⁄F').toAffine)
        = χE (ι₀ (yGen (E₀'⁄F).toAffine)) := by
      rw [← functionFieldMapAlongGeneral_yGen E₀' F F']
      exact kw_surge_hgf4_bcIota₁_compat E₀ E₀' F F' ι₀ _

    have hχE_const : ∀ c : F, χE (algebraMap F (E₀⁄F).toAffine.FunctionField c)
        = algebraMap F' (E₀⁄F').toAffine.FunctionField (algebraMap F F' c) := fun c => by
      rw [AlgHom.commutes,
        IsScalarTower.algebraMap_apply F F' (E₀⁄F').toAffine.FunctionField]

    rcases hQ₀_case : g₀ (.some x y hP) with _ | ⟨qx, qy, hQ₀ns⟩
    ·
      rw [show placeOfPoint (σE' (.zero : (E₀'⁄F).toAffine.Point))
          = (InfinitePlace.place : Place F' (E₀'⁄F').toAffine.FunctionField) from by
        rw [show σE' (.zero : (E₀'⁄F).toAffine.Point)
            = (.zero : (E₀'⁄F').toAffine.Point) from map_zero σE', placeOfPoint_zero]]
      refine AbstractSeam.restrictAlong_eq_infinitePlace (ι₁) hι₁ rfl _ ?_

      rw [hι₁X]
      intro hmem
      have hι₀X_mem : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          ∈ (placeOfEquation hP.left).toValuationSubring :=
        (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mp hmem
      have hX_res : polyToFunctionField (E₀'⁄F).toAffine X
          ∈ ((placeOfEquation hP.left).restrictAlong ι₀ hι₀).toValuationSubring :=
        (Place.mem_restrictAlong_iff ι₀ hι₀ _ _).mpr hι₀X_mem
      rw [hseam₀, hQ₀_case, placeOfPoint_zero] at hX_res

      exact InfinitePlace.not_isFinitePlace (isFinitePlace_of_mem _ hX_res)
    ·
      have hσQ : (E₀'⁄F').toAffine.Nonsingular (algebraMap F F' qx) (algebraMap F F' qy) :=
        kw_surge_hgf4_toAffine_map_eq F F' E₀' ▸
          (((E₀'⁄F).toAffine.map_nonsingular (algebraMap F F').injective qx qy).mpr hQ₀ns)
      have hσE'_some : σE' (.some qx qy hQ₀ns)
          = .some (algebraMap F F' qx) (algebraMap F F' qy) hσQ := by
        have h := Point.map_some (W' := E₀'.toAffine) (F := F) (K := F') σ hQ₀ns
        rw [show σE' (.some qx qy hQ₀ns)
            = Point.map (W' := E₀'.toAffine) σ (.some qx qy hQ₀ns) from rfl, h]
        congr 1 <;> exact hσ _
      rw [hσE'_some, placeOfPoint_some]

      have hseam₀' : (placeOfEquation hP.left).restrictAlong ι₀ hι₀
          = placeOfEquation hQ₀ns.left := by rw [hseam₀, hQ₀_case, placeOfPoint_some]

      have hbrX : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.XClass (E₀'⁄F).toAffine qx)
          = polyToFunctionField (E₀'⁄F).toAffine X - algebraMap F _ qx :=
        AbstractSeam.map_XClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qx
      have hbrY : algebraMap (E₀'⁄F).toAffine.CoordinateRing (E₀'⁄F).toAffine.FunctionField
          (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))
          = yGen (E₀'⁄F).toAffine - algebraMap F _ qy :=
        AbstractSeam.map_YClass (V := (E₀'⁄F).toAffine) (W := (E₀'⁄F).toAffine)
          (AlgHom.id F (E₀'⁄F).toAffine.FunctionField) rfl qy
      have hι₀X_ne : ι₀ (polyToFunctionField (E₀'⁄F).toAffine X)
          - algebraMap F _ qx ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX]
        exact fun h => (CoordinateRing.XClass_ne_zero qx)
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hι₀Y_ne : ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy ≠ 0 := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY]
        exact fun h => (CoordinateRing.YClass_ne_zero (C qy))
          ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp (ι₀.injective
            (h.trans (map_zero ι₀).symm)))
      have hram_pos : 0 < Place.ramificationIndexAlong ι₀ (placeOfEquation hP.left) :=
        Place.ramificationIndexAlong_pos ι₀ hι₀ (placeOfEquation hP.left)
      have hdxF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (polyToFunctionField (E₀'⁄F).toAffine X) - algebraMap F _ qx) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrX,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.XClass (E₀'⁄F).toAffine qx)) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.XClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert _ _))
        positivity
      have hdyF : 0 < (placeOfEquation hP.left).ord
          (ι₀ (yGen (E₀'⁄F).toAffine) - algebraMap F _ qy) := by
        rw [← ι₀.commutes, ← map_sub, ← hbrY,
          Place.ord_restrictAlong ι₀ hι₀, hseam₀']
        have hQord : 0 < (placeOfEquation hQ₀ns.left).ord (algebraMap _ _
            (CoordinateRing.YClass (E₀'⁄F).toAffine (C qy))) :=
          (ord_placeOfEquation_pos_iff hQ₀ns.left (CoordinateRing.YClass_ne_zero _)).mpr
            (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
        positivity

      refine AbstractSeam.restrictAlong_placeOfEquation (ι₁) hι₁ rfl rfl
        hσP.left hσQ.left ?_ ?_ ?_
      ·
        rw [hι₁X]
        refine (kw_surge_hgf4_χE_VSR_compat E₀ F F' hP hσP _).mpr ?_
        rw [← Place.mem_restrictAlong_iff ι₀ hι₀, hseam₀']
        exact isFinitePlace_placeOfEquation hQ₀ns.left _
      ·
        rw [hι₁X, ← hχE_const qx, ← map_sub]
        exact (hχE_ord_pos hP hσP _ hι₀X_ne).mpr hdxF
      ·
        rw [hι₁Y, ← hχE_const qy, ← map_sub]
        exact (hχE_ord_pos hP hσP _ hι₀Y_ne).mpr hdyF

  let δ : (E₀⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
    (φ₁.comp σE) - (σE'.comp φ₀)
  have hδ_affine : ∀ {x y : F} (hP : (E₀⁄F).toAffine.Nonsingular x y),
      δ (.some x y hP) = σE' (g₀ 0) - g₁ 0 := by
    intro x y hP
    show φ₁ (σE (.some x y hP)) - σE' (φ₀ (.some x y hP)) = _
    have h1 : φ₁ (σE (.some x y hP)) = g₁ (σE (.some x y hP)) - g₁ 0 := hgBC₁ _
    have h0 : φ₀ (.some x y hP) = g₀ (.some x y hP) - g₀ 0 := hgBC₀ _
    rw [h1, h0, map_sub, hgBC_nat_affine hP]
    abel

  have hC_zero : σE' (g₀ 0) - g₁ 0 = 0 := by
    obtain ⟨e3⟩ :=
      WeierstrassCurve.nonempty_pointTorsionBy_zmod (W := (E₀⁄F)) (n := 3) (by omega)
    let P₀ : (E₀⁄F).toAffine.Point := (e3.symm (fun _ => 1) : _)
    have hP₀_3 : (3 : ℤ) • P₀ = 0 := by
      have := (e3.symm (fun _ => 1)).2
      simpa [Submodule.mem_torsionBy_iff, P₀] using this
    have hP₀_ne : P₀ ≠ 0 := by
      intro h
      have heq : e3.symm (fun _ => 1) = 0 :=
        Subtype.ext (show (e3.symm (fun _ => 1) : (E₀⁄F).toAffine.Point) = 0 from h)
      have hfun : (fun _ => (1 : ZMod 3)) = (0 : Fin 2 → ZMod 3) := by
        have := congrArg e3 heq
        rwa [e3.apply_symm_apply, map_zero] at this
      exact one_ne_zero (congrFun hfun 0)
    have h2P₀_ne : (2 : ℤ) • P₀ ≠ 0 := by
      intro h2
      have : (3 : ℤ) • P₀ - (2 : ℤ) • P₀ = 0 := by rw [hP₀_3, h2, sub_zero]
      have hP₀_eq : P₀ = 0 := by
        have : ((3 : ℤ) - 2) • P₀ = 0 := by rw [sub_smul]; exact this
        simpa using this
      exact hP₀_ne hP₀_eq

    rcases hP₀_case : P₀ with _ | ⟨px, py, hpP⟩
    · exact (hP₀_ne hP₀_case).elim
    rcases h2P₀_case : (2 : ℤ) • P₀ with _ | ⟨qx, qy, hqQ⟩
    · exact (h2P₀_ne h2P₀_case).elim

    have h2C : (2 : ℤ) • (σE' (g₀ 0) - g₁ 0) = σE' (g₀ 0) - g₁ 0 := by
      calc (2 : ℤ) • (σE' (g₀ 0) - g₁ 0)
          = (2 : ℤ) • δ (.some px py hpP) := by rw [hδ_affine hpP]
        _ = δ ((2 : ℤ) • (.some px py hpP : (E₀⁄F).toAffine.Point)) :=
            (map_zsmul δ 2 _).symm
        _ = δ ((2 : ℤ) • P₀) := by rw [hP₀_case]
        _ = δ (.some qx qy hqQ) := by rw [h2P₀_case]
        _ = σE' (g₀ 0) - g₁ 0 := hδ_affine hqQ

    have hC' : ((2 : ℤ) - 1) • (σE' (g₀ 0) - g₁ 0) = 0 := by
      rw [sub_smul, one_smul, h2C, sub_self]
    simpa using hC'

  intro P
  have hδP : δ P = 0 := by
    rcases P with _ | ⟨x, y, hP⟩
    · exact map_zero δ
    · rw [hδ_affine hP, hC_zero]
  exact sub_eq_zero.mp hδP

end Naturality

end BetweenCurvesTensor

theorem kw_surge_hgf4_hBC_proved : KwD5BetweenCurvesFFSeamBaseChange := by
  have _ := kw_surge_hgf4_hBC_axiomAnchor
  intro R₀ _ E₀ E₀' _ _ F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ σ ι₀ hι₀ hfin₀ N _ hcyc hcard

  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower R₀ F F' := IsScalarTower.of_algebraMap_eq fun r =>
    (σ.commutes r).symm

  haveI : IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
    functionFieldTensorIsDomain_dischargeGeneral E₀ F F'
  haveI : IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') :=
    functionFieldTensorIsDomain_dischargeGeneral E₀' F F'

  let ι₁ := kw_surge_hgf4_bcIota₁ E₀ E₀' F F' ι₀
  have hι₁ := kw_surge_hgf4_bcIota₁_isIntegral E₀ E₀' F F' ι₀ hfin₀
  have hfin₁ := kw_surge_hgf4_bcIota₁_finiteAlong E₀ E₀' F F' ι₀ hfin₀

  have hD := kw_surge_hgf4_bcIota₁_finrankAlong E₀ E₀' F F' ι₀ hfin₀
  have hker₁ : Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) = N := by
    rw [natCard_ker_pointMapOfPushforward_eq_finrankAlong (E₀⁄F').toAffine (E₀'⁄F').toAffine
        ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁), hD,
      ← natCard_ker_pointMapOfPushforward_eq_finrankAlong (E₀⁄F).toAffine (E₀'⁄F).toAffine
        ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀), hcard]

  let σE : (E₀⁄F).toAffine.Point →+ (E₀⁄F').toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀.toAffine) σ
  let σE' : (E₀'⁄F).toAffine.Point →+ (E₀'⁄F').toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀'.toAffine) σ
  have hσE_inj : Function.Injective σE :=
    WeierstrassCurve.Affine.Point.map_injective (W' := E₀.toAffine) σ
  let φ₀ := pointMapOfPushforward ι₀ hι₀ hfin₀ (normFormulaAlong_of_elliptic ι₀ hfin₀)
  let φ₁ := pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁)

  have hnat : ∀ P, φ₁ (σE P) = σE' (φ₀ P) := by

    exact kw_surge_hgf4_pmop_naturality E₀ E₀' F F' ι₀ hι₀ hfin₀ σ (fun _ => rfl)

  have hker_sub : ∀ P ∈ AddMonoidHom.ker φ₀, σE P ∈ AddMonoidHom.ker φ₁ := by
    intro P hP
    rw [AddMonoidHom.mem_ker] at hP ⊢
    rw [hnat P, hP, map_zero]

  let σE_ker : (AddMonoidHom.ker φ₀) →+ (AddMonoidHom.ker φ₁) :=
    { toFun := fun ⟨P, hP⟩ => ⟨σE P, hker_sub P hP⟩
      map_zero' := Subtype.ext (map_zero σE)
      map_add' := fun ⟨P, _⟩ ⟨Q, _⟩ => Subtype.ext (map_add σE P Q) }
  have hσE_ker_inj : Function.Injective σE_ker := fun ⟨P, _⟩ ⟨Q, _⟩ hPQ =>
    Subtype.ext (hσE_inj (Subtype.ext_iff.mp hPQ))

  have hcard_eq : Nat.card (AddMonoidHom.ker φ₀) = Nat.card (AddMonoidHom.ker φ₁) := by
    rw [hcard, hker₁]
  have hfin_ker₀ : Finite (AddMonoidHom.ker φ₀) :=
    Nat.finite_of_card_ne_zero (hcard ▸ (NeZero.ne N))
  have hfin_ker₁ : Finite (AddMonoidHom.ker φ₁) :=
    Nat.finite_of_card_ne_zero (hker₁ ▸ (NeZero.ne N))
  have hσE_ker_bij : Function.Bijective σE_ker :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hσE_ker_inj, hcard_eq⟩

  have hcyc₁ : IsAddCyclic (AddMonoidHom.ker φ₁) := by
    let e : (AddMonoidHom.ker φ₀) ≃+ (AddMonoidHom.ker φ₁) :=
      AddEquiv.ofBijective σE_ker hσE_ker_bij
    obtain ⟨⟨g₀, hg₀⟩⟩ := hcyc
    exact ⟨⟨e g₀, fun y => by
      obtain ⟨k, hk⟩ := hg₀ (e.symm y)
      exact ⟨k, by rw [← e.apply_symm_apply y, ← hk, map_zsmul]⟩⟩⟩
  exact ⟨ι₁, hι₁, hfin₁, hcyc₁, hker₁⟩

section BCNoACEngine
variable {R₀ : Type u} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F).toAffine] [(E₀'⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F).toAffine] [(E₀⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F').toAffine] [(E₀'⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F').toAffine]
variable (ι' : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)
attribute [local instance] Algebra.TensorProduct.rightAlgebra

scoped instance kw_surgehgf4_hfgkd_tensorIsDomain_E :
    IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  functionFieldTensorIsDomain_dischargeGeneralNoAC E₀ F F'

scoped instance kw_surgehgf4_hfgkd_tensorIsDomain_E' :
    IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') :=
  functionFieldTensorIsDomain_dischargeGeneralNoAC E₀' F F'
end BCNoACEngine

/-! ## `KwD5BetweenCurvesKerTransportAlongEmbed` -/

def KwD5BetweenCurvesKerTransportAlongEmbed : Prop :=
  ∀ (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀⁄F₁).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F₁).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F₁).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F₁).toAffine] [(E₀'⁄F₁).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F₁).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F₁).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F₁).toAffine] [(E₀⁄F₂).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀⁄F₂).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀⁄F₂).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀⁄F₂).toAffine] [(E₀'⁄F₂).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (E₀'⁄F₂).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (E₀'⁄F₂).toAffine] [WeierstrassCurve.Affine.AbelTheorem (E₀'⁄F₂).toAffine]
    (ι₁ : (E₀'⁄F₁).toAffine.FunctionField →ₐ[F₁] (E₀⁄F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁)
    (ι₂ : (E₀'⁄F₂).toAffine.FunctionField →ₐ[F₂] (E₀⁄F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂)
    (_hχ : ∀ x : (E₀'⁄F₁).toAffine.FunctionField,
      ι₂ (functionFieldMapAlongGeneralNoAC E₀' F₁ F₂ x)
        = functionFieldMapAlongGeneralNoAC E₀ F₁ F₂ (ι₁ x))
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι₂ hι₂ hfin₂ (normFormulaAlong_of_elliptic ι₂ hfin₂))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₂ hι₂ hfin₂ (normFormulaAlong_of_elliptic ι₂ hfin₂))) = N →
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) ∧
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁))) = N

/-! ## The `kw_surgehgf4_hfgkd_ktd_*` block -/

theorem kw_surgehgf4_hfgkd_ktd_axiomAnchor : True := by
  have h1 : (True ∧ True) = True := propext (by simp)
  have h2 := Classical.choice ⟨()⟩
  have h3 := Quot.sound (r := fun _ _ : Unit => True) (a := ()) (b := ()) trivial
  trivial

theorem kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral
    {R₀ : Type u} [Field R₀] (W : WeierstrassCurve R₀) [W.IsElliptic]
    (F : Type u) [Field F] [Algebra R₀ F] [DecidableEq F] [IsAlgClosed F] [CharZero F]
    (F' : Type u) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [IsAlgClosed F'] [CharZero F']
    [Algebra F F'] [IsScalarTower R₀ F F']
    [(W⁄F).IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F).toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F).toAffine] [WeierstrassCurve.Affine.AbelTheorem (W⁄F).toAffine] [(W⁄F').IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate (W⁄F').toAffine] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred (W⁄F').toAffine] [WeierstrassCurve.Affine.AbelTheorem (W⁄F').toAffine] :
    functionFieldMapAlongGeneralNoAC W F F'
      = functionFieldMapAlongGeneral W F F' := by
  refine functionField_algHom_ext ?_ ?_
  · rw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
      functionFieldMapAlongGeneral_polyToFunctionField_X]
  · rw [functionFieldMapAlongGeneralNoAC_yGen, functionFieldMapAlongGeneral_yGen]

theorem kw_surgehgf4_hfgkd_ktd_kerTransport_proved :
    KwD5BetweenCurvesKerTransportAlongEmbed.{u} := by
  have _ := kw_surgehgf4_hfgkd_ktd_axiomAnchor
  intro R₀ _ E₀ E₀' _ _ F₁ _ _ _ _ _ F₂ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ι₁ hι₁ hfin₁ ι₂ hι₂ hfin₂ hχ N _ hcyc₂ hcard₂

  haveI : IsDomain ((E₀⁄F₁).toAffine.FunctionField ⊗[F₁] F₂) :=
    functionFieldTensorIsDomain_dischargeGeneral E₀ F₁ F₂
  haveI : IsDomain ((E₀'⁄F₁).toAffine.FunctionField ⊗[F₁] F₂) :=
    functionFieldTensorIsDomain_dischargeGeneral E₀' F₁ F₂

  have hχE₀ := kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral E₀ F₁ F₂
  have hχE₀' := kw_surgehgf4_hfgkd_ktd_chiNoAC_eq_chiGeneral E₀' F₁ F₂

  have hχG : ∀ x, ι₂ (functionFieldMapAlongGeneral E₀' F₁ F₂ x)
      = functionFieldMapAlongGeneral E₀ F₁ F₂ (ι₁ x) := by
    intro x; rw [← hχE₀', ← hχE₀]; exact hχ x

  have heq : ι₂ = kw_surge_hgf4_bcIota₁ E₀ E₀' F₁ F₂ ι₁ := by
    refine functionField_algHom_ext ?_ ?_
    · rw [show polyToFunctionField (E₀'⁄F₂).toAffine X
            = functionFieldMapAlongGeneral E₀' F₁ F₂
                (polyToFunctionField (E₀'⁄F₁).toAffine X) from
          (functionFieldMapAlongGeneral_polyToFunctionField_X E₀' F₁ F₂).symm,
        hχG, kw_surge_hgf4_bcIota₁_compat E₀ E₀' F₁ F₂ ι₁]
    · rw [show yGen (E₀'⁄F₂).toAffine
            = functionFieldMapAlongGeneral E₀' F₁ F₂ (yGen (E₀'⁄F₁).toAffine) from
          (functionFieldMapAlongGeneral_yGen E₀' F₁ F₂).symm,
        hχG, kw_surge_hgf4_bcIota₁_compat E₀ E₀' F₁ F₂ ι₁]
  subst heq

  clear hχ hχG hχE₀ hχE₀'

  let φ₁ := pointMapOfPushforward ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁)
  let φ₂ := pointMapOfPushforward _ hι₂ hfin₂ (normFormulaAlong_of_elliptic _ hfin₂)
  have hD := kw_surge_hgf4_bcIota₁_finrankAlong E₀ E₀' F₁ F₂ ι₁ hfin₁
  have hker₁ : Nat.card (AddMonoidHom.ker φ₁) = N := by
    rw [show φ₁ = _ from rfl,
      natCard_ker_pointMapOfPushforward_eq_finrankAlong (E₀⁄F₁).toAffine (E₀'⁄F₁).toAffine
        ι₁ hι₁ hfin₁ (normFormulaAlong_of_elliptic ι₁ hfin₁), ← hD,
      ← natCard_ker_pointMapOfPushforward_eq_finrankAlong (E₀⁄F₂).toAffine (E₀'⁄F₂).toAffine
        _ hι₂ hfin₂ (normFormulaAlong_of_elliptic _ hfin₂)]
    exact hcard₂

  let σ : F₁ →ₐ[R₀] F₂ := IsScalarTower.toAlgHom R₀ F₁ F₂
  let σE : (E₀⁄F₁).toAffine.Point →+ (E₀⁄F₂).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀.toAffine) σ
  let σE' : (E₀'⁄F₁).toAffine.Point →+ (E₀'⁄F₂).toAffine.Point :=
    WeierstrassCurve.Affine.Point.map (W' := E₀'.toAffine) σ
  have hσE_inj : Function.Injective σE :=
    WeierstrassCurve.Affine.Point.map_injective (W' := E₀.toAffine) σ
  have hnat : ∀ P, φ₂ (σE P) = σE' (φ₁ P) :=
    kw_surge_hgf4_pmop_naturality E₀ E₀' F₁ F₂ ι₁ hι₁ hfin₁ σ (fun _ => rfl)

  have hker_sub : ∀ P ∈ AddMonoidHom.ker φ₁, σE P ∈ AddMonoidHom.ker φ₂ := by
    intro P hP
    rw [AddMonoidHom.mem_ker] at hP ⊢
    rw [hnat P, hP, map_zero]
  let σE_ker : (AddMonoidHom.ker φ₁) →+ (AddMonoidHom.ker φ₂) :=
    { toFun := fun ⟨P, hP⟩ => ⟨σE P, hker_sub P hP⟩
      map_zero' := Subtype.ext (map_zero σE)
      map_add' := fun ⟨P, _⟩ ⟨Q, _⟩ => Subtype.ext (map_add σE P Q) }
  have hσE_ker_inj : Function.Injective σE_ker := fun ⟨P, _⟩ ⟨Q, _⟩ hPQ =>
    Subtype.ext (hσE_inj (Subtype.ext_iff.mp hPQ))

  have hcard_eq : Nat.card (AddMonoidHom.ker φ₁) = Nat.card (AddMonoidHom.ker φ₂) := by
    rw [hker₁, hcard₂]
  have hfin_ker₁ : Finite (AddMonoidHom.ker φ₁) :=
    Nat.finite_of_card_ne_zero (hker₁ ▸ (NeZero.ne N))
  have hfin_ker₂ : Finite (AddMonoidHom.ker φ₂) :=
    Nat.finite_of_card_ne_zero (hcard₂ ▸ (NeZero.ne N))
  have hσE_ker_bij : Function.Bijective σE_ker :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hσE_ker_inj, hcard_eq⟩
  let e : (AddMonoidHom.ker φ₁) ≃+ (AddMonoidHom.ker φ₂) :=
    AddEquiv.ofBijective σE_ker hσE_ker_bij
  have hcyc₁ : IsAddCyclic (AddMonoidHom.ker φ₁) := by
    obtain ⟨⟨g₂, hg₂⟩⟩ := hcyc₂
    exact ⟨⟨e.symm g₂, fun y => by
      obtain ⟨k, hk⟩ := hg₂ (e y)
      exact ⟨k, e.injective (by rw [map_zsmul, e.apply_symm_apply]; exact hk)⟩⟩⟩
  exact ⟨hcyc₁, hker₁⟩

end ModularCurve

/-- The pin's `hBC_s17`: the base-change existence seam at the pin's bare name. -/
theorem hBC_s17 : ModularCurve.KwD5BetweenCurvesFFSeamBaseChange :=
  ModularCurve.kw_surge_hgf4_hBC_proved

universe u_kt in
/-- The pin's `kerTransport_s17`: the kernel-transport seam at the pin's bare name. -/
theorem kerTransport_s17 : ModularCurve.KwD5BetweenCurvesKerTransportAlongEmbed.{u_kt} :=
  ModularCurve.kw_surgehgf4_hfgkd_ktd_kerTransport_proved.{u_kt}


/-! ## The two headlines

The statements are the `Theorems/` wrappers', transcribed verbatim (the wrapper, not the
`S_` file's `solution`, is the statement authority: the first quantifies `(R₀ : Type u)`
and concludes a conjunction, the second quantifies `(R₀ : Type)` and concludes the
existential over `ι₁` with `∀ hN₁`). -/

namespace WeierstrassCurve
namespace Affine

/-- **Base change of a cyclic isogeny kernel, the `χ`/`χ'` transport.** If the
base-changed isogeny `ι₂` over `F₂` has cyclic point-map kernel of cardinality `N`, and
it is compatible with `ι₁` through the two algebra maps `χ`, `χ'` (the base changes of
the function-field maps), then `ι₁` has cyclic kernel of the same cardinality. -/
theorem isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
    (R₀ : Type u) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F₁ : Type u) [Field F₁] [Algebra R₀ F₁] [DecidableEq F₁] [IsAlgClosed F₁] [CharZero F₁]
    (F₂ : Type u) [Field F₂] [Algebra R₀ F₂] [DecidableEq F₂] [IsAlgClosed F₂] [CharZero F₂]
    [Algebra F₁ F₂] [IsScalarTower R₀ F₁ F₂]
    [(E₀.baseChange F₁).IsElliptic] [(E₀'.baseChange F₁).IsElliptic]
    [(E₀.baseChange F₂).IsElliptic] [(E₀'.baseChange F₂).IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₁).toAffine]
    [AbelTheorem (E₀.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₁).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₁).toAffine]
    [AbelTheorem (E₀'.baseChange F₁).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F₂).toAffine]
    [AbelTheorem (E₀.baseChange F₂).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F₂).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F₂).toAffine]
    [AbelTheorem (E₀'.baseChange F₂).toAffine]
    (χ : (E₀.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₂).toAffine.FunctionField)
    (hχX : χ (polyToFunctionField (E₀.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀.baseChange F₂).toAffine Polynomial.X)
    (hχY : χ (yCoord (E₀.baseChange F₁).toAffine) = yCoord (E₀.baseChange F₂).toAffine)
    (χ' : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀'.baseChange F₂).toAffine.FunctionField)
    (hχ'X : χ' (polyToFunctionField (E₀'.baseChange F₁).toAffine Polynomial.X)
      = polyToFunctionField (E₀'.baseChange F₂).toAffine Polynomial.X)
    (hχ'Y : χ' (yCoord (E₀'.baseChange F₁).toAffine) = yCoord (E₀'.baseChange F₂).toAffine)
    (ι₁ : (E₀'.baseChange F₁).toAffine.FunctionField →ₐ[F₁] (E₀.baseChange F₁).toAffine.FunctionField)
    (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F₁ ι₁) (hN₁ : NormFormulaAlong F₁ ι₁ hfin₁)
    (ι₂ : (E₀'.baseChange F₂).toAffine.FunctionField →ₐ[F₂] (E₀.baseChange F₂).toAffine.FunctionField)
    (hι₂ : ι₂.toRingHom.IsIntegral) (hfin₂ : FiniteAlong F₂ ι₂) (hN₂ : NormFormulaAlong F₂ ι₂ hfin₂)
    (hcompat : ∀ x, ι₂ (χ' x) = χ (ι₁ x))
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₂ hι₂ hfin₂ hN₂).ker = N) :
    IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
      Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by
  have hχE : χ = ModularCurve.functionFieldMapAlongGeneralNoAC E₀ F₁ F₂ := by
    refine functionField_algHom_ext ?_ ?_
    · rw [hχX, ModularCurve.functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    · rw [ModularCurve.functionFieldMapAlongGeneralNoAC_yGen]; exact hχY
  have hχE' : χ' = ModularCurve.functionFieldMapAlongGeneralNoAC E₀' F₁ F₂ := by
    refine functionField_algHom_ext ?_ ?_
    · rw [hχ'X, ModularCurve.functionFieldMapAlongGeneralNoAC_polyToFunctionField_X]
    · rw [ModularCurve.functionFieldMapAlongGeneralNoAC_yGen]; exact hχ'Y
  subst hχE; subst hχE'
  exact kerTransport_s17.{u} R₀ E₀ E₀' F₁ F₂ ι₁ hι₁ hfin₁ ι₂ hι₂ hfin₂ hcompat N hcyc hcard

/-- **Existence of the base-changed isogeny.** If `ι₀` over `F` has cyclic point-map
kernel of cardinality `N`, then over any field extension `F'` of `F` there is a
base-changed isogeny `ι₁` whose kernel is again cyclic of cardinality `N`, for every
norm formula on it. -/
theorem exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward
    (R₀ : Type) [Field R₀] (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (F F' : Type) [Field F] [Field F'] [Algebra R₀ F] [Algebra R₀ F']
    [DecidableEq F] [DecidableEq F'] [IsAlgClosed F] [IsAlgClosed F'] [CharZero F] [CharZero F']
    [(E₀.baseChange F).IsElliptic] [(E₀'.baseChange F).IsElliptic]
    [(E₀.baseChange F').IsElliptic] [(E₀'.baseChange F').IsElliptic]
    [GenusOnePlaceGate (E₀.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F).toAffine]
    [AbelTheorem (E₀.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F).toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F).toAffine]
    [AbelTheorem (E₀'.baseChange F).toAffine]
    [GenusOnePlaceGate (E₀.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀.baseChange F').toAffine]
    [AbelTheorem (E₀.baseChange F').toAffine]
    [GenusOnePlaceGate (E₀'.baseChange F').toAffine] [GenusOnePlaceGate.IsCentred (E₀'.baseChange F').toAffine]
    [AbelTheorem (E₀'.baseChange F').toAffine]
    (σ : F →ₐ[R₀] F')
    (ι₀ : (E₀'.baseChange F).toAffine.FunctionField →ₐ[F] (E₀.baseChange F).toAffine.FunctionField)
    (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong F ι₀) (hN₀ : NormFormulaAlong F ι₀ hfin₀)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker)
    (hcard : Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N) :
    ∃ (ι₁ : (E₀'.baseChange F').toAffine.FunctionField →ₐ[F'] (E₀.baseChange F').toAffine.FunctionField)
      (hι₁ : ι₁.toRingHom.IsIntegral) (hfin₁ : FiniteAlong F' ι₁),
      ∀ hN₁ : NormFormulaAlong F' ι₁ hfin₁,
        IsAddCyclic (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker ∧
          Nat.card (pointMapOfPushforward ι₁ hι₁ hfin₁ hN₁).ker = N := by
  obtain ⟨ι₁, hι₁, hfin₁, hcyc₁, hcard₁⟩ :=
    hBC_s17 R₀ E₀ E₀' F F' σ ι₀ hι₀ hfin₀ N hcyc hcard
  exact ⟨ι₁, hι₁, hfin₁, fun _ => ⟨hcyc₁, hcard₁⟩⟩

end Affine
end WeierstrassCurve


#print axioms WeierstrassCurve.Affine.isAddCyclic_ker_pointMapOfPushforward_of_baseChange_algHom
#print axioms WeierstrassCurve.Affine.exists_algHom_baseChange_of_isAddCyclic_ker_pointMapOfPushforward

end
