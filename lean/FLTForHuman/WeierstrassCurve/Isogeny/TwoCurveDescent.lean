/-
The two-curve countable descent, and on top of it the headline

  `WeierstrassCurve.Affine.exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward`

This is set **D-6** of the P column; the work order is
`topics/velu/WORKORDER-P3-two-curve-descent.md`.  The pin is
`anthropics/fermats-last-theorem@aa2d8b3`, file

  `P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean`

(3,729 lines) with the statement authority

  `Theorems/Thm_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean`.

The pin's `S_` file is the D row restated in two-curve form: 107 of its 183 declarations are
already in the port, and its base-change engine `kw_surgehgf4_hfgkd_bc*` is D-5's landed
`kw_surge_hgf4_bc*` block.  What is genuinely new is the **two-curve** descent: D-2 landed the
countable descent for an endomorphism of one curve, and the pin's case has an isogeny
`ι : E'.FunctionField →ₐ[K] E.FunctionField` between two *different* curves.  This module
lands that generalisation, built from D-2's promoted descent helpers (`iA_*`, `iCa_*`, `iPFA_*`,
`iPFE_*`), and then the headline, which assembles it with D-5's landed base-change headline.

Route notes (they are deviations from the pin, and deliberate):

* The pin stages its proof through four `KwD5*`/`KwD5BC*` `Prop`s and canonicalises the ambient
  gate instances with a global `scoped instance s13GlobalGate`, whose only proof is the
  producer `exists_genusOnePlaceGate_isCentred_and_abelTheorem` in
  `WeierstrassCurve/GenusOnePlaceGateCentred.lean`.  That producer is **unavailable** here: it
  imports `WeierstrassCurve/Place/RRSpace.lean`, whose `scoped instance instInfinitePlace`
  collides at the name level with `IsogenyEndDatum/Engine.lean`'s `instInfinitePlace`, which
  this module needs through `KernelBaseChange.lean`.  The port therefore declares **none** of
  the `KwD5*`/`KwD5BC*` staging (nor `s13_exists_gate`, `s13GlobalGate`,
  `s13DecEqAlgebraicClosure`) and inlines their content in the headline's proof.  The
  headline's own conclusion already quantifies every gate instance the proof needs, so the
  global device is not needed.
* The pin's base-change engine (`kw_surgehgf4_hfgkd_bcIota₁NoAC`, `A:2501–2839`) is the **gate-
  free, `IsAlgClosed`-free** spelling, and the two-curve descent needs it at `F = K₀` — a
  subfield of `K` that is neither algebraically closed nor gate-equipped.  D-5's landed
  `kw_surge_hgf4_bcIota₁` block is the same proof under the heavier `General` section (it
  hypothesises `[IsAlgClosed F]` and the four gate instances), so it **cannot** be
  instantiated at `K₀`.  The engine is therefore transcribed here, `private`, from the pin's
  `NoAC` block; the pin's `IsDomain` scoped instance becomes the gate-free
  `functionFieldTensorIsDomain_dischargeGeneralNoAC` of D-1.
* The finrank equality is D-5's content, not new mathematics: it is
  `descentBCIota_finrankAlong` (the pin's `…_finrankAlong`) rewritten along the identification
  `descentBCIota (ι') = ι` (the pin's `kw_surgehgf4_cfe_bcIota₁NoAC_eq_ι`).

Everything public here has the pin's name; helpers local to the module are `private` with
content names.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_WeierstrassCurve_Affine_exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward.lean>
-/
import FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField
import FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false

noncomputable section

open Polynomial
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.CoordinateRing AlgebraicCurve
open scoped Polynomial.Bivariate WeierstrassCurve TensorProduct IntermediateField

universe u uK

namespace ModularCurve

/-! ## The descent family of the pin's `kw_iotaDescent*`

The pin's public spelling of the descended function-field map: `pointPullbackHomTo` on the
equation of `E₀.map (algebraMap K₀ E.FunctionField)`, exactly as D-2's `iA_phi`. -/

section Phi

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {K₀ : IntermediateField ℚ K}
variable (E : WeierstrassCurve K) [E.IsElliptic]
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

theorem iotaDescentCurve_map_FF (hmap : E₀.map (algebraMap K₀ K) = E) :
    E₀.map (algebraMap K₀ E.toAffine.FunctionField)
      = E.map (algebraMap K E.toAffine.FunctionField) := by
  have htower : (algebraMap K₀ E.toAffine.FunctionField)
      = (algebraMap K E.toAffine.FunctionField).comp (algebraMap K₀ K) :=
    IsScalarTower.algebraMap_eq K₀ K E.toAffine.FunctionField
  rw [htower, ← WeierstrassCurve.map_map, hmap]

theorem iotaDescentPhi_equation (hmap : E₀.map (algebraMap K₀ K) = E) :
    (E₀.map (algebraMap K₀ E.toAffine.FunctionField)).toAffine.Equation
      (polyToFunctionField E.toAffine X) (yGen E.toAffine) := by
  rw [iotaDescentCurve_map_FF E E₀ hmap]
  exact equation_map_polyToFunctionField_yGen (W := E.toAffine)

theorem iotaDescentPhi_transcendental :
    Function.Injective
      (Polynomial.aeval (R := K₀) (polyToFunctionField E.toAffine X)) := by
  have hK : Transcendental K (polyToFunctionField E.toAffine X) :=
    transcendental_polyToFunctionField_X (W := E.toAffine)
  have hK₀ : Transcendental K₀ (polyToFunctionField E.toAffine X) :=
    hK.restrictScalars (R := K₀) (algebraMap K₀ K).injective
  exact (injective_iff_map_eq_zero _).mpr
    (fun p hp => transcendental_iff.mp hK₀ p hp)

variable (hmap : E₀.map (algebraMap K₀ K) = E)

/-- The descended `K₀`-algebra map `E₀.FunctionField → E.FunctionField` of a model of `E`
over `K₀`; the pin's `kw_iotaDescentPhi`. -/
def iotaDescentPhi : E₀.toAffine.FunctionField →ₐ[K₀] E.toAffine.FunctionField :=
  pointPullbackHomTo (iotaDescentPhi_equation E E₀ hmap)
    (iotaDescentPhi_transcendental E)

theorem iotaDescentPhi_X :
    iotaDescentPhi E E₀ hmap (polyToFunctionField E₀.toAffine X)
      = polyToFunctionField E.toAffine X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

theorem iotaDescentPhi_yGen :
    iotaDescentPhi E E₀ hmap (yGen E₀.toAffine) = yGen E.toAffine :=
  pointPullbackHomTo_yGen _ _

end Phi


/-! ## The gate-free base-change engine of an isogeny, `NoAC` spelling

A transcription of the pin's `kw_surgehgf4_hfgkd_bc*` block (`A:2501–2839`) at its
prefix-stripped names, `private`, over D-1's `NoAC` primitives.  D-5's landed copy of the same
proof carries `[IsAlgClosed F]` and the four `GenusOnePlaceGate` instances in its section, so
it cannot be instantiated at the subfield `K₀`; this copy has neither.  The `IsDomain`
hypotheses are D-1's gate-free `functionFieldTensorIsDomain_dischargeGeneralNoAC`. -/

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section DescentEngine

variable {R₀ : Type uK} [Field R₀]
variable (E₀ E₀' : WeierstrassCurve R₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (F : Type uK) [Field F] [Algebra R₀ F] [DecidableEq F] [CharZero F]
variable (F' : Type uK) [Field F'] [Algebra R₀ F'] [DecidableEq F'] [CharZero F']
variable [Algebra F F'] [IsScalarTower R₀ F F']
variable [(E₀⁄F).IsElliptic] [(E₀'⁄F).IsElliptic]
variable [(E₀⁄F').IsElliptic] [(E₀'⁄F').IsElliptic]
variable [IsDomain ((E₀⁄F).toAffine.FunctionField ⊗[F] F')]
variable [IsDomain ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')]
variable (ι' : (E₀'⁄F).toAffine.FunctionField →ₐ[F] (E₀⁄F).toAffine.FunctionField)

private def descentBCTensorIota :
    (E₀'⁄F).toAffine.FunctionField ⊗[F] F' →ₐ[F] (E₀⁄F).toAffine.FunctionField ⊗[F] F' :=
  Algebra.TensorProduct.map ι' (AlgHom.id F F')

private theorem descentBCTensorIota_tmul (a : (E₀'⁄F).toAffine.FunctionField) (c : F') :
    descentBCTensorIota E₀ E₀' F F' ι' (a ⊗ₜ[F] c) = (ι' a) ⊗ₜ[F] c := by
  simp [descentBCTensorIota, Algebra.TensorProduct.map_tmul]

private theorem descentBCTensorIota_injective :
    Function.Injective (descentBCTensorIota E₀ E₀' F F' ι') :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := F') ι'.toLinearMap ι'.injective

private def descentBCTensorFracIota :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →+* FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  IsFractionRing.map (K := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
    (L := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))
    (descentBCTensorIota_injective E₀ E₀' F F' ι')

private theorem descentBCTensorFracIota_algebraMap
    (t : (E₀'⁄F).toAffine.FunctionField ⊗[F] F') :
    descentBCTensorFracIota E₀ E₀' F F' ι'
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ t)
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
          (descentBCTensorIota E₀ E₀' F F' ι' t) := by
  unfold descentBCTensorFracIota IsFractionRing.map
  exact IsLocalization.map_eq
    (T := nonZeroDivisors ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ t

private theorem descentBCTensorIota_finite (hfin' : FiniteAlong F ι') :
    (descentBCTensorIota E₀ E₀' F F' ι').toRingHom.Finite :=
  RingHom.Finite.tensorProductMap (f := ι') hfin' (g := AlgHom.id F F')
    (RingHom.Finite.id F')

private def descentBCTensorFracIotaAlg :
    FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
      →ₐ[F'] FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F') :=
  { descentBCTensorFracIota E₀ E₀' F F' ι' with
    commutes' := fun c => by
      show descentBCTensorFracIota E₀ E₀' F F' ι' (algebraMap F' _ c)
          = algebraMap F' _ c
      rw [IsScalarTower.algebraMap_apply F' ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply,
        descentBCTensorFracIota_algebraMap E₀ E₀' F F' ι',
        descentBCTensorIota_tmul, map_one,
        IsScalarTower.algebraMap_apply F' ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
          (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')),
        Algebra.TensorProduct.right_algebraMap_apply] }

/-- The `F'`-base change of an isogeny of function fields, `NoAC` spelling: the pin's
`kw_surgehgf4_hfgkd_bcIota₁NoAC`, transcribed `private` because D-5's landed copy of the same
proof requires `[IsAlgClosed F]` and cannot be instantiated at the subfield `K₀`. -/
private def descentBCIota :
    (E₀'⁄F').toAffine.FunctionField →ₐ[F'] (E₀⁄F').toAffine.FunctionField :=
  let ψE := functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  (ψE.symm.toAlgHom.comp (descentBCTensorFracIotaAlg E₀ E₀' F F' ι')).comp
    ψE'.toAlgHom

private theorem descentBCTensorFracIotaSeam (hfin' : FiniteAlong F ι') :
    (descentBCTensorFracIota E₀ E₀' F F' ι').Finite ∧
    (letI := (descentBCTensorFracIota E₀ E₀' F F' ι').toAlgebra
     @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
       (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule)
      = finrankAlong F ι' := by
  classical
  let FF := (E₀⁄F).toAffine.FunctionField
  let FF' := (E₀'⁄F).toAffine.FunctionField
  let T := (E₀⁄F).toAffine.FunctionField ⊗[F] F'
  let T' := (E₀'⁄F).toAffine.FunctionField ⊗[F] F'
  let FrT := FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
  let FrT' := FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
  let ιT : T' →+* T := (descentBCTensorIota E₀ E₀' F F' ι').toRingHom
  let ιFr : FrT' →+* FrT := descentBCTensorFracIota E₀ E₀' F F' ι'
  have hιT_inj : Function.Injective ιT :=
    descentBCTensorIota_injective E₀ E₀' F F' ι'
  have hιT_fin : ιT.Finite := descentBCTensorIota_finite E₀ E₀' F F' ι' hfin'
  have hιFr_am : ∀ t : T', ιFr (algebraMap T' FrT' t) = algebraMap T FrT (ιT t) :=
    descentBCTensorFracIota_algebraMap E₀ E₀' F F' ι'
  letI algι : Algebra FF' FF := ι'.toRingHom.toAlgebra
  letI modι : Module FF' FF := Algebra.toModule
  have hsmul_ι : ∀ (c : FF') (x : FF), c • x = ι' c * x := fun c x => rfl
  haveI hfinFF : Module.Finite FF' FF := hfin'
  haveI hfreeFF : Module.Free FF' FF := Module.Free.of_divisionRing FF' FF
  let D := finrankAlong F ι'
  let b : Module.Basis (Fin D) FF' FF := Module.finBasisOfFinrankEq FF' FF (n := D) rfl
  have hrepr_mul : ∀ (c : FF') (x : FF) (j : Fin D),
      b.repr (ι' c * x) j = c * b.repr x j := fun c x j => by
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
      have hb_sum : a = ∑ i, ι' (b.repr a i) * b i := by
        conv_lhs => rw [← b.linearCombination_repr a, Finsupp.linearCombination_apply,
          Finsupp.sum_fintype _ _ (fun i => by rw [hsmul_ι, _root_.map_zero, zero_mul])]
        exact Finset.sum_congr rfl fun i _ => hsmul_ι _ _
      calc (a ⊗ₜ[F] c : T)
          = (∑ i, ι' (b.repr a i) * b i) ⊗ₜ[F] c := by rw [← hb_sum]
        _ = ∑ i, ιT ((b.repr a i) ⊗ₜ[F] c) * e i := by
            rw [TensorProduct.sum_tmul]
            refine Finset.sum_congr rfl fun i _ => ?_
            show (ι' (b.repr a i) * b i) ⊗ₜ[F] c = ιT ((b.repr a i) ⊗ₜ[F] c) * e i
            rw [show ιT ((b.repr a i) ⊗ₜ[F] c) = (ι' (b.repr a i)) ⊗ₜ[F] c from
                  descentBCTensorIota_tmul E₀ E₀' F F' ι' _ _,
              Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  have hliT : ∀ c : Fin D → T', ∑ i, ιT (c i) * e i = 0 → ∀ j, c j = 0 := by
    intro c hc j
    let pj : FF →ₗ[F] FF' :=
      { toFun := fun x => b.repr x j
        map_add' := fun x y => by simp only [map_add, Finsupp.add_apply]
        map_smul' := fun f x => by
          simp only [RingHom.id_apply, Algebra.smul_def]
          have h := hrepr_mul (algebraMap F FF' f) x j
          rwa [ι'.commutes] at h }
    let Ej : T →ₗ[F] T' := LinearMap.rTensor F' pj
    have hEj_key : ∀ (a : T') (i : Fin D),
        Ej (ιT a * e i) = if i = j then a else 0 := by
      intro a i
      induction a using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy =>
        simp only [map_add, add_mul, hx, hy]; split_ifs <;> simp
      | tmul x c' =>
        rw [show ιT ((x : FF') ⊗ₜ[F] c') = (ι' x) ⊗ₜ[F] c' from
              descentBCTensorIota_tmul E₀ E₀' F F' ι' _ _,
            Algebra.TensorProduct.tmul_mul_tmul, mul_one]
        show (pj (ι' x * b i)) ⊗ₜ[F] c' = if i = j then (x : FF') ⊗ₜ[F] c' else 0
        rw [show pj (ι' x * b i) = if i = j then x else 0 from ?_]
        · split_ifs with h
          · rfl
          · exact TensorProduct.zero_tmul _ c'
        · show b.repr (ι' x * b i) j = if i = j then x else 0
          rw [hrepr_mul, b.repr_self, Finsupp.single_apply]
          split_ifs with h <;> simp [h]
    have hc' : Ej (∑ i, ιT (c i) * e i) = 0 := by rw [hc, _root_.map_zero]
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
      by rw [_root_.map_neg]; exact eq_neg_of_add_eq_zero_right h3⟩
  have hspanFr : ∀ z : FrT, ∃ d : Fin D → FrT', z = ∑ i, ιFr (d i) * bFr i := by
    intro z
    obtain ⟨t, s, _, rfl⟩ := IsFractionRing.div_surjective (A := T) (K := FrT) z
    rcases eq_or_ne s 0 with rfl | hs'
    · exact ⟨0, by simp⟩
    obtain ⟨u, s₀, hs₀, hsu⟩ := hint s hs'
    have hιTs₀ : ιT s₀ ≠ 0 := fun h => hs₀ (hιT_inj (h.trans (_root_.map_zero ιT).symm))
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
      rw [← hp' j, hpj, _root_.map_zero]
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

private theorem descentBCIota_finiteAlong (hfin' : FiniteAlong F ι') :
    FiniteAlong F' (descentBCIota E₀ E₀' F F' ι') := by
  have hFr_fin := (descentBCTensorFracIotaSeam E₀ E₀' F F' ι' hfin').1
  let ψE := functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  have h1 : RingHom.Finite ψE'.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE'.surjective
  have h2 : RingHom.Finite ψE.symm.toAlgHom.toRingHom :=
    RingHom.Finite.of_surjective _ ψE.symm.surjective
  show RingHom.Finite (descentBCIota E₀ E₀' F F' ι').toRingHom
  have hcomp : (descentBCIota E₀ E₀' F F' ι').toRingHom
      = (ψE.symm.toAlgHom.toRingHom.comp
          (descentBCTensorFracIota E₀ E₀' F F' ι')).comp ψE'.toAlgHom.toRingHom := rfl
  rw [hcomp]
  exact RingHom.Finite.comp (RingHom.Finite.comp h2 hFr_fin) h1

private theorem descentBCIota_isIntegral (hfin' : FiniteAlong F ι') :
    (descentBCIota E₀ E₀' F F' ι').toRingHom.IsIntegral :=
  RingHom.Finite.to_isIntegral
    (show RingHom.Finite (descentBCIota E₀ E₀' F F' ι').toRingHom from
      descentBCIota_finiteAlong E₀ E₀' F F' ι' hfin')

private theorem descentBCIota_finrankAlong (hfin' : FiniteAlong F ι') :
    finrankAlong F' (descentBCIota E₀ E₀' F F' ι') = finrankAlong F ι' := by
  let ψE := functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  let ιFr := descentBCTensorFracIota E₀ E₀' F F' ι'
  have hcomm : ∀ x, ιFr (ψE' x) = ψE (descentBCIota E₀ E₀' F F' ι' x) := fun x => by
    show ιFr (ψE' x) = ψE (ψE.symm (_))
    exact (ψE.apply_symm_apply _).symm
  calc finrankAlong F' (descentBCIota E₀ E₀' F F' ι')
      = (letI := ιFr.toAlgebra
         @Module.finrank (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))
           (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F')) _ _ Algebra.toModule) :=
        @Algebra.finrank_eq_of_equiv_equiv
          (E₀'⁄F').toAffine.FunctionField (E₀⁄F').toAffine.FunctionField _ _
          (algebraAlong (descentBCIota E₀ E₀' F F' ι'))
          _ _ _ _ ιFr.toAlgebra ψE'.toRingEquiv ψE.toRingEquiv (RingHom.ext hcomm)
    _ = finrankAlong F ι' := (descentBCTensorFracIotaSeam E₀ E₀' F F' ι' hfin').2

private theorem descentBCIota_compat (a : (E₀'⁄F).toAffine.FunctionField) :
    descentBCIota E₀ E₀' F F' ι' (functionFieldMapAlongGeneralNoAC E₀' F F' a)
      = functionFieldMapAlongGeneralNoAC E₀ F F' (ι' a) := by
  let ψE := functionFieldTensorFracEquivGeneralNoAC E₀ F F'
  let ψE' := functionFieldTensorFracEquivGeneralNoAC E₀' F F'
  let χE := functionFieldMapAlongGeneralNoAC E₀ F F'
  let χE' := functionFieldMapAlongGeneralNoAC E₀' F F'
  have hκE' : ψE' (χE' a)
      = algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')) := by
    have hκ : ((functionFieldTensorFracHomGeneralNoAC E₀' F F').restrictScalars F).comp χE'
        = (IsScalarTower.toAlgHom F ((E₀'⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀'⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine functionField_algHom_ext ?_ ?_
      · show functionFieldTensorFracHomGeneralNoAC E₀' F F' (χE' _) = _
        rw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
          functionFieldTensorFracHomGeneralNoAC_X]; rfl
      · show functionFieldTensorFracHomGeneralNoAC E₀' F F' (χE' _) = _
        rw [functionFieldMapAlongGeneralNoAC_yGen,
          functionFieldTensorFracHomGeneralNoAC_yGen]; rfl
    exact DFunLike.congr_fun hκ a
  have hκE : ∀ b, ψE.symm (algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _
      (b ⊗ₜ[F] (1 : F'))) = χE b := by
    intro b
    refine ψE.injective ?_
    rw [AlgEquiv.apply_symm_apply]
    have hκ : ((functionFieldTensorFracHomGeneralNoAC E₀ F F').restrictScalars F).comp χE
        = (IsScalarTower.toAlgHom F ((E₀⁄F).toAffine.FunctionField ⊗[F] F')
            (FractionRing ((E₀⁄F).toAffine.FunctionField ⊗[F] F'))).comp
            (Algebra.TensorProduct.includeLeft (R := F)) := by
      refine functionField_algHom_ext ?_ ?_
      · show functionFieldTensorFracHomGeneralNoAC E₀ F F' (χE _) = _
        rw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X,
          functionFieldTensorFracHomGeneralNoAC_X]; rfl
      · show functionFieldTensorFracHomGeneralNoAC E₀ F F' (χE _) = _
        rw [functionFieldMapAlongGeneralNoAC_yGen,
          functionFieldTensorFracHomGeneralNoAC_yGen]; rfl
    exact (DFunLike.congr_fun hκ b).symm
  show ψE.symm (descentBCTensorFracIotaAlg E₀ E₀' F F' ι' (ψE' (χE' a))) = χE (ι' a)
  rw [hκE',
    show descentBCTensorFracIotaAlg E₀ E₀' F F' ι'
        (algebraMap ((E₀'⁄F).toAffine.FunctionField ⊗[F] F') _ (a ⊗ₜ[F] (1 : F')))
      = algebraMap ((E₀⁄F).toAffine.FunctionField ⊗[F] F') _ ((ι' a) ⊗ₜ[F] (1 : F')) from by
        show descentBCTensorFracIota E₀ E₀' F F' ι' _ = _
        rw [descentBCTensorFracIota_algebraMap, descentBCTensorIota_tmul],
    hκE (ι' a)]

end DescentEngine


/-! ## The two-curve descent

The pin's `kw_surgehgf4_hSD_*`: the canonical countable `K₀` generated by the coefficients of
both curves and of `ι X`, `ι yGen`; the descended `xP`, `yP`; the descended isogeny `ι'`; its
integrality, finiteness and degree. -/

section TwoCurveCanonical

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
variable (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)

private def twoCurveGenSet : Set K :=
  ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set K) ∪ {E'.a₁, E'.a₂, E'.a₃, E'.a₄, E'.a₆} ∪
    ↑(iCa_ffCoeffSet E (ι (polyToFunctionField E'.toAffine X))) ∪
    ↑(iCa_ffCoeffSet E (ι (yGen E'.toAffine)))

private theorem twoCurveGenSet_finite : (twoCurveGenSet E E' ι).Finite := by
  unfold twoCurveGenSet
  exact (((((Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _).union
      ((Set.finite_singleton _).insert _ |>.insert _ |>.insert _ |>.insert _)).union
    (Finset.finite_toSet _)).union (Finset.finite_toSet _))

private def twoCurveK₀ : IntermediateField ℚ K :=
  IntermediateField.adjoin ℚ (twoCurveGenSet E E' ι)

private theorem twoCurveK₀_fg : (twoCurveK₀ E E' ι).FG :=
  ⟨(twoCurveGenSet_finite E E' ι).toFinset, by rw [Set.Finite.coe_toFinset]; rfl⟩

private theorem twoCurveK₀_mem_E :
    E.a₁ ∈ twoCurveK₀ E E' ι ∧ E.a₂ ∈ twoCurveK₀ E E' ι ∧
    E.a₃ ∈ twoCurveK₀ E E' ι ∧ E.a₄ ∈ twoCurveK₀ E E' ι ∧ E.a₆ ∈ twoCurveK₀ E E' ι := by
  have h : ({E.a₁, E.a₂, E.a₃, E.a₄, E.a₆} : Set K) ⊆ twoCurveK₀ E E' ι :=
    fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inl (Or.inl hx)))
  exact ⟨h (Or.inl rfl), h (Or.inr (Or.inl rfl)), h (Or.inr (Or.inr (Or.inl rfl))),
    h (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

private theorem twoCurveK₀_mem_E' :
    E'.a₁ ∈ twoCurveK₀ E E' ι ∧ E'.a₂ ∈ twoCurveK₀ E E' ι ∧
    E'.a₃ ∈ twoCurveK₀ E E' ι ∧ E'.a₄ ∈ twoCurveK₀ E E' ι ∧ E'.a₆ ∈ twoCurveK₀ E E' ι := by
  have h : ({E'.a₁, E'.a₂, E'.a₃, E'.a₄, E'.a₆} : Set K) ⊆ twoCurveK₀ E E' ι :=
    fun x hx => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inl (Or.inr hx)))
  exact ⟨h (Or.inl rfl), h (Or.inr (Or.inl rfl)), h (Or.inr (Or.inr (Or.inl rfl))),
    h (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), h (Or.inr (Or.inr (Or.inr (Or.inr rfl))))⟩

private theorem twoCurve_ffCoeffSet_subset_X :
    (↑(iCa_ffCoeffSet E (ι (polyToFunctionField E'.toAffine X))) : Set K)
      ⊆ twoCurveK₀ E E' ι :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inl (Or.inr hc))

private theorem twoCurve_ffCoeffSet_subset_Y :
    (↑(iCa_ffCoeffSet E (ι (yGen E'.toAffine))) : Set K) ⊆ twoCurveK₀ E E' ι :=
  fun _ hc => IntermediateField.subset_adjoin ℚ _ (Or.inr hc)

private def twoCurveE₀ : WeierstrassCurve (twoCurveK₀ E E' ι) where
  a₁ := ⟨E.a₁, (twoCurveK₀_mem_E E E' ι).1⟩
  a₂ := ⟨E.a₂, (twoCurveK₀_mem_E E E' ι).2.1⟩
  a₃ := ⟨E.a₃, (twoCurveK₀_mem_E E E' ι).2.2.1⟩
  a₄ := ⟨E.a₄, (twoCurveK₀_mem_E E E' ι).2.2.2.1⟩
  a₆ := ⟨E.a₆, (twoCurveK₀_mem_E E E' ι).2.2.2.2⟩

private theorem twoCurveE₀_map :
    (twoCurveE₀ E E' ι).map (algebraMap (twoCurveK₀ E E' ι) K) = E := by
  ext <;> rfl

private instance twoCurveE₀_isElliptic : (twoCurveE₀ E E' ι).IsElliptic := by
  constructor; rw [isUnit_iff_ne_zero]; intro h0
  have : (algebraMap (twoCurveK₀ E E' ι) K) (twoCurveE₀ E E' ι).Δ = E.Δ := by
    rw [← WeierstrassCurve.map_Δ, twoCurveE₀_map]
  rw [h0, _root_.map_zero] at this; exact E.isUnit_Δ.ne_zero this.symm

private def twoCurveE₀' : WeierstrassCurve (twoCurveK₀ E E' ι) where
  a₁ := ⟨E'.a₁, (twoCurveK₀_mem_E' E E' ι).1⟩
  a₂ := ⟨E'.a₂, (twoCurveK₀_mem_E' E E' ι).2.1⟩
  a₃ := ⟨E'.a₃, (twoCurveK₀_mem_E' E E' ι).2.2.1⟩
  a₄ := ⟨E'.a₄, (twoCurveK₀_mem_E' E E' ι).2.2.2.1⟩
  a₆ := ⟨E'.a₆, (twoCurveK₀_mem_E' E E' ι).2.2.2.2⟩

private theorem twoCurveE₀'_map :
    (twoCurveE₀' E E' ι).map (algebraMap (twoCurveK₀ E E' ι) K) = E' := by
  ext <;> rfl

private instance twoCurveE₀'_isElliptic : (twoCurveE₀' E E' ι).IsElliptic := by
  constructor; rw [isUnit_iff_ne_zero]; intro h0
  have : (algebraMap (twoCurveK₀ E E' ι) K) (twoCurveE₀' E E' ι).Δ = E'.Δ := by
    rw [← WeierstrassCurve.map_Δ, twoCurveE₀'_map]
  rw [h0, _root_.map_zero] at this; exact E'.isUnit_Δ.ne_zero this.symm

end TwoCurveCanonical


/-! ### Finiteness of a `pointPullbackHomTo` along a transcendental coordinate

D-2's `iPFA_finiteAlong` argument, stated at the abstract carriers `F`/`W`/`L` so that its
instance search is cheap: the ambient context is the three fields and the point, not the
whole two-curve pinned section. -/

section FiniteAlongPointPullback

variable {F : Type uK} [Field F] {W : WeierstrassCurve.Affine F}
variable {L : Type uK} [Field L] [Algebra F L]

private theorem finiteAlong_pointPullbackHomTo
    {xP yP : L} (heq : (W.map (algebraMap F L)).toAffine.Equation xP yP)
    (htr : Function.Injective (Polynomial.aeval (R := F) xP))
    (hfd : FiniteDimensional (↥F⟮xP⟯) L) :
    FiniteAlong F (pointPullbackHomTo (W := W) (L := L) heq htr) := by
  set ι := pointPullbackHomTo (W := W) (L := L) heq htr with hι
  have hxPrange : xP ∈ ι.fieldRange :=
    ⟨polyToFunctionField W X, pointPullbackHomTo_polyToFunctionField_X heq htr⟩
  have hle : (F⟮xP⟯) ≤ ι.fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr hxPrange
  letI algIncl : Algebra (↥F⟮xP⟯) (↥ι.fieldRange) :=
    (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI towIncl : IsScalarTower (↥F⟮xP⟯) (↥ι.fieldRange) L :=
    IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI hfdR : FiniteDimensional (↥ι.fieldRange) L :=
    FiniteDimensional.right (↥F⟮xP⟯) (↥ι.fieldRange) L
  show ι.toRingHom.Finite
  let ρ : W.FunctionField →+* ↥ι.fieldRange :=
    { toFun := fun x => ⟨ι x, x, rfl⟩
      map_one' := Subtype.ext (map_one ι)
      map_mul' := fun a b => Subtype.ext (map_mul ι a b)
      map_zero' := Subtype.ext (_root_.map_zero ι)
      map_add' := fun a b => Subtype.ext (map_add ι a b) }
  have hsurj : Function.Surjective ρ := by rintro ⟨y, x, rfl⟩; exact ⟨x, rfl⟩
  have hfactor : ι.toRingHom
      = (algebraMap (↥ι.fieldRange) L).comp ρ := by ext x; rfl
  rw [hfactor]
  exact RingHom.Finite.comp hfdR (RingHom.Finite.of_surjective _ hsurj)

end FiniteAlongPointPullback


section TwoCurvePinned

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (ι : (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
  →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField)

/-- The coefficient hypothesis of the two-curve descent: the coordinates of `ι X` and
`ι yGen` lie in `K₀` (the pin's `kw_surgehgf4_hSD_CoeffsHyp`). -/
private def twoCurveCoeffsHyp : Prop :=
  (iA_crCoeffsIn E₀ (IsLocalization.sec
      (nonZeroDivisors (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing)
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X))).1
    ∧ iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing)
        (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X))).2 :
      (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing))
  ∧ (iA_crCoeffsIn E₀ (IsLocalization.sec
      (nonZeroDivisors (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing)
      (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine))).1
    ∧ iA_crCoeffsIn E₀ ((IsLocalization.sec (nonZeroDivisors
        (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing)
        (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine))).2 :
      (E₀.map (algebraMap K₀ K)).toAffine.CoordinateRing))

variable (hcoeffs : twoCurveCoeffsHyp E₀ E₀' ι)

private def twoCurve_xP : E₀.toAffine.FunctionField :=
  Classical.choose (iA_ffDescend_exists E₀
    (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X))
    hcoeffs.1.1 hcoeffs.1.2)

private def twoCurve_yP : E₀.toAffine.FunctionField :=
  Classical.choose (iA_ffDescend_exists E₀
    (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine)) hcoeffs.2.1 hcoeffs.2.2)

private theorem twoCurve_xP_spec :
    iA_phi E₀ (twoCurve_xP E₀ E₀' ι hcoeffs)
      = ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X) :=
  Classical.choose_spec (iA_ffDescend_exists E₀ _ hcoeffs.1.1 hcoeffs.1.2)

private theorem twoCurve_yP_spec :
    iA_phi E₀ (twoCurve_yP E₀ E₀' ι hcoeffs)
      = ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine) :=
  Classical.choose_spec (iA_ffDescend_exists E₀ _ hcoeffs.2.1 hcoeffs.2.2)

private theorem twoCurve_equation :
    (E₀'.map (algebraMap K₀ E₀.toAffine.FunctionField)).toAffine.Equation
      (twoCurve_xP E₀ E₀' ι hcoeffs) (twoCurve_yP E₀ E₀' ι hcoeffs) := by
  set xP := twoCurve_xP E₀ E₀' ι hcoeffs with hxP
  set yP := twoCurve_yP E₀ E₀' ι hcoeffs with hyP
  have hι : ((E₀'.map (algebraMap K₀ K)).map
      (algebraMap K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField)).toAffine.Equation
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X))
      (ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine)) := by
    have h₀ := equation_map_polyToFunctionField_yGen (W := (E₀'.map (algebraMap K₀ K)).toAffine)
    rw [Affine.equation_iff] at h₀ ⊢
    have h₁ := congrArg ι h₀
    simp only [map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
      AlgHom.commutes] at h₁ ⊢
    linear_combination h₁
  rw [Affine.equation_iff] at hι ⊢
  have hΦx : iA_phi E₀ xP
      = ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X) :=
    hxP ▸ twoCurve_xP_spec E₀ E₀' ι hcoeffs
  have hΦy : iA_phi E₀ yP = ι (yGen (E₀'.map (algebraMap K₀ K)).toAffine) :=
    hyP ▸ twoCurve_yP_spec E₀ E₀' ι hcoeffs
  have hΦc : ∀ (c : K₀), iA_phi E₀ (algebraMap K₀ E₀.toAffine.FunctionField c)
      = algebraMap K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField (algebraMap K₀ K c) :=
    fun c => ((iA_phi E₀).commutes c).trans
      (IsScalarTower.algebraMap_apply K₀ K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField c)
  have hΦinj : Function.Injective (iA_phi E₀) := (iA_phi E₀).toRingHom.injective
  refine hΦinj ?_
  simp only [map_add, map_mul, map_pow, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at hι ⊢
  rw [hΦc, hΦc, hΦc, hΦc, hΦc, hΦx, hΦy]
  exact hι

private theorem twoCurve_transcendental :
    Function.Injective
      (Polynomial.aeval (R := K₀) (twoCurve_xP E₀ E₀' ι hcoeffs)) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  have hK : Transcendental K
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X)) := by
    intro halg
    obtain ⟨r, hr0, hreval⟩ := halg
    refine (transcendental_polyToFunctionField_X
      (W := (E₀'.map (algebraMap K₀ K)).toAffine)) ⟨r, hr0, ?_⟩
    apply ι.toRingHom.injective
    rw [_root_.map_zero, ← hreval]
    exact (Polynomial.aeval_algHom_apply ι _ r).symm
  have hιX : Transcendental K₀
      (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X)) :=
    hK.restrictScalars (R := K₀) (algebraMap K₀ K).injective
  refine transcendental_iff.mp hιX p ?_
  calc Polynomial.aeval (R := K₀)
        (ι (polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X)) p
      = Polynomial.aeval (R := K₀)
          (iA_phi E₀ (twoCurve_xP E₀ E₀' ι hcoeffs)) p := by
        rw [twoCurve_xP_spec]
    _ = iA_phi E₀ (Polynomial.aeval (R := K₀) (twoCurve_xP E₀ E₀' ι hcoeffs) p) :=
        Polynomial.aeval_algHom_apply (iA_phi E₀) _ p
    _ = iA_phi E₀ 0 := by rw [hp]
    _ = 0 := _root_.map_zero _

/-- The descended two-curve isogeny `ι' : E₀'.FunctionField →ₐ[K₀] E₀.FunctionField`. -/
private def twoCurve_ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField :=
  pointPullbackHomTo (twoCurve_equation E₀ E₀' ι hcoeffs)
    (twoCurve_transcendental E₀ E₀' ι hcoeffs)

private theorem twoCurve_ι'_X :
    twoCurve_ι' E₀ E₀' ι hcoeffs (polyToFunctionField E₀'.toAffine X)
      = twoCurve_xP E₀ E₀' ι hcoeffs :=
  pointPullbackHomTo_polyToFunctionField_X _ _

private theorem twoCurve_ι'_yGen :
    twoCurve_ι' E₀ E₀' ι hcoeffs (yGen E₀'.toAffine)
      = twoCurve_yP E₀ E₀' ι hcoeffs :=
  pointPullbackHomTo_yGen _ _

private theorem twoCurve_phiE'_X :
    iA_phi E₀' (polyToFunctionField E₀'.toAffine X)
      = polyToFunctionField (E₀'.map (algebraMap K₀ K)).toAffine X :=
  pointPullbackHomTo_polyToFunctionField_X _ _

private theorem twoCurve_phiE'_yGen :
    iA_phi E₀' (yGen E₀'.toAffine) = yGen (E₀'.map (algebraMap K₀ K)).toAffine :=
  pointPullbackHomTo_yGen _ _

private theorem twoCurve_phiCompat :
    (ι.restrictScalars K₀).comp (iA_phi E₀')
      = (iA_phi E₀).comp (twoCurve_ι' E₀ E₀' ι hcoeffs) := by
  refine functionField_algHom_ext ?_ ?_
  · show ι (iA_phi E₀' (polyToFunctionField E₀'.toAffine X))
        = iA_phi E₀ (twoCurve_ι' E₀ E₀' ι hcoeffs
            (polyToFunctionField E₀'.toAffine X))
    rw [twoCurve_phiE'_X, twoCurve_ι'_X, twoCurve_xP_spec]
  · show ι (iA_phi E₀' (yGen E₀'.toAffine))
        = iA_phi E₀ (twoCurve_ι' E₀ E₀' ι hcoeffs (yGen E₀'.toAffine))
    rw [twoCurve_phiE'_yGen, twoCurve_ι'_yGen, twoCurve_yP_spec]

private theorem twoCurve_phiCompat_apply (x : E₀'.toAffine.FunctionField) :
    ι (iA_phi E₀' x) = iA_phi E₀ (twoCurve_ι' E₀ E₀' ι hcoeffs x) :=
  DFunLike.congr_fun (twoCurve_phiCompat E₀ E₀' ι hcoeffs) x

private theorem twoCurve_finiteAlong :
    FiniteAlong K₀ (twoCurve_ι' E₀ E₀' ι hcoeffs) :=
  finiteAlong_pointPullbackHomTo (W := E₀'.toAffine) (L := E₀.toAffine.FunctionField)
    (xP := twoCurve_xP E₀ E₀' ι hcoeffs) (yP := twoCurve_yP E₀ E₀' ι hcoeffs)
    (twoCurve_equation E₀ E₀' ι hcoeffs) (twoCurve_transcendental E₀ E₀' ι hcoeffs)
    (iPFA_finiteDimensional_adjoin_transcendental E₀.toAffine
      (transcendental_iff_injective.mpr (twoCurve_transcendental E₀ E₀' ι hcoeffs)))

/-- The two spellings of the descended map agree: `iA_phi` is the pin's
`iotaDescentPhi` at the canonical model (the pin's `kw_surgehgf4_hSD_phi_eq_iotaDescentPhi`). -/
private theorem twoCurve_phi_eq_iotaDescentPhi :
    iA_phi E₀ = iotaDescentPhi (E₀.map (algebraMap K₀ K)) E₀ rfl := by
  refine functionField_algHom_ext ?_ ?_
  · exact (pointPullbackHomTo_polyToFunctionField_X _ _).trans
      (iotaDescentPhi_X _ _ rfl).symm
  · exact (pointPullbackHomTo_yGen _ _).trans (iotaDescentPhi_yGen _ _ rfl).symm

private theorem twoCurve_isIntegral :
    (twoCurve_ι' E₀ E₀' ι hcoeffs).toRingHom.IsIntegral :=
  RingHom.Finite.to_isIntegral
    (f := (twoCurve_ι' E₀ E₀' ι hcoeffs).toRingHom)
    (twoCurve_finiteAlong E₀ E₀' ι hcoeffs)

end TwoCurvePinned


/-! ## The degree of the descended isogeny, and the `iA_phi` ↦ `iotaDescentPhi` bridge -/

section TwoCurveBridge

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ : WeierstrassCurve K₀) [E₀.IsElliptic]

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
private def twoCurve_fχ :
    E₀.toAffine.FunctionField →+* (E₀.map (algebraMap K₀ K)).toAffine.FunctionField :=
  (functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K).toRingHom

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
private theorem twoCurve_fχ_apply (a : E₀.toAffine.FunctionField) :
    twoCurve_fχ E₀ a = functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K a := rfl

attribute [-instance] IntermediateField.instAlgebraSubtypeMem in
private theorem twoCurve_chi_const (r : ↥K₀) :
    functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K
        (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
      = algebraMap K (E₀.map (algebraMap K₀ K)).toAffine.FunctionField
          (algebraMap (↥K₀) K r) := by
  erw [(functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K).commutes r]
  exact IsScalarTower.algebraMap_apply (↥K₀) K (E₀⁄K).FunctionField r

private theorem twoCurve_fχ_eq_phi :
    twoCurve_fχ E₀ = (iA_phi E₀).toRingHom := by
  refine iPFE_functionField_ringHom_ext (F := ↥K₀) (W := E₀.toAffine)
    (f := twoCurve_fχ E₀) (g := (iA_phi E₀).toRingHom) (fun r => ?hF) ?hX ?hy
  case hF =>
    show twoCurve_fχ E₀ (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
      = iA_phi E₀ (algebraMap (↥K₀) E₀.toAffine.FunctionField r)
    rw [(iA_phi E₀).commutes r,
      IsScalarTower.algebraMap_apply (↥K₀) K
        (E₀.map (algebraMap K₀ K)).toAffine.FunctionField,
      twoCurve_fχ_apply, twoCurve_chi_const]
  case hX =>
    show twoCurve_fχ E₀ (polyToFunctionField E₀.toAffine X)
      = iA_phi E₀ (polyToFunctionField E₀.toAffine X)
    rw [twoCurve_fχ_apply]
    erw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X E₀ (↥K₀) K]
  case hy =>
    show twoCurve_fχ E₀ (yGen E₀.toAffine) = iA_phi E₀ (yGen E₀.toAffine)
    rw [twoCurve_fχ_apply]
    erw [functionFieldMapAlongGeneralNoAC_yGen E₀ (↥K₀) K]

private theorem twoCurve_chi_eq_phi_apply (a : E₀.toAffine.FunctionField) :
    functionFieldMapAlongGeneralNoAC E₀ (↥K₀) K a = iA_phi E₀ a := by
  rw [← twoCurve_fχ_apply]
  exact DFunLike.congr_fun (twoCurve_fχ_eq_phi E₀) a

end TwoCurveBridge


section TwoCurveBcIota

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
variable {K₀ : IntermediateField ℚ K}
variable (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
variable (ι : (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
  →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField)
variable (hcoeffs : twoCurveCoeffsHyp E₀ E₀' ι)
variable [DecidableEq (↥K₀)]
variable [CharZero (↥K₀)]
variable [IsDomain ((E₀⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K)]
variable [IsDomain ((E₀'⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K)]

/-- The base change of the descended isogeny is the isogeny it descends: the pin's
`kw_surgehgf4_cfe_bcIota₁NoAC_eq_ι`. -/
private theorem twoCurve_bcIota_eq_ι :
    descentBCIota E₀ E₀' (↥K₀) K (twoCurve_ι' E₀ E₀' ι hcoeffs) = ι := by
  set ι' := twoCurve_ι' E₀ E₀' ι hcoeffs with hι'_def
  refine functionField_algHom_ext ?_ ?_
  · have key : ι (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K
          (polyToFunctionField (E₀'⁄(↥K₀)).toAffine X))
        = descentBCIota E₀ E₀' (↥K₀) K ι'
            (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K
              (polyToFunctionField (E₀'⁄(↥K₀)).toAffine X)) := by
      erw [descentBCIota_compat, twoCurve_chi_eq_phi_apply E₀, twoCurve_chi_eq_phi_apply E₀']
      exact twoCurve_phiCompat_apply E₀ E₀' ι hcoeffs _
    erw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X] at key
    exact key.symm
  · have key : ι (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K
          (yGen (E₀'⁄(↥K₀)).toAffine))
        = descentBCIota E₀ E₀' (↥K₀) K ι'
            (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) K
              (yGen (E₀'⁄(↥K₀)).toAffine)) := by
      erw [descentBCIota_compat, twoCurve_chi_eq_phi_apply E₀, twoCurve_chi_eq_phi_apply E₀']
      exact twoCurve_phiCompat_apply E₀ E₀' ι hcoeffs _
    erw [functionFieldMapAlongGeneralNoAC_yGen] at key
    exact key.symm

private theorem twoCurve_finrankEq :
    finrankAlong K₀ (twoCurve_ι' E₀ E₀' ι hcoeffs) = finrankAlong K ι := by
  have hfin' : FiniteAlong (↥K₀) (twoCurve_ι' E₀ E₀' ι hcoeffs) :=
    twoCurve_finiteAlong E₀ E₀' ι hcoeffs
  have hD2 := descentBCIota_finrankAlong E₀ E₀' (↥K₀) K
    (twoCurve_ι' E₀ E₀' ι hcoeffs) hfin'
  rw [twoCurve_bcIota_eq_ι E₀ E₀' ι hcoeffs] at hD2
  exact hD2.symm

end TwoCurveBcIota


/-! ## The two-curve countable descent, as a port-own declaration -/

section TwoCurveAssembly

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

/-- The pin's `kw_surgehgf4_hSD_ιMpr`: an isogeny of the models casts to an isogeny of the
base-changed models along the two model equalities. -/
private def twoCurve_ιMpr {K₀ : IntermediateField ℚ K}
    (E₀ E₀' : WeierstrassCurve K₀) {W W' : WeierstrassCurve K}
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField) :
    (E₀'.map (algebraMap K₀ K)).toAffine.FunctionField
      →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField :=
  Eq.mpr (congrArg (fun V => V.toAffine.FunctionField
      →ₐ[K] (E₀.map (algebraMap K₀ K)).toAffine.FunctionField) heq')
    (Eq.mpr (congrArg (fun V => W'.toAffine.FunctionField →ₐ[K] V.toAffine.FunctionField) heq) ι)

/-- The pin's `kw_surgehgf4_hSD_coeffsHyp_cast`: the canonical coefficient hypothesis, with
the model equalities substituted away. -/
private theorem twoCurve_coeffsHyp_cast {K₀ : IntermediateField ℚ K}
    (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (hX : (↑(iCa_ffCoeffSet W (ι (polyToFunctionField W'.toAffine X))) : Set K)
      ⊆ (K₀ : Set K))
    (hY : (↑(iCa_ffCoeffSet W (ι (yGen W'.toAffine))) : Set K) ⊆ (K₀ : Set K)) :
    twoCurveCoeffsHyp E₀ E₀' (twoCurve_ιMpr E₀ E₀' heq heq' ι) := by
  subst heq; subst heq'
  refine ⟨⟨fun i j => ?_, fun i j => ?_⟩, fun i j => ?_, fun i j => ?_⟩
  · exact (iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hX i j).1
  · exact (iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hX i j).2
  · exact (iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hY i j).1
  · exact (iCa_crCoeffsIn_of_ffCoeffSet_subset _ _ hY i j).2

/-- The pin's `kw_surgehgf4_hSD_instance_cast`: the two-curve descent at arbitrary models
`W`, `W'` of the base changes, with the compatibility square at the pin's
`iotaDescentPhi`.  The proof `subst`s the two model equalities, so that the whole
development below is stated in the models' `map` spelling. -/
private theorem twoCurveDescentInstance {K₀ : IntermediateField ℚ K}
    (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    [DecidableEq (↥K₀)] [CharZero (↥K₀)]
    [IsDomain ((E₀⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K)]
    [IsDomain ((E₀'⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K)]
    {W W' : WeierstrassCurve K} [W.IsElliptic] [W'.IsElliptic]
    (heq : E₀.map (algebraMap K₀ K) = W) (heq' : E₀'.map (algebraMap K₀ K) = W')
    (ι : W'.toAffine.FunctionField →ₐ[K] W.toAffine.FunctionField)
    (hfg : K₀.FG)
    (hcoeffs : twoCurveCoeffsHyp E₀ E₀' (twoCurve_ιMpr E₀ E₀' heq heq' ι)) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₁ : IntermediateField ℚ K) (_ : K₁.FG)
      (E₁ E₁' : WeierstrassCurve K₁) (_ : E₁.IsElliptic) (_ : E₁'.IsElliptic)
      (hE₁map : E₁.map (algebraMap K₁ K) = W) (hE₁'map : E₁'.map (algebraMap K₁ K) = W')
      (ι' : E₁'.toAffine.FunctionField →ₐ[K₁] E₁.toAffine.FunctionField)
      (_hι' : ι'.toRingHom.IsIntegral) (_hfin' : FiniteAlong K₁ ι')
      (_hfinrank : finrankAlong K₁ ι' = finrankAlong K ι),
      ∀ x : E₁'.toAffine.FunctionField,
        ι (iotaDescentPhi W' E₁' hE₁'map x) = iotaDescentPhi W E₁ hE₁map (ι' x) := by
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  subst heq; subst heq'
  refine ⟨K₀, hfg, E₀, E₀', inferInstance, inferInstance, rfl, rfl,
    twoCurve_ι' E₀ E₀' ι hcoeffs, twoCurve_isIntegral E₀ E₀' ι hcoeffs,
    twoCurve_finiteAlong E₀ E₀' ι hcoeffs,
    twoCurve_finrankEq E₀ E₀' ι hcoeffs, fun x => ?_⟩
  rw [← twoCurve_phi_eq_iotaDescentPhi E₀, ← twoCurve_phi_eq_iotaDescentPhi E₀']
  exact twoCurve_phiCompat_apply E₀ E₀' ι hcoeffs x

/-- **The two-curve countable descent.**  Given an isogeny `ι : E'.FunctionField →
E.FunctionField` between two elliptic curves over an algebraically closed `K` of
characteristic zero, there are a countable subfield `K₀ ≤ K`, models `E₀`, `E₀'` of `E`, `E'`
over `K₀`, and a descended isogeny `ι' : E₀'.FunctionField → E₀.FunctionField` of the same
degree whose base change along `K₀ → K` is `ι` on the descended maps.

D-2 landed this for an endomorphism of one curve; the pin's two-curve case occurs only inside
its `KwD5BetweenCurvesSubfieldDescent` staging `Prop`, so this is a port-own declaration with
a content name (it is listed in `OWN_PROOFS`). -/
theorem exists_twoCurveDescent
    (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
    (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : K₀.FG)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (hE₀map : E₀.map (algebraMap K₀ K) = E) (hE₀'map : E₀'.map (algebraMap K₀ K) = E')
      (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
      (_hι' : ι'.toRingHom.IsIntegral) (_hfin' : FiniteAlong K₀ ι')
      (_hfinrank : finrankAlong K₀ ι' = finrankAlong K ι),
      ∀ x : E₀'.toAffine.FunctionField,
        ι (iotaDescentPhi E' E₀' hE₀'map x) = iotaDescentPhi E E₀ hE₀map (ι' x) := by
  classical
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  set K₀ := twoCurveK₀ E E' ι
  set E₀ := twoCurveE₀ E E' ι
  set E₀' := twoCurveE₀' E E' ι
  haveI : DecidableEq (↥K₀) := Classical.decEq _
  haveI : CharZero (↥K₀) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (↥K₀)).injective
  haveI : E₀.IsElliptic := twoCurveE₀_isElliptic E E' ι
  haveI : E₀'.IsElliptic := twoCurveE₀'_isElliptic E E' ι
  have hmap : E₀.map (algebraMap K₀ K) = E := twoCurveE₀_map E E' ι
  have hmap' : E₀'.map (algebraMap K₀ K) = E' := twoCurveE₀'_map E E' ι
  haveI hdom : IsDomain ((E₀⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K) :=
    functionFieldTensorIsDomain_dischargeGeneralNoAC E₀ (↥K₀) K
  haveI hdom' : IsDomain ((E₀'⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] K) :=
    functionFieldTensorIsDomain_dischargeGeneralNoAC E₀' (↥K₀) K
  have hcoeffs : twoCurveCoeffsHyp E₀ E₀' (twoCurve_ιMpr E₀ E₀' hmap hmap' ι) :=
    twoCurve_coeffsHyp_cast E₀ E₀' hmap hmap' ι
      (twoCurve_ffCoeffSet_subset_X E E' ι) (twoCurve_ffCoeffSet_subset_Y E E' ι)
  exact twoCurveDescentInstance E₀ E₀' hmap hmap' ι (twoCurveK₀_fg E E' ι) hcoeffs

end TwoCurveAssembly


/-! ## The composition of the two base-change maps, and the gate descent -/

section TwoCurveChiCompChiEqPhi

variable {K : Type uK} [Field K] [Algebra ℚ K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

/-- The composition of the two base-change maps of the function field is the descended map:
the pin's `kw_surgehgf4_hfgkd_chiCompChiEqPhi_proved`, at D-2's `iA_phi`. -/
private theorem twoCurve_chiCompChiEqPhi
    {K₀ : IntermediateField ℚ K} (W : WeierstrassCurve K₀) [W.IsElliptic]
    (F₁ : Type uK) [Field F₁] [Algebra (↥K₀) F₁] [DecidableEq F₁] [CharZero F₁]
    [Algebra F₁ K] [IsScalarTower (↥K₀) F₁ K]
    [(W.map (algebraMap (↥K₀) K)).IsElliptic]
    (a : W.toAffine.FunctionField) :
    functionFieldMapAlongGeneralNoAC W F₁ K
      (functionFieldMapAlongGeneralNoAC W (↥K₀) F₁ a)
    = iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl a := by
  have hcomp : ((functionFieldMapAlongGeneralNoAC W F₁ K).restrictScalars (↥K₀)).comp
        (functionFieldMapAlongGeneralNoAC W (↥K₀) F₁)
      = iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl := by
    refine functionField_algHom_ext ?_ ?_
    · show (functionFieldMapAlongGeneralNoAC W F₁ K)
          ((functionFieldMapAlongGeneralNoAC W (↥K₀) F₁)
            (polyToFunctionField W.toAffine X))
        = iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl
            (polyToFunctionField W.toAffine X)
      rw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X W (↥K₀) F₁,
        functionFieldMapAlongGeneralNoAC_polyToFunctionField_X W F₁ K,
        iotaDescentPhi_X (W.map (algebraMap (↥K₀) K)) W rfl]
    · show (functionFieldMapAlongGeneralNoAC W F₁ K)
          ((functionFieldMapAlongGeneralNoAC W (↥K₀) F₁) (yGen W.toAffine))
        = iotaDescentPhi (W.map (algebraMap (↥K₀) K)) W rfl (yGen W.toAffine)
      rw [functionFieldMapAlongGeneralNoAC_yGen W (↥K₀) F₁,
        functionFieldMapAlongGeneralNoAC_yGen W F₁ K,
        iotaDescentPhi_yGen (W.map (algebraMap (↥K₀) K)) W rfl]
  exact DFunLike.congr_fun hcomp a

end TwoCurveChiCompChiEqPhi


section GateDescent

variable {K : Type uK} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]

/-- The pin's `kw_surgehgf4_hfgkd_hKD_of_kerTransport`, with the pin's `s13GlobalGate` lines
removed: the gate instances at the two models over the algebraic closure, and at `E`/`E'`
themselves, are the caller's hypotheses (the headline's own `∀` block). -/
private theorem gateDescent_of_descent
    (E E' : WeierstrassCurve K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.toAffine.FunctionField →ₐ[K] E.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N)
    {K₀ : IntermediateField ℚ K}
    (E₀ E₀' : WeierstrassCurve K₀) [E₀.IsElliptic] [E₀'.IsElliptic]
    (hE₀map : E₀.map (algebraMap K₀ K) = E) (hE₀'map : E₀'.map (algebraMap K₀ K) = E')
    (ι' : E₀'.toAffine.FunctionField →ₐ[K₀] E₀.toAffine.FunctionField)
    (hι' : ι'.toRingHom.IsIntegral) (hfin' : FiniteAlong K₀ ι')
    (hcompat : ∀ x : E₀'.toAffine.FunctionField,
      ι (iotaDescentPhi E' E₀' hE₀'map x) = iotaDescentPhi E E₀ hE₀map (ι' x)) :
    ∃ (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField
        →ₐ[AlgebraicClosure K₀] (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N := by
  subst hE₀map; subst hE₀'map
  haveI : DecidableEq (AlgebraicClosure (↥K₀)) := Classical.decEq _
  haveI : CharZero (AlgebraicClosure (↥K₀)) :=
    charZero_of_injective_algebraMap (algebraMap (↥K₀) (AlgebraicClosure (↥K₀))).injective
  haveI : DecidableEq (↥K₀) := Classical.decEq _
  haveI : CharZero (↥K₀) :=
    charZero_of_injective_algebraMap (algebraMap ℚ (↥K₀)).injective
  haveI hE₀K₀ : (E₀⁄(↥K₀)).IsElliptic := inferInstance
  haveI hE₀'K₀ : (E₀'⁄(↥K₀)).IsElliptic := inferInstance
  haveI hE₀K : (E₀⁄K).IsElliptic := inferInstance
  haveI hE₀'K : (E₀'⁄K).IsElliptic := inferInstance
  haveI hdom : IsDomain ((E₀⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] (AlgebraicClosure (↥K₀))) :=
    functionFieldTensorIsDomain_dischargeGeneralNoAC E₀ (↥K₀) (AlgebraicClosure (↥K₀))
  haveI hdom' : IsDomain ((E₀'⁄(↥K₀)).toAffine.FunctionField ⊗[↥K₀] (AlgebraicClosure (↥K₀))) :=
    functionFieldTensorIsDomain_dischargeGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))
  let ι₀ : (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField
      →ₐ[(AlgebraicClosure (↥K₀))] (E₀⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField :=
    descentBCIota E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι'
  have hι₀ : ι₀.toRingHom.IsIntegral :=
    descentBCIota_isIntegral E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι' hfin'
  have hfin₀ : FiniteAlong (AlgebraicClosure (↥K₀)) ι₀ :=
    descentBCIota_finiteAlong E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι' hfin'
  haveI : Module.IsTorsionFree (↥K₀) K :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr (algebraMap (↥K₀) K).injective
  let τ : (AlgebraicClosure (↥K₀)) →ₐ[↥K₀] K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure (↥K₀)) K := τ.toRingHom.toAlgebra
  haveI : IsScalarTower (↥K₀) (AlgebraicClosure (↥K₀)) K :=
    IsScalarTower.of_algebraMap_eq fun r => (τ.commutes r).symm
  have hD3 : ∀ a, ι₀ (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = functionFieldMapAlongGeneralNoAC E₀ (↥K₀) (AlgebraicClosure (↥K₀)) (ι' a) :=
    fun a => descentBCIota_compat E₀ E₀' (↥K₀) (AlgebraicClosure (↥K₀)) ι' a
  have hχΦE : ∀ a : E₀.toAffine.FunctionField,
      functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K
        (functionFieldMapAlongGeneralNoAC E₀ (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = iotaDescentPhi (E₀.map (algebraMap (↥K₀) K)) E₀ rfl a :=
    fun a => twoCurve_chiCompChiEqPhi E₀ (AlgebraicClosure (↥K₀)) a
  have hχΦE' : ∀ a : E₀'.toAffine.FunctionField,
      functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K
        (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀)) a)
      = iotaDescentPhi (E₀'.map (algebraMap (↥K₀) K)) E₀' rfl a :=
    fun a => twoCurve_chiCompChiEqPhi E₀' (AlgebraicClosure (↥K₀)) a
  have hχ : ∀ x : (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField,
      ι (functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K x)
        = functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K (ι₀ x) := by
    have hext := iPFE_functionField_ringHom_ext
      (F := AlgebraicClosure (↥K₀)) (W := (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine)
      (f := ι.toRingHom.comp
        (functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K).toRingHom)
      (g := (functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K).toRingHom.comp
        ι₀.toRingHom)
      (fun r => by
        have h1 : ι (functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K
            (algebraMap (AlgebraicClosure (↥K₀))
              (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField r))
            = algebraMap (AlgebraicClosure (↥K₀))
                (E₀⁄K).toAffine.FunctionField r := by
          rw [(functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K).commutes r,
            IsScalarTower.algebraMap_apply (AlgebraicClosure (↥K₀)) K
              ((E₀'⁄K).toAffine.FunctionField) r]
          exact (ι.commutes _).trans (IsScalarTower.algebraMap_apply (AlgebraicClosure (↥K₀)) K
            ((E₀⁄K).toAffine.FunctionField) r).symm
        have h2 : functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K
            (ι₀ (algebraMap (AlgebraicClosure (↥K₀))
              (E₀'⁄(AlgebraicClosure (↥K₀))).toAffine.FunctionField r))
            = algebraMap (AlgebraicClosure (↥K₀))
                (E₀⁄K).toAffine.FunctionField r := by
          rw [ι₀.commutes r,
            (functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K).commutes r]
        exact h1.trans h2.symm)
      (by
        have key : ι (functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K
            (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))
              (polyToFunctionField (E₀'⁄(↥K₀)).toAffine X)))
            = functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K
              (ι₀ (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))
                (polyToFunctionField (E₀'⁄(↥K₀)).toAffine X))) := by
          erw [hD3, hχΦE, hχΦE']; exact hcompat _
        erw [functionFieldMapAlongGeneralNoAC_polyToFunctionField_X] at key
        exact key)
      (by
        have key : ι (functionFieldMapAlongGeneralNoAC E₀' (AlgebraicClosure (↥K₀)) K
            (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))
              (yGen (E₀'⁄(↥K₀)).toAffine)))
            = functionFieldMapAlongGeneralNoAC E₀ (AlgebraicClosure (↥K₀)) K
              (ι₀ (functionFieldMapAlongGeneralNoAC E₀' (↥K₀) (AlgebraicClosure (↥K₀))
                (yGen (E₀'⁄(↥K₀)).toAffine))) := by
          erw [hD3, hχΦE, hχΦE']; exact hcompat _
        erw [functionFieldMapAlongGeneralNoAC_yGen] at key
        exact key)
    exact fun x => DFunLike.congr_fun hext x
  refine ⟨ι₀, hι₀, hfin₀, ?_⟩
  intro instDec gE gEC ga gE' gEC' ga' hN₀
  have hcyc' : IsAddCyclic (pointMapOfPushforward ι hι hfin
      (normFormulaAlong_of_elliptic ι hfin)).ker :=
    (Subsingleton.elim hN (normFormulaAlong_of_elliptic ι hfin)) ▸ hcyc
  have hcard' : Nat.card (pointMapOfPushforward ι hι hfin
      (normFormulaAlong_of_elliptic ι hfin)).ker = N :=
    (Subsingleton.elim hN (normFormulaAlong_of_elliptic ι hfin)) ▸ hcard
  have hKT := kerTransport_s17 (↥K₀) E₀ E₀' (AlgebraicClosure (↥K₀)) K ι₀ hι₀ hfin₀
    ι hι hfin hχ N hcyc' hcard'
  rw [show hN₀ = normFormulaAlong_of_elliptic ι₀ hfin₀ from Subsingleton.elim _ _]
  exact hKT

end GateDescent

end ModularCurve


namespace WeierstrassCurve
namespace Affine

/-- **The two-curve countable descent, with the gate data quantified.**  Given an isogeny
`ι : E'.FunctionField → E.FunctionField` of elliptic curves over an algebraically closed `K`
of characteristic zero whose point-map kernel is cyclic of cardinality `N`, there are a
countable `K₀ ≤ K` and models over `K₀` such that, *for every admissible gate datum on the
base-changed curves over `AlgebraicClosure K₀`*, the descended isogeny's kernel is again
cyclic of cardinality `N`. -/
theorem exists_intermediateField_countable_map_eq_of_isAddCyclic_ker_pointMapOfPushforward
    {K : Type u} [Field K] [DecidableEq K] [IsAlgClosed K] [CharZero K]
    (E E' : WeierstrassCurve.Affine K) [E.IsElliptic] [E'.IsElliptic]
    [GenusOnePlaceGate E] [GenusOnePlaceGate.IsCentred E] [AbelTheorem E]
    [GenusOnePlaceGate E'] [GenusOnePlaceGate.IsCentred E'] [AbelTheorem E']
    (ι : E'.FunctionField →ₐ[K] E.FunctionField) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι)
    (hN : NormFormulaAlong K ι hfin) (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    letI : Algebra ℚ K := DivisionRing.toRatAlgebra
    ∃ (K₀ : IntermediateField ℚ K) (_ : Countable K₀)
      (E₀ E₀' : WeierstrassCurve K₀) (_ : E₀.IsElliptic) (_ : E₀'.IsElliptic)
      (_ : E₀.map (algebraMap K₀ K) = E) (_ : E₀'.map (algebraMap K₀ K) = E')
      (_ : (E₀.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (_ : (E₀'.baseChange (AlgebraicClosure K₀)).IsElliptic)
      (ι₀ : (E₀'.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField →ₐ[AlgebraicClosure K₀]
        (E₀.baseChange (AlgebraicClosure K₀)).toAffine.FunctionField)
      (hι₀ : ι₀.toRingHom.IsIntegral) (hfin₀ : FiniteAlong (AlgebraicClosure K₀) ι₀),
      ∀ [DecidableEq (AlgebraicClosure K₀)]
        [GenusOnePlaceGate (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [GenusOnePlaceGate.IsCentred (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        [AbelTheorem (E₀'.baseChange (AlgebraicClosure K₀)).toAffine]
        (hN₀ : NormFormulaAlong (AlgebraicClosure K₀) ι₀ hfin₀),
        IsAddCyclic (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker ∧
          Nat.card (pointMapOfPushforward ι₀ hι₀ hfin₀ hN₀).ker = N := by
  classical
  letI : Algebra ℚ K := DivisionRing.toRatAlgebra
  obtain ⟨K₀, hFG, E₀, E₀', hE₀ell, hE₀'ell, hE₀map, hE₀'map, ι', hι', hfin', _hfinrank,
    hcompat⟩ := ModularCurve.exists_twoCurveDescent E E' ι hι hfin
  haveI : Countable (↥K₀) := ModularCurve.iotaSubd_countable_of_fg hFG
  haveI : E₀.IsElliptic := hE₀ell
  haveI : E₀'.IsElliptic := hE₀'ell
  obtain ⟨ι₀, hι₀, hfin₀, hgate⟩ :=
    ModularCurve.gateDescent_of_descent E E' ι hι hfin hN N hcyc hcard
      E₀ E₀' hE₀map hE₀'map ι' hι' hfin' hcompat
  exact ⟨K₀, inferInstance, E₀, E₀', hE₀ell, hE₀'ell, hE₀map, hE₀'map,
    inferInstance, inferInstance, ι₀, hι₀, hfin₀, hgate⟩

end Affine
end WeierstrassCurve

end
