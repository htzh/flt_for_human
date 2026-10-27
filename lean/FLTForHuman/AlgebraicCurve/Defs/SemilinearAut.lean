/-
The `K`-semilinear automorphism group `SemilinearAut K F` and its action on
places, after FLT's `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean` lines
15–206
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean>).

The Divisor/`Pic0` action (lines 206–290) is ported here as of the W5 jH-descent
wave, whose headline *states* `g • x` for `x : Pic0`; the `F ≃ₐ[K] F`-action on
`Place K F` is also restored here, since the Fricke vocabulary needs it
(mc-retrospective §8 item 3). The torsion/`ZMod`-module/`torsionRep` part of the
same pin section (lines 290–356) **remains deferred to this module**, consumed by
`ModularCurve/Defs/ArithmeticGalois.lean`: it is API for the modular
Hecke/Galois-representation layer, not for the exchange cone
(`TOPIC-ac0-vocabulary.md` §2.6), and the port does not need it yet.
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.Divisor
import Mathlib.Algebra.Ring.Action.End
import Mathlib.LinearAlgebra.Dimension.Finrank

set_option autoImplicit false

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

def SemilinearAut : Subgroup (RingAut F × RingAut K) where
  carrier := {p | ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a)}
  one_mem' _ := rfl
  mul_mem' := fun {p q} hp hq a => by
    show p.1 (q.1 (algebraMap K F a)) = algebraMap K F (p.2 (q.2 a))
    rw [hq a, hp (q.2 a)]
  inv_mem' := fun {p} hp a => by
    show p.1.symm (algebraMap K F a) = algebraMap K F (p.2.symm a)
    apply p.1.injective
    rw [RingEquiv.apply_symm_apply, hp (p.2.symm a), RingEquiv.apply_symm_apply]

namespace SemilinearAut

variable {K F}

theorem mem_iff {p : RingAut F × RingAut K} :
    p ∈ SemilinearAut K F ↔ ∀ a : K, p.1 (algebraMap K F a) = algebraMap K F (p.2 a) :=
  Iff.rfl

def toRingAut (g : SemilinearAut K F) : F ≃+* F := g.val.1

def baseAut (g : SemilinearAut K F) : K ≃+* K := g.val.2

theorem commutes (g : SemilinearAut K F) (a : K) :
    toRingAut g (algebraMap K F a) = algebraMap K F (baseAut g a) :=
  g.prop a

@[simp] theorem toRingAut_one : toRingAut (1 : SemilinearAut K F) = 1 := rfl

@[simp] theorem baseAut_one : baseAut (1 : SemilinearAut K F) = 1 := rfl

@[simp] theorem toRingAut_mul (g h : SemilinearAut K F) :
    toRingAut (g * h) = toRingAut g * toRingAut h := rfl

@[simp] theorem baseAut_mul (g h : SemilinearAut K F) :
    baseAut (g * h) = baseAut g * baseAut h := rfl

@[simp] theorem toRingAut_inv (g : SemilinearAut K F) :
    toRingAut g⁻¹ = (toRingAut g).symm := rfl

@[simp] theorem baseAut_inv (g : SemilinearAut K F) :
    baseAut g⁻¹ = (baseAut g).symm := rfl

instance : MulSemiringAction (SemilinearAut K F) F where
  smul g x := toRingAut g x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero g := map_zero (toRingAut g)
  smul_add g := map_add (toRingAut g)
  smul_one g := map_one (toRingAut g)
  smul_mul g := map_mul (toRingAut g)

@[simp]
theorem smul_def (g : SemilinearAut K F) (x : F) : g • x = toRingAut g x := rfl

theorem inv_smul_def (g : SemilinearAut K F) (x : F) : g⁻¹ • x = (toRingAut g).symm x := rfl

theorem smul_algebraMap (g : SemilinearAut K F) (a : K) :
    g • algebraMap K F a = algebraMap K F (baseAut g a) :=
  commutes g a

def ofAlgAut : (F ≃ₐ[K] F) →* SemilinearAut K F where
  toFun σ := ⟨((σ : F ≃+* F), 1), fun a => by simp⟩
  map_one' := Subtype.ext (by ext <;> rfl)
  map_mul' σ τ := Subtype.ext (by ext <;> rfl)

@[simp]
theorem toRingAut_ofAlgAut (σ : F ≃ₐ[K] F) : toRingAut (ofAlgAut σ) = (σ : F ≃+* F) := rfl

@[simp]
theorem baseAut_ofAlgAut (σ : F ≃ₐ[K] F) : baseAut (ofAlgAut σ) = 1 := rfl

@[simp]
theorem ofAlgAut_smul (σ : F ≃ₐ[K] F) (x : F) : ofAlgAut σ • x = σ x := rfl

end SemilinearAut

namespace SemilinearAut

open scoped Pointwise

variable {K F}
variable (g : SemilinearAut K F)

theorem pointwise_smul_top : g • (⊤ : ValuationSubring F) = ⊤ := by
  ext x
  simp only [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun _ => ValuationSubring.mem_top x, fun _ => ValuationSubring.mem_top _⟩

def smulValuationSubringEquiv (A : ValuationSubring F) :
    A ≃+* (g • A : ValuationSubring F) where
  toFun x := ⟨g • (x : F), ValuationSubring.smul_mem_pointwise_smul g (x : F) A x.2⟩
  invFun y := ⟨g⁻¹ • (y : F),
    (ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem (g := g) (S := A)
      (x := (y : F))).mp y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

@[simp]
theorem coe_smulValuationSubringEquiv_apply (A : ValuationSubring F) (x : A) :
    ((smulValuationSubringEquiv g A x : (g • A : ValuationSubring F)) : F) = g • (x : F) :=
  rfl

instance : SMul (SemilinearAut K F) (Place K F) where
  smul g v :=
    { toValuationSubring := g • v.toValuationSubring
      algebraMap_mem' := fun a => by
        have h := ValuationSubring.smul_mem_pointwise_smul g
          (algebraMap K F ((baseAut g).symm a)) v.toValuationSubring
          (v.algebraMap_mem' ((baseAut g).symm a))
        rwa [smul_algebraMap, RingEquiv.apply_symm_apply] at h
      ne_top' := fun h => v.ne_top' <| by
        have h2 := congrArg (g⁻¹ • ·) h
        simpa [pointwise_smul_top] using h2
      isPrincipalIdealRing' :=
        IsPrincipalIdealRing.of_surjective
          (smulValuationSubringEquiv g v.toValuationSubring : _ ≃+* _)
          (smulValuationSubringEquiv g v.toValuationSubring).surjective }

variable (v : Place K F)

@[simp]
theorem smul_toValuationSubring : (g • v).toValuationSubring = g • v.toValuationSubring :=
  rfl

instance : MulAction (SemilinearAut K F) (Place K F) where
  one_smul v := by
    ext1
    rw [smul_toValuationSubring, one_smul]
  mul_smul g h v := by
    ext1
    simp only [smul_toValuationSubring]
    rw [mul_smul]

/-- The `F ≃ₐ[K] F`-action on `Place K F`, through `ofAlgAut`. The pin states it
directly on the pointwise smul of the valuation subring
(`Def_AlgebraicCurve_DivisorClassGroup.lean:285`); this is the same action routed
through the ported `ofAlgAut`, and it is the only place-smul the Fricke
vocabulary needs. It lived in `ModularCurve/Defs/AtkinLehner.lean` until
mc-retrospective §8 item 3 moved it to its AC home. Promoted from a `private`
`SMul`/`MulAction` pair in `P1/DXCoeff.lean` to this single public home in the P3.2
refactor round (R3), together with the `Divisor` action below. -/
instance : MulAction (F ≃ₐ[K] F) (Place K F) where
  smul σ v := ofAlgAut σ • v
  one_smul v := by
    show ofAlgAut (1 : F ≃ₐ[K] F) • v = v
    rw [map_one, one_smul]
  mul_smul σ τ v := by
    show ofAlgAut (σ * τ) • v = ofAlgAut σ • (ofAlgAut τ • v)
    rw [map_mul, mul_smul]

theorem ord_smul (f : F) : (g • v).ord (g • f) = v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ

  set n := v.ord f with hn

  set e := smulValuationSubringEquiv g v.toValuationSubring with he
  have hπ' : Irreducible (e π) := (MulEquiv.irreducible_iff e).mpr hπ
  have hu' : IsUnit (e (u : v.toValuationSubring)) := u.isUnit.map e
  have hcoeu : ((hu'.unit : (g • v).toValuationSubring) : F)
      = toRingAut g ((u : v.toValuationSubring) : F) := by
    rw [IsUnit.unit_spec]
    rfl
  have hcoeπ : ((e π : (g • v).toValuationSubring) : F) = toRingAut g (π : F) := rfl
  have key : toRingAut g f = ((hu'.unit : (g • v).toValuationSubring) : F)
      * (((e π : (g • v).toValuationSubring) : F) ^ n) := by
    rw [hcoeu, hcoeπ, hu, map_mul, map_zpow₀]
  rw [show g • f = toRingAut g f from rfl, key,
    (g • v).ord_unit_smul_zpow hu'.unit hπ' n]

def smulResidueRingEquiv : v.ResidueField ≃+* (g • v).ResidueField :=
  IsLocalRing.ResidueField.mapEquiv (smulValuationSubringEquiv g v.toValuationSubring)

theorem smulResidueRingEquiv_algebraMap (a : K) :
    smulResidueRingEquiv g v (algebraMap K v.ResidueField a)
      = algebraMap K (g • v).ResidueField (baseAut g a) := by
  have h3 : (smulValuationSubringEquiv g v.toValuationSubring)
        (algebraMap K v.toValuationSubring a)
      = algebraMap K (g • v).toValuationSubring (baseAut g a) := by
    ext
    rw [coe_smulValuationSubringEquiv_apply, Place.coe_algebraMap, smul_algebraMap]
    exact (Place.coe_algebraMap (g • v) (baseAut g a)).symm
  show IsLocalRing.ResidueField.mapEquiv _ (IsLocalRing.residue _ _) = IsLocalRing.residue _ _
  rw [IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue]
  exact congrArg _ h3

@[simp]
theorem deg_smul : (g • v).deg = v.deg := by
  refine (Algebra.finrank_eq_of_equiv_equiv (baseAut g) (smulResidueRingEquiv g v) ?_).symm
  ext a
  simpa using (smulResidueRingEquiv_algebraMap g v a).symm

end SemilinearAut

section AlgEquivDivisorAction

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (σ : F ≃ₐ[K] F) (v : Place K F)

/-- Pin `Place.ord_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:314`),
at the `F ≃ₐ[K] F` level through `ofAlgAut`. Promoted from `P1/DXCoeff.lean` in the
P3.2 refactor round (R3). -/
theorem ord_smul (f : F) : (σ • v).ord (σ f) = v.ord f := by
  change (SemilinearAut.ofAlgAut σ • v).ord (SemilinearAut.ofAlgAut σ • f) = v.ord f
  exact SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) v f

/-- Pin `Place.deg_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:348`). -/
theorem deg_smul : (σ • v).deg = v.deg := by
  change (SemilinearAut.ofAlgAut σ • v).deg = v.deg
  exact SemilinearAut.deg_smul (SemilinearAut.ofAlgAut σ) v

end Place

namespace Divisor

/-- Pin `Divisor` instance (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:359`). -/
instance : DistribMulAction (F ≃ₐ[K] F) (Divisor K F) :=
  Finsupp.comapDistribMulAction

/-- Pin `Divisor.smul_def` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:361`). -/
theorem smul_def (σ : F ≃ₐ[K] F) (D : Divisor K F) :
    σ • D = Finsupp.mapDomain (σ • ·) D := rfl

/-- Pin `Divisor.smul_single` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:364`). -/
@[simp]
theorem smul_single (σ : F ≃ₐ[K] F) (v : Place K F) (n : ℤ) :
    σ • Finsupp.single v n = Finsupp.single (σ • v) n := by
  rw [smul_def, Finsupp.mapDomain_single]

/-- Pin `Divisor.smul_apply_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:369`). -/
theorem smul_apply_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) (v : Place K F) :
    (σ • D) (σ • v) = D v := by
  rw [smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective σ) D v

/-- Pin `Divisor.smul_apply` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:374`). -/
theorem smul_apply (σ : F ≃ₐ[K] F) (D : Divisor K F) (w : Place K F) :
    (σ • D) w = D (σ⁻¹ • w) := by
  have : (σ • D) (σ • (σ⁻¹ • w)) = D (σ⁻¹ • w) := smul_apply_smul σ D (σ⁻¹ • w)
  rwa [smul_inv_smul] at this

/-- Pin `Divisor.degree_smul` (`Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:380`). -/
@[simp]
theorem degree_smul (σ : F ≃ₐ[K] F) (D : Divisor K F) : degree (σ • D) = degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, degree_single, degree_single,
        Place.deg_smul]

end Divisor

end AlgEquivDivisorAction


namespace SemilinearAut

/-! ## The `SemilinearAut` action on divisors and `Pic⁰`

The pin's `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean` lines 206–290: the
`DistribMulAction` on `Divisor K F` (by `Finsupp.comapDistribMulAction`), its order and
degree laws, and the induced `SMul`/`DistribMulAction` on `Pic0 K F`.  Ported when the W5
jH-descent headline needed `g • x` in its statement (`g : SemilinearAut`, `x : Pic0`);
the torsion/`ZMod`-module/`torsionRep` part of the same pin section is still deferred to
this module. -/

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

instance divisorDistribMulAction : DistribMulAction (SemilinearAut K F) (Divisor K F) :=
  Finsupp.comapDistribMulAction

theorem divisor_smul_def (g : SemilinearAut K F) (D : Divisor K F) :
    g • D = Finsupp.mapDomain (g • ·) D := rfl

@[simp]
theorem smul_single (g : SemilinearAut K F) (v : Place K F) (n : ℤ) :
    g • Finsupp.single v n = Finsupp.single (g • v) n := by
  rw [divisor_smul_def, Finsupp.mapDomain_single]

theorem divisor_smul_apply_smul (g : SemilinearAut K F) (D : Divisor K F)
    (v : Place K F) : (g • D) (g • v) = D v := by
  rw [divisor_smul_def]
  exact Finsupp.mapDomain_apply_of_injective (MulAction.injective g) D v

theorem divisor_smul_apply (g : SemilinearAut K F) (D : Divisor K F)
    (w : Place K F) : (g • D) w = D (g⁻¹ • w) := by
  have h := divisor_smul_apply_smul g D (g⁻¹ • w)
  rwa [smul_inv_smul] at h

@[simp]
theorem degree_smul (g : SemilinearAut K F) (D : Divisor K F) :
    Divisor.degree (g • D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
      rw [smul_add, map_add, map_add, ih, smul_single, Divisor.degree_single,
        Divisor.degree_single, deg_smul]

theorem smul_mem_degZero (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.degZero (K := K) (F := F)) :
    g • D ∈ Divisor.degZero (K := K) (F := F) := by
  rw [Divisor.mem_degZero] at hD ⊢
  rw [degree_smul, hD]

theorem smul_mem_principal (g : SemilinearAut K F) {D : Divisor K F}
    (hD : D ∈ Divisor.principal (K := K) (F := F)) :
    g • D ∈ Divisor.principal (K := K) (F := F) := by
  obtain ⟨f, hf, hD⟩ := hD
  refine ⟨g • f, ?_, fun w => ?_⟩
  · intro h
    refine hf ?_
    have h' := congrArg (g⁻¹ • ·) h
    simpa using h'
  · rw [divisor_smul_apply, hD (g⁻¹ • w)]
    have h := ord_smul g (g⁻¹ • w) f
    rw [smul_inv_smul] at h
    exact h.symm

def degZeroSMulHom (g : SemilinearAut K F) :
    Divisor.degZero (K := K) (F := F) →+ Divisor.degZero (K := K) (F := F) where
  toFun D := ⟨g • (D : Divisor K F), smul_mem_degZero g D.2⟩
  map_zero' := Subtype.ext (by simp)
  map_add' D E := Subtype.ext (by simp [smul_add])

@[simp]
theorem coe_degZeroSMulHom (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) :
    (degZeroSMulHom g D : Divisor K F) = g • (D : Divisor K F) := rfl

instance pic0SMul : SMul (SemilinearAut K F) (Pic0 K F) where
  smul g := QuotientAddGroup.map _ _ (degZeroSMulHom g) (by
    rintro ⟨D, hD0⟩ hD
    simp only [AddSubgroup.mem_addSubgroupOf] at hD ⊢
    exact smul_mem_principal g hD)

theorem pic0_smul_mk (g : SemilinearAut K F)
    (D : Divisor.degZero (K := K) (F := F)) :
    g • (Pic0.mk D) = Pic0.mk (degZeroSMulHom g D) := rfl

instance pic0DistribMulAction : DistribMulAction (SemilinearAut K F) (Pic0 K F) where
  one_smul x := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by rw [coe_degZeroSMulHom, one_smul]))
  mul_smul g h x := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    rw [pic0_smul_mk, pic0_smul_mk, pic0_smul_mk]
    exact congrArg Pic0.mk (Subtype.ext (by simp only [coe_degZeroSMulHom]; rw [mul_smul]))
  smul_zero g := by
    show g • Pic0.mk 0 = Pic0.mk 0
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (map_zero _)
  smul_add g x y := by
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    show g • Pic0.mk (D + E) = Pic0.mk (degZeroSMulHom g D) + Pic0.mk (degZeroSMulHom g E)
    rw [pic0_smul_mk]
    exact congrArg Pic0.mk (map_add _ _ _)

end SemilinearAut

end AlgebraicCurve
