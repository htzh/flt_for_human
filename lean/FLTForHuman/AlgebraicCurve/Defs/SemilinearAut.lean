/-
The `K`-semilinear automorphism group `SemilinearAut K F` and its action on
places, after FLT's `Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean` lines
15–206
(<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AlgebraicCurve_BaseChangeGalois.lean>).

The Divisor/`Pic0` action-and-torsion section (lines 206–356) is **deferred, with
this module as its decided home**: the `SMul (SemilinearAut K F) (Pic0 K F)`
instance and `SemilinearAut.torsionRep` belong here, consumed by
`ModularCurve/Defs/ArithmeticGalois.lean`. It is API for the modular
Hecke/Galois-representation layer, not for the exchange cone
(`TOPIC-ac0-vocabulary.md` §2.6); the port does not need it yet. The
`F ≃ₐ[K] F`-action on `Place K F` **is** restored here, since the Fricke
vocabulary needs it (mc-retrospective §8 item 3).
-/
import FLTForHuman.AlgebraicCurve.Defs.Place
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
mc-retrospective §8 item 3 moved it to its AC home. -/
instance : SMul (F ≃ₐ[K] F) (Place K F) where
  smul σ v := ofAlgAut σ • v

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

end AlgebraicCurve
