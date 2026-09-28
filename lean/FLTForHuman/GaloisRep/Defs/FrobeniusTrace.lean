/-
  Frobenius traces on torsion: the `ZMod n`-linearity of the Galois action
  (`SMulCommClass`), the representation `galoisRepModuleEnd : G → End_{ℤ/n}(E[n])`,
  its trace `galoisTrace`, and `IsFrobeniusAt` — an arithmetic Frobenius at
  a place, acting on the residue field by `x ↦ x^q`.

  Transcribed verbatim from `Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
  (pinned `aa2d8b3`, 66 lines). The mathematics is math/018 §1.4.
-/
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Valuation.RamificationGroup
import FLTForHuman.GaloisRep.Defs.GaloisAction
import FLTForHuman.GaloisRep.Defs.Ramification

set_option autoImplicit false

noncomputable section

open scoped WeierstrassCurve.Affine

namespace WeierstrassCurve.Affine.Point

universe r s v

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul (DistribSMul.toAddMonoidHom (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

variable (S) in

def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    (K ≃ₐ[S] K) →* Module.End (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)

@[simp] lemma galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K)
    (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd S W' n σ x = σ • x :=
  rfl

variable (S) in

def galoisTrace (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) : ZMod n :=
  LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) (galoisRepModuleEnd S W' n σ)

lemma galoisTrace_def (W' : Affine R) (n : ℕ) (σ : K ≃ₐ[S] K) :
    galoisTrace S W' n σ =
      LinearMap.trace (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd S W' n σ) :=
  rfl

end WeierstrassCurve.Affine.Point

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsFrobeniusAt (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q : ℕ) : Prop :=
  ∃ hσ : σ ∈ A.decompositionSubgroup K,
    ∀ x : IsLocalRing.ResidueField A, (⟨σ, hσ⟩ : A.decompositionSubgroup K) • x = x ^ q

lemma IsFrobeniusAt.mem_decompositionSubgroup {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) : σ ∈ A.decompositionSubgroup K :=
  h.choose

lemma IsFrobeniusAt.smul_residue_eq {A : ValuationSubring L} {σ : L ≃ₐ[K] L} {q : ℕ}
    (h : A.IsFrobeniusAt σ q) (x : IsLocalRing.ResidueField A) :
    (⟨σ, h.mem_decompositionSubgroup⟩ : A.decompositionSubgroup K) • x = x ^ q :=
  h.choose_spec x

end ValuationSubring

end
