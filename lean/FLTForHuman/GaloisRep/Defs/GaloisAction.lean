/-
  The Galois action on the torsion points of an affine Weierstrass curve: the
  `K ≃ₐ[S] K`-action on `(W'⁄K).Point`, its restriction to the `n`-torsion
  `Submodule.torsionBy ℤ (W'⁄K).Point n`, stability of submodules, and
  irreducibility of the resulting representation.

  Transcribed verbatim from `Definitions/Def_FLTPrelim_GaloisRep.lean` (pinned
  `aa2d8b3`, 83 lines); mathlib-only, exactly as the pin. The mathematics is
  math/018 §1.2. The pin's `instModuleZModTorsionBy` is kept for its name and
  statement, but its *value* is mathlib's `AddSubgroup.torsionBy.zmodModule`
  (playbook §4): typeclass search does not reach that instance through the
  `Submodule.torsionBy` carrier, so the instance is restated at the pin's
  carrier with the mathlib proof.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

universe r s v

namespace WeierstrassCurve.Affine.Point

open WeierstrassCurve

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R] [CommRing S] [Field K]
  [DecidableEq K] {W' : Affine R} [Algebra R S] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K]

noncomputable instance instSMulAlgEquiv : SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩

lemma algEquiv_smul_def (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) :
    σ • P = Point.map σ.toAlgHom P :=
  rfl

noncomputable instance instDistribMulActionAlgEquiv :
    DistribMulAction (K ≃ₐ[S] K) (W'⁄K).Point where
  one_smul P := by cases P <;> rfl
  mul_smul σ τ P := by cases P <;> rfl
  smul_zero _ := rfl
  smul_add σ P Q := (Point.map σ.toAlgHom).map_add P Q

lemma algEquiv_smul_zsmul (σ : K ≃ₐ[S] K) (m : ℤ) (P : (W'⁄K).Point) :
    σ • (m • P) = m • (σ • P) :=
  (Point.map σ.toAlgHom).map_zsmul m P

lemma smul_mem_torsionBy {n : ℕ} (σ : K ≃ₐ[S] K) {P : (W'⁄K).Point}
    (hP : P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n) :
    σ • P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n := by
  rw [Submodule.mem_torsionBy_iff] at hP ⊢
  rw [← algEquiv_smul_zsmul, hP, smul_zero]

noncomputable instance instSMulTorsionBy (n : ℕ) :
    SMul (K ≃ₐ[S] K) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  ⟨fun σ P => ⟨σ • (P : (W'⁄K).Point), smul_mem_torsionBy σ P.property⟩⟩

noncomputable instance instDistribMulActionTorsionBy (n : ℕ) :
    DistribMulAction (K ≃ₐ[S] K) (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  one_smul P := Subtype.ext <| one_smul _ (P : (W'⁄K).Point)
  mul_smul σ τ P := Subtype.ext <| mul_smul σ τ (P : (W'⁄K).Point)
  smul_zero σ := Subtype.ext <| smul_zero (A := (W'⁄K).Point) σ
  smul_add σ P Q := Subtype.ext <| smul_add σ (P : (W'⁄K).Point) (Q : (W'⁄K).Point)

/-- The pin's `instModuleZModTorsionBy`, with mathlib's
`AddSubgroup.torsionBy.zmodModule` supplying the value (playbook §4). -/
noncomputable instance instModuleZModTorsionBy (n : ℕ) :
    Module (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  AddSubgroup.torsionBy.zmodModule

variable (S) in

def IsGaloisStable {n : ℕ}
    (N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n)) : Prop :=
  ∀ (σ : K ≃ₐ[S] K), ∀ x ∈ N, σ • x ∈ N

variable (S) in

def GaloisRepIsIrreducible (W' : Affine R) (n : ℕ) : Prop :=
  Nontrivial (Submodule.torsionBy ℤ (W'⁄K).Point n) ∧
    ∀ N : Submodule (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n),
      IsGaloisStable S N → N = ⊥ ∨ N = ⊤

end WeierstrassCurve.Affine.Point

noncomputable instance instDecEqAlgebraicClosureRat :
    DecidableEq (AlgebraicClosure ℚ) :=
  Classical.decEq _
