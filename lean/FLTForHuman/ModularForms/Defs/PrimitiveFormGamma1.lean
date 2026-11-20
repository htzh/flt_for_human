/-
  Primitive forms of level `Γ₁(M)`: the Nebentypus twist law `HasNebentypus`, the
  eigenform predicate `IsEigenformWith`, the eigenpacket occurrence predicate
  `EigenpacketOccursAt`, and `IsPrimitiveForm` (an eigenform whose eigenpacket
  does not occur at a proper divisor of the level), with their projections.

  Transcribed verbatim from `Definitions/Def_CuspForm_PrimitiveFormGamma1.lean`
  (pinned `aa2d8b3`, 72 lines). The mathematics is math/018 §7.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Analysis.Complex.UpperHalfPlane.MoebiusAction
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.QCoeff

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups ModularForm

namespace CuspForm

open ModularForm.Level (dd)

variable {M : ℕ} {k : ℤ}

def HasNebentypus (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε (dd (N := M) γ) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

/-- The Nebentypus law in slash form. `HasNebentypus ε g` is the pointwise statement
`g (γ • τ) = ε (γ 1 1) * (j(γ,τ) ^ k * g τ)` for `γ ∈ Γ₀(M)`; this is its counterpart for the
slash action, `g ∣[k] γ = ε (γ 1 1) • g`, on which the Hecke operators act. The bridge is
`j(γ,τ) = (γ 1 0) τ + (γ 1 1)` (`denom_apply`) and the cancellation of a nonzero `zpow`. -/
theorem hasNebentypus_iff (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) :
    HasNebentypus ε g ↔ ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M →
      (⇑g : UpperHalfPlane → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ε (dd γ) • ⇑g := by
  have key : ∀ (γ : SL(2, ℤ)) (τ : UpperHalfPlane),
      (⇑g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ = ε (dd γ) * g τ ↔
        g (γ • τ) = ε (dd γ) *
          ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ) := by
    intro γ τ
    set J : ℂ := ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) with hJ
    have hJ0 : J ≠ 0 := by
      rw [hJ]
      exact UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
    have hslash : (⇑g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)) τ
        = g (γ • τ) * J ^ (-k) := by
      rw [show (⇑g ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ))
            = ⇑g ∣[k] γ from rfl, ModularForm.SL_slash_apply, ModularGroup.denom_apply, ← hJ]
    rw [hslash, zpow_neg, mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero k hJ0)]
    constructor <;> intro h <;> rw [h] <;> ring
  constructor
  · intro h γ hγ
    funext τ
    exact (key γ τ).mpr (h γ hγ τ)
  · intro h γ hγ τ
    exact (key γ τ).mp (congrFun (h γ hγ) τ)

def IsEigenformWith (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ, qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

def EigenpacketOccursAt (k : ℤ) (a e : ℕ → ℂ) (M' : ℕ) : Prop :=
  ∃ (ε' : DirichletCharacter ℂ M') (h : CuspForm (Gamma1 M') k),
    h ≠ 0 ∧ HasNebentypus ε' h ∧
    ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → p ∉ S →
      ε' (p : ZMod M') = e p ∧
      ∀ n : ℕ,
        qCoeff h (p * n) +
            ε' (p : ZMod M') * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff h (n / p) else 0) =
          a p * qCoeff h n

def IsPrimitiveForm (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  IsEigenformWith ε g ∧
    ∀ M' : ℕ, M' ∣ M → M' ≠ M →
      ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M'

theorem IsEigenformWith.qCoeff_one {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : qCoeff g 1 = 1 := h.1

theorem IsEigenformWith.hecke_of_not_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {p : ℕ} (hp : p.Prime) (hpM : ¬ p ∣ M) (n : ℕ) :
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n := h.2.1 p hp hpM n

theorem IsEigenformWith.hecke_of_dvd {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ℓ ∣ M) (n : ℕ) :
    qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n := h.2.2.1 ℓ hℓ hℓM n

theorem IsEigenformWith.hasNebentypus {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : HasNebentypus ε g := h.2.2.2

theorem IsPrimitiveForm.isEigenformWith {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsPrimitiveForm ε g) : IsEigenformWith ε g := h.1

theorem IsPrimitiveForm.not_eigenpacketOccursAt {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (h : IsPrimitiveForm ε g) {M' : ℕ} (hM' : M' ∣ M) (hne : M' ≠ M) :
    ¬ EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M' := h.2 M' hM' hne

theorem IsEigenformWith.eigenpacketOccursAt {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) (hM : M ≠ 0) (hg : g ≠ 0) :
    EigenpacketOccursAt k (fun n => qCoeff g n) (fun n => ε (n : ZMod M)) M :=
  ⟨ε, g, hg, h.hasNebentypus, Nat.divisors M, fun _ hp hpS => ⟨rfl, fun n =>
    h.hecke_of_not_dvd hp (fun hpM => hpS (Nat.mem_divisors.2 ⟨hpM, hM⟩)) n⟩⟩

end CuspForm
