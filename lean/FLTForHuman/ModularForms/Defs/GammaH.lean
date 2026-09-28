/-
  The `Γ_H` family: the lower-right unit character on `Γ₀(M)`, its pullback
  subgroups, the top/bottom specialisations, the lift of a unit, and the
  conjugation action that underlies the diamond operator.

  This is the vocabulary the Hecke effort's Stage D is gated on
  (`topics/PORTING-Hecke.md` §3.1: `Γ_H` is "gated on porting `CohCarrier.GammaH`").
  The mathematics is base/018 §2.2, §4.

  FLT provenance, pinned `aa2d8b3`:
  * `Definitions/Def_CohCarrier_Level.lean:111–154` — `Gamma0_d_mul_a`,
    `gamma0Units`, `val_gamma0Units`, `GammaH`, `mem_GammaH_iff`,
    `GammaH_le_Gamma0`, `GammaH_top`; and `:162`, `:261–294` — `H1`,
    `GammaH_normal_in_Gamma0`, `conj_mem_GammaH`, `conjHom`, `diamondRaw`.
  * `Definitions/Def_CohCarrier_Inst.lean:39–53` — `gamma0Units_surjective`.
  * `Definitions/Def_ModularCurve_XH.lean:20–68` — `translation_mem_GammaH`,
    `Gamma1_le_GammaH`, `GammaH_bot`, `GammaH_mono`.
  * `Definitions/Def_CuspForm_HeckeOperatorFormsGammaH.lean:18–70` —
    `Gamma_le_GammaH`, `GammaH_finiteIndex`, `gammaLift`, `gamma0Units_gammaLift`,
    `unitOfPrimeNotDvd`, `gammaLift_apply_11`, `mul_inv_mem_GammaH_of_gamma0Units_eq`,
    `slash_mapGL_eq_of_gamma0Units_eq`.

  Statements are transcribed verbatim from the pin's `Definitions/` files;
  proofs are adapted only for mathlib `v4.34.0` (`if_pos`/`if_neg` →
  `ite_eq_left`/`ite_eq_right` and similar). The one placement divergence is
  deliberate: the pin spreads these across four modules and re-inlines them into
  every consumer; here they have one home.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.SlashActions
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Index
import Mathlib.Tactic.Group

set_option autoImplicit false

noncomputable section

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups ModularForm

namespace CohCarrier

section Level

variable (M : ℕ)

/-- Inside `Γ₀(M)`, the lower-right entry is the inverse of the upper-left one
modulo `M`. -/
theorem Gamma0_d_mul_a (γ : Gamma0 M) :
    ((γ.1 1 1 : ℤ) : ZMod M) * ((γ.1 0 0 : ℤ) : ZMod M) = 1 := by
  have hdet := Matrix.SpecialLinearGroup.det_coe γ.1
  rw [Matrix.det_fin_two] at hdet
  have hc : ((γ.1 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp γ.2
  have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_one, hc, mul_zero, sub_zero] at h
  rw [mul_comm]
  exact h

/-- The lower-right entry of a `Γ₀(M)`-matrix, as a unit of `ZMod M`. -/
def gamma0Units : Gamma0 M →* (ZMod M)ˣ where
  toFun γ :=
    { val := Gamma0Map M γ
      inv := ((γ.1 0 0 : ℤ) : ZMod M)
      val_inv := Gamma0_d_mul_a M γ
      inv_val := by rw [mul_comm]; exact Gamma0_d_mul_a M γ }
  map_one' := by ext; simp
  map_mul' γ δ := by ext; exact map_mul (Gamma0Map M) γ δ

@[simp]
theorem val_gamma0Units (γ : Gamma0 M) : (gamma0Units M γ : ZMod M) = Gamma0Map M γ := rfl

/-- `Γ_H(M)`: the elements of `Γ₀(M)` whose lower-right entry lies in `H`. -/
def GammaH (H : Subgroup (ZMod M)ˣ) : Subgroup SL(2, ℤ) :=
  (H.comap (gamma0Units M)).map (Gamma0 M).subtype

variable {M}

theorem mem_GammaH_iff {H : Subgroup (ZMod M)ˣ} {A : SL(2, ℤ)} :
    A ∈ GammaH M H ↔ ∃ hA : A ∈ Gamma0 M, gamma0Units M ⟨A, hA⟩ ∈ H := by
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    exact ⟨γ.2, hγ⟩
  · rintro ⟨hA, h⟩
    exact ⟨⟨A, hA⟩, h, rfl⟩

theorem GammaH_le_Gamma0 (H : Subgroup (ZMod M)ˣ) : GammaH M H ≤ Gamma0 M := by
  intro A hA
  obtain ⟨hA0, _⟩ := mem_GammaH_iff.mp hA
  exact hA0

theorem GammaH_top : GammaH M ⊤ = Gamma0 M := by
  ext A
  rw [mem_GammaH_iff]
  exact ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, Subgroup.mem_top _⟩⟩

theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') :
    CohCarrier.GammaH M H ≤ CohCarrier.GammaH M H' := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  exact mem_GammaH_iff.mpr ⟨hA0, h hAH⟩

end Level

section Translations

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem translation_mem_GammaH : ModularGroup.T ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  have hT0 : ModularGroup.T ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  refine ⟨hT0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨ModularGroup.T, hT0⟩ = 1 := by
    ext
    simp [CohCarrier.gamma0Units, Gamma0Map, ModularGroup.T]
  rw [this]
  exact one_mem H

theorem Gamma1_le_GammaH : Gamma1 M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [Gamma1_mem] at hA
  obtain ⟨_, h11, h10⟩ := hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA0 : A ∈ Gamma0 M := Gamma0_mem.mpr h10
  refine ⟨hA0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, hA0⟩ = 1 := by
    ext
    simp only [CohCarrier.gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Units.val_one, Gamma0Map]
    exact h11
  rw [this]
  exact one_mem H

theorem GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M := by
  refine le_antisymm ?_ (Gamma1_le_GammaH M ⊥)
  intro A hA
  obtain ⟨hA0, hAH⟩ := CohCarrier.mem_GammaH_iff.mp hA
  rw [Subgroup.mem_bot] at hAH
  have h11 : ((A 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) hAH
    simpa [CohCarrier.gamma0Units, Gamma0Map] using this
  have h10 : ((A 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hA0
  rw [Gamma1_mem]
  refine ⟨?_, h11, h10⟩
  have hda := CohCarrier.Gamma0_d_mul_a M ⟨A, hA0⟩
  simp only at hda
  rw [h11, one_mul] at hda
  exact hda

end Translations

section Surjective

variable (M : ℕ)

/-- Every unit of `ZMod M` is the lower-right entry of some `Γ₀(M)`-matrix:
the witness is the explicit `!![u⁻¹.val, k; M, u.val]`. -/
theorem gamma0Units_surjective [NeZero M] : Function.Surjective (gamma0Units M) := by
  intro u
  have hAD : (((((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ) * ((u : ZMod M).val : ℤ) - 1 : ℤ) : ZMod M) = 0 := by
    simp
  obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hAD
  let γ : SL(2, ℤ) := ⟨!![(((u⁻¹ : (ZMod M)ˣ) : ZMod M).val : ℤ), k; (M : ℤ), ((u : ZMod M).val : ℤ)], by
    rw [Matrix.det_fin_two_of]
    linarith⟩
  have hγ0 : γ ∈ Gamma0 M := by
    rw [Gamma0_mem]
    simp [γ]
  refine ⟨⟨γ, hγ0⟩, Units.ext ?_⟩
  simp only [gamma0Units, MonoidHom.coe_mk, OneHom.coe_mk, Gamma0Map]
  simp [γ]

end Surjective

section Lifts

variable {M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ}

theorem Gamma_le_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) : Gamma M ≤ CohCarrier.GammaH M H := by
  intro A hA
  rw [CohCarrier.mem_GammaH_iff]
  have hA' := Gamma_mem.mp hA
  have h0 : A ∈ Gamma0 M := by rw [Gamma0_mem]; exact hA'.2.2.1
  refine ⟨h0, ?_⟩
  have : CohCarrier.gamma0Units M ⟨A, h0⟩ = 1 := by
    ext
    rw [CohCarrier.val_gamma0Units]
    show ((A 1 1 : ℤ) : ZMod M) = ((1 : (ZMod M)ˣ) : ZMod M)
    rw [hA'.2.2.2, Units.val_one]
  rw [this]
  exact one_mem H

instance GammaH_finiteIndex (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    (CohCarrier.GammaH M H).FiniteIndex :=
  Subgroup.finiteIndex_of_le (Gamma_le_GammaH M H)

/-- A chosen lift of a unit `d` to `Γ₀(M)`. -/
def gammaLift (M : ℕ) [NeZero M] (d : (ZMod M)ˣ) : Gamma0 M :=
  Classical.choose (CohCarrier.gamma0Units_surjective M d)

theorem gamma0Units_gammaLift (d : (ZMod M)ˣ) : CohCarrier.gamma0Units M (gammaLift M d) = d :=
  Classical.choose_spec (CohCarrier.gamma0Units_surjective M d)

/-- A prime `ℓ` not dividing `M`, as a unit of `ZMod M`. -/
def unitOfPrimeNotDvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ZMod M)ˣ :=
  ZMod.unitOfCoprime ℓ ((Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓM)

theorem gammaLift_apply_11 {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    ((((gammaLift M (unitOfPrimeNotDvd hℓ hℓM) : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = ℓ := by
  have := congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) (gamma0Units_gammaLift (unitOfPrimeNotDvd hℓ hℓM))
  simp [unitOfPrimeNotDvd, CohCarrier.val_gamma0Units] at this
  exact this

omit [NeZero M] in
theorem mul_inv_mem_GammaH_of_gamma0Units_eq (ρ σ : Gamma0 M)
    (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) :
    (ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹ ∈ CohCarrier.GammaH M H := by
  rw [CohCarrier.mem_GammaH_iff]
  refine ⟨(ρ * σ⁻¹).2, ?_⟩
  have e1 : (⟨(ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹, (ρ * σ⁻¹).2⟩ : Gamma0 M) = ρ * σ⁻¹ := rfl
  rw [e1, map_mul, map_inv, h, mul_inv_cancel]
  exact one_mem H

omit [NeZero M] in
theorem slash_mapGL_eq_of_gamma0Units_eq (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (ρ σ : Gamma0 M) (h : CohCarrier.gamma0Units M ρ = CohCarrier.gamma0Units M σ) (A : GL (Fin 2) ℝ) :
    f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) =
      f ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) * A) := by
  have e : ((Matrix.SpecialLinearGroup.mapGL ℝ (ρ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      (Matrix.SpecialLinearGroup.mapGL ℝ ((ρ : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹) : GL (Fin 2) ℝ) *
        (Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ) := by
    rw [← map_mul, inv_mul_cancel_right]
  rw [e, mul_assoc, SlashAction.slash_mul,
    hf _ (Subgroup.mem_map_of_mem _ (mul_inv_mem_GammaH_of_gamma0Units_eq ρ σ h))]

end Lifts

section Carrier

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : Type*) [AddCommGroup A]

/-- The additive carrier `Additive ↥Γ_H →+ A` of the cohomological Hecke
operators. -/
abbrev H1 : Type _ := Additive ↥(GammaH M H) →+ A

end Carrier

section Operators

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem GammaH_normal_in_Gamma0 :
    ((GammaH M H).subgroupOf (Gamma0 M)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  obtain ⟨_, hnH⟩ := mem_GammaH_iff.mp hn
  rw [mem_GammaH_iff]
  refine ⟨(g * n * g⁻¹).2, ?_⟩
  have e1 : (⟨((g * n * g⁻¹ : ↥(Gamma0 M)) : SL(2, ℤ)), (g * n * g⁻¹).2⟩ : ↥(Gamma0 M)) =
      g * n * g⁻¹ := Subtype.coe_eta _ _
  have e2 : (⟨(n : SL(2, ℤ)), n.2⟩ : ↥(Gamma0 M)) = n := Subtype.coe_eta _ _
  rw [e2] at hnH
  rw [e1, map_mul, map_mul, map_inv, mul_inv_cancel_comm]
  exact hnH

theorem conj_mem_GammaH (σ : Gamma0 M) (γ : ↥(GammaH M H)) :
    (σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ ∈ GammaH M H := by
  obtain ⟨hγ0, _⟩ := mem_GammaH_iff.mp γ.2
  have hmem : (⟨(γ : SL(2, ℤ)), hγ0⟩ : Gamma0 M) ∈ (GammaH M H).subgroupOf (Gamma0 M) := by
    rw [Subgroup.mem_subgroupOf]; exact γ.2
  have := (GammaH_normal_in_Gamma0 M H).conj_mem _ hmem σ
  rw [Subgroup.mem_subgroupOf] at this
  exact this

/-- Conjugation by `σ ∈ Γ₀(M)` as a monoid homomorphism of `Γ_H(M)`. -/
def conjHom (σ : Gamma0 M) : ↥(GammaH M H) →* ↥(GammaH M H) where
  toFun γ := ⟨(σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹, conj_mem_GammaH M H σ γ⟩
  map_one' := Subtype.ext (by simp)
  map_mul' γ δ := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)

variable (A : Type*) [AddCommGroup A]

/-- The raw diamond action: precomposition with the conjugation by `σ`. -/
def diamondRaw (σ : Gamma0 M) : H1 M H A →+ H1 M H A where
  toFun φ := φ.comp (MonoidHom.toAdditive (conjHom M H σ))
  map_zero' := by ext; rfl
  map_add' := by intro φ ψ; ext; rfl

end Operators

end CohCarrier

end
