/-
  The `Γ₁` / diamond vocabulary: the lower-right character on `Γ₀` read modulo
  `N`, the `OnePoint (ZMod p)` weight/representative layer, `IsDiamondLift`, the
  conjugation home for `Γ₁`, and the diamond operator on `Γ₁`-cusp forms.

  This is SET-2 (l2) of `topics/PORTING-Level.md`; the mathematics is base/018
  §4.4–§4.5. Mathlib has `Gamma1` and `Gamma0Map` but no `IsDiamondLift` and no
  diamond operator, so this module supplies them once and later level arguments
  import instead of re-proving.

  FLT provenance, pinned `aa2d8b3`:
  * `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:193–246` — `wt`, `lift`,
    `lift_mem`, `lift_apply_one_one`, `d_mul`, `det_mod`, `mem_Gamma1_of_d_eq_one`,
    `isUnit_wt` (and the `@[simp]` companions `wt_infty`/`wt_coe`/`lift_infty`/
    `lift_coe`).
  * `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:371` — `isUnit_d`.
  * `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean:469–628` — `IsDiamondLift`,
    `exists_isDiamondLift_of_coprime`, `IsDiamondLift.coprime`, `conj_mem_Gamma1`,
    `mem_coe_Gamma1_iff`, `toConjAct_inv_smul_coe_Gamma1`, `slashOfMemGamma0`,
    `slashLinOfMemGamma0`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne` (and
    the `@[simp]`/corollary companions).

  Statements are transcribed verbatim from the pin (the checker is textual); the
  proofs are adapted only for mathlib `v4.34.0`. The pin spreads the group layer
  over `CuspForm.Gamma1Hecke` and the diamond layer over `CuspForm`; here both
  live in one home, `ModularForm.Level`.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

-- The pin's `haveI` walls are kept literal (as in the `WeilExchange` set and
-- `HeckeInvariance.lean`).
set_option linter.style.haveILetI false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm CongruenceSubgroup

open scoped MatrixGroups ModularForm OnePoint Manifold

namespace ModularForm.Level

section reps

variable {p : ℕ}

/-- The weight character of the Hecke representative `x` for `Up` at level `N`:
`p` at the cusp `∞` and `1` on the `ZMod p`-points. -/
def wt (N p : ℕ) (x : OnePoint (ZMod p)) : ZMod N := x.elim (p : ZMod N) (fun _ => 1)

@[simp] theorem wt_infty {N : ℕ} : wt N p ∞ = (p : ZMod N) := rfl

@[simp] theorem wt_coe {N : ℕ} (j : ZMod p) : wt N p j = 1 := rfl

theorem isUnit_wt {N : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) :
    IsUnit (wt N p x) := by
  induction x using OnePoint.rec with
  | infty => exact ZMod.isUnit_prime_of_not_dvd hp hpN
  | coe j => exact isUnit_one

variable {N : ℕ}

/-- The lift of a `Γ₀`-matrix to the Hecke representative at `x`: `σ` at `∞`,
the identity on the `ZMod p`-points. -/
def lift (σ : SL(2, ℤ)) (x : OnePoint (ZMod p)) : SL(2, ℤ) := x.elim σ (fun _ => 1)

@[simp] theorem lift_infty (σ : SL(2, ℤ)) : lift (p := p) σ ∞ = σ := rfl

@[simp] theorem lift_coe (σ : SL(2, ℤ)) (j : ZMod p) : lift σ (j : OnePoint (ZMod p)) = 1 := rfl

theorem lift_mem (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (x : OnePoint (ZMod p)) :
    lift σ x ∈ CongruenceSubgroup.Gamma0 N := by
  induction x using OnePoint.rec with
  | infty => exact hσ
  | coe j => exact one_mem _

theorem lift_apply_one_one (σ : SL(2, ℤ)) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (x : OnePoint (ZMod p)) : (((lift σ x) 1 1 : ℤ) : ZMod N) = wt N p x := by
  induction x using OnePoint.rec with
  | infty => exact hσp
  | coe j => simp

theorem d_mul {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ CongruenceSubgroup.Gamma0 N)
    (h₂ : γ₂ ∈ CongruenceSubgroup.Gamma0 N) :
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N) := by
  have := map_mul (CongruenceSubgroup.Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩
  exact this

theorem det_mod (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have := congrArg (Int.cast : ℤ → ZMod N) hdet
  push_cast at this
  rw [hc] at this
  linear_combination this

theorem mem_Gamma1_of_d_eq_one {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hd : ((γ 1 1 : ℤ) : ZMod N) = 1) : γ ∈ CongruenceSubgroup.Gamma1 N := by
  rw [CongruenceSubgroup.Gamma1_mem]
  have ha : ((γ 0 0 : ℤ) : ZMod N) = 1 := by
    have := det_mod γ hγ; rw [hd, mul_one] at this; exact this
  exact ⟨by simpa using ha, by simpa using hd, by simpa using CongruenceSubgroup.Gamma0_mem.mp hγ⟩

end reps

section isUnit_d

variable {N : ℕ}

theorem isUnit_d {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) :=
  IsUnit.of_mul_eq_one_right _ (det_mod γ hγ)

end isUnit_d

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Lifts

variable (M : ℕ)

/-- A lift of the diamond `⟨d⟩` to `Γ₀(M)`: a matrix in `Γ₀(M)` whose lower-right
entry is `d` modulo `M`. -/
def IsDiamondLift (d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)

variable {M}

theorem exists_isDiamondLift_of_coprime {d : ℕ} (h : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), IsDiamondLift M d γ := by
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h : IsCoprime (d : ℤ) (M : ℤ))
  refine ⟨⟨!![u, -v; (M : ℤ), (d : ℤ)], ?_⟩, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]; linear_combination huv
  · exact Gamma0_mem.mpr (by simp)
  · simp

theorem IsDiamondLift.coprime {d : ℕ} {γ : SL(2, ℤ)} (h : IsDiamondLift M d γ) : Nat.Coprime d M := by
  have hdet := Matrix.det_fin_two γ.1
  rw [γ.2] at hdet
  have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 h.1
  have h1 : ((γ 0 0 : ℤ) : ZMod M) * (d : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc, mul_zero, sub_zero, h.2] at this
    exact this.symm
  exact (ZMod.isUnit_iff_coprime d M).1 (IsUnit.of_mul_eq_one_right _ h1)

theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hx : x ∈ Gamma1 M) :
    γ * x * γ⁻¹ ∈ Gamma1 M := by
  have hx0 : x ∈ Gamma0 M := Gamma1_in_Gamma0 M hx
  have hx' : (⟨x, hx0⟩ : Gamma0 M) ∈ Gamma1' M := by
    rw [Gamma1_to_Gamma0_mem]
    exact (Gamma1_mem M x).1 hx
  haveI : (Gamma1' M).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : Gamma0 M) * ⟨x, hx0⟩ * (⟨γ, hγ⟩ : Gamma0 M)⁻¹ ∈ Gamma1' M :=
    Subgroup.Normal.conj_mem inferInstance _ hx' _
  rw [Gamma1_to_Gamma0_mem] at hc
  exact (Gamma1_mem M _).2 hc

theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in

theorem toConjAct_inv_smul_coe_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, inv_inv, ConjAct.toConjAct_smul]
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := (mem_coe_Gamma1_iff _).1 h
    have hx : x = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ * Matrix.SpecialLinearGroup.mapGL ℝ y
        * Matrix.SpecialLinearGroup.mapGL ℝ γ := by
      rw [hyx, map_inv]; group
    have hmem := conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy
    rw [inv_inv] at hmem
    rw [hx, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ hmem
  · intro h
    obtain ⟨y, hy, rfl⟩ := (mem_coe_Gamma1_iff _).1 h
    rw [← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem _ (conj_mem_Gamma1 hγ hy)

end Lifts

section Diamond

variable (M : ℕ) (k : ℤ)

def slashOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) :
    CuspForm (Γ₁ℝ M) k :=
  (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) rfl
    (toConjAct_inv_smul_coe_Gamma1 hγ).symm

@[simp] theorem coe_slashOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(slashOfMemGamma0 M k hγ f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

def slashLinOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k where
  toFun := slashOfMemGamma0 M k hγ
  map_add' f g := DFunLike.coe_injective <| by
    simp only [coe_slashOfMemGamma0, FunLike.coe_add, SlashAction.add_slash]
  map_smul' c f := DFunLike.coe_injective <| by
    simp only [coe_slashOfMemGamma0, FunLike.coe_smul, RingHom.id_apply]
    exact ModularForm.SL_smul_slash k γ (⇑f) c

@[simp] theorem coe_slashLinOfMemGamma0_apply {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(slashLinOfMemGamma0 M k hγ f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem slash_eq_slash_of_isDiamondLift {d : ℕ} {γ γ' : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (hγ' : IsDiamondLift M d γ') (f : CuspForm (Γ₁ℝ M) k) :
    ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') := by

  have hmem : γ' * γ⁻¹ ∈ Gamma1 M := by
    have hd := Matrix.det_fin_two γ.1
    rw [γ.2] at hd
    have hd' := Matrix.det_fin_two γ'.1
    rw [γ'.2] at hd'
    have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hγ.1
    have hc' : ((γ' 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.1 hγ'.1
    have hδ : ((γ 1 1 : ℤ) : ZMod M) = d := hγ.2
    have hδ' : ((γ' 1 1 : ℤ) : ZMod M) = d := hγ'.2
    have ha : ((γ 0 0 : ℤ) : ZMod M) * d = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod M)) hd
      simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc, mul_zero, sub_zero, hδ] at this
      exact this.symm
    have ha' : ((γ' 0 0 : ℤ) : ZMod M) * d = 1 := by
      have := congrArg (fun z : ℤ => (z : ZMod M)) hd'
      simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, hc', mul_zero, sub_zero, hδ'] at this
      exact this.symm
    have hinv : (γ⁻¹ : SL(2, ℤ)) = ⟨!![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0], by
        rw [Matrix.det_fin_two_of]; have := γ.det_coe; rw [Matrix.det_fin_two] at this
        linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ
    rw [Gamma1_mem, hinv]
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val', Int.cast_add, Int.cast_mul, Int.cast_neg, hc, hc',
      hδ, hδ', neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_neg, Fin.isValue]
    refine ⟨?_, ?_, trivial⟩
    · simpa only [mul_comm] using ha'
    · linear_combination ha
  have hinv := SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)
        = (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ' * γ⁻¹))) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by rw [hinv]
      _ = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') := by
          rw [← SlashAction.slash_mul, ← map_mul, inv_mul_cancel_right]

open Classical in

def diamondLinOne (d : ℕ) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k :=
  if h : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ then slashLinOfMemGamma0 M k h.choose_spec.1
  else LinearMap.id

variable {M k}

theorem coe_diamondLinOne_apply {d : ℕ} {γ : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(diamondLinOne M k d f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by
  have h : ∃ γ : SL(2, ℤ), IsDiamondLift M d γ := ⟨γ, hγ⟩
  rw [diamondLinOne, dite_eq_left h, coe_slashLinOfMemGamma0_apply]
  exact slash_eq_slash_of_isDiamondLift M k h.choose_spec hγ f

theorem coe_diamondLinOne_apply' {d : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (hγd : ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(diamondLinOne M k d f) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) :=
  coe_diamondLinOne_apply ⟨hγ, hγd⟩ f

theorem diamondLinOne_apply_apply {d : ℕ} {γ : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (f : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    diamondLinOne M k d f τ = (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) τ := by
  rw [coe_diamondLinOne_apply hγ]

theorem diamondLinOne_of_not {d : ℕ} (h : ¬ ∃ γ : SL(2, ℤ), IsDiamondLift M d γ) :
    diamondLinOne M k d = LinearMap.id := by
  rw [diamondLinOne, dite_eq_right h]

theorem diamondLinOne_of_not_coprime {d : ℕ} (h : ¬ Nat.Coprime d M) :
    diamondLinOne M k d = LinearMap.id :=
  diamondLinOne_of_not fun ⟨_, hγ⟩ => h hγ.coprime

theorem diamondLinOne_one : diamondLinOne M k 1 = LinearMap.id := by
  refine LinearMap.ext fun f => CuspForm.ext fun τ => ?_
  have h1 : IsDiamondLift M 1 1 := ⟨Subgroup.one_mem _, by simp⟩
  rw [diamondLinOne_apply_apply h1, map_one, SlashAction.slash_one, LinearMap.id_apply]

end Diamond

end ModularForm.Level

end
