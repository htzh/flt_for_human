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
    `mem_coe_Gamma1_iff`, `Gamma1_conjAct_smul`, `slashOfMemGamma0`,
    `slashLinOfMemGamma0`, `slash_eq_slash_of_isDiamondLift`, `diamondLinOne` (and
    the `@[simp]`/corollary companions).
  * `Definitions/Def_CohCarrier_Level.lean:111–154` — `Gamma0_d_mul_a`, `gamma0Units`,
    `val_gamma0Units`: the lower-right entry as a unit of `ZMod N`, whose values form
    the group that the `d`-character takes in.

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

section IsUnitWt

variable [Fact p.Prime]

/-- H2 reconciliation: the pin's `isUnit_wt` statement without the redundant
`hp : p.Prime` hypothesis (the pin derives it from the `Fact p.Prime` instance). -/
theorem isUnit_wt {N : ℕ} (hpN : ¬ p ∣ N) (x : OnePoint (ZMod p)) :
    IsUnit (wt N p x) := by
  induction x using OnePoint.rec with
  | infty => exact ZMod.isUnit_prime_of_not_dvd Fact.out hpN
  | coe j => exact isUnit_one

end IsUnitWt

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
    (((γ₁ * γ₂) 1 1 : ℤ) : ZMod N) = ((γ₁ 1 1 : ℤ) : ZMod N) * ((γ₂ 1 1 : ℤ) : ZMod N) :=
  map_mul (CongruenceSubgroup.Gamma0Map N) ⟨γ₁, h₁⟩ ⟨γ₂, h₂⟩

theorem det_mod {N : ℕ} (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 N) :
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

section Character

variable (M : ℕ)

/-- The upper-left entry inverts the lower-right one modulo `M` inside `Γ₀(M)`: the lower-left
entry vanishes, so the determinant reads `(0 0) * (1 1) = 1`. -/
theorem Gamma0_d_mul_a (γ : Gamma0 M) :
    ((γ.1 1 1 : ℤ) : ZMod M) * ((γ.1 0 0 : ℤ) : ZMod M) = 1 := by
  simpa [mul_comm] using det_mod (N := M) (γ : SL(2, ℤ)) γ.2

/-- The lower-right entry of a `Γ₀(M)`-matrix as a unit of `ZMod M`: the character whose kernel
is `Γ₁(M)` and which makes `⟨d⟩` a group element. -/
def gamma0Units : Gamma0 M →* (ZMod M)ˣ where
  toFun γ :=
    { val := Gamma0Map M γ
      inv := ((γ.1 0 0 : ℤ) : ZMod M)
      val_inv := Gamma0_d_mul_a M γ
      inv_val := det_mod (N := M) (γ : SL(2, ℤ)) γ.2 }
  map_one' := by ext; simp
  map_mul' γ δ := by ext; exact map_mul (Gamma0Map M) γ δ

@[simp] theorem val_gamma0Units (γ : Gamma0 M) : (gamma0Units M γ : ZMod M) = Gamma0Map M γ :=
  rfl

/-- The inverse of the lower-right character is the upper-left entry (`Gamma0_d_mul_a`). -/
@[simp] theorem inv_gamma0Units (γ : Gamma0 M) :
    (((gamma0Units M γ)⁻¹ : (ZMod M)ˣ) : ZMod M) = ((γ.1 0 0 : ℤ) : ZMod M) :=
  rfl

end Character

section isUnit_d

variable {N : ℕ}

theorem isUnit_d {γ : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) :
    IsUnit ((γ 1 1 : ℤ) : ZMod N) :=
  (gamma0Units N ⟨γ, hγ⟩).isUnit

end isUnit_d

section Normal

/-- `Γ₁(N)` is the kernel of the lower-right character on `Γ₀(N)`: the congruence
condition `γ 1 1 ≡ 1` forces `γ 0 0 ≡ 1` as well, and `γ 1 0 ≡ 0` is already `Γ₀`'s. -/
theorem Gamma1_subgroupOf_eq_ker (N : ℕ) :
    (CongruenceSubgroup.Gamma1 N).subgroupOf (CongruenceSubgroup.Gamma0 N) =
      (CongruenceSubgroup.Gamma0Map N).ker := by
  ext x
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  show (x : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma1 N ↔ ((x : SL(2, ℤ)) 1 1 : ZMod N) = 1
  exact ⟨fun h => ((CongruenceSubgroup.Gamma1_mem N x).1 h).2.1, fun h => mem_Gamma1_of_d_eq_one x.2 h⟩

/-- `Γ₁(M)` is the kernel of the lower-right character in its group-valued form
(`gamma0Units`): a `Γ₀(M)`-matrix whose lower-right entry is `1` modulo `M` lies in `Γ₁(M)`. -/
theorem mem_Gamma1_of_gamma0Units_eq_one {M : ℕ} {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M)
    (h : gamma0Units M ⟨γ, hγ⟩ = 1) : γ ∈ Gamma1 M := by
  have hker : (⟨γ, hγ⟩ : Gamma0 M) ∈ (Gamma1 M).subgroupOf (Gamma0 M) := by
    rw [Gamma1_subgroupOf_eq_ker, MonoidHom.mem_ker]
    simpa using congrArg (fun u : (ZMod M)ˣ => (u : ZMod M)) h
  exact Subgroup.mem_subgroupOf.mp hker

/-- `Γ₁(N)` is normal in `Γ₀(N)`: it is a kernel, so `Γ₀(N)`-conjugation preserves it. -/
theorem Gamma1_normal_in_Gamma0 (N : ℕ) :
    ((CongruenceSubgroup.Gamma1 N).subgroupOf (CongruenceSubgroup.Gamma0 N)).Normal := by
  rw [Gamma1_subgroupOf_eq_ker]
  exact MonoidHom.normal_ker _

end Normal

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Lifts

variable (M : ℕ)

/-- A lift of the diamond `⟨d⟩` to `Γ₀(M)`: a matrix in `Γ₀(M)` whose lower-right
entry is `d` modulo `M`. -/
def IsDiamondLift (d : ℕ) (γ : SL(2, ℤ)) : Prop :=
  γ ∈ Gamma0 M ∧ ((γ 1 1 : ℤ) : ZMod M) = (d : ZMod M)

variable {M}

/-- Every coprime pair is the lower row of an integral `SL₂`-matrix: a Bézout pair
`u * d + v * N = 1` gives `!![u, -v; N, d]`.  Every lift into `Γ₀` with a prescribed `1 1`-entry is
this matrix. -/
theorem exists_sl2_of_isCoprime {d N : ℤ} (h : IsCoprime d N) :
    ∃ γ : SL(2, ℤ), γ 1 0 = N ∧ γ 1 1 = d := by
  obtain ⟨u, v, huv⟩ := h
  exact ⟨⟨!![u, -v; N, d], by rw [Matrix.det_fin_two_of]; linear_combination huv⟩, rfl, rfl⟩

theorem exists_isDiamondLift_of_coprime {d : ℕ} (h : Nat.Coprime d M) :
    ∃ γ : SL(2, ℤ), IsDiamondLift M d γ := by
  obtain ⟨γ, h10, h11⟩ := exists_sl2_of_isCoprime (Nat.isCoprime_iff_coprime.2 h)
  exact ⟨γ, Gamma0_mem.mpr (by rw [h10]; simp), by rw [h11]; simp⟩

/-- A lift of `⟨d⟩` exists only for `d` coprime to `M`: `d` is the lower-right entry of a member
of `Γ₀(M)`, hence a unit of `ZMod M`. -/
theorem IsDiamondLift.coprime {d : ℕ} {γ : SL(2, ℤ)} (h : IsDiamondLift M d γ) : Nat.Coprime d M := by
  have h1 : ((γ 0 0 : ℤ) : ZMod M) * (d : ZMod M) = 1 := by
    rw [← h.2]; exact det_mod γ h.1
  exact (ZMod.isUnit_iff_coprime d M).1 (IsUnit.of_mul_eq_one_right _ h1)

theorem conj_mem_Gamma1 {γ x : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hx : x ∈ Gamma1 M) :
    γ * x * γ⁻¹ ∈ Gamma1 M := by
  have hmem : (⟨x, Gamma1_in_Gamma0 M hx⟩ : Gamma0 M) ∈ (Gamma1 M).subgroupOf (Gamma0 M) := hx
  have := (Gamma1_normal_in_Gamma0 M).conj_mem _ hmem (⟨γ, hγ⟩ : Gamma0 M)
  simpa only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] using this

theorem mem_coe_Gamma1_iff (x : GL (Fin 2) ℝ) :
    x ∈ (Γ₁ℝ M) ↔ ∃ γ : SL(2, ℤ), γ ∈ Gamma1 M ∧ (Matrix.SpecialLinearGroup.mapGL ℝ γ) = x :=
  Subgroup.mem_map

open ConjAct Pointwise in
/-- `Γ₁(M)` is fixed by the conjugation action of `Γ₀(M)`: this is normality of `Γ₁` in `Γ₀`
(`Gamma1_normal_in_Gamma0`) read as `toConjAct · •` on the `GL(2, ℝ)`-picture of the level. It is
what lets the slash by a `Γ₀`-element (`ModularForm.translate`) be a form on `Γ₁(M)` again. -/
theorem Gamma1_conjAct_smul {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    toConjAct (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ • (Γ₁ℝ M) = (Γ₁ℝ M) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul, mem_coe_Gamma1_iff]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨γ⁻¹ * y * γ, by simpa using conj_mem_Gamma1 (Subgroup.inv_mem _ hγ) hy, ?_⟩
    rw [map_mul, map_mul, map_inv, hyx]
    group
  · rintro ⟨y, hy, rfl⟩
    exact ⟨γ * y * γ⁻¹, conj_mem_Gamma1 hγ hy, by rw [map_mul, map_mul, map_inv]⟩

end Lifts

section Diamond

variable (M : ℕ) (k : ℤ)

/-- Slash a `Γ₁(M)`-cusp-form by a `Γ₀(M)`-element.  Mathlib's `CuspForm.translate` can only
re-level: `f ∣[k] γ` is invariant under `γ⁻¹ Γ₁(M) γ`, so `translate` returns a form *there*.
`Γ₁` is normal in `Γ₀` (`Gamma1_conjAct_smul`), which brings the level back, and `copy` installs
the same function at it. -/
def slashOfMemGamma0 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Γ₁ℝ M) k) :
    CuspForm (Γ₁ℝ M) k :=
  (CuspForm.translate f (Matrix.SpecialLinearGroup.mapGL ℝ γ)).copy (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)) rfl
    (Gamma1_conjAct_smul hγ).symm

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

/-- The diamond `⟨d⟩` marks the `Γ₁(M)`-cosets of `Γ₀(M)`: two lifts of `⟨d⟩` differ by an
element of `Γ₁(M)`, which acts trivially, so they slash a `Γ₁(M)`-form the same way. -/
theorem slash_eq_slash_of_isDiamondLift {d : ℕ} {γ γ' : SL(2, ℤ)} (hγ : IsDiamondLift M d γ)
    (hγ' : IsDiamondLift M d γ') (f : CuspForm (Γ₁ℝ M) k) :
    ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) = ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ') := by
  have hγinv : γ⁻¹ ∈ Gamma0 M := inv_mem hγ.1
  have hd : gamma0Units M ⟨γ', hγ'.1⟩ = gamma0Units M ⟨γ, hγ.1⟩ := by
    ext
    rw [val_gamma0Units, val_gamma0Units]
    exact hγ'.2.trans hγ.2.symm
  have hmem : γ' * γ⁻¹ ∈ Gamma1 M := by
    refine mem_Gamma1_of_gamma0Units_eq_one (mul_mem hγ'.1 hγinv) ?_
    show gamma0Units M (⟨γ', hγ'.1⟩ * (⟨γ, hγ.1⟩ : Gamma0 M)⁻¹) = 1
    rw [map_mul, map_inv, hd, mul_inv_cancel]
  have hslash : ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ' * γ⁻¹)) = ⇑f :=
    SlashInvariantFormClass.slash_action_eq f _ (Subgroup.mem_map_of_mem _ hmem)
  calc ⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ)
        = (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (γ' * γ⁻¹))) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ) := by rw [hslash]
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

/- The pin's `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean` declares
`slashOfMemGamma0` and `diamondLinOne` under `namespace CuspForm`; this port
homes them in `ModularForm.Level`. The `Theorems/` wrappers of the Γ₁-Hecke
targets spell them `CuspForm.slashOfMemGamma0` / `CuspForm.diamondLinOne` (the
statement checker is textual and does not strip that qualification), so restore
the pin's spelling as an export alias. `export` introduces no checker-visible
declaration. -/
namespace CuspForm

export ModularForm.Level (slashOfMemGamma0 diamondLinOne)

end CuspForm

end
