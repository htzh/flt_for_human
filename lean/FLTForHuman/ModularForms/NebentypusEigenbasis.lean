/-
  The simultaneous eigenbasis of the nebentypus and the Hecke operators on `Γ₁(N)`.

  * `CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen`: the space of `Γ₁(N)`-cusp forms of
    weight `k` has a basis of forms that are simultaneously eigenforms for the nebentypus and for
    every `T_p` with `p ∤ N`.  The `ε`-eigenspaces `nebSpace` are finite dimensional and invariant
    under the pairwise-commuting `T_p` (`heckeT_comm`), the Petersson product is positive definite
    on them (`peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff`), so the commuting family
    `heckeFamily` is simultaneously diagonalizable (`span_eigen_eq_top`).

  The operator itself is not re-developed here.  `T_p` on `Γ₁(N)` is the diamond-twisted
  `heckeTOne` of `ModularForms/Defs/Gamma1HeckeOperators.lean`, whose `ε`-view is the shared
  `CuspForm.heckeFun`; `T_p` is `Γ₀(N)`-equivariant (`heckeTLinOne_slashOfMemGamma0`), so on the
  `ε`-eigenspace it is `ε`-linear (`heckeTOne_slash`), and `heckeT` is its restriction to `nebSpace`.  What is
  local here is the `Γ₁(N)`-indexed `SSbasis` layer — the nebentypus projection `proj`, `nebSpace`,
  `heckeT`, the coefficient recursion `cT`, `B`/`heckeFamily`, and the
  eigenbasis assembly — together with the generic simultaneous-diagonalization statement
  `SimulEigen.IsPosDefHerm.span_common_eigen`.

  Assumes from earlier modules: `ModularForms/Analytic/HeckeEigenvalueConj.lean` (the Petersson
  pair), `ModularForms/HeckeTLinOneQCoeff.lean` (the coefficient law and the `Γ₀`-equivariance of
  `T_ℓ`), `ModularForms/Defs/HeckeRepresentatives.lean` (the coset representatives),
  `ModularForms/HeckeEigenNebentypus.lean` (the `dd` vocabulary, hence `Γ₁(N) = ker dd`),
  `ModularForms/{HeckePrelude,HeckeQCoeff,HeckeAnalytic,HeckeCusps}.lean` (the `T`-periodicity, the
  `q`-coefficient action, the analyticity and cusp vocabulary) and `ModularForms/SturmBound.lean`
  (`finiteDimensional_of_isArithmetic`).

  The invariance half of the pin — `heckeU_add_smul_slash_heckeDiagMatrix_slash_of_mem_Gamma0`
  and its `S_` file — is stated here for the diamond-twisted `T_p` (`heckeTOne_slash`) rather than
  for `U_p + ε(p) • (· ∣[k] diag p)`, so its wire is port-owned and carried by
  `Reserve/ModularForms/PortOwnedSpecPins.lean`; this header wires the eigenbasis pair only.

  spec-pin: Theorems/Thm_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_basis_hasNebentypus_qCoeff_hecke_eigen.lean
-/
import FLTForHuman.ModularForms.Analytic.HeckeEigenvalueConj
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeTLinOneQCoeff
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.Gamma1CuspStructure
import FLTForHuman.ModularForms.HeckeCusps
import FLTForHuman.ModularForms.HeckeEigenNebentypus
import FLTForHuman.ModularForms.SturmBound
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open Matrix.SpecialLinearGroup UpperHalfPlane
open MatrixGroups ModularForm OnePoint
open CuspForm (heckeFun heckeTOne)
open CongruenceSubgroup ModularForm UpperHalfPlane Filter Function
open scoped ModularForm UpperHalfPlane MatrixGroups ComplexConjugate


namespace SimulEigen

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

structure IsPosDefHerm (B : W → W → ℂ) : Prop where
  add_right : ∀ x y z, B x (y + z) = B x y + B x z
  smul_right : ∀ x (c : ℂ) y, B x (c • y) = c * B x y
  conj_symm : ∀ x y, conj (B y x) = B x y
  definite : ∀ x, B x x = 0 → x = 0

namespace IsPosDefHerm

variable {B : W → W → ℂ} (hB : IsPosDefHerm B)
include hB

theorem add_left (x y z : W) : B (x + y) z = B x z + B y z := by
  rw [← hB.conj_symm, hB.add_right, map_add, hB.conj_symm, hB.conj_symm]

theorem smul_left (c : ℂ) (x y : W) : B (c • x) y = conj c * B x y := by
  rw [← hB.conj_symm, hB.smul_right, map_mul, hB.conj_symm]

theorem zero_right (x : W) : B x 0 = 0 := by
  have h := hB.add_right x 0 0
  rw [add_zero] at h
  have h2 : B x 0 + B x 0 - B x 0 = B x 0 - B x 0 := by rw [← h]
  simpa using h2

theorem sub_right (x y z : W) : B x (y - z) = B x y - B x z := by
  rw [sub_eq_add_neg, hB.add_right, ← neg_one_smul ℂ z, hB.smul_right]; ring

theorem sub_left (x y z : W) : B (x - y) z = B x z - B y z := by
  rw [← hB.conj_symm, hB.sub_right, map_sub, hB.conj_symm, hB.conj_symm]

theorem ker_sq (S : W →ₗ[ℂ] W) (hS : ∀ x y, B (S x) y = B x (S y)) (μ : ℂ) (v : W)
    (h : (S - μ • 1) ((S - μ • 1) v) = 0) : (S - μ • 1) v = 0 := by
  set A : W →ₗ[ℂ] W := S - μ • 1 with hA
  set A' : W →ₗ[ℂ] W := S - conj μ • 1 with hA'
  have hAadj : ∀ x y, B (A x) y = B x (A' y) := by
    intro x y
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hB.sub_left, hB.sub_right, hB.smul_left, hB.smul_right, hS]
  have hA'adj : ∀ x y, B (A' x) y = B x (A y) := by
    intro x y
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
    rw [hB.sub_left, hB.sub_right, hB.smul_left, hB.smul_right, hS, Complex.conj_conj]
  have hcomm : ∀ x, A (A' x) = A' (A x) := by
    intro x
    simp only [hA, hA', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
      map_sub, _root_.map_smul]
    module
  set w := A v with hw
  have h1 : A' w = 0 := by
    apply hB.definite
    rw [hA'adj, hcomm, show A w = 0 from h, map_zero, hB.zero_right]
  apply hB.definite
  rw [hAadj, h1, hB.zero_right]

theorem maxGenEigenspace_eq (S : W →ₗ[ℂ] W) (hS : ∀ x y, B (S x) y = B x (S y)) (μ : ℂ) :
    Module.End.maxGenEigenspace (S : Module.End ℂ W) μ = Module.End.eigenspace (S : Module.End ℂ W) μ := by
  apply le_antisymm _ Module.End.eigenspace_le_maxGenEigenspace
  have aux : ∀ (n : ℕ) (v : W), ((S - μ • 1) ^ n) v = 0 → (S - μ • 1) v = 0 := by
    intro n
    induction n with
    | zero => intro v hn; simp at hn; simp [hn]
    | succ n ih =>
      intro v hn
      rw [pow_succ, Module.End.mul_apply] at hn
      exact hB.ker_sq S hS μ v (ih _ hn)
  intro v hv
  rw [Module.End.mem_maxGenEigenspace] at hv
  obtain ⟨n, hn⟩ := hv
  rw [Module.End.mem_eigenspace_iff]
  have h := aux n v hn
  simpa [sub_eq_zero] using h

theorem span_common_eigen [FiniteDimensional ℂ W] {ι : Type*} (T : ι → W →ₗ[ℂ] W)
    (hcomm : ∀ i j, Commute (T i) (T j)) (hT : ∀ i x y, B (T i x) y = B x (T i y)) :
    Submodule.span ℂ {v : W | ∀ i, ∃ c : ℂ, T i v = c • v} = ⊤ := by
  have key : ⨆ χ : ι → ℂ, ⨅ i, Module.End.maxGenEigenspace (T i : Module.End ℂ W) (χ i) = ⊤ := by
    refine Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
      (fun i => (T i : Module.End ℂ W)) (fun i j _ => hcomm i j) fun i => ?_
    exact Module.End.iSup_maxGenEigenspace_eq_top _
  rw [eq_top_iff, ← key, iSup_le_iff]
  intro χ v hv
  refine Submodule.subset_span fun i => ⟨χ i, ?_⟩
  have hvi : v ∈ Module.End.maxGenEigenspace (T i : Module.End ℂ W) (χ i) := (Submodule.mem_iInf _).mp hv i
  rw [hB.maxGenEigenspace_eq (T i) (hT i)] at hvi
  exact Module.End.mem_eigenspace_iff.mp hvi

end IsPosDefHerm

end SimulEigen

namespace SSbasis

variable {N : ℕ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

open CuspForm.HeckeEigenNebentypus
open ModularForm.Level (dd dd_mul isUnit_dd)

theorem dd_eq_one_of_mem_Gamma1 {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) : dd (N := N) γ = 1 :=
  (mem_Gamma1_iff_dd (Gamma1_in_Gamma0 N hγ)).mp hγ

theorem mul_inv_mem_Gamma1 {γ₁ γ₂ : SL(2, ℤ)} (h₁ : γ₁ ∈ Gamma0 N) (h₂ : γ₂ ∈ Gamma0 N)
    (h : dd (N := N) γ₁ = dd γ₂) : γ₂ * γ₁⁻¹ ∈ Gamma1 N := by
  have hX : γ₁⁻¹ * γ₂ ∈ Gamma1 N :=
    CuspForm.HeckeEigenNebentypus.inv_mul_mem_Gamma1 h₁ h₂ h
  have := ModularForm.Level.conj_mem_Gamma1 h₂ hX
  rwa [show γ₂ * (γ₁⁻¹ * γ₂) * γ₂⁻¹ = γ₂ * γ₁⁻¹ by group] at this

theorem exists_lift (u : (ZMod N)ˣ) [NeZero N] :
    ∃ σ : SL(2, ℤ), σ ∈ Gamma0 N ∧ dd (N := N) σ = (u : ZMod N) := by
  obtain ⟨σ, hσ, hd⟩ :=
    CuspForm.HeckeEigenNebentypus.exists_lift (M := N) (u : ZMod N).val
      (ZMod.val_coe_unit_coprime u)
  exact ⟨σ, hσ, by rw [hd, ZMod.natCast_zmod_val]⟩

section Slash

variable {k : ℤ}

theorem sl_slash (f : ℍ → ℂ) (γ : SL(2, ℤ)) :
    f ∣[k] γ = f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) := rfl

theorem slash_mem (g : CuspForm Γ₁(N) k) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma1 N) :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) = ⇑g :=
  SlashInvariantFormClass.slash_action_eq g _ (Subgroup.mem_map_of_mem _ hγ)

theorem slash_eq_of_dd_eq (g : CuspForm Γ₁(N) k) {σ σ' : SL(2, ℤ)} (hσ : σ ∈ Gamma0 N)
    (hσ' : σ' ∈ Gamma0 N) (h : dd (N := N) σ = dd σ') :
    (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ : GL (Fin 2) ℝ)
      = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ' : GL (Fin 2) ℝ) := by
  have hmem := mul_inv_mem_Gamma1 hσ hσ' h
  conv_rhs => rw [show σ' = (σ' * σ⁻¹) * σ by rw [inv_mul_cancel_right], map_mul,
    SlashAction.slash_mul, slash_mem g hmem]

end Slash

section Diamond

variable [NeZero N] {k : ℤ}

def nebSpace (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) :
    Submodule ℂ (CuspForm Γ₁(N) k) where
  carrier := {g | CuspForm.HasNebentypus ε g}
  zero_mem' := by
    intro γ _ τ
    simp
  add_mem' := by
    intro g h hg hh
    rw [Set.mem_ofPred_eq, CuspForm.hasNebentypus_iff] at hg hh ⊢
    intro γ hγ
    rw [FunLike.coe_add, SlashAction.add_slash, hg γ hγ, hh γ hγ, smul_add]
  smul_mem' := by
    intro c g hg
    rw [Set.mem_ofPred_eq, CuspForm.hasNebentypus_iff] at hg ⊢
    intro γ hγ
    rw [FunLike.coe_smul, ← sl_slash, ModularForm.SL_smul_slash, sl_slash, hg γ hγ,
      smul_comm]

theorem mem_nebSpace {ε : DirichletCharacter ℂ N} {g : CuspForm Γ₁(N) k} :
    g ∈ nebSpace N k ε ↔ CuspForm.HasNebentypus ε g := Iff.rfl

def lift (u : (ZMod N)ˣ) : SL(2, ℤ) := (exists_lift (N := N) u).choose

theorem lift_mem (u : (ZMod N)ˣ) : lift (N := N) u ∈ Gamma0 N :=
  (exists_lift (N := N) u).choose_spec.1

theorem dd_lift (u : (ZMod N)ˣ) : dd (N := N) (lift u) = (u : ZMod N) :=
  (exists_lift (N := N) u).choose_spec.2

def proj (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) : CuspForm Γ₁(N) k :=
  ((N.totient : ℂ))⁻¹ • ∑ u : (ZMod N)ˣ, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N) •
    ModularForm.Level.slashLinOfMemGamma0 N k (lift_mem u) g

omit [NeZero N] in
theorem coe_sum {ι : Type*} (s : Finset ι) (F : ι → CuspForm Γ₁(N) k) :
    (⇑(∑ i ∈ s, F i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(F i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

theorem coe_proj (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) :
    (⇑(proj ε g) : ℍ → ℂ) = ((N.totient : ℂ))⁻¹ •
      ∑ u : (ZMod N)ˣ, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N) •
        ((⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u) : GL (Fin 2) ℝ)) := by
  rw [proj, FunLike.coe_smul, coe_sum]
  rfl

theorem proj_mem (ε : DirichletCharacter ℂ N) (g : CuspForm Γ₁(N) k) : proj ε g ∈ nebSpace N k ε := by
  rw [mem_nebSpace, CuspForm.hasNebentypus_iff]
  intro γ hγ
  set d₀ : (ZMod N)ˣ := (isUnit_dd hγ).unit with hd₀
  have hd₀' : (d₀ : ZMod N) = dd γ := (isUnit_dd hγ).unit_spec
  rw [coe_proj, ModularForm.smul_slash, SlashAction.sum_slash]

  have hσ : ∀ c : ℂ, UpperHalfPlane.σ (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) c = c := by
    intro c
    rw [UpperHalfPlane.σ, ite_eq_left (by simp)]
    rfl
  simp_rw [hσ, ModularForm.smul_slash, hσ, ← SlashAction.slash_mul, ← map_mul]

  have hstep : ∀ u : (ZMod N)ˣ,
      (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift u * γ) : GL (Fin 2) ℝ)
        = (⇑g : ℍ → ℂ) ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ (lift (u * d₀)) : GL (Fin 2) ℝ) := by
    intro u
    apply slash_eq_of_dd_eq g (mul_mem (lift_mem u) hγ) (lift_mem _)
    rw [dd_mul (lift_mem u) hγ, dd_lift, dd_lift, ← hd₀', Units.val_mul]
  simp_rw [hstep]
  rw [smul_comm]
  congr 1

  rw [Finset.smul_sum]
  refine (Fintype.sum_equiv (Equiv.mulRight d₀) _ _ fun u => ?_)
  simp only [Equiv.coe_mulRight]
  rw [smul_smul]
  congr 1
  rw [show (u⁻¹ : (ZMod N)ˣ) = d₀ * (u * d₀)⁻¹ by group, Units.val_mul, map_mul, hd₀']

theorem sum_proj (g : CuspForm Γ₁(N) k) : ∑ ε : DirichletCharacter ℂ N, proj ε g = g := by
  apply DFunLike.coe_injective
  rw [coe_sum]
  simp_rw [coe_proj]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have hφ : ((N.totient : ℂ)) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos N)).ne'

  have horth : ∀ u : (ZMod N)ˣ,
      ∑ ε : DirichletCharacter ℂ N, ε ((u⁻¹ : (ZMod N)ˣ) : ZMod N)
        = if u = 1 then (N.totient : ℂ) else 0 := by
    intro u
    have hExp : NeZero ((Monoid.exponent (ZMod N)ˣ : ℕ) : ℂ) :=
      ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
    have := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit u) 1
    simp only [map_one, mul_one, ZMod.inv_coe_unit, Units.val_eq_one] at this
    exact this
  simp_rw [← Finset.sum_smul, horth, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, smul_smul, inv_mul_cancel₀ hφ, one_smul]

  have h1 : lift (N := N) 1 ∈ Gamma1 N := by
    rw [mem_Gamma1_iff_dd (lift_mem 1), dd_lift, Units.val_one]
  exact slash_mem g h1

theorem mem_iSup_nebSpace (g : CuspForm Γ₁(N) k) :
    g ∈ ⨆ ε : DirichletCharacter ℂ N, nebSpace N k ε := by
  rw [← sum_proj g]
  exact Submodule.sum_mem _ fun ε _ => Submodule.mem_iSup_of_mem ε (proj_mem ε g)

end Diamond

section Periodicity

variable {k : ℤ} {p : ℕ}

theorem σ_heckeDiagMatrix_apply (p : ℕ) (c : ℂ) : UpperHalfPlane.σ (heckeDiagMatrix p) c = c := by
  rw [σ_heckeDiagMatrix]; rfl

end Periodicity

/-- The primes at which `T_p` is defined on `Γ₁(N)`: prime and coprime to the level. -/
abbrev GoodPrime (N : ℕ) : Type := {p : ℕ // p.Prime ∧ ¬ p ∣ N}

section Hecke

variable [NeZero N] {k : ℤ} {p : ℕ}

omit [NeZero N] in
/-- The diamond-twisted `T_p` is `Γ₀(N)`-equivariant, so on a form of nebentypus `ε` it is
`ε`-linear: `T_p` preserves the `ε`-eigenspace. -/
theorem heckeTOne_slash (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 N) :
    (⇑(heckeTOne k hp hpN f) : ℍ → ℂ) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ε (dd γ) • ⇑(heckeTOne k hp hpN f) := by
  have hsl : ModularForm.Level.slashOfMemGamma0 N k hγ f = ε (dd γ) • f := by
    ext τ
    rw [ModularForm.Level.coe_slashOfMemGamma0, (CuspForm.hasNebentypus_iff ε f).mp hf γ hγ]
    rfl
  calc (⇑(heckeTOne k hp hpN f) : ℍ → ℂ) ∣[k]
        (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ)
      = ⇑(ModularForm.Level.slashOfMemGamma0 N k hγ
          (CuspForm.heckeTLinOne k hp hpN f)) :=
        (ModularForm.Level.coe_slashOfMemGamma0 N k hγ _).symm
    _ = ⇑(CuspForm.heckeTLinOne k hp hpN
          (ModularForm.Level.slashOfMemGamma0 N k hγ f)) := by
        rw [← CuspForm.heckeTLinOne_slashOfMemGamma0 k hp hpN hγ f]
    _ = ⇑(CuspForm.heckeTLinOne k hp hpN (ε (dd γ) • f)) := by rw [hsl]
    _ = ε (dd γ) • ⇑(CuspForm.heckeTLinOne k hp hpN f) := by
        rw [LinearMap.map_smul, FunLike.coe_smul]
    _ = ε (dd γ) • ⇑(heckeTOne k hp hpN f) := rfl

omit [NeZero N] in
/-- On a form of nebentypus `ε` the diamond `⟨p⟩` acts by `ε(p)`, so the diamond-twisted
`T_p` is `U_p + ε(p) • (· ∣[k] heckeDiagMatrix p)` there. -/
theorem coe_heckeTOne_nebentypus (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    (⇑(heckeTOne k hp hpN f) : ℍ → ℂ) = heckeFun k ε p ⇑f := by
  obtain ⟨σ, hσ⟩ := ModularForm.Level.exists_isDiamondLift_of_coprime (M := N)
    ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
  rw [CuspForm.coe_heckeTOne, ModularForm.Level.coe_diamondLinOne_apply hσ]
  simp only [heckeFun]
  congr 1
  rw [(CuspForm.hasNebentypus_iff ε f).mp hf σ hσ.1, hσ.2]
  simp only [ModularForm.smul_slash, ModularForm.σ_heckeDiagMatrix,
    ContinuousAlgEquiv.refl_apply]

theorem heckeTOne_mem (hp : p.Prime) (hpN : ¬ p ∣ N) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hf : CuspForm.HasNebentypus ε f) :
    heckeTOne k hp hpN f ∈ nebSpace N k ε := by
  rw [mem_nebSpace, CuspForm.hasNebentypus_iff]
  exact fun γ hγ => heckeTOne_slash hp hpN ε f hf hγ

/-- The Hecke operator `T_p` on the `ε`-eigenspace. -/
def heckeT (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    nebSpace N k ε →ₗ[ℂ] nebSpace N k ε where
  toFun f := ⟨heckeTOne k i.2.1 i.2.2 f.1, heckeTOne_mem i.2.1 i.2.2 ε f.1 f.2⟩
  map_add' f g := by
    apply Subtype.ext
    exact map_add (CuspForm.heckeTLinOne k i.2.1 i.2.2) (f : CuspForm Γ₁(N) k) g
  map_smul' c f := by
    apply Subtype.ext
    exact map_smul (CuspForm.heckeTLinOne k i.2.1 i.2.2) c (f : CuspForm Γ₁(N) k)

theorem coe_heckeT (ε : DirichletCharacter ℂ N) (i : GoodPrime N) (f : nebSpace N k ε) :
    (⇑((heckeT ε i f : nebSpace N k ε) : CuspForm Γ₁(N) k) : ℍ → ℂ)
      = heckeFun k ε i.1 ⇑(f : CuspForm Γ₁(N) k) :=
  coe_heckeTOne_nebentypus i.2.1 i.2.2 ε (f : CuspForm Γ₁(N) k) f.2

theorem reg_coe (g : CuspForm Γ₁(N) k) : HasQCoeff (⇑g : ℍ → ℂ) :=
  hasSum_qCoeff (ModularForm.periodic_of_slash_T (slash_mem g (T_mem_Gamma1 N))) (CuspFormClass.holo g)
    (ModularFormClass.bdd_at_infty g)

theorem reg_smul {F : ℍ → ℂ} (h : HasQCoeff F) (c : ℂ) : HasQCoeff (c • F) :=
  hasSum_qCoeff_const_smul h c

theorem reg_analyticAt {F : ℍ → ℂ} (h : HasQCoeff F) : AnalyticAt ℂ (cuspFunction 1 F) 0 :=
  ModularFormClass.analyticAt_cuspFunction_zero_of_hasSum_qCoeff h

theorem reg_slash_heckeDiagMatrix (hp : p ≠ 0) (g : CuspForm Γ₁(N) k) :
    HasQCoeff ((⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p) := by
  have hG : HasQCoeff (fun τ => (⇑g : ℍ → ℂ) (heckeDiagMatrix p • τ)) :=
    hasSum_qCoeff_comp_heckeDiagMatrix_smul hp (reg_coe g)
  have hDG : (⇑g : ℍ → ℂ) ∣[k] heckeDiagMatrix p
      = ((p : ℂ) ^ (k - 1)) • fun τ => (⇑g : ℍ → ℂ) (heckeDiagMatrix p • τ) := by
    funext τ
    rw [slash_heckeDiagMatrix_apply k hp, Pi.smul_apply, smul_eq_mul]
  rw [hDG]
  exact reg_smul hG ((p : ℂ) ^ (k - 1))

theorem reg_heckeU (hp : p.Prime) (f : CuspForm Γ₁(N) k) : HasQCoeff (heckeU k p ⇑f) :=
  hasSum_qCoeff_heckeU hp.ne_zero (reg_coe f) k

theorem qCoeff_heckeFun (hp : p.Prime) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (n : ℕ) :
    ModularFormClass.qCoeff (heckeFun k ε p ⇑f) n
      = ModularFormClass.qCoeff (⇑f) (n * p)
        + ε (p : ZMod N) * (p : ℂ) ^ (k - 1)
          * (if p ∣ n then ModularFormClass.qCoeff (⇑f) (n / p) else 0) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg := reg_coe f
  have hU := reg_heckeU hp f
  have hD := reg_slash_heckeDiagMatrix hp0 f

  set D : ℍ → ℂ := (⇑f : ℍ → ℂ) ∣[k] heckeDiagMatrix p with hDdef
  set G : ℍ → ℂ := fun τ => f (heckeDiagMatrix p • τ) with hG
  have hDG : D = ((p : ℂ) ^ (k - 1)) • G := by
    funext τ
    rw [hDdef, slash_heckeDiagMatrix_apply k hp0, Pi.smul_apply, smul_eq_mul]
  have hpk : ((p : ℂ) ^ (k - 1)) ≠ 0 := zpow_ne_zero _ (Nat.cast_ne_zero.mpr hp0)
  have hGD : G = ((p : ℂ) ^ (k - 1))⁻¹ • D := by
    rw [hDG, smul_smul, inv_mul_cancel₀ hpk, one_smul]
  have hGreg : HasQCoeff G := by rw [hGD]; exact reg_smul hD _
  have hqD : ModularFormClass.qCoeff D n
      = (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff (⇑f) (n / p) else 0) := by
    rw [ModularFormClass.qCoeff, hDG, qExpansion_smul (reg_analyticAt hGreg), _root_.map_smul, smul_eq_mul]
    congr 1
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul hg hp0 n
  have hqU : ModularFormClass.qCoeff (heckeU k p ⇑f) n = ModularFormClass.qCoeff (⇑f) (n * p) := by
    rw [UpperHalfPlane.qCoeff_heckeU hg k hp0 n, coeffHeckeU_apply]
  rw [heckeFun, ModularFormClass.qCoeff, qExpansion_add (reg_analyticAt hU) (reg_analyticAt (reg_smul hD _)),
    qExpansion_smul (reg_analyticAt hD), map_add, _root_.map_smul, smul_eq_mul]
  change ModularFormClass.qCoeff (heckeU k p ⇑f) n + ε (p : ZMod N) * ModularFormClass.qCoeff D n = _
  rw [hqU, hqD, mul_assoc]

def cT (e : ℂ) (p : ℕ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + e * (if p ∣ n then a (n / p) else 0)


omit [NeZero N] in
theorem cT_cT {p q : ℕ} (hp : 0 < p) (hcop : Nat.Coprime p q) (e e' : ℂ) (a : ℕ → ℂ)
    (n : ℕ) :
    cT e p (cT e' q a) n
      = a (n * (p * q)) + e' * (if q ∣ n then a (n / q * p) else 0)
        + e * (if p ∣ n then a (n / p * q) else 0)
        + e * e' * (if p * q ∣ n then a (n / (p * q)) else 0) := by
  simp only [cT]
  have hqnp : (q ∣ n * p) ↔ q ∣ n :=
    ⟨fun h => Nat.Coprime.dvd_of_dvd_mul_right hcop.symm h, fun h => dvd_mul_of_dvd_left h p⟩
  have h2 : (if q ∣ n * p then a (n * p / q) else 0) = (if q ∣ n then a (n / q * p) else 0) := by
    by_cases hqn : q ∣ n
    · rw [ite_eq_left (hqnp.mpr hqn), ite_eq_left hqn, Nat.mul_div_right_comm hqn]
    · rw [ite_eq_right (fun h => hqn (hqnp.mp h)), ite_eq_right hqn]
  have h4 : (if p ∣ n then (a (n / p * q) + e' * (if q ∣ n / p then a (n / p / q) else 0)) else 0)
      = (if p ∣ n then a (n / p * q) else 0)
        + e' * (if p * q ∣ n then a (n / (p * q)) else 0) := by
    by_cases hpn : p ∣ n
    · rw [ite_eq_left hpn, ite_eq_left hpn, Nat.div_div_eq_div_mul]
      obtain ⟨m, rfl⟩ := hpn
      have hiff : q ∣ p * m / p ↔ p * q ∣ p * m := by
        rw [Nat.mul_div_cancel_left _ hp]
        exact (Nat.mul_dvd_mul_iff_left hp).symm
      by_cases hqm : q ∣ p * m / p
      · rw [ite_eq_left hqm, ite_eq_left (hiff.mp hqm)]
      · rw [ite_eq_right hqm, ite_eq_right (fun h => hqm (hiff.mpr h))]
    · rw [ite_eq_right hpn, ite_eq_right hpn, ite_eq_right (fun h => hpn (dvd_trans (dvd_mul_right p q) h))]
      ring
  rw [h2, h4, mul_assoc n p q]
  ring

omit [NeZero N] in
theorem cT_comm {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e e' : ℂ) (a : ℕ → ℂ)
    (n : ℕ) : cT e p (cT e' q a) n = cT e' q (cT e p a) n := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  rw [cT_cT hp.pos hcop, cT_cT hq.pos hcop.symm, mul_comm q p, mul_comm e' e]
  ring

theorem qCoeff_heckeFun' (hp : p.Prime) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) :
    ModularFormClass.qCoeff (heckeFun k ε p ⇑f)
      = cT (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) p (ModularFormClass.qCoeff (⇑f)) := by
  funext n
  rw [qCoeff_heckeFun hp ε f n, cT]

/-- The `T_p` for distinct good primes commute. -/
theorem heckeT_comm (ε : DirichletCharacter ℂ N) (i j : GoodPrime N) :
    Commute (heckeT (k := k) ε i) (heckeT ε j) := by
  rcases eq_or_ne i j with rfl | hij
  · exact Commute.refl _
  have hpq : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  refine LinearMap.ext fun f => ?_
  apply Subtype.ext
  apply DFunLike.coe_injective
  change (⇑((((heckeT ε i) ((heckeT ε j) f)) : nebSpace N k ε) : CuspForm Γ₁(N) k) : ℍ → ℂ)
    = ⇑((((heckeT ε j) ((heckeT ε i) f)) : nebSpace N k ε) : CuspForm Γ₁(N) k)
  conv_lhs => rw [coe_heckeT]
  conv_rhs => rw [coe_heckeT]
  set g₁ : CuspForm Γ₁(N) k := ((heckeT ε j f : nebSpace N k ε) : CuspForm Γ₁(N) k)
  set g₂ : CuspForm Γ₁(N) k := ((heckeT ε i f : nebSpace N k ε) : CuspForm Γ₁(N) k)
  have hg₁ : CuspForm.HasNebentypus ε g₁ := (heckeT ε j f).2
  have hg₂ : CuspForm.HasNebentypus ε g₂ := (heckeT ε i f).2
  have r₁ : HasQCoeff (heckeFun k ε i.1 ⇑g₁) := by
    rw [← coe_heckeTOne_nebentypus i.2.1 i.2.2 ε g₁ hg₁]; exact reg_coe _
  have r₂ : HasQCoeff (heckeFun k ε j.1 ⇑g₂) := by
    rw [← coe_heckeTOne_nebentypus j.2.1 j.2.2 ε g₂ hg₂]; exact reg_coe _
  refine UpperHalfPlane.eq_of_forall_qCoeff_eq r₁ r₂ fun n => ?_
  rw [qCoeff_heckeFun' i.2.1 ε g₁, qCoeff_heckeFun' j.2.1 ε g₂]
  have h₁ : ⇑g₁ = heckeFun k ε j.1 ⇑(f : CuspForm Γ₁(N) k) := by
    show ⇑((heckeT ε j f : nebSpace N k ε) : CuspForm Γ₁(N) k) = _
    rw [coe_heckeT]
  have h₂ : ⇑g₂ = heckeFun k ε i.1 ⇑(f : CuspForm Γ₁(N) k) := by
    show ⇑((heckeT ε i f : nebSpace N k ε) : CuspForm Γ₁(N) k) = _
    rw [coe_heckeT]
  rw [h₁, h₂]
  rw [qCoeff_heckeFun' j.2.1 ε _, qCoeff_heckeFun' i.2.1 ε _]
  exact cT_comm i.2.1 j.2.1 hpq _ _ _ n

end Hecke

section Petersson

variable [NeZero N] {k : ℤ}

def B (ε : DirichletCharacter ℂ N) (f g : nebSpace N k ε) : ℂ :=
  CuspForm.peterssonOn (Gamma1 N) k ⇑(f : CuspForm Γ₁(N) k) ⇑(g : CuspForm Γ₁(N) k)

theorem isPosDefHerm_B (ε : DirichletCharacter ℂ N) : SimulEigen.IsPosDefHerm (B (k := k) ε) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f g h
    exact (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (h : CuspForm Γ₁(N) k) 0).1
  · intro f c g
    exact (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) c).2.1
  · intro f g
    exact (CuspForm.peterssonOn_add_smul_conj (Gamma1 N) k (f : CuspForm Γ₁(N) k)
      (g : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) 0).2.2
  · intro f hf
    have h := (CuspForm.peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff (Gamma1 N) k
      (f : CuspForm Γ₁(N) k)).2.2.mp hf
    exact Subtype.ext h

omit [NeZero N] in
theorem norm_char_prime (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    ‖ε ((i.1 : ℕ) : ZMod N)‖ = 1 := by
  have hu : IsUnit ((i.1 : ℕ) : ZMod N) := (ZMod.isUnit_prime_iff_not_dvd i.2.1).mpr i.2.2
  have := ε.unit_norm_eq_one hu.unit
  rwa [IsUnit.unit_spec] at this

def croot (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : ℂ :=
  (IsAlgClosed.exists_pow_nat_eq (conj (ε ((i.1 : ℕ) : ZMod N))) two_pos).choose

omit [NeZero N] in
theorem croot_sq (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    croot ε i ^ 2 = conj (ε ((i.1 : ℕ) : ZMod N)) :=
  (IsAlgClosed.exists_pow_nat_eq (conj (ε ((i.1 : ℕ) : ZMod N))) two_pos).choose_spec

omit [NeZero N] in
theorem norm_croot (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : ‖croot ε i‖ = 1 := by
  have h : ‖croot ε i‖ ^ 2 = 1 := by
    rw [← norm_pow, croot_sq, Complex.norm_conj, norm_char_prime]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp h

omit [NeZero N] in
theorem croot_ne_zero (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : croot ε i ≠ 0 := by
  intro h; have := norm_croot ε i; rw [h, norm_zero] at this; exact zero_ne_one this

omit [NeZero N] in
theorem conj_croot_mul (ε : DirichletCharacter ℂ N) (i : GoodPrime N) :
    conj (croot ε i) * conj (ε ((i.1 : ℕ) : ZMod N)) = croot ε i := by
  rw [← Complex.inv_eq_conj (norm_croot ε i), ← croot_sq, sq, ← mul_assoc,
    inv_mul_cancel₀ (croot_ne_zero ε i), one_mul]

def heckeFamily (ε : DirichletCharacter ℂ N) (i : GoodPrime N) : nebSpace N k ε →ₗ[ℂ] nebSpace N k ε :=
  croot ε i • heckeT ε i

theorem heckeFamily_comm (ε : DirichletCharacter ℂ N) (i j : GoodPrime N) :
    Commute (heckeFamily (k := k) ε i) (heckeFamily ε j) :=
  ((heckeT_comm ε i j).smul_left _).smul_right _

theorem heckeFamily_selfAdjoint (ε : DirichletCharacter ℂ N) (i : GoodPrime N) (f g : nebSpace N k ε) :
    B ε (heckeFamily ε i f) g = B ε f (heckeFamily ε i g) := by
  have hB := isPosDefHerm_B (k := k) ε
  have hadj : B ε (heckeT ε i f) g
      = conj (ε ((i.1 : ℕ) : ZMod N)) * B ε f (heckeT ε i g) := by
    simp only [B, coe_heckeT]
    exact CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus N k ε i.2.1 i.2.2
      (f : CuspForm Γ₁(N) k) (g : CuspForm Γ₁(N) k) f.2 g.2
  rw [heckeFamily, LinearMap.smul_apply, LinearMap.smul_apply, hB.smul_left, hB.smul_right, hadj,
    ← mul_assoc, conj_croot_mul]

theorem span_eigen_eq_top (ε : DirichletCharacter ℂ N) :
    Submodule.span ℂ {v : nebSpace N k ε | ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v} = ⊤ := by
  have hFD : FiniteDimensional ℂ (CuspForm Γ₁(N) k) := CuspForm.finiteDimensional_Gamma1 N k
  exact (isPosDefHerm_B (k := k) ε).span_common_eigen (heckeFamily ε) (heckeFamily_comm ε)
    (heckeFamily_selfAdjoint ε)

end Petersson

section Assembly

variable [NeZero N] {k : ℤ}

def eigenSet (N : ℕ) [NeZero N] (k : ℤ) : Set (CuspForm Γ₁(N) k) :=
  {v | ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε v ∧
    ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
      ModularFormClass.qCoeff v (p * m) +
          ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
            (if p ∣ m then ModularFormClass.qCoeff v (m / p) else 0) =
        lam * ModularFormClass.qCoeff v m}

theorem mem_eigenSet_of_eigen (ε : DirichletCharacter ℂ N) (v : nebSpace N k ε)
    (hv : ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v) :
    (v : CuspForm Γ₁(N) k) ∈ eigenSet N k := by
  refine ⟨ε, v.2, fun p hp hpN => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨p, hp, hpN⟩
  set lam : ℂ := (croot ε ⟨p, hp, hpN⟩)⁻¹ * c with hlam
  have hL : heckeT ε ⟨p, hp, hpN⟩ v = lam • v := by
    have h1 : croot ε ⟨p, hp, hpN⟩ • heckeT ε ⟨p, hp, hpN⟩ v = c • v := hc
    have h2 : (croot ε ⟨p, hp, hpN⟩)⁻¹ • (croot ε ⟨p, hp, hpN⟩ • heckeT ε ⟨p, hp, hpN⟩ v)
        = (croot ε ⟨p, hp, hpN⟩)⁻¹ • (c • v) := by rw [h1]
    rw [smul_smul, inv_mul_cancel₀ (croot_ne_zero ε ⟨p, hp, hpN⟩), one_smul] at h2
    rw [h2, hlam, smul_smul]
  have hfun : heckeFun k ε p ⇑(v : CuspForm Γ₁(N) k) = lam • ⇑(v : CuspForm Γ₁(N) k) := by
    have := congrArg (fun w : nebSpace N k ε => (⇑(w : CuspForm Γ₁(N) k) : ℍ → ℂ)) hL
    simp only [Submodule.coe_smul, FunLike.coe_smul] at this
    rwa [coe_heckeT] at this
  refine ⟨lam, fun m => ?_⟩
  have hq := congrArg (fun F : ℍ → ℂ => ModularFormClass.qCoeff F m) hfun
  have hsm : ModularFormClass.qCoeff (lam • ⇑(v : CuspForm Γ₁(N) k)) m
      = lam * ModularFormClass.qCoeff (⇑(v : CuspForm Γ₁(N) k)) m := by
    rw [ModularFormClass.qCoeff, ModularFormClass.qCoeff,
      qExpansion_smul (reg_analyticAt (reg_coe (v : CuspForm Γ₁(N) k))), _root_.map_smul, smul_eq_mul]
  rw [qCoeff_heckeFun hp ε _ m, hsm] at hq
  rw [mul_comm p m]
  exact hq

theorem nebSpace_le_span (ε : DirichletCharacter ℂ N) :
    (nebSpace N k ε : Submodule ℂ (CuspForm Γ₁(N) k)) ≤ Submodule.span ℂ (eigenSet N k) := by
  intro g hg
  have hmem : (⟨g, hg⟩ : nebSpace N k ε) ∈
      Submodule.span ℂ {v : nebSpace N k ε | ∀ i : GoodPrime N, ∃ c : ℂ, heckeFamily ε i v = c • v} := by
    rw [span_eigen_eq_top]; trivial
  have himg := Submodule.mem_map_of_mem (f := (nebSpace N k ε).subtype) hmem
  rw [Submodule.map_span] at himg
  refine Submodule.span_mono ?_ himg
  rintro _ ⟨v, hv, rfl⟩
  exact mem_eigenSet_of_eigen ε v hv

theorem span_eigenSet_eq_top : Submodule.span ℂ (eigenSet N k) = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have := mem_iSup_nebSpace (k := k) g
  exact (iSup_le fun ε => nebSpace_le_span (k := k) ε) this

theorem main (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm Γ₁(N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m := by
  have hFD : FiniteDimensional ℂ (CuspForm Γ₁(N) k) := CuspForm.finiteDimensional_Gamma1 N k
  obtain ⟨t, ht, hspan, hli⟩ := exists_linearIndependent ℂ (eigenSet N k)
  have hfin : t.Finite := hli.setFinite
  let hFt : Fintype t := hfin.fintype
  have htop : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : t → CuspForm Γ₁(N) k)) := by
    rw [Subtype.range_coe, hspan, span_eigenSet_eq_top]
  let b₀ : Module.Basis t ℂ (CuspForm Γ₁(N) k) := Module.Basis.mk hli htop
  let e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  refine ⟨Fintype.card t, b₀.reindex e, fun i => ?_⟩
  have hbi : (b₀.reindex e) i = ((e.symm i : t) : CuspForm Γ₁(N) k) := by
    rw [Module.Basis.reindex_apply, Module.Basis.mk_apply]
  have hmem : (b₀.reindex e) i ∈ eigenSet N k := by
    rw [hbi]; exact ht (e.symm i).2
  exact hmem

end Assembly

end SSbasis

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1 N) k)),
      ∀ i, ∃ ε : DirichletCharacter ℂ N, CuspForm.HasNebentypus ε (b i) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∃ lam : ℂ, ∀ m : ℕ,
          ModularFormClass.qCoeff (b i) (p * m) +
              ε (p : ZMod N) * (p : ℂ) ^ (k - 1) *
                (if p ∣ m then ModularFormClass.qCoeff (b i) (m / p) else 0) =
            lam * ModularFormClass.qCoeff (b i) m :=
  SSbasis.main N k

end
