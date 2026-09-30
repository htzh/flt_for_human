/-
  The remainder of the Γ₁ Hecke-operator layer: the rational models
  `heckeMatrixQ`/`heckeDiagMatrixQ`, the cusp transport lemmas
  (`isCusp_smul_map`, `isZeroAt_slash_map`, `isZeroAt_zero`,
  `isZeroAt_finset_sum`, `isZeroAt_slash_heckeDiagMatrix`), the coset-sum
  rewriting (`sum_eq`, `sum_slash_mapGL_of_mem_Gamma0`, `sum_slash_mapGL`) and
  the Γ₁-invariance of `U_p + T_p` (`heckeU_add_slash_heckeDiagMatrix_slash*`),
  followed by the diamond-twisted Hecke operators `heckeTOne`/`heckeTLinOne`.

  Transcribed from `Definitions/Def_CuspForm_Gamma1HeckeOperators.lean`
  (pinned `aa2d8b3`, 680 lines). The Γ₁/diamond half is already on disk in
  `ModularForms/Level/Diamond.lean` and `ModularForms/Defs/HeckeRepresentatives.lean`;
  this module carries the declarations absent from the port. The pin names whose
  port copies carry a *different* statement — `mdifferentiable_heckeU`,
  `isZeroAt_heckeU`, the four `…_mul_of_eq` lemmas and (binder-only)
  `sum_range_eq_sum_zmod` — are deliberately not re-declared here; their
  reconciliation is phase H2 (see `topics/deligneSerre/TOPIC-definitions-and-homes.md`
  §3) and the local proofs below use the port's existing versions instead.
-/
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Algebra.Field.ZMod
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import FLTForHuman.ModularForms.Defs.HeckeOperator
import FLTForHuman.ModularForms.Defs.HeckeRepresentatives
import FLTForHuman.ModularForms.Level.Diamond
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckeCusps

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane ModularForm
open ModularForm.HeckeRepresentatives ModularForm.Level
open scoped MatrixGroups ModularForm OnePoint Manifold ModularForm.HeckeRepresentatives

namespace CuspForm.Gamma1Hecke

def heckeMatrixQ (p j : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (p : ℚ)]
    (by rw [Matrix.det_fin_two_of]; simpa using hp)

def heckeDiagMatrixQ (p : ℕ) (hp : p ≠ 0) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(p : ℚ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simpa using hp)

theorem map_heckeMatrixQ {p : ℕ} (hp : p ≠ 0) (j : ℕ) :
    (heckeMatrixQ p j hp).map (Rat.castHom ℝ) = heckeMatrix p j := by
  apply Units.ext
  rw [val_heckeMatrix hp]
  change ((heckeMatrixQ p j hp : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeMatrixQ
  ext a b; fin_cases a <;> fin_cases b <;> simp

theorem map_heckeDiagMatrixQ {p : ℕ} (hp : p ≠ 0) :
    (heckeDiagMatrixQ p hp).map (Rat.castHom ℝ) = heckeDiagMatrix p := by
  apply Units.ext
  rw [val_heckeDiagMatrix hp]
  change ((heckeDiagMatrixQ p hp : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ).map (Rat.castHom ℝ) = _
  unfold heckeDiagMatrixQ
  ext a b; fin_cases a <;> fin_cases b <;> simp

theorem isCusp_smul_map {c : OnePoint ℝ} (hc : IsCusp c 𝒮ℒ) (g : GL (Fin 2) ℚ) :
    IsCusp (g.map (Rat.castHom ℝ) • c) 𝒮ℒ := by
  rw [isCusp_SL2Z_iff] at hc ⊢
  obtain ⟨c₀, rfl⟩ := hc
  exact ⟨g • c₀, by rw [← Rat.coe_castHom, OnePoint.map_smul]⟩

theorem isZeroAt_slash_map {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) (g : GL (Fin 2) ℚ) {c : OnePoint ℝ}
    (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] g.map (Rat.castHom ℝ)) k := by
  refine OnePoint.IsZeroAt.smul_iff.mp (CuspFormClass.zero_at_cusps f ?_)
  rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc ⊢
  exact isCusp_smul_map hc g

theorem isZeroAt_zero {c : OnePoint ℝ} {k : ℤ} : c.IsZeroAt (0 : ℍ → ℂ) k := fun g _ => by
  rw [SlashAction.zero_slash]
  exact Filter.zero_zeroAtFilter _

theorem isZeroAt_finset_sum {ι : Type*} {c : OnePoint ℝ} {k : ℤ} (s : Finset ι) (G : ι → ℍ → ℂ)
    (h : ∀ i ∈ s, c.IsZeroAt (G i) k) : c.IsZeroAt (∑ i ∈ s, G i) k :=
  Finset.sum_induction G (fun H => c.IsZeroAt H k) (fun _ _ ha hb => ha.add hb) isZeroAt_zero h

theorem isZeroAt_slash_heckeDiagMatrix {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)}
    [Γ.IsArithmetic] {k : ℤ} [CuspFormClass F Γ k] (f : F) {p : ℕ} (hp : p ≠ 0)
    {c : OnePoint ℝ} (hc : IsCusp c Γ) : c.IsZeroAt (⇑f ∣[k] heckeDiagMatrix p) k := by
  rw [← map_heckeDiagMatrixQ hp]
  exact isZeroAt_slash_map f _ hc

section heckeT

variable {p : ℕ} [Fact p.Prime]

variable {N : ℕ} (k : ℤ)

theorem sum_eq (f : ℍ → ℂ) (σ : SL(2, ℤ)) :
    heckeU k p f + (f ∣[k] mapGL ℝ σ) ∣[k] heckeDiagMatrix p
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [heckeU_eq_sum_zmod, add_comm, ← SlashAction.slash_mul]
  refine Eq.trans ?_
    (Fintype.sum_option (fun x : OnePoint (ZMod p) ↦ f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))).symm
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  change f ∣[k] heckeMatrix p j.val = f ∣[k] (mapGL ℝ (lift σ (j : OnePoint (ZMod p))) * heckeRep p j)
  rw [lift_coe, map_one, one_mul, heckeRep_coe]

theorem sum_slash_mapGL_of_mem_Gamma0 (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    (∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] (mapGL ℝ g)
      = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [SlashAction.sum_slash]
  calc ∑ x : OnePoint (ZMod p), (f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] mapGL ℝ g
      = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ (redMatrix p g • x))
          * heckeRep p (redMatrix p g • x)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        obtain ⟨g', hg', hd', hmul⟩ :=
          ModularForm.HeckeRepresentatives.Gamma1Hecke.heckeRep_mul hpN g hg x
        have hg'N : g' ∈ CongruenceSubgroup.Gamma0 N :=
          CongruenceSubgroup.Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hg')

        set D : SL(2, ℤ) := lift σ x * g' * (lift σ (redMatrix p g • x))⁻¹ * g⁻¹ with hD
        have hDmem0 : D ∈ CongruenceSubgroup.Gamma0 N :=
          mul_mem (mul_mem (mul_mem (lift_mem σ hσ x) hg'N) (inv_mem (lift_mem σ hσ _))) (inv_mem hg)
        have hDd : ((D 1 1 : ℤ) : ZMod N) = 1 := by
          have hprod : D * g * lift σ (redMatrix p g • x) = lift σ x * g' := by
            rw [hD, inv_mul_cancel_right, inv_mul_cancel_right]
          have h1 : (((D * g * lift σ (redMatrix p g • x)) 1 1 : ℤ) : ZMod N)
              = (((lift σ x * g') 1 1 : ℤ) : ZMod N) :=
            congrArg (fun γ : SL(2, ℤ) => ((γ 1 1 : ℤ) : ZMod N)) hprod
          rw [d_mul (mul_mem hDmem0 hg) (lift_mem σ hσ _), d_mul hDmem0 hg,
            d_mul (lift_mem σ hσ x) hg'N, lift_apply_one_one σ hσp, lift_apply_one_one σ hσp,
            mul_comm (wt N p x), hd', mul_assoc] at h1
          have hu : IsUnit (((g 1 1 : ℤ) : ZMod N) * wt N p (redMatrix p g • x)) :=
            (isUnit_d hg).mul (isUnit_wt hpN _)
          exact hu.mul_left_injective (h1.trans (one_mul _).symm)
        have hDmem : D ∈ CongruenceSubgroup.Gamma1 N := mem_Gamma1_of_d_eq_one hDmem0 hDd
        have hfactor : mapGL ℝ (lift σ x) * heckeRep p x * mapGL ℝ g
            = mapGL ℝ D * (mapGL ℝ g
              * (mapGL ℝ (lift σ (redMatrix p g • x)) * heckeRep p (redMatrix p g • x))) := by
          rw [mul_assoc, hmul, ← mul_assoc, ← map_mul, hD, ← mul_assoc, ← mul_assoc, ← map_mul,
            ← map_mul, inv_mul_cancel_right, inv_mul_cancel_right]
        rw [← SlashAction.slash_mul, hfactor, SlashAction.slash_mul,
          hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hDmem), SlashAction.slash_mul]
    _ = ∑ x : OnePoint (ZMod p), (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) :=
        Equiv.sum_comp (MulAction.toPerm (redMatrix p g))
          (fun x ↦ (f ∣[k] mapGL ℝ g) ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x))

theorem sum_slash_mapGL (hpN : ¬ p ∣ N) (f : ℍ → ℂ)
    (hf : ∀ γ ∈ (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (g : SL(2, ℤ)) (hg : g ∈ CongruenceSubgroup.Gamma1 N) :
    (∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x)) ∣[k] (mapGL ℝ g)
      = ∑ x : OnePoint (ZMod p), f ∣[k] (mapGL ℝ (lift σ x) * heckeRep p x) := by
  rw [sum_slash_mapGL_of_mem_Gamma0 k hpN f hf σ hσ hσp g (CongruenceSubgroup.Gamma1_in_Gamma0 N hg),
    hf _ (Subgroup.mem_map_of_mem (mapGL ℝ) hg)]

end heckeT

theorem heckeU_add_slash_heckeDiagMatrix_slash
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    (γ : GL (Fin 2) ℝ)
    (hγ : γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :
    (heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] γ
      = heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg, rfl⟩ := hγ
  rw [sum_eq k f σ]
  exact sum_slash_mapGL k hpN f hf σ hσ hσp g hg

theorem heckeU_add_slash_heckeDiagMatrix_slash_of_mem_Gamma0
    {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N) {f : ℍ → ℂ}
    (hf : ∀ γ ∈ ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)),
      f ∣[k] γ = f)
    (σ : SL(2, ℤ)) (hσ : σ ∈ CongruenceSubgroup.Gamma0 N) (hσp : ((σ 1 1 : ℤ) : ZMod N) = p)
    {g : SL(2, ℤ)} (hg : g ∈ CongruenceSubgroup.Gamma0 N) :
    (heckeU k p f + (f ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p) ∣[k] (mapGL ℝ g)
      = heckeU k p (f ∣[k] (mapGL ℝ g))
        + ((f ∣[k] (mapGL ℝ g)) ∣[k] (mapGL ℝ σ)) ∣[k] heckeDiagMatrix p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [sum_eq k f σ, sum_eq k (f ∣[k] mapGL ℝ g) σ]
  exact sum_slash_mapGL_of_mem_Gamma0 k hpN f hf σ hσ hσp g hg

end CuspForm.Gamma1Hecke

open CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace CuspForm

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))
local notation "Γ₀ℝ" M => ((Gamma0 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Hecke

variable (k : ℤ) {M ℓ : ℕ}

def heckeTOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) : CuspForm (Γ₁ℝ M) k :=
  haveI : NeZero M := ⟨fun h => hℓM (h ▸ dvd_zero ℓ)⟩
  { toFun := heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ
    slash_action_eq' := fun γ hγ => by
      obtain ⟨σ, hσ⟩ := exists_isDiamondLift_of_coprime (M := M)
        ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)
      rw [coe_diamondLinOne_apply hσ]
      exact Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash k hℓ hℓM
        (fun γ hγ => SlashInvariantFormClass.slash_action_eq f γ hγ) σ hσ.1 hσ.2 γ hγ
    holo' := (mdifferentiable_heckeU (CuspFormClass.holo f) k ℓ).add
      ((CuspFormClass.holo (diamondLinOne M k ℓ f)).slash k _)
    zero_at_cusps' := fun {c} hc =>
      (CuspFormClass.isZeroAt_heckeU f ℓ hc).add
        (Gamma1Hecke.isZeroAt_slash_heckeDiagMatrix (diamondLinOne M k ℓ f) hℓ.ne_zero hc) }

@[simp] theorem coe_heckeTOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTOne k hℓ hℓM f) = heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ := rfl

def heckeTLinOne (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : CuspForm (Γ₁ℝ M) k →ₗ[ℂ] CuspForm (Γ₁ℝ M) k where
  toFun := heckeTOne k hℓ hℓM
  map_add' f g := DFunLike.coe_injective <| by
    simp only [coe_heckeTOne, CuspForm.coe_add, map_add, heckeU_add, SlashAction.add_slash]
    abel
  map_smul' c f := DFunLike.coe_injective <| by
    simp only [coe_heckeTOne, CuspForm.IsGLPos.coe_smul, map_smul, heckeU_smul, RingHom.id_apply,
      ModularForm.smul_slash, σ_heckeDiagMatrix, ContinuousAlgEquiv.refl_apply, smul_add]

@[simp] theorem coe_heckeTLinOne_apply (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTLinOne k hℓ hℓM f) = heckeU k ℓ ⇑f + (⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ :=
  rfl

theorem coe_heckeTLinOne_apply_of_isDiamondLift (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {σ : SL(2, ℤ)}
    (hσ : IsDiamondLift M ℓ σ) (f : CuspForm (Γ₁ℝ M) k) :
    ⇑(heckeTLinOne k hℓ hℓM f)
      = heckeU k ℓ ⇑f + (⇑f ∣[k] (Matrix.SpecialLinearGroup.mapGL ℝ σ)) ∣[k] heckeDiagMatrix ℓ := by
  rw [coe_heckeTLinOne_apply, coe_diamondLinOne_apply hσ]

theorem heckeTLinOne_apply_apply (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (f : CuspForm (Γ₁ℝ M) k) (τ : ℍ) :
    heckeTLinOne k hℓ hℓM f τ
      = heckeU k ℓ ⇑f τ + ((⇑(diamondLinOne M k ℓ f)) ∣[k] heckeDiagMatrix ℓ) τ :=
  rfl

end Hecke

end CuspForm

end
