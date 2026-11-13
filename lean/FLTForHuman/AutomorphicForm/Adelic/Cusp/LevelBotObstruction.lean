/-
  The level-one obstruction: a "Hecke coset eigenfunction" cannot exist at trivial level.

  A function that is an eigenfunction of every Hecke coset operator at level one and lies in the
  mirabolic-trivial subspace `levelOne _ K N ⊓ finiteAdelicGL2Subgroup K` at `N = ⊥` is forced to be
  zero.  The proof reduces the level-one group to the mirabolic `mirabolicFin`, shows
  `levelOne ⊥ ⊓ top ⊆ mirabolicFin`, and derives the contradiction from the Hecke coset system of a
  local representation (`exists_isHeckeCosetSystem_localRep_heckeGen`), whose double-coset structure the
  pin's `lowerRowOne` and `doubleCoset_*` rows compute.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup.lean`
  (229 lines: thirteen public prelude rows under the pin's two-line label namespace and the headline),
  with the statement from the wrapper of the same name.  The pin's label is a pair of machine tokens
  (`Ws20` / `LevelBot`) and is rectified to the single word namespace `LevelBotObstruction`; the prelude
  rows are public in the pin and stay public here, which is why this module is checker-visible beyond the
  headline.

  Assumes from earlier modules: `Adelic/HeckeCosetSeam.lean`
  (`exists_isHeckeCosetSystem_localRep_heckeGen`, this row's premise) and
  `Adelic/Cusp/LevelOneObstruction.lean` (the level-one and mirabolic vocabulary at the same place).

  spec-pin: Theorems/Thm_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_SmoothCusp_not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.HeckeCosetSeam
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelOneObstruction
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicLevel.Projections
import FLTForHuman.NumberTheory.AdelicBox
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.RepTheory.LocalLanglands.HeckeCosetLocal
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.CuspidalConstituent
open NumberField.SiegelVolume HeckeIntegralSeam LocalGL2 AdelicDock
open scoped ComplexConjugate ENNReal InnerProductSpace BigOperators Topology

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace LevelBotObstruction

def lowerRowOne (R : Type*) [CommRing R] : Subgroup (GL (Fin 2) R) where
  carrier := {g | (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1}
  one_mem' := ⟨by simp, by simp⟩
  mul_mem' := by
    rintro g h ⟨hg0, hg1⟩ ⟨hh0, hh1⟩
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh0]; ring
    · rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, hh1]; ring
  inv_mem' := by
    rintro g ⟨hg0, hg1⟩
    have hmul : (g : Matrix (Fin 2) (Fin 2) R) * ((g⁻¹ : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have h10 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 0) hmul
    have h11 := congrArg (fun M : Matrix (Fin 2) (Fin 2) R => M 1 1) hmul
    simp only [Matrix.mul_apply, Fin.sum_univ_two, hg0, hg1, zero_mul, one_mul, zero_add,
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), Matrix.one_apply_eq] at h10 h11
    exact ⟨h10, h11⟩

theorem mem_lowerRowOne_iff {R : Type*} [CommRing R] (g : GL (Fin 2) R) :
    g ∈ lowerRowOne R ↔ (g : Matrix (Fin 2) (Fin 2) R) 1 0 = 0 ∧ (g : Matrix (Fin 2) (Fin 2) R) 1 1 = 1 :=
  Iff.rfl

variable (F : Type) [Field F] [NumberField F]

noncomputable def mirabolicFin : Subgroup (AdelicGL2 (𝓞 F) F) :=
  (lowerRowOne (FiniteAdeleRing (𝓞 F) F)).comap (glFin (𝓞 F) F)

variable {F}

theorem mem_mirabolicFin_iff (g : AdelicGL2 (𝓞 F) F) :
    g ∈ mirabolicFin F ↔ ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 0 = 0 ∧
      ((glFin (𝓞 F) F g : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 :=
  Iff.rfl

theorem eq_zero_of_mem_idealBall_bot {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∈ idealBall (𝓞 F) F ⊥) : x = 0 := by
  refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
  have h := hx w
  rw [idealBound_bot, le_zero_iff, map_eq_zero] at h
  rw [h]; rfl

variable (F)

theorem levelOne_bot_inf_le_mirabolicFin :
    levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F ≤ mirabolicFin F := by
  intro k hk
  obtain ⟨hk1, -⟩ := Subgroup.mem_inf.mp hk
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1
  obtain ⟨⟨-, h10⟩, h11⟩ := hk1.1
  exact (mem_mirabolicFin_iff k).mpr
    ⟨eq_zero_of_mem_idealBall_bot h10, sub_eq_zero.mp (eq_zero_of_mem_idealBall_bot h11)⟩

theorem levelOne_bot_inf_le_top_inf :
    levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F ≤ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  intro k hk
  obtain ⟨hk1, hkf⟩ := Subgroup.mem_inf.mp hk
  refine Subgroup.mem_inf.mpr ⟨?_, hkf⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1 ⊢
  have hball : ∀ {x : FiniteAdeleRing (𝓞 F) F}, x ∈ idealBall (𝓞 F) F ⊥ → x ∈ idealBall (𝓞 F) F ⊤ :=
    fun hx => by rw [eq_zero_of_mem_idealBall_bot hx]; exact zero_mem_idealBall ⊤
  exact ⟨⟨⟨hk1.1.toIsLevelZeroMatrix.integral, hball hk1.1.lowerLeft⟩, hball hk1.1.lowerRight⟩,
    ⟨⟨hk1.2.toIsLevelZeroMatrix.integral, hball hk1.2.lowerLeft⟩, hball hk1.2.lowerRight⟩⟩

theorem mem_levelOne_bot_inf_of_mem_top_of_mem_mirabolicFin {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F) (hm : k ∈ mirabolicFin F) :
    k ∈ levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F := by
  obtain ⟨hk1, hkf⟩ := Subgroup.mem_inf.mp hk
  have hm' : k⁻¹ ∈ mirabolicFin F := inv_mem hm
  rw [mem_mirabolicFin_iff] at hm hm'
  rw [map_inv] at hm'
  refine Subgroup.mem_inf.mpr ⟨?_, hkf⟩
  rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1 ⊢
  refine ⟨⟨⟨hk1.1.toIsLevelZeroMatrix.integral, ?_⟩, ?_⟩, ⟨⟨hk1.2.toIsLevelZeroMatrix.integral, ?_⟩, ?_⟩⟩
  · rw [hm.1]; exact zero_mem_idealBall ⊥
  · rw [hm.2, sub_self]; exact zero_mem_idealBall ⊥
  · rw [hm'.1]; exact zero_mem_idealBall ⊥
  · rw [hm'.2, sub_self]; exact zero_mem_idealBall ⊥

theorem heckeGen_mem_mirabolicFin (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∈ mirabolicFin F := by
  rw [mem_mirabolicFin_iff, glFin_apply, glFin_apply]
  refine ⟨?_, ?_⟩
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw
      show (((heckeGenAt (𝓞 F) F w (uniformizerUnit F w) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 w = _
      rw [heckeGenAt_snd_apply_self]; rfl
    · show (((heckeGenAt (𝓞 F) F v (uniformizerUnit F v) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 0).2 w = _
      rw [heckeGenAt_snd_apply_of_ne _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw
      show (((heckeGenAt (𝓞 F) F w (uniformizerUnit F w) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 w = _
      rw [heckeGenAt_snd_apply_self]; rfl
    · show (((heckeGenAt (𝓞 F) F v (uniformizerUnit F v) : AdelicGL2 (𝓞 F) F) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) 1 1).2 w = _
      rw [heckeGenAt_snd_apply_of_ne _ hw, Matrix.one_apply_eq]; rfl

theorem finEmbed_localEmbed_mem_mirabolicFin (v : HeightOneSpectrum (𝓞 F)) (m : GL (Fin 2) (v.adicCompletion F))
    (h10 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0)
    (h11 : (m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1 = 1) :
    finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v m) ∈ mirabolicFin F := by
  rw [mem_mirabolicFin_iff, glFin_finEmbed, coe_localEmbed]
  refine ⟨?_, ?_⟩
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [localMat_apply_self, h10]; rfl
    · rw [localMat_apply_of_ne _ _ _ _ _ _ hw, Matrix.one_apply_ne (by decide)]; rfl
  · refine IsDedekindDomain.FiniteAdeleRing.ext (R := 𝓞 F) (K := F) fun w => ?_
    by_cases hw : w = v
    · subst hw; rw [localMat_apply_self, h11]; rfl
    · rw [localMat_apply_of_ne _ _ _ _ _ _ hw, Matrix.one_apply_eq]; rfl

theorem doubleCoset_mono {G : Type*} [Group G] {U U' : Subgroup G} (h : U ≤ U') (g : G) :
    HeckePair.doubleCoset U g ⊆ HeckePair.doubleCoset U' g := by
  intro x hx
  obtain ⟨u, hu, w, hw, hx⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact HeckePair.mem_doubleCoset_iff.mpr ⟨u, h hu, w, h hw, hx⟩

theorem doubleCoset_subset_of_le {G : Type*} [Group G] {U M : Subgroup G} (h : U ≤ M) {g : G} (hg : g ∈ M) :
    HeckePair.doubleCoset U g ⊆ M := by
  intro x hx
  obtain ⟨u, hu, w, hw, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  exact M.mul_mem (M.mul_mem (h hu) hg) (h hw)

theorem localRepInf_inv_entries {v : HeightOneSpectrum (𝓞 F)} (ϖ : v.adicCompletionIntegers F)
    (hϖ0 : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0) :
    (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 ∧
    (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 1
      = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)⁻¹ := by
  set M := (((localRepInf ϖ hϖ0)⁻¹ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) with hM
  have hmul : M * (localRepInf ϖ hϖ0 : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = 1 := by
    rw [hM, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  rw [coe_localRepInf] at hmul
  have h10 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => X 1 0) hmul
  have h11 := congrArg (fun X : Matrix (Fin 2) (Fin 2) (v.adicCompletion F) => X 1 1) hmul
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide),
    Matrix.one_apply_eq, mul_one, mul_zero, add_zero, zero_add] at h10 h11
  exact ⟨h10, eq_inv_of_mul_eq_one_left h11⟩

end LevelBotObstruction

theorem AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ) :
    ¬ SmoothCusp.IsHeckeCosetEigenfunctionAt F (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) v φ c := by
  classical
  rintro ⟨reps, hsys, -⟩
  obtain ⟨ϖ, hϖ0, hϖ1, -, sec, -, hsysAll⟩ :=
    HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen F v
  have hndvd : ¬ v.asIdeal ∣ (⊤ : Ideal (𝓞 F)) := fun h =>
    v.isPrime.ne_top (top_le_iff.mp (Ideal.le_of_dvd h))
  have htop := hsysAll ⊤ hndvd

  have claimA : ∀ i, ∃ cc : 𝓞 F ⧸ v.asIdeal,
      (QuotientGroup.mk (reps i) : AdelicGL2 (𝓞 F) F ⧸ (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F))
        = QuotientGroup.mk (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec cc))))) := by
    intro i
    have hyb := hsys.mem_doubleCoset i
    have hyt : reps i ∈ HeckePair.doubleCoset (levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F)
        (heckeGen (𝓞 F) F v) :=
      LevelBotObstruction.doubleCoset_mono (LevelBotObstruction.levelOne_bot_inf_le_top_inf F) _ hyb
    have hyM : reps i ∈ LevelBotObstruction.mirabolicFin F :=
      LevelBotObstruction.doubleCoset_subset_of_le (LevelBotObstruction.levelOne_bot_inf_le_mirabolicFin F)
        (LevelBotObstruction.heckeGen_mem_mirabolicFin F v) hyb
    obtain ⟨j, hj⟩ := htop.covers (reps i) hyt
    have hk := QuotientGroup.eq.mp hj.symm

    cases j with
    | none =>
      exfalso
      simp only [Option.elim] at hk
      obtain ⟨hk1, -⟩ := Subgroup.mem_inf.mp hk
      rw [mem_levelOne_iff, mem_finiteLevelOne_iff] at hk1
      have hint := hk1.1.toIsLevelZeroMatrix.integral 1 1

      obtain ⟨hI10, hI11⟩ := LevelBotObstruction.localRepInf_inv_entries (F := F) ϖ hϖ0
      have hy11 : ((glFin (𝓞 F) F (reps i) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
          Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 = 1 :=
        ((LevelBotObstruction.mem_mirabolicFin_iff _).mp hyM).2
      have hentry : ((glFin (𝓞 F) F ((finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v (localRepInf ϖ hϖ0)))⁻¹ * reps i) :
            GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (FiniteAdeleRing (𝓞 F) F)) 1 1 v
          = (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ)⁻¹ := by
        rw [map_mul, map_inv, glFin_finEmbed, ← map_inv, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
          coe_localEmbed, coe_add_apply, coe_mul_apply, coe_mul_apply, localMat_apply_self, localMat_apply_self,
          hI10, hI11, hy11, zero_mul, zero_add, coe_one_apply, mul_one]
      have hmem := hint v
      rw [hentry, HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀] at hmem
      have hval : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ) := hϖ1
      rw [hval, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hmem
      omega
    | some cc =>
      refine ⟨cc, ?_⟩
      simp only [Option.elim] at hk
      have hkM : (finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v
            (localRepSome ϖ hϖ0 (algebraMap (𝓞 F) (v.adicCompletionIntegers F) (sec cc)))))⁻¹ * reps i ∈
            LevelBotObstruction.mirabolicFin F := by
        refine (LevelBotObstruction.mirabolicFin F).mul_mem (inv_mem ?_) hyM
        refine LevelBotObstruction.finEmbed_localEmbed_mem_mirabolicFin F v _ ?_ ?_
        · rw [coe_localRepSome]; rfl
        · rw [coe_localRepSome]; rfl
      exact (QuotientGroup.eq.mpr
        (LevelBotObstruction.mem_levelOne_bot_inf_of_mem_top_of_mem_mirabolicFin F hk hkM)).symm

  choose f hf using claimA
  have hfinj : Function.Injective f := by
    intro i j hij
    apply hsys.mk_injective
    show (QuotientGroup.mk (reps i) : AdelicGL2 (𝓞 F) F ⧸ (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F))
      = QuotientGroup.mk (reps j)
    rw [hf i, hf j, hij]
  have hcard : Nat.card (𝓞 F ⧸ v.asIdeal) = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hN : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hfin : Finite (𝓞 F ⧸ v.asIdeal) := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hN)
  have hle : Nat.card (Fin (Ideal.absNorm v.asIdeal + 1)) ≤ Nat.card (𝓞 F ⧸ v.asIdeal) :=
    @Nat.card_le_card_of_injective _ _ hfin f hfinj
  rw [Nat.card_fin, hcard] at hle
  omega
