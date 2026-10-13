/-
  The support of a compactly supported function on the finite adèles: the open
  integral-off sets `integralOff S` (outside-`S` integrality), their exhaustion of
  the finite adèles (`mem_integralOff_exceptional`), the resulting
  `exists_finset_tsupport_subset`, and the uniformizer boxes `boxAt` with their
  openness, monotonicity and existence (`exists_box`).

  Transcribed from the pin's `Fold_ShellSupport` section
  (`M4aLocalCFT.ShellSupport`), declared lines 4726-4872 of file B, pinned
  `aa2d8b3`:
  `https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_integrable_zetaIntegrand.lean`

  Build notes: the pin's `p2m_*` scaffolding is dropped; `M4aLocalCFT.` is renamed
  to `NumberField.TateGlobal.`.  The pin's deprecated `Set.mem_setOf_eq` is spelled
  `Set.mem_ofPred_eq` (proof-only).  No file-wide option beyond
  `set_option autoImplicit false`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.UnifPowBridge

set_option autoImplicit false

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing NumberField
open NumberField.AdelicLevel NumberField.AdelicVolume NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open MeasureTheory MeasureTheory.Measure Set Filter Topology TopologicalSpace
open LanglandsTunnell.TateLocal
open scoped NNReal ENNReal Pointwise Topology NumberField.TateGlobal Classical

section Fold_ShellSupport

open NumberField.TateGlobal

open scoped NNReal

noncomputable section

namespace NumberField
namespace TateGlobal
namespace ShellSupport

variable {F : Type} [Field F] [NumberField F]

-- pin: integralOff (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4726)
def integralOff (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (FiniteAdeleRing (𝓞 F) F) :=
  {x | ∀ v, v ∉ S → x v ∈ v.adicCompletionIntegers F}

-- pin: integralOff_mono (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4729)
theorem integralOff_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    integralOff (F := F) S ⊆ integralOff T :=
  fun _x hx v hv => hx v fun hvS => hv (hST hvS)

-- pin: isOpen_integralOff (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4733)
theorem isOpen_integralOff (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (integralOff (F := F) S) := by
  have h := RestrictedProduct.isOpen_forall_imp_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (fun v => (Valued.isOpen_integer (v.adicCompletion F)))
    (p := fun v => v ∉ S)
  exact h

-- pin: mem_integralOff_exceptional (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4742)
theorem mem_integralOff_exceptional (x : FiniteAdeleRing (𝓞 F) F) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), x ∈ integralOff S := by
  have hev : {v : HeightOneSpectrum (𝓞 F) | ¬ (x v ∈ v.adicCompletionIntegers F)}.Finite :=
    Filter.eventually_cofinite.mp x.2
  refine ⟨hev.toFinset, fun v hv => ?_⟩
  by_contra hnot
  exact hv (hev.mem_toFinset.mpr hnot)

-- pin: exists_finset_tsupport_subset (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4750)
theorem exists_finset_tsupport_subset {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    (hcs : HasCompactSupport h) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 F)), tsupport h ⊆ integralOff S := by
  classical
  have hcover : tsupport h ⊆
      ⋃ S : Finset (HeightOneSpectrum (𝓞 F)), integralOff (F := F) S := by
    intro x _
    obtain ⟨S, hS⟩ := mem_integralOff_exceptional x
    exact Set.mem_iUnion.mpr ⟨S, hS⟩
  obtain ⟨t, ht⟩ := hcs.elim_finite_subcover
    (fun S : Finset (HeightOneSpectrum (𝓞 F)) => integralOff (F := F) S)
    (fun S => isOpen_integralOff S) hcover
  refine ⟨t.sup id, ht.trans ?_⟩
  refine Set.iUnion₂_subset fun S hS => integralOff_mono ?_
  exact Finset.le_sup (f := id) hS

-- pin: apply_eq_zero (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4766)
theorem apply_eq_zero {h : FiniteAdeleRing (𝓞 F) F → ℂ}
    {S : Finset (HeightOneSpectrum (𝓞 F))} (hsupp : tsupport h ⊆ integralOff S)
    {x : FiniteAdeleRing (𝓞 F) F} (hx : x ∉ integralOff S) : h x = 0 :=
  image_eq_zero_of_notMem_tsupport fun hmem => hx (hsupp hmem)

-- pin: boxAt (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4771)
def boxAt (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    Set (v.adicCompletion F) :=
  {y | ((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y ∈ v.adicCompletionIntegers F}

-- pin: isOpen_boxAt (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4775)
theorem isOpen_boxAt (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) (m : ℕ) :
    IsOpen (boxAt ϖ v m) :=
  (Valued.isOpen_integer (v.adicCompletion F)).preimage
    (continuous_const.mul continuous_id)

-- pin: boxAt_mono (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4780)
theorem boxAt_mono (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) {m m' : ℕ}
    (hmm : m ≤ m') : boxAt ϖ v m ⊆ boxAt ϖ v m' := by
  intro y hy
  simp only [boxAt, Set.mem_ofPred_eq] at hy ⊢
  have hfac : ((ϖ.ϖ v ^ m' : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
      = ((ϖ.ϖ v ^ (m' - m) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
        * (((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y) := by
    rw [← mul_assoc, ← Units.val_mul, ← pow_add, Nat.sub_add_cancel hmm]
  rw [hfac]
  have hint : ((ϖ.ϖ v ^ (m' - m) : (v.adicCompletion F)ˣ) : v.adicCompletion F)
      ∈ v.adicCompletionIntegers F := by
    rw [mem_integers_iff_ordAt_nonneg]
    have h1 : ordAt v (ϖ.ϖ v ^ ((m' - m : ℕ) : ℤ)) = ((m' - m : ℕ) : ℤ) * 1 := by
      rw [ordAt_zpow, ϖ.ordAt_eq_one v]
    rw [zpow_natCast] at h1
    rw [h1]
    positivity
  exact mul_mem hint hy

-- pin: mem_boxAt_exists (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4799)
theorem mem_boxAt_exists (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F))
    (y : v.adicCompletion F) : ∃ m : ℕ, y ∈ boxAt ϖ v m := by
  rcases eq_or_ne y 0 with rfl | hy0
  · refine ⟨0, ?_⟩
    simp only [boxAt, Set.mem_ofPred_eq, mul_zero]
    exact zero_mem _
  · set u : (v.adicCompletion F)ˣ := Units.mk0 y hy0 with hu
    refine ⟨(-ordAt v u).toNat, ?_⟩
    have hcoe : ((ϖ.ϖ v ^ (-ordAt v u).toNat : (v.adicCompletion F)ˣ) : v.adicCompletion F) * y
        = ((ϖ.ϖ v ^ (-ordAt v u).toNat * u : (v.adicCompletion F)ˣ) : v.adicCompletion F) := by
      rw [Units.val_mul, hu, Units.val_mk0]
    simp only [boxAt, Set.mem_ofPred_eq]
    rw [hcoe, mem_integers_iff_ordAt_nonneg, ordAt_mul]
    have h1 : ordAt v (ϖ.ϖ v ^ (((-ordAt v u).toNat : ℕ) : ℤ)) = (((-ordAt v u).toNat : ℕ) : ℤ) * 1 := by
      rw [ordAt_zpow, ϖ.ordAt_eq_one v]
    rw [zpow_natCast] at h1
    rw [h1]
    omega

-- pin: exists_box (S_NumberField_TateGlobal_integrable_zetaIntegrand.lean:4818)
theorem exists_box {h : FiniteAdeleRing (𝓞 F) F → ℂ} (hcs : HasCompactSupport h)
    (ϖ : Uniformizers F) (v : HeightOneSpectrum (𝓞 F)) :
    ∃ m : ℕ, ∀ x ∈ tsupport h,
      ((ϖ.ϖ v ^ m : (v.adicCompletion F)ˣ) : v.adicCompletion F) * x v
        ∈ v.adicCompletionIntegers F := by
  have hcont : Continuous fun x : FiniteAdeleRing (𝓞 F) F => x v :=
    RestrictedProduct.continuous_eval v
  have himg : IsCompact ((fun x : FiniteAdeleRing (𝓞 F) F => x v) '' tsupport h) :=
    hcs.image hcont
  have hcover : ((fun x : FiniteAdeleRing (𝓞 F) F => x v) '' tsupport h) ⊆
      ⋃ m : ℕ, boxAt ϖ v m := by
    intro y _
    obtain ⟨m, hm⟩ := mem_boxAt_exists ϖ v y
    exact Set.mem_iUnion.mpr ⟨m, hm⟩
  obtain ⟨t, ht⟩ := himg.elim_finite_subcover (boxAt ϖ v) (isOpen_boxAt ϖ v) hcover
  rcases t.eq_empty_or_nonempty with rfl | htne
  · refine ⟨0, fun x hx => ?_⟩
    have := ht (Set.mem_image_of_mem _ hx)
    simp at this
  · refine ⟨t.max' htne, fun x hx => ?_⟩
    have hy := ht (Set.mem_image_of_mem _ hx)
    obtain ⟨m, hm, hym⟩ := Set.mem_iUnion₂.mp hy
    exact boxAt_mono ϖ v (t.le_max' m hm) hym

end ShellSupport

end NumberField.TateGlobal

end

end Fold_ShellSupport
