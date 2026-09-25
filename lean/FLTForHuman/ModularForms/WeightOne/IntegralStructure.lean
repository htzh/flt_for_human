/-
  The capstone: the trace lemma and the integral structure (route C′).

  This is the only module that creates `CuspForm.HasIntegralStructure`, replacing
  the pin's 657-node Eichler–Shimura tower. The mathematics is
  `math/013-integral-structure-gamma1-basis.md` §5: for `Γ₁(N) ⊴ Γ₀(N)` of finite
  index `r`, with `b₁ … bₙ` a `ℂ`-basis of `S_k(Γ₁)` whose `Γ₀`-translates have
  integral `q`-coefficients, the trace `T(bᵢ) = ∑_{q : Γ₀ ⼸ Γ₁} bᵢ ∣[k] q` is a
  `Γ₀`-cusp form with integral `q`-coefficients, and `{T(bᵢ)}` spans `S_k(Γ₀)`
  because `T(w) = r · w` for `w ∈ S_k(Γ₀)`.

  Headlines:
  * `CuspForm.hasIntegralStructure_of_basis_gamma1` — **ours**: FLT reaches this
    statement only through the Eichler–Shimura tower, so it has no wrapper. The
    proof consumes mathlib's bundled `CuspForm.trace`
    (`Mathlib/NumberTheory/ModularForms/NormTrace.lean`). The one API gap is that
    `[𝒢.IsFiniteRelIndex 𝒧]` is not an instance for `Γ₁ ≤ Γ₀`; the local
    `private instance instIsFiniteRelIndexGamma1Gamma0` supplies it from the
    `SL(2, ℤ)` relative index (`Subgroup.relIndex_comap` +
    `Subgroup.comap_map_eq_self_of_injective mapGL_injective`, then
    `Subgroup.relIndex_mul_index` with `(Gamma1 N).FiniteIndex`).
  * `CuspForm.hasIntegralStructure_of_two_le` and `CuspForm.hasIntegralStructure_two`
    — statements verbatim from the pinned wrappers
    `Theorems/Thm_CuspForm_hasIntegralStructure_of_two_le.lean` and
    `Theorems/Thm_CuspForm_hasIntegralStructure_two.lean`; both are corollaries
    of the trace lemma applied to SET-11's
    `CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (`hk` unused).

  Proof shape: the restriction `restrictCusp : CuspForm Γ₀ k → CuspForm Γ₁ k` is
  the identity on functions, and `trace ∘ restrictCusp = r • id` as bundled forms
  (`trace_restrictCusp`, by function extensionality over the quotient sum). The
  basis expansion of `restrictCusp w` is pushed through the additivity and
  `ℂ`-homogeneity of `trace` (`trace_sum_smul`, from `quotientFunc_add` /
  `quotientFunc_smul`), and each `trace (bᵢ)` lies in `intLattice` because its
  `q`-expansion is the finite sum of the `q`-expansions of the `Γ₁`-translates
  (`qCoeffLin`, built from `UpperHalfPlane.qExpansion_add`/`qExpansion_smul`; the
  local `attribute [local instance] Fintype.ofFinite` supplies the quotient
  `Fintype`, since `CuspForm.trace` uses `Fintype.ofFinite` internally and no
  global instance exists).

  `Γ₁(N) ⊴ Γ₀(N)` is needed only for the translates `translateCusp` /
  `traceSummand`; it is proved locally (`conj_mem_Gamma1`) since mathlib exposes
  `Gamma1' N` as a kernel. Every helper above the three headlines is `private`.

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_hasIntegralStructure_of_two_le.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_hasIntegralStructure_two.lean
-/

import FLTForHuman.ModularForms.WeightOne.Gamma1IntegralBasis
import FLTForHuman.ModularForms.Defs.IntegralStructure
import Mathlib.NumberTheory.ModularForms.NormTrace
import Mathlib.NumberTheory.ModularForms.Cusps
import Mathlib.NumberTheory.ModularForms.Identities

set_option autoImplicit false

noncomputable section

open CongruenceSubgroup ModularForm ModularFormClass SlashInvariantForm UpperHalfPlane Matrix
open scoped ModularForm MatrixGroups UpperHalfPlane

attribute [local instance] Fintype.ofFinite

namespace CuspForm

private abbrev Gamma0GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma0 N
private abbrev Gamma1GL (N : ℕ) : Subgroup (GL (Fin 2) ℝ) := CongruenceSubgroup.Gamma1 N

private lemma relIndex_mapGL_ne_zero (N : ℕ) [NeZero N] : (Gamma1GL N).relIndex (Gamma0GL N) ≠ 0 := by
  rw [← Subgroup.relIndex_comap (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma1 N)) (Matrix.SpecialLinearGroup.mapGL ℝ)
      (CongruenceSubgroup.Gamma0 N),
    Subgroup.comap_map_eq_self_of_injective Matrix.SpecialLinearGroup.mapGL_injective]
  intro h0
  have hmul := Subgroup.relIndex_mul_index (CongruenceSubgroup.Gamma1_in_Gamma0 N)
  have hidx : (CongruenceSubgroup.Gamma1 N).index ≠ 0 :=
    (CongruenceSubgroup.instFiniteIndexGamma1 N).index_ne_zero
  exact hidx (by rw [← hmul, h0, zero_mul])

private instance instIsFiniteRelIndexGamma1Gamma0 (N : ℕ) [NeZero N] :
    (Gamma1GL N).IsFiniteRelIndex (Gamma0GL N) := ⟨relIndex_mapGL_ne_zero N⟩

private lemma le_Gamma1_Gamma0 (N : ℕ) : Gamma1GL N ≤ Gamma0GL N :=
  Subgroup.map_mono (f := Matrix.SpecialLinearGroup.mapGL ℝ) (CongruenceSubgroup.Gamma1_in_Gamma0 N)

private lemma conj_mem_Gamma1 {N : ℕ} {γ x : SL(2, ℤ)} (hγ : γ ∈ CongruenceSubgroup.Gamma0 N)
    (hx : x ∈ CongruenceSubgroup.Gamma1 N) :
    γ * x * γ⁻¹ ∈ CongruenceSubgroup.Gamma1 N := by
  have hx0 : x ∈ CongruenceSubgroup.Gamma0 N := CongruenceSubgroup.Gamma1_in_Gamma0 N hx
  have hx' : (⟨x, hx0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem]
    exact (CongruenceSubgroup.Gamma1_mem N x).1 hx
  have hN : (CongruenceSubgroup.Gamma1' N).Normal := MonoidHom.normal_ker _
  have hc : (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N) * ⟨x, hx0⟩ *
      (⟨γ, hγ⟩ : CongruenceSubgroup.Gamma0 N)⁻¹ ∈ CongruenceSubgroup.Gamma1' N :=
    Subgroup.Normal.conj_mem hN _ hx' _
  rw [CongruenceSubgroup.Gamma1_to_Gamma0_mem] at hc
  exact (CongruenceSubgroup.Gamma1_mem N _).2 hc

private lemma conj_mem_Gamma1_GL {N : ℕ} {γ x : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL N)
    (hx : x ∈ Gamma1GL N) : γ * x * γ⁻¹ ∈ Gamma1GL N := by
  obtain ⟨γ₀, hγ₀, hγeq⟩ := Subgroup.mem_map.mp hγ
  obtain ⟨x₀, hx₀, hxeq⟩ := Subgroup.mem_map.mp hx
  rw [← hγeq, ← hxeq]
  simpa only [map_mul, map_inv] using
    Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (conj_mem_Gamma1 hγ₀ hx₀)

private lemma one_mem_strictPeriods_Gamma1 (N : ℕ) : (1 : ℝ) ∈ (Gamma1GL N).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff, Subgroup.mem_map]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem]
    simp
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [GeneralLinearGroup.upperRightHom, Matrix.SpecialLinearGroup.mapGL,
        Matrix.SpecialLinearGroup.toGL, ModularGroup.coe_T]

private lemma isCusp_smul_mem_Gamma1 {N : ℕ} [NeZero N] {c : OnePoint ℝ} (hc : IsCusp c (Gamma1GL N))
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL N) : IsCusp (γ • c) (Gamma1GL N) :=
  (isCusp_iff_of_relIndex_ne_zero (le_Gamma1_Gamma0 N) (relIndex_mapGL_ne_zero N) (γ • c)).mpr
    (IsCusp.smul_of_mem (IsCusp.mono (le_Gamma1_Gamma0 N) hc) hγ)

private noncomputable def translateCusp {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm (Gamma1GL N) k) (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Gamma0GL N) :
    CuspForm (Gamma1GL N) k where
  toFun := (⇑f : ℍ → ℂ) ∣[k] γ
  slash_action_eq' δ hδ := by
    have hconj : γ * δ * γ⁻¹ ∈ Gamma1GL N := conj_mem_Gamma1_GL hγ hδ
    have hfix : (⇑f : ℍ → ℂ) ∣[k] (γ * δ * γ⁻¹) = ⇑f := f.slash_action_eq' _ hconj
    calc (⇑f ∣[k] γ) ∣[k] δ
        = ⇑f ∣[k] (γ * δ) := (SlashAction.slash_mul k γ δ ⇑f).symm
      _ = ⇑f ∣[k] ((γ * δ * γ⁻¹) * γ) := by
            rw [show (γ * δ * γ⁻¹) * γ = γ * δ by group]
      _ = (⇑f ∣[k] (γ * δ * γ⁻¹)) ∣[k] γ := SlashAction.slash_mul k (γ * δ * γ⁻¹) γ ⇑f
      _ = ⇑f ∣[k] γ := by rw [hfix]
  holo' := f.holo'.slash k γ
  zero_at_cusps' hc := by
    rw [← OnePoint.IsZeroAt.smul_iff]
    exact f.zero_at_cusps' (isCusp_smul_mem_Gamma1 hc hγ)

private lemma coe_translateCusp {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1GL N) k)
    (γ : GL (Fin 2) ℝ) (hγ : γ ∈ Gamma0GL N) :
    (⇑(translateCusp f γ hγ) : ℍ → ℂ) = (⇑f : ℍ → ℂ) ∣[k] γ := rfl

private lemma periodic_cuspForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1GL N) k) :
    Function.Periodic ((⇑f : ℍ → ℂ) ∘ UpperHalfPlane.ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods_Gamma1 N)

private lemma isBoundedAtImInfty_cuspForm {N : ℕ} [NeZero N] {k : ℤ}
    (f : CuspForm (Gamma1GL N) k) : IsBoundedAtImInfty (⇑f : ℍ → ℂ) := by
  have hc : IsCusp OnePoint.infty (Gamma1GL N) :=
    (Gamma1GL N).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods_Gamma1 N)
  exact (OnePoint.isZeroAt_infty_iff.mp (f.zero_at_cusps' hc)).isBoundedAtImInfty

private lemma analyticAt_cuspForm {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm (Gamma1GL N) k) :
    AnalyticAt ℂ (cuspFunction 1 (⇑f : ℍ → ℂ)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic_cuspForm f) f.holo'
    (isBoundedAtImInfty_cuspForm f)

private noncomputable def qCoeffLin (N : ℕ) [NeZero N] (k : ℤ) :
    CuspForm (Gamma1GL N) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun f := fun m => ModularFormClass.qCoeff (⇑f : ℍ → ℂ) m
  map_add' f g := by
    funext m
    simp only [ModularFormClass.qCoeff, Pi.add_apply, FunLike.coe_add]
    rw [UpperHalfPlane.qExpansion_add (analyticAt_cuspForm f) (analyticAt_cuspForm g), map_add]
  map_smul' c f := by
    funext m
    simp only [ModularFormClass.qCoeff, Pi.smul_apply, FunLike.coe_smul, smul_eq_mul]
    rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspForm f), map_smul]
    simp [smul_eq_mul]

private lemma quotientFunc_add {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    (f g : CuspForm 𝒢 k) (q : ℋ ⧸ (𝒢.subgroupOf ℋ)) :
    quotientFunc (f + g) q = quotientFunc f q + quotientFunc g q := by
  induction q using Quotient.inductionOn with
  | h r => simp [SlashAction.add_slash]

private lemma quotientFunc_smul {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ]
    [𝒢.HasDetOne] [ℋ.HasDetOne] {k : ℤ} (c : ℂ) (f : CuspForm 𝒢 k)
    (q : ℋ ⧸ (𝒢.subgroupOf ℋ)) :
    quotientFunc (c • f) q = c • quotientFunc f q := by
  induction q using Quotient.inductionOn with
  | h r =>
      simp only [quotientFunc_mk, FunLike.coe_smul]
      rw [ModularForm.smul_slash]
      congr 1
      have hdet : ((↑r : GL (Fin 2) ℝ)⁻¹).det = 1 := by
        rw [← Subgroup.coe_inv]
        exact Subgroup.HasDetOne.det_eq (inv_mem r.2)
      simp [σ, hdet]

private lemma trace_add {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    (f g : CuspForm 𝒢 k) :
    CuspForm.trace ℋ (f + g) = CuspForm.trace ℋ f + CuspForm.trace ℋ g := by
  ext τ
  simp only [CuspForm.coe_trace, FunLike.coe_add, Pi.add_apply, Finset.sum_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => congrFun (quotientFunc_add f g q) τ

private lemma trace_smul {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ]
    [𝒢.HasDetOne] [ℋ.HasDetOne] {k : ℤ} (c : ℂ) (f : CuspForm 𝒢 k) :
    CuspForm.trace ℋ (c • f) = c • CuspForm.trace ℋ f := by
  ext τ
  simp only [CuspForm.coe_trace, FunLike.coe_smul, Pi.smul_apply, Finset.sum_apply]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => congrFun (quotientFunc_smul c f q) τ

private lemma quotientFunc_zero {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ}
    (q : ℋ ⧸ (𝒢.subgroupOf ℋ)) : quotientFunc (0 : CuspForm 𝒢 k) q = 0 := by
  induction q using Quotient.inductionOn with
  | h r => simp

private lemma trace_zero {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ] {k : ℤ} :
    CuspForm.trace ℋ (0 : CuspForm 𝒢 k) = 0 := by
  ext τ
  rw [CuspForm.coe_trace]
  simp only [Finset.sum_apply]
  simp [quotientFunc_zero]

private lemma trace_sum_smul {𝒢 ℋ : Subgroup (GL (Fin 2) ℝ)} [𝒢.IsFiniteRelIndex ℋ]
    [𝒢.HasDetOne] [ℋ.HasDetOne] {k : ℤ} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (g : ι → CuspForm 𝒢 k) :
    CuspForm.trace ℋ (∑ i ∈ s, c i • g i) = ∑ i ∈ s, c i • CuspForm.trace ℋ (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [trace_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, trace_add, trace_smul, ih]

private def restrictCusp {N : ℕ} [NeZero N] {k : ℤ} (w : CuspForm (Gamma0GL N) k) :
    CuspForm (Gamma1GL N) k where
  toFun := ⇑w
  slash_action_eq' γ hγ := w.slash_action_eq' γ (le_Gamma1_Gamma0 N hγ)
  holo' := w.holo'
  zero_at_cusps' hc := w.zero_at_cusps' ((isCusp_iff_of_relIndex_ne_zero
    (le_Gamma1_Gamma0 N) (relIndex_mapGL_ne_zero N) _).mp hc)

private lemma coe_restrictCusp {N : ℕ} [NeZero N] {k : ℤ} (w : CuspForm (Gamma0GL N) k) :
    (⇑(restrictCusp w) : ℍ → ℂ) = ⇑w := rfl

private lemma trace_restrictCusp {N : ℕ} [NeZero N] {k : ℤ}
    [(Gamma1GL N).IsFiniteRelIndex (Gamma0GL N)] (w : CuspForm (Gamma0GL N) k) :
    CuspForm.trace (Gamma0GL N) (restrictCusp w) =
      (Fintype.card ((Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N)) : ℂ) • w := by
  ext τ
  rw [CuspForm.coe_trace]
  simp only [Finset.sum_apply]
  have hq : ∀ q : (Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N),
      quotientFunc (restrictCusp w) q = ⇑w := by
    intro q
    conv_lhs => rw [← Quotient.out_eq q]
    rw [SlashInvariantForm.quotientFunc_mk]
    exact w.slash_action_eq' ((q.out : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹
      (inv_mem (q.out : Gamma0GL N).2)
  trans (∑ q : (Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N), (⇑w : ℍ → ℂ) τ)
  · exact Finset.sum_congr rfl fun q _ => congrFun (hq q) τ
  · simp [Finset.sum_const, Finset.card_univ, smul_eq_mul]

private noncomputable def traceSummand {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k)) (i : Fin n)
    (q : (Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N)) : CuspForm (Gamma1GL N) k :=
  translateCusp (b i) ((q.out : Gamma0GL N) : GL (Fin 2) ℝ)⁻¹ (inv_mem (q.out : Gamma0GL N).2)

private lemma coe_traceSummand {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k)) (i : Fin n)
    (q : (Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N)) :
    quotientFunc (b i) q = (⇑(traceSummand b i q) : ℍ → ℂ) := by
  have h := SlashInvariantForm.quotientFunc_mk (f := b i) (q.out)
  rw [Quotient.out_eq q] at h
  rw [h]
  rfl

private lemma coe_finset_sum {𝒢 : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} {ι : Type*}
    (s : Finset ι) (g : ι → CuspForm 𝒢 k) :
    (⇑(∑ i ∈ s, g i) : ℍ → ℂ) = ∑ i ∈ s, ⇑(g i) := by
  let φ : CuspForm 𝒢 k →+ (ℍ → ℂ) :=
    { toFun := fun f => ⇑f, map_zero' := rfl, map_add' := fun f g => rfl }
  exact map_sum φ g s

private lemma coe_trace_eq_sum {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    [(Gamma1GL N).IsFiniteRelIndex (Gamma0GL N)]
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k)) (i : Fin n) :
    (⇑(CuspForm.trace (Gamma0GL N) (b i)) : ℍ → ℂ) = ∑ q, ⇑(traceSummand b i q) := by
  rw [CuspForm.coe_trace]
  exact Finset.sum_congr rfl fun q _ => (coe_traceSummand b i q)

private lemma qCoeff_translateCusp_mem_range {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k))
    (hb : ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ m : ℕ,
      ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ))
    (i : Fin n) {γ : GL (Fin 2) ℝ} (hγ : γ ∈ Gamma0GL N) (m : ℕ) :
    ModularFormClass.qCoeff ((⇑(translateCusp (b i) γ hγ) : ℍ → ℂ)) m ∈
      Set.range ((↑) : ℤ → ℂ) := by
  obtain ⟨γ₀, hγ₀, hγeq⟩ := Subgroup.mem_map.mp hγ
  rw [coe_translateCusp, ← hγeq]
  change ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ₀) m ∈ Set.range ((↑) : ℤ → ℂ)
  exact hb i γ₀ hγ₀ m

private lemma sum_mem_range_intCast {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, f i ∈ Set.range ((↑) : ℤ → ℂ)) :
    ∑ i ∈ s, f i ∈ Set.range ((↑) : ℤ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      obtain ⟨z₁, hz₁⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨z₂, hz₂⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      exact ⟨z₁ + z₂, by rw [Int.cast_add, hz₁, hz₂]⟩

private lemma qCoeff_trace_eq_sum {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    [(Gamma1GL N).IsFiniteRelIndex (Gamma0GL N)]
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k)) (i : Fin n) (m : ℕ) :
    ModularFormClass.qCoeff ((⇑(CuspForm.trace (Gamma0GL N) (b i)) : ℍ → ℂ)) m =
      ∑ q, ModularFormClass.qCoeff ((⇑(traceSummand b i q) : ℍ → ℂ)) m := by
  rw [coe_trace_eq_sum, ← coe_finset_sum]
  have := congrFun (map_sum (qCoeffLin N k) (fun q => traceSummand b i q) Finset.univ) m
  simpa only [qCoeffLin, LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply] using this

private lemma trace_basis_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
    [(Gamma1GL N).IsFiniteRelIndex (Gamma0GL N)]
    (b : Module.Basis (Fin n) ℂ (CuspForm (Gamma1GL N) k))
    (hb : ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ m : ℕ,
      ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ))
    (i : Fin n) : CuspForm.trace (Gamma0GL N) (b i) ∈ CuspForm.intLattice N k := by
  rw [CuspForm.intLattice]
  refine Submodule.subset_span ?_
  intro m
  rw [qCoeff_trace_eq_sum b i m]
  obtain ⟨z, hz⟩ := sum_mem_range_intCast
    (s := (Finset.univ : Finset ((Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N))))
    (f := fun q => ModularFormClass.qCoeff ((⇑(traceSummand b i q) : ℍ → ℂ)) m)
    (fun q _ => qCoeff_translateCusp_mem_range b hb i (inv_mem (q.out : Gamma0GL N).2) m)
  exact ⟨z, hz.symm⟩

theorem hasIntegralStructure_of_basis_gamma1 {N : ℕ} [NeZero N] {k : ℤ}
    (h : ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm (CongruenceSubgroup.Gamma1 N) k)),
      ∀ (i : Fin n) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 N → ∀ m : ℕ,
        ModularFormClass.qCoeff ((⇑(b i) : ℍ → ℂ) ∣[k] γ) m ∈ Set.range ((↑) : ℤ → ℂ)) :
    CuspForm.HasIntegralStructure N k := by
  obtain ⟨n, b, hb⟩ := h
  rw [CuspForm.HasIntegralStructure, Submodule.eq_top_iff']
  intro w
  have hrepr : restrictCusp w = ∑ i, b.repr (restrictCusp w) i • b i := (b.sum_repr _).symm
  have htrace : CuspForm.trace (Gamma0GL N) (restrictCusp w) =
      ∑ i, b.repr (restrictCusp w) i • CuspForm.trace (Gamma0GL N) (b i) := by
    conv_lhs => rw [hrepr]
    rw [trace_sum_smul Finset.univ]
  have hmem : CuspForm.trace (Gamma0GL N) (restrictCusp w) ∈
      Submodule.span ℂ (CuspForm.intLattice N k : Set (CuspForm (Gamma0GL N) k)) := by
    rw [htrace]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (Submodule.subset_span (trace_basis_mem_intLattice b hb i))
  rw [trace_restrictCusp w] at hmem
  set r : ℂ := (Fintype.card ((Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N)) : ℂ)
  have hr : r ≠ 0 := by
    rw [show r = (Fintype.card ((Gamma0GL N) ⧸ (Gamma1GL N).subgroupOf (Gamma0GL N)) : ℂ) from rfl,
      Nat.cast_ne_zero]
    exact Fintype.card_ne_zero
  have hw : w = r⁻¹ • (r • w) := by rw [smul_smul, inv_mul_cancel₀ hr, one_smul]
  rw [hw]
  exact Submodule.smul_mem _ _ hmem

theorem hasIntegralStructure_of_two_le (N' : ℕ) [NeZero N'] (k : ℤ) (hk : 2 ≤ k) :
    HasIntegralStructure N' k := by
  have _ := hk
  exact hasIntegralStructure_of_basis_gamma1
    (CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast N' k)

theorem hasIntegralStructure_two (N : ℕ) [NeZero N] : CuspForm.HasIntegralStructure N 2 :=
  hasIntegralStructure_of_two_le N 2 le_rfl

end CuspForm
