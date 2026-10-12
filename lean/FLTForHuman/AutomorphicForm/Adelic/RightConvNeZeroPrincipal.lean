/-
  Non-vanishing right convolution with a `principalLevel`-invariant test function.

  The principal-level sibling of `RightConvNeZero`: the invariance is under
  `principalLevel N ⊓ finiteAdelicGL2Subgroup K` (`principalLevel` is `levelOne N`
  intersected with its Weyl conjugate). Only the level-specific part of the prelude is
  written here — the finite principal-level lattice `finitePrincipalLevel` and the
  `Kf`/`ff`/`testFn` family built on it; the archimedean machinery (`mixedHomeo`, `J`,
  `Ψ`, `fa`, `bumpAt`, `exists_radius_of_continuous`, `rightConv_ne_zero_of_bound`, …)
  is imported from the `AutomorphicForm.TestFnNearIdentity` home.

  Transcribed from the `TestFnNearIdentity` block (lines 303–520) and `solution`
  (lines 527–566) of
  `P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant.lean`
  (pinned `aa2d8b3`), at its `Theorems/` wrapper name.
-/
import FLTForHuman.AutomorphicForm.Adelic.TestFnNearIdentity
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.NumberTheory.AdelicLevel.PrincipalLevel

set_option autoImplicit false

-- The pin's `letI`/`haveI` walls feed instance search.
set_option linter.style.haveILetI false

open NumberField NumberField.AdelicLevel
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion IsDedekindDomain AutomorphicForm
open NumberField.InfiniteAdeleRing Metric Topology MeasureTheory

open scoped Classical

noncomputable section

namespace AutomorphicForm.TestFnPrincipalLevel

open AutomorphicForm.TestFnNearIdentity

variable (F : Type) [Field F] [NumberField F]

def weylFin : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := AdelicLevel.glFin (𝓞 F) F (AdelicLevel.weyl (𝓞 F) F)

def finitePrincipalLevel (N : Ideal (𝓞 F)) : Subgroup (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  AdelicLevel.finiteLevelOne (𝓞 F) F N ⊓
    (AdelicLevel.finiteLevelOne (𝓞 F) F N).map (MulAut.conj (weylFin F)).toMonoidHom

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (w g : G) :
    g ∈ H.map (MulAut.conj w).toMonoidHom ↔ w⁻¹ * g * w ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem mem_principalLevel_iff_glFin {N : Ideal (𝓞 F)} (g : AdelicGL2 (𝓞 F) F) :
    g ∈ AdelicLevel.principalLevel (𝓞 F) F N ↔ AdelicLevel.glFin (𝓞 F) F g ∈ finitePrincipalLevel F N := by
  unfold finitePrincipalLevel weylFin
  rw [AdelicLevel.mem_principalLevel_iff, Subgroup.mem_inf, mem_map_conj_iff, mem_map_conj_iff,
    AdelicLevel.mem_levelOne_iff, AdelicLevel.mem_levelOne_iff, map_mul, map_mul, map_inv]

theorem isOpen_finitePrincipalLevel {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) :
    IsOpen (finitePrincipalLevel F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  have h1 := AdelicLevel.isOpen_finiteLevelOne (𝓞 F) F (N := N) hN
  have h2 : IsOpen ((fun g => (weylFin F)⁻¹ * g * weylFin F) ⁻¹'
      (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  unfold finitePrincipalLevel
  rw [Subgroup.mem_inf, mem_map_conj_iff]

theorem isClosed_finitePrincipalLevel (N : Ideal (𝓞 F)) :
    IsClosed (finitePrincipalLevel F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) := by
  have h1 := AdelicLevel.isClosed_finiteLevelOne (𝓞 F) F N
  have h2 : IsClosed ((fun g => (weylFin F)⁻¹ * g * weylFin F) ⁻¹'
      (AdelicLevel.finiteLevelOne (𝓞 F) F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))) :=
    h1.preimage ((continuous_const.mul continuous_id).mul continuous_const)
  convert h1.inter h2 using 1
  ext g
  simp only [Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  unfold finitePrincipalLevel
  rw [Subgroup.mem_inf, mem_map_conj_iff]

theorem isCompact_finitePrincipalLevel (N : Ideal (𝓞 F)) :
    IsCompact (finitePrincipalLevel F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F))) :=
  (AdelicLevel.isCompact_finiteLevelOne (𝓞 F) F N).of_isClosed_subset (isClosed_finitePrincipalLevel F N)
    (inf_le_left : finitePrincipalLevel F N ≤ AdelicLevel.finiteLevelOne (𝓞 F) F N)

def Kf (N : Ideal (𝓞 F)) : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :=
  (finitePrincipalLevel F N : Set (GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)))

def ff (N : Ideal (𝓞 F)) : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Kf F N).indicator fun _ => 1

theorem isOpen_Kf {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsOpen (Kf F N) :=
  isOpen_finitePrincipalLevel F hN

theorem isClosed_Kf (N : Ideal (𝓞 F)) : IsClosed (Kf F N) :=
  isClosed_finitePrincipalLevel F N

theorem isCompact_Kf (N : Ideal (𝓞 F)) : IsCompact (Kf F N) :=
  isCompact_finitePrincipalLevel F N

theorem isFinTestFactor_ff {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFinTestFactor F (ff F N) := by
  refine ⟨?_, HasCompactSupport.intro' (isCompact_Kf F N) (isClosed_Kf F N)
    fun x hx => Set.indicator_of_notMem hx _⟩
  intro s
  have hpre : ff F N ⁻¹' s
      = (if (1 : ℂ) ∈ s then Kf F N else ∅) ∪ (if (0 : ℂ) ∈ s then (Kf F N)ᶜ else ∅) := by
    ext x
    by_cases hx : x ∈ Kf F N <;> by_cases h1 : (1 : ℂ) ∈ s <;> by_cases h0 : (0 : ℂ) ∈ s <;>
      simp [ff, Set.indicator, hx, h1, h0]
  rw [hpre]
  refine IsOpen.union ?_ ?_
  · split_ifs
    · exact isOpen_Kf F hN
    · exact isOpen_empty
  · split_ifs
    · exact (isClosed_Kf F N).isOpen_compl
    · exact isOpen_empty

theorem ff_mul_of_mem (N : Ideal (𝓞 F)) {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : k ∈ finitePrincipalLevel F N) (x : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    ff F N (k * x) = ff F N x := by
  by_cases hx : x ∈ Kf F N
  · have hx' : x ∈ finitePrincipalLevel F N := hx
    have hkx : k * x ∈ Kf F N := mul_mem hk hx'
    simp only [ff, Set.indicator_of_mem hx, Set.indicator_of_mem hkx]
  · have hkx : k * x ∉ Kf F N := fun h =>
      hx ((Subgroup.mul_mem_cancel_left (finitePrincipalLevel F N) hk).1
        (show k * x ∈ finitePrincipalLevel F N from h))
    simp only [ff, Set.indicator_of_notMem hx, Set.indicator_of_notMem hkx]

def testFn (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℂ := fun g =>
  fa F ρ hρ (AdelicLevel.glArch (𝓞 F) F g) * ff F N (AdelicLevel.glFin (𝓞 F) F g)

def testFnR (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : AdelicGL2 (𝓞 F) F → ℝ := fun g =>
  (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F g)) *
    (Kf F N).indicator (fun _ => (1 : ℝ)) (AdelicLevel.glFin (𝓞 F) F g)

theorem isFactorizableTestFn_testFn (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2)
    {N : Ideal (𝓞 F)} (hN : N ≠ ⊥) : IsFactorizableTestFn F (testFn F ρ hρ N) :=
  ⟨fa F ρ hρ, ff F N, isArchTestFactor_fa F ρ hρ hρε, isFinTestFactor_ff F hN, fun _ => rfl⟩

theorem testFn_mul_of_mem (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (x : AdelicGL2 (𝓞 F) F) :
    testFn F ρ hρ N (k * x) = testFn F ρ hρ N x := by
  obtain ⟨hk₁, hk₂⟩ := Subgroup.mem_inf.1 hk
  have h1 : AdelicLevel.glArch (𝓞 F) F k = 1 := (mem_finiteAdelicGL2Subgroup_iff F k).1 hk₂
  have h2 : AdelicLevel.glFin (𝓞 F) F k ∈ finitePrincipalLevel F N :=
    (mem_principalLevel_iff_glFin F k).1 hk₁
  simp only [testFn, map_mul, h1, one_mul, ff_mul_of_mem F N h2]

theorem testFn_decomp (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N) :
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x ∈
      AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
  · rw [mem_principalLevel_iff_glFin, map_mul, map_inv, glFin_adelicArchGLIncl, inv_one, one_mul]
    exact hx
  · rw [mem_finiteAdelicGL2Subgroup_iff, map_mul, map_inv, glArch_adelicArchGLIncl, inv_mul_cancel]

theorem glFin_mem_of_testFn_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F))
    (x : AdelicGL2 (𝓞 F) F) (hx : testFn F ρ hρ N x ≠ 0) : AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  by_contra h
  exact hx (by simp only [testFn, ff, Set.indicator_of_notMem h, mul_zero])

theorem testFn_support (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFn F ρ hρ N x ≠ 0) :
    ∃ a k : AdelicGL2 (𝓞 F) F, AdelicLevel.glFin (𝓞 F) F a = 1 ∧
      k ∈ AdelicLevel.principalLevel (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F ∧ x = a * k :=
  ⟨adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x),
    (adelicArchGLIncl F (AdelicLevel.glArch (𝓞 F) F x))⁻¹ * x, glFin_adelicArchGLIncl F _,
    testFn_decomp F N x (glFin_mem_of_testFn_ne_zero F ρ hρ N x hx), (mul_inv_cancel_left _ _).symm⟩

theorem testFn_eq_ofReal (ρ : ℝ) (hρ : 0 < ρ) (hρε : ρ ≤ ε F / 2) (N : Ideal (𝓞 F))
    (g : AdelicGL2 (𝓞 F) F) : testFn F ρ hρ N g = ((testFnR F ρ hρ N g : ℝ) : ℂ) := by
  simp only [testFn, testFnR, fa_eq F ρ hρ hρε, ff, Complex.ofReal_mul]
  congr 1
  by_cases h : AdelicLevel.glFin (𝓞 F) F g ∈ Kf F N
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, Complex.ofReal_one]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, Complex.ofReal_zero]

theorem testFnR_nonneg (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (g : AdelicGL2 (𝓞 F) F) :
    0 ≤ testFnR F ρ hρ N g :=
  mul_nonneg (bumpAt F ρ hρ).nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem testFnR_one (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) : testFnR F ρ hρ N 1 = 1 := by
  have h1 : (bumpAt F ρ hρ).toFun (archEntries F 1) = 1 :=
    (bumpAt F ρ hρ).one_of_mem_closedBall (mem_closedBall_self (bumpAt F ρ hρ).rIn_pos.le)
  have h2 : (Kf F N).indicator (fun _ => (1 : ℝ)) 1 = 1 :=
    Set.indicator_of_mem
      (show (1 : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) ∈ Kf F N from
        (finitePrincipalLevel F N).one_mem) _
  simp only [testFnR, map_one, h1, h2, mul_one]

theorem of_testFnR_ne_zero (ρ : ℝ) (hρ : 0 < ρ) (N : Ideal (𝓞 F)) (x : AdelicGL2 (𝓞 F) F)
    (hx : testFnR F ρ hρ N x ≠ 0) :
    dist (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) (cE F) < ρ ∧
      AdelicLevel.glFin (𝓞 F) F x ∈ Kf F N := by
  constructor
  · by_contra h
    rw [not_lt] at h
    have h0 : (bumpAt F ρ hρ).toFun (archEntries F (AdelicLevel.glArch (𝓞 F) F x)) = 0 :=
      (bumpAt F ρ hρ).zero_of_le_dist h
    exact hx (by simp only [testFnR, h0, zero_mul])
  · by_contra h
    exact hx (by simp only [testFnR, Set.indicator_of_notMem h, mul_zero])

theorem rightConv_ne_zero_of_bound (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφ : Continuous φ)
    (g₀ : AdelicGL2 (𝓞 F) F) (hg₀ : φ g₀ ≠ 0) (f : AdelicGL2 (𝓞 F) F → ℂ) (hfc : Continuous f)
    (hfs : HasCompactSupport f) (fR : AdelicGL2 (𝓞 F) F → ℝ) (hfR : ∀ x, f x = ((fR x : ℝ) : ℂ))
    (hR0 : ∀ x, 0 ≤ fR x) (hR1 : fR 1 ≠ 0)
    (hbound : ∀ x, fR x ≠ 0 → ‖φ (g₀ * x) - φ g₀‖ ≤ ‖φ g₀‖ / 2) :
    rightConv F φ f g₀ ≠ 0 := by
  letI : MeasurableSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.glBorel (Fin 2) (𝓞 F) F
  haveI : BorelSpace (AdelicGL2 (𝓞 F) F) := AdelicHaar.borelSpace_glBorel (Fin 2) (𝓞 F) F
  haveI := AdelicHaar.isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  have hRre : fR = fun x => (f x).re := by
    funext x
    rw [hfR x, Complex.ofReal_re]
  have hRc : Continuous fR := by
    rw [hRre]
    exact Complex.continuous_re.comp hfc
  have hRs : HasCompactSupport fR := by
    rw [hRre]
    exact hfs.comp_left Complex.zero_re
  have hRi : Integrable fR (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    hRc.integrable_of_hasCompactSupport hRs
  have hIpos : 0 < ∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (integral_pos_iff_support_of_nonneg (fun x => hR0 x) hRi).2
      (hRc.isOpen_support.measure_pos _ ⟨1, hR1⟩)
  have hmul : Continuous fun x : AdelicGL2 (𝓞 F) F => g₀ * x := continuous_const.mul continuous_id
  have hi₁ : Integrable (fun x => φ (g₀ * x) * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    ((hφ.comp hmul).mul hfc).integrable_of_hasCompactSupport hfs.mul_left
  have hi₂ : Integrable (fun x => φ g₀ * f x) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) :=
    (hfc.integrable_of_hasCompactSupport hfs).const_mul _
  have h3 : ∫ x, f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ) := by
    simp only [hfR]
    exact integral_complex_ofReal
  intro h0
  have h2 : ∫ x, φ (g₀ * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = 0 := h0
  have hint : ∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
      = -(φ g₀ * ((∫ x, fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) : ℝ) : ℂ)) := by
    have h1 : (fun x => (φ (g₀ * x) - φ g₀) * f x) = fun x => φ (g₀ * x) * f x - φ g₀ * f x := by
      funext x
      ring
    rw [h1, integral_sub hi₁ hi₂, h2, integral_const_mul, h3, zero_sub]
  have hle : ‖∫ x, (φ (g₀ * x) - φ g₀) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)‖
      ≤ ∫ x, ‖φ g₀‖ / 2 * fR x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    refine norm_integral_le_of_norm_le (hRi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, hfR x, Complex.norm_real, Real.norm_of_nonneg (hR0 x)]
    by_cases hx : fR x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hbound x hx) (hR0 x)
  rw [hint, norm_neg, norm_mul, Complex.norm_real, Real.norm_of_nonneg hIpos.le,
    integral_const_mul] at hle
  have hc : 0 < ‖φ g₀‖ := norm_pos_iff.2 hg₀
  nlinarith [mul_pos hc hIpos]

end AutomorphicForm.TestFnPrincipalLevel

open AutomorphicForm.TestFnPrincipalLevel in

theorem AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by
  obtain ⟨g₀, hg₀⟩ := hne
  obtain ⟨ρ, hρ, hρε, hV⟩ := TestFnNearIdentity.exists_radius_of_continuous K φ hcont g₀ hg₀
  have htier := isFactorizableTestFn_testFn K ρ hρ hρε hN
  refine ⟨testFn K ρ hρ N, htier, fun _ hk x => testFn_mul_of_mem K ρ hρ N hk x,
    fun x hx => testFn_support K ρ hρ N x hx, g₀, ?_⟩
  obtain ⟨hfc, hfs⟩ :=
    AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ htier
  refine TestFnNearIdentity.rightConv_ne_zero_of_bound K φ hcont g₀ hg₀ _ hfc hfs (testFnR K ρ hρ N)
    (testFn_eq_ofReal K ρ hρ hρε N) (testFnR_nonneg K ρ hρ N)
    (by rw [testFnR_one]; exact one_ne_zero) fun x hx => ?_
  obtain ⟨hdist, hfin⟩ := of_testFnR_ne_zero K ρ hρ N x hx
  have hx' : g₀ * x = (g₀ * adelicArchGLIncl K (glArch (𝓞 K) K x)) *
      ((adelicArchGLIncl K (glArch (𝓞 K) K x))⁻¹ * x) := by
    rw [mul_assoc, mul_inv_cancel_left]
  rw [hx', hlev _ _ (testFn_decomp K N x hfin)]
  exact hV _ hdist
