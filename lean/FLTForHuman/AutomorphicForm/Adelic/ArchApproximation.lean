/-
  The archimedean cut projector commutes with right convolution, through the archimedean
  approximation identity.

  Two headlines and the two membership lemmas they consume, one subject: the **archimedean cut**
  `archCutSubmodule F tys` (the vectors whose archimedean type lies in a finite family `tys`) and the
  **projector** `Q` onto it.

  * `isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule`:
    for a continuous function `e₁ ⊗ e₂` on the row-isometry product against a Haar measure `μ`, the
    integral
    `y ↦ ∫ p, e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)`
    is again an archimedean test factor, and is **bi-finite for `tys`** as soon as `e₂` lies in the
    type-submodules of the dual representations and `κ ↦ e₁ κ⁻¹` in those of the representations —
    the approximation that turns the type decomposition into an integral over the row-isometry group;
  * `exists_rightConv_eq_of_archCutProjector`: if `Q` fixes the cut, maps into the cut intersected
    with the orbit span, and commutes with right translation by row isometries, then for `y` in the
    cut and `f` factorizable, `Q (rightConv y f)` is again `rightConv y f'` with `f'` factorizable and
    bi-finite for `tys`.

  The two membership lemmas —
  `apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective` (a right-equivariant linear map
  preserves a supremum of type submodules) and `rightConv_mem_archCutSubmodule_of_isArchBiFinite`
  (convolving by an archimedean-bi-finite factorizable test function keeps a vector in the cut) —
  are the two halves the first headline's proof consumes.

  Transcribed from the pin's four `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  80 + 190 + 1,175 + 1,131 lines). It is a **composition** set: 1,148 of the 2,490 declaration lines
  are already in the port (`port_plan`), and it sits on top of the archimedean cut projector of
  `Adelic/ArchCutProjector.lean` rather than inside it, because that module is 825 lines with four
  in-tree importers and this is its consumer.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective.lean
  spec-pin: Theorems/Thm_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_rightConv_mem_archCutSubmodule_of_isArchBiFinite.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_rightConv_eq_of_archCutProjector.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_rightConv_eq_of_archCutProjector.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_linearMap_archCutProjector.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_linearMap_archCutProjector.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchCutProjector
import FLTForHuman.AutomorphicForm.Adelic.TestFnInvariance
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothComplexLeft
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.TestFnTop
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.RepTheory.ConvolutionLimit
import FLTForHuman.AutomorphicForm.Adelic.ArchDualCut
import FLTForHuman.AutomorphicForm.Adelic.ArchCutSpan
import FLTForHuman.AutomorphicForm.Adelic.RightConvRegularity

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped ENNReal Pointwise BigOperators Classical

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

namespace TypePush

variable {H K G : Type*} [Group H] [Group K] [Group G]

/-- The right regular representation of `H` on functions on `K`, along `j : H →* K`. -/
def rightRegular (j : H →* K) : Representation ℂ H (K → ℂ) where
  toFun k :=
    { toFun := fun u κ => u (κ * j k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j 1) = u κ
    rw [map_one, mul_one]
  map_mul' k k' := by
    apply LinearMap.ext
    intro u
    funext κ
    show u (κ * j (k * k')) = u (κ * j k * j k')
    rw [map_mul, mul_assoc]

theorem rightRegular_apply (j : H →* K) (k : H) (u : K → ℂ) :
    rightRegular j k u = fun κ => u (κ * j k) :=
  rfl

theorem map_typeSubmodule_le_of_isRightEquivariant (j : H →* K) (ι' : H →* G)
    (Text : (K → ℂ) →ₗ[ℂ] (G → ℂ)) (hText : IsRightEquivariant ι' (rightRegular j) Text)
    {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ H W) :
    (typeSubmodule j ρ).map Text ≤ typeSubmodule ι' ρ := by
  show (Submodule.span ℂ _).map Text ≤ _
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨f, ⟨T, hT, v, rfl⟩, rfl⟩
  have hTT : IsRightEquivariant ι' ρ (Text ∘ₗ T) := by
    intro k v' x
    show Text (T (ρ k v')) x = Text (T v') (x * ι' k)
    have h1 : T (ρ k v') = rightRegular j k (T v') := funext fun κ => hT k v' κ
    rw [h1]
    exact hText k (T v') x
  exact mem_typeSubmodule_of_isRightEquivariant hTT v

end TypePush

/-- A right-equivariant linear map on a type-submodule carrier preserves the supremum of type
submodules. -/
theorem apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective
    {H K G : Type*} [Group H] [Group K] [Group G]
    (j : H →* K) (ι' : H →* G) (hι' : Function.Injective ι')
    (C : Submodule ℂ (K → ℂ)) (hC : ∀ (k : H) (u : K → ℂ), u ∈ C → (fun κ => u (κ * j k)) ∈ C)
    (A : ↥C →ₗ[ℂ] (G → ℂ))
    (hA : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨fun κ => (u : K → ℂ) (κ * j k), hC k u u.2⟩ x = A u (x * ι' k))
    {I : Type*} {W : I → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ρ : ∀ i, Representation ℂ H (W i)) (u : K → ℂ) (hu : u ∈ C)
    (hut : u ∈ ⨆ i, typeSubmodule j (ρ i)) :
    A ⟨u, hu⟩ ∈ ⨆ i, typeSubmodule ι' (ρ i) := by
  have hC' : ∀ (k : H) (u : K → ℂ), u ∈ C → TypePush.rightRegular j k u ∈ C := fun k u h => hC k u h
  have hA' : ∀ (k : H) (u : ↥C) (x : G),
      A ⟨TypePush.rightRegular j k u, hC' k u u.2⟩ x = A u (x * ι' k) := fun k u x => hA k u x
  obtain ⟨Text, hText, hTextC⟩ :=
    exists_isRightEquivariant_comp_subtype_eq_of_injective ι' hι' (TypePush.rightRegular j) C hC' A hA'
  have hAu : A ⟨u, hu⟩ = Text u := by
    rw [← hTextC]
    rfl
  rw [hAu]
  have hle : (⨆ i, typeSubmodule j (ρ i)).map Text ≤ ⨆ i, typeSubmodule ι' (ρ i) := by
    rw [Submodule.map_iSup]
    exact iSup_mono fun i => TypePush.map_typeSubmodule_le_of_isRightEquivariant j ι' Text hText (ρ i)
  exact hle ⟨u, hut, rfl⟩

/-- Right convolution by an archimedean-bi-finite factorizable test function keeps a vector in the
archimedean cut. -/
theorem rightConv_mem_archCutSubmodule_of_isArchBiFinite
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (g : AdelicGL2 (𝓞 F) F → ℂ) (hg : Continuous g)
    (α : AdelicGL2 (𝓞 F) F → ℂ) (hα : IsFactorizableTestFn F α) (hαt : IsArchBiFinite F tys α) :
    rightConv F g α ∈ archCutSubmodule F tys := by
  classical
  set μ : Measure (AdelicGL2 (𝓞 F) F) := adelicGLHaar (Fin 2) (𝓞 F) F with hμ
  have hHaar : μ.IsHaarMeasure := isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  obtain ⟨hαc, hαsupp⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F α hα

  set αv : AdelicGL2 (𝓞 F) F → ℂ := fun x => α x⁻¹ with hαv
  have hαvc : Continuous αv := hαc.comp continuous_inv
  have hαvsupp : HasCompactSupport αv := hαsupp.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))

  set Λ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun h x => ∫ y, g (x * y) * h y⁻¹ ∂μ with hΛ
  have hΛα : rightConv F g α = Λ αv := by
    funext x; simp only [hΛ, hαv, rightConv_apply, inv_inv, hμ]
  have hint : ∀ h : AdelicGL2 (𝓞 F) F → ℂ, Continuous h → HasCompactSupport h →
      ∀ x, Integrable (fun y => g (x * y) * h y⁻¹) μ := fun h hh hhs x =>
    ((hg.comp (continuous_const.mul continuous_id)).mul (hh.comp continuous_inv)).integrable_of_hasCompactSupport
      (hhs.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))).mul_left
  have hΛadd : ∀ h₁ h₂ : AdelicGL2 (𝓞 F) F → ℂ, Continuous h₁ → HasCompactSupport h₁ → Continuous h₂ → HasCompactSupport h₂ →
      Λ (h₁ + h₂) = Λ h₁ + Λ h₂ := by
    intro h₁ h₂ c₁ s₁ c₂ s₂
    funext x
    simp only [hΛ, Pi.add_apply]
    rw [← integral_add (hint h₁ c₁ s₁ x) (hint h₂ c₂ s₂ x)]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛsmul : ∀ (c : ℂ) (h : AdelicGL2 (𝓞 F) F → ℂ), Λ (c • h) = c • Λ h := by
    intro c h
    funext x
    simp only [hΛ, Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    ring
  have hΛeq : ∀ (h : AdelicGL2 (𝓞 F) F → ℂ) (k x : AdelicGL2 (𝓞 F) F), Λ (fun y => h (y * k)) x = Λ h (x * k) := by
    intro h k x
    simp only [hΛ]
    have h1 := integral_mul_left_eq_self (μ := μ) (fun y => g (x * k * y) * h y⁻¹) k⁻¹
    rw [← h1]
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    show g (x * y) * h (y⁻¹ * k) = g (x * k * (k⁻¹ * y)) * h (k⁻¹ * y)⁻¹
    rw [mul_inv_rev, inv_inv, mul_assoc x k, mul_inv_cancel_left]

  rw [mem_archCutSubmodule_iff]
  intro w
  set ι : ↥(rowIsometrySubgroup₀ w.Completion) →* AdelicGL2 (𝓞 F) F := rowIsometryInclAt₀ F w with hιdef
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    have h1 := congrArg (fun x => archComponent F w (glArch (𝓞 F) F x)) h
    simpa only [hιdef, rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply,
      glArch_adelicArchGLIncl, archComponent_archGLIncl_self] using h1
  have hcut := (mem_archCutSubmodule_iff F tys αv).mp hαt.1 w

  have hcut' : αv ∈ Submodule.span ℂ (⋃ i : Fin (tys.card w),
      {φ : AdelicGL2 (𝓞 F) F → ℂ | ∃ T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
        IsRightEquivariant ι (tys.rep w i).ρ T ∧ φ ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hcut
  obtain ⟨n, c, gen, hsum⟩ := Submodule.mem_span_set'.mp hcut'
  have hgen : ∀ j : Fin n, ∃ (i : Fin (tys.card w)) (T : (Fin (tys.rep w i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
      (v : Fin (tys.rep w i).n → ℂ), IsRightEquivariant ι (tys.rep w i).ρ T ∧ T v = (gen j : AdelicGL2 (𝓞 F) F → ℂ) := by
    intro j
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (gen j).2
    obtain ⟨T, hT, v, hv⟩ := hi
    exact ⟨i, T, v, hT, hv⟩
  choose idx Tj vj hTj hTv using hgen

  let W : Type := (j : Fin n) → (Fin (tys.rep w (idx j)).n → ℂ)
  let ρW : Representation ℂ ↥(rowIsometrySubgroup₀ w.Completion) W :=
    { toFun := fun k => LinearMap.pi fun j => ((tys.rep w (idx j)).ρ k).comp (LinearMap.proj j)
      map_one' := by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ 1 (a j) = a j
        rw [map_one]; rfl
      map_mul' := fun k k' => by
        apply LinearMap.ext; intro a; funext j
        show (tys.rep w (idx j)).ρ (k * k') (a j) = (tys.rep w (idx j)).ρ k ((tys.rep w (idx j)).ρ k' (a j))
        rw [map_mul]; rfl }
  have ρW_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W) (j : Fin n), ρW k a j = (tys.rep w (idx j)).ρ k (a j) := fun _ _ _ => rfl
  let TW : W →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := ∑ j, (Tj j).comp (LinearMap.proj j)
  have TW_apply : ∀ a : W, TW a = ∑ j, Tj j (a j) := fun a => by
    simp only [TW, LinearMap.coe_sum, Finset.sum_apply, LinearMap.coe_comp, Function.comp_apply]
    rfl
  have hTW : IsRightEquivariant ι ρW TW := by
    intro k a x
    rw [TW_apply, TW_apply, Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ρW_apply]
    exact hTj j k (a j) x

  let Rk : ↥(rowIsometrySubgroup₀ w.Completion) → (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := fun k => LinearMap.funLeft ℂ ℂ fun y : AdelicGL2 (𝓞 F) F => y * ι k
  have Rk_apply : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (h : AdelicGL2 (𝓞 F) F → ℂ) (y : AdelicGL2 (𝓞 F) F), Rk k h y = h (y * ι k) := fun _ _ _ => rfl
  let V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun k : ↥(rowIsometrySubgroup₀ w.Completion) => Rk k αv)
  have h0supp : HasCompactSupport (0 : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [HasCompactSupport, tsupport, Function.support_zero, closure_empty]; exact isCompact_empty
  have hVcc : ∀ h ∈ V, Continuous h ∧ HasCompactSupport h := by
    intro h hh
    induction hh using Submodule.span_induction with
    | mem h hh =>
      obtain ⟨k, rfl⟩ := hh
      exact ⟨hαvc.comp (continuous_id.mul continuous_const), hαvsupp.comp_homeomorph (Homeomorph.mulRight (ι k))⟩
    | zero => exact ⟨continuous_const, h0supp⟩
    | add h₁ h₂ _ _ ih₁ ih₂ => exact ⟨ih₁.1.add ih₂.1, ih₁.2.add ih₂.2⟩
    | smul a h _ ih => exact ⟨ih.1.const_smul a, ih.2.smul_left (f := fun _ => a)⟩
  have hVstab : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)), ∀ h ∈ V, Rk k h ∈ V := by
    intro k h hh
    have hle : V.map (Rk k) ≤ V := by
      refine (Submodule.map_span_le _ _ _).mpr ?_
      rintro _ ⟨k', rfl⟩
      refine Submodule.subset_span ⟨k * k', ?_⟩
      funext y
      show αv (y * ι (k * k')) = αv (y * ι k * ι k')
      rw [map_mul, mul_assoc]
    exact hle ⟨h, hh, rfl⟩

  let A : Submodule ℂ W := V.comap TW
  have hTWρ : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), TW (ρW k a) = Rk k (TW a) := fun k a => funext fun x => hTW k a x
  have hA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : W), a ∈ A → ρW k a ∈ A := fun k a ha => by
    show TW (ρW k a) ∈ V
    rw [hTWρ]
    exact hVstab k _ ha
  let TA : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun a => Λ (TW a)
      map_add' := fun a b => by
        rw [Submodule.coe_add, map_add]
        exact hΛadd _ _ (hVcc _ a.2).1 (hVcc _ a.2).2 (hVcc _ b.2).1 (hVcc _ b.2).2
      map_smul' := fun a x => by
        rw [Submodule.coe_smul, map_smul, RingHom.id_apply]
        exact hΛsmul a _ }
  have hTA : ∀ (k : ↥(rowIsometrySubgroup₀ w.Completion)) (a : ↥A) (x : AdelicGL2 (𝓞 F) F), TA ⟨ρW k a, hA k a a.2⟩ x = TA a (x * ι k) := by
    intro k a x
    show Λ (TW (ρW k a)) x = Λ (TW a) (x * ι k)
    rw [hTWρ]
    exact hΛeq (TW a) (ι k) x
  obtain ⟨Text, hText, hTextA⟩ :=
    exists_isRightEquivariant_comp_subtype_eq_of_injective ι hι ρW A hA TA hTA

  let a₀ : W := fun j => c j • vj j
  have hTWa₀ : TW a₀ = αv := by
    rw [TW_apply, ← hsum]
    refine Finset.sum_congr rfl fun j _ => ?_
    show Tj j (c j • vj j) = c j • (gen j : AdelicGL2 (𝓞 F) F → ℂ)
    rw [map_smul, hTv]
  have ha₀ : a₀ ∈ A := by
    show TW a₀ ∈ V
    rw [hTWa₀]
    refine Submodule.subset_span ⟨1, ?_⟩
    funext y
    show αv (y * ι 1) = αv y
    rw [map_one, mul_one]
  have hgoal : rightConv F g α = Text a₀ := by
    rw [hΛα, ← hTWa₀]
    have h := congrArg (fun f : ↥A →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) => f ⟨a₀, ha₀⟩) hTextA
    exact h.symm
  rw [hgoal, show a₀ = ∑ j, Pi.single j (a₀ j) from (Finset.univ_sum_single a₀).symm, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_

  have hTj' : IsRightEquivariant ι (tys.rep w (idx j)).ρ
      (Text.comp (LinearMap.single ℂ (fun j => Fin (tys.rep w (idx j)).n → ℂ) j)) := by
    intro k u x
    show Text (Pi.single j ((tys.rep w (idx j)).ρ k u)) x = Text (Pi.single j u) (x * ι k)
    rw [← hText k (Pi.single j u) x]
    have hsingle : ρW k (Pi.single j u) = Pi.single j ((tys.rep w (idx j)).ρ k u) := by
      funext j'
      rw [ρW_apply]
      by_cases hj : j' = j
      · subst hj; simp only [Pi.single_eq_same]
      · simp only [Pi.single_eq_of_ne hj, map_zero]
    rw [hsingle]
  exact Submodule.mem_iSup_of_mem (idx j) (mem_typeSubmodule_of_isRightEquivariant hTj' (a₀ j))

section RowThreeHelpers

variable (F : Type) [Field F] [NumberField F]

/-- The archimedean product inclusion `inclArch` is the only homomorphism whose archimedean
components are the coordinates. -/
private theorem eq_inclArch (ι : ArchInfra.Kprod F →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : ArchInfra.Kprod F) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion)) :
    ι = ArchInfra.inclArch F := by
  refine MonoidHom.ext fun κ => Units.ext (Matrix.ext fun i j => funext fun w => ?_)
  have h1 := AdelicLevel.archComponent_apply F w (ι κ) i j
  have h2 := AdelicLevel.archComponent_apply F w (ArchInfra.inclArch F κ) i j
  rw [← h1, ← h2, hι, ArchInfra.archComponent_inclArch]

omit [NumberField F] in
/-- The single-place archimedean inclusion of the row-isometry subgroup is injective. -/
private theorem injective_archRowIsometryInclAt₀ (w : InfinitePlace F) :
    Function.Injective (archRowIsometryInclAt₀ F w) := by
  intro a b h
  apply Subtype.ext
  have h1 : archComponent F w (archGLIncl F w (a : GL (Fin 2) w.Completion)) =
      archComponent F w (archGLIncl F w (b : GL (Fin 2) w.Completion)) :=
    congrArg (archComponent F w) h
  rwa [archComponent_archGLIncl_self, archComponent_archGLIncl_self] at h1

/-- A double convolution against a compactly supported archimedean test factor is compactly
supported in the outer variable. -/
private theorem hasCompactSupport_dconvWith_gen {H Kc : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [Group Kc] [TopologicalSpace Kc] [CompactSpace Kc] [MeasurableSpace Kc]
    {μ : Measure Kc}
    {a : Kc →* H} {e₁ e₂ : Kc → ℂ} {ψ : H → ℂ} (ha : Continuous a) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (ArchApproxIdentity.dconvWith μ a e₁ e₂ ψ) := by
  let S : Set H := (fun q : (Kc × H) × Kc => a q.1.1 * q.1.2 * a q.2) '' ((Set.univ ×ˢ tsupport ψ) ×ˢ Set.univ)
  have hS : IsCompact S :=
    ((isCompact_univ.prod hψ).prod isCompact_univ).image
      (((ha.comp (continuous_fst.comp continuous_fst)).mul (continuous_snd.comp continuous_fst)).mul
        (ha.comp continuous_snd))
  refine HasCompactSupport.intro hS fun y hy => ?_
  have hzero : ∀ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) = 0 := by
    intro p
    have hnot : (a p.1)⁻¹ * y * (a p.2)⁻¹ ∉ tsupport ψ := by
      intro hmem
      refine hy ⟨((p.1, (a p.1)⁻¹ * y * (a p.2)⁻¹), p.2), ⟨⟨Set.mem_univ _, hmem⟩, Set.mem_univ _⟩, ?_⟩
      show a p.1 * ((a p.1)⁻¹ * y * (a p.2)⁻¹) * a p.2 = y
      group
    rw [image_eq_zero_of_notMem_tsupport hnot, mul_zero]
  show (∫ p : Kc × Kc, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = 0
  simp_rw [hzero]
  exact integral_zero _ _

end RowThreeHelpers

section RowThreeHelpersFieldLevel

variable (L : Type) [Field L] [NumberField L]

/-- The two-sided action of a continuous family of archimedean matrices on the matrix of mixed
embeddings is continuous in the family. -/
private theorem continuous_sandwich_family {T : Type*} [TopologicalSpace T]
    {A B : T → GL (Fin 2) (InfiniteAdeleRing L)} (hA : Continuous A) (hB : Continuous B) :
    Continuous fun t => LinearMap.toContinuousLinearMap
      (sandwich L (A t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))
        (B t : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing L))) := by
  refine (continuous_clm_apply (𝕜 := ℝ)).mpr fun X => ?_
  have hεA : ∀ i k, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) :=
    fun i k => (continuous_apply k).comp ((continuous_apply i).comp ((continuous_archEntries L).comp hA))
  have hεB : ∀ l j, Continuous fun t => InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j) :=
    fun l j => (continuous_apply j).comp ((continuous_apply l).comp ((continuous_archEntries L).comp hB))
  refine continuous_pi fun i => continuous_pi fun j => ?_
  show Continuous fun t => ∑ k, ∑ l, InfiniteAdeleRing.ringEquiv_mixedSpace L ((A t : Matrix _ _ _) i k) * X k l *
    InfiniteAdeleRing.ringEquiv_mixedSpace L ((B t : Matrix _ _ _) l j)
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    (((hεA i k).mul continuous_const).mul (hεB l j))

omit [NumberField L] in
/-- The local row-isometry subgroup is compact (through the port's `ArchInfra`). -/
private theorem compactSpace_rowIsometrySubgroup₀_of_numberField (w : InfinitePlace L) :
    CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
  haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := L) w
  isCompact_iff_compactSpace.mp (ArchInfra.isCompact_rowIsometrySubgroup₀ w.Completion)

/-- The double convolution of two continuous factors with an archimedean test factor is a `C^∞`
function of the archimedean coordinates. -/
private theorem exists_contDiff_dconvWithC [MeasurableSpace (ArchInfra.Kprod L)]
    [BorelSpace (ArchInfra.Kprod L)] [SecondCountableTopology (ArchInfra.Kprod L)]
    (μ : Measure (ArchInfra.Kprod L)) [IsFiniteMeasure μ]
    {e₁ e₂ : ArchInfra.Kprod L → ℂ} (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    {ψ : GL (Fin 2) (InfiniteAdeleRing L) → ℂ} (hψt : IsArchTestFactor L ψ) :
    ∃ Φ : (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧
      ∀ y, ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch L) e₁ e₂ ψ y = Φ (archEntries L y) := by
  have hCw : ∀ w : InfinitePlace L, CompactSpace (rowIsometrySubgroup₀ w.Completion) :=
    compactSpace_rowIsometrySubgroup₀_of_numberField L
  obtain ⟨⟨Φψ, hΦψ, hψΦ⟩, -⟩ := hψt
  let a := ArchInfra.inclArch L
  have ha : Continuous a := ArchInfra.continuous_inclArch
  let Φf : ArchInfra.Kprod L × ArchInfra.Kprod L →
      (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) →L[ℝ]
        (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace L) := fun p =>
    LinearMap.toContinuousLinearMap (sandwich L ((a p.1)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L))
      ((a p.2)⁻¹ : GL (Fin 2) (InfiniteAdeleRing L)))
  have hΦf : Continuous Φf :=
    continuous_sandwich_family L ((ha.comp continuous_fst).inv) ((ha.comp continuous_snd).inv)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hΦf.continuousOn
  have ht : Continuous fun p : ArchInfra.Kprod L × ArchInfra.Kprod L => e₁ p.1 * e₂ p.2 :=
    (he₁.comp continuous_fst).mul (he₂.comp continuous_snd)
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn ht.continuousOn
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  refine ⟨fun X => ∫ p, (e₁ p.1 * e₂ p.2) * Φψ (Φf p X) ∂(μ.prod μ), ?_, fun y => ?_⟩
  · exact ArchApproxIdentity.contDiff_parametricIntegral_mul Φf hΦf.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => hC p (Set.mem_univ _)) hΦψ ht.aestronglyMeasurable hB0
      (Filter.Eventually.of_forall fun p => (hB p (Set.mem_univ _)).trans (le_max_left _ _))
  · show (∫ p, e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) ∂(μ.prod μ)) = _
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show e₁ p.1 * e₂ p.2 * ψ ((a p.1)⁻¹ * y * (a p.2)⁻¹) =
      e₁ p.1 * e₂ p.2 * Φψ (Φf p (archEntries L y))
    rw [hψΦ ((a p.1)⁻¹ * y * (a p.2)⁻¹), archEntries_mul_mul]
    rfl

end RowThreeHelpersFieldLevel

/-- The integral over a row-isometry product of a continuous factor against an archimedean test
factor is again one, and is bi-finite for `tys` when both factors lie in its type submodules. -/
theorem isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
    (F : Type) [Field F] [NumberField F] [DecidableEq (InfinitePlace F)]
    [MeasurableSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    [BorelSpace (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)]
    (μ : Measure (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion))
    [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (ι : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) →* GL (Fin 2) (InfiniteAdeleRing F))
    (hι : ∀ (κ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion)) (w : InfinitePlace F),
      archComponent F w (ι κ) = ((κ w : rowIsometrySubgroup₀ w.Completion) : GL (Fin 2) w.Completion))
    (tys : AutomorphicForm.ArchTypeFamily F)
    (e₁ e₂ : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) → ℂ) (he₁ : Continuous e₁) (he₂ : Continuous e₂)
    (h : GL (Fin 2) (InfiniteAdeleRing F) → ℂ) (hh : IsArchTestFactor F h) :
    IsArchTestFactor F (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ)) ∧
    ((∀ w : InfinitePlace F,
        e₂ ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ.dual) →
      (∀ w : InfinitePlace F,
        (fun κ => e₁ κ⁻¹) ∈ ⨆ i : Fin (tys.card w),
          typeSubmodule (MonoidHom.mulSingle (fun w : InfinitePlace F => rowIsometrySubgroup₀ w.Completion) w)
            (tys.rep w i).ρ) →
      IsArchFactorBiFinite F tys (fun y => ∫ p : (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion) × (∀ w : InfinitePlace F, rowIsometrySubgroup₀ w.Completion),
        e₁ p.1 * e₂ p.2 * h ((ι p.1)⁻¹ * y * (ι p.2)⁻¹) ∂(μ.prod μ))) := by
  classical
  have hSC : SecondCountableTopology (ArchInfra.Kprod F) :=
    ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ F
  have hCpt : ∀ w : InfinitePlace F, CompactSpace (rowIsometrySubgroup₀ w.Completion) := fun w =>
    haveI : ProperSpace w.Completion := NumberField.AdelicBox.properSpace_completion (K := F) w
    isCompact_iff_compactSpace.mp (ArchInfra.isCompact_rowIsometrySubgroup₀ w.Completion)
  obtain rfl : ι = ArchInfra.inclArch F := eq_inclArch F ι hι
  have ha : Continuous (ArchInfra.inclArch F) := ArchInfra.continuous_inclArch
  have hhc : Continuous h := continuous_of_isArchTestFactor F hh
  have haj : ∀ (w : InfinitePlace F) (k : rowIsometrySubgroup₀ w.Completion),
      ArchInfra.inclArch F
          (MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w k) =
        archRowIsometryInclAt₀ F w k := fun w k => ArchInfra.inclArch_mulSingle w k
  refine ⟨⟨?_, hasCompactSupport_dconvWith_gen ha hh.2⟩, fun he₂t he₁t => ⟨?_, ?_⟩⟩
  · obtain ⟨Φ, hΦ, hΦeq⟩ := exists_contDiff_dconvWithC F μ he₁ he₂ hh
    exact ⟨Φ, hΦ, hΦeq⟩
  · show (fun x => ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁ e₂ h x⁻¹) ∈
      ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorTypeSubmoduleAt F w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    show _ ∈ ⨆ i : Fin (tys.card w), typeSubmodule (archRowIsometryInclAt₀ F w) (tys.rep w i).ρ
    let j : rowIsometrySubgroup₀ w.Completion →* ArchInfra.Kprod F :=
      MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w
    let C : Submodule ℂ (ArchInfra.Kprod F → ℂ) := ArchApproxIdentity.contSubmodule (ArchInfra.Kprod F)
    have hC : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ArchInfra.Kprod F → ℂ),
        u ∈ C → (fun κ => u (κ * j k)) ∈ C :=
      fun k u hu => ArchApproxIdentity.mem_contSubmodule.mpr
        ((ArchApproxIdentity.mem_contSubmodule.mp hu).comp (continuous_id.mul continuous_const))
    let S : ↥C →ₗ[ℂ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
      { toFun := fun u x =>
          ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) (fun κ => (u : ArchInfra.Kprod F → ℂ) κ⁻¹) e₂ h x⁻¹
        map_add' := fun u v => by
          funext x
          show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F)
              (fun κ => ((u : ArchInfra.Kprod F → ℂ) + (v : ArchInfra.Kprod F → ℂ)) κ⁻¹) e₂ h x⁻¹ = _
          rw [show (fun κ => ((u : ArchInfra.Kprod F → ℂ) + (v : ArchInfra.Kprod F → ℂ)) κ⁻¹) =
              (fun κ => (u : ArchInfra.Kprod F → ℂ) κ⁻¹) + fun κ => (v : ArchInfra.Kprod F → ℂ) κ⁻¹ from rfl]
          exact ArchApproxIdentity.dconvWith_add_left
            ((ArchApproxIdentity.mem_contSubmodule.mp u.2).comp continuous_inv)
            ((ArchApproxIdentity.mem_contSubmodule.mp v.2).comp continuous_inv) he₂ hhc ha x⁻¹
        map_smul' := fun c u => by
          funext x
          show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F)
              (fun κ => (c • (u : ArchInfra.Kprod F → ℂ)) κ⁻¹) e₂ h x⁻¹ = _
          rw [show (fun κ => (c • (u : ArchInfra.Kprod F → ℂ)) κ⁻¹) =
              c • fun κ => (u : ArchInfra.Kprod F → ℂ) κ⁻¹ from rfl]
          exact ArchApproxIdentity.dconvWith_smul_left c x⁻¹ }
    have hS : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ↥C) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        S ⟨fun κ => (u : ArchInfra.Kprod F → ℂ) (κ * j k), hC k u u.2⟩ x =
          S u (x * archRowIsometryInclAt₀ F w k) := by
      intro k u x
      show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F)
          (fun κ => (u : ArchInfra.Kprod F → ℂ) (κ⁻¹ * j k)) e₂ h x⁻¹ =
        ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F)
          (fun κ => (u : ArchInfra.Kprod F → ℂ) κ⁻¹) e₂ h (x * archRowIsometryInclAt₀ F w k)⁻¹
      exact ArchApproxIdentity.dconvWith_rt_left (haj w) e₂ h (u : ArchInfra.Kprod F → ℂ) k x
    have he₁' : Continuous fun κ : ArchInfra.Kprod F => e₁ κ⁻¹ := he₁.comp continuous_inv
    have hmem := apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective j
      (archRowIsometryInclAt₀ F w) (injective_archRowIsometryInclAt₀ F w) C hC S hS
      (fun i : Fin (tys.card w) => (tys.rep w i).ρ) (fun κ => e₁ κ⁻¹)
      (ArchApproxIdentity.mem_contSubmodule.mpr he₁') (he₁t w)
    have hSe : S ⟨fun κ => e₁ κ⁻¹, ArchApproxIdentity.mem_contSubmodule.mpr he₁'⟩ =
        fun x => ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁ e₂ h x⁻¹ := by
      funext x
      show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F)
          (fun κ => (fun κ => e₁ κ⁻¹) κ⁻¹) e₂ h x⁻¹ = _
      simp only [inv_inv]
    rw [hSe] at hmem
    exact hmem
  · show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁ e₂ h ∈
      ⨅ w : InfinitePlace F, ⨆ i : Fin (tys.card w), archFactorDualTypeSubmoduleAt F w (tys.rep w i)
    refine (Submodule.mem_iInf _).mpr fun w => ?_
    show _ ∈ ⨆ i : Fin (tys.card w), typeSubmodule (archRowIsometryInclAt₀ F w) (tys.rep w i).ρ.dual
    let j : rowIsometrySubgroup₀ w.Completion →* ArchInfra.Kprod F :=
      MonoidHom.mulSingle (fun v : InfinitePlace F => rowIsometrySubgroup₀ v.Completion) w
    let C : Submodule ℂ (ArchInfra.Kprod F → ℂ) := ArchApproxIdentity.contSubmodule (ArchInfra.Kprod F)
    have hC : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ArchInfra.Kprod F → ℂ),
        u ∈ C → (fun κ => u (κ * j k)) ∈ C :=
      fun k u hu => ArchApproxIdentity.mem_contSubmodule.mpr
        ((ArchApproxIdentity.mem_contSubmodule.mp hu).comp (continuous_id.mul continuous_const))
    let S : ↥C →ₗ[ℂ] (GL (Fin 2) (InfiniteAdeleRing F) → ℂ) :=
      { toFun := fun u => ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁ (u : ArchInfra.Kprod F → ℂ) h
        map_add' := fun u v => by
          funext x
          exact ArchApproxIdentity.dconvWith_add_right he₁
            (ArchApproxIdentity.mem_contSubmodule.mp u.2) (ArchApproxIdentity.mem_contSubmodule.mp v.2)
            hhc ha x
        map_smul' := fun c u => by
          funext x
          exact ArchApproxIdentity.dconvWith_smul_right c x }
    have hS : ∀ (k : rowIsometrySubgroup₀ w.Completion) (u : ↥C) (x : GL (Fin 2) (InfiniteAdeleRing F)),
        S ⟨fun κ => (u : ArchInfra.Kprod F → ℂ) (κ * j k), hC k u u.2⟩ x =
          S u (x * archRowIsometryInclAt₀ F w k) := by
      intro k u x
      show ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁
          (fun κ => (u : ArchInfra.Kprod F → ℂ) (κ * j k)) h x =
        ArchApproxIdentity.dconvWith μ (ArchInfra.inclArch F) e₁ (u : ArchInfra.Kprod F → ℂ) h
          (x * archRowIsometryInclAt₀ F w k)
      exact ArchApproxIdentity.dconvWith_rt_right (haj w) e₁ (u : ArchInfra.Kprod F → ℂ) h k x
    exact apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective j
      (archRowIsometryInclAt₀ F w) (injective_archRowIsometryInclAt₀ F w) C hC S hS
      (fun i : Fin (tys.card w) => (tys.rep w i).ρ.dual) e₂
      (ArchApproxIdentity.mem_contSubmodule.mpr he₂) (he₂t w)


section RowFourHelpers

open AutomorphicForm.ArchCompactOrbit

variable (F : Type) [Field F] [NumberField F]

/-- The reflection `z ↦ z⁻¹` of the group variable, as a linear map on functions. -/
private def reflL : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) where
  toFun X := fun z => X z⁻¹
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem reflL_apply (X : AdelicGL2 (𝓞 F) F → ℂ) (z : AdelicGL2 (𝓞 F) F) :
    reflL F X z = X z⁻¹ := rfl

private theorem reflL_reflL (X : AdelicGL2 (𝓞 F) F → ℂ) : reflL F (reflL F X) = X := by
  funext z; simp [reflL_apply]

private theorem reflL_rightTranslate (h : AdelicGL2 (𝓞 F) F) (X : AdelicGL2 (𝓞 F) F → ℂ) :
    reflL F (rightTranslate F h X) = fun z => reflL F X (h⁻¹ * z) := by
  funext z; simp [reflL_apply, rightTranslate, mul_inv_rev]

private theorem continuous_reflL {X : AdelicGL2 (𝓞 F) F → ℂ} (hX : Continuous X) :
    Continuous (reflL F X) :=
  hX.comp continuous_inv

private theorem hasCompactSupport_reflL {X : AdelicGL2 (𝓞 F) F → ℂ} (hX : HasCompactSupport X) :
    HasCompactSupport (reflL F X) :=
  hX.comp_homeomorph (Homeomorph.inv (AdelicGL2 (𝓞 F) F))

private theorem rightConv_comp_mul_left_eq (ψ f : AdelicGL2 (𝓞 F) F → ℂ) (h : AdelicGL2 (𝓞 F) F) :
    rightConv F ψ (fun z => f (h⁻¹ * z)) = rightTranslate F h (rightConv F ψ f) := by
  have hHaar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  show (∫ z, ψ (x * z) * f (h⁻¹ * z) ∂(adelicGLHaar (Fin 2) (𝓞 F) F)) =
    ∫ z, ψ (x * h * z) * f z ∂(adelicGLHaar (Fin 2) (𝓞 F) F)
  rw [← integral_mul_left_eq_self (fun z => ψ (x * z) * f (h⁻¹ * z)) h]
  simp only [mul_assoc, inv_mul_cancel_left]

private theorem integrable_mul_rightConv {ψ f : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (x : AdelicGL2 (𝓞 F) F) :
    Integrable (fun y => ψ (x * y) * f y) (adelicGLHaar (Fin 2) (𝓞 F) F) := by
  have hHaar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  exact ((hψ.comp (continuous_const.mul continuous_id)).mul hf).integrable_of_hasCompactSupport hfs.mul_left

private theorem rightConv_add_right {ψ f g : AdelicGL2 (𝓞 F) F → ℂ} (hψ : Continuous ψ)
    (hf : Continuous f) (hfs : HasCompactSupport f) (hg : Continuous g) (hgs : HasCompactSupport g) :
    rightConv F ψ (f + g) = rightConv F ψ f + rightConv F ψ g := by
  have hHaar : (adelicGLHaar (Fin 2) (𝓞 F) F).IsHaarMeasure :=
    isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F
  funext x
  rw [Pi.add_apply, rightConv_apply, rightConv_apply, rightConv_apply,
    ← integral_add (integrable_mul_rightConv F hψ hf hfs x) (integrable_mul_rightConv F hψ hg hgs x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (f y + g y) = ψ (x * y) * f y + ψ (x * y) * g y
  ring

private theorem rightConv_smul_right (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F ψ (c • f) = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show ψ (x * y) * (c * f y) = c * (ψ (x * y) * f y)
  ring

private theorem rightConv_smul_left (c : ℂ) (ψ f : AdelicGL2 (𝓞 F) F → ℂ) :
    rightConv F (c • ψ) f = c • rightConv F ψ f := by
  funext x
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply, rightConv_apply, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  show c * ψ (x * y) * f y = c * (ψ (x * y) * f y)
  ring

/-- The bilinear form `(s, t) ↦ rightConv s t` on a submodule of continuous functions and a
submodule of continuous compactly supported ones. -/
private theorem exists_bilin_rightConv (S T : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ s ∈ S, Continuous s) (hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t) :
    ∃ β : S →ₗ[ℂ] T →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      ∀ (s : S) (t : T), β s t = rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ) := by
  refine ⟨LinearMap.mk₂ ℂ (fun (s : S) (t : T) =>
    rightConv F (s : AdelicGL2 (𝓞 F) F → ℂ) (t : AdelicGL2 (𝓞 F) F → ℂ)) ?_ ?_ ?_ ?_, fun s t => rfl⟩
  · intro s s' t
    rw [Submodule.coe_add]
    exact rightConv_add_left F (hS s s.2) (hS s' s'.2) (hT t t.2).1 (hT t t.2).2
  · intro c s t
    rw [Submodule.coe_smul]
    exact rightConv_smul_left F c s t
  · intro s t t'
    rw [Submodule.coe_add]
    exact rightConv_add_right F (hS s s.2) (hT t t.2).1 (hT t t.2).2 (hT t' t'.2).1 (hT t' t'.2).2
  · intro c s t
    rw [Submodule.coe_smul]
    exact rightConv_smul_right F c s t

/-- A left translate of a type-vector is a type-vector. -/
private theorem comp_mul_left_mem_typeSubmodule {G H : Type*} [Group G] [Group H] {ι : H →* G}
    {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ H W} {f : G → ℂ}
    (hf : f ∈ typeSubmodule ι ρ) (h : G) : (fun x => f (h * x)) ∈ typeSubmodule ι ρ := by
  refine Submodule.span_induction (p := fun f _ => (fun x => f (h * x)) ∈ typeSubmodule ι ρ)
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨T, hT, v, rfl⟩
    let Lh : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
      { toFun := fun u x => u (h * x)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hT' : IsRightEquivariant ι ρ (Lh ∘ₗ T) := by
      intro k v x
      show T (ρ k v) (h * x) = T v (h * (x * ι k))
      rw [hT k v (h * x), mul_assoc]
    exact mem_typeSubmodule_of_isRightEquivariant hT' v
  · exact (typeSubmodule ι ρ).zero_mem
  · intro f g _ _ hf hg
    exact (typeSubmodule ι ρ).add_mem hf hg
  · intro c f _ hf
    exact (typeSubmodule ι ρ).smul_mem c hf

private theorem comp_mul_left_mem_archCutSubmodule {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archCutSubmodule F tys) (h : AdelicGL2 (𝓞 F) F) :
    (fun x => f (h * x)) ∈ archCutSubmodule F tys := by
  rw [mem_archCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (h * x)) ∈ ⨆ i : Fin (tys.card w), archTypeSubmoduleAt F w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archTypeSubmoduleAt F w (tys.rep w j)) i (comp_mul_left_mem_typeSubmodule hfi h)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

private theorem comp_mul_left_mem_archDualCutSubmodule {tys : ArchTypeFamily F}
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : f ∈ archDualCutSubmodule F tys) (h : AdelicGL2 (𝓞 F) F) :
    (fun x => f (h * x)) ∈ archDualCutSubmodule F tys := by
  rw [mem_archDualCutSubmodule_iff] at hf ⊢
  intro w
  refine Submodule.iSup_induction _
    (motive := fun f => (fun x => f (h * x)) ∈ ⨆ i : Fin (tys.card w), archDualTypeSubmoduleAt F w (tys.rep w i))
    (hf w) ?_ ?_ ?_
  · intro i f hfi
    exact le_iSup (fun j => archDualTypeSubmoduleAt F w (tys.rep w j)) i (comp_mul_left_mem_typeSubmodule hfi h)
  · exact Submodule.zero_mem _
  · exact fun _ _ hu hv => Submodule.add_mem _ hu hv

/-- A vector of a span of a parametrised family is a finite linear combination. -/
private theorem exists_eq_sum_of_mem_span_range {G : Type*} {ι : Type*} (t : ι → G → ℂ) {h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range t)) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → ι), h = fun x => ∑ j, c j * t (k j) x := by
  classical
  obtain ⟨n, c, v, hv⟩ := (Submodule.mem_span_set').mp hh
  have hk : ∀ j : Fin n, ∃ i : ι, t i = (v j : G → ℂ) := fun j => (v j).2
  choose k hk using hk
  refine ⟨n, c, k, ?_⟩
  rw [← hv]
  funext x
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by rw [hk j]

private theorem exists_eq_sum_of_mem_span_translates {G : Type*} [Group G] {ι : Type*} (g : ι → G)
    {f h : G → ℂ}
    (hh : h ∈ Submodule.span ℂ (Set.range fun i : ι => fun x : G => f (x * g i))) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (k : Fin n → ι), h = fun x => ∑ j, c j * f (x * g (k j)) :=
  exists_eq_sum_of_mem_span_range (fun i x => f (x * g i)) hh

omit [NumberField F] in
private theorem injective_of_forall_apply_eq_zero {V V' : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup V'] [Module ℂ V'] (p : Submodule ℂ V) (q : Submodule ℂ V') (f : p →ₗ[ℂ] q)
    (h : ∀ m, f m = 0 → m = 0) : Function.Injective f := by
  intro a b hab
  have h1 : f (a - b) + f b = f b := by rw [← map_add, sub_add_cancel, hab]
  have h2 : f (a - b) = 0 := add_right_cancel (h1.trans (zero_add _).symm)
  exact sub_eq_zero.mp (h _ h2)

private theorem orbitSpan_le_Ecf {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ Ecf F) :
    orbitSpan F φ ≤ Ecf F := by
  intro ψ hψ
  have hfd : FiniteDimensional ℂ (orbitSpan F φ) := hφ.2
  exact ⟨continuous_of_mem_orbitSpan F hφ.1 ψ hψ,
    Submodule.finiteDimensional_of_le (orbitSpan_le_of_mem F hψ)⟩

private theorem rightTranslate_mem_archCutSubmodule_of_mem_iSup_range (tys : ArchTypeFamily F)
    {k : AdelicGL2 (𝓞 F) F} (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    ∀ φ ∈ archCutSubmodule F tys, rightTranslate F k φ ∈ archCutSubmodule F tys :=
  ArchCutProjector.rightTranslate_mem_of_mem_iSup_range' F _
    (fun w k _ hφ => comp_mul_rowIsometryInclAt₀_mem_archCutSubmodule F hφ w k) hk

private theorem orbitSpanc_le_of_mem {φ ψ : Ecf F} (h : ψ ∈ orbitSpanc F φ) :
    orbitSpanc F ψ ≤ orbitSpanc F φ := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact (Representation.mem_invtSubmodule _).mp (orbitSpanc_mem_invtSubmodule F φ) k h

private theorem coe_mem_orbitSpan_of_mem_orbitSpanc {φ ψ : Ecf F} (h : ψ ∈ orbitSpanc F φ) :
    (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [← map_orbitSpanc]; exact Submodule.mem_map_of_mem h

private theorem mem_orbitSpanc_of_coe_mem_orbitSpan {φ ψ : Ecf F}
    (h : (ψ : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (φ : AdelicGL2 (𝓞 F) F → ℂ)) :
    ψ ∈ orbitSpanc F φ := by
  rw [← map_orbitSpanc] at h
  obtain ⟨ψ', hψ', he⟩ := h
  have : ψ' = ψ := Subtype.ext he
  rwa [this] at hψ'

private theorem mem_Ecf_of_mem_archCut' (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hA : φ ∈ archCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [ArchCutProjector.orbitSpan_eq_span]
  exact finiteDimensional_span_rightTranslate_of_mem_archCutSubmodule F tys hA

private theorem mem_Ecf_of_mem_archDualCut' (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hA : φ ∈ archDualCutSubmodule F tys) (hc : Continuous φ) : φ ∈ Ecf F := by
  refine ⟨hc, ?_⟩
  rw [ArchCutProjector.orbitSpan_eq_span]
  exact finiteDimensional_span_rightTranslate_of_mem_archDualCutSubmodule F tys hA

/-- The data of the `y`-convolution as a linear map on the archimedean orbit span of `G0`. -/
private structure LamData (y G0 : Ecf F) where
  raw : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)
  raw_apply : ∀ X, raw X = rightConv F y (reflL F X)

private theorem exists_lamData (y G0 : Ecf F) (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    Nonempty (LamData F y G0) := by
  let O := orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)
  let T := O.map (reflL F)
  have hT : ∀ t ∈ T, Continuous t ∧ HasCompactSupport t := by
    rintro _ ⟨X, hX, rfl⟩
    exact ⟨continuous_reflL F (continuous_of_mem_orbitSpan F G0.2.1 X hX),
      hasCompactSupport_reflL F (ArchDualCut.hasCompactSupport_of_mem_orbitSpan F hG0s X hX)⟩
  obtain ⟨β, hβ⟩ := exists_bilin_rightConv F (Submodule.span ℂ {(y : AdelicGL2 (𝓞 F) F → ℂ)}) T
    (fun s hs => by
      rw [Submodule.mem_span_singleton] at hs
      obtain ⟨c, rfl⟩ := hs
      exact y.2.1.const_smul c) hT
  let r : O →ₗ[ℂ] T := (reflL F).restrict fun X hX => Submodule.mem_map_of_mem hX
  refine ⟨⟨(β ⟨y, Submodule.mem_span_singleton_self _⟩) ∘ₗ r, fun X => ?_⟩⟩
  rw [LinearMap.comp_apply, hβ]
  rfl

private theorem orbitSpan_le_archCut (tys : ArchTypeFamily F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ archCutSubmodule F tys) : orbitSpan F φ ≤ archCutSubmodule F tys := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  exact rightTranslate_mem_archCutSubmodule_of_mem_iSup_range F tys
    (ArchCutProjector.archProdIncl_mem_iSup F k) φ hφ

private theorem LamData_raw_archRep (y G0 : Ecf F) (L : LamData F y G0) (k : ArchIsometryProd F)
    (X : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) :
    L.raw ⟨archRep F k (X : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) k _ X.2⟩ =
      archRep F k (L.raw X) := by
  rw [L.raw_apply, L.raw_apply]
  dsimp only
  rw [archRep_apply, archRep_apply, reflL_rightTranslate]
  exact rightConv_comp_mul_left_eq F _ _ _

private theorem LamData_raw_mem_Ecf (y G0 : Ecf F) (L : LamData F y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ))
    (X : orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) : L.raw X ∈ Ecf F := by
  have hfd : FiniteDimensional ℂ (orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) := G0.2.2
  refine ⟨?_, ?_⟩
  · rw [L.raw_apply]
    exact continuous_rightConv_of_continuous_of_hasCompactSupport F _ y.2.1 _
      (continuous_reflL F (continuous_of_mem_orbitSpan F G0.2.1 _ X.2))
      (hasCompactSupport_reflL F (ArchDualCut.hasCompactSupport_of_mem_orbitSpan F hG0s _ X.2))
  · have hle : orbitSpan F (L.raw X) ≤ LinearMap.range L.raw := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨k, rfl⟩
      exact ⟨⟨archRep F k (X : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) k _ X.2⟩, LamData_raw_archRep F y G0 L k X⟩
    exact Submodule.finiteDimensional_of_le hle

private def LamData_toEcf (y G0 : Ecf F) (L : LamData F y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) : orbitSpanc F G0 →ₗ[ℂ] Ecf F where
  toFun X := ⟨L.raw ⟨(X : Ecf F), by
      have h := Submodule.mem_map_of_mem (f := (Ecf F).subtype) X.2
      rwa [map_orbitSpanc] at h⟩, LamData_raw_mem_Ecf F y G0 L hG0s _⟩
  map_add' a b := by
    apply Subtype.ext
    show L.raw ⟨(a : Ecf F) + (b : Ecf F), _⟩ = L.raw _ + L.raw _
    rw [← map_add]; rfl
  map_smul' c a := by
    apply Subtype.ext
    show L.raw ⟨c • ((a : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = c • L.raw _
    rw [← map_smul]; rfl

private theorem LamData_toEcf_coe (y G0 : Ecf F) (L : LamData F y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (X : orbitSpanc F G0) :
    ((LamData_toEcf F y G0 L hG0s X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) =
      rightConv F y (reflL F ((X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)) :=
  L.raw_apply _

private theorem LamData_toEcf_ρc (y G0 : Ecf F) (L : LamData F y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (k : ArchIsometryProd F)
    (X : orbitSpanc F G0) :
    LamData_toEcf F y G0 L hG0s
        ⟨ρc F k X, (Representation.mem_invtSubmodule _).mp (orbitSpanc_mem_invtSubmodule F G0) k X.2⟩ =
      ρc F k (LamData_toEcf F y G0 L hG0s X) := by
  apply Subtype.ext
  show L.raw ⟨archRep F k ((X : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = archRep F k (L.raw _)
  exact LamData_raw_archRep F y G0 L k ⟨(X : Ecf F), coe_mem_orbitSpan_of_mem_orbitSpanc F X.2⟩

private theorem LamData_raw_mem_archCutSubmodule (y G0 : Ecf F) (L : LamData F y G0)
    (tys : ArchTypeFamily F) {q : AdelicGL2 (𝓞 F) F → ℂ}
    (hqO : q ∈ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (hqA : q ∈ archCutSubmodule F tys) :
    L.raw ⟨q, hqO⟩ ∈ archCutSubmodule F tys := by
  classical
  have hG0fd : FiniteDimensional ℂ (orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ)) := G0.2.2
  let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan F q
  have hSO : S ≤ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan_le_of_mem F hqO
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSO
  let θ₀ : S →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) := L.raw ∘ₗ Submodule.inclusion hSO
  have hθ₀ : ∀ (k : ArchIsometryProd F) (s : S),
      θ₀ ⟨archRep F k (s : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F q k (s : AdelicGL2 (𝓞 F) F → ℂ) s.2⟩ = archRep F k (θ₀ s) := by
    intro k s
    show L.raw ⟨archRep F k (s : AdelicGL2 (𝓞 F) F → ℂ), _⟩ = archRep F k (L.raw ⟨s, hSO s.2⟩)
    exact LamData_raw_archRep F y G0 L k ⟨s, hSO s.2⟩
  have hSA : S ≤ archCutSubmodule F tys := orbitSpan_le_archCut F tys hqA
  rw [mem_archCutSubmodule_iff]
  intro w
  refine (ArchCutProjector.le_iSup_archTypeSubmoduleAt_of_surjective F w tys S (LinearMap.range θ₀) ?_ ?_
    θ₀.rangeRestrict (LinearMap.surjective_rangeRestrict θ₀) ?_ ?_)
    (LinearMap.mem_range_self θ₀ ⟨q, mem_orbitSpan_self F q⟩)
  · rintro k _ ⟨s, rfl⟩
    refine ⟨⟨archRep F (Pi.mulSingle w k) (s : AdelicGL2 (𝓞 F) F → ℂ),
      archRep_mem_orbitSpan F q (Pi.mulSingle w k) _ s.2⟩, ?_⟩
    refine (hθ₀ (Pi.mulSingle w k) s).trans ?_
    rw [archRep_apply, ArchCutProjector.archProdIncl_mulSingle]
  · intro k s hs
    have h := archRep_mem_orbitSpan F q (Pi.mulSingle w k) (s : AdelicGL2 (𝓞 F) F → ℂ) hs
    rwa [archRep_apply, ArchCutProjector.archProdIncl_mulSingle] at h
  · intro k s
    have h := hθ₀ (Pi.mulSingle w k) s
    simp only [archRep_apply, ArchCutProjector.archProdIncl_mulSingle] at h
    exact h
  · intro s hs
    exact (mem_archCutSubmodule_iff F tys (s : AdelicGL2 (𝓞 F) F → ℂ)).mp (hSA hs) w

private theorem eq_zero_of_injective_equivariant (tys : ArchTypeFamily F)
    (Pc : Submodule ℂ (Ecf F)) (hPcinv : ∀ (k : ArchIsometryProd F) (c : Ecf F), c ∈ Pc → ρc F k c ∈ Pc)
    (hPcA : ∀ c : Pc, ((c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys → c = 0)
    (Rc : Pc →ₗ[ℂ] Ecf F)
    (hRc : ∀ (k : ArchIsometryProd F) (c : Pc),
      Rc ⟨ρc F k (c : Ecf F), hPcinv k (c : Ecf F) c.2⟩ = ρc F k (Rc c))
    (hRinj : Function.Injective Rc)
    (c₀ : Pc) (hvA : ((Rc c₀ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys) :
    Rc c₀ = 0 := by
  classical
  set v : Ecf F := Rc c₀ with hv
  let e : Pc ≃ₗ[ℂ] LinearMap.range Rc := LinearEquiv.ofInjective Rc hRinj
  have he : ∀ c : Pc, ((e c : LinearMap.range Rc) : Ecf F) = Rc c := fun c => rfl
  have hrangeinv : ∀ (k : ArchIsometryProd F), ∀ r ∈ LinearMap.range Rc, ρc F k r ∈ LinearMap.range Rc := by
    rintro k _ ⟨c, rfl⟩
    exact ⟨⟨ρc F k (c : Ecf F), hPcinv k (c : Ecf F) c.2⟩, hRc k c⟩
  have hOv : ∀ s ∈ orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ),
      ∃ hs : s ∈ Ecf F, (⟨s, hs⟩ : Ecf F) ∈ LinearMap.range Rc := by
    intro s hs
    have hs' : s ∈ (LinearMap.range Rc).map (Ecf F).subtype := by
      refine (Submodule.span_le.mpr ?_) hs
      rintro _ ⟨k, rfl⟩
      exact ⟨ρc F k v, hrangeinv k v ⟨c₀, rfl⟩, rfl⟩
    obtain ⟨r, hr, rfl⟩ := hs'
    exact ⟨r.2, by simpa using hr⟩
  let S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ)
  have hSfd : FiniteDimensional ℂ S := v.2.2

  let ι₁ : S →ₗ[ℂ] LinearMap.range Rc :=
    { toFun := fun s => ⟨⟨(s : AdelicGL2 (𝓞 F) F → ℂ), (hOv s s.2).1⟩, (hOv s s.2).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let cof : S → Pc := fun s => e.symm (ι₁ s)
  have hcof : ∀ s : S, ((Rc (cof s) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := by
    intro s
    have h1 : e (cof s) = ι₁ s := LinearEquiv.apply_symm_apply e (ι₁ s)
    have h2 : ((e (cof s) : LinearMap.range Rc) : Ecf F) = Rc (cof s) := he (cof s)
    rw [h1] at h2
    have h3 : (((ι₁ s : LinearMap.range Rc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := rfl
    rw [← h3, h2]
  have hcof_add : ∀ a b : S, cof (a + b) = cof a + cof b := fun a b => by
    show e.symm (ι₁ (a + b)) = _
    rw [map_add, map_add]
  have hcof_smul : ∀ (r : ℂ) (a : S), cof (r • a) = r • cof a := fun r a => by
    show e.symm (ι₁ (r • a)) = _
    rw [map_smul, map_smul]
  let θ₀ : S →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    { toFun := fun s => (((cof s : Pc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ)
      map_add' := fun a b => by simp only [hcof_add, Submodule.coe_add]
      map_smul' := fun r a => by simp only [hcof_smul, Submodule.coe_smul, RingHom.id_apply] }
  have hθ₀_def : ∀ s : S, θ₀ s = (((cof s : Pc) : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := fun s => rfl
  have hcof_eq : ∀ (k : ArchIsometryProd F) (s : S),
      cof ⟨archRep F k (s : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ) k (s : _) s.2⟩ =
        ⟨ρc F k (cof s : Pc), hPcinv k _ (cof s).2⟩ := by
    intro k s
    apply hRinj
    rw [hRc]
    apply Subtype.ext
    rw [hcof, ρc_apply_coe, hcof]
  have hθ₀ : ∀ (k : ArchIsometryProd F) (s : S),
      θ₀ ⟨archRep F k (s : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ) k (s : _) s.2⟩ =
        archRep F k (θ₀ s) := by
    intro k s
    rw [hθ₀_def, hθ₀_def, hcof_eq]
    rfl

  have hSA : S ≤ archCutSubmodule F tys := orbitSpan_le_archCut F tys hvA
  have hθ₀A : ∀ s : S, θ₀ s ∈ archCutSubmodule F tys := by
    intro s
    rw [mem_archCutSubmodule_iff]
    intro w
    refine (ArchCutProjector.le_iSup_archTypeSubmoduleAt_of_surjective F w tys S (LinearMap.range θ₀) ?_ ?_
      θ₀.rangeRestrict (LinearMap.surjective_rangeRestrict θ₀) ?_ ?_) (LinearMap.mem_range_self θ₀ s)
    · rintro k _ ⟨s, rfl⟩
      refine ⟨⟨archRep F (Pi.mulSingle w k) (s : AdelicGL2 (𝓞 F) F → ℂ),
        archRep_mem_orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ) (Pi.mulSingle w k) _ s.2⟩, ?_⟩
      refine (hθ₀ (Pi.mulSingle w k) s).trans ?_
      rw [archRep_apply, ArchCutProjector.archProdIncl_mulSingle]
    · intro k s hs
      have h := archRep_mem_orbitSpan F (v : AdelicGL2 (𝓞 F) F → ℂ) (Pi.mulSingle w k)
        (s : AdelicGL2 (𝓞 F) F → ℂ) hs
      rwa [archRep_apply, ArchCutProjector.archProdIncl_mulSingle] at h
    · intro k s
      have h := hθ₀ (Pi.mulSingle w k) s
      simp only [archRep_apply, ArchCutProjector.archProdIncl_mulSingle] at h
      exact h
    · intro s hs
      exact (mem_archCutSubmodule_iff F tys (s : AdelicGL2 (𝓞 F) F → ℂ)).mp (hSA hs) w
  have hz : cof ⟨v, mem_orbitSpan_self F _⟩ = 0 := hPcA _ (by rw [← hθ₀_def]; exact hθ₀A _)
  have hfin := hcof ⟨v, mem_orbitSpan_self F _⟩
  rw [hz, map_zero] at hfin
  apply Subtype.ext
  exact hfin.symm

private theorem LamData_apply_raw_eq_zero (y G0 : Ecf F) (L : LamData F y G0)
    (hG0s : HasCompactSupport (G0 : AdelicGL2 (𝓞 F) F → ℂ)) (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (h1 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ)
    (h2 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F →
      Q φ ∈ archCutSubmodule F tys ∧ Q φ ∈ orbitSpan F φ)
    (h3 : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → ∀ k : ArchIsometryProd F,
      Q (archRep F k φ) = archRep F k (Q φ))
    (hc : Ecf F) (hhO : (hc : AdelicGL2 (𝓞 F) F → ℂ) ∈ orbitSpan F (G0 : AdelicGL2 (𝓞 F) F → ℂ))
    (hQh : Q hc = 0) : Q (L.raw ⟨hc, hhO⟩) = 0 := by
  classical
  have hQW : ∀ w' ∈ orbitSpan F (hc : AdelicGL2 (𝓞 F) F → ℂ), Q w' = 0 := by
    intro w' hw'
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hw'
    · rintro _ ⟨k, rfl⟩; rw [h3 _ hc.2 k, hQh, map_zero]
    · exact map_zero Q
    · intro a b _ _ ha hb; rw [map_add, ha, hb, add_zero]
    · intro c a _ ha; rw [map_smul, ha, smul_zero]

  have hWA : ∀ w' ∈ orbitSpan F (hc : AdelicGL2 (𝓞 F) F → ℂ), w' ∈ archCutSubmodule F tys → w' = 0 := by
    intro w' hw' hA
    rw [← h1 w' (continuous_of_mem_orbitSpan F hc.2.1 w' hw') hA]
    exact hQW w' hw'

  have hhcO : hc ∈ orbitSpanc F G0 := mem_orbitSpanc_of_coe_mem_orbitSpan F hhO
  have hWOc : orbitSpanc F hc ≤ orbitSpanc F G0 := orbitSpanc_le_of_mem F hhcO
  have hWinv : ∀ (k : ArchIsometryProd F) (x : Ecf F), x ∈ orbitSpanc F hc → ρc F k x ∈ orbitSpanc F hc :=
    fun k x hx => (Representation.mem_invtSubmodule (ρc F)).mp (orbitSpanc_mem_invtSubmodule F hc) k hx
  let ΛW : orbitSpanc F hc →ₗ[ℂ] Ecf F := LamData_toEcf F y G0 L hG0s ∘ₗ Submodule.inclusion hWOc
  have hΛW_def : ∀ x : orbitSpanc F hc, ΛW x = LamData_toEcf F y G0 L hG0s ⟨x, hWOc x.2⟩ := fun x => rfl
  have hΛW : ∀ (k : ArchIsometryProd F) (x : orbitSpanc F hc),
      ΛW ⟨ρc F k (x : Ecf F), hWinv k (x : Ecf F) x.2⟩ = ρc F k (ΛW x) := by
    intro k x
    rw [hΛW_def, hΛW_def]
    exact LamData_toEcf_ρc F y G0 L hG0s k ⟨x, hWOc x.2⟩
  have hΛWcoe : ∀ x : orbitSpanc F hc, ((ΛW x : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) =
      L.raw ⟨(x : Ecf F), coe_mem_orbitSpan_of_mem_orbitSpanc F (hWOc x.2)⟩ := fun x => rfl

  let P : Submodule ℂ (Ecf F) := (LinearMap.ker ΛW).map (orbitSpanc F hc).subtype
  have hPW : P ≤ orbitSpanc F hc := Submodule.map_subtype_le _ _
  have hPinv : P ∈ (ρc F).invtSubmodule := by
    rw [Representation.mem_invtSubmodule]
    rintro k _ ⟨x, hx, rfl⟩
    have hx' : ΛW x = 0 := hx
    refine ⟨⟨ρc F k (x : Ecf F), hWinv k (x : Ecf F) x.2⟩, ?_, rfl⟩
    show ΛW ⟨ρc F k (x : Ecf F), _⟩ = 0
    rw [hΛW, hx', map_zero]
  obtain ⟨Pc, hPcinv, hPPc, hPsup⟩ :=
    exists_invt_compl F (orbitSpanc F hc) (orbitSpanc_mem_invtSubmodule F hc) P hPinv hPW
  have hPcinv' : ∀ (k : ArchIsometryProd F) (c : Ecf F), c ∈ Pc → ρc F k c ∈ Pc :=
    fun k c hcm => (Representation.mem_invtSubmodule (ρc F)).mp hPcinv k hcm
  have hPcW : Pc ≤ orbitSpanc F hc := by rw [← hPsup]; exact le_sup_right
  let Rc : Pc →ₗ[ℂ] Ecf F := ΛW ∘ₗ Submodule.inclusion hPcW
  have hRc_def : ∀ c : Pc, Rc c = ΛW ⟨c, hPcW c.2⟩ := fun c => rfl
  have hRc : ∀ (k : ArchIsometryProd F) (c : Pc),
      Rc ⟨ρc F k (c : Ecf F), hPcinv' k (c : Ecf F) c.2⟩ = ρc F k (Rc c) := by
    intro k c
    rw [hRc_def, hRc_def]
    exact hΛW k ⟨c, hPcW c.2⟩
  have hRinj : Function.Injective Rc := by
    refine injective_of_forall_apply_eq_zero Pc (Ecf F) Rc fun c hc0 => ?_
    have hcP : (c : Ecf F) ∈ P := ⟨⟨c, hPcW c.2⟩, hc0, rfl⟩
    have hmem : (c : Ecf F) ∈ P ⊓ Pc := ⟨hcP, c.2⟩
    rw [hPPc, Submodule.mem_bot] at hmem
    exact Subtype.ext hmem
  have hPcA : ∀ c : Pc, ((c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) ∈ archCutSubmodule F tys → c = 0 := by
    intro c hcA
    have h0 := hWA _ (coe_mem_orbitSpan_of_mem_orbitSpanc F (hPcW c.2)) hcA
    apply Subtype.ext; apply Subtype.ext; exact h0

  have hrange : ∀ x : orbitSpanc F hc, ∃ c : Pc, Rc c = ΛW x := by
    intro x
    have hx : (x : Ecf F) ∈ P ⊔ Pc := by rw [hPsup]; exact x.2
    obtain ⟨p, hp, c, hcm, hpc⟩ := Submodule.mem_sup.mp hx
    obtain ⟨p', hp', rfl⟩ := hp
    have hp'' : ΛW p' = 0 := hp'
    refine ⟨⟨c, hcm⟩, ?_⟩
    have hxe : x = p' + ⟨c, hPcW hcm⟩ := Subtype.ext hpc.symm
    rw [hRc_def, hxe, map_add, hp'', zero_add]

  have hΛhE : L.raw ⟨hc, hhO⟩ ∈ Ecf F := LamData_raw_mem_Ecf F y G0 L hG0s ⟨hc, hhO⟩
  obtain ⟨hQA, hQO⟩ := h2 _ hΛhE
  have hΛh_eq : L.raw ⟨hc, hhO⟩ =
      ((ΛW ⟨hc, mem_orbitSpanc_self F hc⟩ : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) := by
    rw [hΛWcoe]
  obtain ⟨c₁, hc₁⟩ := hrange ⟨hc, mem_orbitSpanc_self F hc⟩
  have hmem : ∀ s ∈ orbitSpan F (L.raw ⟨hc, hhO⟩),
      ∃ c : Pc, ((Rc c : Ecf F) : AdelicGL2 (𝓞 F) F → ℂ) = s := by
    intro s hs
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hs
    · rintro _ ⟨k, rfl⟩
      refine ⟨⟨ρc F k (c₁ : Ecf F), hPcinv' k (c₁ : Ecf F) c₁.2⟩, ?_⟩
      rw [hRc, ρc_apply_coe, hc₁, ← hΛh_eq]
    · exact ⟨0, by rw [map_zero]; rfl⟩
    · rintro a b _ _ ⟨ca, rfl⟩ ⟨cb, rfl⟩
      exact ⟨ca + cb, by rw [map_add]; rfl⟩
    · rintro r a _ ⟨ca, rfl⟩
      exact ⟨r • ca, by rw [map_smul]; rfl⟩
  obtain ⟨c, hcq⟩ := hmem _ hQO
  rw [← hcq] at hQA ⊢
  rw [eq_zero_of_injective_equivariant F tys Pc hPcinv' hPcA Rc hRc hRinj c hQA]
  rfl

end RowFourHelpers

open AutomorphicForm.ArchCompactOrbit

/-- The archimedean cut projector fixes right convolution up to a factorizable, bi-finite test
function. -/
theorem exists_rightConv_eq_of_archCutProjector
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ))
    (hQ :
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        ∀ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          Q (rightTranslate F k φ) = rightTranslate F k (Q φ)))
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hyc : Continuous y) (hy : y ∈ archCutSubmodule F tys)
    {f : AdelicGL2 (𝓞 F) F → ℂ} (tys' : ArchTypeFamily F) (hf : IsFactorizableTestFn F f) (hbf : IsArchBiFinite F tys' f) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      Q (rightConv F y f) = rightConv F y f' := by
  classical
  have h2' : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F →
      Q φ ∈ archCutSubmodule F tys ∧ Q φ ∈ orbitSpan F φ := by
    intro φ hφ
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ
        {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          ψ = rightTranslate F k φ}) := by
      rw [← ArchCutProjector.orbitSpan_eq_span]; exact hφ.2
    obtain ⟨hA, hS⟩ := hQ.2.1 φ hφ.1 hfd
    exact ⟨hA, by rw [ArchCutProjector.orbitSpan_eq_span]; exact hS⟩
  have h3' : ∀ φ : AdelicGL2 (𝓞 F) F → ℂ, φ ∈ Ecf F → ∀ k : ArchIsometryProd F,
      Q (archRep F k φ) = archRep F k (Q φ) := by
    intro φ hφ k
    have hfd : FiniteDimensional ℂ (Submodule.span ℂ
        {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
          ψ = rightTranslate F k φ}) := by
      rw [← ArchCutProjector.orbitSpan_eq_span]; exact hφ.2
    rw [archRep_apply]
    exact hQ.2.2 φ hφ.1 hfd _ (ArchCutProjector.archProdIncl_mem_iSup F k)

  obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  have hG0A : reflL F f ∈ archCutSubmodule F tys' := hbf.1
  have hG0c : Continuous (reflL F f) := continuous_reflL F hfc
  have hG0s : HasCompactSupport (reflL F f) := hasCompactSupport_reflL F hfs
  have hG0E : reflL F f ∈ Ecf F := mem_Ecf_of_mem_archCut' F tys' hG0A hG0c
  set G0 : Ecf F := ⟨reflL F f, hG0E⟩ with hG0
  have hyE : y ∈ Ecf F := mem_Ecf_of_mem_archCut' F tys hy hyc
  obtain ⟨L⟩ := exists_lamData F ⟨y, hyE⟩ G0 hG0s
  have hconv : rightConv F y f = L.raw ⟨reflL F f, mem_orbitSpan_self F _⟩ := by
    rw [L.raw_apply, reflL_reflL]

  obtain ⟨hqA, hqO⟩ := h2' (reflL F f) hG0E
  have hqc : Continuous (Q (reflL F f)) := continuous_of_mem_orbitSpan F hG0c _ hqO
  have hqs : HasCompactSupport (Q (reflL F f)) :=
    ArchDualCut.hasCompactSupport_of_mem_orbitSpan F hG0s _ hqO
  have hhO : reflL F f - Q (reflL F f) ∈ orbitSpan F (reflL F f) :=
    Submodule.sub_mem _ (mem_orbitSpan_self F _) hqO
  have hQh : Q (reflL F f - Q (reflL F f)) = 0 := by
    rw [map_sub, hQ.1 _ hqc hqA, sub_self]
  have hsplit : L.raw ⟨reflL F f, mem_orbitSpan_self F _⟩ =
      L.raw ⟨Q (reflL F f), hqO⟩ + L.raw ⟨_, hhO⟩ := by
    rw [← map_add]; congr 1; apply Subtype.ext; simp
  have hΛqA : L.raw ⟨Q (reflL F f), hqO⟩ ∈ archCutSubmodule F tys :=
    LamData_raw_mem_archCutSubmodule F ⟨y, hyE⟩ G0 L tys hqO hqA
  have hΛqE : L.raw ⟨Q (reflL F f), hqO⟩ ∈ Ecf F := LamData_raw_mem_Ecf F ⟨y, hyE⟩ G0 L hG0s ⟨_, hqO⟩
  have hQΛq : Q (L.raw ⟨Q (reflL F f), hqO⟩) = L.raw ⟨Q (reflL F f), hqO⟩ :=
    hQ.1 _ hΛqE.1 hΛqA
  have hQΛh : Q (L.raw ⟨_, hhO⟩) = 0 :=
    LamData_apply_raw_eq_zero F ⟨y, hyE⟩ G0 L hG0s tys Q hQ.1 h2' h3'
      ⟨_, orbitSpan_le_Ecf F hG0E hhO⟩ hhO hQh
  have hQconv : Q (rightConv F y f) = rightConv F y (reflL F (Q (reflL F f))) := by
    rw [hconv, hsplit, map_add, hQΛq, hQΛh, add_zero, L.raw_apply]

  set q := Q (reflL F f) with hq
  obtain ⟨n, c, κ, hqsum⟩ := exists_eq_sum_of_mem_span_translates (archProdIncl F) (f := reflL F f)
    (h := q) (by exact hqO)
  have hf2 : reflL F q = fun x => ∑ j, c j * f ((archProdIncl F (κ j))⁻¹ * x * 1) := by
    funext x
    rw [reflL_apply, hqsum]
    simp only [reflL_apply, mul_inv_rev, inv_inv, mul_one]
  have hf2T : IsFactorizableTestFn F (reflL F q) := by
    rw [hf2]
    exact isFactorizableTestFn_sum_mul_comp_mul_mul F hf c _ _
      (fun j => Subgroup.inv_mem _ (ArchCutProjector.archProdIncl_mem_iSup F (κ j)))
      (fun _ => Subgroup.one_mem _)
  have hf2D : reflL F q ∈ archDualCutSubmodule F tys' := by
    have hsum : reflL F q = ∑ j, c j • fun x => f ((archProdIncl F (κ j))⁻¹ * x) := by
      rw [hf2]; funext x; simp [Finset.sum_apply]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (comp_mul_left_mem_archDualCutSubmodule F hbf.2 _)
  have hf2c : Continuous (reflL F q) := continuous_reflL F hqc
  have hf2s : HasCompactSupport (reflL F q) := hasCompactSupport_reflL F hqs
  have hf2E : reflL F q ∈ Ecf F := mem_Ecf_of_mem_archDualCut' F tys' hf2D hf2c
  have hf2K : FiniteDimensional ℂ (Submodule.span ℂ
      {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range),
        ψ = rightTranslate F k (reflL F q)}) := by
    rw [← ArchCutProjector.orbitSpan_eq_span]; exact hf2E.2

  obtain ⟨f3, hf3S, hf3D, hf3conv⟩ :=
    exists_mem_span_rightTranslate_mem_archDualCutSubmodule_and_rightConv_eq F tys hyc hy
      hf2c hf2s hf2K
  rw [← ArchCutProjector.orbitSpan_eq_span] at hf3S
  obtain ⟨m, c', κ', hf3sum⟩ := exists_eq_sum_of_mem_span_translates (archProdIncl F) (f := reflL F q)
    (h := f3) (by exact hf3S)
  refine ⟨f3, ?_, ⟨?_, hf3D⟩, ?_⟩
  · have hf3 : f3 = fun x => ∑ j, c' j * reflL F q (1 * x * archProdIncl F (κ' j)) := by
      rw [hf3sum]; funext x; simp only [one_mul]
    rw [hf3]
    exact isFactorizableTestFn_sum_mul_comp_mul_mul F hf2T c' _ _
      (fun _ => Subgroup.one_mem _) (fun j => ArchCutProjector.archProdIncl_mem_iSup F (κ' j))
  · have hdual : (fun x => f3 x⁻¹) = ∑ j, c' j • fun x => q ((archProdIncl F (κ' j))⁻¹ * x) := by
      rw [hf3sum]; funext x
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, reflL_apply, mul_inv_rev, inv_inv]
    rw [hdual]
    exact Submodule.sum_mem _ fun j _ =>
      Submodule.smul_mem _ _ (comp_mul_left_mem_archCutSubmodule F hqA _)
  · rw [hQconv, hf3conv]


end AutomorphicForm

end


/-
  The projector's three properties, without the translate commutation.

  The pin's shorter companion to the headline above: the same `Q`, the same first two properties,
  and the `rightConv` property read through `exists_rightConv_eq_of_archCutProjector`
  (`Adelic/ArchApproximation.lean`), which is the shape the cusp constituent's rows consume.
-/
open AutomorphicForm
open MeasureTheory NumberField AutomorphicForm AutomorphicForm.CuspidalConstituent
open scoped BigOperators

theorem AutomorphicForm.exists_linearMap_archCutProjector
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F) :
    ∃ Q : (AdelicGL2 (𝓞 F) F → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ → φ ∈ archCutSubmodule F tys → Q φ = φ) ∧
      (∀ φ : AdelicGL2 (𝓞 F) F → ℂ, Continuous φ →
        FiniteDimensional ℂ (Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) →
        Q φ ∈ archCutSubmodule F tys ⊓ Submodule.span ℂ
          {ψ : AdelicGL2 (𝓞 F) F → ℂ | ∃ k ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range), ψ = rightTranslate F k φ}) ∧
      (∀ y : AdelicGL2 (𝓞 F) F → ℂ, Continuous y → y ∈ archCutSubmodule F tys →
        ∀ (f : AdelicGL2 (𝓞 F) F → ℂ) (tys' : ArchTypeFamily F), IsFactorizableTestFn F f → IsArchBiFinite F tys' f →
          ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
            Q (rightConv F y f) = rightConv F y f') := by
  obtain ⟨Q, h1, h2, h3⟩ := AutomorphicForm.exists_linearMap_archCutProjector_comm_rightTranslate F tys
  exact ⟨Q, h1, h2, fun y hyc hy f tys' hf hbf =>
    AutomorphicForm.exists_rightConv_eq_of_archCutProjector F tys Q ⟨h1, h2, h3⟩ hyc hy tys' hf hbf⟩
