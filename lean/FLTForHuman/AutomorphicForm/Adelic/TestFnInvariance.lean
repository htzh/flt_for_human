/-
  The factorizable test functions are stable under the right action, and the equivariant extension
  lemma the archimedean approximation consumes.

  Three rows, one theme — the algebra of the test functions `IsFactorizableTestFn`:

  * `isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn`: `y ↦ f (t⁻¹ * y)` is again
    factorizable (the archimedean and finite factors are each composed with a left translate, which
    preserves `IsArchTestFactor` / `IsFinTestFactor`);
  * `isFactorizableTestFn_sum_mul_comp_mul_mul`: a finite sum `∑ i, c i * f (a i * y * b i)` is
    factorizable when the `a i` and `b i` are **row isometries** — the archimedean factor is the
    sum of the sandwished archimedean factors, which stays `C^∞` with compact support because the
    row-isometry action is by a continuous linear change of the matrix variable;
  * `exists_isRightEquivariant_comp_subtype_eq_of_injective`: the **generic** extension lemma that
    the first two are used with — a linear map `TA` on an invariant submodule `A ⊆ W` that is
    right-equivariant along an injective `ι : H →* G` extends to a right-equivariant `T` on `W`,
    with `T ∘ A.subtype = TA` (choose representatives of the `H`-cosets in `G` and let `T` act
    through the representation on the `ι`-component).

  The first two are the premisses of `exists_rightConv_eq_of_archCutProjector` (1,131 silo) and of
  the archimedean cut projector's invariance; the third is the premise of the archimedean
  approximation identity (`isArchTestFactor_and_isArchFactorBiFinite_integral_prod_…`, 1,175) and of
  `rightConv_mem_archCutSubmodule_of_isArchBiFinite` (190).

  Transcribed from the pin's three `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  70 + 98 + 51 lines). None of them is more than a screen of proof, and all three have
  `return 0` consumers of their own: they are the cheapest rows on the shelf (§1 of
  `lean/topics/automorphicForm/SET-AF22.md`).

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isRightEquivariant_comp_subtype_eq_of_injective.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_sum_mul_comp_mul_mul.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothLeft
import FLTForHuman.AutomorphicForm.Adelic.ArchType
import FLTForHuman.RepTheory.TypeInvariance

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel IsDedekindDomain
open AutomorphicForm
open scoped Classical ENNReal Pointwise BigOperators

noncomputable section

namespace AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel

/-- **The generic equivariant extension.** A right-equivariant linear map on an invariant submodule
extends to the whole space, along an injective group homomorphism. -/
theorem exists_isRightEquivariant_comp_subtype_eq_of_injective
    {H G : Type*} [Group H] [Group G] {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι) (ρ : Representation ℂ H W)
    (A : Submodule ℂ W) (hA : ∀ (k : H) (a : W), a ∈ A → ρ k a ∈ A)
    (TA : ↥A →ₗ[ℂ] (G → ℂ))
    (hTA : ∀ (k : H) (a : ↥A) (x : G), TA ⟨ρ k a, hA k a a.2⟩ x = TA a (x * ι k)) :
    ∃ T : W →ₗ[ℂ] (G → ℂ), IsRightEquivariant ι ρ T ∧ T ∘ₗ A.subtype = TA := by
  classical
  let R : Setoid G := ⟨fun x y => ∃ k : H, y = x * ι k,
    ⟨fun x => ⟨1, by rw [map_one, mul_one]⟩,
     fun {x y} h => by
       obtain ⟨k, hk⟩ := h
       exact ⟨k⁻¹, by rw [hk, map_inv, mul_inv_cancel_right]⟩,
     fun {x y z} h h' => by
       obtain ⟨k, hk⟩ := h
       obtain ⟨k', hk'⟩ := h'
       exact ⟨k * k', by rw [hk', hk, map_mul, mul_assoc]⟩⟩⟩
  let s : Quotient R → G := Quotient.out
  have hs : ∀ x : G, ∃ k : H, x = s (Quotient.mk R x) * ι k :=
    fun x => Quotient.exact (Quotient.out_eq (Quotient.mk R x))
  choose kx hkx using hs
  have hq_mul : ∀ (x : G) (k : H), Quotient.mk R (x * ι k) = Quotient.mk R x :=
    fun x k => Quotient.sound ⟨k⁻¹, by rw [map_inv, mul_inv_cancel_right]⟩
  have huniq : ∀ (q : Quotient R) (k₁ k₂ : H), s q * ι k₁ = s q * ι k₂ → k₁ = k₂ :=
    fun q k₁ k₂ h => hι (mul_left_cancel h)
  have hk_mul : ∀ (x : G) (k : H), kx (x * ι k) = kx x * k := by
    intro x k
    apply huniq (Quotient.mk R x)
    have h1 : s (Quotient.mk R x) * ι (kx (x * ι k)) = x * ι k := by
      have h := hkx (x * ι k)
      rw [hq_mul] at h
      exact h.symm
    have h2 : s (Quotient.mk R x) * ι (kx x * k) = x * ι k := by
      rw [map_mul, ← mul_assoc, ← hkx x]
    exact h1.trans h2.symm
  let e : ↥A →ₗ[ℂ] (Quotient R → ℂ) :=
    { toFun := fun a q => TA a (s q)
      map_add' := by intro a b; funext q; simp only [map_add, Pi.add_apply]
      map_smul' := by intro c a; funext q; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  obtain ⟨E, hE⟩ := LinearMap.exists_extend e
  have hEe : ∀ a : ↥A, E (a : W) = e a := fun a => by rw [← hE]; rfl
  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => E (ρ (kx x) w) (Quotient.mk R x)
      map_add' := by intro v w; funext x; simp only [map_add, Pi.add_apply]
      map_smul' := by intro c w; funext x; simp only [map_smul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨T, ?_, ?_⟩
  · intro k v x
    show E (ρ (kx x) (ρ k v)) (Quotient.mk R x) = E (ρ (kx (x * ι k)) v) (Quotient.mk R (x * ι k))
    rw [hk_mul, hq_mul, map_mul]
    rfl
  · apply LinearMap.ext
    intro a
    funext x
    show E (ρ (kx x) (a : W)) (Quotient.mk R x) = TA a x
    have hmem : ρ (kx x) (a : W) ∈ A := hA _ _ a.2
    have h1 : E (ρ (kx x) (a : W)) = e ⟨ρ (kx x) (a : W), hmem⟩ := hEe ⟨ρ (kx x) (a : W), hmem⟩
    rw [h1]
    show TA ⟨ρ (kx x) (a : W), hmem⟩ (s (Quotient.mk R x)) = TA a x
    rw [hTA (kx x) a (s (Quotient.mk R x)), ← hkx x]

theorem archEntries_mul (K : Type) [Field K] (a h : GL (Fin 2) (InfiniteAdeleRing K)) (i j : Fin 2) :
    archEntries K (a * h) i j = ∑ k : Fin 2, archEntries K a i k * archEntries K h k j := by
  simp only [archEntries_apply, Units.val_mul, Matrix.mul_apply, map_sum, map_mul]

theorem isArchTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ} (hfa : IsArchTestFactor K fa)
    (a : GL (Fin 2) (InfiniteAdeleRing K)) : IsArchTestFactor K (fun h => fa (a * h)) := by
  obtain ⟨⟨Φ, hΦ, hfaΦ⟩, hsupp⟩ := hfa
  refine ⟨⟨fun X => Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * X k j), ?_, ?_⟩, ?_⟩
  · exact hΦ.comp (by fun_prop)
  · intro h
    show fa (a * h) = Φ (fun i j => ∑ k : Fin 2, archEntries K a i k * archEntries K h k j)
    rw [hfaΦ]
    congr 1
    funext i j
    exact archEntries_mul K a h i j
  · exact hsupp.comp_homeomorph (Homeomorph.mulLeft a)

theorem isFinTestFactor_comp_mul_left (K : Type) [Field K] [NumberField K]
    {ff : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K) → ℂ} (hff : IsFinTestFactor K ff)
    (b : GL (Fin 2) (FiniteAdeleRing (𝓞 K) K)) : IsFinTestFactor K (fun h => ff (b * h)) :=
  ⟨hff.1.comp_continuous (continuous_const_mul b), hff.2.comp_homeomorph (Homeomorph.mulLeft b)⟩

/-- A left translate by an inverse is again a factorizable test function. -/
theorem isFactorizableTestFn_comp_inv_mul_of_isFactorizableTestFn
    (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (hf : IsFactorizableTestFn K f)
    (t : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    IsFactorizableTestFn K (fun y => f (t⁻¹ * y)) := by
  obtain ⟨fa, ff, hfa, hff, hfx⟩ := hf
  refine ⟨fun h => fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * h),
    fun h => ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * h),
    isArchTestFactor_comp_mul_left K hfa _, isFinTestFactor_comp_mul_left K hff _, ?_⟩
  intro y
  show f (t⁻¹ * y) = fa (AdelicLevel.glArch (𝓞 K) K t⁻¹ * AdelicLevel.glArch (𝓞 K) K y) *
    ff (AdelicLevel.glFin (𝓞 K) K t⁻¹ * AdelicLevel.glFin (𝓞 K) K y)
  rw [hfx (t⁻¹ * y), map_mul (AdelicLevel.glArch (𝓞 K) K) t⁻¹ y,
    map_mul (AdelicLevel.glFin (𝓞 K) K) t⁻¹ y]

section SumMulCompMulMul

variable (F : Type) [Field F] [NumberField F]

theorem glFin_eq_one_of_mem_iSup_range {k : AdelicGL2 (𝓞 F) F}
    (hk : k ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) : glFin (𝓞 F) F k = 1 := by
  refine Subgroup.iSup_induction _ (C := fun k => glFin (𝓞 F) F k = 1) hk ?_ (map_one _) ?_
  · rintro w k ⟨k', rfl⟩
    exact glFin_rowIsometryInclAt₀ F w k'
  · intro a b ha hb
    rw [map_mul, ha, hb, mul_one]

def sandwich (A B : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) :
    (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (Fin 2 → Fin 2 → mixedEmbedding.mixedSpace F) where
  toFun m := fun p q => ∑ k : Fin 2, ∑ l : Fin 2,
    InfiniteAdeleRing.ringEquiv_mixedSpace F (A p k) * m k l * InfiniteAdeleRing.ringEquiv_mixedSpace F (B l q)
  map_add' m m' := by
    funext p q
    simp only [Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' r m := by
    funext p q
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

omit [NumberField F] in
theorem archEntries_mul_mul (A x B : GL (Fin 2) (InfiniteAdeleRing F)) :
    archEntries F (A * x * B) = sandwich F (A : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) B (archEntries F x) := by
  funext p q
  simp only [archEntries_apply, sandwich, LinearMap.coe_mk, AddHom.coe_mk, Units.val_mul, Matrix.mul_apply,
    Finset.sum_mul, map_sum, map_mul]
  rw [Finset.sum_comm]

theorem isFactorizableTestFn_sum_mul_translate_of_mem_iSup_range
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)
    (hb : ∀ i, b i ∈ ⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) := by
  obtain ⟨fa, ff, ⟨⟨Φ, hΦ, hfaΦ⟩, hfaS⟩, hffT, hfeq⟩ := hf
  have ha1 : ∀ i, glFin (𝓞 F) F (a i) = 1 := fun i => glFin_eq_one_of_mem_iSup_range F (ha i)
  have hb1 : ∀ i, glFin (𝓞 F) F (b i) = 1 := fun i => glFin_eq_one_of_mem_iSup_range F (hb i)
  have hfeq' : ∀ y, (∑ i, c i * f (a i * y * b i))
      = (fun x => ∑ i, c i * fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i))) (glArch (𝓞 F) F y)
        * ff (glFin (𝓞 F) F y) := by
    intro y
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfeq, map_mul, map_mul, map_mul, map_mul, ha1, hb1, one_mul, mul_one]
    ring
  refine ⟨fun x => ∑ i, c i * fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i)), ff,
    ⟨⟨fun m => ∑ i, c i * Φ ((sandwich F (glArch (𝓞 F) F (a i) : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F))
      (glArch (𝓞 F) F (b i))).toContinuousLinearMap m), ?_, fun x => ?_⟩, ?_⟩, hffT, hfeq'⟩
  · exact ContDiff.sum fun i _ => contDiff_const.mul (hΦ.comp (ContinuousLinearMap.contDiff _))
  · simp only [LinearMap.coe_toContinuousLinearMap']
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hfaΦ, archEntries_mul_mul]
  ·
    refine HasCompactSupport.intro
      (isCompact_iUnion fun i : Fin n => hfaS.image
        (show Continuous (fun z : GL (Fin 2) (InfiniteAdeleRing F) =>
            (glArch (𝓞 F) F (a i))⁻¹ * z * (glArch (𝓞 F) F (b i))⁻¹) from
          (continuous_const.mul continuous_id).mul continuous_const)) fun x hx => ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    have hz : fa (glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i)) = 0 := by
      by_contra hne
      apply hx
      refine Set.mem_iUnion.mpr ⟨i, glArch (𝓞 F) F (a i) * x * glArch (𝓞 F) F (b i),
        subset_tsupport _ (Function.mem_support.mpr hne), ?_⟩
      simp only [← mul_assoc, inv_mul_cancel, one_mul, mul_inv_cancel_right]
    rw [hz, mul_zero]

end SumMulCompMulMul

/-- A finite sum of double row-isometry translates of a factorizable test function is again
factorizable. -/
theorem isFactorizableTestFn_sum_mul_comp_mul_mul
    (F : Type) [Field F] [NumberField F]
    {f : AdelicGL2 (𝓞 F) F → ℂ} (hf : IsFactorizableTestFn F f) {n : ℕ} (c : Fin n → ℂ)
    (a b : Fin n → AdelicGL2 (𝓞 F) F)
    (ha : ∀ i, a i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range))
    (hb : ∀ i, b i ∈ (⨆ w : InfinitePlace F, (rowIsometryInclAt₀ F w).range)) :
    IsFactorizableTestFn F (fun y => ∑ i, c i * f (a i * y * b i)) :=
  isFactorizableTestFn_sum_mul_translate_of_mem_iSup_range F hf c a b ha hb

end AutomorphicForm

end
