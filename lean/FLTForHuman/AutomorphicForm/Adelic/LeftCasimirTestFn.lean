/-
  The left Casimir acting on factorizable test functions.

  Right convolution by a factorizable test function is the smoothing operator of the automorphic
  layer, and the archimedean Casimir `Ω` acts on the test function itself through the left flow
  derivative `L d γ y = deriv (fun t => γ (archFlowAt hw d (-t) * y)) 0`. This module carries the
  algebra of that action: `Ω α` is again factorizable and arch-bi-finite, right convolution by `Ω α`
  is the Casimir applied to the convolution, and the two memberships (the level-`N` invariants and
  the archimedean cut) are preserved — for the real place and for the complex one, where the complex
  Casimir is the four-term `H`/`iH`/`E`/`F⁻` combination and its conjugate `βb` is carried beside it.

  The third headline is the eigenvalue lemma the archimedean type theory consumes: an eigenvector of
  `rightConv · f` in the archimedean cut is an eigenvector of `rightConv · f'` for some *arch-bi-finite*
  factorizable `f'`.

  Transcribed from the pin's three `S_` files and their `Theorems/` wrappers (pinned `aa2d8b3`,
  472 + 651 + 412 lines).

  **Route.** The two place rows are the pin's prelude transcribed (`Ld`, `leftCasimir`/`leftCas`,
  the `Tens` tensor algebra, `Reg`, `OpPkg` and the two equivariance membership lemmas), with the
  port's `apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective` underneath the pin's
  `equivariant_mem_iSup_typeSubmodule`. The block the pin writes once per place (`rT` and its three
  laws, `rowIsometryInclAt₀_injective`, `rightConv_mem_levelInvariantSubmodule_of_left_inv`, the
  `Tens` algebra) is written once here, in `LeftCasimirShared`.

  The eigenvalue lemma does **not** replay the pin's 290-line `sandwich`: the port already carries the
  generic double-convolution identity `ArchApproxIdentity.integral_mul_dconvWith`
  (`RepTheory/ConvolutionLimit.lean`), so the headline is `ArchCutReproducer`'s reproducing kernel
  (`exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule`)
  + `ArchApproximation`'s kernel bi-finiteness row + that identity. The pin needed
  `set_option maxHeartbeats 3200000` for its `sandwich`; this route stays inside the default budget.

  The four `attribute [local instance]` lines below stand in for the pin's in-proof
  `letI`/`haveI := AdelicHaar.glBorel …` blocks, which the port's
  `linter.style.haveILetI` wants written as `let`/`have` in a proposition; no `set_option` disables it.

  **Wiring.** `spec/check_port.py` owns the declarations here.
  spec-pin: Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite.lean
  spec-pin: Theorems/Thm_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite.lean
  spec-pin: Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimir
import FLTForHuman.AutomorphicForm.Adelic.ArchCasimirComplex
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFn
import FLTForHuman.AutomorphicForm.Adelic.RightConvolution
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsGeneral
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConv
import FLTForHuman.AutomorphicForm.Adelic.ArchDerivRightConvComplex
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmooth
import FLTForHuman.AutomorphicForm.Adelic.FactorizableTestFnArchSmoothComplex
import FLTForHuman.AutomorphicForm.Adelic.ArchApproximation
import FLTForHuman.AutomorphicForm.Adelic.MaximalCompactFactors
import FLTForHuman.AutomorphicForm.Adelic.ArchCutReproducer
import FLTForHuman.AutomorphicForm.Adelic.ArchApproxIdentity.ArchInfra
import FLTForHuman.NumberTheory.AdelicLevel.Countability

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox
open AutomorphicForm MeasureTheory
open IsDedekindDomain Filter
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion
open AutomorphicForm.CuspidalConstituent
open scoped ENNReal Topology Classical ArchInfra

attribute [local instance] NumberField.AdelicHaar.glBorel NumberField.AdelicHaar.borelSpace_glBorel
attribute [local instance] NumberField.AdelicHaar.isHaarMeasure_adelicGLHaar
attribute [local instance] NumberField.AdelicHaar.isMulRightInvariant_adelicGLHaar

namespace AutomorphicForm

/-! ### Preblock shared by the two places

The pin writes this block once for each place (its `Ws23.H1` and `Ws26.CASLH`), and the two
copies are the same 43 lines: the right regular action `rT` of a row-isometry subgroup, the
equivariance lemma through which a right-equivariant operator preserves a supremum of type
submodules, and the three closure facts (`rT_mem_iSup_typeSubmodule`,
`rT_mem_span_range_rT`, `rowIsometryInclAt₀_injective`) plus the level-invariance of a right
convolution by a left-invariant test function. -/

namespace LeftCasimirShared

variable {H G : Type*} [Group H] [Group G]

/-- The right regular action of `H` on functions on `G`, along `ι : H →* G`. -/
def rT (ι : H →* G) (k : H) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun u x := u (x * ι k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rT_apply (ι : H →* G) (k : H) (u : G → ℂ) (x : G) : rT ι k u x = u (x * ι k) := rfl

theorem rT_mul (ι : H →* G) (h k : H) (u : G → ℂ) : rT ι h (rT ι k u) = rT ι (h * k) u := by
  funext x; simp [mul_assoc]

/-- A right-equivariant linear map preserves a supremum of type submodules. -/
theorem equivariant_mem_iSup_typeSubmodule {m : ℕ} {W : Fin m → Type*} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : ∀ i : Fin m, Representation ℂ H (W i))
    (V : Submodule ℂ (G → ℂ)) (hV : ∀ k : H, ∀ u ∈ V, rT ι k u ∈ V)
    (hVle : V ≤ ⨆ i, typeSubmodule ι (ρ i))
    (Ψ : V →ₗ[ℂ] (G → ℂ))
    (hΨ : ∀ (k : H) (u : V), Ψ ⟨rT ι k u, hV k u u.2⟩ = rT ι k (Ψ u)) (u : V) :
    Ψ u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  have h := AutomorphicForm.apply_mem_iSup_typeSubmodule_of_isRightEquivariant_of_injective ι ι hι V
    (fun k u hu => hV k u hu) Ψ (fun k u x => congrFun (hΨ k u) x) ρ (u : G → ℂ) u.2 (hVle u.2)
  simpa only [Subtype.coe_eta] using h

variable {K : Type} [Field K] [NumberField K]

theorem rowIsometryInclAt₀_injective (v : InfinitePlace K) : Function.Injective (rowIsometryInclAt₀ K v) := by
  intro a b h
  apply Subtype.ext
  have h1 := congrArg (fun x => archComponent K v (glArch (𝓞 K) K x)) h
  simpa only [rowIsometryInclAt₀_apply, adelicArchGLInclAt, MonoidHom.comp_apply, glArch_adelicArchGLIncl,
    archComponent_archGLIncl_self] using h1

theorem rT_mem_iSup_typeSubmodule {H G : Type*} [Group H] [Group G] {m : ℕ} {W : Fin m → Type*}
    [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)] (ι : H →* G)
    (ρ : ∀ i : Fin m, Representation ℂ H (W i)) {u : G → ℂ}
    (hu : u ∈ ⨆ i, typeSubmodule ι (ρ i)) (k : H) : rT ι k u ∈ ⨆ i, typeSubmodule ι (ρ i) := by
  have hle : (⨆ i, typeSubmodule ι (ρ i)).map (rT ι k) ≤ ⨆ i, typeSubmodule ι (ρ i) := by
    rw [Submodule.map_iSup]
    refine iSup_mono fun i => ?_
    rintro _ ⟨f, hf, rfl⟩
    exact comp_mul_mem_typeSubmodule hf k
  exact hle (Submodule.mem_map_of_mem hu)

theorem rT_mem_span_range_rT {H G : Type*} [Group H] [Group G] (ι : H →* G) (f : G → ℂ) (k : H) {u : G → ℂ}
    (hu : u ∈ Submodule.span ℂ (Set.range fun k : H => rT ι k f)) :
    rT ι k u ∈ Submodule.span ℂ (Set.range fun k : H => rT ι k f) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨k', rfl⟩
    rw [rT_mul]
    exact Submodule.subset_span ⟨k * k', rfl⟩
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro u v _ _ hu hv; rw [map_add]; exact Submodule.add_mem _ hu hv
  · intro c u _ hu; rw [map_smul]; exact Submodule.smul_mem _ c hu

/-- The pin's tensor predicate, shared by the two places: `γ` is a tensor of an archimedean test
factor with a fixed finite factor. -/
def Tens (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) (γ : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  ∃ fa : GL (Fin 2) (InfiniteAdeleRing K) → ℂ, IsArchTestFactor K fa ∧ ∀ y, γ y = fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)

/-- Right convolution by a left-invariant test function lands in the level invariant submodule. -/
theorem rightConv_mem_levelInvariantSubmodule_of_left_inv (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) :
    rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D
      (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N := by
  intro g u hu
  rw [AutomorphicForm.rightConv_apply_mul_eq_rightConv_comp_inv_mul_apply]
  have hfun : (fun y => β (u⁻¹ * y)) = β := funext fun y => hβU u⁻¹ (Subgroup.inv_mem _ hu) y
  rw [hfun]

theorem Tens.add {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {γ γ' : AdelicGL2 (𝓞 K) K → ℂ}
    (hγ : Tens ff γ) (hγ' : Tens ff γ') : Tens ff (fun y => γ y + γ' y) := by
  obtain ⟨fa, ⟨⟨Φ, hΦ, hfa⟩, hs⟩, h⟩ := hγ
  obtain ⟨fa', ⟨⟨Φ', hΦ', hfa'⟩, hs'⟩, h'⟩ := hγ'
  have hΦΦ' : ContDiff ℝ (⊤ : ℕ∞) (fun m => Φ m + Φ' m) := hΦ.add hΦ'
  refine ⟨fun z => fa z + fa' z, ⟨⟨fun m => Φ m + Φ' m, hΦΦ', fun z => ?_⟩, hs.add hs'⟩, fun y => ?_⟩
  · show fa z + fa' z = Φ (archEntries K z) + Φ' (archEntries K z)
    rw [hfa, hfa']
  · show γ y + γ' y = (fa (glArch (𝓞 K) K y) + fa' (glArch (𝓞 K) K y)) * ff (glFin (𝓞 K) K y)
    rw [h, h']; ring

theorem Tens.const_mul {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγ : Tens ff γ) (c : ℂ) : Tens ff (fun y => c * γ y) := by
  obtain ⟨fa, ⟨⟨Φ, hΦ, hfa⟩, hs⟩, h⟩ := hγ
  have hcΦ : ContDiff ℝ (⊤ : ℕ∞) (fun m => c * Φ m) := contDiff_const.mul hΦ
  refine ⟨fun z => c * fa z, ⟨⟨fun m => c * Φ m, hcΦ, fun z => ?_⟩, hs.mul_left⟩, fun y => ?_⟩
  · show c * fa z = c * Φ (archEntries K z)
    rw [hfa]
  · show c * γ y = c * fa (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y)
    rw [h]; ring

theorem Tens.zero (ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ) : Tens ff (fun _ => 0) :=
  ⟨fun _ => 0, isArchTestFactor_zero K, fun _ => by simp⟩

theorem Tens.sum {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {n : ℕ}
    {W : Fin n → (AdelicGL2 (𝓞 K) K → ℂ)} (hW : ∀ i, Tens ff (W i)) (c : Fin n → ℂ) :
    Tens ff (fun y => ∑ i, c i * W i y) := by
  induction n with
  | zero => simpa using Tens.zero ff
  | succ n ih =>
    have h := (Tens.const_mul (hW 0) (c 0)).add (ih (W := fun i => W i.succ) (fun i => hW i.succ) (fun i => c i.succ))
    refine (show (fun y => ∑ i, c i * W i y) = fun y => c 0 * W 0 y + ∑ i : Fin n, c i.succ * W i.succ y from ?_) ▸ h
    funext y; rw [Fin.sum_univ_succ]

theorem isFactorizableTestFn_of_tens {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ}
    (hff : IsFinTestFactor K ff) {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : Tens ff γ) : IsFactorizableTestFn K γ := by
  obtain ⟨fa, hfa, h⟩ := hγ
  exact ⟨fa, ff, hfa, hff, h⟩

end LeftCasimirShared

/-! ## The real place (pin `:472`) -/

namespace LeftCasimirReal

open MeasureTheory LeftCasimirShared

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

section RealPlace

variable (hw : w.IsReal)

/-- The pin's `Ld`: the left flow derivative. -/
def Ld (d : ArchDir) (γ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0

/-- The pin's real `leftCasimir`, the enveloping-algebra element acting by left translation. -/
def leftCasimir (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y)

/-- The left flow derivative of a factorizable test function is factorizable with the same finite
factor. -/
theorem isFactorizableTestFn_Ld {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : IsFactorizableTestFn K γ) (d : ArchDir) :
    IsFactorizableTestFn K (Ld hw d γ) := by
  obtain ⟨fa, ff, hfa, hff, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', ff, hfa', hff, fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

theorem Ld_left_inv {γ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1)
    (h : ∀ y, γ (k * y) = γ y) (d : ArchDir) (y : AdelicGL2 (𝓞 K) K) :
    Ld hw d γ (k * y) = Ld hw d γ y := by
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * (k * y))) 0 = deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
  congr 1
  funext t
  rw [← mul_assoc, archFlowAt_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc, h]

theorem leftCasimir_left_inv (N : Ideal (𝓞 K)) (α : AdelicGL2 (𝓞 K) K → ℂ)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K,
      leftCasimir hw α (k * y) = leftCasimir hw α y := by
  intro k hk y
  have hk1 : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2
  have hα' : ∀ y, α (k * y) = α y := fun y => (hαU y k hk).1
  have e1 : ∀ y, Ld hw .H α (k * y) = Ld hw .H α y := fun y => Ld_left_inv hw hk1 hα' .H y
  have e2 : ∀ y, Ld hw .H (Ld hw .H α) (k * y) = Ld hw .H (Ld hw .H α) y := fun y => Ld_left_inv hw hk1 e1 .H y
  have e3 : ∀ y, Ld hw .Fm α (k * y) = Ld hw .Fm α y := fun y => Ld_left_inv hw hk1 hα' .Fm y
  have e4 : ∀ y, Ld hw .E (Ld hw .Fm α) (k * y) = Ld hw .E (Ld hw .Fm α) y := fun y => Ld_left_inv hw hk1 e3 .E y
  show -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) (k * y) - (1 / 2 : ℂ) * Ld hw .H α (k * y) + Ld hw .E (Ld hw .Fm α) (k * y)) =
    -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y)
  rw [e1, e2, e4]

/-- Right convolution by the left Casimir is the Casimir of the three `L`-summands. -/
theorem rightConv_leftCasimir_eq (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' (leftCasimir hw α) = fun g => -((1 / 4 : ℂ) * rightConv K x' (Ld hw .H (Ld hw .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (Ld hw .H α) g + rightConv K x' (Ld hw .E (Ld hw .Fm α)) g) := by
  intro x' hx'
  have hfac1 : IsFactorizableTestFn K (Ld hw .H α) := isFactorizableTestFn_Ld hw hαf .H
  have hfac2 : IsFactorizableTestFn K (Ld hw .H (Ld hw .H α)) := isFactorizableTestFn_Ld hw hfac1 .H
  have hfac4 : IsFactorizableTestFn K (Ld hw .E (Ld hw .Fm α)) :=
    isFactorizableTestFn_Ld hw (isFactorizableTestFn_Ld hw hαf .Fm) .E
  have hint : ∀ {γ : AdelicGL2 (𝓞 K) K → ℂ}, IsFactorizableTestFn K γ → ∀ g : AdelicGL2 (𝓞 K) K,
      Integrable (fun y => x' (g * y) * γ y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro γ hγ g
    obtain ⟨hγc, hγs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K γ hγ
    exact ((hx'.comp (continuous_const.mul continuous_id)).mul hγc).integrable_of_hasCompactSupport hγs.mul_left
  funext g
  rw [rightConv_apply, rightConv_apply, rightConv_apply, rightConv_apply]
  have hfun : (fun y => x' (g * y) * leftCasimir hw α y) = fun y => -((1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y) -
      (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y) + x' (g * y) * Ld hw .E (Ld hw .Fm α) y) := by
    funext y
    show x' (g * y) * -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y) = _
    ring
  have hA : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hint hfac2 g).const_mul _
  have hB : Integrable (fun y => (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y)) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) :=
    (hint hfac1 g).const_mul _
  have hAB : Integrable (fun y => (1 / 4 : ℂ) * (x' (g * y) * Ld hw .H (Ld hw .H α) y) - (1 / 2 : ℂ) * (x' (g * y) * Ld hw .H α y))
      (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := hA.sub hB
  rw [hfun, integral_neg, integral_add hAB (hint hfac4 g), integral_sub hA hB, integral_const_mul, integral_const_mul]

theorem rightConv_mem_archCutSubmodule (tys : ArchTypeFamily K) (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβf : IsFactorizableTestFn K β) (hβb : IsArchBiFinite K tys β)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hx' : Continuous x') :
    rightConv K x' β ∈ archCutSubmodule K tys :=
  AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tys x' hx' β hβf hβb

theorem rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K))
    (tys : ArchTypeFamily K) (β : AdelicGL2 (𝓞 K) K → ℂ)
    (hβf : IsFactorizableTestFn K β) (hβb : IsArchBiFinite K tys β)
    (hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys :=
  fun x' hx' _ _ => Submodule.mem_inf.mpr
    ⟨rightConv_mem_levelInvariantSubmodule_of_left_inv D N β hβU x',
      rightConv_mem_archCutSubmodule tys β hβf hβb x' hx'⟩

theorem rightConv_leftCasimir_mem (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g)
    (hβf : IsFactorizableTestFn K (leftCasimir hw α)) (hβb : IsArchBiFinite K tys (leftCasimir hw α)) :
    ∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K)
        (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' (leftCasimir hw α) ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys :=
  rightConv_mem_levelInvariantSubmodule_inf_archCutSubmodule D N tys (leftCasimir hw α) hβf hβb
    (leftCasimir_left_inv hw N α hαU)

theorem tens_Ld {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγ : Tens ff γ) (d : ArchDir) : Tens ff (Ld hw d γ) := by
  obtain ⟨fa, hfa, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAt_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) =
      fun t : ℝ => fa (glArch (𝓞 K) K (archFlowAt hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAt hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

theorem isFactorizableTestFn_leftCasimir (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (leftCasimir hw α) := by
  classical
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hαf
  have hT0 : Tens ff α := ⟨fa, hfa, hαeq⟩
  obtain ⟨fa1, ⟨⟨Φ1, hΦ1, hfa1⟩, hs1⟩, h1⟩ := tens_Ld hw hT0 .H
  obtain ⟨fa2, ⟨⟨Φ2, hΦ2, hfa2⟩, hs2⟩, h2⟩ := tens_Ld hw (tens_Ld hw hT0 .H) .H
  obtain ⟨fa4, ⟨⟨Φ4, hΦ4, hfa4⟩, hs4⟩, h4⟩ := tens_Ld hw (tens_Ld hw hT0 .Fm) .E
  have hβeq : ∀ y, leftCasimir hw α y = (fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z)
      (glArch (𝓞 K) K y) * ff (glFin (𝓞 K) K y) := by
    intro y
    show -((1 / 4 : ℂ) * Ld hw .H (Ld hw .H α) y - (1 / 2 : ℂ) * Ld hw .H α y + Ld hw .E (Ld hw .Fm α) y) = _
    rw [h1, h2, h4]
    ring
  refine ⟨fun z => (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z, ff, ⟨⟨fun m => (-(1 / 4 : ℂ)) * Φ2 m +
    (1 / 2 : ℂ) * Φ1 m + (-1 : ℂ) * Φ4 m, ?_, fun z => ?_⟩, ?_⟩, hff, hβeq⟩
  · exact ((contDiff_const.mul hΦ2).add (contDiff_const.mul hΦ1)).add (contDiff_const.mul hΦ4)
  · show (-(1 / 4 : ℂ)) * fa2 z + (1 / 2 : ℂ) * fa1 z + (-1 : ℂ) * fa4 z = _
    rw [hfa2, hfa1, hfa4]
  · exact (hs2.mul_left.add hs1.mul_left).add hs4.mul_left

theorem leftCasimir_eq_archCasimirAt (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    leftCasimir hw α = archCasimirAt hw α :=
  funext (AutomorphicForm.leftCasimir_eq_archCasimirAt_of_isArchSmoothAt K w hw α
    (AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α hαf).1)

end RealPlace

/-! ### The two membership lemmas for the real Casimir, through the equivariance lemma -/

theorem comp_inv_archCasimirAt_mem_archCutSubmodule {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαs : IsArchSmoothAt hw α) (hα : (fun x => α x⁻¹) ∈ archCutSubmodule K tys) :
    (fun x => archCasimirAt hw α x⁻¹) ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : (fun x => α x⁻¹) ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set αc : AdelicGL2 (𝓞 K) K → ℂ := fun x => α x⁻¹ with hαc
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k αc) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι αc k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hSm : ∀ u ∈ V, IsArchSmoothAt hw (fun y => u y⁻¹) := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      have e : (fun y => (rT ι k αc) y⁻¹) = fun y => α ((ι k)⁻¹ * y) := by
        funext y
        simp only [rT_apply, hαc, _root_.mul_inv_rev, inv_inv]
      rw [e]
      exact hαs.comp_mul_left _
    · exact isArchSmoothAt_const hw 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u x => archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
      map_add' := fun u u' => by
        funext x
        show archCasimirAt hw (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
          archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹ +
            archCasimirAt hw (fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
            (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) + fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, archCasimirAt_add (hSm _ u.2) (hSm _ u'.2)]
        rfl
      map_smul' := fun c u => by
        funext x
        show archCasimirAt hw (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
          c • archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) = c • fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, archCasimirAt_smul]
        rfl }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    funext x
    show archCasimirAt hw (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
      archCasimirAt hw (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) (x * ι k)⁻¹
    have e : (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
        fun y => (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) ((ι k)⁻¹ * y) := by
      funext y
      simp only [rT_apply, _root_.mul_inv_rev, inv_inv]
    rw [e, _root_.mul_inv_rev]
    exact congrFun (archCasimirAt_comp_mul_left hw (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) (ι k)⁻¹) x⁻¹
  have hαcV : αc ∈ V := by
    have e : rT ι 1 αc = αc := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  have key := equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ)
    V hVstab hVle Ψ hΨ ⟨αc, hαcV⟩
  have e2 : (Ψ ⟨αc, hαcV⟩ : AdelicGL2 (𝓞 K) K → ℂ) = fun x => archCasimirAt hw α x⁻¹ := by
    funext x
    show archCasimirAt hw (fun y => αc y⁻¹) x⁻¹ = _
    have e : (fun y => αc y⁻¹) = α := funext fun y => by simp only [hαc, inv_inv]
    rw [e]
  rw [e2] at key
  exact key

/-- The pin's regularity predicate for the real archimedean derivations. -/
def Reg {w : InfinitePlace K} (hw : w.IsReal) (u : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Continuous u ∧ IsArchSmoothAt hw u ∧ (∀ d : ArchDir, Continuous (archDerivAt hw d u)) ∧
    ∀ d d' : ArchDir, Continuous (archDerivAt hw d (archDerivAt hw d' u))

theorem Reg.add {w : InfinitePlace K} {hw : w.IsReal} {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (hv : Reg hw v) :
    Reg hw (u + v) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAt_add hu.2.1 hv.2.1]
    exact (hu.2.2.1 d).add (hv.2.2.1 d)
  · rw [archDerivAt_add hu.2.1 hv.2.1, archDerivAt_add (hu.2.1.archDerivAt d') (hv.2.1.archDerivAt d')]
    exact (hu.2.2.2 d d').add (hv.2.2.2 d d')

theorem Reg.smul {w : InfinitePlace K} {hw : w.IsReal} {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (c : ℂ) :
    Reg hw (c • u) := by
  refine ⟨hu.1.const_smul c, hu.2.1.smul c, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAt_smul]
    exact (hu.2.2.1 d).const_smul c
  · rw [archDerivAt_smul, archDerivAt_smul]
    exact (hu.2.2.2 d d').const_smul c

theorem reg_of_isFactorizableTestFn {w : InfinitePlace K} (hw : w.IsReal) {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : IsFactorizableTestFn K α) : Reg hw α := by
  have hT := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw α hα
  obtain ⟨hαs, fa, ff, hfa, hff, hαeq, hder⟩ := hT
  have hD : ∀ d : ArchDir, IsFactorizableTestFn K (archDerivAt hw d α) := by
    intro d
    obtain ⟨fa', hfa', h⟩ := hder d
    exact ⟨fa', ff, hfa', hff, h⟩
  refine ⟨(AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα).1, hαs,
    fun d => (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hD d)).1, fun d d' => ?_⟩
  have hT' := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAt_and_archDerivAt_eq_tensor K w hw _ (hD d')
  obtain ⟨_, fa1, ff1, hfa1, hff1, h1eq, hder1⟩ := hT'
  obtain ⟨fa'', hfa'', h⟩ := hder1 d
  exact (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ ⟨fa'', ff1, hfa'', hff1, h⟩).1

theorem rowIsometryInclAt₀_eq_archRealGLAt {w : InfinitePlace K} (hw : w.IsReal) (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ K w k =
      archRealGLAt hw ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) w.Completion)) := by
  rw [rowIsometryInclAt₀_apply]
  show adelicArchGLInclAt K w (k : GL (Fin 2) w.Completion) =
    adelicArchGLInclAt K w ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).toMonoidHom
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) w.Completion)))
  rw [MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]

theorem reg_rT_and_archCasimirAt_rT {w : InfinitePlace K} (hw : w.IsReal) (v : InfinitePlace K)
    (k : rowIsometrySubgroup₀ v.Completion) {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) :
    Reg hw (rT (rowIsometryInclAt₀ K v) k u) ∧
      archCasimirAt hw (rT (rowIsometryInclAt₀ K v) k u) = rT (rowIsometryInclAt₀ K v) k (archCasimirAt hw u) := by
  obtain ⟨huc, hus, hD1, hD2⟩ := hu
  have hcont : Continuous (rT (rowIsometryInclAt₀ K v) k u) := huc.comp (continuous_mul_const _)
  by_cases hvw : v = w
  · subst hvw
    have h := AutomorphicForm.archCasimirAt_rightTranslate_archRealGLAt K v hw u huc hus hD1 hD2
      ((glEquivOfRingEquiv (ringEquivRealOfIsReal hw).symm).symm (k : GL (Fin 2) v.Completion))
    rw [← rowIsometryInclAt₀_eq_archRealGLAt hw k] at h
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩
  · have h := AutomorphicForm.archCasimirAt_rightTranslate_rowIsometryInclAt_of_ne K w hw u huc hus hD1 hD2 v hvw k
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2⟩

theorem archCasimirAt_mem_archDualCutSubmodule {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαr : Reg hw α) (hα : α ∈ archDualCutSubmodule K tys) :
    archCasimirAt hw α ∈ archDualCutSubmodule K tys := by
  rw [mem_archDualCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : α ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ.dual := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k α) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι α k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ.dual :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hReg : ∀ u ∈ V, Reg hw u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      exact (reg_rT_and_archCasimirAt_rT hw v k hαr).1
    · have e : (0 : AdelicGL2 (𝓞 K) K → ℂ) = (0 : ℂ) • α := by simp
      rw [e]
      exact hαr.smul 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u => archCasimirAt hw (u : AdelicGL2 (𝓞 K) K → ℂ)
      map_add' := fun u u' => by rw [Submodule.coe_add]; exact archCasimirAt_add (hReg _ u.2).2.1 (hReg _ u'.2).2.1
      map_smul' := fun c u => by rw [RingHom.id_apply, Submodule.coe_smul, archCasimirAt_smul] }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    exact (reg_rT_and_archCasimirAt_rT hw v k (hReg _ u.2)).2
  have hαV : α ∈ V := by
    have e : rT ι 1 α = α := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  exact equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ.dual)
    V hVstab hVle Ψ hΨ ⟨α, hαV⟩

theorem isArchBiFinite_archCasimirAt {w : InfinitePlace K} (hw : w.IsReal) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α) :
    IsArchBiFinite K tys (archCasimirAt hw α) :=
  ⟨comp_inv_archCasimirAt_mem_archCutSubmodule hw tys α (reg_of_isFactorizableTestFn hw hαf).2.1 hαb.1,
    archCasimirAt_mem_archDualCutSubmodule hw tys α (reg_of_isFactorizableTestFn hw hαf) hαb.2⟩

end LeftCasimirReal

theorem isFactorizableTestFn_leftCasimir_and_rightConv_mem_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsReal)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDir → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAt hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ :=
      fun y => -((1 / 4 : ℂ) * L .H (L .H α) y - (1 / 2 : ℂ) * L .H α y + L .E (L .Fm α) y)
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      rightConv K x' β = fun g => -((1 / 4 : ℂ) * rightConv K x' (L .H (L .H α)) g
        - (1 / 2 : ℂ) * rightConv K x' (L .H α) g + rightConv K x' (L .E (L .Fm α)) g)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys)
    := by
  intro L β
  have hβf : IsFactorizableTestFn K β := LeftCasimirReal.isFactorizableTestFn_leftCasimir hw α hαf
  have hβb : IsArchBiFinite K tys β := by
    show IsArchBiFinite K tys (LeftCasimirReal.leftCasimir hw α)
    rw [LeftCasimirReal.leftCasimir_eq_archCasimirAt hw α hαf]
    exact LeftCasimirReal.isArchBiFinite_archCasimirAt hw tys α hαf hαb
  exact ⟨⟨hβf, hβb⟩, LeftCasimirReal.rightConv_leftCasimir_eq hw α hαf,
    LeftCasimirReal.rightConv_leftCasimir_mem hw D N tys α hαU hβf hβb⟩

/-! ## The complex place (pin `:651`) — the real block's mirror with the conjugate `βb` -/

namespace LeftCasimirComplex

open MeasureTheory LeftCasimirShared
open scoped Classical

variable {K : Type} [Field K] [NumberField K] {w : InfinitePlace K}

variable (hw : w.IsComplex)

/-- The complex left flow derivative. -/
def Ld (d : ArchDirComplex) (γ : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ :=
  fun y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0

/-- The pin's complex `leftCasimir`, the four-term `H`/`iH`/`E`/`iF⁻` combination. -/
def leftCas (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
  -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H (α)) y + ((-Complex.I) : ℂ) * Ld hw .H (Ld hw .iH (α)) y + ((-Complex.I) : ℂ) * Ld hw .iH (Ld hw .H (α)) y + (-1 : ℂ) * Ld hw .iH (Ld hw .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H (α) y + ((-Complex.I) : ℂ) * Ld hw .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm (α)) y + ((-Complex.I) : ℂ) * Ld hw .E (Ld hw .iFm (α)) y + ((-Complex.I) : ℂ) * Ld hw .iE (Ld hw .Fm (α)) y + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm (α)) y))

/-- Its conjugate `leftCasBar`, the same with `+i` in place of `−i`. -/
def leftCasBar (α : AdelicGL2 (𝓞 K) K → ℂ) : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
  -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .H (Ld hw .H (α)) y + (Complex.I : ℂ) * Ld hw .H (Ld hw .iH (α)) y + (Complex.I : ℂ) * Ld hw .iH (Ld hw .H (α)) y + (-1 : ℂ) * Ld hw .iH (Ld hw .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * Ld hw .H (α) y + (Complex.I : ℂ) * Ld hw .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * Ld hw .E (Ld hw .Fm (α)) y + (Complex.I : ℂ) * Ld hw .E (Ld hw .iFm (α)) y + (Complex.I : ℂ) * Ld hw .iE (Ld hw .Fm (α)) y + (-1 : ℂ) * Ld hw .iE (Ld hw .iFm (α)) y))

/-- The ten `L`-summands of the complex Casimir. -/
def W10 (α : AdelicGL2 (𝓞 K) K → ℂ) : Fin 10 → (AdelicGL2 (𝓞 K) K → ℂ) :=
  ![Ld hw .H (Ld hw .H α), Ld hw .H (Ld hw .iH α), Ld hw .iH (Ld hw .H α), Ld hw .iH (Ld hw .iH α),
    Ld hw .H α, Ld hw .iH α,
    Ld hw .E (Ld hw .Fm α), Ld hw .E (Ld hw .iFm α), Ld hw .iE (Ld hw .Fm α), Ld hw .iE (Ld hw .iFm α)]

/-- The ten coefficients of `leftCas`. -/
def c10 : Fin 10 → ℂ :=
  ![-(1 / 4) * (1 / 4), -(1 / 4) * (1 / 4) * (-Complex.I), -(1 / 4) * (1 / 4) * (-Complex.I), -(1 / 4) * (1 / 4) * (-1),
    (1 / 2) * (1 / 2), (1 / 2) * (1 / 2) * (-Complex.I),
    -(1 / 4), -(1 / 4) * (-Complex.I), -(1 / 4) * (-Complex.I), -(1 / 4) * (-1)]

/-- The ten coefficients of `leftCasBar`. -/
def c10b : Fin 10 → ℂ :=
  ![-(1 / 4) * (1 / 4), -(1 / 4) * (1 / 4) * Complex.I, -(1 / 4) * (1 / 4) * Complex.I, -(1 / 4) * (1 / 4) * (-1),
    (1 / 2) * (1 / 2), (1 / 2) * (1 / 2) * Complex.I,
    -(1 / 4), -(1 / 4) * Complex.I, -(1 / 4) * Complex.I, -(1 / 4) * (-1)]

theorem leftCas_eq_sum (α : AdelicGL2 (𝓞 K) K → ℂ) :
    leftCas hw α = fun y => ∑ i, c10 i * W10 hw α i y := by
  funext y
  simp only [leftCas, W10, c10, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem leftCasBar_eq_sum (α : AdelicGL2 (𝓞 K) K → ℂ) :
    leftCasBar hw α = fun y => ∑ i, c10b i * W10 hw α i y := by
  funext y
  simp only [leftCasBar, W10, c10b, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

theorem tens_Ld {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {γ : AdelicGL2 (𝓞 K) K → ℂ}
    (hγ : Tens ff γ) (d : ArchDirComplex) : Tens ff (Ld hw d γ) := by
  obtain ⟨fa, hfa, hγeq⟩ := hγ
  obtain ⟨fa', hfa', heq⟩ :=
    (AutomorphicForm.archDerivAtComplex_rightConv_eq_rightConv_deriv_of_isFactorizableTestFn K hw d).2.1 fa ff hfa
  refine ⟨fa', hfa', fun y => ?_⟩
  have hfun : (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) = fun t : ℝ =>
      fa (glArch (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) * ff (glFin (𝓞 K) K (archFlowAtComplex hw d (-t) * y)) := by
    funext t; exact hγeq _
  show deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0 = _
  rw [hfun]
  exact congrFun heq y

theorem isFactorizableTestFn_Ld {γ : AdelicGL2 (𝓞 K) K → ℂ} (hγ : IsFactorizableTestFn K γ) (d : ArchDirComplex) :
    IsFactorizableTestFn K (Ld hw d γ) := by
  obtain ⟨fa, ff, hfa, hff, hγeq⟩ := hγ
  exact isFactorizableTestFn_of_tens hff (tens_Ld hw ⟨fa, hfa, hγeq⟩ d)

/-- Every list of complex directions applied to a factorizable test function stays factorizable. -/
theorem isFactorizableTestFn_foldr {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    ∀ l : List ArchDirComplex, IsFactorizableTestFn K (l.foldr (Ld hw) α)
  | [] => hα
  | d :: l => isFactorizableTestFn_Ld hw (isFactorizableTestFn_foldr hα l) d

theorem tens_W10 {ff : GL (Fin 2) (IsDedekindDomain.FiniteAdeleRing (𝓞 K) K) → ℂ} {α : AdelicGL2 (𝓞 K) K → ℂ}
    (hα : Tens ff α) : ∀ i, Tens ff (W10 hw α i) := by
  intro i
  fin_cases i <;>
    simp only [W10] <;>
    first
      | exact tens_Ld hw (tens_Ld hw hα _) _
      | exact tens_Ld hw hα _

theorem isFactorizableTestFn_W10 {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    ∀ i, IsFactorizableTestFn K (W10 hw α i) := by
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hα
  exact fun i => isFactorizableTestFn_of_tens hff (tens_W10 hw ⟨fa, hfa, hαeq⟩ i)

theorem isFactorizableTestFn_leftCas {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) :
    IsFactorizableTestFn K (leftCas hw α) ∧ IsFactorizableTestFn K (leftCasBar hw α) := by
  obtain ⟨fa, ff, hfa, hff, hαeq⟩ := hα
  have hT : Tens ff α := ⟨fa, hfa, hαeq⟩
  refine ⟨?_, ?_⟩
  · rw [leftCas_eq_sum]; exact isFactorizableTestFn_of_tens hff (Tens.sum (tens_W10 hw hT) c10)
  · rw [leftCasBar_eq_sum]; exact isFactorizableTestFn_of_tens hff (Tens.sum (tens_W10 hw hT) c10b)

theorem rightConv_sum (x' : AdelicGL2 (𝓞 K) K → ℂ) (hx' : Continuous x') {n : ℕ}
    {W : Fin n → (AdelicGL2 (𝓞 K) K → ℂ)} (hW : ∀ i, IsFactorizableTestFn K (W i)) (c : Fin n → ℂ) :
    rightConv K x' (fun y => ∑ i, c i * W i y) = fun g => ∑ i, c i * rightConv K x' (W i) g := by
  have hint : ∀ i (g : AdelicGL2 (𝓞 K) K),
      Integrable (fun y => x' (g * y) * W i y) (AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K) := by
    intro i g
    obtain ⟨hγc, hγs⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hW i)
    exact ((hx'.comp (continuous_const.mul continuous_id)).mul hγc).integrable_of_hasCompactSupport hγs.mul_left
  funext g
  rw [rightConv_apply]
  have hfun : (fun y => x' (g * y) * ∑ i, c i * W i y) = fun y => ∑ i, c i * (x' (g * y) * W i y) := by
    funext y; rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  rw [hfun, integral_finsetSum _ fun i _ => (hint i g).const_mul (c i)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, rightConv_apply]

theorem Ld_left_inv {γ : AdelicGL2 (𝓞 K) K → ℂ} {k : AdelicGL2 (𝓞 K) K} (hk : glArch (𝓞 K) K k = 1)
    (h : ∀ y, γ (k * y) = γ y) (d : ArchDirComplex) (y : AdelicGL2 (𝓞 K) K) : Ld hw d γ (k * y) = Ld hw d γ y := by
  show deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * (k * y))) 0 =
    deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
  congr 1
  funext t
  rw [← mul_assoc, archFlowAtComplex_mul_comm_of_glArch_eq_one hw d (-t) hk, mul_assoc, h]

theorem leftCas_left_inv (N : Ideal (𝓞 K)) (α : AdelicGL2 (𝓞 K) K → ℂ)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      α (k * g) = α g ∧ α (g * k) = α g) :
    (∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K,
      leftCas hw α (k * y) = leftCas hw α y) ∧
    (∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K,
      leftCasBar hw α (k * y) = leftCasBar hw α y) := by
  have key : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K),
      (∀ d y, Ld hw d α (k * y) = Ld hw d α y) ∧ (∀ d d' y, Ld hw d (Ld hw d' α) (k * y) = Ld hw d (Ld hw d' α) y) := by
    intro k hk
    have hk1 : glArch (𝓞 K) K k = 1 := (mem_finiteAdelicGL2Subgroup_iff K k).mp (Subgroup.mem_inf.mp hk).2
    have hα' : ∀ y, α (k * y) = α y := fun y => (hαU y k hk).1
    have h1 : ∀ d y, Ld hw d α (k * y) = Ld hw d α y := fun d y => Ld_left_inv hw hk1 hα' d y
    exact ⟨h1, fun d d' y => Ld_left_inv hw hk1 (h1 d') d y⟩
  refine ⟨fun k hk y => ?_, fun k hk y => ?_⟩
  · obtain ⟨h1, h2⟩ := key k hk
    simp only [leftCas, h1, h2]
  · obtain ⟨h1, h2⟩ := key k hk
    simp only [leftCasBar, h1, h2]

theorem rightConv_mem_inf (D : Set (AdelicGL2 (𝓞 K) K)) (N : Ideal (𝓞 K)) (tys : ArchTypeFamily K)
    (β : AdelicGL2 (𝓞 K) K → ℂ) (hβf : IsFactorizableTestFn K β) (hβb : IsArchBiFinite K tys β)
    (hβU : ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), ∀ y : AdelicGL2 (𝓞 K) K, β (k * y) = β y)
    (x' : AdelicGL2 (𝓞 K) K → ℂ) (hx' : Continuous x') :
    rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓
        archCutSubmodule K tys :=
  Submodule.mem_inf.mpr ⟨rightConv_mem_levelInvariantSubmodule_of_left_inv D N β hβU x',
    AutomorphicForm.rightConv_mem_archCutSubmodule_of_isArchBiFinite K tys x' hx' β hβf hβb⟩

/-! ### The operator algebra of the two complex Casimirs -/

theorem archDelAt_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDir) :
    archDelAt hw d (φ + ψ) = archDelAt hw d φ + archDelAt hw d ψ := by
  unfold archDelAt
  rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem archDelBarAt_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDir) :
    archDelBarAt hw d (φ + ψ) = archDelBarAt hw d φ + archDelBarAt hw d ψ := by
  unfold archDelBarAt
  rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

theorem archDelAt_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (d : ArchDir) :
    archDelAt hw d (c • φ) = c • archDelAt hw d φ := by
  unfold archDelAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul]
  funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]; ring

theorem archDelBarAt_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) (d : ArchDir) :
    archDelBarAt hw d (c • φ) = c • archDelBarAt hw d φ := by
  unfold archDelBarAt
  rw [archDerivAtComplex_smul, archDerivAtComplex_smul]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]; ring

theorem archCasimirAtComplex_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) :
    archCasimirAtComplex hw (φ + ψ) = archCasimirAtComplex hw φ + archCasimirAtComplex hw ψ := by
  unfold archCasimirAtComplex
  rw [archDelAt_add' hw hφ hψ .H, archDelAt_add' hw (hφ.archDelAt .H) (hψ.archDelAt .H) .H,
    archDelAt_add' hw hφ hψ .Fm, archDelAt_add' hw (hφ.archDelAt .Fm) (hψ.archDelAt .Fm) .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]; ring

theorem archCasimirBarAtComplex_add' {φ ψ : AdelicGL2 (𝓞 K) K → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) :
    archCasimirBarAtComplex hw (φ + ψ) = archCasimirBarAtComplex hw φ + archCasimirBarAtComplex hw ψ := by
  unfold archCasimirBarAtComplex
  rw [archDelBarAt_add' hw hφ hψ .H, archDelBarAt_add' hw (hφ.archDelBarAt .H) (hψ.archDelBarAt .H) .H,
    archDelBarAt_add' hw hφ hψ .Fm, archDelBarAt_add' hw (hφ.archDelBarAt .Fm) (hψ.archDelBarAt .Fm) .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]; ring

theorem archCasimirAtComplex_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archCasimirAtComplex hw (c • φ) = c • archCasimirAtComplex hw φ := by
  unfold archCasimirAtComplex
  rw [archDelAt_smul' hw c φ .H, archDelAt_smul' hw c _ .H, archDelAt_smul' hw c φ .Fm, archDelAt_smul' hw c _ .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]; ring

theorem archCasimirBarAtComplex_smul' (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ) :
    archCasimirBarAtComplex hw (c • φ) = c • archCasimirBarAtComplex hw φ := by
  unfold archCasimirBarAtComplex
  rw [archDelBarAt_smul' hw c φ .H, archDelBarAt_smul' hw c _ .H, archDelBarAt_smul' hw c φ .Fm,
    archDelBarAt_smul' hw c _ .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]; ring

theorem archDelAt_comp_mul_left' (d : ArchDir) (φ : AdelicGL2 (𝓞 K) K → ℂ) (a : AdelicGL2 (𝓞 K) K) :
    archDelAt hw d (fun x => φ (a * x)) = fun x => archDelAt hw d φ (a * x) := by
  unfold archDelAt
  rw [archDerivAtComplex_comp_mul_left, archDerivAtComplex_comp_mul_left]
  funext x; simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

theorem archDelBarAt_comp_mul_left' (d : ArchDir) (φ : AdelicGL2 (𝓞 K) K → ℂ) (a : AdelicGL2 (𝓞 K) K) :
    archDelBarAt hw d (fun x => φ (a * x)) = fun x => archDelBarAt hw d φ (a * x) := by
  unfold archDelBarAt
  rw [archDerivAtComplex_comp_mul_left, archDerivAtComplex_comp_mul_left]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]

theorem archCasimirAtComplex_comp_mul_left' (φ : AdelicGL2 (𝓞 K) K → ℂ) (a : AdelicGL2 (𝓞 K) K) :
    archCasimirAtComplex hw (fun x => φ (a * x)) = fun x => archCasimirAtComplex hw φ (a * x) := by
  unfold archCasimirAtComplex
  rw [archDelAt_comp_mul_left' hw .H φ, archDelAt_comp_mul_left' hw .H, archDelAt_comp_mul_left' hw .Fm φ,
    archDelAt_comp_mul_left' hw .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]

theorem archCasimirBarAtComplex_comp_mul_left' (φ : AdelicGL2 (𝓞 K) K → ℂ) (a : AdelicGL2 (𝓞 K) K) :
    archCasimirBarAtComplex hw (fun x => φ (a * x)) = fun x => archCasimirBarAtComplex hw φ (a * x) := by
  unfold archCasimirBarAtComplex
  rw [archDelBarAt_comp_mul_left' hw .H φ, archDelBarAt_comp_mul_left' hw .H, archDelBarAt_comp_mul_left' hw .Fm φ,
    archDelBarAt_comp_mul_left' hw .E]
  funext x; simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, smul_eq_mul]

/-- The pin's complex regularity predicate. -/
def Reg (u : AdelicGL2 (𝓞 K) K → ℂ) : Prop :=
  Continuous u ∧ IsArchSmoothAtComplex hw u ∧ (∀ d : ArchDirComplex, Continuous (archDerivAtComplex hw d u)) ∧
    ∀ d d' : ArchDirComplex, Continuous (archDerivAtComplex hw d (archDerivAtComplex hw d' u))

variable {hw} in
theorem Reg.add {u v : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (hv : Reg hw v) : Reg hw (u + v) := by
  refine ⟨hu.1.add hv.1, hu.2.1.add hv.2.1, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAtComplex_add hu.2.1 hv.2.1]
    exact (hu.2.2.1 d).add (hv.2.2.1 d)
  · rw [archDerivAtComplex_add hu.2.1 hv.2.1,
      archDerivAtComplex_add (hu.2.1.archDerivAtComplex d') (hv.2.1.archDerivAtComplex d')]
    exact (hu.2.2.2 d d').add (hv.2.2.2 d d')

variable {hw} in
theorem Reg.smul {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) (c : ℂ) : Reg hw (c • u) := by
  refine ⟨hu.1.const_smul c, hu.2.1.smul c, fun d => ?_, fun d d' => ?_⟩
  · rw [archDerivAtComplex_smul]
    exact (hu.2.2.1 d).const_smul c
  · rw [archDerivAtComplex_smul, archDerivAtComplex_smul]
    exact (hu.2.2.2 d d').const_smul c

theorem reg_of_isFactorizableTestFn {α : AdelicGL2 (𝓞 K) K → ℂ} (hα : IsFactorizableTestFn K α) : Reg hw α := by
  have hT := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor K w hw α hα
  obtain ⟨hαs, fa, ff, hfa, hff, hαeq, hder⟩ := hT
  have hD : ∀ d : ArchDirComplex, IsFactorizableTestFn K (archDerivAtComplex hw d α) := by
    intro d
    obtain ⟨fa', hfa', h⟩ := hder d
    exact ⟨fa', ff, hfa', hff, h⟩
  refine ⟨(AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K α hα).1, hαs,
    fun d => (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ (hD d)).1, fun d d' => ?_⟩
  have hT' := AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor K w hw _ (hD d')
  obtain ⟨_, fa1, ff1, hfa1, hff1, h1eq, hder1⟩ := hT'
  obtain ⟨fa'', hfa'', h⟩ := hder1 d
  exact (AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn K _ ⟨fa'', ff1, hfa'', hff1, h⟩).1

theorem rowIsometryInclAt₀_eq_archComplexGLAt (k : rowIsometrySubgroup₀ w.Completion) :
    rowIsometryInclAt₀ K w k =
      archComplexGLAt hw (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) w.Completion)) := by
  rw [rowIsometryInclAt₀_apply, archComplexGLAt_glEquivOfRingEquiv]

/-- A package of the four laws an archimedean operator obeys so that it preserves the complex
Casimir's two memberships. -/
structure OpPkg (Op : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)) : Prop where
  add : ∀ {φ ψ : AdelicGL2 (𝓞 K) K → ℂ}, IsArchSmoothAtComplex hw φ → IsArchSmoothAtComplex hw ψ →
    Op (φ + ψ) = Op φ + Op ψ
  smul : ∀ (c : ℂ) (φ : AdelicGL2 (𝓞 K) K → ℂ), Op (c • φ) = c • Op φ
  comp_mul_left : ∀ (φ : AdelicGL2 (𝓞 K) K → ℂ) (a : AdelicGL2 (𝓞 K) K), Op (fun x => φ (a * x)) = fun x => Op φ (a * x)
  rT : ∀ (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion) {u : AdelicGL2 (𝓞 K) K → ℂ}, Reg hw u →
    Reg hw (rT (rowIsometryInclAt₀ K v) k u) ∧ Op (rT (rowIsometryInclAt₀ K v) k u) = rT (rowIsometryInclAt₀ K v) k (Op u)

theorem reg_rT_and_comm (v : InfinitePlace K) (k : rowIsometrySubgroup₀ v.Completion)
    {u : AdelicGL2 (𝓞 K) K → ℂ} (hu : Reg hw u) :
    Reg hw (rT (rowIsometryInclAt₀ K v) k u) ∧
      archCasimirAtComplex hw (rT (rowIsometryInclAt₀ K v) k u) = rT (rowIsometryInclAt₀ K v) k (archCasimirAtComplex hw u) ∧
      archCasimirBarAtComplex hw (rT (rowIsometryInclAt₀ K v) k u) =
        rT (rowIsometryInclAt₀ K v) k (archCasimirBarAtComplex hw u) := by
  obtain ⟨huc, hus, hD1, hD2⟩ := hu
  have hcont : Continuous (rT (rowIsometryInclAt₀ K v) k u) := huc.comp (continuous_mul_const _)
  by_cases hvw : v = w
  · subst hvw
    have h := AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt K v hw u huc hus hD1 hD2
      (glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw) (k : GL (Fin 2) v.Completion))
    rw [← rowIsometryInclAt₀_eq_archComplexGLAt hw k] at h
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩
  · have h := AutomorphicForm.archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne K w hw u huc hus hD1 hD2 v hvw k
    exact ⟨⟨hcont, h.1, h.2.1, h.2.2.1⟩, h.2.2.2.1, h.2.2.2.2⟩

theorem opPkg_casimir : OpPkg hw (archCasimirAtComplex hw) where
  add := fun hφ hψ => archCasimirAtComplex_add' hw hφ hψ
  smul := archCasimirAtComplex_smul' hw
  comp_mul_left := archCasimirAtComplex_comp_mul_left' hw
  rT := fun v k _ hu => ⟨(reg_rT_and_comm hw v k hu).1, (reg_rT_and_comm hw v k hu).2.1⟩

theorem opPkg_casimirBar : OpPkg hw (archCasimirBarAtComplex hw) where
  add := fun hφ hψ => archCasimirBarAtComplex_add' hw hφ hψ
  smul := archCasimirBarAtComplex_smul' hw
  comp_mul_left := archCasimirBarAtComplex_comp_mul_left' hw
  rT := fun v k _ hu => ⟨(reg_rT_and_comm hw v k hu).1, (reg_rT_and_comm hw v k hu).2.2⟩

theorem comp_inv_op_mem_archCutSubmodule {Op : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)}
    (hOp : OpPkg hw Op) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαs : IsArchSmoothAtComplex hw α) (hα : (fun x => α x⁻¹) ∈ archCutSubmodule K tys) :
    (fun x => Op α x⁻¹) ∈ archCutSubmodule K tys := by
  rw [mem_archCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : (fun x => α x⁻¹) ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set αc : AdelicGL2 (𝓞 K) K → ℂ := fun x => α x⁻¹ with hαc
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k αc) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι αc k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hSm : ∀ u ∈ V, IsArchSmoothAtComplex hw (fun y => u y⁻¹) := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      have e : (fun y => (rT ι k αc) y⁻¹) = fun y => α ((ι k)⁻¹ * y) := by
        funext y
        simp only [rT_apply, hαc, _root_.mul_inv_rev, inv_inv]
      rw [e]
      exact hαs.comp_mul_left _
    · exact isArchSmoothAtComplex_const hw 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u x => Op (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
      map_add' := fun u u' => by
        funext x
        show Op (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
          Op (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹ + Op (fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => ((u : AdelicGL2 (𝓞 K) K → ℂ) + (u' : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
            (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) + fun y => (u' : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, hOp.add (hSm _ u.2) (hSm _ u'.2)]
        rfl
      map_smul' := fun c u => by
        funext x
        show Op (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ = c • Op (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) x⁻¹
        have e : (fun y => (c • (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) = c • fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹ := rfl
        rw [e, hOp.smul]
        rfl }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    funext x
    show Op (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) x⁻¹ =
      Op (fun y => (u : AdelicGL2 (𝓞 K) K → ℂ) y⁻¹) (x * ι k)⁻¹
    have e : (fun y => (rT ι k (u : AdelicGL2 (𝓞 K) K → ℂ)) y⁻¹) =
        fun y => (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) ((ι k)⁻¹ * y) := by
      funext y
      simp only [rT_apply, _root_.mul_inv_rev, inv_inv]
    rw [e, _root_.mul_inv_rev]
    exact congrFun (hOp.comp_mul_left (fun z => (u : AdelicGL2 (𝓞 K) K → ℂ) z⁻¹) (ι k)⁻¹) x⁻¹
  have hαcV : αc ∈ V := by
    have e : rT ι 1 αc = αc := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  have key := equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ)
    V hVstab hVle Ψ hΨ ⟨αc, hαcV⟩
  have e2 : (Ψ ⟨αc, hαcV⟩ : AdelicGL2 (𝓞 K) K → ℂ) = fun x => Op α x⁻¹ := by
    funext x
    show Op (fun y => αc y⁻¹) x⁻¹ = _
    have e : (fun y => αc y⁻¹) = α := funext fun y => by simp only [hαc, inv_inv]
    rw [e]
  rw [e2] at key
  exact key

theorem op_mem_archDualCutSubmodule {Op : (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ)}
    (hOp : OpPkg hw Op) (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαr : Reg hw α) (hα : α ∈ archDualCutSubmodule K tys) :
    Op α ∈ archDualCutSubmodule K tys := by
  rw [mem_archDualCutSubmodule_iff] at hα ⊢
  intro v
  have hαv : α ∈ ⨆ i, typeSubmodule (rowIsometryInclAt₀ K v) (tys.rep v i).ρ.dual := hα v
  set ι := rowIsometryInclAt₀ K v with hι
  set V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ) :=
    Submodule.span ℂ (Set.range fun k : rowIsometrySubgroup₀ v.Completion => rT ι k α) with hVdef
  have hVstab : ∀ k : rowIsometrySubgroup₀ v.Completion, ∀ u ∈ V, rT ι k u ∈ V :=
    fun k u hu => rT_mem_span_range_rT ι α k hu
  have hVle : V ≤ ⨆ i, typeSubmodule ι (tys.rep v i).ρ.dual :=
    Submodule.span_le.mpr (by rintro _ ⟨k, rfl⟩; exact rT_mem_iSup_typeSubmodule ι _ hαv k)
  have hReg : ∀ u ∈ V, Reg hw u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro _ ⟨k, rfl⟩
      exact (hOp.rT v k hαr).1
    · have e : (0 : AdelicGL2 (𝓞 K) K → ℂ) = (0 : ℂ) • α := by simp
      rw [e]
      exact hαr.smul 0
    · intro u u' _ _ hu hu'
      exact hu.add hu'
    · intro c u _ hu
      exact hu.smul c
  let Ψ : V →ₗ[ℂ] (AdelicGL2 (𝓞 K) K → ℂ) :=
    { toFun := fun u => Op (u : AdelicGL2 (𝓞 K) K → ℂ)
      map_add' := fun u u' => by rw [Submodule.coe_add]; exact hOp.add (hReg _ u.2).2.1 (hReg _ u'.2).2.1
      map_smul' := fun c u => by rw [RingHom.id_apply, Submodule.coe_smul, hOp.smul] }
  have hΨ : ∀ (k : rowIsometrySubgroup₀ v.Completion) (u : V), Ψ ⟨rT ι k u, hVstab k u u.2⟩ = rT ι k (Ψ u) := by
    intro k u
    exact (hOp.rT v k (hReg _ u.2)).2
  have hαV : α ∈ V := by
    have e : rT ι 1 α = α := by funext y; simp only [rT_apply, map_one, mul_one]
    rw [← e]
    exact Submodule.subset_span ⟨1, rfl⟩
  exact equivariant_mem_iSup_typeSubmodule ι (rowIsometryInclAt₀_injective v) (fun i => (tys.rep v i).ρ.dual)
    V hVstab hVle Ψ hΨ ⟨α, hαV⟩

theorem isArchBiFinite_casimirs (tys : ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α) :
    IsArchBiFinite K tys (archCasimirAtComplex hw α) ∧ IsArchBiFinite K tys (archCasimirBarAtComplex hw α) :=
  ⟨⟨comp_inv_op_mem_archCutSubmodule hw (opPkg_casimir hw) tys α (reg_of_isFactorizableTestFn hw hαf).2.1 hαb.1,
    op_mem_archDualCutSubmodule hw (opPkg_casimir hw) tys α (reg_of_isFactorizableTestFn hw hαf) hαb.2⟩,
   ⟨comp_inv_op_mem_archCutSubmodule hw (opPkg_casimirBar hw) tys α (reg_of_isFactorizableTestFn hw hαf).2.1 hαb.1,
    op_mem_archDualCutSubmodule hw (opPkg_casimirBar hw) tys α (reg_of_isFactorizableTestFn hw hαf) hαb.2⟩⟩

theorem leftCas_eq_casimirs (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) :
    leftCas hw α = archCasimirAtComplex hw α ∧ leftCasBar hw α = archCasimirBarAtComplex hw α := by
  have h := AutomorphicForm.leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex K w hw α
    (AutomorphicForm.IsFactorizableTestFn.isArchSmoothAtComplex_and_archDerivAtComplex_eq_tensor K w hw α hαf).1
  exact ⟨funext fun y => (h y).1, funext fun y => (h y).2⟩

end LeftCasimirComplex

theorem isFactorizableTestFn_leftCasimirComplex_and_rightConv_mem_of_isArchBiFinite
    (K : Type) [Field K] [NumberField K]
    (D : Set (AdelicGL2 (𝓞 K) K))
    (w : InfinitePlace K) (hw : w.IsComplex)
    (N : Ideal (𝓞 K)) (tys : AutomorphicForm.ArchTypeFamily K)
    (α : AdelicGL2 (𝓞 K) K → ℂ) (hαf : IsFactorizableTestFn K α) (hαb : IsArchBiFinite K tys α)
    (hαU : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ (levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K), α (k * g) = α g ∧ α (g * k) = α g) :
    let L : ArchDirComplex → (AdelicGL2 (𝓞 K) K → ℂ) → (AdelicGL2 (𝓞 K) K → ℂ) :=
      fun d γ y => deriv (fun t : ℝ => γ (archFlowAtComplex hw d (-t) * y)) 0
    let β : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + ((-Complex.I) : ℂ) * L .H (L .iH (α)) y + ((-Complex.I) : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + ((-Complex.I) : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + ((-Complex.I) : ℂ) * L .E (L .iFm (α)) y + ((-Complex.I) : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    let βb : AdelicGL2 (𝓞 K) K → ℂ := fun y =>
      -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * L .H (L .H (α)) y + (Complex.I : ℂ) * L .H (L .iH (α)) y + (Complex.I : ℂ) * L .iH (L .H (α)) y + (-1 : ℂ) * L .iH (L .iH (α)) y)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * L .H (α) y + (Complex.I : ℂ) * L .iH (α) y)) + (1 / 4 : ℂ) * ((1 : ℂ) * L .E (L .Fm (α)) y + (Complex.I : ℂ) * L .E (L .iFm (α)) y + (Complex.I : ℂ) * L .iE (L .Fm (α)) y + (-1 : ℂ) * L .iE (L .iFm (α)) y))
    (IsFactorizableTestFn K β ∧ IsArchBiFinite K tys β ∧ IsFactorizableTestFn K βb ∧ IsArchBiFinite K tys βb) ∧
    (∀ (l : List ArchDirComplex), IsFactorizableTestFn K (l.foldr L α)) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      (rightConv K x' β = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .H (L .iH (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g))) ∧
      (rightConv K x' βb = fun g =>
        -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (L .H (α))) g + (Complex.I : ℂ) * rightConv K x' (L .H (L .iH (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iH (L .H (α))) g + (-1 : ℂ) * rightConv K x' (L .iH (L .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (L .H (α)) g + (Complex.I : ℂ) * rightConv K x' (L .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (L .E (L .Fm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .E (L .iFm (α))) g + (Complex.I : ℂ) * rightConv K x' (L .iE (L .Fm (α))) g + (-1 : ℂ) * rightConv K x' (L .iE (L .iFm (α))) g)))) ∧
    (∀ x' : AdelicGL2 (𝓞 K) K → ℂ, Continuous x' →
      x' ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N → x' ∈ archCutSubmodule K tys →
      rightConv K x' β ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys ∧
      rightConv K x' βb ∈ levelInvariantSubmodule K (productionPinsOf K D (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) N ⊓ archCutSubmodule K tys)
    := by
  intro L β βb
  have hβf := LeftCasimirComplex.isFactorizableTestFn_leftCas hw hαf
  have hbr := LeftCasimirComplex.leftCas_eq_casimirs hw α hαf
  have hfin := LeftCasimirComplex.isArchBiFinite_casimirs hw tys α hαf hαb
  have hβb : IsArchBiFinite K tys β ∧ IsArchBiFinite K tys βb := by
    show IsArchBiFinite K tys (LeftCasimirComplex.leftCas hw α) ∧ IsArchBiFinite K tys (LeftCasimirComplex.leftCasBar hw α)
    rw [hbr.1, hbr.2]
    exact hfin
  have hinv := LeftCasimirComplex.leftCas_left_inv hw N α hαU
  refine ⟨⟨hβf.1, hβb.1, hβf.2, hβb.2⟩, LeftCasimirComplex.isFactorizableTestFn_foldr hw hαf,
    fun x' hx' => ⟨?_, ?_⟩,
    fun x' hx' _ _ => ⟨LeftCasimirComplex.rightConv_mem_inf D N tys _ hβf.1 hβb.1 hinv.1 x' hx',
      LeftCasimirComplex.rightConv_mem_inf D N tys _ hβf.2 hβb.2 hinv.2 x' hx'⟩⟩
  · show rightConv K x' (LeftCasimirComplex.leftCas hw α) = _
    rw [LeftCasimirComplex.leftCas_eq_sum,
      LeftCasimirComplex.rightConv_sum x' hx' (LeftCasimirComplex.isFactorizableTestFn_W10 hw hαf)]
    funext g
    simp only [LeftCasimirComplex.W10, LeftCasimirComplex.c10, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    show _ = -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (LeftCasimirComplex.Ld hw .H (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (LeftCasimirComplex.Ld hw .iH (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (LeftCasimirComplex.Ld hw .H (α))) g + (-1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (LeftCasimirComplex.Ld hw .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (α)) g + ((-Complex.I) : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .E (LeftCasimirComplex.Ld hw .Fm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .E (LeftCasimirComplex.Ld hw .iFm (α))) g + ((-Complex.I) : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iE (LeftCasimirComplex.Ld hw .Fm (α))) g + (-1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iE (LeftCasimirComplex.Ld hw .iFm (α))) g))
    ring
  · show rightConv K x' (LeftCasimirComplex.leftCasBar hw α) = _
    rw [LeftCasimirComplex.leftCasBar_eq_sum,
      LeftCasimirComplex.rightConv_sum x' hx' (LeftCasimirComplex.isFactorizableTestFn_W10 hw hαf)]
    funext g
    simp only [LeftCasimirComplex.W10, LeftCasimirComplex.c10b, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ]
    show _ = -((1 / 4 : ℂ) * ((1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (LeftCasimirComplex.Ld hw .H (α))) g + (Complex.I : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (LeftCasimirComplex.Ld hw .iH (α))) g + (Complex.I : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (LeftCasimirComplex.Ld hw .H (α))) g + (-1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (LeftCasimirComplex.Ld hw .iH (α))) g)) - (1 / 2 : ℂ) * ((1 / 2 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .H (α)) g + (Complex.I : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iH (α)) g)) + (1 / 4 : ℂ) * ((1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .E (LeftCasimirComplex.Ld hw .Fm (α))) g + (Complex.I : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .E (LeftCasimirComplex.Ld hw .iFm (α))) g + (Complex.I : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iE (LeftCasimirComplex.Ld hw .Fm (α))) g + (-1 : ℂ) * rightConv K x' (LeftCasimirComplex.Ld hw .iE (LeftCasimirComplex.Ld hw .iFm (α))) g))
    ring

theorem exists_isFactorizableTestFn_isArchBiFinite_rightConv_eq_smul_of_rightConv_eq_smul
    (F : Type) [Field F] [NumberField F] (tys : ArchTypeFamily F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (hφc : Continuous φ) (hφt : φ ∈ archCutSubmodule F tys)
    (f : AdelicGL2 (𝓞 F) F → ℂ) (hf : IsFactorizableTestFn F f) (lam : ℂ)
    (heig : rightConv F φ f = lam • φ) :
    ∃ f' : AdelicGL2 (𝓞 F) F → ℂ, IsFactorizableTestFn F f' ∧ IsArchBiFinite F tys f' ∧
      rightConv F φ f' = lam • φ
    := by
  classical
  let _mK : MeasurableSpace (ArchInfra.Kprod F) := borel _
  have _bK : BorelSpace (ArchInfra.Kprod F) := ⟨rfl⟩
  have _cK : CompactSpace (ArchInfra.Kprod F) := Pi.compactSpace
  have _nK : Nonempty (ArchInfra.Kprod F) := ⟨1⟩
  have _scK : SecondCountableTopology (ArchInfra.Kprod F) :=
    ArchInfraTopology.secondCountableTopology_piRowIsometrySubgroup₀ F
  have _pK : IsProbabilityMeasure (ArchInfra.muK F) := ⟨ArchInfra.muK_univ F⟩
  have _rK : (ArchInfra.muK F).IsMulRightInvariant := ArchInfra.isMulRightInvariant_muK F

  obtain ⟨hEfd, hEc, hEt, hEK⟩ :=
    AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule F (ArchInfra.inclArch F)
      (fun κ w => ArchInfra.archComponent_inclArch κ w) tys φ hφc hφt
  set E : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ) := Submodule.span ℂ (Set.range fun κ : ArchInfra.Kprod F =>
    fun g : AdelicGL2 (𝓞 F) F => φ (g * adelicArchGLIncl F (ArchInfra.inclArch F κ))) with hE
  have hφE : φ ∈ E := by
    refine Submodule.subset_span ⟨1, ?_⟩
    funext g
    simp only [map_one, mul_one]
  obtain ⟨e, he, -, -, het, het', hrep⟩ :=
    AutomorphicForm.exists_continuous_conj_invariant_integral_mul_apply_mul_eq_of_finiteDimensional_of_le_archCutSubmodule
      F (ArchInfra.muK F) (ArchInfra.inclArch F) (fun κ w => ArchInfra.archComponent_inclArch κ w) tys E hEfd hEc hEt hEK
  obtain ⟨hfc, hfK⟩ := AutomorphicForm.continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
  obtain ⟨fa, ff, hfa, hff, hfeq⟩ := hf
  set fa' : GL (Fin 2) (InfiniteAdeleRing F) → ℂ := fun y =>
    ∫ p : ArchInfra.Kprod F × ArchInfra.Kprod F,
      e p.1 * e p.2 * fa ((ArchInfra.inclArch F p.1)⁻¹ * y * (ArchInfra.inclArch F p.2)⁻¹)
        ∂((ArchInfra.muK F).prod (ArchInfra.muK F)) with hfa'
  obtain ⟨hfa't, hfa'bf⟩ :=
    AutomorphicForm.isArchTestFactor_and_isArchFactorBiFinite_integral_prod_of_continuous_of_mem_iSup_typeSubmodule
      F (ArchInfra.muK F) (ArchInfra.inclArch F) (fun κ w => ArchInfra.archComponent_inclArch κ w) tys e e he he fa hfa
  set f' : AdelicGL2 (𝓞 F) F → ℂ := fun g => fa' (glArch (𝓞 F) F g) * ff (glFin (𝓞 F) F g) with hf'
  refine ⟨f', ⟨fa', ff, hfa't, hff, fun g => rfl⟩, IsArchBiFinite.of_factorization F (fun g => rfl) (hfa'bf het het'), ?_⟩

  have hf'J : ∀ x : AdelicGL2 (𝓞 F) F,
      f' x = ∫ p : ArchInfra.Kprod F × ArchInfra.Kprod F,
        e p.1 * e p.2 * f ((ArchInfra.inclAdelic F p.1)⁻¹ * x * (ArchInfra.inclAdelic F p.2)⁻¹)
          ∂((ArchInfra.muK F).prod (ArchInfra.muK F)) := by
    intro x
    have h1 : ∀ p : ArchInfra.Kprod F × ArchInfra.Kprod F,
        e p.1 * e p.2 * f ((ArchInfra.inclAdelic F p.1)⁻¹ * x * (ArchInfra.inclAdelic F p.2)⁻¹)
          = e p.1 * e p.2 * fa ((ArchInfra.inclArch F p.1)⁻¹ * glArch (𝓞 F) F x * (ArchInfra.inclArch F p.2)⁻¹) *
            ff (glFin (𝓞 F) F x) := by
      intro p
      rw [hfeq, ArchInfra.inclAdelic_apply, ArchInfra.inclAdelic_apply, map_mul, map_mul, map_mul, map_mul,
        map_inv, map_inv, map_inv, map_inv, glArch_adelicArchGLIncl, glArch_adelicArchGLIncl,
        glFin_adelicArchGLIncl, glFin_adelicArchGLIncl, inv_one, one_mul, mul_one]
      ring
    show fa' (glArch (𝓞 F) F x) * ff (glFin (𝓞 F) F x) = _
    simp_rw [h1]
    rw [integral_mul_const]
  have heig' : ∀ g : AdelicGL2 (𝓞 F) F,
      ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g := by
    intro g
    have h := congrFun heig g
    rw [rightConv_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h
  have hrep' : ∀ z : AdelicGL2 (𝓞 F) F,
      ∫ κ, e κ * φ (z * ArchInfra.inclAdelic F κ) ∂(ArchInfra.muK F) = φ z := fun z => hrep φ hφE z
  have hνR : ∀ (κ : ArchInfra.Kprod F) (h : AdelicGL2 (𝓞 F) F → ℂ), Continuous h → HasCompactSupport h →
      ∫ y, h (y * ArchInfra.inclAdelic F κ) ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) =
        ∫ y, h y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro κ h _ _
    exact integral_mul_right_eq_self (μ := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) h
      (ArchInfra.inclAdelic F κ)
  have hrepψ : ∀ z : AdelicGL2 (𝓞 F) F,
      ∫ κ, e κ * (∫ y, φ (z * ArchInfra.inclAdelic F κ * y) * f y
        ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) ∂(ArchInfra.muK F) =
        ∫ y, φ (z * y) * f y ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) := by
    intro z
    have h1 : ∀ κ : ArchInfra.Kprod F,
        e κ * (∫ y, φ (z * ArchInfra.inclAdelic F κ * y) * f y
          ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)) =
          lam * (e κ * φ (z * ArchInfra.inclAdelic F κ)) := by
      intro κ
      rw [heig' (z * ArchInfra.inclAdelic F κ)]
      ring
    simp_rw [h1]
    rw [integral_const_mul, hrep' z]
    exact (heig' z).symm
  funext g
  rw [Pi.smul_apply, smul_eq_mul, rightConv_apply]
  show ∫ x, φ (g * x) * f' x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g
  simp_rw [hf'J]
  show ∫ x, φ (g * x) * ArchApproxIdentity.dconvWith (ArchInfra.muK F) (ArchInfra.inclAdelic F) e e f x
      ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F) = lam * φ g
  rw [ArchApproxIdentity.integral_mul_dconvWith (μ := ArchInfra.muK F)
    (a := ArchInfra.inclAdelic F) (ν := AdelicHaar.adelicGLHaar (Fin 2) (𝓞 F) F)
    (ArchInfra.continuous_inclAdelic (F := F)) he hφc hfc hfK hνR hrep' hrepψ g]
  exact heig' g

end AutomorphicForm
