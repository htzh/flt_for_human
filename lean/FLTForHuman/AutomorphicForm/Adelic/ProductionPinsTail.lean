/-
The production-pins tail: window counting, invariance, and cuspidal linearity.

Five small facts: the ample-window rational points have a bounded `ncard`; an invariant function is
determined by its finite part on the rational points; `U_mul` meets the rational points; and the
cuspidal functions are closed under addition and scalar multiplication.

  spec-pin: P2M/Sol/S_AutomorphicForm_exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_ext_of_invariant_of_forall_glFin_eq_one_rat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_exists_mem_productionPinsCompact_U_mul_eq_rat.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsCuspidalFn_add.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_IsCuspidalFn_smul.lean

## Port deltas

* added `import FLTForHuman.NumberTheory.AdelicLevel.LatticeCounting` — the two level-covering
  engines (`exists_decomp`, pin 2 `:42`; `exists_mem_productionPinsCompact_U_mul_eq_rat_impl`,
  pin 3 `:28`) rest on `NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat`
  (pin 3 `:1` / pin 2 `:3`), which is declared there and is not reachable from the scaffold's
  import closure.

## Namespaces

The pins' search-stage labels are renamed to subject names: pin 1's `Ws23.Mult` (a workspace
label) is dropped, so its engine sits directly in `AutomorphicForm`; pin 2's own `ExtEngine` is
kept (`AutomorphicForm.ExtEngine`); pin 3's `M4aP1R.LevelCoveringDecomp` loses only the workspace
label (`AutomorphicForm.LevelCoveringDecomp`). The two `IsCuspidalFn` rows stay in the pin's
unqualified text inside the nested `namespace IsCuspidalFn` (FR-0224: the checker hashes text).

## Heartbeat probe (recorded, never installed — FR-0225)

`lake env lean -DautoImplicit=false -DmaxHeartbeats=N FLTForHuman/AutomorphicForm/Adelic/ProductionPinsTail.lean`
is **silent at N = 6 250** and **fails at N = 3 125** (= 6 250 / 2), at
`(deterministic) timeout at whnf` on the closing `rw [mul_assoc, inv_mul_cancel_right, map_inv,
hg', inv_mul_cancel_left]` of `exists_mem_productionPinsCompact_U_mul_eq_rat_impl`. No
`set_option maxHeartbeats` is in this module.

## Proof-only deviations from the pin

* `exists_mem_productionPinsCompact_U_mul_eq_rat` (the row): the pin closes with
  `first | exact …_impl … | (apply …_impl <;> assumption)`; the second alternative is
  unreachable and fires `linter.unusedTactic`/`linter.unreachableTactic`, so the row is closed by
  the first alternative alone. Statement unchanged.
* `Set.mem_setOf_eq` is `Set.mem_ofPred_eq` at v4.34 (deprecated alias).
* The frozen binder `hκ` of row 1 is dead in the pin's proof; it is spent once
  (`have hκ' : 1 ≤ κ := hκ`) rather than renamed (FR-0236).
-/
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.CentreCutSiegelSetAmple
import FLTForHuman.AutomorphicForm.Adelic.LsXi
import FLTForHuman.AutomorphicForm.Adelic.Siegel.AmpleFiniteness
import FLTForHuman.AutomorphicForm.Adelic.ProductionPinsCompact
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import FLTForHuman.LanglandsTunnell.DeltaLift
import FLTForHuman.AutomorphicForm.Adelic.Cusp.IsotypicVanishing
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.NumberTheory.AdelicLevel.LatticeCounting

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open scoped ENNReal NNReal BigOperators

namespace AutomorphicForm

theorem finite_and_ncard_biUnion_le {α ι : Type*} [DecidableEq ι] (T : Finset ι) (E : ι → Set α)
    (M : ℕ)
    (hE : ∀ i ∈ T, (E i).Finite ∧ (E i).ncard ≤ M) :
    (⋃ i ∈ T, E i).Finite ∧ (⋃ i ∈ T, E i).ncard ≤ T.card * M := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hE' : ∀ i ∈ T, (E i).Finite ∧ (E i).ncard ≤ M := fun i hi => hE i (Finset.mem_insert_of_mem hi)
    obtain ⟨hfin, hcard⟩ := ih hE'
    obtain ⟨hafin, hacard⟩ := hE a (Finset.mem_insert_self a T)
    rw [Finset.set_biUnion_insert, Finset.card_insert_of_notMem ha]
    refine ⟨hafin.union hfin, ?_⟩
    calc (E a ∪ ⋃ i ∈ T, E i).ncard ≤ (E a).ncard + (⋃ i ∈ T, E i).ncard := Set.ncard_union_le _ _
      _ ≤ M + T.card * M := Nat.add_le_add hacard hcard
      _ = (T.card + 1) * M := by ring

theorem exists_forall_ncard_setOf_globalPoints_mul_mem_iUnion_centreCutSiegelSetAmple_le
    (F : Type) [Field F] [NumberField F]
    (c u d₁ d₂ κ : ℝ) (hκ : 1 ≤ κ) (hc : 0 < c) (hd₁ : 0 < d₁)
    (T : Finset (AdelicGL2 (𝓞 F) F)) :
    ∃ N : ℕ, ∀ h : AdelicGL2 (𝓞 F) F,
      {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.Finite ∧
        {γ : Matrix.GeneralLinearGroup (Fin 2) F |
          globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}.ncard ≤ N
  := by
  classical

  /- the pin's proof spends `hc`/`hd₁` only; the frozen binder `hκ` is spent once (FR-0236). -/
  have hκ' : 1 ≤ κ := hκ
  have h1 : ∀ w : InfinitePlace F,
      archComponent F w (glArch (𝓞 F) F (1 : AdelicGL2 (𝓞 F) F)) ∈ rowIsometrySubgroup (w.Completion) := by
    intro w
    rw [map_one, map_one]
    exact one_mem _
  have hA := AutomorphicForm.finite_setOf_exists_globalPoints_mul_mem_image_centreCutSiegelSetAmple
    F c u d₁ d₂ κ hc hd₁ 1 h1
  set A : Set (Matrix.GeneralLinearGroup (Fin 2) F) := {γ | ∃ s ∈ centreCutSiegelSetAmple F c u d₁ d₂ κ,
      globalPoints (𝓞 F) F γ * s ∈ (· * (1 : AdelicGL2 (𝓞 F) F)) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}
    with hAdef
  refine ⟨T.card * A.ncard, fun h => ?_⟩

  let E : AdelicGL2 (𝓞 F) F → Set (Matrix.GeneralLinearGroup (Fin 2) F) := fun x =>
    {γ | globalPoints (𝓞 F) F γ * h ∈ (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}
  have hE : ∀ x ∈ T, (E x).Finite ∧ (E x).ncard ≤ A.ncard := by
    intro x _
    by_cases hne : (E x).Nonempty
    · obtain ⟨γ₁, hγ₁⟩ := hne
      obtain ⟨s₁, hs₁, hs₁eq⟩ := hγ₁

      have hmap : Set.MapsTo (fun γ => γ * γ₁⁻¹) (E x) A := by
        intro γ hγ
        obtain ⟨s, hs, hseq⟩ := hγ
        refine ⟨s₁, hs₁, s, hs, ?_⟩

        dsimp only at hs₁eq hseq ⊢
        rw [mul_one, map_mul, map_inv]
        have e1 : s₁ = globalPoints (𝓞 F) F γ₁ * h * x⁻¹ := by rw [← hs₁eq, mul_inv_cancel_right]
        have e2 : s = globalPoints (𝓞 F) F γ * h * x⁻¹ := by rw [← hseq, mul_inv_cancel_right]
        rw [e1, e2]
        group
      have hinj : Set.InjOn (fun γ => γ * γ₁⁻¹) (E x) := fun a _ b _ hab => mul_right_cancel hab
      have hfin : (E x).Finite := Set.Finite.of_injOn hmap hinj hA
      exact ⟨hfin, Set.ncard_le_ncard_of_injOn _ hmap hinj hA⟩
    · rw [Set.not_nonempty_iff_eq_empty] at hne
      rw [hne]
      simp
  have hsub : {γ : Matrix.GeneralLinearGroup (Fin 2) F |
      globalPoints (𝓞 F) F γ * h ∈ ⋃ x ∈ T, (· * x) '' centreCutSiegelSetAmple F c u d₁ d₂ κ}
      = ⋃ x ∈ T, E x := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, E]
  obtain ⟨hfin, hcard⟩ := finite_and_ncard_biUnion_le T E A.ncard hE
  rw [hsub]
  exact ⟨hfin, hcard⟩

namespace ExtEngine

open NumberField.InfinitePlace AdelicDock

private theorem isReal_rat_infinitePlace (v : InfinitePlace ℚ) : v.IsReal := IsTotallyReal.isReal v

private noncomputable def ratArchHom : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) →* GL (Fin 2) ℝ :=
  (Matrix.GeneralLinearGroup.map
    (InfinitePlace.Completion.ringEquivRealOfIsReal (isReal_rat_infinitePlace default)).toRingHom).comp
    ((archComponent ℚ default).comp (glArch (𝓞 ℚ) ℚ))

private theorem ratArchHom_apply (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ratArchHom g = LanglandsTunnell.ratArchGL2 g := rfl

private theorem ratArch_mul (g g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (g * g')
      = LanglandsTunnell.ratArchGL2 g * LanglandsTunnell.ratArchGL2 g' := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, ← ratArchHom_apply, map_mul]

private theorem ratArch_inv (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 g⁻¹ = (LanglandsTunnell.ratArchGL2 g)⁻¹ := by
  rw [← ratArchHom_apply, ← ratArchHom_apply, map_inv]

private theorem ratArch_finEmbed (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)) :
    LanglandsTunnell.ratArchGL2 (finEmbed (𝓞 ℚ) ℚ u) = 1 := by
  unfold LanglandsTunnell.ratArchGL2
  rw [glArch_finEmbed, map_one, map_one]

theorem exists_decomp {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : AdelicGL2 (𝓞 ℚ) ℚ) :
    ∃ (γ : GL (Fin 2) ℚ) (h : AdelicGL2 (𝓞 ℚ) ℚ) (u : GL (Fin 2) (FiniteAdeleRing (𝓞 ℚ) ℚ)),
      u ∈ finiteLevelOne (𝓞 ℚ) ℚ N ∧ glFin (𝓞 ℚ) ℚ h = 1 ∧
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ ∧
          globalPoints (𝓞 ℚ) ℚ γ * g = h * finEmbed (𝓞 ℚ) ℚ u := by
  obtain ⟨γ, hlev, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set y : AdelicGL2 (𝓞 ℚ) ℚ := globalPoints (𝓞 ℚ) ℚ γ * g with hy
  refine ⟨γ, y * (finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ y))⁻¹, glFin (𝓞 ℚ) ℚ y, ?_, ?_, ?_, ?_⟩
  · exact (mem_levelOne_iff (R := 𝓞 ℚ) (K := ℚ) (N := N)).mp hlev
  · rw [map_mul, map_inv, glFin_finEmbed, mul_inv_cancel]
  · rw [ratArch_mul, ratArch_inv, ratArch_finEmbed, inv_one, mul_one]
    exact hpos default (isReal_rat_infinitePlace default)
  · rw [inv_mul_cancel_right]

end ExtEngine

namespace LevelCoveringDecomp

open NumberField.InfinitePlace AdelicDock

theorem exists_mem_productionPinsCompact_U_mul_eq_rat_impl
    {N : Ideal (𝓞 ℚ)} (hN : N ≠ ⊥) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) :
    ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
      u ∈ (productionPinsCompact ℚ).U N ∧
        glFin (𝓞 ℚ) ℚ h = 1 ∧
        (∀ (w : InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map (Completion.ringEquivRealOfIsReal hw).toRingHom
              (archComponent ℚ w (glArch (𝓞 ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = globalPoints (𝓞 ℚ) ℚ γ * h * u := by
  obtain ⟨γ, hmem, hpos⟩ := NumberField.AdelicLevel.exists_globalPoints_mul_mem_levelOne_rat hN g
  set g' : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) := globalPoints (𝓞 ℚ) ℚ γ * g with hg'
  set u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ) :=
    AdelicDock.finEmbed (𝓞 ℚ) ℚ (glFin (𝓞 ℚ) ℚ g') with hu
  refine ⟨γ⁻¹, g' * u⁻¹, u, ?_, ?_, ?_, ?_⟩
  ·
    rw [productionPinsCompact_U, Subgroup.mem_inf, hu, AdelicDock.finEmbed_mem_levelOne_iff,
      mem_finiteAdelicGL2Subgroup_iff, AdelicDock.glArch_finEmbed]
    exact ⟨(mem_levelOne_iff).mp hmem, rfl⟩
  ·
    rw [map_mul, map_inv, hu, AdelicDock.glFin_finEmbed, mul_inv_cancel]
  ·
    intro w hw
    rw [map_mul, map_inv, hu, AdelicDock.glArch_finEmbed, inv_one, mul_one]
    exact hpos w hw
  ·
    rw [mul_assoc, inv_mul_cancel_right, map_inv, hg', inv_mul_cancel_left]

end LevelCoveringDecomp

theorem ext_of_invariant_of_forall_glFin_eq_one_rat
    {M : Type*} {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    {Ψ₁ Ψ₂ : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ → M}
    (h₁ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₁ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₁ x)
    (h₂ : ∀ (γ : GL (Fin 2) ℚ) (x : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ),
      Ψ₂ (AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * x) = Ψ₂ x)
    (h₁' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₁ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₁ x)
    (h₂' : ∀ u ∈ NumberField.AdelicLevel.finiteLevelOne (NumberField.RingOfIntegers ℚ) ℚ N,
      ∀ x, Ψ₂ (x * AdelicDock.finEmbed (NumberField.RingOfIntegers ℚ) ℚ u) = Ψ₂ x)
    (heq : ∀ h : AutomorphicForm.AdelicGL2 (NumberField.RingOfIntegers ℚ) ℚ,
      NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 →
        LanglandsTunnell.ratArchGL2 h ∈ Matrix.GLPos (Fin 2) ℝ → Ψ₁ h = Ψ₂ h) :
    Ψ₁ = Ψ₂
  := by
  funext g
  obtain ⟨γ, h, u, hu, hfin, hpos, hdec⟩ := ExtEngine.exists_decomp hN g
  rw [← h₁ γ g, ← h₂ γ g, hdec, h₁' u hu h, h₂' u hu h]
  exact heq h hfin hpos

theorem exists_mem_productionPinsCompact_U_mul_eq_rat
    {N : Ideal (NumberField.RingOfIntegers ℚ)} (hN : N ≠ ⊥)
    (g : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)) :
    ∃ (γ : Matrix.GeneralLinearGroup (Fin 2) ℚ)
      (h u : Matrix.GeneralLinearGroup (Fin 2) (NumberField.AdeleRing (NumberField.RingOfIntegers ℚ) ℚ)),
      u ∈ (AutomorphicForm.productionPinsCompact ℚ).U N ∧
        NumberField.AdelicLevel.glFin (NumberField.RingOfIntegers ℚ) ℚ h = 1 ∧
        (∀ (w : NumberField.InfinitePlace ℚ) (hw : w.IsReal),
          Matrix.GeneralLinearGroup.map
              (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hw).toRingHom
              (NumberField.AdelicLevel.archComponent ℚ w
                (NumberField.AdelicLevel.glArch (NumberField.RingOfIntegers ℚ) ℚ h))
            ∈ Matrix.GLPos (Fin 2) ℝ) ∧
        g = AutomorphicForm.globalPoints (NumberField.RingOfIntegers ℚ) ℚ γ * h * u
  := by
  exact LevelCoveringDecomp.exists_mem_productionPinsCompact_U_mul_eq_rat_impl hN g

namespace IsCuspidalFn

theorem add
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f₁ f₂ : G → ℂ}
    (hf₁ : IsCuspidalFn μ u f₁) (hf₂ : IsCuspidalFn μ u f₂)
    (h₁ : ∀ g, Integrable (constantTermIntegrand u f₁ g) μ)
    (h₂ : ∀ g, Integrable (constantTermIntegrand u f₂ g) μ) :
    IsCuspidalFn μ u (fun x => f₁ x + f₂ x)
  := by
  intro g
  rw [AutomorphicForm.constantTerm_add μ u g (h₁ g) (h₂ g), hf₁ g, hf₂ g, add_zero]

theorem smul
    {Q : Type*} [MeasurableSpace Q] {G : Type*} [Group G]
    {μ : Measure Q} {u : Q → G} {f : G → ℂ}
    (hf : IsCuspidalFn μ u f) (c : ℂ) : IsCuspidalFn μ u (fun x => c * f x)
  := by
  intro g
  rw [constantTerm_smul, hf g, mul_zero]

end IsCuspidalFn

end AutomorphicForm

end
