/-
  A non-trivial constituent meets the character-typed cut.

  If `V ⊓ levelInvariantSubmodule ⊓ archCutSubmodule tys` is non-zero, then some archimedean
  character `χ` has `V ⊓ levelInvariantSubmodule ⊓ archCutSubmodule (ArchTypeFamily.ofChar K χ)`
  non-zero.  The proof reads a non-zero member, decomposes it by the pin's cut-weight theorem
  `exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent` into a finite sum of
  pure weight-character summands, takes a non-zero summand `ys j`, and reads the character
  `archWeightCharAt (hreal w) (nw w)` off it at every real place; the `archCutSubmodule` membership
  is then `mem_archCutSubmodule_ofChar_iff`.  It is the row that lets a consumer which needs a
  *character* type family replace an arbitrary `tys` by one.

  Transcribed from the pin's proof file (pinned `aa2d8b3`)
  `P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot.lean`
  (56 lines), with the statement from the wrapper of the same name.

  Home: this is the character-cut companion of the cut-weight decomposition, whose module
  `Cusp/CutWeightDecomposition.lean` is the mathematics it belongs beside — that module is still
  wired through the frozen `spec/old_check_stmts.py` (`PORT_FILES`), so putting the row there would
  drag a full legacy migration into this wave; the row is homed in this module instead, one import
  above it, and the migration stays on the legacy work list rather than being paid here.

  spec-pin: Theorems/Thm_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot.lean
  spec-pin: P2M/Sol/S_AutomorphicForm_CuspidalConstituent_exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.CutWeightDecomposition
import FLTForHuman.AutomorphicForm.Adelic.Cusp.Constituent
import FLTForHuman.AutomorphicForm.Adelic.ArchWeightChar
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm WindowedSiegel SiegelCovering
open AutomorphicForm.CuspidalConstituent
open scoped ComplexConjugate ENNReal InnerProductSpace

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.exists_inf_archCutSubmodule_ofChar_ne_bot_of_ne_bot
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (hX : V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys ≠ ⊥) :
    ∃ χ : ∀ v : InfinitePlace K, rowIsometrySubgroup₀ v.Completion →* ℂˣ,
      V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K (ArchTypeFamily.ofChar K χ) ≠ ⊥ := by
  classical
  obtain ⟨y, hy, hy0⟩ := (Submodule.ne_bot_iff _).mp hX
  obtain ⟨m, ys, hys, hchar, hsum⟩ :=
    AutomorphicForm.CuspidalConstituent.exists_eq_sum_hasArchCharacterAt_archWeightCharAt_of_isCuspConstituent K c u d₁ d₂ T
      hc hd₁ hd hcov ξ N hN tys V hV y hy

  have hex : ∃ j, ys j ≠ 0 := by
    by_contra h
    push Not at h
    apply hy0
    rw [hsum]
    exact Finset.sum_eq_zero fun j _ => h j
  obtain ⟨j, hj⟩ := hex

  choose nw hnw using fun w : InfinitePlace K => hchar j w (hreal w)
  refine ⟨fun w => archWeightCharAt (hreal w) (nw w), ?_⟩
  rw [Submodule.ne_bot_iff]
  refine ⟨ys j, Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp (hys j)).1, ?_⟩, hj⟩
  exact (mem_archCutSubmodule_ofChar_iff K _ _).mpr fun w => hnw w
