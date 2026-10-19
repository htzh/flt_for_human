/-
  The continuous norm section: `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq`.

  The idèle norm `ideleNorm F : (AdeleRing (𝓞 F) F)ˣ → ℝ` is a continuous surjection onto the
  positive reals, and this headline splits it continuously: there is a continuous monoid
  homomorphism `s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` with `ideleNorm F (s r) = r` and trivial
  finite part. The section is supported at a single archimedean place — at a real place
  `t ↦ e.symm t` along the isometry `e = ringEquivRealOfIsReal`, at a complex place
  `r ↦ e.symm (√r : ℂ)` because `w.mult = 2` there — merged by `if hv : IsReal w` and pushed
  into the idèles through `archUnitHom w`, whose finite part is `1` by construction. The place
  is `Classical.arbitrary (InfinitePlace F)`: a nonempty `F` always has one.

  This is the thin listed façade: the proof is the shared tier-3 engine
  `FLTForHuman/NumberTheory/NumberField/TateGlobal/NormSection.lean`
  (`NumberField.TateGlobal.FujisakiC3`), which the norm-`Q` engine
  `TateGlobal/FujisakiC3.lean` is deliberately not part of, so a consumer of the section does
  not drag in the latter's 11k-line T1 cone.

  Pin: `anthropics/fermats-last-theorem` at `aa2d8b3`; the statement is the wrapper
  https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean
  and the proof is the silo's `solution` at lines 893–901 of
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_NumberField_TateGlobal_exists_continuous_monoidHom_ideleNorm_apply_eq.lean#L893-L901
  The node's story is `topics/numberTheory/tateGlobal/TOPIC-norm-section.md`.
-/
import FLTForHuman.NumberTheory.NumberField.TateGlobal.NormSection

set_option autoImplicit false

open NumberField NumberField.TateGlobal
open scoped NNReal

/-- The idèle norm has a continuous splitting: a continuous monoid homomorphism
`ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` whose norm is the identity on `ℝ≥0ˣ`, with trivial finite part
at every point. Read off the tier-3 engine `NumberField.TateGlobal.FujisakiC3.normSectionAt` at
an arbitrary archimedean place. -/
theorem NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq
    (F : Type) [Field F] [NumberField F] :
    ∃ s : ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ, Continuous s ∧
      (∀ r : ℝ≥0ˣ, ideleNorm F (s r) = ((r : ℝ≥0) : ℝ)) ∧
      ∀ r : ℝ≥0ˣ, ((s r : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 = 1 := by
  classical
  refine ⟨FujisakiC3.normSectionAt (Classical.arbitrary (InfinitePlace F)),
    FujisakiC3.continuous_normSectionAt _, fun r => ?_, fun r => rfl⟩
  exact FujisakiC3.ideleNorm_normSectionAt _ r
