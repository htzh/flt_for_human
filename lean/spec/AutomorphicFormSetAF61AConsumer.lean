/-
  SET-AF61A consumer: the level-one obstruction, spent.

  **The row.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/LevelBotObstruction.lean`:
  `AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`
  — no function is a Hecke coset eigenfunction of `heckeGen` for the place `v` at the trivial level
  `levelOne _ F ⊥ ⊓ finiteAdelicGL2Subgroup F`.  The row is a `¬`, so every reading below spends it by
  landing on a `False` and continuing from there.

  **The readings.**  The set's title is "a Hecke coset eigenfunction at trivial level is zero"; the
  row states the stronger, hypothesis-free form (there is no such function at all).  Four executed
  compositions, each a strict consumer of the row:

  * Zone A. The row at hypothesis strength: an eigenfunction `φ` at the trivial level, with *any*
    eigenvalue `c`, is the zero function.  `φ` and `c` are the row's own arguments, so they enter in
    hypothesis form — the row is spent on the goal `φ = 0`, which is the "is zero" reading.
  * Zone B. The same, pointwise: every value of `φ` vanishes.  Zone A composed with `congrFun`, i.e.
    the zero function read at a point.
  * Zone C. The sharpest reading, and the only one that is not a re-statement of the row: *no Hecke
    coset system exists* for the trivial level and `heckeGen`.  The row is applied to the zero
    function, whose level-invariance is `rfl` and whose eigen-equation is
    `AutomorphicForm.SmoothCusp.heckeCosetSum_const`, so the coset-system half of
    `IsHeckeCosetEigenfunctionAt` is the entire obstruction.  The composition turns the row into a
    statement about `HeckeIntegralSeam.IsHeckeCosetSystem` itself.
  * Zone D. Zone C composed with the existential reading of `IsHeckeCosetEigenfunctionAt`: no pair
    `(φ, c)` exists at the trivial level.

  Zone C is the concrete zone: the zero function is an eigenfunction candidate by computation, so the
  row's hypothesis is inhabited in form and refuted only through the coset system.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.LevelBotObstruction

noncomputable section

open IsDedekindDomain NumberField NumberField.AdelicLevel
open AutomorphicForm

namespace AutomorphicForm.SetAF61AConsumer

/-! ### Zone A: an eigenfunction at the trivial level is zero -/

/-- **Zone A.**  The row at hypothesis strength.  Any `φ` that is a Hecke coset eigenfunction of
`heckeGen` for `v` at `levelOne _ F ⊥ ⊓ finiteAdelicGL2Subgroup F`, with any eigenvalue `c`, is the
zero function: the row's `False` is spent at `φ = 0`. -/
theorem consumer_levelBot_eigenfunction_eq_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ)
    (hφ : SmoothCusp.IsHeckeCosetEigenfunctionAt F
      (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) v φ c) :
    φ = 0 :=
  (SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup F v φ c hφ).elim

/-! ### Zone B: the same, read at a point -/

/-- **Zone B.**  Zone A composed with `congrFun`: the eigenfunction vanishes at every point of
`GL₂(𝔸_F)`, not only as a function. -/
theorem consumer_levelBot_eigenfunction_apply_eq_zero
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ)
    (hφ : SmoothCusp.IsHeckeCosetEigenfunctionAt F
      (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) v φ c)
    (g : AdelicGL2 (𝓞 F) F) :
    φ g = 0 :=
  congrFun (consumer_levelBot_eigenfunction_eq_zero F v φ c hφ) g

/-! ### Zone C: no Hecke coset system exists at the trivial level -/

/-- **Zone C.**  The row spent on the zero function, whose eigen-equation holds by
`AutomorphicForm.SmoothCusp.heckeCosetSum_const` and whose level-invariance holds by `rfl`.  What the
row therefore refutes is the *coset system*: there is no `reps` at all for the trivial level and
`heckeGen`. -/
theorem consumer_no_levelBot_cosetSystem
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
    (reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F) :
    ¬ HeckeIntegralSeam.IsHeckeCosetSystem
      (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) reps := by
  intro hsys
  exact SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup F v
    (fun _ => 0) 0
    ⟨reps, hsys, fun g => by
      rw [SmoothCusp.heckeCosetSum_const (F := F) reps 0 g]
      simp⟩

/-! ### Zone D: no eigenfunction exists at the trivial level -/

/-- **Zone D.**  Zone C composed with the existential reading of `IsHeckeCosetEigenfunctionAt`: the
trivial level carries no Hecke coset eigenfunction of `heckeGen`, with any eigenvalue. -/
theorem consumer_no_levelBot_eigenfunction
    (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    ¬ ∃ (φ : AdelicGL2 (𝓞 F) F → ℂ) (c : ℂ),
      SmoothCusp.IsHeckeCosetEigenfunctionAt F
        (levelOne (𝓞 F) F ⊥ ⊓ finiteAdelicGL2Subgroup F) (heckeGen (𝓞 F) F v) v φ c := by
  rintro ⟨φ, c, reps, hsys, -⟩
  exact consumer_no_levelBot_cosetSystem F v reps hsys

end AutomorphicForm.SetAF61AConsumer
