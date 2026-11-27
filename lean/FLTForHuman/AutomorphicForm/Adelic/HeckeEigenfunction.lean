/-
Hecke eigenfunctions of the carrier's pins.

A cuspidal form is a **Hecke eigenfunction** of a carrier `pins : CarrierPins F` with a
central character `ξ` when it is fixed by the level representation `levelRT pins Φ.level` —
the image of the level subgroup `pins.U N` under the right-regular action — and, at every
place `v` whose ideal does not divide the level, the abstract Hecke operator belonging to
`pins.gen v` acts on it by the eigenvalue `Φ.a v`, with the central-scalar eigenvalue
`Φ.b v` being the residue-field cardinality times `ξ` of the uniformizer idèle.

This module supplies the vocabulary and the two facts every downstream eigenfunction
argument uses:

* `IsHeckeEigenfunctionOf` — the predicate, on the right-translation group
  `RightTranslationGroup F = DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)`;
* `agreesAwayFromFinite_of_level_eq` — two eigensystems attached to one nonzero
  eigenfunction and the same level agree away from finitely many places (a form with one
  nonzero value pins its eigenvalues down, because a Hecke operator's eigenvalue is read
  off any nonzero vector of its eigenspace);
* `isHeckeEigenfunctionOf_zero_inhabitant` — the predicate is inhabited at `F = ℚ`: the
  zero form is a Hecke eigenfunction of the trivial pins at every eigenvalue.

The right-translation group is the `DomMulAct` of the opposite group, which is what makes
`φ ↦ φ (· * g)` a *left* action: the level representation and the Hecke operators are
subgroups of the same `Subgroup (RightTranslationGroup F)`, so `fixedPoints` applies to
both without a covariance side condition.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean>

## What is transcribed, and the one substitution

Seven of the pin's eight declarations are transcribed here at the pin's names and
statements.  The eighth, `uniformizerIdele`, is **not**: the port already has
`AutomorphicForm.uniformizerIdele` at `NumberTheory/NumberField/TateGlobal/Defs.lean`, with the
pin's definition verbatim (`Units.map (finIncl …) (localUnit … (uniformizerUnit …))`), so this
module imports it rather than declaring a second copy — two modules declaring one public full
name is a latent `import` collision (they cannot be imported together), which is how this was
found: the Euler-product module imports both this one and `TateGlobal.Defs`.

spec-pin: Definitions/Def_AutomorphicForm_HeckeEigenfunction.lean
-/
import FLTForHuman.AutomorphicForm.Adelic.CarrierPins
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.NumberField.TateGlobal.Defs
import FLTForHuman.RepTheory.AbstractHeckeOperator

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

/-- The right-translation group of `AdelicGL2 (𝓞 F) F`, as the `DomMulAct` of the opposite
group: this is the group acting on `AdelicGL2 (𝓞 F) F → ℂ` by `φ ↦ φ (· * g)`. -/
abbrev RightTranslationGroup : Type _ :=
  DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)

/-- The embedding of `AdelicGL2 (𝓞 F) F` in its right-translation group. -/
def rightTranslationEmbed : AdelicGL2 (𝓞 F) F →* RightTranslationGroup F where
  toFun g := DomMulAct.mk (MulOpposite.op g)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem rightTranslationEmbed_smul_apply (g x : AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    (rightTranslationEmbed F g • φ) x = φ (x * g) := rfl

end Defs

variable {F : Type} [Field F] [NumberField F]

/-- The level representation of the carrier pins: the level subgroup `pins.U N`, read in the
right-translation group. -/
def levelRT (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Subgroup (RightTranslationGroup F) :=
  (pins.U N).map (rightTranslationEmbed F)

/-- `φ` is a Hecke eigenfunction of the carrier pins with central character `ξ` and
eigensystem `Φ`: it is fixed by the level representation, and at every place outside the
level the abstract Hecke operator of `pins.gen v` acts on it by `Φ.a v`, the central
eigenvalue being the residue-field cardinality times `ξ` of the uniformizer idèle. -/
def IsHeckeEigenfunctionOf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ hmem : φ ∈ fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ),
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level →
      (∃ hfin : (QuotientGroup.mk ''
            ((levelRT pins Φ.level : Set (RightTranslationGroup F))
              * {rightTranslationEmbed F (pins.gen v)}) :
            Set (RightTranslationGroup F ⧸ levelRT pins Φ.level)).Finite,
        AbstractHeckeOperator.HeckeOperator (R := ℂ)
            (rightTranslationEmbed F (pins.gen v))
            (levelRT pins Φ.level) (levelRT pins Φ.level) hfin ⟨φ, hmem⟩
          = Φ.a v •
            (⟨φ, hmem⟩ : fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)))
      ∧ ∃ hz : uniformizerIdele F v ∈ pins.Z,
          Φ.b v = (Nat.card ((𝓞 F) ⧸ v.asIdeal) : ℂ)
            * ((ξ ⟨uniformizerIdele F v, hz⟩ : ℂˣ) : ℂ)

namespace IsHeckeEigenfunctionOf

/-- Two eigensystems attached to the same nonzero eigenfunction at the same level agree away
from finitely many places: the Hecke eigenvalue is determined by any nonzero vector of the
eigenspace, so the two systems' `a`-values coincide wherever both operators are defined. -/
theorem agreesAwayFromFinite_of_level_eq {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} {Φ Φ' : HeckeEigensystem F ℂ}
    (h : IsHeckeEigenfunctionOf pins ξ φ Φ) (h' : IsHeckeEigenfunctionOf pins ξ φ Φ')
    (hlev : Φ.level = Φ'.level) (hnz : ∃ x, φ x ≠ 0) :
    HeckeEigensystem.AgreesAwayFromFinite Φ Φ' := by
  obtain ⟨x₀, hx₀⟩ := hnz
  obtain ⟨N', hN', a', b'⟩ := Φ'
  dsimp only at hlev
  subst hlev
  obtain ⟨hmem, hcl⟩ := h
  obtain ⟨hmem', hcl'⟩ := h'
  have hfactors : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Φ.level}.Finite :=
    Ideal.finite_factors (by simpa using Φ.level_ne_bot)
  refine ⟨hfactors.toFinset, fun v hv => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_ofPred_eq] at hv
  obtain ⟨⟨hfin, heig⟩, hz, hb⟩ := hcl v hv
  obtain ⟨⟨hfin', heig'⟩, hz', hb'⟩ := hcl' v hv
  constructor
  · have hEq :
        Φ.a v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ))
          = a' v • (⟨φ, hmem⟩ :
            fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)) :=
      heig.symm.trans heig'
    have hval := congrArg Subtype.val hEq
    rw [FixedPoints.coe_smul, FixedPoints.coe_smul] at hval
    have hpt := congrFun hval x₀
    simp only [Pi.smul_apply, smul_eq_mul] at hpt
    exact mul_right_cancel₀ hx₀ hpt
  · exact hb.trans hb'.symm

end IsHeckeEigenfunctionOf

/-- The predicate is inhabited: over `ℚ`, the zero form is a Hecke eigenfunction of the
trivial carrier, with every `a`-eigenvalue zero. -/
theorem isHeckeEigenfunctionOf_zero_inhabitant :
    ∃ (pins : CarrierPins ℚ) (ξ : pins.Z →* ℂˣ) (φ : AdelicGL2 (𝓞 ℚ) ℚ → ℂ)
      (Φ : HeckeEigensystem ℚ ℂ), IsHeckeEigenfunctionOf pins ξ φ Φ := by
  refine ⟨⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩, 1, (fun _ => (0 : ℂ)),
    ⟨⊤, by simp, fun _ => 0,
      fun v => (Nat.card ((𝓞 ℚ) ⧸ v.asIdeal) : ℂ) * 1⟩, ?_⟩
  have hmem0 : (fun _ => (0 : ℂ)) ∈
      fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
        (AdelicGL2 (𝓞 ℚ) ℚ → ℂ) := fun _ => smul_zero _
  refine ⟨hmem0, fun v _ => ⟨⟨?_, ?_⟩, Subgroup.mem_top _, rfl⟩⟩
  · refine Set.Finite.image _ (Set.Finite.subset (Set.finite_singleton 1) ?_)
    rintro x ⟨u, hu, y, hy, rfl⟩
    rcases hy with rfl
    have hu1 : u = 1 := by
      rcases hu with ⟨w, hw, rfl⟩
      rcases hw with rfl
      exact map_one _
    simp [hu1]
  · have hzero : (⟨(fun _ => (0 : ℂ)), hmem0⟩ :
        fixedPoints (levelRT (F := ℚ) ⟨⊤, 0, ∅, ⊤, fun _ => ⊥, fun _ => 1, ⊤, 0⟩ ⊤)
          (AdelicGL2 (𝓞 ℚ) ℚ → ℂ)) = 0 := Subtype.ext rfl
    rw [hzero, map_zero]
    exact Subtype.ext (by simp)

end AutomorphicForm
