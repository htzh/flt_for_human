/-
  LD6-2 — the `Γ`-general complex-place dictionary: the choice function
  `realizeOf`, the structure `ComplexPlaceDictionaryOf`, and its comparison with
  the `Γ₀(N)` dictionary (`realizeOf_gamma0`, `ofGamma0`, `toGamma0`,
  `pt_ofGamma0`, `pt_toGamma0`, `pt_smul_of_mem`, `ramification_ne_zero`).

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_ModularCurve_ComplexPlaceDictionaryOf.lean` (116 lines whole;
  its 102-line declaration block, lines 15–116, 11 declarations, transcribed in
  full).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Definitions/Def_ModularCurve_ComplexPlaceDictionaryOf.lean

  `realizeOf Γ x τ` is `realize` with `Γ₀(N)` generalised to an arbitrary
  subgroup `Γ ≤ SL(2, ℤ)`; the `by classical exact if H : … then … else 0`
  *term* is kept verbatim, so `realizeOf_gamma0` and
  `ComplexPlaceDictionaryOf.ofGamma0`/`toGamma0` are `rfl` on the nose and
  `realizeOf_def` is `rfl`.  The structure's `mem_pt_iff` keeps the
  `Filter.IsBoundedUnder` boundedness shape over `laurentBaseChange ℂ F₀`, and
  `meromorphicOrderAt_realizeOf` the `WithTop ℤ` coercion
  `(((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)`, both verbatim.

  One proof deviates from the pin, and only at the spelling of a moved API lemma:
  `realizeOf_of_not` is proved with `dite_eq_right` where the pin writes the now
  deprecated `dif_neg` (deprecated in v4.34, `Init/Core.lean`).  The statement is
  untouched.

  The pin imports `Definitions/Def_AlgebraicCurve_DivisorClassGroup`; **the port
  does not**, and needs no substitute: the wave's audit (SET-LEAVESDEF §0)
  measured that no declaration of this module names anything from it.  The
  module sits on `ModularCurve/ComplexPlaceDictionary.lean` (`realize`,
  `ComplexPlaceDictionary`), `Defs/Laurent.lean` (`laurentBaseChange`,
  `LaurentSeries`) and `AlgebraicCurve/Defs/Place.lean` (`Place`, `Place.ord`).

  `spec-pin:` below names the one pin module transcribed.  No `Thm_` wrapper
  restating any of these 11 declarations exists in the pin: `grep -rlw` over
  `Theorems/` finds `realizeOf` in ten leaf-row statements
  (`Thm_ModularCurve_realizeOf_eq_div` and siblings), none of which is a wrapper
  of a declaration hosted here.

  The leaf row `ModularCurve.realizeOf_eq_div` (LV-6) is inserted below; its
  wrapper and `S_` copy are the two `spec-pin:` lines that follow.

spec-pin: Definitions/Def_ModularCurve_ComplexPlaceDictionaryOf.lean
spec-pin: Theorems/Thm_ModularCurve_realizeOf_eq_div.lean
spec-pin: P2M/Sol/S_ModularCurve_realizeOf_eq_div.lean
-/
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.Meromorphic.Order
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.ModularCurve.ComplexPlaceDictionary

set_option autoImplicit false

noncomputable section

open UpperHalfPlane
open scoped MatrixGroups Topology

namespace ModularCurve

/-- FLT's `realizeOf`: `realize` at an arbitrary `Γ ≤ SL(2, ℤ)` — on
`x : LaurentSeries ℂ` at `τ : ℍ`, the ratio `f.1 τ / f.2 τ` of a chosen pair of
`Γ`-modular forms whose q-expansions realise `x` with non-vanishing denominator
at `τ`, and `0` when no such pair exists. -/
def realizeOf (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) : ℂ := by
  classical
  exact
    if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
    then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
    else 0

/-- `realizeOf` unfolded: the definition is literally the `if H : … then … else 0`
term, so this is `rfl`. -/
theorem realizeOf_def (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf Γ x τ = by
      classical
      exact
        if H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
            (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
              x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
                ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)
        then (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ
        else 0 :=
  rfl

/-- When no realising pair of `Γ`-modular forms exists at `τ`, `realizeOf`
vanishes. -/
theorem realizeOf_of_not (Γ : Subgroup SL(2, ℤ)) (x : LaurentSeries ℂ) (τ : ℍ)
    (h : ¬ ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
        (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
          x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
            ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ)) :
    realizeOf Γ x τ = 0 := by
  classical
  rw [realizeOf_def]
  exact dite_eq_right h

/-- FLT's `ComplexPlaceDictionaryOf`: the `Γ`-general complex-place dictionary
over an arbitrary `F₀ : IntermediateField ℚ (LaurentSeries ℚ)` — a `ℍ`-indexed
family of places of `laurentBaseChange ℂ F₀`, with a positive ramification index,
`Γ`-invariance, the boundedness description of the valuation ring through
`realizeOf`, and the order law
`ord (realizeOf x) τ = ramification τ * ord_place x`. -/
structure ComplexPlaceDictionaryOf (Γ : Subgroup SL(2, ℤ))
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) where

  pt : ℍ → AlgebraicCurve.Place ℂ (laurentBaseChange ℂ F₀)

  ramification : ℍ → ℕ

  ramification_pos : ∀ τ : ℍ, 0 < ramification τ

  pt_smul : ∀ (γ : Γ) (τ : ℍ), pt ((γ : SL(2, ℤ)) • τ) = pt τ

  mem_pt_iff : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀),
    x ∈ (pt τ).toValuationSubring ↔
      Filter.IsBoundedUnder (· ≤ ·) (𝓝[≠] τ)
        (fun z : ℍ => ‖realizeOf Γ (x : LaurentSeries ℂ) z‖)

  meromorphicOrderAt_realizeOf : ∀ (τ : ℍ) (x : laurentBaseChange ℂ F₀), x ≠ 0 →
    meromorphicOrderAt (fun z : ℂ => realizeOf Γ (x : LaurentSeries ℂ) (ofComplex z)) (τ : ℂ) =
      (((ramification τ : ℤ) * (pt τ).ord x : ℤ) : WithTop ℤ)

namespace ComplexPlaceDictionaryOf

variable {Γ : Subgroup SL(2, ℤ)} {F₀ : IntermediateField ℚ (LaurentSeries ℚ)}

/-- `pt` is invariant under the elements of `Γ`, not only under the subtype. -/
theorem pt_smul_of_mem (D : ComplexPlaceDictionaryOf Γ F₀) {γ : SL(2, ℤ)} (hγ : γ ∈ Γ) (τ : ℍ) :
    D.pt (γ • τ) = D.pt τ :=
  D.pt_smul ⟨γ, hγ⟩ τ

/-- The ramification index is non-zero. -/
theorem ramification_ne_zero (D : ComplexPlaceDictionaryOf Γ F₀) (τ : ℍ) : D.ramification τ ≠ 0 :=
  (D.ramification_pos τ).ne'

end ComplexPlaceDictionaryOf

/-- At `Γ = Γ₀(N)` the general `realizeOf` is the level-`Γ₀(N)` `realize`. -/
theorem realizeOf_gamma0 (N : ℕ) (x : LaurentSeries ℂ) (τ : ℍ) :
    realizeOf (CongruenceSubgroup.Gamma0 N) x τ = realize N x τ :=
  rfl

/-- Read a level-`Γ₀(N)` dictionary as a `Γ₀(N)`-general one over
`modularFunctionFieldFull N`. -/
def ComplexPlaceDictionaryOf.ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N) where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realizeOf := D.meromorphicOrderAt_realize

/-- Read a `Γ₀(N)`-general dictionary over `modularFunctionFieldFull N` as a
level-`Γ₀(N)` one. -/
def ComplexPlaceDictionaryOf.toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    ComplexPlaceDictionary N where
  pt := D.pt
  ramification := D.ramification
  ramification_pos := D.ramification_pos
  pt_smul := D.pt_smul
  mem_pt_iff := D.mem_pt_iff
  meromorphicOrderAt_realize := D.meromorphicOrderAt_realizeOf

@[simp]
theorem ComplexPlaceDictionaryOf.pt_ofGamma0 {N : ℕ} [NeZero N] (D : ComplexPlaceDictionary N) :
    (ComplexPlaceDictionaryOf.ofGamma0 D).pt = D.pt :=
  rfl

@[simp]
theorem ComplexPlaceDictionaryOf.pt_toGamma0 {N : ℕ} [NeZero N]
    (D : ComplexPlaceDictionaryOf (CongruenceSubgroup.Gamma0 N) (modularFunctionFieldFull N)) :
    D.toGamma0.pt = D.pt :=
  rfl

/-- `1` is a strict period of `Γ` as soon as `T ∈ Γ`: `strictPeriods` is then
`ℤ • 1`.  The `S_` copy's helper (`RealizeOfWD.one_mem_strictPeriods`). -/
private theorem one_mem_strictPeriods_of_T_mem (Γ : Subgroup SL(2, ℤ))
    (hT : ModularGroup.T ∈ Γ) :
    (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem hT]
  exact AddSubgroup.mem_zmultiples _

/-- **The realising ratio.** If `x` is realised at `τ` by the pair `(g, h)` — the
q-expansion identity `x * qExp(h) = qExp(g)` holds and `h τ ≠ 0` — then
`realizeOf Γ x τ` is the ratio `g τ / h τ`.  This is the `S_` file's
`realizeOf_eq_div` at the wrapper's statement: the choice made inside
`realizeOf` is compared with the given pair through the q-expansion
multiplication law. -/
theorem realizeOf_eq_div
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ) {k : ℤ}
    (g h : ModularForm Γ k) (x : LaurentSeries ℂ)
    (hx : x * ((UpperHalfPlane.qExpansion 1 (h : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
      ((UpperHalfPlane.qExpansion 1 (g : UpperHalfPlane → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ))
    (τ : UpperHalfPlane) (hτ : (h : UpperHalfPlane → ℂ) τ ≠ 0) :
    ModularCurve.realizeOf Γ x τ = (g : UpperHalfPlane → ℂ) τ / (h : UpperHalfPlane → ℂ) τ := by
  classical
  have h1 : (1 : ℝ) ∈ (Γ : Subgroup (GL (Fin 2) ℝ)).strictPeriods :=
    one_mem_strictPeriods_of_T_mem Γ hT
  have H : ∃ p : (k : ℤ) × (ModularForm Γ k × ModularForm Γ k),
      (p.2.2 : ℍ → ℂ) τ ≠ 0 ∧
        x * ((qExpansion 1 (p.2.2 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) =
          ((qExpansion 1 (p.2.1 : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) :=
    ⟨⟨k, g, h⟩, hτ, hx⟩
  have hval : ModularCurve.realizeOf Γ x τ =
      (H.choose.2.1 : ℍ → ℂ) τ / (H.choose.2.2 : ℍ → ℂ) τ := by
    rw [ModularCurve.realizeOf_def]
    exact dite_eq_left H
  rw [hval]
  obtain ⟨hτ', hx'⟩ := H.choose_spec
  set p := H.choose with hp
  obtain ⟨k', g', h'⟩ := p
  simp only at hτ' hx' ⊢
  have hq : qExpansion 1 ((g' : ℍ → ℂ) * (h : ℍ → ℂ)) =
      qExpansion 1 ((g : ℍ → ℂ) * (h' : ℍ → ℂ)) := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ) (R := ℂ))
    rw [ModularForm.qExpansion_mul_coe one_pos h1, ModularForm.qExpansion_mul_coe one_pos h1,
      PowerSeries.coe_mul, PowerSeries.coe_mul, ← hx, ← hx']
    ring
  have hAB : (g'.mul h : ModularForm Γ (k' + k)) =
      ModularForm.mcast (add_comm k k') (g.mul h') := by
    rw [← sub_eq_zero, ← ModularForm.qExpansion_eq_zero_iff one_pos h1, FunLike.coe_sub,
      ModularForm.qExpansion_sub one_pos h1, sub_eq_zero, ModularForm.coe_mcast,
      ModularForm.coe_mul, ModularForm.coe_mul, hq]
  have hτeq : (g' : ℍ → ℂ) τ * (h : ℍ → ℂ) τ = (g : ℍ → ℂ) τ * (h' : ℍ → ℂ) τ := by
    have := congrArg (fun f : ModularForm Γ (k' + k) => (f : ℍ → ℂ) τ) hAB
    simpa [ModularForm.coe_mul, ModularForm.coe_mcast] using this
  rw [div_eq_div_iff hτ' hτ, hτeq]

end ModularCurve

end
