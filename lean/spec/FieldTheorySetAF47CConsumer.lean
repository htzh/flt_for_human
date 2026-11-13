/-
  SET-AF47C consumer: the complete-splitting headline and the counting bound, read at their two
  smallest concrete instances.

  **The zone.** Two rows, both read off
  `FLTForHuman/FieldTheory/ValuationSubringCompleteSplitting.lean`.

  Row 1 (`ValuationSubring.exists_valuation_mul_eq_one_of_finrank_le_card`, the module's headline) is
  read at the smallest complete splitting: `F' = F` (degree one), `ι = Fin 1`, `O' = ![O]`.  The
  three hypotheses are discharged, not assumed:

  * `hinj` — `Fin 1` is a subsingleton, so any map out of it is injective;
  * `hO'` — `![O] i = O` for the unique `i : Fin 1`, and `comap` of the identity algebra map is the
    subring itself (`O.comap (algebraMap F F) = O` by `ValuationSubring.mem_comap`);
  * `hcard` — `Module.finrank F F = 1 ≤ Fintype.card (Fin 1) = 1` (`Module.finrank_self`).

  What comes back has no `F'` left: `∃ h : F, O.valuation (h * g) = 1` for every `g ≠ 0` — the
  `e = 1` headline at the trivial prolongation, `O`'s value group being all of the value group.

  Row 2 (`ValuationSubring.CompleteSplitting.card_add_card_le_finrank`, the counting bound
  `#s + #τ ≤ [F' : F]`) is read at `R = ⊤ : ValuationSubring F`, `F' = F`, the singleton prolongation
  family `S' = {⊤}`, the empty witness index `τ = Fin 0`, and the one-element residue set
  `s = {1} : Finset (ResidueField ↥⊤)`:

  * `hS'` is `comap` of the identity and `hRS'` is `⊤ ∈ {⊤}`;
  * `clsR`, `ω`, `hclsR`, `hne`, `hωlt` are all maps out of `Fin 0`, hence vacuous;
  * `hind` is vacuous because its unit premise `∃ t : Fin 0, …` is empty;
  * `hs` — the linear independence of the one-element family `{1}` — is
    `linearIndependent_unique_iff`: the index type `↥{1}` is a singleton (`Unique`), and its sole
    vector is `1 ≠ 0`.

  The bound then reads `#s + #τ = 1 + 0 ≤ [F : F] = 1`.

  **The residue-field algebra.** Row 2's `hs` has the type `LinearIndependent` over
  `ResidueField ↥(R.comap …)` acting on `ResidueField ↥R`, whose `Module` structure is the
  `residueAlgebra` instance the module installs with `attribute [local instance]` (the `ResidueField`
  carrier is a `def` in this mathlib, so instance search does not unfold it to find an algebra).  The
  same line is repeated here: it is what makes the hypothesis's `Module` instance resolvable at all.

  This module is outside every library: it is a spec-side composition check, not part of the port's
  import graph.
-/
import FLTForHuman.FieldTheory.ValuationSubringCompleteSplitting

set_option autoImplicit false

noncomputable section

open IsLocalRing
open ValuationSubring

namespace ValuationSubring.SetAF47CConsumer

attribute [local instance] ValuationSubring.CompleteSplitting.residueAlgebra

/-- **Row 1.** The headline at the smallest complete splitting: `F' = F` (degree one), `ι = Fin 1`,
`O' = ![O]`, `i = 0`.  Injectivity is subsingleton-triviality of `Fin 1`, the prolongation equation is
`comap` of the identity algebra map, and the cardinality bound is `finrank F F = 1 ≤ 1`.  The
conclusion has no `F'` left: every `g ≠ 0` of `F` has an `O`-unit multiple by an element of `F`. -/
theorem consumer_row1_headline_degree_one {F : Type*} [Field F] (O : ValuationSubring F) (g : F)
    (hg : g ≠ 0) : ∃ h : F, O.valuation (h * g) = 1 := by
  have hcomap : O.comap (algebraMap F F) = O := by
    ext x
    rw [ValuationSubring.mem_comap, Algebra.algebraMap_self_apply]
  have hmain : ∃ h : F,
      ((![O] : Fin 1 → ValuationSubring F) 0).valuation (algebraMap F F h * g) = 1 :=
    exists_valuation_mul_eq_one_of_finrank_le_card (F := F) (F' := F) O (ι := Fin 1) ![O]
      (by
        intro i j _
        exact Subsingleton.elim i j)
      (fun i => by
        have hi : i = 0 := Subsingleton.elim i 0
        subst hi
        exact hcomap)
      (by simp) 0 g hg
  exact hmain

/-- **Row 2.** The counting bound `#s + #τ ≤ [F' : F]` at `F' = F`, `R = ⊤`, `S' = {⊤}`,
`τ = Fin 0`, `s = {1}`.  The two families over `Fin 0` are vacuous, `hind`'s unit premise is empty,
and the one-element residue family `{1}` is linearly independent because its index type is a
singleton and its vector is `1 ≠ 0`.  The bound reads `1 + 0 ≤ [F : F]`. -/
theorem consumer_row2_card_add_card_le_finrank (F : Type*) [Field F] :
    (1 : ℕ) ≤ Module.finrank F F := by
  classical
  have h := CompleteSplitting.card_add_card_le_finrank (F := F) (F' := F)
    (R := (⊤ : ValuationSubring F)) (S' := {⊤})
    (by
      intro P hP
      rw [Finset.mem_singleton] at hP
      subst hP
      rfl)
    (Finset.mem_singleton_self ⊤)
    (τ := Fin 0) (clsR := Fin.elim0)
    (fun t => Fin.elim0 t)
    (fun t => Fin.elim0 t)
    (ω := Fin.elim0)
    (fun t => Fin.elim0 t)
    (fun _ _ _ _ _ hunit => by
      obtain ⟨t, -⟩ := hunit
      exact Fin.elim0 t)
    (s := ({1} : Finset (ResidueField ↥(⊤ : ValuationSubring F))))
    (by
      rw [linearIndependent_unique_iff]
      have hsingle : (default : ↥({1} : Finset (ResidueField ↥(⊤ : ValuationSubring F)))) =
          ⟨1, Finset.mem_singleton_self 1⟩ := Subsingleton.elim _ _
      rw [hsingle]
      exact one_ne_zero)
  simp only [Finset.card_singleton, Fintype.card_fin, Nat.add_zero] at h
  exact h

end ValuationSubring.SetAF47CConsumer
