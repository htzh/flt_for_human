/-
  SET-AF83A consumer: the archimedean type submodules, read as directness and as a family.

  **The rows.** `FLTForHuman/AutomorphicForm/Adelic/Cusp/ArchTypeSubmodule.lean` carries the three
  rows of the archimedean type decomposition: `exists_isArchBiFinite_flat` (arch-bi-finiteness
  survives the cuspidal flattening), `exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup`
  (an irreducible constituent of a supremum of arch type submodules sits in one of finitely many
  irreducible arch types) and `typeSubmodule_inf_typeSubmodule_eq_bot` (inequivalent irreducibles
  give disjoint `typeSubmodule`s).

  **The readings.** The third row is an equation; the consumers of such an equation never use it in
  that form. So:

  * Zone 1 — **the intersection is zero**: a function in both type submodules is `0`. This is the
    `Submodule.mem_bot` form, and it is the one a proof of linear independence spends.
  * Zone 2 — **the pair is `Disjoint`**: the form the direct-sum and isotypic-decomposition lemmas
    take, obtained from the equation by `disjoint_iff_inf_le`. Cross-form reading of the same row.
  * Zone 3 — **the flat row at `σ = 0`**: the cuspidal flattening at the central point is still
    arch-bi-finite, with a family that the row does not name.
  * Zone 4 — **the constituent row's family read alone**: at no archimedean generator the row still
    produces a finite family of *irreducible* `ArchRepAt`s. This is the "finitely many arch types"
    half of the row, which is what a consumer of the isotypic decomposition needs; the `∀ S` half is
    left to the row.

  `spec/` is outside every Lake library, so this file is checked by
  `lake env lean spec/AutomorphicFormSetAF83AConsumer.lean` and never enters the build.
-/
import FLTForHuman.AutomorphicForm.Adelic.Cusp.ArchTypeSubmodule

set_option autoImplicit false

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open AutomorphicForm AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ENNReal Classical InnerProductSpace

namespace AutomorphicFormSetAF83AConsumer

/-! ### Zone 1 — an element of both type submodules is zero -/

/-- **Zone 1.** `Submodule.mem_bot` form of the disjointness row: for two inequivalent irreducible
representations of `H`, a function of `ℂ[G]` cannot be a matrix coefficient of both. -/
theorem eq_zero_of_mem_typeSubmodule_inf {H G W W' : Type*} [Group H] [Group G]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ'))
    {x : G → ℂ} (hx : x ∈ typeSubmodule ι ρ ⊓ typeSubmodule ι ρ') : x = 0 := by
  have h := typeSubmodule_inf_typeSubmodule_eq_bot ι ρ ρ' hne
  rw [h] at hx
  simpa using hx

/-! ### Zone 2 — the pair is `Disjoint`, the form the direct-sum lemmas take -/

/-- **Zone 2.** The same row in `Disjoint` form, which is what an isotypic decomposition consumes. -/
theorem disjoint_typeSubmodule {H G W W' : Type*} [Group H] [Group G]
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (ι : H →* G) (ρ : Representation ℂ H W) (ρ' : Representation ℂ H W')
    [ρ.IsIrreducible] [ρ'.IsIrreducible] (hne : IsEmpty (ρ.Equiv ρ')) :
    Disjoint (typeSubmodule ι ρ) (typeSubmodule ι ρ') := by
  rw [disjoint_iff_inf_le, typeSubmodule_inf_typeSubmodule_eq_bot ι ρ ρ' hne]

/-! ### Zone 3 — the flat row at the central point -/

/-- **Zone 3.** `σ = 0`: the cuspidal flattening at the central point keeps arch-bi-finiteness, with
a family the row does not name. -/
theorem exists_isArchBiFinite_flat_zero (F : Type) [Field F] [NumberField F]
    (tys : ArchTypeFamily F) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : IsFactorizableTestFn F f) (hft : IsArchBiFinite F tys f) :
    ∃ tys' : ArchTypeFamily F, IsArchBiFinite F tys' (flat F 0 f) :=
  exists_isArchBiFinite_flat F 0 tys f hf hft

/-! ### Zone 4 — the constituent row's family, read alone -/

/-- **Zone 4.** At the empty archimedean family (`m = 0`) the constituent row still produces a
finite family of irreducible `ArchRepAt`s at `w` — the "finitely many arch types" half of the row. -/
theorem exists_irreducible_archRepAt (F : Type) [Field F] [NumberField F]
    (w : InfinitePlace F) :
    ∃ (r : ℕ) (σs : Fin r → ArchRepAt F w), ∀ j, (σs j).ρ.IsIrreducible := by
  obtain ⟨r, σs, hirr, -⟩ :=
    exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup F w 0 (fun i => i.elim0)
  exact ⟨r, σs, hirr⟩

end AutomorphicFormSetAF83AConsumer
