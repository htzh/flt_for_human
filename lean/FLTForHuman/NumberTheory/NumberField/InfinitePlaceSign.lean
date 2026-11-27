/-
The sign of the norm is the product of the real embeddings' signs.

`NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal`: for `x ≠ 0`,
`sign (N x) = ∏_{w real} sign (embedding_of_isReal w x)` — the sign bookkeeping the archimedean
positivity arguments use, and a leaf with project citers outside this column.

Home `NumberTheory/NumberField/InfinitePlaceSign.lean` (new).

## The rows

* `NumberField.InfinitePlace.sign_norm_eq_prod_sign_embedding_of_isReal` — 94 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean>

spec-pin: Theorems/Thm_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean
spec-pin: P2M/Sol/S_NumberField_InfinitePlace_sign_norm_eq_prod_sign_embedding_of_isReal.lean

## Port notes (order AF107F)

* **Surface = the pin's.** 5 declarations, 5 public / 0 private, against the pin's 6 entries
  (`Theorems/Thm_…` + `S_…`'s `placeFactor`, `prod_fiber_eq`, `norm_eq_prod_placeFactor`, `main`,
  `solution` — the last being the same statement as the `Thm_…` wrapper). 6 − 1 = 5.
* **`check_port`**: 5 ok, 0 mismatch, 0 missing, 0 own, 0 kw.
* **Substitutions**: none; the whole proof is mathlib's own `InfinitePlace`/`ComplexEmbedding`
  API (`mk_eq_iff`, `mk_conjugate_eq`, `conjugate_coe_eq`, `Algebra.norm_eq_prod_embeddings`,
  `Finset.prod_fiberwise`), and the scaffold's import list carried it — no import added, and in
  particular the pin's bare `import Mathlib` was **not** transcribed.
* **API drift** (`v4.33.1` → `v4.34.0`): `dif_pos`/`dif_neg` are deprecated in favour of
  `dite_eq_left`/`dite_eq_right`; the four uses were renamed and nothing else changed.
* **Namespaces**: the pin's generated `P2mSignNorm` label is replaced by
  `NumberField.InfinitePlace`; the pin's declaration names are kept, so `main` is public as
  `NumberField.InfinitePlace.main`, exactly as in the pin's `S_` file.
* **Axioms**: all 5 public declarations depend on a subset of
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* **`dedup --within`**: 1 cluster, 10 lines — `main` ↔ `sign_norm_eq_prod_sign_embedding_of_isReal`
  (identical statements). This is the pin's own headline↔engine pair, kept for faithfulness.
* **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe (recorded, never installed)**: downward ladder 40000 / 20000 / 10000 / 5000
  pass, 1000 fails — at `main`'s
  `rw [← Fintype.prod_subtype_mul_prod_subtype …]` (`isDefEq`). Module floor passes at
  1000, so the cost is in the proof term, not the types.
-/

import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Basic.Real.Sign
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

open NumberField NumberField.InfinitePlace
open scoped Classical

set_option autoImplicit false

namespace NumberField.InfinitePlace

noncomputable section

/-- The archimedean factor of the norm at a place: the real embedding at a real place, and the
squared complex norm at a complex one. -/
noncomputable def placeFactor {K : Type} [Field K] (w : InfinitePlace K) (x : K) : ℝ :=
  if hw : IsReal w then embedding_of_isReal hw x else Complex.normSq (w.embedding x)

theorem prod_fiber_eq {K : Type} [Field K] [NumberField K] (w : InfinitePlace K) (x : K) :
    (∏ φ ∈ ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ)), φ x) = (placeFactor w x : ℂ) := by
  classical
  have hfibset : ({φ | InfinitePlace.mk φ = w} : Finset (K →+* ℂ))
      = {w.embedding, NumberField.ComplexEmbedding.conjugate w.embedding} := by
    ext φ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      have h' : InfinitePlace.mk φ = InfinitePlace.mk w.embedding :=
        h.trans (InfinitePlace.mk_embedding w).symm
      rcases InfinitePlace.mk_eq_iff.mp h' with h1 | h2
      · exact Or.inl h1
      · exact Or.inr ((star_star φ).symm.trans (congrArg star h2))
    · rintro (h | h)
      · rw [h, InfinitePlace.mk_embedding]
      · rw [h, InfinitePlace.mk_conjugate_eq, InfinitePlace.mk_embedding]
  by_cases hw : InfinitePlace.IsReal w
  · have hre : NumberField.ComplexEmbedding.conjugate w.embedding = w.embedding :=
      NumberField.ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    rw [hfibset, hre, Finset.insert_eq_self.mpr (Finset.mem_singleton_self _),
      Finset.prod_singleton, placeFactor, dite_eq_left hw, InfinitePlace.embedding_of_isReal_apply hw]
  · have hne : w.embedding ≠ NumberField.ComplexEmbedding.conjugate w.embedding := by
      intro h
      exact hw (InfinitePlace.isReal_iff.mpr
        (NumberField.ComplexEmbedding.isReal_iff.mpr h.symm))
    rw [hfibset, Finset.prod_pair hne, NumberField.ComplexEmbedding.conjugate_coe_eq,
      Complex.mul_conj, placeFactor, dite_eq_right hw]

theorem norm_eq_prod_placeFactor {K : Type} [Field K] [NumberField K] (x : K) :
    ((Algebra.norm ℚ x : ℚ) : ℝ) = ∏ w : InfinitePlace K, placeFactor w x := by
  classical
  have htot : algebraMap ℚ ℂ (Algebra.norm ℚ x) =
      ((∏ w : InfinitePlace K, placeFactor w x : ℝ) : ℂ) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x,
      ← Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ) (fun φ : K →+* ℂ => φ x)
        (fun σ : K →ₐ[ℚ] ℂ => σ x)
        (fun φ => by simp [RingHom.equivRatAlgHom_apply]),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ x),
      Finset.prod_congr rfl fun w _ => prod_fiber_eq w x, ← Complex.ofReal_prod]
  have hofreal : (((Algebra.norm ℚ x : ℚ) : ℝ) : ℂ) =
      ((∏ w : InfinitePlace K, placeFactor w x : ℝ) : ℂ) := by
    rw [← htot, eq_ratCast (algebraMap ℚ ℂ) (Algebra.norm ℚ x), Complex.ofReal_ratCast]
  exact Complex.ofReal_inj.mp hofreal

theorem main (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) := by
  have hcast : SignType.sign (Algebra.norm ℚ x) = SignType.sign ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    rcases lt_trichotomy (Algebra.norm ℚ x) 0 with h | h | h
    · rw [sign_neg h, sign_neg (by exact_mod_cast h)]
    · rw [h, sign_zero, Rat.cast_zero, sign_zero]
    · rw [sign_pos h, sign_pos (by exact_mod_cast h)]
  rw [hcast, norm_eq_prod_placeFactor x]
  rw [show SignType.sign (∏ w : InfinitePlace K, placeFactor w x) =
      ∏ w : InfinitePlace K, SignType.sign (placeFactor w x) from map_prod signHom _ _]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun w : InfinitePlace K => IsReal w)]
  have hcomplex : ∏ w : {w : InfinitePlace K // ¬ IsReal w}, SignType.sign (placeFactor w.1 x) = 1 := by
    refine Finset.prod_eq_one fun w _ => ?_
    rw [placeFactor, dite_eq_right w.2]
    apply sign_pos
    apply Complex.normSq_pos.mpr
    rw [← map_zero w.1.embedding]
    exact fun h => hx (w.1.embedding.injective h)
  rw [hcomplex, mul_one]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [placeFactor, dite_eq_left w.2]

open scoped Classical in
theorem sign_norm_eq_prod_sign_embedding_of_isReal
    (K : Type) [Field K] [NumberField K] {x : K} (hx : x ≠ 0) :
    SignType.sign (Algebra.norm ℚ x) =
      ∏ w : {w : InfinitePlace K // w.IsReal}, SignType.sign (embedding_of_isReal w.2 x) :=
  main K hx

end

end NumberField.InfinitePlace
