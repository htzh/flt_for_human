/-
A tower of intermediate fields built by adjoining one element at each step.

If `L : ℕ → IntermediateField F E` and `f : ℕ → E` with `L (n + 1) = F(L n, f n)` — each
level the previous one adjoined its own generator — then the `n`-th level is the field
generated over `F` by the bottom level and the elements adjoined at the steps before it.
The proof is that induction, and its step is mathlib's telescoping identity
`adjoin_insert_adjoin`.

Mathlib-first check (2026-11-04, mathlib `v4.34.0`): the ingredients are in
`Mathlib/FieldTheory/IntermediateField/Adjoin/Defs.lean` — `adjoin_insert_adjoin` (:400),
`adjoin_self` (:441), `adjoin_le_iff` (:55), `adjoin.mono` (:342), `subset_adjoin` — and the
statement is not. The nearest thing in mathlib is `Mathlib/FieldTheory/CardinalEmb.lean`,
whose filtration `E⟮<i⟯ = adjoin F (b ∘ φ '' Iio i)` is *defined* by the flat adjoin, so its
`filtration_succ` (:171) derives the step from the flat form; the direction here — the flat
form from the steps — is the one no mathlib proof needs, and `rg -n "adjoin.*Iio|Iio.*adjoin"
Mathlib/` finds only that file. This module restates nothing.

This is port-owned vocabulary, not pin material: the pin writes the specialisation out as a
`private` helper (`full_le_adjoin_chain`, `S_ModularCurve_functionFieldGeneration.lean:501`)
beside its `hall_all`, and that helper feeds its `jqN_pow_not_mem_full`. It is stated here
in the general form, so a second consumer can use it without copying the induction; the
specialisation at `L n = F^full_{M p ^ n}`, `f n = j(q ^ (p ^ (n + 1)))` stays in the
consumer (`ModularCurve/FunctionFieldGeneration/Capstone.lean`).

No `spec-pin:` directive: the module holds no statement of the pin's, so there is nothing
to diff it against, and it is registered by `spec/unwired_register.py` as tier 3.
-/
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs

set_option autoImplicit false

namespace IntermediateField

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **A tower built one generator at a time.** If every level is the previous one adjoined
its own generator, `L (n + 1) = F(L n, f n)`, then level `n` is generated over `F` by the
bottom level together with the generators adjoined before it. -/
theorem adjoin_eq_adjoin_Iio (L : ℕ → IntermediateField F E) (f : ℕ → E)
    (h : ∀ n, L (n + 1) = adjoin F (insert (f n) (L n))) (n : ℕ) :
    L n = adjoin F ((L 0 : Set E) ∪ f '' Set.Iio n) := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [h k, ih, adjoin_insert_adjoin]
    congr 1
    have hIio : Set.Iio (k + 1) = insert k (Set.Iio k) := by
      ext x
      simp only [Set.mem_Iio, Set.mem_insert_iff]
      omega
    rw [hIio, Set.image_insert_eq]
    ext x
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto

end IntermediateField
