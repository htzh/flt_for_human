/-
  The `σ`-twisted centralizer of an element of a group.

  `sigmaCentralizer σ δ` is the subgroup of `G` consisting of the `t` with
  `t * δ * (σ t)⁻¹ = δ`, i.e. the fixed points of the twisted conjugation
  `t ↦ δ * σ t * δ⁻¹`; `sigmaCentralizer_id` identifies it with the ordinary
  centralizer of `{δ}` and `sigmaCentralizer_one_eq_bot` with the trivial subgroup for the
  trivial `σ`.

  Transcribed from the pin's `Definitions/Def_AutomorphicForm_SigmaCentralizer.lean` (pinned
  `aa2d8b3`, 61 lines / 6 declarations), whole and at the pin's names, with a `-- pin:`
  provenance comment on every declaration.

  ## Substitutions against mathlib `v4.34.0`

  | pin declaration | mathlib `v4.34.0` | action |
  |---|---|---|
  | (proof use) `Set.mem_setOf_eq` | `Set.mem_ofPred_eq` | substituted in the `one_mem'`/`mul_mem'`/`inv_mem'` proofs of `sigmaCentralizer` — the pin's name is deprecated |

  The twisted centralizer itself is not in mathlib (`Subgroup.centralizer` is the untwisted
  special case, and `sigmaCentralizer_id` relates the two); every declaration is transcribed
  at the pin's name.  The pin's `import Mathlib.GroupTheory.Subgroup.Centralizer` and
  `import Mathlib.Tactic.Group` are already explicit.  The pin's implicit-variable option is
  dropped: the package's `lakefile.lean` already sets `autoImplicit` to `false` for the
  whole library and the edit loop passes `-DautoImplicit=false`.
-/
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Tactic.Group

set_option autoImplicit false

namespace AutomorphicForm

variable {G : Type*} [Group G]

-- pin: sigmaCentralizer (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:10)
def sigmaCentralizer (σ : G →* G) (δ : G) : Subgroup G where
  carrier := {t | t * δ * (σ t)⁻¹ = δ}
  one_mem' := by
    simp only [Set.mem_ofPred_eq, one_mul, map_one, inv_one, mul_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    have key : a * b * δ * (σ (a * b))⁻¹ = a * (b * δ * (σ b)⁻¹) * (σ a)⁻¹ := by
      simp only [map_mul, mul_inv_rev]
      group
    rw [key, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [map_inv, inv_inv]
    have h2 : δ * σ a = a * δ := by
      calc δ * σ a = (a * δ * (σ a)⁻¹) * σ a := by rw [ha]
        _ = a * δ := by group
    calc a⁻¹ * δ * σ a = a⁻¹ * (δ * σ a) := by group
      _ = a⁻¹ * (a * δ) := by rw [h2]
      _ = δ := by group

-- pin: mem_sigmaCentralizer_iff (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:32)
@[simp] theorem mem_sigmaCentralizer_iff {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t * δ * (σ t)⁻¹ = δ := Iff.rfl

-- pin: mem_sigmaCentralizer_iff_fixed (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:35)
theorem mem_sigmaCentralizer_iff_fixed {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ δ * σ t * δ⁻¹ = t := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul]
  exact eq_comm

-- pin: mem_sigmaCentralizer_iff_inv (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:40)
theorem mem_sigmaCentralizer_iff_inv {σ : G →* G} {δ t : G} :
    t ∈ sigmaCentralizer σ δ ↔ t⁻¹ * δ * σ t = δ := by
  rw [mem_sigmaCentralizer_iff, mul_inv_eq_iff_eq_mul, mul_assoc, inv_mul_eq_iff_eq_mul]
  exact eq_comm

-- pin: sigmaCentralizer_id (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:45)
theorem sigmaCentralizer_id (δ : G) :
    sigmaCentralizer (MonoidHom.id G) δ = Subgroup.centralizer {δ} := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_centralizer_singleton_iff, MonoidHom.id_apply,
    mul_inv_eq_iff_eq_mul]

-- pin: sigmaCentralizer_one_eq_bot (Definitions/Def_AutomorphicForm_SigmaCentralizer.lean:51)
theorem sigmaCentralizer_one_eq_bot (δ : G) :
    sigmaCentralizer (1 : G →* G) δ = ⊥ := by
  ext t
  rw [mem_sigmaCentralizer_iff, Subgroup.mem_bot]
  constructor
  · intro h
    have h1 : t * δ = δ := by
      simpa using h
    exact mul_right_cancel (by rw [one_mul]; exact h1)
  · rintro rfl
    simp
