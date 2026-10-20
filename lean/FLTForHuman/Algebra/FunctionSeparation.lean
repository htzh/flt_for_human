/-
  Separation of variables for a function on a finite product, in additive and in
  multiplicative form.

  `Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul`:
  if every coordinate line of `Φ : (∀ i, X i) → ℂ` through a base point `b` — that is
  `t ↦ Φ (update b i t)` for `i ≠ i₀` — is a finite linear combination of `d`
  functions of the `i`-th coordinate alone, then `Φ` itself is a finite sum of
  products `∏ i, Φ (update (β α i) i (t i))` of its own values.

  `Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero`:
  if along each such line the values of `Φ` satisfy one fixed non-trivial linear
  relation `c.1 * Φ (update b i t) + c.2 * Φ (update b' i t) = 0`, then `Φ` is
  multiplicative up to the power `card ι - 1` of a reference value.

  Transcribed verbatim from the pin

  * `Theorems/Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.lean`
    (`P2M/Sol/S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.lean`,
    220 pin lines), and
  * `Theorems/Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean`
    (`P2M/Sol/S_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean`,
    91 pin lines),

  pinned `aa2d8b3`. The pin's `S_` development is `namespace Function.SepFinAux` /
  `namespace Function.FactorAux` under its `Function` namespace; the port drops only
  the `P2MW.S_<stem>` prefix, so the helpers sit in `Function.SepFinAux` and
  `Function.FactorAux` (the outer `Function` is mathlib's own namespace, which is
  what the pin's `p2m_export "Function" …` re-export was papering over). The pin's
  `p2m_*` scaffolding lines (`p2m_export`, `p2m_open`) are dropped, as the order
  requires; they only re-alias `Function.update` and its companions, which are
  mathlib's `Mathlib.Logic.Function.Basic` declarations and are reached directly.

  The mathematics: the first statement is the rank argument for the space spanned by
  the coordinate-wise restrictions (`exists_points_eq_sum_apply_smul`, a
  finite-dimensional space of functions is determined by evaluation at finitely many
  points, proved by induction on the rank), applied once per coordinate; the second
  is the two-term case of the same separation, where the one-dimensional space of
  relations on a line forces the `2 × 2` determinant `f x * g y = f y * g x`.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  Mathlib-first check (2026-10-20): mathlib has neither statement. `rg` over
  `Mathlib/` for `exists_eq_sum_mul_prod_apply_update`, `mul_pow_card_sub_one_eq_mul_prod_update`,
  `exists_points_eq_sum_apply_smul` and `det_eq_of_dep` returns nothing, and no
  concept search for a "separation of variables" / "evaluation-determined subspace"
  lemma finds a more general form. Everything the proofs use is mathlib's own:
  `Function.update` and its `update_self`/`update_of_ne`/`update_eq_iff`/`ne_iff`
  (`Mathlib.Logic.Function.Basic`), `Finsupp.mem_span_range_iff_exists_finsupp`
  (`Mathlib.LinearAlgebra.Finsupp.LinearCombination`),
  `Submodule.finrank_lt_finrank_of_lt`, `Submodule.finrank_eq_zero`,
  `FiniteDimensional.span_of_finite` (`Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`),
  `LinearMap.proj` (`Mathlib.LinearAlgebra.Pi`) and `Finset.piecewise`
  (`Mathlib.Algebra.BigOperators.Group.Finset.Piecewise`).

  Drift against `v4.34.0` — statements untouched, all in proofs/bodies:

  * the pin's file-wide `import Mathlib` becomes the ten named modules above; its
    `p2m_export`/`p2m_open` scaffolding is dropped (it re-aliased mathlib's own
    `Function.update`/`update_of_ne`/`update_eq_iff`/`update_self`/`ne_iff`/
    `support`, which resolve directly in the port's `Function` namespace);
  * port:110, 118 (`exists_points_eq_sum_apply_smul`) and port:182, 184–187
    (`direction_step`): the pin's `haveI : FiniteDimensional …` become `have`
    (`linter.style.haveILetI`'s own suggestion, `haveI`→`have`), and the instance is
    then passed positionally — `ih W' hW'fin hrank`,
    `@Submodule.finiteDimensional_of_le … hspan hWle`, and
    `@exists_points_eq_sum_apply_smul (X i) W hWfin`. The local class hypotheses here
    are *not* reachable by instance search (they are built by
    `FiniteDimensional.span_of_finite` from a finite range), so the explicit
    application is the source fix rather than a `set_option`;
  * port:62: `Mathlib.Data.Complex.Basic` is deprecated in `v4.34.0` and is imported
    as `Mathlib.Basic.Complex.Basic`.

  spec-pin: Theorems/Thm_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.lean
  spec-pin: P2M/Sol/S_Function_exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul.lean
  spec-pin: Theorems/Thm_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean
  spec-pin: P2M/Sol/S_Function_mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero.lean
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Order.Basic

set_option autoImplicit false

namespace Function

namespace SepFinAux

open Finset

/-- A finite-dimensional space of complex-valued functions is spanned by the
evaluation functionals at finitely many points. -/
theorem exists_points_eq_sum_apply_smul {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ W] :
    ∃ (r : ℕ) (s : Fin r → X) (ℓ : Fin r → (X → ℂ)), (∀ j, ℓ j ∈ W) ∧ ∀ f ∈ W, f = ∑ j, f (s j) • ℓ j := by
  classical

  suffices H : ∀ n : ℕ, ∀ (W : Submodule ℂ (X → ℂ)), FiniteDimensional ℂ W → Module.finrank ℂ W ≤ n →
      ∃ (r : ℕ) (s : Fin r → X) (ℓ : Fin r → (X → ℂ)), (∀ j, ℓ j ∈ W) ∧ ∀ f ∈ W, f = ∑ j, f (s j) • ℓ j from
    H _ W inferInstance le_rfl
  intro n
  induction n with
  | zero =>
    intro W _ hW
    have hbot : W = ⊥ := Submodule.finrank_eq_zero.mp (Nat.le_zero.mp hW)
    refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun f hf => ?_⟩
    rw [hbot, Submodule.mem_bot] at hf
    simp [hf]
  | succ n ih =>
    intro W _ hW
    by_cases hbot : W = ⊥
    · refine ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun f hf => ?_⟩
      rw [hbot, Submodule.mem_bot] at hf
      simp [hf]

    obtain ⟨f₀, hf₀W, hf₀⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨x, hx⟩ : ∃ x, f₀ x ≠ 0 := Function.ne_iff.mp hf₀

    let W' : Submodule ℂ (X → ℂ) := W ⊓ LinearMap.ker (LinearMap.proj x : (X → ℂ) →ₗ[ℂ] ℂ)
    have hW'le : W' ≤ W := inf_le_left
    have hW'fin : FiniteDimensional ℂ W' := Submodule.finiteDimensional_of_le hW'le
    have hlt : W' < W := by
      refine lt_of_le_of_ne hW'le fun h => hx ?_
      have : f₀ ∈ W' := h ▸ hf₀W
      exact this.2
    have hrank : Module.finrank ℂ W' ≤ n := by
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    obtain ⟨r, s, ℓ, hℓ, hrep⟩ := ih W' hW'fin hrank

    let ℓ₀ : X → ℂ := (f₀ x)⁻¹ • f₀ - ∑ j, ((f₀ x)⁻¹ * f₀ (s j)) • ℓ j
    have hℓ₀ : ℓ₀ ∈ W :=
      W.sub_mem (W.smul_mem _ hf₀W) (W.sum_mem fun j _ => W.smul_mem _ (hW'le (hℓ j)))
    refine ⟨r + 1, Fin.cons x s, Fin.cons ℓ₀ ℓ, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simpa using hℓ₀
      · intro j; simpa using hW'le (hℓ j)
    · intro f hf
      set c : ℂ := f x * (f₀ x)⁻¹ with hc
      have hmem : f - c • f₀ ∈ W' := by
        refine ⟨W.sub_mem hf (W.smul_mem _ hf₀W), ?_⟩
        show (f - c • f₀) x = 0
        simp [hc, hx]
      have e1 := hrep _ hmem
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]

      have e2 : ∑ j, (f - c • f₀) (s j) • ℓ j = (∑ j, f (s j) • ℓ j) - c • ∑ j, f₀ (s j) • ℓ j := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_smul, Finset.sum_sub_distrib, Finset.smul_sum,
          smul_smul]
      have e3 : f x • ℓ₀ = c • f₀ - c • ∑ j, f₀ (s j) • ℓ j := by
        simp only [ℓ₀, smul_sub, smul_smul, Finset.smul_sum, hc, mul_assoc]
      rw [e3]
      rw [e2] at e1
      have e4 : f = c • f₀ + ((∑ j, f (s j) • ℓ j) - c • ∑ j, f₀ (s j) • ℓ j) := by
        rw [← e1]; abel
      refine e4.trans ?_
      abel

end SepFinAux

namespace SepFinAux

open Finset

variable {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}

omit [Fintype ι] in

/-- One coordinate of the separation: a line of `Φ` that is a finite linear
combination of `d` functions of one variable is a finite sum of products of two
values of `Φ`. -/
theorem direction_step (Φ : (∀ j, X j) → ℂ) (i : ι)
    (h : ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (B : Type) (_ : Fintype B) (sB : B → X i) (aB : B → ℂ) (bB : B → ∀ j, X j),
      ∀ (b : ∀ j, X j) (t : X i),
        Φ (Function.update b i t) = ∑ β, aB β * Φ (Function.update b i (sB β)) * Φ (Function.update (bB β) i t) := by
  classical
  obtain ⟨d, φ, hφ⟩ := h

  let P : (∀ j, X j) → (X i → ℂ) := fun b t => Φ (Function.update b i t)
  let W : Submodule ℂ (X i → ℂ) := Submodule.span ℂ (Set.range P)
  have hWle : W ≤ Submodule.span ℂ (Set.range φ) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨b, rfl⟩
    obtain ⟨c, hc⟩ := hφ b
    have hPb : P b = ∑ k, c k • φ k := by
      funext t
      simp only [P, hc, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [hPb]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have hspan : FiniteDimensional ℂ (Submodule.span ℂ (Set.range φ)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range φ)
  have hWfin : FiniteDimensional ℂ W :=
    @Submodule.finiteDimensional_of_le ℂ (X i → ℂ) _ _ _ W (Submodule.span ℂ (Set.range φ)) hspan hWle

  obtain ⟨r, s, ℓ, hℓW, hrep⟩ := @exists_points_eq_sum_apply_smul (X i) W hWfin
  have hcf : ∀ j, ∃ cj : (∀ j, X j) →₀ ℂ, (cj.sum fun b a => a • P b) = ℓ j := fun j =>
    Finsupp.mem_span_range_iff_exists_finsupp.mp (hℓW j)
  choose cf hcf using hcf
  refine ⟨(Σ j : Fin r, ((cf j).support : Type)), inferInstance, fun x => s x.1, fun x => cf x.1 x.2,
    fun x => (x.2 : ∀ j, X j), fun b t => ?_⟩

  have hPbW : P b ∈ W := Submodule.subset_span ⟨b, rfl⟩
  have e1 : Φ (Function.update b i t) = ∑ j, Φ (Function.update b i (s j)) * ℓ j t := by
    have := congrFun (hrep _ hPbW) t
    simpa only [P, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
  have e2 : ∀ j, ℓ j t = ∑ b' ∈ (cf j).support, cf j b' * Φ (Function.update b' i t) := by
    intro j
    have := congrFun (hcf j) t
    rw [← this, Finsupp.sum, Finset.sum_apply]
    simp only [P, Pi.smul_apply, smul_eq_mul]
  rw [e1, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [e2 j, Finset.mul_sum, ← Finset.sum_coe_sort (cf j).support]
  refine Finset.sum_congr rfl fun b' _ => ?_
  ring

omit [Fintype ι] in

/-- The induction over the coordinate set: `Φ` is a finite sum of products of its
own values on the coordinates in `S` and one value on the complement. -/
theorem main_induction (Φ : (∀ j, X j) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∀ S : Finset ι, i₀ ∉ S →
      ∃ (A : Type) (_ : Fintype A) (coef : A → ℂ) (β : A → ι → ∀ j, X j) (γ : A → ∀ j, X j),
        ∀ t : ∀ j, X j, Φ t = ∑ a, coef a * ((∏ i ∈ S, Φ (Function.update (β a i) i (t i))) * Φ (S.piecewise (γ a) t)) := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    by_cases hne : Nonempty (∀ j, X j)
    · refine ⟨Unit, inferInstance, fun _ => 1, fun _ _ => hne.some, fun _ => hne.some, fun t => ?_⟩
      simp
    · exact ⟨PEmpty, inferInstance, nofun, nofun, nofun, fun t => (hne ⟨t⟩).elim⟩
  | insert i S hiS ih =>
    intro hi₀
    have hii₀ : i ≠ i₀ := fun e => hi₀ (e ▸ Finset.mem_insert_self i S)
    have hi₀S : i₀ ∉ S := fun e => hi₀ (Finset.mem_insert_of_mem e)
    obtain ⟨A, _, coef, β, γ, hA⟩ := ih hi₀S
    obtain ⟨B, _, sB, aB, bB, hB⟩ := direction_step Φ i (h i hii₀)
    refine ⟨A × B, inferInstance, fun p => coef p.1 * aB p.2, fun p => Function.update (β p.1) i (bB p.2),
      fun p => Function.update (γ p.1) i (sB p.2), fun t => ?_⟩

    have key : ∀ a : A, Φ (S.piecewise (γ a) t) =
        ∑ b, aB b * Φ ((insert i S).piecewise (Function.update (γ a) i (sB b)) t) *
          Φ (Function.update (bB b) i (t i)) := by
      intro a
      have h0 : S.piecewise (γ a) t = Function.update (S.piecewise (γ a) t) i (t i) := by
        rw [eq_comm, Function.update_eq_iff]
        exact ⟨(Finset.piecewise_eq_of_notMem _ _ _ hiS).symm, fun _ _ => rfl⟩
      rw [h0, hB]
      refine Finset.sum_congr rfl fun b _ => ?_
      have hpc : S.piecewise (Function.update (γ a) i (sB b)) t = S.piecewise (γ a) t := by
        funext j
        by_cases hj : j ∈ S
        · rw [Finset.piecewise_eq_of_mem _ _ _ hj, Finset.piecewise_eq_of_mem _ _ _ hj, Function.update_of_ne]
          rintro rfl; exact hiS hj
        · rw [Finset.piecewise_eq_of_notMem _ _ _ hj, Finset.piecewise_eq_of_notMem _ _ _ hj]
      congr 2
      rw [Finset.piecewise_insert, Function.update_self, hpc]
    rw [hA t, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    dsimp only
    have hprod : ∏ j ∈ S, Φ (Function.update (Function.update (β a) i (bB b) j) j (t j)) =
        ∏ j ∈ S, Φ (Function.update (β a j) j (t j)) :=
      Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hiS)]
    rw [Finset.prod_insert hiS, Function.update_self, hprod]
    ring

end SepFinAux

end Function

open Function.SepFinAux in
/-- Separation of variables in product form. -/
theorem Function.exists_eq_sum_mul_prod_apply_update_of_forall_exists_forall_apply_update_eq_sum_mul
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∃ (d : ℕ) (φ : Fin d → X i → ℂ), ∀ b : ∀ j, X j, ∃ c : Fin d → ℂ,
      ∀ t : X i, Φ (Function.update b i t) = ∑ k, c k * φ k t) :
    ∃ (m : ℕ) (coef : Fin m → ℂ) (β : Fin m → ι → ∀ j, X j),
      ∀ t : ∀ j, X j, Φ t = ∑ α, coef α * ∏ i, Φ (Function.update (β α i) i (t i)) := by
  classical
  obtain ⟨A, _, coef, β, γ, hA⟩ := main_induction Φ i₀ h (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _)
  let e := Fintype.equivFin A
  refine ⟨Fintype.card A, fun k => coef (e.symm k), fun k => Function.update (β (e.symm k)) i₀ (γ (e.symm k)),
    fun t => ?_⟩
  rw [hA t, ← Equiv.sum_comp e.symm]
  refine Finset.sum_congr rfl fun k _ => ?_
  dsimp only
  have hpw : (Finset.univ.erase i₀).piecewise (γ (e.symm k)) t = Function.update (γ (e.symm k)) i₀ (t i₀) := by
    funext j
    by_cases hj : j = i₀
    · subst hj; rw [Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ (Finset.notMem_erase j _)]
    · rw [Function.update_of_ne hj, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)]
  have hprod : ∏ j ∈ Finset.univ.erase i₀, Φ (Function.update (Function.update (β (e.symm k)) i₀ (γ (e.symm k)) j) j (t j)) =
      ∏ j ∈ Finset.univ.erase i₀, Φ (Function.update (β (e.symm k) j) j (t j)) :=
    Finset.prod_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀), Function.update_self, hprod, hpw]
  ring

namespace Function

namespace FactorAux

/-- Two complex-valued functions satisfying one fixed non-trivial linear relation
pointwise have proportional `2 × 2` determinants. -/
theorem det_eq_of_dep {X : Type} (f g : X → ℂ) (h : ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t, c.1 * f t + c.2 * g t = 0)
    (x y : X) : f x * g y = f y * g x := by
  obtain ⟨c, hc, hfg⟩ := h
  by_cases h1 : c.1 = 0
  · have h2 : c.2 ≠ 0 := by
      intro h2; apply hc; exact Prod.ext h1 h2
    have hg : ∀ t, g t = 0 := fun t => by
      have := hfg t; rw [h1, zero_mul, zero_add] at this
      exact (mul_eq_zero.1 this).resolve_left h2
    simp [hg]
  · have hf : ∀ t, f t = -(c.2 / c.1) * g t := fun t => by
      have := hfg t
      field_simp
      linear_combination this
    rw [hf x, hf y]; ring

end FactorAux

end Function

open Function.FactorAux in
/-- The multiplicative form: a one-parameter family with a fixed linear relation is
multiplicative up to a power of a reference value. -/
theorem Function.mul_pow_card_sub_one_eq_mul_prod_update_of_forall_exists_linearCombination_update_eq_zero
    {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type}
    (Φ : (∀ i, X i) → ℂ) (i₀ : ι)
    (h : ∀ i, i ≠ i₀ → ∀ b b' : ∀ j, X j,
      ∃ c : ℂ × ℂ, c ≠ 0 ∧ ∀ t : X i, c.1 * Φ (Function.update b i t) + c.2 * Φ (Function.update b' i t) = 0)
    (b₀ t : ∀ j, X j) :
    Φ t * Φ b₀ ^ (Fintype.card ι - 1) =
      Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ Finset.univ.erase i₀, Φ (Function.update b₀ i (t i)) := by
  classical

  have main : ∀ S : Finset ι, i₀ ∉ S → ∀ t : ∀ j, X j, (∀ j, j ∉ S → j ≠ i₀ → t j = b₀ j) →
      Φ t * Φ b₀ ^ S.card = Φ (Function.update b₀ i₀ (t i₀)) * ∏ i ∈ S, Φ (Function.update b₀ i (t i)) := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      intro _ t ht
      have hteq : t = Function.update b₀ i₀ (t i₀) := by
        funext j
        by_cases hj : j = i₀
        · subst hj; simp
        · rw [Function.update_of_ne hj]; exact ht j (by simp) hj
      simp only [Finset.card_empty, pow_zero, mul_one, Finset.prod_empty]
      rw [← hteq]
    | insert i S hiS ih =>
      intro hi₀ t ht
      have hii₀ : i ≠ i₀ := fun h => hi₀ (h ▸ Finset.mem_insert_self i S)
      have hi₀S : i₀ ∉ S := fun h => hi₀ (Finset.mem_insert_of_mem h)

      set t' : ∀ j, X j := Function.update t i (b₀ i) with ht'
      have ht'agree : ∀ j, j ∉ S → j ≠ i₀ → t' j = b₀ j := by
        intro j hjS hji₀
        by_cases hji : j = i
        · subst hji; simp [ht']
        · rw [ht', Function.update_of_ne hji]
          exact ht j (by simp [hji, hjS]) hji₀
      have hIH := ih hi₀S t' ht'agree

      have hex : Φ t * Φ b₀ = Φ t' * Φ (Function.update b₀ i (t i)) := by
        have hd := det_eq_of_dep (fun s => Φ (Function.update t i s)) (fun s => Φ (Function.update b₀ i s))
          (h i hii₀ t b₀) (t i) (b₀ i)
        simp only [Function.update_eq_self] at hd
        rw [ht']
        exact hd

      have ht'i₀ : t' i₀ = t i₀ := by rw [ht', Function.update_of_ne (Ne.symm hii₀)]
      have ht'S : ∀ j ∈ S, Function.update b₀ j (t' j) = Function.update b₀ j (t j) := by
        intro j hj
        have hji : j ≠ i := fun h => hiS (h ▸ hj)
        rw [ht', Function.update_of_ne hji]
      rw [Finset.card_insert_of_notMem hiS, pow_succ, ← mul_assoc, mul_comm (Φ t), mul_assoc, hex,
        Finset.prod_insert hiS]
      calc Φ b₀ ^ S.card * (Φ t' * Φ (Function.update b₀ i (t i)))
          = (Φ t' * Φ b₀ ^ S.card) * Φ (Function.update b₀ i (t i)) := by ring
        _ = (Φ (Function.update b₀ i₀ (t' i₀)) * ∏ j ∈ S, Φ (Function.update b₀ j (t' j))) *
              Φ (Function.update b₀ i (t i)) := by rw [hIH]
        _ = Φ (Function.update b₀ i₀ (t i₀)) * (Φ (Function.update b₀ i (t i)) *
              ∏ j ∈ S, Φ (Function.update b₀ j (t j))) := by
            rw [ht'i₀, Finset.prod_congr rfl (fun j hj => by rw [ht'S j hj])]; ring
  have h := main (Finset.univ.erase i₀) (Finset.notMem_erase i₀ _) t (fun j hj hji₀ => absurd (Finset.mem_erase.2 ⟨hji₀, Finset.mem_univ j⟩) hj)
  rwa [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ] at h
