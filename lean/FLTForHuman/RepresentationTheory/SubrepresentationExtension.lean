/-
  Extending a `G`-invariant, `H`-equivariant functional on a subrepresentation to the
  whole representation.

  Let `ι : H →* G` be an injective group homomorphism, `ρ` a complex representation of
  `H` on `W` and `P ≤ W` an `H`-stable subspace. A linear functional `T` on `P` with
  values in functions on `G`, twisted by `ι` (`T (ρ k v) x = T v (x * ι k)`), extends to
  a linear functional `T'` on `W` whose twist-invariance holds on all of `W` and whose
  restriction to `P` is `T`.

  The route is the pin's and is a coset decomposition, not an averaging argument: a set
  of coset representatives `sec : G → G` of the subgroup `ι.range` (Kawada's
  `Quotient.out`) and the complementary factor `kof : G → H` with `x = sec x * ι (kof x)`
  turn a linear projection `π : W → P` (any complement of `P`) into the extension
  `T' v x = T (π (ρ (kof x) v)) (sec x)`; the twisting law follows from
  `sec (x * ι k) = sec x` and `kof (x * ι k) = kof x * k`.

  Transcribed verbatim from the pin's node `Representation.exists_extend_forall_apply_mul_of_injective`
  — `Theorems/Thm_Representation_exists_extend_forall_apply_mul_of_injective.lean` (the
  statement authority) and `P2M/Sol/S_Representation_exists_extend_forall_apply_mul_of_injective.lean`
  (69 pin lines, pinned `aa2d8b3`). The pin's public target is its `solution` tail; the
  port keeps the wrapper's statement verbatim and strips the pin's `P2MW.S_…` wrapper namespace, and
  drops `import P2M.Util` (nothing of it is used).

  Mathlib-first audit (one line per declaration; the pin's helper-free proof has no
  helper declarations to audit):

  * `Representation.exists_extend_forall_apply_mul_of_injective` — searched mathlib for
    an extension of a linear map/functional along an injective monoid hom and for a
    twisted-invariance extension on `Representation` (`rg -n --multiline
    'exists_extend.*injective|LinearMap.*extend.*injective|forall_apply_mul' Mathlib`):
    nothing. Mathlib supplies the two constituents used verbatim — coset
    representatives `QuotientGroup.mk_out_eq_mul` (`GroupTheory/Coset/Defs.lean:216`)
    and complements/projections `Submodule.exists_isCompl`
    (`LinearAlgebra/Basis/VectorSpace.lean:280`), `Submodule.linearProjOfIsCompl`
    (`LinearAlgebra/Projection.lean:347`) — but states no such extension theorem.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_Representation_exists_extend_forall_apply_mul_of_injective.lean
  spec-pin: P2M/Sol/S_Representation_exists_extend_forall_apply_mul_of_injective.lean
-/

import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Projection
import Mathlib.RepresentationTheory.Basic

set_option autoImplicit false

universe u v w


theorem Representation.exists_extend_forall_apply_mul_of_injective
    {H : Type u} {G : Type v} [Group H] [Group G] {W : Type w} [AddCommGroup W] [Module ℂ W]
    (ι : H →* G) (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ k : H, ∀ v ∈ P, ρ k v ∈ P)
    (T : P →ₗ[ℂ] (G → ℂ))
    (hT : ∀ (k : H) (v : P) (x : G), T ⟨ρ k v, hP k v v.2⟩ x = T v (x * ι k)) :
    ∃ T' : W →ₗ[ℂ] (G → ℂ),
      (∀ (k : H) (v : W) (x : G), T' (ρ k v) x = T' v (x * ι k)) ∧ ∀ v : P, T' v = T v := by
  classical
  set S : Subgroup G := ι.range with hS

  let sec : G → G := fun x => (QuotientGroup.mk x : G ⧸ S).out
  have hx : ∀ x : G, ∃ k : H, x = sec x * ι k := by
    intro x
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul S x
    obtain ⟨k, hk⟩ := h.2
    refine ⟨k⁻¹, ?_⟩
    show x = (QuotientGroup.mk x : G ⧸ S).out * ι k⁻¹
    rw [hh, map_inv, hk, mul_inv_cancel_right]
  let kof : G → H := fun x => (hx x).choose
  have hkof : ∀ x, x = sec x * ι (kof x) := fun x => (hx x).choose_spec
  have hsec : ∀ (x : G) (k : H), sec (x * ι k) = sec x := by
    intro x k
    show (QuotientGroup.mk (x * ι k) : G ⧸ S).out = (QuotientGroup.mk x : G ⧸ S).out
    congr 1
    apply QuotientGroup.eq.mpr
    refine ⟨k⁻¹, ?_⟩
    rw [map_inv]; group
  have hkof_mul : ∀ (x : G) (k : H), kof (x * ι k) = kof x * k := by
    intro x k
    apply hι
    have h1 := hkof (x * ι k)
    rw [hsec] at h1
    have h2 := hkof x

    rw [map_mul]
    apply mul_left_cancel (a := sec x)
    rw [← mul_assoc, ← h2]; exact h1.symm

  obtain ⟨Pc, hPc⟩ := Submodule.exists_isCompl P
  let π : W →ₗ[ℂ] P := Submodule.projectionOnto (p := P) (q := Pc) hPc
  have hπ : ∀ v : P, π v = v := fun v => Submodule.projectionOnto_apply_left hPc v
  let ℓ : G → W →ₗ[ℂ] ℂ := fun r => (LinearMap.proj r).comp (T.comp π)
  have hℓ : ∀ (r : G) (v : P), ℓ r v = T v r := fun r v => by
    simp only [ℓ, LinearMap.comp_apply, LinearMap.proj_apply, hπ]

  let T' : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun v x => ℓ (sec x) (ρ (kof x) v)
      map_add' := fun v w => by funext x; simp only [map_add, Pi.add_apply]
      map_smul' := fun c v => by funext x; simp only [map_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
  refine ⟨T', ?_, ?_⟩
  · intro k v x
    show ℓ (sec x) (ρ (kof x) (ρ k v)) = ℓ (sec (x * ι k)) (ρ (kof (x * ι k)) v)
    rw [hsec, hkof_mul, map_mul]; rfl
  · intro v
    funext x
    show ℓ (sec x) (ρ (kof x) v) = T v x
    have hmem : ρ (kof x) v ∈ P := hP _ _ v.2
    have : ℓ (sec x) (ρ (kof x) (v : W)) = ℓ (sec x) ((⟨ρ (kof x) v, hmem⟩ : P) : W) := rfl
    rw [this, hℓ, hT, ← hkof]

