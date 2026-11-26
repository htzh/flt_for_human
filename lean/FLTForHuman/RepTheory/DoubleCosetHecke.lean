/-
  An operator calculus on double cosets.

  For a group `G`, a subgroup `K`, a representation `π` of `G` on an `A`-module `W` and a
  function `f : G → A` with finite support modulo `K`, `heckeFun π K f` is the operator
  `∑ᶠ q : G ⧸ K, f q.out • π q.out`. Because it is indexed by `f` and not by one double
  coset, the whole Hecke algebra acts through one operator: composition is the convolution
  `heckeFun_heckeFun`, and every question about representatives, levels and finiteness is a
  hypothesis on `f` (`HasFiniteCosets`, `IsHeckeFunction`).

  `levelSpace π K χ` is the space of vectors on which `K` acts through the character `χ`;
  `heckeFun_mem_levelSpace` is then the statement that a function invariant on the left under
  `K'` with the twist `χ'` carries the `(K,χ)`-space into the `(K',χ')`-space. The trivial
  character case is `IsHeckeFunction.heckeFun_mem`: a level space is preserved by the operator
  of a bi-invariant function.

  Adapted from `grh/src/Lib/Adelic/Hecke/Basic.lean` of `lsernau/grh-lean`, pinned `72fead1`
  (Copyright 2026 Anthropic, PBC, Apache License 2.0), which states and proves the declarations,
  with the source's `Lib.Base` import (mathlib instantiation-speed settings) dropped. Changes:
  mathlib `v4.34.0` spellings for the `finsum` reindexing lemmas; `heckeFun_heckeFun` is proved
  through `sum_finsum_comm` rather than the source's finite-support rewrites; and
  `levelSpace_anti` carries the character comparison as a hypothesis because the source's
  `Subgroup.inclusion` spelling of the restricted character is not definitional here. The
  source's class sums, its `vol K = 1` mean and its means over compact subgroups are not
  ported, and neither is the source's `isHeckeFunction_doubleCoset`, whose compact-open
  hypothesis is not satisfied by a discrete congruence subgroup: a concrete coset system
  supplies the finiteness through `heckeFun_eq_sum`'s covering hypothesis instead.
-/
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.DoubleCoset
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Coset.Card
import Mathlib.RepresentationTheory.Basic

set_option autoImplicit false

noncomputable section

open Set Function DoubleCoset Finset

namespace DoubleCosetHecke

/-! ## Level spaces, operators and Hecke functions -/

variable {A G W W' : Type*} [Group G] [CommSemiring A] [AddCommMonoid W] [Module A W]
  [AddCommMonoid W'] [Module A W']

/-- For a representation `π` of `G`, a subgroup `K` and a character `χ` of `K`, the submodule
of vectors `v` with `π k v = χ k • v` for all `k` in `K`. -/
def levelSpace (π : Representation A G W) (K : Subgroup G) (χ : K →* A := 1) : Submodule A W where
  carrier := {v : W | ∀ k : K, π k v = χ k • v}
  add_mem' hv hw k := by rw [map_add, hv k, hw k, smul_add]
  zero_mem' k := by rw [map_zero, smul_zero]
  smul_mem' a v hv k := by rw [map_smul, hv k, smul_comm]

variable {π : Representation A G W} {K K' : Subgroup G}

@[simp]
lemma mem_levelSpace {χ : K →* A} {v : W} : v ∈ levelSpace π K χ ↔ ∀ k : K, π k v = χ k • v :=
  .rfl

/-- A linear map that commutes with every `π k` preserves the level space. -/
lemma map_mem_levelSpace_of_commute {χ : K →* A} {v : W} {a : W →ₗ[A] W}
    (hv : v ∈ levelSpace π K χ) (h_comm : ∀ k : K, Commute (π k) a) :
    a v ∈ levelSpace π K χ := by
  refine mem_levelSpace.2 fun k ↦ ?_
  rw [show π k (a v) = a (π k v) from LinearMap.congr_fun (h_comm k).eq v, hv k, map_smul]

/-- A level space for a bigger subgroup is contained in the one for a smaller subgroup, the
character being restricted along the inclusion `K ≤ K'`. -/
lemma levelSpace_anti (hK : K ≤ K') {χ' : K' →* A} {χ : K →* A}
    (hχ : ∀ k : K, χ k = χ' ⟨k.1, hK k.2⟩) : levelSpace π K' χ' ≤ levelSpace π K χ :=
  fun _v hv k ↦ by rw [hχ k]; exact hv ⟨k.1, hK k.2⟩

/-- For a function `f` on `G`, the operator `∑ f(g) π(g)` over chosen representatives `g` of
`G ⧸ K` (zero if infinitely many terms are nonzero). Let `f` be right `K`-invariant and
supported on finitely many cosets `gK`. On a vector fixed by `K` the value does not depend on
the representatives (`heckeFun_eq_sum`), and it is the action of `f` for the measure with
`vol K = 1`. -/
def heckeFun (π : Representation A G W) (K : Subgroup G) (f : G → A) : Module.End A W :=
  ∑ᶠ q : G ⧸ K, f q.out • π q.out

/-- The Hecke operator of the double coset `KgK`: the sum of `π(h)` over chosen
representatives `h` of the cosets `hK` in `KgK` (zero if there are infinitely many). -/
def heckeCoset (π : Representation A G W) (K : Subgroup G) (g : G) : Module.End A W :=
  heckeFun π K ((doubleCoset g K K).indicator 1)

/-- The function `f` is nonzero at the chosen representatives of only finitely many cosets
`gK`. -/
abbrev HasFiniteCosets (K : Subgroup G) (f : G → A) : Prop :=
  (support fun q : G ⧸ K ↦ f q.out).Finite

/-- The function `f` is left and right `K`-invariant and supported on finitely many cosets
`gK`. -/
abbrev IsHeckeFunction (K : Subgroup G) (f : G → A) : Prop :=
  HasFiniteCosets K f ∧ ∀ᵉ (g : G) (k ∈ K), f (g * k) = f g ∧ f (k * g) = f g

/-! ## The operator of a Hecke function -/

/-- The evaluation of a finite sum of endomorphisms, at a vector. -/
lemma sum_apply_end {ι : Type*} (s : Finset ι) (E : ι → Module.End A W) (v : W) :
    (∑ i ∈ s, E i) v = ∑ i ∈ s, E i v := by
  exact map_sum (LinearMap.applyₗ v) E s

/-- If `f` lives on finitely many cosets, its operator is the finite sum over those cosets. -/
lemma heckeFun_eq_sum_toFinset {f : G → A} (h : HasFiniteCosets K f) (v : W) :
    heckeFun π K f v = ∑ q ∈ h.toFinset, f q.out • π q.out v := by
  have h_support :
      support (fun q : G ⧸ K ↦ f q.out • π q.out) ⊆ (h.toFinset : Set (G ⧸ K)) := by
    intro q hq
    simp only [Function.mem_support] at hq
    exact h.mem_toFinset.mpr fun h0 ↦ hq (by simp [h0])
  rw [heckeFun, finsum_eq_finsetSum_of_support_subset _ h_support, sum_apply_end]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [LinearMap.smul_apply]

/-- The value of the operator of `f` at `v`, as a sum over all cosets. -/
lemma heckeFun_apply {f : G → A} (h : HasFiniteCosets K f) (v : W) :
    heckeFun π K f v = ∑ᶠ q : G ⧸ K, f q.out • π q.out v := by
  rw [heckeFun_eq_sum_toFinset h]
  exact (finsum_eq_finsetSum_of_support_subset (fun q : G ⧸ K ↦ f q.out • π q.out v)
    (s := h.toFinset) fun q hq ↦ by
      simp only [Function.mem_support] at hq
      exact h.mem_toFinset.mpr fun h0 ↦ hq (by simp [h0])).symm

/-- A linear map `L` that intertwines `π g` and `π' g` at `v` for all `g` intertwines the two
operators of `f` at `v`. -/
lemma map_heckeFun (L : W →ₗ[A] W') {f : G → A} (h : HasFiniteCosets K f)
    {π' : Representation A G W'} {v : W} (hL : ∀ g : G, L (π g v) = π' g (L v)) :
    L (heckeFun π K f v) = heckeFun π' K f (L v) := by
  rw [heckeFun_eq_sum_toFinset h, heckeFun_eq_sum_toFinset h, map_sum]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [map_smul, hL]

/-- **Any representatives serve.** Let `f (g * k) = f g` for `k ∈ K` and let `v` be fixed by
`K`. If the cosets `r i * K`, `i ∈ s`, are distinct and cover the support of `f`, then `f`
lives on finitely many cosets and its operator sends `v` to `∑ i ∈ s, f (r i) • π (r i) v`. -/
lemma heckeFun_eq_sum {f : G → A} {v : W}
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace π K) {ι : Type*}
    {s : Finset ι} {r : ι → G} (hr : InjOn (fun i : ι ↦ (r i : G ⧸ K)) (s : Set ι))
    (hs : ∀ g : G, f g ≠ 0 → ∃ i ∈ s, (r i : G ⧸ K) = g) :
    HasFiniteCosets K f ∧ heckeFun π K f v = ∑ i ∈ s, f (r i) • π (r i) v := by
  classical
  have support_subset (q : G ⧸ K) (hq : f q.out ≠ 0) : q ∈ s.image fun i ↦ (r i : G ⧸ K) := by
    simpa using hs _ hq
  refine ⟨(toFinite _).subset support_subset, ?_⟩
  have term (g : G) : f (g : G ⧸ K).out • π (g : G ⧸ K).out v = f g • π g v := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    rw [hk, hf, map_mul, Module.End.mul_apply, mem_levelSpace.1 hv k, MonoidHom.one_apply,
      one_smul]
  have h_support : support (fun q : G ⧸ K ↦ f q.out • π q.out) ⊆
      (s.image fun i ↦ (r i : G ⧸ K) : Set (G ⧸ K)) := by
    intro q hq
    simp only [Function.mem_support] at hq
    exact support_subset q fun h0 ↦ hq (by simp [h0])
  rw [heckeFun, finsum_eq_finsetSum_of_support_subset _ h_support, sum_image hr,
    sum_apply_end]
  exact Finset.sum_congr rfl fun i _ ↦ term (r i)

/-- **Any representatives serve, pulled back along a map of groups.** Let `f (g * k) = f g`
for `k ∈ K`, let `v` be fixed by `K`, and let `θ : G' → G` induce an injection
`G' ⧸ J → G ⧸ K` covering the support of `f`. Suppose `f (θ x) = 0` at the chosen
representative `x` of every coset outside the finite set `s`. Then `f` lives on finitely many
cosets, and its operator sends `v` to `∑ f (θ x) π (θ x) v` over the representatives `x` of
the cosets in `s`. -/
lemma heckeFun_eq_sum_pullback {G' : Type*} [Group G'] {J : Subgroup G'} {f : G → A} {v : W}
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace π K) (s : Finset (G' ⧸ J))
    (θ : G' → G) (hθ : ∀ g : G, f g ≠ 0 → ∃ x : G', (θ x : G ⧸ K) = g)
    (h_inj : ∀ a b : G', (θ a)⁻¹ * θ b ∈ K ↔ a⁻¹ * b ∈ J)
    (hs : ∀ q : G' ⧸ J, q ∉ s → f (θ q.out) = 0) :
    HasFiniteCosets K f ∧ heckeFun π K f v = ∑ q ∈ s, f (θ q.out) • π (θ q.out) v := by
  have h_coset (a b : G') : (θ a : G ⧸ K) = θ b ↔ (a : G' ⧸ J) = b := by
    simp [QuotientGroup.eq, h_inj]
  have h_injOn : InjOn (fun q : G' ⧸ J ↦ (θ q.out : G ⧸ K)) (s : Set (G' ⧸ J)) := by
    simp [InjOn, h_coset]
  refine heckeFun_eq_sum hf hv h_injOn fun g hg ↦ ?_
  obtain ⟨x, hx⟩ := hθ g hg
  have h_out : (θ (x : G' ⧸ J).out : G ⧸ K) = g := by simp [← hx, h_coset]
  refine ⟨x, ?_, h_out⟩
  by_contra h_not
  have h_mem : g⁻¹ * θ (x : G' ⧸ J).out ∈ K := QuotientGroup.eq.1 h_out.symm
  apply hg
  rw [← hf g ⟨_, h_mem⟩, mul_inv_cancel_left, hs _ h_not]

/-- Let `a : G' → G` be surjective with `a ⁻¹K = J`, let `f` be right `K`-invariant and `v`
fixed by `K`, and let `F = f ∘ a` be nonzero on finitely many cosets `gJ`. If
`ρ g v = π (a g) v` for all `g`, then the operator of `F` in `ρ` and the operator of `f` in
`π` send `v` to the same vector. -/
lemma heckeFun_comp {G' : Type*} [Group G'] {J : Subgroup G'} {F : G' → A} (a : G' →* G)
    {f : G → A} {v : W} (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hv : v ∈ levelSpace π K) (hF : HasFiniteCosets J F) (ha : Surjective a)
    (hK : ∀ g : G', a g ∈ K ↔ g ∈ J) {ρ : Representation A G' W}
    (hρ : ∀ g : G', ρ g v = π (a g) v) (hF_eq : ∀ g : G', F g = f (a g)) :
    heckeFun ρ J F v = heckeFun π K f v := by
  have h_cover (g : G) (_ : f g ≠ 0) : ∃ x : G', (a x : G ⧸ K) = g :=
    (ha g).imp fun x hx ↦ congrArg QuotientGroup.mk hx
  have h_inj (x y : G') : (a x)⁻¹ * a y ∈ K ↔ x⁻¹ * y ∈ J := by simp [← hK]
  have h_zero (q : G' ⧸ J) (hq : q ∉ hF.toFinset) : f (a q.out) = 0 := by
    simpa [← hF_eq] using hq
  obtain ⟨-, h_sum⟩ := heckeFun_eq_sum_pullback hf hv hF.toFinset a h_cover h_inj h_zero
  rw [h_sum, heckeFun_eq_sum_toFinset hF]
  exact Finset.sum_congr rfl fun q _ ↦ by rw [hF_eq, hρ]

/-- If `f (g * k) = f g` for `k ∈ K` and `f` lives on finitely many cosets `gK`, so does its
left translate `g ↦ f (x⁻¹ * g)`. -/
lemma HasFiniteCosets.comp_inv_mul {f : G → A} (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (x : G) :
    HasFiniteCosets K fun g : G ↦ f (x⁻¹ * g) := by
  have h_value (q : G ⧸ K) : f (x⁻¹ • q).out = f (x⁻¹ * q.out) := by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K (x⁻¹ * q.out)
    rw [← MulAction.Quotient.mk_smul_out, smul_eq_mul, hk, hf]
  refine (hf_fin.preimage (MulAction.injective x⁻¹).injOn).subset fun q hq ↦ ?_
  simpa [Function.mem_support, h_value] using hq

/-- Let `f (g * k) = f g` for `k ∈ K`, let `f` live on finitely many cosets and let `v` be
fixed by `K`. The operator of the left translate `g ↦ f (x⁻¹ * g)` sends `v` to `π x` of the
image of `v` under the operator of `f`. -/
lemma heckeFun_comp_inv_mul {f : G → A} {v : W} (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace π K) (x : G) :
    heckeFun π K (fun g : G ↦ f (x⁻¹ * g)) v = π x (heckeFun π K f v) := by
  have h_right (g : G) (k : K) : f (x⁻¹ * (g * k)) = f (x⁻¹ * g) := by
    rw [← mul_assoc, hf]
  have h_cover (g : G) (_ : f (x⁻¹ * g) ≠ 0) : ∃ y : G, ((x * y : G) : G ⧸ K) = g :=
    ⟨x⁻¹ * g, by simp⟩
  have h_zero (q : G ⧸ K) (hq : q ∉ hf_fin.toFinset) : f (x⁻¹ * (x * q.out)) = 0 := by
    simpa using hq
  obtain ⟨-, h_sum⟩ := heckeFun_eq_sum_pullback (f := fun g : G ↦ f (x⁻¹ * g)) h_right hv
    hf_fin.toFinset (x * ·) h_cover (fun a b ↦ by simp) h_zero
  rw [h_sum, heckeFun_eq_sum_toFinset hf_fin, map_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  rw [show x⁻¹ * (x * q.out) = q.out by simp, map_smul, ← Module.End.mul_apply, ← map_mul]

/-- The convolution of two functions that are nonzero on finitely many cosets is nonzero on
finitely many cosets, if the first one is right `K`-invariant. -/
lemma HasFiniteCosets.convolution {f f' : G → A} (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (h' : HasFiniteCosets K f') :
    HasFiniteCosets K fun x : G ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x) := by
  classical
  refine (Finset.biUnion h'.toFinset fun q ↦
    (hf_fin.comp_inv_mul hf q.out).toFinset).finite_toSet.subset ?_
  intro p hp
  simp only [Function.mem_support, Finset.mem_coe, Finset.mem_biUnion] at hp ⊢
  by_contra h
  simp only [not_exists, not_and] at h
  refine hp (Finset.sum_eq_zero fun q hq ↦ ?_)
  have hz : f (q.out⁻¹ * p.out) = 0 := by
    by_contra hne
    exact h q hq (by simpa [Function.mem_support] using hne)
  rw [hz, mul_zero]

/-- **Composition is convolution.** Let `f` and `f'` live on finitely many cosets `g K`, let
`f` be right `K`-invariant and let `v` be fixed by `K`. Applying the operator of `f` and then
that of `f'` to `v` is the same as applying the operator of
`x ↦ ∑ f' g * f (g⁻¹ * x)`, the sum running over the representatives `g` of the cosets where
`f'` is nonzero. -/
lemma heckeFun_heckeFun {f : G → A} {v : W} (hf_fin : HasFiniteCosets K f)
    (hf : ∀ (g : G) (k : K), f (g * k) = f g) (hv : v ∈ levelSpace π K) {f' : G → A}
    (h' : HasFiniteCosets K f') :
    heckeFun π K f' (heckeFun π K f v) =
      heckeFun π K (fun x : G ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) v := by
  classical
  have hfin (q : G ⧸ K) :
      HasFiniteSupport fun p : G ⧸ K ↦ f (q.out⁻¹ * p.out) • π p.out v :=
    (hf_fin.comp_inv_mul hf q.out).subset fun p hp ↦ by
      simp only [Function.mem_support] at hp ⊢
      exact fun h0 ↦ hp (by rw [h0, zero_smul])
  have hfin' (q : G ⧸ K) :
      HasFiniteSupport fun p : G ⧸ K ↦ (f' q.out * f (q.out⁻¹ * p.out)) • π p.out v := by
    refine (hfin q).subset ?_
    intro p hp
    simp only [Function.mem_support] at hp ⊢
    exact fun h ↦ hp (by rw [mul_smul, h, smul_zero])
  have hL : heckeFun π K f' (heckeFun π K f v) =
      ∑ q ∈ h'.toFinset, ∑ᶠ p : G ⧸ K, (f' q.out * f (q.out⁻¹ * p.out)) • π p.out v := by
    rw [heckeFun_eq_sum_toFinset h']
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← heckeFun_comp_inv_mul hf_fin hf hv q.out,
      heckeFun_apply (hf_fin.comp_inv_mul hf q.out), smul_finsum' (f' q.out) (hfin q)]
    exact finsum_congr fun p ↦ by rw [mul_smul]
  have hR : heckeFun π K (fun x : G ↦ ∑ q ∈ h'.toFinset, f' q.out * f (q.out⁻¹ * x)) v =
      ∑ q ∈ h'.toFinset, ∑ᶠ p : G ⧸ K, (f' q.out * f (q.out⁻¹ * p.out)) • π p.out v := by
    rw [heckeFun_apply (hf_fin.convolution hf h')]
    simp only [Finset.sum_smul]
    exact finsum_sum_comm h'.toFinset
      (fun (p : G ⧸ K) (q : G ⧸ K) ↦ (f' q.out * f (q.out⁻¹ * p.out)) • π p.out v)
      fun q _ ↦ hfin' q
  rw [hL, hR]

/-- Let `f` live on finitely many cosets `g K` with `f (g * k) = f g` for `k ∈ K` and
`χ' k * f (k * g) = f g` for `k ∈ K'`. The operator of `f` sends a vector fixed by `K` into
the level space of `(K', χ')`, where each `k ∈ K'` acts as the scalar `χ' k`. -/
lemma heckeFun_mem_levelSpace {f : G → A} {χ' : K' →* A} {v : W}
    (hf_fin : HasFiniteCosets K f) (hf : ∀ (g : G) (k : K), f (g * k) = f g)
    (hf_left : ∀ (g : G) (k : K'), χ' k * f (k * g) = f g) (hv : v ∈ levelSpace π K) :
    heckeFun π K f v ∈ levelSpace π K' χ' := by
  refine mem_levelSpace.2 fun k ↦ ?_
  have h_translate (g : G) : f ((k : G)⁻¹ * g) = χ' k * f g := by
    simp [← hf_left ((k : G)⁻¹ * g) k]
  have h_scale : heckeFun π K (fun g : G ↦ f ((k : G)⁻¹ * g)) = χ' k • heckeFun π K f := by
    ext v
    rw [heckeFun_apply (hf_fin.comp_inv_mul hf (k : G)), LinearMap.smul_apply,
      heckeFun_apply hf_fin, smul_finsum' (χ' k) (hf_fin.subset fun q hq ↦ by
        simp only [Function.mem_support] at hq ⊢
        exact fun h0 ↦ hq (by rw [h0, zero_smul]))]
    exact finsum_congr fun q ↦ by rw [h_translate, mul_smul]
  rw [← heckeFun_comp_inv_mul hf_fin hf hv k, h_scale, LinearMap.smul_apply]

/-- The operator of a `K`-bi-invariant function on finitely many cosets preserves the space of
vectors fixed by `K`. -/
lemma IsHeckeFunction.heckeFun_mem {f : G → A} {v : W} (hv : v ∈ levelSpace π K)
    (hb : IsHeckeFunction K f) : heckeFun π K f v ∈ levelSpace π K := by
  obtain ⟨h_finite, h_inv⟩ := hb
  exact heckeFun_mem_levelSpace h_finite (fun g k ↦ (h_inv g k k.2).1)
    (fun g k ↦ by simp [(h_inv g k k.2).2]) hv

end DoubleCosetHecke

end
