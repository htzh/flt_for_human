/-
  The coset sum of a Hecke representative system, and its level invariance.

  The Hecke operator of a double coset `K g K` is the sum of the slashes by representatives of the
  left cosets of `K` inside `K g K`. Everything a family has to say about its operator is
  geometric, and it is exactly three statements: the representatives lie in `K g K`, distinct
  representatives lie in distinct left cosets, and every element of `K g K` lies in the left coset
  of a representative. That is the structure `Transversal` below, and this module proves what the
  three statements buy: the level invariance (`Transversal.slash_invariant`) and, in the carrier
  section, the two facts that put the coset sum into the abstract calculus — the slash action as a
  representation of `GL(2,ℝ)⁺` (`slashRep`, by the inverse action) and the level-space dictionary
  (`mem_levelSpace_slashRep`). The identification of the coset sum with the abstract double-coset
  operator is the next slice of this module and is specified in
  `topics/hecke/TOPIC-abstract-coset-calculus.md` §5.

  Nothing in `Transversal.slash_invariant` goes through the group `Gᵐᵒᵖ`, a coset quotient, a
  double-coset witness or a representation: the sum is a sum of functions and the argument is
  `F ∣ (r i * γ) = F ∣ (κ i * r (σ i)) = F ∣ r (σ i)`, reindexed by the permutation `σ` of the
  index set. The abstract calculus is needed only to name the operator.

  The weight `k` slash action on `ℍ → ℂ` is mathlib's (`ModularForm ∣[k]`), so this module imports
  it rather than restating it.
-/
import Mathlib.NumberTheory.ModularForms.SlashActions
import FLTForHuman.RepTheory.DoubleCosetHecke
import FLTForHuman.RepTheory.LocalLanglands.HeckePair

set_option autoImplicit false

noncomputable section

open scoped ModularForm BigOperators Pointwise

open Function UpperHalfPlane

namespace HeckeCoset

variable {G : Type*} [Group G]

/-- A finite family of representatives of the **left** cosets of `K` in the double coset `K g K`:
every representative lies in `K g K`, two representatives lying in the same left coset `K r` are
equal, and every element of `K g K` lies in the left coset of some representative. The left cosets
of the representatives are then exactly the cosets of `K` inside `K g K`, which is what makes the
coset sum well defined and level-invariant. -/
structure Transversal (K : Subgroup G) (g : G) (ι : Type*) [Fintype ι] where
  /-- The representatives. -/
  r : ι → G
  /-- Every representative lies in the double coset `K g K`. -/
  mem : ∀ i, r i ∈ HeckePair.doubleCoset K g
  /-- Distinct representatives lie in distinct left cosets. -/
  distinct : ∀ i j, r i * (r j)⁻¹ ∈ K → i = j
  /-- Every element of the double coset lies in the left coset of a representative. -/
  cover : ∀ x ∈ HeckePair.doubleCoset K g, ∃ i, x * (r i)⁻¹ ∈ K

namespace Transversal

variable {ι : Type*} [Fintype ι]
variable {K : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}

/-- **The coset sum is level-invariant.** Right multiplication by `γ ∈ K` moves each representative
into the left coset of another one — `r i * γ = κ i * r (σ i)` with `κ i ∈ K` — so after reindexing
by `σ` the sum is unchanged, and each `r i` is fixed by `F`'s level invariance up to `κ i`. The
permutation `σ` and the cocycle `κ` are *derived* from the three geometric statements, so a family
states its cosets once and gets invariance without restating this argument. -/
theorem slash_invariant {k : ℤ} (T : Transversal K g ι)
    {γ : GL (Fin 2) ℝ} (hγ : γ ∈ K) {F : ℍ → ℂ} (hF : ∀ γ ∈ K, F ∣[k] γ = F) :
    (∑ i, F ∣[k] T.r i) ∣[k] γ = ∑ i, F ∣[k] T.r i := by
  classical
  have hD (i : ι) : T.r i * γ ∈ HeckePair.doubleCoset K g :=
    HeckePair.doubleCoset_mul_mem (T.mem i) hγ
  choose σ hσ using fun i => T.cover (T.r i * γ) (hD i)
  set κ : ι → GL (Fin 2) ℝ := fun i ↦ (T.r i * γ) * (T.r (σ i))⁻¹
  have hκ : ∀ i, κ i ∈ K := hσ
  have hr (i : ι) : T.r i = κ i * T.r (σ i) * γ⁻¹ := by
    show T.r i = ((T.r i * γ) * (T.r (σ i))⁻¹) * T.r (σ i) * γ⁻¹
    group
  have hterm (i : ι) : F ∣[k] (T.r i * γ) = F ∣[k] T.r (σ i) := by
    rw [show T.r i * γ = κ i * T.r (σ i) from by rw [hr i]; group,
      SlashAction.slash_mul, hF _ (hκ i)]
  have hinj : Injective σ := by
    intro i j hij
    refine T.distinct i j ?_
    have h : T.r i * (T.r j)⁻¹ = κ i * (κ j)⁻¹ := by
      rw [hr i, hr j, hij]
      group
    rw [h]
    exact K.mul_mem (hκ i) (K.inv_mem (hκ j))
  have hbij : Bijective σ := Finite.injective_iff_bijective.mp hinj
  calc (∑ i, F ∣[k] T.r i) ∣[k] γ
      = ∑ i, (F ∣[k] T.r i) ∣[k] γ := SlashAction.sum_slash k γ
    _ = ∑ i, F ∣[k] (T.r i * γ) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [SlashAction.slash_mul]
    _ = ∑ i, F ∣[k] T.r (σ i) := Finset.sum_congr rfl fun i _ => hterm i
    _ = ∑ i, F ∣[k] T.r i := Fintype.sum_bijective σ hbij _ _ fun i => rfl

end Transversal


namespace Transversal

variable {G : Type*} [Group G]

/-- The subgroup of `K` fixing the left coset of `g`: `K ⊓ g⁻¹ K g`. -/
def stabiliser (K : Subgroup G) (g : G) : Subgroup ↥K :=
  (K ⊓ K.comap (MulAut.conj g).toMonoidHom).subgroupOf K

theorem mem_stabiliser {K : Subgroup G} {g : G} {x : ↥K} :
    x ∈ stabiliser K g ↔ ((x : G) ∈ K ∧ g * (x : G) * g⁻¹ ∈ K) := by
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := Subgroup.mem_subgroupOf.mp h
    have h3 : (MulAut.conj g).toMonoidHom (x : G) ∈ K := Subgroup.mem_comap.mp h2
    exact ⟨h1, by simpa [MulAut.conj_apply] using h3⟩
  · rintro ⟨h1, h2⟩
    exact Subgroup.mem_subgroupOf.mpr
      ⟨h1, Subgroup.mem_comap.mpr (by simpa [MulAut.conj_apply] using h2)⟩

/-- **Every family is a level quotient.** For any subgroup `K`, any `g`, and any level subgroup
`J ≤ K` with `J = K ⊓ g⁻¹Kg`, the finite family `c ↦ g * c⁻¹` over `K ⧸ J` is a transversal of
`K g K`: it lies in the double coset by construction, distinct classes give distinct left cosets
because `J` *is* the stabiliser, and exhaustiveness is the quotient's `out` map. A family therefore
does not prove the three geometric facts at all — it only has to identify its own level subgroup
with `K ⊓ g⁻¹Kg` and its own index with this quotient. -/
noncomputable def ofQuotient (K : Subgroup G) (g : G) [Fintype (↥K ⧸ stabiliser K g)] :
    Transversal K g (↥K ⧸ stabiliser K g) where
  r c := g * (((c.out : ↥K) : G))⁻¹
  mem c := HeckePair.mem_doubleCoset_iff.mpr
    ⟨1, one_mem K, (((c.out : ↥K) : G))⁻¹, K.inv_mem c.out.2, by group⟩
  distinct a b hab := by
    have hconj : g * ((((a.out : ↥K) : G))⁻¹ * (((b.out : ↥K) : G))) * g⁻¹ ∈ K := by
      have h := hab
      rw [show (g * (((a.out : ↥K) : G))⁻¹) * (g * (((b.out : ↥K) : G))⁻¹)⁻¹
          = g * ((((a.out : ↥K) : G))⁻¹ * (((b.out : ↥K) : G))) * g⁻¹ from by group] at h
      exact h
    have hmem : (⟨(((a.out : ↥K) : G))⁻¹ * (((b.out : ↥K) : G)),
        K.mul_mem (K.inv_mem a.out.2) b.out.2⟩ : ↥K) ∈ stabiliser K g := by
      rw [mem_stabiliser]
      exact ⟨K.mul_mem (K.inv_mem a.out.2) b.out.2, hconj⟩
    rw [show a = QuotientGroup.mk (a.out : ↥K) from (QuotientGroup.out_eq' a).symm,
      show b = QuotientGroup.mk (b.out : ↥K) from (QuotientGroup.out_eq' b).symm, QuotientGroup.eq]
    exact hmem
  cover z hz := by
    obtain ⟨u, hu, v, hv, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hz
    set c : ↥K ⧸ stabiliser K g := QuotientGroup.mk (⟨v⁻¹, K.inv_mem hv⟩ : ↥K) with hc
    refine ⟨c, ?_⟩
    have hcls : (⟨v, hv⟩ : ↥K) * c.out ∈ stabiliser K g := by
      have h : (QuotientGroup.mk (⟨v⁻¹, K.inv_mem hv⟩ : ↥K) : ↥K ⧸ stabiliser K g)
          = (QuotientGroup.mk (c.out : ↥K) : ↥K ⧸ stabiliser K g) := by
        rw [hc]
        exact (QuotientGroup.out_eq' c).symm
      have h2 : ((⟨v⁻¹, K.inv_mem hv⟩ : ↥K)⁻¹ : ↥K) * c.out ∈ stabiliser K g := QuotientGroup.eq.mp h
      have h3 : ((⟨v⁻¹, K.inv_mem hv⟩ : ↥K)⁻¹ : ↥K) = ⟨v, hv⟩ := Subtype.ext (by simp)
      rwa [h3] at h2
    obtain ⟨-, hconj⟩ := mem_stabiliser.mp hcls
    have hfac : (u * g * v) * (g * (((c.out : ↥K) : G))⁻¹)⁻¹
        = u * (g * (v * (((c.out : ↥K) : G))) * g⁻¹) := by
      group
    rw [hfac]
    exact K.mul_mem hu hconj

end Transversal


/-- Two representatives of the same left coset give the same slash on a level-invariant function:
this is what lets a family compare its own coset sum with the quotient sum term by term. -/
theorem slash_eq_of_mem_mul_inv {k : ℤ} {K : Subgroup (GL (Fin 2) ℝ)} {F : ℍ → ℂ}
    (hF : ∀ γ ∈ K, F ∣[k] γ = F) {a b : GL (Fin 2) ℝ} (hab : a * b⁻¹ ∈ K) :
    F ∣[k] a = F ∣[k] b := by
  have h : a = (a * b⁻¹) * b := by group
  rw [h, SlashAction.slash_mul, hF _ hab]

/-- The image in `GL(2,ℝ)` of a subgroup of `SL(2,ℤ)` has positive determinant, which is the
hypothesis the operator identity needs. -/
theorem det_pos_of_mem_mapSL {H : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)}
    {γ : GL (Fin 2) ℝ}
    (hγ : γ ∈ H.map (Matrix.SpecialLinearGroup.mapGL ℝ)) : 0 < (γ.det : ℝ) := by
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hγ
  rw [Matrix.SpecialLinearGroup.det_mapGL]
  norm_num

/-! ## The carrier: the slash action as a representation of `GL(2,ℝ)⁺` -/

section Carrier

/-- The slash action of `GL(2,ℝ)⁺`, inherited from `GL (Fin 2) ℝ`. -/
instance : SlashAction ℤ (Matrix.GLPos (Fin 2) ℝ) (ℍ → ℂ) :=
  monoidHomSlashAction (Subgroup.subtype _)

@[simp] theorem slash_coe {k : ℤ} (γ : Matrix.GLPos (Fin 2) ℝ) (F : ℍ → ℂ) :
    F ∣[k] γ = F ∣[k] ((γ : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ) := rfl

/-- The weight `k` slash action of a positive-determinant matrix, as a `ℂ`-linear map: it is
`ℂ`-linear because `σ γ` is the identity for `0 < det γ`. -/
def slashLin (k : ℤ) (γ : Matrix.GLPos (Fin 2) ℝ) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun F := SlashAction.map k γ F
  map_add' F G := SlashAction.add_slash k γ F G
  map_smul' c F := by
    have hσ : σ ((γ : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ) = ContinuousAlgEquiv.refl ℝ ℂ := by
      rw [σ]
      exact ite_eq_left ((Matrix.mem_glpos _).mp γ.2)
    rw [slash_coe, ModularForm.smul_slash, hσ, ContinuousAlgEquiv.refl_apply, RingHom.id_apply]
    rfl

/-- The weight `k` slash action of `GL(2,ℝ)⁺`, as a representation of `GL(2,ℝ)⁺` by the **inverse**
action `γ ↦ slash(γ⁻¹)`. The slash action is an anti-action, and `slash(γ⁻¹)` is the equivalent
genuine left action: the calculus of `RepTheory/DoubleCosetHecke.lean` applies to it with no
opposite group anywhere, and its coset sums are the classical ones. -/
def slashRep (k : ℤ) : Representation ℂ (Matrix.GLPos (Fin 2) ℝ) (ℍ → ℂ) where
  toFun γ := slashLin k γ⁻¹
  map_one' := by
    refine LinearMap.ext fun F => ?_
    show SlashAction.map k (↑((1 : Matrix.GLPos (Fin 2) ℝ)⁻¹) : GL (Fin 2) ℝ) F = F
    simp
  map_mul' a b := by
    refine LinearMap.ext fun F => ?_
    show SlashAction.map k (↑((a * b)⁻¹) : GL (Fin 2) ℝ) F
      = SlashAction.map k (↑a⁻¹ : GL (Fin 2) ℝ) (SlashAction.map k (↑b⁻¹ : GL (Fin 2) ℝ) F)
    simp only [Subgroup.coe_inv, Subgroup.coe_mul]
    rw [mul_inv_rev]
    exact SlashAction.slash_mul k _ _ F

@[simp] theorem slashRep_apply {k : ℤ} (γ : Matrix.GLPos (Fin 2) ℝ) (F : ℍ → ℂ) :
    slashRep k γ F = F ∣[k] γ⁻¹ := rfl

/-- The level space of a subgroup of `GL(2,ℝ)⁺` is the space of functions fixed by its slash
action: the dictionary between the abstract calculus and modular forms. -/
theorem mem_levelSpace_slashRep {k : ℤ} (K : Subgroup (Matrix.GLPos (Fin 2) ℝ)) (F : ℍ → ℂ) :
    F ∈ DoubleCosetHecke.levelSpace (slashRep k) K ↔ ∀ γ ∈ K, F ∣[k] γ = F := by
  constructor
  · intro h γ hγ
    have hk : F ∣[k] γ⁻¹ = F := by
      simpa using (DoubleCosetHecke.mem_levelSpace.mp h ⟨γ, hγ⟩)
    have h2 : (F ∣[k] γ⁻¹) ∣[k] γ = F := by
      rw [← SlashAction.slash_mul, inv_mul_cancel, SlashAction.slash_one]
    calc F ∣[k] γ = (F ∣[k] γ⁻¹) ∣[k] γ := by rw [hk]
      _ = F := h2
  · intro h
    refine DoubleCosetHecke.mem_levelSpace.mpr fun kk => ?_
    have hk : F ∣[k] ((kk : Matrix.GLPos (Fin 2) ℝ)⁻¹) = F := h _ (K.inv_mem kk.2)
    simpa [slashRep_apply] using hk

end Carrier

/-! ## The operator identity: the coset sum is the abstract double-coset operator -/

section Operator

variable {K : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}

/-- The inverse of `g` in `GL(2,ℝ)⁺`, for `g` of positive determinant. It is the label of the
double coset whose coset sum is the operator of `K g K` (see `doubleCosetOperator`). -/
def invPos (g : GL (Fin 2) ℝ) (hg : 0 < (g.det : ℝ)) : Matrix.GLPos (Fin 2) ℝ :=
  ⟨g⁻¹, (Matrix.mem_glpos _).mpr (by
    have h : ((g⁻¹).det : ℝ) = ((g.det : ℝ))⁻¹ := by simp
    rw [h]
    exact inv_pos.mpr hg)⟩

@[simp] theorem coe_invPos (g : GL (Fin 2) ℝ) (hg : 0 < (g.det : ℝ)) :
    ((invPos g hg : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ) = g⁻¹ := rfl

/-- The level subgroup of `GL(2,ℝ)⁺` cut out by a subgroup of `GL(2,ℝ)`. -/
def levelPos (K : Subgroup (GL (Fin 2) ℝ)) : Subgroup (Matrix.GLPos (Fin 2) ℝ) :=
  K.comap (Subgroup.subtype _)

theorem mem_levelPos {x : Matrix.GLPos (Fin 2) ℝ} :
    x ∈ levelPos K ↔ (x : GL (Fin 2) ℝ) ∈ K :=
  Subgroup.mem_comap

/-- **The Hecke operator of the double coset `K g K`.** It is the abstract double-coset operator of
`RepTheory/DoubleCosetHecke.lean`, on the level space of `K`; a family never writes it, it identifies
its coset sum with it (`Transversal.sum_eq_doubleCosetOperator`). The label is `g⁻¹` because
`slashRep` is the inverse action: the two inversions cancel, and the operator of the coset sum
`∑ i, F ∣[k] r i` over the left cosets of `K g K` is the operator of `K g K`. -/
def doubleCosetOperator (k : ℤ) (K : Subgroup (GL (Fin 2) ℝ)) (g : GL (Fin 2) ℝ)
    (hg : 0 < (g.det : ℝ)) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) :=
  DoubleCosetHecke.heckeCoset (slashRep k) (levelPos K) (invPos g hg)

/-- The inverse of a double coset is the double coset of the inverse. -/
theorem doubleCoset_inv {x : GL (Fin 2) ℝ} (hx : x ∈ HeckePair.doubleCoset K g) :
    x⁻¹ ∈ HeckePair.doubleCoset K g⁻¹ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hx
  refine HeckePair.mem_doubleCoset_iff.mpr ⟨b⁻¹, K.inv_mem hb, a⁻¹, K.inv_mem ha, ?_⟩
  group

/-- The indicator of a double coset is invariant under right multiplication by the subgroup. -/
theorem indicator_doubleCoset_mul {G' : Type*} [Group G'] (U : Subgroup G') (g₀ : G')
    {x : G'} {κ : U} :
    (HeckePair.doubleCoset U g₀).indicator (1 : G' → ℂ) (x * κ)
      = (HeckePair.doubleCoset U g₀).indicator (1 : G' → ℂ) x := by
  by_cases hx : x ∈ HeckePair.doubleCoset U g₀
  · rw [Set.indicator_of_mem (HeckePair.doubleCoset_mul_mem hx κ.2), Set.indicator_of_mem hx]
    rfl
  · rw [Set.indicator_of_notMem (fun h => hx ?_), Set.indicator_of_notMem hx]
    simpa using HeckePair.doubleCoset_mul_mem h (U.inv_mem κ.2)

/-- Membership in a double coset of `GL(2,ℝ)⁺` is membership in the double coset of its image in
`GL(2,ℝ)`; the converse direction lifts the two level elements, which is where the positivity of
their determinants is used. -/
theorem mem_doubleCoset_levelPos_iff (hK : ∀ γ ∈ K, 0 < ((γ : GL (Fin 2) ℝ).det : ℝ))
    (g₀ : Matrix.GLPos (Fin 2) ℝ) {y : Matrix.GLPos (Fin 2) ℝ} :
    y ∈ HeckePair.doubleCoset (levelPos K) g₀
      ↔ (y : GL (Fin 2) ℝ) ∈ HeckePair.doubleCoset K (g₀ : GL (Fin 2) ℝ) := by
  constructor
  · intro hy
    obtain ⟨a, ha, b, hb, rfl⟩ := HeckePair.mem_doubleCoset_iff.mp hy
    exact HeckePair.mem_doubleCoset_iff.mpr
      ⟨(a : GL (Fin 2) ℝ), mem_levelPos.mp ha, (b : GL (Fin 2) ℝ), mem_levelPos.mp hb, by simp⟩
  · intro hy
    obtain ⟨a, ha, b, hb, h⟩ := HeckePair.mem_doubleCoset_iff.mp hy
    refine HeckePair.mem_doubleCoset_iff.mpr
      ⟨⟨a, (Matrix.mem_glpos _).mpr (hK a ha)⟩, mem_levelPos.mpr ha,
        ⟨b, (Matrix.mem_glpos _).mpr (hK b hb)⟩, mem_levelPos.mpr hb, ?_⟩
    apply Subtype.ext
    simpa using h

end Operator

namespace Transversal

variable {ι : Type*} [Fintype ι]
variable {K : Subgroup (GL (Fin 2) ℝ)} {g : GL (Fin 2) ℝ}

/-- **The coset sum is the operator of the double coset.** For a transversal of `K g K` whose
elements have positive determinant — derived from `mem`, the positivity of `K` and that of `g` —
the sum of the slashes over the representatives is the abstract double-coset operator of `K g K`.
This is the whole content of "the concrete sum computes the Hecke operator": the representatives,
the finiteness and the coset bookkeeping are `Transversal`'s three fields, and nothing here mentions
a coset quotient. -/
theorem sum_eq_doubleCosetOperator {k : ℤ} (T : Transversal K g ι) {F : ℍ → ℂ}
    (hF : ∀ γ ∈ K, F ∣[k] γ = F) (hK : ∀ γ ∈ K, 0 < ((γ : GL (Fin 2) ℝ).det : ℝ))
    (hg : 0 < (g.det : ℝ)) :
    ∑ i, F ∣[k] T.r i = doubleCosetOperator k K g hg F := by
  classical
  have hpos (i : ι) : 0 < ((T.r i).det : ℝ) := by
    obtain ⟨a, ha, b, hb, hAB⟩ := HeckePair.mem_doubleCoset_iff.mp (T.mem i)
    rw [← hAB]
    have h : ((a * g * b).det : ℝ) = (a.det : ℝ) * (g.det : ℝ) * (b.det : ℝ) := by simp [map_mul]
    rw [h]
    exact mul_pos (mul_pos (hK a ha) hg) (hK b hb)
  set x : ι → Matrix.GLPos (Fin 2) ℝ := fun i => invPos (T.r i) (hpos i)
  have hx (i : ι) : ((x i : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ) = (T.r i)⁻¹ := by simp [x]
  set f : Matrix.GLPos (Fin 2) ℝ → ℂ :=
    (HeckePair.doubleCoset (levelPos K) (invPos g hg)).indicator 1
  have hm : ∀ i : ι, x i ∈ HeckePair.doubleCoset (levelPos K) (invPos g hg) := by
    intro i
    refine (mem_doubleCoset_levelPos_iff (K := K) hK (invPos g hg)).mpr ?_
    rw [hx i, coe_invPos]
    exact doubleCoset_inv (T.mem i)
  have hf : ∀ (a : Matrix.GLPos (Fin 2) ℝ) (κ : levelPos K), f (a * κ) = f a := fun a κ =>
    indicator_doubleCoset_mul (levelPos K) (invPos g hg) (x := a) (κ := κ)
  have hv : F ∈ DoubleCosetHecke.levelSpace (slashRep k) (levelPos K) := by
    refine (mem_levelSpace_slashRep (levelPos K) F).mpr fun γ hγ => ?_
    exact hF (γ : GL (Fin 2) ℝ) (mem_levelPos.mp hγ)
  have hr : Set.InjOn (fun i => (x i : Matrix.GLPos (Fin 2) ℝ ⧸ levelPos K))
      (Finset.univ : Finset ι) := by
    intro i _ j _ hij
    rw [QuotientGroup.eq] at hij
    have h : T.r i * (T.r j)⁻¹ ∈ K := by
      have hcoe : (((x i)⁻¹ * x j : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ)
          = T.r i * (T.r j)⁻¹ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hx i, hx j, inv_inv]
      rw [← hcoe]
      exact mem_levelPos.mp hij
    exact T.distinct i j h
  have hs : ∀ a : Matrix.GLPos (Fin 2) ℝ, f a ≠ 0 →
      ∃ i ∈ (Finset.univ : Finset ι), (x i : Matrix.GLPos (Fin 2) ℝ ⧸ levelPos K) = a := by
    intro a ha
    have haD : a ∈ HeckePair.doubleCoset (levelPos K) (invPos g hg) := by
      by_contra h
      exact ha (Set.indicator_of_notMem h 1)
    have h1 : (a : GL (Fin 2) ℝ) ∈ HeckePair.doubleCoset K (invPos g hg : GL (Fin 2) ℝ) :=
      (mem_doubleCoset_levelPos_iff hK (invPos g hg)).mp haD
    rw [coe_invPos] at h1
    obtain ⟨i, hi⟩ := T.cover _ (doubleCoset_inv h1)
    refine ⟨i, Finset.mem_univ i, ?_⟩
    rw [QuotientGroup.eq]
    refine mem_levelPos.mpr ?_
    have hcoe : (((x i)⁻¹ * a : Matrix.GLPos (Fin 2) ℝ) : GL (Fin 2) ℝ)
        = T.r i * (a : GL (Fin 2) ℝ) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hx i, inv_inv]
    rw [hcoe]
    simpa using K.inv_mem hi
  obtain ⟨-, hsum⟩ := DoubleCosetHecke.heckeFun_eq_sum (π := slashRep k) (K := levelPos K)
    (f := f) (v := F) hf hv hr hs
  rw [show doubleCosetOperator k K g hg F
      = DoubleCosetHecke.heckeFun (slashRep k) (levelPos K) f F from rfl, hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show f (x i) = 1 from Set.indicator_of_mem (hm i) 1, one_smul, slashRep_apply, slash_coe,
    Subgroup.coe_inv, hx i, inv_inv]

end Transversal

end HeckeCoset
