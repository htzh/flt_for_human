/-
  The primitive-coset / `jLattice` column: the leaf node
  `PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`.

  Given `(L'.lattice : Set ℂ) ⊆ L.lattice`, `sublatticeIndex L L' = N` and
  `IsAddCyclic (sublatticeQuotient L L')`, the headline produces `a b d : ℕ` and
  `τ σ : ℍ` with `(a, b, d) ∈ ModularCurve.primCosetReps N`,
  `(σ : ℂ) = ((a : ℂ) * τ + b) / d`, `L.jLattice = (ofTau τ).jLattice` and
  `L'.jLattice = (ofTau σ).jLattice`.  It is the bridge from an abstract lattice
  inclusion to the classical `τ`-model: normalise by a complex scaling to an
  `ofTau`, read the sublattice off a Hermite-normal-form triple recovered from a
  `ℤ²`-quotient, use the cyclicity to prove that triple primitive, and read the
  `j`-invariants off `ofTau`.

  Pin source, `anthropics/fermats-last-theorem@aa2d8b3`:

    `P2M/Sol/S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`
    (848 lines, 71 declarations); statement authority
    `Theorems/Thm_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean`.

  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic.lean>

  **What is imported, not re-proved.**  The pin's inlined `PeriodPair` scale /
  `G_scale` / `discriminant_scale` / `*_eq_of_lattice_eq` prelude is the port's
  `Elliptic/PeriodPair/{Basic,Lattice}.lean`; the `toPointHom`/uniformization
  dictionary is `Uniformization.lean`; and the two shared lemmas
  `ModularCurve.kw_scale_lattice_toAddSubgroup` and
  `ModularCurve.kwSublatticeIndex_scale` are S-2's `LatticeIndex.lean` (imported,
  never redeclared).  The generic `ℤ²` block is
  `FLTForHuman/Algebra/IntPairSubgroup.lean` (this set's other module); the
  primitive-coset API is `ModularCurve/Defs/PrimCosetReps.lean`.

  **Pin-`private` helpers re-derived `private` here.**  A `private` declaration is
  not reachable across a module boundary, so the following, which the pin's one
  file carries inline, are re-derived with content names: `mem_scale_lattice_iff`
  (private in S-2's `LatticeIndex.lean`), `im_div_ne_zero` / `span_neg_fst` /
  `ofTau_latticeEquivProd_symm_apply` (private in `Discriminant.lean`), and
  `g₂_cubed_scale` / `jLattice_scale`.  `jLattice_eq_of_lattice_eq` is pin-*public*
  and was absent from the port; it is landed here at its pin name.

  **Not transcribed.**  The pin's `p2m_*` scaffolding, its
  `attribute [-instance]`/`attribute [-simp]` blocks, its heartbeat bumps
  (`maxHeartbeats 6400000`, `synthInstance.maxHeartbeats 1600000` — the port's cap
  is 4,000,000), and the `kw_surgehgf4_qtzz_axiomAnchor : True` stub.

  **Namespaces.**  The generic `ℤ²` block goes to `IntPairSubgroup`; the transport,
  criterion and headline keep the pin's `ModularCurve` / `PeriodPair` namespaces.
-/
import FLTForHuman.Elliptic.PeriodPair.Basic
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.Elliptic.PeriodPair.JLine
import FLTForHuman.Elliptic.PeriodPair.LatticeIndex
import FLTForHuman.Algebra.IntPairSubgroup
import FLTForHuman.ModularCurve.Defs.PrimCosetReps
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.LinearAlgebra.FreeModule.Int
import Mathlib.GroupTheory.Archimedean
import Mathlib.Tactic

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

open scoped UpperHalfPlane PeriodPair
open UpperHalfPlane
open PeriodPair
open IntPairSubgroup
open ModularCurve

namespace PeriodPair

/-! ## The prelude lemmas this set needs that the port did not carry -/

section Scale

variable (L : PeriodPair) (α : ℂˣ)

/-- Membership in the rescaled lattice, read off the ported `PeriodPair.scale_lattice`.
Pin `mem_scale_lattice_iff` (private in both target files). -/
private theorem mem_scale_lattice_iff {z : ℂ} :
    z ∈ (L.scale α).lattice ↔ ∃ l ∈ L.lattice, z = (α : ℂ) * l := by
  rw [scale_lattice, Submodule.mem_map]
  constructor
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.symm⟩
  · rintro ⟨l, hl, h⟩; exact ⟨l, hl, h.symm⟩

end Scale

section Homogeneity

variable (L : PeriodPair) (α : ℂˣ)

/-- Pin `g₂_cubed_scale` (private): the cube of `g₂` is homogeneous of degree `-12`. -/
private theorem g₂_cubed_scale : (L.scale α).g₂ ^ 3 = ((α : ℂ) ^ 12)⁻¹ * L.g₂ ^ 3 := by
  rw [g₂_scale, mul_pow, inv_pow, ← pow_mul]

/-- Pin `PeriodPair.jLattice_scale` (private): `jLattice` is scale-invariant. -/
private theorem jLattice_scale : (L.scale α).jLattice = L.jLattice := by
  have hα : ((α : ℂ) ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ α.ne_zero)
  unfold jLattice
  rw [discriminant_scale, g₂_cubed_scale, mul_left_comm (1728 : ℂ), mul_div_mul_left _ _ hα]

end Homogeneity

section LatticeDependence

variable {L L' : PeriodPair}

/-- Pin `PeriodPair.jLattice_eq_of_lattice_eq`: `jLattice` depends only on the lattice. -/
theorem jLattice_eq_of_lattice_eq (h : L.lattice = L'.lattice) :
    L.jLattice = L'.jLattice := by
  unfold jLattice; rw [g₂_eq_of_lattice_eq h, g₃_eq_of_lattice_eq h]

end LatticeDependence

section RecoverTau

variable (L : PeriodPair)

/-- Pin `im_div_ne_zero` (private in `Discriminant.lean`): `ω₁ / ω₂` is not real. -/
private theorem im_div_ne_zero (L : PeriodPair) : (L.ω₁ / L.ω₂).im ≠ 0 := by
  have hω₂ : L.ω₂ ≠ 0 := by
    have := L.indep.ne_zero 1; simpa using this
  intro him

  have hdiv : (L.ω₁ / L.ω₂ : ℂ) = ((L.ω₁ / L.ω₂).re : ℂ) :=
    Complex.ext (by simp) (by simp [him])
  have hreal : L.ω₁ = ((L.ω₁ / L.ω₂).re : ℂ) * L.ω₂ := by
    rw [← hdiv, div_mul_cancel₀ _ hω₂]
  have key : (1 : ℝ) • L.ω₁ + (-(L.ω₁ / L.ω₂).re) • L.ω₂ = 0 := by
    rw [one_smul, _root_.neg_smul, Complex.real_smul, ← hreal, add_neg_cancel]
  exact one_ne_zero (LinearIndependent.pair_iff.mp L.indep 1 (-(L.ω₁ / L.ω₂).re) key).1

/-- Pin `span_neg_fst` (private in `Discriminant.lean`): negating the first generator
does not change the `ℤ`-span. -/
private theorem span_neg_fst (a b : ℂ) :
    Submodule.span ℤ ({-a, b} : Set ℂ) = Submodule.span ℤ ({a, b} : Set ℂ) := by
  have hna : (-a : ℂ) ∈ Submodule.span ℤ ({a, b} : Set ℂ) :=
    neg_mem (Submodule.subset_span (Set.mem_insert _ _))
  have ha : (a : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) := by
    have hneg : (-(-a) : ℂ) ∈ Submodule.span ℤ ({-a, b} : Set ℂ) :=
      neg_mem (Submodule.subset_span (Set.mem_insert _ _))
    simpa using hneg
  apply le_antisymm <;> rw [Submodule.span_le, Set.insert_subset_iff] <;>
    exact ⟨by assumption,
      Set.singleton_subset_iff.mpr (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))⟩

end RecoverTau

end PeriodPair

namespace ModularCurve

/-! ## Transport: normalising to `ofTau`, and moving the hypotheses -/

/-- Pin `ModularCurve.kw_scale_lattice_subset`: rescaling preserves an inclusion of
lattices. -/
theorem kw_scale_lattice_subset (L L' : PeriodPair) (α : ℂˣ)
    (h : (L'.lattice : Set ℂ) ⊆ L.lattice) :
    ((L'.scale α).lattice : Set ℂ) ⊆ (L.scale α).lattice := by
  intro z hz
  rw [SetLike.mem_coe] at hz ⊢
  rw [PeriodPair.mem_scale_lattice_iff L' α] at hz
  rw [PeriodPair.mem_scale_lattice_iff L α]
  obtain ⟨l, hl, rfl⟩ := hz
  exact ⟨l, h hl, rfl⟩

/-- Pin `ModularCurve.kw_exists_scale_ofTau_lattice_eq`: every period pair is a
rescaled `ofTau`. -/
theorem kw_exists_scale_ofTau_lattice_eq (L : PeriodPair) :
    ∃ (α : ℂˣ) (τ : ℍ), (L.scale α).lattice = (ofTau τ).lattice := by
  have hω₂ : L.ω₂ ≠ 0 := by have := L.indep.ne_zero 1; simpa using this
  set α : ℂˣ := (Units.mk0 L.ω₂ hω₂)⁻¹
  have hα : (α : ℂ) = (L.ω₂)⁻¹ := by simp only [α, Units.val_inv_eq_inv_val, Units.val_mk0]
  have hlat : (L.scale α).lattice = Submodule.span ℤ {L.ω₁ / L.ω₂, 1} := by
    simp only [lattice, scale_ω₁, scale_ω₂, hα, div_eq_inv_mul, inv_mul_cancel₀ hω₂]
  rcases lt_or_gt_of_ne (PeriodPair.im_div_ne_zero L) with hneg | hpos
  · exact ⟨α, ⟨-(L.ω₁ / L.ω₂), by simp only [Complex.neg_im]; linarith⟩,
      hlat.trans (PeriodPair.span_neg_fst _ _).symm⟩
  · exact ⟨α, ⟨L.ω₁ / L.ω₂, hpos⟩, hlat⟩

/-! ## `kw_phiTau` and the `ℤ²` model `kw_HZZ` -/

section PhiTau

/-- Pin `kw_ofTau_latticeEquivProd_symm_apply` (private in `Discriminant.lean`). -/
private theorem ofTau_latticeEquivProd_symm_apply (τ : ℍ) (p : ℤ × ℤ) :
    ((ofTau τ).latticeEquivProd.symm p : ℂ) = p.1 * (τ : ℂ) + p.2 := by
  rw [latticeEquiv_symm_apply]; simp

/-- Pin `ModularCurve.kw_phiTau`: the coordinates of `ofTau τ` as an additive map. -/
def kw_phiTau (τ : ℍ) : ℤ × ℤ →+ ℂ :=
  ((ofTau τ).lattice.subtype.toAddMonoidHom).comp
    (ofTau τ).latticeEquivProd.symm.toLinearMap.toAddMonoidHom

/-- Pin `ModularCurve.kw_phiTau_apply`. -/
theorem kw_phiTau_apply (τ : ℍ) (p : ℤ × ℤ) :
    kw_phiTau τ p = (p.1 : ℂ) * (τ : ℂ) + (p.2 : ℂ) := by
  change ((ofTau τ).latticeEquivProd.symm p : ℂ) = _
  exact_mod_cast ofTau_latticeEquivProd_symm_apply τ p

/-- Pin `ModularCurve.kw_phiTau_range`. -/
theorem kw_phiTau_range (τ : ℍ) :
    (kw_phiTau τ).range = (ofTau τ).lattice.toAddSubgroup := by
  ext z
  simp only [AddMonoidHom.mem_range, Submodule.mem_toAddSubgroup]
  refine ⟨?_, fun hz => ⟨(ofTau τ).latticeEquivProd ⟨z, hz⟩, ?_⟩⟩
  · rintro ⟨p, rfl⟩; exact ((ofTau τ).latticeEquivProd.symm p).2
  · change ((ofTau τ).latticeEquivProd.symm ((ofTau τ).latticeEquivProd ⟨z, hz⟩) : ℂ) = z
    rw [LinearEquiv.symm_apply_apply]

/-- Pin `ModularCurve.kw_HZZ`: the sublattice `L'` read in the `ℤ²` coordinates of
`ofTau τ`. -/
def kw_HZZ (τ : ℍ) (L' : PeriodPair) : AddSubgroup (ℤ × ℤ) :=
  L'.lattice.toAddSubgroup.comap (kw_phiTau τ)

/-- Pin `ModularCurve.kw_HZZ_index`. -/
theorem kw_HZZ_index (τ : ℍ) (L' : PeriodPair) :
    (kw_HZZ τ L').index = PeriodPair.sublatticeIndex (ofTau τ) L' := by
  rw [kw_HZZ, AddSubgroup.index_comap, kw_phiTau_range]
  rfl

/-- Pin `ModularCurve.kw_HZZ_map_eq`. -/
theorem kw_HZZ_map_eq (τ : ℍ) (L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ (ofTau τ).lattice) :
    (kw_HZZ τ L').map (kw_phiTau τ) = L'.lattice.toAddSubgroup := by
  rw [kw_HZZ, AddSubgroup.map_comap_eq_self]
  rw [kw_phiTau_range]
  exact fun z hz => hsub hz

/-- Pin `ModularCurve.kw_sublattice_eq_span`: `L'` is spanned by the HNF triple of
`kw_HZZ τ L'`, transported back through `kw_phiTau`. -/
theorem kw_sublattice_eq_span (τ : ℍ) (L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ (ofTau τ).lattice) :
    L'.lattice = Submodule.span ℤ
      {(aOf (kw_HZZ τ L') : ℂ) * (τ : ℂ) + (bOf (kw_HZZ τ L') : ℂ),
       (dOf (kw_HZZ τ L') : ℂ)} := by
  apply Submodule.toAddSubgroup_injective
  rw [Submodule.span_int_eq_addSubgroupClosure, ← kw_HZZ_map_eq τ L' hsub]
  conv_lhs => rw [← latticeOf_canonical_eq (kw_HZZ τ L')]
  rw [latticeOf, AddMonoidHom.map_closure, Set.image_pair,
    kw_phiTau_apply, kw_phiTau_apply]
  push_cast
  ring_nf

/-- Pin `ModularCurve.kw_hnfPoint`: the point `(a τ + b) / d` of the upper half
plane. -/
def kw_hnfPoint (τ : ℍ) (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a) (hd : 0 < d) : ℍ :=
  ⟨((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ), by
    have him : ((a : ℂ) * (τ : ℂ) + (b : ℂ)).im = (a : ℝ) * τ.im := by simp
    have haτ : (0 : ℝ) < (a : ℝ) * τ.im := mul_pos (by exact_mod_cast ha) τ.im_pos
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    simp only [Complex.div_im, him, Complex.natCast_im, mul_zero, zero_div, sub_zero,
      Complex.natCast_re, Complex.normSq_natCast]
    positivity⟩

/-- Pin `ModularCurve.kw_hnfPoint_coe`. -/
@[scoped simp] theorem kw_hnfPoint_coe (τ : ℍ) (a : ℕ) (b : ℤ) (d : ℕ) (ha : 0 < a)
    (hd : 0 < d) :
    (kw_hnfPoint τ a b d ha hd : ℂ) = ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / (d : ℂ) := rfl

/-- Pin `ModularCurve.kw_hnfPoint_scale_lattice`. -/
theorem kw_hnfPoint_scale_lattice (τ : ℍ) (a : ℕ) (b : ℤ) (d : ℕ)
    (ha : 0 < a) (hd : 0 < d) :
    ((ofTau (kw_hnfPoint τ a b d ha hd)).scale
      (Units.mk0 (d : ℂ) (Nat.cast_ne_zero.mpr hd.ne'))).lattice
      = Submodule.span ℤ {(a : ℂ) * (τ : ℂ) + (b : ℂ), (d : ℂ)} := by
  have hd' : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  simp only [lattice, scale_ω₁, scale_ω₂, ofTau_ω₁, ofTau_ω₂, Units.val_mk0,
    kw_hnfPoint_coe, mul_div_cancel₀ _ hd', mul_one]

end PhiTau

/-! ## The product-cyclicity / HNF-coprimality criterion -/

section Criterion

set_option maxHeartbeats 4000000

/-- Pin `ModularCurve.kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod`: for `p > 1`,
`ZMod p × ZMod p` is not cyclic. -/
theorem kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod {p : ℕ} (hp : 1 < p) :
    ¬ IsAddCyclic (ZMod p × ZMod p) := by
  rintro ⟨⟨g, hg⟩⟩
  haveI : NeZero p := ⟨by omega⟩
  have hord : addOrderOf g ∣ p := by
    rw [addOrderOf_dvd_iff_nsmul_eq_zero]
    show ((p • g.1, p • g.2) : ZMod p × ZMod p) = 0
    simp [nsmul_eq_mul]
  have hcard : Nat.card (ZMod p × ZMod p) = p * p := by
    simp only [Nat.card_prod, Nat.card_zmod]
  have htop : AddSubgroup.zmultiples g = ⊤ := by
    rw [AddSubgroup.eq_top_iff']
    intro x; obtain ⟨k, hk⟩ := hg x
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, hk⟩
  have hspan : Nat.card (ZMod p × ZMod p) = addOrderOf g := by
    rw [← Nat.card_zmultiples g, htop, AddSubgroup.card_top]
  have : p * p ≤ p := hcard ▸ hspan ▸ Nat.le_of_dvd (by omega) hord
  nlinarith

/-- Pin `ModularCurve.kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic`: a cyclic quotient
of `ℤ × ℤ` forces the HNF triple to be primitive. -/
theorem kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic
    {H : AddSubgroup (ℤ × ℤ)} (hN : H.index ≠ 0)
    (hcyc : IsAddCyclic ((ℤ × ℤ) ⧸ H)) :
    Nat.gcd (aOf H) (Nat.gcd (bOf H).toNat (dOf H)) = 1 := by
  by_contra hgcd
  have hgcd_ne : Nat.gcd (aOf H) (Nat.gcd (bOf H).toNat (dOf H)) ≠ 1 := hgcd
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hgcd_ne
  have hd0 : dOf H ≠ 0 := fun h => hN (by rw [index_eq_dOf_mul_aOf, h, zero_mul])
  have hpa : (p : ℤ) ∣ (aOf H : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpdvd.trans (Nat.gcd_dvd_left _ _))
  have hpb : (p : ℤ) ∣ bOf H := by
    have hb : ((bOf H).toNat : ℤ) = bOf H := Int.toNat_of_nonneg (bOf_nonneg H hd0)
    have : p ∣ (bOf H).toNat :=
      hpdvd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
    exact hb ▸ Int.natCast_dvd_natCast.mpr this
  have hpd : (p : ℤ) ∣ (dOf H : ℤ) :=
    Int.natCast_dvd_natCast.mpr (hpdvd.trans ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)))
  haveI : NeZero p := ⟨hp.ne_zero⟩
  let π : ℤ × ℤ →+ ZMod p × ZMod p :=
    (Int.castAddHom (ZMod p)).prodMap (Int.castAddHom (ZMod p))
  have hπapply : ∀ x y : ℤ, π (x, y) = ((x : ZMod p), (y : ZMod p)) := fun x y => rfl
  have hπsurj : Function.Surjective π := by
    rintro ⟨x, y⟩
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective x
    obtain ⟨b, hb⟩ := ZMod.intCast_surjective y
    exact ⟨(a, b), by rw [hπapply, ha, hb]⟩
  have hHker : H ≤ π.ker := by
    rw [← latticeOf_canonical_eq H, latticeOf, AddSubgroup.closure_le]
    rintro z (rfl | rfl)
    · show π ((aOf H : ℤ), bOf H) = 0
      rw [hπapply]
      exact Prod.ext ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpa)
        ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpb)
    · show π (0, (dOf H : ℤ)) = 0
      rw [hπapply]
      exact Prod.ext (by simp) ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpd)
  have hmapsurj : Function.Surjective
      (QuotientAddGroup.map H π.ker (AddMonoidHom.id _) hHker) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective y
    exact ⟨QuotientAddGroup.mk x, rfl⟩
  have hqsurj : Function.Surjective
      ((QuotientAddGroup.quotientKerEquivOfSurjective π hπsurj).toAddMonoidHom.comp
        (QuotientAddGroup.map H π.ker (AddMonoidHom.id _) hHker)) :=
    (QuotientAddGroup.quotientKerEquivOfSurjective π hπsurj).surjective.comp hmapsurj
  have : IsAddCyclic (ZMod p × ZMod p) := by
    obtain ⟨⟨g, hg⟩⟩ := hcyc
    exact ⟨⟨_, fun y => by
      obtain ⟨x, hx⟩ := hqsurj y; obtain ⟨k, hk⟩ := hg x
      exact ⟨k, by rw [← hx, ← hk, map_zsmul]⟩⟩⟩
  exact kw_surgehgf4_hu5c_not_isAddCyclic_zmod_prod hp.one_lt this

end Criterion

/-! ## `KwSublatticeQuotientZZTransport` and the `qtzz_*` block -/

/-- Pin `ModularCurve.KwSublatticeQuotientZZTransport`: cyclicity of
`sublatticeQuotient L L'` transports to the `ℤ²`-quotient `(ℤ × ℤ) ⧸ kw_HZZ τ (L'.scale α)`
along any scaled `ofTau` model of `L`. -/
def KwSublatticeQuotientZZTransport : Prop :=
  ∀ (L L' : PeriodPair), (L'.lattice : Set ℂ) ⊆ L.lattice →
    ∀ (α : ℂˣ) (τ : ℍ), (L.scale α).lattice = (ofTau τ).lattice →
      IsAddCyclic (PeriodPair.sublatticeQuotient L L') →
        IsAddCyclic ((ℤ × ℤ) ⧸ kw_HZZ τ (L'.scale α))

section Psi

variable (L L' : PeriodPair) (α : ℂˣ) (τ : ℍ)

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_phiTau_mem_scale`. -/
theorem kw_surgehgf4_qtzz_phiTau_mem_scale
    (hlat : (L.scale α).lattice = (ofTau τ).lattice) (p : ℤ × ℤ) :
    kw_phiTau τ p ∈ (L.scale α).lattice := by
  have h : kw_phiTau τ p ∈ (ofTau τ).lattice.toAddSubgroup := by
    rw [← kw_phiTau_range τ]; exact ⟨p, rfl⟩
  exact hlat ▸ h

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_phiTau_invMul_mem`. -/
theorem kw_surgehgf4_qtzz_phiTau_invMul_mem
    (hlat : (L.scale α).lattice = (ofTau τ).lattice) (p : ℤ × ℤ) :
    ((α : ℂ)⁻¹ * kw_phiTau τ p) ∈ L.lattice := by
  obtain ⟨l, hl, hlp⟩ := (PeriodPair.mem_scale_lattice_iff L α).mp
    (kw_surgehgf4_qtzz_phiTau_mem_scale L α τ hlat p)
  rw [hlp, inv_mul_cancel_left₀ α.ne_zero]
  exact hl

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_psi₀`: `ℤ² → L.lattice`, `p ↦ α⁻¹ (phiTau p)`. -/
def kw_surgehgf4_qtzz_psi₀ (hlat : (L.scale α).lattice = (ofTau τ).lattice) :
    (ℤ × ℤ) →+ ↥L.lattice.toAddSubgroup where
  toFun p := ⟨(α : ℂ)⁻¹ * kw_phiTau τ p,
    kw_surgehgf4_qtzz_phiTau_invMul_mem L α τ hlat p⟩
  map_zero' := Subtype.ext (by simp)
  map_add' p q := Subtype.ext (by simp [mul_add])

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_psi₀_apply`. -/
theorem kw_surgehgf4_qtzz_psi₀_apply
    (hlat : (L.scale α).lattice = (ofTau τ).lattice) (p : ℤ × ℤ) :
    ((kw_surgehgf4_qtzz_psi₀ L α τ hlat p : ↥L.lattice.toAddSubgroup) : ℂ)
      = (α : ℂ)⁻¹ * kw_phiTau τ p := rfl

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_psi`: `ℤ² → sublatticeQuotient L L'`. -/
def kw_surgehgf4_qtzz_psi (hlat : (L.scale α).lattice = (ofTau τ).lattice) :
    (ℤ × ℤ) →+ PeriodPair.sublatticeQuotient L L' :=
  (QuotientAddGroup.mk' _).comp (kw_surgehgf4_qtzz_psi₀ L α τ hlat)

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_psi_surjective`. -/
theorem kw_surgehgf4_qtzz_psi_surjective
    (hlat : (L.scale α).lattice = (ofTau τ).lattice) :
    Function.Surjective (kw_surgehgf4_qtzz_psi L L' α τ hlat) := by
  refine (QuotientAddGroup.mk'_surjective _).comp fun l => ?_
  have hαl : ((α : ℂ) * (l : ℂ)) ∈ (ofTau τ).lattice.toAddSubgroup := by
    rw [← hlat]
    exact (PeriodPair.mem_scale_lattice_iff L α).mpr ⟨l, l.2, rfl⟩
  obtain ⟨p, hp⟩ := (kw_phiTau_range τ ▸ hαl : ((α : ℂ) * (l : ℂ)) ∈ (kw_phiTau τ).range)
  refine ⟨p, Subtype.ext ?_⟩
  rw [kw_surgehgf4_qtzz_psi₀_apply, hp, inv_mul_cancel_left₀ α.ne_zero]

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_psi_ker`. -/
theorem kw_surgehgf4_qtzz_psi_ker
    (hlat : (L.scale α).lattice = (ofTau τ).lattice) :
    (kw_surgehgf4_qtzz_psi L L' α τ hlat).ker = kw_HZZ τ (L'.scale α) := by
  ext p
  simp only [kw_surgehgf4_qtzz_psi, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply,
    QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf, kw_HZZ, AddSubgroup.mem_comap,
    Submodule.mem_toAddSubgroup]

  rw [kw_surgehgf4_qtzz_psi₀_apply, PeriodPair.mem_scale_lattice_iff]
  constructor
  · intro hmem
    exact ⟨(α : ℂ)⁻¹ * kw_phiTau τ p, hmem, (mul_inv_cancel_left₀ α.ne_zero _).symm⟩
  · rintro ⟨l', hl', hp⟩
    rw [hp, inv_mul_cancel_left₀ α.ne_zero]
    exact hl'

end Psi

/-- Pin `ModularCurve.kw_surgehgf4_qtzz_proved`: the transport class is proved. -/
theorem kw_surgehgf4_qtzz_proved : KwSublatticeQuotientZZTransport := by
  intro L L' hsub α τ hlat hcyc
  let ψ := kw_surgehgf4_qtzz_psi L L' α τ hlat
  have hψsurj := kw_surgehgf4_qtzz_psi_surjective L L' α τ hlat
  have hψker := kw_surgehgf4_qtzz_psi_ker L L' α τ hlat
  let e : ((ℤ × ℤ) ⧸ kw_HZZ τ (L'.scale α)) ≃+ PeriodPair.sublatticeQuotient L L' :=
    (QuotientAddGroup.quotientAddEquivOfEq hψker.symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective ψ hψsurj)
  exact isAddCyclic_of_surjective e.symm.toAddMonoidHom e.symm.surjective

end ModularCurve

/-! ## The headline -/

/-- Pin `PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic`. -/
theorem PeriodPair.exists_mem_primCosetReps_and_jLattice_eq_of_isAddCyclic
    {N : ℕ} [NeZero N] (L L' : PeriodPair)
    (hsub : (L'.lattice : Set ℂ) ⊆ L.lattice) (hidx : PeriodPair.sublatticeIndex L L' = N)
    (hcyc : IsAddCyclic (PeriodPair.sublatticeQuotient L L')) :
    ∃ (a b d : ℕ) (τ σ : ℍ), (a, b, d) ∈ ModularCurve.primCosetReps N ∧
      (σ : ℂ) = ((a : ℂ) * τ + b) / d ∧
      L.jLattice = (PeriodPair.ofTau τ).jLattice ∧
        L'.jLattice = (PeriodPair.ofTau σ).jLattice := by
  obtain ⟨α, τ, hlat⟩ := kw_exists_scale_ofTau_lattice_eq L
  have hjL : L.jLattice = (ofTau τ).jLattice :=
    (PeriodPair.jLattice_scale L α).symm.trans (jLattice_eq_of_lattice_eq hlat)
  have hjL' : L'.jLattice = (L'.scale α).jLattice := (PeriodPair.jLattice_scale L' α).symm
  have hsub' : ((L'.scale α).lattice : Set ℂ) ⊆ (ofTau τ).lattice :=
    hlat ▸ kw_scale_lattice_subset L L' α hsub
  have hidx' : PeriodPair.sublatticeIndex (ofTau τ) (L'.scale α) = N := by
    have hstep : PeriodPair.sublatticeIndex (ofTau τ) (L'.scale α)
        = PeriodPair.sublatticeIndex (L.scale α) (L'.scale α) := by
      unfold PeriodPair.sublatticeIndex; rw [hlat]
    rw [hstep, kwSublatticeIndex_scale]; exact hidx
  set H := kw_HZZ τ (L'.scale α)
  have hNH : dOf H * aOf H = N := (index_eq_dOf_mul_aOf H).symm.trans
    ((kw_HZZ_index τ (L'.scale α)).trans hidx')
  have ha : 0 < aOf H := Nat.pos_of_ne_zero fun h =>
    NeZero.ne N (by rw [← hNH, h, mul_zero])
  have hd : 0 < dOf H := Nat.pos_of_ne_zero fun h =>
    NeZero.ne N (by rw [← hNH, h, zero_mul])
  have hb0 : 0 ≤ bOf H := bOf_nonneg H hd.ne'
  have hbd : bOf H < ((dOf H : ℕ) : ℤ) := bOf_lt H hd.ne'
  have hb : ((bOf H).toNat : ℂ) = (bOf H : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hb0
  have hHidx : H.index ≠ 0 := by rw [kw_HZZ_index, hidx']; exact NeZero.ne N
  have hcycH : IsAddCyclic ((ℤ × ℤ) ⧸ H) := kw_surgehgf4_qtzz_proved L L' hsub α τ hlat hcyc
  have hgcd := kw_surgehgf4_hu5c_gcd_eq_one_of_isAddCyclic hHidx hcycH
  let σ := kw_hnfPoint τ (aOf H) (bOf H) (dOf H) ha hd
  have hjM' : (L'.scale α).jLattice = (ofTau σ).jLattice := by
    have hlat' : (L'.scale α).lattice
        = ((ofTau σ).scale (Units.mk0 (dOf H : ℂ) (Nat.cast_ne_zero.mpr hd.ne'))).lattice := by
      rw [kw_sublattice_eq_span τ (L'.scale α) hsub', kw_hnfPoint_scale_lattice]
    exact (jLattice_eq_of_lattice_eq hlat').trans
      (PeriodPair.jLattice_scale (ofTau σ) (Units.mk0 (dOf H : ℂ) (Nat.cast_ne_zero.mpr hd.ne')))
  refine ⟨aOf H, (bOf H).toNat, dOf H, τ, σ, ?_, ?_, hjL, hjL'.trans hjM'⟩
  · exact (ModularCurve.mem_primCosetReps (NeZero.ne N)).mpr
      ⟨(mul_comm _ _).trans hNH, by omega, hgcd⟩
  · rw [kw_hnfPoint_coe, hb]

end
