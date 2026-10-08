/-
  The `PeriodPair` lattice/index arithmetic: the two S-2 headlines, the three
  `ModularCurve` classes they prove, and the shared `hID_*` / `kqe_*` engines.

  Ported from the pin's

    `P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean`
    (978 lines)  and
    `P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean`
    (2,021 lines)

  (`anthropics/fermats-last-theorem@aa2d8b3`). The statement authorities are the two
  `Theorems/` wrappers; the pin's `solution` bodies are the proofs.

  **One module for the two nodes, and the pin's duplication written once.** The two
  `S_` files ship the same torsion prelude (`divNHom` … `card_torsionBy_latticeQuotient`,
  `kwLatticeCoeAddEquiv` … `kwSublatticeIndex_scale`) and the same `hID_*` block twice
  (`port_advise` measures 41 names / ≈768 removable lines in the pair). Both are written
  here exactly once. The 2,021 node imports the 978 node's headline for its `hID`.

  **What is imported, not re-proved.** The pin's inlined uniformization prelude is the
  port's `Elliptic/PeriodPair/*` modules; the place dictionary and `normFormulaAlong_of_elliptic`
  are `WeierstrassCurve/Place/Dictionary.lean` and `WeierstrassCurve/IsogenyEndDatum/Engine.lean`;
  `ModularCurve.KwD5BetweenCurvesHoloLift` is D-5's `Isogeny/KernelBaseChange.lean` (imported,
  never redeclared); and the `toPointHom` promotion set
  (`PeriodPair.{toPointHom,toPointHom_apply,ker_toPointHom,discriminantNeZero,toPointAddEquiv}`)
  is `Elliptic/PeriodPair/Uniformization.lean`. In particular the 2,021 `solution`'s
  re-derivation of `hH2` is replaced by the ported
  `ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift` (S-1, `HoloLift.lean`), and `hID`
  by this module's `ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved`.

  **Pin-private helpers re-derived here.** `mem_scale_lattice_iff` and the interior steps of
  the `kqe_*` engine are pin-`private` and are re-derived `private`: `mem_scale_lattice_iff`
  (from the public `PeriodPair.scale_lattice`), the covering/Liouville layer
  (`sub_fract_mem_lattice`, `apply_eq_apply_of_differentiable_of_forall_periodic`,
  `apply_eq_apply_of_continuous_of_mapsTo_lattice`), the affine extraction
  (`exists_smul_mem_and_apply_eq_of_forall_sub_mem`, ≈69 lines, the one drag `port_advise`
  reports as new), `toPoint_add_mem`, and `infinite_point` (the pin's
  `kw_infinite_quotientLattice`/`kw_infinite_point`). The pin's `mulLeftR`/`mulLeftZ` are not
  needed: `mem_scale_lattice_iff` is read off the already-ported `scale_lattice`.
  `Uncountable ℝ` (used for `infinite_point`) needs `Mathlib/Analysis/Real/Cardinality.lean`,
  which is not in the pin's explicit list but is a specific mathlib module, not `import Mathlib`.

  **Not transcribed.** The pin's `attribute [-instance]`/`attribute [-simp]` blocks, its
  `p2m_*` scaffolding, the `*_axiomAnchor : True` stubs, `MilneI72IntersectionData` (a
  `structure` with no uses), and the 2,021 file's duplicate copies of the shared blocks. The
  pin's `set_option maxHeartbeats 6400000` / `synthInstance.maxHeartbeats 8000000` are not
  transcribed either: the port's cap is 4,000,000.

  Reference (public mirror, pinned):
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker.lean>
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_PeriodPair_exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient.lean>
-/
import FLTForHuman.Elliptic.PeriodPair.Basic
import FLTForHuman.Elliptic.PeriodPair.Lattice
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.Elliptic.PeriodPair.Uniformization
import FLTForHuman.Elliptic.PeriodPair.HoloLift
import FLTForHuman.WeierstrassCurve.Isogeny.ConditionalCurrency
import FLTForHuman.WeierstrassCurve.Isogeny.KernelBaseChange
import FLTForHuman.WeierstrassCurve.IsogenyEndDatum.Engine
import FLTForHuman.WeierstrassCurve.Place.Dictionary
import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.Analysis.Real.Cardinality
import Mathlib.LinearAlgebra.FreeModule.Finite.CardQuotient
import Mathlib.LinearAlgebra.FreeModule.ModN
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Tactic

noncomputable section

open scoped PeriodPair UpperHalfPlane
open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## The `PeriodPair` scale layer and the analytic extraction -/

namespace PeriodPair

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

section Gates

variable (L : PeriodPair)

/-- Pin `gate_scale_mul` (`:420` in the 978 file): rescaling twice is rescaling by the
product.  Shared by the two target files (`gate_scale_mul` ships 6 times in the pin). -/
theorem gate_scale_mul (α β : ℂˣ) :
    ((L.scale α).scale β).lattice = (L.scale (β * α)).lattice := by
  ext z
  simp only [mem_scale_lattice_iff, Units.val_mul]
  constructor
  · rintro ⟨-, ⟨l, hl, rfl⟩, rfl⟩; exact ⟨l, hl, (mul_assoc _ _ _).symm⟩
  · rintro ⟨l, hl, rfl⟩; exact ⟨(α : ℂ) * l, ⟨l, hl, rfl⟩, mul_assoc _ _ _⟩

end Gates

section Liouville

variable (L : PeriodPair)

/-- Pin `sub_fract_mem_lattice` (private). -/
private theorem sub_fract_mem_lattice (z : ℂ) : z - ZSpan.fract L.basis z ∈ L.lattice := by
  rw [L.lattice_eq_span_range_basis]
  have h := (ZSpan.fract_eq_fract L.basis (ZSpan.fract L.basis z) z).mp
    (by rw [ZSpan.fract_eq_self.mpr (ZSpan.fract_mem_fundamentalDomain L.basis z)])
  simpa [neg_add_eq_sub] using h

/-- Pin `apply_eq_apply_of_differentiable_of_forall_periodic` (private): a differentiable
lattice-periodic function on `ℂ` is constant. -/
private theorem apply_eq_apply_of_differentiable_of_forall_periodic {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hper : ∀ l ∈ L.lattice, ∀ z, f (z + l) = f z) (z w : ℂ) :
    f z = f w := by
  apply hf.apply_eq_apply_of_bounded
  have hrange : Set.range f ⊆ f '' closure (ZSpan.fundamentalDomain L.basis) := by
    rintro - ⟨u, rfl⟩
    refine ⟨ZSpan.fract L.basis u, subset_closure (ZSpan.fract_mem_fundamentalDomain _ u), ?_⟩
    have h := hper _ (sub_fract_mem_lattice L u) (ZSpan.fract L.basis u)
    rw [add_sub_cancel] at h
    exact h.symm
  refine Bornology.IsBounded.subset ?_ hrange
  refine (IsCompact.image ?_ hf.continuous).isBounded
  exact Metric.isCompact_of_isClosed_isBounded isClosed_closure
    (ZSpan.fundamentalDomain_isBounded L.basis).closure

/-- Pin `apply_eq_apply_of_continuous_of_mapsTo_lattice` (private): a continuous map into
the discrete lattice is constant. -/
private theorem apply_eq_apply_of_continuous_of_mapsTo_lattice {f : ℂ → ℂ} (hf : Continuous f)
    (hmem : ∀ z, f z ∈ L.lattice) (z w : ℂ) : f z = f w := by
  refine IsPreconnected.constant_of_mapsTo (isPreconnected_univ) ?_
    hf.continuousOn (fun u _ => hmem u) (Set.mem_univ z) (Set.mem_univ w)
  rw [isDiscrete_iff_discreteTopology]
  exact inferInstanceAs (DiscreteTopology L.lattice)

/-- Pin `exists_smul_mem_and_apply_eq_of_forall_sub_mem` (private, ≈69 lines): a
differentiable function whose lattice-translates stay in `L'` is affine.  `port_advise`
reports this as the one genuinely new drag of the 2,021 file. -/
private theorem exists_smul_mem_and_apply_eq_of_forall_sub_mem (L' : PeriodPair) {F : ℂ → ℂ}
    (hF : Differentiable ℂ F)
    (hper : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z ∈ L'.lattice) :
    ∃ α : ℂ, (∀ l ∈ L.lattice, α * l ∈ L'.lattice) ∧ ∀ z, F z = F 0 + α * z := by
  have hFc : Continuous F := hF.continuous
  have hconst : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z = F l - F 0 := by
    intro l hl z
    have h := apply_eq_apply_of_continuous_of_mapsTo_lattice (L := L')
      (f := fun u => F (u + l) - F u)
      ((hFc.comp (continuous_id.add continuous_const)).sub hFc) (hper l hl) z 0
    simpa using h
  have hadd : ∀ z w, F (z + w) = F z + F w - F 0 := by
    intro z w
    have hper' : ∀ l ∈ L.lattice, ∀ u,
        (fun u => F (u + w) - F u) (u + l) = (fun u => F (u + w) - F u) u := by
      intro l hl u
      have h1 := hconst l hl (u + w)
      have h2 := hconst l hl u
      rw [show u + w + l = u + l + w by ring] at h1
      simp only
      linear_combination h1 - h2
    have h := apply_eq_apply_of_differentiable_of_forall_periodic (L := L)
      (f := fun u => F (u + w) - F u)
      ((hF.comp (differentiable_id.add_const w)).sub hF) hper' z 0
    simp only [zero_add] at h
    linear_combination h
  set α : ℂ := deriv F 0 with hα
  have hderiv : ∀ z, deriv F z = α := by
    intro z
    have hfun : (fun w => F (z + w)) = fun w => F w + (F z - F 0) := by
      funext w
      rw [hadd z w]; ring
    have h1 : deriv (fun w => F (z + w)) 0 = deriv F z := by
      rw [deriv_comp_const_add]
      simp
    have h2 : deriv (fun w => F w + (F z - F 0)) 0 = deriv F 0 := by
      rw [deriv_add_const]
    rw [← h1, hfun, h2]
  have haffine : ∀ z, F z = F 0 + α * z := by
    have hG : Differentiable ℂ fun z => F z - α * z :=
      hF.sub (differentiable_id.const_mul α)
    have hG' : ∀ z, deriv (fun z => F z - α * z) z = 0 := by
      intro z
      have hd : HasDerivAt (fun z => F z - α * z) (deriv F z - α * 1) z :=
        (hF z).hasDerivAt.sub ((hasDerivAt_id z).const_mul α)
      rw [hd.deriv, hderiv z]
      ring
    intro z
    have h := is_const_of_deriv_eq_zero hG hG' z 0
    simp only [mul_zero, sub_zero] at h
    linear_combination h
  refine ⟨α, fun l hl => ?_, haffine⟩
  have h := hper l hl 0
  rw [zero_add, haffine l] at h
  simpa using h

/-- The point group of a complex elliptic curve is infinite (pin
`kw_infinite_quotientLattice`/`kw_infinite_point`, private). -/
private theorem infinite_point (L : PeriodPair) : Infinite L.weierstrassCurve.toAffine.Point := by
  have hcount : (L.lattice : Set ℂ).Countable := by
    refine (Set.countable_range fun p : ℤ × ℤ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂).mono ?_
    intro z hz
    obtain ⟨m, n, h⟩ := mem_lattice.mp hz
    exact ⟨(m, n), h⟩
  have hquot : Infinite (ℂ ⧸ L.lattice.toAddSubgroup) := by
    rw [← not_finite_iff_infinite]
    intro hfin
    haveI : Countable L.lattice.toAddSubgroup := Set.countable_coe_iff.mpr hcount
    haveI : Countable ((ℂ ⧸ L.lattice.toAddSubgroup) × L.lattice.toAddSubgroup) := inferInstance
    have hCc : Countable ℂ := Countable.of_equiv _
      (AddSubgroup.addGroupEquivQuotientProdAddSubgroup (s := L.lattice.toAddSubgroup)).symm
    haveI : Uncountable ℂ := Complex.ofReal_injective.uncountable
    exact absurd hCc not_countable
  exact L.toPointAddEquiv.toEquiv.infinite_iff.mp hquot

/-- Pin `toPoint_add_mem` (public in the pin, `private` in the port's `Uniformization.lean`):
`toPoint` is invariant under lattice translation. -/
private theorem toPoint_add_mem (L : PeriodPair) (h : L.DiscriminantNeZero) (z : ℂ) {l : ℂ}
    (hl : l ∈ L.lattice) : L.toPoint h (z + l) = L.toPoint h z := by
  by_cases hz : z ∈ L.lattice
  · rw [L.toPoint_of_mem h hz, L.toPoint_of_mem h (add_mem hz hl)]
  · have hzl : z + l ∉ L.lattice := fun hmem => hz (by simpa using sub_mem hmem hl)
    rw [L.toPoint_of_notMem h hz, L.toPoint_of_notMem h hzl]
    have hP : ℘[L] (z + l) = ℘[L] z := L.weierstrassP_add_coe z ⟨l, hl⟩
    have hP' : ℘'[L] (z + l) = ℘'[L] z := L.derivWeierstrassP_add_coe z ⟨l, hl⟩
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hP, by rw [hP']⟩

end Liouville

end PeriodPair

/-! ## The torsion prelude, the `zlattice` count, and the index/scale API -/

namespace ModularCurve

section LatticeQuotient

variable {V : Type*} [AddCommGroup V] [DivisibleBy V ℤ] [NoZeroSMulDivisors ℤ V]

/-- Pin `divNHom`: division by `n` as an additive homomorphism on a divisible group. -/
def divNHom (n : ℤ) (hn : n ≠ 0) : V →+ V where
  toFun v := DivisibleBy.div v n
  map_zero' := smul_right_injective V hn (by
    show n • DivisibleBy.div (0 : V) n = n • 0
    rw [DivisibleBy.div_cancel _ hn, smul_zero])
  map_add' a b := smul_right_injective V hn (by
    show n • DivisibleBy.div (a + b) n = n • (DivisibleBy.div a n + DivisibleBy.div b n)
    rw [smul_add, DivisibleBy.div_cancel _ hn, DivisibleBy.div_cancel _ hn,
      DivisibleBy.div_cancel _ hn])

@[scoped simp] theorem smul_divNHom (n : ℤ) (hn : n ≠ 0) (v : V) :
    n • divNHom n hn v = v :=
  DivisibleBy.div_cancel v hn

theorem divNHom_smul (n : ℤ) (hn : n ≠ 0) (v : V) :
    divNHom n hn (n • v) = v :=
  smul_right_injective V hn
    (show n • divNHom n hn (n • v) = n • v from smul_divNHom n hn (n • v))

variable (Λ : AddSubgroup V) {n : ℕ}

/-- Pin `latticeDivQuot`: `Λ → Λ'/nΛ'` through division by `n`. -/
def latticeDivQuot (hn : (n : ℤ) ≠ 0) :
    ↥Λ →+ Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ) where
  toFun w := ⟨QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)), by
    rw [Submodule.mem_torsionBy_iff]
    show (n : ℤ) • (QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)) : V ⧸ Λ) = 0
    rw [← QuotientAddGroup.mk_zsmul, smul_divNHom]
    exact (QuotientAddGroup.eq_zero_iff _).mpr w.2⟩
  map_zero' := by
    apply Subtype.ext
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((0 : ↥Λ) : V)) : V ⧸ Λ) = 0
    simp
  map_add' a b := by
    apply Subtype.ext
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn (((a + b : ↥Λ)) : V)) : V ⧸ Λ)
        = QuotientAddGroup.mk (divNHom (n : ℤ) hn (a : V))
          + QuotientAddGroup.mk (divNHom (n : ℤ) hn (b : V))
    push_cast
    rw [map_add, QuotientAddGroup.mk_add]

@[scoped simp] theorem coe_latticeDivQuot (hn : (n : ℤ) ≠ 0) (w : ↥Λ) :
    ((latticeDivQuot Λ hn w : Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) : V ⧸ Λ)
      = QuotientAddGroup.mk (divNHom (n : ℤ) hn (w : V)) :=
  rfl

theorem latticeDivQuot_surjective (hn : (n : ℤ) ≠ 0) :
    Function.Surjective (latticeDivQuot Λ hn) := by
  rintro ⟨x, hx⟩
  rw [Submodule.mem_torsionBy_iff] at hx
  obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hvΛ : (n : ℤ) • v ∈ Λ := by
    rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]
    exact hx
  refine ⟨⟨(n : ℤ) • v, hvΛ⟩, Subtype.ext ?_⟩
  rw [coe_latticeDivQuot]
  show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((n : ℤ) • v)) : V ⧸ Λ)
      = QuotientAddGroup.mk v
  rw [divNHom_smul]

theorem mem_ker_latticeDivQuot (hn : (n : ℤ) ≠ 0) (w : ↥Λ) :
    w ∈ (latticeDivQuot Λ hn).ker
      ↔ w ∈ LinearMap.range (LinearMap.lsmul ℤ ↥Λ (n : ℤ)) := by
  constructor
  · intro hker
    rw [AddMonoidHom.mem_ker] at hker
    have hcoe : ((latticeDivQuot Λ hn w :
        Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) : V ⧸ Λ) = 0 := by
      rw [hker]; rfl
    rw [coe_latticeDivQuot, QuotientAddGroup.eq_zero_iff] at hcoe
    refine ⟨⟨divNHom (n : ℤ) hn (w : V), hcoe⟩, ?_⟩
    apply Subtype.ext
    show (n : ℤ) • divNHom (n : ℤ) hn (w : V) = (w : V)
    exact smul_divNHom (n : ℤ) hn (w : V)
  · rintro ⟨μ, rfl⟩
    rw [AddMonoidHom.mem_ker]
    apply Subtype.ext
    rw [coe_latticeDivQuot]
    show (QuotientAddGroup.mk (divNHom (n : ℤ) hn ((n : ℤ) • (μ : V))) : V ⧸ Λ) = 0
    rw [divNHom_smul, QuotientAddGroup.eq_zero_iff]
    exact μ.2

theorem ker_latticeDivQuot (hn : (n : ℤ) ≠ 0) :
    (latticeDivQuot Λ hn).ker
      = (LinearMap.range (LinearMap.lsmul ℤ ↥Λ (n : ℤ))).toAddSubgroup := by
  ext w
  exact mem_ker_latticeDivQuot Λ hn w

/-- Pin `latticeQuotTorsionEquiv`: `Λ'/nΛ' ≃ (Λ'/nΛ)[n]`. -/
def latticeQuotTorsionEquiv (hn : (n : ℤ) ≠ 0) :
    ModN ↥Λ n ≃+ Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ) := by
  refine AddEquiv.ofBijective
    (QuotientAddGroup.lift _ (latticeDivQuot Λ hn) ?_) ⟨?_, ?_⟩
  · intro w hw
    have : w ∈ (latticeDivQuot Λ hn).ker := by
      rw [ker_latticeDivQuot]; exact hw
    exact this
  · rintro ⟨a⟩ ⟨b⟩ hab
    refine (Submodule.Quotient.eq _).mpr ?_
    have hker : a - b ∈ (latticeDivQuot Λ hn).ker := by
      rw [AddMonoidHom.mem_ker, map_sub]
      exact sub_eq_zero.mpr hab
    rwa [ker_latticeDivQuot] at hker
  · intro y
    obtain ⟨w, hw⟩ := latticeDivQuot_surjective Λ hn y
    exact ⟨QuotientAddGroup.mk w, hw⟩

/-- Pin `card_torsionBy_latticeQuotient`: the `n`-torsion of `Λ'/nΛ'` has `n ^ finrank ℤ Λ`
elements. -/
theorem card_torsionBy_latticeQuotient [Module.Free ℤ ↥Λ] [Module.Finite ℤ ↥Λ]
    (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (V ⧸ Λ) (n : ℤ)) = n ^ Module.finrank ℤ ↥Λ := by
  haveI : NeZero n := ⟨by exact_mod_cast hn⟩
  rw [← Nat.card_congr (latticeQuotTorsionEquiv Λ hn).toEquiv, ModN.natCard_eq]

end LatticeQuotient

section ZLatticeTorsion

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

scoped instance (priority := low) kwRealModuleDivisibleByInt : DivisibleBy E ℤ where
  div v n := ((n : ℝ)⁻¹) • v
  div_zero v := by simp
  div_cancel {n} v hn := by
    have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
    calc n • ((n : ℝ)⁻¹ • v) = (n : ℝ) • ((n : ℝ)⁻¹ • v) := (Int.cast_smul_eq_zsmul ℝ n _).symm
      _ = v := by rw [smul_smul, mul_inv_cancel₀ hn', one_smul]

scoped instance (priority := low) kwRealModuleNoZeroSMulDivisorsInt : NoZeroSMulDivisors ℤ E where
  eq_zero_or_eq_zero_of_smul_eq_zero {n} {v} h := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl rfl
    · refine Or.inr ?_
      have h' : (n : ℝ) • v = 0 := by rwa [Int.cast_smul_eq_zsmul ℝ]
      have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
      exact (smul_eq_zero.mp h').resolve_left hn'

variable [FiniteDimensional ℝ E] [ProperSpace E]
variable (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- Pin `kwLatticeCoeAddEquiv`: `L` and its underlying `AddSubgroup` are additively
equivalent by the identity. -/
def kwLatticeCoeAddEquiv : L ≃+ L.toAddSubgroup where
  toFun x := ⟨(x : E), x.2⟩
  invFun x := ⟨(x : E), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

scoped instance kwLatticeToAddSubgroupFree : Module.Free ℤ (L.toAddSubgroup) :=
  have : Module.Free ℤ L := ZLattice.module_free ℝ L
  Module.Free.of_equiv (kwLatticeCoeAddEquiv L).toIntLinearEquiv

scoped instance kwLatticeToAddSubgroupFinite : Module.Finite ℤ (L.toAddSubgroup) :=
  have : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  Module.Finite.equiv (kwLatticeCoeAddEquiv L).toIntLinearEquiv

/-- Pin `kw_card_torsionBy_zlatticeQuotient`. -/
theorem kw_card_torsionBy_zlatticeQuotient {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E ⧸ L.toAddSubgroup) (n : ℤ)) =
      n ^ Module.finrank ℤ L := by
  have h := card_torsionBy_latticeQuotient (V := E) (L.toAddSubgroup) hn
  rw [h]
  exact congrArg (fun k => n ^ k)
    (LinearEquiv.finrank_eq (kwLatticeCoeAddEquiv L).toIntLinearEquiv).symm

/-- Pin `kw_card_torsionBy_zlatticeQuotient_finrank_real`. -/
theorem kw_card_torsionBy_zlatticeQuotient_finrank_real
    {n : ℕ} (hn : (n : ℤ) ≠ 0) :
    Nat.card (Submodule.torsionBy ℤ (E ⧸ L.toAddSubgroup) (n : ℤ)) =
      n ^ Module.finrank ℝ E := by
  rw [kw_card_torsionBy_zlatticeQuotient L hn, ZLattice.rank ℝ L]

end ZLatticeTorsion

/-- Pin `kw_scale_lattice_toAddSubgroup`. -/
theorem kw_scale_lattice_toAddSubgroup (L : PeriodPair) (α : ℂˣ) :
    (L.scale α).lattice.toAddSubgroup
      = L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft (α : ℂ)) := by
  ext z
  simp only [Submodule.mem_toAddSubgroup, PeriodPair.mem_scale_lattice_iff L α,
    AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
  exact ⟨fun ⟨l, hl, hz⟩ => ⟨l, hl, hz.symm⟩, fun ⟨l, hl, hz⟩ => ⟨l, hl, hz.symm⟩⟩

/-- Pin `kwSublatticeIndex_scale`: the sublattice index is invariant under rescaling
both pairs by the same unit. -/
theorem kwSublatticeIndex_scale (L L' : PeriodPair) (α : ℂˣ) :
    PeriodPair.sublatticeIndex (L.scale α) (L'.scale α) = PeriodPair.sublatticeIndex L L' := by
  have hinj : Function.Injective (AddMonoidHom.mulLeft (α : ℂ)) :=
    fun _ _ h => mul_left_cancel₀ α.ne_zero h
  change AddSubgroup.relIndex _ _ = AddSubgroup.relIndex _ _
  rw [kw_scale_lattice_toAddSubgroup, kw_scale_lattice_toAddSubgroup,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

/-! ## The `KwD5BetweenCurvesIndexDual` class and the `hID_*` engine -/

/-- Pin `KwD5BetweenCurvesIndexDual` (the 978 copy: the weaker, gate-free form, which is
the one `kw_surgehgf4_hID_betweenCurvesIndexDual_proved` proves). -/
def KwD5BetweenCurvesIndexDual : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point),
    (∀ z, L'.toPointHom ((α : ℂ) * z) = ψ (L.toPointHom z)) →
    ∃ (β : ℂˣ), ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker

section BetweenCurves

variable (L L' : PeriodPair)
  [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
  (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hint : ∀ z, L'.toPointHom ((α : ℂ) * z) = ψ (L.toPointHom z))

include hint in

/-- Pin `kw_surgehgf4_hID_kerIndexHom`: `L'.lattice → ψ.ker`, `l' ↦ α⁻¹ l'`. -/
def kw_surgehgf4_hID_kerIndexHom : L'.lattice.toAddSubgroup →+ ψ.ker where
  toFun l' := ⟨L.toPointHom ((α : ℂ)⁻¹ * (l' : ℂ)), by
    rw [AddMonoidHom.mem_ker, ← hint ((α : ℂ)⁻¹ * (l' : ℂ)),
      mul_inv_cancel_left₀ α.ne_zero]
    have hl'0 : L'.toPointHom (l' : ℂ) = 0 := by
      rw [← AddMonoidHom.mem_ker, L'.ker_toPointHom]; exact l'.2
    exact hl'0⟩
  map_zero' := Subtype.ext <| by simp
  map_add' l'₁ l'₂ := Subtype.ext <| by
    push_cast; rw [mul_add]; exact map_add L.toPointHom _ _

include hint in
theorem kw_surgehgf4_hID_kerIndexHom_apply (l' : L'.lattice.toAddSubgroup) :
    (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint l' : L.weierstrassCurve.toAffine.Point)
      = L.toPointHom ((α : ℂ)⁻¹ * (l' : ℂ)) := rfl

include hint in

theorem kw_surgehgf4_hID_scale_subset :
    ((L.scale α).lattice : Set ℂ) ⊆ L'.lattice := by
  intro z hz
  rw [SetLike.mem_coe, PeriodPair.mem_scale_lattice_iff L α] at hz
  obtain ⟨l, hl, rfl⟩ := hz
  rw [SetLike.mem_coe, ← Submodule.mem_toAddSubgroup, ← L'.ker_toPointHom,
    AddMonoidHom.mem_ker, hint]
  have hl0 : L.toPointHom l = 0 := by
    rw [← AddMonoidHom.mem_ker, L.ker_toPointHom]; exact hl
  rw [hl0, map_zero]

include hint in

theorem kw_surgehgf4_hID_kerIndexHom_surjective :
    Function.Surjective (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint) := by
  rintro ⟨P, hP⟩
  obtain ⟨z, hz⟩ := (L.isUniformization_toPoint L.discriminantNeZero).2.1 P
  have hαz : (α : ℂ) * z ∈ L'.lattice.toAddSubgroup := by
    rw [← L'.ker_toPointHom, AddMonoidHom.mem_ker, hint, L.toPointHom_apply, hz]
    exact hP
  exact ⟨⟨(α : ℂ) * z, hαz⟩, Subtype.ext <| by
    simp only [kw_surgehgf4_hID_kerIndexHom_apply, inv_mul_cancel_left₀ α.ne_zero,
      L.toPointHom_apply, hz]⟩

include hint in

theorem kw_surgehgf4_hID_ker_kerIndexHom :
    (kw_surgehgf4_hID_kerIndexHom L L' α ψ hint).ker
      = (L.scale α).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup := by
  ext ⟨l', hl'⟩
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_scale_lattice_iff L α]
    refine ⟨(α : ℂ)⁻¹ * l', ?_, (mul_inv_cancel_left₀ α.ne_zero l').symm⟩
    have h0 : L.toPointHom ((α : ℂ)⁻¹ * l') = 0 := Subtype.ext_iff.mp h
    rwa [← AddMonoidHom.mem_ker, L.ker_toPointHom, Submodule.mem_toAddSubgroup] at h0
  · intro h
    rw [Submodule.mem_toAddSubgroup, PeriodPair.mem_scale_lattice_iff L α] at h
    obtain ⟨v, hv, hvl'⟩ := h
    apply Subtype.ext
    show L.toPointHom ((α : ℂ)⁻¹ * l') = 0
    rw [show (l' : ℂ) = (α : ℂ) * v from hvl', inv_mul_cancel_left₀ α.ne_zero,
      ← AddMonoidHom.mem_ker, L.ker_toPointHom]
    exact hv

include hint in

theorem kw_surgehgf4_hID_forwardIndex_eq_card_ker :
    PeriodPair.sublatticeIndex L' (L.scale α) = Nat.card ψ.ker := by
  unfold PeriodPair.sublatticeIndex
  rw [← kw_surgehgf4_hID_ker_kerIndexHom L L' α ψ hint, ← Nat.card_congr
    (QuotientAddGroup.liftEquiv _
      (kw_surgehgf4_hID_kerIndexHom_surjective L L' α ψ hint) rfl).toEquiv]
  rfl

include hint in

theorem kw_surgehgf4_hID_card_smul_subset :
    ∀ l' ∈ L'.lattice, (Nat.card ψ.ker : ℂ) * l' ∈ (L.scale α).lattice := by
  intro l' hl'
  set N := Nat.card ψ.ker with hNdef
  have hidx : ((L.scale α).lattice.toAddSubgroup.addSubgroupOf
      L'.lattice.toAddSubgroup).index = N := by
    have h := kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint
    unfold PeriodPair.sublatticeIndex at h; exact h
  set H := (L.scale α).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup with hHdef
  have hmem : N • (⟨l', hl'⟩ : L'.lattice.toAddSubgroup) ∈ H := hidx ▸ H.nsmul_index_mem _
  rw [hHdef, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at hmem
  have heq : ((N • (⟨l', hl'⟩ : L'.lattice.toAddSubgroup) : L'.lattice.toAddSubgroup) : ℂ)
      = (Nat.card ψ.ker : ℂ) * l' := by
    rw [AddSubmonoidClass.coe_nsmul, nsmul_eq_mul, hNdef]
  rw [← heq]; exact hmem

end BetweenCurves

/-- Pin `kw_surgehgf4_hID_dualUnit`: the dual homothety `(N : ℂ) * α⁻¹`. -/
noncomputable def kw_surgehgf4_hID_dualUnit {X Y : Type*} [AddGroup X] [AddGroup Y]
    (α : ℂˣ) (ψ : X →+ Y) (hN : 0 < Nat.card ψ.ker) : ℂˣ :=
  Units.mk0 (Nat.card ψ.ker : ℂ) (by exact_mod_cast hN.ne') * α⁻¹

theorem kw_surgehgf4_hID_dualUnit_val {X Y : Type*} [AddGroup X] [AddGroup Y]
    (α : ℂˣ) (ψ : X →+ Y) (hN : 0 < Nat.card ψ.ker) :
    (kw_surgehgf4_hID_dualUnit α ψ hN : ℂ) = (Nat.card ψ.ker : ℂ) * (α : ℂ)⁻¹ := by
  simp only [kw_surgehgf4_hID_dualUnit, Units.val_mul, Units.val_mk0,
    Units.val_inv_eq_inv_val]

section BetweenCurves

variable (L L' : PeriodPair)
  [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
  (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hint : ∀ z, L'.toPointHom ((α : ℂ) * z) = ψ (L.toPointHom z))

include hint in

theorem kw_surgehgf4_hID_dual_subset (hN : 0 < Nat.card ψ.ker) :
    ((L'.scale (kw_surgehgf4_hID_dualUnit α ψ hN)).lattice : Set ℂ) ⊆ L.lattice := by
  intro z hz
  rw [SetLike.mem_coe,
    PeriodPair.mem_scale_lattice_iff L' (kw_surgehgf4_hID_dualUnit α ψ hN)] at hz
  obtain ⟨l', hl', rfl⟩ := hz
  have hNl' := kw_surgehgf4_hID_card_smul_subset L L' α ψ hint l' hl'
  rw [PeriodPair.mem_scale_lattice_iff L α] at hNl'
  obtain ⟨v, hv, hveq⟩ := hNl'
  rw [SetLike.mem_coe, kw_surgehgf4_hID_dualUnit_val α ψ hN, mul_assoc,
    show (Nat.card ψ.ker : ℂ) * ((α : ℂ)⁻¹ * l')
      = (α : ℂ)⁻¹ * ((Nat.card ψ.ker : ℂ) * l') from by ring,
    hveq, inv_mul_cancel_left₀ α.ne_zero]
  exact hv

theorem kw_surgehgf4_hID_sublatticeIndex_congr_snd {A M M' : PeriodPair}
    (h : M.lattice = M'.lattice) :
    PeriodPair.sublatticeIndex A M = PeriodPair.sublatticeIndex A M' := by
  unfold PeriodPair.sublatticeIndex; rw [h]

/-- Pin `kw_surgehgf4_hID_scaleIndexHom`: `M.lattice → (ℂ/M.lattice)[N]`. -/
def kw_surgehgf4_hID_scaleIndexHom (M : PeriodPair) {N : ℕ} (hN : 0 < N) :
    M.lattice.toAddSubgroup
      →+ (Submodule.torsionBy ℤ (ℂ ⧸ M.lattice.toAddSubgroup) (N : ℤ)) where
  toFun l := ⟨QuotientAddGroup.mk ((N : ℂ)⁻¹ * (l : ℂ)), by
    rw [Submodule.mem_torsionBy_iff, ← QuotientAddGroup.mk_zsmul,
      QuotientAddGroup.eq_zero_iff]
    have hNne : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
    have : (N : ℤ) • ((N : ℂ)⁻¹ * (l : ℂ)) = (l : ℂ) := by
      rw [zsmul_eq_mul, Int.cast_natCast, mul_inv_cancel_left₀ hNne]
    rw [this]; exact l.2⟩
  map_zero' := Subtype.ext <| by simp
  map_add' l₁ l₂ := Subtype.ext <| by
    simp only [AddSubgroup.coe_add, mul_add]
    rfl

/-- Pin `kw_surgehgf4_hID_sublatticeIndex_scale_nat`: scaling by `N` has index `N ^ 2`. -/
theorem kw_surgehgf4_hID_sublatticeIndex_scale_nat (M : PeriodPair)
    {N : ℕ} (hN : 0 < N) :
    PeriodPair.sublatticeIndex M (M.scale (Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne'))) = N ^ 2 := by
  set Nu := Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne') with hNudef
  have hNuval : (Nu : ℂ) = (N : ℂ) := by rw [hNudef, Units.val_mk0]
  have hNinv : (Nu : ℂ)⁻¹ = (N : ℂ)⁻¹ := by rw [hNuval]
  have hsurj : Function.Surjective (kw_surgehgf4_hID_scaleIndexHom M hN) := by
    rintro ⟨x, hx⟩
    rw [Submodule.mem_torsionBy_iff] at hx
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
    have hNz : (N : ℂ) * z ∈ M.lattice.toAddSubgroup := by
      have : (N : ℤ) • z ∈ M.lattice.toAddSubgroup := by
        rw [← QuotientAddGroup.eq_zero_iff, QuotientAddGroup.mk_zsmul]; exact hx
      simpa [zsmul_eq_mul] using this
    refine ⟨⟨(N : ℂ) * z, hNz⟩, Subtype.ext ?_⟩
    show QuotientAddGroup.mk ((N : ℂ)⁻¹ * ((N : ℂ) * z)) = QuotientAddGroup.mk z
    rw [inv_mul_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]
  have hker : (kw_surgehgf4_hID_scaleIndexHom M hN).ker
      = (M.scale Nu).lattice.toAddSubgroup.addSubgroupOf M.lattice.toAddSubgroup := by
    ext ⟨l, hl⟩
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
      PeriodPair.mem_scale_lattice_iff M Nu]
    constructor
    · intro h0
      have h0' : (N : ℂ)⁻¹ * l ∈ M.lattice.toAddSubgroup := by
        have := Subtype.ext_iff.mp h0
        simp only [kw_surgehgf4_hID_scaleIndexHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          ZeroMemClass.coe_zero] at this
        rwa [QuotientAddGroup.eq_zero_iff] at this
      exact ⟨(N : ℂ)⁻¹ * l, h0',
        by rw [hNuval, mul_inv_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]⟩
    · rintro ⟨v, hv, hvl⟩
      apply Subtype.ext
      show QuotientAddGroup.mk ((N : ℂ)⁻¹ * l) = 0
      rw [QuotientAddGroup.eq_zero_iff,
        show l = (N : ℂ) * v from hNuval ▸ hvl,
        inv_mul_cancel_left₀ (by exact_mod_cast hN.ne' : (N : ℂ) ≠ 0)]
      exact hv
  have htor : Nat.card ↥(Submodule.torsionBy ℤ (ℂ ⧸ M.lattice.toAddSubgroup) (N : ℤ))
      = N ^ 2 := by
    rw [kw_card_torsionBy_zlatticeQuotient_finrank_real M.lattice
      (by exact_mod_cast hN.ne' : (N : ℤ) ≠ 0), Complex.finrank_real_complex]
  unfold PeriodPair.sublatticeIndex
  rw [← hker, ← htor, ← Nat.card_congr
    (QuotientAddGroup.liftEquiv _ hsurj rfl).toEquiv]
  rfl

include hint in

theorem kw_surgehgf4_hID_card_ker_pos : 0 < Nat.card ψ.ker := by
  rw [← kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint]
  refine Nat.pos_of_ne_zero ?_
  have hle : (L.scale α).lattice ≤ L'.lattice :=
    fun z hz => kw_surgehgf4_hID_scale_subset L L' α ψ hint hz
  have hcov := ZLattice.covolume_div_covolume_eq_relIndex'
    (L.scale α).lattice L'.lattice hle
  have hpos₁ : (0 : ℝ) < ZLattice.covolume (L.scale α).lattice MeasureTheory.volume :=
    ZLattice.covolume_pos (L.scale α).lattice MeasureTheory.volume
  have hpos₂ : (0 : ℝ) < ZLattice.covolume L'.lattice MeasureTheory.volume :=
    ZLattice.covolume_pos L'.lattice MeasureTheory.volume
  have hratio : (0 : ℝ) < ZLattice.covolume (L.scale α).lattice
      / ZLattice.covolume L'.lattice := div_pos hpos₁ hpos₂
  intro h0
  unfold PeriodPair.sublatticeIndex at h0
  have h0R : ((L.scale α).lattice.toAddSubgroup.relIndex L'.lattice.toAddSubgroup : ℝ)
      = 0 := by exact_mod_cast h0
  rw [← hcov] at h0R
  exact absurd h0R (ne_of_gt hratio)

include hint in

theorem kw_surgehgf4_hID_dualIndex_eq (hN : 0 < Nat.card ψ.ker) :
    PeriodPair.sublatticeIndex L (L'.scale (kw_surgehgf4_hID_dualUnit α ψ hN))
      = Nat.card ψ.ker := by
  set N := Nat.card ψ.ker with hNdef
  set β := kw_surgehgf4_hID_dualUnit α ψ hN with hβdef
  set Nu := Units.mk0 (N : ℂ) (by exact_mod_cast hN.ne') with hNudef
  have h1 : PeriodPair.sublatticeIndex L (L'.scale β)
      = PeriodPair.sublatticeIndex (L.scale α) ((L'.scale β).scale α) :=
    (kwSublatticeIndex_scale L (L'.scale β) α).symm
  have hαβ : α * β = Nu := by
    apply Units.ext
    simp only [hβdef, hNudef, Units.val_mul, kw_surgehgf4_hID_dualUnit_val,
      Units.val_mk0]
    field_simp
    exact_mod_cast hNdef.symm
  have h2 : ((L'.scale β).scale α).lattice = (L'.scale Nu).lattice := by
    rw [PeriodPair.gate_scale_mul L' β α, hαβ]
  have h3 : PeriodPair.sublatticeIndex (L.scale α) ((L'.scale β).scale α)
      = PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu) :=
    kw_surgehgf4_hID_sublatticeIndex_congr_snd h2
  rw [h1, h3]
  have hsub1 : ((L'.scale Nu).lattice : Set ℂ) ⊆ (L.scale α).lattice := by
    intro z hz
    rw [SetLike.mem_coe, PeriodPair.mem_scale_lattice_iff L' Nu] at hz
    obtain ⟨l', hl', rfl⟩ := hz
    simp only [hNudef, Units.val_mk0]
    exact kw_surgehgf4_hID_card_smul_subset L L' α ψ hint l' hl'
  have hsub2 : ((L.scale α).lattice : Set ℂ) ⊆ L'.lattice :=
    kw_surgehgf4_hID_scale_subset L L' α ψ hint
  have htower : PeriodPair.sublatticeIndex L' (L'.scale Nu)
      = PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu)
        * PeriodPair.sublatticeIndex L' (L.scale α) := by
    unfold PeriodPair.sublatticeIndex
    have hle1 : (L'.scale Nu).lattice.toAddSubgroup ≤ (L.scale α).lattice.toAddSubgroup := by
      intro z hz; exact hsub1 hz
    have hle2 : (L.scale α).lattice.toAddSubgroup ≤ L'.lattice.toAddSubgroup := by
      intro z hz; exact hsub2 hz
    exact (AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 hle2).symm
  have hN2 : PeriodPair.sublatticeIndex L' (L'.scale Nu) = N ^ 2 :=
    kw_surgehgf4_hID_sublatticeIndex_scale_nat L' hN
  have hfwd : PeriodPair.sublatticeIndex L' (L.scale α) = N :=
    kw_surgehgf4_hID_forwardIndex_eq_card_ker L L' α ψ hint
  rw [hN2, hfwd] at htower
  have : PeriodPair.sublatticeIndex (L.scale α) (L'.scale Nu) * N = N * N := by
    rw [← htower]; ring
  exact Nat.eq_of_mul_eq_mul_right hN this

theorem kw_surgehgf4_hID_betweenCurvesIndexDual_proved :
    KwD5BetweenCurvesIndexDual := by
  intro L L' _ _ α ψ hint
  have hN := kw_surgehgf4_hID_card_ker_pos L L' α ψ hint
  exact ⟨kw_surgehgf4_hID_dualUnit α ψ hN,
    kw_surgehgf4_hID_dual_subset L L' α ψ hint hN,
    kw_surgehgf4_hID_dualIndex_eq L L' α ψ hint hN⟩

end BetweenCurves

/-! ## The remaining two classes and the three-way assembly -/

/-- Pin `KwD5BetweenCurvesPointHomSublatticeCyclic`. -/
def KwD5BetweenCurvesPointHomSublatticeCyclic : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'')
    (N : ℕ) [NeZero N],
    IsAddCyclic (AddMonoidHom.ker
      (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin''))) →
    Nat.card (AddMonoidHom.ker
      (pointMapOfPushforward ι'' hι'' hfin''
        (normFormulaAlong_of_elliptic ι'' hfin''))) = N →
    ∃ (β : ℂˣ), ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = N ∧
      IsAddCyclic (PeriodPair.sublatticeQuotient L (L'.scale β))

/-- Pin `KwD5BetweenCurvesKerQuotEquivBC`. -/
def KwD5BetweenCurvesKerQuotEquivBC : Prop :=
  ∀ (L L' : PeriodPair)
    [L.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L.weierstrassCurve] [L'.weierstrassCurve.IsElliptic] [WeierstrassCurve.Affine.GenusOnePlaceGate L'.weierstrassCurve] [WeierstrassCurve.Affine.GenusOnePlaceGate.IsCentred L'.weierstrassCurve] [WeierstrassCurve.Affine.AbelTheorem L'.weierstrassCurve]
    (ι'' : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ]
      L.weierstrassCurve.toAffine.FunctionField)
    (hι'' : ι''.toRingHom.IsIntegral) (hfin'' : FiniteAlong ℂ ι'')
    (N : ℕ) [NeZero N],
    let ψ := pointMapOfPushforward ι'' hι'' hfin'' (normFormulaAlong_of_elliptic ι'' hfin'')
    Nat.card ψ.ker = N →
    KwD5BetweenCurvesHoloLift → KwD5BetweenCurvesIndexDual →
    IsAddCyclic ψ.ker →
    ∃ (β : ℂˣ), ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker ∧
      IsAddCyclic (PeriodPair.sublatticeQuotient L (L'.scale β))

/-- Pin `kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three`: `hH2 → hID → hKQE`. -/
theorem kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three
    (hH2 : KwD5BetweenCurvesHoloLift) (hID : KwD5BetweenCurvesIndexDual)
    (hKQE : KwD5BetweenCurvesKerQuotEquivBC) :
    KwD5BetweenCurvesPointHomSublatticeCyclic := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin'' N _ hcyc hcard
  obtain ⟨β, hsub, hidx, hcycQ⟩ := hKQE L L' ι'' hι'' hfin'' N hcard hH2 hID hcyc
  exact ⟨β, hsub, hidx.trans hcard, hcycQ⟩

/-! ## The `kqe_*` engine (the 2,021 file only) -/

section CoreLemma

variable {N : ℕ} [NeZero N]

/-- Pin `kw_surgehgf4_kqe_map_fst`. -/
theorem kw_surgehgf4_kqe_map_fst (φ : ZMod N × ZMod N →+ ZMod N) (x : ZMod N) :
    φ (x, 0) = x * φ (1, 0) := by
  have hx : ((x, 0) : ZMod N × ZMod N) = x.val • ((1, 0) : ZMod N × ZMod N) := by
    simp [Prod.smul_mk, nsmul_eq_mul, ZMod.natCast_val]
  rw [hx, map_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id']
  rfl

/-- Pin `kw_surgehgf4_kqe_map_snd`. -/
theorem kw_surgehgf4_kqe_map_snd (φ : ZMod N × ZMod N →+ ZMod N) (y : ZMod N) :
    φ (0, y) = y * φ (0, 1) := by
  have hy : ((0, y) : ZMod N × ZMod N) = y.val • ((0, 1) : ZMod N × ZMod N) := by
    simp [Prod.smul_mk, nsmul_eq_mul, ZMod.natCast_val]
  rw [hy, map_nsmul, nsmul_eq_mul, ZMod.natCast_val, ZMod.cast_id']
  rfl

/-- Pin `kw_surgehgf4_kqe_map_eq`. -/
theorem kw_surgehgf4_kqe_map_eq (φ : ZMod N × ZMod N →+ ZMod N)
    (p : ZMod N × ZMod N) :
    φ p = p.1 * φ (1, 0) + p.2 * φ (0, 1) := by
  have hp : p = ((p.1, 0) : ZMod N × ZMod N) + (0, p.2) := by ext <;> simp
  conv_lhs => rw [hp]
  rw [map_add, kw_surgehgf4_kqe_map_fst, kw_surgehgf4_kqe_map_snd]

/-- Pin `kw_surgehgf4_kqe_negSwap_mem_ker`. -/
theorem kw_surgehgf4_kqe_negSwap_mem_ker (φ : ZMod N × ZMod N →+ ZMod N) :
    (-φ (0, 1), φ (1, 0)) ∈ φ.ker := by
  rw [AddMonoidHom.mem_ker, kw_surgehgf4_kqe_map_eq]
  ring

/-- Pin `kw_surgehgf4_kqe_addOrderOf_negSwap`. -/
theorem kw_surgehgf4_kqe_addOrderOf_negSwap (a b : ZMod N) :
    addOrderOf ((-b, a) : ZMod N × ZMod N) = Nat.lcm (addOrderOf a) (addOrderOf b) := by
  rw [Prod.addOrderOf, addOrderOf_neg, Nat.lcm_comm]

/-- Pin `kw_surgehgf4_kqe_lcm_addOrderOf_eq`. -/
theorem kw_surgehgf4_kqe_lcm_addOrderOf_eq (φ : ZMod N × ZMod N →+ ZMod N)
    (hφ : Function.Surjective φ) :
    Nat.lcm (addOrderOf (φ (1, 0))) (addOrderOf (φ (0, 1))) = N := by
  set a := φ (1, 0); set b := φ (0, 1)
  refine Nat.dvd_antisymm ?_ ?_
  · exact Nat.lcm_dvd (addOrderOf_dvd_of_nsmul_eq_zero (by simp))
      (addOrderOf_dvd_of_nsmul_eq_zero (by simp))
  · obtain ⟨p, hp⟩ := hφ 1
    have h1 : addOrderOf (p.1 * a + p.2 * b) = N := by
      rw [← kw_surgehgf4_kqe_map_eq, hp]; exact ZMod.addOrderOf_one N
    have hlcm0 : Nat.lcm (addOrderOf a) (addOrderOf b) • (p.1 * a + p.2 * b) = 0 := by
      rw [smul_add]
      have ha0 : Nat.lcm (addOrderOf a) (addOrderOf b) • (p.1 * a) = 0 := by
        rw [nsmul_eq_mul, mul_comm p.1 a, ← mul_assoc, ← nsmul_eq_mul]
        obtain ⟨k, hk⟩ := Nat.dvd_lcm_left (addOrderOf a) (addOrderOf b)
        rw [hk, mul_nsmul, addOrderOf_nsmul_eq_zero, smul_zero, zero_mul]
      have hb0 : Nat.lcm (addOrderOf a) (addOrderOf b) • (p.2 * b) = 0 := by
        rw [nsmul_eq_mul, mul_comm p.2 b, ← mul_assoc, ← nsmul_eq_mul]
        obtain ⟨k, hk⟩ := Nat.dvd_lcm_right (addOrderOf a) (addOrderOf b)
        rw [hk, mul_nsmul, addOrderOf_nsmul_eq_zero, smul_zero, zero_mul]
      rw [ha0, hb0, add_zero]
    calc N = addOrderOf (p.1 * a + p.2 * b) := h1.symm
      _ ∣ Nat.lcm (addOrderOf a) (addOrderOf b) := addOrderOf_dvd_of_nsmul_eq_zero hlcm0

/-- Pin `kw_surgehgf4_kqe_card_ker`. -/
theorem kw_surgehgf4_kqe_card_ker (φ : ZMod N × ZMod N →+ ZMod N)
    (hφ : Function.Surjective φ) :
    Nat.card φ.ker = N := by
  have hG : Nat.card (ZMod N × ZMod N) = N ^ 2 := by simp [sq]
  have hcodom : Nat.card (ZMod N) = N := by simp
  have htot := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm
  rw [hG, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
    hcodom, sq] at htot
  exact Nat.eq_of_mul_eq_mul_left (NeZero.pos N) htot

/-- Pin `kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective`. -/
theorem kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective
    (φ : ZMod N × ZMod N →+ ZMod N) (hφ : Function.Surjective φ) :
    IsAddCyclic φ.ker := by
  set a := φ (1, 0); set b := φ (0, 1)
  set g : φ.ker := ⟨(-b, a), kw_surgehgf4_kqe_negSwap_mem_ker φ⟩ with hgdef
  refine ⟨g, fun x => ?_⟩
  have hg_ord : addOrderOf g = N := by
    have hcoe : addOrderOf g = addOrderOf ((-b, a) : ZMod N × ZMod N) :=
      (AddSubgroup.addOrderOf_coe g).symm
    rw [hcoe, kw_surgehgf4_kqe_addOrderOf_negSwap,
      kw_surgehgf4_kqe_lcm_addOrderOf_eq φ hφ]
  have hgen : AddSubgroup.zmultiples g = ⊤ := by
    refine AddSubgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zmultiples, hg_ord]
    exact (kw_surgehgf4_kqe_card_ker φ hφ).symm
  exact (AddSubgroup.eq_top_iff' _).mp hgen x

/-- Pin `kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective'`. -/
theorem kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective'
    {C : Type*} [AddCommGroup C]
    (φ : ZMod N × ZMod N →+ C) (hφ : Function.Surjective φ)
    (hcard : Nat.card C = N) (hcyc : IsAddCyclic C) :
    IsAddCyclic φ.ker := by
  haveI hfin : Finite C := Nat.finite_of_card_ne_zero (hcard ▸ NeZero.ne N)
  obtain ⟨g, hg⟩ := hcyc
  let e : C ≃+ ZMod N := (zmodAddEquivOfGenerator hg hcard).symm
  have hker_eq : (e.toAddMonoidHom.comp φ).ker = φ.ker := by
    ext x
    rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, AddMonoidHom.comp_apply]
    exact ⟨fun h => e.injective (by rw [_root_.map_zero]; exact h),
      fun h => by rw [h, _root_.map_zero]⟩
  rw [← hker_eq]
  exact kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective _ (e.surjective.comp hφ)

end CoreLemma

section ZModSqEquiv

variable (M : PeriodPair) {N : ℕ} [NeZero N]

local notation "πN" => (Int.castAddHom (ZMod N))

/-- Pin `kw_surgehgf4_kqe_toZModSq`: the lattice coordinates reduced mod `N`. -/
noncomputable def kw_surgehgf4_kqe_toZModSq :
    M.lattice.toAddSubgroup →+ ZMod N × ZMod N :=
  (AddMonoidHom.prodMap πN πN).comp
    (AddMonoidHomClass.toAddMonoidHom M.latticeEquivProd.toAddEquiv)

theorem kw_surgehgf4_kqe_toZModSq_apply (l : M.lattice.toAddSubgroup) :
    kw_surgehgf4_kqe_toZModSq M (N := N) l
      = (((M.latticeEquivProd ⟨l, l.2⟩).1 : ZMod N), ((M.latticeEquivProd ⟨l, l.2⟩).2 : ZMod N)) := by
  rfl

theorem kw_surgehgf4_kqe_toZModSq_surjective :
    Function.Surjective (kw_surgehgf4_kqe_toZModSq M (N := N)) := by
  intro ⟨c₁, c₂⟩
  obtain ⟨n₁, hn₁⟩ := ZMod.intCast_surjective c₁
  obtain ⟨n₂, hn₂⟩ := ZMod.intCast_surjective c₂
  refine ⟨⟨M.latticeEquivProd.symm (n₁, n₂), (M.latticeEquivProd.symm (n₁, n₂)).2⟩, ?_⟩
  rw [kw_surgehgf4_kqe_toZModSq_apply]
  simp [hn₁, hn₂]

theorem kw_surgehgf4_kqe_ker_toZModSq :
    (kw_surgehgf4_kqe_toZModSq M (N := N)).ker
      = (M.scale (Units.mk0 (N : ℂ)
          (by exact_mod_cast NeZero.ne N))).lattice.toAddSubgroup.addSubgroupOf
          M.lattice.toAddSubgroup := by
  ext l
  rw [AddMonoidHom.mem_ker, kw_surgehgf4_kqe_toZModSq_apply, Prod.mk_eq_zero,
    ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd,
    AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
    PeriodPair.mem_scale_lattice_iff M (Units.mk0 (N : ℂ) (by exact_mod_cast NeZero.ne N))]
  set p := M.latticeEquivProd ⟨l, l.2⟩ with hpdef
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨M.latticeEquivProd.symm (a, b), (M.latticeEquivProd.symm (a, b)).2, ?_⟩
    have heq : (⟨(l : ℂ), l.2⟩ : M.lattice) = (N : ℤ) • M.latticeEquivProd.symm (a, b) := by
      apply M.latticeEquivProd.injective
      rw [map_zsmul, LinearEquiv.apply_symm_apply, ← hpdef]
      ext <;> simp [ha, hb, mul_comm]
    have hcoe : (l : ℂ) = (N : ℂ) * (M.latticeEquivProd.symm (a, b) : ℂ) := by
      have := congrArg Subtype.val heq
      simp only [SetLike.val_smul, zsmul_eq_mul, Int.cast_natCast] at this
      exact this
    rw [hcoe, Units.val_mk0]
  · rintro ⟨v, hv, hlv⟩
    have hsub : (⟨(l : ℂ), l.2⟩ : M.lattice) = (N : ℤ) • (⟨v, hv⟩ : M.lattice) := by
      apply Subtype.ext
      simp only [SetLike.val_smul, zsmul_eq_mul, Int.cast_natCast]
      rw [show (l : ℂ) = _ from hlv, Units.val_mk0]
    have hvl : p = (N : ℤ) • M.latticeEquivProd ⟨v, hv⟩ := by
      rw [hpdef, hsub, map_zsmul]
    exact ⟨⟨(M.latticeEquivProd ⟨v, hv⟩).1, by rw [hvl]; simp⟩,
      ⟨(M.latticeEquivProd ⟨v, hv⟩).2, by rw [hvl]; simp⟩⟩

/-- Pin `kw_surgehgf4_kqe_zmodSqEquiv`: `sublatticeQuotient M (M.scale N) ≃ ZMod N × ZMod N`. -/
noncomputable def kw_surgehgf4_kqe_zmodSqEquiv :
    PeriodPair.sublatticeQuotient M (M.scale (Units.mk0 (N : ℂ) (by exact_mod_cast NeZero.ne N)))
      ≃+ ZMod N × ZMod N :=
  (QuotientAddGroup.quotientAddEquivOfEq (kw_surgehgf4_kqe_ker_toZModSq M).symm).trans
    (QuotientAddGroup.liftEquiv _ (kw_surgehgf4_kqe_toZModSq_surjective M) rfl)

end ZModSqEquiv

section Equivs

variable (L L' : PeriodPair)
  [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
  (α : ℂˣ)
  (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
  (hint : ∀ z, L'.toPointHom ((α : ℂ) * z) = ψ (L.toPointHom z))

include hint in
/-- Pin `kw_surgehgf4_kqe_forwardEquiv`: `sublatticeQuotient L' (L.scale α) ≃ ψ.ker`. -/
noncomputable def kw_surgehgf4_kqe_forwardEquiv :
    PeriodPair.sublatticeQuotient L' (L.scale α) ≃+ ψ.ker :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (kw_surgehgf4_hID_ker_kerIndexHom L L' α ψ hint).symm).trans
    (QuotientAddGroup.liftEquiv _
      (kw_surgehgf4_hID_kerIndexHom_surjective L L' α ψ hint) rfl)

variable {N : ℕ} [NeZero N] (hcard : Nat.card ψ.ker = N)

include hint in
theorem kw_surgehgf4_kqe_alpha_mem (l : L.lattice.toAddSubgroup) :
    (α : ℂ) * (l : ℂ) ∈ L'.lattice.toAddSubgroup := by
  have hmem : (α : ℂ) * (l : ℂ) ∈ (L.scale α).lattice := by
    rw [PeriodPair.mem_scale_lattice_iff L α]; exact ⟨l, l.2, rfl⟩
  exact kw_surgehgf4_hID_scale_subset L L' α ψ hint hmem

include hint in
/-- Pin `kw_surgehgf4_kqe_Psi`: `L.lattice → ZMod N × ZMod N`, `l ↦ α l` mod `N`. -/
noncomputable def kw_surgehgf4_kqe_Psi :
    L.lattice.toAddSubgroup →+ ZMod N × ZMod N where
  toFun l := kw_surgehgf4_kqe_toZModSq L' (N := N)
    ⟨(α : ℂ) * (l : ℂ), kw_surgehgf4_kqe_alpha_mem L L' α ψ hint l⟩
  map_zero' := by
    show kw_surgehgf4_kqe_toZModSq L' ⟨(α : ℂ) * 0, _⟩ = 0
    conv_lhs => rw [show ((⟨(α : ℂ) * 0, _⟩ : L'.lattice.toAddSubgroup) : L'.lattice.toAddSubgroup)
      = 0 from Subtype.ext (by simp)]
    exact _root_.map_zero _
  map_add' l₁ l₂ := by
    show kw_surgehgf4_kqe_toZModSq L' ⟨(α : ℂ) * _, _⟩
      = kw_surgehgf4_kqe_toZModSq L' ⟨_, _⟩ + kw_surgehgf4_kqe_toZModSq L' ⟨_, _⟩
    rw [← map_add (kw_surgehgf4_kqe_toZModSq L')]
    congr 1
    apply Subtype.ext
    push_cast; ring

include hint hcard in
theorem kw_surgehgf4_kqe_ker_Psi :
    (kw_surgehgf4_kqe_Psi L L' α ψ hint (N := N)).ker
      = (L'.scale (kw_surgehgf4_hID_dualUnit α ψ
          (hcard ▸ NeZero.pos N))).lattice.toAddSubgroup.addSubgroupOf
          L.lattice.toAddSubgroup := by
  ext l
  rw [AddMonoidHom.mem_ker]
  show kw_surgehgf4_kqe_toZModSq L'
      ⟨(α : ℂ) * (l : ℂ), kw_surgehgf4_kqe_alpha_mem L L' α ψ hint l⟩ = 0 ↔ _
  rw [show (kw_surgehgf4_kqe_toZModSq L' (N := N)
          ⟨(α : ℂ) * (l : ℂ), kw_surgehgf4_kqe_alpha_mem L L' α ψ hint l⟩ = 0)
        ↔ (⟨(α : ℂ) * (l : ℂ), kw_surgehgf4_kqe_alpha_mem L L' α ψ hint l⟩
            : L'.lattice.toAddSubgroup)
          ∈ (kw_surgehgf4_kqe_toZModSq L' (N := N)).ker from Iff.rfl,
    kw_surgehgf4_kqe_ker_toZModSq, AddSubgroup.mem_addSubgroupOf,
    AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup,
    Submodule.mem_toAddSubgroup,
    PeriodPair.mem_scale_lattice_iff L' (Units.mk0 (N : ℂ) (by exact_mod_cast NeZero.ne N)),
    PeriodPair.mem_scale_lattice_iff L'
      (kw_surgehgf4_hID_dualUnit α ψ (hcard ▸ NeZero.pos N))]
  constructor
  · rintro ⟨v, hv, hav⟩
    refine ⟨v, hv, ?_⟩
    have hav' : (α : ℂ) * (l : ℂ) = (N : ℂ) * v := by
      have := hav; simpa [Units.val_mk0] using this
    rw [kw_surgehgf4_hID_dualUnit_val, hcard,
      show (l : ℂ) = (α : ℂ)⁻¹ * ((α : ℂ) * (l : ℂ)) from
        (inv_mul_cancel_left₀ α.ne_zero _).symm,
      hav']
    ring
  · rintro ⟨v, hv, hlv⟩
    refine ⟨v, hv, ?_⟩
    show (α : ℂ) * (l : ℂ) = _
    rw [hlv, kw_surgehgf4_hID_dualUnit_val, hcard, Units.val_mk0]
    field_simp

include hint hcard in
theorem kw_surgehgf4_kqe_Nu_le_alpha :
    (L'.scale (Units.mk0 (N : ℂ)
        (by exact_mod_cast NeZero.ne N))).lattice.toAddSubgroup.addSubgroupOf
        L'.lattice.toAddSubgroup
      ≤ (L.scale α).lattice.toAddSubgroup.addSubgroupOf L'.lattice.toAddSubgroup := by
  intro l' hl'
  rw [AddSubgroup.mem_addSubgroupOf, Submodule.mem_toAddSubgroup] at hl' ⊢
  rw [PeriodPair.mem_scale_lattice_iff L' (Units.mk0 (N : ℂ) (by exact_mod_cast NeZero.ne N))] at hl'
  obtain ⟨v, hv, hlv⟩ := hl'
  rw [show (l' : ℂ) = _ from hlv, Units.val_mk0]
  exact hcard ▸ kw_surgehgf4_hID_card_smul_subset L L' α ψ hint v hv

include hint hcard in
/-- Pin `kw_surgehgf4_kqe_Phi'`. -/
noncomputable def kw_surgehgf4_kqe_Phi' :
    ZMod N × ZMod N →+ PeriodPair.sublatticeQuotient L' (L.scale α) :=
  (QuotientAddGroup.map _ _ (AddMonoidHom.id _)
    (by simpa using kw_surgehgf4_kqe_Nu_le_alpha L L' α ψ hint hcard)).comp
    (kw_surgehgf4_kqe_zmodSqEquiv L' (N := N)).symm.toAddMonoidHom

include hint hcard in
theorem kw_surgehgf4_kqe_Phi'_surjective :
    Function.Surjective (kw_surgehgf4_kqe_Phi' L L' α ψ hint hcard) := by
  intro x
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective x
  refine ⟨(kw_surgehgf4_kqe_zmodSqEquiv L' (N := N)) (QuotientAddGroup.mk y), ?_⟩
  unfold kw_surgehgf4_kqe_Phi'
  rw [AddMonoidHom.comp_apply]
  simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.symm_apply_apply]
  rfl

include hint hcard in
theorem kw_surgehgf4_kqe_Phi'_comp_Psi :
    ∀ l, kw_surgehgf4_kqe_Phi' L L' α ψ hint hcard
      (kw_surgehgf4_kqe_Psi L L' α ψ hint (N := N) l) = 0 := by
  intro l
  unfold kw_surgehgf4_kqe_Phi'
  rw [AddMonoidHom.comp_apply]
  have hsymm : (kw_surgehgf4_kqe_zmodSqEquiv L' (N := N)).symm.toAddMonoidHom
        (kw_surgehgf4_kqe_Psi L L' α ψ hint (N := N) l)
      = QuotientAddGroup.mk
          ⟨(α : ℂ) * (l : ℂ), kw_surgehgf4_kqe_alpha_mem L L' α ψ hint l⟩ := by
    apply (kw_surgehgf4_kqe_zmodSqEquiv L' (N := N)).injective
    simp only [AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply]
    rfl
  rw [hsymm]
  show QuotientAddGroup.mk _ = 0
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    Submodule.mem_toAddSubgroup, PeriodPair.mem_scale_lattice_iff L α]
  exact ⟨l, l.2, rfl⟩

end Equivs

/-- Pin `kw_surgehgf4_kqe_proved`: the kernel-quotient engine. -/
theorem kw_surgehgf4_kqe_proved : KwD5BetweenCurvesKerQuotEquivBC := by
  intro L L' _ _ _ _ _ _ _ _ ι'' hι'' hfin'' N _ ψ hcard hH2 _hID hcyc
  have hNe : Nat.card ψ.ker ≠ 0 := hcard ▸ NeZero.ne N
  obtain ⟨F, hFdiff, hF0, hFint⟩ := hH2 L L' ι'' hι'' hfin''
  have hper : ∀ l ∈ L.lattice, ∀ z, F (z + l) - F z ∈ L'.lattice := by
    intro l hl z
    have h1 : L'.toPointHom (F (z + l) - F z) = 0 := by
      rw [map_sub, hFint, hFint, L.toPointHom_apply, L.toPointHom_apply,
        PeriodPair.toPoint_add_mem L L.discriminantNeZero z hl, sub_self]
    rwa [← AddMonoidHom.mem_ker, L'.ker_toPointHom, Submodule.mem_toAddSubgroup] at h1
  obtain ⟨α, hαΛ, hFα⟩ :=
    PeriodPair.exists_smul_mem_and_apply_eq_of_forall_sub_mem L L' hFdiff hper
  have hint : ∀ z, L'.toPointHom (α * z) = ψ (L.toPointHom z) := by
    intro z
    have hF0' : L'.toPointHom (F 0) = 0 := by
      rw [← AddMonoidHom.mem_ker, L'.ker_toPointHom, Submodule.mem_toAddSubgroup]
      exact hF0
    calc L'.toPointHom (α * z)
        = L'.toPointHom (F z - F 0) := by rw [hFα z]; ring_nf
      _ = L'.toPointHom (F z) - L'.toPointHom (F 0) := map_sub _ _ _
      _ = L'.toPointHom (F z) := by rw [hF0', sub_zero]
      _ = ψ (L.toPointHom z) := hFint z
  have hα0 : α ≠ 0 := by
    intro h0
    have hψ0 : ∀ P, ψ P = 0 := by
      intro P
      obtain ⟨z, hz⟩ := (L.isUniformization_toPoint L.discriminantNeZero).2.1 P
      have := hint z
      rw [h0, zero_mul, _root_.map_zero, L.toPointHom_apply, hz] at this
      exact this.symm
    have hker : ψ.ker = ⊤ := top_unique fun P _ => hψ0 P
    have hcard0 : Nat.card (ψ.ker : Type _) = 0 := by
      rw [hker, Nat.card_eq_zero]
      exact Or.inr ((AddSubgroup.topEquiv).symm.toEquiv.infinite_iff.mp
        (PeriodPair.infinite_point L))
    exact hNe hcard0
  let αu : ℂˣ := Units.mk0 α hα0
  have hαu : (αu : ℂ) = α := rfl
  have hintU : ∀ z, L'.toPointHom ((αu : ℂ) * z) = ψ (L.toPointHom z) := hαu ▸ hint
  have hN : 0 < Nat.card ψ.ker := Nat.pos_of_ne_zero hNe
  set β := kw_surgehgf4_hID_dualUnit αu ψ hN with hβdef
  refine ⟨β, kw_surgehgf4_hID_dual_subset L L' αu ψ hintU hN,
    kw_surgehgf4_hID_dualIndex_eq L L' αu ψ hintU hN, ?_⟩
  have hfwd := kw_surgehgf4_kqe_forwardEquiv L L' αu ψ hintU
  have hcycLαL : IsAddCyclic (PeriodPair.sublatticeQuotient L' (L.scale αu)) :=
    isAddCyclic_of_surjective hfwd.symm.toAddMonoidHom hfwd.symm.surjective
  have hcardLαL : Nat.card (PeriodPair.sublatticeQuotient L' (L.scale αu)) = N := by
    rw [Nat.card_congr hfwd.toEquiv, hcard]
  set Φ' := kw_surgehgf4_kqe_Phi' L L' αu ψ hintU hcard with hΦdef
  have hcycΦker : IsAddCyclic Φ'.ker :=
    kw_surgehgf4_kqe_isAddCyclic_ker_of_surjective' Φ'
      (kw_surgehgf4_kqe_Phi'_surjective L L' αu ψ hintU hcard)
      hcardLαL hcycLαL
  set Ψ := kw_surgehgf4_kqe_Psi L L' αu ψ hintU (N := N) with hΨdef
  have hrangeSub : Ψ.range ≤ Φ'.ker := by
    rintro _ ⟨l, rfl⟩
    rw [AddMonoidHom.mem_ker]
    exact kw_surgehgf4_kqe_Phi'_comp_Psi L L' αu ψ hintU hcard l
  have hLβEquiv : PeriodPair.sublatticeQuotient L (L'.scale β) ≃+ Ψ.range :=
    (QuotientAddGroup.quotientAddEquivOfEq
      (kw_surgehgf4_kqe_ker_Psi L L' αu ψ hintU hcard).symm).trans
      (QuotientAddGroup.quotientKerEquivRange Ψ)
  have hcardLβ : Nat.card (PeriodPair.sublatticeQuotient L (L'.scale β)) = N := by
    have hdual := kw_surgehgf4_hID_dualIndex_eq L L' αu ψ hintU hN
    show ((L'.scale β).lattice.toAddSubgroup.addSubgroupOf L.lattice.toAddSubgroup).index = N
    rw [hβdef]
    exact hdual.trans hcard
  have hcardΦker : Nat.card Φ'.ker = N := by
    have hG : Nat.card (ZMod N × ZMod N) = N ^ 2 := by simp [sq]
    have htot := (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Φ'.ker).symm
    rw [hG, Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective _
        (kw_surgehgf4_kqe_Phi'_surjective L L' αu ψ hintU hcard)).toEquiv,
      hcardLαL, sq] at htot
    exact Nat.eq_of_mul_eq_mul_left (NeZero.pos N) htot
  have hcardRange : Nat.card Ψ.range = N := by
    rw [← Nat.card_congr hLβEquiv.toEquiv, hcardLβ]
  have hrangeEq : Ψ.range = Φ'.ker := by
    refine AddSubgroup.eq_of_le_of_card_ge hrangeSub ?_
    rw [hcardRange, hcardΦker]
  rw [← hrangeEq] at hcycΦker
  exact isAddCyclic_of_surjective hLβEquiv.symm.toAddMonoidHom hLβEquiv.symm.surjective

end ModularCurve

/-! ## The two headlines -/

namespace PeriodPair

/-- Pin `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker` (the
978 node): the arithmetic converse of S-1. -/
theorem exists_scale_lattice_subset_and_sublatticeIndex_eq_natCard_ker
    (L L' : PeriodPair) (hL : L.DiscriminantNeZero) (hL' : L'.DiscriminantNeZero) (α : ℂˣ)
    (ψ : L.weierstrassCurve.toAffine.Point →+ L'.weierstrassCurve.toAffine.Point)
    (hψ : ∀ z : ℂ, L'.toPoint hL' ((α : ℂ) * z) = ψ (L.toPoint hL z)) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = Nat.card ψ.ker := by
  haveI : L.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr L.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  haveI : L'.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr L'.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  refine ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved L L' α ψ ?_
  intro z
  rw [PeriodPair.toPointHom_apply, PeriodPair.toPointHom_apply]
  exact hψ z

/-- Pin `PeriodPair.exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient`
(the 2,021 node): the same inclusion with the index pinned to `N` and the quotient cyclic. -/
theorem exists_scale_lattice_subset_and_sublatticeIndex_eq_and_isAddCyclic_sublatticeQuotient
    (L L' : PeriodPair) [L.weierstrassCurve.IsElliptic] [L'.weierstrassCurve.IsElliptic]
    [GenusOnePlaceGate L.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L.weierstrassCurve.toAffine]
    [AbelTheorem L.weierstrassCurve.toAffine]
    [GenusOnePlaceGate L'.weierstrassCurve.toAffine] [GenusOnePlaceGate.IsCentred L'.weierstrassCurve.toAffine]
    [AbelTheorem L'.weierstrassCurve.toAffine]
    (ι : L'.weierstrassCurve.toAffine.FunctionField →ₐ[ℂ] L.weierstrassCurve.toAffine.FunctionField)
    (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong ℂ ι) (hN : NormFormulaAlong ℂ ι hfin)
    (N : ℕ) [NeZero N]
    (hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker)
    (hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = N) :
    ∃ β : ℂˣ, ((L'.scale β).lattice : Set ℂ) ⊆ L.lattice ∧
      PeriodPair.sublatticeIndex L (L'.scale β) = N ∧
      IsAddCyclic (PeriodPair.sublatticeQuotient L (L'.scale β)) := by
  have hH2 : ModularCurve.KwD5BetweenCurvesHoloLift :=
    ModularCurve.kw_surgehgf4_hH2f_betweenCurvesHoloLift
  have hID : ModularCurve.KwD5BetweenCurvesIndexDual :=
    ModularCurve.kw_surgehgf4_hID_betweenCurvesIndexDual_proved
  exact ModularCurve.kw_surgehgf4_hscd_pointHomSublatticeCyc_of_three hH2 hID
    ModularCurve.kw_surgehgf4_kqe_proved L L' ι hι hfin N hcyc hcard

end PeriodPair

end
