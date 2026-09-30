/-
  Existence of an arithmetic Frobenius at a place of `ℚ̄`: for a valuation ring
  `A` lying over the prime `q`, `ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime`
  produces `φ` in the decomposition group acting on the residue field by
  `x ↦ x ^ q`; `ValuationSubring.exists_isFrobeniusAt_rat` is the corollary that
  such a place over any prime `ℓ` exists.

  Ported from
  `P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime.lean` and
  `P2M/Sol/S_ValuationSubring_exists_isFrobeniusAt_rat.lean` (pinned `aa2d8b3`,
  314 + 30 lines). The pin's `PlaceTransitivity` helper block is transcribed
  `private` (playbook §7.1), with two changes: the integral-membership step
  `PlaceTransitivity.coe_mem` (pin lines 17–28) is the public
  `ValuationSubring.mem_of_isIntegral` of `NumberTheory/ValuationAtPlace.lean`
  written once, and the one-line `inferInstance` restatements `isGalois_Qbar` /
  `isAlgebraic_Qbar` (pin lines 91–97) are inlined as `haveI`. The mathematics is
  math/018 §1.4.
-/
import Mathlib.Algebra.Algebra.Rat
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import FLTForHuman.GaloisRep.Defs.Ramification
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.NumberTheory.ValuationAtPlace

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals; they are
-- transcribed verbatim, as in the other ported proof files.
set_option linter.style.haveILetI false

open scoped NumberField Pointwise

local notation "ℚ̄" => AlgebraicClosure ℚ

private noncomputable abbrev Zbar : Subalgebra ℤ ℚ̄ := integralClosure ℤ ℚ̄

local notation "ℤ̄" => Zbar

/-- `ℤ̄ →+* A` is the restriction of the inclusion of the integral closure. -/
private noncomputable def toPlace (A : ValuationSubring ℚ̄) : ℤ̄ →+* A :=
  ((Subalgebra.val ℤ̄).toRingHom).codRestrict A.toSubring
    (fun b => ValuationSubring.mem_of_isIntegral A (b : ℚ̄) b.2)

@[simp] private theorem coe_toPlace (A : ValuationSubring ℚ̄) (b : ℤ̄) :
    (toPlace A b : ℚ̄) = b := rfl

/-- The prime of `ℤ̄` cut out by the maximal ideal of `A`. -/
private noncomputable def center (A : ValuationSubring ℚ̄) : Ideal ℤ̄ :=
  Ideal.comap (toPlace A) (IsLocalRing.maximalIdeal A)

private theorem mem_center_iff {A : ValuationSubring ℚ̄} {b : ℤ̄} :
    b ∈ center A ↔ (b : ℚ̄) ∈ A.nonunits := by
  rw [center, Ideal.mem_comap, ← ValuationSubring.coe_mem_nonunits_iff, coe_toPlace]

private instance center_isPrime (A : ValuationSubring ℚ̄) : (center A).IsPrime :=
  Ideal.comap_isPrime _ _

private theorem center_under {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) :
    (center A).under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
  refine (hmax.eq_of_le ?_ ?_).symm
  · exact Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top inferInstance)
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ ℤ̄ (q : ℤ) ∈ center A
    rw [mem_center_iff]
    have : ((algebraMap ℤ ℤ̄ (q : ℤ) : ℤ̄) : ℚ̄) = (q : ℚ̄) := by
      rw [map_natCast]; rfl
    rw [this]
    exact hA

private theorem mem_smul_nonunits_iff {K L : Type*} [Field K] [Field L] [Algebra K L]
    {τ : L ≃ₐ[K] L} {A : ValuationSubring L} {x : L} :
    x ∈ (τ • A).nonunits ↔ τ.symm x ∈ A.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  have e0 : x = 0 ↔ τ.symm x = 0 := by
    constructor
    · intro h; rw [h, _root_.map_zero]
    · intro h; simpa using congrArg τ h
  have e1 : x⁻¹ ∈ τ • A ↔ (τ.symm x)⁻¹ ∈ A := by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    have : (τ⁻¹ : L ≃ₐ[K] L) • x⁻¹ = (τ.symm x)⁻¹ := by
      show τ.symm x⁻¹ = (τ.symm x)⁻¹
      exact map_inv₀ _ _
    rw [this]
  rw [e0, e1]

private theorem le_of_forall_not_mem_nonunits {q : ℕ} (hq : q.Prime)
    {V W : ValuationSubring ℚ̄} (hV : V.LiesOverPrime q)
    (h : ∀ s : ℤ̄, (s : ℚ̄) ∉ V.nonunits → (s : ℚ̄) ∉ W.nonunits) : V ≤ W := by
  intro x hx
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime V hq hV x hx
  have hsW : (s : ℚ̄) ∉ W.nonunits := h s hs
  rw [ValuationSubring.mem_nonunits_iff_or, not_or, not_not] at hsW
  obtain ⟨hs0, hsinv⟩ := hsW
  have hx_eq : x = (x' : ℚ̄) * (s : ℚ̄)⁻¹ := by
    rw [← hxs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [hx_eq]
  exact W.mul_mem _ _ (ValuationSubring.mem_of_isIntegral W (x' : ℚ̄) x'.2) hsinv

private theorem exists_smul_center_eq {q : ℕ} (hq : q.Prime) {A A₀ : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) (hA₀ : A₀.LiesOverPrime q) :
    ∃ g : ℚ̄ ≃ₐ[ℚ] ℚ̄, center A₀ = g • center A := by
  classical
  haveI : IsGalois ℚ ℚ̄ := inferInstance
  haveI : Algebra.IsAlgebraic ℚ ℚ̄ := inferInstance
  haveI : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace ℤ̄ := ⊥
  haveI : DiscreteTopology ℤ̄ := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) ℤ̄ := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : ℚ̄))
  haveI : Algebra.IsInvariant ℤ ℤ̄ (ℚ̄ ≃ₐ[ℚ] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap ℚ ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : ℤ̄ => (z : ℚ̄)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℚ̄)
        (algebraMap ℚ ℚ̄).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ ℤ̄ n : ℤ̄) : ℚ̄) = b
    rw [← hr, ← hn]
    simp⟩
  have hu : (center A).under ℤ = (center A₀).under ℤ := by
    rw [center_under hq hA, center_under hq hA₀]
  exact Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
    (A := ℤ) (G := ℚ̄ ≃ₐ[ℚ] ℚ̄) (center A) (center A₀) hu

private theorem smul_eq_of_smul_center_eq {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    (hA : A.LiesOverPrime q) {g : ℚ̄ ≃ₐ[ℚ] ℚ̄} (hg : g • center A = center A) :
    g • A = A := by
  classical
  have key : ∀ s : Zbar, (s : ℚ̄) ∈ (g • A).nonunits ↔ (s : ℚ̄) ∈ A.nonunits := by
    intro s
    rw [mem_smul_nonunits_iff, ← mem_center_iff (A := A), ← hg,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem_center_iff]
    have : ((g⁻¹ • s : Zbar) : ℚ̄) = g.symm s := by
      rw [integralClosure.coe_smul, AlgEquiv.smul_def, AlgEquiv.aut_inv]
    rw [this]
  have hgA : (g • A).LiesOverPrime q := by
    show (q : ℚ̄) ∈ (g • A).nonunits
    rw [mem_smul_nonunits_iff, map_natCast]
    exact hA
  apply le_antisymm
  · exact le_of_forall_not_mem_nonunits hq hgA fun s hs => fun h => hs ((key s).mpr h)
  · exact le_of_forall_not_mem_nonunits hq hA fun s hs => fun h => hs ((key s).mp h)

private theorem exists_frobenius_algEquiv {q : ℕ} (hq : q.Prime) {A : ValuationSubring ℚ̄}
    [(center A).LiesOver (Ideal.span {(q : ℤ)})] :
    ∃ f : (Zbar ⧸ center A) ≃ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A),
      ∀ b : Zbar, f (Ideal.Quotient.mk (center A) b) = (Ideal.Quotient.mk (center A) b) ^ q := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩

  have hqmem : ((q : ℤ) : Zbar) ∈ center A := by
    have := (Ideal.mem_of_liesOver (center A) (Ideal.span {(q : ℤ)}) (q : ℤ)).mp
      (Ideal.mem_span_singleton_self _)
    simpa using this
  haveI : CharP (Zbar ⧸ center A) q := by
    rw [CharP.charP_iff_prime_eq_zero hq]
    have : ((q : ℕ) : Zbar ⧸ center A) = Ideal.Quotient.mk (center A) ((q : ℤ) : Zbar) := by
      simp
    rw [this]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hqmem
  let fr : (Zbar ⧸ center A) →+* (Zbar ⧸ center A) := frobenius (Zbar ⧸ center A) q
  have fr_apply : ∀ y, fr y = y ^ q := fun y => rfl

  let fa : (Zbar ⧸ center A) →ₐ[ℤ ⧸ Ideal.span {(q : ℤ)}] (Zbar ⧸ center A) :=
    { fr with
      commutes' := fun r => by
        obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective r
        rw [Ideal.Quotient.algebraMap_mk_of_liesOver]
        show fr (Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)) =
          Ideal.Quotient.mk (center A) (algebraMap ℤ Zbar n)
        rw [eq_intCast, map_intCast, map_intCast] }
  have fa_apply : ∀ y, fa y = y ^ q := fun y => rfl

  have hinj : Function.Injective fa := by
    intro y₁ y₂ h
    rw [fa_apply, fa_apply] at h
    exact frobenius_inj (Zbar ⧸ center A) q h
  have hsurj : Function.Surjective fa := by
    intro y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (b : ℚ̄) hq.pos
    have hcint : IsIntegral ℤ c := by
      refine IsIntegral.of_pow hq.pos ?_
      rw [hc]; exact b.2
    refine ⟨Ideal.Quotient.mk (center A) ⟨c, hcint⟩, ?_⟩
    rw [fa_apply, ← map_pow]
    congr 1
    exact Subtype.ext hc
  exact ⟨AlgEquiv.ofBijective fa ⟨hinj, hsurj⟩, fun b => rfl⟩

theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime {q : ℕ} (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    ∃ φ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ), A.IsFrobeniusAt φ q := by
  classical

  haveI : IsGalois ℚ ℚ̄ := inferInstance
  haveI : Algebra.IsAlgebraic ℚ ℚ̄ := inferInstance
  haveI : Algebra.IsIntegral ℚ ℚ̄ := Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  letI : TopologicalSpace Zbar := ⊥
  haveI : DiscreteTopology Zbar := ⟨rfl⟩
  haveI : ContinuousSMul (ℚ̄ ≃ₐ[ℚ] ℚ̄) Zbar := by
    refine continuousSMul_iff_stabilizer_isOpen.mpr fun b => ?_
    haveI : FiniteDimensional ℚ (IntermediateField.adjoin ℚ {(b : ℚ̄)}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral (b : ℚ̄))
    refine Subgroup.isOpen_mono ?_
      (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin ℚ {(b : ℚ̄)}))
    intro g hg
    rw [MulAction.mem_stabilizer_iff]
    apply Subtype.ext
    change g • (b : ℚ̄) = b
    rw [IntermediateField.mem_fixingSubgroup_iff] at hg
    exact hg _ (IntermediateField.mem_adjoin_simple_self ℚ (b : ℚ̄))
  haveI : Algebra.IsInvariant ℤ Zbar (ℚ̄ ≃ₐ[ℚ] ℚ̄) := ⟨fun b hb => by
    have hb' : (b : ℚ̄) ∈ Set.range (algebraMap ℚ ℚ̄) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro g
      exact congrArg (fun z : Zbar => (z : ℚ̄)) (hb g)
    obtain ⟨r, hr⟩ := hb'
    have hrint : IsIntegral ℤ r := by
      have h := b.2
      rw [mem_integralClosure_iff, ← hr] at h
      exact (isIntegral_algHom_iff (IsScalarTower.toAlgHom ℤ ℚ ℚ̄)
        (algebraMap ℚ ℚ̄).injective).mp h
    obtain ⟨n, hn⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
    refine ⟨n, Subtype.ext ?_⟩
    show ((algebraMap ℤ Zbar n : Zbar) : ℚ̄) = b
    rw [← hr, ← hn]
    simp⟩

  haveI hover : (center A).LiesOver (Ideal.span {(q : ℤ)}) := ⟨(center_under hq hA).symm⟩
  obtain ⟨f, hf⟩ := exists_frobenius_algEquiv (A := A) hq
  obtain ⟨g, hg⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite
    (G := ℚ̄ ≃ₐ[ℚ] ℚ̄) (Ideal.span {(q : ℤ)}) (center A) f

  have hgQ : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • center A = center A := g.2
  have hgA : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • A = A := smul_eq_of_smul_center_eq hq hA hgQ
  have hgD : (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) ∈ A.decompositionSubgroup ℚ := MulAction.mem_stabilizer_iff.mpr hgA
  refine ⟨g, hgD, ?_⟩

  let ψ : Zbar →+* IsLocalRing.ResidueField A := (IsLocalRing.residue A).comp (toPlace A)
  have hψ : ∀ b : Zbar, ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • b) = ψ b ^ q := by
    intro b
    have h1 : Ideal.Quotient.mk (center A) (g • b) = (Ideal.Quotient.mk (center A) b) ^ q := by
      rw [← hf b, ← hg, Ideal.Quotient.stabilizerHom_apply]
    rw [← map_pow, Ideal.Quotient.eq] at h1
    have h1' : toPlace A (g • b) - toPlace A (b ^ q) ∈ IsLocalRing.maximalIdeal A := by
      have := h1
      unfold center at this
      rw [Ideal.mem_comap, map_sub] at this
      exact this
    have h2 := (Ideal.Quotient.eq (I := IsLocalRing.maximalIdeal A)).mpr h1'
    show IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • b)) =
      (IsLocalRing.residue A (toPlace A b)) ^ q
    rw [← map_pow, ← map_pow]
    exact h2

  intro x
  obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective x
  obtain ⟨x', s, hs, hxs⟩ :=
    ValuationSubring.exists_integral_mul_eq_of_liesOverPrime A hq hA a a.2
  set d : A.decompositionSubgroup ℚ := ⟨g, hgD⟩
  have hψs : ψ s ≠ 0 := by
    intro h0
    apply hs
    have : toPlace A s ∈ IsLocalRing.maximalIdeal A :=
      (IsLocalRing.residue_eq_zero_iff _).mp h0
    rw [← ValuationSubring.coe_mem_nonunits_iff] at this
    exact this

  have e1 : a * toPlace A s = toPlace A x' := Subtype.ext hxs
  have e2 : (d • a) * toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s) = toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x') := by
    apply Subtype.ext
    show (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (a : ℚ̄) * (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (s : ℚ̄) = (g : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x' : ℚ̄)
    rw [← map_mul, hxs]
  have e1' : IsLocalRing.residue A a * ψ s = ψ x' := by
    show IsLocalRing.residue A a * IsLocalRing.residue A (toPlace A s) =
      IsLocalRing.residue A (toPlace A x')
    rw [← map_mul, e1]
  have e2' : IsLocalRing.residue A (d • a) * ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s) =
      ψ ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x') := by
    show IsLocalRing.residue A (d • a) * IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • s)) =
      IsLocalRing.residue A (toPlace A ((g : ℚ̄ ≃ₐ[ℚ] ℚ̄) • x'))
    rw [← map_mul, e2]
  rw [hψ s, hψ x', ← e1', mul_pow] at e2'
  have hcancel := mul_right_cancel₀ (pow_ne_zero q hψs) e2'
  show d • IsLocalRing.residue A a = (IsLocalRing.residue A a) ^ q
  have : d • (IsLocalRing.residue A a) = IsLocalRing.residue A (d • a) :=
    (IsLocalRing.ResidueField.residue_smul (A.decompositionSubgroup ℚ) d a).symm
  exact this.trans hcancel

theorem ValuationSubring.exists_isFrobeniusAt_rat (ℓ : ℕ) (hℓ : ℓ.Prime) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ ∧
      ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ ℓ := by
  classical
  let O : Subalgebra ℤ (AlgebraicClosure ℚ) := integralClosure ℤ (AlgebraicClosure ℚ)

  have hℓZ : Prime (ℓ : ℤ) := Int.prime_iff_natAbs_prime.mpr (by simpa using hℓ)
  haveI hPmax : (Ideal.span {(ℓ : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hℓZ.irreducible

  have hker : RingHom.ker (algebraMap ℤ O) ≤ Ideal.span {(ℓ : ℤ)} := by
    rw [(RingHom.injective_iff_ker_eq_bot _).mp (algebraMap ℤ O).injective_int]
    exact bot_le
  obtain ⟨𝔔, h𝔔max, h𝔔⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral (S := O) (Ideal.span {(ℓ : ℤ)}) hker
  have hℓ𝔔 : (ℓ : O) ∈ 𝔔 := by
    have h : (ℓ : ℤ) ∈ Ideal.comap (algebraMap ℤ O) 𝔔 := by
      change (ℓ : ℤ) ∈ Ideal.under ℤ 𝔔
      rw [h𝔔]; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using h

  obtain ⟨A, -, h𝔔A⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (A := O.toSubring) 𝔔 h𝔔max.ne_top
  have hA : A.LiesOverPrime ℓ := by
    have h : ((ℓ : O) : AlgebraicClosure ℚ) ∈ A.nonunits := h𝔔A ⟨(ℓ : O), hℓ𝔔, rfl⟩
    simp at h
    exact h
  obtain ⟨φ, hφ⟩ := ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA
  exact ⟨A, hA, φ, hφ⟩

/-! ### The arithmetic Frobenius from its action on the residue field (S7-I)

`ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem` is the converse of the
construction above: an automorphism `τ` that preserves a maximal ideal `Qt ⊆ 𝓞 ℚ̄`
and acts on it by `x ↦ x ^ ℓ` is a Frobenius at any place `A` that is the
localisation of `𝓞 ℚ̄` at `Qt`.  The pin's private `C6PortS10T3b` prelude is
transcribed `private` here. -/

namespace ValuationSubring

/-- The pin's `IsLoc`: `A` is the localisation of `𝓞 ℚ̄` at the maximal ideal `Qt`. -/
private def IsLoc (Qt : Ideal (𝓞 (AlgebraicClosure ℚ)))
    (A : ValuationSubring (AlgebraicClosure ℚ)) : Prop :=
  ∀ x : AlgebraicClosure ℚ, x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧
    ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a

private theorem coe_ne_zero_of_notMem {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {s : 𝓞 (AlgebraicClosure ℚ)} (hs : s ∉ Qt) : (s : AlgebraicClosure ℚ) ≠ 0 := by
  intro h
  exact hs ((NumberField.RingOfIntegers.coe_eq_zero_iff.mp h).symm ▸ Qt.zero_mem)

private theorem coe_mem {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    (x : 𝓞 (AlgebraicClosure ℚ)) : (x : AlgebraicClosure ℚ) ∈ A :=
  (hA x).2 ⟨1, (Ideal.ne_top_iff_one Qt).1 Ideal.IsPrime.ne_top', x, by simp⟩

private noncomputable def ψ {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A) :
    𝓞 (AlgebraicClosure ℚ) →+* A :=
  (algebraMap (𝓞 (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ)).codRestrict A (coe_mem hA)

@[simp] private theorem coe_ψ {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    (x : 𝓞 (AlgebraicClosure ℚ)) :
    ((ψ hA x : A) : AlgebraicClosure ℚ) = x := rfl

private theorem isUnit_ψ {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    {s : 𝓞 (AlgebraicClosure ℚ)} (hs : s ∉ Qt) : IsUnit (ψ hA s) := by
  have hs0 := coe_ne_zero_of_notMem hs
  have hinv : (s : AlgebraicClosure ℚ)⁻¹ ∈ A := (hA _).2 ⟨s, hs, 1, by simp [hs0]⟩
  exact IsUnit.of_mul_eq_one (b := ⟨_, hinv⟩) (Subtype.ext (mul_inv_cancel₀ hs0))

private theorem ψ_mem_maximalIdeal {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    {z : 𝓞 (AlgebraicClosure ℚ)} (hz : z ∈ Qt) :
    ψ hA z ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff]
  rintro ⟨u, hu⟩
  have hinvA : ((u⁻¹ : Aˣ) : A).1 ∈ A := ((u⁻¹ : Aˣ) : A).2
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 hinvA
  apply hs
  have hzu : (z : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1 = 1 := by
    have := congrArg (fun v : A => (v : AlgebraicClosure ℚ)) u.mul_inv
    simpa [hu] using this
  have hs_eq : (s : AlgebraicClosure ℚ) = z * a := by
    calc (s : AlgebraicClosure ℚ)
        = s * ((z : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1) := by rw [hzu, mul_one]
      _ = z * ((s : AlgebraicClosure ℚ) * ((u⁻¹ : Aˣ) : A).1) := by ring
      _ = z * a := by rw [hsa]
  have : s = z * a := NumberField.RingOfIntegers.coe_injective (by simpa using hs_eq)
  exact this ▸ Qt.mul_mem_right a hz

private theorem liesOverPrime {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : IsLoc Qt A) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) : A.LiesOverPrime ℓ := by
  rw [LiesOverPrime, mem_nonunits_iff_or]
  refine Or.inr fun hinv => ?_
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 hinv
  apply hs
  have hℓ0 : (ℓ : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
  have hs_eq : (s : AlgebraicClosure ℚ) = (ℓ : AlgebraicClosure ℚ) * a := by
    rw [← hsa, mul_left_comm, mul_inv_cancel₀ hℓ0, mul_one]
  have : s = ℓ * a := NumberField.RingOfIntegers.coe_injective (by simpa using hs_eq)
  exact this ▸ Qt.mul_mem_right a hℓQ

private theorem smul_mem {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : IsLoc Qt A)
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hσ : ∀ x : 𝓞 (AlgebraicClosure ℚ), σ • x ∈ Qt ↔ x ∈ Qt) {x : AlgebraicClosure ℚ}
    (hx : x ∈ A) : σ • x ∈ A := by
  obtain ⟨s, hs, a, hsa⟩ := (hA x).1 hx
  refine (hA _).2 ⟨σ • s, fun h => hs ((hσ s).1 h), σ • a, ?_⟩
  have : σ • ((s : AlgebraicClosure ℚ) * x) = σ • (a : AlgebraicClosure ℚ) := by rw [hsa]
  rwa [smul_mul'] at this

private theorem mem_decompositionSubgroup {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : IsLoc Qt A)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt) :
    τ ∈ A.decompositionSubgroup ℚ := by
  have hstab' : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ⁻¹ • x ∈ Qt ↔ x ∈ Qt := fun x => by
    simpa using (hstab (τ⁻¹ • x)).symm
  rw [MulAction.mem_stabilizer_iff]
  ext x
  rw [mem_pointwise_smul_iff_inv_smul_mem]
  exact ⟨fun h => by simpa using smul_mem hA hstab h, fun h => smul_mem hA hstab' h⟩

private theorem smul_ψ {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ A.decompositionSubgroup ℚ)
    (x : 𝓞 (AlgebraicClosure ℚ)) :
    (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • ψ hA x = ψ hA (τ • x) := rfl

private theorem smul_residue {Qt : Ideal (𝓞 (AlgebraicClosure ℚ))}
    {A : ValuationSubring (AlgebraicClosure ℚ)} [Qt.IsMaximal] (hA : IsLoc Qt A)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} {ℓ : ℕ}
    (hτ : τ ∈ A.decompositionSubgroup ℚ)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (y : IsLocalRing.ResidueField A) :
    (⟨τ, hτ⟩ : A.decompositionSubgroup ℚ) • y = y ^ ℓ := by
  set g : A.decompositionSubgroup ℚ := ⟨τ, hτ⟩
  have key : ∀ x : 𝓞 (AlgebraicClosure ℚ),
      g • IsLocalRing.residue A (ψ hA x) = IsLocalRing.residue A (ψ hA x) ^ ℓ := fun x => by
    rw [← IsLocalRing.ResidueField.residue_smul, smul_ψ hA hτ, ← map_pow, ← map_pow, ← sub_eq_zero,
      ← map_sub, IsLocalRing.residue_eq_zero_iff, ← map_sub]
    exact ψ_mem_maximalIdeal hA (hfrob x)
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
  change g • IsLocalRing.residue A r = IsLocalRing.residue A r ^ ℓ
  obtain ⟨s, hs, a, hsa⟩ := (hA _).1 r.2
  have hsr : ψ hA s * r = ψ hA a := Subtype.ext hsa
  have hu : IsLocalRing.residue A (ψ hA s) ≠ 0 := by
    rw [Ne, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, _root_.mem_nonunits_iff,
      not_not]
    exact isUnit_ψ hA hs
  have h1 : IsLocalRing.residue A (ψ hA s) * IsLocalRing.residue A r =
      IsLocalRing.residue A (ψ hA a) := by
    rw [← map_mul, hsr]
  have h2 : g • (IsLocalRing.residue A (ψ hA s) * IsLocalRing.residue A r) =
      IsLocalRing.residue A (ψ hA s) ^ ℓ * g • IsLocalRing.residue A r := by
    rw [smul_mul', key]
  rw [h1, key, ← h1, mul_pow] at h2
  exact (mul_left_cancel₀ (pow_ne_zero ℓ hu) h2).symm

end ValuationSubring

theorem ValuationSubring.isFrobeniusAt_of_forall_smul_sub_pow_mem
    (Qt : Ideal (𝓞 (AlgebraicClosure ℚ))) [Qt.IsMaximal] (ℓ : ℕ) (hℓ : ℓ.Prime)
    (hℓQ : (ℓ : 𝓞 (AlgebraicClosure ℚ)) ∈ Qt) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hstab : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x ∈ Qt ↔ x ∈ Qt)
    (hfrob : ∀ x : 𝓞 (AlgebraicClosure ℚ), τ • x - x ^ ℓ ∈ Qt)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : ∀ x : AlgebraicClosure ℚ,
      x ∈ A ↔ ∃ s : 𝓞 (AlgebraicClosure ℚ), s ∉ Qt ∧ ∃ a : 𝓞 (AlgebraicClosure ℚ), (s : AlgebraicClosure ℚ) * x = a) :
    A.LiesOverPrime ℓ ∧ A.IsFrobeniusAt τ ℓ := by
  have hA' : ValuationSubring.IsLoc Qt A := hA
  have hτ := ValuationSubring.mem_decompositionSubgroup hA' hstab
  exact ⟨ValuationSubring.liesOverPrime hA' hℓ hℓQ, hτ,
    ValuationSubring.smul_residue hA' hτ hfrob⟩

/-- Existence of a place of `ℚ̄` over a rational prime `p`. -/
theorem ValuationSubring.exists_liesOverPrime_algebraicClosure_rat (p : Nat.Primes) :
    ∃ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) := by
  obtain ⟨A, hA, -⟩ := ValuationSubring.exists_isFrobeniusAt_rat (p : ℕ) p.2
  exact ⟨A, hA⟩

/-- Every place of `ℚ̄` over a rational prime `p` carries an arithmetic Frobenius. -/
theorem ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat
    {p : ℕ} (hp : p.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)}
    (hA : A.LiesOverPrime p) :
    ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt σ p :=
  ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hp A hA

/-- A place of `ℚ̄` over `p` and an arithmetic Frobenius at it, simultaneously. -/
theorem ValuationSubring.exists_liesOverPrime_isFrobeniusAt_ratAlgClosure
    (p : Nat.Primes) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      A.LiesOverPrime (p : ℕ) ∧ A.IsFrobeniusAt σ (p : ℕ) := by
  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat p
  obtain ⟨σ, hσ⟩ :=
    ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime_algebraicClosure_rat p.2 hA
  exact ⟨A, σ, hA, hσ⟩
