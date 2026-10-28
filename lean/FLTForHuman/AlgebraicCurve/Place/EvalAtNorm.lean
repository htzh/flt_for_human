/-
The value of a norm on a fibre, and the descent of Riemann–Roch coefficients.

Two companion statements of the place dictionary.  The first is the
valuation-theoretic form of `ord (norm f) = ∑ inertiaDeg · ord f`: at a rational
place `v` of `F`, with every place of the fibre of `v` in `F'` rational and `f` a
unit at all of them, the value of the norm of `f` is the product of the values of
`f`, each raised to the ramification index of its place.  The second says that the
`K'`-coefficients of a Riemann–Roch element are themselves `K`-Riemann–Roch: if a
`K`-linearly independent family of `K'` multiplies a finitely supported family of
`F` into the `L`-space of the pushed-forward divisor, then every coefficient lies
in the `L`-space of the original divisor.

**The norm computation.**  Write `f = c` in the integral closure `A` of `v`'s
valuation subring in `F'`; integrality on the fibre is
`Place.exists_integralClosureAt_of_ord_fiber_nonneg`.  The two sides are compared in
the residue field of `v`, where `algebraMap_residueField_injective` makes it enough
to match the residues.  On the left, `residue (norm c)` is the norm of the image of
`c` in `A ⧸ conductorIdeal` (`residue_norm_eq_norm_mk`), a finite ring over the
residue field of `v`.  The conductor factors as the product of the fibre-centre
powers (`conductorIdeal_eq_prod_fiber`), the fibre ideals are pairwise coprime
(`isCoprime_fiberIdeal`), and multiplicativity of the norm over a coprime product
(`norm_mk_prod_fiberIdeal`) turns it into a product over the fibre.  At a rational
place of the fibre the centre power has residue ring of `K`-dimension the
ramification index (`finrank_fiberCenterPow`) and the image of `c` differs from a
constant by a nilpotent (`isNilpotent_mk_sub_algebraMap`), so its norm is that
constant to the ramification index (`norm_mk_fiberCenterPow`); the constant is
`w.evalAt` of `c` by `sub_algebraMap_evalAt_mem_fiberCenter`.  Composing the
residues gives `residue_norm_eq_prod_evalAt`, and `algebraMap_evalAt_coe` promotes
the `K`-residue computation to `v.evalAt`.

**The `L`-space descent** is the pin's two lines: the hypothesis is the pushed
divisor's order inequality at the lifted place, and
`Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension`
bounds it below by `v.ord (g j)` for each `j`.

Statements from the `Theorems/` wrappers, proofs after the `P2M/Sol/S_` files of the
pinned FLT (`anthropics/fermats-last-theorem`, `aa2d8b3`).  The pin's `S_` files carry
a private engine (`conductorIdeal`, the fibre ideals and their norms); it stays
private here, exactly as the pin keeps it below its headline.

The third statement, `Divisor.evalFun_algebraMap_pushforward`, is a separate bookkeeping
identity of the same dictionary: the `evalFun` of a base-changed function on a divisor of
the extension is the `evalFun` of the function on the pushed-forward divisor, one fibre at
a time.  Its only helper is the exponent bookkeeping `zpow_finset_sum'`.

spec-pin: Theorems/Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain.lean   -- comparable copy
spec-pin: Theorems/Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward.lean
spec-pin: P2M/Sol/S_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward.lean   -- comparable copy
-/
import FLTForHuman.AlgebraicCurve.Defs.PushPull
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension
import FLTForHuman.AlgebraicCurve.Place.IntegralClosureAtFiber
import FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtensionRamification
import FLTForHuman.RingTheory.Norm.Elementary

set_option autoImplicit false

-- The pin's `haveI` instance walls are transcribed literally (as in
-- `Differential/ConstantFieldExtension.lean`).
set_option linter.style.haveILetI false

noncomputable section

open AlgebraicCurve

open IsDedekindDomain WithZero IsLocalRing UniqueFactorizationMonoid

-- The pin's instance wall for the valuation-subring algebra (as in `P1/UnitFinite.lean`).
attribute [local instance 0] Place.valuationSubringAlgebra

namespace AlgebraicCurve

/-! ## The `K'`-coefficients of a Riemann–Roch element descend -/

/-- **The `K'`-coefficients of a Riemann–Roch element descend.** Statement from
`Theorems/Thm_AlgebraicCurve_mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain.lean`;
proof after the pin's `S_` file: the hypothesis is the order inequality at the
lifted place, and the non-cancellation node turns it into the inequality at `v`. -/
theorem mem_riemannRochSpace_of_sum_basis_smul_algebraMap_mem_mapDomain
    (K F K' F' : Type*)
    [Field K] [Field F] [Field K'] [Field F'] [Algebra K F] [Algebra K' F']
    [Algebra K K'] [Algebra F F'] [Algebra K F'] [IsScalarTower K K' F'] [IsScalarTower K F F']
    [IsAlgClosed K] [IsAlgClosed K'] [IsCurveOver K F] [IsCurveOver K' F']
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K' x ∧
      FiniteDimensional (IntermediateField.adjoin K' ({x} : Set F')) F')
    (hgen : IntermediateField.adjoin K' (Set.range (algebraMap F F')) = ⊤)
    (lift : Place K F → Place K' F')
    (hlift_ord : ∀ (P : Place K F) (f : F), (lift P).ord (algebraMap F F' f) = P.ord f)
    (hlift_inj : Function.Injective lift)
    (D : Divisor K F) {ι : Type*} (B : ι → K') (hB : LinearIndependent K B)
    (g : ι →₀ F)
    (hmem : (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j))
      ∈ LSpace (K := K') (Finsupp.mapDomain lift D)) :
    ∀ j, g j ∈ LSpace (K := K) D := by
  classical
  intro j₀
  rcases eq_or_ne (g j₀) 0 with hj0 | hj0
  · rw [hj0]; exact zero_mem _
  have hj0supp : j₀ ∈ g.support := Finsupp.mem_support_iff.mpr hj0
  have hgne : g ≠ 0 := fun h => hj0 (by rw [h]; rfl)
  refine mem_lSpace_iff_ord.mpr (Or.inr fun v => ?_)
  obtain ⟨hne, hle⟩ :=
    Place.ord_sum_algebraMap_mul_le_ord_of_linearIndependent_of_constantFieldExtension
      K F K' F' hfg hfg' hgen lift hlift_ord v B hB g hgne
  have hordSig : -(Finsupp.mapDomain lift D) (lift v) ≤
      (lift v).ord (∑ j ∈ g.support, algebraMap K' F' (B j) * algebraMap F F' (g j)) :=
    (mem_lSpace_iff_ord.mp hmem).resolve_left hne (lift v)
  rw [Finsupp.mapDomain_apply_of_injective hlift_inj] at hordSig
  exact hordSig.trans (hle j₀ hj0supp)

/-! ## The private engine: conductors, fibre ideals and their norms

The pin's `S_` file derives the norm formula through the conductor of `v` in the
integral closure of its valuation subring in `F'`; the block is private here, as the
pin keeps it below its headline. -/

section Engine

variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [CharZero F]

namespace Place

variable (v : Place K F)

private instance : Module.Free v.toValuationSubring (integralClosureAt F' v) :=
  Module.free_of_finite_type_torsion_free'

private abbrev conductorIdeal : Ideal (integralClosureAt F' v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (integralClosureAt F' v))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

theorem conductorIdeal_ne_top : conductorIdeal (F' := F') v ≠ ⊤ := by
  obtain ⟨Q, hQmax, hQover⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (R := v.toValuationSubring) (S := integralClosureAt F' v)
    (IsLocalRing.maximalIdeal v.toValuationSubring)
    (fun x hx => by
      rw [RingHom.mem_ker] at hx
      rw [show x = 0 from algebraMap_integralClosureAt_injective v (by rw [hx, map_zero])]
      exact zero_mem _)
  intro htop
  exact hQmax.ne_top (top_le_iff.mp (htop ▸ Ideal.map_le_iff_le_comap.mpr hQover.ge))

omit [Algebra K F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']
  [CharZero F] in

theorem conductorIdeal_ne_bot : conductorIdeal (F' := F') v ≠ ⊥ := by
  intro h
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπmem : algebraMap v.toValuationSubring (integralClosureAt F' v) π
      ∈ conductorIdeal (F' := F') v :=
    Ideal.mem_map_of_mem _ (hπ.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
  rw [h, Ideal.mem_bot] at hπmem
  exact hπ.ne_zero (algebraMap_integralClosureAt_injective v (by rw [hπmem, map_zero]))

private instance conductorQuotientAlgebra :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ conductorIdeal (F' := F') v) :=
  Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] in

theorem residue_norm_eq_norm_mk (c : integralClosureAt F' v) :
    IsLocalRing.residue v.toValuationSubring
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by
  have key : algebraMap v.toValuationSubring
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
        (Algebra.norm v.toValuationSubring c)
      = Algebra.norm
          (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c) := by
    have hequiv := Algebra.norm_eq_of_algEquiv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor (A := v.toValuationSubring)
        (integralClosureAt F' v) (IsLocalRing.maximalIdeal v.toValuationSubring))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
    rw [Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk] at hequiv
    have hbase : algebraMap v.toValuationSubring
        (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
          (Algebra.norm v.toValuationSubring c)
          = Algebra.norm
              (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
              ((1 : v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
                ⊗ₜ[v.toValuationSubring] c) := by
      rw [Algebra.norm_apply, Algebra.norm_apply, ← Algebra.baseChange_lmul,
        LinearMap.det_baseChange]
    exact hbase.trans hequiv
  exact key

end Place

/-! ### The fibre-centre power and its residue ring -/

namespace Place

variable {v : Place K F} {w : Place K F'}

private abbrev fiberCenterPow (hw : w.restrict F = v) : Ideal (integralClosureAt F' v) :=
  (fiberCenter F' v hw).asIdeal
    ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
        (fiberCenter F' v hw).asIdeal

omit [CharZero F] in

theorem conductorIdeal_le_fiberCenterPow (hw : w.restrict F = v) :
    conductorIdeal (F' := F') v ≤ fiberCenterPow hw :=
  Ideal.le_pow_ramificationIdx'

omit [CharZero F] in

theorem fiberCenterPow_ne_top (hw : w.restrict F = v) : fiberCenterPow hw ≠ ⊤ := by
  have hpos : 0 < (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter hw]
    exact w.ramificationIndex_pos
  intro htop
  refine ((fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot).ne_top
    (top_le_iff.mp ?_)
  calc (⊤ : Ideal (integralClosureAt F' v)) = fiberCenterPow hw := htop.symm
    _ ≤ (fiberCenter F' v hw).asIdeal ^ 1 := Ideal.pow_le_pow_right hpos
    _ = (fiberCenter F' v hw).asIdeal := pow_one _

private instance fiberCenterPowQuotientAlgebra (hw : w.restrict F = v) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberCenterPow hw))

private instance (hw : w.restrict F = v) :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := by
  haveI : IsScalarTower v.toValuationSubring
      (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) := IsScalarTower.of_algebraMap_eq' rfl
  exact Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring)
    (integralClosureAt F' v ⧸ fiberCenterPow hw)

omit [CharZero F] in

theorem isNilpotent_mk_sub_algebraMap (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    IsNilpotent (Ideal.Quotient.mk (fiberCenterPow hw) c
      - algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberCenterPow hw)
          (IsLocalRing.residue v.toValuationSubring r)) := by
  have halg : algebraMap (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberCenterPow hw) (IsLocalRing.residue v.toValuationSubring r)
        = Ideal.Quotient.mk (fiberCenterPow hw)
            (algebraMap v.toValuationSubring (integralClosureAt F' v) r) := rfl
  rw [halg, ← map_sub]
  refine ⟨(IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
    (fiberCenter F' v hw).asIdeal, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.pow_mem_pow hr _

omit [CharZero F] in

theorem norm_mk_fiberCenterPow (hw : w.restrict F = v) {c : integralClosureAt F' v}
    {r : v.toValuationSubring}
    (hr : c - algebraMap v.toValuationSubring (integralClosureAt F' v) r
      ∈ (fiberCenter F' v hw).asIdeal) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberCenterPow hw) c)
      = IsLocalRing.residue v.toValuationSubring r
          ^ Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
              (integralClosureAt F' v ⧸ fiberCenterPow hw) :=
  Algebra.norm_eq_pow_finrank_of_isNilpotent_sub_algebraMap
    (isNilpotent_mk_sub_algebraMap hw hr)

set_option linter.deprecated false in
omit [CharZero F] in

theorem finrank_fiberCenterPow (hw : w.restrict F = v) (hwrat : w.IsRational)
    (hvrat : v.IsRational) :
    Module.finrank (IsLocalRing.ResidueField v.toValuationSubring)
        (integralClosureAt F' v ⧸ fiberCenterPow hw)
      = w.ramificationIndex F := by
  haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
    (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
  have hne : (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
      (fiberCenter F' v hw).asIdeal ≠ 0 := by
    rw [← ramificationIndex_eq_ramificationIdx_fiberCenter hw]
    exact w.ramificationIndex_pos.ne'
  haveI := fiberCenter_liesOver hw
  have key : Module.finrank
      (v.toValuationSubring ⧸ IsLocalRing.maximalIdeal v.toValuationSubring)
      (integralClosureAt F' v ⧸ (fiberCenter F' v hw).asIdeal
        ^ (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
            (fiberCenter F' v hw).asIdeal) = w.ramificationIndex F := by
    rw [Ideal.finrank_prime_pow_ramificationIdx _ _ (fiberCenter F' v hw).ne_bot hne,
      ← Ideal.inertiaDeg_algebraMap, ← inertiaDeg_eq_inertiaDeg_fiberCenter hw,
      w.inertiaDeg_eq_one_of_isRational hwrat (hw.symm ▸ hvrat), mul_one,
      ← ramificationIndex_eq_ramificationIdx_fiberCenter hw]
  exact key

end Place

/-! ### The conductor as a product of fibre ideals -/

namespace Place

variable (v : Place K F) [HasPrincipalDivisors K F']

private instance : DecidableEq (Place K F') := Classical.decEq _

omit [CharZero F] [HasPrincipalDivisors K F'] in

def fiberIdeal (w : Place K F') : Ideal (integralClosureAt F' v) :=
  if hw : w.restrict F = v then fiberCenterPow hw else ⊤

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem fiberIdeal_of_mem {w : Place K F'} (hw : w.restrict F = v) :
    fiberIdeal v w = fiberCenterPow hw := dite_eq_left hw

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem fiberIdeal_of_notMem {w : Place K F'} (hw : ¬w.restrict F = v) :
    fiberIdeal v w = ⊤ := dite_eq_right hw

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem conductorIdeal_le_fiberIdeal (w : Place K F') :
    conductorIdeal (F' := F') v ≤ fiberIdeal v w := by
  by_cases hw : w.restrict F = v
  · rw [fiberIdeal_of_mem v hw]
    exact conductorIdeal_le_fiberCenterPow hw
  · rw [fiberIdeal_of_notMem v hw]
    exact le_top

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem isCoprime_fiberIdeal {w w' : Place K F'} (hne : w ≠ w') :
    IsCoprime (fiberIdeal v w) (fiberIdeal v w') := by
  by_cases hw : w.restrict F = v
  · by_cases hw' : w'.restrict F = v
    · rw [fiberIdeal_of_mem v hw, fiberIdeal_of_mem v hw']
      haveI : (fiberCenter F' v hw).asIdeal.IsMaximal :=
        (fiberCenter F' v hw).isPrime.isMaximal (fiberCenter F' v hw).ne_bot
      haveI : (fiberCenter F' v hw').asIdeal.IsMaximal :=
        (fiberCenter F' v hw').isPrime.isMaximal (fiberCenter F' v hw').ne_bot
      refine IsCoprime.pow (Ideal.isCoprime_of_isMaximal ?_)
      intro heq
      exact hne (eq_of_fiberCenter_eq hw hw' (HeightOneSpectrum.ext heq))
    · rw [fiberIdeal_of_notMem v hw', ← Ideal.one_eq_top]
      exact isCoprime_one_right
  · rw [fiberIdeal_of_notMem v hw, ← Ideal.one_eq_top]
    exact isCoprime_one_left

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem count_normalizedFactors_conductorIdeal {w : Place K F'} (hw : w.restrict F = v) :
    (normalizedFactors (conductorIdeal (F' := F') v)).count (fiberCenter F' v hw).asIdeal
      = (IsLocalRing.maximalIdeal v.toValuationSubring).ramificationIdx'
          (fiberCenter F' v hw).asIdeal := by
  haveI : (fiberCenter F' v hw).asIdeal.IsPrime := (fiberCenter F' v hw).isPrime
  exact (Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count
    (conductorIdeal_ne_bot (F' := F') v) inferInstance (fiberCenter F' v hw).ne_bot).symm

omit [CharZero F] in

theorem conductorIdeal_eq_prod_fiber :
    conductorIdeal (F' := F') v = ∏ w ∈ v.fiber F', fiberIdeal v w := by
  classical
  have hbot := conductorIdeal_ne_bot (F' := F') v
  set S : Multiset (Ideal (integralClosureAt F' v)) := normalizedFactors (conductorIdeal v)
    with hS
  have hfactor : ∀ Q ∈ S.toFinset, ∃ w' : Place K F', ∃ hw' : w'.restrict F = v,
      (fiberCenter F' v hw').asIdeal = Q := by
    intro Q hQ
    rw [Multiset.mem_toFinset] at hQ
    have hQprime : Prime Q := prime_of_normalized_factor Q hQ
    have hQbot : Q ≠ ⊥ := hQprime.ne_zero
    haveI : Q.IsPrime := Ideal.isPrime_of_prime hQprime
    exact ⟨placeOfPrime ⟨Q, inferInstance, hQbot⟩, restrict_placeOfPrime _,
      congrArg HeightOneSpectrum.asIdeal (fiberCenter_placeOfPrime
        (⟨Q, inferInstance, hQbot⟩ : HeightOneSpectrum (integralClosureAt F' v)))⟩
  set T : Finset (Ideal (integralClosureAt F' v)) := (v.fiber F').attach.image
    (fun w' => (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) with hT
  have hsub : S.toFinset ⊆ T := by
    intro Q hQ
    obtain ⟨w', hw', rfl⟩ := hfactor Q hQ
    exact Finset.mem_image.mpr ⟨⟨w', mem_fiber.mpr hw'⟩, Finset.mem_attach _ _, rfl⟩
  have hinj : Set.InjOn (fun w' : {x // x ∈ v.fiber F'} =>
      (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal) (v.fiber F').attach := by
    intro w₁ _ w₂ _ h
    exact Subtype.ext (eq_of_fiberCenter_eq (mem_fiber.mp w₁.2) (mem_fiber.mp w₂.2)
      (HeightOneSpectrum.ext h))
  calc
    conductorIdeal (F' := F') v = ∏ Q ∈ S.toFinset, Q ^ S.count Q := by
          rw [← Finset.prod_multiset_count, hS, Ideal.prod_normalizedFactors_eq_self hbot]
    _ = ∏ Q ∈ T, Q ^ S.count Q := by
          refine Finset.prod_subset hsub fun Q _ hQ => ?_
          rw [Multiset.count_eq_zero_of_notMem
            (fun h => hQ (Multiset.mem_toFinset.mpr h)), pow_zero]
    _ = ∏ w' ∈ (v.fiber F').attach,
          (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal
            ^ S.count (fiberCenter F' v (mem_fiber.mp w'.2)).asIdeal := by
          rw [hT, Finset.prod_image hinj]
    _ = ∏ w' ∈ (v.fiber F').attach, fiberIdeal v w'.1 := by
          refine Finset.prod_congr rfl fun w' _ => ?_
          rw [hS, count_normalizedFactors_conductorIdeal v (mem_fiber.mp w'.2),
            fiberIdeal_of_mem v (mem_fiber.mp w'.2)]
    _ = ∏ w ∈ v.fiber F', fiberIdeal v w := Finset.prod_attach (v.fiber F') (fiberIdeal v)

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem prod_fiberIdeal_le_of_subset {s t : Finset (Place K F')} (hst : s ⊆ t) :
    ∏ w ∈ t, fiberIdeal v w ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  rw [← Finset.prod_sdiff hst]
  exact Ideal.mul_le_right

omit [CharZero F] in

theorem conductorIdeal_le_prod_fiberIdeal (s : Finset (Place K F')) :
    conductorIdeal (F' := F') v ≤ ∏ w ∈ s, fiberIdeal v w := by
  classical
  calc conductorIdeal (F' := F') v
      = ∏ w ∈ v.fiber F', fiberIdeal v w := conductorIdeal_eq_prod_fiber v
    _ = ∏ w ∈ v.fiber F' ∪ s, fiberIdeal v w := by
        refine Finset.prod_subset Finset.subset_union_left fun w _ hw' => ?_
        exact (fiberIdeal_of_notMem v fun hmem => hw' (mem_fiber.mpr hmem)).trans
          Ideal.one_eq_top.symm
    _ ≤ ∏ w ∈ s, fiberIdeal v w :=
        prod_fiberIdeal_le_of_subset v Finset.subset_union_right

end Place
/-! ### Norms modulo the fibre ideals -/

namespace Place

variable (v : Place K F) [HasPrincipalDivisors K F']

private instance : DecidableEq (Place K F') := Classical.decEq _

private instance fiberIdealQuotientAlgebra (w : Place K F') :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_fiberIdeal v w))

private instance prodFiberIdealQuotientAlgebra (s : Finset (Place K F')) :
    Algebra (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
  Ideal.Quotient.algebraQuotientOfLEComap
    (Ideal.map_le_iff_le_comap.mp (conductorIdeal_le_prod_fiberIdeal v s))

omit [Algebra K F'] [IsScalarTower K F F'] [CharZero F] [HasPrincipalDivisors K F'] in

theorem finite_quotient_of_conductorLE (Q : Ideal (integralClosureAt F' v))
    [Algebra (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)]
    [IsScalarTower v.toValuationSubring (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q)] :
    Module.Finite (IsLocalRing.ResidueField v.toValuationSubring)
      (integralClosureAt F' v ⧸ Q) :=
  Module.Finite.of_restrictScalars_finite v.toValuationSubring
    (IsLocalRing.ResidueField v.toValuationSubring) (integralClosureAt F' v ⧸ Q)

omit [CharZero F] in

theorem norm_mk_prod_fiberIdeal (c : integralClosureAt F' v) (s : Finset (Place K F')) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c)
      = ∏ w ∈ s,
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  induction s using Finset.cons_induction with
  | empty =>
      haveI : Subsingleton
          (integralClosureAt F' v ⧸ (∏ w ∈ (∅ : Finset (Place K F')), fiberIdeal v w)) :=
        Ideal.Quotient.subsingleton_iff.mpr (by rw [Finset.prod_empty]; exact Ideal.one_eq_top)
      conv_rhs => rw [Finset.prod_empty]
      exact Algebra.norm_of_subsingleton _
  | cons a s ha ih =>
      have hcop : IsCoprime (fiberIdeal v a) (∏ w ∈ s, fiberIdeal v w) :=
        IsCoprime.prod_right fun w hw => isCoprime_fiberIdeal v (fun h => ha (h ▸ hw))
      have hprod : ∏ w ∈ Finset.cons a s ha, fiberIdeal v w
          = fiberIdeal v a ⊓ ∏ w ∈ s, fiberIdeal v w := by
        rw [Finset.prod_cons, Ideal.mul_eq_inf_of_isCoprime hcop]
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := IsScalarTower.of_algebraMap_eq' rfl
      haveI : IsScalarTower v.toValuationSubring
          (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        IsScalarTower.of_algebraMap_eq' rfl
      haveI := finite_quotient_of_conductorLE v (fiberIdeal v a)
      haveI := finite_quotient_of_conductorLE v (∏ w ∈ s, fiberIdeal v w)
      haveI : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ fiberIdeal v a) := Module.Free.of_divisionRing _ _
      haveI : Module.Free (IsLocalRing.ResidueField v.toValuationSubring)
          (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) := Module.Free.of_divisionRing _ _
      set e : (integralClosureAt F' v ⧸ (∏ w ∈ Finset.cons a s ha, fiberIdeal v w)) ≃+*
          (integralClosureAt F' v ⧸ fiberIdeal v a)
            × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w) :=
        (Ideal.quotEquivOfEq hprod).trans
          (Ideal.quotientInfEquivQuotientProd _ _ hcop) with he
      have hemk : ∀ x : integralClosureAt F' v,
          e (Ideal.Quotient.mk _ x) = (Ideal.Quotient.mk _ x, Ideal.Quotient.mk _ x) := by
        intro x
        rw [he, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
        exact Prod.ext
          (by rw [Ideal.quotientInfEquivQuotientProd_fst, Ideal.Quotient.factor_mk])
          (by rw [Ideal.quotientInfEquivQuotientProd_snd, Ideal.Quotient.factor_mk])
      have hkey : Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)
            = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                ((Ideal.Quotient.mk (fiberIdeal v a) c,
                  Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) :
                  (integralClosureAt F' v ⧸ fiberIdeal v a)
                    × (integralClosureAt F' v ⧸ ∏ w ∈ s, fiberIdeal v w)) := by
        refine (Algebra.norm_eq_of_equiv_equiv
          (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring)) e ?_
          (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c)).trans ?_
        · refine RingHom.ext fun x => ?_
          obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
          exact (hemk (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm
        · rw [hemk]
          rfl
      calc (Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ Finset.cons a s ha, fiberIdeal v w) c))
          = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (fiberIdeal v a) c)
            * Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
              (Ideal.Quotient.mk (∏ w ∈ s, fiberIdeal v w) c) := by
            rw [hkey]; exact Algebra.norm_prod _
        _ = ∏ w ∈ Finset.cons a s ha,
              Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
                (Ideal.Quotient.mk (fiberIdeal v w) c) := by
            rw [Finset.prod_cons, ih]

omit [CharZero F] in

theorem norm_mk_conductor_eq_prod_fiber (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
      = ∏ w ∈ v.fiber F',
          Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
            (Ideal.Quotient.mk (fiberIdeal v w) c) := by
  classical
  rw [← norm_mk_prod_fiberIdeal v c (v.fiber F')]
  have he : (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v))
      (Ideal.Quotient.mk (conductorIdeal (F' := F') v) c)
        = Ideal.Quotient.mk (∏ w ∈ v.fiber F', fiberIdeal v w) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (conductorIdeal_eq_prod_fiber (F' := F') v)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (conductorIdeal_eq_prod_fiber (F' := F') v)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

end Place

/-! ### The residue of `c` is the value of `c` at the place -/

namespace Place

variable {v : Place K F} [HasPrincipalDivisors K F']

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem sub_algebraMap_evalAt_mem_fiberCenter {w : Place K F'} (hw : w.restrict F = v)
    (hwrat : w.IsRational) {c : integralClosureAt F' v}
    (_hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (_hord : w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    c - algebraMap v.toValuationSubring (integralClosureAt F' v)
        (algebraMap K v.toValuationSubring
          (w.evalAt (algebraMap (integralClosureAt F' v) F' c)))
      ∈ (fiberCenter F' v hw).asIdeal := by
  set lam : K := w.evalAt (algebraMap (integralClosureAt F' v) F' c) with hlam
  set d : integralClosureAt F' v := c - algebraMap v.toValuationSubring
    (integralClosureAt F' v) (algebraMap K v.toValuationSubring lam) with hd
  rcases eq_or_ne d 0 with hd0 | hd0
  · rw [hd0]; exact Ideal.zero_mem _
  rw [mem_fiberCenter_iff_ord_pos hw hd0]
  have hcoe : algebraMap (integralClosureAt F' v) F' d
      = algebraMap (integralClosureAt F' v) F' c - algebraMap K F' lam := by
    rw [hd, map_sub]
    congr 1
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply v.toValuationSubring
      F F',
      show (algebraMap v.toValuationSubring F) (algebraMap K v.toValuationSubring lam)
        = algebraMap K F lam from v.coe_algebraMap lam,
      ← IsScalarTower.algebraMap_apply]
  have hmem : algebraMap (integralClosureAt F' v) F' c ∈ w.toValuationSubring :=
    forall_mem_of_restrict_eq hw c
  have hres : residue w.toValuationSubring ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
      = algebraMap K w.ResidueField lam := (w.algebraMap_evalAt hwrat hmem).symm
  have hdmem : algebraMap (integralClosureAt F' v) F' d ∈ w.toValuationSubring := by
    rw [hcoe]
    exact sub_mem hmem (w.algebraMap_mem' lam)
  have hdF : algebraMap (integralClosureAt F' v) F' d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (integralClosureAt F' v) F')).mpr hd0
  rw [← w.mem_maximalIdeal_iff_ord_pos hdF hdmem]
  rw [← IsLocalRing.residue_eq_zero_iff]
  have hsplit : (⟨algebraMap (integralClosureAt F' v) F' d, hdmem⟩ : w.toValuationSubring)
      = ⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
        - algebraMap K w.toValuationSubring lam := by
    refine Subtype.ext ?_
    show algebraMap (integralClosureAt F' v) F' d
      = ((⟨algebraMap (integralClosureAt F' v) F' c, hmem⟩
          - algebraMap K w.toValuationSubring lam : w.toValuationSubring) : F')
    rw [hcoe]
    push_cast
    rw [w.coe_algebraMap]
  rw [hsplit, map_sub, hres, sub_eq_zero, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply]

end Place

/-! ### The norm on a fibre centre power, and the product formula -/

namespace Place

variable {v : Place K F} [HasPrincipalDivisors K F']

private instance : DecidableEq (Place K F') := Classical.decEq _

omit [CharZero F] in

theorem algebraMap_evalAt_coe (hv : v.IsRational) (r : v.toValuationSubring) :
    algebraMap K v.ResidueField
        (v.evalAt (algebraMap v.toValuationSubring F r))
      = IsLocalRing.residue v.toValuationSubring r := by
  have hcoe : algebraMap v.toValuationSubring F r = (r : F) := rfl
  rw [hcoe]
  have hmem : (r : F) ∈ v.toValuationSubring := r.2
  rw [v.algebraMap_evalAt hv hmem]

omit [CharZero F] in

/-- The residue of a constant is that constant, in the algebra form the proof reads off
the quotient (`Place.residue_algebraMap` is the subtype form). -/
theorem residue_algebraMap_vs (lam : K) :
    IsLocalRing.residue v.toValuationSubring (algebraMap K v.toValuationSubring lam)
      = algebraMap K v.ResidueField lam :=
  Place.residue_algebraMap v lam

omit [CharZero F] [HasPrincipalDivisors K F'] in

theorem norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow {w : Place K F'}
    (hw : w.restrict F = v) (c : integralClosureAt F' v) :
    Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
        (Ideal.Quotient.mk (fiberIdeal v w) c)
      = Algebra.norm (IsLocalRing.ResidueField v.toValuationSubring)
          (Ideal.Quotient.mk (fiberCenterPow hw) c) := by
  have he : (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw))
      (Ideal.Quotient.mk (fiberIdeal v w) c) = Ideal.Quotient.mk (fiberCenterPow hw) c :=
    Ideal.quotEquivOfEq_mk _ _
  rw [← he]
  refine Algebra.norm_eq_of_equiv_equiv
    (RingEquiv.refl (IsLocalRing.ResidueField v.toValuationSubring))
    (Ideal.quotEquivOfEq (fiberIdeal_of_mem v hw)) ?_ _
  refine RingHom.ext fun x => ?_
  obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
  exact (Ideal.quotEquivOfEq_mk (fiberIdeal_of_mem v hw)
    (algebraMap v.toValuationSubring (integralClosureAt F' v) r)).symm

omit [CharZero F] in

theorem residue_norm_eq_prod_evalAt (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) {c : integralClosureAt F' v}
    (hc : algebraMap (integralClosureAt F' v) F' c ≠ 0)
    (hord : ∀ w ∈ v.fiber F', w.ord (algebraMap (integralClosureAt F' v) F' c) = 0) :
    IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c)
      = ∏ w ∈ v.fiber F',
          algebraMap K v.ResidueField
              (w.evalAt (algebraMap (integralClosureAt F' v) F' c))
            ^ w.ramificationIndex F := by
  classical
  rw [residue_norm_eq_norm_mk v c, norm_mk_conductor_eq_prod_fiber v c]
  refine Finset.prod_congr rfl fun w hw => ?_
  have hwv : w.restrict F = v := mem_fiber.mp hw
  have hsub := sub_algebraMap_evalAt_mem_fiberCenter hwv (hrat w hw) hc (hord w hw)
  rw [norm_mk_fiberIdeal_eq_norm_mk_fiberCenterPow hwv c, norm_mk_fiberCenterPow hwv hsub,
    finrank_fiberCenterPow hwv (hrat w hw) hv, residue_algebraMap_vs]

end Place

end Engine

namespace Place

/-- **The value of a norm is the product of the values over the fibre.** Statement from
`Theorems/Thm_AlgebraicCurve_Place_evalAt_norm_eq_prod_fiber.lean`; proof after the pin's
`S_` file: compare in the residue field of `v`, where the norm of the image of `c` in
`A ⧸ conductorIdeal` is the product of the norms modulo the fibre ideals. -/
theorem evalAt_norm_eq_prod_fiber {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']
    (v : Place K F) (f : F') (hf : f ≠ 0) (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w) (hord : ∀ w ∈ v.fiber F', w.ord f = 0) :
    v.evalAt (Algebra.norm F f)
      = ∏ w ∈ v.fiber F', w.evalAt f ^ (w.ramificationIndex F) := by
  classical
  obtain ⟨c, rfl⟩ := Place.exists_integralClosureAt_of_ord_fiber_nonneg
    (v := v) hf (fun w hw => (hord w hw).ge)
  have hc : c ≠ 0 := fun h => hf (by rw [h, map_zero])
  have hnorm : Algebra.norm F (algebraMap (integralClosureAt F' v) F' c)
      = algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c) := by
    rw [← Algebra.algebraMap_intNorm (A := v.toValuationSubring) (K := F) (L := F')
      (B := integralClosureAt F' v), Algebra.intNorm_eq_norm]
  refine v.algebraMap_residueField_injective ?_
  rw [hnorm]
  have hlhs : algebraMap K v.ResidueField
      (v.evalAt (algebraMap v.toValuationSubring F (Algebra.norm v.toValuationSubring c)))
        = IsLocalRing.residue v.toValuationSubring (Algebra.norm v.toValuationSubring c) :=
    Place.algebraMap_evalAt_coe hv _
  rw [hlhs, Place.residue_norm_eq_prod_evalAt hv hrat hf hord, map_prod]
  exact Finset.prod_congr rfl fun w hw => (map_pow _ _ _).symm

end Place

namespace Divisor

private theorem zpow_finset_sum' {K : Type*} [Field K] {c : K} (hc : c ≠ 0) {ι : Type*}
    (s : Finset ι) (n : ι → ℤ) : ∏ i ∈ s, c ^ n i = c ^ (∑ i ∈ s, n i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.prod_cons, Finset.sum_cons, zpow_add₀ hc, ih]

/-- **The `evalFun` of a base extension is the `evalFun` of the pushforward.**  For a
finite integral extension `F → F'`, a divisor `D` of `F'` supported on rational places
whose restrictions to `F` are rational, and a function `g` of `F` that is a unit at all
of them, evaluating the base-changed `g` on `D` is evaluating `g` on the pushed-forward
divisor.  Statement from
`Theorems/Thm_AlgebraicCurve_Divisor_evalFun_algebraMap_pushforward.lean`; proof after
the pin's `S_` file — `evalFun` is a product over the support, so both sides are
fiberwise products over the restriction map, and each fibre contributes
`evalAt g ^ (D w · inertiaDeg)`, the inertia degree being `1` since every place
involved is rational. -/
theorem evalFun_algebraMap_pushforward {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
    [Algebra.IsIntegral F F'] {g : F} (hg : g ≠ 0) (D : Divisor K F')
    (hratw : ∀ w ∈ D.support, Place.IsRational w)
    (hratv : ∀ w ∈ D.support, (w.restrict F).IsRational)
    (hord : ∀ w ∈ D.support, (w.restrict F).ord g = 0) :
    Divisor.evalFun (algebraMap F F' g) D = Divisor.evalFun g (Divisor.pushforward F D) := by
  classical
  have hstep1 : evalFun (algebraMap F F' g) D
      = ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w := by
    rw [evalFun_def]
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [w.evalAt_algebraMap_eq_evalAt_restrict (hratv w hw)
      ((w.restrict F).mem_of_ord_nonneg hg (hord w hw).ge)]
  have hne : ∀ w ∈ D.support, (w.restrict F).evalAt g ≠ 0 := fun w hw =>
    (w.restrict F).evalAt_ne_zero (hratv w hw) hg (hord w hw)
  have hstep2 : ∏ w ∈ D.support, (w.restrict F).evalAt g ^ D w
      = ∏ v ∈ D.support.image (fun w => w.restrict F),
          ∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w :=
    (Finset.prod_fiberwise_of_maps_to
      (fun w hw => Finset.mem_image.mpr ⟨w, hw, rfl⟩) _).symm
  have hstep3 : ∀ v ∈ D.support.image (fun w => w.restrict F),
      (∏ w ∈ D.support with w.restrict F = v, (w.restrict F).evalAt g ^ D w)
        = v.evalAt g ^ (pushforward F D v) := by
    intro v hv
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hv
    calc
      ∏ w ∈ D.support with w.restrict F = w₀.restrict F, (w.restrict F).evalAt g ^ D w
          = ∏ w ∈ D.support with w.restrict F = w₀.restrict F,
              (w₀.restrict F).evalAt g ^ (D w * (w.inertiaDeg F : ℤ)) := by
            refine Finset.prod_congr rfl fun w hw => ?_
            obtain ⟨hwD, hwv⟩ := Finset.mem_filter.mp hw
            rw [hwv, w.inertiaDeg_eq_one_of_isRational (hratw w hwD) (hratv w hwD),
              Nat.cast_one, mul_one]
      _ = (w₀.restrict F).evalAt g
            ^ (∑ w ∈ D.support with w.restrict F = w₀.restrict F,
                D w * (w.inertiaDeg F : ℤ)) :=
            zpow_finset_sum' (hne w₀ hw₀) _ _
      _ = (w₀.restrict F).evalAt g ^ (pushforward F D (w₀.restrict F)) := by
            rw [pushforward_apply, Finset.sum_filter]
  rw [hstep1, hstep2, Finset.prod_congr rfl hstep3]
  exact (Finsupp.prod_of_support_subset _ (support_pushforward_subset D)
    (fun v n => v.evalAt g ^ n) fun v _ => zpow_zero _).symm

end Divisor

end AlgebraicCurve
