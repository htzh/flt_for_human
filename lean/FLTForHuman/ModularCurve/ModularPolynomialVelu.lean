/-
  The forward modular equation for an odd Vélu quotient.

  For `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)`, an elliptic `W/𝕂`, a point `Q` with
  `addOrderOf Q = 2n+1`, and the odd Vélu quotient `W/⟨Q⟩` again elliptic,
  `j(W/⟨Q⟩)` is a root of `Φ_{2n+1}(j(W), Y)`.  That is one half of the moduli
  interpretation of the modular polynomial at a transcendental `j` — "a cyclic
  `N`-isogeny gives a root".  The other half (every root is such a quotient, and
  the `ψ(N)`-count that glues the two) is scoped with this one in
  `lean/topics/modularCurve/TOPIC-modular-equation-transcendental-j.md`.

  The proof instantiates
  `WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward`,
  the general theorem that a cyclic kernel of order `N` over an algebraically
  closed characteristic-`0` field forces `Φ_N(j(E), j(E')) = 0`.  The Vélu
  function-field embedding supplies the integral finite `ι` with kernel `ℤQ` and
  degree `2n+1`, and the seven premises that theorem consumes (the theorem itself,
  the Vélu embedding, the two genus-one place-gate producers, the Dedekind
  coordinate ring, principal divisors, `HahnSeries.isAlgClosed_rat`,
  `AlgebraicCurve.normFormulaAlong`) are all in the port.  Nothing in the proof is new mathematics; it is the instance
  plumbing that makes the capstone's hypotheses available.

  Pin `anthropics/fermats-last-theorem@aa2d8b3`: statement
  `Theorems/Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean`,
  proof `P2M/Sol/S_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean`
  (87 lines).  The porting history — readiness measurement, premise homes,
  substitutions, warning audit — is in `lean/logs/modular-polynomial-velu.md`.

  ## The two faces of the same equality

  For a transcendental `j(W)` and odd `N`, the roots of `Φ_N(j(W), Y)` are exactly the
  `j(W/H)` for the cyclic order-`N` subgroups `H ≤ W[N]`.  The forward node above is the
  `⇒`; this module also carries the two statements the theory consumes.

  *The product form* (`fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`, at an odd
  prime `ℓ`): the fibre of `Φ_ℓ` at `j(W)` factors over an injective family of `ℓ + 1`
  order-`ℓ` points as `∏ i, (X - C (j (W/⟨Q i⟩)))`.  The forward node makes each
  quotient's `j` a root, transcendental rigidity makes the family injective, and
  `ψ(ℓ) = ℓ + 1` supplies the degree count; monic polynomials of equal degree with the
  same roots coincide.  That is the `N = 2` row
  (`ModularPolynomialFibreTwo.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j`) at general odd
  prime level.

  *The root-membership face* (`mem_of_isRoot_map_j_of_transcendental_of_odd`, 145 lines):
  if a subfield `L` contains the coefficients of `W` and the coordinates of every
  `N`-torsion point, then every root of `Φ_N(j(W), Y)` lies in `L`.  The proof runs the
  same set equality inside `L` — every `j(W/H)` is in `L` by the Vélu-quotient membership
  lemma, and `Φ_N(j(W), ·)` has exactly `ψ(N)` roots because it is monic of that degree
  over an algebraically closed field — and reads off `r ∈ L`.  The public statement is
  that corollary; the set equality itself stays inside the proof.

  Pin files for these two:
  `Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean`
  (31 lines) with proof
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean`
  (97 lines), and
  `Theorems/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean`
  (25 lines) with proof
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean`
  (145 lines).

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean
-/
import FLTForHuman.ModularCurve.Defs.DedekindPsi
import FLTForHuman.ModularCurve.Defs.FibrePoly
import FLTForHuman.ModularCurve.ModularPolynomialEvalJ
import FLTForHuman.RingTheory.HahnSeries.IsAlgClosed
import FLTForHuman.WeierstrassCurve.GenusOnePlaceGateCentred
import FLTForHuman.WeierstrassCurve.Place.CoordinateRingDedekind
import FLTForHuman.WeierstrassCurve.PrincipalDivisors
import FLTForHuman.WeierstrassCurve.Velu.CyclicQuotientJInjective
import FLTForHuman.WeierstrassCurve.Velu.CyclicSubgroupCount
import FLTForHuman.WeierstrassCurve.Velu.Discriminant
import FLTForHuman.WeierstrassCurve.Velu.PointMapOddOrder
import FLTForHuman.WeierstrassCurve.Velu.SubfieldMembership
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.HahnSeries.Multiplication

set_option autoImplicit false
-- Every `haveI` in the proof is load-bearing for typeclass search (the two gate
-- instances, alg-closed/char-zero, the principal-divisor instances), so the style
-- linter's `have` suggestion does not apply to an instance local; suppress it here,
-- as the other pin-transcribed modules with instance walls do.
set_option linter.style.haveILetI false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

local notation "𝕂" => HahnSeries ℚ (AlgebraicClosure ℚ)

/-- **The forward modular equation at a Vélu quotient.**  For an elliptic curve
`W` over `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` and a point `Q` of odd order
`2n+1` whose Vélu quotient `W/⟨Q⟩` is again elliptic, the `j`-invariant of the
quotient is a root of `Φ_{2n+1}(j(W), Y)`. -/
theorem ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (n : ℕ) (Q : W.toAffine.Point) (hQ : addOrderOf Q = 2 * n + 1)
    (hΔ : (W.veluQuotient (W.oddOrderSummingSet Q n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot
      (W.veluQuotient (W.oddOrderSummingSet Q n)).j := by
  haveI : (W.veluQuotient (W.oddOrderSummingSet Q n)).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI : IsAlgClosed 𝕂 := HahnSeries.isAlgClosed_rat
  haveI : CharZero 𝕂 :=
    charZero_of_injective_ringHom (HahnSeries.C_injective (R := AlgebraicClosure ℚ) (Γ := ℚ))

  haveI : IsDedekindDomain W.toAffine.CoordinateRing := CoordinateRing.isDedekindDomain W
  haveI : HasPrincipalDivisors 𝕂 W.toAffine.FunctionField := hasPrincipalDivisors_functionField W.toAffine
  obtain ⟨g, hgc, hga⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (F := 𝕂) (W := W.toAffine)
  letI := g
  haveI := hgc
  haveI := hga
  haveI : IsDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.CoordinateRing :=
    CoordinateRing.isDedekindDomain (W.veluQuotient (W.oddOrderSummingSet Q n))
  haveI : HasPrincipalDivisors 𝕂 (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    hasPrincipalDivisors_functionField (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine
  obtain ⟨g', hgc', hga'⟩ :=
    exists_genusOnePlaceGate_isCentred_and_abelTheorem (F := 𝕂)
      (W := (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine)
  letI := g'
  haveI := hgc'
  haveI := hga'

  obtain ⟨ι, hι, hfin, hdeg, hker⟩ :=
    WeierstrassCurve.exists_veluFunctionFieldHom_pointMapOfPushforward_ker_eq_zmultiples
      (W := W) (Q := Q) (n := n) hQ hΔ

  haveI : CharZero (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField :=
    charZero_of_injective_algebraMap
      (algebraMap 𝕂 (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField).injective
  have hsep : SeparableAlong 𝕂 ι := by
    letI := algebraAlong ι
    haveI := isScalarTower_along ι
    haveI : Module.Finite (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine.FunctionField
        W.toAffine.FunctionField := hfin
    show Algebra.IsSeparable _ _
    infer_instance
  have hN : NormFormulaAlong 𝕂 ι hfin := AlgebraicCurve.normFormulaAlong ι hfin hsep
  have hkerQ := hker hN
  have hcyc : IsAddCyclic (pointMapOfPushforward ι hι hfin hN).ker := by
    rw [hkerQ]; infer_instance
  have hcard : Nat.card (pointMapOfPushforward ι hι hfin hN).ker = 2 * n + 1 := by
    rw [hkerQ, Nat.card_zmultiples, hQ]
  exact WeierstrassCurve.Affine.eval_modularPolynomial_map_j_eq_zero_of_isAddCyclic_ker_pointMapOfPushforward
    𝕂 W.toAffine (W.veluQuotient (W.oddOrderSummingSet Q n)).toAffine ι hι hfin hN (2 * n + 1)
    hcyc hcard data

/-! ### The product form: `Φ_ℓ(j(W), Y) = ∏ᵢ (Y - j(W/⟨Qᵢ⟩))` -/

section ProductForm

open Polynomial ModularCurve

/-- The product form at the abstract shape `N = 2n+1`, with the summing-set
half-index `m` passed separately so that the public statement's `ℓ / 2` can be
identified with `n` once `ℓ = 2n+1`.  `private`: it is a proof device, not a
statement of the theory.  (The pin states and uses the same shape inside its proof
of the public theorem.) -/
private theorem fibrePoly_j_eq_prod_of_odd_prime
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (n m : ℕ) (hmn : m = n) [Fact (2 * n + 1).Prime]
    (data : ModularPolynomialData (2 * n + 1))
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2 * n + 1 + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) m)).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j _ _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) m)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  subst hmn
  have hP : (2 * m + 1).Prime := Fact.out

  let jq : ι → HahnSeries ℚ (AlgebraicClosure ℚ) := fun i => @WeierstrassCurve.j _ _
    (W.veluQuotient (W.oddOrderSummingSet (Q i) m)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
  have hp0 : fibrePoly data.Φ W.j ≠ 0 := (ModularCurve.monic_fibrePoly data.monic W.j).ne_zero

  have hroot : ∀ i, (fibrePoly data.Φ W.j).IsRoot (jq i) := fun i =>
    ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq W m (Q i) (hQ i) (hΔ i) data

  have hinj : Function.Injective jq := by
    intro i i' h
    apply hQinj
    exact WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental W ht m (Q i) (Q i')
      (hQ i) (hQ i') (hΔ i) (hΔ i') h

  have hdeg : (fibrePoly data.Φ W.j).natDegree = Fintype.card ι := by
    rw [hι, ModularCurve.natDegree_fibrePoly data.monic, data.natDegree_eq,
      ModularCurve.dedekindPsi_prime hP]

  have hsnodup : (Finset.univ.val.map jq).Nodup := Finset.univ.nodup.map hinj
  have hsle : Finset.univ.val.map jq ≤ (fibrePoly data.Φ W.j).roots := by
    rw [Multiset.le_iff_subset hsnodup]
    intro a ha
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    exact (Polynomial.mem_roots hp0).mpr (hroot i)
  have hdvd : ((Finset.univ.val.map jq).map fun a => X - C a).prod ∣ fibrePoly data.Φ W.j :=
    (Multiset.prod_X_sub_C_dvd_iff_le_roots hp0 _).mpr hsle
  have hprod : ∏ i, (X - C (jq i)) = ((Finset.univ.val.map jq).map fun a => X - C a).prod := by
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]; rfl
  have hmonic' : (∏ i, (X - C (jq i))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hdeg' : (∏ i, (X - C (jq i))).natDegree = Fintype.card ι := by
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _]
    simp
  rw [hprod] at hmonic' hdeg'
  rw [← hprod] at hdvd hmonic' hdeg'

  exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonic' (ModularCurve.monic_fibrePoly data.monic W.j)
    hdvd (by rw [hdeg, hdeg'])

/-- **The product form of the modular equation at an odd prime.**  Let `ℓ` be an odd
prime, `W` elliptic over `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` with `j(W)`
transcendental, and `Q : ι → W` an injective family of `ℓ + 1` order-`ℓ` points with
elliptic odd Vélu quotients.  Then `Φ_ℓ(j(W), Y)` is the product of the linear factors
`Y - j(W/⟨Q i⟩)`.  Verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean`. -/
theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularPolynomialData ℓ)
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j _ _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  have hℓP : ℓ.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = 2 * n + 1 := by
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact h
  exact fibrePoly_j_eq_prod_of_odd_prime n ((2 * n + 1) / 2) (by omega) data W ht hι Q hQ hQinj hΔ

end ProductForm

/-! ### The converse: every root lies in the torsion field -/

section RootMembership

open Polynomial ModularCurve

variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The summing set of an odd-order point has both coordinates in any subfield that
contains the coordinates of every `N`-torsion point. -/
private theorem oddOrderSummingSet_coords_mem (L : Subfield F) {n : ℕ} {Q : W.toAffine.Point}
    (hord : addOrderOf Q = 2 * n + 1)
    (htors : ∀ (x y : F) (h : W.toAffine.Nonsingular x y),
      (2 * n + 1) • (Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L) :
    ∀ P ∈ W.oddOrderSummingSet Q n, P.1 ∈ L ∧ P.2 ∈ L := by
  intro P hP
  obtain ⟨k, hk1, hkn, hkP⟩ := W.mem_oddOrderSummingSet.mp hP
  have hkQne : k • Q ≠ 0 := by
    intro h
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero, hord] at h
    exact absurd (Nat.le_of_dvd hk1 h) (by omega)
  rcases hkQ : (k • Q) with _ | ⟨x, y, hns⟩
  · exact absurd hkQ hkQne
  have hQd : (2 * n + 1) • Q = 0 := hord ▸ addOrderOf_nsmul_eq_zero Q
  have hd : (2 * n + 1) • (Point.some x y hns : W.toAffine.Point) = 0 := by
    rw [← hkQ, smul_comm, hQd, smul_zero]
  rw [← hkP, hkQ]
  exact htors x y hns hd

/-- A cyclic subgroup of cardinality `m` is generated by an element of order `m`. -/
private theorem exists_generator_of_isAddCyclic {G : Type*} [AddCommGroup G] (H : AddSubgroup G)
    (hc : IsAddCyclic H) {m : ℕ} (hm : Nat.card H = m) :
    ∃ g : G, AddSubgroup.zmultiples g = H ∧ addOrderOf g = m := by
  obtain ⟨⟨g, hgH⟩, hg⟩ := hc.exists_generator
  have hzm : AddSubgroup.zmultiples g = H := by
    apply le_antisymm (AddSubgroup.zmultiples_le.mpr hgH)
    intro x hx
    obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hg ⟨x, hx⟩)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩
  refine ⟨g, hzm, ?_⟩
  rw [← Nat.card_zmultiples g, hzm, hm]

end RootMembership

open Polynomial ModularCurve in
/-- **Every root of the modular equation lies in the torsion field.**  If `L` is a
subfield of `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` containing the coefficients of an
elliptic `W/𝕂` and the coordinates of every `N`-torsion point, and `j(W)` is
transcendental, then every root of `Φ_N(j(W), Y)` lies in `L` (`N` odd).  Verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean`. -/
theorem ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    [DecidableEq (HahnSeries ℚ (AlgebraicClosure ℚ))]
    (W : WeierstrassCurve (HahnSeries ℚ (AlgebraicClosure ℚ))) [W.IsElliptic] (ht : Transcendental ℚ W.j)
    (L : Subfield (HahnSeries ℚ (AlgebraicClosure ℚ)))
    (h₁ : W.a₁ ∈ L) (h₂ : W.a₂ ∈ L) (h₃ : W.a₃ ∈ L) (h₄ : W.a₄ ∈ L) (h₆ : W.a₆ ∈ L)
    (htors : ∀ (x y : HahnSeries ℚ (AlgebraicClosure ℚ)) (h : W.toAffine.Nonsingular x y),
      N • (WeierstrassCurve.Affine.Point.some x y h : W.toAffine.Point) = 0 → x ∈ L ∧ y ∈ L)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hr : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)).IsRoot r) :
    r ∈ L := by
  haveI hK : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  haveI : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    charZero_of_injective_ringHom (HahnSeries.C_injective (R := AlgebraicClosure ℚ) (Γ := ℚ))
  obtain ⟨n, rfl⟩ := hN
  have hNK : ((2 * n + 1 : ℕ) : HahnSeries ℚ (AlgebraicClosure ℚ)) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  set Φj := data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ))) W.j)
    with hΦj
  have hΦjm : Φj.Monic := data.monic.map _

  let B := {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2 * n + 1}
  have hBcard : Nat.card B = ModularCurve.dedekindPsi (2 * n + 1) :=
    WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed
      (F := HahnSeries ℚ (AlgebraicClosure ℚ)) (K := HahnSeries ℚ (AlgebraicClosure ℚ)) W hNK
  have hψpos : 0 < ModularCurve.dedekindPsi (2 * n + 1) := by
    unfold ModularCurve.dedekindPsi
    refine Finset.sum_pos' (fun _ _ => Nat.zero_le _) ⟨1, ?_, ?_⟩
    · simp [Nat.mem_divisors]
    · simp
  haveI : Finite B := Nat.finite_of_card_ne_zero (hBcard ▸ hψpos.ne')
  haveI : Fintype B := Fintype.ofFinite _

  have hgen : ∀ H : B, ∃ g : W.toAffine.Point,
      AddSubgroup.zmultiples g = H.1 ∧ addOrderOf g = 2 * n + 1 :=
    fun H => exists_generator_of_isAddCyclic H.1 H.2.1 H.2.2
  choose gen hgenH hgenord using hgen
  have hΔgen : ∀ H : B, (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).Δ ≠ 0 := fun H =>
    WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq
      W n (gen H) (hgenord H)
  let jH : B → HahnSeries ℚ (AlgebraicClosure ℚ) := fun H =>
    haveI : (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (hΔgen H)⟩
    (W.veluQuotient (W.oddOrderSummingSet (gen H) n)).j

  have hjHmem : ∀ H : B, jH H ∈ L := fun H =>
    WeierstrassCurve.veluQuotient_j_mem_of_mem W L _ h₁ h₂ h₃ h₄ h₆
      (oddOrderSummingSet_coords_mem W L (hgenord H) htors) (hΔgen H)

  have hjHroot : ∀ H : B, Φj.IsRoot (jH H) := fun H =>
    ModularCurve.ModularPolynomialData.isRoot_map_j_veluQuotient_j_of_addOrderOf_eq W n (gen H) (hgenord H)
      (hΔgen H) data

  have hjHinj : Function.Injective jH := by
    intro H H' hjeq
    have hz := WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental W ht n (gen H) (gen H')
      (hgenord H) (hgenord H') (hΔgen H) (hΔgen H') hjeq
    exact Subtype.ext ((hgenH H).symm.trans (hz.trans (hgenH H')))

  have hJcard : (Finset.univ.image jH).card = ModularCurve.dedekindPsi (2 * n + 1) := by
    rw [Finset.card_image_of_injective _ hjHinj, Finset.card_univ, ← Nat.card_eq_fintype_card, hBcard]
  have hJsub : Finset.univ.image jH ⊆ Φj.roots.toFinset := by
    intro x hx
    obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]
    exact hjHroot H
  have hroots : Φj.roots.toFinset = Finset.univ.image jH := by
    refine (Finset.eq_of_subset_of_card_le hJsub ?_).symm
    calc Φj.roots.toFinset.card ≤ Multiset.card Φj.roots := Multiset.toFinset_card_le _
      _ = ModularCurve.dedekindPsi (2 * n + 1) := by
          rw [hΦj, ← data.natDegree_eq]
          exact ModularCurve.card_roots_fibrePoly_of_monic (K := HahnSeries ℚ (AlgebraicClosure ℚ)) data.monic W.j
      _ = (Finset.univ.image jH).card := hJcard.symm

  have hrmem : r ∈ Φj.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hΦjm.ne_zero]; exact hr
  rw [hroots] at hrmem
  obtain ⟨H, -, rfl⟩ := Finset.mem_image.mp hrmem
  exact hjHmem H

end
