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

  *The descent* is the module's last section.  The product form above is stated over
  `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)`; the `TDescent` block there embeds an arbitrary
  algebraically closed `K` of characteristic zero into `𝕂`, carries `W` and its `ℓ + 1` points
  along the embedding, commutes Vélu with it, and reads the equality back.  Its headline is
  `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed`, with pin
  `Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean`
  (30 lines) and proof
  `P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean`
  (510 lines); the transcendental node is the premise there, not re-proved.

  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_isRoot_map_j_veluQuotient_j_of_addOrderOf_eq.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_mem_of_isRoot_map_j_of_transcendental_of_odd.lean
  spec-pin: Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean
  spec-pin: P2M/Sol/S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean
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

/-! ### The descent to the transcendental node

The product form `fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` above is stated over
`𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)`.  This last section removes that restriction: for `W`
over an arbitrary algebraically closed field `K` of characteristic zero it embeds `K` into `𝕂`
(`exists_cover_hahn`; the cardinality input is `aleph0_lt_mk_hahn`, and `nonempty_ringHom_hahn`
supplies the embedding from `AlgebraicClosure L` by `IsAlgClosed.lift`), maps `W` and its
`ℓ + 1` points along the composite (`mapFun`/`mapPoint`), commutes Vélu with the map
(`veluQuotient_map`), runs the *ported* transcendental node there, and pulls the equality back
(`conclT_map_iff`).  The product form itself is never re-proved here.

The pin's whole `TDescent` block is transcribed verbatim in its own `TDescent` namespace (the
port's names for `mapFun`, `mapPoint`, `ConclT` cannot collide with anything else), and the
public statement
`fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed` is its headline. -/

section Descent

open Polynomial ModularCurve

universe uF

namespace TDescent

section MapPoint

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (W : WeierstrassCurve R)

-- A nonsingular point of `W` maps to a nonsingular point of the curve mapped along an
-- injective ring hom.  (`omit`: the two `DecidableEq`s are section variables for `mapFun_add`
-- only; the pin states the same signature.)
omit [DecidableEq R] [DecidableEq S] in
theorem nonsingular_map {x y : R} (h : W.toAffine.Nonsingular x y) :
    (W.map φ).toAffine.Nonsingular (φ x) (φ y) :=
  (Affine.map_nonsingular (W := W.toAffine) (f := φ) φ.injective x y).mpr h

/-- The map on the point sets induced by an injective ring hom `R →+* S`. -/
def mapFun : W.toAffine.Point → (W.map φ).toAffine.Point
  | 0 => 0
  | .some x y h => .some (φ x) (φ y) (nonsingular_map φ W h)

omit [DecidableEq R] [DecidableEq S] in
theorem mapFun_zero : mapFun φ W 0 = 0 := by rfl

omit [DecidableEq R] [DecidableEq S] in
theorem mapFun_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapFun φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := by rfl

/-- `mapFun` is a group homomorphism: the group law on points is a coordinate chase, and
the chord/tangent formulas commute with `φ` by `map_slope`, `map_addX`, `map_addY`,
`map_negY`.  The case order is the pin's. -/
theorem mapFun_add (P Q : W.toAffine.Point) :
    mapFun φ W (P + Q) = mapFun φ W P + mapFun φ W Q := by
  have hneg : ∀ x y : R, (W.map φ).toAffine.negY (φ x) (φ y) = φ (W.toAffine.negY x y) :=
    fun x y => Affine.map_negY (W' := W.toAffine) φ x y
  have hslope : ∀ x₁ x₂ y₁ y₂ : R,
      (W.map φ).toAffine.slope (φ x₁) (φ x₂) (φ y₁) (φ y₂) = φ (W.toAffine.slope x₁ x₂ y₁ y₂) :=
    fun x₁ x₂ y₁ y₂ => Affine.map_slope (W := W.toAffine) φ x₁ x₂ y₁ y₂
  have haddX : ∀ x₁ x₂ ℓ : R,
      (W.map φ).toAffine.addX (φ x₁) (φ x₂) (φ ℓ) = φ (W.toAffine.addX x₁ x₂ ℓ) :=
    fun x₁ x₂ ℓ => Affine.map_addX (W' := W.toAffine) φ x₁ x₂ ℓ
  have haddY : ∀ x₁ x₂ y₁ ℓ : R,
      (W.map φ).toAffine.addY (φ x₁) (φ x₂) (φ y₁) (φ ℓ) = φ (W.toAffine.addY x₁ x₂ y₁ ℓ) :=
    fun x₁ x₂ y₁ ℓ => Affine.map_addY (W' := W.toAffine) (f := φ) (x₁ := x₁) (x₂ := x₂)
      (y₁ := y₁) (ℓ := ℓ)
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  any_goals rfl
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · rw [Affine.Point.add_of_Y_eq hxy.1 hxy.2]
    exact (Affine.Point.add_of_Y_eq (congrArg φ hxy.1) (by rw [hxy.2, hneg])).symm
  · have hxy' : ¬(φ x₁ = φ x₂ ∧ φ y₁ = (W.map φ).toAffine.negY (φ x₂) (φ y₂)) := fun h =>
      hxy ⟨φ.injective h.1, φ.injective (by rw [hneg] at h; exact h.2)⟩
    rw [Affine.Point.add_some hxy]
    show mapFun φ W _ = Affine.Point.some _ _ _ + Affine.Point.some _ _ _
    rw [Affine.Point.add_some hxy', mapFun_some]
    congr 1
    · rw [hslope, haddX]
    · rw [hslope, haddY]

/-- `mapFun` as an additive homomorphism of point groups. -/
def mapPoint : W.toAffine.Point →+ (W.map φ).toAffine.Point where
  toFun := mapFun φ W
  map_zero' := rfl
  map_add' := mapFun_add φ W

/-- `mapPoint` on a coordinate point is the coordinate-wise image. -/
theorem mapPoint_some {x y : R} (h : W.toAffine.Nonsingular x y) :
    mapPoint φ W (.some x y h) = .some (φ x) (φ y) (nonsingular_map φ W h) := rfl

/-- The induced map on point groups is injective (the zero case and the coordinate case). -/
theorem mapPoint_injective : Function.Injective (mapPoint φ W) := by
  intro P Q hPQ
  rcases P with _ | ⟨x₁, y₁, h₁⟩ <;> rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · rfl
  · exact absurd hPQ.symm (Affine.Point.some_ne_zero _)
  · exact absurd hPQ (Affine.Point.some_ne_zero _)
  · have h := hPQ
    change Affine.Point.some (φ x₁) (φ y₁) _ = Affine.Point.some (φ x₂) (φ y₂) _ at h
    simp only [Affine.Point.some.injEq] at h
    obtain ⟨hx, hy⟩ := h
    cases φ.injective hx
    cases φ.injective hy
    rfl

/-- Coordinates of the mapped point: `Prod.map φ φ` of the coordinates, with `0 ↦ (0, 0)`. -/
theorem coordsOrZero_mapPoint (P : W.toAffine.Point) :
    (mapPoint φ W P).coordsOrZero = Prod.map φ φ P.coordsOrZero := by
  rcases P with _ | ⟨x, y, h⟩
  · show ((0 : S), (0 : S)) = (φ 0, φ 0)
    simp
  · rfl

/-- The order of a point is unchanged by the embedding. -/
theorem addOrderOf_mapPoint (P : W.toAffine.Point) :
    addOrderOf (mapPoint φ W P) = addOrderOf P :=
  addOrderOf_injective (mapPoint φ W) (mapPoint_injective φ W) P

/-- The odd-order summing set of the mapped point is the image of the original summing set
under `Prod.map φ φ`. -/
theorem oddOrderSummingSet_mapPoint (Q : W.toAffine.Point) (n : ℕ) :
    (W.map φ).oddOrderSummingSet (mapPoint φ W Q) n =
      (W.oddOrderSummingSet Q n).image (Prod.map φ φ) := by
  simp only [WeierstrassCurve.oddOrderSummingSet, Finset.image_image]
  refine Finset.image_congr fun k _ => ?_
  show (k • mapPoint φ W Q).coordsOrZero = Prod.map φ φ (k • Q).coordsOrZero
  rw [← map_nsmul, coordsOrZero_mapPoint]

end MapPoint

section Velu

variable {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (W : WeierstrassCurve R)

/-- `φ` commutes with the Vélu function `veluT`. -/
theorem map_veluT (x y : R) : φ (W.veluT x y) = (W.map φ).veluT (φ x) (φ y) := by
  simp [WeierstrassCurve.veluT, WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

/-- `φ` commutes with the Vélu function `veluW`. -/
theorem map_veluW (x y : R) : φ (W.veluW x y) = (W.map φ).veluW (φ x) (φ y) := by
  simp [WeierstrassCurve.veluW, WeierstrassCurve.veluU, WeierstrassCurve.veluT,
    WeierstrassCurve.veluGx, WeierstrassCurve.veluGy, map_ofNat]

variable [DecidableEq S]

/-- `φ` commutes with `veluTSum`, provided `φ × φ` is injective on the summing set. -/
theorem map_veluTSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluTSum T) = (W.map φ).veluTSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluTSum, WeierstrassCurve.veluTSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluT φ W P.1 P.2

/-- `φ` commutes with `veluWSum`, provided `φ × φ` is injective on the summing set. -/
theorem map_veluWSum (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    φ (W.veluWSum T) = (W.map φ).veluWSum (T.image (Prod.map φ φ)) := by
  rw [WeierstrassCurve.veluWSum, WeierstrassCurve.veluWSum, Finset.sum_image hφ, map_sum]
  exact Finset.sum_congr rfl fun P _ => map_veluW φ W P.1 P.2

/-- **Vélu commutes with the embedding**: the `φ`-image of the quotient of `W` by `T` is the
quotient of `W.map φ` by the image summing set (the pin's `Set.InjOn (Prod.map φ φ) T`). -/
theorem veluQuotient_map (T : Finset (R × R)) (hφ : Set.InjOn (Prod.map φ φ) T) :
    (W.veluQuotient T).map φ = (W.map φ).veluQuotient (T.image (Prod.map φ φ)) := by
  ext
  · rfl
  · rfl
  · rfl
  · show φ (W.a₄ - 5 * W.veluTSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₄, map_sub, map_mul, map_ofNat, map_veluTSum φ W T hφ]
    rfl
  · show φ (W.a₆ - W.b₂ * W.veluTSum T - 7 * W.veluWSum T) = _
    rw [WeierstrassCurve.veluQuotient_a₆, map_sub, map_sub, map_mul, map_mul, map_ofNat,
      map_veluTSum φ W T hφ, map_veluWSum φ W T hφ, ← WeierstrassCurve.map_b₂]
    rfl

end Velu

/-- Finitely many elements of an algebraically closed field are covered by a subfield that is
algebraically closed (`K₀`), i.e. `g` factors through an embedding `K₀ →+* F`.  The pin's
`IsAlgClosed`-only form; `exists_cover_hahn` adds the embedding into `𝕂`. -/
theorem exists_cover {F : Type uF} [Field F] [IsAlgClosed F] {m : ℕ} (g : Fin m → F) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : IsAlgClosed K₀) (φ : K₀ →+* F), ∀ i, g i ∈ Set.range φ := by
  classical
  let ev : MvPolynomial (Fin m) ℤ →+* F := MvPolynomial.eval₂Hom (Int.castRingHom F) g
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  let D : Type := MvPolynomial (Fin m) ℤ ⧸ RingHom.ker ev
  let ψ₁ : D →+* F := RingHom.kerLift ev
  have hψ₁ : Function.Injective ψ₁ := RingHom.kerLift_injective ev
  let L : Type := FractionRing D
  let ψ₂ : L →+* F := IsFractionRing.lift hψ₁
  let K₀ : Type := AlgebraicClosure L
  let _ : Algebra L F := ψ₂.toAlgebra
  have : Module.IsTorsionFree L F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact ψ₂.injective)
  let ψ₃ : K₀ →ₐ[L] F := IsAlgClosed.lift
  refine ⟨K₀, inferInstance, inferInstance, ψ₃.toRingHom, fun i => ?_⟩
  refine ⟨algebraMap L K₀ (algebraMap D L (Ideal.Quotient.mk (RingHom.ker ev) (MvPolynomial.X i))), ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  simp [ev]

/-- The fibre of `Φ` at `φ a` is the `φ`-image of the fibre at `a`. -/
theorem fibrePoly_map_ringHom {R S : Type*} [Field R] [Field S] (φ : R →+* S)
    (Φ : Polynomial (Polynomial ℤ)) (a : R) :
    fibrePoly Φ (φ a) = (fibrePoly Φ a).map φ := by
  have hcomp : Polynomial.eval₂RingHom (Int.castRingHom S) (φ a) =
      φ.comp (Polynomial.eval₂RingHom (Int.castRingHom R) a) := by
    refine Polynomial.ringHom_ext (fun z => ?_) ?_
    · simp
    · simp
  rw [fibrePoly, fibrePoly, hcomp, ← Polynomial.map_map]

/-- The pin's `Prop` packaging of the conclusion at the half-index shape `N = 2n+1`: the fibre
at `j(X)` is the product over the `j`-invariants of the odd Vélu quotients.  Its point is that
`conclT_map_iff` can rewrite it along `φ`. -/
def ConclT {F : Type*} [Field F] [DecidableEq F] (X : WeierstrassCurve F) [X.IsElliptic]
    {ι : Type*} [Fintype ι] (Q : ι → X.toAffine.Point) (n : ℕ)
    (hΔ : ∀ i, (X.veluQuotient (X.oddOrderSummingSet (Q i) n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) : Prop :=
  fibrePoly data.Φ X.j =
    ∏ i, (Polynomial.X - C (@WeierstrassCurve.j F _
      (X.veluQuotient (X.oddOrderSummingSet (Q i) n)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))

/-- `j` does not depend on the elliptic-curve structure proof, only on the curve. -/
theorem j_congr {F : Type*} [Field F] {A B : WeierstrassCurve F} (h : A = B)
    (hA : A.IsElliptic) (hB : B.IsElliptic) :
    @WeierstrassCurve.j F _ A hA = @WeierstrassCurve.j F _ B hB := by
  subst h
  rfl

section Transport

variable {R S : Type*} [Field R] [Field S] [DecidableEq R] [DecidableEq S] (φ : R →+* S)
  (V : WeierstrassCurve R)

/-- The odd Vélu quotient `W/⟨Q⟩` maps to the odd Vélu quotient of `W.map φ` at `mapPoint φ V Q`. -/
theorem veluQuotient_oddOrderSummingSet_mapPoint (Q : V.toAffine.Point) (n : ℕ) :
    (V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q) n) =
      (V.veluQuotient (V.oddOrderSummingSet Q n)).map φ := by
  rw [oddOrderSummingSet_mapPoint φ V Q n,
    veluQuotient_map φ V _ (Function.Injective.prodMap φ.injective φ.injective).injOn]

/-- The quotient `W/⟨Q⟩` is elliptic iff its image is (its discriminant is a unit/zero exactly
when the original's is). -/
theorem veluQuotient_mapPoint_Δ_ne_zero_iff (Q : V.toAffine.Point) (n : ℕ) :
    ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V Q) n)).Δ ≠ 0 ↔
      (V.veluQuotient (V.oddOrderSummingSet Q n)).Δ ≠ 0 := by
  rw [veluQuotient_oddOrderSummingSet_mapPoint, WeierstrassCurve.map_Δ, map_ne_zero_iff φ φ.injective]

variable [V.IsElliptic]

/-- **The conclusion transports along `φ`**: `ConclT` holds for `V.map φ` at the image family iff
it holds for `V` at the family (the fibres `Φ`-image and the products agree via
`fibrePoly_map_ringHom` and injectivity of `Polynomial.map`). -/
theorem conclT_map_iff {ι : Type*} [Fintype ι] (Q : ι → V.toAffine.Point) (n : ℕ)
    (hΔ : ∀ i, (V.veluQuotient (V.oddOrderSummingSet (Q i) n)).Δ ≠ 0)
    (hΔ' : ∀ i, ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n)).Δ ≠ 0)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    ConclT (V.map φ) (fun i => mapPoint φ V (Q i)) n hΔ' data ↔ ConclT V Q n hΔ data := by
  unfold ConclT
  have hj : ∀ i, @WeierstrassCurve.j S _
      ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n))
        ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩
      = φ (@WeierstrassCurve.j R _ (V.veluQuotient (V.oddOrderSummingSet (Q i) n))
          ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩) := by
    intro i
    have : (V.veluQuotient (V.oddOrderSummingSet (Q i) n)).IsElliptic :=
      ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩
    rw [j_congr (veluQuotient_oddOrderSummingSet_mapPoint φ V (Q i) n) ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩
      inferInstance, WeierstrassCurve.map_j]
  have hrhs : (∏ i, (Polynomial.X - C (@WeierstrassCurve.j S _
      ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (mapPoint φ V (Q i)) n))
        ⟨isUnit_iff_ne_zero.mpr (hΔ' i)⟩)))
      = (∏ i, (Polynomial.X - C (@WeierstrassCurve.j R _
          (V.veluQuotient (V.oddOrderSummingSet (Q i) n)) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩))).map φ := by
    rw [Polynomial.map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, hj i]
  rw [WeierstrassCurve.map_j, fibrePoly_map_ringHom, hrhs]
  exact (Polynomial.map_injective φ φ.injective).eq_iff

end Transport

section EmbedHahn

open Cardinal

/-- `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)` is uncountable: a `Set ℕ`-indexed family of series
with `0/1` coefficients is injective, so `#𝕂 ≥ #(Set ℕ) > ℵ₀`. -/
theorem aleph0_lt_mk_hahn : ℵ₀ < #(HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  classical
  let f : Set ℕ → HahnSeries ℚ (AlgebraicClosure ℚ) := fun S =>
    HahnSeries.ofPowerSeries ℚ (AlgebraicClosure ℚ) (PowerSeries.mk fun n => if n ∈ S then 1 else 0)
  have hf : Function.Injective f := by
    intro S T h
    have h' := HahnSeries.ofPowerSeries_injective h
    ext n
    have hn := congrArg (PowerSeries.coeff n) h'
    simp only [PowerSeries.coeff_mk] at hn
    by_cases hS : n ∈ S <;> by_cases hT : n ∈ T <;> simp_all
  calc ℵ₀ = #ℕ := Cardinal.mk_nat.symm
    _ < 2 ^ #ℕ := Cardinal.cantor _
    _ = #(Set ℕ) := (Cardinal.mk_set).symm
    _ ≤ #(HahnSeries ℚ (AlgebraicClosure ℚ)) := Cardinal.mk_le_of_injective hf

/-- Every countable field of characteristic zero embeds into `𝕂`: pick transcendence bases
`s` of `L` and `t` of `𝕂` (whose cardinality exceeds `ℵ₀`), embed `s ↪ t`, extend to an
embedding of the algebraic closures, and use `IsAlgClosed.lift`.  The `IsAlgClosed`-free pin
shape: `𝕂` is closed by `HahnSeries.isAlgClosed_rat`. -/
theorem nonempty_ringHom_hahn (L : Type) [Field L] [CharZero L] [Countable L] :
    Nonempty (L →+* HahnSeries ℚ (AlgebraicClosure ℚ)) := by
  classical
  have : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  have : CharZero (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    charZero_of_injective_ringHom (HahnSeries.C_injective (R := AlgebraicClosure ℚ) (Γ := ℚ))

  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ L
  obtain ⟨t, ht⟩ := exists_isTranscendenceBasis ℚ (HahnSeries ℚ (AlgebraicClosure ℚ))

  have hK : #(HahnSeries ℚ (AlgebraicClosure ℚ)) = #t := by
    simpa using IsAlgClosed.cardinal_eq_cardinal_transcendence_basis_of_aleph0_lt _ ht
      Cardinal.mk_le_aleph0 aleph0_lt_mk_hahn
  have hst : #s ≤ #t := by
    rw [← hK]
    exact (Cardinal.mk_le_aleph0.trans aleph0_lt_mk_hahn.le)
  obtain ⟨e⟩ : Nonempty (s ↪ t) := (Cardinal.le_def _ _).mp hst

  let w : s → HahnSeries ℚ (AlgebraicClosure ℚ) := fun x => ((e x : t) : HahnSeries ℚ (AlgebraicClosure ℚ))
  have hw : AlgebraicIndependent ℚ w := ht.1.comp _ e.injective

  let A : Subalgebra ℚ L := Algebra.adjoin ℚ (Set.range ((↑) : s → L))
  let A' : Subalgebra ℚ (HahnSeries ℚ (AlgebraicClosure ℚ)) := Algebra.adjoin ℚ (Set.range w)
  let ψ₁ : A →+* HahnSeries ℚ (AlgebraicClosure ℚ) :=
    (algebraMap A' (HahnSeries ℚ (AlgebraicClosure ℚ))).comp
      (hw.aevalEquiv.toRingEquiv.toRingHom.comp hs.1.aevalEquiv.symm.toRingEquiv.toRingHom)
  have hψ₁ : Function.Injective ψ₁ := by
    intro a b hab
    have h1 : ((hw.aevalEquiv (hs.1.aevalEquiv.symm a) : A') : HahnSeries ℚ (AlgebraicClosure ℚ))
        = (hw.aevalEquiv (hs.1.aevalEquiv.symm b) : A') := hab
    exact hs.1.aevalEquiv.symm.injective (hw.aevalEquiv.injective (Subtype.val_injective h1))

  have : Algebra.IsAlgebraic A L := hs.isAlgebraic
  let _ : Algebra A (HahnSeries ℚ (AlgebraicClosure ℚ)) := ψ₁.toAlgebra
  have : Module.IsTorsionFree A (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact hψ₁)
  have : Module.IsTorsionFree A L :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr Subtype.val_injective
  exact ⟨(IsAlgClosed.lift : L →ₐ[A] HahnSeries ℚ (AlgebraicClosure ℚ)).toRingHom⟩

/-- The working form of the cover: finitely many elements of `F` lie in the range of an embedding
`K₀ →+* F` from an algebraically closed `K₀` which *also* embeds into `𝕂`.  The field `K₀` is
`AlgebraicClosure` of the fraction field of a residue ring of `ℤ[X₁,…,X_m]`, hence countable and
of characteristic zero, so `nonempty_ringHom_hahn` applies. -/
theorem exists_cover_hahn {F : Type*} [Field F] [IsAlgClosed F] [CharZero F] {m : ℕ} (g : Fin m → F) :
    ∃ (K₀ : Type) (_ : Field K₀) (_ : IsAlgClosed K₀) (φ : K₀ →+* F)
      (_ : K₀ →+* HahnSeries ℚ (AlgebraicClosure ℚ)), ∀ i, g i ∈ Set.range φ := by
  classical
  let ev : MvPolynomial (Fin m) ℤ →+* F := MvPolynomial.eval₂Hom (Int.castRingHom F) g
  have : (RingHom.ker ev).IsPrime := RingHom.ker_isPrime ev
  let D : Type := MvPolynomial (Fin m) ℤ ⧸ RingHom.ker ev
  let ψ₁ : D →+* F := RingHom.kerLift ev
  have hψ₁ : Function.Injective ψ₁ := RingHom.kerLift_injective ev
  let L : Type := FractionRing D
  let ψ₂ : L →+* F := IsFractionRing.lift hψ₁
  let K₀ : Type := AlgebraicClosure L
  let _ : Algebra L F := ψ₂.toAlgebra
  have : Module.IsTorsionFree L F :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact ψ₂.injective)
  let ψ₃ : K₀ →ₐ[L] F := IsAlgClosed.lift

  have : CharZero L := ψ₂.charZero
  have : Countable (MvPolynomial (Fin m) ℤ) := Cardinal.mk_le_aleph0_iff.mp
    ((MvPolynomial.cardinalMk_le_max (σ := Fin m) (R := ℤ)).trans
      (max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl))
  have : Countable D := Quotient.countable
  have : Countable L := Cardinal.mk_le_aleph0_iff.mp
    ((Localization.cardinalMk_le (S := nonZeroDivisors D)).trans Cardinal.mk_le_aleph0)
  obtain ⟨χ⟩ := nonempty_ringHom_hahn L
  let _ : Algebra L (HahnSeries ℚ (AlgebraicClosure ℚ)) := χ.toAlgebra
  have : Module.IsTorsionFree L (HahnSeries ℚ (AlgebraicClosure ℚ)) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (by
      rw [RingHom.algebraMap_toAlgebra]; exact χ.injective)
  have : IsAlgClosed (HahnSeries ℚ (AlgebraicClosure ℚ)) := HahnSeries.isAlgClosed_rat
  let ψ₄ : K₀ →ₐ[L] HahnSeries ℚ (AlgebraicClosure ℚ) := IsAlgClosed.lift
  refine ⟨K₀, inferInstance, inferInstance, ψ₃.toRingHom, ψ₄.toRingHom, fun i => ?_⟩
  refine ⟨algebraMap L K₀ (algebraMap D L (Ideal.Quotient.mk (RingHom.ker ev) (MvPolynomial.X i))), ?_⟩
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes, RingHom.algebraMap_toAlgebra,
    IsFractionRing.lift_algebraMap, RingHom.kerLift_mk]
  simp [ev]

end EmbedHahn

section Assembly

/-- Transcendentality of `a` over `ℚ` is transported to `φ a` along an injective ring hom. -/
theorem transcendental_ringHom_iff {R S : Type*} [Field R] [Field S] [Algebra ℚ R] [Algebra ℚ S]
    (φ : R →+* S) (a : R) : Transcendental ℚ (φ a) ↔ Transcendental ℚ a := by
  have key : IsAlgebraic ℚ ((φ.toRatAlgHom : R →ₐ[ℚ] S) a) ↔ IsAlgebraic ℚ a :=
    isAlgebraic_algHom_iff (φ.toRatAlgHom) φ.injective
  exact not_congr (by simpa using key)

/-- **The assembly over a covered field.**  Given the cover `φ : K₀ →+* F` of the coefficients
and the coordinates of the `Q i`, plus the embedding `ψ : K₀ →+* 𝕂`, descend every point to
`K₀` (`mapPoint φ V`), run the transcendental node at `V.map ψ`, and transport back twice.
The hypotheses are stated on `V.map φ` so that the caller supplies them for its own `W` after
`V.map φ = W`. -/
theorem aux (K₀ : Type*) [Field K₀] [IsAlgClosed K₀]
    (ψ : K₀ →+* HahnSeries ℚ (AlgebraicClosure ℚ))
    {F : Type*} [Field F] [DecidableEq F] [CharZero F] [IsAlgClosed F]
    (φ : K₀ →+* F) (V : WeierstrassCurve K₀)
    {ι : Type*} [Fintype ι] (n : ℕ) [Fact (2 * n + 1).Prime] (hn2 : 2 * n + 1 ≠ 2)
    (hι : Fintype.card ι = 2 * n + 1 + 1)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) :
    ∀ (Q : ι → (V.map φ).toAffine.Point),
      (∀ i, (Q i).coordsOrZero.1 ∈ Set.range φ ∧ (Q i).coordsOrZero.2 ∈ Set.range φ) →
      ∀ (hE : (V.map φ).IsElliptic), Transcendental ℚ (@WeierstrassCurve.j F _ (V.map φ) hE) →
      (∀ i, addOrderOf (Q i) = 2 * n + 1) →
      (Function.Injective fun i => AddSubgroup.zmultiples (Q i)) →
      ∀ (hΔ : ∀ i, ((V.map φ).veluQuotient ((V.map φ).oddOrderSummingSet (Q i) n)).Δ ≠ 0),
      @ConclT F _ _ (V.map φ) hE ι _ Q n hΔ data := by
  classical
  intro Q hQr hE ht hord hinjQ hΔ
  have : CharZero K₀ := φ.charZero

  have hdesc : ∀ i, ∃ P₀ : V.toAffine.Point, mapPoint φ V P₀ = Q i := by
    intro i
    obtain ⟨hx, hy⟩ := hQr i
    rcases hQi : Q i with _ | ⟨x, y, h⟩
    · exact ⟨0, rfl⟩
    · rw [hQi] at hx hy
      obtain ⟨x₀, rfl⟩ := hx
      obtain ⟨y₀, rfl⟩ := hy
      exact ⟨Affine.Point.some x₀ y₀
        ((Affine.map_nonsingular (W := V.toAffine) (f := φ) φ.injective x₀ y₀).mp h), rfl⟩
  choose Q₀ hQ₀ using hdesc
  have hQfun : Q = fun i => mapPoint φ V (Q₀ i) := funext fun i => (hQ₀ i).symm
  subst hQfun

  have hV : V.IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr fun h0 => ?_⟩
    have h1 : (V.map φ).Δ = 0 := by rw [WeierstrassCurve.map_Δ, h0, map_zero]
    exact (isUnit_iff_ne_zero.mp (@WeierstrassCurve.isUnit_Δ _ _ (V.map φ) hE)) h1
  have ht₀ : Transcendental ℚ V.j := by
    rw [WeierstrassCurve.map_j] at ht
    exact (transcendental_ringHom_iff φ V.j).mp ht
  have hord₀ : ∀ i, addOrderOf (Q₀ i) = 2 * n + 1 := fun i => by
    rw [← addOrderOf_mapPoint φ V (Q₀ i)]; exact hord i
  have hinj₀ : Function.Injective fun i => AddSubgroup.zmultiples (Q₀ i) := by
    intro i i' h
    apply hinjQ
    simp only at h ⊢
    rw [← AddMonoidHom.map_zmultiples, ← AddMonoidHom.map_zmultiples, h]
  have hΔ₀ : ∀ i, (V.veluQuotient (V.oddOrderSummingSet (Q₀ i) n)).Δ ≠ 0 := fun i =>
    (veluQuotient_mapPoint_Δ_ne_zero_iff φ V (Q₀ i) n).mp (hΔ i)

  have hΔ₁ : ∀ i, ((V.map ψ).veluQuotient ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) n)).Δ ≠ 0 :=
    fun i => (veluQuotient_mapPoint_Δ_ne_zero_iff ψ V (Q₀ i) n).mpr (hΔ₀ i)
  have ht₁ : Transcendental ℚ (V.map ψ).j := by
    rw [WeierstrassCurve.map_j]; exact (transcendental_ringHom_iff ψ V.j).mpr ht₀
  have hord₁ : ∀ i, addOrderOf (mapPoint ψ V (Q₀ i)) = 2 * n + 1 := fun i => by
    rw [addOrderOf_mapPoint]; exact hord₀ i
  have hinj₁ : Function.Injective fun i => AddSubgroup.zmultiples (mapPoint ψ V (Q₀ i)) := by
    intro i i' h
    apply hinj₀
    simp only at h ⊢
    rw [← AddMonoidHom.map_zmultiples, ← AddMonoidHom.map_zmultiples] at h
    exact AddSubgroup.map_injective (mapPoint_injective ψ V) h
  have hn : (2 * n + 1) / 2 = n := by omega

  have G0 : ∀ (hΔm : ∀ i, ((V.map ψ).veluQuotient
        ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) ((2 * n + 1) / 2))).Δ ≠ 0),
      fibrePoly data.Φ (V.map ψ).j =
        ∏ i, (Polynomial.X - C (@WeierstrassCurve.j _ _
          ((V.map ψ).veluQuotient ((V.map ψ).oddOrderSummingSet (mapPoint ψ V (Q₀ i)) ((2 * n + 1) / 2)))
          ⟨isUnit_iff_ne_zero.mpr (hΔm i)⟩)) :=
    fun hΔm => ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental
      hn2 data (V.map ψ) ht₁ hι (fun i => mapPoint ψ V (Q₀ i)) hord₁ hinj₁ hΔm
  rw [hn] at G0
  have G' : ConclT (V.map ψ) (fun i => mapPoint ψ V (Q₀ i)) n hΔ₁ data := G0 hΔ₁

  have H₀ : ConclT V Q₀ n hΔ₀ data := (conclT_map_iff ψ V Q₀ n hΔ₀ hΔ₁ data).mp G'
  exact (conclT_map_iff φ V Q₀ n hΔ₀ hΔ data).mpr H₀

/-- The half-index assembly at `N = 2n+1`: cover the five coefficients of `W` and the two
coordinates of each `Q i` by `exists_cover_hahn`, rebuild `W` as `V.map φ` (`V` over `K₀`), and
read the conclusion at `W` from `aux`. -/
theorem main {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    (n : ℕ) [Fact (2 * n + 1).Prime] (hn2 : 2 * n + 1 ≠ 2)
    (data : ModularCurve.ModularPolynomialData (2 * n + 1)) (W : WeierstrassCurve K) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 2 * n + 1 + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) n)).Δ ≠ 0) :
    ConclT W Q n hΔ data := by
  classical

  obtain ⟨e⟩ : Nonempty (ι ≃ Fin (Fintype.card ι)) := ⟨Fintype.equivFin ι⟩
  let g : Fin (5 + 2 * Fintype.card ι) → K := fun k =>
    Fin.addCases (![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆])
      (fun k' : Fin (2 * Fintype.card ι) =>
        if k'.val % 2 = 0 then (Q (e.symm ⟨k'.val / 2, by omega⟩)).coordsOrZero.1
        else (Q (e.symm ⟨k'.val / 2, by omega⟩)).coordsOrZero.2) k
  obtain ⟨K₀, _, _, φ, ψ, hg⟩ := exists_cover_hahn g
  obtain ⟨b₁, hb₁⟩ := hg (Fin.castAdd _ 0)
  obtain ⟨b₂, hb₂⟩ := hg (Fin.castAdd _ 1)
  obtain ⟨b₃, hb₃⟩ := hg (Fin.castAdd _ 2)
  obtain ⟨b₄, hb₄⟩ := hg (Fin.castAdd _ 3)
  obtain ⟨b₆, hb₆⟩ := hg (Fin.castAdd _ 4)
  have hcoord : ∀ i, (Q i).coordsOrZero.1 ∈ Set.range φ ∧ (Q i).coordsOrZero.2 ∈ Set.range φ := by
    intro i
    constructor
    · have := hg (Fin.natAdd 5 ⟨2 * (e i).val, by omega⟩)
      simpa [g, Fin.addCases, Nat.mul_mod_right, Nat.mul_div_right] using this
    · have := hg (Fin.natAdd 5 ⟨2 * (e i).val + 1, by omega⟩)
      simpa [g, Fin.addCases, Nat.mul_add_mod, Nat.mul_add_div] using this
  let V : WeierstrassCurve K₀ := ⟨b₁, b₂, b₃, b₄, b₆⟩
  have hW : V.map φ = W := by
    ext
    · simpa [g, Fin.addCases] using hb₁
    · simpa [g, Fin.addCases] using hb₂
    · simpa [g, Fin.addCases] using hb₃
    · simpa [g, Fin.addCases] using hb₄
    · simpa [g, Fin.addCases] using hb₆
  have key : ∀ (Q' : ι → W.toAffine.Point),
      (∀ i, (Q' i).coordsOrZero.1 ∈ Set.range φ ∧ (Q' i).coordsOrZero.2 ∈ Set.range φ) →
      ∀ (hE : W.IsElliptic), Transcendental ℚ (@WeierstrassCurve.j K _ W hE) →
      (∀ i, addOrderOf (Q' i) = 2 * n + 1) →
      (Function.Injective fun i => AddSubgroup.zmultiples (Q' i)) →
      ∀ (hΔ' : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q' i) n)).Δ ≠ 0),
      @ConclT K _ _ W hE ι _ Q' n hΔ' data := by
    rw [← hW]
    exact aux K₀ ψ φ V n hn2 hι data
  exact key Q hcoord inferInstance ht hQ hQinj hΔ

end Assembly

end TDescent

end Descent

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine in
/-- **The fibre product form at an arbitrary algebraically closed field.**  Descend the
product form to `K` along the embedding into `HahnSeries ℚ (AlgebraicClosure ℚ)`.
Verbatim from
`Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed.lean`. -/
theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] [CharZero K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    (ht : Transcendental ℚ W.j)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  have hℓP : ℓ.Prime := Fact.out
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = 2 * n + 1 := by
    rcases hℓP.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · exact h
  have hn : (2 * n + 1) / 2 = n := by omega
  revert hΔ
  rw [hn]
  intro hΔ
  exact TDescent.main n hℓ2 data W ht hι Q hQ hQinj hΔ

end
