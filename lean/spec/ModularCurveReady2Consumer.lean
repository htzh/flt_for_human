/-
  Consumer specification for **ready shelf 2** — the `ModularCurve` residue's orders B and C.
  Written-down *uses* of the wave's headlines, composed across modules. Not part of any library;
  run by hand:

      cd lean
      timeout 300 lake env lean -DmaxHeartbeats=4000000 spec/ModularCurveReady2Consumer.lean 2>&1 | grep -c error

  ZONES
  -----
    [coset] ZONE B — order B's two rows consumed. The coset-root row is fed to the descent row
            `forall_isRoot_cosetConj_jqModC_of_complex`, which is exactly how the pin uses it
            (the roots over `ℂ` become roots over any field); and the level-two `fibrePoly` row
            is instantiated at a data package produced by `nonempty_modularPolynomialData`,
            i.e. at `Φ₂ = data.Φ` rather than at the pin's `phiTwo`.
    [constExt] ZONE C — order C's two rows consumed. The `coeffMap`/`qMap` transfer of C1 is read
            as a membership plus a generation statement, and C2's fullness of `laurentBaseChange`
            is composed with `coeffEmb_ne_zero_iff` so that a nonzero source series survives into
            the base-changed field.

    [siegelProd] ZONE A — order A's row consumed, with its witness `(C, d)` kept and fed to
            `SiegelUnit/Basic`'s product law: for `e` periodic in `s` the numerator of the row's
            summand product is `Γ₁(N)`-invariant, so the row's coefficient series is the same at
            `γ • τ`; and the row is instantiated at `N = 1`, where `d 0 = 1`.
    [special] ZONE D — order D's row read through the place dictionary of `LevelN/Places`: the
            dictionary that turns an analytic order at a point of `ℍ` into the order of `jK` at a
            place, and the row's three bounds, both at an arbitrary `τ₀`; plus the two elliptic
            bounds rewritten at the values they realise (`j(i) = 1728`, `j(ρ) = 0`) with the
            stabiliser-cardinality bounds, which is the form a fibre-lower-bound consumer reads.

-/

import FLTForHuman.ModularCurve.ModularPolynomialCoset
import FLTForHuman.ModularCurve.ModularPolynomialFibreTwo
import FLTForHuman.ModularCurve.X1.FunctionFieldConstExt
import FLTForHuman.ModularCurve.LevelN.SpecialRamification
import FLTForHuman.ModularCurve.FunctionFieldGeneration.ModularPolynomialExistence
import FLTForHuman.ModularCurve.SiegelUnit.Integrality

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups UpperHalfPlane

namespace Ready2Consumer

/-! ## Zone B — `[coset]` the coset roots and the level-two fibre -/

/-- Order B's coset-root row, read through the descent row of the same module: a primitive root
over `ℂ` for `Φ_N(data)` gives, for every field `K` and every primitive `N`-th root `ζ` in `K`, the
root property for `Φ_N(data)` evaluated at `jqModC K`.  This is precisely the shape the pin's
`splitting` rows consume. -/
theorem coset_roots_over_field (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) (K : Type*) [Field K]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ N) :
    ∀ t ∈ ModularCurve.primCosetReps N,
      (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries K))
        (ModularCurve.qExpand K N (ModularCurve.jqModC K)))).IsRoot
        (ModularCurve.cosetConj ζ (ModularCurve.jqModC K) t) :=
  ModularCurve.ModularPolynomialData.forall_isRoot_cosetConj_jqModC_of_complex N data
    (ModularCurve.ModularPolynomialData.exists_isPrimitiveRoot_forall_isRoot_cosetConj_complex N data)
    K ζ hζ

/-- Order B's fibre row at an *arbitrary* level-two data package, not at the pin's `phiTwo`: the
`Φ₂ = data.Φ` identification (`phi_eq_phiTwo`) is absorbed into the fibre identity.  The data
package is the one `nonempty_modularPolynomialData` produces. -/
theorem fibrePoly_j_eq_prod_veluQuotient2_j_of_data
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularCurve.ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    ModularCurve.fibrePoly data.Φ W.j =
      ∏ i, (Polynomial.X - Polynomial.C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  data.fibrePoly_j_eq_prod_veluQuotient2_j h2 W hι P hP hPeq hPgy hΔ

/-- … and instantiated at the data package the port's own nonemptiness row supplies, which is the
statement a consumer outside this wave actually sees. -/
theorem fibrePoly_j_eq_prod_veluQuotient2_j_capstone
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    ModularCurve.fibrePoly
        (Classical.choice (ModularCurve.nonempty_modularPolynomialData 2)).Φ W.j =
      ∏ i, (Polynomial.X - Polynomial.C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) :=
  fibrePoly_j_eq_prod_veluQuotient2_j_of_data h2
    (Classical.choice (ModularCurve.nonempty_modularPolynomialData 2)) W hι P hP hPeq hPgy hΔ

/-! ## Zone C — `[constExt]` the constant extension of the `q`-expansion function field -/

/-- Order C's transfer engine in the two halves a consumer needs: the `coeffMap` image of the
source field lands in the target field, and the target is generated over the constants by the
image of the source (`qMap`). -/
theorem coeffMap_image_generates {K₀ K : Type*} [Field K₀] [Field K] (φ : K₀ →+* K)
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (x : ModularCurve.qExpFunctionFieldC K₀ Γ) :
    (ModularCurve.coeffMap φ (x : LaurentSeries K₀) ∈ ModularCurve.qExpFunctionFieldC K Γ) ∧
      ModularCurve.qExpFunctionFieldC K Γ ≤
        (IntermediateField.adjoin K (Set.range (ModularCurve.QExpConstExt.qMap φ Γ))).map
          (ModularCurve.qExpFunctionFieldC K Γ).val :=
  ⟨ModularCurve.QExpAutBaseChange.coeffMap_mem φ Γ x.2,
    ModularCurve.QExpConstExt.le_map_adjoin_range φ Γ⟩

/-- Order C's second row, in the form its successors consume: `laurentBaseChange` of
`qExpFunctionFieldC ℚ Γ` is the whole target field, and a nonzero source series stays nonzero
there (`coeffEmb_ne_zero_iff`). -/
theorem laurentBaseChange_full_and_ne_zero (K : Type*) [Field K] [Algebra ℚ K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {x : LaurentSeries ℚ} (hx : x ≠ 0) :
    ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ) =
        ModularCurve.qExpFunctionFieldC K Γ ∧
      ModularCurve.coeffEmb K x ≠ 0 :=
  ⟨ModularCurve.laurentBaseChange_qExpFunctionFieldC_eq K Γ,
    (ModularCurve.FullnessGamma1.coeffEmb_ne_zero_iff K x).mpr hx⟩

/-- … and the finiteness half of the same row, at a generator of the base-changed field: the
relative degree of `K⟮y⟯` over the base-changed field is the `K`-degree of the adjoin of `y`,
so `finrank_adjoin_eq_relfinrank` transports the pin's index bound to either side. -/
theorem finrank_adjoin_transfer (K : Type*) [Field K] [Algebra ℚ K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))) :
    Module.finrank
        ↥(IntermediateField.adjoin K
          ({y} : Set ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) =
      (IntermediateField.adjoin K ({(y : LaurentSeries K)} : Set (LaurentSeries K))).relfinrank
        (ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) :=
  ModularCurve.FullnessGamma1.finrank_adjoin_eq_relfinrank _ y

/-! ## Zone D — `[special]` the special places of `X(N)`, through the place dictionary -/

/-- Order D's row composed with the dictionary it is derived through: at a fraction field `K` of
the level-`N` ring and any `τ₀ : ℍ`, `LevelN.exists_place_analyticOrderAt_eq_mul_ord` gives a place
`W` with a positive index `e` and the order of every nonzero element of the ring read off the
analytic order at `τ₀`, and the row gives the three special places of `j`. -/
theorem special_places_and_order_dictionary (N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : ℍ) :
    (∃ (W : AlgebraicCurve.Place ℂ K) (e : ℕ), 0 < e ∧
        ∀ (F : ℍ → ℂ) (hF : F ∈ ModularCurve.LevelN.ring N), F ≠ 0 →
          analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ) ≠ ⊤ ∧
            ↑(analyticOrderAt (F ∘ UpperHalfPlane.ofComplex) (τ₀ : ℂ)).toNat =
              ↑e * W.ord (algebraMap (ModularCurve.LevelN.ring N) K ⟨F, hF⟩)) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) - 1728) ≤ 2) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ∧
          W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) ≤ 3) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
          -(N : ℤ) ≤ W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N))) := by
  obtain ⟨h1, h2, h3⟩ := ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level N K
  exact ⟨ModularCurve.LevelN.exists_place_analyticOrderAt_eq_mul_ord N K τ₀, h1, h2, h3⟩

/-- The same row at an arbitrary `τ₀` against the cusp bound: the elliptic bound is
`|Stab(τ₀)| / 2` at `j - j(τ₀)` (the form the `j`-fibre rows consume, with `τ₀ = i` and
`τ₀ = ρ` the two cases the row states as `1728` and `0`), and the cusp bound is the row's
third conjunct. -/
theorem ord_jsub_tau0_and_cusp (N : ℕ) [NeZero N] (K : Type*) [Field K]
    [Algebra ℂ K] [Algebra (ModularCurve.LevelN.ring N) K]
    [IsScalarTower ℂ (ModularCurve.LevelN.ring N) K]
    [IsFractionRing (ModularCurve.LevelN.ring N) K] (τ₀ : ℍ) :
    (∃ W : AlgebraicCurve.Place ℂ K,
        0 < W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) -
          algebraMap ℂ K (ModularCurve.LevelN.jAnalytic τ₀)) ∧
      W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N) -
          algebraMap ℂ K (ModularCurve.LevelN.jAnalytic τ₀)) ≤
        (Nat.card (MulAction.stabilizer SL(2, ℤ) τ₀) / 2 : ℕ)) ∧
      (∃ W : AlgebraicCurve.Place ℂ K,
        W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N)) < 0 ∧
          -(N : ℤ) ≤ W.ord (algebraMap (ModularCurve.LevelN.ring N) K (ModularCurve.LevelN.jGen N))) :=
  ⟨ModularCurve.LevelN.SpecialRamification.exists_place_ord_sub_le N K τ₀,
    (ModularCurve.LevelN.exists_place_ord_jGen_le_two_three_level N K).2.2⟩

end Ready2Consumer

/-! ## Zone A — the Siegel product (order A)

The product row run once, its witness kept, and composed with `SiegelUnit/Basic`'s product law;
then instantiated at `N = 1`, where the constant term collapses to `1`. -/

namespace Ready2ConsumerA

/-- Order A's row, with its witness kept: the product row supplies `(C, d)` with `C ^ N = 1`,
every coefficient of `d` integral over `ℤ`, nonzero constant term `d 0`, the `HasSum` of the
product at every `τ`, and the `Γ₁(N)`-invariance of the product (the product law of
`SiegelUnit/Basic`), so that the row's coefficient series is the same at `γ • τ`. -/
theorem siegelProd_slash_Gamma1 (N : ℕ) [NeZero N] (e : ZMod N → ZMod N → ℕ) (he : e 0 0 = 0)
    (hper : ∀ r s : ZMod N, e r (s + r) = e r s) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ N = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧ d 0 ≠ 0 ∧
      (∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, γ ∈ CongruenceSubgroup.Gamma1 N →
        ∀ τ : UpperHalfPlane,
          (∏ r : ZMod N, ∏ s : ZMod N,
              ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ)
                ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) =
            ∏ r : ZMod N, ∏ s : ZMod N,
              ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * N * e r s) ∧
          HasSum
            (fun n : ℕ => d n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) *
              ((γ • τ : UpperHalfPlane) : ℂ) / (N : ℂ)))
            ((∏ r : ZMod N, ∏ s : ZMod N,
                ModularCurve.siegelFun N (r.val : ℤ) (s.val : ℤ)
                  ((γ • τ : UpperHalfPlane) : ℂ) ^ (12 * N * e r s)) /
              (C * Complex.exp (2 * Real.pi * Complex.I *
                ((∑ r : ZMod N, ∑ s : ZMod N,
                    (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) +
                      (N : ℤ) ^ 2)) : ℂ) * ((γ • τ : UpperHalfPlane) : ℂ) / (N : ℂ))))) := by
  obtain ⟨C, d, hC, hdint, _hd0, hd0ne, _hinv, hHas, _hTend⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow N e he
  refine ⟨C, d, hC, hdint, hd0ne, fun γ hγ τ => ⟨?_, hHas (γ • τ)⟩⟩
  exact (ModularCurve.SiegelUnit.prod_siegelFun_pow_specialLinearGroup_smul N e).2 hper γ hγ τ

/-- Order A's row at `N = 1`: the constant term is `1` — the product `∏ s, (1 - exp …) ^ (12 e 0 s)`
collapses because `ZMod 1` is a singleton and `e 0 0 = 0` — so the cusp value of the product is
`1`, and the row's per-coefficient integrality is the integrality of this series. -/
theorem siegelProd_cusp_value_level_one (e : ZMod 1 → ZMod 1 → ℕ) (he : e 0 0 = 0) :
    ∃ (C : ℂ) (d : ℕ → ℂ), C ^ 1 = 1 ∧ (∀ n : ℕ, IsIntegral ℤ (d n)) ∧ d 0 = 1 ∧
      Filter.Tendsto
        (fun τ : UpperHalfPlane =>
          (∏ r : ZMod 1, ∏ s : ZMod 1,
              ModularCurve.siegelFun 1 (r.val : ℤ) (s.val : ℤ) (τ : ℂ) ^ (12 * 1 * e r s)) /
            (C * Complex.exp (2 * Real.pi * Complex.I *
              ((∑ r : ZMod 1, ∑ s : ZMod 1,
                  (e r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (1 : ℤ) * (r.val : ℤ) +
                    (1 : ℤ) ^ 2)) : ℂ) * (τ : ℂ) / (1 : ℂ))))
        UpperHalfPlane.atImInfty (nhds 1) := by
  obtain ⟨C, d, hC, hdint, hd0, hd0ne, _hinv, _hHas, hTend⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_prod_siegelFun_pow 1 e he
  have hd1 : d 0 = 1 := by
    rw [hd0]
    refine Finset.prod_eq_one fun s _ => ?_
    have hs : s = 0 := Subsingleton.elim s 0
    rw [hs, he]
    simp
  refine ⟨C, d, hC, hdint, hd1, ?_⟩
  simpa only [hd1, Nat.cast_one] using hTend

end Ready2ConsumerA

