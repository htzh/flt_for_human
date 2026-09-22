/-
  T9 — the integrality of the descended coefficients.

  This is the first half of the cone's piece (b): the descended family
  `c : ℕ → LaurentSeries ℚ` of `phiProd` has **integer** `q`-expansion
  coefficients (`PhiGenDescends.intCoeffs`), and consequently a polynomial
  `P ∈ ℚ[X]` with `IntCoeffs (aeval jq P)` already lies in `ℤ[X]`
  (`aeval_jq_intCoeffs_descent`). Together they are what (d)'s
  `exists_modularPolynomialData_coeff_eq` needs to build an element of
  `ℤ[X][Y]`.

  ## Route A shipped (the deviation from FLT's script)

  FLT proves the first statement coefficientwise: it defines
  `CoeffsIntegral f := ∀ m, f.coeff m ∈ integralClosure ℤ K` and proves it is
  closed under `0, 1, -, *, qExpand, qTwist` (six lemmas), then reads the
  integrality of `(phiProd …).coeff k` off three polynomial-coefficient lemmas
  (`coeffsIntegral_coeff_X_sub_C`, `_mul`, `_prod`, ~42 lines). This port takes
  the route the work order calls **Route A**:

  * lift `jq` to `jqZ : LaurentSeries ℤ` (its coefficients are the
    `jNum : PowerSeries ℤ` coefficients, by construction) and then to
    `jqO : LaurentSeries (integralClosure ℤ K)`;
  * lift the conjugate family to `conjO i : LaurentSeries (integralClosure ℤ K)`
    using a unit `zetaUnit e : (integralClosure ℤ K)ˣ` lifting `ζ ^ e`;
  * `coeffMap (algebraMap 𝒪 K) : LaurentSeries 𝒪 →+* LaurentSeries K` is a ring
    hom, so it pushes through `qExpand` (`coeffMap_qExpand`, already public),
    through `qTwist` (`coeffMap_qTwist`, new) and through the polynomial product
    `phiProd` (`map_phiProdO`); every coefficient of the `K`-series is therefore
    an `𝒪`-multiple, hence integral;
  * the descent `hc` plus injectivity of `coeffEmb` produces the integer.

  The measured payoff is in `logs/phiGen-port.md` §9: the ~83 lines of FLT's
  `CoeffsIntegral` closure and polynomial-coefficient machinery are replaced by
  ~90 lines of bridging lemmas, and the 24 lines of manual root-of-unity
  integrality by one generic `mem_integralClosure_of_pow_eq_one` over `X ^ ℓ - 1`.

  **Deviation from the work order's letter.** `poleOrderLE_aeval_jq` could not be
  promoted into `Defs/Jq.lean` (it needs `PoleOrderLE`, defined in
  `Defs/PhiGen.lean`, which imports `Defs/Jq.lean`); it was promoted into
  `Defs/PhiGen.lean` instead, and `coeff_aeval_jq_neg` into `Defs/Jq.lean`. The
  pin's public copy of both is
  `P2M/Sol/S_ModularCurve_exists_aeval_jq_sub_holomorphicAtInfty.lean`.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:

  - `P2M/Sol/S_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean` (239) — the
    product's integrality;
  - `P2M/Sol/S_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean` (308, of
    which ~108 is the descent and ~180 a duplicated `TPoleOrderLE` block that
    belongs to the pole-bound topic and is **not** ported here).

  The two public statements are verbatim from their `Theorems/` wrappers.

  ## Assumptions

  `LaurentSeries`, `HahnSeries`, `PowerSeries`, `Polynomial`, `integralClosure`,
  `IsIntegrallyClosed.isIntegral_iff` and `mem_integralClosure_iff` are mathlib's;
  `IntCoeffs`, `PhiGenDescends`, `conj`, `phiProd` are the port's `Defs/PhiGen`
  and `jq`, `jq_pow`, `coeff_jq_pow_self`, `coeff_jq_pow_of_lt`, `jNum`,
  `jNumQ`, `coeff_aeval_jq_neg` the port's `Defs/Jq`; `coeffMap`,
  `coeffEmb`, `coeffMap_coeff`, `coeffMap_qExpand`, `ofPowerSeries_coeff_of_neg`
  the port's `Defs/Laurent`/`Defs/Jq`. Names are FLT's verbatim where the pin has
  them.
-/
import FLTForHuman.ModularCurve.Defs.PhiGen

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries IntermediateField Polynomial

namespace ModularCurve
namespace PhiGen

variable {K : Type*} [Field K] [Algebra ℚ K]

/-! ## Bridging `coeffMap` to `HahnSeries.ofPowerSeries` and `qTwist`

`jq` is built from `jNum : PowerSeries ℤ` through `HahnSeries.ofPowerSeries`; the
`𝒪`-lift has to commute `coeffMap` with that embedding and with the unit twist.
Both are coefficientwise computations. -/

/-- `jq` lifted to `LaurentSeries ℤ`: its coefficients are `jNum`'s. -/
private def jqZ : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ jNum

private theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (x : PowerSeries R) :
    coeffMap f (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (x.map f) := by
  ext m
  rcases lt_or_ge m 0 with hm | hm
  · rw [coeffMap_coeff, ofPowerSeries_coeff_of_neg _ hm, map_zero,
      ofPowerSeries_coeff_of_neg _ hm]
  · have hcast : m = (((m.toNat : ℕ)) : ℤ) := (Int.toNat_of_nonneg hm).symm
    rw [hcast]
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_map]

/-! `coeffMap_qTwist` was this module's `private` 3-argument transport copy; T16
promoted the canonical 5-argument form (with the explicit `v`/`huv`) to
`Defs/Twist.lean`, which this module imports transitively through `Defs/PhiGen`.
The one call site below now names the public lemma explicitly. -/

private theorem coeffMap_jqZ : coeffMap (algebraMap ℤ K) jqZ = coeffEmb K jq := by
  have hcomp : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = algebraMap ℤ K :=
    Subsingleton.elim _ _
  change coeffMap (algebraMap ℤ K) (HahnSeries.single (-1 : ℤ) 1 *
      HahnSeries.ofPowerSeries ℤ ℤ jNum)
    = coeffMap (algebraMap ℚ K) (HahnSeries.single (-1 : ℤ) 1 *
        HahnSeries.ofPowerSeries ℤ ℚ jNumQ)
  rw [map_mul, map_mul, coeffMap_single, coeffMap_single, map_one (algebraMap ℤ K),
    map_one (algebraMap ℚ K), coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, jNumQ,
    show (PowerSeries.map (algebraMap ℚ K)) ((PowerSeries.map (Int.castRingHom ℚ)) jNum)
      = PowerSeries.map ((algebraMap ℚ K).comp (Int.castRingHom ℚ)) jNum from rfl,
    hcomp]

/-! ## The `𝒪`-lift of the conjugate family

`ζ ^ e` is a root of `X ^ ℓ - 1`, hence integral; so is its inverse, and together
they are a unit of `integralClosure ℤ K` mapping to `ζ ^ e` in `K`. -/

omit [Algebra ℚ K] in
private theorem mem_integralClosure_of_pow_eq_one {n : ℕ} (hn : n ≠ 0) {x : K}
    (hx : x ^ n = 1) : x ∈ integralClosure ℤ K := by
  rw [mem_integralClosure_iff]
  exact ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 hn, by simp [hx]⟩

variable {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]

/-- The unit of `integralClosure ℤ K` lifting `ζ ^ e`, for `ζ ^ ℓ = 1`. -/
private def zetaUnit (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (e : ℕ) :
    (integralClosure ℤ K)ˣ :=
  let u : Kˣ := ζ ^ e
  have hu : u ^ ℓ = 1 := by
    rw [← pow_mul, mul_comm e ℓ, pow_mul, hζ1, one_pow]
  have hval : (u : K) ^ ℓ = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  have hinv : ((u⁻¹ : Kˣ) : K) ^ ℓ = 1 := by
    rw [Units.val_inv_eq_inv_val, inv_pow, hval, inv_one]
  Units.mkOfMulEqOne
    ⟨(u : K), mem_integralClosure_of_pow_eq_one hℓ.out.ne_zero hval⟩
    ⟨((u⁻¹ : Kˣ) : K), mem_integralClosure_of_pow_eq_one hℓ.out.ne_zero hinv⟩
    (by ext; simp)

omit [Algebra ℚ K] in
private theorem coeffMap_zetaUnit (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (e : ℕ) :
    Units.map (algebraMap (integralClosure ℤ K) K).toMonoidHom (zetaUnit ζ hζ1 e)
      = ζ ^ e := by
  ext
  simp [zetaUnit]

/-- The `𝒪`-lift of `jq`. -/
private def jqO : LaurentSeries (integralClosure ℤ K) :=
  coeffMap (algebraMap ℤ (integralClosure ℤ K)) jqZ

private theorem coeffMap_jqO :
    coeffMap (algebraMap (integralClosure ℤ K) K) jqO = coeffEmb K jq := by
  rw [jqO, coeffMap_coeffMap, coeffMap_congr (Subsingleton.elim _ _), coeffMap_jqZ]

/-- The `𝒪`-lift of the conjugate family. -/
private def conjO (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    LaurentSeries (integralClosure ℤ K) :=
  qExpand (integralClosure ℤ K) (cosetA ℓ i * cosetA ℓ i)
    (qTwist (zetaUnit ζ hζ1 (cosetA ℓ i * cosetB ℓ i)) jqO)

private theorem coeffMap_conjO (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) (i : Fin (ℓ + 1)) :
    coeffMap (algebraMap (integralClosure ℤ K) K) (conjO ζ hζ1 i) = conj ℓ ζ i := by
  rw [conjO, coeffMap_qExpand,
    coeffMap_qTwist (algebraMap (integralClosure ℤ K) K)
      (zetaUnit ζ hζ1 (cosetA ℓ i * cosetB ℓ i))
      (Units.map (algebraMap (integralClosure ℤ K) K).toMonoidHom
        (zetaUnit ζ hζ1 (cosetA ℓ i * cosetB ℓ i))) rfl,
    coeffMap_jqO, coeffMap_zetaUnit]
  unfold conj cosetSubst
  rw [RingHom.comp_apply]

/-- The `𝒪`-lift of the product `∏_i (Y - conj i)`. `phiProd` is stated for a
field, so the lift is the bare product over the (non-field) integral closure. -/
private def phiProdO (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) :
    Polynomial (LaurentSeries (integralClosure ℤ K)) :=
  ∏ i : Fin (ℓ + 1), (Polynomial.X - Polynomial.C (conjO ζ hζ1 i))

private theorem map_phiProdO (ζ : Kˣ) (hζ1 : ζ ^ ℓ = 1) :
    Polynomial.map (coeffMap (algebraMap (integralClosure ℤ K) K)) (phiProdO ζ hζ1)
      = phiProd ℓ (conj ℓ ζ) := by
  rw [phiProdO, phiProd]
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, coeffMap_conjO]

/-! ## The integrality of the descended family -/

private theorem exists_intCast_eq_of_mem {q : ℚ}
    (h : algebraMap ℚ K q ∈ integralClosure ℤ K) : ∃ z : ℤ, q = (z : ℚ) := by
  rw [mem_integralClosure_iff] at h
  obtain ⟨P, hPmonic, hPeval⟩ := h
  have hcomp : algebraMap ℤ K = (algebraMap ℚ K).comp (Int.castRingHom ℚ) :=
    Subsingleton.elim _ _
  rw [hcomp, ← Polynomial.hom_eval₂] at hPeval
  have h0 : Polynomial.eval₂ (Int.castRingHom ℚ) q P = 0 :=
    FaithfulSMul.algebraMap_injective ℚ K (by rw [hPeval, map_zero])
  have hint : IsIntegral ℤ q :=
    ⟨P, hPmonic, by
      rwa [show algebraMap ℤ ℚ = Int.castRingHom ℚ from Subsingleton.elim _ _]⟩
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  exact ⟨z, by rw [← hz]; simp⟩

variable {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}

/-- The descended coefficients of `phiProd` have integer `q`-expansion
coefficients. Verbatim from the pin wrapper
`Theorems/Thm_ModularCurve_PhiGen_PhiGenDescends_intCoeffs.lean`. -/
theorem PhiGenDescends.intCoeffs {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ}
    [hℓ : Fact (Nat.Prime ℓ)] {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ}
    (hc : PhiGenDescends ℓ ζ c) (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : IntCoeffs (c k) := by
  intro m
  have h1 : algebraMap ℚ K ((c k).coeff m)
      = ((phiProd ℓ (conj ℓ ζ)).coeff k).coeff ((ℓ : ℤ) * m) := by
    rw [hc k, coeffEmb_coeff, qExpand_coeff_mul]
  refine exists_intCast_eq_of_mem (K := K) ?_
  rw [h1, ← map_phiProdO ζ hζ1, Polynomial.coeff_map, coeffMap_coeff]
  exact (((phiProdO ζ hζ1).coeff k).coeff ((ℓ : ℤ) * m)).property

/-! ## The triangularity descent

`jq = q⁻¹ + ⋯`, so `P.coeff (natDegree P)` is the `q ^ (-natDegree)` coefficient
of `P(jq)` (`coeff_aeval_jq_neg`, promoted to `Defs/Jq.lean`); subtracting that
top term and inducting on the degree turns `IntCoeffs (P(jq))` into `P ∈ ℤ[X]`.
The auxiliary integer-coefficient lemmas are the pin's. -/

private theorem intCoeffs_jq_pow (n : ℕ) : IntCoeffs (jq ^ n) := by
  intro m
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  by_cases hneg : (m - -(n : ℤ)) < 0
  · exact ⟨0, by rw [ofPowerSeries_coeff_of_neg _ hneg, Int.cast_zero]⟩
  · refine ⟨(PowerSeries.coeff (m - -(n : ℤ)).toNat (jNum ^ n) : ℤ), ?_⟩
    have hcast : (m - -(n : ℤ)) = (((m - -(n : ℤ)).toNat : ℕ) : ℤ) :=
      (Int.toNat_of_nonneg (not_lt.mp hneg)).symm
    rw [hcast, HahnSeries.ofPowerSeries_apply_coeff]
    show PowerSeries.coeff _ (jNumQ ^ n) = _
    rw [jNumQ, ← map_pow, PowerSeries.coeff_map]
    rfl

private theorem intCoeffs_jq : IntCoeffs jq := by
  have h := intCoeffs_jq_pow 1
  rwa [pow_one] at h

private theorem intCoeffs_algebraMap_int_mul_jq_pow (z : ℤ) (n : ℕ) :
    IntCoeffs (algebraMap ℚ (LaurentSeries ℚ) ((z : ℚ)) * jq ^ n) := by
  intro m
  obtain ⟨a, ha⟩ := intCoeffs_jq_pow n m
  refine ⟨z * a, ?_⟩
  rw [algebraMap_apply_eq_single, HahnSeries.coeff_single_zero_mul, ha]
  push_cast
  ring

private theorem IntCoeffs.sub {f g : LaurentSeries ℚ} (hf : IntCoeffs f) (hg : IntCoeffs g) :
    IntCoeffs (f - g) := by
  intro m
  obtain ⟨a, ha⟩ := hf m
  obtain ⟨b, hb⟩ := hg m
  exact ⟨a - b, by rw [HahnSeries.coeff_sub, ha, hb]; push_cast; ring⟩

/-- The triangularity descent: a rational polynomial whose value at `jq` has
integer `q`-expansion coefficients is itself in `ℤ[X]`. Verbatim from the pin
wrapper `Theorems/Thm_ModularCurve_PhiGen_aeval_jq_intCoeffs_descent.lean`. -/
theorem aeval_jq_intCoeffs_descent (P : Polynomial ℚ)
    (hP : IntCoeffs (Polynomial.aeval jq P)) (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) := by
  suffices H : ∀ d : ℕ, ∀ P : Polynomial ℚ, P.natDegree = d →
      IntCoeffs (Polynomial.aeval jq P) → ∀ k : ℕ, ∃ z : ℤ, P.coeff k = (z : ℚ) by
    exact H P.natDegree P rfl hP k
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro P hd hP k
  obtain ⟨zd, hzd⟩ := hP (-(d : ℤ))
  have hlead : P.coeff d = (zd : ℚ) := by
    rw [← coeff_aeval_jq_neg P hd.le, hzd]
  rcases lt_trichotomy k d with hk | rfl | hk
  ·
    set Q : Polynomial ℚ := P - Polynomial.C (P.coeff d) * Polynomial.X ^ d with hQ
    have hQcoeff : Q.coeff k = P.coeff k := by
      rw [hQ, Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
        ite_eq_right (by omega), mul_zero, sub_zero]
    have hQdeg : Q.natDegree < d := by
      rcases eq_or_ne Q 0 with hQ0 | hQ0
      · rw [hQ0, Polynomial.natDegree_zero]; omega
      refine lt_of_le_of_ne ?_ ?_
      · refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hd]
        exact max_le le_rfl (Polynomial.natDegree_C_mul_X_pow_le _ _)
      · intro hcon
        apply hQ0
        rw [← Polynomial.leadingCoeff_eq_zero, Polynomial.leadingCoeff, hcon, hQ,
          Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          ite_eq_left rfl, mul_one, sub_self]
    have hQint : IntCoeffs (Polynomial.aeval jq Q) := by
      rw [hQ, map_sub, map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X, hlead]
      exact hP.sub (intCoeffs_algebraMap_int_mul_jq_pow zd d)
    obtain ⟨z, hz⟩ := ih Q.natDegree hQdeg Q rfl hQint k
    exact ⟨z, by rw [← hQcoeff, hz]⟩
  · exact ⟨zd, hlead⟩
  · exact ⟨0, by rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), Int.cast_zero]⟩

/-! ## The wire test

`P = X`: `aeval jq X = jq`, `hP` is `intCoeffs_jq`, and the conclusion is
`X.coeff 1 = 1 ∈ ℤ`. It is private because the module's public surface is exactly
the two pin wrappers, but the name records the instantiation. -/
private theorem aeval_jq_intCoeffs_descent_X :
    ∃ z : ℤ, (Polynomial.X : Polynomial ℚ).coeff 1 = (z : ℚ) :=
  aeval_jq_intCoeffs_descent Polynomial.X (by simpa using intCoeffs_jq) 1

end PhiGen
end ModularCurve

end
