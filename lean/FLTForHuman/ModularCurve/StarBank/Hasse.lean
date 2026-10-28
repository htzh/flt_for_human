/-
  The StarBank under the Hasse hypothesis: the star polynomial (`StarBank.starK`), the
  root count (`StarBank.count`), and the Eisenstein integrality that feeds them
  (`StarBank.eisInt_series` / `StarBank.eisInt_not_dvd_num`).

  ## The Hasse hypothesis implies a star polynomial: `StarBank.starK`

  For a field `K` of characteristic `ℓ`, the Hasse hypothesis — a `q`-expansion `T`
  over `ℤ` whose positive coefficients are all divisible by `ℓ` while its constant
  term is not, realising `T = G(j(q)) · Δ(q) ^ (ℓ - 1)` with `deg G = ℓ - 1` — produces
  `M ≥ 1`, `(M : K) ≠ 0` and `G : K[X]` of degree `M` with

    `G(j(q)) · (q · η(q) ^ 24) ^ M = 1`.

  `ℓ < 5` is dispatched by `(240 : K) = 0` (`j(q) · q · η(q) ^ 24 = 1`, since
  `E₄ = jNum` collapses to `1`), and `5 ≤ ℓ` by applying the `ℤ → K` coefficient map
  to the Hasse datum: `T` becomes the constant `c` and `G` is rescaled by `c⁻¹`. The
  `Dseries`/`hahnMapRingHom` layer below is that naturality.

  ## The root count: `StarBank.count`

  For an algebraically closed `K`, `p ≥ 2`, `(p : K) ≠ 0`, `R` monic of degree `p`,
  `0 < deg G` and `G.comp R ∣ C c · G ^ (p + 1)` with `c ≠ 0`: all roots of `G` coincide
  in a single `β₀` and `R = (X - β₀) ^ p + β₀`. The dichotomy is the odd/even root
  count over `G.comp R`'s root multiset.

  ## Eisenstein integrality: `eisInt_series` and `eisInt_not_dvd_num`

  `ℓ ∣ (bernoulli (ℓ - 1)).den` (von Staudt–Clausen) and `ℓ ∤ (bernoulli (ℓ - 1)).num`
  are the two halves of the Hasse hypothesis for the Eisenstein series: the second
  is what makes `StarBank.starK`'s constant term survive the reduction, and together
  with `EisensteinSeries.E_qExpansion_coeff` they give an integral `q`-expansion `T`
  of `((bernoulli (ℓ - 1)).num) • E_{ℓ - 1}` with every positive coefficient divisible
  by `ℓ`. The 99-line prelude (`eisInt_not_dvd_den_shift`, `eisInt_dvd_den`,
  `eisInt_bernoulli_ne_zero`, `eisInt_coeff`) is written **once** here: the pin
  duplicates it in both `S_` files.

  ## Source

  FLT `anthropics/fermats-last-theorem@aa2d8b3`:
  `P2M/Sol/S_ModularCurve_StarBank_starK.lean` (210 lines),
  `P2M/Sol/S_ModularCurve_StarBank_count.lean` (192 lines),
  `P2M/Sol/S_ModularCurve_StarBank_eisInt_series.lean` (161 lines),
  `P2M/Sol/S_ModularCurve_StarBank_eisInt_not_dvd_num.lean` (156 lines), and the
  matching `Theorems/` wrappers, whose statements are the public headlines below.

  ## Recorded deviations

  * The pin declares `StarBank.starK`, `StarBank.eisInt_series` and
    `StarBank.eisInt_not_dvd_num` `private` in their `S_` files and restates them in
    the public `Theorems/` wrappers; each is stated **once**, public, here, at the
    wrapper's name (the precedent is `ModularPolynomialStarBank.lean`'s
    `delta_pow_ne`).
  * The pin's four anonymous probes are dropped: two are one-line `decide` checks of
    arithmetic (`(720 : ℚ) ≠ 0`, `¬ (7 : ℤ) ∣ -240`) carrying no mathematics, and are
    regression checks of the *statement* rather than of this node. The two `Kbar2`
    probes of `count`, which witness that the row is not vacuous, are kept below and
    are why `Kbar2` — the pin's local abbreviation for `AlgebraicClosure (ZMod 2)`,
    which the corpus parser misreads as `BassSerre.Gp` — is written locally,
    `private`.

  spec-pin: Theorems/Thm_ModularCurve_StarBank_starK.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_starK.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_count.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_count.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_eisInt_series.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_eisInt_series.lean
  spec-pin: Theorems/Thm_ModularCurve_StarBank_eisInt_not_dvd_num.lean
  spec-pin: P2M/Sol/S_ModularCurve_StarBank_eisInt_not_dvd_num.lean
-/
import FLTForHuman.ModularCurve.Defs.JqCoeff
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.Splits
import Mathlib.Data.Rat.Lemmas
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Bernoulli
import Mathlib.NumberTheory.ModularForms.EisensteinSeries.QExpansion

set_option autoImplicit false

open scoped ArithmeticFunction.sigma

noncomputable section

namespace ModularCurve

namespace W1

open Finset

/-- The `ℓ`-shift of the von Staudt–Clausen denominator: `ℓ` does not divide the
denominator of `bernoulli (ℓ - 1) + 1 / ℓ`. The sum in von Staudt–Clausen splits as
`1 / ℓ` plus a sum over primes `p ≠ ℓ`, whose denominator is coprime to `ℓ`. -/
theorem eisInt_not_dvd_den_shift {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den := by
  have hℓp : ℓ.Prime := Fact.out

  obtain ⟨m, hm⟩ := hℓp.odd_of_ne_two (by omega)
  set k₀ := (ℓ - 1) / 2 with hk₀def
  have h2k₀ : 2 * k₀ = ℓ - 1 := by omega

  obtain ⟨z, hz⟩ := Bernoulli.vonStaudt_clausen k₀

  rw [h2k₀] at hz
  have hrange : ℓ - 1 + 2 = ℓ + 1 := by omega
  rw [hrange] at hz

  set S := {p ∈ range (ℓ + 1) | p.Prime ∧ p - 1 ∣ ℓ - 1} with hSdef
  have hℓS : ℓ ∈ S := by
    simp only [hSdef, mem_filter, mem_range]
    exact ⟨Nat.lt_succ_self ℓ, hℓp, dvd_refl _⟩

  have hsplit := (add_sum_erase S (fun p => (1 : ℚ) / (p : ℚ)) hℓS).symm
  rw [hsplit] at hz

  have hz' : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)
      = (z : ℚ) - ∑ p ∈ S.erase ℓ, (1 : ℚ) / (p : ℚ) := by
    linarith [hz]
  rw [hz', Rat.intCast_sub_den]

  have hdendvd := Rat.den_sum_dvd_prod_den (S.erase ℓ) (fun p => (1 : ℚ) / (p : ℚ))
  have hcop : (∏ p ∈ S.erase ℓ, ((1 : ℚ) / (p : ℚ)).den).Coprime ℓ := by
    refine Nat.Coprime.prod_left fun p hp => ?_
    have hpS : p ∈ S := Finset.mem_of_mem_erase hp
    have hpne : p ≠ ℓ := Finset.ne_of_mem_erase hp
    have hpp : p.Prime := (mem_filter.mp hpS).2.1
    have : ((1 : ℚ) / (p : ℚ)).den = p := by simp [hpp.ne_zero]
    rw [this]
    exact (Nat.coprime_primes hpp hℓp).mpr hpne
  intro hdvd
  exact (Nat.Prime.coprime_iff_not_dvd hℓp).mp
    (Nat.Coprime.of_dvd_left hdendvd hcop).symm hdvd

/-! ### The `Dseries` / `hahnMapRingHom` layer of `StarBank.starK`

`Dseries K` is the Laurent series `q · η(q) ^ 24 = Δ` over `K`, and
`hahnMapRingHom (Int.castRingHom K)` is the coefficient map `ℤ⟦q⟧ → K⟦q⟧`: the
two objects `StarBank.starK`'s `5 ≤ ℓ` branch reads the Hasse datum through. -/

/-- `q · η(q) ^ 24` over `K`: the `Δ` whose powers `StarBank.starK` turns into `1`. -/
abbrev Dseries (K : Type*) [CommRing K] : LaurentSeries K :=
  HahnSeries.single (1 : ℤ) (1 : K)
    * HahnSeries.ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24

/-- The coefficient map `LaurentSeries R →+* LaurentSeries S` induced by `f : R →+* S`. -/
private def hahnMapRingHom {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    LaurentSeries R →+* LaurentSeries S where
  toFun x := x.map f
  map_one' := HahnSeries.map_one f.toMonoidWithZeroHom
  map_mul' _ _ := HahnSeries.map_mul f.toNonUnitalRingHom
  map_zero' := HahnSeries.map_zero f.toZeroHom
  map_add' _ _ := HahnSeries.map_add f.toAddMonoidHom

private theorem hahnMapRingHom_apply {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (x : LaurentSeries R) : hahnMapRingHom f x = x.map f := rfl

/-- `HahnSeries.ofPowerSeries` is natural in the coefficient ring. -/
theorem ofPowerSeries_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (u : PowerSeries R) :
    (HahnSeries.ofPowerSeries ℤ R u).map f = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext k
  rw [HahnSeries.map_coeff]
  rcases le_or_gt 0 k with hk | hk
  · lift k to ℕ using hk
    rw [HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]
  · rw [ofPowerSeries_coeff_of_neg _ hk,
      ofPowerSeries_coeff_of_neg _ hk, map_zero]

private theorem hahnMapRingHom_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (u : PowerSeries R) :
    hahnMapRingHom f (HahnSeries.ofPowerSeries ℤ R u)
      = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f u) :=
  ofPowerSeries_map f u

private theorem hahnMapRingHom_single {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (g : ℤ) (r : R) :
    hahnMapRingHom f (HahnSeries.single g r) = HahnSeries.single g (f r) :=
  HahnSeries.map_single (f := f.toZeroHom)

private theorem hahnMapRingHom_etaBlock (K : Type*) [CommRing K] :
    hahnMapRingHom (Int.castRingHom K)
        (HahnSeries.single (1 : ℤ) (1 : ℤ)
          * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24)
      = HahnSeries.single (1 : ℤ) (1 : K)
          * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24 := by
  rw [map_mul, map_pow, hahnMapRingHom_single, hahnMapRingHom_ofPowerSeries, map_one]

private theorem hahnMapRingHom_aeval_jqModC (K : Type*) [CommRing K] (G : Polynomial ℤ) :
    hahnMapRingHom (Int.castRingHom K) (Polynomial.aeval (jqModC ℤ) G)
      = Polynomial.aeval (jqModC K) (G.map (Int.castRingHom K)) := by
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := ℤ) (S := LaurentSeries ℤ) (T := K) (U := LaurentSeries K)
    (φ := Int.castRingHom K) (ψ := hahnMapRingHom (Int.castRingHom K))
    (RingHom.ext_int _ _) G (jqModC ℤ)
  rw [h, hahnMapRingHom_apply, map_jqModC]

private theorem powerSeries_map_eq_C_of_dvd {K : Type*} [CommRing K] {ℓ : ℕ} [CharP K ℓ]
    {T : PowerSeries ℤ} (hT : ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) :
    T.map (Int.castRingHom K) = PowerSeries.C ((PowerSeries.constantCoeff T : ℤ) : K) := by
  ext m
  rw [PowerSeries.coeff_map, PowerSeries.coeff_C]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [ite_eq_left rfl, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, eq_intCast]
  · rw [ite_eq_right hm.ne']
    exact_mod_cast (CharP.intCast_eq_zero_iff K ℓ _).mpr (hT m hm)

private theorem eisenstein4_map_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    PowerSeries.map (Int.castRingHom K) eisenstein4 = 1 := by
  ext n
  rw [PowerSeries.coeff_map, eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [ite_eq_right hn.ne', ite_eq_right hn.ne']
    have h240Z : (Int.castRingHom K) (240 : ℤ) = 0 := by simpa using h240
    rw [map_mul, h240Z, zero_mul]

/-- In characteristic `240`, `j(q) · q · η(q) ^ 24 = 1`: `jNum` collapses to `1` because
`eisenstein4` does, and `dedekindEtaUnit` cancels its inverse. -/
theorem jqModC_mul_Dseries_of_240 {K : Type*} [CommRing K] (h240 : (240 : K) = 0) :
    jqModC K * Dseries K = 1 := by
  have heis := eisenstein4_map_of_240 h240
  have hjnum : PowerSeries.map (Int.castRingHom K) jNum
      = PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv := by
    rw [jNum, map_mul, map_pow, heis, one_pow, one_mul]
  have heta : HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24
      = HahnSeries.ofPowerSeries ℤ K
        (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit) := by
    rw [dedekindEtaUnit, map_pow, map_pow]
  rw [jqModC, Dseries, hjnum, heta]
  have hinv : PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv
      * PowerSeries.map (Int.castRingHom K) dedekindEtaUnit = 1 := by
    rw [← map_mul, mul_comm, dedekindEtaUnit_mul_inv, map_one]
  calc HahnSeries.single (-1 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K
            (PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv)
        * (HahnSeries.single (1 : ℤ) (1 : K)
            * HahnSeries.ofPowerSeries ℤ K
                (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit))
      = (HahnSeries.single (-1 : ℤ) (1 : K) * HahnSeries.single (1 : ℤ) (1 : K))
        * (HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) dedekindEtaUnitInv)
            * HahnSeries.ofPowerSeries ℤ K
              (PowerSeries.map (Int.castRingHom K) dedekindEtaUnit)) := by ring
    _ = HahnSeries.single (0 : ℤ) (1 : K)
        * HahnSeries.ofPowerSeries ℤ K (1 : PowerSeries K) := by
        rw [HahnSeries.single_mul_single, ← map_mul, hinv]; ring_nf
    _ = 1 := by rw [HahnSeries.single_zero_one, map_one, one_mul]

end W1

namespace StarBank

open Finset

/-- `ℓ` divides the denominator of `bernoulli (ℓ - 1)`: the von Staudt–Clausen
denominator is a product of primes `p` with `p - 1 ∣ ℓ - 1`, and `ℓ` is one of them. -/
theorem eisInt_dvd_den {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ℓ ∣ (bernoulli (ℓ - 1)).den := by
  have hℓp : ℓ.Prime := Fact.out
  have hshift := ModularCurve.W1.eisInt_not_dvd_den_shift hℓ5

  have hℓden : ((1 : ℚ) / (ℓ : ℚ)).den = ℓ := by simp [hℓp.ne_zero]
  have hdvd : ℓ ∣ (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)).den * (bernoulli (ℓ - 1)).den := by
    have h := Rat.sub_den_dvd (bernoulli (ℓ - 1) + 1 / (ℓ : ℚ)) (bernoulli (ℓ - 1))
    have hsimp : bernoulli (ℓ - 1) + 1 / (ℓ : ℚ) - bernoulli (ℓ - 1) = 1 / (ℓ : ℚ) := by ring
    rw [hsimp, hℓden] at h
    exact h
  exact ((hℓp.dvd_mul).mp hdvd).resolve_left hshift

/-- `ℓ` does not divide the numerator of `bernoulli (ℓ - 1)`: the fraction is reduced
and `ℓ` divides its denominator. -/
theorem eisInt_not_dvd_num {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) :
    ¬ (ℓ : ℤ) ∣ (bernoulli (ℓ - 1)).num := by
  intro hdvd
  have hden := eisInt_dvd_den hℓ5
  have hnum : ℓ ∣ (bernoulli (ℓ - 1)).num.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hcop := (bernoulli (ℓ - 1)).reduced
  have hgcd : ℓ ∣ Nat.gcd (bernoulli (ℓ - 1)).num.natAbs (bernoulli (ℓ - 1)).den :=
    Nat.dvd_gcd hnum hden
  unfold Nat.Coprime at hcop
  rw [hcop] at hgcd
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp hgcd)

/-- `bernoulli (ℓ - 1) ≠ 0` for an odd prime `ℓ ≥ 5`, from `ℓ ∣ den`. -/
theorem eisInt_bernoulli_ne_zero
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ) : bernoulli (ℓ - 1) ≠ 0 := by
  intro h
  have := eisInt_dvd_den hℓ5
  rw [h, Rat.den_zero] at this
  exact (Nat.Prime.one_lt (Fact.out : ℓ.Prime)).ne' (Nat.dvd_one.mp this)

/-- The `m`-th coefficient of `((bernoulli (ℓ - 1)).num) • E_{ℓ - 1}` is an integer; its
`m = 0` value is the numerator itself, and for `1 ≤ m` it is divisible by `ℓ`. -/
theorem eisInt_coeff {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) (m : ℕ) :
    ∃ z : ℤ, ((bernoulli (ℓ - 1)).num : ℂ)
          * (UpperHalfPlane.qExpansion 1 (ModularForm.E hk)).coeff m = ↑z
        ∧ (m = 0 → z = (bernoulli (ℓ - 1)).num) ∧ (1 ≤ m → (ℓ : ℤ) ∣ z) := by
  classical
  have hℓp : ℓ.Prime := Fact.out
  have hkeven : Even (ℓ - 1) := by
    obtain ⟨c, hc⟩ := hℓp.odd_of_ne_two (by omega); exact ⟨c, by omega⟩
  set B := bernoulli (ℓ - 1) with hBdef
  have hB0 : B ≠ 0 := eisInt_bernoulli_ne_zero hℓ5
  have hcoeff := EisensteinSeries.E_qExpansion_coeff hk hkeven m
  rcases Nat.eq_zero_or_pos m with hm0 | hm1
  · subst hm0
    refine ⟨B.num, ?_, fun _ => rfl, by omega⟩
    rw [hcoeff]; simp
  ·
    have hm1' : m ≠ 0 := hm1.ne'
    rw [hcoeff, ite_eq_right hm1']
    refine ⟨-(2 * (↑(ℓ - 1) : ℤ) * (↑B.den : ℤ) * (↑(σ (ℓ - 1 - 1) m) : ℤ)), ?_, ?_, ?_⟩
    ·
      have hnum : (B.num : ℂ) ≠ 0 := by
        exact_mod_cast Rat.num_ne_zero.mpr hB0
      have hcast : ((B : ℚ) : ℂ) = (B.num : ℂ) / (B.den : ℂ) := by
        exact_mod_cast Rat.cast_def (K := ℂ) B
      rw [hcast]
      have hden0 : (B.den : ℂ) ≠ 0 := by
        exact_mod_cast B.den_ne_zero
      field_simp
      push_cast
      ring
    · intro h; omega
    · intro _
      have hd : (ℓ : ℤ) ∣ (↑B.den : ℤ) :=
        Int.natCast_dvd_natCast.mpr (eisInt_dvd_den hℓ5)
      exact dvd_neg.mpr ((hd.mul_left _).mul_right _)

/-- The Hasse hypothesis's `q`-expansion half: some `T : ℤ⟦q⟧` maps to
`((bernoulli (ℓ - 1)).num) • E_{ℓ - 1}`, has constant term the numerator, and has every
positive coefficient divisible by `ℓ`. -/
theorem eisInt_series {ℓ : ℕ} [Fact ℓ.Prime] (hℓ5 : 5 ≤ ℓ)
    (hk : 3 ≤ ℓ - 1) :
    ∃ T : PowerSeries ℤ,
      T.map (Int.castRingHom ℂ)
        = ((bernoulli (ℓ - 1)).num : ℂ) • UpperHalfPlane.qExpansion 1 (⇑(ModularForm.E hk))
      ∧ PowerSeries.constantCoeff T = (bernoulli (ℓ - 1)).num
      ∧ ∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m := by
  classical
  refine ⟨PowerSeries.mk fun m => (eisInt_coeff hℓ5 hk m).choose, ?_, ?_, ?_⟩
  · ext m
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, PowerSeries.coeff_smul, smul_eq_mul]
    exact (eisInt_coeff hℓ5 hk m).choose_spec.1.symm
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_mk]
    exact (eisInt_coeff hℓ5 hk 0).choose_spec.2.1 rfl
  · intro m hm
    rw [PowerSeries.coeff_mk]
    exact (eisInt_coeff hℓ5 hk m).choose_spec.2.2 hm

/-! ### The Hasse hypothesis implies a star polynomial -/

/-- The `ℓ < 5` branch of `StarBank.starK`: in characteristic `240`, `j(q) · Δ = 1`,
so the star polynomial is `X` of degree `1`. -/
private theorem starK_of_240 (K : Type*) [Field K] (h240 : (240 : K) = 0) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  refine ⟨1, le_refl 1, ?_, Polynomial.X, Polynomial.natDegree_X, ?_⟩
  · exact_mod_cast one_ne_zero (α := K)
  · rw [Polynomial.aeval_X, pow_one]
    exact ModularCurve.W1.jqModC_mul_Dseries_of_240 h240

/-- **The Hasse hypothesis implies a star polynomial.** If `5 ≤ ℓ` and there is an
integral `q`-expansion `T` divisible by `ℓ` at every positive coefficient but not at
its constant term, and `T = G(j) · Δ ^ (ℓ - 1)`, then over any field `K` of
characteristic `ℓ` there is `M ≥ 1`, `(M : K) ≠ 0` and `P : K[X]` of degree `M` with
`P(j) · Δ ^ M = 1`. -/
theorem starK (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (hHasse : 5 ≤ ℓ → ∃ (T : PowerSeries ℤ) (G : Polynomial ℤ),
        (∀ m, 1 ≤ m → (ℓ : ℤ) ∣ T.coeff m) ∧ ¬ (ℓ : ℤ) ∣ PowerSeries.constantCoeff T
        ∧ G.natDegree = ℓ - 1 ∧ G.coeff (ℓ - 1) = PowerSeries.constantCoeff T
        ∧ HahnSeries.ofPowerSeries ℤ ℤ T
            = Polynomial.aeval (jqModC ℤ) G
              * (HahnSeries.single (1 : ℤ) (1 : ℤ)
                  * HahnSeries.ofPowerSeries ℤ ℤ etaProd ^ 24) ^ (ℓ - 1)) :
    ∃ M : ℕ, 1 ≤ M ∧ (M : K) ≠ 0 ∧ ∃ G : Polynomial K, G.natDegree = M
      ∧ Polynomial.aeval (jqModC K) G
          * (HahnSeries.single (1 : ℤ) (1 : K)
              * HahnSeries.ofPowerSeries ℤ K
                  (PowerSeries.map (Int.castRingHom K) etaProd) ^ 24) ^ M = 1 := by
  have hℓp : ℓ.Prime := Fact.out
  rcases lt_or_ge ℓ 5 with hℓ5 | hℓ5
  ·
    have hℓdvd : ℓ ∣ 240 := by
      interval_cases ℓ <;> first | decide | exact absurd hℓp (by decide)
    exact starK_of_240 K ((CharP.cast_eq_zero_iff K ℓ 240).mpr hℓdvd)
  ·
    obtain ⟨T, G₀, hTdvd, hTconst, hGdeg, hGcoeff, hId⟩ := hHasse hℓ5
    set cT := PowerSeries.constantCoeff T with hcTdef
    have hcTK : ((cT : ℤ) : K) ≠ 0 := fun h =>
      hTconst ((CharP.intCast_eq_zero_iff K ℓ cT).mp h)

    have hmap := congrArg (ModularCurve.W1.hahnMapRingHom (Int.castRingHom K)) hId
    rw [map_mul, map_pow, ModularCurve.W1.hahnMapRingHom_aeval_jqModC,
      ModularCurve.W1.hahnMapRingHom_etaBlock,
      ModularCurve.W1.hahnMapRingHom_apply, ModularCurve.W1.ofPowerSeries_map,
      ModularCurve.W1.powerSeries_map_eq_C_of_dvd hTdvd,
      HahnSeries.ofPowerSeries_C] at hmap

    refine ⟨ℓ - 1, by omega, ?_,
      Polynomial.C (((cT : ℤ) : K)⁻¹) * G₀.map (Int.castRingHom K), ?_, ?_⟩
    ·
      have h1 : (1 : ℕ) ≤ ℓ := hℓp.one_lt.le
      have : ((ℓ - 1 : ℕ) : K) = (ℓ : K) - 1 := by exact_mod_cast Nat.cast_sub h1
      rw [this, CharP.cast_eq_zero K ℓ, zero_sub]
      exact neg_ne_zero.mpr one_ne_zero
    ·
      have hdegK : (G₀.map (Int.castRingHom K)).natDegree = ℓ - 1 := by
        refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_ |>.trans hGdeg
        rw [Polynomial.leadingCoeff, hGdeg, hGcoeff]; simpa using hcTK
      rw [Polynomial.natDegree_C_mul (inv_ne_zero hcTK), hdegK]
    ·
      rw [map_mul (Polynomial.aeval (jqModC K)), Polynomial.aeval_C, mul_assoc, ← hmap,
        HahnSeries.algebraMap_apply' ℤ, PowerSeries.algebraMap_eq,
        HahnSeries.ofPowerSeries_C, ← map_mul, inv_mul_cancel₀ hcTK, map_one]

/-! ### The root count

`Kbar2` is the pin's local abbreviation for `AlgebraicClosure (ZMod 2)`, the field its
two non-vacuity probes of `StarBank.count` are stated over. The corpus parser reads the
name as `BassSerre.Gp`; it is not. -/

private abbrev Kbar2 : Type := AlgebraicClosure (ZMod 2)

/-- `StarBank.count`'s divisibility hypothesis is satisfiable as stated. -/
example : ((Polynomial.X ^ 2 - Polynomial.X : Polynomial Kbar2)).comp (Polynomial.X ^ 2)
    ∣ Polynomial.C 1 * (Polynomial.X ^ 2 - Polynomial.X) ^ (2 + 1) := by
  have h2K : (2 : Kbar2) = 0 := by exact_mod_cast CharP.cast_eq_zero Kbar2 2
  have h2 : (2 : Polynomial Kbar2) = 0 := by
    rw [← map_ofNat (Polynomial.C : Kbar2 →+* Polynomial Kbar2) 2, h2K, map_zero]
  have hcomp : (Polynomial.X ^ 2 - Polynomial.X :
      Polynomial Kbar2).comp (Polynomial.X ^ 2) = (Polynomial.X ^ 2 - Polynomial.X) ^ 2 := by
    rw [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.X_comp]
    have key : (Polynomial.X ^ 2 - Polynomial.X : Polynomial Kbar2) ^ 2
        = (Polynomial.X ^ 2) ^ 2 - Polynomial.X ^ 2
            + 2 * (Polynomial.X ^ 2 - Polynomial.X ^ 3) := by ring
    rw [key, h2, zero_mul, add_zero]
  rw [hcomp, Polynomial.C_1, one_mul]
  exact pow_dvd_pow _ (by norm_num)

/-- `count`'s conclusion is not automatic: over `Kbar2` the datum `R = X ^ 2`,
`G = X ^ 2 - X` satisfies the divisibility but no single `β₀` collects all roots. -/
example : ¬ ∃ β₀ : Kbar2, (∀ β : Kbar2,
      (Polynomial.X ^ 2 - Polynomial.X : Polynomial Kbar2).IsRoot β → β = β₀) ∧
    (Polynomial.X ^ 2 : Polynomial Kbar2) = (Polynomial.X - Polynomial.C β₀) ^ 2
      + Polynomial.C β₀ := by
  rintro ⟨β₀, huniq, -⟩
  have h0 : (Polynomial.X ^ 2 - Polynomial.X : Polynomial Kbar2).IsRoot 0 := by
    simp [Polynomial.IsRoot]
  have h1 : (Polynomial.X ^ 2 - Polynomial.X : Polynomial Kbar2).IsRoot 1 := by
    simp [Polynomial.IsRoot]
  exact one_ne_zero ((huniq 1 h1).trans (huniq 0 h0).symm)

open Polynomial

/-- **The root count.** Let `K` be algebraically closed, `p ≥ 2` with `(p : K) ≠ 0`, `R`
monic of degree `p`, `G` of positive degree, `c ≠ 0`, and
`G.comp R ∣ C c · G ^ (p + 1)`. Then all roots of `G` are one `β₀`, and
`R = (X - β₀) ^ p + β₀`. -/
theorem count {K : Type*} [Field K] [IsAlgClosed K] {p : ℕ}
    (hp0 : (p : K) ≠ 0) (hp2 : 2 ≤ p) {R G : Polynomial K} (hR : R.Monic)
    (hRdeg : R.natDegree = p) (hG : 0 < G.natDegree) {c : K} (hc : c ≠ 0)
    (hdvd : G.comp R ∣ Polynomial.C c * G ^ (p + 1)) :
    ∃ β₀ : K, (∀ β : K, G.IsRoot β → β = β₀) ∧
      R = (Polynomial.X - Polynomial.C β₀) ^ p + Polynomial.C β₀ := by
  classical
  have hG0 : G ≠ 0 := fun h => by simp [h] at hG

  have hclosure : ∀ γ : K, G.IsRoot (R.eval γ) → G.IsRoot γ := by
    intro γ hγ
    obtain ⟨H, hH⟩ := hdvd
    have he := congrArg (eval γ) hH
    simp only [eval_mul, eval_C, eval_pow, eval_comp] at he
    rw [show G.eval (R.eval γ) = 0 from hγ, zero_mul] at he
    rcases mul_eq_zero.mp he with h | h
    · exact absurd h hc
    · exact (pow_eq_zero_iff (by omega : p + 1 ≠ 0)).mp h

  set S : Finset K := G.roots.toFinset with hS
  have hmemS : ∀ {β : K}, β ∈ S ↔ G.IsRoot β := by
    intro β
    rw [hS, Multiset.mem_toFinset, mem_roots']
    exact ⟨fun h => h.2, fun h => ⟨hG0, h⟩⟩

  have hmonic : ∀ b : K, (R - C b).Monic := fun b =>
    hR.sub_of_left (lt_of_le_of_lt degree_C_le
      (natDegree_pos_iff_degree_pos.mp (by omega)))
  have hdegS : ∀ b : K, (R - C b).natDegree = p := fun b => by
    rw [natDegree_sub_C, hRdeg]
  have hcard : ∀ b : K, (R - C b).roots.card = p := fun b =>
    (splits_iff_card_roots.mp (IsAlgClosed.splits _)).trans (hdegS b)

  have hsub : ∀ b ∈ S, (R - C b).roots.toFinset ⊆ S := by
    intro b hb γ hγ
    rw [Multiset.mem_toFinset, mem_roots'] at hγ
    have hev : R.eval γ = b := by
      have h := hγ.2
      rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
      exact h
    exact hmemS.mpr (hclosure γ (by rw [hev]; exact hmemS.mp hb))

  have hinner : ∀ b ∈ S, (∑ γ ∈ S, (R - C b).roots.count γ) = p := by
    intro b hb
    rw [← Finset.sum_subset (hsub b hb) (fun γ _ hγ =>
      Multiset.count_eq_zero.mpr fun hmem => hγ (Multiset.mem_toFinset.mpr hmem))]
    rw [Multiset.toFinset_sum_count_eq]
    exact hcard b

  set M : Multiset K := ∑ b ∈ S, (R - C b).roots with hM
  have hterm0 : ∀ γ b : K, b ∈ S → b ≠ R.eval γ → (R - C b).roots.count γ = 0 := by
    intro γ b _ hbne
    rw [Multiset.count_eq_zero]
    intro hmem
    rw [mem_roots'] at hmem
    have h := hmem.2
    rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at h
    exact hbne h.symm
  have hMcount : ∀ γ : K, R.eval γ ∈ S → M.count γ = (R - C (R.eval γ)).roots.count γ := by
    intro γ hin
    rw [hM, Multiset.count_sum']
    exact Finset.sum_eq_single_of_mem _ hin fun b hb hbne => hterm0 γ b hb hbne
  have hMcount0 : ∀ γ : K, R.eval γ ∉ S → M.count γ = 0 := by
    intro γ hnot
    rw [hM, Multiset.count_sum']
    exact Finset.sum_eq_zero fun b hb => hterm0 γ b hb fun h => hnot (h ▸ hb)

  have hMle : ∀ γ ∈ S, M.count γ ≤ p := by
    intro γ _
    by_cases hin : R.eval γ ∈ S
    · rw [hMcount γ hin]
      exact (Multiset.count_le_card _ _).trans (hcard _).le
    · rw [hMcount0 γ hin]
      exact Nat.zero_le p
  have hMsum : (∑ γ ∈ S, M.count γ) = ∑ γ ∈ S, p :=
    calc (∑ γ ∈ S, M.count γ)
        = ∑ γ ∈ S, ∑ b ∈ S, (R - C b).roots.count γ :=
          Finset.sum_congr rfl fun γ _ => by rw [hM, Multiset.count_sum']
      _ = ∑ b ∈ S, ∑ γ ∈ S, (R - C b).roots.count γ := Finset.sum_comm
      _ = ∑ b ∈ S, p := Finset.sum_congr rfl hinner
  have hMeq : ∀ γ ∈ S, M.count γ = p := (Finset.sum_eq_sum_iff_of_le hMle).mp hMsum

  have hfact : ∀ γ ∈ S, R.eval γ ∈ S ∧ R - C (R.eval γ) = (X - C γ) ^ p := by
    intro γ hγ
    have hin : R.eval γ ∈ S := by
      by_contra hnot
      have h0 := hMcount0 γ hnot
      rw [hMeq γ hγ] at h0
      omega
    refine ⟨hin, ?_⟩
    have hcnt : (R - C (R.eval γ)).roots.count γ = p := by
      rw [← hMcount γ hin]
      exact hMeq γ hγ
    have hall : ∀ b ∈ (R - C (R.eval γ)).roots, b = γ := by
      have hcc : (R - C (R.eval γ)).roots.count γ = (R - C (R.eval γ)).roots.card :=
        hcnt.trans (hcard _).symm
      exact fun b hb => (Multiset.count_eq_card.mp hcc b hb).symm
    have hrep : (R - C (R.eval γ)).roots = Multiset.replicate p γ := by
      have h1 := Multiset.eq_replicate_card.mpr hall
      rwa [hcard] at h1
    have h2 := (IsAlgClosed.splits (R - C (R.eval γ))).eq_prod_roots_of_monic (hmonic _)
    rw [hrep, Multiset.map_replicate, Multiset.prod_replicate] at h2
    exact h2

  obtain ⟨β₀, hβ₀⟩ := IsAlgClosed.exists_root G (natDegree_pos_iff_degree_pos.mp hG).ne'
  have hβ₀S : β₀ ∈ S := hmemS.mpr hβ₀
  have hcoeff : ∀ b : K, ((X - C b : Polynomial K) ^ p).coeff (p - 1) = -b * p := by
    intro b
    have hXb : (X - C b : Polynomial K) = X + C (-b) := by rw [sub_eq_add_neg, ← C_neg]
    rw [hXb, coeff_X_add_C_pow]
    have h1 : p - (p - 1) = 1 := by omega
    have h2 : p.choose (p - 1) = p := by
      rw [Nat.choose_symm_of_eq_add (n := p) (a := p - 1) (b := 1) (by omega),
        Nat.choose_one_right]
    rw [h1, h2, pow_one]
  have hRcoeff : ∀ β ∈ S, R.coeff (p - 1) = -β * p := by
    intro β hβ
    have e := (hfact β hβ).2
    rw [sub_eq_iff_eq_add] at e
    rw [e, coeff_add, hcoeff, coeff_C, ite_eq_right (by omega : ¬(p - 1 = 0)), add_zero]
  have huniq : ∀ β : K, G.IsRoot β → β = β₀ := by
    intro β hβ
    have h1 := hRcoeff β (hmemS.mpr hβ)
    have h2 := hRcoeff β₀ hβ₀S
    rw [h1] at h2
    rw [neg_mul, neg_mul, neg_inj] at h2
    exact mul_right_cancel₀ hp0 h2

  refine ⟨β₀, huniq, ?_⟩
  obtain ⟨hin₀, hf₀⟩ := hfact β₀ hβ₀S
  rw [sub_eq_iff_eq_add] at hf₀
  have hev : R.eval β₀ = β₀ := huniq _ (hmemS.mp hin₀)
  rw [hev] at hf₀
  exact hf₀

end StarBank

end ModularCurve
