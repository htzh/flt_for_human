/-
The Hecke-compositum degree: the degeneracy-cover degree multiplies.

Two headlines, because the pin states the same theorem twice and the port proves it once:

* `relfinrank_xHHeckeCompositum_eq_mul` — over `X_H(M)`, the full development below;
* `relfinrank_x1HeckeCompositum_eq_mul` — over `X₁(M)`, the `H := ⊥` instance of it, six
  lines at the bottom of the file.  The pin's `x1` file (884 lines) is *not* transcribed:
  every one of its 61 theorem/lemmas has a same-shape twin in the `xH` file, and the port
  holds the bridge `CohCarrier.GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M`, so the `x₁`
  statement is the `x_H` statement with `H := ⊥` (the three function fields are
  `qExpFunctionFieldC K _` of those subgroups and collapse by `rfl`).

For `ℓ, ℓ'` coprime, with `Γ_A = Γ_H(M) ⊓ Γ₀(Mℓ)`, `Γ_B = Γ_H(M) ⊓ Γ₀(Mℓ')` and
`Q = F(Γ_H(M))(q ^ ℓ)` the `q ↦ q ^ ℓ` stretch of the `q`-expansion function field of `Γ_H(M)`,

`[Q(F_A ⊔ F_B) : Q] = [F(Γ_H(M)) : F(Γ_B)] * [Q : Q F_A]`

over any `ℚ`-algebra `L` — the Hecke-compositum equality the `xH` Hecke operators are
built on.

The proof is the pin's.  It runs in three layers.

* **Groups.**  `Γ_H(M) = Γ₁(M)` up to a unipotent correction: every `g ∈ Γ_H(M)` factors
  `g = a · δ` with `a ∈ Γ₁(M)`, `δ ∈ Γ_H(M) ⊓ Γ₀(M ℓ ℓ')` chosen so that `g δ⁻¹` is
  congruent to `1` mod `M` (`exists_delta`); `Γ₁(M)` in turn factors through
  `Γ₁(M) ⊓ Γ₀(Mℓ)` and `Γ₁(M) ⊓ Γ₀(Mℓ')` (`exists_mul_eq_of_mem_Gamma1`, the Bezout
  argument).  The resulting surjection of coset spaces gives
  `[(Γ_H ⊓ Γ₀(Mℓ')) : Γ_H] ≤ [(Γ_H ⊓ Γ₀(Mℓ')) : (Γ_H ⊓ Γ₀(Mℓ))]`.
* **Over `ℂ`.**  `A(Γ) = adjoin ℂ (ratioSet Γ)` is `F(Γ)` for the groups at hand
  (`AA_GammaH_eq`, the only place the analytic input
  `qExpansion_div_mem_laurentBaseChange_xHFunctionField` enters), and the two engine
  bounds `relIndex_gamma0_le_relrank_adjoin_insert_jqNModC` and
  `relrank_adjoin_qExpansion_div_le_relIndex` sandwich the tower law
  `main_C`.
* **Base change `ℚ → L`.**  Everything is transported along `laurentBaseChange`
  (`relfinrank_laurentBaseChange_eq`), with a transcendental generator obtained from
  `JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`.

The engine is `private`; the two headlines are the module's public content, each at its
wrapper's name and statement.  The ground this module stands on is frozen and is *not*
re-proved here:

* `ModularCurve/Degree/Relfinrank.lean` — the ten `RelFinrankKit` lemmas
  (`open ModularCurve.RelFinrankKit` gives the pin's call sites verbatim) and
  `relfinrank_laurentBaseChange_eq`;
* `ModularCurve/Degree/LaurentGlue.lean` — `laurentBaseChange_{map,sup,qExpFunctionFieldC}`;
* `ModularCurve/RelIndex/LeRelrank.lean` and `LeRelIndex.lean` — the two engine
  headlines, called in `main_C` and `relfinrank_FF1_FFB_le`;
* `ModularCurve/RelIndex/RatioField.lean` — `ratioSet` is the pin's `anSet`;
* `ModularCurve/XH/DiamondLift.lean` — `DiamondLift.XH.cocycle` is the pin's
  `conj_hyp_GammaH`, and its `scoped instance finiteIndex_GammaH`;
* `ModularCurve/X1/QExpansionDiv.lean`, `X1/QExpandStretch.lean`,
  `X1/FunctionFieldBaseChange.lean` — the analytic ratio, the `q`-stretch of the ratio
  set, and the transcendental generator;
* `CongruenceSubgroup.{Gamma0_le_of_dvd,Gamma1_le_of_dvd,Gamma1_in_Gamma0}` are the
  pin's local `Gamma0_le_of_dvd` and the two congruence-subgroup facts.

`XHHeckeSol` holds the pin's `XHLDGroups`/`XHLDMain` blocks; the pin's `XHLDField` block
is `RelFinrankKit`, its `XHLDLaurent` block is the frozen ground, so neither is
transcribed.  The pin's `conj_hyp_top` *is* transcribed: `jqNModC_mem_FF` needs it even
in the `xH` file (the pin reaches `⊤` there), and the pin's `conj_hyp_GammaH` is
`DiamondLift.XH.cocycle`.

FLT provenance, pinned `aa2d8b3`:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean

https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean

spec-pin: Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
spec-pin: P2M/Sol/S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean
spec-pin: Theorems/Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean
-/
import FLTForHuman.ModularCurve.Degree.LaurentGlue
import FLTForHuman.ModularCurve.Degree.Relfinrank
import FLTForHuman.ModularCurve.RelIndex.LeRelIndex
import FLTForHuman.ModularCurve.RelIndex.LeRelrank
import FLTForHuman.ModularCurve.X1.FunctionFieldBaseChange
import FLTForHuman.ModularCurve.X1.QExpandStretch
import FLTForHuman.ModularCurve.X1.QExpansionDiv
import FLTForHuman.ModularCurve.XH.DiamondLift
import FLTForHuman.ModularCurve.XH.FunctionField
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupOrder

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups

open CongruenceSubgroup Matrix UpperHalfPlane IntermediateField Polynomial Cardinal
  HahnSeries

namespace ModularCurve

namespace XHHeckeSol

open RelFinrankKit

/-! ## The `Γ_H(M)` group lemmas

The pin's `XHLDGroups` block.  `Γ₁` and `Γ_H` are treated in one development: the `Γ₁`
factorisation is what `Γ_H` reduces to after `exists_delta`. -/

private theorem mem_Gamma0_iff_dvd (n : ℕ) (A : SL(2, ℤ)) :
    A ∈ Gamma0 n ↔ (n : ℤ) ∣ A 1 0 := by
  rw [Gamma0_mem, ZMod.intCast_zmod_eq_zero_iff_dvd]

private theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ Gamma1 M := by
  rw [Gamma1_mem]
  simp [ModularGroup.T]

private theorem T_mem_Gamma0 (n : ℕ) : ModularGroup.T ∈ Gamma0 n := by
  rw [Gamma0_mem]
  simp [ModularGroup.T]

private theorem T_zpow_mem_Gamma1 (M : ℕ) (j : ℤ) : ModularGroup.T ^ j ∈ Gamma1 M :=
  Subgroup.zpow_mem _ (T_mem_Gamma1 M) j

private theorem T_zpow_mem_Gamma0 (n : ℕ) (j : ℤ) : ModularGroup.T ^ j ∈ Gamma0 n :=
  Subgroup.zpow_mem _ (T_mem_Gamma0 n) j

private theorem Gamma0_mul_inf_Gamma0_mul (M ℓ ℓ' : ℕ) (h : Nat.Coprime ℓ ℓ') :
    Gamma0 (M * ℓ) ⊓ Gamma0 (M * ℓ') = Gamma0 (M * ℓ * ℓ') := by
  ext A
  rw [Subgroup.mem_inf, mem_Gamma0_iff_dvd, mem_Gamma0_iff_dvd, mem_Gamma0_iff_dvd]
  constructor
  · rintro ⟨ha, hb⟩
    obtain ⟨k, hk⟩ := ha
    rcases eq_or_ne M 0 with rfl | hM
    · rw [hk]; simp
    · have h2 : (M : ℤ) * ℓ' ∣ (M : ℤ) * (ℓ * k) := by
        have : (A 1 0 : ℤ) = (M : ℤ) * (ℓ * k) := by rw [hk]; push_cast; ring
        rw [← this]; exact_mod_cast hb
      have h3 : (ℓ' : ℤ) ∣ (ℓ : ℤ) * k := (mul_dvd_mul_iff_left (by exact_mod_cast hM)).mp h2
      obtain ⟨k', rfl⟩ := (Nat.isCoprime_iff_coprime.mpr h).symm.dvd_of_dvd_mul_left h3
      exact ⟨k', by rw [hk]; push_cast; ring⟩
  · intro hab
    refine ⟨dvd_trans ?_ hab, dvd_trans ?_ hab⟩
    · exact_mod_cast (dvd_mul_right (M * ℓ) ℓ')
    · refine Int.natCast_dvd_natCast.mpr ⟨ℓ, by ring⟩

private theorem exists_isCoprime_add_mul {c d : ℤ} (hcd : IsCoprime c d) (K : ℤ) (hK : K ≠ 0) :
    ∃ j : ℤ, IsCoprime K (d + j * c) := by
  classical
  let P : Finset ℕ := K.natAbs.primeFactors.filter fun p => ¬ (p : ℤ) ∣ d
  refine ⟨∏ p ∈ P, (p : ℤ), ?_⟩
  set j : ℤ := ∏ p ∈ P, (p : ℤ) with hj
  rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
  refine Nat.coprime_of_dvd fun p hp hpK hpd => ?_
  have hpK' : (p : ℤ) ∣ K := Int.natCast_dvd.mpr hpK
  have hpd' : (p : ℤ) ∣ d + j * c := Int.natCast_dvd.mpr hpd
  have hpP : (p : ℤ) ∣ j ↔ ¬ (p : ℤ) ∣ d := by
    constructor
    · intro hpj
      rw [hj] at hpj
      obtain ⟨q, hqP, hpq⟩ :=
        (Prime.dvd_finsetProd_iff (Int.prime_iff_natAbs_prime.mpr (by simpa using hp)) _).mp hpj
      have hq := (Finset.mem_filter.mp hqP)
      have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq.1
      have : p = q := by
        have h1 : (p : ℤ).natAbs ∣ (q : ℤ).natAbs := Int.natAbs_dvd_natAbs.mpr hpq
        simp only [Int.natAbs_natCast] at h1
        exact (Nat.prime_dvd_prime_iff_eq hp hqprime).mp h1
      subst this
      exact hq.2
    · intro hnd
      have hpmem : p ∈ P := by
        refine Finset.mem_filter.mpr ⟨?_, hnd⟩
        exact Nat.mem_primeFactors.mpr ⟨hp, hpK, Int.natAbs_ne_zero.mpr hK⟩
      rw [hj]
      exact Finset.dvd_prod_of_mem _ hpmem
  by_cases hpc : (p : ℤ) ∣ c
  · have hpd2 : (p : ℤ) ∣ d := by
      have : (p : ℤ) ∣ d + j * c - j * c := dvd_sub hpd' (dvd_mul_of_dvd_right hpc _)
      simpa using this
    have hunit := hcd.isUnit_of_dvd' hpc hpd2
    rw [Int.isUnit_iff_natAbs_eq, Int.natAbs_natCast] at hunit
    exact hp.one_lt.ne' hunit
  · by_cases hpdd : (p : ℤ) ∣ d
    · have hpj : ¬ (p : ℤ) ∣ j := fun h' => (hpP.mp h') hpdd
      have hpjc : ¬ (p : ℤ) ∣ j * c := fun h' =>
        ((Int.prime_iff_natAbs_prime.mpr (by simpa using hp)).dvd_or_dvd h').elim hpj hpc
      apply hpjc
      have : (p : ℤ) ∣ d + j * c - d := dvd_sub hpd' hpdd
      simpa using this
    · have hpj : (p : ℤ) ∣ j := hpP.mpr hpdd
      apply hpdd
      have : (p : ℤ) ∣ d + j * c - j * c := dvd_sub hpd' (dvd_mul_of_dvd_left hpj _)
      simpa using this

private theorem exists_mul_eq_of_mem_Gamma1 (M ℓ ℓ' : ℕ) [NeZero ℓ'] (hcop : Nat.Coprime ℓ ℓ')
    {g : SL(2, ℤ)} (hg : g ∈ Gamma1 M) :
    ∃ a ∈ Gamma1 M ⊓ Gamma0 (M * ℓ), ∃ b ∈ Gamma1 M ⊓ Gamma0 (M * ℓ'), g = a * b := by
  classical
  by_cases hℓ1 : ℓ = 1
  · subst hℓ1
    refine ⟨g, Subgroup.mem_inf.mpr ⟨hg, ?_⟩, 1, one_mem _, (mul_one g).symm⟩
    rw [mul_one]
    exact Gamma1_in_Gamma0 M hg
  obtain ⟨u, v, huv⟩ : IsCoprime (ℓ : ℤ) (ℓ' : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hv : v ≠ 0 := by
    rintro rfl
    simp only [zero_mul, add_zero] at huv
    have h1 : (ℓ : ℤ) ∣ 1 := ⟨u, by linarith⟩
    have : ℓ = 1 := by
      have := Int.eq_one_of_dvd_one (by positivity) h1
      exact_mod_cast this
    exact hℓ1 this
  obtain ⟨hg00, hg11, hg10⟩ := (Gamma1_mem M g).mp hg
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at this
    linarith
  have hM10 : (M : ℤ) ∣ g 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hg10
  obtain ⟨c', hc'⟩ := hM10
  have hcd : IsCoprime (g 1 0) (g 1 1) := ⟨-g 0 1, g 0 0, by linarith⟩
  have hK : (ℓ' : ℤ) * v ≠ 0 := mul_ne_zero (by exact_mod_cast NeZero.ne ℓ') hv
  obtain ⟨j, hj⟩ := exists_isCoprime_add_mul hcd ((ℓ' : ℤ) * v) hK
  set d' : ℤ := g 1 1 + j * g 1 0 with hd'
  have hrs : IsCoprime ((ℓ' : ℤ) * v * g 1 0) d' := by
    refine IsCoprime.mul_left hj ?_
    obtain ⟨x, y, hxy⟩ := hcd
    exact ⟨x - y * j, y, by rw [hd']; linear_combination hxy⟩
  obtain ⟨x, y, hxy⟩ := hrs
  let b₀ : SL(2, ℤ) := ⟨!![y, -x; (ℓ' : ℤ) * v * g 1 0, d'], by
    rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  let a : SL(2, ℤ) := ⟨!![g 0 0 * d' - (g 0 1 + j * g 0 0) * ((ℓ' : ℤ) * v * g 1 0),
      g 0 0 * x + (g 0 1 + j * g 0 0) * y;
      g 1 0 * d' - d' * ((ℓ' : ℤ) * v * g 1 0), g 1 0 * x + d' * y], by
    rw [Matrix.det_fin_two_of]
    have h2 : g 0 0 * d' - (g 0 1 + j * g 0 0) * g 1 0 = 1 := by rw [hd']; linear_combination hdet
    linear_combination (x * ((ℓ' : ℤ) * v * g 1 0) + y * d') * h2 + hxy⟩
  have hb₀T : b₀ * ModularGroup.T ^ (-j) ∈ Gamma1 M ⊓ Gamma0 (M * ℓ') := by
    refine mul_mem (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨T_zpow_mem_Gamma1 M _, T_zpow_mem_Gamma0 _ _⟩)
    · rw [Gamma1_mem]
      refine ⟨?_, ?_, ?_⟩
      · show ((y : ℤ) : ZMod M) = 1
        have h1 : ((x * ((ℓ' : ℤ) * v * g 1 0) + y * d' : ℤ) : ZMod M) = 1 := by
          rw [hxy]; simp
        have h2 : ((g 1 0 : ℤ) : ZMod M) = 0 := hg10
        have h3 : ((d' : ℤ) : ZMod M) = 1 := by
          rw [hd']; push_cast; rw [h2, hg11]; ring
        push_cast at h1
        rw [h2, h3] at h1
        simpa using h1
      · show ((d' : ℤ) : ZMod M) = 1
        rw [hd']; push_cast; rw [hg10, hg11]; ring
      · show (((ℓ' : ℤ) * v * g 1 0 : ℤ) : ZMod M) = 0
        push_cast; rw [hg10]; ring
    · rw [mem_Gamma0_iff_dvd]
      show ((M * ℓ' : ℕ) : ℤ) ∣ (ℓ' : ℤ) * v * g 1 0
      rw [hc']
      exact ⟨v * c', by push_cast; ring⟩
  have ha : a ∈ Gamma1 M ⊓ Gamma0 (M * ℓ) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Gamma1_mem]
      have h2 : ((g 1 0 : ℤ) : ZMod M) = 0 := hg10
      have h3 : ((d' : ℤ) : ZMod M) = 1 := by
        rw [hd']; push_cast; rw [h2, hg11]; ring
      refine ⟨?_, ?_, ?_⟩
      · show ((g 0 0 * d' - (g 0 1 + j * g 0 0) * ((ℓ' : ℤ) * v * g 1 0) : ℤ) : ZMod M) = 1
        push_cast; rw [h2, h3, hg00]; ring
      · show ((g 1 0 * x + d' * y : ℤ) : ZMod M) = 1
        have h1 : ((x * ((ℓ' : ℤ) * v * g 1 0) + y * d' : ℤ) : ZMod M) = 1 := by
          rw [hxy]; simp
        push_cast at h1 ⊢
        rw [h2, h3] at h1 ⊢
        linear_combination h1
      · show ((g 1 0 * d' - d' * ((ℓ' : ℤ) * v * g 1 0) : ℤ) : ZMod M) = 0
        push_cast; rw [h2]; ring
    · rw [mem_Gamma0_iff_dvd]
      show ((M * ℓ : ℕ) : ℤ) ∣ g 1 0 * d' - d' * ((ℓ' : ℤ) * v * g 1 0)
      have : g 1 0 * d' - d' * ((ℓ' : ℤ) * v * g 1 0) = (M * ℓ : ℤ) * (c' * d' * u) := by
        have h1 : (1 : ℤ) - ℓ' * v = u * ℓ := by linarith
        rw [hc']
        linear_combination (M : ℤ) * c' * d' * h1
      rw [this]
      exact ⟨c' * d' * u, by push_cast; ring⟩
  refine ⟨a, ha, b₀ * ModularGroup.T ^ (-j), hb₀T, ?_⟩
  have hgT : g * ModularGroup.T ^ j = a * b₀ := by
    ext i j'
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ModularGroup.coe_T_zpow]
    fin_cases i <;> fin_cases j' <;>
      simp [a, b₀, Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-(g 0 0 : ℤ)) * hxy
    · linear_combination (-(g 0 1 + j * g 0 0 : ℤ)) * hxy
    · linear_combination (-(g 1 0 : ℤ)) * hxy
    · linear_combination (-d') * hxy - hd'
  calc g = g * ModularGroup.T ^ j * ModularGroup.T ^ (-j) := by
          rw [mul_assoc, ← _root_.zpow_add, add_neg_cancel, zpow_zero, mul_one]
    _ = a * (b₀ * ModularGroup.T ^ (-j)) := by rw [hgT, mul_assoc]

private theorem T_mem_GammaH (M : ℕ) (H : Subgroup (ZMod M)ˣ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H :=
  CohCarrier.translation_mem_GammaH M H

private theorem T_mem_infH (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ) :
    ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ Gamma0 t :=
  Subgroup.mem_inf.mpr ⟨T_mem_GammaH M H, T_mem_Gamma0 t⟩

private theorem exists_delta (M : ℕ) [NeZero M] (K : ℕ) [NeZero K] {g : SL(2, ℤ)}
    (hg : g ∈ Gamma0 M) :
    ∃ δ : SL(2, ℤ), δ ∈ Gamma0 (M * K) ∧ ((δ 1 1 : ℤ) : ZMod M) = ((g 1 1 : ℤ) : ZMod M) ∧
      g * δ⁻¹ ∈ Gamma1 M := by
  obtain ⟨c', hc'⟩ := (mem_Gamma0_iff_dvd M g).mp hg
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at this
    linarith
  have hcd : IsCoprime (M : ℤ) (g 1 1) :=
    ⟨-(g 0 1) * c', g 0 0, by rw [hc'] at hdet; linear_combination hdet⟩
  obtain ⟨j, hj⟩ := exists_isCoprime_add_mul hcd (K : ℤ) (by exact_mod_cast NeZero.ne K)
  set D : ℤ := g 1 1 + j * M with hD
  have hcdD : IsCoprime (M : ℤ) D := by
    obtain ⟨x, y, hxy⟩ := hcd
    exact ⟨x - y * j, y, by rw [hD]; linear_combination hxy⟩
  have hMK : IsCoprime ((M : ℤ) * K) D := IsCoprime.mul_left hcdD (by simpa [mul_comm] using hj)
  obtain ⟨x, y, hxy⟩ := hMK
  let δ : SL(2, ℤ) := ⟨!![y, -x; (M : ℤ) * K, D], by rw [Matrix.det_fin_two_of]; linear_combination hxy⟩
  have hinv00 : ((δ⁻¹) 0 0 : ℤ) = D := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [δ]
  have hinv01 : ((δ⁻¹) 0 1 : ℤ) = x := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [δ]
  have hinv10 : ((δ⁻¹) 1 0 : ℤ) = -((M : ℤ) * K) := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [δ]
  have hinv11 : ((δ⁻¹) 1 1 : ℤ) = y := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]; simp [δ]
  have e00 : ((g * δ⁻¹) 0 0 : ℤ) = g 0 0 * D - g 0 1 * ((M : ℤ) * K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv00, hinv10]
    ring
  have e11 : ((g * δ⁻¹) 1 1 : ℤ) = g 1 0 * x + g 1 1 * y := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv01, hinv11]
  have e10 : ((g * δ⁻¹) 1 0 : ℤ) = g 1 0 * D - g 1 1 * ((M : ℤ) * K) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, hinv00, hinv10]
    ring
  have h10 : ((g 1 0 : ℤ) : ZMod M) = 0 := by rw [hc']; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hD' : ((D : ℤ) : ZMod M) = ((g 1 1 : ℤ) : ZMod M) := by
    rw [hD]; push_cast; rw [ZMod.natCast_self, mul_zero, add_zero]
  have hyD : ((y : ℤ) : ZMod M) * ((g 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hxy
    push_cast at this
    rw [ZMod.natCast_self, zero_mul, mul_zero, zero_add, hD'] at this
    exact this
  have had : ((g 0 0 : ℤ) : ZMod M) * ((g 1 1 : ℤ) : ZMod M) = 1 := by
    have := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    push_cast at this
    rw [h10, mul_zero, sub_zero] at this
    exact this
  refine ⟨δ, ?_, ?_, ?_⟩
  · exact (mem_Gamma0_iff_dvd (M * K) δ).mpr ⟨1, by push_cast; simp [δ]⟩
  · show ((D : ℤ) : ZMod M) = ((g 1 1 : ℤ) : ZMod M)
    exact hD'
  · rw [Gamma1_mem]
    refine ⟨?_, ?_, ?_⟩
    · rw [e00]; push_cast; rw [hD', ZMod.natCast_self, zero_mul, mul_zero, sub_zero, had]
    · rw [e11]; push_cast; rw [h10, zero_mul, zero_add, mul_comm, hyD]
    · rw [e10]; push_cast; rw [h10, ZMod.natCast_self, zero_mul, zero_mul, mul_zero, sub_zero]

private theorem exists_mul_eq_of_mem_GammaH (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ)
    [NeZero ℓ] [NeZero ℓ'] (hcop : Nat.Coprime ℓ ℓ') {g : SL(2, ℤ)}
    (hg : g ∈ CohCarrier.GammaH M H) :
    ∃ a ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ), ∃ b ∈ CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ'),
      g = a * b := by
  obtain ⟨hg0, hgu⟩ := CohCarrier.mem_GammaH_iff.mp hg
  have hN : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  obtain ⟨δ, hδ0, hδ11, hg1⟩ := exists_delta M (ℓ * ℓ') hg0
  have hδM : δ ∈ Gamma0 M := Gamma0_le_of_dvd (dvd_mul_right M (ℓ * ℓ')) hδ0
  have hδℓ : δ ∈ Gamma0 (M * ℓ) := Gamma0_le_of_dvd ⟨ℓ', by ring⟩ hδ0
  have hδℓ' : δ ∈ Gamma0 (M * ℓ') := Gamma0_le_of_dvd ⟨ℓ, by ring⟩ hδ0
  have hδH : δ ∈ CohCarrier.GammaH M H := by
    rw [CohCarrier.mem_GammaH_iff]
    refine ⟨hδM, ?_⟩
    have : CohCarrier.gamma0Units M ⟨δ, hδM⟩ = CohCarrier.gamma0Units M ⟨g, hg0⟩ := by
      apply Units.ext
      rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
      exact hδ11
    rw [this]; exact hgu
  obtain ⟨a, ha, b, hb, hfac⟩ := exists_mul_eq_of_mem_Gamma1 M ℓ ℓ' hcop hg1
  refine ⟨a, Subgroup.mem_inf.mpr ⟨CohCarrier.Gamma1_le_GammaH M H ha.1, ha.2⟩, b * δ,
    Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (CohCarrier.Gamma1_le_GammaH M H hb.1) hδH
  · exact mul_mem hb.2 hδℓ'
  · rw [← mul_assoc, ← hfac, inv_mul_cancel_right]

private theorem relIndex_le_relIndex_infH (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero M]
    [NeZero ℓ] [NeZero ℓ'] (hcop : Nat.Coprime ℓ ℓ') :
    (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ')).relIndex (CohCarrier.GammaH M H) ≤
      (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ')).relIndex (CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)) := by
  classical
  set B := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ') with hB
  set A := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ) with hA
  have hle : A ≤ CohCarrier.GammaH M H := inf_le_left
  let e := Subgroup.quotientSubgroupOfEmbeddingOfLE B hle
  have hsurj : Function.Surjective e := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨a, ha, b, hb, hgab⟩ := exists_mul_eq_of_mem_GammaH M H ℓ ℓ' hcop g.2
      refine ⟨QuotientGroup.mk ⟨a, ha⟩, ?_⟩
      rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion]
      rw [hgab, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hb
  have hcard : Nat.card (↥A ⧸ B.subgroupOf A) =
      Nat.card (↥(CohCarrier.GammaH M H) ⧸ B.subgroupOf (CohCarrier.GammaH M H)) :=
    Nat.card_eq_of_bijective e ⟨e.injective, hsurj⟩
  show (B.subgroupOf (CohCarrier.GammaH M H)).index ≤ (B.subgroupOf A).index
  rw [Subgroup.index, Subgroup.index, hcard]

/-! ## The `FF` layer

`A(Γ) = adjoin ℂ (ratioSet Γ)` (the pin's `AA`, its `anSet` being `RelIndex.ratioSet`)
and `F(Γ) = qExpFunctionFieldC` (the pin's `FF`).  `AA_GammaH_eq` identifies the two at
`Γ_H(M)`: this is where the analytic input enters. -/

abbrev AA (Γ : Subgroup SL(2, ℤ)) : IntermediateField ℂ (LaurentSeries ℂ) :=
  adjoin ℂ (RelIndex.ratioSet Γ)

abbrev FF (K : Type*) [Field K] (Γ : Subgroup SL(2, ℤ)) :
    IntermediateField K (LaurentSeries K) :=
  qExpFunctionFieldC K Γ

private theorem FF_le_AA (Γ : Subgroup SL(2, ℤ)) : FF ℂ Γ ≤ AA Γ := by
  refine adjoin.mono ℂ _ _ ?_
  rintro x ⟨k, f, g, pf, pg, hf, hg, hg0, rfl⟩
  have hf' : intSeriesC ℂ pf = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) := by
    rw [intSeriesC]; exact congrArg _ hf
  have hg' : intSeriesC ℂ pg = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑g) := by
    rw [intSeriesC]; exact congrArg _ hg
  refine ⟨k, f, g, ?_, by rw [hf', hg']; rfl⟩
  intro h0
  apply hg0
  rw [hg', h0, map_zero]

private theorem AA_GammaH_eq (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) :
    AA (CohCarrier.GammaH M H) = FF ℂ (CohCarrier.GammaH M H) := by
  refine le_antisymm ?_ (FF_le_AA _)
  refine adjoin_le_iff.mpr ?_
  rintro x ⟨k, f, g, hg, rfl⟩
  have hg' : g ≠ 0 := by
    intro h0
    apply hg
    rw [h0]
    exact qExpansion_zero 1
  have hmem := qExpansion_div_mem_laurentBaseChange_xHFunctionField M H f g hg'
  have hfield : laurentBaseChange ℂ (xHFunctionField M H) = FF ℂ (CohCarrier.GammaH M H) :=
    laurentBaseChange_qExpFunctionFieldC ℂ (CohCarrier.GammaH M H)
  rw [hfield] at hmem
  exact hmem

private theorem conj_hyp_top {Γ' : Subgroup SL(2, ℤ)} (t : ℕ) [NeZero t] (h : Γ' ≤ Gamma0 t) :
    ∀ γ ∈ Γ', ∃ γ₁ ∈ (⊤ : Subgroup SL(2, ℤ)),
      γ₁ 0 0 = γ 0 0 ∧ γ₁ 0 1 = (t : ℤ) * γ 0 1 ∧ (t : ℤ) * γ₁ 1 0 = γ 1 0 ∧ γ₁ 1 1 = γ 1 1 := by
  intro γ hγ
  obtain ⟨k, hk⟩ := (mem_Gamma0_iff_dvd t γ).mp (h hγ)
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at this
    linarith
  refine ⟨⟨!![γ 0 0, (t : ℤ) * γ 0 1; k, γ 1 1], ?_⟩, Subgroup.mem_top _, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    rw [hk] at hdet
    linear_combination hdet
  all_goals simp [hk]

private theorem jqNModC_mem_FF (K : Type*) [Field K] {Γ' : Subgroup SL(2, ℤ)} (t : ℕ) [NeZero t]
    (h : Γ' ≤ Gamma0 t) : jqNModC K t ∈ FF K Γ' := by
  have hj : jqModC K ∈ intFormRatiosC K (⊤ : Subgroup SL(2, ℤ)) :=
    ModularCurve.jqModC_mem_intFormRatiosC K ⊤
  have hT : ModularGroup.T ∈ (⊤ : Subgroup SL(2, ℤ)) := Subgroup.mem_top _
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := ⊤) (Γ' := Γ') hT t
    (conj_hyp_top t h)
  exact intFormRatiosC_subset K Γ' (hsub ⟨_, hj, rfl⟩)

private theorem map_FF_GammaH_le (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (t : ℕ)
    [NeZero M] [NeZero t] :
    (FF K (CohCarrier.GammaH M H)).map (qExpAlg K t) ≤ FF K (CohCarrier.GammaH M H ⊓ Gamma0 (M * t)) := by
  rw [← adjoin_qExpand_image]
  refine adjoin_le_iff.mpr ?_
  rintro x ⟨y, hy, rfl⟩
  have hsub := ModularCurve.qExpand_image_intFormRatiosC_subset K (Γ := CohCarrier.GammaH M H)
    (Γ' := CohCarrier.GammaH M H ⊓ Gamma0 (M * t)) (T_mem_GammaH M H) t
    (DiamondLift.XH.cocycle M H t)
  have hy' : qExpand K t y ∈ (FF K (CohCarrier.GammaH M H)).map (qExpAlg K t) := ⟨y, hy, rfl⟩
  have hmap : (FF K (CohCarrier.GammaH M H)).map (qExpAlg K t) =
      adjoin K (qExpand K t '' intFormRatiosC K (CohCarrier.GammaH M H)) := by
    show (qExpFunctionFieldC K (CohCarrier.GammaH M H)).map _ = _
    rw [qExpFunctionFieldC, adjoin_map]
    rfl
  rw [hmap] at hy'
  have := adjoin.mono K _ _ (hsub.trans (intFormRatiosC_subset K _)) hy'
  rwa [adjoin_self] at this

/-! ## The four fields and their inclusions

`Q = F(Γ_H)(q ^ ℓ)`, `F_A = F(Γ_A)`, `F_B = F(Γ_B)`, `roof = F_A ⊔ F_B(q ^ ℓ)`. -/

section Fields

variable (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero M] [NeZero ℓ]
  [NeZero ℓ']

abbrev GA : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ)

abbrev GB : Subgroup SL(2, ℤ) := CohCarrier.GammaH M H ⊓ Gamma0 (M * ℓ')

abbrev QQ : IntermediateField K (LaurentSeries K) :=
  (FF K (CohCarrier.GammaH M H)).map (qExpAlg K ℓ)

abbrev BP : IntermediateField K (LaurentSeries K) := (FF K (GB M H ℓ')).map (qExpAlg K ℓ)

abbrev roof : IntermediateField K (LaurentSeries K) := FF K (GA M H ℓ) ⊔ BP K M H ℓ ℓ'

omit [NeZero M] [NeZero ℓ] [NeZero ℓ'] in
private theorem FF1_le_FFB : FF K (CohCarrier.GammaH M H) ≤ FF K (GB M H ℓ') :=
  qExpFunctionFieldC_mono K inf_le_left

omit [NeZero ℓ'] in
theorem QQ_le_FFA : QQ K M H ℓ ≤ FF K (GA M H ℓ) := map_FF_GammaH_le K M H ℓ

omit [NeZero M] [NeZero ℓ'] in
theorem QQ_le_BP : QQ K M H ℓ ≤ BP K M H ℓ ℓ' := IntermediateField.map_mono _ (FF1_le_FFB K M H ℓ')

omit [NeZero ℓ'] in
theorem QQ_le_roof : QQ K M H ℓ ≤ roof K M H ℓ ℓ' := (QQ_le_FFA K M H ℓ).trans le_sup_left

end Fields

/-! ## The `ℂ` step

`main_C` is the heart: the two engine bounds and the tower law. -/

section OverC

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero M] [NeZero ℓ] [NeZero ℓ']

private theorem theta_mem_BP : jqNModC ℂ (ℓ * (M * ℓ')) ∈ BP ℂ M H ℓ ℓ' := by
  have hN : NeZero (ℓ * (M * ℓ')) :=
    ⟨mul_ne_zero (NeZero.ne ℓ) (mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ'))⟩
  have hθ : jqNModC ℂ (M * ℓ') ∈ FF ℂ (GB M H ℓ') := jqNModC_mem_FF ℂ (M * ℓ') inf_le_right
  have : jqNModC ℂ (ℓ * (M * ℓ')) = qExpAlg ℂ ℓ (jqNModC ℂ (M * ℓ')) := by
    rw [qExpAlg_apply, jqNModC, jqNModC, qExpand_qExpand]
  rw [this]
  exact ⟨_, hθ, rfl⟩

omit [NeZero M] [NeZero ℓ] [NeZero ℓ'] in
private theorem Gamma0_inf_GA (hcop : Nat.Coprime ℓ ℓ') :
    Gamma0 (ℓ * (M * ℓ')) ⊓ GA M H ℓ = GB M H ℓ' ⊓ GA M H ℓ := by
  have hN : ℓ * (M * ℓ') = M * ℓ * ℓ' := by ring
  rw [hN, ← Gamma0_mul_inf_Gamma0_mul M ℓ ℓ' hcop]
  ext A
  simp only [GA, GB, Subgroup.mem_inf]
  tauto

private theorem relIndex_GB_le (hcop : Nat.Coprime ℓ ℓ') :
    (GB M H ℓ').relIndex (CohCarrier.GammaH M H) ≤ (Gamma0 (ℓ * (M * ℓ'))).relIndex (GA M H ℓ) := by
  rw [← Subgroup.inf_relIndex_right (Gamma0 _), Gamma0_inf_GA M H ℓ ℓ' hcop,
    Subgroup.inf_relIndex_right]
  exact relIndex_le_relIndex_infH M H ℓ ℓ' hcop

private theorem relIndex_GB_ne_zero : (GB M H ℓ').relIndex (CohCarrier.GammaH M H) ≠ 0 := by
  have hN : NeZero (M * ℓ') := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ')⟩
  have hfi : (GB M H ℓ').FiniteIndex :=
    Subgroup.finiteIndex_of_le (H := Gamma1 (M * ℓ'))
      (le_inf ((Gamma1_le_of_dvd (dvd_mul_right M ℓ')).trans (CohCarrier.Gamma1_le_GammaH M H))
        (Gamma1_in_Gamma0 _))
  intro h
  have := Subgroup.relIndex_mul_index (inf_le_left : GB M H ℓ' ≤ CohCarrier.GammaH M H)
  rw [h, zero_mul] at this
  exact Subgroup.FiniteIndex.index_ne_zero this.symm

private theorem relfinrank_FF1_FFB_le :
    relfinrank (FF ℂ (CohCarrier.GammaH M H)) (FF ℂ (GB M H ℓ')) ≤
      (GB M H ℓ').relIndex (CohCarrier.GammaH M H) := by
  have hU := ModularCurve.relrank_adjoin_qExpansion_div_le_relIndex (CohCarrier.GammaH M H)
    (GB M H ℓ') inf_le_left (T_mem_infH M H (M * ℓ')) (relIndex_GB_ne_zero M H ℓ')
  change relrank (AA (CohCarrier.GammaH M H)) (AA (GB M H ℓ')) ≤ _ at hU
  rw [AA_GammaH_eq] at hU
  exact relfinrank_le_of_relrank_le (FF1_le_FFB ℂ M H ℓ') (FF_le_AA _) hU

private theorem main_C (hcop : Nat.Coprime ℓ ℓ') :
    relfinrank (QQ ℂ M H ℓ) (roof ℂ M H ℓ ℓ') =
      relfinrank (FF ℂ (CohCarrier.GammaH M H)) (FF ℂ (GB M H ℓ')) *
        relfinrank (QQ ℂ M H ℓ) (FF ℂ (GA M H ℓ)) := by
  have hN : NeZero (ℓ * (M * ℓ')) :=
    ⟨mul_ne_zero (NeZero.ne ℓ) (mul_ne_zero (NeZero.ne M) (NeZero.ne ℓ'))⟩
  set a := relfinrank (QQ ℂ M H ℓ) (FF ℂ (GA M H ℓ)) with ha
  set b := relfinrank (QQ ℂ M H ℓ) (BP ℂ M H ℓ ℓ') with hb
  set r := relfinrank (QQ ℂ M H ℓ) (roof ℂ M H ℓ ℓ') with hr
  have hbb : b = relfinrank (FF ℂ (CohCarrier.GammaH M H)) (FF ℂ (GB M H ℓ')) :=
    relfinrank_map_map _ _ _
  rw [← hbb]
  have hQA : QQ ℂ M H ℓ ≤ FF ℂ (GA M H ℓ) := QQ_le_FFA ℂ M H ℓ
  have hQB : QQ ℂ M H ℓ ≤ BP ℂ M H ℓ ℓ' := QQ_le_BP ℂ M H ℓ ℓ'
  have hAroof : FF ℂ (GA M H ℓ) ≤ roof ℂ M H ℓ ℓ' := le_sup_left
  have hBroof : BP ℂ M H ℓ ℓ' ≤ roof ℂ M H ℓ ℓ' := le_sup_right
  have htowerA := relfinrank_mul_relfinrank hQA hAroof
  have htowerB := relfinrank_mul_relfinrank hQB hBroof
  by_cases ha0 : a = 0
  · rw [ha0, mul_zero]
    rw [← hr, ← ha, ha0, zero_mul] at htowerA
    exact htowerA.symm
  by_cases hb0 : b = 0
  · rw [hb0, zero_mul]
    rw [← hr, ← hb, hb0, zero_mul] at htowerB
    exact htowerB.symm
  obtain ⟨hrle, hr0⟩ := relfinrank_sup_le hQA hQB ha0 hb0
  rw [← hr, ← ha, ← hb] at hrle
  rw [← hr, ← ha] at htowerA
  set t := relfinrank (FF ℂ (GA M H ℓ)) (roof ℂ M H ℓ ℓ') with ht
  have ht0 : t ≠ 0 := by
    intro h0; apply hr0; rw [← hr, ← htowerA, h0, mul_zero]
  have hθroof : jqNModC ℂ (ℓ * (M * ℓ')) ∈ roof ℂ M H ℓ ℓ' := hBroof (theta_mem_BP M H ℓ ℓ')
  obtain ⟨hint, hdeg⟩ := isIntegral_and_finrank_adjoin_le_relfinrank hAroof ht0 hθroof
  obtain ⟨hint', _⟩ := isIntegral_and_natDegree_minpoly_le (FF_le_AA (GA M H ℓ)) hint
  have hdeg' := finrank_adjoin_simple_le_of_le (FF_le_AA (GA M H ℓ)) hint
  have hC := ModularCurve.relIndex_gamma0_le_relrank_adjoin_insert_jqNModC (GA M H ℓ)
    (T_mem_infH M H (M * ℓ)) (ℓ * (M * ℓ'))
  change ((Gamma0 (ℓ * (M * ℓ'))).relIndex (GA M H ℓ) : Cardinal) ≤
    relrank (AA (GA M H ℓ))
      (adjoin ℂ (insert (jqNModC ℂ (ℓ * (M * ℓ'))) (RelIndex.ratioSet (GA M H ℓ)))) at hC
  rw [AA, relrank_adjoin_insert_eq hint', Nat.cast_le] at hC
  have hidx := relIndex_GB_le M H ℓ ℓ' hcop
  have hup := relfinrank_FF1_FFB_le M H ℓ'
  rw [← hbb] at hup
  have hbt : b ≤ t := hup.trans (hidx.trans (hC.trans (hdeg'.trans hdeg)))
  refine le_antisymm ((mul_comm a b) ▸ hrle) ?_
  calc b * a = a * b := mul_comm _ _
    _ ≤ a * t := Nat.mul_le_mul_left a hbt
    _ = r := htowerA

end OverC

/-! ## The base change `ℚ → L` -/

section BaseChange

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero M] [NeZero ℓ] [NeZero ℓ']

private theorem FF_eq_bc (L : Type*) [Field L] [Algebra ℚ L] (Γ : Subgroup SL(2, ℤ)) :
    FF L Γ = laurentBaseChange L (FF ℚ Γ) := (laurentBaseChange_qExpFunctionFieldC L Γ).symm

omit [NeZero M] [NeZero ℓ'] in
private theorem QQ_eq_bc (L : Type*) [Field L] [Algebra ℚ L] :
    QQ L M H ℓ = laurentBaseChange L (QQ ℚ M H ℓ) := by
  rw [QQ, QQ, laurentBaseChange_map, laurentBaseChange_qExpFunctionFieldC]

omit [NeZero M] [NeZero ℓ'] in
private theorem roof_eq_bc (L : Type*) [Field L] [Algebra ℚ L] :
    roof L M H ℓ ℓ' = laurentBaseChange L (roof ℚ M H ℓ ℓ') := by
  rw [roof, roof, laurentBaseChange_sup, BP, BP, laurentBaseChange_map,
    laurentBaseChange_qExpFunctionFieldC, laurentBaseChange_qExpFunctionFieldC]

private theorem exists_witness_gen (L : Type*) [Field L] [Algebra ℚ L] :
    ∃ t : LaurentSeries L, t ∈ FF L (CohCarrier.GammaH M H) ∧ Transcendental L t ∧
      relfinrank L⟮t⟯ (FF L (CohCarrier.GammaH M H)) ≠ 0 := by
  obtain ⟨x, hxtr, hxfin⟩ :=
    ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange L
      (CohCarrier.GammaH M H) (T_mem_GammaH M H)
  have := hxfin
  have hR : relfinrank L⟮(x : LaurentSeries L)⟯ (laurentBaseChange L (FF ℚ (CohCarrier.GammaH M H))) ≠ 0 := by
    rw [relfinrank_adjoin_simple_eq_finrank]
    convert (Module.finrank_pos (R := ↥L⟮x⟯)
      (M := ↥(laurentBaseChange L (FF ℚ (CohCarrier.GammaH M H))))).ne' using 3
  refine ⟨x, ?_, transcendental_coe hxtr, ?_⟩
  · show (x : LaurentSeries L) ∈ qExpFunctionFieldC L (CohCarrier.GammaH M H)
    rw [← laurentBaseChange_qExpFunctionFieldC L (CohCarrier.GammaH M H)]
    exact x.2
  · show relfinrank L⟮(x : LaurentSeries L)⟯ (qExpFunctionFieldC L (CohCarrier.GammaH M H)) ≠ 0
    rw [← laurentBaseChange_qExpFunctionFieldC L (CohCarrier.GammaH M H)]
    exact hR

omit [NeZero ℓ'] in
private theorem exists_witnesses :
    ∃ t₁ : LaurentSeries ℚ, t₁ ∈ FF ℚ (CohCarrier.GammaH M H) ∧ Transcendental ℚ t₁ ∧
      relfinrank ℚ⟮t₁⟯ (FF ℚ (CohCarrier.GammaH M H)) ≠ 0 ∧
      qExpand ℚ ℓ t₁ ∈ QQ ℚ M H ℓ ∧ Transcendental ℚ (qExpand ℚ ℓ t₁) ∧
      relfinrank ℚ⟮qExpand ℚ ℓ t₁⟯ (QQ ℚ M H ℓ) ≠ 0 := by
  obtain ⟨t₁, ht₁, htr, hR⟩ := exists_witness_gen M H ℚ
  refine ⟨t₁, ht₁, htr, hR, ⟨_, ht₁, rfl⟩, transcendental_map (qExpAlg ℚ ℓ) htr, ?_⟩
  have hmap : ℚ⟮qExpand ℚ ℓ t₁⟯ = (ℚ⟮t₁⟯).map (qExpAlg ℚ ℓ) := by
    rw [adjoin_map, Set.image_singleton]; rfl
  rw [hmap, QQ, relfinrank_map_map]
  exact hR

omit [NeZero ℓ'] in
private theorem relfinrank_bc (L : Type*) [Field L] [Algebra ℚ L] :
    relfinrank (QQ L M H ℓ) (roof L M H ℓ ℓ') = relfinrank (QQ ℚ M H ℓ) (roof ℚ M H ℓ ℓ') ∧
    relfinrank (QQ L M H ℓ) (FF L (GA M H ℓ)) = relfinrank (QQ ℚ M H ℓ) (FF ℚ (GA M H ℓ)) ∧
    relfinrank (FF L (CohCarrier.GammaH M H)) (FF L (GB M H ℓ')) =
      relfinrank (FF ℚ (CohCarrier.GammaH M H)) (FF ℚ (GB M H ℓ')) := by
  obtain ⟨t₁, ht₁, ht₁tr, hR₁, ht₂, ht₂tr, hR₂⟩ := exists_witnesses M H ℓ
  refine ⟨?_, ?_, ?_⟩
  · rw [QQ_eq_bc, roof_eq_bc]
    exact ModularCurve.relfinrank_laurentBaseChange_eq L (QQ_le_roof ℚ M H ℓ ℓ') ht₂ ht₂tr hR₂
  · rw [QQ_eq_bc, FF_eq_bc L]
    exact ModularCurve.relfinrank_laurentBaseChange_eq L (QQ_le_FFA ℚ M H ℓ) ht₂ ht₂tr hR₂
  · rw [FF_eq_bc L, FF_eq_bc L]
    exact ModularCurve.relfinrank_laurentBaseChange_eq L (FF1_le_FFB ℚ M H ℓ') ht₁ ht₁tr hR₁

private theorem main_L (L : Type*) [Field L] [Algebra ℚ L] (hcop : Nat.Coprime ℓ ℓ') :
    relfinrank (QQ L M H ℓ) (roof L M H ℓ ℓ') =
      relfinrank (FF L (CohCarrier.GammaH M H)) (FF L (GB M H ℓ')) *
        relfinrank (QQ L M H ℓ) (FF L (GA M H ℓ)) := by
  obtain ⟨h1, h2, h3⟩ := relfinrank_bc M H ℓ ℓ' L
  obtain ⟨c1, c2, c3⟩ := relfinrank_bc M H ℓ ℓ' ℂ
  rw [h1, h2, h3, ← c1, ← c2, ← c3]
  exact main_C M H ℓ ℓ' hcop

end BaseChange

/-! ## The headline -/

private theorem solution (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) := by
  change IntermediateField.relfinrank
      (IntermediateField.adjoin L
        (qExpand L ℓ '' (laurentBaseChange L (FF ℚ (CohCarrier.GammaH M H)) : Set (LaurentSeries L))))
      (laurentBaseChange L (FF ℚ (GA M H ℓ)) ⊔
        IntermediateField.adjoin L
          (qExpand L ℓ '' (laurentBaseChange L (FF ℚ (GB M H ℓ')) : Set (LaurentSeries L))))
    = IntermediateField.relfinrank (laurentBaseChange L (FF ℚ (CohCarrier.GammaH M H)))
        (laurentBaseChange L (FF ℚ (GB M H ℓ'))) *
      IntermediateField.relfinrank
        (IntermediateField.adjoin L
          (qExpand L ℓ '' (laurentBaseChange L (FF ℚ (CohCarrier.GammaH M H)) : Set (LaurentSeries L))))
        (laurentBaseChange L (FF ℚ (GA M H ℓ)))
  rw [laurentBaseChange_qExpFunctionFieldC, laurentBaseChange_qExpFunctionFieldC,
    laurentBaseChange_qExpFunctionFieldC, adjoin_qExpand_image, adjoin_qExpand_image]
  exact main_L M H ℓ ℓ' L hℓ

end XHHeckeSol

/-- **The Hecke-compositum degree.**  For `ℓ, ℓ'` coprime the degree of
`Q(F_A ⊔ F_B)` over `Q = F(Γ_H(M))(q ^ ℓ)` is the product of the degree of `F(Γ_H(M))`
over `F(Γ_H(M) ⊓ Γ₀(Mℓ'))` and the degree of `Q` over `Q F_A`, over any `ℚ`-algebra `L`.
Verbatim from `Theorems/Thm_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean`. -/
theorem relfinrank_xHHeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.xHFunctionField M H) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.xHTopFunctionFieldC ℚ M H (M * ℓ))) :=
  XHHeckeSol.solution L M H ℓ ℓ' hℓ

/-- **The Hecke-compositum degree over `X₁(M)`.**  The `xH` theorem at `H := ⊥`, since
`CohCarrier.GammaH M ⊥ = Gamma1 M`.  Verbatim from
`Theorems/Thm_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean`; the pin's
`S_ModularCurve_relfinrank_x1HeckeCompositum_eq_mul.lean` is not transcribed. -/
theorem relfinrank_x1HeckeCompositum_eq_mul (L : Type*) [Field L] [Algebra ℚ L]
    (M : ℕ) [NeZero M] (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] (hℓ : Nat.Coprime ℓ ℓ') :
    IntermediateField.relfinrank
        (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
          (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
            Set (LaurentSeries L))))
        (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ)) ⊔
          IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')) :
              Set (LaurentSeries L))))
      = IntermediateField.relfinrank
            (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ')))
        * IntermediateField.relfinrank
            (IntermediateField.adjoin L (ModularCurve.qExpand L ℓ ''
              (ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M) :
                Set (LaurentSeries L))))
            (ModularCurve.laurentBaseChange L (ModularCurve.x1x0FunctionFieldC ℚ M (M * ℓ))) := by
  have h := relfinrank_xHHeckeCompositum_eq_mul L M ⊥ ℓ ℓ' hℓ
  simpa only [CohCarrier.GammaH_bot, xHFunctionFieldC, x1FunctionFieldC, xHTopFunctionFieldC,
    x1x0FunctionFieldC, xHFunctionField, x1FunctionField] using h

end ModularCurve

end
