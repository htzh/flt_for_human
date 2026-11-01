/-
  The peaked auxiliary form on `Γ₁(N)`: the product form whose non-`Γ₁(N)` slashes peak.

  Two rows of one subject. The first is the pin's
  `ModularCurve.SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd` (252 lines), whose weight
  is normalized to `12 ∣ w`; the second is `ModularCurve.exists_gamma1_peaked_auxiliary_form` (249
  lines), the same form with the weight normalized to the parity of an arbitrary `k` — `Even (k + w)`,
  so that `ϑ` multiplies into weight `k`. A *peaked
  exponent* is a Siegel exponent function `m` whose induced weight
  `Ord x y = ∑_{r s} m r s · (6·(r x + s y).val² - 6N·(r x + s y).val + N²)` is strictly maximal at
  `(1, 0)` — the row of the `S`-cusp — among the primitive rows that miss the two degenerate ones.
  Fed into the three layers of `ProductForm.lean`, that exponent yields an auxiliary form `ϑ` on
  `Γ₁(N)` of weight `12 t` with four properties:

  * its weight is a multiple of `12` and is carried by the `m₀`-th coefficient: `12 ∣ w` and
    `w < 12 m₀` with `m₀` pinned by `N m₀ = Ord + N t`;
  * the width-`N` coefficients of its `S`-slash are integral over `ℤ` after multiplying by `N ^ a`;
  * its width-`1` expansion vanishes below `m₀`, is non-zero at `m₀`, and `N ^ a` times every
    coefficient — and the inverse of the `m₀` coefficient — is integral;
  * **peaked**: for every `β` outside `±Γ₁(N)` whose `T`-translates also miss `Γ₁(N)`, the slash
    `ϑ ∣[w] β` decays like `exp (-2π (m₀ + δ) im)` for some `δ > 0`, i.e. strictly faster than the
    `m₀`-th power of the cusp's own growth.

  Those are exactly the properties the `Γ₁(N)` basis argument consumes: a form whose cusp behaviour
  starts at `m₀` with integral coefficients and whose other slashes are peaked can be isolated in the
  `Γ₁(N)` space. The existence of the peaked exponent is `BernoulliWeight.lean`'s
  `exists_peaked_exponent`; this module is its consumer — it selects `t` from the exponent, applies
  the 249 row to get `ϑ`, the 457 row for `m₀` and the width-`1` coefficients, and the 469 row for the
  width-`N` integrality, and turns the weight comparison into the peak estimate.

  Transcribed from the pin's
  `P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean`, pinned
  `aa2d8b3`; the statement is the `Theorems/` wrapper's verbatim. The pin's `UEven` block — the four
  counting/integrality lemmas the proof rests on — is written `private` here, and the pin's
  `attribute [-simp]` wall and `p2m_*` prelude are not transcribed.

  FLT provenance, pinned `aa2d8b3`:
  <https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean>
  spec-pin: Theorems/Thm_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean
  spec-pin: P2M/Sol/S_ModularCurve_SiegelUnit_exists_gamma1_peaked_auxiliary_form_twelve_dvd.lean   -- comparable copy
  spec-pin: Theorems/Thm_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_gamma1_peaked_auxiliary_form.lean   -- comparable copy
-/
import FLTForHuman.ModularCurve.SiegelUnit.ProductForm
import FLTForHuman.ModularCurve.SiegelUnit.BernoulliWeight
import FLTForHuman.ModularCurve.SiegelUnit.Eisenstein
import FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupLattice

open scoped MatrixGroups ModularForm

namespace ModularCurve

namespace SiegelUnit

/-! ## The four counting and integrality lemmas the assembly rests on -/

namespace PeakedAux

/-- The sum of an `r`-invariant function over `ZMod N` is divisible by the additive order of `r`:
the fibres of the quotient by `AddSubgroup.zmultiples r` all have `Nat.card H = addOrderOf r`
elements. -/
private theorem addOrderOf_dvd_sum_of_invariant {N : ℕ} [NeZero N] (r : ZMod N)
    (f : ZMod N → ℕ) (hf : ∀ s, f (s + r) = f s) : addOrderOf r ∣ ∑ s : ZMod N, f s := by
  classical
  set H : AddSubgroup (ZMod N) := AddSubgroup.zmultiples r with hH
  have hinvn : ∀ (k : ℕ) (s : ZMod N), f (s + k • r) = f s := by
    intro k
    induction k with
    | zero => intro s; rw [zero_smul, add_zero]
    | succ k ih => intro s; rw [succ_nsmul, ← add_assoc, hf, ih]
  have hinv : ∀ h ∈ H, ∀ s, f (s + h) = f s := by
    intro h hh s
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hh
    have hn : 0 < addOrderOf r := addOrderOf_pos r
    obtain ⟨k', hk'⟩ : ∃ k' : ℕ, (k' : ℤ) • r = k • r := by
      refine ⟨(k % (addOrderOf r : ℤ)).toNat, ?_⟩
      have h0 : 0 ≤ k % (addOrderOf r : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hn.ne')
      rw [Int.toNat_of_nonneg h0]
      have : k % (addOrderOf r : ℤ) = k - (k / (addOrderOf r : ℤ)) * (addOrderOf r : ℤ) := by
        have := Int.emod_add_mul_ediv k (addOrderOf r : ℤ)
        have := mul_comm (addOrderOf r : ℤ) (k / (addOrderOf r : ℤ))
        omega
      rw [this, sub_zsmul, mul_zsmul, natCast_zsmul, addOrderOf_nsmul_eq_zero, zsmul_zero, neg_zero,
        add_zero]
    rw [← hk', natCast_zsmul]
    exact hinvn k' s
  let π : ZMod N → ZMod N ⧸ H := QuotientAddGroup.mk
  have hfib : ∀ c : ZMod N ⧸ H,
      ∑ s ∈ Finset.univ.filter (fun s => π s = c), f s = Nat.card H * f (Quotient.out c) := by
    intro c
    have hconst : ∀ s ∈ Finset.univ.filter (fun s => π s = c), f s = f (Quotient.out c) := by
      intro s hs
      rw [Finset.mem_filter] at hs
      have hπ : π (Quotient.out c) = c := Quotient.out_eq c
      have : π s = π (Quotient.out c) := hs.2.trans hπ.symm
      have hmem : -Quotient.out c + s ∈ H := QuotientAddGroup.eq.mp this.symm
      have := hinv _ hmem (Quotient.out c)
      rwa [add_neg_cancel_left] at this
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
    congr 1
    rw [← Nat.card_eq_finsetCard]
    have e : ↥H ≃ {s : ZMod N // s ∈ Finset.univ.filter (fun s => π s = c)} :=
      { toFun := fun h => ⟨Quotient.out c + h, by
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          have e1 : π (Quotient.out c) = c := Quotient.out_eq c
          have e2 : π (Quotient.out c + h) = π (Quotient.out c) := by
            apply Eq.symm
            apply QuotientAddGroup.eq.mpr
            rw [neg_add_cancel_left]; exact h.2
          exact e2.trans e1⟩
        invFun := fun s => ⟨-Quotient.out c + s.1, by
          have hs := s.2
          rw [Finset.mem_filter] at hs
          have : π s.1 = π (Quotient.out c) := hs.2.trans (Quotient.out_eq c).symm
          exact QuotientAddGroup.eq.mp this.symm⟩
        left_inv := fun h => by ext; simp
        right_inv := fun s => by ext; simp }
    exact (Nat.card_congr e).symm
  rw [← Finset.sum_fiberwise Finset.univ π f]
  have hcard : Nat.card H = addOrderOf r := Nat.card_zmultiples r
  rw [← hcard]
  apply Finset.dvd_sum
  intro c _
  rw [hfib c]
  exact dvd_mul_right _ _

/-- The gcd of `N` and `v` divides the weight `6 v² - 6 N v + N²`. -/
private theorem gcd_dvd_weight (N v : ℕ) :
    ((Nat.gcd N v : ℕ) : ℤ) ∣ 6 * (v : ℤ) ^ 2 - 6 * (N : ℤ) * (v : ℤ) + (N : ℤ) ^ 2 := by
  have h1 : ((Nat.gcd N v : ℕ) : ℤ) ∣ (v : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_right N v)
  have h2 : ((Nat.gcd N v : ℕ) : ℤ) ∣ (N : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.gcd_dvd_left N v)
  refine dvd_add (dvd_sub ?_ ?_) ?_
  · exact dvd_mul_of_dvd_right (dvd_pow h1 two_ne_zero) _
  · exact dvd_mul_of_dvd_right h1 _
  · exact dvd_pow h2 two_ne_zero

/-- `N` divides the total weight of an `r`-invariant exponent function: the `r`-sum is divisible by
`addOrderOf r`, the weight by `gcd N r`, and their product is `N`. -/
private theorem natCast_dvd_sum_weight {N : ℕ} [NeZero N] (m : ZMod N → ZMod N → ℕ)
    (hm : ∀ r s : ZMod N, m r (s + r) = m r s) :
    (N : ℤ) ∣ ∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
  apply Finset.dvd_sum
  intro r _
  rw [← Finset.sum_mul]
  have h1 : ((addOrderOf r : ℕ) : ℤ) ∣ ∑ s : ZMod N, (m r s : ℤ) := by
    have := addOrderOf_dvd_sum_of_invariant r (m r) (fun s => hm r s)
    have h := Int.natCast_dvd_natCast.mpr this
    push_cast at h
    exact h
  have h2 := gcd_dvd_weight N r.val
  have hN : (N : ℤ) = ((addOrderOf r : ℕ) : ℤ) * ((Nat.gcd N r.val : ℕ) : ℤ) := by
    have hr : (r : ZMod N) = ((r.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val r).symm
    have ho : addOrderOf r = N / Nat.gcd N r.val := by
      conv_lhs => rw [hr]
      exact ZMod.addOrderOf_coe r.val (NeZero.ne N)
    rw [ho]
    exact_mod_cast (Nat.div_mul_cancel (Nat.gcd_dvd_left N r.val)).symm
  have := mul_dvd_mul h1 h2
  rwa [← hN] at this

/-- Raising the scaling power keeps integrality: `N ^ a · z` integral implies `N ^ b · z` integral
for `a ≤ b`, since `N ^ (b - a)` is an integer. -/
private theorem isIntegral_pow_mul_of_le {N : ℕ} {a b : ℕ} (hab : a ≤ b) {z : ℂ}
    (h : IsIntegral ℤ ((N : ℂ) ^ a * z)) : IsIntegral ℤ ((N : ℂ) ^ b * z) := by
  have hN : IsIntegral ℤ ((N : ℂ) ^ (b - a)) := by
    have : IsIntegral ℤ (N : ℂ) := by
      have := isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ))
      simpa using this
    exact this.pow _
  have : (N : ℂ) ^ b * z = (N : ℂ) ^ (b - a) * ((N : ℂ) ^ a * z) := by
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hab]
  rw [this]
  exact hN.mul h

end PeakedAux

open scoped MatrixGroups ModularForm in
/-- **The peaked auxiliary form.**  For `N ≥ 2` there is a form `ϑ` on `Γ₁(N)`, of weight `w` with
`12 ∣ w`, whose width-`N` slashed coefficients and width-`1` coefficients are integral after
multiplying by `N ^ a`, whose width-`1` expansion starts at `m₀`, and whose every non-`Γ₁(N)` slash
decays like `exp (-2π (m₀ + δ) im)` with `δ > 0`. -/
theorem exists_gamma1_peaked_auxiliary_form_twelve_dvd (N : ℕ) (hN : 2 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      12 ∣ w ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  classical
  have : NeZero N := ⟨by omega⟩
  obtain ⟨m, Ord, hOrd, hm00, hminv, hpos, hpeak⟩ := exists_peaked_exponent N hN
  set t : ℕ := ∑ x : ZMod N, ∑ y : ZMod N, (Ord x y).natAbs with ht_def
  have hOrd_ge : ∀ x y : ZMod N, -(t : ℤ) ≤ Ord x y := by
    intro x y
    have h1 : (Ord x y).natAbs ≤ t := by
      rw [ht_def]
      exact (Finset.single_le_sum (f := fun y => (Ord x y).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ y)).trans
        (Finset.single_le_sum (f := fun x => ∑ y, (Ord x y).natAbs) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ x))
    have h2 : -((Ord x y).natAbs : ℤ) ≤ Ord x y := by
      rw [Int.natCast_natAbs]; exact neg_abs_le _
    omega
  have hNpos : (0 : ℤ) < N := by exact_mod_cast (show 0 < N by omega)
  have htN : ∀ x y : ZMod N, 0 ≤ Ord x y + (N : ℤ) * t := by
    intro x y
    have := hOrd_ge x y
    have ht0 : (0 : ℤ) ≤ t := by exact_mod_cast Nat.zero_le t
    nlinarith
  have htF : ∀ β : SL(2, ℤ), 0 ≤ (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) ^ 2
          - 6 * (N : ℤ) * ((r * ((β 0 0 : ℤ) : ZMod N) + s * ((β 1 0 : ℤ) : ZMod N)).val : ℤ) +
            (N : ℤ) ^ 2)) + (N : ℤ) * t := by
    intro β
    have := htN (((β 0 0 : ℤ) : ZMod N)) (((β 1 0 : ℤ) : ZMod N))
    rw [hOrd] at this
    exact this
  obtain ⟨ϑ, hϑ, hdecF⟩ :=
    exists_modularForm_gamma1_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m hm00 hminv t htF
  have hS1 : Ord 1 0 = ∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2) := by
    rw [hOrd]
    refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun s _ => ?_
    rw [mul_one, mul_zero, add_zero]
  have hdvd : (N : ℤ) ∣ Ord 1 0 + (N : ℤ) * t := by
    rw [hS1]; exact dvd_add (PeakedAux.natCast_dvd_sum_weight m hminv) (dvd_mul_right _ _)
  obtain ⟨M, hM⟩ := hdvd
  have hMpos : (t : ℤ) < M := by
    have : (N : ℤ) * t < (N : ℤ) * M := by rw [← hM]; linarith
    exact lt_of_mul_lt_mul_left this hNpos.le
  have hM0 : 0 ≤ M := by
    have : (0 : ℤ) ≤ t := by exact_mod_cast Nat.zero_le t
    omega
  obtain ⟨m₀, hm₀M⟩ : ∃ m₀ : ℕ, (m₀ : ℤ) = M := ⟨M.toNat, Int.toNat_of_nonneg hM0⟩
  have hm₀eq : (N : ℤ) * m₀ = (∑ r : ZMod N, ∑ s : ZMod N,
      (m r s : ℤ) * (6 * (r.val : ℤ) ^ 2 - 6 * (N : ℤ) * (r.val : ℤ) + (N : ℤ) ^ 2)) +
        (N : ℤ) * t := by
    rw [hm₀M, ← hM, hS1]
  obtain ⟨a₁, hz, hne, hinv₁, hint₁⟩ :=
    qExpansion_one_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m hm00 t ϑ hϑ m₀ hm₀eq
  obtain ⟨a₂, hint₂⟩ :=
    isIntegral_qExpansion_slash_S_coeff_of_coe_eq_prod_siegelFun_pow_mul_discriminant_pow N m t ϑ hϑ
  refine ⟨12 * (t : ℤ), m₀, max a₁ a₂, 1 / (N : ℝ), ϑ, dvd_mul_right _ _, ?_, ?_, ?_, hz, hne, ?_,
    ?_, ?_⟩
  · have : (t : ℤ) < m₀ := by rw [hm₀M]; exact hMpos
    linarith
  · have : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    positivity
  · intro n; exact PeakedAux.isIntegral_pow_mul_of_le (le_max_right _ _) (hint₂ n)
  · exact PeakedAux.isIntegral_pow_mul_of_le (le_max_left _ _) hinv₁
  · intro n; exact PeakedAux.isIntegral_pow_mul_of_le (le_max_left _ _) (hint₁ n)
  · intro β hβ1 hβ2
    obtain ⟨hc1, hc2, hprim⟩ :=
      CongruenceSubgroup.mem_or_neg_mem_Gamma1_iff_and_exists_T_zpow_S_inv_iff N β
    set x : ZMod N := ((β 0 0 : ℤ) : ZMod N) with hx
    set y : ZMod N := ((β 1 0 : ℤ) : ZMod N) with hy
    have hnot1 : ¬ (y = 0 ∧ (x = 1 ∨ x = -1)) := fun h => (not_or.mpr hβ1) (hc1.mpr h)
    have hnot2 : ¬ (y = 1 ∨ y = -1) := fun h => by
      obtain ⟨j, hj⟩ := hc2.mpr h
      exact (not_or.mpr (hβ2 j)) hj
    have hlt : Ord 1 0 < Ord x y := hpeak x y hprim hnot1 hnot2
    refine (hdecF β).trans ?_
    refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun τ => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.abs_exp, Real.abs_exp, Real.exp_le_exp]
    have hsum : (∑ r : ZMod N, ∑ s : ZMod N, (m r s : ℤ) *
        (6 * ((r * x + s * y).val : ℤ) ^ 2 - 6 * (N : ℤ) * ((r * x + s * y).val : ℤ) +
          (N : ℤ) ^ 2)) = Ord x y := (hOrd x y).symm
    rw [hsum]
    have hτ : 0 ≤ τ.im := τ.im_pos.le
    have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hkey : (m₀ : ℝ) + 1 / (N : ℝ) ≤ ((Ord x y : ℤ) : ℝ) / (N : ℝ) + (t : ℝ) := by
      have hZ : (N : ℤ) * m₀ + 1 ≤ Ord x y + (N : ℤ) * t := by
        rw [hm₀M, ← hM]; omega
      have hR : (N : ℝ) * m₀ + 1 ≤ ((Ord x y : ℤ) : ℝ) + (N : ℝ) * t := by exact_mod_cast hZ
      rw [← sub_nonneg]
      have : ((Ord x y : ℤ) : ℝ) / N + t - ((m₀ : ℝ) + 1 / N) =
          (((Ord x y : ℤ) : ℝ) + N * t - (N * m₀ + 1)) / N := by
        field_simp
      rw [this]
      exact div_nonneg (by linarith) hNr.le
    have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    have h2 : 2 * Real.pi * ((m₀ : ℝ) + 1 / (N : ℝ)) ≤
        2 * Real.pi * (((Ord x y : ℤ) : ℝ) / (N : ℝ) + (t : ℝ)) :=
      mul_le_mul_of_nonneg_left hkey hπ
    exact mul_le_mul_of_nonneg_right (neg_le_neg h2) hτ

end SiegelUnit

/-! ## The same auxiliary form at an arbitrary weight

The pin's `ModularCurve.exists_gamma1_peaked_auxiliary_form` (249 lines) frees the weight
normalisation of the row above: `Even (k + w)` in place of `12 ∣ w`, so that `ϑ` can be multiplied
into a form of weight `k`. The proof is one case split on the parity of `k`. For even `k` the weight
`w` above already has the right parity, with `k + w = 2 (k/2 + 6 c)` for `w = 12 c`. For odd `k`
(hence `3 ≤ N`) it multiplies `ϑ` by the weight-three Eisenstein form of `SiegelUnit/Eisenstein.lean`,
whose width-`1` constant coefficient is a unit up to `N ^ b` and whose `S`-slash is again
`N`-integral: the product keeps every coefficient fact with the exponents added, gains the weight
`w + 3` (odd + odd is even), and keeps the peak estimate because a slash of a form bounded at `i∞`
is bounded. -/

namespace PeakedAuxW

open UpperHalfPlane

/-- The cusp function of `ϑ ∣[w] S` is analytic at `0`: the slash is the form `Thetaform ϑ` on the
`S`-conjugate group `GammaS N`, and `N` is a strict period of that group. -/
private theorem analyticAt_cuspFunction_slash_S {N : ℕ} [NeZero N] {w : ℤ}
    (ϑ : ModularForm ((CongruenceSubgroup.Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) w) :
    AnalyticAt ℂ (cuspFunction (N : ℝ)
      ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))) 0 := by
  rw [← SiegelUnit.IntZero.coe_Thetaform ϑ]
  exact ModularFormClass.analyticAt_cuspFunction_zero (SiegelUnit.IntZero.Thetaform ϑ)
    (Nat.cast_pos.mpr (NeZero.pos N)) (SiegelUnit.IntZero.natCast_mem_strictPeriods_GammaS N)

/-- The `m₀`-th coefficient of a product, when the left factor vanishes below `m₀`. -/
private theorem coeff_mul_of_coeff_lt_eq_zero {φ ψ : PowerSeries ℂ} {m₀ : ℕ}
    (h : ∀ n : ℕ, n < m₀ → φ.coeff n = 0) :
    (φ * ψ).coeff m₀ = φ.coeff m₀ * ψ.coeff 0 := by
  rw [PowerSeries.coeff_mul, Finset.sum_eq_single (m₀, 0)]
  · intro p hp hne
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hlt : p.1 < m₀ := by
      rcases lt_or_ge p.1 m₀ with h' | h'
      · exact h'
      · exfalso
        apply hne
        have h1 : p.1 = m₀ := by omega
        have h2 : p.2 = 0 := by omega
        exact Prod.ext h1 h2
    rw [h p.1 hlt, zero_mul]
  · intro hn
    exact absurd (Finset.HasAntidiagonal.mem_antidiagonal.mpr (by simp)) hn

/-- The same for every coefficient below `m₀`. -/
private theorem coeff_mul_eq_zero_of_lt {φ ψ : PowerSeries ℂ} {m₀ n : ℕ}
    (h : ∀ n : ℕ, n < m₀ → φ.coeff n = 0) (hn : n < m₀) :
    (φ * ψ).coeff n = 0 := by
  rw [PowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [h p.1 (by omega), zero_mul]

/-- The product of two power series whose coefficients are integral after scaling by `N ^ a` and
`N ^ b` has coefficients integral after scaling by `N ^ (a + b)`. -/
private theorem isIntegral_pow_mul_coeff_mul {φ ψ : PowerSeries ℂ} {N a b : ℕ}
    (hφ : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * φ.coeff n))
    (hψ : ∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ b * ψ.coeff n)) (n : ℕ) :
    IsIntegral ℤ ((N : ℂ) ^ (a + b) * (φ * ψ).coeff n) := by
  rw [PowerSeries.coeff_mul, Finset.mul_sum]
  refine IsIntegral.sum _ fun p _ => ?_
  have e : (N : ℂ) ^ (a + b) * (φ.coeff p.1 * ψ.coeff p.2) =
      ((N : ℂ) ^ a * φ.coeff p.1) * ((N : ℂ) ^ b * ψ.coeff p.2) := by
    rw [pow_add]; ring
  rw [e]
  exact (hφ p.1).mul (hψ p.2)

/-- The slash of a product is the product of the slashes. -/
private theorem coe_mul_slash {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.HasDetPlusMinusOne] {k₁ k₂ : ℤ}
    (f : ModularForm Γ k₁) (g : ModularForm Γ k₂) (β : SL(2, ℤ)) :
    ((⇑(f.mul g) : UpperHalfPlane → ℂ) ∣[k₁ + k₂] (β : GL (Fin 2) ℝ)) =
      ((⇑f : UpperHalfPlane → ℂ) ∣[k₁] (β : GL (Fin 2) ℝ)) *
        ((⇑g : UpperHalfPlane → ℂ) ∣[k₂] (β : GL (Fin 2) ℝ)) := by
  rw [ModularForm.coe_mul]
  exact ModularForm.mul_slash_SL2 k₁ k₂ β _ _

end PeakedAuxW

open PeakedAuxW in
open scoped MatrixGroups ModularForm in
open UpperHalfPlane in
/-- **The peaked auxiliary form at any weight.**  For `N ≥ 2`, a form `ϑ` on `Γ₁(N)` of weight `w`
with `Even (k + w)` — so that `ϑ` multiplies into weight `k` — whose width-`N` slashed coefficients
and width-`1` coefficients are integral after scaling by `N ^ a`, whose width-`1` expansion starts at
`m₀`, and whose non-`Γ₁(N)` slashes peak at `m₀ + δ`. -/
theorem exists_gamma1_peaked_auxiliary_form (N : ℕ) (hN : 2 ≤ N) (k : ℤ) (hk : Odd k → 3 ≤ N) :
    ∃ (w : ℤ) (m₀ a : ℕ) (δ : ℝ)
      (ϑ : ModularForm (CongruenceSubgroup.Gamma1 N : Subgroup (GL (Fin 2) ℝ)) w),
      Even (k + w) ∧ w < 12 * (m₀ : ℤ) ∧ 0 < δ ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a * (UpperHalfPlane.qExpansion (N : ℝ)
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ))).coeff n)) ∧
      (∀ n : ℕ, n < m₀ → (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n = 0) ∧
      (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀ ≠ 0 ∧
      IsIntegral ℤ ((N : ℂ) ^ a *
        ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) ∧
      (∀ n : ℕ, IsIntegral ℤ ((N : ℂ) ^ a *
        (UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff n)) ∧
      ∀ β : SL(2, ℤ),
        (β ∉ CongruenceSubgroup.Gamma1 N ∧ -β ∉ CongruenceSubgroup.Gamma1 N) →
        (∀ j : ℤ, β * ModularGroup.T ^ j * ModularGroup.S⁻¹ ∉ CongruenceSubgroup.Gamma1 N ∧
          -(β * ModularGroup.T ^ j * ModularGroup.S⁻¹) ∉ CongruenceSubgroup.Gamma1 N) →
        ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] (β : GL (Fin 2) ℝ)) =O[UpperHalfPlane.atImInfty]
          fun τ : UpperHalfPlane => Real.exp (-(2 * Real.pi * ((m₀ : ℝ) + δ)) * τ.im) := by
  have : NeZero N := ⟨by omega⟩
  obtain ⟨w, m₀, a, δ, ϑ, h12, hw, hδ, h1, h2a, h2b, h2c, h2d, h3⟩ :=
    SiegelUnit.exists_gamma1_peaked_auxiliary_form_twelve_dvd N hN
  obtain ⟨c, hc⟩ := h12
  rcases Int.even_or_odd k with hke | hko
  · obtain ⟨r, hr⟩ := hke
    exact ⟨w, m₀, a, δ, ϑ, ⟨r + 6 * c, by omega⟩, hw, hδ, h1, h2a, h2b, h2c, h2d, h3⟩
  · have hN3 : 3 ≤ N := hk hko
    obtain ⟨E, b, hE1, hE0, hEinv, hES⟩ :=
      SiegelUnit.exists_modularForm_gamma1_weight_three_isIntegral_qExpansion N hN3
    obtain ⟨j, hj⟩ := hko
    have hq1 : UpperHalfPlane.qExpansion 1 (⇑(ϑ.mul E) : UpperHalfPlane → ℂ) =
        UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ) *
          UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ) :=
      ModularForm.qExpansion_mul one_pos (ModularForm.Level.one_mem_strictPeriods N) ϑ E
    have hqN : UpperHalfPlane.qExpansion (N : ℝ)
          ((⇑(ϑ.mul E) : UpperHalfPlane → ℂ) ∣[w + 3] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        UpperHalfPlane.qExpansion (N : ℝ)
            ((⇑ϑ : UpperHalfPlane → ℂ) ∣[w] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) *
          UpperHalfPlane.qExpansion (N : ℝ)
            ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] ((ModularGroup.S : SL(2, ℤ)) : GL (Fin 2) ℝ)) := by
      rw [coe_mul_slash ϑ E ModularGroup.S]
      exact UpperHalfPlane.qExpansion_mul (analyticAt_cuspFunction_slash_S ϑ)
        (analyticAt_cuspFunction_slash_S E)
    refine ⟨w + 3, m₀, a + b, δ, ϑ.mul E, ⟨j + 6 * c + 2, by omega⟩, by omega, hδ,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      rw [hqN]
      exact isIntegral_pow_mul_coeff_mul h1 hES n
    · intro n hn
      rw [hq1]
      exact coeff_mul_eq_zero_of_lt h2a hn
    · rw [hq1, coeff_mul_of_coeff_lt_eq_zero h2a]
      exact mul_ne_zero h2b hE0
    · rw [hq1, coeff_mul_of_coeff_lt_eq_zero h2a, mul_inv, pow_add]
      have e : (N : ℂ) ^ a * (N : ℂ) ^ b *
          (((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹ *
            ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) =
          ((N : ℂ) ^ a * ((UpperHalfPlane.qExpansion 1 (⇑ϑ : UpperHalfPlane → ℂ)).coeff m₀)⁻¹) *
            ((N : ℂ) ^ b * ((UpperHalfPlane.qExpansion 1 (⇑E : UpperHalfPlane → ℂ)).coeff 0)⁻¹) := by
        ring
      rw [e]
      exact h2c.mul hEinv
    · intro n
      rw [hq1]
      exact isIntegral_pow_mul_coeff_mul h2d hE1 n
    · intro β hβ hβ0
      rw [coe_mul_slash ϑ E β]
      have hE : UpperHalfPlane.IsBoundedAtImInfty
          ((⇑E : UpperHalfPlane → ℂ) ∣[(3 : ℤ)] (β : GL (Fin 2) ℝ)) :=
        ModularFormClass.bdd_at_infty_slash E β
      exact ((h3 β hβ hβ0).mul hE).congr (fun _ => rfl) (fun _ => mul_one _)

end ModularCurve
