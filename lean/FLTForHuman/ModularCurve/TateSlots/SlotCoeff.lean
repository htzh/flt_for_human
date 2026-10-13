/-
  The slot-coefficient engine of the Tate-slot weight-4 development: the base
  faces of `tateBase`, the substitution API (`slotFamily` / `slotSubst`), the
  elementary combinatorics `SpecS0`–`SpecS4` (`toFin2`, `reidxLineSet`,
  `coeff_subst_pair`, `coeff_slotSubst`, `coeff_slotSubst_diag`), the toric
  coefficient formulas (`ToricFaces`, `ToricCoeffs`), the `W4Bdev` slot-substitution
  coefficients (`coeff_slotSubst_eq_boxSum`, `boxSum_eq_head_add_doubleSum`,
  `coeff_slotSubst_tateUnivX` / `_tateUnivY`, `slotSubst_gen_injective`), and the
  head / Laurent closed forms (`GeomHeads`, `Laurent`).

  FLT provenance, pinned `aa2d8b3`: the shared development carried by the
  fourteen `P2M/Sol/S_ModularCurve_*.lean` files; the representative
  transcription source is
  `P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean` (1,649 lines), sections
  `BaseFaces` (19–51), `SlotSubstAPI` (53–78), `SpecS0`–`SpecS4` (80–284),
  `ToricFaces` (767–781), `ToricCoeffs` (784–889), `W4Bdev.Abstract` (894–942),
  `W4Bdev` (945–1003), `EngineAux1` (1008–1039), `W4Bdev.Bridge` (1042–1421),
  `GeomHeads` (1427–1587) and `Laurent` (1590–1635).
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean

  Transcribed whole (playbook §2.3); the pin's `p2m_*` commands and outer
  `P2MW.S_ModularCurve_tsum_of_coeff_lt_eq_zero` frame are dropped —
  `Defs/TateSlots.lean` already provides the definitions in `ModularCurve`. The
  pin's duplicate `ofPowerSeries_coeff_neg` / `ofPowerSeries_coeff_int`
  (`ModularCurve.OfPowerSeriesInt`, 744–764) is deliberately not re-declared here
  (work order §3.4); it lives once in `Convergence.lean`. The twelve headline
  kernels of this module are promoted to public `ModularCurve.TateSlots.<name>`
  with the binders of their `Theorems/` wrappers.
-/
import FLTForHuman.ModularCurve.Defs.TateSlots
import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Basic

set_option autoImplicit false

noncomputable section

open PowerSeries HahnSeries

namespace ModularCurve

section BaseFaces

variable (K : Type*) [CommRing K] (p : ℕ) [NeZero p]

-- pin: tateBase_a₁ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:23)
theorem tateBase_a₁ : (tateBase K p).a₁ = 1 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₁, tatePowerSeries_a₁, map_one]

-- pin: tateBase_a₂ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:26)
theorem tateBase_a₂ : (tateBase K p).a₂ = 0 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₂, tatePowerSeries_a₂, map_zero]

-- pin: tateBase_a₃ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:29)
theorem tateBase_a₃ : (tateBase K p).a₃ = 0 := by
  simp only [tateBase, tateLaurent, WeierstrassCurve.map_a₃, tatePowerSeries_a₃, map_zero]

-- pin: tateBase_a₄ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:32)
theorem tateBase_a₄ : (tateBase K p).a₄ = qExpand K p (laurentOfInt K tateA4) := by
  simp only [tateBase, WeierstrassCurve.map_a₄, tateLaurent_a₄]

-- pin: tateBase_a₆ (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:35)
theorem tateBase_a₆ : (tateBase K p).a₆ = qExpand K p (laurentOfInt K tateA6) := by
  simp only [tateBase, WeierstrassCurve.map_a₆, tateLaurent_a₆]

namespace TateSlots

-- pin: ModularCurve.equation_tateBase_iff (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:38)
theorem equation_tateBase_iff (x y : LaurentSeries K) :
    (tateBase K p).toAffine.Equation x y ↔
      y ^ 2 + x * y = x ^ 3 + qExpand K p (laurentOfInt K tateA4) * x
        + qExpand K p (laurentOfInt K tateA6) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  have e1 : (tateBase K p).toAffine.a₁ = 1 := tateBase_a₁ K p
  have e2 : (tateBase K p).toAffine.a₂ = 0 := tateBase_a₂ K p
  have e3 : (tateBase K p).toAffine.a₃ = 0 := tateBase_a₃ K p
  have e4 : (tateBase K p).toAffine.a₄ = qExpand K p (laurentOfInt K tateA4) := tateBase_a₄ K p
  have e6 : (tateBase K p).toAffine.a₆ = qExpand K p (laurentOfInt K tateA6) := tateBase_a₆ K p
  rw [e1, e2, e3, e4, e6]
  constructor <;> intro h <;> linear_combination h

end TateSlots

end BaseFaces

section SlotSubstAPI

variable (K : Type*) [CommRing K]

-- pin: hasSubst_slotFamily (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:57)
theorem hasSubst_slotFamily (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries.HasSubst (slotFamily K p c j) := by
  refine MvPowerSeries.hasSubst_of_constantCoeff_zero ?_
  intro s
  fin_cases s
  · show PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  · show PowerSeries.constantCoeff (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp), mul_zero]

-- pin: slotHom (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:67)
def slotHom (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    MvPowerSeries (Fin 2) ℤ →+* LaurentSeries K :=
  (HahnSeries.ofPowerSeries ℤ K).comp
    (MvPowerSeries.substAlgHom (hasSubst_slotFamily K p c j hj hjp)).toRingHom

-- pin: slotHom_apply (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:72)
theorem slotHom_apply (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) :
    slotHom K p c j hj hjp f = HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) := by
  simp only [slotHom, slotSubst, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    MvPowerSeries.substAlgHom_apply]

end SlotSubstAPI

section SpecS0

-- pin: reidxLineSet (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:82)
def reidxLineSet (a b N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1) ×ˢ Finset.range (N+1)).filter fun e => a * e.1 + b * e.2 = N

-- pin: toFin2 (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:85)
def toFin2 (e : ℕ × ℕ) : Fin 2 →₀ ℕ := Finsupp.equivFunOnFinite.symm ![e.1, e.2]

-- pin: toFin2_apply_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:87)
@[scoped simp] theorem toFin2_apply_zero (e : ℕ × ℕ) : toFin2 e 0 = e.1 := by simp [toFin2]

-- pin: toFin2_apply_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:89)
@[scoped simp] theorem toFin2_apply_one (e : ℕ × ℕ) : toFin2 e 1 = e.2 := by simp [toFin2]

-- pin: toFin2_injective (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:91)
theorem toFin2_injective : Function.Injective toFin2 := by
  intro x y h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  simp only [toFin2_apply_zero, toFin2_apply_one] at h0 h1
  exact Prod.ext h0 h1

-- pin: toFin2_pair (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:98)
theorem toFin2_pair (d : Fin 2 →₀ ℕ) : toFin2 (d 0, d 1) = d := by
  ext i
  fin_cases i
  · exact toFin2_apply_zero _
  · exact toFin2_apply_one _

-- pin: mem_reidxLineSet (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:104)
theorem mem_reidxLineSet {a b N : ℕ} (ha : 0 < a) (hb : 0 < b) {e : ℕ × ℕ} :
    e ∈ reidxLineSet a b N ↔ a * e.1 + b * e.2 = N := by
  simp only [reidxLineSet, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
    and_iff_right_iff_imp]
  intro h
  have h1 : e.1 ≤ a * e.1 := Nat.le_mul_of_pos_left _ ha
  have h2 : e.2 ≤ b * e.2 := Nat.le_mul_of_pos_left _ hb
  exact ⟨Nat.lt_succ_of_le (h1.trans (le_of_le_of_eq (Nat.le_add_right _ _) h)),
    Nat.lt_succ_of_le (h2.trans (le_of_le_of_eq (Nat.le_add_left _ _) h))⟩

end SpecS0

section SpecS1

-- pin: prod_pow_fin_two (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:118)
theorem prod_pow_fin_two {M : Type*} [CommMonoid M] (a : Fin 2 → M) (d : Fin 2 →₀ ℕ) :
    (d.prod fun s n => a s ^ n) = a 0 ^ (d 0) * a 1 ^ (d 1) := by
  rw [Finsupp.prod_fintype d (fun s n => a s ^ n) fun _ => pow_zero _, Fin.prod_univ_two]

-- pin: coeff_subst_pair (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:122)
theorem coeff_subst_pair {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A B : PowerSeries S) (hA : PowerSeries.constantCoeff A = 0)
    (hB : PowerSeries.constantCoeff B = 0) (f : MvPowerSeries (Fin 2) R) (N : ℕ) :
    PowerSeries.coeff N (MvPowerSeries.subst ![A, B] f : PowerSeries S) =
      ∑ e ∈ Finset.range (N + 1) ×ˢ Finset.range (N + 1),
        MvPowerSeries.coeff (toFin2 e) f • PowerSeries.coeff N (A ^ e.1 * B ^ e.2) := by
  have ha : MvPowerSeries.HasSubst (![A, B] : Fin 2 → PowerSeries S) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun s => by
      fin_cases s
      · exact hA
      · exact hB
  have key : ∀ d : Fin 2 →₀ ℕ, ¬(d 0 ≤ N ∧ d 1 ≤ N) →
      PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0 := by
    intro d hd
    obtain ⟨A', hA'⟩ := PowerSeries.X_dvd_iff.mpr hA
    obtain ⟨B', hB'⟩ := PowerSeries.X_dvd_iff.mpr hB
    rw [hA', hB', mul_pow, mul_pow, mul_mul_mul_comm, ← _root_.pow_add, PowerSeries.coeff_X_pow_mul',
      ite_eq_right (by omega)]
  change MvPowerSeries.coeff (Finsupp.single () N) (MvPowerSeries.subst ![A, B] f) = _
  rw [MvPowerSeries.coeff_subst ha,
    finsum_eq_sum_of_support_subset _
      (s := (Finset.range (N + 1) ×ˢ Finset.range (N + 1)).image toFin2)]
  · rw [Finset.sum_image fun x _ y _ h => toFin2_injective h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff (toFin2 e) f •
        PowerSeries.coeff N (A ^ (toFin2 e 0) * B ^ (toFin2 e 1)) = _
    rw [toFin2_apply_zero, toFin2_apply_one]
  · intro d hd
    rw [Function.mem_support] at hd
    rw [Finset.coe_image, Set.mem_image]
    refine ⟨(d 0, d 1), ?_, toFin2_pair d⟩
    rw [Finset.mem_coe, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    by_contra hbox
    apply hd
    rw [prod_pow_fin_two]
    change MvPowerSeries.coeff d f • PowerSeries.coeff N (A ^ (d 0) * B ^ (d 1)) = 0
    rw [key d (by omega), smul_zero]

end SpecS1

section SpecS2

variable (K : Type*) [CommRing K]

-- pin: coeff_slotSubst (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:167)
theorem coeff_slotSubst (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      ∑ e ∈ reidxLineSet j (p - j) N,
        ((f (toFin2 e) : ℤ) : K) * ((c ^ e.1 * c⁻¹ ^ e.2 : Kˣ) : K) := by
  have hA : PowerSeries.constantCoeff (PowerSeries.C (c : K) * PowerSeries.X ^ j) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow hj.ne', mul_zero]
  have hB : PowerSeries.constantCoeff
      (PowerSeries.C ((c⁻¹ : Kˣ) : K) * PowerSeries.X ^ (p - j)) = 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (Nat.sub_ne_zero_of_lt hjp),
      mul_zero]
  rw [slotSubst, slotFamily, coeff_subst_pair _ _ hA hB, reidxLineSet, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_mul_mul_comm, ← map_mul,
    ← _root_.pow_add, PowerSeries.coeff_C_mul_X_pow]
  by_cases h : j * e.1 + (p - j) * e.2 = N
  · rw [ite_eq_left h.symm, ite_eq_left h, Algebra.smul_def, eq_intCast, MvPowerSeries.coeff_apply,
      Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, smul_zero]

end SpecS2

section SpecS3

variable (K : Type*) [CommRing K]

-- pin: coeff_slotSubst_diag (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:193)
theorem coeff_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) (N : ℕ) :
    PowerSeries.coeff N (slotSubst K p c j f) =
      if p ∣ N then ((PowerSeries.coeff (N / p) g : ℤ) : K) else 0 := by
  have hpj : 0 < p - j := Nat.sub_pos_of_lt hjp
  have hline : ∀ m : ℕ, j * m + (p - j) * m = p * m := fun m => by
    rw [← add_mul, Nat.add_sub_cancel' hjp.le]
  rw [coeff_slotSubst K p c j hj hjp]
  by_cases hN : p ∣ N
  · obtain ⟨m, rfl⟩ := hN
    rw [ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p),
      Finset.sum_eq_single_of_mem (m, m) ((mem_reidxLineSet hj hpj).mpr (hline m))]
    · rw [hf, toFin2_apply_zero, toFin2_apply_one, ite_eq_left rfl, ← mul_pow, mul_inv_cancel, one_pow,
        Units.val_one, mul_one]
    · intro e he hne
      have h := (mem_reidxLineSet hj hpj).mp he
      rw [hf, toFin2_apply_zero, toFin2_apply_one]
      by_cases h01 : e.1 = e.2
      · exfalso
        refine hne (Prod.ext ?_ ?_)
        · change e.1 = m
          rw [h01, hline e.2] at h
          exact h01.trans (Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h)
        · change e.2 = m
          rw [h01, hline e.2] at h
          exact Nat.eq_of_mul_eq_mul_left (NeZero.pos p) h
      · rw [ite_eq_right h01, Int.cast_zero, zero_mul]
  · rw [ite_eq_right hN]
    refine Finset.sum_eq_zero fun e he => ?_
    have h := (mem_reidxLineSet hj hpj).mp he
    rw [hf, toFin2_apply_zero, toFin2_apply_one]
    by_cases h01 : e.1 = e.2
    · exfalso
      rw [h01, hline e.2] at h
      exact hN ⟨e.2, h.symm⟩
    · rw [ite_eq_right h01, Int.cast_zero, zero_mul]

-- pin: ofPowerSeries_slotSubst_diag (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:231)
theorem ofPowerSeries_slotSubst_diag (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) (f : MvPowerSeries (Fin 2) ℤ) (g : PowerSeries ℤ)
    (hf : ∀ e : Fin 2 →₀ ℕ, f e = if e 0 = e 1 then PowerSeries.coeff (e 0) g else 0) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j f) = qExpand K p (laurentOfInt K g) := by
  ext n
  by_cases hpn : (p : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hpn
    rw [qExpand_coeff_mul, laurentOfInt_apply]
    rcases lt_or_ge k 0 with hk | hk
    · rw [ofPowerSeries_coeff_of_neg _ hk, ofPowerSeries_coeff_of_neg _
        (mul_neg_of_pos_of_neg (by exact_mod_cast NeZero.pos p) hk)]
    · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
      rw [show (p : ℤ) * (m : ℤ) = ((p * m : ℕ) : ℤ) by push_cast; rfl,
        HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
        PowerSeries.coeff_map, coeff_slotSubst_diag K p c j hj hjp f g hf,
        ite_eq_left (dvd_mul_right p m), Nat.mul_div_cancel_left m (NeZero.pos p), eq_intCast]
  · rw [qExpand_coeff_of_not_dvd p _ hpn]
    rcases lt_or_ge n 0 with hn | hn
    · exact ofPowerSeries_coeff_of_neg _ hn
    · obtain ⟨N, rfl⟩ := Int.eq_ofNat_of_zero_le hn
      rw [HahnSeries.ofPowerSeries_apply_coeff, coeff_slotSubst_diag K p c j hj hjp f g hf,
        ite_eq_right (fun h => hpn (Int.natCast_dvd_natCast.mpr h))]

-- pin: ofPowerSeries_slotSubst_tateUnivA4 (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:254)
theorem ofPowerSeries_slotSubst_tateUnivA4 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA4) = (tateBase K p).a₄ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA4 tateA4 fun _ => rfl).trans rfl

-- pin: ofPowerSeries_slotSubst_tateUnivA6 (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:259)
theorem ofPowerSeries_slotSubst_tateUnivA6 (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) :
    HahnSeries.ofPowerSeries ℤ K (slotSubst K p c j tateUnivA6) = (tateBase K p).a₆ :=
  (ofPowerSeries_slotSubst_diag K p c j hj hjp tateUnivA6 tateA6 fun _ => rfl).trans rfl

end SpecS3

section SpecS4

variable (K : Type*) [CommRing K]

-- pin: tateUnivCurve_map_slotHom (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:270)
theorem tateUnivCurve_map_slotHom (p : ℕ) [NeZero p] (c : Kˣ) (j : ℕ) (hj : 0 < j)
    (hjp : j < p) : tateUnivCurve.map (slotHom K p c j hj hjp) = tateBase K p := by
  refine WeierstrassCurve.ext ?_ ?_ ?_ ?_ ?_
  · change slotHom K p c j hj hjp 1 = qExpand K p (laurentOfInt K 1)
    simp only [map_one]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp 0 = qExpand K p (laurentOfInt K 0)
    simp only [map_zero]
  · change slotHom K p c j hj hjp tateUnivA4 = (tateBase K p).a₄
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA4 K p c j hj hjp]
  · change slotHom K p c j hj hjp tateUnivA6 = (tateBase K p).a₆
    rw [slotHom_apply, ofPowerSeries_slotSubst_tateUnivA6 K p c j hj hjp]

end SpecS4

section ToricFaces

variable (K : Type*) [Field K] (p : ℕ)

namespace TateSlots

-- pin: ModularCurve.toricPoint_fst_coeff_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:771)
theorem toricPoint_fst_coeff_zero (c : K) : (toricPoint K p c).1.coeff 0 = c / (1 - c) ^ 2 := by
  rw [toricPoint_fst, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk]
  simp

-- pin: ModularCurve.toricPoint_snd_coeff_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:776)
theorem toricPoint_snd_coeff_zero (c : K) : (toricPoint K p c).2.coeff 0 = c ^ 2 / (1 - c) ^ 3 := by
  rw [toricPoint_snd, show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_mk]
  simp

end TateSlots

end ToricFaces

section ToricCoeffs

variable (K : Type*) [Field K] (p : ℕ)

-- pin: toricPoint_fst_coeff_natCast (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:788)
theorem toricPoint_fst_coeff_natCast (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K p c).1.coeff (m : ℤ) =
      (∑ d ∈ m.divisors, if p ∣ d then ((m / d : ℕ) : K) * (c ^ (m / d) + c⁻¹ ^ (m / d)) else 0)
        - 2 * (if p ∣ m then ((∑ e ∈ (m / p).divisors, (e : ℕ)) : K) else 0) := by
  simp only [toricPoint_fst, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, ite_eq_right hm]

-- pin: toricPoint_snd_coeff_natCast (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:794)
theorem toricPoint_snd_coeff_natCast (c : K) {m : ℕ} (hm : m ≠ 0) :
    (toricPoint K p c).2.coeff (m : ℤ) =
      (∑ d ∈ m.divisors, if p ∣ d then
          ((m / d).choose 2 : K) * c ^ (m / d) - ((m / d + 1).choose 2 : K) * c⁻¹ ^ (m / d) else 0)
        + (if p ∣ m then ((∑ e ∈ (m / p).divisors, (e : ℕ)) : K) else 0) := by
  simp only [toricPoint_snd, HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mk, ite_eq_right hm]

namespace TateSlots

-- pin: ModularCurve.toricPoint_fst_coeff_of_not_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:801)
theorem toricPoint_fst_coeff_of_not_dvd (c : K) {m : ℕ} (hpm : ¬ p ∣ m) :
    (toricPoint K p c).1.coeff (m : ℤ) = 0 := by
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  rw [toricPoint_fst_coeff_natCast K p c hm, ite_eq_right hpm, mul_zero, sub_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [ite_eq_right]
  exact fun hpd => hpm (hpd.trans (Nat.mem_divisors.mp hd).1)

-- pin: ModularCurve.toricPoint_snd_coeff_of_not_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:809)
theorem toricPoint_snd_coeff_of_not_dvd (c : K) {m : ℕ} (hpm : ¬ p ∣ m) :
    (toricPoint K p c).2.coeff (m : ℤ) = 0 := by
  have hm : m ≠ 0 := fun h => hpm (h ▸ dvd_zero p)
  rw [toricPoint_snd_coeff_natCast K p c hm, ite_eq_right hpm, add_zero]
  refine Finset.sum_eq_zero fun d hd => ?_
  rw [ite_eq_right]
  exact fun hpd => hpm (hpd.trans (Nat.mem_divisors.mp hd).1)

end TateSlots

-- pin: sum_divisors_mul_ite_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:817)
theorem sum_divisors_mul_ite_dvd {β : Type*} [AddCommMonoid β] (hp : 0 < p) (M : ℕ) (F : ℕ → β) :
    (∑ d ∈ (p * M).divisors, if p ∣ d then F d else 0) = ∑ d' ∈ M.divisors, F (p * d') := by
  rw [← Finset.sum_filter]
  have hset : (p * M).divisors.filter (fun d => p ∣ d) = M.divisors.image (fun d' => p * d') := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hd, hpM⟩, d', rfl⟩
      exact ⟨d', ⟨(Nat.mul_dvd_mul_iff_left hp).mp hd, fun h => hpM (by rw [h, mul_zero])⟩, rfl⟩
    · rintro ⟨d', ⟨hd', hM⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left p hd', mul_ne_zero hp.ne' hM⟩, d', rfl⟩
  rw [hset, Finset.sum_image]
  intro x _ y _ h
  exact Nat.eq_of_mul_eq_mul_left hp h

namespace TateSlots

-- pin: ModularCurve.toricPoint_fst_coeff_mul (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:832)
theorem toricPoint_fst_coeff_mul (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).1.coeff ((p * M : ℕ) : ℤ) = ∑ e ∈ M.divisors, (e : K) * (c ^ e + c⁻¹ ^ e - 2) := by
  have hpM : p * M ≠ 0 := mul_ne_zero hp.ne' hM
  rw [toricPoint_fst_coeff_natCast K p c hpM, sum_divisors_mul_ite_dvd p hp M, ite_eq_left (dvd_mul_right p M),
    Nat.mul_div_cancel_left M hp]
  simp_rw [Nat.mul_div_mul_left _ _ hp]
  rw [Nat.sum_div_divisors M (fun e => ((e : ℕ) : K) * (c ^ e + c⁻¹ ^ e)), Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun e _ => by ring

end TateSlots

-- pin: toricPoint_snd_coeff_mul (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:842)
theorem toricPoint_snd_coeff_mul (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) =
      ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * c ^ e - (((e + 1).choose 2 : ℕ) : K) * c⁻¹ ^ e + (e : K)) := by
  have hpM : p * M ≠ 0 := mul_ne_zero hp.ne' hM
  rw [toricPoint_snd_coeff_natCast K p c hpM, sum_divisors_mul_ite_dvd p hp M, ite_eq_left (dvd_mul_right p M),
    Nat.mul_div_cancel_left M hp]
  simp_rw [Nat.mul_div_mul_left _ _ hp]
  rw [Nat.sum_div_divisors M (fun e => (((e : ℕ).choose 2 : ℕ) : K) * c ^ e - (((e + 1).choose 2 : ℕ) : K) * c⁻¹ ^ e),
    ← Finset.sum_add_distrib]

namespace TateSlots

-- pin: ModularCurve.toricPoint_snd_coeff_mul' (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:852)
theorem toricPoint_snd_coeff_mul_eq_sum_divisors (hp : 0 < p) (c : K) {M : ℕ} (hM : M ≠ 0) :
    (toricPoint K p c).2.coeff ((p * M : ℕ) : ℤ) =
      ∑ e ∈ M.divisors, (((e.choose 2 : ℕ) : K) * (c ^ e - c⁻¹ ^ e) - (e : K) * c⁻¹ ^ e + (e : K)) := by
  rw [toricPoint_snd_coeff_mul K p hp c hM]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Nat.choose_succ_succ' e 1, Nat.choose_one_right, Nat.cast_add]
  ring

end TateSlots

example : (toricPoint ℚ 3 (-1)).1.coeff 0 = -1 / 4 := by
  rw [TateSlots.toricPoint_fst_coeff_zero]; norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 0 = 1 / 8 := by
  rw [TateSlots.toricPoint_snd_coeff_zero]; norm_num

example : (toricPoint ℚ 3 (-1)).1.coeff 3 = -4 := by
  rw [show (3 : ℤ) = ((3 * 1 : ℕ) : ℤ) by norm_num, TateSlots.toricPoint_fst_coeff_mul ℚ 3 (by norm_num) (-1) one_ne_zero,
    Nat.divisors_one, Finset.sum_singleton]
  norm_num

example : (toricPoint ℚ 3 (-1)).1.coeff 6 = -4 := by
  rw [show (6 : ℤ) = ((3 * 2 : ℕ) : ℤ) by norm_num, TateSlots.toricPoint_fst_coeff_mul ℚ 3 (by norm_num) (-1) two_ne_zero,
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by decide)]
  norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 3 = 2 := by
  rw [show (3 : ℤ) = ((3 * 1 : ℕ) : ℤ) by norm_num, toricPoint_snd_coeff_mul ℚ 3 (by norm_num) (-1) one_ne_zero,
    Nat.divisors_one, Finset.sum_singleton]
  norm_num

example : (toricPoint ℚ 3 (-1)).2.coeff 6 = 2 := by
  rw [show (6 : ℤ) = ((3 * 2 : ℕ) : ℤ) by norm_num, toricPoint_snd_coeff_mul ℚ 3 (by norm_num) (-1) two_ne_zero,
    Nat.Prime.divisors Nat.prime_two, Finset.sum_pair (by decide)]
  norm_num [Nat.choose]

example : (toricPoint ℚ 3 (-1)).1.coeff 4 = 0 :=
  TateSlots.toricPoint_fst_coeff_of_not_dvd ℚ 3 (-1) (m := 4) (by decide)

end ToricCoeffs

namespace W4Bdev

section Abstract

variable {K : Type*} [CommRing K] (c : Kˣ)

-- pin: hasSubst_slotFamily_two (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:898)
theorem hasSubst_slotFamily_two : MvPowerSeries.HasSubst (slotFamily K 2 c 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by
    fin_cases s <;> simp [slotFamily, PowerSeries.C, PowerSeries.X])

-- pin: prod_slotFamily_two (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:902)
theorem prod_slotFamily_two (d : Fin 2 →₀ ℕ) :
    (d.prod fun s e => (slotFamily K 2 c 1 s) ^ e)
      = PowerSeries.C ((c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1) * PowerSeries.X ^ (d 0 + d 1) := by
  rw [Finsupp.prod_pow, Fin.prod_univ_two]
  simp only [slotFamily, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show (2 : ℕ) - 1 = 1 from rfl, pow_one, mul_pow, mul_pow, ← map_pow, ← map_pow,
    mul_mul_mul_comm, ← map_mul, ← _root_.pow_add]

variable (φ : MvPowerSeries (Fin 2) ℤ)

-- pin: coeff_slotSubst_two (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:912)
theorem coeff_slotSubst_two (n : ℕ) :
    PowerSeries.coeff n (slotSubst K 2 c 1 φ)
      = ∑ᶠ d' : Fin 2 →₀ ℕ, MvPowerSeries.coeff d' φ •
          (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0) := by
  simp only [slotSubst]
  rw [PowerSeries.coeff_def Finsupp.single_eq_same,
    MvPowerSeries.coeff_subst (hasSubst_slotFamily_two c)]
  congr 1
  funext d'
  rw [prod_slotFamily_two, ← PowerSeries.coeff_def Finsupp.single_eq_same,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]

-- pin: support_coeff_slotSubst_two (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:924)
theorem support_coeff_slotSubst_two (n : ℕ) :
    (Function.support fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
      (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0)).Finite := by
  have hfun : (fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
        (if n = d' 0 + d' 1 then (c : K) ^ d' 0 * ((c⁻¹ : Kˣ) : K) ^ d' 1 else 0))
      = fun d' : Fin 2 →₀ ℕ => MvPowerSeries.coeff d' φ •
          MvPowerSeries.coeff (Finsupp.single () n)
            (d'.prod fun s e => (slotFamily K 2 c 1 s) ^ e) := by
    funext d'
    rw [prod_slotFamily_two, ← PowerSeries.coeff_def Finsupp.single_eq_same,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [hfun]
  exact MvPowerSeries.coeff_subst_finite (hasSubst_slotFamily_two c) φ (Finsupp.single () n)

-- pin: slotSubst_two_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:938)
theorem slotSubst_two_zero : slotSubst K 2 c 1 (0 : MvPowerSeries (Fin 2) ℤ) = 0 := by
  simp only [slotSubst]
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_slotFamily_two c), map_zero]

end Abstract

-- pin: genR (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:945)
def genR : (LaurentSeries ℚ)ˣ :=
  Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)

-- pin: genR_val (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:948)
@[scoped simp] theorem genR_val : (genR : LaurentSeries ℚ) = HahnSeries.single (1 : ℤ) (1 : ℚ) := rfl

-- pin: genR_inv_val (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:950)
@[scoped simp] theorem genR_inv_val :
    ((genR⁻¹ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) = HahnSeries.single (-1 : ℤ) (1 : ℚ) := by
  simp [genR, HahnSeries.inv_single]

-- pin: genR_pow_mul_inv_pow (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:954)
theorem genR_pow_mul_inv_pow (i j : ℕ) :
    (genR : LaurentSeries ℚ) ^ i * ((genR⁻¹ : (LaurentSeries ℚ)ˣ) : LaurentSeries ℚ) ^ j
      = HahnSeries.single ((i : ℤ) - (j : ℤ)) (1 : ℚ) := by
  rw [genR_val, genR_inv_val, HahnSeries.single_pow, HahnSeries.single_pow, one_pow, one_pow,
    HahnSeries.single_mul_single, one_mul, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_neg_one,
    ← sub_eq_add_neg]

-- pin: coeff_coeff_slotSubst_gen (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:961)
theorem coeff_coeff_slotSubst_gen (φ : MvPowerSeries (Fin 2) ℤ) (d : Fin 2 →₀ ℕ) :
    ((PowerSeries.coeff (d 0 + d 1)) (slotSubst (LaurentSeries ℚ) 2 genR 1 φ)).coeff
        ((d 0 : ℤ) - (d 1 : ℤ))
      = ((MvPowerSeries.coeff d φ : ℤ) : ℚ) := by
  have hmap : ∀ F : (Fin 2 →₀ ℕ) → LaurentSeries ℚ, (Function.support F).Finite →
      (finsum F).coeff ((d 0 : ℤ) - (d 1 : ℤ)) = ∑ᶠ d', (F d').coeff ((d 0 : ℤ) - (d 1 : ℤ)) :=
    fun F hF => (AddMonoidHom.mk' (fun x : LaurentSeries ℚ => x.coeff ((d 0 : ℤ) - (d 1 : ℤ)))
      (fun a b => by simp [HahnSeries.coeff_add])).map_finsum hF
  rw [coeff_slotSubst_two genR φ (d 0 + d 1),
    hmap _ (support_coeff_slotSubst_two genR φ (d 0 + d 1))]
  refine (finsum_eq_single _ d fun d' hd' => ?_).trans ?_
  · rcases eq_or_ne (d 0 + d 1) (d' 0 + d' 1) with h1 | h1
    · rw [ite_eq_left h1, HahnSeries.coeff_smul, genR_pow_mul_inv_pow, HahnSeries.coeff_single,
        ite_eq_right (fun hdiff => hd' (by
          have e0 : d' 0 = d 0 := by omega
          have e1 : d' 1 = d 1 := by omega
          ext i
          fin_cases i
          · exact e0
          · exact e1)), smul_zero]
    · rw [ite_eq_right h1, smul_zero, HahnSeries.coeff_zero]
  · rw [ite_eq_left rfl, HahnSeries.coeff_smul, genR_pow_mul_inv_pow, HahnSeries.coeff_single_same,
      zsmul_eq_mul, mul_one]

end W4Bdev

namespace TateSlots

-- pin: ModularCurve.W4Bdev.slotSubst_gen_injective (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:985)
theorem slotSubst_gen_injective :
    Function.Injective (slotSubst (LaurentSeries ℚ) 2
      (Units.mk0 (HahnSeries.single (1 : ℤ) (1 : ℚ)) (HahnSeries.single_ne_zero one_ne_zero)) 1) := by
  change Function.Injective (slotSubst (LaurentSeries ℚ) 2 W4Bdev.genR 1)
  intro φ ψ h
  ext d
  have h2 := congrArg
    (fun F => ((PowerSeries.coeff (d 0 + d 1)) F).coeff ((d 0 : ℤ) - (d 1 : ℤ))) h
  simp only [W4Bdev.coeff_coeff_slotSubst_gen] at h2
  exact_mod_cast h2

end TateSlots

namespace W4Bdev

-- pin: slotSubst_gen_eq_zero_iff (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:994)
theorem slotSubst_gen_eq_zero_iff (φ : MvPowerSeries (Fin 2) ℤ) :
    slotSubst (LaurentSeries ℚ) 2 genR 1 φ = 0 ↔ φ = 0 := by
  constructor
  · intro h
    refine TateSlots.slotSubst_gen_injective ?_
    change slotSubst (LaurentSeries ℚ) 2 W4Bdev.genR 1 φ = slotSubst (LaurentSeries ℚ) 2 W4Bdev.genR 1 0
    rw [h, slotSubst_two_zero]
  · rintro rfl
    exact slotSubst_two_zero genR

end W4Bdev

namespace W4Bdev

section EngineAux1

variable (K : Type*) [CommRing K]

-- pin: coeff_monomial_pair (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1012)
theorem coeff_monomial_pair (a b : K) (k q m l n : ℕ) :
    PowerSeries.coeff n ((PowerSeries.C a * PowerSeries.X ^ k) ^ m * (PowerSeries.C b * PowerSeries.X ^ q) ^ l)
      = if n = k * m + q * l then a ^ m * b ^ l else 0 := by
  have h : (PowerSeries.C a * PowerSeries.X ^ k) ^ m * (PowerSeries.C b * PowerSeries.X ^ q) ^ l
      = PowerSeries.C (a ^ m * b ^ l) * PowerSeries.X ^ (k * m + q * l) := by
    rw [mul_pow, mul_pow, ← map_pow, ← map_pow, ← pow_mul, ← pow_mul, map_mul, _root_.pow_add]; ring
  rw [h, PowerSeries.coeff_C_mul_X_pow]

-- pin: coeff_prod_slotFamily (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1020)
theorem coeff_prod_slotFamily (p : ℕ) (c : Kˣ) (k : ℕ) (d : Fin 2 →₀ ℕ) (n : ℕ) :
    PowerSeries.coeff n (d.prod fun s e => slotFamily K p c k s ^ e) =
      if n = k * d 0 + (p - k) * d 1 then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0 := by
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fin.prod_univ_two]
  exact coeff_monomial_pair K (c : K) ((c⁻¹ : Kˣ) : K) k (p - k) (d 0) (d 1) n

-- pin: coeff_slotSubst_finsum (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1026)
theorem coeff_slotSubst_finsum (p : ℕ) (c : Kˣ) (k : ℕ) (hk : 0 < k) (hkp : k < p)
    (f : MvPowerSeries (Fin 2) ℤ) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c k f) =
      ∑ᶠ d : Fin 2 →₀ ℕ, ((MvPowerSeries.coeff d f : ℤ) : K) *
        (if n = k * d 0 + (p - k) * d 1 then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0) := by
  have h := MvPowerSeries.coeff_subst (hasSubst_slotFamily K p c k hk hkp) f (Finsupp.single () n)
  rw [slotSubst]
  show MvPowerSeries.coeff (Finsupp.single () n) (MvPowerSeries.subst (slotFamily K p c k) f) = _
  rw [h]
  refine finsum_congr fun d => ?_
  show (MvPowerSeries.coeff d f : ℤ) • PowerSeries.coeff n (d.prod fun s e => slotFamily K p c k s ^ e) = _
  rw [coeff_prod_slotFamily, Algebra.smul_def, eq_intCast]

end EngineAux1

section Bridge

variable {K : Type*} [CommRing K]

-- pin: coe_pow_add_mul_inv_pow (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1046)
theorem coe_pow_add_mul_inv_pow (c : Kˣ) (b e : ℕ) :
    (c : K) ^ (b + e) * ((c⁻¹ : Kˣ) : K) ^ b = (c : K) ^ e := by
  rw [pow_add, mul_comm ((c : K) ^ b), mul_assoc, ← mul_pow, Units.mul_inv, one_pow, mul_one]

-- pin: coe_pow_mul_inv_pow_add (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1050)
theorem coe_pow_mul_inv_pow_add (c : Kˣ) (b e : ℕ) :
    (c : K) ^ b * ((c⁻¹ : Kˣ) : K) ^ (b + e) = ((c⁻¹ : Kˣ) : K) ^ e := by
  rw [pow_add, ← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]

-- pin: coe_pow_mul_inv_pow_self (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1054)
theorem coe_pow_mul_inv_pow_self (c : Kˣ) (b : ℕ) :
    (c : K) ^ b * ((c⁻¹ : Kˣ) : K) ^ b = 1 := by
  rw [← mul_pow, Units.mul_inv, one_pow]

-- pin: pairF (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1058)
def pairF (ab : ℕ × ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 ab.1 + Finsupp.single 1 ab.2

-- pin: pairF_apply_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1061)
@[scoped simp] theorem pairF_apply_zero (ab : ℕ × ℕ) : pairF ab 0 = ab.1 := by
  simp [pairF]

-- pin: pairF_apply_one (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1064)
@[scoped simp] theorem pairF_apply_one (ab : ℕ × ℕ) : pairF ab 1 = ab.2 := by
  simp [pairF]

-- pin: eq_pairF (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1067)
theorem eq_pairF (d : Fin 2 →₀ ℕ) : d = pairF (d 0, d 1) := by
  ext i
  fin_cases i <;> simp [pairF]

-- pin: coeff_slotSubst_eq_boxSum (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1071)
theorem coeff_slotSubst_eq_boxSum (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (φ : MvPowerSeries (Fin 2) ℤ) (E : ℕ → ℕ → ℤ)
    (hE : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d φ = E (d 0) (d 1)) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j φ)
      = ∑ ab ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
          ((E ab.1 ab.2 : ℤ) : K) *
            (if n = j * ab.1 + (p - j) * ab.2
             then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0) := by
  rw [coeff_slotSubst_finsum K p c j hj hjp φ n]
  have hsupp : (Function.support fun d : Fin 2 →₀ ℕ =>
      ((MvPowerSeries.coeff d φ : ℤ) : K) *
        (if n = j * d 0 + (p - j) * d 1
         then (c : K) ^ d 0 * ((c⁻¹ : Kˣ) : K) ^ d 1 else 0))
      ⊆ ↑((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).image pairF) := by
    intro d hd
    simp only [Function.mem_support] at hd
    have hcond : n = j * d 0 + (p - j) * d 1 := by
      by_contra hc
      simp [hc] at hd
    have hd0 : d 0 ≤ n := by
      have h1 : d 0 ≤ j * d 0 := Nat.le_mul_of_pos_left _ hj
      omega
    have hd1 : d 1 ≤ n := by
      have h1 : d 1 ≤ (p - j) * d 1 := Nat.le_mul_of_pos_left _ (by omega)
      omega
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(d 0, d 1), ?_, (eq_pairF d).symm⟩)
    simp [Finset.mem_product, hd0, hd1]
  have hinj : ∀ x ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
      ∀ y ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1), pairF x = pairF y → x = y := by
    intro x _ y _ h
    have h0 := congrArg (fun f : Fin 2 →₀ ℕ => f 0) h
    have h1 := congrArg (fun f : Fin 2 →₀ ℕ => f 1) h
    simp only [pairF_apply_zero, pairF_apply_one] at h0 h1
    exact Prod.ext h0 h1
  rw [finsum_eq_finsetSum_of_support_subset _ hsupp, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun ab _ => ?_
  rw [hE (pairF ab)]
  simp

-- pin: tableEntry (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1110)
def tableEntry (Dterm U V : ℕ → ℤ) (a b : ℕ) : ℤ :=
  if a = b then ∑ e ∈ b.divisors, Dterm e
  else if b < a then (if a - b ∣ b then U (a - b) else 0)
  else (if b - a ∣ b then V (b - a) else 0)

-- pin: coeff_tateUnivX_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1115)
theorem coeff_tateUnivX_eq (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d tateUnivX
      = tableEntry (fun e => -2 * e) (fun e => (e : ℤ)) (fun e => (e : ℤ)) (d 0) (d 1) := by
  rw [MvPowerSeries.coeff_apply]
  show (if d 0 = d 1 then -2 * ∑ e ∈ (d 1).divisors, (e : ℤ)
    else if d 1 < d 0 then (if d 0 - d 1 ∣ d 1 then ((d 0 - d 1 : ℕ) : ℤ) else 0)
    else (if d 1 - d 0 ∣ d 1 then ((d 1 - d 0 : ℕ) : ℤ) else 0)) = _
  rw [tableEntry, Finset.mul_sum]

-- pin: coeff_tateUnivY_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1124)
theorem coeff_tateUnivY_eq (d : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff d tateUnivY
      = tableEntry (fun e => (e : ℤ)) (fun e => (e.choose 2 : ℤ))
          (fun e => -(((e + 1).choose 2 : ℕ) : ℤ)) (d 0) (d 1) := by
  rw [MvPowerSeries.coeff_apply]
  rfl

-- pin: boxSum_eq_head_add_doubleSum (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1131)
theorem boxSum_eq_head_add_doubleSum (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p)
    (Dterm U V : ℕ → ℤ) (hU0 : U 0 = 0) (n : ℕ) :
    ∑ ab ∈ Finset.range (n + 1) ×ˢ Finset.range (n + 1),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = (if j ∣ n then ((U (n / j) : ℤ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
            (((U e : ℤ) : K) * (c : K) ^ e * (if n = p * M + j * e then 1 else 0)
              + ((V e : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ e * (if n + j * e = p * M then 1 else 0)
              + ((Dterm e : ℤ) : K) * (if n = p * M then 1 else 0)) := by
  classical
  have hp2 : p = j + (p - j) := by omega

  have htgt : ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
        (((U e : ℤ) : K) * (c : K) ^ e * (if n = p * M + j * e then 1 else 0)
          + ((V e : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ e * (if n + j * e = p * M then 1 else 0)
          + ((Dterm e : ℤ) : K) * (if n = p * M then 1 else 0))
      = (∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n = p * x.1 + j * x.2 then ((U x.2 : ℤ) : K) * (c : K) ^ x.2 else 0)
        + (∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n + j * x.2 = p * x.1 then ((V x.2 : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ x.2 else 0)
        + (∑ M ∈ Finset.range (n + 1),
            (∑ e ∈ M.divisors, ((Dterm e : ℤ) : K)) * (if n = p * M then 1 else 0)) := by
    rw [Finset.sum_sigma, Finset.sum_sigma, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun M _ => ?_
    rw [Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun e _ => ?_
    dsimp only
    simp only [mul_ite, mul_one, mul_zero]

  rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.range (n + 1) ×ˢ Finset.range (n + 1)) (fun ab => ab.2 < ab.1),
    ← Finset.sum_filter_add_sum_filter_not
      ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ¬ ab.2 < ab.1)
      (fun ab => ab.1 = ab.2), Finset.filter_filter]
  have hsetD : ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      fun ab => ¬ ab.2 < ab.1 ∧ ab.1 = ab.2)
      = (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.1 = ab.2 :=
    Finset.filter_congr fun ab _ => by omega
  have hsetB : (((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
      fun ab => ¬ ab.2 < ab.1).filter fun ab => ¬ ab.1 = ab.2)
      = (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.1 < ab.2 := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun ab _ => by omega
  rw [hsetD, hsetB]

  have hD : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.1 = ab.2),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = ∑ M ∈ Finset.range (n + 1),
          (∑ e ∈ M.divisors, ((Dterm e : ℤ) : K)) * (if n = p * M then 1 else 0) := by
    refine Finset.sum_bij' (fun ab _ => ab.1) (fun M _ => ((M, M) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro ab hab
      exact (Finset.mem_product.mp (Finset.mem_filter.mp hab).1).1
    · intro M hM
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hM, hM⟩, rfl⟩
    · intro ab hab
      exact Prod.ext rfl (Finset.mem_filter.mp hab).2
    · intro M _
      rfl
    · intro ab hab
      obtain ⟨-, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨a, b⟩ := ab
      obtain rfl : a = b := heq
      have hkey : j * a + (p - j) * a = p * a := by
        calc j * a + (p - j) * a = (j + (p - j)) * a := by ring
          _ = p * a := by rw [← hp2]
      rw [tableEntry, ite_eq_left rfl, hkey, coe_pow_mul_inv_pow_self, Int.cast_sum, Finset.sum_mul]

  have hB : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.1 < ab.2),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = ∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
          if n + j * x.2 = p * x.1 then ((V x.2 : ℤ) : K) * ((c⁻¹ : Kˣ) : K) ^ x.2 else 0 := by
    rw [← Finset.sum_filter_of_ne (p := fun ab : ℕ × ℕ => (ab.2 - ab.1) ∣ ab.2
        ∧ n + j * (ab.2 - ab.1) = p * ab.2) ?vanishB, Finset.filter_filter, ← Finset.sum_filter]
    case vanishB =>
      intro ab hab hne
      obtain ⟨-, hlt⟩ := Finset.mem_filter.mp hab
      by_contra hcon
      rcases Decidable.not_and_iff_or_not.mp hcon with hnd | hnc
      · rw [tableEntry, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right hnd] at hne
        simp at hne
      · have hb : ab.2 = ab.1 + (ab.2 - ab.1) := by omega
        have hkey : j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1) = p * ab.2 := by
          calc j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1)
              = j * (ab.1 + (ab.2 - ab.1)) + (p - j) * ab.2 := by ring
            _ = j * ab.2 + (p - j) * ab.2 := by rw [← hb]
            _ = (j + (p - j)) * ab.2 := by ring
            _ = p * ab.2 := by rw [← hp2]
        rw [ite_eq_right (fun hcond : n = j * ab.1 + (p - j) * ab.2 => hnc (by omega))] at hne
        simp at hne
    refine Finset.sum_bij' (fun ab _ => (⟨ab.2, ab.2 - ab.1⟩ : Σ _ : ℕ, ℕ))
      (fun x _ => ((x.1 - x.2, x.1) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
    · intro ab hab
      obtain ⟨hmem, hlt, hdvd, hcond⟩ := Finset.mem_filter.mp hab
      obtain ⟨-, hb⟩ := Finset.mem_product.mp hmem
      have hdm : ab.2 - ab.1 ∈ (ab.2).divisors := Nat.mem_divisors.mpr ⟨hdvd, by omega⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hb, hdm⟩, hcond⟩
    · intro x hx
      obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hx
      obtain ⟨hM, he⟩ := Finset.mem_sigma.mp hmem
      have hMn := Finset.mem_range.mp hM
      obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
      have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
      have heM : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) hdvd
      have hsub : x.1 - (x.1 - x.2) = x.2 := by omega
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
        ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩, by omega,
        by rw [hsub]; exact hdvd, by rw [hsub]; exact hcond⟩
    · intro ab hab
      dsimp only
      obtain ⟨-, hlt, -, -⟩ := Finset.mem_filter.mp hab
      exact Prod.ext (by omega) rfl
    · intro x hx
      dsimp only
      obtain ⟨hmem, -⟩ := Finset.mem_filter.mp hx
      obtain ⟨-, he⟩ := Finset.mem_sigma.mp hmem
      have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
      have hM0 : x.1 ≠ 0 := (Nat.mem_divisors.mp he).2
      have heM : x.2 ≤ x.1 := Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp he).1
      exact Sigma.ext rfl (by simp only [heq_eq_eq]; omega)
    · intro ab hab
      obtain ⟨-, hlt, hdvd, hcond⟩ := Finset.mem_filter.mp hab
      have hb : ab.2 = ab.1 + (ab.2 - ab.1) := by omega
      have hkey : j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1) = p * ab.2 := by
        calc j * ab.1 + (p - j) * ab.2 + j * (ab.2 - ab.1)
            = j * (ab.1 + (ab.2 - ab.1)) + (p - j) * ab.2 := by ring
          _ = j * ab.2 + (p - j) * ab.2 := by rw [← hb]
          _ = (j + (p - j)) * ab.2 := by ring
          _ = p * ab.2 := by rw [← hp2]
      rw [tableEntry, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left hdvd,
        ite_eq_left (show n = j * ab.1 + (p - j) * ab.2 by omega),
        show ((c⁻¹ : Kˣ) : K) ^ ab.2 = ((c⁻¹ : Kˣ) : K) ^ (ab.1 + (ab.2 - ab.1)) from by
          rw [← hb],
        coe_pow_mul_inv_pow_add]

  have hA : ∑ ab ∈ (Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter
        (fun ab => ab.2 < ab.1),
        ((tableEntry Dterm U V ab.1 ab.2 : ℤ) : K) *
          (if n = j * ab.1 + (p - j) * ab.2
           then (c : K) ^ ab.1 * ((c⁻¹ : Kˣ) : K) ^ ab.2 else 0)
      = (if j ∣ n then ((U (n / j) : ℤ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ x ∈ (Finset.range (n + 1)).sigma (fun M => M.divisors),
            if n = p * x.1 + j * x.2 then ((U x.2 : ℤ) : K) * (c : K) ^ x.2 else 0 := by
    rw [← Finset.sum_filter_add_sum_filter_not
        ((Finset.range (n + 1) ×ˢ Finset.range (n + 1)).filter fun ab => ab.2 < ab.1)
        (fun ab => ab.2 = 0), Finset.filter_filter, Finset.filter_filter]
    congr 1
    ·
      trans (∑ a ∈ (Finset.range (n + 1)).filter (fun a => 0 < a),
        ((U a : ℤ) : K) * (if n = j * a then (c : K) ^ a else 0))
      · refine Finset.sum_bij' (fun ab _ => ab.1) (fun a _ => ((a, 0) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
        · intro ab hab
          obtain ⟨hmem, hlt, hb0⟩ := Finset.mem_filter.mp hab
          exact Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hmem).1, by omega⟩
        · intro a ha
          obtain ⟨hmem, hpos⟩ := Finset.mem_filter.mp ha
          exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨hmem, Finset.mem_range.mpr (by omega)⟩, by omega, rfl⟩
        · intro ab hab
          obtain ⟨-, -, hb0⟩ := Finset.mem_filter.mp hab
          exact Prod.ext rfl hb0.symm
        · intro a _
          rfl
        · intro ab hab
          obtain ⟨-, hlt, hb0⟩ := Finset.mem_filter.mp hab
          obtain ⟨a, b⟩ := ab
          obtain rfl : b = 0 := hb0
          rw [tableEntry, ite_eq_right (by omega), ite_eq_left (show (0:ℕ) < a by omega), Nat.sub_zero,
            ite_eq_left (dvd_zero a), mul_zero, add_zero, pow_zero, mul_one]
      · by_cases hdvd : j ∣ n
        · rw [ite_eq_left hdvd, Finset.sum_eq_single (n / j)]
          · rw [ite_eq_left (Nat.mul_div_cancel' hdvd).symm]
          · intro b hb hne
            rw [ite_eq_right, mul_zero]
            intro hcon
            exact hne (by rw [hcon, Nat.mul_div_cancel_left b hj])
          · intro hns
            rcases Nat.eq_zero_or_pos (n / j) with h0 | hpos
            · rw [h0, hU0]
              simp
            · exact absurd (Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self n j)), hpos⟩) hns
        · rw [ite_eq_right hdvd]
          apply Finset.sum_eq_zero
          intro b _
          rw [ite_eq_right (fun h : n = j * b => hdvd ⟨b, h⟩), mul_zero]
    ·
      rw [← Finset.sum_filter_of_ne (p := fun ab : ℕ × ℕ => (ab.1 - ab.2) ∣ ab.2
          ∧ n = p * ab.2 + j * (ab.1 - ab.2)) ?vanishA, Finset.filter_filter, ← Finset.sum_filter]
      case vanishA =>
        intro ab hab hne
        obtain ⟨-, hlt, hb0⟩ := Finset.mem_filter.mp hab
        by_contra hcon
        rcases Decidable.not_and_iff_or_not.mp hcon with hnd | hnc
        · rw [tableEntry, ite_eq_right (by omega), ite_eq_left hlt, ite_eq_right hnd] at hne
          simp at hne
        · have ha : ab.1 = ab.2 + (ab.1 - ab.2) := by omega
          have hkey : j * ab.1 + (p - j) * ab.2 = p * ab.2 + j * (ab.1 - ab.2) := by
            calc j * ab.1 + (p - j) * ab.2
                = j * (ab.2 + (ab.1 - ab.2)) + (p - j) * ab.2 := by rw [← ha]
              _ = (j + (p - j)) * ab.2 + j * (ab.1 - ab.2) := by ring
              _ = p * ab.2 + j * (ab.1 - ab.2) := by rw [← hp2]
          rw [ite_eq_right (fun hcond : n = j * ab.1 + (p - j) * ab.2 => hnc (by omega))] at hne
          simp at hne
      refine Finset.sum_bij' (fun ab _ => (⟨ab.2, ab.1 - ab.2⟩ : Σ _ : ℕ, ℕ))
        (fun x _ => ((x.1 + x.2, x.1) : ℕ × ℕ)) ?_ ?_ ?_ ?_ ?_
      · intro ab hab
        obtain ⟨hmem, ⟨hlt, hb0⟩, hdvd, hcond⟩ := Finset.mem_filter.mp hab
        obtain ⟨-, hb⟩ := Finset.mem_product.mp hmem
        refine Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨hb, ?_⟩, hcond⟩
        exact Nat.mem_divisors.mpr ⟨hdvd, hb0⟩
      · intro x hx
        obtain ⟨hmem, hcond⟩ := Finset.mem_filter.mp hx
        obtain ⟨hM, he⟩ := Finset.mem_sigma.mp hmem
        have hMn := Finset.mem_range.mp hM
        obtain ⟨hdvd, hM0⟩ := Nat.mem_divisors.mp he
        have hepos : 0 < x.2 := Nat.pos_of_mem_divisors he
        have hjx : x.2 ≤ j * x.2 := Nat.le_mul_of_pos_left _ hj
        have hpx : x.1 ≤ p * x.1 := Nat.le_mul_of_pos_left _ (by omega)
        have hsub : x.1 + x.2 - x.1 = x.2 := by omega
        refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr (by omega)⟩,
          ⟨by omega, by omega⟩, by rw [hsub]; exact hdvd, by rw [hsub]; exact hcond⟩
      · intro ab hab
        dsimp only
        obtain ⟨-, ⟨hlt, -⟩, -, -⟩ := Finset.mem_filter.mp hab
        exact Prod.ext (by omega) rfl
      · intro x _
        dsimp only
        exact Sigma.ext rfl (by simp only [heq_eq_eq]; omega)
      · intro ab hab
        obtain ⟨-, ⟨hlt, -⟩, hdvd, hcond⟩ := Finset.mem_filter.mp hab
        have ha : ab.1 = ab.2 + (ab.1 - ab.2) := by omega
        have hkey : j * ab.1 + (p - j) * ab.2 = p * ab.2 + j * (ab.1 - ab.2) := by
          calc j * ab.1 + (p - j) * ab.2
              = j * (ab.2 + (ab.1 - ab.2)) + (p - j) * ab.2 := by rw [← ha]
            _ = (j + (p - j)) * ab.2 + j * (ab.1 - ab.2) := by ring
            _ = p * ab.2 + j * (ab.1 - ab.2) := by rw [← hp2]
        rw [tableEntry, ite_eq_right (by omega), ite_eq_left hlt, ite_eq_left hdvd, hkey, ite_eq_left hcond,
          show (c : K) ^ ab.1 = (c : K) ^ (ab.2 + (ab.1 - ab.2)) from by rw [← ha],
          coe_pow_add_mul_inv_pow]
  rw [hD, hB, hA, htgt]
  ring

end Bridge

end W4Bdev

namespace TateSlots

-- pin: ModularCurve.W4Bdev.coeff_slotSubst_tateUnivX (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1383)
theorem coeff_slotSubst_tateUnivX {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j tateUnivX)
      = (if j ∣ n then ((n / j : ℕ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors, (e : K) *
            ((if n = p * M + j * e then (c : K) ^ e else 0)
              + (if n + j * e = p * M then ((c⁻¹ : Kˣ) : K) ^ e else 0)
              - (if n = p * M then 2 else 0)) := by
  rw [W4Bdev.coeff_slotSubst_eq_boxSum p c j hj hjp tateUnivX _ W4Bdev.coeff_tateUnivX_eq n,
    W4Bdev.boxSum_eq_head_add_doubleSum p c j hj hjp (fun e => -2 * e) (fun e => (e : ℤ))
      (fun e => (e : ℤ)) (by simp) n]
  congr 1
  · split_ifs with h
    · norm_cast
    · rfl
  · refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    push_cast
    split_ifs <;> ring

-- pin: ModularCurve.W4Bdev.coeff_slotSubst_tateUnivY (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1401)
theorem coeff_slotSubst_tateUnivY {K : Type*} [CommRing K] (p : ℕ) (c : Kˣ) (j : ℕ) (hj : 0 < j) (hjp : j < p) (n : ℕ) :
    PowerSeries.coeff n (slotSubst K p c j tateUnivY)
      = (if j ∣ n then (((n / j).choose 2 : ℕ) : K) * (c : K) ^ (n / j) else 0)
        + ∑ M ∈ Finset.range (n + 1), ∑ e ∈ M.divisors,
            ((if n = p * M + j * e then ((e.choose 2 : ℕ) : K) * (c : K) ^ e else 0)
              - (if n + j * e = p * M then (((e + 1).choose 2 : ℕ) : K) * ((c⁻¹ : Kˣ) : K) ^ e
                 else 0)
              + (if n = p * M then (e : K) else 0)) := by
  rw [W4Bdev.coeff_slotSubst_eq_boxSum p c j hj hjp tateUnivY _ W4Bdev.coeff_tateUnivY_eq n,
    W4Bdev.boxSum_eq_head_add_doubleSum p c j hj hjp (fun e => (e : ℤ)) (fun e => (e.choose 2 : ℤ))
      (fun e => -(((e + 1).choose 2 : ℕ) : ℤ)) (by simp) n]
  congr 1
  · split_ifs with h
    · push_cast
      ring
    · rfl
  · refine Finset.sum_congr rfl fun M _ => Finset.sum_congr rfl fun e _ => ?_
    push_cast
    split_ifs <;> ring

end TateSlots

section GeomHeads

variable (K : Type*) [CommRing K]

-- pin: headX (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1431)
def headX (j : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.mk fun n => if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0

-- pin: headY (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1434)
def headY (j : ℕ) (c : K) : PowerSeries K :=
  PowerSeries.mk fun n => if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0

-- pin: coeff_headX (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1437)
theorem coeff_headX (j : ℕ) (c : K) (n : ℕ) :
    PowerSeries.coeff n (headX K j c) = if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0 :=
  PowerSeries.coeff_mk _ _

-- pin: coeff_headY (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1441)
theorem coeff_headY (j : ℕ) (c : K) (n : ℕ) :
    PowerSeries.coeff n (headY K j c) = if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0 :=
  PowerSeries.coeff_mk _ _

-- pin: coeff_headX_mul (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1445)
theorem coeff_headX_mul (j : ℕ) (hj : 0 < j) (c : K) (m : ℕ) :
    PowerSeries.coeff (j * m) (headX K j c) = (m : K) * c ^ m := by
  rw [coeff_headX, ite_eq_left (dvd_mul_right j m), Nat.mul_div_cancel_left m hj]

-- pin: coeff_headY_mul (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1449)
theorem coeff_headY_mul (j : ℕ) (hj : 0 < j) (c : K) (m : ℕ) :
    PowerSeries.coeff (j * m) (headY K j c) = ((m.choose 2 : ℕ) : K) * c ^ m := by
  rw [coeff_headY, ite_eq_left (dvd_mul_right j m), Nat.mul_div_cancel_left m hj]

-- pin: coeff_headX_of_not_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1453)
theorem coeff_headX_of_not_dvd (j : ℕ) (c : K) {n : ℕ} (h : ¬ j ∣ n) :
    PowerSeries.coeff n (headX K j c) = 0 := by
  rw [coeff_headX, ite_eq_right h]

-- pin: coeff_headY_of_not_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1457)
theorem coeff_headY_of_not_dvd (j : ℕ) (c : K) {n : ℕ} (h : ¬ j ∣ n) :
    PowerSeries.coeff n (headY K j c) = 0 := by
  rw [coeff_headY, ite_eq_right h]

-- pin: not_dvd_sub_of_not_dvd (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1461)
theorem not_dvd_sub_of_not_dvd {j n : ℕ} (h : ¬ j ∣ n) (t : ℕ) (ht : t * j ≤ n) : ¬ j ∣ n - t * j :=
  fun h' => h (by have := dvd_add h' (dvd_mul_left j t); rwa [Nat.sub_add_cancel ht] at this)

-- pin: headX_mul_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1464)
theorem headX_mul_eq (j : ℕ) (hj : 0 < j) (c : K) :
    headX K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 2 = PowerSeries.C c * PowerSeries.X ^ j := by
  have expand : headX K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 2 =
      headX K j c - PowerSeries.C (2 * c) * (headX K j c * PowerSeries.X ^ j) + PowerSeries.C (c ^ 2) * (headX K j c * PowerSeries.X ^ (2 * j)) := by
    rw [map_mul, map_pow, map_ofNat, pow_mul' PowerSeries.X 2 j]
    ring
  ext n
  rw [expand, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_C_mul_X_pow]
  by_cases hjn : j ∣ n
  · obtain ⟨m, rfl⟩ := hjn
    rw [coeff_headX_mul K j hj c m]
    rcases Nat.lt_or_ge m 1 with hm | hm
    ·
      obtain rfl : m = 0 := by omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    ·
      obtain rfl : m = 1 := by omega
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega), show j * 1 - j = j * 0 by omega,
        coeff_headX_mul K j hj c 0]
      simp
    ·
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      have h1 : j ≤ j * (k + 2) := Nat.le_mul_of_pos_right j (by omega)
      have h2 : 2 * j ≤ j * (k + 2) := by
        rw [Nat.mul_comm j (k + 2)]; exact Nat.mul_le_mul_right j (by omega)
      have h3 : ¬ j * (k + 2) = j := fun h =>
        absurd (Nat.eq_of_mul_eq_mul_left hj (h.trans (mul_one j).symm)) (by omega)
      have e1 : j * (k + 2) - j = j * (k + 1) := by
        rw [show k + 2 = (k + 1) + 1 from rfl, Nat.mul_succ, Nat.add_sub_cancel]
      have e2 : j * (k + 2) - 2 * j = j * k := by
        rw [Nat.mul_add, Nat.mul_comm j 2, Nat.add_sub_cancel]
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_right h3, e1, e2, coeff_headX_mul K j hj c (k + 1), coeff_headX_mul K j hj c k]
      push_cast
      ring
  · have z0 := coeff_headX_of_not_dvd K j c hjn
    have z1 : (if j ≤ n then PowerSeries.coeff (n - j) (headX K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headX_of_not_dvd K j c (by simpa using not_dvd_sub_of_not_dvd hjn 1 (by simpa using h))
      · rfl
    have z2 : (if 2 * j ≤ n then PowerSeries.coeff (n - 2 * j) (headX K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headX_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 2 h)
      · rfl
    rw [z0, z1, z2, ite_eq_right (fun h => hjn ⟨1, by rw [h, mul_one]⟩)]
    ring

-- pin: headY_mul_eq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1513)
theorem headY_mul_eq (j : ℕ) (hj : 0 < j) (c : K) :
    headY K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 3 = (PowerSeries.C c * PowerSeries.X ^ j) ^ 2 := by
  have expand : headY K j c * (1 - PowerSeries.C c * PowerSeries.X ^ j) ^ 3 =
      headY K j c - PowerSeries.C (3 * c) * (headY K j c * PowerSeries.X ^ j) + PowerSeries.C (3 * c ^ 2) * (headY K j c * PowerSeries.X ^ (2 * j))
        - PowerSeries.C (c ^ 3) * (headY K j c * PowerSeries.X ^ (3 * j)) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_ofNat, pow_mul' PowerSeries.X 2 j,
      pow_mul' PowerSeries.X 3 j]
    ring
  have rhs : (PowerSeries.C c * PowerSeries.X ^ j) ^ 2 = PowerSeries.C (c ^ 2) * PowerSeries.X ^ (2 * j) := by
    rw [map_pow, pow_mul' PowerSeries.X 2 j]; ring
  ext n
  rw [expand, rhs, map_sub, map_add, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow',
    PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_C_mul_X_pow]
  by_cases hjn : j ∣ n
  · obtain ⟨m, rfl⟩ := hjn
    rw [coeff_headY_mul K j hj c m]
    rcases Nat.lt_or_ge m 1 with hm | hm
    · obtain rfl : m = 0 := by omega
      rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
      simp
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
        show j * 1 - j = j * 0 by omega, coeff_headY_mul K j hj c 0]
      simp
    rcases Nat.lt_or_ge m 3 with hm3 | hm3
    · obtain rfl : m = 2 := by omega
      have h2 : 2 * j ≤ j * 2 := by rw [Nat.mul_comm]
      rw [ite_eq_left (by omega), ite_eq_left h2, ite_eq_right (by omega), ite_eq_left (by rw [Nat.mul_comm]),
        show j * 2 - j = j * 1 by omega, show j * 2 - 2 * j = j * 0 by omega,
        coeff_headY_mul K j hj c 1, coeff_headY_mul K j hj c 0]
      norm_num [Nat.choose]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
      have h1 : j ≤ j * (k + 3) := Nat.le_mul_of_pos_right j (by omega)
      have h2 : 2 * j ≤ j * (k + 3) := by
        rw [Nat.mul_comm j (k + 3)]; exact Nat.mul_le_mul_right j (by omega)
      have h3 : 3 * j ≤ j * (k + 3) := by
        rw [Nat.mul_comm j (k + 3)]; exact Nat.mul_le_mul_right j (by omega)
      have h4 : ¬ j * (k + 3) = 2 * j := fun h => by
        rw [Nat.mul_comm 2 j] at h
        exact absurd (Nat.eq_of_mul_eq_mul_left hj h) (by omega)
      have e1 : j * (k + 3) - j = j * (k + 2) := by
        rw [show k + 3 = (k + 2) + 1 from rfl, Nat.mul_succ, Nat.add_sub_cancel]
      have e2 : j * (k + 3) - 2 * j = j * (k + 1) := by
        rw [show k + 3 = (k + 1) + 2 from rfl, Nat.mul_add, Nat.mul_comm j 2, Nat.add_sub_cancel]
      have e3 : j * (k + 3) - 3 * j = j * k := by
        rw [Nat.mul_add, Nat.mul_comm j 3, Nat.add_sub_cancel]
      rw [ite_eq_left h1, ite_eq_left h2, ite_eq_left h3, ite_eq_right h4, e1, e2, e3, coeff_headY_mul K j hj c (k + 2),
        coeff_headY_mul K j hj c (k + 1), coeff_headY_mul K j hj c k]
      have c3 : (k + 3).choose 2 = (k + 2) + (k + 2).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' (k + 2) 1
      have c2 : (k + 2).choose 2 = (k + 1) + (k + 1).choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' (k + 1) 1
      have c1 : (k + 1).choose 2 = k + k.choose 2 := by
        simpa [Nat.choose_one_right] using Nat.choose_succ_succ' k 1
      rw [c3, c2, c1]
      push_cast
      ring
  · have z0 := coeff_headY_of_not_dvd K j c hjn
    have z1 : (if j ≤ n then PowerSeries.coeff (n - j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (by simpa using not_dvd_sub_of_not_dvd hjn 1 (by simpa using h))
      · rfl
    have z2 : (if 2 * j ≤ n then PowerSeries.coeff (n - 2 * j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 2 h)
      · rfl
    have z3 : (if 3 * j ≤ n then PowerSeries.coeff (n - 3 * j) (headY K j c) else 0) = 0 := by
      split_ifs with h
      · exact coeff_headY_of_not_dvd K j c (not_dvd_sub_of_not_dvd hjn 3 h)
      · rfl
    rw [z0, z1, z2, z3, ite_eq_right (fun h => hjn ⟨2, by rw [h, Nat.mul_comm]⟩)]
    ring

end GeomHeads

section Laurent

variable (K : Type*) [Field K]

-- pin: single_eq_ofPowerSeries (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1594)
theorem single_eq_ofPowerSeries (j : ℕ) (c : K) :
    HahnSeries.single (j : ℤ) c = HahnSeries.ofPowerSeries ℤ K (PowerSeries.C c * PowerSeries.X ^ j) := by
  rw [map_mul, HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X_pow]
  change _ = HahnSeries.single 0 c * HahnSeries.single (j : ℤ) 1
  rw [HahnSeries.single_mul_single, zero_add, mul_one]

-- pin: one_sub_single_eq_ofPowerSeries (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1600)
theorem one_sub_single_eq_ofPowerSeries (j : ℕ) (c : K) :
    (1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c = HahnSeries.ofPowerSeries ℤ K (1 - PowerSeries.C c * PowerSeries.X ^ j) := by
  rw [map_sub, map_one, single_eq_ofPowerSeries]

-- pin: one_sub_single_ne_zero (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1604)
theorem one_sub_single_ne_zero (j : ℕ) (hj : 0 < j) (c : K) :
    (1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c ≠ 0 := by
  intro h
  have h0 := congrArg (fun x : LaurentSeries K => x.coeff 0) h
  have hj0 : (0 : ℤ) ≠ (j : ℤ) := by exact_mod_cast hj.ne
  simp only [HahnSeries.coeff_sub, HahnSeries.coeff_one, HahnSeries.coeff_single, ite_eq_right hj0,
    sub_zero, HahnSeries.coeff_zero] at h0
  exact one_ne_zero h0

namespace TateSlots

-- pin: ModularCurve.single_div_one_sub_sq (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1613)
theorem single_div_one_sub_sq (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2 =
      HahnSeries.ofPowerSeries ℤ K (headX K j c) := by
  rw [div_eq_iff (pow_ne_zero 2 (one_sub_single_ne_zero K j hj c)), one_sub_single_eq_ofPowerSeries,
    single_eq_ofPowerSeries, ← map_pow, ← map_mul, headX_mul_eq K j hj c]

-- pin: ModularCurve.single_sq_div_one_sub_cube (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1619)
theorem single_sq_div_one_sub_cube (j : ℕ) (hj : 0 < j) (c : K) :
    HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3 =
      HahnSeries.ofPowerSeries ℤ K (headY K j c) := by
  rw [div_eq_iff (pow_ne_zero 3 (one_sub_single_ne_zero K j hj c)), one_sub_single_eq_ofPowerSeries,
    single_eq_ofPowerSeries, ← map_pow, ← map_pow, ← map_mul, headY_mul_eq K j hj c]

end TateSlots

-- pin: single_div_one_sub_sq_coeff (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1625)
theorem single_div_one_sub_sq_coeff (j : ℕ) (hj : 0 < j) (c : K) (n : ℕ) :
    (HahnSeries.single (j : ℤ) c / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 2).coeff (n : ℤ) =
      if j ∣ n then ((n / j : ℕ) : K) * c ^ (n / j) else 0 := by
  rw [TateSlots.single_div_one_sub_sq K j hj c, HahnSeries.ofPowerSeries_apply_coeff, coeff_headX]

-- pin: single_sq_div_one_sub_cube_coeff (S_ModularCurve_tsum_of_coeff_lt_eq_zero.lean:1630)
theorem single_sq_div_one_sub_cube_coeff (j : ℕ) (hj : 0 < j) (c : K) (n : ℕ) :
    (HahnSeries.single (j : ℤ) c ^ 2 / ((1 : LaurentSeries K) - HahnSeries.single (j : ℤ) c) ^ 3).coeff (n : ℤ) =
      if j ∣ n then (((n / j).choose 2 : ℕ) : K) * c ^ (n / j) else 0 := by
  rw [TateSlots.single_sq_div_one_sub_cube K j hj c, HahnSeries.ofPowerSeries_apply_coeff, coeff_headY]

end Laurent

end ModularCurve

end
