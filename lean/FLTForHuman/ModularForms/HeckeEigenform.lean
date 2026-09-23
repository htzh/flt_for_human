/-
  The eigenform interface: a normalized eigenform is exactly a simultaneous
  eigenvector of the Hecke operators.

  This is the dictionary the FLT route consumes when it speaks of "the eigenform
  attached to a Galois representation". The three characterisations
  `isNormalizedEigenform_iff_heckeT` (surface operators), `…_iff_heckeTLin`
  (bundled maps) and `…_iff_coeffHecke` (coefficient maps) are one statement in
  three registers; the pin proves each separately, while the port proves the
  coefficient one and **derives** the other two (see below). The single-operator
  `iff`s, the forward `heckeTLin_apply_eq_qCoeff_smul` directions, the
  coefficient eigenvalue/vanishing pair, the formal multiplicity statement and
  `PowerSeries.coeff_heckeT_pow_sub_mem_span` complete the interface.

  Dedup against the pin (pinned `aa2d8b3`):

  * the whole analytic head of `S_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul`
    (175 lines) and `…_heckeULin…` (132) re-derives `hasSum_hecke{U,T}`; the port
    gets both targets as the forward direction of `iff_heckeTLin`;
  * the two thin `iff`s are derived from `iff_coeffHecke` + the single-operator
    `iff`s rather than re-proved (the pin's 26- and 13-line files are the pattern,
    its three separate proofs are not);
  * `W2WsF.eq_of_forall_qCoeff_eq` is T5's public
    `UpperHalfPlane.eq_of_forall_qCoeff_eq`.

  FLT provenance: `Definitions/Def_FLTPrelim_Modularity.lean` (the structure,
  `Defs/Eigenform.lean`) and the `P2M/Sol/S_*` files named per declaration.
-/
import FLTForHuman.ModularForms.Defs.Eigenform
import FLTForHuman.ModularForms.HeckeCommute
import FLTForHuman.ModularForms.Defs.FormalHeckeOperators

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace CuspForm

open ModularFormClass

/-! ## The coefficient algebra (private)

The pin's `M4cP2.W25c` block: a four-clause recursion over `ℕ` translating
between the structure's coefficient clauses and the `coeffHecke{T,U}` eigenvalue
equations. -/

private theorem zpow_two_sub_one (p : ℕ) : (p : ℂ) ^ ((2 : ℤ) - 1) = p := by norm_num

private theorem coeffHeckeT_two (a : ℕ → ℂ) (p n : ℕ) :
    ModularForm.coeffHeckeT 2 p a n = a (n * p) + if p ∣ n then (p : ℂ) * a (n / p) else 0 := by
  rw [ModularForm.coeffHeckeT_apply, zpow_two_sub_one]

private theorem coprime_pow_of_not_dvd {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) (k : ℕ) :
    (p ^ k).Coprime m :=
  Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)

private theorem heckeT_eigen_of_rec {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r)) (n : ℕ) :
    ModularForm.coeffHeckeT 2 p a n = a p * a n := by
  rw [coeffHeckeT_two]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  cases r with
  | zero =>
    have hpm : ¬ p ∣ p ^ 0 * m := by simpa using hm
    rw [ite_eq_right hpm, add_zero, pow_zero, one_mul, hmul m p
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)), mul_comm]
  | succ s =>
    have hpn : p ∣ p ^ (s + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
    have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
      rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
    rw [ite_eq_left hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 2)), hmul _ _ (coprime_pow_of_not_dvd hp hm s),
      hmul _ _ (coprime_pow_of_not_dvd hp hm (s + 1)), hrec s]
    ring

private theorem heckeU_eigen_of_rec {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (h0 : a 0 = 0)
    (h1 : a 1 = 1)
    (hmul : ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n)
    (hrec : ∀ r : ℕ, a (p ^ (r + 2)) = a p * a (p ^ (r + 1))) (n : ℕ) :
    ModularForm.coeffHeckeU p a n = a p * a n := by
  rw [ModularForm.coeffHeckeU_apply]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [h0]
  obtain ⟨r, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
  have hstep : a (p ^ (r + 1)) = a p * a (p ^ r) := by
    cases r with
    | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
    | succ s => exact hrec s
  rw [show p ^ r * m * p = p ^ (r + 1) * m by ring, hmul _ _ (coprime_pow_of_not_dvd hp hm (r + 1)),
    hmul _ _ (coprime_pow_of_not_dvd hp hm r), hstep]
  ring

private theorem rec_of_heckeT_eigen {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime)
    (hT : ∀ n : ℕ, ModularForm.coeffHeckeT 2 p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) - p * a (p ^ r) := by
  have h := hT (p ^ (r + 1))
  have hpn : p ∣ p ^ (r + 1) := dvd_pow_self p (Nat.succ_ne_zero r)
  have hdiv : p ^ (r + 1) / p = p ^ r := by
    rw [pow_succ', Nat.mul_div_cancel_left _ hp.pos]
  rw [coeffHeckeT_two, ite_eq_left hpn, hdiv, ← pow_succ] at h
  linear_combination h

private theorem rec_of_heckeU_eigen {a : ℕ → ℂ} {p : ℕ}
    (hU : ∀ n : ℕ, ModularForm.coeffHeckeU p a n = a p * a n) (r : ℕ) :
    a (p ^ (r + 2)) = a p * a (p ^ (r + 1)) := by
  have h := hU (p ^ (r + 1))
  rwa [ModularForm.coeffHeckeU_apply, ← pow_succ] at h

private theorem pow_mul_of_heckeT_eigen {a : ℕ → ℂ} {p : ℕ} (hp : p.Prime) (h1 : a 1 = 1)
    (hT : ∀ n : ℕ, ModularForm.coeffHeckeT 2 p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
    intro m hm
    match r, ih with
    | 0, _ => rw [pow_zero, one_mul, h1, one_mul]
    | 1, _ =>
      have h := hT m
      rw [coeffHeckeT_two, ite_eq_right hm, add_zero] at h
      rw [pow_one, mul_comm p m, h]
    | s + 2, ih =>
      have h := hT (p ^ (s + 1) * m)
      have hpn : p ∣ p ^ (s + 1) * m := dvd_mul_of_dvd_left (dvd_pow_self p (Nat.succ_ne_zero s)) m
      have hdiv : p ^ (s + 1) * m / p = p ^ s * m := by
        rw [show p ^ (s + 1) * m = p * (p ^ s * m) by ring, Nat.mul_div_cancel_left _ hp.pos]
      rw [coeffHeckeT_two, ite_eq_left hpn, hdiv, show p ^ (s + 1) * m * p = p ^ (s + 2) * m by ring,
        ih (s + 1) (by omega) m hm, ih s (by omega) m hm] at h
      rw [rec_of_heckeT_eigen hp hT s]
      linear_combination h

private theorem pow_mul_of_heckeU_eigen {a : ℕ → ℂ} {p : ℕ} (h1 : a 1 = 1)
    (hU : ∀ n : ℕ, ModularForm.coeffHeckeU p a n = a p * a n) :
    ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m := by
  intro r
  induction r with
  | zero => intro m _; rw [pow_zero, one_mul, h1, one_mul]
  | succ s ih =>
    intro m hm
    have h := hU (p ^ s * m)
    rw [ModularForm.coeffHeckeU_apply, show p ^ s * m * p = p ^ (s + 1) * m by ring, ih m hm] at h
    have hstep : a (p ^ (s + 1)) = a p * a (p ^ s) := by
      cases s with
      | zero => rw [zero_add, pow_one, pow_zero, h1, mul_one]
      | succ t => exact rec_of_heckeU_eigen hU t
    rw [h, hstep]
    ring

private theorem mul_of_coprime_of_pow_mul {a : ℕ → ℂ} (h1 : a 1 = 1)
    (hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m → a (p ^ r * m) = a (p ^ r) * a m) :
    ∀ m n : ℕ, m.Coprime n → a (m * n) = a m * a n := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hmn
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · interval_cases m
      · rw [Nat.coprime_zero_left] at hmn
        subst hmn
        rw [mul_one, h1, mul_one]
      · rw [one_mul, h1, one_mul]
    · have hm0 : m ≠ 0 := by omega
      have hm1 : m ≠ 1 := by omega
      set p := m.minFac with hp_def
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpm : p ∣ m := Nat.minFac_dvd m
      obtain ⟨r, m', hm', hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 p hp.ne_one
      have hr : r ≠ 0 := by
        rintro rfl
        rw [pow_zero, one_mul] at hmeq
        exact hm' (hmeq ▸ hpm)
      have hm'pos : 0 < m' := Nat.pos_of_ne_zero (fun h0 => hm0 (by rw [hmeq, h0, mul_zero]))
      have hm'lt : m' < m := by
        have hpr : 2 ≤ p ^ r := by
          calc 2 ≤ p := hp.two_le
            _ = p ^ 1 := (pow_one p).symm
            _ ≤ p ^ r := Nat.pow_le_pow_right hp.pos (Nat.pos_of_ne_zero hr)
        calc m' = 1 * m' := (one_mul _).symm
          _ < p ^ r * m' := Nat.mul_lt_mul_of_pos_right (by omega) hm'pos
          _ = m := hmeq.symm
      have hpn : ¬ p ∣ n := fun hdvd =>
        hp.ne_one (Nat.eq_one_of_dvd_coprimes hmn hpm hdvd)
      have hm'n : m'.Coprime n :=
        Nat.Coprime.coprime_dvd_left (⟨p ^ r, by rw [hmeq]; ring⟩ : m' ∣ m) hmn
      have hpm'n : ¬ p ∣ m' * n := fun hdvd =>
        (hp.dvd_mul.mp hdvd).elim hm' hpn
      rw [hmeq, show p ^ r * m' * n = p ^ r * (m' * n) by ring, hpow p hp r (m' * n) hpm'n,
        ih m' hm'lt n hm'n, hpow p hp r m' hm']
      ring

/-- `qCoeff f 0 = 0` for a cusp form. Stated verbatim from
`Theorems/Thm_CuspForm_qCoeff_zero.lean` (ported here because
`isNormalizedEigenform_iff_coeffHecke` consumes it). -/
theorem qCoeff_zero {N : ℕ} {k : ℤ} (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ModularFormClass.qCoeff f 0 = 0 := by
  have h1 : (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
    rw [CongruenceSubgroup.strictPeriods_Gamma0]
    exact AddSubgroup.mem_zmultiples 1
  exact CuspFormClass.qExpansion_coeff_zero f one_pos h1

/-- The coefficient characterisation. Stated verbatim from
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_coeffHecke.lean`. -/
theorem isNormalizedEigenform_iff_coeffHecke {N : ℕ}
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔
    (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
      ((¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT 2 p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) ∧
       (p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n))) := by
  have h0 : qCoeff f 0 = 0 := qCoeff_zero f
  constructor
  · intro hf
    refine ⟨hf.qCoeff_one, fun p hp => ⟨fun hpN n => ?_, fun hpN n => ?_⟩⟩
    · exact heckeT_eigen_of_rec hp h0 hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_not_dvd p r hp hpN) n
    · exact heckeU_eigen_of_rec hp h0 hf.qCoeff_one hf.qCoeff_mul_of_coprime
        (fun r => hf.qCoeff_prime_pow_of_dvd p r hp hpN) n
  · rintro ⟨h1, hE⟩
    have hpow : ∀ p : ℕ, p.Prime → ∀ r m : ℕ, ¬ p ∣ m →
        qCoeff f (p ^ r * m) = qCoeff f (p ^ r) * qCoeff f m := by
      intro p hp
      by_cases hpN : p ∣ N
      · exact pow_mul_of_heckeU_eigen h1 ((hE p hp).2 hpN)
      · exact pow_mul_of_heckeT_eigen hp h1 ((hE p hp).1 hpN)
    exact
      { qCoeff_one := h1
        qCoeff_mul_of_coprime := mul_of_coprime_of_pow_mul h1 hpow
        qCoeff_prime_pow_of_not_dvd := fun p r hp hpN =>
          rec_of_heckeT_eigen hp ((hE p hp).1 hpN) r
        qCoeff_prime_pow_of_dvd := fun p r hp hpN =>
          rec_of_heckeU_eigen ((hE p hp).2 hpN) r }

end CuspForm

end

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology UpperHalfPlane
open ModularForm

/-! ## The single-operator `iff`s and the two thin characterisations -/

namespace ModularFormClass

/-- The analytic core of `heckeT_eq_smul_iff`. -/
private theorem qCoeff_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
    (hbdd : IsBoundedAtImInfty f) (c : ℂ) (n : ℕ) : qCoeff (c • f) n = c * qCoeff f n := by
  simp only [qCoeff]
  rw [UpperHalfPlane.qExpansion_smul (analyticAt_cuspFunction_zero one_pos hper hhol hbdd)]
  simp

private theorem periodic_const_smul {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (c : ℂ) :
    Periodic ((c • f) ∘ ofComplex) 1 := fun z => by
  simpa using congrArg (c * ·) (hper z)

private theorem mf_periodic {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f hΓ

private theorem mf_bdd {F : Type*} [FunLike F UpperHalfPlane ℂ]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) :
    IsBoundedAtImInfty ⇑f :=
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  bdd_at_infty f

private theorem heckeT_eq_smul_iff_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeT k p f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (qCoeff f) n = c * qCoeff f n := by
  constructor
  · intro h n
    rw [← UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hp n, h,
      qCoeff_const_smul hper hhol hbdd]
  · intro h
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic_heckeT_comp_ofComplex hper k p)
      (mdifferentiable_heckeT hhol k p) (isBoundedAtImInfty_heckeT hbdd k p)
      (periodic_const_smul hper c) (hhol.const_smul c) (hbdd.const_smul_left c) fun n => ?_
    rw [UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hp n, h n,
      qCoeff_const_smul hper hhol hbdd]

private theorem heckeU_eq_smul_iff_bare {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1)
    (hhol : MDiff f) (hbdd : IsBoundedAtImInfty f) (k : ℤ) {p : ℕ} (hp : p ≠ 0) (c : ℂ) :
    ModularForm.heckeU k p f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (qCoeff f) n = c * qCoeff f n := by
  constructor
  · intro h n
    rw [← UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hp n, h,
      qCoeff_const_smul hper hhol hbdd]
  · intro h
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic_heckeU_comp_ofComplex hper k p)
      (mdifferentiable_heckeU hhol k p) (isBoundedAtImInfty_heckeU hbdd k p)
      (periodic_const_smul hper c) (hhol.const_smul c) (hbdd.const_smul_left c) fun n => ?_
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hp n, h n,
      qCoeff_const_smul hper hhol hbdd]

/-- `T_p f = c f` iff the coefficients satisfy the eigenvalue equation. Stated
verbatim from `Theorems/Thm_ModularFormClass_heckeT_eq_smul_iff.lean`. -/
theorem heckeT_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) : ModularForm.heckeT k p ⇑f = c • ⇑f ↔ ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n :=
  heckeT_eq_smul_iff_bare (mf_periodic f hΓ) (ModularFormClass.holo f) (mf_bdd f hΓ) k hp c

/-- `U_p f = c f` iff the coefficients satisfy the eigenvalue equation. Stated
verbatim from `Theorems/Thm_ModularFormClass_heckeU_eq_smul_iff.lean`. -/
theorem heckeU_eq_smul_iff {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p : ℕ} (hp : p ≠ 0) (c : ℂ) : ModularForm.heckeU k p ⇑f = c • ⇑f ↔ ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n :=
  heckeU_eq_smul_iff_bare (mf_periodic f hΓ) (ModularFormClass.holo f) (mf_bdd f hΓ) k hp c

end ModularFormClass

namespace CuspForm

/-- `(1 : ℝ)` is a strict period of `Γ₀(N)`. -/
private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-- The bundled `T_p` eigenvalue condition, in coefficients. Stated verbatim from
`Theorems/Thm_CuspForm_heckeTLin_apply_eq_smul_iff.lean`. -/
theorem heckeTLin_apply_eq_smul_iff {N : ℕ} (k : ℤ) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeTLin k hp hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeT k p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by
  rw [← ModularFormClass.heckeT_eq_smul_iff f (one_mem_strictPeriods_Gamma0 N) hp.ne_zero c,
    DFunLike.ext'_iff, CuspForm.coe_heckeTLin_apply, FunLike.coe_smul]

/-- The bundled `U_p` eigenvalue condition, in coefficients. Stated verbatim from
`Theorems/Thm_CuspForm_heckeULin_apply_eq_smul_iff.lean`. -/
theorem heckeULin_apply_eq_smul_iff {N : ℕ} [NeZero N] (k : ℤ) {p : ℕ} (hpN : p ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (c : ℂ) :
    CuspForm.heckeULin k hpN f = c • f ↔
      ∀ n : ℕ, ModularForm.coeffHeckeU p (ModularFormClass.qCoeff f) n = c * ModularFormClass.qCoeff f n := by
  rw [← ModularFormClass.heckeU_eq_smul_iff f (one_mem_strictPeriods_Gamma0 N)
      (ne_zero_of_dvd_ne_zero (NeZero.ne N) hpN) c,
    DFunLike.ext'_iff, CuspForm.coe_heckeULin_apply, FunLike.coe_smul]

/-- Surface-operator characterisation. Stated verbatim from
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeT.lean`. Derived from
`isNormalizedEigenform_iff_coeffHecke` through the two `ModularFormClass` iff's
(the pin proves it separately in 26 lines). -/
theorem isNormalizedEigenform_iff_heckeT {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : f.IsNormalizedEigenform ↔
    (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ p : ℕ, p.Prime →
      ((¬ p ∣ N → ModularForm.heckeT 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f) ∧
       (p ∣ N → ModularForm.heckeU 2 p ⇑f = ModularFormClass.qCoeff f p • ⇑f))) := by
  rw [isNormalizedEigenform_iff_coeffHecke]
  refine and_congr_right fun _ => forall_congr' fun p => forall_congr' fun hp => ?_
  rw [ModularFormClass.heckeT_eq_smul_iff f (one_mem_strictPeriods_Gamma0 N) hp.ne_zero,
    ModularFormClass.heckeU_eq_smul_iff f (one_mem_strictPeriods_Gamma0 N) hp.ne_zero]

/-- Bundled-operator characterisation. Stated verbatim from
`Theorems/Thm_CuspForm_isNormalizedEigenform_iff_heckeTLin.lean`. Derived from
`…_iff_heckeT` by unfolding the coercion (the pin proves it separately, 13 lines). -/
theorem isNormalizedEigenform_iff_heckeTLin {N : ℕ} [NeZero N] (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) :
    f.IsNormalizedEigenform ↔ (ModularFormClass.qCoeff f 1 = 1 ∧ ∀ (p : ℕ) (hp : p.Prime),
      ((hpN : ¬ p ∣ N) → CuspForm.heckeTLin 2 hp hpN f = ModularFormClass.qCoeff f p • f) ∧
      ((hpN : p ∣ N) → CuspForm.heckeULin 2 hpN f = ModularFormClass.qCoeff f p • f)) := by
  rw [CuspForm.isNormalizedEigenform_iff_heckeT]
  simp only [DFunLike.ext'_iff (f := CuspForm.heckeTLin 2 _ _ f),
    DFunLike.ext'_iff (f := CuspForm.heckeULin 2 _ f), CuspForm.coe_heckeTLin_apply,
    CuspForm.coe_heckeULin_apply, FunLike.coe_smul]

/-- The forward direction of `…_iff_heckeTLin` at the prime. Stated verbatim from
`Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeTLin_apply_eq_qCoeff_smul.lean`.
The pin's 175-line `S_` file re-derives `hasSum_heckeT`; the port takes the
forward direction of the characterisation. -/
theorem IsNormalizedEigenform.heckeTLin_apply_eq_qCoeff_smul (N : ℕ)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    CuspForm.heckeTLin 2 hℓ hℓN f = ModularFormClass.qCoeff f ℓ • f := by
  have hN : NeZero N := ⟨fun h => hℓN (h ▸ dvd_zero ℓ)⟩
  exact ((isNormalizedEigenform_iff_heckeTLin f).mp hf).2 ℓ hℓ |>.1 hℓN

/-- The forward direction of `…_iff_heckeTLin` at the prime, `U` case. Stated
verbatim from
`Theorems/Thm_CuspForm_IsNormalizedEigenform_heckeULin_apply_eq_qCoeff_smul.lean`.
The pin's 132-line `S_` file re-derives `hasSum_heckeU`; the port takes the
forward direction of the characterisation. -/
theorem IsNormalizedEigenform.heckeULin_apply_eq_qCoeff_smul (N : ℕ) [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (hf : f.IsNormalizedEigenform)
    (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) :
    CuspForm.heckeULin 2 hqN f = ModularFormClass.qCoeff f q • f :=
  ((isNormalizedEigenform_iff_heckeTLin f).mp hf).2 q hq |>.2 hqN

end CuspForm

/-! ## The coefficient eigenvalue/vanishing pair -/

namespace ModularForm

/-- If a coefficient sequence with `a 1 = 0` satisfies the `T_p`/`U_p` eigenvalue
equations, it vanishes. Stated verbatim from
`Theorems/Thm_ModularForm_eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero.lean`. -/
theorem eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 0) : ∀ n : ℕ, n ≠ 0 → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · obtain rfl : n = 1 := by omega
      exact h1
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm0 : m ≠ 0 := by rintro rfl; simp at hn
      have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
      have hmlt : m < p * m := by nlinarith [hp.two_le]
      have ham : a m = 0 := ih m hmlt hm0
      by_cases hpN : p ∣ N
      · have h := hU p hp hpN m
        rw [ModularForm.coeffHeckeU_apply, ham, mul_zero, mul_comm m p] at h
        exact h
      · have h := hT p hp hpN m
        rw [ModularForm.coeffHeckeT_apply, ham, mul_zero, mul_comm m p] at h
        by_cases hpm : p ∣ m
        · obtain ⟨q, rfl⟩ := hpm
          have hq0 : q ≠ 0 := by rintro rfl; simp at hm0
          have hqlt : q < p * (p * q) := by
            have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
            nlinarith [hp.two_le]
          have haq : a q = 0 := ih q hqlt hq0
          rw [ite_eq_left (dvd_mul_right p q), Nat.mul_div_cancel_left q hp.pos, haq, mul_zero,
            add_zero] at h
          exact h
        · rw [ite_eq_right hpm, add_zero] at h
          exact h

/-- For a coefficient eigenvector with `a 1 = 1`, the eigenvalue at `p` is `a p`.
Stated verbatim from
`Theorems/Thm_ModularForm_coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one.lean`. -/
theorem coeffHecke_eigenvalue_eq_apply_of_apply_one_eq_one (k : ℤ) (N : ℕ) (a c : ℕ → ℂ)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeT k p a n = c p * a n)
    (hU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n : ℕ, ModularForm.coeffHeckeU p a n = c p * a n)
    (h1 : a 1 = 1) : ∀ p : ℕ, p.Prime → c p = a p := by
  intro p hp
  by_cases hpN : p ∣ N
  · have h := hU p hp hpN 1
    rw [ModularForm.coeffHeckeU_apply, one_mul, h1, mul_one] at h
    exact h.symm
  · have h := hT p hp hpN 1
    rw [ModularForm.coeffHeckeT_apply, ite_eq_right hp.not_dvd_one, add_zero, one_mul, h1, mul_one] at h
    exact h.symm

end ModularForm

/-! ## Formal multiplicity one -/

namespace LaurentSeries

/-- Multiplicity one: a formal Laurent series that is a simultaneous eigenvector
of the `T_ℓ`/`U_q` with nonnegative support and `a 1 = 0` vanishes. Stated
verbatim from
`Theorems/Thm_LaurentSeries_eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero.lean`. -/
theorem eq_zero_of_heckeT_eq_smul_of_heckeU_eq_smul_of_coeff_one_eq_zero
    (R : Type*) [CommRing R] (M k : ℕ) (θ : Nat.Primes → R) (f : LaurentSeries R)
    (hneg : ∀ n : ℤ, n ≤ 0 → f.coeff n = 0)
    (hT : ∀ ℓ : Nat.Primes, ¬ (ℓ : ℕ) ∣ M → LaurentSeries.heckeT R (ℓ : ℕ) ℓ.2.pos k f = θ ℓ • f)
    (hU : ∀ q : Nat.Primes, (q : ℕ) ∣ M → LaurentSeries.heckeU R (q : ℕ) q.2.pos f = θ q • f)
    (h1 : f.coeff 1 = 0) :
    f = 0 := by
  have key : ∀ m : ℕ, f.coeff (m : ℤ) = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · exact hneg 0 le_rfl
        · exact_mod_cast h1
      · obtain ⟨ℓ, hℓ, hℓm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
        obtain ⟨m', rfl⟩ := hℓm
        have hℓpos : 0 < ℓ := hℓ.pos
        have hm' : m' < ℓ * m' := by
          have : 1 < ℓ := hℓ.one_lt
          have hm'pos : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm)
          nlinarith
        by_cases hℓN : ℓ ∣ M
        ·
          have := congrArg (fun g : LaurentSeries R => g.coeff (m' : ℤ)) (hU ⟨ℓ, hℓ⟩ hℓN)
          simp only [LaurentSeries.coeff_heckeU, HahnSeries.coeff_smul, smul_eq_mul] at this
          rw [ih m' hm', mul_zero] at this
          exact_mod_cast this
        ·
          have := congrArg (fun g : LaurentSeries R => g.coeff (m' : ℤ)) (hT ⟨ℓ, hℓ⟩ hℓN)
          simp only [LaurentSeries.coeff_heckeT, HahnSeries.coeff_smul, smul_eq_mul] at this
          rw [ih m' hm', mul_zero] at this
          have hif : (if ((ℓ : ℕ) : ℤ) ∣ (m' : ℤ) then f.coeff ((m' : ℤ) / (ℓ : ℕ)) else 0) = 0 := by
            split_ifs with hd
            · obtain ⟨c, hc⟩ := Int.natCast_dvd_natCast.mp hd
              have hcm : c < ℓ * m' := by
                rcases Nat.eq_zero_or_pos c with rfl | hc0
                · simp at hc; subst hc; exact Nat.pos_of_ne_zero (by omega)
                · calc c ≤ ℓ * c := Nat.le_mul_of_pos_left c hℓpos
                    _ = m' := hc.symm
                    _ < ℓ * m' := hm'
              have : (m' : ℤ) / (ℓ : ℕ) = (c : ℤ) := by
                rw [hc]; push_cast; rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast hℓ.ne_zero)]
              rw [this]; exact ih c hcm
            · rfl
          rw [hif, mul_zero, add_zero] at this
          exact_mod_cast this
  ext n
  rcases le_or_gt n 0 with hn | hn
  · simpa using hneg n hn
  · lift n to ℕ using hn.le
    simpa using key n

end LaurentSeries

end

/-! ## The Frobenius/mod-`p` input -/

namespace PowerSeries

/-- `ℓ ^ b ≡ ℓ ^ a` mod `p` when `(p - 1) ∣ (b - a)`. -/
private lemma pow_congr_of_dvd_sub (p : ℕ) [Fact p.Prime] {ℓ : ℕ} (hℓp : ¬ p ∣ ℓ)
    (a b : ℕ) (hab : (p - 1 : ℕ) ∣ b - a) (hba : a ≤ b) :
    (ℓ : integralClosure ℤ ℂ) ^ b - (ℓ : integralClosure ℤ ℂ) ^ a ∈
      Ideal.span {(p : integralClosure ℤ ℂ)} := by
  obtain ⟨t, ht⟩ := hab
  have hz : (p : ℤ) ∣ ℓ ^ (b - a) - 1 := by
    have h0 : ((ℓ ^ (b - a) - 1 : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [ht, pow_mul, ZMod.pow_card_sub_one_eq_one (by
        intro h
        apply hℓp
        have h' : ((ℓ : ℤ) : ZMod p) = 0 := by exact_mod_cast h
        exact Int.natCast_dvd_natCast.mp ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h')), one_pow]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  obtain ⟨u, hu⟩ := hz
  have hsplit : (ℓ : integralClosure ℤ ℂ) ^ b =
      (ℓ : integralClosure ℤ ℂ) ^ a * (ℓ : integralClosure ℤ ℂ) ^ (b - a) := by
    rw [← pow_add]
    congr 1
    omega
  refine Ideal.mem_span_singleton.mpr ⟨(ℓ : integralClosure ℤ ℂ) ^ a * (u : integralClosure ℤ ℂ), ?_⟩
  have hcast := congrArg (fun z : ℤ => ((z : ℤ) : integralClosure ℤ ℂ)) hu
  push_cast at hcast
  rw [hsplit]
  linear_combination (ℓ : integralClosure ℤ ℂ) ^ a * hcast

/-- The mod-`p` congruence feeding the Frobenius machinery. Stated verbatim from
`Theorems/Thm_PowerSeries_coeff_heckeT_pow_sub_mem_span.lean`. -/
theorem coeff_heckeT_pow_sub_mem_span (p : ℕ) [Fact p.Prime] {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform)
    (a : ℕ → integralClosure ℤ ℂ) (ha : ∀ n : ℕ, (a n : ℂ) = ModularFormClass.qCoeff f n)
    (j k : ℕ) (hk : 2 ≤ k) (hk2 : (p - 1 : ℕ) ∣ k - 2)
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.heckeT ℓ k (PowerSeries.mk fun m => a m ^ p ^ j))
      - a ℓ ^ p ^ j * a n ^ p ^ j ∈ Ideal.span {(p : integralClosure ℤ ℂ)} := by
  have hp' : p.Prime := Fact.out
  have hP0 : p ^ j ≠ 0 := pow_ne_zero _ hp'.ne_zero
  rw [PowerSeries.coeff_heckeT]
  simp only [PowerSeries.coeff_mk]
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  ·
    subst hn0
    have ha0 : a 0 = 0 := by
      apply Subtype.coe_injective
      show ((a 0 : integralClosure ℤ ℂ) : ℂ) = ((0 : integralClosure ℤ ℂ) : ℂ)
      rw [ha 0]
      simpa using CuspForm.qCoeff_zero f
    simp [ha0, zero_pow hP0, Nat.zero_div, mul_zero]
  by_cases hdvd : ℓ ∣ n
  ·
    have hn0 : n ≠ 0 := hnpos.ne'
    set e : ℕ := n.factorization ℓ with hedef
    have he1 : 1 ≤ e := (hℓ.factorization_pos_of_dvd hn0 hdvd)
    set m : ℕ := n / ℓ ^ e with hmdef
    have hℓm : ¬ ℓ ∣ m := Nat.not_dvd_ordCompl hℓ hn0
    have hcopm : ∀ r : ℕ, Nat.Coprime (ℓ ^ r) m := fun r =>
      (hℓ.coprime_iff_not_dvd.mpr hℓm).pow_left _
    have hn : n = ℓ ^ e * m := (Nat.ordProj_mul_ordCompl_eq_self n ℓ).symm
    have hℓn : ℓ * n = ℓ ^ (e + 1) * m := by
      rw [hn, pow_succ]
      ring
    have hndiv : n / ℓ = ℓ ^ (e - 1) * m := by
      rw [hn, show (ℓ : ℕ) ^ e = ℓ * ℓ ^ (e - 1) from by
        rw [← pow_succ']
        congr 1
        omega]
      rw [mul_assoc]
      exact Nat.mul_div_cancel_left _ hℓ.pos

    have haℓn : a (ℓ * n) = a ℓ * a n - (ℓ : integralClosure ℤ ℂ) * a (n / ℓ) := by
      apply Subtype.coe_injective
      push_cast
      rw [ha, ha, ha, ha, hℓn, hndiv, hn,
        hf.qCoeff_mul_of_coprime _ _ (hcopm (e + 1)),
        hf.qCoeff_mul_of_coprime _ _ (hcopm e),
        hf.qCoeff_mul_of_coprime _ _ (hcopm (e - 1)),
        show e + 1 = (e - 1) + 2 from by omega,
        hf.qCoeff_prime_pow_of_not_dvd ℓ (e - 1) hℓ hℓN,
        show (e - 1) + 1 = e from by omega]
      ring

    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp'
      (a (ℓ * n)) ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) j
    have hsum : a (ℓ * n) + (ℓ : integralClosure ℤ ℂ) * a (n / ℓ) = a ℓ * a n := by
      rw [haℓn]
      ring
    rw [hsum] at hr

    have hexp : (ℓ : integralClosure ℤ ℂ) ^ (k - 1) - (ℓ : integralClosure ℤ ℂ) ^ p ^ j ∈
        Ideal.span {(p : integralClosure ℤ ℂ)} := by
      by_cases hℓp : ℓ = p
      · subst hℓp
        refine Ideal.mem_span_singleton.mpr ⟨(ℓ : integralClosure ℤ ℂ) ^ (k - 2) -
          (ℓ : integralClosure ℤ ℂ) ^ (ℓ ^ j - 1), ?_⟩
        have h1 : (ℓ : integralClosure ℤ ℂ) ^ (k - 1) =
            (ℓ : integralClosure ℤ ℂ) * (ℓ : integralClosure ℤ ℂ) ^ (k - 2) := by
          rw [← pow_succ']
          congr 1
          omega
        have h2 : (ℓ : integralClosure ℤ ℂ) ^ ℓ ^ j =
            (ℓ : integralClosure ℤ ℂ) * (ℓ : integralClosure ℤ ℂ) ^ (ℓ ^ j - 1) := by
          rw [← pow_succ']
          congr 1
          have := Nat.one_le_pow j ℓ hℓ.pos
          omega
        rw [h1, h2]
        ring
      · have hpℓ : ¬ p ∣ ℓ := fun hd => hℓp ((Nat.prime_dvd_prime_iff_eq hp' hℓ).mp hd).symm
        have h1 := pow_congr_of_dvd_sub p hpℓ 1 (k - 1)
          (by rw [show (k - 1) - 1 = k - 2 from by omega]; exact hk2) (by omega)
        have hnatdvd : (p - 1 : ℕ) ∣ p ^ j - 1 := by
          have hZ : ((p : ℤ) - 1) ∣ (p : ℤ) ^ j - 1 := by
            simpa using sub_dvd_pow_sub_pow (p : ℤ) 1 j
          have e1 : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := by
            rw [Nat.cast_sub hp'.one_lt.le, Nat.cast_one]
          have e2 : ((p ^ j - 1 : ℕ) : ℤ) = (p : ℤ) ^ j - 1 := by
            rw [Nat.cast_sub (Nat.one_le_pow j p hp'.pos), Nat.cast_one, Nat.cast_pow]
          exact Int.natCast_dvd_natCast.mp (by rw [e1, e2]; exact hZ)
        have h2 := pow_congr_of_dvd_sub p hpℓ 1 (p ^ j)
          (by simpa using hnatdvd) (Nat.one_le_pow _ _ hp'.pos)
        have := Ideal.sub_mem _ h1 h2
        simpa using this

    simp only [ite_eq_left hdvd]
    have hfin : a (ℓ * n) ^ p ^ j +
        (ℓ : integralClosure ℤ ℂ) ^ (k - 1) * a (n / ℓ) ^ p ^ j -
        a ℓ ^ p ^ j * a n ^ p ^ j =
        ((ℓ : integralClosure ℤ ℂ) ^ (k - 1) - (ℓ : integralClosure ℤ ℂ) ^ p ^ j) *
          a (n / ℓ) ^ p ^ j -
        (p : integralClosure ℤ ℂ) *
          (a (ℓ * n) * ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) * r) := by
      have hmp : (a ℓ * a n) ^ p ^ j = a ℓ ^ p ^ j * a n ^ p ^ j := mul_pow _ _ _
      have hlp : ((ℓ : integralClosure ℤ ℂ) * a (n / ℓ)) ^ p ^ j =
          (ℓ : integralClosure ℤ ℂ) ^ p ^ j * a (n / ℓ) ^ p ^ j := mul_pow _ _ _
      linear_combination hmp - hr - hlp
    rw [hfin]
    exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ hexp)
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_singleton _)))
  ·
    have hcop : Nat.Coprime ℓ n := hℓ.coprime_iff_not_dvd.mpr hdvd
    have haℓn : a (ℓ * n) = a ℓ * a n := by
      apply Subtype.coe_injective
      push_cast
      rw [ha, ha, ha, hf.qCoeff_mul_of_coprime _ _ hcop]
    simp only [ite_eq_right hdvd, mul_zero, add_zero]
    rw [haℓn, mul_pow]
    simp

end PowerSeries
