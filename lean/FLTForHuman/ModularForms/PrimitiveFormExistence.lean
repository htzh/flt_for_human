/-
  The existence of a primitive form behind a Hecke eigenform, and the `j`-conjugation invariance of a
  cusp form.

  * `CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen`: a `Γ₁(M)`-cusp form with
    nebentypus whose coefficients satisfy the Hecke eigen-relation at every prime has a *primitive*
    form with the same eigenvalues (`PrimitiveFormOfEigenvector`).
  * `CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen`: the same without the nebentypus hypothesis
    (`PrimitiveFormOfEigenform`).
  * `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem`: a cusp form invariant under the
    `j`-conjugation on `SL(2, ℤ)` is determined by its values at `J • τ`.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `S_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen.lean` (253 lines),
  `S_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen.lean` (254) and
  `S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.lean` (69), with the statements
  from the wrappers of the same names.  The pin label namespaces are word names and are kept:
  `PrimitiveFormOfEigenvector`, `PrimitiveFormOfEigenform` and `CuspForm.ConjInvolution`.

  Assumes from earlier modules: `ModularForms/NewformDecomposition.lean` (the newform decomposition,
  their only premise) and `ModularForms/Defs/PrimitiveFormGamma1.lean`.

  spec-pin: Theorems/Thm_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen.lean
  spec-pin: Theorems/Thm_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_isPrimitiveForm_of_qCoeff_hecke_eigen.lean
  spec-pin: Theorems/Thm_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem.lean
-/
import FLTForHuman.ModularForms.NewformDecomposition
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckeNebentypusExistence
import FLTForHuman.ModularCurve.PeriodHomPair
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section



open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups


namespace PrimitiveFormOfEigenvector

theorem exists_packet_eq {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (v : ι → V) (β : ι → P → K) (α : P → K) (s : Finset ι) :
    ∀ c : ι → K,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ p, T p (∑ i ∈ s, c i • v i) = α p • ∑ i ∈ s, c i • v i) →
      (∑ i ∈ s, c i • v i ≠ 0) →
      ∃ i ∈ s, ∀ p, β i p = α p := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hv hw hne
    by_cases hall : ∃ i ∈ s, ∀ p, β i p = α p
    · exact hall
    push Not at hall
    have hsne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact hne (by simp)
    obtain ⟨j, hj⟩ := hsne
    obtain ⟨p₀, hp₀⟩ := hall j hj
    set w : V := ∑ i ∈ s, c i • v i with hwdef

    set c' : ι → K := fun i => c i * (β i p₀ - β j p₀) with hc'
    have hsum : ∑ i ∈ s, c' i • v i = (α p₀ - β j p₀) • w := by
      have h2 : ∑ i ∈ s, c' i • v i = T p₀ w - β j p₀ • w := by
        rw [hwdef, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_smul, hv i hi p₀, smul_smul, smul_smul, ← sub_smul, hc']
        congr 1
        ring
      rw [h2, hw p₀, sub_smul]
    have herase : ∑ i ∈ s.erase j, c' i • v i = ∑ i ∈ s, c' i • v i := by
      apply Finset.sum_erase
      rw [hc']
      simp
    have hne' : ∑ i ∈ s.erase j, c' i • v i ≠ 0 := by
      rw [herase, hsum]
      exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hp₀)) hne
    have heig' : ∀ p, T p (∑ i ∈ s.erase j, c' i • v i) = α p • ∑ i ∈ s.erase j, c' i • v i := by
      intro p
      rw [herase, hsum, map_smul, hw p, smul_comm]
    obtain ⟨i, hi, hβ⟩ := ih (s.erase j) (Finset.erase_ssubset hj) c'
      (fun i hi p => hv i (Finset.mem_of_mem_erase hi) p) heig' hne'
    exact ⟨i, Finset.mem_of_mem_erase hi, hβ⟩

def heckeSeq (k : ℤ) (e : ℕ → ℂ) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun s := fun n => s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0)
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeSeq_apply (k : ℤ) (e : ℕ → ℂ) (p : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    heckeSeq k e p s n = s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0) := by
  rfl

def stretchSeq (d : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun n => if d ∣ n then b (n / d) else 0

theorem stretchSeq_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchSeq d b n = if d ∣ n then b (n / d) else 0 := by
  rfl

theorem heckeSeq_stretchSeq {k : ℤ} {e : ℕ → ℂ} {p d : ℕ} (hp0 : p ≠ 0) (hd : d ≠ 0)
    (hpd : Nat.Coprime p d)
    {b : ℕ → ℂ} {lam : ℂ}
    (hb : ∀ m : ℕ, b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = lam * b m) :
    heckeSeq k e p (stretchSeq d b) = lam • stretchSeq d b := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, Pi.smul_apply, smul_eq_mul, stretchSeq_apply]
  by_cases hdn : d ∣ n
  ·
    obtain ⟨m, rfl⟩ := hdn
    have h1 : d ∣ p * (d * m) := ⟨p * m, by ring⟩
    have h2 : p * (d * m) / d = p * m := by
      rw [show p * (d * m) = d * (p * m) by ring, Nat.mul_div_cancel_left _ hdpos]
    have h3 : d * m / d = m := Nat.mul_div_cancel_left _ hdpos
    rw [ite_eq_left h1, h2, ite_eq_left (dvd_mul_right d m), h3]
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      have h4 : p ∣ d * (p * r) := ⟨d * r, by ring⟩
      have h5 : d * (p * r) / p = d * r := by
        rw [show d * (p * r) = p * (d * r) by ring, Nat.mul_div_cancel_left _ hppos]
      rw [ite_eq_left h4, h5, ite_eq_left (dvd_mul_right d r), Nat.mul_div_cancel_left _ hdpos]
      have := hb (p * r)
      rw [ite_eq_left (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos] at this
      exact this
    · have h4 : ¬ p ∣ d * m := fun h => hpm (hpd.dvd_of_dvd_mul_left h)
      rw [ite_eq_right h4]
      have := hb m
      rw [ite_eq_right hpm] at this
      exact this
  ·
    have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
    rw [ite_eq_right h1, ite_eq_right hdn, mul_zero]
    have hmid : (if p ∣ n then (if d ∣ n / p then b (n / p / d) else 0) else 0) = 0 := by
      split_ifs with hpn hdnp
      · exact absurd (dvd_trans hdnp (Nat.div_dvd_of_dvd hpn)) hdn
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

theorem changeLevel_apply_natCast {M N : ℕ} [NeZero N] (hMN : M ∣ N) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N) (h : DirichletCharacter.changeLevel hMN εM = ε)
    (p : ℕ) (hp : Nat.Coprime p N) :
    εM (p : ZMod M) = ε (p : ZMod N) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu
  have hu' : (u : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hp
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu', ZMod.cast_natCast hMN]

theorem one_mem_strictPeriods (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem eq_zero_of_forall_qCoeff_eq_zero {N : ℕ} {k : ℤ} (f : CuspForm (Gamma1 N) k)
    (h : ∀ n : ℕ, qCoeff f n = 0) : f = 0 := by
  have hΓ := one_mem_strictPeriods N
  have hcusp : Fact (IsCusp OnePoint.infty
      ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  have hq : UpperHalfPlane.qExpansion 1 (⇑f) = 0 := by
    ext n
    simpa [qCoeff] using h n
  have hcoe : (⇑f : UpperHalfPlane → ℂ) = 0 :=
    (UpperHalfPlane.qExpansion_eq_zero_iff one_pos
      (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ) (ModularFormClass.holo f)
      (ModularFormClass.bdd_at_infty f)).mp hq
  exact DFunLike.ext f 0 fun τ => by simpa using congrFun hcoe τ

theorem main
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus ε f) (lam : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (εM : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = lam p ∧ εM (p : ZMod M) = ε (p : ZMod N) := by
  classical

  obtain ⟨n, M, d, hMd, εM, g, c, hprim, hdec⟩ :=
    CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus N k ε f hε

  set e : ℕ → ℂ := fun m => ε (m : ZMod N) with he
  let T : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => heckeSeq k e p
  let a : ℕ → ℂ := fun m => ModularFormClass.qCoeff f m
  let v : Fin n → (ℕ → ℂ) := fun i => stretchSeq (d i) (fun m => ModularFormClass.qCoeff (g i) m)

  let good : ℕ → Prop := fun p => p.Prime ∧ ¬ p ∣ N
  let α : ℕ → ℂ := fun p => if good p then lam p else 0
  let β : Fin n → ℕ → ℂ := fun i p => if good p then ModularFormClass.qCoeff (g i) p else 0
  let T' : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => if good p then T p else 0

  have hM_dvd : ∀ i, M i ∣ N := fun i => dvd_of_mul_right_dvd (hMd i)
  have hd_dvd : ∀ i, d i ∣ N := fun i => dvd_of_mul_left_dvd (hMd i)
  have hd_ne : ∀ i, d i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hd_dvd i))
  have hM_ne : ∀ i, M i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hM_dvd i))

  have ha_sum : (∑ i ∈ Finset.univ, c i • v i) = a := by
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, v, stretchSeq_apply, a]
    exact (hdec m).symm

  have hv : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ p, T' p (v i) = β i p • v i := by
    intro i _ p
    by_cases hg : good p
    · simp only [T', β, ite_eq_left hg]
      obtain ⟨hp, hpN⟩ := hg
      have hpM : ¬ p ∣ M i := fun h => hpN (dvd_trans h (hM_dvd i))
      have hpd : Nat.Coprime p (d i) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (dvd_trans h (hd_dvd i))
      have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
      have hεi : εM i (p : ZMod (M i)) = ε (p : ZMod N) :=
        changeLevel_apply_natCast (hM_dvd i) (εM i) ε (hprim i).2 p hpcop
      refine heckeSeq_stretchSeq hp.ne_zero (hd_ne i) hpd fun m => ?_
      have h := (hprim i).1.isEigenformWith.hecke_of_not_dvd hp hpM m
      rw [hεi] at h
      exact h
    · simp only [T', β, ite_eq_right hg, LinearMap.zero_apply, zero_smul]

  have ha : ∀ p, T' p a = α p • a := by
    intro p
    by_cases hg : good p
    · simp only [T', α, ite_eq_left hg]
      obtain ⟨hp, hpN⟩ := hg
      funext m
      rw [Pi.smul_apply, smul_eq_mul]
      change heckeSeq k e p a m = _
      rw [heckeSeq_apply]
      exact hf p hp hpN m
    · simp only [T', α, ite_eq_right hg, LinearMap.zero_apply, zero_smul]
  have hw : ∀ p, T' p (∑ i ∈ Finset.univ, c i • v i) = α p • ∑ i ∈ Finset.univ, c i • v i := by
    intro p; rw [ha_sum]; exact ha p

  have hne : (∑ i ∈ Finset.univ, c i • v i) ≠ 0 := by
    rw [ha_sum]
    intro h0
    exact hf0 (eq_zero_of_forall_qCoeff_eq_zero f fun m => congrFun h0 m)

  obtain ⟨i, -, hi⟩ := exists_packet_eq T' v β α Finset.univ c hv hw hne
  have : NeZero (M i) := ⟨hM_ne i⟩
  refine ⟨M i, ⟨hM_ne i⟩, εM i, g i, hM_dvd i, (hprim i).1, fun p hp hpN => ⟨?_, ?_⟩⟩
  · have h := hi p
    simp only [β, α, ite_eq_left (show good p from ⟨hp, hpN⟩)] at h
    exact h
  · have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    exact changeLevel_apply_natCast (hM_dvd i) (εM i) ε (hprim i).2 p hpcop

end PrimitiveFormOfEigenvector

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_isPrimitiveForm_of_hasNebentypus_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k) (hf0 : f ≠ 0)
    (hε : CuspForm.HasNebentypus ε f) (lam : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          lam p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (εM : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm εM g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = lam p ∧ εM (p : ZMod M) = ε (p : ZMod N) := by
  exact PrimitiveFormOfEigenvector.main N k ε f hf0 hε lam hf

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups


namespace PrimitiveFormOfEigenform

theorem exists_packet_eq {K V P ι : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (v : ι → V) (β : ι → P → K) (α : P → K) (s : Finset ι) :
    ∀ c : ι → K,
      (∀ i ∈ s, ∀ p, T p (v i) = β i p • v i) →
      (∀ p, T p (∑ i ∈ s, c i • v i) = α p • ∑ i ∈ s, c i • v i) →
      (∑ i ∈ s, c i • v i ≠ 0) →
      ∃ i ∈ s, ∀ p, β i p = α p := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
    intro c hv hw hne
    by_cases hall : ∃ i ∈ s, ∀ p, β i p = α p
    · exact hall
    push Not at hall
    have hsne : s.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      rintro rfl
      exact hne (by simp)
    obtain ⟨j, hj⟩ := hsne
    obtain ⟨p₀, hp₀⟩ := hall j hj
    set w : V := ∑ i ∈ s, c i • v i with hwdef
    set c' : ι → K := fun i => c i * (β i p₀ - β j p₀) with hc'
    have hsum : ∑ i ∈ s, c' i • v i = (α p₀ - β j p₀) • w := by
      have h2 : ∑ i ∈ s, c' i • v i = T p₀ w - β j p₀ • w := by
        rw [hwdef, map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [map_smul, hv i hi p₀, smul_smul, smul_smul, ← sub_smul, hc']
        congr 1
        ring
      rw [h2, hw p₀, sub_smul]
    have herase : ∑ i ∈ s.erase j, c' i • v i = ∑ i ∈ s, c' i • v i := by
      apply Finset.sum_erase
      rw [hc']
      simp
    have hne' : ∑ i ∈ s.erase j, c' i • v i ≠ 0 := by
      rw [herase, hsum]
      exact smul_ne_zero (sub_ne_zero.mpr (Ne.symm hp₀)) hne
    have heig' : ∀ p, T p (∑ i ∈ s.erase j, c' i • v i) = α p • ∑ i ∈ s.erase j, c' i • v i := by
      intro p
      rw [herase, hsum, map_smul, hw p, smul_comm]
    obtain ⟨i, hi, hβ⟩ := ih (s.erase j) (Finset.erase_ssubset hj) c'
      (fun i hi p => hv i (Finset.mem_of_mem_erase hi) p) heig' hne'
    exact ⟨i, Finset.mem_of_mem_erase hi, hβ⟩

def heckeSeq (k : ℤ) (e : ℕ → ℂ) (p : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun s := fun n => s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0)
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeSeq_apply (k : ℤ) (e : ℕ → ℂ) (p : ℕ) (s : ℕ → ℂ) (n : ℕ) :
    heckeSeq k e p s n = s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0) := by
  rfl

def stretchSeq (d : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun n => if d ∣ n then b (n / d) else 0

theorem stretchSeq_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchSeq d b n = if d ∣ n then b (n / d) else 0 := by
  rfl

theorem heckeSeq_stretchSeq {k : ℤ} {e : ℕ → ℂ} {p d : ℕ} (hp0 : p ≠ 0) (hd : d ≠ 0)
    (hpd : Nat.Coprime p d)
    {b : ℕ → ℂ} {lam : ℂ}
    (hb : ∀ m : ℕ, b (p * m) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ m then b (m / p) else 0) = lam * b m) :
    heckeSeq k e p (stretchSeq d b) = lam • stretchSeq d b := by
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  funext n
  simp only [heckeSeq_apply, Pi.smul_apply, smul_eq_mul, stretchSeq_apply]
  by_cases hdn : d ∣ n
  ·
    obtain ⟨m, rfl⟩ := hdn
    have h1 : d ∣ p * (d * m) := ⟨p * m, by ring⟩
    have h2 : p * (d * m) / d = p * m := by
      rw [show p * (d * m) = d * (p * m) by ring, Nat.mul_div_cancel_left _ hdpos]
    have h3 : d * m / d = m := Nat.mul_div_cancel_left _ hdpos
    rw [ite_eq_left h1, h2, ite_eq_left (dvd_mul_right d m), h3]
    by_cases hpm : p ∣ m
    · obtain ⟨r, rfl⟩ := hpm
      have h4 : p ∣ d * (p * r) := ⟨d * r, by ring⟩
      have h5 : d * (p * r) / p = d * r := by
        rw [show d * (p * r) = p * (d * r) by ring, Nat.mul_div_cancel_left _ hppos]
      rw [ite_eq_left h4, h5, ite_eq_left (dvd_mul_right d r), Nat.mul_div_cancel_left _ hdpos]
      have := hb (p * r)
      rw [ite_eq_left (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos] at this
      exact this
    · have h4 : ¬ p ∣ d * m := fun h => hpm (hpd.dvd_of_dvd_mul_left h)
      rw [ite_eq_right h4]
      have := hb m
      rw [ite_eq_right hpm] at this
      exact this
  ·
    have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
    rw [ite_eq_right h1, ite_eq_right hdn, mul_zero]
    have hmid : (if p ∣ n then (if d ∣ n / p then b (n / p / d) else 0) else 0) = 0 := by
      split_ifs with hpn hdnp
      · exact absurd (dvd_trans hdnp (Nat.div_dvd_of_dvd hpn)) hdn
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

theorem changeLevel_apply_natCast {M N : ℕ} [NeZero N] (hMN : M ∣ N) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N) (h : DirichletCharacter.changeLevel hMN εM = ε)
    (p : ℕ) (hp : Nat.Coprime p N) :
    εM (p : ZMod M) = ε (p : ZMod N) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu
  have hu' : (u : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hp
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu', ZMod.cast_natCast hMN]

end PrimitiveFormOfEigenform

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_isPrimitiveForm_of_qCoeff_hecke_eigen
    (N : ℕ) [NeZero N] (k : ℤ) (f : CuspForm (Gamma1 N) k)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (χ : ℕ → ℂ)
    (hf : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            χ p * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n) :
    ∃ (M : ℕ) (_ : NeZero M) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k),
      M ∣ N ∧ CuspForm.IsPrimitiveForm ε g ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        ModularFormClass.qCoeff g p = ModularFormClass.qCoeff f p ∧
          ε (p : ZMod M) * (p : ℂ) ^ (k - 1) = χ p := by
  classical

  have hf0 : f ≠ 0 := by
    intro h
    have : ModularFormClass.qCoeff (⇑f) 1 = 0 := by
      rw [h, ModularFormClass.qCoeff, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero, map_zero]
    rw [this] at hf₁
    exact zero_ne_one hf₁

  obtain ⟨εN, hεN, hεNp⟩ :=
    CuspForm.exists_hasNebentypus_of_qCoeff_hecke_eigen N k f hf0 χ
      (fun p hp hpN => ⟨ModularFormClass.qCoeff f p, hf p hp hpN⟩)

  obtain ⟨n, M, d, hMd, εM, g, c, hprim, hdec⟩ :=
    CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus N k εN f hεN

  set e : ℕ → ℂ := fun m => εN (m : ZMod N) with he
  let T : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => PrimitiveFormOfEigenform.heckeSeq k e p
  let a : ℕ → ℂ := fun m => ModularFormClass.qCoeff f m
  let v : Fin n → (ℕ → ℂ) :=
    fun i => PrimitiveFormOfEigenform.stretchSeq (d i) (fun m => ModularFormClass.qCoeff (g i) m)

  let good : ℕ → Prop := fun p => p.Prime ∧ ¬ p ∣ N
  let α : ℕ → ℂ := fun p => if good p then ModularFormClass.qCoeff f p else 0
  let β : Fin n → ℕ → ℂ := fun i p => if good p then ModularFormClass.qCoeff (g i) p else 0
  let T' : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => if good p then T p else 0

  have hM_dvd : ∀ i, M i ∣ N := fun i => dvd_of_mul_right_dvd (hMd i)
  have hd_dvd : ∀ i, d i ∣ N := fun i => dvd_of_mul_left_dvd (hMd i)
  have hd_ne : ∀ i, d i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hd_dvd i))
  have hM_ne : ∀ i, M i ≠ 0 := fun i h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hM_dvd i))

  have ha_sum : (∑ i ∈ Finset.univ, c i • v i) = a := by
    funext m
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, v, PrimitiveFormOfEigenform.stretchSeq_apply, a]
    exact (hdec m).symm

  have hv : ∀ i ∈ (Finset.univ : Finset (Fin n)), ∀ p, T' p (v i) = β i p • v i := by
    intro i _ p
    by_cases hg : good p
    · simp only [T', β, ite_eq_left hg]
      obtain ⟨hp, hpN⟩ := hg
      have hpM : ¬ p ∣ M i := fun h => hpN (dvd_trans h (hM_dvd i))
      have hpd : Nat.Coprime p (d i) :=
        (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => hpN (dvd_trans h (hd_dvd i))
      have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
      have hεi : εM i (p : ZMod (M i)) = εN (p : ZMod N) :=
        PrimitiveFormOfEigenform.changeLevel_apply_natCast (hM_dvd i) (εM i) εN (hprim i).2 p hpcop
      refine PrimitiveFormOfEigenform.heckeSeq_stretchSeq hp.ne_zero (hd_ne i) hpd fun m => ?_
      have h := (hprim i).1.isEigenformWith.hecke_of_not_dvd hp hpM m
      rw [hεi] at h
      exact h
    · simp only [T', β, ite_eq_right hg, LinearMap.zero_apply, zero_smul]

  have ha : ∀ p, T' p a = α p • a := by
    intro p
    by_cases hg : good p
    · simp only [T', α, ite_eq_left hg]
      obtain ⟨hp, hpN⟩ := hg
      funext m
      rw [Pi.smul_apply, smul_eq_mul]
      change PrimitiveFormOfEigenform.heckeSeq k e p a m = _
      rw [PrimitiveFormOfEigenform.heckeSeq_apply]
      have h := hf p hp hpN m
      rw [← hεNp p hp hpN] at h
      exact h
    · simp only [T', α, ite_eq_right hg, LinearMap.zero_apply, zero_smul]
  have hw : ∀ p, T' p (∑ i ∈ Finset.univ, c i • v i) = α p • ∑ i ∈ Finset.univ, c i • v i := by
    intro p; rw [ha_sum]; exact ha p
  have hne : (∑ i ∈ Finset.univ, c i • v i) ≠ 0 := by
    rw [ha_sum]
    intro h0
    have : a 1 = 0 := by rw [h0]; rfl
    change ModularFormClass.qCoeff f 1 = 0 at this
    rw [hf₁] at this
    exact one_ne_zero this

  obtain ⟨i, -, hi⟩ :=
    PrimitiveFormOfEigenform.exists_packet_eq T' v β α Finset.univ c hv hw hne
  have : NeZero (M i) := ⟨hM_ne i⟩
  refine ⟨M i, ⟨hM_ne i⟩, εM i, g i, hM_dvd i, (hprim i).1, fun p hp hpN => ⟨?_, ?_⟩⟩
  · have h := hi p
    simp only [β, α, ite_eq_left (show good p from ⟨hp, hpN⟩)] at h
    exact h
  · have hpcop : Nat.Coprime p N := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpN
    rw [PrimitiveFormOfEigenform.changeLevel_apply_natCast (hM_dvd i) (εM i) εN (hprim i).2 p hpcop]
    exact hεNp p hp hpN

open UpperHalfPlane Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm ComplexConjugate Pointwise


namespace CuspForm
namespace ConjInvolution
open CuspForm
theorem J_inv_mul_mapGL_mul_J (γ : SL(2, ℤ)) :
    UpperHalfPlane.J⁻¹ * (mapGL ℝ γ : GL (Fin 2) ℝ) * UpperHalfPlane.J =
      (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) := by
  have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
    rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
  rw [hJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [UpperHalfPlane.J, Matrix.mul_apply, Fin.sum_univ_two, ModularCurve.Period.jConjMat,
      Matrix.GeneralLinearGroup.mkOfDetNeZero, Matrix.vecMul, dotProduct]

theorem conjAct_J_inv_smul_eq (Γ : Subgroup SL(2, ℤ))
    (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) :
    ConjAct.toConjAct (UpperHalfPlane.J)⁻¹ • (Γ : Subgroup (GL (Fin 2) ℝ)) =
      (Γ : Subgroup (GL (Fin 2) ℝ)) := by
  ext x
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← ConjAct.toConjAct_inv, inv_inv,
    ConjAct.toConjAct_smul]
  constructor
  · rintro ⟨γ, hγ, hx⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    rw [← J_inv_mul_mapGL_mul_J]
    rw [show (mapGL ℝ γ : GL (Fin 2) ℝ) = UpperHalfPlane.J * x * UpperHalfPlane.J⁻¹ from hx]
    group
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨ModularCurve.Period.jConjSL γ, hΓ γ hγ, ?_⟩
    change (mapGL ℝ (ModularCurve.Period.jConjSL γ) : GL (Fin 2) ℝ) = _
    rw [← J_inv_mul_mapGL_mul_J]
    have hJ : UpperHalfPlane.J⁻¹ = UpperHalfPlane.J := by
      rw [inv_eq_iff_mul_eq_one, ← sq, UpperHalfPlane.J_sq]
    rw [hJ]

def conjOf (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) : CuspForm Γ k :=
  (CuspForm.translate f UpperHalfPlane.J).copy ((⇑f) ∣[k] UpperHalfPlane.J) rfl
    (conjAct_J_inv_smul_eq Γ hΓ).symm

theorem conjOf_apply (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) {k : ℤ}
    (f : CuspForm Γ k) (τ : ℍ) : conjOf Γ hΓ f τ = conj (f (UpperHalfPlane.J • τ)) := by
  show ((⇑f) ∣[k] UpperHalfPlane.J) τ = _
  rw [ModularForm.slash_def]
  simp [UpperHalfPlane.sigma_J, UpperHalfPlane.denom_J, UpperHalfPlane.det_J]

end CuspForm.ConjInvolution

open scoped MatrixGroups

theorem CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    (Γ : Subgroup SL(2, ℤ)) (hΓ : ∀ γ ∈ Γ, ModularCurve.Period.jConjSL γ ∈ Γ) (k : ℤ)
    (f : CuspForm Γ k) :
    ∃ g : CuspForm Γ k, ∀ τ : UpperHalfPlane, g τ = (starRingEnd ℂ) (f (UpperHalfPlane.J • τ)) := by
  exact ⟨CuspForm.ConjInvolution.conjOf Γ hΓ f, CuspForm.ConjInvolution.conjOf_apply Γ hΓ f⟩


end
