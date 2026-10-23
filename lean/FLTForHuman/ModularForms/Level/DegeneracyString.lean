/-
  The degeneracy string of a `Γ₁` eigenform: its `T_ℓ` and `U_q` action.

  Fix `L ∣ M`, a Dirichlet character `εL` modulo `L`, and a `Γ₁(L)` cusp form `g`
  with `IsEigenformWith εL g`. The statements below are phrased on a
  *hypothesised* family `G : ℕ → CuspForm (Γ₁(M)) k` whose members are the
  degeneracy images `G_d(τ) = g(d τ)` for `d ∣ M / L` — the hypothesis pattern
  `(G, hG)` on which the whole oldform theory is stated. `G` is never
  constructed here: the `Γ₀` construction (`Level/Degeneracy.lean`) builds the
  map, this module acts on the string.

  The two headlines are the pin's `M4bOld` and `M4cStrings` blocks — one
  development cut in two by the pin's artifact split — transcribed at their
  `Theorems/` wrappers' statements. The pin's `main` and `solution` are not
  carried: `main` has the headline's statement, so the proofs are written at
  the headlines.

  FLT provenance (pinned `aa2d8b3`):
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean

  spec-pin: Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean
  spec-pin: Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean
  spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean
-/
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.HeckeAnalytic
import FLTForHuman.ModularForms.HeckePrelude

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology
open ModularForm ModularFormClass

namespace CuspForm

namespace IsEigenformWith

/-- The coset form of `T_ℓ` acts on the degeneracy `G_d` of a `Γ₁(L)` eigenform by
the eigenvalue at level `L`, for `ℓ ∤ M` prime and `d ∣ M / L`. Stated verbatim
from
`Theorems/Thm_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean`. -/
theorem heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    ModularForm.heckeU k ℓ ⇑(G d) + εL (ℓ : ZMod L) • ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) =
      ModularFormClass.qCoeff g ℓ • ⇑(G d) := by
  classical
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hML : M / L ≠ 0 := by
    obtain ⟨e, he⟩ := hLM
    rw [he, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (NeZero.ne L))]
    rintro rfl
    exact NeZero.ne M (by rw [he, mul_zero])
  have hd0 : d ≠ 0 := fun h0 => hML (Nat.eq_zero_of_zero_dvd (h0 ▸ hd))
  have hℓL : ¬ ℓ ∣ L := fun h => hℓM (h.trans hLM)
  have hℓd : ¬ ℓ ∣ d := fun h => hℓM ((h.trans hd).trans (Nat.div_dvd_of_dvd hLM))
  have hcop : Nat.Coprime ℓ d := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr hℓd

  have hper : Periodic (⇑(G d) ∘ ofComplex) 1 := cusp_periodic (G d)
  have hhol : MDiff (⇑(G d) : ℍ → ℂ) := cusp_holo (G d)
  have hbdd : IsBoundedAtImInfty (⇑(G d) : ℍ → ℂ) := cusp_bdd (G d)
  have gper : Periodic (⇑g ∘ ofComplex) 1 := cusp_periodic g
  have ghol : MDiff (⇑g : ℍ → ℂ) := cusp_holo g
  have gbdd : IsBoundedAtImInfty (⇑g : ℍ → ℂ) := cusp_bdd g

  have hcoe : (⇑(G d) : ℍ → ℂ) = fun τ => g (ModularForm.heckeDiagMatrix d • τ) :=
    funext (hG d hd)
  have hb : ∀ m : ℕ, qCoeff (⇑(G d)) m = if d ∣ m then qCoeff (⇑g) (m / d) else 0 := by
    intro m
    rw [hcoe]
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul gper ghol gbdd hd0 m

  have hD : (⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ
      = ModularForm.heckeT k ℓ ⇑(G d) - ModularForm.heckeU k ℓ ⇑(G d) := by
    rw [ModularForm.heckeT_eq_heckeU_add, add_sub_cancel_left]

  have hUper := ModularForm.periodic_heckeU_comp_ofComplex hper k ℓ
  have hUhol := ModularForm.mdifferentiable_heckeU hhol k ℓ
  have hUbdd := ModularForm.isBoundedAtImInfty_heckeU hbdd k ℓ
  have hTper := ModularForm.periodic_heckeT_comp_ofComplex hper k ℓ
  have hThol := ModularForm.mdifferentiable_heckeT hhol k ℓ
  have hTbdd := ModularForm.isBoundedAtImInfty_heckeT hbdd k ℓ
  have hDper : Periodic (((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) ∘ ofComplex) 1 := by
    rw [hD]; exact UpperHalfPlane.periodic_sub hTper hUper
  have hDhol : MDiff ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
    rw [hD]; exact hThol.sub hUhol
  have hDbdd : IsBoundedAtImInfty ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) := by
    rw [hD]; exact hTbdd.sub hUbdd
  set c : ℂ := εL (ℓ : ZMod L) with hc
  have hcDper := UpperHalfPlane.periodic_smul hDper c
  have hcDhol := hDhol.const_smul c
  have hcDbdd : IsBoundedAtImInfty (c • ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ)) :=
    hDbdd.const_smul_left c

  refine UpperHalfPlane.eq_of_forall_qCoeff_eq (UpperHalfPlane.periodic_add hUper hcDper)
    (hUhol.add hcDhol) (hUbdd.add hcDbdd) (UpperHalfPlane.periodic_smul hper _)
    (hhol.const_smul _) (hbdd.const_smul_left _) fun n => ?_
  have hqU : qCoeff (ModularForm.heckeU k ℓ ⇑(G d)) n = qCoeff ⇑(G d) (n * ℓ) := by
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hℓ0 n, ModularForm.coeffHeckeU_apply]
  have hqT : qCoeff (ModularForm.heckeT k ℓ ⇑(G d)) n
      = qCoeff ⇑(G d) (n * ℓ)
        + (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) := by
    rw [UpperHalfPlane.qCoeff_heckeT hper hhol hbdd k hℓ0 n, ModularForm.coeffHeckeT_apply]
  have hqD : qCoeff ((⇑(G d)) ∣[k] ModularForm.heckeDiagMatrix ℓ) n
      = (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) := by
    rw [hD, ModularFormClass.qCoeff_sub hTper hThol hTbdd hUper hUhol hUbdd, hqT, hqU,
      add_sub_cancel_left]
  rw [ModularFormClass.qCoeff_add hUper hUhol hUbdd hcDper hcDhol hcDbdd,
    ModularFormClass.qCoeff_const_smul hDper hDhol hDbdd,
    ModularFormClass.qCoeff_const_smul hper hhol hbdd, hqU, hqD]

  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    have e1 : qCoeff ⇑(G d) (d * m * ℓ) = qCoeff ⇑g (m * ℓ) := by
      rw [hb, ite_eq_left ⟨m * ℓ, by ring⟩, mul_assoc, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    have e2 : qCoeff ⇑(G d) (d * m) = qCoeff ⇑g m := by
      rw [hb, ite_eq_left ⟨m, rfl⟩, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
    have key := hg.hecke_of_not_dvd hℓ hℓL m
    rw [mul_comm ℓ m] at key
    by_cases hℓm : ℓ ∣ m
    · have e3 : qCoeff ⇑(G d) (d * m / ℓ) = qCoeff ⇑g (m / ℓ) := by
        rw [Nat.mul_div_assoc d hℓm, hb, ite_eq_left ⟨m / ℓ, rfl⟩,
          Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]
      rw [ite_eq_left (hℓm.mul_left d), e1, e2, e3]
      rw [ite_eq_left hℓm] at key
      rw [← key]
      ring
    · have hℓdm : ¬ ℓ ∣ d * m := fun h => hℓm ((Nat.Coprime.dvd_mul_left hcop).mp h)
      rw [ite_eq_right hℓdm, e1, e2]
      rw [ite_eq_right hℓm] at key
      rw [← key]
      ring
  · have e1 : qCoeff ⇑(G d) (n * ℓ) = 0 := by
      rw [hb, ite_eq_right (fun h => hdn ((Nat.Coprime.dvd_mul_right hcop.symm).mp h))]
    have e2 : qCoeff ⇑(G d) n = 0 := by rw [hb, ite_eq_right hdn]
    have e3 : (if ℓ ∣ n then (ℓ : ℂ) ^ (k - 1) * qCoeff ⇑(G d) (n / ℓ) else 0) = 0 := by
      split_ifs with hℓn
      · rw [hb, ite_eq_right (fun h' => hdn (h'.trans (Nat.div_dvd_of_dvd hℓn))), mul_zero]
      · rfl
    rw [e1, e2, e3]
    ring

/-- The three cases of `U_q` on the degeneracy string, for `q ∣ M` prime: `q ∣ d`
gives `U_q G_d = G_{d/q}`; `¬ q ∣ d`, `q ∣ L` gives the eigenform action; and
`¬ q ∣ d`, `¬ q ∣ L` adds the `εL(q) q^{k-1}` correction at `G_{d q}`. Stated
verbatim from
`Theorems/Thm_CuspForm_IsEigenformWith_heckeU_degeneracy_of_dvd_level.lean`. -/
theorem heckeU_degeneracy_of_dvd_level
    (M : ℕ) [NeZero M] (k : ℤ) {L : ℕ} [NeZero L] (hLM : L ∣ M)
    {εL : DirichletCharacter ℂ L} {g : CuspForm (CongruenceSubgroup.Gamma1 L) k}
    (hg : CuspForm.IsEigenformWith εL g)
    (G : ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (hG : ∀ d : ℕ, d ∣ M / L → ∀ τ : UpperHalfPlane, G d τ = g (ModularForm.heckeDiagMatrix d • τ))
    {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) {d : ℕ} (hd : d ∣ M / L) :
    (q ∣ d → ModularForm.heckeU k q ⇑(G d) = ⇑(G (d / q))) ∧
    (¬ q ∣ d → q ∣ L → ModularForm.heckeU k q ⇑(G d) = ModularFormClass.qCoeff g q • ⇑(G d)) ∧
    (¬ q ∣ d → ¬ q ∣ L →
      ModularForm.heckeU k q ⇑(G d) =
        ModularFormClass.qCoeff g q • ⇑(G d) -
          (εL (q : ZMod L) * (q : ℂ) ^ (k - 1)) • ⇑(G (d * q))) := by
  classical
  have hq0 : q ≠ 0 := hq.ne_zero
  obtain ⟨e, he⟩ := hLM
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hMLe : M / L = e := by rw [he, Nat.mul_div_cancel_left _ hL0]
  have he0 : e ≠ 0 := by rintro rfl; exact NeZero.ne M (by rw [he, mul_zero])
  have hd0 : d ≠ 0 := fun h0 => he0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hMLe ▸ hd))

  have gper : Periodic (⇑g ∘ ofComplex) 1 := cusp_periodic g
  have ghol : MDiff (⇑g : ℍ → ℂ) := cusp_holo g
  have gbdd : IsBoundedAtImInfty (⇑g : ℍ → ℂ) := cusp_bdd g
  have hb : ∀ {d' : ℕ}, d' ∣ M / L → d' ≠ 0 → ∀ m : ℕ,
      qCoeff (⇑(G d')) m = if d' ∣ m then qCoeff (⇑g) (m / d') else 0 := by
    intro d' hd' hd'0 m
    rw [show (⇑(G d') : ℍ → ℂ) = fun τ => g (ModularForm.heckeDiagMatrix d' • τ) from
      funext (hG d' hd')]
    exact UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul gper ghol gbdd hd'0 m

  have hper : Periodic (⇑(G d) ∘ ofComplex) 1 := cusp_periodic (G d)
  have hhol : MDiff (⇑(G d) : ℍ → ℂ) := cusp_holo (G d)
  have hbdd : IsBoundedAtImInfty (⇑(G d) : ℍ → ℂ) := cusp_bdd (G d)
  have hUper := ModularForm.periodic_heckeU_comp_ofComplex hper k q
  have hUhol := ModularForm.mdifferentiable_heckeU hhol k q
  have hUbdd := ModularForm.isBoundedAtImInfty_heckeU hbdd k q
  have hqU : ∀ m : ℕ, qCoeff (ModularForm.heckeU k q ⇑(G d)) m = qCoeff ⇑(G d) (m * q) := fun m => by
    rw [UpperHalfPlane.qCoeff_heckeU hper hhol hbdd k hq0 m, ModularForm.coeffHeckeU_apply]
  refine ⟨fun hqd => ?_, fun hqd hqL => ?_, fun hqd hqL => ?_⟩
  ·
    obtain ⟨d', rfl⟩ := hqd
    have hd'0 : d' ≠ 0 := fun h => hd0 (by rw [h, mul_zero])
    have hdq : q * d' / q = d' := Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hq0)
    have hd' : d' ∣ M / L := (Dvd.intro_left q rfl).trans hd
    have h'per : Periodic (⇑(G (q * d' / q)) ∘ ofComplex) 1 := cusp_periodic (G (q * d' / q))
    have h'hol : MDiff (⇑(G (q * d' / q)) : ℍ → ℂ) := cusp_holo (G (q * d' / q))
    have h'bdd : IsBoundedAtImInfty (⇑(G (q * d' / q)) : ℍ → ℂ) := cusp_bdd (G (q * d' / q))
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd h'per h'hol h'bdd fun m => ?_
    rw [hqU m, hb hd hd0, hdq, hb hd' hd'0]
    by_cases hdm : d' ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      rw [ite_eq_left ⟨m', by ring⟩, ite_eq_left ⟨m', rfl⟩, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd'0),
        show d' * m' * q / (q * d') = m' from by
          rw [show d' * m' * q = (q * d') * m' from by ring, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)]]
    · rw [ite_eq_right hdm, ite_eq_right (fun h => hdm ?_)]

      obtain ⟨t, ht⟩ := h
      refine ⟨t, Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hq0) ?_⟩
      calc m * q = q * d' * t := ht
        _ = d' * t * q := by ring
  ·
    have hcop : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd (UpperHalfPlane.periodic_smul hper _)
      (hhol.const_smul _) (hbdd.const_smul_left _) fun m => ?_
    rw [hqU m, ModularFormClass.qCoeff_const_smul hper hhol hbdd, hb hd hd0, hb hd hd0]
    by_cases hdm : d ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      rw [ite_eq_left ⟨m' * q, by ring⟩, ite_eq_left ⟨m', rfl⟩, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0),
        mul_comm m' q]
      exact hg.hecke_of_dvd hq hqL m'
    · rw [ite_eq_right (fun h => hdm ((Nat.Coprime.dvd_mul_right hcop.symm).mp h)), ite_eq_right hdm, mul_zero]
  ·
    have hcop : Nat.Coprime q d := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqd
    have hqe : q ∣ e := by
      have : q ∣ L * e := he ▸ hqM
      exact ((Nat.Prime.dvd_mul hq).mp this).resolve_left hqL
    have hdq : d * q ∣ M / L := by
      rw [hMLe] at hd ⊢
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hd hqe
    have hdq0 : d * q ≠ 0 := mul_ne_zero hd0 hq0
    have h'per : Periodic (⇑(G (d * q)) ∘ ofComplex) 1 := cusp_periodic (G (d * q))
    have h'hol : MDiff (⇑(G (d * q)) : ℍ → ℂ) := cusp_holo (G (d * q))
    have h'bdd : IsBoundedAtImInfty (⇑(G (d * q)) : ℍ → ℂ) := cusp_bdd (G (d * q))
    set c : ℂ := εL (q : ZMod L) * (q : ℂ) ^ (k - 1) with hc
    refine UpperHalfPlane.eq_of_forall_qCoeff_eq hUper hUhol hUbdd
      (UpperHalfPlane.periodic_sub (UpperHalfPlane.periodic_smul hper _)
        (UpperHalfPlane.periodic_smul h'per _))
      ((hhol.const_smul _).sub (h'hol.const_smul _))
      ((hbdd.const_smul_left _).sub (h'bdd.const_smul_left _)) fun m => ?_
    rw [hqU m, ModularFormClass.qCoeff_sub (UpperHalfPlane.periodic_smul hper _)
        (hhol.const_smul _) (hbdd.const_smul_left _)
        (UpperHalfPlane.periodic_smul h'per _) (h'hol.const_smul _) (h'bdd.const_smul_left _),
      ModularFormClass.qCoeff_const_smul hper hhol hbdd,
      ModularFormClass.qCoeff_const_smul h'per h'hol h'bdd, hb hd hd0, hb hd hd0, hb hdq hdq0]
    by_cases hdm : d ∣ m
    · obtain ⟨m', rfl⟩ := hdm
      have key := hg.hecke_of_not_dvd hq hqL m'
      rw [ite_eq_left ⟨m' * q, by ring⟩, ite_eq_left ⟨m', rfl⟩, mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0), Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0),
        mul_comm m' q]
      by_cases hqm' : q ∣ m'
      · rw [ite_eq_left (mul_dvd_mul_left d hqm'),
          show d * m' / (d * q) = m' / q from Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hd0)]
        rw [ite_eq_left hqm'] at key
        rw [← key, hc]
        ring
      · rw [ite_eq_right (fun h => hqm' ?_)]
        · rw [ite_eq_right hqm'] at key
          rw [← key]
          ring
        · exact (Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hd0)).mp h
    · rw [ite_eq_right (fun h => hdm ((Nat.Coprime.dvd_mul_right hcop.symm).mp h)), ite_eq_right hdm,
        ite_eq_right (fun h => hdm ((dvd_mul_right d q).trans h))]
      ring

end IsEigenformWith

end CuspForm
