/-
  The Γ₀-rationality pair, shared engine written once.

  Targets (pin `aa2d8b3`, statements from the `Theorems/Thm_*.lean` wrappers):

  * `ModularCurve.exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd`
    (`P2M/Sol/S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean`);
  * `ModularCurve.exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion`
    (`P2M/Sol/S_ModularCurve_exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion.lean`).

  The two pin files share the weight-one prelude, which is already public in the
  port (`X1DiamondRational`, `UpperHalfPlaneAux`, `WLight`); it is imported, not
  re-proved.  Only the genuinely new declarations of the two files are written
  here, and the port-private helpers they need are re-derived locally as
  `private` declarations (`coe_zetaK`, `idxMap`, `discForm`, ...).

  This module sits in `ModularForms/WeightOne/` because both headlines consume
  the WLight `Thm_*` wrapper cluster.
-/
import FLTForHuman.ModularForms.WeightOne.Defs.GammaRational
import FLTForHuman.ModularForms.WeightOne.Gamma0Rationality
import FLTForHuman.ModularForms.WeightOne.Gamma1Basis
import FLTForHuman.ModularForms.WeightOne.MonicRel
import FLTForHuman.ModularForms.QExpansionCoeff
import FLTForHuman.ModularForms.DiscPow

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option autoImplicit false

noncomputable section

open Complex UpperHalfPlane ModularForm CongruenceSubgroup Function Filter
open scoped Real Manifold MatrixGroups ModularForm Topology
open WLight
open X1DiamondRational
open UpperHalfPlaneAux

local notation "Δ" => ModularForm.discriminant

namespace ModularCurve



/-! ## Local re-derivations of port-`private` helpers -/

private theorem coe_zetaK (N : ℕ) [NeZero N] : ((zetaK N : kN N) : ℂ) = zetaN N := rfl

private theorem kN_eq (N : ℕ) [NeZero N] :
    kN N = IntermediateField.adjoin ℚ {Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ))} :=
  WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisEven.kN_eq N

private theorem exists_ne_zero {v : ℍ → ℂ} (hv : v ≠ 0) : ∃ τ, v τ ≠ 0 := by
  by_contra h
  push Not at h
  exact hv (funext h)

private theorem disc_ne_zero (τ : ℍ) : Δ τ ≠ 0 := discriminant_ne_zero τ

private theorem periodic_disc (N : ℕ) : Periodic ((Δ : ℍ → ℂ) ∘ ofComplex) N :=
  periodic_ofComplex_natCast periodic_disc_one N

private theorem periodic_sub {g g' : ℍ → ℂ} {c : ℂ} (h : Periodic (g ∘ ofComplex) c)
    (h' : Periodic (g' ∘ ofComplex) c) : Periodic ((g - g') ∘ ofComplex) c := by
  intro z; have h1 := h z; have h2 := h' z
  simp only [comp_apply, Pi.sub_apply] at h1 h2 ⊢; rw [h1, h2]

private theorem bdd_pow {f : ℍ → ℂ} (hf : IsBoundedAtImInfty f) (n : ℕ) : IsBoundedAtImInfty (f ^ n) := by
  induction n with
  | zero => (have h__af := (Filter.const_boundedAtFilter atImInfty (1 : ℂ)); simp at h__af; exact h__af)
  | succ n ih => rw [pow_succ]; exact ih.mul hf

private def idxMap (N : ℕ) (α : SL(2, ℤ)) : Idx N → Idx N :=
  fun o => o.map fun v => ⟨vm N α v.1, vm_ne_zero N α v.2⟩

private theorem mdifferentiable_jf : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) jf :=
  WLightS9.S_ModularFunction_exists_mdifferentiable_sigmaTransport_of_frickeQuotient.FrickeTransport.mdifferentiable_jf
    jf jf_spec

private def E6sq : ModularForm 𝒮ℒ 12 := (E₆.pow 2).mcast (by norm_num)

private def discForm : ModularForm 𝒮ℒ 12 := (1728 : ℂ)⁻¹ • (E4cube - E6sq)

private theorem coe_discForm : (⇑discForm : ℍ → ℂ) = Δ := by
  funext z
  rw [discForm, smul_apply, sub_apply, discriminant_eq_E₄_cube_sub_E₆_sq]
  simp only [E4cube, E6sq, coe_mcast, coe_pow, Pi.pow_apply, smul_eq_mul]
  ring

namespace RatS

section Cyclo

variable (N : ℕ) [NeZero N]

theorem zetaN_pow : zetaN N ^ N = 1 := (isPrimitiveRoot_zetaN N).pow_eq_one

end Cyclo

section Width

variable (N : ℕ) [NeZero N]

theorem qExpansion_disc_pow_rat (r : ℕ) (n : ℕ) :
    ∃ q : ℚ, (qExpansion N ((Δ : ℍ → ℂ) ^ r)).coeff n = (q : ℂ) := by
  have hF : (⇑(discForm.pow r) : ℍ → ℂ) = Δ ^ r := by rw [coe_pow, coe_discForm]
  rw [← hF]
  refine WLightS11.S_CuspForm_exists_gamma1_qCoeff_eq_algEquiv_apply_of_even.GammaOneGaloisEven.qExpansion_widthN_rat_of_levelOne N _ (fun n => ?_) n
  have hone : ∀ m, ∃ r : ℚ, (qExpansion 1 (⇑discForm : ℍ → ℂ)).coeff m = (r : ℂ) := by
    intro m; rw [coe_discForm]; exact qExpansion_disc_rat_one m
  obtain ⟨p, hp⟩ := exists_map_of_rat hone
  refine rat_of_exists_map ⟨p ^ r, ?_⟩ n
  rw [ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL, map_pow, hp]

variable {N}

theorem analyticAt_disc_pow (r : ℕ) : AnalyticAt ℂ (cuspFunction N ((Δ : ℍ → ℂ) ^ r)) 0 :=
  analyticAt_cuspFunction_zero (natCast_pos N) (periodic_pow (periodic_disc N) r)
    (mdifferentiable_disc.pow r) (bdd_pow isBoundedAtImInfty_disc r)

end Width

section Group

variable (N : ℕ)

theorem redN_apply (γ : SL(2, ℤ)) (i j : Fin 2) : redN N γ i j = ((γ i j : ℤ) : ZMod N) := rfl

theorem redN_det (γ : SL(2, ℤ)) : (redN N γ).det = 1 := by
  rw [redN_eq, ← RingHom.map_det, Matrix.SpecialLinearGroup.det_coe, map_one]

variable {N}

theorem periodic_cw {G : ℍ → ℂ} (β : SL(2, ℤ)) (N : ℕ)
    (hinv : ∀ τ : ℍ, G ((β * ModularGroup.T ^ (N : ℤ) * β⁻¹) • τ) = G τ) :
    Periodic ((cw G β) ∘ ofComplex) N := by
  intro w
  by_cases hw : 0 < im w
  · have hwN : 0 < im (w + N) := by simpa using hw
    simp only [comp_apply, ofComplex_apply_of_im_pos hwN, ofComplex_apply_of_im_pos hw, cw_apply]
    have hpt : (⟨w + N, hwN⟩ : ℍ) = ModularGroup.T ^ (N : ℤ) • (⟨w, hw⟩ : ℍ) := by
      rw [modular_T_zpow_smul]
      apply UpperHalfPlane.ext
      simp [UpperHalfPlane.coe_vadd, add_comm]
    rw [hpt]
    have := hinv (β • (⟨w, hw⟩ : ℍ))
    rw [← this]
    congr 1
    simp only [mul_smul, inv_smul_smul]
  · have hw' : im w ≤ 0 := not_lt.mp hw
    have hwN : im (w + N) ≤ 0 := by simpa using hw'
    simp only [comp_apply]
    rw [ofComplex_apply_eq_of_im_nonpos hwN hw']

end Group

section Fricke

variable {N : ℕ} [NeZero N]

def ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : kN N →+* ℂ)
    (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ :=
  MvPolynomial.aeval (gen N t) (MvPolynomial.map ψ R)

abbrev ev₀ (R : MvPolynomial (Idx N) (kN N)) : ℍ → ℂ := ev id (algebraMap (kN N) ℂ) R

theorem ev_mul (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ψ : kN N →+* ℂ)
    (R S : MvPolynomial (Idx N) (kN N)) : ev t ψ (R * S) = ev t ψ R * ev t ψ S := by
  simp [ev]

theorem mdifferentiable_gen (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (o : Idx N) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (gen N t o) := by
  cases o with
  | none => exact mdifferentiable_jf
  | some v => exact mdifferentiable_fricke N (ht v.1 v.2)

theorem mdifferentiable_ev (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)) (ht : ∀ v, v ≠ 0 → t v ≠ 0)
    (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)) : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (ev t ψ R) := by
  rw [ev]
  induction (MvPolynomial.map ψ R) using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.aeval_C]; exact mdifferentiable_const
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p o hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact hp.mul (mdifferentiable_gen t ht o)

theorem cw_gen {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm N α (t v) = t (vm N α' v)) (o : Idx N) :
    cw (gen N t o) α = gen N t (idxMap N α' o) := by
  cases o with
  | none => funext τ; exact jf_smul α τ
  | some v => funext τ; rw [cw_apply, gen, gen, Option.elim, fricke_smul, h]; rfl

theorem cw_ev {t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N)} {α α' : SL(2, ℤ)}
    (h : ∀ v, vm N α (t v) = t (vm N α' v)) (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)) :
    cw (ev t ψ R) α = ev t ψ (MvPolynomial.rename (idxMap N α') R) := by
  rw [ev, ev, cw_aeval, MvPolynomial.map_rename, MvPolynomial.aeval_rename]
  have : (fun i => cw (gen N t i) α) = gen N t ∘ idxMap N α' := funext fun o => cw_gen h o
  rw [this]

theorem ev_mem_adjoin (R : MvPolynomial (Idx N) (kN N)) : ev₀ R ∈ Algebra.adjoin ℂ (genSet N) :=
  aeval_mem_adjoin _

theorem ev_prod_ne_zero {ι : Type*} (s : Finset ι) (Q : ι → MvPolynomial (Idx N) (kN N))
    (hQ : ∀ i ∈ s, ev₀ (Q i) ≠ 0) : ev₀ (∏ i ∈ s, Q i) ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [ev]
  | insert a s ha ih =>
      rw [Finset.prod_insert ha]
      intro h0
      have h0' : ev₀ (Q a) * ev₀ (N := N) (∏ i ∈ s, Q i) = 0 := by
        rw [← h0]; simp [ev, map_mul]
      rcases adjoin_isDomain (ev_mem_adjoin _) (ev_mem_adjoin _) h0' with h | h
      · exact hQ a (Finset.mem_insert_self a s) h
      · exact ih (fun i hi => hQ i (Finset.mem_insert_of_mem hi)) h

theorem exists_ev_of_mem_adjoin {x : ℍ → ℂ} (hx : x ∈ Algebra.adjoin (kN N) (genSet N)) :
    ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = x := by
  classical
  rw [Algebra.adjoin_eq_range] at hx
  obtain ⟨R₀, rfl⟩ := hx
  have hsec : ∀ y : genSet N, ∃ o : Idx N, gen N id o = y := by
    rintro ⟨y, hy⟩
    rcases hy with rfl | ⟨v, hv, rfl⟩
    · exact ⟨none, rfl⟩
    · exact ⟨some ⟨v, hv⟩, rfl⟩
  choose sec hsec using hsec
  refine ⟨MvPolynomial.rename sec R₀, ?_⟩
  simp only [ev₀, ev, MvPolynomial.aeval_map_algebraMap, MvPolynomial.aeval_rename]
  have : (gen N id ∘ sec) = Subtype.val := funext hsec
  rw [this]
  rfl

theorem descent {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : RatAt N (kN N) m G) :
    ∃ P Q : MvPolynomial (Idx N) (kN N), ev₀ Q ≠ 0 ∧ G * ev₀ Q = ev₀ P := by
  classical
  set S : Set (ℍ → ℂ) := {F | ∃ α : SL(2, ℤ), F = cw G α} with hS
  have hGS : G ∈ S := ⟨1, (cw_one G).symm⟩
  have hhol : ∀ F ∈ S, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F := by
    rintro F ⟨α, rfl⟩; exact mdifferentiable_cw hG α
  have hpb' : ∀ F ∈ S, ∃ m : ℕ, IsBoundedAtImInfty (F * ModularForm.discriminant ^ m) := by
    rintro F ⟨α, rfl⟩; exact ⟨m, hpb α⟩
  have hst : ∀ γ : SL(2, ℤ), ∀ F ∈ S, (F ∘ (γ • ·)) ∈ S := by
    rintro γ F ⟨α, rfl⟩
    exact ⟨α * γ, by rw [cw_mul]; rfl⟩
  have hinvS : ∀ F ∈ S, ∀ γ ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, F (γ • τ) = F τ := by
    rintro F ⟨α, rfl⟩ γ hγ τ
    simp only [cw_apply]
    have : α • γ • τ = (α * γ * α⁻¹) • α • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (conj_mem_Gamma N α hγ) _
  obtain ⟨a, b, ha, hb, hb0, hGb⟩ := WLight.exists_levelFraction_of_stable_family N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec S hhol hpb' hst hinvS hGS
  have hpbG : ∀ γ : SL(2, ℤ), ∃ m : ℕ, IsBoundedAtImInfty ((G ∘ (γ • ·)) * ModularForm.discriminant ^ m) :=
    fun γ => ⟨m, hpb γ⟩
  obtain ⟨d, p, hprel⟩ := WLight.exists_monicRel_j_of_mdifferentiable_levelFraction N tauPair tauPair_spec
    (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec ha hb hb0 hG hGb hpbG
  obtain ⟨n, lam, Gi, Pi, Qi, di, pi, hGsum, hGimd, hPQ, hpiK, hGirel⟩ :=
    WLight.frickeFunction_intBaseChange N tauPair tauPair_spec (WW N) (WW_spec N) (fricke N)
      (fricke_spec N) jf jf_spec hG ha hb hb0 hGb p hprel
  have hPi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = Pi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).1
  have hQi : ∀ i, ∃ R : MvPolynomial (Idx N) (kN N), ev₀ R = Qi i := fun i =>
    exists_ev_of_mem_adjoin (hPQ i).2.1
  choose Ph hPh using hPi
  choose Qh hQh using hQi
  have hrati : ∀ i, ∃ mi : ℕ, RatAt N (kN N) mi (Gi i) := by
    intro i
    obtain ⟨mi, h1, h2, h3⟩ := WLight.exists_qExpansion_coeff_mem_of_mdifferentiable_levelFraction N
      tauPair tauPair_spec (WW N) (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) rfl
      (hGimd i) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i))
      (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh i)) (coeff_map_mem _) (coeff_map_mem _)
      (by
        have := (hPQ i).2.2.1
        rwa [← hQh i] at this)
      (by
        have := (hPQ i).2.2.2
        rw [← hQh i, ← hPh i] at this
        exact this)
      ⟨di i, pi i, hpiK i, hGirel i⟩
    exact ⟨mi, (hGimd i), h1, h2, h3⟩
  choose mi hmi using hrati
  set M : ℕ := m + ∑ i, mi i with hM
  have hGM : RatAt N (kN N) M G := hrat.of_le (Nat.le_add_right _ _)
  have hGiM : ∀ i, RatAt N (kN N) M (Gi i) := fun i =>
    (hmi i).of_le (le_trans (Finset.single_le_sum (fun j _ => Nat.zero_le (mi j)) (Finset.mem_univ i))
      (Nat.le_add_left _ _))
  have hmem : G ∈ Submodule.span ℂ (Set.range Gi) := by
    rw [hGsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨κ, hκ⟩ := exists_rat_combination (kN N) hGiM hGM hmem
  refine ⟨∑ i, MvPolynomial.C (κ i) * Ph i * ∏ j ∈ Finset.univ.erase i, Qh j, ∏ i, Qh i, ?_, ?_⟩
  · exact ev_prod_ne_zero Finset.univ Qh fun i _ => by rw [hQh i]; exact (hPQ i).2.2.1
  · have hev_prod : ∀ (s : Finset (Fin n)), ev₀ (∏ j ∈ s, Qh j) = ∏ j ∈ s, Qi j := by
      intro s; simp only [ev₀, ev, map_prod]; exact Finset.prod_congr rfl fun j _ => hQh j
    rw [hκ, hev_prod, Finset.sum_mul]
    simp only [ev₀, ev, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.aeval_C, map_prod]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Ph i)) = Pi i := hPh i
    have h2 : ∀ j, (MvPolynomial.aeval (gen N id)) (MvPolynomial.map (algebraMap (kN N) ℂ) (Qh j)) = Qi j :=
      hQh
    simp only [h1, h2]
    rw [← Finset.mul_prod_erase Finset.univ Qi (Finset.mem_univ i), ← (hPQ i).2.2.2]
    simp only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [smul_one_smul, mul_assoc]
    rfl

end Fricke

section Transport

variable {N : ℕ} [NeZero N]


def TD (φ : kN N →+* ℂ) (m₀ : ℕ) (u u' : ℍ → ℂ) : Prop := ∀ M : ℕ, m₀ ≤ M →
  (Function.Periodic ((u * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n ∈ kN N) ∧
  (Function.Periodic ((u' * ModularForm.discriminant ^ M) ∘ UpperHalfPlane.ofComplex) N ∧
    IsBoundedAtImInfty (u' * ModularForm.discriminant ^ M) ∧
    ∀ n : ℕ, (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n ∈ kN N) ∧
  ∀ (n : ℕ) (z : kN N),
    (z : ℂ) = (UpperHalfPlane.qExpansion N (u * ModularForm.discriminant ^ M)).coeff n →
    (UpperHalfPlane.qExpansion N (u' * ModularForm.discriminant ^ M)).coeff n = φ z

theorem transportT {s : ℕ} (hs : s.Coprime N) (φ : kN N →+* ℂ)
    (hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ s)
    {u : ℍ → ℂ} (hu : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u) (P Q : MvPolynomial (Idx N) (kN N))
    (hQ0 : ev₀ Q ≠ 0) (huQ : u * ev₀ Q = ev₀ P) :
    ev (ds N s) φ Q ≠ 0 ∧ ∃ u' : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) u' ∧
      u' * ev (ds N s) φ Q = ev (ds N s) φ P ∧ ∃ m₀ : ℕ, TD φ m₀ u u' :=
  ModularFunction.exists_mdifferentiable_sigmaTransport_of_frickeQuotient N tauPair tauPair_spec (WW N)
    (WW_spec N) (fricke N) (fricke_spec N) jf jf_spec (kN N) (kN_eq N) s hs φ hφ u hu P Q hQ0 huQ

theorem eq_of_TD {φ : kN N →+* ℂ} {u F₁ F₂ : ℍ → ℂ} (h₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₁)
    (h₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) F₂)
    {m₁ m₂ : ℕ} (hT₁ : TD φ m₁ u F₁) (hT₂ : TD φ m₂ u F₂) : F₁ = F₂ := by
  set M : ℕ := m₁ + m₂ with hM
  obtain ⟨⟨-, -, hmem⟩, ⟨hper₁, hbd₁, -⟩, hco₁⟩ := hT₁ M (Nat.le_add_right _ _)
  obtain ⟨-, ⟨hper₂, hbd₂, -⟩, hco₂⟩ := hT₂ M (Nat.le_add_left _ _)
  have hexp : qExpansion N (F₁ * Δ ^ M) = qExpansion N (F₂ * Δ ^ M) := by
    ext n
    obtain ⟨z, hz⟩ : ∃ z : kN N, (z : ℂ) = (qExpansion N (u * Δ ^ M)).coeff n := ⟨⟨_, hmem n⟩, rfl⟩
    rw [hco₁ n z hz, hco₂ n z hz]
  have hmd₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₁ * Δ ^ M) := h₁.mul (mdifferentiable_disc.pow M)
  have hmd₂ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (F₂ * Δ ^ M) := h₂.mul (mdifferentiable_disc.pow M)
  have han₁ := analyticAt_cuspFunction_zero (natCast_pos N) hper₁ hmd₁ hbd₁
  have han₂ := analyticAt_cuspFunction_zero (natCast_pos N) hper₂ hmd₂ hbd₂
  have hzero : qExpansion N (F₁ * Δ ^ M - F₂ * Δ ^ M) = 0 := by
    rw [qExpansion_sub han₁ han₂, hexp, sub_self]
  rw [qExpansion_eq_zero_iff (natCast_pos N) (periodic_sub hper₁ hper₂) (hmd₁.sub hmd₂) (hbd₁.sub hbd₂)]
    at hzero
  funext τ
  have := congrFun hzero τ
  simp only [Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, Pi.zero_apply] at this
  have hΔ : Δ τ ^ M ≠ 0 := pow_ne_zero _ (disc_ne_zero τ)
  have : (F₁ τ - F₂ τ) * Δ τ ^ M = 0 := by rw [sub_mul]; exact this
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hΔ)

theorem TD_self {φ : kN N →+* ℂ} {m : ℕ} {u : ℍ → ℂ} (hu : RatAt N ⊥ m u) : TD φ m u u := by
  intro M hM
  have hM' : RatAt N ⊥ M u := hu.of_le hM
  have hK : ∀ n, (qExpansion N (u * Δ ^ M)).coeff n ∈ kN N := by
    intro n
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (hM'.mem n)
    rw [← hr]; exact ratCast_mem r
  refine ⟨⟨hM'.periodic, hM'.bdd, hK⟩, ⟨hM'.periodic, hM'.bdd, hK⟩, fun n z hz => ?_⟩
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (hM'.mem n)
  have hzr : z = (r : kN N) := by
    apply Subtype.ext
    rw [hz, ← hr]
    simp
  rw [hzr, map_ratCast, ← hr]
  rfl

theorem exists_of_mul_eq {K : Type*} [Field K] (ι φ : K →+* ℂ)
    {B A : PowerSeries K} (hB : B ≠ 0) {ξ₁ ξ₂ : PowerSeries ℂ}
    (h1 : ξ₁ * B.map ι = A.map ι) (h2 : ξ₂ * B.map φ = A.map φ) :
    ∃ X : PowerSeries K, X.map ι = ξ₁ ∧ X.map φ = ξ₂ := by
  classical
  set v : ℕ := B.order.toNat with hv
  set U : PowerSeries K := B.divXPowOrder with hU
  have hBU : PowerSeries.X ^ v * U = B := PowerSeries.X_pow_order_mul_divXPowOrder
  have hUunit : IsUnit U := by
    rw [PowerSeries.isUnit_iff_constantCoeff, hU, PowerSeries.constantCoeff_divXPowOrder]
    exact isUnit_iff_ne_zero.mpr (PowerSeries.coeff_order hB)
  obtain ⟨u, hu⟩ := hUunit
  have hAι : A.map ι = PowerSeries.X ^ v * (ξ₁ * U.map ι) := by
    rw [← h1, ← hBU]
    simp only [map_mul, map_pow, PowerSeries.map_X]
    ring
  have hAdvd : PowerSeries.X ^ v ∣ A := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro n hn
    have hcoef : PowerSeries.coeff n (A.map ι) = 0 := by
      rw [hAι, PowerSeries.coeff_X_pow_mul', ite_eq_right (not_le.mpr hn)]
    rw [PowerSeries.coeff_map] at hcoef
    exact ι.injective (by rw [hcoef, map_zero])
  obtain ⟨A', hA'⟩ := hAdvd
  have hXv : (PowerSeries.X : PowerSeries ℂ) ^ v ≠ 0 := pow_ne_zero _ PowerSeries.X_ne_zero
  have key : ∀ (ψ : K →+* ℂ) (ξ : PowerSeries ℂ), ξ * B.map ψ = A.map ψ → ξ * U.map ψ = A'.map ψ := by
    intro ψ ξ h
    rw [← hBU, hA'] at h
    simp only [map_mul, map_pow, PowerSeries.map_X] at h
    have : (PowerSeries.X : PowerSeries ℂ) ^ v * (ξ * U.map ψ) = PowerSeries.X ^ v * A'.map ψ := by
      rw [← h]; ring
    exact mul_left_cancel₀ hXv this
  refine ⟨A' * ↑u⁻¹, ?_, ?_⟩
  · have hk := key ι ξ₁ h1
    have hUι : U.map ι ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map ι).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUι
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]
  · have hk := key φ ξ₂ h2
    have hUφ : U.map φ ≠ 0 := by
      rw [← hu]; exact (Units.map (PowerSeries.map φ).toMonoidHom u).ne_zero
    apply mul_right_cancel₀ hUφ
    rw [hk, map_mul, mul_assoc, ← map_mul, ← hu, Units.inv_mul, map_one, mul_one]

theorem exists_discPowSeries (φ : kN N →+* ℂ) (r : ℕ) :
    ∃ δ : PowerSeries (kN N), δ.map (algebraMap (kN N) ℂ) = qExpansion N ((Δ : ℍ → ℂ) ^ r) ∧
      δ.map φ = qExpansion N ((Δ : ℍ → ℂ) ^ r) ∧ δ ≠ 0 := by
  choose q hq using qExpansion_disc_pow_rat N r
  refine ⟨PowerSeries.mk fun n => ((q n : ℚ) : kN N), ?_, ?_, ?_⟩
  · ext n; simp [hq n]
  · ext n
    rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, map_ratCast, hq n]
  · intro h0
    have h1 : qExpansion N ((Δ : ℍ → ℂ) ^ r) = 0 := by
      ext n
      have := congrArg (PowerSeries.coeff n) h0
      simp only [PowerSeries.coeff_mk, map_zero, Rat.cast_eq_zero] at this
      rw [hq n, this]; simp
    rw [qExpansion_eq_zero_iff (natCast_pos N) (periodic_pow (periodic_disc N) r)
      (mdifferentiable_disc.pow r) (bdd_pow isBoundedAtImInfty_disc r)] at h1
    exact disc_pow_ne_zero r UpperHalfPlane.I (by rw [h1]; rfl)

end Transport

section Matrices

variable {N : ℕ} [NeZero N]

theorem redN_S : redN N ModularGroup.S = !![0, -1; 1, 0] := by
  rw [redN, ModularGroup.coe_S]
  ext i j; fin_cases i <;> fin_cases j <;> simp

theorem T_pow_mem_Gamma (N : ℕ) : ModularGroup.T ^ (N : ℤ) ∈ CongruenceSubgroup.Gamma N := by
  rw [Gamma_mem, ModularGroup.coe_T_zpow]
  simp

theorem exists_diag_lift {c : ℕ} (hc : c.Coprime N) :
    ∃ γ₀ : SL(2, ℤ), redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)] := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime c hc with hu
  set t : ZMod N := ((u⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul u
  set M' : Matrix (Fin 2) (Fin 2) (ZMod N) := !![t, 0; 0, (c : ZMod N)] with hM'
  have hdet : M'.det = 1 := by rw [hM', Matrix.det_fin_two_of]; rw [htc]; ring
  obtain ⟨A', hA'⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod N ⟨M', hdet⟩
  refine ⟨A', ?_⟩
  have := congrArg (fun y : SL(2, ZMod N) => (y : Matrix (Fin 2) (Fin 2) (ZMod N))) hA'
  simpa [redN_eq] using this

theorem vm_S_diag {c : ℕ} (hc : c.Coprime N) {γ₀ : SL(2, ℤ)}
    (hγ₀ : redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)])
    (v : Fin 2 → ZMod N) :
    vm N (ModularGroup.S * γ₀) (ds N c v) = ds N c (vm N ModularGroup.S v) := by
  set t : ZMod N := (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul (ZMod.unitOfCoprime c hc)
  funext i
  simp only [vm, redN_mul, redN_S, hγ₀, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    rw [mul_comm ((c : ZMod N)), mul_assoc, mul_comm (c : ZMod N) t, htc, mul_one]
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, mul_comm]

theorem conj_mem_Gamma1 {c : ℕ} (hc : c.Coprime N) {γ₀ : SL(2, ℤ)}
    (hγ₀ : redN N γ₀ = !![(((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N), 0; 0, (c : ZMod N)])
    {γ : SL(2, ℤ)} (hb : ((γ 0 1 : ℤ) : ZMod N) = 0) (hd : ((γ 1 1 : ℤ) : ZMod N) = c) :
    ModularGroup.S * γ * γ₀⁻¹ * ModularGroup.S⁻¹ ∈ Gamma1 N := by
  set t : ZMod N := (((ZMod.unitOfCoprime c hc)⁻¹ : (ZMod N)ˣ) : ZMod N) with ht
  have htc : t * (c : ZMod N) = 1 := Units.inv_mul (ZMod.unitOfCoprime c hc)
  have hct : (c : ZMod N) * t = 1 := Units.mul_inv (ZMod.unitOfCoprime c hc)
  have hγ₀inv : redN N γ₀⁻¹ = !![(c : ZMod N), 0; 0, t] := by
    rw [redN, Matrix.SpecialLinearGroup.coe_inv]
    have : (γ₀ : Matrix (Fin 2) (Fin 2) ℤ).adjugate.map ((↑) : ℤ → ZMod N) = (redN N γ₀).adjugate := by
      rw [redN_eq]
      exact RingHom.map_adjugate (Int.castRingHom (ZMod N)) _
    rw [this, hγ₀, Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hSinv : redN N ModularGroup.S⁻¹ = !![0, 1; -1, 0] := by
    rw [redN, Matrix.SpecialLinearGroup.coe_inv, ModularGroup.coe_S, Matrix.adjugate_fin_two_of]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  set a : ZMod N := ((γ 0 0 : ℤ) : ZMod N) with ha
  set x : ZMod N := ((γ 1 0 : ℤ) : ZMod N) with hx
  have hγred : redN N γ = !![a, 0; x, (c : ZMod N)] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [redN_apply, ha, hx, hb, hd]
  have hac : a * (c : ZMod N) = 1 := by
    have := redN_det N γ
    rw [hγred, Matrix.det_fin_two_of] at this
    simpa using this
  have hred : redN N (ModularGroup.S * γ * γ₀⁻¹ * ModularGroup.S⁻¹) = !![1, -(x * (c : ZMod N)); 0, 1] := by
    rw [redN_mul, redN_mul, redN_mul, redN_S, hγred, hγ₀inv, hSinv]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hct, hac, mul_comm]
  rw [Gamma1_mem]
  refine ⟨?_, ?_, ?_⟩
  · have := congrFun (congrFun hred 0) 0
    rw [redN_apply] at this; simpa using this
  · have := congrFun (congrFun hred 1) 1
    rw [redN_apply] at this; simpa using this
  · have := congrFun (congrFun hred 1) 0
    rw [redN_apply] at this; simpa using this

end Matrices

section Bridge

variable {N : ℕ} [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem exists_zeta_lift (ι : ℚbar →+* ℂ) : ∃ ζ₁ : ℚbar, ζ₁ ^ N = 1 ∧ ι ζ₁ = zetaN N := by
  have hNpos : 0 < N := NeZero.pos N
  obtain ⟨ζ₀, hζ₀⟩ : ∃ ζ₀ : ℚbar, IsPrimitiveRoot ζ₀ N := by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic N ℚbar)
      (Polynomial.degree_cyclotomic_pos N ℚbar hNpos).ne'
    exact ⟨z, (Polynomial.isRoot_cyclotomic_iff).mp hz⟩
  have hι : IsPrimitiveRoot (ι ζ₀) N := hζ₀.map_of_injective ι.injective
  obtain ⟨i, -, hi⟩ := hι.eq_pow_of_pow_eq_one (zetaN_pow N)
  exact ⟨ζ₀ ^ i, by rw [← pow_mul, mul_comm, pow_mul, hζ₀.pow_eq_one, one_pow], by rw [map_pow, hi]⟩

theorem exists_bridge (ι : ℚbar →+* ℂ) :
    ∃ ψ : kN N →+* ℚbar, ∀ x : kN N, ι (ψ x) = x := by
  let ι' : ℚbar →ₐ[ℚ] ℂ := ι.toRatAlgHom
  obtain ⟨ζ₁, -, hζ₁⟩ := exists_zeta_lift (N := N) ι
  have hle : (kN N).toSubalgebra ≤ ι'.range := by
    have h1 : kN N ≤ ι'.fieldRange := by
      rw [kN, IntermediateField.adjoin_simple_le_iff]
      exact ⟨ζ₁, hζ₁⟩
    exact h1
  let e := AlgEquiv.ofInjectiveField ι'
  refine ⟨(e.symm.toAlgHom.comp (Subalgebra.inclusion hle)).toRingHom, fun x => ?_⟩
  have h2 : ι' (e.symm (Subalgebra.inclusion hle x)) = ((Subalgebra.inclusion hle x : ι'.range) : ℂ) := by
    have := AlgEquiv.ofInjective_apply ι' ι'.toRingHom.injective (e.symm (Subalgebra.inclusion hle x))
    rw [← this]
    simp [e, AlgEquiv.ofInjectiveField]
  exact h2

end Bridge

section Main

variable {N : ℕ} [NeZero N]

local notation "ℚbar" => AlgebraicClosure ℚ

theorem hbd_cw {m : ℕ} {G : ℍ → ℂ}
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m)) (α : SL(2, ℤ)) :
    IsBoundedAtImInfty (cw G α * Δ ^ m) := hbd α

theorem ratAt_bot {m : ℕ} {G : ℍ → ℂ} (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ)) :
    RatAt N ⊥ m G := by
  have hper1 : Periodic ((G * Δ ^ m) ∘ ofComplex) 1 := by
    have hG1 : Periodic ((cw G 1) ∘ ofComplex) (1 : ℕ) := by
      refine periodic_cw 1 1 fun τ => ?_
      simp only [one_mul, inv_one, mul_one, Nat.cast_one, zpow_one]
      exact hinv _ (by rw [Gamma1_mem]; simp [ModularGroup.coe_T]) τ
    rw [cw_one, Nat.cast_one] at hG1
    exact periodic_mul hG1 (periodic_pow periodic_disc_one m)
  have hbd1 : IsBoundedAtImInfty (G * Δ ^ m) := by
    have := hbd 1
    simpa using this
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ m) := hG.mul (mdifferentiable_disc.pow m)
  refine ⟨hG, periodic_ofComplex_natCast hper1 N, hbd1, fun n => ?_⟩
  rw [qExpansion_coeff_widthN N hmd hper1 hbd1 n, IntermediateField.mem_bot]
  split_ifs with h
  · obtain ⟨r, hr⟩ := hrat (n / N)
    exact ⟨r, hr.symm⟩
  · exact ⟨0, by simp⟩

theorem ratAt_kN_of_bot {m : ℕ} {G : ℍ → ℂ} (h : RatAt N ⊥ m G) : RatAt N (kN N) m G :=
  ⟨h.mdiff, h.periodic, h.bdd, fun n => by
    obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp (h.mem n)
    rw [← hr]; exact ratCast_mem r⟩

theorem main (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ : ℍ => G (α • τ)) * Δ ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ, (qExpansion 1 (G * Δ ^ m)).coeff n = (r : ℂ))
    (ι : ℚbar →+* ℂ) :
    ∃ a : ℕ → ℚbar,
      (∀ n : ℕ, (qExpansion N (cw G ModularGroup.S * Δ ^ m)).coeff n = ι (a n)) ∧
      ∀ (σ : ℚbar ≃ₐ[ℚ] ℚbar) (c : ℕ), (∀ ζ : ℚbar, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (qExpansion N (cw G (ModularGroup.S * γ) * Δ ^ m)).coeff n = ι (σ (a n)) := by
  classical
  have hRb : RatAt N ⊥ m G := ratAt_bot hG hinv hbd hrat
  have hR : RatAt N (kN N) m G := ratAt_kN_of_bot hRb
  have hinvΓ : ∀ g ∈ CongruenceSubgroup.Gamma N, ∀ τ : ℍ, G (g • τ) = G τ :=
    fun g hg τ => hinv g (Gamma_le_Gamma1 N hg) τ
  obtain ⟨P, Q, hQ0, hGQ⟩ := descent hG hinvΓ (hbd_cw hbd) hR

  set S := ModularGroup.S with hSdef
  set G₁ : ℍ → ℂ := cw G S with hG₁def
  set P₁ : MvPolynomial (Idx N) (kN N) := MvPolynomial.rename (idxMap N S) P with hP₁
  set Q₁ : MvPolynomial (Idx N) (kN N) := MvPolynomial.rename (idxMap N S) Q with hQ₁
  have hcwS : ∀ (ψ : kN N →+* ℂ) (R : MvPolynomial (Idx N) (kN N)),
      cw (ev id ψ R) S = ev id ψ (MvPolynomial.rename (idxMap N S) R) :=
    fun ψ R => cw_ev (t := id) (α := S) (α' := S) (fun v => rfl) ψ R
  have hcwS₀ : ∀ R : MvPolynomial (Idx N) (kN N), cw (ev₀ R) S = ev₀ (MvPolynomial.rename (idxMap N S) R) :=
    fun R => hcwS _ R
  have hG₁ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G₁ := mdifferentiable_cw hG S
  have hQ₁0 : ev₀ Q₁ ≠ 0 := by
    rw [hQ₁, ← hcwS₀]
    exact WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.cw_ne_zero hQ0 S
  have hG₁Q : G₁ * ev₀ Q₁ = ev₀ P₁ := by
    rw [hQ₁, hP₁, ← hcwS₀, ← hcwS₀, hG₁def, ← cw_mul_fun, hGQ]

  have hperSγ : ∀ γ : SL(2, ℤ), Periodic ((cw G (S * γ) * Δ ^ m) ∘ ofComplex) N := by
    intro γ
    refine periodic_mul (periodic_cw (S * γ) N fun τ => hinvΓ _ ?_ τ) (periodic_pow (periodic_disc N) m)
    exact conj_mem_Gamma N (S * γ) (T_pow_mem_Gamma N)

  have hφ₁ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      (algebraMap (kN N) ℂ) z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ 1 := by
    intro z hz; rw [pow_one]; exact hz
  obtain ⟨-, u₁, -, -, m₁, hTD₁⟩ := transportT (Nat.coprime_one_left N) (algebraMap (kN N) ℂ) hφ₁ hG₁ P₁ Q₁
    hQ₁0 hG₁Q
  obtain ⟨⟨hper₁, hbd₁, hmem₁⟩, -, -⟩ := hTD₁ (m₁ + m) (Nat.le_add_right _ _)
  have hR₁M : RatAt N (kN N) (m₁ + m) G₁ := ⟨hG₁, hper₁, hbd₁, hmem₁⟩
  obtain ⟨p₁, hp₁⟩ := hR₁M.exists_map

  have hper₁m : Periodic ((G₁ * Δ ^ m) ∘ ofComplex) N := by
    have := hperSγ 1; rwa [mul_one] at this
  have hbd₁m : IsBoundedAtImInfty (G₁ * Δ ^ m) := by
    have := hbd S; exact this
  have han₁m : AnalyticAt ℂ (cuspFunction N (G₁ * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hper₁m (hG₁.mul (mdifferentiable_disc.pow m)) hbd₁m
  obtain ⟨δ, hδι, -, hδ0⟩ := exists_discPowSeries (N := N) (algebraMap (kN N) ℂ) m₁
  have hsplit : ∀ (r : ℕ) (w : ℍ → ℂ), w * Δ ^ (r + m) = w * Δ ^ m * Δ ^ r := by
    intro r w; rw [add_comm, pow_add, mul_assoc]
  have hmul₁ : qExpansion N (G₁ * Δ ^ m) * δ.map (algebraMap (kN N) ℂ) = p₁.map (algebraMap (kN N) ℂ) := by
    rw [hδι, hp₁, hsplit m₁, qExpansion_mul han₁m (analyticAt_disc_pow m₁)]
  obtain ⟨A, hAι, -⟩ := exists_of_mul_eq (algebraMap (kN N) ℂ) (algebraMap (kN N) ℂ) hδ0 hmul₁ hmul₁

  obtain ⟨ψ, hψ⟩ := exists_bridge (N := N) ι
  refine ⟨fun n => ψ (PowerSeries.coeff n A), fun n => ?_, ?_⟩
  · rw [hψ, ← hAι, PowerSeries.coeff_map]; rfl

  intro σ c hσ γ hγb hγd n

  obtain ⟨ζ₁, hζ₁N, hζ₁⟩ := exists_zeta_lift (N := N) ι
  have hprim₁ : IsPrimitiveRoot ζ₁ N := by
    have h := isPrimitiveRoot_zetaN N
    rw [← hζ₁] at h
    exact h.of_map_of_injective ι.injective
  have hc : c.Coprime N := by
    have h1 : IsPrimitiveRoot (σ ζ₁) N := hprim₁.map_of_injective σ.injective
    rw [hσ ζ₁ hζ₁N] at h1
    exact (hprim₁.pow_iff_coprime (NeZero.pos N) c).mp h1
  set φ : kN N →+* ℂ := ι.comp ((σ : ℚbar ≃ₐ[ℚ] ℚbar).toRingEquiv.toRingHom.comp ψ) with hφdef
  have hφapp : ∀ z : kN N, φ z = ι (σ (ψ z)) := fun z => rfl
  have hψζ : ψ (zetaK N) = ζ₁ := ι.injective (by rw [hψ, coe_zetaK, hζ₁])
  have hφ : ∀ z : kN N, (z : ℂ) = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) →
      φ z = Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (N : ℂ)) ^ c := by
    intro z hz
    have hz' : z = zetaK N := Subtype.ext hz
    rw [hφapp, hz', hψζ, hσ ζ₁ hζ₁N, map_pow, hζ₁]; rfl

  obtain ⟨-, G', hG', hG'Q, m₂, hTD₂⟩ := transportT hc φ hφ hG P Q hQ0 hGQ
  have hGG' : G' = G := eq_of_TD hG' hG hTD₂ (TD_self (φ := φ) hRb)
  rw [hGG'] at hG'Q

  obtain ⟨γ₀, hγ₀⟩ := exists_diag_lift (N := N) hc
  have hcw₀ : ∀ R : MvPolynomial (Idx N) (kN N),
      cw (ev (ds N c) φ R) (S * γ₀) = ev (ds N c) φ (MvPolynomial.rename (idxMap N S) R) :=
    fun R => cw_ev (t := ds N c) (α := S * γ₀) (α' := S) (vm_S_diag hc hγ₀) φ R
  have hSγ₀Q : cw G (S * γ₀) * ev (ds N c) φ Q₁ = ev (ds N c) φ P₁ := by
    rw [hQ₁, hP₁, ← hcw₀, ← hcw₀, ← cw_mul_fun, hG'Q]

  obtain ⟨hQ₁c0, G₁', hG₁', hG₁'Q, m₃, hTD₃⟩ := transportT hc φ hφ hG₁ P₁ Q₁ hQ₁0 hG₁Q
  have hident : G₁' = cw G (S * γ₀) := by
    have hdiff : ∀ τ : ℍ, (G₁' - cw G (S * γ₀)) τ * ev (ds N c) φ Q₁ τ = 0 := by
      intro τ
      have e1 := congrFun hG₁'Q τ
      have e2 := congrFun hSγ₀Q τ
      simp only [Pi.mul_apply, Pi.sub_apply] at e1 e2 ⊢
      rw [sub_mul, e1, e2, sub_self]
    obtain ⟨τ₀, hτ₀⟩ := exists_ne_zero hQ₁c0
    have := eq_zero_of_mul_eq_zero (hG₁'.sub (mdifferentiable_cw hG _))
      (mdifferentiable_ev (ds N c) (fun v hv => ds_ne_zero N hc hv) φ Q₁) hdiff hτ₀
    exact sub_eq_zero.1 this

  have hγγ₀ : cw G (S * γ) = cw G (S * γ₀) := by
    funext τ
    simp only [cw_apply]
    have hmem := conj_mem_Gamma1 hc hγ₀ hγb hγd
    have : (S * γ) • τ = (S * γ * γ₀⁻¹ * S⁻¹) • (S * γ₀) • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this, hinv _ hmem]

  set M : ℕ := m₃ + m with hM
  obtain ⟨⟨hperM, hbdM, hmemM⟩, ⟨hperM', hbdM', -⟩, hcoM⟩ := hTD₃ M (Nat.le_add_right _ _)
  have hR₁' : RatAt N (kN N) M G₁ := ⟨hG₁, hperM, hbdM, hmemM⟩
  obtain ⟨p, hpι⟩ := hR₁'.exists_map
  have hpφ : p.map φ = qExpansion N (G₁' * Δ ^ M) := by
    ext k
    rw [PowerSeries.coeff_map]
    symm
    apply hcoM
    rw [← hpι, PowerSeries.coeff_map]
    rfl
  obtain ⟨δ', hδ'ι, hδ'φ, hδ'0⟩ := exists_discPowSeries (N := N) φ m₃

  have hAδ : A * δ' = p := by
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [map_mul, hAι, hδ'ι, hpι, hM, hsplit m₃, qExpansion_mul han₁m (analyticAt_disc_pow m₃)]

  have hperγ : Periodic ((cw G (S * γ) * Δ ^ m) ∘ ofComplex) N := hperSγ γ
  have hbdγ : IsBoundedAtImInfty (cw G (S * γ) * Δ ^ m) := hbd (S * γ)
  have hanγ : AnalyticAt ℂ (cuspFunction N (cw G (S * γ) * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos N) hperγ ((mdifferentiable_cw hG _).mul
      (mdifferentiable_disc.pow m)) hbdγ
  have hkey : qExpansion N (cw G (S * γ) * Δ ^ m) * qExpansion N ((Δ : ℍ → ℂ) ^ m₃) =
      A.map φ * qExpansion N ((Δ : ℍ → ℂ) ^ m₃) := by
    rw [← qExpansion_mul hanγ (analyticAt_disc_pow m₃), ← hsplit m₃, hγγ₀, ← hident, ← hM, ← hpφ, ← hAδ,
      map_mul, hδ'φ]
  have hΔM0 : qExpansion N ((Δ : ℍ → ℂ) ^ m₃) ≠ 0 := by
    rw [← hδ'ι]
    intro h0
    apply hδ'0
    apply PowerSeries.map_injective (algebraMap (kN N) ℂ) Subtype.val_injective
    rw [h0, map_zero]
  have hfin := mul_right_cancel₀ hΔM0 hkey
  rw [hfin, PowerSeries.coeff_map, hφapp]

end Main

end RatS

namespace RatA

section Width

variable (N : ℕ) [NeZero N]

theorem qParam_eq_pow_mul (h : ℕ) [NeZero h] (τ : ℍ) :
    Periodic.qParam h τ = Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ N := by
  simp only [Periodic.qParam]
  rw [← Complex.exp_nat_mul]
  congr 1
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  have hh : (h : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne h)
  push_cast
  field_simp

theorem qExpansion_coeff_width_mul (h : ℕ) [NeZero h] {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) h) (hbd : IsBoundedAtImInfty g) (n : ℕ) :
    (qExpansion ((N * h : ℕ) : ℝ) g).coeff n = if (N : ℕ) ∣ n then (qExpansion h g).coeff (n / N) else 0 := by
  classical
  have : NeZero (N * h) := NeZero.mul
  have hhpos : (0 : ℝ) < h := Nat.cast_pos.mpr (NeZero.pos h)
  have hperN : Periodic (g ∘ ofComplex) ((N * h : ℕ) : ℝ) := by
    have := hper.nat_mul N
    push_cast at this ⊢
    exact this
  set c : ℕ → ℂ := fun n => if (N : ℕ) ∣ n then (qExpansion h g).coeff (n / N) else 0 with hc
  have hNpos : 0 < N := NeZero.pos N
  have hsum : ∀ τ : ℍ, HasSum (fun m => c m • Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ m) (g τ) := by
    intro τ
    have h1 := hasSum_qExpansion hhpos (by simpa using hper) hg hbd τ
    have hinj : Function.Injective fun m : ℕ => N * m := mul_right_injective₀ hNpos.ne'
    have hsupp : ∀ x ∉ Set.range (fun m : ℕ => N * m),
        (fun m => c m • Periodic.qParam ((N * h : ℕ) : ℝ) τ ^ m) x = 0 := by
      intro x hx
      have : ¬ (N : ℕ) ∣ x := by
        rintro ⟨y, rfl⟩; exact hx ⟨y, rfl⟩
      simp [hc, this]
    refine (hinj.hasSum_iff hsupp).1 ?_
    convert h1 using 1
    funext m
    simp only [comp_apply, hc, dvd_mul_right, ↓reduceIte, Nat.mul_div_cancel_left _ hNpos]
    rw [qParam_eq_pow_mul N h τ, ← pow_mul]
  rw [← qExpansion_coeff_unique' (natCast_pos (N * h)) (analyticAt_cuspFunction_zero (natCast_pos (N * h))
    (by simpa using hperN) hg hbd) hsum n]

theorem qExpansion_widthDiv_rat (h : ℕ) [NeZero h] {g : ℍ → ℂ} (hg : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g)
    (hper : Periodic (g ∘ ofComplex) h) (hbd : IsBoundedAtImInfty g)
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion ((N * h : ℕ) : ℝ) g).coeff n = (r : ℂ)) (n : ℕ) :
    ∃ r : ℚ, (qExpansion h g).coeff n = (r : ℂ) := by
  obtain ⟨r, hr⟩ := hrat (N * n)
  rw [qExpansion_coeff_width_mul N h hg hper hbd, ite_eq_left (dvd_mul_right N n),
    Nat.mul_div_cancel_left _ (NeZero.pos N)] at hr
  exact ⟨r, hr⟩

end Width

section Group

variable (N : ℕ)

theorem T_pow_mem_Gamma1 (t : ℤ) : ModularGroup.T ^ t ∈ Gamma1 N := by
  rw [Gamma1_mem, ModularGroup.coe_T_zpow]
  simp

end Group

section GroupAL

variable {M ℓ : ℕ}

abbrev ΓSL (M ℓ : ℕ) : Subgroup SL(2, ℤ) := Gamma1 M ⊓ Gamma0 (M * ℓ)

theorem T_zpow_mem_ΓSL (t : ℤ) : ModularGroup.T ^ t ∈ ΓSL M ℓ := by
  refine Subgroup.mem_inf.mpr ⟨T_pow_mem_Gamma1 M t, ?_⟩
  rw [Gamma0_mem, ModularGroup.coe_T_zpow]
  simp

theorem Gamma1_le_of_dvd' {M' : ℕ} (h : M ∣ M') : Gamma1 M' ≤ Gamma1 M := by
  intro A hA
  rw [Gamma1_mem] at hA ⊢
  obtain ⟨h1, h2, h3⟩ := hA
  refine ⟨?_, ?_, ?_⟩
  · have := congrArg (ZMod.castHom h (ZMod M)) h1; rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h2; rwa [map_intCast, map_one] at this
  · have := congrArg (ZMod.castHom h (ZMod M)) h3; rwa [map_intCast, map_zero] at this

theorem Gamma_le_ΓSL : CongruenceSubgroup.Gamma (M * ℓ) ≤ ΓSL M ℓ :=
  le_inf ((Gamma_le_Gamma1 (M * ℓ)).trans (Gamma1_le_of_dvd' (dvd_mul_right M ℓ)))
    ((Gamma_le_Gamma1 (M * ℓ)).trans (Gamma1_in_Gamma0 _))

theorem conj_T_pow_mem {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) : γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹ ∈ ΓSL M ℓ := by
  have hc : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨r, hr⟩ := hc
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hinv : (γ⁻¹ : SL(2, ℤ)) = ⟨!![γ 1 1, -(γ 0 1); -(γ 1 0), γ 0 0], by
      rw [Matrix.det_fin_two_of]; have := γ.det_coe; rw [Matrix.det_fin_two] at this
      linear_combination this⟩ := Matrix.SpecialLinearGroup.SL2_inv_expl γ
  have h10 : (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) 1 0 = -(γ 1 0 * γ 1 0 * ℓ) := by
    rw [hinv]
    erw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ModularGroup.coe_T_zpow]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact X1DiamondRational.conj_mem_Gamma1 M hγ (T_pow_mem_Gamma1 M (ℓ : ℤ))
  · rw [Gamma0_mem, h10, hr, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact ⟨-(r * M * r), by push_cast; ring⟩

theorem exists_twist_conj' [NeZero (M * ℓ)] {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1)
    {s : ℕ} (hs : s.Coprime (M * ℓ)) :
    ∃ γ' : SL(2, ℤ), (∃ g ∈ ΓSL M ℓ, γ' = g * γ) ∧
      ∀ v : Fin 2 → ZMod (M * ℓ), vm (M * ℓ) γ' (ds (M * ℓ) s v) = ds (M * ℓ) s (vm (M * ℓ) γ v) := by
  obtain ⟨c₁, hc₁⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp hγ)
  obtain ⟨d₁, hd₁⟩ := hγℓ
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.det_coe; rwa [Matrix.det_fin_two] at this
  have hMℓ : IsCoprime (M : ℤ) (ℓ : ℤ) :=
    ⟨-(γ 0 1 * c₁), γ 0 0 * d₁, by rw [hc₁, hd₁] at hdet; linear_combination hdet⟩
  obtain ⟨u₁, v₁, huv₁⟩ := hMℓ
  obtain ⟨t, v₂, huv₂⟩ := Nat.isCoprime_iff_coprime.mpr hs
  set w : ℤ := 1 + M * u₁ * (t - 1) with hw
  have hwM : IsCoprime w (M : ℤ) := ⟨1, -(u₁ * (t - 1)), by rw [hw]; ring⟩
  have hswℓ : (s : ℤ) * w + (v₂ * M + s * v₁ * (t - 1)) * ℓ = 1 := by
    rw [hw]; push_cast at huv₂; linear_combination (s : ℤ) * (t - 1) * huv₁ + huv₂
  have hwℓ : IsCoprime w (ℓ : ℤ) := ⟨s, v₂ * M + s * v₁ * (t - 1), hswℓ⟩
  have hwN : IsCoprime w ((M * ℓ : ℕ) : ℤ) := by push_cast; exact hwM.mul_right hwℓ
  obtain ⟨p, q, hpq⟩ := hwN
  let δ₀ : SL(2, ℤ) := ⟨!![p, -q; ((M * ℓ : ℕ) : ℤ), w], by
    rw [Matrix.det_fin_two_of]; linear_combination hpq⟩
  have hδ₀00 : δ₀ 0 0 = p := rfl; have hδ₀01 : δ₀ 0 1 = -q := rfl
  have hδ₀10 : δ₀ 1 0 = ((M * ℓ : ℕ) : ℤ) := rfl; have hδ₀11 : δ₀ 1 1 = w := rfl
  have hδ₀mem : δ₀ ∈ ΓSL M ℓ := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Gamma1_mem, hδ₀00, hδ₀11, hδ₀10]
      have hwM1 : ((w : ℤ) : ZMod M) = 1 := by rw [hw]; push_cast; simp
      have hp1 : ((p : ℤ) : ZMod M) = 1 := by
        have := congrArg (Int.cast : ℤ → ZMod M) hpq
        push_cast at this
        rw [hwM1, ZMod.natCast_self, zero_mul, mul_one, mul_zero, add_zero] at this
        exact this
      refine ⟨hp1, hwM1, ?_⟩
      push_cast; simp
    · rw [Gamma0_mem, hδ₀10]; push_cast; exact_mod_cast ZMod.natCast_self (M * ℓ)
  have hN0 : ((M * ℓ : ℕ) : ZMod (M * ℓ)) = 0 := ZMod.natCast_self _
  have hN0' : (M : ZMod (M * ℓ)) * (ℓ : ZMod (M * ℓ)) = 0 := by exact_mod_cast hN0
  have hpw : (p : ZMod (M * ℓ)) * (w : ZMod (M * ℓ)) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod (M * ℓ)) hpq
    push_cast at this
    linear_combination this - (q : ZMod (M * ℓ)) * hN0'
  obtain ⟨a, ha⟩ : ∃ a : ZMod (M * ℓ), a = ((γ 0 0 : ℤ) : ZMod (M * ℓ)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ZMod (M * ℓ), b = ((γ 0 1 : ℤ) : ZMod (M * ℓ)) := ⟨_, rfl⟩
  obtain ⟨c, hcz⟩ : ∃ c : ZMod (M * ℓ), c = ((γ 1 0 : ℤ) : ZMod (M * ℓ)) := ⟨_, rfl⟩
  obtain ⟨d, hdz⟩ : ∃ d : ZMod (M * ℓ), d = ((γ 1 1 : ℤ) : ZMod (M * ℓ)) := ⟨_, rfl⟩
  have hdetz : a * d - b * c = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod (M * ℓ)) hdet
    push_cast at this
    rw [ha, hb, hcz, hdz]; exact this
  have h3 : (s : ZMod (M * ℓ)) * (w : ZMod (M * ℓ)) * c = c := by
    have hint : ((s : ℤ) * w - 1) * γ 1 0 = ((M * ℓ : ℕ) : ℤ) * (-(v₂ * M + s * v₁ * (t - 1)) * c₁) := by
      rw [hc₁]; push_cast; linear_combination (M : ℤ) * c₁ * hswℓ
    have := congrArg (Int.cast : ℤ → ZMod (M * ℓ)) hint
    push_cast at this
    rw [hcz]
    linear_combination this + (-((v₂ : ZMod (M * ℓ)) * M + (s : ZMod (M * ℓ)) * v₁ * ((t : ZMod (M * ℓ)) - 1)) * c₁) * hN0'
  have h4 : ((w : ZMod (M * ℓ)) - 1) * d = 0 := by
    have hint : ((w : ℤ) - 1) * γ 1 1 = ((M * ℓ : ℕ) : ℤ) * (u₁ * (t - 1) * d₁) := by
      rw [hd₁, hw]; push_cast; ring
    have := congrArg (Int.cast : ℤ → ZMod (M * ℓ)) hint
    push_cast at this
    rw [hdz]
    linear_combination this + ((u₁ : ZMod (M * ℓ)) * ((t : ZMod (M * ℓ)) - 1) * d₁) * hN0'
  have hAD : ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c) * ((w : ZMod (M * ℓ)) * d) -
      ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d) * ((w : ZMod (M * ℓ)) * c) = 1 := by
    linear_combination ((p : ZMod (M * ℓ)) * (w : ZMod (M * ℓ))) * hdetz + hpw
  have haD : a * ((w : ZMod (M * ℓ)) * d) - (s : ZMod (M * ℓ)) * b * ((w : ZMod (M * ℓ)) * c) = 1 := by
    linear_combination a * h4 - b * h3 + hdetz
  obtain ⟨lam, hlam⟩ : ∃ lam : ℤ, (lam : ZMod (M * ℓ)) =
      ((s : ZMod (M * ℓ)) * b - ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d)) *
          ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c) -
        (a - ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c)) *
          ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d) :=
    ⟨((((s : ZMod (M * ℓ)) * b - ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d)) *
          ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c) -
        (a - ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c)) *
          ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d)).val : ℤ), by
      push_cast; exact ZMod.natCast_zmod_val _⟩
  have e1 : ((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c) +
      (lam : ZMod (M * ℓ)) * ((w : ZMod (M * ℓ)) * c) = a := by
    linear_combination (-((p : ZMod (M * ℓ)) * a - (q : ZMod (M * ℓ)) * c)) * haD + a * hAD +
      ((w : ZMod (M * ℓ)) * c) * hlam
  have e2 : ((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d) +
      (lam : ZMod (M * ℓ)) * ((w : ZMod (M * ℓ)) * d) = (s : ZMod (M * ℓ)) * b := by
    linear_combination (-((p : ZMod (M * ℓ)) * b - (q : ZMod (M * ℓ)) * d)) * haD +
      ((s : ZMod (M * ℓ)) * b) * hAD + ((w : ZMod (M * ℓ)) * d) * hlam
  refine ⟨ModularGroup.T ^ lam * δ₀ * γ,
    ⟨ModularGroup.T ^ lam * δ₀, mul_mem (T_zpow_mem_ΓSL lam) hδ₀mem, rfl⟩, ?_⟩
  intro v
  have hT : redN (M * ℓ) (ModularGroup.T ^ lam) = !![1, (lam : ZMod (M * ℓ)); 0, 1] := by
    rw [redN, ModularGroup.coe_T_zpow]
    ext i j; fin_cases i <;> fin_cases j <;> simp
  have hδ : redN (M * ℓ) δ₀ = !![(p : ZMod (M * ℓ)), -(q : ZMod (M * ℓ)); 0, (w : ZMod (M * ℓ))] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [redN, hδ₀00]
    · simp [redN, hδ₀01]
    · change (((δ₀ 1 0 : ℤ)) : ZMod (M * ℓ)) = 0
      rw [hδ₀10]; push_cast; exact hN0'
    · simp [redN, hδ₀11]
  have hγm : redN (M * ℓ) γ = !![a, b; c, d] := by
    rw [ha, hb, hcz, hdz]
    ext i j; fin_cases i <;> fin_cases j <;> rfl
  funext i
  simp only [vm, redN_mul, hT, hδ, hγm, ds]
  fin_cases i
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    linear_combination (v 0) * e1 + (v 1) * h3
  · simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    linear_combination (v 0) * e2 + ((s : ZMod (M * ℓ)) * v 1) * h4

end GroupAL

section Invariance

variable {N : ℕ}

theorem periodic_of_T_zpow_invariant {G : ℍ → ℂ} (n : ℕ)
    (h : ∀ τ : ℍ, G ((ModularGroup.T ^ (n : ℤ)) • τ) = G τ) : Periodic (G ∘ ofComplex) n := by
  intro w
  by_cases hw : 0 < im w
  · have this : 0 < im (w + n) := by simp [hw]
    simp only [comp_apply, ofComplex_apply_of_im_pos this, ofComplex_apply_of_im_pos hw]
    have := h ⟨w, hw⟩
    rw [modular_T_zpow_smul] at this
    convert this using 2
    ext
    simp [add_comm, UpperHalfPlane.coe_vadd]
  · push Not at hw
    have : im (w + n) ≤ 0 := by simpa using hw
    simp [ofComplex_apply_of_im_nonpos this, ofComplex_apply_of_im_nonpos hw]

end Invariance

section Main

variable {N : ℕ} [NeZero N]

private theorem evφ_algebraMap (t : (Fin 2 → ZMod N) → (Fin 2 → ZMod N))
    (R : MvPolynomial (Idx N) (kN N)) :
    evφ N (algebraMap (kN N) ℂ) t R = ev N t R := rfl

theorem exists_series_fixed {M ℓ : ℕ} [NeZero M] [NeZero ℓ] [NeZero (M * ℓ)] {m : ℕ} {G : ℍ → ℂ}
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ ΓSL M ℓ, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion ((M * ℓ : ℕ) : ℝ) (G * Δ ^ m)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (σ : (kN (M * ℓ)) ≃ₐ[ℚ] (kN (M * ℓ))) :
    ∃ X : PowerSeries (kN (M * ℓ)), X.map (algebraMap (kN (M * ℓ)) ℂ) =
        qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m) ∧
      X.map (phiOf (M * ℓ) σ) = qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m) := by
  classical
  have hperG : Periodic (G ∘ ofComplex) 1 :=
    periodic_of_T_invariant fun τ => hinv _ (by simpa using T_zpow_mem_ΓSL (M := M) (ℓ := ℓ) 1) τ
  have hperγℓ : Periodic (cw G γ ∘ ofComplex) ℓ := by
    refine periodic_of_T_zpow_invariant ℓ fun τ => ?_
    simp only [cw_apply]
    have : γ • ModularGroup.T ^ (ℓ : ℤ) • τ = (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) • γ • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (conj_T_pow_mem hγ) _
  have hperγ : Periodic (cw G γ ∘ ofComplex) ((M * ℓ : ℕ) : ℝ) := by
    have := hperγℓ.nat_mul M
    push_cast at this ⊢
    exact this
  have hratG : RatAt (M * ℓ) (kN (M * ℓ)) m G :=
    ⟨hG, periodic_mul (periodic_ofComplex_natCast hperG (M * ℓ))
      (periodic_pow (periodic_ofComplex_natCast periodic_disc_one (M * ℓ)) m),
      by simpa [cw_one] using hpb 1,
      fun n => by obtain ⟨r, hr⟩ := hrat n; rw [hr]; exact ratCast_mem r⟩
  obtain ⟨P, Q, hb0, hGb⟩ := descent hG (fun g hg => hinv g (Gamma_le_ΓSL hg)) hpb hratG
  obtain ⟨s, hs, hσ⟩ := exists_pow_of_aut (M * ℓ) σ
  have hT0 : Tσ σ (G * evφ (M * ℓ) (algebraMap (kN (M * ℓ)) ℂ) id Q - evφ (M * ℓ) (algebraMap (kN (M * ℓ)) ℂ) id P)
      (G * evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ id) Q - evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ id) P) := by
    have hfam : ∀ o : Option (Idx (M * ℓ)), Tσ σ ((fun o : Option (Idx (M * ℓ)) => o.elim G (gen (M * ℓ) id)) o)
        ((fun o : Option (Idx (M * ℓ)) => o.elim G (gen (M * ℓ) (ds (M * ℓ) s ∘ id))) o) := by
      intro o
      cases o with
      | none =>
          exact tRel_self_of_rat hG hratG.periodic hratG.bdd hrat
      | some o => exact tσ_gen σ hs hσ id (fun v hv => hv) o
    have := tσ_aeval σ hfam (MvPolynomial.X none * MvPolynomial.rename some Q - MvPolynomial.rename some P)
    rwa [WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.aeval_relPoly, WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.aeval_relPoly] at this
  have hzero : G * evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s) Q - evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s) P = 0 := by
    have h0 : G * evφ (M * ℓ) (algebraMap (kN (M * ℓ)) ℂ) id Q - evφ (M * ℓ) (algebraMap (kN (M * ℓ)) ℂ) id P = 0 := by
      rw [evφ_algebraMap, evφ_algebraMap, hGb, sub_self]
    exact (tσ_zero_iff σ hT0).mp h0
  obtain ⟨γ', ⟨g₁, hg₁, rfl⟩, hvm⟩ := exists_twist_conj' hγ hγℓ hs
  have hvm' : (vm (M * ℓ) (g₁ * γ) ∘ ds (M * ℓ) s) = (ds (M * ℓ) s ∘ vm (M * ℓ) γ) := funext hvm
  have hcwG : cw G (g₁ * γ) = cw G γ := by
    rw [cw_mul]; congr 1; funext τ; exact hinv g₁ hg₁ τ
  have hE1 : cw G γ * ev (M * ℓ) (vm (M * ℓ) γ) Q = ev (M * ℓ) (vm (M * ℓ) γ) P := by
    have := congrArg (fun F => cw F γ) hGb
    simp only [cw_mul_fun, cw_ev] at this
    exact this
  have hE2 : cw G γ * evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ vm (M * ℓ) γ) Q =
      evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ vm (M * ℓ) γ) P := by
    have h := congrArg (fun F => cw F (g₁ * γ)) (sub_eq_zero.mp hzero)
    simp only [cw_mul_fun, cw_evφ, hcwG] at h
    rw [hvm'] at h
    exact h
  have hTQ : Tσ σ (ev (M * ℓ) (vm (M * ℓ) γ) Q) (evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ vm (M * ℓ) γ) Q) :=
    tσ_ev σ hs hσ (vm (M * ℓ) γ) (fun v hv => vm_ne_zero (M * ℓ) γ hv) Q
  have hTP : Tσ σ (ev (M * ℓ) (vm (M * ℓ) γ) P) (evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ vm (M * ℓ) γ) P) :=
    tσ_ev σ hs hσ (vm (M * ℓ) γ) (fun v hv => vm_ne_zero (M * ℓ) γ hv) P
  obtain ⟨mQ, hQr, hQr', hQlift⟩ := WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.tσ_lift σ hTQ
  obtain ⟨mP, hPr, hPr', hPlift⟩ := WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.tσ_lift σ hTP
  set MQ : ℕ := mQ + mP with hMQ
  obtain ⟨pB, hpB, hpB'⟩ := hQlift MQ (Nat.le_add_right _ _)
  obtain ⟨pA, hpA, hpA'⟩ := hPlift (m + MQ) (by omega)
  have hmdγ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G γ * Δ ^ m) := (mdifferentiable_cw hG γ).mul (mdifferentiable_disc.pow m)
  have hperγm : Periodic ((cw G γ * Δ ^ m) ∘ ofComplex) (M * ℓ : ℕ) := by
    have h1 : Periodic ((cw G γ * Δ ^ m) ∘ ofComplex) ((M * ℓ : ℕ) : ℝ) :=
      periodic_mul hperγ (by
        have := periodic_pow (periodic_ofComplex_natCast periodic_disc_one (M * ℓ)) m
        push_cast at this ⊢; exact this)
    simpa using h1
  have hanγ : AnalyticAt ℂ (cuspFunction (M * ℓ : ℕ) (cw G γ * Δ ^ m)) 0 :=
    analyticAt_cuspFunction_zero (natCast_pos (M * ℓ)) hperγm hmdγ (hpb γ)
  have hQR : RatAt (M * ℓ) (kN (M * ℓ)) MQ (ev (M * ℓ) (vm (M * ℓ) γ) Q) := hQr.of_le (Nat.le_add_right _ _)
  have hQR' : RatAt (M * ℓ) (kN (M * ℓ)) MQ (evφ (M * ℓ) (phiOf (M * ℓ) σ) (ds (M * ℓ) s ∘ vm (M * ℓ) γ) Q) :=
    hQr'.of_le (Nat.le_add_right _ _)
  have h1 : qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m) * pB.map (algebraMap (kN (M * ℓ)) ℂ) =
      pA.map (algebraMap (kN (M * ℓ)) ℂ) := by
    rw [hpB, hpA, ← hE1, ← qExpansion_mul hanγ hQR.analyticAt]
    congr 1; rw [pow_add]; ring
  have h2 : qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m) * pB.map (phiOf (M * ℓ) σ) = pA.map (phiOf (M * ℓ) σ) := by
    rw [hpB', hpA', ← hE2, ← qExpansion_mul hanγ hQR'.analyticAt]
    congr 1; rw [pow_add]; ring
  have hpB0 : pB ≠ 0 := by
    intro h0
    have hne := hQR.qExpansion_ne_zero (by
      have : ev (M * ℓ) (vm (M * ℓ) γ) Q = cw (ev (M * ℓ) id Q) γ := by rw [cw_ev]; rfl
      rw [this]
      exact WLightS10.S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0.X1DiamondRational.cw_ne_zero hb0 γ)
    rw [← hpB, h0, map_zero] at hne
    exact hne rfl
  exact exists_of_mul_eq (algebraMap (kN (M * ℓ)) ℂ) (phiOf (M * ℓ) σ) hpB0 h1 h2

theorem rat_cw_of_mem_Gamma0_of_dvd {M ℓ : ℕ} [NeZero M] [NeZero ℓ] [NeZero (M * ℓ)] {m : ℕ} {G : ℍ → ℂ}
    (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ ΓSL M ℓ, ∀ τ : ℍ, G (g • τ) = G τ)
    (hpb : ∀ α : SL(2, ℤ), IsBoundedAtImInfty (cw G α * Δ ^ m))
    (hrat : ∀ n, ∃ r : ℚ, (qExpansion ((M * ℓ : ℕ) : ℝ) (G * Δ ^ m)).coeff n = (r : ℂ))
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (n : ℕ) :
    ∃ r : ℚ, (qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m)).coeff n = (r : ℂ) := by
  obtain ⟨X₀, hX₀, -⟩ := exists_series_fixed hG hinv hpb hrat hγ hγℓ AlgEquiv.refl
  set x : kN (M * ℓ) := PowerSeries.coeff n X₀ with hx
  have hxξ : (x : ℂ) = (qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m)).coeff n := by
    rw [← hX₀, PowerSeries.coeff_map]; rfl
  obtain ⟨r, hr⟩ := exists_rat_of_fixed (M * ℓ) x (fun σ => by
    obtain ⟨X, hX, hX'⟩ := exists_series_fixed hG hinv hpb hrat hγ hγℓ σ
    have hy : ((PowerSeries.coeff n X : kN (M * ℓ)) : ℂ) = (qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m)).coeff n := by
      rw [← hX, PowerSeries.coeff_map]; rfl
    have hyx : PowerSeries.coeff n X = x := Subtype.ext (hy.trans hxξ.symm)
    have hφ : phiOf (M * ℓ) σ (PowerSeries.coeff n X) = (qExpansion ((M * ℓ : ℕ) : ℝ) (cw G γ * Δ ^ m)).coeff n := by
      rw [← hX', PowerSeries.coeff_map]
    rw [hyx, phiOf_apply, ← hxξ] at hφ
    exact Subtype.ext hφ)
  exact ⟨r, by rw [← hxξ, hr]⟩

theorem cardK (M ℓ : ℕ) [NeZero M] [NeZero ℓ] (m : ℕ) (G : ℍ → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ), ∀ τ : ℍ, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), IsBoundedAtImInfty ((fun τ => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (n : ℕ) :
    ∃ r : ℚ, (qExpansion ℓ ((fun τ => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) := by
  have : NeZero (M * ℓ) := NeZero.mul
  have hperG : Periodic (G ∘ ofComplex) 1 :=
    periodic_of_T_invariant fun τ => hinv _ (by simpa using T_zpow_mem_ΓSL (M := M) (ℓ := ℓ) 1) τ
  have hperγℓ : Periodic (cw G γ ∘ ofComplex) ℓ := by
    refine periodic_of_T_zpow_invariant ℓ fun τ => ?_
    simp only [cw_apply]
    have : γ • ModularGroup.T ^ (ℓ : ℤ) • τ = (γ * ModularGroup.T ^ (ℓ : ℤ) * γ⁻¹) • γ • τ := by
      simp only [mul_smul, inv_smul_smul]
    rw [this]
    exact hinv _ (conj_T_pow_mem hγ) _
  have hper1 : Periodic ((G * Δ ^ m) ∘ ofComplex) 1 :=
    periodic_mul hperG (periodic_pow periodic_disc_one m)
  have hperℓ : Periodic ((cw G γ * Δ ^ m) ∘ ofComplex) ℓ :=
    periodic_mul hperγℓ (periodic_pow (periodic_ofComplex_natCast periodic_disc_one ℓ) m)
  have hmd : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (G * Δ ^ m) := hG.mul (mdifferentiable_disc.pow m)
  have hmdγ : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (cw G γ * Δ ^ m) :=
    (mdifferentiable_cw hG γ).mul (mdifferentiable_disc.pow m)
  have hbd1 : IsBoundedAtImInfty (G * Δ ^ m) := by simpa [cw_one] using hbd 1
  have hratN : ∀ n, ∃ r : ℚ, (qExpansion ((M * ℓ : ℕ) : ℝ) (G * Δ ^ m)).coeff n = (r : ℂ) :=
    qExpansion_widthN_rat (M * ℓ) hmd hper1 hbd1 hrat
  have key := fun n => rat_cw_of_mem_Gamma0_of_dvd (M := M) (ℓ := ℓ) hG hinv hbd hratN hγ hγℓ n
  exact qExpansion_widthDiv_rat M ℓ hmdγ hperℓ (hbd γ) key n

end Main

end RatA

open scoped MatrixGroups Manifold in
theorem exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd (M ℓ : ℕ) [NeZero M]
    [NeZero ℓ] (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 M ⊓ CongruenceSubgroup.Gamma0 (M * ℓ),
      ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M) (hγℓ : (ℓ : ℤ) ∣ γ 1 1) (n : ℕ) :
    ∃ r : ℚ, (UpperHalfPlane.qExpansion ℓ
      ((fun τ : UpperHalfPlane => G (γ • τ)) * ModularForm.discriminant ^ m)).coeff n = (r : ℂ) :=
  RatA.cardK M ℓ m G hG hinv hbd hrat γ hγ hγℓ n

open scoped MatrixGroups Manifold in
theorem exists_qExpansion_S_smul_eq_and_conj_eq_of_ratCast_qExpansion (N : ℕ) [NeZero N]
    (m : ℕ) (G : UpperHalfPlane → ℂ) (hG : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) G)
    (hinv : ∀ g ∈ CongruenceSubgroup.Gamma1 N, ∀ τ : UpperHalfPlane, G (g • τ) = G τ)
    (hbd : ∀ α : SL(2, ℤ), UpperHalfPlane.IsBoundedAtImInfty
      ((fun τ : UpperHalfPlane => G (α • τ)) * ModularForm.discriminant ^ m))
    (hrat : ∀ n : ℕ, ∃ r : ℚ,
      (UpperHalfPlane.qExpansion 1 (G * ModularForm.discriminant ^ m)).coeff n = (r : ℂ))
    (ι : AlgebraicClosure ℚ →+* ℂ) :
    ∃ a : ℕ → AlgebraicClosure ℚ,
      (∀ n : ℕ, (UpperHalfPlane.qExpansion N
        ((fun τ : UpperHalfPlane => G (ModularGroup.S • τ)) * ModularForm.discriminant ^ m)).coeff n =
          ι (a n)) ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ),
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ c) →
        ∀ γ : SL(2, ℤ), ((γ 0 1 : ℤ) : ZMod N) = 0 → ((γ 1 1 : ℤ) : ZMod N) = c →
          ∀ n : ℕ, (UpperHalfPlane.qExpansion N
            ((fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) *
              ModularForm.discriminant ^ m)).coeff n = ι (σ (a n)) := by
  obtain ⟨a, ha, hb⟩ := RatS.main m G hG hinv hbd hrat ι
  refine ⟨a, ha, fun σ c hσ γ hγb hγd n => ?_⟩
  have := hb σ c hσ γ hγb hγd n
  have hfun : (fun τ : UpperHalfPlane => G (ModularGroup.S • γ • τ)) = cw G (ModularGroup.S * γ) := by
    funext τ; simp [cw, mul_smul]
  rw [hfun]
  exact this

end ModularCurve

end
