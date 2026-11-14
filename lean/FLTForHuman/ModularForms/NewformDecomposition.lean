/-
  The newform decomposition of a nebentypus cusp form: Atkin--Lehner lowering along `ε`, the span of
  the primitive forms, and multiplicity one at the level of a primitive form.

  * `CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero`: a
    `Γ₁(N)`-cusp form with nebentypus `ε` whose coefficients vanish at every index prime to `K` is a sum
    of degeneracy lifts `g (d • ·)` of forms at the levels `Γ₁(N / p)`, with the level-changed
    nebentypus — the AF63 level-lowering row pushed through the nebentypus (the eigenbasis supplies the
    decomposition into `ε`-eigenspaces, `HasNebentypus.sum_filter_eq_of_sum_eq` the character
    separation).
  * `CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus`: such a form is a finite `ℂ`-linear
    combination `∑ c i • (g i ∣ V_{d i})` of primitive (new) forms `g i` at the levels `M i ∣ N`, with
    `d i * M i ∣ N` — the newform decomposition.
  * `CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen`: multiplicity one — two forms of the same
    level and weight that are Hecke eigenforms with the same eigenvalues are proportional.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean`
  (201 lines), `S_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus.lean` (733 lines) and
  `S_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen.lean` (499 lines), with the statements
  from the wrappers of the same names.  The pin label namespaces are word names and are kept:
  `AtkinLehnerNebentypus`, `ALLiDecomposition` and `MultOnePrimitive`.

  Assumes from earlier modules: `ModularForms/NebentypusEigenbasis.lean` and
  `ModularForms/NebentypusDirectSum.lean` (the two AF64 rows the first two headlines consume),
  `ModularForms/AtkinLehnerLowering.lean` (the level-lowering row and its prelude),
  `ModularForms/NebentypusSeparation.lean`, `ModularForms/HeckeDiagDegeneracy.lean` (the degeneracy
  lift), `ModularForms/HeckeULevel.lean` (`exists_gamma1_coe_eq_heckeU_of_dvd`) and
  `ModularForms/{HeckePrelude,HeckeQCoeff}.lean`.

  spec-pin: Theorems/Thm_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero.lean
  spec-pin: Theorems/Thm_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus.lean
  spec-pin: Theorems/Thm_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen.lean
  spec-pin: P2M/Sol/S_CuspForm_eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen.lean
-/
import FLTForHuman.ModularForms.NebentypusEigenbasis
import FLTForHuman.ModularForms.NebentypusDirectSum
import FLTForHuman.ModularForms.NebentypusSeparation
import FLTForHuman.ModularForms.HeckeDiagDegeneracy
import FLTForHuman.ModularForms.HeckeULevel
import FLTForHuman.ModularForms.HeckePrelude
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.ModularForms.QExpansion
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section


open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups


namespace AtkinLehnerNebentypus

variable {L : ℕ} {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

theorem qCoeff_add (f g : CuspForm Γ₁(L) k) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods L) f g]
  simp

theorem qCoeff_smul (c : ℂ) (f : CuspForm Γ₁(L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods L) c f]
  simp

def qCoeffLin (n : ℕ) : CuspForm Γ₁(L) k →ₗ[ℂ] ℂ where
  toFun f := qCoeff (⇑f) n
  map_add' f g := qCoeff_add f g n
  map_smul' c f := qCoeff_smul c f n

theorem qCoeffLin_apply (n : ℕ) (f : CuspForm Γ₁(L) k) : qCoeffLin n f = qCoeff (⇑f) n := rfl

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (f : ι → CuspForm Γ₁(L) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, f i)) n = ∑ i ∈ s, qCoeff (⇑(f i)) n := by
  rw [← qCoeffLin_apply, map_sum]; rfl

theorem qCoeff_zero' (n : ℕ) : qCoeff (⇑(0 : CuspForm Γ₁(L) k)) n = 0 := by
  rw [← qCoeffLin_apply, map_zero]

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ L) :
    CuspForm.HasNebentypus ε (0 : CuspForm Γ₁(L) k) := by
  intro γ _ τ
  simp

theorem hasNebentypus_add {ε : DirichletCharacter ℂ L} {f g : CuspForm Γ₁(L) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  simp only [add_apply]
  rw [hf γ hγ τ, hg γ hγ τ]
  ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ L} {f : CuspForm Γ₁(L) k}
    (hf : CuspForm.HasNebentypus ε f) (c : ℂ) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  simp only [smul_apply, smul_eq_mul]
  rw [hf γ hγ τ]
  ring

theorem hasNebentypus_sum {ε : DirichletCharacter ℂ L} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm Γ₁(L) k) (hf : ∀ i ∈ s, CuspForm.HasNebentypus ε (f i)) :
    CuspForm.HasNebentypus ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNebentypus_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasNebentypus_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem main (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (ε : DirichletCharacter ℂ N)
    (f : CuspForm Γ₁(N) k) (hε : CuspForm.HasNebentypus ε f)
    (hf : ∀ n : ℕ, Nat.Coprime n K → qCoeff (⇑f) n = 0) :
    ∃ g : (p : ℕ) → CuspForm Γ₁(N / p) k,
      (∀ (p : ℕ) (hp : p ∈ N.primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ∀ n : ℕ, qCoeff (⇑f) n =
        ∑ p ∈ N.primeFactors, if p ∣ n then qCoeff (⇑(g p)) (n / p) else 0 := by
  classical

  obtain ⟨h, hh⟩ :=
    CuspForm.exists_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero N k K hK f hf

  set pf := N.primeFactors with hpf
  have hdvd : ∀ P : pf, (P : ℕ) ∣ N := fun P => Nat.dvd_of_mem_primeFactors P.2
  have hdiv : ∀ P : pf, N / (P : ℕ) ∣ N := fun P => Nat.div_dvd_of_dvd (hdvd P)
  have hne : ∀ P : pf, NeZero (N / (P : ℕ)) := fun P =>
    ⟨(Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) (hdvd P))
      (Nat.prime_of_mem_primeFactors P.2).pos).ne'⟩
  have hmul : ∀ P : pf, N / (P : ℕ) * (P : ℕ) ∣ N := fun P => by
    rw [Nat.div_mul_cancel (hdvd P)]

  have hSS : ∀ P : pf, ∃ (n : ℕ) (b : Module.Basis (Fin n) ℂ (CuspForm Γ₁(N / (P : ℕ)) k))
      (εb : Fin n → DirichletCharacter ℂ (N / (P : ℕ))), ∀ i, CuspForm.HasNebentypus (εb i) (b i) := by
    intro P
    have := hne P
    obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen (N / (P : ℕ)) k
    choose εb hεb _ using hb
    exact ⟨n, b, εb, hεb⟩
  choose n b εb hεb using hSS

  have hDEG : ∀ (P : pf) (i : Fin (n P)), ∃ G : CuspForm Γ₁(N) k,
      (∀ m : ℕ, qCoeff (⇑G) m = if (P : ℕ) ∣ m then qCoeff (⇑(b P i)) (m / P) else 0) ∧
      CuspForm.HasNebentypus (DirichletCharacter.changeLevel (hdiv P) (εb P i)) G := by
    intro P i
    obtain ⟨G, -, hGq, hGε⟩ :=
      CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) (hmul P) (b P i)
    exact ⟨G, hGq, hGε _ (hεb P i)⟩
  choose G hGq hGε using hDEG

  let ι := Σ P : pf, Fin (n P)
  let c : ι → ℂ := fun x => (b x.1).repr (h x.1) x.2
  let χ : ι → DirichletCharacter ℂ N := fun x =>
    DirichletCharacter.changeLevel (hdiv x.1) (εb x.1 x.2)

  have hsum : ∑ x : ι, c x • G x.1 x.2 = f := by
    refine ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods N) fun m => ?_
    rw [qCoeff_sum, hh m, Fintype.sum_sigma, ← Finset.sum_coe_sort pf]
    refine Finset.sum_congr rfl fun P _ => ?_
    simp only [qCoeff_smul, hGq, c]
    split_ifs with hPm
    ·
      have := congrArg (fun F : CuspForm Γ₁(N / (P : ℕ)) k => qCoeff (⇑F) (m / P))
        ((b P).sum_repr (h P))
      simp only [qCoeff_sum, qCoeff_smul] at this
      exact this
    · simp

  have hfilt := CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq Finset.univ χ
    (fun x : ι => c x • G x.1 x.2) (fun x _ => hasNebentypus_smul (hGε x.1 x.2) _) hε hsum

  let g : (p : ℕ) → CuspForm Γ₁(N / p) k := fun p =>
    if hp : p ∈ pf then
      ∑ i ∈ Finset.univ.filter (fun i => χ ⟨⟨p, hp⟩, i⟩ = ε), c ⟨⟨p, hp⟩, i⟩ • b ⟨p, hp⟩ i
    else 0
  have hg : ∀ P : pf, g P = ∑ i ∈ Finset.univ.filter (fun i => χ ⟨P, i⟩ = ε), c ⟨P, i⟩ • b P i := by
    intro P
    simp only [g, dite_eq_left P.2]
  refine ⟨g, fun p hp => ?_, fun m => ?_⟩
  ·
    set P : pf := ⟨p, hp⟩
    by_cases hex : ∃ εp : DirichletCharacter ℂ (N / p),
        DirichletCharacter.changeLevel (hdiv P) εp = ε
    · obtain ⟨εp, hεp⟩ := hex
      refine Or.inr ⟨εp, hεp, ?_⟩
      rw [show g p = g P from rfl, hg P]
      refine hasNebentypus_sum _ _ fun i hi => hasNebentypus_smul ?_ _
      obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi

      have hinj := DirichletCharacter.changeLevel_injective (R := ℂ) (hdiv P) (hi.trans hεp.symm)
      rw [← hinj]
      exact hεb P i
    · refine Or.inl ?_
      rw [show g p = g P from rfl, hg P]
      refine Finset.sum_eq_zero fun i hi => ?_
      obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi
      exact absurd ⟨εb P i, hi⟩ hex
  ·
    rw [← hfilt, qCoeff_sum, Finset.sum_filter, Fintype.sum_sigma, ← Finset.sum_coe_sort pf]
    refine Finset.sum_congr rfl fun P _ => ?_
    rw [hg P, qCoeff_sum, Finset.sum_filter]
    split_ifs with hPm
    · refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with hχ
      · rw [qCoeff_smul, qCoeff_smul, hGq, ite_eq_left hPm]
      · rfl
    · refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with hχ
      · rw [qCoeff_smul, hGq, ite_eq_right hPm, mul_zero]
      · rfl

end AtkinLehnerNebentypus

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
    (N : ℕ) [NeZero N] (k : ℤ) (K : ℕ) (hK : K ≠ 0) (ε : DirichletCharacter ℂ N)
    (f : CuspForm (Gamma1 N) k) (hε : CuspForm.HasNebentypus ε f)
    (hf : ∀ n : ℕ, Nat.Coprime n K → ModularFormClass.qCoeff f n = 0) :
    ∃ g : (p : ℕ) → CuspForm (Gamma1 (N / p)) k,
      (∀ (p : ℕ) (hp : p ∈ N.primeFactors), g p = 0 ∨
        ∃ εp : DirichletCharacter ℂ (N / p),
          DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
          CuspForm.HasNebentypus εp (g p)) ∧
      ∀ n : ℕ, ModularFormClass.qCoeff f n =
        ∑ p ∈ N.primeFactors, if p ∣ n then ModularFormClass.qCoeff (g p) (n / p) else 0 :=
  AtkinLehnerNebentypus.main N k K hK ε f hε hf

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups


namespace ALLiDecomposition

def heckeSeq (p : ℕ) (c : ℂ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun s := fun n => s (p * n) + c * (if p ∣ n then s (n / p) else 0)
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem heckeSeq_apply (p : ℕ) (c : ℂ) (s : ℕ → ℂ) (n : ℕ) :
    heckeSeq p c s n = s (p * n) + c * (if p ∣ n then s (n / p) else 0) := rfl

theorem heckeSeq_eq_smul_iff {p : ℕ} {c lam : ℂ} {s : ℕ → ℂ} :
    heckeSeq p c s = lam • s ↔
      ∀ n : ℕ, s (p * n) + c * (if p ∣ n then s (n / p) else 0) = lam * s n := by
  constructor
  · intro h n
    have := congrFun h n
    rwa [heckeSeq_apply, Pi.smul_apply, smul_eq_mul] at this
  · intro h
    funext n
    rw [heckeSeq_apply, Pi.smul_apply, smul_eq_mul]
    exact h n

def stretchLin (d : ℕ) : (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) where
  toFun b := fun n => if d ∣ n then b (n / d) else 0
  map_add' s t := by
    funext n
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' a s := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

theorem stretchLin_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchLin d b n = if d ∣ n then b (n / d) else 0 := rfl

theorem stretchLin_one (b : ℕ → ℂ) : stretchLin 1 b = b := by
  funext n
  simp [stretchLin_apply]

theorem stretchLin_stretchLin {d d' : ℕ} (hd : d ≠ 0) (hd' : d' ≠ 0) (b : ℕ → ℂ) :
    stretchLin d (stretchLin d' b) = stretchLin (d' * d) b := by
  funext n
  simp only [stretchLin_apply]
  have hpos : 0 < d := Nat.pos_of_ne_zero hd
  have hpos' : 0 < d' := Nat.pos_of_ne_zero hd'
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
    rw [ite_eq_left (dvd_mul_right d m), Nat.mul_div_cancel_left _ hpos]
    by_cases hd'm : d' ∣ m
    · obtain ⟨r, rfl⟩ := hd'm
      have h1 : d' * d ∣ d * (d' * r) := ⟨r, by ring⟩
      rw [ite_eq_left (dvd_mul_right d' r), ite_eq_left h1, Nat.mul_div_cancel_left _ hpos',
        show d * (d' * r) = d' * d * r by ring, Nat.mul_div_cancel_left _ (by positivity)]
    · have h1 : ¬ d' * d ∣ d * m := by
        rintro ⟨r, hr⟩
        apply hd'm
        refine ⟨r, ?_⟩
        have : d * m = d * (d' * r) := by rw [hr]; ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      rw [ite_eq_right hd'm, ite_eq_right h1]
  · have h1 : ¬ d' * d ∣ n := fun h => hdn (dvd_trans (dvd_mul_left d d') h)
    rw [ite_eq_right hdn, ite_eq_right h1]

theorem heckeSeq_stretchLin {c : ℂ} {p d : ℕ} (hp0 : p ≠ 0) (hd : d ≠ 0)
    (hpd : Nat.Coprime p d) {b : ℕ → ℂ} {lam : ℂ} (hb : heckeSeq p c b = lam • b) :
    heckeSeq p c (stretchLin d b) = lam • stretchLin d b := by
  rw [heckeSeq_eq_smul_iff] at hb ⊢
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have hppos : 0 < p := Nat.pos_of_ne_zero hp0
  intro n
  simp only [stretchLin_apply]
  by_cases hdn : d ∣ n
  · obtain ⟨m, rfl⟩ := hdn
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
      rwa [ite_eq_left (dvd_mul_right p r), Nat.mul_div_cancel_left _ hppos] at this
    · have h4 : ¬ p ∣ d * m := fun h => hpm (hpd.dvd_of_dvd_mul_left h)
      rw [ite_eq_right h4]
      have := hb m
      rwa [ite_eq_right hpm] at this
  · have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
    rw [ite_eq_right h1, ite_eq_right hdn, mul_zero]
    have hmid : (if p ∣ n then (if d ∣ n / p then b (n / p / d) else 0) else 0) = 0 := by
      split_ifs with hpn hdnp
      · exact absurd (dvd_trans hdnp (Nat.div_dvd_of_dvd hpn)) hdn
      · rfl
      · rfl
    rw [hmid, mul_zero, add_zero]

def decSeq (ℓ : ℕ) (s : ℕ → ℂ) : ℕ → ℂ := fun n => s (ℓ * n)

theorem heckeSeq_decSeq {c : ℂ} {p ℓ : ℕ} (hp0 : p ≠ 0) (hpl : Nat.Coprime p ℓ) (s : ℕ → ℂ) :
    heckeSeq p c (decSeq ℓ s) = decSeq ℓ (heckeSeq p c s) := by
  funext n
  simp only [heckeSeq_apply, decSeq]
  rw [show p * (ℓ * n) = ℓ * (p * n) by ring]
  congr 2
  by_cases hpn : p ∣ n
  · obtain ⟨m, rfl⟩ := hpn
    have hppos : 0 < p := Nat.pos_of_ne_zero hp0
    have h1 : p ∣ ℓ * (p * m) := ⟨ℓ * m, by ring⟩
    rw [ite_eq_left (dvd_mul_right p m), ite_eq_left h1, Nat.mul_div_cancel_left _ hppos,
      show ℓ * (p * m) = p * (ℓ * m) by ring, Nat.mul_div_cancel_left _ hppos]
  · have h1 : ¬ p ∣ ℓ * n := fun h => hpn (hpl.dvd_of_dvd_mul_left h)
    rw [ite_eq_right hpn, ite_eq_right h1]

theorem apply_eq_zero_of_eigen {a : ℕ → ℂ} (h1 : a 1 = 0) (good : ℕ → Prop) (c lam : ℕ → ℂ)
    (heig : ∀ p : ℕ, p.Prime → good p → heckeSeq p (c p) a = lam p • a) :
    ∀ n : ℕ, n ≠ 0 → (∀ p : ℕ, p.Prime → p ∣ n → good p) → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hgood
    rcases Nat.lt_or_ge 1 n with hlt | hle
    ·
      set p := n.minFac with hp
      have hpp : p.Prime := Nat.minFac_prime (ne_of_gt hlt)
      have hpn : p ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hpn
      have hppos : 0 < p := hpp.pos
      have hm0 : m ≠ 0 := by rintro rfl; simp [hm] at hn
      have hmlt : m < n := by
        rw [hm]; exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hm0) hpp.one_lt
      have hgood_p : good p := hgood p hpp ⟨m, hm⟩
      have hrel := (heckeSeq_eq_smul_iff.mp (heig p hpp hgood_p)) m
      have ham : a m = 0 :=
        ih m hmlt hm0 fun q hq hqm => hgood q hq (dvd_trans hqm ⟨p, by rw [hm, mul_comm]⟩)
      have hmid : (if p ∣ m then a (m / p) else 0) = 0 := by
        split_ifs with hpm
        · obtain ⟨r, rfl⟩ := hpm
          rw [Nat.mul_div_cancel_left _ hppos]
          have hr0 : r ≠ 0 := by rintro rfl; simp at hm0
          refine ih r ?_ hr0 fun q hq hqr => hgood q hq ?_
          · calc r < p * r := lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hr0) hpp.one_lt
              _ < n := hmlt
          · exact dvd_trans hqr ⟨p * p, by rw [hm]; ring⟩
        · rfl
      rw [hmid, ham, mul_zero, mul_zero, add_zero] at hrel
      rw [hm]
      exact hrel
    · interval_cases n
      · exact absurd rfl hn
      · exact h1

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

theorem exists_packet_eq_of_mem_span {K V P : Type*} [Field K] [AddCommGroup V] [Module K V]
    (T : P → V →ₗ[K] V) (G : Set V) (pk : V → P → K)
    (hG : ∀ v ∈ G, ∀ p, T p v = pk v p • v) {w : V} (hw : w ∈ Submodule.span K G) (α : P → K)
    (hα : ∀ p, T p w = α p • w) (hne : w ≠ 0) :
    ∃ v ∈ G, ∀ p, pk v p = α p := by
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hw
  obtain ⟨i, -, hi⟩ := exists_packet_eq T (fun i => (g i : V)) (fun i => pk (g i)) α Finset.univ c
    (fun i _ p => hG _ (g i).2 p) (fun p => by rw [hsum]; exact hα p) (by rw [hsum]; exact hne)
  exact ⟨g i, (g i).2, hi⟩

section Forms

variable {L : ℕ} {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁(L)).strictPeriods := by
  rw [strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples 1

def cf (f : CuspForm Γ₁(L) k) : ℕ → ℂ := fun n => qCoeff f n

theorem cf_apply (f : CuspForm Γ₁(L) k) (n : ℕ) : cf f n = qCoeff f n := rfl

theorem cf_add (f g : CuspForm Γ₁(L) k) : cf (f + g) = cf f + cf g := by
  funext n
  simp only [cf, Pi.add_apply]
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_add, ModularForm.qExpansion_add one_pos (one_mem_strictPeriods L) f g]
  simp

theorem cf_smul (c : ℂ) (f : CuspForm Γ₁(L) k) : cf (c • f) = c • cf f := by
  funext n
  simp only [cf, Pi.smul_apply, smul_eq_mul]
  unfold ModularFormClass.qCoeff
  rw [FunLike.coe_smul, ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods L) c f]
  simp

def cfLin : CuspForm Γ₁(L) k →ₗ[ℂ] (ℕ → ℂ) where
  toFun := cf
  map_add' := cf_add
  map_smul' := cf_smul

@[scoped simp] theorem cfLin_apply (f : CuspForm Γ₁(L) k) : cfLin f = cf f := rfl

theorem cf_zero : cf (0 : CuspForm Γ₁(L) k) = 0 := by
  rw [← cfLin_apply, map_zero]

theorem cf_sub (f g : CuspForm Γ₁(L) k) : cf (f - g) = cf f - cf g := by
  rw [← cfLin_apply, map_sub]; rfl

theorem cf_sum {ι : Type*} (s : Finset ι) (f : ι → CuspForm Γ₁(L) k) :
    cf (∑ i ∈ s, f i) = ∑ i ∈ s, cf (f i) := by
  rw [← cfLin_apply, map_sum]; rfl

theorem cf_injective {f g : CuspForm Γ₁(L) k} (h : cf f = cf g) : f = g :=
  ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods L) fun n => congrFun h n

theorem eq_zero_of_cf_eq_zero {f : CuspForm Γ₁(L) k} (h : cf f = 0) : f = 0 :=
  cf_injective (h.trans cf_zero.symm)

theorem hasNebentypus_zero (ε : DirichletCharacter ℂ L) :
    CuspForm.HasNebentypus ε (0 : CuspForm Γ₁(L) k) := by
  intro γ _ τ
  simp

theorem hasNebentypus_add {ε : DirichletCharacter ℂ L} {f g : CuspForm Γ₁(L) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  simp only [add_apply]
  rw [hf γ hγ τ, hg γ hγ τ]
  ring

theorem hasNebentypus_smul {ε : DirichletCharacter ℂ L} {f : CuspForm Γ₁(L) k}
    (hf : CuspForm.HasNebentypus ε f) (c : ℂ) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  simp only [smul_apply, smul_eq_mul]
  rw [hf γ hγ τ]
  ring

theorem hasNebentypus_sub {ε : DirichletCharacter ℂ L} {f g : CuspForm Γ₁(L) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f - g) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ g]
  exact hasNebentypus_add hf (hasNebentypus_smul hg _)

theorem hasNebentypus_sum {ε : DirichletCharacter ℂ L} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm Γ₁(L) k) (hf : ∀ i ∈ s, CuspForm.HasNebentypus ε (f i)) :
    CuspForm.HasNebentypus ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNebentypus_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasNebentypus_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

end Forms

theorem changeLevel_apply_natCast {M N : ℕ} [NeZero N] (hMN : M ∣ N) (εM : DirichletCharacter ℂ M)
    (ε : DirichletCharacter ℂ N) (h : DirichletCharacter.changeLevel hMN εM = ε)
    (p : ℕ) (hp : Nat.Coprime p N) :
    εM (p : ZMod M) = ε (p : ZMod N) := by
  set u : (ZMod N)ˣ := ZMod.unitOfCoprime p hp with hu
  have hu' : (u : ZMod N) = (p : ZMod N) := ZMod.coe_unitOfCoprime p hp
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu',
    ZMod.cast_natCast hMN]

theorem dirichletCharacter_eq_of_forall_prime {N : ℕ} [NeZero N] {χ₁ χ₂ : DirichletCharacter ℂ N}
    (S : Finset ℕ) (h : ∀ p : ℕ, p.Prime → p ∉ S → χ₁ (p : ZMod N) = χ₂ (p : ZMod N)) :
    χ₁ = χ₂ := by
  refine MulChar.ext fun u => ?_
  obtain ⟨p, hpgt, hp, hpu⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (Units.isUnit u) (S.sup id)
  have hpS : p ∉ S := fun hpS => by
    have : p ≤ S.sup id := Finset.le_sup (f := id) hpS
    omega
  rw [← hpu]
  exact h p hp hpS

section Prim

variable (k : ℤ)

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

structure PrimData (L : ℕ) (ε : DirichletCharacter ℂ L) (Q : ℕ → Prop) where

  M : ℕ

  d : ℕ
  hML : M * d ∣ L

  εM : DirichletCharacter ℂ M

  g : CuspForm Γ₁(M) k
  hQ : Q M
  prim : CuspForm.IsPrimitiveForm εM g
  hch : DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hML) εM = ε

variable {k}

def PrimData.seq {L : ℕ} {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop} (x : PrimData k L ε Q) : ℕ → ℂ :=
  stretchLin x.d (cf x.g)


variable (k) in
def primSet (L : ℕ) (ε : DirichletCharacter ℂ L) (Q : ℕ → Prop) : Set (ℕ → ℂ) :=
  Set.range (PrimData.seq : PrimData k L ε Q → ℕ → ℂ)

theorem PrimData.seq_mem {L : ℕ} {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop} (x : PrimData k L ε Q) :
    x.seq ∈ primSet k L ε Q := ⟨x, rfl⟩

theorem PrimData.d_ne_zero {L : ℕ} [NeZero L] {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop}
    (x : PrimData k L ε Q) : x.d ≠ 0 := fun h0 =>
  (NeZero.ne L) (Nat.eq_zero_of_zero_dvd (h0 ▸ dvd_of_mul_left_dvd x.hML))

theorem PrimData.M_dvd {L : ℕ} {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop} (x : PrimData k L ε Q) :
    x.M ∣ L := dvd_of_mul_right_dvd x.hML

theorem primSet_mono {L : ℕ} {ε : DirichletCharacter ℂ L} {Q Q' : ℕ → Prop} (hQ : ∀ M, Q M → Q' M) :
    primSet k L ε Q ⊆ primSet k L ε Q' := by
  rintro _ ⟨x, rfl⟩
  exact ⟨⟨x.M, x.d, x.hML, x.εM, x.g, hQ _ x.hQ, x.prim, x.hch⟩, rfl⟩

theorem stretchLin_mem_span {L M' d : ℕ} [NeZero L] (hd : M' * d ∣ L) {ε' : DirichletCharacter ℂ M'}
    {ε : DirichletCharacter ℂ L}
    (hε : DirichletCharacter.changeLevel (dvd_of_mul_right_dvd hd) ε' = ε)
    {Q Q' : ℕ → Prop} (hQ : ∀ M, M ∣ M' → Q M → Q' M)
    {s : ℕ → ℂ} (hs : s ∈ Submodule.span ℂ (primSet k M' ε' Q)) :
    stretchLin d s ∈ Submodule.span ℂ (primSet k L ε Q') := by
  have hM' : NeZero M' := ⟨fun h0 => (NeZero.ne L) (Nat.eq_zero_of_zero_dvd (by
    rw [h0, zero_mul] at hd; exact hd))⟩
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact (NeZero.ne L) (Nat.eq_zero_of_zero_dvd (by simpa using hd))
  have himage : (stretchLin d) '' primSet k M' ε' Q ⊆ primSet k L ε Q' := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hML : x.M * (x.d * d) ∣ L := by
      rw [← mul_assoc]; exact dvd_trans (mul_dvd_mul_right x.hML d) hd
    refine ⟨⟨x.M, x.d * d, hML, x.εM, x.g, hQ _ x.M_dvd x.hQ, x.prim, ?_⟩, ?_⟩
    · rw [DirichletCharacter.changeLevel_trans x.εM x.M_dvd (dvd_of_mul_right_dvd hd), x.hch, hε]
    · simp only [PrimData.seq]
      rw [stretchLin_stretchLin hd0 x.d_ne_zero]
  have h1 : stretchLin d s ∈ Submodule.map (stretchLin d) (Submodule.span ℂ (primSet k M' ε' Q)) :=
    Submodule.mem_map_of_mem hs
  rw [Submodule.map_span] at h1
  exact Submodule.span_mono himage h1

theorem PrimData.heckeSeq_seq {L : ℕ} [NeZero L] {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop}
    (x : PrimData k L ε Q) {p : ℕ} (hp : p.Prime) (hpL : ¬ p ∣ L) :
    heckeSeq p (ε (p : ZMod L) * (p : ℂ) ^ (k - 1)) x.seq = (qCoeff x.g p) • x.seq := by
  have hpM : ¬ p ∣ x.M := fun h' => hpL (dvd_trans h' x.M_dvd)
  have hpd : Nat.Coprime p x.d :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr fun h' => hpL (dvd_trans h' (dvd_of_mul_left_dvd x.hML))
  have hpcop : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpL
  have hε : x.εM (p : ZMod x.M) = ε (p : ZMod L) :=
    changeLevel_apply_natCast x.M_dvd x.εM ε x.hch p hpcop
  refine heckeSeq_stretchLin hp.ne_zero x.d_ne_zero hpd ?_
  rw [heckeSeq_eq_smul_iff]
  intro n
  have := x.prim.isEigenformWith.hecke_of_not_dvd hp hpM n
  rw [hε] at this
  exact this

theorem exists_prim_of_mem_span {L : ℕ} [NeZero L] {ε : DirichletCharacter ℂ L} {Q : ℕ → Prop}
    {s : ℕ → ℂ} (hs : s ∈ Submodule.span ℂ (primSet k L ε Q)) (hs0 : s ≠ 0)
    (F : Set ℕ) (hF : ∀ p ∈ F, p.Prime ∧ ¬ p ∣ L) (lam : ℕ → ℂ)
    (heig : ∀ p ∈ F, heckeSeq p (ε (p : ZMod L) * (p : ℂ) ^ (k - 1)) s = lam p • s) :
    ∃ x : PrimData k L ε Q, ∀ p ∈ F, qCoeff x.g p = lam p := by
  classical
  let T : F → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun p => heckeSeq p (ε (p : ZMod L) * (p : ℂ) ^ (k - 1))
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).mp hs

  have hsum : ∑ x ∈ c.support, c x • (x : PrimData k L ε Q).seq = s := hc
  obtain ⟨x, -, hx⟩ := exists_packet_eq T (fun x : PrimData k L ε Q => x.seq)
    (fun x (p : F) => qCoeff x.g p) (fun p : F => lam p) c.support c
    (fun x _ p => x.heckeSeq_seq (hF p p.2).1 (hF p p.2).2)
    (fun p => by rw [hsum]; exact heig p p.2) (by rw [hsum]; exact hs0)
  exact ⟨x, fun p hp => hx ⟨p, hp⟩⟩

end Prim

section Induction

variable {k : ℤ}

local notation "Γ₁(" M ")" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem decSeq_smul (ℓ : ℕ) (c : ℂ) (s : ℕ → ℂ) : decSeq ℓ (c • s) = c • decSeq ℓ s := rfl

theorem decSeq_sub (ℓ : ℕ) (s t : ℕ → ℂ) : decSeq ℓ (s - t) = decSeq ℓ s - decSeq ℓ t := rfl

variable (k) in
def Decomp (L : ℕ) : Prop :=
  ∀ (_ : NeZero L) (ε : DirichletCharacter ℂ L) (f : CuspForm Γ₁(L) k),
    CuspForm.HasNebentypus ε f → cf f ∈ Submodule.span ℂ (primSet k L ε fun _ => True)

theorem old_mem_span {N : ℕ} [NeZero N] (ih : ∀ L, L ∣ N → L ≠ N → Decomp k L)
    {ε : DirichletCharacter ℂ N} {u : CuspForm Γ₁(N) k} (hu : CuspForm.HasNebentypus ε u)
    {K : ℕ} (hK : K ≠ 0) (hvan : ∀ n : ℕ, Nat.Coprime n K → qCoeff u n = 0) :
    cf u ∈ Submodule.span ℂ (primSet k N ε (· ≠ N)) := by
  obtain ⟨g, hg, hdec⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      N k K hK ε u hu hvan
  have hcf : cf u = ∑ p ∈ N.primeFactors, stretchLin p (cf (g p)) := by
    funext n
    rw [Finset.sum_apply]
    exact hdec n
  rw [hcf]
  refine Submodule.sum_mem _ fun p hp => ?_
  have hpN : p ∣ N := Nat.dvd_of_mem_primeFactors hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  rcases hg p hp with h0 | ⟨εp, hεp, hgp⟩
  · rw [h0, cf_zero, map_zero]
    exact zero_mem _
  · have hpos : 0 < N / p := Nat.div_pos (Nat.le_of_dvd (NeZero.pos N) hpN) hpp.pos
    have hne : NeZero (N / p) := ⟨hpos.ne'⟩
    have hlt : N / p < N := Nat.div_lt_self (NeZero.pos N) hpp.one_lt
    have hmem := ih (N / p) (Nat.div_dvd_of_dvd hpN) hlt.ne hne εp (g p) hgp
    have hd : N / p * p ∣ N := by rw [Nat.div_mul_cancel hpN]
    refine stretchLin_mem_span hd hεp (fun M hM _ => ?_) hmem
    exact (lt_of_le_of_lt (Nat.le_of_dvd hpos hM) hlt).ne

theorem old_of_eigen {N : ℕ} [NeZero N] (ih : ∀ L, L ∣ N → L ≠ N → Decomp k L)
    {ε : DirichletCharacter ℂ N} {v : CuspForm Γ₁(N) k} (hv : CuspForm.HasNebentypus ε v)
    (h1 : qCoeff v 1 = 0) (S : Finset ℕ) (c lam : ℕ → ℂ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S → heckeSeq p (c p) (cf v) = lam p • cf v) :
    cf v ∈ Submodule.span ℂ (primSet k N ε (· ≠ N)) := by

  set K : ℕ := 2 * N * ∏ q ∈ S, max q 1 with hK
  have hprod : (∏ q ∈ S, max q 1) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun q _ => (Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right q 1)).ne'
  have hK0 : K ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero (NeZero.ne N)) hprod
  have hK1 : K ≠ 1 := by
    intro hK1
    have h2 : 2 ∣ K := ⟨N * ∏ q ∈ S, max q 1, by rw [hK]; ring⟩
    rw [hK1] at h2
    exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
  refine old_mem_span ih hv hK0 fun n hn => ?_
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hK1 (Nat.coprime_zero_left _ |>.mp hn)
  refine apply_eq_zero_of_eigen (a := cf v) h1 (fun p => ¬ p ∣ N ∧ p ∉ S) c lam
    (fun p hp hg => heig p hp hg.1 hg.2) n hn0 fun p hp hpn => ?_
  have hpK : ¬ p ∣ K := fun hpK => by
    have h1' : p ∣ 1 := by
      have := Nat.dvd_gcd hpn hpK
      rwa [Nat.Coprime.gcd_eq_one hn] at this
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1')
  refine ⟨fun hpN => hpK (dvd_trans hpN ⟨2 * ∏ q ∈ S, max q 1, by rw [hK]; ring⟩),
    fun hpS => hpK ?_⟩
  have : p ∣ ∏ q ∈ S, max q 1 := by
    have := Finset.dvd_prod_of_mem (fun q => max q 1) hpS
    simp only [max_eq_left hp.one_lt.le] at this
    exact this
  exact dvd_trans this ⟨2 * N, by rw [hK]; ring⟩

theorem eigen_mem_span_of_qCoeff_one {N : ℕ} [NeZero N] (ih : ∀ L, L ∣ N → L ≠ N → Decomp k L)
    {ε : DirichletCharacter ℂ N} {w : CuspForm Γ₁(N) k} (hw : CuspForm.HasNebentypus ε w)
    (h1 : qCoeff w 1 = 1) (lam : ℕ → ℂ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf w) = lam p • cf w) :
    cf w ∈ Submodule.span ℂ (primSet k N ε fun _ => True) := by
  classical

  have hlam : ∀ p : ℕ, p.Prime → ¬ p ∣ N → qCoeff w p = lam p := by
    intro p hp hpN
    have := (heckeSeq_eq_smul_iff.mp (heig p hp hpN)) 1
    rwa [mul_one, ite_eq_right (fun h => hp.one_lt.ne' (Nat.dvd_one.mp h)), mul_zero, add_zero,
      cf_apply, cf_apply, h1, mul_one] at this
  by_cases hex : ∃ (M : ℕ) (hM : M ∣ N), M ≠ N ∧ ∃ (εM : DirichletCharacter ℂ M) (g : CuspForm Γ₁(M) k),
      CuspForm.IsPrimitiveForm εM g ∧ DirichletCharacter.changeLevel hM εM = ε ∧
        ∃ S : Finset ℕ, ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S → qCoeff g p = lam p
  ·
    obtain ⟨M, hM, hMN, εM, g, hprim, hch, S, hS⟩ := hex
    have hM1 : M * 1 ∣ N := by rwa [mul_one]
    obtain ⟨G, -, hGq, hGε⟩ := CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) hM1 g
    have hGε' : CuspForm.HasNebentypus ε G := by
      have := hGε εM hprim.isEigenformWith.hasNebentypus
      rwa [hch] at this
    let x₀ : PrimData k N ε (fun _ => True) := ⟨M, 1, hM1, εM, g, trivial, hprim, hch⟩
    have hx₀ : x₀.seq = cf g := by
      simp only [PrimData.seq]
      exact stretchLin_one _
    have hcfG : cf G = cf g := by
      funext n
      rw [cf_apply, hGq n, ite_eq_left (one_dvd n), Nat.div_one, cf_apply]
    have hv1 : qCoeff (⇑(w - G)) 1 = 0 := by
      have := congrFun (cf_sub w G) 1
      rw [cf_apply, Pi.sub_apply, cf_apply, cf_apply, h1, hGq 1, ite_eq_left (one_dvd 1), Nat.div_one,
        hprim.isEigenformWith.qCoeff_one, sub_self] at this
      exact this
    have heigG : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S →
        heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf G) = lam p • cf G := by
      intro p hp hpN hpS
      rw [hcfG, ← hx₀, ← hS p hp hpN hpS]
      exact x₀.heckeSeq_seq hp hpN
    have heigv : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ S →
        heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf (w - G)) = lam p • cf (w - G) := by
      intro p hp hpN hpS
      rw [cf_sub, map_sub, heig p hp hpN, heigG p hp hpN hpS, smul_sub]
    have hold := old_of_eigen ih (hasNebentypus_sub hw hGε') hv1 S _ lam heigv
    have hsplit : cf w = cf (w - G) + cf G := by rw [cf_sub, sub_add_cancel]
    rw [hsplit]
    refine add_mem (Submodule.span_mono (primSet_mono fun _ _ => trivial) hold) ?_
    rw [hcfG, ← hx₀]
    exact Submodule.subset_span x₀.seq_mem
  ·
    suffices hprimw : CuspForm.IsPrimitiveForm ε w by
      let x₀ : PrimData k N ε (fun _ => True) :=
        ⟨N, 1, by rw [mul_one], ε, w, trivial, hprimw, DirichletCharacter.changeLevel_self ε⟩
      have hx₀ : x₀.seq = cf w := by
        simp only [PrimData.seq]
        exact stretchLin_one _
      rw [← hx₀]
      exact Submodule.subset_span x₀.seq_mem

    have hforbid : ∀ s : ℕ → ℂ, s ∈ Submodule.span ℂ (primSet k N ε (· ≠ N)) →
        (∀ p : ℕ, p.Prime → ¬ p ∣ N →
          heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) s = lam p • s) → s = 0 := by
      intro s hs hseig
      by_contra hs0
      obtain ⟨x, hx⟩ := exists_prim_of_mem_span hs hs0 {p | p.Prime ∧ ¬ p ∣ N} (fun p hp => hp) lam
        (fun p hp => hseig p hp.1 hp.2)
      exact hex ⟨x.M, x.M_dvd, x.hQ, x.εM, x.g, x.prim, x.hch, ∅, fun p hp hpN _ => hx p ⟨hp, hpN⟩⟩
    refine ⟨⟨h1, ?_, ?_, hw⟩, ?_⟩
    ·
      intro p hp hpN n
      have := (heckeSeq_eq_smul_iff.mp (heig p hp hpN)) n
      rwa [← hlam p hp hpN] at this
    ·
      intro ℓ hℓ hℓN n
      obtain ⟨U, -, hUq, hUε⟩ := CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd k hℓN w
      have hcfU : cf U = decSeq ℓ (cf w) := funext hUq
      have hUε' : CuspForm.HasNebentypus ε U := hUε ε hw
      set u : CuspForm Γ₁(N) k := U - (qCoeff w ℓ) • w with hu
      have hcfu : cf u = decSeq ℓ (cf w) - qCoeff w ℓ • cf w := by
        rw [hu, cf_sub, cf_smul, hcfU]
      have hu1 : qCoeff u 1 = 0 := by
        have := congrFun hcfu 1
        rw [cf_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, decSeq, mul_one, cf_apply, cf_apply,
          h1, mul_one, sub_self] at this
        exact this
      have hueig : ∀ p : ℕ, p.Prime → ¬ p ∣ N → p ∉ (∅ : Finset ℕ) →
          heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf u) = lam p • cf u := by
        intro p hp hpN _
        have hpl : Nat.Coprime p ℓ := (Nat.coprime_primes hp hℓ).mpr fun h => hpN (h ▸ hℓN)
        rw [hcfu, map_sub, map_smul, heckeSeq_decSeq hp.ne_zero hpl, heig p hp hpN, decSeq_smul,
          smul_sub, smul_comm (qCoeff w ℓ) (lam p) (cf w)]
      have hold := old_of_eigen ih (hasNebentypus_sub hUε' (hasNebentypus_smul hw _)) hu1 ∅ _ lam hueig
      have hu0 : cf u = 0 := hforbid _ hold fun p hp hpN => hueig p hp hpN (Finset.notMem_empty p)
      have := congrFun (hcfu.symm.trans hu0) n
      rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, decSeq, cf_apply, cf_apply, Pi.zero_apply] at this
      exact sub_eq_zero.mp this
    ·
      intro M' hM' hne hocc
      obtain ⟨ε', h, hh0, hε'h, S, hS⟩ := hocc
      have hne' : NeZero M' := ⟨fun h0 => (NeZero.ne N) (Nat.eq_zero_of_zero_dvd (h0 ▸ hM'))⟩
      have hmem : cf h ∈ Submodule.span ℂ (primSet k M' ε' fun _ => True) := ih M' hM' hne hne' ε' h hε'h
      have hh0' : cf h ≠ 0 := fun h0 => hh0 (eq_zero_of_cf_eq_zero h0)
      obtain ⟨x, hx⟩ := exists_prim_of_mem_span hmem hh0' {p | p.Prime ∧ p ∉ S ∧ ¬ p ∣ N}
        (fun p hp => ⟨hp.1, fun h' => hp.2.2 (dvd_trans h' hM')⟩) (fun p => qCoeff w p)
        (fun p hp => by
          obtain ⟨-, hrel⟩ := hS p hp.1 hp.2.1
          rw [heckeSeq_eq_smul_iff]
          exact hrel)
      apply hex
      refine ⟨x.M, dvd_trans x.M_dvd hM', fun hMN => hne (Nat.dvd_antisymm hM' (hMN ▸ x.M_dvd)),
        x.εM, x.g, x.prim, ?_, S, fun p hp hpN hpS => ?_⟩
      ·
        rw [DirichletCharacter.changeLevel_trans x.εM x.M_dvd hM', x.hch]
        refine dirichletCharacter_eq_of_forall_prime (S ∪ N.primeFactors) fun p hp hpS => ?_
        rw [Finset.mem_union, not_or] at hpS
        have hpN : ¬ p ∣ N := fun h' => hpS.2 (Nat.mem_primeFactors.mpr ⟨hp, h', NeZero.ne N⟩)
        rw [← changeLevel_apply_natCast hM' ε' _ rfl p ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpN)]
        exact (hS p hp hpS.1).1
      · rw [hx p ⟨hp, hpS, hpN⟩, hlam p hp hpN]

theorem eigen_mem_span {N : ℕ} [NeZero N] (ih : ∀ L, L ∣ N → L ≠ N → Decomp k L)
    {ε : DirichletCharacter ℂ N} {w : CuspForm Γ₁(N) k} (hw : CuspForm.HasNebentypus ε w)
    (lam : ℕ → ℂ)
    (heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
      heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf w) = lam p • cf w) :
    cf w ∈ Submodule.span ℂ (primSet k N ε fun _ => True) := by
  by_cases h1 : qCoeff w 1 = 0
  · exact Submodule.span_mono (primSet_mono fun _ _ => trivial)
      (old_of_eigen ih hw h1 ∅ _ lam fun p hp hpN _ => heig p hp hpN)
  · set c : ℂ := qCoeff w 1 with hc
    have hw' : CuspForm.HasNebentypus ε (c⁻¹ • w) := hasNebentypus_smul hw _
    have h1' : qCoeff (⇑(c⁻¹ • w)) 1 = 1 := by
      have := congrFun (cf_smul c⁻¹ w) 1
      rw [cf_apply, Pi.smul_apply, smul_eq_mul, cf_apply, ← hc, inv_mul_cancel₀ h1] at this
      exact this
    have heig' : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        heckeSeq p (ε (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf (c⁻¹ • w)) = lam p • cf (c⁻¹ • w) := by
      intro p hp hpN
      rw [cf_smul, map_smul, heig p hp hpN, smul_comm]
    have hmem := eigen_mem_span_of_qCoeff_one ih hw' h1' lam heig'
    have : cf w = c • cf (c⁻¹ • w) := by rw [cf_smul, smul_smul, mul_inv_cancel₀ h1, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ hmem

theorem decomp (k : ℤ) : ∀ N : ℕ, Decomp k N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro hN ε f hf
    classical
    have ih' : ∀ L, L ∣ N → L ≠ N → Decomp k L := fun L hL hne =>
      ih L (lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos N) hL) hne)
    obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen N k
    choose εb hεb hTb using hb

    have hrepr : ∑ i, (b.repr f i) • b i = f := b.sum_repr f
    have hfilt := CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq Finset.univ εb
      (fun i => b.repr f i • b i) (fun i _ => hasNebentypus_smul (hεb i) _) hf hrepr
    rw [← hfilt, cf_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨-, hi⟩ := Finset.mem_filter.mp hi
    rw [cf_smul]
    refine Submodule.smul_mem _ _ ?_

    choose lam hlam using hTb i
    let lam' : ℕ → ℂ := fun p => if h : p.Prime ∧ ¬ p ∣ N then lam p h.1 h.2 else 0
    have heig : ∀ p : ℕ, p.Prime → ¬ p ∣ N →
        heckeSeq p (εb i (p : ZMod N) * (p : ℂ) ^ (k - 1)) (cf (b i)) = lam' p • cf (b i) := by
      intro p hp hpN
      rw [heckeSeq_eq_smul_iff]
      intro m
      simp only [lam', dite_eq_left (show p.Prime ∧ ¬ p ∣ N from ⟨hp, hpN⟩)]
      exact hlam p hp hpN m
    have := eigen_mem_span ih' (hεb i) lam' heig
    rwa [hi] at this

end Induction

end ALLiDecomposition

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) k)
    (hf : CuspForm.HasNebentypus ε f) :
    ∃ (n : ℕ) (M d : Fin n → ℕ) (hM : ∀ i, M i * d i ∣ N)
      (εM : (i : Fin n) → DirichletCharacter ℂ (M i))
      (g : (i : Fin n) → CuspForm (Gamma1 (M i)) k) (c : Fin n → ℂ),
      (∀ i, CuspForm.IsPrimitiveForm (εM i) (g i) ∧
        DirichletCharacter.changeLevel (dvd_of_mul_right_dvd (hM i)) (εM i) = ε) ∧
      ∀ m : ℕ, ModularFormClass.qCoeff f m =
        ∑ i, c i * (if d i ∣ m then ModularFormClass.qCoeff (g i) (m / d i) else 0) := by
  classical
  have hmem := ALLiDecomposition.decomp k N inferInstance ε f hf
  obtain ⟨n, c, g, hsum⟩ := Submodule.mem_span_set'.mp hmem
  have hx : ∀ i, ∃ x : ALLiDecomposition.PrimData k N ε (fun _ => True),
      x.seq = (g i : ℕ → ℂ) := fun i => (g i).2
  choose x hx using hx
  refine ⟨n, fun i => (x i).M, fun i => (x i).d, fun i => (x i).hML, fun i => (x i).εM,
    fun i => (x i).g, c, fun i => ⟨(x i).prim, (x i).hch⟩, fun m => ?_⟩
  have := congrFun hsum m
  rw [Finset.sum_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul] at this
  rw [show ModularFormClass.qCoeff (⇑f) m = ALLiDecomposition.cf f m from rfl, ← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hx i]
  rfl

open CongruenceSubgroup ModularFormClass UpperHalfPlane Function
open scoped MatrixGroups


namespace MultOnePrimitive

local notation "Γ₁ℝ" M => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

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
    heckeSeq k e p s n = s (p * n) + e p * (p : ℂ) ^ (k - 1) * (if p ∣ n then s (n / p) else 0) :=
  rfl

def stretchSeq (d : ℕ) (b : ℕ → ℂ) : ℕ → ℂ := fun n => if d ∣ n then b (n / d) else 0

theorem stretchSeq_apply (d : ℕ) (b : ℕ → ℂ) (n : ℕ) :
    stretchSeq d b n = if d ∣ n then b (n / d) else 0 := rfl

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
  · obtain ⟨m, rfl⟩ := hdn
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
  · have h1 : ¬ d ∣ p * n := fun h => hdn ((Nat.Coprime.symm hpd).dvd_of_dvd_mul_left h)
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
  rw [← h, ← hu', DirichletCharacter.changeLevel_eq_cast_of_dvd εM hMN u, hu',
    ZMod.cast_natCast hMN]

section QCoeff

variable {L : ℕ} {k : ℤ}

theorem one_mem_strictPeriods (L : ℕ) : (1 : ℝ) ∈ (Γ₁ℝ L).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma1]
  exact AddSubgroup.mem_zmultiples _

theorem periodic (f : CuspForm (Γ₁ℝ L) k) : Periodic (⇑f ∘ ofComplex) 1 :=
  SlashInvariantFormClass.periodic_comp_ofComplex f (one_mem_strictPeriods L)

theorem bdd (f : CuspForm (Γ₁ℝ L) k) : IsBoundedAtImInfty (⇑f) := by
  have hc : Fact (IsCusp OnePoint.infty (Γ₁ℝ L)) :=
    ⟨(Γ₁ℝ L).isCusp_of_mem_strictPeriods one_pos (one_mem_strictPeriods L)⟩
  exact ModularFormClass.bdd_at_infty f

theorem analytic (f : CuspForm (Γ₁ℝ L) k) : AnalyticAt ℂ (cuspFunction 1 (⇑f)) 0 :=
  analyticAt_cuspFunction_zero one_pos (periodic f) f.holo' (bdd f)

theorem eq_of_qCoeff_eq (f₁ f₂ : CuspForm (Γ₁ℝ L) k) (h : ∀ n : ℕ, qCoeff f₁ n = qCoeff f₂ n) :
    f₁ = f₂ :=
  DFunLike.ext' (UpperHalfPlane.eq_of_forall_qCoeff_eq (periodic f₁) f₁.holo' (bdd f₁)
    (periodic f₂) f₂.holo' (bdd f₂) h)

theorem qCoeff_zero_fun (n : ℕ) : qCoeff (0 : ℍ → ℂ) n = 0 := by
  rw [qCoeff, UpperHalfPlane.qExpansion_zero, map_zero]

theorem qCoeff_zero (n : ℕ) : qCoeff (⇑(0 : CuspForm (Γ₁ℝ L) k)) n = 0 := by
  rw [FunLike.coe_zero, qCoeff_zero_fun]

theorem qCoeff_add (f₁ f₂ : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(f₁ + f₂)) n = qCoeff (⇑f₁) n + qCoeff (⇑f₂) n := by
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_add, qExpansion_add (analytic f₁) (analytic f₂), map_add]

theorem qCoeff_smul (c : ℂ) (f : CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  rw [qCoeff, qCoeff, FunLike.coe_smul, qExpansion_smul (analytic f), map_smul, smul_eq_mul]

theorem qCoeff_sub_smul (f g : CuspForm (Γ₁ℝ L) k) (c : ℂ) (n : ℕ) :
    qCoeff (⇑(f - c • g)) n = qCoeff (⇑f) n - c * qCoeff (⇑g) n := by
  have hcg : AnalyticAt ℂ (cuspFunction 1 (c • (⇑g : ℍ → ℂ))) 0 := analytic (c • g)
  rw [qCoeff, qCoeff, qCoeff, FunLike.coe_sub, FunLike.coe_smul,
    qExpansion_sub (analytic f) hcg, map_sub, qExpansion_smul (analytic g), map_smul, smul_eq_mul]

theorem qCoeff_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → CuspForm (Γ₁ℝ L) k) (n : ℕ) :
    qCoeff (⇑(∑ i ∈ s, c i • f i)) n = ∑ i ∈ s, c i * qCoeff (⇑(f i)) n := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, qCoeff_zero]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj, qCoeff_add, qCoeff_smul, ih]

end QCoeff

theorem hasNebentypus_sub_smul {L : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ L}
    {f g : CuspForm (Γ₁ℝ L) k} (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g)
    (c : ℂ) : CuspForm.HasNebentypus ε (f - c • g) := by
  intro γ hγ τ
  have h1 := hf γ hγ τ
  have h2 := hg γ hγ τ
  simp only [FunLike.coe_sub, FunLike.coe_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [h1, h2]
  ring

theorem hasNebentypus_smul {L : ℕ} {k : ℤ} {ε : DirichletCharacter ℂ L}
    {g : CuspForm (Γ₁ℝ L) k} (hg : CuspForm.HasNebentypus ε g) (c : ℂ) :
    CuspForm.HasNebentypus ε (c • g) := by
  intro γ hγ τ
  have h2 := hg γ hγ τ
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  rw [h2]
  ring

theorem apply_eq_zero_of_good {k : ℤ} (a : ℕ → ℂ) (e lam : ℕ → ℂ) (good : ℕ → Prop)
    (h1 : a 1 = 0)
    (heig : ∀ q : ℕ, q.Prime → good q → ∀ m : ℕ,
      a (q * m) + e q * (q : ℂ) ^ (k - 1) * (if q ∣ m then a (m / q) else 0) = lam q * a m) :
    ∀ n : ℕ, n ≠ 0 → (∀ q : ℕ, q.Prime → q ∣ n → good q) → a n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn0 hgood
    by_cases hn1 : n = 1
    · rw [hn1]; exact h1
    · set q := n.minFac with hq
      have hqp : q.Prime := Nat.minFac_prime hn1
      have hqn : q ∣ n := Nat.minFac_dvd n
      obtain ⟨m, hm⟩ := hqn
      have hm0 : m ≠ 0 := by rintro rfl; exact hn0 (by rw [hm, mul_zero])
      have hmlt : m < n := by
        rw [hm]
        exact lt_mul_left (Nat.pos_of_ne_zero hm0) hqp.one_lt
      have hgood_m : ∀ r : ℕ, r.Prime → r ∣ m → good r :=
        fun r hr hrm => hgood r hr (hm ▸ dvd_mul_of_dvd_right hrm q)
      have ham : a m = 0 := ih m hmlt hm0 hgood_m
      have hrel := heig q hqp (hgood q hqp ⟨m, hm⟩) m
      rw [ham, mul_zero] at hrel
      have hmid : (if q ∣ m then a (m / q) else 0) = 0 := by
        split_ifs with hqm
        · obtain ⟨r, hr⟩ := hqm
          have hr0 : r ≠ 0 := by rintro rfl; exact hm0 (by rw [hr, mul_zero])
          have hrlt : r < n := by
            calc r < m := by rw [hr]; exact lt_mul_left (Nat.pos_of_ne_zero hr0) hqp.one_lt
              _ < n := hmlt
          have hdiv : m / q = r := by rw [hr, Nat.mul_div_cancel_left _ hqp.pos]
          rw [hdiv]
          exact ih r hrlt hr0 (fun t ht htr => hgood_m t ht (hr ▸ dvd_mul_of_dvd_right htr q))
        · rfl
      rw [hmid, mul_zero, add_zero] at hrel
      rw [hm]
      exact hrel

section PerPrime

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem perPrime (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (S : Finset ℕ)
    (p : ℕ) (hp : p ∈ M.primeFactors) (G : CuspForm (Γ₁ℝ (M / p)) k)
    (hG : G = 0 ∨ ∃ εp : DirichletCharacter ℂ (M / p),
      DirichletCharacter.changeLevel (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_primeFactors hp)) εp = ε ∧
        CuspForm.HasNebentypus εp G) :
    ∃ (n : ℕ) (v : Fin n → ℕ → ℂ) (lam : Fin n → ℕ → ℂ) (c : Fin n → ℂ) (s : Finset (Fin n)),
      (∀ i ∈ s, ∀ q : ℕ, q.Prime → ¬ q ∣ M →
        heckeSeq k (fun m => ε (m : ZMod M)) q (v i) = lam i q • v i) ∧
      (∀ i ∈ s, ¬ ∀ q : ℕ, q.Prime → q ∉ S → ¬ q ∣ M → lam i q = qCoeff (⇑g) q) ∧
      (∀ n : ℕ, (if p ∣ n then qCoeff (⇑G) (n / p) else 0) = ∑ i ∈ s, c i * v i n) := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpM : p ∣ M := Nat.dvd_of_mem_primeFactors hp
  have hM0 : M ≠ 0 := NeZero.ne M
  have hLdvd : M / p ∣ M := Nat.div_dvd_of_dvd hpM
  have hL0 : M / p ≠ 0 := by
    intro h0
    exact hM0 (Nat.eq_zero_of_zero_dvd (h0 ▸ hLdvd))
  have hLne : M / p ≠ M := by
    intro hLM
    have : M / p < M := Nat.div_lt_self (Nat.pos_of_ne_zero hM0) hpp.one_lt
    rw [hLM] at this
    exact lt_irrefl _ this
  have hMp : NeZero (M / p) := ⟨hL0⟩
  rcases hG with hG0 | ⟨εp, hεp, hGneb⟩
  ·
    refine ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, by simp, by simp, fun n => ?_⟩
    rw [hG0, Finset.sum_empty]
    split_ifs
    · exact qCoeff_zero _
    · rfl
  ·
    obtain ⟨n, bs, hbs⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen (M / p) k
    choose χ hχ hlam using hbs

    let lam : Fin n → ℕ → ℂ := fun i q =>
      if h : q.Prime ∧ ¬ q ∣ M / p then Classical.choose (hlam i q h.1 h.2) else 0
    have hlam_spec : ∀ i (q : ℕ) (hq : q.Prime) (hqL : ¬ q ∣ M / p), ∀ m : ℕ,
        qCoeff (⇑(bs i)) (q * m) + χ i (q : ZMod (M / p)) * (q : ℂ) ^ (k - 1) *
          (if q ∣ m then qCoeff (⇑(bs i)) (m / q) else 0) = lam i q * qCoeff (⇑(bs i)) m := by
      intro i q hq hqL m
      have : lam i q = Classical.choose (hlam i q hq hqL) := by
        simp only [lam, dite_eq_left (show q.Prime ∧ ¬ q ∣ M / p from ⟨hq, hqL⟩)]
      rw [this]
      exact Classical.choose_spec (hlam i q hq hqL) m

    set c : Fin n → ℂ := fun i => bs.repr G i with hc
    have hsum0 : ∑ i ∈ (Finset.univ : Finset (Fin n)), c i • bs i = G := by
      rw [hc]; exact bs.sum_repr G
    have hproj := CuspForm.HasNebentypus.sum_filter_eq_of_sum_eq (Finset.univ : Finset (Fin n)) χ
      (fun i => c i • bs i) (fun i _ => hasNebentypus_smul (hχ i) (c i)) hGneb hsum0
    set s := (Finset.univ : Finset (Fin n)).filter (fun i => χ i = εp) with hs
    let v : Fin n → ℕ → ℂ := fun i => stretchSeq p (fun m => qCoeff (⇑(bs i)) m)
    refine ⟨n, v, lam, c, s, ?_, ?_, ?_⟩
    ·
      intro i hi q hq hqM
      have hχi : χ i = εp := (Finset.mem_filter.1 hi).2
      have hqL : ¬ q ∣ M / p := fun h => hqM (dvd_trans h hLdvd)
      have hqcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM
      have hqp : Nat.Coprime q p :=
        (Nat.coprime_primes hq hpp).2 (fun h => hqM (h ▸ hpM))
      have hεq : χ i (q : ZMod (M / p)) = ε (q : ZMod M) := by
        rw [hχi]; exact changeLevel_apply_natCast hLdvd εp ε hεp q hqcop
      refine heckeSeq_stretchSeq hq.ne_zero hpp.ne_zero hqp (fun m => ?_)
      have := hlam_spec i q hq hqL m
      rw [hεq] at this
      exact this
    ·
      intro i hi hall
      have hχi : χ i = εp := (Finset.mem_filter.1 hi).2
      apply hg.not_eigenpacketOccursAt hLdvd hLne
      refine ⟨χ i, bs i, bs.ne_zero i, hχ i, S ∪ M.primeFactors, fun q hq hqS => ?_⟩
      rw [Finset.mem_union, not_or] at hqS
      have hqM : ¬ q ∣ M := fun h => hqS.2 (Nat.mem_primeFactors.2 ⟨hq, h, hM0⟩)
      have hqL : ¬ q ∣ M / p := fun h => hqM (dvd_trans h hLdvd)
      have hqcop : Nat.Coprime q M := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqM
      have hεq : χ i (q : ZMod (M / p)) = ε (q : ZMod M) := by
        rw [hχi]; exact changeLevel_apply_natCast hLdvd εp ε hεp q hqcop
      refine ⟨hεq, fun m => ?_⟩
      have := hlam_spec i q hq hqL m
      rw [hall q hq hqS.1 hqM] at this
      exact this
    ·
      intro m
      have hcoef : ∀ r : ℕ, qCoeff (⇑G) r = ∑ i ∈ s, c i * qCoeff (⇑(bs i)) r := by
        intro r
        rw [← qCoeff_sum s c bs r, hproj]
      simp only [v, stretchSeq_apply]
      split_ifs with hpm
      · rw [hcoef]
      · simp

end PerPrime

section Main

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem main (ε : DirichletCharacter ℂ M) (g : CuspForm (Γ₁ℝ M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (f : CuspForm (Γ₁ℝ M) k)
    (hf : CuspForm.HasNebentypus ε f) (S : Finset ℕ)
    (hfS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
        qCoeff (⇑f) (p * n) + ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
          (if p ∣ n then qCoeff (⇑f) (n / p) else 0) = qCoeff (⇑g) p * qCoeff (⇑f) n) :
    f = qCoeff (⇑f) 1 • g := by
  classical
  have hM0 : M ≠ 0 := NeZero.ne M
  have heig := hg.isEigenformWith
  set e : ℕ → ℂ := fun m => ε (m : ZMod M) with he
  set b : ℕ → ℂ := fun m => qCoeff (⇑g) m with hb

  set f' : CuspForm (Γ₁ℝ M) k := f - qCoeff (⇑f) 1 • g with hf'
  have hf'neb : CuspForm.HasNebentypus ε f' := hasNebentypus_sub_smul hf heig.hasNebentypus _
  set a : ℕ → ℂ := fun m => qCoeff (⇑f') m with ha
  have ha_apply : ∀ m, a m = qCoeff (⇑f) m - qCoeff (⇑f) 1 * qCoeff (⇑g) m := fun m =>
    qCoeff_sub_smul f g _ m
  have ha1 : a 1 = 0 := by rw [ha_apply, heig.qCoeff_one, mul_one, sub_self]
  let good : ℕ → Prop := fun q => q.Prime ∧ q ∉ S ∧ ¬ q ∣ M
  have haeig : ∀ q : ℕ, q.Prime → good q → ∀ m : ℕ,
      a (q * m) + e q * (q : ℂ) ^ (k - 1) * (if q ∣ m then a (m / q) else 0) = b q * a m := by
    intro q hq hgq m
    have h1 := hfS q hq hgq.2.1 hgq.2.2 m
    have h2 := heig.hecke_of_not_dvd hq hgq.2.2 m
    simp only [ha_apply, hb, he]
    have hite : (if q ∣ m then qCoeff (⇑f) (m / q) - qCoeff (⇑f) 1 * qCoeff (⇑g) (m / q) else 0) =
        (if q ∣ m then qCoeff (⇑f) (m / q) else 0) -
          qCoeff (⇑f) 1 * (if q ∣ m then qCoeff (⇑g) (m / q) else 0) := by
      split_ifs <;> ring
    rw [hite]
    linear_combination h1 - qCoeff (⇑f) 1 * h2

  set K : ℕ := 2 * M * ∏ q ∈ S.filter Nat.Prime, q with hK
  have hK0 : K ≠ 0 := by
    rw [hK]
    refine mul_ne_zero (mul_ne_zero two_ne_zero hM0) ?_
    rw [Finset.prod_ne_zero_iff]
    intro q hq
    exact (Nat.prime_of_mem_primeFactors (by
      have := (Finset.mem_filter.1 hq).2
      exact Nat.mem_primeFactors.2 ⟨this, dvd_refl q, this.ne_zero⟩)).ne_zero
  have hvan : ∀ m : ℕ, Nat.Coprime m K → a m = 0 := by
    intro m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hm
      have h2 : 2 ∣ K := ⟨M * ∏ q ∈ S.filter Nat.Prime, q, by rw [hK]; ring⟩
      rw [hm] at h2
      exact absurd (Nat.le_of_dvd one_pos h2) (by norm_num)
    refine apply_eq_zero_of_good (k := k) a e b good ha1 haeig m hm0 (fun q hq hqm => ⟨hq, ?_, ?_⟩)
    · intro hqS
      have hqK : q ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem _ (Finset.mem_filter.2 ⟨hqS, hq⟩)) _
      exact hq.one_lt.ne' ((hm.coprime_dvd_left hqm).eq_one_of_dvd hqK)
    · intro hqM
      have hqK : q ∣ K := by
        rw [hK]
        exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right hqM 2) _
      exact hq.one_lt.ne' ((hm.coprime_dvd_left hqm).eq_one_of_dvd hqK)

  obtain ⟨G, hG, hGcoef⟩ :=
    CuspForm.exists_hasNebentypus_qCoeff_eq_sum_primeFactors_of_forall_coprime_qCoeff_eq_zero
      M k K hK0 ε f' hf'neb hvan

  have hall : ∀ p : ℕ, ∃ (n : ℕ) (v : Fin n → ℕ → ℂ) (lam : Fin n → ℕ → ℂ) (c : Fin n → ℂ)
      (s : Finset (Fin n)), p ∈ M.primeFactors →
      (∀ i ∈ s, ∀ q : ℕ, q.Prime → ¬ q ∣ M → heckeSeq k e q (v i) = lam i q • v i) ∧
      (∀ i ∈ s, ¬ ∀ q : ℕ, q.Prime → q ∉ S → ¬ q ∣ M → lam i q = qCoeff (⇑g) q) ∧
      (∀ n : ℕ, (if p ∣ n then qCoeff (⇑(G p)) (n / p) else 0) = ∑ i ∈ s, c i * v i n) := by
    intro p
    by_cases hp : p ∈ M.primeFactors
    · obtain ⟨n, v, lam, c, s, h1, h2, h3⟩ := perPrime ε g hg S p hp (G p) (hG p hp)
      exact ⟨n, v, lam, c, s, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, Fin.elim0, ∅, fun h => absurd h hp⟩
  choose n v lam c s hpk using hall

  set T : Finset (Σ p : ℕ, Fin (n p)) := M.primeFactors.sigma s with hT
  let V : (Σ p : ℕ, Fin (n p)) → ℕ → ℂ := fun x => v x.1 x.2
  let C : (Σ p : ℕ, Fin (n p)) → ℂ := fun x => c x.1 x.2
  let 𝒯 : ℕ → (ℕ → ℂ) →ₗ[ℂ] (ℕ → ℂ) := fun q => if good q then heckeSeq k e q else 0
  let β : (Σ p : ℕ, Fin (n p)) → ℕ → ℂ := fun x q => if good q then lam x.1 x.2 q else 0
  let α : ℕ → ℂ := fun q => if good q then b q else 0
  have ha_sum : (∑ x ∈ T, C x • V x) = a := by
    funext m
    rw [Finset.sum_apply, hT, Finset.sum_sigma]
    simp only [Pi.smul_apply, smul_eq_mul, V, C]
    rw [ha]
    simp only
    rw [hGcoef m]
    exact Finset.sum_congr rfl (fun p hp => ((hpk p hp).2.2 m).symm)
  have hv : ∀ x ∈ T, ∀ q, 𝒯 q (V x) = β x q • V x := by
    intro x hx q
    obtain ⟨hp, hi⟩ := Finset.mem_sigma.1 hx
    by_cases hgq : good q
    · simp only [𝒯, β, ite_eq_left hgq]
      exact (hpk x.1 hp).1 x.2 hi q hgq.1 hgq.2.2
    · simp only [𝒯, β, ite_eq_right hgq, LinearMap.zero_apply, zero_smul]
  have haT : ∀ q, 𝒯 q a = α q • a := by
    intro q
    by_cases hgq : good q
    · simp only [𝒯, α, ite_eq_left hgq]
      funext m
      rw [Pi.smul_apply, smul_eq_mul, heckeSeq_apply]
      exact haeig q hgq.1 hgq m
    · simp only [𝒯, α, ite_eq_right hgq, LinearMap.zero_apply, zero_smul]

  have ha0 : a = 0 := by
    by_contra hne
    have hw : ∀ q, 𝒯 q (∑ x ∈ T, C x • V x) = α q • ∑ x ∈ T, C x • V x := by
      intro q; rw [ha_sum]; exact haT q
    have hne' : (∑ x ∈ T, C x • V x) ≠ 0 := by rwa [ha_sum]
    obtain ⟨x, hx, hxβ⟩ := exists_packet_eq 𝒯 V β α T C hv hw hne'
    obtain ⟨hp, hi⟩ := Finset.mem_sigma.1 hx
    apply (hpk x.1 hp).2.1 x.2 hi
    intro q hq hqS hqM
    have := hxβ q
    simp only [β, α, ite_eq_left (show good q from ⟨hq, hqS, hqM⟩)] at this
    exact this

  have hf'0 : f' = 0 := by
    apply eq_of_qCoeff_eq
    intro m
    rw [qCoeff_zero]
    exact congrFun ha0 m
  rw [hf', sub_eq_zero] at hf'0
  exact hf'0

end Main

end MultOnePrimitive

open CongruenceSubgroup
open scoped MatrixGroups

theorem CuspForm.eq_smul_of_isPrimitiveForm_of_qCoeff_hecke_eigen
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k)
    (hg : CuspForm.IsPrimitiveForm ε g) (f : CuspForm (Gamma1 M) k)
    (hf : CuspForm.HasNebentypus ε f) (S : Finset ℕ)
    (hfS : ∀ p : ℕ, p.Prime → p ∉ S → ¬ p ∣ M → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod M) * (p : ℂ) ^ (k - 1) *
              (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff g p * ModularFormClass.qCoeff f n) :
    f = ModularFormClass.qCoeff f 1 • g :=
  MultOnePrimitive.main ε g hg f hf S hfS

end
