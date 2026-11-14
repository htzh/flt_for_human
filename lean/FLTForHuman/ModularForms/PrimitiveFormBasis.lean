/-
  The Atkin--Lehner--Li basis of the cusp-form space from primitive forms.

  * `CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus`:
    the `Γ₁(M)`-space of weight-`k` cusp forms with a fixed nebentypus `ε` has a basis of degeneracy
    images `g(d · τ)` of finitely many pairwise distinct primitive forms `g` of levels `L ∣ M` whose
    characters change level to `ε`; the degeneracies over the divisors of `M / L` are linearly
    independent and span.  The primitive forms are packaged by their level, character and
    coefficients (`NebentypusFormBasis.PF`), the degeneracies by `NebentypusFormBasis.lift`, and the spanning statement
    is the coefficient-linear-functional argument (`NebentypusFormBasis.qCoeffLin`).
  * `CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply`:
    the same basis for the subgroup `Γ_H(M)`, with the classical action of `T_ℓ` (`ℓ ∤ M`), the
    diamond operators and `U_q` (`q ∣ M`) computed on each basis vector — the `T_ℓ` eigenvalue of
    `g` at every `ℓ ∤ M`, the character value of `u ∈ H` raised to level `M`, and the three-branch
    `U_q` recursion (`q ∣ d`, `q ∣ L`, neither).
  * `CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm`: the five commutation laws of these operators
    on `Γ_H(M)`-cusp forms — `T_ℓ` with `T_ℓ'`, `T_ℓ` with `U_q`, `T_ℓ` with the diamonds, `U_q` with
    the diamonds, and the diamonds with each other.

  Transcribed from the pin's proof files (pinned `aa2d8b3`)
  `P2M/Sol/S_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus.lean`
  (277 lines), `S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.lean`
  (492) and `S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.lean` (176), with the statements from the
  wrappers of the same names.  The pin label namespaces are rectified to word names: `DEC1` ->
  `NebentypusFormBasis`, `DCMP` -> `GammaHFormBasis`, `COMMALL` -> `HeckeOperatorCommutation`.  The three files each keep
  their own copy of the short `one_mem_strictPeriods_Gamma1`/`L_ne_zero`/`mul_dvd_div` prelude, which
  the frozen statement set of each file requires.

  spec-pin: Theorems/Thm_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus.lean
  spec-pin: Theorems/Thm_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.lean
  spec-pin: P2M/Sol/S_CuspForm_exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply.lean
  spec-pin: Theorems/Thm_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.lean
  spec-pin: P2M/Sol/S_CuspForm_heckeTLinH_heckeULinH_diamondLinH_comm.lean
-/
import FLTForHuman.ModularForms.Level.DegeneracyString
import FLTForHuman.ModularForms.GammaHDictionary
import FLTForHuman.ModularForms.NebentypusEigenbasis
import FLTForHuman.ModularForms.NebentypusSeparation
import FLTForHuman.ModularForms.NewformDecomposition
import FLTForHuman.ModularForms.PrimitiveFormLevelReduction
import FLTForHuman.ModularForms.HeckeDiagDegeneracy
import FLTForHuman.ModularForms.Gamma1CuspStructure
import FLTForHuman.ModularForms.HeckeULevel
import FLTForHuman.ModularForms.Defs.GammaH
import FLTForHuman.ModularForms.Defs.PrimitiveFormGamma1
import FLTForHuman.ModularForms.Defs.HeckeOperator
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

open CongruenceSubgroup ModularFormClass
namespace NebentypusFormBasis

variable (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M)

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

structure PF where
  L : ℕ
  hL : L ∣ M
  chr : DirichletCharacter ℂ L
  g : CuspForm (Gamma1 L) k
  hprim : CuspForm.IsPrimitiveForm chr g
  hch : DirichletCharacter.changeLevel hL chr = ε

variable {M k ε}

theorem PF.L_ne_zero (p : PF M k ε) : p.L ≠ 0 := fun h => by
  have := p.hL; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this

theorem PF.ext_of (p q : PF M k ε) (hL : p.L = q.L) (hq : ∀ m : ℕ, qCoeff p.g m = qCoeff q.g m) :
    p = q := by
  obtain ⟨L, hL1, chr, g, hprim, hch⟩ := p
  obtain ⟨L', hL1', chr', g', hprim', hch'⟩ := q
  dsimp only at hL hq
  subst hL
  have hg : g = g' := ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma1 L) hq
  subst hg
  have hc : chr = chr' := DirichletCharacter.changeLevel_injective hL1 (hch.trans hch'.symm)
  subst hc
  rfl

def lift (p : PF M k ε) (d : ℕ) : CuspForm (Gamma1 M) k :=
  if h : p.L * d ∣ M then Classical.choose (CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) h p.g)
  else 0

theorem mul_dvd_of_dvd_div (p : PF M k ε) {d : ℕ} (hd : d ∣ M / p.L) : p.L * d ∣ M := by
  have _ := NeZero.ne M
  exact (Nat.dvd_div_iff_mul_dvd p.hL).mp hd

theorem lift_spec (p : PF M k ε) {d : ℕ} (hd : d ∣ M / p.L) :
    (∀ τ : UpperHalfPlane, lift p d τ = p.g (ModularForm.heckeDiagMatrix d • τ)) ∧
    (∀ n : ℕ, qCoeff (lift p d) n = if d ∣ n then qCoeff p.g (n / d) else 0) ∧
    CuspForm.HasNebentypus ε (lift p d) := by
  have h := mul_dvd_of_dvd_div p hd
  have hs := Classical.choose_spec (CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) h p.g)
  have hl : lift p d = Classical.choose (CuspForm.exists_degeneracy_gamma1_hasNebentypus (k := k) h p.g) :=
    dite_eq_left h
  rw [hl]
  refine ⟨hs.1, hs.2.1, ?_⟩
  have := hs.2.2 p.chr p.hprim.isEigenformWith.hasNebentypus
  rwa [show DirichletCharacter.changeLevel (dvd_of_mul_right_dvd h) p.chr = ε from p.hch] at this

theorem one_dvd_div (p : PF M k ε) : 1 ∣ M / p.L := by
  have _ := NeZero.ne M
  exact one_dvd _

theorem sep (p q : PF M k ε) (hpq : p ≠ q) :
    ∃ r : ℕ, r.Prime ∧ ¬ r ∣ M ∧ qCoeff p.g r ≠ qCoeff q.g r := by
  classical
  by_contra hall
  push Not at hall
  have : NeZero p.L := ⟨p.L_ne_zero⟩
  have : NeZero q.L := ⟨q.L_ne_zero⟩
  have ha : ∀ r : ℕ, r.Prime → r ∉ M.primeFactors → qCoeff p.g r = qCoeff q.g r := fun r hr hrS =>
    hall r hr (fun h => hrS (Nat.mem_primeFactors.mpr ⟨hr, h, NeZero.ne M⟩))
  have hε : ∀ r : ℕ, r.Prime → r ∉ M.primeFactors → p.chr (r : ZMod p.L) = q.chr (r : ZMod q.L) := by
    intro r hr hrS
    have hrM : ¬ r ∣ M := fun h => hrS (Nat.mem_primeFactors.mpr ⟨hr, h, NeZero.ne M⟩)
    have hu : IsUnit (r : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hr).mpr hrM
    have := congrArg (fun χ : DirichletCharacter ℂ M => χ (hu.unit : ZMod M)) (p.hch.trans q.hch.symm)
    rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      IsUnit.unit_spec, ZMod.cast_natCast p.hL, ZMod.cast_natCast q.hL] at this
    exact this
  have key := CuspForm.IsPrimitiveForm.level_eq_and_qCoeff_eq_of_forall_prime_notMem_qCoeff_eq
    p.hprim q.hprim M.primeFactors ha hε
  exact hpq (PF.ext_of p q key.1 key.2)

theorem div_ne_zero (p : PF M k ε) : M / p.L ≠ 0 :=
  Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) p.hL)
    (Nat.pos_of_ne_zero p.L_ne_zero))

theorem li_enum {n : ℕ} (P : Fin n → PF M k ε) (hPinj : Function.Injective P) :
    LinearIndependent ℂ (fun i => lift (P i) 1) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  have hNZ : ∀ i, NeZero ((fun i => (P i).L) i) := fun i => ⟨(P i).L_ne_zero⟩
  have hcollapse : ∀ i : Fin n,
      (∑ d ∈ Nat.divisors (M / (P i).L), (if d = 1 then c i else 0) • lift (P i) d) = c i • lift (P i) 1 := by
    intro i
    rw [Finset.sum_eq_single_of_mem 1 (Nat.one_mem_divisors.mpr (div_ne_zero (P i)))]
    · rw [ite_eq_left rfl]
    · intro d _ hd1; rw [ite_eq_right hd1, zero_smul]
  have hsum : (∑ i, ∑ d ∈ Nat.divisors (M / (P i).L), (if d = 1 then c i else 0) • lift (P i) d) = 0 := by
    rw [← hc]
    exact Finset.sum_congr rfl fun i _ => hcollapse i
  have hM4a := CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne M k n
    (fun i => (P i).L) (fun i => (P i).hL) (fun i => (P i).chr) (fun i => (P i).g)
    (fun i => (P i).hprim.isEigenformWith)
    (fun i j hij => sep (P i) (P j) (fun h => hij (hPinj h)))
    (fun i d => lift (P i) d) (fun i d hd => (lift_spec (P i) hd).1) (fun i d => if d = 1 then c i else 0) hsum
  have h1 := hM4a i₀ 1 (Nat.one_mem_divisors.mpr (div_ne_zero (P i₀)))
  simpa using h1

theorem linearIndependent_lift_one : LinearIndependent ℂ (fun p : PF M k ε => lift p 1) := by
  classical
  rw [linearIndependent_iff_finset_linearIndependent]
  intro s
  let eqv : ↥s ≃ Fin s.card := s.equivFin
  have h := li_enum (fun i => ((eqv.symm i : ↥s) : PF M k ε))
    (fun i j hij => eqv.symm.injective (Subtype.ext hij))
  have : (fun i => lift (((eqv.symm i : ↥s) : PF M k ε)) 1) =
      ((fun p : PF M k ε => lift p 1) ∘ (Subtype.val : ↥s → PF M k ε)) ∘ eqv.symm := rfl
  rw [this, linearIndependent_equiv] at h
  exact h

theorem finite_PF : Finite (PF M k ε) := by
  obtain ⟨n, b, -⟩ := CuspForm.exists_basis_hasNebentypus_qCoeff_hecke_eigen M k
  have : Module.Finite ℂ (CuspForm (Gamma1 M) k) := Module.Finite.of_basis b
  exact LinearIndependent.finite_of_isNoetherian linearIndependent_lift_one

end NebentypusFormBasis

namespace NebentypusFormBasis

variable {M : ℕ} [NeZero M] {k : ℤ} {ε : DirichletCharacter ℂ M}

theorem qCoeff_def (f : UpperHalfPlane → ℂ) (n : ℕ) :
    qCoeff f n = (UpperHalfPlane.qExpansion 1 f).coeff n := rfl

def qCoeffLin (N : ℕ) (k : ℤ) (m : ℕ) : CuspForm (Gamma1 N) k →ₗ[ℂ] ℂ where
  toFun F := qCoeff F m
  map_add' F G := by
    rw [qCoeff_def, qCoeff_def, qCoeff_def, FunLike.coe_add,
      ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma1 N) F G]
    simp
  map_smul' a F := by
    rw [qCoeff_def, qCoeff_def, FunLike.coe_smul,
      ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma1 N) a F]
    simp

theorem qCoeffLin_apply (N : ℕ) (k : ℤ) (m : ℕ) (F : CuspForm (Gamma1 N) k) :
    qCoeffLin N k m F = qCoeff F m := rfl

theorem main (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k),
      (∀ i, CuspForm.IsPrimitiveForm (εL i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, DirichletCharacter.changeLevel (hL i) (εL i) = ε) ∧
      (∀ (L' : ℕ) [NeZero L'] (hL' : L' ∣ M) (ε' : DirichletCharacter ℂ L')
          (g' : CuspForm (CongruenceSubgroup.Gamma1 L') k),
        CuspForm.IsPrimitiveForm ε' g' → DirichletCharacter.changeLevel hL' ε' = ε →
        ∃ i, L i = L' ∧ ∀ m : ℕ, ModularFormClass.qCoeff (g i) m = ModularFormClass.qCoeff g' m) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
        CuspForm.HasNebentypus ε (G i d)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      (∀ f : CuspForm (CongruenceSubgroup.Gamma1 M) k, CuspForm.HasNebentypus ε f →
        f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))) := by
  classical
  have : Finite (PF M k ε) := finite_PF
  have : Fintype (PF M k ε) := Fintype.ofFinite _
  let n : ℕ := Fintype.card (PF M k ε)
  let eqv : PF M k ε ≃ Fin n := Fintype.equivFin _
  let P : Fin n → PF M k ε := fun i => eqv.symm i
  have hPinj : Function.Injective P := eqv.symm.injective
  have hPsurj : Function.Surjective P := eqv.symm.surjective
  refine ⟨n, fun i => (P i).L, fun i => (P i).hL, fun i => (P i).chr, fun i => (P i).g,
    fun i d => lift (P i) d, fun i => (P i).hprim, ?_, fun i => (P i).hch, ?_, ?_, ?_, ?_⟩
  ·
    intro i j hij
    by_contra h
    push Not at h
    exact hij (hPinj (PF.ext_of _ _ h.1 h.2))
  ·
    intro L' _ hL' ε' g' hprim' hch'
    obtain ⟨i, hi⟩ := hPsurj ⟨L', hL', ε', g', hprim', hch'⟩
    refine ⟨i, ?_, ?_⟩
    · change (P i).L = L'
      rw [hi]
    · intro m
      change qCoeff (⇑(P i).g) m = qCoeff (⇑g') m
      rw [hi]
  ·
    intro i d hd
    exact ⟨(lift_spec (P i) hd).1, (lift_spec (P i) hd).2.2⟩
  ·
    have hNZ : ∀ i, NeZero ((fun i => (P i).L) i) := fun i => ⟨(P i).L_ne_zero⟩
    rw [Fintype.linearIndependent_iff]
    intro c hc x
    let c' : Fin n → ℕ → ℂ := fun i d => if h : d ∈ Nat.divisors (M / (P i).L) then c ⟨i, ⟨d, h⟩⟩ else 0
    have hsum : (∑ i, ∑ d ∈ Nat.divisors (M / (P i).L), c' i d • lift (P i) d) = 0 := by
      rw [← hc, Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_coe_sort]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp only [c', dite_eq_left d.2]
    have hM4a := CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne M k n
      (fun i => (P i).L) (fun i => (P i).hL) (fun i => (P i).chr) (fun i => (P i).g)
      (fun i => (P i).hprim.isEigenformWith)
      (fun i j hij => sep (P i) (P j) (fun h => hij (hPinj h)))
      (fun i d => lift (P i) d) (fun i d hd => (lift_spec (P i) hd).1) c' hsum
    have := hM4a x.1 x.2 x.2.2
    simp only [c', dite_eq_left x.2.2] at this
    exact this
  ·
    intro f hf
    obtain ⟨n', M', d', hM', εM', g', c, hprops, hcoeff⟩ :=
      CuspForm.exists_qCoeff_eq_sum_isPrimitiveForm_of_hasNebentypus M k ε f hf
    let q : Fin n' → PF M k ε := fun j =>
      ⟨M' j, dvd_of_mul_right_dvd (hM' j), εM' j, g' j, (hprops j).1, (hprops j).2⟩
    have hd' : ∀ j, d' j ∣ M / (q j).L := fun j =>
      (Nat.dvd_div_iff_mul_dvd (dvd_of_mul_right_dvd (hM' j))).mpr (hM' j)
    set F : CuspForm (Gamma1 M) k := ∑ j, c j • lift (q j) (d' j) with hF
    have hfF : f = F := by
      apply ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma1 M)
      intro m
      rw [hcoeff m, ← qCoeffLin_apply M k m F, hF, map_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul, qCoeffLin_apply, (lift_spec (q j) (hd' j)).2.1 m, smul_eq_mul]
    rw [hfF, hF]
    refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    obtain ⟨i, hi⟩ := hPsurj (q j)
    have hLi : (P i).L = (q j).L := by rw [hi]
    refine ⟨⟨i, ⟨d' j, Nat.mem_divisors.mpr ⟨by change d' j ∣ M / (P i).L; rw [hLi]; exact hd' j, div_ne_zero (P i)⟩⟩⟩, ?_⟩
    change lift (P i) (d' j) = lift (q j) (d' j)
    rw [hi]

end NebentypusFormBasis


open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus
    (M : ℕ) [NeZero M] (k : ℤ) (ε : DirichletCharacter ℂ M) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (εL : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CongruenceSubgroup.Gamma1 M) k),
      (∀ i, CuspForm.IsPrimitiveForm (εL i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, DirichletCharacter.changeLevel (hL i) (εL i) = ε) ∧
      (∀ (L' : ℕ) [NeZero L'] (hL' : L' ∣ M) (ε' : DirichletCharacter ℂ L')
          (g' : CuspForm (CongruenceSubgroup.Gamma1 L') k),
        CuspForm.IsPrimitiveForm ε' g' → DirichletCharacter.changeLevel hL' ε' = ε →
        ∃ i, L i = L' ∧ ∀ m : ℕ, ModularFormClass.qCoeff (g i) m = ModularFormClass.qCoeff g' m) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
        CuspForm.HasNebentypus ε (G i d)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      (∀ f : CuspForm (CongruenceSubgroup.Gamma1 M) k, CuspForm.HasNebentypus ε f →
        f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))) := by
  exact NebentypusFormBasis.main M k ε

namespace GammaHFormBasis

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

theorem one_mem_strictPeriods_Gamma1 (N : ℕ) :
    (1 : ℝ) ∈ ((Gamma1 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

theorem denom_eq (A : SL(2, ℤ)) (τ : UpperHalfPlane) :
    UpperHalfPlane.denom (A : GL (Fin 2) ℝ) τ = ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) := by
  simp [UpperHalfPlane.denom]

variable {M k}

theorem slash_eq_smul_of_hasNebentypus {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} (hg : CuspForm.HasNebentypus ε g)
    (A : SL(2, ℤ)) (hA0 : A ∈ Gamma0 M) :
    (⇑g) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ A : GL (Fin 2) ℝ)) = ε ((A 1 1 : ℤ) : ZMod M) • ⇑g := by
  have _ := NeZero.ne M
  funext τ
  show ((⇑g) ∣[k] A) τ = _
  rw [ModularForm.SL_slash_apply, hg A hA0 τ, Pi.smul_apply, smul_eq_mul]
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  rw [denom_eq, mul_assoc, mul_assoc, mul_comm (_ ^ k), mul_assoc, ← zpow_add₀ hne, neg_add_cancel,
    zpow_zero, mul_one]

theorem hasNebentypus_of_slash_eq_smul {ε : DirichletCharacter ℂ M}
    {g : CuspForm (Gamma1 M) k} {F : UpperHalfPlane → ℂ} (hF : F = ⇑g)
    (h : ∀ σ : Gamma0 M, F ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
      ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • F) :
    CuspForm.HasNebentypus ε g := by
  have _ := NeZero.ne M
  intro A hA0 τ
  have := congrFun (h ⟨A, hA0⟩) τ
  rw [hF] at this
  change ((⇑g) ∣[k] A) τ = _ at this
  rw [ModularForm.SL_slash_apply, Pi.smul_apply, smul_eq_mul, denom_eq] at this
  have hne : ((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ) ≠ 0 := by
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  have hz : (((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ)) ^ (-k) ≠ 0 := zpow_ne_zero _ hne

  have := congrArg (fun z => z * (((A 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((A 1 1 : ℤ) : ℂ)) ^ k) this
  simp only at this
  rw [mul_assoc, ← zpow_add₀ hne, neg_add_cancel, zpow_zero, mul_one] at this
  rw [this]; ring

end GammaHFormBasis

namespace GammaHFormBasis

variable {M : ℕ} [NeZero M] {k : ℤ}

theorem nebentypus_unique {L : ℕ} [NeZero L] {ε₁ ε₂ : DirichletCharacter ℂ L} {g : CuspForm (Gamma1 L) k}
    (hg : g ≠ 0) (h₁ : CuspForm.HasNebentypus ε₁ g) (h₂ : CuspForm.HasNebentypus ε₂ g) : ε₁ = ε₂ := by
  have hτ : ∃ τ : UpperHalfPlane, g τ ≠ 0 := by
    by_contra h
    push Not at h
    exact hg (DFunLike.ext _ _ h)
  obtain ⟨τ, hτ⟩ := hτ
  apply MulChar.ext
  intro u
  obtain ⟨γ, hγ⟩ := CohCarrier.gamma0Units_surjective L u
  have e1 := h₁ (γ : SL(2, ℤ)) γ.2 τ
  have e2 := h₂ (γ : SL(2, ℤ)) γ.2 τ
  rw [e1] at e2
  have hd : (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod L) = (u : ZMod L) := by
    rw [← hγ, CohCarrier.val_gamma0Units]; rfl
  rw [hd] at e2
  have hne : ((((γ : SL(2, ℤ)) 1 0 : ℤ) : ℂ) * (τ : ℂ) + (((γ : SL(2, ℤ)) 1 1 : ℤ) : ℂ)) ^ k * g τ ≠ 0 := by
    refine mul_ne_zero (zpow_ne_zero _ ?_) hτ
    rw [← denom_eq]; exact UpperHalfPlane.denom_ne_zero _ _
  exact mul_right_cancel₀ hne e2

variable (M k)

structure Dat where
  n : DirichletCharacter ℂ M → ℕ
  L : (ε : DirichletCharacter ℂ M) → Fin (n ε) → ℕ
  hL : ∀ ε i, L ε i ∣ M
  chr : (ε : DirichletCharacter ℂ M) → (i : Fin (n ε)) → DirichletCharacter ℂ (L ε i)
  g : (ε : DirichletCharacter ℂ M) → (i : Fin (n ε)) → CuspForm (Gamma1 (L ε i)) k
  G : (ε : DirichletCharacter ℂ M) → Fin (n ε) → ℕ → CuspForm (Gamma1 M) k
  hprim : ∀ ε i, CuspForm.IsPrimitiveForm (chr ε i) (g ε i)
  hdist : ∀ ε i j, i ≠ j → L ε i ≠ L ε j ∨ ∃ m : ℕ, qCoeff (g ε i) m ≠ qCoeff (g ε j) m
  hch : ∀ ε i, DirichletCharacter.changeLevel (hL ε i) (chr ε i) = ε
  hG : ∀ ε i (d : ℕ), d ∣ M / L ε i →
    (∀ τ : UpperHalfPlane, G ε i d τ = g ε i (ModularForm.heckeDiagMatrix d • τ)) ∧
    CuspForm.HasNebentypus ε (G ε i d)
  hli : ∀ ε, LinearIndependent ℂ (fun x : (Σ i : Fin (n ε), ↥(Nat.divisors (M / L ε i))) => G ε x.1 (x.2 : ℕ))
  hspan : ∀ ε (f : CuspForm (Gamma1 M) k), CuspForm.HasNebentypus ε f →
    f ∈ Submodule.span ℂ (Set.range fun x : (Σ i : Fin (n ε), ↥(Nat.divisors (M / L ε i))) => G ε x.1 (x.2 : ℕ))

theorem nonempty_dat : Nonempty (Dat M k) := by
  choose n L hL chr g G hprim hdist hch _hcomp hG hli hspan using
    fun ε : DirichletCharacter ℂ M =>
      CuspForm.exists_isPrimitiveForm_linearIndependent_degeneracy_and_mem_span_of_hasNebentypus M k ε
  exact ⟨⟨n, L, hL, chr, g, G, hprim, hdist, hch, hG, hli, hspan⟩⟩

variable {M k}
variable (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

def EH : Finset (DirichletCharacter ℂ M) := by
  classical
  exact Finset.univ.filter (fun ε => ∀ u : (ZMod M)ˣ, u ∈ H → ε (u : ZMod M) = 1)

theorem mem_EH {ε : DirichletCharacter ℂ M} : ε ∈ EH H ↔ ∀ u : (ZMod M)ˣ, u ∈ H → ε (u : ZMod M) = 1 := by
  classical
  simp [EH]

abbrev Idx : Type := Σ ε : ↥(EH H), Fin (𝒟.n (ε : DirichletCharacter ℂ M))

abbrev chrOf (x : Idx H 𝒟) : DirichletCharacter ℂ M := (x.1 : DirichletCharacter ℂ M)
abbrev LOf (x : Idx H 𝒟) : ℕ := 𝒟.L (chrOf H 𝒟 x) x.2

theorem chrOf_mem (x : Idx H 𝒟) : ∀ u : (ZMod M)ˣ, u ∈ H → chrOf H 𝒟 x (u : ZMod M) = 1 :=
  (mem_EH H).mp x.1.2

def GH (x : Idx H 𝒟) (d : ℕ) : CuspForm (CohCarrier.GammaH M H) k :=
  if hd : d ∣ M / LOf H 𝒟 x then
    Classical.choose (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k (chrOf H 𝒟 x) (chrOf_mem H 𝒟 x)
      (𝒟.G (chrOf H 𝒟 x) x.2 d) ((𝒟.hG (chrOf H 𝒟 x) x.2 d hd).2))
  else 0

theorem coe_GH (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    (⇑(GH H 𝒟 x d) : UpperHalfPlane → ℂ) = ⇑(𝒟.G (chrOf H 𝒟 x) x.2 d) := by
  rw [GH, dite_eq_left hd]
  exact Classical.choose_spec (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k (chrOf H 𝒟 x)
    (chrOf_mem H 𝒟 x) (𝒟.G (chrOf H 𝒟 x) x.2 d) ((𝒟.hG (chrOf H 𝒟 x) x.2 d hd).2))

theorem LOf_ne_zero (x : Idx H 𝒟) : LOf H 𝒟 x ≠ 0 := fun h => by
  have := 𝒟.hL (chrOf H 𝒟 x) x.2; rw [show 𝒟.L (chrOf H 𝒟 x) x.2 = 0 from h, zero_dvd_iff] at this
  exact NeZero.ne M this

theorem div_ne_zero (x : Idx H 𝒟) : M / LOf H 𝒟 x ≠ 0 :=
  Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL _ _))
    (Nat.pos_of_ne_zero (LOf_ne_zero H 𝒟 x)))

theorem dist (x y : Idx H 𝒟) (hxy : x ≠ y) :
    LOf H 𝒟 x ≠ LOf H 𝒟 y ∨ ∃ m : ℕ, qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) m ≠ qCoeff (𝒟.g (chrOf H 𝒟 y) y.2) m := by
  obtain ⟨ε, i⟩ := x
  obtain ⟨ε', j⟩ := y
  by_cases hε : ε = ε'
  · subst hε
    have hij : i ≠ j := fun h => hxy (by subst h; rfl)
    exact 𝒟.hdist _ i j hij
  ·
    by_contra h
    push Not at h
    obtain ⟨hL, hq⟩ := h
    apply hε
    apply Subtype.ext

    change 𝒟.L (ε : DirichletCharacter ℂ M) i = 𝒟.L (ε' : DirichletCharacter ℂ M) j at hL
    have key : ∀ (L₁ : ℕ) (h₁ : L₁ ∣ M) (c₁ : DirichletCharacter ℂ L₁) (g₁ : CuspForm (Gamma1 L₁) k)
        (L₂ : ℕ) (h₂ : L₂ ∣ M) (c₂ : DirichletCharacter ℂ L₂) (g₂ : CuspForm (Gamma1 L₂) k),
        CuspForm.IsPrimitiveForm c₁ g₁ → CuspForm.IsPrimitiveForm c₂ g₂ → L₁ = L₂ →
        (∀ m : ℕ, qCoeff g₁ m = qCoeff g₂ m) →
        DirichletCharacter.changeLevel h₁ c₁ = DirichletCharacter.changeLevel h₂ c₂ := by
      intro L₁ h₁ c₁ g₁ L₂ h₂ c₂ g₂ hp₁ hp₂ hL12 hq12
      subst hL12
      have : NeZero L₁ := ⟨fun h => by rw [h, zero_dvd_iff] at h₁; exact NeZero.ne M h₁⟩
      have hg : g₁ = g₂ := ModularFormClass.eq_of_forall_qCoeff_eq (one_mem_strictPeriods_Gamma1 L₁) hq12
      subst hg
      have hne : g₁ ≠ 0 := by
        intro h0
        have := hp₁.isEigenformWith.qCoeff_one
        rw [h0] at this
        simp [qCoeff, UpperHalfPlane.qExpansion_zero] at this
      rw [nebentypus_unique hne hp₁.isEigenformWith.hasNebentypus hp₂.isEigenformWith.hasNebentypus]
    have := key _ (𝒟.hL _ i) _ _ _ (𝒟.hL _ j) _ _ (𝒟.hprim _ i) (𝒟.hprim _ j) hL hq
    rwa [𝒟.hch, 𝒟.hch] at this

end GammaHFormBasis

namespace GammaHFormBasis

variable {M : ℕ} [NeZero M] {k : ℤ} (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

theorem hasNebentypus_zero {N : ℕ} (ε : DirichletCharacter ℂ N) :
    CuspForm.HasNebentypus ε (0 : CuspForm (Gamma1 N) k) := by
  intro γ _ τ; simp

theorem hasNebentypus_add {N : ℕ} {ε : DirichletCharacter ℂ N} {f g : CuspForm (Gamma1 N) k}
    (hf : CuspForm.HasNebentypus ε f) (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.HasNebentypus ε (f + g) := by
  intro γ hγ τ
  simp only [add_apply, hf γ hγ τ, hg γ hγ τ]
  ring

theorem hasNebentypus_smul {N : ℕ} {ε : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) k} (c : ℂ)
    (hf : CuspForm.HasNebentypus ε f) : CuspForm.HasNebentypus ε (c • f) := by
  intro γ hγ τ
  simp only [smul_apply, smul_eq_mul, hf γ hγ τ]
  ring

theorem hasNebentypus_sum {N : ℕ} {ε : DirichletCharacter ℂ N} {ι : Type*} (s : Finset ι)
    (f : ι → CuspForm (Gamma1 N) k) (hf : ∀ i ∈ s, CuspForm.HasNebentypus ε (f i)) :
    CuspForm.HasNebentypus ε (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hasNebentypus_zero ε
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact hasNebentypus_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem coe_sum {Γ : Subgroup (GL (Fin 2) ℝ)} {ι : Type*} (s : Finset ι) (f : ι → CuspForm Γ k) :
    (⇑(∑ i ∈ s, f i) : UpperHalfPlane → ℂ) = ∑ i ∈ s, ⇑(f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

def Fof (c : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) → ℂ) (e : ↥(EH H)) : CuspForm (Gamma1 M) k :=
  ∑ i : Fin (𝒟.n (e : DirichletCharacter ℂ M)),
    ∑ dd : ↥(Nat.divisors (M / 𝒟.L (e : DirichletCharacter ℂ M) i)),
      c ⟨⟨e, i⟩, dd⟩ • 𝒟.G (e : DirichletCharacter ℂ M) i (dd : ℕ)

theorem hasNebentypus_Fof (c : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) → ℂ) (e : ↥(EH H)) :
    CuspForm.HasNebentypus (e : DirichletCharacter ℂ M) (Fof H 𝒟 c e) := by
  unfold Fof
  refine hasNebentypus_sum _ _ fun i _ => hasNebentypus_sum _ _ fun dd _ => hasNebentypus_smul _ ?_
  exact (𝒟.hG _ i dd (Nat.dvd_of_mem_divisors dd.2)).2

theorem linearIndependent :
    LinearIndependent ℂ (fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 y.1 (y.2 : ℕ)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc y

  let gB : DirichletCharacter ℂ M → CuspForm (CohCarrier.GammaH M H) k := fun ε =>
    if h : ε ∈ EH H then
      Classical.choose (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k ε ((mem_EH H).mp h)
        (Fof H 𝒟 c ⟨ε, h⟩) (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩))
    else 0
  have hgB : ∀ (ε) (h : ε ∈ EH H), (⇑(gB ε) : UpperHalfPlane → ℂ) = ⇑(Fof H 𝒟 c ⟨ε, h⟩) := by
    intro ε h
    simp only [gB, dite_eq_left h]
    exact Classical.choose_spec (CuspForm.exists_gammaH_coe_eq_of_hasNebentypus M H k ε ((mem_EH H).mp h)
      (Fof H 𝒟 c ⟨ε, h⟩) (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩))
  have hslash : ∀ ε ∈ EH H, ∀ σ : Gamma0 M,
      ⇑(gB ε) ∣[k] ((Matrix.SpecialLinearGroup.mapGL ℝ (σ : SL(2, ℤ)) : GL (Fin 2) ℝ)) =
        ε (((σ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) • ⇑(gB ε) := by
    intro ε h σ
    rw [hgB ε h]
    exact slash_eq_smul_of_hasNebentypus (hasNebentypus_Fof H 𝒟 c ⟨ε, h⟩) _ σ.2
  have hsum0 : (∑ ε ∈ EH H, ⇑(gB ε)) = 0 := by
    have h1 : (∑ ε ∈ EH H, ⇑(gB ε)) = ∑ e : ↥(EH H), ⇑(Fof H 𝒟 c e) := by
      rw [← Finset.sum_coe_sort]
      exact Finset.sum_congr rfl fun e _ => hgB e e.2
    have h2 : (⇑(∑ y, c y • GH H 𝒟 y.1 (y.2 : ℕ)) : UpperHalfPlane → ℂ) =
        ∑ y, c y • ⇑(𝒟.G (chrOf H 𝒟 y.1) y.1.2 (y.2 : ℕ)) := by
      rw [coe_sum Finset.univ (fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) =>
        c y • GH H 𝒟 y.1 (y.2 : ℕ))]
      exact Finset.sum_congr rfl fun y _ => by
        rw [FunLike.coe_smul, coe_GH H 𝒟 y.1 (Nat.dvd_of_mem_divisors y.2.2)]
    have h3 : (∑ e : ↥(EH H), (⇑(Fof H 𝒟 c e) : UpperHalfPlane → ℂ)) =
        ∑ y, c y • ⇑(𝒟.G (chrOf H 𝒟 y.1) y.1.2 (y.2 : ℕ)) := by
      simp only [Fof, coe_sum, FunLike.coe_smul, Fintype.sum_sigma]
    rw [h1, h3, ← h2, hc, FunLike.coe_zero]
  have hB := (CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH M H k).2 (EH H) gB hslash hsum0

  have hF : ∀ e : ↥(EH H), Fof H 𝒟 c e = 0 := by
    intro e
    apply DFunLike.ext'
    rw [← hgB e e.2, hB e e.2]
    rfl

  obtain ⟨⟨e, i⟩, dd⟩ := y
  have hli := (Fintype.linearIndependent_iff.mp (𝒟.hli (e : DirichletCharacter ℂ M)))
    (fun z => c ⟨⟨e, z.1⟩, z.2⟩) ?_ ⟨i, dd⟩
  · exact hli
  · have := hF e
    rw [Fof] at this
    simpa only [Fintype.sum_sigma] using this

theorem mem_span (f : CuspForm (CohCarrier.GammaH M H) k) :
    f ∈ Submodule.span ℂ (Set.range fun y : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) =>
      GH H 𝒟 y.1 (y.2 : ℕ)) := by
  classical
  obtain ⟨s, fε, hH, hslash, hsum⟩ := (CuspForm.exists_finset_dirichlet_sum_eq_and_independent_of_gammaH M H k).1 f
  have hf : f = ∑ ε ∈ s, fε ε := by
    apply DFunLike.ext'
    rw [coe_sum]; exact hsum
  rw [hf]
  refine Submodule.sum_mem _ fun ε hε => ?_

  obtain ⟨g₁, hg₁⟩ := CuspForm.exists_gamma1_coe_eq_of_gammaH M H k (fε ε)
  have hneb : CuspForm.HasNebentypus ε g₁ := hasNebentypus_of_slash_eq_smul hg₁.symm (hslash ε hε)
  let e : ↥(EH H) := ⟨ε, (mem_EH H).mpr (hH ε hε)⟩
  have hsp := 𝒟.hspan ε g₁ hneb
  rw [Submodule.mem_span_range_iff_exists_fun] at hsp
  obtain ⟨a, ha⟩ := hsp
  have hfe : fε ε = ∑ z : (Σ i : Fin (𝒟.n ε), ↥(Nat.divisors (M / 𝒟.L ε i))), a z • GH H 𝒟 ⟨e, z.1⟩ (z.2 : ℕ) := by
    apply DFunLike.ext'
    rw [coe_sum, ← hg₁, ← ha, coe_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [FunLike.coe_smul, FunLike.coe_smul, coe_GH H 𝒟 ⟨e, z.1⟩ (Nat.dvd_of_mem_divisors z.2.2)]
  rw [hfe]
  refine Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨⟨e, z.1⟩, z.2⟩, rfl⟩)

end GammaHFormBasis

namespace GammaHFormBasis

variable {M : ℕ} [NeZero M] {k : ℤ} (H : Subgroup (ZMod M)ˣ) (𝒟 : Dat M k)

theorem chr_natCast_eq (x : Idx H 𝒟) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    chrOf H 𝒟 x (ℓ : ZMod M) = 𝒟.chr (chrOf H 𝒟 x) x.2 (ℓ : ZMod (LOf H 𝒟 x)) := by
  have hu : IsUnit (ℓ : ZMod M) := (ZMod.isUnit_prime_iff_not_dvd hℓ).mpr hℓM
  have := congrArg (fun χ : DirichletCharacter ℂ M => χ (hu.unit : ZMod M)) (𝒟.hch (chrOf H 𝒟 x) x.2)
  rw [DirichletCharacter.changeLevel_eq_cast_of_dvd, IsUnit.unit_spec, ZMod.cast_natCast (𝒟.hL _ _)] at this
  exact this.symm

theorem heckeT_GH {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CuspForm.heckeTLinH k hℓ hℓM (GH H 𝒟 x d) = qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) ℓ • GH H 𝒟 x d := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : NeZero (LOf H 𝒟 x) := ⟨LOf_ne_zero H 𝒟 x⟩
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).2.1 ℓ hℓ hℓM
  have hM4b := CuspForm.IsEigenformWith.heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul M k
    (𝒟.hL _ _) (𝒟.hprim (chrOf H 𝒟 x) x.2).isEigenformWith (𝒟.G (chrOf H 𝒟 x) x.2)
    (fun d hd => (hG d hd).1) hℓ hℓM hd
  apply DFunLike.ext'
  rw [hM2c, FunLike.coe_smul, coe_GH H 𝒟 x hd, ← hM4b, chr_natCast_eq H 𝒟 x hℓ hℓM]

theorem diamond_GH (u : (ZMod M)ˣ) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    CuspForm.diamondLinH k u (GH H 𝒟 x d) =
      DirichletCharacter.changeLevel (𝒟.hL _ _) (𝒟.chr (chrOf H 𝒟 x) x.2) (u : ZMod M) • GH H 𝒟 x d := by
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).1 u
  apply DFunLike.ext'
  rw [hM2c, FunLike.coe_smul, coe_GH H 𝒟 x hd, 𝒟.hch]

theorem mul_dvd_div {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : Idx H 𝒟) (hqL : ¬ q ∣ LOf H 𝒟 x) {d : ℕ}
    (hd : d ∣ M / LOf H 𝒟 x) (hqd : ¬ q ∣ d) : d * q ∣ M / LOf H 𝒟 x := by
  have hcop : Nat.Coprime d q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
  refine hcop.mul_dvd_of_dvd_of_dvd hd ?_
  have hqML : Nat.Coprime q (LOf H 𝒟 x) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqL
  have : q ∣ LOf H 𝒟 x * (M / LOf H 𝒟 x) := by rw [Nat.mul_div_cancel' (𝒟.hL _ _)]; exact hqM
  exact hqML.dvd_of_dvd_mul_left this

theorem heckeU_GH {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (x : Idx H 𝒟) {d : ℕ} (hd : d ∣ M / LOf H 𝒟 x) :
    (q ∣ d → CuspForm.heckeULinH k q (GH H 𝒟 x d) = GH H 𝒟 x (d / q)) ∧
    (¬ q ∣ d → q ∣ LOf H 𝒟 x → CuspForm.heckeULinH k q (GH H 𝒟 x d) =
      qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) q • GH H 𝒟 x d) ∧
    (¬ q ∣ d → ¬ q ∣ LOf H 𝒟 x → CuspForm.heckeULinH k q (GH H 𝒟 x d) =
      qCoeff (𝒟.g (chrOf H 𝒟 x) x.2) q • GH H 𝒟 x d -
        (𝒟.chr (chrOf H 𝒟 x) x.2 (q : ZMod (LOf H 𝒟 x)) * (q : ℂ) ^ (k - 1)) • GH H 𝒟 x (d * q)) := by
  have : NeZero (LOf H 𝒟 x) := ⟨LOf_ne_zero H 𝒟 x⟩
  have hG := 𝒟.hG (chrOf H 𝒟 x) x.2
  have hM2c := (CuspForm.coe_diamondLinH_and_coe_heckeTLinH_and_coe_heckeULinH_of_hasNebentypus M H k
    (chrOf H 𝒟 x) (GH H 𝒟 x d) (𝒟.G (chrOf H 𝒟 x) x.2 d) (coe_GH H 𝒟 x hd) (hG d hd).2).2.2 q hq hqM
  have hM4c := CuspForm.IsEigenformWith.heckeU_degeneracy_of_dvd_level M k (𝒟.hL _ _)
    (𝒟.hprim (chrOf H 𝒟 x) x.2).isEigenformWith (𝒟.G (chrOf H 𝒟 x) x.2) (fun d hd => (hG d hd).1) hq hqM hd
  refine ⟨fun hqd => ?_, fun hqd hqL => ?_, fun hqd hqL => ?_⟩
  · apply DFunLike.ext'
    rw [hM2c, hM4c.1 hqd, coe_GH H 𝒟 x ((Nat.div_dvd_of_dvd hqd).trans hd)]
  · apply DFunLike.ext'
    rw [hM2c, hM4c.2.1 hqd hqL, FunLike.coe_smul, coe_GH H 𝒟 x hd]
  · apply DFunLike.ext'
    rw [hM2c, hM4c.2.2 hqd hqL, FunLike.coe_sub, FunLike.coe_smul, FunLike.coe_smul,
      coe_GH H 𝒟 x hd, coe_GH H 𝒟 x (mul_dvd_div H 𝒟 hq hqM x hqL hd hqd)]

theorem main (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) := by
  classical
  obtain ⟨𝒟⟩ := nonempty_dat M k
  let N : ℕ := Fintype.card (Idx H 𝒟)
  let e : Idx H 𝒟 ≃ Fin N := Fintype.equivFin _
  let X : Fin N → Idx H 𝒟 := fun y => e.symm y
  have hXinj : Function.Injective X := e.symm.injective
  refine ⟨N, fun y => LOf H 𝒟 (X y), fun y => 𝒟.hL _ _, fun y => 𝒟.chr (chrOf H 𝒟 (X y)) (X y).2,
    fun y => 𝒟.g (chrOf H 𝒟 (X y)) (X y).2, fun y d => GH H 𝒟 (X y) d,
    fun y => 𝒟.hprim _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact dist H 𝒟 (X i) (X j) (fun h => hij (hXinj h))
  · intro i u hu
    rw [𝒟.hch]
    exact chrOf_mem H 𝒟 (X i) u hu
  · intro i d hd τ
    rw [coe_GH H 𝒟 (X i) hd]
    exact (𝒟.hG _ _ d hd).1 τ
  ·
    have h := linearIndependent H 𝒟
    let σ : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) ≃
        (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) := Equiv.sigmaCongrLeft (β := fun x : Idx H 𝒟 => ↥(Nat.divisors (M / LOf H 𝒟 x))) e.symm
    have : (fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
        (fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ)) ∘ σ := by
      funext z; rfl
    rw [this, linearIndependent_equiv]
    exact h
  · apply top_unique
    intro f _
    have hf := mem_span H 𝒟 f
    let σ : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) ≃
        (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) := Equiv.sigmaCongrLeft (β := fun x : Idx H 𝒟 => ↥(Nat.divisors (M / LOf H 𝒟 x))) e.symm
    have : (Set.range fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
        Set.range fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ) := by
      have hc : (fun z : (Σ y : Fin N, ↥(Nat.divisors (M / LOf H 𝒟 (X y)))) => GH H 𝒟 (X z.1) (z.2 : ℕ)) =
          (fun w : (Σ x : Idx H 𝒟, ↥(Nat.divisors (M / LOf H 𝒟 x))) => GH H 𝒟 w.1 (w.2 : ℕ)) ∘ σ := by
        funext z; rfl
      rw [hc, EquivLike.range_comp]
    rw [this]
    exact hf
  · intro ℓ hℓ hℓM i d hd
    exact heckeT_GH H 𝒟 hℓ hℓM (X i) hd
  · intro u i d hd
    exact diamond_GH H 𝒟 u (X i) hd
  · intro q hq hqM i d hd
    exact heckeU_GH H 𝒟 hq hqM (X i) hd

end GammaHFormBasis


open scoped MatrixGroups ModularForm

theorem CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    ∃ (n : ℕ) (L : Fin n → ℕ) (hL : ∀ i, L i ∣ M)
      (ε : (i : Fin n) → DirichletCharacter ℂ (L i))
      (g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k)
      (G : Fin n → ℕ → CuspForm (CohCarrier.GammaH M H) k),
      (∀ i, CuspForm.IsPrimitiveForm (ε i) (g i)) ∧
      (∀ i j, i ≠ j → L i ≠ L j ∨ ∃ m : ℕ, ModularFormClass.qCoeff (g i) m ≠ ModularFormClass.qCoeff (g j) m) ∧
      (∀ i, ∀ u : (ZMod M)ˣ, u ∈ H → DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) = 1) ∧
      (∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        ∀ τ : UpperHalfPlane, G i d τ = g i (ModularForm.heckeDiagMatrix d • τ)) ∧
      LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) ∧
      Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
        haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
        CuspForm.heckeTLinH k hℓ hℓM (G i d) = ModularFormClass.qCoeff (g i) ℓ • G i d) ∧
      (∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
        CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d) ∧
      (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
        (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
        (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = ModularFormClass.qCoeff (g i) q • G i d) ∧
        (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
          ModularFormClass.qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))) := by
  exact GammaHFormBasis.main M H k

namespace HeckeOperatorCommutation

variable (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ)

abbrev W : Type := CuspForm (CohCarrier.GammaH M H) k

structure Datum where
  n : ℕ
  L : Fin n → ℕ
  hL : ∀ i, L i ∣ M
  ε : (i : Fin n) → DirichletCharacter ℂ (L i)
  g : (i : Fin n) → CuspForm (CongruenceSubgroup.Gamma1 (L i)) k
  G : Fin n → ℕ → W M H k
  hli : LinearIndependent ℂ (fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ))
  hspan : Submodule.span ℂ (Set.range fun x : (Σ i : Fin n, ↥(Nat.divisors (M / L i))) => G x.1 (x.2 : ℕ)) = ⊤
  hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin n) (d : ℕ), d ∣ M / L i →
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    CuspForm.heckeTLinH k hℓ hℓM (G i d) = qCoeff (g i) ℓ • G i d
  hD : ∀ (u : (ZMod M)ˣ) (i : Fin n) (d : ℕ), d ∣ M / L i →
    CuspForm.diamondLinH k u (G i d) = DirichletCharacter.changeLevel (hL i) (ε i) (u : ZMod M) • G i d
  hU : ∀ (q : ℕ), q.Prime → q ∣ M → ∀ (i : Fin n) (d : ℕ), d ∣ M / L i →
    (q ∣ d → CuspForm.heckeULinH k q (G i d) = G i (d / q)) ∧
    (¬ q ∣ d → q ∣ L i → CuspForm.heckeULinH k q (G i d) = qCoeff (g i) q • G i d) ∧
    (¬ q ∣ d → ¬ q ∣ L i → CuspForm.heckeULinH k q (G i d) =
      qCoeff (g i) q • G i d - (ε i (q : ZMod (L i)) * (q : ℂ) ^ (k - 1)) • G i (d * q))

theorem nonempty_datum : Nonempty (Datum M H k) := by
  obtain ⟨n, L, hL, ε, g, G, -, -, -, -, hli, hspan, hT, hD, hU⟩ :=
    CuspForm.exists_isPrimitiveForm_basis_gammaH_and_heckeTLinH_and_diamondLinH_and_heckeULinH_apply M H k
  exact ⟨⟨n, L, hL, ε, g, G, hli, hspan, hT, hD, hU⟩⟩

variable {M H k}
variable (𝒟 : Datum M H k)

abbrev Idx : Type := Σ i : Fin 𝒟.n, ↥(Nat.divisors (M / 𝒟.L i))

def basis : Module.Basis (Idx 𝒟) ℂ (W M H k) :=
  Module.Basis.mk (v := fun x : Idx 𝒟 => 𝒟.G x.1 (x.2 : ℕ)) 𝒟.hli (by rw [𝒟.hspan])

theorem basis_apply (x : Idx 𝒟) : basis 𝒟 x = 𝒟.G x.1 (x.2 : ℕ) := by simp [basis]

def V (i : Fin 𝒟.n) : Submodule ℂ (W M H k) :=
  Submodule.span ℂ (Set.range fun d : ↥(Nat.divisors (M / 𝒟.L i)) => 𝒟.G i (d : ℕ))

theorem L_ne_zero (i : Fin 𝒟.n) : 𝒟.L i ≠ 0 := fun h => by
  have := 𝒟.hL i; rw [h, zero_dvd_iff] at this; exact NeZero.ne M this

theorem div_ne_zero (i : Fin 𝒟.n) : M / 𝒟.L i ≠ 0 :=
  Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne M)) (𝒟.hL i))
    (Nat.pos_of_ne_zero (L_ne_zero 𝒟 i)))

theorem G_mem_V (i : Fin 𝒟.n) {d : ℕ} (hd : d ∣ M / 𝒟.L i) : 𝒟.G i d ∈ V 𝒟 i :=
  Submodule.subset_span ⟨⟨d, Nat.mem_divisors.mpr ⟨hd, div_ne_zero 𝒟 i⟩⟩, rfl⟩

theorem scalar_on_V (T : Module.End ℂ (W M H k)) (i : Fin 𝒟.n) (c : ℂ)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) = c • 𝒟.G i d) : ∀ v ∈ V 𝒟 i, T v = c • v := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, smul_add]
  | smul a x _ hx => rw [map_smul, hx, smul_comm]

theorem stab_on_V (T : Module.End ℂ (W M H k)) (i : Fin 𝒟.n)
    (h : ∀ d : ℕ, d ∣ M / 𝒟.L i → T (𝒟.G i d) ∈ V 𝒟 i) : ∀ v ∈ V 𝒟 i, T v ∈ V 𝒟 i := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨d, rfl⟩ := hx; exact h d (Nat.dvd_of_mem_divisors d.2)
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem heckeT_scalar {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (i : Fin 𝒟.n) :
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    ∀ v ∈ V 𝒟 i, CuspForm.heckeTLinH k hℓ hℓM v = qCoeff (𝒟.g i) ℓ • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hT ℓ hℓ hℓM i d hd)

theorem diamond_scalar (u : (ZMod M)ˣ) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.diamondLinH k u v = DirichletCharacter.changeLevel (𝒟.hL i) (𝒟.ε i) (u : ZMod M) • v :=
  scalar_on_V 𝒟 _ i _ (fun d hd => 𝒟.hD u i d hd)

theorem mul_dvd_div {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) (hqL : ¬ q ∣ 𝒟.L i) {d : ℕ}
    (hd : d ∣ M / 𝒟.L i) (hqd : ¬ q ∣ d) : d * q ∣ M / 𝒟.L i := by
  have hcop : Nat.Coprime d q := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
  refine hcop.mul_dvd_of_dvd_of_dvd hd ?_
  have hqML : Nat.Coprime q (𝒟.L i) := (Nat.Prime.coprime_iff_not_dvd hq).mpr hqL
  have : q ∣ 𝒟.L i * (M / 𝒟.L i) := by rw [Nat.mul_div_cancel' (𝒟.hL i)]; exact hqM
  exact hqML.dvd_of_dvd_mul_left this

theorem heckeU_stab {q : ℕ} (hq : q.Prime) (hqM : q ∣ M) (i : Fin 𝒟.n) :
    ∀ v ∈ V 𝒟 i, CuspForm.heckeULinH k q v ∈ V 𝒟 i := by
  refine stab_on_V 𝒟 _ i (fun d hd => ?_)
  obtain ⟨h1, h2, h3⟩ := 𝒟.hU q hq hqM i d hd
  by_cases hqd : q ∣ d
  · rw [h1 hqd]; exact G_mem_V 𝒟 i ((Nat.div_dvd_of_dvd hqd).trans hd)
  · by_cases hqL : q ∣ 𝒟.L i
    · rw [h2 hqd hqL]; exact Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd)
    · rw [h3 hqd hqL]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (G_mem_V 𝒟 i hd))
        (Submodule.smul_mem _ _ (G_mem_V 𝒟 i (mul_dvd_div 𝒟 hq hqM i hqL hd hqd)))

theorem comm_of_scalar_of_stab (A B : Module.End ℂ (W M H k)) (c : Fin 𝒟.n → ℂ)
    (hA : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v = c i • v) (hB : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, B v ∈ V 𝒟 i) :
    ∀ f : W M H k, A (B f) = B (A f) := by
  have : A * B = B * A := by
    refine (basis 𝒟).ext fun x => ?_
    obtain ⟨i, d⟩ := x
    have hmem : 𝒟.G i d ∈ V 𝒟 i := G_mem_V 𝒟 i (Nat.dvd_of_mem_divisors d.2)
    rw [basis_apply, Module.End.mul_apply, Module.End.mul_apply, hA i _ (hB i _ hmem), hA i _ hmem, map_smul]
  intro f
  exact congrArg (fun T : Module.End ℂ (W M H k) => T f) this

theorem stab_of_scalar (A : Module.End ℂ (W M H k)) (c : Fin 𝒟.n → ℂ)
    (hA : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v = c i • v) : ∀ (i : Fin 𝒟.n), ∀ v ∈ V 𝒟 i, A v ∈ V 𝒟 i :=
  fun i v hv => by rw [hA i v hv]; exact Submodule.smul_mem _ _ hv

end HeckeOperatorCommutation


open scoped MatrixGroups ModularForm

theorem CuspForm.heckeTLinH_heckeULinH_diamondLinH_comm
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (k : ℤ) :
    (∀ (ℓ ℓ' : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (hℓ' : ℓ'.Prime) (hℓ'M : ¬ ℓ' ∣ M)
        (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      haveI : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeTLinH k hℓ' hℓ'M f) =
        CuspForm.heckeTLinH k hℓ' hℓ'M (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (q : ℕ), q.Prime → q ∣ M →
        ∀ f : CuspForm (CohCarrier.GammaH M H) k,
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.heckeULinH k q f) =
        CuspForm.heckeULinH k q (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
      CuspForm.heckeTLinH k hℓ hℓM (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeTLinH k hℓ hℓM f)) ∧
    (∀ (q : ℕ), q.Prime → q ∣ M → ∀ (d : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.heckeULinH k q (CuspForm.diamondLinH k d f) =
        CuspForm.diamondLinH k d (CuspForm.heckeULinH k q f)) ∧
    (∀ (d d' : (ZMod M)ˣ) (f : CuspForm (CohCarrier.GammaH M H) k),
      CuspForm.diamondLinH k d (CuspForm.diamondLinH k d' f) =
        CuspForm.diamondLinH k d' (CuspForm.diamondLinH k d f)) := by
  obtain ⟨𝒟⟩ := HeckeOperatorCommutation.nonempty_datum M H k
  refine ⟨fun ℓ ℓ' hℓ hℓM hℓ' hℓ'M f => ?_, fun ℓ hℓ hℓM q hq hqM f => ?_, fun ℓ hℓ hℓM d f => ?_,
    fun q hq hqM d f => ?_, fun d d' f => ?_⟩
  · have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have : NeZero ℓ' := ⟨hℓ'.ne_zero⟩
    exact HeckeOperatorCommutation.comm_of_scalar_of_stab 𝒟 _ _ _
      (fun i => HeckeOperatorCommutation.heckeT_scalar 𝒟 hℓ hℓM i)
      (HeckeOperatorCommutation.stab_of_scalar 𝒟 _ _ (fun i => HeckeOperatorCommutation.heckeT_scalar 𝒟 hℓ' hℓ'M i)) f
  · have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact HeckeOperatorCommutation.comm_of_scalar_of_stab 𝒟 _ _ _
      (fun i => HeckeOperatorCommutation.heckeT_scalar 𝒟 hℓ hℓM i)
      (fun i => HeckeOperatorCommutation.heckeU_stab 𝒟 hq hqM i) f
  · have : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact HeckeOperatorCommutation.comm_of_scalar_of_stab 𝒟 _ _ _
      (fun i => HeckeOperatorCommutation.heckeT_scalar 𝒟 hℓ hℓM i)
      (HeckeOperatorCommutation.stab_of_scalar 𝒟 _ _ (fun i => HeckeOperatorCommutation.diamond_scalar 𝒟 d i)) f
  · exact (HeckeOperatorCommutation.comm_of_scalar_of_stab 𝒟 _ _ _
      (fun i => HeckeOperatorCommutation.diamond_scalar 𝒟 d i)
      (fun i => HeckeOperatorCommutation.heckeU_stab 𝒟 hq hqM i) f).symm
  · exact HeckeOperatorCommutation.comm_of_scalar_of_stab 𝒟 _ _ _
      (fun i => HeckeOperatorCommutation.diamond_scalar 𝒟 d i)
      (HeckeOperatorCommutation.stab_of_scalar 𝒟 _ _ (fun i => HeckeOperatorCommutation.diamond_scalar 𝒟 d' i)) f


end
