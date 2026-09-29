/-
  From a Hecke character to a normalised eigenform.

  * `CuspForm.linearIndependent_of_mem_intLattice` — `ℤ`-independence of cusp
    forms in the integral lattice implies `ℂ`-independence.
  * `CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul` — the
    generic faithful-lattice eigenvector (`Algebra/FaithfulLatticeEigenvector.lean`)
    applied to the Hecke algebra acting on `intLattice`.
  * `CuspForm.HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq` — the
    eigenvalue system produced by the first node is turned into a normalised
    eigenform, using `RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed`
    to extend the character from `heckeAlgebra N 2 S` to `heckeAlgebra N 2 ∅`.

  The three statements are the pin's `Theorems/` wrappers verbatim; the proofs are
  transcribed from the `P2M/Sol/S_*` files, pinned `aa2d8b3`:

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_linearIndependent_of_mem_intLattice.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.lean

  **Truncation dedup (work order §2).** The pin's first file introduces a *third*
  copy of the Sturm truncation — its `FrobChareqC2.sturmB`/`trunc`/`trunc_injective`
  (lines 33–49). The port does not: it reuses the public `CuspForm.qCoeffTrunc`
  (`ModularForms/SturmBound.lean`) with the injectivity derived once, privately,
  from the public `CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero`. The helper
  `qCoeffTrunc_injective` is the only new truncation statement and it is a
  three-line corollary of the existing bound.

  The `FrobChareqC2` q-coefficient helpers of the third pin file are likewise not
  re-proved: `hΓ` is `CongruenceSubgroup.one_mem_strictPeriods_Gamma0`,
  `qCoeff_zero'` is `CuspForm.qCoeff_zero`, and
  `qCoeff_hecke{T,U}Lin_one` are kept `private` here (their only consumer is
  `C2_7a`).
-/
import FLTForHuman.ModularForms.HeckeFiniteAlgebra
import FLTForHuman.ModularForms.SturmBound
import FLTForHuman.ModularForms.Defs.Eigenform
import FLTForHuman.Algebra.FaithfulLatticeEigenvector
import FLTForHuman.Algebra.IntegralExtensionCharacters
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange

set_option autoImplicit false

-- The pin's `haveI` walls are load-bearing; keep them literal (port convention).
set_option linter.style.haveILetI false

noncomputable section

open UpperHalfPlane ModularForm ModularFormClass
open scoped MatrixGroups ModularForm CongruenceSubgroup

namespace CuspForm

variable {N : ℕ} {k : ℤ}

/-! ## The truncation, derived from the existing Sturm bound -/

/-- Injectivity of the coefficient truncation beyond the Sturm bound, as a
corollary of `CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero` (this is the
private replacement for the pin's third `sturmB`/`trunc`/`trunc_injective`). -/
private theorem qCoeffTrunc_injective (N : ℕ) [NeZero N] (k : ℤ) {d : ℕ}
    (hd : k * Nat.card (𝒮ℒ ⧸ ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) < 12 * d) :
    Function.Injective (CuspForm.qCoeffTrunc N k d) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine CuspForm.Gamma0_eq_zero_of_qExpansion_coeff_eq_zero f d hd ?_
  intro m hm
  have hfm := congrFun hf ⟨m, hm⟩
  simpa [CuspForm.qCoeffTrunc] using hfm

/-- **`ℤ`-independence implies `ℂ`-independence on the integral lattice.**
Stated verbatim from `Theorems/Thm_CuspForm_linearIndependent_of_mem_intLattice.lean`. -/
theorem linearIndependent_of_mem_intLattice {N : ℕ} [NeZero N] {k : ℤ} (n : ℕ)
    (f : Fin n → CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : ∀ i, f i ∈ CuspForm.intLattice N k) (h : LinearIndependent ℤ f) :
    LinearIndependent ℂ f := by
  classical

  have hint : ∀ i (j : ℕ), ∃ m : ℤ, qCoeff ⇑(f i) j = (m : ℂ) := fun i =>
    (CuspForm.mem_intLattice_iff (f i)).mp (hf i)
  choose v hv using hint
  -- The truncation length and its injectivity, from the finite-dimensionality proof.
  set c : ℕ := Nat.card (𝒮ℒ ⧸ ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) with hc
  set d : ℕ := k.toNat * c + 1 with hd_def
  have hd : k * (c : ℤ) < 12 * (d : ℤ) := by
    have h1 : k * (c : ℤ) ≤ (k.toNat : ℤ) * c :=
      mul_le_mul_of_nonneg_right (Int.self_le_toNat k) (Int.natCast_nonneg c)
    have h2 : (0 : ℤ) ≤ (k.toNat : ℤ) * c := by positivity
    have h3 : (12 : ℤ) * (d : ℤ) = 12 * ((k.toNat : ℤ) * c) + 12 := by
      rw [hd_def]; push_cast; ring
    linarith
  have hd' : k * Nat.card (𝒮ℒ ⧸ ((CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)) < 12 * d := by
    rw [← hc]; exact hd
  let w : Fin n → Fin d → ℤ := fun i j => v i j
  have htr : ∀ i, CuspForm.qCoeffTrunc N k d (f i) = algebraMap ℤ ℂ ∘ w i := by
    intro i; funext j
    show qCoeff ⇑(f i) j = algebraMap ℤ ℂ (v i j)
    rw [hv, eq_intCast]

  have hw : LinearIndependent ℤ w := by
    rw [Fintype.linearIndependent_iff]
    intro μ hμ
    have h0 : CuspForm.qCoeffTrunc N k d (∑ i, μ i • f i) = 0 := by
      rw [map_sum]
      funext j
      rw [Finset.sum_apply, Pi.zero_apply]
      have := congrFun hμ j
      rw [Finset.sum_apply, Pi.zero_apply] at this
      simp only [Pi.smul_apply, smul_eq_mul] at this
      calc ∑ i, (CuspForm.qCoeffTrunc N k d (μ i • f i)) j = ∑ i, ((μ i : ℂ) * algebraMap ℤ ℂ (w i j)) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Int.cast_smul_eq_zsmul ℂ, map_smul, Pi.smul_apply, smul_eq_mul, htr]
            rfl
        _ = algebraMap ℤ ℂ (∑ i, μ i * w i j) := by
            rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul, eq_intCast, eq_intCast]
        _ = 0 := by rw [this, map_zero]
    have hzero : ∑ i, μ i • f i = 0 :=
      qCoeffTrunc_injective N k (d := d) hd' (by rw [h0, map_zero])
    exact Fintype.linearIndependent_iff.mp h μ hzero

  have hC : LinearIndependent ℂ (fun i => algebraMap ℤ ℂ ∘ w i) :=
    (linearIndependent_algebraMap_comp_iff (R := ℤ) (S := ℂ)).mpr hw
  have hC' : LinearIndependent ℂ (CuspForm.qCoeffTrunc N k d ∘ f) := by
    convert hC using 1
    funext i; exact htr i
  exact LinearIndependent.of_comp _ hC'

/-! ## The eigenvector from the faithful lattice -/

/-- **The eigenvector for a Hecke character.** Stated verbatim from
`Theorems/Thm_CuspForm_HasIntegralStructure_exists_ne_zero_forall_apply_eq_smul.lean`. -/
theorem HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul {N : ℕ} [NeZero N] {k : ℤ}
    (hN : CuspForm.HasIntegralStructure N k) (hk : 1 ≤ k) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N k S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) k, f ≠ 0 ∧
      ∀ t : CuspForm.heckeAlgebra N k S,
        (t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)) f = χ t • f := by
  have h := Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom (K := ℂ)
    (heckeAlgebra N k S).val.toRingHom (intLattice N k) (CuspForm.intLattice_fg N k)
    (fun t f hf => CuspForm.mem_intLattice_of_mem_heckeAlgebra hk t.2 hf)
    (fun t ht => Subtype.ext (CuspForm.HasIntegralStructure.eq_zero_of_forall_mem_intLattice hN (t : Module.End ℂ _) ht))
    (fun n f hf hind => CuspForm.linearIndependent_of_mem_intLattice n f hf hind) χ
  exact h

/-! ## The eigenvalue system becomes a normalised eigenform -/

/- The q-coefficient helpers of the pin's `FrobChareqC2` block. Private: their
only consumer is `C2_7a`, and the ported `CuspForm.qCoeff_zero` /
`ModularFormClass.qCoeff_hecke{T,U}` already carry the shared content. -/
namespace FrobChareqC2

private theorem qCoeff_zero' (n : ℕ) :
    qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) n = 0 := by
  simp only [qCoeff, FunLike.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

private theorem qCoeff_smul (c : ℂ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = c • ⇑f := by ext z; simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) c f]
  simp

private theorem qCoeff_heckeTLin_one {N : ℕ} {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (c : ℂ)
    (h : CuspForm.heckeTLin 2 hℓ hℓN f = c • f) : qCoeff ⇑f ℓ = c * qCoeff ⇑f 1 := by
  have := ((CuspForm.heckeTLin_apply_eq_smul_iff 2 hℓ hℓN f c).mp h) 1
  have h1 : ¬ ℓ ∣ 1 := fun hd => hℓ.one_lt.ne' (Nat.dvd_one.mp hd)
  rw [ModularForm.coeffHeckeT_apply, one_mul, ite_eq_right h1, add_zero] at this
  exact this

private theorem qCoeff_heckeULin_one {N : ℕ} [NeZero N] {q : ℕ} (hqN : q ∣ N)
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (c : ℂ)
    (h : CuspForm.heckeULin 2 hqN f = c • f) : qCoeff ⇑f q = c * qCoeff ⇑f 1 := by
  have := ((CuspForm.heckeULin_apply_eq_smul_iff 2 hqN f c).mp h) 1
  rw [ModularForm.coeffHeckeU_apply, one_mul] at this
  exact this

/-- The `S = ∅` case of the extraction: a normalised eigenform whose prime
coefficients are the character values. This is the pin's `C2_7a`, private. -/
private theorem C2_7a {N : ℕ} [NeZero N] (hN : HasIntegralStructure N 2) (χ : heckeAlgebra N 2 ∅ →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N),
        ModularFormClass.qCoeff f ℓ = χ (heckeAlgebra.T hℓ hℓN (Set.notMem_empty ℓ))) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N),
        ModularFormClass.qCoeff f q = χ (heckeAlgebra.U hq hqN (Set.notMem_empty q)) := by
  obtain ⟨g, hg0, hg⟩ := CuspForm.HasIntegralStructure.exists_ne_zero_forall_apply_eq_smul hN one_le_two χ

  classical
  let c : ℕ → ℂ := fun p => if hp : p.Prime then
    (if hpN : p ∣ N then χ (heckeAlgebra.U hp hpN (Set.notMem_empty p))
      else χ (heckeAlgebra.T hp hpN (Set.notMem_empty p))) else 0
  have hT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N), CuspForm.heckeTLin 2 hℓ hℓN g = c ℓ • g := by
    intro ℓ hℓ hℓN
    have := hg (heckeAlgebra.T hℓ hℓN (Set.notMem_empty ℓ))
    rw [heckeAlgebra.coe_T] at this
    rw [this]; simp only [c, dite_eq_left hℓ, dite_eq_right hℓN]
  have hU : ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N), CuspForm.heckeULin 2 hqN g = c q • g := by
    intro q hq hqN
    have := hg (heckeAlgebra.U hq hqN (Set.notMem_empty q))
    rw [heckeAlgebra.coe_U] at this
    rw [this]; simp only [c, dite_eq_left hq, dite_eq_left hqN]

  set a₁ := qCoeff ⇑g 1 with ha₁
  have ha₁0 : a₁ ≠ 0 := by
    intro h0
    apply hg0
    have hcoefT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n, coeffHeckeT 2 p (qCoeff ⇑g) n = c p * qCoeff ⇑g n :=
      fun p hp hpN => (CuspForm.heckeTLin_apply_eq_smul_iff 2 hp hpN g (c p)).mp (hT p hp hpN)
    have hcoefU : ∀ p : ℕ, p.Prime → p ∣ N → ∀ n, coeffHeckeU p (qCoeff ⇑g) n = c p * qCoeff ⇑g n :=
      fun p hp hpN => (CuspForm.heckeULin_apply_eq_smul_iff 2 hpN g (c p)).mp (hU p hp hpN)
    have hzero : ∀ n, n ≠ 0 → qCoeff ⇑g n = 0 :=
      ModularForm.eq_zero_of_coeffHecke_eigen_of_apply_one_eq_zero 2 N (qCoeff ⇑g) c hcoefT hcoefU h0
    refine ModularFormClass.eq_of_forall_qCoeff_eq (CongruenceSubgroup.one_mem_strictPeriods_Gamma0 N) fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [CuspForm.qCoeff_zero, CuspForm.qCoeff_zero]
    · rw [hzero n hn.ne']
      exact (qCoeff_zero' (N := N) (k := 2) n).symm

  refine ⟨a₁⁻¹ • g, ?_, ?_, ?_⟩
  · rw [CuspForm.isNormalizedEigenform_iff_heckeTLin]
    refine ⟨by rw [qCoeff_smul, ← ha₁, inv_mul_cancel₀ ha₁0], fun p hp => ⟨fun hpN => ?_, fun hpN => ?_⟩⟩
    · rw [map_smul, hT p hp hpN, smul_comm, qCoeff_smul, qCoeff_heckeTLin_one hp hpN g (c p) (hT p hp hpN),
        ← ha₁, mul_comm a₁⁻¹, mul_assoc, mul_inv_cancel₀ ha₁0, mul_one]
    · rw [map_smul, hU p hp hpN, smul_comm, qCoeff_smul, qCoeff_heckeULin_one hpN g (c p) (hU p hp hpN),
        ← ha₁, mul_comm a₁⁻¹, mul_assoc, mul_inv_cancel₀ ha₁0, mul_one]
  · intro ℓ hℓ hℓN
    rw [qCoeff_smul, qCoeff_heckeTLin_one hℓ hℓN g (c ℓ) (hT ℓ hℓ hℓN), ← ha₁, mul_comm a₁⁻¹, mul_assoc,
      mul_inv_cancel₀ ha₁0, mul_one]
    simp only [c, dite_eq_left hℓ, dite_eq_right hℓN]
  · intro q hq hqN
    rw [qCoeff_smul, qCoeff_heckeULin_one hqN g (c q) (hU q hq hqN), ← ha₁, mul_comm a₁⁻¹, mul_assoc,
      mul_inv_cancel₀ ha₁0, mul_one]
    simp only [c, dite_eq_left hq, dite_eq_left hqN]

end FrobChareqC2

open FrobChareqC2 in

/-- **The character's eigenvalue system is a normalised eigenform.** Stated
verbatim from
`Theorems/Thm_CuspForm_HasIntegralStructure_exists_isNormalizedEigenform_qCoeff_eq.lean`. -/
theorem HasIntegralStructure.exists_isNormalizedEigenform_qCoeff_eq {N : ℕ} [NeZero N]
    (hN : CuspForm.HasIntegralStructure N 2) {S : Set ℕ}
    (χ : CuspForm.heckeAlgebra N 2 S →+* ℂ) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) 2, f.IsNormalizedEigenform ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
        ModularFormClass.qCoeff f ℓ = χ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) ∧
      ∀ (q : ℕ) (hq : q.Prime) (hqN : q ∣ N) (hqS : q ∉ S),
        ModularFormClass.qCoeff f q = χ (CuspForm.heckeAlgebra.U hq hqN hqS) := by
  haveI : Module.Finite ℤ (heckeAlgebra N 2 ∅) := CuspForm.HasIntegralStructure.moduleFinite_heckeAlgebra hN one_le_two ∅
  let ι : heckeAlgebra N 2 S →ₐ[ℤ] heckeAlgebra N 2 ∅ :=
    Subalgebra.inclusion (heckeAlgebra_mono (Set.empty_subset S))
  letI : Algebra (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) := ι.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) :=
    ⟨fun x => by
      have h := (Algebra.IsIntegral.isIntegral (R := ℤ) x).map_of_comp_eq
        (algebraMap ℤ (heckeAlgebra N 2 S)) (RingHom.id (heckeAlgebra N 2 ∅)) (RingHom.ext_int _ _)
      rwa [RingHom.id_apply] at h⟩
  have hker : RingHom.ker (algebraMap (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅)) ≤ RingHom.ker χ := by
    have hinj : Function.Injective ι := Subalgebra.inclusion_injective _
    have : RingHom.ker (algebraMap (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅)) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).mp hinj
    rw [this]
    exact bot_le
  obtain ⟨ψ, hψ⟩ := RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed χ hker
  have hψι : ∀ t : heckeAlgebra N 2 S, ψ (ι t) = χ t := fun t => by
    rw [← hψ]
    rfl
  obtain ⟨f, hf, hfT, hfU⟩ := C2_7a hN ψ
  refine ⟨f, hf, fun ℓ hℓ hℓN hℓS => ?_, fun q hq hqN hqS => ?_⟩
  · rw [hfT ℓ hℓ hℓN, ← hψι]
    rfl
  · rw [hfU q hq hqN, ← hψι]
    rfl

end CuspForm

end
