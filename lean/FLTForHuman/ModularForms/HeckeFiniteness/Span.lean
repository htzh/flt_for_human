/-
  The `ℂ`-span of the weight-two Hecke algebra has the dimension of `S₂(Γ₀(N))`.

  The first `q`-coefficient `a₁` gives a pairing between the `ℂ`-span of the Hecke
  algebra at level `∅` and `S₂(Γ₀(N))`, injective in both slots: in the second by the
  definition of `formKer`, in the first because an operator annihilating `a₁` of every
  form annihilates the whole space, by the `T_p`/`U_p` recurrence along the `q`-expansion.
  Two finite-dimensional `ℂ`-vector spaces with an injection each way have equal
  dimension.

  FLT provenance, pinned `aa2d8b3`:
  `Theorems/Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank.lean`.
-/
import FLTForHuman.ModularForms.HeckeAlgebra
import FLTForHuman.ModularForms.HeckeEigenform
import FLTForHuman.ModularForms.HeckeQCoeff
import FLTForHuman.ModularForms.QCoeffClass
import FLTForHuman.ModularForms.SturmBound

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped MatrixGroups ModularForm Manifold

namespace CuspForm

variable {N : ℕ} {k : ℤ} {S : Set ℕ}

/-! ## The span of the weight-2 Hecke algebra

The first `q`-coefficient `a₁Pairing T f = a₁(T f)` is a pairing between the
`ℂ`-span `fullC` of the Hecke algebra at level `∅` and `S₂(Γ₀(N))`, injective in
both slots (in the first because a Hecke operator annihilating `a₁` of every form
annihilates the whole space, by the `T_p`/`U_p` recurrence along the `q`-expansion;
in the second by definition of `formKer`). Hence the two finite-dimensional
`ℂ`-vector spaces have the same dimension. -/

section FinrankSpan

open ModularForm ModularFormClass

private abbrev S2 (N : ℕ) : Type := CuspForm (CongruenceSubgroup.Gamma0 N) 2

private def fullC (N : ℕ) [NeZero N] : Subalgebra ℂ (Module.End ℂ (S2 N)) :=
  Algebra.adjoin ℂ (CuspForm.heckeGenerators N 2 (∅ : Set ℕ))

private instance instFullCIsMulCommutative (N : ℕ) [NeZero N] : IsMulCommutative (fullC N) :=
  Algebra.isMulCommutative_adjoin ℂ fun _ hT _ hT' _ =>
    CuspForm.commute_of_mem_heckeGenerators hT hT'

open scoped IsMulCommutative in
private instance instFullCCommRing (N : ℕ) [NeZero N] : CommRing (fullC N) := inferInstance

private theorem span_heckeAlgebra_eq_fullC (N : ℕ) [NeZero N] :
    Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) : Set (Module.End ℂ (S2 N)))
      = Subalgebra.toSubmodule (fullC N) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    intro T hT
    have hle : CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) ≤ (fullC N).restrictScalars ℤ := by
      refine Algebra.adjoin_le ?_
      intro x hx
      exact (Algebra.subset_adjoin hx : x ∈ fullC N)
    exact (hle hT : T ∈ fullC N)
  · rw [fullC, Algebra.adjoin_eq_span]
    apply Submodule.span_mono
    intro T hT
    change T ∈ CuspForm.heckeAlgebra N 2 (∅ : Set ℕ)
    exact (Submonoid.closure_le.mpr (fun x hx => Algebra.subset_adjoin hx)) hT

private theorem qCoeff_heckeTLin (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f : S2 N) (n : ℕ) :
    qCoeff (⇑(CuspForm.heckeTLin 2 hp hpN f)) n
      = qCoeff (⇑f) (p * n) + (p : ℂ) * (if p ∣ n then qCoeff (⇑f) (n / p) else 0) := by
  unfold qCoeff
  rw [CuspForm.qExpansion_heckeTLin hp hpN f, PowerSeries.coeff_heckeT]
  simp

private theorem qCoeff_heckeULin (N : ℕ) [NeZero N] {p : ℕ} (hp : p.Prime) (hpN : p ∣ N)
    (f : S2 N) (n : ℕ) :
    qCoeff (⇑(CuspForm.heckeULin 2 hpN f)) n = qCoeff (⇑f) (n * p) := by
  rw [CuspForm.coe_heckeULin_apply]
  rw [ModularFormClass.qCoeff_heckeU f
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1)
      hp.ne_zero n,
    ModularForm.coeffHeckeU_apply]

private def formKer (N : ℕ) [NeZero N] : Set (S2 N) :=
  {f | ∀ T ∈ fullC N, qCoeff (⇑(T f)) 1 = 0}

private theorem formKer_stable (N : ℕ) [NeZero N] {f : S2 N} (hf : f ∈ formKer N)
    {U : Module.End ℂ (S2 N)} (hU : U ∈ fullC N) : U f ∈ formKer N := by
  intro T hT
  have h : (T * U) f = T (U f) := rfl
  rw [← h]
  exact hf _ ((fullC N).mul_mem hT hU)

private theorem qCoeff_eq_zero_of_mem_formKer (N : ℕ) [NeZero N] :
    ∀ (n : ℕ) (f : S2 N), f ∈ formKer N → qCoeff (⇑f) n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro f hf
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact CuspForm.qCoeff_zero f
      · simpa using hf 1 (fullC N).one_mem
    ·
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (show n ≠ 1 by omega)
      obtain ⟨m, rfl⟩ := hpn
      have hm : m < p * m := by
        have := hp.one_lt
        have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; omega)
        nlinarith
      by_cases hpN : p ∣ N
      ·
        have hU : CuspForm.heckeULin 2 hpN f ∈ formKer N :=
          formKer_stable N hf (Algebra.subset_adjoin
            (CuspForm.heckeULin_mem_heckeGenerators hp hpN (by simp)))
        have := ih m hm _ hU
        rw [qCoeff_heckeULin N hp hpN] at this
        rwa [mul_comm] at this
      ·
        have hT : CuspForm.heckeTLin 2 hp hpN f ∈ formKer N :=
          formKer_stable N hf (Algebra.subset_adjoin
            (CuspForm.heckeTLin_mem_heckeGenerators hp hpN (by simp)))
        have h1 := ih m hm _ hT
        rw [qCoeff_heckeTLin N hp hpN] at h1
        have h2 : (if p ∣ m then qCoeff (⇑f) (m / p) else 0) = 0 := by
          split_ifs with hpm
          · exact ih (m / p) (lt_of_le_of_lt (Nat.div_le_self m p) hm) f hf
          · rfl
        rw [h2, mul_zero, add_zero] at h1
        exact h1

private theorem eq_zero_of_mem_formKer (N : ℕ) [NeZero N] {f : S2 N} (hf : f ∈ formKer N) :
    f = 0 := by
  refine ModularFormClass.eq_of_forall_qCoeff_eq
    (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1) fun n => ?_
  rw [qCoeff_eq_zero_of_mem_formKer N n f hf]
  simp [ModularFormClass.qCoeff, FunLike.coe_zero, UpperHalfPlane.qExpansion_zero]

/-- The concrete-spelling copy of `ModularFormClass.qCoeff_add'`. -/
private theorem qCoeff_add' (N : ℕ) [NeZero N] (f g : S2 N) (n : ℕ) :
    qCoeff (⇑(f + g)) n = qCoeff (⇑f) n + qCoeff (⇑g) n := by
  simpa only [qCoeff, FunLike.coe_add] using
    ModularFormClass.qCoeff_add' (k := 2) (Γ := CongruenceSubgroup.Gamma0 N)
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1) f g n

/-- The concrete-spelling copy of `ModularFormClass.qCoeff_const_smul'`. -/
private theorem qCoeff_smul' (N : ℕ) [NeZero N] (c : ℂ) (f : S2 N) (n : ℕ) :
    qCoeff (⇑(c • f)) n = c * qCoeff (⇑f) n := by
  simpa only [qCoeff, FunLike.coe_smul] using
    ModularFormClass.qCoeff_const_smul' (k := 2) (Γ := CongruenceSubgroup.Gamma0 N)
      (by rw [CongruenceSubgroup.strictPeriods_Gamma0]; exact AddSubgroup.mem_zmultiples 1) f c n

private def a1Pairing (N : ℕ) [NeZero N] : fullC N →ₗ[ℂ] S2 N →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun T f => qCoeff (⇑((T : Module.End ℂ (S2 N)) f)) 1)
    (fun T U f => by
      show qCoeff (⇑(((T : Module.End ℂ (S2 N)) + (U : Module.End ℂ (S2 N))) f)) 1 = _
      rw [LinearMap.add_apply, qCoeff_add'])
    (fun c T f => by
      show qCoeff (⇑((c • (T : Module.End ℂ (S2 N))) f)) 1 = _
      rw [LinearMap.smul_apply, qCoeff_smul', smul_eq_mul])
    (fun T f g => by
      show qCoeff (⇑((T : Module.End ℂ (S2 N)) (f + g))) 1 = _
      rw [map_add, qCoeff_add'])
    (fun c T f => by
      show qCoeff (⇑((T : Module.End ℂ (S2 N)) (c • f))) 1 = _
      rw [map_smul, qCoeff_smul', smul_eq_mul])

@[simp] private theorem a1Pairing_apply (N : ℕ) [NeZero N] (T : fullC N) (f : S2 N) :
    a1Pairing N T f = qCoeff (⇑((T : Module.End ℂ (S2 N)) f)) 1 := rfl

private def a1PairingDual (N : ℕ) [NeZero N] : S2 N →ₗ[ℂ] Module.Dual ℂ (fullC N) :=
  (a1Pairing N).flip

private theorem a1PairingDual_injective (N : ℕ) [NeZero N] :
    Function.Injective (a1PairingDual N) := by
  rw [injective_iff_map_eq_zero]
  intro f hf
  apply eq_zero_of_mem_formKer N
  intro T hT
  have := congrArg (fun ψ : Module.Dual ℂ (fullC N) => ψ ⟨T, hT⟩) hf
  simpa [a1PairingDual] using this

private theorem eq_zero_of_mem_fullC_of_forall_qCoeff_one_eq_zero (N : ℕ) [NeZero N]
    {T : Module.End ℂ (S2 N)} (hT : T ∈ fullC N)
    (h : ∀ f : S2 N, qCoeff (⇑(T f)) 1 = 0) : T = 0 := by
  refine LinearMap.ext fun f => ?_
  rw [LinearMap.zero_apply]
  apply eq_zero_of_mem_formKer N
  intro U hU
  have hcomm : U * T = T * U :=
    congrArg Subtype.val (mul_comm (⟨U, hU⟩ : fullC N) ⟨T, hT⟩)
  have : U (T f) = T (U f) := by
    change (U * T) f = (T * U) f
    rw [hcomm]
  rw [this]
  exact h (U f)

private theorem a1Pairing_injective (N : ℕ) [NeZero N] : Function.Injective (a1Pairing N) := by
  rw [injective_iff_map_eq_zero]
  intro T hT
  apply Subtype.ext
  refine eq_zero_of_mem_fullC_of_forall_qCoeff_one_eq_zero N T.2 fun f => ?_
  have := congrArg (fun ψ : S2 N →ₗ[ℂ] ℂ => ψ f) hT
  simpa using this

private theorem finrank_fullC_eq_finrank_cuspForm (N : ℕ) [NeZero N] :
    Module.finrank ℂ (fullC N) = Module.finrank ℂ (S2 N) := by
  have : FiniteDimensional ℂ (S2 N) := CuspForm.finiteDimensional_Gamma0 (N := N) (k := 2)
  refine le_antisymm ?_ ?_
  · have h1 : Module.finrank ℂ (fullC N) ≤ Module.finrank ℂ (Module.Dual ℂ (S2 N)) :=
      LinearMap.finrank_le_finrank_of_injective (a1Pairing_injective N)
    rwa [Subspace.dual_finrank_eq] at h1
  · have h2 : Module.finrank ℂ (S2 N) ≤ Module.finrank ℂ (Module.Dual ℂ (fullC N)) :=
      LinearMap.finrank_le_finrank_of_injective (a1PairingDual_injective N)
    rwa [Subspace.dual_finrank_eq] at h2

end FinrankSpan

/-- The `ℂ`-span of the weight-`2` Hecke algebra has the dimension of
`S₂(Γ₀(N))`. Stated verbatim from
`Theorems/Thm_CuspForm_finrank_span_heckeAlgebra_eq_finrank.lean`. -/
theorem finrank_span_heckeAlgebra_eq_finrank (N : ℕ) [NeZero N] :
    Module.finrank ℂ (Submodule.span ℂ (CuspForm.heckeAlgebra N 2 (∅ : Set ℕ) :
      Set (Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)))) =
      Module.finrank ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) := by
  rw [span_heckeAlgebra_eq_fullC (N := N)]
  exact finrank_fullC_eq_finrank_cuspForm N

end CuspForm

end
