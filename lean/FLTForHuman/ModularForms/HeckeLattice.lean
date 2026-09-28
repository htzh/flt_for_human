/-
  The Hecke algebra preserves the integral lattice.

  `intLattice N k` is a `Submodule.span ℤ`; the pin's key observation is that its
  defining set is *already* a `ℤ`-submodule, so `Submodule.span_eq` turns
  membership into the coefficient integrality condition
  (`mem_intLattice_iff`). The two `_coe_eq_` targets then transport T5's
  `coeffHecke{T,U}_int` through `qCoeff_hecke{T,U}`, and the algebra target is the
  `Algebra.adjoin` closure induction over `heckeGenerators`, dispatching each
  generator to the `T`/`U` case.

  The weight-2 auxiliary lattice vocabulary of T10's `Defs/IntegralLattice.lean`
  is deliberately absent — it is a different object with different names.

  T10's finiteness half also lands its lattice-side prerequisite here
  (`intLattice_fg`, `intLattice_free_and_finite`), because the finite-generation
  proof is the pin's `S_CuspForm_intLattice_fg.lean` and needs the same private
  `qCoeff`-linearity block this module already carries (`qCoeff_add`,
  `qCoeff_zsmul`); the Hecke-algebra finiteness itself is
  `HeckeFiniteAlgebra.lean`. The engine is FLT's Sturm bound
  `ModularForm.sturm_bound_Gamma0` — mathlib `v4.34.0` still has no such form,
  but the port carries it in `SturmBound.lean`.

  FLT provenance, pinned `aa2d8b3`: `Definitions/Def_CuspForm_IntegralStructure.lean`
  (`Defs/IntegralStructure.lean`), the three `S_` files
  `S_CuspForm_mem_intLattice_of_{coe_eq_heckeT,coe_eq_heckeU,mem_heckeAlgebra}`
  and `S_CuspForm_intLattice_{fg,free_and_finite}.lean`.
-/
import FLTForHuman.ModularForms.Defs.IntegralStructure
import FLTForHuman.ModularForms.HeckeAlgebra
import FLTForHuman.ModularForms.SturmBound

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology UpperHalfPlane
open ModularForm ModularFormClass

namespace CuspForm

variable {N : ℕ} {k : ℤ}

/-- `(1 : ℝ)` is a strict period of `Γ₀(N)`. -/
private theorem one_mem_strictPeriods_Gamma0 (N : ℕ) :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma0 N : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)).strictPeriods := by
  rw [CongruenceSubgroup.strictPeriods_Gamma0]
  exact AddSubgroup.mem_zmultiples 1

/-! ## The defining set is a submodule (private) -/

private theorem qCoeff_add (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(f + g) n = qCoeff ⇑f n + qCoeff ⇑g n := by
  simp only [qCoeff, FunLike.coe_add]
  rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods_Gamma0 N) f g, map_add]

private theorem qCoeff_zero' (n : ℕ) :
    qCoeff ⇑(0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) n = 0 := by
  simp only [qCoeff, FunLike.coe_zero]
  rw [UpperHalfPlane.qExpansion_zero, map_zero]

private theorem qCoeff_zsmul (c : ℤ) (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (n : ℕ) :
    qCoeff ⇑(c • f) n = c * qCoeff ⇑f n := by
  have h1 : ⇑(c • f) = (c : ℂ) • ⇑f := by
    ext z
    simp
  simp only [qCoeff, h1]
  rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods_Gamma0 N) (c : ℂ) f]
  simp

/-- The forms with integral `q`-coefficients, as a `ℤ`-submodule. -/
private def intSubmodule (N : ℕ) (k : ℤ) :
    Submodule ℤ (CuspForm (CongruenceSubgroup.Gamma0 N) k) where
  carrier := {f | ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ)}
  add_mem' {f g} hf hg n := by
    obtain ⟨a, ha⟩ := hf n
    obtain ⟨b, hb⟩ := hg n
    exact ⟨a + b, by rw [qCoeff_add, ha, hb]; push_cast; ring⟩
  zero_mem' n := ⟨0, by rw [qCoeff_zero']; simp⟩
  smul_mem' c {f} hf n := by
    obtain ⟨a, ha⟩ := hf n
    exact ⟨c * a, by rw [qCoeff_zsmul, ha]; push_cast; ring⟩

private theorem intLattice_eq (N : ℕ) (k : ℤ) :
    CuspForm.intLattice N k = intSubmodule N k :=
  Submodule.span_eq (intSubmodule N k)

/-- The span characterisation of `intLattice`: membership is exactly coefficient
integrality. -/
private theorem mem_intLattice_iff (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    f ∈ CuspForm.intLattice N k ↔ ∀ n : ℕ, ∃ m : ℤ, qCoeff f n = (m : ℂ) := by
  rw [intLattice_eq]
  rfl

/-! ## The lattice action -/

/-- `T_p` preserves the integral lattice. Stated verbatim from
`Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeT.lean`. -/
theorem mem_intLattice_of_coe_eq_heckeT {N : ℕ} {k : ℤ} (hk : 1 ≤ k) {p : ℕ} (hp : p ≠ 0)
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : ⇑g = ModularForm.heckeT k p ⇑f)
    (hf : f ∈ CuspForm.intLattice N k) : g ∈ CuspForm.intLattice N k := by
  rw [mem_intLattice_iff] at hf ⊢
  intro n
  obtain ⟨m, hm⟩ := ModularForm.coeffHeckeT_int k hk p hf n
  exact ⟨m, by rw [hg, ModularFormClass.qCoeff_heckeT f (one_mem_strictPeriods_Gamma0 N) hp n, hm]⟩

/-- `U_p` preserves the integral lattice. Stated verbatim from
`Theorems/Thm_CuspForm_mem_intLattice_of_coe_eq_heckeU.lean`. -/
theorem mem_intLattice_of_coe_eq_heckeU {N : ℕ} {k : ℤ} {p : ℕ} (hp : p ≠ 0)
    {f g : CuspForm (CongruenceSubgroup.Gamma0 N) k} (hg : ⇑g = ModularForm.heckeU k p ⇑f)
    (hf : f ∈ CuspForm.intLattice N k) : g ∈ CuspForm.intLattice N k := by
  rw [mem_intLattice_iff] at hf ⊢
  intro n
  obtain ⟨m, hm⟩ := ModularForm.coeffHeckeU_int p hf n
  exact ⟨m, by rw [hg, ModularFormClass.qCoeff_heckeU f (one_mem_strictPeriods_Gamma0 N) hp n, hm]⟩

/-- The whole Hecke algebra preserves the integral lattice. Stated verbatim from
`Theorems/Thm_CuspForm_mem_intLattice_of_mem_heckeAlgebra.lean`. -/
theorem mem_intLattice_of_mem_heckeAlgebra {N : ℕ} [NeZero N] {k : ℤ} (hk : 1 ≤ k)
    {S : Set ℕ} {t : Module.End ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) k)}
    (ht : t ∈ CuspForm.heckeAlgebra N k S) {f : CuspForm (CongruenceSubgroup.Gamma0 N) k}
    (hf : f ∈ CuspForm.intLattice N k) : t f ∈ CuspForm.intLattice N k := by
  revert f
  refine Algebra.adjoin_induction (p := fun t _ => ∀ {f}, f ∈ intLattice N k → t f ∈ intLattice N k)
    ?_ ?_ ?_ ?_ ht
  · rintro x (⟨ℓ, hℓ, hℓN, -, rfl⟩ | ⟨q, hqN, hq, -, rfl⟩) f hf
    · exact mem_intLattice_of_coe_eq_heckeT hk hℓ.ne_zero
        (CuspForm.coe_heckeTLin_apply k hℓ hℓN f) hf
    · exact mem_intLattice_of_coe_eq_heckeU hq.ne_zero
        (CuspForm.coe_heckeULin_apply k hqN f) hf
  · intro r f hf
    rw [Algebra.algebraMap_eq_smul_one, LinearMap.smul_apply, Module.End.one_apply]
    exact (intLattice N k).smul_mem r hf
  · intro x y _ _ hx hy f hf
    rw [LinearMap.add_apply]
    exact add_mem (hx hf) (hy hf)
  · intro x y _ _ hx hy f hf
    rw [Module.End.mul_apply]
    exact hx (hy hf)

/-! ## Finite generation and freeness of the lattice

FLT's `S_CuspForm_intLattice_fg.lean` shows that members of the lattice are
determined by their first `sturmB N k + 1` `q`-coefficients; the truncation is a
`ℤ`-linear injection into a free `ℤ`-module of finite rank, so the lattice is
finitely generated. `intLattice_free_and_finite` then adds freeness over `ℤ` from
torsion-freeness. -/

/-- The Sturm bound `k · [Γ₀(N) : 1] / 12` — the number of `q`-coefficients that
determine a weight-`k` form at level `Γ₀(N)`. -/
private def sturmB (N : ℕ) (k : ℤ) : ℕ := (k * (CongruenceSubgroup.Gamma0 N).index).toNat / 12

/-- The first `sturmB N k + 1` `q`-coefficients, as a `ℤ`-linear map. -/
private def trunc (N : ℕ) (k : ℤ) :
    CuspForm (CongruenceSubgroup.Gamma0 N) k →ₗ[ℤ] (Fin (sturmB N k + 1) → ℂ) where
  toFun f i := qCoeff ⇑f i
  map_add' f g := by
    funext i
    exact qCoeff_add f g i
  map_smul' c f := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply]
    rw [qCoeff_zsmul, zsmul_eq_mul]

private theorem trunc_injective (N : ℕ) [NeZero N] (k : ℤ) :
    Function.Injective (trunc N k) := by
  refine (injective_iff_map_eq_zero _).mpr fun f hf ↦ ?_
  have hmf : (f : ModularForm (CongruenceSubgroup.Gamma0 N) k) = 0 := by
    refine ModularForm.sturm_bound_Gamma0 N _ fun n hn ↦ ?_
    have := congrFun hf ⟨n, Nat.lt_succ_of_le hn⟩
    simpa [trunc, qCoeff] using this
  have hcoe : (⇑f : ℍ → ℂ) = 0 := by
    have := congrArg (fun F : ModularForm (CongruenceSubgroup.Gamma0 N) k ↦ (⇑F : ℍ → ℂ)) hmf
    simpa using this
  exact DFunLike.coe_injective (by rw [hcoe, FunLike.coe_zero])

/-- The integral lattice is a finitely generated `ℤ`-module. Stated verbatim from
`Theorems/Thm_CuspForm_intLattice_fg.lean`. -/
theorem intLattice_fg (N : ℕ) [NeZero N] (k : ℤ) : (CuspForm.intLattice N k).FG := by
  classical
  set B := sturmB N k
  set M : Submodule ℤ (Fin (B + 1) → ℂ) :=
    Submodule.span ℤ (Set.range fun i : Fin (B + 1) ↦ (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ))
    with hM
  have hMfg : M.FG := Submodule.fg_span (Set.finite_range _)
  have hle : (CuspForm.intLattice N k).map (trunc N k) ≤ M := by
    rw [CuspForm.intLattice, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨f, hf, rfl⟩
    choose m hm using hf
    have hv : trunc N k f =
        ∑ i : Fin (B + 1), (m i) • (Pi.single i (1 : ℂ) : Fin (B + 1) → ℂ) := by
      funext j
      rw [Finset.sum_apply, Finset.sum_eq_single j, Pi.smul_apply, Pi.single_eq_same, zsmul_eq_mul,
        mul_one]
      · exact hm j
      · intro i _ hij
        rw [Pi.smul_apply, Pi.single_eq_of_ne' hij, smul_zero]
      · simp
    rw [hv]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact Submodule.fg_of_fg_map_injective (trunc N k) (trunc_injective N k) (hMfg.of_le hle)

/-- The integral lattice is free and finite over `ℤ`. Stated verbatim from
`Theorems/Thm_CuspForm_intLattice_free_and_finite.lean`. -/
theorem intLattice_free_and_finite (N : ℕ) [NeZero N] (k : ℤ) :
    Module.Free ℤ (CuspForm.intLattice N k) ∧ Module.Finite ℤ (CuspForm.intLattice N k) := by
  have : Module.Finite ℤ (CuspForm.intLattice N k) :=
    Module.Finite.iff_fg.mpr (CuspForm.intLattice_fg N k)
  have htorsV : IsAddTorsionFree (CuspForm (CongruenceSubgroup.Gamma0 N) k) := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    have h : (n : ℂ) • a = (n : ℂ) • b := by
      simpa only [Nat.cast_smul_eq_nsmul] using hab
    exact smul_right_injective _ (Nat.cast_ne_zero.mpr hn) h
  have : IsAddTorsionFree (CuspForm.intLattice N k) := by
    refine ⟨fun n hn a b hab ↦ ?_⟩
    apply Subtype.ext
    exact IsAddTorsionFree.nsmul_right_injective (M := CuspForm (CongruenceSubgroup.Gamma0 N) k) hn
      (by simpa using congrArg Subtype.val hab)
  exact ⟨inferInstance, inferInstance⟩

end CuspForm

end
