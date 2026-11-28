/-
The regular differentials of `X₁(M)` are the weight-two cusp forms, after `⊗ ℂ`.

`exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm` (329 pin lines): there is a
`ℂ`-linear equivalence between `ℂ ⊗[ℚ̄] (regular differentials of X₁(M)'s function field)` and
`CuspForm (Γ₁ M) 2`, and the `diffQExp` coefficient map is carried to the `q`-expansion along it.  This is
the dictionary's linear form — the shape a consumer wants when it adds or compares differentials — and it
is built on SET-AF107D's two rows (`exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion` in
`QExpansionDifferentialLift.lean` and its `regularDifferentials` refinement in
`X1/IntegralityDifferential.lean`), together with the finite-dimensionality of both sides
(`Canonical/RegularDifferentialsFinrank`, `Gamma1CuspStructure`) and the `Γ₁` integral basis.

The home is new: no existing `X1` module is above all eight premise modules (the `X1` family is a DAG
whose top is split between `IntegralityDifferential`, `GenusBound` and `Structure`), so the composition is
its own module.

## The rows

* `ModularCurve.exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm` — 329 pin `S_` lines.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.lean>

spec-pin: Theorems/Thm_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.lean
spec-pin: P2M/Sol/S_ModularCurve_exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm.lean

## Port notes

* **Declaration surface.** The whole `S_` block is ported, not just the headline: seventeen helpers and
  the headline, at the pin's names, with the generated label namespace
  `P2MW.S_ModularCurve_exists_linearEquiv_….X1RegDiff` replaced by the subject namespace
  `ModularCurve.X1RegDiff` (`p2m_open "ModularCurve~…"` puts the pin's block under `ModularCurve`, so
  the block keeps that prefix).  The headline's own `letI := ι₀.toAlgebra`-scoped `∃ e : ℂ ⊗[ℚ̄] … ≃ₗ[ℂ] …`
  is the scaffold's text, unchanged.
* **Gate readings.** `check_port --force` → **18 ok, 0 mismatch, 0 missing, 0 own, 0 kw** (all 18 `S_`
  rows).  Engine diff (pin sources 2: the `Theorems/` wrapper + the `S_` file): pin decls 19, module decls
  19, **18 by hash, 0 by name, 1 unaccounted** — the one is the `private` helper
  `linearIndependent_coeffMap_comp` below (a port-owned workaround, not a pin row; see the next bullet).
  `dedup --within` → 0 clusters; `move_dead --dry-run` → `0 declarations, 0 lines`; every public
  declaration's `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}` (no `sorryAx`).
* **Substitutions: none taken.** The advise's four near-matches are not usable at the pin's shapes, so the
  `S_` text is restated: the port's `one_mem_strictPeriods` (`ModularForms/PrimitiveFormExistence.lean:166`)
  and `qCoeffLin` (`ModularForms/PrimitiveFormBasis.lean:192`) are stated over `Gamma1 N : Subgroup SL(2,ℤ)`
  with an extra `(N : ℕ)` binder (the pin's `{M : ℕ}`-section form with `CongruenceSubgroup.Gamma1 M`
  coerced at `GL (Fin 2) ℝ` does not hash to them), and the port's `eq_zero_of_forall_qCoeff_eq_zero`
  (`ModularForms/PrimitiveFormExistence.lean:169`) and `eq_of_forall_qCoeff_eq`
  (`ModularForms/Gamma1CuspStructure.lean:56`) carry explicit `{N}{k}` / `{Γ}` binders.
* **One port-surface defect, worked around `private`.** `ModularCurve.linearIndependent_coeffMap_comp_of_linearIndependent`
  (`X1/CoeffMap.lean:270`) is stored with `Module κ (LaurentSeries κ)` elaborated to `Algebra.toModule`,
  while an ordinary `LinearIndependent κ f` in a consumer elaborates the same class to
  `HahnSeries.instModule`; the two are not syntactically equal, so the lemma cannot be applied at all
  (`Application type mismatch`), in any module.  Its companion
  `QExpAutBaseChange.coeff_smul'` (`X1/CoeffMap.lean:89`) is instance-fixed the same way and does not fire
  at the v4.34 `HahnSeries` module instances.  The `private` helper `linearIndependent_coeffMap_comp` is
  that lemma's proof with `HahnSeries.coeff_smul` (instance-polymorphic) in place of `coeff_smul'`; it is
  the only declaration this module owns that the wire does not have.  **Manager decision:** `X1/CoeffMap.lean`
  is another order's file, so it is reported, not edited.
* **Linters.** None silenced module-wide.
* **Heartbeat probe pair** (recorded, never installed): the module is **silent at `120000`** and hits a
  deterministic timeout at `80000` (`whnf`); it is also silent at the 200 k edit-loop cap and at `160000`.
  The full downward ladder `40000 / 20000 / 10000 / 5000 / 1000` (and the `160000 / 120000 / 80000 / 60000`
  bisection) is in `lean/tmp/af108/AF108D-REPORT.md`.  No `set_option maxHeartbeats` is installed.
-/

import FLTForHuman.AlgebraicCurve.Canonical.RegularDifferentialsFinrank
import FLTForHuman.ModularCurve.QExpansionDifferentialLift
import FLTForHuman.ModularCurve.X1.CoeffMap
import FLTForHuman.ModularCurve.X1.GenusBound
import FLTForHuman.ModularCurve.X1.IntegralityDifferential
import FLTForHuman.ModularCurve.X1.Structure
import FLTForHuman.ModularForms.Gamma1CuspStructure
import FLTForHuman.ModularForms.WeightOne.Gamma1IntegralBasis
import Mathlib.Tactic

open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace ModularCurve

/- The pin's `X1RegDiff` block: the `ℂ`-linear dictionary in five steps.  `childA`/`childB`/`childC`
move between `ℂ`-valued `q`-expansions and regular differentials (SET-AF107D's two rows);
`childE`/`childG1`/`childH` supply the finite-dimensionality and injectivity of the two sides; the
`coeffFun`/`coeffFunC` family reads a `ℂ ⊗[ℚ̄]` differential off its `n`-th Laurent coefficient; and
`main` builds `Ψ` from a `ℚ̄`-rational `q`-coefficient basis, proves it injective by coefficient
separation and surjective by the `childC` generation, and reads the `q`-expansion statement off the
left inverse. -/
namespace X1RegDiff

open ModularForm ModularFormClass Complex
open UpperHalfPlane hiding I

local notation "𝕢" => Function.Periodic.qParam
local notation "ℚ̄" => AlgebraicClosure ℚ

section Children

theorem childA (M : ℕ) [NeZero M] (ι₀ : ℚ̄ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (hf : ∀ n : ℕ, (qExpansion 1 ⇑f).coeff n ∈ ι₀.range) :
    ∃ ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄],
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) :=
  ModularCurve.exists_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion M ι₀ f hf

theorem childB (M : ℕ) [NeZero M] (ι₀ : ℚ̄ →+* ℂ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2)
    (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])
    (hω : coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f)) :
    ω ∈ AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M) :=
  ModularCurve.mem_regularDifferentials_x1FunctionFieldBar_of_coeffMap_diffQExp_eq_qExpansion M ι₀ f ω hω

theorem childC (M : ℕ) [NeZero M] (ι₀ : ℚ̄ →+* ℂ) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])
    (hω : ω ∈ AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) ω) = HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑f) :=
  ModularCurve.exists_cuspForm_coeffMap_diffQExp_x1FunctionFieldBar_eq_qExpansion_of_mem_regularDifferentials M ι₀ ω hω

theorem childE (M : ℕ) [NeZero M] :
    Module.Finite ℚ̄ ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) := by
  have := ModularCurve.isCurveOver_x1FunctionFieldBar M
  have := ModularCurve.essFiniteType_x1FunctionFieldBar M
  have := ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar M
  exact (AlgebraicCurve.finite_and_finrank_regularDifferentials_eq_genus (K := ℚ̄) (F := ↥(x1FunctionFieldBar M))).1

theorem childG1 (M : ℕ) [NeZero M] :
    Function.Injective (diffQExp (x1FunctionFieldBar M) : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄] → LaurentSeries ℚ̄) :=
  ModularCurve.diffQExp_x1FunctionFieldBar_injective M

theorem childH (M : ℕ) [NeZero M] : FiniteDimensional ℂ (CuspForm (CongruenceSubgroup.Gamma1 M) 2) :=
  CuspForm.finiteDimensional_Gamma1 M 2

end Children

section Gamma1

variable {M : ℕ} {k : ℤ}

lemma one_mem_strictPeriods :
    (1 : ℝ) ∈ (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  simp

lemma hasSum_qCoeff (f : CuspForm (CongruenceSubgroup.Gamma1 M) k) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m * 𝕢 1 τ ^ m) (f τ) := by
  have : Fact (_root_.IsCusp OnePoint.infty (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos one_mem_strictPeriods⟩
  have := hasSum_qExpansion one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f) τ
  exact this

lemma eq_zero_of_forall_qCoeff_eq_zero (f : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (h : ∀ n, qCoeff f n = 0) : f = 0 := by
  refine DFunLike.ext _ _ fun τ => ?_
  have hs := hasSum_qCoeff f τ
  have hz : (fun m ↦ qCoeff f m * 𝕢 1 τ ^ m) = fun _ => 0 := by
    funext m
    rw [h m, zero_mul]
  rw [hz] at hs
  simpa using hs.unique hasSum_zero

lemma eq_of_forall_qCoeff_eq (f g : CuspForm (CongruenceSubgroup.Gamma1 M) k)
    (h : ∀ n, qCoeff f n = qCoeff g n) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_qCoeff_eq_zero _ fun n => ?_
  simp only [qCoeff, FunLike.coe_sub]
  rw [ModularForm.qExpansion_sub one_pos one_mem_strictPeriods f g, map_sub, sub_eq_zero]
  exact h n

end Gamma1

section S2side

variable (M : ℕ)

def qCoeffLin (n : ℕ) : CuspForm (CongruenceSubgroup.Gamma1 M) 2 →ₗ[ℂ] ℂ where
  toFun f := qCoeff f n
  map_add' f g := by
    simp only [qCoeff, FunLike.coe_add]
    rw [ModularForm.qExpansion_add one_pos (one_mem_strictPeriods (M := M)), map_add]
  map_smul' c f := by
    simp only [qCoeff, FunLike.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [ModularForm.qExpansion_smul one_pos (one_mem_strictPeriods (M := M)) c f]
    simp

@[scoped simp] lemma qCoeffLin_apply (n : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2) :
    qCoeffLin M n f = qCoeff f n := rfl

end S2side

section Coeff

variable (M : ℕ) [NeZero M]

def coeffFun (n : ℕ) : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) →ₗ[ℚ̄] ℚ̄ where
  toFun ω := (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])).coeff (n : ℤ)
  map_add' ω₁ ω₂ := by
    simp only [Submodule.coe_add, map_add, HahnSeries.coeff_add]
  map_smul' c ω := by
    simp only [Submodule.coe_smul, RingHom.id_apply, smul_eq_mul]
    rw [← algebraMap_smul (x1FunctionFieldBar M) c (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄]), map_smul]
    change (((algebraMap ℚ̄ (x1FunctionFieldBar M) c : x1FunctionFieldBar M) :
        LaurentSeries ℚ̄) * diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])).coeff (n : ℤ) = _
    change (algebraMap ℚ̄ (LaurentSeries ℚ̄) c * _).coeff _ = _
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul]

omit [NeZero M] in
@[scoped simp] theorem coeffFun_apply (n : ℕ) (ω : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M))) :
    coeffFun M n ω = (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])).coeff (n : ℤ) := rfl

variable [Algebra ℚ̄ ℂ]

def coeffFunC (n : ℕ) : ℂ ⊗[ℚ̄] ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) →ₗ[ℂ] ℂ :=
  (Algebra.TensorProduct.lmul'' ℚ̄ (S := ℂ)).toLinearMap ∘ₗ
    (((Algebra.linearMap ℚ̄ ℂ).comp (coeffFun M n)).baseChange ℂ)

omit [NeZero M] in
theorem coeffFunC_tmul (n : ℕ) (c : ℂ) (ω : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M))) :
    coeffFunC M n (c ⊗ₜ ω) =
      c * algebraMap ℚ̄ ℂ ((diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])).coeff (n : ℤ)) := by
  simp [coeffFunC, LinearMap.baseChange_tmul]
  rfl

end Coeff

/-- The pin's `linearIndependent_coeffMap_comp_of_linearIndependent`, at the `Module` instance this
file's `hLIq` is stated with.  The port's `X1/CoeffMap.lean` copy is stored at a different `Module κ
(LaurentSeries κ)` instance (elaborated there as `Algebra.toModule`), so it cannot be applied to a
`LinearIndependent` produced here; this is its proof, with `QExpAutBaseChange.coeff_smul'` (likewise
instance-fixed) replaced by the instance-polymorphic `HahnSeries.coeff_smul`.  `private`: not a pin row. -/
private theorem linearIndependent_coeffMap_comp {κ k : Type*} [Field κ] [Field k] [Algebra κ k]
    {n : ℕ} (f : Fin n → LaurentSeries κ) (hf : LinearIndependent κ f) :
    LinearIndependent k (⇑(coeffMap (algebraMap κ k)) ∘ f) := by
  classical
  rw [Fintype.linearIndependent_iff] at hf ⊢
  intro c hc i₀
  let B := Module.Basis.ofVectorSpace κ k
  have hcomb : ∀ j, ∑ i, (B.repr (c i) j) • f i = 0 := by
    intro j
    ext m
    have hm : ∑ i, ((f i).coeff m) • c i = 0 := by
      have h0 := congrArg (fun x : LaurentSeries k => x.coeff m) hc
      simp only [HahnSeries.coeff_zero, HahnSeries.coeff_sum, Function.comp_apply,
        HahnSeries.coeff_smul, coeffMap_coeff, smul_eq_mul] at h0
      rw [← h0]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, mul_comm]
    have hj := congrArg (fun x : k => B.repr x j) hm
    simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, map_zero, Finsupp.coe_zero, Pi.zero_apply] at hj
    rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
    simp only [HahnSeries.coeff_smul, smul_eq_mul]
    rw [← hj]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hzero : ∀ j, B.repr (c i₀) j = 0 := fun j => hf _ (hcomb j) i₀
  have hrepr : B.repr (c i₀) = 0 := Finsupp.ext hzero
  simpa using congrArg B.repr.symm hrepr

section Main

variable (M : ℕ) [NeZero M]

theorem main (ι₀ : ℚ̄ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[ℚ̄] ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) ≃ₗ[ℂ] CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ∀ ω : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)),
        coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(e (1 ⊗ₜ ω))) := by
  let : Algebra ℚ̄ ℂ := ι₀.toAlgebra
  have := childH M
  have := childE M

  obtain ⟨n, b, hb⟩ := CuspForm.exists_basis_gamma1_qCoeff_mem_range_ratCast M 2

  have hω : ∀ i : Fin n, ∃ ω : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)),
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (ω : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])) =
        HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 ⇑(b i)) := by
    intro i
    have hrange : ∀ m : ℕ, (qExpansion 1 ⇑(b i)).coeff m ∈ ι₀.range := by
      intro m
      obtain ⟨r, hr⟩ := hb i m
      refine ⟨r, ?_⟩
      rw [map_ratCast, hr]
      rfl
    obtain ⟨ω, hωq⟩ := childA M ι₀ (b i) hrange
    exact ⟨⟨ω, childB M ι₀ (b i) ω hωq⟩, hωq⟩
  choose ω hω using hω

  let Ψ : CuspForm (CongruenceSubgroup.Gamma1 M) 2 →ₗ[ℂ] ℂ ⊗[ℚ̄] ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) :=
    b.constr ℂ fun i => (1 : ℂ) ⊗ₜ[ℚ̄] ω i
  have hΨb : ∀ i, Ψ (b i) = (1 : ℂ) ⊗ₜ[ℚ̄] ω i := fun i => by
    simp only [Ψ, Module.Basis.constr_basis]

  have hQω : ∀ (i : Fin n) (m : ℕ), coeffFunC M m ((1 : ℂ) ⊗ₜ[ℚ̄] ω i) = qCoeff (b i) m := by
    intro i m
    rw [coeffFunC_tmul, one_mul]
    have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) (hω i)
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
    exact h
  have hQΨ : ∀ (m : ℕ) (f : CuspForm (CongruenceSubgroup.Gamma1 M) 2), coeffFunC M m (Ψ f) = qCoeff f m := by
    intro m
    have hcomp : (coeffFunC M m).comp Ψ = qCoeffLin M m := by
      refine b.ext fun i => ?_
      rw [LinearMap.comp_apply, hΨb, hQω, qCoeffLin_apply]
    intro f
    simpa using LinearMap.congr_fun hcomp f

  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro f hf
    refine eq_zero_of_forall_qCoeff_eq_zero f fun m => ?_
    rw [← hQΨ m f, LinearMap.mem_ker.mp hf, map_zero]

  have hsep : ∀ x : ℂ ⊗[ℚ̄] ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)),
      (∀ m : ℕ, coeffFunC M m x = 0) → x = 0 := by
    intro x hx

    let Bq := Module.finBasis ℚ̄ ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M))
    let BC := Algebra.TensorProduct.basis ℂ Bq
    have hBC : ∀ i, BC i = (1 : ℂ) ⊗ₜ[ℚ̄] Bq i := fun i => Algebra.TensorProduct.basis_apply Bq i
    obtain ⟨c, rfl⟩ : ∃ c : Fin _ → ℂ, x = ∑ i, c i • BC i := ⟨fun i => BC.repr x i, (BC.sum_repr x).symm⟩

    let g : Fin _ → LaurentSeries ℂ := fun i =>
      coeffMap ι₀ (diffQExp (x1FunctionFieldBar M) (Bq i : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄]))
    have hgps : ∀ i, ∃ p : PowerSeries ℂ, g i = HahnSeries.ofPowerSeries ℤ ℂ p := fun i => by
      obtain ⟨f, hf⟩ := childC M ι₀ (Bq i : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄]) (Bq i).2
      exact ⟨_, hf⟩
    have hLIq : LinearIndependent ℚ̄ (fun i => diffQExp (x1FunctionFieldBar M) (Bq i : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])) := by

      let Θq : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄] →ₗ[ℚ̄] LaurentSeries ℚ̄ := (diffQExp (x1FunctionFieldBar M)).restrictScalars ℚ̄
      have h1 : LinearIndependent ℚ̄ (fun i => ((Bq i : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M))) :
          Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])) :=
        Bq.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
      have h2 := h1.map' Θq (LinearMap.ker_eq_bot.mpr (childG1 M))
      exact h2
    have hLI : LinearIndependent ℂ g := by
      have := linearIndependent_coeffMap_comp (κ := ℚ̄) (k := ℂ)
        (fun i => diffQExp (x1FunctionFieldBar M) (Bq i : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄])) hLIq
      exact this

    have hsum : ∑ i, c i • g i = 0 := by
      ext m
      rw [HahnSeries.coeff_sum, HahnSeries.coeff_zero]
      simp only [HahnSeries.coeff_smul, smul_eq_mul]
      rcases le_or_gt 0 m with hm | hm
      · obtain ⟨m', rfl⟩ := Int.eq_ofNat_of_zero_le hm
        have h0 := hx m'
        rw [map_sum] at h0
        simp only [map_smul, hBC, coeffFunC_tmul, one_mul, smul_eq_mul] at h0

        convert h0 using 2 with i
        all_goals first | with_reducible_and_instances rfl | rfl
      · apply Finset.sum_eq_zero
        intro i _
        obtain ⟨p, hp⟩ := hgps i
        have hr : m ∉ Set.range (fun m : ℕ => (m : ℤ)) := by
          rintro ⟨m'', hm''⟩
          simp only at hm''
          omega
        rw [hp, HahnSeries.ofPowerSeries_apply, HahnSeries.embDomain_of_notMem_range hr, mul_zero]
    have hc : ∀ i, c i = 0 := fun i => Fintype.linearIndependent_iff.mp hLI c hsum i
    simp [hc]
  have hsurj : Function.Surjective Ψ := by
    have hgen : ∀ ω' : ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)),
        (1 : ℂ) ⊗ₜ[ℚ̄] ω' ∈ LinearMap.range Ψ := by
      intro ω'
      obtain ⟨fω, hfω⟩ := childC M ι₀ (ω' : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄]) ω'.2
      refine ⟨fω, ?_⟩
      rw [← sub_eq_zero]
      refine hsep _ fun m => ?_
      rw [map_sub, hQΨ, coeffFunC_tmul, one_mul, sub_eq_zero]
      have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) hfω
      simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
      exact h.symm
    rw [← LinearMap.range_eq_top, eq_top_iff]
    rintro x -
    induction x using TensorProduct.inductionOn with
    | tmul c ω' =>
      have : c ⊗ₜ[ℚ̄] ω' = c • ((1 : ℂ) ⊗ₜ[ℚ̄] ω') := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ c (hgen ω')
    | add x y hx hy => exact Submodule.add_mem _ hx hy

  let e₀ : CuspForm (CongruenceSubgroup.Gamma1 M) 2 ≃ₗ[ℂ] ℂ ⊗[ℚ̄] ↥(AlgebraicCurve.regularDifferentials ℚ̄ ↥(x1FunctionFieldBar M)) :=
    LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩
  refine ⟨e₀.symm, fun ω' => ?_⟩
  obtain ⟨fω, hfω⟩ := childC M ι₀ (ω' : Ω[↥(x1FunctionFieldBar M)⁄ℚ̄]) ω'.2
  have hfeq : e₀.symm ((1 : ℂ) ⊗ₜ[ℚ̄] ω') = fω := by
    apply eq_of_forall_qCoeff_eq
    intro m
    have he : Ψ (e₀.symm ((1 : ℂ) ⊗ₜ[ℚ̄] ω')) = (1 : ℂ) ⊗ₜ[ℚ̄] ω' := e₀.apply_symm_apply _
    rw [← hQΨ m, he, coeffFunC_tmul, one_mul]
    have h := congrArg (fun x : LaurentSeries ℂ => x.coeff (m : ℤ)) hfω
    simp only [coeffMap_coeff, HahnSeries.ofPowerSeries_apply_coeff] at h
    exact h
  rw [hfeq]
  exact hfω

end Main

end X1RegDiff

open scoped TensorProduct in
theorem exists_linearEquiv_tensor_regularDifferentials_x1FunctionFieldBar_cuspForm
    (M : ℕ) [NeZero M] (ι₀ : AlgebraicClosure ℚ →+* ℂ) :
    letI := ι₀.toAlgebra
    ∃ e : ℂ ⊗[AlgebraicClosure ℚ]
          ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
              ↥(ModularCurve.x1FunctionFieldBar M)) ≃ₗ[ℂ]
        CuspForm (CongruenceSubgroup.Gamma1 M) 2,
      ∀ ω : ↥(AlgebraicCurve.regularDifferentials (AlgebraicClosure ℚ)
          ↥(ModularCurve.x1FunctionFieldBar M)),
        ModularCurve.coeffMap ι₀
            (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
              (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ])) =
          HahnSeries.ofPowerSeries ℤ ℂ (UpperHalfPlane.qExpansion 1 ⇑(e (1 ⊗ₜ ω))) :=
  X1RegDiff.main M ι₀

end ModularCurve
