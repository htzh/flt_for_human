/-
The semisimple-representation criterion from Frobenius trace/determinant ranges.

Let `ρ : Γ_ℚ → GL₂ Ω` be a Galois representation over an algebraically closed field `Ω` that
factors through a finite level, and suppose that at every prime `p` outside a finite set `S`,
at every prime `A` of `ℚ̄` above `p`, for every Frobenius `σ` at `A`, both the trace and the
determinant of `ρ σ` lie in the image of a residue field `κ ↪ Ω`.  Then `ρ` has a model
`ρ₀ : Γ_ℚ → GL₂ κ` over `κ` which

* factors through a finite level,
* is **semisimple** as a `matrixRepresentation`,
* has the same kernel as `ρ` (`ρ σ = 1 ↔ ρ₀ σ = 1`), and
* has the same characteristic polynomial after `κ ↪ Ω` at every `σ`.

This is the descent step that turns an `Ω`-representation with rational trace/determinant data
into a semisimple `κ`-representation: the charpolys of the Frobenius elements generate the
invariant ring, Brauer–Nesbitt plus the trace/determinant range condition give semisimplicity,
and the finite-level condition makes the descent a finite-dimensional algebra computation.

Alongside it, the two `ValuationSubring` leaves the criterion's hypothesis is stated in:
`IsFrobeniusAt.apply_eq_pow_of_pow_eq_one` (a Frobenius at `A` acts on `m`-torsion roots of unity
by `q`-th powers when `m` is coprime to the residue characteristic) and
`charP_residueField_of_liesOverPrime` (the residue field of a prime above `ℓ` has characteristic
`ℓ`).  Their vocabulary — `A.LiesOverPrime q`, `A.IsFrobeniusAt σ q` — lives in
`GaloisRep/Defs/{Ramification,FrobeniusTrace}.lean`, which is why they are homed here rather
than in a `FieldTheory` module.

The engine is `GaloisRep/SemisimpleDescent.lean` (the desingularisation of a matrix
representation by charpoly data), `ModularCurve/ResidualDescent.lean` (the finite-level descent)
and `NumberTheory/FrobeniusDensity/PrimeIsFrobeniusAtConjPow.lean` (the Frobenius-conjugacy
arithmetic), plus `Definitions/Deformations_MatrixRepresentation`'s
`Deformation.matrixRepresentation.IsSemisimpleRepresentation`.

## The port (SET-AF105, order D)

The pin's generated namespace label `P2MW.S_GaloisRep_…` and its inner label `DSRt` both come
off, as in `DeligneSerre`'s port (whose pin's inner label `DSRed` was dropped the same way): the
engine is `namespace GaloisRep`, the two leaves keep their root names
(`ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one`,
`ValuationSubring.charP_residueField_of_liesOverPrime`), and the headline is the wrapper's
`GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range`.

**Substitutions (imported, not transcribed) — 4 of the main pin's 30 engine rows:**

* `charpoly_fin_two`, `finrank_eq_one_of_ne_bot_of_ne_top`,
  `isSemisimpleRepresentation_of_forall_exists_isCompl` → `DeligneSerre.…`, homed **publicly**
  at the pin's names in `GaloisRep/SemisimpleDescent.lean` for exactly this deferred half
  (byte-identical statements; the pin duplicates them between the two `S_` nodes);
* `finite_range_of_factorsThroughFiniteLevel` → `GaloisRep.…` in `GaloisRep/Prelude.lean`
  (already public, same mathematics stated as `Finite (MonoidHom.range ρ)` rather than
  `(Set.range M).Finite`; FR-0274 forbids a second public declaration of the name, so
  `finite_range_linRep` bridges the two). This fourth row is *not* one of the three the order
  lists — it surfaced as an existing public port declaration with the pin's last name.

`spec-pin:` wires all three rows; `check_port --force` reads **29 ok / 0 mismatch / 0 missing /
0 own / 0 kw** (33 pin rows − 4 substituted; the two leaves verify against the `Theorems/`
wrappers, the headline against the wrapper's `solution`). Engine diff over the three `S_` pins:
pin sources 3 (+3 `Theorems/`), pin decls 33, module decls 29 — **26 by statement hash, 0 by name
only, 3 unaccounted** (the two leaves and the headline, which the pins name `solution`; all three
read `ok` against the `Theorems/` wires). `#print axioms`: all 29 public declarations are
`[propext, Classical.choice, Quot.sound]`, no `sorryAx`. `dedup --within`: 0 clusters.
`move_dead --dry-run`: 0 declarations, 0 lines. Silent at the edit loop, one locked
`lake build` with 0 warning lines from this file.

**Heartbeat probe pair (recorded, never installed; FR-0225).** The edit loop's cap is 200000;
the downward bisector `40000 / 20000 / 10000 / 5000` reads: silent at 200000, 40000 and 20000;
at 10000 the first failure is `GaloisRep.main` at the case-B charpoly normalisation
(`simp only [χ₁, χ₂, map_add, map_mul]`, the line after `rw [hcp, …]`); at 5000 the first
failure is `GaloisRep.trace_mem_and_det_mem` at `rw [hval, Matrix.trace_units_conj]`. So the
module floor lies between 10000 and 20000 heartbeats — the residual is nowhere near the
lakefile's 4 M bound, and no `set_option maxHeartbeats` (module or instance) is carried. The
pin's `attribute [-instance]` / `attribute [-simp]` wall is not transcribed.

References (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one.lean>
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_ValuationSubring_charP_residueField_of_liesOverPrime.lean>

spec-pin: Theorems/Thm_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.lean
spec-pin: Theorems/Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one.lean
spec-pin: Theorems/Thm_ValuationSubring_charP_residueField_of_liesOverPrime.lean
spec-pin: P2M/Sol/S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.lean
spec-pin: P2M/Sol/S_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one.lean
spec-pin: P2M/Sol/S_ValuationSubring_charP_residueField_of_liesOverPrime.lean
-/
import FLTForHuman.GaloisRep.Defs.FrobeniusTrace
import FLTForHuman.GaloisRep.Defs.Ramification
import FLTForHuman.GaloisRep.Defs.Residual
import FLTForHuman.GaloisRep.Deformation.Charpoly
import FLTForHuman.GaloisRep.Deformation.FiniteDescent
import FLTForHuman.GaloisRep.SemisimpleDescent
import FLTForHuman.ModularCurve.ResidualDescent
import FLTForHuman.NumberTheory.FrobeniusDensity.PrimeIsFrobeniusAtConjPow
import FLTForHuman.GaloisRep.Defs.MatrixRepresentation
import FLTForHuman.GaloisRep.Prelude
import Mathlib.FieldTheory.KrullTopology
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Determinant
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic

noncomputable section

set_option autoImplicit false

-- The pin's proofs introduce instances with `haveI` in `Prop` goals, and `include`d section
-- variables are sometimes unused by an individual declaration; both are transcribed verbatim,
-- as in `GaloisRep/SemisimpleDescent.lean` and `GaloisRep/ConjFromFrobenius.lean`.
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open Polynomial

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace GaloisRep

/-! ## The two-by-two Cayley–Hamilton engine -/

section TwoByTwo

variable {K : Type*} [CommRing K]

/-- The traces of the first `n+1` powers of a `2 × 2` matrix are determined by its trace
and determinant. -/
theorem trace_pow_mem (S : Subring K) (A : Matrix (Fin 2) (Fin 2) K) (ht : A.trace ∈ S) (hd : A.det ∈ S)
    (n : ℕ) : (A ^ n).trace ∈ S ∧ (A ^ (n + 1)).trace ∈ S := by
  induction n with
  | zero =>
    refine ⟨?_, by simpa using ht⟩
    rw [pow_zero, Matrix.trace_one, Fintype.card_fin]
    exact_mod_cast natCast_mem S 2
  | succ n ih =>
    refine ⟨ih.2, ?_⟩

    have hCH : A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have h := Matrix.aeval_self_charpoly A
      rw [DeligneSerre.charpoly_fin_two] at h
      simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        Algebra.algebraMap_eq_smul_one] at h
      rw [sq, smul_one_mul] at h
      have : A * A - A.trace • A + A.det • (1 : Matrix (Fin 2) (Fin 2) K) = 0 := h
      rw [← sub_eq_zero]; rw [← this]; abel
    have : A ^ (n + 1 + 1) = A.trace • A ^ (n + 1) - A.det • A ^ n := by
      rw [pow_succ, pow_succ, mul_assoc, hCH, mul_sub, mul_smul_comm, mul_smul_comm, mul_one, ← pow_succ]
    rw [this, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]
    exact S.sub_mem (S.mul_mem ht ih.2) (S.mul_mem hd ih.1)

end TwoByTwo

/-! ## Finite level: an open kernel -/

theorem isOpen_ker_of_factorsThroughFiniteLevel {X : Type} [Group X] (M : Γℚ →* X)
    (hM : GaloisFactorsThroughFiniteLevel M) : IsOpen (M.ker : Set Γℚ) := by
  obtain ⟨L', hfd, hker⟩ := hM
  haveI := hfd
  apply Subgroup.isOpen_mono (H₁ := L'.fixingSubgroup) _ (IntermediateField.fixingSubgroup_isOpen L')
  intro σ hσ
  rw [MonoidHom.mem_ker]
  exact hker σ (fun x hx => hσ ⟨x, hx⟩)

/-! ## Chebotarev: the trace and determinant at *every* element -/

section Chebotarev

variable {Ω : Type} [Field Ω] (S : Subring Ω) (ρ : Γℚ →* GL (Fin 2) Ω)
  (hρ : GaloisFactorsThroughFiniteLevel ρ) (T : Finset ℕ)
  (hfrob : ∀ p : ℕ, p.Prime → p ∉ T →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
        Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ S ∧ Matrix.det (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ S)

include hρ hfrob

theorem trace_mem_and_det_mem (σ : Γℚ) :
    Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ S ∧ Matrix.det (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ S := by
  classical

  set M : ℕ := ∏ s ∈ T, max s 1 with hM
  have hMpos : 0 < M := Finset.prod_pos fun s _ => lt_max_of_lt_right one_pos
  have hdvd : ∀ p : ℕ, p.Prime → ¬ p ∣ M → p ∉ T := by
    intro p hp hpM hpT
    apply hpM
    have : max p 1 = p := max_eq_left hp.one_lt.le
    rw [hM, ← this]
    exact Finset.dvd_prod_of_mem _ hpT
  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓM, hA, hτ, hmem⟩ :=
    Subgroup.exists_prime_isFrobeniusAt_conj_pow_mem_of_isOpen ρ.ker
      (isOpen_ker_of_factorsThroughFiniteLevel ρ hρ) σ hMpos
  obtain ⟨hτt, hτd⟩ := hfrob ℓ hℓ (hdvd ℓ hℓ hℓM) A hA τ hτ

  have hσ : ρ σ = ρ g * ρ τ ^ n * (ρ g)⁻¹ := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, mul_inv_eq_one] at hmem
    exact hmem.symm
  have hval : (ρ σ : Matrix (Fin 2) (Fin 2) Ω) =
      (ρ g : Matrix (Fin 2) (Fin 2) Ω) * (ρ τ : Matrix (Fin 2) (Fin 2) Ω) ^ n * ((ρ g)⁻¹ : GL (Fin 2) Ω) := by
    rw [hσ]; simp [Units.val_pow_eq_pow_val]
  constructor
  · rw [hval, Matrix.trace_units_conj]
    rcases n with _ | n
    · rw [pow_zero, Matrix.trace_one, Fintype.card_fin]; exact_mod_cast natCast_mem S 2
    · exact (trace_pow_mem S _ hτt hτd n).2
  · rw [hval, Matrix.det_units_conj, Matrix.det_pow]
    exact S.pow_mem hτd n

end Chebotarev

/-! ## The linear representation attached to a matrix representation -/

section LinRep

variable {Ω : Type} [Field Ω] (ρ : Γℚ →* GL (Fin 2) Ω)

noncomputable def linRep : Γℚ →* ((Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv Ω (Fin 2 → Ω)).toMonoidHom.comp
    (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρ)

theorem linRep_toLinearMap (σ : Γℚ) :
    ((linRep ρ σ : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) =
      (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVecLin := by
  simp only [linRep, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap]
  exact Matrix.GeneralLinearGroup.coe_toLin _

theorem linRep_apply (σ : Γℚ) (v : Fin 2 → Ω) :
    linRep ρ σ v = (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v := by
  have := congrArg (fun f : (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω) => f v) (linRep_toLinearMap ρ σ)
  simpa using this

theorem trace_linRep (σ : Γℚ) :
    LinearMap.trace Ω _ ((linRep ρ σ : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) =
      Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) Ω) := by
  rw [linRep_toLinearMap, ← Matrix.toLin'_apply', LinearMap.trace_eq_matrix_trace Ω (Pi.basisFun Ω (Fin 2)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

theorem det_linRep (σ : Γℚ) :
    LinearMap.det ((linRep ρ σ : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) : (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) =
      Matrix.det (ρ σ : Matrix (Fin 2) (Fin 2) Ω) := by
  rw [linRep_toLinearMap, ← Matrix.toLin'_apply', LinearMap.det_toLin']

theorem linRep_eq_one {σ : Γℚ} (h : ρ σ = 1) : linRep ρ σ = 1 := by
  simp [linRep, h]

theorem finite_range_linRep (hρ : GaloisFactorsThroughFiniteLevel ρ) : Finite (linRep ρ).range := by
  have hfin : (Set.range ρ).Finite :=
    MonoidHom.coe_range ρ ▸ finite_range_of_factorsThroughFiniteLevel ρ hρ
  have : Set.range (linRep ρ) =
      (fun x => (LinearMap.GeneralLinearGroup.generalLinearEquiv Ω (Fin 2 → Ω))
        (Matrix.GeneralLinearGroup.toLin x)) '' Set.range ρ := by
    ext y; simp [linRep]
  have hfin' : (Set.range (linRep ρ)).Finite := by rw [this]; exact hfin.image _
  exact (MonoidHom.coe_range (linRep ρ) ▸ hfin').to_subtype

end LinRep

/-! ## The stable-line case: two characters -/

section StableLine

variable {Ω : Type} [Field Ω] (ρ : Γℚ →* GL (Fin 2) Ω)
  {v₀ : Fin 2 → Ω} (hv₀ : v₀ ≠ 0)
  (hstab : ∀ σ : Γℚ, ∃ c : Ω, (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = c • v₀)

include hv₀ hstab

theorem eigen_unique {σ : Γℚ} {c c' : Ω} (hc : (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = c • v₀)
    (hc' : (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = c' • v₀) : c = c' :=
  smul_left_injective Ω hv₀ (hc.symm.trans hc')

theorem eigen_ne_zero {σ : Γℚ} {c : Ω} (hc : (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = c • v₀) : c ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hc
  apply hv₀
  have := congrArg (((ρ σ)⁻¹ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).mulVec hc
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_zero, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at this

noncomputable def chi1 : Γℚ →* Ωˣ where
  toFun σ := Units.mk0 (hstab σ).choose (eigen_ne_zero ρ hv₀ hstab (hstab σ).choose_spec)
  map_one' := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_one]
    apply eigen_unique ρ hv₀ hstab (hstab 1).choose_spec
    rw [map_one, Units.val_one, Matrix.one_mulVec, one_smul]
  map_mul' σ τ := by
    apply Units.ext
    simp only [Units.val_mk0, Units.val_mul]
    set cσ := (hstab σ).choose
    set cτ := (hstab τ).choose
    set cστ := (hstab (σ * τ)).choose
    have h1 : (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = cσ • v₀ := (hstab σ).choose_spec
    have h2 : (ρ τ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = cτ • v₀ := (hstab τ).choose_spec
    have h12 : (ρ (σ * τ) : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = cστ • v₀ := (hstab (σ * τ)).choose_spec
    apply eigen_unique ρ hv₀ hstab h12
    rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, h2, Matrix.mulVec_smul, h1, smul_smul, mul_comm]

theorem chi1_spec (σ : Γℚ) : (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v₀ = (chi1 ρ hv₀ hstab σ : Ω) • v₀ :=
  (hstab σ).choose_spec

noncomputable def chi2 : Γℚ →* Ωˣ :=
  (Matrix.GeneralLinearGroup.det.comp ρ) / chi1 ρ hv₀ hstab

theorem chi1_mul_chi2 (σ : Γℚ) :
    (chi1 ρ hv₀ hstab σ : Ω) * chi2 ρ hv₀ hstab σ = Matrix.det (ρ σ : Matrix (Fin 2) (Fin 2) Ω) := by
  simp only [chi2, MonoidHom.div_apply, MonoidHom.coe_comp, Function.comp_apply, Units.val_div_eq_div_val,
    Matrix.GeneralLinearGroup.val_det_apply]
  rw [mul_div_cancel₀ _ (chi1 ρ hv₀ hstab σ).ne_zero]

theorem chi1_add_chi2 (σ : Γℚ) :
    (chi1 ρ hv₀ hstab σ : Ω) + chi2 ρ hv₀ hstab σ = Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) Ω) := by
  set A : Matrix (Fin 2) (Fin 2) Ω := (ρ σ : Matrix (Fin 2) (Fin 2) Ω)
  set c : Ω := (chi1 ρ hv₀ hstab σ : Ω)

  have hsc : (Matrix.scalar (Fin 2) c).mulVec v₀ = c • v₀ := by
    ext i; simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have hker : (Matrix.scalar (Fin 2) c - A).mulVec v₀ = 0 := by
    rw [Matrix.sub_mulVec, hsc, chi1_spec ρ hv₀ hstab σ, sub_self]
  have hdet : (Matrix.scalar (Fin 2) c - A).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.mp ⟨v₀, hv₀, hker⟩
  have hroot : c ^ 2 - A.trace * c + A.det = 0 := by
    have h := Matrix.eval_charpoly A c
    rw [hdet, DeligneSerre.charpoly_fin_two] at h
    simpa using h
  have hc0 : c ≠ 0 := (chi1 ρ hv₀ hstab σ).ne_zero
  have h2 : (chi2 ρ hv₀ hstab σ : Ω) = A.det / c := by
    rw [eq_div_iff hc0, mul_comm]; exact chi1_mul_chi2 ρ hv₀ hstab σ
  rw [h2]
  have : A.det / c = A.trace - c := by rw [div_eq_iff hc0]; linear_combination hroot
  rw [this]; ring

theorem chi1_eq_one {σ : Γℚ} (h : ρ σ = 1) : chi1 ρ hv₀ hstab σ = 1 := by
  apply Units.ext
  rw [Units.val_one]
  apply eigen_unique ρ hv₀ hstab (chi1_spec ρ hv₀ hstab σ)
  rw [h, Units.val_one, Matrix.one_mulVec, one_smul]

theorem chi2_eq_one {σ : Γℚ} (h : ρ σ = 1) : chi2 ρ hv₀ hstab σ = 1 := by
  have h1 := chi1_eq_one ρ hv₀ hstab h
  simp only [chi2, MonoidHom.div_apply, h1, div_one, MonoidHom.coe_comp, Function.comp_apply, h, map_one]

end StableLine

/-! ## Transport through a `κ`-basis -/

section Transport

variable {κ : Type} [Field κ] {V₀ : Type} [AddCommGroup V₀] [Module κ V₀]
  (b : Module.Basis (Fin 2) κ V₀) (ρ₀ : Γℚ →* (V₀ ≃ₗ[κ] V₀))

noncomputable def matRep : Γℚ →* GL (Fin 2) κ :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom).comp
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv κ V₀).symm.toMonoidHom.comp ρ₀)

theorem matRep_val (σ : Γℚ) :
    ((matRep b ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ) =
      LinearMap.toMatrix b b ((ρ₀ σ : V₀ ≃ₗ[κ] V₀) : V₀ →ₗ[κ] V₀) := by
  simp only [matRep, MonoidHom.coe_comp, Function.comp_apply, Units.coe_map,
    MulEquiv.coe_toMonoidHom]
  rfl

theorem matRep_mulVec (σ : Γℚ) (v : V₀) :
    ((matRep b ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).mulVec (b.equivFun v) =
      b.equivFun (ρ₀ σ v) := by
  rw [matRep_val]
  have := LinearMap.toMatrix_mulVec_repr b b ((ρ₀ σ : V₀ ≃ₗ[κ] V₀) : V₀ →ₗ[κ] V₀) v
  simpa [Module.Basis.equivFun_apply] using this

theorem matRep_eq_one {σ : Γℚ} (h : ρ₀ σ = 1) : matRep b ρ₀ σ = 1 := by
  simp [matRep, h]

theorem charpoly_matRep (σ : Γℚ) :
    ((matRep b ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).charpoly =
      X ^ 2 - C (LinearMap.trace κ V₀ ((ρ₀ σ : V₀ ≃ₗ[κ] V₀) : V₀ →ₗ[κ] V₀)) * X +
        C (LinearMap.det ((ρ₀ σ : V₀ ≃ₗ[κ] V₀) : V₀ →ₗ[κ] V₀)) := by
  rw [DeligneSerre.charpoly_fin_two, matRep_val, ← LinearMap.trace_eq_matrix_trace κ b, LinearMap.det_toMatrix]

theorem matRep_isSemisimple
    (hcompl : ∀ W : Submodule κ V₀, (∀ σ, ∀ v ∈ W, ρ₀ σ v ∈ W) →
      ∃ W' : Submodule κ V₀, (∀ σ, ∀ v ∈ W', ρ₀ σ v ∈ W') ∧ IsCompl W W') :
    (Deformation.matrixRepresentation (matRep b ρ₀)).IsSemisimpleRepresentation := by
  apply DeligneSerre.isSemisimpleRepresentation_of_forall_exists_isCompl
  intro W hW
  let e : V₀ ≃ₗ[κ] (Fin 2 → κ) := b.equivFun

  let W₀ : Submodule κ V₀ := W.comap (e : V₀ →ₗ[κ] (Fin 2 → κ))
  have hW₀ : ∀ σ, ∀ v ∈ W₀, ρ₀ σ v ∈ W₀ := by
    intro σ v hv
    change e (ρ₀ σ v) ∈ W
    rw [← matRep_mulVec]
    exact hW σ _ hv
  obtain ⟨W₀', hW₀', hc⟩ := hcompl W₀ hW₀
  refine ⟨W₀'.map (e : V₀ →ₗ[κ] (Fin 2 → κ)), ?_, ?_⟩
  · rintro σ _ ⟨v, hv, rfl⟩
    refine ⟨ρ₀ σ v, hW₀' σ v hv, ?_⟩
    exact (matRep_mulVec b ρ₀ σ v).symm
  · have hWmap : W = W₀.map (e : V₀ →ₗ[κ] (Fin 2 → κ)) := by
      rw [Submodule.map_comap_eq_of_surjective e.surjective]
    rw [hWmap]
    exact hc.map (Submodule.orderIsoMapComap e)

end Transport

/-! ## The main theorem -/

theorem main (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : Γℚ →* GL (Fin 2) Ω) (hρ : GaloisFactorsThroughFiniteLevel ρ) (T : Finset ℕ)
    (hfrob : ∀ p : ℕ, p.Prime → p ∉ T →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          Matrix.trace (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
            Matrix.det (ρ σ : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : Γℚ →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ₀ ∧
      (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
      (∀ σ, ρ σ = 1 → ρ₀ σ = 1) ∧
      ∀ σ, (((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        (ρ σ : Matrix (Fin 2) (Fin 2) Ω).charpoly := by
  classical

  have hall := trace_mem_and_det_mem ι.range ρ hρ T hfrob

  have hlevel : ∀ ρ₀ : Γℚ →* GL (Fin 2) κ, (∀ σ, ρ σ = 1 → ρ₀ σ = 1) → GaloisFactorsThroughFiniteLevel ρ₀ := by
    intro ρ₀ h
    obtain ⟨L, hL, hker⟩ := hρ
    exact ⟨L, hL, fun σ hσ => h σ (hker σ hσ)⟩
  by_cases hirr : ∀ W : Submodule Ω (Fin 2 → Ω),
      (∀ σ, ∀ v ∈ W, (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec v ∈ W) → W = ⊥ ∨ W = ⊤
  ·
    obtain ⟨p, hpchar⟩ := CharP.exists κ
    haveI := hpchar
    have hp : p.Prime := (CharP.char_is_prime_or_zero κ p).resolve_right (CharP.char_ne_zero_of_finite κ p)
    haveI : Fact p.Prime := ⟨hp⟩
    have hpΩ : (p : Ω) = 0 := by
      rw [← map_natCast ι, CharP.cast_eq_zero, map_zero]
    have hV : Module.finrank Ω (Fin 2 → Ω) = 2 := Module.finrank_fin_fun Ω
    have hirr' : ∀ W : Submodule Ω (Fin 2 → Ω), (∀ σ, ∀ v ∈ W, linRep ρ σ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      exact hirr W (fun σ v hv => by rw [← linRep_apply]; exact hW σ v hv)
    have htr : ∀ σ, LinearMap.trace Ω _ ((linRep ρ σ : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) :
        (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) ∈ ι.range := fun σ => by rw [trace_linRep]; exact (hall σ).1
    have hdet : ∀ σ, LinearMap.det ((linRep ρ σ : (Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω)) :
        (Fin 2 → Ω) →ₗ[Ω] (Fin 2 → Ω)) ∈ ι.range := fun σ => by rw [det_linRep]; exact (hall σ).2
    have hcyc : ModularCurve.CyclotomicDeterminant 0 p (linRep ρ) := by
      intro ℓ _ hℓ; simp at hℓ
    obtain ⟨V₀, _, _, ρ₀, hV₀, -, hker, htr₀, hdet₀, hcompl⟩ :=
      ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite (K := ℚ)
        (L := AlgebraicClosure ℚ) 0 p Ω κ ι (Fin 2 → Ω) (linRep ρ) hpΩ hV
        (finite_range_linRep ρ hρ) hirr' htr hdet hcyc
    haveI : FiniteDimensional κ V₀ := Module.finite_of_finrank_eq_succ hV₀
    let b : Module.Basis (Fin 2) κ V₀ := Module.finBasisOfFinrankEq κ V₀ hV₀
    have hone : ∀ σ, ρ σ = 1 → matRep b ρ₀ σ = 1 := by
      intro σ hσ
      apply matRep_eq_one
      have : σ ∈ (linRep ρ).ker := by rw [MonoidHom.mem_ker]; exact linRep_eq_one ρ hσ
      exact (MonoidHom.mem_ker).mp (hker this)
    refine ⟨matRep b ρ₀, hlevel _ hone, matRep_isSemisimple b ρ₀ hcompl, hone, fun σ => ?_⟩
    rw [Matrix.charpoly_map, charpoly_matRep, DeligneSerre.charpoly_fin_two]
    simp only [Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
      Polynomial.map_X, Polynomial.map_C]
    rw [htr₀, hdet₀, trace_linRep, det_linRep]
  ·
    push Not at hirr
    obtain ⟨W, hW, hW0, hW1⟩ := hirr
    have hV : Module.finrank Ω (Fin 2 → Ω) = 2 := Module.finrank_fin_fun Ω
    have hWl : Module.finrank Ω W = 1 := DeligneSerre.finrank_eq_one_of_ne_bot_of_ne_top hV hW0 hW1
    obtain ⟨w, hw0, hwspan⟩ := finrank_eq_one_iff'.mp hWl
    have hv₀ : (w : Fin 2 → Ω) ≠ 0 := fun e => hw0 (Subtype.ext e)
    have hstab : ∀ σ : Γℚ, ∃ c : Ω, (ρ σ : Matrix (Fin 2) (Fin 2) Ω).mulVec w = c • (w : Fin 2 → Ω) := by
      intro σ
      obtain ⟨c, hc⟩ := hwspan ⟨_, hW σ w w.2⟩
      exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩
    let χ₁ := chi1 ρ hv₀ hstab
    let χ₂ := chi2 ρ hv₀ hstab
    have hadd : ∀ σ, (χ₁ σ : Ω) + χ₂ σ ∈ ι.range := fun σ => by
      simp only [χ₁, χ₂]; rw [chi1_add_chi2]; exact (hall σ).1
    have hmul : ∀ σ, (χ₁ σ : Ω) * χ₂ σ ∈ ι.range := fun σ => by
      simp only [χ₁, χ₂]; rw [chi1_mul_chi2]; exact (hall σ).2
    obtain ⟨ρ₀, hss, hone, hcp⟩ :=
      DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range ι χ₁ χ₂
        hadd hmul
    have hone' : ∀ σ, ρ σ = 1 → ρ₀ σ = 1 := fun σ hσ =>
      hone σ (chi1_eq_one ρ hv₀ hstab hσ) (chi2_eq_one ρ hv₀ hstab hσ)
    refine ⟨ρ₀, hlevel _ hone', hss, hone', fun σ => ?_⟩
    rw [hcp, DeligneSerre.charpoly_fin_two, ← chi1_add_chi2 ρ hv₀ hstab, ← chi1_mul_chi2 ρ hv₀ hstab]
    simp only [χ₁, χ₂, map_add, map_mul]
    ring

end GaloisRep

theorem ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) (σ : L ≃ₐ[K] L) (q m : ℕ)
    (hA : A.LiesOverPrime q) (hσ : A.IsFrobeniusAt σ q) (hm : m.Coprime q)
    (ζ : L) (hζ : ζ ^ m = 1) :
    σ ζ = ζ ^ q := by
  classical
  set k := IsLocalRing.ResidueField A with hk
  have hqA : ((q : A) : L) ∈ A.nonunits := by
    push_cast
    exact hA
  have hq𝔪 : (q : A) ∈ IsLocalRing.maximalIdeal A :=
    ValuationSubring.coe_mem_nonunits_iff.mp hqA
  have hqk : (q : k) = 0 := by
    rw [← map_natCast (IsLocalRing.residue A), IsLocalRing.residue_eq_zero_iff]
    exact hq𝔪
  have hmk : (m : k) ≠ 0 := by
    intro hm0
    have h1 : ringChar k ∣ m := (ringChar.spec (R := k) m).mp hm0
    have h2 : ringChar k ∣ q := (ringChar.spec (R := k) q).mp hqk
    have h3 : ringChar k ∣ Nat.gcd m q := Nat.dvd_gcd h1 h2
    rw [hm.gcd_eq_one, Nat.dvd_one] at h3
    exact CharP.ringChar_ne_one h3
  have hm0 : m ≠ 0 := by
    rintro rfl
    have hq1 : q = 1 := by simpa using hm
    subst hq1
    push_cast at hq𝔪
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      ((Ideal.eq_top_iff_one _).mpr hq𝔪)
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hm0] at hζ
    exact zero_ne_one hζ
  have hζA : ζ ∈ A := by
    rcases A.mem_or_inv_mem ζ with h | h
    · exact h
    · have : ζ = (ζ⁻¹) ^ (m - 1) := by
        rw [inv_pow]
        refine (inv_eq_of_mul_eq_one_right ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm0), hζ]
      rw [this]
      exact pow_mem h _
  set g : A.decompositionSubgroup K := ⟨σ, hσ.mem_decompositionSubgroup⟩ with hg
  set a : A := ⟨ζ, hζA⟩ with ha
  set b : A := g • a with hb
  have hbL : ((b : A) : L) = σ ζ := rfl
  have ham : a ^ m = 1 := Subtype.ext (by simp [ha, hζ])
  have hbm : b ^ m = 1 := by rw [hb, ← smul_pow', ham, smul_one]
  set v : A := a ^ q with hv
  have hvm : v ^ m = 1 := by rw [hv, ← pow_mul, mul_comm, pow_mul, ham, one_pow]
  have hres : IsLocalRing.residue A b = IsLocalRing.residue A v := by
    rw [hb, IsLocalRing.ResidueField.residue_smul, hg, hσ.smul_residue_eq, hv, map_pow]
  set S : A := ∑ i ∈ Finset.range m, b ^ i * v ^ (m - 1 - i) with hS
  have hSbv : S * (b - v) = 0 := by
    rw [hS, (Commute.all b v).geom_sum₂_mul, hbm, hvm, sub_self]
  have hresv_ne : IsLocalRing.residue A v ≠ 0 := by
    have h1 : IsLocalRing.residue A v ^ m = 1 := by rw [← map_pow, hvm, map_one]
    exact ne_zero_pow hm0 (by rw [h1]; exact one_ne_zero)
  have hresS : IsLocalRing.residue A S = (m : k) * IsLocalRing.residue A v ^ (m - 1) := by
    rw [hS, map_sum]
    have : ∀ i ∈ Finset.range m, IsLocalRing.residue A (b ^ i * v ^ (m - 1 - i))
        = IsLocalRing.residue A v ^ (m - 1) := by
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      rw [map_mul, map_pow, map_pow, hres, ← pow_add]
      congr 1
      omega
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hSunit : IsUnit S := by
    by_contra hSu
    have hS𝔪 : S ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal S).mpr hSu
    have h0 : IsLocalRing.residue A S = 0 := (IsLocalRing.residue_eq_zero_iff S).mpr hS𝔪
    rw [hresS] at h0
    exact (mul_ne_zero hmk (pow_ne_zero _ hresv_ne)) h0
  have hbv : b = v := sub_eq_zero.mp ((hSunit.mul_right_eq_zero).mp hSbv)
  have := congrArg (fun z : A => (z : L)) hbv
  simpa [hbL, hv, ha] using this

open scoped TensorProduct

open IsLocalRing in
theorem ValuationSubring.charP_residueField_of_liesOverPrime
    (ℓ : ℕ) [Fact ℓ.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime ℓ) : CharP (ResidueField ↥A) ℓ := by
  have hp : ℓ.Prime := Fact.out
  have hmem : (ℓ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A :=
    ValuationSubring.coe_mem_nonunits_iff (A := A).mp hA
  have hzero : (ℓ : ResidueField ↥A) = 0 := by
    rw [← map_natCast (IsLocalRing.residue ↥A)]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hmem
  have hrc : ringChar (ResidueField ↥A) ∣ ℓ := (ringChar.spec (R := ResidueField ↥A) ℓ).mp hzero
  have hrcℓ : ringChar (ResidueField ↥A) = ℓ :=
    (hp.eq_one_or_self_of_dvd _ hrc).resolve_left (CharP.ringChar_ne_one (R := ResidueField ↥A))
  exact hrcℓ ▸ ringChar.charP (ResidueField ↥A)

theorem GaloisRep.exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range
    (κ : Type) [Field κ] [Finite κ] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ι : κ →+* Ω)
    (ρ : Γℚ →* GL (Fin 2) Ω) (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ)
    (hfrob : ∀ p : ℕ, p.Prime → p ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
        ∀ σ : Γℚ, A.IsFrobeniusAt σ p →
          Matrix.trace ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range ∧
            Matrix.det ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω) ∈ ι.range) :
    ∃ ρ₀ : Γℚ →* GL (Fin 2) κ, GaloisFactorsThroughFiniteLevel ρ₀ ∧
      (Deformation.matrixRepresentation ρ₀).IsSemisimpleRepresentation ∧
      (∀ σ : Γℚ, ρ σ = 1 → ρ₀ σ = 1) ∧
      ∀ σ : Γℚ, (((ρ₀ σ : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        ((ρ σ : GL (Fin 2) Ω) : Matrix (Fin 2) (Fin 2) Ω).charpoly :=
  GaloisRep.main κ Ω ι ρ hρ S hfrob

