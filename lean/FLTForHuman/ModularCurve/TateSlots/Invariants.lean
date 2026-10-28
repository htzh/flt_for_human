/-
  The two invariants statements of the Tate slots: the Γ₁ integral
  `q`-expansion / toric-point theorem and the `E₄³/Δ` orbit statement.

  1. `ModularCurve.exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum`: for
     every level `M`, five objects — two families of modular forms
     `B : ZMod M → ModularForm Γ₁(M) 2` and `D : ZMod M → ModularForm Γ₁(M) 4`, their
     integral `q`-expansions `b d : ZMod M → PowerSeries ℤ`, and the four properties:
     `IsIntegralQExp` for both families, the `Γ₀(M)`-slash law
     `B c ∣[2] γ = B (c γ₀₀)`, `D c ∣[4] γ = D (c γ₀₀)`, and the two Laurent-series
     identities at a primitive `M`-th root `ζ` (the `tateLaurent` `a₄` form of the
     toric point).  The engine is the ported `℘`-at-torsion form family
     `PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff`
     (`Elliptic/PeriodPair/InvariantsTorsion.lean`): its `W` supplies the weight-2
     forms, `W²` minus the level-one `E₄` the weight-4 ones, and the whole
     `q`-expansion bookkeeping is the pin's finite-Fourier block (`ToricFourier`,
     reconstructed here because the port has no copy of it).

  2. `ModularCurve.exists_smul_eq_of_E4_cube_div_discriminant_eq`: `E₄³/Δ` separates
     the `SL(2, ℤ)`-orbits of `ℍ`.  The proof is the ported
     `PeriodPair.lattice_eq_of_g2_eq_of_g3_eq` (same module): equal `j`-type data
     makes the two period lattices equal up to the scalar `w`, the two `ℤ`-coordinates
     of `ω₁'`/`ω₂'` and of `u ω₁`/`u ω₂` give a `2 × 2` integer matrix of determinant
     `1`, and `exists_sl2z_of_lattice_rel` turns it into `γ • τ = τ'`.

  Statements are the pin's, verbatim (pinned `aa2d8b3`); of the pin's two `S_` files'
  declarations the port already carries

    `PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff`,
    `WPGamma1.T_mem_Gamma1`, `WPGamma1.one_mem_strictPeriods`
                                    (`Elliptic/PeriodPair/InvariantsTorsion.lean`),
    `PeriodPair.G_ofTau_eq` / `g₂_scale` / `g₃_scale` / `g₂_ofTau` / `g₃_ofTau`,
    `PeriodPair.mem_scale_lattice_iff`, `PeriodPair.ofTau_lattice`, `lattice` membership
                                    (`Elliptic/PeriodPair/{Lattice,Discriminant}.lean`),

  so the second row's `Bridge` section is imported rather than re-proved (the pin's
  `mem_scale_lattice` is the port's `mem_scale_lattice_iff` composed with
  `PeriodPair.mem_lattice`, used at the four extraction sites instead of restated).
  The `ToricFourier.Generic` block has no port copy at all (`port_advise --nodes`:
  3 substitutable declarations, all imported above), so it is transcribed whole.

  Private declarations.  The pin's `JSeparatesOrbits.pow_four_six_of_sq` is `private`
  and stays `private` here.  The pin's public helpers `finset_sum_slash`,
  `coe_finset_sum`, `det_mod` exist in the port only as `private` declarations
  (`ModularForms/WeightOne/Gamma1Basis.lean`, `ModularForms/HeckeNebentypusFricke.lean`),
  which are not importable; `finset_sum_slash` / `coe_finset_sum` are transcribed
  at the pin's public names, and `det_mod`'s four-line determinant computation is
  inlined at its single use site (`sum_reindex`) so that no duplicate lemma exists.
  `E₄_cube_sub_E₆_sq_ne_zero` is a pin-public statement whose port copy
  (`Discriminant.lean`'s `E4cube_ne_E6sq`) is `private` and has a different
  statement; it is transcribed here.

  No wrapper.  The first `S_` file ends in the pair `ToricFourier.main` /
  root-level `solution` (637:593, 637:620), whose two statements are the same
  five-object existential up to the `Gamma1`/`CongruenceSubgroup.Gamma1`
  spelling, and whose proofs are `⟨…⟩` and `main M` respectively — the pin's own
  wrapper-over-engine.  Neither is declared here: the port's headline carries the
  engine's proof term directly, so the module has no one-line restatement.

  Provenance (pinned `aa2d8b3`):
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean
  https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean

  spec-pin: Theorems/Thm_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.lean
  spec-pin: Theorems/Thm_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean
  spec-pin: P2M/Sol/S_ModularCurve_exists_smul_eq_of_E4_cube_div_discriminant_eq.lean
-/
import FLTForHuman.Elliptic.PeriodPair.InvariantsTorsion
import FLTForHuman.Elliptic.PeriodPair.Discriminant
import FLTForHuman.ModularCurve.X1.Defs
import FLTForHuman.ModularCurve.Defs.TateSlots
import FLTForHuman.ModularForms.JqAnalyticModel

set_option autoImplicit false

noncomputable section

open UpperHalfPlane hiding I
open Complex Filter Function ModularForm CongruenceSubgroup Polynomial ModularCurve
open scoped MatrixGroups ModularForm Topology Manifold Matrix Real Polynomial

namespace ModularCurve

namespace ToricFourier

/-! ## The Γ₁-level modular-form bookkeeping over `ℂ` -/

section Prelude

variable (M : ℕ)

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

theorem coe_finset_sum {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ModularForm Γ₁ᴳ k) :
    (⇑(∑ i ∈ s, G i) : ℍ → ℂ) = ∑ i ∈ s, (⇑(G i) : ℍ → ℂ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add, ih]

theorem qExpansion_finset_sum {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ModularForm Γ₁ᴳ k) :
    qExpansion 1 (⇑(∑ i ∈ s, G i)) = ∑ i ∈ s, qExpansion 1 (⇑(G i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [qExpansion_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, FunLike.coe_add,
      ModularForm.qExpansion_add one_pos (WPGamma1.one_mem_strictPeriods M) (G a) (∑ i ∈ s, G i), ih]

theorem qExpansion_smul' {k : ℤ} (c : ℂ) (f : ModularForm Γ₁ᴳ k) :
    qExpansion 1 (⇑(c • f)) = c • qExpansion 1 (⇑f) := by
  rw [FunLike.coe_smul]
  exact ModularForm.qExpansion_smul one_pos (WPGamma1.one_mem_strictPeriods M) c f

theorem finset_sum_slash {k : ℤ} {ι : Type*} (s : Finset ι) (G : ι → ℍ → ℂ) (γ : SL(2, ℤ)) :
    (∑ i ∈ s, G i) ∣[k] γ = ∑ i ∈ s, (G i ∣[k] γ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

def E4Γ : ModularForm Γ₁ᴳ 4 := restrictForm (Subgroup.map_le_range _ _) E₄

theorem coe_E4Γ : (⇑(E4Γ M) : ℍ → ℂ) = E₄ := rfl

theorem qExpansion_E4Γ : qExpansion 1 (⇑(E4Γ M)) = eisenstein4.map (Int.castRingHom ℂ) := by
  rw [coe_E4Γ]
  exact qExpansion_E4_eq_map_eisenstein4

theorem E4Γ_slash (γ : SL(2, ℤ)) : (⇑(E4Γ M) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(E4Γ M) := by
  rw [coe_E4Γ, ModularForm.SL_slash]
  exact SlashInvariantFormClass.slash_action_eq E₄ _ ⟨γ, rfl⟩

end Prelude

/-! ## The integer-polynomial side of the Fourier coefficients -/

section IntPoly

/-- The `M`-average of the coefficients of a polynomial with integer coefficients. -/
def avg (M : ℕ) (R : ℤ[X]) : ℤ :=
  ∑ j ∈ Finset.range (R.natDegree + 1), if M ∣ j then R.coeff j else 0

/-- The `M`-Fourier inversion functional: `four M c R` is
`M * avg M (X ^ (-c).val * R) - R.eval 1`. -/
def four (M : ℕ) (c : ZMod M) (R : ℤ[X]) : ℤ := M * avg M (X ^ (-c).val * R) - R.eval 1

section FilterNZ

variable {M : ℕ} [NeZero M]

theorem filter_ne_zero_eq :
    (Finset.univ.filter fun a : ZMod M => a ≠ 0) = Finset.univ.erase 0 := by
  classical
  exact Finset.filter_ne' _ _

end FilterNZ

/-- The polynomial `∑ j < M, j X ^ j`. -/
def S1 (M : ℕ) : ℤ[X] := ∑ j ∈ Finset.range M, (j : ℤ[X]) * X ^ j

/-- The `X`-side polynomial whose `ψ`-evaluation is `M²` times the weight-2
`q`-expansion coefficient. -/
def xT (M : ℕ) (n : ℕ) : ℤ[X] :=
  if n = 0 then X * S1 M ^ 2
  else C ((M : ℤ) ^ 2) *
    ((∑ d ∈ n.divisors, (d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) - C (2 * ∑ d ∈ n.divisors, (d : ℤ)))

/-- The weight-2 integral `q`-expansion polynomial. -/
def wT (M : ℕ) (n : ℕ) : ℤ[X] := C ((M : ℤ) ^ 2 * (if n = 0 then 1 else 0)) + C 12 * xT M n

/-- The `n`-th coefficient of the Tate `a₄`. -/
def a4Z (n : ℕ) : ℤ := PowerSeries.coeff n tateA4

/-- The `X`-side polynomial whose `ψ`-evaluation is `M⁴` times the weight-4
`q`-expansion coefficient. -/
def fT (M : ℕ) (n : ℕ) : ℤ[X] :=
  C ((M : ℤ) ^ 2) * xT M n + C 6 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, xT M p.1 * xT M p.2) +
    C (2 * (M : ℤ) ^ 4 * a4Z n)

/-- The `c`-th weight-2 integral `q`-expansion coefficient. -/
def bZ (M : ℕ) (c : ZMod M) (n : ℕ) : ℤ := four M c (wT M n)

/-- The `c`-th weight-4 integral `q`-expansion coefficient. -/
def dZ (M : ℕ) (c : ZMod M) (n : ℕ) : ℤ := four M c (fT M n)

end IntPoly

/-! ## The field-valued Fourier coefficients -/

section FieldCoeffs

variable {F : Type*} [Field F]

/-- The `n`-th coefficient of the toric point's `x`-coordinate. -/
def xcoef (u : F) (n : ℕ) : F :=
  if n = 0 then u / (1 - u) ^ 2
  else (∑ d ∈ n.divisors, (d : F) * (u ^ d + u⁻¹ ^ d)) - 2 * ∑ d ∈ n.divisors, (d : F)

/-- The weight-2 `q`-expansion coefficient. -/
def wcoef (u : F) (n : ℕ) : F := (if n = 0 then (1 : F) else 0) + 12 * xcoef u n

/-- The weight-4 `q`-expansion coefficient. -/
def fcoef (u : F) (n : ℕ) : F :=
  xcoef u n + 6 * (∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, xcoef u p.1 * xcoef u p.2) + 2 * (a4Z n : ℤ)

def xS (u : F) : PowerSeries F := PowerSeries.mk (xcoef u)

def wS (u : F) : PowerSeries F := PowerSeries.mk (wcoef u)

def fS (u : F) : PowerSeries F := PowerSeries.mk (fcoef u)

theorem wS_eq (u : F) : wS u = 1 + PowerSeries.C (12 : F) * xS u := by
  ext n
  simp only [wS, xS, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    wcoef]

theorem fS_eq (u : F) :
    fS u = xS u + PowerSeries.C (6 : F) * (xS u * xS u) +
      PowerSeries.C (2 : F) * (tateA4.map (Int.castRingHom F)) := by
  ext n
  rw [map_add, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
    PowerSeries.coeff_map]
  simp only [fS, xS, PowerSeries.coeff_mk, fcoef, a4Z, eq_intCast]

theorem wS_eq' (u : F) : wS u = 1 + 12 * xS u := by
  rw [wS_eq, show PowerSeries.C (12 : F) = (12 : PowerSeries F) from map_ofNat _ 12]

theorem fS_eq' (u : F) :
    fS u = xS u + 6 * (xS u * xS u) + 2 * (tateA4.map (Int.castRingHom F)) := by
  rw [fS_eq, show PowerSeries.C (6 : F) = (6 : PowerSeries F) from map_ofNat _ 6,
    show PowerSeries.C (2 : F) = (2 : PowerSeries F) from map_ofNat _ 2]

theorem eisenstein4_map_eq :
    eisenstein4.map (Int.castRingHom F) = 1 - 48 * tateA4.map (Int.castRingHom F) := by
  rw [show (48 : PowerSeries F) = PowerSeries.C (48 : F) from (map_ofNat _ 48).symm]
  ext n
  rw [PowerSeries.coeff_map, map_sub, PowerSeries.coeff_one, PowerSeries.coeff_C_mul,
    PowerSeries.coeff_map, coeff_tateA4, eisenstein4, PowerSeries.coeff_mk]
  by_cases hn : n = 0
  · subst hn; simp
  · simp only [hn, ite_false, eq_intCast, Int.cast_mul, Int.cast_ofNat, Int.cast_sum, Int.cast_pow,
      Int.cast_natCast, Int.cast_neg, zero_sub, Finset.mul_sum, mul_neg, neg_neg]
    refine Finset.sum_congr rfl fun d _ => ?_
    ring

end FieldCoeffs

section FieldPolyEval

variable {F : Type*} [Field F] {M : ℕ}

theorem aeval_S1 (u : F) : aeval u (S1 M) = ∑ j ∈ Finset.range M, (j : F) * u ^ j := by
  simp [S1, map_sum]

end FieldPolyEval

/-! ## The finite Fourier block -/

section CharFourier

variable {F : Type*} [Field F] {M : ℕ} [NeZero M] {z : F} (hz : IsPrimitiveRoot z M)

/-- The additive character of `ZMod M` attached to a primitive `M`-th root `z`. -/
def ψ (hz : IsPrimitiveRoot z M) : AddChar (ZMod M) F := AddChar.zmodChar M hz.pow_eq_one

theorem ψ_apply (a : ZMod M) : ψ hz a = z ^ a.val := rfl

theorem ψ_isPrimitive : (ψ hz).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root M hz

theorem ψ_eq_one_iff (a : ZMod M) : ψ hz a = 1 ↔ a = 0 :=
  (ψ_isPrimitive hz).zmod_char_eq_one_iff M a

theorem sum_ψ_mul (b : ZMod M) : ∑ a : ZMod M, ψ hz (a * b) = if b = 0 then (M : F) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (ψ_isPrimitive hz)]
  split_ifs <;> simp [ZMod.card]

theorem ψ_pow (a : ZMod M) (j : ℕ) : ψ hz a ^ j = ψ hz ((j : ZMod M) * a) := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

include hz in
theorem natCast_ne_zero : (M : F) ≠ 0 :=
  haveI : NeZero (M : F) := IsPrimitiveRoot.neZero' hz
  NeZero.ne (M : F)

theorem ψ_ne_zero (a : ZMod M) : ψ hz a ≠ 0 := by
  rw [ψ_apply]
  exact pow_ne_zero _ (hz.ne_zero (NeZero.ne M))

theorem ψ_pow_M (a : ZMod M) : ψ hz a ^ M = 1 := by
  rw [ψ_apply, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]

theorem ψ_ne_one {a : ZMod M} (ha : a ≠ 0) : ψ hz a ≠ 1 := fun h => ha ((ψ_eq_one_iff hz a).mp h)

theorem one_sub_ψ_ne_zero {a : ZMod M} (ha : a ≠ 0) : 1 - ψ hz a ≠ 0 :=
  sub_ne_zero.mpr (ψ_ne_one hz ha).symm

theorem geom_ψ {a : ZMod M} (ha : a ≠ 0) : ∑ j ∈ Finset.range M, ψ hz a ^ j = 0 := by
  rw [geom_sum_eq (ψ_ne_one hz ha) M, ψ_pow_M, sub_self, zero_div]

theorem ψ_pow_sub_one (a : ZMod M) : ψ hz a ^ (M - 1) = (ψ hz a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [pow_sub_one_mul (NeZero.ne M), ψ_pow_M]

theorem sum_aeval (R : ℤ[X]) : ∑ a : ZMod M, aeval (ψ hz a) R = (M : F) * (avg M R : ℤ) := by
  classical
  simp_rw [aeval_eq_sum_range]
  rw [Finset.sum_comm, avg, Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp_rw [zsmul_eq_mul]
  rw [← Finset.mul_sum]
  have h : ∑ a : ZMod M, ψ hz a ^ j = if M ∣ j then (M : F) else 0 := by
    simp_rw [ψ_pow hz _ j]
    have : ∀ a : ZMod M, (j : ZMod M) * a = a * (j : ZMod M) := fun a => mul_comm _ _
    simp_rw [this]
    rw [sum_ψ_mul hz (j : ZMod M)]
    exact if_congr (ZMod.natCast_eq_zero_iff j M) rfl rfl
  rw [h]
  split_ifs <;> simp [mul_comm]

theorem sum_filter_aeval (c : ZMod M) (R : ℤ[X]) :
    ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * aeval (ψ hz a) R =
      ((four M c R : ℤ) : F) := by
  classical
  have h1 : ∀ a : ZMod M, ψ hz (-(a * c)) * aeval (ψ hz a) R = aeval (ψ hz a) (X ^ (-c).val * R) := by
    intro a
    rw [map_mul, map_pow, aeval_X, ψ_pow hz a (-c).val, ZMod.natCast_zmod_val]
    congr 2
    ring
  simp_rw [h1]
  rw [filter_ne_zero_eq, Finset.sum_erase_eq_sub (Finset.mem_univ _), sum_aeval hz, four,
    Int.cast_sub, Int.cast_mul, Int.cast_natCast, AddChar.map_zero_eq_one]
  congr 1
  rw [aeval_def, eval₂_at_one, eq_intCast, eval_mul, eval_pow, eval_X, one_pow, one_mul]

theorem fourier_inversion (g : ZMod M → F) (s : ZMod M) (hs : s ≠ 0) :
    ∑ c : ZMod M, ψ hz (s * c) *
        ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0), ψ hz (-(a * c)) * g a =
      (M : F) * g s := by
  classical
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have h : ∀ a : ZMod M, ∑ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) =
      (if a = s then (M : F) else 0) * g a := by
    intro a
    have : ∀ c : ZMod M, ψ hz (s * c) * (ψ hz (-(a * c)) * g a) = ψ hz (c * (s - a)) * g a := by
      intro c
      rw [← mul_assoc, ← AddChar.map_add_eq_mul]
      congr 2
      ring
    simp_rw [this]
    rw [← Finset.sum_mul, sum_ψ_mul hz (s - a)]
    congr 1
    simp only [sub_eq_zero]
    by_cases h : a = s
    · rw [ite_eq_left h.symm, ite_eq_left h]
    · rw [ite_eq_right (Ne.symm h), ite_eq_right h]
  simp_rw [h, ite_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp [hs]

theorem one_sub_mul_S1 {a : ZMod M} (ha : a ≠ 0) :
    (1 - ψ hz a) * aeval (ψ hz a) (S1 M) = -(M : F) := by
  set u := ψ hz a with hu
  set T : F := ∑ j ∈ Finset.range M, (j : F) * u ^ j with hT
  rw [aeval_S1, ← hT]
  have h1 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j = T + M * u ^ M := Finset.sum_range_succ _ M
  have h2 : ∑ j ∈ Finset.range (M + 1), (j : F) * u ^ j =
      ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) := by
    rw [Finset.sum_range_succ']
    simp
  have h3 : ∑ j ∈ Finset.range M, ((j + 1 : ℕ) : F) * u ^ (j + 1) =
      u * T + u * ∑ j ∈ Finset.range M, u ^ j := by
    rw [hT, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [geom_ψ hz ha, ψ_pow_M] at *
  have key : u * T = T + M := by
    have := h1.symm.trans (h2.trans h3)
    rw [mul_zero, add_zero, mul_one] at this
    exact this.symm
  linear_combination -key

theorem inv_formula {a : ZMod M} (ha : a ≠ 0) :
    (M : F) ^ 2 * (ψ hz a / (1 - ψ hz a) ^ 2) = ψ hz a * (aeval (ψ hz a) (S1 M)) ^ 2 := by
  have h := one_sub_mul_S1 hz ha
  have hne := one_sub_ψ_ne_zero hz ha
  have : aeval (ψ hz a) (S1 M) = -(M : F) / (1 - ψ hz a) := by
    rw [eq_div_iff hne, mul_comm]; exact h
  rw [this]
  field_simp

theorem aeval_xT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (xT M n) = (M : F) ^ 2 * xcoef (ψ hz a) n := by
  by_cases hn : n = 0
  · subst hn
    rw [xT, ite_eq_left rfl, xcoef, ite_eq_left rfl, map_mul, map_pow, aeval_X, inv_formula hz ha]
  · rw [xT, ite_eq_right hn, xcoef, ite_eq_right hn]
    have h : ∀ d ∈ n.divisors, aeval (ψ hz a) ((d : ℤ[X]) * (X ^ d + X ^ ((M - 1) * d))) =
        (d : F) * (ψ hz a ^ d + (ψ hz a)⁻¹ ^ d) := by
      intro d _
      rw [map_mul, map_natCast, map_add, map_pow, map_pow, aeval_X, pow_mul, ψ_pow_sub_one hz a]
    rw [map_mul, map_sub, map_sum, Finset.sum_congr rfl h, aeval_C, aeval_C]
    simp only [algebraMap_int_eq, eq_intCast, Int.cast_pow, Int.cast_natCast, Int.cast_mul,
      Int.cast_ofNat, Int.cast_sum]

theorem aeval_wT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (wT M n) = (M : F) ^ 2 * wcoef (ψ hz a) n := by
  have hx := aeval_xT hz ha n
  by_cases hn : n = 0
  · subst hn
    simp only [wT, ite_true, mul_one, map_add, map_mul, map_pow, map_natCast, map_ofNat, hx, wcoef]
    ring
  · simp only [wT, hn, ite_false, mul_zero, map_zero, zero_add, map_mul, map_ofNat, hx, wcoef]
    ring

theorem aeval_fT {a : ZMod M} (ha : a ≠ 0) (n : ℕ) :
    aeval (ψ hz a) (fT M n) = (M : F) ^ 4 * fcoef (ψ hz a) n := by
  have h : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, aeval (ψ hz a) (xT M p.1 * xT M p.2) =
      (M : F) ^ 4 * (xcoef (ψ hz a) p.1 * xcoef (ψ hz a) p.2) := by
    intro p _
    rw [map_mul, aeval_xT hz ha, aeval_xT hz ha]; ring
  rw [fT, map_add, map_add, map_mul, map_mul, map_sum, Finset.sum_congr rfl h, ← Finset.mul_sum,
    aeval_xT hz ha, fcoef]
  simp only [eq_intCast, map_pow, map_natCast, map_ofNat, map_mul, map_intCast]
  ring

theorem bZ_eq_sum (c : ZMod M) (n : ℕ) :
    ((bZ M c n : ℤ) : F) = ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0),
      ψ hz (-(a * c)) * ((M : F) ^ 2 * wcoef (ψ hz a) n) := by
  rw [bZ, ← sum_filter_aeval hz]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [aeval_wT hz (Finset.mem_filter.mp ha).2]

theorem dZ_eq_sum (c : ZMod M) (n : ℕ) :
    ((dZ M c n : ℤ) : F) = ∑ a ∈ Finset.univ.filter (fun a : ZMod M => a ≠ 0),
      ψ hz (-(a * c)) * ((M : F) ^ 4 * fcoef (ψ hz a) n) := by
  rw [dZ, ← sum_filter_aeval hz]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [aeval_fT hz (Finset.mem_filter.mp ha).2]

theorem sum_ψ_bZ (s : ZMod M) (hs : s ≠ 0) (n : ℕ) :
    ∑ c : ZMod M, ψ hz (s * c) * ((bZ M c n : ℤ) : F) = (M : F) ^ 3 * wcoef (ψ hz s) n := by
  simp_rw [bZ_eq_sum hz]
  rw [fourier_inversion hz (fun a => (M : F) ^ 2 * wcoef (ψ hz a) n) s hs]
  ring

theorem sum_ψ_dZ (s : ZMod M) (hs : s ≠ 0) (n : ℕ) :
    ∑ c : ZMod M, ψ hz (s * c) * ((dZ M c n : ℤ) : F) = (M : F) ^ 5 * fcoef (ψ hz s) n := by
  simp_rw [dZ_eq_sum hz]
  rw [fourier_inversion hz (fun a => (M : F) ^ 4 * fcoef (ψ hz a) n) s hs]
  ring

end CharFourier

/-! ## The five-object existential over `ℂ` -/

section OverComplex

variable (M : ℕ) [NeZero M]

local notation "Γ₁ᴳ" => ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

def μ : ℂ := cexp (2 * π * I / M)

theorem hμ : IsPrimitiveRoot (μ M) M := Complex.isPrimitiveRoot_exp M (NeZero.ne M)

def W : ZMod M → ModularForm Γ₁ᴳ 2 :=
  (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose

theorem W_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(W M t) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(W M (t * ((γ 1 1 : ℤ) : ZMod M))) :=
  (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose_spec.2.1 t γ hγ

theorem qExpansion_W_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (W M t)).coeff n = wcoef (ψ (hμ M) t) n := by
  rw [W, (PeriodPair.exists_gamma1_two_eq_weierstrassP_and_slash_and_qExpansion_coeff M).choose_spec.2.2
    t ht n, wcoef, xcoef, ψ_apply]
  by_cases hn : n = 0
  · simp [hn, μ, mul_div_assoc]
  · simp only [hn, ite_false, zero_add, μ]
    congr 1
    congr 1
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [← pow_mul, ← inv_pow, ← pow_mul]

theorem qExpansion_W (t : ZMod M) (ht : t ≠ 0) : qExpansion 1 (W M t) = wS (ψ (hμ M) t) := by
  ext n
  rw [qExpansion_W_coeff M t ht, wS, PowerSeries.coeff_mk]

abbrev nz : Finset (ZMod M) := Finset.univ.filter fun a : ZMod M => a ≠ 0

def B (c : ZMod M) : ModularForm Γ₁ᴳ 2 :=
  ((M : ℂ) ^ 2) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • W M t

theorem coe_B (c : ZMod M) :
    (⇑(B M c) : ℍ → ℂ) = ((M : ℂ) ^ 2) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • (⇑(W M t) : ℍ → ℂ) := by
  rw [B, FunLike.coe_smul, coe_finset_sum]
  simp only [FunLike.coe_smul]

theorem qExpansion_B_coeff (c : ZMod M) (n : ℕ) :
    (qExpansion 1 (B M c)).coeff n = ((bZ M c n : ℤ) : ℂ) := by
  rw [B, qExpansion_smul', qExpansion_finset_sum, bZ_eq_sum (hμ M)]
  simp only [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [qExpansion_smul', map_smul, smul_eq_mul, qExpansion_W_coeff M t (Finset.mem_filter.mp ht).2]
  ring

theorem isIntegralQExp_B (c : ZMod M) : IsIntegralQExp (⇑(B M c)) (PowerSeries.mk (bZ M c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_B_coeff]

def Wsq (t : ZMod M) : ModularForm Γ₁ᴳ 4 := ((W M t).mul (W M t)).mcast (by norm_num)

theorem coe_Wsq (t : ZMod M) : (⇑(Wsq M t) : ℍ → ℂ) = ⇑(W M t) * ⇑(W M t) := by
  rw [Wsq, coe_mcast, ModularForm.coe_mul]

def Fform (t : ZMod M) : ModularForm Γ₁ᴳ 4 := (24 : ℂ)⁻¹ • (Wsq M t - E4Γ M)

theorem coe_Fform (t : ZMod M) :
    (⇑(Fform M t) : ℍ → ℂ) = (24 : ℂ)⁻¹ • (⇑(W M t) * ⇑(W M t) - ⇑(E4Γ M)) := by
  rw [Fform, FunLike.coe_smul, FunLike.coe_sub, coe_Wsq]

theorem qExpansion_Fform (t : ZMod M) (ht : t ≠ 0) : qExpansion 1 (Fform M t) = fS (ψ (hμ M) t) := by
  rw [Fform, qExpansion_smul', FunLike.coe_sub,
    ModularForm.qExpansion_sub one_pos (WPGamma1.one_mem_strictPeriods M) (Wsq M t) (E4Γ M), coe_Wsq,
    ModularForm.qExpansion_mul_coe one_pos (WPGamma1.one_mem_strictPeriods M) (W M t) (W M t),
    qExpansion_W M t ht, qExpansion_E4Γ, eisenstein4_map_eq, wS_eq', fS_eq', PowerSeries.smul_eq_C_mul]
  set x := xS (ψ (hμ M) t)
  set a := tateA4.map (Int.castRingHom ℂ)
  have h : (1 + 12 * x) * (1 + 12 * x) - (1 - 48 * a) = 24 * (x + 6 * (x * x) + 2 * a) := by ring
  rw [h, ← mul_assoc, show PowerSeries.C (24 : ℂ)⁻¹ * (24 : PowerSeries ℂ) = 1 by
    rw [← map_ofNat PowerSeries.C 24, ← map_mul, inv_mul_cancel₀ (by norm_num), map_one], one_mul]

theorem qExpansion_Fform_coeff (t : ZMod M) (ht : t ≠ 0) (n : ℕ) :
    (qExpansion 1 (Fform M t)).coeff n = fcoef (ψ (hμ M) t) n := by
  rw [qExpansion_Fform M t ht, fS, PowerSeries.coeff_mk]

theorem Fform_slash (t : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(Fform M t) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(Fform M (t * ((γ 1 1 : ℤ) : ZMod M))) := by
  rw [coe_Fform, coe_Fform, ModularForm.SL_smul_slash, sub_eq_add_neg, SlashAction.add_slash,
    SlashAction.neg_slash, E4Γ_slash, ← sub_eq_add_neg]
  congr 2
  have h := ModularForm.mul_slash_SL2 2 2 γ (⇑(W M t)) (⇑(W M t))
  rw [show (2 : ℤ) + 2 = 4 by norm_num] at h
  rw [h, W_slash M t γ hγ]

def D (c : ZMod M) : ModularForm Γ₁ᴳ 4 :=
  ((M : ℂ) ^ 4) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • Fform M t

theorem coe_D (c : ZMod M) :
    (⇑(D M c) : ℍ → ℂ) = ((M : ℂ) ^ 4) • ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • (⇑(Fform M t) : ℍ → ℂ) := by
  rw [D, FunLike.coe_smul, coe_finset_sum]
  simp only [FunLike.coe_smul]

theorem qExpansion_D_coeff (c : ZMod M) (n : ℕ) :
    (qExpansion 1 (D M c)).coeff n = ((dZ M c n : ℤ) : ℂ) := by
  rw [D, qExpansion_smul', qExpansion_finset_sum, dZ_eq_sum (hμ M)]
  simp only [map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [qExpansion_smul', map_smul, smul_eq_mul, qExpansion_Fform_coeff M t (Finset.mem_filter.mp ht).2]
  ring

theorem isIntegralQExp_D (c : ZMod M) : IsIntegralQExp (⇑(D M c)) (PowerSeries.mk (dZ M c)) := by
  rw [isIntegralQExp_iff]
  intro n
  rw [PowerSeries.coeff_mk, qExpansion_D_coeff]

theorem sum_reindex {V : Type*} [AddCommMonoid V] [Module ℂ V] (G : ZMod M → V) (c : ZMod M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) :
    ∑ t ∈ nz M, (ψ (hμ M) (-(t * c))) • G (t * ((γ 1 1 : ℤ) : ZMod M)) =
      ∑ t ∈ nz M, (ψ (hμ M) (-(t * (c * ((γ 0 0 : ℤ) : ZMod M))))) • G t := by
  set δ : ZMod M := ((γ 1 1 : ℤ) : ZMod M) with hδ
  set a : ZMod M := ((γ 0 0 : ℤ) : ZMod M) with ha
  have hda : δ * a = 1 := by
    have hdet := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hdet
    have h := congrArg (fun z : ℤ => (z : ZMod M)) hdet
    simp only [Int.cast_sub, Int.cast_mul, Int.cast_one] at h
    have hc : ((γ 1 0 : ℤ) : ZMod M) = 0 := Gamma0_mem.mp hγ
    rw [hc, mul_zero, sub_zero, mul_comm] at h
    exact h
  refine Finset.sum_nbij' (fun t => t * δ) (fun t => t * a) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * δ * a = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, hda, mul_one] at this
  · intro t ht
    simp only [nz, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
    intro h
    apply ht
    have : t * a * δ = 0 := by rw [h, zero_mul]
    rwa [mul_assoc, mul_comm a δ, hda, mul_one] at this
  · intro t _
    rw [mul_assoc, hda, mul_one]
  · intro t _
    rw [mul_assoc, mul_comm a δ, hda, mul_one]
  · intro t _
    congr 2
    linear_combination (t * c) * hda

theorem B_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(B M c) : ℍ → ℂ) ∣[(2 : ℤ)] γ = ⇑(B M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_B, coe_B, ModularForm.SL_smul_slash, finset_sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (hμ M) (-(t * c))) • (⇑(W M t) : ℍ → ℂ)) ∣[(2 : ℤ)] γ =
      (ψ (hμ M) (-(t * c))) • (⇑(W M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, W_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(W M t) : ℍ → ℂ)) c hγ

theorem D_slash (c : ZMod M) (γ : SL(2, ℤ)) (hγ : γ ∈ Gamma0 M) :
    (⇑(D M c) : ℍ → ℂ) ∣[(4 : ℤ)] γ = ⇑(D M (c * ((γ 0 0 : ℤ) : ZMod M))) := by
  rw [coe_D, coe_D, ModularForm.SL_smul_slash, finset_sum_slash]
  congr 1
  have h : ∀ t ∈ nz M, ((ψ (hμ M) (-(t * c))) • (⇑(Fform M t) : ℍ → ℂ)) ∣[(4 : ℤ)] γ =
      (ψ (hμ M) (-(t * c))) • (⇑(Fform M (t * ((γ 1 1 : ℤ) : ZMod M))) : ℍ → ℂ) := by
    intro t _
    rw [ModularForm.SL_smul_slash, Fform_slash M t γ hγ]
  rw [Finset.sum_congr rfl h]
  exact sum_reindex M (fun t => (⇑(Fform M t) : ℍ → ℂ)) c hγ

end OverComplex

/-! ## The Laurent-series identities over an arbitrary field -/

section AnyField

open HahnSeries

variable {M : ℕ} [NeZero M] (K : Type*) [Field K] {ζ : K} (hζ : IsPrimitiveRoot ζ M)

theorem toricPoint_fst_eq (u : K) : (toricPoint K 1 u).1 = ofPowerSeries ℤ K (xS u) := by
  rw [toricPoint_fst]
  congr 1
  ext m
  rw [PowerSeries.coeff_mk, xS, PowerSeries.coeff_mk, xcoef]
  by_cases hm : m = 0
  · simp [hm]
  · simp only [hm, ite_false, one_dvd, ite_true, Nat.div_one]
    congr 1
    exact Nat.sum_div_divisors m (fun d => (d : K) * (u ^ d + u⁻¹ ^ d))

theorem intSeriesC_eq (p : PowerSeries ℤ) :
    intSeriesC K p = ofPowerSeries ℤ K (p.map (Int.castRingHom K)) := rfl

theorem smul_ofPowerSeries (a : K) (P : PowerSeries K) :
    a • ofPowerSeries ℤ K P = ofPowerSeries ℤ K (PowerSeries.C a * P) := by
  rw [map_mul, ofPowerSeries_C, C_mul_eq_smul]

include hζ in
theorem weightTwo (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [toricPoint_fst_eq, hu]

  have lhs : (M : LaurentSeries K) ^ 3 * (1 + 12 * ofPowerSeries ℤ K (xS (ψ hζ s))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 3) * wS (ψ hζ s)) := by
    rw [wS_eq', map_mul, map_add, map_one, map_mul, map_ofNat, ofPowerSeries_C, map_pow, map_natCast]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (bZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (bZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, wS, PowerSeries.coeff_mk, ← sum_ψ_bZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

include hζ in
theorem weightFour (s : ZMod M) (hs : s ≠ 0) :
    (M : LaurentSeries K) ^ 5 * ((toricPoint K 1 (ζ ^ s.val)).1 + 6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
        2 * (tateLaurent K).a₄) =
      ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) := by
  have hu : ζ ^ s.val = ψ hζ s := rfl
  rw [toricPoint_fst_eq, hu, tateLaurent_a₄, laurentOfInt_apply]
  have lhs : (M : LaurentSeries K) ^ 5 * (ofPowerSeries ℤ K (xS (ψ hζ s)) +
      6 * ofPowerSeries ℤ K (xS (ψ hζ s)) ^ 2 + 2 * ofPowerSeries ℤ K (tateA4.map (Int.castRingHom K))) =
      ofPowerSeries ℤ K (PowerSeries.C ((M : K) ^ 5) * fS (ψ hζ s)) := by
    simp only [fS_eq', map_mul, map_add, map_ofNat, map_pow, map_natCast, sq]
  have rhs : ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (PowerSeries.mk (dZ M c)) =
      ofPowerSeries ℤ K (∑ c : ZMod M, PowerSeries.C (ψ hζ (s * c)) *
        (PowerSeries.mk (dZ M c)).map (Int.castRingHom K)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [intSeriesC_eq, smul_ofPowerSeries]
    rfl
  rw [lhs, rhs]
  congr 1
  ext n
  rw [PowerSeries.coeff_C_mul, map_sum, fS, PowerSeries.coeff_mk, ← sum_ψ_dZ hζ s hs n]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_map, PowerSeries.coeff_mk, eq_intCast]

end AnyField

end ToricFourier

universe u in

/-- The Γ₁ integral `q`-expansion / toric-point theorem: five objects `B`, `D`, `b`, `d`
whose slash laws and toric-point Fourier identities hold. -/
theorem exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum (M : ℕ) [NeZero M] :
    ∃ (B : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 2)
      (D : ZMod M → ModularForm (CongruenceSubgroup.Gamma1 M : Subgroup (GL (Fin 2) ℝ)) 4)
      (b d : ZMod M → PowerSeries ℤ),
      (∀ c : ZMod M, IsIntegralQExp (B c) (b c)) ∧
      (∀ c : ZMod M, IsIntegralQExp (D c) (d c)) ∧
      (∀ (c : ZMod M) (γ : SL(2, ℤ)), γ ∈ CongruenceSubgroup.Gamma0 M →
        (⇑(B c) : UpperHalfPlane → ℂ) ∣[(2 : ℤ)] γ = ⇑(B (c * ((γ 0 0 : ℤ) : ZMod M))) ∧
        (⇑(D c) : UpperHalfPlane → ℂ) ∣[(4 : ℤ)] γ = ⇑(D (c * ((γ 0 0 : ℤ) : ZMod M)))) ∧
      ∀ (K : Type u) [Field K] (ζ : K), IsPrimitiveRoot ζ M → ∀ s : ZMod M, s ≠ 0 →
        (M : LaurentSeries K) ^ 3 * (1 + 12 * (toricPoint K 1 (ζ ^ s.val)).1) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (b c) ∧
        (M : LaurentSeries K) ^ 5 *
            ((toricPoint K 1 (ζ ^ s.val)).1 +
                6 * (toricPoint K 1 (ζ ^ s.val)).1 ^ 2 +
              2 * (tateLaurent K).a₄) =
            ∑ c : ZMod M, (ζ ^ (s * c).val) • intSeriesC K (d c) := by
  refine ⟨ToricFourier.B M, ToricFourier.D M, fun c => PowerSeries.mk (ToricFourier.bZ M c),
    fun c => PowerSeries.mk (ToricFourier.dZ M c),
    ToricFourier.isIntegralQExp_B M, ToricFourier.isIntegralQExp_D M,
    fun c γ hγ => ⟨ToricFourier.B_slash M c γ hγ, ToricFourier.D_slash M c γ hγ⟩, ?_⟩
  intro K _ ζ hζ s hs
  exact ⟨ToricFourier.weightTwo K hζ s hs, ToricFourier.weightFour K hζ s hs⟩

/-! ## `E₄³/Δ` separates the `SL(2, ℤ)`-orbits of `ℍ` -/

namespace JSeparatesOrbits

private lemma pow_four_six_of_sq {t x : ℂ} (h : t ^ 2 = x) : t ^ 4 = x ^ 2 ∧ t ^ 6 = x ^ 3 := by
  constructor <;> [rw [show (4:ℕ) = 2 * 2 from rfl]; rw [show (6:ℕ) = 2 * 3 from rfl]] <;>
    rw [pow_mul, h]

theorem exists_scalar {a₁ b₁ a₂ b₂ : ℂ}
    (h₁ : a₁ ^ 3 - b₁ ^ 2 ≠ 0) (h₂ : a₂ ^ 3 - b₂ ^ 2 ≠ 0)
    (R1 : a₁ ^ 3 * b₂ ^ 2 = a₂ ^ 3 * b₁ ^ 2) :
    ∃ w : ℂ, w ≠ 0 ∧ a₂ = w ^ 4 * a₁ ∧ b₂ = w ^ 6 * b₁ := by
  by_cases ha₁ : a₁ = 0
  ·
    subst ha₁
    have hb₁ : b₁ ≠ 0 := by rintro rfl; exact h₁ (by ring)
    have ha₂ : a₂ = 0 := by
      have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1]; ring
      simpa [hb₁] using this
    subst ha₂
    have hb₂ : b₂ ≠ 0 := by rintro rfl; exact h₂ (by ring)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (b₂ / b₁) (by norm_num : 0 < 6)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
      exact ht.elim hb₂ hb₁
    exact ⟨t, ht0, by simp, by rw [ht]; field_simp⟩
  ·
    have ha₂ : a₂ ≠ 0 := by
      intro ha₂; subst ha₂
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      exact h₂ (by rw [hb₂]; ring)
    by_cases hb₁ : b₁ = 0
    · subst hb₁
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      subst hb₂
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₂ / a₁) (by norm_num : 0 < 4)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
        exact ht.elim ha₂ ha₁
      exact ⟨t, ht0, by rw [ht]; field_simp, by simp⟩
    · have hb₂ : b₂ ≠ 0 := by
        intro hb₂
        have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1, hb₂]; ring
        simp [ha₂, hb₁] at this
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₁ * b₂ / (a₂ * b₁)) (by norm_num : 0 < 2)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff, mul_eq_zero, mul_eq_zero] at ht
        rcases ht with (h | h) | (h | h) <;> contradiction
      obtain ⟨ht4, ht6⟩ := pow_four_six_of_sq ht
      have ha : a₂ = t ^ 4 * a₁ := by
        rw [ht4, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -R1
      have hb : b₂ = t ^ 6 * b₁ := by
        rw [ht6, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -(b₁ * b₂) * R1
      exact ⟨t, ht0, ha, hb⟩

lemma int_indep (τ : ℍ) {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = m' * τ + n') : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, coe_im,
    coe_re] at him
  have hm : m = m' := by
    have : ((m : ℝ) - m') * τ.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact_mod_cast sub_eq_zero.1 h0
    · exact absurd h0 τ.im_pos.ne'
  subst hm
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

theorem exists_sl2z_of_lattice_rel (τ₁ τ₂ : ℍ) {u : ℂ} (hu : u ≠ 0)
    {a b c d p q r s : ℤ}
    (h1 : u * (a * τ₁ + b) = τ₂) (h2 : u * (c * τ₁ + d) = 1)
    (h3 : p * (τ₂ : ℂ) + q = u * τ₁) (h4 : r * (τ₂ : ℂ) + s = u) :
    ∃ γ : SL(2, ℤ), γ • τ₁ = τ₂ := by

  have hrow₁ : p * a + q * c = 1 ∧ p * b + q * d = 0 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination p * h1 + q * h2 + h3
  have hrow₂ : r * a + s * c = 0 ∧ r * b + s * d = 1 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination r * h1 + s * h2 + h4
  have hdet : (a * d - b * c) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * d) * hrow₁.1 - (r * a + s * c) * hrow₁.2 + hrow₂.2

  have hz : (c : ℂ) * τ₁ + d ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
  have hτ₂ : (τ₂ : ℂ) * (c * τ₁ + d) = a * τ₁ + b := by
    linear_combination -((c : ℂ) * τ₁ + d) * h1 + ((a : ℂ) * τ₁ + b) * h2
  have him : τ₂.im * Complex.normSq (c * τ₁ + d) = (a * d - b * c) * τ₁.im := by
    have h := congrArg Complex.im
      (show (τ₂ : ℂ) * (Complex.normSq ((c : ℂ) * τ₁ + d) : ℂ) =
          (a * τ₁ + b) * (starRingEnd ℂ) (c * τ₁ + d) by
        rw [← Complex.mul_conj, ← mul_assoc, hτ₂])
    simp only [mul_im, ofReal_re, ofReal_im, mul_zero, add_zero, add_im, add_re, mul_re,
      intCast_re, intCast_im, zero_mul, sub_zero, Complex.conj_re, Complex.conj_im, coe_re,
      coe_im] at h
    rw [zero_add] at h
    rw [h]
    ring
  have hdet1 : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · exfalso
      have hpos : 0 < τ₂.im * Complex.normSq (c * τ₁ + d) :=
        mul_pos τ₂.im_pos (Complex.normSq_pos.2 hz)
      rw [him] at hpos
      have : ((a * d - b * c : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this
      rw [this] at hpos
      linarith [τ₁.im_pos]

  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨γ, ?_⟩
  apply UpperHalfPlane.ext
  rw [coe_specialLinearGroup_apply]
  simp only [γ, algebraMap_int_eq, eq_intCast, ofReal_intCast, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Matrix.empty_val']
  rw [div_eq_iff hz, hτ₂]

theorem E₄_cube_sub_E₆_sq_ne_zero (z : ℍ) : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := fun h0 => by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [h0, zero_div] at h
  exact ModularForm.discriminant_ne_zero z h

end JSeparatesOrbits

open JSeparatesOrbits PeriodPair in

/-- `E₄³/Δ` separates the `SL(2, ℤ)`-orbits of `ℍ`. -/
theorem exists_smul_eq_of_E4_cube_div_discriminant_eq (τ τ' : ℍ)
    (h : (ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ =
      (ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') :
    ∃ γ : SL(2, ℤ), γ • τ = τ' := by

  have R1 : E₄ τ ^ 3 * E₆ τ' ^ 2 = E₄ τ' ^ 3 * E₆ τ ^ 2 := by
    rw [ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq, ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq,
      div_eq_div_iff (by simpa using E₄_cube_sub_E₆_sq_ne_zero τ)
        (by simpa using E₄_cube_sub_E₆_sq_ne_zero τ')] at h
    change E₄ τ ^ 3 * ((E₄ τ' ^ 3 - E₆ τ' ^ 2) / 1728) =
      E₄ τ' ^ 3 * ((E₄ τ ^ 3 - E₆ τ ^ 2) / 1728) at h
    linear_combination -1728 * h

  obtain ⟨w, hw, hwa, hwb⟩ := exists_scalar (E₄_cube_sub_E₆_sq_ne_zero τ)
    (E₄_cube_sub_E₆_sq_ne_zero τ') R1

  set uU : ℂˣ := (Units.mk0 w hw)⁻¹ with huU
  set u : ℂ := (uU : ℂ) with huc
  have hu : u ≠ 0 := uU.ne_zero
  have hwu : w = u⁻¹ := by simp [huc, huU]
  have hΛ : (PeriodPair.ofTau τ').lattice = ((PeriodPair.ofTau τ).scale uU).lattice := by
    apply PeriodPair.lattice_eq_of_g2_eq_of_g3_eq
    · rw [g₂_scale, g₂_ofTau, g₂_ofTau, hwa, ← huc, hwu, inv_pow]; ring
    · rw [g₃_scale, g₃_ofTau, g₃_ofTau, hwb, ← huc, hwu, inv_pow]; ring

  obtain ⟨a, b, h1⟩ : ∃ a b : ℤ, u * (a * τ + b) = τ' := by
    have h := (PeriodPair.ofTau τ').ω₁_mem_lattice
    rw [hΛ, PeriodPair.mem_scale_lattice_iff] at h
    obtain ⟨l, hl, hlω⟩ := h
    obtain ⟨a, b, hab⟩ := PeriodPair.mem_lattice.mp hl
    have hl' : (a : ℂ) * (τ : ℂ) + (b : ℂ) = l := by simpa using hab
    have hlω' : (↑τ' : ℂ) = ↑uU * l := by simpa using hlω
    exact ⟨a, b, by rw [huc, hl', hlω']⟩
  obtain ⟨c, d, h2⟩ : ∃ c d : ℤ, u * (c * τ + d) = 1 := by
    have h := (PeriodPair.ofTau τ').ω₂_mem_lattice
    rw [hΛ, PeriodPair.mem_scale_lattice_iff] at h
    obtain ⟨l, hl, hlω⟩ := h
    obtain ⟨c, d, hcd⟩ := PeriodPair.mem_lattice.mp hl
    have hl' : (c : ℂ) * (τ : ℂ) + (d : ℂ) = l := by simpa using hcd
    have hlω' : (1 : ℂ) = ↑uU * l := by simpa using hlω
    exact ⟨c, d, by rw [huc, hl', hlω']⟩
  obtain ⟨p, q, h3⟩ : ∃ p q : ℤ, p * (τ' : ℂ) + q = u * τ := by
    have h := ((PeriodPair.ofTau τ).scale uU).ω₁_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    obtain ⟨p, q, hpq⟩ := h
    exact ⟨p, q, by simpa using hpq⟩
  obtain ⟨r, s, h4⟩ : ∃ r s : ℤ, r * (τ' : ℂ) + s = u := by
    have h := ((PeriodPair.ofTau τ).scale uU).ω₂_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    obtain ⟨r, s, hrs⟩ := h
    exact ⟨r, s, by simpa using hrs⟩
  exact exists_sl2z_of_lattice_rel τ τ' hu h1 h2 h3 h4

end ModularCurve

end
