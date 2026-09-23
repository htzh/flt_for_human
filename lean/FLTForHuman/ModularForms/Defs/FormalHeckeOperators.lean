/-
  The formal Hecke operators on `PowerSeries`.

  These are the power-series substitution operators the `qExpansion` bridge of the
  Hecke layer is phrased against: `heckeU ℓ` keeps the coefficients in the image of
  `n ↦ ℓ * n` (`f ↦ ∑ n, f (ℓ * n) X ^ n`), `heckeV ℓ` is the dilation
  `X ^ n ↦ X ^ {n ℓ}`, and `heckeT ℓ k = heckeU ℓ + ℓ ^ (k - 1) • heckeV ℓ`.

  FLT provenance, pinned `aa2d8b3`:
  `Definitions/Def_PowerSeries_FormalHeckeOperators.lean` (43 lines), transcribed
  verbatim; only `import Mathlib` is replaced by the specific import. This is a
  definitions module (no `Theorems/` wrapper), so the checker verifies it by name
  against the pin's `Definitions/` file.

  The declarations write their qualified names (`def PowerSeries.heckeU …`, with
  `open PowerSeries` supplying the unqualified occurrences inside the statements)
  rather than sitting inside a `namespace PowerSeries` block: the checker matches
  by **last name**, and `heckeU`/`heckeT` also occur in the pin's
  `Def_ModularForm_HeckeOperator.lean`. The qualified spelling is what lets the
  two collisions be exempted precisely, without also exempting the surface
  `ModularForm.heckeU`/`heckeT` (see `spec/check_flt_statements.py` `OWN_PROOFS`).
  The statement text after each name is the pin's, since the section variable `R`
  is not a binder.

  Note the type clash with the surface Hecke operators of
  `Defs/HeckeOperator.lean`: here the weight is a `ℕ` (`PowerSeries.heckeT ℓ k`),
  while `ModularForm.heckeT` takes `k : ℤ` — the pin's own split, kept as is. The
  two are identified only in `ModularFormClass.qExpansion_heckeT_eq_heckeT`, which
  casts `k : ℕ` to `ℤ` and rewrites with `zpow_natCast`.
-/
import Mathlib.RingTheory.PowerSeries.Basic

set_option autoImplicit false

noncomputable section

open PowerSeries

variable {R : Type*} [CommRing R]

/-- The formal `U_ℓ`: `f ↦ ∑ n, f (ℓ * n) X ^ n`. -/
def PowerSeries.heckeU (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => coeff (ℓ * n) f
  map_add' f g := by ext n; simp
  map_smul' c f := by ext n; simp

@[simp] lemma PowerSeries.coeff_heckeU (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeU ℓ f) = coeff (ℓ * n) f := by
  simp [heckeU]

/-- The formal `V_ℓ`: the dilation `X ^ n ↦ X ^ (n * ℓ)`. -/
def PowerSeries.heckeV (ℓ : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun f := mk fun n => if ℓ ∣ n then coeff (n / ℓ) f else 0
  map_add' f g := by ext n; by_cases h : ℓ ∣ n <;> simp [h]
  map_smul' c f := by ext n; by_cases h : ℓ ∣ n <;> simp [h]

@[simp] lemma PowerSeries.coeff_heckeV (ℓ n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeV ℓ f) = if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeV]

/-- `U` is a left inverse of `V` for `ℓ ≠ 0`. -/
lemma PowerSeries.heckeU_heckeV (ℓ : ℕ) (hℓ : ℓ ≠ 0) (f : R⟦X⟧) :
    heckeU ℓ (heckeV ℓ f) = f := by
  ext n
  simp [Nat.mul_div_cancel_left n (Nat.pos_of_ne_zero hℓ), Dvd.intro n rfl]

/-- The formal `T_ℓ = U_ℓ + ℓ ^ (k - 1) • V_ℓ`. -/
def PowerSeries.heckeT (ℓ k : ℕ) : R⟦X⟧ →ₗ[R] R⟦X⟧ :=
  heckeU ℓ + (ℓ : R) ^ (k - 1) • heckeV ℓ

lemma PowerSeries.coeff_heckeT (ℓ k n : ℕ) (f : R⟦X⟧) :
    coeff n (heckeT ℓ k f) =
      coeff (ℓ * n) f + (ℓ : R) ^ (k - 1) * if ℓ ∣ n then coeff (n / ℓ) f else 0 := by
  simp [heckeT]

end
