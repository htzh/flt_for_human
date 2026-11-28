/-
Every global additive character is a multiple of the standard one.

`AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` (118 pin lines): for a global
additive character `ψ` of `F` there is `a ≠ 0` with `ψ x = stdAddChar (algebraMap a * x)` for every adele
`x` — the normalization that turns the `hψ_inf` hypothesis of the whole trace-dual family into a
*consequence*.

Its three premises are the box measure, SET-AF110B's `NonzeroTrace` (the archimedean existence form) and
the standard character's trace row; no existing module is above all three, so the home is new.

## The rows

* `AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` — 118 pin `S_` lines.

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar.lean>

spec-pin: Theorems/Thm_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar.lean
spec-pin: P2M/Sol/S_AutomorphicForm_exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar.lean

## Landing (SET-AF111, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** Three declarations in 118 pin `S_` lines: the pin's two `private` helpers
  `GlobalAddCharFrequency.forall_eq_of_forall_mk_zero_eq` and
  `…forall_apply_mul_eq_stdAddChar` are transcribed **`private`, as in the pin**, and the headline
  `AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar` is the pin's
  `solution`. The pin's helper namespace `GlobalAddCharFrequency` is a subject name, not a generated
  label, so it is kept. `check_port`: **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw** (private
  helpers are invisible to it); `port_omissions` on the wire: 2 pin publics — 1 declared, 1 folded,
  0 MISSING.
* **Substitutions**: none. All the premises are the port's:
  `NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar`
  (`NonzeroTrace.lean`), `NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace`
  and `(StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK` (`StandardAddCharTrace.lean`), and
  `AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers` /
  `AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles` (the box module). The pin's proof ran
  unchanged; the one spelling that differs is the box lemma, which the port states for a general
  `R K`, so the call carries `(R := 𝓞 F) (K := F)`.
* **Drift**: none measured beyond that `R K` naming; `fun_prop` discharges the continuity goal exactly
  as the pin's `have hc : Continuous ψ := hψ.continuous; fun_prop` does.
* **Axioms**: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; this module carries no `set_option`): downward
  ladder 40000 / 20000 / 10000 / 5000 / 1000 — **silent at 40000, 20000 and 5000, fails at 1000**
  (`whnf` at `:67`, inside `forall_eq_of_forall_mk_zero_eq`'s `hcancel` step). Module floor (every
  proof `sorry`, statements verbatim): **passes at 1000**, so at the 1000 cap the cost is in the
  proof, not in the types.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.AdelicFourier.NonzeroTrace
import FLTForHuman.NumberTheory.NumberField.StandardAddCharTrace
import Mathlib.Tactic

set_option autoImplicit false

open NumberField

namespace GlobalAddCharFrequency

open IsDedekindDomain AutomorphicForm

variable {F : Type} [Field F] [NumberField F]

private theorem forall_eq_of_forall_mk_zero_eq
    (f : AdeleRing (𝓞 F) F → ℂ) (η : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (hfc : Continuous f) (hηc : Continuous η)
    (hfmul : ∀ y z : AdeleRing (𝓞 F) F, f (y + z) = f y * f z)
    (hfF : ∀ x : F, f (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)
    (hηF : ∀ x : F, η (algebraMap F (AdeleRing (𝓞 F) F) x) = 1)
    (harch : ∀ u : InfiniteAdeleRing F,
      f ((u, 0) : AdeleRing (𝓞 F) F) = η ((u, 0) : AdeleRing (𝓞 F) F)) :
    ∀ y : AdeleRing (𝓞 F) F, f y = η y := by
  have hη0 : ∀ z : AdeleRing (𝓞 F) F, η z ≠ 0 := by
    intro z
    have h1 : η z * η (-z) = 1 := by
      rw [← AddChar.map_add_eq_mul η z (-z), add_neg_cancel, AddChar.map_zero_eq_one]
    exact left_ne_zero_of_mul_eq_one h1
  have hadd : ∀ y z t : AdeleRing (𝓞 F) F, t = y + z → f y = η y → f z = η z → f t = η t := by
    intro y z t ht hy hz
    subst ht
    rw [hfmul, AddChar.map_add_eq_mul, hy, hz]
  have hcancel : ∀ y z t : AdeleRing (𝓞 F) F, t = y + z → f t = η t → f z = η z → f y = η y := by
    intro y z t ht hyt hz
    subst ht
    rw [hfmul, AddChar.map_add_eq_mul, hz] at hyt
    exact mul_right_cancel₀ (hη0 z) hyt
  have hfin_principal : ∀ x : F,
      f ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) x) : AdeleRing (𝓞 F) F)
        = η ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) x) : AdeleRing (𝓞 F) F) := by
    intro x
    refine hcancel _ ((algebraMap F (InfiniteAdeleRing F) x, 0) : AdeleRing (𝓞 F) F)
      (algebraMap F (AdeleRing (𝓞 F) F) x) ?_ ((hfF x).trans (hηF x).symm) (harch _)
    exact Prod.ext (zero_add _).symm (add_zero _).symm
  have hclosed : IsClosed {w : FiniteAdeleRing (𝓞 F) F |
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F)} := by
    have hι : Continuous fun w : FiniteAdeleRing (𝓞 F) F => ((0, w) : AdeleRing (𝓞 F) F) :=
      continuous_const.prodMk continuous_id
    exact isClosed_eq (hfc.comp hι) (hηc.comp hι)
  have hrange : Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) ⊆
      {w : FiniteAdeleRing (𝓞 F) F |
        f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F)} := by
    rintro _ ⟨o, rfl⟩
    show f ((0, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) o) : AdeleRing (𝓞 F) F)
      = η ((0, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) o) : AdeleRing (𝓞 F) F)
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) o]
    exact hfin_principal _
  have hint : ∀ w ∈ AdelicBox.integralFiniteAdeles (𝓞 F) F,
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F) := by
    intro w hw
    exact closure_minimal hrange hclosed
      (AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers F hw)
  have hfin : ∀ w : FiniteAdeleRing (𝓞 F) F,
      f ((0, w) : AdeleRing (𝓞 F) F) = η ((0, w) : AdeleRing (𝓞 F) F) := by
    intro w
    obtain ⟨k, hk⟩ := AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (R := 𝓞 F) (K := F) w
    refine hcancel _ ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) k) : AdeleRing (𝓞 F) F)
      ((0, algebraMap F (FiniteAdeleRing (𝓞 F) F) k + w) : AdeleRing (𝓞 F) F)
      ?_ (hint _ hk) (hfin_principal k)
    exact Prod.ext (add_zero (0 : InfiniteAdeleRing F)).symm (add_comm _ _)
  intro y
  refine hadd ((0, y.2) : AdeleRing (𝓞 F) F) ((y.1, 0) : AdeleRing (𝓞 F) F) y ?_ (hfin y.2) (harch y.1)
  exact Prod.ext (zero_add y.1).symm (add_zero y.2).symm

private theorem forall_apply_mul_eq_stdAddChar {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) (a : F)
    (harch : ∀ u : InfiniteAdeleRing F,
      ψ ((algebraMap F (InfiniteAdeleRing F) a * u, 0) : AdeleRing (𝓞 F) F)
        = StandardAddChar.stdAddChar F ((u, 0) : AdeleRing (𝓞 F) F)) :
    ∀ y : AdeleRing (𝓞 F) F,
      ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) = StandardAddChar.stdAddChar F y := by
  have hstd : IsGlobalAddChar F (StandardAddChar.stdAddChar F) :=
    (StandardAddChar.adelicTraceData F).isGlobalAddChar_psiK
  refine forall_eq_of_forall_mk_zero_eq (fun y => ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y))
    (StandardAddChar.stdAddChar F) ?_ hstd.continuous ?_ ?_ hstd.principalInvariant ?_
  · have hc : Continuous ψ := hψ.continuous
    fun_prop
  · intro y z
    show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * (y + z))
      = ψ (algebraMap F (AdeleRing (𝓞 F) F) a * y) * ψ (algebraMap F (AdeleRing (𝓞 F) F) a * z)
    rw [mul_add, AddChar.map_add_eq_mul]
  · intro x
    show ψ (algebraMap F (AdeleRing (𝓞 F) F) a * algebraMap F (AdeleRing (𝓞 F) F) x) = 1
    rw [← map_mul (algebraMap F (AdeleRing (𝓞 F) F)) a x]
    exact hψ.principalInvariant (a * x)
  · intro u
    refine (congrArg ψ ?_).trans (harch u)
    exact Prod.ext rfl (mul_zero _)

end GlobalAddCharFrequency

open GlobalAddCharFrequency AutomorphicForm in
theorem AutomorphicForm.exists_ne_zero_forall_eq_stdAddChar_mul_of_isGlobalAddChar
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ a : F, a ≠ 0 ∧
      (∀ x : AdeleRing (𝓞 F) F,
        ψ x = StandardAddChar.stdAddChar F (algebraMap F (AdeleRing (𝓞 F) F) a * x)) := by
  obtain ⟨a, ha, harch⟩ :=
    NumberField.AdelicFourier.exists_ne_zero_apply_eq_fourierChar_trace_of_isGlobalAddChar F hψ
  have hkey := forall_apply_mul_eq_stdAddChar hψ a fun u =>
    (harch u).trans
      (NumberField.StandardAddChar.stdAddChar_apply_mk_zero_eq_fourierChar_trace F u).symm
  refine ⟨a⁻¹, inv_ne_zero ha, fun x => ?_⟩
  have h := hkey (algebraMap F (AdeleRing (𝓞 F) F) a⁻¹ * x)
  rw [← mul_assoc, ← map_mul (algebraMap F (AdeleRing (𝓞 F) F)) a a⁻¹, mul_inv_cancel₀ ha, map_one,
    one_mul] at h
  exact h

