/-
The trace-dual of the integer lattice is the finite part of the character's vanishing set.

`NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual` (85 pin lines): for a
global additive character `ψ` whose archimedean part is `fourierChar ∘ trace` and `ξ : F`, the finite
adelic character `z ↦ ψ (0, ξ z)` is trivial on the integral finite adeles **iff** `ξ` lies in the trace
dual `FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F)`.

The proof is the finiteness computation `integralFiniteAdeles ⊆ closure (range (algebraMap F …))`
(`AdelicBox/Measure.lean`) glued to the archimedean trace formula
(`NumberField/StandardAddCharTrace.lean`, SET-AF108H). The home is new because both premises are above
`NumberTheory/AdelicFourier.lean` — the box module reaches the Fourier development through
`AdelicFourier/Transform.lean`, so inserting there would be a cycle. `PureTensorSummable.lean` is the
sibling module of the same kind (one consumer of the box measure above the Fourier API).

## The rows

* `NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual` — 85 pin `S_` lines.
* `NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles`
  — 144 pin `S_` lines, 13 declarations (SET-AF110E).
* `NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual`
  — 99 pin `S_` lines, 7 declarations (SET-AF110E).

Reference (public mirror, pinned):
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean>

spec-pin: Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual.lean
spec-pin: Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles.lean
spec-pin: Theorems/Thm_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual.lean

## Landing (AF109G, pin `aa2d8b3` against the port's mathlib `v4.34.0`)

* **Surface.** One public declaration, 139 lines (107 of them the module the scaffold left, the rest
  this note) against the pin's 85. `check_port`:
  **1 ok / 0 mismatch / 0 missing / 0 own / 0 kw**.
* **Substitutions**: none. Both premises are the port's
  (`NumberField.AdelicBox.integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers`,
  `NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace`), and the
  pin's proof ran unchanged but for the four drifts below.
* **Drift (four sites, none a statement change).**
  - `algebraMap_mem_adicCompletionIntegers` is `NumberField.AdelicLevel.…` in the port, not
    `NumberField.AdelicBox.…` as in the pin; opening `NumberField.AdelicLevel` for it is **not**
    allowed here — that namespace declares a second `integralFiniteAdeles` (identical type
    `Set (FiniteAdeleRing (𝓞 F) F)`), and opening both makes every applied occurrence of the bare
    name an *ambiguous term* (`AdelicBox.integralFiniteAdeles` vs `AdelicLevel.integralFiniteAdeles`).
    `open`-order does not fix it (measured, both orders ambiguous), so the **lemma** is spelled
    qualified and the pin's bare `integralFiniteAdeles` stays bare in the statement.
  - `Circle.exp_eq_one` moved to `Mathlib/Analysis/SpecialFunctions/Complex/Circle.lean` in
    `v4.34.0`; that single module is the one import added (its `.olean` exists).
  - the pin's `(𝓞 F) F` explicit instance args to `algebraMap_mem_adicCompletionIntegers` are
    implicit here, so the call is `… v α`.
  - `Mathlib.Analysis.SpecialFunctions.Complex.Circle` is the *only* import added; `Mathlib.Tactic`
    was already there.
* **Engine gate**: pin sources 2, pin decls 2, module decls 1; **1 by hash** (`ecf63fe9dd8c820ada2b`),
  0 by name, 0 unaccounted.
* **Axioms**: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: 0 clusters. **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; the module carries no `set_option`):
  downward ladder 40000 / 20000 / 10000 / 5000 / 1000 — **silent at 10000, fails at 5000**
  (`isDefEq`, in the `push_cast; linarith` step of the forward direction). Module floor (the row's
  proof `sorry`, statement verbatim): **passes at 5000, fails at 1000** (`isDefEq`, reported at the
  statement's `FractionalIdeal.dual` subterm), so at the 1000 cap the cost is in the types.

## Landing (SET-AF110E, same pin and mathlib)

* **Surface.** Two insertions, **14 new declarations in 214 lines** (the module moves from 189 to 398
  lines; the pin's two `S_` blocks are 144 + 99 = 243 lines and 13 + 7 = 20 declarations, of which one
  is substituted twice and two are merged). `check_port`: **17 ok / 0 mismatch / 0 missing / 0 own /
  0 kw** (3 before) — every public declaration of the module matched a wire row.
* **Two merges forced by the dropped generated namespaces.** The pin's `…Ws25.Biann` and `…Ws25ANN`
  blocks both declare `mul_mem_integralFiniteAdeles` (same statement, binder spelling only), and
  `…Ws25ANN.addChar_zero_add` has the *same* `S_` statement hash as `…Ws25.Biann.apply_zero_add`
  (`3e08ee8b5fc6`). Declaring either twice would be an FR-0274 collision and a `dedup --within`
  cluster, so each is declared **once** (`mul_mem_integralFiniteAdeles`, `apply_zero_add`).
* **Substitutions (imported, not restated).** `add_mem_integralFiniteAdeles` and
  `neg_mem_integralFiniteAdeles` → `NumberField.AdelicBox.BoxKernel.…`
  (`NumberTheory/AdelicBox/Measure.lean:161` and `:166`), statement-identical; both take `F`
  explicitly there and implicitly in the pin. Nothing else is unported.
* **Drift (proof-level only, but for `mul_apply`/`neg_apply`/`ann_impl`'s `F`).** `F` is a section
  variable in the port for those three: the pin's `variable (F : Type)` puts `F` in **no binder** of its
  `S_` text, and writing it as a binder read `MISMATCH` for the first two (measured). `finitePart` is
  `noncomputable`; `algebraMap_mem_adicCompletionIntegers` is spelled `NumberField.AdelicLevel.…` (the
  AF109G note above); `one_le_dual_one`'s extra membership argument in the pin is here the application
  of `1 ≤ dual`; the pin's `set_option maxHeartbeats 1600000` is not installed.
* **Engine gate** (pin-vs-module declaration diff, not last-name credit): pin sources **6**, pin decls
  **24**, module public decls **17** — **17 by hash**, 0 by name, **0 unaccounted**, and 17 *distinct*
  pin rows hit (each port declaration against its own wire row).
* **Axioms**: all 17 public declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`move_dead --dry-run`**: 0 declarations, 0 lines. **`dedup --within`**: **2 clusters, both the
  pin's own headline↔engine pairs** — `forall_iff_mem` (46 L) ↔ the `…of_forall_iff_mem_integral
  FiniteAdeles` headline (37 L; `S_…of_forall_iff_mem_integralFiniteAdeles.lean:81` and `:131`, the
  pin's `solution` being `forall_iff_mem hψ hψ_inf u`), and `ann_impl` (36 L) ↔ the
  `…iff_exists_mem_traceDual` headline (13 L; `S_…iff_exists_mem_traceDual.lean:50` and `:89`,
  `solution := ann_impl …`). Each pair is
  two `S_` rows of the same wire, so neither declaration can be dropped; the pin's own blocks carry the
  duplication.
* **Heartbeat probe** (recorded, **never installed**; this module carries no `set_option`):
  downward ladder 40000 / 10000 / 5000 — **silent at 40000 and 10000, fails at 5000** (`whnf`, first
  at `:74`, the AF109G headline's *statement*). The first failure is therefore **above every AF110E
  line**: the two insertions add no measurable cost (they elaborate inside the AF109G row's budget).
* **Linters**: none silenced; `lake env lean` at the 200 k edit-loop cap is silent and the locked
  `lake build` logs no warning line of this file.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.NumberField.StandardAddCharTrace
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic

set_option autoImplicit false

open NumberField NumberField.AdelicFourier NumberField.AdelicBox AutomorphicForm IsDedekindDomain MeasureTheory
open scoped Classical FourierTransform nonZeroDivisors

theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (ξ : F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F,
        ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ * z) = 1)
      ↔ ξ ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F) := by
  set ιξ := algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ
  have hιO : ∀ α : 𝓞 F, algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α
      ∈ integralFiniteAdeles (𝓞 F) F := fun α v =>
    NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v α
  have hιcompat : ∀ α : 𝓞 F,
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (α : F)
        = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α := fun α =>
    (IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F) α).symm

  have hfc : ∀ t : ℝ, (↑(Real.fourierChar t) : ℂ) = 1 ↔ ∃ n : ℤ, t = n := by
    intro t
    rw [show ((1 : ℂ) = ((1 : Circle) : ℂ)) from rfl, Circle.coe_inj,
      Real.fourierChar_apply', Circle.exp_eq_one]
    have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨n, mul_left_cancel₀ h2π ?_⟩
      linarith [hn]
    · rintro ⟨n, rfl⟩
      exact ⟨n, by ring⟩
  have h1ne : (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := one_ne_zero
  constructor
  · intro h
    rw [FractionalIdeal.mem_dual h1ne]
    intro a ha
    obtain ⟨α, hα⟩ := (FractionalIdeal.mem_one_iff _).mp ha
    subst hα
    rw [Algebra.traceForm_apply]
    have hval : ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1 := h _ (hιO α)
    rw [← hιcompat, ← map_mul,
      NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
        F hψ hψ_inf (ξ * (α : F))] at hval
    obtain ⟨n, hn⟩ := (hfc _).mp hval
    refine ⟨-n, ?_⟩
    have : ((Algebra.trace ℚ F (ξ * (α : F)) : ℚ) : ℝ) = ((-n : ℤ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this.symm
  · intro hξ z hz
    have hχ_cont : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ψ (0, ιξ * w)) := by
      have : Continuous (fun w : FiniteAdeleRing (𝓞 F) F => ((0, ιξ * w) : AdeleRing (𝓞 F) F)) :=
        continuous_const.prodMk (continuous_const.mul continuous_id)
      exact hψ.continuous.comp this
    set K : Set (FiniteAdeleRing (𝓞 F) F) := {w | ψ (0, ιξ * w) = 1}
    have hK_closed : IsClosed K := isClosed_eq hχ_cont continuous_const
    have hιO_K : Set.range (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F)) ⊆ K := by
      rintro _ ⟨α, rfl⟩
      show ψ (0, ιξ * algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) α) = 1
      rw [← hιcompat, ← map_mul,
        NumberField.AdelicFourier.addChar_zero_finitePart_algebraMap_eq_fourierChar_neg_trace
          F hψ hψ_inf (ξ * (α : F))]
      have htr : Algebra.trace ℚ F (ξ * (α : F)) ∈ (algebraMap ℤ ℚ).range := by
        have := (FractionalIdeal.mem_dual h1ne).mp hξ (α : F)
          ((FractionalIdeal.mem_one_iff _).mpr ⟨α, rfl⟩)
        rwa [Algebra.traceForm_apply] at this
      obtain ⟨n, hn⟩ := htr
      refine (hfc _).mpr ⟨-n, ?_⟩
      have : (algebraMap ℤ ℚ) n = (n : ℚ) := by simp [eq_intCast]
      rw [← hn, this]; push_cast; ring
    have hdense := integralFiniteAdeles_subset_closure_range_algebraMap_ringOfIntegers F
    exact hK_closed.closure_subset_iff.mpr hιO_K (hdense hz)

/-
## SET-AF110 insertion: NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles

The finite-part vanishing set is self-dual under the integral finite adeles.

`NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles`
(144 pin lines): `u` lies in `integralFiniteAdeles` iff the vanishing of the finite part on
`integralFiniteAdeles` is *hereditary* along `u` — the `IntegralFiniteAdeles`-module form of the
trace-dual criterion this module states.

The wire's `S_` block is **13 declarations** (144 lines) in its generated label namespace `…Ws25.Biann`;
the label comes off, so the prelude and the headline sit in `NumberField.AdelicFourier`. Twelve are
transcribed verbatim below. The one **substitution** is
`add_mem_integralFiniteAdeles` → `NumberField.AdelicBox.BoxKernel.add_mem_integralFiniteAdeles`
(`NumberTheory/AdelicBox/Measure.lean:161`), statement-identical up to binder spelling; it is imported,
not restated. Proof drift: the port spells `algebraMap_mem_adicCompletionIntegers` qualified as
`NumberField.AdelicLevel.…` (this module may not `open NumberField.AdelicLevel` — it declares a second
`integralFiniteAdeles`; see the AF109G note above), and its instance arguments are implicit there. The
pin's `set_option maxHeartbeats 1600000` is not installed.
-/

variable {F : Type} [Field F] [NumberField F]

theorem NumberField.AdelicFourier.mul_mem_integralFiniteAdeles {y z : FiniteAdeleRing (𝓞 F) F}
    (hy : y ∈ integralFiniteAdeles (𝓞 F) F) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) :
    y * z ∈ integralFiniteAdeles (𝓞 F) F := fun v => mul_mem (hy v) (hz v)

theorem NumberField.AdelicFourier.algebraMap_coe_mem_integralFiniteAdeles (q : 𝓞 F) :
    algebraMap F (FiniteAdeleRing (𝓞 F) F) (algebraMap (𝓞 F) F q) ∈ integralFiniteAdeles (𝓞 F) F :=
  fun v => NumberField.AdelicLevel.algebraMap_mem_adicCompletionIntegers v q

noncomputable def NumberField.AdelicFourier.finitePart (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) :
    AddChar (FiniteAdeleRing (𝓞 F) F) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHom.inr (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))

@[scoped simp] theorem NumberField.AdelicFourier.finitePart_apply
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (x : FiniteAdeleRing (𝓞 F) F) :
    finitePart ψ x = ψ (0, x) := rfl

theorem NumberField.AdelicFourier.apply_zero_add (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ)
    (a b : FiniteAdeleRing (𝓞 F) F) :
    ψ (0, a + b) = ψ (0, a) * ψ (0, b) := by
  rw [← finitePart_apply, ← finitePart_apply, ← finitePart_apply, AddChar.map_add_eq_mul]

def NumberField.AdelicFourier.annih (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) :
    Set (FiniteAdeleRing (𝓞 F) F) :=
  {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}

theorem NumberField.AdelicFourier.mem_annih {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {w : FiniteAdeleRing (𝓞 F) F} :
    w ∈ annih ψ ↔ ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1 := Iff.rfl

theorem NumberField.AdelicFourier.mul_mem_annih {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {w z : FiniteAdeleRing (𝓞 F) F}
    (hw : w ∈ annih ψ) (hz : z ∈ integralFiniteAdeles (𝓞 F) F) : w * z ∈ annih ψ :=
  fun z' hz' => by rw [mul_assoc]; exact hw _ (mul_mem_integralFiniteAdeles hz hz')

theorem NumberField.AdelicFourier.apply_zero_mul_eq_one_of_mem
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    {u w : FiniteAdeleRing (𝓞 F) F} (hu : u ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ annih ψ) : ψ (0, u * w) = 1 := by
  rw [mul_comm]; exact hw u hu

theorem NumberField.AdelicFourier.mem_one_of_forall_mul_mem {I : FractionalIdeal (𝓞 F)⁰ F}
    (hI : I ≠ 0) {q : F}
    (hq : ∀ r ∈ I, q * r ∈ I) : q ∈ (1 : FractionalIdeal (𝓞 F)⁰ F) := by
  have hle : FractionalIdeal.spanSingleton (𝓞 F)⁰ q * I ≤ I :=
    FractionalIdeal.spanSingleton_mul_le_iff.mpr hq
  have hle' : FractionalIdeal.spanSingleton (𝓞 F)⁰ q ≤ 1 := by
    calc FractionalIdeal.spanSingleton (𝓞 F)⁰ q
        = FractionalIdeal.spanSingleton (𝓞 F)⁰ q * I * I⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hI, mul_one]
      _ ≤ I * I⁻¹ := mul_le_mul' hle le_rfl
      _ = 1 := mul_inv_cancel₀ hI
  exact hle' (FractionalIdeal.mem_spanSingleton_self (S := (𝓞 F)⁰) q)

theorem NumberField.AdelicFourier.forall_iff_mem
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F := by
  have hdual := NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual
    F hψ hψ_inf
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero (A := ℤ) (K := ℚ) one_ne_zero
  constructor
  · intro h

    obtain ⟨k, hk⟩ := exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F u
    set q : F := -k with hq
    set u₀ := algebraMap F (FiniteAdeleRing (𝓞 F) F) k + u with hu₀
    have hu : u = algebraMap F (FiniteAdeleRing (𝓞 F) F) q + u₀ := by
      rw [hu₀, hq, map_neg]; abel

    have hqA : ∀ w ∈ annih ψ, ψ (0, algebraMap F (FiniteAdeleRing (𝓞 F) F) q * w) = 1 := by
      intro w hw
      have h1 : ψ (0, u * w) = 1 := h w hw
      rw [hu, add_mul, apply_zero_add, apply_zero_mul_eq_one_of_mem hk hw, mul_one] at h1
      exact h1

    have hqD : ∀ r ∈ D, q * r ∈ D := by
      intro r hr
      have hrA : algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ annih ψ := (hdual r).mpr hr
      refine (hdual (q * r)).mp fun z hz => ?_
      have := hqA _ (mul_mem_annih hrA hz)
      rwa [← mul_assoc, ← map_mul] at this

    obtain ⟨q', hq'⟩ :=
      (FractionalIdeal.mem_one_iff (S := (𝓞 F)⁰)).mp (mem_one_of_forall_mul_mem hD0 hqD)
    rw [hu, ← hq']
    exact NumberField.AdelicBox.BoxKernel.add_mem_integralFiniteAdeles F
      (algebraMap_coe_mem_integralFiniteAdeles q') hk
  · intro hu w hw
    exact apply_zero_mul_eq_one_of_mem hu hw

/- The wire's `solution` row: the pin's headline is the one-line wrapper
`forall_iff_mem hψ hψ_inf u`, kept so that the module states the row at the published name. -/
theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_of_forall_iff_mem_integralFiniteAdeles
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (u : FiniteAdeleRing (𝓞 F) F) :
    (∀ w : FiniteAdeleRing (𝓞 F) F,
        (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1) → ψ (0, u * w) = 1)
      ↔ u ∈ integralFiniteAdeles (𝓞 F) F :=
  NumberField.AdelicFourier.forall_iff_mem hψ hψ_inf u

/-
## SET-AF110 insertion: NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual

The finite-part vanishing set, with the `w`-coset form of the trace dual.

`NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual` (99 pin
lines): the finite part vanishes at `w` on the integral finite adeles iff `w` differs from a principal
adele of a trace-dual element by an integral element. It is the *coset* form of
`forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual`, and the form a Poisson-summation consumer
holds.

The wire's `S_` block is **7 declarations** (99 lines) in its generated label namespace `…Ws25ANN`;
six are carried below (the seventh is the headline). Substitutions, imported not restated:
`neg_mem_integralFiniteAdeles` → `NumberField.AdelicBox.BoxKernel.neg_mem_integralFiniteAdeles`
(`NumberTheory/AdelicBox/Measure.lean:166`), and the pin's `…Ws25ANN.mul_mem_integralFiniteAdeles`,
whose statement is identical to the `…Ws25.Biann` row transcribed above, is that one declaration — the
two generated namespaces collapse into `NumberField.AdelicFourier`, so declaring it twice would be an
FR-0274 collision and a `dedup --within` cluster. For the same reason the pin's
`…Ws25ANN.addChar_zero_add` (its `S_` hash `3e08ee8b5fc6` equals `…Ws25.Biann.apply_zero_add`'s) is
`apply_zero_add` above, declared once. Drift, all measured: the two `BoxKernel` lemmas have implicit
`F` in the port, so the pin's `… F` applications drop the argument; `mul_apply`, `neg_apply` and
`ann_impl` take `F` from the module's `variable` (the pin's `variable (F : Type)` puts `F` in no
binder of its `S_` text, and writing it as a binder read MISMATCH for the first two); and
`one_le_dual_one`'s extra membership argument in the pin is the application of `1 ≤ dual` here.
-/
theorem NumberField.AdelicFourier.mul_apply (u z : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (u * z) v = u v * z v := rfl

theorem NumberField.AdelicFourier.neg_apply (u : FiniteAdeleRing (𝓞 F) F)
    (v : HeightOneSpectrum (𝓞 F)) : (-u) v = -(u v) := rfl

theorem NumberField.AdelicFourier.ann_impl {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F := by

  have ker := fun ξ : F =>
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_mem_traceDual F hψ hψ_inf ξ
  have h1 : (1 : F) ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) :
      FractionalIdeal (𝓞 F)⁰ F) :=
    (FractionalIdeal.one_le_dual_one ℤ ℚ) (FractionalIdeal.one_mem_one (𝓞 F)⁰)
  have hO : ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, z) = 1 := fun z hz => by
    simpa only [map_one, one_mul] using (ker 1).mpr h1 z hz
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  constructor
  · intro h
    obtain ⟨k, hk⟩ :=
      NumberField.AdelicBox.exists_algebraMap_add_mem_integralFiniteAdeles (𝓞 F) F w
    refine ⟨-k, ?_, ?_⟩
    · refine (ker (-k)).mp fun z hz => ?_

      have hsplit : ι (-k) * z = w * z + (-(ι k + w)) * z := by rw [map_neg]; ring
      rw [hsplit, apply_zero_add, h z hz, one_mul]
      exact hO _ (mul_mem_integralFiniteAdeles
        (NumberField.AdelicBox.BoxKernel.neg_mem_integralFiniteAdeles F hk) hz)
    · have : w - ι (-k) = ι k + w := by rw [map_neg, sub_neg_eq_add, add_comm]
      rw [this]; exact hk
  · rintro ⟨r, hr, hu⟩ z hz
    have hsplit : w * z = ι r * z + (w - ι r) * z := by ring
    rw [hsplit, apply_zero_add, (ker r).mpr hr z hz, one_mul]
    exact hO _ (mul_mem_integralFiniteAdeles hu hz)

theorem NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ))
    (w : FiniteAdeleRing (𝓞 F) F) :
    (∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1)
      ↔ ∃ r : F, r ∈ (FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) : FractionalIdeal (𝓞 F)⁰ F)
          ∧ w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F :=
  NumberField.AdelicFourier.ann_impl hψ hψ_inf w

