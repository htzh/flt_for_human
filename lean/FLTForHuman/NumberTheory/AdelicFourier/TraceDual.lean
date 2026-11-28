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
spec-pin: Theorems/Thm_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_measure_setOf_forall_addChar_finitePart_mul_eq_one.lean
spec-pin: Theorems/Thm_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.lean
spec-pin: P2M/Sol/S_NumberField_AdelicFourier_isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one.lean

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

## Landing (SET-AF111, same pin and mathlib)

* **Surface.** Two insertions, **5 new declarations in 273 lines of code** (the module moves from 445
  to 718 code lines; this note is the rest). The pin's two `S_` blocks are 263 + 117 = 380 lines and
  7 + 6 = 13 declarations, and the 13 rows map to 11 declarations: 2 are the headlines the scaffold
  wrote, 2 are declarations this module already had (`algebraMap_coe_mem_integralFiniteAdeles` and
  `mul_mem_integralFiniteAdeles`, covering the three rows that spell them), 2 are substituted from
  modules above (`add_mem_integralFiniteAdeles` twice, `sub_mem_integralFiniteAdeles`), and 5 are new
  here: `exists_eq_coe_of_algebraMap_mem`, `ncard_map_eq_absNorm`, `measure_annih_eq`
  (`S_…measure….lean:41`, `:59`, `:91`), `continuous_apply_zero` and `isCompact_and_isOpen`
  (`S_…isCompact….lean:40`, `:44`). `check_port`: **24 ok / 0 mismatch / 0 missing / 0 own / 0 kw**
  (19 before).
* **Substitutions (imported, not restated).** `add_mem_integralFiniteAdeles` →
  `NumberField.AdelicBox.BoxKernel.add_mem_integralFiniteAdeles` (`NumberTheory/AdelicBox/Measure.lean:161`);
  `sub_mem_integralFiniteAdeles` → `NumberField.AdelicFourier.sub_mem_integralFiniteAdeles`
  (`NumberTheory/AdelicFourier/Space.lean:442`, which takes `F` **explicitly** — that section's
  `variable (F : Type)` — so the call is `sub_mem_integralFiniteAdeles F …`); and
  `algebraMap_coe_mem_integralFiniteAdeles` / `mul_mem_integralFiniteAdeles` are this module's own
  (`:216` and `:220`). `import FLTForHuman.NumberTheory.AdelicFourier.Space` is the one import added
  for the third; it is acyclic (`Space.lean` does not reach this module) and it is the *only* way to
  have the pin's `sub_mem_integralFiniteAdeles` row in scope: **declaring it here would be an FR-0274
  collision**, since `Space.lean` already declares that public full name and `PureTensorPoisson.lean`
  imports both modules.
* **Engine gate** (`tools/deps/port_omissions.py`): **39 pin public declarations — 26 declared,
  6 imported (6 of them alpha only), 5 folded, 2 MISSING.**
  - One MISSING is this section's: `S_…measure….lean:33 sub_mem_integralFiniteAdeles`. The row *is*
    stated by the port (`Space.lean:442`) and now sits in this module's import closure, but that copy
    spells its conclusion `AdelicBox.integralFiniteAdeles …` where the pin (and this module) spell it
    bare, so `port_omissions`' alpha tier — a text comparison — rejects the credit. De-qualifying
    `Space.lean:442`–`:444` (statement-preserving: that module opens `NumberField.AdelicBox`) would
    turn the row into an `ALPHA` credit; it is outside this order's three files, so it is reported,
    not edited.
  - The other is pre-existing: `S_…iff_exists_mem_traceDual.lean:44 addChar_zero_add`, the AF110E
    merge described above (`:81`), which no declaration named `addChar_zero_add` can credit.
* **Drift (proof-level only).** `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (`v4.34.0` deprecation, in
  `isCompact_and_isOpen`'s `iInter` step); the pin's `haveI : Finite (𝓞 F ⧸ I)` is **`have`** in both
  `ncard_map_eq_absNorm` and `measure_annih_eq` — `linter.style.haveILetI` rejects `haveI`/`letI` for
  a `Prop`-valued class and a local hypothesis of class type is already an instance (FR-0323);
  `measure_annih_eq`'s `coeIdeal_differentIdeal` is spelled positionally `ℤ ℚ F (𝓞 F)`; and the pin's
  `set_option maxHeartbeats 1600000` is not installed.
* **Axioms**: all 24 public declarations ⊆ `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
* **`dedup --within`**: **4 intra-module clusters**, all the pin's own headline↔engine pairs —
  `forall_iff_mem` ↔ `…of_forall_iff_mem_integralFiniteAdeles` and `ann_impl` ↔
  `…iff_exists_mem_traceDual` (both AF110E, above), plus this section's `measure_annih_eq` (157 L) ↔
  `measure_setOf_forall_addChar_finitePart_mul_eq_one` (21 L; `S_…measure….lean:91` and `:251`) and
  `isCompact_and_isOpen` (60 L) ↔ `isCompact_and_isOpen_setOf_…` (11 L; `S_…isCompact….lean:44` and
  `:107`, whose `solution` is the one-line wrapper `isCompact_and_isOpen hψ hψ_inf`). Each pair is two
  `S_` rows of the same wire, so neither declaration can be dropped.
* **`move_dead --dry-run`**: 0 declarations, 0 lines.
* **Heartbeat probe** (recorded, **never installed**; this module carries no `set_option`): downward
  ladder 40000 / 20000 / 10000 / 5000 — **silent at 40000 and 20000, fails at 10000** (`isDefEq`, first
  at `:548`, the `congrArg (algebraMap (𝓞 F) F)` inside `measure_annih_eq`'s `hσD` — a new SET-AF111
  line). The insertion therefore raises the module's cost above AF110E's record (which failed at 5000):
  five new declarations, three of them measure-theoretic, are no longer free. Module floor (every
  proof `sorry`, statements verbatim): **silent at 10000 and 5000, fails at 1000** (`isDefEq` at
  `:132`, the AF109G headline's *statement* — the same site AF110E recorded), so at the 1000 cap the
  cost is still in the types.
-/
import FLTForHuman.AutomorphicForm.Adelic.WhittakerCoefficient
import FLTForHuman.NumberTheory.AdelicBox.Measure
import FLTForHuman.NumberTheory.AdelicFourier.Space
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

/-
## SET-AF111 insertion: NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one

The measure of the trace-dual vanishing set.

`NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one` (263 pin lines): the Haar
measure of `{u | ∀ z ∈ integralFiniteAdeles, ψ (0, u z) = 1}` is the covolume of the trace dual — the
measure-theoretic form of the criterion this module states.
-/
theorem NumberField.AdelicFourier.exists_eq_coe_of_algebraMap_mem {ξ : F}
    (h : algebraMap F (FiniteAdeleRing (𝓞 F) F) ξ ∈ integralFiniteAdeles (𝓞 F) F) :
    ∃ e : 𝓞 F, ξ = (e : F) := by
  have hset : (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) 0
      + algebraMap F (FiniteAdeleRing (𝓞 F) F) ((1 : 𝓞 F) : F) * z) '' integralFiniteAdeles (𝓞 F) F
      = integralFiniteAdeles (𝓞 F) F := by
    have : (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) 0
        + algebraMap F (FiniteAdeleRing (𝓞 F) F) ((1 : 𝓞 F) : F) * z) = id := by
      funext z
      rw [show ((1 : 𝓞 F) : F) = 1 from map_one (algebraMap (𝓞 F) F), map_zero, map_one,
        zero_add, one_mul, id]
    rw [this, Set.image_id]
  have hLS := NumberField.AdelicBox.algebraMap_mem_image_integralFiniteAdeles_iff F 1 one_ne_zero 0 ξ
  rw [hset] at hLS
  obtain ⟨e, he⟩ := hLS.mp h
  refine ⟨e, ?_⟩
  rw [he, show ((1 : 𝓞 F) : F) = 1 from map_one (algebraMap (𝓞 F) F), zero_add, one_mul]

theorem NumberField.AdelicFourier.ncard_map_eq_absNorm {a : 𝓞 F} (ha : a ≠ 0) {𝔡 𝔟 : Ideal (𝓞 F)}
    (h : Ideal.span {a} = 𝔡 * 𝔟) :
    ((𝔟.map (Ideal.Quotient.mk (Ideal.span {a})) : Ideal (𝓞 F ⧸ Ideal.span {a})) :
        Set (𝓞 F ⧸ Ideal.span {a})).ncard = Ideal.absNorm 𝔡 := by
  set I : Ideal (𝓞 F) := Ideal.span {a} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact ha
  have h𝔟0 : 𝔟 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot] at h
    exact hI0 h
  have hle : I ≤ 𝔟 := by rw [h]; exact Ideal.mul_le_right
  have : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  set Q : Ideal (𝓞 F ⧸ I) := 𝔟.map (Ideal.Quotient.mk I) with hQ

  have h1 : Nat.card (𝓞 F ⧸ I) = Nat.card Q * Nat.card ((𝓞 F ⧸ I) ⧸ Q) :=
    Submodule.card_eq_card_quotient_mul_card Q
  have h2 : Nat.card ((𝓞 F ⧸ I) ⧸ Q) = Nat.card (𝓞 F ⧸ 𝔟) :=
    Nat.card_congr (DoubleQuot.quotQuotEquivQuotOfLE hle).toEquiv
  have h3 : Nat.card (𝓞 F ⧸ I) = Ideal.absNorm I :=
    ((Ideal.absNorm_apply I).trans (Submodule.cardQuot_apply _)).symm
  have h4 : Nat.card (𝓞 F ⧸ 𝔟) = Ideal.absNorm 𝔟 :=
    ((Ideal.absNorm_apply 𝔟).trans (Submodule.cardQuot_apply _)).symm
  have h5 : Ideal.absNorm I = Ideal.absNorm 𝔡 * Ideal.absNorm 𝔟 := by
    rw [h, map_mul]
  have h𝔟N : Ideal.absNorm 𝔟 ≠ 0 := fun h0 => h𝔟0 (Ideal.absNorm_eq_zero_iff.mp h0)
  have key : Nat.card Q * Ideal.absNorm 𝔟 = Ideal.absNorm 𝔡 * Ideal.absNorm 𝔟 := by
    rw [← h5, ← h3, h1, h2, h4]
  have := mul_right_cancel₀ h𝔟N key
  rw [← Nat.card_coe_set_eq]
  exact this

theorem NumberField.AdelicFourier.measure_annih_eq
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ν {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      = (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ENNReal) * ν (integralFiniteAdeles (𝓞 F) F) := by
  have hann :=
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
      F hψ hψ_inf
  set A : Set (FiniteAdeleRing (𝓞 F) F) :=
    {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} with hA
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  have hD0 : D ≠ 0 := FractionalIdeal.dual_ne_zero (A := ℤ) (K := ℚ) one_ne_zero
  have hmemA : ∀ w, w ∈ A ↔ ∃ r : F, r ∈ D ∧
      w - algebraMap F (FiniteAdeleRing (𝓞 F) F) r ∈ integralFiniteAdeles (𝓞 F) F :=
    fun w => hann w

  have hOD : ∀ e : 𝓞 F, (e : F) ∈ D := fun e =>
    FractionalIdeal.one_le_dual_one ℤ ℚ
      ((FractionalIdeal.mem_one_iff (S := (𝓞 F)⁰)).mpr ⟨e, rfl⟩)

  set 𝔡 : Ideal (𝓞 F) := differentIdeal ℤ (𝓞 F) with h𝔡
  have h𝔡D : (𝔡 : FractionalIdeal (𝓞 F)⁰ F) = D⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have h𝔡0 : 𝔡 ≠ ⊥ := by
    intro h0
    rw [h0, FractionalIdeal.coeIdeal_bot] at h𝔡D
    exact inv_ne_zero hD0 h𝔡D.symm
  have hN0 : Ideal.absNorm 𝔡 ≠ 0 := fun h0 => h𝔡0 (Ideal.absNorm_eq_zero_iff.mp h0)
  set a : 𝓞 F := (Ideal.absNorm 𝔡 : 𝓞 F) with ha_def
  have ha𝔡 : a ∈ 𝔡 := Ideal.absNorm_mem 𝔡
  have ha0 : a ≠ 0 := by rw [ha_def]; exact Nat.cast_ne_zero.mpr hN0
  have haF : (a : F) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero ha0)
  obtain ⟨𝔟, h𝔟⟩ : 𝔡 ∣ Ideal.span {a} := Ideal.dvd_span_singleton.mpr ha𝔡

  have h𝔟D : (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * D := by
    have h1 : (↑(Ideal.span {a}) : FractionalIdeal (𝓞 F)⁰ F) = ↑(𝔡 * 𝔟) := by rw [h𝔟]
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_mul, h𝔡D] at h1

    calc (𝔟 : FractionalIdeal (𝓞 F)⁰ F) = D * (D⁻¹ * ↑𝔟) := by
          rw [← mul_assoc, mul_inv_cancel₀ hD0, one_mul]
      _ = D * FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) := by rw [← h1]
      _ = FractionalIdeal.spanSingleton (𝓞 F)⁰ (a : F) * D := mul_comm _ _

  have h𝔟_div : ∀ b ∈ 𝔟, (b : F) * (a : F)⁻¹ ∈ D := by
    intro b hb
    have hbF : (b : F) ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) :=
      (FractionalIdeal.mem_coeIdeal (S := (𝓞 F)⁰)).mpr ⟨b, hb, rfl⟩
    rw [h𝔟D] at hbF
    obtain ⟨r, hr, hbr⟩ := FractionalIdeal.mem_singleton_mul.mp hbF
    rw [hbr, mul_comm (a : F) r, mul_assoc, mul_inv_cancel₀ haF, mul_one]
    exact hr
  have hD_mul : ∀ r ∈ D, ∃ b ∈ 𝔟, (b : F) = (a : F) * r := by
    intro r hr
    have : (a : F) * r ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := by
      rw [h𝔟D]
      exact FractionalIdeal.mem_singleton_mul.mpr ⟨r, hr, rfl⟩
    obtain ⟨b, hb, hbr⟩ := (FractionalIdeal.mem_coeIdeal (S := (𝓞 F)⁰)).mp this
    exact ⟨b, hb, hbr⟩

  set I : Ideal (𝓞 F) := Ideal.span {a} with hI
  have hmk : Function.Surjective (Ideal.Quotient.mk I) := Ideal.Quotient.mk_surjective
  set σ : 𝓞 F ⧸ I → 𝓞 F := Function.surjInv hmk with hσ
  have hσ_mk : ∀ q, Ideal.Quotient.mk I (σ q) = q := Function.surjInv_eq hmk
  set Q : Set (𝓞 F ⧸ I) := ((𝔟.map (Ideal.Quotient.mk I) : Ideal (𝓞 F ⧸ I)) : Set (𝓞 F ⧸ I))
    with hQ
  have hI0 : I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact ha0
  have : Finite (𝓞 F ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hI0
  have hQfin : Q.Finite := Set.toFinite Q

  have hσD : ∀ q ∈ Q, (σ q : F) * (a : F)⁻¹ ∈ D := by
    intro q hq
    obtain ⟨b, hb, hbq⟩ := (Ideal.mem_map_iff_of_surjective _ hmk).mp hq
    have hqb : Ideal.Quotient.mk I (σ q) = Ideal.Quotient.mk I b := by rw [hσ_mk, hbq]
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (Ideal.Quotient.eq.mp hqb)

    have hσq : (σ q : F) = (b : F) + (c : F) * (a : F) := by
      rw [← map_mul, ← map_add]
      exact congrArg (algebraMap (𝓞 F) F) (by rw [hc]; abel)
    rw [hσq, add_mul, mul_assoc, mul_inv_cancel₀ haF, mul_one]
    exact Submodule.add_mem (D : Submodule (𝓞 F) F) (h𝔟_div b hb) (hOD c)

  set P : 𝓞 F ⧸ I → Set (FiniteAdeleRing (𝓞 F) F) := fun q =>
    (fun z => algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ q : F) * (a : F)⁻¹) + z) ''
      integralFiniteAdeles (𝓞 F) F with hP

  have hcover : A = ⋃ q ∈ hQfin.toFinset, P q := by
    ext w
    simp only [Set.mem_iUnion, Set.Finite.mem_toFinset]
    constructor
    · intro hw
      obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw
      obtain ⟨b, hb, hbr⟩ := hD_mul r hr
      refine ⟨Ideal.Quotient.mk I b, Ideal.mem_map_of_mem _ hb, ?_⟩

      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp
        (Ideal.Quotient.eq.mp (hσ_mk (Ideal.Quotient.mk I b)))
      have hσb : (σ (Ideal.Quotient.mk I b) : F) * (a : F)⁻¹ = r + (c : F) := by
        have : (σ (Ideal.Quotient.mk I b) : F) = (b : F) + (c : F) * (a : F) := by
          rw [← map_mul, ← map_add]
          exact congrArg (algebraMap (𝓞 F) F) (by rw [hc]; abel)
        rw [this, hbr, add_mul, mul_inv_cancel_right₀ haF, mul_comm (a : F) r,
          mul_inv_cancel_right₀ haF]
      refine ⟨w - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ (Ideal.Quotient.mk I b) : F) * (a : F)⁻¹),
        ?_, by simp only; abel⟩
      rw [hσb, map_add, ← sub_sub]
      exact sub_mem_integralFiniteAdeles F hwr (algebraMap_coe_mem_integralFiniteAdeles c)
    · rintro ⟨q, hq, z, hz, rfl⟩
      refine (hmemA _).mpr ⟨(σ q : F) * (a : F)⁻¹, hσD q hq, ?_⟩
      simpa only [add_sub_cancel_left] using hz

  have hdisj : Set.PairwiseDisjoint (↑hQfin.toFinset : Set (𝓞 F ⧸ I)) P := by
    intro q₁ hq₁ q₂ hq₂ hne
    refine Set.disjoint_left.mpr fun x hx₁ hx₂ => hne ?_
    obtain ⟨z₁, hz₁, rfl⟩ := hx₁
    obtain ⟨z₂, hz₂, hx⟩ := hx₂

    have hdiff : algebraMap F (FiniteAdeleRing (𝓞 F) F)
        (((σ q₂ : F) - (σ q₁ : F)) * (a : F)⁻¹) ∈ integralFiniteAdeles (𝓞 F) F := by
      have heq : algebraMap F (FiniteAdeleRing (𝓞 F) F) (((σ q₂ : F) - (σ q₁ : F)) * (a : F)⁻¹)
          = z₁ - z₂ := by
        simp only at hx
        rw [sub_mul, map_sub]
        linear_combination hx
      rw [heq]
      exact fun v => sub_mem (hz₁ v) (hz₂ v)
    obtain ⟨e, he⟩ := exists_eq_coe_of_algebraMap_mem hdiff

    have hOe : σ q₂ - σ q₁ = e * a := by
      apply IsFractionRing.injective (𝓞 F) F
      rw [map_sub, map_mul]
      show (σ q₂ : F) - (σ q₁ : F) = (e : F) * (a : F)
      rw [← he, mul_assoc, inv_mul_cancel₀ haF, mul_one]
    have : Ideal.Quotient.mk I (σ q₂) = Ideal.Quotient.mk I (σ q₁) :=
      Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton'.mpr ⟨e, hOe.symm⟩)
    rw [hσ_mk, hσ_mk] at this
    exact this.symm

  have hPre : ∀ q, P q = (fun z => -algebraMap F (FiniteAdeleRing (𝓞 F) F) ((σ q : F) * (a : F)⁻¹) + z) ⁻¹'
      integralFiniteAdeles (𝓞 F) F := fun q => Set.image_add_left
  have hmeas : ∀ q ∈ hQfin.toFinset, MeasurableSet (P q) := fun q _ => by
    rw [hPre]
    exact ((isClosed_integralFiniteAdeles F).preimage (continuous_const.add continuous_id)).measurableSet
  have hνP : ∀ q, ν (P q) = ν (integralFiniteAdeles (𝓞 F) F) := fun q => by
    rw [hPre]
    exact measure_preimage_add ν _ _

  rw [hcover, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl fun q _ => hνP q,
    Finset.sum_const, nsmul_eq_mul]
  congr 1
  rw [← Set.ncard_eq_toFinset_card Q hQfin, hQ, ncard_map_eq_absNorm ha0 h𝔟]

theorem NumberField.AdelicFourier.measure_setOf_forall_addChar_finitePart_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : MeasureTheory.Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    ν {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      = (Ideal.absNorm (differentIdeal ℤ (𝓞 F)) : ENNReal) * ν (integralFiniteAdeles (𝓞 F) F) :=
  measure_annih_eq ν hψ hψ_inf

/-
## SET-AF111 insertion: NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one

The trace-dual vanishing set is compact and open.

`NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one` (117 pin
lines): the same set is compact *and* open — the topological form, and the input to the discreteness
argument the D–S route's Fourier step uses.
-/
theorem NumberField.AdelicFourier.continuous_apply_zero {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ}
    (hψ : IsGlobalAddChar F ψ) :
    Continuous fun x : FiniteAdeleRing (𝓞 F) F => ψ (0, x) :=
  hψ.continuous.comp (continuous_const.prodMk continuous_id)

theorem NumberField.AdelicFourier.isCompact_and_isOpen
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F |
          ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} := by
  have hann :=
    NumberField.AdelicFourier.forall_addChar_finitePart_mul_eq_one_iff_exists_mem_traceDual
      F hψ hψ_inf
  set A : Set (FiniteAdeleRing (𝓞 F) F) :=
    {w | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} with hA
  set D : FractionalIdeal (𝓞 F)⁰ F :=
    FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) with hD
  set ι := algebraMap F (FiniteAdeleRing (𝓞 F) F) with hι
  have hmemA : ∀ w, w ∈ A ↔ ∃ r : F, r ∈ D ∧ w - ι r ∈ integralFiniteAdeles (𝓞 F) F :=
    fun w => hann w

  have hclosed : IsClosed A := by
    have hcont : ∀ z : FiniteAdeleRing (𝓞 F) F, Continuous fun w => ψ (0, w * z) := fun z =>
      (continuous_apply_zero hψ).comp (continuous_id.mul continuous_const)
    have : A = ⋂ z ∈ integralFiniteAdeles (𝓞 F) F, {w | ψ (0, w * z) = 1} := by
      ext w; simp only [hA, Set.mem_ofPred_eq, Set.mem_iInter]
    rw [this]
    exact isClosed_biInter fun z _ => isClosed_eq (hcont z) continuous_const

  obtain ⟨a, ha0, ha⟩ := D.isFractional
  have ha0' : (algebraMap (𝓞 F) F a) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha0

  have hsub : A ⊆ (fun z => ι (algebraMap (𝓞 F) F a)⁻¹ * z) '' integralFiniteAdeles (𝓞 F) F := by
    intro w hw
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw

    obtain ⟨c, hc⟩ : ∃ c : 𝓞 F, algebraMap (𝓞 F) F c = a • r := ha r hr
    refine ⟨ι (algebraMap (𝓞 F) F a) * w, ?_, ?_⟩
    · have hsplit : ι (algebraMap (𝓞 F) F a) * w
          = ι (algebraMap (𝓞 F) F c) + ι (algebraMap (𝓞 F) F a) * (w - ι r) := by
        rw [hc, Algebra.smul_def, map_mul, mul_sub]; abel
      rw [hsplit]
      exact NumberField.AdelicBox.BoxKernel.add_mem_integralFiniteAdeles F
        (algebraMap_coe_mem_integralFiniteAdeles c)
        (mul_mem_integralFiniteAdeles (algebraMap_coe_mem_integralFiniteAdeles a) hwr)
    · show ι (algebraMap (𝓞 F) F a)⁻¹ * (ι (algebraMap (𝓞 F) F a) * w) = w
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha0', map_one, one_mul]
  have hcompact : IsCompact A :=
    ((isCompact_integralFiniteAdeles F).image (continuous_const.mul continuous_id)).of_isClosed_subset
      hclosed hsub

  have hopen : IsOpen A := by
    refine isOpen_iff_forall_mem_open.mpr fun w hw => ?_
    obtain ⟨r, hr, hwr⟩ := (hmemA w).mp hw
    refine ⟨(fun z => ι r + z) '' integralFiniteAdeles (𝓞 F) F, ?_, ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact (hmemA _).mpr ⟨r, hr, by rwa [add_sub_cancel_left]⟩
    · exact isOpenMap_add_left (ι r) _ (isOpen_integralFiniteAdeles F)
    · exact ⟨w - ι r, hwr, add_sub_cancel (ι r) w⟩
  exact ⟨hcompact, hopen⟩

theorem NumberField.AdelicFourier.isCompact_and_isOpen_setOf_forall_addChar_finitePart_mul_eq_one
    (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ)
    (hψ_inf : ∀ x : InfiniteAdeleRing F,
        ψ (x, 0) = (Real.fourierChar (Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (InfiniteAdeleRing.ringEquiv_mixedSpace F x)) : ℂ)) :
    IsCompact {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1}
      ∧ IsOpen {w : FiniteAdeleRing (𝓞 F) F | ∀ z ∈ integralFiniteAdeles (𝓞 F) F, ψ (0, w * z) = 1} :=
  isCompact_and_isOpen hψ hψ_inf

