/-
  Consumer specification for Layer 0 of `PORTING-FFG.md`.

  WHAT THIS FILE IS
  -----------------
  A written-down *use* of Layer 0a: the statements we want the port to make
  possible, expressed in Lean so that each one is either bound or not. It is a
  deliverable measure, not a proof obligation.

  It is deliberately **not part of any library**. `lake build` does not see it
  (nothing globs `spec/`), so it cannot break the verified port's green build.
  Run it by hand:

      cd lean
      lake env lean spec/ModularCurveConsumer.lean 2>&1 | grep -c error

  It **compiles today** — the error count, which is the metric, is 0 — but it is
  deliberately kept out of every library, so it can never break a verified build.
  The one remaining `sorry` is the deferred capstone theorem, which is by design.

  HOW TO READ IT
  --------------
  Every block is labelled:

    [0a]  bound by Layer 0a.  ZONE A: reached 0 errors.
    [0b]  bound by Layer 0b.  ZONE B: bound.
    [--]  not delivered by the Definitions layer; bound later.  ZONE C: bound
          (the `jq` coefficients by the topic module, `TS` by Layer 0b).

  When Zone A reached 0 errors, Layer 0a was done by this measure. Zones B and C
  were then allowed to go green only by explicit decisions — Zone B in Layer 0b,
  `TS` and the two coefficients later — never by scope creep.

  WHY ZONE C IS IN HERE
  ---------------------
  The justification for Layer 0a is that computable `jq` / `qExpand` / `qTwist`
  serve base/004's `j`-invariant claims and math/010's q-expansion statements.
  Zone C writes those claims down, and thereby recorded the finding that Layer 0a
  does *not* deliver the low coefficients of `jq` by itself. They were expected to
  come from the modular-form q-expansion cluster inside the 44-node subtree that
  §7.1 of the blueprint designates an input; `JqCoefficients.lean` reaches them
  without it, from `etaProd` plus mathlib's pentagonal theorem. The zone is kept
  as the record of that finding.
-/

-- The Layer 0 modules. They exist now, so these are live imports and the
-- placeholder mathlib imports they replaced are gone. The checks below are
-- bound by the definitions/lemmas those modules provide.
import FLTForHuman.ModularCurve.Defs.Laurent
import FLTForHuman.ModularCurve.Defs.Twist
import FLTForHuman.ModularCurve.Defs.Jq
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Target
import FLTForHuman.ModularCurve.Defs.Polynomial
import FLTForHuman.ModularCurve.Defs.Fields
import FLTForHuman.ModularCurve.Defs.PhiGen
import FLTForHuman.ModularCurve.Defs.TS
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Collapse
-- The topic module: the low coefficients of `jq`, via mathlib's pentagonal route.
import FLTForHuman.ModularCurve.JqCoefficients
-- The conditional capstone: the spine, with FLT's significant statements as `Inputs`.
import FLTForHuman.ModularCurve.FunctionFieldGeneration.Spine
-- The R1 analytic model of `jq` (topic 6): `jq` sums to `E₄³/Δ` on `ℍ`.
import FLTForHuman.ModularForms.JqAnalyticModel
-- T7: R1's Hauptmodul form, and the `RealL`/Cauchy-product interface for T8.
import FLTForHuman.ModularForms.Hauptmodul

set_option autoImplicit false

-- `open ModularCurve` now binds the Layer 0a namespace.
open ModularCurve

open HahnSeries IntermediateField PowerSeries

/-! ## Zone A — [0a] the objects exist with the expected shapes

Expected signatures below are transcribed from
`anthropics/fermats-last-theorem@aa2d8b3`, `Definitions/Def_ModularCurve_*.lean`.
Matching them is the mechanical part of the port. -/

-- Laurent.lean
#check qExpand      -- (R) {N : ℕ} [NeZero N] : LaurentSeries R →+* LaurentSeries R
#check qExpandₐ     -- {N : ℕ} [NeZero N] : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ
#check coeffMap     -- {R S} [CommRing R] [CommRing S] (f : R →+* S) : LaurentSeries R →+* LaurentSeries S
#check coeffEmb     -- {L} [Field L] [Algebra ℚ L] : LaurentSeries ℚ →+* LaurentSeries L

-- Twist.lean
#check qTwistFun    -- {R} [CommRing R] (u : Rˣ) (f : LaurentSeries R) : LaurentSeries R
#check qTwist       -- {R} [CommRing R] (u : Rˣ) : LaurentSeries R →+* LaurentSeries R

-- Jq.lean
#check eisenstein4        -- : PowerSeries ℤ
#check etaProd            -- : PowerSeries ℤ
#check jNum               -- : PowerSeries ℤ
#check jq                 -- : LaurentSeries ℚ
#check jqN                -- (N : ℕ) [NeZero N] : LaurentSeries ℚ
#check dedekindPsi        -- (N : ℕ) : ℕ
#check evalAtJ            -- : Polynomial ℤ →+* LaurentSeries ℚ

-- Target.lean — the target statement is a `def`, and it mentions only Zone A
-- objects (`jq`, `qExpand`, `IntermediateField.adjoin`), so it belongs here.
#check FunctionFieldGeneration   -- (M : ℕ) [NeZero M] : Prop

/-! ## Zone A — [0a] the facts Zone A makes available -/

-- The pole of `j`: `jq = q⁻¹ + ⋯`.  These are Def-layer lemmas, so they must
-- be bound by Layer 0a. Each is stated and now discharged by the corresponding
-- library lemma.
example : jq.coeff (-1 : ℤ) = 1 := coeff_jq_neg_one
example {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := coeff_jq_of_lt hk
example (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := coeff_jq_pow_self n

-- THE WIRE TEST (PORTING-FFG.md §6).  This statement composes `qExpand`
-- (Laurent.lean) with `jq` (Jq.lean) across a module boundary, and uses the
-- coefficient formula from Laurent.lean.  It is the check that the definitions
-- are *connected*, not merely green — the first port's `Universal.lean` sat in
-- no import chain and nothing failed until a round-12 attempt to use it.
--
-- Route: `-(N : ℤ)` is written as `(N : ℤ) * (-1)` so
-- `qExpand_coeff_mul` fires, and the goal closes with `jq.coeff (-1) = 1`
-- (Zone A, above).
example (N : ℕ) [NeZero N] : (qExpand ℚ N jq).coeff (-(N : ℤ)) = 1 := by
  rw [show (-(N : ℤ)) = (N : ℤ) * (-1) by ring, qExpand_coeff_mul, coeff_jq_neg_one]

-- `qTwist u` rescales coefficients by `u ^ k`; `qTwist` after `qExpand` is the
-- substitution `q ⟼ u q^N`.  Both are Def-layer lemmas.
example {L : Type*} [Field L] [Algebra ℚ L] (u : Lˣ) (k : ℤ) :
    (qTwist u (coeffEmb (L := L) jq)).coeff k = (u ^ k : Lˣ) * jq.coeff k := by
  simp [qTwist_coeff, coeffEmb_coeff]
example {L : Type*} [Field L] [Algebra ℚ L] (u : Lˣ) (N : ℕ) [NeZero N] :
    qTwist u (qExpand L N (coeffEmb (L := L) jq))
      = qExpand L N (qTwist (u ^ (N : ℤ)) (coeffEmb (L := L) jq)) := by
  -- This is FLT's `qTwist_qExpand` at `f = coeffEmb jq`. As written in the
  -- first draft of this file the statement was ill-typed and false (it applied
  -- `qExpand ℚ N` to a `LaurentSeries L` and dropped the `u ^ N` twist on the
  -- right); see the friction list at the end of this file.
  exact qTwist_qExpand u N (coeffEmb (L := L) jq)

-- The target statement is *expressible* from Zone A alone, and its degenerate
-- case is *provable* from Zone A alone.
example (N : ℕ) [NeZero N] : FunctionFieldGeneration N := by sorry  -- the capstone, unproved
#check functionFieldGeneration_one   -- FunctionFieldGeneration 1, proved in the Def layer

/-! ## Zone B — [0b] the fields and the polynomial datum

Bound by Layer 0b, plus the *conditional* capstone from `Spine.lean` (a topic
module). Nothing here is needed to state the target (`FunctionFieldGeneration`
does not mention `modularFunctionField`), which is why Zone A could ship without
it. The conditional capstone is the collapse's companion and is **proved**; only
the unconditional Zone A example remains a `sorry`. -/

#check ModularPolynomialData       -- (N : ℕ) [NeZero N] : Type
#check modularFunctionField      -- (N : ℕ) [NeZero N] : IntermediateField ℚ (LaurentSeries ℚ)
#check modularFunctionFieldFull  -- (N : ℕ) : IntermediateField ℚ (LaurentSeries ℚ)
#check jq_mem                    -- jq ∈ modularFunctionField N
#check jqN_mem                   -- qExpand ℚ N jq ∈ modularFunctionField N
#check divisorExpansions         -- (N : ℕ) : Set (LaurentSeries ℚ)

-- Note: `modularFunctionFieldFull` and `divisorExpansions` carry no `[NeZero N]`,
-- because Lean omits the section variable when the body does not use it. The
-- checks still bind; this only corrects the expected signature in the comment.

-- The collapse, which is Layer 0b's one theorem (`FLTForHuman/ModularCurve/FunctionFieldGeneration/Collapse.lean`).
example (N : ℕ) [NeZero N] :
    FunctionFieldGeneration N ↔ modularFunctionFieldFull N = modularFunctionField N :=
  functionFieldGeneration_iff_full_eq N

-- The *conditional* capstone (`FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean`), the
-- collapse's companion: it proves `FunctionFieldGeneration` outright from FLT's
-- significant remaining statements bundled as `Inputs`, so unlike the Zone A
-- example below it carries no `sorry`. The Zone A example is the *unconditional*
-- theorem, which stays deferred.
example (h : Inputs) (N : ℕ) [NeZero N] : FunctionFieldGeneration N :=
  functionFieldGeneration_of h N

/-! ## Zone C — the claims the Definitions layer does not deliver

Written down so the gap is visible.

`[0b]` The `TS` block below is now bound: `TS` was decided in for Layer 0b, and
`Defs/TS.lean` provides it. `[topic]` The two `jq.coeff` claims of base/004 — the
item this zone was named for — are now bound too, by
`FLTForHuman/ModularCurve/JqCoefficients.lean`. Layer 0 itself does not deliver
them; the topic module reaches them from the Definitions layer *plus* mathlib's
pentagonal number theorem, a deliberate divergence from FLT's modular-form route.
-/

-- base/004: `j(q) = q⁻¹ + 744 + 196884 q + ⋯`. The pole (`q⁻¹`) is in the Def
-- layer (Zone A above); the *regular* coefficients were the first item this zone
-- held open.
--
-- `Def_ModularCurve_X0.lean` defines `eisenstein4` by an explicit coefficient
-- formula but `etaProd` as a `∏'` (a topological product), so `jNum` is not an
-- evaluable expression: `#eval`/`decide` cannot reach these numbers. FLT proves
-- them in the modular-form q-expansion cluster — `Thm_ModularCurve_hasSum_jq_qParam`,
-- `qExpansion_*`, `hasSum_qParam_*` — inside the 44-node subtree that
-- PORTING-FFG.md §7.1 designates an input; the topic module avoids that subtree by
-- rewriting `etaProd` to mathlib's `pentagonalSeries` and computing the low
-- coefficients. These two examples are now discharged by real proofs.
example : jq.coeff 0 = 744 := coeff_jq_zero
example : jq.coeff 1 = 196884 := coeff_jq_one

-- math/010's `TS K e u`, the series of math/010 §1, is introduced in the
-- *solution* file, not in `Definitions/`. It was held out of Layer 0a and
-- decided in by Layer 0b; `Defs/TS.lean` now provides it, and the decision is
-- recorded in `logs/ffg-port.md` §4. This `[0b]` item is therefore bound, and
-- the identity below is the definition itself.
#check TS   -- (K) [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) : LaurentSeries K
example {K : Type*} [Field K] [Algebra ℚ K] (e : ℕ) [NeZero e] (u : Kˣ) :
    TS K e u = qExpand K e (qTwist u (coeffEmb (L := K) jq)) := rfl

/-! ## Zone D — [T6] the R1 analytic model of `jq`

`FLTForHuman/ModularForms/JqAnalyticModel.lean` binds `hasSum_jq_qParam`: for
every `τ : ℍ`, the formal Laurent series `jq` sums to `E₄(τ)³ / Δ(τ)`. That is
the realization hypothesis R1's Hauptmodul form (T7) will consume, and the only
bridge from the port's `PowerSeries`-built `jq` to mathlib's analytic `E₄` and
`Δ`; `E4_cube_div_discriminant_smul` is the model's `SL₂(ℤ)`-invariance.

The **wire test** below is a genuine cross-module composition: `hasSum_jq_qParam`
(the model, topic 6) composed with `coeff_jq_neg_one` (`Defs/Jq.lean`) and
`coeff_jq_zero`/`coeff_jq_one` (`JqCoefficients.lean`, the `jq`-coefficients
topic). Together they say the realized sum is the classical
`j(q) = q⁻¹ + 744 + 196884 q + ⋯`: the model supplies the `HasSum`, the
coefficient modules supply the three leading coefficients. Extracting the
coefficients *from* the `HasSum` alone is not attempted (a `HasSum` does not
expose its terms), so the composition is stated as the `HasSum` plus the
coefficient values — the form named in the work order.
-/

-- The model at any point (the pin's `hasSum_jq_qParam`, verbatim).
example (τ : UpperHalfPlane) :
    HasSum (fun m : ℤ => ((jq.coeff m : ℚ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) :=
  hasSum_jq_qParam τ

-- The leading coefficients the model realizes, from the two `jq` modules.
example : (jq.coeff (-1), jq.coeff 0, jq.coeff 1) = (1, 744, 196884) := by
  rw [coeff_jq_neg_one, coeff_jq_zero, coeff_jq_one]

-- The model's `SL₂(ℤ)`-invariance (the second public statement).
example (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (τ : UpperHalfPlane) :
    ModularForm.E₄ (γ • τ) ^ 3 / ModularForm.discriminant (γ • τ)
      = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ :=
  E4_cube_div_discriminant_smul γ τ

/-! ## Zone E — [T7] R1 completed: the Hauptmodul form

`FLTForHuman/ModularForms/Hauptmodul.lean` proves the headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant`: a Laurent series realized by an
`SL₂(ℤ)`-invariant function on `ℍ` lies in `ℚ[jq]`. Its proof composes T5's
kernel with this module's pole killing and T6's realization; its T8 interface
(`RealL` + closure, `hasSum_qParam_mul{,_laurent}`) is exported public.

The **wire test** below is the whole hypothesis chain across three modules: the
headline (T7) applied to `f = jq` and `F = E₄³/Δ`, with `hF` from T6's
`hasSum_jq_qParam` and `hinv` from T6's `E4_cube_div_discriminant_smul`. The
conclusion `jq ∈ ℚ[jq]` is trivial mathematically, so the test is exactly that
the *interface* holds: T7's statement accepts T6's two theorems.
-/

example : jq ∈ Algebra.adjoin ℚ {jq} :=
  mem_adjoin_jq_of_hasSum_of_slash_invariant jq
    (fun τ => ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ)
    (fun τ => hasSum_jq_qParam τ)
    (fun γ τ => E4_cube_div_discriminant_smul γ τ)

/-! ## The measure

    cd lean
    lake env lean spec/ModularCurveConsumer.lean 2>&1 | grep -c error

Zone A errors: the count of Zone A items still unbound. It must reach 0.
Zone B and Zone C errors are expected to remain — if they drop without a
decision to port the theorem, the scope has crept.

The error count is the number of unbound names. Since the topic module landed it
is **0**: Zones A, B and C are all bound. What remains unproved is exactly one
`sorry`, the Zone A capstone — the deferred theorem, which is the design. (Zone C
was originally expected to stay red; the topic showed it was reachable from the
Definitions layer plus mathlib, and the scope decision to take it is recorded in
`topics/functionFieldGeneration/TOPIC-jq-coefficients.md`.)

**Layer 0a result (2026-09-21).** Zone A is at **0 errors**; the file reports
**10 errors**, all of them Zone B (8: the six `#check`s plus the two unbound
names in the collapse example) and Zone C (2: the two `TS` occurrences). The one
remaining Zone A `sorry` is the capstone example at the top, which is the
theorem and is not provable from 0a — it is there so the target *statement* is
checked. All the other Zone A examples are discharged by real proofs, including
both cross-module compositions (the `qExpand`/`jq` wire test and
`qTwist_qExpand`), so the definitions are connected and not merely green.

**Layer 0b result (2026-09-21).** The file reports **0 errors** — Zone A, Zone B
and the `TS` half of Zone C are all bound. The three remaining `sorry`s are
exactly the deliberate ones: the Zone A capstone (the deferred theorem) and the
two `jq.coeff` claims in Zone C (`744`, `196884`), which belong to the modular-form
cluster inside the deferred Φ_p subtree and are expected to stay red. The Zone B
collapse is now discharged by `functionFieldGeneration_iff_full_eq`, Layer 0's
only theorem.

**Topic result (2026-09-21).** `FLTForHuman/ModularCurve/JqCoefficients.lean`
discharges the two Zone C `jq.coeff` examples (`coeff_jq_zero`, `coeff_jq_one`),
so the only remaining `sorry` in this file is the Zone A capstone. The topic did
not port any of the modular-form cluster: `etaProd` is identified with mathlib's
`pentagonalSeries` by `tprod_one_sub_X_pow`, and the rest is a low-order
`PowerSeries` coefficient computation.

**Conditional-capstone result (2026-09-21).**
`FLTForHuman/ModularCurve/FunctionFieldGeneration/Spine.lean` adds a *proved* Zone B item,
`functionFieldGeneration_of (h : Inputs)`, carrying no `sorry`. It is the
`PORTING-FFG.md` §7.4 artifact: a strong induction (`hall_all`, the helper block
above it is glue) with FLT's significant remaining statements bundled as the
structure `Inputs`, whose fields are the exact debt a full port would still
owe. It is *not* the deferred theorem: the Zone A example stays the
unconditional statement and stays `sorry`. Zone B's example is discharged by
applying `functionFieldGeneration_of` to an arbitrary `Inputs`, so the count of
`sorry`s in this file is unchanged at 1.

**Interface-tier result (2026-09-21).** Nine public interface lemmas were added
to `Defs/Laurent.lean` and `Defs/Jq.lean`, and two of the `Inputs` fields
(`dedekindPsi_mul_of_coprime`, `dedekindPsi_prime_pow`) were discharged into
`Defs/Jq.lean`, so `Inputs` is down to **8** fields. Nothing in this file
changed: still **0 errors** and one `sorry`.

**Generic-kernel result (2026-09-21).** The third `cites = 0` field,
`relfinrank_modularFunctionField`, was discharged into `Defs/Fields.lean` beside
`adjoin_jq_le`, so `Inputs` is down to **7** fields; the generic engine behind the
segment (`FLTForHuman/FieldTheory/CommonRoot.lean`) is mathlib-only and touches
nothing here. Its instantiations live in that module, so this file is again
unchanged: **0 errors**, one `sorry`.

**R1-model result (2026-09-22).** Zone D is added and bound:
`FLTForHuman/ModularForms/JqAnalyticModel.lean` supplies `hasSum_jq_qParam`
(the realization R1's Hauptmodul form consumes) and
`E4_cube_div_discriminant_smul`. The zone's wire test composes topic 6's model
with `Defs/Jq.lean`'s `coeff_jq_neg_one` and `JqCoefficients.lean`'s
`coeff_jq_zero`/`coeff_jq_one`, exhibiting the classical
`j(q) = q⁻¹ + 744 + 196884 q + ⋯`. This file is still **0 errors**, one `sorry`.

**Hauptmodul result (2026-09-22).** Zone E is added and bound:
`FLTForHuman/ModularForms/Hauptmodul.lean` proves the headline
`mem_adjoin_jq_of_hasSum_of_slash_invariant`, completing R1. The zone's wire test
runs the headline on `f = jq`, `F = E₄³/Δ` with `hF` from T6's `hasSum_jq_qParam`
and `hinv` from T6's `E4_cube_div_discriminant_smul` — a cross-module composition
over three modules whose conclusion (`jq ∈ ℚ[jq]`) is trivial but whose
hypotheses are the whole interface. The module also exports the `RealL` closure
and `hasSum_qParam_mul{,_laurent}` that T8 imports. Still **0 errors**, one
`sorry`.

## Friction list (mathlib `v4.34.0` against FLT's `v4.33.0`)

Recorded while porting, as the playbook asks. The mathematics is unchanged in
every entry.

1. **`HahnSeries.embDomain_notin_range` was renamed** to
   `HahnSeries.embDomain_of_notMem_range` (same signature, so a drop-in
   replacement). Hit in `Defs/Laurent.lean` (`qExpand_coeff_of_not_dvd`) and
   `Defs/Jq.lean` (`ofPowerSeries_coeff_of_neg`); FLT's pinned mathlib still has
   the old name.
2. **`if_pos` was deprecated** in favour of `ite_eq_left` (already on the first
   port's drift list). Hit in `Defs/Jq.lean` (`dedekindPsi_one`).
3. **Style linter `linter.style.haveILetI`**: FLT's `haveI := hne` in
   `functionFieldGeneration_one` is flagged — the goal is a proposition, so
   `have` is preferred, and the `NeZero d` introduced by `intro` is already a
   local instance in context. Dropping the line keeps the proof and clears the
   warning. `FunctionFieldGeneration/Target.lean`.
4. **Two Zone A examples in *this* file were wrong as first drafted** (our spec
   bug, not FLT's; FLT's own `qTwist_qExpand` is correct and was transcribed
   verbatim):
   - the twist-coefficient example omitted `[Algebra ℚ L]`, which `coeffEmb`
     requires, so it could not elaborate;
   - the `qTwist_qExpand` example applied `qExpand ℚ N` to a
     `LaurentSeries L` (a universe/type mismatch) and, on the right, dropped the
     `u ^ (N : ℤ)` twist, which makes the statement false. It now reads exactly
     as FLT's theorem at `f = coeffEmb jq`.
5. **No drift found** in the remaining API the port leans on:
   `HahnSeries.embDomainRingHom`, `HahnSeries.map_mul`, `HahnSeries.map_*`,
   `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow`,
   `PowerSeries.mul_invOfUnit`, `Finset.filter_singleton`,
   `Units.mul_right_eq_zero`, `Subfield.closure_induction`,
   `IntermediateField.subset_adjoin`, `map_ratCast`. The `open Finset renaming
   antidiagonal → pwoAntidiagonal` inside `qTwist` also still works.
6. **The predicted failure did not occur.** The earlier work plan and the
   playbook §3.5 expected the monomorphic-helper gap (`rw [map_mul]` not firing
   on a `def`-as-ring-hom) to be the most repeated obstacle, for `coeffMap`,
   `coeffEmb`, `qExpand` and `qTwist`. It never came up: FLT proves these
   lemmas coefficientwise (`ext k; simp`), and its own `[simp]` coefficient
   lemmas (`qExpand_coeff_mul`, `coeffMap_coeff`, `qTwist_coeff`, …) are the
   named bridges, so no additional `*_mul` restatement was needed. This is the
   one respect in which this layer was cheaper than the playbook's model.

### Layer 0b additions

7. **`if_pos` / `if_neg` → `ite_eq_left` / `ite_eq_right`** again, this time in
   `Defs/PhiGen.lean` (`cosetA_zero`, `cosetB_zero`, `cosetA_succ`,
   `cosetB_succ`). Same family as entry 2; FLT's pinned mathlib has the old
   names.
8. **`linter.style.haveILetI` again.** Two `haveI`s in `Defs/Fields.lean` were
   unnecessary and cleared the warning by deletion:
   `full_degeneracy_le`'s `haveI := hne` (the `NeZero d` from `rintro` is
   already a local instance) and `full_degeneracy_map_le`'s explicit
   `haveI : NeZero (ℓ * d)`, which typeclass search derives from
   `[NeZero ℓ]` and `[NeZero d]`. The same-line `haveI` inside the `def`
   `cosetSubst` is *not* flagged (the linter only fires on `Prop` goals) and was
   kept.
9. **Unused section variables are auto-omitted, so two expected signatures in
   this file were wrong.** `modularFunctionFieldFull` and `divisorExpansions`
   carry no `[NeZero N]` — Lean drops the variable because neither body uses it
   — and their `#check` comments have been corrected. FLT's signatures are the
   same; this was a spec-comment bug, like entry 4.
10. **`TS` is at `ModularCurve.TS` in the port, `ModularCurve.W1.TS` in FLT.**
    FLT defines it inside a `namespace W1` local to each solution file that needs
    it and never exports it to `ModularCurve`; the port promotes it to a
    `Definitions`-layer module, which is what this file checks. A recorded
    deliberate divergence in *name*, not in mathematics: all ten statements are
    FLT's verbatim.
11. **The three shape risks named for 0b did not bite.** `swapInner`/`swapBivar`
    (predicted to trigger the rewrite-search gap) proved verbatim; the
    `Subalgebra` vs `IntermediateField` split needed no coercion work;
    `phiProd` and `toAdjoin_monic` worked verbatim. `TS_injective` — the one
    proof with content, reading the pair `(e, u)` off two coefficients — also
    worked as transcribed.
12. **Statement correspondence is now mechanical.** `spec/check_flt_statements.py`
    extracts each port declaration's statement and diffs it against the pinned
    source: **146 of 146 identical** (68 from 0a, 69 from 0b, 9 interface
    lemmas), 0 mismatched, 0 missing. The check is non-vacuous (a mutated
    statement is caught).
13. **Topic 3 — the interface tier, and two source-selection wrinkles.** The
    `Theorems/` wrappers qualify every occurrence with `ModularCurve.`, so the
    checker now strips that namespace prefix from both sides before comparing;
    and `coeffEmb_qExpand` exists twice in the pin (the public wrapper with
    explicit `(L : Type*)`, the `solution` file's `W1` copy with implicit `{K}`),
    so the wrappers precede the solution file in `SOURCES`. `dif_neg` →
    `dite_eq_right` appeared once already (0b entry 7's family). The one real
    dependency addition is `Mathlib.NumberTheory.ArithmeticFunction.Misc`, for
    `dedekindPsi_mul_of_coprime`; it was already in the build closure, so the
    planned job count did not move.
14. **Topic 6 — the audit's one wrong prediction, and two small drifts.**
    (a) The work order expected `ModularForm.discriminant_cuspFunction_eqOn` to
    replace the pin's 199-line eta-product Taylor series. It does not: it gives
    the *value* of `cuspFunction 1 Δ` on the disc, while the `q`-expansion needs
    the *Taylor coefficients* of `∏' (1-qⁿ)²⁴`, which no mathlib lemma computes.
    The pin's truncated-polynomial/locally-uniform-convergence argument was
    ported (with `if_neg` → `ite_eq_right`; entry 2's family). The 4-line value
    lemma *is* replaced by `ModularForm.discriminant_eq_q_prod`.
    (b) `open PowerSeries` makes `derivative` ambiguous with
    `Polynomial.derivative` in the truncated-polynomial lemmas; the port does
    not open `PowerSeries` and qualifies instead. (c) The pin's
    `ModularFormClass.qExpansion_coeff_unique` call is already on the *bundled*
    `CuspForm.discriminant`, which is exactly what avoids T5's `DFunLike.coe`
    blow-up — no restatement was needed here.
15. **Topic 7 — the glue topic, and the checker's raw-text requirement.**
    (a) No blow-up: nothing is instantiated at a bare function type, and the
    module typechecked on the first bounded `lake env lean` (6 s build). The one
    drift was `if_pos` → `ite_eq_left` in `hasSum_single_mul_coe_iff` (entry 2's
    family; the same file also hits `LaurentSeries.coeff_coe_powerSeries`).
    (b) **A real spec constraint, not drift.** The exported statements had to be
    written in the *wrappers'* raw form, not the port's convenient one: the
    wrappers write `UpperHalfPlane → ℂ` and `Function.Periodic.qParam`, while the
    `S_` files write `ℍ` and the local `𝕢`. The two are definitionally equal but
    the checker's `norm` is a text diff, so `RealL` (whose comparable source is
    the `S_` file) keeps `ℍ`/`𝕢` while `hasSum_qParam_mul{,_laurent}` and the
    headline (whose comparable sources are the wrappers) use the long forms.
    **The rule for later topics: match the wrapper's spelling, not the S file's,
    for any public declaration the checker verifies.**

The `sorry`s are not errors and do not count: their job is to keep the
*statements* checkable while the proofs are out of scope.
-/
