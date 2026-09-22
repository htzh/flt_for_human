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
-- T8: the cone's (c), `mem_adjoin_jq_of_phiGenDescends`, and the Hecke layer.
import FLTForHuman.ModularForms.PhiGenDescends
-- T9: the cone's (b) integrality, `PhiGenDescends.intCoeffs` and
-- `aeval_jq_intCoeffs_descent`, in the `ModularCurve` algebraic layer.
import FLTForHuman.ModularCurve.PhiGenIntegrality
-- T10: the cone's (b) pole bounds, `phiProd_conj_coeff_{zero_lead,eq_zero_of_le}`,
-- plus the shared `TPoleOrderLE` prelude now public in `Defs/PhiGen.lean`.
import FLTForHuman.ModularCurve.PhiGenPoleBounds
-- T11: the construction — (a)'s descent, the 328 block, and (d)'s assembly.
import FLTForHuman.ModularCurve.PhiGenDescent
import FLTForHuman.ModularCurve.ModularPolynomialAssembly
-- T12: the properties — coefficient positivity, the 895 block, and existence.
import FLTForHuman.ModularCurve.JqCoeffPositivity
import FLTForHuman.ModularCurve.ModularPolynomialProperties
-- T13: the consequence — uniqueness, the degree, and the cone's headline.
import FLTForHuman.ModularCurve.ModularPolynomialUniqueness
import FLTForHuman.ModularCurve.PhiGenSplits
-- T14: the shared slot prelude — the upstream vocabulary and the downstream
-- at-slot roots API.
import FLTForHuman.ModularCurve.Defs.PhiAtSlot
import FLTForHuman.ModularCurve.PhiSlotRoots
-- The cyclotomic instances for the end-to-end wire tests of Zones I, J and K.
import Mathlib.NumberTheory.Cyclotomic.Basic

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

/-! ## Zone F — [T8] the cone's (c): the descended coefficients lie in `ℚ[jq]`

`FLTForHuman/ModularForms/PhiGenDescends.lean` proves
`PhiGen.mem_adjoin_jq_of_phiGenDescends`, the application R1 was isolated for: a
descended coefficient of the conjugate product lies in `ℚ[jq]`. Its proof
composes the whole sub-effort — this topic's two Hecke-translate q-expansions and
`cosetPoly_smul`, T7's `RealL` closure and headline, and T6's realization.

**The wire test is a binding, not a concrete instance.** The internal chain is
genuine (`hasSum_coeff_of_phiGenDescends` produces the realization, T7's headline
consumes it, the two Hecke lemmas feed the former), but its hypothesis
`hc : PhiGenDescends ℓ ζ c` is the cone's piece **(a)**, which is *not* ported, so
no concrete `hc` exists to instantiate. The zone therefore binds the exported
statement, the T8 interface T8's siblings use, and the correspondence; the node's
real consumer is the cone's (d) `exists_modularPolynomialData_coeff_eq`, which is
also not ported.
-/

#check @ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends
#check @cosetPoly_smul
#check @hasSum_qParam_heckeMatrix_smul
#check @hasSum_qParam_heckeDiagMatrix_smul
#check @ModularForm.heckeMatrix
#check @ModularForm.coe_heckeMatrix_smul

-- The statement in hypothesis form: the full signature, including the
-- `PhiGenDescends` descent hypothesis, elaborates against the port's `Defs/`.
example (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : (CyclotomicField ℓ ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField ℓ ℚ) ℓ)
    (c : ℕ → LaurentSeries ℚ) (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) (k : ℕ) :
    c k ∈ Algebra.adjoin ℚ {jq} :=
  ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ ζ hζ c hc k

/-! ## Zone G — [T9] the cone's (b) integrality: descended coefficients are integral

`FLTForHuman/ModularCurve/PhiGenIntegrality.lean` proves the first half of the
cone's piece (b): `PhiGenDescends.intCoeffs` says the descended family `c` has
integer `q`-expansion coefficients, and `aeval_jq_intCoeffs_descent` turns that
triangularity into "a rational `P` with `IntCoeffs (P(jq))` lies in `ℤ[X]`".
Route A (the deviation) shipped: `LaurentSeries 𝒪` + `coeffMap` + mathlib's
integral closure, replacing FLT's `CoeffsIntegral` closure machinery.

**The wire test is a binding plus a hypothesis-form instance.** As with Zone F,
`PhiGenDescends.intCoeffs`'s hypothesis `hc : PhiGenDescends ℓ ζ c` is the cone's
piece (a), which is not ported, so no concrete `hc` exists and none is invented.
Its real consumer is the cone's (d) `exists_modularPolynomialData_coeff_eq`, not
yet ported. `aeval_jq_intCoeffs_descent` *does* have a concrete instance
(`P = X`, `hP` the port's `intCoeffs_jq`); it is proved and named
`aeval_jq_intCoeffs_descent_X` inside the module, where the private
`intCoeffs_jq` is in scope. Zone G binds the exported statement and its
hypothesis form.
-/

#check @ModularCurve.PhiGen.PhiGenDescends.intCoeffs
#check @ModularCurve.PhiGen.aeval_jq_intCoeffs_descent

-- The statement in hypothesis form: the full `intCoeffs` signature, including
-- the `PhiGenDescends` descent hypothesis, elaborates against the port's `Defs/`.
example {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (c : ℕ → LaurentSeries ℚ) (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c)
    (hζ1 : ζ ^ ℓ = 1) (k : ℕ) : ModularCurve.PhiGen.IntCoeffs (c k) :=
  ModularCurve.PhiGen.PhiGenDescends.intCoeffs hc hζ1 k

-- The statement in hypothesis form for the descent.
example (P : Polynomial ℚ) (hP : ModularCurve.PhiGen.IntCoeffs (Polynomial.aeval jq P))
    (k : ℕ) : ∃ z : ℤ, P.coeff k = (z : ℚ) :=
  ModularCurve.PhiGen.aeval_jq_intCoeffs_descent P hP k

/-! ## Zone H — [T10] the cone's (b) pole bounds: the product's coefficients

`FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` proves the second half of (b).
`phiProd_conj_coeff_zero_lead` computes the leading coefficient of the constant
term of `phiProd ℓ (conj ℓ ζ)`: the pole is exactly `q ^ (-(ℓ * ℓ + ℓ))` with
residue `1`. `phiProd_conj_coeff_eq_zero_of_le` bounds every non-constant
coefficient to the same order. Their shared `TPoleOrderLE` prelude (the closure
`mono`/`zero`/`one`/`neg`/`add`/`mul`/`qTwist`/`qExpand`, the conjugate bounds and
the polynomial-coefficient bounds) is public in `Defs/PhiGen.lean`; FLT copies it
into six files and T11 imports it from there.

**The wire test is concrete, unlike T9's.** Both statements take only
`hζ : IsPrimitiveRoot (ζ : K) ℓ` over an arbitrary field, so they instantiate:
`K = ℂ`, `ℓ = 2`, `ζ = -1` (`IsPrimitiveRoot.neg_one`), carried out and named
inside the module (`wire_zero_lead`, `wire_eq_zero_of_le`). Zone H binds both
exported statements and their hypothesis forms.
-/

#check @ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead
#check @ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le

-- The statement in hypothesis form for the leading coefficient.
example {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ((ModularCurve.PhiGen.phiProd ℓ (ModularCurve.PhiGen.conj ℓ ζ)).coeff 0).coeff
      (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 :=
  ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead ℓ ζ hζ

-- The statement in hypothesis form for the non-constant bound.
example {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)]
    (ζ : Kˣ) (k : ℕ) (hk : k ≠ 0) (m : ℕ) (hm : ℓ * ℓ + ℓ ≤ m) :
    ((ModularCurve.PhiGen.phiProd ℓ (ModularCurve.PhiGen.conj ℓ ζ)).coeff k).coeff
      (-(m : ℤ)) = 0 :=
  ModularCurve.PhiGen.phiProd_conj_coeff_eq_zero_of_le ℓ ζ k hk m hm

/-! ## Zone I — [T11] the construction: descent, the 328 block, the datum

`FLTForHuman/ModularCurve/PhiGenDescent.lean` proves (a),
`PhiGen.exists_phiGenDescends`: the coefficients of the conjugate product descend
to `ℚ((q))`. `FLTForHuman/ModularCurve/PhiGenDescendsStructure.lean` proves the
328 block's shape exports (`c_top`, `c_eq_zero`, `poleOrderLE`,
`sum_mul_jqN_pow_eq_zero`, `evalAtJ_injective`), the last by the mathlib route
through the public `transcendental_jq`. `FLTForHuman/ModularCurve/ModularPolynomialAssembly.lean`
proves (d): `exists_modularPolynomialData_coeff_eq` assembles the datum and
`splits_of_coeff_evalAtJ_eq` turns it back into the product. Together with T9's
integrality and T8's membership they compose into the cone's construction.

**The wire test is end-to-end.** Unlike Zones F/G, (a) is now ported, so the whole
chain can be run on a concrete field: `K = CyclotomicField ℓ ℚ` with mathlib's
primitive root (the instances are set up as the pin's
`exists_phiIrreducible_evalSymm` does). The example below produces a descended
family `c`, verifies its integrality (T9), membership in `ℚ[jq]` (T8) and pole
bound (T11), and assembles `data` with `evalAtJ (data.Φ.coeff k) = c k` — (a) +
(b) + (c) + (d) in one instance. `evalAtJ_injective` is unconditional and also
bound.
-/

#check @ModularCurve.PhiGen.exists_phiGenDescends
#check @ModularCurve.PhiGen.PhiGenDescends.c_top
#check @ModularCurve.PhiGen.PhiGenDescends.c_eq_zero
#check @ModularCurve.PhiGen.PhiGenDescends.poleOrderLE
#check @ModularCurve.PhiGen.PhiGenDescends.sum_mul_jqN_pow_eq_zero
#check @ModularCurve.PhiGen.evalAtJ_injective
#check @ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq
#check @ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq

-- The 328 block in hypothesis form.
example {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c) :
    c (ℓ + 1) = 1 :=
  ModularCurve.PhiGen.PhiGenDescends.c_top hc

example {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c)
    (k : ℕ) : PoleOrderLE (c k) (ℓ + 1) :=
  ModularCurve.PhiGen.PhiGenDescends.poleOrderLE hc k

example : Function.Injective evalAtJ :=
  ModularCurve.PhiGen.evalAtJ_injective

-- The assembly in hypothesis form.
example {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)]
    {ζ : Kˣ} {c : ℕ → LaurentSeries ℚ} (hc : ModularCurve.PhiGen.PhiGenDescends ℓ ζ c)
    (hint : ∀ k, ModularCurve.PhiGen.IntCoeffs (c k))
    (hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq}) :
    ∃ data : ModularCurve.ModularPolynomialData ℓ,
      ∀ k, evalAtJ (data.Φ.coeff k) = c k :=
  ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem

-- The end-to-end wire test: (a) + (b) + (c) + (d) on `K = CyclotomicField ℓ ℚ`.
set_option linter.style.haveILetI false in
example (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ∃ c : ℕ → LaurentSeries ℚ, ∃ data : ModularCurve.ModularPolynomialData ℓ,
      (∀ k, evalAtJ (data.Φ.coeff k) = c k) ∧
      (∀ k, ModularCurve.PhiGen.IntCoeffs (c k)) ∧
      (∀ k, c k ∈ Algebra.adjoin ℚ {jq}) ∧
      (∀ k, PoleOrderLE (c k) (ℓ + 1)) := by
  haveI : NeZero ((ℓ : ℕ) : ℚ) := ⟨Nat.cast_ne_zero.mpr hℓ.out.ne_zero⟩
  haveI : IsCyclotomicExtension {ℓ} ℚ (CyclotomicField ℓ ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := ℓ) (K := ℚ)
  haveI : FiniteDimensional ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.finiteDimensional {ℓ} ℚ (CyclotomicField ℓ ℚ)
  haveI : IsGalois ℚ (CyclotomicField ℓ ℚ) :=
    IsCyclotomicExtension.isGalois (S := {ℓ}) (K := ℚ) (L := CyclotomicField ℓ ℚ)
  obtain ⟨z, hz⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot ℚ (CyclotomicField ℓ ℚ)
    (Set.mem_singleton ℓ) hℓ.out.ne_zero
  have hzu : IsUnit z := hz.isUnit hℓ.out.ne_zero
  have hζ : IsPrimitiveRoot ((hzu.unit : (CyclotomicField ℓ ℚ)ˣ) : CyclotomicField ℓ ℚ) ℓ := by
    rw [hzu.unit_spec]
    exact hz
  have hζ1 : hzu.unit ^ ℓ = 1 := by
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, hζ.pow_eq_one, Units.val_one]
  obtain ⟨c, hc⟩ := ModularCurve.PhiGen.exists_phiGenDescends ℓ hzu.unit hζ
  have hint : ∀ k, ModularCurve.PhiGen.IntCoeffs (c k) := fun k => hc.intCoeffs hζ1 k
  have hmem : ∀ k, c k ∈ Algebra.adjoin ℚ {jq} :=
    fun k => ModularCurve.PhiGen.mem_adjoin_jq_of_phiGenDescends ℓ hzu.unit hζ c hc k
  obtain ⟨data, hcoeff⟩ :=
    ModularCurve.PhiGen.exists_modularPolynomialData_coeff_eq hc hint hmem
  exact ⟨c, data, hcoeff, hint, hmem, fun k => hc.poleOrderLE k⟩

/-! ## Zone J — [T12] the properties: irreducibility, symmetry, existence

`FLTForHuman/ModularCurve/JqCoeffPositivity.lean` proves `one_le_coeff_jq` (every
regular coefficient of `j(q)` is at least `1`), with the audit's two mathlib
substitutions. `FLTForHuman/ModularCurve/ModularPolynomialIrreducible.lean` is the
895 block written once: `conj_injective`, `aeval_jq_ne_jqN`/
`jqN_not_mem_adjoin_jq`, `phiIrreducible_of_splits`,
`swapBivar_monic_of_coeff_bounds`, `transposeToAdjoin_monic_of_qExpansion`,
`evalSymm_of_irreducible`, `evalSymm_of_splits`, `evalAtJGen_injective`,
`swapBivar_eq_of_evalSymm` and the two minimal-polynomial facts.
`FLTForHuman/ModularCurve/ModularPolynomialProperties.lean` concludes:
`evalSymm_of_coeff_evalAtJ_eq` (T10's pole bounds feed the transpose degree count)
and `exists_phiIrreducible_evalSymm`.

**The wire test is unconditional — the first.** `exists_phiIrreducible_evalSymm`
needs no unported hypothesis, so it instantiates at `ℓ = 2`; `one_le_coeff_jq` is
unconditional at `n = 0`; and `aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq` become
unconditional once `one_le_coeff_jq` is supplied for their `hpos`.
-/

#check @ModularCurve.one_le_coeff_jq
#check @ModularCurve.PhiGen.phiIrreducible_of_splits
#check @ModularCurve.PhiGen.evalSymm_of_splits
#check @ModularCurve.ModularPolynomialData.transposeToAdjoin_monic_of_qExpansion
#check @ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq
#check @ModularCurve.exists_phiIrreducible_evalSymm
#check @ModularCurve.evalAtJGen_injective
#check @ModularCurve.swapBivar_monic_of_coeff_bounds
#check @ModularCurve.ModularPolynomialData.evalSymm_of_irreducible
#check @ModularCurve.swapBivar_eq_of_evalSymm
#check @ModularCurve.PhiGen.conj_injective
#check @ModularCurve.aeval_jqN_toAdjoin
#check @ModularCurve.ModularPolynomialData.minpoly_jqN_eq

-- The unconditional capstone: at `ℓ = 2` there is an irreducible symmetric datum.
example : ∃ data : ModularCurve.ModularPolynomialData 2,
    ModularCurve.PhiIrreducible data ∧ ModularCurve.EvalSymm data.Φ :=
  ModularCurve.exists_phiIrreducible_evalSymm (ℓ := 2) (hℓ := ⟨Nat.prime_two⟩)

-- `one_le_coeff_jq` at a concrete value, against `JqCoefficients`' `coeff_jq_zero`.
example : (1 : ℚ) ≤ ModularCurve.jq.coeff (0 : ℤ) := ModularCurve.one_le_coeff_jq 0

-- `j(q ^ ℓ)` is not a polynomial in `j(q)` — unconditional once `hpos` is supplied.
example (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (P : Polynomial ℚ) :
    Polynomial.aeval ModularCurve.jq P ≠ ModularCurve.jqN ℓ :=
  ModularCurve.PhiGen.aeval_jq_ne_jqN ℓ ModularCurve.one_le_coeff_jq P

example (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] :
    ModularCurve.jqN ℓ ∉ Algebra.adjoin ℚ {ModularCurve.jq} :=
  ModularCurve.PhiGen.jqN_not_mem_adjoin_jq ℓ ModularCurve.one_le_coeff_jq

/-! ## Zone K — [T13] the consequence and the cone's capstone

`FLTForHuman/ModularCurve/ModularPolynomialUniqueness.lean` proves
`finrank_adjoin_jqN_eq_of_prime` (the relative degree is `p + 1`) and
`ModularPolynomialData.eq_of_prime` (any two prime-level data are equal).
`FLTForHuman/ModularCurve/PhiGenSplits.lean` proves `PhiGen.splits_of_prime` and
the cone's headline `PhiGen.splits_prime_at_slot`.

**The wire is the cone, end to end.** `splits_prime_at_slot` is instantiated at a
concrete field and level datum — `K = CyclotomicField 2 ℚ`, `N = p = 2`, `e = 1`,
`u = 1` — for any primitive square root in that field, over an arbitrary
`ModularPolynomialData 2`. `eq_of_prime` and `finrank_adjoin_jqN_eq_of_prime` are
unconditional and are bound too.

The consumer's remaining `sorry` — the *unconditional*
`FunctionFieldGeneration N` — is the FFG `Inputs` gap, not this cone's: with
`splits_prime_at_slot` now a theorem, the seven `Inputs` fields of
`PORTING-FFG.md` §7.8 (T14–T19) can be discharged downstream.
-/

#check @ModularCurve.finrank_adjoin_jqN_eq_of_prime
#check @ModularCurve.ModularPolynomialData.eq_of_prime
#check @ModularCurve.PhiGen.splits_of_prime
#check @ModularCurve.PhiGen.splits_prime_at_slot

-- Uniqueness: two data at `p = 2` agree.
example (d d' : ModularCurve.ModularPolynomialData 2) : d = d' :=
  ModularCurve.ModularPolynomialData.eq_of_prime 2 (hp := ⟨Nat.prime_two⟩) d d'

-- The degree `[ℚ(j)(j(q ^ 2)) : ℚ(j)] = 2 + 1`.
example : Module.finrank (IntermediateField.adjoin ℚ ({ModularCurve.jq} : Set (LaurentSeries ℚ)))
    (IntermediateField.adjoin (IntermediateField.adjoin ℚ ({ModularCurve.jq} : Set (LaurentSeries ℚ)))
      ({ModularCurve.jqN 2} : Set (LaurentSeries ℚ))) = 3 :=
  ModularCurve.finrank_adjoin_jqN_eq_of_prime (ℓ := 2) (hℓ := ⟨Nat.prime_two⟩)

open scoped BigOperators

-- The capstone: the cone's headline at `K = CyclotomicField 2 ℚ`, `N = p = 2`,
-- `e = 1`, `u = 1`, for an arbitrary datum and primitive square root.
set_option linter.style.haveILetI false in
example (data : ModularCurve.ModularPolynomialData 2) (ζ : (CyclotomicField 2 ℚ)ˣ)
    (hζ : IsPrimitiveRoot (ζ : CyclotomicField 2 ℚ) 2) :
    data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries (CyclotomicField 2 ℚ)))
      (qExpand (CyclotomicField 2 ℚ) (2 * 1)
        (qTwist ((1 : (CyclotomicField 2 ℚ)ˣ) ^ 2)
          (coeffEmb (CyclotomicField 2 ℚ) ModularCurve.jq)))) =
      (Polynomial.X - Polynomial.C (qExpand (CyclotomicField 2 ℚ) (2 * (2 * 1))
        (qTwist ((1 : (CyclotomicField 2 ℚ)ˣ) ^ (2 * 2))
          (coeffEmb (CyclotomicField 2 ℚ) ModularCurve.jq)))) *
        ∏ b ∈ Finset.range 2,
          (Polynomial.X - Polynomial.C (qExpand (CyclotomicField 2 ℚ) 1
            (qTwist ((1 : (CyclotomicField 2 ℚ)ˣ) * ζ ^ (b * (2 / 2)))
              (coeffEmb (CyclotomicField 2 ℚ) ModularCurve.jq)))) :=
  ModularCurve.PhiGen.splits_prime_at_slot (K := CyclotomicField 2 ℚ) (N := 2) (ζ := ζ) (hζ := hζ)
    (p := 2) (hp := ⟨Nat.prime_two⟩) (hpN := dvd_rfl) (data := data) (e := 1) (u := 1)

/-! ## Zone L — [T14] the shared slot prelude

`FLTForHuman/ModularCurve/Defs/PhiAtSlot.lean` is the slot vocabulary written once:
the `conj`/`TS` bridges, the conjugate product's expansion and roots, and
`phiAtSeed` with its naturality/monicity/degree/vanishing lemmas.
`FLTForHuman/ModularCurve/Defs/Twist.lean` gains the twist equivalence
`qTwistEquiv` and `qTwist_iota_of_pow_eq_one`; `Defs/TS.lean` and `Defs/Jq.lean`
gain the remaining `TS`-dependent bridges; and
`FLTForHuman/ModularCurve/PhiSlotRoots.lean` is the one downstream module: the
at-slot roots API `roots_prime_at_slot*`/`isRoot_prime_at_slot_iff` read off
T13's `splits_prime_at_slot`.

**The chosen wire is `roots_phiProd_conj_nodup` at `p = 2`, `K = ℂ`, `ζ = -1`.**
It is the strongest cross-module composition in the topic: it joins
`Defs/PhiGen`'s `conj`/`phiProd`, `Defs/PhiAtSlot`'s `roots_phiProd_conj_nodup` and
`Defs/TS`'s `TS_injective`, over a concrete primitive square root supplied by
mathlib's `IsPrimitiveRoot.neg_one`. The other two candidates from the work
order are kept beside it as supporting compositions: the `qTwistEquiv`
round-trip (against a concrete `f = coeffEmb ℂ jq`, so it also touches
`Defs/Jq`) and `phiAtSeed`'s monicity/degree at `modularPolynomialDataOne`
(against `Defs/Polynomial`). -/

#check @ModularCurve.qTwistEquiv
#check @ModularCurve.qTwist_iota_of_pow_eq_one
#check @ModularCurve.qTwist_TS_one_cycle
#check @ModularCurve.qExpand_qTwist_TS
#check @ModularCurve.qExpand_qTwist_notMem_range_qExpand
#check @ModularCurve.iota_jqN
#check @ModularCurve.jqN_congr
#check @ModularCurve.phiProd_conj_eq
#check @ModularCurve.roots_phiProd_conj
#check @ModularCurve.roots_phiProd_conj_nodup
#check @ModularCurve.phiAtSeed
#check @ModularCurve.phiAtSeed_monic
#check @ModularCurve.phiAtSeed_natDegree
#check @ModularCurve.phiAtSeed_eval_symm
#check @ModularCurve.phiAtSeed_jqN_eval_down
#check @ModularCurve.prod_form_ne_zero
#check @ModularCurve.roots_prime_at_slot
#check @ModularCurve.roots_prime_at_slot_nodup
#check @ModularCurve.isRoot_prime_at_slot_iff

-- The chosen wire: the `p + 1 = 3` conjugate values at `ζ = -1` over `ℂ` are
-- distinct, via the primitive square root `IsPrimitiveRoot.neg_one`.
example : (ModularCurve.TS ℂ (2 * 2) 1 ::ₘ
    (Multiset.range 2).map (fun b => ModularCurve.TS ℂ 1 ((-1 : ℂˣ) ^ b))).Nodup :=
  @ModularCurve.roots_phiProd_conj_nodup ℂ _ _ 2 ⟨Nat.prime_two⟩ (-1) (by
    show IsPrimitiveRoot (((-1 : ℂˣ) : ℂ)) 2
    rw [Units.val_neg, Units.val_one]
    exact IsPrimitiveRoot.neg_one 0 two_ne_zero.symm)

-- Its underlying root identity, from the same module.
example : (ModularCurve.PhiGen.phiProd 2 (ModularCurve.PhiGen.conj 2 (-1 : ℂˣ))).roots =
    ModularCurve.TS ℂ (2 * 2) 1 ::ₘ
      (Multiset.range 2).map (fun b => ModularCurve.TS ℂ 1 ((-1 : ℂˣ) ^ b)) :=
  @ModularCurve.roots_phiProd_conj ℂ _ _ 2 ⟨Nat.prime_two⟩ (-1)

-- Supporting wire: the `qTwistEquiv` round-trip at `f = coeffEmb ℂ jq`.
example :
    ModularCurve.qTwistEquiv (-1 : ℂˣ)
      (ModularCurve.qTwist ((-1 : ℂˣ))⁻¹ (ModularCurve.coeffEmb ℂ ModularCurve.jq)) =
        ModularCurve.coeffEmb ℂ ModularCurve.jq := by
  rw [ModularCurve.qTwistEquiv_apply, ModularCurve.qTwist_qTwist, mul_inv_cancel,
    ModularCurve.qTwist_one_apply]

-- Supporting wire: `phiAtSeed`'s degree at `modularPolynomialDataOne`,
-- against `Defs/Polynomial`.
example : (ModularCurve.phiAtSeed ModularCurve.modularPolynomialDataOne (0 : ℚ)).Monic :=
  ModularCurve.phiAtSeed_monic _ _

example : (ModularCurve.phiAtSeed ModularCurve.modularPolynomialDataOne (0 : ℚ)).natDegree =
    ModularCurve.dedekindPsi 1 :=
  ModularCurve.phiAtSeed_natDegree _ _

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

**Φ_p application result (2026-09-22).** Zone F is added and bound:
`FLTForHuman/ModularForms/PhiGenDescends.lean` proves the cone's (c),
`PhiGen.mem_adjoin_jq_of_phiGenDescends`, over the new Hecke layer
(`Defs/HeckeOperator.lean`, `HeckeQExpansion.lean`). The topic's plan sequence is
now complete and (c) is discharged. Zone F binds the statement, the T8 interface
and the correspondence; it has **no concrete wire instance**, because the
hypothesis `hc : PhiGenDescends ℓ ζ c` is the cone's piece (a), which is not
ported — the internal chain is nonetheless a genuine four-module composition.
Still **0 errors**, one `sorry`.

**Integrality result (2026-09-22).** Zone G is added and bound:
`FLTForHuman/ModularCurve/PhiGenIntegrality.lean` proves the first half of the
cone's (b) by **Route A** (`LaurentSeries 𝒪` + `coeffMap` + mathlib's integral
closure, replacing FLT's `CoeffsIntegral` closure machinery).
`PhiGenDescends.intCoeffs` is a binding whose hypothesis `hc` is the cone's (a)
(not ported), so — as in Zone F — no concrete instance is invented;
`aeval_jq_intCoeffs_descent`'s concrete `P = X` instance is the module's private
`aeval_jq_intCoeffs_descent_X`, and Zone G binds its hypothesis form. Still
**0 errors**, one `sorry`.

**Pole-bounds result (2026-09-22).** Zone H is added and bound:
`FLTForHuman/ModularCurve/PhiGenPoleBounds.lean` proves the second half of the
cone's (b) — the leading coefficient of `phiProd`'s constant term and the sharp
pole bound for the other coefficients — and promotes the shared ~180-line
`TPoleOrderLE` prelude into `Defs/PhiGen.lean`, which T11 imports. The wire test
is concrete here (`ℂ`, `ℓ = 2`, `ζ = -1`) and named inside the module. Still
**0 errors**, one `sorry`.

**Construction result (2026-09-22).** Zone I is added and bound: T11's three
modules build the cone's object end-to-end. `PhiGenDescent.lean` proves (a)
`exists_phiGenDescends`; `PhiGenDescendsStructure.lean` the 328 block's five shape
exports (`evalAtJ_injective` by the mathlib `transcendental_jq` route, so T12
imports it rather than carrying the pin's private copy);
`ModularPolynomialAssembly.lean` (d) `exists_modularPolynomialData_coeff_eq` and
`splits_of_coeff_evalAtJ_eq`. The Zone I wire test is **end-to-end** —
`K = CyclotomicField ℓ ℚ` produces a descended family, verifies its T9
integrality, T8 membership and T10/T11 pole bound, and assembles the datum — the
first zone that exercises the whole (a)→(b)→(c)→(d) chain concretely. Still
**0 errors**, one `sorry`.

**Properties result (2026-09-22).** Zone J is added and bound: T12's three modules
prove the datum's properties. `JqCoeffPositivity.lean` gives `one_le_coeff_jq`
(two of the audit's mathlib substitutions landed);
`ModularPolynomialIrreducible.lean` is the 895 block written once (FLT ships it
five times), including `conj_injective`, `aeval_jq_ne_jqN`/
`jqN_not_mem_adjoin_jq`, `phiIrreducible_of_splits`,
`transposeToAdjoin_monic_of_qExpansion`, `evalSymm_of_splits` and
`swapBivar_eq_of_evalSymm`; `ModularPolynomialProperties.lean` concludes
`evalSymm_of_coeff_evalAtJ_eq` and the capstone
`exists_phiIrreducible_evalSymm`. The Zone J wire test is the first
**unconditional** one: `exists_phiIrreducible_evalSymm` at `ℓ = 2` produces an
irreducible symmetric datum with no unported hypothesis, and
`aeval_jq_ne_jqN`/`jqN_not_mem_adjoin_jq` become unconditional once
`one_le_coeff_jq` supplies their `hpos`. Still **0 errors**, one `sorry`.

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
16. **Topic 8 — no Hecke operators in mathlib, and three real shape issues.**
    (a) `grep -rln heckeMatrix Mathlib/` is empty: mathlib has no Hecke
    matrices, so `Defs/HeckeOperator.lean` is a definitions port, the first since
    Layer 0b. Only the subset the cone uses (4 public declarations plus private
    `val_*`/`det_*`/`denom_*`) is taken; the `heckeU`/`heckeT`/`coeffHecke*`/
    `slash_hecke*`/`σ_hecke*` block has **0 occurrences** in T8's five pin files
    and appears in the cone's other node files only in the doc-site
    `attribute [-simp] ModularForm.heckeU_zero …` pragma (5 files), never
    mathematically.
    (b) **A transparency issue, fixed by mathlib's own workaround.** The pin's
    `@[scoped simp] mapGL_apply` (and every explicit variant) failed to rewrite
    the entries of the *anonymous* `SL(2,ℤ)` matrix `⟨!![…], _⟩` produced by
    `refine`, with Lean reporting "not type-correct under the implicit
    transparency level". `set_option backward.isDefEq.respectTransparency.types
    false in` before the four commutation lemmas — the same directive mathlib uses
    in `Discriminant.lean` — makes the default `simp` reduce the entries, and
    `mapGL_apply` is not needed at all. Not a heartbeat blow-up.
    (c) Two smaller shape issues: `redMatrix g` needed explicit `(p := p)` (the
    `Fact p.Prime` instance stayed stuck on an unresolved `p`), and in
    `sigma_zeta` a local `have : IsCyclotomicExtension …` is *not* found by
    instance search where `haveI` is, so the `linter.style.haveILetI` warning is
    disabled locally for that declaration rather than silently weakening the
    proof. `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` again (entry 2's
    family), four times.
17. **Topic 10 — the shared-block promotion, and `ite_eq_*` again.**
    (a) FLT keeps the `TPoleOrderLE` closure `private` (or exposes it only through
    the `p2m_export` alias) in all six files that repeat it, so the text checker
    has no *public* statement to diff for eleven of the promoted declarations;
    the port promotes them anyway (T11 has to name them from `Defs/`), and the
    checker gained a dotted-name fallback that reads the pin's `private`
    declarations (entry below). This is the first promotion the checker can
    verify only through a `private` source.
    (b) `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` six times in the ported
    block (entry 2's family), all flagged by the deprecation linter.
    (c) The wire test's `Fact (Nat.Prime 2)` has no global instance in mathlib
    (only `Quaternion.lean` supplies one locally), so the instance is passed
    explicitly as `(hℓ := ⟨Nat.prime_two⟩)` rather than with `haveI`, which the
    style linter would flag.
18. **Topic 11 — the mathlib route for `evalAtJ_injective`, and the cyclotomic
    instances.**
    (a) The work order's `transcendental_jq` route closed on the first attempt:
    `transcendental_iff_injective.mp transcendental_jq` composed with
    `Polynomial.map_injective _ Int.cast_injective` through the six-line
    `evalAtJ_eq_aeval_map` bridge. The pin's private 19-line `aeval_jq_eq_zero` is
    not ported here; the port's public `aeval_jq_eq_zero` (from `Defs/Jq.lean`,
    and the `Thm_ModularCurve_aeval_jq_eq_zero` interface) stays as it is.
    (b) `IsGalois`/`FiniteDimensional` for `CyclotomicField ℓ ℚ` are theorems, not
    instances, so the Zone I wire test and the pin's `exists_phiIrreducible_evalSymm`
    both install them with `haveI` (`IsCyclotomicExtension.isGalois`/
    `.finiteDimensional`); the style linter flags those `haveI`s, and the example
    disables `linter.style.haveILetI` locally rather than weakening the proof.
    (c) `PoleOrderLE` and `evalAtJ` live at the `ModularCurve` level, not
    `ModularCurve.PhiGen`; the `PhiGenDescends.*` methods and `evalAtJ_injective`
    do live under `PhiGen`.
19. **Topic 12 — the scoped fraction-field instances, and the wrapper-spelling
    rule again.**
    (a) **The one real blocker.** `Algebra (Algebra.adjoin F S) (adjoin F S)` and
    the matching `IsFractionRing` are mathlib's **scoped** instances in
    `IntermediateField.algebraAdjoinAdjoin`. FLT's `p2m_open` activated that
    namespace; a textual translation drops it, and the port needed an explicit
    `open scoped IntermediateField.algebraAdjoinAdjoin`. The
    `IsIntegrallyClosed adjoinJq` instance the work order worried about was *not*
    needed — the private scoped `UniqueFactorizationMonoid adjoinJq` from
    `transcendental_jq` plus mathlib's UFD → integrally-closed path suffices.
    (b) **Wrapper binders, fourth time.** `aeval_jqN_toAdjoin` and
    `minpoly_jqN_eq` were first written with the `S_` file's section variables and
    the checker flagged both against their wrappers' explicit binders (the same
    rule as entries 7, 10 and 17). Public declarations verified against a
    `Theorems/` wrapper must carry the wrapper's binders.
    (c) `Polynomial.degree_sub_lt` is deprecated in favour of
    `Polynomial.degree_sub_lt_left`; the `haveI` style linter fired once (the
    cyclotomic instances) and was disabled locally. The Vieta step's
    `Polynomial.eq_of_natDegree_lt_card_of_eval_eq` and
    `prod_X_sub_C_coeff_card_pred` matched the pin's spelling unchanged.

    **T13 closed the cone.** `ModularPolynomialUniqueness.lean` (the degree
    `ℓ + 1` and uniqueness) and `PhiGenSplits.lean` (`splits_of_prime` and the
    headline `splits_prime_at_slot`) landed in one round — 407 lines against 766
    deduplicated pin lines (ratio 0.53), with ~200 dead pin prelude lines dropped
    and all four public statements matching their wrappers on the first build.
    T13 also promoted the cyclotomic roots to the public `Defs/Cyclotomic.lean`
    (removing the FFG spine's private twins), so the checker moved 233 → 242. The
    one remaining `sorry` below is the FFG `Inputs` gap, not this cone's.

The `sorry`s are not errors and do not count: their job is to keep the
*statements* checkable while the proofs are out of scope.
-/
