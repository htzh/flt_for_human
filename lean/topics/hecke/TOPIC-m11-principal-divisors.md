# Topic m11 — `HasPrincipalDivisors` for the modular function fields (M11)

**Status: work order drafted (pending the earlier sets).** Second topic of
[SET-M4](SET-M4.md). Read [SET-M1](SET-M1.md) §2–§3 first.

**Goal.** One module, `FLTForHuman/ModularCurve/PrincipalDivisors/ModularCurveBar.lean`,
with the two M11 nodes:

```lean
theorem ModularCurve.hasPrincipalDivisors_laurentBaseChange_modularFunctionFieldFull
    (L : Type*) [Field L] [Algebra ℚ L] (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors L (laurentBaseChange L (modularFunctionFieldFull N))

theorem ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar
    (hΦ : ModularPolynomialFamily) (N : ℕ) [NeZero N] :
    HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
```

**Why this topic.** These are `math/009` §5's principal-divisors input, and the
coverage report (§5) predicted they are "nearly a corollary" of the ported AC
transcendence theorem. Test that prediction.

## 1. The route

AC's port already has (`AlgebraicCurve/PrincipalDivisors/Transcendence.lean`):

```lean
theorem AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K] [CharZero K]
    {LF : Type*} [Field LF] [Algebra K LF] (x : LF) (hx : Transcendental K x) (T : Finset LF)
    (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF)))
```

and its `[... ] : FiniteDimensional` companion `hasPrincipalDivisors_of_transcendental`.

**Layer form.** Take `L` for `K`, `x = coeffEmb L jq` (so
`IntermediateField.adjoin L {x} = L⟮jqModC L⟯` by m7's `coeffEmb_jq`), `hx` from
m6's `transcendental_jqModC L`, and `T` = the finite generating set of m10's
`gens`/`isIntegral_gens` machinery (`T = {jqNModC L d | d ∣ N}`), whose elements
are integral by m10's `isIntegral_jqNModC_mul`. m7's
`laurentBaseChange_modularFunctionFieldFull` rewrites
`laurentBaseChange L (modularFunctionFieldFull N)` as
`adjoin L (insert x (T : Set LF))`.

**Bar form.** `modularFunctionFieldBar N` is *definitionally*
`laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)`; apply the
layer form at `L = AlgebraicClosure ℚ` (char zero fires by
`PerfectField.ofCharZero`/`CharZero` instances, as AC's T9 recorded) and unfold.

**Report `hΦ`'s role honestly.** The wrapper takes `(hΦ : ModularPolynomialFamily)`;
state whether the proof consumes it only through the datum-integrality lemmas (m6/m10)
or whether a `data : ModularPolynomialData N` is needed directly. If the pin's proof
uses more than the adjoin route, quote the divergence rather than adding a hypothesis.

## 2. Verification

- Append the two wrappers to `SOURCES`; the module to `PORT_FILES`.
- checker 0 mismatched / 0 missing.
- `#print axioms` on both; both must be `[propext, Classical.choice, Quot.sound]`.
- Consumer Zone G `[inputs]`: `hasPrincipalDivisors_modularFunctionFieldBar`
  applied at `N = 1`, and the `HeckeInputsAlong` instance it feeds (with m10's
  integrality) for a concrete prime.

## 3. Budget

**1 goal round.** It is a two-node corollary topic; if it does not collapse, stop
and report.

**Stop early on**: the AC theorem's `FiniteDimensional`/`IsIntegral` hypotheses
not matching the modular field's shape; or `hΦ` being consumed in a way the
adjoin route cannot express.

## 4. Reporting back

1. Module/line/decl table and checker before/after.
2. The exact AC theorem used and the instantiation of its hypotheses.
3. `hΦ`'s role, and whether the 38-content prediction held.
