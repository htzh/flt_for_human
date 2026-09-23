# T9 — `HasPrincipalDivisors` via transcendence (2 nodes + the norm block)

**Status (2026-09-23): work order written, not started.** Fourth and last topic of
SET 2; read [SET-2.md](SET-2.md) first. Depends on **T8** and SET 1's **T2**
(`Defs/PlaceDictionary.lean`) and **T1**.

**Audience.** A fresh session closing SET 2. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5; the plan is
[PORTING-AC.md](../../PORTING-AC.md) §3.2 (Route B), §5 (T9's note) and §8 (risks 5
and 9). Read the SET 1 hand-off in [SET-2.md](SET-2.md) §0 — the 16-declaration
fibre dictionary is already public in `Defs/PlaceDictionary.lean` and **must be
imported, not restated**.

**Goal.** Prove `hasPrincipalDivisors_of_transcendental` — for `K` of
characteristic zero and `F` a finite-dimensional extension of `K(x)` with `x`
transcendental, `HasPrincipalDivisors K F` — plus its `adjoin` form. The route is
the norm formula
`ord_v(N_{F'/F} f) = ∑_{w | v} inertiaDeg(w) · ord_w(f)` built on the fibre-centre
dictionary and `Ideal.relNorm`, transferred from the `P¹` base case (T8).

This is one of the three generic inputs of `math/009`'s exchange reduction, so its
statement is deliberately generic in `K` (characteristic zero), **not** specialised
to `AlgebraicClosure ℚ` (risk 10).

## 1. The two nodes

Wrapper statements:

```lean
theorem AlgebraicCurve.hasPrincipalDivisors_of_transcendental (K : Type*) [Field K] [CharZero K]
    {F : Type*} [Field F] [Algebra K F] (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] :
    HasPrincipalDivisors K F

theorem AlgebraicCurve.hasPrincipalDivisors_adjoin_of_transcendental (K : Type*) [Field K]
    [CharZero K] {LF : Type*} [Field LF] [Algebra K LF] (x : LF) (hx : Transcendental K x)
    (T : Finset LF) (hT : ∀ t ∈ T, IsIntegral (IntermediateField.adjoin K ({x} : Set LF)) t) :
    HasPrincipalDivisors K (IntermediateField.adjoin K (insert x (T : Set LF)))
```

Home: `FLTForHuman/AlgebraicCurve/PrincipalDivisors/Transcendence.lean`.

## 2. The pin's structure (all declarations, with what to keep public)

The pin file is `S_AlgebraicCurve_hasPrincipalDivisors_of_transcendental.lean`
(799 raw / 588 content). Lines 36–386 are the **fibre dictionary**, which SET 1
already promoted into `Defs/PlaceDictionary.lean` — **do not re-port it**. What
remains, in dependency order (all `private` in the pin unless noted):

| # | declaration | pin line | note |
|---|---|---|---|
| 1 | `Place.aeval_mem` | 403 | `Q.coeff i ∈ w.toValuationSubring` and `x ∈ w.toValuationSubring` ⇒ `aeval x Q ∈ …` |
| 2 | `Place.exists_coeff_ord_ne_zero` | 412 | from `ord f ≠ 0` produce a non-zero coefficient of `minpoly` with non-zero `ord` |
| 3 | `ord_coe_eq_of_span_singleton_eq_pow_maximalIdeal` | 487 | `span {r} = maximalIdeal ^ n ⇒ v.ord (r : F) = n` |
| 4 | `relNorm_fiberCenter` | 526 | `relNorm p (fiberCenter …).asIdeal = p ^ w.inertiaDeg F` via `Ideal.relNorm_eq_pow_of_isMaximal` |
| 5 | `count_normalizedFactors_span_singleton` | 539 | `count (normalizedFactors (span {c})) P = (ord c).toNat` via `Ideal.count_normalizedFactors_eq` |
| 6 | `relNorm_span_singleton` | 556 | `relNorm p (span {c}) = p ^ ∑_{w} inertiaDeg(w) · (ord_w c).toNat`, by factoring over the fibre-centre primes |
| 7 | `ord_norm_algebraMap_integralClosureAt` | 644 | the integral-closure form of the norm formula |
| 8 | `ord_norm_eq_sum_fiberOver` | 663 | `v.ord (Algebra.norm F f) = ∑_{w ∈ fiberOver} (inertiaDeg w : ℤ) * w.ord f` |
| 9 | `pushforwardNormFormula_of_finiteDimensional` | 703 | `Divisor.PushforwardNormFormula K F F'` from #8 |
| 10 | `finite_setOf_ord_ne_zero_of_finiteDimensional` | 730 | `{w | w.ord f ≠ 0}.Finite` via `minpoly`, #2, T8's `finite_setOf_ord_ne_zero`, and AC0's `finite_setOf_restrict_eq` |
| 11 | `hasPrincipalDivisors_of_finiteDimensional_ratFunc` | 754 | **make this public** (risk 9) — the shared finite-dimensional theorem |
| 12 | `solution` = `hasPrincipalDivisors_of_transcendental` | 780 | the wrapper node |
| 13 | `hasPrincipalDivisors_adjoin` (the `adjoin` file) | — | the second wrapper node, in `S_AlgebraicCurve_hasPrincipalDivisors_adjoin_of_transcendental.lean` (85/53) |

**Keep 1–10 `private`**; **expose 11 public** as
`AlgebraicCurve.hasPrincipalDivisors_of_finiteDimensional_ratFunc` (it is the
out-of-cone duplicate's shared statement: the pin's
`S_AlgebraicCurve_hasPrincipalDivisors_of_finiteDimensional_ratFunc.lean` is
byte-identical to 11–13's core, and `PORTING-AC.md` §8 risk 9 settles that one copy
is exposed for both consumers). Add both pin `S_` files to the checker's `SOURCES`
so 11–13 and the private helpers' dotted fallbacks are read.

## 3. Route notes

- **The norm block is real mathematics mathlib does not have** (`PORTING-AC.md`
  §3.2). `relNorm` exists, but "the norm of the fibre-centre ideal is the maximal
  ideal to the inertia degree" (#4) and the `normalizedFactors` factorisation (#6)
  do not. The pin's `normalizedFactors` route: `Ideal.prod_normalizedFactors_eq_self`,
  `map_prod`/`map_pow`, `Finset.prod_pow_eq_pow_sum`, `Ideal.relNorm_eq_pow_of_isMaximal`,
  and the fibre-centre bijection (`placeOfPrime`/`restrict_placeOfPrime`/
  `fiberCenter_placeOfPrime`, `eq_of_fiberCenter_eq`, `Finset.sum_image`). Golfing
  it is out of scope — the blueprint §6.1 leaves it in place until a route audit
  says otherwise (`PORTING-AC.md` §10's last open question).
- **Risk 5, `PerfectField`:** `Ideal.relNorm_eq_pow_of_isMaximal` requires
  `[PerfectField (FractionRing R)]`. Here `R = v.toValuationSubring` and its
  fraction ring is `F`, so the instance comes from `PerfectField.ofCharZero` on
  `F` (the section has `[CharZero F]`, transported from `[CharZero K]`). Make it
  fire; do **not** weaken the statement or add a hypothesis. If `synthInstance`
  needs help, provide the `CharZero (FractionRing …)` instance explicitly and
  record it.
- **The deprecated `Ideal` API appears in the norm block** (`inertiaDeg'`,
  `inertiaDeg_algebraMap`, `ramificationIdx_spec`, `inertiaDeg'_pos`). Since 1–10
  are `private`, the checker never sees them; the module may carry
  `set_option linter.deprecated false` with a reason (SET-1 §3.1's table gives the
  replacements: `Ideal.inertiaDeg'_eq_inertiaDeg`, `Ideal.inertiaDeg'_algebraMap`,
  `Ideal.ramificationIdx'_spec`, `Ideal.inertiaDeg_pos`). Prefer the new names in
  the proofs; keep the pin's text where it is a statement.
- **#11 `hasPrincipalDivisors_of_finiteDimensional_ratFunc`:** build
  `D := Finsupp.onFinset hfin.toFinset (fun w => w.ord f) …` from #10, show
  `Divisor.degree (Divisor.pushforward (RatFunc K) D) = 0` by T8's
  `degree_eq_zero_of_forall_eq_ord` applied to `pushforwardNormFormula_of_finiteDimensional`,
  and rewrite by `Divisor.degree_pushforward`. Note the `CharZero (RatFunc K)`
  instance from `charZero_of_injective_algebraMap`.
- **#12 `solution`:** transfer along
  `e : RatFunc K ≃ₐ[K] ↥(IntermediateField.adjoin K {x}) := RatFunc.algEquivOfTranscendental x hx`,
  install `Algebra (RatFunc K) F` through `e`, the two `IsScalarTower`s,
  `Module.Finite (RatFunc K) (adjoin …)` from `e.surjective`, and
  `FiniteDimensional (RatFunc K) F` by `Module.Finite.trans`; then apply #11. This
  is the pin's `letI`/`haveI` block, 25 lines.
- **#13 `hasPrincipalDivisors_adjoin`:** the `IntermediateField` packaging:
  `x' : F := ⟨x, …⟩` with `Transcendental K x'` from
  `transcendental_algebraMap_iff`, `A := adjoin K {x'}`, `lift A = adjoin K {x}`
  via `lift_adjoin_simple`, `e : A ≃ₐ[K] adjoin K {x}` from `liftAlgEquiv`,
  `FiniteDimensional A F` via `finiteDimensional_adjoin` + a `lift`/`restrictScalars`
  `⊤` computation, then #12. It is 53 content lines and uses the three
  `isIntegral_adjoin_*` lemmas from SET 1's `Defs/IntegralAdjoin.lean`.

## 4. Named shape risks

| risk | mitigation |
|---|---|
| `Ideal.relNorm_eq_pow_of_isMaximal`'s `PerfectField` | `PerfectField.ofCharZero` on `F`; make it fire, never weaken |
| the `normalizedFactors` factorisation | transcribe the pin; the two `Finset.sum_subset`/`sum_image` steps are where it can stall |
| `count_normalizedFactors_eq`'s two side goals | they are the `le_ord_iff_mem_pow_fiberCenter` (T2) boundaries; `omega`/`push_cast` |
| the `Finsupp.onFinset` construction | its `support` proof is the finiteness #10 |
| `transcendental_algebraMap_iff` in the adjoin node | mathlib's; check its binder order |

## 5. Budget and stop-early

**3 goal rounds, checkpoint at 1.** 641 content lines, minus the ≈350 that SET 1
already wrote as the dictionary → ≈290 new, mostly the `relNorm`/`normalizedFactors`
block (which the blueprint prices as irreducible).

**Stop early, and report rather than restate, on**: `PerfectField (FractionRing R)`
not synthesizing (quote the goal); `Ideal.prod_normalizedFactors_eq_self` or
`Ideal.count_normalizedFactors_eq` having a different v4.34 shape; or the `adjoin`
node needing an `IntermediateField` lemma mathlib lacks.

## 6. Definition of done

- [ ] `PrincipalDivisors/Transcendence.lean` with the two nodes public (statements
      verbatim), `hasPrincipalDivisors_of_finiteDimensional_ratFunc` public, the
      norm block `private`, and the T2 dictionary imported.
- [ ] Consumer **Zone I** (`[transcendence]`) at 0 errors:
      `HasPrincipalDivisors K (RatFunc K)` and the transcendence statement, and a
      composition of the two (the blueprint §7.2 Zone G).
- [ ] `spec/check_flt_statements.py`: the two wrappers **plus** the two pin `S_`
      files in `SOURCES`; 0 mismatched, 0 missing.
- [ ] `#print axioms` on `hasPrincipalDivisors_of_transcendental` and
      `hasPrincipalDivisors_adjoin_of_transcendental` clean.
- [ ] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [ ] `logs/ac-port.md` T9 section (the `PerfectField` outcome, the norm-block cost);
      `README.md` rows.
- [ ] SET 2 complete report: the per-topic table, checker line, consumer zones, and
      the hand-off to the human's T7 (`Bifibre.lean`/`LocalExchange.lean` exposure
      and the `HasPrincipalDivisors` instances T7's typeclasses need).

## 7. Reporting back

Beyond [SET-2.md](SET-2.md) §3: (1) the `PerfectField` outcome and the exact
instance that fired; (2) whether any of the norm block was reducible to a mathlib
`relNorm` lemma (the blueprint §10 open question — a recorded *negative* is as
valuable as a win); (3) whether `hasPrincipalDivisors_of_finiteDimensional_ratFunc`
exposed publicly caused any consumer or checker issue.
