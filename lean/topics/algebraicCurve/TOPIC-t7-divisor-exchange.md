# T7 — the divisor exchange (CAPSTONE, reserved for the human reviewer)

**Status (2026-09-23): done by the human reviewer.** The capstone is proved in
`FLTForHuman/AlgebraicCurve/WeilExchange/DivisorExchange.lean` (143 lines, statement
verbatim); consumer Zone J composes it with T4's
`Divisor.correspondence_correspondence`; the checker reports 618 identical / 0
mismatched / 0 missing; `#print axioms` is clean. See `logs/ac-port.md` §10–§11. This
is the **capstone**
of the `AlgebraicCurve` effort and it is reserved for the human reviewer, as the
review instrument: the best way to check what SET 1 and SET 2 produced is to consume
it. It is the last topic; do not dispatch it to a coding agent.

**Audience.** The reviewer, after SET 2's T5 and T6 have landed and been reviewed.

**Goal.** Prove
`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`
in `FLTForHuman/AlgebraicCurve/WeilExchange/DivisorExchange.lean`, then close the
effort: consumer Zone D, `#print axioms`, the checker at 0/0, the log, the blueprint
status and `README.md`.

This is the declaration `ModularCurve.heckeOperatorsCommuteBar` calls
(`S_ModularCurve_heckeOperatorsCommuteBar.lean:42`), so proving it makes the AC side
of `math/009`'s exchange reduction unconditional.

## 1. The statement, and what it consumes

Pin: `S_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`
(121 raw / 99 content), wrapper
`Theorems/Thm_AlgebraicCurve_Divisor_pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong.lean`.

```lean
theorem AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong
    {K F A B E : Type*} [Field K] [Field F] [Field A] [Field B] [Field E]
    [Algebra K F] [Algebra K A] [Algebra K B] [Algebra K E]
    [HasPrincipalDivisors K B] [HasPrincipalDivisors K E]
    (a : F →ₐ[K] A) (b : F →ₐ[K] B) (a' : A →ₐ[K] E) (b' : B →ₐ[K] E)
    (ha : a.toRingHom.IsIntegral) (hb : b.toRingHom.IsIntegral)
    (ha' : a'.toRingHom.IsIntegral) (hb' : b'.toRingHom.IsIntegral)
    (hsq : b'.comp b = a'.comp a)
    (hfin : FiniteAlong K (a'.comp a)) (hsep : SeparableAlong K (a'.comp a))
    (hgen : Algebra.adjoin K (Set.range a' ∪ Set.range b') = ⊤)
    (hLD : finrankAlong K (a'.comp a) = finrankAlong K a * finrankAlong K b)
    (D : Divisor K A) :
    Divisor.pullbackAlong b hb (Divisor.pushforwardAlong a ha D) =
      Divisor.pushforwardAlong b' hb' (Divisor.pullbackAlong a' ha' D)
```

Dependencies, all SET 1/T5/T6:

| ingredient | from |
|---|---|
| `algebraAlong`, `isScalarTower_along`, `isIntegral_along`, `FiniteAlong`, `SeparableAlong`, `finrankAlong`, `pullbackAlong`, `pushforwardAlong`, `fiberAlong`, `restrictAlong`, `ramificationIndexAlong`, `inertiaDegAlong` | AC0 |
| `restrict_restrict` (the shared prelude) | T4, `WeilExchange/Transport.lean` |
| `sum_ramificationIndex_mul_inertiaDeg_exchange` | T6 |
| `Place.fiberOver`, `mem_fiberOver` (through T6) | T2 |

Note: the statement is unconditional — every premise is an explicit argument or a
`HasPrincipalDivisors` **instance**. That is why the AC effort has no conditional
`Spine.lean` (the blueprint's §7.2 Zone E); see that note now folded into
`PORTING-AC.md` §7.2.

## 2. Route notes — the pin's proof, annotated

The pin's proof is 99 content lines and is almost entirely setup plus a
`Finsupp`/`Finset` computation:

1. **`classical`**, then the six `letI`s that install `algebraAlong` for
   `a`, `b`, `a'`, `b'`, `a'.comp a` and the `IsScalarTower`s that make the
   along-API applicable; then the four `Algebra.IsIntegral` instances and
   `Module.Finite F E`, `Algebra.IsIntegral F E` (from finiteness),
   `Algebra.IsSeparable F E` (from `hsep`), `FiniteDimensional` for `A E`, `B E`,
   `F A`, `F B`.
2. **`hgenF`**: restate `hgen` over `F` instead of `K`:
   `Algebra.adjoin F (Set.range (algebraMap A E) ∪ Set.range (algebraMap B E)) = ⊤`.
   The pin proves it via `Algebra.adjoin_le` and `Subalgebra.mem_restrictScalars`.
   The set equality `Set.range (algebraMap A E) ∪ Set.range (algebraMap B E) =
   Set.range a' ∪ Set.range b'` is `rfl`.
3. **The four `rfl` bridges** — the named shape risk:
   ```lean
   have eA : ∀ W : Place K E, Place.ramificationIndexAlong a' W = W.ramificationIndex A := fun _ => rfl
   have fB : ∀ W : Place K E, W.inertiaDegAlong b' hb' = W.inertiaDeg B := fun _ => rfl
   have fF : ∀ w : Place K A, w.inertiaDegAlong a ha = w.inertiaDeg F := fun _ => rfl
   have eF : ∀ w : Place K B, Place.ramificationIndexAlong b hb = w.ramificationIndex F := fun _ => rfl
   ```
   These hold only while `algebraAlong` is an `abbrev` (T4's canary). If one fails,
   the fix is to restore the `abbrev`/instance, **not** to add a `simp` lemma.
4. **`Finsupp.addHom_ext fun wA n => …`** on `Divisor.pushforwardAlong_single` and
   `Divisor.pullbackAlong_single`, then `ext wB` and **`Finset.sum_apply'` twice**,
   then `simp only [Finsupp.single_apply, Finset.sum_ite_eq', eA, fB, fF, eF]`.
5. **Split on `hv : wB.restrictAlong b hb = wA.restrictAlong a ha`.** In the `if_pos`
   branch, build
   ```lean
   have hT : ∀ W, W ∈ (Place.fiberAlong a' ha' wA).filter (fun W => W.restrictAlong b' hb' = wB)
       ↔ W.restrict A = wA ∧ W.restrict B = wB
   ```
   and feed it to **T6's** `Place.sum_ramificationIndex_mul_inertiaDeg_exchange`, then
   reassociate with `Finset.sum_congr`/`Finset.mul_sum` and finish with
   `exact_mod_cast key.symm`. In the `if_neg` branch the sum is zero, and the
   contradiction uses `Place.mem_fiberAlong` plus `restrict_restrict` (T4) twice.
6. `suffices … from DFunLike.congr_fun h D` wraps the add-monoid-hom equality.

The `DecidableEq (Place K E)` needs (blueprint §8 risk 8) are the
`Finset.filter`/`Finset.sum_ite_eq'` steps; `classical` supplies them, and the
`simp only` set must not be expanded blindly or the `if` splits will not match.

## 3. Named shape risks

| risk | mitigation |
|---|---|
| `Finsupp.addHom_ext` + `Finset.sum_apply'` plumbing | transcribe the pin's `simp only` set literally; do not golf the split |
| `DecidableEq (Place K E)` for `Finset.filter` | keep `classical` at the proof head; make the instance explicit only if synthesis fails |
| the four `rfl` bridges | T4's `abbrev`/`reducible` attributes must still be in place; if a bridge fails, stop and fix the attribute, do not re-prove |
| `hgenF`'s `Subalgebra.mem_restrictScalars` step | mathlib API; check the two directions before rewriting |
| `exact_mod_cast key.symm` | the exchange is a `ℤ`-valued `Finset.sum` with `ℕ`-valued indices; keep the pin's cast direction |

## 4. Budget and stop-early

**2 goal rounds, checkpoint at 1.** 99 content lines, all plumbing, with T6 as a
black box. Stop early and report on: an `rfl` bridge that fails (attribute damage); a
T6 statement whose binders do not match the call site; or `Finset.sum_apply'`
production of an impossible goal shape (quote it).

## 5. Definition of done

- [ ] `WeilExchange/DivisorExchange.lean` with the theorem public, statement verbatim
      from the wrapper; `hgenF` and the `eA`/`fB`/`fF`/`eF` bridges `have`s in the
      proof, not new public declarations.
- [ ] Consumer **Zone D** (renamed from the blueprint's Zone C/D scheme): the
      abstract-square wire test — state the theorem and apply it to a concrete
      abstract square, with the `algebraAlong`/`IsScalarTower` setup itself as the
      wire test, then compose with `Pic0.correspondence_correspondence_comm`.
      (T4 already added a first exchange zone; this closes it.)
- [ ] `#print axioms` on the theorem is `[propext, Classical.choice, Quot.sound]`.
- [ ] `spec/check_flt_statements.py`: the AC wrapper in `SOURCES`; 0 mismatched,
      0 missing.
- [ ] `timeout 300 lake build` green, **0 warnings**, no `sorry`; the consumer at
      0 errors.
- [ ] `logs/ac-port.md` T7 section, and its §0 table row for the capstone.
- [ ] `PORTING-AC.md` status set to **complete**, the §0 "what this port is not"
      table unchanged in scope (the `ModularCurve` Hecke layer remains out of scope),
      and the §11 links verified to point at `aa2d8b3`.
- [ ] `README.md` module table and status updated; `logs/ac-port.md` friction log
      finalised; the FFG retrospective's "residual items" pattern applied: list what
      SET 2 deferred (`card_fiberOver_eq`/`fiber_eq_fiberOver` if dropped, the
      `RatFuncPlaces` `Place.Congr` cut, the Galois `≃ₐ` action) as deferred API, not
      as gaps.
- [ ] The three `math/009` inputs this layer supplies — the Weil exchange,
      `separableAlong_of_charZero`, and `HasPrincipalDivisors` for the modular
      function field — are ported theorems, and the note says so.

## 6. Reporting back (the closeout report)

The final report to the repository's record should state, with quoted command output:
the per-topic table (all ten topics), total lines/declarations written vs the
blueprint's ≈5.1k–5.9k estimate, the checker's final line, the consumer's error count,
the two `#print axioms` results, the measured drop list, the friction log's headline
entries, and the residual/deferred list. That report is what makes the *next* port
cheaper; write it into `logs/ac-port.md` and link it from `PORTING-AC.md`.
