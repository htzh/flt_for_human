# Topic: the low coefficients of `jq` — `744` and `196884`

**Status: done (2026-09-21), 1 goal round of 4.** `coeff_jq_zero` and
`coeff_jq_one` are proved in `FLTForHuman/ModularCurve/JqCoefficients.lean`
(2 public theorems + 22 `private` helpers, 207 lines); the consumer is at 0
errors with only the capstone `sorry`, and `lake build` is green, warning-free and
`sorry`-free. The route is the one in §2 below; the only unanticipated API was
the two `coeff_two_*` helpers. The measured cost, the **≈0.87 : 1** ratio against
FLT's closest analogue, and the finding that FLT proves these coefficients in a
standalone 237-line file rather than the 11k-line cluster are in
[logs/ffg-port.md](../../logs/ffg-port.md) §2c and §8.3.

**Audience.** A fresh session taking the first *topic* of the
`functionFieldGeneration` effort, now that Layer 0 is complete
([logs/ffg-port.md](../../logs/ffg-port.md) §8). Read
[PORTING-FFG.md](../../PORTING-FFG.md) §0 and §2 once for the scope argument, and
[porting-playbook.md](../../porting-playbook.md) §3–§5 for the method. Everything
Layer 0 established still binds.

**Goal.** Prove

```lean
theorem coeff_jq_zero : jq.coeff 0 = 744
theorem coeff_jq_one  : jq.coeff 1 = 196884
```

in a new module `FLTForHuman/ModularCurve/JqCoefficients.lean` (a result, so **not** under
`Defs/`), mathlib-only, green, zero warnings, zero `sorry`. That closes the last
two consumer items: after this, the only `sorry` left in
`spec/ModularCurveConsumer.lean` is the capstone example, which is the deferred
theorem by design.

## 1. Why this topic, and what is settled

This is the payoff of [base/004](../../../base/004-the-j-invariant.md)'s
`j(q) = q⁻¹ + 744 + 196884 q + ⋯`. Consumer Zone C has carried those two claims
as `sorry` since Layer 0, on the assumption that reaching them meant porting the
modular-form q-expansion cluster — 44 nodes and 11k lines inside the deferred Φ_p
subtree. **That assumption is wrong, and this work order exists because it is.**

- **Settled: use mathlib's pentagonal route, not FLT's.** FLT reaches `η`'s
  coefficients through `S_ModularCurve_StarBank_deltaNorm.lean`
  (`rescale_tprod_one_sub_X_pow`, `expand_tprod_one_sub_X_pow`) and the modular
  form cluster. mathlib already has the classical expansion:
  `PowerSeries.tprod_one_sub_X_pow : ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R`,
  with `coeff_pentagonalSeries_pentagonal` and
  `coeff_pentagonalSeries_eq_zero` giving the coefficients. Since
  `Def_ModularCurve_X0.lean` defines `etaProd` as *exactly* that `∏'`, the
  coefficients are available without any of FLT's cluster. **This is a deliberate
  divergence from FLT's route**, and it is the same hybrid strategy that made the
  first port cheap: where mathlib has absorbed the analytic-adjacent layer, use
  mathlib. Record the divergence in the module header.
- **Settled: the topic is the two coefficients and nothing else.** Do not port
  `StarBank`, the modular forms, or anything else from the Φ_p subtree. Do not
  take a second topic in the same session.
- **Settled: names.** FLT has no declaration for these two facts (`hasSum_jq_qParam`
  is a different statement reached a different way), so there is no FLT name to
  keep. Follow the port's own convention from `Defs/Jq.lean`: `coeff_jq_zero`,
  `coeff_jq_one`, sitting next to `coeff_jq_neg_one`, `coeff_jq_of_lt`.

## 2. The route

All of this is Layer 0 material, already ported:

1. `jq` is defined as `HahnSeries.single (-1) 1 * ofPowerSeries jNumQ`, so
   `jq.coeff k = jNumQ.coeff (k + 1)`. Reduce both goals to coefficients of
   `jNum` at `1` and `2`.
2. `jNum = eisenstein4 ^ 3 * dedekindEtaUnitInv` and
   `jNumQ = jNum.map (Int.castRingHom ℚ)`. Go through `PowerSeries.coeff_mul`
   and `PowerSeries.coeff_pow` (both explicit `Finset` sums).
3. `eisenstein4` has an explicit coefficient formula
   (`PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, d ^ 3`),
   so its low coefficients are `1, 240, 2160, …`.
4. `dedekindEtaUnit = etaProd ^ 24`, `dedekindEtaUnitInv = dedekindEtaUnit.invOfUnit 1`.
   Rewrite `etaProd` to `pentagonalSeries` with `tprod_one_sub_X_pow`; its low
   coefficients are `1, -1, -1, 0, 0, 1, …` from
   `coeff_pentagonalSeries_pentagonal` / `coeff_pentagonalSeries_eq_zero`.
   `PowerSeries.coeff_pow` then gives `η ^ 24`'s low coefficients, and
   `PowerSeries.coeff_invOfUnit` (the recursive inverse formula, with constant
   term `1`) gives `Δ⁻¹`'s.
5. Finish with `norm_num` / `decide` on the resulting arithmetic. As a check, the
   numbers are `E₄³ = 1 + 720q + 179280q² + ⋯`, `η²⁴ = 1 - 24q + 252q² + ⋯`,
   `Δ⁻¹ = 1 + 24q + 324q² + ⋯`, hence `jNum = 1 + 744q + 196884q² + ⋯`.

A useful fallback if the general route is fiddly: prove just the coefficients
needed, `coeff (eisenstein4 ^ 3) 1`, `coeff (etaProd ^ 24) 1`,
`coeff (etaProd ^ 24) 2`, `coeff dedekindEtaUnitInv 1`, `coeff dedekindEtaUnitInv 2`,
as small private lemmas and combine them. That is likely the whole job.

## 3. What is different about this topic

**It is the first *proof* layer of this effort.** Both 0a and 0b were definitions,
and the calibration (playbook §7.3) is that transcribing a pinned definition is
cheap — 1 round each — while nothing here has yet measured what a *proof* costs.
Two consequences:

- **The cost model is untested.** The playbook's ~1:1 line ratio came from the
  first port. Do not assume it; measure and report it.
- **This proof has no FLT route to copy.** The port has so far been a
  transcription exercise with mechanical faithfulness checking
  (`spec/check_flt_statements.py`). Here the *statement* still comes from
  base/004, but the proof is ours. So `check_flt_statements.py` will report these
  two declarations as `MISSING IN FLT` — that is expected and correct, not a
  failure. Either add an explicit exemption list to the script (preferred, with a
  comment saying why) or state the lemmas with `-- own proof, no FLT source` and
  adjust the script's sources accordingly.

The shape risks are ordinary: `PowerSeries` coefficient lemmas are explicit
`Finset` sums, so the work is arithmetic, but expect to name a monomorphic helper
or two if a `rw` will not fire (playbook §3.5) — `coeff_pow` and `coeff_invOfUnit`
are the likely spots.

**One structural consequence.** Layer 0's two libraries have been merged into a
single `FLTForHuman` (the definitions and the first port now sit side by side
under one `lean_lib`), so `FLTForHuman/ModularCurve/JqCoefficients.lean` will be
in the **default build target** the moment it is created. Since `lake build` is
expected to stay green, warning-free and `sorry`-free, a half-finished proof must
not land there: do the experimentation in the gitignored `Scratch.lean`, and add
the module (and its `import` in the consumer) only when it is complete. If a
`sorry` is genuinely wanted as a checkpoint, say so explicitly in the report
rather than leaving one in the library.

## 4. Budget

**4 goal rounds, scouting checkpoint at round 1.** This is a proof with an
untested cost model, so the first round should establish feasibility rather than
push for the result: get `pentagonalSeries`'s low coefficients and the
`invOfUnit` recursion working at all, in `Scratch.lean` if easier. If by the end
of round 1 the route is not obviously viable, **stop and report** — the fallback
is to leave Zone C as it is, which costs nothing and is the status quo.

Do not fall back to FLT's modular-forms route: that is the 11k-line subtree this
topic exists to avoid. If mathlib's route fails, the answer is "decline the
topic", not "port the cluster".

## 5. Definition of done

- [x] `coeff_jq_zero` and `coeff_jq_one` proved in
      `FLTForHuman/ModularCurve/JqCoefficients.lean`, with a header recording the source of
      the *statement* (base/004) and the deliberate divergence in the *proof*
      (mathlib's pentagonal route, not FLT's).
- [x] `lake build` green, 0 warnings, no `sorry` — the module now lives in the
      default target, so nothing half-finished lands in it (see §3).
- [x] `#print axioms` on both: only `propext, Classical.choice, Quot.sound`.
- [x] Consumer: the two Zone C `sorry`s replaced by references to the new
      theorems; the file's only remaining `sorry` is the capstone.
- [x] `spec/check_flt_statements.py` still reports 0 mismatches (with the two new
      declarations handled explicitly, not silently).
- [x] `logs/ffg-port.md` gains a short section: measured cost of this topic, the
      proof-cost ratio, and whether the mathlib route held up.
- [x] README module table and PORTING-FFG updated.

## 6. Reporting back

Same format as before. Two things are specifically wanted, because they set the
cost model for anything that follows:

1. **The measured proof cost** — rounds, declarations, lines written, and the
   ratio against the FLT source size of the analogous material. Definitions were
   1 round/68 decls and 1 round/69 decls; this is the first data point for proofs.
2. **Whether the hybrid held** — did mathlib's pentagonal route deliver, or did
   the computation need FLT's cluster after all? Either answer is useful; the
   second would be the first evidence that this cone has no cheap route anywhere,
   which is exactly the kind of thing that should stop the effort.
