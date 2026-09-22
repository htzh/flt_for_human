# Topic: the interface tier

**Status: done (2026-09-21), 1 goal round of 2.** The nine interface lemmas are
public in `Defs/Laurent.lean` (4) and `Defs/Jq.lean` (5), every statement verified
against its pin wrapper; `Spine.lean` is down to 25 declarations with `Inputs` at
**8** fields and no `h : Inputs` on the `ψ` helpers; `lake build` is green, 0
warnings, no `sorry`; `#print axioms functionFieldGeneration_of` is clean; the
checker reports **146 identical, 0 mismatched, 0 missing** with `OWN_PROOFS`
unchanged; the consumer is unchanged at 0 errors / one `sorry`. Exposure was
**free** — every lemma transcribed on the first try, the only wrinkle being that
the pin carries `coeffEmb_qExpand` twice (wrapper with explicit `L`, `W1` copy
with implicit `K`). The interface table and measured cost are in
[logs/ffg-port.md](logs/ffg-port.md) §2e; the nine carry **520 of the cone's 946**
≥5-indegree tier (55%).

**Audience.** A fresh session taking the third topic of the
`functionFieldGeneration` effort. Layer 0, the `jq`-coefficients topic and the
conditional capstone are done ([logs/ffg-port.md](logs/ffg-port.md) §0). Read
[PORTING-FFG.md](PORTING-FFG.md) §2 and §2.1 once — the second measures why this
topic exists — and [porting-playbook.md](porting-playbook.md) §3–§5 and §7 for
the method. The two surveys in [studies/](../studies/) are the background:
[flt-ffg-field-theory.md](../studies/flt-ffg-field-theory.md) §0.1 and §8.

**Goal.** Add the cone's **outbound interface** to the port — the declarations
the rest of FLT reaches this segment through — as public lemmas placed with the
objects they concern, and use two of them to shrink the capstone's `Inputs`
from 10 fields to 8.

## 1. Why this topic, and what is settled

The cone is the floor of FLT's arithmetic tower: **70 nodes**, **5,804 transitive
dependents** (19.7% of the repository), and the traffic flows not through the
headline theorem but through a handful of small declarations
([logs/ffg-port.md](logs/ffg-port.md) §8.5). The port today transcribes the
*definitions* those declarations are stated over and exposes almost none of them —
and the single most-shared declaration in the whole cone, `coeffMap_qExpand`
(indeg **194**), is `private` inside `Spine.lean`.

So this is where the effort's own cost model says to go: the work is
reorganization guided by outbound dependencies, not porting, and the interface is
what a fifth of FLT actually consumes. It is also where the two selection
criteria coincide — two of these lemmas are simultaneously high-indegree interface
nodes and assumed `Inputs` fields, so porting them removes debt *and* exposes an
interface.

- **Settled: the interface is public and lives with its object.** Lemma placement
  follows this port's existing principle ("a module is a mathematical role"):
  `coeffMap`/`coeffEmb` facts go in `Defs/Laurent.lean` beside those maps,
  `dedekindPsi` and `jq` facts in `Defs/Jq.lean`. The *interface* is a usage
  property, not a mathematical role, so it is recorded as a table in the log
  rather than as a directory. (A dedicated `Interface.lean` is the deliberate
  alternative; it was rejected because it would separate each lemma from the
  object it is about.)
- **Settled: statements are FLT's, verbatim.** Every declaration below has a
  6-line `Thm_ModularCurve_*` wrapper in the pin, so the checker can *verify*
  these rather than exempt them — see §5.
- **Settled: the two `Inputs` fields are discharged, not restated.** After
  `dedekindPsi_mul_of_coprime` and `dedekindPsi_prime_pow` are proved, they are
  removed from `Spine.lean`'s `Inputs` (10 → 8) and the three ψ helpers there
  (`dedekindPsi_prime'`, `dedekindPsi_mul_prime_not_dvd`,
  `dedekindPsi_mul_prime_dvd`) lose their `h : Inputs` parameter.
- **Settled: one thing is deliberately not ported.**
  `S_ModularCurve_dedekindPsi_mul_of_coprime.lean` is 471 lines, but its ψ part
  is lines 23–72 and the remaining ~399 are a resultant/elimination development
  for `nonempty_modularPolynomialData_mul_of_coprime`, which is **not a graph
  node** and is off the capstone path. Port the ψ section; skip the rest. This is
  the reorganization the topic is for.

## 2. The scouted inventory — all of it, with indegrees

Every proof is small and self-contained. "cites 0" means the FLT node depends on
no FLT theorem.

| declaration | indeg | FLT proof file (lines) | deps | target module |
|---|---|---|---|---|
| `coeffMap_qExpand` | **194** | `S_ModularCurve_coeffMap_qExpand` (15) | none — **already proved in `Spine.lean`, but `private`** | `Defs/Laurent.lean` |
| `dedekindPsi_prime` | 72 | `S_ModularCurve_dedekindPsi_prime` (13) | none (cites 0) | `Defs/Jq.lean` |
| `coeffEmb_qExpand` | 66 | `S_ModularCurve_coeffEmb_qExpand` (5) | `coeffMap_qExpand` | `Defs/Laurent.lean` |
| `transcendental_jq` | 56 | `S_ModularCurve_transcendental_jq` (13) | `aeval_jq_eq_zero` | `Defs/Jq.lean` |
| `dedekindPsi_mul_of_coprime` | 46 | `S_…_dedekindPsi_mul_of_coprime` 23–72 | mathlib `ArithmeticFunction` | `Defs/Jq.lean` |
| `dedekindPsi_prime_pow` | 33 | `S_ModularCurve_dedekindPsi_prime_pow` (38) | none (cites 0) | `Defs/Jq.lean` |
| `coeffMap_injective` | 32 | `S_ModularCurve_coeffMap_injective` (10) | `coeffMap_coeff` (ours) | `Defs/Laurent.lean` |
| `coeffEmb_injective` | 19 | `S_ModularCurve_coeffEmb_injective` (9) | `coeffMap_injective` | `Defs/Laurent.lean` |
| `aeval_jq_eq_zero` | 2 | `S_ModularCurve_aeval_jq_eq_zero` (28) | none (cites 0) | `Defs/Jq.lean` |

Sum of the indegrees: **520**. Nine declarations, ~150 lines of proof, of which
two are already written.

The statements, from the pin's wrappers (transcribe verbatim):

```lean
theorem coeffMap_qExpand {R S} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n]
    (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x)
theorem coeffEmb_qExpand (L) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x)
theorem coeffMap_injective {R S} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : Function.Injective f) : Function.Injective (coeffMap f)
theorem coeffEmb_injective (L) [Field L] [Algebra ℚ L] : Function.Injective (coeffEmb L)
theorem dedekindPsi_prime {p : ℕ} (hp : p.Prime) : dedekindPsi p = p + 1
theorem dedekindPsi_prime_pow (p k : ℕ) (hp : p.Prime) (hk : k ≠ 0) :
    dedekindPsi (p ^ k) = p ^ k + p ^ (k - 1)
theorem dedekindPsi_mul_of_coprime (M N : ℕ) (h : Nat.Coprime M N) :
    dedekindPsi (M * N) = dedekindPsi M * dedekindPsi N
theorem aeval_jq_eq_zero {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0
theorem transcendental_jq : Transcendental ℚ jq
```

Route notes, so none of this has to be rediscovered:

- `coeffMap_qExpand` proves by `ext k` and the two cases `(n : ℤ) ∣ k` / not, using
  our `coeffMap_coeff`, `qExpand_coeff_mul`, `qExpand_coeff_of_not_dvd`. That is
  exactly what the private copy in `Spine.lean` already does — **move it, do not
  rewrite it**.
- `coeffEmb_qExpand` is `coeffMap_qExpand _ n x`.
- `coeffMap_injective`: `ext k`, then `hf` on the `k`-th coefficients.
- `coeffEmb_injective`: `coeffMap_injective (FaithfulSMul.algebraMap_injective ℚ L)`.
- `dedekindPsi_prime`: `rw [dedekindPsi, Finset.sum_filter, hp.divisors,
  Finset.sum_pair hp.one_lt.ne]; simp [hp.squarefree, Nat.div_self hp.pos]`.
- `dedekindPsi_prime_pow`: self-contained; needs `Nat.dvd_prime_pow`, a
  `Squarefree (p ^ j) ↔ j ≤ 1` helper, `interval_cases`, and the divisor filter
  collapsing to `{1, p}`. Import `Mathlib.Tactic.IntervalCases`.
- `dedekindPsi_mul_of_coprime`: goes through `ArithmeticFunction`. Define the
  squarefree indicator, show `dedekindPsi N = (squarefreeIndicator *
  ArithmeticFunction.id) N`, and use `IsMultiplicative.map_mul_of_coprime`.
  Import `Mathlib.NumberTheory.ArithmeticFunction.Misc`. The pin also carries
  `le_dedekindPsi` and `dedekindPsi_pos` in the same section — port them only if
  something needs them.
- `aeval_jq_eq_zero` and `transcendental_jq`: 28 + 13 lines in the pin;
  `transcendental_jq` is `transcendental_iff.mpr fun _ hp => aeval_jq_eq_zero hp`.
  Note `aeval_jq_eq_zero` is stated over `Polynomial ℚ`, not our `evalAtJ`
  (`Polynomial ℤ`); keep the pin's form.

## 3. What is different about this topic

- **Most of it is exposure, not proof.** Two of the nine already compile in
  `Spine.lean`; the rest are 9–38 lines each. Expect it to be the cheapest topic
  so far, and if it is not, that is itself the finding.
- **It edits a `private` block that a verified artifact depends on.**
  `Spine.lean` uses `coeffMap_qExpand`/`coeffEmb_qExpand` in `iota_jqN` and in
  `root_shape`. Moving them out means `Spine.lean` imports them; check those two
  proofs still elaborate, and that `Spine`'s `Inputs`-parameterised ψ helpers are
  simplified to the real lemmas without changing any other field.
- **The placement decision is the interesting one.** The interface is a *usage*
  property; the modules are named for *mathematical roles*. Keep the roles (that
  is why `Defs/Laurent.lean` and `Defs/Jq.lean` get the lemmas) and record the
  interface as a table — don't invent an `Interface.lean` and split lemmas from
  their objects.
- **The checker flips from exempting to verifying.** These nine have pin
  wrappers, so add the nine `Theorems/Thm_ModularCurve_*.lean` files to
  `SOURCES`, and *remove* `coeffMap_qExpand`/`coeffEmb_qExpand` from needing any
  special treatment (they were never exempted — they were `private`, so the
  checker never saw them; it will now, and it will verify them).

## 4. Budget

**2 goal rounds, checkpoint at 1.** One round has covered 68, 69, 24 and 29
declarations respectively; nine declarations with two already written should fit
in one. Two is the "something structural is wrong" threshold, not the
expectation.

**Stop early on**: a statement that will not match its pin wrapper (record the
divergence rather than weakening it); `dedekindPsi_mul_of_coprime` needing
anything from the off-path resultant section; or `Spine.lean`'s proofs breaking
in a way that needs the `Inputs` type to change rather than shrink.

## 5. Definition of done

- [x] The nine declarations public in `Defs/Laurent.lean` (4) and `Defs/Jq.lean`
      (5), statements verbatim from the pin, headers/docstrings naming what each
      transports.
- [x] `Spine.lean`: `Inputs` down to **8** fields (`dedekindPsi_mul_of_coprime`,
      `dedekindPsi_prime_pow` removed), the three ψ helpers no longer take
      `h : Inputs`, and the two moved lemmas imported rather than redeclared.
- [x] `lake build` green, 0 warnings, no `sorry`.
- [x] `#print axioms` on `functionFieldGeneration_of` still only `propext,
      Classical.choice, Quot.sound`.
- [x] `spec/check_flt_statements.py`: the nine wrappers added to `SOURCES`, the
      verified count up (137 → 146), `OWN_PROOFS` unchanged, 0 mismatched.
- [x] Consumer unchanged except its count prose if it states one (it should still
      be 0 errors, one `sorry`).
- [x] `logs/ffg-port.md` gains a §2e (cost) and an **interface table**:
      declaration → indegree → module, with the measured indegrees above, as the
      topic's payload. The `Inputs` field table in §8.4 updated 10 → 8 with the
      two removed rows marked discharged.
- [x] README module table and PORTING-FFG status updated.

## 6. Reporting back

Same shape as the previous topics. Two things specifically:

1. **The interface table**, with indegrees re-derived rather than copied, and the
   claim checked that the port now exposes most of the cone's outbound indegree
   mass (520 of what the cone's ≥5-indegree tier sums to).
2. **Whether exposure was free.** Every one of these lemmas was already in the
   pin at ≤38 lines; if any turned out to need real work, say which — that
   distinguishes "the interface is small" from "the interface looked small and
   wasn't", and it is the evidence the next topic's pricing depends on.
