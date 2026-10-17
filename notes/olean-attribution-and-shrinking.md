# Attributing and shrinking a `.olean` hog

[lean-build-cost.md](lean-build-cost.md) measures the build *ladder* — when a
build is paid and how to avoid paying it twice. This note is the complementary
procedure for a single module whose `.olean` is too big: how to attribute the
size to a declaration, how to tell the two failure signatures apart, and how to
shrink the proof term without touching a statement. It distils two successful
passes, each with its own topic note:

| module | before | after | the move |
|---|---:|---:|---|
| `Velu/OrderTwo` | 276 MB / 2168 s | 29.3 MiB (30,697,960 B) / 23 s | Vieta factorization of the secant identity, small certificates |
| `Velu/OrderTwoMap` | 568 MB / 728 s | 60.3 MiB / 49 s | shifted coordinates, atomisation, one syntactic certificate |
| `ModularCurve.ModularPolynomialFibreTwo` | 82.4 MiB (86,436,408 B) / 61–73 s | 5.16 MiB (5,413,568 B) / 6.3 s | normalized root triple `(0,a,b)` |

`.olean` sizes are byte-exact for a given source and are the comparison that
holds; the wall times are contended (4-thread tree walls for the "before"
column), so read them as magnitudes only.

Companions: the two refactor home notes,
[../lean/topics/velu/TOPIC-order-two-tangent-direct.md](../lean/topics/velu/TOPIC-order-two-tangent-direct.md)
and
[../lean/topics/modularCurve/TOPIC-fibre-two-coefficient-normalization.md](../lean/topics/modularCurve/TOPIC-fibre-two-coefficient-normalization.md);
the mathematics of the first is
[../math/029-order-two-velu-quotient-and-its-cleared-identities.md](../math/029-order-two-velu-quotient-and-its-cleared-identities.md).

## 1. Why size is the metric

A theorem's `.olean` entry is its type plus its **proof term** — what the kernel
checks and what the file serialises. A module's `.olean` is also the price every
*consumer* pays at import. So when a module takes minutes and hundreds of MB, the
two questions are "which declaration?" and "what in its proof term?".

Wall time is a poor proxy for both: it moves with the job count and with
contention, and the same module has been logged at 728 s and 1070 s in two
4-thread tree builds. Rank by size, confirm by time.

## 2. Finding the candidates

Rank the tree's `.olean`s:

```bash
find lean/.lake/build/lib/lean/FLTForHuman -name '*.olean' -printf '%s %p\n' \
  | sort -rn | head -15
```

A hog is not subtle: it is an order of magnitude or more above the next module
in its own directory (before its pass, `ModularPolynomialFibreTwo` was 82.4 MiB
against 1.6 MiB for the next `ModularCurve` module). The per-module times in the
tree logs name the same modules. A hog that is *expensive in time but not in
size* is a different problem — instance search or a looping `whnf`, treated in
[lean-build-cost.md](lean-build-cost.md) §3 and §8.

## 3. Attributing to a declaration

Copy the module, replace every theorem body by `sorry` except one, compile the
copy, and read the declaration's proof term as the output size minus the
all-`sorry` baseline:

```bash
cd lean
# tmp/ is gitignored; one copy per kept declaration
lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false -o tmp/iso/<name>.olean tmp/iso/<name>.lean
ls -l tmp/iso/<name>.olean        # size - size(all-sorry baseline)
```

With the module and a baseline in hand, a few hours of work becomes a one-line
table. Pitfalls, all of them hit at least once:

* **Replace bodies last-declaration-first.** Each `sorry` changes the line
  numbers of everything after it; applying the edits front-to-back silently
  mangles the next declaration. The same applies to any scripted body
  replacement.
* **`:= by` is not `:=`.** A generated statement that ends in `:=` with tactics
  on the following lines fails as `unknown identifier 'subst'`, not as a parse
  error about the missing `by`.
* **`lake env lean` does not inherit the package's `leanOptions`** — it runs at
  Lean's defaults, not the port's `maxHeartbeats := 4_000_000` and
  `autoImplicit := false`. Pass `-DmaxHeartbeats=4000000
  -DautoImplicit=false` when the module needs them, and set
  `set_option autoImplicit false` in generated scratch files (otherwise an
  undeclared `a`/`b` is silently auto-bound and the probe measures the wrong
  thing).
* **Do not prefix-compile.** A prefix re-elaborates from line 1, so it attributes
  the union of everything before the cut. Isolate declarations instead.
* **The sum over-counts.** Isolated runs share no subterms; three declarations
  that are 12.7 + 31.7 + 40.7 MiB in isolation made an 82.4 MiB module. Use the
  table to find the targets, not to add up to the total.
* **A failed tactic in a probe may be a false statement, not a limitation.**
  Check the probe's statement with a CAS first. A hand-written "cleared" form
  with one misplaced parenthesis (`g0*(…)³` for `(g0*(…))³`) made `ring` fail
  and produced a wrong conclusion about `maxRecDepth`; the corrected statement
  closed in 9 s.

For *time* attribution (which declaration burns the seconds), `set_option
profiler true` plus the `[Elab.command]` lines is the other half of the
picture; in this port the interesting column is often `typeclass inference`.

## 4. The two failure signatures

**Certificate hogs.** The proof is a `linear_combination` whose arguments are
long explicit polynomials. The *certificate text* may be modest; the cost is
that the arguments go **into the proof term**. Symptoms: a source line of a few
kB, an isolated size of tens of MB, and `linear_combination (norm := skip)` plus
`trace_state` printing a residual that is a small polynomial identity. The fix
is a different, smaller certificate — or a different proof (the Vélu passes
replaced one 28,925-character certificate by two 19-term ones, and a
three-branch elimination by a Vieta factorization).

**Expansion hogs.** The proof is `field_simp; ring` and the statement is a
rational identity in several variables. Symptoms: a small statement, no
`linear_combination`, and a proof term whose size tracks the *expanded*
polynomial — `ring` proves the cleared identity by constructing its expansion.
`ModularPolynomialFibreTwo` was three of these: 12.7 / 31.7 / 40.7 MiB for
cleared degrees 12 / 24 / 36 in three variables.

The signatures need different moves. For a certificate hog the lever is the
certificate (few terms, short statements); for an expansion hog it is the
*coordinates*. Both obey one rule: the proof term is proportional to the number
of monomials the normaliser must walk, and a certificate of ≤ 20 terms is
milliseconds while hundreds of monomials is megabytes.

## 5. Shrinking: the normalization move

For an expansion hog, ask what the identity is invariant under **before**
touching the proof.

1. **Find the invariance.** In `ModularPolynomialFibreTwo` every ingredient —
   $`c_4`$, $`\Delta`$, the $`g_i`$ and the $`d_i`$ — is built from differences
   of the three roots, so the identities are unchanged by
   $`x_i \mapsto x_i + t`$. In the Vélu work the analogous move is putting the
   2-torsion point at the origin.
2. **Prefer the representative that needs no division.** The centroid
   $`x_i - e_1/3`$ is the natural normalization, but it divides by 3 and the
   module assumes only $`(2 : K) \ne 0`$; characteristic 3 is a real case.
   Shifting by $`x_0`$ is division-free, sound in every characteristic, and was
   in fact smaller (13/17/25 monomials per side against 13/25/37).
3. **Restate the helper lemmas in the normalized coordinates** and transport the
   general hypotheses in the consumer with small `ring`s. In
   `ModularPolynomialFibreTwo` that is eleven one-line transports in `main`; the
   helpers went from 85 MiB to 4.3 MiB and the transports cost well under 1 MiB.
4. **Keep the big polynomial out of the statements.** A helper's *type* is
   elaborated and serialised like its proof; a lemma that restates the expanded
   form pays for it twice. Use `let`-bound or free variables in the statement
   when the expanded form is the problem.
5. **Keep the new `ring`s small.** The transports are low-degree identities in
   the consumer; if one needs the expanded form, the normalization is wrong.
   (When the hog is a `linear_combination` instead, the certificate rule
   applies: twenty terms or fewer, and a local `maxHeartbeats 200000` as a
   regression guard.)

## 6. Verify, measure, document

* **Before the Lean edit, verify the algebra in a CAS.** `sympy` confirmed the
  three normalized identities, the transport identities, the relation
  $`\Delta = g_i^2\,d_i`$ and the partial-fraction sums
  $`\sum_i x_i^k/g_i = 1, 0, 0`$ for $`k = 2, 1, 0`$. This
  is also how you find the invariance in step 1.
* **Measure the landed module the way you measured the hog**: a clean
  `lake env lean -DmaxHeartbeats=4000000 -o` for the size, then
  `lake build <module>` for the build. Only a *module* build — the tree build is
  the manager's / needs permission.
* **Run `spec/check_flt_statements.py`.** The refactors only touch `private`
  helpers, so the expected report is unchanged `identical` with **0 mismatched,
  0 missing**; the public headline's statement is byte-identical to its pin
  wrapper.
* **Target 0 warnings** in the module, and record the before/after pairs.
* **Write the topic note**, in the module's topic directory, with the
  measurement, the mechanism, the landed change and the verification. Keep the
  probes under `lean/tmp/` (untracked) for review; delete the generated copies,
  which are large.

## 7. Size and readability

A proof term is the *proof*, serialised. A declaration whose proof term is a 4 kB
`linear_combination` of monomials is unreadable even when correct: a human cannot
check it, a reviewer cannot see what it means, and the next refactor cannot find
the crux. So size is not only a build metric — **it is a proxy for whether the
mathematics in the proof can be read**. Three working rules follow from the two
passes:

* **Name the relations.** A certificate over `hP`, `hQ`, `hgy` says nothing about
  what it proves. A certificate over a *named* shifted-curve equation, a named
  2-division root relation, and `b_relation` reads as a sentence.
* **Factor the coefficients.** `4u²(u²-G)²`, `4u⁶` and
  `4a₁u⁵G - 4u⁴(u²-G)v` are checkable at a glance; the same identity written as
  three monomial lists is not. Factor the certificate in a CAS before writing it.
* **A readable rewrite need not shrink the term much.** `OrderTwo.lean`'s
  `velu2_equation_cleared_four` went from three monomial monoliths to a 3-term
  factored certificate plus one named hypothesis, and its isolated size fell only
  14.9 → 12.6 MiB, because `ring` still normalises the same 3-variable identity.
  The readability gain is in the *declaration*; the size gain came from the
  coordinate change (§5), not from editing the certificate. If the goal is size,
  change the coordinates; if the goal is comprehension, name and factor.

**Some certificates cannot be reduced, and that is worth recording.** `OrderTwo`'s
`Delta_eq_veluGx_sq_mul_velu2QuadDisc` and `veluQuotient2_Delta_eq` state the
2-division cofactor factorization `Δ = G x² · velu2QuadDisc`. A compact
certificate would use the 2-division root relation and `b_relation`
(`4 b₈ = b₂ b₆ - b₄²`); the coefficient of `b₈` is `-b₂²`, so `b_relation` enters
with `-b₂²/4` — a division by 4 that the statements' `CommRing` does not allow.
Expanding `b₈` (`simp only [..., b₈, ...]`) is therefore forced, and the
certificate must also use the curve equation. Both identities keep their ported
certificates, with a `-- Reading.` comment giving the factorization; the
obstruction, not a smaller certificate, is the thing to write down.

## 8. Checklist

1. Rank `.olean`s; pick the outlier.
2. Isolate per declaration (`-o` copies, last-first replacement, heartbeat and
   autoImplicit flags).
3. Classify: certificate hog (`linear_combination`) or expansion hog
   (`field_simp; ring`).
4. For an expansion hog, find the invariance and a division-free representative;
   restate the helpers there and transport in the consumer.
5. Verify the algebra in a CAS; land; measure size and time; run the statement
   checker; 0 warnings.
6. Write the topic note and record the numbers.
7. For a **readability** pass (which is not the same as a size pass): factor the
   certificate coefficients in a CAS, name every relation the certificate uses,
   and record any certificate that cannot be reduced together with the
   obstruction that blocks it.
