# The order-two tangent identity, proved directly — the `Velu/OrderTwo` hog

**Status: both `OrderTwo` identities are refactored and landed (2026-10-16; the
secant one re-proved by a Vieta argument in the follow-up), and all four heavy
alignments of `OrderTwoMap` — `kw_velu2_tanY_SI2c`, `kw_velu2_secX_align`,
`kw_velu2_secY_negAddY_align` and `kw_velu2_tanX_align` — are rewritten and
landed (§9).** The proofs of
`velu2_tangent_negAddY_cleared_identity` and
`velu2_secant_negAddY_cleared_identity` no longer contain large certificates: the
tangent one is a two-branch argument (largest polynomial 19 terms), and the secant
one is now a *single* Vieta argument with no case split at all. Measured in
`Velu/OrderTwo.lean`: `.olean` **276 MB → 29.3 MiB**, module build
**2168 s → 23 s**; `Velu/OrderTwoMap.lean`: **391.2 MiB → 60.3 MiB** and
**459 s → 49 s** (§9). This note
records (i) the measurement that found the hog, (ii) why the ported proof is
catastrophic, (iii) the refactored proofs and their small certificates, and
(iv) exactly what is left. Pin `anthropics/fermats-last-theorem@aa2d8b3`;
mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §3.5 (build ladder), §4
(faithfulness — statements fixed, proofs adapted).

Companions:

- [../logs/](../../logs/) — the campaign logs; this note's `tools/deps/warnings/`
  scripts were the warning sweep's tooling.
- [../../notes/lean-build-cost.md](../../../notes/lean-build-cost.md) — the
  measurement note this session's 4-thread build extends.
- The mathematics of the quotient is in the `S_`/`Definitions` pair below; the
  port-side inventory is [TOPIC-H2-engine.md](TOPIC-H2-engine.md) and
  [TOPIC-V1-ready-columns.md](TOPIC-V1-ready-columns.md).

## 1. The measurement that found it

A full tree build at four jobs — `LEAN_NUM_THREADS=4 lake build` (Lake 5 has no
`-j`; the Lean runtime pool is the knob) — ran in **3290.5 s wall / 9256.6 s USER /
2103.6 s SYS**, i.e. 3.45 of 4 threads busy, and rebuilt 596 modules. The
per-module ranking it produced has two entries that no earlier log contained:

| module | build | `.olean` |
|---|---:|---:|
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwo` | **2168 s** | **263 MB** |
| `FLTForHuman.WeierstrassCurve.Velu.OrderTwoMap` | **728 s** | **568 MB** |
| next (`WeightOne.Gamma1Basis`) | 171 s | 7.6 MB |

`OrderTwoMap` imports `OrderTwo`, so the pair is a **serial 48-minute chain
inside a 55-minute build**; the port's 1.1 GB of oleans is 831 MB of it. The
`tmp/tree_build_500k.log` this work started from does not mention either module —
its head is truncated, so the log that motivated the whole exercise never showed
the real hogs. Per-module wall in the 500k run was inflated 8–60× over the
4-thread run.

## 2. Why the ported proof costs 36 minutes

The declaration is
`WeierstrassCurve.velu2_tangent_negAddY_cleared_identity`
([OrderTwo.lean:359](../../FLTForHuman/WeierstrassCurve/Velu/OrderTwo.lean#L359)),
transcribed from the pin's

- `Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`
  (`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/Theorems/Thm_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`)
- `P2M/Sol/S_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`
  (`https://raw.githubusercontent.com/anthropics/fermats-last-theorem/aa2d8b3/P2M/Sol/S_WeierstrassCurve_velu2_tangent_negAddY_cleared_identity.lean`)

Only the *statement* is pinned (and it is untouched by this work, so
`spec/check_flt_statements.py` is unaffected). The *proof* is a hand-written
`linear_combination` whose arguments are enormous polynomials written out
monomial by monomial — the largest single argument runs to tens of thousands of
characters, and the pin itself needs `set_option maxHeartbeats 16000000` and
`maxRecDepth 8000` for it. `linear_combination` puts those arguments **into the
proof term**, and the term is what the kernel checks and what the `.olean`
serialises: hence 36 minutes and 263 MB. Measured decomposition on a scratch copy:

| step | wall |
|---|---:|
| the port's preprocessing (`rw`, `simp only`, `field_simp`) | 3.9 s |
| `ring1` on the cleared goal alone (fails: the hypotheses are needed) | 71 s |
| elaborating just the three certificate coefficients | >235 s (timed out) |

`polyrith` is not an option — it "relied on an external service that has been
shut down" — and `nlinarith` fails in 4 s. The fix has to be a *different proof*,
not a better search.

**Where the time actually goes (measured 2026-10-16).** For the 2 kB direct
certificate, `set_option profiler true` reports `ring 300ms` but **typeclass
inference 19–32 s**: elaborating an explicit polynomial that long over a
`Field` variable is the cost, not the search. That is why the same identity
blows a 200,000-heartbeat budget while passing the port's `maxHeartbeats
4000000`, and it also explains why shrinking the certificate (rather than
removing it) is the only lever. `[CommRing F]` still costs 19 s;
`[CommSemiring F]` drops to 5 s but cannot express subtraction. A certificate
of ≤ 20 terms elaborates in milliseconds.

## 3. The direct proof (what the certificate was doing)

Shift to the 2-torsion point `Q = (x₀, y₀)`: $`u = x - x_0`$, $`v = y - y_0`$,
$`\beta = a_2 + 3x_0`$, $`G = \mathrm{veluGx}\ x_0\ y_0`$
([Defs.lean:38](../../FLTForHuman/WeierstrassCurve/Velu/Defs.lean#L38)), and let
$`D = 2v + a_1u`$ (this is `y - negY x y`, nonzero by `hy`).

**1. The curve, shifted.** Using `hQ` ($`Q`$ on the curve) and `hord`
($`2y_0 + a_1x_0 + a_3 = 0`$, the 2-torsion condition), the Weierstrass equation
becomes, for $`(u,v)`$ on the curve,

$$v^2 + a_1 u v \;=\; u^3 + \beta u^2 + G u .$$

**2. Every chord through `Q` has the same root product.** Substituting the line
$`v = mu`$ into that cubic gives

$$u \cdot \bigl(u^2 + (\beta - m^2 - a_1 m)u + G\bigr) = 0,$$

so for *any* line through `Q`, the parameters of its two other intersections have
sum $`m^2 + a_1m - \beta`$ and **product $`G`$**. That is the whole geometric
content of `veluGx x₀ y₀` in this file.

**3. What the statement says.** Writing $`m = v/u`$ for the slope of the chord
from `Q` to `P` and $`m_R = v_R/u_R`$ for the chord from `Q` to $`-2P`$ (where
$`(u_R, v_R)`$ is the double, i.e. `addX`/`negAddY` of the tangent at `P`), the
theorem's left-hand side is *identically*

$$T \;=\; u \, u_R \, \bigl[u^2 (a_1 + m + m_R) \;-\; u\,u_R\,(a_1 + 2m) \;+\; G\,(m - m_R)\bigr].$$

This is the relation between the slope from `Q` to `P` and the slope from `Q` to
its double — the chord–tangent compatibility that `OrderTwoMap`'s conceptual
lemmas (`kw_velu2X_addKernel`, `kw_velu2X_eq_iff`, …) then build on. It is degree 4
in four quantities; the pin's certificate is a brute-force expansion of it in raw
monomials of `x, y, x₀, y₀`, and the coefficient of the *linear* hypothesis `hord`
is the largest of the three, which is pure slack — the representation is wildly
non-unique.

## 4. The certificate, refactored into two small branches

With $`E = 3u^2 + 2\beta u + G - a_1 v`$, $`D = 2v + a_1u`$,
$`g_2 = m_P D - E`$ and $`F = 2E + a_1D = (2m_P+a_1)D - 2g_2`$, the first cut at
the direct proof needed

$$T \cdot D^3 \;=\; C_1 \cdot \text{curve} \;+\; q \cdot g_2$$

with a 570-character $`C_1`$ and a 1532-character, **irreducible** $`q`$. That
identity is true, but `q` does not factor and cannot be shrunk, and elaborating
it costs the 19–32 s of typeclass inference measured in §2 — so it satisfies no
200,000-heartbeat budget even though its `ring` is 300 ms.

The landed proof avoids it. Three facts do the work:

- $`(2m_P+a_1) \cdot D = F + 2g_2`$, so $`F \ne 0 \iff 2m_P+a_1 \ne 0`$, since
  $`D \ne 0`$ by `hy` + `hord`;
- **branch $`F \ne 0`$**, one small certificate with $`u_R = m_P^2 + a_1m_P - \beta - 2u`$,
  $`S = -2v(2m_P+a_1) + g_2 - a_1u(2m_P+a_1)`$ and $`B`$ the $`v`$-coefficient of
  $`T`$ (12 terms):

  $$T\,(2m_P+a_1) \;=\; -(u-u_R)\bigl((2m_P+a_1)^2\,\text{curve} + S\,g_2\bigr) \;+\; B\,g_2 ,$$

  whence $`T(2m_P+a_1)=0`$ and $`T=0`$;
- **branch $`F = 0`$, where $`2m_P+a_1=0`$**: the integer certificate
  $`2^5\,T = P_1 F + 2Q\,(2m_P+a_1)`$ with $`P_1`$ 4 terms and $`Q`$ 19 terms.
  If $`2 = 0`$ then $`F = a_1D \ne 0`$, contradicting the branch, so $`2 \ne 0`$
  and $`2^5T = 0`$ gives $`T = 0`$.

The largest polynomial in the whole proof has 19 terms; the powers of two clear
the halves of the elimination, so no division is ever introduced and the
argument is valid in every characteristic. The first certificate is literally
"reduce $`T`$ by the curve, then use $`m_P = E/D`$"; the second is the
elimination of $`m_P`$ and $`G`$ by $`2m_P+a_1`$ and $`F`$.

## 4′. The secant identity, re-proved by Vieta

§6.1's three-branch secant proof was itself replaced by the following, which has
no case split. Write the chord through $`P_1,P_2`$ as $`v = mu+c`$, so that
$`c = v_1-mu_1 = v_2-mu_2`$ is its intercept and $`u_R = c+mu_R`$ is the third
intersection. Substituting $`v = mu+c`$ into the shifted curve
$`v^2+a_1uv = u^3+\beta u^2+Gu`$ gives the cubic

$$u^3 - (m^2+a_1m-\beta)u^2 + \bigl(G-c(2m+a_1)\bigr)u - c^2 ,$$

whose roots are exactly $`u_1,u_2,u_R`$. Hence the Vieta relations

$$u_1u_2+u_1u_R+u_2u_R \\;=\\; G-c(2m+a_1),\qquad u_1u_2u_R \\;=\\; c^2 .$$

The statement is *identically* (with $`u_R`$ a free variable!)

$$T_{\text{sec}} \\;=\\; (u_2-u_R)\Bigl[c\\,(\sigma_2-G) + (2m+a_1)\\,u_1u_2u_R\Bigr],
\qquad \sigma_2 := u_1u_2+u_1u_R+u_2u_R ,$$

and its bracket is $`c\,(\sigma_2-G+c(2m+a_1))+(2m+a_1)(u_1u_2u_R-c^2)`$, killable
by the two Vieta relations. In Lean those two relations are certified from the
two shifted curve equations alone: writing $`c_1,c_2`$ for them and
$`v_2 = v_1-md`$ for the slope relation,

$$d\\,\bigl(\sigma_2-G+c(2m+a_1)\bigr) \\;=\\; c_1-c_2,\qquad
u_1u_2u_R-c^2 \\;=\\; u_1\bigl(\sigma_2-G+c(2m+a_1)\bigr)-c_1 ,$$

so $`d \ne 0`$ gives $`\sigma_2-G = -c(2m+a_1)`$ and $`u_1u_2u_R = c^2`$, the
bracket vanishes and $`T_{\text{sec}} = 0`$ in every characteristic. The whole
proof is two private lemmas: `secant_factor` (the factorization, a ring identity
on free variables) and `velu_secant_core`. The nine lemmas of the branch proof,
and its characteristic-$`2`$ corner, disappear.

## 5. Verification and measurements (2026-10-16)

- **Symbolic check**: `tools/deps/warnings/velu_refactor_check.py` re-derives
  and asserts every identity used by the refactored proof — the shifted curve
  from `hP - hQ - (y - y₀) * hord`, the equality "statement LHS $`= T`$", both
  branch certificates, and $`(2m_P+a_1)D = F + 2g_2`$. It passes, with term
  counts $`B = 12`$, $`S = 6`$, $`P_1 = 4`$, $`Q = 19`$.
- **Lean**: `velu_tangent_core` and the rewired theorem compile with
  `set_option maxHeartbeats 200000` and `maxRecDepth 8000`; the whole file
  elaborates in 6.8 s wall including the `Velu/Defs` import (the declaration
  itself is well under a second). The old 28,925-character `linear_combination`
  argument is gone.
- **Module**: `lake build FLTForHuman.WeierstrassCurve.Velu.OrderTwo`
  **55 s**, `.olean` **68 MB** (was 2168 s / 276 MB). The module now succeeds
  under the port's global cap and under a 200 K local cap.
- The residual 68 MB / 55 s was the **secant** certificate, then still the ported
  one.
- **Second pass (secant, Vieta).** The three-branch secant refactor of §6.1 was
  replaced by the Vieta proof of §4′: the statement factors as
  $`T_{\text{sec}} = (u_2-u_R)\bigl(c(\sigma_2-G)+(2m+a_1)u_1u_2u_R\bigr)`$ with
  $`c = v_1-mu_1`$ and $`\sigma_2 = u_1u_2+u_1u_R+u_2u_R`$, and the two Vieta
  relations $`\sigma_2-G = -c(2m+a_1)`$, $`u_1u_2u_R = c^2`$ are certified from the
  two *shifted curve equations* alone. The nine private lemmas of the branch
  proof collapse to two (`secant_factor`, `velu_secant_core`), and no
  characteristic hypothesis or case split survives. Measured:
  `.olean` **45.8 MB → 29.3 MiB**, module build **69 s → 23 s**, and the
  profiler's typeclass inference **62.9 s → 5.4 s** (single-threaded
  `lake env lean`: 60.8 s → 16.6 s). Statement check unchanged (9791 identical).
- **Where the remaining 29.3 MiB is.** A prefix build of the module attributes it
  to `velu2_equation_cleared_four` (≈ 16 MB; line 150 prefix alone is 16.1 MB /
  15 s), then `veluQuotient2_Delta_eq` (≈ 4.7 MB) and
  `Delta_eq_veluGx_sq_mul_velu2QuadDisc` (≈ 2.5 MB). Those three still carry
  ported certificates and are the next candidates; the two `negAddY` identities
  now cost almost nothing.

## 6. What is left

1. **The secant identity — landed, then superseded by §4′.** The first refactor
   (kept here for the record) used three small certificates in shifted coordinates
   instead of the ported 14,355-character `linear_combination` (four arguments of
   6,783 / 3,189 / 2,830 / 1,553 characters), split on $`A := d(a_1+2m)`$:
   - branch $`A \ne 0`$: $`d\,A\,T = \alpha_1c_1+\alpha_2c_2+\alpha_3g_2`$;
   - branch $`A = 0`$, $`2 \ne 0`$: $`32\,d\,T^{(s)} = 4B\,P_2 + M\,(2m+a_1)`$;
   - characteristic 2 (where $`A = d\,a_1`$, so the case is $`a_1 = 0`$): the
     mod-2 certificate $`d\,T = \mu_0g_2+\mu_2\hat R+2E+a_1F`$, whose essential
     factor is the unit $`d = u_1-u_2 \ne 0`$.
   Measured: certificate text 14,355 → 7,066 chars; proof term 40.4 → 15.3 MB;
   `OrderTwo.olean` 67.3 → 45.8 MB. But the module build went 55 → 69 s: the cost
   was in the *nine* private lemmas, each restating the expanded $`T_{\text{sec}}`$.
   The Vieta proof of §4′ replaced all of them by two short-statement lemmas, at
   **29.3 MiB / 23 s**. Statements unchanged throughout
   (`spec/check_flt_statements.py`: 9791 identical).
2. **`Velu/OrderTwoMap` (596 MB, 728 s) — target (c) landed; (a), (b)
   diagnosed.** Attribution by prefix compiles with `-o`, each inside the
   2-minute cap. The original ladder:

   | prefix end | `.olean` | wall |
   |---|---:|---:|
   | line 352 (`AddKernel`) | 1.2 MB | 5.8 s |
   | line 635 (`SecantCarrier`) | 19.2 MB | 21 s |
   | line 771 (`SecantConjunctOne`) | 19.7 MB | 23 s |
   | line 820 (`SecantAlign: kw_velu2_secX_align`) | — | **> 120 s** |
   | same, with that theorem's `linear_combination` replaced by `sorry` | 19.9 MB | **33 s** |

   and the same ladder re-taken after (c) (line numbers shifted by +25):

   | prefix end | `.olean` | wall |
   |---|---:|---:|
   | line 489 (`TangentYContent`, holds `kw_velu2_tanY_SI2c`) | **4.36 MB** | **6.0 s** (was 19.08 MB / 17.6 s) |
   | line 670 (`SecantCarrier`) | 5.47 MB | 7.7 s |
   | line 806 (`SecantConjunctOne`) | 5.91 MB | 7.8 s |
   | line 867 (`kw_velu2_secX_align`) | **20.6 MB** | **18.4 s** (was > 170 s) |
   | line 919 (`kw_velu2_secY_negAddY_align`) | 88.1 MB | 75.2 s |

   **(c) `kw_velu2_tanY_SI2c` — landed.** Its statement is unchanged; its 4.8 kB
   raw-monomial certificate is replaced by a port-local helper
   `tanY_SI2c_shifted`, a **nine-term** multiple of the shifted curve, plus four
   short `ring` rewrites that put the raw statement into shifted form so the
   helper applies definitionally (the technique of §4′). The declaration alone
   went 15.89 MB / 15.1 s to **1.21 MB / ~1.3 s**; the module prefix through it
   went 19.08 MB / 17.6 s to 4.36 MB / 6.0 s. Re-checked by
   `tools/deps/warnings/velu_map_check.py`.

   **(a) `kw_velu2_secX_align` — landed.** The pin's certificate is *syntactic*:
   it verifies only while `x₁-x₀`, `x₂-x₀`, `x₁-x₂`, `veluGx` are the literal
   subterms, which is why every attempt to atomise the goal (and every attempt to
   `set` instead of `generalize`) either failed the ring check or unfolded the
   local definitions and stayed slow. `generalize … at *` names the four
   subterms `u₁,u₂,d,G` in the goal *and* in the `SI2`/`SI3` hypotheses, at the
   cost of dropping the definitional relation `d = u₁-u₂`; a port-local
   `hrel : d = u₁-u₂` restores it, and the certificate gains a third term whose
   coefficient is a 208-monomial polynomial (computed with `sympy`). The
   declaration went from **> 150 s** to about **10 s**; the prefix through it
   from **> 170 s** to **18.4 s / 20.6 MB**.

   **(b) `kw_velu2_secY_negAddY_align` — partially landed, then blocked on the
   normalizer.** Its local `set xA`/`set nAY` are now `generalize`d, so `simp` can
   no longer zeta-unfold the whole `addX`/`negAddY` bodies into the goal; the
   certificate is unchanged and the prefix through `kw_velu2_secY_align` went
   75.2 s / 88.1 MB → **71.1 s / 87.76 MB**. The *full* recipe of (a) does **not**
   transfer: generalizing `x₁-x₀, x₂-x₀, x₁-x₂, veluGx` and substituting
   `d = u₁-u₂` away with `rw` leaves a **small** goal (1.6 kB printed, and the
   whole setup through `mul_left_cancel₀` is only 1.6–3.5 s), and the three
   certificate coefficients are only **42/125/229** expanded monomials — yet the
   final `linear_combination` does not finish within 115 s.

   A one-line diagnostic isolates it: `linear_combination (norm := skip) …`
   compiles in **3.9 s**. So neither the certificate elaboration nor the goal is
   the problem; the default post-normalizer `ring1` is the hog (it is asked to
   prove the target over the generalized atoms), and `ring_nf` as the normalizer
   does not help either. That is different from (a), where the same recipe made
   `ring1` cheap.

   **What the next session needs to know.** (i) The substitution step must be
   `subst hrel`, *not* `rw [hrel] at *`: the latter rewrites `hrel` itself first,
   turning it into `u₁-u₂ = u₁-u₂`, and so is a no-op everywhere else — `d`
   survives in the goal and all hypotheses. With `subst`, everything is
   genuinely shifted, the goal is 1.6 kB, and `(norm := skip)` is ~4 s.
   (ii) The pin's certificate does **not** transfer by substitution alone: a
   `sympy` model of the shifted goal and hypotheses says `c₁·hSIY +
   c₂·hxA_rel + c₃·hnAY_rel` is *not* the goal (that model also fails to
   reproduce the *original* certificate, so the model or `linear_combination`'s
   own target-forming step must be pinned down first). The ground truth for that
   is the goal `linear_combination (norm := skip)` leaves, which
   `lean/tmp/study_b_skip.lean` prints in full. (iii) `hSIY` is the cleared
   secant identity that `OrderTwo` now proves cheaply by Vieta, so deriving
   `hColQ`'s certificate in those shifted coordinates is the natural route; the
   isolated block is `lean/tmp/study_b.lean` (its dependencies are public).
   **Scratches (kept):** `lean/tmp/study_b.lean` — isolated landed `hColQ`;
   `lean/tmp/study_b_gen.lean` — the `generalize`+`subst` recipe;
   `lean/tmp/study_b_skip.lean` — the `(norm := skip)` diagnostic and its
   printed target.

   **(d) `TangentXAlign` is the next hog, and it is `field_simp`-bound.**
   Prefixes: through `kw_velu2_secY_align` **72.7 s**; through
   `Piece_KwVeluOrderTwoTangentXAlign` **> 160 s**. Yet `kw_velu2_tanX_align`'s
   certificate is the tiny `linear_combination -W.veluGx x₀ y₀ * hNpp`, so its
   cost is the `field_simp`/`simp`/`rw` setup — a different bottleneck from (a)
   and (b). The `tanY` alignments and the block at 1109-1428 are still
   unmeasured.

   **The earlier diagnosis still explains (a)/(b) ring cost.** The goal
   `field_simp` leaves is *not* big — 3.5 kB printed and only 5,584
   `(x,y,x₀,y₀)`-monomials expanded (9,005 with `a₁,a₂,a₄`) — yet `ring_nf` on it
   alone takes 53–74 s (profiler: `tactic execution` 53 s, `ring` 0.5 s,
   typeclass inference 1 s); removing the dead `(common factor) * 0` on its RHS,
   lowering `maxRecDepth`, and `ring_nf` as the `linear_combination` normalizer
   all fail to help. The cost is ring's per-monomial proof construction on the
   **raw** presentation, which the `generalize`-plus-relation recipe of (a)
   removes when the certificate is small enough to elaborate.
   **Method and constraints.** The full module build (~688 s) exceeds the
   2-minute cap. To attribute cost, do *not* prefix-compile (it re-elaborates
   everything from line 1); instead copy the target declaration plus its private
   dependencies into a scratch importing the built module, and compile that with
   `lake env lean -o`. Remember `set_option maxHeartbeats 4000000`, which
   `lake build` supplies but `lake env lean` on a scratch does not. Land a batch,
   then take one full `lake build` to re-measure.
   **Risk.** (b) and (d) are *functional* statements (`velu2X`/`velu2Y` against
   the quotient's `addX`/`addY`) proved through `field_simp`; (b) needs its
   certificate re-derived, (d) needs the clearing itself made cheaper.
3. **Re-take the tree measurement** (4 threads) and re-rank the modules with
   `tools/deps/warnings/analyze_build.py`; `OrderTwo` should now read ~45.8 MB
   and ~69 s, and the tree should have lost the old 48-minute `OrderTwo` chain.
4. **The `math/` note is written**:
   `math/029-order-two-velu-quotient-and-its-cleared-identities.md`.

## 7. Artifacts

| path | what |
|---|---|
| `lean/tmp/velu_core2.lean` | the landed core: two-branch small certificates, compiles at `maxHeartbeats 200000` |
| `lean/tmp/velu_full.lean` | core + wired theorem, compiles at 200 K (6.8 s wall) |
| `tools/deps/warnings/velu_refactor_check.py` | sympy verification of every identity in §4 |
| `tools/deps/warnings/velu_secant_check.py` | sympy verification of the Vieta proof of §4′ (statement = `T`, the factorization, and the two Vieta certificates) |
| `tools/deps/warnings/velu_map_check.py` | sympy verification of the `OrderTwoMap` target (c): the shifted `kw_velu2_tanY_SI2c` and its nine-term certificate |
| `lean/tmp/map_tanY3.lean` | the landed `OrderTwoMap` target (c): `tanY_SI2c_shifted` + the rewired theorem, compiles at the global heartbeat cap |
| `lean/tmp/study_b.lean` | isolated copy of `kw_velu2_secY_negAddY_align`'s `hColQ` block (its dependencies are public), for cheap iteration on (b)'s certificate |
| `lean/tmp/study_b_gen.lean` | the same block with the `generalize`+`subst hrel` recipe (shifted goal, fast setup, slow `ring1`) |
| `lean/tmp/study_b_skip.lean` | the `linear_combination (norm := skip)` diagnostic; prints the exact normalisation target for (b) |
| `lean/tmp/map_tanY.lean` | the previous session's probe of the *ported* `kw_velu2_tanY_SI2c` (15.89 MB / 15.1 s), kept for the before/after |
| `lean/tmp/velu_secant_v2.lean` | the landed secant core: `secant_factor` + the Vieta `velu_secant_core`, compiles at `maxHeartbeats 200000` |
| `lean/tmp/velu_secant_core3.lean` | the superseded three-branch secant core (branch A, char ≠ 2, char 2) |
| `lean/tmp/velu_secant_full.lean` | the superseded three-branch core + wired theorem |
| `math/029-order-two-velu-quotient-and-its-cleared-identities.md` | the mathematics of the quotient, both identities, and the refactors |
| `lean/tmp/velu_core.lean` | the superseded D³ core (single 2 kB certificate; does not fit 200 K) |
| `tmp/velu_cert.txt` | the superseded certificate `C₁` and `q` (as sympy expressions) |
| `tools/deps/warnings/analyze_build.py` | ranks a `lake build` log by module wall time |
| `tools/deps/warnings/{fix_warnings,fix_loop.sh,fix_dep,sweep,screen}.py` | the warning sweep's tooling |

To reproduce the tangent refactor (any CAS): define `T` as the statement's left-hand
side with `addX`/`negAddY`/`slope`/`veluGx` unfolded and `u_R, v_R` inlined via
`m_P`; then take the `v`-coefficient `B`, the substitution residual `S`, and the
elimination multipliers `P₁`, `Q` of §4. The script above does exactly that.
To reproduce the secant Vieta proof: factor the statement as in §4′ with `u_R`
free, then verify the two Vieta certificates against the two curve equations —
`velu_secant_check.py` does that.

## 8. Open threads elsewhere (campaign state at handoff)

- **The warning sweep** from `tmp/tree_build_500k.log` is 322 → **66**, with 0
  errors in every file. What is left: **52 public `unusedSectionVars` /
  `overlappingInstances`** (left deliberately — for a public theorem every real
  fix removes leading binders from its type, so the interface-preserving route is
  a targeted per-declaration linter switch, which was declined); **11 deprecated
  names whose replacement changed shape** (`TensorProduct.induction_on`,
  the `Ideal.inertiaDeg'` family, `Ideal.inertiaDeg'_eq_inertiaDeg` — proof work,
  not renames); **3 deprecated imports**
  (`Mathlib.NumberTheory.RamificationInertia.*` → `Mathlib.RingTheory.…`, which
  needs the uses renamed in the same pass — swapping alone loses
  `Ideal.sum_ramification_inertia_eq_finrank`). Tooling: `tools/deps/warnings/`.
- **One error I introduced and repaired**: a tree-wide import swap over-reverted
  six files that legitimately used the *new* `RingTheory.RamificationInertia`
  modules; `PlacesOverDVR` was rebuilt and `WeilExchange/FiberOverCount` now
  elaborates with 0 errors, 0 warnings.
- **Not yet built at 4 M**: the 25 pending `AlgebraicCurve` modules plus
  `OrderTwo`'s dependents — one more `lake build` reaches a green tree.
- The 4-thread build itself: `tmp/tree_build_4t.log`, ranked with
  `python3 tools/deps/warnings/analyze_build.py tmp/tree_build_4t.log`.

## 9. Second wave (2026-10-16, evening): the three ring-term hogs

A later tree build (`tmp/my.log`) showed `OrderTwoMap` at 1070 s wall (that
figure is a 4-thread tree wall, inflated by contention). Measured cleanly with
one `lake env lean -DmaxHeartbeats=4000000 -o` per module, the pre-fix module is
**459.3 s / 391.2 MiB**.

**Isolation.** `tmp/iso_gen.py` copies the module with all theorem bodies
replaced by `sorry` except a named keep-list, so each declaration can be timed
and sized on its own (`tmp/iso/run*.sh`; results in `tmp/iso/RESULTS*.txt`).
The `.olean` difference from the all-`sorry` baseline is the declaration's proof
term. The whole 391 MiB was four declarations:

| declaration | wall | `.olean` |
|---|---:|---:|
| `kw_velu2_tanX_align` | 306 s | 242.1 MB |
| `kw_velu2_tanY_negAddY_align` | 67 s | 71.7 MB |
| `kw_velu2_secY_negAddY_align` | 54 s | 67.9 MB |
| `kw_velu2_secX_align` | 16 s | 15.1 MB |
| everything else | ≤ 24 s | ≤ 2.3 MB |

All four costs are in the final `linear_combination`: e.g. for `tanX_align` the
whole `rw`/`simp`/`field_simp` setup is 0.6 MB / 5 s, and the last
`linear_combination -W.veluGx x₀ y₀ * hNpp` is 242 MB / 306 s. The certificate
text is tiny; the cost is `ring`'s normalisation of the raw presentation.

**The fixes.** `sympy` is the ground truth for what `ring` must prove: replace
the normaliser with `linear_combination (norm := skip)`, `trace_state`, and
parse the residual (`tmp/iso/tanx_skip.log`). It is an identity; the question is
only its *presentation*.

- `secY_negAddY_align`'s `hColQ`: the statement's cleared form is 30 terms and
  its certificate against `veluGx`-free atoms is **4 + 4 monomials**
  (`tmp/colq.py`, `tmp/colq2.py`): `T = G·u₁·(u₁-U)·(u₁-u₂)·hSIY
  - U·u₁·u₂·(Uu₁-G)·(u₁u₂-G)·hnAY_rel`, with `hxA_rel` not needed at all.
  Factoring the four `velu2X/Y` differences into single fractions
  (`hX21/hXR1/hYR1/hY21`) makes `field_simp` produce exactly `T`.
- `tanX_align`: `generalize` the shifted atoms *after* `simp only [velu2X, …]`,
  but first normalise the shapes so the goal and `hNpp` agree syntactically.
  `sympy` factors the naive atomised residual as
  `-A·G·u·(u²-G)·C·(S - a₁D - 2E)`; `S = a₁D + 2E` holds in the base variables
  but is lost once `D,E` are atoms, so `S` is rewritten to `a₁D + 2E` in the
  same `simp only`. (Generalising *before* `simp only [velu2X, velu2Y]` re-mints
  raw `veluGx` — that was the first failed attempt.)
- `tanY_negAddY_align`: same idea with only `A, E, G` generalised, again after
  `simp only [velu2X, velu2Y]`; the certificate keeps the raw `(x-x₀)`,
  `(x2P-x₀)` factors, so no relations are severed.

**Result.** `lake env lean -DmaxHeartbeats=4000000 -o … OrderTwoMap.lean`:
**459.3 s / 391.2 MiB → 48.6 s / 60.3 MiB**, 0 errors, 0 warnings (landed in
[`htzh/flt_for_human@c46cb57`](https://github.com/htzh/flt_for_human/tree/c46cb57);
`lake build` of the module reports 49 s). The
remaining weight is `secX_align` (15 MB), `tan_quotSlope_eq` (9.6 MB) and `tanY`
(~22 MB), all now under the port's caps by a wide margin. Scratch certificates:
`tmp/iso/tanx_fix.lean`, `tmp/iso/tany3.lean`.
