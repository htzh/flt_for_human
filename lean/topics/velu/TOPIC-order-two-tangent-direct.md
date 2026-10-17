# The order-two tangent identity, proved directly — the `Velu/OrderTwo` hog

**Status: both identities are refactored and landed (2026-10-16).** The proofs
of `velu2_tangent_negAddY_cleared_identity` and
`velu2_secant_negAddY_cleared_identity` no longer contain large certificates: the
tangent one is a two-branch argument (largest polynomial 19 terms), the secant
one a three-branch argument (certificate text 14,355 → 7,066 chars), and neither
uses a giant `linear_combination`. Measured in `Velu/OrderTwo.lean`: `.olean`
**276 MB → 45.8 MB**, module build **2168 s → 69 s**. The remaining work is
`Velu/OrderTwoMap.lean` (§6.2). This note
records (i) the measurement that found the hog, (ii) why the ported proof is
catastrophic, (iii) the refactored proof and its two small certificates, and
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
- The residual 68 MB / 55 s is the **secant** certificate, which is still the
  ported one.

## 6. What is left

1. **The secant identity — landed (2026-10-16).** `velu2_secant_negAddY_cleared_identity`
   now uses three small certificates in shifted coordinates instead of the ported
   14,355-character `linear_combination` (four arguments of 6,783 / 3,189 / 2,830 /
   1,553 characters), split on $`A := d(a_1+2m)`$:
   - branch $`A \ne 0`$: $`d\,A\,T = \alpha_1c_1+\alpha_2c_2+\alpha_3g_2`$;
   - branch $`A = 0`$, $`2 \ne 0`$: $`32\,d\,T^{(s)} = 4B\,P_2 + M\,(2m+a_1)`$;
   - characteristic 2 (where $`A = d\,a_1`$, so the case is $`a_1 = 0`$): the
     mod-2 certificate $`d\,T = \mu_0g_2+\mu_2\hat R+2E+a_1F`$, whose essential
     factor is the unit $`d = u_1-u_2 \ne 0`$. Without it, $`T`$ is *not* in the
     ideal generated by the shifted relations (§5 of the math note).
   Measured: certificate text 14,355 → 7,066 chars; the proof term 40.4 → 15.3 MB;
   `OrderTwo.olean` 67.3 → **45.8 MB**; module build 55 → 69 s (the cost sits in
   the many large statements, not in the certificates). Statements unchanged
   (`spec/check_flt_statements.py`: 9791 identical).
2. **`Velu/OrderTwoMap` (569 MB, 728 s) — plan for a new session.** Attribution
   by prefix compiles with `-o`, each inside the 2-minute cap:

   | prefix end | `.olean` | wall |
   |---|---:|---:|
   | line 352 (`AddKernel`) | 1.2 MB | 5.8 s |
   | line 635 (`SecantCarrier`) | 19.2 MB | 21 s |
   | line 771 (`SecantConjunctOne`) | 19.7 MB | 23 s |
   | line 820 (`SecantAlign: kw_velu2_secX_align`) | — | **> 120 s** |
   | same, with that theorem's `linear_combination` replaced by `sorry` | 19.9 MB | **33 s** |

   **Targets, in order.**
   (a) `kw_velu2_secX_align` (`OrderTwoMap.lean:790-819`) — **> 87 s by itself**;
       its certificate multiplies two very large cleared expressions, so the
       elaboration (not `field_simp`) is the hog. Refactor: state the cleared
       `addX` alignment in shifted coordinates, certify it with small
       polynomials (its ingredients `kw_velu2_secX_SI2/3` are already moderate),
       then derive the alignment.
   (b) the rest of `SecantAlign`: `kw_velu2_secY_negAddY_align` (`:821-871`,
       808/836-character arguments) and `kw_velu2_secY_align` — same shape.
   (c) `kw_velu2_tanY_SI2c` (`:431-450`) — **15.9 MB** on its own; the tangent
       machinery of §4 should apply directly.
   (d) then the heavy proofs in lines 1109-1428 (`PointMap2_add_self`,
       `PointMap2_add'`, the carrier discharge), re-measuring as we go.
   **Method and constraints.** The full module build (~728 s) exceeds the
   2-minute cap, so iterate by extracting individual theorems into scratch files
   importing `Velu.OrderTwo`/`Velu.Defs` and compiling with `lake env lean -o`;
   attribute with prefix compiles as in the table. Land a batch, then take one
   full `lake build` to re-measure.
   **Risk.** Several of these are *functional* statements (`velu2X`/`velu2Y`
   against the quotient's `addX`/`addY`) proved through `field_simp`; the win
   comes from replacing the giant ring verification by a cleared identity with a
   small certificate, exactly as for `OrderTwo`'s two identities.
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
| `tools/deps/warnings/velu_secant_check.py` | sympy facts for the secant identity (statement = `T`, ideal membership, branch-`A` certificate, `B₀ = -d·D₀'`) |
| `lean/tmp/velu_secant_core3.lean` | the landed secant core: three branches (branch A, char ≠ 2, char 2), compiles |
| `lean/tmp/velu_secant_full.lean` | secant core + wired theorem (the landing reference) |
| `math/029-order-two-velu-quotient-and-its-cleared-identities.md` | the mathematics of the quotient, both identities, and the refactor |
| `lean/tmp/velu_core.lean` | the superseded D³ core (single 2 kB certificate; does not fit 200 K) |
| `tmp/velu_cert.txt` | the superseded certificate `C₁` and `q` (as sympy expressions) |
| `tools/deps/warnings/analyze_build.py` | ranks a `lake build` log by module wall time |
| `tools/deps/warnings/{fix_warnings,fix_loop.sh,fix_dep,sweep,screen}.py` | the warning sweep's tooling |

To reproduce the refactor (any CAS): define `T` as the statement's left-hand
side with `addX`/`negAddY`/`slope`/`veluGx` unfolded and `u_R, v_R` inlined via
`m_P`; then take the `v`-coefficient `B`, the substitution residual `S`, and the
elimination multipliers `P₁`, `Q` of §4. The script above does exactly that.

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
