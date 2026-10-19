# Sharing one certificate: the singleton Vélu identity, general and special

**Moral of the story.** The hardness here was manufactured by the original cut, not by
the mathematics. The pin's singleton block was partitioned *syntactically* — following
the block structure of its solution silo: one `private` section per file, statements
transcribed where they happened to be written — and that partition does not reflect the
best mathematics. It leaves the kernel point generic and discharges the result with
monolithic `linear_combination` certificates of hundreds of monomials per side. The
same identity, stated where it is small (kernel point translated to the origin, §8), has
a certificate that is one square, with the general statement following by pure
invariance — and the term size drops out as a by-product. The lesson generalises:
module-local optimisation (certificate shape, staging the ring, `norm :=`, even
consolidating duplicate proofs) only ever shaves constants; the real gains, for clarity
as much as for size, come from asking whether the *statement* and the API around it are
cut the way the mathematics wants. That requires reading the whole structure, not the
silo in front of you.

**Status of §1–§6: landed (2026-10-17); superseded by §8.** `Velu/Formula.lean`'s largest declaration,
`velu_singleton_deficit_cleared_eq_psi`, and `Velu/Defs.lean`'s
`velu_singleton_equation_cleared`, are the *general* form and the `Ψ₃ = 0`
*specialization* of one identity. Each carried its own ~40 MiB `linear_combination`
certificate; they now share one, homed in `Defs` (upstream of `Formula`).
`Velu/Formula.lean` falls from **48.99 MiB to 8.94 MiB** (38 s → 7 s) and
`Velu/Defs.lean` moves 42.52 → 42.77 MiB — a net tree saving of **≈40 MiB** — with
every statement untouched (`9792 identical, 0 mismatched, 0 missing`, 43 own-proof
declarations exempted). A same-day follow-up (§6) folded the port-local name back into
the pinned-named `velu_singleton_deficit_cleared_eq_psi`, so the exemption count is now
**42**.

## 1. The pair

With $`u = x-x_0`$, $`v = y-y_0`$ and the singleton quotient data
$`T = \mathrm{veluT}\,x_0\,y_0`$, $`U = \mathrm{veluU}\,x_0\,y_0`$,
$`W = \mathrm{veluW}\,x_0\,y_0`$, both declarations compare the same left-hand side
$`\mathrm{veluYNum}^2 + a_1\mathrm{veluXNum}\,\mathrm{veluYNum}\,u + a_3\mathrm{veluYNum}\,u^3`$
with the quotient curve's right-hand side
$`\mathrm{veluXNum}^3 + a_2\mathrm{veluXNum}^2u^2 + (a_4-5T)\mathrm{veluXNum}\,u^4 + (a_6-b_2T-7W)u^6`$:

* `Defs.velu_singleton_equation_cleared`, given $`h_\Psi : \Psi_3(x_0) = 0`$, says
  the two are equal;
* `Formula.velu_singleton_deficit_cleared_eq_psi`, with **no** $`h_\Psi`$, says
  their difference is `veluDeficitPsiCofactor x₀ x * (W.Ψ₃).eval x₀`.

The cofactor is exactly the $`h_\Psi`$ coefficient of the special certificate
(`Defs.lean`, old lines 220–223), so the special case is the general one at
$`\Psi_3(x_0) = 0`$ — and each module was paying ~40 MiB for its own copy of the
same expansion.

## 2. The consolidation

* **new** `Defs.velu_singleton_deficit_cleared` (public): the general identity,
  with the cofactor written out inline and the certificate transplanted from
  `Formula` (it uses only `hP` and `hQ`; `Defs`'s private `eval_Ψ₃_eq` replaces
  `Formula`'s `eval_Ψ₃_eq'`).
* `Defs.velu_singleton_equation_cleared`: now three lines — take the general
  identity, specialize at $`h_\Psi`$, and cancel.
* `Formula.velu_singleton_deficit_cleared_eq_psi`: now
  `simpa only [veluDeficitPsiCofactor] using W.velu_singleton_deficit_cleared hP hQ`
  — its statement is unchanged, so consumers do not move.

The general identity has to live in `Defs` (or upstream): `Formula` imports
`Defs`, so the shared proof cannot live in the pinned home. The new public
declaration is registered in `spec/old_check_stmts.py`'s `OWN_PROOFS` (by
last name), which is what keeps the check at 0 missing rather than 1.

## 3. What this says about the recipe

The certificate is genuinely large — the odd-order analogue of the order-two
identity, which `ring` must normalise whatever the certificate's shape. A CAS
*factored* decomposition of the special case was found and verified (the $`h_C`$
coefficient is the square $`(u(2G+a_1gy-u^2)+2gy^2)^2`$ and the $`h_\Psi`$
coefficient collapses to five terms), but landing it **grew** the proof term
(42.52 → 45.15 MiB factored, 45.49 MiB expanded), so it was reverted. The
reusable lesson is in
[olean-attribution-and-shrinking.md](../../../notes/olean-attribution-and-shrinking.md)
§7: when the identity is too large to compress, look for a **second copy of it**.

## 4. Numbers

| module | before | after |
|---|---:|---:|
| `Velu/Formula.lean` | 48.99 MiB / 38 s | **8.94 MiB / 7 s** |
| `Velu/Defs.lean` | 42.52 MiB / 35 s | 42.77 MiB / 37 s |
| the pair | 91.51 MiB | **51.71 MiB** |

Sizes are `.olean` bytes (exact); times are single `lake env lean -o` /
`lake build <module>` wall times on this machine, and are indicative only.

## 5. Follow-up (2026-10-17): staging the ring does not clear this term

§3 records a *readability* reading of the identity and a *size* win from
consolidation. The natural next question is whether the ~40 MiB proof term can
be removed by **staging** — never handing `ring` the whole expanded identity,
but proving it in small steps, in the spirit of `OrderTwoMap.lean`'s
`kw_velu2_tanX_align` (242 MB → ≈1 MB: shape rewrites `at *`, `generalize` the
atoms `at *`, then a one-term certificate whose residual is *literally* zero).
For this identity the measured answer is **no**. The probes are scratch files
under `lean/tmp/velu_odd/` (untracked); sizes are exact `.olean` bytes of an
isolated copy of the declaration, compiled with `lake env lean -o`.

| probe | `.olean` |
|---|---:|
| statement only (`sorry`) | 46,480 B |
| statement + `rw`/`simp only` setup (`sorry`) | 82,248 B |
| compact certificate $`A_0\cdot hP-(A_0+u^2B)\cdot hQ`$ | 42,532,928 B |
| staged proof (free atoms + Vieta + reduced ring) | 44,305,968 B |
| staged, reduction step `sorry`d (reduced-identity ring only) | 38,662,856 B |

Two facts fall out. First, **the proof term is all `ring`**: the whole
`rw`/`simp only` setup is 82 kB, and replacing the ported monomial certificate
by a compact one changes nothing (the ported certificate's two coefficients are
~160-monomial polynomials; the compact one is a square plus 42 monomials).
Second, **staging the reduction does not shrink the hog**: with the free-atom
reduction `sorry`d, the single remaining `linear_combination` on the raw
*reduced* identity is still 38.7 MiB.

The compact certificate used above, sympy-verified, is the general case of the
square quoted in §3. With $`u=x-x_0`$, $`v=y-y_0`$, $`gy=\mathrm{veluGy}\,x_0y_0`$,
$`G=\mathrm{veluGx}\,x_0y_0`$,

$$ \text{deficit} \\;=\\; A_0\cdot(hP-hQ) \\;-\\; u^2\\,B\cdot hQ,\qquad
A_0=\bigl(u(2G+a_1gy-u^2)+2gy^2\bigr)^2, $$

where $`B`$ is the 4-$`u`$-monomial quotient of $`Q+\mathrm{Red}\cdot\Psi_3`$ by
$`hQ`$ (42 monomials). The Vieta split behind it is
$`\mathrm{veluYNum}=D_0v+P_0`$ with $`D_0=u^3-2U-Tu`$, the bracket
$`D_0(gy-a_1u)+2P_0+a_1X u+a_3u^3=0`$, $`\text{deficit}\equiv-u^2Q \pmod{hP-hQ}`$,
and $`Q+\mathrm{Red}\cdot\Psi_3=B\cdot hQ`$.

**Why the `tanX_align` move cannot apply.** There the 242 MB was a *presentation
mismatch*: the goal carried $`\Sigma`$ while the certificate carried
$`a_1D+2E`$, so the residual was a large nonzero polynomial; making every
occurrence the same atom made it zero. Here the reduced identity is a genuinely
large polynomial identity. Splitting $`Q+\mathrm{Red}\cdot\Psi_3=B\cdot hQ`$ by
$`u`$-degree gives coefficient identities of **105, 71, 0, 20 and 7** monomials;
the 71-, 20- and 7-monomial ones are free under `ring` (2,888 B each — the
statement-only size), while the 105-monomial $`u^0`$ identity does not finish in
115 s and a `factor` call on it does not finish in 60 s. That one coefficient is
the irreducible core.

**Where to look next.** The lever is to prove the $`u^0`$ coefficient identity
without `ring` (from the structure of $`\Psi_3`$ / the curve relation), or to
find a geometric proof that the deficit is cofactor $`\times\Psi_3`$. Certificate
shape and $`v`$-degree staging are both exhausted for *size*; the compact
certificate is nevertheless landed (§6): it is a readability win (a square and one
quotient, checkable in a CAS) and, measured on the module, a small size one too.

## 6. Follow-up (2026-10-17): the port-local name is folded back

§2's `Defs.velu_singleton_deficit_cleared` was port-local and its statement spelled
the cofactor out inline (`Defs.lean`, old lines 220–223). That inline expansion was
forced by declaration order, not by mathematics: `def veluDeficitPsiCofactor` lived
in `Formula`, downstream of `Defs`. The pin has no such declaration at all — its
`velu_singleton_deficit_cleared_eq_psi` and `veluDeficitPsiCofactor` are `private`
in the `P2M/Sol/` singleton-deficit block — so the statement was ours to choose.

The fix is a move, not a new declaration:

* `veluDeficitPsiCofactor` and `velu_singleton_deficit_cleared_eq_psi` move from
  `Velu/Formula.lean` into `Velu/Defs.lean`; the general identity is stated with the
  cofactor **named** and carries the certificate directly;
* `velu_singleton_deficit_cleared` is **deleted** — its only consumers
  (`velu_singleton_equation_cleared` and `Formula`'s
  `veluDeficit_singleton_mul_pow_eq_psi`) now use the pinned-named declaration;
* the `OWN_PROOFS` entry and the old `Velu/Formula.lean` attribution are removed, and
  `Formula` keeps only the reduced-cofactor forms.

Measured (move only): `Velu/Defs.lean` `44,846,360 -> 44,887,472 B`, `Velu/Formula.lean`
`9,375,624 -> 9,321,936 B`; the checker reports `9792 identical, 0 mismatched, 0 missing`
with **42** own-proof exemptions (was 43), and `Velu/Engine.lean` rebuilds. The net is
flat, as expected — the certificate did not move modules.

The certificate itself is then replaced by the compact form of §5,

```lean
  set A0 : R := ((x - x₀) ^ 3 - 2 * (2 * y₀ + W.a₁ * x₀ + W.a₃) ^ 2
      - (6 * x₀ ^ 2 + (W.a₁ ^ 2 + 4 * W.a₂) * x₀ + 2 * W.a₄ + W.a₁ * W.a₃) * (x - x₀)) ^ 2
    with hA0
  set B0 : R := (…) with hB0
  linear_combination A0 * hP - (A0 + (x - x₀) ^ 2 * B0) * hQ
```

with $`A_0`$ the square of the $`v`$-coefficient of $`\mathrm{veluYNum}`$ and $`B`$ the
quotient of $`Q+\mathrm{Red}\cdot\Psi_3`$ by $`hQ`$. This took `Velu/Defs.lean` from
`44,887,472` to **`44,053,128 B`** — ≈0.8 MiB smaller, not merely the readability win §5
predicted (the compact certificate also elaborates more cheaply than the two
~160-monomial lists). `Velu/Formula.lean` is unchanged at `9,321,936 B`, and the checker
still reports `9792 identical, 0 mismatched, 0 missing`, 42 exemptions.

The general identity is still **public** in `Defs`: `private` does not cross a module
boundary and `Formula` consumes it. Making it private (as the pin has it) would need
the larger cut that moves the point-map statements and the live consumer downstream,
out of the hub module — not done here.

## 7. Follow-up: certificate *reshaping* cannot beat the expansion floor

A suggested route was to avoid handing `ring` the two monomial lists by factoring the
hypotheses: prove instead

```lean
  linear_combination A0 * (hP - hQ) - ((x - x₀) ^ 2 * B0) * hQ
```

i.e. "subtract $`A_0(h_P - h_Q)`$ from the goal and `ring` the residual". This is
expressible (`linear_combination` does accept a coefficient times a *difference* of
hypotheses), but it **cannot** shrink the term, for an algebraic reason: by
distributivity

$$A_0\\,h_P-(A_0+u^2B)\\,h_Q \\;=\\; A_0(h_P-h_Q)-u^2B\\,h_Q,$$

`linear_combination`'s normaliser walks the same *expanded* polynomial either way. The
two shapes also cost the same to reify, and the difference is not even in the right
direction. Isolated probes (same statement, same `set`-bound $`A_0,B_0`$, exact
`lake env lean -o` bytes):

| probe | `.olean` |
|---|---:|
| current certificate $`A_0 h_P-(A_0+u^2B)h_Q`$ | 42,092,712 B |
| reshaped $`A_0(h_P-h_Q)-u^2B\,h_Q`$ | 44,547,544 B |
| statement + `ring_nf` on the goal, then `sorry` | 34,236,888 B |

The third row is the real datum: **normalising the expanded goal is already 34 MiB.**
That is the floor for any proof that lets `ring` see the expansion, so no certificate
of the current shape can go below it (the compact certificate's 42 MiB, the staged
38.7 MiB of §5 and this 34 MiB are all the same walk). Certificate shape is exhausted;
the only lever left is to make the *polynomial* smaller.

That lever is coordinate elimination and it is quantitative. With
$`u=x-x_0`$, $`v=y-y_0`$ the residual $`R = D - \mathrm{Cof}\cdot\Psi_3`$ has, in the
nine atoms $`x,y,x_0,y_0,a_1,\dots,a_6`$, **803 monomials** (degree 9 in $`x_0`$).
Eliminating the curve relations $`y^2=\mathrm{sP}`$, $`y_0^2=\mathrm{sQ}`$ (from
$`h_P,h_Q`$) leaves an identity with **207 monomials in the seven atoms**
$`x,x_0,a_1,\dots,a_6`$ — and there both sides are *equal as polynomials*, so the final
`ring` has no cancellation to find. The $`v`$-split of §5 removes $`y`$ but not
$`y_0`$; the $`y_0`$ elimination is the missing half.

Two notes on the earlier "105-monomial $`u^0`$ coefficient does not finish" verdict
(§5): re-running the probe here fails during **statement elaboration**
(`maximum recursion depth` on the explicit monomial list in the hypothesis type), not
inside `ring`. The scratch statements should be written with `set`/free atoms, per
§5.4, before concluding that the $`u`$-degree split is dead.

### 7.1 Attempted: the structural $`y_0`$ elimination (measured, negative)

The reduction is real: in coordinates $`u=x-x_0`$, $`v=y-y_0`$, after the §5 Vieta split
the residual $`\mathrm{hred} - C\Psi_3`$ has only **179 monomials** (degree 4 in
$`y_0`$), and eliminating $`y_0^2=\mathrm{sQ}`$ makes it vanish — the reduced left side
is **108 monomials** and equals $`C\Psi_3`$ exactly. So a proof through the reduced
identity would, if `ring` only saw that identity, cost a few MiB.

It does not work, because `ring`/`ring_nf` must expand the *unreduced* goal first, and
that expansion is what costs. `lean/tmp/velu_odd/Y0Elim.lean` implements exactly the
plan (derive $`y_0^2`$, `ring_nf`, `rw`, `ring_nf`, `rw`, `ring_nf`); it compiles, and
the staged measurement pins the cost of each step:

| probe (prefix of `Y0Elim`) | `.olean` | marginal |
|---|---:|---:|
| setup + `hC` + `hbr` + `hred` | 6,852,648 B | 6.9 MiB |
| + `rw [hD0, …]` + **one** `ring_nf` | 42,632,272 B | **+35.8 MiB** |
| + `rw [hy0_4, hy0_3, hy0]` + second `ring_nf` | 64,369,320 B | +21.7 MiB |
| + `rw [hy0]` + third `ring_nf` (full proof) | 74,654,384 B | +10.3 MiB |

The first `ring_nf` costs the same 35 MiB as normalising the *unreduced* goal
(§7's 34 MiB), even though the final form has only 179 monomials: the normaliser's term
tracks the expansion of the atom products (`D0²`, `P0²`, `Xn³`, each built from
$`\mathrm{veluGy}^2`$), not the final monomial count. And each subsequent `ring_nf`
re-normalises the whole goal, so staging *multiplies* the cost instead of splitting it.
Net: 74.7 MiB against the 42.1 MiB in place.

The conclusion sharpens §7: the floor is not the certificate, it is one `ring`
expansion of the goal in these coordinates, and no amount of post-hoc $`y_0`$
elimination gets under it. A win now needs the *statement itself* in coordinates where
the expansion is small (the §5 "normalization move"), not a cheaper route to the
existing statement.

Probes: `lean/tmp/velu_odd/{Baseline,Subtract,ProbeRNF,Y0Elim,Y0ElimP0,Y0ElimP1,Y0ElimP2}.lean`
(untracked).

## 8. Landed (2026-10-17): the coordinate-normalized statement

§7.1 concluded that a win needs the statement in coordinates where the expansion is
small. This section lands that move.

**The normalization.** Translate the kernel point to the origin: `x = x' + x₀`,
`y = y' + y₀` is a Weierstrass isomorphism onto `W.shiftCurve x₀ y₀` with

$`a_2' = a_2+3x_0`$, $`a_3' = a_3+a_1x_0+2y_0`$, $`a_4' = a_4-a_1y_0+2a_2x_0+3x_0^2`$,
$`a_6' = a_6+a_4x_0+a_2x_0^2+x_0^3-a_3y_0-a_1x_0y_0-y_0^2 = \mathrm{qResidual}`$.

Keeping the *actual* $`a_6'`$ (not setting it to zero) makes the transport **exact
invariance**, no correction terms: the CAS and Lean both confirm
`clr_W(x₀,y₀,x₀+u,y₀+v) = clr_{W'}(0,0,u,v)`, and likewise for
$`C_{\text{reduced}}`$ and $`\Psi_3`$. (Forcing $`a_6'=0`$ instead produces the
corrections $`-u^6q`$, $`12u^2q`$, $`b_2'q`$; keeping it cancels them.)  This is why
the Engine and every public statement stay untouched, correcting §7's "moving the
Engine bridge" — only proofs move.

**Where it is small.** On the translated curve the cleared deficit is a 52-monomial
identity and the certificate is one square, `(u³ - a₁a₃u - 2a₃² - 2a₄u)² · (hP form)`.

**Module layout.** New `Velu/Shift.lean` (imports `Velu.Defs`): `shiftCurve`,
`qResidual`, `clr`, the projection lemmas, the shift lemmas for
`veluT/veluU/veluGx/veluGy/veluW/veluXNum/veluYNum` and the cofactor, the invariance
`clr_shift`, `shiftCurve_equation`, the normalized identity, then
`velu_singleton_deficit_cleared_eq_psi`, `velu_singleton_equation_cleared` and
`velu_singleton_map_equation` (statements unchanged). `Defs` keeps the vocabulary;
`Formula` imports `Shift`.

`shiftCurve` is **Mathlib's** admissible change of variables, not a new abstraction:
it is `VariableChange.mk (1 : Rˣ) x₀ 0 y₀ • W` (`shiftCurve_def` records the
identification), division-free because `u = 1`. Our `shiftCurve_a₁ … shiftCurve_a₆`
are thin adapters proved from `variableChange_a₁ … a₆`, kept because the explicit
coefficient form is what the invariance proofs want; `qResidual` is Mathlib's
`variableChange_a₆` value. The pin does not use this — its proof is the direct
`linear_combination` certificate, and the port had no translation before §8.

**Cofactor cleanup.** The full `veluDeficitPsiCofactor` (26 monomials), the factoring
lemma `veluDeficitPsiCofactor_eq_sq_mul_reduced` and the six-power identity
`veluDeficit_singleton_mul_pow_eq_psi` were pure intermediates — Engine consumes only
the *reduced* cofactor. All three are deleted; the general identity is stated with
`(x - x₀)^2 * veluDeficitPsiCofactorReduced x₀ x * (Ψ₃).eval x₀`, the reduced cofactor
moves to `Defs`, and `veluDeficit_singleton_mul_pow_four_eq` is derived directly.

**Numbers** (exact `.olean` bytes):

| declaration / module | before | after |
|---|---:|---:|
| `Velu/Defs.lean` | 44,053,128 | **1,330,704** |
| `Velu/Shift.lean` | — | **25,785,120** |
| `Velu/Formula.lean` | 9,321,936 | **8,980,152** |
| Defs + Shift | 44,053,128 | **27,115,824** |

so the singleton identity's cost drops ≈38% and moves out of the hub module. The
identity itself was 42 MB of monomial certificate; it is now a 1.2 MB normalized
`linear_combination`, ≈23 MB of translation invariance (one `ring`), and ≈0.5 MB of
curve-equation transport.

**Verification.** `Engine`, `CyclicQuotientJ`, `Equivariance`,
`ModularPolynomialFibreTwo` and `OrderTwo` rebuild. `spec/old_check_stmts.py`
reports **0 mismatched, 0 missing**, 42 exemptions (9786 identical); no public
statement changed.

One measurement worth keeping: the invariance `clr_shift` is ≈23 MB in the
`(x₀ + u)` shape but ≈59 MB if stated as `(x - x₀)`, because `ring` then keeps `x`
and `x₀` as separate variables and expands `(x - x₀)^6`. The lemmas are stated with
explicit offsets and the `(x - x₀)` forms are `simpa` corollaries.

Probes: `lean/tmp/velu_odd/{NormLemma,ShiftLemmas}.lean` (untracked).
