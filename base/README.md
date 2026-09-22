# `base/` — foundational mathlib-level notes

Notes in this directory explain the mathlib layers the FLT formalization is
*written against*, as opposed to the FLT-specific argument itself. The two
series are deliberately separate:

| | [`../math/`](../math/) | `base/` (this directory) |
|---|---|---|
| subject | one step of the FLT proof, opened up | one mathlib theory or Lean-encoding convention |
| typical question | "why does `Mazur_Frey` follow from this dichotomy?" | "what *is* `K ≃ₐ[S] K`, and why does the definition look like that?" |
| citations | FLT `Definitions/`/`Theorems/`/`P2M/Sol/`, plus mathlib where used | mathlib first, then the FLT declaration that instantiates it |
| numbering | follows the proof route | grouped by mathlib subject, so order is not a path |

Both series follow the writing and citation rules in [`../AGENTS.md`](../AGENTS.md)
and the research loop in [`../notes/research-workflow-math-notes.md`](../notes/research-workflow-math-notes.md):
pin every FLT citation to the sha `aa2d8b3`, cite mathlib at tag `v4.33.0`,
quote Lean verbatim, and never cite an untracked local file. Line-number
citations are rendered GitHub links carrying `#L` anchors.

**Reading order and assumed background.** Note 001 is the primer on field and
Galois theory: it fixes how the project writes field extensions (`Algebra`, the
`R → S → K` tower), Galois groups (`K ≃ₐ[S] K`), algebraic closures, and the
Galois action on modules, and later notes do not re-explain those. Notes 002 onward assume 001 and move faster over
notation, spending their space on the subject at hand.

## Notes so far

- [001 — Field extensions, Galois groups, and Galois actions](001-field-extensions-and-galois-basics.md):
  the field and Galois theory every later note assumes — extensions and their
  adjectives (algebraic, separable, normal, Galois), the absolute Galois group
  of `ℚ` and what it acts on, decomposition and inertia, the Galois action on
  modules with Galois-stable submodules and the fixed/cofixed dichotomy, and the
  finite versus infinite Galois correspondence; then the Lean encoding in one
  summary section (`Algebra` towers, `IsAlgClosure`, the type `K ≃ₐ[S] K`,
  `Point.map`, `IsGaloisStable`, `HasGaloisStableCofixedLine`, inertia
  subgroups) with its reading traps. The running example is `AlgebraicClosure ℚ`;
  the module-action section is where `GaloisRepIsIrreducible` and
  `HasGaloisStableCofixedLine` come from.
- [002 — Modular forms at the mathlib level](002-modular-forms-basics.md):
  the `SlashInvariantForm`/`ModularForm`/`CuspForm` chain, why the level is a
  subgroup of `GL (Fin 2) ℝ`, `qExpansion` and the one-line `qCoeff` wrapper,
  an explicit inventory of what mathlib lacks (Hecke operators, eigenforms,
  newforms, any level above one), the Hecke operators and Hecke algebra FLT
  builds instead, `IsNormalizedEigenform` as four recursions on `q`-coefficients,
  and the `S₂(Γ₀(2)) = 0` endgame.
- [003 — No level-2 weight-2 cusp forms](003-no-level-2-weight-2-cusp-forms.md):
  the proof of `S₂(Γ₀(2)) = 0` as mathematics rather than as Lean — the index
  `[SL₂(ℤ) : Γ₀(2)] = 3` by counting the first column mod 2, the norm
  construction (weight multiplied by the index, vanishing only on zero forms),
  and the level-one vanishing of §4 taken all the way down to the
  maximum-modulus principle and the fundamental domain.
- [004 — The j-invariant: its q-expansion and first properties](004-the-j-invariant.md):
  where FLT's `eisenstein4`, `etaProd` and `Δ/q` come from, the long division
  that produces `j = q⁻¹ + 744 + 196884q + ⋯`, the formal proof that the
  coefficients are integers, weight-zero invariance, the simple pole at the cusp,
  the disc picture and the natural boundary on the real line, why the
  q-expansion faithfully models the function field, and the values
  `j(i) = 1728`, `j(ρ) = 0`, with the compactification `X(1) ≅ ℙ¹`, the
  Hauptmodul property `ℂ(j)`, CM and moonshine stated and cited but not proved.
- [005 — Cyclic isogenies, congruence level, and the j-invariant](005-cyclic-isogenies-and-level.md):
  complex tori as lattices and the moduli reading of `j` (with the Lean model
  `ofJ`, `nearCurve`/`goodModel`, `jLineRingEquiv`), order-`N` subgroups / cyclic
  isogenies / the `p+1` quotient curves `E_{pτ}` and `E_{(τ+b)/p}`, the index
  contrast `[Λ + ℤ(1/p) : Λ] = p` versus `[(1/p)Λ : Λ] = p²`, the Dedekind count
  `ψ(N)`, duality, and the congruence level `Γ₀(N)`.
- [006 — The modular equation: integrality and splitting](006-the-modular-equation.md):
  the classical language behind [math/010 §3](../math/010-function-field-generation.md#3-the-modular-polynomial-and-the-roots-of-the-modular-equation) —
  the modular polynomial `Φ_N` and its zero locus in `X(1) × X(1)`, why the symmetric
  functions of the roots have integer coefficients (algebraic-integer
  q-expansions, Galois descent, `ℤ` integrally closed in `ℚ`, and the residue-one
  pole reading off the top coefficient), the prime-level splitting and the
  coset/slot parametrization `j(ζ_M^{ab} q^{a²})`, the cover `X_0(p) → X(1)` with
  its monodromy and what proves algebraicity, a `p = 3` example carried through in
  full, the Lean route quoted as a route map, and a hand computation of `Φ₂`.
- [007 — The Weil pairing](007-weil-pairing.md):
  the pairing and its six laws, matched to the fields of FLT's `IsWeilPairing`;
  why nondegeneracy on a basis is primitivity of `e_n(P,Q)`; the two-line
  derivation that `det ρ_{E,n} = χ_n` and hence that the representation is odd;
  the divisorial definition `e_n(P,Q) = (-1)^n f_P(Q)/f_Q(P)` and Miller's
  algorithm, which is `WeilDatum.pairing` in the formalization; the
  characteristic-zero cases — the explicit formula
  `e_n(u/n, v/n) = ζ_n^{ad-bc}` on `ℂ/Λ` with the `ℤ[i]`, `n = 3` example,
  Galois equivariance over a number field, and the Tate module and its
  cyclotomic multiplier; the finite-field/Frobenius shadow; the four worked
  examples from `../pymath/weil_pairing.py`; and how the FLT proof uses it (the
  Frey determinant and `IsOdd`, `frey_reducible_hasCofixedLine`, the cyclotomic
  multiplier on the Tate module of `J₀(N)`, and rank `2g`).
- [008 — Divisors, linear equivalence, and Pic⁰](008-divisors-and-pic0.md):
  the classical divisor theory behind the proof's use of the Jacobian — a point
  as a discrete valuation ring, the order of vanishing, residue fields and the
  degree of a point; divisors as finite integer combinations of points, their
  degree and degree-zero part; principal divisors, the residue theorem, linear
  equivalence, and `Pic`/`Pic0`; the Jacobian of `X₀(N)` with its Hecke and
  Galois actions and the rank-`2g` count; ramification, the fundamental
  identity, pushforward and pullback, and the correspondence that becomes `T_ℓ`;
  differentials, the canonical class and Riemann–Roch; and one summary section
  (§8) on how the code encodes all of it, with the key-point table, plus the
  genus-one computation from `../pymath/divisors_and_pic0.py`.
- [009 — Differentials, residues, and Riemann–Roch](009-differentials-residues-riemann-roch.md):
  the machinery behind 008's two standing facts — the one-dimensional space of
  differentials `Ω[F⁄K]`, the order and divisor of a differential, the canonical
  class and `genus = (deg K + 2)/2`; local residues and the residue theorem, and
  how its log-derivative case yields "a nonzero function has as many zeros as
  poles"; the function space `L(D)`, its dimension `ell D` and the index of
  specialty; the Riemann inequality and Riemann–Roch, with the genus-0, genus-1
  and degree-zero cases; the genera-0-to-4 computation from
  `../pymath/riemann_roch.py`; and one summary section (§6) on the code, where
  `IsCurveOver` carries the residue theorem and the Riemann/duality/Riemann–Roch
  rows are four named `Prop`s.
- [010 — Finite fields, Frobenius, and point counts](010-finite-fields-frobenius-and-point-counts.md):
  the arithmetic of a curve over a finite field — rational points as the fixed
  points of the `q`-power map; the Frobenius endomorphism, `deg φ_q = q`, and
  `#E(𝔽_q) = deg(φ_q - 1)`; the characteristic polynomial `T² - a_q T + q`,
  Hasse's bound `a_q² ≤ 4q`, and the counts over every extension; the free
  rank-2 (rank-2g) Tate module, with the `p`-torsion caveat; why the polynomial
  is the bridge from an elliptic curve to a modular form
  (`ResidualGaloisRep.IsAttachedTo`) and the constant term is the cyclotomic
  character; the point counts of `../pymath/frobenius_charpoly.py`; and one
  summary section (§7) on the code, with the key-point table.
- [011 — Deformations, Hecke algebras, and `R = T`](011-deformations-hecke-algebras-and-r-equals-t.md):
  the layer joining the modular-forms side to the Galois side — deformations of
  a residual representation and the universal deformation ring with its
  universal property; the Hecke algebra as a ring, its generators and
  eigenideals; the map `R → T` built from the Eichler–Shimura representation,
  and what `R = T` asserts (a size statement, proved by the numerical criterion
  plus Taylor–Wiles patching); the Eisenstein/non-Eisenstein dichotomy; and one
  summary section (§6) on the code with the key-point table, quoting
  `DeformationRingData`, the deformation functors,
  `HeckeAlg`/`heckeGen`/`eigenIdeal`, `heckeTorsion`/`mTorsionGaloisRep` and the
  dichotomy data. Notes that the code has no single declaration named for the
  equality.
- [012 — Adeles and automorphic representations](012-adeles-and-automorphic-representations.md):
  the adelic language the projective side of 002 eventually feeds — the adele
  ring as a restricted product and the idele class group; `GL₂` over the adeles
  and the compact-open `K₀(N)`; automorphic representations and the local–global
  picture (with an explicit note that the restricted tensor product is not
  formalized in the code, and what stands in for it); the classical ↔ adelic
  dictionary; Hecke operators and the eigenvalue dictionary; local newvectors,
  conductor and level; Hecke characters and the cyclotomic character's
  idele-class description; and one summary section (§10) with the 30-row
  key-point table.
- [013 — Riemann existence for modular curves, and the level-one q-expansion
  principle](013-riemann-existence-and-the-q-expansion-principle.md):
  the classical Riemann existence theorem in its function-field form and its
  modular-curve corollary — the compact curve `X₀(N)`, the cover
  `X₀(N) → X(1)` of degree `ψ(N)`, its cusps, genus and monodromy; then the
  separation of the two facts the modular-equation argument needs (R1, the
  level-one q-expansion principle / Liouville on `X(1)`, and R2, degree and
  connectedness at level `N`), the observation that the FLT proof keeps R1 only
  at level one and reconstructs R2 from the explicit root list of `Φ_p` and the
  twist automorphism, a walk through the analytic segment
  (`RealL` → pole killing → the constancy kernel → the `ℚ[j]` headline → the
  coset application), and the direct answer that the genuine analytic input is R1
  specialized to `X(1)`, stated minimally as the kernel; with the key-point
  table.
