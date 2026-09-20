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

**Reading order and assumed background.** Note 001 is the notation primer: it
fixes how the project writes field extensions (`Algebra`, the `R → S → K`
tower), Galois groups (`K ≃ₐ[S] K`), and algebraic closures, and later notes do
not re-explain those. Notes 002 onward assume 001 and move faster over
notation, spending their space on the subject at hand.

## Notes so far

- [001 — Field extensions and Galois theory at the mathlib level](001-field-extensions-and-galois-basics.md):
  `Algebra` instead of "field tower", the `R → S → K` binders and why they are
  inherited rather than needed, algebraic/separable/normal, `IsAlgClosure`,
  the Galois group as the type `K ≃ₐ[S] K`, `Point.map` as the action,
  decomposition/inertia subgroups, and the finite vs. infinite Galois
  correspondence. The running example is `AlgebraicClosure ℚ`.
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

## Candidate topics (not yet written, no order implied)

A working list, kept so the series does not drift into the FLT-specific
material already covered in `../math/`:

- **`ZMod n` and the mod-`n` world**: `ZMod` as a ring, its `Z`-module
  structure, `ZMod p` a field, cardinality and `Nat.card` facts. The substrate
  of `E[n]`.
- **Torsion submodules and cardinality**: `Submodule.torsionBy`, the
  `ZMod n`-module structure on `E[n]`, `natCard_eq_pow_finrank`, freeness and
  `finrank`, the basis construction behind `E[p] ≅ 𝔽_p²`.
- **Group actions on modules**: `SMul`/`DistribMulAction`/`SMulCommClass`,
  `IsGaloisStable`, trivial action on a quotient, the fixed/cofixed
  linear-algebra core, `DistribMulAction.toModuleAut`/`toModuleEnd`.
- **Deformation theory and Hecke algebras as rings**: `HeckeAlg`,
  eigenideals, `DeformationRingData`, and how `R = T` is stated — the bridge
  from note 002 to the modularity-lifting step of the proof.
- **Adeles and automorphic representations**: the `AdelicGL2` layer, local
  newvectors, Hecke characters — the language notes 002's projective side
  eventually feeds.

When a new note is added, extend the list above rather than renumbering.
