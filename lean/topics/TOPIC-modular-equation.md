# The modular-equation theory: one subject, two theories, and the seam between them

**Status: theory A rebuilt and retargeted; body rewrites still to come.** This file records the
restructuring of the modular-polynomial / `PhiGen` cluster into the theory `ModularCurve.ModularEquation`,
the retarget of its consumers, and the retirement of the old modules to `Reserve`. Theory B (the level
tower / function field generation) is deliberately not restructured here.

The mathematics of theory A is [base/006](../../base/006-the-modular-equation.md); the level tower is
[math/010](../../math/010-function-field-generation.md) and
[math/010a](../../math/010a-any-field-supplement.md). This file is about the shape of the code.

## 1. The discovery: one seam, not several

The old cluster had no clean boundary. `ModularPolynomial*` and `PhiGen*` imported each other in both
directions, and the function field generation imported the modular polynomial in eight places while two
modular-polynomial modules imported the generation. What forced the boundary was a question about one
lemma: `eval_swap_eq_zero_of_splits` took the splitting as a hypothesis, which suggested it was restating
the product's vanishing at `j(q)`; it is not — the product fact is one line inside, and the lemma exists
to move a vanishing across the coefficient embedding.

Chasing that question up the import graph exposed the real interface. Theory B (generation, degrees,
non-membership, the level tower) reaches the modular equation only through two theorem families:

* the prime datum — a monic `Φ` of degree `psi(p) = p + 1` at `(j(q), j(q ^ p))`, irreducible and
  symmetric — used to give the level-`p` polynomial and the integrality of the level series;
* the root family at a slot — the splitting of `Φ_p` at an arbitrary level datum, over the rationals
  and over an arbitrary field carrying a primitive `p`-th root.

Everything else in the old cluster (the conjugate product, the descent, the integrality of the
coefficients, the assembly, the transpose, the dictionary, the level-two computation) is invisible to B.
Conversely, the composite-level closure (uniqueness at every level, the leading coefficient, the
resultant routes) is *proved from* B's degree count `[Q(j)(j(q ^ N)) : Q(j)] = psi(N)`, so it belongs to
B and not to the modular equation.

The seam is therefore a small, checkable fact about the code: the two theories are separate exactly
because the interface is two theorem families, both about `Φ_p`.

## 2. Why not three theories, and why not one

The natural first guess is a tower: modular polynomial, then `PhiGen`, then function field generation.
It is wrong for a structural reason and a mathematical one.

* Structurally, `PhiGen`'s splitting module imports the modular polynomial's *uniqueness* (the split at a
  prime is obtained by identifying the caller's datum with the assembled one). So a `PhiGen` theory below
  the modular-polynomial theory is a two-cycle — the very pathology the restructuring is meant to remove.
* Mathematically, `PhiGen` is the *construction* of `Φ`: the product over cyclic subgroups is the
  classical definition of the modular polynomial, and the descent/integrality/assembly statements are the
  statement that this product has integer coefficients. A proof technique is not a theory.

One theory fails in the other direction. Every subject of the level tower consumes the prime split, so
folding B into A would stack B's subjects on top of A's main results — three layers, not two.

Two theories, then, with the seam above: **A = the modular equation at a prime**, **B = the level tower**
(deferred), and a shared floor of `Defs/*` support.

## 3. Theory A's shape

`FLTForHuman/ModularCurve/ModularEquation/` holds seven modules in two layers plus support.

| module | lines | role |
|---|---|---|
| `Support/LevelEmbedding` | 77 | the level-`l` nome embedding `Q((q)) -> K((q))`, its injectivity, `evalAtJK`, and `conj 1 = j(q)` |
| `Support/PoleBounds` | 250 | the product's pole bounds at the cusp: the leading `1` at `q ^ -(l*l + l)` and the vanishing at and below it |
| `Transpose` | 240 | subject: the transpose engine (`swapBivar` against mathlib's `Bivariate.swap`), the monic/degree bookkeeping, the pole-bound-to-degree dictionary, and the transposed evaluation |
| `Construction` | 816 | subject: descent to `Q((q))`, the descended family's shape, integrality, assembly of the datum, and the q-expansion dictionary of a descent |
| `Existence` | 734 | main result: distinct conjugates, `j(q ^ l)` not a polynomial in `j(q)`, the minimal polynomial, irreducibility, and `exists_phiIrreducible_evalSymm` |
| `Split` | 709 | main result and the seam: prime-level uniqueness and degree, the split over `Q` and over any field, the slot root API, the coefficient-degree bound, and the symmetry corollary |
| `LevelTwo` | 440 | main result: `Φ = Φ₂` |

The layer discipline is visible in the imports: `Construction` and `Transpose` import only the two support
modules and `Defs/*`, and neither imports the other, so the subject layer is flat. The main results sit
above them. `LevelTwo`'s thirty-six computation helpers are `private`; its only public declaration is
`phi_eq_phiTwo`.

A second discipline is the public surface. The seam is exactly `Existence` + `Split` (plus `LevelTwo` for
the fibre computation); no Laurent-series internals, no pole-bound lemmas, no descent machinery cross it.

## 4. Rebuilding without breaking: copy, don't import

The new modules keep the old public names (`exists_phiGenDescends`, `splits_prime_at_slot`,
`eval_swap_eq_zero_of_splits`, ...), because the retarget should be an import swap and not a rename. That
has a hard consequence: Lean forbids one import cone from containing two declarations with the same name,
so during development the new directory must be a **self-contained parallel copy** — it may import only
`Defs/*` and pure support modules, never an old cluster module. It does: its only imports are `Defs/*`,
`JqCoefficients`, `JqCoeffPositivity` and `ModularForms/PhiGenDescends`.

The old and the new theory therefore coexist as two disjoint import cones until the retarget, which is
legal and harmless. The verification loop is single-module and cheap:

```
lake env lean -o /tmp/x.olean FLTForHuman/ModularCurve/ModularEquation/Existence.lean
lake build FLTForHuman.ModularCurve.ModularEquation.Existence
```

No tree build. Each module of theory A was checked this way (4–9 s per module) while the old cluster was
still live, which is what made a seven-module rewrite safe to do incrementally.

Header hygiene for the new modules: the subject, the statement of what is proved, and nothing about
provenance — no pin, no checker, no topic references. The old headers keep that material; the new ones
are meant to be read as mathematics.

## 5. The retarget

The mapping used, old module to new home:

| old | new |
|---|---|
| `ModularPolynomialIrreducible`, `ModularPolynomialProperties` | `ModularEquation.Existence` |
| `ModularPolynomialUniqueness`, `PhiGenSplits`, `PhiGenSplitsAnyField` | `ModularEquation.Split` |
| `ModularPolynomialLevelTwo` | `ModularEquation.LevelTwo` |
| `PhiGenDescent`, `PhiGenIntegrality`, `PhiGenDescendsStructure`, `ModularPolynomialAssembly` | `ModularEquation.Construction` |
| `PhiGenPoleBounds` | `ModularEquation.Support.PoleBounds` |

Twenty-one library modules and the two spec consumers were re-pointed. Four fixes were needed beyond the
import swaps, and each is a lesson:

* `Degree/PhiData` defined `exists_modularPolynomialData_evalSymm`, now a corollary in `Split`; the copy
  was deleted.
* `ModularPolynomialUniquenessIrreducible` carried `evalSymm_of_prime` and the coefficient-degree-bound
  block, both now in `Split`; they were deleted, leaving the composite-level closure that belongs to B.
* `HeckeInputs/Integrality` had a `private theorem qExpand_jqNModC` whose name now collided with the
  public one in `Defs/TS`, which the new split brings into the cone. A private declaration cannot shadow
  a public one of the same name; it was renamed. This is the kind of failure that only shows up in the
  retarget, not in the copy.
* Stale oleans: after the import swap, four retargeted modules had not been rebuilt, and their old oleans
  still recorded imports of the retired modules, so a consumer loading them failed with a duplicate-name
  error from a module it never imported. The fix is to rebuild every module whose source changed; the
  check is `olean` mtime against source mtime.

## 6. Retiring the old modules

After the retarget no source under `FLTForHuman/` or `spec/` imports the eleven old modules. Deadness was
established from the import graph; `move_dead.py --dry-run` is module-scoped (it computes what is
unreachable from a module's *own* public API), so on a dead module's header it reports
`0 declarations, 0 lines` — which is the confirmation that nothing is left to move.

The eleven modules were moved to `Reserve/ModularCurve/` as **header-only** files: the original module
docstring with its `spec-pin:` wires, plus one line naming the new home. The bodies are gone because the
content is duplicated in the new theory. The wires stay because the deps tools count ported modules by
header, and the checker finds the pin mapping there; the empty modules are deliberately **not** listed in
`Reserve/README.md`.

The declaration-marker table needs the same pass: `spec/decl_markers.tsv` lost its twelve `pin:` / `own:`
rows for the removed modules, since the declarations they described no longer exist and the new modules
carry no wires.

## 7. What theory A still owes: the proofs

The restructuring changed one proof. Everything else is a move. The one rewrite is `eval_swap_eq_zero_of_splits`:
the old proof went *up* a level (`qExpand` applied to the K-vanishing, then `qEmbedT` injectivity, plus an
`hhom` identity reconciling two composites on `X`), because `qEmbedT` changes the nome and hence moves
`j(q ^ l)` to `j(q ^ (l * l))`. But the goal is a statement over `Q((q))`, and the index-preserving
`coeffEmb` carries `evalAtJqN` to `evalAtJK` directly: the composite identity
`(coeffEmb K).comp (evalAtJqN l) = evalAtJK K l` is two lines, and then the whole proof is that identity,
the product's root at `j(q)`, and injectivity of `coeffEmb`. Fifteen lines became nine, and the `hhom`
disappeared. The dictionary entry was updated with the code.

The rest of the old problems are still there, in rough order of how much they cost a reader:

* `LevelTwo` is a 440-line computation: a normal form for a Laurent series with a listed tail, seven
  coefficient lists and their convolutions, pinning four coefficients of `Φ` and then upgrading the
  agreement by the coefficient-degree bound. The mathematics is trivial (a monic cubic with three known
  roots is determined by its first coefficients); the proof is a table. This is the clearest candidate
  for a real rewrite.
* `Existence` carries the old refutation route: Vieta's sums, `j(q ^ l)` not in `Q[j(q)]`, and a
  factor-counting engine through `adjoinEmbedT` and a vanishing `q ^ -1` coefficient. It works, but it is
  written as a chain of proof steps, and the same conclusion is available from the degree count once B
  exists — which would be a different theory boundary, not a local cleanup.
* `Split`'s any-field half transports the split through the integral cyclotomic order: `cyclRing`,
  `iota`, `integral`, `zetaLift`. The argument is the pin's (010a), and it is the place where a
  base-change formulation would be shorter if the port ever wanted one.
* `Support/PoleBounds` is 250 lines with twelve private helpers (`coeff_mul_lead`,
  `pow_sum_range_isPrimitiveRoot`, `prod_inv_pow_isPrimitiveRoot`, ...) for a statement about a product of
  linear factors at a cusp. The `q`-expansion content is clear; the formalisation is old-style.
* `Construction` is a merge of five old modules. The descent is the real proof and reads as such; the
  assembly (`exists_intPoly`, `exists_modularPolynomialData_coeff_eq`) is a transcription, and
  `splits_of_descends` / `coeff_poleBounds_of_splits` are port-authored staging statements that a rewrite
  should probably inline.
* `Transpose` still bridges to mathlib's bivariate API through one private `swapBivar_eq_swap` because
  `swapBivar` is the port's own ring hom. Using mathlib's `Bivariate.swap` directly would delete the
  bridge and the bookkeeping that goes with it.

None of these is a correctness problem. They are the difference between a module that has been *moved*
and one that has been *written*.

## 8. The deferred half

Theory B (the level tower) gets the same treatment later, and its shape is not yet decided. What is
already certain from the seam: B's content includes the composite-level modular-polynomial facts (general
uniqueness, irreducibility, existence, the leading coefficient, the resultant route) because they are
proved from B's degree count; and B must import exactly `Existence` and `Split` from A. The rest — the
spine of the strong induction, the two instances, the slot arithmetic, the non-membership — is a design
question for later.

## 9. Numbers

| | modules | lines |
|---|---|---|
| old cluster, retired | 11 | 3984 |
| theory A, new | 7 | 3266 |

Retarget touched 21 library modules and 2 spec consumers; 4 modules needed more than an import swap;
12 marker rows were removed; 11 modules moved to `Reserve`.

Verification: every theory-A module typechecked on its own and was built singly; after the retarget, the
target set `HeckeCommuteBar`, `FunctionFieldGeneration.Capstone`, the composite-closure modules, the six
moduli consumers (`Velu`, `StarBank`, `Coset`, `EvalJ`, `FibreTwo`, `E4Cube`), `LeadingCoeff`,
`UniquenessIrreducible` and the four stale retargeted modules built green (exit 0), and both spec
consumers typechecked. No tree build was run: it is expensive and the target set covers the dependency
cone of everything that changed.
