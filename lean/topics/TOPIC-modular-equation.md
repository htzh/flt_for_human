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

`FLTForHuman/ModularCurve/ModularEquation/` holds five subject modules over four support modules.

| module | lines | role |
|---|---|---|
| `Support/LevelEmbedding` | 77 | the level-`l` nome embedding `Q((q)) -> K((q))`, its injectivity, `evalAtJK`, and `conj 1 = j(q)` |
| `Support/Descent` | 139 | the range tests behind the descent: a twist-fixed series is a level-`l` expand (`mem_range_qExpand_of_qTwist_eq`), a Galois-fixed series is rational (`mem_range_coeffEmb_of_forall_coeffMap_eq`), and their intersection is the image of `coeffEmb ∘ qExpand` (`mem_range_coeffEmb_qExpand_of_mem_inter`); the private contraction `qContract` |
| `Support/PoleBounds` | 250 | the product's pole bounds at the cusp: the leading `1` at `q ^ -(l*l + l)` and the vanishing at and below it |
| `Support/Permutation` | 267 | three sections: *products under a permutation* (`map_prod_of_perm`: any finite family, any permutation of it, any coefficient endomorphism); *the twist's permutation* (`twistPerm`, its label formula and only fixed point, `qTwist_conj`, and its factorwise form); *the Galois permutation* (`galExp`, the value of the cyclotomic character, `galLabelPerm` — labels multiplied by it, `galPerm`, `coeffMap_conj`, and its factorwise form); also `Fin.succEquivOfEquiv` |
| `Transpose` | 240 | subject: the transpose engine (`swapBivar` against mathlib's `Bivariate.swap`), the monic/degree bookkeeping, the pole-bound-to-degree dictionary, and the transposed evaluation |
| `Construction` | 438 | subject: descent to `Q((q))`, the integrality of the descended family, and the assembly of the datum; one public constructor `exists_modularPolynomialData_splits` |
| `Existence` | 782 | main result: distinct conjugates, `j(q ^ l)` not a polynomial in `j(q)`, the minimal polynomial, irreducibility, the two read-offs of the descent (private), and `exists_phiIrreducible_evalSymm` |
| `Split` | 697 | main result and the seam: prime-level uniqueness and degree, the split over `Q` and over any field, the slot root API, the coefficient-degree bound, and the symmetry corollary |
| `LevelTwo` | 440 | main result: `Φ = Φ₂` |

The layer discipline is visible in the imports: `Transpose` imports only the support modules and `Defs/*`;
`Construction` additionally imports `Support/LevelEmbedding`, `Support/Descent`, `Support/Permutation`
and the analytic j-line membership `ModularForms/PhiGenDescends`, which is the one cross-area input it
consumes. Neither imports the other, so the subject layer stays flat. The main results sit above them.
`LevelTwo`'s thirty-six computation helpers are `private`; its only public declaration is
`phi_eq_phiTwo`.

A second discipline is the public surface. `Existence` and `Split` consume one constructor,
`exists_modularPolynomialData_splits`, which returns the datum together with its map to `phiProd`; they
do not see the descended family `c`, the assembly, or the coefficient equality. The only other
crossing is `evalAtJ_injective`.

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

**Build scope while the theory is being rewritten.** Only modules of the theory itself. Consumers are not
built: a public-name change inside the theory is recorded as an API delta (by `grep`, not by compiling
the downstream cone) and paid for at the next retarget. Building the consumers on every change is the
friction that stops refactoring; a single consumer, on request, is the most that is worth running.

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
* `Construction` is a merge of five old modules. The general range tests behind the descent live in
  `Support/Descent`: `mem_range_qExpand_of_qTwist_eq` (a twist-fixed series is a level-`ell`
  expand), `mem_range_coeffEmb_of_forall_coeffMap_eq` (a Galois-fixed series is rational), and
  `mem_range_coeffEmb_qExpand_of_mem_inter` (their intersection). Rationality is the fixed-field
  theorem `IsGalois.mem_range_algebraMap_iff_fixed`, applied coefficientwise in
  `mem_range_coeffEmb_of_forall_coeffMap_eq`; the cyclotomic action is used only to prove
  `gal_fixes`. `exists_phiGenDescends` is now a short application of the three range tests.
  The public constructor consumed by `Existence` and `Split` is
  `exists_modularPolynomialData_splits`: it consumes `exists_phiGenDescends`,
  `PhiGenDescends.intCoeffs`, `mem_adjoin_jq_of_phiGenDescends` and
  `exists_modularPolynomialData_coeff_eq`, and returns the datum together with its map to
  `phiProd`. Its parameters are only `ell`, `zeta` and `hzeta`: the cyclotomic field's
  `IsCyclotomicExtension` and `IsGalois` are established locally, and `FiniteDimensional` follows
  from them. The generic `exists_phiGenDescends` and the range lemmas in `Support/Descent` keep
  `[IsGalois]`/`[FiniteDimensional]` because they are stated over an arbitrary field `K`.
  `Split.splits_of_prime` keeps one local `IsCyclotomicExtension`, because mathlib's
  `IsPrimitiveRoot.embeddingsEquivPrimitiveRoots` takes that instance as a section variable.
  The contraction `qContract` is private in `Support/Descent`. The permutation work is split into
  two levels: the generic fact (`Polynomial.map_prod_of_perm`: any finite family, any permutation, any
  coefficient endomorphism) and the exhibited pairs for the two symmetries (`twistPerm` with
  `qTwist_X_sub_C_conj`; `galPerm` with `coeffMap_X_sub_C_conj`, the latter through the value `galExp`
  of the cyclotomic character). Both `twist_fixes` and `gal_fixes` in the descent are now single lines —
  the generic theorem applied to an exhibited pair — so the descent carries **no** permutation
  hypothesis at all. What is left in that module is the cycle structure: the iteration `b ↦ b + n` on
  the labels, order `ℓ`, and transitivity on the finite cusps (the arithmetic form of "`twistPerm` is
  one `ℓ`-cycle"); the iteration needs the `Fin ℓ`-level rotation lemma, which is the missing piece.
  **The assembly has since been written, not moved.** Its shape now is: for each `k` an integer
  polynomial `Q k` with `Q k (jq) = c k`, obtained from the *polar* part of `c k`
  (`IntPoleCoeffs`, the private sharpening of `IntCoeffs` — the triangularity of `j` reads only the
  nonpositive exponents, so no pole bound is threaded); the sum `Φ = ∑ Q k (X) Y^k`; and one
  coefficientwise identity `Φ.map (evalAtJK K ℓ) = phiProd ℓ (conj ℓ ζ)`. Monicity, degree `ψ(ℓ)`
  and vanishing at `j(q^ℓ)` are the *product's* properties, pulled back along the injective level
  embedding by three one-line transports (`monic_of_map_eq_phiProd`,
  `natDegree_of_map_eq_phiProd`, `eval₂_eq_zero_of_map_eq_phiProd`), so the module no longer states
  the descended family's own shape: `PhiGenDescends.c_top`, `.c_eq_zero`, `.poleOrderLE`,
  `.sum_mul_jqN_pow_eq_zero`, the intermediate `exists_modularPolynomialData_coeff_eq`, the private
  `exists_intPoly`/`splits_of_descends`/`coeffEmb_qExpand_injective` and the old assembly haves are
  gone. The public surface is four statements (`exists_phiGenDescends`,
  `PhiGenDescends.intCoeffs`, `evalAtJ_injective`, `exists_modularPolynomialData_splits`); the
  dictionary entry is [ModularEquation/Constructions.md](../dict/ModularCurve/ModularEquation/Constructions.md)
  — one entry for the whole theory.
  `coeff_poleBounds_of_splits` is private in `Existence`.
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
| theory A, now | 9 | 3332 |

Retarget touched 21 library modules and 2 spec consumers; 4 modules needed more than an import swap;
12 marker rows were removed; 11 modules moved to `Reserve`.

Verification: every theory-A module typechecked on its own and was built singly; after the retarget, the
target set `HeckeCommuteBar`, `FunctionFieldGeneration.Capstone`, the composite-closure modules, the six
moduli consumers (`Velu`, `StarBank`, `Coset`, `EvalJ`, `FibreTwo`, `E4Cube`), `LeadingCoeff`,
`UniquenessIrreducible` and the four stale retargeted modules built green (exit 0), and both spec
consumers typechecked. No tree build was run: it is expensive and the target set covers the dependency
cone of everything that changed.
