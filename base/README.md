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
quote Lean verbatim, and never cite an untracked local file.

## Notes so far

- [001 — Field extensions and Galois theory at the mathlib level](001-field-extensions-and-galois-basics.md):
  `Algebra` instead of "field tower", the `R → S → K` binders and why they are
  inherited rather than needed, algebraic/separable/normal, `IsAlgClosure`,
  the Galois group as the type `K ≃ₐ[S] K`, `Point.map` as the action,
  decomposition/inertia subgroups, and the finite vs. infinite Galois
  correspondence. The running example is `AlgebraicClosure ℚ`.

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
- **The automorphic side**: `CuspForm`, `CongruenceSubgroup.Gamma0`,
  `q`-expansions, Hecke operators, eigenforms, and how "weight 2 level N" is
  spelled in mathlib.

When a new note is added, extend the list above rather than renumbering.
