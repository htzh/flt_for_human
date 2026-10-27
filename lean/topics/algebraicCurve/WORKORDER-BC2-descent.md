# WORKORDER BC2 — descent to a countable algebraically closed constant field (Lefschetz)

Scope: port **three** pin nodes, which are one development with three headlines, into **one new
module**. Do not touch any other file. Statements come from the `Theorems/` wrappers; proofs
from the `S_` files.

## Pin sources (pinned `aa2d8b3`, clone at `~/proj/fermats-last-theorem`)

| node | wrapper (statement authority) | proof |
|---|---|---|
| `AlgebraicCurve.exists_constantFieldDescent` | `Theorems/Thm_AlgebraicCurve_exists_constantFieldDescent.lean` | `P2M/Sol/S_AlgebraicCurve_exists_constantFieldDescent.lean` (270) |
| `…_finset` | `…/Thm_AlgebraicCurve_exists_constantFieldDescent_finset.lean` | `…/S_AlgebraicCurve_exists_constantFieldDescent_finset.lean` (306) |
| `…_correspondence` | `…/Thm_AlgebraicCurve_exists_constantFieldDescent_correspondence.lean` | `…/S_AlgebraicCurve_exists_constantFieldDescent_correspondence.lean` (558) |

**The mathematics.** `K` algebraically closed of characteristic zero, `F/K` a curve with a
transcendental element whose `K⟮x⟯` is finite over `F`. The pin descends both to a
**countable** algebraically closed `K₀ ⊆ K` and `F₀ ⊆ F`: it cuts `K` down to the algebraic
closure of a finitely generated field (`isAlgebraic_of_rational_relation`,
`nonempty_ringHom_complex` supplies the `K₀ → ℂ` embedding), and shows the transcendence and
finiteness data, the curve structure and (in the third headline) a whole finite family of
correspondence roofs survive (`descent_abstract`, `restrictHom`, `finiteAlong_of_…`).

## The three pin files share a prelude — write it once

`port_advise` measures **105 duplicate lines** across the trio:
`descent_abstract` 45, `isAlgebraic_of_rational_relation` 34, `nonempty_ringHom_complex` 26
(copies in all three files), plus `aeval_mem_of_lift` (11) and `aeval_mem_of_repr` (14–18) twice.

| declaration | copies | statement | how to write it |
|---|---:|---|---|
| `nonempty_ringHom_complex` | 3 | identical | **once**, public |
| `isAlgebraic_of_rational_relation` | 3 | identical | **once**, public |
| `descent_abstract` | 3 | **two different statements** (`_correspondence` and `_finset` differ) | **both**, in **two namespaces** — never merge them |
| `aeval_mem_of_lift` | 2 | identical | once |
| `aeval_mem_of_repr` | 2 | 18 vs 14 lines (same statement) | once, the longer proof |
| `exists_constantFieldDescent_core` | 1 | line 224 of file 1 | public |
| `core` | 2 | two statements (files 2 and 3) | both, two namespaces |
| `finiteDimensional_adjoin_map`, `restrictHom`, `coe_restrictHom`, `finiteAlong_of_isIntegral_of_adjoin_eq_top`, `finiteAlong_of_transcendental_image` | 1 each | file 3 | public |

The three files' own namespaces are machine tokens (`W4B`, `W7XDesc`) — **rectify** them: the
whole development goes under `AlgebraicCurve.ConstantFieldDescent`, with one sub-namespace for
the second spelling of each same-name/different-statement pair (the pin's precedent for such a
pair is a namespace split, never a rename). The three headlines end up at
`AlgebraicCurve.exists_constantFieldDescent{,_finset,_correspondence}` — the wrappers' names.

## Use the port, do not re-derive

`essFiniteType_of_fg'` and `hasCanonicalDivisor_of_charZero'` in the pin files are the port's
public `AlgebraicCurve.essFiniteType_of_fg` and `AlgebraicCurve.hasCanonicalDivisor_of_charZero`
(`IsCurveOver/ConstantFieldExtensionExists.lean`): import and use them, do not declare local
copies. Everything else in the trio is new to the port (`port_advise`: `prelude 0/…`).

## Traps

1. **The `∃`-packed conclusions** are 10–15 instance binders each, including `Algebra K₀ ℂ`,
   `IsAlgClosed K₀`, `Countable K₀` and two `IsScalarTower`s. Copy the wrapper's binder block
   character for character; the checker diffs it. Universes: file 1 and 2 use `u v`, file 3 adds
   `w x` for the roof family — take each wrapper's own `universe` line.
2. `Countable K₀` is a hypothesis in the conclusion, not an instance you can synthesize: it
   comes from the construction (a countable algebraic closure of a finitely generated field).
3. Keep the pin's `letI`/`haveI` walls and its `Algebra k F`/`IsScalarTower` `letI`s inside the
   proofs; the module carries `set_option linter.style.haveILetI false` for that reason.
4. `AlgebraicClosure`/`Cardinal` API drift is likely; adapt the tactic/namespace, never a
   statement.

## Build and check discipline

- **Never a tree build.** Edit loop:
  `timeout 110 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldDescent.lean`
  from `lean/`. Finished file:
  `flock .lake/flt_build.lock timeout 110 lake build FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldDescent`.
- Every command under 2 minutes with its own `timeout`; no loops around the cap. Long output
  to `lean/tmp/bc2-build.log`, then read the log.
- Header of the module: a `/- … -/` block with one `spec-pin:` line per pin file named above
  (all six), 6–10 lines of prose on the mathematics, no cross-references to port modules or
  notes. `set_option autoImplicit false`.
- `python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldDescent.lean`
  → target **0 mismatch, 0 missing** (`ok` count = every public declaration of the module).
- `#print axioms` on the three headlines in `lean/tmp/axioms-bc2.lean`, each
  `[propext, Classical.choice, Quot.sound]`; 0 warnings; no `sorry`/`admit`/`axiom`.

## Report (one message)

build + warnings, the checker summary line, the three axioms lines, the declarations whose
proof deviates from the pin beyond a tactic rename (one line each), and any blocker at first
belief — a missing port declaration, an instance that will not synthesize, a statement that
will not diff. Never weaken a statement, never edit a hub module, never deliver a `sorry`.
