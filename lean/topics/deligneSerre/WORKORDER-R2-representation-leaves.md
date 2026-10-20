# WORKORDER-R2 — the five small `Representation` leaves (mathlib-shaped homes, mathlib-first)

**Status: landed 2026-10-20** (five modules, 21 checked; record
[logs/representation-leaves.md](../../logs/representation-leaves.md)). Five ready leaves of the D-S cone's
`Representation` family (`TOPIC-ds-leaf-families.md` §7.5; `frontier.py --ds --include-leaves
--ready` lists all five). They are mathlib-shaped mathematics, so they are **homed in mathlib's own
layout** (`RepresentationTheory/`, `LinearAlgebra/`), not under an FLT subject directory.

## 1. Scope

| node | pin file (`P2M/Sol/`) | lines | publics | new private |
|---|---|---:|---:|---|
| `Representation.exists_extend_forall_apply_mul_of_injective` | `S_Representation_exists_extend_forall_apply_mul_of_injective.lean` | 69 | 1 | 0 |
| `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous` | `S_Representation_exists_isCompl_forall_mem_of_compactSpace_of_continuous.lean` | 112 | 1 | 0 |
| `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` | `S_Representation_pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero.lean` | 36 | 1 | 0 |
| `Representation.span_range_eq_top_of_isIrreducible` | `S_Representation_span_range_eq_top_of_isIrreducible.lean` | 151 | 1 | 2 (65 lines) |
| `Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` | `S_Representation_exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue.lean` | 291 | 17 | 0 |

Each has a `Theorems/Thm_…` wrapper carrying the statement authority; take every node **whole**
(§2.3), nothing to home, no `Definitions/` gate (the only non-mathlib import is `P2M.Util`).
`~590 declaration lines, ~545 net new` (44 lines already in the port); 5 wired headlines plus the
291-line node's 17 publics.

*Not this topic:* the big descent node (WORKORDER-R1); the `BrauerNesbitt` node (ported).

## 2. Homes — mirror mathlib, one module per node

| node | module |
|---|---|
| `span_range_eq_top_of_isIrreducible` (Burnside/Brauer–Nesbitt) | `FLTForHuman/RepresentationTheory/Burnside.lean` |
| `pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` (invariant pairing) | `FLTForHuman/RepresentationTheory/InvariantPairing.lean` |
| `exists_isCompl_forall_mem_of_compactSpace_of_continuous` (compact-group invariant complement) | `FLTForHuman/RepresentationTheory/CompactGroup.lean` |
| `exists_extend_forall_apply_mul_of_injective` (extending a functional from a subrepresentation) | `FLTForHuman/RepresentationTheory/SubrepresentationExtension.lean` |
| `exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` (2-dim rep, trace/det in a subfield) | `FLTForHuman/LinearAlgebra/Matrix/SubfieldBasis.lean` |

The directory is the claim: a module here is a mathlib supplement, and its header says so. If a
node's subject is not what the table says, put it where mathlib would and record the reason.

## 3. mathlib-first — the substitution audit this order exists for

Before transcribing any declaration (the node **and** each of its helpers — the pin-private ones
too), search mathlib for the statement:

```bash
rg -n --multiline '<distinctive token of the statement>' .lake/packages/mathlib/Mathlib | head
```

For `span_range_eq_top_of_isIrreducible` start from `Burnside`, `span_range`, `IsIrreducible`; for
the compact-group node from `RepresentationTheory/Continuous` + averaging over a compact group
(`MeasureTheory`/`Haar`); for the pairing node from `IsSimpleOrder`/`Subrepresentation`/invariant
pairing; for the 291-line node from `charpoly`, `Subfield`, `Matrix.toMatrix`, `HasEigenvalue`,
`Module.finrank = 2`; for the extension node from `LinearMap` extension along an injective monoid
hom and `Representation`.

* if mathlib **states the same theorem**, prove the pin's declaration by `exact`/`simpa` of the
  mathlib lemma and record the hit;
* if mathlib states it **under another name or with different binders**, keep the pin's name and
  statement (the wire needs them) and note the equivalence;
* if mathlib has nothing, transcribe the pin's proof;
* a **negative** must also be recorded: one line per declaration, in the module header, saying
  which mathlib area was searched and what was found (`§6`'s "mathlib-first" rule).

The port already holds two of `span_range`'s helpers as **private** in
`FLTForHuman/RepresentationTheory/BrauerNesbitt.lean` (`range_asAlgebraHom_toLinearMap` 15 lines,
`span_range_eq_top_iff_surjective_asAlgebraHom` 5). **Promote them** (they are pin declarations;
the checker's promoted-from-pin-private fallback diffs them) and import, rather than re-prove; the
node's two remaining helpers (`surjective_toModuleEnd_of_surjective_algebraMap_end` 35,
`span_range_eq_top_of_isIrreducible` 30) are new and stay `private` unless the pin has them public.

## 4. Deliverable

Five modules as in §2, each carrying `spec-pin:` for its S_ file **and** its `Theorems/Thm_` file,
keeping the pin's `P2MW.S_…` namespace and declaration names verbatim (the checker matches by name
and statement hash). No new public declaration that the pin does not have; if one is unavoidable,
stop and report. No `own:` rows are expected — if you believe one is owed, stop and report (the
manager adds it to `spec/decl_markers.tsv`).

## 5. Route and risks

**Stop-early risks, in order:** (i) the wrapper's binder shape differing from the S_ file's (take
the wrapper's for the wired statement, §7.4) — both `trace_eq_of_charpoly_eq` and
`span_range_eq_top_of_isIrreducible` show this in the pin; (ii) `ℂ`-valued representations in two
nodes — check whether `Module ℂ` can be generalised to a `RCLike`/`[IsROrC]` field without changing
the statement (it cannot for the wire; keep `ℂ`); (iii) the compact-group node's continuity
hypothesis (`∀ ℓ v, Continuous fun k => ℓ (π k v)`) is the pin's weak form — do not strengthen it;
(iv) the 291-line node's 17 publics are the real cost: read them as a group and check each against
mathlib before writing.

**Deviation protocol:** if a statement cannot be transcribed verbatim, stop and report — do not
weaken, rename or `own:` it.

## 6. Build discipline (copied)

Edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`; the cap
is a **diagnostic**, never raised; `lake build <module>` per finished module, bounded and
serialized. **The R1 agent shares this tree: put every `lake env lean` and every `lake build` under
`flock .lake/flt_build.lock` (`flock .lake/flt_build.lock timeout 120 lake env lean …`).** Never a
bare whole-tree `lake build`; no `set_option maxHeartbeats`; 0 warnings.

If a declaration blows the diagnostic, use the probe ladder (`logs/poisson-summation-statements.md`,
playbook §3.5).

## 7. Verification and report

* `python3 spec/check_port.py <module>` per module (and `--strict-markers` once): 0 mismatch,
  0 missing.
* `lake build <module>` green, 0 warnings; `#print axioms` on each of the five headlines =
  `[propext, Classical.choice, Quot.sound]`; `grep -c sorry` = 0.
* Report: the five modules and their lines, the wired count, the mathlib substitution per
  declaration (and the negatives), the build wall times, any deviation/blocker, and the checker's
  exact line.
