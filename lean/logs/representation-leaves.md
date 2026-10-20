# The `Representation` leaves — five mathlib-shaped modules (R2)

**Status: landed 2026-10-20.** Five new modules, one per pin node, **955 port lines**, **21
statement-checked declarations**, `0 mismatch / 0 missing / 0 own / 0 kw`, 0 warnings, all Lean
invocations serialized on `.lake/flt_build.lock` (the sibling descent port, R1, was elaborated
concurrently in the same tree). Record of the audit and the split:
[TOPIC-ds-leaf-families.md](../topics/deligneSerre/TOPIC-ds-leaf-families.md) §7.5; order:
[WORKORDER-R2-representation-leaves.md](../topics/deligneSerre/WORKORDER-R2-representation-leaves.md).

| module (`FLTForHuman/…`) | node | pin lines | port lines | checked |
|---|---|---:|---:|---:|
| `RepresentationTheory/Burnside.lean` | `Representation.span_range_eq_top_of_isIrreducible` | 151 | 175 | 1 |
| `RepresentationTheory/InvariantPairing.lean` | `Representation.pairing_eq_zero_of_invariant_of_isSimpleOrder_of_exists_ne_zero` | 36 | 82 | 1 |
| `RepresentationTheory/CompactGroup.lean` | `Representation.exists_isCompl_forall_mem_of_compactSpace_of_continuous` | 112 | 176 | 1 |
| `RepresentationTheory/SubrepresentationExtension.lean` | `Representation.exists_extend_forall_apply_mul_of_injective` | 69 | 119 | 1 |
| `LinearAlgebra/Matrix/SubfieldBasis.lean` | `Representation.exists_basis_toMatrix_mem_subfield_of_trace_det_mem_of_hasEigenvalue` | 291 | 403 | 17 |

Per module, `python3 spec/check_port.py <module>`: `1/1/1/1/17 ok`, 0 mismatch, 0 missing; all five
with `--force --strict-markers`: `21 ok, 0 mismatch, 0 missing, 0 own, 0 kw — 5 module(s)`.

**Homing.** The five are mathlib-shaped mathematics and live where mathlib would put them
(`RepresentationTheory/`, `LinearAlgebra/Matrix/`), not under an FLT subject directory; each header
says so and carries `spec-pin:` for the pin `S_` file **and** its `Theorems/` wrapper, keeping the
pin's `P2MW.S_…` namespace and names (the checker matches by name and by statement hash).

**The one edit to an existing module.** `RepresentationTheory/BrauerNesbitt.lean` promotes
`Representation.range_asAlgebraHom_toLinearMap` and
`Representation.span_range_eq_top_iff_surjective_asAlgebraHom` from `private` to public (statements
untouched); `Burnside.lean` imports them instead of re-proving 20 lines. The checker now reads that
module as **3 ok** — the promoted pair is a pin declaration, so the promoted-from-pin-private
fallback diffs it and no `own:` row is owed.

## mathlib first — the audit the order existed for

Every declaration (the five headline nodes and each private helper) was searched in mathlib, and the
result is a line in the module header. **All are negatives**: the pin's proof is transcribed. What
mathlib *did* supply is used verbatim as ingredients rather than re-proved:

* **Burnside** — no Burnside/spanning theorem in mathlib; Schur (`IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed`),
  Jacobson density (`jacobson_density`) and `irreducible_iff_isSimpleModule_asModule` are the proofs'
  ingredients. The pin-private `surjective_toModuleEnd_of_surjective_algebraMap_end` is *not* mathlib's
  `Module.Finite.toModuleEnd_moduleEnd_surjective` (different hypotheses).
* **InvariantPairing** — no invariant-pairing theorem; `IsSimpleOrder (Subrepresentation ρ)` and
  `IsSimpleOrder.eq_bot_or_eq_top` carry the proof.
* **CompactGroup** — no compact-group invariant-complement theorem; mathlib's only invariant
  complement is Maschke's finite-group `exists_isCompl`, not applicable (the pin's hypothesis is a
  compact topological group with a weak continuity condition). `MeasureTheory.integral_mul_left_eq_self`
  + `Measure.haarMeasure_self` carry the averaging.
* **SubrepresentationExtension** — no extension theorem; `QuotientGroup.mk_out_eq_mul` and
  `Submodule.projectionOnto` carry it.
* **SubfieldBasis** (17 declarations) — no `2×2`/charpoly-subfield statement in mathlib;
  `basisOfLinearIndependentOfCardEqFinrank`, `LinearIndependent.pair_iff`,
  `LinearMap.toMatrix{,_mul,_apply}`, `trace_eq_matrix_trace`, `det_toMatrix`,
  `HasEigenvalue.hasEigenvector` are the proofs as written.

## Builds, axioms, deviations

* `lake build` green, 0 warnings (wall): `SubrepresentationExtension` 4.20 s, `InvariantPairing`
  5.35 s, `CompactGroup` 4.79 s, `Burnside` 4.05 s, `SubfieldBasis` 6.93 s;
  `RepresentationTheory/BrauerNesbitt` after the promotion 5.74 s. Edit loop at the 200k cap: 3.0–5.9 s.
  The 291-line node's pin `set_option maxHeartbeats 6400000` is **not** carried and not needed.
* axioms: four headlines `[propext, Classical.choice, Quot.sound]`; `InvariantPairing` is
  `[propext, Quot.sound]` (a subset — no `Classical` in that proof). No `sorry`, no axioms, no
  statement weakened or renamed.
* **three linter suppressions**: `set_option linter.style.haveILetI false` in `Burnside`,
  `CompactGroup`, `SubfieldBasis`. v4.34's style linter wants `have` where the pin writes `haveI`/`letI`,
  and those instances are consumed by later elaboration — rewriting them would break the proofs. 259
  modules in the port already carry this option; no statement is touched.
* **one dedup decision**: the Burnside node's third helper `trace_asAlgebraHom_eq_of_forall_trace_eq`
  is *not* redeclared there — the port already has it private, with the pin's exact name and
  statement, in `RepresentationTheory/BrauerNesbitt.lean`, where its only consumer is §2.4.
* the pin's `span_range_eq_top_of_isIrreducible` is `private` in the `S_` file and public in the
  wrapper: declared once, public, with the wrapper's binders (§7.4).

## The family is complete

The sixth node, `Representation.exists_conj_eq_map_of_charpoly_coeff_mem_range_of_finite_of_span_range_eq_top`
(1,692 lines, 105 public declarations), landed the same day as
[WORKORDER-R1-descent-charpoly.md](../topics/deligneSerre/WORKORDER-R1-descent-charpoly.md) — three
`GaloisRep/Deformation/` modules, 1,938 port lines, 103 checked, record
[logs/descent-charpoly.md](descent-charpoly.md). The `Representation` family is therefore complete:
six nodes, 2,351 raw pin lines, eight modules, **124 checked declarations** (21 + 103), 0 mismatch /
0 missing; global checker **3,010 ok / 0 mismatched / 0 missing / 11 own / 0 kw over 117 wired
modules**.
