# Work order — S5: semisimple descent of a reducible residual representation (1 node)

**Status: ready to dispatch — H and S1–S4 are closed and green (checker 2463/0/0).**
Independent of S1–S4 and of the H homes. Method handbook:
`lean/porting-playbook.md` (§3.1–§3.5, §4). Mathematics: `math/019` §4.

## 0. Scope

If the trace and the determinant of a residual representation lie in a subfield,
the two characters descend and the representation is semisimple over that subfield
(the finite-field Frobenius argument `x ↦ x ^ q`). One node, 675 pin lines.

**Explicitly not this set:** everything else. Edit only the new module below.

## 1. The public target — statement verbatim

```lean
theorem DeligneSerre.exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range
    {G : Type} [Group G] {κ : Type} [Field κ] [Finite κ] {Ω : Type} [Field Ω]
    (ι : κ →+* Ω) (χ₁ χ₂ : G →* Ωˣ)
    (hadd : ∀ g : G, (χ₁ g : Ω) + χ₂ g ∈ ι.range) (hmul : ∀ g : G, (χ₁ g : Ω) * χ₂ g ∈ ι.range) :
    ∃ ρ : G →* GL (Fin 2) κ,
      (Deformation.matrixRepresentation ρ).IsSemisimpleRepresentation ∧
      (∀ g : G, χ₁ g = 1 → χ₂ g = 1 → ρ g = 1) ∧
      ∀ g : G, (((ρ g : GL (Fin 2) κ) : Matrix (Fin 2) (Fin 2) κ).map ι).charpoly =
        (X - C (χ₁ g : Ω)) * (X - C (χ₂ g : Ω))
```

## 2. Home and route

New module `FLTForHuman/GaloisRep/SemisimpleDescent.lean`, namespace `DeligneSerre`
(the pin's name).

**Dedup against the deferred sibling (scouting report, confirmed).** The pin
duplicates three engines verbatim in two files: the in-scope node's file (private
namespace `DSRed`) and the **out-of-scope** sibling
`S_GaloisRep_exists_isSemisimpleRepresentation_charpoly_map_eq_of_trace_det_frobenius_mem_range.lean`
(namespace `DSRt`), which belongs to the deferred density-dependent half and is not
one of the 54 nodes. The shared blocks are `charpoly_fin_two`,
`finrank_eq_one_of_ne_bot_of_ne_top` and
`isSemisimpleRepresentation_of_forall_exists_isCompl`. Home these **publicly** (in
`GaloisRep/SemisimpleDescent.lean`, or a small shared module it exports) rather than
`private`, so the deferred half imports them instead of re-proving them; log the
choice. The pin's `DSRt.main` additionally imports the ported
`DeligneSerre.exists_isSemisimpleRepresentation_…` target, so that half will be
glue once this set lands. It imports `FLTForHuman/GaloisRep/Defs/MatrixRepresentation.lean`
(phase D: `Deformation.matrixRepresentation`) and the mathlib
`Representation.IsSemisimpleRepresentation` API; it needs no H home.

Route: finite-field representation theory. The two characters give a candidate
`GL (Fin 2) κ`; the Frobenius `x ↦ x ^ q` (`q = Nat.card κ`) makes the
`ι.range`-membership hypotheses usable. `#check` the mathlib lemmas for
`IsSemisimpleRepresentation` (Maschke/semilocal), `Submodule`-invariance and
`Matrix.charpoly` before transcribing. Keep helpers `private`; record a negative for
any search that finds nothing.

## 3. Verification, build discipline, closing

As `WORKORDER-S1-eisenstein.md` §4: checker wiring (`PORT_FILES` + the pin `S_` in
`SOURCES`) appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.GaloisRep.SemisimpleDescent`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands.

---

## Appendix — pin declaration inventory

#### S5 — pin `P2M/Sol/S_DeligneSerre_exists_isSemisimpleRepresentation_charpoly_map_eq_of_add_mem_range_of_mul_mem_range.lean` (675 lines, 63 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `charpoly_fin_two` | theorem | 16 | 28 |  |
| `isCompl_of_finrank_eq_one_of_ne` | theorem | 44 | 24 |  |
| `finrank_eq_one_of_ne_bot_of_ne_top` | theorem | 68 | 16 |  |
| `isSemisimpleRepresentation_of_forall_exists_isCompl` | theorem | 84 | 37 |  |
| `map_pow_card` | theorem | 121 | 2 |  |
| `add_pow_card` | theorem | 123 | 9 |  |
| `sub_pow_card` | theorem | 132 | 3 |  |
| `mem_range_of_pow_card_eq` | theorem | 135 | 29 |  |
| `exists_eq_add_mul_of_pow_card_sq_eq` | theorem | 164 | 64 |  |
| `pow_card_eq_or` | theorem | 228 | 20 |  |
| `pow_card_eq_or'` | theorem | 248 | 4 |  |
| `chi2_mem_range_of_chi1_mem_range` | theorem | 252 | 5 |  |
| `chi2_eq_pow_of_not_mem` | theorem | 257 | 46 |  |
| `pullbackChar` | def | 303 | 9 |  |
| `map_pullbackChar` | theorem | 312 | 14 |  |
| `diagGL` | def | 326 | 13 |  |
| `diagRep` | def | 339 | 11 |  |
| `diagRep_val` | theorem | 350 | 4 |  |
| `axis` | def | 354 | 2 |  |
| `finrank_axis` | theorem | 356 | 3 |  |
| `axis_zero_ne_axis_one` | theorem | 359 | 7 |  |
| `diagonal_mulVec_mem_axis` | theorem | 366 | 7 |  |
| `diagRep_isSemisimple` | theorem | 373 | 21 |  |
| `charpoly_map_diagRep` | theorem | 394 | 10 |  |
| `_root_.DSRed.comp` | def | 404 | 4 | yes |
| `elt` | def | 408 | 3 |  |
| `elt_mul` | theorem | 411 | 6 |  |
| `trace_elt` | theorem | 417 | 3 |  |
| `det_elt` | theorem | 420 | 3 |  |
| `elt_one_zero` | theorem | 423 | 2 |  |
| `BData` | structure | 425 | 15 |  |
| `chi2_eq` | theorem | 440 | 3 |  |
| `x0_pow` | theorem | 443 | 2 |  |
| `x0_pow_pow` | theorem | 445 | 10 |  |
| `pow_pow_eq` | theorem | 455 | 13 |  |
| `coord_unique` | theorem | 468 | 16 |  |
| `exists_coord` | theorem | 484 | 4 |  |
| `coord` | def | 488 | 2 |  |
| `coord_spec` | theorem | 490 | 4 |  |
| `t0` | def | 494 | 2 |  |
| `d0` | def | 496 | 2 |  |
| `t0_spec` | theorem | 498 | 3 |  |
| `d0_spec` | theorem | 501 | 3 |  |
| `x0_sq` | theorem | 504 | 3 |  |
| `coord_eq_of` | theorem | 507 | 7 |  |
| `coord_one` | theorem | 514 | 2 |  |
| `coord_g0` | theorem | 516 | 2 |  |
| `coord_mul` | theorem | 518 | 17 |  |
| `mat` | def | 535 | 2 |  |
| `mat_one` | theorem | 537 | 3 |  |
| `mat_mul` | theorem | 540 | 3 |  |
| `map_trace_mat` | theorem | 543 | 6 |  |
| `map_det_mat` | theorem | 549 | 7 |  |
| `det_mat_ne_zero` | theorem | 556 | 6 |  |
| `repB` | def | 562 | 5 |  |
| `repB_val` | theorem | 567 | 2 |  |
| `charpoly_map_mat` | theorem | 569 | 7 |  |
| `charpoly_map_repB` | theorem | 576 | 5 |  |
| `repB_eq_one` | theorem | 581 | 5 |  |
| `no_root` | theorem | 586 | 13 |  |
| `repB_isSemisimple` | theorem | 599 | 33 |  |
| `main` | theorem | 632 | 34 |  |
| `solution` | theorem | 666 | 10 |  |
