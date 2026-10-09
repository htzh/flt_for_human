# WORKORDER-W2 — full level structure and the division field

**Status: ready to dispatch (2026-10-08).** Second set of the `WeierstrassCurve` ready shelf,
scoped in [TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md) §2B and §6
(story B). **Two new modules, in this order**, mutually independent — neither imports the
other, so the order is smallest-first only to get an early green. Predecessor:
[WORKORDER-W1-automorphisms.md](WORKORDER-W1-automorphisms.md) (its §11 records the
conventions this order assumes). No existing module is edited and **no definition-layer work
and no promotion is needed** (§0).

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Torsion/NatCardStructure.lean` | `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq` | `S_…_of_natCard_torsion_eq_sq.lean` (68) |
| 2 | `FLTForHuman/WeierstrassCurve/Torsion/DivisionField.lean` | `WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq` | `S_…_card_torsion_eq_sq.lean` (842) |

The module paths are the reviewer's proposal; if the mathematics admits a leaf-side home,
re-home and record it, but do not split one theory across modules. Verify order 1 before
starting order 2.

## 0. What is already in the port

Both headlines have exactly **one** premise, and it is ported:

* `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` — public in
  `FLTForHuman/Elliptic/TorsionZMod.lean` (theorem at line 180), which imports
  `FLTForHuman.Algebra.ZModTorsion` (`AddCommGroup.nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq`)
  and `FLTForHuman.Elliptic.TorsionCard`. **Import, never redeclare.**

**The definition layer is empty** — *of imports*. The division-field `S_` file's only `Def_*`
import, `Definitions/Def_WeierstrassCurve_DivPolyMulFormulaCore.lean`, declares **nothing
public** — three `private` `linear_combination` cores and no consumer inside the file — and
the `S_` file reaches it only through its `attribute [-simp] …` scaffolding. Do **not** port
it, do **not** add it to `SOURCES`, and do **not** transcribe the `attribute [-instance] …` /
`attribute [-simp] …` blocks of either wrapper: they name `sizeOf_spec`, `EllSequence`,
`compl₂EDS`, `TateCurve` and `FLT.DivisorConvolution` lemmas that are not in the port's cone.

*(Corrected 2026-10-08 during the W2 review — the sentence above was true of the import list
and false of the proof.)* **The proof does reach an unported public block.** Its helpers
`ΨSq_eval_eq_zero_of_addOrderOf_prime` and `isRoot_of_nsmul_eq` rest on
`MFred`/`mfred_all`/`nsmul_succ_eq_zero_of_ΨSq_eval_eq_zero`/`ΨSq_eval_eq_zero_or_of_succ_nsmul_eq_zero`/
`lowTorsionFree_of_lt_addOrderOf` from `Definitions/Def_WeierstrassCurve_DivPolyMulFormula.lean`
(public there, ≈1,750 lines, absent from the port). This is the same class of miss §4a of the
column plan warns about, one level deeper: a `Def_*` **import** can be a stub while the
`S_` proof still needs a block of a *different* `Def_*` module it drags in transitively. The
implementer re-derived the two consumers from the ported
`FLTForHuman.Elliptic.smul_formula_or_zero` (strictly stronger for their use) instead, so the
`MFred` chain is unnecessary and no promotion is needed — but the scoping rule is now: **walk
the proof's own definition uses (`fltdata.proof_defs`), not just the import list,** before
declaring a definition layer empty.

**Transcribe the pin's `linter.*` suppressions, never `maxHeartbeats`** (the W1 review's
correction). Order 1's pin file sets nothing; order 2's sets exactly
`set_option autoImplicit false` and `set_option linter.unusedSectionVars false` (its lines
9–10) — carry both, and add `linter.unusedVariables` / `linter.unusedSimpArgs` only if a real
warning of that class appears, recording the addition. The project's global heartbeat cap is
4,000,000; the pin sets no `maxHeartbeats` here.

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only;
never modify). **Statement = the `Theorems/Thm_<stem>.lean` wrapper**, binders verbatim;
proof = the matching `P2M/Sol/S_<stem>.lean`. Adapt proofs, never statements.

* `Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean`
  and its `S_` file (68 lines; `torsionEquiv` at 17, `main` at 24, `solution` at 63).
* `Theorems/Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean`
  and its `S_` file (842 lines; `mem_separableClosure_of_root` at 22,
  `separable_of_natDegree_le_card` at 31, `sepPoints` at 51, the torsion block at 170–201,
  `solution` at the end).

Public mirrors, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean>.

## 2. Order 1 — the count-`N²` structure theorem

```lean
theorem WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq
    {k Ω : Type*} [Field k] [Field Ω] [DecidableEq Ω] [Algebra k Ω] (E : WeierstrassCurve k)
    [E.IsElliptic] (N : ℕ) [NeZero N] (hN : (N : k) ≠ 0)
    (hfull : Nat.card {P : (E.baseChange Ω).toAffine.Point // N • P = 0} = N ^ 2) :
    Nonempty (ZMod N × ZMod N ≃+ Submodule.torsionBy ℤ (E.baseChange Ω).toAffine.Point N)
```

The pin's `torsionEquiv` and `main` stay `private` at the pin's leaf names; only the headline
is public. Proof route (pin): pass to an algebraic closure of `Ω` — `(N : k) ≠ 0` gives
`(N : Ω̄) ≠ 0`, so the ported alg-closed isomorphism supplies `ZMod N × ZMod N ≃+ E(Ω̄)[N]` and
hence `N²` points; the map on points induced by `Ω → Ω̄` is an injective homomorphism on
`N`-torsion, and `hfull` makes source and target the same cardinality, so it is bijective.
Use `Submodule.torsionBy`'s `ℤ`-action where the pin does; do not restate the subtype
cardinality in a different spelling.

## 3. Order 2 — the `n`-division field

```lean
universe u v in
theorem WeierstrassCurve.exists_intermediateField_isGalois_card_torsion_eq_sq
    {F : Type u} {Ω : Type v} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic F Ω] [DecidableEq Ω]
    (E : WeierstrassCurve F) [E.IsElliptic] {n : ℕ} (hn : (n : F) ≠ 0) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      Nat.card {P : (E.baseChange L).toAffine.Point // n • P = 0} = n ^ 2 ∧
      ∀ σ : L ≃ₐ[F] L,
        (∀ P : (E.baseChange L).toAffine.Point, n • P = 0 → Point.map (σ : L →ₐ[F] L) P = P) →
        σ = 1
```

Build the division field from the separable closure: `mem_separableClosure_of_root` and
`separable_of_natDegree_le_card` are the two generic field helpers, `sepPoints` is the image
of the points over `separableClosure F Ω`, `some_mem_sepPoints_iff`/`Y_mem_of_X_mem` relate
coordinates to it, `card_le_two_mul_card_image_xOrZero` counts, and the torsion block
(`finite_and_ncard_torsion`, `torsFinset`, `mem_torsFinset`, …) supplies the `n²` cardinality
from the ported premise. Keep all of it `private` at the pin's leaf names; only the headline
is public. `natCast_ne_zero_of_dvd` (the pin's only helper with pool duplicates, 2 files)
stays `private` here.

## 4. Route and risks

* **`IntermediateField` / `IsGalois` / separable-closure API drift** is the real cost, and the
  pin is **not** on this port's mathlib line: the pin is Lean `v4.33.1` / mathlib `db584cd6`
  (the `v4.33.0` bump), the port is Lean `v4.34.0` / mathlib `v4.34.0`. Expect deprecation and
  behaviour drift throughout, and prefer the port's own spellings — check
  `FLTForHuman/WeierstrassCurve/Isogeny/IntermediateField.lean`, which already proves
  intermediate-field transport statements in the same vocabulary, before introducing any
  helper. *(Corrected 2026-10-08 during the review: an earlier draft claimed the pin was on
  the same mathlib line; it is not, and the implementer had to fix `if_neg` → `ite_eq_right`,
  `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, a `Nat.card_zmod` `NeZero`, a
  `Finite.of_equiv`/`Set.toFinite` route, and a `rfl` that no longer closes.)*
* `Nat.card` on the `N`-torsion subtype: keep the pin's subtype spelling exactly; the
  headline's `Nat.card {P : … // n • P = 0}` is the statement and any re-association is a
  checker `MISMATCH`.
* The pin's `variable (E : WeierstrassCurve F) [E.IsElliptic] …` sections: keep the same
  section-variable discipline so the `def`/`theorem` statement text matches (a typeclass
  argument that moves from the section to the binder changes no elaborated type but does
  change the checker's text — the trap that has fired four times).
* Order 2's proof is 842 pin lines; expect the file to be the set's build cost. Bound it; if a
  single declaration exceeds the wall bound, quarantine and report rather than raising the
  cap.

## 5. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` per module; **no whole-tree
build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit. Both modules are leaves — nothing
imports them yet, so no cascade is expected.

## 6. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive
it locally as `private` in your module and report it. If a promotion seems genuinely required,
**stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides. Order 1's proof must
not be factored into `Elliptic/TorsionZMod.lean`.

## 7. Wiring

In `lean/spec/check_flt_statements.py`, appending **last** so no earlier last-name match can
flip, per order:

* order 1: `Theorems/Thm_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean`
  and `P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq.lean`
  to `SOURCES`; `"FLTForHuman/WeierstrassCurve/Torsion/NatCardStructure.lean"` to `PORT_FILES`.
* order 2: `Theorems/Thm_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean`
  and `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_isGalois_card_torsion_eq_sq.lean`
  to `SOURCES`; `"FLTForHuman/WeierstrassCurve/Torsion/DivisionField.lean"` to `PORT_FILES`.

Run the checker **as soon as each module is written** (text-only, no build). Baseline at
dispatch: **7231 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (7267
checked)**; expected **+1 per order** (7232, 7233) with the public surface being the two
headlines only. Any other delta is statement drift to fix before building. Target
**0 mismatched, 0 missing**, then mutation-test one headline per order and revert.

## 8. Stop and report

If a statement cannot be matched without moving the pin's text; if the `attribute [-simp]`
scaffolding turns out to be load-bearing (it should not — the port has no such names); if a
helper is genuinely needed publicly and is `private` in a hub; or if a build exceeds its bound
and bisecting does not settle it.

## 9. Completion report (per order)

Module path; public/`private` counts; the tier-0 warning count (target **0**) and wall/CPU;
tier-1 wall/CPU; every local `private` re-derivation with its host; the checker before → after
with the `identical` delta reconciled against the new public surface and the mutation result;
`#print axioms` for each headline (`[propext, Classical.choice, Quot.sound]`); `git status
--porcelain` showing only the set's files; anything you could not match, quoted.

## 10. Outcome (2026-10-08, landed and manager-verified)

One set, one implementer, two orders; no stop condition fired; no existing Lean module
edited, no promotion, nothing committed.

| order | module | lines | public / private | tier 0 | tier 1 |
|---|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve/Torsion/NatCardStructure.lean` | 68 | 1 / 2 | 88 s | 67 s |
| 2 | `WeierstrassCurve/Torsion/DivisionField.lean` | 842 | 1 / 29 | 47.5 s | 77 s |

Wall is contention-sensitive this round (the manager's own tier-0 runs came in at 0
warnings, 0 errors); CPU is stable (order 1 ≈ 6 + 23 s, order 2 ≈ 19 + 14 s). Nothing
approached the wall bound; no cap raised.

**Checker 7231 → 7233 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
(7269 checked)**, +1 per order = the single public headline each; the 31 private declarations
are invisible to the checker. Mutation tests (implementer, both reverted): order 1 `N^2` →
`N^3` gave 7231/1/0, order 2 `n^2` → `n^3` gave 7232/1/0. `#print axioms` on both headlines:
`[propext, Classical.choice, Quot.sound]`. Warning-free on both (`grep -c warning` = 0). No
`sorry`/`admit`/`axiom`/`native_decide`, no `import Mathlib`, no heartbeat override.

**The manager's wire test** is `Zone W2` in `spec/DeligneSerreConsumer.lean`: the two
headlines **composed** — `exists_intermediateField_isGalois_card_torsion_eq_sq` produces `L`
with its `n²` cardinality conjunct, which is exactly the `hfull` hypothesis of
`nonempty_torsionBy_addEquiv_zmod_prod_of_natCard_torsion_eq_sq`, yielding
`Nonempty (ZMod n × ZMod n ≃+ E(L)[n])`. Elaborates exit 0; deleting either module fails the
zone.

### Deviations, recorded

* **The order's §0/§4 claims were both wrong and the implementer was right on both.** The
  definition layer is empty *of imports* but the proof consumes the unported
  `MFred`/`mfred_all` block of `Def_WeierstrassCurve_DivPolyMulFormula.lean` (§0, corrected);
  and the pin is on Lean `v4.33.1` / mathlib `db584cd6`,
  not this port's line (§4, corrected). Both corrections are in the order text.
* **Local `private` re-derivations** (no hub was touched, no promotion needed):
  `LowTorsionFree` (pin `Def_WeierstrassCurve_DivPolyMulFormula.lean:766`);
  `Ψ₂Sq_eval_ne_zero'` (pin `:27`) and `Ψ₂Sq_eval_eq_zero_iff_two_smul'` (pin `:33`), from the
  ported `Elliptic.sub_negY_sq_eq_Ψ₂Sq_eval`; `ΨSq_of_odd` (pin `:223`) from mathlib's
  `ΨSq_ofNat`/`preΨ_ofNat`/`ΨSq_neg`/`preΨ_neg`; and `nsmul_ne_zero_of_lt_addOrderOf`, which
  has no public pin host (it is `private` in two pin `S_` files and otherwise arrives through
  the pin's `p2m` prelude).
* **`haveI`/`letI` in a `Prop` goal** trips this project's `linter.style.haveILetI`; the pin's
  five local instances are threaded explicitly (`addOrderOf_eq_prime (hp := …)`,
  `@IntermediateField.finiteDimensional_adjoin`, `@IntermediateField.normal_iff_forall_map_le`,
  `isGalois_iff.mpr`), so nothing beyond the pin's own two suppressions is transcribed.
* The pin's `scoped instance instIsEllipticBaseChange` (its `-instance` workaround) is
  dropped; the port's `[E.IsElliptic]` suffices.
* Specific imports stand in for `import Mathlib`: `Mathlib.FieldTheory.Normal.Closure`,
  `Mathlib.FieldTheory.Galois.Basic`, `FLTForHuman.Elliptic.{TorsionCard,TorsionZMod}` and
  `FLTForHuman.WeierstrassCurve.Velu.Formula` (the port's public `Point.xOrZero`).
