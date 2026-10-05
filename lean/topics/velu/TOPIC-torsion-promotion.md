# The torsion-API promotion — an H5 follow-up

**Status: scoped (2026-10-05); dispatched.** Promotes the two H5 re-proofs worth
keeping, per [TOPIC-port-plan.md](TOPIC-port-plan.md) §5 item 5. Pin
`anthropics/fermats-last-theorem@aa2d8b3`; mathlib `v4.34.0`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.2 (route audit),
§3.1–§3.2 (module layout), §3.5 (build ladder), §4 (faithfulness), §5 (share real
math, keep glue private). The H5 record is [../../logs/velu-port.md](../../logs/velu-port.md).

## 1. Which two, and why the third is not promoted

H5's dual column hit three unported pin `Theorems/` nodes and re-proved them
locally. Two are worth promoting; one is glue:

| pin declaration | port today | verdict |
|---|---|---|
| `WeierstrassCurve.finite_torsionBy_of_natCast_ne_zero` | `private finite_torsionBy_aux`, exact statement | **stays private** — it only specialises the ported `FLTForHuman.Elliptic.card_torsion_of_isAlgClosed` |
| `WeierstrassCurve.Affine.Point.exists_zsmul_eq_of_isAlgClosed` | public but renamed `surjective_zsmul_of_ne_zero` **and weakened with `[CharZero K]`** | **promote** — a fidelity gap: the pin is char-free |
| `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` | omitted; its consumer re-proved directly | **promote** — a structural statement with a wide fan-out |

## 2. Mathlib audit (recorded negatives)

Searched mathlib `v4.34.0` for each ingredient; **none exists**, so both proofs
are irreducible port work:

* no `ZMod n × ZMod n ≃+ Submodule.torsionBy ℤ A n` classification — no
  `nonempty_zmod_prod_addEquiv_torsionBy`, no "`Nat.card A[n] = n²` for all
  `d ∣ n` implies `(Z/n)²`" lemma, in `Algebra/Module/Torsion/`, `GroupTheory/`,
  `Algebra/Module/ZMod/` or the elliptic-curve tree;
* no `Divisible` instance and no `nsmul`/`zsmul` surjectivity for
  `WeierstrassCurve.Affine.Point` over an algebraically closed field anywhere in
  `Mathlib/AlgebraicGeometry/`.

What mathlib *does* have, and the port should build on: the `Submodule.torsionBy`
API (`Algebra/Module/Torsion/Basic.lean`, including `torsionBy_isInternal` for
primary decomposition). The port's own `FLTForHuman.Elliptic.smul_surjective`
gives the `(n : K) ≠ 0` case only, which is why the pin's char-free proof is a
genuine addition.

## 3. Source (pin)

* `P2M/Sol/S_AddCommGroup_nonempty_zmod_prod_addEquiv_torsionBy_of_card_torsionBy_eq_sq.lean`
  — **378 lines / 14 declarations**, `Mathlib`-only. The p-primary case
  (`nonempty_zmodPowSqAddEquiv_of_card_pow` and its `pSmulHom` machinery) then the
  coprime/CRT split (`torsionByMulCoprimeSplitAddEquiv`,
  `nonempty_zmodSqAddEquiv_torsionBy_mul_of_coprime`).
* `P2M/Sol/S_WeierstrassCurve_Affine_Point_exists_zsmul_eq_of_isAlgClosed.lean`
  — **376 lines / 13 declarations**; its `nsmul_surjective_charfree` is the
  char-free core and `exists_zsmul_eq` the headline.
* `P2M/Sol/S_WeierstrassCurve_nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed.lean`
  — **23 lines / 1 declaration**: a wrapper applying the generic lemma with the
  cardinality hypothesis supplied by `W.card_torsion_of_isAlgClosed`.
* The `Theorems/Thm_…` wrappers with the same three names are the statement
  authority.

## 4. Deliverables

1. **New `FLTForHuman/Algebra/ZModTorsion.lean`** — the generic node's 14
   declarations, statement-verbatim, `Mathlib`-only (no `FLTForHuman` import).
2. **New `FLTForHuman/Elliptic/TorsionZMod.lean`** — the char-free
   `Point.exists_zsmul_eq_of_isAlgClosed` node's declarations and the
   `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
   wrapper. Imports `FLTForHuman/Algebra/ZModTorsion.lean`,
   `FLTForHuman/Elliptic/TorsionCard.lean` and the EDS/division-polynomial modules
   the char-free proof uses. Register both new modules in `PORT_FILES` (append
   last).
3. **Checker `SOURCES`** — append the three `Theorems/` wrappers (and, if the
   checker needs them for the promoted helpers, the three `S_` files), last. None
   is diffed today, so the port's weaker/omitted statements are currently
   invisible.
4. **Consumer switch** in `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/DualEndData.lean`
   — `surjective_zsmul_of_ne_zero` is defined there and used once (line 2412);
   replace the use with the promoted char-free
   `Point.exists_zsmul_eq_of_isAlgClosed` and delete the local copy.
   `cmm5_dp_natCard_ker_natCast` keeps its pin statement (its proof may route
   through the promoted classification if that is simpler). `Vocabulary.lean` is
   checked too in case it cites either.

## 5. Fidelity rules

* Statements verbatim from the wrappers; the checker cannot see section
  variables, so `#check @<name>` each headline against its wrapper.
* `solution` stays `private` and the wrapper name is exposed (the SET-2 pattern):
  several pin `S_` files declare a public `solution`, and a public `solution`
  would diff against the wrong one.
* Promote pin-private helpers public where the checker's dotted fallback verifies
  them; keep purely local helpers `private`.
* The hypotheses are load-bearing and must not be strengthened:
  `exists_zsmul_eq_of_isAlgClosed` is **char-free** (`{n : ℤ} (hn : n ≠ 0)`, no
  `[CharZero K]`), and `nonempty_torsionBy…` needs `n` invertible in `K`.

## 6. Build discipline (copy into the work order)

1. Edit loop (no `.olean`, no cascade):
   `timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`
   (`lake env lean` does not inherit the lakefile options).
2. Module done: `timeout 300 flock .lake/flt_build.lock bash -c 'time lake build <module>'`
   (the lock lives at `lean/.lake/flt_build.lock`, not `/tmp`).
3. `python3 spec/check_flt_statements.py` at every module close; target
   `0 mismatched / 0 missing`, record the `identical` delta.
4. `#print axioms` clean, no `sorry`; never raise `maxHeartbeats`.
5. No bare `lake build` (the whole-tree milestone is the manager's); no
   concurrent builds.

## 7. Verification

Both new modules `lake env lean` clean and `lake build` green; checker
`0 mismatched / 0 missing` with the delta recorded; three wrappers diffed; the
switched consumer green; `#print axioms` on the two headlines and the generic
lemma `[propext, Classical.choice, Quot.sound]`; no `sorry`.

## 8. Risk

| risk | mitigation |
|---|---|
| the generic proof needs a `ZMod`-module structure on `torsionBy` mathlib lacks | it is a `Submodule` of an `AddCommGroup`; the pin proves it with `Mathlib` only, so transcribe its route |
| `solution` name collision across pin `S_` files | keep it `private`, expose the wrapper name (SET-2 pattern) |
| the char-free proof needs machinery not yet in `FLTForHuman/Elliptic/` | the port's EDS/`TorsionCard` material is already there; if a piece is missing, stop and report rather than weaken the hypothesis |
| switching `DualEndData`'s consumer changes a proof that currently compiles | keep `cmm5_dp_natCard_ker_natCast`'s statement; adapt only the proof, and re-run the checker |
