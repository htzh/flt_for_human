# SET 4 — the eigenform interface, the integral lattice and the finite algebra (T8–T10)

**Status (2026-09-23): work orders written, not started.** This is the run brief
for the **fourth** coding set of the Hecke-operator effort, written after SET 3
was reviewed. It authorizes exactly three topics:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-t8-eigenform-interface.md](TOPIC-t8-eigenform-interface.md) | `IsNormalizedEigenform` and the operator/eigenvector dictionary | ~1,100 | 400–500 | T5, T6, T7 |
| 2 | [TOPIC-t9-integral-lattice.md](TOPIC-t9-integral-lattice.md) | `intLattice`/`HasIntegralStructure` and the lattice action | ~250 | 150–250 | T7 |
| 3 | [TOPIC-t10-finite-algebra.md](TOPIC-t10-finite-algebra.md) | `Module.Finite`/`Free` of `heckeAlgebra`, the eigenbasis span | ~5,600 (≈600 real) | 300–450 | T9 |

Earlier sets: [TOPIC-slash-invariance.md](TOPIC-slash-invariance.md) (T1),
[SET-2.md](SET-2.md) (T2–T4), [SET-3.md](SET-3.md) (T5–T7). Run T8 → T9 → T10;
T8 and T9 are independent, T10 needs T9.

**Outcome (2026-09-23, reviewed).** T8 and T9 are done and verified (checker
**802 identical, 0 mismatched, 0 missing**; full build 4054 jobs, 0 warnings, no
`sorry`; `#print axioms` clean). **T10 is blocked and re-scoped to SET 5**: its
premise — that the integral-structure existence is portable via the `χ₋₃`
Eisenstein series — is false. The pin's `hasIntegralStructure_of_two_le` imports
`Def_CuspForm_ModPForms`, `Def_HeckeEis_BinaryFormRep`, `Def_Gamma0CoeffCohomology`,
`Def_Gamma0HeckeOperatorHom` and ten Eichler–Shimura/period-package wrappers, none
of which the port has; the other finiteness targets also need the Sturm bound
(absent from mathlib `v4.34.0`) and the Petersson inner product. Only the two
self-contained definition modules (`Defs/EisensteinChiNegThree.lean`,
`Defs/IntegralLattice.lean`) landed. The full blocker and the SET-5 topic order
are in [TOPIC-t10-finite-algebra.md](TOPIC-t10-finite-algebra.md) §7. The pin's
4,308- and 212-line `_two` bodies remain not-to-be-transcribed.

**Scoping decision, stated explicitly.** The survey's §4 Tiers 2–4 (Γ₁/Nebentypus,
Γ_H, Atkin–Lehner) are **not** in this set. They are a different axis (missing
levels of the *invariance* layer, not the *use* of the operators) and their
blockers are definitional: Γ_H needs `CohCarrier.GammaH` (`Def_CohCarrier_Level`)
plus mathlib's transfer, and Atkin–Lehner needs the `AtkinLehnerDatum`/`alSlash`/
`diamondLinH` tree. SET 4 finishes the survey's Stages A–C *usage* half (the
operators are now an object other mathematics can be stated against); the tiers
become SET 5 — which is now **T10's re-scoped infrastructure first, then the
tiers** (see the outcome note above). Say so if a tier topic should be pulled
forward.

**Do not start SET 5.** If a SET-4 topic needs a tier declaration, prove a local
`private` helper and record it.

## 0. What SET 3 handed over (verified)

SET 3 was independently re-verified by the reviewer: checker **772 identical
(53 promoted), 0 mismatched, 0 missing, 14 own-proof**; full `lake build` exit 0,
4048 jobs, 0 warnings, no `sorry`; `#print axioms` clean on 17 headlines. All of
it is committed (`c7d668b "Hecke operators"`). The surface SET 4 builds on:

- **`ModularForms/HeckeQCoeff.lean`** — `ModularFormClass.qCoeff` (the pin's
  definition), `qCoeff_hecke{U,T}` at both levels, `qCoeff_comp_heckeDiagMatrix_smul`,
  `qExpansion_hecke{U,T}_eq_hecke{U,T}`, `qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`,
  `UpperHalfPlane.eq_of_forall_qCoeff_eq`, `coeffHecke{T,U}_comm`/`_int`.
- **`ModularForms/HeckeOperatorForms.lean`** — `ModularForm.heckeTLin`/`heckeULin`,
  `CuspForm.heckeTLin`/`heckeULin` (+ the four `coe_*`/`_apply_apply` `rfl`s each),
  `CuspForm.qExpansion_heckeTLin`, `exists_coe_eq_hecke{T,U}`.
- **`ModularForms/HeckeCommute.lean`** — the function-level, bundled and formal
  commutations.
- **`ModularForms/HeckeAlgebra.lean`** — `heckeGenerators`, `heckeAlgebra`,
  `commute_of_mem_heckeGenerators`, `instIsMulCommutative`/`instCommRing`/
  `instIsAddTorsionFree`, `heckeAlgebra.T`/`.U`.
- **`ModularForms/Defs/FormalHeckeOperators.lean`** — `PowerSeries.hecke{U,V,T}`,
  `heckeU_heckeV`, `coeff_heckeT`.
- **`ModularCurve/Defs/LaurentSeriesHecke.lean`** — `LaurentSeries.hecke{U,V,T}`.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3`, at
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- Statement = `Theorems/Thm_<dotted, `_` for `.`>.lean`; proof =
  `P2M/Sol/S_<same>.lean`; the wrapper is the statement authority.
- Definition modules have no wrapper; the checker verifies them by name. SET 4
  adds `Def_CuspForm_IntegralLattice.lean`, `Def_CuspForm_IntegralStructure.lean`,
  and the `CuspForm.IsNormalizedEigenform` structure from
  `Def_FLTPrelim_Modularity.lean:26–40` (the port has transcribed `qCoeff` from
  that file but not the structure).
- **The pin repeats whole developments inside single theorems.** The 4,308-line
  `S_CuspForm_moduleFinite_heckeAlgebra_two.lean` re-derives the Hecke analytic
  machinery the port now has in `HeckeAnalytic.lean`/`HeckeOperatorForms.lean`.
  T10 must *use* the port's modules, not transcribe it; the `S_` file is a
  reading aid for the statement, not a porting source.

## 2. Build discipline — read this first

Measured in this checkout with mathlib prebuilt: `lake env lean` small module
~6 s warm; `lake build <module>` deps-cached ~4–6 s; full `lake build` green at
**4048 jobs**. The lakefile sets `maxHeartbeats` to 4,000,000 globally, so the
`timeout` is the only real guard.

- Bound every build: `timeout 120 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 600 lake build`. A non-return at
  120 s is a blow-up.
- Quarantine immediately on a timeout: comment out/bisect, or reproduce in the
  gitignored `Scratch*.lean` with `set_option diagnostics true`.
- **Never add or raise `maxHeartbeats`.** T8's `isNormalizedEigenform_iff_coeffHecke`
  is the likely stall (a four-clause recursion over `ℕ`), and T10's finiteness
  proofs are the others; restate over the concrete type rather than raise the cap.
- Keep imports specific.

## 3. Shared conventions

1. Statements verbatim from the wrappers, binders included.
2. **Dedup where FLT duplicates.** T8's `iff_coeffHecke` and T10's `_two` file both
   re-derive machinery; import the port's modules. Record `grep -c`.
3. The checker: append each topic's wrappers to `SOURCES` and each new module to
   `PORT_FILES`; definition declarations verify by name. Target **0 mismatched,
   0 missing**.
4. No consumer zone; checker + full build is the wire test.
5. `logs/hecke-port.md` gains §T8/§T9/§T10; `README.md` gains the rows. The
   `SET`/`TOPIC` files are the manager's.
6. **No commits.** The working tree is the hand-off.
7. **Do not touch the FFG modules** (`ModularCurve/ModularPolynomial*.lean`,
   `FunctionFieldGeneration/*`): a separate effort owns them.

## 4. Definition of done (per topic)

- Module(s) as named; statements verbatim; specific imports.
- `timeout 600 lake build` green, 0 warnings, no `sorry`/`admit`.
- `#print axioms` on the topic's headlines clean.
- `spec/check_flt_statements.py`: sources appended; **0 mismatched, 0 missing**.
- Dedup demonstrated with `grep -c` (T8, T10).
- `logs/hecke-port.md` section; `README.md` rows.

## 5. What to report back

1. The per-topic table (modules, lines, decls, build, checker before/after).
2. **The eigenform dictionary** T8 lands: the three `iff`s and the
   `apply_eq_smul_iff` family, with the exact names SET 5 / the FLT machinery
   downstream will use.
3. **T10's route**: how much of the 4,308-line `_two` file was avoidable by
   importing `HeckeAnalytic`/`HeckeOperatorForms`, and where the finiteness proof
   actually bit.
4. Any statement that would not match its wrapper, quoted rather than weakened.
5. The SET-5 hand-off: Tiers 2–4 entry cost, and anything the eigenform interface
   left `private`.
