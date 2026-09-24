# SET 3 — the `q`-coefficient layer and the bundling (T5–T7)

**Status (2026-09-23): work orders written, not started.** This is the run brief
for the **third** coding set of the Hecke-operator effort, written after
reviewing SET 2. It authorizes exactly three topics:

| order | work order | object | pin | ≈ port | prereq |
|---|---|---|---|---|---|
| 1 | [TOPIC-t5-qcoeff.md](TOPIC-t5-qcoeff.md) | the formal `PowerSeries` operators + the `qCoeff`/`qExpansion` bridge | 43 + 4×353 + ~440 | 400–500 | T1, T3 |
| 2 | [TOPIC-t6-bundling.md](TOPIC-t6-bundling.md) | the bundled `heckeTLin`/`heckeULin` on `ModularForm`/`CuspForm` | 112 + 19 | 150–200 | T1, T3, T4 |
| 3 | [TOPIC-t7-commutativity-algebra.md](TOPIC-t7-commutativity-algebra.md) | commutation of the operators and the Hecke algebra | ~360 + 93 | 250–350 | T6 |

SET 1 is [TOPIC-slash-invariance.md](TOPIC-slash-invariance.md); SET 2 is
[SET-2.md](SET-2.md) (done and reviewed; see `logs/hecke-port.md` §"SET-2
review"). Run T5 → T6 → T7 in order: T5 supplies the `q`-coefficient vocabulary
T6's `qExpansion` lemmas use, and T6 supplies the linear maps T7 commutes and
algebras over.

**Do not start the deferred pieces.** They are SET 4:
- the **eigenform interface** (survey §8): `CuspForm.isNormalizedEigenform_iff_heckeT`/`_heckeTLin`/`_coeffHecke`, the `hecke?Lin_apply_eq_smul_iff` family, `ModularFormClass.hecke?T/U_eq_smul_iff`, and the newform multiplicity results;
- the **finite/free Hecke algebra** (survey §9's `Module.Finite`/`Module.Free`/spanning theorems: `CuspForm.moduleFinite_heckeAlgebra`, `mem_intLattice_of_mem_heckeAlgebra`, `span_heckeTLin_eigen_eq_top`, …);
- **Tiers 2–4** of the survey's §4 (Γ₁/Nebentypus, Γ_H, Atkin–Lehner).

If a SET-3 topic needs a SET-4 declaration, prove a local `private` helper and
record it — do not open the deferred modules.

## 0. What SET 2 handed over (verified)

SET 2 was independently re-verified by the reviewer: checker **696 identical
(34 promoted), 0 mismatched, 0 missing, 14 own-proof**; full `lake build` exit 0,
4042 jobs, 0 warnings, no `sorry`; `#print axioms` clean on the 13 SET-2
headlines. The surface SET 3 builds on:

- **`Defs/HeckeOperator.lean`** (247 lines) — the Tier-0 block. Public:
  `heckeMatrix`, `heckeDiagMatrix`, `upperTriangularGL`, the `val_*`/`val_det_*`
  helpers, `heckeU`/`heckeT` and the whole operator/coefficient API. `val_heckeMatrix`,
  `val_heckeDiagMatrix`, `upperTriangularGL`/`val_upperTriangularGL` were promoted
  for SET 1–2; the remaining `det_*`/`denom_*` stay private.
- **`Defs/HeckeRepresentatives.lean`** (353 lines) — the shared Γ₀ block.
- **`HeckeInvariance.lean`** (110) — the three Γ₀ statements.
- **`HeckeFricke.lean`** (380) — the Fricke pair, one development, via mathlib's
  `ModularForm.trace`; its private `heckeU_slash_W`/`slash_scalar` are the
  likely SET-4 promotions.
- **`HeckeAnalytic.lean`** (227) — the analytic head (`mdifferentiable_heckeU/T`,
  `periodic_heckeU/T_comp_ofComplex`, `isBoundedAtImInfty_heckeU/T`,
  `mdifferentiable_slash_heckeDiagMatrix`); the block-internal
  `heckeMatrix_one_zero`/`heckeDiagMatrix_one_zero`, `isZeroAtImInfty_*` and the
  `vadd` machinery are `private`.
- **`HeckeCusps.lean`** (216) — `ModularFormClass.isBoundedAt_heckeU/T` and
  `CuspFormClass.isZeroAt_heckeU/T`; the rational-cusp block is private.

SET 2's measured compression was 3,177 pin → 823 port lines. The same pattern
applies again: the pin's `q`-coefficient theorems are stated in four more copies
of the 353-line block (pin lines 158–345), whose tail the port now writes once.

## 1. The source of truth, and how to read it

- **Pin**: `anthropics/fermats-last-theorem@aa2d8b3`, at
  `~/proj/fermats-last-theorem`. Read it; never modify it.
- Statement = `Theorems/Thm_<dotted name, `_` for `.`>.lean`; proof =
  `P2M/Sol/S_<same>.lean`. The wrapper is the statement authority (playbook
  §7.4, the checker is textual).
- Definition modules have no `Thm_` wrapper; the checker diffs them against
  `Definitions/` directly. T5 adds `Def_PowerSeries_FormalHeckeOperators.lean`,
  T6 `Def_ModularForm_HeckeOperatorForms.lean`, T7 `Def_CuspForm_HeckeAlgebra.lean`.
- mathlib is the pinned `v4.34.0`. `ModularFormClass.qCoeff`/`qExpansion`,
  `PowerSeries`, `LaurentSeries`, `HasSum` and `ModularForm.trace` are mathlib;
  the port's own `ModularCurve.qExpand`/`qTwist` live in
  `FLTForHuman/ModularCurve/Defs/`.
- **The block is in four more 353-line files.** `UpperHalfPlane.qCoeff_heckeU/T`
  and `ModularFormClass.qCoeff_heckeU/T` are all 353 lines with the same head T3
  already ported and a tail (`qExpansion_coeff_unique'`, `hasSum_qCoeff`,
  `eq_of_forall_qCoeff_eq`, `qParam_hecke*`, `sum_rootOfUnity_pow`,
  `hasSum_average`, `hasSum_diag`, `hasSum_heckeU/T`, `qCoeff_heckeU/T_bare/class`)
  this set ports once. Count before you port.

## 2. Build discipline — read this first

Every build is bounded and a blow-up is quarantined, not waited on. Measured in
this checkout with mathlib prebuilt: `lake env lean` on a small module **~6 s**
warm (~20 s cold); `lake build <module>` deps-cached **~4–6 s**; full `lake build`
green at **4042 jobs**, nearly all cached. The lakefile sets `maxHeartbeats`
to 4,000,000 globally, so the `timeout` is the only real guard.

- Bound every build: `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 180 lake build`. A non-return at
  120 s is a blow-up.
- Quarantine immediately on a timeout: comment out/bisect, or reproduce in the
  gitignored `Scratch*.lean` with `set_option diagnostics true`.
- **Never add or raise `maxHeartbeats`.** The usual cause is a `FunLike` lemma
  instantiated at a bare function; restate over the concrete `ℍ → ℂ` (or the
  concrete `F`). T5's `UpperHalfPlane.qCoeff_*` targets are already over
  `ℍ → ℂ`; the `ModularFormClass` ones are over `F` — keep the shapes the pin
  uses.
- Keep imports specific. T5's `PowerSeries`/`LaurentSeries` work needs
  `Mathlib.RingTheory.PowerSeries.*`; T7's `Module.End` work needs
  `Mathlib.Algebra.Algebra.Subalgebra.Basic`.

## 3. Shared conventions

1. **Statements verbatim from the wrappers**, binders included; the wrapper wins
   over the `S_` file and the divergence goes in the log.
2. **Write the shared tail once.** T5 ports the 353-block's tail once. Deleting a
   private copy is success; record `grep -c` before and after.
3. **The checker.** Append each topic's wrappers to `SOURCES` and each new module
   to `PORT_FILES`. Definition-module declarations (T5's `PowerSeries.hecke*`,
   T6's `heckeTLin`/`heckeULin`, T7's `heckeGenerators`/`heckeAlgebra`) verify by
   name against the `Definitions/` file; the wrappers verify against their
   `Thm_` files. Target **0 mismatched, 0 missing**.
4. **No consumer zone.** Checker + full build is the wire test; probes go in
   `Scratch*.lean`.
5. **`logs/hecke-port.md`** gains a §T5/§T6/§T7 section; `README.md` gains the new
   module rows. The `SET`/`TOPIC` files are the manager's and are not rewritten
   by the coder.
6. **No commits.** The working tree is the hand-off.
7. **Do not touch `ModularCurve/ModularPolynomialIrreducible.lean`** or any other
   FFG module: a separate session owns them (see the SET-2 review in the log).

## 4. Definition of done (per topic)

- Module(s) as named in the work order; statements verbatim; specific imports.
- `timeout 180 lake build` green, **0 warnings**, no `sorry`/`admit`.
- `#print axioms` on the topic's public headlines: only
  `propext, Classical.choice, Quot.sound`.
- `spec/check_flt_statements.py`: sources appended; **0 mismatched, 0 missing**.
- The dedup demonstrated with `grep -c` counts (T5).
- `logs/hecke-port.md` section; `README.md` rows.

## 5. What to report back

1. The per-topic table (modules, lines, decls, build, checker before/after).
2. **The compression** (T5's four-file tail) and the **new public surface** —
   for T6 and T7 this is the deliverable: the exact `heckeTLin`/`heckeULin` API
   and the `heckeAlgebra` instance names downstream code will use.
3. Whether the scouted routes held — specifically T5's `qExpansion_coeff_unique'`
   over `ℍ → ℂ` (the historical `DFunLike` stall site) and T7's
   `IsMulCommutative` instance.
4. Any statement that would not match its wrapper, quoted rather than weakened.
5. The SET-4 hand-off (eigenform interface, finite/free algebra, Tiers 2–4).
