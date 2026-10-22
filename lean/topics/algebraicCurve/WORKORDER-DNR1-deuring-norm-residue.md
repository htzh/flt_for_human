# WORKORDER-DNR1 — the residue of a norm (Deuring norm-residue)

**Status: landed (2026-10-22).** One new module, no existing module edited; the measured reading is
§9.

## 0. The node

`AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction` — pin `S_` file 697 lines, 31 declarations
(30 under `namespace DeuringNormResidue`, plus the pin's `solution` twin at :675), **32 public** in the
tool's count; all new (0 already in the port, 0 shared with another target). Report the module's own
count and expect `ok` to equal it — do not match the tool's 32 blindly.

**Readiness, measured 2026-10-22 after RPF1 landed.** Its demand is itself (`needed 1 / 697 lines`);
its one premise `AlgebraicCurve.linearIndependent_of_constantFieldExtension` is ported
(`FLTForHuman/AlgebraicCurve/IsCurveOver/ConstantFieldExtension.lean`, 579 lines — the single `F` node
in the cone). Its **single consumer is in the D-S demand**:
`AlgebraicCurve.Divisor.mapDomain_placeReduction_eq_ord_of_retraction`, whose own demand is 6 nodes /
2,524 lines (11 literal) and which this node leaves one premise shorter. `used_by cone 1 / project 1`.

Not ready, for the record: the two consumers named in `WORKORDER-RPF1` §9 are still sets —
`RegularProlongation.residue_integralClosure_surjective_of_genusFF_eq` needs 15 nodes / 4,042 lines,
`Divisor.finrank_riemannRochSpace_le_finrank_riemannRochSpace_mapDomain_placeReduction` needs 9 nodes /
3,412 lines (14 literal), both at hops 1. Neither is a leaf; do not schedule them as one dispatch.

Statement authority, `Theorems/Thm_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction.lean`:

```lean
theorem AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction
    (K F E FE : Type*) [Field K] [Field F] [Field E] [Field FE] [Algebra K F] [Algebra E FE]
    [Algebra K E] [Algebra F FE] [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧ FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [Algebra (RatFunc E) FE] [IsScalarTower E (RatFunc E) FE] [FiniteDimensional (RatFunc E) FE]
    (hX : algebraMap (RatFunc E) FE RatFunc.X = algebraMap F FE (algebraMap (RatFunc K) F RatFunc.X))
    (A : ValuationSubring E)
    (hKA : ∀ k : K, algebraMap K E k ∈ A)
    (hArat : ∀ a : E, a ∈ A → ∃ k : K, A.valuation (a - algebraMap K E k) < 1)
    (O : ValuationSubring FE) (ρ : O →+* F)
    (hO : ∀ c : E, algebraMap E FE c ∈ O ↔ c ∈ A)
    (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ f : F, ∃ h : algebraMap F FE f ∈ O, ρ ⟨algebraMap F FE f, h⟩ = f)
    (g : O) (hg : ρ g ≠ 0) :
    ∃ h : algebraMap (RatFunc E) FE (Algebra.norm (RatFunc E) (g : FE)) ∈ O,
      ρ ⟨_, h⟩ = algebraMap (RatFunc K) F (Algebra.norm (RatFunc K) (ρ g))
```

One sentence: the residue of a norm is the norm of the residue, for a retraction `ρ : O →+* F` of a
valuation subring (`K` algebraically closed, so the two function-field towers are `RatFunc` towers) —
Deuring's norm step, which turns a norm downstairs into a norm upstairs so the residue can be read.

## 1. Deliverable

**One new module**, `FLTForHuman/AlgebraicCurve/DeuringNormResidue.lean`.

* Namespace `AlgebraicCurve` → **`AlgebraicCurve.DeuringNormResidue`** (the pin's own subject name,
  kept); the pin's `P2MW.S_<stem>` wrapper namespace is dropped, the `p2m_open`/`p2m_export`/
  `p2m_reactivate` staging with it.
* Imports: `FLTForHuman.AlgebraicCurve.IsCurveOver.ConstantFieldExtension` (the ported premise) plus
  the narrow mathlib modules the proof needs (`FieldTheory/RatFunc/…`, `FieldTheory/Normal/…` or
  `Algebra/Norm…`, `RingTheory/Valuation/ValuationSubring`, `FieldTheory/IntermediateField/Adjoin/…`,
  `Algebra/Polynomial/Eval/Defs`). **Drop `import Definitions.Def_AlgebraicCurve_DivisorClassGroup`**:
  the pin imports it, and a `grep` shows the file never names anything from it (`Divisor`, `Place`,
  `DivisorClassGroup`, `Pic0`, `mapDomain`, `placeReduction`, `ord`, `PlaceMap` — zero occurrences).
  Also drop the unused `import P2M.Util`. No `import Mathlib`; `Mathlib.Tactic.*` modules as needed.
* Header docstring in the port's style: subject, pin source with pinned URLs (`aa2d8b3`), the two
  `spec-pin:` lines, the drift note, `set_option autoImplicit false`.
* Keep the pin's three phase **sections** (`RationalPlace`, `TwoTowers`, `Reduction`); they are proof
  phases and make the 697 lines navigable.
* Public surface: the pin's public declarations at the pin's last names — they are descriptive, e.g.
  `valuation_algebraMap_eq_one`, `sigmaFun_spec`, `exists_algebraMap_eq`, `exists_basis_algebraMap`,
  `exists_rho_eq_algebraMap`, `algebraMap_coord_mem`, `residue_norm_eq_norm_residue` — plus the
  headline `AlgebraicCurve.residue_norm_eq_norm_residue_of_retraction` verbatim from the wrapper. The
  pin's `solution` (:675) sits **outside** the namespace and is a one-line application of
  `residue_norm_eq_norm_residue`; keep it as a private twin or inline it into the headline, either
  way it is not public.
* The pin's one `set_option linter.unusedVariables false in` may stay (a linter option, not a
  heartbeat one); prefer deleting it if the unused variable can be removed, but never add
  `maxHeartbeats`.

Wiring: `spec-pin:` for the wrapper first, then
`P2M/Sol/S_AlgebraicCurve_residue_norm_eq_norm_residue_of_retraction.lean` as the comparable copy.
Expected: `0 mismatch, 0 missing, 0 own, 0 kw`, `ok` = the module's public declaration count.

## 2. Reuse

* `AlgebraicCurve.linearIndependent_of_constantFieldExtension` (`IsCurveOver/ConstantFieldExtension.lean`)
  — called once in the pin at its `TwoTowers` phase (`have hW := …`); import it, never restate it.
* The silo cites no other pin node (the `DivisorClassGroup` import is inert, §1), so nothing else to
  dedup against: if a statement from another `AlgebraicCurve/` module turns out to be needed, **stop
  and report** — it would be a premise the graph missed.
* mathlib supplies `RatFunc` (`RatFunc.X`, `algebraMap`), `Algebra.norm` and its tower lemmas,
  `IntermediateField.adjoin`, `ValuationSubring`.

## 3. Names

No rectification pass: the pin's declaration names are descriptive and stay, and
`DeuringNormResidue` is a subject namespace, not a token. Nothing to drop beyond §1's wrapper and
staging.

## 4. Route

Follow the pin's phases in order — each is a milestone you can elaborate:

1. `RationalPlace`: `valuation_algebraMap_eq_one`, the rational-place and residue lemmas
   (pin 12–104);
2. `TwoTowers`: the norm/residue compatibility over the two `RatFunc` towers, including the single
   call to `linearIndependent_of_constantFieldExtension` (pin 159–295);
3. `Reduction`: the reduction argument that produces the `O`-membership of the norm and the residue
   identity (pin 297–667); `solution` (pin 675–697, outside the namespace) is the one-line twin and
   the headline closes on it.

## 5. Build discipline — read before the first compile

From `lean/`, always through the lock:

```bash
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AlgebraicCurve/DeuringNormResidue.lean
```

A finished file: `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.AlgebraicCurve.DeuringNormResidue`.

* **The 200,000 cap is a diagnostic.** No `set_option maxHeartbeats`, no
  `synthInstance.maxHeartbeats`, ever; the pin's bumps (if any) are not inherited.
* **Bound the floor first**: a `lean/tmp/` copy with every theorem proof `sorry` (statements, defs,
  instances, section variables verbatim) gives the floor in one run. If the floor aborts, the cost is
  in the frozen types; levers in order: an unused section variable becomes a `haveI`/term-`letI` in
  the proof that needs it, `private abbrev` aliases, then **stop and report**.
* **Probes, not bisection** (`porting-playbook.md` §3.5): statement-vs-proof; isolate with earlier
  proofs stubbed; shrink the statement, not the file; one kept `diagnostics` trace; `isDefEq` at
  `-DmaxHeartbeats=3000` only when the counters are the question. A probe over 60 s is the probe's
  fault.
* **Bound, do not measure**: no `time`; anything that can run a minute is a background job with its
  own `timeout` and a log you read afterwards. One probe, one edit, one bounded compile per turn;
  every tool call under two minutes; no bare or whole-tree `lake build`.
* Expected risk here: the tower instances (`IsScalarTower`, `FiniteDimensional` over `RatFunc`) and
  `Algebra.norm` over them — the fix for a slow declaration is a syntactic form for the type, not a
  bump.

## 6. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/DeuringNormResidue.lean
python3 spec/check_port.py --changed --strict-markers
```

plus: 0 warnings; `#print axioms` on the headline `[propext, Classical.choice, Quot.sound]`; no
`sorry`/`admit`/`native_decide`/`import Mathlib`; only `set_option autoImplicit false` (plus the pin's
linter option if kept); `git status` adds exactly one file.

## 7. Stop and report — do not improvise — if

an existing module must change (declaration, host, `tools/deps/build_ladder.py --edit` price); the
proof needs a statement from another pin node; a heartbeat raise looks necessary (give the
statement-only probe at 200k and the reading); the headline reads `MISMATCH`; or a
`spec/decl_markers.tsv` row looks needed.

## 8. Report shape

(i) lines, declaration count, public/private split, public surface; (ii) the checker reading,
`--changed --strict-markers`, the build's jobs/warnings; (iii) axioms; (iv) proof deviations with sites
and the drift they answer; (v) names carried, wrapper and staging dropped, the inert import dropped;
(vi) what belongs in `CARRY-FORWARD.md`; (vii) `git status`; plus the floor probe and the pin ranges
consumed.

Records: [TOPIC-mathlib-module-homing.md](../TOPIC-mathlib-module-homing.md),
[porting-playbook.md](../../porting-playbook.md) §3.1–§3.5, §4–§6,
[WORKORDER-RPF1](WORKORDER-RPF1-regular-prolongation-finrank.md) (the previous cut in this area and
its landed numbers).

## 9. Landed (2026-10-22)

`FLTForHuman/AlgebraicCurve/DeuringNormResidue.lean` — **804 lines, 33 declarations = 32 public + 1
private** (`solution`, the pin's twin, private at :753). Namespace `AlgebraicCurve` →
`AlgebraicCurve.DeuringNormResidue`; the pin's three phase sections kept (`RationalPlace` :91,
`TwoTowers` :238, `Reduction` :376); the `P2MW.S_…` wrapper, its `p2m_reactivate`, and the two inert
imports (`Definitions.Def_AlgebraicCurve_DivisorClassGroup`, `P2M.Util`) are gone from the code and
named only in the drift note.

| gate | reading |
|---|---|
| `check_port --force` (module) | **32 ok**, 0 mismatch, 0 missing, 0 own, 0 kw; headline → `Theorems/Thm_…:9`, the rest to their `P2M/Sol/S_…` lines |
| `--changed --strict-markers` | 4173 ok, 0 / 0, 12 own (pre-existing), 0 kw — 165 modules, 0 stale markers |
| `lake build …DeuringNormResidue` | 2,596 jobs, green, **0 warnings** |
| edit loop at 200k | exit 0, empty log |
| axioms (headline and the namespace's main theorem) | `[propext, Classical.choice, Quot.sound]` |
| hygiene | `set_option autoImplicit false` (:81) and the pin's `linter.unusedVariables false in` (:750) only; no `sorry`/`admit`/`native_decide`/`import Mathlib` |

**Floor**: statements are cheap — a `sorry`-stubbed copy (26 namespace theorems + the twin + the
headline stubbed, `coe_constEmb`'s `rfl` and the four `def`s verbatim) elaborates at 200k in one pass,
so the floor is in the proofs; the full module then closes at the same cap in one pass. No abort, no
bisection, no lever.

**Proof deviations (4 kinds, 5 sites, all proof-side; every statement the pin's verbatim — the checker
hashes all 32 identical).** `Polynomial.finset_sum_coeff` → `finsetSum_coeff` (:193, the v4.34 rename,
now a drift-table row); `letI` → `let` (:306) and `haveI` → `have` (:308) for `linter.style.haveILetI`
(both binders are local instances either way); `zero_le'` → `zero_le` (:504, :634, deprecated alias).
Everything else — the `include`/`omit` discipline, the `Module.finBasis`/`leftMulMatrix` determinant
route, the `@[scoped simp] coe_constEmb` attribute — is the pin's text.

**Effect on the frontier**: `F` 1146 → **1147** nodes (+697 lines), the D-S demand 1229 → **1228**
nodes / 466,612 → **465,915** lines, and the consumer
`Divisor.mapDomain_placeReduction_eq_ord_of_retraction` drops from 6 nodes / 2,524 lines to **5 nodes /
1,827 lines**. Its single premise call remains `linearIndependent_of_constantFieldExtension`, used once
in `exists_basis_algebraMap`; no new pin citation appeared.

**Pin ranges consumed**: `S_…` 12–104, 106–157, 159–295, 297–667, 672–697 (not 1–11, 669, 670);
`Theorems/Thm_…` 9–29, the headline statement only.
