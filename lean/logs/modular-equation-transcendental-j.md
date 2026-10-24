# The modular equation at transcendental `j` — eight nodes, 543 pin lines, all landed

**Landed 2026-10-23, one set in four sub-sets.** The theory is scoped in
[../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md](../topics/modularCurve/TOPIC-modular-equation-transcendental-j.md);
its forward node landed earlier and has its own record,
[modular-polynomial-velu.md](modular-polynomial-velu.md), which also carries the
standards pass that prepared these homes (§2.6 there). This record covers the
remaining **eight** nodes: the three-node rigidity ladder (M-SET-1), the product
face (M-SET-2), the membership/count support columns (M-SET-3) and the converse
(M-SET-4).

Pin `anthropics/fermats-last-theorem@aa2d8b3` (`git -C ~/proj/fermats-last-theorem
rev-parse HEAD` = `aa2d8b34692b16c70f699536de0d8e75b9a3e9ef`), port Lean `v4.34.0` /
mathlib `v4.34.0`.

## 1. The nodes

Every statement is transcribed verbatim from the pin's `Theorems/` wrapper; the
proof is adapted from the matching `P2M/Sol/S_*.lean`.

| id | declaration | pin `S_` | wrapper | port lines | home |
|---|---|---:|---:|---:|---|
| R1 | `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag` | 14 | 10 | 8 | `WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` |
| R2 | `WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j` | 62 | 21 | 45 | same module |
| R3 | `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental` | 80 | 27 | 31 | appended to `WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` |
| P | `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental` | 97 | 31 | 19 (+58 private helper) | appended to `ModularCurve/ModularPolynomialVelu.lean` |
| M1 | `WeierstrassCurve.j_mem_of_a_mem` | 32 | 7 | 27 | `WeierstrassCurve/Velu/SubfieldMembership.lean` |
| M2 | `WeierstrassCurve.veluQuotient_j_mem_of_mem` | 91 | 11 | 26 (+46 private helpers) | same module |
| C | `WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed` | 22 | 15 | 8 | `WeierstrassCurve/Velu/CyclicSubgroupCount.lean` |
| B | `ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd` | 145 | 25 | 82 (+31 private helpers) | appended to `ModularCurve/ModularPolynomialVelu.lean` |
| | **total** | **543** | 147 | **381 Lean lines** | 3 new modules, 2 appends |

Two homes moved from the topic note's first draft, both as the work order directs and
both for the mathematics rather than the build: **R1** sits beside R2 (its only
consumer is R2's proof; the pair reads as one ladder), and **C** gets its own module
instead of appending to `Velu/CyclicCount.lean`, which owns the *generic*
`AddCommGroup` count — C is the Weierstrass instantiation over `(W⁄K).Point`.

## 2. Modules and their public declarations

### `FLTForHuman/WeierstrassCurve/IsogenyEndDatum/TranscendentalRigidity.lean` (new, 115 lines)

Public: `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag` (a two-line
wrapper over the landed `…isUnit_leadingCoeff_diag_of_not_isSquare`, applied to
`h2 : 2 ≤ N`),
`WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j`.
No private helpers.

The mathematics: a non-scalar `IsogenyEndDatum` endomorphism produces, via the
characteristic-polynomial/degree count and the squarefree values of `a² + t a b + n b²`,
a degree-`N` endomorphism with `N ≥ 2` not a square; the diagonal vanishing
`aeval_j_diag_eq_zero_of_finrankAlong_eq` then makes `W.j` a root of a monic integral
polynomial whose leading coefficient is a unit of `ℤ`, so `W.j` is integral over `ℤ` —
against transcendence.

Imports the five landed premises explicitly
(`FunctionFieldGeneration/Capstone` for `nonempty_modularPolynomialData`,
`ModularPolynomialLeadingCoeff`, `NumberTheory/SquarefreeValues`,
`IsogenyEndDatum/{CharPolySquare,DiagonalPhi}`).

### `FLTForHuman/WeierstrassCurve/Velu/CyclicQuotientJInjective.lean` (grown, 472 → 523 lines)

New public: `WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental`,
which supplies the two `CharZero`/`IsAlgClosed` instances, the two place gates and the
`NormFormulaAlong` family over `𝕂 = HahnSeries ℚ (AlgebraicClosure ℚ)`, then feeds
`hEnd D := IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j W hNs ht' D`
to the landed `…_of_forall_isogenyEndDatum_exists_int`. No new private helpers.

### `FLTForHuman/WeierstrassCurve/Velu/SubfieldMembership.lean` (new, 146 lines)

Public: `WeierstrassCurve.j_mem_of_a_mem`,
`WeierstrassCurve.veluQuotient_j_mem_of_mem`.
Seven `private` helpers, all `private` at the pin too, kept at descriptive names:
`veluGx_mem`, `veluGy_mem`, `veluT_mem`, `veluU_mem`, `veluW_mem`, `veluTSum_mem`,
`veluWSum_mem`. The pin re-exports them into its own proof namespace with
`p2m_export`; no `Theorems/` wrapper carries them, so they are proof-local and are not
diffed.

### `FLTForHuman/WeierstrassCurve/Velu/CyclicSubgroupCount.lean` (new, 55 lines)

Public: `WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed`
— `NeZero n` from `hn`, the torsion equivalence from
`W.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`, then the landed
`AddCommGroup.natCard_isAddCyclic_addSubgroup_eq_dedekindPsi_of_addEquiv_torsionBy`.
No private helpers.

### `FLTForHuman/ModularCurve/ModularPolynomialVelu.lean` (grown, 113 → 376 lines)

New public: `ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental`
and `ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd`.
Three `private` helpers: `fibrePoly_j_eq_prod_of_odd_prime` (the pin's `GAux.main`),
`oddOrderSummingSet_coords_mem` and `exists_generator_of_isAddCyclic` (the pin's
`S13K2` block, renamed out of the machine-token namespace).

The product form: the forward node makes each `j(W/⟨Q i⟩)` a root, R3 makes the family
injective, `ψ(ℓ) = ℓ + 1` supplies the degree count, and
`eq_of_monic_of_dvd_of_natDegree_le` finishes. The converse: the same set equality
inside a fixed subfield `L` (every `j(W/⟨Q i⟩)` in `L` by M2, the roots counted by
`card_roots_fibrePoly_of_monic`, equal cardinality forcing
`Φj.roots.toFinset = Finset.univ.image jH`), whose corollary `r ∈ L` is the pin's public
statement.

## 3. Build and verification

Built with `flock .lake/flt_build.lock timeout 100 lake build <Module>` from `lean/`;
the edit loop is `timeout 100 lake env lean -DautoImplicit=false
-DmaxHeartbeats=200000 <file>`, and **every** declaration of the eight nodes
elaborates at that 200,000-heartbeat cap — no heartbeat bump anywhere, scoped or not.
The project cap is 4,000,000.

| module | build jobs | module time | warnings from the module |
|---|---:|---:|---|
| `…IsogenyEndDatum.TranscendentalRigidity` | 4,506 | 3.2 s | 0 |
| `…Velu.CyclicQuotientJInjective` | 4,517 | 7.1 s | 0 |
| `…Velu.SubfieldMembership` | 2,717 | 2.3 s | 0 |
| `…Velu.CyclicSubgroupCount` | 3,352 | 2.2 s | 0 |
| `…ModularCurve.ModularPolynomialVelu` | 4,522 | 4.1 s | 0 |

**Checker** — `python3 spec/check_port.py <module>`, corpus `aa2d8b3`:

| module | verdict |
|---|---|
| `…/IsogenyEndDatum/TranscendentalRigidity.lean` | 2 ok, 0 mismatch, 0 missing, 0 own, 0 kw |
| `…/Velu/CyclicQuotientJInjective.lean` | 2 ok, 0 mismatch, 0 missing, 0 own, 0 kw |
| `…/Velu/SubfieldMembership.lean` | 2 ok, 0 mismatch, 0 missing, 0 own, 0 kw |
| `…/Velu/CyclicSubgroupCount.lean` | 1 ok, 0 mismatch, 0 missing, 0 own, 0 kw |
| `…/ModularCurve/ModularPolynomialVelu.lean` | 3 ok, 0 mismatch, 0 missing, 0 own, 0 kw |

No `spec/decl_markers.tsv` row was needed: every public declaration is the pin's name
at the pin's statement, so nothing was renamed and nothing is the port's own. No
module was added to `spec/old_check_stmts.py`.

Whole wired set after this set (`spec/check_port.py --changed`, everything cached):
**4950 ok, 0 mismatch, 0 missing, 19 own, 0 kw over 217 modules**, 534 exempt
(`PORT_FILES`), corpus `aa2d8b3`. That is 4,941/213 before the set plus the eight new
declarations.

**Axioms** — `lean/tmp/AxiomsTranscendentalJ.lean` (a probe, not a module; the modules
carry no `#print`):

```
'ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.Affine.IsogenyEndDatum.exists_forall_pointEnd_eq_zsmul_of_transcendental_j' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.zmultiples_eq_of_veluQuotient_j_eq_of_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
'ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j_of_transcendental' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.j_mem_of_a_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.veluQuotient_j_mem_of_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'WeierstrassCurve.natCard_addSubgroup_isAddCyclic_card_eq_dedekindPsi_of_isAlgClosed' depends on axioms: [propext, Classical.choice, Quot.sound]
'ModularCurve.ModularPolynomialData.mem_of_isRoot_map_j_of_transcendental_of_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, no `sorryAx`.

**Warnings.** None from any of the five modules: the 164 warning lines in the
`ModularPolynomialVelu` build log all name dependency modules (40 `DualEndData`, 30
`Velu/Shift`, 26 `Velu/RestrictAlong`, 15 `AlgebraicCurve/P1/TraceEngine`, 12
`Velu/Discriminant`, 11 `P1/PerfectResidue`, 8 `Genus/Stichtenoth`, 8 `Velu/Discharge`,
8 `Velu/Equivariance`, …). They are the cold tree's pre-existing deprecation/simp-arg
and unused-section-variable warnings, replayed.

## 4. Substitutions and deviations from the pin

1. **B's discriminant premise — the 1,045-line detour not taken.** The pin's converse
   calls `WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero h2 W n Q hQ`
   (100 lines), proved through `veluX_oddOrderSummingSet_injOn_psi2Sq_roots` (781) and
   `eval_psi2Sq_veluQuotient_veluX_eq_zero_of_eval_psi2Sq_eq_zero` (164). The port uses
   `WeierstrassCurve.veluQuotient_oddOrderSummingSet_discriminant_ne_zero_of_addOrderOf_eq`
   (`WeierstrassCurve/Velu/Discriminant.lean`), which has the same conclusion with **no**
   `[IsAlgClosed]` and **no** `(2 : F) ≠ 0` — strictly stronger, from the port's product
   formula `…discriminant_prod_veluU_pow`. **None of the three pin nodes is ported** and
   no statement changed. Consequence: the pin's `have h2 : (2 : 𝕂) ≠ 0` inside B is
   dropped (it fed only that lemma); it was a proof-local `have`, not a binder.
2. **R3's `CharZero`.** The pin's private `Ws13B.charZero_hahn` (a `RingHom.charZero_iff`
   argument on `HahnSeries.C`) is spelled
   `charZero_of_injective_ringHom (HahnSeries.C_injective (R := AlgebraicClosure ℚ) (Γ := ℚ))`
   — the same substitution the landed forward module uses.
3. **R3's `normFormulaAlong_of_elliptic`.** The pin's private `Ws13B` copy is the port's
   public `normFormulaAlong_of_elliptic` (`IsogenyEndDatum/Engine.lean`), already imported
   by the host module; no re-derivation.
4. **P's `GAux.main`** is kept as the `private theorem fibrePoly_j_eq_prod_of_odd_prime`
   (the pin's `n`/`m` generalisation, which lets the public statement's `ℓ / 2` be
   identified with `n`). Private, and named for its content rather than the pin's token.
5. **B's `S13K2` block** becomes two `private` theorems at descriptive names,
   `oddOrderSummingSet_coords_mem` and `exists_generator_of_isAddCyclic`; the
   machine-token namespace is not carried.
6. **`ws13B`/`GAux`/`S13K2`/`p2m_*` scaffolding, `attribute [-instance]`/`[-simp]` blocks
   and heartbeat bumps are not transcribed** anywhere. No name from those attribute lists
   is in the port's cone.
7. **One tactic respelling**, for the style linter rather than the mathematics: R3's
   `convert ht using 2 <;> first | rfl | exact Subsingleton.elim _ _` (the pin's text)
   trips `linter.unnecessarySeqFocus`, so the port writes `convert ht using 2` then
   `all_goals first | rfl | exact Subsingleton.elim _ _`. Same proof term.
8. **Linter suppressions** (no heartbeat bumps): the four `haveI`s that bind *instance
   locals* (`NeZero N`, `IsElliptic` on a Vélu quotient) are load-bearing for typeclass
   search, so `set_option linter.style.haveILetI false` is scoped with `… in` to the one
   declaration in `TranscendentalRigidity`, `CyclicQuotientJInjective`,
   `SubfieldMembership` and `CyclicSubgroupCount` (each with a comment);
   `ModularPolynomialVelu` already carries the same option file-wide.
   `SubfieldMembership` also carries the pin's `linter.unusedVariables`/
   `unusedSectionVars` suppressions, which its `variable` block needs.

## 5. Dead code, dedup, promotions

- `python3 tools/deps/dedup.py --module <M> --within --min-cost 0` on all five modules:
  **0 duplicate clusters, 0 removable lines** each.
- `python3 tools/deps/move_dead.py --source lean/FLTForHuman/<path>.lean --target
  lean/Reserve/<…>Dead.lean --select dead --dry-run` on all five: **0 declarations,
  0 lines, 0 live private helpers needed** each. Nothing was shelved, deleted or copied.
- The three `fibrePoly` facts (`monic_fibrePoly`, `natDegree_fibrePoly`,
  `card_roots_fibrePoly_of_monic`) and `ModularCurve.dedekindPsi_prime` are the already
  landed promotions in `ModularCurve/Defs/{FibrePoly,DedekindPsi}.lean`; they are
  imported, not redeclared.

## 6. What was not done, and what a reader should not conclude

- Nothing in the eight nodes was dropped, weakened or left `sorry`. The ψ₂²/discriminant
  block is **not** ported and must not be cited as needed (§2.4 of the topic note): the
  port's discriminant lemma replaces it.
- B's public statement is `r ∈ L`, not `r = j(W/⟨Q⟩)`; the set equality is internal to
  its proof and is not exposed. P is prime-level only (`[Fact ℓ.Prime]`, `ℓ ≠ 2`,
  `card ι = ℓ + 1`); the odd-`N` factorization is a different, still-unported node.
- `Φ_N` remains an **input** datum (`ModularPolynomialData`); this set does not prove its
  existence or integrality.
- No `spec/*Consumer.lean` zone was added for this set (the topic's §3.1 asks for one
  composing P's product with B's root set). It is the natural next step and is the one
  verification instrument this set did not run.

## 8. Consumer zone

`lean/spec/TranscendentalJConsumer.lean` (a `spec/` probe, not a library module)
composes the set: zone 1 reads the product form at one of its own factors, zone 2
hands that root to the converse so it lands in a subfield containing the
coefficients and the `ℓ`-torsion coordinates, and zone 3 composes the count with
`ModularCurve.dedekindPsi_prime` to read `ψ(ℓ) = ℓ + 1`. It elaborates clean in
~4.2 s with `lake env lean spec/TranscendentalJConsumer.lean`; deleting any of the
five modules breaks it.
