# W5 — the ℚ̄ → ℂ descent: the jH injectivity premise

Fifth wave of the aj subject, 2026-10-27. Parent:
[../TOPIC-abel-jacobi-port-structure.md](../TOPIC-abel-jacobi-port-structure.md) (§1, §9.2, §12.1
chain 3). Predecessors, all landed: [PLAN-W1-stokes.md](PLAN-W1-stokes.md),
[PLAN-W2-parabolic-homs.md](PLAN-W2-parabolic-homs.md),
[PLAN-W3b-hecke-equivariance.md](PLAN-W3b-hecke-equivariance.md) and
[PLAN-W4-rank-basis.md](PLAN-W4-rank-basis.md). Pin `anthropics/fermats-last-theorem@aa2d8b34`;
port mathlib `v4.34.0`.

**Decision.** W4 left the Tate identification
`exists_heckeEquivariant_linearEquiv_tateModule_jH_padicInt_tensor_periodLatticeOf` (653) with **one**
unported direct premise, the injectivity node
`exists_injective_heckeEquivariant_addMonoidHom_jH_quotient_periodLatticeOf` (302). Measured today,
that premise's demand splits into **two nearly disjoint bodies**:

```
needed(302) = 132 nodes / 48,469 lines, of which
  302 lines          the glue itself (AJHGlue), needs both bodies
   69 lines          CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem
    6,256 lines      this wave: the jH-injectivity body, 18 nodes
   41,863 lines      the xH-bijective body, 113 nodes (A's mouth, 817, + the period/dictionary body)
```

The two bodies share exactly **one** node, the 21-line
`isCurveOver_of_isAlgClosed_of_transcendental`, so they are independent work and the order between them
is free. W5 takes the jH body: it is the last block of A that is **not** modular analysis. It is the
constant-field-extension descent ℚ̄ → ℂ of places, divisors and derivations — the mathematics §12.1
calls chain 3, "zero period vector ⇒ principal is decided over ℚ̄ and descended", where RR's vanishing
does the deciding.

**What the wave buys and what it does not.** After W5, `needed(302)` reads 114 nodes / 42,213 and
`needed(653)` 115 nodes / 42,866, and A's mouth has exactly one premise left, the xH body. W5 closes no
user-visible node: the 302 is glue over *both* mouths, so the Tate chain still waits on the xH body.
That is the price of taking the cheap half first, and it is deliberate — it retires the non-analytic
half at 0.80 of its raw price while the 41.9k body is being sliced.

## 1. Measurement

`frontier --target …` on the port as it stands (union frontier, `--ds` off, no avoid set):

| reading | value |
|---|---|
| `needed(653)` | **133 nodes / 49,122 lines** (49,122 − 653 = the 302's 48,469) |
| `needed(302)` | 132 nodes / 48,469 |
| of that, the jH body | **18 nodes / 6,256** |
| of that, the xH body | 113 nodes / 41,863 |
| intersection of the two bodies | 1 node / 21 lines |
| unported demand by distance, for 302 | 1: 63, 2: 17, 3: 1 |

The split is exact: 41,863 + 6,256 + 69 − 21 + 302 = 48,469, and 48,469 + 653 = 49,122. W4's §7
projection was 134 / 49,364; the re-measure is 133 / 49,122, i.e. it passes with one node and 242 lines
to spare.

**The eighteen nodes, in the pin's dependency layers** (`port_plan --section layers`; lines are the raw
`S_` files, which is what the frontier prices):

| layer | node | lines |
|---|---|---:|
| 0 | `Place.exists_of_valuationSubring` | 207 |
| 0 | `Place.exists_toValuationSubring_eq_comap_ringHom` | 207 |
| 0 | `Place.exists_ord_algebraMap_eq_mul_ord` | 137 |
| 0 | `Place.exists_comap_eq_toValuationSubring` | 93 |
| 0 | `Place.deg_eq_one_iff_surjective_algebraMap_residueField` | 28 |
| 0 | `isCurveOver_of_isAlgClosed_of_transcendental` | 21 |
| 0 | `Place.inertiaDeg_eq_one_of_isRational` | 13 |
| 1 | `Place.exists_comap_algebraMap_eq_of_constantFieldExtension` | 615 |
| 1 | `Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed` | 401 |
| 1 | `Place.exists_ord_neg_of_transcendental` | 80 |
| 1 | `Place.sum_ramificationIndex_eq_finrank` | 17 |
| 2 | `mem_span_range_algebraMap_of_constantFieldExtension` | 859 |
| 2 | `Place.eq_of_forall_valuation_sub_lt_one_of_constantFieldExtension` | 429 |
| 3 | `Divisor.isPrincipal_of_constantFieldExtension` | 402 |
| 3 | `Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension` | 205 |
| 4 | `exists_derivation_constantFieldExtension_map_mem` | 994 |
| 5 | `Divisor.exists_torsion_descent_of_constantFieldExtension` | 878 |
| 6 | **`ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jH_pic0_complex`** | 670 |

Two ready nodes are already at layer 0 with every premise ported:
`isCurveOver_of_isAlgClosed_of_transcendental` (21) and `Place.inertiaDeg_eq_one_of_isRational` (13).

**What each layer is.** L0 is the valuation-subring ↔ place dictionary of a one-variable function field
(every nontrivial valuation subring containing the constants is a place's; its comap along a ring hom
is a place's; ord along an integral extension is `e · ord`); L1 is the constant-field-extension place
lift (a place of `F` lifts to `F' = K'·F`), the constant-field "constants are base" fact, the existence
of a place with negative order at a transcendental, and the rational-place ramification sum; L2 is the
spanning of `F'` over `K'` and the equality of places from their valuation-below-one behaviour; L3 is
principality descent and the uniqueness of the lifted place; L4 is the extension of a derivation of `E`
to `FE = E·F` that vanishes on `F`, agrees on `E`, and preserves every place's valuation subring
(`AlgebraicCurve.HorizDeriv`); L5 is the descent of `n`-torsion divisor classes; L6 is the modular
packaging.

**The 670 file is not one theorem.** Its 74 declarations are the `K1HBC` construction: the base change
of the function field (`FQ` over ℚ̄, `FC = laurentBaseChange ℂ`, the ring hom `phi` built from
`coeffMap`, the chosen place lift `liftPlace`), and then `iota : JH M H →+ Pic0 ℂ FC` with six
compatibilities (the `coeffMap` reading of `phi`, injectivity, torsion containment, Hecke-T, the
semilinear action, the alg-equiv extension). The
pin's public `solution` is the six-clause existential bundling them. This is the file whose
statement is the wave's mouth, and its definitions are the manager's.

## 1b. Groundwork: `port_advise` and `port_plan` over the wave's 36 files

`port_advise --nodes …` on the eighteen nodes (one `--nodes` per name) resolves 36 files (18 `S_`, 18
`Theorems/` wrappers), 329 declarations; `port_plan --json` reads the same slice. Both are cheap to
re-run and are the wave's price; the numbers below are theirs.

**Budget (`port_plan --section budget`).**

| | lines |
|---|---:|
| raw `S_` lines | 6,256 |
| declaration lines | 5,837 |
| duplicate copies (removable by porting once) | 693 |
| boilerplate (imports/attrs/p2m) | 419 |
| once-cost after dedup | 5,144 |
| already in the port (vetted) | 123 |
| **net new math lines** | **5,021** |

So the wave is **5,021 written**, 0.80 of the raw price.

**The single most important reading: 0 of the 18 headline statements is in the port.** Every
substitution the tool found is a *helper inside* the files, and neither the exact tier nor the
"same name, different statement" list contains a headline. There is no shortcut for the wave's own
content.

**Substitutions: 9 declarations / ≈167 raw lines, all byte-identical and importable** (vetted 123).
The ones that matter, with their port homes:

| pin helper | port declaration |
|---|---|
| `ord_nonneg_of_mem` (4 copies in the wave) | `Place.ord_nonneg_of_mem_vs` (`Canonical/WeilDifferential.lean`) |
| `ord_nonneg_of_mem'` | same |
| `mem_of_ord_nonneg'` | `Place.mem_toValuationSubring_of_ord_nonneg_alt` (`Defs/PlaceEvaluationAlgebra.lean`) |
| `mem_iff_ord_nonneg'` | `TraceDifferentBound.mem_iff_ord_nonneg'` (`Differential/CorrespondenceRegular.lean`) |
| `ord_algebraMap` | `Place.ord_algebraMap_base` (`P1/EnginePrelude.lean`) |
| `coeffMap_qExpand` | `ModularCurve.coeffMap_qExpand` (`ModularCurve/Defs/Laurent.lean`) |
| `isSeparable_of_finrank_fieldRange_frobenius_eq` | `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq` (`Algebra/IsSeparableFrobenius.lean`) |

**14 more names the port already defines with a different binder skeleton — pointers, not verdicts.**
`transcendental_algebraMap` (3 copies, 62 lines) → `ConstantFieldExtension.transcendental_algebraMap`;
`constantsAreBase_of_isAlgClosed` → `ResidueTheorem/RRAssembly.lean`;
`linearIndependent_pow_iff_transcendental` → `RegularProlongationFinrank.lean`; `ord_natCast` →
`Differential/Hurwitz.lean`; `mk_eq_zero_iff` → `WeilExchange/Transport.lean`; plus
`finiteDimensional_adjoin_of_transcendental`, `inertiaDegAlong_eq_one`, `algebraMap_mem`, `T_mem_inf`,
`degree_eq_sum`. **Read the two texts before banking one** (§7's caution, and W4's
`Place.inertiaDeg_pos`): `transcendental_algebraMap`'s pin form carries `[IsAlgClosed K] [CharZero K]`
and an existential `hfg`, while the port's takes `{x} [FiniteDimensional K⟮x⟯ F]` — the port's looks
*stronger*, so the pin's should be a short application, but the shape tier ignores exactly that
difference.

**Port once: 34 names proved in ≥2 of the 36 files, ≈758 lines** (only 20 of it wrapper restatement).
Six blocks carry the structure, and they are this wave's factoring units:

| once | decls | files | content |
|---:|---:|---:|---|
| 192 | 4 | `Divisor_isPrincipal` + `exists_derivation` | `ord_sum_le` 128, `exists_linearIndependent_repr` 41, `ord_pos_of_mem_maximalIdeal` 13, `isUnit_of_ord_eq_zero` 10 |
| 165 | 3 | `mem_span_range` | `exists_basis` 127, `linearIndependent_pow_of_transcendental` 26, `aeval_mem` 12 |
| 119 | 9 | the two `Place` valuation-subring files | `idealOfA_ne_bot` 23, `exists_place_of_mem` 19, `place_of_idealOfA_le` 16, … |
| 116 | 6 | the two `…valuation_sub_lt_one…` files | `exists_centred` 83, `mulMap_injective` 19, … |
| 100 | 4 | `isPrincipal` + `exists_derivation` + `mem_span_range` | `mem_of_ord_nonneg` 62, `exists_sub_algebraMap_mem_maximalIdeal` 22, … |
| 72 | 2 | `exists_comap_algebraMap_eq` + `exists_derivation` | `mem_iff_ord_nonneg` 55, `one_le_ord_of_mem_of_inv_not_mem` 17 |

**Six more names have a duplicate outside the slice**, so their home serves later A waves:
`aeval_mem` (+6 pool files), `coeffMap_qExpand` (+5), `iota_injective` (+5), `T_mem_inf` (+2),
`linearIndependent_pow_of_transcendental` (+2), `exists_basis` (+2).

**Three things `port_advise` cannot see, because it reads declarations and not imports.**

* The 670's proof imports two *ported* nodes, so they cost nothing:
  `ModularCurve.JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`
  (`X1/FunctionFieldBaseChange.lean`) and
  `AlgebraicCurve.linearIndependent_of_constantFieldExtension`
  (`IsCurveOver/ConstantFieldExtension.lean`).
* **`Def_GaloisRep_ComplexConjugation` is not in the port.** The 670's *statement* is written against
  `complexEmbedding : AlgebraicClosure ℚ →ₐ[ℚ] ℂ`, and neither `complexEmbedding` nor
  `complexConjAlgEquiv`/`complexConjugation` occurs anywhere in `FLTForHuman`. It is the 62-line
  mathlib-only definition module (`IsAlgClosed.lift`, `AlgEquiv.restrictNormalHom`, `starRingAut`), a
  `Def_*` unit and therefore the manager's — checkpoint **P0**. The 302's conjugation clauses will need
  the rest of it, so it is ported whole.
* `Def_ModularCurve_XHHeckeOperator` is ported (`XH/HeckeOperator.lean`) and `UpperHalfPlane.J`/`I` are
  mathlib, so nothing else is missing.

## 2. Scope — one body, six layers

Everything in §1's table, and nothing else. Explicitly out of scope:

* **the 302 glue** (302 lines) and its one other premise
  `CuspForm.exists_apply_eq_conj_apply_J_smul_of_forall_jConjSL_mem` (69): the glue needs the xH mouth,
  which this wave does not port;
* **the xH body** (113 nodes / 41,863): the next wave's subject, sliced separately (see §8);
* the ported prerequisites of §1b and the pin's `p2m_*` scaffolding — but **not**
  `Def_GaloisRep_ComplexConjugation`, which is unported and is P0.

The pin's style in this body is uniform and worth stating once: each file has one public
`theorem solution` that is a **one-line application** of a private engine in the same file
(`Place.rowMain`, `Place.mem_range_algebraMap_of_forall_ord_eq_zero_core`, `HorizDeriv.exists_derivation_map_mem`,
`TorsionDescentDeriv.main`, `W7XK1a.isPrincipal_of_constantFieldExtension`, `K1HBC.…`). The engines are
the content, and the ones shared across files are the six blocks of §1b. The port keeps one public
headline per pin node and homes each engine once, private unless a block is shared.

## 3. Order and checkpoints

The chain is strict: `roots → comap lift → mem_span_range → isPrincipal → derivation → torsion descent
→ 670`, with the uniqueness/equality-of-places nodes feeding the derivation. One implementer, not two:
the body is 5k, every layer's nodes are the next layer's premises, and the two independent sub-clusters
(the `Place` descent and the span/derivation algebra) merge at `mem_span_range`.

Checkpoints, each a green module:

0. **P0 `GaloisRep/Defs/ComplexConjugation.lean`** (new, manager) — the pin's
   `Def_GaloisRep_ComplexConjugation` (62 lines): `complexEmbedding` (`IsAlgClosed.lift`),
   `complexConjAlgEquiv`, `complexConjugation` and the `ExtCitation` archimedean block, with the pin's
   local instances. P6's statement is written against `complexEmbedding`; the 302's later conjugation
   clauses need the rest. It is the wave's only `Def_*` unit, and it is independent of P1–P5.
1. **P1 `AlgebraicCurve/Place/FromValuationSubring.lean`** — the two layer-0 roots
   (`exists_of_valuationSubring` 207, `exists_toValuationSubring_eq_comap_ringHom` 207) and their shared
   ten-helper prelude (119 lines once). This is the wave's only self-contained prelude and it is what
   the pin's files duplicate most (119 + 40 + 18 lines across three files).
2. **P2 `AlgebraicCurve/Place/ConstantFieldExtension.lean`** — the place-descent cluster:
   `exists_comap_algebraMap_eq` (615), `mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed`
   (401), `eq_of_forall_valuation_sub_lt_one` (429), `existsUnique_valuation_sub_lt_one` (205),
   `exists_ord_neg_of_transcendental` (80), `deg_eq_one_iff_surjective_algebraMap_residueField` (28),
   `sum_ramificationIndex_eq_finrank` (17), `inertiaDeg_eq_one_of_isRational` (13).
3. **P3 `AlgebraicCurve/IsCurveOver/ConstantFieldExtensionSpan.lean`** (new;
   `isCurveOver_of_isAlgClosed_of_transcendental` 21 appended to `IsCurveOver/Transcendental.lean`) —
   `mem_span_range_algebraMap_of_constantFieldExtension` (859) and its 165-line block.
   **Not appended to the legacy `IsCurveOver/ConstantFieldExtension.lean`** (the fallback this plan
   allowed): that module sits *below* `Place/ConstantFieldExtension.lean`, because the P2 place-descent
   nodes consume its `linearIndependent_of_constantFieldExtension`, while the 859 file needs the P2
   place lemmas — an append would be an import cycle. The legacy module therefore stays byte-identical
   and unwired; the new span module sits above both and is wired. (Measured on landing: it was a
   one-for-one port, so the cycle is the only reason.)
4. **P4 `AlgebraicCurve/Differential/ConstantFieldExtension.lean`** —
   `exists_derivation_constantFieldExtension_map_mem` (994) and the shared 192-line engine
   (`ord_sum_le`, `exists_linearIndependent_repr`, …), which is public here because P5 imports it.
5. **P5 `AlgebraicCurve/Genus/ConstantFieldExtension.lean`** —
   `Divisor.isPrincipal_of_constantFieldExtension` (402) and
   `Divisor.exists_torsion_descent_of_constantFieldExtension` (878).
6. **P6 `ModularCurve/XH/JHDescent.lean`** — the 670 headline and its `K1HBC` definitions.
7. **P7 close** — wire, `dedup`/`move_dead`, axioms, re-measure.

P1 and P2 are the wave's safe half (2,200 raw); P3–P5 are the algebra; P6 is packaging. If P4 stalls,
P5 and P6 stall with it (the torsion descent cites the derivation), so P4 is the risk checkpoint.

## 4. Homing

| block | module | why |
|---|---|---|
| P0 (complex conjugation) | `GaloisRep/Defs/ComplexConjugation.lean` (new) | `GaloisRep/Defs/` is the port's home for `Definitions/Def_*` (`Adic`, `GaloisAction`, `Residual`, …); the module is mathlib-only and sits below every consumer |
| P1 (valuation-subring ↔ place) | `AlgebraicCurve/Place/FromValuationSubring.lean` (new) | `Place/` already hosts `IsPrimeOverValuationSubring`, `ValueDictionary`, `DegreeOne`; `ValueDictionary` is the value/residue dictionary and does not own this converse direction |
| P2 (place descent under the constant extension) | `AlgebraicCurve/Place/ConstantFieldExtension.lean` (new) | the nodes are all `Place`/`ord` statements over `F ⊆ F' = K'·F`; `IsCurveOver/` already imports `Place/FiniteResidue`, so the direction is established |
| `isCurveOver_of_isAlgClosed_of_transcendental` (21) | append to `AlgebraicCurve/IsCurveOver/Transcendental.lean` | beside the two headlines already there; it is the `[IsAlgClosed K]` specialization of the same constructor |
| P3 (spanning over the constant extension) | `AlgebraicCurve/IsCurveOver/ConstantFieldExtensionSpan.lean` (new) | `mem_span_range` is the spanning counterpart of the legacy module's linear independence, but it needs the P2 place lemmas and the legacy module is below them, so it cannot be appended; the new module imports both and is the only home that closes |
| P4 (derivation extension) | `AlgebraicCurve/Differential/ConstantFieldExtension.lean` (new) | Kähler/derivation content, beside `Coefficient`, `TraceDiff`, `Hurwitz`; `Genus/` imports `Differential/`, so P5 can take the 192 block from here |
| P5 (principality and torsion descent) | `AlgebraicCurve/Genus/ConstantFieldExtension.lean` (new) | the RR-level descent of §12.1 chain 3; `Genus/` is the RR home (`Stichtenoth`, `DegreeIdentity`, `Index`) |
| P6 (the jH headline + `K1HBC`) | `ModularCurve/XH/JHDescent.lean` (new) | `XH/` owns the xH function field, its Hecke inputs and operators; the node is the ℚ̄ → ℂ base change of that field, not period-lattice content |

## 5. Decisions

* **D1 (inherited).** Pinned statements verbatim; headlines public at the pin's names with the pin's
  qualified spellings intact; helpers `private` unless two modules need them. Here six helper blocks
  *do* cross files (§1b), so they are public and homed, not private copies — the pin's own duplication
  is the thing this wave must not reproduce.
* **D2 — the six blocks are ported once, into the homes of §4.** The 119- and 116-line blocks sit with
  their P1 and P2 nodes; the 192 belongs to P4 (P5 imports `Differential/`); the 165 to P3; the 100 and
  72 to P1/P2 according to content (the `maximalIdeal` pair is P1's subject, the `ord`-iff pair P2's),
  both below every consumer. This is where the 693 duplicate lines go, and the plan's budget already
  assumes it.
* **D3 — drop the global walls, keep the local registrations.** The 670 file has three global wall
  lines (`[-instance]` / `[-simp]`, several hundred entries between them) and six
  `attribute [local instance]` registrations of the section's own
  `algebraMap`/`IsScalarTower`/`IsCurveOver` facts. The three global walls are dropped in full; the six
  local ones are load-bearing (the pin's `letI`-wall in another spelling) and travel with the section.
  Policy unchanged from W3b/W4 for everything else: prefer a local `include`/`omit` or an explicit
  instance argument, **record which lemma needed which**, never reinstate a global attribute. If more
  than a handful turn out to be needed, that is an instance-design defect to report, not to paper over.
* **D4 — the shape-tier pointers are read, not imported.** For
  `transcendental_algebraMap` (the pin's 62 lines in three files), `constantsAreBase_of_isAlgClosed`,
  `linearIndependent_pow_iff_transcendental`, `ord_natCast` and `degree_eq_sum`, read the two texts
  first: if the port's form is stronger, the pin's is a short application; if the hypotheses differ in
  kind (as `transcendental_algebraMap` does), the pin's statement is written and the port's is used
  inside its proof. Never import through the shape tier alone.
* **D5 — the pin's `solution := engine.main` shape is kept.** One public headline per node, the engine
  as the same file's private block, and a shared engine promoted to the home named in D2. The checker
  diffs public statements only, so the private engines are free to differ in name and spelling; this is
  also what makes the 693 dedup lines land without touching a headline.
* **D6 — no `--ds`, no prune, plain reading.** The wave's price is taken on the union frontier with no
  avoid set: `§7` of the topic records why the prune is not a scoping instrument here, and W4's
  re-measure (133 / 49,122) is the number this plan is built on.

## 6. Budget

**5,021 net new math lines** for the eighteen nodes, on 5,837 declaration lines (6,256 raw, 693
duplicates, 419 boilerplate), 123 already in the port; plus P0's 62-line definition module, i.e.
**≈5,083 written** at W4's transcription ratio of ≈1.0. Split roughly: P0 60, P1 ≈300, P2 ≈1,500,
P3 ≈750, P4 ≈850, P5 ≈1,050, P6 ≈600.

Upside risk is P4's 994-line derivation (the only node that mixes `Derivation` with `IsCurveOver` and
place valuations) and P3's 859-line span. Downside: the six shared blocks are net savings, not costs;
the plan does not subtract them twice. The manager layer adds no math but the wires: the new P1/P2/P3span/P4/P5/P6 modules' `spec-pin` blocks and the two extra pins of `IsCurveOver/Transcendental.lean`.

## 7. Verification

The W4 wire, unchanged:

* `spec-pin:` in each new or touched module naming the pin's `S_` file and the `Theorems/` wrapper;
* `python3 spec/check_port.py <module> --force` → `0 mismatch / 0 missing / 0 own`. No legacy module is
  touched: `IsCurveOver/Transcendental.lean` is already wired and gains the `isAlgClosed` node's two
  pin sources, and the new P1/P2/P3span/P4/P5/P6 modules are wired for the first time;
* `#print axioms` = `[propext, Classical.choice, Quot.sound]` on all eighteen headlines, from one
  scratch module;
* one module at a time, `timeout 110 lake build <Module>`, logs in `lean/tmp`, no tree build, no
  warnings, no `sorry`/`axiom`/`native_decide`;
* `tools/deps/dedup.py` and `move_dead.py` on the new modules after they close; `port_plan`'s 693
  duplicates is the baseline the dedup should confirm;
* **re-measure, in this order:** `needed(302)` should read **114 nodes / 42,213** and `needed(653)`
  **115 nodes / 42,866**, with the xH body (113 / 41,863) now the only unported premise under the 302.
  If either is off, the difference is the finding.

## 8. First moves

1. **Manager layer.** Read the 670's `K1HBC` block and the six shared blocks; land the module
   skeletons with the pin's definitions (`HFG`, `sigmaR`, `phi`, `liftPlace`, `iota`, the `FQ`/`FC`
   abbreviations) and the statements of the eighteen headlines; write the `spec-pin` blocks. This is
   the `Def_*`-and-refactor part of the wave (the port instructions' "Manager must do `Def_*` nodes"),
   and it fixes the statements before any proof is written.
   **P0 first** — `GaloisRep/Defs/ComplexConjugation.lean`, 62 lines, because P6's statement cannot
   even be elaborated without `complexEmbedding`.
2. **P1** — the valuation-subring roots and their prelude. Smallest checkpoint, and it discharges the
   wave's largest pin-internal duplication.
3. **P2** — the place descent in layer order, with the ready `inertiaDeg_eq_one_of_isRational` (13) and
   `deg_eq_one_iff_surjective_algebraMap_residueField` (28) as openers.
4. **P3**, **P4**, **P5**, **P6** in that order (P0 is done in the manager layer); each is a green
   module and a re-read of the next layer's pin file before writing it.
5. **Close**: wire, axioms, `dedup`/`move_dead`, re-measure. Then the xH body — a separate plan, priced
   by its own `port_advise` run over its 113 `S_` files, whose measured blocks are
   the fibre-sum/`UpperHalfPlane` pair (`eventually_abelFibreSumOf_sub_mem_periodLatticeOf` 1,547 with
   ten nodes, 4,982), the row-2 pairings (810 + 1,052 + 596 + 874 + 693), the dictionary
   (`ComplexPlaceDictionaryOf` 22 nodes / 9,244 + `exists_complexPlaceDictionaryOf` 441 + the
   `realizeOf` family), the multiplier/`meromorphicOrderAt` family, and the mouth 817 last.

## 9. Execution

One implementer for the proof bodies, manager for definitions, homes, wiring and the final
`dedup`/`move_dead`; the execution contract is
[WORKORDER-W5-jh-injectivity.md](WORKORDER-W5-jh-injectivity.md), scoped to the eighteen nodes with the
layer order of §3, the build discipline of `porting-playbook.md` (one module at a time, `timeout 110`,
log in `lean/tmp`, no tree build), and an early blocker report for P4. No polling: the implementer
reports at each checkpoint.

**Manager layer, landed 2026-10-27.** P0 is in
`FLTForHuman/GaloisRep/Defs/ComplexConjugation.lean` (the pin's 62-line module, three mathlib imports
rather than the pin's `import Mathlib`, silent green build); the workorder is written; P0–P2 are green
and wired (P1 2 ok, P2 41 ok, `Transcendental` 4 ok), and the place prelude's four shared pieces were
re-spelled to the pin's section-variable binder shape rather than excused with markers. P3's 859 node
moved to `IsCurveOver/ConstantFieldExtensionSpan.lean` on the import-cycle finding above.

**P3 closed.** The span module is 862 lines and wired at **29 ok / 0 mismatch / 0 missing / 0 own**;
`move_dead` 0; `dedup` reports one 19-line `name`-tier cluster — the public headline
`AlgebraicCurve.mem_span_range_algebraMap_of_constantFieldExtension` and its engine
`W7XH.mem_span_range_algebraMap_of_constantFieldExtension` — and that is the pin's own
engine-plus-wrapper structure, a false positive of the kind W4's §1b recorded, not a removable
duplication. The engine is `private` here, so only the headline is on the wire; the 165-line block
(`W7XH.exists_basis`, `…linearIndependent_pow_of_transcendental`, `…aeval_mem`) stays public and
matched — the pin declares those three publicly in its `S_` file, and no other module of the wave
consumes them, so this is the pin's surface kept, not a helper exposed.

**P4 closed.** `Differential/ConstantFieldExtension.lean` is 921 lines and wired at **5 ok / 0 mismatch /
0 missing / 0 own** (the 994 headline, the public 192-line block minus the imported pair, and the
pin-shaped `ord_pos_of_mem_maximalIdeal` adapter; the P5 `isPrincipal` `S_` file is its second wire
source because the block is declared there too). `move_dead` 0 after deleting one 3-line unused private
alias; `dedup`'s one 20-line `shape` cluster is again the engine-plus-headline pair — the pin's own
structure, not removable duplication. One manager-level promotion was made for P5: the alg-closed
`degree_eq_sum` (4 lines, the pin repeats it in its `isPrincipal` file) is now public as
`AlgebraicCurve.W7XH.degree_eq_sum` in the span module, with the `isPrincipal` `S_` file added to that
module's wire.

**P5 closed.** `Genus/ConstantFieldExtension.lean` is 1,027 lines and wired at **2 ok / 0 mismatch /
0 missing / 0 own** (the two headlines only — every `W7XK1a`/`TorsionDescentDeriv` engine is `private`,
which is what P6 needs). `move_dead` 0 (the pin's four declared-and-unused helpers were omitted, as the
pin itself never calls them). `dedup` reports two `shape` clusters, 38 and 23 lines, each an engine
(`isPrincipal_of_constantFieldExtension` 94 lines, `TorsionDescentDeriv.main` 239) against its public
one-line application — the same engine-plus-headline false positive as P3/P4, not removable. The
torsion-descent proof is where §12.1 chain 3 actually lands: RR's vanishing is decided over the
algebraically closed base and descended, on the ported `Genus/Index` + `Genus/Stichtenoth` facts.

**P6 closed, and the wave with it.** `ModularCurve/XH/JHDescent.lean` is 849 lines and wired at
**68 ok / 0 mismatch / 0 missing / 0 own** — the 670 headline and the whole `K1HBC` construction (63
public declarations, the pin's names, `phi`, `liftPlace`, `conorm`, `iota` and the six compatibilities).
`dedup` 0, `move_dead` 0. Two manager interventions were needed and both are findings:

1. **The `SemilinearAut` action on `Divisor`/`Pic0` was unported**, and the 670's *statement* needs
   `g • x`: the implementer wrote it privately at the head of the module and flagged it. It was
   re-homed to its decided home, `AlgebraicCurve/Defs/SemilinearAut.lean` (whose header names this block
   as its own and had deferred it), public at the pin's names, with the `DistribMulAction` on `Pic0`
   added so the API is complete; the torsion/`ZMod`/`torsionRep` half of the same pin section stays
   deferred there. `dedup`/`move_dead` 0 on that module too.

   **Review of the re-home.** The ten named statements are transcribed exactly, but the frozen
   checker (`spec/old_check_stmts.py`, which owns this module through its transcribed-definition
   list) read the port's three *named* instances `divisorDistribMulAction`/`pic0SMul`/
   `pic0DistribMulAction` as `MISSING IN FLT`: the pin's instances are anonymous, `DECL_RE` sees no
   unnamed instance on either side, so a port-side name is visible exactly where the pin's is not.
   That is the same mechanism as the 670's `scoped` instances above (item 2), and it is now fixed
   the same way — the three are anonymous, as the pin writes them. The module reads **43 ok / 0
   mismatch / 0 missing / 0 own**, `dedup`/`move_dead` still 0, and the header records the rule. The
   header's block ranges were also off the pin's real boundaries and are now exact: 15–195,
   197–289, 291–355 (for 15–206, 206–290, 290–356). One honest caveat on the `dedup` 0: the module
   now carries the pin's two spellings of the Divisor action side by side (the `F ≃ₐ[K] F` block
   from `Def_AlgebraicCurve_DivisorClassGroup.lean` and the new `SemilinearAut` block, five laws
   each). Their statements differ by the scalar type, so they are not interchangeable and `dedup`
   reports them as a `generalise` row of cost 0 — the pin's own duplication, kept.

   **Handed over (same day).** Since the module had to be touched, it was brought to the current
   protocol rather than left on the frozen registry: its header now carries `spec-pin:` lines for
   `Def_AlgebraicCurve_BaseChangeGalois.lean` and `Def_AlgebraicCurve_DivisorClassGroup.lean`, and
   `check_port.py --force` diffs all 43 declarations with **no marker row in
   `spec/decl_markers.tsv`**. The `PORT_FILES` entry is replaced by a handover comment (the file is
   frozen; handing a module over is the documented removal, and the corpus went 299 → 300 modules,
   504 → 503 exempt). The header prose was rewritten in the current shape and carries no
   doc/module cross-references, and `spec/AlgebraicCurveConsumer.lean` gained **zone M**, which
   *executes* the block — order along the moved place, degree, principal invariance, `Pic0`
   additivity and the `degZero` descent — instead of only diffing it. That consumer was one error
   short of the gate before this: its zone C still `#check`ed `Place.inertiaDeg_pos`, the weak node
   the T2 wave deliberately did not port in favour of
   `Place.inertiaDeg_pos_of_finiteDimensional`; the line now names the ported one and the consumer
   is back at 0 errors.

   **The tail is landed too (port-whole).** Two declarations outside the module had recorded the
   missing action as their blocker — `ModularCurve/X1/Diamond.lean`'s `diamondOneBar` pair and the
   `PicAction` section of `ModularCurve/Defs/ArithmeticGalois.lean` — but the tail was three links
   deep, not one: `JZero.torsionGaloisRep` in the same `ArithmeticGalois` section needs
   `SemilinearAut.torsionRep`, which is the pin's torsion half (lines 291–355), which needs
   `Pic0.torsion` — a declaration the port never had. "Deferred on scope" is not a reason under
   port-whole, so the whole chain is landed in pin order:

   * `Defs/Divisor.lean`: `Pic0.torsion` and `Pic0.mem_torsion` (pin 244–247), **18 ok**;
   * `Defs/SemilinearAut.lean`: the torsion half, nine declarations with the pin's four instance
     names, so the module is the whole pin file 15–355, **52 ok**;
   * `ModularCurve/Defs/ArithmeticGalois.lean`: `PicAction` (the `L ≃ₐ[ℚ] L` action on `Pic0`
     through `arithmeticGalois`) and `JZero.torsionGaloisRep` with its two lemmas, **13 ok**;
   * `ModularCurve/X1/Diamond.lean`: `diamondOneBar` and `diamondOneBar_apply`, so the file is
     verbatim, **14 ok**.

   All four are handed over (`spec-pin:` lines, removal from `PORT_FILES`), `dedup`/`move_dead`
   0 on each, and the corpus is **6,631 ok / 0 mismatch / 0 missing / 32 own, 303 modules,
   500 exempt** — the 54 added statements are exactly 18 + 9 + 13 + 14. One API point: the port's
   `ModularInstance` section carried a `[NeZero N]` that neither the pin's section nor
   `modularFunctionFieldFull` needs, which surfaced as an unused-section-variable warning on the
   two new lemmas. It is dropped from the `variable` line rather than `omit`ted per declaration —
   that reproduces the pin's API exactly (`#check` shows no instance on any of the three) and
   changes nothing that was in the committed surface, since the two abbrevs never took it either.
   The consumers are extended: `AlgebraicCurveConsumer`'s zone M gains the torsion action, and
   `ModularCurveConsumer` gains zone Y over the two modular modules; both are at 0 errors.

2. **The two layer-0 roots were not public.** This workorder's own first draft told the implementer to
   write them as "private engines of the P2 files", which is wrong: each has its own `S_`/`Theorems/`
   pair and is a public node. They were added as one-line headlines over the shared `rowMain` engine
   (`Place.exists_ord_algebraMap_eq_mul_ord`, `Place.exists_comap_eq_toValuationSubring`) and wired;
   P2 is 43 ok. The `Fact` instances of the 670 file were kept `scoped` as the pin writes them, with
   `open scoped K1HBC` replacing the pin's `p2m_reactivate` — that is also what makes them
   checker-invisible, so no marker was needed (an `own:`/`pin:` marker cannot reach a `scoped
   instance`).

**Wave close (P7).** Corpus: **6,532 ok / 0 mismatch / 0 missing / 32 own, 299 modules, 504 exempt** —
all 32 `own` are pre-existing port-authored or renamed statements, none from this wave. `#print
axioms` on all eighteen headlines from one scratch module: exactly
`[propext, Classical.choice, Quot.sound]`, no exceptions.

**Corpus after the P6 handover.** Re-run the same day: **6,631 ok / 0 mismatch / 0 missing / 32 own,
303 modules, 500 exempt** — the handovers add `Defs/SemilinearAut.lean`, `Defs/Divisor.lean`,
`ModularCurve/Defs/ArithmeticGalois.lean` and `ModularCurve/X1/Diamond.lean` to the wired set with
their 43 + 9 + 13 + 14 declarations, and the consumer gate is 0 errors again. The counts are the
instrument's; the module
is on the wire from now on, not on the frozen list.

**Re-measure, and it is exact.** `needed(302)` = **114 nodes / 42,213 lines** and `needed(653)` =
**115 nodes / 42,866**, i.e. §1's projection to the node and to the line (132 − 18, 48,469 − 6,256;
133 − 18, 49,122 − 6,256). The 113-node / 41,863-line xH body is now the only unported premise under
A's mouth, and §8's next step is untouched by this wave.
