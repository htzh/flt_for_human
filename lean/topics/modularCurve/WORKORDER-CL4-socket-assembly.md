# WORKORDER-CL4 — the socket assembly, and the transport that reaches `hall`

Status: **open**, dispatched 2026-10-25. Owner: the set's agent, reviewed by the manager.
Depends on: WORKORDER-JQ2 (`jqNModC_mem_modularFunctionFieldC_mul_prime`) for its `hKG1` slot.
Either order may land first — `hKG1` is a *parameter* of `pkg_of_socket`, so this order compiles
against JQ2's statement as soon as that statement exists.

The nodes, with what is actually new in each (the measurement is §10.3 of the topic
[TOPIC-qexp-function-field-c.md](../functionFieldGeneration/TOPIC-qexp-function-field-c.md)):

| node | pin `S_` | raw | already in the port | new |
|---|---|---:|---|---:|
| `ModularCurve.package_of_socket` | `S_ModularCurve_package_of_socket.lean` | 1,003 | 74 of 82 declarations (`S_:39–780`), `port_advise` 56 of 85 statements ≈657 lines | **223** |
| `ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` | `S_…_of_socket.lean` | 518 | 38 of 55 declarations (`S_:1–276`) | **242** |
| `ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` | `S_…_of_charZero.lean` | 518 | **same development, port once** (the two files differ in 32 lines of namespace plumbing only) | — |
| `ModularCurve.map_intCast_pow_char_eq_qExpand` | `S_…_map_intCast_pow_char_eq_qExpand.lean` | 176 | 4 of 14 declarations (the `laurentMap*` block at 75–120 is the pin's, `qExpand_ofPowerSeries_eq_expand` 75, `pow_char_single_one_eq` 104, `pow_char_ofPowerSeries_eq` 112, `intCast_pow_char_eq` 146) | **≈100** |
| `ModularCurve.qExpand_jqModC_eq_pow_unconditional` | `S_…_qExpand_jqModC_eq_pow_unconditional.lean` | 105 | 10 of 14 declarations (`S_:17–83` is the ported `jqModC`/`coeff`/`order` API re-stated) | **22** |

**This is not a transcription job.** The two socket files are a ported prefix plus a 223-line and
a 242-line tail respectively; copying the files whole writes ~1,150 lines to deliver 465. The
assembly goes into the module that already owns `fullC`, `eFull`, `divSet` and
`relfinrank_fullC_step`; the transport gets its own `Degree/` module (the `PrimeNonAdjoin` /
`JqCyclotomicConjugates` pattern).

**Ground already laid (2026-10-25, manager).** `Pkg` is in the tree: `ModularCurve.Pkg` is an
`abbrev` at `Defs/JqCoeff.lean:253`, statement verbatim the pin's `S_:781`. The four `private`
`hall` hypotheses of `SlotProductAnyField` now take `Pkg K M` (the two *public* headlines keep the
pin's spelled-out text — see §4.1), so the assembly's statements write `Pkg K M` from the start.

## 1. What the mathematics is

**The socket is the induction over divisors.** The pin's `Pkg` is the `hall` statement:

```
Pkg K M := ∀ d, d ∣ M → ∀ [NeZero d],
  finrank K⟮j(q)⟯ (K⟮j(q)⟯⟮j(q^d)⟯) = dedekindPsi d
  ∧ modularFunctionFieldC K d = K⟮ j(q^d') ∣ d' ∣ d ⟯
```

`pkg_of_socket` proves `Pkg K M` from the prime step (`hKG1`, JQ2) by induction on `M` over the
divisors: write the cofactor as `d = e * q` with `q = minFac`, peel it with
`mffC_eq_fullC_of_steps`, and read the degree off `tight_iff_relfinrank_fullC` plus the
prime-power tower. The ingredients, all already ported or free:

- `relfinrank_adjoin_insert` and `dedekindPsi_mul_of_coprime` — the tower arithmetic;
- `relfinrank_fullC_step` / `relfinrank_fullC_mul_prime_pow` (CL2) — the `(p + 1) * p^a` level step;
- `dedekindPsi_prime_pow` — the arithmetic evaluation;
- `jqNModC_prime_not_mem_fullC` (CL1) — what `hnm` is;
- `fullC_one`, `adjoin_jqModC_le_fullC`, `fullC_mono` — the trivial end of the tower;
- `hKG1` (JQ2) — the only new input.

So the new lines are glue: an `abbrev`, five short congruence/containment lemmas, the induction,
and the tower composition.

**Why a transport module is needed.** `package_of_socket` wants a primitive `d`-th root of unity,
which `K` need not contain. The pin therefore proves over `AlgebraicClosure K` (where `ζ` exists),
and descends: `finrank_adjoin_jqNModC_eq_of_map σ` takes the statement over `K'` to the statement
over `K` for `σ : K →+* K'`, by transporting `phiAtSeed data (jA K)` along `tauAdjoin σ` and
comparing `minpoly`s. That descent is the whole content of the second file. Its direction is
**downward only** — the ported ℚ twin (`ModularPolynomialUniqueness.lean`) cannot be pushed up to
an arbitrary `[Field K]`, which is why the socket is not avoidable: see the topic §10.3.

## 2. Module plan

### P1 — the assembly, appended to `ModularCurve/FunctionFieldGeneration/PrimePowerStepAnyField.lean`

Nine declarations, names as the pin's: `mffC_congr`, `fullC_congr'`, `adjoin_jqModC_le_fullC`,
`fullC_one`, `tight_iff_relfinrank_fullC`, `mffC_eq_fullC_of_steps`,
`relfinrank_fullC_prime_pow_tower`, `pkg_of_socket`, and the public headline `package_of_socket`.

`Pkg` itself is **already in the tree** (`ModularCurve.Pkg`, `Defs/JqCoeff.lean:253`, landed
2026-10-25): import it, do not declare a second copy. It is the pin's own `abbrev`, so the checker
diffs it by statement, and the assembly's statements can write `Pkg K M` from the first line.

The module's header gains two `spec-pin:` lines (`P2M/Sol/S_ModularCurve_package_of_socket.lean`,
`Theorems/Thm_ModularCurve_package_of_socket.lean`) beside the two it already carries.

### P2 — `ModularCurve/Degree/FinrankAdjoinJqNModC.lean` (new, wired)

The transport and the two headlines, from `S_…_of_socket.lean:277–518` (the twin's content is the
same; port it once and wire both `Theorems/` wrappers):

- the `PoleOrder` block: `coeff_algebraMap_mul`, `coeff_aeval_jqModC_neg_natDegree`, and
  `aeval_jqNModC_phiAtSeed_jA`;
- the `Transport` section: `coeffMap_algebraMap_eq`, `coeffMap_jqModC_eq`,
  `coeffMap_jqNModC_eq`, `coeffMap_aeval_jqModC_eq`, `exists_map_eq_of_aeval_eq_coeffMap`,
  `jqNModC_not_mem_adjoin_of_not_mem_adjoin`, `coeffMap_mem_adjoin`, `def tauAdjoin`,
  `tauAdjoin_jA`, `finrank_adjoin_jqNModC_eq_of_map`;
- `natCast_ne_zero_of_socket`, `jqNModC_prime_not_mem_adjoin_of_ringHom`;
- the two headlines: `finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket` (binders from
  `Theorems/Thm_ModularCurve_finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket.lean`) and
  `finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` (binders from the `_of_charZero` wrapper).

**Omit** the pin's `private` `finrank_adjoin_jqNModC_sq_eq_of_socket` and
`…_sq_mul_prime_eq_of_socket` unless a consumer names them: they are unused convenience
specialisations of the headline, and `move_dead.py` will flag them if ported.

`coeffMap_jqModC_eq` is already `map_jqModC` in `Defs/JqCoeff.lean`; call it, do not restate it.

### P3 — `ModularCurve/Defs/QExpandCharP.lean` (new, wired)

The two char-`p` Frobenius facts, small and independent of the socket:
`map_intCast_pow_char_eq_qExpand` (176) and `qExpand_jqModC_eq_pow_unconditional` (105). They are
premises of the second file's `natCast_ne_zero_of_socket`, so they can be done first and in
parallel. Measure before asserting the price — `port_advise.py -t` on each has not been run; the
port may already hold most of both (`qExpand_*_TS`, `qExpand_jqNModC`).

### P4 — wiring, use test, dedup

- `spec/check_port.py` on the three touched modules with all `spec-pin:` lines, and `own:` markers
  where the port owns a lemma.
- **The use test**: `spec/DsHeadConsumer.lean` gains a zone that instantiates
  `finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` (at `K = ℚ` and a concrete `d`) and
  `package_of_socket` (at `M = 1` or a small prime), so that deleting or renaming either breaks
  the consumer. Per CL3 §4.2 this use is what pins the statements, alongside the checker.
- `dedup.py` / `move_dead.py` over the three modules; the `hall`-spelling duplication is the
  expected residue — record it rather than forcing a cross-module refactor of a wired module.

## 3. What the port already has — import, do not restate

`fullC`, `eFull`, `divSet`, `qExpandₐK`, `jqNModC_mem_fullC`, `fullC_le_iff`,
`relfinrank_*_insert*`, `relfinrank_fullC_step`, `relfinrank_fullC_mul_prime_pow`,
`fullC_mul_prime_eq_adjoin_insert_image` — all in `PrimePowerStepAnyField.lean`.
`jqNModC_prime_not_mem_fullC`, `minpoly_jqNModC_map_eq_prod_slots` — `SlotProductAnyField.lean`.
`dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime` — `Defs/DedekindPsi.lean`.
`isIntegral_jqNModC_of_modularPolynomialData` — `X1/IntegralityJqNModC.lean`.
`Pkg` — `Defs/JqCoeff.lean` (landed 2026-10-25).
`splits_prime_at_slot_of_isPrimitiveRoot`, `roots_*_of_isPrimitiveRoot`,
`isRoot_prime_at_slot_iff_of_isPrimitiveRoot` — `PhiGenSplitsAnyField.lean`. `phiAtSeed*` —
`Defs/PhiAtSlot.lean`. `exists_phiIrreducible(_evalSymm)` — `ModularPolynomialProperties.lean`.
`map_jqModC` — `Defs/JqCoeff.lean`. Checker expectation: `PrimePowerStepAnyField`'s header already
carries the two `spec-pin:` files of `relfinrank_fullC_mul_prime_pow`; the ten additions extend that
list, and each must read `ok` against the pin's `S_:781–1003`.

## 4. Known drifts — read these before transcribing

1. **`Pkg` is an `abbrev` and must stay one** — its reducibility is what lets the induction apply
   `hall`-typed data as the conjunction it is. It is landed at `Defs/JqCoeff.lean` with the pin's
   verbatim statement. The port's two *public* CL1 headlines (`minpoly_jqNModC_map_eq_prod_slots`,
   `jqNModC_prime_not_mem_fullC`) still spell the block out and must keep doing so: the checker
   hashes statement *text* and does not unfold abbreviations, so restating them as `Pkg K M` would
   read `MISMATCH`. Their four `private` neighbours were restated on 2026-10-25; do not restate
   the public ones.
2. **Dead guards in statements stay**: `if h : …` and friends are part of the pin's text, and the
   checker diffs text.
3. **Keep `hstep`/`hgen'` as hypotheses** in `mffC_eq_fullC_of_steps`; the pin passes `pkg_lt` at
   the recursive call. Do not weaken them into the induction.
4. **The `_of_charZero` twin**: the two `S_` files are one development (32 differing lines: two
   namespace paths and two `first | rfl | simp`). Port once, let the checker wire both wrappers to
   the same module.
5. **`coeffMap` spellings**: get `coeffMap_jqNModC_eq` from `map_jqModC` plus `coeffMap_qExpand`;
   do not re-prove `coeffMap_qExpand`.

## 5. Gates (all green, and report the readings)

1. `lake env lean` then single-module `lake build` for each touched module — **never a tree
   build**; each call inside the project's 2-minute rule, output logged to `lean/tmp/`.
   0 warnings; `#print axioms` on both headlines reads `[propext, Classical.choice, Quot.sound]`.
2. `cd lean && python3 spec/check_port.py <three modules>` → **0 mismatch, 0 missing**; the new
   readings for `PrimePowerStepAnyField` and the two new modules are the order's numbers.
3. `python3 tools/deps/frontier.py --target` on each of `ModularCurve.package_of_socket`,
   `ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_socket`,
   `…_of_charZero` → **needed 0** each; and
   `--ds --target ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_charZero` → **needed 0**
   (it was 5 nodes / 2,346 raw before JQ2 + this order).
4. `dedup.py` and `move_dead.py` over the three modules — 0 dead; the `hall`-spelling clusters
   recorded, not forced.
5. `spec/DsHeadConsumer.lean` at 0 errors, and it must fail if either headline is deleted.
6. `tools/check_math_delimiters.py` on this order and any other Markdown touched.

## 6. Recording

`CARRY-FORWARD.md` is **open issues only**. Record in
`topics/functionFieldGeneration/TOPIC-qexp-function-field-c.md` §10.3 (replace the estimate with the
measured written lines — §10.3 already carries the argument and the source measurement) and in §7
below. This order *is* the answer to that topic's §10 Q2, so the answer is written into that
section, not only into a log.

## 7. Result

Landed 2026-10-25. Written **1,012 lines** across three modules against the 465 + ≈122 content
bound (ratio 1.24 written ÷ content). Nothing is `sorry`; no `own:` rows; `Pkg` was imported, not
re-declared.

| part | module | lines | new content | checker |
|---|---|---:|---:|---|
| P1 | `PrimePowerStepAnyField.lean` (1,295 → 1,564) | +269 | 223 | **50 ok** (+5) |
| P2 | `Degree/FinrankAdjoinJqNModC.lean` (new) | 367 | 242 | **15 ok** |
| P3 | `Defs/QExpandCharP.lean` (new) | 125 | 122 | **2 ok** |

P1's nine declarations are the pin's (`Pkg` comes from `Defs/JqCoeff.lean`, and `pkg_of_socket`'s
`hKG1 : … → Pkg K M → …` is the pin's own text, so it diffs as written); P2 ports the twin pair
once and wires all four `Theorems/` wrappers; P3 needed nothing beyond the port's existing
`qExpand_*_TS` API — the two `private` ring-level steps it carries are the pin's own design (its
headlines are stated over `[CommRing K]`, the ported field-level halves are `[Field K]`).

**Gates.** `lake build` green on all three (12 s / 9.9 s, 0 warnings); `check_port --force` reads
50 / 2 / 15 ok with **0 mismatch, 0 missing, 0 own**; tree-wide `--changed` reads **5,482 ok, 0
mismatch, 0 missing, 31 own**, exit 0; `dedup` **0 clusters**, `move_dead` **0 declarations** on each;
`lake env lean spec/DsHeadConsumer.lean` **exit 0**, its new `[socket]` zone applying
`package_of_socket` at `M = 1` and at a general level plus both degree headlines, so deleting any of
them breaks the consumer.

**Frontier.** All five nodes read `needed 0`. The D-S column moves from 1,189 / 448,680 to
**1,184 / 446,334** — exactly the five-node / 2,346-raw socket chain, which takes the parent topic's
cone from 19 nodes / 5,664 raw to 14 / 3,318.

**Residue** (recorded, not fixed — [`logs/cl4-socket-assembly.md`](../../logs/cl4-socket-assembly.md)):
the three spelled-out `hall` sites cannot be restated as `Pkg` because the checker hashes statement
text and never unfolds abbreviations; `Defs/JqCoeff.lean` lists the socket pin file only so that
`Pkg` is accounted for where it is declared; and the pin's two unused `private` specialisations
(`…_sq_eq_of_socket`, `…_sq_mul_prime_eq_of_socket`) are deliberately not ported.

Deviation from the order's dispatch plan, recorded because it produced this log: the port was
started by a worker and finished by the manager, so every reading above was re-taken on the final
tree, by one author, after the worker was stopped.
