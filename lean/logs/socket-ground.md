# Socket ground: `Pkg` homed, the `hall` block deduped, the Frobenius nodes measured

2026-10-25. Ground preparation for
[JQ2](../topics/modularCurve/WORKORDER-JQ2-mffc-mul-prime.md) and
[CL4](../topics/modularCurve/WORKORDER-CL4-socket-assembly.md), done by the manager before either
dispatch. No proof bodies were written; nothing is left `sorry`.

## 1. `Pkg` — the one def the socket needs, landed

`ModularCurve.Pkg` is an `abbrev` at
[`Defs/JqCoeff.lean:253`](../FLTForHuman/ModularCurve/Defs/JqCoeff.lean), statement **verbatim**
the pin's `P2M/Sol/S_ModularCurve_package_of_socket.lean:781`, docstring stating that it is the
`hall` hypothesis of the `C`-layer engines and why it must stay an `abbrev`.

Home rationale. `Pkg` is a property of the level field, and `Defs/JqCoeff.lean` owns
`modularFunctionFieldC`, `jqModC`, `jqNModC`; `dedekindPsi` reaches it transitively through
`Defs/Fields` → `Defs/Polynomial` → `Defs/DedekindPsi`, so no import had to be added and no new
module (and no `unwired_register` row) was needed. It is **not** a `def`: the pin's reducibility is
what lets `pkg_of_socket`'s induction pass `hall`-typed data around and still apply it as the
conjunction it is.

Wiring. `Defs/JqCoeff.lean`'s header gains `spec-pin: P2M/Sol/S_ModularCurve_package_of_socket.lean`
(the file `Pkg` came from). Without it the checker read
`MISSING ModularCurve.Pkg (no match)` — a public port declaration must be accounted for by its
module's wire, and the statement was already identical, so the line was the only thing missing.
With it:

    FLTForHuman/ModularCurve/Defs/JqCoeff.lean  [ok]  20 ok, 0 mismatch, 0 missing, 0 own, 0 kw
      ok      ModularCurve.Pkg  -> P2M/Sol/S_ModularCurve_package_of_socket.lean:781

## 2. The `hall` block: four restatements, and two that must not be touched

`SlotProductAnyField.lean` spelled the block out eight times. The four `private` lemmas whose
hypothesis was a named `hall` (`sv_ne_image_of_dvd`, `isRoot_map_minpoly_sv_of_descent`,
`isRoot_map_minpoly_sv`, `jqNModC_prime_not_mem_adjoin`) now take `(hall : Pkg K M)`: −20 lines,
and one name for one hypothesis.

The two **public** headlines (`minpoly_jqNModC_map_eq_prod_slots`, `jqNModC_prime_not_mem_fullC`)
keep the pin's spelled-out text. Reason, measured not assumed: the checker hashes statement
*text* (`spec/statement_db.py:nhash` over `lean_parser.norm`, which strips comments, drops
`ModularCurve.`/`AlgebraicCurve.` prefixes and erases `kw*`, but **does not unfold abbreviations**),
so `Pkg K M` in a pinned statement would read `MISMATCH`. The same rule is why `Pkg` itself keeps
the pin's name rather than a descriptive one: the pin's `pkg_of_socket` statement mentions `Pkg K M`,
so the constant has to be spelled `Pkg` for that statement to diff.

Left alone, deliberately: `SlotProductAt` (the strong-induction predicate) and `rval_aux`'s
anonymous hypothesis. They are the same block, but they are the recursion's *type*, and CL3 §4.1 is
the recorded precedent for how a statement change there can cost a declaration its heartbeat
budget (the `sv`/`coeffEmb` probe: a 70k-heartbeat declaration timed out at 400k). Not worth it for
text alone — recorded here as residue instead.

## 3. Promotions: none needed, and the one candidate must stay private

The candidate `prod_form_ne_zero` (7 lines, `PhiGenSplitsAnyField.lean`) is `private` **on purpose**:
its public home is `PhiSlotRoots.prod_form_ne_zero`, which states the `ℚ`/`coeffEmb` spelling, so a
public copy of the `C` spelling would collide on the name. JQ2's engine does not need it (its
hypotheses never mention it, and the roots-API lemmas that use it are already public), so the two
orders were corrected rather than the module.

Everything else both orders call is already public and checked:

| declaration | home | kind |
|---|---|---|
| `splits_prime_at_slot_of_isPrimitiveRoot`, `roots_prime_at_slot{,_nodup,_roots_nodup}_of_isPrimitiveRoot`, `isRoot_prime_at_slot_iff_of_isPrimitiveRoot` | `PhiGenSplitsAnyField.lean` | public |
| `minpoly_jqNModC_map_eq_prod_slots`, `jqNModC_prime_not_mem_fullC` | `SlotProductAnyField.lean` | public |
| `fullC`, `eFull`, `divSet`, `qExpandₐK`, `fullC_le_iff`, `fullC_mono`, `jqNModC_mem_fullC`, `eFull_eq_map`, `relfinrank_adjoin_insert`, `relfinrank_fullC_step`, `relfinrank_fullC_mul_prime_pow` | `PrimePowerStepAnyField.lean` | public |
| `dedekindPsi_prime_pow`, `dedekindPsi_mul_of_coprime` | `Defs/DedekindPsi.lean` | public |
| `isIntegral_jqNModC_of_modularPolynomialData` | `X1/IntegralityJqNModC.lean:429` | public |
| `map_jqModC` | `Defs/JqCoeff.lean` | public |
| `mem_range_of_unique_common_root` | `FieldTheory/CommonRoot.lean` | public |

## 4. CL4's P3 priced (it was "not measured")

The two char-`p` Frobenius nodes are much cheaper than their raw lines: both files are largely a
re-statement of already-ported API.

| node | raw | declarations already in the port | new |
|---|---:|---|---:|
| `qExpand_jqModC_eq_pow_unconditional` | 105 | 10 of 14 (`S_:17–83` is the ported `jqModC`/`coeff`/`order` API) | **22** |
| `map_intCast_pow_char_eq_qExpand` | 176 | 4 of 14 (`laurentMap*` is the pin's own prelude; `qExpand_ofPowerSeries_eq_expand`, `pow_char_single_one_eq`, `pow_char_ofPowerSeries_eq`, `intCast_pow_char_eq` are in the port) | **≈100** |

`port_advise` on the first: 10 of 15 statements substitute (4 byte-identical, 6 up to binder
spelling, ≈67 lines). So P3 is ≈122 new raw lines, not 281 — the CL4 table carries the numbers now.

## 5. Gates run

| gate | reading |
|---|---|
| `lake build FLTForHuman.ModularCurve.Defs.JqCoeff` | green, 20 s |
| `lake build FLTForHuman.ModularCurve.FunctionFieldGeneration.SlotProductAnyField` | green, 41 s, 0 warnings |
| `spec/check_port.py --force` on both modules | **22 ok, 0 mismatch, 0 missing, 0 own**, corpus `aa2d8b3` |
| `tools/deps/dedup.py --module '*SlotProductAnyField*' --module '*JqCoeff*'` | **0 clusters**, 111 declarations in 4 modules |
| `tools/deps/move_dead.py --select dead` on both | **0 declarations, 0 lines** each |
| tree build | **not run** (not permitted) — the only downstream module replayed is `PrimePowerStepAnyField`, built on its own |

No `own:` rows were added: `Pkg` diffs `ok` against its pin, and the four restated hypotheses are
`private`, which the checker skips.

## 6. What this buys

- CL4's P1 drops from "declare `Pkg` + nine" to nine declarations, and every statement it writes
  can say `Pkg K M` — including `pkg_of_socket`'s `hKG1 : … → Pkg K M → …`, which is the pin's own
  text and now resolves.
- JQ2 needs no promotion and no new import beyond `SlotProductAnyField` (which brings the whole
  substitution list transitively).
- The remaining unknown in the socket chain is `package_of_socket`'s own 223 lines and the
  transport's 242; both numbers are measured, and the two Frobenius nodes are now ≈122 rather
  than an unmeasured 281.
