# CL4 landing log: the socket assembly and its transport

2026-10-25. Port of `ModularCurve.package_of_socket` and
`ModularCurve.finrank_adjoin_jqNModC_eq_dedekindPsi_of_(socket|charZero)` (one development, two
wrappers), plus the two char-`p` Frobenius premises. Order:
[WORKORDER-CL4](../topics/modularCurve/WORKORDER-CL4-socket-assembly.md). Ground:
[logs/socket-ground.md](socket-ground.md).

The port was started by a worker agent and finished by the manager after the worker was stopped;
every reading below was re-taken by the manager on the final tree, so the log has one author. No
`sorry`; no `own:` rows; nothing outside the order's scope was edited.

## The three modules

| part | module | lines | declarations added | checker |
|---|---|---:|---|---|
| P1 | `FunctionFieldGeneration/PrimePowerStepAnyField.lean` (append) | 1,295 → **1,564** (+269) | 9: `mffC_congr`, `fullC_congr'`, `adjoin_jqModC_le_fullC`, `fullC_one` (`private`); `tight_iff_relfinrank_fullC`, `mffC_eq_fullC_of_steps`, `relfinrank_fullC_prime_pow_tower`, `pkg_of_socket`, `package_of_socket` | **50 ok** (was 45, +5) |
| P2 | `Degree/FinrankAdjoinJqNModC.lean` (new) | **367** | 14 + the two headlines: `PoleOrder` (`coeff_algebraMap_mul` `private`, `coeff_aeval_jqModC_neg_natDegree`, `aeval_jqNModC_phiAtSeed_jA`), `Transport` (`coeffMap_algebraMap_eq`, `coeffMap_jqModC_eq`, `coeffMap_jqNModC_eq`, `coeffMap_aeval_jqModC_eq`, `exists_map_eq_of_aeval_eq_coeffMap`, `jqNModC_not_mem_adjoin_of_not_mem_adjoin`, `coeffMap_mem_adjoin`, `tauAdjoin`, `tauAdjoin_jA`, `finrank_adjoin_jqNModC_eq_of_map`), `natCast_ne_zero_of_socket`, `jqNModC_prime_not_mem_adjoin_of_ringHom` (`private`), the two headlines | **15 ok** |
| P3 | `Defs/QExpandCharP.lean` (new) | **125** | `map_intCast_pow_char_eq_qExpand`, `qExpand_jqModC_eq_pow_unconditional` (+ two `private` ring-level steps) | **2 ok** |

Written 1,012 lines against 818 net new content (231 JQ2 + 223 + 242 + 122), a written ÷ content
ratio of 1.24 — inside the playbook's 1.1–1.3.

`Pkg` was **not** re-declared: P1 imports `ModularCurve.Pkg` (`Defs/JqCoeff.lean:253`), and
`pkg_of_socket`'s `hKG1 : … → Pkg K M → …` is the pin's own statement text, so it diffs as written.
The four `private` helpers of P1 use the pin's names; the four `private` ones of P2 are the pin's
`private` helpers too (`coeff_algebraMap_mul`, `jqNModC_prime_not_mem_adjoin_of_ringHom`), which is
why no `own:` row was needed.

Left out deliberately: the pin's `private` `finrank_adjoin_jqNModC_sq_eq_of_socket` and
`…_sq_mul_prime_eq_of_socket` (unused convenience specialisations of the headline — `move_dead`
would have flagged them).

## The socket is the assembly, not a route — confirmed in the tree

`pkg_of_socket` consumes the prime step as `hKG1`; the P1 wrapper fills it from JQ2's
`jqNModC_mem_modularFunctionFieldC_mul_prime` (imported from `MffCMulPrime`), and nothing in the
module re-proves the level bookkeeping it already had. The port's numbers landed where the order
predicted: 223 new lines for the 1,003-line pin file, 242 for the 518-line one.

## Gates

| gate | reading |
|---|---|
| `lake build` P1 / P3 / P2 | green — 12 s / instant / 9.9 s, **0 warnings** |
| `spec/check_port.py --force` on the three modules | **50 / 2 / 15 ok, 0 mismatch, 0 missing, 0 own**, corpus `aa2d8b3` |
| tree-wide `spec/check_port.py --changed` | **5,482 ok, 0 mismatch, 0 missing, 31 own, 0 kw — 247 modules, exit 0** |
| `tools/deps/dedup.py` over the four modules | **0 clusters**, 96 declarations |
| `tools/deps/move_dead.py` on the three | **0 declarations, 0 lines** each |
| `lake env lean spec/DsHeadConsumer.lean` | **exit 0** — the new `[socket]` zone applies `package_of_socket` at `M = 1` and at a general level, and both degree headlines |
| `frontier --target` on the five nodes | **needed 0** each |
| `frontier --ds` | **1,184 nodes / 446,334 raw**, from 1,189 / 448,680 — the five-node socket chain, exactly −2,346 |

The consumer zone is the use test: each of its four `example`s *is* one of the landings applied, so
deleting a headline (or the module) stops the file elaborating — nothing else in the file mentions
these names.

## Residue, recorded not fixed

1. **The `hall` block now has three spelled-out sites** (`SlotProductAnyField` ×2 public, pinned;
   `MffCMulPrime` ×1 public, pinned) plus `Pkg`. The pinned ones cannot be restated: the checker
   hashes statement text and does not unfold abbreviations. That is the whole reason `Pkg` exists
   as an `abbrev` with the pin's name.
2. **`Defs/JqCoeff.lean` now lists the socket pin file** (`spec-pin: P2M/Sol/S_…_package_of_socket.lean`)
   only so that `Pkg` is accounted for by the module that declares it; that pin file's other
   declarations are checked where they land (P1, P2), not there.
3. **P3's two `private` ring-level steps** are four-line repetitions of the field-level lemmas in
   `Frobenius/Defs.lean`; the pin states its headlines over `[CommRing K]` and those are field-only,
   so the repetition is the pin's own design, not port debt.
