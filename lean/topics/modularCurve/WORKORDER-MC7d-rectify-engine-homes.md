# WORKORDER-MC7d — rectifying the shared-engine homes (scheduled)

Status: **resolved 2026-10-27** — every item below is either done or decided, none is open.
Owner: the manager.

| item | outcome |
|---|---|
| D1 | **done** — `X1/GaussResidue.lean` is the only copy of the `resF` assembly; `QExpRegularProlongation` (681 → 228) imports it; the four `own:` rows are in `spec/decl_markers.tsv` |
| D2 | **decided as is** — the `Forms`/`FracForm` chain lives in `GaussResidue` (private) because `resHom_mem` needs the pin's fourth `exists_frac_form` conjunct and `exists_resHom_eq` proves the opposite containment; no other module consumes it |
| D3 | **done** — `AutTrace.lean` is wired to the 934 row's `S_` file now that the row is ported: `5 ok / 0 / 0`, and `frontier.py --selfcheck` still PASSes |
| D4 | **decided as is** — `D12top`/`N12top` stay as one-line aliases of `RelrankSol.AF`/`BF` (packaging: the pin's statements name the forms, and the alias carries no proof); the two public `P4`/`P6` spellings (`RelrankSol`, `JOneESRat`) stay, because each is the home of a different pin file's statements and MC-1b/2c import one of them — renaming either would migrate a landed module for no mathematical gain.  `dedup.py --cross` reports no cluster on the pair |
| D5 | **done for the wave** — the measured numbers are in `SET-MC1/2/3` §after-landing and in `TOPIC-ready-shelf.md`; the three row orders' statuses are updated.  The rows' consumer-zone compositions are **decided as is**: the definition wave's zone (`spec/ModularCurveMC7DefConsumer.lean`) is the set's zone and the rows are checker/axioms-gated; the rows' cross-composition belongs to the set that reads their successors (§7's two new ready rows) |

This order exists because of the set's standing rule: **we do not duplicate mathematics.**
Duplication for packaging (a re-export, an `open`, a notation) is fine; a second copy of a proof
is not; and a *facade* — re-declaring a pin-shaped statement whose body delegates to a
differently-spelled port declaration — is not packaging. When the port's engine is stated at a
weaker/different spelling than the pin's text, the port keeps **one** declaration and records the
difference in the wire, it does not grow a second one to match the pin's words.

The set left four pieces of deferred work. Do them in this order.

## D1 — `X1/GaussResidue.lean` is the only copy of the `resF` assembly

MC-7a moves the `resF` block out of `X1/QExpRegularProlongation.lean` (where it is `private`)
into the new shared `ModularCurve/X1/GaussResidue.lean` and makes the old module import it.
Verify, do not re-do:

- `grep -c "private theorem resF\|private def resF\|private theorem resHom_mem" QExpRegularProlongation.lean`
  → 0, and the module builds;
- `GaussResidue.lean` is **unwired** and its header says why (the pin's block spells the engine
  `gaussRing A hT`; the port's is the hT-free spelling of the sibling `S_` file, so a
  `spec-pin:` for the 953 `S_` would read the 953 headline as ported — MD-001's failure mode —
  and for the regular-prolongation `S_` every declaration would `MISMATCH` on the `hT`);
- the 953 row module's four `own:` rows are in `spec/decl_markers.tsv`, keyed
  `(module, full name)`, with the reason "the pin's `hT : ModularGroup.T ∈ Γ` is unused in the
  port's engine; the port states the weaker form": `coe_ne_zero_of_resHom_ne_zero`, `resF_inv`,
  `exists_unit_of_mem_closure`, `mapDomain_placeMap`;
- `python3 spec/check_port.py --force` on both modules: `GaussResidue` is tier 3 (no wire, no
  verdict), the row module `0 mismatch` after the markers.

## D2 — the `Lam`/`homSpan`/`IsFrac`/`exists_frac_form_mem` chain keeps its single copy

It moved into `X1/GaussResidue.lean` with the assembly, because `resHom_mem` needs the pin's fourth
`exists_frac_form` conjunct and only `exists_frac_form_mem` proves it (the public
`QExpDeuring.exists_frac_form` is the sibling file's 3-conjunct spelling; `exists_resHom_eq` proves
the opposite containment). It stays `private` there (engine internals; the pin states the block
public at its `hT` spelling, so promoting it is a separate decision with its own `own:` rows — not
this order). Confirm with `grep -rn "homSpan\|IsFrac"` that the only consumer is `GaussResidue`
and that `QExpRegularProlongation` no longer carries a copy.

## D3 — `AutTrace` gets its wire once 934 has landed

`AlgebraicCurve/Differential/AutTrace.lean` (five declarations, real proofs) is deliberately tier
3 while the 934 row is unported. When MC-7b lands, add

```
spec-pin: P2M/Sol/S_ModularCurve_coeffMap_diffQExp_correspondence_diamondAutBar_eq_qExpansion_diamondLinOne.lean
```

and **only** that line (not the `Thm_` wrapper — the wrapper's headline is MC-7b's, not this
module's). Expected `5 ok / 0 / 0`; the `S_` block's `K`-spelled statements are the module's, so
no `own:` rows. Then confirm `frontier.py --selfcheck` still PASSes and that the 934 row is in
the frontier **only** because MC-7b landed it.

## D4 — the `P4`/`P6` double spelling (the port's own redundancy, pre-dating the set)

The port defines the two Eisenstein power series more than once: public in
`ModularCurve/XH/Relrank.lean` (`P4`, `P6`, used by `isIntegralQExp_E4/_E6`, `AF`/`BF`) and in
`ModularCurve/X1/FunctionField.lean` (`JOneES.JOneESRat.P6` and friends), plus `private` copies in
`ModularForms/WeightOne/{Gamma0Integral,Gamma0Rationality}.lean`. MC-7b/7c import the public one
and copy nothing, but the port still has the duplicate definitions.

`D12top`/`N12top` (the pin's names for `E₄³` and `E₆²` restricted to `⊤`) are the same objects:
`RelrankSol.AF`/`BF`. MC-7b had to alias them because the pin's statements name the forms, so the
port now has two names for one definition. Settle it here: give the objects the pin's names in
their home (`RelrankSol` or wherever the pair belongs) and have the alias deleted, **or** keep the
alias with a one-line comment and record it — the pair must not grow a third name.

Measure first: `python3 ../../tools/deps/dedup.py --cross --min-cost 0 --tier body` and
`port_graph.py --duplicates` on `P4`/`P6`. Then keep the home whose subject is the pair
(`XH/Relrank.lean` is the "relrank solution" module, `X1/FunctionField.lean` the `jqModC` module:
the pair belongs to the E₄/E₆ integrality subject, so `XH/Relrank.lean` unless the audit says
otherwise), make the others import it, and delete the private copies. Build the two
`ModularForms/WeightOne` modules and `X1/FunctionField.lean` after the edit; no tree build.
If the audit shows the two public copies are *not* the same statement (different coefficients),
stop and report — that would be a real mathematical difference, not redundancy.

## D5 — close the set's records

- `SET-MC7.md` §7's measured numbers: re-run the read after all three rows land
  (`frontier.py --ds --ready --include-leaves …`, `--selfcheck`), report what the set consumed,
  the new `needed`, and **which rows became ready because of it** (recipe §7);
- the three row modules' `WORKORDER-MC7a/b/c` status lines → landed, with their checker/axioms
  numbers;
- the set's consumer zone (`spec/ModularCurveMC7DefConsumer.lean`) gains the three rows' zones:
  the 953 `gaussReduction` composed with `ConstantReduction.pic0Map_mk`/`ord_algebraMap`, the 868
  coefficient identity at `ℓ`, and the 934 correspondence at `d = 1`; the error count is the
  deliverable metric;
- append the frictions found while landing to `lean/logs/frictions.md`.

## Gates for this order

Every module touched: its own silent build under `flock`/`timeout`, `check_port --force` with
`0 mismatch / 0 missing` (or the recorded `own:` rows), zero warnings, no `set_option
maxHeartbeats`, and a `dedup.py` reading that is **lower** than before the order (that is the
point of it). No tree build; no `git` writes.
