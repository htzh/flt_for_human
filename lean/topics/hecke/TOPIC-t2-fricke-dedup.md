# Topic 2: the Fricke dedup

**Status: planned (not started).** Second topic of the Hecke-operator effort, first
of [SET-2](SET-2.md). SET 1 left the Fricke pair as two private namespaces in
`FLTForHuman/ModularForms/HeckeInvariance.lean`: `HeckeFricke` (lines 123–337, 27
decls) and `HeckeFrickeLevelOne` (358–637, 30 decls), transcribed from two FLT
`S_` files that import only the definition module — so the pin shares nothing
between them and the port inherited the double development. This topic removes
it. Statements do not change.

**Audience.** A fresh session taking the first SET-2 topic. Read
[SET-2.md](SET-2.md) §0–§3; [TOPIC-slash-invariance.md](TOPIC-slash-invariance.md)
§1–§2 for what SET 1 built; `base/014` §4 for the mathematics; the current
`FLTForHuman/ModularForms/HeckeInvariance.lean` lines 118–653; and
`Mathlib/NumberTheory/ModularForms/NormTrace.lean` §`ModularForm` for the trace
API. [porting-playbook.md](../../porting-playbook.md) §3 and §7.

**Goal.** Reorganize the Fricke pair so that one trace, one coset argument and one
`U_p ∣ W` computation serve both public theorems, in a dedicated
`FLTForHuman/ModularForms/HeckeFricke.lean`. The two public statements
(`ModularForm.heckeU_add_slash_fricke_eq_zero` and
`ModularForm.exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke`) keep their
names, binders and files' verification status.

## 1. Why this topic, and what is settled

The pair's two halves answer two questions at prime level `p`:

1. `heckeU_add_slash_fricke_eq_zero`: `U_p f + f ∣ W = 0`, i.e. the level-`p` →
   level-one trace vanishes in weight 2. Proved through mathlib's
   `ModularForm.trace` (= 0 by `levelOne_weight_two_rank_zero`) plus a concrete
   coset list.
2. `exists_levelOne_coe_eq_zpow_smul_add_heckeU_slash_fricke`: `p^{k-2} X + U_p(X ∣ W)`
   is a level-one form. Proved by building a trace-level-one form by hand.

The rederivation, item by item (all line numbers are the port's
`HeckeInvariance.lean`):

| rederived in `HeckeFrickeLevelOne` | already exists as |
|---|---|
| `traceFun` (367), `traceForm` (565), `trace_slash_T`/`_S`/`_SL`/`_GL` (430/488/518/533), `trace_holo` (537), `trace_bdd` (547) | **mathlib `ModularForm.trace`** (`NormTrace.lean:82`) with `ModularForm.coe_trace`, which the other half of the same file already uses: `HeckeFricke.main` calls `ModularForm.trace 𝒮ℒ f` at line 256 |
| the 15 generator/arithmetic helpers (`coe_T_pow`, `T_mem`, `S_mul_S_mem`, `eta0`, `eta0_mem`, `S_T_pow_add_p`, `u_add_p`, `v`, `u_slash_T`, `etaS`, `u_mul_S`, `v_slash_S`, `v_zero_slash_S`, `X_slash_S`) | exist only to run the `T`/`S`-generator check for that hand-rolled trace; they fall with it |
| `sum_zmod_val` (414) | `ModularForm.HeckeRepresentatives.sum_range_eq_sum_zmod`, public in the module this file already imports |
| `heckeU_slash_W` (601, general weight `k`) | subsumes `HeckeFricke.heckeU_slash_fricke_eq` (241, weight 2); its inner `hWM` repeats `HeckeFricke.fricke_mul_heckeMatrix` (228) |
| `slash_scalar` (577, weight `k`) and `slash_two_scalar` (143, weight 2, arbitrary unit) | two instances of `f ∣[k] scalar u = (u : ℂ)^(k-2) • f` |
| the coset representative `R j = !![0,-1;1,j]` (125) vs `heckeU_slash_W`'s `S * T^j` (615) | the same matrix; neither half proves it |

**Settled: this is a reorg, not a statement change.** The five public
declarations (`…heckeU/T_slash_eq_self…` stay in `HeckeInvariance.lean`; the two
Fricke ones move to `HeckeFricke.lean`) keep their names and types, so the
checker must stay **682 identical (34 promoted), 0 mismatched** throughout. Any
mismatch is a bug, not a licence to restate.

**Settled: `ModularForm.trace` is the shared trace.** It is a bundled
`ModularForm ℋ k` with `holo'`/`bdd_at_cusps'` already proved and coercion
`∑ q : 𝒬, quotientFunc f q` (`@[simps!]` gives `coe_trace`). The one bridge this
topic must build is from that quotient sum to the explicit `∑ j, u X j` form
`heckeU_slash_W` consumes.

**Settled: keep the two public theorems' proof shape.** The final assembly
(`refine ⟨p^(k-2) • trace, ?_⟩; rw [heckeU_slash_W]; …`) is already minimal and
should survive with `traceForm` replaced by `ModularForm.trace 𝒮ℒ X`.

## 2. The scouted inventory

One new module, both developments:

| piece | port lines now | target |
|---|---|---|
| `HeckeFricke` (123–337) + public theorem (341) | ≈225 | ≈150 — keep `R`, `ι`/`sum_quotientFunc_eq`, `fricke_mul_heckeMatrix`, `heckeU_slash_W`-derived weight-2 |
| `HeckeFrickeLevelOne` (358–637) + public theorem (642) | ≈290 | ≈100 — keep the coercion bridge, `slash_scalar`, the assembly; delete the manual trace |
| the pair | ≈515 | **≈250–300**, below the pin's 531 |

The declarations that must survive, and why:

- **`R` and the coset list.** `R j = !![0,-1;1,j]` and `sum_quotientFunc_eq`
  (`∑ q, quotientFunc f q = f + ∑ j : Fin p, f | R j`) — the latter is the
  concrete form of `ModularForm.coe_trace`, and is exactly the input the deleted
  hand-rolled trace was trying to prove from scratch.
- **`fricke_mul_heckeMatrix`**: `W * heckeMatrix p j = scalar p * R j`. Prove
  `R j = S * T^j` once (a `matrix`/`ext` computation) and this is the only
  `W * heckeMatrix` rewrite in the file.
- **`slash_scalar`** in general form: `f ∣[k] scalar u = (u : ℂ)^(k-2) • f` for
  `u : ℝˣ`. Derive the weight-2 `slash_two_scalar` and the `scalar p` instance
  from it; delete both originals.
- **`heckeU_slash_W`** at general `k`: `U_p (X ∣ W) = p^{k-2} • ∑ j, u X j`. The
  weight-2 `heckeU_slash_fricke_eq` is the `k = 2` instance (`p^{0} = 1`).

The declarations that go: the whole `traceForm`/`traceFun`/`trace_slash_*`/
`trace_holo`/`trace_bdd` group and the 15 generator helpers, `sum_zmod_val`,
`slash_two_scalar`, and whichever of `heckeU_slash_fricke_eq` /
`fricke_mul_heckeMatrix` is not needed after step 3.

Route notes, so none of this is rediscovered:

- Build the bridge as `⇑(ModularForm.trace 𝒮ℒ X) = traceFun X` (or directly as
  the sum form `heckeU_slash_W` needs): `rw [ModularForm.coe_trace,
  sum_quotientFunc_eq]`, then reindex `∑ j : Fin p` to `∑ j ∈ Finset.range p`
  (`Fin.sum_univ_eq_sum_range`) and match `R j` with `S * T^j`. The `Fintype`
  instance in `coe_trace` comes from `Fintype.ofFinite`, so expect a
  `letI`/`haveI : Fintype (𝒮ℒ ⧸ (Γ p).subgroupOf 𝒮ℒ)` wall.
- `ModularForm.trace` needs `(Γ p).IsFiniteRelIndex 𝒮ℒ`; `HeckeFricke.main`
  already instantiates it, so copy that instance block rather than re-derive it.
- Keep `HeckeFricke`'s `main` as the weight-2 vanishing proof
  (`ModularForm.trace 𝒮ℒ f = 0` + `sum_quotientFunc_eq`) — it is already the
  mathlib route; do not re-prove it.
- Move the public theorems with their docstrings into `HeckeFricke.lean`; leave
  `HeckeInvariance.lean` importing it and re-exporting nothing extra.

## 3. What is different about this topic

- **It is the first *pure reorg* of the effort** (the T1 finding was a
  promotion; this is a deletion). Expect no new mathematics except the
  `R j = S * T^j` identification and the coercion bridge.
- **The measurement is the deliverable.** Record pin lines, port lines before
  and after, and the `grep -c` for each deleted group. The point is to show that
  the pair's "does not compress" reading was FLT's duplication, not the
  mathematics.
- **Statements unchanged means the checker is a regression test.** If the count
  moves anywhere except by the new module's declarations, stop.
- **If the trace bridge resists**, fall back to *proving*
  `traceForm X = ModularForm.trace 𝒮ℒ X` (or the coercion equality) and keep the
  old definition only if the proof of the bridge itself is what is hard — but
  record it. Do not silently keep both.

## 4. Budget

**2 goal rounds, checkpoint at 1.** Round 1: `R = S * T^j`, the general
`slash_scalar`, and the `ModularForm.trace` bridge in `Scratch*.lean`. Round 2:
the module move, the deletions, the build/checker. The only real risk is the
`Fintype`/`IsFiniteRelIndex` wall in `coe_trace`.

**Stop early on**: a statement that will not match its wrapper; the trace
bridge needing an instance the port cannot supply; or the reorg turning into a
proof rewrite (that would mean the pair is not as duplicated as scouted — record
it and stop).

## 5. Definition of done

**Reviewed and ticked (2026-09-23), independently re-verified by the reviewer.**
Checker **696 identical (34 promoted), 0 mismatched, 0 missing**; full
`lake build` exit 0 (4042 jobs), 0 warnings, no `sorry`; `#print axioms` clean on
both public theorems. One amendment to the third item below: `coe_T_pow`/
`coe_T_pow'` survive, because `R_eq_S_mul_T_pow` needs them; the *hand-rolled
trace* declarations and the rest of the generator block are gone.

- [x] `FLTForHuman/ModularForms/HeckeFricke.lean` created; the two public
      theorems there, names/types unchanged.
- [x] `HeckeInvariance.lean` no longer contains the Fricke namespaces; it
      imports `HeckeFricke` and keeps the three Γ₀ statements.
- [x] `traceForm`/`traceFun`/`trace_slash_*`/`trace_holo`/`trace_bdd` gone,
      replaced by `ModularForm.trace` + the `coe_trace_eq` bridge; the generator
      block is gone except `coe_T_pow`/`coe_T_pow'` (needed by
      `R_eq_S_mul_T_pow`); `grep -c` counts recorded.
- [x] one `R = S * T^j` lemma; one `fricke_mul_heckeMatrix`; one general
      `heckeU_slash_W`; one general `slash_scalar` (with `slash_two_scalar` now a
      two-line corollary of it); `sum_zmod_val` gone.
- [x] `timeout 300 lake build` green, 0 warnings, no `sorry`.
- [x] checker: **0 mismatched, 0 missing**; `PORT_FILES` gains
      `HeckeFricke.lean`; `SOURCES` unchanged (no new wrappers).
- [x] `#print axioms` on the two public theorems clean.
- [x] `logs/hecke-port.md` §T2: pin/port lines before and after, the deletion
      counts, and whether the `ModularForm.trace` bridge held.
- [x] `README.md` module table row for `HeckeFricke.lean`.

## 6. Reporting back

1. **The compression**, measured: the pair's port lines before/after, and the
   per-declaration `grep -c` for the deleted trace/generator groups.
2. **The bridge**: did `coe_trace` + `sum_quotientFunc_eq` deliver the explicit
   `∑ j, u X j` form, or was a fallback needed?
3. **Whether anything was *not* duplicated** — a piece of `HeckeFrickeLevelOne`
   that had no `ModularForm.trace` counterpart (say which, and why).
4. **The SET-3 hand-off**: what `HeckeFricke.lean` now exposes that the
   `q`-coefficient layer or the bundling can use.
