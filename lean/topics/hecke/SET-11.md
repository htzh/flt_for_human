# SET 11 — the Γ₁-basis from Galois rationality to the integral-slash basis

**Status: work orders written, not started.** Seventh and **last executor** coding
set of the route-C′ effort, authorized after the SET-10 review (§0). Two orders.
After this set, only the manager's capstone remains. Route plan:
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md).

| order | module | declarations | pin `S_` lines | closure |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/Gamma1Basis.lean` | `exists_mul_E4_pow_mul_E6_pow_eq_iff` (422), `ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq` (333), `exists_gamma1_frickeRational_sigmaTransport` (784), `span_frickeRational_E4_pow_E6_pow_eq_top` (1,390), `exists_gamma1_qCoeff_eq_algEquiv_apply_of_even` (913), `exists_gamma1_qCoeff_eq_algEquiv_apply` (352) | 4,194 | 3–28 |
| 2 | `ModularForms/WeightOne/Gamma1IntegralBasis.lean` | `exists_basis_gamma1_qCoeff_mem_adjoin_exp_of_even` (128), `exists_basis_gamma1_qCoeff_mem_adjoin_exp` (458), `exists_basis_gamma1_qCoeff_mem_range_ratCast` (261), `exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (183) | 1,030 | 31–53 |

Run in series, order 1 first. Every premise is ported (SET-5 `Basic`, SET-6
`EisensteinChiNegThree`/`LevelOneHauptmodul`, SET-7 `WeierstrassPTorsion`, SET-8
`MonicRel`/`FrickeFunction`, SET-9 `LevelFraction`/`LevelN`, SET-10
`Gamma0Rationality`/`Gamma0Integral`) or is in order 1. Inside order 2 the
dependency chain is `adjoin_exp_of_even → adjoin_exp → ratCast → slash_intCast`.

**`CuspForm.exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (order 2, last) is
the capstone's input** — the manager's `WeightOne/IntegralStructure.lean` consumes
exactly it. Do not create the capstone.

## 0. SET-10 review (verified by the manager)

- `Gamma0Rationality.lean` (3,024 lines, 4 headlines + 297 `private`) and
  `Gamma0Integral.lean` (2,529 lines, 3 headlines + public `ModularCurve.IsIntegralQExp`
  + 223 `private`): green, statements verbatim, all helpers `private`.
- Independent re-run: full `timeout 240 lake build` **4329 jobs, exit 0, 0
  warnings**; checker **1300 identical / 70 promoted / 0 mismatched / 0 missing /
  14 own (1314 checked)**; consumer exit 0; 0 bare `import Mathlib`; 0
  `set_option maxHeartbeats`/`maxRecDepth`; 0 `sorry`/`admit`; temp files removed.
- **Accepted integration judgment:** `ModularCurve.IsIntegralQExp` is public
  because an order-2 headline's statement names it; it is transcribed verbatim from
  `Definitions/Def_ModularCurve_X1.lean` (now in `SOURCES`) and the capstone may
  consume it.
- **v4.34 drift to reuse:** `X1DiamondRationalForms.mul_inv_mem_Gamma1`'s Γ₁ matrix
  computation needs `set_option backward.isDefEq.respectTransparency.types false in`;
  `isIntegral_algebraMap_iff` now takes `FaithfulSMul`; `summable_geometric_of_norm_lt_one`
  dropped its `K` argument; `Cyclo` blocks need
  `import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots`.

## 1. Source of truth and build discipline

Pin `aa2d8b3` at `~/proj/fermats-last-theorem` (read-only); wrapper =
`Theorems/Thm_<dotted>.lean` (statement authority), proof = `P2M/Sol/S_<dotted>.lean`.
**Copy the pin file's `open`/`open scoped` lines and its specific imports first**
(SET-8's four-minute lesson). Per-file helpers `private` in their own namespace;
`end <full.namespace>` (SET-9's lesson).

- **Fixed bounds, never raised/bypassed:** `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`; never raise
  `maxHeartbeats`/`maxRecDepth`.
- **On a bound-hitting build, diagnose in order:** (1) log for `unknown
  identifier`/parse errors and missing opens; (2) PID-poll the `lean` process for
  CPU/RSS (`/usr/bin/time -v` under-attributes lake's child); (3) only then bisect
  by declaration with a low cap in scratch. No errors + high CPU = real blow-up:
  quarantine and report.
- Likely stall points: `span_frickeRational_E4_pow_E6_pow_eq_top` and
  `exists_gamma1_qCoeff_eq_algEquiv_apply_of_even` (the heaviest of the set).
  State over concrete types.
- **`synthInstance` drift:** prefer an explicit instance constructor over
  `inferInstance` when the search is heavy; never a heartbeat option.

## 2. Conventions and definition of done

1. Statements verbatim from wrappers, binders included.
2. Specific imports; no bare `import Mathlib`; copy the pin's opens.
3. Only the headlines public.
4. Checker: append the ten wrappers to `SOURCES` and both modules to `PORT_FILES`;
   **0 mismatched, 0 missing**.
5. `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`;
   `#print axioms` clean on all ten headlines; `README.md` two rows; temp files
   removed. No commits; pin/FFG/Sturm/capstone untouched.
6. On a wrapper mismatch, quote both and stop; never weaken.

## 3. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` with the ten `#check`s plus one executed
application per order (order 2's natural target is an application of
`exists_basis_gamma1_qCoeff_slash_mem_range_intCast` at a concrete `N, k`, which
the capstone will reuse). `timeout 120 lake env lean spec/WeightOneConsumer.lean`
exits 0 with no warnings.

## 4. Report back

SET-6 §7's seven items, plus any bound hit with the §1 diagnosis order and its
evidence, and confirmation the capstone, FFG, Sturm and the pin are untouched.

## 5. After this set

Only the capstone remains (manager): `WeightOne/IntegralStructure.lean` — the
trace lemma `CuspForm.hasIntegralStructure_of_basis_gamma1` and the two corollaries
`hasIntegralStructure_of_two_le`/`_two` — consuming order 2's slash basis.
