# SET 10 — Γ₀-rationality and the bounded-denominator integrality

**Status: done and reviewed (2026-09-24).** Both orders landed and passed
independent verification (full build 4329 jobs, 0 warnings; checker
1300/70/0/0; consumer exit 0; no caps/`sorry`/bare `import Mathlib`); the review
record is in [SET-11.md](SET-11.md) §0. Sixth coding set of the route-C′ effort,
authorized after the SET-9 review (§0). Two orders. Route plan:
[TOPIC-route-c-prime-integral-structure.md](TOPIC-route-c-prime-integral-structure.md).

| order | module | declarations | pin `S_` lines | closure |
|---|---|---|---|---|
| 1 | `ModularForms/WeightOne/Gamma0Rationality.lean` | `exists_ne_zero_forall_mul_qExpansion_coeff_fricke_mem_adjoin`, `ModularForm.gamma1_qExpansion_coeff_mem_of_frickeRational`, `exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0`, `exists_mvPolynomial_mul_aeval_fricke_eq_of_qExpansion_coeff_mem` | 709+424+1,267+583 | 2/10/17/16 |
| 2 | `ModularForms/WeightOne/Gamma0Integral.lean` | `exists_ne_zero_forall_intCast_mul_qExpansion_coeff_of_gamma_invariant`, `exists_ratCast_qExpansion_slash_of_mem_Gamma0`, `exists_isIntegralQExp_smul_of_ratCast_qExpansion` | 1,362+597+488 | 23/19/25 |

Run in series. All premises are already ported: order 1 needs SET-7's
`weierstrassP_qExpansion_package` and SET-9's `qExpansion_sigmaTransport_package`
/ `levelN_structure_package` / `exists_levelFraction_of_stable_family` /
`exists_monicRel_j_K_…` / `exists_qExpansion_coeff_mem_…`; order 2 needs order 1's
`comp_smul`, plus SET-6's `e1Chi3IsModular`, SET-8's `frickeFunction_modularity_package`,
SET-6's `linearIndependent_complex_of_qExpansion_rational` and the ported
`qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit`. Inside order 2, declare
`exists_ne_zero_forall_intCast_mul_…` before `exists_isIntegralQExp_smul_…`
(the latter cites the former).

**Reserved for the manager (do not start):** `WeightOne/IntegralStructure.lean`
(the trace lemma + `hasIntegralStructure_of_two_le`/`_two`) and SET 11. A helper
belonging to SET 11 becomes a local `private` helper here and is recorded.

## 0. SET-9 review (verified by the manager)

- `LevelFraction.lean` (3,874 lines, 4 headlines, 277 `private`) and
  `LevelN.lean` (3,386 lines, 3 headlines, 251 `private`): green; first compiles
  78.5 s / 80.9 s (close to the 180 s bound, still inside it); cached 3 s.
- Independent re-run: full `timeout 240 lake build` **4327 jobs, exit 0, 0
  warnings**; checker **1292 identical / 70 promoted / 0 mismatched / 0 missing /
  14 own (1306 checked)**; consumer exit 0; 0 bare `import Mathlib`; 0
  `set_option maxHeartbeats`/`maxRecDepth`; 0 `sorry`/`admit`; temp files removed.
- **Structural fix worth carrying:** when concatenating pin files, `end <last
  component>` does **not** close a hierarchical `namespace A.B`; emit
  `end <full.namespace>` (the SET-9 assembler left `WLightS9` open, nesting later
  blocks and producing 51 `duplicate namespace` warnings).
- **`synthInstance` drift:** `IsDedekindDomain ↥(polyJ N) := inferInstance`
  exceeds the default `synthInstance.maxHeartbeats` (20000); use the explicit
  `IsPrincipalIdealRing.isDedekindDomain ↥(polyJ N)`, never a heartbeat option.

## 1. Source of truth and build discipline

Pin `aa2d8b3` at `~/proj/fermats-last-theorem` (read-only); wrapper =
`Theorems/Thm_<dotted>.lean` (the statement authority), proof =
`P2M/Sol/S_<dotted>.lean`. **Copy the pin file's `open`/`open scoped` lines and
its specific imports first** (SET-8's four-minute lesson: a missing `open` produces
error-recovery churn that mimics a blow-up). v4.34 drift list:
[porting-playbook.md](../../porting-playbook.md) §4 plus SET-6/7/8/9.

- **Fixed bounds, never raised/bypassed:** `timeout 60 lake env lean <file>`,
  `timeout 180 lake build <module>`, `timeout 240 lake build`. Never raise
  `maxHeartbeats`/`maxRecDepth`.
- **On a bound-hitting build, diagnose in order:** (1) log for `unknown
  identifier`/parse errors and missing opens; (2) PID-poll the `lean` process for
  CPU/RSS (`/usr/bin/time -v` under-attributes it); (3) only then bisect by
  declaration with a low cap in scratch. A non-return with no errors and high CPU
  is a real blow-up: quarantine and report.
- Likely stall points here: `exists_ne_zero_forall_intCast_mul_…` (the bounded
  denominator engine) and the `mvPolynomial`/`aeval` transfer. State over
  concrete types; per-package helpers `private` in their own namespace.

## 2. Conventions and definition of done

1. Statements verbatim from wrappers, binders included.
2. Specific imports; no `import Mathlib`; copy the pin's opens.
3. Only the headlines public.
4. Checker: append the seven wrappers to `SOURCES` and both modules to
   `PORT_FILES`; target **0 mismatched, 0 missing**.
5. `timeout 180 lake build <module>` green, 0 warnings, no `sorry`/`admit`;
   `#print axioms` clean on the seven headlines; `README.md` two rows; temp files
   removed. No commits; pin/FFG/Sturm/capstone untouched.
6. On a wrapper mismatch, quote both and stop; never weaken.

## 3. Consumer / wire test

Extend `spec/WeightOneConsumer.lean` with the seven `#check`s plus one executed
application per order; `timeout 120 lake env lean spec/WeightOneConsumer.lean`
exits 0 with no warnings (or report why an honest application is impossible).

## 4. Report back

SET-6 §7's seven items, plus any bound hit with the §1 diagnosis order and its
evidence, and confirmation the capstone, FFG, Sturm and the pin are untouched.

## 5. Later sets (manager's view; not authorized)

| set | orders |
|---|---|
| 11 | `Gamma1Basis`: `exists_gamma1_qCoeff_eq_algEquiv_apply`(+`_of_even`), `exists_gamma1_frickeRational_sigmaTransport`, `exists_mul_E4_pow_mul_E6_pow_eq_iff`, `span_frickeRational_E4_pow_E6_pow_eq_top`, `ModularCurve.exists_gamma1_eisenstein_isIntegralQExp_and_slash_eq`, `exists_basis_gamma1_qCoeff_mem_adjoin_exp`(+`_of_even`), `exists_basis_gamma1_qCoeff_mem_range_ratCast`, `exists_basis_gamma1_qCoeff_slash_mem_range_intCast` (≈5,200) |
| capstone (**manager**) | `IntegralStructure` (trace lemma + corollaries) |
