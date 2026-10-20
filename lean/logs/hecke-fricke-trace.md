# The last `UpperHalfPlane` row — the Fricke conjugate of `U_q`

**Landed 2026-10-20, manager's own one-node set.** The six-family audit had left
`UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU` (156 pin
lines) unported on the phase-3 *shape* test — FLT's Hecke/Fricke layer, not a
mathlib supplement. It was never blocked: its only `Definitions/` gate,
`Def_ModularForm_HeckeOperator`, is homed whole at
`ModularForms/Defs/HeckeOperator.lean` (all 50 pin declarations). The manager's
decision was to take it anyway and clear the namespace.

## 1. Where it is homed, and why

`FLTForHuman/ModularForms/HeckeFrickeTrace.lean` — the port's Hecke/Fricke layer,
next to `ModularForms/HeckeFricke.lean` (the prime-level Fricke pair) and
`ModularForms/HeckeNebentypusFricke.lean` (the nebentypus Fricke action). A new
module rather than an append:

* both neighbouring files are legacy `PORT_FILES` modules, so an append would
  force a handoff (add `spec-pin:`, delete the `PORT_FILES` line) for no
  mathematical gain;
* the node is a distinct general-level identity (`q ∣ N`, the `q` lower-unipotent
  coset representatives `S * T^(j*(N/q)) * S⁻¹`), not the prime-level `U_p ∣ W`
  display of `HeckeFricke.lean`;
* the pin's `ALTraceIdentity` namespace is kept verbatim, and its three public
  `frickeGL` lemmas are declared here as the pin has them — the *private* copies in
  `HeckeNebentypusFricke.lean` live in `CuspForm.FrickeHecke`, a different
  namespace, and are neither imported nor touched.

The consumers are `CuspForm.IsPrimitiveForm.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_dvd`
and its `heckeDiagMatrix` sibling — the Atkin–Lehner trace step of the primitive-form
layer, so this is the right shelf.

## 2. Result

| item | value |
|---|---|
| pin source | `P2M/Sol/S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.lean` (156 lines) + `Theorems/Thm_…` |
| module | 178 lines, 10 declarations (9 pin-public + the headline) |
| build | `flock … lake build FLTForHuman.ModularForms.HeckeFrickeTrace` — 3011 jobs, 4.4 s, 0 warnings |
| checker | **10 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |
| axioms | `[propext, Classical.choice, Quot.sound]` |
| drift | one proof-level name: the pin's `UpperHalfPlane.specialLinearGroup_apply` is `UpperHalfPlane.coe_specialLinearGroup_apply` in `v4.34.0`; no statement changed |

## 3. Effect

* checker **3496 → 3506 ok over 129 → 130 modules**;
* the `UpperHalfPlane` demand row is **gone**; the only remaining row of the
  six-family audit's subjects is `Matrix` 1 / 1,242 (set MG3);
* the D-S demand falls **1,259 → 1,258 nodes / 480,304 → 480,148 raw `S_` lines**.

## 4. Reproduce

```bash
cd lean
lake build FLTForHuman.ModularForms.HeckeFrickeTrace
python3 spec/check_port.py --force FLTForHuman/ModularForms/HeckeFrickeTrace.lean
```
