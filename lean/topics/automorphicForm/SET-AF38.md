# SET-AF38 — the `Γ₁` Hecke operators `U_ℓ` and `Diag_d`

**Status: scoped 2026-11-08, two orders in parallel** — §4 is the forecast, §6 the landing record (to be
appended). Read off the D–S shelf with the recipe in
[../deligneSerre/TOPIC-scoping-a-ds-set.md](../deligneSerre/TOPIC-scoping-a-ds-set.md), on the read that
follows SET-AF34/36. It is the **thirty-eighth** set of the column, and the first cut in the
`ModularForms` (Γ₁/nebentypus) layer since SET-S8.

**4 rows / 1,158 silo / 935 net priced** — the pin's own two-operator development, and the highest-leverage
row on the shelf is in it (`exists_degeneracy_gamma1_hasNebentypus`, **9 cone / 12 project** consumers).

| # | row | silo | lev | prem | what it says |
|---|---|---:|---:|---:|---|
| **A** | `CuspForm.exists_gamma1_coe_eq_heckeU_of_dvd` | 241 | 3/4 | 3 | `U_ℓ` maps `Γ₁(N)`-cusp forms to `Γ₁(N)`-cusp forms, `qCoeff (U_ℓ f) n = qCoeff f (ℓn)`, and preserves the nebentypus |
| **B** | `CuspForm.exists_gamma1_div_coe_eq_heckeU_of_dvd_div` | 348 | 1/2 | 3 | for `ℓ² ∣ N`: `U_ℓ f` descends to level `N/ℓ`, with the nebentypus changed along the level map |
| **C** | `CuspForm.exists_degeneracy_gamma1_hasNebentypus` | 218 | **9/12** | 1 | for `M·d ∣ N`: the degeneracy lift `G τ = g (heckeDiagMatrix d • τ)` is a `Γ₁(N)`-cusp form with `qCoeff G n = if d ∣ n then qCoeff g (n/d) else 0` and the level-changed nebentypus |
| **D** | `CuspForm.gamma1_eq_zero_of_prime_not_dvd_of_qCoeff_eq_zero` | 351 | 1/1 | 1 | a `Γ₁(N)`-cusp form whose coefficients vanish at every `n` not divisible by a prime `p ∤ N` is zero |

**One story.** `U_ℓ` and `Diag_d` are the two standard level-changing operators on `Γ₁` cusp forms —
`U_ℓ` lowers (`A`, `B`), `Diag_d` raises (`C`) — and both are read on the `q`-expansion, with the
nebentypus tracked through the level change; `D` is the coefficient criterion that makes the two readings
compatible (a form is determined by its coefficients off the `p`-multiples when `p ∤ N`). The pin puts them
in four files that share the same definition layer (`Def_ModularForm_HeckeOperator`,
`Def_FLTPrelim_Modularity`, `Def_CuspForm_PrimitiveFormGamma1`); `port_advise --with-defs` finds **26 of
those 76 declarations already substituted** and none of the three modules unported.

## 0. The read

The read SET-AF34/36 left (`needed` **753 / 313,678**, `--selfcheck` PASS; the in-flight wave's scaffolds
are priced as landed — FR-0157). The four rows sit on the ready block; `CuspForm` ready is 9 rows.

**Premise audit** (name *and* statement): A and B share `CuspFormClass.isZeroAt_heckeU`,
`ModularForm.mdifferentiable_heckeU`, `ModularFormClass.qCoeff_heckeU`; C's is
`UpperHalfPlane.qCoeff_comp_heckeDiagMatrix_smul`; D's is
`CuspForm.eq_zero_of_slash_heckeDiagMatrix_slash_eq_of_mem_Gamma1` (`ModularForms/Gamma1Vanishing.lean`).
Every last name occurs exactly once in the port. No shadow. **This is the "port once" case the recipe
§2 describes**: A and B are one engine and two statements (the level-lowering row adds the `ℓ² ∣ N`
hypothesis and the level change), and they are one module.

## 1. The cut

| order | module | rows | silo |
|---|---|---|---:|
| **38A** | `ModularForms/HeckeULevel.lean` | A + B | 589 |
| **38B** | `ModularForms/HeckeDiagDegeneracy.lean` | C + D | 569 |

Both are new modules above the existing Γ₁ layer (`Defs/HeckeOperator`, `HeckeQCoeff`,
`HeckeNebentypus`, `Gamma1Vanishing`, `HeckePrelude`), which is where the pin's definitions already live;
`Gamma1Vanishing.lean` holds D's premise and is imported, not touched.

## 2. The price

| figure | value |
|---|---:|
| raw `S_` lines | 1,158 |
| declaration lines | 1,066 |
| — duplicate copies | 40 (A and B's shared three-premise prelude) |
| — boilerplate | 92 |
| distinct declaration groups | 86 |
| already in the port (vetted) | 91 |
| **net new math lines** | **935** |

83 trusted substitutions, 8 suspect: `IsEigenformWith → CuspForm.HasNebentypus` (9) and
`IsPrimitiveForm → CuspForm.HasNebentypus` (5) are **type-only `Prop`-valued `def` matches** — the pin's
own predicates are not the port's `HasNebentypus`; do not substitute them.

**Definition gate: none.** The three pin `Def_` modules are ported
(`Def_CuspForm_PrimitiveFormGamma1` 11/11, `Def_FLTPrelim_Modularity` 15/15,
`Def_ModularForm_HeckeOperator` 46/50; the four unsubstituted names are `heckeU_apply`,
`coeffHeckeT_apply`, `coeffHeckeU_apply`, `coeffHeckeT_eq_coeffHeckeU_add` — definitional `rfl`-lemmas the
port states under its own spelling, so a proof that needs them states them locally as `private` helpers).

## 3. Orders and gates

`lean/tmp/WORKORDER-AF38A-heckeU-level.md`, `…-AF38B-hecke-diag-degeneracy.md`. The standard gates.

## 4. Forecast

| figure | before | after |
|---|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | **749 / 312,520** |
| `needed [literal]` | 765 / 317,143 | **761 / 315,985** |
| frontier F | 1,663 / 813,698 | **1,667 / 814,856** |
| ready rows | 59 / 12,916 | **55 / 11,758** |
| leaves | 200 / 50,557 | 200 / 50,557 |
| `CuspForm` demand | 44 / 13,622 | **40 / 12,464** |

## 5. What this set does not do

- The **Γ₁ sum decomposition** `CuspForm.exists_sum_eq_forall_gamma1_div_slash_eq` (570) — the pin's
  Atkin–Lehner decomposition of a sum of Γ₁ forms — is a different subject and ready but not cut.
- The **Γ₁ operator-algebra tail** (`heckeULinH_comm` 74, `coe_diamondLinH_and_…` 51,
  `exists_basis_gamma1_two_qCoeff_mem_range_intCast` 19, `finiteDimensional_Gamma1` 16).
- The **`HasNebentypus`-Fricke/neben layer** behind `exists_degeneracy_…`'s 12 project consumers.
- No definition layer, no promotion, no migration, no legacy touch, no tree build.

## 6. The landing (2026-11-08)

Two orders, two modules, all gates green.

| order | module | lines | declarations | `check_port` (after the surface gate) | build | axioms |
|---|---|---:|---:|---|---:|---|
| **38A** | `ModularForms/HeckeULevel.lean` | 459 | 36 (2 headlines + 34 helpers, all public) | **34 ok / 0 / 0** | 3,695 jobs, silent | clean, both |
| **38B** | `ModularForms/HeckeDiagDegeneracy.lean` | 625 | 36 (2 headlines + 34 helpers, 3 `own:`) | **33 ok / 3 own / 0 / 0** | 3,715 jobs, silent | clean, both |

**What the set consumed**: 4 rows / 1,158 silo in **1,084 written lines**. Two new imports in 38A
(`HeckeCusps`) and two in 38B (`HeckePrelude`, `ModularCurve.X1.QExpandStretch`), each reported; nothing
else outside the two modules was touched. Consumers `spec/ModularFormsSetAF38AConsumer.lean` (95 lines) and
`…AF38BConsumer.lean` (95) — 0 errors each, both real compositions (the two-level agreement of `U_p` at
`N = p²`; the lift/coefficient-criterion meeting at `d = p`).

### 6.1 The surface gate did the set's real work

Both modules landed with their pin-public helpers `private`, i.e. `check_port` read **2 ok** each — the two
headlines and nothing else. Stripping `private` (the policy the wave settled on after AF38A: *pin-public ⇒
public*, FR-0160) moved them to **34 ok / 0 mismatch / 0 missing** and **33 ok / 0 mismatch / 0 missing /
3 own** — a checked surface of 36 declarations each, with *no proof changed*. The three `own:` rows are the
set's only statement-level exceptions, and each is registered in `spec/decl_markers.tsv`:

| declaration | why it cannot be `ok` |
|---|---|
| `CuspForm.DegeneracyGamma1.diagMatInt` | the pin states it in `Definitions/Def_FreyPackage_ModMCarrier_Rescale.lean:15`, an unported `Def_` module; the statement is that pin's verbatim |
| `CuspForm.DegeneracyGamma1.diagMatInt_map_eq` | same, at `:60` |
| `CuspForm.SupportVanishing.val_transGL_pow` | the pin's `hp : p ≠ 0` binder is unused, and an unused explicit binder cannot be silenced without `set_option` |

### 6.2 Deviations held for review

1. **The two carried `diagMatInt` declarations are the set's one definition-layer gap**:
   `Def_FreyPackage_ModMCarrier_Rescale` is imported by the pin's degeneracy file but is **not** in
   `--with-defs`'s closure (that closure is over statement vocabulary), so the gate read clean while the
   proof needed two of its lemmas. Recorded as FR-0161; the declarations are carried and marked `own:`.
2. **`val_transGL_pow` drops an unused binder** (the only statement-level change in the set, marked).
3. **`det_lowGL` is kept although the pin never uses it** (its own `move_dead` finding): the playbook's
   rule is to port the pin's unreachable mathematics, not to prune it in the same touch.
4. **`exists_cocycle_rescale` inlined**, `rescaleSlash_isZeroAt` folded into `stretchSlash`,
   `heckeDiagMatrix_mul_eq` kept as the pin's conjugation proof (no cross-module duplicate), the pin's
   `haveI` → `have` (the `haveILetI` linter cannot be disabled), and a module-local
   `open scoped UpperHalfPlane Manifold Real` + `Γ₁(·)` notation so the helpers transcribe at the pin's
   spellings.

## 7. The re-read (measured with SET-AF37)

Taken with SET-AF37 in the same wave, with the next wave's scaffolds un-ported (FR-0157):

| figure | before | forecast | **actual** |
|---|---:|---:|---:|
| `needed [F terminal]` | 753 / 313,678 | 749 / 312,520 | **746 / 310,900** (the wave, both sets) |
| `needed [literal]` | 765 / 317,143 | 761 / 315,985 | **758 / 314,365** (the wave) |
| frontier F | 1,663 / 813,698 | 1,667 / 814,856 | **1,670 / 816,476** (the wave) |
| ready rows | 59 / 12,916 | 55 / 11,758 | **54 / 10,425** (the wave) |
| leaves | 200 / 50,557 | 200 / 50,557 | **200 / 50,557** ✓ |
| `CuspForm` demand | 44 / 13,622 | 40 / 12,464 | **40 / 12,464** ✓ |

This set's own delta, from the shelf diff: four rows left the ready block (−1,158) and **two entered** —
`CuspForm.IsPrimitiveForm.qCoeff_eq_zero_of_dvd_div` (**69**) and
`CuspForm.linearIndependent_degeneracy_of_isEigenformWith_of_pairwise_qCoeff_ne` (**218**) — i.e. the
degeneracy lift readied 287 silo of new work, and the second of those is the level-raising statement the
Frey/weight-one layer wants.

The line columns all landed where the forecast put them; the ready cell is the one that moved for a good
reason, which is the fourth set in a row where "readied rows" rather than the port itself changed a
forecast cell.
