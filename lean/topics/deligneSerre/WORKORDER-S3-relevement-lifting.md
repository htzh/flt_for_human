# Work order — S3: the relèvement and the weight-one → weight-two lifting (2 nodes)

**Status: ready to dispatch — phase H2 and S2 are closed and green (checker 2453/0/0).** Method handbook:
`lean/porting-playbook.md` (§2.4, §3.1–§3.5, §4). Mathematics: `math/019` §3.

## 0. Scope

The heart of the batch. `exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` is
the **weight-generic relèvement**: a residual eigenvector of the Hecke algebra on a
finite-dimensional space of cusp forms lifts to a genuine eigenform.
`exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen` is the
weight-one → weight-two instance. 1,918 pin lines.

**Prerequisite:** the H2 reconciliations and S2 (its `CuspForm.HasNebentypus`, the
`Gamma1` Hecke vocabulary, the `_11` refinements), plus the S4 coefficient-ring
interface where the statement is used. Dispatch after S2's review.

**Explicitly not this set:** S4–S8. Home both nodes in a **new top-level
`DeligneSerre/` directory**; the relèvement is weight-generic, so keep it separate
from the weight-one instance.

## 1. The two public targets — statements verbatim

```lean
theorem DeligneSerre.exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr
    (N : ℕ) [NeZero N] (w : ℕ) (ε : DirichletCharacter ℂ N)
    (h : CuspForm (Gamma1 N) w) (hεh : CuspForm.HasNebentypus ε h)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff h n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ)
    (hne : ∃ n : ℕ, φ ⟨ModularFormClass.qCoeff h n, hR n⟩ ≠ 0)
    (α : ℕ → R)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 → ∀ n : ℕ, ∃ r : R,
        (r : ℂ) = ModularFormClass.qCoeff h (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff h (n / p) else 0) ∧
        φ r = φ (α p) * φ ⟨ModularFormClass.qCoeff h n, hR n⟩) :
    ∃ (g : CuspForm (Gamma1 N) w) (b : ℕ → ℂ), g ≠ 0 ∧ CuspForm.HasNebentypus ε g ∧
      (∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff g (p * n) +
            ε (p : ZMod N) * (p : ℂ) ^ (w - 1) *
              (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
          b p * ModularFormClass.qCoeff g n) ∧
      ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ),
        (∀ x : ZMod N, ∃ hx : ε x ∈ R', φ' ⟨ε x, hx⟩ = φ ⟨ε x, hε x⟩) ∧
        ∀ p : ℕ, p.Prime → ¬ p ∣ N → (p : κ) ≠ 0 →
          ∃ hb : b p ∈ R', φ' ⟨b p, hb⟩ = φ (α p)
```

```lean
theorem DeligneSerre.exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen
    (N : ℕ) [NeZero N] (ε : DirichletCharacter ℂ N) (f : CuspForm (Gamma1 N) 1)
    (hf₁ : ModularFormClass.qCoeff f 1 = 1)
    (hT : ∀ p : ℕ, p.Prime → ¬ p ∣ N → ∀ n : ℕ,
        ModularFormClass.qCoeff f (p * n) +
            ε (p : ZMod N) * (if p ∣ n then ModularFormClass.qCoeff f (n / p) else 0) =
          ModularFormClass.qCoeff f p * ModularFormClass.qCoeff f n)
    (R : Subalgebra ℤ ℂ) (hR : ∀ n : ℕ, ModularFormClass.qCoeff f n ∈ R)
    (hε : ∀ x : ZMod N, ε x ∈ R)
    (κ : Type) [Field κ] [Finite κ] (φ : R →+* κ) :
    ∃ (M : ℕ) (_ : NeZero M),
      (∀ p : ℕ, p.Prime → (p ∣ M ↔ p ∣ N ∨ (p : κ) = 0)) ∧
      ∃ (η : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) 2) (b : ℕ → ℂ),
        g ≠ 0 ∧ CuspForm.HasNebentypus η g ∧
        (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
          ModularFormClass.qCoeff g (p * n) +
              η (p : ZMod M) * (p : ℂ) *
                (if p ∣ n then ModularFormClass.qCoeff g (n / p) else 0) =
            b p * ModularFormClass.qCoeff g n) ∧
        ∃ (R' : Subalgebra ℤ ℂ) (φ' : R' →+* κ) (hη : ∀ x : ZMod M, η x ∈ R')
          (hb : ∀ p : ℕ, p.Prime → ¬ p ∣ M → b p ∈ R'),
          ∀ (p : ℕ) (hp : p.Prime) (hpM : ¬ p ∣ M),
            φ' ⟨b p, hb p hp hpM⟩ = φ ⟨ModularFormClass.qCoeff f p, hR p⟩ ∧
            φ' ⟨η (p : ZMod M), hη _⟩ * (p : κ) = φ ⟨ε (p : ZMod N), hε _⟩
```

## 2. Homes and order

| order | node | new module | imports |
|---:|---|---|---|
| 1 | `exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr` (weight-generic relèvement) | `DeligneSerre/Relevement.lean` | S2's `ModularForms/HeckeNebentypus.lean`/`Gamma1Vanishing.lean`; `ModularForms/Defs/PrimitiveFormGamma1.lean`; `ModularForms/HeckeQCoeff.lean`; the H1 `HeckePrelude` |
| 2 | `exists_weightTwo_…_of_weightOne_…` (weight-one instance) | `DeligneSerre/Lifting.lean` | `DeligneSerre/Relevement.lean` |

Both keep the pin's `DeligneSerre.*` namespace. The pin's per-file private preludes
(the `mdifferentiable_heckeU` copy, the `periodic_smul` family) are **not** re-ported:
import them from the H1 `HeckePrelude` / the H2-reconciled names
(`ModularForm.HeckeGamma1.mdifferentiable_heckeU`,
`X1DiamondRational.PeriodOne.periodic_smul`).

`locKer` and `adjoinRoot'` are **absent tree-wide** — H2 verified they are unported
phase-T content, not promotions. `S_DeligneSerre_exists_weightTwo_…` uses `locKer`
(pin line 149), so port it here, at the pin's statement, into `DeligneSerre/Lifting.lean`
(or a small `DeligneSerre/Defs.lean` if both nodes need it), and log the home.
`adjoinRoot'` only if a node actually cites it — grep first.

## 3. Route and risk

- Node 1 is a finite-dimensional linear-algebra/eigenvector argument over a finite
  field plus the Hecke action; `#check` the S2 `HasNebentypus` API and the S4
  lattice/eigenvector lemmas (S4 ports `Module.End.exists_ne_zero_forall_apply_eq_smul_of_ringHom`
  and the rational-coordinate lemmas) before writing.
- Node 2 is the 1,242-line instance: the multiplier (S1), the nebentypus derivation
  (S2), then node 1. If it needs an S1 theorem that is not yet in the port, stop and
  report rather than inline it.
- Keep helpers `private`; record a negative for any mathlib search that finds nothing.

## 4. Verification, build discipline, closing

As `WORKORDER-S1-eisenstein.md` §4: checker wiring appended last; edit loop
`timeout 60 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`;
file-done `flock /tmp/flt_for_human.lock timeout 120 lake build FLTForHuman.DeligneSerre.<Module>`;
no bare whole-tree `lake build`; no `sorry`/`admit`/`axiom`; no `import Mathlib`;
`#print axioms` clean; friction log appended; no writing git commands.

---

## Appendix — pin declaration inventory

#### S3a — pin `P2M/Sol/S_DeligneSerre_exists_hecke_eigen_reduction_eq_of_qCoeff_hecke_congr.lean` (676 lines, 63 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `one_mem_strictPeriods` | theorem | 22 | 4 |  |
| `qCoeffLin` | def | 26 | 13 |  |
| `qCoeffLin_apply` | theorem | 39 | 2 |  |
| `qCoeff_add'` | theorem | 41 | 4 |  |
| `qCoeff_smul'` | theorem | 45 | 4 |  |
| `qCoeff_sub'` | theorem | 49 | 4 |  |
| `qCoeff_zero'` | theorem | 53 | 3 |  |
| `eq_of_forall_qCoeff_eq'` | theorem | 56 | 4 |  |
| `eq_zero_of_weight_zero` | theorem | 60 | 18 |  |
| `denom_eq` | theorem | 78 | 5 |  |
| `denom_ne_zero'` | theorem | 83 | 4 |  |
| `SL_slash_apply'` | theorem | 87 | 7 |  |
| `SL_smul_slash'` | theorem | 94 | 4 |  |
| `hasNebentypus_iff_slash` | theorem | 98 | 21 |  |
| `nebSubmodule` | def | 119 | 16 |  |
| `mem_nebSubmodule` | theorem | 135 | 3 |  |
| `hasNebentypus_heckeTLinOne` | theorem | 138 | 17 |  |
| `heckeTNeb` | def | 155 | 4 |  |
| `coe_heckeTNeb_apply` | theorem | 159 | 6 |  |
| `qCoeff_heckeT_of_hasNebentypus` | theorem | 165 | 11 |  |
| `heckeT_comm_of_hasNebentypus` | theorem | 176 | 37 |  |
| `heckeTNeb_comm` | theorem | 213 | 6 |  |
| `prime_eq_of_cast_eq_zero` | theorem | 219 | 15 |  |
| `red` | def | 234 | 7 |  |
| `red_of_mem` | theorem | 241 | 3 |  |
| `red_coe` | theorem | 244 | 3 |  |
| `red_add` | theorem | 247 | 3 |  |
| `red_sub` | theorem | 250 | 3 |  |
| `red_mul` | theorem | 253 | 3 |  |
| `red_neg` | theorem | 256 | 3 |  |
| `red_zero` | theorem | 259 | 7 |  |
| `qc` | def | 266 | 3 |  |
| `qc_add` | theorem | 269 | 3 |  |
| `qc_sub` | theorem | 272 | 3 |  |
| `qc_smul` | theorem | 275 | 3 |  |
| `qc_zero` | theorem | 278 | 2 |  |
| `qc_neg` | theorem | 280 | 5 |  |
| `qc_heckeTNeb` | theorem | 285 | 10 |  |
| `IsInt` | def | 295 | 6 |  |
| `IsInt.add` | theorem | 301 | 3 |  |
| `IsInt.sub` | theorem | 304 | 3 |  |
| `IsInt.smul` | theorem | 307 | 3 |  |
| `isInt_zero` | theorem | 310 | 4 |  |
| `IsResEigen` | def | 314 | 4 |  |
| `PresInt` | def | 318 | 3 |  |
| `PresNull` | def | 321 | 7 |  |
| `isResEigen_one` | theorem | 328 | 3 |  |
| `isResEigen_zero` | theorem | 331 | 3 |  |
| `IsResEigen.add` | theorem | 334 | 5 |  |
| `IsResEigen.neg` | theorem | 339 | 4 |  |
| `IsResEigen.mul` | theorem | 343 | 16 |  |
| `admissible` | def | 359 | 28 |  |
| `mem_admissible` | theorem | 387 | 4 |  |
| `IsResEigen.unique` | theorem | 391 | 9 |  |
| `resChar` | def | 400 | 20 |  |
| `resChar_eq` | theorem | 420 | 5 |  |
| `isResEigen_smul_one` | theorem | 425 | 4 |  |
| `smul_one_mem_admissible` | theorem | 429 | 6 |  |
| `natCast_pow_mem` | theorem | 435 | 5 |  |
| `presInt_heckeTNeb` | theorem | 440 | 8 |  |
| `presNull_heckeTNeb` | theorem | 448 | 14 |  |
| `exists_eigenvector_lift` | theorem | 462 | 156 |  |
| `solution` | theorem | 618 | 59 |  |

#### S3b — pin `P2M/Sol/S_DeligneSerre_exists_weightTwo_hecke_eigen_reduction_eq_of_weightOne_hecke_eigen.lean` (1242 lines, 62 declarations)

| decl | kind | line | lines to next | private |
|---|---|---:|---:|---|
| `gamma1_le_of_dvd` | theorem | 22 | 12 |  |
| `gamma0_le_of_dvd` | theorem | 34 | 6 |  |
| `gamma1GL_le_of_dvd` | theorem | 40 | 6 |  |
| `restrictMF` | def | 46 | 12 |  |
| `restrictCF` | def | 58 | 12 |  |
| `one_mem_strictPeriods_gamma1` | theorem | 70 | 4 |  |
| `isUnit_entry_of_mem_gamma0` | theorem | 74 | 14 |  |
| `changeLevel_apply_entry` | theorem | 88 | 8 |  |
| `changeLevel_natCast_of_not_dvd'` | theorem | 96 | 8 |  |
| `changeLevel_mem'` | theorem | 104 | 12 |  |
| `hasNebentypus_of_hecke` | theorem | 116 | 33 |  |
| `locKer` | def | 149 | 29 |  |
| `mem_locKer_iff` | theorem | 178 | 3 |  |
| `mem_locKer_of_mem` | theorem | 181 | 5 |  |
| `le_locKer` | theorem | 186 | 2 |  |
| `locKerExt` | def | 188 | 3 |  |
| `map_mul_mk` | theorem | 191 | 5 |  |
| `locKerExt_eq` | theorem | 196 | 23 |  |
| `locKerExt_of_mem` | theorem | 219 | 13 |  |
| `locKerHom` | def | 232 | 50 |  |
| `locKerHom_apply` | theorem | 282 | 2 |  |
| `locKerHom_of_mem` | theorem | 284 | 4 |  |
| `mem_locKer_of_mul_mem` | theorem | 288 | 3 |  |
| `locKerHom_eq_of_mul_mem` | theorem | 291 | 8 |  |
| `exists_natCast_eq_of_pow_eq_self` | theorem | 299 | 65 |  |
| `exists_ringHom_extends_of_pow_eq_one` | theorem | 364 | 105 |  |
| `adjoinRoot'` | def | 469 | 2 |  |
| `le_adjoinRoot'` | theorem | 471 | 3 |  |
| `self_mem_adjoinRoot'` | theorem | 474 | 5 |  |
| `exists_ringHom_adjoinRoot'_extends` | theorem | 479 | 35 |  |
| `isPrimitiveRoot_map_of_isPrimitiveRoot` | theorem | 514 | 38 |  |
| `ubar` | def | 552 | 3 |  |
| `ubar_ne_zero` | theorem | 555 | 9 |  |
| `ubar_mul` | theorem | 564 | 4 |  |
| `ubar_inv` | theorem | 568 | 6 |  |
| `ubar_inv_pow` | theorem | 574 | 9 |  |
| `exists_pow_eq_ubar_inv` | theorem | 583 | 6 |  |
| `teichExp` | def | 589 | 2 |  |
| `teichExp_spec` | theorem | 591 | 4 |  |
| `_root_.IsPrimitiveRoot.pow_eq_pow_iff_modEq'` | theorem | 595 | 10 | yes |
| `pow_eq_pow_iff` | theorem | 605 | 5 |  |
| `zetaUnit` | def | 610 | 4 |  |
| `teichUnitHom` | def | 614 | 16 |  |
| `teich` | def | 630 | 2 |  |
| `teich_apply_unit` | theorem | 632 | 6 |  |
| `teich_mem` | theorem | 638 | 8 |  |
| `map_teich_mul_ubar` | theorem | 646 | 10 |  |
| `map_teich_natCast_mul` | theorem | 656 | 21 |  |
| `pow_half_eq_neg_one` | theorem | 677 | 9 |  |
| `teich_odd` | theorem | 686 | 12 |  |
| `teich_isPrimitive` | theorem | 698 | 18 |  |
| `teichSum_mem` | theorem | 716 | 4 |  |
| `map_sum_eq_neg_one` | theorem | 720 | 62 |  |
| `engine` | theorem | 782 | 228 |  |
| `chi4` | def | 1010 | 2 |  |
| `chi4_apply` | theorem | 1012 | 2 |  |
| `chi4_mem` | theorem | 1014 | 3 |  |
| `chi4_odd` | theorem | 1017 | 8 |  |
| `chi4_isPrimitive` | theorem | 1025 | 32 |  |
| `chi4_sum` | theorem | 1057 | 10 |  |
| `chi4_natCast_of_odd` | theorem | 1067 | 13 |  |
| `solution` | theorem | 1080 | 163 |  |
