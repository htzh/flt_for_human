# The `Module.End` and `PowerSeries` leaf families — landed

**Status: landed 2026-10-20.** Two sets, **five modules, zero host edits, zero promotions, zero
marker entries**. Eight graph leaves / **1,724 pin `S_` lines** → **1,980 port lines**, **66
statement-checked declarations**. Checker **3,539 → 3,605 ok / 135 → 140 wired modules**, 0
mismatched / 0 missing / 11 own / 0 kw (corpus `aa2d8b3`). Tier-1 builds
2,311 / 2,065 / 1,448 / 2,069 / 2,042 jobs at 6.5 / 8.3 / 4.9 / 8.1 / 14.1 s, **0 warnings**; all
eight headlines' axioms `[propext, Classical.choice, Quot.sound]`. Orders:
[topics/deligneSerre/WORKORDER-PH3A-module-end-eigenspace.md](../topics/deligneSerre/WORKORDER-PH3A-module-end-eigenspace.md),
[topics/deligneSerre/WORKORDER-PH3B-powerseries-coefficients.md](../topics/deligneSerre/WORKORDER-PH3B-powerseries-coefficients.md);
pricing: [topics/deligneSerre/TOPIC-phase3-small-supplements.md](../topics/deligneSerre/TOPIC-phase3-small-supplements.md).

| module | lines | public | private | checker | build (jobs / s) |
|---|---:|---:|---:|---|---|
| `LinearAlgebra/Eigenspace/Sl2Strings.lean` | 504 | 22 | 1 | 22 ok | 2,311 / 6.5 |
| `LinearAlgebra/Eigenspace/MultiplicityOne.lean` | 622 | 29 | 3 | 29 ok | 2,065 / 8.3 |
| `RingTheory/PowerSeries/Saturation.lean` | 495 | 7 | 1 | 7 ok | 2,042 / 14.1 |
| `RingTheory/PowerSeries/GaloisDescent.lean` | 236 | 6 | 0 | 6 ok | 2,069 / 8.1 |
| `RingTheory/PowerSeries/CoeffMem.lean` | 124 | 2 | 0 | 2 ok | 1,448 / 4.9 |

The two families were the whole of the frontier's `Module.` (4 nodes / 1,028 lines) and
`PowerSeries.` (4 / 696) namespace rows, i.e. the smallest remaining groups of the leaf shelf —
this landed them from **366 → 358 candidates** and took the D-S demand **1,256 → 1,248 nodes /
478,516 → 476,792 raw `S_` lines**, exactly the eight files. The phase-3 note had priced the two
families at 2 + 3 nodes / 522 lines and missed three rows (the 466-line `sl₂`-string node, the
305-line multiplicity-one node and the 431-line saturated-lattice node), which is 1,202 of the
1,724 lines: **recomputing before cutting was the whole of the work's sizing.**

## 1. Why these homes

The homing standard is [topics/TOPIC-mathlib-module-homing.md](../topics/TOPIC-mathlib-module-homing.md)
§3. This set is the case where the two axes coincide and almost nothing had to be decided:

* **All eight statements are about `Module.End` or `PowerSeries`**, and both are mathlib's own
  object namespaces — so the pin's **headline names are kept verbatim** and **no headline was
  renamed**. The checker's statement hashes are therefore the pin's, and the 66 declarations came
  out `0 mismatch / 0 missing` on the first forced run.
* **The paths are the subjects.** `LinearAlgebra/Eigenspace/` is where mathlib files eigenspace
  structure of endomorphisms (every file there declares `namespace Module.End`), and the four
  `Module.End` rows are exactly eigenspace/decomposition statements. `RingTheory/PowerSeries/` is
  mathlib's power-series directory, and all four `PowerSeries` rows are coefficient statements.
  Both are new directories in the port; no existing module was edited.
* **The pin's inner labels went** (homing note §8.1 class A), keeping every last name: `Ws26` and
  `Sl2Strings` → `Module.End.Sl2Strings`; `ALG` → `Module.End.MultiplicityOne`; `DivisorStringWs41`
  → `Module.End.DivisorString`; `M7` → `Module.End.SeparatingProjector`; `SaturationLemma` →
  `PowerSeries.Saturation`; `A2GaloisDescentPS` → `PowerSeries.GaloisDescent`.
* **The `PowerSeries` rows stayed out of `FieldTheory/Galois/` and `RingTheory/Valuation/`.**
  Row 2 is a Galois descent argument (trace form, dual basis, normal closure) and row 1 is
  valuation theory, but both *state* facts about power series, and Galois theory / valuation
  theory are mathlib **libraries** here, not a theory from another area — §3 rule 1's second
  sentence. A user looking for these imports `RingTheory/PowerSeries/`.
* **One homing smell is recorded, not fixed**: `PowerSeries.Saturation.linearIndependent_comp_ringHom`
  (79 lines) is generic linear algebra — a field hom carries `𝔽`-linear independence to
  `k`-linear independence — with no consumer but this development. It stays public at its pin name
  and its pin namespace (visibility and re-homing are separate passes, homing note §8.10), and the
  module header names it as a future `LinearAlgebra/` candidate.

## 2. What each module is

1. **`Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top`** (466 pin lines) —
   complete reducibility for `𝔰𝔩₂` in string form: for `e f h : V →ₗ[ℂ] V` with
   `h∘e - e∘h = 2e`, `h∘f - f∘h = -2f`, `e∘f - f∘e = h` and `⨆ μ, ker(h - μ) = ⊤`, there are
   primitive vectors `t_i` with `e t_i = 0`, `h t_i = n_i t_i`, `f^{n_i+1} t_i = 0`, whose `f`-strings
   `f^p t_i` are independent and span `V`, with the classical weight and lowering formulas. The
   engine is the `𝔰𝔩₂` calculus (`h_e_apply` … `κ`), the eigenbasis, the independence of the
   strings and the span. This is the linear algebra behind the archimedean `su(2)`-string cut.
2. **`Module.End.nonempty_basis_fin_one_and_finrank_iInf_eigenspace_eq_one_of_iSupIndep_of_cyclic`**
   (305) — multiplicity one: a finite-dimensional `W` that is the internal direct sum of cyclic
   `A`-summands is free of rank one over the commutative separating operator algebra `A`, and every
   joint eigenspace has dimension exactly `1`. Three pin blocks (`decomp`/`ψ`/`ψe`/`nonempty_basis`,
   then the `Eig` layer, then the Nakayama/socle layer).
3. **`Module.End.mem_span_prod_apply_and_finrank_iInf_eigenspace_le_one_of_divisorString`** (181) —
   divisor strings: a `D`-divisor-indexed basis on which the prime-indexed `U_q` act by the
   `U_q`-down / `U_q`-base relations makes `V` cyclic over `Algebra.adjoin ℂ {U_q}` generated by
   `e_D`, and every joint eigenspace at most `1`-dimensional.
4. **`Module.End.exists_mem_adjoin_apply_eq_self_and_apply_eq_zero_of_forall_ne_exists_ne`** (76) —
   Lagrange-interpolation projectors: separating scalar actions on a finite family of subspaces
   give, inside `Algebra.adjoin K 𝒯`, an element that is the identity on `W i` and zero on every
   other `W j` — no independence, spanning or finiteness assumed.
5. **`PowerSeries.exists_eq_C_mul_map_of_mem_span_of_saturated`** (431) — reduction of a saturated
   lattice of integral power series: for a valuation subring `A ⊆ L` and a `ℤ`-saturated subgroup
   `N ⊆ ℤ⟦X⟧`, every nonzero `V` in the `L`-span of `N`'s image is `C c · (u.map A.subtype)` with
   `c ≠ 0`, `u ∈ A⟦X⟧`, and the residue of `u` nonzero and back in `N`'s image.
6. **`PowerSeries.exists_map_eq_sum_smul_map_of_forall_map_algEquiv_mem`** (186) — Galois descent for
   power series: if `A ∈ ℚ̄⟦X⟧` has all coefficients in a finite-dimensional `K ⊆ ℚ̄` and every
   `σ`-conjugate of `A` lands in an `E`-subspace `V`, then `A` is a `K`-combination of `ℚ`-rational
   series whose images lie in `V`. Proved through the normal closure, the trace form's dual basis
   and `trace_eq_sum_automorphisms`.
7. **`PowerSeries.coeff_mem_subring_of_coeff_mul_mem`** (41) — dividing by a unit-led power series
   keeps coefficients in a subring.
8. **`PowerSeries.exists_sum_smul_eq_of_forall_coeff_mem`** (38) — coefficient descent: a
   `K₀`-linear combination with all coefficients in `K₀` is a `K₀`-combination with coefficients in
   `K₀`.

The headline namespaces are `Module.End` (rows 1–4) and `PowerSeries` (rows 5–8). `Saturation.main`
and `Sl2Strings.main` are the pin's `solution` wrappers and are **private** (homing note §8.2 F);
the eight `solution` theorems are not ported, each headline carrying the `solution` body.

## 3. The `import Mathlib` replacement (the reusable output)

All four `PowerSeries` pin files say `import Mathlib`, which costs **86 s** to load on this
checkout — more than the edit loop allows, so deriving the targeted lists was the set's main
engineering task. They are 4 / 7 / 15 named imports and load in 5–8 s:

* **`CoeffMem`** (4): `Algebra.Field.Subfield.Basic`, `RingTheory.PowerSeries.Basic`,
  `Algebra.Order.Antidiag.Prod`, `LinearAlgebra.Basis.VectorSpace`.
* **`GaloisDescent`** (7): `RingTheory.PowerSeries.Basic`, `FieldTheory.IsAlgClosed.AlgebraicClosure`,
  `FieldTheory.Galois.GaloisClosure`, `FieldTheory.Normal.Closure`, `RingTheory.Trace.Basic`,
  `LinearAlgebra.BilinearForm.Properties`, `LinearAlgebra.LinearIndependent.Basic`.
* **`Saturation`** (15): `RingTheory.PowerSeries.Basic`, `RingTheory.PowerSeries.NoZeroDivisors`,
  `Algebra.Field.ZMod`, `Algebra.Algebra.Rat`, `RingTheory.Valuation.ValuationSubring`,
  `RingTheory.LocalRing.ResidueField.Defs`, `LinearAlgebra.LinearIndependent.Basic`,
  `LinearAlgebra.Finsupp.LinearCombination`, `Algebra.Module.Torsion.Free`,
  `RingTheory.Localization.Module`, `RingTheory.Artinian.Module`, `LinearAlgebra.FreeModule.PID`,
  `Algebra.CharP.Defs`, `Data.Finset.Max`, `Algebra.Order.GroupWithZero.Basic`.

Two mathlib-version facts came out of this and are worth knowing for the next set:
`Mathlib.FieldTheory.Subfield` does not exist at `v4.34.0` (`Subfield` and `Subfield.smul_def` are
in `Mathlib/Algebra/Field/Subfield/{Defs,Basic}`), and `Mathlib.FieldTheory.NormalClosure` does not
exist either (`IntermediateField.normalClosure`, `AlgEquiv.liftNormal` are in
`Mathlib/FieldTheory/Normal/Closure.lean`; `IsLocalRing.residue` is in
`Mathlib/RingTheory/LocalRing/ResidueField/Defs.lean`).

The four `Module.End` files import mathlib narrowly already; their lists were kept as the pin
wrote them (6 for `Sl2Strings`, the union of the three — 15 — for `MultiplicityOne`), and
`import P2M.Util` was dropped from all eight.

## 4. Drift — forty sites, no proof re-routed

Every statement is the pin's text; the changes are deprecation renames, linter-driven
`haveI`→`have`/`letI`→`let`, and section-variable `omit`s. Nothing was generalised, strengthened or
re-proved.

* **`if`/`dif` deprecations (9)** — `if_pos`/`if_neg`/`dif_pos`/`dif_neg` →
  `ite_eq_left`/`ite_eq_right`/`dite_eq_left`/`dite_eq_right` at `Sl2Strings.lean` 287, 290, 301,
  304, 307, 310, 314 (pin 249–276) and `GaloisDescent.lean` 139, 219 (pin 134, 214).
* **`haveI`/`letI` → `have`/`let` (13)** — `Sl2Strings` 123, 230; `MultiplicityOne` 287, 288,
  290, 291 (the `exists_socle` block); `Saturation` 312, 313, 340, 373, 374; `GaloisDescent` 157, 158. Lean
  `v4.34.0` accepts a plain `have` for a class-valued hypothesis because instance search finds it;
  this is behaviour-preserving here including the load-bearing `have : Fact ℓ.Prime` (verified with
  a throwaway probe, not assumed).
* **`omit` (16)** — `MultiplicityOne`: 13 `[FiniteDimensional K W]` omits on the row-2 theorems and
  3 on row 4's. The pin silenced `linter.unusedSectionVars` file-wide; the port narrows it to
  `omit`, which is stronger (the binder is dropped, not the warning). The cascade is larger than
  the pin's own 4 omits because omitting on `decomp`/`e_w0` frees 9 downstream theorems that used
  the binder only in passing. Checker-safe — `omit` does not change a statement, and the forced
  run is `29 ok / 0 mismatch / 0 missing` (precedent: `Algebra/AddAut/TransvectionFrame.lean`).
* **`coe_finset_sum` → `coe_finsetSum`** (`MultiplicityOne` 151, pin row 2: 86).
* **one unused `simp` argument dropped** (`MultiplicityOne` 244).
* **the pin's `set_option maxHeartbeats 6400000` on row 2 dropped** — it was precaution, as in the
  leaf-families wave; no module needed any override and every edit-loop run passed at 200,000.
* **three unused headline binders** (`hVind`, `hstab`, `hcomm`) are referenced in-proof
  (`have _ := …`) rather than dropped: the headline's statement is the wrapper's and may not lose a
  hypothesis.
* **`p2m_*` scaffolding dropped, zero replacement sites** — row 5's
  `p2m_export "PowerSeries" "coeff_mk mk coeff_smul coe_one coeff_map smul_eq_C_mul ext map_eq_zero
  map C coeff coe_smul"` and its two `p2m_open` lines, and row 6's two `p2m_reactivate` lines. The
  port declares inside `namespace PowerSeries`, so every aliased name resolves unqualified and no
  `rw`/`simp` site had to be requalified — the alias block was pure scaffolding.

## 5. What the landing unblocks

Measured with `frontier.py --target` before and after (nodes / raw `S_` lines of the whole demand):

| successor | before | after |
|---|---:|---:|
| `AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex` | 4 / 2,530 | **3 / 2,064** |
| `ModularCurve.exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC` | 2 / 1,284 | **1 / 853** |
| `ModularCurve.exists_sum_smul_eq_of_qExpansion_coeff_mem` | 2 / 116 | **1 / 78** |
| `ModularCurve.exists_slash_fricke_eq_sum_smul_of_ratCast_qExpansion` | 5 / 2,977 | 4 / 2,791 |
| `ModularForm.qExpansion_slash_coeff_mem_of_peaked_auxiliary` | 6 / 1,617 | 5 / 1,576 |

The first two are the near-ready ones: the `su2Strings` consumer now lacks only three
`AutomorphicForm` nodes, and the **Gauss regular-prolongation row** — the `ModularCurve` row that
consumes the saturated-lattice node — lacks one 853-line node. The other two `regularProlongation`
siblings (the `_residue_mul_eq` and `_residue_div` rows) are reached through the same node.
`CuspForm.nonempty_basis_fin_one_gammaH_and_finrank_eigenspace_eq_one`, the consumer of rows 2–4, is
still 51 nodes out and stays banked.

## 6. Residuals

* **`PowerSeries.Saturation.linearIndependent_comp_ringHom`** is generic linear algebra with one
  consumer (§1). A future `LinearAlgebra/` home, if a second consumer appears.
* **`Saturation.main` and `Sl2Strings.main` are private**, so the checked surface is 15 + 51 rather
  than 16 + 51. That is the expected signal, not a shortfall (homing note §8.4).
* **`MultiplicityOne.lean` is three pin developments in one module** (562 pin lines, 622 port lines):
  correct by subject, but the largest module of the five and the one to split if a consumer ever
  wants only the divisor-string part.
* **`Sl2Strings` is `𝔰𝔩₂` representation theory stated for bare endomorphisms.** mathlib's
  `IsSl2Triple` / `HasPrimitiveVectorWith` (`Mathlib/Algebra/Lie/Sl2.lean`) is the same mathematics
  in the `LieModule` setting and does **not** contain the string-basis assembly; the pin's statement
  was transcribed, not strengthened, and the generalisation stays declined (playbook §4).
