# S-4 work order — the `E₄³ − E₆²` / `jLattice` modular-polynomial tail

**Status: drafted 2026-10-07, depends on S-3; dispatch after S-3 lands.** The coset form cites
S-3's headline, and the coset form itself cites the `Matrix.SpecialLinearGroup` diagonalisation
leaf, so this order folds that leaf in (a blueprint correction recorded in
[TOPIC-V5-row-S-scoping.md](TOPIC-V5-row-S-scoping.md) §4). Fourth set of row S; reconnaissance
is §2.3 and §4 there, re-measured here. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port
mathlib `v4.34.0`. Depends on landed sets: S-1/S-2/S-3, the `ModularForm`/`ModularCurve`
layers (`ModularForms/*`, `ModularCurve/ModularPolynomial*.lean`), and
`ModularCurve/Defs/PrimCosetReps.lean`. Method:
[../../porting-playbook.md](../../porting-playbook.md) §2.1–§2.4, §3.1–§3.5, §4–§5.

## 1. Scope

Land the row's **modular-polynomial tail**, the three `ModularCurve.ModularPolynomialData`
Nodes

* `eval_E4_cube_div_discriminant_smul_eq_zero` (367 pin lines) — for `σ' = N·σ`,
  `Φ` evaluated at `E₄(σ)³/Δ(σ)` evaluated at `E₄(σ')³/Δ(σ')` is `0`;
* `eval_E4_cube_div_discriminant_coset_eq_zero` (85) — the same at a primitive-coset pair
  `(a, b, d) ∈ primCosetReps N` with `τ' = (aτ + b)/d`;
* `eval_jLattice_eq_zero_of_isAddCyclic` (25) — the same for a `PeriodPair` pair
  `L, L'` with S-3's hypotheses, via `jLattice_ofTau`;

plus the leaf `Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one`
(88 lines), which the coset form consumes:

> `{N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (hgcd : Nat.gcd a (Nat.gcd b d) = 1) :
> ∃ γ₁ γ₂ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
>   !![(a : ℤ), b; 0, d] = (γ₁ : Matrix (Fin 2) (Fin 2) ℤ) * !![(N : ℤ), 0; 0, 1] * (γ₂ : ...)`

The three nodes are one proof at three levels of generality: the smul form is the `E₄³/Δ`
q-expansion computation over `heckeDiagMatrix N`; the coset form reduces the primitive coset
to the smul form through `upperTriangularGL = γ₁ · heckeDiagMatrix N · γ₂`; the `jLattice` form
feeds S-3's `(a, b, d, τ, σ)` into the coset form. This is the last mathematical set before the
capstone, and it is where the row meets the *modular-forms* layer rather than the `PeriodPair`
layer.

**Not this set:** the capstone SC (manager's), and the three SC-only leaves
(`Field.nonempty_ringHom_complex_of_countable`, `PeriodPair.exists_variableChange_smul_weierstrassCurve_eq`,
`IsAddCyclic.of_squarefree_natCard`). The SL₂ leaf **is** this set's (see above).

## 2. Source and the dedup

Four pin files and their statement authorities (spell the binders **exactly**; all four have a
`Theorems/Thm_*.lean` wrapper):

| pin `S_` file | lines | wrapper statement (abbreviated) |
|---|---:|---|
| `S_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_smul_eq_zero.lean` | 367 | `(N) [NeZero N] (data : ModularPolynomialData N) (σ σ' : ℍ) (hσ' : (σ' : ℂ) = N * σ) : (data.Φ.map (eval₂RingHom (Int.castRingHom ℂ) (E₄ σ ^ 3 / Δ σ))).eval (E₄ σ' ^ 3 / Δ σ') = 0` |
| `S_..._coset_eq_zero.lean` | 85 | `(N) [NeZero N] (data) {a b d : ℕ} (habd : (a,b,d) ∈ ModularCurve.primCosetReps N) (τ τ' : ℍ) (hτ' : (τ' : ℂ) = (a * τ + b) / d) : … = 0` |
| `S_..._eval_jLattice_eq_zero_of_isAddCyclic.lean` | 25 | `(N) [NeZero N] (data) (L L' : PeriodPair) (hsub) (hidx) (hcyc) : (data.Φ.map (eval₂RingHom (Int.castRingHom ℂ) L.jLattice)).eval L'.jLattice = 0` |
| `S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one.lean` | 88 | quoted in §1 |

Pin citations: File A imports `Thm_ModularCurve_jqModC_eq_qExpansion_E4_cube_div_discriminant`,
`Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne`,
`Thm_ModularForm_exists_degeneracy_Gamma0` — all **ported**
(`ModularCurve/JqIntegralRatios.lean`, `ModularForms/HeckeQCoeff.lean`,
`ModularForms/Level/Degeneracy.lean`). File B imports File A **and the SL₂ leaf**. File C
imports S-3's wrapper, `Thm_PeriodPair_jLattice_ofTau`, and File B.

`port_advise` on the four files: **2 substitutions ≈ 5 lines** (only `e4cubeSL`/`deltaSL`
matched, and only through the tool's `def`-level blind spot against
`ModularForms/DiscPow.lean`'s `eCubeSubESq`). **The tool's figure is not the reuse figure
here**: the port's `eCubeSubESq` (`DiscPow.lean`) and the `E₄`/`Δ` layer
(`ModularForms/JInvariant.lean`) are statement-counterparts of the pin's `e4cubeSL`/`deltaSL`
under different names and spellings, and the heavy inputs (`ModularForm.exists_degeneracy_Gamma0`,
`heckeDiagMatrix`, `coe_heckeDiagMatrix_smul`, `ModularCurve.primCosetReps`/`mem_primCosetReps`,
`upperTriangularGL`/`val_upperTriangularGL`, `val_heckeDiagMatrix`, `ModularForm.E₄`,
`ModularForm.discriminant`, `jqModC_eq_qExpansion_E4_cube_div_discriminant`) are all in the
port. **Audit the two forms and the q-expansion helpers by statement before pricing**; the
scoping note's net estimate is ≈360 lines.

Regions, with dispositions:

| file | lines | contents | disposition |
|---|---|---|---|
| A | `:24–61` | `gamma0_one_eq_top`, `gamma0_one_coe`, `heckeDiagMatrix_one`, `one_mem_sp`, `e4cubeSL`/`coe_e4cubeSL`, `deltaSL`/`coe_deltaSL`, `e4cube1`/`delta1`/`coe_*` | **new** — the `𝒮ℒ`-level `E₄³`/`Δ` forms (audit against `eCubeSubESq`/`JInvariant`) |
| A | `:63–167` | `An` and `An.{mul,add,smul}`, `an_of_modularForm`, `qExpansion_finset_prod`, `qExpansion_finset_sum_smul`, `pow_mul_div_pow`, `fam`, `card_univ_mul`, `mono`, `prod_ite_pow`, `coe_mono`, `coeAddHom` | **new** — the pin's q-expansion bookkeeping (absent from the port by name) |
| A | `:168` | `solution` | the smul headline, ~90 lines |
| B | `:23–58` | `jt`, `sl_mem`, `jt_smul`, `upperTriangularGL_eq`, `coe_upperTriangularGL_smul` | **new** |
| B | `:59` | `solution` | the coset headline, ~28 lines |
| C | `:16` | `solution` | the `jLattice` headline, ~9 lines |
| leaf | `:12–83` | `exists_coprime_mul_add`, `main`, `solution` | **new** (mathlib-only) |

The `*_axiomAnchor` stubs and `p2m_*` scaffolding are not landed; the pin's
`attribute [-instance]`/`[-simp]` and heartbeat bumps are not transcribed.

## 3. The mathematics, and the direction of the chain

1. **The leaf** (`Matrix.SpecialLinearGroup.PrimitiveSmith`): `exists_coprime_mul_add` picks
   `p` with `Coprime (a*p + b) d` from `gcd a (gcd b d) = 1` (a `primeFactors` product
   argument); `main` turns `IsCoprime (a*p+b) d` into two explicit `SL₂(ℤ)` matrices whose
   product sandwiches `!![a, b; 0, d]`; `solution` is `main`. Mathlib supplies `IsCoprime`,
   `Nat.Coprime`, `Matrix.SpecialLinearGroup`; the construction is the pin's.
2. **The smul form**: `σ' = heckeDiagMatrix N • σ`; `exists_degeneracy_Gamma0` gives four
   level-one forms `e, δ, eN, δN` with `⇑e = E₄³`, `⇑δ = Δ`, `⇑eN = e4cubeSL ∘ heckeDiagMatrix N`,
   `⇑δN = deltaSL ∘ heckeDiagMatrix N`; `Φ` is a modular polynomial, so
   `Φ(E₄(σ)³/Δ(σ), E₄(σ')³/Δ(σ')) = 0` follows from the `q`-expansion of `jqModC = E₄³/Δ`
   (`jqModC_eq_qExpansion_E4_cube_div_discriminant`) and the pin's `qExpansion_*`/`mono`/`fam`
   bookkeeping.
3. **The coset form**: `habd` gives `a*d = N` and `gcd a (gcd b d) = 1`; the leaf gives
   `γ₁, γ₂` with `!![a,b;0,d] = γ₁ · !![N,0;0,1] · γ₂`; `upperTriangularGL_eq` turns that into
   `upperTriangularGL a b d = γ₁ · heckeDiagMatrix N · γ₂`; `coe_upperTriangularGL_smul` gives
   `τ' = upperTriangularGL • τ`; `jt_smul` + the smul form close it.
4. **The `jLattice` form**: S-3's headline gives `(a, b, d, τ, σ)`; rewrite both `jLattice`s
   by `PeriodPair.jLattice_ofTau` and apply the coset form.

## 4. Deliverable — two modules

**(a) `FLTForHuman/Algebra/SpecialLinearGroupSmith.lean`** (new; mathlib-only, leaf): the SL₂
diagonalisation at namespace `Matrix.SpecialLinearGroup.PrimitiveSmith` (the pin's namespace;
the checker matches by last name, so this is a free choice — keep the pin's). Declarations at
the pin names `exists_coprime_mul_add`, `main`, and the headline.

**(b) `FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean`** (new leaf; a sibling of
`ModularPolynomial{Assembly,Irreducible,Properties,Uniqueness}.lean`), in namespace
`ModularCurve.ModularPolynomialData` (the scoping note §4's home). The three headlines, the
`E₄³`/`Δ` forms, the q-expansion bookkeeping, `jt`/`upperTriangularGL_eq`/
`coe_upperTriangularGL_smul`, and the three `solution`s. Public at pin names; helpers local to
the module `private` with content names. Imports: `ModularCurve/ModularPolynomial*`,
`ModularCurve/Defs/PrimCosetReps`, `ModularCurve/JqIntegralRatios`,
`ModularForms/{JInvariant,DiscPow,HeckeQExpansion,HeckeQCoeff,Level/Degeneracy,Gamma1Vanishing,Defs/HeckeOperator}`,
`Algebra/SpecialLinearGroupSmith`, `Elliptic/PeriodPair/{PrimCosetReps,Lattice,JLine}` (S-3/S-1),
plus mathlib `Mathlib.NumberTheory.ModularForms.*` as needed. Never `import Mathlib`; never
`GenusOnePlaceGateCentred.lean`/`Place/RRSpace.lean`.

**Audit before writing**: the port's `eCubeSubESq` (`DiscPow.lean`) and the `E₄`/`Δ` layer
(`JInvariant.lean`) against the pin's `e4cubeSL`/`deltaSL`/`e4cube1`/`delta1`, and the pin's
`qExpansion_finset_prod`/`qExpansion_finset_sum_smul`/`pow_mul_div_pow`/`coeAddHom`/`mono`
against anything the port's q-expansion layer already proves under another name. Import or
generalise where the statement matches; do not re-prove. Record every audit with `grep -c`.

## 5. Route, with recorded negatives

- **The leaf is mathlib-foundational, pin-constructed.** `IsCoprime`, `Nat.Coprime`,
  `Nat.Coprime.isCoprime`, `Matrix.SpecialLinearGroup`, `Matrix.det_fin_two` exist; there is no
  mathlib "Smith normal form for `SL₂(ℤ)`", so `exists_coprime_mul_add`/`main` are written.
- **The modular-polynomial step is a q-expansion computation over the ported layer**; the
  heavy inputs are ported (§2). The pin's generic bookkeeping names are absent, so expect to
  write ~150 lines of `qExpansion`/`mono`/`fam` API — the set's cost. If a ported lemma already
  gives one under another name, use it.
- **Reuse wins.** `PeriodPair.jLattice_ofTau` (`JLine.lean`), `ModularCurve.primCosetReps`/
  `mem_primCosetReps` (`ModularCurve/Defs/PrimCosetReps.lean`), `ModularForm.exists_degeneracy_Gamma0`,
  `heckeDiagMatrix`/`coe_heckeDiagMatrix_smul`, `upperTriangularGL`/`val_upperTriangularGL`,
  `jqModC_eq_qExpansion_E4_cube_div_discriminant` are all in the port. S-3's headline is the
  `jLattice` form's premise.
- **Heartbeats / traps**: the pin's bumps are not transcribed; never raise the cap. Prose in
  `/- … -/` blocks (playbook §4); do not open `Polynomial.Bivariate` file-wide (playbook §6).

## 6. Stop conditions

Stop and report, do not push on: an unported prerequisite outside §2; a statement that does not
transcribe to `v4.34.0`; a declaration that will not fit the 4,000,000 cap; any pull toward the
SC-only leaves or the capstone; any pressure to import the two forbidden modules.

## 7. Build discipline (binding) and pre-flight

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`; `lake build <module>`
> when done; **one** `lake build` per wave; `timeout` + `flock .lake/flt_build.lock`; time it;
> **never raise `maxHeartbeats`**. Iterate in a gitignored `lean/Scratch*.lean`, leaf module
> first (it is fast and independent).

**Pre-flight** (report the numbers):

1. `timeout 300 lake env lean <opts>` on the leaf module and on a stub importing the
   `ModularPolynomial*` + `ModularForm` cone, timed (the `E₄`/`Δ`/`heckeDiagMatrix` cone is
   the expensive one).
2. `#check @Matrix.SpecialLinearGroup.exists_eq_mul_diagonal_mul_of_gcd_eq_one` is not
   available until you write it; `#check` the mathlib primitives (`IsCoprime`, `Nat.Coprime`,
   `Matrix.SpecialLinearGroup.det`, `Matrix.det_fin_two`), `ModularForm.exists_degeneracy_Gamma0`,
   `ModularForm.coe_heckeDiagMatrix_smul`, `ModularCurve.jqModC_eq_qExpansion_E4_cube_div_discriminant`,
   `ModularCurve.mem_primCosetReps`, `PeriodPair.jLattice_ofTau`, and S-3's headline.
3. `port_advise --targets build/rowS4_targets.txt` against the landed tree; report the
   substitution figure and the by-statement audit of the `E₄³`/`Δ` forms and the q-expansion
   helpers.

## 8. Verification

- `lake env lean` clean; `lake build` both modules; one `flock`ed wave; whole-tree `lake build`
  green.
- `python3 spec/check_flt_statements.py` → **0 mismatched / 0 missing**. **Re-run it at
  dispatch** (S-2/S-3 will have moved the baseline off `6074 (313,83) / 0 / 0 / 36 own (6110)`).
  Reconcile every delta.
- `SOURCES`: append, wrapper before its `S_` file, the four pairs
  (`Thm/S_Matrix_SpecialLinearGroup_exists_eq_mul_diagonal_mul_of_gcd_eq_one`,
  `Thm/S_…smul_eq_zero`, `Thm/S_…coset_eq_zero`, `Thm/S_…eval_jLattice_eq_zero_of_isAddCyclic`);
  none is in the list today. `PORT_FILES`: append `FLTForHuman/Algebra/SpecialLinearGroupSmith.lean`
  then `FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean` (last). Report before/after.
- `spec/ModularPolynomialE4CubeConsumer.lean` (new, `spec/` only): real executed zones, no
  `#check`, no `sorry`; deleting the modules must make it fail; exit 0. ≥1 zone applies the
  leaf at concrete `a, b, d`; ≥1 applies the smul form at a concrete level-one form; ≥1 runs
  S-3's headline into the `jLattice` form. Run `timeout 90 lake env lean <opts>`; report exit
  and wall time; do not add it to the lakefile.
- `#print axioms` on the four headlines and `main`: `[propext, Classical.choice, Quot.sound]`;
  no `sorry`.
- `build_ladder.py --edit` on both modules; report the cascade (the `ModularPolynomialE4Cube`
  dependents are the SC capstone's business).

## 9. Close-out (fill on landing)

Written lines per module; the by-statement audit of the `E₄³`/`Δ` forms and the q-expansion
helpers (with `grep -c`); checker before → after and the reconciliation; the measured saving
against the 477 raw pin lines of A+B+C (+88 for the leaf) and what was actually written;
consumer exit and time; whole-tree build jobs and seconds; `#print axioms`; the friction
findings — in particular how much of the pin's q-expansion bookkeeping the port already had
under another name and whether the `E₄³`/`Δ` forms collapse onto `eCubeSubESq`/`JInvariant`.
Then update `TOPIC-V5-row-S-scoping.md` §2.3/§5 and fold the generalizable part into
[../../porting-playbook.md](../../porting-playbook.md) and
[../../logs/velu-port.md](../../logs/velu-port.md).

### Landed 2026-10-07 — the close-out

**Two modules plus one prerequisite.** `FLTForHuman/Algebra/SpecialLinearGroupSmith.lean`, **111
lines** (3 checker-visible public declarations, mathlib-only, namespace
`Matrix.SpecialLinearGroup.PrimitiveSmith`); `FLTForHuman/ModularCurve/ModularPolynomialE4Cube.lean`,
**529 lines** (34 public declarations — 26 in `DeepCosetAux`, 5 in `CosetRootAux`, 3 headlines; 0
`private`); plus **+38 net lines** (42 added / 4 header lines rewritten) in
`FLTForHuman/ModularForms/Level/Degeneracy.lean`; plus `spec/ModularPolynomialE4CubeConsumer.lean`
(149 lines, five zones / eleven `example`s).

- **Prerequisite surprise.** §2's audit recorded `ModularForm.exists_degeneracy_Gamma0` as landed;
  the port had only the **`CuspForm` twin** — the `ModularForm` helpers had been deliberately
  dropped by the original CuspForm-only pass ("no self-consumed lemmas", `Level/Degeneracy.lean`'s
  old header). It is ported here at its pin name with `restrictMF`/`coe_restrictMF`/
  `exists_modularForm` kept `private`, and its wrapper
  `Theorems/Thm_ModularForm_exists_degeneracy_Gamma0.lean` is added to `SOURCES` (no `S_` file
  needed: the helpers stay `private`). `#print axioms` on the twin is
  `[propext, Classical.choice, Quot.sound]`.
- **Audit — the `E₄³`/`Δ` forms did *not* collapse.** Declaration-line `grep -c` over the pre-S-4
  port (excluding the new module): `e4cubeSL` 0, `deltaSL` 0, `e4cube1` 0, `delta1` 0.
  `ModularForms/DiscPow.lean`'s `eCubeSubESq` is `E₄³ − E₆²` (`E₄.pow 3 − E₆.pow 2`), the numerator
  of `1728Δ` via `discriminant_eq_smul_eCubeSubESq` — a *different* form, so it is not the pin's
  `e4cubeSL`. `DiscPow.discPowForm 1` is the nearest twin of `deltaSL`
  (`mcast … (CuspForm.toModularFormₗ discriminant).pow 1`, weight `12 * 1`, coe
  `⇑CuspForm.discriminant ^ 1`), but neither its weight nor its coe is `deltaSL`'s
  (weight `12`, coe `ModularForm.discriminant`), so it is not a drop-in. `JInvariant.lean`'s
  `ModularForm.j` (`fun τ => E₄ τ ^ 3 / discriminant τ`) **is** definitionally the pin's `jt`; the
  pin's `jt`/`jt_smul` are pin-public, so the port keeps them (and `jt_smul` has a pre-existing
  statement-counterpart under another name, `WLight.j_smul_eq`,
  `ModularForms/WeightOne/LevelField.lean:288`, invisible to `port_advise`; it sits outside S-4's
  import cone — `LevelField` is imported only by `LevelN` — so the pin's 10-line proof was
  transcribed rather than dragging the weight-one module in). Net: 4 new public defs (23 lines with
  their `coe_*`).
- **Audit — the q-expansion bookkeeping was genuinely absent.** Declaration-line `grep -c` over the
  pre-S-4 port (excluding the new module): `qExpansion_finset_prod` 0, `qExpansion_finset_sum_smul`
  0, `pow_mul_div_pow` 0, `prod_ite_pow` 0, `card_univ_mul` 0, `coeAddHom` 0, `def An` 0, `def fam`
  0; `def mono`/`coe_mono` matched only unrelated `private` declarations
  (`EichlerShimura/BinaryForm.lean:232,235`). ≈120 new lines, but thin glue over facts the port
  already had: `UpperHalfPlane.qExpansion_{mul,add,smul,zero,one}`,
  `UpperHalfPlane.cuspFunction_{mul,add,smul}`, `UpperHalfPlane.analyticAt_cuspFunction_zero`,
  `ModularForm.qExpansion_eq_zero_iff`, `ModularForm.{mcast,coe_mcast,coe_mul,one_coe_eq_one}`,
  mathlib's `ModularForm.prodEqualWeights`/`coe_prodEqualWeights`, `HahnSeries.ofPowerSeries_injective`,
  `HahnSeries.C_mul_eq_smul`, and `ModularCurve.{qExpand,qExpand_coeff_mul,qExpand_coeff_of_not_dvd,
  qExpand_injective,coeffMap,coeffMap_coeff,jqModC,jqModC_eq_qExpansion_E4_cube_div_discriminant,
  jqModC_rat,map_jqModC,evalAtJ,evalAtJ_X,jqN,jq,jNum,constantCoeff_jNum,mem_primCosetReps}`.
  **The pin's `set_option maxHeartbeats 6400000 in` was not transcribed and was not needed**: the
  smul headline fits the frozen `4_000_000` cap — the first declaration in the row the pin had to
  boost and the port does not.
- **Saving.** Raw pin lines 565 (A 367 + B 85 + C 25 + leaf 88) / content 463 (298 + 85 + 10 + 70).
  `port_advise` on the landed tree: **32 of 37** A/B/C declarations and **4 of 4** leaf
  declarations are statement-identical (≈511 lines) — the pre-port figure was **2 substitutions ≈5
  lines**, the renamed-declaration blind spot. **678 lines written** (111 + 529 + 38), ratio ≈1.20
  over content; the excess is headers/import lists/docstrings and the pin's own statement spelling.
- **Checker.** before `6181 (312 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own (6217
  checked)` → after `6219 (312, 83), 0 mismatched, 0 missing, 36 own (6255 checked)`. Delta **+38
  identical / +38 checked = 34 `ModularPolynomialE4Cube` + 3 `SpecialLinearGroupSmith` + 1
  `ModularForm.exists_degeneracy_Gamma0`** (26 + 5 + 3 + 3 + 1); `promoted`/`renamed`/`own`/
  `mismatched`/`missing` all unmoved. `--prop-bodies`: **263 identical / 6 textual** (unchanged;
  `def An`'s body is identical and the 6 are the pre-existing advisory rows). `SOURCES` gained the
  four wrapper/`S_` pairs at the pin names plus the degeneracy wrapper; `PORT_FILES` gained
  `SpecialLinearGroupSmith.lean` then `ModularPolynomialE4Cube.lean`, appended last.
- **Consumer.** `spec/ModularPolynomialE4CubeConsumer.lean` exits **0**, wall **57.94 s**
  (`timeout 90 lake env lean`, flocked; two failing iterations 66.8 s / 67.6 s). Zones: (1) the leaf
  at `(N, a, b, d) = (6, 2, 1, 3)` with `exists_coprime_mul_add` and the determinant certificates
  read off `γ.det_coe`; (2) the `E₄³`/`Δ` forms (`coe_e4cubeSL`/`coe_deltaSL`), the degeneracy step
  at `d = 1`, and the smul headline at the concrete level-one `modularPolynomialDataOne`; (3) the
  coset headline at the concrete primitive triple `(2, 1, 3)` (membership via `mem_primCosetReps`);
  (4) S-3's headline composed into the coset form with both `jLattice`s rewritten by
  `PeriodPair.jLattice_ofTau`, and the packaged `jLattice` headline; (5) `jt_smul`. Deleting either
  module gives `object file … does not exist`.
- **Axioms.** `#print axioms` on `PrimitiveSmith.main`,
  `exists_eq_mul_diagonal_mul_of_gcd_eq_one`, `ModularForm.exists_degeneracy_Gamma0` and the three
  headlines: all `[propext, Classical.choice, Quot.sound]`; 0 `sorry`.
- **Builds.** Pre-flight: the `ModularPolynomial*`+`ModularForm` cone stub **2:02.04** wall /
  4.39 GB RSS cold, **84.46 s** warm (user 5.5 / sys 25.3); the leaf stub **46.83 s**. Edit loop:
  leaf clean **46.83 s**; main module **84.29 s** (error round) → **64.01 s** clean; the axioms
  scratch **71.31 s**. `lake build SpecialLinearGroupSmith Level.Degeneracy` **9.52 s** wall / 9.61
  user / 9.40 sys / 3,602 jobs; `lake build SpecialLinearGroupSmith ModularPolynomialE4Cube`
  **117.22 s** wall / 20.02 user / 38.51 sys / 9,108 jobs (the main module 102 s). `build_ladder
  --edit` on the two new modules plus the `Degeneracy` edit: **2 dependents / 454 lines ≈15 s**
  (`WeierstrassCurve.ModularityLifting` 241, `ModularForms.EigenformLevel` 213). Whole-tree flocked
  `lake build` green, **9,325 jobs**, **25.26 s** wall / 15.94 user / 18.89 sys.
- **Friction.**
  1. **An order's "ported" row is a claim to `grep -c`, not a fact — the S-2/S-3 finding recurs.**
     `ModularForm.exists_degeneracy_Gamma0` was absent; `grep -rl` found its name only inside three
     comment lines. Porting it cost 38 net lines and is the set's one addition outside the two
     ordered modules.
  2. **`port_advise` under-reports the reuse by ~16× pre-port and over-reports it after landing.**
     2 ≈5 pre-port; 32 ≈428 + 4 ≈83 on the landed tree, i.e. every public declaration of the four
     `S_` files is statement-identical once written. Neither figure is the *content* figure; only
     the by-statement `grep -c` audit is.
  3. **The `E₄³`/`Δ` forms are the pin's spelling, not the port's `eCubeSubESq`.** The
     `1728Δ = E₄³ − E₆²` identity (`discriminant_eq_smul_eCubeSubESq`) ties `eCubeSubESq` to `Δ`,
     but the object is a difference form; the four pin defs are new. The port's *only* definitional
     twin is `ModularForm.j` for `jt`.
  4. **Three `v4.34.0` drift tokens, all in proof bodies.** `Prime.dvd_finset_prod_iff` →
     `Prime.dvd_finsetProd_iff` (the pin already carries a `first | … | …`); `ModularForm.coe_smul`
     → `FunLike.coe_smul`; `ModularForm.coe_zero` → `FunLike.coe_zero` (both deprecated aliases).
     Statements were untouched.
  5. **`end A.B` closes *both* scopes.** Under `namespace ModularCurve` / `namespace DeepCosetAux`,
     writing `end ModularCurve.DeepCosetAux` also closes `ModularCurve`, silently de-nesting
     everything after it; the two ends must be bare (`end DeepCosetAux`, `end CosetRootAux`). The
     first error surfaced fifteen lines downstream of the real mistake.
  6. **Import discipline is load-bearing for the audit.** `ModularPolynomialE4Cube` imports
     `Level/Degeneracy` (for the new twin) but **not** `ModularForms/WeightOne/LevelField.lean`
     (where the `jt_smul` counterpart lives); the edit was to an existing module, so `lake env lean`
     on the new module used a stale `Degeneracy.olean` until a tier-1 `lake build` refreshed it
     (the S-3 finding, again).
