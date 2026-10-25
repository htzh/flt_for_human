# NB1: the Atkin–Lehner slash and two headlines over one proof

2026-10-25. The landing record for
[`topics/deligneSerre/WORKORDER-NB1-alSlash-and-twin-headlines.md`](../topics/deligneSerre/WORKORDER-NB1-alSlash-and-twin-headlines.md),
against the pin `anthropics/fermats-last-theorem@aa2d8b3`. Three new modules, four headline
nodes, one copy of the shared 1,189-line block.

## 1. What landed

| module | lines | decls | pin |
|---|---:|---:|---|
| `ModularForms/AtkinLehnerSlash.lean` | 367 | 24 (21 public, 3 private) | the twin premise pair `S_ModularForm_{isZeroAt,mdifferentiable}_alSlash.lean` |
| `ModularForms/WeightOne/PrimitiveQCoeffNorm.lean` | 1,297 (1,223 of block) | 71 (70 public, 1 private) | `S_CuspForm_norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd.lean` (1,321 L) |
| `ModularForms/WeightOne/NebentypusQCoeffSq.lean` | 138 | 2 (1 public, 1 private) | `S_CuspForm_qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_…lean` (1,312 L) |

**P1, the slash calculus.** The 23 declarations of the premise file, ported once, plus the two
root headlines `ModularForm.isZeroAt_alSlash` / `ModularForm.mdifferentiable_alSlash` at the
statement of their `Theorems/` wrappers. The premises' two `solution`s differ only in which
`alSlash` lemma they state, so the port has one development and two wrappers instead of two
copies. The pin's `private` helpers stay `private` (`mat_mul_normalizes`, `denom_scalarGL`,
`num_scalarGL`); six more (`map_int_mul`, `val_det_scalarGL`, `det_scalarGL_pos`,
`scalarGL_smul`, `slash_scalarGL`, `alGL_mul_alGL`) are **public** here, because A's twin file
states them publicly and P2 imports them rather than repeating them — see §4. Each carries a
`-- pin: <name> (P2M/Sol/S_CuspForm_norm_…:line)` marker, since that file is not in P1's
header wire.

**P2, the shared block + A.** Declarations `section API` … `end Main` of A, verbatim, in a fresh
namespace `CuspForm.PrimitiveQCoeffNorm` (so that no name is shadowed and the headline can be
`CuspForm.…`), with A's `ℓ` spelling throughout; A's `main` becomes the `private`
`main_of_isPrimitiveForm`; the public headline is A's wrapper statement
`CuspForm.norm_qCoeff_sq_eq_pow_of_isPrimitiveForm_of_not_sq_dvd`.

**P3, B's head only.** Imports P2, `open CuspForm.PrimitiveQCoeffNorm`, adds the `private`
`main_of_nebentypus` (B's 64-line assembly) and B's headline
`CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd`,
copied from `Theorems/Thm_…:13`. **None of the shared block is re-declared** — B's pin rows for
the block are simply never compared (verdicts are computed on port declarations only). `datum`
stays in P2 (A's `ℓ` spelling); B's `p`-spelling `datum` is not declared, so its row is not
compared either. 1,312 of B's lines reduce to 138.

## 2. The block diffed against A

Chunked at `section API` … `end Main` (pin lines 30–1306, 1,277 lines), the port keeps **1,189
lines byte-identical** (after `rstrip`). The non-identical lines are:

| change | lines | why |
|---|---:|---|
| `map_int_mul` deleted | 4 | P1 now carries it publicly (A's statement, verbatim) |
| `scalarGL` group deleted (`scalarGL`, `scalarGL_coe`, `val_det_scalarGL`, `det_scalarGL_pos`, `scalarGL_smul`, `slash_scalarGL`, `alGL_mul_alGL`) | 55 | same: P1's copies are public and P2 imports them |
| `let δ` hoists in seven proofs | 7 × +1 | Lean 4.34 elaboration, see §5 |
| `if_pos` → `ite_eq_left` | 1 | v4.34 deprecation |
| `T_mem_Gamma1` proof → `simp` | 1 | the port's `Gamma1_mem` simp set is the shorter one |
| `periodic_of_slash_T` proof → the port's | 19 → 2 | the lemma is already ported (`ModularForm.periodic_of_slash_T`) |
| `main` → `private main_of_isPrimitiveForm` | 1 | the order's arrangement |

Every *statement* in the block is A's text, byte for byte. The four `ℓ`-vs-`p` binders, the
`Γ₁ℝ`/`Γ₀ℝ` local notations and the `IsOfType`/`repMat`/`wt`/`trForm` names are A's.

## 3. Gates

| gate | reading |
|---|---|
| `lake build` P1 / P2 / P3 | green, 5.3 s / 9.3 s / 4.2 s, **0 warnings** each |
| `#print axioms` on the four headlines | `[propext, Classical.choice, Quot.sound]` each |
| `check_port --force` P1 | **21 ok**, 0 mismatch, 0 missing, 0 own, 0 kw |
| `check_port --force` P2 | **70 ok**, 0 mismatch, 0 missing, 0 own, 0 kw |
| `check_port --force` P3 | **1 ok**, 0 mismatch, 0 missing, 0 own, 0 kw |
| `frontier --target` `ModularForm.isZeroAt_alSlash` | **needed 0** |
| `frontier --target` `ModularForm.mdifferentiable_alSlash` | **needed 0** |
| `frontier --target` `CuspForm.norm_qCoeff_sq_eq_pow_…` | **needed 0** |
| `frontier --target` `CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_…` | **needed 0** |
| `dedup.py` over the three | **0 clusters** (99 declarations, 3 modules) |
| `move_dead.py --select dead` | 0 declarations each |
| `spec/DsHeadConsumer.lean` (new zone `[nb1]`) | exit 0, **0 errors**; renaming the P3 headline gives `unknown constant …`, exit 1 |
| `frontier --ds` | **1,180 nodes / 443,088 raw** (was 1,184 / 446,334) |

P1's 21 = the 15 declarations of the premise pair (13 with public statements + 2 wrapper
headlines) + the 6 now-public helpers diffed against A. P2's 70 + `private main_of_isPrimitiveForm`
+ the headline row. P3's single row is B's headline.

## 4. Arrangement decisions worth knowing

- **The promoted seven are not used by P2.** The ground record made `phi`, `phi_props`,
  `phi_eq_smul_of_qCoeff`, `cusp_slash_T_pow`, `isBoundedAtImInfty_heckeU`, `T_mem_Gamma1`,
  `denom_ne_zero'` importable, and they still are; but A's file declares its own copies, and
  the order asks for "the shared 63-declaration block verbatim from A's spelling". Keeping the
  block whole was the cheaper and more faithful reading, and `dedup` is satisfied by making the
  six helpers P1 also needs public in P1 instead of copying them into P2. So the promotions are
  *available*, not *consumed*, by this wave. (One promotion *was* consumed as a proof: P2's
  `periodic_of_slash_T` delegates to the ported `ModularForm.periodic_of_slash_T`, 19 lines to
  2.)
- **`CuspForm.PrimitiveQCoeffNorm`** is where the block lives, so `CuspForm.norm_…` is the
  headline's full name and the frontier tool sees the node. The block's names are unchanged
  otherwise; the checker matches by last name.
- **Two `alSlash_alSlash` declarations are kept**: P1's (arbitrary functions, level-invariance
  hypothesis, `ModularForm.alSlash_alSlash`) and A's (the `IsOfType`/`CuspForm` version, in P2's
  namespace). Their statements differ, and both are needed; no reshaping was necessary, and
  `dedup` does not confuse them.

## 5. Friction hit (so the next reader does not rediscover it)

- **`⟨_, hdetδ⟩ ∈ Gamma0 M` does not elaborate in v4.34.** `SL(2, ℤ)` is a plain `def` for
  `Subtype (fun A => A.det = 1)`, and the `Membership.mem` arguments are checked at *implicit*
  transparency: an anonymous constructor produces a `Subtype`-headed term, not an `SL`-headed
  one. Eight proofs in the pin (one in P1, seven in P2) write exactly that. The fix used is a
  local `let δ : SL(2, ℤ) := ⟨matrix, hdetδ⟩` then `refine ⟨δ, …⟩`; `δ` is a local definition, so
  later `rfl`/`exact` goals still see through it. (In P1, where `Units.ext` follows, a `hδcoe`
  from `rfl` was needed as well.)
- `𝓘(ℂ)`/`MDifferentiable` need `Mathlib.Geometry.Manifold.MFDeriv.Defs` and
  `Mathlib.Geometry.Manifold.IsManifold.Basic`; `ChartedSpace ℂ ℍ` needs
  `Mathlib.Analysis.Complex.UpperHalfPlane.Manifold`; `MDifferentiable.slash` needs
  `Mathlib.NumberTheory.ModularForms.Basic`; `Nat.prime_iff_prime_int` needs
  `Mathlib.Data.Nat.Prime.Int`.
- P2 additionally needs `Mathlib.NumberTheory.DirichletCharacter.Basic` +
  `.Bounds` (`ε.unit_norm_eq_one`) and `FLTForHuman.ModularForms.HeckeCusps`
  (`CuspFormClass.isZeroAt_heckeU`) and `FLTForHuman.ModularForms.HeckePrelude` (the ported
  `periodic_of_slash_T` and the T-matrix block).
- The pin's `haveI` walls are kept literal; P2/P3 carry the port's
  `set_option linter.style.haveILetI false` for that, as `HeckePrelude` does. Without it, one
  style warning in P2.
- Three `if_pos` → `ite_eq_left` (two in P1, one left in P2 after the `scalarGL` block moved to
  P1).
- `T_mem_Gamma1`'s pin proof `simp [Gamma1_mem, ModularGroup.T]` leaves an unsolved goal in
  v4.34 and makes `Gamma1_mem` an unused simp arg; `by simp` is the port's own proof and works.

## 6. Consumer

`spec/DsHeadConsumer.lean` gains the zone `[nb1]`: both `CuspForm` headlines applied at
`M = 2`, `k = 0`, `ℓ = p = 2` (so `M / ℓ = 1` and `ε'` is a level-1 character), with
`IsPrimitiveForm` / `HasNebentypus` from `Defs/PrimitiveFormGamma1.lean`. The two
`alSlash` headlines are used by the `CuspForm` ones (headline A/B's proofs call
`ModularForm.isZeroAt_alSlash` / `…_mdifferentiable_alSlash`), and the zone is an executed
application of all four, so deleting any headline breaks the file. Verified by renaming P3's
headline: the consumer failed with `Unknown constant
CuspForm.qCoeff_sq_eq_mul_zpow_or_exists_hasNebentypus_qCoeff_hecke_eigen_of_dvd_of_not_sq_dvd`.

## 7. Tree state

The three modules build green with no warnings and no `sorry`; `spec/DsHeadConsumer.lean` is not
part of any library (nothing globs `spec/`). No file outside the three new modules, their
`spec-pin` wiring, `spec/DsHeadConsumer.lean`, this log, the work order's §7 and the topic note
was touched.

## Manager pass (2026-10-25)

Every reading above was re-taken on the final tree. Two corrections to the worker's report:

- The "1,189 of 1,223 block lines byte-identical to A" figure is a *line-level* similarity. At
  declaration level, 64 of the 69 shared declarations are byte-identical (749 lines of A) and 5
  differ: `exists_traceRep_cocycle` (159 → 168 lines) and `exists_cocycle_hecke_al` (196 → 209),
  both only by the `let δ : SL(2, ℤ) := …` fix for the `Gamma0` membership elaboration (statements
  untouched — the checker diffs them `ok`), `smul_slash_pos` and `T_mem_Gamma1` at equal size, and
  `periodic_of_slash_T` (22 → 5), the deliberate delegation to the ported
  `ModularForm.periodic_of_slash_T`.
- `#print axioms` is verified **out of band**, not in the module. The manager first appended the
  four lines; that makes every build print `info:` lines, which violates the silent-build standard
  and was reverted. The check now lives in `lean/tmp/axioms.lean` (import the module, then
  `#print axioms …`), and all four headlines read `[propext, Classical.choice, Quot.sound]`
  there. The three orders now say so explicitly, so no later worker re-adds the prints.
