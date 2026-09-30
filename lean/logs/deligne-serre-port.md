# The Deligne–Serre weight-one port — the unconditional 54-node slice

Record of the port of the unconditional slice of the Deligne–Serre weight-one
effort ([topics/PORTING-DeligneSerre.md](../topics/PORTING-DeligneSerre.md)) from
the FLT pin `anthropics/fermats-last-theorem@aa2d8b3` into `FLTForHuman/`, mathlib
`v4.34.0`. The method is [porting-playbook.md](../porting-playbook.md); the
per-set work orders are `topics/deligneSerre/WORKORDER-{H,S1,…,S8}*.md`; the
running friction ledger is [deligne-serre-friction.md](deligne-serre-friction.md).
**Status: COMPLETE — 54/54 nodes, checker 2552 identical / 0 mismatched / 0
missing, full build green, consumer green.** The working tree is uncommitted; the
human owns git.

## 0. What shipped

| phase | subject | nodes / modules | written lines | checker (identical) |
|---|---|---|---:|---:|
| **D** | the 20 pin `Def_*` modules | 15 new + 5 verify-only | 1,922 | 2058 → 2252 |
| **H1** | the four shared prelude homes | 4 new | 624 | 2252 → 2295 |
| **H2** | promotions and the 22 clash reconciliations | edits in 11 files | — | 2295 → 2301 |
| **S1** | weight-one Eisenstein series | 5 targets / 5 modules | 2,074 | 2301 → 2444 |
| **S2** | Hecke / Γ₁ vanishing and nebentypus | 9 targets / 5 modules | 1,893 | 2444 → 2453 |
| **S3** | relèvement and the lifting | 2 targets / 2 modules | ~2,000 | 2453 → 2457 |
| **S4** | coefficient ring and Galois conjugation | 6 targets / 2 new + 2 extended | 1,381 | 2457 → 2463 |
| **S5** | semisimple descent | 1 target / 1 module | 727 | 2463 → 2467 |
| **S7** | Frobenius density and Frobenius elements | 27 targets / 17 modules | ~2,900 | 2467 → 2548 |
| **S6** | representation conjugacy and lifting | 3 targets / 3 modules | 1,174 | 2548 → 2551 |
| **S8** | the complex-trace assembly | 1 target / 1 module | 493 | 2551 → 2552 |
| | **total** | **54 targets** | **≈15,200** | **2058 → 2552 (+494)** |

Plus the wire test `spec/DeligneSerreConsumer.lean` (281 lines, 13 zones) and 48
new `.lean` files. Baseline **2058 identical / 0 mismatched / 0 missing / 30
own-proof exempted** before the effort; final **2552 / 0 / 0 / 30**, 92 promoted
from pin-`private` declarations, 2582 port declarations checked.

## 1. Phase D — the definitions layer

Fifteen new modules and five verified-only, in the pin's four-level import DAG:
`GaloisRep/Defs/{MatrixRepresentation,FrobeniusPowerDense}`,
`ModularForms/Eisenstein/WeierstrassZeta`, `FieldTheory/RatAlgClosureGalois`,
`ModularCurve/Defs/{Gamma0Away,IharaIota,IharaAmalgam,IharaAmalgamMap}`,
`Algebra/BrauerNesbitt`, `ModularForms/Defs/{Gamma1HeckeOperators,PrimitiveFormGamma1}`,
`NumberTheory/FrobeniusDensity/{TaylorWilesPrimes,DegOneAsymptotic,BadPrimes,PrimeSums}`.
Verified-only: `Def_ModularForm_HeckeOperator`, `Def_FLTPrelim_Ramification`,
`Def_FLTPrelim_Modularity`, `Def_EllipticCurve_FrobeniusTrace`,
`Def_GaloisRep_Residual`. The 7 declarations of
`Def_CuspForm_Gamma1HeckeOperators` whose port name carried a different statement
were deliberately not shadowed and handed to H2.

## 2. Phase H — the prelude homes and the reconciliation pass

**H1** wrote four homes from the `port_advise` reading: `GaloisRep/Prelude.lean`,
`ModularForms/Eisenstein/Cotangent.lean`, `NumberTheory/FrobeniusDensity/Basic.lean`,
`ModularForms/HeckePrelude.lean`. Two findings:
* the 78-block list is a **proof** dedup, so it omitted repeated **definitions** —
  the manager's addendum had `om` (four Eisenstein files) and `ser` (two) homed in
  `Cotangent.lean`, which would otherwise have been copied three and two times;
* `hasSum_ser` cannot live in a prelude: its pin proof calls S1's own
  `hasSum_weierstrassZeta_sub_mul_G2`. It was deferred and is ported in S1's
  `WeierstrassZetaQuasiPeriod.lean`. `sum_moebius_mem_zpowers` and
  `degOneSum_ne_top` were deferred the same way and homed in S7-II.

**H2** performed the only cascade: the seven port-`private` promotions (five
existed; `adjoinRoot'`/`locKer` are absent tree-wide — unported, not promotable),
the four `private …_11` refinements promoted to the pin's three-conjunct public
statements with the two-conjunct copies renamed `…_two`, and the 22 clashes
reconciled by shape (binder-only, naming-only, dropped-conjunct **strengthened**,
specialised-vs-general, genuine content, unrelated collision). Two clashes the
advice tool missed — `isZeroAt_heckeU` and `sum_range_eq_sum_zmod` — were taken
from the phase-D friction log. Several pin-statement copies live in distinct
namespaces (`ModularForm.HeckeGamma1.*`, `HeckeRepresentatives.HeckeGamma1.*`,
`X1DiamondRational.PeriodOne.*`, `CuspForm.Gamma1Hecke.*`) and phase-T consumers
must open them. One `export` alias in `Level/Diamond.lean` restores the pin's
`CuspForm.diamondLinOne`/`CuspForm.slashOfMemGamma0` spelling; it adds no
checker-visible declaration.

## 3. The theorem sets

* **S1** — the `E₁(1, χ)` multiplier: `WeierstrassZetaSum`,
  `WeierstrassZetaQuasiPeriod`, `EisensteinG1Transform`, `EisensteinG1QExpansion`,
  `WeightOneMultiplier`, all under `ModularForms/Eisenstein/`. The cotangent
  calculus is imported from H1, never re-proved; the multiplier did **not** need an
  unported interface.
* **S2** — `HeckeTLinOneQCoeff`, `HeckeNebentypus`, `Gamma1Vanishing`,
  `HeckeEigenNebentypus`, `ModularCurve/IharaSurjective`. The Γ₁/diamond half and
  the H2-reconciled statements are imported; `heckeU_add_slash_…` is a thin `exact`
  over the D1 `heckeU_add_slash_…_of_mem_Gamma0`.
* **S3** — `DeligneSerre/{Relevement,Lifting}`: the weight-generic relèvement and
  the weight-one instance. The relèvement's pin proof needed S4's node 5 before S4
  was ported, so it was transcribed `private` and, in the refactor round, replaced
  by S4's public copy and deleted.
* **S4** — `Algebra/LatticeEigenvalues` (nodes 1–3), `Algebra/IntegralExtensionCharacters`
  extended (node 4), `Algebra/FaithfulLatticeEigenvector` extended (node 5),
  `DeligneSerre/CoefficientRing` (node 6). Node 6 stands in the H1 `HeckePrelude`
  `cusp_*` lemmas for the pin's `T_pow_mem_Gamma1`/`cusp_slash_T`, so the heavy
  `WeightOne/GammaRational` cone is not imported.
* **S5** — `GaloisRep/SemisimpleDescent`, namespace `DeligneSerre`. Three engines
  duplicated verbatim in the deferred `DSRt` sibling are homed **publicly** so that
  half can import them.
* **S6** — `GaloisRep/{RepConj,RepLift,ConjFromFrobenius}`. `RepConj` reuses phase
  D's `Algebra/BrauerNesbitt`; `RepLift` (the 772-line risk) needed no ported
  prerequisite, only mathlib's Witt-vector/`CharP`/transcendence-basis API.
* **S7** — 27 nodes in the `FrobeniusDensity/` subject home, dispatched in three
  rounds plus a tail. The coset arguments use mathlib's `Ideal` orbit API; the
  PhiGen/Hecke SL(2,ℤ) coset ports and `FieldTheory/FiniteGroupAction.lean` /
  `WeilExchange/Bifibre.lean` are the **wrong geometry** here (recorded negative).
* **S8** — `DeligneSerre/Assembly`, the capstone: `hfam` stays a genuine
  hypothesis (the ray-class input is deferred by design, `PORTING-DeligneSerre.md`
  §0.3). No upstream binder or lemma was missing — the wire test passed.

## 4. Verification — the milestone gate

Independently re-run by the manager at the end:

* `python3 spec/check_flt_statements.py` → **2552 identical / 0 mismatched / 0
  missing / 30 own-proof exempted**, 2582 checked;
* `flock … lake build` → **green, 4805 jobs**;
* a `#print axioms` probe over **all 54 headlines** (generated, not hand-listed)
  → every name resolves, **no `sorryAx`**, axioms `[propext, Classical.choice,
  Quot.sound]`;
* no real `sorry`/`admit`/`axiom`/`native_decide` anywhere in `FLTForHuman/`, no
  bare `import Mathlib`, no `maxHeartbeats`/`maxRecDepth` overrides;
* `spec/DeligneSerreConsumer.lean` compiles (`lake env lean`, exit 0), with one
  executed cross-module zone per set and hypothesis-form zones for the unported
  inputs (`heig`, `hT`, the S5 character conditions, `hfam`).

The one-token mutation test the statement checker was verified with (`2462/1/0`
etc.) was run by each worker on its own set; the checker itself was mutated in the
phase-D and S7-I rounds.

## 5. Dedup and reuse (measured)

* The pin's 78 shared in-target blocks (585 removable lines by the greedy count)
  were homed once in H1; `card_le_of_forall_pow_eq`, `ncard_conj_mem_eq_card_mul_ncard`
  and the zeta chain are the load-bearing ones.
* 28 substitutions/21 importable reuse points were imported, not re-proved; the
  S1 multiplier imports `ModularFormClass.qCoeff` from the existing `HeckeQCoeff`.
* The three semisimple engines shared with the deferred sibling are public.
* The only real cross-set duplication found in the refactor scan was S3/S4's node 5,
  promoted and deleted. Deliberately **not** promoted: S2's prelude copies (public
  homes sit in the heavy `WeightOne` cone; sharing would invert the import graph),
  `exists_finset_separating` (no public home), S7-III's `tendsto_log_sub_one`
  (deliberate 7-line duplicate), and the private `det_eq` in
  `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean` (identical to the public
  `ModularForm.HeckeRepresentatives.det_eq`; outside the refactor round's whitelist).

## 6. Friction highlights (the generalizable part)

* **Checker textual rules bite**: the diff is textual, so a declaration must spell
  its binders exactly as the wrapper; a name that reads `MISSING IN FLT` usually
  means the `Thm_*` wrapper is missing from `SOURCES` (the `S_` file calls the
  target `solution`). `lemma` vs `theorem` is matched; section variables hide
  explicit binders. This recurred across S1, S2 and S7.
* **The `git status` trap**: untracked directories are collapsed, so a script that
  harvests new modules from `git status --porcelain` must pass `-uall` (it silently
  skipped the whole `DeligneSerre/` directory during the axioms probe).
* **API drift (mathlib `v4.34.0`)**: `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`,
  `dif_pos`/`dif_neg` → `dite_eq_left`/`dite_eq_right`, `Set.mem_setOf_eq` →
  `Set.mem_ofPred_eq`, `Set.Infinite.diff` → `sdiff`, `Polynomial.finite_setOf_isRoot`
  → `finite_setOfPred_isRoot`; a `Mathlib.*` directory is not a module
  (`IntegralClosure.IntegralClosure`, `Ideal.Quotient.HasFiniteQuotients`); a
  `normalizedFactors … .toFinset` `simp` rewrite; explicit-positional application
  against an implicit binder; `simp only [...] at` cannot wrap its location list.
  The full list is in the per-set friction sections.
* **Stale-olean `Unknown constant`**: after a module's olean is added, a consumer
  checked with `lake env lean` can report `Unknown constant` until the defining
  module is built. `touch` does not force a rebuild (lake hashes content).
* **Ordering**: S3 needed S4's node 5 and was dispatched before S4; the refactor
  round repaired it. S7-I's tail node needed S7-II's `degOneSum_add_log_isBigO` and
  was dispatched as a tail. The manager's rule held: a worker stops at a boundary
  and logs, rather than editing a closed file or weakening a statement.

## 7. Residuals, and what is deliberately out of scope

* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer
  today (kept public per the pin).
* `linter.style.haveILetI` / `unusedSectionVars` notes remain in a few proof
  modules (they are style, and in some cases the `haveI` is load-bearing).
* The **deferred half** is untouched by design: Group B (the irreducibility
  criterion and image-order bound, behind the ray-class analytic continuation), the
  density block as a second interface, the two analytic gates, and the converse
  cone. See `PORTING-DeligneSerre.md` §7.

## 8. Re-running and the hand-off

```bash
cd lean
python3 spec/check_flt_statements.py          # 2552 / 0 / 0 expected
flock /tmp/flt_for_human.lock timeout 400 lake build   # 4805 jobs
flock /tmp/flt_for_human.lock timeout 180 \
  lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

The per-set work orders carry the statement provenance and the pin file:line for
every block; the friction log carries the resolved-locally ledger and the
refactor-round record. The pin is `aa2d8b3`; line-anchored raw links are in the
module headers.
