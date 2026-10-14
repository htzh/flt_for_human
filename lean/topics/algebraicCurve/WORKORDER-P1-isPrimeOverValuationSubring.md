# WORKORDER-P1 — the place realising a prime over a valuation subring

**Status (closed 2026-10-14): landed and reviewed green.** One set, one module, one
public headline. No manager pre-round was owed (§2). Measured outcome: module
`FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean` (1,775 lines, 1
public / 124 `private`); checker **9743 identical (671 promoted, 83 renamed), 0
mismatched, 0 missing, 38 own-proof exempted (9781 checked)** — delta +1, the
headline; tier-1 build green, 0 warnings, 2,691 jobs; axioms
`[propext, Classical.choice, Quot.sound]`; consumer 0 errors; grep sweep clean. The
manager re-ran the checker, the tier-1 build and the axioms probe and confirmed a 1:1
declaration map to the pin (125 each, `solution` → the headline). Friction:
[ac-port.md](../../logs/ac-port.md) §12.

**Audience.** A fresh coding session. The method is
[porting-playbook.md](../../porting-playbook.md) §3–§5 (especially §3.3 the order
template, §3.5 the build ladder, §4 faithfulness, §5 sharing); the house style is the
sibling modules in `FLTForHuman/AlgebraicCurve/Place/`. Read this whole order before
writing a line.

**Companion.** The row was scoped against
[PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2 and the AC column's
[ac-port.md](../../logs/ac-port.md) §11.1 (the deferred definition-module API list).
The other `AlgebraicCurve` ready-shelf leaf, `RadialRegion.exists_rect_sixArcs`, is
**not** this set — it shares nothing with this node and needs its own
`Def_AlgebraicCurve_CellDissection` pre-round; do not touch it.

## 1. Scope

Port the one pin node `AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring`:
the valuation-theoretic realisation step for an integral affine model of a curve over
a valuation subring. Given an algebraically closed `K`, a field extension `F`,
`A : ValuationSubring K`, `j : F` transcendental over `K` with `F` finite-dimensional
and separable over `K(j)`, a subring `B ≤ F` containing the constants and `j` and
integral over `K[A] ∪ {j}`, and a prime `𝔮` of `B` over the maximal ideal of `A` with
`j - a₀ ∈ 𝔮`, produce a place `w` of `F` with `0 < w.ord (j - algebraMap K F a₀)` and
`b ∈ 𝔮 ↔ ∃ a ∈ maximalIdeal A, (b - algebraMap K F a) ∈ w.toValuationSubring.nonunits`
for every `b : B`.

The node is the pin `S_` file **whole** (playbook §2.3): its 68 `_root_.`-rooted
`private` helpers, the namespace-local `private` helpers, and the one public
headline. Nothing in the pin file is out of scope except the pin-only scaffolding
(`p2m_export` / `p2m_open` / `p2m_reactivate`, §5.2) and the `P2M.Util` import it
buys.

**Not this set:** the `RadialRegion` row; any edit to an existing module (the hub
prohibition, §7); the deferred definition-module API of §2.

Measured (playbook step 3):

| quantity | value |
|---|---:|
| pin `S_` lines | 1,886 |
| net new math lines | **1,853** |
| declaration groups | 122 |
| public headlines | **1** |
| substitutions | 0 trusted / 0 suspect |

That is a large single set (~1.9k content lines, playbook §0.2's ~1,500 dispatch
point), but it is one mathematical story and one module, so it is not split.

## 2. Pre-round: none is owed

The workflow's step 4 is the manager's. It is already done or not needed, and this is
the evidence; an agent that finds it wrong stops and reports rather than editing a
hub.

**(a) The definition layer is homed.** The pin `S_` file imports two
`Definitions/` modules: `Def_AlgebraicCurve_PlacesOverDVR` and
`Def_AlgebraicCurve_DivisorClassGroup`. Both are in the port.

* `Def_AlgebraicCurve_PlacesOverDVR` (45 decls) → `Defs/PlacesOverDVR.lean`:
  `port_advise` reads 39 byte-identical (36 public, 3 port-`private`), and the proof
  names exactly two of them, both public:
  `Place.mem_of_eval_monic_eq_zero` and `Place.mem_maximalIdeal_iff_ord_pos`.
* `Def_AlgebraicCurve_DivisorClassGroup` (63 decls) → `Defs/Place.lean`,
  `Defs/Divisor.lean`, `Defs/SemilinearAut.lean`,
  `WeierstrassCurve/Velu/MapEquation.lean`: 47 byte-identical. The statement uses
  the `Place` structure and its `ord`/`deg`/`ResidueField` API; the proof uses
  `Place.ext` from `Defs/Place.lean`.
* The unported remainder is exactly the AC column's **documented deferred
  definition-module API** (`logs/ac-port.md` §11.1): the Galois `≃ₐ` action on
  `Place`/`Divisor`/`Pic0`, `Pic`/`torsion`/`AbelJacobiCard`,
  `Place.card_fiberOver_eq` / `fiber_eq_fiberOver`,
  `Place.finite_setOf_forall_mem_and_ord_pos`, `placeOfPoint`/`Place.Congr`. Each
  has a `grep -c 0` for this node: the `S_` proof names **none** of
  `coe_chartHom`, `finite_setOf_forall_mem_and_ord_pos`, `card_fiberOver_eq`,
  `fiber_eq_fiberOver`, `torsion`, `mem_torsion`, `AbelJacobiCard`,
  `smul_mem_degZero`, `smul_mem_principal`, `degZeroSMulHom`,
  `coe_degZeroSMulHom`, `smul_mk`. The `S_` file re-derives its own private
  `ValuationSubring.inv_algebraMap_mem` (pin line 975), so the port-`private` copy
  in `Defs/PlacesOverDVR.lean` is not needed. Do not port the remainder here.

**(b) No promotions.** `port_advise` §1 reports no importable port copy for any of
the 122 target declarations, and no port-`private` declaration the target must name
(the §2 "port once" list is empty). The five names the target shares with the pin
pool are `centre`, `inv_algebraMap_mem`, `isDedekindDomain_integralClosure_adjoin`,
`isFractionRing_integralClosure_adjoin`,
`surjective_algebraMap_residueField_of_deg_eq_one` — all re-proved `private` in the
port, none requiring an existing declaration to move.

**(c) No dedup and no name collisions.** The target set is the `S_` file plus its
`Theorems/` wrapper, which are the same single headline; `port_advise` §2 finds no
name proved in two target files. None of the 68 rooted `private` helper names
collides with an existing port declaration (`IsFinitePlace.centre` is a different
namespace), so the checker's dotted fallback has nothing ambiguous to match.

## 3. Source

Pinned `anthropics/fermats-last-theorem@aa2d8b3`:

* statement (the comparable copy): `Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean`
  (the wrapper, `-- pin:` source for the headline);
* proof: `P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean`
  (1,886 lines). The `Theorems/` wrapper declares the statement and closes it with
  `p2m_exact_reverting @_root_.P2MW.S_..._valuationSubring.solution`; the port states
  it directly.

Rendered links:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean>
and
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean>.

The wrapper carries the pin's global preludes

```lean
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt ... (9 names)
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring ... AlgebraicCurve.Pic0.coe_pullbackDegZeroHom (17 names)
```

These disable downstream instances/simps because the pin's `S_` file redeclares
`private` copies of some of the same facts (its own `centre`, `compSubring`,
`value`, `inv_algebraMap_mem`). The port does **not** copy the blanket attributes:
it keeps those helpers `private` (so they cannot fight the public API) and narrows
any needed `attribute [-simp]` to the single declaration if a proof genuinely
needs it, with a one-line reason. Record any narrowing in the module header.

## 4. Deliverable

Home: `FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean`
(the `Place/` directory already holds `DegreeOne.lean`, `FiniteResidue.lean`,
`Completion.lean`, `AdicCompletion.lean`).

Imports:

```lean
import FLTForHuman.AlgebraicCurve.Defs.Place
import FLTForHuman.AlgebraicCurve.Defs.PlacesOverDVR
-- plus the pin's own Mathlib imports (pin lines 1-20) that are not already reached
```

Do **not** write `import Mathlib`. Start from the pin's list and drop what the two
`FLTForHuman` imports already pull; confirm with the edit loop, not by guess.

Namespace map (the pin's `p2m_export`/`p2m_open` machinery is *not* ported; use
explicit namespaces and `open`s):

| pin block | lines | port placement |
|---|---:|---|
| `namespace ValuationSubring` | 28–98, 722–881, 952–1023, 1089–1269, 1360–1388, 1755–1775 | `namespace ValuationSubring`, `private` |
| `namespace Subring` | 101–134, 890–949 | `namespace Subring`, `private` |
| `namespace AlgebraicCurve` / `Place` | 143–717, 1026–1058, 1467–1614, 1617–1752, 1778–1838 | `namespace AlgebraicCurve` / `namespace Place`, `private` |
| `namespace Valuation` | 1065–1086 | `namespace Valuation`, `private` |
| `namespace RingHom` | 1393–1464 | `namespace RingHom`, `private` |
| **`solution`** | 1841–1886 | **public** `AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring` |

Everything is `private` except the single headline. The `S_` file has exactly one
non-`private` declaration (`theorem solution`, line 1841); keep it that way.

The headline, stated exactly as the wrapper (this is the checker-comparable text;
carry the `-- pin:` comment above it):

```lean
-- pin: exists_of_isPrime_over_valuationSubring (S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean:1841)
theorem AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring {K F : Type*} [Field K]
    [Field F] [Algebra K F] [IsAlgClosed K] (A : ValuationSubring K) {j : F}
    (hj : Transcendental K j)
    [FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({j} : Set F)) F]
    {B : Subring F} (hconst : ∀ a : A, algebraMap K F a ∈ B) (hjB : j ∈ B)
    (hint : ∀ b : B,
      IsIntegral (Subring.closure (Set.range ((algebraMap K F).comp A.subtype) ∪ {j})) (b : F))
    (𝔮 : Ideal B) [𝔮.IsPrime]
    (h𝔮A : ∀ a : A, a ∈ IsLocalRing.maximalIdeal A → (⟨algebraMap K F a, hconst a⟩ : B) ∈ 𝔮)
    (a₀ : A) (hja : (⟨j, hjB⟩ : B) - ⟨algebraMap K F a₀, hconst a₀⟩ ∈ 𝔮) :
    ∃ w : AlgebraicCurve.Place K F,
      0 < w.ord (j - algebraMap K F a₀) ∧
      ∀ b : B, b ∈ 𝔮 ↔ ∃ a : A, a ∈ IsLocalRing.maximalIdeal A ∧
        ((b : F) - algebraMap K F a) ∈ w.toValuationSubring.nonunits := by
  ...
```

The pin's proof body is the 46-line `solution` block at lines 1841–1886, which
reduces the hypothesis `h𝔮A` to an iff (its own `h𝔮A'`) and then applies
`Place.exists_place_centre_comap_eq` (line 1483, 144 lines) — the mathematical core —
via `hasValueAt_iff_ord_pos`, `mem_centre_iff`, `value`, `mem_centre_iff_of_hasValueAt`.

### Declaration inventory (pin line → what it is)

* `ValuationSubring` 34–93: `closureConstantsAdjoin_eq_range_aeval`,
  `aeval_injective_of_transcendental`, `aeval_mem_closure`, `polynomialEquivClosure`,
  `isIntegrallyClosed_closure`.
* `Subring` 107–111: `isIntegral_iff_exists_monic_eval₂`,
  `exists_ideal_le_comap_eq_of_isIntegral`.
* `AlgebraicCurve.Place` 153–706: the `HasValueAt` valuation/residue cluster
  (`algebraMap_mem`, `mem_of_ord_pos`, `mem_nonunits_iff_ord_pos`, `HasValueAt` and
  its `.unique`/`.add`/`.neg`/`.mul`/`.pow`/`.inv`/`.div`,
  `hasValueAt_iff_ord_pos`, `surjective_algebraMap_residueField_of_isAlgClosed`,
  `surjective_algebraMap_residueField_of_deg_eq_one`), the `compSubring`/`value`
  dictionary (`compSubring`, `mem_compSubring_iff`, `value`,
  `hasValueAt_value`, `value_surjective`, `algebraMap_mem_compSubring_iff`), the
  `centre` ideal (`centre`, `mem_centre_iff`, `mem_centre_iff_of_hasValueAt`,
  `mem_centre_of_ord_pos`, `algebraMap_mem_centre_iff`), the dominating valuation
  subring (`mem_compSubring_or_inv_mem`, `compValuationSubring`,
  `mem_compSubring_of_isIntegral`, `mem_compSubring_of_isIntegral'`,
  `exists_unique_valueHom`), and the residue/centre map facts
  (`residue_comp_value_surjective`, `ker_residue_comp_value`,
  `centre_comap_isMaximal`, `sub_value_mem_centre_comap`,
  `algebraMap_mem_centre_comap_iff`).
* `ValuationSubring` 728–868: `algebraMap_bijective_of_isIntegral_of_isAlgClosed`,
  `exists_sub_constants_mem`, `constants_unique_mod`, `ValuationSubring.constants`.
* `Subring` 896–933: `exists_valuationSubring_dominating`, `ne_top_of_dominating`,
  `algebraMap_mem_of_dominating`.
* `ValuationSubring` 960–1017: `centreOver`, `mem_centreOver_iff`,
  `inv_algebraMap_mem`, `centreOver_ne_bot`, `centreHeightOneSpectrum`,
  `valuationSubringAtPrime_centre_le`, `eq_valuationSubringAtPrime_centre`,
  `isPrincipalIdealRing_of_dedekind_le`.
* `AlgebraicCurve.Place` 1037–1049: `ofValuationSubringOver` and its two facts.
* `Valuation` 1071: `exists_ne_map_eq_of_sum_eq_zero`.
* `ValuationSubring` 1096–1264: the `CharP`/`IsAlgClosed` residue block
  (`natCast_mem_ker`, `natCast_mem_maximalIdeal`, `isUnit_intCast_of_not_dvd`,
  `map_intCast_eq_zero_of_not_isUnit`, `map_eq_zero_of_rat_mem_maximalIdeal`,
  `exists_pow_valuation_eq_of_isRoot`, `ker_eq_maximalIdeal_of_isAlgebraic`,
  `exists_mul_eq_one_of_map_ne_zero`, `ker_eq_maximalIdeal_apply`).
* `AlgebraicCurve` 1285–1341: `isPrincipalIdealRing_adjoin_singleton`,
  `isDedekindDomain_adjoin_singleton`, `isDedekindDomain_integralClosure_adjoin`,
  `isFractionRing_integralClosure_adjoin`, `integralClosure_adjoin_le_valuationSubring`,
  `algebraMap_mem_integralClosure_adjoin`, `self_mem_integralClosure_adjoin`,
  `le_integralClosure_adjoin_of_isIntegral`.
* `ValuationSubring` 1366: `isAlgClosed_of_surjective`.
* `RingHom` 1399–1458: `imagePrime`, `rangeRestrict_mem_imagePrime_iff`,
  `mk_mem_imagePrime_iff`, `mem_imagePrime_iff`, `imagePrime_ne_top`,
  `imagePrime_isPrime`, `imagePrime_isMaximal`, `eq_zero_of_const_mem_imagePrime`,
  `const_mem_range`.
* `AlgebraicCurve.Place` 1477–1483: `eq_zero_of_X_sub_C_dvd_C`,
  **`exists_place_centre_comap_eq`** (the core, 144 lines).
* `AlgebraicCurve.Place` 1627–1745: `finite_residueField_of_adjoin_simple_eq_top_of_mem`,
  `IntermediateField.adjoin_simple_inv_eq`,
  `finite_residueField_of_adjoin_simple_eq_top`,
  `finiteResidue_of_adjoin_simple_eq_top`.
* `ValuationSubring` 1762 and `AlgebraicCurve.Place` 1788–1827:
  `eq_of_forall_mem_nonunits_iff` (both copies),
  `eq_of_forall_mem_nonunits_iff_of_surjective`,
  `integralClosure_adjoin_le_of_forall_isIntegral_mem`,
  `exists_eq_of_integralClosure_adjoin`.

## 5. Route

**5.1 Reuse, never restate.** The port's shared ground is the public API of
`Defs/Place.lean` (`Place` structure with `toValuationSubring`, `ord`, `deg`,
`ResidueField`, `heightOneSpectrum`, `adicValuation`, `Place.ext`, the `ord_*`
lemmas, `ord_algebraMap`) and `Defs/PlacesOverDVR.lean`
(`Place.mem_of_eval_monic_eq_zero`, `Place.mem_maximalIdeal_iff_ord_pos`, the
`center`/`fiberCenter`/`placeOfPrime` API). Import them; the pin names the same
declarations, so the checker will agree.

**5.2 The pin scaffolding does not port.** The `S_` file opens with
`namespace P2MW.S_...`, `p2m_export "ValuationSubring" "..."`, `p2m_open`, and
eight `p2m_reactivate` lines. These are FLT's export/move machinery. In the port
they become plain `namespace`/`open` and the declarations keep their proper
namespaces. The `p2m_export` lists are useful as an index: they name exactly which
`ValuationSubring` helpers the pin moves into the public namespace.

**5.3 Faithfulness.** Transcribe the statements and proof bodies; adapt only what
v4.34 forces (playbook §4). The AC column's friction log (`logs/ac-port.md` §11.2)
records the recurrent v4.33.1 → v4.34.0 drift to expect:
`Set.mem_setOf_eq`, `zero_le'`, `if_pos`/`if_neg`, `finiteDimensional_adjoin`, the
deprecated `Ideal` ramification API, `prime_of_normalized_factor`. Prefer the new
mathlib names in proofs; if a *statement* must keep pin text for the checker, say
so in the module header and keep the suppression on the single declaration.

**5.4 Stop-early risks, with the deviation protocol.**

* **A needed port-`private` declaration.** If a proof requires
  `Defs/PlacesOverDVR`'s port-`private` `inv_algebraMap_mem`, `chartHom`, or
  `mem_center_iff` — or any other existing module's `private` — **stop and report**
  with the declaration, host and a `build_ladder.py --edit` price. Do not promote
  it yourself; re-derive it locally `private` instead if it is cheap (the hub
  prohibition, §7).
* **The blanket `attribute [-instance]` / `[-simp]` preludes.** Do not copy them
  file-wide. If one proof needs a simp set narrowed, narrow it on that
  declaration and record it.
* **The `HasValueAt`/`centre` name overlap.** The pin's `private` copies share
  short names with public port API (`centre` vs `center`, `value`). Because they
  stay `private` and the port's names differ, there is no clash; if Lean reports
  one, rename the port helper at the pin's dotted name and report.
* **Build-time blow-up.** Instance inference, not proof length, is the cost
  (playbook §3.5). Diagnose with `set_option diagnostics true` on the one
  declaration in a scratch copy; never raise `maxHeartbeats`.

## 6. Build discipline (copy, do not paraphrase)

> Edit loop
> `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` —
> the cap is **low on purpose**: a declaration that exceeds it has an
> instance-inference defect, and the low cap is what finds it. Never raise
> `maxHeartbeats`, never add a module `set_option maxHeartbeats`. `lake build
> <module>` per finished file, serialized with `flock` and bounded with `timeout`.
> Per wave, build only the wave's affected targets — **never a bare whole-tree
> `lake build`**. A whole-tree build happens once, at the session's end, only after
> the user agrees to it, and never on the agent's own initiative.

Run from `lean/`. The finished-file build is
`flock .lake/flt_build.lock timeout 300 lake build FLTForHuman.AlgebraicCurve.Place.IsPrimeOverValuationSubring`.

## 7. Hub prohibition

This set adds one module and edits exactly three checker lists (§8.2). It must not
edit any existing `.lean` module, must not touch `SOURCES`/`PORT_FILES` entries
other than the three appends, and must not run `git commit`. A subagent that
believes a promotion or a host edit is genuinely required **stops and reports**
with the declaration, the host and the `build_ladder.py --edit` price; the manager
decides. Re-derive a cheap missing helper locally `private` and report it in the
friction log.

## 8. Verification

**8.1 The checker.** Baseline on the tree this order was written against:
`9742 statements identical (671 promoted from pin-private, 83 renamed), 0
mismatched, 0 missing, 38 own-proof declarations exempted (9780 checked)`.

The expected delta is **+1 identical** — the single public headline. Every other
declaration in the module is `private`, so the checker does not see it. Report the
actual numbers; they must be `0 mismatched / 0 missing`.

**8.2 Wiring (append last, in this order).**

* `spec/check_flt_statements.py` `SOURCES` (pin paths):
  * `"Theorems/Thm_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean"`
  * `"P2M/Sol/S_AlgebraicCurve_Place_exists_of_isPrime_over_valuationSubring.lean"`
* `spec/check_flt_statements.py` `PORT_FILES`:
  * `"FLTForHuman/AlgebraicCurve/Place/IsPrimeOverValuationSubring.lean"`

Add a one-line comment naming this order, as the neighbouring entries do. The
wrapper is the comparable copy; the `S_` file is listed for the pin's public
headline and the dotted fallback.

**8.3 The rest of the gate.**

```bash
cd lean
python3 spec/check_flt_statements.py                 # expect 9743 identical / 0 / 0 / 38
flock .lake/flt_build.lock timeout 900 lake build FLTForHuman.AlgebraicCurve.Place.IsPrimeOverValuationSubring
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
```

plus:

* `#print axioms AlgebraicCurve.Place.exists_of_isPrime_over_valuationSubring` —
  expect `[propext, Classical.choice, Quot.sound]` and nothing else;
* a `grep` sweep of the new module for `sorry` / `admit` / `axiom` /
  `native_decide` / `import Mathlib` / `maxHeartbeats` — all zero;
* tier 1 build green with **0 warnings**;
* `git status` showing only the new module and the two checker-list appends.

`tools/deps/unwired_register.py --check` is not owed: this module is tier 1 (in
`PORT_FILES`), not a tier-3 engine.

## 9. Report shape

Report, in order: (1) the module path and the final public/`private` split; (2) the
build result per tier actually run, wall and user CPU; (3) the checker before/after
with the delta reconciled against the headline; (4) the `#print axioms` line; (5)
the grep sweep; (6) every deviation — statement changes, narrowed attributes,
helpers re-derived that the port already had, and any promotion you stopped on;
(7) the friction to append to `logs/ac-port.md`, in the existing format; (8) any
successor the landing puts on the ready shelf — in particular confirm that
`RadialRegion.exists_rect_sixArcs` remains and that its
`Def_AlgebraicCurve_CellDissection` pre-round is still owed.
