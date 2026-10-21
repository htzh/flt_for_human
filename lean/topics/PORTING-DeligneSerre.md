# The Deligne–Serre weight-one column — frontier, workflow and plan

The column ports `DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen` — the weight-one
mod-`ℓ` Galois-representation theorem — from the pin `anthropics/fermats-last-theorem@aa2d8b3`
(Lean `v4.33.1` / mathlib `db584cd6`) into the port library at mathlib `v4.34.0`. This note is
the column's state and plan: §1 what the port contains, §2 the frontier as it stands, §3 the
workflow the manager follows, §4 the shared ground (definitions, promotions, hubs) that is the
manager's own work, §5 the build economy, §6 verification, §7 what remains, §8 reproduce, §9
residuals. Every measurement is the pin's, read through `tools/deps`. The section numbers are
stable: work orders across the column cite §3 for the workflow and §7 for the gates.

The checker is **`spec/check_port.py` alone**, one module at a time, wired by the module's own
`spec-pin:` header (§6). The statement parser itself is **`spec/lean_parser.py`** (2026-10-20):
the checker, the corpus builder and the `tools/deps` planning tools import it directly, and the
frozen `old_check_stmts.py` imports it rather than owning it; the extraction also fixed the
`end A.B` namespace-stack bug (FR-0035). On 2026-10-20 it reads **3506 ok, 0 mismatched, 0 missing, 11 own, 0 kw
over 129 wired modules** (582 `PORT_FILES` modules exempt; corpus `aa2d8b3`). `spec/old_check_stmts.py`
is the grandfathered registry and is **not run as a gate**; its last reading, before the handoff,
was 10473 identical (774 promoted, 83 renamed), 0 mismatched, 0 missing, 42 own-proof exemptions
(10809 checked). Declaration-level exceptions live in `spec/decl_markers.tsv`, never in the Lean
source. This column's recent landings: the
`TateFormal`/`TateSlots` definition layer, 9241 → 9304; the weight-4 Tate-slot engine and headline
façade (WORKORDER-F1), 9304 → 9318; the six `tateCurve`/Katz definition modules of WORKORDER-F2,
9318 → 9535 (+217); the `BridgeX` twin/triplet engine and headline façade (WORKORDER-F2),
9535 → 9540 (+5); and the `CohCarrier` Hecke–diamond definition layer
([deligneSerre/TOPIC-cohcarrier-comm-triplet.md](deligneSerre/TOPIC-cohcarrier-comm-triplet.md) §4–§6),
`CohCarrierLevel.lean` + `CohCarrierLower.lean`, 9786 → 9854 (+68) with both modules green,
then its Hecke–diamond commutation triplet engine + three-headline façade (WORKORDER-CT1),
9854 → **9857 (+3)**; and the D-S cone's `HahnSeries.isAlgClosed_rat` leaf, ported as a
**tier-3** mathlib supplement (`RingTheory/HahnSeries/IsAlgClosed.lean`, the generalized
Newton–Puiseux theorem, 67 public declarations, all registered in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md); record:
[logs/hahn-series-alg-closed.md](../logs/hahn-series-alg-closed.md)) — no checker delta, since
the module is unlisted; and the Petersson adjointness of `T_p` on the nebentypus component,
`CuspForm.peterssonOn_hecke_eq_conj_mul_of_hasNebentypus` (1,230 pin lines, the leaf above the
nebentypus eigenbasis), 9857 → **9877 (+20)**: `peterssonOn` (+3), the fundamental-domain
ground (+16), the tier-1 headline (+1), with its 100-declaration engine tier-3 and registered
(record: [deligneSerre/TOPIC-petersson-hecke-adjointness.md](deligneSerre/TOPIC-petersson-hecke-adjointness.md)); and
the archimedean Casimir **definition layer**, the ground for the arch-derivative subject the
`--include-leaves` shelf shows 78 needed nodes of (33,726 raw `S_` lines): the pin's
`Def_LanglandsTunnell_ArchParam` (33 declarations) and `Def_AutomorphicForm_ArchDerivCasimir` (58,
the whole `archDerivAt`/`archCasimirAt`/`IsArchSmoothAt`/`ArchDir` API, which the port did not have
at all) homed whole at `LanglandsTunnell/ArchParam.lean` and
`AutomorphicForm/Adelic/ArchDerivCasimir.lean`, 9877 → **10104 (+91)** — measured against the tree
as found, which the note's 9877 had already left at 10013 by other columns' landings — and then its
first proof set, the real-place `CasCore` trio
([automorphicForm/WORKORDER-AC2-cascore-trio.md](automorphicForm/WORKORDER-AC2-cascore-trio.md)):
one listed module, `AutomorphicForm/Adelic/ArchCasimir.lean`, whose wire is exactly three headlines,
10104 → **10107 (+3)**, with the 128-declaration shared engine public and registered tier 3
([automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md),
[automorphicForm/WORKORDER-AC1-defs.md](automorphicForm/WORKORDER-AC1-defs.md)). The **centre-cut
pair** — the vanishing leaf
`AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`
(902 pin lines) and its sibling
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre`
(892 pin lines) — landed together with the checker at **10239 identical**, one headline each (+1
per leaf). The two pin files share a 645-line block, ported once and public as the tier-3 engine
`AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean` (964 lines, 49 declarations, registered); the
façades are `CentreCutVanishing.lean` (64 lines) and `CuspUnrealizable.lean` (59 lines). Records:
[logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md); orders:
[automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md](automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md),
[automorphicForm/WORKORDER-CCS-centre-cut-sibling.md](automorphicForm/WORKORDER-CCS-centre-cut-sibling.md).
The **centre-cut fundamental-domain trio** then landed on the shared slab prelude promoted public in
`PeterssonSlabPairing.lean`: the automorphy-transfer node
`AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre`
(325 pin lines, `Adelic/DetNormSlab.lean`) and the two measurable-fundamental-domain twins
`exists_measurableSet_isFundamentalDomain_subset_iUnion_{integralWindowed,centreCut}SiegelSet_of_coversModCentre`
(267/266, one module `Adelic/MeasurableFundamentalDomainCover.lean`); checker **10263 identical**
(+3 headlines, +21 promoted prelude declarations the checker can diff). The fourth `--ready` row,
the 234-line slab-integral bound, is deferred on the missing
`Def_AutomorphicForm_CuspidalSpectrumCarrier.lean` (carry-forward). Record:
[logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md); order:
[automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md](automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md).
The **complex archimedean Casimir layer** then landed as Set B wave 0: the missing 196-line
`ArchDerivCasimirComplex` and 381-line `ArchDerivCasimirComplexAPI` definition pair (checker +78),
the 857-line complex engine `AutomorphicForm/Adelic/ArchCasimirComplex.lean` (96 declarations public
tier 3), and its first headline
`AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` (+1); checker **10342
identical**, 294 registered-unwired exempted. `port_advise` found 0 substitutions and only 43
binder-spelling variants against the real `ArchCasimir.lean`; the two engines are architectural
mirrors (normalized similarity ≈0.38) because the complex half adds `archDelAt`/`archDelBarAt`,
`Del1`/`Del2`, the conjugate transport and `archCasimirBarAtComplex`, so the complex engine was
ported once as a separate tier-3 engine. Record:
[logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md); order:
[automorphicForm/WORKORDER-ACC-arch-casimir-complex.md](automorphicForm/WORKORDER-ACC-arch-casimir-complex.md).
The **continuous norm section** then landed as the first `NumberField.TateGlobal` cut after the
`continuous_ideleNorm` hub: `NumberField.TateGlobal.exists_continuous_monoidHom_ideleNorm_apply_eq`
— a continuous monoid hom `ℝ≥0ˣ →* (AdeleRing (𝓞 F) F)ˣ` splitting the idèle norm, with trivial
finite part — as the 239-line tier-3 engine `NumberField/TateGlobal/NormSection.lean` (25 public
declarations, at the pin's `FujisakiC3` names; the same block is re-proved in nine sibling `S_`
files) plus the 44-line listed façade `NumberField/TateGlobalNormSection.lean` (one headline,
checker **+1**, **10343 identical**), again with no existing module edited. The node is a graph
leaf with 57 whole-project dependents and lies on the shortest citation path to
`fermatLastTheorem`. Record: [logs/norm-section.md](../logs/norm-section.md); topic and order:
[numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md),
[numberTheory/tateGlobal/WORKORDER-T4-norm-section.md](numberTheory/tateGlobal/WORKORDER-T4-norm-section.md).
**GL₂ strong approximation over ℚ** then landed as the first *theorem* over the `AdelicLevel`
definition layer: `NumberField.AdelicLevel.exists_globalPoints_mul_mem_finiteIntegralGL2_rat` —
every finite idèle class has a rational representative modulo the integral level — as a
five-module tier-3 engine `NumberField/AdelicLevel/StrongApprox/{Elementary,Membership,Conjugation,Gauss,Approximation}.lean`
(45 public declarations, 1,136 lines) plus the 49-line listed façade
`NumberField/AdelicLevel/StrongApproxRat.lean`. This is the column's first **pure
transcription**: `port_advise` reports **0 substitutions**, so 874 of the 898 pin lines are new
mathematics, and none of the 45 names is re-proved anywhere else in the pin. Checker **+1**,
**10344 identical**; no existing module edited. Record:
[logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md); topic and order:
[numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md](numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md),
[numberTheory/adelicLevel/WORKORDER-T5-gl2-strong-approximation.md](numberTheory/adelicLevel/WORKORDER-T5-gl2-strong-approximation.md).
The **`EisensteinGeneral` local twisted integral** then landed as the column's first
`EisensteinGeneral` cut: the five ready shelf rows of that namespace are one story — the local
integral of a twisted smooth function at one place — 2,134 raw `S_` lines of which 673 are
duplicate copies. The set opened with its **definition gate**,
`LanglandsTunnell/TateLocalConstantsAt.lean` (the pin's `Def_LanglandsTunnell_TateLocalConstantsAt`
whole, 21 declarations, +21; the five statements all quantify over `higherUnitsAt`), three
promotions out of `private` in `TateGlobal/WeylSmooth.lean` and `WeylShell.lean` (+3), and the
dedup that the gate forced — `WeylSmooth.lean` carried a second `higherUnitsAt` and now imports
the gate (−1). Then **Set A** (the ramified trio): two tier-3 engines
`EisensteinGeneral/LocalTwisted.lean` (527 lines, 25 declarations — the 486-line prelude the pin
writes twice, so 972 → 527 lines) and `LocalRamShells.lean` (265, 9), plus the 354-line listed
façade `LocalRam.lean` with three headlines (**+3**); and **Set B** (the unramified pair): the
single listed module `EisensteinGeneral/LocalUnr.lean` (408 lines, 18 declarations, **+18**),
listed whole with its two `S_` files because its machinery has no other consumer — the first set
in the column where most of the checker delta comes through the promoted-from-pin-private
fallback (702 → 718). Checker **10388 identical**, 0 mismatched / 0 missing. Records:
[logs/eisenstein-local-twisted-ram.md](../logs/eisenstein-local-twisted-ram.md),
[logs/eisenstein-local-twisted-unr.md](../logs/eisenstein-local-twisted-unr.md); topic and
orders: [numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md),
[numberTheory/eisensteinGeneral/WORKORDER-E1-local-twisted-ram.md](numberTheory/eisensteinGeneral/WORKORDER-E1-local-twisted-ram.md),
[numberTheory/eisensteinGeneral/WORKORDER-E2-local-twisted-unr.md](numberTheory/eisensteinGeneral/WORKORDER-E2-local-twisted-unr.md).
The **finite-adelic integral as an Euler product** then landed as the column's largest
`EisensteinGeneral` cut: `EisensteinGeneral.Factorization.integrable_finprod_and_inv_measure_mul_integral_eq_tprod`
(864 pin lines, 58 declarations, 839 net new) — the integral of `∏ᶠ v, h v (x v)` over the finite
adèles equals the Euler product of the normalized local integrals, given summable deviations from
`1`. It is homed as five engines (`EisensteinGeneral/Factorization/{ProductMeasure,Stratum,Measure,Integrability,Tprod}.lean`,
1,035 lines, 56 declarations) plus a 145-line listed façade, and — unlike every other engine in the
column — **all six modules are listed** with the pin `S_` file in `SOURCES`, so all **57**
declarations are statement-checked (**+57**, the column's biggest single wired delta; the
promoted-from-pin-private count moves 718 → 774). The only non-new declaration is a one-line alias
of `TateGlobal.ShellSupport.integralOff`. Checker **10445 identical**, 0 mismatched / 0 missing.
Record: [logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md); topic and order:
[numberTheory/eisensteinGeneral/TOPIC-factorization.md](numberTheory/eisensteinGeneral/TOPIC-factorization.md),
[numberTheory/eisensteinGeneral/WORKORDER-E3-factorization.md](numberTheory/eisensteinGeneral/WORKORDER-E3-factorization.md).
The **nebentypus Hecke bound** `CuspForm.norm_sq_lt_of_hasNebentypus_qCoeff_hecke_eigen`
(`‖a‖² < (p+1)² p^{k-2}` for `p ∤ M`) then landed as **P3** of the coset/Petersson set — and it
is the column's clearest dedup case: the pin's two `norm_sq` silos share their prelude, so **24
of the silo's 57 declarations were already in the tree** (in `ModularForms/Analytic/NormSqPow.lean`,
namespace `CuspForm.LiNormSq`), and two more (the `p`/`ℓ` variants of `geom_sum_root` and
`qParam_heckeDiag_smul`) are subsumed by the ported copies at the consumers — so the landing is
**≈614 net new lines / 30 declarations**, not 893. One listed module, `ModularForms/Analytic/NormSqLt.lean` (732 lines, namespace
`CuspForm.HeckeBoundGamma1`, importing the sibling's silo and `open`ing it so the pin's proofs
transcribe), checker **+31**, **10476 identical**. Record: [logs/normsq-lt.md](../logs/normsq-lt.md);
order and results:
[deligneSerre/WORKORDER-P3-normsq-lt.md](deligneSerre/WORKORDER-P3-normsq-lt.md); the set's topic
(now complete: P1/P2/P3) is
[deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md).
The **local-parameter finite cover** then landed as the cone's first `AlgebraicCurve` cut
after the `normsq-lt` set, and the column's first landing under the **new per-module statement
protocol** (§6): the 857-line leaf `AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`
("finitely many parameter discs cover every place" — the compactness of the Riemann surface of a
complex function field) as **two modules, 30 statement-checked declarations, one headline**. The
manager's pre-round `AlgebraicCurve/Place/OrdCalculus.lean` (218 lines, 13 declarations) homes the
generic place calculus the pin writes into the prelim section of all three `localParam` `S_` files —
five of the thirteen appear verbatim in both siblings and two more in one, and eleven are re-proved
in 3–40 pin files each, so this is a real dedup, not a convenience; the silo itself is
`AlgebraicCurve/Place/FiniteCover.lean` (654 lines, 17 declarations: `sum_support_eq_zero`, the two
local-analysis lemmas, `structure Fam` and its eleven lemmas, `Fam.exists_finset_cover`, and the
headline at the wrapper's name). Both modules carry `spec-pin:` lines and **no** `PORT_FILES`
entry: `spec/check_port.py` verifies **30 ok / 0 mismatch / 0 missing** against the pin, the frozen
checker is unchanged at **10473**, the tier-1 build is 3,295 jobs with 0 warnings, and every
headline's axioms are `[propext, Classical.choice, Quot.sound]`. Records:
[logs/localParam-finite-cover.md](../logs/localParam-finite-cover.md); topic and order:
[algebraicCurve/TOPIC-localParam-finite-cover.md](algebraicCurve/TOPIC-localParam-finite-cover.md),
[algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md](algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md).

The **rest of the `localParam` family** then landed in six modules, 2,653 lines and **167
statement-checked declarations** — the largest wired surface of the column, all of it under the
new checker: the branch-uniqueness leaf (`Place/BranchUniqueness.lean`, 37 ok), the third leaf as a
60-declaration `MeroRealize` engine plus a 40-declaration `LocalParam.Datum` layer
(`Place/MeroRealize.lean`, `Place/LocalParamDatum.lean`), and its four premise leaves
(`Place/LaurentSeriesModel.lean` 1, `Place/TranscendentalOfOrdNeZero.lean` 2,
`IsCurveOver/FinitenessTransfer.lean` 3, `Analysis/PowerSeries/EisensteinAlgSeries.lean` 24 — the
column's first `Analysis/` module). Tier-1 builds 0 warnings throughout, axioms
`[propext, Classical.choice, Quot.sound]`, the frozen checker unchanged at **10473** (nothing was
wired the old way), and the frontier's demand fell by exactly the six nodes. Record:
[logs/localParam-family.md](../logs/localParam-family.md); orders:
[algebraicCurve/WORKORDER-LP2-branch-uniqueness.md](algebraicCurve/WORKORDER-LP2-branch-uniqueness.md),
[algebraicCurve/WORKORDER-LP3a-laurent-and-generator-transfers.md](algebraicCurve/WORKORDER-LP3a-laurent-and-generator-transfers.md),
[algebraicCurve/WORKORDER-LP3b-power-series-growth.md](algebraicCurve/WORKORDER-LP3b-power-series-growth.md),
[algebraicCurve/WORKORDER-LP4-meromorphic-order-dictionary.md](algebraicCurve/WORKORDER-LP4-meromorphic-order-dictionary.md).

The **correspondence-regular leaf** of the `AlgebraicCurve` `Differential` layer then landed as
one module, `AlgebraicCurve/Differential/CorrespondenceRegular.lean` (653 lines,
**19 statement-checked declarations**, one headline): a correspondence — pull back along `φ`,
trace down along `ψ` — preserves regular differentials. It is the column's first set where the
byte tier of `port_advise` fires hard (7 of 26 pin rows already in the tree, 219 lines imported,
581 net new), and it takes two homing decisions worth recording: `Place.exists_restrict_eq` is
the `M := F'` instance of the general theorem in `WeilExchange/Bifibre.lean` and is *called*, not
restated; and the byte tier's suggested home for `ord_nonneg_of_mem'`
(`Canonical/WeilDifferential.lean`, above the Riemann–Roch assembly) was declined for
`Defs/PushPull.lean`'s copy of the same lemma, which keeps the module in the `Defs/` layer (build
2,775 → 2,740 jobs, and the 7 `WeilDifferential` warnings leave the log). The pin's local
`maxHeartbeats` raises are not inherited — the transcription fits the 200,000 cap. Record:
[logs/differential-correspondence-regular.md](../logs/differential-correspondence-regular.md);
order:
[algebraicCurve/WORKORDER-DC1-correspondence-regular.md](algebraicCurve/WORKORDER-DC1-correspondence-regular.md).

The **archimedean type-span leaf** then landed as the automorphic demand's rank-#2 high-impact
leaf: `AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
(813 pin lines) — the `ℂ`-span of the row-isometry right translates of a vector in finitely many
archimedean types is finite-dimensional, stable and still in the same supremum — as **one module,
125 lines, one statement-checked declaration**, `AutomorphicForm/Adelic/Cusp/ArchTypeSpan.lean`.
It is the column's clearest **cross-silo reuse**: 31 of the pin's 39 declarations (696 of 786
declaration lines) are byte-identical to the shared `Q09` engine in
`RepTheory/TypeReproducer.lean` (tier 3, registered), which was homed from the *archTestFactor*
silo's pin file — the pin writes that engine twice and the port wrote it once, so this leaf
**imports** it and adds only the pin's 59-line instantiation plus the headline (90 net new lines,
31 trusted / 0 suspect substitutions, no host edit, no promotion, no registration). Checker **+1**,
**1816 ok / 0 mismatched / 0 missing** over 45 modules; tier-1 build 3,838 jobs, 0 warnings;
axioms `[propext, Classical.choice, Quot.sound]`. The definition walk found no gate owed: the pin
imports the unported `Def_AutomorphicForm_CuspidalSpectrumCarrier`, but none of its declarations
(and none of `FactorizableTestFn`'s) occurs in the proof, so it stays where it was — the centre-cut
slab bound's gate. Record: [logs/arch-type-span.md](../logs/arch-type-span.md); order:
[automorphicForm/WORKORDER-ATS-arch-type-span.md](automorphicForm/WORKORDER-ATS-arch-type-span.md).

The **separating-uniformiser twin** then landed as the column's first **exact-twin cut over a
pre-ported engine**: `AlgebraicCurve.Place.isSeparable_adjoin_of_ord_eq_one` (455 pin lines, 23
citers) and `…_of_ord_ne_zero_of_cast_natAbs_ne_zero` (460), the two pin files differing by 33 diff
lines, as **one module, 149 lines, two headlines** —
`AlgebraicCurve/Place/SeparableUniformiser.lean`. Two structural moves are worth the record.
First, the pin's private `isSeparable_of_not_pow_mem_range` (and `D_pow_eq_zero`) are **not
ported**: the port's public `Algebra.IsSeparable.of_finrank_fieldRange_frobenius_eq` is the same
theorem up to spelling, so it is called with `frobeniusSubfield` unfolded — 93 net new lines where
a transcription would have been ≈430. Second, the engine they rest on was already in the tree as
**eighteen private declarations** of `AlgebraicCurve/IsCurveOver/FrobeniusSubfield.lean`; the set
promotes the three a consumer states (`frobeniusSubfield`, its transcendental-adjoin index, its
transport) and **hands the host over** — `spec-pin:` lines in, `PORT_FILES` entry out, the
column's first such deletion. Checker **+6** (host 4, façade 2), **1822 ok**; tier-1 builds 2,694
and 1,975 jobs, the dependent wave 4,329 jobs, 0 warnings from the set; axioms
`[propext, Classical.choice, Quot.sound]`. Records:
[logs/separating-uniformiser.md](../logs/separating-uniformiser.md); order:
[algebraicCurve/WORKORDER-SU1-separable-uniformiser.md](algebraicCurve/WORKORDER-SU1-separable-uniformiser.md).

The **Hecke coset seam** then landed as the column's largest set so far — a leaf whose whole cost
was its definition gate: `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (807 pin
lines, `cites 0`, cited by **40** theorems), the explicit `q_v + 1`-coset decomposition of the Hecke
double coset at a finite place, as an engine module `AutomorphicForm/Adelic/HeckeCosetSeam.lean`
(49 statement-checked declarations, the pin's 48 `private` ones made **public** because the
`_principalLevel` sibling imports them) plus the **gate** the statement forced —
`RepTheory/LocalLanglands/{IntegralSubgroup,IntegralSubgroupOpen,HeckeCosetLocal}.lean`, the three
pin `Definitions/` modules the port had never homed (45 declarations, verbatim). `port_advise` read
**0 substitutions** on the leaf and the gate's five "type-only `def` matches" are wrong (recorded);
the transcription is mechanical except one real drift — mathlib `v4.34.0`'s `adicCompletion` is a
one-field structure, so `ext` on an `adicCompletion`-valued matrix now compares `.toCompletion`
images (three proof steps adapted, the pin's `attribute [-ext] adicCompletion.ext` not restored).
Checker **+94**, **1916 ok / 0 mismatched / 0 missing** over 51 modules; tier-1 builds 1,795 / 2,164
/ 2,247 (gate) and 3,625 (leaf) jobs, 0 warnings; axioms
`[propext, Classical.choice, Quot.sound]`. Records:
[logs/hecke-coset-seam.md](../logs/hecke-coset-seam.md); order:
[automorphicForm/WORKORDER-HS1-hecke-coset-seam.md](automorphicForm/WORKORDER-HS1-hecke-coset-seam.md).

The seam's last in-demand row then followed as an **append, not a module**:
`HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem` (39 pin lines, `cites 0`, 33 project
citers) is the *well-definedness* half of the coset-system structure — the coset sum does not depend
on the representatives — so it belongs in the module that already homes `IsHeckeCosetSystem`,
`RepTheory/LocalLanglands/HeckeCosetSystem.lean`. The append was priced as the hub edit it is
(**34 dependent modules / 16,230 lines**, because `SmoothRealization` and `HeckeCosetSeam` import
it), built once as one wave, and it doubles as that module's **handoff** — `spec-pin:` in,
`PORT_FILES` out, so its 14 existing declarations become verified too. Checker **+15**,
**1931 ok**; the `HeckeIntegralSeam.` namespace leaves the D-S demand entirely (`needed`
1,363 → 1,362 nodes, −39 lines). Work-order addendum §9. The family's **`_principalLevel` near
twin** (908 pin lines, 171 diff lines from the leaf) then landed too, although it is outside the
cone: with the engine public it is **11 restated declarations** (the Weyl-conjugacy block, the
`prinU`-flavoured docked statement and the headline) and **45 imported**, including the twin's
`l1U`-spelled membership lemmas — the parent's `(productionPinsGeneral F).U` versions, the same
group by definition. Checker **+11**, **1942 ok** over 53 modules. Work-order addendum §10.

The **matrix-group right-finite supplement** then landed as the column's largest single wired delta
and its cleanest supplement case: the two pin leaves
`Matrix.UnitaryGroup.exists_polynomial_eq_of_continuous_of_rightFinite` (802 pin lines) and
`Matrix.OrthogonalGroup.…` (748) — the D-S leaf shelf's ranks #2 and #5 of 442 — are **one
development the pin writes twice**, since mathlib's `Matrix.orthogonalGroup` *is* the `abbrev` for
`unitaryGroup` and the `ℝ` proof text is the `ℂ` one without conjugation (≈80 % identical at the
base field: 170 changed lines, 37 hunks). It is a Fejér-kernel argument on a compact matrix group
("a continuous right-finite function on `U(2)`/`O(2)` is a polynomial in the entries"), it names
only mathlib objects, and both pin files import mathlib plus the pin's tactic macros and nothing
else — **no definition gate**. Ported faithfully and *not* strengthened (the generic `[RCLike 𝕜]`
and general-`n` routes are recorded as declined, with reasons) as the shared prelude
`LinearAlgebra/Dual/EvalSpan.lean` (68 lines, 1 declaration — the evaluation-combination lemma the
two files duplicate byte-identically) plus `Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`
(816 / 760 lines, 49 / 46 wired declarations), 1,434 net new lines. Checker **+96**, **2038
identical** over 56 modules, 0 mismatched / 0 missing; tier-1 builds 2,051 / 2,639 / 2,639 jobs with
0 warnings; a pre-dispatch scout compiled both pin files unchanged on `v4.34.0` (0 proof drift,
axioms `[propext, Classical.choice, Quot.sound]`), so the set's whole diff is eight warning fixes.
The landing removes 2 nodes / 1,550 raw `S_` lines from the demand. Records:
[logs/matrixgroup-rightfinite.md](../logs/matrixgroup-rightfinite.md); topic and order:
[deligneSerre/TOPIC-matrixgroup-rightfinite.md](deligneSerre/TOPIC-matrixgroup-rightfinite.md),
[deligneSerre/WORKORDER-MG1-right-finite-supplement.md](deligneSerre/WORKORDER-MG1-right-finite-supplement.md).
The rest of the `Matrix.`-namespace demand — nine nodes / 2,969 raw lines after the landing — is
priced together in
[deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md): four
ready leaves (1,041 → 970 net new, +73, WORKORDER-MG2), the
`GeneralLinearGroup.exists_natCard_le_…` row behind its own `ModularCurve.SerreImage.contains_SL2`
premise (1,632 → 1,611 net new, +53, set MG4 in the pricing note; landed 2026-10-20), and four
`SpecialLinearGroup` free-group rows that landed 2026-10-20 as the free-group family.

**The four ready `Matrix.` rows then landed** (WORKORDER-MG2) as four more mathlib supplements, one
module each: `LinearAlgebra/Matrix/SimultaneousEigenbasis.lean` (850 lines — simultaneous-eigenbasis
descent from ℂ to any characteristic-zero field, 63 wired), `Analysis/MatrixGroup/SpecialUnitary2.lean`
(162 — the `SU(2)` Euler decomposition, 7), `LinearAlgebra/Matrix/SL2Generation.lean` (150 — `SL₂(K)`
is generated by diagonal, unipotent and Weyl; its whole proof is private, so 1 wired) and
`LinearAlgebra/Matrix/SpecialLinearGroupHermite.lean` (118 — the Hermite-type coset representative, 2).
970 net new lines, **checker +73** (2038 → **2111 ok over 60 modules**), 0 warnings, axioms
`[propext, Classical.choice, Quot.sound]`; rows 2 and 4 are drift-free, row 3 has the set's one real
drift (a `convert` between two `Membership.mem` props now yields an `Iff`), and row 1's pin `import
Mathlib` became 33 named imports. The `Matrix.`-namespace demand fell to 5 nodes / 1,928 lines: set MG3 and the four free-group
rows, all since landed. Record: [logs/matrix-family-four.md](../logs/matrix-family-four.md).

**The nine small-family pairs of the leaf-families survey then landed** (WORKORDER-MG3, phase 1) — the
wave's first large dedup batch: **18 modules, 6,291 port lines, 323 statement-checked declarations**,
**28 of its 31 priced nodes** plus the bonus `ModularCurve.theta_mul` (185 pin lines, the one declaration
`omegaRow_T2`'s proof lacked). Checker **2111 → 2434 ok over 78 modules**, 0 mismatched / 0 missing,
0 warnings, axioms `[propext, Classical.choice, Quot.sound]`. Along the way it homed **four pin
definition modules whole** — `Def_AlgebraicCurve_ConstantReduction` (127 lines, a hub with 1,944
importers) and `Def_AlgebraicCurve_RegularProlongation` (84, with its 3-declaration
`toRegularProlongation` bridge), `Def_HeckeCharacter_FiniteOrder` (30), `Def_ModularCurve_OmegaOf` (94) —
and deferred one (`Def_ModularCurve_EigenformIdeal`, whose three declarations need the port-blocked
`Def_HeckeGalois_EichlerShimura`; `omegaRow_T2` references none of them; recorded with its trigger in
[CARRY-FORWARD.md](../CARRY-FORWARD.md)). Two items came out of it as standing policy: the 200k
edit-loop cap is a **diagnostic, not the build budget** (§5), and the `ZLattice` pair — drafted but not
landable, because its 563-line `SchwartzMap` module needs >4 minutes at ~110 % CPU — is deferred with its
drafts parked at `lean/tmp/` and its two hotspots diagnosed (§5 of the record). Record:
[logs/ds-leaf-families-wave1.md](../logs/ds-leaf-families-wave1.md); order:
[deligneSerre/WORKORDER-MG3-ds-leaf-families.md](deligneSerre/WORKORDER-MG3-ds-leaf-families.md).
**Phase 2 of that same order then landed and closed the front** (2026-10-20): three groups, **29 modules,
9,874 port lines, 417 statement-checked declarations**, **44 of 49 dispatched nodes** (8,504 pin lines
including the 99-line `Def_Compat_Mathlib430` block-D gate that v4.34's deletion of `Group (AddAut A)`
forced), checker **2434 → 2851 ok over 107 modules**, 0 warnings, axioms
`[propext, Classical.choice, Quot.sound]`, and **no `set_option maxHeartbeats` in any module** — five of the
pins' large bumps turned out to be precaution and were dropped, the two real ones being instance-inference
shape problems. Five nodes are deferred on missing definition gates (`LocalNewvector` 864 lines,
`HeckeEis` 304, `RatAdele` 144 with 799 importers, `RatIdele`'s `Def_RatIdele_Normalizer`), all recorded in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). The frontier over the session: **1,360 → 1,285 nodes / 505,110 →
489,200 raw `S_` lines**. Record: [logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md).
The front's scope criterion (§8 of the leaf-families note) and the re-scoped **phase 3** cut it admits — 37
nodes / 3,641 lines / 7 families, recorded and **not scheduled** — are in
[deligneSerre/TOPIC-phase3-small-supplements.md](deligneSerre/TOPIC-phase3-small-supplements.md); phase 2
overshot that criterion and the note says how.

**The two `Rat*` definition gates and their two proof nodes then landed (2026-10-20).** The gates
phase 2 deferred were homed whole and verbatim: `LanglandsTunnell/StandardLocalConstantsAt.lean`
(the pin's `Def_LanglandsTunnell_StandardLocalConstantsAt`, 144 lines, 799 importers, 21
declarations) and `NumberTheory/RatIdele/Normalizer.lean` (the pin's `Def_RatIdele_Normalizer`,
391 lines, 63 declarations), checker **+84** (3010 → 3094 over 119 modules); the only proof drift
is the v4.34 namespacing of `FiniteAdeleRing.ext` and the `Set.mem_setOf_eq` deprecation. Their
two proof nodes followed in one set: `NumberTheory/RatAdele/DenseRange.lean` (372 lines, 21
declarations, 20 `private`) and `NumberTheory/RatIdele/ClassCharNorm.lean` (376 lines, 49
declarations), checker **+2** (3094 → 3096 over 121 modules), axioms
`[propext, Classical.choice, Quot.sound]`; the pin's `attribute [-instance]` block was dropped
whole and never needed, and the `distribHaarChar` premise's statement is identical. Records:
[logs/rat-def-gates.md](../logs/rat-def-gates.md), [logs/rat-nodes.md](../logs/rat-nodes.md);
order: [deligneSerre/WORKORDER-RN1-rat-nodes.md](deligneSerre/WORKORDER-RN1-rat-nodes.md).

**The `q`-expansion trio and the free-group family then landed (WORKORDER-FG1).** Thirteen nodes /
4,342 pin lines → **eight modules**, ~3,730 body lines, **checker +400** (3096 →
**3496 ok over 129 modules**), 0 mismatch / 0 missing / 0 own / 0 kw, 0 warnings, every headline's
axioms `[propext, Classical.choice, Quot.sound]`. The trio is one module,
`NumberTheory/ModularForms/QExpansionCoeff.lean` (19 wired). The free-group family was re-homed by
subject rather than kept as one engine file — the first cut's single 3,079-line module was split —
into `Combinatorics/SimpleGraph/Transversal.lean` (21: the prelude plus the eleven graph
declarations the engine used to carry), `GroupTheory/FreeDoubleCoset.lean` (12),
`GroupTheory/BassSerre/CosetGraph.lean` (49), `GroupTheory/ModularGroup/FreeProduct.lean` (68),
`GroupTheory/BassSerre/MinimalPeriod.lean` (75), `GroupTheory/FreeGroup/KuroshRank.lean`
(104, the Kurosh engine) and `GroupTheory/FreeGroup/SpecialLinearGroupGenerators.lean` (52, the
four `Matrix.SpecialLinearGroup` headlines — a user-facing API module over the engine, kept for the
user's import path, not as a checker façade). The set paid
the measured dedup — 52 copies deleted (39 in the Kurosh engine: 29 Bass–Serre + 10 graph
transversal; 10 in the façade prelude including `mem_center_iff_eq` 4→1), the one real
substitution (`det_entries`), `mul_entry` restated because the legacy module's copy is private,
and the three parser type-only matches declined. It closes the free-group family, the four
`Matrix.SpecialLinearGroup` rows and the `UpperHalfPlane` q-expansion rows; the frontier falls
**1,276 → 1,259 nodes / 485,836 → 480,304 raw `S_` lines** (the 15 nodes plus the two
`NumberField.`-qualified aliases of the `Rat*` rows). Records:
[logs/qexp-and-freegroup.md](../logs/qexp-and-freegroup.md); order:
[deligneSerre/WORKORDER-FG1-qexp-and-freegroup.md](deligneSerre/WORKORDER-FG1-qexp-and-freegroup.md).

**The last `UpperHalfPlane` row then followed (2026-10-20).** The Fricke conjugate of `U_q`
(`UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU`, 156 lines) had
been excluded by the six-family audit on the *shape* test — FLT's Hecke/Fricke layer, not a
mathlib supplement — although it was never blocked (`Def_ModularForm_HeckeOperator` is homed
whole). It was taken as `ModularForms/HeckeFrickeTrace.lean` (10 wired, build 3,011 jobs /
4.4 s, axioms `[propext, Classical.choice, Quot.sound]`, the pin's `ALTraceIdentity` namespace
kept; the private `frickeGL` copies in the legacy `HeckeNebentypusFricke.lean` are a different
namespace and were not touched). Checker **+10** (3496 → **3506** over 130 modules); the
`UpperHalfPlane` demand row is gone and the D-S demand reads **1,258 nodes / 480,148 raw `S_`
lines**. Record: [logs/hecke-fricke-trace.md](../logs/hecke-fricke-trace.md).

For the landings above that wired into the frozen checker's lists, each delta is exactly its new
public surface, 0 mismatched / 0 missing; the `localParam` landing has no such delta (§6). Since
the 2026-10-19–20 handoff the column verifies with `spec/check_port.py` instead (§6), and a
landing's delta is its statement-checked surface there: the arch-type-span leaf is **+1**, the
separating-uniformiser twin **+6** (four on the handed-over host, two headlines), the Hecke-seam
gate + leaf **+94**, the coset-sum append **+15** (14 from the handed-over coset-system module,
1 headline) and the `_principalLevel` sibling **+11** (the engine imported, not re-proved) of the
1942; the **matrix-group right-finite supplement of §1 is +96** (1942 → 2038 over 56 modules), the
column's largest wired delta, the **four ready `Matrix.` rows of §1 are +73** (2038 → 2111 over 60
modules), the **nine small-family pairs of §1 are +323** (2111 → 2434 over 78 modules), and **phase 2 of
the same order is +417** (2434 → **2851** over 107 modules). The host handoff is also the column's first **deletion** from
`PORT_FILES` — a migration, not an append (§6). The 9542 → 9569 (+27) step is
the `NumberField.AdelicHeight` definition gate, the manager's own ground for the adelic-modulus
round
([numberTheory/adelicModulus/TOPIC-adelic-modulus.md](numberTheory/adelicModulus/TOPIC-adelic-modulus.md)),
not this column's; the remaining growth since the note's earlier figures (9569 → 9786) is other
columns' landings; the column's own history lives in `../logs/` and the work orders.

Companions:

- [../../math/019-deligne-serre-weight-one.md](../../math/019-deligne-serre-weight-one.md)
  — the mathematics: the theorem, the lifting, the assembly from residual data.
- [../../studies/deligne-serre-weight-one-scout.md](../../studies/deligne-serre-weight-one-scout.md)
  — the effort measurement, the subject clusters and the two gates.
- [porting-playbook.md](../porting-playbook.md) — the rules; §2.1–§2.6 (planning),
  §3.1–§3.7 (execution, sets, the build ladder), §4 (faithfulness), §5 (sharing).
- The q-expansion layer's planning records:
  [functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md](functionFieldGeneration/TOPIC-qexp-rationality-degree-head.md)
  and its successors
  [functionFieldGeneration/TOPIC-qexp-successors.md](functionFieldGeneration/TOPIC-qexp-successors.md),
  [functionFieldGeneration/TOPIC-qexp-successors-2.md](functionFieldGeneration/TOPIC-qexp-successors-2.md).
- Adjacent columns: [PORTING-Hecke.md](PORTING-Hecke.md), [PORTING-Level.md](PORTING-Level.md).
- The `NumberField` rows the target closure reaches but this column does not cut: the
  `continuous_ideleNorm` hub's port plan and landing record (the frontier's most connected
  `NumberField` leaf, 15 of the closure's nodes directly above it) is
  [numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md](numberTheory/tateGlobal/TOPIC-continuous-ideleNorm.md),
  and the next cut of the same family — the continuous splitting of the idèle norm — is
  [numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
  with [logs/norm-section.md](../logs/norm-section.md). The first *theorem* over the
  `AdelicLevel` layer, GL₂ strong approximation over ℚ, is
  [numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md](numberTheory/adelicLevel/TOPIC-gl2-strong-approximation.md)
  with [logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md); its definition
  layer is [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md). The `EisensteinGeneral`
  local twisted integral — the local factor computation of the Godement–Eisenstein series, five
  ready rows plus its definition gate — is
  [numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md)
  with [logs/eisenstein-local-twisted-ram.md](../logs/eisenstein-local-twisted-ram.md) and
  [logs/eisenstein-local-twisted-unr.md](../logs/eisenstein-local-twisted-unr.md); its global
  counterpart, the Euler-product factorization of the finite-adelic integral, is
  [numberTheory/eisensteinGeneral/TOPIC-factorization.md](numberTheory/eisensteinGeneral/TOPIC-factorization.md)
  with [logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md).
- The mathematics of the Petersson adjointness proved in this column:
  [../../math/030-petersson-adjointness-of-hecke.md](../../math/030-petersson-adjointness-of-hecke.md).
  The coset/Petersson set's own topic — now complete, P1 the definition layer, P2 the newform
  eigenvalue, P3 the nebentypus bound — is
  [deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md),
  with [logs/normsq-lt.md](../logs/normsq-lt.md) for P3.
- The `WeierstrassCurve` ready shelf, its scoping and its set orders:
  [deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).
- The `AlgebraicCurve` local-parameter leaves — the finite cover as the `Fam` engine, the
  24-lemma prelim block the three `localParam` `S_` files share, and the family's charted-space
  capstone:
  [algebraicCurve/TOPIC-localParam-finite-cover.md](algebraicCurve/TOPIC-localParam-finite-cover.md),
  [algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md](algebraicCurve/WORKORDER-LP1-localParam-finite-cover.md).
- The `CohCarrier` Hecke–diamond commutativity triplet — the three `--include-leaves`
  rows, the 914-line development they share, and the two unported definition modules both
  pin files sit under:
  [deligneSerre/TOPIC-cohcarrier-comm-triplet.md](deligneSerre/TOPIC-cohcarrier-comm-triplet.md).
- The Γ₁/Nebentypus successor pair — the two `CuspForm` rows the shelf once showed, which are the
  lifting column's, not this column's:
  [deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md).
- The `ModularCurve` ready shelf's first cuts — the level-`N` function field and the modular
  polynomial:
  [modularCurve/TOPIC-levelN-and-modular-polynomial.md](modularCurve/TOPIC-levelN-and-modular-polynomial.md),
  [modularCurve/WORKORDER-A-levelN-field.md](modularCurve/WORKORDER-A-levelN-field.md),
  [modularCurve/WORKORDER-B1-phi-rows.md](modularCurve/WORKORDER-B1-phi-rows.md),
  [modularCurve/WORKORDER-B2-fibre-two.md](modularCurve/WORKORDER-B2-fibre-two.md),
  [modularCurve/WORKORDER-C2-x1-function-field.md](modularCurve/WORKORDER-C2-x1-function-field.md),
  [modularCurve/WORKORDER-D1-petersson.md](modularCurve/WORKORDER-D1-petersson.md),
  [modularCurve/WORKORDER-D2-period-map.md](modularCurve/WORKORDER-D2-period-map.md),
  [modularCurve/WORKORDER-E-levelN-qexp-bridge.md](modularCurve/WORKORDER-E-levelN-qexp-bridge.md).
- The weight-4 Tate-slot group the frontier's `--include-leaves` view once showed as fourteen
  `ModularCurve` leaves at ~1650 lines: its mathematics, dedup and port structure are
  [modularCurve/TOPIC-tate-slots-weight-four.md](modularCurve/TOPIC-tate-slots-weight-four.md), and
  the shared-engine order is
  [modularCurve/WORKORDER-F1-tate-slots-engine.md](modularCurve/WORKORDER-F1-tate-slots-engine.md).
- The `tateCurve` twin pair and the triplet lurking beside it — the three rows F1's step-6 re-read
  put on the shelf, five near-identical files sharing one `BridgeX` development:
  [modularCurve/TOPIC-tate-curve-twins.md](modularCurve/TOPIC-tate-curve-twins.md) and
  [modularCurve/WORKORDER-F2-tate-curve-twins.md](modularCurve/WORKORDER-F2-tate-curve-twins.md).
- The archimedean Iwasawa analytic core — the 13 `AutomorphicForm.{Complex,Real}Iwasawa` rows of
  §7's Gate 1 at the infinite place, ported as two deduped engine/façade waves:
  [automorphicForm/TOPIC-iwasawa-analytic-core.md](automorphicForm/TOPIC-iwasawa-analytic-core.md),
  its mathematics
  [../../math/028-iwasawa-decomposition-and-archimedean-estimates.md](../../math/028-iwasawa-decomposition-and-archimedean-estimates.md),
  and the orders
  [automorphicForm/WORKORDER-I1-complex-engine.md](automorphicForm/WORKORDER-I1-complex-engine.md),
  [automorphicForm/WORKORDER-I2-complex-successors.md](automorphicForm/WORKORDER-I2-complex-successors.md),
  [automorphicForm/WORKORDER-I3-real-engine.md](automorphicForm/WORKORDER-I3-real-engine.md).
- The archimedean `𝔰𝔩₂` / Casimir calculus — the other archimedean subject at the same places, and
  the one the `--include-leaves` reading prices highest after the ray-class hub: the definition
  layer, the 78-node / 33,726-line demand behind it, and the real-place `CasCore` trio that is its
  first proof set:
  [automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md),
  [automorphicForm/WORKORDER-AC1-defs.md](automorphicForm/WORKORDER-AC1-defs.md),
  [automorphicForm/WORKORDER-AC2-cascore-trio.md](automorphicForm/WORKORDER-AC2-cascore-trio.md).
- The archimedean **type-span** leaf — the `--include-leaves` demand's rank-#2 row, ported as a
  façade over the shared `Q09` engine, and its `finiteDimensional_span_translates_of_mem_archCutSubmodule`
  successor (now ready at 184 lines):
  [automorphicForm/WORKORDER-ATS-arch-type-span.md](automorphicForm/WORKORDER-ATS-arch-type-span.md),
  [logs/arch-type-span.md](../logs/arch-type-span.md). The engine's own planning note is
  [automorphicForm/TOPIC-archTestFactor-family.md](automorphicForm/TOPIC-archTestFactor-family.md).
- The **matrix-group right-finite supplement** — `U(2)`/`O(2)`, the pin's twin pair ported as one
  faithful development over a shared evaluation-combination prelude, and the pricing of the rest of
  the `Matrix.`-namespace demand in the cone:
  [deligneSerre/TOPIC-matrixgroup-rightfinite.md](deligneSerre/TOPIC-matrixgroup-rightfinite.md),
  [deligneSerre/WORKORDER-MG1-right-finite-supplement.md](deligneSerre/WORKORDER-MG1-right-finite-supplement.md),
  [deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md),
  [deligneSerre/WORKORDER-MG2-matrix-family.md](deligneSerre/WORKORDER-MG2-matrix-family.md),
  [logs/matrixgroup-rightfinite.md](../logs/matrixgroup-rightfinite.md),
  [logs/matrix-family-four.md](../logs/matrix-family-four.md).
- The **mathlib-like leaf families of the cone** — the 179 self-contained leaves that carry no FLT
  import, grouped by the frontier's own family preamble, with the free-group family priced as one
  engine + four headlines, and the preamble's one-to-three-node families split into 43 ready and 11
  blocked (nine of them one ready leaf away), plus the nine-pair wave that landed from it:
  [deligneSerre/TOPIC-ds-leaf-families.md](deligneSerre/TOPIC-ds-leaf-families.md),
  [deligneSerre/WORKORDER-MG3-ds-leaf-families.md](deligneSerre/WORKORDER-MG3-ds-leaf-families.md),
  [logs/ds-leaf-families-wave1.md](../logs/ds-leaf-families-wave1.md),
  [logs/ds-leaf-families-wave2.md](../logs/ds-leaf-families-wave2.md). The re-scoped cut that
  the criterion actually admits — 37 nodes / 3,641 lines / 7 families, all ready and gate-free — is
  [deligneSerre/TOPIC-phase3-small-supplements.md](deligneSerre/TOPIC-phase3-small-supplements.md),
  recorded but **not scheduled**.
- The **mathlib-first check for supplements, and the survey behind it** — first the habit (name /
  concept / statement `rg` over mathlib `v4.34.0`, with the three traps: trailing-name collisions, a
  more general mathlib lemma, a pin `import Mathlib` hiding the library), then the one-off study of the
  pin's 2,723 clean-import unported `S_` files (538,498 raw lines) outside the D-S cone: the subject
  families, the ten hand-read supplements with mathlib-mirroring homes and verified gaps (the 57-line
  `ValuationSubring` residue-field pair at 124 + 197 consumers is the cheapest), the FLT-flavoured
  ~135k lines that are *not* supplements, and the dedup cases:
  [TOPIC-mathlib-supplements.md](TOPIC-mathlib-supplements.md).
- The `HeckeIntegralSeam` **coset seam** — the explicit `q_v + 1`-coset decomposition of the Hecke
  double coset at a finite place, its three-module `LocalLanglands` definition gate, and the public
  engine its `_principalLevel` sibling will import:
  [automorphicForm/WORKORDER-HS1-hecke-coset-seam.md](automorphicForm/WORKORDER-HS1-hecke-coset-seam.md),
  [logs/hecke-coset-seam.md](../logs/hecke-coset-seam.md). The adelic definition layer it sits on
  is [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md) (`D3`–`D6`: `levelOne`,
  `finiteAdelicGL2Subgroup`, `heckeGen`, `localEmbed`, `finEmbed`).
- The `Place` **separating-uniformiser twin** — a uniformiser (or a tame-order element) is a
  separating element, the ready pair ported as two headlines over the promoted Frobenius-subfield
  engine, with the criterion *called* rather than re-proved:
  [algebraicCurve/WORKORDER-SU1-separable-uniformiser.md](algebraicCurve/WORKORDER-SU1-separable-uniformiser.md),
  [logs/separating-uniformiser.md](../logs/separating-uniformiser.md). Its AC neighbours are
  [algebraicCurve/TOPIC-t1-ord-interface.md](algebraicCurve/TOPIC-t1-ord-interface.md) (the `ord`
  interface it is stated over) and
  [algebraicCurve/TOPIC-t9-transcendence.md](algebraicCurve/TOPIC-t9-transcendence.md) (its two
  premises).

## 1. What the port contains

The port holds the column's unconditional half, the `ModularCurve` q-expansion, function-field and
Frobenius layers, the analytic and period layer, the Tate-slots definition and weight-4 layers, and
the definition and hub ground the rest builds on. The dated records are in `../logs/` and, for the
`ModularCurve` sets, in the work order that produced them.

**The unconditional slice.** Everything that does not depend on the two automorphic gates — the
weight-one mod-`ℓ` lifting half and the assembly half. It takes the residual family as a
hypothesis, so it is stated without the ray-class input and without the automorphic layer; the
two gates attach to a fixed interface and can be ported later without reworking it. The consumer
wire test is `spec/DeligneSerreConsumer.lean`; the record is
[../logs/deligne-serre-port.md](../logs/deligne-serre-port.md) and the friction/promotion ledger
is [../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

**The coset-space Petersson layer, and the level-prime eigenvalue.** The definition layer
`ModularForms/Analytic/PeterssonCoset.lean` — `Nice`, the raw pairing `pair`, the slash
transfer and the relative-index machinery, 56 declarations, checker +56 — and the silo
`ModularForms/Analytic/NormSqPow.lean`, the level-prime bound `‖a‖² = ℓ^(k-1)` for a form new at
`ℓ`, 72 declarations, checker +72; the 18 statement-identical declarations the pin wrote twice
were moved out of the `PeterssonHecke` engine into the definition layer. Record:
[deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md](deligneSerre/TOPIC-petersson-coset-and-level-prime-eigenvalue.md),
order: [deligneSerre/WORKORDER-P2-normsq.md](deligneSerre/WORKORDER-P2-normsq.md).

**The `ModularCurve` q-expansion layer.** The Γ₀-rationality pair, the `X_H` relative-degree
bound, the JOneES finrank/index and residue-field rows, the Deuring-reduction /
constant-extension / Atkin–Lehner successors, and the `isAlgClosed` finrank bound, in
`functionFieldGeneration/SET-R-*`, `X1/*`, `XH/*` and `WeightOne/*`. The planning records are the
`TOPIC-qexp-*` notes.

**The `X_H`/`X₁` function field and Frobenius.** The `q`-expansion Frobenius inputs headline
`qExpFrobeniusInputsModL_and_finrankAlong_of_transcendental`, appended to
`ModularCurve/Frobenius/QExpModL.lean` — the module already held its private machinery and its
`Fr* Fr_* = ℓ` sibling, so the append needed no new file and no promotion. The ten landed leaf
rows (`qExpansion_div_mem_laurentBaseChange_xHFunctionField`,
`isIntegral_jqNModC_of_modularPolynomialData`, `exists_gamma0_qExpansion_div_eq_jqNModC`,
`eisenstein4_cube_sub_mk_sq`, `diffQExp_x1FunctionFieldBar_injective`,
`modularFunctionFieldC_eq_modularFunctionFieldFullC_of_charZero`,
`modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0`, `closure_elemSet_eq_top`,
`isCurveOver_x1FunctionFieldBar`, `essFiniteType_x1FunctionFieldBar`) sit in
`ModularCurve/X1/{QExpansionDiv,IntegralityJqNModC,Structure,FunctionFieldInclusion}.lean`, on the
definition modules `ModularCurve/Defs/{HeckeDifferential,SL2Elementary}.lean`,
`ModularCurve/X0/FunctionFieldFull.lean` and `AlgebraicCurve/Differential/PushPull.lean`, each
ported whole. The eleventh row is deferred (§7). Record:
[modularCurve/WORKORDER-C2-x1-function-field.md](modularCurve/WORKORDER-C2-x1-function-field.md).

**The analytic and period layer.** The pin's four `Def_AutomorphicForm_*` modules whole —
hyperbolic measure, fundamental-domain volume, the Siegel set cover and the Γ₀ fundamental set, in
`AutomorphicForm/`, keeping the pin's `FLT.*` namespaces — and the Petersson pairing
`ModularCurve/Analytic/PeterssonPairing.lean`, whose two headlines make the period pairing
perfect. The period map of a finite-index subgroup is
`ModularCurve/Period/{PeriodLatticeSpan,PeriodLatticeBoundary,ParabolicHoms,QExpansionDerivative}.lean`,
and the pin's `Def_ModularCurve_QExpansionDiff.lean` node is whole across
`Period/QExpansionDiff.lean` and `AlgebraicCurve/Differential/TraceDiff.lean`. Records:
[modularCurve/WORKORDER-D1-petersson.md](modularCurve/WORKORDER-D1-petersson.md),
[modularCurve/WORKORDER-D2-period-map.md](modularCurve/WORKORDER-D2-period-map.md).

**The level-`N` function field and the `Φ_N` rows.** `ModularCurve/LevelN/FunctionField.lean` is
the pin's 53-line definition module whole (`wp`, `fricke`, `jAnalytic`, `generators`, `ring`,
`jGen` and the membership lemmas), and `LevelN/{Prelude,FieldGalois,Places}.lean` hold the eight
rows — `isDomain_ring`, `slash_eq_self_of_mem_Gamma_of_mul_eq`,
`exists_monoidHom_algEquiv_fixedField_eq_adjoin`, `exists_algHom_laurentSeries_qExpansion`,
`exists_place_ord_neg_forall_smul_eq`, `exists_place_ord_sub_pos_forall_smul_eq`,
`exists_place_analyticOrderAt_eq_mul_ord`, `valuation_apply_smul_le_one_of_tendsto_div_smul`. The
six `Φ_N` rows sit in
`ModularCurve/ModularPolynomial{LeadingCoeff,UniquenessIrreducible,StarBank,FibreTwo}.lean`, on the
wave's `Defs/{ClassicalModularPolynomials,FibrePoly}.lean` (`phiTwo`/`phiThree`/`intFibre`, the
public `fibrePoly`, the `ReduceModBivar` block), and the level-`N` `q`-expansion bridge is the
deduped twin development in `ModularCurve/LevelN/QExpBridge.lean`. Records:
[modularCurve/WORKORDER-A-levelN-field.md](modularCurve/WORKORDER-A-levelN-field.md),
[modularCurve/WORKORDER-B1-phi-rows.md](modularCurve/WORKORDER-B1-phi-rows.md),
[modularCurve/WORKORDER-B2-fibre-two.md](modularCurve/WORKORDER-B2-fibre-two.md),
[modularCurve/WORKORDER-E-levelN-qexp-bridge.md](modularCurve/WORKORDER-E-levelN-qexp-bridge.md).

**The `WeierstrassCurve` layer.** The whole good-reduction definition chain —
`WeierstrassCurve/Reduction/{Point,TorsionIntegral,ReduceHom,ZeroComponent}.lean`, the pin's four
`Def_*` modules ported whole — and the eight ready-shelf nodes it gated: the exceptional
automorphisms in characteristics 2 and 3, full level structure and the division field, reduction
surjectivity on the prime-to-`p` torsion, the inertia-equivariant reduction, and the
Vélu-quotient `j`-map. Its scoping and set orders are
[deligneSerre/TOPIC-weierstrass-ready-shelf.md](deligneSerre/TOPIC-weierstrass-ready-shelf.md).

**The `TateFormal`/`TateSlots` definition layer.** The two pin `Definitions/` modules the
weight-4 slot cluster's fourteen `S_ModularCurve_*` leaves all import, ported whole (playbook
§2.3) at `ModularCurve/Defs/TateFormal.lean` (26 declarations — `tateB`, `tateA4`/`tateA6`,
`eisenstein6`, the `tatePowerSeries`/`tateLaurent` curves with their ellipticity instances, and
`laurentOfInt`) and `ModularCurve/Defs/TateSlots.lean` (37 declarations — `tateUnivX`/`tateUnivY`,
`slotFamily`/`slotSubst`, `tateBase`, the non-toric/toric and Vélu slot sets). The pin's
downstream consumers (`Def_ModularCurve_TatePoint`, `…_TateVeluRing`, `…_TateOrigin`,
`…_ShimuraGenerator`, `Theorems/Thm_ModularCurve_Delta_tatePowerSeries`) name the same
declarations, so the whole node is homed rather than only the block the `S_` files reach. Neither
pin module has a `Theorems/` wrapper, so both verify by name against their `Definitions/` files;
neither has a `private` declaration, so no promotion is owed. Both are appended last to
`SOURCES` / `PORT_FILES`.

**The weight-4 Tate-slot engine and headline façade.** The fourteen `S_ModularCurve_*` leaves the
frontier's `--include-leaves` view showed at ~1650 lines are one 1,671-net-line development written
fourteen times (23,094 raw lines, 112 shared names, ≈20,810 removable); it is ported once as the
tier-3 engine `ModularCurve/TateSlots/{Convergence,SlotCoeff}.lean` (537 + 1,293 lines, 38 + 81
public declarations, declaration parity exact, no build-time blow-up) and the fourteen public
headlines in the tier-1 façade `ModularCurve/TateSlots/CoefficientFormulas.lean`. The engine's fourteeen
kernels are public as `ModularCurve.TateSlots.<name>` with the pin `Theorems/` wrapper binders;
the façade states the wrappers verbatim. The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md); the façade is the checker wire (delta +14).
No existing module was edited. Mathematics, measurement and structure:
[modularCurve/TOPIC-tate-slots-weight-four.md](modularCurve/TOPIC-tate-slots-weight-four.md); the
order and its results:
[modularCurve/WORKORDER-F1-tate-slots-engine.md](modularCurve/WORKORDER-F1-tate-slots-engine.md).

**The `tateCurve` `BridgeX` layer and its definition chain.** The three `tateCurve` rows F1's
step-6 re-read put on the shelf are a **twin pair and a triplet** — five near-identical pin `S_`
files sharing one 1,338-line `ModularCurve.BridgeX` development (47 declarations in all five, 23
more in the pair only, 5 headlines). Ported once as the tier-3 engine
`ModularCurve/TateCurve/{Bridge,Slot}.lean` (839 + 674 lines, 50 + 25 public declarations, no
build-time blow-up), with the five public headlines in the tier-1 façade
`ModularCurve/TateCurve/QPow.lean`. Its six unported `Definitions/` modules are homed whole at
`Algebra/LaurentSeriesXAdic.lean`, `TateCurve/{QSeries,PointSeries}.lean`,
`ModularForms/KatzLevelOne.lean` and `ModularCurve/Defs/{KatzLevelP,KatzLevelPCusps}.lean` (217
declarations, checker +217). The engine stays tier 3 and is recorded in
[spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md). Mathematics and structure:
[modularCurve/TOPIC-tate-curve-twins.md](modularCurve/TOPIC-tate-curve-twins.md); the order and its
results:
[modularCurve/WORKORDER-F2-tate-curve-twins.md](modularCurve/WORKORDER-F2-tate-curve-twins.md).

**The archimedean Iwasawa analytic core.** The two gates of §7 take their input at the infinite
place from 13 `AutomorphicForm.{Complex,Real}Iwasawa` rows — the decomposition's compact factor and
the Fourier decay of its radial length. They are ported as the pre-gate wave the gates attach to:
the pin `Def_AutomorphicForm_ComplexIwasawa` (4 declarations) and the shared generic Fourier bound
(`M4aP3B.FourierDecay`, 2 declarations) homed as the definition layer, seven tier-3 engines
(`AutomorphicForm/Iwasawa/{Complex,Real}/{Core,Decay,UniformDecay,Continuation}.lean`, 5,818 lines)
holding the deduped development (10,378 raw `S_` lines → 5,256 net), and the two subject façades
`AutomorphicForm/Iwasawa/{Complex,Real}/Estimates.lean` (13 headlines) as the checker wire. Checker
9654 → 9673, 0 mismatched / 0 missing; the cone's `needed` falls 1,617 → 1,604 nodes and no Iwasawa
row remains in the demand. Topic, mathematics and orders: the companion bullet above.

**The centre-cut pair.** The vanishing leaf
`AutomorphicForm.eq_zero_of_isAutomorphicFnAt_of_continuous_of_nonpos_of_lt_of_coversModCentre`
rules out a continuous automorphic function supported on a centre-cut Siegel cover: if
`c ≤ 0 < d₁ < d₂` and the finite union of translates of `centreCutSiegelSet F c u d₁ d₂` covers
the centre, then `φ = 0`. Its sibling
`AutomorphicForm.not_isArithGenuineCuspRealizable_of_nonpos_of_lt_of_coversModCentre` rules out an
arithmetic genuine cuspidal realization on the same cover. The two pin `S_` files share a
645-line / 47-declaration block byte-for-byte; it is ported once as the tier-3 engine
`AutomorphicForm/Adelic/Cusp/CentreCutEngine.lean` (964 lines, 49 public declarations, each with
`-- pin:` provenance), and the two façades `CentreCutVanishing.lean` (64 lines) and
`CuspUnrealizable.lean` (59 lines) hold one headline each. The first pass's 902-line module was
reduced when the sibling was cut; the engine's general `no_function_of_ne_zero` serves both
headlines, so the sibling's pin-specific `no_realization_of_ne_zero` is not ported. Checker
**10239 identical** (one headline each, +1 per leaf). Records:
[logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md); orders:
[automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md](automorphicForm/WORKORDER-CMV-centre-cut-vanishing.md),
[automorphicForm/WORKORDER-CCS-centre-cut-sibling.md](automorphicForm/WORKORDER-CCS-centre-cut-sibling.md).

**The centre-cut fundamental-domain trio.** The next ready rows were the automorphy-transfer node
`AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre`
(325 pin lines) and the two twins
`AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_{integralWindowed,centreCut}SiegelSet_of_coversModCentre`
(267/266). They need the same fundamental-domain/slab prelude that `PeterssonSlabPairing.lean`
already carried `private`; the prelude was promoted once there (20 declarations, plus the 107-line
`exists_measurableSet_isFundamentalDomain_subset` and the 36/23-line `setLIntegral_fd_le_sum_mul` /
`cover_of_forall`), and the façades `Adelic/DetNormSlab.lean` and
`Adelic/MeasurableFundamentalDomainCover.lean` hold the three headlines. Checker **10263
identical** (+3 headlines, +21 promoted prelude declarations). The fourth `--ready` row, the
234-line `CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample`, is **not
actually ready**: it needs the unported 288-line
`Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`, recorded in
[CARRY-FORWARD.md](../CARRY-FORWARD.md). Record:
[logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md); order:
[automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md](automorphicForm/WORKORDER-CCF-centre-cut-fundamental-domain.md).

**The complex archimedean Casimir layer.** Set B of the arch-Casimir subject was blocked on two
unported pin `Definitions/` modules: `Def_AutomorphicForm_ArchDerivCasimirComplex` (196 lines / 32
declarations) and `…ComplexAPI` (381 / 46). Both were homed whole at
`AutomorphicForm/Adelic/ArchDerivCasimirComplex.lean` and `…ComplexAPI.lean` (checker +78), and the
first complex headline
`AutomorphicForm.archCasimirAtComplex_rightTranslate_archComplexGLAt` was ported as the 857-line
engine `AutomorphicForm/Adelic/ArchCasimirComplex.lean` (96 public declarations, tier 3,
registered; +1 headline). The engine is the complex mirror of the real `ArchCasimir.lean`: the
types are `ℂ` rather than `ℝ`, and the complex half adds the holomorphic/anti-holomorphic Del
operators, the conjugate transport and the second Casimir. `port_advise` reports 0 substitutions
and 43 binder-spelling variants; a normalized comparison is only ≈0.38 similar, so the
architectural duplication did not justify a generic `RCLike` rewrite of the landed real engine.
The remaining complex headlines are `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex`
(1,227) and `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne` (133), then the 35-file
complex fan. Records:
[logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md); order:
[automorphicForm/WORKORDER-ACC-arch-casimir-complex.md](automorphicForm/WORKORDER-ACC-arch-casimir-complex.md).

**The Poisson-summation pair then closed the `ZLattice` deferral** (§9's last parked item): the
563-line `SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace` and the two `ZLattice` headlines (229 +
221 pin lines) as `FLTForHuman/Analysis/Fourier/PoissonSummationPi.lean` (613 lines, **31 wired + 7
`own:`**) and `PoissonSummationZLattice.lean` (293 lines, **2 wired**). The 429 s the pair was
deferred on was exactly three declarations blowing the diagnostic **in their statements**: a locally
bound `hf` — "every lattice translate is summable in sup-norm on every compact", written inline in
all six `PeriodizeLift` declarations — made `isDefEq` unfold the norm on a restricted
`ContinuousMap` (`ContinuousMap.instNorm = dist x 0`, `sInf`, `Finset.sum`); naming that type
`LocSum` removed the unfolding, and the module now builds in **5.5 s** (3,189 jobs), 0 warnings, the
sibling in 5.4 s (3,202 jobs). This is the column's first **registered deviation set**: 7 `own:`
rows in `spec/decl_markers.tsv` (the six binders and `LocSum`; the statements stay defeq to the
pin's). Checker **2,851 → 2,884 ok, 107 → 109 wired modules, 4 → 11 own**, 0 mismatched / 0
missing; both headlines' axioms are `[propext, Classical.choice, Quot.sound]`. The second module had
never been elaborated and carried two hard name errors (a bare `open PiPoissonSummation`, the engine
lives under `P2MW.S_….PiPoissonSummation`, and one qualified helper use) — fixed; its head is a
proof just over 20k. Record:
[logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md).

**The `Representation` family then closed whole** — six ready nodes / 2,351 raw pin lines, cut by size
and subject as the family note's §7.5 priced it. The five small mathlib-shaped leaves landed as five
mathlib-mirrored modules
(`RepresentationTheory/{Burnside,InvariantPairing,CompactGroup,SubrepresentationExtension}.lean`,
`LinearAlgebra/Matrix/SubfieldBasis.lean`; 21 wired), and the 1,692-line descent development as three
`GaloisRep/Deformation/` modules (`Charpoly`, `Cocycle`, `FiniteDescent`; 103 wired) — **eight modules,
2,893 port lines, 124 checked declarations**, 0 mismatch / 0 missing / 0 own, 0 warnings, axioms
`[propext, Classical.choice, Quot.sound]` (the `InvariantPairing` headline a subset without
`Classical`). The mathlib-first audit recorded a negative for every declaration, with mathlib supplying
ingredients only (`Matrix.map_injective`, Schur, Jacobson density, Haar averaging, `toMatrix`/trace
dictionary, the `FiniteField` Frobenius/norm API); two helpers in `RepresentationTheory/BrauerNesbitt.lean`
were promoted for the Burnside module and now diff through the pin-private fallback (+2 ok, no `own:`).
The family is complete: checker **2,884 → 3,010 ok, 109 → 117 wired modules**. Records:
[logs/representation-leaves.md](../logs/representation-leaves.md),
[logs/descent-charpoly.md](../logs/descent-charpoly.md); orders:
[WORKORDER-R2-representation-leaves.md](deligneSerre/WORKORDER-R2-representation-leaves.md),
[WORKORDER-R1-descent-charpoly.md](deligneSerre/WORKORDER-R1-descent-charpoly.md).

**The shared ground that edits existing modules.** The `ValuationSubring` residue block in
`NumberTheory/ValuationAtPlace.lean`; the `Gamma0Integral` promotion and its duplicate-block
collapse; the resolution of the `normFormulaAlong_of_elliptic` co-import collision (one public
copy; the character-free copy is named `normFormulaAlong_of_elliptic_cf`); the C1 append into
`ModularCurve/Frobenius/QExpModL.lean` — the one landing that edits a module rather than adds
one; and the wave that homed the shelf's definition layer, which also deduped `fibrePoly` out of
`Degree/PhiData.lean` into `Defs/FibrePoly.lean` at its public pin name. Registered in
[CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 2. The frontier

```bash
cd tools/deps
# the canonical D-S cone read: --ds excludes the prunable complex-analytic subject
# (deligneSerre/PRUNABLE-complex-analytic.md) and --include-leaves shows the demand's
# graph leaves, which --ready and --hops drop
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
python3 frontier.py --ds --rank-by silo --ready --top 0   # the ready shelf alone
```

The table below is the **default** (unexcluded, `union`) reading, kept for reference;
the `--ds` commands above are the ones to use for "what is left".

| quantity | value |
|---|---:|
| target closure | 2,308 nodes / 1,089,430 raw `S_` lines |
| frontier `F` (union) | 901 nodes / 517,169 |
| `F` inside the cone | 660 nodes / 412,941 |
| `needed` (unported demand, `F` terminal) | 1,635 nodes / 673,014 |
| `needed` (literal closure-minus-ported) | 1,648 nodes / 676,489 |
| **ready to port** (all premises available) | **67 nodes** |

The ready shelf by top-level namespace: `AlgebraicCurve` 24, `ModularCurve` 13, `CuspForm` 8,
`NumberField` 5, `AutomorphicForm` 4, `ModularForm` 3, `PeriodPair` 2, `LanglandsTunnell` 2,
`CohCarrier` 2, `EisensteinGeneral` 2, `CuspFormClass` 2. `WeierstrassCurve` no longer appears —
all eight shelf nodes are ported. The `ModularCurve` part is **13 nodes**, the column's own shelf:

| node | silo lines |
|---|---:|
| `ModularCurve.tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst` | 1,343 |
| `ModularCurve.tateCurve_pointY_C_mul_X_pow_eq_nonToricPoint_snd` | 1,343 |
| `ModularCurve.phiIrreducible_all` | 434 |
| `ModularCurve.exists_exp_eq_of_invariant_ne_zero_isParabolicHom` | 410 |
| `ModularCurve.SerreImage.contains_SL2` | 390 |
| `ModularCurve.qTwist_nonToricPoint_of_pow_eq_one` | 185 |
| `ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand` | 165 |
| `ModularCurve.j_tateLaurent` | 144 |
| `ModularCurve.exists_modularForm_mul_qExpansion_eq_coeffEmb_qExpand_jq` | 102 |
| `ModularCurve.ModularPolynomialData.natDegree_coeff_le` | 62 |
| `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` (mispriced, §7) | 36 |
| `ModularCurve.hasCanonicalDivisor_x1FunctionFieldBar` | 22 |
| `ModularCurve.ModularPolynomialData.isUnit_leadingCoeff_diag` | 14 |

**The step-6 effect of the last landing.** WORKORDER-F1's engine and façade took the fourteen
~1650-line leaves off the demand and put **three successors** on the shelf, all reading the
slot-substitution engine it homed: the two `tateCurve_…_nonToricPoint_…` rows at 1,343 silo lines
each and `qTwist_nonToricPoint_of_pow_eq_one` (185). The first two are the largest `ModularCurve`
rows and the natural next cut; `phiIrreducible_all` (434) remains the standing candidate behind
them. The other ten rows predate the Tate-slot round. The `CuspForm`,
`PeriodPair`, `ModularForm` and `CohCarrier` rows are reached by the target closure but are not
`ModularCurve` rows, and are not this column's to cut; the `NumberField.TateGlobal` rows are cut
through their own topic notes (the `continuous_ideleNorm` hub and, now, the continuous norm
section — §1), and their remaining shelf rows are the two
`exists_norm_apply_eq_ideleNorm_rpow` cousins (§7).

**The `AlgebraicCurve` rows are now being cut too**, through their own AC-homed notes: the
`localParam` family's first leaf, `AlgebraicCurve.Place.exists_finset_forall_exists_localParam_eq_complex`,
landed on 2026-10-19 (§1) and the rest of the family followed the same day — the branch
uniqueness, the local parameter with its meromorphic-order dictionary, and the four leaves those
rest on — so the charted-space capstone
`Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` (1,576 silo lines) now lacks
only its own assembly, with `Place.exists_forall_ord_eq_finset` (291) ready beside it. The `--ds` ready shelf itself read
**85 candidates** at that landing (the 67 in §7 predates four other columns' landings). The
`Place` **separability pair** followed on 2026-10-20 (§1): a uniformiser is a separating element,
and so is an element of nonzero tame order — one module, two headlines, over a three-declaration
promotion in the Frobenius-subfield engine; it put the `ordDiff` rows on the ready shelf (§7).

**The demand's leaves are the other shelf, and its rank-#2 row has landed.** `--ready` and `--hops`
drop graph leaves (a leaf has `needed == 1` and can never reach `F`), so the automorphic demand's
biggest self-contained rows appear only under `--include-leaves` or in a direct query. The
archimedean type-span leaf
`AutomorphicForm.CuspidalConstituent.finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`
— 813 silo lines, `used_by` 3 cone / 9 project — was rank #2 there behind the ray-class hub and
landed 2026-10-20 (§1, WORKORDER-ATS); the leaf shelf drops 445 → **444** candidates and its head
moves to `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRep_heckeGen` (807). The leaf's own
successor `AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule` (184) is now
on the `--ready` shelf — the same principle at the whole cut, and the next cut of the family.

**The leaf shelf's next two rows were the `Matrix.` pair, and they have landed** (§1, WORKORDER-MG1):
the shelf reads **442 → 440** and loses 1,550 raw lines, and the `Matrix.`-namespace demand goes
**11 nodes / 4,519 lines → 9 / 2,969**. The family's remainder is priced together in
[deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md) — four
ready leaves (970 net new, +73, WORKORDER-MG2), the
`GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` row
(1,242) behind its own `ModularCurve.SerreImage.contains_SL2` premise (390), and four
`Matrix.SpecialLinearGroup` free-group rows that are **not ready** (686 own lines behind 3,275 raw
lines of `Monoid.CoprodI` / `SimpleGraph` / `Subgroup` premises) and are another column's subject.

**The two `tateCurve_…_nonToricPoint_…` rows are exact twins, and must be cut as one.**
`S_ModularCurve_tateCurve_pointX_C_mul_X_pow_eq_nonToricPoint_fst.lean` and its `_pointY_…_snd`
sibling are both 1,343 lines and differ by **8 diff lines**; normalized at the namespace stem, the
only difference is the final `solution` — `… = (nonToricPoint F p c j).1 := BridgeX.pointX_slot …`
against `… = (nonToricPoint F p c j).2 := BridgeX.pointY_slot …`. The 69 other declarations
(1,311 lines) are byte-identical at the same line numbers. `port_plan` reads 2,686 raw → **1,325
net new** / 72 groups, 0 substitutions. The order is the WORKORDER-E shape: write the shared
development once (`private`) and derive both public headlines from the two `BridgeX` conjuncts;
the checker delta is exactly +2.

**The readings differ, and the conservative one is the one to plan from.** The table above is the
default `union` name scan. `--frontier sources` (no name scan) gives `F` 837 nodes / 519,647, a
`needed` of 1,438 nodes / 542,136, and 85 ready candidates (2026-10-19; the 756 / 1,704 / 61 this
note carried predate four columns' landings). Both readings now count a module wired by its own
`spec-pin:` header as ported — `frontier.py` reads those headers into the `sources` tier — so the
new wire's handoff does not drop a landing out of the conservative reading. The gap is the last-name blindness of
§9: a pin node whose last name matches a ported declaration of another namespace is priced as
ported. `port_advise` and `port_plan` never walk imports either, so an unported premise outside
the target files is invisible to them; both frontier readings stay in the loop.

**One ready row is mispriced.** `ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1` is
listed at 36 silo lines, but its premise
`ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast` is unported and the `CuspForm` twin
cannot substitute — so it is a whole node, deferred to its own order (§7, §9). Under
`--frontier sources` the same query prices it at 10 needed nodes / 5,172 raw `S_` lines.

**A prunable subject sits on this shelf and is not this column's.** The complex-analytic
Jacobian / path-integral / Abel–Jacobi / `CellDissection` subject is in the target *closure*
(44 nodes / 30,570 lines on 2026-10-14) but is a second supply to a step the D-S route already
reaches by the differentials ↔ cusp-forms transport, so it is prunable — 205 nodes / 107,257
lines, a 186-node / 91,105-line saving on that tree. Read the frontier with it excluded —
`frontier.py --ds` is the one-flag form ([deligneSerre/PRUNABLE-complex-analytic.md](deligneSerre/PRUNABLE-complex-analytic.md),
`tools/deps/ds_prunable.py`) — or its leaves read as D-S work; its plan is RR phase 3
([algebraicCurve/TOPIC-cell-dissection.md](algebraicCurve/TOPIC-cell-dissection.md)).

**Not schedulable from this list.** The two gates of §7 remain in the unported demand but are not
ready; they must not be scheduled off a ready shelf.

## 3. The workflow

This is the loop the column runs. Steps 1–4 are the manager's; step 5 is the subagents'; step 6
closes.

**1. Read the frontier.** The canonical command above is `--ds --include-leaves` (`--ds` excludes
the prunable complex-analytic subject, `--include-leaves` surfaces the demand's graph leaves);
`--ready` narrows to the nodes whose whole demand is
themselves — every premise is already ported, so only the node's own proof is missing — and
`--rank-by silo` orders them by the raw `S_` lines of their **whole demand**, i.e. by how much
mathematics stands behind them, not by the size of their own file. This is demand, and it is the
only list to plan from. The `hops`/`used_by` columns choose *within* a cluster; they do not choose
the cluster. `--include-leaves` additionally surfaces the demand's graph leaves (no premises, so
they never reach `F`); that view prices a leaf at its whole file, so a cluster of near-identical
leaves — the Tate-slot fourteen were one — must be deduped by `port_advise` before it is believed.

**2. Cut a cluster by mathematics.** 3–6 ready nodes that tell one story in one layer — the
level-`N` place/valuation cluster, the `AlgebraicCurve` curve-and-divisor cluster, the `CuspForm`
Nebentypus cluster. Namespace and pin file are *not* the cut: one namespace can span several
layers, which is why the q-expansion head ran as several sets. The test is whether one sentence
states the cluster's subject without an "and".

**3. Scope the cluster with the tools.**

* `port_advise.py --target <node> … --json build/<cluster>_advise.json` — the substitution table
  (declarations the port already has: import, never re-prove), the port-`private` rows (promote or
  re-derive), the **shared blocks** the target files have in common (the dedup: write once), the
  near-duplicate / binder-only rows, and the *suspect* type-only `def` matches the parser cannot
  judge (read both copies before applying any). **Read the substitution table by shape, not by
  text**: it reports two tiers — the checker's byte-identical tier, and the *shape* tier (same
  conclusion, same hypothesis list, once section variables, instance arguments and bound names are
  normalised). The shape tier is the reuse answer: the pin writes one lemma many ways
  (`mem_of_ord_nonneg` occurs in 33 distinct texts across 263 files), and the port's copies were
  homed from the `Theorems/` wrappers, so a byte scan under-reports systematically. Its `residue`
  list names the few the shape tier cannot settle (one side keeps the variable in a file-level
  `variable`); read those two texts. A *restated* lemma must still use the pin's own text shape, or
  `check_port.py` reports a `MISMATCH` — importing is the normal move.
* `port_plan.py --json …` — the budget: raw lines, once-only dedup, boilerplate, **net new math
  lines**, declaration groups.
* `build_ladder.py --edit <host>` on **every** candidate host — the cascade each edit will force,
  in modules and lines.
* **Hand-check the import list.** `--ready` and `--with-defs` do not see import-only definitions:
  every `Definitions/Def_*.lean` a target `S_` file imports must be checked by hand against the
  port, declaration by declaration, and the target's proof's own definition uses checked too
  (`fltdata.proof_defs`) — a stub import can hide a live dependency. See §4(a).

**4. The manager does the shared ground — this is the point of the split.** Before any subagent
runs:

* **(a) the definition layer, whole node.** Home the pin `Def_*` module the cluster imports **in
  full** — every declaration with a consumer, not only the block the cluster reaches (playbook
  §2.3) — at the natural *theory* home rather than a new `Def_`-named file; promote out of
  `private` whatever the cluster must name. Checked against the pin; a new module is wired by its
  own `spec-pin:` header (§6) and **not** by an entry in the frozen `SOURCES`/`PORT_FILES`.
* **(b) promotions and every other hub edit.** Any edit to an existing module is the manager's,
  not a subagent's: it is the only thing that re-elaborates the cone, so it is done once,
  deliberately, with the price known.
* **(c) dedup the scoping turned up.** A hub that carries the same private block twice, a copy
  that a promotion makes redundant — fold it into the same pass, because the wave is already
  being paid and deferring it pays nothing.

Each such edit is priced, applied, built at tier 1, checker-run, and followed by **one** wave
build; then the touched files freeze and no subagent may edit them.

**5. Divide into sets; dispatch and review in series.** One set = one mathematical story = one
module or a small group = one subagent = one work order. Sets run **one at a time**: parallel
`lake build`s contend on Lake's lock and cross-invalidate, so the second one looks like a blow-up
and both are slower. The one safe overlap is two sets with no shared prelude and disjoint
namespaces: they may write their modules in parallel if the shared checker wiring stays with the
manager and every build is serialized; the review order is still one set at a time. The manager
writes the work order, dispatches, and then reviews the tree *itself* before writing the next
order.

*Work-order template* (playbook §3.3): scope and what is explicitly not this set; pin sources
(`Theorems/` wrapper for the statement, `P2M/Sol/S_` for the proof); deliverable modules and the
public/`private` split; what is already in the port and must be reused; route with recorded
negatives; risks; the build-discipline block verbatim; the stop conditions; the report shape.
Every order carries the **hub prohibition**: a subagent that needs a `private` helper re-derives
it locally and reports it; one that believes a promotion is genuinely required **stops and
reports** with the declaration, host and `build_ladder.py --edit` price. The manager decides.

*Review checklist* after each set: `spec/check_port.py --force` on the set's modules with **0
mismatched / 0 missing** and every public declaration accounted for (matched, or recorded in
`spec/decl_markers.tsv` as a `pin:`/`own:` entry) — no in-source per-declaration marker is added;
`--all` (or `--changed`) green over the whole wired surface, whose counts are the progress metric;
tier 1 green and 0 warnings; no `sorry`/`admit`, no bare `import Mathlib`; `#print axioms` on
every headline `[propext, Classical.choice, Quot.sound]`; `git status` showing only the set's
files. `spec/old_check_stmts.py` is the frozen registry, not run as a gate and never appended to
(§6). The checker is cache-aware and `--force` re-checks one module from scratch, which is the
per-set gate. The statement instrument itself — `norm`, the declaration regex, the hash — is
shared with `spec/old_check_stmts.py`, so its mutation sensitivity is still exercised by
`python3 spec/old_check_stmts.py --selftest` when that parser changes, not per set.

**6. Close out, then re-read the frontier.** Re-run step 1: the landed nodes leave the shelf and
their successors appear. Record the outcome in the work order and in the cluster's topic, name
the successors the landing unblocked, and cut the next cluster.

## 4. The shared ground

**(a) Definitions first, whole node, and check them by hand.** Nothing can be *stated* before the
pin `Def_*` modules the cluster imports exist in the port. They are leaves — cheap to build, no
cascade — and they are invisible to `frontier.py`'s readiness test, so the list is built by
reading each target `S_` file's `import` block and walking its `Definitions/Def_*.lean`
declarations against the port. **Home the whole module** (playbook §2.3): the closure the
cluster's proof reaches is the floor and the order, not the scope — the rest has consumers
elsewhere and `frontier.py` prices by file. A declaration with no consumer anywhere is the only
exclusion, and it needs a `grep -c` (excluding the pin's global `attribute [-simp]` preludes and
`p2m_export` rows) to justify. The partial-port failure this guards against is on the record:
`Def_ModularCurve_QExpansionDiff.lean` had its `thetaL` half ported against a set's needs while its
`QExpansionDiff` and `TraceDiff` halves, with no consumer in that set but pin consumers elsewhere,
were not — and `port_advise`'s per-target view did not show it.

**(b) `private` is a build tool, not a statement about mathematics.** A helper stays `private`
when it only adapts another theory, or is generic glue a consumer can re-derive in a few lines; it
is promoted when it carries mathematics another theory will state or reuse. A promoted
pin-`private` helper is renamed at the pin's name, and the checker verifies it through its
dotted-name fallback. The counterexample to avoid: a "promotion" of a declaration whose pin
statement is not the port's — the parser's type-only `def` matches are exactly this.

**(c) A hub edit is a wave, and the wave is the same price whether or not you also clean up in
it.** So: price it, do all of it at once, and only then freeze. A subagent never opens the
question; it reports and stops.

## 5. The build economy

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>` — the
  cap is **low on purpose**: a declaration that exceeds it has an instance-inference defect, and
  the low cap is what finds it. Diagnose it (`set_option diagnostics true` /
  `trace.Meta.synthInstance true` on that one declaration, in a scratch copy), fix the inference,
  re-run. Never raise `maxHeartbeats`, never add a module `set_option maxHeartbeats`. The edit loop
  writes no `.olean` and builds no dependent;
* **to isolate a slow declaration, never re-elaborate a file.** The quick recipe, in order of
  preference: (i) `import` the module that already owns the declaration (its olean is the prelude) and
  restate only the target, proof pasted — the probe then costs that proof alone; (ii) in a scratch copy,
  stub the prelude with `sorry` (keep the statements, replace the proofs) and elaborate the one target;
  (iii) cut at *section* boundaries only, deleting a whole section's proofs rather than truncating the
  file — a truncated file fails to elaborate at all, which burns a long run and answers nothing. Every
  probe is a ≤ 60 s turn; if a probe cannot finish in that, the probe is wrong, not the file. One long
  *profiled* run per module is the sanctioned exception — `set_option profiler true` at the library cap
  gives the per-declaration split (elaboration vs typeclass inference vs tactics) and the module's total,
  once, after which the isolation above takes over;
* **a timeout is not automatically a slow proof.** Stub the suspect declaration's *proof* with `sorry`
  and re-probe at the low cap: if the statement still times out, the cost is a term in the type, and
  no proof-level change (pinning a search argument, a local `letI`, a reshaped tactic block) can move
  it. First instance: the now-landed `ZLattice` pair's three `PeriodizeLift` declarations, each far
  over the 200k diagnostic (one alone still timed out at 1M) — all of it the argument check of a
  hypothesis whose type contains the norm on a restricted `ContinuousMap` (`isDefEq` unfolds `dist x 0`
  and its `BoundedContinuousFunction` machinery); naming that hypothesis type once brought the whole
  614-line module to ~6 s at 20k hearts and a 5.5 s build. The fix was a name, not a pinned instance —
  full bisection, mechanism and the 7 registered `own:` rows:
  [logs/poisson-summation-statements.md](../logs/poisson-summation-statements.md);
* **the register of open build-time issues is [logs/build-time-issues.md](../logs/build-time-issues.md)**
  (the owed `ResidueSumQExpansion` rework, the resolved `ZLattice` blocker, the tree's incomplete
  oleans, the lock/memory rules, and the `/usr/bin/time` measurement trap). Read it before any
  build-heavy wave;
* **the cap is a diagnostic, not the build budget.** The library's own setting is the lakefile's
  `maxHeartbeats 4000000`, so a declaration whose measured cost is **arithmetic defeq** rather than
  instance synthesis (`Add.add`/`Nat.rec` unfolding from a large expression) may exceed the 200,000
  edit-loop budget and still be correct and green at tier 1. The rule for that case: **no `set_option`
  of any kind**, the pin's own bump, the bisection and the diagnosis recorded in the module header, and
  the tier-1 `lake build` as the gate. First instance:
  `EisensteinSeries.sum_eisensteinG_vecCons_eq_mul_tsum_divisorSum_mul_cexp_pow` (pin 4,000,000; port
  300k–400k; `lake build` 31 s, WORKORDER-MG3). Deferral is reserved for a proof that no longer
  **closes** at any budget — the `HeckeCosetSeam.of_dvd` case;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` when a file is done (writes the
  `.olean`, builds dependencies, never dependents);
* **no bare whole-tree `lake build`** while a set is in flight; one at a milestone, with
  permission;
* every `lake build` serialized and bounded.

The wave that a hub edit forces can exceed the 300 s bound on a real compute
(`ModularPolynomialE4Cube` alone is ~280 s). That is not a blow-up: the tell is CPU time — high
user CPU with a timeout is real work and the target list should be re-run with a larger wall
bound; ~0 CPU wall-time is another agent's lock. A genuine blow-up is bisected, never re-run with
a bigger heartbeat cap.

## 6. Verification

```bash
cd lean
python3 spec/check_port.py --changed                    # the new per-module wire (the registry)
python3 spec/check_port.py --force <the set's module>   # one module, every public declaration
python3 spec/check_port.py --all                        # the whole wired surface
flock .lake/flt_build.lock timeout 900 lake build        # the milestone build
timeout 180 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false spec/DeligneSerreConsumer.lean
python3 spec/unwired_register.py --check                # tier-3 surface current
```

plus a `#print axioms` probe over the set's headlines and a `grep` sweep for
`sorry`/`admit`/`axiom`/`native_decide`/`import Mathlib`/heartbeat overrides.

**One checker, one wire per module** (playbook §4). A set's new module carries `spec-pin:` lines —
the pin file per source, the `Theorems/` wrapper for a statement and the `P2M/Sol/S_` file for a
transcribed proof — and is verified by `spec/check_port.py`, which matches on the statement hash:
a faithful but renamed copy verifies, a same-name statement that differs is a `MISMATCH`, and an
engine's internal declarations are checked, not only its headline. Declaration-level exceptions
are `pin:`/`own:` entries in **`spec/decl_markers.tsv`**, keyed by `(module, full declaration
name)`; the source carries no marker for new work, and the grandfathered in-source `-- pin:`/
`-- own:` comments are still read where they exist. `spec/old_check_stmts.py` is the frozen
registry of the grandfathered `PORT_FILES`/`SOURCES` set, **not run as a gate**: do not append to
it, and do not expect its 10473 to move. Each work order records its own numbers, measured on the
tree it leaves, not copied from this note.

The checker's exemption list is keyed by **dotted name, never bare last name**: a bare
`"correspondence"` silently exempted two live declarations alongside its namesake, and dotting it
to `"AlgebraicCurve.Pic0.correspondence"` moved the count by +2 verified / −2 exemptions. That is
the same last-name blindness `frontier.py` shows on the `ModularForm`/`CuspForm` rename pairs
(§2, §9).

## 7. What remains

The unconditional slice stops where the automorphic input begins. Two gates remain, both on one
subject (the automorphic/adèlic `GL₂` layer, scout §2):

* **Gate 1 — the Rankin-type second-moment bound.**
  `DeligneSerre.exists_tsum_norm_qCoeff_sq_mul_rpow_le_log_of_weightOne_hecke_eigen`
  (764 needed nodes, 271 own `S_` lines), feeding
  `DeligneSerre.isIrreducible_matrixRepresentation_of_tsum_norm_trace_sq_le_log_of_odd`
  (11 needed, 478 own).
* **Gate 2 — coefficient-ring finiteness by upper density.**
  `DeligneSerre.exists_finset_qCoeff_mem_of_upperDensity_le_of_weightOne_hecke_eigen`
  (765 needed nodes, 248 own `S_` lines), feeding
  `DeligneSerre.exists_natCard_range_le_of_charpoly_frobenius_mem_of_upperDensity_le`
  (13 needed, 283 own).

Both reach the shared ray-class node `M4aTorus` (12,126 raw `S_` lines) by exactly one route —
`NumberField.exists_differentiable_eq_rayClassLSeries_of_ne_one` — and use only its continuation
conjunct, discarding the functional equation. Budget by the `S_`-line column, not by node count:
most of those nodes are self-contained against mathlib and show cost 1 in `frontier.py`. The
**converse cone** (`exists_weightOne_cuspForm_tameConductor_of_qCoeff_eq_trace`) is a separate
subject and a separate effort.

**The ready shelf** of §2 read 85 candidates on 2026-10-19 (67 when this note was last
refreshed), of which 13 are `ModularCurve` and the column's own. The
step-6 re-read after WORKORDER-F1 put the two `tateCurve_…_nonToricPoint_…` rows (1,343 each) and
`qTwist_nonToricPoint_of_pow_eq_one` (185) on it; the first two are the natural next cut and are
**exact twins** — one 1,325-net-line development with two headlines, the WORKORDER-E shape (§2) —
with `phiIrreducible_all` (434) behind them once a definition-layer check says so. The level-`N`
and `Φ_N` subjects and the level-`N` `q`-expansion bridge have landed, and their successor
`ModularCurve.LevelN.exists_algHom_laurentBaseChange_apply_eq_qExpand` (165) is on the shelf.

The **centre-cut pair** and the **fundamental-domain trio** have landed
([../logs/centre-cut-vanishing.md](../logs/centre-cut-vanishing.md),
[../logs/centre-cut-sibling.md](../logs/centre-cut-sibling.md),
[../logs/centre-cut-fundamental-domain-trio.md](../logs/centre-cut-fundamental-domain-trio.md)):
the pair shares the tier-3 `Cusp/CentreCutEngine.lean`, the trio shares the promoted slab prelude in
`PeterssonSlabPairing.lean`. The 234-line
`CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_…_ample` is deferred on the
unported `Def_AutomorphicForm_CuspidalSpectrumCarrier.lean`; the larger `coversModCentre` silo
(`exists_isIrreducibleGLRep_linearMap_span_translate_realization_of_coversModCentre`, 3,038 lines)
is still behind the unit-factorizable chain recorded in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

The **complex archimedean Casimir** wave has landed its definition pair and first headline
([../logs/arch-casimir-complex.md](../logs/arch-casimir-complex.md)); the next leaves of that
subject are `leftCasimirComplex_eq_archCasimirAtComplex_of_isArchSmoothAtComplex` (1,227) and the
133-line `archCasimirAtComplex_rightTranslate_rowIsometryInclAt_of_ne`, then the 35-file complex
fan of [automorphicForm/TOPIC-arch-casimir.md](automorphicForm/TOPIC-arch-casimir.md) §5 Set C.

The **archimedean type-span leaf** has landed too
([../logs/arch-type-span.md](../logs/arch-type-span.md), WORKORDER-ATS): it was the demand's
rank-#2 high-impact leaf, it is a façade over the shared `Q09` engine
(`RepTheory/TypeReproducer.lean`), and it put its successor
`AutomorphicForm.finiteDimensional_span_translates_of_mem_archCutSubmodule` — the same principle at
the whole archimedean cut, 184 silo lines, `used_by` 6 cone / 7 project — on the ready shelf. The
family's third row,
`CuspidalConstituent.inf_iSup_archTypeSubmoduleAt_le_iSup_inf_of_continuous`, still needs three
nodes / 369 lines; the seven other consumers are the `CuspidalConstituent` cut-weight and
isotypic-cut rows of §2.

The **matrix-group right-finite pair** has landed too (§1, WORKORDER-MG1) as a mathlib supplement,
and it moved the `Matrix.`-namespace remainder onto the shelf: the four ready leaves of
`Matrix.exists_bijective_transpose_mulVec_of_adjoin_intCast` (765), `…specialUnitaryGroup_fin_two_eq_diag_mul_rotation_mul_diag`
(114), `…SpecialLinearGroup.closure_diagonal_unipotent_weyl_eq_top` (86) and
`…exists_specialLinearGroup_mul_upperTriangular` (76) are WORKORDER-MG2 (970 net new, +73); the
`GeneralLinearGroup.exists_natCard_le_of_isSemisimpleRepresentation_of_card_image_charpoly_le` row
(1,242) is ready only with `ModularCurve.SerreImage.contains_SL2` (390, the column's own §2 shelf
row) and is set MG4 (the older rows call it MG3; 1,611 net new, +53), **landed 2026-10-20** as a full
dispatch (record: [logs/matrix-gl2-count.md](../logs/matrix-gl2-count.md)); the four `Matrix.SpecialLinearGroup` free-group rows landed 2026-10-20. All three cuts are priced in
[deligneSerre/TOPIC-matrix-family-in-cone.md](deligneSerre/TOPIC-matrix-family-in-cone.md).

The **Hecke coset seam** has landed (§1, WORKORDER-HS1) with its definition gate — the three
`LocalLanglands` `Definitions/` modules the port had never homed — and its 39-line well-definedness
row has landed as an append to `RepTheory/LocalLanglands/HeckeCosetSystem.lean` (addendum §9 of the
order). **The `HeckeIntegralSeam.` namespace is out of the D-S demand entirely.** The
`_principalLevel` near twin has landed as well (addendum §10): outside the cone, but banked now
because it re-proves the same engine — with the engine public it cost 11 restated declarations and
45 imports. What the family still holds, all outside the cone and cut when a column needs it:
`exists_isHeckeCosetSystem_integralSubgroup_diagPi` (35),
`IsHeckeCosetSystem.exists_bijective_forall_exists_mul_eq_mul_of_mem` (72),
`IsHeckeCosetSystem.sum_apply_mul_prod_ofFn_eq_of_mem` (111),
`exists_isHeckeCosetSystem_and_isHeckeCosetSystem_mul_inv_of_conj_eq` (137), and
`exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd` (957 pin lines, the same engine under
`v ∣ N`, which is now a small module on the public engine). The first consumer to become ready is
`AutomorphicForm.SmoothCusp.not_isHeckeCosetEigenfunctionAt_levelOne_bot_inf_finiteAdelicGL2Subgroup`
(229).

The `Place` **separability pair** has landed too (§1, WORKORDER-SU1): a uniformiser at a place
is a separating element, and so is an element of nonzero tame order
([../logs/separating-uniformiser.md](../logs/separating-uniformiser.md)). It put four rows on the
ready shelf — the top one is
`AlgebraicCurve.Place.ord_diffCoeff_D_nonneg_of_isSeparable` (576 silo lines, 5 of its 6 cone nodes
ported), then `Place.diffCoeff_smul_D_of_ord_eq_one` (28), `Place.diffCoeff_smul_D_eq_of_ord_eq_one`
(26) and `AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable` (20) — and the first is the
natural next cut of the differential-layer family.

The **local-parameter family** is complete (§1): the finite cover
([logs/localParam-finite-cover.md](../logs/localParam-finite-cover.md)), the branch uniqueness,
the local parameter with its meromorphic-order dictionary, and the four leaves those rest on
([logs/localParam-family.md](../logs/localParam-family.md)). Its capstone is the charted-space
node `AlgebraicCurve.Place.exists_chartedSpace_meromorphicOrderAt_evalAt_eq_ord_complex` ("the
places of a complex function field form a compact Riemann surface", 1,576 silo lines), which now
lacks only its own assembly; beside it sit
`Place.connectedSpace_of_chartedSpace_of_meromorphicOrderAt_eq_ord_complex` (679),
`Place.exists_forall_ord_eq_finset` (291, ready) and `Place.exists_ord_eq_one`. The family's own
prelim blocks are *not* reproduced: the port imports one copy of each, at its theory home
(`Place/OrdCalculus.lean`, 19 declarations after the re-home) — see
[logs/localParam-family.md](../logs/localParam-family.md) §1 and §3.5.

The **Γ₁/Nebentypus pair** the shelf once showed at its head — the two `CuspForm` rows — is the
**lifting column's**, not this column's, and has landed there as
[deligneSerre/WORKORDER-S8-nebentypus.md](deligneSerre/WORKORDER-S8-nebentypus.md)
(`ModularForms/HeckeNebentypus{Existence,Fricke}.lean`, checker +2, deduped onto the promoted
`CuspForm.HeckeEigenNebentypus` API).

The **continuous norm section** has landed ([../logs/norm-section.md](../logs/norm-section.md)):
the tier-3 engine `NumberField/TateGlobal/NormSection.lean` now homes the 25 declarations nine
pin `S_` files re-prove, so the family's remaining cuts import it rather than copy it. The next
two rows of that family are the cousins
`NumberField.TateGlobal.exists_norm_apply_eq_ideleNorm_rpow` (236 silo lines, 42 project
dependents) and `RatIdele.exists_norm_apply_eq_ideleNorm_rpow` (312, 7) — "the absolute value of
a continuous idèle-class character is a power of the norm", 496 net new lines for the pair, with
an `expUnit`/`expUnit_*` block they share with each other. They are their own order:
[numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
§5, §7.

**GL₂ strong approximation over ℚ** has landed too ([../logs/gl2-strong-approximation.md](../logs/gl2-strong-approximation.md)):
the five-module engine `NumberField/AdelicLevel/StrongApprox/` puts the `AdelicLevel` vocabulary
to work for the first time (874 of 898 pin lines were new, 0 substitutions). Its successors are
the level-`N` variant `NumberField.AdelicLevel.exists_glFin_globalPoints_mul_mem_finiteLevelOne_rat`
(397 pin lines; demand now 3 nodes / ≈720 raw `S_` lines), then
`AutomorphicForm.SiegelCovering.centreCutSiegelSet_coversModCentre_rat` — the adelic cover the
centre-cut subject of §1 needs at ℚ — and two `AutomorphicForm` coset/isotypic nodes. None is
ready; the level-`N` row is the next cut of that family.

The **`EisensteinGeneral` local twisted integral** is complete on the ready shelf: five headlines
landed (three ramified, two unramified) over a shared engine and one definition gate
([numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md](numberTheory/eisensteinGeneral/TOPIC-local-twisted-integral.md)
§6). The family's remaining rows are `EisensteinGeneral.LocalUnr.integral_twisted_eq` (601 pin
lines — the general unramified formula, of which the landed vanishing row is the special case;
it needs two unported `LanglandsTunnell` rows, 249 raw lines) and the `LocalCorrection` pair
(173 lines, not ready). The five headlines' consumers — the `AutomorphicForm`
Godement–Eisenstein local-factor assembly — are not this column's.

The **factorization** node (the global counterpart: `∏ᶠ` integral = Euler `∏'`) has landed too
([logs/eisenstein-factorization.md](../logs/eisenstein-factorization.md)); its successor
`EisensteinGeneral.Factorization.inv_measure_adelicBox_mul_fourierIntegral_tensor_eq` (185 pin
lines) needs two unported `NumberField` rows (420 raw `S_` lines) before it is ready.

**Deferred to its own order** is the C2 row
`ModularCurve.exists_sum_smul_eq_of_isIntegralQExp_gamma1`. Its one substantive step is the
unported premise `ModularForm.exists_basis_gamma1_qCoeff_mem_range_ratCast`, and the chain behind
it is ≈4.8k raw / ≈2.1k `S_` lines; the ported `CuspForm` twin cannot stand in for it because the
cuspidal subspace does not span the Eisenstein part. The row is documented in
`X1/IntegralityJqNModC.lean`'s docstring and open in [CARRY-FORWARD.md](../CARRY-FORWARD.md).

## 8. Reproduce

```bash
cd tools/deps
# the D-S cone, canonical: --ds targets the weight-one headline and excludes the
# prunable complex-analytic subject (deligneSerre/PRUNABLE-complex-analytic.md §4;
# tools/deps/ds_prunable.py), --include-leaves shows the demand's graph leaves that
# --ready/--hops drop
python3 frontier.py --ds --include-leaves --rank-by silo --top 0
# ... the conservative (no name-scan) reading, and the ready shelf / needed alone
python3 frontier.py --ds --include-leaves --frontier sources --top 0
python3 frontier.py --ds --rank-by silo --ready --top 0
python3 frontier.py --ds --top 0

# scope one cluster (step 3): advise → plan → price
python3 port_advise.py --target <node> --target <node> --json build/cluster_advise.json
python3 port_plan.py --json build/cluster_advise.json
python3 build_ladder.py --edit FLTForHuman/<host>.lean

# the gates
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen --top 0
```

The checker wiring convention is the per-module one: a module carries `spec-pin:` lines in its
leading `/- … -/` block naming the pin files that verify it (the `Theorems/` wrapper for a
headline, the `P2M/Sol/S_` file for a transcribed engine). Declaration-level exceptions — a rename,
a source outside the header, a tier-2 statement — are `pin:`/`own:` entries in
**`spec/decl_markers.tsv`**, keyed by `(module, full declaration name)`; the Lean source carries
**no** per-declaration marker for new work (the grandfathered in-source comments still work).
Nothing is appended to `spec/old_check_stmts.py`: that file is now only the frozen registry and
the shared parser. `spec/statement_db.py build` makes the pin corpus (`tmp/flt-statements/`,
git-ignored) that the checker reads; `spec/statement_db.py show <name>` prints a pin signature
with its `file:line`.

The statement instrument's mutation sensitivity is its own unit test — the parser and hash are
shared with `spec/old_check_stmts.py`, so run it when that parser changes rather than on every
set:

```bash
cd lean
python3 spec/old_check_stmts.py --selftest
```

## 9. Residuals

* **The norm-section engine.** `NumberField/TateGlobal/NormSection.lean` is tier 3 and its 25
  declarations have exactly one importer today (the façade); their intended consumers are the
  eight `normQ` siblings, unported, which must import it rather than copy it
  ([numberTheory/tateGlobal/TOPIC-norm-section.md](numberTheory/tateGlobal/TOPIC-norm-section.md)
  §3, §5). Two of the 25 (`norm_ringEquiv{,Real,Complex}*_symm`) duplicate an inline argument in
  `TateGlobal/ArchNorm.lean` and a public copy in
  `AutomorphicForm/Adelic/WeylIntegrable/LatticeEstimates.lean`; `ArchNorm.lean` is the natural
  home if `AutomorphicForm` ever needs them from here (≈45 s hub wave, not owed).
* **The GL₂ strong-approximation engine.** `NumberField/AdelicLevel/StrongApprox/*.lean` is tier 3
  with 45 declarations and one importer (the façade); the intended consumers are the headline's
  5 whole-project dependents, unported. Two of its names collide *by spelling only* with other pin
  declarations (`exists_common_denominator` with six `ModularCurve` PD-pairing files, `detUnit`
  with a `ℝˣ`-valued `private def` in an `AutomorphicForm` silo), so neither is a home to share;
  recorded so a later `port_advise` run does not read them as duplicates. The five-module split
  is the layout, not a promise: merging them changes no statement.
* **The local twisted-integral engine.** `EisensteinGeneral/LocalTwisted.lean` +
  `LocalRamShells.lean` are tier 3 (34 declarations) with one importer each (the façade, and Set
  B's module); their intended other consumer is the `AutomorphicForm` Godement–Eisenstein
  local-factor assembly, unported. The two `untwisted` definitions (5-arg ramified in
  `TwistedSmoothLocal`, 3-arg unramified in `TwistedUnramifiedLocal`) are deliberately *not*
  unified: their statements differ, and a `Set B` proof that opened both would tie on
  `untwisted` — the ambiguity is recorded in the log.
* **Two wiring lessons from the factorization landing**, both now in the checker's comments: a
  listed `S_` file shadows its own `Theorems/` wrapper for last-name matching unless the wrapper is
  listed **first** (the headline's pin-private twin inherits its binders from a section variable, so
  the two texts differ); and a pin spelling the port seems to lack may already exist as a port-only
  alias elsewhere (`AdelicBox.integralFinteAdeles` is such an alias, in
  `NumberTheory/AdelicHaar/PlaceMeasure.lean`), so grep for the alias before declaring a name
  unspellable. The factorization set also carries the column's one file-level
  `set_option linter.style.haveILetI false` (six modules, 24 load-bearing `haveI` sites) — a
  candidate for narrowing.
* **Register.** The weight-4 engine (`TateSlots/{Convergence,SlotCoeff}.lean`) is tier 3: built and
  importable, not in `PORT_FILES`, with its 119 public declarations carrying `-- pin:` provenance
  in [spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md) (78 modules / 1,906 public / 1,618 with a
  pin original). Only the façade `TateSlots/CoefficientFormulas.lean` is diffed.
* **The `Q09` engine now has a second pin-silo consumer.** `RepTheory/TypeReproducer.lean` (tier 3,
  registered) is the home of the `TypePiece`…`MultiPlace` engine that the pin writes into both
  `S_AutomorphicForm_exists_isArchTestFactor_…` and
  `S_AutomorphicForm_CuspidalConstituent_finiteDimensional_span_rightTranslate_of_mem_iSup_archTypeSubmoduleAt`;
  the arch-type-span landing ([logs/arch-type-span.md](../logs/arch-type-span.md)) imports it and
  re-proves nothing. Two consequences for later work: (i) the remaining eight consumers of that
  leaf will find the engine there, not in their own silos; (ii) their proofs rely, as the pin does,
  on `archTypeSubmoduleAt` being *definitionally* `typeSubmodule (rowIsometryInclAt₀ F w) τ.ρ`
  (`hcut := rfl`), so a wrapper around that definition would turn a `rfl` into a proof obligation.
* **The matrix-group twin is parallel by construction.** `Analysis/MatrixGroup/{Unitary,Orthogonal}RightFinite.lean`
  are ≈80 % identical (898 diff lines, 33 hunks) because the pin writes the `ℝ` development as the
  `ℂ` one without conjugation, and the port keeps the pin's text. The generic `[RCLike 𝕜]` statement
  — which after the base-field normalization is *one* sentence, since `Matrix.orthogonalGroup` is
  mathlib's `abbrev` for `unitaryGroup` — is the natural revision, not a cleanup: it would wire 2
  headlines instead of 96 statements and leave ≈45 declarations in the tier-3 register. The route
  was priced and declined on 2026-10-20 (topic §7). The shared
  `LinearAlgebra/Dual/EvalSpan.lean` lemma has no mathlib counterpart (a recorded negative from
  `Mathlib/LinearAlgebra/Dual/`) and exactly two importers today.
* `locKer`/`adjoinRoot'` are public in `DeligneSerre/Lifting.lean` with no consumer today (kept
  per the pin).
* The private `det_eq` copies in `Gamma1Vanishing.lean`/`HeckeEigenNebentypus.lean` are
  statement-identical to the public `ModularForm.HeckeRepresentatives.det_eq`; the one
  un-promoted dedup candidate.
* **`Gamma1_le_of_dvd` is homed (2026-10-18).** mathlib has no order lemma for `Gamma1`, the pin
  re-declares the fact in 12 files and uses it at 135 sites, and the port carried five copies. The
  wave [logs/gamma1-le-of-dvd-home.md](../logs/gamma1-le-of-dvd-home.md) added the tier-3 mathlib
  supplement `NumberTheory/ModularForms/CongruenceSubgroupOrder.lean`
  (`CongruenceSubgroup.Gamma1_le_of_dvd`, the general `{m n}` shape — "the API lemma every consumer
  wants" — plus the `Gamma0` companion), deleted the three `private` copies (`DeligneSerre/Lifting.lean`
  ×2 including the `Gamma0` one, `WeightOne/IntegralWeightOneForm.lean`,
  `WeightOne/Gamma0Integral.lean`) and turned the three checker-listed copies into one-line wrappers
  at their pin binders (`ModularCurve/X1/Defs.lean`, `Analytic/NormSqLt.lean`,
  `WeightOne/RationalityDvd.lean` as `Gamma1_le_of_dvd'`). The checker is unchanged at 10,476 / 0 / 0;
  the wave also cleared `Lifting.lean`'s 18 `haveILetI` warnings by taking Lean's own
  `haveI`→`have` suggestion at every site. The next tenant of the same home is `Gamma_le_Gamma1`
  (public in `CuspForm.LiNormSq` — that copy must stay, it is the pin's — and `private` in
  `WeightOne/Gamma1IntegralBasis.lean` and `…/Gamma0Integral.lean`).
* The `Gamma0Integral.lean` prelude still exists `private` in its two sibling namespaces
  (`…GammaNBounded`, `…X1BoundedDenominators`); `GammaNBounded`'s `IsRat` is a *different
  formulation*, not a copy, and was deliberately left.
* The two gates of §7 are deferred by design, behind the fixed interface the unconditional slice
  leaves.
* The subject-A modules carry **15 narrow `set_option linter.* false in`** suppressions (13
  `unusedSectionVars`, 1 `style.haveILetI`, 1 `unusedVariables`), each on the individual
  declaration rather than file-wide. They are not stylistic: Lean auto-includes `[NeZero N]` in
  those signatures because the *value* uses it while the *type* does not, the linter then calls it
  unused, and `omit [NeZero N] in` is refused (`cannot omit referenced section variable`). The pin
  sets the same options file-wide in six of the eight `S_` files and 192 other port modules do the
  same, so this is house style narrowed, not a new licence — but a work order's "no
  `set_option linter.*` suppression" line should say so. Recorded in
  [CARRY-FORWARD.md](../CARRY-FORWARD.md).
* **The frontier and the new wire.** `frontier.py`'s `sources` tier reads the frozen checker's
  `SOURCES` *and* the `spec-pin:` headers of the port tree (2026-10-19), so a module handed over from
  `PORT_FILES` is ported in both readings; the `names` tier had always seen it (it scans
  `lean/FLTForHuman`). Measured on this landing: `union` `needed` 511,586 → 510,729 and `F` 991 →
  992, `sources` `needed` 542,993 → 542,136 and `F` 836 → 837, each exactly the 857 silo lines.
  Neither reading has any per-declaration "ported" flag: the unit is the pin *node*, so the pin's
  hundreds of copies of one lemma (263 for `mem_of_ord_nonneg`) stay in the demand as nodes of their
  own even when the port homes the lemma once — the landing only makes each of them cheaper.
* `frontier.py --ready` resolves names by last name, so a pin node that shares a last name with a
  ported declaration of another namespace is priced as ported. The known instance is the
  `ModularForm`/`CuspForm` rename pair of §7's deferred row — 10 needed nodes / 5,172 raw `S_`
  lines under `--frontier sources`, 1 / 36 under the default `union`. Read the pin node itself
  before trusting `ready` for such a pair, price the pin's `Theorems/` imports too, not only its
  `Definitions/` ones, and re-run both frontier readings: `port_advise` and `port_plan` never walk
  imports, so an unported premise outside the target files is invisible to them.
* **Protocol migration.** The per-module wire (`spec-pin:` header + `spec/check_port.py`, with
  `spec/decl_markers.tsv` for declaration-level exceptions) is current in
  [porting-playbook.md](../porting-playbook.md) §4, in this note's §3/§6/§8 and in the tooling
  (`tools/deps`, `spec/unwired_register.py`). The **older column notes and work orders still
  describe the retired "append to `PORT_FILES`/`SOURCES`" route** — they are the record of how those
  landings were wired, not instructions; a new set follows §6. The 583 modules still owned by the
  frozen registry are the migration backlog, and each moves when it is edited for another reason
  (playbook §4) — the Frobenius-subfield host moved that way on 2026-10-20 (§1).
* **The `of_dvd` seam sibling is scoped and deferred.** `HeckeIntegralSeam.exists_isHeckeCosetSystem_localRepSome_heckeGen_of_dvd`
  (957 pin lines, 55 declarations) is the family's last large row and sits outside the cone. It
  drags in **no modules** (every dependency is inside `HeckeCosetSeam`'s closure; its five extra
  `Definitions/` imports are inert), but its residual — 13 declarations / ≈320 lines — is dominated
  by a 153-line covering lemma that carries `set_option maxHeartbeats 3200000 in` in the pin and
  whose entrywise matrix steps no longer close under mathlib `v4.34.0`. That is proof development
  under the no-heartbeat-raise rule, so it waits for its own order (WORKORDER-HS1 addendum §11; a
  compiling draft is parked at `lean/tmp/HeckeCosetSeamDvd.draft.lean`).
