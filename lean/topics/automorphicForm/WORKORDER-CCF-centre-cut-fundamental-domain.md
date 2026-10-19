# WORKORDER-CCF — the centre-cut fundamental-domain trio

One set: the three genuinely ready centre-cut fundamental-domain nodes, plus the shared slab
prelude they need. Mathematics and landing record:
[../../logs/centre-cut-fundamental-domain-trio.md](../../logs/centre-cut-fundamental-domain-trio.md);
column: [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §3.

**Status: landed 2026-10-18.** The fourth `--ready` row is deferred (below).

## 1. Scope

| node | pin proof | deliverable |
|---|---|---|
| `AutomorphicForm.isAutomorphicFnAt_of_isFundamentalDomain_of_isAutomorphicFnAt_of_coversModCentre` | 325 lines | `AutomorphicForm/Adelic/DetNormSlab.lean` |
| `AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_integralWindowedSiegelSet_of_coversModCentre` | 267 lines | `AutomorphicForm/Adelic/MeasurableFundamentalDomainCover.lean` |
| `AutomorphicForm.exists_measurableSet_isFundamentalDomain_subset_iUnion_centreCutSiegelSet_of_coversModCentre` | 266 lines | same module (twin headline) |
| `AutomorphicForm.CuspidalSpectrum.exists_forall_setLIntegral_le_mul_setLIntegral_of_isSlabFundamentalDomain_of_coversModCentre_ample` | 234 lines | **deferred**, see §4 |

`port_advise` on the four: 1,092 raw lines, 953 declaration lines, 259 duplicate copies, 252 lines
already in the port as `private` in `PeterssonSlabPairing.lean`, 442 net new if copied blindly.
The three landed headlines are ~100 lines of proof in total once the prelude is shared.

**Not this set:** the deferred 234-line slab-integral bound; the larger `coversModCentre` silo; any
change to the port's `CuspidalSpectrumCarrier` (it does not exist).

## 2. The prelude

`PeterssonSlabPairing.lean` already owns the generic `FundamentalDomainSlab` prelude and the adelic
slab vocabulary. `port_advise` found 47 declarations / ≈350 lines of the target slice identical to
its `private` declarations. The order **promotes in place**:

* 20 declarations from `private` to public, each with a `-- pin:` marker into one of the three S
  files;
* three new shared theorems: `exists_measurableSet_isFundamentalDomain_subset` (107 lines),
  `setLIntegral_fd_le_sum_mul` (36), `cover_of_forall` (23);
* the rest stays `private`.

`build_ladder.py --edit FLTForHuman/AutomorphicForm/Adelic/PeterssonSlabPairing.lean` prices the
edit at **0 dependent modules**; the checker verifies the promoted declarations against existing
`SOURCES` copies where they exist and exempts the rest as tier 3.

The two twins are one module: private `main_integral` and `main_centre`, two public headlines. The
shared 107-line engine is used by both.

## 3. Deliverables

* `DetNormSlab.lean`: imports the hub, one headline, 325-pin-line statement;
* `MeasurableFundamentalDomainCover.lean`: imports the hub and
  `DetNormSlabFundamentalDomain` (for `exists_isFundamentalDomain_globalPoints_range_restrict_ideleNorm_det_Icc`),
  two private `main` developments and two headlines;
* no helper is public in a façade;
* the hub docstring records the shared-prelude role and the tier-3 markers.

## 4. The deferral

The 234-line node is **not ready** despite `frontier.py --ready`. Its wrapper imports
`Definitions/Def_AutomorphicForm_CuspidalSpectrumCarrier.lean` (288 lines / 31 declarations:
`IsSlabFundamentalDomain`, `fdPins`, `weightedMeasure`, `memberSubmodule`, `cuspMemberSubmodule`,
`pairing`, `toCarrier`, `IsLift`, …), which the port does not have. The frontier matched the *name*
`IsSlabFundamentalDomain` to nothing and priced the node as ported; this is the playbook §4(a)
import-only-definition blindness. The module imports only the already-ported `CuspidalConstituent`
and `TateGlobalZeta`, so it is a cheap definition wave when the node is scheduled. Recorded in
[CARRY-FORWARD.md](../../CARRY-FORWARD.md); do not schedule the 234 off `--ready` until it lands.

## 5. Build discipline

* edit loop `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 <file>`;
* `flock .lake/flt_build.lock timeout 300 lake build <module>` (hub first, then the façades);
* no whole-tree build; no `sorry`/`admit`; no heartbeat override; no `import Mathlib`.

## 6. Wiring

* `SOURCES`: the three wrappers only; the S files stay unlisted so the promoted prelude is tier 3;
* `PORT_FILES`: `DetNormSlab.lean` and `MeasurableFundamentalDomainCover.lean`;
* run `python3 ../tools/deps/unwired_register.py` after the wiring.

## 7. Results

* edit loop: 0 errors / 0 warnings;
* `lake build`: hub 7.7 s, `DetNormSlab` 3.5 s, `MeasurableFundamentalDomainCover` 3.9 s;
* checker: **10,263 identical**, 0 mismatched / 0 missing, 10,503 checked (3 headlines + 21
  promoted prelude declarations);
* `#print axioms` on all three headlines: `[propext, Classical.choice, Quot.sound]`;
* register current; 198 registered-unwired declarations;
* `git status`: the two modules, the promoted hub, the wiring, the register, and the records.
