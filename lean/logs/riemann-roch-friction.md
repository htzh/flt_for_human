# Riemann–Roch friction log

Running ledger for the Riemann–Roch port (`lean/topics/riemannRoch/`), phase 1
onward. Append as friction is hit; the generalizable part is folded into
`porting-playbook.md` at the end. Method and set map: phase 1
[PLAN-P1.md](../topics/riemannRoch/PLAN-P1.md), phase 3
[PLAN-P3-1.md](../topics/riemannRoch/PLAN-P3-1.md).

## Set D — definition layer (`WORKORDER-D-defs.md`)

*(dispatched 2026-09-29; entries appended by the worker)*

- **`port_advise` substitution false positives (manager, pre-dispatch).** On the
  six `RiemannRochRows` predicates (`RiemannInequality`, `RiemannIndexFormula`,
  `WeilDualityAdelic`, `WeilDuality`, `WeilOmegaEllAgrees`,
  `FunctionFieldRiemannRoch`) and on `HasPoleDivisorPackage`, the tool reports an
  identical statement already in the port, matched against
  `EisensteinWeightOne.E1Chi3IsModular` ("19 copies"). These are `def … : Prop`
  degeneracies, not real reuse. Verified by hand: the port has none of them. The
  `--with-defs` "126 substitutions / 1,118 lines" is therefore an upper bound.
- **Inventory tool omits `class`.** `port_advise`'s inventory (the checker's own
  `raw_declarations`) does not report `class` declarations, so
  `Place.DCoordGenerates`, `IsCurveOver`, `HasCanonicalDivisor` are absent from
  `tools/deps/build/rr_defs_inventory.txt`. Add them by hand to any work order.

### Worker entries (set D port)

- **Boundary crossing: `Pic` absent from `Defs/Divisor.lean`.** Pin
  `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean:221` declares
  `abbrev Pic : Type _ := Divisor K F ⧸ Divisor.principal (K := K) (F := F)`;
  the port's `Divisor.lean` header says the `Pic`/`torsion`/`AbelJacobiCard`
  block was deliberately not ported. `canonicalClass`
  (`Definitions/Def_AlgebraicCurve_CanonicalDivisor.lean:27-31`) is typed
  `: Pic K F`, and the checker diffs statement *text*, so `Pic0` cannot stand in
  (and is the wrong quotient: `Pic0` is the degree-zero piece). **Resolution:**
  `Pic` was transcribed verbatim into the new `CanonicalDivisor.lean` — the
  module that needs it — keeping the diff inside the six deliverable files. The
  checker verifies it automatically against the already-registered
  `Def_AlgebraicCurve_DivisorClassGroup.lean`, so no `OWN_PROOFS` entry is
  needed. **Manager decision wanted:** either keep `Pic` beside its pin siblings
  in `Defs/Divisor.lean` (un-skipping one line of the deliberately-skipped Pic
  family) or leave it in `CanonicalDivisor.lean` as written.
- **Work-order / inventory arithmetic.** `rr_defs_inventory.txt` sums to 133
  rows, not the 147 quoted in `WORKORDER-D-defs.md` §2. Reconciliation of the
  checker delta: 133 rows − 3 private (`uniformizer`, `ord_uniformizer`,
  `uniformizer_ne_zero`, correctly kept `private` in the port) = 130, plus the
  transcribed `Pic` = **131 diffed declarations** (2552 → 2683). The three
  `class` declarations (`Place.DCoordGenerates`, `HasCanonicalDivisor`,
  `IsCurveOver`) are landed and elaborate but are not parsed by the checker (or
  the inventory), so 134 public declarations actually landed.
- **No `port_advise` substitution was taken.** All six modules were transcribed
  from the pin; the port had none of the new names. The only substitution the
  tool offers on this set is the documented false positive
  `HasPoleDivisorPackage` → `EisensteinWeightOne.E1Chi3IsModular`
  (`tools/deps/build/rr_family_advise.json`, `substitutions[110]` and `[111]`),
  reproduced and rejected: it is a bare `def … : Prop` match and the two
  statements are unrelated. The six `RiemannRochRows` predicates do not appear in
  that substitutions list (they are `Definitions/`-only, not `S_` targets), but
  are the same shape.
- **No mathlib negative.** Every name the pin's seven files call resolved as the
  pin writes it under mathlib v4.34.0; no rename, no search, no replacement lemma
  was needed. In particular `Algebra.IsSeparable E F` discharged the
  `[Algebra.IsIntegral E F]` side-condition of `Divisor.pullback` in
  `TranscendenceTower.poleDivisor` with no extra instance — the one place the
  risk list expected API drift.
- **Statement spellings: pin, not wrapper.** There are no `Theorems/` wrappers
  for this set, so all 131 checked statements are the pin `Definitions/` text
  verbatim. No statement was respelled against a wrapper, and no statement was
  changed to ease a proof. No `OWN_PROOFS` addition was needed.
- **Deprecation warnings kept (from the pin's own proofs).** `dif_pos`
  (`CanonicalDivisor.lean:72`) and `zero_le'` (`AdelicIndex.lean:64`, `:335`)
  elaborate with `deprecated` warnings. They are the pin's proof terms and the
  checker ignores proof bodies, so they were left verbatim rather than rewritten;
  a later cosmetics pass may swap them (`dite_eq_left`, `zero_le`).
- **Imports.** `WORKORDER-D-defs.md` §1 lists `Defs.Place` for module 1, but
  `HasCanonicalDivisor`/`genus`/`Pic` need `Defs.Divisor` (`Defs.Place` does not
  import it). Module 1 imports `Defs.Divisor` (which re-exports `Defs.Place`).
  No module writes `import Mathlib`.
- **Build-discipline note.** `lake` keys rebuilds on content hashes, so `touch`
  does not force recompilation; the per-module wall times reported to the manager
  come from deleting each module's `.olean` and re-running the bounded file-done
  command. Every `lake build` ran under
  `flock /tmp/flt_for_human.lock timeout 120`; one per module, no whole-tree
  build.

### Manager review (Set D gate) — ACCEPTED

Independent checks, not the worker's report:

- `python3 spec/check_flt_statements.py` → **2683 identical / 0 mismatched / 0
  missing / 30 own-proof** (2713 checked); matches the worker.
- `flock … timeout 300 lake build` of all six modules → **success, 2530 jobs,
  1.8 s replay**; only the pin's own `dif_pos`/`zero_le'` deprecation warnings.
- Hygiene `grep` → every hit is a specific `import Mathlib.X` or a comment
  mentioning `import Mathlib`; no `sorry`/`admit`/`axiom`/heartbeat override.
- The three `class` declarations match the pin text verbatim by hand:
  `class DCoordGenerates : Prop where`, `class HasCanonicalDivisor : Prop where`,
  `class IsCurveOver : Prop extends HasPrincipalDivisors K F where`.
- `#print axioms` in `lean/tmp/rr_axioms_probe.lean` → `genus`, `indexOfSpecialty`,
  `omegaSpace`, `RiemannInequality`, `FunctionFieldRiemannRoch` all exactly
  `[propext, Classical.choice, Quot.sound]`.

**`Pic` decision:** keep it in `CanonicalDivisor.lean` as written. It is the
general curve vocabulary and its right long-term home is `Defs/Divisor.lean`
beside `Pic0`, but phase 1's only consumer is `canonicalClass`, which nothing else
uses; moving it means editing an existing ported module for no phase-1 gain.
Recorded as a **refactor-round item**.

**Follow-up (tooling, not this port): the checker does not parse `class`.**
`DECL_RE` (`spec/check_flt_statements.py:2124`) accepts
`def|theorem|lemma|abbrev|structure|instance` but not `class`, so `class`
declarations are invisible to the 0/0 gate in *both* directions. Set D's three are
hand-verified, but every later set with a `class` needs the same manual check.
Adding `class` to the alternation (treating it like `structure`: header + ordered
field names) would close the gap, but it would start diffing every `class` in the
port and is a bounded checker task of its own — **do not fold it into a porting
set**; schedule it separately and expect it may surface pre-existing mismatches.

## Set H1a — adelic index / `ell` prelude and the index targets (`WORKORDER-H1a-index.md`)

*(dispatched 2026-09-29; entries appended by the worker)*

- **Boundary call: the fifth target is in the H1a order's §1 table but not in the
  75-row appendix.** The order's §1 lists five public targets and says to spell
  all five from their `Theorems/Thm_*` wrappers; §0 says H1a carries "the five
  index targets". But `exists_genus_riemannIndex_of_stichtenothGenusExists`
  does not appear in `tools/deps/build/rr_homes.txt` §H1a (which has 75 rows);
  its pin body is the `_port`-named declaration at
  `S_…_exists_genus_…:1616`, and that row is filed under **H1b** (`rr_homes.txt`
  line 185). Decision: write the wrapper-named target in `Index.lean` (it is
  cheap and rests only on H1a material), as §0/§1 direct. **Manager flag:** if
  H1b later writes the same target under its wrapper name, it will clash with
  `Index.lean` (which H1b imports); H1b should either drop that row or spell it
  `_port`-named. The H1b order's §1 names only the two `RatFunc` targets, so the
  row is likely vestigial — but it is a boundary the H1a order did not resolve.
- **H1b declarations inside the primary source were dropped, not inlined.** The
  primary `S_` file also carries `weilDifferentialRankOne_of_stichtenothGenusExists`
  (`:1599`) and `indexOfSpecialty_eq_ell_sub_of_rankOne_max` (`:1606`), both
  `rr_homes.txt` §H1b rows. A wholesale transcription of lines 48–1624 picked
  them up; they were removed. They are not in the H1a 75-name union and §3's
  stop-early rule forbids inlining them.
- **Collapsed `_port` duplicates and the assembly tail (6 of the 75 rows).**
  `eq_of_ge_port`, `indexOfSpecialty_eq_of_genusReached_port`,
  `indexOfSpecialty_eq_zero_of_genusReached_port`,
  `omegaSpace_finite_of_genusReached_port` are byte-identical in statement to the
  non-`_port` copies (checked file-by-file); `stichtenothGenusExists_of_isCurveOver_port`
  is a port-named wrapper (and, in its own file, carries extra
  `[PerfectField K] [Algebra.EssFiniteType K F] (hC : ConstantsAreBase K F)`
  hypotheses) — it is H2's `stichtenothGenusExists_of_isCurveOver`; not written
  here. `solution` (`S_…_weilDualityAdelic_…:14`) is H2's assembly. Union landed:
  **70 public declarations** = 69 unique H1a names + the fifth target.
- **Statement spellings: five from wrappers, 65 from the `S_` file.** The wrapper
  forms differ from the `S_` copies only in the explicit `{K F : Type*} [Field K]
  [Field F] [Algebra K F] …` binder prefix and in the `↥` coercion notation
  (`FiniteDimensional K ↥(LSpace …)`, `Module.Finite K (↥(adeleSpace …) ⧸ …)`,
  `Module.Finite K ↥(omegaSpace …)`); the `S_` copies elide the binder prefix into
  section variables. All five port statements were verified byte-equal (under the
  checker's `norm`) to their wrappers. No `_port` copy carries a weaker statement,
  and no statement was weakened to ease a proof. `mk_mem_maximalIdeal_iff` and
  `eq_of_ge` are pin-`private` and promoted to public (the checker credits them
  through its pin-private fallback: 93 promoted overall, up from the D-layer
  count).
- **Explicit binders shadow section variables.** The module keeps the pin's
  namespace-level `variable {K F : Type*} [Field K] [Field F] [Algebra K F]` and
  writes the five wrapper-spelled targets with their own explicit `{K F : Type*}`
  binders. Lean excludes the shadowed section variables, so the source text is the
  wrapper's — confirmed by probe before writing.
- **No mathlib negative and no proof rewrite.** Every pin proof transcribed
  unchanged under mathlib `v4.34.0` (pin `v4.33.0`); the only edits are removal of
  the pin's `p2m_export`/`p2m_open` commands, the `import Mathlib`/`Definitions/`
  headers, the duplicated pin `Definitions` structures (`PoleDivisorPackage`,
  `HasPoleDivisorPackage`, already in Set D), and the already-ported
  `ord_nonneg_of_mem`/`mem_of_ord_nonneg`/`mem_iff_ord_nonneg`. The audit's R5
  negatives were honored: the four `Submodule` chain helpers stay port-local
  (`Submodule.nestedComapMapMkQEquiv`, `finrank_quotient_chain`,
  `finrank_quotient_chain'`, plus `comap_subtype_sup_of_le_of_le`,
  `finrank_quotient_chain_top`); `Submodule.mapQ_injective` does not exist, so
  `lSpaceQuotientToAdeleBddQuotient_injective` uses the pin's
  `Submodule.Quotient.mk_eq_zero` route. The audit's SUBSTITUTE rows are all
  Set-D statements (imported, not re-proved); its R2 (`Units.mulLeftLinearEquiv`)
  is an optional proof saving that was not needed. No new mathlib search was run.
- **The pin's local heartbeat overrides were dropped.** The `S_` file sets
  `maxHeartbeats` 3,200,000 globally and 1,600,000/2,400,000/3,200,000 on five
  `in`-scoped declarations; the port's global cap is 4,000,000, so all bodies
  elaborate without any local override (checked in 11 s). No `set_option
  maxHeartbeats` appears in the module.
- **Imports.** Beyond the Set D modules, the module imports nine specific mathlib
  files for the quotient/finrank/finiteness API
  (`LinearAlgebra.Dimension.{RankNullity,Constructions,Finrank,Finite,StrongRankCondition}`,
  `LinearAlgebra.Isomorphisms`, `LinearAlgebra.FiniteDimensional.Lemmas`,
  `RingTheory.Finiteness.Finsupp`, `Data.Int.LeastGreatest`); no `import Mathlib`.
  `open Module IsDedekindDomain WithZero` replaces the pin's
  `p2m_open "Module IsLocalRing Module.IsLocalRing IsDedekindDomain WithZero"`.
- **Deprecation warnings kept (from the pin's own proofs).** `zero_le'` at
  `Index.lean:488`, `:493`, `:517`, `:523` (the pin's `adeleBddQuotSingleEquivResidueField`
  and `finrank_adeleBdd_quotient` bodies). The checker ignores proof bodies, so
  they were left verbatim rather than rewritten; a later cosmetics pass may swap
  them for `zero_le`.
- **Verification.** `python3 spec/check_flt_statements.py` → **2753 identical /
  0 mismatched / 0 missing / 30 own-proof** (2783 checked), up from the
  2683/0/0 baseline by exactly the 70 new public declarations;
  `flock /tmp/flt_for_human.lock timeout 180 lake build
  FLTForHuman.AlgebraicCurve.Genus.Index` → success, 2530 jobs, 14.0 s wall;
  `#print axioms` on the five headlines all
  `[propext, Classical.choice, Quot.sound]`. The module is 1,517 lines.

### Manager review (H1a gate) — ACCEPTED

- `python3 spec/check_flt_statements.py` → **2753 identical / 0 mismatched / 0
  missing / 30 own-proof** (2783 checked); Δ = +70, exactly the new public surface.
- `flock … timeout 240 lake build FLTForHuman.AlgebraicCurve.Genus.Index` →
  **success, 2530 jobs, 2.3 s replay**; only the pin's own `zero_le'` warnings.
- Hygiene: the ten `import Mathlib` hits are nine specific submodules plus one
  comment; no `sorry`/`admit`/`axiom`/heartbeat override.
- Independent `#print axioms` probe → all five headlines exactly
  `[propext, Classical.choice, Quot.sound]`.
- Technique note (not a reusable tool): H1a assembled the module by slicing the
  pin `S_` file (lines 48–1624) and applying targeted in-place replacements for
  the five wrapper-spelled targets — cheap and faithful for a union-prelude file.
  The one-off scripts were removed.
- **Boundary resolution:** `exists_genus_riemannIndex_of_stichtenothGenusExists`
  landed in `Index.lean` under the **wrapper name** (H1a order §1 lists it as the
  fifth target). Its pin body `…_port` is filed in the H2 section of
  `build/rr_homes.txt` (line 185), so **H2 must not re-land it** — H2 imports
  `Genus/Index.lean`. The H2 order was corrected accordingly.
  `indexOfSpecialty_eq_ell_sub_of_rankOne_max` and
  `weilDifferentialRankOne_of_stichtenothGenusExists` are H2 rows (not H1b, as the
  worker's message said) and remain in H2's scope.

## Set H1b — the Stichtenoth genus-existence tower (`WORKORDER-H1b-stichtenoth.md`)

*(dispatched 2026-09-29; entries appended by the worker)*

- **Scout gate (playbook §2.6), pre-estimate.** Before writing the module the spine
  `TranscendenceTower → IntegralBasisInLSpace.ofRegularOutside →
  PoleDivisorPackage.ofTranscendenceTower → HasPoleDivisorPackage →
  stichtenothGenusExists_of_transcendenceTower` plus the two junctions
  (`ofTranscendenceTower`; the `RatFunc` instance `transcendenceTower` via
  `placeInfty`/`IsFractionRing`/`adjoin X`) was prototyped in `ScratchH1b.lean`.
  Pre-estimate: the order's ~950-line transcription budget (86 names / 949 once-each
  lines, minus the two collapsed `_port` duplicates). **Post-estimate: the spine
  transcribes; the module is 976 lines** and the union's genuinely new content is
  smaller than 949 because 15 rows of the H1b `S_` file were already landed by H1a
  (below). No statement was changed.
- **Collapsed `_port` duplicates (2 rows) and one H1a overlap.**
  `stichtenothGenusExists_port` ≡ the target `stichtenothGenusExists`, and
  `finiteDimensional_lSpace_zero_of_constantsAreBase_port` ≡ its target — both
  written once, spelled from the `Theorems/Thm_AlgebraicCurve_RationalFunctionField_*`
  wrappers (explicit-binder form; the two `S_` files differ only by the namespace
  name and the `_port` suffix, so no statement changed). The H1b order's
  `exists_genus_riemannIndex_of_stichtenothGenusExists_port` was not landed (H1a
  has it under the wrapper name in `Genus/Index.lean`), per the H1a manager note.
- **15 H1b-list rows were already in `Genus/Index.lean` — imported, not restated.**
  The H1b `S_` file repeats the whole H1a tail at its lines 1541–1725:
  `mul_mem_lSpace_add`, `pow_mem_lSpace_nsmul`,
  `PoleDivisorPackage.{pow_mul_u_mem_lSpace, pow_mul_u_mem_lSpace_of_le,
  ell_nsmul_poleDivisor_ge, degree_nsmul_sub_ell_le, ell_nsmul_sub_pos,
  degree_sub_ell_le}`, `riemannGenusBounded_of_poleDivisorPackage`,
  `stichtenothGenusExists_of_poleDivisorPackage` (H1a landed these from the H1a
  `S_` file), plus the two collapsed `_port` rows. Only the H1b-list gates built on
  them (`indexOfSpecialtyFinite_of_{poleDivisor,hasPoleDivisor}Package`,
  `stichtenothGenusExists_of_hasPoleDivisorPackage`,
  `gate_stichtenothGenus_le_of_poleDivisorPackage`, `gate_ell_c_nsmul_ge`,
  `gate_{x_transcendental,u_linearIndependent}_of_poleDivisorPackage`) are new.
- **Boundary stop NOT hit — but the two named wrappers are genuinely absent, and
  the spine was rebuilt from ported public facts.** The H1b order flags
  `ord_placeInfty` (`Theorems/Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty.lean:13`),
  `deg_placeInfty` (`…deg_placeInfty.lean:13`) and
  `eq_ofHeightOneSpectrum_or_eq_placeInfty` (`…eq_ofHeightOneSpectrum_or_eq_placeInfty.lean:14`)
  as unported, and none is public in the port. The tower does **not** need them:
  `PrincipalDivisors/RatFuncDegree.lean` already carries the same mathematics
  publicly —
  `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum` (`:186`),
  `deg_eq_one_of_forall_ne_ofHeightOneSpectrum` (`:253`),
  `toValuationSubring_eq_of_forall_ne_ofHeightOneSpectrum` (`:104`),
  `subsingleton_setOf_forall_ne_ofHeightOneSpectrum` (`:86`),
  `exists_forall_ne_ofHeightOneSpectrum` (`:97`) — and holds the dichotomy and
  `placeInfty_ne_ofHeightOneSpectrum` only as `private` (`:59`, `:76`), therefore
  inaccessible across modules. Resolution (proof-only, no statement touched):
  `ord_placeInfty_X`'s proof goes through
  `ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum`;
  `transcendenceTower.hvdeg` uses
  `deg_eq_one_of_forall_ne_ofHeightOneSpectrum (placeInfty K) …` instead of the pin's
  `deg_placeInfty`; and a **private** `exists_ofHeightOneSpectrum_or_eq_placeInfty`
  (Stichtenoth.lean, RationalFunctionField block) is rebuilt from the public
  classification above, so `algebraMap_polynomial_mem_of_ne_placeInfty`'s pin proof
  transcribes textually. This required importing
  `FLTForHuman.AlgebraicCurve.PrincipalDivisors.RatFuncDegree`, which the order's §1
  import hint did not list.
- **Boundary note: the pin's `instSumRamificationInertia_port` (`S_…:1784`) has no
  port counterpart.** `Divisor.degree_pullback` needs
  `[FundamentalIdentity K E F]`, and the pin supplies it by a `scoped instance`
  built from the public `Place.sum_ramificationIndex_mul_inertiaDeg`
  (`Theorems/Thm_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg.lean:13`),
  neither of which the port landed. The port's equivalent is
  `Place.sum_ramificationIndex_mul_inertiaDeg_fiberOver`
  (`WeilExchange/FiberOverCount.lean:33`), stated over `fiberOver` rather than
  `fiber`. Resolution: a **private** instance
  `instSumRamificationInertiaOfFiniteDimensional` bridges the two finsets
  (`Finset.ext` + `Place.mem_fiber`/`Place.mem_fiberOver`) and feeds
  `PushPull.instFundamentalIdentityOfSumRamificationInertia`; it is `private`, so it
  stays outside the checked surface. Without it `degree_poleDivisor_eq_finrank`,
  `gate_degree_pullback_single_of_deg_eq` and the whole `ofTranscendenceTower`
  junction fail instance synthesis.
- **Mathlib negatives.**
  - No public place-at-infinity degree/order wrappers in
    `Defs/RatFuncPlaces.lean`, and no `SumRamificationInertia`/`FundamentalIdentity`
    instance in the AC cone: both had to be supplied as above.
  - No `Algebra.adjoin_eq_self` (as the order notes) — not needed;
    `Algebra.adjoin_le` + `Algebra.subset_adjoin` suffice.
  - `Polynomial.basisMonomials` is **not** in
    `Mathlib.FieldTheory.RatFunc.Basic`/`Degree`; it needs
    `Mathlib.Algebra.Polynomial.Basis` (added). Likewise
    `RatFunc.transcendental_X` (AsPolynomial) and `RatFunc.intDegree_X` (Degree) are
    pulled in via `Mathlib.FieldTheory.RatFunc.Degree`.
  - `IsFractionRing.of_field` needs only `[FaithfulSMul R K]`, not `[Field R]`; the
    `adjoin X` route transcribes verbatim.
  - `linearIndependent_smul` is `Mathlib.RingTheory.AlgebraTower:97` (present in the
    cone); `FiniteDimensional.exists_is_basis_integral` is
    `Mathlib.RingTheory.DedekindDomain.IntegralClosure:125`.
- **Respellings.** None at the statement level: the checker moved
  **2753 → 2823 identical, +70 = exactly the public H1b declarations**, with
  `0 mismatched / 0 missing`; every public H1b declaration matched its pin
  statement on the nose. The only proof-level rewrites are the three in the
  boundary note above.
- **Deprecation/linter warnings kept (from the pin's own proofs/idioms).**
  `if_neg` (Stichtenoth.lean:305, :333, the pin's
  `xF_mem_lSpace_poleDivisor`/`mem_lSpace_nsmul_poleDivisor_of_regular_outside`),
  `push_neg` (:789, the pin's `algebraMap_polynomial_mem_of_ne_placeInfty`), and
  `linter.overlappingInstances` on the `stichtenothGenusExists_of_*` family (the
  pin's own `HasPrincipalDivisors`/`IsCurveOver` overlap). The checker ignores
  bodies, so they were left verbatim.
- **Verification.** `flock /tmp/flt_for_human.lock timeout 180 lake build
  FLTForHuman.AlgebraicCurve.Genus.Stichtenoth` → **success, 2718 jobs, 7.72 s
  wall** (first full build 8.81 s). `#print axioms` on
  `RationalFunctionField.stichtenothGenusExists`,
  `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase`,
  `RiemannGenusBounded` and `HasPoleDivisorPackage` all
  `[propext, Classical.choice, Quot.sound]`. The module is 976 lines; no
  `sorry`/`admit`/`axiom`, no heartbeat override, no `import Mathlib`.

### Manager review (H1b gate) — ACCEPTED

- `python3 spec/check_flt_statements.py` → **2823 identical / 0 mismatched / 0
  missing / 30 own-proof** (2853 checked); Δ = +70, the public H1b surface.
- `flock … timeout 240 lake build FLTForHuman.AlgebraicCurve.Genus.Stichtenoth` →
  **success, 2718 jobs, 1.8 s replay** (first build 8.8 s); only the pin's own
  `overlappingInstances`/deprecation notes.
- Hygiene: the `import Mathlib` hits are specific submodules plus one comment; no
  `sorry`/`admit`/`axiom`/heartbeat override.
- Independent `#print axioms` probe → `stichtenothGenusExists`,
  `finiteDimensional_lSpace_zero_of_constantsAreBase`, `RiemannGenusBounded`,
  `HasPoleDivisorPackage` all exactly `[propext, Classical.choice, Quot.sound]`.
- Scout gate honoured: `ScratchH1b.lean` (963 lines) compiled before the module;
  pre-estimate ~950 → post 976 lines.
- **Boundary stop not hit, but two real gaps surfaced that H2 must know about:**
  1. the pin's `Place.sum_ramificationIndex_mul_inertiaDeg` /
     `instSumRamificationInertia_port` are not in the port; H1b supplied a
     **`private`** `instSumRamificationInertiaOfFiniteDimensional` bridging
     `fiber`/`fiberOver` (it is *not* exported). If H2 needs it for a tower
     extension it must re-provide or a support dispatch must promote it.
  2. the pin's `stichtenothGenusExists_of_isCurveOver` wrapper
     (`S_…_exists_genus_riemannIndex_of_isCurveOver.lean:25`,
     `stichtenothGenusExists_of_isCurveOver_port`) is listed in the H1a section
     of `build/rr_homes.txt` (line 76) but was **not** landed by H1a (the worker
     classified it as an H2 wrapper) and is **not** in H2's 21-row list — it is
     currently unlanded. H2's `exists_genus_riemannIndex_of_isCurveOver` needs it;
     the H2 order was amended to land it as a port-named `private` helper.
- The three unported `RatFunc` wrappers the H1b order flagged
  (`ord_placeInfty`, `deg_placeInfty`, `eq_ofHeightOneSpectrum_or_eq_placeInfty`
  — all still absent) were **avoided**: `PrincipalDivisors/RatFuncDegree.lean`
  carries the same mathematics, so the proof bodies were rewritten and a private
  dichotomy rebuilt, statements untouched. That is a recorded reuse win, not a
  boundary stop.


## Set H2 — assembly, the Weil canonical divisor, and the `H¹` identification (`WORKORDER-H2-assembly.md`)

*(dispatched 2026-09-29; entries appended by the worker)*

- **Boundary that the H2 order did not anticipate, and its local resolution.**
  The order's §2 gap 1 asked for the pin's curve-level helper
  `stichtenothGenusExists_of_isCurveOver`
  (`S_AlgebraicCurve_exists_genus_riemannIndex_of_isCurveOver.lean:25`, port-named
  `stichtenothGenusExists_of_isCurveOver_port`) as a `private` helper. That helper's
  *only* pin proof obtains a separating transcendental from
  `AlgebraicCurve.IsCurveOver.exists_separating_transcendental`, whose sole home is
  `P2M/Sol/S_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean`
  (229 lines; wrapper `Theorems/Thm_AlgebraicCurve_IsCurveOver_exists_separating_transcendental.lean:13`).
  That lemma is **not in the port** — H1b's order §2 explicitly assigns it to a
  focused support dispatch — and it is load-bearing for *three* of H2's six targets
  (`exists_genus_riemannIndex_of_isCurveOver`,
  `weilDifferentialRankOne_of_isCurveOver`, and `main` →
  `exists_weilCanonical_riemannRoch`).  Rather than stop three targets, the missing
  mathematics was **re-provided locally as `private`** (the H1b precedent for
  `instSumRamificationInertiaOfFiniteDimensional`, and PLAN-P1.md §2's "resolve locally
  `private`, append to the friction log" rule): `Assembly.lean:73–170` now carries a
  private transcription of the pin's `kaehlerAdjoinBasis`,
  `kaehlerOfSeparatingTranscendentalBasis`,
  `finrank_kaehler_eq_card_of_separating'`, `trdeg_le_one`,
  `IsCurveOver.trdeg_eq_one_local` and
  `IsCurveOver.exists_separating_transcendental_local`.  The helper
  `stichtenothGenusExists_of_isCurveOver_port` (`:552`) and `main` (`:590`) are also
  `private`.  No pin statement was weakened; no frozen file was edited.  **Manager
  flag:** these private helpers are outside the checked surface and should be
  promoted by the final refactor round (their names collide with the pin's public
  names, so promotion means landing the pin's
  `IsCurveOver.exists_separating_transcendental` properly).
- **Second unlanded prerequisite, also absent from every `rr_homes.txt` section.**
  The H2 target `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists`
  calls `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached`
  (`S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean:17`,
  wrapper `Theorems/Thm_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean:13`),
  which is **not** in Set D, H1a, H1b or the H2 21-row union — the measurement only
  counted the 14 target `S_` files, so this 15th helper target fell through.  It was
  landed as a `private` transcription (`Assembly.lean:468–523`) since it is not part
  of H2's stated public surface (adding its own `S_`/wrapper pair to `SOURCES` would
  have exceeded the order's six-file wiring).  **Manager flag:** if the checker is to
  verify it, the refactor round should add
  `S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean`
  + its wrapper to `SOURCES` and drop the `private`.
- **Collapsed duplicates.** `exists_genus_riemannIndex_of_stichtenothGenusExists_port`
  ≡ the H1a target `exists_genus_riemannIndex_of_stichtenothGenusExists`
  (`Genus/Index.lean:1508`), already imported — not restated.  `main`
  (`S_AlgebraicCurve_exists_weilCanonical_riemannRoch.lean:146`) is public in the pin
  but kept `private` in the port, per the order §1.  The union's public surface
  landed here is therefore **19 prelude names + 6 headlines = 25 declarations**.
- **No statement drift.**  The six headlines are spelled verbatim from their
  `Theorems/Thm_*` wrappers (explicit-binder form); the 19 prelude names from the two
  pin `S_` files.  Checker: **2823 → 2848 identical, 0 mismatched / 0 missing**
  (2878 port declarations checked, 30 own-proof).  `+25` is exactly the new public
  surface.  `Submodule.Quotient.equiv` needed the pin's full 4-argument form
  (`_ _ e hmap`, `P`/`Q` are explicit section variables) — the pin already wrote it
  that way, so this was an initial transcription slip, not API drift.  The one genuine
  port-mathlib rename encountered was `Basis` → `Module.Basis` in the private
  separating-transcendental block (`open Module`); everything else in the pin's
  machinery (`mvPolynomialBasis`, `tensorKaehlerEquivOfFormallyEtale`,
  `FormallyEtale.of_isLocalization`/`of_isSeparable`, `IsFractionRing.of_ringEquiv_left`,
  `exists_isTranscendenceBasis_and_isSeparable_of_perfectField`,
  `IsAlgebraic.isSeparable_of_perfectField`, `trdeg_pos`) resolved as written under
  mathlib v4.34.0.
- **Imports.**  Beyond Set D + `Genus.{Index,Stichtenoth}` the module adds eight
  specific mathlib files for the private re-provision
  (`RingTheory.Kaehler.Polynomial`, `RingTheory.Etale.{Kaehler,Field,Basic}`,
  `RingTheory.Localization.FractionRing`, `FieldTheory.SeparablyGenerated`,
  `RingTheory.AlgebraicIndependent.TranscendenceBasis`, `LinearAlgebra.Basis.Basic`);
  no `import Mathlib`.
- **Warnings kept.**  `Finsupp.finset_sum_apply` deprecation and `zero_le'`
  deprecation (from the pin's `boundedFamilies`/`adeleBdd_sup_le` bodies), plus
  `linter.style.haveILetI` on the pin's `haveI := hne; haveI := hfin` idiom in the
  transcribed `main`.  The checker ignores bodies; left verbatim.
- **Verification.**  `flock /tmp/flt_for_human.lock timeout 300 lake build
  FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly` → **success, 2750 jobs, 10.11 s
  wall** (bounded file-done command is `timeout 180`; the 300 was the outer wrapper).
  `#print axioms` on all six headlines:
  `indexOfSpecialty_eq_finrank_H1`, `exists_genus_riemannIndex_of_isCurveOver`,
  `weilDifferentialRankOne_of_isCurveOver`,
  `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists`,
  `exists_weilCanonical_riemannRoch`,
  `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` — each
  exactly `[propext, Classical.choice, Quot.sound]`.  The module is 736 lines; no
  `sorry`/`admit`/`axiom`, no heartbeat override, no `import Mathlib`.  The
  `SumRamificationInertia` gap H1b flagged was **not** hit: the curve-level helper
  reaches `RationalFunctionField.stichtenothGenusExists`, whose proof already consumed
  that private instance, so no local instance was needed here.

### Manager review (H2 gate) — ACCEPTED

- `python3 spec/check_flt_statements.py` → **2848 identical / 0 mismatched / 0
  missing / 30 own-proof** (2878 checked); Δ = +25, the public H2 surface.
- `flock … timeout 240 lake build FLTForHuman.AlgebraicCurve.RiemannRoch.Assembly`
  → **success, 2750 jobs, 1.9 s replay**; only the pin's own deprecation/`haveI`
  linter notes.
- Hygiene: specific mathlib imports only (eight for the private separating-
  transcendental re-provision); no `sorry`/`admit`/`axiom`/heartbeat override.
- Independent `#print axioms` probe on **all six** headlines → each exactly
  `[propext, Classical.choice, Quot.sound]`.
- **Accepted with two promotion debts for the refactor round** (not defects: the
  playbook's "resolve locally `private`, promote later" rule):
  1. `IsCurveOver.exists_separating_transcendental` (pin 229 ln, public wrapper) is
     re-proved `private` inside `Assembly.lean:73–170`; it must be landed publicly
     (its own home, checker-wired) and `Assembly.lean` rewired to import it.
  2. `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` (a **15th**
     helper target the 14-file measurement missed) is `private` at
     `Assembly.lean:468–523`; it needs its `S_`+wrapper in `SOURCES` and promotion.
- **Measurement gap recorded:** the 14-`S_`-file cone misses helper targets that the
  targets' proofs reach (here one 15th node, ~56 ln). The plan's scope numbers are
  therefore a lower bound on the *checked* surface, though they were accurate for
  the 14 headlines.


## Set H3 — the differentials bridge and the Weil-differential interface (`WORKORDER-H3-weildifferential.md`)

*(dispatched 2026-09-29; entries appended by the worker)*

- **Boundary the H3 order did not anticipate (the H2 measurement gap again).**
  The union's primary source,
  `P2M/Sol/S_AlgebraicCurve_exists_linearEquiv_regularDifferentials_omegaSpace_zero.lean`,
  imports two wrappers whose bodies are in files that are neither in
  `rr_homes.txt` §H3 (the 25-row union), nor in Set D, H1a, H1b or H2, nor among
  the four named `Definitions/Def_*` modules:
  1. `Theorems/Thm_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean`
     → `P2M/Sol/S_AlgebraicCurve_weilOfKaehler_mem_omegaSpace_of_residueTheorem.lean:9`
     (18 ln);
  2. `Theorems/Thm_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean`
     → `P2M/Sol/S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean:146–196`
     (199 ln; the file's private proof block runs `:21–188`).
  The headline's proof uses (1) once (`kaehlerToWeil_mem_omegaSpace_zero`) and (2)
  three times (injectivity, the nonvanishing of the rank-one base point, and the
  maximality step that puts `f • ω₀` in `regularDifferentials`), so it is
  unprovable without them. This is exactly the "14-`S_`-file cone misses
  proof-reached helper targets" gap the H2 entry records, now on the differentials
  side (the port has **no** `weilOfKaehler` before H3). Per PLAN-P1.md §2's "resolve
  locally `private`, append to the friction log, and let the final refactor round
  promote" rule — the H2 precedent — both were transcribed into
  `Canonical/WeilDifferential.lean` as `private` declarations with their
  `Theorems/`-wrapper statements verbatim (no statement weakened, no frozen file
  reopened). **Manager flag:** these two are outside the checked surface and need
  promotion (a home + `SOURCES`/wrapper wiring) in the final refactor round; the
  alternative was a hard stop that would have left the H3 headline unlanded.
- **Public `uniformizer` re-exposure, not a re-open of Set D.**
  `Defs/CanonicalDivisor.lean` (Set D) transcribed the pin's
  `Def_ModularCurve_CanonicalDivisor.lean` with `uniformizer`,
  `ord_uniformizer` and `uniformizer_ne_zero` **private**; the pin then
  re-exposes them publicly in
  `Definitions/Def_ModularCurve_CanonicalDivisorUniformizer.lean:18–27`. H3 lands
  that module as `Defs/CanonicalDivisorUniformizer.lean` (four public names); the
  private copies in Set D are untouched. `dCoord_eq : v.dCoord = D K F v.uniformizer`
  is `rfl` because both `uniformizer` defs share the same
  `IsDiscreteValuationRing.exists_irreducible` choose body (`IsDiscreteValuationRing`
  is `Prop`-valued, so the instance arguments are proof-irrelevant).
- **mathlib drift: `LinearEquiv.ofBijective_apply` under a `Subtype.val` coercion.**
  The pin's last proof line
  `rw [LinearEquiv.ofBijective_apply, coe_regularToOmega_apply, kaehlerToWeil_eq_weilOfKaehler hω]`
  fails under mathlib v4.34.0: the occurrence
  `(LinearEquiv.ofBijective (regularToOmega hRT) ⟨hinj, hsurj⟩) ω` sits as the
  argument of the `Subtype.val` coercion `↑(e ω)`, and `rw` does not reach it
  (the `[simp]` lemma is `ofBijective_apply`, a `rfl` at the subtype level).
  Replaced by an explicit `change ((regularToOmega hRT ω : ↥(omegaSpace …)) : Module.Dual …)
  = weilOfKaehler K F hω` (definitionally equal) followed by the same two rewrites.
  Statement untouched; the `change` is proof-only.
- **Warnings kept, bodies verbatim.** `linter.unusedSectionVars` fires on several
  transcriptions (the pin's union/definition files do not set the option; only the
  `ne_zero_and_maximal` helper file sets `linter.unusedSectionVars false`),
  `zero_le'` is deprecated, and `kaehlerToWeil_zero` has the pin's unused-`α`
  binder. The checker ignores bodies; all left verbatim.
- **Verification.** `python3 spec/check_flt_statements.py`:
  **2848 → 2920 identical, 0 mismatched / 0 missing / 30 own-proof** (2878 → 2950
  port declarations checked; 93 → 98 promoted from pin-private). The `+72` is
  exactly the new public surface: 4 (`CanonicalDivisorUniformizer`) + 29
  (`LocalResidue`; the one private aux is excluded) + 10 (`WeilOfKaehler`) + 3
  (`RegularDifferentials`) + 26 (`Canonical/WeilDifferential.lean`: the 25-name
  union incl. the `'` copy, plus the `Theorems/`-wrapper headline). Build:
  `flock /tmp/flt_for_human.lock timeout 180 lake build
  FLTForHuman.AlgebraicCurve.Canonical.WeilDifferential` → success, 2755 jobs,
  4.7 s wall (the combined five-module replay is 1.92 s); the four `Defs` modules
  first build in 3.7–4.8 s each, all under the 180 s bound. `#print axioms` on the
  headline, its `'` copy, `ResidueTheorem`, `regularDifferentials`, `kaehlerToWeil`,
  `weilOfKaehler` and `HasCanonicalLocalResidueKStar` → each exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`/`admit`/`axiom`, no
  `import Mathlib`, no heartbeat override.
- **Headline is conditional, confirmed.** `#check` shows
  `[PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
  [HasCanonicalDivisor] [∀ v, v.DCoordGenerates] [HasCanonicalLocalResidueKStar K F] →
  (hC : ConstantsAreBase K F) → (hRT : ResidueTheorem K F) → ∃ e, …` — the pin's
  `hRT` and `HasCanonicalDivisor` hypotheses are kept verbatim and not discharged.
  The two helper wrappers were deliberately **not** added to `SOURCES`: they are
  `private` in the port, so adding them would have exceeded the order's five-file
  wiring (the H2 choice for its private helper target).

### Manager review (H3 gate) — ACCEPTED; all 14 targets landed

- `python3 spec/check_flt_statements.py` → **2920 identical / 0 mismatched / 0
  missing / 30 own-proof** (2950 checked); Δ = +72, the public H3 surface.
- Five modules build green (2755 jobs, 2.1 s replay); the four `Defs` first-build
  in 3.7–4.8 s. Hygiene: no `sorry`/`admit`/`axiom`/heartbeat override; only
  specific mathlib imports.
- Independent `#print axioms` probe → the headline, `ResidueTheorem`,
  `weilOfKaehler` each `[propext, Classical.choice, Quot.sound]`; the headline's
  conditionality (`hRT`, `[HasCanonicalDivisor]`) is kept, not discharged.
- **All 14 phase-1 targets are now landed and checker-verified.** The remaining
  work is quality, not targets: the promotion debts (§`WORKORDER-R-refactor.md`)
  and the consumer wire test.

**Method finding (third instance).** The 14-`S_`-file measurement is accurate for
the 14 headlines but a lower bound on the checked surface: proofs reach helper
targets outside the measured set. Instances so far:
`exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` (H2),
`weilOfKaehler_mem_omegaSpace_of_residueTheorem` and
`weilOfKaehler_ne_zero_and_maximal` (H3), plus the curve-level prerequisite
`IsCurveOver.exists_separating_transcendental` (H2). A future measurement should
close over the targets' **proof-reached public wrappers**, not just their own `S_`
files. Recorded in `PLAN-P1.md` and the refactor order.


## Refactor round (`WORKORDER-R-refactor.md`)

*(dispatched 2026-09-29; worker entries. Baseline 2920 identical / 0 mismatched /
0 missing / 30 own-proof, 2950 checked.)*

The round is the one allowed to reopen `Genus/Index.lean`, `Genus/Stichtenoth.lean`,
`RiemannRoch/Assembly.lean`, `Canonical/WeilDifferential.lean`,
`Defs/CanonicalDivisor.lean` and `Defs/Divisor.lean`.  No mathematical statement
changed; every move is recorded below.

### R1 — `IsCurveOver.exists_separating_transcendental` (promote)

- **New home** `FLTForHuman/AlgebraicCurve/IsCurveOver/SeparatingTranscendental.lean`
  (9 public declarations, all spelled at pin-public names): `kaehlerAdjoinBasis`,
  `kaehlerOfSeparatingTranscendentalBasis`, `finrank_kaehler_eq_card_of_separating`,
  `finrank_kaehler_eq_card_of_separating'`, `IsCurveOver.one_le_trdeg`,
  `IsCurveOver.trdeg_eq_one`, `IsCurveOver.trdeg_le_one`,
  `IsCurveOver.trdeg_eq_one_of_perfectField`,
  `IsCurveOver.exists_separating_transcendental` (from the `Theorems/` wrapper).
- The pin's `Basis` is `Module.Basis` in v4.34; `open Module` restores the pin's
  spelling, so the two `Basis`-valued defs diff verbatim (the H2 note's
  "`Basis` ↦ `Module.Basis`" adaptation is text-identical under the `open`).
- **No support lemma was kept private**: every name the target needs is pin-public.
  The pin-public `not_isSeparable`/`not_isAlgebraic`/`instTranscendental`/
  `exists_transcendental`/`trdeg_pos`/`trdeg_ne_zero`/`exists_separating_transcendental_s6`
  are not needed by the port proof and are left unported (not debts).
- `Assembly.lean`: deleted the whole `private` block (`:73–171`, 5 688 chars),
  added `import …IsCurveOver.SeparatingTranscendental`, and rewired
  `stichtenothGenusExists_of_isCurveOver` to it.  Header docstring updated.
- **Checker move** `SOURCES` += `Thm_…_IsCurveOver_exists_separating_transcendental`
  then `S_…_IsCurveOver_exists_separating_transcendental` (wrapper first);
  `PORT_FILES` += the new module.  `+9` identical.

### R2.1 — `exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached` (promote)

- The 15th helper target the 14-`S_`-file measurement missed.  **Home**
  `Genus/Index.lean` (appended at the end of the file, after
  `exists_genus_riemannIndex_of_stichtenothGenusExists`).  `Assembly.lean`'s
  `private` copy (`:345–405`, 2 498 chars) and its docstring deleted; the public
  `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists` imports it.
- **Checker move** `SOURCES` += its wrapper then its `S_` file (wrapper first),
  placed in the H1a block.  `+1` identical.

### R2.2 — the two Weil-differential helper targets (promote + move)

- **Home** `Defs/WeilOfKaehler.lean`, appended as a fresh `namespace AlgebraicCurve`
  block (upstream of the H3 consumer).  Made public: the pin-public support
  `kaehlerResidueTerm_single_of_ne`, `weilOfKaehler_single_s6`, `simplePoleProbe`,
  `weilOfKaehler_simplePoleProbe`, `simplePoleProbe_mem_adeleBdd`,
  `weilOfKaehler_ne_zero_s6`, `trace_residueField_eq_zero_of_weilOfKaehler_mem`,
  `weilOfKaehler_omegaSpace_le_canonical_s6`,
  `weilOfKaehler_ne_zero_and_maximal_s6`, plus the two targets
  `weilOfKaehler_mem_omegaSpace_of_residueTheorem` and
  `weilOfKaehler_ne_zero_and_maximal` (wrapper-spelled, explicit binders).
  `+11` identical.
- The pin-`private` helpers `ord_nonneg_of_mem`,
  `localResidue_mul_uniformizer_inv`, `exists_trace_residue_ne_zero` stay `private`
  (pin-private; recorded under R3).
- `Canonical/WeilDifferential.lean`: both `private` blocks (`:119–135` and
  `:262–400`, 5 958 chars of the second) deleted; the module keeps only the public
  headline; header docstring updated to record the promotion.  It now has **no
  private declaration**.
- **Checker move** `SOURCES` += the two wrappers + their `S_` files (wrapper first)
  in the H3 block.  `WeilOfKaehler.lean` gained
  `import Mathlib.RingTheory.Trace.Basic` and the pin's
  `set_option linter.unusedSectionVars false`.

### R3 — the port's own private layer

Every `private` declaration in the four reopened homes was decided:

| home | private | decision | reason |
|---|---|---|---|
| `Genus/Index.lean` | — | — | none |
| `Canonical/WeilDifferential.lean` | — | — | none left after R2.2 |
| `Assembly.lean` | `main` (:409) | keep | the pin's proof body of `exists_weilCanonical_riemannRoch`; order §1 says keep it private |
| `Assembly.lean` | `stichtenothGenusExists_of_isCurveOver_port` | **promote** | renamed to the pin-public `stichtenothGenusExists_of_isCurveOver` (the pin has `Theorems/Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver.lean:17`); wrapper + `S_` file wired into `SOURCES`; `+1` identical |
| `Stichtenoth.lean` | `instSumRamificationInertiaOfFiniteDimensional` (:254) | keep | adapter glue (§5) bridging the port's `fiberOver` sum to the class field's `fiber`; `grep` shows its only consumers are in `Stichtenoth` (`Divisor.degree_pullback` at `:308`/`:456`); every other module takes `FundamentalIdentityAlong` as a hypothesis |
| `Stichtenoth.lean` | `x_ne_zero`, `poleDivisor_apply`, `poleDivisor_nonneg`, `xF_mem_lSpace_poleDivisor`, `degree_poleDivisor_eq_finrank`, `mem_lSpace_nsmul_poleDivisor_of_regular_outside`, `exists_forall_mem_lSpace_nsmul_poleDivisor` | keep | all pin-`private` in the H1b `S_` file (`:1813`, `:1823`, `:1830`, `:1840`, `:1852`, `:1860`, `:1884`) |
| `Stichtenoth.lean` | `mem_of_isIntegral`, `mem_of_isIntegral_of_algebraMap_mem`, `mem_of_isIntegral_of_restrict`, `ord_nonneg_of_isIntegral_of_restrict`, `ord_nonneg_of_isIntegral_of_regularOutside`, `adjoin_x_regularOutside` | keep | all pin-`private` in the H1b `S_` file (`:2052`, `:2082`, `:2096`, `:2108`, `:2193`; `mem_of_isIntegral` is the pin's local twin of the public T12 `ValuationSubring.mem_of_isIntegral`, different statement/namespace) |
| `Stichtenoth.lean` | `exists_ofHeightOneSpectrum_or_eq_placeInfty` (:784) | keep | pin-public name is `eq_ofHeightOneSpectrum_or_eq_placeInfty`, but its port transcription is `private` in `PrincipalDivisors/RatFuncDegree.lean:59`, a module **not** reopenable this round; the Stichtenoth rebuild is the only cross-module-visible route, and publishing it here would add a second public home for a `RatFunc` fact whose natural home is closed |
| `Stichtenoth.lean` | `placeInfty_ne_ofHeightOneSpectrum'` (:799) | keep | same: pin-public name `placeInfty_ne_ofHeightOneSpectrum`, port copy `private` at `PrincipalDivisors/RatFuncDegree.lean:76`, outside the reopen set |
| `Stichtenoth.lean` | `exists_restrict_eq` (:928) | **dedup-delete** | a thin adapter over the public `Place.exists_restrict_eq` (`WeilExchange/Bifibre.lean:64`, itself pin-verified via `Thm_AlgebraicCurve_Place_exists_restrict_eq`); its single consumer `nonempty_place_of_ratFunc_tower` now calls the public lemma.  Pin's own copy is `private` (`S_…:2482`) |
| `Defs/WeilOfKaehler.lean` | `ord_nonneg_of_mem` (:171), `localResidue_mul_uniformizer_inv` (:218), `exists_trace_residue_ne_zero` (:274) | keep | pin-`private` in `S_AlgebraicCurve_weilOfKaehler_ne_zero_and_maximal.lean` (`:21`, `:70`, `:129`) |
| `IsCurveOver/SeparatingTranscendental.lean` | — | — | none: every needed name is pin-public |

No `OWN_PROOFS` entry was needed: every promoted statement diffed verbatim against
a pin-public source (wrapper or `S_` file).

### R4 — `Pic` placement (move)

- `abbrev Pic` moved from `Defs/CanonicalDivisor.lean` to `Defs/Divisor.lean`,
  beside `Pic0` (after the `Pic0` namespace), its general-curve home.  Its only
  consumer `canonicalClass` (in `CanonicalDivisor`, which imports `Divisor`) is
  unchanged.  Both docstrings updated; `Defs/Divisor.lean`'s "`Pic` deliberately
  not ported" note replaced.  Checker unchanged (`Pic` still verifies against
  `Def_AlgebraicCurve_DivisorClassGroup:221`, already in `SOURCES`).

### R5 — `uniformizer` (unify)

- **Promote once** in `Defs/CanonicalDivisor.lean`: `uniformizer`,
  `ord_uniformizer`, `uniformizer_ne_zero` are now public (the pin keeps them
  `private` there and re-exposes them in
  `Def_ModularCurve_CanonicalDivisorUniformizer.lean`, already in `SOURCES`).
- `Defs/CanonicalDivisorUniformizer.lean` keeps only the pin declaration
  `dCoord_eq : v.dCoord = KaehlerDifferential.D K F v.uniformizer`; the three
  duplicated copies are deleted, so the port has exactly one public
  `Place.uniformizer`.  Net checker count `0` (three names moved from the
  re-export file to `CanonicalDivisor`); both docstrings updated.

### Verification

- Checker: **2942 identical / 0 mismatched / 0 missing / 30 own-proof (2972
  checked)** — Δ = **+22** over the 2920 baseline, exactly the promoted public
  declarations: 9 (R1) + 1 (R2.1) + 11 (R2.2) + 1 (R3
  `stichtenothGenusExists_of_isCurveOver`); R3's dedup and R4/R5 move net zero.
  The `98 promoted from pin-private` count is unchanged.
- Individual module builds (flock, `lake build`): `Defs.{Divisor,CanonicalDivisor,
  CanonicalDivisorUniformizer}`, `IsCurveOver.SeparatingTranscendental`,
  `Defs.WeilOfKaehler`, `Genus.{Index,Stichtenoth}`, `RiemannRoch.Assembly`,
  `Canonical.WeilDifferential` — all green.
- **Bounded wave**: the order's literal `lake build FLTForHuman.AlgebraicCurve`
  is not a valid target in this tree (there is no `FLTForHuman/AlgebraicCurve.lean`
  facade: `error: no such file …`).  The wave was run over the 32 modules of the
  `FLTForHuman/AlgebraicCurve` tree, with the nine reopened/touched modules
  `touch`ed first so their dependents re-elaborate:
  `flock … timeout 400 lake build <32 AC modules>` → **success, 2765 jobs,
  10.68 s wall** (parallel; e.g. `PrincipalDivisors.Transcendence` 8.8 s,
  `WeilExchange.LocalExchange` 4.2 s).
- `#print axioms` on the 14 headlines
  (`indexOfSpecialty_eq_of_genusReached`, `indexOfSpecialty_eq_zero_of_genusReached`,
  `RiemannGenusReachedAt.eq_of_ge`, `omegaSpace_finite_of_genusReached`,
  `exists_genus_riemannIndex_of_stichtenothGenusExists`,
  `RationalFunctionField.stichtenothGenusExists`,
  `RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase`,
  `indexOfSpecialty_eq_finrank_H1`, `exists_genus_riemannIndex_of_isCurveOver`,
  `weilDifferentialRankOne_of_isCurveOver`,
  `weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists`,
  `exists_weilCanonical_riemannRoch`,
  `exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists`,
  `exists_linearEquiv_regularDifferentials_omegaSpace_zero`) → each exactly
  `[propext, Classical.choice, Quot.sound]`, unchanged.
- Hygiene: no `sorry`/`admit`/`axiom`, no `import Mathlib`, no heartbeat override
  in any touched file; probe confined to `ScratchR.lean`; no git command run.
- **Not in this round** (unchanged): the checker's missing `class` branch
  (`DECL_RE`, `spec/check_flt_statements.py`) remains a separate tooling task.

### Method finding (confirmed; for PLAN-P1.md §1 and the playbook)

The 14-`S_`-file cone is exact for the 14 headlines but a lower bound on the
checked surface.  This round closed the four proof-reached gaps it had recorded
(`IsCurveOver.exists_separating_transcendental`,
`exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached`,
`weilOfKaehler_mem_omegaSpace_of_residueTheorem`,
`weilOfKaehler_ne_zero_and_maximal`), plus the H2 curve-level wrapper
`stichtenothGenusExists_of_isCurveOver`.  A future measurement should close over
the targets' proof-reached public wrappers, not just their own `S_` files.

### Manager review (refactor gate) — ACCEPTED

- `python3 spec/check_flt_statements.py` → **2942 identical / 0 mismatched / 0
  missing / 30 own-proof** (2972 checked); Δ = +22 = the promoted public surface (9
  R1 + 1 R2.1 + 11 R2.2 + 1 R3).
- Wave build over the reopened modules and their dependents → **success, 2756 jobs,
  1.8 s replay**; hygiene clean (only comment mentions of `import Mathlib`).
- Independent `#print axioms` probe on **all 14** headlines (flattened output) →
  each exactly `[propext, Classical.choice, Quot.sound]`.
- Private counts after the round: `Genus/Index` 0, `Canonical/WeilDifferential` 0,
  `IsCurveOver/SeparatingTranscendental` 0, `Assembly` 1 (`main`),
  `Defs/WeilOfKaehler` 3 (pin-private), `Genus/Stichtenoth` 16 (pin-private +
  adapter glue) — every one recorded with a reason in the R3 table above.
- **Command correction (to apply in the plan/orders):** `lake build
  FLTForHuman.AlgebraicCurve` is **not** a valid target — there is no
  `FLTForHuman/AlgebraicCurve.lean` facade. The bounded wave must name the module
  list (`FLTForHuman.AlgebraicCurve.Genus.Index`, `…Genus.Stichtenoth`,
  `…RiemannRoch.Assembly`, `…Canonical.WeilDifferential`,
  `…IsCurveOver.SeparatingTranscendental`, `…Defs.{Divisor,CanonicalDivisor,
  CanonicalDivisorUniformizer,WeilOfKaehler}`) or build the whole library
  (`FLTForHuman`, which exists). `PLAN-P1.md` §6/§7 was corrected.
- **One reasoned residual, deliberately not a target-of-this-round:** the two
  `RatFunc` helpers `Place.eq_ofHeightOneSpectrum_or_eq_placeInfty` and
  `Place.placeInfty_ne_ofHeightOneSpectrum` are pin-public (both have `Theorems/`
  wrappers) but port-`private` in `PrincipalDivisors/RatFuncDegree.lean` (`:59`,
  `:76`), and the Stichtenoth tower keeps private rebuilds. Playbook §4 sanctions a
  tight public surface, so this is a design choice, not a missed gap; closing it
  means reopening `RatFuncDegree.lean` (a different effort's module) to promote both
  and rewire the tower — a small standalone dispatch if we want the two extra
  checked statements.

### R2 follow-up — the two `RatFunc` helpers promoted (`WORKORDER-R2-ratfunc-promote.md`)

- **Statement drift found and corrected (authorized).** The port's private
  `Place.placeInfty_ne_ofHeightOneSpectrum` (`PrincipalDivisors/RatFuncDegree.lean:76`)
  bound `K` implicitly (`{K : Type*}`), while every pin copy binds it explicitly:
  the wrapper `Theorems/Thm_AlgebraicCurve_RationalFunctionField_placeInfty_ne_ofHeightOneSpectrum.lean:12`,
  the pin's public original `Definitions/Def_AlgebraicCurve_RatFuncPlaceClassification.lean:31`
  (under `variable (K : Type*)` at `:16`), and the private `S_` copies. The checker's
  `norm` distinguishes the two, so promoting as-is would have yielded
  `2943 identical / 1 mismatched`. The manager authorized the binder fix as
  convergence to the pin (playbook §4: statements are the pin's), not respelling:
  `{K : Type*}` → `(K : Type*)` at `:76`, with `K` passed at the sole internal call
  site `:102`. `eq_ofHeightOneSpectrum_or_eq_placeInfty` was already identical
  (both implicit `{K : Type*}`), so the diff gate stopped on the second only.
- Both declarations dropped `private`. The two Stichtenoth rebuilds
  (`exists_ofHeightOneSpectrum_or_eq_placeInfty`, `placeInfty_ne_ofHeightOneSpectrum'`)
  were deleted and their consumers (`:809`/`:815`/`:833`, now `:782`/`:788`/`:806`)
  rewired to the public names; `Stichtenoth` already imported `RatFuncDegree`.
- `SOURCES` gained the `eq_` wrapper first, then the `placeInfty_` wrapper, then
  `P2M/Sol/S_AlgebraicCurve_RationalFunctionField_finite_setOf_ord_ne_zero.lean`
  (dotted-name fallback). `PORT_FILES` already listed `RatFuncDegree.lean`.
- **Checker:** 2942 → **2944 identical / 0 mismatched / 0 missing / 30 own-proof**
  (2974 checked) — Δ = +2; the `98 promoted from pin-private` count is unchanged.
- **Builds (flock):** `…PrincipalDivisors.RatFuncDegree` (2658 jobs),
  `…Genus.Stichtenoth` (2718 jobs), and the direct dependents
  `…PrincipalDivisors.Transcendence`, `…RiemannRoch.Assembly`,
  `…Canonical.WeilDifferential`, `…ModularCurve.Analytic.CuspDichotomy`
  (4051 jobs) — all green, only pre-existing linter warnings.
- `#print axioms` on all 14 headlines (probe `ScratchR2.lean`) → each exactly
  `[propext, Classical.choice, Quot.sound]`, unchanged.
- Hygiene: no `sorry`/`admit`/`axiom`/bare `import Mathlib`/heartbeat override in
  either touched file; private-declaration counts fell with none added
  (`RatFuncDegree` 7 → 5, `Stichtenoth` 16 → 14); no git command run. The residual
  recorded above is **closed** (`PLAN-P1.md` §7 updated).

## Set P2 — the canonical divisor (`WORKORDER-P2-canonical.md`)

Two new modules, both transcription; no statement changed.

- `FLTForHuman/AlgebraicCurve/Defs/KaehlerTranscendental.lean` — the two Kähler
  headlines (`span_D_eq_top_of_transcendental`, `D_ne_zero_of_transcendental`) plus
  their shared private `exists_basis` prelude (the pin's two `S_` files carry the
  same 35-line proof; the port writes it once). 94 lines.
- `FLTForHuman/AlgebraicCurve/Canonical/HasCanonicalDivisor.lean` — the union of
  `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`, with the wrapper
  headline `AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver` (and the pin-name
  `…_s12` kept public) and all six scoped instances. 1,559 lines.

### Scout gate (playbook §2.6)

- Prototype in `ScratchP2.lean` (the whole module body), compiled end-to-end with
  `timeout 600 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false
  ScratchP2.lean` → **17 s**, 0 errors. The spine
  `span_D_eq_top_of_transcendental` → `valSubringKaehlerSpanTop_of_…` →
  `hasCanonicalDivisor_of_generator_finiteSupport_s12` → headline is the pin's own
  chain and elaborates unchanged.
- **Pre/post estimate:** pre raw ≈1,850 / content ≈1,200–1,400; post 1,653 written
  lines (1,537 body + headers), i.e. ~10 % over the top of the estimate. The excess
  is the six `instance`s the inventory tool missed and the statement-verbatim
  `uniformizerSubring'` aliases below. Holds; no stop-early condition hit.

### Mathlib drift forced by `v4.34.0` (two real fixes)

1. **`TensorProduct` induction.** The pin's
   `induction t with | zero => … | add … | tmul …` (at the pin's `:107` and `:1562`)
   no longer elaborates: `TensorProduct.inductionOn`
   (`LinearAlgebra/TensorProduct/Defs.lean:135`) is now the registered
   `@[induction_eliminator]` and has only **two** cases (`tmul`, `add`); the old
   `TensorProduct.induction_on` (`:144`, three cases) is deprecated. Both proofs
   were rewritten to `refine TensorProduct.inductionOn t ?_ ?_` with the `tmul` case
   first and the `add` case second; the mathematics is unchanged. (Error was
   `Invalid alternative name 'zero': There are no unhandled alternatives`.)
2. **The `K⟮t⟯` macro.** `open scoped IntermediateField.algebraAdjoinAdjoin` does
   *not* activate it — the scoped macro at
   `FieldTheory/IntermediateField/Adjoin/Defs.lean:529` is scoped to plain
   `IntermediateField`. `open IntermediateField` was added.
   (`SeparatingTranscendental.lean` gets away with only the scoped open because it
   also has `open … IntermediateField`.)

### Reuse (recorded, not re-proved)

- The pin-private `ord_nonneg_of_mem_s12` / `mem_of_ord_nonneg_s12` are **dropped**;
  their call sites use the port's `Place.ord_nonneg_of_mem_vs` and
  `Place.mem_vs_of_ord_nonneg` (`Canonical/WeilDifferential.lean:57/69`). This is the
  one real `port_advise` reuse the work order recorded. `port_advise`'s other
  `--nodes` substitutions are the known `def … : Prop` false positives (the model
  predicates are bespoke; `AUDIT-mathlib-p2.md` §6 confirms none has a mathlib
  analogue).
- **Deliberate divergence from the audit's design note.** The audit suggests
  deleting `uniformizerSubring'`/`''`/`'''` (`:31`/`:75`/`:184`) in favour of the
  port's `Place.uniformizer`. They are kept as private aliases because the *public*
  pin statement `ValSubringKaehlerSpanTop` mentions `Place.uniformizerSubring' v`;
  rewriting it to `v.uniformizer` would change the statement text and force a
  checker `MISMATCH`. Statement fidelity (work order §2) wins over the alias cleanup.
  The aliases are `private`, so they add nothing to the checked surface.

### Inventory correction

The pin's `tools/deps/build/p2_inventory.txt` lists 134 declarations; the true row
count is **140** — the six `instance`s at pin lines 35 (`instSMulCommClass_subring`),
451 (`centerIdeal_isPrime`), 593 (`centerLocalizationSubalgebra_isLocalization`),
597 (`…_isDomain`), 608 (`…_isFractionRing`) and 638
(`centerLocalizationValuationSubring_isDiscreteValuationRing`). All six are
transcribed as `scoped instance`s and activated with
`open scoped AlgebraicCurve.Place` (the pin's `p2m_open`/`p2m_reactivate` pair).

### Checker wiring, builds, verification

- `spec/check_flt_statements.py`: `SOURCES` += the three `Theorems/Thm_*` wrappers
  first, then the three `S_` files; `PORT_FILES` += the two new modules.
- **Checker: 2944 → 3013 identical / 0 mismatched / 0 missing / 30 own-proof**
  (3043 checked) — Δ = +69 public declarations verified, `98 promoted from
  pin-private` (the `+69` is net of the two dropped prelude aliases).
- `flock /tmp/flt_for_human.lock timeout 240 lake build
  FLTForHuman.AlgebraicCurve.Defs.KaehlerTranscendental` → 3.7 s (2578 jobs).
  `…Canonical.HasCanonicalDivisor` → 20 s (2766 jobs); both green, only pre-existing
  linter warnings (`polynomialIsScalarTower` `def`-vs-`theorem`,
  `Set.mem_setOf_eq` deprecation).
- `#print axioms` (probe) on the headline, its `_s12` copy and the two Kähler
  theorems → each exactly `[propext, Classical.choice, Quot.sound]`.
- `spec/RiemannRochConsumer.lean` re-elaborated (bounded) → exit 0, no output.
- Hygiene: no `sorry`/`admit`/`axiom`/bare `import Mathlib`/heartbeat override in
  either module; no whole-tree `lake build`; no git command run.

### Promotion debt — out-of-set declarations resolved locally: **none**

The target reaches only the three measured `S_` files plus already-landed port
declarations (`IsCurveOver.exists_separating_transcendental`,
`HasPrincipalDivisors.exists_divisor`,
`Place.{ord_nonneg_of_mem_vs,mem_vs_of_ord_nonneg,differentialCoeff_unique,ordDifferential_smul,FiniteResidue.finite}`)
and mathlib. Nothing outside the three `S_` files had to be re-provisioned
`private`, so the promotion-debt list is empty (`AUDIT-mathlib-p2.md` §6 found no
stop-early risk either).

### Manager gap round (P2) — the private layer promoted

The worker's out-of-set debt was empty, so the remaining gap was the **private
layer**: 47 declarations the pin `p2m_export`s publicly were kept `private` in the
port. Cross-referencing the module's `private` set against the pin's export
inventory (`tools/deps/build/p2_exports.txt`) and dropping `private` on exactly the
exported ones (backups in `tools/deps/build/p2_backup/`):

- **Checker: 3013 → 3060 identical / 0 mismatched / 0 missing** (3043 → 3090
  checked); `145 promoted from pin-private` (98 → 145), i.e. all 47 verified through
  the checker's dotted-name fallback with **no `OWN_PROOFS` addition**.
- Builds green (`HasCanonicalDivisor` 2766 jobs; full `lake build` **4837 jobs, exit
  0**); `spec/RiemannRochConsumer.lean` exit 0; hygiene clean.
- The promoted set is the pin-public API a later phase would otherwise re-derive:
  the `centerIdeal`/`centerLocalization*` block, `modelInclusion`/`modelAlgebra*`,
  `isIntegrallyClosed_toValuationSubring`, `mem_valuationSubring_of_isIntegral(_subalgebra)`,
  `integralClosure_subset_valuationSubring`, `maximalIdeal_eq_span_uniformizer`,
  `ker_algebraMap_residueField_eq_span`, the Kähler/residue-field helpers, the
  `uniformizerSubring'`/`''`/`'''` aliases and the `_s12` order/coordinate lemmas.
- **Kept `private`:** 15 in the big module + `FF2.exists_basis` in the Kähler module —
  the genuinely pin-private helpers (`ofPrime_congr_s12`, the `*_adjoin_s12` family,
  `inv_s12`, `ordDifferential_D_eq_zero_of_span_eq_top_s12`,
  `span_D_eq_top_of_isUnramifiedAt_s12`, `instSMulCommClass_subring`, …), each
  pin-`private` and not exported.
- Note: the worker's reason for keeping the `uniformizerSubring'` aliases private
  (the public `ValSubringKaehlerSpanTop` statement names them) does not require
  privacy — the aliases can be public without changing any referring statement's
  text, which is what this round did.

### Closeout — scratch files removed

All nine gitignored `Scratch*.lean` probe files (`Scratch.lean`,
`ScratchAuditP2.lean`, `ScratchH1a/H1b/H2/H3.lean`, `ScratchP2.lean`,
`ScratchR.lean`, `ScratchR2.lean`) and the `tools/deps/build/p2_backup/` promotion
backups were deleted after the phase-2 full build passed. The two route audits'
"Scratch evidence" pointers now say so; their classifications remain the record. The
work orders' and this log's mentions of `Scratch*.lean` are historical (the
convention they instructed), not live file references.

## Phase 3 — plan, and set 3.1 (`WORKORDER-P3-1-residue-instance.md`)

**Phase-scoping rename (2026-09-30).** The phase-1 plan `PLAN.md` was renamed
`PLAN-P1.md` (it is the phase-1 operative plan only), and every reference in the
tracked notes, the phase-1/2 work orders, `AUDIT-mathlib.md` and the
`WeilDifferential.lean` module header was updated. `PORTING-RR.md` §3's
seven-row work-item table is now the phase map — each row is a self-contained
phase executed with its own dispatch and review gate — and the new operative plan
`PLAN-P3-1.md` records the decomposition, with row 1 detailed as phase 3.1.

**Phase 3.1 is the `HasCanonicalLocalResidueKStar` producer.** The class and its
API already landed in `Defs/LocalResidue.lean` (phase 1, H3); phase 3.1 supplies
the unconditional instance, from the two pin `Definitions/` files
`Def_AlgebraicCurve_PlaceCompletion.lean` (529 ln, 33 decls) and
`Def_AlgebraicCurve_CanonicalLocalResidueInstanceV2.lean` (2,173 ln, 131 decls).
Measured price (frontier 608, `port_advise`): raw 2,702 → **≈2,600 written**, no
shared prelude, ≈100 lines of substitutions. Split into set 3.1a (the completion
layer) and set 3.1b (the instance), on the dispatch-time assumption that 3.1b
imports 3.1a — **the audit later showed 3.1b does not need it** (see the manager
review below).

**Open risk at dispatch.** `PlaceCompletion` imports the unported 564-line
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean`. Reconnaissance found no
InlineSpecific lemma referenced by name in `PlaceCompletion`, and the port's
newer mathlib has `Valuation.IsRankOneDiscrete.rankOne` as a plain function, so
the import may be droppable; the worker confirms this as the set's scout gate and
ports only the exact declaration(s) needed, if any. A parallel audit
(`AUDIT-mathlib-p3-1.md`) is classifying both files against mathlib `v4.34.0` and
pinning the InlineSpecific disposition.

Dispatched 2026-09-30: set 3.1a (worker `ScratchP3.lean`) and the phase-3.1
mathlib audit (worker `ScratchAuditP31.lean`) in parallel, per the phase-2
precedent. Checker baseline before the set: **3060 identical / 0 mismatched / 0
missing / 30 own-proof** (3090 checked).

## Set P3.1 — the adic-completion layer (`WORKORDER-P3-1-residue-instance.md`, set 3.1a)

**Scout gate — the `InlineSpecific` disposition (2026-09-30).** `PlaceCompletion`
elaborates against mathlib `v4.34.0` plus the port's
`Defs/{Place,Divisor,PushPull}` with **one** declaration unioned from the
unported `Def_DedekindDomain_AdicValuation_InlineSpecific.lean`: the anonymous
instance

    instance : Valuation.IsRankOneDiscrete (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)

at InlineSpecific 215–219 (namespace `IsDedekindDomain.HeightOneSpectrum`). No
InlineSpecific lemma is referenced by name anywhere in the pin body, but the
pin's `kw_ffgc_rankOne_adicCompletion` (pin 264–266) calls
`Valuation.IsRankOneDiscrete.rankOne`, whose `[IsRankOneDiscrete]` instance
argument has no mathlib adic-completion instance in `v4.34.0` (the
reconnaissance's "`rankOne` is now a plain function" is true, but the instance is
still needed). The union is transcribed verbatim in the marked section of the
module; its proof uses only mathlib (`Valuation.IsRankOneDiscrete.mk'`,
`.generator`, `.generator_zpowers_eq_valueGroup`, `.generator_lt_one` and
`adicCompletion_valueGroup_eq`). **Pre/post estimate: 529 pin lines → ≈530
written pre-scout → 572 written post-scout (435 non-blank/non-comment)**, the
delta concentrated in the module header, the specific-import block and the
unioned instance section, partly offset by the two dropped private helpers below.

**Two private pin helpers are import-discharged, not re-proved.** The pin's
`mem_of_ord_nonneg_placeCompletionAux` / `ord_nonneg_of_mem_placeCompletionAux`
(pin 432/441) are the port's public `Place.mem_of_ord_nonneg` /
`Place.ord_nonneg_of_mem` (`Defs/PushPull.lean`), as `port_advise` predicted; the
module imports them and drops the copies. Both were pin-`private` and so never
checker-visible.

**The checker is blind to the `scoped`/anonymous part of this surface.** `+31`
identical for `34` named public declarations: the three `scoped instance`s
(`kw_ffgc_algebraAdicCompletionComap`, `…ComapIntegers`,
`…IntegersToCompletion`, pin 226/234/238) begin a line with `scoped`, which
`DECL_RE` parses on neither side, and the two anonymous instances (pin 9 and the
unioned one) have no name. They are still built and axiom-checked.

**`import Mathlib` → specific imports; one path drift.** The module imports
`Mathlib.RingTheory.DedekindDomain.AdicValuation`,
`Mathlib.RingTheory.Valuation.Discrete.RankOne`,
`Mathlib.Topology.Algebra.Valued.{ValuationTopology,WithVal,NormedValued}`,
`Mathlib.Topology.Algebra.UniformRing` (`Completion.mapRingHom`),
`Mathlib.Analysis.SpecialFunctions.Pow.Real`,
`Mathlib.Topology.Algebra.Module.FiniteDimension` and
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`. Drift:
`Mathlib.LinearAlgebra.FiniteDimensional` is a directory, not a module; `.Basic`
is where `Fintype.linearCombination` lives.

**`Set.mem_setOf_eq` → `Set.mem_ofPred_eq`** in the
`kw_ffgc_uniformContinuous_withValMapAlgebraMap` proof (pin 94): the recorded
`v4.34.0` rename, applied in the proof only.

**Warnings kept, not silenced.** `kw_ffgc_finiteDimensional_adicCompletion`'s two
`letI`s (pin 372–374) draw `linter.style.haveILetI`; the pin's
`first | exact h | (rw [algebraMap_adicCompletion]; exact h)` fallback in
`kwHgfV352_valued_algebraMap_adicCompletion` (pin 426–428) is dead in `v4.34.0`
(`exact h` lands) and draws `linter.unusedTactic` / `unreachableTactic`. Both are
transcribed verbatim; the module builds green with four warnings.

**Measured (2026-09-30, set 3.1a).** `python3 spec/check_flt_statements.py`:
**3060 → 3091 identical / 0 mismatched / 0 missing / 30 own-proof** (3090 → 3121
checked; `+31` = the checker-visible public surface). File-done build
`flock /tmp/flt_for_human.lock timeout 240 lake build
FLTForHuman.AlgebraicCurve.Defs.PlaceCompletion`: **9.5 s wall, 2817 jobs,
green**. `#print axioms` on the full public surface — all 34 declarations (the 29
named non-`scoped` ones, the two `abbrev`s and the three `scoped instance`s):
`[propext, Classical.choice, Quot.sound]`, no exceptions. No `sorry` / `admit` /
`axiom`; no `import Mathlib`.

**Manager review — the audit landed and changed two things (2026-09-30).** The
parallel audit `AUDIT-mathlib-p3-1.md` (617 ln; counts
`PlaceCompletion` 6/21/7 = 34, V2 10/95/26 = 131, total 16/116/33 = 165)
contradicted the worker on the one adaptation the worker thought was forced, and
the manager verified and applied the correction:

- **R1 — the InlineSpecific instance is mathlib's.** The worker unioned it because
  its specific-import block did not include
  `Mathlib.NumberTheory.NumberField.Completion.FinitePlace`, where mathlib
  `v4.34.0` keeps the anonymous `IsRankOneDiscrete` instance for `Valued.v` on an
  adic completion (generic over a Dedekind domain, no finiteness hypothesis;
  audit probe A1). The 24-line verbatim union was replaced by that one import.
  Lesson for the friction log: a name absent from the *imported* modules is not
  the same as absent from mathlib — the §2.2 audit must search the tree, not the
  module's closure.
- **R3 — the pin's global `Algebra O L` instance is dropped.** The pin opens with
  `instance … : Algebra O L` for every `O : ValuationSubring K` (pin line 9); the
  worker transcribed it. mathlib `v4.34.0` now supplies that algebra structure
  (manager probe: `inferInstance` closes), so keeping the pin's copy is a
  global-instance diamond. The module elaborates without it.
- Re-verified after both edits: `PlaceCompletion.lean` **551 ln**; checker
  **3091 / 0 / 0 / 30 own-proof** (unchanged — both dropped declarations are
  anonymous/scoped and invisible); forced `lake build` **6.8 s, green**; sampled
  `#print axioms` (including `kw_ffgc_rankOne_adicCompletion`, which now uses the
  mathlib instance, and `instAlgebraKAdicCompletionIntegers`)
  `[propext, Classical.choice, Quot.sound]`. The module's own build closure grew
  2817 → 3407 jobs from the `FinitePlace` import; wall time is unchanged and the
  number-theory closure is largely already in the port tree.

**R2 — set 3.1b does not need `PlaceCompletion`.** The pin's V2 import is
vestigial: `lg37_completion v := AdicCompletion (maximalIdeal
v.toValuationSubring) v.toValuationSubring`, and grep count is 0 in V2 for every
`kw_ffgc_*` / `kwHgfV352_*` / `adicCompletion` / `algebraMapKIntegers` /
`KwF4gRRTate` name (audit §4/§5, probe D1). 3.1b therefore drops the import and is
**independent** of 3.1a — the work order §0 wording "3.1b imports 3.1a" is
superseded by §4.

**Checker note corrected.** The checker's `DECL_RE` *does* parse a named
`instance` (only `scoped`-prefixed and anonymous ones are invisible), so
`instHasCanonicalLocalResidueKStar` will be statement-diffed; it still needs a real
consumer `example` because a statement check does not exercise the term.

### Set 3.1b-i — the V2 `Place` pole/Laurent layer (pin 1–789)

`Defs/CanonicalLocalResidueInstanceV2.lean`, 552 ln, 58 public declarations
(the pin's block-1 68 rows minus the 10 import-discharged ones).  Checker
3091 → 3149 identical / 0 mismatched / 0 missing / 30 own-proof; forced
`lake build` 6.8 s, green; all 58 public declarations `#print axioms`
`[propext, Classical.choice, Quot.sound]`.

- **`uniformizerSubring`: the audit's import-discharge target is outside the
  mandated import set.**  The audit and the work order replace the pin's
  `def uniformizerSubring` (pin 199) by the port's `Place.uniformizerSubring'`
  (`Canonical/HasCanonicalDivisor.lean:64`), but the task's import list is only
  mathlib plus `Defs/{LocalResidue,IsCurveOver,PushPull,Place}`, and
  `HasCanonicalDivisor.lean` transitively imports
  `Canonical/WeilDifferential.lean` — which the same task forbids importing into a
  `Defs/` module.  Resolution: the pin's one-line `def` body
  (`(IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose`, no
  proof) is transcribed verbatim, which is `rfl`-equal to `uniformizerSubring'`.
  The two dependent statements `coe_uniformizerSubring` (pin 202) and
  `irreducible_uniformizerSubring` (pin 205) then land at the pin text with
  `rfl`/`choose_spec` proofs as the work order intends.  Refactor round: once the
  V2 module may import the canonical-divisor module, replace the body by
  `v.uniformizerSubring'` (a one-line change, no statement moves).
- **`Set.mem_setOf_eq` is deprecated in `v4.34.0`** (use `Set.mem_ofPred_eq`);
  the two `Submodule` `add_mem'`/`zero_mem'` proofs (pin 244–246, 342–344) use the
  new name.  Body-only; no statement changes.
- **`gate_uniformizer_inv_mem_simplePoleSubmodule` (pin 312) is at the pin's
  `AlgebraicCurve` level with an explicit `(v : Place K F)` binder.**  A first
  transcription inside `namespace Place` made `v` an implicit auto-bound variable;
  the checker flagged the statement mismatch (`flt: (v : Place K F) : …`), and the
  theorem was moved out of the namespace.  Lesson: at this pin every declaration
  outside the pin's `section Restrict`/`section DegPos` that writes `(v : Place
  K F)` explicitly must be transcribed at `AlgebraicCurve` level with the binder
  written out.
- **Import-discharged blocks dropped whole.**  The pin's `namespace Place /
  section Restrict` (pin 121–178, six declarations) is the port's
  `restrictInclusion`/`restrictResidueMap` block (`Defs/PushPull.lean`); the three
  pin-private ord helpers (pin 208/223/231) are the public
  `Place.ord_nonneg_of_mem`/`mem_of_ord_nonneg`/`mem_iff_ord_nonneg`; and
  `gate_hasLocalResidue_uniformizer_inv` (pin 308) is
  `Place.gate_localResidue_uniformizer_inv` (`Defs/LocalResidue.lean`).  No
  transcribed statement references any of them except through those port names.
- **Empty pin scaffolding omitted.**  `section PerfectDischarge` (pin 29–34) and
  the three empty sections under `ModularCurve.Ldgr37Ch` (pin 50–93) declare
  nothing; they contribute no namespace a declaration needs and are omitted.  The
  `p2m_*`/`attribute [-instance]`/`attribute [-simp]` scaffolding is dropped as
  usual.





### Set 3.1b-ii — the `Lg37`/Hensel/`KwNo6Pin` engine and the instance (pin 797–2173)

`Defs/CanonicalLocalResidueInstanceV2.lean` appended, **552 → 1696 ln** (part 2
= 1138 ln from the second `noncomputable section`, of which 6 are the added
imports); +63 checker-visible declarations, all 63 pin rows of blocks 2–5.
Checker **3149 → 3212 identical / 0 mismatched / 0 missing / 30 own-proof**
(3179 → 3242 checked); forced `lake build` **13.0 s wall / 2688 jobs, green**
(edit-loop compile 12 s at the 4 M heartbeat cap); the phase headline
`instHasCanonicalLocalResidueKStar` and the whole public surface `#print axioms`
`[propext, Classical.choice, Quot.sound]`.  Consumer `ScratchP3bii.lean`:
`example {K F} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] [PerfectField
K] : HasCanonicalLocalResidueKStar K F := inferInstance` elaborates, and the
instance's `dataKStar`/`localResidue_eq_resStar` are exercised by real terms.

- **`isLocalRing_of_isAdicComplete_maximal` is not in the audit's named import
  set.**  It lives in `Mathlib.RingTheory.AdicCompletion.LocalRing` (line 49), a
  module the audit §6/§8 does not list; `AdicCompletion.{Algebra,Completeness}`
  do not re-export it.  Added that specific import (still no `import Mathlib`, no
  `PlaceCompletion`).  This is the one import the audit under-specified.
- **`AlgEquiv.coe_to_algHom` is misnamed in the audit §6.**  In `v4.34.0` the
  lemma is `AlgEquiv.coe_toAlgHom` (capital `H`; `Mathlib/Algebra/Algebra/Equiv.lean:197`),
  and `coe_algHom` is the deprecated alias (line 202).  Pin 1681's `simpa only
  [AlgHom.comp_apply, AlgEquiv.coe_algHom]` becomes `…, AlgEquiv.coe_toAlgHom`.
- **`IntermediateField.topEquiv_apply` (pin 1365) is an unused simp argument in
  `v4.34.0`.**  The `@[simps!]`-generated lemma no longer matches the goal shape
  after `AlgEquiv.trans_apply`; the `simp only` closes without it, so it was
  dropped from the list.  Body-only, no statement change.
- **`AdjoinRoot.liftAlgHom`'s `h`-binder transparency.**  The pin's
  `(by rw [aeval_def] at hroot; exact hroot)` proof term has type
  `eval₂ (algebraMap K _) αhat p = 0`, while `liftAlgHom`'s binder expects
  `eval₂ ↑(Algebra.ofId K _) αhat p = 0`; the two are `rfl`-equal
  (`Algebra.toRingHom_ofId`) but `rw`'s matcher works at `implicit` transparency
  and so cannot unify them, making the whole `liftAlgHom …` application invisible
  to `AdjoinRoot.liftAlgHom_root`.  Resolution: `sectionOfPrimitiveRoot` is built
  as `let hlift0 : (minpoly K ᾱ).eval₂ (↑(Algebra.ofId K (lg37_completion v)))
  αhat = 0 := by rw [Polynomial.aeval_def] at hroot; exact hroot; { … }` and the
  `liftAlgHom`/`hkey` terms use the let-bound `hlift0`.  The declaration's
  *statement* (its type) is unchanged — only the structure literal became a `let`
  plus literal.
- **Empty pin scaffolding omitted (no declarations, so no namespace is needed).**
  `ModularCurve.Ldgr35Cl` (pin 797–807), `ModularCurve.Ldgr35Cs` (814–824), the
  un-namespaced empty `section`s (828–834 and 918–922), `ModularCurve.Ldgr36Si`
  (842–859, only a `section Generic` of variables), `ModularCurve.Ldgr36Rc`
  (866–914, five sections of variables, one carrying `[HasCanonicalLocalResidueKStar
  K F']`), and the `open ModularCurve.Ldgr36Si/Ldgr36Rc/Ldgr35Cs` in `Lg37`;
  `ModularCurve.Lg37.MovedCarrier` (pin 964–970, only a `variable
  [HasCanonicalLocalResidueKStar K F']`); the `open ModularCurve.Ldgr37Ch` and
  `attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial` calls; the
  three `RatProduction` sections (pin 1284–1291, 1333–1337, 1521–1528, only
  `variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]` and the
  `AlgebraicClosure ℚ` copy); and `ModularCurve.KwNo6Pin.WitnessW` (pin
  2117–2122).  Same convention as part 1's omitted `ModularCurve.Ldgr37Ch`
  sections.
- **No private helpers and no out-of-set declarations.**  Part 2 resolved every
  proof inside the pin's V2 file plus mathlib; it added no `private` lemma, and
  the one API gap (`isLocalRing_of_isAdicComplete_maximal`) was closed by import,
  not by a local copy.  3.1b-ii therefore adds **no promotion debt**.
- **Warnings kept.**  Seven `linter.style.haveILetI` warnings from the pin's
  `haveI := map_isMaximal v` / `haveI := isAdicComplete_map v` /
  `haveI : FiniteDimensional …` / `haveI : Algebra.IsSeparable …` uses; the
  linter's `have` suggestion would drop the instance, so the `haveI`s are kept
  verbatim.

### Manager closeout — phase 3.1 ACCEPTED (2026-09-30)

Set 3.1b-ii's own report is above; the manager re-ran every gate independently:

- **Checker** (from `lean/`): **3212 identical / 0 mismatched / 0 missing / 30
  own-proof** (3242 checked) — from 3060 at the phase-3 baseline (`+152`: `+31`
  set 3.1a, `+58` 3.1b-i, `+63` 3.1b-ii).
- **Builds**: forced `lake build
  FLTForHuman.AlgebraicCurve.Defs.CanonicalLocalResidueInstanceV2` → 12.4 s /
  2688 jobs, exit 0; **whole-tree `lake build` → 4853 jobs, exit 0** (the new
  global instances do not disturb any existing module); the only warning is the
  pre-existing `Set.mem_setOf_eq` deprecation in `HasCanonicalDivisor.lean`.
- **Axioms**: `instHasCanonicalLocalResidueKStar`,
  `completionSection_nonempty_generic`, `localResidue_eq_resStar{,ₗ}`, plus a
  sample of the engine (`canonicalLocalResidueDataKStar`, `aCoeff`,
  `mp72a102_t1_exists_completion_root_of_residue_root`,
  `mp72a102_t3_sigma_taylor_expansion`) — all
  `[propext, Classical.choice, Quot.sound]`.
- **Consumer** (the manager's review instrument): `spec/RiemannRochConsumer.lean`
  gained **ZONE F**: `inferInstance : HasCanonicalLocalResidueKStar K F` over
  `[IsCurveOver K F] [PerfectField K]`, and the H3 differentials headline
  consumed **without** an explicit `HasCanonicalLocalResidueKStar` hypothesis
  (compare ZONE E). `lake env lean … spec/RiemannRochConsumer.lean` exit 0.
- **Deliberate drops, all recorded**: the pin's V1 shim
  (`Def_AlgebraicCurve_CanonicalLocalResidueInstance.lean`), the 564-line
  `InlineSpecific` prelude (its one needed declaration is mathlib's), the pin's
  global anonymous `Algebra O L` instance (mathlib supplies it), the empty
  scaffolding sections, and the `p2m_*`/`attribute` scaffolding. No statement was
  changed; no `sorry`/`admit`/`axiom`; no `import Mathlib`.
- **Carried refactor debt (not blocking 3.2)**: V2's transcribed one-line
  `def uniformizerSubring` vs `Canonical/HasCanonicalDivisor.lean`'s
  `uniformizerSubring'` (import-graph reason), and the
  `HasSeparableResidue.of_perfectField*` instances vs the port's
  `hasSeparableResidue_of_perfectField` theorem (frozen-module reason). The final
  promotion round can collapse each pair without moving a statement.

### Closeout — scratch files removed

`ScratchP3.lean`, `ScratchP3b.lean`, `ScratchP3bii.lean`,
`ScratchP3biiAxioms.lean`, `ScratchMgrP3.lean` and `ScratchAuditP31.lean` were
deleted after the phase-3.1 whole-tree build passed. The audit note's and this
log's "scratch evidence" pointers are historical (the convention they instructed),
not live file references.

## Phase 3.2 — scoping, and the P3.1 debt round (2026-09-30)

**Row 2 re-scope.** `port_advise` on `build/pf_core.txt` confirms row 2 is ≈16–17k
written (raw 29,118; 3,378 substitution lines, ~731 of them false positives; 9,526
removable), and shows it is not four files: the master ℙ¹ file shares **572/580
declarations (99%)** with the K base file of row 6, and its only "unique" names are
the `p1PlaceInfty` twins of row 6's `placeInfty`. So the engine is one development
for both endings and row 2 must be split into the engine blocks 3.2a–d plus the two
endings. The measurement, the proposed boundaries and reproduce commands are in
`../topics/riemannRoch/PLAN-P3-2.md`.

**P3.1 debt round — DONE (existing-file reconciliation, the phase's one cascade).**
Both recorded duplications were collapsed without moving a statement:

1. `Place.uniformizerSubring'` moved from `Canonical/HasCanonicalDivisor.lean:64`
   down into `Defs/CanonicalDivisor.lean` (beside `Place.uniformizer`, the same
   `Classical.choose`), and the V2 module's pin-named `uniformizerSubring` is now
   `v.uniformizerSubring'` instead of a second copy of the choose. The move is
   import-graph-correct (a `Defs/` home, not the `Canonical/` module's), which is
   exactly what the 3.1b-i worker had flagged as unreachable.
2. `hasSeparableResidue_of_perfectField` moved from `Canonical/WeilDifferential.lean`
   to `Defs/LocalResidue.lean`, next to the `HasSeparableResidue` class, and the V2
   `HasSeparableResidue.of_perfectField` instance is now
   `:= hasSeparableResidue_of_perfectField`. Friction: the file's top-level
   `variable [HasCanonicalLocalResidueKStar K F]` (line 119) leaked into the moved
   theorem and had to be excluded with `omit [HasCanonicalLocalResidueKStar K F] in`
   placed **before** the docstring (after it, Lean parses `omit` as an unexpected
   token).

Re-verified after both: checker **3212 identical / 0 mismatched / 0 missing / 30
own-proof** (unchanged — no statement moved); whole-tree `lake build` green (4853
jobs, 47 s cascade, the one intentional whole-tree build of this round). No
declaration was renamed or restated.

**Build economy for 3.2 (from `PORTING-DeligneSerre.md` §3, applied).** Every 3.2
set lands in a **new** file, so it cannot cascade; the edit loop is
`lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` (writes no
`.olean`), file-done is `flock /tmp/flt_for_human.lock timeout 240 lake build
<module>` (deps only, never dependents), and there is **no bare whole-tree
`lake build` during 3.2** — one at the phase milestone. The debt round above was
the deliberate exception (existing-file reconciliation), and its cascade was
verified once.

### Set 3.2a — the ℙ¹ place/ord dictionary (`WORKORDER-P3-2a-p1-dictionary.md`)

Scoped and dispatched 2026-09-30. Two new files, no cascade: `Defs/PlaceEvaluation.lean`
(the pin's unported `Def_AlgebraicCurve_PlaceEvaluation.lean`, 86 ln: `IsRational`,
`residueInv`, `evalAt`, `evalFun`, `WeilReciprocity`) and `Defs/P1Dictionary.lean`
(the 11 standalone dictionary node files, the biggest being
`ord_placeOfPoint_algebraMap`, 1,263 ln / 67 public). Measured price (`port_advise`
on `build/p32a_nodes.txt`): 22 target files / 91 declarations, raw ≈1,459, 1
substitution (14 ln), no shared prelude → **≈1,445 written**, one worker.

**Mathlib audit for 3.2a (dispatched in parallel, `AUDIT-mathlib-p3-2a.md`).** 3.2a
was first dispatched without a §2.2 audit, unlike 3.1; the manager caught this and
dispatched the audit plus sent the leads to the running worker. The first pass found
two likely large reuse wins, both to be probed rather than assumed:
`Mathlib.FieldTheory.RatFunc.Valuation` (`RatFunc.inftyValuation`/`inftyValuationDef`
with `.X`/`.X_zpow`/`.polynomial`/`.C`) as the ℙ¹ valuation at infinity behind
`ord_placeInfty`/`deg_placeInfty` (and the engine's `p1PlaceInfty`), and
`Mathlib.FieldTheory.RatFunc.Degree` (`RatFunc.intDegree`, `_X`/`_mul`/`_inv`/`_div`)
behind the ℙ¹ divisor-degree block (`principalDivisor`, `degree_principalDivisor`,
`sum_ord_mul_deg_eq_zero`). `Algebra.trace_ne_zero`
(`RingTheory/Trace/Basic.lean:517`) is already the call inside
`hasSeparableResidue_of_perfectField`. The audit note is folded into work order §3
when it lands. **Rule recorded: every 3.2 block gets its `AUDIT-mathlib-p3-2x.md`
before it is accepted.**

**Audit early findings — two scope gaps the measurement missed (2026-09-30).** The
91-declaration `port_advise` reading was a lower bound, as playbook §2.1 warns:

- **Gap A — the dropped `placeOfPoint` block.** The big node needs pin
  `Def_AlgebraicCurve_RatFuncPlaces.lean:236–274` (`placeOfPoint`,
  `placeOfPoint_def`, `placeOfPoint_eq_ofHeightOneSpectrum`, `placeOfPoint_injective`,
  `deg_placeOfPoint`; 5 decls ≈39 ln), which the port **deliberately dropped** from
  `Defs/RatFuncPlaces.lean`. They go into the new `Defs/P1Dictionary.lean`, not the
  existing module (cascade).
- **Gap B — `PlaceEvaluationAlgebra`.** Six unported nodes of
  `Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` (160 ln) —
  `Divisor.evalFun_{add,mul,ne_zero,zsmul,zpow_left,single_sub_single}` — are used by
  the big file's `reciprocity_*` proofs and exist nowhere under `FLTForHuman/`. New
  module `Defs/PlaceEvaluationAlgebra.lean`.

Both are budgeted into 3.2a (still one set, still three **new** files, so still no
cascade) and the running worker was messaged with the exact declarations. The audit
also corrected the work order: the pin's public `le_exp_neg_one_of_lt_one` is
`AlgebraicCurve.le_exp_neg_one_of_lt_one` (outside `namespace Place`), so the port's
private `Place.le_exp_neg_one_of_lt_one` cannot be promoted to match it — transcribe
the 14-line proof. Confirmed reuse: `placeInfty.toValuationSubring =
(RatFunc.inftyValuation K).valuationSubring` is `rfl`, the three tiny ℙ¹ nodes are
one-liners on public port lemmas, and `degree_eq_zero_of_forall_eq_ord` discharges
the `principalDivisor` degree block. Drift: `Polynomial.degree_sub_lt` →
`Polynomial.degree_sub_lt_left`; `dif_pos` → `dite_eq_left`.

#### Set 3.2a — worker result (2026-09-30)

**Landed, green, no cascade.** Three **new** modules (the work order said two; the
audit's Gap B adds the third):

| module | written | build (`lake build <module>`) |
|---|---:|---|
| `Defs/PlaceEvaluation.lean` | 104 | 2.0 s / 2518 jobs (2.8 s wall) |
| `Defs/PlaceEvaluationAlgebra.lean` | 185 | 2.6 s / 2519 jobs (3.6 s wall) |
| `Defs/P1Dictionary.lean` | 1,344 | 5.3 s / 2665 jobs (7.3 s wall) |
| **total** | **1,633** | |

Edit loop was `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false`; no
whole-tree `lake build`; no `.olean` written outside these three modules.

**Checker.** Baseline 3212 / 0 / 0 / 30 (3242 checked) → **3316 identical /
0 mismatched / 0 missing / 30 own-proof (3346 checked)**: +104 checked and +104
identical, i.e. every new public declaration verifies (no exemption, no miss).

**`#print axioms` on the 11 public nodes.** All eleven are
`[propext, Classical.choice, Quot.sound]`.

**Gap A (included).** The five `placeOfPoint` words
(`placeOfPoint`, `_def`, `_eq_ofHeightOneSpectrum`, `_injective`, `deg_placeOfPoint`)
are public in `P1Dictionary.lean`, transcribed from
`Definitions/Def_AlgebraicCurve_RatFuncPlaces.lean:236–274`; that source was already
in `SOURCES`, so they verify with no wiring change. No existing module was touched.

**Gap B (included, as a third module).** `Defs/PlaceEvaluationAlgebra.lean` ports
the whole `Definitions/Def_AlgebraicCurve_PlaceEvaluationAlgebra.lean` law layer at
its pin names (`mem_toValuationSubring_of_ord_nonneg_alt`, `isUnit_mk_of_ord_eq_zero`,
`residue_ne_zero_of_ord_eq_zero`, `evalAt_ne_zero_of_ord_eq_zero`,
`evalAt_mul_of_mem`, `evalAt_algebraMap_eq`, `evalFun_ne_zero_of_forall_ne_zero`,
`evalFun_add_of_forall_ne_zero`, `evalFun_mul_of_forall_mem`, `support_smul_subset`,
`evalFun_natCast_smul_divisor`, `evalFun_zsmul_divisor`,
`evalFun_zpow_left_of_ord_eq_zero`; `evalAt_inv`/`evalAt_zpow` stay `private`),
**minus** its `deg_eq_one_of_isRational`, which `P1Dictionary.lean` already carries
from the ℙ¹ `S_` file (same full name — porting both would collide), **plus**
`evalFun_single_sub_single`, whose only pin statement is its wrapper
(`Theorems/Thm_AlgebraicCurve_Divisor_evalFun_single_sub_single.lean`). The module
is self-contained (imports only `Defs/PlaceEvaluation`), so `P1Dictionary.lean`
imports it and calls the `Definitions/`-file names in the `reciprocity_*` proofs
instead of the pin's wrapper names — no import cycle, statements unchanged.

**`le_exp_neg_one_of_lt_one` disposition.** Transcribed **publicly** at the pin name
`AlgebraicCurve.le_exp_neg_one_of_lt_one` (the audit's name correction), not
promoted from the port's `private` `AlgebraicCurve.Place.le_exp_neg_one_of_lt_one` in
`Defs/Place.lean`; that file is untouched. The dispatch brief's "keep it private"
was superseded by the audit note — the pin declaration is one of the 66 public rows.

**Private helpers kept.** `Place.isUnit_algebraMap` (P1Dictionary),
`RationalFunctionField.ofOption` / `ofOption_bijective` (P1Dictionary), and
`Place.evalAt_inv` / `evalAt_zpow` (PlaceEvaluationAlgebra). The five
`Divisor.evalFun_*` helpers are **not** private: per Gap B they are public in
`PlaceEvaluationAlgebra.lean`. `RatFuncDegree`'s `private`
`exists_sub_algebraMap_intDegree_neg` / `single_add_single_apply_eq_ord` /
`degree_single_add_single` are shadowed across modules by the new public
`P1Dictionary` transcriptions (allowed; the private aliases are module-local).
`exists_sub_algebraMap_intDegree_neg` is transcribed publicly although
`deg_placeInfty` now one-lines through
`deg_eq_one_of_forall_ne_ofHeightOneSpectrum`, because it is one of the 66 rows.

**Out-of-set declarations resolved locally: none.** The six `Divisor.evalFun_*`
were the only out-of-measurement reach; the manager moved them into the new public
module, so no `private` promotion debt was created. The reused public declarations
were imported, not re-proved: `RationalFunctionField.{eq_ofHeightOneSpectrum_or_eq_placeInfty,
placeInfty_ne_ofHeightOneSpectrum}` (RatFuncDegree), `Place.{ord_nonneg_of_mem,
mem_of_ord_nonneg, mem_iff_ord_nonneg}` (PushPull), `Place.placeInfty` /
`finitePlace` / `heightOneSpectrumOfIrreducible` / `deg_finitePlace` /
`degree_eq_zero_of_forall_eq_ord` (RatFuncPlaces / RatFuncDegree).

**Friction / drift.**
- `dif_pos` → `dite_eq_left` (PlaceEvaluation's `evalAt_of_mem`), as the audit
  predicted.
- `Polynomial.degree_sub_lt` → `Polynomial.degree_sub_lt_left` (kept in the
  transcribed `exists_sub_algebraMap_intDegree_neg`).
- The pin's `section DegInfty` opens `variable (K) [DecidableEq (RatFunc K)]`; under
  v4.34 the redundant `(K)` is a hard error (`redundant binder annotation update`)
  that then suppresses the `DecidableEq` instance and makes `K` unknown downstream.
  Dropping `(K)` fixes it; the statement text is unchanged (`variable` binders are
  not on the declaration line).
- The three manager one-liners were applied (`deg_placeInfty`,
  `ord_placeInfty`, `ord_placeInfty_algebraMap`); the pin's long `deg_placeInfty`
  proof body is not transcribed.
- `Finset.prod_zpow` takes explicit arguments in v4.34; the pin's
  `Def_..._PlaceEvaluationAlgebra` spelling happens to already pass them, so no
  change was needed there.

**Manager review — 3.2a ACCEPTED (2026-09-30).** Independently re-run: checker
**3316 identical / 0 mismatched / 0 missing / 30 own-proof** (3346 checked, from
3212); forced per-module builds green (`PlaceEvaluation` 2.0 s / 2518 jobs,
`PlaceEvaluationAlgebra` 2.6 s / 2519, `P1Dictionary` 5.3 s / 2665) with **no
whole-tree build** and only the three new `.olean`s (the Deligne–Serre §3 build
economy held); `#print axioms` on the eleven nodes plus
`RationalFunctionField.{placeOfPoint_injective, deg_placeOfPoint,
ord_placeOfPoint_X_sub_C, principalDivisor_isPrincipal}` all
`[propext, Classical.choice, Quot.sound]`; hygiene clean.

The final `AUDIT-mathlib-p3-2a.md` (532 ln; 5 SUBSTITUTE / 81 PROOF-INGREDIENT / 8
BESPOKE over 94 in-set rows + 11 out-of-set rows) corrected one of the manager's
leads: the `principalDivisor` degree block reduces to the port's
`degree_eq_zero_of_forall_eq_ord`, **not** to `RatFunc.intDegree`. The
measurement-gap lesson is the round's main finding: the 91-declaration
`port_advise` reading missed both `placeOfPoint` and the whole
`PlaceEvaluationAlgebra` layer, and only the §2.2 audit found them — so **3.2b–d
are each audited before acceptance**. Carried debt: `P1Dictionary`'s public
transcriptions of `RatFuncDegree`'s private `exists_sub_algebraMap_intDegree_neg` /
`single_add_single_apply_eq_ord` / `degree_single_add_single` (cascade avoidance;
promote the `RatFuncDegree` copies in a later round). Scratch files removed:
`ScratchP32a.lean`, `ScratchAuditP32a.lean`, `ScratchMgrP32a.lean`.

## Workflow doc, and set 3.2b (2026-09-30)

**`WORKFLOW.md` written** (topic dir) — the operating procedure distilled from
phases 1–3.2a: the measure → audit → dedup → work order → dispatch → review →
closeout loop, the concrete commands, the Deligne–Serre build economy, the checker
wiring conventions, the work-order skeleton, the review checklist, the refactor
round, and the seven failure modes that actually bit (measurement-gap lower bound,
mathlib-name absence, global-instance diamonds, checker blind spots, v4.34 drift,
`p2m` instance disables, `variable` binder quirks).

**3.2b scoped and dispatched.** Row 2's remaining engine is ported as **ordered
chunks of the master file** into one new module `Defs/P1ResidueCore.lean` (the
plan's role labels guide the understanding, but the module is one role — the ℙ¹
residue core — and the chunk boundaries are the pin's own declaration order, to
avoid reordering an intricate dependency chain). Chunk 1 = declarations #0–#144
(pin 295–3387; inventory `tools/deps/build/p32_master_inventory.txt`). Measured for
the four engine files together (`build/p32_engine_advise.log`): 279 substitutions /
5,477 lines, 166 shared names / 8,251 removable, so the union is far below the
25,439 raw. The decisive dedup: phase **3.1b-ii already ported the general
machinery** (`ModularCurve.Lg37.Lg37CompletionSection`, the `Mp72a102T1/T3`,
`Mp72a103T2` engine, `Place.canonicalLocalResidueDataKOfExtend`, the `KwNo6Pin.aCoeff*`
block), so 3.2b–e only write the **ℙ¹-specific** computation; the rest is import.
Dispatched with a parallel `AUDIT-mathlib-p3-2b.md`; work order
`WORKORDER-P3-2b-p1core-1.md`.

### Set 3.2b — worker result (2026-09-30)

New module `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`, **848 written
lines**, declarations #0–#144 (pin 295–3387) of the master ℙ¹ `S_` file. Checker
**3316 / 0 / 0 / 30** (3346 checked) → **3356 / 0 / 0 / 30** (3386 checked); the
new public surface is 40 declarations; `#print axioms` on all 40 is
`[propext, Classical.choice, Quot.sound]`. Forced per-module build green (2.2 s
warm / 7.4 s cold, 2842 jobs) with only `P1ResidueCore.olean` written (no
whole-tree build, no cascade); the consumer wire test still passes.

**Substitutions imported (do not re-prove).** Of the 145 in-set declarations, 83
have an advise substitution; after the false-positive check the load-bearing
imports are: `ModularCurve.Lg37.{lg37_completion, lg37_residueHat,
lg37_residueHat_algebraMap, Lg37CompletionSection}`, the whole
`Mp72a102T1`/`Mp72a102T2`/`Mp72a102T3` engine and the
`uniformizerSubring`/`simplePoleSubmodule`/`poleSubmodule`/`laurentTailCoeff`
layer (`Defs/CanonicalLocalResidueInstanceV2.lean`), the promoted ord interface
and `isUnit_mk_comap_iff`/`exists_ord_algebraMap_pos`/`ramificationIndex_*`
(`Defs/PushPull.lean`), the ℙ¹ dictionary
(`Defs/{RatFuncPlaces,P1Dictionary}.lean`), `Place.mk_mem_maximalIdeal_iff`
(`Genus/Index.lean`), and the `ValSubringKaehler*`/
`valSubringKaehlerSpanTop_of_polynomialFormallyUnramified` block
(`Canonical/HasCanonicalDivisor.lean`). The three advise "false positives" were
checked with the checker: `OrdDifferentialWellDefined` is genuinely unported and
transcribed; `ValSubringKaehlerSpanTop` and `ValSubringPolynomialFormallyUnramified`
have real same-name homes in `Canonical/HasCanonicalDivisor.lean` and are imported.

**The `p1PlaceInfty` decision (the round's one structural call).** The pin's
`p1PlaceInfty` and the port's `RationalFunctionField.placeInfty` are the same
`Place.mk` (only the `Nontrivial` value-group instance is supplied differently,
so the proofs are proof-irrelevant), and five in-set names
(`deg_placeInfty`, `inftyValuation_isEquiv_adicValuation`, rows 29–32,
`ord_placeInfty_X`) are already public in the port **at the same name** but stated
for `placeInfty`. Re-transcribing them would be a redeclaration. We therefore
land `@[reducible] def p1PlaceInfty : Place K (RatFunc K) := placeInfty K`: the
pin statement text (`: Place K (RatFunc K)`) is unchanged, the pin name stays
available for chunks 3.2c–e, and reducibility lets the imported `placeInfty`
lemmas elaborate against `p1PlaceInfty` goals without any statement rewrite.

**Public-in-pin, private-in-port declarations transcribed** (the port copies are
inaccessible): `Place.isUnit_mk_comap_iff` (pin 703; port private in
`Defs/PushPull.lean`), `Place.isPrincipalIdealRing_comap` (pin 750; port private),
`RationalFunctionField.finite_setOf_valuation_ne_one` (pin 1000; port private in
`PrincipalDivisors/RatFuncDegree.lean`),
`AlgebraicCurve.finite_setOf_ord_ne_zero_of_finiteDimensional` (pin 2457; port
private in `PrincipalDivisors/Transcendence.lean`). Transcribing the last one
required local `private` copies of `Place.aeval_mem` (pin 2353) and
`Place.exists_coeff_ord_ne_zero` (pin 2361) — **in-set rows, not out-of-set
promotion debt**; the only drift was `Set.mem_setOf_eq` →
`Set.mem_ofPred_eq` in v4.34 (proof-body only, statement unchanged).

**Private helpers kept** (pin names, all invisible to the checker):
`Place.ord_add_eq_min` (478), `Place.algebraMap_ne_zero` (668),
`Place.ord_add_eq_left` (829), `Place.aeval_mem` (2353),
`Place.exists_coeff_ord_ne_zero` (2361), `Place.chartHom` (2418),
`Place.inv_algebraMap_mem` (2424). The private `Place.uniformizerSubring'`
(1223), `instSMulCommClass_subring` (1227),
`kaehlerMap_subring_D_uniformizer` (1230), the `uniformizerSubring''`/cotangent
block (2509–2569) and the `ag9b14c_*` row (1856) are unused in this chunk and
imported/omitted respectively (`uniformizerSubring'` is public in
`Defs/CanonicalDivisor.lean`; `kaehlerMap_subring_D_uniformizer` and the
cotangent block are public in `Canonical/HasCanonicalDivisor.lean`).

**Mathlib note.** `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`
is not reachable from the four imported port modules; the module adds
`import Mathlib.Algebra.Polynomial.PartialFractions` (the pin reached it through
`import Mathlib`).

**Out-of-set declarations resolved locally: none.** Everything transcribed is an
in-set row; no frozen module was edited.

**Promotion debt.** None added — but the manager may wish a later refactor to
promote `RatFuncDegree.finite_setOf_valuation_ne_one` and
`Transcendence.{aeval_mem, exists_coeff_ord_ne_zero,
finite_setOf_ord_ne_zero_of_finiteDimensional}` so 3.2c–e can import instead of
carrying the private copies.

**One checker subtlety.** Appending the master `S_` file to `SOURCES` reclassifies
some *existing* port declarations from the "promoted from pin-private" bucket to
the public bucket (promoted 145 → 132, identical 3316 → 3356): `find` accepts any
source with a matching statement, so adding candidates can only convert a miss
into a hit. `0 mismatched / 0 missing` and the 30 own-proof exemptions are
unchanged.

**Manager review — 3.2b chunk 1 ACCEPTED (2026-09-30).** Independently re-run:
checker **3356 identical / 0 mismatched / 0 missing / 30 own-proof** (3386 checked);
forced `lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore` green (2.1 s warm /
7.4 s cold, 2842 jobs, only this module's `.olean` moved); `#print axioms` on the
sampled public surface (`OrdDifferentialWellDefined`, `principalAdele`,
`p1PlaceInfty_ne_ofHeightOneSpectrum`, `Place.{isUnit_mk_comap_iff,
isPrincipalIdealRing_comap}`, `finite_setOf_valuation_ne_one`,
`finite_setOf_ord_ne_zero_of_finiteDimensional`) all
`[propext, Classical.choice, Quot.sound]`; hygiene clean. The `AUDIT-mathlib-p3-2b.md`
(631 ln; 108/30/7) was folded into the work order §3; its correction that
`ord_ofHeightOneSpectrum_of_span` is row #145 (so it opens 3.2c) is applied.
**3.2c** (rows #145–#289, pin 3388–6744) is dispatched with a parallel
`AUDIT-mathlib-p3-2c.md`. Refactor debt offered: promote
`RatFuncDegree.finite_setOf_valuation_ne_one` and the `Transcendence` privates so
3.2c–e import instead of re-carrying them.


### Set 3.2c — worker result (2026-09-30)

Append-only additions to `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean`:
declarations **#145–#289** (pin 3388–6744) of the master ℙ¹ `S_` file. Module
**848 → 2429 lines** (1581 appended, of which 3 are linter options; 1578 written
Lean). Checker **3356 / 0 / 0 / 30** (3386 checked) → **3422 / 0 / 0 / 30**
(3452 checked): +66 public statements, the other 9 of the 75 transcribed
declarations are pin- or locally-`private` (the checker also skips `scoped
instance`, so `instHasPrincipalDivisors` is landed but not statement-diffed).
Forced `lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore` green:
**11.62 s** cold (olean removed, 2842 jobs), and a `.olean`-mtime sweep shows
only `P1ResidueCore.olean` moved (no cascade, no whole-tree build).
`#print axioms` on all **67** new public declarations →
`[propext, Classical.choice, Quot.sound]`. Consumer wire test
(`spec/RiemannRochConsumer.lean`) still exits 0. Hygiene clean.

**Substitutions imported (70 rows omitted, import do not re-prove):**
rows #145–#155 (`Defs/P1Dictionary.lean` + `PrincipalDivisors/RatFuncDegree.lean`:
`ord_ofHeightOneSpectrum_of_span`, `ord_placeInfty*`,
`single_add_single_apply_eq_ord`, `degree_single_add_single`, `principalDivisor*`,
`degree_eq_zero_of_forall_eq_ord*`); #165–#176 (`Defs/PlaceDictionary.lean`);
#177–#186 and #189 (`Canonical/HasCanonicalDivisor.lean`, the public
`_root_.AlgebraicCurve.Place.*` block, so the pin-`private` copies are not
restated); #192–#202 and #208–#211 (`Defs/CanonicalLocalResidueInstanceV2.lean`,
including the unprimed `higherPoleCorrection*`, `aCoeff`, `Mp72a103T2.*`);
#237 `Divisor.degree_eq_sum_support` (`Genus/Index.lean`); #251–#253
(`HasCanonicalDivisor`); #254–#270 (`V2` `KwNo6Pin` `aCoeff_*`/`clearPow_mem`/
`resStar*`/`canonicalLocalResidueDataKStar`). The `port_advise` false positives
(`def … : Prop` matched against `EisensteinWeightOne.E1Chi3IsModular`) for
`OrdDifferentialWellDefined`, `ValSubringKaehlerFinite`,
`ValSubringEssFiniteType`, `KaehlerRankOne`, `RamificationInertiaIdentity`,
`CanonicalLocalResidueKDifferentialCoordIndep` were checked by hand; the first has
a real same-name home in chunk 1, the others are genuinely new and transcribed.

**Pin-private helpers kept `private`:** #187
`isSeparable_residueField_of_charZero_of_finiteResidue`, #188
`subsingleton_polynomialKaehler_of_charZero_of_finite`, #204–#207 the
`ag9b15u_*` block, #220 `uniformizer_ne_zero'`, #239
`_root_.AlgebraicCurve.Place.ord_prod` (used via `w.ord_prod` in #240).

**Out-of-set declarations resolved locally (promotion debt).** Rows #240/#241/
#243/#244 state the `F ≃ₐ[K] F` Galois action on `Divisor`, whose layer the port
deliberately deferred (`Defs/SemilinearAut.lean:7`, "the Divisor/`Pic0`
action-and-torsion section is deferred"). Transcribed locally `private`, statements
verbatim from `Definitions/Def_AlgebraicCurve_DivisorClassGroup.lean`:
`Place.ord_smul` (:314), `Place.deg_smul` (:348), the `F ≃ₐ[K] F`
`MulAction (Place K F)` underlying :285/:305, the `Divisor` `DistribMulAction`
(:359), `Divisor.smul_def` (:361), `smul_single` (:364), `smul_apply_smul` (:369),
`smul_apply` (:374), `degree_smul` (:380). All are proved from the ported
`SemilinearAut.ord_smul`/`deg_smul`; `simpa` will not unfold the `SMul` instance,
so `change (SemilinearAut.ofAlgAut σ • v) …` is used first. A second local copy
`Place.ord_add_eq_left'` (statement from pin 829) was needed because the chunk-1
twin is `private` in this same module. Promotion candidates: port that
`DivisorClassGroup` block into `Defs/SemilinearAut.lean`, and make
`P1ResidueCore`'s `Place.{ord_add_eq_left, ord_add_eq_min}` public so 3.2d–e
import them.

**Inventory / advise gaps.** The brief's row list was stale: rows #156–#164 had
already been merged into `P1ResidueCore.lean` and row #237 into `Genus/Index.lean`
(the inventory marks neither), which cost time on `already declared` errors. The
`AUDIT-mathlib-p3-2c.md` did not land during the round; the substitutions above
were checked against the imported modules directly.

**Drift.** `Finsupp.mapDomain_apply (h_inj) …` → `Finsupp.mapDomain_apply_of_injective
(h_inj) …`; `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right`;
`Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (proof bodies only; statements unchanged).

**Manager review — 3.2c chunk 2 ACCEPTED (2026-09-30).** Independently re-run:
checker **3422 identical / 0 mismatched / 0 missing / 30 own-proof** (3452 checked);
forced build green (1.9 s warm / 11.6 s cold, 2842 jobs, no cascade); `#print axioms`
on `two_le_ord_placeInfty_p1PrincipalPartAtom`, `ratFuncDXCoeff`,
`IsCurveOver.kaehler_free_rank_one` clean; hygiene clean. The 668-line
`AUDIT-mathlib-p3-2c.md` (72/67/6) was already folded into the work order §3 —
the worker's "audit never landed" was a timing artefact. Carried **promotion debt**:
the `F ≃ₐ[K] F` divisor-action layer (`Place.ord_smul`/`deg_smul`, the
`MulAction`/`DistribMulAction` instances, `smul_*`, `degree_smul`) is transcribed
`private` from `Def_AlgebraicCurve_DivisorClassGroup.lean` for rows
#240/#241/#243/#244; `Defs/SemilinearAut.lean` deferred it, so a later round either
promotes it there or the engine keeps the private copies.

**Subject homes (human decision, 2026-09-30).** The generic files get their own
homes rather than being lumped: set **3.2d′** is dispatched to create
`Defs/LocalResidueCalculus.lean` from the 1,244-line generic
`CanonicalLocalResidueDataK.res_differentialCoeff_*`/`p0n22_cpf_res_*` file, **before**
engine chunk 3 (the ℙ¹ core re-uses those names); the ~1,803-line `evalAt`
trace/norm/fiber API gets a `PlaceEvaluation`-adjacent home when the forward cone
reaches it; and the seven `evalAt`/`IsRational` leaves currently in `P1Dictionary`
move to `PlaceEvaluation.lean` in the next refactor round. `P1ResidueCore` stays one
role, split into subject sections, and becomes modules if it passes ~4k lines.

### Set 3.2d′ — worker result (2026-09-30)

New module `FLTForHuman/AlgebraicCurve/Defs/LocalResidueCalculus.lean`, **1,229
lines** (54 of module header/imports/options + 1,175 transcribed), from the pin
`P2M/Sol/S_AlgebraicCurve_Place_CanonicalLocalResidueDataK_res_differentialCoeff_D_mul_pow_inv_eq_zero_of_surjective_algebraMap.lean`
(1,244 ln, 38 declarations) + its `Theorems/Thm_*` wrapper. 26 public
declarations (2 pin rows replaced by imports) + 9 `private` helpers. Checker
**3422 / 0 / 0 / 30** (3452 checked) → **3448 / 0 / 0 / 30** (3478 checked):
+26 public statements, 0 mismatched / 0 missing. Forced
`lake build FLTForHuman.AlgebraicCurve.Defs.LocalResidueCalculus` green:
**8.7 s** wall (6.7 s build, 2689 jobs); an `.olean`-mtime sweep shows only
`LocalResidueCalculus.olean` moved (new file, no dependents, no cascade, no
whole-tree build). `#print axioms` on all 26 public declarations →
`[propext, Classical.choice, Quot.sound]`. Consumer wire test
(`spec/RiemannRochConsumer.lean`) exits 0. Hygiene clean (no
`sorry`/`admit`/`axiom`, no `import Mathlib`).

**Substitutions imported (3, omitted not re-proved):**
`Place.ord_nonneg_of_mem`, `Place.mem_of_ord_nonneg`,
`Place.mem_iff_ord_nonneg` (`Defs/PushPull.lean`, public). The other rows
`port_advise` §1 flagged as "substitute" are only port-`private` in
`Defs/P1ResidueCore.lean` (`ord_add_eq_min` + the four `ag9b15u_*`) and cannot be
imported: this module is a *predecessor* of the ℙ¹ core's later chunks (they will
import it), so the copies are transcribed `private` here and the duplication is
promotion debt. The char-0 `ag9b13t_*` engine the brief pointed at
`Defs/CanonicalLocalResidueInstanceV2.lean` (phase 3.1b-ii) is **not** in the
port — verified by grep over `FLTForHuman/` — so its 44-line row is transcribed
(new, not a substitution).

**Pin-private helpers kept `private` (9):** `ord_add_eq_min` (pin 61),
`differentialCoeff_add''` (107), `differentialCoeff_D_uniformizer_pow_inv`
(113), `ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero`
(196), `ag9b15u_eq_zero_or_one_le_ord_of_residue_eq_zero` (240),
`ag9b15u_exists_unit_normal_form_of_surj` (261),
`ag9b15u_exists_K_truncation_of_mem_poleSubmodule` (310),
`ag9b15u_differentialCoeff_D_unit_mul_uniformizer` (351),
`ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one` (376).

**Promotion debt (private duplicates), pin file:line.** Five of the nine already
exist privately in `Defs/P1ResidueCore.lean` with the same statement:
`ord_add_eq_min` (`P1ResidueCore.lean:131`; pin 61) and the four `ag9b15u_*`
(`P1ResidueCore.lean:1102/1122/1170/1210`; pin 240/261/310/351). The remaining
four have no port home yet: `differentialCoeff_add''` (pin 107),
`differentialCoeff_D_uniformizer_pow_inv` (pin 113),
`ag9b13t_…_natCast_ne_zero` (pin 196) and
`ag9b14c_res_uniformizer_zpow_eq_zero_of_ne_neg_one` (pin 376) — all
local-residue-calculus-private, to promote to a shared home together with the
`P1ResidueCore` copies in the next refactor round.

**Drift.** `if_pos`/`if_neg` → `ite_eq_left`/`ite_eq_right` (7 sites, proof
bodies only; statements unchanged). `include hp hKp in` still works in v4.34.
No `Set.mem_setOf_eq`/`dif_pos`/`degree_sub_lt` on this path.

**Forward references.** None: the file is self-contained; no ℙ¹ specialization
appears.

**Manager review — 3.2d′ ACCEPTED (2026-09-30).** Independently re-run: checker
**3448 identical / 0 mismatched / 0 missing / 30 own-proof** (3478 checked); forced
build green (2.0 s warm / 9.0 s cold, 2689 jobs, no cascade); hygiene clean. This is
the first phase-3 block whose natural subject home was created by decision rather
than by pin file: the generic local-residue calculus is `Defs/LocalResidueCalculus.lean`,
keeping it out of the ℙ¹ core. The audit's correction (the char-0 `ag9b13t_*` engine
is not in the port) was accepted by the worker during the run.

**Duplication recorded (for the 3.2 closeout refactor round).** `LocalResidueCalculus`
and `P1ResidueCore` each carry `private` copies of `Place.ord_add_eq_min` and the
four `ModularCurve.MilneAvAg9bRd15UnitNormalFormLaurentSeed.ag9b15u_*` (the generic
module must precede the core's later chunks, so it cannot import them). Nothing
imports either module yet, so the fix is cascade-free: make the five public in
`LocalResidueCalculus.lean`, import it from `P1ResidueCore.lean`, drop the core's
copies. **3.2d (chunk 3, rows #290–#434, pin 6745–9499) is dispatched**, and it
imports `LocalResidueCalculus` for the generic `p0n22_cpf_res_*` /
`res_differentialCoeff_D_*` names (the master re-uses them 63×).

**3.2d audit — the master file's #307–#404 are a duplicate of phase 2
(2026-09-30).** `AUDIT-mathlib-p3-2d.md` (643 ln; 67 SUBSTITUTE / 65
PROOF-INGREDIENT / 13 BESPOKE) found that **98 of the chunk's 145 rows merely
re-prove the phase-2 pin file `S_AlgebraicCurve_hasCanonicalDivisor_of_isCurveOver.lean`**,
whose port is `Canonical/HasCanonicalDivisor.lean`. 59 rows have exact public
copies there; ten are `private` there (`ofPrime_congr_s12`,
`inv_mem`/`div_mem_of_not_mem_centerIdeal`, `coe_toKSubalgebra`, the
`Transcendental.*_s12`/`inv_s12` at :788–:813) and must be re-landed locally (the
frozen-module rule) as promotion debt. The manager steered the running worker with
this before it transcribed the block. Two other corrections: `Ideal.sum_ramification_inertia`
does not exist in v4.34 (`…_eq_finrank`), and the brief's content list under-scoped
chunk 3 by 98 rows. Lesson for the remaining chunks: **run the audit before
choosing the chunk boundary where possible** — a pin S_ file can duplicate an
already-ported pin file wholesale.

### Set 3.2d — worker result (2026-09-30)

Appended chunk 3 to `FLTForHuman/AlgebraicCurve/Defs/P1ResidueCore.lean` (rows
#290–#434, pin 6745–9499 of the master ℙ¹ `S_` file). Module **2,429 → 3,974
lines** (+4 specific imports, +1 blank, **+1,540 appended**). Append-only: chunks
1–2 are byte-identical; the only header edit is the four added imports
(`Mathlib.RingTheory.Kaehler.Polynomial`, `Mathlib.LinearAlgebra.Basis.Basic`,
`Mathlib.RingTheory.RamificationInertia.Basic`, `Mathlib.Algebra.BigOperators.Field`).

**98 declarations appended** — 82 public statement-checked (the checker parses 79
theorems/defs plus the 3 `ValuationSubring.*` aliases; its `DECL_RE` skips the 3
`scoped instance`s), 13 `private` helpers, 3 `scoped instance`s. Checker
**3448 / 0 / 0 / 30** (3478 checked) → **3530 / 0 / 0 / 30** (3560 checked):
+82 identical, 0 mismatched / 0 missing. Forced
`lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore` green: **16.7 s** wall
(2843 jobs); only `P1ResidueCore.olean` moved (no cascade, no whole-tree build).
`#print axioms` on all 85 reachable public declarations →
`[propext, Classical.choice, Quot.sound]` (one distinct set). Consumer wire test
(`spec/RiemannRochConsumer.lean`) exits 0. Hygiene clean.

**The audit's big dedup applied.** 47 rows (#311–#317, #319–#320, #337–#352,
#363–#370, #373, #394–#406) have exact public copies in
`Canonical/HasCanonicalDivisor.lean` / `Defs/CanonicalLocalResidueInstanceV2.lean`
and were omitted (imported), not re-transcribed. Nine name-translation rows landed
as one-line aliases over the phase-2 `_s12` copies: `eq_top_of_idealOfLE_eq_bot`,
`idealOfLE_ne_bot_of_ne_top`, `eq_of_isDiscreteValuationRing_of_le`, and the six
`IntermediateField.*` (`adjoin_simple_inv`, `algebraMap_comp_equivOfEq`,
`finiteDimensional_of_eq`, `isSeparable_of_eq`, `finiteDimensional_adjoin_inv`,
`isSeparable_adjoin_inv`). New work transcribed from the pin: #290–#306 (ℙ¹ Kähler
prelude, ramification wrappers, deg-one/principal-part), #321–#334, #354–#362
(AdjoinRoot trace engine), #374–#387 (finite-place residue engine), #408–#420
(placeInfty Euler value), #427–#434.

**Out-of-measured-file / private-copy rows resolved locally `private` (10;
promotion debt).** The phase-2 copies are `private`, so they cannot be imported and
were re-landed at the pin names: `ValuationSubring.ofPrime_congr` (pin 7135),
`Place.inv_mem_of_not_mem_centerIdeal` (7892), `Place.div_mem_of_not_mem_centerIdeal`
(7906), `Place.toKSubalgebra` (8415), and the six `Transcendental.*` /
`Algebra.FiniteType.adjoin_singleton` rows (8824/8831/8837/8843/8849/8854). Their
public homes are `HasCanonicalDivisor.lean:372/498/512/755/788–813` (`_s12`
suffixes); the closeout refactor should promote those and delete these copies.

**BLOCKER on the work order's `import LocalResidueCalculus` instruction.** The
order says to add `import FLTForHuman.AlgebraicCurve.Defs.LocalResidueCalculus` and
draw the generic `p0n22_cpf_res_*` / `res_differentialCoeff_D_*` /
`gate_canonicalLocalResidueDataK_uniformizer_inv` names from it. That import is
**impossible without editing frozen code**: `LocalResidueCalculus.lean:384`
re-declares `AlgebraicCurve.gate_canonicalLocalResidueDataK_uniformizer_inv`, which
`P1ResidueCore.lean:1095` (chunk 2) already declares publicly, so importing it is a
duplicate-declaration error. Neither module may be edited (3.2d′ is frozen; chunks
1–2 are append-only), so the import was **omitted**. Rows #290–#434 contain **zero**
references to the generic local-residue names (grep over pin 6745–9499: `p0n22_cpf_`
0, `ag9b15u_` 0, `D_pow_succ_inv` 0, `res_differentialCoeff_D_of_` 0,
`gate_canonicalLocalResidueDataK_uniformizer_inv` 0), so nothing is lost in this
chunk; the 63 master-file references all live in later chunks. The 3.2 closeout
refactor must first drop the chunk-2 `gate_...` copy (or rename the 3.2d′ one)
before any `P1ResidueCore → LocalResidueCalculus` import can be added.

**Drift applied.** `Ideal.sum_ramification_inertia` → `Ideal.sum_ramification_inertia_eq_finrank`
(#297; the `Finset s` form reuses the `FiberOverCount.lean:44–100` bridge recipe,
including the `ramificationIdx'_eq_ramificationIdx` / `inertiaDeg'_eq_inertiaDeg`
conversions); `Polynomial.degree_sub_lt` → `Polynomial.degree_sub_lt_left` (#434);
`Basis.*` → `Module.Basis.*` under `open Module` (the pin's `Basis` spelling is kept
in the declarations); generic `Finset.sum_div` was missing from the import closure
(added `Mathlib.Algebra.BigOperators.Field`); `K⟮t⟯` needs
`open scoped IntermediateField` outside the `IntermediateField` namespace (#427–#434).
`KaehlerDifferential.polynomialEquiv` / `tensorKaehlerEquivOfFormallyEtale` needed
`Mathlib.RingTheory.Kaehler.Polynomial`.

**Forward references.** None: the last row #434 ends at pin line 9499 exactly; no
row past the boundary is reached.

**Manager review — 3.2d chunk 3 ACCEPTED, plus the dedup refactor (2026-09-30).**
Independently re-run: checker **3448 → 3530 identical / 0 mismatched / 0 missing /
30 own-proof** before the refactor; build green (16.7 s, 2843 jobs, no cascade);
axioms clean; hygiene clean. The audit (`AUDIT-mathlib-p3-2d.md`, 643 ln; 67/65/13)
had found that **98 of the chunk's 145 rows re-prove the phase-2 file**, and the
manager steered the worker before it transcribed them; 47 rows were omitted as exact
public copies and 9 landed as one-line `_s12` aliases. Ten pin-private `_s12` rows
were re-landed `private` (promotion debt).

**Blocked import, fixed by a bounded refactor.** The chunk-3 order told the worker
to `import Defs/LocalResidueCalculus`, but both modules declared
`gate_canonicalLocalResidueDataK_uniformizer_inv` **publicly** → duplicate name on
import. The manager's first attempt (a scripted bulk removal of all six duplicates)
mangled section structure and was reverted from a backup; the correct minimal fix
was to remove only the core's unused `gate_…` copy (it had no in-module consumer)
and add the import, leaving the five `private` helpers duplicated (mangled names, no
clash) as recorded debt. Post-refactor: checker **3529 / 0 / 0 / 30** (3559 checked),
forced build green (18.1 s), `LocalResidueCalculus` unchanged. **Lesson:** a
scripted "delete declaration to next declaration" pass crosses `section`/`end`
boundaries — do declaration surgery by hand or with a namespace-aware parser, and
always back up first. **3.2e (chunk 4, rows #435–#579, the residue computation and
the atom-1 headline) is dispatched** with `AUDIT-mathlib-p3-2e.md`.

### Set 3.2e — worker result (2026-09-30)

**Landed.** Append-only chunk 4 of `Defs/P1ResidueCore.lean`: rows **#435–#579**
(pin lines 9500–13173, the end of the master ℙ¹ `S_` file), **2,499 written lines**,
module **3,971 → 6,470 ln**. No statement of chunks 1–3 was touched.

**Inventory undercount (145 → 147).** The inventory `p32_master_inventory.txt` rows
435–579 missed two `scoped instance (priority := low)` rows: pin 10166
`AlgebraicCurve.RationalFunctionField.instDCoordGenerates` (body
`ModularCurve.gate_dCoordGenerates_of_ratFunc_sat ⟨AlgEquiv.refl⟩ v`) and pin 10880
`…instDCoordGeneratesPerfectField` (body = row #493
`exists_ne_zero_smul_dX_of_uniformizer`). Both landed; the checker's `DECL_RE` skips
`scoped instance`, so they are verified by the build only. New declarations after the
28 substitutions: **119 public + 1 local `private` re-land** (#469, below).

**Substitutions imported (28 rows; nothing re-transcribed).** #459
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop` (`HasCanonicalDivisor.lean:987`);
#468 `D_pow_succ_inv`, #469 `Place.differentialCoeff_add''` (private), #470
`Place.differentialCoeff_D_uniformizer_pow_inv` (private), #480/#481
`CanonicalLocalResidueDataK.res_differentialCoeff_D_of_{mem_poleSubmodule,surj}`,
#500 `ag9b13t_res_differentialCoeff_D_mul_pow_inv_of_surj_of_natCast_ne_zero`
(private), and the whole `p0n22_cpf_*` cone #554–#574 — all in
`Defs/LocalResidueCalculus.lean` (`:96/:109/:114/:127/:170/:191`, cone `:397–1182`).
Load-bearing imported names used by the new proofs:
`gate_canonicalLocalResidueDataK_uniformizer_inv` (LRC:384), `D_pow_succ_inv`,
`res_differentialCoeff_D_of_surj`, and row #575's call to the generic
`p0n22_cpf_res_differentialCoeff_D_mul_pow_inv_of_surj`. Omissions #459/468/469/470/
480/481/500/554–574 are the exact 28 the audit lists.

**#459 double-declaration caught before build.** The first generated append kept
`Place.dCoordGenerates_of_valSubringKaehlerSpanTop` and re-declared the imported
`HasCanonicalDivisor.lean:987` copy; the audit flagged it and #459 joined the omit
list. #460 `…_of_valSubringKaehlerFinite_of_charZero` now calls the imported copy.

**One pin-private helper re-landed `private`.** #469 `differentialCoeff_add''` has an
in-append consumer (row #483's proof uses `v.differentialCoeff_add''`); LRC's copy is
`private` and unimportable, so the pin's private declaration was re-landed verbatim
in `P1ResidueCore` (the same recorded-debt pattern as `ord_add_eq_min` and the four
`ag9b15u_*`). #470 and #500 have **no** in-append consumer and are imported outright.
The five helpers private in both modules were left untouched; the new chunk uses
`P1ResidueCore`'s module-local copies.

**v4.34 / scaffolding drift fixed in the append.** The pin's `p2m_open`/`p2m_export`/
`p2m_reactivate`/`p2m_open_scoped` scaffolding was dropped; the name-opening it did
was replaced by `open scoped IntermediateField Polynomial AlgebraicCurve
AlgebraicCurve.RationalFunctionField` plus `open KaehlerDifferential Module
IntermediateField` at the head of the chunk (`p2m_open` also runs `activateScoped`,
so the scoped `instDCoordGenerates*`/`instHasCanonicalDivisorRatFunc*` instances must
be opened explicitly). `K⟮t⟯` needs `open scoped IntermediateField` outside the
`IntermediateField` namespace; `AdjoinSimple.gen` needs `open IntermediateField`. The
pin's `if_pos`/`if_neg`, `Set.mem_setOf_eq` and `Polynomial.degree_sub_lt` drift all
sit in chunks 1–3, not here.

**Chunk-1–3 defect worked around (no frozen edit).** The port's
`p1DifferentialCoeffRegularFinite_of_unitFinite` dropped the pin's `omit … in`, so the
port copy carries four extra instance binders. Row #495
`p1DifferentialCoeffRegularFinite_dX_of_perfectField` therefore inlines the one-line
proof body instead of calling it (statement verbatim). A closeout refactor can restore
the `omit` in chunk 1–3 and revert #495 to the pin's call.

**Verification.** Checker **3529 / 0 / 0 / 30** (3559 checked) → **3642 / 0 / 0 / 30**
(3672 checked), +113 identical / +113 checked. Forced per-module
`flock … lake build FLTForHuman.AlgebraicCurve.Defs.P1ResidueCore` green (26.9 s,
2844 jobs); only `P1ResidueCore.olean` moved (nothing imports it yet). `#print axioms`
on the headline and 20 further public rows (the `p0n22`/`p0n21`
`residueTheoremK_ratFunc…` endings, `kaehlerResidueFunctionalK_dX_eq_zero`, the
`ag9b{12c,13e}_*` Euler rows, the `res_differentialCoeff_D_*` rows, `IsPurelyTranscendentalSimple.congr`,
the two scoped `instDCoordGenerates*` and the two `instHasCanonicalDivisorRatFunc*`)
→ `[propext, Classical.choice, Quot.sound]` throughout. Hygiene clean; no
`sorry`/`admit`/`axiom`/`import Mathlib`. The headline `solution` is published as
`AlgebraicCurve.RationalFunctionField.trace_localResidue_placeInfty_X_pow_eq_zero`
(the wrapper's name). **Out-of-set declarations: none. Forward references: none
(this is the last chunk).** Scratch `lean/ScratchP32e.lean` removed.

## Set P3.2f — the row-2 sibling atom tails (2026-09-30)

**Landing.** `P1/TwoPlace.lean` (122 ln, atom 2) and `P1/DivPow.lean` (713 ln, the
atom-3 `P1Tower` tail). Checker 3645 / 0 / 0 / 30 (3675 checked) → **3701 / 0 / 0 /
30 (3731 checked)**, +56 identical / +56 checked (TwoPlace 6, DivPow 50). Both modules
forced-built green (`TwoPlace` 3.5 s / 2859 jobs; `DivPow` 3578 jobs); only the two
new `.olean`s moved. `#print axioms` on all 51 public nodes → `[propext,
Classical.choice, Quot.sound]`. Hygiene clean; consumer exit 0.

**The work order's atom-3 price was a measurement gap — the real prerequisite is the
Tate agreement.** The 3.2f order priced atom 3 at "43 substituted; 3 new private
helpers" (`gen`, `isIntegral_gen`, `ord_neg'`), because `port_advise` reads only the
target file's same-file closure. The atom-3 headline proof (pin
`S_…_div_pow_eq_zero.lean:2016–2140`) calls the imported
`AlgebraicCurve.completionTraceSum_of_isSeparable` (:2078) and
`AlgebraicCurve.residueTraceCompletionCommute_v2` (:2077). Neither is in the port, and
the second needs `tateCommFinite` / `tateAgreement_v2` / `tateChainRule` /
`tateTraceCompat_of_isSeparable` (pin 1,257 + 4,816 + 2,832 + 4,418 ln ≈ the
8,000-written "Tate agreement" row of `PORTING-RR.md` §3). The port also lacks the
`Def_AlgebraicCurve_TateResidueCurrency` definitions those use (`kaehlerPullback`,
`kwHgfV352_localResidueCompletion`, `kwHgfV352_completionTraceAt`,
`KwHgfV352CompletionTraceSum`, `KwF4R1V391aResidueTraceCompletionCommute`). This is
the WORKFLOW §6.1 failure mode, and §2.2's parallel audit is the instrument that would
have caught it before dispatch.

**Gated rows (not ported).** `RationalFunctionField.trace_localResidue_finitePlace_div_pow_eq_zero`
— gated on the trace-completion commutation (row 3.4) and the Tate agreement (row 3.3);
`AlgebraicCurve.residueTheorem_ratFunc_of_perfectField` — its `solution` builds
`P1FinitePlaceTermZeroMGeTwo` from atom 3's headline, so it is gated on the same two
rows. Both `SOURCES` entries are already wired so the follow-up only appends
`PORT_FILES`.

**One pin-private helper re-landed `private`.** `kwHgfV352_localResidueCompletion`
(pin `Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean:185`) is public in the
pin but the port has no copy; it is re-landed `private` in `DivPow` so the two public
rows `kwHgfV352_localResidueCompletion_{spec,algebraMap}` still verify against the
atom-3 `S_` source. Promotion debt for a later refactor round.

**v4.34 drift.** `isIntegral_algebraMap_iff` now takes no injectivity argument (it uses
`FaithfulSMul`); the pin's `(algebraMap (RatFunc K) L).injective` argument was dropped
in `separable_minP`. The atom-3 `S_` file's `RationalFunctionField.hasPrincipalDivisors`
is not a port name (the port has `IsCurveOver.hasPrincipalDivisors` and
`RationalFunctionField.hasPrincipalDivisors_of_isGalois`); the tower block that needed
it is the headline's, which is gated, so no copy was written.

**Friction.** `P1/DivPow.lean` needs `Defs/PlaceCompletion` explicitly: the R1 comment
in `LocalResidue/Instance.lean` claimed the pin's `PlaceCompletion` import was dropped,
but `Place.adicCompletion` and `kwHgfV352_exists_sub_mem_adicCompletionIntegers` are
only reachable through that import.

## Set P3.3a — the Tate agreement, finiteness half (2026-09-30)

**Landing.** Two new modules: `Defs/TateResidueCurrency.lean` (417 ln, the 27-declaration
shared API home of row 3.3, from
`Definitions/Def_AlgebraicCurve_TateResidueCurrency.lean`) and `Tate/CommFinite.lean`
(883 ln, the 51 public declarations of the `tateCommFinite` cone from
`P2M/Sol/S_AlgebraicCurve_tateCommFinite.lean` — the pin's 53-declaration public surface
minus `ord_nonneg_of_mem`/`mem_of_ord_nonneg`, which the port imports from
`Defs/PushPull.lean`, and minus `solution`, which is published under the wrapper's name
`AlgebraicCurve.tateCommFinite`). Checker **3701 / 0 / 0 / 30 (3731 checked) → 3779 / 0 /
0 / 30 (3809 checked)**, +78 identical / +78 checked (27 + 51). Both modules forced-built
green (`Defs` 3,413 jobs / 39 s, `CommFinite` 3,415 jobs); `.olean` mtimes:
`TateResidueCurrency.olean` 17:58:31, `CommFinite.olean` 18:08:12 — no other library
olean moved in these builds (the `P1/TwoPlace`/`P1/DivPow` oleans at 17:45/17:49 predate
this set and are not ours). `#print axioms` on all 78 public nodes → `[propext,
Classical.choice, Quot.sound]` (three `tateComm*` are subsets). Hygiene clean; consumer
`spec/RiemannRochConsumer.lean` exit 0. Scratch removed. Not committed.

**The pin's `InlineSpecific` file was the one out-of-measured-set reach.** The
`kwF4R1V410a_*` block needs `completionIdeal` and `adicCompletion.mem_completionIdeal_pow`
from `Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pin 299–551),
which set 3.1a deliberately did not port. Following the stop-early rule the closure is
resolved **`private` at the pin's names**: `completionIdeal` (299), `exists_uniformizer`
(430), `uniformizer_ne_zero` (438), `uniformizer_not_isUnit` (447),
`eq_pow_uniformizer_mul_unit` (455), `maximalIdeal_eq_span_uniformizer` (474), the
`IsDiscreteValuationRing (v.adicCompletionIntegers K)` instance (513) and
`mem_completionIdeal_pow` (525). **Promotion debt**: these belong in a future
`Place/Completion.lean` (or the InlineSpecific home) when a consumer needs them publicly.
The pin's `DVR`/`Ring.DimensionLEOne` instances in the same file are not needed and were
not transcribed.

**A second, reverse-direction duplication.** `kwHgfV352_localResidueCompletion` is public
in the pin Def file and now lives publicly in `Defs/TateResidueCurrency.lean`; the
port-side copy in `P1/DivPow.lean:683` is `private` (the 3.2f debt note). The private
`DivPow` copy is now redundant and should be deleted in the refactor round that promotes
the InlineSpecific closure — recorded, not edited (this set touches no existing module).

**v4.34 drift hit four times, all proof-level (statements verbatim).**
1. `HeightOneSpectrum.adicCompletionIntegers` is a `def` (not an `abbrev`), so
   `ValuationSubring.isUnit_of_valued_eq_one` applied at `v.adicCompletionIntegers K`
   fails to unify `hv.v.valuationSubring` with it at implicit transparency. Resolved with
   the private adapter `isUnit_adicCompletionIntegers_of_valued_eq_one` that ascribes the
   valuation-subring type via `show … from x`.
2. `lmulK` is `abbrev (Algebra.lmul K _) fh`; after `ext x` the goal is stated on
   `adicCompletion.toCompletion` projections (`(…) .toCompletion = …`), so the pin's
   `show fh * (gh * x) = gh * (fh * x); ring` does not fire. Replaced with
   `simp only [LinearMap.comp_apply, lmulK, Algebra.coe_lmul_eq_mul, LinearMap.mul_apply']`,
   `simp only [IsDedekindDomain.HeightOneSpectrum.adicCompletion.toCompletion_mul]` then
   `ring`.
3. `Ideal.quotientMap`'s `hIJ : I ≤ J.comap f` and `Ideal.quotientMap_injective'`'s `h`
   do not accept the pin's inline pointwise lambdas under implicit transparency; bind them
   as typed `let hIJ`/`let hJI` and pass `(H := hIJ)`. `rw [Ideal.quotientMap_mk]` also
   missed the syntactically-same term, so use `simp only [Ideal.quotientMap_mk]`.
4. `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`; `WithZero.zero_le _` → `zero_le` (no
   argument); `Int.ofAdd_mul` needed an explicit `import
   Mathlib.Algebra.Group.Int.TypeTags`.

**Qualification friction.** `open AlgebraicCurve.Place` makes the bare namespace
`adicCompletion` resolve to `AlgebraicCurve.Place.adicCompletion`, shadowing mathlib's
`IsDedekindDomain.HeightOneSpectrum.adicCompletion`; the private `mem_completionIdeal_pow`
and the public `isOpen_setOf_valued_le` must be written with their full
`IsDedekindDomain.HeightOneSpectrum.adicCompletion.` prefix in the `kwF4R1V410a` block.
The pin's unused `FunctionField` open is dropped (the port has no such namespace).

**Heartbeats.** The pin raises `synthInstance.maxHeartbeats` to 6,400,000 and
`maxHeartbeats` to 12,800,000 (and one 25,600,000 for
`finiteDimensional_restrictScalarsQuot_pow`). Not transcribed: the whole module
elaborates under the project cap 4,000,000, so this set is not a cap casualty.

**Checker wiring.** `SOURCES` += `Thm_AlgebraicCurve_tateCommFinite` (statement authority
for the one target), then `S_AlgebraicCurve_tateCommFinite`, then
`Def_AlgebraicCurve_TateResidueCurrency`; `PORT_FILES` += the two new modules. Appended
last, no reorder. All 78 public statements diff identical to the pin.

**Audit fold-in (parallel `AUDIT-mathlib-p3-3a.md`).** The audit's one substantive
finding is applied: the pin's `ValuationSubring.{valued_eq_one_of_isUnit,
isUnit_of_valued_eq_one, isUnit_iff_valued_eq_one}` triple is no longer re-proved — the
three names are now one-line aliases of
`Valuation.Integers.{one_of_isUnit, isUnit_of_one', isUnit_iff_valuation_eq_one}` at
`Valuation.valuationSubring.integers hv.v` (statements unchanged, so the checker stayed
3779 / 0 / 0 / 30). The audit's item 3 is applied too: the unported
`Definitions/Def_DedekindDomain_AdicValuation_InlineSpecific.lean` is appended to
`SOURCES` (last, so no earlier match can flip) — the private closure stays `private`, so
it does not change the checked count, but a later promotion will verify against the pin's
originals. `kwHgfV352_localResidueCompletion` is public in the Defs home and remains
`private` in `P1/DivPow.lean`; deleting that copy needs an existing-module edit and is
recorded as debt, not done here.

## P3.3d — Tate trace compatibility (`Tate/TraceCompat.lean`)

**Measurement.** `port_advise --target P2M/Sol/S_AlgebraicCurve_tateTraceCompat_of_isSeparable.lean`
reads 2 targets / 146 declarations; 53 "substitutes". Six of those are false positives:
the checker sees only a `def`'s signature, so every `def … : Prop` with the pin's binder
block matches `EisensteinWeightOne.E1Chi3IsModular` (and two more matched a different-named
`def`). `KwF4gRRTateProjectorIndep`, `KwF4gRRTatePoleWindowImageFinite`,
`KwF4gRRTateCommFiniteGen`, `tateCommDual`, `KwF4gRRTateTraceCompatBlockSum` and
`KwF4gRRTateIntegralBasisCompat` are therefore new, not importable — the same trap the
3.3a audit recorded for four `Prop`s. Real split: 40 importable public, 2 generalise, 94 new.

**Statement text and section variables.** The pin's new rows live under `section`/`variable`
blocks, so the checker's post-name statement text is the *short* form; the port keeps the
pin's variable structure rather than spelling binders explicitly. Dropping a substituted
declaration can strand its `variable … in` line (two consecutive ones are a hard "redundant
binder annotation update" error); the extraction drops any `variable … in` whose target is gone.

**Parallel-set duplication.** 3.3b (`ChainRule.lean`) and 3.3c (`Agreement.lean`) landed
while this set ran. Each pin `tate*` `S_` file re-proves a common trace/projector prelude, so
the three modules share 37 (Agreement) / 21 (ChainRule) last names, including
`finrankTrace_comp_comm`, `SameRangeIdemProjectors`, `KwF4gRRTateProjectorIndep`,
`tateProj_idem`, `alphaMap`/`mulOnRange`/`deltaQuotFactor` and the `tateComm*_add_fst`
family. They build independently, but **a consumer importing two of the three collides**.
Dedup debt for a refactor round (hoist into a shared `Tate/ProjectorPrelude.lean`); not done
here because it edits sibling modules. The checker count is inflated by the copies.

**v4.34 drift (worked examples).**
- `Algebra.TensorProduct.lift`'s `hfg` is now `∀ x y, Commute (f x) (g y)`, not an
  equality: `(fun _ _ => mul_comm _ _)` → `(fun _ _ => Commute.all _ _)` at pin 3952.
- `TensorProduct.induction_on` is deprecated and `inductionOn` has no `zero` alternative;
  the pin's three-case `induction` is kept under `set_option linter.deprecated false in`.
- `rw [NNReal.coe_pow]` cannot match the `letI`-shaped occurrence produced by
  `kw_ffgc_norm_adicCompletion_eq` (`letI` in the theorem *statement*); `push_cast` after
  the norm rewrites is the fix.
- `𝓞` needs `open scoped NumberField`; `⊗[E]`/`→ₐ[R]` need `open scoped TensorProduct`.
- The two duplicate `scoped instance`s (pin 1431/2206) are imported from `Tate/CommFinite.lean`;
  re-landing them is a hard "already declared".

**Checker wiring.** `SOURCES` += `Thm_AlgebraicCurve_tateTraceCompat_of_isSeparable` (statement
authority for the one target), then `S_AlgebraicCurve_tateTraceCompat_of_isSeparable`;
`PORT_FILES` += `Tate/TraceCompat.lean`. Appended last. Checker **3932 identical / 0 mismatched
/ 0 missing / 30 own-proof** (3962) — the +153 over the 3779 dispatch baseline is 3.3b's
`ChainRule.lean` plus this set's 94 net-new checked declarations. Build green
(3496 jobs), `.olean` 18:23; `#print axioms` on the public nodes
`[propext, Classical.choice, Quot.sound]`.

## P3.3c — the Tate agreement (`Tate/Agreement.lean`)

**Measurement / dedup.** `port_advise` reads 2 files / 174 declarations / "46 identical";
8 of the reported substitutes are the `def`-body blind spot (`def … : Prop` →
`EisensteinWeightOne.E1Chi3IsModular`, `def cohenB` → `adicIntegersKSubmod`). Corrected:
**37** pin declarations already identical in the port (35 the shared `tateCommFinite`
chain in `Tate/CommFinite.lean`, 2 `kwHgfV352_localResidueCompletion_{spec,algebraMap}` in
`P1/DivPow.lean`), 3 pin-`private` `Place` helpers public in `Defs/PushPull.lean`, 2
checker-invisible `scoped instance`s imported from `CommFinite`; **133 new checker-visible
declarations**. The `_v2` twin is dropped (PORTING-RR §3).

**The public/private `kwHgfV352_localResidueCompletion` split.** The port has two constants
of that name: public in `Defs/TateResidueCurrency.lean:159` and `private` in
`P1/DivPow.lean:683`. `P1/DivPow.lean`'s public `_spec`/`_algebraMap` are about the private
copy, so they cannot rewrite the public def; the two new additivity/EPS lemmas use private
`_spec₀`/`_algebraMap₀` re-proofs. Refactor debt: drop the `DivPow` private def and restate
the two facts about the `Defs` def.

**Unported `InlineSpecific` slice, again.** `instIsAdicCompleteCompletionIdealAdicCompletionIntegers`
and the `kwF4R1V410a` bridge reach `completionIdeal`/`mem_completionIdeal_pow`/
`exists_ofAdd_natCast_lt` and the uniformizer chain from
`Def_DedekindDomain_AdicValuation_InlineSpecific.lean` (pin 104/299/430/438/447/455/474/525).
Re-landed `private` here (module-local, as 3.3a did) — promotion debt to a shared
`Place/Completion.lean`.

**v4.34 drift (worked examples).**
- `exists_ofAdd_natCast_lt`'s pin proof ends `norm_cast; exact inv_mabs_le y`; in `v4.34.0`
  `norm_cast` leaves `ofAdd (-↑y.natAbs) ≤ y` and `inv_mabs_le` does not match. Re-proved by
  `lift x to Multiplicative ℤ` + `ofAdd_toAdd`/`ofAdd_lt` + `Int.le_natAbs` + `omega`.
- `IsAdicComplete.liftRingHom`/`mk_liftRingHom` live in
  `Mathlib.RingTheory.AdicCompletion.RingHom`, not in the port's import closure; a specific
  import was added.
- `scoped instance` under `open scoped MazurTorsion`: the top-of-file `open scoped` fails
  because the namespace is declared later in the file; place it immediately before its
  consumer. Same for `open ModularCurve.{KwF4R1V394a,KwTateRR3,KwNo6HrouteR,KwOdaDHDR}` —
  the file-local namespaces exist only after their (empty) scaffolding blocks, so the opens
  must follow them.
- `Set.mem_setOf_eq` → `Set.mem_ofPred_eq`, `WithZero.zero_le _` → `zero_le` (4 sites).
- `linter.style.haveILetI` fires on the pin's many `haveI` proofs; disabled file-locally.

**Checker wiring.** `SOURCES` += `Thm_AlgebraicCurve_tateAgreement` (statement authority for
the headline; the pin's `S_` file calls it `solution`), then `S_AlgebraicCurve_tateAgreement`;
`PORT_FILES` += `Tate/Agreement.lean`. Appended last. Checker **4065 identical / 0 mismatched
/ 0 missing / 30 own-proof** (4095); the +133 over the 3.3d close (3932) is this set. Build
green (3583 jobs, 91 s), `.olean` 18:49; `#print axioms` on the public nodes
`[propext, Classical.choice, Quot.sound]`.

## Refactor round — the row-3.3 Tate shared prelude (`Tate/Prelude.lean`)

**Detector.** A statement-normalized diff of the two consumers' `ModularCurve.KwF4gRRTate.*`
declarations (`tools/tmp/dedup_detect_tate.py`, reusing the checker's namespace tracking and
`norm`) finds **exactly 25 shared declarations**: `finrankTrace_{add,neg,zero,sub,congr,
sub_eq,comp_comm,eq_trace_on_superspace}`, `instFinDimRange{Add,Neg,Zero,Sub}`,
`tateComm{,Restrict,Trace,Res}_add_fst`, `alphaMap`, `finiteDimensional_range_alphaMap`,
`range_{sub_le,comp_map_left}`, `tateProj_idem`, and the pole-window pair
(`KwF4gRRTatePoleWindowImageFinite`/`kwF4gRRTate_poleWindowFinite`/
`kwF4gRRTate_poleWindowImageFinite`, `lmul_adicIntegers_subset_poleWindow`). All 25 are
**byte-identical in statement text**; none differ in binders and none differ genuinely (some
proof bodies differ, which is irrelevant for the hoist). `Tate/Agreement.lean` shares no
public name (its copies are `private`), so it was not touched. Because the two copies were
declared in the same namespace, any module importing both was a hard duplicate-declaration
error — the reason set 3.4 could not start.

**Hoist.** `Tate/Prelude.lean` takes the `ChainRule.lean` copy verbatim (lines 64–451) and
both consumers import it; the 25 duplicates are deleted from `ChainRule.lean` (contiguous
lines 66–451) and `TraceCompat.lean` (nine small wrapper blocks). Both consumers keep their
public headlines and unique rows. `Prelude` imports **both** `Defs/TateResidueCurrency.lean`
and `Tate/CommFinite.lean`: the pole-window discharge (`kwF4gRRTate_poleWindowFinite`,
`lmul_adicIntegers_subset_poleWindow`, `kwF4gRRTate_poleWindowImageFinite`) reaches
`kwF4gRRTate_poleWindowFinite_of_DVRQuotPowKFinite`, `poleWindowKSubmod` and
`kwF4gRRTate_clearPole` from set 3.3a, so a `TateResidueCurrency`-only prelude was not
available. Nothing imports `Prelude` except the two consumers, so no cascade.

**Checker.** `PORT_FILES` += `Tate/Prelude.lean` (appended last); no new `SOURCES` entry —
the rows are already sourced by the `tateChainRule`/`tateTraceCompat` `S_` files. Checker
**4044 identical / 0 mismatched / 0 missing / 30 own-proof** (4074), a **−21** step from
4065. The delta is not a statement/binder change: 21 of the 25 hoisted declarations are
checker-visible (the four `scoped instance`s are invisible to `DECL_RE`), and the checker had
been counting those 21 identical rows once per consumer; hoisting them to one file removes
exactly 21 duplicate positive counts. (A dedup round cannot leave the count unchanged while
`PORT_FILES` lists the declaration once.)

**Build economy.** Edit-loop green for `Prelude`/`ChainRule`/`TraceCompat`; per-module builds
green; one whole-tree `lake build` green (4896 jobs). Only **three** `.olean`s moved:
`Prelude` (new, 19:08), `ChainRule` (19:09), `TraceCompat` (19:09) — `Tate/CommFinite` and
`Tate/Agreement` are untouched (they do not depend on the two consumers). The consumer wire
test `spec/RiemannRochConsumer.lean` exits 0. No `sorry`/`admit`/`axiom`/bare `import Mathlib`.

**Debt left.** The pin's `S_` `tateTraceCompat` file also re-proves the 37-row projector
cluster (`SameRangeIdemProjectors`, `KwF4gRRTateProjectorIndep`, `deltaQuotFactor`,
`mulOnRange`, …) that `Tate/Agreement.lean` carries `private`; a later round can hoist that
cluster into `Prelude.lean` too, but it is not a public-name collision today.

## P3.2g — the two gated row-2 ℙ¹ headlines (atom-3 `div_pow`, PF base)

**What landed.** `P1/DivPowEnding.lean` (254 ln) and `P1/PerfectBase.lean` (528 ln), each
importing the `P1/` engine; the atom-3 headline consumes the surviving
`AlgebraicCurve.residueTraceCompletionCommute` (the `_v2` twin is dropped) and
`completionTraceSum_of_isSeparable`, and the PF base case consumes the atom-2/atom-3
headlines. Checker **4010 → 4049 identical** (4040 → 4079 checked), **0 mismatched / 0
missing / 30 own-proof**; the +39 is exactly the two modules' public surface. Per-module
builds green (3607 jobs), only the two new `.olean`s moved; `#print axioms` on all 12 public
nodes → `[propext, Classical.choice, Quot.sound]`; consumer exits 0.

**Friction 1 — a module-local `private` blocks the next file's proof text.** `P1/DivPow.lean`
declares `private def gen` (pin 1446) and the public `P1Tower` lemmas that mention it carry
the mangled private constant in their *types*; a consumer cannot name it. The atom-3 proof
uses `gen` as a term, so the headline re-lands `gen` `private` verbatim — the stop-early
protocol's re-land rule, promotion debt for a future refactor. The same pattern hit
`kwHgfV352_localResidueCompletion_{spec,algebraMap}`: `P1/DivPow.lean`'s public copies are
about *its* private def while the wire proof's goal uses the `Defs/TateResidueCurrency.lean`
public def, so the headline re-lands the pair `private` (`…_spec₀`/`…_algebraMap₀`), exactly
as `Tate/Agreement.lean:907/928` does. Generalisable: a port-`private` def whose public
lemmas are statement-visible forces every later consumer that needs the *term* to re-land it;
a definitions round should promote the union once.

**Friction 2 — a section variable can silently widen a public lemma.** The port's
`surjective_algebraMap_residueField_of_deg_eq_one` (`P1/KaehlerIntegral.lean:474`) sits in
`section AlgClosedDischarge` with `variable (K) [Field K] [CharZero K] […K (RatFunc K)]`, so
its effective signature carries `[CharZero K]` although the pin's atom-3 copy (S_ line 1325)
is `CharZero`-free. The atom-3 context is `[PerfectField K]` (char `p` allowed), so the
public lemma is unusable and the pin's copy is re-landed `private`
(`…_of_deg_eq_one'`). Lesson: check a section-variable lemma's *effective* signature, not its
source text, before promising it as a substitute (`#check @…`).

**Friction 3 — the checker diffs text, so section-variable binders are invisible.** The two
headlines must spell the `Thm_` wrapper's binders *in the declaration text*; my first
`residueTheorem_ratFunc_of_perfectField` used the section's implicit `K` and was flagged
MISMATCH against the wrapper. The eight `kaehlerResidueKernel (K := K) (F := F)` named-arg
calls were likewise flagged against the pin's `kaehlerResidueKernel K F`; fixed by making
`K`/`F` explicit on the two `def`s (`variable (K F) in`, the pin's own device). The checker
is the authority: write the binders as the source copy spells them.

**Build economy.** Edit-loop `lake env lean` on the two files; `lake build` of both modules
under `flock` (3607 jobs, green). `.olean` mtimes: `DivPowEnding` 19:37, `PerfectBase` 19:52;
`DivPow` (17:49) and `TwoPlace` (17:45) untouched. No whole-tree build. No
`sorry`/`admit`/`axiom`/bare `import Mathlib`; no heartbeat raise.

## Refactor round — the P3.2 promotion debt (R1–R10, 2026-09-30)

**Scope.** The residual checklist of `PLAN-P3-2.md` §6, executed as one bounded
refactor round on existing modules, ending in one whole-tree build. Checker
**4049 → 4071 identical / 0 mismatched / 0 missing / 30 own-proof** (4079 → 4101
checked). Whole tree green (4,901 jobs); `#print axioms` on 31 new/moved public nodes
`[propext, Classical.choice, Quot.sound]`; consumer exit 0; hygiene clean.

**Executed.** R1/R2 (promote `ord_add_eq_min` + the four `ag9b15u_*` in
`LocalResidue/Calculus`, delete the `P1/EnginePrelude`/`P1/Differential`/`P1/DivPow`
copies); R3 (home the `F ≃ₐ[K] F` `MulAction` + `Place.ord_smul`/`deg_smul` + the
`Divisor` action in `Defs/SemilinearAut.lean`, delete the `P1/DXCoeff` copies); R4
(delete the dead `P1/TraceEngine`/`P1/FinitePlaceResidue` copies of ten helpers; keep
`HasCanonicalDivisor` the private home); R5 (state `P1/DivPow`'s public
`kwHgfV352_localResidueCompletion_{spec,algebraMap}` about the public
`Defs/TateResidueCurrency` def, delete the private def and the three `_spec₀`/
`_algebraMap₀` re-landings); R6 (public `P1Tower.gen` in `P1/DivPow`, delete the
`P1/DivPowEnding` re-landing); R8 (new public `Place/Completion.lean`, delete the three
Tate private blocks); R10 (move the seven `evalAt`/`IsRational` leaves to
`Defs/PlaceEvaluation.lean`, delete `PlaceEvaluationAlgebra`'s duplicate private
`evalAt_inv`/`evalAt_zpow`). R7 kept (both copies, human). R9 no change.

**R9 was a false positive (corrected).** The checklist called `P1/Dictionary.lean`'s
three specialisations "transcriptions of `RatFuncDegree`'s private helpers". They are
not: the `RatFuncDegree` helpers are *general* (`{vinf}`/`hvinf`), the `P1/Dictionary`
statements are the pin's *specialised* dictionary nodes at `placeInfty`, and the pin
ships both. Promoting the general copies would MISMATCH the checker, so nothing was
done. Measurement lesson (again): "same name" ≠ "same statement"; diff before dedup.

**R4 was deletion, not promotion.** The ten pin-private helpers' `P1` copies turned out
to be dead (used only inside their own block), so promoting them would only have
exposed `_s12`-suffixed names to the checker. Deleting the dead copies closed the
duplication with no statement churn.

**R10 needed a hidden extra step.** `Defs/PlaceEvaluationAlgebra.lean` carries private
`evalAt_inv`/`evalAt_zpow` (the pin's `PlaceEvaluationAlgebra` copies) that collide with
the moved `Place_evalAt_*` node laws; they were deleted so the public home is unique.
`Defs/PlaceEvaluation.lean` gained `import Defs/PushPull` (for `mem_of_ord_nonneg`) and
`open IsDedekindDomain WithZero` (for `exp_log`/`exp_lt_exp`).

**R8: checker-driven spelling.** The hoisted `InlineSpecific` declarations had to be
written with the pin's section-`variable` structure (not explicit binders): the checker
diffs the declaration text after the name, so a promoted prelude must spell binders
exactly as the pin does. Two `Tate/Agreement.lean` calls pass `L`/`u.heightOneSpectrum`
explicitly to `mem_completionIdeal_pow` because the pin's section variables are
explicit. The private instance and the v4.34 `Valued` adapter stay out of the checked
surface (`private`/anonymous).

**Sequencing (build economy).** Edits were grouped by layer — `Defs/` (PlaceEvaluation,
PlaceEvaluationAlgebra, SemilinearAut, Place/Completion), then the `P1/` chain, then
`Tate/` — with one `lake build` per layer; a single whole-tree build closed the round.
No `sorry`/`admit`/`axiom`/bare `import Mathlib`.
