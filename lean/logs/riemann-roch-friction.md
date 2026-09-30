# Riemann–Roch phase-1 friction log

Running ledger for the phase-1 port (`lean/topics/riemannRoch/`). Append as
friction is hit; the generalizable part is folded into `porting-playbook.md` at
the end. Method and set map: [PLAN.md](../topics/riemannRoch/PLAN.md).

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
  `instSumRamificationInertiaOfFiniteDimensional`, and PLAN.md §2's "resolve locally
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
  side (the port has **no** `weilOfKaehler` before H3). Per PLAN.md §2's "resolve
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
files. Recorded in `PLAN.md` and the refactor order.


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

### Method finding (confirmed; for PLAN.md §1 and the playbook)

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
  (`FLTForHuman`, which exists). `PLAN.md` §6/§7 was corrected.
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
  recorded above is **closed** (`PLAN.md` §7 updated).

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

