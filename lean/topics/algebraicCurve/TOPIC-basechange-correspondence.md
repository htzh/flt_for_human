# TOPIC — base change of a curve correspondence along a constant field extension

**Status (2026-10-27): landed and green.** The module is
`FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean` (703 lines, 18 public
declarations): checker **18 ok, 0 mismatch, 0 missing**, warning-free tier-1 build,
`[propext, Classical.choice, Quot.sound]` on every headline probe, consumer zone at 0 errors,
and one hub edit (four `private` → public in the `CentredPlaceRigidity` block). §8 is the
landing record; §2–§6 are the pre-port measurement and plan.

Pinned at `anthropics/fermats-last-theorem` `aa2d8b3`; the port's mathlib is
`v4.34.0`. Measurements are pin lines unless the row says otherwise; every command
used is in §7.

**Subject, in one sentence.** A correspondence `(φ, ψ)` on a curve `F/K` base-changes
along a constant field extension `E ⊆ FE`: the maps extend to `χE : FE →ₐ[E] F'E` into a
constant field extension of the roof, integrality, finiteness and the two along-formulas
transfer, and the base-changed correspondence's coefficients are computed place by place
by counting the `K`-embeddings `σ : F' →ₐ[K] E` with `σ ∘ φ = e`.

**Provenance.** `frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen
--ready --rank-by silo` reports it at **silo 743, `used_by` 2 (cone) / 4 (project),
`needed` 1, hops 1** — the sixth row of the ready shelf. Both cone consumers are
`Pic⁰` rows: `AlgebraicCurve.Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero`
and `AlgebraicCurve.Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`;
outside the cone it is also cited by `AlgebraicCurve.exists_int_matrix_forall_toMatrix_tateModule_rep_correspondence_eq_map`
and the Čerednik–Drinfeld uniformisation node. §14 of the sibling note
([TOPIC-constant-field-extension.md](TOPIC-constant-field-extension.md)) already named
this row as a hub of the constant-field-extension corner, whose nine consumers each drop
a node when it lands.

## 1. The node

| item | value |
|---|---|
| pin wrapper | `Theorems/Thm_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.lean` (54) |
| pin proof | `P2M/Sol/S_AlgebraicCurve_exists_baseChange_correspondence_of_constantFieldExtension.lean` (743) |
| declarations | 22 public + the `solution` package name (23), **zero `private`** |
| imports (pin) | `Mathlib`, `P2M.Util`, `Def_AlgebraicCurve_{Correspondence,IsCurveOver,CanonicalDivisor}`, and eight `Theorems/Thm_*` premises |

The wrapper is the statement authority: one theorem with a 31-binder prefix and a
three-conjunct conclusion whose first conjunct is an eleven-component `∃`
(`F'E`, the two `Algebra`s and three instances, `IsCurveOver E F'E`, `φE`, `ψE`, their
integrality, `FundamentalIdentityAlong`, `FiniteAlong`, `NormFormulaAlong`).

The pin's 22 public declarations, in the file's own layering:

| group | declarations | pin lines |
|---|---|---|
| general place lemmas | `mem_of_valuation_lt_one`, `eq_zero_of_valuation_algebraMap_lt_one`, `centre_unique`, `algebraMap_mem_of_centred` | 33–63 |
| transport of valuations | `valuation_lt_one_iff_inv_not_mem`, `valuation_comap_lt_one_iff`, `valuation_restrictAlong_lt_one_iff` | 69–93 |
| the span lemma | `span_eq_top_of_adjoin_eq_top` | 97–138 |
| tensor-product lift | `liftMap`, `liftMap_tmul`, `liftMap_injective` | 147–168 |
| extending along the constant extension | `exists_extension`, `isIntegral_extension`, `finite_extension` | 183–303 |
| bookkeeping | `essFiniteType_of_fg`, `finiteAlong_of_isIntegral`, `fg_of_finiteAlong` | 311–361 |
| the restriction block | `centred_restrictAlong`, `inertiaDegAlong_eq_one`, `exists_of_correspondence_single_ne_zero` | 369–406 |
| the fibre core | `fibre_centred`, `correspondence_single_apply_centred` | 420–624 |
| headline | `solution` (wrapper: `exists_baseChange_correspondence_of_constantFieldExtension`) | 633–743 |

## 2. Measurements

**`port_advise.py --nodes …`** (2 target files / 24 declarations; port corpus 25,931
declarations):

| section | result |
|---|---|
| substitute | 2 rows: `essFiniteType_of_fg` **importable** (public in `IsCurveOver/ConstantFieldExtensionExists.lean`, identical up to binder spelling); `span_eq_top_of_adjoin_eq_top` **port-private** in `Place/ConstantFieldExtension.lean` |
| port once | `no name is proved in two or more of the target files` |
| generalise | no target name carries two statements; 0 port name clashes |
| drags | `S_`: public surface 23, same-file closure adds **0** helpers |
| same name, different statement (binder spelling) | 4: `mem_of_valuation_lt_one`, `eq_zero_of_valuation_algebraMap_lt_one`, `centre_unique`, `essFiniteType_of_fg` — all four already in the port at `E FE` instead of `E L` |

**`port_plan.py`**: raw 743 / declaration lines 711 / boilerplate 32 / **23 declaration
groups** / already in the port (vetted) 61 lines / **net new math 650 lines**.

**`twin_scan.py --node …`**: `new=1`, `prelude 0/23` over 940 port modules and 17,368
public statements — no twin, public or `private`, and no member of the node is already
public in the port.

**Cone membership.** The node sits in the D–S `needed` set (cone closure 2,308 nodes);
its own target closure is one node, itself, since all eight premises are ported:

| premise (pin) | port home |
|---|---|
| `exists_constantFieldExtension` | `IsCurveOver/ConstantFieldExtensionExists.lean:308` |
| `linearIndependent_of_constantFieldExtension` | `IsCurveOver/ConstantFieldExtension.lean:682` |
| `Place.existsUnique_valuation_sub_lt_one_of_constantFieldExtension` | `Place/ConstantFieldExtension.lean:1679` |
| `fundamentalIdentityAlong`, `normFormulaAlong`, `separableAlong_of_charZero` | `WeilExchange/Transport.lean:303/315/270` |
| `isCurveOver_of_transcendental_of_isSeparable` | `IsCurveOver/Transcendental.lean:102` |
| `hasCanonicalDivisor_of_isCurveOver` | `Canonical/HasCanonicalDivisor.lean:442` |

**Mathlib** (read against both the port's `v4.34.0` tree and the pin's own
`.lake/packages/mathlib`). Present and used: `Algebra.TensorProduct.{lift,basis,basis_apply}`,
`IsFractionRing.{of_field,liftAlgHom,lift_algebraMap}`, `AlgHom.card`,
`IntermediateField.mem_adjoin_iff_div`, `IntermediateField.fg_top`,
`Algebra.EssFiniteType.comp`, `finrank_range_le_card`,
`finsum_mem_eq_finite_toFinset_sum`, `Finset.sum_bij`. Recorded negatives: mathlib has no
tensor-product-lift injectivity from linear independence of the image
(`liftMap_injective`), no transfer of `FiniteAlong`/`finrankAlong` along a constant
extension, and no fibre formula for `Divisor.correspondence` — the three things the node
is about.

## 3. What is new mathematics

- **The extension of an alg-hom along a constant field extension, ~170 lines.**
  `exists_extension` sends `E ⊗[K] F` into `FE` and into `F'E` by the two `liftMap`s, both
  injective by `linearIndependent_of_constantFieldExtension`; the range is a subalgebra `S`
  over which `FE` is a fraction ring, and `χE` is `IsFractionRing.liftAlgHom` of the
  composite. Then `isIntegral_extension` (an integral generating set stays integral) and
  `finite_extension` (a spanning family with a finrank bound). This is the same
  fraction-ring construction as the ported `CentredPlaceRigidity.exists_centred`, one
  roof further out.
- **The fibre formula, ~200 lines.** `fibre_centred` is a counting argument: the
  restrictions `W ↦ W.restrictAlong χE` of the fibre at a centred place `P` are injective
  on centres (`centre_unique`), their cardinality is `finrankAlong K χ = #(F' →ₐ[F] E)`
  (`AlgHom.card`), the ramification indices of the fibre multiply to `finrankAlong E χE`
  (`FundamentalIdentity.sum_ramificationIndex_mul_deg`, `deg = 1` over an algebraically
  closed base), and `finrankAlong E χE ≤ finrankAlong K χ` (`finite_extension`) forces
  every index to be one and the two sets to have equal cardinality. The
  `omega` steps are the arithmetic of that squeeze.
  `correspondence_single_apply_centred` is then `Finset.sum_bij` between the fibre sum and
  the `finsum` over `{σ | σ ∘ φ = e}`.
- **Not new anywhere:** the general place lemmas, the three valuation-transport lemmas and
  `liftMap`/`liftMap_tmul` are 2–10-line wrappers around mathlib facts; they are
  transcribed because the pin states them public.

## 4. Deliverable, and the dedup decisions

**One new module, no other module touched**:
`FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean` — the pin's
development under `AlgebraicCurve.BaseChangeCorrespondence`, with the headline at
`AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension` (the
wrapper's name). The pin's `solution` is the same statement and is not a second
declaration.

**18 public declarations**: the pin's 22, minus the four that the port already holds
(§5), minus `essFiniteType_of_fg` (imported), plus nothing invented.

The four dedup decisions, each mechanical:

1. **`essFiniteType_of_fg` — imported, not restated.** Already public in
   `IsCurveOver/ConstantFieldExtensionExists.lean`, same statement up to binder spelling
   (`port_advise` tier "identical up to binder spelling"). Restating it would be a second
   copy of the same mathematics in the same directory.
2. **The four general place/span lemmas — promoted, not restated** (§5).
3. **`liftMap` stays in this module at the pin's name**, even though
   `CentredPlaceRigidity.mulMap` is its specialisation with a fixed basis: sharing would
   mean the hub importing this module, i.e. an import inversion. Recorded as a
   **deliberately not cut** pair (a 3-line `def`, a `rfl` lemma and a 15-line injectivity
   proof, all `private` on the other side).
4. **`algebraMap_mem_of_centred` is written here**, not in the promoted block: the pin
   states it public in both files but the port has no copy of it yet, so there is nothing
   to promote — and its only consumer is this node.

## 5. The hub edit: four promotions in `Place/ConstantFieldExtension.lean`

The pin states `mem_of_valuation_lt_one`, `eq_zero_of_valuation_algebraMap_lt_one`,
`centre_unique` and `span_eq_top_of_adjoin_eq_top` **publicly in three files** (this node's
`S_` file, the `CentredPlaceRigidity` file, and `span_eq_top_of_adjoin_eq_top` a third time
in the `PlaceReductionCorrespondence` file). The port transcribed them once, in
`AlgebraicCurve.CentredPlaceRigidity`, as `private` — a real result left `private` for the
next theory to re-derive. Four `private` removals make them public at the pin's own names;
the promotion is checker-clean because the pin file that declares them is already in that
module's wire:

| declaration | pin line in the wire | checker |
|---|---:|---|
| `mem_of_valuation_lt_one` | `S_…Place_eq_of_forall_valuation_sub_lt_one…:32` | ok |
| `eq_zero_of_valuation_algebraMap_lt_one` | `:47` | ok |
| `centre_unique` | `:57` | ok |
| `span_eq_top_of_adjoin_eq_top` | `:95` | ok |

Cost measured before the edit: `build_ladder.py --edit Place/ConstantFieldExtension.lean`
→ **4 dependent modules, 3,593 lines, ≈64 s** (tier 2). The module's own checker run after
the edit is **47 ok, 0 mismatch, 0 missing**; its own two `private` siblings
(`adicValuation_lt_one_of_valuation_lt_one`, `ord_ne_zero_of_valuation_lt_one`) stay
`private` — they are not shared.

`algebraMap_mem_of_centred` is *not* added to that hub: it is unused there, and the new
module is its only consumer (§4.4).

The same touch also rectifies the module's one machine token: the pin's `W7XUnram` namespace
(the engine for the constant-field place lift) is renamed `ConstantFieldPlaceLift`, with its
two consumers updated (`IsCurveOver/ConstantFieldExtensionSpan.lean`,
`ModularCurve/XH/JHDescent.lean`). Math clarity is the priority here: the pin's token is a
proof-search label, the mathematics is the lift. All three modules re-check green after the
rename; §8.1 records the full standard audit.

## 6. Route, alternatives, risks

**Route.** The statement layer was transcribed first, verbatim, and passed
`check_port` before a single proof was written — the section/`variable` structure is the
pin's own (`section General/Transport/Lift/Extend/Bookkeeping/Restrict/Fibre`), which is
what makes the textual diff agree. Proofs are then a transcription of the pin's, with
`v4.34.0` tactic drift only (`push Not` → `push_neg`, the deprecated `TensorProduct`
induction) and the six imported premises above in place of the pin's `p2m_export`s.

**Alternatives refused.** *Route the fibre formula through `LinearDisjoint` / a
`Finset.sum_bij`-free bijection*: rejected — the pin's statement is a `finsum` over a set
of embeddings, and the counting argument is exactly the mathematics. *Port the pin's
`solution` as a second declaration*: rejected — same statement as the wrapper's, and the
checker would report one of the two as a duplicate. *Restate the four promoted lemmas in
this module's namespace* (the pin's own spelling): rejected — that is the duplication
§2.4 exists to prevent, and the promoted copy is at the pin's `CentredPlaceRigidity`
names with identical statements.

**Risks, in the order they bite.** (1) The `∃`-packed conclusion: the headline must
assemble eleven components in the wrapper's order, and `IsCurveOver E F'E` /
`FundamentalIdentityAlong E ψE` must be found as instances — the pin's own `haveI` chain
is the transcription, so a failure here is an instance-supply defect, not an editing one.
(2) `fibre_centred`'s integer squeeze: `omega` over `Finset.card` casts; the pin's
`exact_mod_cast` chain is load-bearing. (3) `isIntegral_extension`'s
`IntermediateField.adjoin_toSubalgebra_of_isAlgebraic` rewrite, ported by drift.
(4) Import drift: `IsFractionRing` and `TensorProduct.Basis` must come in narrowly (never
`import Mathlib`).

**Deviation protocol.** A statement that does not match is a stop-and-report: the
statements are checker-clean and frozen. A proof that does not transcribe returns with
the declaration, the pin line and the failing goal.

## 7. Reproduce

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --ready --rank-by silo --top 0                     # the shelf row (silo 743)
python3 port_advise.py --nodes AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension \
  --json build/bc-corr-advise.json                   # substitution / sharing / drags
python3 port_plan.py --json build/bc-corr-advise.json       # the budget (650 net new lines)
python3 twin_scan.py --node AlgebraicCurve.exists_baseChange_correspondence_of_constantFieldExtension
python3 build_ladder.py --edit FLTForHuman/AlgebraicCurve/Place/ConstantFieldExtension.lean

cd ../../lean
python3 spec/check_port.py --force FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean
```

## 8. Landing record (2026-10-27)

| item | value |
|---|---|
| module | `FLTForHuman/AlgebraicCurve/IsCurveOver/BaseChangeCorrespondence.lean`, **703 lines** |
| declarations | 18 public: the pin's 22 − 4 promoted (§5) − `essFiniteType_of_fg` (imported); the pin's `solution` is the headline, at the wrapper's name |
| statement check, before any proof | **18 ok, 0 mismatch, 0 missing** (`--force`, module alone) — the skeleton was written with statements only and checked first |
| hub edit | 4 × `private` removed in `Place/ConstantFieldExtension.lean`; that module re-checks **47 ok / 0 / 0** |
| proofs | 7 by the manager (the definition layer: `liftMap`, `liftMap_tmul`, `liftMap_injective`, the three valuation-transport lemmas, `algebraMap_mem_of_centred`), **11 by one subagent** under WORKORDER-BC1 |
| build | `lake build FLTForHuman.AlgebraicCurve.IsCurveOver.BaseChangeCorrespondence` → **8.3 s, 0 warnings, 0 sorries** |
| checker, after the proofs | **18 ok, 0 mismatch, 0 missing, 0 own, 0 kw** |
| axioms | 6 probes (`headline`, `fibre_centred`, `correspondence_single_apply_centred`, `exists_extension`, `finite_extension`, `liftMap_injective`), all `[propext, Classical.choice, Quot.sound]` |
| tier-2 wave build | `lake build FLTForHuman.ModularCurve.XH.JHDescent …BaseChangeCorrespondence` → 4,313 jobs, exit 0 (JHDescent 54 s; no warning names any edited file) |
| `dedup.py` | new module: 0 clusters over 18 declarations. The touched hub: 2 `shape` clusters, **both deliberately not cut** — they are wrapper-over-engine pairs (the public pin statements `exists_ord_algebraMap_eq_mul_ord` and `exists_comap_eq_toValuationSubring` are one-line wrappers over `rowMain` and `exists_comap_eq_toValuationSubring_core`), and the shape tier normalises away the engine's extra binders |
| `move_dead.py` | new module 0 dead declarations (all 18 reachable from the public API); touched hub 0 (§8 note) |
| consumer | `spec/BaseChangeCorrespondenceConsumer.lean` — **0 errors**: zone A unpacks the headline's `∃` and feeds its `FundamentalIdentityAlong`/`FiniteAlong`/`NormFormulaAlong` fields to `Pic0.correspondence` (so "the base-changed correspondence acts on `Pic⁰`" is executed, not `#check`ed), zone B composes `fibre_centred` with `Divisor.pullbackAlong_single` to get the unramified pullback of a centred place |
| wiring | two `spec-pin:` lines in the module; no `spec/decl_markers.tsv` row (every statement matched by last name); no promotion of a module-local helper; no `OWN_PROOFS` entry |
| hub edits | exactly one, the four-declaration promotion of §5; nothing else outside the module was touched |

### 8.1 The touched module brought to standard

`Place/ConstantFieldExtension.lean` is **not** a legacy node — it is not in
`spec/old_check_stmts.py`'s `PORT_FILES`/`SOURCES`, it carries its own `spec-pin:` wire and is
already tier 1 — so the edit owes no migration off the frozen checker. It does owe the rest of
the standard, which it now meets after the touch:

| standard | state after the edit |
|---|---|
| `spec_pin` | its `spec-pin:` block already existed; unchanged by this wave |
| out of the frozen checker | not listed in either legacy list; nothing to delete |
| silent build | `lake build FLTForHuman.AlgebraicCurve.Place.ConstantFieldExtension` → 14 s, **0 warnings** from the module |
| no build-time blow-up | 14 s for 1,775 lines (measured after the edit); the four promotions add no elaboration and the rename is a name change, so the edit buys no new cost — the *pre-edit* time was not measured, so this is a bound, not a delta |
| no random tokens in names | **one rectified**: the pin's machine namespace `W7XUnram` (the block's own docstring calls the mathematics "the constant-field place lift") is now `ConstantFieldPlaceLift`. Two port modules referenced it, both tier 1 and both re-checked green: `IsCurveOver/ConstantFieldExtensionSpan.lean` (**5 ok / 0 / 0**) and `ModularCurve/XH/JHDescent.lean` (**68 ok / 0 / 0**); the tier-2 build covers the three, exit 0, no warning from any |
| `dedup.py` | 2 `shape` clusters, both wrapper-over-engine (`rowMain`, `exists_comap_eq_toValuationSubring_core`): **deliberately not cut**, with the reason in the table above — the public statements are the pin's and their consumers call them by name |
| `move_dead.py` | **0** dead declarations: every declaration of the module is reachable from its public API |

The remaining pin token in the module's namespaces is `PointPlaceDictionary`, which names its
subject (`Place` ↔ point dictionary); `CentredPlaceRigidity` likewise. Neither is a
proof-search artefact.

One legacy module is *imported* by this wave and untouched:
`IsCurveOver/ConstantFieldExtension.lean` is in `PORT_FILES` (line 4872). It is a premise, not
an edit — no standard is owed, and migrating it is its own small wave.

**Proof-level deviations from the pin** (statements untouched; the checker is the
authority on that): `if_neg` → `ite_eq_right` (`v4.34` deprecation) in
`exists_of_correspondence_single_ne_zero`; the pin's `beta_reduce` dropped in
`correspondence_single_apply_centred` (the goal arrives beta-reduced, so it trips
`linter.unusedTactic`); everything else is the pin's text, including `push Not`
(`push_neg` is the *deprecated* spelling in `v4.34` — recorded as FR-0036 and a drift row),
the `have _hFI := hFI; … clear` unused-hypothesis device, the `omega` cardinality
squeezes, and the `letI`/`haveI` walls.

**Not done here, deliberately**: the four project consumers of the headline are each their
own node; the sibling genus node imports the promoted block rather than restating it; no
`Reserve/` shelf, since nothing was cut.

**What the landing changes on the shelf** (measured after the module built): the D–S
`--ready --rank-by silo` list drops from **125 to 124 candidates** — this row and its 743
silo lines are consumed — and the node no longer appears at all. Its two cone consumers
(`Pic0.exists_principal_geometricCycle_of_lift_correspondence_eq_zero`,
`Pic0.freeAlgebra_lift_correspondence_eq_zero_of_lift_differential_eq_zero`) are **not** in
the 124-candidate list, so each still waits on other unported premises: this node was a
premise of theirs, not their last one.
