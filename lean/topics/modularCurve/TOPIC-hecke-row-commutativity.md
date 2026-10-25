# The Hecke-row commutativity on `J₁(M)` and `J_H(M)` — mathematics, and the shape of the port

Scoped 2026-10-22, after `WORKORDER-HD1` landed the α-row degree pair. This note is the blueprint for
the last layer of the Hecke-row column: the two concrete commutativity theorems
`ModularCurve.heckeOperatorOneBar_comm` (X₁) and `ModularCurve.heckeOperatorHAlong_comm` (X_H), which
are **the same development twice** over two group vocabularies. It records what the port already has,
what is genuinely missing, and the cut the next two work orders implement: `WORKORDER-HD2` (the
substrate, §5 layer 0) and `WORKORDER-HD3` (the pair, §5 layer 1).

**Re-measured 2026-10-25** (§4, §6) with the two headlines run through the pre-port advisor *together*:
the twinship is stronger than the first scoping assumed. 96 of the 100 names occur in both files and
**95 of the 96 are the same statement** once the group vocabulary is substituted; 886 of the 1,873
declaration lines are a verbatim second copy, and neither `S_` file has a single `private` helper. The
price therefore moves from ≈1,350–1,450 to **1,563 lines** transcribed as the pin wrote it; the unified
alternative (827) died at the §5.3 gate, because the two group vocabularies are only *propositionally*
equal. Pin `anthropics/fermats-last-theorem@aa2d8b3`.

## 0. The two statements

```lean
theorem ModularCurve.heckeOperatorOneBar_comm (M : ℕ) [NeZero M] (ℓ ℓ' : Nat.Primes) :
    ModularCurve.heckeOperatorOneBar M ℓ * ModularCurve.heckeOperatorOneBar M ℓ' =
      ModularCurve.heckeOperatorOneBar M ℓ' * ModularCurve.heckeOperatorOneBar M ℓ

theorem ModularCurve.heckeOperatorHAlong_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (ℓ ℓ' : ℕ) [Fact ℓ.Prime] [Fact ℓ'.Prime] (P : ModularCurve.JH M H) :
    ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ' P) =
      ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ'
        (ModularCurve.heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ P)
```

The first is a `Module.End ℤ (JOne M)` identity (via `Module.End.mul_apply`), the second pointwise on
`JH M H`. Both are **unconditional**: for every prime $`\ell`$, including $`\ell \mid M`$ (the `U_ℓ`
case), and for $`\ell = \ell'`$; no coprimality or distinctness is assumed in the statement.

## 1. The mathematics

Fix `M`, a prime `ℓ`, and let `F = x1FunctionField M` (resp. `xHFunctionField M H`) be the
q-expansion function field of $`X_1(M)`$ (resp. $`X_H(M)`$), and
`F_ℓ = x1x0FunctionFieldC ℚ M (M*ℓ)` (resp. `xHTopFunctionFieldC ℚ M H (M*ℓ)`) that of
$`X_1(M)\cap X_0(M\ell)`$. Everything happens over `L = AlgebraicClosure ℚ`, on
$`\bar F = F\otimes L`$ and $`\bar F_\ell = F_\ell\otimes L`$ (in the port: `laurentBaseChange L`).

* **The two legs.** `α_ℓ : F ↪ F_ℓ` is the identity inclusion (the forgetful/identity map of the
  degeneracy cover), and `β_ℓ : F ↪ F_ℓ` is the `q ↦ q^ℓ` substitution, whose image is the
  subfield `QQ ℓ = F.map (qExpAlgHom L ℓ)`. The Hecke operator at `ℓ` is the correspondence
  `β_* α^*` — push-forward along the "new level" leg, pull-back along the "old level" leg:
  on divisor classes, `T_ℓ = (β_ℓ)_* ∘ (α_ℓ)^*`. When `ℓ ∣ M` the α map is used in place of β
  (`HeckeBetaOneDefined` fails), which is exactly the `U_ℓ` operator; that fallback is what makes
  the statement run over **all** primes.
* **The roof square.** The two covers `M ↦ Mℓ` and `M ↦ Mℓ'` are compared inside the
  compositum level `Mℓℓ'`: with `KT t = F_t` (level `M*t`), the roof is
  `roof = KT(Mℓ) ⊔ KT(Mℓ')` inside `BB = KT(Mℓℓ')`, and the square
  `β_ℓ'` then `α_ℓ` versus `α_ℓ` then `β_ℓ'` **commutes** at the level of the two field inclusions
  (`hsq`), because both composites are the identity inclusion of `F` into the roof.
* **The two ingredients that make the square an identity of correspondences.**
  (i) *Push–pull exchange* (`AlgebraicCurve.Divisor.pullbackAlong_pushforwardAlong_eq_pushforwardAlong_pullbackAlong`):
  for a linearly disjoint square of function fields, `β_* α'^* = u_* v^*` — i.e. the two ways around
  the square agree on divisors. (ii) *Degree multiplicativity*
  (`relfinrank_{x1,xH}HeckeCompositum_eq_mul`): `[roof : F] = [KT(Mℓ) : F] · [KT(Mℓ') : F]` for
  coprime `ℓ, ℓ'`, which is what lets the two composites be compared after pushing to `RR` (the sup
  of the two roofs) — the degree of the common leg is the same on both sides, and cancels.
* **Conclusion.** `correspondence (β_ℓ) (α_ℓ) ∘ correspondence (β_ℓ') (α_ℓ')` equals the composite in
  the other order at the divisor level (`heckeDiv_heckeDiv`), hence on `Pic⁰`
  (`AlgebraicCurve.Pic0.correspondence_correspondence_comm`), hence on `J` as `ℤ`-linear maps. The
  case `ℓ = ℓ'` is trivial (`rfl`), and the `HeckeInputs*` predicates — β defined, α/β integral,
  principal divisors on the top field, finiteness along α, the fundamental identity along β, the
  norm formula along α — make the operator the **zero** map when they fail, so the commutativity is
  total.

The `Nice` predicate packages exactly the hypotheses the square needs of an intermediate field
(base-changed top field, principal divisors, finiteness, integrality, separability, non-zero
degree); each vertex of the roof diagram is `Nice`, and `Nice` is monotone along `≤`.

## 2. What the port already has

| piece | module | role |
|---|---|---|
| `heckeAlphaBar`, `heckeBetaBar`, `towerInclBar`, `towerSubstBar`, `heckeSquareBar_commutes` | `ModularCurve/Defs/HeckeOperator.lean`, `Defs/DegeneracyTower.lean` | the **abstract** (`Bar`) row family and its square |
| `HeckeExchangeAt`, `JZero`, `heckeOperatorBar`, `HeckeOperatorsCommuteBar` | `Defs/DegeneracyTower.lean`, `Defs/HeckeModule.lean` | the abstract predicates and operator |
| `heckeExchangeAt_of_WEX`, `heckeOperatorsCommuteBar` (**unconditional**) | `ModularCurve/HeckeCommuteBar.lean` (137 lines, reviewer-owned capstone) | the abstract theorem, proved |
| `relfinrank_x1HeckeCompositum_eq_mul`, `relfinrank_xHHeckeCompositum_eq_mul` | `ModularCurve/HeckeCompositum.lean` | the degree multiplicativity (both sides) |
| `heckeAlphaOneBar`, `heckeBetaOneDefined`, `heckeBetaOneBar`, `heckeDivOneBar`, `heckePic0OneBar`, `HeckeInputsOneAlong`, `heckeOperatorOneAlong` | `ModularCurve/X1/HeckeOperator.lean` | the X₁ row data (no `Module.End` wrapper) |
| the H analogues (`HeckeInputsHAlong`, `heckePic0HBar`, …) | `ModularCurve/XH/HeckeOperator.lean`, `XH/HeckeInputs.lean`, `XH/Operators.lean` | the X_H row data (no operator) |
| `KL`, `roof`/`KL`, `relfinrank_KL_EL`, `finrankAlong_inclusion`, `fieldRange_val_comp_inclusion` | `ModularCurve/XH/HeckeDegree.lean` (HD1) | the base-changed field and degree API the roof uses |
| `QQ`, `roof`, `GA`/`GB`, `BP` (`private`, generalised over `K` and `Γ_H`) | `ModularCurve/HeckeCompositum.lean:539-548` | the compositum's own `Q`/roof block — the same shape of field the pair rebuilds (`FF`/`map (qExpAlg …)` vs `laurentBaseChange`/`qExpand ''`), a §7.4 read (§4) |
| `Pic0.correspondence_correspondence_comm`, the push–pull exchange, ramification/inertia transport, `hasPrincipalDivisors_of_transcendental`, `separableAlong_of_charZero`, `finrankAlong_eq_relfinrank_fieldRange`, `qExpand`/`coeffMap`/`laurentBaseChange` API | `AlgebraicCurve/…`, `ModularCurve/Defs/Laurent.lean` | the engine below both files |

## 3. What is missing

1. **`AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong`** — 22 pin lines, the
   fundamental identity $`\sum_{w \mid v} e_w f_w = [F':F]`$ along an integral separable map. Unported;
   needed by both files (frontier lists it as the second needed node of each).
2. **`ModularCurve.heckeOperatorHAlong`** — `Def_…_XHHeckeOperator.lean:195`, the additive endo on
   `JH M H` (`if HeckeInputsHAlong … then heckePic0HBar … else 0`). `XH/HeckeOperator.lean`'s header
   explicitly left it "off this cone"; it is now on it.
3. **`ModularCurve.heckeOperatorOneBar`** — `Def_…_X1HeckeModule.lean:36`, the `Module.End ℤ`
   wrapper of the already-ported `heckeOperatorOneAlong`. One line, but it is the statement's head.
4. **The generic prelude** — see §4.
5. **The two side modules** — the Γ₁/Γ_H cocycle and q-expansion prelude, the roof and the legs, the
   divisor-level square, and the headline.

**Checked against the port, 2026-10-25.** Every name the two `S_` files *use* that the pin declares
elsewhere resolves in the port except four, and each is small (the fourth, `JH`, is the headline's
binder type and was missed by the first pass — a name-level scan that drops two-letter names):

| pin prerequisite | state in the port |
|---|---|
| `Place.sum_ramificationIndexAlong_mul_inertiaDegAlong` | absent, but its whole proof is 7 lines — `letI := algebraAlong φ`, three `haveI` (`isScalarTower_along`, `isIntegral_along`, `FiniteAlong`/`SeparableAlong` as `Module.Finite`/`IsSeparable`), then `exact Place.sum_ramificationIndex_mul_inertiaDeg v` — and that global form is ported (`AlgebraicCurve/ResidueTheorem/KFamily.lean:63`, same binders, so the fibre form transcribes literally) |
| `heckeOperatorOneBar`, `heckeOperatorOneBar_apply` | absent; one line, `(heckeOperatorOneAlong (AlgebraicClosure ℚ) M ℓ).toIntLinearMap`, with the exact precedent already in the port at `Defs/HeckeModule.lean:37`; `JOne` is ported (`X1/Defs.lean:198`) |
| `JH`, `xHFunctionFieldBar` | `JH` absent (`abbrev JH := Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)`, 2 lines); `xHFunctionFieldBar` is ported (`XH/FunctionField.lean:98`), and `JH` is the type of the `X_H` headline's `P : JH M H` |
| `heckeOperatorHAlong`, `_eq`, `_of_not` | absent, together with the `HeckePic0HBar` block they need — `heckeDivHBar`, `heckePic0HBar`, `heckeDivHBarTranspose`, `heckePic0HBarTranspose` (~35 lines); the X₁ twins are ported **verbatim in shape** at `X1/HeckeOperator.lean:124-152`, and `heckeAlphaHBar`/`heckeBetaHBar`/`HeckeBetaHDefined`/`HeckeAlphaHBarIntegral`/`HeckeBetaHBarIntegral`/`HeckeInputsHAlong` are all ported |

Everything else on the pin's import list is already here: `relfinrank_{x1,xH}HeckeCompositum_eq_mul`,
`qExpand_image_intFormRatiosC_subset`, `hasPrincipalDivisors_of_transcendental`,
`separableAlong_of_charZero`, the three `Divisor` transport lemmas,
`Pic0.correspondence_correspondence_comm`, `finrankAlong_eq_relfinrank_fieldRange`, `Γ₁ ≤ Γ_H`
(`ModularForms/Defs/GammaH.lean:123`), and the `JOneES` premise — the same statement, ported under
another qualifier at `X1/FunctionFieldBaseChange.lean:340`. So the substrate is **three small pieces**,
not a subject; `frontier.py` agrees (each headline: 1 hop, `needed [F terminal]` 2 nodes, and
`--list` prints exactly *themselves + the Place identity*). The audit is name-level: it says the
premises exist, not that their binder blocks match the pin's — that residue is §4's review bucket.

What is left after these three is **the pair itself** (§5) — the 1,563 lines of §6, plus the wiring
(one `spec-pin:` pair per module, and the `Thm_` wrappers' statement diff).

## 4. The twinship, measured

Scoped off the pre-port advisor on the wrappers; re-measured 2026-10-25 with **both headlines taken
together**, which is the unit that matters (the two `Thm_` wrappers come in as siblings): 4 target
files, 202 declarations, against a 24,104-declaration port corpus.

```bash
cd tools/deps
python3 port_advise.py --nodes ModularCurve.heckeOperatorHAlong_comm,ModularCurve.heckeOperatorOneBar_comm \
  --json build/hd1-pair.json
```

| | `OneBar_comm` | `HAlong_comm` |
|---|---:|---:|
| pin `S_` lines | 979 | 993 |
| declarations | 100 | 100 |
| `theorem` / `abbrev` / `def` / `structure` | 85 / 12 / 2 / 1 | 85 / 12 / 2 / 1 |
| `private` declarations | 0 | 0 |
| **shared names** | **96** (8 one-sided) | |
| same statement after the group substitution | **95 of 96** | |
| lines that are a verbatim second copy | **886 of 1,873** | |

* **The two `S_` files are a mirror, not a pair of siblings.** 96 of the 100 names occur in both.
  Normalising *only the group vocabulary* — delete the standalone `H` argument,
  `heckeAlphaHBar`→`heckeAlphaOneBar`, `heckeBetaHBar`→`heckeBetaOneBar`,
  `HeckeBetaHDefined`→`HeckeBetaOneDefined`, `CohCarrier.GammaH M H`→`Gamma1 M` — makes **95 of the
  96 pairs byte-identical**. The only statement that genuinely differs is the pair of `solution`
  headlines, i.e. §0 itself. The second file is the first with the group substituted: 886 of the
  1,873 declaration lines.
* **Eight names are one-sided**, four per file, and they are exactly the group's own vocabulary:
  `T_mem_Gamma1`/`T_mem_GammaH` (3 ls), `T_mem_Gamma1_inf_Gamma0`/`T_mem_GammaH_inf_Gamma0` (4 ls),
  `heckeBetaOneDefined`/`betaHDefined_input` (10 ls), and the pointwise headline
  `heckeOperatorOneAlong_comm`/`heckeOperatorHAlong_comm'` (28 ls).
* **`drags` is empty for both files.** 100 public declarations each, and the same-file closure adds
  **0 helpers**: the pin pre-factored nothing, so there is no private prelude to take for free on
  either side and the whole 1,873 lines is the drag of the two headlines. This is the opposite of the
  WeightOne shape, where a package's private prelude dominated — here a *pre-port* dedup has nothing
  to find, and the only redundancy is between the two files.
* **The instrument's `port once` section is 2.5× low on a mirror.** It prices this pair at 360 lines /
  26 proofs, because its byte tier sees only the 34 pairs whose text is identical *before*
  normalisation. The other 61 twins surface in the `generalise` section instead: 49 names share a
  name but not the statement (ratios 0.97–0.99), plus 11 conclusion-same/binder-different inside the
  target set. On a pair like this the two sections must be read together.
* **Already in the port: 8 theorem statements, 61 distinct lines** (`coeffMap_qExpand`,
  `laurentBaseChange_mono`, `coeffEmb_qExpand`, `charZero_base`, `T_mem_Gamma1`, `T_mem_GammaH`,
  `qExpand_mem_laurentBaseChange`, `Gamma0_le_of_dvd` — the last two up to binder spelling). Two more
  are **only `private` in `X1/Inputs.lean`**: `finiteAlong_of_transcendental` (27 ls) and
  `isIntegral_of_finiteAlong` (7 ls). Promote them; do not re-prove them. `port_advise` reports these
  as "20 declarations, ≈190 lines" because it counts both copies, one per `S_` file; distinct, they
  are 10 statements / ≈98 lines.
* **Seven names (65 distinct lines) sit in the port with a different statement** — the roof block
  leads. `QQ`, `QQ_le_roof` and `BB` clash at ratio 0.949 with `HeckeCompositum.lean:539-548`, which
  already carries `QQ` and `roof` **`private`, generalised over `K` and `Γ_H`** (the same shape of
  field: `FF`/`qExpFunctionFieldC` and `map (qExpAlg …)`, against the pin's
  `laurentBaseChange`/`KT` and `qExpand ''`). The rest are
  `finiteDimensional_adjoin_of_transcendental` (32 ls, `X1/Inputs.lean`), `correspondence_congr`
  (`AlgebraicCurve/WeilExchange/Transport.lean`), `fieldRange_val_comp_inclusion`,
  `heckeBetaOneDefined`. These are §7.4 decisions (take the port's binders), not new proofs.
* **One instrument caveat, worth knowing before trusting a row here.** An `abbrev`'s statement is its
  carrier type, so the byte tier "matches" any two `abbrev`s of the same type: it reports `roof` as
  importable from `HeckeDegree.KL` (`IntermediateField L (LaurentSeries L)`, both), which is a type
  coincidence, not a duplicate. Every `abbrev` row in this section is a pointer to read, never a
  verdict.

The files are layered, and the layering is the cut. Two different senses of "shared" live here, and
the measurement separates them: **generic** (the statement never mentions the side's maps, so one
proof serves both) and **twin** (the same statement up to the group substitution, so the port *may*
keep two copies — or unify).

* `…CommGeneric` (~20 declarations: `isAlgebraic_adjoin_of_transcendental`,
  `finiteDimensional_adjoin_of_transcendental`, `finiteAlong_of_transcendental`,
  `isIntegral_of_finiteAlong`, `finrankAlong_pos_of_finiteAlong`, **`pushforwardAlong_pullbackAlong`**,
  `correspondence_comp_eq_smul`, `correspondence_congr`, `eq_of_zsmul_eq_zsmul`,
  `fieldRange_val_comp_inclusion`, `finrankAlong_inclusion`) — **group-agnostic and identical in both
  files**; two of them are already public in `HeckeDegree`.
* `…CommFields` (~25: `qExpAlgHom`, `coeffMap_qExpand`, `coeffEmb_qExpand`,
  `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`, the `T_mem_*`/`Gamma0_le_of_dvd`, the
  **cocycle** computation `cocycle_inf`/`cocycle_one`, `KK`/`KT`, the subsets, `heckeBetaOneDefined`,
  transcendence, `qExpTo`) — the q-expansion/group vocabulary, **side-specific in spelling, twin in
  statement** (the 4 one-sided names and the `Γ₁`→`Γ_H` renamings).
* `…CommRoof` (~40: `QQ`/`roof`/`BB`, the `Nice` predicate and its 8 consequences, `nice_*`, the
  legs `legU`/`legU'`/`legP`/`legI`, `hgen`, `finrankAlong_alpha`/`beta`/`diag`, `relfinrank_KK_roof`,
  `hsq`, `exchange`, `heckeDiv_heckeDiv`) — the field part (`QQ`/`roof`/`BB`/`Nice`/`nice_*`) is
  generic; the leg and degree lemmas mention the side's maps.
* `…CommMain` (~10: `RR`, `nice_RR`, `heckeDiv_comm`, `…Along_comm`) — side-specific.

So **~38 of the 100 declarations are generic** — the prelude plus `Nice`/`roof`/`BB` (the field
constructions and their 8 `Nice` consequences, which never mention α/β) — and **96 are twins**, 95 of
them statement-identical up to the group substitution. The 38 is what *must* be written once; the
other 58 twins are what *may* be, if `KK L M H` and `KK L M` are unified into one statement family. The
pin never took that step (see §6).

## 5. The structure: one module for the pair, two extensions, five promotions

Revised 2026-10-25, against the port as it stands. The decision below is not new: the port has
already made it **twice for this very pair of pin files**, and both times it worked.

* `ModularCurve/HeckeCompositum.lean` — the compositum's degree multiplicativity, whose pin states it
  twice (an 884-line `x1` file): *"the pin's `x1` file is **not** transcribed: every one of its 61
  theorem/lemmas has a same-shape twin in the `xH` file, and the port holds the bridge
  `CohCarrier.GammaH_bot : CohCarrier.GammaH M ⊥ = Gamma1 M`, so the `x₁` statement is the `x_H`
  statement with `H := ⊥`"* — both headlines in one root module, the `x₁` one six lines at the bottom.
* `XH/HeckeDegree.lean` — the α/β degree engine, *"the shared engine, **once** … The `X₁`
  specialisation imports the engine from here and adds only its `H = ⊥` assembly"*; there the `X₁`
  side did earn its own module (`X1/HeckeDegree.lean`, 415 lines), because its `q ∣ M` branch is
  mathematics the engine does not state.

The commutativity pair is the first case, not the second: §4 finds **no** mathematics on the `X₁`
side that the `X_H` side does not state — 95 of its 96 twins *are* the same statement. So:

**One new module** — `ModularCurve/HeckeRowCommute.lean` (root, beside `HeckeCompositum.lean` and
`HeckeCommuteBar.lean`, for the same reason those are at the root: it belongs to neither side and
serves both).

| content | visibility |
|---|---|
| the `H`-general development, transcribed from the `X_H` `S_` file at the pin's names (cocycle, `KK`/`KT`/`QQ`/`roof`/`BB`, `Nice` + `nice_*`, the legs, `finrankAlong_alpha`/`beta`/`diag`, `relfinrank_KK_roof`, `hsq`, `exchange`, `heckeDiv_heckeDiv`, `RR`, `heckeDiv_comm`) | **public** — it is the engine, and the next consumer (`HeckeDiamondCommuteBar`, the Tate Hecke algebra) is on the same row data |
| `ModularCurve.heckeOperatorHAlong_comm` | public, statement verbatim from its wrapper |
| the `X₁` half — the pin's `…CommFields`/`…CommRoof`/`…CommMain` transcribed from the One text, in a second namespace of the same file (§5.3) | `private` |
| `ModularCurve.heckeOperatorOneBar_comm` | public, statement verbatim from its wrapper |

Wires: **two** `spec-pin:` pairs on the one module (`Thm_`+`S_` ×2) — `XH/HeckeDegree.lean` already
carries three such pairs (six `spec-pin:` lines), so this is the convention, not a special case.

What is **not** new, and is imported rather than restated (the HD1 rule: the pin's private vocabulary
is imported wherever the port has a public home): `pushforwardAlong_pullbackAlong`,
`correspondence_comp_eq_smul`, `correspondence_congr`, `eq_of_zsmul_eq_zsmul`, `fieldRange_val_comp_inclusion`,
`finrankAlong_inclusion` (`XH/HeckeDegree.lean:294,304`), `KL`/`EL` (`:272,274` — the pin's `KK`/`KT`),
`qExpand`/`coeffMap`/`coeffEmb`/`laurentBaseChange` (`Defs/Laurent.lean`), `Gamma1_le_GammaH`,
`Gamma0_le_of_dvd`, `qExpand_image_intFormRatiosC_subset`, `relfinrank_{x1,xH}HeckeCompositum_eq_mul`,
`hasPrincipalDivisors_of_transcendental`, `separableAlong_of_charZero`,
`finrankAlong_eq_relfinrank_fieldRange`, `JOneES.exists_transcendental_finiteDimensional_laurentBaseChange`
(`X1/FunctionFieldBaseChange.lean:340`).

**Layer 0 — four small pieces, in the modules that own them** (verified in §3):

| module | content |
|---|---|
| `AlgebraicCurve/ResidueTheorem/KFamily.lean` (**already wired**) | `Place.sum_ramificationIndexAlong_mul_inertiaDegAlong`, next to the lemma its 7-line proof is: `sum_ramificationIndex_mul_inertiaDeg` (`:63`). One new `spec-pin:` line (`Thm_AlgebraicCurve_Place_sum_ramificationIndexAlong_mul_inertiaDegAlong.lean`), no legacy module touched |
| `ModularCurve/XH/FunctionField.lean` (extend) | `JH` (`abbrev JH := Pic0 (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)`), beside `xHFunctionFieldBar:98` — the headline's binder type |
| `ModularCurve/X1/HeckeModule.lean` (extend) | `heckeOperatorOneBar` + `_apply` (one line each; `Defs/HeckeModule.lean:37` is the precedent) |
| `ModularCurve/XH/HeckeOperator.lean` (extend) | the `HeckePic0HBar` block (`heckeDivHBar`, `heckePic0HBar`, both transposes), `heckeOperatorHAlong`, `_eq`, `_of_not`; its header's "off this cone (0 references in the four `S_` files)" is now false and must be corrected |

**No `HeckeRoof.lean`.** That module would have held the generic prelude — but its two halves have
homes: the group-agnostic lemmas are `AlgebraicCurve` facts (promote where they adapt, below) and the
roof/`QQ`/`BB` block is the compositum's (`HeckeCompositum.lean`, below). A module that only collects
the pair's prelude is the "externals/misc" shell §5 of the playbook tells us to dissolve.

### 5.1 Refactoring this pair wants (measure each; promotion shrinks its host)

| # | site | change | why |
|---|---|---|---|
| R1 | `ModularCurve/HeckeCompositum.lean:539-561` | promote `GA`, `GB`, `QQ`, `BP`, `roof`, `QQ_le_roof` (+ `QQ_le_FFA`, `QQ_le_BP`) from `private` | they *are* the pair's roof block, already generalised over `K` and `Γ_H`; the pin restates them in both `S_` files. Leave the degree proof's group helpers (`exists_delta`, `main_C`, `relIndex_*`) private |
| R2 | `ModularCurve/X1/Inputs.lean:105,139` | **promote in place**, public (`finiteAlong_of_transcendental` 27 ls, `isIntegral_of_finiteAlong` 7 ls) | left `private` in a consumer they are the WeightOne failure mode ("a real result left `private` and re-derived in the next theory is pure loss"); the pin restates them in both `S_` files. The *natural* home is `AlgebraicCurve/WeilExchange/Transport.lean` (next to `separableAlong_of_charZero`), but no `WeilExchange` module is wired, so moving them there triggers `Transport`'s full modernisation — see §5.2. Promote here now, migrate later with `Transport` |
| R3 | `ModularCurve/X1/HeckeModule.lean` and `XH/HeckeOperator.lean` headers | correct the two scope sentences that declare the operator and the `HeckePic0HBar` block out of scope | both are on this cone now (§3) |
| R4 | `ModularCurve/HeckeCompositum.lean:676-690` | keep `FF_eq_bc`/`QQ_eq_bc`/`roof_eq_bc` where they are, and import them | they are the bridge between the port's `FF`/`qExpAlg` spelling and the pin's `laurentBaseChange`/`qExpand ''`; the pair needs exactly that bridge and should not write a third spelling |
| R5 | `ModularCurve/XH/FunctionField.lean`, `X1/Defs.lean` | nothing — `xHFunctionFieldBar`/`JOne` are already there, and `JH` lands beside the former | — |
| R6 | `ModularCurve/HeckeCommuteBar.lean`, `X1|XH/HeckeDegree.lean`, `Defs/Laurent.lean`, `Defs/HeckeModule.lean` | no change | already the homes they should be |

### 5.2 The modernisation bill: touching a legacy module is a commitment (2026-10-25)

Standing policy in this project: **a legacy module that is touched is brought up to the current
standard in the same pass** — its `spec-pin:` header, out of `spec/old_check_stmts.py`'s
`PORT_FILES`, building quietly, no generated name tokens, natural subject hosting, `dedup.py` clean
and `move_dead.py --select dead` empty (dedup counting lemmas with real content, not the one-line
helpers that exist to make elaboration go). So the first question about a refactor here is not "is it
right" but "which modules does it put on the bill". Measured for every module in §5.1:

| module | state | `spec-pin:` sources that cover it (this is the bill) | public names | dedup | dead |
|---|---|---:|---:|---|---|
| `ModularCurve/XH/FunctionField.lean` | legacy | 1: `Definitions/Def_ModularCurve_XH.lean` (covers 12/12) | 12 → 13 with `JH` | 0 | 0 |
| `ModularCurve/X1/HeckeModule.lean` | legacy | 1: `Definitions/Def_ModularCurve_X1HeckeModule.lean` (1/1) | 1 → 2 | 0 | 0 |
| `ModularCurve/XH/HeckeOperator.lean` | legacy | 1: `Definitions/Def_ModularCurve_XHHeckeOperator.lean` (16/16) | 16 → ~20 | 0 | 0 |
| `ModularCurve/X1/Inputs.lean` | legacy | 2: `Thm_ModularCurve_heckeDiamondInputsAll.lean` for today's surface, plus `S_ModularCurve_JOne_degeneracyPullbackInputs.lean` for the R2 promotions | 1 → 3 | 0 | 0 |
| `AlgebraicCurve/WeilExchange/FiberOverCount.lean` | legacy | 2: `Thm_…_sum_ramificationIndex_mul_inertiaDeg_fiberOver.lean`, `Thm_…_le_finrank.lean` | 3 → 4 | 0 | 0 |
| `AlgebraicCurve/WeilExchange/Transport.lean` | legacy | **~10–12 files** (its 24 public names were generalised out of many pin `S_` files) | 24 | 0 | 0 |
| `ModularCurve/HeckeCompositum.lean` | **wired** (3 `spec-pin:` lines) | none new — `AA`/`FF`/`GA`/`GB`/`QQ`/`BP`/`roof`/`QQ_le_*` are all in the wired `S_ModularCurve_relfinrank_xHHeckeCompositum_eq_mul.lean:647-777` | 2 → ~12, all covered | 1 shape cluster (its `private solution`, 750, vs its own headline, 791) | **2 declarations / 29 lines** |
| `ModularCurve/X1/Defs.lean` | **wired** | none | 26 | 0 | 0 |

Consequences, and the two plan changes they forced:

* **The Place identity moved off `FiberOverCount.lean`** (§5, layer 0): both are legacy, but
  `ResidueTheorem/KFamily.lean` is already wired and holds the lemma the 7-line proof is. That turns
  the piece into a `spec-pin:` line in a module that is already checked, instead of a new legacy
  module on the bill.
* **R2 stays in `X1/Inputs.lean`.** Moving the two lemmas to their natural home
  (`WeilExchange/Transport.lean`) would cost ~10–12 `spec-pin:` lines and a 24-statement reconcile —
  five to ten times the rest of this wave's bill — for a hosting improvement on two generic lemmas.
  Promote them here; migrate `Transport` when something else next touches it.
* **The three layer-0 extensions are cheap**: one `spec-pin:` line each, because each module's
  public surface was transcribed from a single `Definitions/` file. `X1/Inputs.lean` needs a second
  line only for the R2 promotions.
* **`HeckeCompositum.lean` is already wired, so R1/R4 cost no wiring** — but it is not clean: two
  declarations / 29 lines are dead, and its `private solution` (the pin's `S_` headline transcribed
  below the public headline that wraps it, `:750` vs `:791`) is a shape-duplicate of that headline.
  Fold the two together (the public name stands, the pin's proof body sits at it), and let
  `move_dead --apply` take its two dead declarations — `T_mem_inf` (3 ls) and
  `relIndex_le_relIndex_inf` (26 ls) — together with the three group helpers they are the only
  users of (`T_mem_Gamma0`, `T_mem_Gamma1`, `exists_mul_eq_of_mem_Gamma1`).
* **Six `PORT_FILES` entries come out** with these modules (`old_check_stmts.py:3570, 3574, 4192,
  4211, 4538, 4539`). Do not touch `SOURCES`: it is global and other modules still read those files.
* Build quietness and name hygiene are already satisfied everywhere in the bill: no
  `attribute [-…]` walls, no heartbeat bumps, no `kw_`/`p0nN`/`_sN` tokens, no `sorry`. The one
  exception worth a look is `X1/Inputs.lean:165`, `set_option backward.isDefEq.respectTransparency`.
  `types false in` on a single theorem — either document it or remove it before that module is
  declared modern.

### 5.3 The scout gate fired: the `H = ⊥` route is not statable (2026-10-25)

The gate was run before layer 1 and it **failed**, so the price below is the transcription, not the
unification. The finding, read off the sources:

* `heckeAlphaHBar L M ⊥ ℓ` and `heckeAlphaOneBar L M ℓ` do not even have the same *type*:
  `A →ₐ[L] B` with `A = laurentBaseChange L (xHFunctionField M ⊥)` against
  `laurentBaseChange L (x1FunctionField M)`. `xHFunctionFieldC_bot` is a `rw`-theorem
  (`CohCarrier.GammaH_bot` is a `le_antisymm`), so the two fields are **propositionally equal, never
  definitionally** — an equation between the maps cannot be elaborated at all.
* Every row-level predicate puts the map in a *type* position — `(φ).toRingHom.IsIntegral`,
  `FiniteAlong L φ`, `FundamentalIdentityAlong L φ hβ`, `Divisor.correspondence φ ψ …` — so each one
  needs a bespoke transport lemma; `correspondence_congr` is same-type only and cannot carry it. The
  only cheap bridge is `HeckeBetaHDefined M ⊥ ℓ ↔ HeckeBetaOneDefined M ℓ` (set membership, ~4 lines).
* The two earlier `H = ⊥` successes do not transfer: `HeckeCompositum.lean`'s six-line `x₁` instance
  and `X1/HeckeDegree.lean`'s assembly are **property-level** theses (`relfinrank`, `finrankAlong`),
  where the statement mentions the field but never *is* a map into it.

Adopted cut: **two modules, engine and twin** — `ModularCurve/XH/HeckeCommute.lean` (the public `X_H`
development at the pin's names: the engine, its group-agnostic prelude, and
`heckeOperatorHAlong_comm`, wired by two `spec-pin:` lines) and `ModularCurve/X1/HeckeCommute.lean`
(the pin's One text transcribed at the pin's names and visibility, plus `heckeOperatorOneBar_comm`,
wired by its own
two). This was first written as *one* file, on the argument that the two halves are the same
development; the measurement overturned that argument — the twin re-declares 74 of its 80 names
(`Nice`, the legs, `hsq`, `exchange`, `RR`, `heckeDiv_comm`, the fields) and shares only the 202-line
public prelude `XHHeckeCommute.Generic`, which an `import` carries as well as a file does. Two halves
that share no proof are two subjects, so the `HeckeDegree` pattern (`XH` engine, `X1` assembly
importing it) applies; co-location bought nothing, since a `private` twin is invisible to any
consumer of the engine's file. Not two
side modules (the pin's file split is an artifact of its own duplication, and one module keeps the two
halves in view of each other), and not a transport library (inventing one to save ~700 lines would put
the whole engine on a vocabulary the pin never used).

A by-product of the scout, now load-bearing for the port: `heckeInputsHAlong`
(`XH/HeckeInputs.lean:405`) and `heckeInputsOneAlong` (`X1/Inputs.lean:259`) are **theorems** in the
port, so both operators' `if` always takes the first branch and the pin's `Nice` machinery is already
discharged — the headlines should be proved by `heckeOperator{H,One}Along_eq` + `dite_eq_left`, never by
case-splitting on the bundle.

### 5.4 What landed (2026-10-25): layer 0, the promotions, four modernisations

Done in one pass; every module below is green in `spec/check_port.py` (**text** check, no build ran —
the tree is not built without the user's word).

| piece | where | checker |
|---|---|---|
| `Place.sum_ramificationIndexAlong_mul_inertiaDegAlong` (the 6-line instance pack over `sum_ramificationIndex_mul_inertiaDeg`) | `AlgebraicCurve/ResidueTheorem/KFamily.lean` (already wired; +2 `spec-pin:` lines) | 30 ok / 0 |
| `JH` | `ModularCurve/XH/FunctionField.lean:106` (modernised) | 13 ok / 0 |
| `heckeOperatorOneBar` + `_apply` | `ModularCurve/X1/HeckeModule.lean` (modernised) | 3 ok / 0 |
| `HeckePic0HBar` block (`heckeDivHBar`, `heckePic0HBar`, both transposes), `heckeOperatorHAlong`, `_eq`, `_of_not` | `ModularCurve/XH/HeckeOperator.lean` (modernised; header corrected) | 23 ok / 0 |
| R2: `finiteAlong_of_transcendental`, `isIntegral_of_finiteAlong` promoted | `ModularCurve/X1/Inputs.lean` (modernised) | 3 ok / 0 |
| R1: `AA`, `FF`, `GA`, `GB`, `QQ`, `BP`, `roof`, `QQ_le_FFA`, `QQ_le_BP`, `QQ_le_roof` promoted | `ModularCurve/HeckeCompositum.lean` | 12 ok / 0 |

`PORT_FILES` lost four entries (`X1/HeckeModule`, `X1/Inputs`, `XH/FunctionField`, `XH/HeckeOperator`);
`SOURCES` untouched. Two lessons the checker taught, worth carrying: the **binder block decides the
diff** — type-class binders written in a `variable` line instead of the declaration made the Place
identity a MISMATCH on a statement that was otherwise verbatim; and `dite_eq_left`/`dite_eq_right`
replace the pin's `dif_pos`/`dif_neg` in this mathlib.

**First compile round (the user's build, 2026-10-25).** Three of the six edits compiled:
`ResidueTheorem/KFamily` (the `Along` fibre identity), `XH/FunctionField` (`JH`) and `X1/HeckeModule`
(`heckeOperatorOneBar`). Two failed and were fixed the same hour: `XH/HeckeOperator`'s
`variable (L) in` was a *redundant binder annotation* (the section already has `variable (L)`), and
`X1/Inputs`'s `private theorem charZero_of_algebraRat` collides with the **public**
`ModularCurve.charZero_of_algebraRat` (`Defs/Laurent.lean:526`) — a latent break, not one this wave
introduced: the duplicate predates it and the file's stale `.olean` had hidden the clash until the
promotion forced a rebuild. Deleted (it was byte-identical to the public one, so the fix is also the
dedup). `HeckeCompositum` and `HeckeRowCommute` were never scheduled in that round, because the build
stopped at the two failures. Lesson worth keeping: *touching* a legacy module also means auditing the
private names it declares against the public surface of its import cone — a shadowed public name is a
hard error, and only a rebuild can reveal it.

Two pieces of debt remain, both recorded rather than fixed:

* `HeckeCompositum.lean`'s `private solution` (`:721`) is a shape-duplicate of the public headline
  that wraps it (`:762`); folding the 41-line proof body onto the public name needs a build to check,
  so it waits.
* `move_dead --select dead` found its two dead declarations (`T_mem_inf`, `relIndex_le_relIndex_inf`,
  29 ls) but could only shelve them by `--expose`-ing three live private group helpers
  (`T_mem_Gamma0`, `T_mem_Gamma1`, `exists_mul_eq_of_mem_Gamma1`) onto the wired module's API, which
  the statement check would reject. They are group-theory plumbing, not mathematics, so they were
  binned (playbook §3.8) instead of shelved.

#### 5.4.1c The split into two modules (2026-10-25)

`HeckeRowCommute.lean` became `XH/HeckeCommute.lean` (932 lines) + `X1/HeckeCommute.lean` (663 lines),
the second importing the first. The line numbers quoted in §5.4.1a and §5.4.1b refer to the pre-split
file; nothing else in them changes.

| | pre-split | split |
|---|---|---|
| lines | 1,534 | 932 + 663 = 1,595 |
| public surface | 96 declarations in one file, 74 of them shadowed by the private twin | 85 + 1 own in `XH`; **73** in `X1` (72 transcribed + its headline) |
| `spec-pin:` wires | 4 on one module | 2 + 2, one pair per headline |
| build (single module each) | 31.5 s | **17 s + 14 s = 31 s** |
| `check_port` | 86 ok / 1 own | `XH` 85 ok / 0 / 0 / 1 own; `X1` 1 ok / 0 / 0 / 0 |
| `move_dead` | 0 | 0 + 0 |
| `dedup` | 0 clusters | **2 clusters, 12 lines** — `algebra_subtype` and `semiring_subtype` (6 lines each) now exist in both files |

The two dedup clusters are deliberate: a `private instance` is file-scoped, so the generic bricks
cannot be imported, and they are elaboration helpers, not mathematics — exactly the residue the
dedup rule says not to chase. The `own:` row in `spec/decl_markers.tsv` moved with the declaration to
`FLTForHuman/ModularCurve/XH/HeckeCommute.lean`.

What the split buys: the `X_H` module's public surface is now its own (no second half shadowing 74 of
its names); each headline has its own provenance wire; the dependency `X1 → XH` is explicit, matching
`Γ₁ ≤ Γ_H` and the two directories; and the `X₁` half is a single, self-contained file that becomes a
deletion rather than a surgery once a transport library for the two vocabularies exists.

**Correction (2026-10-25, after the split): the twin should never have been demoted to `private`.**
The pin states every one of those 81 declarations publicly (its `S_` files carry no `private` at all),
so they are *pin-public statements*, and the port's rule for those is "keep the pin's name **and its
visibility**"; only machinery the port invents may be `private`. The demotion was made to give the
single merged file one public surface — an artifact of the merge, not a policy — and its cost was
that 598 transcribed lines escaped the statement check (only the headline was diffed). Corrected when
the halves became separate modules: 73 declarations promoted (the `Nice` structure among them — a
`structure`, so the first sweep missed it) (visibility only, no name or statement
change) and the pin's `scoped instance finiteIndex_Gamma1_inf_Gamma0` restored to `scoped` — which
is also what let the checker match it. The `X1` module now reads **73 ok / 0 mismatch / 0 missing /
0 own**: every pin-public statement in it is diffed. The nine declarations still `private` are the
port's own elaboration bricks (`algebra_subtype`, `semiring_subtype`, `algebra_laurent_rat` and the
six per-field `algebra_*`), which is what `private` is for.

#### 5.4.1a It compiles — and what it costs (2026-10-25)

`ModularCurve/HeckeRowCommute.lean` now **builds** (the first compile round needed ~20 proof
repairs; every one was port-API drift, not mathematics). Text checks: `check_port` **86 ok /
0 mismatch / 0 missing / 1 own**, `dedup` 0 clusters, `move_dead` 0. The `own:` row
(`spec/decl_markers.tsv`) is the one port-own declaration: `finiteDimensional_adjoin_of_transcendental'`,
which states the finite-dimensionality as an *explicit hypothesis* because the field is spelled
`KT …` in the goal and unfolded over `qExpFunctionFieldC` in the witness and `xHTopFunctionFieldC`
is a `def` — the instance key misses and the search burns its budget. That is the playbook §6 row
"an instance keyed on a semireducible `def`", cured statically, with **no heartbeat bump**.

**Build time: 98 s → 52 s, fixed by naming the instances once.** The profiler put **109 s into
`Algebra` typeclass inference over 340 searches** (~350 ms each) against **13 s of tactic execution**,
so the cost was not proof search. `trace.Meta.synthInstance true` on one hot declaration (`finrankAlong_diag`)
showed why they are *re-derived*: the winning candidate is the **unkeyed** `algebra'` form
(`Algebra R A` with `{R A}` and the sub-goals `SMul`/`Mul`/`Distrib`/… inferable), so it cannot be
looked up by head symbol — Lean tries it against *every* `Algebra` goal first (`Algebra L ↥(roof …) ≟
Algebra ℚ L`, ❌) and each `≟` has to unfold the field expression (`roof` through `⊔`/`adjoin`/`KT`,
`KT` through the `def xHTopFunctionFieldC`). Instance search also does not reuse the answer across
occurrences: the trace shows the *same* goal (`Algebra L ↥(roof …)`) searched 5 times in one proof,
plus `Algebra ℚ L` 12 times, 219 distinct goals / 1,618 searches for that declaration alone. So the
fix is the playbook's brick recipe at the narrowest useful scope: **`private instance algebra_KK :
Algebra L ↥(KK L M H) := inferInstance`** and the same for `KT (M*ℓ)`, `KT (M*ℓ')`, `QQ`, `roof`,
`BB` in each half — one derivation per field, every later occurrence an assumption lookup. Nothing
public, nothing statement-level, no budget raised. An earlier attempt at the *wrong* key (the file's
`≤` facts as `local instance`s) broke seven declarations and saved nothing; reverted before the real
cause was known.

#### 5.4.1b Second pass: 52 s → 31.5 s, three more keyed instances (2026-10-25)

The first pass named the *concrete* fields; what it cannot name is every carrier that is a
**variable** — `Nice.*`, the prelude (`qExpTo`, `fieldRange_val_comp_qExpTo`,
`finiteDimensional_adjoin_of_le`) and the legs all state their results at
`{A A' : IntermediateField L (LaurentSeries L)}`, so no `algebra_roof`-style brick can exist for them
and `IntermediateField.algebra'` stays the winning candidate: its conclusion `Algebra ?R ?S` has both
arguments as metavariables, so its key is `Algebra` alone, and each win re-derives
`SMul`/`Mul`/`Distrib`/`Semiring` (~250 ms). Two *generic* keyed instances answer that class of goal
(the key is `Subtype`, which is as specific as the discrimination tree gets for a `↥` carrier), and a
third names the one concrete carrier the Γ-vocabulary proofs keep asking for:

| kept | statement | why it was hot |
|---|---|---|
| `algebra_subtype` | `Algebra K ↥A` for `A : IntermediateField K L` | the `Nice.*` cluster: 6 searches × ~250 ms in each of 12 declarations (both halves) |
| `semiring_subtype` | `Semiring ↥A`, same generality | the `[Semiring ↥A]` argument of *every* such goal, ~25 ms per occurrence (176 occurrences) |
| `algebra_laurent_rat` | `Algebra ℚ (LaurentSeries ℚ)` | `DivisionRing.toRatAlgebra` over the Hahn-series fraction field, ~68 ms; the four `intFormRatiosC ℚ _` proofs (`qExpand_KK_subset`, `qExpand_KT_subset`, `betaHDefined_input`, ×2 halves) each ask several times |

Measured ladder — `lake build FLTForHuman.ModularCurve.HeckeRowCommute` (wall, user) against the
probe's profiler cumulative (CPU seconds); all three text checks re-run green at every step
(`check_port` **86 ok / 0 mismatch / 0 missing / 1 own**, `dedup` 0 clusters, `move_dead` 0):

| stage | build wall | build user | probe wall / user | typeclass | tactics | type checking | elaboration |
|---|---:|---:|---:|---:|---:|---:|---:|
| start | **52 s** | — | 51.9 / 102.7 s | 49 s | 28.1 s | 15.7 s | 10.4 s |
| `+algebra_subtype` | 37.9 s | 77.3 s | 35.5 / 74.9 s | 19.5 s | 28.7 s | 11.7 s | 11.3 s |
| `+semiring_subtype` | 35.5 s | 73.9 s | 29.5 / 63.2 s | 12.9 s | 26.4 s | 9.75 s | 10.6 s |
| `+algebra_laurent_rat` | **31.5 s** | 63.5 s | 28.2 / 60.2 s | 11.4 s | 25.5 s | 9.12 s | 10.5 s |

The bill moved from **29.5 s in 101 searches of ≥100 ms** (plus ~19 s under the print threshold) to
**8.4 s in 1,445 searches averaging ~6 ms**. One search ≥100 ms is left, a 151 ms `AddHomClass` in
`qExpTo`'s own type. What remains is no longer instance inference: `tactic execution` 25.5 s (11.7 s
of it `rewriteSeq`), kernel `type checking` 9.1 s, `elaboration` 10.5 s, and a typeclass tail with no
single mechanism — the two worst declarations are `finiteDimensional_adjoin_of_le` (0.75 s / 99
searches) and `heckeDiv_comm` (0.70 s / 63, in each half), all at 5–15 ms per search.

Rejected, with the measurement: `Algebra ↥A (LaurentSeries L)` as a brick (`toAlgebra`'s keyed twin)
made the probe *worse* — 1,444 → 1,519 searches, typeclass 9.76 → 10.08 s — because it only adds a
candidate to every `Algebra` goal whose carrier is a subtype. Bricks for the still-unbricked concrete
carriers (`RR`, `roof … ℓ' ℓ`, `QQ ℓ'`, `BB ℓ' ℓ`, the bare `adjoin` carrier) are unnecessary rather
than wrong: with the three generic instances in place each of those goals synthesizes in **2.5–7 ms**
(measured on a micro-probe over those five carriers), so a brick would save nothing and add six more
candidates per goal.

**Method, reused as the recipe.** `--json` is what makes the profiler attributable: with `lake env
lean --json -Dprofiler=true -Dprofiler.threshold=1`, every event carries the position of the command
it belongs to, so the log sums by declaration in a few lines of Python (`pos.line` → sum of
`typeclass inference of <class> took <N>ms`; one message's `data` can hold several events). Bisect
cheaply: elaborating a scratch copy of the module (`lake env lean`, no lake scheduling) reuses the
oleans and costs ~30 s, and a micro-probe of one `example` per carrier (~7 s) prices one class at one
carrier — which is how each brick above was validated before a build was spent on it.

**Friction worth keeping: a `--` comment is a checker hazard in this file.** The first version of the
new comment block used `--` lines, and `check_port` then reported `1 missing, 0 own` on
`XHHeckeCommute.Generic.finiteDimensional_adjoin_of_transcendental'`. Cause: `namespace_events` scans
`strip_line_comments(text)`, which *deletes* `--` text and so shifts every later position, while
declarations are matched at positions in the un-stripped (block-comment-blanked) code — a 600-character
`--` block above the first declaration pushes `namespace Generic` back behind it and the parser
attributes the wrong namespace to the rest of the file. A `/- … -/` block comment (blanked by
`flat_code`, line count kept) is the cure. The `--` comments already in the module shift positions the
same way today, so the next agent to touch this file should not lengthen them.

#### 5.4.1 Layer 1 landed (2026-10-25): two modules, engine and twin (§5.4.1c records the split)

The cut of §5.3 is implemented. One new root module, **1,514 lines** (see the accounting at the end
of this subsection), holds:

| content | visibility |
|---|---|
| `XHHeckeCommute.Generic` — the group-agnostic prelude: `qExpAlgHom` (the pin's name for the port's `qExpAlg`), the two level `NeZero` instances, `charZero_base`/`charZero_sub`, `transcendental_coe_iff`/`transcendental_qExpand`, `qExpTo`/`coe_qExpTo`/`fieldRange_val_comp_qExpTo`, and five `Along`/`Divisor` lemmas (`finiteDimensional_adjoin_of_le`, `finrankAlong_pos_of_finiteAlong`, `pushforwardAlong_pullbackAlong`, `correspondence_comp_eq_smul`, `eq_of_zsmul_eq_zsmul`) | **public** (identical text in both `S_` files) |
| the `X_H` development: cocycle, `KK`/`KT`/`QQ`/`roof`/`BB`, `Nice` + the eight `nice_*`/`Nice.*`, the four legs, `finrankAlong_alpha`/`_beta`/`_diag`, `hLD`, `relfinrank_KK_roof`, `hsq`, `exchange`, `heckeDiv_heckeDiv`, `RR`, `heckeDiv_comm`, `heckeOperatorHAlong_comm'` | **public**, at the pin's names |
| `ModularCurve.heckeOperatorHAlong_comm` | public, wrapper statement verbatim |
| the `X₁` twin of the pin's `…CommFields`/`…CommRoof`/`…CommMain` (`X1HeckeCommute`) | `private` |
| `ModularCurve.heckeOperatorOneBar_comm` | public, wrapper statement verbatim |

Checks (all three **text-only**; no build ran): `spec/check_port.py --force` →
**86 ok, 0 mismatch, 0 missing, 0 own, 0 kw** (the four `spec-pin:` lines wire both pairs);
`dedup.py --module` → **0 clusters**; `move_dead.py --select dead` → **0 declarations**.

What the gate changed in the plan of §5, and what it did not:

* **No `H = ⊥` bridges at all** — not even the cheap `HeckeBetaHDefined` iff: nothing needs it once the
  twin is transcribed. So §5's third row is replaced by the private twin, and the module has no
  map-level transport anywhere.
* **The shared text is 15 declarations, not 38.** Most of the pin's group-agnostic declarations are
  imported rather than restated: the four `Defs/Laurent` prelude lemmas (`coeffMap_qExpand`,
  `coeffEmb_qExpand`, `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`),
  `qExpAlgHom_apply`/`coe_qExpAlgHom` (the port's `qExpAlg_apply`/`coe_qExpAlg`),
  `isAlgebraic_algebraAdjoin`/`isAlgebraic_adjoin_of_transcendental`/
  `finiteDimensional_adjoin_of_transcendental` (`AlgebraicCurve`),
  `correspondence_congr`, `finiteAlong_of_transcendental`, `isIntegral_of_finiteAlong`,
  `fieldRange_val_comp_inclusion`/`finrankAlong_inclusion` and `Gamma0_le_of_dvd`. The pin's
  `qExpAlgHom` is the one `def` that *had* to be re-declared: `QQ_eq_map`'s statement names it, and
  the checker diffs that text.
* **R1/R4 were not needed.** `HeckeCompositum.lean`'s `FF_eq_bc`/`QQ_eq_bc`/`roof_eq_bc` stay
  `private`: the pair states its roof on the *laurentBaseChange* spelling directly, so it never
  crosses the port's `FF`/`qExpAlg` spelling. `HeckeCompositum.lean` is unchanged, and its
  `check_port` verdict is untouched.
* **Price, measured (§6):** **1,595 lines across the two modules (932 + 663) against the 1,563
  estimate** — the pre-split single file was 1,514, and the split adds 81 lines of two headers and the
  duplicated generic instances (§5.4.1c); either way the estimate held to a few per cent., and the two numbers
  measure slightly different things (the estimate counted the 1,873 pin *declaration* lines minus 310
  already-ported; the module counts file lines, which include ~97 of header/imports/sections but drop
  the pin's `P2M` scaffolding and its two `attribute [-]` walls). Inside the 1,514: **820 for the
  public `X_H` engine, 598 for the private `X₁` twin, 96 framework**. The twin is 40 % of the module,
  which is the mirror the gate proved unreachable to remove: had the `H = ⊥` route worked, the
  projection was 827 and the module would be ~880. So §6's *first* bullet is the price that was
  actually paid, and the 736-line gap between the bullets is the transport library that does not exist.
  Of the 1,514, **46 lines are not transcription**: the compile-repair pass (explicit-`hfin`
  reformulations, `Subgroup.mem_inf` spellings) and the two six-instance brick sets that took the
  build from 98 s to 52 s.
* **No `HeckeRoof.lean`, no two side modules**, and no `attribute [-]` wall: none of the pin's two
  walls was needed.

Two facts about the checker worth carrying for the next row-layer module:

* The statement checker's port parser **does not see `scoped instance`** declarations (they are not in
  the corpus either). That is harmless — but it means a `scoped instance` that a *second* namespace
  needs must be reached by `open scoped`, not by `open`; the port-side twin here needs
  `charZero_sub`/`neZero_*` and therefore carries `open scoped XHHeckeCommute.Generic`.
* The two headlines are proved by the pin's `by_cases h : HeckeInputs*Along` split, not by
  `heckeInputs*Along` + `dite_eq_left`: the `X₁` half is transcribed at general `L`, where the port's
  `heckeInputsOneAlong` is `private` in `X1/Inputs.lean` (its public form is the
  `AlgebraicClosure ℚ`-only `heckeDiamondInputsAll`). The split is total — the failing branch is the
  `0` map on both sides — so the statements stay unconditional. A later pass can shorten both
  branches to `_eq`+`dite_eq_left` once `heckeInputsOneAlong` is promoted.

## 6. Price, in the port's units

Measured (§4), so the cut can be priced both ways:

* Pin lines: 979 + 993 = **1,972** in the two `S_` files, **1,873** of them in declarations; 200
  declarations (85 theorems, 12 abbrevs, 2 defs, 1 `structure` per side).
* Written once per distinct declaration: **104 declarations, 987 lines**.
* Already in the port: **8 importable theorems (61 distinct lines)** + **2 port-`private` theorems
  (34 lines, promote)**; a further **7 names (65 lines)** are §7.4 reads, not proofs (§4).
* **One price, since §5.3's gate fired: 1,563 new port lines.** The 1,873 declaration lines of the
  two `S_` files, minus the 310 whose statement already has a port counterpart (counted per
  declaration as the pin has them: 58 + 64 + 68 + 120 across the two copies). The earlier
  1,350–1,450 estimate was 10–15 % low: it scored the twins at "~38 shared / ≈450 lines" and the
  side-specific part at "~60 each / ≈450 each", while the measurement finds 96 twins / 886 duplicate
  lines.
* The unified alternative (987 − 160 = 827 lines) is **not reachable** by transcription: the fields
  are only propositionally equal, the row predicates take the map in a type position, and no
  transport library for that exists in the port. The 736-line gap is the price of *inventing* one, on
  a vocabulary the pin never used — so it is not on the table for this set.
* Either way it is one set by the staffing rule (§0.2, ~1,500 content lines), split as two dispatches
  because layer 0 must be built and checked before either headline starts — and layer 0 is now
  landed (§5.4).

## 7. Risks and stop conditions

* **The `attribute [-]` walls.** Both pin wrappers carry long `attribute [-instance]`/`[-simp]`
  blocks (the 22-line leaf's wrapper has the longest in the cone). The port's convention is to try
  without them (HD1 did, successfully); if a module needs one, it is added file-scoped with a header
  sentence naming the load-bearing line.
* **`heckeOperatorBar` ≠ `heckeOperatorOneBar`.** The abstract capstone is about the `Bar` family on
  `JZero N` (the `modularFunctionFieldFull` fields); the pair is about the X₁/X_H rows. `HeckeCommuteBar`
  is the *template*, not a drop-in: the concrete proofs re-run the roof on their own fields. Do not
  try to transport the capstone along an identity it does not have.
* **The `if h : HeckeInputs*` design.** Both operators are `if h then … else 0`; the proof splits on
  the predicate and closes the failing branch with `simp`. A "clean" restatement that drops the
  zero branch changes the statement — not allowed.
* **`ℓ = ℓ'` and `ℓ ∣ M`.** Both are in scope of the statements: the first by `rfl` under
  `Nat.Primes` (the X₁ headline) or by the hypothesis `ℓ = ℓ' ∨ Coprime` (the pointwise form), the
  second through the β fallback. Any proof that assumes `ℓ ≠ ℓ'` and coprimality globally will fail
  the checker.
* **Two group vocabularies.** `Γ₁(M) ∩ Γ₀(Mℓ)` and `Γ_H(M) ∩ Γ₀(Mℓ)` differ only in the group, and
  §4 settles the second half of this bullet: `cocycle_inf` and `cocycle_one` **are** the same
  statement once `CohCarrier.GammaH M H` is read as `Gamma1 M` (38 vs 30 lines, 12 vs 12), so by this
  note's own instruction they are the lemmas to promote in the second pass, not to pre-factor now.
* Stop-early: if layer 0's `Nice`/`roof` block cannot be stated without the α/β maps (i.e. a
  `Nice` lemma needs the side's maps in its *statement*), the generic layer shrinks and the cut is
  re-measured before layer 1 starts.

## 8. What this buys

The last layer of the Hecke-row column on both sides of the Γ_H/Γ₁ split: `heckeOperatorOneBar_comm`
and `heckeOperatorHAlong_comm` are exactly the row data the capstone `heckeOperatorsCommuteBar`
consumes, so after this set the `X₁`/`X_H` Hecke-row statements (`HeckeDiamondCommuteBar`, the Hecke
algebra on the Tate module) become one-hop. It also finishes the `Place` degree API
(`sum_ramification…`) and closes the two gaps the frontier does not count (the operator definitions).

## 9. The degree layer comes first — the α/β `finrankAlong` family

The pair in §0 is **not** the next dispatch: the shelf head after HD1 is
`ModularCurve.finrankAlong_heckeBetaOneBar`, the β-row (q ↦ q^ℓ) degree, which is the sibling of
what HD1 landed and consumes its α headline. The whole degree layer is one family of eleven nodes:

| node | lines | state |
|---|---:|---|
| `finrankAlong_heckeAlphaOneBar` | 495 | **ported** (HD1) |
| `finrankAlong_heckeAlphaHBar` (ℓ ∤ M) | 384 | **ported** (HD1) |
| `finrankAlong_heckeBetaBar` (abstract `Bar`) | — | **ported** (`Degree/Roof.lean`) |
| `finrankAlong_heckeAlphaHBar_pos_and_le_relIndex` | — | open |
| `finrankAlong_heckeAlphaC_residueField_eq_add_one` | — | open (charP tail) |
| `finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_add_one_of_charP_of_dvd` | — | open (mod-ℓ tail) |
| `finrankAlong_heckeAlphaModLH_eq_and_relfinrank_eq_of_charP_of_dvd_div` | — | open (mod-ℓ tail) |
| `finrankAlong_heckeBetaModLH` | — | open (mod-ℓ tail) |
| `finrankAlong_heckeBetaOneBar` | 334 | **ported** (HD1b) |
| `finrankAlong_heckeAlphaHBar_of_dvd` (p ∣ M) | 418 | **ported** (HD1b) |
| `finrankAlong_heckeBetaHBar` | 349 | **ported** (HD1b) |

The three ready ones landed as `WORKORDER-HD1b` (one dispatch, extending the two HD1 modules): they
were the same computation as HD1's headlines on the same four nested fields, and twenty declarations
of each pin file were already public in `ModularCurve.HeckeDegree`. The degree layer is now left with
the mod-ℓ/charP tail, which is a different subject (residue-field degrees at characteristic `p`) and
belongs to its own order. The six `private` β-tower lemmas duplicated between the two β proofs were
promoted into the engine by `WORKORDER-HD1c` (dedup now 0 clusters over the two degree modules), so the
degree layer is closed except for the mod-ℓ/charP tail.

Only then does the commutativity pair (§0) make sense as a set: it is the *row* layer above these
degrees, and its own missing pieces are the 22-line Place identity, the two operator definitions and
the roof machinery (§5 layer 0). The two work orders are therefore `WORKORDER-HD1b` (degree layer,
now) and `WORKORDER-HD3` (the pair, after it); `WORKORDER-HD2` in §5 is the substrate of `HD3` and is
unchanged.
