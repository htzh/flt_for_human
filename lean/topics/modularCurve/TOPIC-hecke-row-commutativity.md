# The Hecke-row commutativity on `J₁(M)` and `J_H(M)` — mathematics, and the shape of the port

Scoped 2026-10-22, after `WORKORDER-HD1` landed the α-row degree pair. This note is the blueprint for
the last layer of the Hecke-row column: the two concrete commutativity theorems
`ModularCurve.heckeOperatorOneBar_comm` (X₁) and `ModularCurve.heckeOperatorHAlong_comm` (X_H), which
are **the same development twice** over two group vocabularies. It records what the port already has,
what is genuinely missing, and the cut the next two work orders implement: `WORKORDER-HD2` (the
substrate, §5 layer 0) and `WORKORDER-HD3` (the pair, §5 layer 1).

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
`JH M H`. Both are **unconditional**: for every prime $\ell$, including $\ell \mid M$ (the `U_ℓ`
case), and for $\ell = \ell'$; no coprimality or distinctness is assumed in the statement.

## 1. The mathematics

Fix `M`, a prime `ℓ`, and let `F = x1FunctionField M` (resp. `xHFunctionField M H`) be the
q-expansion function field of $X_1(M)$ (resp. $X_H(M)$), and
`F_ℓ = x1x0FunctionFieldC ℚ M (M*ℓ)` (resp. `xHTopFunctionFieldC ℚ M H (M*ℓ)`) that of
$X_1(M)\cap X_0(M\ell)$. Everything happens over `L = AlgebraicClosure ℚ`, on
$\bar F = F\otimes L$ and $\bar F_\ell = F_\ell\otimes L$ (in the port: `laurentBaseChange L`).

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
| `Pic0.correspondence_correspondence_comm`, the push–pull exchange, ramification/inertia transport, `hasPrincipalDivisors_of_transcendental`, `separableAlong_of_charZero`, `finrankAlong_eq_relfinrank_fieldRange`, `qExpand`/`coeffMap`/`laurentBaseChange` API | `AlgebraicCurve/…`, `ModularCurve/Defs/Laurent.lean` | the engine below both files |

## 3. What is missing

1. **`AlgebraicCurve.Place.sum_ramificationIndexAlong_mul_inertiaDegAlong`** — 22 pin lines, the
   fundamental identity $\sum_{w \mid v} e_w f_w = [F':F]$ along an integral separable map. Unported;
   needed by both files (frontier lists it as the second needed node of each).
2. **`ModularCurve.heckeOperatorHAlong`** — `Def_…_XHHeckeOperator.lean:195`, the additive endo on
   `JH M H` (`if HeckeInputsHAlong … then heckePic0HBar … else 0`). `XH/HeckeOperator.lean`'s header
   explicitly left it "off this cone"; it is now on it.
3. **`ModularCurve.heckeOperatorOneBar`** — `Def_…_X1HeckeModule.lean:36`, the `Module.End ℤ`
   wrapper of the already-ported `heckeOperatorOneAlong`. One line, but it is the statement's head.
4. **The generic prelude** — see §4.
5. **The two side modules** — the Γ₁/Γ_H cocycle and q-expansion prelude, the roof and the legs, the
   divisor-level square, and the headline.

## 4. The twinship, measured

| | `OneBar_comm` | `HAlong_comm` |
|---|---:|---:|
| pin `S_` lines | 979 | 993 |
| declarations | 98 | 98 |
| **shared names** | **94** | |
| line similarity | 0.62 | |
| statements already in the port (`port_advise`) | 20 (≈190 lines) | same, plus the twins' own |

The files are layered, and the layering is the cut:

* `…CommGeneric` (~20 declarations: `isAlgebraic_adjoin_of_transcendental`,
  `finiteDimensional_adjoin_of_transcendental`, `finiteAlong_of_transcendental`,
  `isIntegral_of_finiteAlong`, `finrankAlong_pos_of_finiteAlong`, **`pushforwardAlong_pullbackAlong`**,
  `correspondence_comp_eq_smul`, `correspondence_congr`, `eq_of_zsmul_eq_zsmul`,
  `fieldRange_val_comp_inclusion`, `finrankAlong_inclusion`) — **group-agnostic and identical in both
  files**; two of them are already public in `HeckeDegree`.
* `…CommFields` (~25: `qExpAlgHom`, `coeffMap_qExpand`, `coeffEmb_qExpand`,
  `laurentBaseChange_mono`, `qExpand_mem_laurentBaseChange`, the `T_mem_*`/`Gamma0_le_of_dvd`, the
  **cocycle** computation `cocycle_inf`/`cocycle_one`, `KK`/`KT`, the subsets, `heckeBetaOneDefined`,
  transcendence, `qExpTo`) — the q-expansion/group vocabulary, **side-specific** (the 4 names that
  differ, and the 3 `Γ₁`→`Γ_H` renamings).
* `…CommRoof` (~40: `QQ`/`roof`/`BB`, the `Nice` predicate and its 8 consequences, `nice_*`, the
  legs `legU`/`legU'`/`legP`/`legI`, `hgen`, `finrankAlong_alpha`/`beta`/`diag`, `relfinrank_KK_roof`,
  `hsq`, `exchange`, `heckeDiv_heckeDiv`) — the field part (`QQ`/`roof`/`BB`/`Nice`/`nice_*`) is
  generic; the leg and degree lemmas mention the side's maps.
* `…CommMain` (~10: `RR`, `nice_RR`, `heckeDiv_comm`, `…Along_comm`) — side-specific.

So **~38 of the 98 declarations are provably shared**: the generic prelude plus `Nice`/`roof`/`BB`
(the field constructions and their 8 `Nice` consequences, which never mention α/β).

## 5. The proposed structure

Three layers, five modules. The rule is the port's own: *the shared mathematics is public and
written once; the side-specific row data is `private` behind its one headline*.

**Layer 0 — substrate (one dispatch, small).**

| module | content | why there |
|---|---|---|
| `AlgebraicCurve/Place/FundamentalIdentity.lean` (or the existing `Place/ValueDictionary.lean`) | `sum_ramificationIndexAlong_mul_inertiaDegAlong` | it is the degree-of-a-place-fibre identity, next to the place-valuation dictionary; the pin's wrapper's `attribute [-]` wall is not transcribed |
| `ModularCurve/XH/HeckeOperator.lean` (extend) | `heckeOperatorHAlong` | the tail of its own pin file; the module's header already explains why it was left out, and this order is the "on this cone" it awaited |
| `ModularCurve/X1/HeckeModule.lean` (extend) | `heckeOperatorOneBar` (one line, from `heckeOperatorOneAlong`) | its own pin file (`Def_…_X1HeckeModule.lean:36`) |
| `ModularCurve/HeckeRoof.lean` (**new**, public) | the generic prelude (`…CommGeneric`) + `Nice` and the `roof`/`QQ`/`BB` field constructions with their 8 consequences | used by both sides; the port already keeps `HeckeCommuteBar.lean` at the `ModularCurve/` root for the same reason |

**Layer 1 — the pair (one dispatch, two modules).**

| module | content | public surface |
|---|---|---|
| `ModularCurve/X1/HeckeCommute.lean` | the Γ₁ fields/cocycle prelude, the legs, `finrankAlong_*`, `relfinrank_KK_roof`, `hsq`, `exchange`, `heckeDiv_heckeDiv`, `RR`, `heckeDiv_comm`, `heckeOperatorOneAlong_comm` | `ModularCurve.heckeOperatorOneBar_comm` only |
| `ModularCurve/XH/HeckeCommute.lean` | the same with `Γ_H`, `xHFunctionField`/`xHTopFunctionFieldC`, `heckeAlphaHBar`/`heckeBetaHBar` | `ModularCurve.heckeOperatorHAlong_comm` only |

Names: the headlines keep their pin names and their wrappers' statements (the checker diffs them);
everything else is `private` (the pin makes all of it public in the `S_` files, but it is machinery —
the port's "pin-public keeps its name, private machinery may be private" rule, applied to
`P2M/Sol/S_` declarations that the checker never sees).

Wires: one `spec-pin:` pair (wrapper + `S_`) per module for the pair; the layer-0 modules wire to
their own pin files, and the two extensions to the `Definitions/` files they complete.

## 6. Price, in the port's units

* Pin lines: 979 + 993 = **1,972**, 196 declarations.
* Already in the port: 20 statements (≈190 lines) + the whole `AlgebraicCurve`/`HeckeCommuteBar`
  engine below.
* Shared and written once: ~38 declarations (≈450 lines) → layer 0.
* Side-specific: ~60 declarations each (≈450 lines each) → layer 1.
* Net new: ≈ **1,350–1,450 lines** over 5 modules — one set by the port's staffing rule
  (§0.2, ~1,500 content lines), split as two dispatches because layer 0 must be built and checked
  before either headline starts.

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
* **Two group vocabularies.** `Γ₁(M) ∩ Γ₀(Mℓ)` and `Γ_H(M) ∩ Γ₀(Mℓ)` differ only in the group, but
  the cocycle lemmas (`cocycle_inf`/`cocycle_one`) are where the two files genuinely diverge. If
  they turn out to be the same statement after all, promote them in the second pass — do not
  pre-factor them.
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
