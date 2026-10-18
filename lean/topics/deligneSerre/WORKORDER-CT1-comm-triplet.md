# WORKORDER-CT1 — the `CohCarrier` Hecke–diamond commutation triplet

**Status: landed 2026-10-17.** Parent record:
[TOPIC-cohcarrier-comm-triplet.md](TOPIC-cohcarrier-comm-triplet.md) §1–§6; its §6 (the
definition layer) was already green when this order was dispatched.

Measured outcome: engine `ModularForms/CohCarrier/Engine/CommTriplet.lean`, 1,022 lines,
**89 declarations** (the pin's 90 minus the top-level `solution`); tier-1 façade
`ModularForms/CohCarrier/CommTriplet.lean`, 46 lines, **3 headlines**. Both green with 0
errors and 0 warnings, `lake build` green. Checker `9854 → 9857 identical (+3)`, 0
mismatched / 0 missing; `#print axioms` on all three headlines
`[propext, Classical.choice, Quot.sound]`. The engine is registered in
`spec/UNWIRED-PUBLIC.md` with all 89 pin originals. The worker's one proof adaptation
(`Prime.not_unit` → `Prime.not_isUnit`) and its scoped-attribute choice (global
`attribute [instance] HeckeFamily.instFintype`, plain `@[simp]` on the twelve entry
lemmas) are recorded in the engine header.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port
mathlib `v4.34.0`.

## 1. Scope

Port the pin's **one deduped development** that yields the three graph leaves
`CohCarrier.heckeT_diamondRaw_comm`, `CohCarrier.heckeT_comm_of_prime`,
`CohCarrier.diamondRaw_comm`. The three `P2M/Sol/S_CohCarrier_*.lean` files are
byte-identical except the final 5–6-line `solution`, and each file carries **all three**
`_impl`s; so port the shared development **once**, with all three kernels, and re-prove the
three headlines in a tier-1 façade. In-scope node:
`P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean`, taken whole (§2.3).

**Not this topic:** the other nine `CohCarrier` nodes of the `--ds` demand (they share
nothing with this block), the off-demand 8-file `IharaMintRQ` family (do not port it; the
shared transfer prelude is kept family-neutral), any `spec/` edit, any topic/note edit,
`PORT_FILES` wiring and `UNWIRED-PUBLIC.md` registration — all the manager's.

## 2. Source

* Development: `P2M/Sol/S_CohCarrier_heckeT_diamondRaw_comm.lean`, 999 lines, **90
  declarations** (checker `raw_declarations`; the parent note's §2), **0 `private`**. The other two files (`…_diamondRaw_comm.lean`,
  `…_heckeT_comm_of_prime.lean`) are the same 986 lines plus their own `solution`.
* Statement authority for the three headlines:
  `Theorems/Thm_CohCarrier_{heckeT_diamondRaw_comm,heckeT_comm_of_prime,diamondRaw_comm}.lean`
  — the wrapper statements, **not** the pin's `solution`, are the check target.
* The development's layout (line ranges; see the parent note §2 for the section table):

| lines | namespace / section | content |
|---|---|---|
| 12–97 | `IharaSolRQ` | right-coset/transfer block: `coe_slip`, `cls_rep_mul`, `mulRight`, `toRight`, `secL`, `transL`, `toAdditiveLeft_transfer_apply`, `heckeT_apply_eq_sum_rq` |
| 101–300 | `IharaSolComm.HeckeFamily` | abstract `HeckeFamily` structure `(K, δ, act, η)` with `T`, `T_comp`, `act_eq_of_sameCosets`, `T_eq_of_sameCosets`, `T_comm_of_sameCosets`, `Distinct`, `ofDistinct`, `SameCosetsComm` |
| 303–434 | `IharaSolComm` (`DockHeckeT`) | `ιQ`, `ιΓ`, `alpha`, `famT`, `heckeT_eq_famT` |
| 437–539 | `CC3` | `αZ`, `comp_famT_distinct`, `heckeT_comm_of_sameCosetsComm` |
| 542–558 | `HeckeFamily.sameCosets_of_exhibit` | coset-exhibiting criterion |
| 561–744 | `Diamond` | `famD`, `diamondRaw_eq_famD`, `diamondRaw_congr`, `sigmaLow`, `sfac`, `gDiaSL`, `gDia`, `heckeDiamond_impl` (73 lines) |
| 747–815 | `CC3b` | `TwoSidedReduction`, `sameCosetsComm_of_twoSided` |
| 818–951 | `CC3bPrime` | `pMat`, `zMat`, `mem_GammaH_of_entries`, `isCoprime_of_prime_not_dvd`, `twoSidedReduction_of_prime`, `commPrime_impl` |
| 954–986 | `DiamondDiamond` | `diamondRaw_diamondRaw`, `commutator_mem_GammaH`, `twoDiamonds_impl` |

* All `p2m_reactivate "…"` lines (298, 301, 435, 540, 559, 745, 816, 952, 987, 990) are
  activation bookkeeping: **drop them** (see §4 for what to do with the scoped attributes).

## 3. Deliverable

Two modules, both under namespace `CohCarrier` (the pin's outer
`P2MW.S_CohCarrier_heckeT_diamondRaw_comm` wrapper is dropped, and its inner namespaces
become sub-namespaces of the port's `CohCarrier`):

```
FLTForHuman/ModularForms/CohCarrier/Engine/CommTriplet.lean     -- tier 3, unlisted
FLTForHuman/ModularForms/CohCarrier/CommTriplet.lean            -- tier 1, the three headlines
```

**Engine** — transcribe the whole pin development (90 declarations, the three `_impl`s
included), statements verbatim, proofs adapted only where `v4.34.0` forces it. Namespace map:

| pin | port |
|---|---|
| `P2MW.S_CohCarrier_heckeT_diamondRaw_comm.IharaSolRQ` | `CohCarrier.IharaSolRQ` |
| `…IharaSolComm` | `CohCarrier.IharaSolComm` |
| `…IharaSolComm.HeckeFamily` | `CohCarrier.IharaSolComm.HeckeFamily` |
| sections `CC3`, `Diamond`, `CC3b`, `CC3bPrime`, `DiamondDiamond` | the same sections under `CohCarrier.IharaSolComm` |

Every pin-public declaration stays public — no demotion, no `private`. The pin's top-level
`solution` is **not** transcribed (the façade replaces it). The three kernels keep their
names and signatures: `IharaSolComm.heckeDiamond_impl`, `IharaSolComm.commPrime_impl`,
`IharaSolComm.twoDiamonds_impl`.

**Façade** — the three headlines exactly as the `Theorems/` wrappers state them, each the
one-line application of the corresponding kernel, exactly as the pin's `solution` forwards:

```lean
namespace CohCarrier

theorem heckeT_diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    (σ : CongruenceSubgroup.Gamma0 M)
    (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : Matrix.SpecialLinearGroup (Fin 2) ℤ) 1 0)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (diamondRaw M H V σ F) = diamondRaw M H V σ (heckeT M H ℓ V F) :=
  IharaSolComm.heckeDiamond_impl M H ℓ σ hσ V F

theorem heckeT_comm_of_prime (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') {V : Type} [AddCommGroup V] (F : H1 M H V) :
    heckeT M H ℓ V (heckeT M H ℓ' V F) = heckeT M H ℓ' V (heckeT M H ℓ V F) :=
  IharaSolComm.commPrime_impl M H ℓ ℓ' hℓ hcop V F

theorem diamondRaw_comm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (σ σ' : CongruenceSubgroup.Gamma0 M)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    diamondRaw M H V σ (diamondRaw M H V σ' F) = diamondRaw M H V σ' (diamondRaw M H V σ F) :=
  IharaSolComm.twoDiamonds_impl M H σ σ' V F

end CohCarrier
```

Each of the three carries a `-- pin: <name> (Theorems/Thm_CohCarrier_<name>.lean:<line>)`
provenance comment. The façade header must name the engine as its tier-3 source.

## 4. Route and risks

**Imports.** Engine:

```lean
import FLTForHuman.ModularForms.Defs.CohCarrierLower
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Prime.Int
```

(the pin's `Definitions.Def_CohCarrier_Lower` is the port's
`FLTForHuman.ModularForms.Defs.CohCarrierLower`; `P2M.Util` is dropped). Façade: the engine.

**Available from the port** (do not re-prove): `CohCarrier.rep`, `cls`, `slip`, `uMat`,
`uElt`, `rightQuotEquivOfDvd`, `GammaHLower`, `conjLowerL`, `heckeTlower` in
`Defs/CohCarrierLower.lean`; `heckeT`, `GammaHUpper`, `conjL`, `conjUpperMat`, `LevelLE`,
`iotaDeg` in `Defs/CohCarrierLevel.lean`; `GammaH`, `H1`, `diamondRaw`, `gamma0Units`,
`conj_mem_GammaH`, `conjHom` in `Defs/GammaH.lean`.

**Attributes.** The pin sets `attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex`
at file top — copy it into the engine. The pin's `p2m_reactivate` calls activate the
`@[scoped simp]` / `@[scoped instance]` attributes of `IharaSolComm` and
`IharaSolComm.HeckeFamily` (`ιQ_coe_apply`, `ιΓ_coe_apply`, `actEquiv_apply`,
`HeckeFamily.instFintype`, …). Since `p2m_reactivate` is gone, either activate the scopes
(`open scoped CohCarrier.IharaSolComm CohCarrier.IharaSolComm.HeckeFamily`, placed after the
namespaces exist) or make those attributes global (`@[simp]`, `instance`); choose what keeps
the transcriptions working with the fewest proof changes and **record the choice in the
module header**. Do **not** reproduce the wrappers' `attribute [-instance]
CohCarrier.GammaHLower_finiteIndex` / `attribute [-simp] …uMat_apply_*` prelude: the port
keeps those global (parent note §7).

**Known `v4.34.0` frictions** (parent note §7, all verified in the definition layer):

* `MonoidHom.transfer_def` takes the transversal **before** the group element:
  `transfer_def ϕ T [FiniteIndex] g`; never `_` inside a `simp` argument list.
* `ext` on an `AddMonoidHom` equality may pick the `toMultiplicativeRight` extensionality;
  use `apply AddMonoidHom.ext; intro g`, and the pointwise argument is `Additive.toMul g`
  inside `toAdditiveLeft_apply_apply`.
* The `Subtype.val` vs `instCoeToMatrix` product-coercion obstruction: a `simp` will not
  unfold `↑(m * m')`. Force it with
  `show ((x * y : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = <explicit matrices> from by rw [Matrix.SpecialLinearGroup.coe_mul]; rfl`
  before the entrywise `simp` (`conjUpperMat_mul` / `conjLowerMat_mul` are the worked
  examples in `Defs/CohCarrierLevel.lean`).
* `Set.mem_setOf_eq` is deprecated → `Set.mem_ofPred_eq`; the port wants **0 warnings**.
* The style linter `linter.style.haveILetI` fires on genuine local `haveI` instances of
  `Prop` classes; suppress locally with `set_option linter.style.haveILetI false in` above
  the declaration rather than turning them into `have`/`let`.
* The pin's five imports suffice; `linear_combination`, `push_cast`, `group` are available.
* `Matrix.two_mul_expl a b` has shape `(0,0) ∧ ((0,1) ∧ ((1,0) ∧ (1,1)))`.

**Do not** substitute `Distinct`/`TwoSidedReduction` by `PeriodPair.DiscriminantNeZero`
(parent note §8) — they are bare `Prop` defs in the pin and different mathematics; write
them as in the pin.

**Stop-early protocol.** If a name cannot be matched, a prerequisite seems unported, or an
existing-module edit looks necessary, send a short message — "blocked on `<decl>` at pin
`:NNN`; likely needs `<X>`" — and keep working on independent parts. Never work around a
hub defect locally; never edit `spec/` or the notes.

## 5. Build discipline

* Edit loop: `cd lean && timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/ModularForms/CohCarrier/Engine/CommTriplet.lean`
  (then the façade). This writes no olean and recompiles nothing else.
* Tier 1 done: `flock .lake/flt_build.lock timeout 600 lake build FLTForHuman.ModularForms.CohCarrier.Engine.CommTriplet`
  then `… .CohCarrier.CommTriplet` — run as background jobs; each tool call must finish in
  under 2 minutes.
* **No tree `lake build`**, no `set_option maxHeartbeats`, no `sorry`, no `axiom`.
* Every tool call under 2 minutes; no loops to circumvent the limit.

## 6. Verification and report

* Both modules compile with **0 errors and 0 warnings** under the edit-loop command.
* `lake build` of both modules succeeds; no `sorry`.
* `#print axioms` on the three headlines: `[propext, Classical.choice, Quot.sound]`.
* Report: the two module paths; the exact declaration count/list (engine and façade); any
  proof adapted for `v4.34.0` (one line each); the scoped-attribute choice; the build wall
  times; the friction log. The manager wires `PORT_FILES`/`SOURCES` and runs the checker —
  do not touch `spec/` yourself.
