# SET MS-1 — the Fricke pull-back on the base-changed `X_H` field and its Galois twist

**Status: landed (2026-10-28), first order of wave 1.** Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U1**, §2, §3, §4; brief
[WORKORDER-MS1-fricke-galois.md](WORKORDER-MS1-fricke-galois.md). One row, one new module, no
manager lane.

| figure | priced (§0.3 of the shelf note) | measured |
|---|---:|---:|
| rows | 1 | 1 |
| silo | 1,176 | 1,176 |
| net new math lines | ≈1,008 | **1,008** (declaration lines 1,154 − in-port 146) |
| module | **new** `ModularCurve/XH/FrickeGalois.lean` | 1,293 lines, 131 declarations |
| declarations | 125 pin | **1 public + 130 private** (125 pin + 6 v4.34 adapters) |
| definition gate | none | none |
| migration | none | none |

## 0. What landed

`ModularCurve/XH/FrickeGalois.lean`: `ModularCurve.exists_algEquiv_xHFunctionFieldBar_slash_fricke_and_galois_smul`,
statement verbatim from `Theorems/Thm_…`, proved from the pin's 13-section `S_` file transcribed in
order — `Groups` (the `frickeGL`/`frickeForm`/`scalarGL` block), `QExp` (the `qC` block), `Coeff`
(the `*_mem_ratios` block, `ratioField`), `Spec`/`Rep` (`coeffMap`/`gen`/`rep_*`), `Diamond` (the
`DiaP` block), `LawTwo` (`qW`), `Cyclo` (`frickeOneConst`), `Span` (the `FrP` block), `FrickeQ`
(`wAlg`/`wEquiv`), `Construction`, `GaloisLaw` (`galois_gen`/`conjAlgHom`/`galois_law`), headline.
The whole engine is `private` in the inner namespace `ModularCurve.FrickeGalois`; the wire is one
statement, and the header records the split.

Imports are exactly the two the brief names (`XH/Operators`, `XH/FrickeSlash`) — the planned set was
verified before dispatch to cover all four modules the row names, and it did.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | **1 ok / 0 mismatch / 0 missing / 0 own** (`…_slash_fricke_and_galois_smul -> Theorems/Thm_…:9`) |
| `#print axioms` | `[propext, Classical.choice, Quot.sound]` |
| module build | `Build completed successfully (4243 jobs)`, `exit=0` |
| edit loop (200k cap) | silent, zero warnings |
| `dedup.py --within --tier shape` | **0 duplicate clusters**, 0 removable lines |
| `move_dead.py --dry-run` | 1 "dead" = the public headline (API); 0 live private helpers |
| `set_option` | only the project-universal `autoImplicit false`; no heartbeat cap |

## 2. Deviations from the brief (all forced, all recorded in the module header)

1. `ΓGL` is **imported** (`ModularForm.Level.ΓGL`, already in the closure); the pin declares its own
   identical abbrev. This is a dedup win, not a copy.
2. `frickeGL` body is `ALTraceIdentity.frickeGL M (NeZero.ne M)` — trap 1 honoured: no third copy,
   no promotion.
3. `qC_mul` (and the `cross_mul_eq` family) go through `ModularForm.qExpansion_mul_coe`: the pin's
   `qExpansion_mul` needs `[Γ.HasDetPlusMinusOne]` on the form level in v4.34.
4. Deprecated spellings replaced to stay warning-free: `ModularForm.coe_add/coe_sub/coe_zero` →
   `FunLike.…`; `AlgEquiv.coe_algHom` → `AlgEquiv.coe_toAlgHom`.
5. `qC_ne_zero_of_witness`: the pin's `map_ne_zero_iff _ (RingHom.injective _)` does not exist in
   v4.34; a one-line private `coeffMap_injective'` (general ring hom + injectivity) backs both it
   and `coeffMap_injective`.
6. `wfun` is a plain `private def` + `rfl` `wfun_def` instead of the pin's `irreducible_def` (that
   tactic is outside the two-import closure); same downstream interface.
7. `conjAlgHom.commutes'` via `SemilinearAut.smul_algebraMap` (the port's spelling — `baseAut` is a
   `RingEquiv` here) instead of the pin's `commutes` chain.
8. `exists_gamma0_upperLeft` via `CohCarrier.gamma0Units_surjective M d⁻¹`, with the binder
   ascription `⟨γd, γd.2⟩` so `rw [← h1]; rfl` fires on the port's explicit `inv` field.
9. The pin's `_root_.A2FRE.coeffMap_coeffEmb` (general `ι : ℚ̄ →+* ℂ`) is **re-proved privately** as
   `coeffMap_coeffEmb_gen`: the port's copy lives in `X1/DiamondCorrespondence` (outside this
   module's closure) and `Defs/Laurent.coeffMap_coeffEmb` is only the `≃ₐ[ℚ]` case. This is the one
   place a promotion was *considered* and rejected for this order (the module is the only consumer
   in the closure) — a wave-2 candidate if another row needs it.
10. Three `mapGL` adapters copied from `XH/FrickeSlash.lean`'s adapters (the pin's coercion
    computation does not fire in v4.34). Same-subject duplication, recorded for `dedup.py`'s eye.
11. Pin scaffolding not transcribed: `p2m_open/export/reactivate`, the `P2MW.S_`/`A2FRE`
    namespaces, `attribute [-simp]` preludes.
12. The pin's `hT'` renamed `diamond_T_mem`; same proof term.

## 3. What this row unlocks (forecast, from the consumer scan of the shelf note §7)

Five direct consumers of 1,097–1,149 silo: `exists_frickeAlgEquiv_xHFunctionFieldBar` (1,105),
`…_galois_smul` (1,097), `frickeAlgEquiv_pic0_laws_of_slash_fricke_of_galois_smul` (1,109),
`heckePic0HBarTranspose_smul_diamondHBar_smul_smul_of_qExpansion_slash_fricke` (1,098), and the
`X₁ × X_H` triple (1,149) — the ≈5.5k-silo **Fricke block** that is the family's next shelf. The
`JHNeronObjectAtP` row (1,626) also consumes it on the Tate side.

## 4. What this set does not do

- It does not claim `w`'s first conjunct for any concrete form (the statement is the law, not an
  instantiation): the consumer zone
  ([spec/ModularCurveReady1Consumer.lean](../../spec/ModularCurveReady1Consumer.lean) zone A)
  unpacks the second conjunct and derives the identity-Galois corollary.
- No promotion, no migration, no `PORT_FILES` edit, no marker row.
