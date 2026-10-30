# SET MS-5 — the complex-place dictionary: existence, the `Γ₀(M)` pull-back, and conjugation

**Status: landed (2026-10-28), fifth order of ready shelf 1** (after a pause/resume: the module was
parked mid-order as a non-compiling draft in `tmp/ms5/` and finished on resume). Ready shelf 1
([TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md)) §0.4 **U3**, §1, §2, §3, §4; brief
[WORKORDER-MS5-place-dictionary.md](WORKORDER-MS5-place-dictionary.md). Three rows, **one** new
module, one shared engine, no manager lane.

| row | silo | home | checker | promotion (§9.1) |
|---|---:|---|---:|---:|
| `exists_complexPlaceDictionaryOf` | 441 | **new** `ComplexPlaceDictionaryAction.lean` | 1 ok | — |
| `ComplexPlaceDictionaryOf.ofAlgAut_smul_pt_eq_pt_inv_smul` | 684 | same module | 1 ok | — |
| `ComplexPlaceDictionaryOf.arithmeticGalois_complexConjAlgEquiv_smul_pt` | 648 | same module | 1 ok | — |
| **module** | **1,345 lines** | 3 public + 86 private | **3 ok / 0 / 0 / 0** | → **71 ok / 0 / 0** |

| figure | priced | measured |
|---|---:|---:|
| rows / silo | 3 / 1,773 | 3 / 1,773 |
| net new math lines | ≈1,130 | 1,130 (the three `S_` files' declaration lines 1,698 − 511 duplicate copies − 57 in-port) |
| declarations | 169 pin (48 + 59 + 62) | 3 public + 86 private |
| imports | 7 port modules | **exactly the seven** the brief named — no addition needed |

## 0. What landed

One module, one engine, three headlines:

- **441** — `ModularCurve.exists_complexPlaceDictionaryOf`: the pin's `Pres` (multiplicative,
  additive, constant and inverse-preserving) and `mu` (the meromorphic-order function, with
  `exists_mu_pos`, `mu_smul`, `mu_nonneg_iff`) path, closing on
  `AlgebraicCurve.Place.exists_of_orderMap`; the dictionary record is assembled in the private
  `dictionaryOf`.
- **684** — `…ofAlgAut_smul_pt_eq_pt_inv_smul`: `gammaH_le_conj` → `slashForm` →
  `IsPullbackAlong` → the `Key` block over `Subfield.closure` (`key_algebraMap`,
  `key_add/mul/neg/inv`, `key_generator`, `key_all`) → the place-level `smul_pt_eq`.
- **648** — `…arithmeticGalois_complexConjAlgEquiv_smul_pt`: `qParam_J_smul`,
  `conj_apply_J_smul_of_isIntegralQExp`, the `kappa` family, the conjugation `Key` block, the `J`
  transport and `smul_pt_eq`.

The pin's `qL`/`qL_*`/`one_ne_zero'`/`mul_ne_zero'` are **not** rewritten: the port already has
them as the public `ModularCurve.RatioFieldOfGroup` copies in `X1/CoeffMap.lean` (the same module the
166 row went into), and they are imported.

## 1. Gates, as measured

| gate | result |
|---|---|
| `check_port --force` | **3 ok / 0 mismatch / 0 missing / 0 own** |
| `#print axioms` | all three `[propext, Classical.choice, Quot.sound]` |
| build (workspace lock) | `✔ Built FLTForHuman.ModularCurve.ComplexPlaceDictionaryAction (17s)` / 4,399 jobs / `EXIT=0` |
| edit loop (200k cap) | silent, zero warnings |
| `dedup.py --module … --within --tier shape` | **0 duplicate clusters**, 0 removable lines — the 511-line triplicate of the pin became one engine |
| `spec-pin:` lines | 6 |
| `set_option` | only the project-universal `autoImplicit false`; no heartbeat cap |

## 2. Deviations (all recorded in the module header; none touches a statement)

1. **One engine, private.** The `Pres`/`mu`/`realize_*` block, the Möbius transport and the two
   generic place/boundedness lemmas are single copies; the 684/648 duplicates of the pin are one
   statement at `γ` and at `J`.
2. **`moeb`/`isBoundedUnder_comp_smul_iff`/`mem_smul_place_iff`** are stated at `g : GL (Fin 2) ℝ`
   (and over `F₀`), the two pin spellings being the two instances.
3. **648's `Key` block** lives in the nested `PlaceDictionaryAction.ConjPlaceTransport`, because both
   pin files name `Key`/`key_*`/`smul_pt_eq` and two private declarations of one name in one file
   would collide.
4. **No `SMul SL(2, ℤ) ℂ` in the port**, so 684's `Key` laws are stated at the coerced action
   `((γ : GL (Fin 2) ℝ)) • ·`, bridged by `sl_smul_upperHalf` (`by simp`). Places untouched.
5. **Instance discipline**: `omit hT` / `omit [NeZero M]` replace the pin's
   `linter.unusedSectionVars false`; `[NeZero M]` is dropped from the two private 684 sections that
   never use it (the headline keeps it verbatim). `haveI` under a Prop goal is refused by
   `linter.style.haveILetI`, so 441's `Fact` instance is an explicit argument of `dictionaryOf` and
   648's `Fact (IsCusp ∞ Γ)` is a `local instance`.
6. **Proof-only refactors**: `Pres.slash_pres_ne` names `Pres.inv`'s inline obligation;
   `@[scoped simp]` on `coe_slashForm` dropped (its consumer rewrites explicitly); deprecated names
   refreshed (`FunLike.coe_zero/add/smul`).

## 3. The pause/resume episode (recorded because it is a process fact)

The order was interrupted with the module at 1,298 lines and **18 elaboration errors**. The draft was
moved out of the port tree (`tmp/ms5/ComplexPlaceDictionaryAction.draft.lean`) because a
non-compiling module must not sit in `FLTForHuman/`, and restored on resume; the engine then went in
in one pass (the errors were all in the `Pres`/`mu`/`realize_*` block, not in the statements — the
checker already read 3 ok on the draft).

## 4. What this story unlocks

- 441's consumer `ComplexPlaceDictionaryOf.heckeDivHBar_single_pt` (1,215), and from the 684/648 pair
  the `exists_bijective_heckeEquivariant_addMonoidHom_pic0_complex_xH_quotient_periodLatticeOf` pair
  (817 / 796) — the Pic⁰-complex dictionary.
