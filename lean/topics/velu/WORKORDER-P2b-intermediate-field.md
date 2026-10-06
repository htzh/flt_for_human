# P-2b work order — the countable descent (D-2)

**Status: open, 2026-10-06.** Set D-2 of [WORKORDER-P2-basechange.md](WORKORDER-P2-basechange.md).
New-file-only. Pin `anthropics/fermats-last-theorem@aa2d8b3`; port mathlib `v4.34.0`.
Depends on set D-1 (`FLTForHuman/WeierstrassCurve/Isogeny/BaseChange.lean`), which must be
reviewed and landed first. Method: [../../porting-playbook.md](../../porting-playbook.md)
§2.4, §3.1–§3.2, §3.5, §3.7, §4.

## 1. Scope

Port the headline

```
WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq
```

(2,684 pin lines) together with the descent block it rests on: the `TreeIsogenyEndDatum`
descent vocabulary (`kw_iPFA*`, `kw_iPFE*`, `kw_iP*`, `kw_iA*`, `kw_iCa*`, `kw_iPF*`,
`kw_iota*`, `KwIsogenyEndDatum{FGFieldDescent,IotaDescendToFG,SubfieldDescent,…}`), the
`kw_baseChangeToAC*` block, and the `kw_iE2E*` wrappers — 93 node-unique declarations,
1,878 pin lines (plus the headline's own proof). Everything else it needs is D-1.

**Not this set:** anything in D-1 (the shared prelude: `pointPullback*`,
`kw_functionField_algHom_ext`, `kw_coordinateRingBasis`, `TreeIsogenyEndDatum` / `degree`
— those are D-1's; import them), the `mrtw60a*` variable-change block (D-3), the
`kw_surgehgf4_pck*` block (D-4), and the `kw_surge_hgf4_*` / `KwD5BetweenCurves*` seam
(D-4/D-5). Stop at the boundary and report rather than widening.

## 2. Source (pin)

`P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
(2,684 lines), namespace `P2MW.S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq`.
The wrapper `Theorems/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
is the statement authority **for the headline only** — spell its binders exactly (note it
uses `{K : Type u}`, the `S_` file's `solution` uses `{K : Type uK}`; the wrapper wins).

The declaration groups, by pin line (read each region; the pin's `p2m_export` machinery is
dropped and no `p2m_*` line is transcribed):

| lines | contents |
|---:|---|
| 525 | `of_module_finite` (228) |
| 798–870 | `KwIsogenyEndDatumFGFieldDescent`, `KwIsogenyEndDatumSubfieldDescent{,,''}` (defs, with the `of_module_finite` interface) |
| 857–930 | `KwIsogenyEndDatumIotaDescendToFG{,,''}` |
| 982–1480 | the `NoAC` tensor block **and** `kw_baseChangeToAC_uncond` (55), `KwIsogenyEndDatumBaseChangeToAlgebraicClosure{,,''}` — **check D-1 first**: the tensor `…NoAC` declarations (982–1480) are D-1's; only the `kw_i*` / `KwIsogenyEndDatum*` descent declarations in this range are yours |
| 1482–1730 | `kw_iA_{CoeffsHyp,phi,phiEquation,phiCRCompat,phiTranscendental,crDescend,crDescend_map,polyDescend,polyDescend_map,polyToFF_eq_aeval}`, `kw_iP_{xP,yP,xP_spec,yP_spec,ι₀,ι₀_X,ι₀_yGen,equation,transcendental}` |
| 1718–1870 | `KwIsogenyEndDatumSubfieldDescent`, `KwIsogenyEndDatumFGFieldDescentIotaAtom'`, `kw_iotaAtom_…`, `kw_subfieldDescent_…`, `kw_iotaSubd_countable_of_fg`, `kw_fgFieldDescent_of_subfieldDescent_of_baseChangeToAC` |
| 1887–2050 | `kw_iCa_{K₀,K₀_fg,K₀_mem_aᵢ,E₀,E₀_map,ffNum,ffDen,ffCoeffSet,ffCoeffSet_subset_X,ffCoeffSet_subset_Y,crRepr,crRepr_coeff_mem,crCoeffSet,crCoeffsIn_of_ffCoeffSet_subset,crCoeffsIn,D'}` |
| 2099–2230 | `kw_iPF_{phi_X,phi_yGen}`, `kw_iotaPinnedFinrank_of_finiteSeam`, `kw_iotaDescendToFG_of_canonicalFinrank`, `kw_iCaW_*` |
| 2251–2600 | `kw_iPFA_{isTranscendenceBasis_coord,isAlgebraic_adjoin_transcendental,finiteDimensional_adjoin_transcendental,finiteAlong}`, `kw_iotaPinnedFiniteSeam_of_finrankEq`, `kw_iPFE_{functionField_ringHom_ext,canonicalFinrank_uncond,pinnedFinrank_uncond,finrankEq,iotaDescendToFG_uncond}` |
| 2612–2650 | `kw_iE2E_{iotaDescendToFG_of_iotaDescendToFG'',iotaDescendToFG_uncond,subfieldDescent_of_subfieldDescent'',subfieldDescent_uncond,fgFieldDescent_uncond}` |
| 2670 | `solution` → the headline |

Run `port_advise.py --nodes WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq`
before transcribing and import the hits; the tool's statement test is the contract.

## 3. Deliverable

**`FLTForHuman/WeierstrassCurve/Isogeny/IntermediateField.lean`** (new). Pin names and pin
namespaces; the headline from the wrapper's binders, every `kw_i*` helper `private` with a
content name (**no `kw_` prefix** for new private helpers). Imports D-1 and only what the
pin's specific imports require (`Mathlib.FieldTheory.IntermediateField.*`,
`Mathlib.RingTheory.TensorProduct.*` as needed; never `import Mathlib`).

## 4. Route, with recorded negatives

- **The descent is generic field theory, not Weierstrass geometry.** The proof descends the
  pair `(E, ι)` to a countable `K₀ ≤ K` and compares `finrankAlong` at `K` and
  `AlgebraicClosure K₀`. Keep the pin's structure; do not "simplify" the statement.
- **`TreeIsogenyEndDatum` and `degree` are D-1's.** If D-1 named them differently, stop and
  report rather than re-declaring them.
- **The `NoAC` tensor block in lines 982–1480 is D-1's.** Reuse it; only the descent block
  is new.
- **`finrankAlong` is already ported** (`WeierstrassCurve.FunctionFieldFinite` /
  `AlgebraicCurve` FiniteAlong API). Import; do not re-derive.
- **Binder spellings.** The headline must use the wrapper's `Type u` binders and
  `WeierstrassCurve.exists_intermediateField_countable_map_eq_and_finrankAlong_eq`.

## 5. Bound and stop conditions

Stop and report: an unported prerequisite outside §2; a `NoAC`/`General` mismatch with D-1;
a statement that does not transcribe to `v4.34.0`; any pull toward the S row or the
`eval_modularPolynomial_…` capstone.

## 6. Build discipline (binding)

> `lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>` is the edit loop;
> `lake build <module>` when done; **one** `lake build` per wave, `flock`ed on
> `.lake/flt_build.lock` and bounded (`timeout 60`/`90`/`300`), timed wall + user/sys.
> Never raise `maxHeartbeats`. Iterate in bounded blocks, not per declaration.

The `finrankAlong`/intermediate-field proof is the one place a `maxRecDepth` bump may be
needed; if so, restructure (explicit instance / `set_option maxRecDepth` **inside one
declaration** is allowed only if the pin does it — prefer restructuring).

## 7. Verification

- `lake env lean` clean; `lake build FLTForHuman.WeierstrassCurve.Isogeny.IntermediateField`.
- Append the module to `PORT_FILES` (last); append
  `Theorems/Thm_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
  and `P2M/Sol/S_WeierstrassCurve_exists_intermediateField_countable_map_eq_and_finrankAlong_eq.lean`
  to `SOURCES` (last, wrapper first) if D-1 did not already.
- `python3 spec/check_flt_statements.py` → 0 mismatched / 0 missing; reconcile the delta
  against §2.
- One `spec/` zone composing the headline with a concrete curve and a ported
  `finrankAlong` fact, or a hypothesis-form test if a concrete instance needs unported
  hypotheses; deleting the module must make the zone fail.
- `#print axioms` on the headline: `[propext, Classical.choice, Quot.sound]`; no `sorry`.
- Whole-tree `flock`ed `lake build`; jobs + seconds. `grep -c` of every drop, in the log.
