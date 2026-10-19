# `Gamma1_le_of_dvd` — a mathlib supplement, and the six copies it replaced

**Status: landed 2026-10-18.** One new module and six consumer edits; every edited module builds
green locally, the checker is unchanged at **10,476 identical / 0 mismatched / 0 missing**, and
`Lifting.lean` went from 18 warnings to 0.

| | |
|---|---|
| new home | `FLTForHuman/NumberTheory/ModularForms/CongruenceSubgroupOrder.lean` — 66 lines, 2 declarations (`CongruenceSubgroup.Gamma1_le_of_dvd`, `Gamma0_le_of_dvd`), tier 3, registered |
| consumers edited | `DeligneSerre/Lifting.lean`, `ModularForms/WeightOne/{IntegralWeightOneForm,Gamma0Integral,RationalityDvd}.lean`, `ModularCurve/X1/Defs.lean`, `ModularForms/Analytic/NormSqLt.lean` |
| copies removed | **4** (`private` in `Lifting` ×2 — the `Gamma1` and the `Gamma0` one —, `IntegralWeightOneForm`, `Gamma0Integral`) |
| copies wrapped | **3** onto the home, one line each (`X1/Defs` `{M'}`, `NormSqLt` `{N}`, `RationalityDvd` `Gamma1_le_of_dvd'`) |
| checker | 10,476 identical, 0 mismatched / 0 missing, 10,812 checked — **unchanged**, as expected (the wrappers keep the pin's statement text) |
| register | 136 → 137 modules, 4,134 → 4,136 public declarations; the home's two are the only additions |

## 1. Why this is worth a module

The lemma is three lines — unfold `Gamma1_mem`, push the three entries through
`ZMod.castHom h (ZMod m)` — but it is the level-monotonicity workhorse of every level-changing
construction, and mathlib has **no order lemma for `Gamma1`** (`CongruenceSubgroups.lean` has
`Gamma1`, `Gamma1_mem`, `Gamma1'`, `Gamma0Map` and nothing monotone). The pin re-declares it in
**12 files** and uses it at **135 sites**; the port had accumulated **five** copies (one public in
`ModularCurve/X1/Defs.lean`, one in P3's `NormSqLt.lean`, three `private`), each with a different
binder spelling:

| spelling | where |
|---|---|
| `{M' : ℕ} (h : M ∣ M')` | `Def_ModularCurve_X1.lean:158` and the `ModularCurve` silos |
| `{N : ℕ} (h : M ∣ N)` | the `CuspForm` silos (`Def_…_norm_sq_lt` pin:97) |
| `{M' : ℕ}` with a prime name | `S_ModularCurve_exists_ratCast_qExpansion_comp_smul_of_mem_Gamma0_of_dvd.lean:516`, as `Gamma1_le_of_dvd'` |
| `{A B : ℕ} (h : A ∣ B)` | `DeligneSerre/Lifting.lean`, as `gamma1_le_of_dvd` |

Five proofs of one fact, all identical after the rename. The home is the general shape — both
indices explicit, `{m n : ℕ} (h : m ∣ n) : Gamma1 n ≤ Gamma1 m` — which is what "everyone wants"
and what every spelling instantiates.

`Gamma0_le_of_dvd` is the companion (also absent from mathlib, also re-derived privately in
`Lifting`), so the module is a genuine two-lemma API rather than a single-fact file.

## 2. The shape of the supplement

* one mathlib import (`Mathlib.NumberTheory.ModularForms.CongruenceSubgroups`) and **no port
  dependency** — it is a leaf, 3.2 s to elaborate, 2,229 jobs to build;
* `namespace CongruenceSubgroup`, so the lemma is found by the `open CongruenceSubgroup` that every
  consumer already carries, and reads as the API extension it is;
* **unlisted (tier 3) and registered**: its statements are the port's *generalised* ones, not any
  single pin spelling, so the checker cannot diff it against a pin declaration. It appears in
  [spec/UNWIRED-PUBLIC.md](../spec/UNWIRED-PUBLIC.md) with `0` pin counterparts — the honest
  classification for a port-authored generalisation;
* a good upstream candidate: with `CongruenceSubgroup.Gamma1_le_of_dvd` in mathlib this file and
  every remaining wrapper disappear.

## 3. The wave, scheduled upstream-first

The cascade was the whole planning problem: `X1/Defs.lean` has 27 dependent modules (≈161 s) and
`Gamma0Integral.lean` 47 (≈341 s), while `Lifting` and `IntegralWeightOneForm` have none. So the
home was built first (a leaf, nothing depends on it), then the consumers were edited from the
leaves upward, each built once with `flock … lake build <module>` — **no tree build**:

| module | cascade | tier-1 result |
|---|---|---|
| `CongruenceSubgroupOrder` (home) | 0 | green, 2,229 jobs, 2.1 s |
| `DeligneSerre/Lifting.lean` | 0 | green, 4,037 jobs, 9.5 s |
| `WeightOne/IntegralWeightOneForm.lean` | 0 | green, 4,243 jobs, 5.1 s |
| `WeightOne/RationalityDvd.lean` | 2 / 2,595 | green, 4,129 jobs, 24 s |
| `ModularCurve/X1/Defs.lean` | 27 / 13,231 | green, 4,125 jobs, 3.8 s |
| `WeightOne/Gamma0Integral.lean` | 47 / 26,149 | green, 4,118 jobs |
| `Analytic/NormSqLt.lean` | 1 | green, 3,580 jobs, 7.9 s |

The two big-cone modules were edited *last*, so no earlier edit forced a second elaboration of
their dependents. The dependents' oleans are now stale by hash (their imports changed) but their
*statements* cannot have changed — the wrappers keep the pin's text, and the private deletions are
invisible outside their modules — so they will simply rebuild whenever they are next needed.

## 4. Warnings fixed

`DeligneSerre/Lifting.lean` carried **18** `linter.style.haveILetI` warnings, all of them on
`haveI`/`letI` bindings whose value is a proposition. Lean's own suggestion (`haveI` → `have`,
`letI` → `let`) was **taken at every site and all 18 declarations still compile** — tested on a
scratch copy first, then applied: the module is now at **0 warnings**. No `set_option` suppression
was added.

The other five consumers were already at 0 warnings and remain so.

## 5. Verification

| check | result |
|---|---|
| tier-0 on the home and all six consumers | 0 errors, **0 warnings** |
| tier-1, module by module, upstream-first | all green (table in §3) |
| checker | **10,476 identical / 0 mismatched / 0 missing** (10,812 checked) — unchanged, as required |
| register | 137 modules / 4,136 public / 3,830 with a pin counterpart; the home's 2 rows have 0 pin counterparts |
| `git status` | the new module and the six consumer files |

## 6. What is left of the family

* `Gamma_le_Gamma1` (i.e. `CongruenceSubgroup.Gamma N ≤ Gamma1 N`) is the next tenant of the same
  home: the port has it **public** in `CuspForm.LiNormSq` (pin-derived and checker-listed, so that
  copy must stay) and **`private`** in `WeightOne/Gamma1IntegralBasis.lean:120` and
  `WeightOne/Gamma0Integral.lean:1965`. Moving the two private ones onto a homed version is the
  same treatment; `Gamma0Integral` is already in this wave's set, `Gamma1IntegralBasis` is not.
* `gamma1GL_le_of_dvd` (`DeligneSerre/Lifting.lean`) stays local: it is the `GL`-coercion image of
  the home lemma, not a `CongruenceSubgroup` fact.
* The home is a mathlib gap; upstreaming it would retire this file and all three wrappers.

## 7. Reproduce

```bash
cd lean
flock .lake/flt_build.lock timeout 280 lake build \
  FLTForHuman.NumberTheory.ModularForms.CongruenceSubgroupOrder
for m in DeligneSerre/Lifting ModularForms/WeightOne/IntegralWeightOneForm \
         ModularForms/WeightOne/RationalityDvd ModularCurve/X1/Defs \
         ModularForms/WeightOne/Gamma0Integral ModularForms/Analytic/NormSqLt; do
  flock .lake/flt_build.lock timeout 280 lake build "FLTForHuman.${m//\//.}"
done
timeout 600 python3 spec/check_flt_statements.py | tail -1   # 10476 identical
python3 tools/deps/unwired_register.py --check
```
