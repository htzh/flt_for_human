# WORKORDER-IW1 — the continuous Iwasawa K-factor at the big cell, and the height relation on induced sections

**Status: landed (2026-10-23)** — see §7. Pure addition: **one** new module, no existing module
edited. One dispatch, not a set: the silo is 664 lines and its proofs are local matrix algebra plus
continuity, so there is nothing for a wave plan to protect (§3.7's split is for sets that must not
cascade).

## 0. The node

| node | pin `S_` lines | decls |
|---|---:|---:|
| `AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent` | 664 | 80 (79 helpers + `solution`) |

What it says. Fix a number field `F`, let `α` be the modulus character of `𝔸_F^×` pushed to `ℝ^×`,
and assume `hα : ∀ t, 0 < α t`. Then there is a map `κ : 𝔸_F → GL₂(𝔸_F)` such that: `κ` is
continuous; for every `x` the finite part `glFin (κ x)` lies in the level-⊤ integral subgroup
`finiteIntegralGL2` and every archimedean component `archComponent F w (glArch (κ x))` is a
`IsRowIsometry`; `w⁻¹ · n(x) · (κ x)⁻¹` lies in `adelicBorel` (so `κ` is the Iwasawa compact factor
of the big-cell representative); `κ` is coordinatewise local (each finite component depends only on
the finite component of `x`, the archimedean part only on the archimedean part); and for every
`s : ℂ` and every `IsInducedSection` `φ` for the pair `(etaFst 1 α hα s, etaSnd 1 α hα s)` one has
`φ (w⁻¹ n(x)) = H(w⁻¹ n(x))^(s+1/2) · φ (κ x)`, with `H = adelicHeight`.

**Readiness, verified.** Every premise is ported and homed; nothing is new:

* the node's **only** graph premise, `NumberField.AdeleRing.distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm`,
  is at `FLTForHuman/NumberTheory/AdelicModulus.lean:74` (used in the pin at `:594`, inside
  `adelicHeight_weylUnip` — the height as the product of local heights);
* every definition the statement names has a port home (the import list is §1);
* **nothing to substitute**: `tools/deps/port_advise.py` finds 0 of the 80 statements in the port
  ("every target declaration is new"), and `tools/deps/shapes.py` agrees by *shape* over the whole
  pin corpus and the port (0 in the port, for all 64 theorem/lemma declarations);
* **no shared private prelude inside this set** — it is a single silo, nothing proved twice;
* the pin is already clean: `set_option autoImplicit false` only, no `sorry`, no heartbeat bump.

**Demand — and it is a leaf.** Its only consumer is
`AutomorphicForm.exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family`,
which `tools/deps/frontier.py` prices at **10 new nodes / 4,490 lines**; this node is the
**cheapest of the ten (664 lines)**, so porting it advances the frontier but buys no usable consumer
yet. Say so in the record rather than implying the consumer is now reachable.

**One duplication recorded, not this order's work.** `shapes.py` finds 5 of the 64 statements with
same-shape twins in *sibling pin files* of the same unported family —
`coe_weylInv_mul_unipotent` (6 copies, e.g. `S_AutomorphicForm_apply_weylInv_unipotent*.lean`),
`mul_apply_fst`, `mul_apply_snd`, `archComponent_weylUnip_coe`, `finComponent_weylUnip_coe` (2 each).
This order ports the silo as it stands; when the family is dispatched those five are one shared
home, not five copies.

## 1. Deliverable — one module

`FLTForHuman/AutomorphicForm/Adelic/IwasawaWeylUnipotent.lean`.

* **Namespace** `AutomorphicForm`, engine in the sub-namespace **`AutomorphicForm.IwasawaWeyl`**
  (the pin's `IwasWeyl`). The headline stays in the outer namespace, at its full pin name.
* **79 helpers, public, at the pin's last names.** The pin marks **all 80 declarations public** (no
  `private` anywhere in the `S_` file), so §3.1's rule applies unchanged: a pin-public statement
  keeps its name, and the checker diffs it. Do not privatise and do not rename — that is what makes
  the expected reading `80 ok` and checks 79 statements that the FTF1 shape could not check.
  The compressed tokens (`kf`, `kfInv`, `ka`, `kaInv`, `cc`, `cj`, `ofR`, `emb`, `bor`, `tor`) are
  **carried, not rectified**, for the same reason.
* **The pin's six sections kept** — `Finite` (29–147), `Arch` (149–292), `Assembly` (294–393),
  `Props` (395–464), `Height` (466–599), `Section` (601–634). They are the file's skeleton, not a
  work plan: port straight through, in the pin's order.
* **The pin's `local notation` kept**: `"Fv"` (pin :33), `"Ov"` (:34), `"L"` (:153). The helpers'
  statements are written with them and the checker is text-only — spelling `v.adicCompletion F` out
  would read as a `mismatch` on every `Finite`-section helper.
* **Headline verbatim** (from `Theorems/Thm_…:18–36` — the `let` binder included, and the checker
  hashes the signature up to the first top-level `:=`, which is the `:= by` on :36):

```lean
theorem AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent
    (F : Type) [Field F] [NumberField F] :
    let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ :=
      ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp
        (distribHaarChar (AdeleRing (𝓞 F) F))).toHomUnits
    ∀ (hα : ∀ t, 0 < ((α t : ℝˣ) : ℝ)),
    ∃ κ : AdeleRing (𝓞 F) F → AdelicGL2 (𝓞 F) F,
      Continuous κ ∧
      (∀ x, glFin (𝓞 F) F (κ x) ∈ finiteIntegralGL2 (𝓞 F) F ∧
        ∀ w : InfinitePlace F, IsRowIsometry (archComponent F w (glArch (𝓞 F) F (κ x)))) ∧
      (∀ x, (adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x * (κ x)⁻¹ ∈ adelicBorel (𝓞 F) F) ∧
      (∀ x y : AdeleRing (𝓞 F) F, ∀ v : HeightOneSpectrum (𝓞 F), x.2 v = y.2 v →
        finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ x)) = finComponent (𝓞 F) F v (glFin (𝓞 F) F (κ y))) ∧
      (∀ x y : AdeleRing (𝓞 F) F, x.1 = y.1 → glArch (𝓞 F) F (κ x) = glArch (𝓞 F) F (κ y)) ∧
      (∀ (s : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ),
        IsInducedSection (𝓞 F) F (etaFst 1 α hα s) (etaSnd 1 α hα s) φ →
        ∀ x : AdeleRing (𝓞 F) F,
          φ ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) =
            ((adelicHeight F ((adelicWeyl (𝓞 F) F)⁻¹ * unipotentGL2 x) : ℝ) : ℂ) ^ (s + 1 / 2) * φ (κ x))
```

  Its proof is the body of the pin's `solution` (pin :641–664): one `intro α hα` and a single
  `exact ⟨kappa F, continuous_kappa F, …⟩`. No `solution` twin is kept; the port then has 79 helpers
  + 1 headline, all public.
* **Imports** — the port homes, then narrow `Mathlib.*`; **never `import Mathlib`**:

```lean
import FLTForHuman.AutomorphicForm.Adelic.BorelSubgroup        -- adelicBorel
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm         -- unipotentGL2
import FLTForHuman.AutomorphicForm.Adelic.EtaFamily            -- etaFst, etaSnd
import FLTForHuman.AutomorphicForm.Adelic.InducedSection       -- IsInducedSection
import FLTForHuman.AutomorphicForm.Adelic.WeylIntertwining     -- adelicWeyl
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.RowIsometry  -- IsRowIsometry
import FLTForHuman.AutomorphicForm.Adelic.WindowedSiegel.Set   -- localHeight
import FLTForHuman.NumberTheory.AdelicHeight                   -- adelicHeight, finHeight, archHeight, finLocalHeight, rowNormSq, rowMaxNorm
import FLTForHuman.NumberTheory.AdelicLevel.Level              -- finiteIntegralGL2
import FLTForHuman.NumberTheory.AdelicLevel.Projections        -- glFin, glArch, finComponent, archComponent
import FLTForHuman.NumberTheory.AdelicModulus                  -- distribHaarChar_eq_prod_norm_pow_mult_mul_finprod_norm
```

  plus whatever the proofs themselves name (start from `Meas. Haar. DistribChar` for
  `distribHaarChar` and the `Valued`/`Valued.integer` API for `Valued.isClosed_valuationSubring`).
  Drop the rest of the pin's imports: `P2M.Util`, the `P2MW.S_<stem>` wrapper namespace, the
  `Theorems/` wrapper's `p2m_exact_reverting` glue.
* **The pin's two `attribute` lines.** `attribute [-instance] instCountableOfNumberField_definitions`
  **must go** — the port has no such definition. `attribute [-ext] …adicCompletion.ext` /
  `…Completion.ext` keep **only if** the build actually needs them (they stop `ext`/`simp` from
  splitting those structures); decide by compiling, and report which survived.
* **Header docstring** in the port's style: the subject, the pin source with pinned URLs (`aa2d8b3`),

  * `Theorems/Thm_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent.lean` (36 lines) — the
    statement, verbatim;
  * `P2M/Sol/S_AutomorphicForm_exists_continuous_iwasawa_weyl_unipotent.lean` (664 lines, 80
    declarations) — the proof, its `solution` inlined into the headline;

  the two `spec-pin:` lines (this module carries its own wire, so the checker diffs all 80), a note
  that the 79 helpers are the pin's public ones at the pin's names, and
  `set_option autoImplicit false`.

## 2. Names and namespaces — the one policy question, settled

Keep the pin's last names, keep them public, put them in `AutomorphicForm.IwasawaWeyl`. The port has
`kappa` (2 modules), `emb`, `cc`, `adele_ext` elsewhere, all in other namespaces: nothing collides, and
nothing may be moved out of the sub-namespace to "tidy" it (a top-level `kf`/`tor`/`bor` would be a
port-wide collision waiting to happen). No `spec/decl_markers.tsv` row is expected: names match, so
the checker matches every declaration by last name.

## 3. Build discipline — read before the first compile

From `lean/`, always through the lock:

```bash
flock .lake/flt_build.lock timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000 FLTForHuman/AutomorphicForm/Adelic/IwasawaWeylUnipotent.lean
```

A finished file: `flock .lake/flt_build.lock timeout 120 lake build FLTForHuman.AutomorphicForm.Adelic.IwasawaWeylUnipotent`.

* **No tree `lake build`, ever.** Every tool call finishes inside two minutes; a loop is not a way
  around that. Anything that can plausibly run a minute is a **background job** with its own
  `timeout` and a log read afterwards.
* **The 200,000 cap is a diagnostic.** No `set_option maxHeartbeats`, no
  `synthInstance.maxHeartbeats`; the pin's bumps (there are none here) are not inherited.
* **One compile per edit, and probes, not bisection** (`porting-playbook.md` §3.5). If the first
  compile fails, run the floor first: a `lean/tmp/` copy with every proof `sorry` separates
  statements from proofs in one run. Levers, in order: an unused section variable becomes a
  `haveI`/term-`letI` in the proof that needs it, `private abbrev` aliases, then stop and report. A
  probe over 60 s is the probe's fault.
* **Where friction is expected**: the pin is `v4.33.1`/`db584cd6`, the port `v4.34.0` — the `Valued`/
  `adicCompletion`/`IsClopen` API at the finite places, `Matrix (Fin 2) (Fin 2) 𝕜` entrywise
  continuity, and `Complex.cpow`/`ofReal` in `cpow_div_ofReal`. No `Finset`/`tsum` work, so no
  heartbeat risk is expected; a heartbeat raise looking necessary is §5.

## 4. Gates

```bash
cd lean
flock .lake/flt_build.lock timeout 120 python3 spec/check_port.py --force \
  FLTForHuman/AutomorphicForm/Adelic/IwasawaWeylUnipotent.lean
# expected: 80 ok, 0 mismatch, 0 missing, 0 own, 0 kw
python3 spec/check_port.py --changed --strict-markers
```

plus: `lake build` green with **0 warnings**; `#print axioms` on the headline
`[propext, Classical.choice, Quot.sound]`; no `sorry`/`admit`/`native_decide`/`import Mathlib`;
only `set_option autoImplicit false`; `git status` adds exactly one file.

## 5. Stop and report — do not improvise — if

an existing module must change (declaration, host, import path); the proof needs a statement from
another pin node, i.e. something outside §0's one premise (a new citation is a real finding); a
heartbeat raise looks necessary (give the statement-only probe at 200k and the reading); the headline
reads `MISMATCH`; a `spec/decl_markers.tsv` row looks needed; or a name in
`AutomorphicForm.IwasawaWeyl` collides inside the port.

## 6. Report shape

(i) lines, declaration count, public/private split, namespace; (ii) the checker readings and
`--changed --strict-markers`; (iii) the build's warnings and the axioms; (iv) **every proof deviation
from the pin, with its site** — the statements must not deviate; (v) the names carried and the
imports dropped (including which of the two `attribute` lines survived); (vi) open issues only, for
`CARRY-FORWARD.md`; (vii) `git status`; plus the floor probe (only if it was needed) and the pin ranges consumed:
`S_` 1–20 (imports, the two `[-ext]` pin attributes, `namespace P2MW.S_…`, `set_option`) replaced by
the port's header and imports; 21–664 transcribed verbatim except the `P2MW` wrapper removal, the
`IwasWeyl` → `AutomorphicForm.IwasawaWeyl` rename and the dropped `attribute [-instance]`;
`Theorems/` 18–36 (statement, verbatim) with :36's `p2m_exact_reverting` replaced by the `solution`
body at `S_` 641–664.

Records: [porting-playbook.md](../../porting-playbook.md) §3.1–§3.5, §4–§6;
[TOPIC-iwasawa-analytic-core.md](TOPIC-iwasawa-analytic-core.md) §6 (which records that these
adèlic `iwasawa` nodes are *not* that note's subject — the word is shared, the theory is not);
[WORKORDER-FTF1](WORKORDER-FTF1-factorizable-testfn-archsmooth.md) for the opposite visibility
decision and the §9 lesson behind it.

## 7. Landed (2026-10-23)

One new module, no existing module edited.

`FLTForHuman/AutomorphicForm/Adelic/IwasawaWeylUnipotent.lean` — **737 lines, 80 declarations, all
80 public, 0 private**. Engine in `AutomorphicForm.IwasawaWeyl` (the pin's `IwasWeyl`), headline at
`AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent` in the outer namespace, its proof the
pin's `solution` body (`S_` 660–664) with no `solution` twin. The pin's six sections and its three
`local notation` lines (`Fv`, `Ov`, `L`) are kept verbatim — and they had to be: the `Finite`-section
statements are written with the notations, and the text-only checker diffs them.

| gate | reading |
|---|---|
| `check_port --force` | **80 ok**, 0 mismatch, 0 missing, 0 own, 0 kw (79 helpers + headline; the wire's `solution` correctly has no counterpart) |
| `--changed --strict-markers` | 4255 ok, 0 mismatch, 0 missing, 12 own (pre-existing), 0 kw — **168 modules**, 0 stale markers, exit 0 (was 4175 / 167) |
| `lake build` | green, 3491 jobs, **5.6 s, 0 warnings** |
| edit loop at 200k | exit 0, empty log; no cap raise, no `set_option`, no stub file |
| `#print axioms` (headline) | `[propext, Classical.choice, Quot.sound]` |
| hygiene | `set_option autoImplicit false` (:58) only; no `sorry`/`admit`/`native_decide`/`import Mathlib` |

**No statement deviates.** 11 proof deviations, all proof-side. The one that is a real adaptation:
in `kMat_mul_kMatInv`, `kMatInv_mul_kMat` (four branches) and `glArch_kappa_eq`, the pin's
`simp only [kMat, …, Matrix.of_apply, finEntry_apply, …]` no longer reduces the `Matrix.of` entries
on mathlib `v4.34.0` — `rw`'s keyed matching runs at `implicit` transparency and cannot see through
`x.1`/`x.2` on the `AdeleRing` product — so each site states the sum it needs with
`rw [show ∑ … = ∑ ka/kf … from rfl]` (a function `show` in `glArch_kappa_eq`), the same unfolding at
default transparency, leaving the pin's `rw [h, …]`/`split_ifs <;> rfl` tail untouched. That failure
mode now has its own row in [TOPIC-mathlib-drift.md](../TOPIC-mathlib-drift.md) (when `simp only`
stops unfolding a projection, do not hunt for a lemma: restate the goal at default transparency with
`show … from rfl`), which is where a drift belongs; the `if_pos`/`if_neg` and `omit [NumberField F]`
deviations below were rows there already. The other ten: unused `simp` arguments and a no-op
`<;> skip` dropped (`kf`, `ka`, `rowIso_ka`, `continuous_kMat(Inv)`, `bor_*`), the deprecated
`if_pos`/`if_neg` replaced by the hypothesis in the simp set (`norm_tor_fin`), `bor_fst_arch`'s
trailing `<;> ring` split into two bullets, and **19 `omit [NumberField F] in` prefixes** for
`linter.unusedSectionVars` (the pin's `variable … [NumberField F]` is in scope but unused by those
statements; a prefix is not statement text, so all 19 still diff `ok`).

**Names, imports, attributes.** All 79 helpers carry the pin's last names unrectified, compressed
tokens included (`kf`, `ka`, `cc`, `cj`, `ofR`, `emb`, `bor`, `tor`, `kMat`, `kappa`) — they are
pin-*public* statements, so §3.1 keeps their names, and that is what makes 80 statements diff instead
of one. The pin's `import Mathlib`, its seven `Definitions.*`/`Theorems.*` imports and `P2M.Util` are
replaced by eleven port homes and three narrow `Mathlib.*` modules
(`Analysis.SpecialFunctions.Pow.Complex`, `MeasureTheory.Measure.Haar.DistribChar`,
`Topology.Algebra.Valued.ValuationTopology`). The `P2MW.S_<stem>` namespace and the wrapper's
`p2m_exact_reverting` are dropped. **Neither `[-ext]` attribute survived** (both unnecessary on
`v4.34.0`) and the `[-instance]` line is gone as ordered; no `spec/decl_markers.tsv` row was needed.

**Pin ranges consumed.** `S_` 1–20 (imports, both `[-ext]` attributes, `namespace P2MW.S_…`, the
`[-instance]` attribute, `set_option`, the three `open`s) replaced by the module's header, imports and
namespace; 21–664 transcribed, with `namespace IwasWeyl` → `namespace IwasawaWeyl` and `solution`
(641–664) inlined instead of kept. `Theorems/` 18–36 verbatim as the headline's statement, its
`:= by p2m_exact_reverting … solution` replaced by the `solution` body.

**Open issues — none for `CARRY-FORWARD.md`.** No deferred declaration, no marker row, no API gap.
Two things for the family's future order, not this one: five statements here are one shared home when
the sibling files land (`coe_weylInv_mul_unipotent` ×6, `mul_apply_fst`/`mul_apply_snd`/
`archComponent_weylUnip_coe`/`finComponent_weylUnip_coe` ×2 each), and the consumer status is
unchanged — this node is a leaf, and
`exists_pos_eventually_le_re_sub_one_half_mul_weylIntertwiningIntegral_one_of_nonneg_of_isArchKFinite_family`
still needs nine further nodes (≈3,826 lines).

`git status`: one new module (this order file aside). Nothing else modified; no `git add`/commit.
