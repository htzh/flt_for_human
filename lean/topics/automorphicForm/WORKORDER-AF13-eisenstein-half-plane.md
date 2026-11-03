# WORKORDER-AF13 — the Bruhat Eisenstein series in the half-plane

**Issued 2026-11-02, one dispatch.** Scope: [SET-AF13.md](SET-AF13.md) — §1 the four rows, §2 the
price and the substitutions, §3 the definition gate, §4 the home, §6 the risk register, and
**Appendix B, the per-declaration worklist**. This order states the work, the manager's landed layer,
the traps and the gates.

**Audience.** A fresh coding session. Wire: the target module carries its own `spec-pin:` header and
`spec/check_port.py` owns its statements. **No per-declaration markers.** Pin clone
`/home/haitao/proj/fermats-last-theorem`, pinned `aa2d8b3`. Port mathlib `v4.34.0`.

**The size.** 4 rows, 1,637 silo, **947 lines in 56 declarations to write** (959 net by `port_plan`) —
a **composition** set: 562 of the 1,509 declaration lines are already in the port.

## 0. The manager's layer, landed (do not redo it)

1. **The module exists and is wired.** `AutomorphicForm/Adelic/BruhatEisenstein.lean` (skeleton:
   header, imports, opens, empty `namespace AutomorphicForm`) carries **eight `spec-pin:` lines** —
   the four `Theorems/` wrappers and the four `S_` files — and `check_port --force` reads **0 ok / 0
   mismatch / 0 missing** (no declarations yet).
2. **Its imports are complete; add none.** `WeylIntertwining`, `InducedSectionFlat`, `EtaFamily`,
   `ConstantTerm`, `LsXi`, `ArchKFinite`, `SmoothAutomorphicFn`, `WindowedSiegel/{CentreCutSet,
   RowIsometry}`, `WeylIntegrable` (the engine umbrella), `NumberTheory/AdelicHeight`,
   `NumberTheory/AdelicLevel/Projections`, and the three mathlib modules the pin's first `S_` file
   needs instead of its `import Mathlib` (`MeasureTheory.Integral.Pi`,
   `Analysis.SpecialFunctions.Log.Summable`, `Topology.Algebra.InfiniteSum.Order`, and
   `Analysis.Complex.LocallyUniformLimit` — added at the worker's row-1 blocker, which supplies
   `Complex.differentiableOn_tsum_of_summable_norm`). If a proof needs anything else, that is a
   blocker.
3. **Its opens are the wrappers'**, and the probe below settled two of them: `open
   NumberField.AdelicHeight` (the port nests `adelicHeight` there; the pin has it directly in
   `NumberField`) and `open scoped NNReal` (the `ℝ≥0` in the `distribHaarChar`-to-`ℝˣ` monoid hom).
   Without them two statements do not even parse.
4. **The statements are verified, not assumed.** `lean/tmp/probe-af13-statements.lean` states all
   **four** headlines verbatim from their wrappers as `example … := by sorry` against the skeleton,
   and elaborates with exactly four `declaration uses sorry` warnings. Re-run it first.
5. **No `Def_` node, no promotion, no migration.** `gate_scan` over the eight `Def_` modules of the
   closure reports **0 missing** in every one (max use 4/27 `AdelicHeight`, 4/9 `ArchKFinite`); two of
   the eight port homes are legacy (`NumberField/AdelicHaar/Adele.lean`, `…/Adelic/ArchKFinite.lean`)
   and are imported, never edited, so no migration is owed. And
   `norm_finComponent_le_one_of_mem` is **public** at `NumberField/AdelicHeight.lean:442`: import that
   copy (the advise file pointed at a `private` twin in `BigCellExpansion.Height`), do not re-state it.
6. **No `set_option`.** The pin's `letI`/`haveI` walls in proofs become `have`/`let` (Lean 4 registers
   local instances for those; a suppression is justified only for a term-mode `letI` inside a
   definition body).

## 1. What you write

All of it in `AutomorphicForm/Adelic/BruhatEisenstein.lean`, appended below the skeleton. The four
headlines are **public at `AutomorphicForm` level** (the pin's `solution` body is the headline's
body); the helpers' visibility **follows the pin's**: the pin-public ones sit in four subject namespaces
(the wire carries them), and the ones the pin states `private` stay `private` — its preludes contain
several (`exists_bound_on_unitBox_family_j1`, `hpow`, `finLocalHeight_one'`), and promoting one is a
checker `MISMATCH` on the section binders, not a rewrite:

| namespace | the pin's label it replaces | holds |
|---|---|---|
| `BruhatEisensteinDiff` | `SolE_j1` | the derivative/unfolding calculus of the differentiability row |
| `FlatEisensteinHeight` | `Ws37EisMaj` | the local/ultrametric height calculus of the bound |
| `FlatSectionFamily` | `FlatFamilyThroughSection` (kept in substance) | the dictionary row's `InK`/`finLocalHeight` lemmas |
| `BruhatConstantTerm` | `BruhatCTSol` | the unfolding of the constant term |

| row (`AutomorphicForm.` dropped) | pin `S_` file | work | shape |
|---|---|---:|---|
| `bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family` | `S_…bruhatEisenstein_differentiableOn_re_gt_half_of_entire_family.lean` | **160** / 5 | the pin's `Generic`/`Adelic` sections: the summand's local-uniform convergence, then the `tsum` differentiability |
| `exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet` | `S_…exists_flatEisenstein_mul_le_mul_archHeight_rpow_of_mem_centreCutSiegelSet.lean` | **380** / 25 | the `Local` (normed field) and `Ultra` (ultrametric) height calculus, then the bound on the centre-cut Siegel set |
| `exists_flat_isInducedSection_family_eq_of_isInducedSection` | `S_…exists_flat_isInducedSection_family_eq_of_isInducedSection.lean` | **196** / 18 | the `Local`/`Ultra` section calculus, then the family's construction and its five properties |
| `constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral` | `S_…constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral.lean` | **211** / 8 | the `Unfold` section: unfold the constant term over the Bruhat orbit, then the volume factor and the Weyl integral |

**Do them in this order**, because the constant-term row's statement is the one that cannot be
trusted to the checker (§2.1): differentiability, dictionary, height, constant term.

## 2. Traps

1. **The constant-term row's statement carries a `letI`.** Its conclusion is
   `letI := adeleBorel (𝓞 F) F; let E := …; constantTerm … = φ g + (vol box)⁻¹ * weylIntertwiningIntegral …`.
   `check_port`'s parser stops at the first top-level `:=`, which is the instance binding's value, so
   the checker's verdict on this row is **degenerate** (FR-0056): a green `ok` does not mean the
   statement is faithful. Copy the wrapper's text verbatim and read it by eye, `letI` included.
2. **The `hpow` substitution is a shift, not a rename.** The pin's `hpow t g = (adelicHeight g) ^ t`;
   the port's `FlatInducedSection.flatOne s g = (adelicHeight g) ^ (s + 1/2)`, so `hpow t = flatOne
   (t - 1/2)`. Use the `flatOne` twins of `hpow_mul_inK`/`hpow_of_inK` if they exist (check
   `InducedSectionFlat`), or write the two-line `hpow`; state which in the report.
3. **`norm_finComponent_le_one_of_mem` has a public copy** at `NumberField/AdelicHeight.lean:442` —
   import it. (The advise file matched its `private` twin in `BigCellExpansion.Height`: read the
   `port` module, not only the `port_name`.) `FlatInducedSection.finLocalHeight_one` and the other
   byte-identical substitutions are public and are imported, not restated.
   **And the pin-private helpers stay `private`** — if one of them is made public, its statement comes
   out mismatched, because the pin spells it with the file's `section` variables.
4. **The 380-line height row is the set's cost** (25 declarations). Read the pin's `Local` and
   `Ultra` sections in order; do not unify them before the last declaration, and note that the bound
   is `archHeight (glArch s) ^ (σ + 1/2)` with `re s = σ > 1/2` — the exponent is `σ + 1/2`, not `σ`.
5. **Binder shadowing for the checker** (FR-0123): the four headlines spell the wrappers' binders
   inline, including the `let α : (AdeleRing (𝓞 F) F)ˣ →* ℝˣ := …` preamble of two of them and the
   `open scoped NNReal` that makes `ℝ≥0` parse. The probe is the check, not the ok count.
6. **No `set_option maxHeartbeats`, no `native_decide`, no `sorry`/`admit`/`axiom`**; zero warnings; no
   new module, no new import, no hub edit, no `private` marker.

## 3. Gates

1. `timeout 120 lake env lean -DautoImplicit=false -DmaxHeartbeats=200000
   FLTForHuman/AutomorphicForm/Adelic/BruhatEisenstein.lean` silent, then its own
   `flock .lake/flt_build.lock timeout 280 lake build
   FLTForHuman.AutomorphicForm.Adelic.BruhatEisenstein`; **no tree build**, no dependents.
2. `python3 spec/check_port.py --force` on the module: `0 mismatch / 0 missing`, and the ok count
   measured (target = 4 headlines + the engine declarations that resolve by hash; the port's 0 at the
   skeleton). Then apply the recipe's surface gate: with `private` dropped on everything, read the
   three numbers again — a `MISSING` is a port-side helper (keep it private), a `MISMATCH` a spelling
   to fix.
3. `#print axioms` on all four headlines → `[propext, Classical.choice, Quot.sound]`.
4. Zero warnings on the module.
5. `dedup.py --within` and `move_dead.py --source <path> --target /dev/null --dry-run`: report every
   cluster and disposition. A pin-own prelude duplication (the two `hpow`/`flatOne` spellings, the
   `Local`/`Ultra` twins of one height lemma) is kept with the reason recorded.
6. `spec/AutomorphicFormSetAF13Consumer.lean` — **one zone**, a real composition, no `#check`, no
   `sorry`: take the section family produced by the dictionary row
   (`exists_flat_isInducedSection_family_eq_of_isInducedSection`) from one arch-`K`-finite,
   `K_f`-smooth, continuous induced section, and read the constant-term identity
   (`constantTerm_bruhatEisenstein_eq_section_add_weylIntertwiningIntegral`) at that family's `ψ s`,
   concluding that the constant term of the flat Eisenstein series of `ψ s` is
   `ψ s g + (vol box)⁻¹ * weylIntertwiningIntegral (ψ s) g`; if the instantiation needs a hypothesis
   neither row supplies, state it on the consumer side and report it — do not weaken a headline.
   It imports the new module only; `lake env lean` it to zero errors.
7. `lean/tmp/probe-af13-statements.lean` still elaborates (four `sorry` warnings, nothing else).

## 4. Report

Per row: lines written, declarations written and their namespace, every worklist entry dropped and
why (with the pin line), the pin line of every deviation, build time and silence, the checker counts
(before 0, after measured), the four `#print axioms` blocks, `dedup`'s clusters and `move_dead`'s
dispositions, the consumer zone's error count, and one paragraph on the height row: whether the
`Local`/`Ultra` calculus transcribed cleanly or needed restructuring, with the reason.

**A blocker goes back immediately** — "blocked on `<decl>` at pin `:NNN`; likely needs `<X>`", with
the pin line and the error. Do not grind out a diagnosis, never work around a hub defect locally, and
do not add an import, a module, or a `set_option`.
