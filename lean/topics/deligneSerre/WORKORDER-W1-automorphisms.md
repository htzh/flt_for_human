# WORKORDER-W1 — the exceptional automorphisms of the supersingular curves

**Status: ready to dispatch (2026-10-08).** First set of the `WeierstrassCurve` ready shelf,
scoped in [TOPIC-weierstrass-ready-shelf.md](TOPIC-weierstrass-ready-shelf.md) (stories A and
the dedup of §4). **Three new modules, in this order**; the orders share one prelude, written
once in order 1. No existing module is edited, no promotion is proposed, and the definition
layer is already in place (§0).

| order | module | headline | `S_` file |
|---|---|---|---|
| 1 | `FLTForHuman/WeierstrassCurve/Automorphism/Basic.lean` | the shared point-transport prelude (11 declarations, §2) | the two `S_` files of orders 2–3 |
| 2 | `FLTForHuman/WeierstrassCurve/Automorphism/CharTwo.lean` | `WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two` | `S_…_of_char_two.lean` (988) |
| 3 | `FLTForHuman/WeierstrassCurve/Automorphism/CharThree.lean` | `WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three` | `S_…_of_char_three.lean` (424) |

Order 1 must check clean before order 2 starts; verify order 2 before order 3. The module
paths are the reviewer's proposal — if the mathematics admits a leaf-side home, re-home and
record it (playbook host rule), but do not split one theory across modules.

## 0. What is already in the port

Every premise of both headlines is ported; **no definition-layer work and no hub edit is
needed**:

* `WeierstrassCurve.Affine.Point.vcInvFun` and the vocabulary it is stated in
  (`vcX`/`vcY`/`vcXInv`/`vcYInv`, `vcFun`, `variableChangeEquiv`) — public in
  `FLTForHuman/WeierstrassCurve/Velu/Equivariance.lean` (namespace
  `WeierstrassCurve.Affine`/`…Affine.Point`). **Import, never redeclare.**
* `WeierstrassCurve.Affine.Point.vcInvFun_add` — public in
  `FLTForHuman/WeierstrassCurve/Velu/VariableChangePoint.lean`.
* `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed` — public in
  `FLTForHuman/Elliptic/TorsionZMod.lean` (order 2's only other premise).
* `Def_WeierstrassCurve_VariableChangePointEquiv` is in `SOURCES`; the pin's
  `WeierstrassCurve.VariableChange` itself is **mathlib** (`Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange`),
  with `mul_def`/`inv_def` giving the component formulas the pin states as `rfl` lemmas.

Do **not** transcribe the pin's `attribute [-instance] …` / `attribute [-simp] …` scaffolding
lines (including every `sizeOf_spec` and `EllSequence`/`compl₂EDS` name): they are build
scaffolding, not mathematics, and their names are not in the port's import cone.
`set_option maxHeartbeats 6400000` in the pin is **not** transcribed either — this project's
global cap is 4,000,000 and no work order raises it.

**Do** transcribe the pin's `linter.*` suppressions, at the pin's own list for each file:
`linter.unusedSectionVars false`, `linter.unusedVariables false` and (char 2 only, pin line 13)
`linter.unusedSimpArgs false`. Eighty-six landed port modules carry the pin's
`linter.unusedSectionVars false`, and the project's review gate is a warning-free tier-1
elaboration; these `set_option`s are part of the source's declaration environment, not build
scaffolding. *(Corrected 2026-10-08 during the W1 review: an earlier draft of this order said
not to transcribe them, which left 60+ linter warnings in the three new modules.)*

## 1. Source of truth

Pin `anthropics/fermats-last-theorem@aa2d8b3` at `~/proj/fermats-last-theorem` (read-only;
never modify). **Statement = the `Theorems/Thm_<stem>.lean` wrapper**, binders verbatim;
proof = the matching `P2M/Sol/S_<stem>.lean`. Adapt proofs, never statements.

* `Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean`
  and `P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean`
  (988 lines; prelude §Action at 320–360, `main` at 939, `solution` at 970).
* `Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean`
  and `P2M/Sol/S_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean`
  (424 lines; prelude 18–84, `solution` at 375).

Public mirrors, pinned:
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two.lean>,
<https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/Theorems/Thm_WeierstrassCurve_exists_addMonoidHom_i_tau_vcInvFun_of_char_three.lean>.

## 2. Order 1 — the shared prelude, verbatim

Both `S_` files declare this block byte-identically (char 2's `act = vcHom` specialised to
`E₀`; that specialisation is order 2's business, not this module's). Transcribe it **once**,
public, at the pin's names, in `FLTForHuman/WeierstrassCurve/Automorphism/Basic.lean`, inside
`namespace WeierstrassCurve.Automorphism` with
`open WeierstrassCurve WeierstrassCurve.Affine` and the section variables
`variable {K : Type*} [Field K] [DecidableEq K]`:

```lean
def xy {W : WeierstrassCurve K} : W.toAffine.Point → Option (K × K)
  | 0 => none
  | .some x y _ => some (x, y)

theorem xy_injective {W : WeierstrassCurve K} : Function.Injective (xy (W := W))

theorem xy_vcInvFun (γ : VariableChange K) {W : WeierstrassCurve K} (P : W.toAffine.Point) :
    xy (Point.vcInvFun γ W.toAffine P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2))

def castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) : W₁.toAffine.Point ≃+ W₂.toAffine.Point

theorem heq_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    HEq P (castPt e P)

theorem xy_castPt {W₁ W₂ : WeierstrassCurve K} (e : W₁ = W₂) (P : W₁.toAffine.Point) :
    xy (castPt e P) = xy P

noncomputable def vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W) :
    W.toAffine.Point →+ W.toAffine.Point

theorem vcHom_apply (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : vcHom γ W hW P = castPt hW (Point.vcInvFun γ W.toAffine P)

theorem heq_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) : HEq (Point.vcInvFun γ W.toAffine P) (vcHom γ W hW P)

theorem xy_vcHom (γ : VariableChange K) (W : WeierstrassCurve K) (hW : γ • W = W)
    (P : W.toAffine.Point) :
    xy (vcHom γ W hW P) = (xy P).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2))

theorem heq_of_xy_eq {W : WeierstrassCurve K} (γ : VariableChange K) (hW : γ • W = W)
    (T : W.toAffine.Point) (Q : W.toAffine.Point)
    (h : (xy T).map (fun q => (vcXInv γ q.1, vcYInv γ q.1 q.2)) = xy Q) :
    HEq (Point.vcInvFun γ W.toAffine T) Q
```

(The bodies are in the pin, `S_…_of_char_three.lean` lines 18–84; the statements above are
abridged only by eliding proof bodies. **Copy the pin's statement text verbatim**, in
particular the section-variable shape: `def xy {W : WeierstrassCurve K} : …` — do **not**
inline `(K : Type*)`, which is the checker's `def`-flavoured trap that has fired four times.)

## 3. Orders 2 and 3 — the two headlines

Each headline is the only **public** declaration of its module (private helpers are invisible
to the checker, so keep the pin's internal machinery `private` at the pin's leaf names). Put
each in `namespace WeierstrassCurve` — the FQN is fixed by the wrapper — with
`open WeierstrassCurve WeierstrassCurve.Affine`.

The statements, verbatim from the wrappers (do not weaken, do not reorder conjuncts):

**Order 2** (988 lines of pin proof; the witnesses `σ`, `ι` — the pin's `σ`/`τ` — and every
field/curve lemma stay `private`):

```lean
theorem WeierstrassCurve.exists_addMonoidHom_vcInvFun_pow_heq_and_forall_exists_ne_smul_of_char_two
    {L : Type*} [Field L] [DecidableEq L] [IsAlgClosed L] [CharP L 2]
    (w : Lˣ) (hw : (w : L) ^ 3 = 1) (hw1 : (w : L) ≠ 1) (M : ℕ) (hM : (M : L) ≠ 0) :
    ∃ σ ι : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point →+
        (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨w, 0, 0, 0⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (σ^[k] P)) ∧
      (∀ (k : ℕ) (P : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point),
        HEq (Point.vcInvFun ((⟨1, 1, 1, (w : L)⟩ : VariableChange L) ^ k)
          (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine P) (ι^[k] P)) ∧
      (∀ P, σ (σ P) + σ P + P = 0) ∧ (∀ P, ι (ι P) = -P) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, σ a ≠ k • a) ∧
      (∀ p : ℕ, p.Prime → p ∣ M →
        ∃ a : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve L).toAffine.Point,
          addOrderOf a = p ∧ ∀ k : ℕ, ι a ≠ k • a)
```

**Order 3** (424 lines of pin proof; `E0`, `SixForm`, `αH`/`βH`, the stabiliser computation and
the field lemmas stay `private`):

```lean
theorem WeierstrassCurve.exists_addMonoidHom_i_tau_vcInvFun_of_char_three
    {K : Type*} [Field K] [DecidableEq K] [CharP K 3] (i : Kˣ) (hi : (i : K) ^ 2 = -1) :
    ∃ α β : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
        (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
      (∀ T, HEq (Point.vcInvFun (⟨i, 0, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (α T)) ∧
      (∀ T, HEq (Point.vcInvFun (⟨1, 1, 0, 0⟩ : VariableChange K)
          (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (β T)) ∧
      (∀ T, α (α T) = -T) ∧ (∀ T, β (β T) + β T + T = 0) ∧ (∀ T, α (β T) = β (β (α T))) ∧
      (∀ γ : VariableChange K,
          γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ →
        ∃ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) ∧
          ((∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T)) ∨
            (∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T)
              (-(m T))))) ∧
      (∀ m : (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point →+
            (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine.Point,
          (m = AddMonoidHom.id _ ∨ m = α ∨ m = β ∨ m = β.comp β ∨ m = α.comp β ∨
              m = α.comp (β.comp β)) →
        ∃ γ : VariableChange K, γ • (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K) = ⟨0, 0, 0, -1, 0⟩ ∧
          ∀ T, HEq (Point.vcInvFun γ (⟨0, 0, 0, -1, 0⟩ : WeierstrassCurve K).toAffine T) (m T))
```

## 4. Route, and its recorded negatives

* The pin's `VariableChange` component lemmas (`mul_u`/`mul_r`/`mul_s`/`mul_t`) are `rfl` in
  FLT and are **not** ported: mathlib supplies `VariableChange.mul_def`. Rewrite with
  `simp only [VariableChange.mul_def]` (or `ext`) instead of declaring them.
* The pin's `Point.vcInvFun_add` is the port's `WeierstrassCurve.Affine.Point.vcInvFun_add`
  (`Velu/VariableChangePoint.lean`); its conclusion is stated with explicit `C W` — check the
  argument order before use.
* The pin's char-2 proof uses `WeierstrassCurve.nonempty_torsionBy_addEquiv_zmod_prod_of_isAlgClosed`
  (`Elliptic/TorsionZMod.lean`) for the `p`-torsion step; it is public, import it.
* Every `E₀`/`E0` definition stays `private` — the headline statements use the literal
  coefficient tuple `⟨0, 0, 1, 0, 0⟩` / `⟨0, 0, 0, -1, 0⟩`, so no curve def needs to be public.
* `open scoped` instances: keep `scoped` exactly where mathlib/the pin has it; dropping it
  turns a declaration visible and creates spurious checker work.

## 5. Build discipline

`lake env lean <file>` is the edit loop; `lake build <module>` per module; **no whole-tree
build**. Bound everything:
`timeout 300 lake env lean -DmaxHeartbeats=4000000 -DautoImplicit=false <file>`,
`flock .lake/flt_build.lock timeout 300 lake build <module>`. Never raise
`maxHeartbeats`/`maxRecDepth`; on a timeout quarantine and bisect, and tell a blow-up from
contention by CPU time. Serial builds only. Do not commit. The new modules are leaves —
nothing imports them yet, so no cascade is expected; if a build exceeds its bound, stop and
report rather than raising it.

## 6. The hub prohibition

**Do not edit any existing Lean module.** If a needed helper is `private` in a hub, re-derive
it locally as `private` in your module and report it. If a promotion seems genuinely required,
**stop and report** with the declaration, host, reason and
`python3 tools/deps/build_ladder.py --edit <host>` — the manager decides.

## 7. Wiring

In `lean/spec/check_flt_statements.py`, appending **last** so no earlier last-name match can
flip, per order:

* order 1: the two `Theorems/Thm_…` wrappers and the two `P2M/Sol/S_…` files to `SOURCES`;
  `"FLTForHuman/WeierstrassCurve/Automorphism/Basic.lean"` to `PORT_FILES`.
* order 2: `"FLTForHuman/WeierstrassCurve/Automorphism/CharTwo.lean"` to `PORT_FILES`.
* order 3: `"FLTForHuman/WeierstrassCurve/Automorphism/CharThree.lean"` to `PORT_FILES`.

Run the checker **as soon as order 1 is written** (it is text-only and needs no build): the
11 prelude statements must each land `identical`, and the expected delta from the 7218
baseline is +11 after order 1, +1 after order 2, +1 after order 3. Any other delta, a
`MISMATCH`, or a `MISSING` is a statement drift to fix before building. Target
**0 mismatched, 0 missing**, then mutation-test one headline per order and revert.

## 8. Risks

* **Statement drift on the prelude.** `xy`, `castPt`, `vcHom` are copied across many pin files
  (`castPt` alone in 82); the lookup accepts any statement-identical `SOURCES` candidate, so a
  drift shows up as `MISMATCH`, not as a benign ambiguity. Transcribe verbatim and use the
  checker as the instrument, not the build.
* **The `def`-binder trap** (§2). `xy`/`castPt`/`vcHom` take `K` from a section variable; spell
  them that way.
* **`•` on curves and `(γ • W).toAffine`**: the port's `Velu/Equivariance.lean` and
  `Velu/CyclicQuotientJ.lean` already thread this; when a `rw` reports no progress, look for
  the ported spelling there before introducing a helper.
* **The char-2 proof is long (988 pin lines) with an explicitly computed `σ²+σ+1 = 0` case
  analysis.** Budget the module's edit loop accordingly (the pin's tactic blocks are
  `nlinarith`/`linear_combination` heavy); if a single declaration exceeds the wall bound,
  quarantine it and report rather than raising the cap.
* The pin's `set_option maxHeartbeats 6400000` is **not** transcribed (global cap
  4,000,000); its `linter.unusedSectionVars` / `linter.unusedVariables` (and char 2's
  `linter.unusedSimpArgs`) suppressions **are** — see §0, corrected during review.

## 9. Stop and report

If a statement cannot be matched without moving the pin's text; if a helper is genuinely
needed publicly and is `private` in a hub; if the shared prelude cannot be one module because
the two consumers need different section variables; or if a build exceeds its bound and
bisecting does not settle it.

## 10. Completion report (per order)

Module path; public/`private` counts; every local `private` re-derivation with its host;
tier 0 / tier 1 wall and CPU times; checker before → after with the `identical` delta
reconciled against the new public surface and the mutation result; `#print axioms` for each
headline (`[propext, Classical.choice, Quot.sound]`); `git status` showing only the set's
files; anything you could not match, quoted.

## 11. Outcome (2026-10-08, landed and manager-verified)

One set, one implementer, three orders; no stop condition fired; no existing Lean module
edited, no promotion proposed, nothing committed.

| order | module | lines | public / private | tier 0 | tier 1 |
|---|---|---:|---:|---:|---:|
| 1 | `WeierstrassCurve/Automorphism/Basic.lean` | 94 | 11 / 0 | 20.0 s → 3.6 s | 5.1 s → 7.1 s |
| 2 | `WeierstrassCurve/Automorphism/CharTwo.lean` | 1,003 | 1 / 74 | 35.2 s → 61.7 s | 76.4 s → 90.8 s |
| 3 | `WeierstrassCurve/Automorphism/CharThree.lean` | 413 | 1 / 38 | 5.4 s → 9.4 s | 8.5 s → 11.8 s |

(The second figure in each cell is after the review's warning-cleanup round; wall is
contention-sensitive, CPU is stable. Nothing approached the wall bound; no cap raised; no
whole-tree build until the milestone.)

**Checker 7218 → 7231 identical (313 promoted, 83 renamed), 0 mismatched, 0 missing, 36 own
(7267 checked)**, +13 = exactly the 11 prelude declarations plus the two headlines, run at
every order boundary and again by the manager after the cleanup. The manager's own one-token
mutation (`α (α T) = -T` → `= T` in order 3) gave **7230 / 1 / 0** with the diff printed, and
the revert restored 7231 / 0 / 0; the implementer ran the same test once per order with the
same shape.

`#print axioms` on both headlines: `[propext, Classical.choice, Quot.sound]`. Warning-free
tier-1 elaboration on all three (`grep -c warning` = 0; the six "warning" lines lake replays
come from untouched dependencies). No `sorry`/`admit`/`axiom`/`native_decide`, no
`import Mathlib`, no heartbeat override.

**The manager's wire test** is `Zone W1` in `spec/DeligneSerreConsumer.lean`: a `HEq`-level
coordinate transport through the bundled `vcHom` (prelude), the characteristic-2 `σ` with its
quadratic relation and a non-scalar `3`-torsion witness (order 2), and the characteristic-3
converse half of the classification — `α ∘ β` realised by a variable change and re-expressed
through the prelude (order 3). Elaborates exit 0; deleting any of the three modules fails its
zone.

### Deviations, recorded

* **The order was wrong about the linter options, and the review corrected it.** An earlier
  draft of §0/§8 forbade transcribing the pin's `linter.*` suppressions; the pin sets
  `unusedSectionVars`/`unusedVariables` in both files (plus `unusedSimpArgs` in char 2) and 86
  landed port modules transcribe them, so the set is warning-free only with them. The
  corrected §0 is the contract; the two order headers were corrected with it. The
  generalizable rule: transcribe the pin's `linter.*` options, never its `maxHeartbeats`.
* **Self-base-change is not definitional in mathlib `v4.34.0`.** The pin's char-2 torsion
  arguments use `(E₀ K)⁄K = E₀ K` definitionally; the port carries
  `have hb : (E₀ K).baseChange K = E₀ K` and transports with `hb ▸ ⟨e⟩`, the adaptation
  already used at `WeierstrassCurve/Velu/CyclicCount.lean:429`.
* **The pin's `scoped instance E₀_isElliptic` is not reproducible** (it needs
  `p2m_open_scoped`); the port declares a private unscoped instance keyed on the private
  `E₀`, unusable by importers and invisible to the checker, and drops the `@[scoped simp]`
  attributes on the private `E₀_aᵢ` rfl lemmas.
* **`act` is `vcHom`.** The pin's char-2 `act`/`heq_act`/`xy_act` are the char-3
  `vcHom`/`heq_vcHom`/`xy_vcHom` specialised to `E₀`; the shared prelude carries the general
  three once, and char 2 gets a private `abbrev`. The pin's `xy_neg` and
  `exists_eq_some_of_xy_eq` are needed by char 3 only, so they stay private there rather than
  joining the shared prelude.
* **Namespace shape.** `private` is namespace-scoped and the headlines' FQNs are fixed by the
  wrappers, so the machinery lives directly in `namespace WeierstrassCurve` (the prelude in
  `WeierstrassCurve.Automorphism`) at the pin's leaf names. No hub name is shadowed.
