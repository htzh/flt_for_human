# WORKORDER MSDEF — the MS-7 gate and the `qExpansion_E6_eq_map_mk` promotion

**SET**: [TOPIC-ready-shelf-1.md](TOPIC-ready-shelf-1.md) §0.2, §1.1, §5 item 6. **The manager
lane**, not an order: it blocks only **MS-7**, and it is independent of waves 1–2.
**Size**: 37 pin lines + a 15-line promotion. Two single-module builds.

Neither item moves a shelf figure: the gate is a definition layer (not a premise) and the
promotion only makes an already-counted node *importable*.

## Item 1 — the definition gate

**New module** `lean/FLTForHuman/ModularCurve/Defs/XHDiamondModL.lean`, transcribing
`Definitions/Def_ModularCurve_XHDiamondModL.lean` (50 lines, two declarations):

```
def IsDiamondPullbackModL (K : Type*) [Field K] (M : ℕ) (H : Subgroup (ZMod M)ˣ)
    (ρ : CongruenceSubgroup.Gamma0 M →*
      (qExpFunctionFieldC K (CohCarrier.GammaH M H) ≃ₐ[K]
        qExpFunctionFieldC K (CohCarrier.GammaH M H))) : Prop :=
  ∀ (γ : CongruenceSubgroup.Gamma0 M) (k : ℤ)
    (f g f₁ g₁ : ModularForm (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)) k)
    (pf pg pf₁ pg₁ : PowerSeries ℤ), …
```

and `IsDiamondPullbackModL.coe_apply_eq` (its projection lemma). Both at the pin's names, nothing
else — **no** additional helper, no `set_option`, no `attribute [-simp]` prelude.

Wire: **exactly one** `spec-pin:` line, `spec-pin: Definitions/Def_ModularCurve_XHDiamondModL.lean`
(the def-wave convention: `ModularCurve/Defs/ResidualRealization.lean:22`).

Imports: the vocabulary's homes, each already ported — `ModularCurve/X1/Defs.lean` (or wherever
`qExpFunctionFieldC` lives), `ModularForms/Defs/GammaH.lean`, `ModularCurve/X1/Integral.lean`
(`IsIntegralQExp`), `Defs/Laurent.lean` (`intSeriesC`). Take the smallest set that elaborates; every
candidate is a leaf-ish def module, so the closure is cheap. `X1DiamondPullback`
(`ModularCurve/X1/DiamondAut.lean`) is the X₁ precedent — do **not** import it (it is a 745-line
proof module; the gate needs only the vocabulary).

Gates: edit loop silent at 200k; `flock tmp/lean-build.lock timeout 90 lake build
FLTForHuman.ModularCurve.Defs.XHDiamondModL`; `python3 spec/check_port.py --force
FLTForHuman/ModularCurve/Defs/XHDiamondModL.lean` → **2 ok / 0 mismatch / 0 missing / 0 own**;
`#print axioms` on both → `[propext, Classical.choice, Quot.sound]`; zero warnings.

## Item 2 — the promotion

**Edit** `lean/FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean`. Today it holds, at lines
97–111, inside `namespace EisensteinCube` (opened at line 90):

```
private theorem qExpansion_E6_eq_map_mk :
    UpperHalfPlane.qExpansion 1 ⇑ModularForm.E₆ =
      PowerSeries.map (Int.castRingHom ℂ)
        (PowerSeries.mk fun n => if n = 0 then 1 else -504 * ∑ d ∈ n.divisors, (d : ℤ) ^ 5) := …
```

which is byte-identical to the pin's public node `ModularCurve.qExpansion_E6_eq_map_mk`
(`Theorems/Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean`, whose `S_` copy is a 34-line leaf with
2 cone and 10 project consumers). Promote it:

- **public**, and at **`ModularCurve.qExpansion_E6_eq_map_mk`** — i.e. *not* inside
  `ModularCurve.EisensteinCube`. Move the declaration out of the `EisensteinCube` section (keep the
  docstring); the in-file use in `eisenstein4_cube_sub_mk_sq_aux` resolves by namespace lookup and
  needs no change.
- add **two** `spec-pin:` lines to the header: `Theorems/Thm_ModularCurve_qExpansion_E6_eq_map_mk.lean`
  and the matching `P2M/Sol/S_…` copy. (If `check_port --force` objects to the `S_` line — the pin's
  `S_` file's three Bernoulli helpers are *not* transcribed, the port's proof uses `decide +kernel` —
  keep the `Thm_` line only and record the reason in the header prose.)
- the module's own prose says the deferred headline is "Not ported here": leave that paragraph
  alone (it is about `exists_sum_smul_eq_of_isIntegralQExp_gamma1`, a different node).

Do **not** promote `qExpansion_E4_cube_sub_E6_sq`, `qExpansion_E4_eq_map_eisenstein4` (already
public elsewhere) or any other helper.

Gates: edit loop silent at 200k; `flock tmp/lean-build.lock timeout 90 lake build
FLTForHuman.ModularCurve.X1.IntegralityJqNModC`; `python3 spec/check_port.py --force
FLTForHuman/ModularCurve/X1/IntegralityJqNModC.lean` → **4 ok / 0 mismatch / 0 missing / 0 own**
(baseline today: 3 ok); `#print axioms ModularCurve.qExpansion_E6_eq_map_mk` →
`[propext, Classical.choice, Quot.sound]`; zero warnings.

**The verification of the pair** (run these, quote the output):

```bash
cd tools/deps && python3 twin_scan.py --node ModularCurve.qExpansion_E6_eq_map_mk   # twin-private -> twin-public
python3 frontier.py --selfcheck                                                     # PASS
python3 frontier.py --ds --ready --include-leaves --rank-by silo --top 0 --json > build/msdef-read.json
```

The second and third must show the read **unchanged**: `needed` 960 / 388,827, MC ready
20 / 8,178, frontier 1,455 / 738,539. A promotion that moves the read is a promotion that changed
a statement — stop and report.

## Not this order

- Do not touch the five wave-1 hosts, the topic note, or the three wave-1 workorders.
- No tree build, no git, every command under 2 minutes, builds serialized on
  `tmp/lean-build.lock` (three other agents share it).
- No `sorry`/`admit`/`axiom`/`native_decide`, no `set_option`, no linter suppression.
