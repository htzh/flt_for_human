# The Iwasawa analytic core — mathematics, measurement and the two-wave port

The Deligne–Serre frontier's step-6 re-read (after the F1/F2 Tate landings) surfaces the analytic
half of the archimedean `GL₂` layer at a complex and a real place. Its nodes sit under
`AutomorphicForm.ComplexIwasawa` and `AutomorphicForm.RealIwasawa`, they are the bottom of the
subtree that feeds `AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary`
and `AutomorphicForm.bruhatEisenstein_sub_constantTerm_isRapidlyDecreasingOn`, and through them the
Rankin-type second-moment gate of [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §7. This
note is the group's home: §1 the mathematics, §2 the cone measurement, §3 the duplication and
budget, §4 the definition layer and the manager's ground, §5 the port structure and the two waves,
§6 risks and recorded negatives, §7 reproduce, §8 residuals.

Pin `anthropics/fermats-last-theorem@aa2d8b3` (Lean `v4.33.1` / mathlib `db584cd6`); port mathlib
`v4.34.0`.

Companions: the mathematics of the decomposition and its archimedean estimates —
[../../math/028-iwasawa-decomposition-and-archimedean-estimates.md](../../math/028-iwasawa-decomposition-and-archimedean-estimates.md);
the column note [../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2 and §7 (the
gates these estimates stand behind); the playbook [../porting-playbook.md](../porting-playbook.md)
§2.1–§2.4 (measurement, route, whole nodes, dedup), §3.2–§3.5 (layout, work orders, sets, build
ladder), §4 (faithfulness), §5 (sharing); the sibling def-layer effort
[PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md) (the adèlic foundation, a different
subject); the work orders [WORKORDER-I1-complex-engine.md](WORKORDER-I1-complex-engine.md),
[WORKORDER-I2-complex-successors.md](WORKORDER-I2-complex-successors.md) and
[WORKORDER-I3-real-engine.md](WORKORDER-I3-real-engine.md).

## 1. The mathematics

At an archimedean place the Iwasawa decomposition writes a translate of an invertible `2×2` matrix
as a triangular (Borel) factor times a compact (unitary) factor. The pin proves it by hand — mathlib
has no `GL₂` Iwasawa decomposition — and then estimates the compact factor's smoothness and the
Fourier transform of its radial length, which is what an archimedean weight in a Rankin–Selberg /
Whittaker integral needs.

**Complex place.** Fix `g : Matrix (Fin 2) (Fin 2) ℂ` with `g.det ≠ 0`, `w = !![0,1;1,0]` the Weyl
element and `n(z) = !![1,z;0,1]` the upper unipotent. With
`P(z) = g₀₀ + z g₁₀` (`botP`), `Q(z) = g₀₁ + z g₁₁` (`botQ`),

* the **radial length** is `radC g z = √(‖P(z)‖² + ‖Q(z)‖²)` and
* the **compact factor** is `kC g z = !![conj Q / r, -conj P / r; P / r, Q / r]`,

which lies in `SU(2)` and satisfies `w n(z) g = borelC g z * kC g z` (`borelC` being the
triangular factor). The analytic statements, in the order they depend on one another:

1. `contDiff_and_exists_bound_iteratedFDeriv_kC_apply` — every entry of `kC g ·` is `C^∞` and all
   its iterated real Fréchet derivatives are bounded;
2. `exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact` — the same bounds, uniform as `g`
   ranges over a compact set of invertible matrices;
3. `kC_mem_specialUnitaryGroup`, `weyl_mul_unipotent_mul_eq_borel_mul_kC` — the group/decomposition
   facts (`kC` unitary, the explicit Borel factor);
4. `exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact` — away from `det g = 0`,
   `radC g z²` grows like `1 + ‖z‖²` uniformly, so `radC^{-κ}` is integrable for `κ > 2`;
5. `contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact` — the symbol
   estimate: `radC^{-u}` is smooth with every derivative dominated by the undifferentiated majorant
   `radC^{-Re u}`, uniformly on compacta;
6. `norm_fourierIntegral_cpow_radC_mul_le_polyDecay` and its uniform form
   `exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` — integration by
   parts against (5) gives faster-than-any-polynomial decay of the Fourier transform of
   `radC^{-u} · P` in the unipotent variable;
7. `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` — the complex-place
   Whittaker (Jacquet) integral is continuous and holomorphic in the spectral parameter on its
   half-plane of absolute convergence, with rapid decay in the additive variable.

**Real place.** The same development with `K = ℝ`: `botRow g u = (g₀₁ + u g₁₁, g₀₀ + u g₁₀)` as a
complex pair, `rad g u = ‖botRow g u‖ = √((g₀₀ + u g₁₀)² + (g₀₁ + u g₁₁)²)`, and the compact factor
is the rotation `kR` with angle `θ(g,u)`. The real statements mirror the complex ones —
`contDiff_and_exists_bound_iteratedFDeriv_kR_apply`,
`norm_fourierIntegral_cpow_rad_mul_le_polyDecay`,
`exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact`, and the Whittaker
continuation `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral`.

The two halves are **parallel, not twins**: the complex factor is a `SU(2)` matrix over `ℂ`, the real
one a rotation over `ℝ`, and the estimates are proved separately (`ℂ`-power vs `ℝ`-power, `normSq`
vs `sq`). They share exactly one non-trivial fact, the generic Fourier bound of §4.

## 2. The cone measurement

`frontier.py` prices the family inside the Deligne–Serre cone at **13 nodes** — 9 `ComplexIwasawa`
and 4 `RealIwasawa`. Nine are graph **leaves** (`needed == 1`, no premises); the other four are the
successors those leaves unblock. Neither the default `--rank` view nor `--ready` shows any of them:
they are below `F` but their consumers are the gate, so the leaves only appear under
`--include-leaves`, and the four successors only under `--rank-scope all`.

| node | N/C/R | layer | needed | own `S_` | silo |
|---|---|:--:|---:|---:|---:|
| `contDiff_and_exists_bound_iteratedFDeriv_kC_apply` | C | 0 | 1 | 1,324 | 1,324 |
| `exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact` | C | 0 | 1 | 1,754 | 1,754 |
| `kC_mem_specialUnitaryGroup` | C | 0 | 1 | 97 | 97 |
| `weyl_mul_unipotent_mul_eq_borel_mul_kC` | C | 0 | 1 | 109 | 109 |
| `exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact` | C | 0 | 1 | 234 | 234 |
| `norm_fourierIntegral_cpow_radC_mul_le_polyDecay` | C | 0 | 1 | 1,955 | 1,955 |
| `contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact` | C | 1 | 3 | 493 | 3,571 |
| `exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` | C | 2 | 5 | 203 | 4,008 |
| `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` | C | 3 | 6 | 371 | 4,379 |
| `contDiff_and_exists_bound_iteratedFDeriv_kR_apply` | R | 0 | 1 | 744 | 744 |
| `norm_fourierIntegral_cpow_rad_mul_le_polyDecay` | R | 0 | 1 | 1,209 | 1,209 |
| `exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact` | R | 0 | 1 | 1,530 | 1,530 |
| `continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` | R | 1 | 3 | 355 | 2,629 |

The nine leaves are the "top silos" — 8,956 raw `S_` lines between them. **The silo reading
overstates them ~2.2×**, because the pin writes one self-contained development into every `S_` file
of a family (§3). The successors are priced by the same demand once the leaves land.

`--ready` shows **0** Iwasawa rows today (the 88-node shelf's `AutomorphicForm` rows are other
subjects), and the 4 successors do not appear in the default cone-wide `--rank` at all; the family is
read with

```bash
cd tools/deps
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --include-leaves --top 0          # the 9 leaves
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --rank-scope all --top 0          # all 13, with `needed`
```

**Where the family sits.** These are *not* `ModularCurve` rows, so
[../PORTING-DeligneSerre.md](../PORTING-DeligneSerre.md) §2's "not this column's to cut" applies; the
def-layer blueprint [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md) is the adèlic
foundation and does not mention Iwasawa either. The cluster has no prior owner: this note is it.

## 3. Duplication and budget

The pin's `S_` files are self-contained: each re-carries the whole prelude it needs. `port_advise`
on the 13 nodes reports **0 trusted substitutions and 35 suspect ones** — every "reuse" is a
type-only `def` match the parser cannot judge (`botP : ℂ → ℂ` against `pval`, `radFloor` against
`EisensteinSeries.rho`, `weylR` against `CuspForm.FrickeHecke.frickeGL`, `centerC` against
`SiegelCoordinates.xCoord`) — so read them by hand (§6) and expect **nothing to reuse**. The port has
no `radC`/`kC`/`weylR`, and `twin_scan` calls both headline kernels `new`.

`port_advise`/`port_plan` on all 13:

| | raw `S_` | declaration | duplicate | groups | **net new math** |
|---|---:|---:|---:|---:|---:|
| 9 cone leaves | 8,956 | 8,791 | 4,709 | 277 | **4,082** |
| **Complex** (9 nodes) | 6,540 | 6,367 | 2,999 | 172 | **3,368** |
| **Real** (4 nodes) | 3,838 | 3,768 | 1,819 | 207 | **1,949** |
| Complex + Real (13) | 10,378 | 10,135 | 4,879 | 377 | **5,256** |

0 already in the port, 243 boilerplate lines. The shared blocks:

| block | decls | once-cost | files |
|---|---:|---:|---|
| Complex common (the `kC`/`radC` development) | 65 | 1,155 | the 3 big Complex files |
| Real common (`kR`/`rot`) | 92 | 619 | the 3 Real files with `norm`/`contDiff` |
| Real non-uniform extension | 40 | 512 | the 2 Real `norm` files |
| Complex `radC` prelude | 8 | 102 | 5 Complex files |
| Complex decomposition pair | 6 | 74 | `kC_mem`, `weyl_mul` |
| Complex `cpow` pair | 4 | 58 | `contDiff_cpow`, `norm_fourier` |
| **generic Fourier (cross Complex/Real)** | **1** | **44** | 2 Complex + 2 Real files |

Inside a namespace the duplication is severe (86 Complex-internal shared names / 2,914 removable
lines, 133 Real-internal / 1,696); **between the two namespaces it is one declaration** — the
generic `pow_mul_norm_fourierIntegral_le_of_coercive`. Joining the waves saves 61 of 5,256 lines
(5,317 separate → 5,256 together).

## 4. The definition layer and the manager's ground

**(a) The pin `Def_AutomorphicForm_ComplexIwasawa` is homed whole** — 25 lines, 4 declarations
(`botP`, `botQ`, `radC`, `kC`) under the pin's namespace `AutomorphicForm.ComplexIwasawa`. It is a
leaf and it is *invisible to the frontier*, which walks citations, not imports; the wrapper
statements of wave 1 name `radC` and `kC`, so nothing can be stated before it lands. The pin's
`S_` files also carry their own namespaced copies of these four (inside `M4aP3C.CplxIwasawa`); they
are byte-identical to the `Definitions/` module and are **dropped** in favour of the homed copy
(defeq; the pin's `M4aP3C.CplxIwasawa` names are not statement vocabulary). Home:
`FLTForHuman/AutomorphicForm/Iwasawa/Complex/Basic.lean` (playbook §3.1: the module is the
mathematical role, the pin `Def_` file is not the home's name).

**(b) The one shared generic block is homed once.** `pow_mul_norm_fourierIntegral_le_of_coercive`
(pin `M4aP3B.FourierDecay`, `S_AutomorphicForm_ComplexIwasawa_norm_…:1524` and
`S_AutomorphicForm_RealIwasawa_norm_…:871`, statements byte-identical) bounds
`(c‖w‖)^n · ‖∫ f e^{-i⟨Lv,w⟩}‖` by `2^n Σ_j ∫ ‖D^j f‖` for a coercive `L`; it and the trivial
`gate_degenerate` are the only cross-wave sharing. Home: `FLTForHuman/MeasureTheory/FourierDecay.lean`
— a generic measure/Fourier fact, not Iwasawa mathematics (playbook §5: a theory exports only from
its own domain). Both waves import it instead of each transcribing 44 lines.

**(c) The real definitions have no public home and stay proof-local.** The pin has no
`Def_AutomorphicForm_RealIwasawa`; the real vocabulary (`rot`, `rotGL`, `weylUnip`, `botNormSq`,
`foot`, `center`, `dir`, `botRow`, `rad`) lives *inside* the `S_` files, and the real wrapper
statements spell `Real.sqrt ((g₀₀ + x g₁₀)² + (g₀₁ + x g₁₁)²)⁻¹ …` inline — no named definition is
statement vocabulary. So the real engine keeps them `private` (or file-public where the pin is
public), and **no real definition module is owed**.

**(d) Two non-promotions are recorded now** (playbook §5, hub prohibition):
`weylR` is only a *type-only* match for the port-`private`
`CuspForm.FrickeHecke.frickeGL` (different statement) — re-derive it locally; and the real `rot`
(`θ : ℝ ↦ !![cos θ, -sin θ; sin θ, cos θ]`) shares a last name with the port's
`RepTheory.AntiInvolutionHaar.rot (p q : ℝ) ↦ !![p, q; -q, p]` but not its statement — keep the real
one in `AutomorphicForm.RealIwasawa.*` and do **not** promote or reconcile. Neither is a collision:
the namespaces are disjoint.

**Namespace policy** (playbook §5, decided before the wave): the pin's mangled
`P2MW.S_<stem>.M4aP3C.*` / `…M4aP3B.*` chapter is replaced by the theory namespaces
**`AutomorphicForm.ComplexIwasawa.*`** and **`AutomorphicForm.RealIwasawa.*`**, keeping the pin's
declaration names verbatim inside them. The definition module keeps
`AutomorphicForm.ComplexIwasawa.{botP,botQ,radC,kC}` because the wrappers name those.

## 5. The port structure — two waves

Two clusters, because the cross-namespace share is one generic lemma (§3), the namespaces are
disjoint, the definition ground differs (§4c), and each half is a set-sized story on its own
(playbook §3.2: one sentence without an "and"; §3.5: disjoint namespaces and no shared prelude are
the one safe parallel overlap). **Within** a wave the several `S_` files are one development written
several times and are ported **once**, as an engine plus a headline façade — the F1/F2 shape, not
file-by-file.

| wave | cluster | nodes | net new | engine modules (tier 3) | façade (tier 1) |
|---|---|---:|---:|---|---|
| 1 | ComplexIwasawa | 9 | 3,368 | `AutomorphicForm/Iwasawa/Complex/{Core,Decay,UniformDecay,Continuation}.lean` | `…/Complex/Estimates.lean` |
| 2 | RealIwasawa | 4 | 1,949 | `AutomorphicForm/Iwasawa/Real/{Core,Decay,Continuation}.lean` | `…/Real/Estimates.lean` |

Wave 1 is 2.2× the playbook's ~1,500-line dispatch size, so it is **three work orders**: I1 the six
layer-0 kernels (Core + Decay), I2 the three successors (UniformDecay + Continuation), I3 the real
engine. I1 and I3 are independent and may be written in parallel (serialised builds); I2 waits for
I1 and never reopens I1's two modules.

**Tiers.** The engines are tier 3 — built, importable, in `spec/UNWIRED-PUBLIC.md`, not in
`PORT_FILES`. The façades state the pin wrappers' statements verbatim and prove them by a one-line
application of the engine kernels; they are the checker wire (`PORT_FILES`, appended last), so the
checker delta is exactly the wave's headline count (+9 and +4) plus the def layer's +4. Every
transcribed declaration carries a `-- pin: <name> (<S_ file>:<line>)` provenance comment for
`tools/deps/unwired_register.py`.

The façades are named **`Estimates.lean`** — the mathematical subject they carry — and not
`Headlines.lean`: a module is a mathematical role, not an artifact kind (playbook §3.1), so the
`Complex/` and `Real/` theory directories stay open to further subjects instead of parking a
catch-all "headline" module that every later statement would have to be added to or duplicated
beside.

**Module roles.**

| module | role | kernels (public) |
|---|---|---|
| `Complex/Basic.lean` (manager) | the pin `Def_` module whole | `botP`, `botQ`, `radC`, `kC` |
| `MeasureTheory/FourierDecay.lean` (manager) | the shared generic Fourier block | `pow_mul_norm_fourierIntegral_le_of_coercive`, `gate_degenerate` |
| `Complex/Core.lean` (I1) | the shared complex engine: the `radC` prelude and the 1,155-line common block, written once, plus the compact-factor and decomposition kernels | `Engine.contDiff_and_exists_bound_iteratedFDeriv_kC_apply`, `Engine.exists_forall_bound_iteratedFDeriv_kC_apply_of_isCompact`, `Engine.kC_mem_specialUnitaryGroup`, `Engine.weyl_mul_unipotent_mul_eq_borel_mul_kC` |
| `Complex/Decay.lean` (I1) | the decay engine: integrability and pointwise Fourier decay | `Engine.exists_forall_integrable_integral_rpow_neg_radC_le_of_isCompact`, `Engine.norm_fourierIntegral_cpow_radC_mul_le_polyDecay` |
| `Complex/UniformDecay.lean` (I2) | the uniform-in-`g` symbol and decay forms | `Engine.contDiff_and_exists_forall_bound_iteratedFDeriv_cpow_neg_radC_of_isCompact`, `Engine.exists_forall_norm_fourierIntegral_cpow_radC_mul_le_polyDecay_of_isCompact` |
| `Complex/Continuation.lean` (I2) | the complex-place Whittaker/Jacquet integral | `Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` |
| `Real/Core.lean` (I3) | the rotation engine | `Engine.contDiff_and_exists_bound_iteratedFDeriv_kR_apply` |
| `Real/Decay.lean` (I3) | the real decay engine | `Engine.norm_fourierIntegral_cpow_rad_mul_le_polyDecay`, `Engine.exists_forall_norm_fourierIntegral_cpow_rad_mul_le_polyDecay_of_isCompact` |
| `Real/Continuation.lean` (I3) | the real-place Whittaker/Jacquet integral | `Engine.continuousOn_differentiableOn_norm_le_polyDecay_weightFourierIntegral` |
| `Complex/Estimates.lean` (manager, tier 1) | the nine public complex-place statements | the nine `AutomorphicForm.ComplexIwasawa.<name>` headlines |
| `Real/Estimates.lean` (manager, tier 1) | the four public real-place statements | the four `AutomorphicForm.RealIwasawa.<name>` headlines |

The kernels keep the **pin `S_` file's** names under the engine namespace
`AutomorphicForm.ComplexIwasawa.Engine` / `AutomorphicForm.RealIwasawa.Engine`, stated with the
`Theorems/` wrapper binders (the statement authority, playbook §4). The manager's façade declares the
pin headline `AutomorphicForm.{ComplexIwasawa,RealIwasawa}.<name>` and proves it by applying the
engine kernel — the F2 split between `ModularCurve.TateCurve.<kernel>` and `ModularCurve.<name>`. The
pin's internal sub-namespaces (`CplxIwasawa`, `CplxSmooth`, `CplxDecay`, `RealKTower`, `RealDecay`,
…) are kept as sub-namespaces of the port theory namespace, so the pin's prelude names stay verbatim
and the register can read them.

## 6. Risks and recorded negatives

* **API drift is the named route risk.** The pin is Lean `v4.33.1` / mathlib `db584cd6`; the port is
  `v4.34.0` (playbook §7). The surfaces: `ContDiff`/`iteratedFDeriv` and `VectorFourier` bounds,
  `Real.rpow`/`Complex.cpow` lemmas, `Matrix`/`Star`/`conjTranspose`, `MeasureTheory` integrability,
  and `Finset`/`tsum` reorganisations. Statements stay the pin's; only proofs adapt.
* **Build-time blow-up is the other named risk.** The long declarations are the
  `exists_bound_iteratedFDeriv_*` chains (the pin's 139/119/117-line kernels) and the
  `norm_fourierIntegral_*` integration-by-parts; the low `maxHeartbeats=200000` cap is the
  instrument, and a declaration that will not fit is an instance-inference defect to fix, never a cap
  to raise. The pin's own heartbeat-bump markers are dropped.
* **Recorded negative: the 35 `port_advise` substitutions are not reuse.** All are type-only `def`
  matches across unrelated theories; the port has no `radC`/`kC`/`weylR` and no twin of either
  headline (`twin_scan`: `new`).
* **Recorded negative: no `Def_AutomorphicForm_RealIwasawa` exists.** The real vocabulary is
  proof-local and is not named by any wrapper statement (§4c).
* **Recorded negative: the pin is not on the port's mathlib line** (`db584cd6` vs `v4.34.0`).
* **Not this note's subject:** the adèlic `iwasawa` nodes in the same cone
  (`LocalGL2.iwasawa_decomposition`, `AutomorphicForm.exists_continuous_iwasawa_weyl_unipotent`,
  `…isLocallyConstant_iwasawaShellIndex…`, `NumberField.AdelicHaar.exists_lintegral_adelicGLHaar_eq_mul_lintegral_iwasawa`)
  share the word, not the theory: they are the adèlic/local decomposition and the shell-index
  machinery, which belong to [PORTING-AutomorphicForm.md](PORTING-AutomorphicForm.md).

## 7. Reproduce

```bash
cd tools/deps
# the family, both views (13 nodes / 9 leaves)
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --include-leaves --top 0
python3 frontier.py --target DeligneSerre.exists_galoisRep_of_weightOne_qCoeff_hecke_eigen \
  --rank-by silo --rank-scope all --top 0

# the budget and the shared blocks
python3 port_advise.py --nodes "<the 13 Complex/Real Iwasawa nodes>" --json build/iwasawa_advise.json
python3 port_plan.py --json build/iwasawa_advise.json

# the route
python3 twin_scan.py --node AutomorphicForm.ComplexIwasawa.norm_fourierIntegral_cpow_radC_mul_le_polyDecay
python3 explore.py  AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary
```

The checker wiring convention (the `Theorems/` wrappers first, the `S_` files second, both appended
last to `SOURCES`; the façade appended last to `PORT_FILES`; the engines tier 3) is in the work
orders and in [../logs/deligne-serre-friction.md](../logs/deligne-serre-friction.md).

## 8. Residuals

* **Ownership.** The cluster is below the Deligne–Serre gates and outside both columns' declared
  scope; this note claims it. If the automorphic column wants it, the note moves.
* **The successors are the gate's inputs, not the gate.** Landing all 13 moves
  `AutomorphicForm.norm_integral_weyl_unipotent_mul_addChar_le_polyDecay_of_unitary` one step closer,
  but the two §7 gates remain unported and unscheduled.
* **The engines stay tier 3.** Their public surface carries `-- pin:` provenance in
  `spec/UNWIRED-PUBLIC.md`; only the façades are diffed.
