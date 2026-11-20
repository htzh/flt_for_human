/-
  The determinant companion of the central character of the weight-one lift.

  `weightOneLift_centralScalar_det_gen_mul` is the scalar law of the lift applied at one particular
  central element. Let `f` be a weight-one form on `Γ₁(n)` with central character `χ`, let `Φ` be a
  Hecke eigensystem, and suppose

  * (`hb`) outside a finite set `S` of places, the `v`-th Hecke eigenvalue of `Φ` is the central
    character of the lift — `χ` read on idèle classes by
    `DirichletCharacter.dirichletIdeleChar` times the normalized absolute value — evaluated at the
    determinant of the `v`-th production pin:
    `Φ.b v = ω_χ (det (gen v))` as complex numbers; and
  * (`hlaw`) the lift transforms along the whole centre `Z`: for every `z : Z` and every `g`,
    `weightOneLift n f (centralScalar z * g) = ω_χ z * weightOneLift n f g`.

  Then for every `v ∉ S` and every `g` the same relation holds with the arbitrary central element
  `z` replaced by the `det`-value of the pin,

      weightOneLift n f (centralScalar (det (gen v)) * g) = Φ.b v * weightOneLift n f g.

  **Relation to `weightOneLift_centralScalar_mul`.** That row (AF95D,
  `LanglandsTunnell/WeightOneLiftCentralScalar.lean`) is the one that *proves* `hlaw`, from `n ≠ 0`
  and the two `Γ`-conditions on `f`; this module does not reprove it, it consumes it as the second
  hypothesis. The two rows are the two halves of one statement: `weightOneLift_centralScalar_mul`
  gives the centre law at an arbitrary idèle class `z : Z`, and this row feeds that law the
  specific element `det (gen v)`, whose character value a Hecke eigensystem supplies as `Φ.b v`.
  The composition is the row's own body, one application.

  The pin's two `private` lemmas are the `det` bookkeeping on the production pins: for the
  *compact* pins the centre subgroup is everything, `Z = ⊤` (`productionPinsCompact_Z`), so the
  determinant of any `gen v` is central (`det_gen_mem_Z`); `det_gen_law_of_central_law` is `hlaw` at
  that particular element, with `hb` turning the character value into the eigenvalue.

  spec-pin: P2M/Sol/S_LanglandsTunnell_weightOneLift_centralScalar_det_gen_mul.lean

  ## Port deltas

  - **Import narrowing (the scaffold's umbrella).** The scaffold opened with `import Mathlib`. This
    file's content is entirely `WeightOneLiftCentralScalar`'s vocabulary plus
    `dirichletIdeleChar` (`NumberTheory/RatIdele/UnitResidue`), and both of those modules already
    carry the mathlib modules the statements and the three bodies use (`det`, `⊤` of a subgroup,
    `rw`/`exact`), so the umbrella is dropped and the file elaborates silently on the two port
    imports alone — the port's established practice (cf. `RepTheory/LocalLanglands/IntegralSubgroup.lean`).
    Statement-neutral. Measured: the umbrella's olean closure is 6.1 GB, which on this box is
    >100 s wall and >6 GB RSS per `lake env lean` run (the gate's `timeout 100` cannot pass);
    without it the module elaborates in 6–9 s user CPU (2–4 GB RSS; 16–160 s wall, the spread being
    the box's load from the other orders, not this file).
  - **Namespace flattening only.** The pin's `solution` lives in the search-stage
    `P2MW.….P2GProbe.C2`; here the row is `LanglandsTunnell.weightOneLift_centralScalar_det_gen_mul`
    and the two `det` lemmas sit beside it at the same namespace. The pin states the two lemmas
    `private`; the scaffold declares them public so that the checker reads them
    (FR-0242 — a `private` port declaration is skipped, and the pin's statement hash is what the
    checker verifies). The pin's row calls the lemmas through the stage namespace and the port's
    row calls them by their flattened names; nothing else about the statements changed.
  - **The pin's two disarming `attribute` lines are not carried.** The pin opens with
    `attribute [-instance] instCountableOfNumberField_definitions` and
    `attribute [-simp] AdelicDock.coe_finEmbed AdelicDock.splice_apply_self AdelicDock.coe_localEmbed`.
    The first names a pin-only instance (`instCountableOfNumberField_definitions` has no port
    counterpart), and the second is unnecessary in the port: nothing here unfolds through
    `AdelicDock`, and the module is silent without both lines.
  - **No body-level substitution at all.** Both `det` lemmas replay the pin's bodies verbatim
    (`rw [productionPinsCompact_Z]`, `exact Subgroup.mem_top _`; and `intro` / `rw [hb v hv]` /
    `exact hlaw ⟨…, det_gen_mem_Z v⟩ g`), and the row's body is the pin's
    `det_gen_law_of_central_law f χ Φ S hb (weightOneLift_centralScalar_mul hn f hf χ hχ)`. No
    deprecated spelling, no `haveI`, no `Matrix.SpecialLinearGroup` rewrite: none of FR-0238's /
    FR-0245's / FR-0250's drift classes is met here.

  ## Deferred pin surface

  None. `move_dead.py` reports 0 declarations / 0 lines, and the pin's three declarations are all
  declared here: the two `det` lemmas and the row (onto which the pin's `solution` wrapper folds —
  `scaffold_audit` reads it `FOLDED`, the wrapper glue at pin `:55`).

  ## Gates

  - `lake env lean -DautoImplicit=false` — exit 0, **no output at all** (the silence gate; `sorry`-free,
    no linter warning). `lake build FLTForHuman.LanglandsTunnell.WeightOneLiftCentralDet` under the
    build lock — green.
  - `spec/check_port.py --force` — **3 ok, 0 mismatch, 0 missing, 0 own, 0 kw** (corpus `aa2d8b3`;
    the two `det` lemmas at pin `:19`/`:24`, the row at pin `:55`).
  - `tools/deps/scaffold_audit.py` — **complete**: 1 pin public declaration on the wire, 3 port
    declarations, 0 satisfied by the import closure, 1 `FOLDED` (the `solution` wrapper).
  - `#print axioms` on all three declarations — `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx` (probe: `lean/tmp/af96/probe.lean`).
  - `dedup.py --within --module WeightOneLiftCentralDet` — **0 duplicate clusters**, 3 declarations,
    0 removable lines. `move_dead.py --dry-run` — **0 declarations, 0 lines**.
  - Heartbeat probe pair (measured, **never installed**, FR-0225): silent at
    `-DmaxHeartbeats=4000`; first failure at `2000` — `(deterministic) timeout at whnf` in
    `det_gen_law_of_central_law`, whose statement carries the `hb` telescope
    (`Units.map … |·| … |>.comp … |>.comp det`), so the heaviest declaration costs ≈2–4 k heartbeats
    and the row costs less than its own lemma. The project cap is 4,000,000, so there is no build
    risk. No `set_option maxHeartbeats` is carried.
-/

import FLTForHuman.LanglandsTunnell.WeightOneLiftCentralScalar
import FLTForHuman.NumberTheory.RatIdele.UnitResidue

set_option autoImplicit false

noncomputable section

open NumberField AutomorphicForm UpperHalfPlane DihedralWeightOne
open IsDedekindDomain
open scoped ModularForm MatrixGroups

namespace LanglandsTunnell


theorem det_gen_mem_Z (v : HeightOneSpectrum (𝓞 ℚ)) :
    Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v) ∈ (productionPinsCompact ℚ).Z := by
  rw [productionPinsCompact_Z]
  exact Subgroup.mem_top _

theorem det_gen_law_of_central_law {n : ℕ} [NeZero n] (f : ℍ → ℂ)
    (χ : DirichletCharacter ℂ n)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ))
    (hlaw : ∀ (z : (productionPinsCompact ℚ).Z) (g : AdelicGL2 (𝓞 ℚ) ℚ),
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f (centralScalar (𝓞 ℚ) ℚ (z : (AdeleRing (𝓞 ℚ) ℚ)ˣ) * g)
        = ((((DirichletCharacter.dirichletIdeleChar χ *
            (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
              (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          (productionPinsCompact ℚ).Z.subtype) z : ℂˣ) : ℂ) * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  intro v hv g
  rw [hb v hv]
  exact hlaw ⟨Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v), det_gen_mem_Z v⟩ g

theorem weightOneLift_centralScalar_det_gen_mul
    {n : ℕ} [NeZero n] (hn : n ≠ 0) (f : ℍ → ℂ)
    (hf : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma1 n → f ∣[(1 : ℤ)] (ε : GL (Fin 2) ℝ) = f)
    (χ : DirichletCharacter ℂ n)
    (hχ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 n →
      f ∣[(1 : ℤ)] (γ : GL (Fin 2) ℝ) = χ ((γ 1 1 : ℤ) : ZMod n) • f)
    (Φ : HeckeEigensystem ℚ ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (hb : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
      Φ.b v = ((((DirichletCharacter.dirichletIdeleChar χ *
          (Units.map (Complex.ofRealHom.toMonoidHom.comp NNReal.toRealHom.toMonoidHom)).comp
            (MeasureTheory.distribHaarChar (AdeleRing (𝓞 ℚ) ℚ)).toHomUnits).comp
          Matrix.GeneralLinearGroup.det) ((productionPinsCompact ℚ).gen v) : ℂˣ) : ℂ)) :
    ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S →
    ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
      weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f
          (centralScalar (𝓞 ℚ) ℚ (Matrix.GeneralLinearGroup.det ((productionPinsCompact ℚ).gen v)) * g)
        = Φ.b v * weightOneLift (Ideal.span {(n : 𝓞 ℚ)}) f g := by
  exact det_gen_law_of_central_law f χ Φ S hb
    (LanglandsTunnell.weightOneLift_centralScalar_mul hn f hf χ hχ)

end LanglandsTunnell

end
