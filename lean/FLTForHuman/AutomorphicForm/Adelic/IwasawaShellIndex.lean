/-
  The Iwasawa shell index: the valuation of the determinant minus the bottom row.

  spec-pin: Definitions/Def_AutomorphicForm_IwasawaShellIndex.lean

  For a number field `K`, a place `v` and `g : GL₂(𝔸_K)`, write `|a|_v = Valued.v (a.2 v)` for the
  normalised absolute value at `v`, multiplicative with values in `WithZero (Multiplicative ℤ)` —
  `|0|_v = 0`, `|1|_v = 1`, `|ϖ_v|_v = exp (-1)` for a uniformiser — and `WithZero.log` for its
  inverse on nonzero values (`log_exp`, `exp_log`, `log_mul`, `log_pow`). The vocabulary is

  * `finEntryValuation K v g i j = |g_{ij}|_v` and `finDetValuation K v g = |det g|_v`;
  * the localisation of `g` at `v`, `localMatrix v g = (g_{ij}.2 v)_{ij}`, i.e. the image of `g`
    under `Matrix.map (adeleEvalFin v)`, where `adeleEvalFin v = finAdeleEval v ∘ adeleFin`;
  * the index itself,
    ```
    iwasawaShellIndex K v g = 2 * log (max |g₁₀|_v |g₁₁|_v) - log |det g|_v  : ℤ.
    ```

  **What the number is.** `iwasawaShellIndex` is the Iwasawa (torus) exponent of `g` at `v`, read
  off the bottom row. For upper-triangular `g = [[a, b], [0, d]]` the bottom row is `(0, d)` and the
  determinant is `a * d`, so the index is `log |d|_v - log |a|_v`: the log-ratio of the two
  diagonal entries, i.e. the position of the diagonal of `g` in the shell decomposition of the
  torus at `v`. The two valuations that enter the formula are nonzero — the bottom row of `g` is
  never `(0, 0)`, and the determinant of `g` is a unit of `𝔸_K` — and that is exactly
  `max_finEntryValuation_ne_zero` and `finDetValuation_ne_zero`, the two facts that make the
  formula an honest integer; `iwasawaShellIndex_eq_zero_iff` (with its raw form
  `iwasawaShellIndex_eq_zero_iff'`) then identifies the vanishing of the index with the balanced
  case `|det g|_v = (max |g₁₀|_v |g₁₁|_v)²`.

  **The invariance lemmas are the algebra the rows consume.** Every proof below works in the
  `localMatrix` shape, which is the shape `iwasawaShellIndex_eq` exposes. The master statement is
  `iwasawaShellIndex_eq_of_localMatrix`: if `g'` has the bottom row of `g` and
  `det g' = a * det g` with `a ≠ 0`, then `index g' = index g - log |a|_v`. The three invariance
  families are its special cases:

  * `iwasawaShellIndex_centralScalar_mul` (a central idèle `u`): `diag (u, u)` multiplies the bottom
    row by `u` and the determinant by `u²`, and the two `log |u|_v` contributions cancel;
  * `iwasawaShellIndex_unipotentGL2_mul` (an additive adèle `x`): `!![1, x; 0, 1] * g` has the
    bottom row, and the determinant, of `g`;
  * `iwasawaShellIndex_heckeGen_mul` / `iwasawaShellIndex_heckeGen_mul_of_ne` (the double-coset
    generator `diag (ϖ_v, 1)`): at its own place it raises the index by exactly `1`, because
    `log |ϖ_v|_v = -1` (`valued_uniformizerUnit`, `WithZero.log_exp`); at every other place
    `heckeGen` localises to `1` and it does nothing.

  `localMatrix_mul` (localisation is a ring homomorphism), `localMatrix_heckeGen_self` and
  `localMatrix_heckeGen_of_ne` are the entry computations those three reductions run on.

  The five `def`s (`finEntryValuation`, `finDetValuation`, `iwasawaShellIndex`, `adeleEvalFin`,
  `localMatrix`) are the pin's bodies verbatim, as a `Definitions/` module requires. Every proof
  below is the pin's own body, replayed at this mathlib; the single substitution is recorded in
  `## Port deltas`.

  ## Port deltas

  - **Import narrowing (the scaffold's umbrella).** The scaffold opened with `import Mathlib`. On
    this box that umbrella's olean closure is 6.1 GB against 7 GB of RAM and costs ~100 s wall per
    `lake env lean` run (it never stays cached), which is what makes the `timeout 100` silence gate
    fail — not the mathematics. It is replaced by the three mathlib modules the declarations come
    from — `Mathlib.Algebra.GroupWithZero.WithZero` (`WithZero.log`, `log_mul`, `log_pow`,
    `log_exp`, `exp_log`), `Mathlib.Topology.Algebra.Valued.ValuationTopology` (`Valued`, and with
    it `Valued.v`) and `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic` (the `GL₂` coercion
    and determinant API: `coe_mul`, `val_det_apply`, `scalar`) — together with the scaffold's five
    port imports. Statement-neutral, and the port's established practice (cf. the header of
    `RepTheory/LocalLanglands/IntegralSubgroup.lean`). Measured: 9 s wall / 5 s user for the
    whole module, against >100 s with the umbrella. The tactics used here (`rw`, `simp`,
    `split_ifs`, `fin_cases`, `ext`, `ring`) come from the port closure, as in neighbouring
    modules, so no `Mathlib.Tactic` umbrella is imported either.
  - **`zero_le'` → `zero_le`** (two sites in `max_finEntryValuation_ne_zero`, pin `:68` and `:69`).
    `zero_le'` is deprecated at mathlib `v4.34`, and the silence gate fails on a warning. The
    replacement is the non-deprecated spelling of the same lemma, so the body's meaning is
    unchanged; this is FR-0250 (a)'s drift class, the only instance of it here.
  - **No other body-level substitution.** No `haveI`, no rewrite through a `def`-abbreviation such
    as `Matrix.SpecialLinearGroup`/`GLPos` (FR-0238/FR-0245), no `set`-naming of an unfolded
    abbreviation: the remaining bodies are the pin's character for character, including the
    `Valuation.map_mul` / `max_mul_mul_left` / `Matrix.det_smul` / `WithZero.log_mul` rewrite chain
    of `iwasawaShellIndex_centralScalar_mul` and the `Matrix.det_fin_two_of` computation of
    `iwasawaShellIndex_unipotentGL2_mul`. Note that `iwasawaShellIndex_eq_zero_iff'` is proved by
    the pin's one line `exact iwasawaShellIndex_eq_zero_iff v g`, which is a definitional
    identification (`finEntryValuation`/`finDetValuation` are `def`s, and `rfl`-equal to their
    bodies) and needs no `change`.
  - **Sections, not the pin's single `section Lemmas`.** The scaffold declares each item in its own
    `section` with the pin's `variable` lines; the elaborated types — hence the statement hashes —
    are identical, and `check_port` reads 23/23 `ok`. The pin's `variable` order is preserved.

  ## Deferred pin surface

  None. `move_dead.py --dry-run` reports **0 declarations, 0 lines**, and the pin's 23 declarations
  are all declared here (`scaffold_audit` reads `complete`: 23 pin publics / 23 port declarations,
  0 satisfied by the import closure). The pin's `section Lemmas` carries nothing else.

  ## Gates

  - `lake env lean -DautoImplicit=false` — exit 0, **no output at all** (0 bytes: `sorry`-free, no
    linter warning, no deprecation); 448 lines, 23 declarations, 9 s wall / 5 s user for the module.
  - `lake build FLTForHuman.AutomorphicForm.Adelic.IwasawaShellIndex` under the build lock — green
    (5 s to build the module).
  - `spec/check_port.py --force` — **23 ok, 0 mismatch, 0 missing, 0 own, 0 kw** (corpus `aa2d8b3`).
  - `tools/deps/scaffold_audit.py` — **complete**: 23 pin public declarations on the wire, 23 port
    declarations, 0 satisfied by the import closure.
  - `#print axioms` on `iwasawaShellIndex_eq_zero_iff`, `max_finEntryValuation_ne_zero`,
    `finDetValuation_eq`, `iwasawaShellIndex_centralScalar_mul`,
    `iwasawaShellIndex_unipotentGL2_mul`, `iwasawaShellIndex_heckeGen_mul` and
    `iwasawaShellIndex_heckeGen_mul_of_ne` — `[propext, Classical.choice, Quot.sound]`, no
    `sorryAx` (probe: `lean/tmp/af96/AF96G-axioms.lean`).
  - `dedup.py --within --module IwasawaShellIndex` — 23 declarations, **0 duplicate clusters**,
    0 removable lines. `move_dead.py --source … --target /dev/null --dry-run` — **0 declarations,
    0 lines**.
  - **Heartbeat probe pair (measured, never installed, FR-0225):** silent at
    `-DmaxHeartbeats=5000`, first failure at `2500` — `(deterministic) timeout at whnf` inside
    `iwasawaShellIndex_centralScalar_mul`, the `Matrix.det_smul`/`max_mul_mul_left` chain with the
    `Fintype.card_fin` cast. That is the heaviest declaration of the module; the Hecke lemmas cost
    less. The project cap is 4,000,000, so there is no build risk. **No `set_option maxHeartbeats`
    is carried in the file**: a probe is a measurement, a floor is a defect marker (FR-0225).
-/

import Mathlib.Algebra.GroupWithZero.WithZero
import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import FLTForHuman.AutomorphicForm.Adelic.Basic
import FLTForHuman.AutomorphicForm.Adelic.ConstantTerm
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.NumberTheory.AdelicHaar.GeneralLinear

set_option autoImplicit false

noncomputable section

open NumberField NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace AutomorphicForm


section
variable (K : Type*) [Field K] [NumberField K]

def finEntryValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) (i j : Fin 2) :
    WithZero (Multiplicative ℤ) :=
  Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v)

end

section
variable (K : Type*) [Field K] [NumberField K]

def finDetValuation (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : WithZero (Multiplicative ℤ) :=
  Valued.v (((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K).2 v)

end

section
variable (K : Type*) [Field K] [NumberField K]

def iwasawaShellIndex (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K) : ℤ :=
  2 * WithZero.log (max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) -
    WithZero.log (finDetValuation K v g)

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

def adeleEvalFin : AdeleRing (𝓞 K) K →+* v.adicCompletion K :=
  (finAdeleEval (𝓞 K) K v).comp (adeleFin (𝓞 K) K)

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem adeleEvalFin_apply (x : AdeleRing (𝓞 K) K) : adeleEvalFin v x = x.2 v := rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

def localMatrix : Matrix (Fin 2) (Fin 2) (v.adicCompletion K) :=
  (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).map (adeleEvalFin v)

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem localMatrix_apply (i j : Fin 2) :
    localMatrix v g i j = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) i j).2 v := rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem localMatrix_mul (h : AdelicGL2 (𝓞 K) K) : localMatrix v (g * h) = localMatrix v g * localMatrix v h := by
  rw [localMatrix, Matrix.GeneralLinearGroup.coe_mul, Matrix.map_mul]; rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem finEntryValuation_eq (i j : Fin 2) : finEntryValuation K v g i j = Valued.v (localMatrix v g i j) := rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem finDetValuation_eq : finDetValuation K v g = Valued.v (localMatrix v g).det := by
  rw [finDetValuation, Matrix.GeneralLinearGroup.val_det_apply]
  show Valued.v (adeleEvalFin v (g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)).det) = _
  rw [RingHom.map_det]
  rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem det_localMatrix_ne_zero : (localMatrix v g).det ≠ 0 := by
  have h : (localMatrix v g).det = adeleEvalFin v ((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) :
      AdeleRing (𝓞 K) K) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]; rfl
  rw [h]
  exact (Units.map (adeleEvalFin v : AdeleRing (𝓞 K) K →+* v.adicCompletion K).toMonoidHom
    (Matrix.GeneralLinearGroup.det g)).ne_zero

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem finDetValuation_ne_zero : finDetValuation K v g ≠ 0 := by
  rw [finDetValuation_eq, Valuation.ne_zero_iff]; exact det_localMatrix_ne_zero v g

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem max_finEntryValuation_ne_zero :
    max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1) ≠ 0 := by
  intro h
  have h0 : finEntryValuation K v g 1 0 = 0 := le_antisymm (le_of_max_le_left h.le) zero_le
  have h1 : finEntryValuation K v g 1 1 = 0 := le_antisymm (le_of_max_le_right h.le) zero_le
  rw [finEntryValuation_eq, Valuation.zero_iff] at h0 h1
  apply det_localMatrix_ne_zero v g
  rw [Matrix.det_fin_two, h0, h1]; ring

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_eq_zero_iff :
    iwasawaShellIndex K v g = 0 ↔
      finDetValuation K v g = (max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) ^ 2 := by
  have hM := max_finEntryValuation_ne_zero v g
  have hD := finDetValuation_ne_zero v g
  rw [iwasawaShellIndex, sub_eq_zero]
  constructor
  · intro h
    have h' : WithZero.log (finDetValuation K v g) =
        WithZero.log ((max (finEntryValuation K v g 1 0) (finEntryValuation K v g 1 1)) ^ 2) := by
      rw [WithZero.log_pow, ← h]; simp [two_mul]
    rw [← WithZero.exp_log hD, ← WithZero.exp_log (pow_ne_zero 2 hM), h']
  · intro h
    rw [h, WithZero.log_pow]; simp [two_mul]

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_eq_zero_iff' :
    iwasawaShellIndex K v g = 0 ↔
      Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
        (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
             (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2 :=
  iwasawaShellIndex_eq_zero_iff v g

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_eq :
    iwasawaShellIndex K v g =
      2 * WithZero.log (max (Valued.v (localMatrix v g 1 0)) (Valued.v (localMatrix v g 1 1))) -
        WithZero.log (Valued.v (localMatrix v g).det) := by
  rw [iwasawaShellIndex, finDetValuation_eq]; rfl

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_eq_of_localMatrix (g' : AdelicGL2 (𝓞 K) K) (a : v.adicCompletion K) (ha : a ≠ 0)
    (hrow : ∀ j : Fin 2, localMatrix v g' 1 j = localMatrix v g 1 j)
    (hdet : (localMatrix v g').det = a * (localMatrix v g).det) :
    iwasawaShellIndex K v g' = iwasawaShellIndex K v g - WithZero.log (Valued.v a) := by
  rw [iwasawaShellIndex_eq, iwasawaShellIndex_eq, hrow 0, hrow 1, hdet, Valuation.map_mul,
    WithZero.log_mul ((Valuation.ne_zero_iff _).mpr ha)
      ((Valuation.ne_zero_iff _).mpr (det_localMatrix_ne_zero v g))]
  ring

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_centralScalar_mul (u : (AdeleRing (𝓞 K) K)ˣ) :
    iwasawaShellIndex K v (centralScalar (𝓞 K) K u * g) = iwasawaShellIndex K v g := by
  set uv : v.adicCompletion K := adeleEvalFin v (u : AdeleRing (𝓞 K) K) with huv_def
  have huv : uv ≠ 0 := (Units.map (adeleEvalFin v : AdeleRing (𝓞 K) K →+* v.adicCompletion K).toMonoidHom u).ne_zero
  have hloc : localMatrix v (centralScalar (𝓞 K) K u * g) = uv • localMatrix v g := by
    rw [localMatrix_mul]
    have : localMatrix v (centralScalar (𝓞 K) K u) = Matrix.scalar (Fin 2) uv := by
      ext i j
      rw [localMatrix, centralScalar,
        show ((Matrix.GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
          Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) = Matrix.scalar (Fin 2) (u : AdeleRing (𝓞 K) K) from rfl,
        Matrix.scalar_apply, Matrix.scalar_apply, Matrix.map_apply, Matrix.diagonal_apply, Matrix.diagonal_apply]
      split_ifs <;> simp [huv_def]
    rw [this, Matrix.scalar_apply, ← Matrix.smul_eq_diagonal_mul]
  have hvu : Valued.v uv ≠ 0 := (Valuation.ne_zero_iff _).mpr huv
  rw [iwasawaShellIndex_eq, iwasawaShellIndex_eq, hloc, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul,
    smul_eq_mul, Valuation.map_mul, Valuation.map_mul, max_mul_mul_left, Matrix.det_smul, Fintype.card_fin,
    Valuation.map_mul, Valuation.map_pow,
    WithZero.log_mul hvu ((finEntryValuation_eq v g 1 0) ▸ (finEntryValuation_eq v g 1 1) ▸
      max_finEntryValuation_ne_zero v g),
    WithZero.log_mul (pow_ne_zero 2 hvu) ((Valuation.ne_zero_iff _).mpr (det_localMatrix_ne_zero v g)),
    WithZero.log_pow]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  ring

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_unipotentGL2_mul (x : AdeleRing (𝓞 K) K) :
    iwasawaShellIndex K v (unipotentGL2 x * g) = iwasawaShellIndex K v g := by
  have hloc : localMatrix v (unipotentGL2 x) = !![1, adeleEvalFin v x; 0, 1] := by
    ext i j
    rw [localMatrix, Matrix.map_apply, unipotentGL2_coe]
    fin_cases i <;> fin_cases j <;> simp
  have h := iwasawaShellIndex_eq_of_localMatrix v g (unipotentGL2 x * g) 1 one_ne_zero
    (fun j => by
      rw [localMatrix_mul, hloc, Matrix.mul_apply, Fin.sum_univ_two]
      simp)
    (by rw [localMatrix_mul, hloc, Matrix.det_mul, Matrix.det_fin_two_of]; ring)
  rw [h, Valuation.map_one, WithZero.log_one, sub_zero]

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem localMatrix_heckeGen_self :
    localMatrix v (heckeGen (𝓞 K) K v) =
      Matrix.diagonal ![((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K), 1] := by
  ext i j
  rw [localMatrix_apply, heckeGen, heckeGenAt_snd_apply_self]

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem localMatrix_heckeGen_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : v ≠ w) :
    localMatrix v (heckeGen (𝓞 K) K w) = 1 := by
  ext i j
  rw [localMatrix_apply, heckeGen, heckeGenAt_snd_apply_of_ne _ hw]

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_heckeGen_mul :
    iwasawaShellIndex K v (heckeGen (𝓞 K) K v * g) = iwasawaShellIndex K v g + 1 := by
  have hϖ : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := Units.ne_zero _
  have h := iwasawaShellIndex_eq_of_localMatrix v g (heckeGen (𝓞 K) K v * g) _ hϖ
    (fun j => by
      rw [localMatrix_mul, localMatrix_heckeGen_self, Matrix.diagonal_mul]
      simp)
    (by rw [localMatrix_mul, localMatrix_heckeGen_self, Matrix.det_mul, Matrix.det_diagonal]; simp)
  rw [h, valued_uniformizerUnit, WithZero.log_exp]
  ring

end

section
variable (K : Type*) [Field K] [NumberField K]
variable {K}
variable (v : HeightOneSpectrum (𝓞 K)) (g : AdelicGL2 (𝓞 K) K)

theorem iwasawaShellIndex_heckeGen_mul_of_ne {w : HeightOneSpectrum (𝓞 K)} (hw : v ≠ w) :
    iwasawaShellIndex K v (heckeGen (𝓞 K) K w * g) = iwasawaShellIndex K v g := by
  have h := iwasawaShellIndex_eq_of_localMatrix v g (heckeGen (𝓞 K) K w * g) 1 one_ne_zero
    (fun j => by rw [localMatrix_mul, localMatrix_heckeGen_of_ne v hw, one_mul])
    (by rw [localMatrix_mul, localMatrix_heckeGen_of_ne v hw, one_mul, one_mul])
  rw [h, Valuation.map_one, WithZero.log_one, sub_zero]

end

end AutomorphicForm

end
