/-
  The unramified Whittaker function on the Hecke shell.

  Two statements about the local component of a Whittaker function `W` at a finite place `v` that is
  an eigenfunction of the unramified Hecke operator, of the central character, and of the unipotent
  character `ψv`:

  * `mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero`: on the shell where the `v`-component of
    `g` has its determinant valuation equal to twice the valuation of its bottom row, the value of
    `W` at `heckeGen ^ m * g` times the (conjugated) value of a second such `W'` is the product
    `heckeRecursionSeq N λ ω m * heckeRecursionSeq N (conj λ') (conj ω') m` times `W g * conj (W' g)`;
    and `W` vanishes at `heckeGen⁻¹ ^ m * g` for `m > 0` (the shell's negative half is zero).
  * `exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero`: if `W` is a nonzero eigenfunction of the
    unramified Hecke and central operators at every place outside a finite `S`, of the unipotent
    character there, and of the level-one congruence subgroup away from `S`, then `W` does not vanish
    at `diagOne a₀ * g₀` for a `g₀` that is the identity away from `S` and a unit `a₀` that is `1`
    away from `S`.

  The local dictionary (`heckeRecursionSeq`, `torusFactor`, `placeEmbed`, `diagZ`, `unipotent`,
  `repSome`, `repInf`, `scalarPi`) is `RepTheory/LocalLanglands/UnramifiedWhittaker.lean`; the
  recursion identity for the diagonal `placeEmbed v * diagZ π m` is the row of
  `RepTheory/LocalLanglands/WhittakerRecursion.lean`, which both statements consume.

  Transcribed from the two `S_` files below (pinned `aa2d8b3`, 646 + 618 lines). The two pins are
  flattened files: their engine declarations are all public, in the pins' search-stage namespaces,
  which the port renames to subject names (`UnramW17` -> `Shell`, `C8P1` -> `DiagOne`).

  ## The surface: 85 declarations, all public

  The checker line is `84 ok, 0 mismatch, 0 missing, 1 own, 0 kw` over a wire of **85 pin public
  declarations**, and `scaffold_audit.py` reads `complete`. Two of the wire's 85 are the pins'
  `solution` wrappers, which the audit reports as `FOLDED`: their statements *are* the two rows, so
  the module's 85 declarations are the wire's 83 non-`solution` publics plus those two rows. The
  audit counts 82 port declarations rather than 85 because the two pins declare three names twice
  (`cpt`, `cpt_apply`, `swapGL`); each copy is declared once, in its own namespace, and diffed
  against its own pin. Every engine declaration is **public**, because the pins are flattened files
  with no `private` one: 78 `theorem`s and 7 `def`s, 0 `private`.

  Nothing is renamed beyond the namespace segment, and nothing is dropped: the two files' helper
  sets are disjoint, so both are transcribed in full. The one declaration on an `own:` marker is
  `DiagOne.finComponent_prod_localEmbed`, whose pin states it by equation clauses
  (`| [], _ =>` / `| a :: l, hl =>`): with no top-level `:=` the statement checker cannot find the
  cut and records the whole proof body as the statement, so the port's signature-identical copy
  cannot be diffed and the `own:` row carries the reason.

  ## Proof and body drift under mathlib v4.34 / Lean v4.34, all statement-preserving

  * `conj_heckeRecursionSeq`: the pin's `suffices`/`Nat`-induction proof is replaced by
    `EulerFactor.conj_heckeRecursionSeq` (`WhittakerRecursion.lean`) at `(N : ℂ)` plus
    `Complex.conj_natCast` — the general `(N lam om : ℂ)` form the port already carries. The pin's
    `(N : ℕ)` variant is kept at the pin's statement, so both exist.
  * `if_pos` / `if_neg` -> `ite_eq_left` / `ite_eq_right` (8 sites: 6 in `finComponent_prod_localEmbed`,
    2 in `exists_apply_ne_zero_cpt_eq_one_off_finset`), deprecated in this toolchain since 2026-07-21.
  * `zero_le'` -> `zero_le` (4 sites: 2 in `local_iwasawa_of_le`, 2 in `exists_mul_upper`).
  * `torusFactor_zero`: the pin's `simp [torusFactor, heckeRecursionSeq]` is `simp [torusFactor]`;
    `linter.style` reports the unfolding argument unused (it is found through the `torusFactor`
    definition).
  * The pin's `attribute [-ext] IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext` wall is
    dropped (the port's recorded practice); both `ext` uses in `ext_of_glArch_of_cpt` close as the
    pin writes them, so nothing needed re-spelling.

  ## Heartbeat probe (recorded, not installed)

  `lake env lean -DautoImplicit=false -DmaxHeartbeats=N` on this file: **silent at `N = 20000`,
  fails at `N = 10000`** (and already at 15000 — the first abort is in `local_iwasawa_of_le`), so
  the module's floor is between 15000 and 20000, an order of magnitude under the edit loop's
  200000 cap. No `set_option maxHeartbeats` in the file.

  spec-pin: P2M/Sol/S_UnramifiedWhittaker_mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero.lean
  spec-pin: P2M/Sol/S_UnramifiedWhittaker_exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero.lean
-/
import FLTForHuman.RepTheory.LocalLanglands.UnramifiedWhittaker
import FLTForHuman.RepTheory.LocalLanglands.WhittakerRecursion
import FLTForHuman.NumberTheory.AdelicLevel.Level
import FLTForHuman.NumberTheory.AdelicLevel.HeckeGen
import FLTForHuman.AutomorphicForm.Adelic.SmoothAutomorphicFn

set_option autoImplicit false

noncomputable section

open Matrix
open IsDedekindDomain NumberField NumberField.AdelicLevel AdelicDock UnramifiedWhittaker
open AutomorphicForm

namespace UnramifiedWhittaker

namespace Shell

theorem conj_heckeRecursionSeq (N : ℕ) (lam om : ℂ) (m : ℕ) :
    (starRingEnd ℂ) (heckeRecursionSeq (N : ℂ) lam om m) =
      heckeRecursionSeq (N : ℂ) ((starRingEnd ℂ) lam) ((starRingEnd ℂ) om) m := by
  rw [EulerFactor.conj_heckeRecursionSeq, Complex.conj_natCast]


theorem torusFactor_natCast (N lam om : ℂ) (m : ℕ) :
    torusFactor N lam om (m : ℤ) = heckeRecursionSeq N lam om m := by
  simp [torusFactor]


theorem torusFactor_neg (N lam om : ℂ) {m : ℤ} (hm : m < 0) : torusFactor N lam om m = 0 := by
  simp [torusFactor, not_le.mpr hm]


section Matrices

variable {F : Type*} [Field F]

theorem diagZ_add (π : F) (hπ : π ≠ 0) (a b : ℤ) :
    diagZ π hπ (a + b) = diagZ π hπ a * diagZ π hπ b := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, Matrix.mul_apply, Fin.sum_univ_two, zpow_add₀ hπ]


theorem diagZ_zero' (π : F) (hπ : π ≠ 0) : diagZ π hπ 0 = 1 := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [diagZ]


theorem diagZ_one_pow (π : F) (hπ : π ≠ 0) (m : ℕ) : diagZ π hπ 1 ^ m = diagZ π hπ (m : ℤ) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, diagZ_zero']
  | succ m ih => rw [pow_succ, ih, ← diagZ_add]; push_cast; rfl


theorem diagZ_one_inv (π : F) (hπ : π ≠ 0) : (diagZ π hπ 1)⁻¹ = diagZ π hπ (-1) := by
  rw [inv_eq_iff_mul_eq_one, ← diagZ_add, show (1 : ℤ) + -1 = 0 by norm_num, diagZ_zero']


theorem diagZ_one_inv_pow (π : F) (hπ : π ≠ 0) (m : ℕ) :
    (diagZ π hπ 1)⁻¹ ^ m = diagZ π hπ (-(m : ℤ)) := by
  rw [diagZ_one_inv]
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, neg_zero, diagZ_zero']
  | succ m ih =>
    rw [pow_succ, ih, ← diagZ_add]
    congr 1
    push_cast
    ring


def scalarHom : Fˣ →* GL (Fin 2) F := Units.map (Matrix.scalar (Fin 2) : F →+* _).toMonoidHom


theorem scalarHom_coe_apply (t : Fˣ) (i j : Fin 2) :
    ((scalarHom t : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = if i = j then (t : F) else 0 := by
  show (Matrix.scalar (Fin 2) (t : F)) i j = _
  rw [Matrix.scalar_apply, Matrix.diagonal_apply]


theorem scalarPi_eq_scalarHom (π : F) (hπ : π ≠ 0) : scalarPi π hπ = scalarHom (Units.mk0 π hπ) := by
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [scalarHom_coe_apply]
  fin_cases i <;> fin_cases j <;> simp [scalarPi]


theorem scalarHom_commute (t : Fˣ) (g : GL (Fin 2) F) : scalarHom t * g = g * scalarHom t := by
  refine Units.ext ?_
  simp only [Units.val_mul]
  exact (Matrix.scalar_commute (t : F) (fun r' => Commute.all _ _) (g : Matrix (Fin 2) (Fin 2) F)).eq


theorem unipotent_coe_apply (x : F) (i j : Fin 2) :
    ((unipotent x : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = !![1, x; 0, 1] i j := rfl


theorem diagZ_coe_apply (π : F) (hπ : π ≠ 0) (m : ℤ) (i j : Fin 2) :
    ((diagZ π hπ m : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) i j = !![π ^ m, 0; 0, 1] i j := rfl


end Matrices

end Shell

namespace Shell

section Local

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_map_eq_of_integral (g : GL (Fin 2) (v.adicCompletion K))
    (hint : ∀ i j, (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K)
    (hdet : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k = g := by
  let M : Matrix (Fin 2) (Fin 2) (v.adicCompletionIntegers K) := Matrix.of fun i j => ⟨_, hint i j⟩
  have hM : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).mapMatrix M =
      (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    ext i j; rfl
  have hdetM : (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) M.det =
      Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [RingHom.map_det, hM]
  have hunit : IsUnit M.det := by
    rw [HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
    show Valued.v ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) M.det) = 1
    rw [hdetM, hdet]
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hunit, ?_⟩
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [Matrix.GeneralLinearGroup.map_apply]
  rfl


theorem exists_map_eq_unipotent (r : v.adicCompletionIntegers K) :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k =
        unipotent (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) := by
  refine exists_map_eq_of_integral K v _ (fun i j => ?_) ?_
  · rw [unipotent_coe_apply]
    fin_cases i <;> fin_cases j
    · exact one_mem _
    · exact r.2
    · exact zero_mem _
    · exact one_mem _
  · have : Matrix.det ((unipotent (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) :
        GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = 1 := by
      show Matrix.det !![(1 : v.adicCompletion K), _; 0, 1] = 1
      rw [Matrix.det_fin_two_of]; ring
    rw [this, map_one]


def swapGL : GL (Fin 2) (v.adicCompletion K) :=
  GeneralLinearGroup.mkOfDetNeZero !![(0 : v.adicCompletion K), 1; 1, 0]
    (by rw [Matrix.det_fin_two_of]; simp)


theorem swapGL_coe_apply (i j : Fin 2) :
    ((swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      !![(0 : v.adicCompletion K), 1; 1, 0] i j := rfl


theorem exists_map_eq_swapGL :
    ∃ k : GL (Fin 2) (v.adicCompletionIntegers K),
      Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k =
        swapGL K v := by
  refine exists_map_eq_of_integral K v _ (fun i j => ?_) ?_
  · rw [swapGL_coe_apply]
    fin_cases i <;> fin_cases j
    · exact zero_mem _
    · exact one_mem _
    · exact one_mem _
    · exact zero_mem _
  · show Valued.v (Matrix.det !![(0 : v.adicCompletion K), 1; 1, 0]) = 1
    rw [Matrix.det_fin_two_of]
    simp


theorem local_iwasawa_of_le (π : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2)
    (hle : Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0) ≤
      Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)) :
    ∃ (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K)),
      g = unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
        Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k := by
  set a := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0 with ha
  set b := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 1 with hb
  set c := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 with hc
  set d := (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 with hd
  rw [max_eq_right hle] at hg
  have hdetg : Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = a * d - b * c :=
    Matrix.det_fin_two _
  have hdet0 : Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) ≠ 0 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det g).ne_zero
  have hd0 : d ≠ 0 := by
    intro h0
    have h : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 0 := by
      rw [hg, h0, map_zero, zero_pow two_ne_zero]
    exact hdet0 ((Valuation.zero_iff Valued.v).mp h)
  have hvd0 : Valued.v d ≠ 0 := (Valuation.ne_zero_iff _).mpr hd0
  set n : ℤ := WithZero.log (Valued.v d) with hn
  have hvd : Valued.v d = WithZero.exp n := (WithZero.exp_log hvd0).symm
  set s : v.adicCompletion K := (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) ^ (-n) with hs
  have hvs : Valued.v s = WithZero.exp n := by
    rw [hs, map_zpow₀, hπv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg]
  have hs0 : s ≠ 0 := by rw [hs]; exact zpow_ne_zero _ hπ
  have hvs0 : Valued.v s ≠ 0 := (Valuation.ne_zero_iff _).mpr hs0

  set α : v.adicCompletion K := (a - b / d * c) / s with hα
  have hαds : α * d * s = Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
    rw [hdetg, hα]; field_simp
  have hvα : Valued.v α = 1 := by
    have h := congrArg Valued.v hαds
    rw [map_mul, map_mul, hg, hvd, hvs, sq] at h
    have hn0 : WithZero.exp n ≠ 0 := WithZero.exp_ne_zero
    calc Valued.v α = Valued.v α * WithZero.exp n * WithZero.exp n / (WithZero.exp n * WithZero.exp n) := by
          field_simp
      _ = 1 := by rw [h]; field_simp
  have hα0 : α ≠ 0 := fun h => by rw [h, map_zero] at hvα; exact zero_ne_one hvα
  have hkdet : Matrix.det !![α, 0; c / s, d / s] ≠ 0 := by
    rw [Matrix.det_fin_two_of]
    simp only [zero_mul, sub_zero]
    exact mul_ne_zero hα0 (div_ne_zero hd0 hs0)
  set kF : GL (Fin 2) (v.adicCompletion K) := GeneralLinearGroup.mkOfDetNeZero _ hkdet with hkF
  have hkFij : ∀ i j, (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = !![α, 0; c / s, d / s] i j :=
    fun i j => rfl
  have hint : ∀ i j, (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j ∈ v.adicCompletionIntegers K := by
    intro i j
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, hkFij]
    fin_cases i <;> fin_cases j
    · show Valued.v α ≤ 1
      rw [hvα]
    · show Valued.v (0 : v.adicCompletion K) ≤ 1
      rw [map_zero]; exact zero_le
    · show Valued.v (c / s) ≤ 1
      rw [map_div₀, hvs, ← hvd]
      exact div_le_one_of_le₀ hle zero_le
    · show Valued.v (d / s) ≤ 1
      rw [map_div₀, hvs, hvd, div_self WithZero.exp_ne_zero]
  have hkdet1 : Valued.v (Matrix.det (kF : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) = 1 := by
    show Valued.v (Matrix.det !![α, 0; c / s, d / s]) = 1
    rw [Matrix.det_fin_two_of]
    simp only [zero_mul, sub_zero]
    rw [map_mul, hvα, map_div₀, hvs, hvd, div_self WithZero.exp_ne_zero, one_mul]
  obtain ⟨k, hk⟩ := exists_map_eq_of_integral K v kF hint hkdet1
  refine ⟨b / d, -n, k, ?_⟩
  rw [hk]
  have hS : ∀ i j, ((scalarHom (Units.mk0 _ hπ ^ (-n)) : GL (Fin 2) (v.adicCompletion K)) :
      Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j = if i = j then s else 0 := by
    intro i j
    rw [scalarHom_coe_apply, Units.val_zpow_eq_zpow_val, Units.val_mk0]
  refine GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply,
    Fin.sum_univ_two, Fin.sum_univ_two]
  simp only [unipotent_coe_apply, hS, hkFij, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  fin_cases i <;> fin_cases j
  · show a = _
    simp
    rw [hα]; field_simp; ring
  · show b = _
    simp; field_simp
  · show c = _
    simp; field_simp
  · show d = _
    simp; field_simp


end Local

end Shell

namespace Shell

section Local2

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem local_iwasawa (π : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) =
      WithZero.exp (-1 : ℤ))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : Valued.v (Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2) :
    ∃ (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K)),
      g = unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
        Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k := by
  rcases le_or_gt (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
      (Valued.v ((g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1)) with hle | hlt
  · exact local_iwasawa_of_le K v π hπ hπv g hg hle
  · obtain ⟨w, hw⟩ := exists_map_eq_swapGL K v
    have h10 : ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, swapGL_coe_apply, swapGL_coe_apply]
      simp
    have h11 : ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1 =
        (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0 := by
      rw [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, swapGL_coe_apply, swapGL_coe_apply]
      simp
    have hdet : Matrix.det ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = -Matrix.det (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) := by
      rw [Units.val_mul, Matrix.det_mul]
      show _ * Matrix.det !![(0 : v.adicCompletion K), 1; 1, 0] = _
      rw [Matrix.det_fin_two_of]; ring
    have hg₂ : Valued.v (Matrix.det ((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
        (max (Valued.v (((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
          (Valued.v (((g * swapGL K v : GL (Fin 2) (v.adicCompletion K)) :
          Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2 := by
      rw [hdet, Valuation.map_neg, h10, h11, max_comm]; exact hg
    obtain ⟨x, j, k, hk⟩ := local_iwasawa_of_le K v π hπ hπv _ hg₂ (by rw [h10, h11]; exact hlt.le)
    refine ⟨x, j, k * w⁻¹, ?_⟩
    rw [map_mul, map_inv, hw, ← mul_assoc, ← hk, mul_inv_cancel_right]


end Local2

theorem norm_addChar_apply_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (y : v.adicCompletion K) : ‖ψ y‖ = 1 := by
  obtain ⟨b, hb0, hb⟩ :=
    HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers (K := K) v y
  set N : ℕ := Ideal.absNorm (Ideal.span {b}) with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero hb0
  have hNmem : (N : 𝓞 K) ∈ Ideal.span {b} := Ideal.absNorm_mem _
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hNmem
  have hmem : (N : v.adicCompletion K) * y ∈ v.adicCompletionIntegers K := by
    have e : (N : v.adicCompletion K) =
        algebraMap (𝓞 K) (v.adicCompletion K) b * algebraMap (𝓞 K) (v.adicCompletion K) r := by
      rw [← map_mul, mul_comm, hr, map_natCast]
    rw [e, mul_comm, ← mul_assoc]
    exact mul_mem hb (HeightOneSpectrum.coe_mem_adicCompletionIntegers v r)
  have h1 : ψ y ^ N = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
    exact hψ0 ⟨_, hmem⟩
  have h2 := congrArg norm h1
  rw [norm_pow, norm_one] at h2
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN0).mp h2


theorem addChar_mul_conj_eq_one (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψ : AddChar (v.adicCompletion K) ℂ)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (y : v.adicCompletion K) : ψ y * (starRingEnd ℂ) (ψ y) = 1 := by
  rw [Complex.mul_conj', norm_addChar_apply_eq_one K v ψ hψ0 y]
  simp


section Adelic

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

def cpt : GL (Fin 2) (AdeleRing R K) →* GL (Fin 2) (v.adicCompletion K) :=
  (finComponent R K v).comp (glFin R K)


theorem coe_cpt (h : GL (Fin 2) (AdeleRing R K)) :
    ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (finAdeleEval R K v).mapMatrix ((adeleFin R K).mapMatrix (h : Matrix (Fin 2) (Fin 2) (AdeleRing R K))) :=
  rfl


theorem cpt_apply (h : GL (Fin 2) (AdeleRing R K)) (i j : Fin 2) :
    ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) i j =
      ((h : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) i j).2 v :=
  rfl


theorem coe_placeEmbed (X : GL (Fin 2) (v.adicCompletion K)) :
    ((placeEmbed K v X : GL (Fin 2) (AdeleRing R K)) : Matrix (Fin 2) (Fin 2) (AdeleRing R K)) =
      finMat R K (localMat R K v (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) :=
  rfl


theorem cpt_placeEmbed (X : GL (Fin 2) (v.adicCompletion K)) : cpt K v (placeEmbed K v X) = X := by
  show finComponent R K v (glFin R K (finEmbed R K (localEmbed R K v X))) = X
  rw [glFin_finEmbed, finComponent_localEmbed_self]


theorem det_cpt (g : GL (Fin 2) (AdeleRing R K)) :
    Matrix.det ((cpt K v g : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      (((Matrix.GeneralLinearGroup.det g : (AdeleRing R K)ˣ) : AdeleRing R K)).2 v := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, coe_cpt, ← RingHom.map_det, ← RingHom.map_det]
  rfl


theorem placeEmbed_mul_eq_mul_of_commute (X : GL (Fin 2) (v.adicCompletion K)) (h : GL (Fin 2) (AdeleRing R K))
    (hc : (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) *
        ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) =
      ((cpt K v h : GL (Fin 2) (v.adicCompletion K)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) * X) :
    placeEmbed K v X * h = h * placeEmbed K v X := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_placeEmbed]
  refine matrix_eq_of_mapMatrix_arch_fin_eq R K ?_ ?_
  · rw [map_mul, map_mul, mapMatrix_arch_finMat, one_mul, mul_one]
  · rw [map_mul, map_mul, mapMatrix_fin_finMat]
    refine matrix_eq_of_forall_mapMatrix_finAdeleEval_eq R K fun w => ?_
    rw [map_mul, map_mul]
    by_cases hw : w = v
    · subst hw; rw [mapMatrix_localMat_self]; exact hc
    · rw [mapMatrix_localMat_of_ne R K v _ hw, one_mul, mul_one]


theorem mul_placeEmbed_comm_of_cpt_eq_one (h : GL (Fin 2) (AdeleRing R K)) (h1 : cpt K v h = 1)
    (X : GL (Fin 2) (v.adicCompletion K)) : h * placeEmbed K v X = placeEmbed K v X * h := by
  refine (placeEmbed_mul_eq_mul_of_commute K v X h ?_).symm
  rw [h1, Units.val_one, mul_one, one_mul]


theorem placeEmbed_scalarHom_mul_comm (t : (v.adicCompletion K)ˣ) (h : GL (Fin 2) (AdeleRing R K)) :
    placeEmbed K v (scalarHom t) * h = h * placeEmbed K v (scalarHom t) :=
  placeEmbed_mul_eq_mul_of_commute K v _ h
    (Matrix.scalar_commute (t : v.adicCompletion K) (fun _ => Commute.all _ _) _).eq


theorem cpt_inv_placeEmbed_cpt_mul (g : GL (Fin 2) (AdeleRing R K)) :
    cpt K v ((placeEmbed K v (cpt K v g))⁻¹ * g) = 1 := by
  rw [map_mul, map_inv, cpt_placeEmbed, inv_mul_cancel]


theorem valued_eq_of_placeEmbed_diagZ_eq_heckeGen (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen R K v) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) := by
  have h := congrArg (fun y => ((cpt K v y : GL (Fin 2) (v.adicCompletion K)) :
    Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 0 0) hgen
  rw [cpt_placeEmbed, diagZ_coe_apply, cpt_apply, heckeGen, heckeGenAt_snd_apply_self] at h
  simp at h
  rw [show (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ : v.adicCompletion K) =
    (uniformizerUnit K v : v.adicCompletion K) from h]
  exact valued_uniformizerUnit K v


end Adelic

end Shell

namespace Shell

theorem torusFactor_zero (N lam om : ℂ) : torusFactor N lam om 0 = 1 := by
  simp [torusFactor]


theorem diagZ_mul_unipotent' {F : Type*} [Field F] (π : F) (hπ : π ≠ 0) (m : ℤ) (x : F) :
    diagZ π hπ m * unipotent x = unipotent (π ^ m * x) * diagZ π hπ m := by
  refine GeneralLinearGroup.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [diagZ, unipotent, Matrix.mul_apply, Fin.sum_univ_two]


theorem unipotent_scalarHom_comm {F : Type*} [Field F] (x : F) (t : Fˣ) :
    scalarHom t * unipotent x = unipotent x * scalarHom t :=
  scalarHom_commute t _


section Key

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_central_value (W : GL (Fin 2) (AdeleRing R K) → ℂ) (ϖ : v.adicCompletion K) (hπ : ϖ ≠ 0)
    (om : ℂ) (hZ : ∀ g : GL (Fin 2) (AdeleRing R K), W (g * placeEmbed K v (scalarPi ϖ hπ)) = om * W g)
    (j : ℤ) :
    ∃ c : ℂ, ∀ h : GL (Fin 2) (AdeleRing R K),
      W (h * placeEmbed K v (scalarHom (Units.mk0 ϖ hπ ^ j))) = c * W h := by
  have hP : placeEmbed K v (scalarHom (Units.mk0 ϖ hπ ^ j)) = (placeEmbed K v (scalarPi ϖ hπ)) ^ j := by
    rw [map_zpow, ← scalarPi_eq_scalarHom, map_zpow]
  rw [hP]
  set P := placeEmbed K v (scalarPi ϖ hπ) with hPdef
  have hnat : ∀ (n : ℕ) (h : GL (Fin 2) (AdeleRing R K)), W (h * P ^ n) = om ^ n * W h := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih => intro h; rw [pow_succ, ← mul_assoc, hZ, ih, pow_succ]; ring
  by_cases hom : om = 0
  · refine ⟨0, fun h => ?_⟩
    have hW : ∀ g : GL (Fin 2) (AdeleRing R K), W g = 0 := fun g => by
      have e := hZ (g * P⁻¹)
      rw [inv_mul_cancel_right, hom, zero_mul] at e
      exact e
    rw [hW, hW, mul_zero]
  · refine ⟨om ^ j, fun h => ?_⟩
    rcases Int.eq_nat_or_neg j with ⟨n, rfl | rfl⟩
    · rw [zpow_natCast, zpow_natCast, hnat]
    · have e := hnat n (h * P ^ (-(n : ℤ)))
      rw [mul_assoc, ← zpow_natCast, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one] at e
      rw [_root_.zpow_neg om, zpow_natCast, e, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero n hom), one_mul]


theorem key_identity (W : GL (Fin 2) (AdeleRing R K) → ℂ) (ψ : AddChar (v.adicCompletion K) ℂ)
    (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0) (lam om : ℂ)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing R K)),
      W (placeEmbed K v (unipotent x) * g) = ψ x * W g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing R K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing R K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (x : v.adicCompletion K) (j : ℤ) (k : GL (Fin 2) (v.adicCompletionIntegers K))
    (g' : GL (Fin 2) (AdeleRing R K)) (hg' : cpt K v g' = 1) :
    ∃ c : ℂ, ∀ m : ℤ,
      W (placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ m) *
          (placeEmbed K v (unipotent x * scalarHom (Units.mk0 _ hπ ^ j) *
            Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k) * g')) =
        ψ ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ m * x) * c *
          (W g' * torusFactor (Fintype.card I) lam om m) := by
  obtain ⟨c, hc⟩ := exists_central_value K v W _ hπ om hZ j
  refine ⟨c, fun m => ?_⟩
  set ϖF := algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ with hϖF
  have hK' : ∀ (r : v.adicCompletionIntegers K) (g : GL (Fin 2) (AdeleRing R K)),
      W (g * placeEmbed K v (unipotent
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r))) = W g := by
    intro r g
    obtain ⟨kr, hkr⟩ := exists_map_eq_unipotent K v r
    rw [← hkr]
    exact hK kr g
  have hg'c : ∀ X : GL (Fin 2) (v.adicCompletion K), g' * placeEmbed K v X = placeEmbed K v X * g' :=
    mul_placeEmbed_comm_of_cpt_eq_one K v g' hg'

  have e1 : placeEmbed K v (diagZ ϖF hπ m) *
        (placeEmbed K v (unipotent x * scalarHom (Units.mk0 ϖF hπ ^ j) *
          Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k) * g') =
      placeEmbed K v (unipotent (ϖF ^ m * x)) *
        ((placeEmbed K v (diagZ ϖF hπ m) * g') * placeEmbed K v (scalarHom (Units.mk0 ϖF hπ ^ j)) *
          placeEmbed K v (Matrix.GeneralLinearGroup.map
            (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) k)) := by
    rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, diagZ_mul_unipotent', map_mul]
    simp only [mul_assoc]
    congr 2
    symm
    rw [← mul_assoc, hg'c, mul_assoc, hg'c]
  rw [e1, hN, hK, hc, ← hg'c,
    UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hK' hT hZ hg'c m]
  ring


end Key

end Shell

namespace DiagOne

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

noncomputable def cpt (v : HeightOneSpectrum (𝓞 F)) :
    GL (Fin 2) (AdeleRing (𝓞 F) F) →* GL (Fin 2) (v.adicCompletion F) :=
  (finComponent (𝓞 F) F v).comp (glFin (𝓞 F) F)

variable {F}

theorem cpt_apply (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (i j : Fin 2) :
    ((cpt F v g : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j
      = ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v := rfl

theorem placeEmbed_eq (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    placeEmbed F v x = finEmbed (𝓞 F) F (localEmbed (𝓞 F) F v x) := rfl

theorem cpt_finEmbed (v : HeightOneSpectrum (𝓞 F)) (k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) :
    cpt F v (finEmbed (𝓞 F) F k) = finComponent (𝓞 F) F v k := by
  show finComponent (𝓞 F) F v (glFin (𝓞 F) F (finEmbed (𝓞 F) F k)) = _
  rw [glFin_finEmbed]

@[scoped simp] theorem cpt_placeEmbed_self (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    cpt F v (placeEmbed F v x) = x := by
  rw [placeEmbed_eq, cpt_finEmbed, finComponent_localEmbed_self]

theorem cpt_placeEmbed_of_ne {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v)
    (x : GL (Fin 2) (v.adicCompletion F)) : cpt F w (placeEmbed F v x) = 1 := by
  rw [placeEmbed_eq, cpt_finEmbed, finComponent_localEmbed_of_ne (𝓞 F) F v x hw]

@[scoped simp] theorem glArch_placeEmbed (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin 2) (v.adicCompletion F)) :
    glArch (𝓞 F) F (placeEmbed F v x) = 1 := by
  rw [placeEmbed_eq, glArch_finEmbed]

theorem ext_of_glArch_of_cpt {g h : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (harch : glArch (𝓞 F) F g = glArch (𝓞 F) F h) (hfin : ∀ w, cpt F w g = cpt F w h) : g = h := by
  refine Matrix.GeneralLinearGroup.ext fun i j => Prod.ext ?_ ?_
  · have := congrArg
      (fun m : GL (Fin 2) (InfiniteAdeleRing F) => (m : Matrix (Fin 2) (Fin 2) (InfiniteAdeleRing F)) i j) harch
    simpa only [glArch_apply] using this
  · ext w : 1
    have := congrArg
      (fun m : GL (Fin 2) (w.adicCompletion F) => (m : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j)
      (hfin w)
    simpa only [cpt_apply] using this

theorem mul_placeEmbed_comm {v : HeightOneSpectrum (𝓞 F)} {g : GL (Fin 2) (AdeleRing (𝓞 F) F)}
    (hg : cpt F v g = 1) (x : GL (Fin 2) (v.adicCompletion F)) :
    g * placeEmbed F v x = placeEmbed F v x * g := by
  refine ext_of_glArch_of_cpt (by rw [map_mul, map_mul, glArch_placeEmbed, mul_one, one_mul]) fun w => ?_
  rw [map_mul, map_mul]
  by_cases hw : w = v
  · subst hw; rw [hg, one_mul, mul_one]
  · rw [cpt_placeEmbed_of_ne hw, one_mul, mul_one]

theorem one_entry_snd (w : HeightOneSpectrum (𝓞 F)) (i j : Fin 2) :
    ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w
      = (1 : Matrix (Fin 2) (Fin 2) (w.adicCompletion F)) i j := by
  rw [Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> rfl

theorem cpt_eq_one_iff (w : HeightOneSpectrum (𝓞 F)) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    cpt F w g = 1 ↔ ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w =
        ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w := by
  rw [Matrix.GeneralLinearGroup.ext_iff]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [cpt_apply, one_entry_snd, Units.val_one]

theorem mem_localLevelOne_top {v : HeightOneSpectrum (𝓞 F)} (k k' : GL (Fin 2) (v.adicCompletion F))
    (hkk' : k * k' = 1)
    (hk : ∀ i j, Valued.v ((k : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1)
    (hk' : ∀ i j, Valued.v ((k' : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) i j) ≤ 1) :
    k ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have aux : ∀ m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F), (∀ i j, Valued.v (m i j) ≤ 1) →
      IsLocalLevelOne (𝓞 F) F v ⊤ m := fun m hm =>
    { integral := fun i j => (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm i j)
      lowerLeft := by rw [idealBound_top]; exact hm 1 0
      lowerRight := by
        rw [idealBound_top, ← HeightOneSpectrum.mem_adicCompletionIntegers]
        exact sub_mem ((HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr (hm 1 1)) (one_mem _) }
  rw [mem_localLevelOne_iff, inv_eq_of_mul_eq_one_right hkk']
  exact ⟨aux _ hk, aux _ hk'⟩

theorem placeEmbed_mem_of_mem_localLevelOne {v : HeightOneSpectrum (𝓞 F)}
    {k : GL (Fin 2) (v.adicCompletion F)} (hk : k ∈ localLevelOne (𝓞 F) F v ⊤) :
    placeEmbed F v k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [placeEmbed_eq, finEmbed_mem_levelOne_iff, localEmbed_mem_finiteLevelOne_iff]; exact hk
  · rw [mem_finiteAdelicGL2Subgroup_iff, glArch_placeEmbed]

section W

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem apply_mul_placeEmbed_of_mem_localLevelOne
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) {k : GL (Fin 2) (v.adicCompletion F)}
    (hk : k ∈ localLevelOne (𝓞 F) F v ⊤) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    W (g * placeEmbed F v k) = W g :=
  hK _ (placeEmbed_mem_of_mem_localLevelOne hk)
    (fun w hw => (cpt_eq_one_iff w _).mp (cpt_placeEmbed_of_ne (fun h : w = v => hv (h ▸ hw)) k)) g

end W

end DiagOne

namespace DiagOne

open scoped Classical

variable {F : Type} [Field F] [NumberField F]

theorem isLocalLevelOne_top_of_forall_mem {v : HeightOneSpectrum (𝓞 F)}
    {m : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)}
    (hm : ∀ i j, m i j ∈ v.adicCompletionIntegers F) : IsLocalLevelOne (𝓞 F) F v ⊤ m where
  integral := hm
  lowerLeft := by
    rw [idealBound_top]; exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (hm 1 0)
  lowerRight := by
    rw [idealBound_top, ← HeightOneSpectrum.mem_adicCompletionIntegers]
    exact sub_mem (hm 1 1) (one_mem _)

theorem eventually_cpt_mem (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) :
    ∀ᶠ w in Filter.cofinite, cpt F w g ∈ localLevelOne (𝓞 F) F w ⊤ := by
  have h1 : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j : Fin 2,
      ((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w ∈ w.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2).property
  have h2 : ∀ᶠ w : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j : Fin 2,
      (((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 w
        ∈ w.adicCompletionIntegers F :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      ((((g⁻¹ : GL (Fin 2) (AdeleRing (𝓞 F) F)) : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2).property
  filter_upwards [h1, h2] with w hw1 hw2
  rw [mem_localLevelOne_iff, ← map_inv]
  exact ⟨isLocalLevelOne_top_of_forall_mem fun i j => hw1 i j,
    isLocalLevelOne_top_of_forall_mem fun i j => hw2 i j⟩

theorem mem_finiteLevelOne_of_forall_finComponent {N : Ideal (𝓞 F)}
    {k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)}
    (hk : ∀ w, finComponent (𝓞 F) F w k ∈ localLevelOne (𝓞 F) F w N) :
    k ∈ finiteLevelOne (𝓞 F) F N := by
  have aux : ∀ m : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F),
      (∀ w, IsLocalLevelOne (𝓞 F) F w N
        ((finComponent (𝓞 F) F w m : GL (Fin 2) (w.adicCompletion F)) : Matrix _ _ _)) →
      IsLevelOneMatrix (𝓞 F) F N (m : Matrix _ _ _) := fun m hm =>
    { integral := fun i j w => (hm w).integral i j
      lowerLeft := fun w => (hm w).lowerLeft
      lowerRight := fun w => by
        rw [coe_sub_apply, coe_one_apply]; exact (hm w).lowerRight }
  rw [mem_finiteLevelOne_iff]
  refine ⟨aux k fun w => ((mem_localLevelOne_iff _ _ _ _).mp (hk w)).1,
    aux k⁻¹ fun w => ?_⟩
  rw [map_inv]
  exact ((mem_localLevelOne_iff _ _ _ _).mp (hk w)).2

theorem finComponent_prod_localEmbed (c : ∀ w : HeightOneSpectrum (𝓞 F), GL (Fin 2) (w.adicCompletion F))
    (w : HeightOneSpectrum (𝓞 F)) :
    ∀ l : List (HeightOneSpectrum (𝓞 F)), l.Nodup →
      finComponent (𝓞 F) F w (l.map fun w' => localEmbed (𝓞 F) F w' (c w')).prod
        = if w ∈ l then c w else 1
  | [], _ => by simp
  | (a :: l), hl => by
    rw [List.map_cons, List.prod_cons, map_mul,
      finComponent_prod_localEmbed c w l (List.nodup_cons.mp hl).2]
    by_cases hwa : w = a
    · subst hwa
      rw [finComponent_localEmbed_self, ite_eq_right (List.nodup_cons.mp hl).1, mul_one, ite_eq_left (List.mem_cons_self)]
    · rw [finComponent_localEmbed_of_ne (𝓞 F) F a (c a) hwa, one_mul]
      by_cases hwl : w ∈ l
      · rw [ite_eq_left hwl, ite_eq_left (List.mem_cons_of_mem a hwl)]
      · rw [ite_eq_right hwl, ite_eq_right (by simp [hwa, hwl])]

section W

variable {S : Finset (HeightOneSpectrum (𝓞 F))} {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem exists_apply_ne_zero_cpt_eq_one_off_finset
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : W g ≠ 0) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (g₁ : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W g₁ ≠ 0 ∧ ∀ w, w ∉ S → w ∉ T → cpt F w g₁ = 1 := by
  obtain ⟨T, hT⟩ : ∃ T : Finset (HeightOneSpectrum (𝓞 F)), ∀ w, w ∉ T → cpt F w g ∈ localLevelOne (𝓞 F) F w ⊤ :=
    ⟨(Filter.eventually_cofinite.mp (eventually_cpt_mem g)).toFinset, fun w hw => by
      by_contra h; exact hw (Set.Finite.mem_toFinset _ |>.mpr h)⟩

  set L : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) :=
    ((S ∪ T).toList.map fun w' => localEmbed (𝓞 F) F w' (cpt F w' g)).prod with hL
  set k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F) := (glFin (𝓞 F) F g)⁻¹ * L with hk
  have hLw : ∀ w, finComponent (𝓞 F) F w L = if w ∈ S ∪ T then cpt F w g else 1 := fun w => by
    rw [hL, finComponent_prod_localEmbed (fun w' => cpt F w' g) w _ (Finset.nodup_toList _)]
    simp only [Finset.mem_toList]
  have hkw : ∀ w, finComponent (𝓞 F) F w k = (cpt F w g)⁻¹ * (if w ∈ S ∪ T then cpt F w g else 1) :=
    fun w => by rw [hk, map_mul, map_inv, hLw]; rfl
  have hkmem : ∀ w, finComponent (𝓞 F) F w k ∈ localLevelOne (𝓞 F) F w ⊤ := fun w => by
    rw [hkw]
    split_ifs with h
    · rw [inv_mul_cancel]; exact one_mem _
    · rw [mul_one]; exact inv_mem (hT w fun h' => h (Finset.mem_union_right _ h'))
  refine ⟨T, g * finEmbed (𝓞 F) F k, ?_, fun w hwS hwT => ?_⟩
  · rw [hK _ (Subgroup.mem_inf.mpr ⟨(finEmbed_mem_levelOne_iff _ _ _).mpr
        (mem_finiteLevelOne_of_forall_finComponent hkmem),
        (mem_finiteAdelicGL2Subgroup_iff _ _).mpr (glArch_finEmbed _ _ _)⟩) (fun w hw => ?_)]
    · exact hg
    · rw [← cpt_eq_one_iff, cpt_finEmbed, hkw, ite_eq_left (Finset.mem_union_left _ hw), inv_mul_cancel]
  · rw [map_mul, cpt_finEmbed, hkw, ite_eq_right (by simp [hwS, hwT]), mul_one, mul_inv_cancel]

end W

end DiagOne

namespace DiagOne

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

noncomputable def lowerUnipotent (t : v.adicCompletion F) : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; t, 1] (by simp [det_fin_two_of])

variable (v) in

noncomputable def swapGL : GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by simp [det_fin_two_of])

noncomputable def diagGL (a d : v.adicCompletion F) (ha : a ≠ 0) (hd : d ≠ 0) :
    GL (Fin 2) (v.adicCompletion F) :=
  GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, d] (by simp [det_fin_two_of, ha, hd])

@[scoped simp] theorem val_lowerUnipotent (t : v.adicCompletion F) :
    ((lowerUnipotent t : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![1, 0; t, 1] := rfl

@[scoped simp] theorem val_swapGL :
    ((swapGL v : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![0, 1; 1, 0] := rfl

@[scoped simp] theorem val_diagGL (a d : v.adicCompletion F) (ha : a ≠ 0) (hd : d ≠ 0) :
    ((diagGL a d ha hd : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![a, 0; 0, d] := rfl

@[scoped simp] theorem val_unipotent (x : v.adicCompletion F) :
    ((unipotent x : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![1, x; 0, 1] := rfl

@[scoped simp] theorem val_scalarPi (π : v.adicCompletion F) (hπ : π ≠ 0) :
    ((scalarPi π hπ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π, 0; 0, π] := rfl

@[scoped simp] theorem val_diagZ (π : v.adicCompletion F) (hπ : π ≠ 0) (m : ℤ) :
    ((diagZ π hπ m : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π ^ m, 0; 0, 1] := rfl

theorem lowerUnipotent_mem {t : v.adicCompletion F} (ht : Valued.v t ≤ 1) :
    lowerUnipotent t ∈ localLevelOne (𝓞 F) F v ⊤ := by
  refine mem_localLevelOne_top _ (lowerUnipotent (-t)) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_lowerUnipotent, val_lowerUnipotent, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp [ht]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, ht]

theorem unipotent_mem (r : v.adicCompletionIntegers F) :
    unipotent (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r)
      ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have hr : Valued.v (r : v.adicCompletion F) ≤ 1 :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp r.2
  refine mem_localLevelOne_top _
    (unipotent (-(algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_unipotent, val_unipotent, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp [hr]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [Valuation.map_neg, hr]

variable (v) in
theorem swapGL_mem : swapGL v ∈ localLevelOne (𝓞 F) F v ⊤ := by
  refine mem_localLevelOne_top _ (swapGL v) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_swapGL, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp
  · intro i j; fin_cases i <;> fin_cases j <;> simp

theorem diagGL_mem {a d : v.adicCompletion F} (ha : Valued.v a = 1) (hd : Valued.v d = 1) :
    diagGL a d ((Valuation.ne_zero_iff _).mp (ha ▸ one_ne_zero)) ((Valuation.ne_zero_iff _).mp (hd ▸ one_ne_zero))
      ∈ localLevelOne (𝓞 F) F v ⊤ := by
  have ha0 : a ≠ 0 := (Valuation.ne_zero_iff _).mp (ha ▸ one_ne_zero)
  have hd0 : d ≠ 0 := (Valuation.ne_zero_iff _).mp (hd ▸ one_ne_zero)
  refine mem_localLevelOne_top _ (diagGL a⁻¹ d⁻¹ (inv_ne_zero ha0) (inv_ne_zero hd0)) ?_ ?_ ?_
  · refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [Units.val_mul, val_diagGL, val_diagGL, Matrix.mul_fin_two, Units.val_one]
    fin_cases i <;> fin_cases j <;> simp [ha0, hd0]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [ha, hd]
  · intro i j; fin_cases i <;> fin_cases j <;> simp [map_inv₀, ha, hd]

theorem exists_eq_zpow_mul {π : v.adicCompletion F} (hπ : Valued.v π = WithZero.exp (-1 : ℤ))
    {t : v.adicCompletion F} (ht : t ≠ 0) :
    ∃ (a : ℤ) (u : v.adicCompletion F), Valued.v u = 1 ∧ t = π ^ a * u := by
  have hπ0 : π ≠ 0 := fun h => by rw [h, map_zero] at hπ; exact WithZero.exp_ne_zero hπ.symm
  have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).mpr ht
  have hπa : Valued.v (π ^ (-WithZero.log (Valued.v t))) = Valued.v t := by
    rw [map_zpow₀, hπ, ← WithZero.exp_zsmul, smul_eq_mul, neg_mul_neg, mul_one, WithZero.exp_log hvt]
  refine ⟨-WithZero.log (Valued.v t), (π ^ (-WithZero.log (Valued.v t)))⁻¹ * t, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hπa, inv_mul_cancel₀ hvt]
  · rw [mul_inv_cancel_left₀ (zpow_ne_zero _ hπ0)]

theorem det_coe_ne_zero (x : GL (Fin 2) (v.adicCompletion F)) :
    (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)).det ≠ 0 := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact (Matrix.GeneralLinearGroup.det x).ne_zero

theorem exists_mul_upper (x : GL (Fin 2) (v.adicCompletion F)) :
    ∃ k ∈ localLevelOne (𝓞 F) F v ⊤,
      ((x * k : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) 1 0 = 0 := by
  obtain ⟨a, b, c, d, hx⟩ : ∃ a b c d : v.adicCompletion F,
      (x : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdet : a * d - b * c ≠ 0 := by rw [← Matrix.det_fin_two_of, ← hx]; exact det_coe_ne_zero x
  rcases le_or_gt (Valued.v c) (Valued.v d) with hcd | hdc
  · have hd : d ≠ 0 := by
      rintro rfl
      rw [map_zero, le_zero_iff, Valuation.zero_iff] at hcd
      exact hdet (by rw [hcd]; ring)
    refine ⟨lowerUnipotent (-(c / d)), lowerUnipotent_mem ?_, ?_⟩
    · rw [Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ hcd zero_le
    · have h : d * (c / d) = c := by field_simp
      rw [Units.val_mul, hx, val_lowerUnipotent, Matrix.mul_fin_two]
      simp [h]
  · have hc : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hdc
      exact not_lt_zero hdc
    refine ⟨swapGL v * lowerUnipotent (-(d / c)), mul_mem (swapGL_mem v) (lowerUnipotent_mem ?_), ?_⟩
    · rw [Valuation.map_neg, map_div₀]
      exact div_le_one_of_le₀ hdc.le zero_le
    · have h : c * (d / c) = d := by field_simp
      rw [← mul_assoc, Units.val_mul, Units.val_mul, hx, val_swapGL, val_lowerUnipotent, Matrix.mul_fin_two,
        Matrix.mul_fin_two]
      simp [h]

theorem exists_iwasawa {π : v.adicCompletion F} (hπv : Valued.v π = WithZero.exp (-1 : ℤ)) (hπ0 : π ≠ 0)
    (x : GL (Fin 2) (v.adicCompletion F)) :
    ∃ (ξ : v.adicCompletion F) (a c : ℤ) (k : GL (Fin 2) (v.adicCompletion F)),
      k ∈ localLevelOne (𝓞 F) F v ⊤ ∧
      x = unipotent ξ * diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0) * k := by
  obtain ⟨k₁, hk₁, h10⟩ := exists_mul_upper x
  obtain ⟨α, β, γ, δ, hy⟩ : ∃ α β γ δ : v.adicCompletion F,
      ((x * k₁ : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
        = !![α, β; γ, δ] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hγ : γ = 0 := by rw [hy] at h10; simpa using h10
  have hdet : α * δ ≠ 0 := by
    have := det_coe_ne_zero (x * k₁)
    rw [hy, Matrix.det_fin_two_of, hγ, mul_zero, sub_zero] at this
    exact this
  obtain ⟨a, u₁, hu₁, hαu⟩ := exists_eq_zpow_mul hπv (left_ne_zero_of_mul hdet)
  obtain ⟨c, u₂, hu₂, hδu⟩ := exists_eq_zpow_mul hπv (right_ne_zero_of_mul hdet)
  have hδ : δ ≠ 0 := right_ne_zero_of_mul hdet
  have hu₁0 : u₁ ≠ 0 := (Valuation.ne_zero_iff _).mp (hu₁ ▸ one_ne_zero)
  have hu₂0 : u₂ ≠ 0 := (Valuation.ne_zero_iff _).mp (hu₂ ▸ one_ne_zero)
  refine ⟨β / δ, a, c, diagGL u₁ u₂ hu₁0 hu₂0 * k₁⁻¹, mul_mem (diagGL_mem hu₁ hu₂) (inv_mem hk₁), ?_⟩
  have hy' : x * k₁ = unipotent (β / δ) * diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0)
      * diagGL u₁ u₂ hu₁0 hu₂0 := by
    refine Matrix.GeneralLinearGroup.ext fun i j => ?_
    rw [hy, Units.val_mul, Units.val_mul, val_unipotent, val_diagGL, val_diagGL, Matrix.mul_fin_two,
      Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j
    · simp [hαu]
    · simp [hδu]; field_simp
    · simp [hγ]
    · simp [hδu]
  rw [← mul_assoc, ← hy', mul_assoc, mul_inv_cancel, mul_one]

theorem val_scalarPi_pow (π : v.adicCompletion F) (hπ : π ≠ 0) (n : ℕ) :
    ((scalarPi π hπ ^ n : GL (Fin 2) (v.adicCompletion F)) : Matrix (Fin 2) (Fin 2) (v.adicCompletion F))
      = !![π ^ n, 0; 0, π ^ n] := by
  induction n with
  | zero => rw [pow_zero, Units.val_one, pow_zero]; exact Matrix.one_fin_two
  | succ n ih =>
    rw [pow_succ, Units.val_mul, ih, val_scalarPi, Matrix.mul_fin_two]
    simp [pow_succ]

theorem diagGL_mul_scalarPi_pow {π : v.adicCompletion F} (hπ0 : π ≠ 0) (a c : ℤ) :
    diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ0) (zpow_ne_zero c hπ0) * scalarPi π hπ0 ^ (-c).toNat
      = scalarPi π hπ0 ^ c.toNat * diagZ π hπ0 (a - c) := by
  have hc : ((c.toNat : ℕ) : ℤ) - (((-c).toNat : ℕ) : ℤ) = c := Int.toNat_sub_toNat_neg c
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, val_scalarPi_pow, val_scalarPi_pow, val_diagGL, val_diagZ,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  have h00 : π ^ a * π ^ (-c).toNat = π ^ c.toNat * π ^ (a - c) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hπ0, ← zpow_add₀ hπ0]
    congr 1; omega
  have h11 : π ^ c * π ^ (-c).toNat = π ^ c.toNat := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hπ0]
    congr 1; omega
  fin_cases i <;> fin_cases j <;> simp [h00, h11]

theorem scalarPi_comm (π : v.adicCompletion F) (hπ : π ≠ 0) (y : GL (Fin 2) (v.adicCompletion F)) :
    scalarPi π hπ * y = y * scalarPi π hπ := by
  obtain ⟨a, b, c, d, hyx⟩ : ∃ a b c d : v.adicCompletion F,
      (y : Matrix (Fin 2) (Fin 2) (v.adicCompletion F)) = !![a, b; c, d] := ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [Units.val_mul, Units.val_mul, hyx, val_scalarPi, Matrix.mul_fin_two, Matrix.mul_fin_two]
  fin_cases i <;> fin_cases j <;> simp [mul_comm]

end DiagOne

namespace DiagOne

open scoped Classical

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
  {W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ}

theorem addChar_apply_ne_zero {A : Type*} [AddGroup A] (ψ : AddChar A ℂ) (x : A) : ψ x ≠ 0 := fun h => by
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem apply_mul_placeEmbed_scalarPi_pow {π : v.adicCompletion F} (hπ : π ≠ 0) {om : ℂ}
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * placeEmbed F v (scalarPi π hπ)) = om * W g)
    (g : GL (Fin 2) (AdeleRing (𝓞 F) F)) (n : ℕ) :
    W (g * placeEmbed F v (scalarPi π hπ ^ n)) = om ^ n * W g := by
  induction n with
  | zero => rw [pow_zero, map_one, mul_one, pow_zero, one_mul]
  | succ n ih =>
    rw [pow_succ, map_mul, ← mul_assoc, hZ, ih, ← mul_assoc]
    congr 1; ring

theorem om_ne_zero {π : v.adicCompletion F} (hπ : π ≠ 0) {om : ℂ}
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * placeEmbed F v (scalarPi π hπ)) = om * W g)
    {g : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hg : W g ≠ 0) : om ≠ 0 := by
  intro hom
  have := hZ (g * placeEmbed F v (scalarPi π hπ)⁻¹)
  rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one, hom, zero_mul] at this
  exact hg this

theorem apply_ne_zero_of_local {ψ : AddChar (v.adicCompletion F) ℂ} {ϖ : v.adicCompletionIntegers F}
    (hπ : algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ ≠ 0)
    (hπv : Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) = WithZero.exp (-1 : ℤ))
    {lam om : ℂ} {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers F)
    (hψ0 : ∀ r : v.adicCompletionIntegers F,
      ψ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers F,
      ψ (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) ≠ 1)
    (hN : ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ x * W g)
    (hKv : ∀ k ∈ localLevelOne (𝓞 F) F v ⊤, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v k) = W g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) = lam * W g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ) hπ)) = om * W g)
    {h : GL (Fin 2) (AdeleRing (𝓞 F) F)} (hh : W h ≠ 0) :
    W (h * placeEmbed F v (cpt F v h)⁻¹) ≠ 0 := by
  set π := algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) ϖ with hπdef
  set h' := h * placeEmbed F v (cpt F v h)⁻¹ with hh'
  have hcpt : cpt F v h' = 1 := by rw [hh', map_mul, cpt_placeEmbed_self, mul_inv_cancel]
  have hdec : h = h' * placeEmbed F v (cpt F v h) := by
    rw [hh', mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]
  obtain ⟨ξ, a, c, k, hk, hx⟩ := exists_iwasawa hπv hπ (cpt F v h)
  have hom : om ≠ 0 := om_ne_zero hπ hZ hh

  have h1 : W (h' * placeEmbed F v (diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ) (zpow_ne_zero c hπ))) ≠ 0 := by
    have e : W h = ψ ξ *
        W (h' * placeEmbed F v (diagGL (π ^ a) (π ^ c) (zpow_ne_zero a hπ) (zpow_ne_zero c hπ))) := by
      rw [hdec, hx, map_mul, map_mul, ← mul_assoc, hKv k hk, ← mul_assoc, mul_placeEmbed_comm hcpt,
        mul_assoc, hN]
    exact fun h0 => hh (by rw [e, h0, mul_zero])

  have h2 : W (h' * placeEmbed F v (scalarPi π hπ ^ c.toNat) * placeEmbed F v (diagZ π hπ (a - c))) ≠ 0 := by
    rw [mul_assoc, ← map_mul, ← diagGL_mul_scalarPi_pow hπ a c, map_mul, ← mul_assoc,
      apply_mul_placeEmbed_scalarPi_pow hπ hZ]
    exact mul_ne_zero (pow_ne_zero _ hom) h1

  have hcomm : ∀ y : GL (Fin 2) (v.adicCompletion F),
      h' * placeEmbed F v (scalarPi π hπ ^ c.toNat) * placeEmbed F v y
        = placeEmbed F v y * (h' * placeEmbed F v (scalarPi π hπ ^ c.toNat)) := fun y => by
    rw [mul_assoc, ← map_mul, (Commute.pow_left (scalarPi_comm π hπ y) c.toNat).eq, map_mul, ← mul_assoc,
      mul_placeEmbed_comm hcpt, mul_assoc]
  have hKu : ∀ (r : v.adicCompletionIntegers F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (g * placeEmbed F v (unipotent
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r))) = W g :=
    fun r g => hKv _ (unipotent_mem r) g
  rw [UnramifiedWhittaker.apply_mul_placeEmbed_diagZ_eq_mul_torusFactor v hπ b hψ0 hψ1 hN hKu hT hZ hcomm
    (a - c)] at h2
  have h3 := left_ne_zero_of_mul h2
  rw [apply_mul_placeEmbed_scalarPi_pow hπ hZ] at h3
  exact right_ne_zero_of_mul h3

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

theorem exists_forall_cpt_eq_one
    (hstep : ∀ v ∉ S, ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 →
      W (h * placeEmbed F v (cpt F v h)⁻¹) ≠ 0)
    (U : Finset (HeightOneSpectrum (𝓞 F))) :
    ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 → (∀ w, w ∉ S → w ∉ U → cpt F w h = 1) →
      ∃ g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F), W g₀ ≠ 0 ∧ ∀ w, w ∉ S → cpt F w g₀ = 1 := by
  induction U using Finset.induction_on with
  | empty => exact fun h hh htriv => ⟨h, hh, fun w hw => htriv w hw (Finset.notMem_empty w)⟩
  | insert v U hvU ih =>
    intro h hh htriv
    by_cases hvS : v ∈ S
    · exact ih h hh fun w hwS hwU => htriv w hwS (by
        rw [Finset.mem_insert]; rintro (rfl | h'); exacts [hwS hvS, hwU h'])
    · refine ih (h * placeEmbed F v (cpt F v h)⁻¹) (hstep v hvS h hh) fun w hwS hwU => ?_
      by_cases hwv : w = v
      · subst hwv; rw [map_mul, cpt_placeEmbed_self, mul_inv_cancel]
      · rw [map_mul, cpt_placeEmbed_of_ne hwv, mul_one]
        exact htriv w hwS (by simp [hwv, hwU])

end DiagOne

open UnramifiedWhittaker.Shell

theorem mul_conj_apply_heckeGen_pow_mul_eq_of_shell_zero
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (ψv : AddChar (v.adicCompletion K) ℂ) (ϖ : v.adicCompletionIntegers K)
    (hπ : algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ ≠ 0)
    (hgen : placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ 1) =
      heckeGen (𝓞 K) K v)
    {I : Type*} [Fintype I] [Nonempty I] (b : I → v.adicCompletionIntegers K)
    (hI : Fintype.card I = Ideal.absNorm v.asIdeal)
    (hψ0 : ∀ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r) = 1)
    (hψ1 : ∃ r : v.adicCompletionIntegers K,
      ψv (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) r /
        algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ≠ 1)
    (W W' : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (lam om lam' om' : ℂ)
    (hN : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (placeEmbed K v (unipotent x) * g) = ψv x * W g)
    (hN' : ∀ (x : v.adicCompletion K) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (placeEmbed K v (unipotent x) * g) = ψv x * W' g)
    (hK : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W g)
    (hK' : ∀ (kv : GL (Fin 2) (v.adicCompletionIntegers K)) (g : GL (Fin 2) (AdeleRing (𝓞 K) K)),
      W' (g * placeEmbed K v (Matrix.GeneralLinearGroup.map
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)) kv)) = W' g)
    (hT : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam * W g)
    (hT' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      (∑ i, W' (g * placeEmbed K v (repSome
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (b i))))) +
        W' (g * placeEmbed K v (repInf
          (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = lam' * W' g)
    (hZ : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om * W g)
    (hZ' : ∀ g : GL (Fin 2) (AdeleRing (𝓞 K) K),
      W' (g * placeEmbed K v (scalarPi
        (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ)) = om' * W' g)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K))
    (hg : Valued.v ((((Matrix.GeneralLinearGroup.det g : (AdeleRing (𝓞 K) K)ˣ) : AdeleRing (𝓞 K) K)).2 v) =
      (max (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 0).2 v))
           (Valued.v (((g : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 K) K)) 1 1).2 v))) ^ 2) :
    (∀ m : ℕ,
      W ((heckeGen (𝓞 K) K v) ^ m * g) * (starRingEnd ℂ) (W' ((heckeGen (𝓞 K) K v) ^ m * g)) =
        heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m *
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) lam') ((starRingEnd ℂ) om') m *
          (W g * (starRingEnd ℂ) (W' g))) ∧
    (∀ m : ℕ, 0 < m → W ((heckeGen (𝓞 K) K v)⁻¹ ^ m * g) = 0) := by
  have hπv : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) = WithZero.exp (-1 : ℤ) :=
    valued_eq_of_placeEmbed_diagZ_eq_heckeGen K v ϖ hπ hgen

  set X : GL (Fin 2) (v.adicCompletion K) := cpt K v g with hX
  set g' : GL (Fin 2) (AdeleRing (𝓞 K) K) := (placeEmbed K v X)⁻¹ * g with hg'def
  have hg' : cpt K v g' = 1 := cpt_inv_placeEmbed_cpt_mul K v g
  have hgX : g = placeEmbed K v X * g' := by rw [hg'def, mul_inv_cancel_left]

  have hXshell : Valued.v (Matrix.det (X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K))) =
      (max (Valued.v ((X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 0))
        (Valued.v ((X : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) 1 1))) ^ 2 := by
    rw [hX, det_cpt, cpt_apply, cpt_apply]; exact hg
  obtain ⟨x, j, k, hXeq⟩ := local_iwasawa K v ϖ hπ hπv X hXshell

  obtain ⟨c, hc⟩ := key_identity K v W ψv ϖ hπ lam om b hψ0 hψ1 hN hK hT hZ x j k g' hg'
  obtain ⟨c', hc'⟩ := key_identity K v W' ψv ϖ hπ lam' om' b hψ0 hψ1 hN' hK' hT' hZ' x j k g' hg'
  have hψu : ∀ y : v.adicCompletion K, ψv y * (starRingEnd ℂ) (ψv y) = 1 :=
    addChar_mul_conj_eq_one K v ψv hψ0

  have hGm : ∀ m : ℕ, (heckeGen (𝓞 K) K v) ^ m = placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (m : ℤ)) := fun m => by
    rw [← hgen, ← map_pow, diagZ_one_pow]
  have hGinv : ∀ m : ℕ, (heckeGen (𝓞 K) K v)⁻¹ ^ m = placeEmbed K v (diagZ (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) hπ (-(m : ℤ))) := fun m => by
    rw [← hgen, ← map_inv, ← map_pow, diagZ_one_inv_pow]
  have hW0 : W g = ψv x * c * W g' := by
    have e := hc 0
    rw [diagZ_zero', map_one, one_mul, zpow_zero, one_mul, ← hXeq, ← hgX, torusFactor_zero, mul_one] at e
    exact e
  have hW0' : W' g = ψv x * c' * W' g' := by
    have e := hc' 0
    rw [diagZ_zero', map_one, one_mul, zpow_zero, one_mul, ← hXeq, ← hgX, torusFactor_zero, mul_one] at e
    exact e
  have hcard : (Fintype.card I : ℂ) = ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) := by rw [hI]
  refine ⟨fun m => ?_, fun m hm => ?_⟩
  · have e := hc m
    have e' := hc' m
    rw [← hXeq, ← hgX, ← hGm, torusFactor_natCast, hcard] at e e'
    rw [e, e', hW0, hW0']
    simp only [map_mul, conj_heckeRecursionSeq]
    have u1 := hψu ((algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) ϖ) ^ (m : ℤ) * x)
    have u0 := hψu x
    linear_combination
      (c * (starRingEnd ℂ) c' * (W g' * (starRingEnd ℂ) (W' g')) *
        (heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) lam om m *
          heckeRecursionSeq ((Ideal.absNorm v.asIdeal : ℕ) : ℂ) ((starRingEnd ℂ) lam') ((starRingEnd ℂ) om') m)) *
        (u1 - u0)
  · have e := hc (-(m : ℤ))
    rw [← hXeq, ← hgX, ← hGinv, torusFactor_neg _ _ _ (by omega)] at e
    rw [e, mul_zero, mul_zero]


theorem exists_apply_diagOne_mul_ne_zero_of_apply_ne_zero
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (W : GL (Fin 2) (AdeleRing (𝓞 F) F) → ℂ)
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), AddChar (v.adicCompletion F) ℂ)
    (ϖ : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletionIntegers F)
    (hπ : ∀ v : HeightOneSpectrum (𝓞 F),
      algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v) ≠ 0)
    (hϖ : ∀ v ∉ S,
      Valued.v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) =
        WithZero.exp (-1 : ℤ))
    {I : HeightOneSpectrum (𝓞 F) → Type*} [∀ v, Fintype (I v)] [∀ v, Nonempty (I v)]
    (b : ∀ v : HeightOneSpectrum (𝓞 F), I v → v.adicCompletionIntegers F)
    (lam om : HeightOneSpectrum (𝓞 F) → ℂ)
    (hψ0 : ∀ v ∉ S, ∀ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r) = 1)
    (hψ1 : ∀ v ∉ S, ∃ r : v.adicCompletionIntegers F,
      ψ v (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) r /
        algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) ≠ 1)
    (hN : ∀ v ∉ S, ∀ (x : v.adicCompletion F) (g : GL (Fin 2) (AdeleRing (𝓞 F) F)),
      W (placeEmbed F v (unipotent x) * g) = ψ v x * W g)
    (hT : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      (∑ i, W (g * placeEmbed F v (repSome
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v)
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (b v i))))) +
        W (g * placeEmbed F v (repInf
          (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        lam v * W g)
    (hZ : ∀ v ∉ S, ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F),
      W (g * placeEmbed F v (scalarPi
        (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) (ϖ v)) (hπ v))) =
        om v * W g)
    (hK : ∀ k : GL (Fin 2) (AdeleRing (𝓞 F) F),
      k ∈ levelOne (𝓞 F) F ⊤ ⊓ finiteAdelicGL2Subgroup F →
      (∀ v ∈ S, ∀ i j : Fin 2,
        ((k : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) →
      ∀ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W (g * k) = W g)
    (hW : ∃ g : GL (Fin 2) (AdeleRing (𝓞 F) F), W g ≠ 0) :
    ∃ (g₀ : GL (Fin 2) (AdeleRing (𝓞 F) F)) (a₀ : (AdeleRing (𝓞 F) F)ˣ),
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ i j : Fin 2,
        ((g₀ : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v =
          ((1 : Matrix (Fin 2) (Fin 2) (AdeleRing (𝓞 F) F)) i j).2 v) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ((a₀ : (AdeleRing (𝓞 F) F)ˣ) : AdeleRing (𝓞 F) F).2 v = 1) ∧
      W (diagOne a₀ * g₀) ≠ 0 := by
  classical
  obtain ⟨g, hg⟩ := hW
  obtain ⟨T, g₁, hg₁, hT₁⟩ := UnramifiedWhittaker.DiagOne.exists_apply_ne_zero_cpt_eq_one_off_finset hK hg
  have hstep : ∀ v ∉ S, ∀ h : GL (Fin 2) (AdeleRing (𝓞 F) F), W h ≠ 0 →
      W (h * placeEmbed F v (UnramifiedWhittaker.DiagOne.cpt F v h)⁻¹) ≠ 0 :=
    fun v hv h hh => UnramifiedWhittaker.DiagOne.apply_ne_zero_of_local (hπ v) (hϖ v hv) (b v) (hψ0 v hv)
      (hψ1 v hv) (hN v hv)
      (fun k hk g => UnramifiedWhittaker.DiagOne.apply_mul_placeEmbed_of_mem_localLevelOne hK hv hk g)
      (hT v hv) (hZ v hv) hh
  obtain ⟨g₀, hg₀, htriv⟩ :=
    UnramifiedWhittaker.DiagOne.exists_forall_cpt_eq_one hstep T g₁ hg₁ fun w hwS hwT => hT₁ w hwS hwT
  refine ⟨g₀, 1, fun v hv => (UnramifiedWhittaker.DiagOne.cpt_eq_one_iff v g₀).mp (htriv v hv),
    fun v _ => rfl, ?_⟩
  rwa [map_one, one_mul]

end UnramifiedWhittaker
