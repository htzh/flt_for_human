/-
  The Hecke recursion and the explicit coset representatives of the unramified Whittaker
  function at a finite place.

  Two independent blocks, both local at a finite place `v` of the number field `K`.

  *The recursion.* `heckeRecursionSeq N lam om` is the sequence of Hecke eigenvalues of the
  unramified Whittaker function of `GL₂`, normalised by the level `N` and the two Satake
  parameters `lam` (the trace) and `om` (the product):

    `f 0 = 1`, `f 1 = lam / N`, `f (m+2) = (lam * f (m+1) - om * f m) / N`.

  `torusFactor N lam om m` is that sequence at a nonnegative exponent and `0` at a negative
  one — the torus part of the unramified Whittaker function in the Iwasawa parametrisation.

  *The representatives.* In `GL₂(K)`:
  `unipotent x = !![1, x; 0, 1]`, `diagZ π m = diag(π^m, 1)`, and the two coset
  representatives `repSome π β = !![π, β; 0, 1]` and `repInf π = diag(1, π)` of the Hecke
  double coset of `diag(π, 1)`, together with the central element `scalarPi π = diag(π, π)`.
  `placeEmbed v` is the embedding of `GL₂(K_v)` into `GL₂(𝔸_K)`: the local matrix at `v`,
  the identity elsewhere, that is `finEmbed` after `localEmbed`.

  These are the objects the two realization-scalar identities of the Whittaker coefficient
  are phrased in: the sum over the `q + 1` representatives at a place where the coefficient
  is a Hecke eigenfunction, and the central-scalar identity `scalarPi` at a place where it is
  not exceptional.

  Transcribed verbatim from `Definitions/Def_UnramifiedWhittaker_HeckeRecursion.lean`
  (pinned `aa2d8b3`, 55 lines, 8 declarations, no `private`). Its single `Definitions/`
  import is the already-ported `FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding`, which
  supplies `finEmbed`, `localEmbed` and `HeightOneSpectrum`'s completion.

  `repSome`/`repInf` restate, over an arbitrary nonzero `π ∈ K`, the matrices the port's
  `LocalGL2.localRepSome`/`localRepInf` build from a uniformiser `ϖ` of the valuation ring;
  the two pairs are type-distinct (an arbitrary `π : K` versus `algebraMap R K ϖ`), so both
  statements are kept and the pin's inline equality proof is available at each use site.

  spec-pin: Definitions/Def_UnramifiedWhittaker_HeckeRecursion.lean
-/
import FLTForHuman.NumberTheory.AdelicDock.LocalEmbedding
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option autoImplicit false

noncomputable section

open Matrix

namespace UnramifiedWhittaker

def heckeRecursionSeq (N lam om : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => lam / N
  | m + 2 => (lam * heckeRecursionSeq N lam om (m + 1) - om * heckeRecursionSeq N lam om m) / N

def torusFactor (N lam om : ℂ) (m : ℤ) : ℂ :=
  if 0 ≤ m then heckeRecursionSeq N lam om m.toNat else 0

section Matrices

variable {K : Type*} [Field K]

def unipotent (x : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, x; 0, 1] (by simp [det_fin_two_of])

def diagZ (π : K) (hπ : π ≠ 0) (m : ℤ) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π ^ m, 0; 0, 1] (by simp [det_fin_two_of, zpow_ne_zero m hπ])

def repSome (π : K) (hπ : π ≠ 0) (β : K) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, β; 0, 1] (by simp [det_fin_two_of, hπ])

def repInf (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![1, 0; 0, π] (by simp [det_fin_two_of, hπ])

def scalarPi (π : K) (hπ : π ≠ 0) : GL (Fin 2) K :=
  GeneralLinearGroup.mkOfDetNeZero !![π, 0; 0, π] (by simp [det_fin_two_of, hπ])

end Matrices

section Adelic

open IsDedekindDomain NumberField AdelicDock

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def placeEmbed (v : HeightOneSpectrum R) :
    GL (Fin 2) (v.adicCompletion K) →* GL (Fin 2) (AdeleRing R K) :=
  (finEmbed R K).comp (localEmbed R K v)

end Adelic

end UnramifiedWhittaker

end
