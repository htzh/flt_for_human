/-
  Freeness from a full-length weakly regular sequence.

  `Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal` — if `xs` is a
  regular sequence spanning the maximal ideal of a Noetherian local ring `R`, and
  `s` is a weakly regular `M`-sequence of the same length whose elements lie in the
  maximal ideal and whose quotient `M ⧸ (s) M` has finite length, then `M` is free.

  The statement is the pin's `Theorems/` wrapper verbatim; the proof is transcribed
  from `P2M/Sol/S_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal.lean`
  (pinned `aa2d8b3`), with the private `OnePrime` helper block.

  **Reuse checked against mathlib (work order §2).** `#check` on the `OnePrime`
  block found that most of it is already mathlib:

  * `ModuleCat.projectiveDimension_quotient_eq_length` and
    `ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular` are
    mathlib's (the pin already calls them);
  * `projective_iff_hasProjectiveDimensionLT_one`, `IsProjective.iff_projective`,
    `Module.Projective.of_equiv`, `Module.Flat.of_projective`,
    `Module.free_of_flat_of_isLocalRing`, `hasProjectiveDimensionLT_of_iso`,
    `hasProjectiveDimensionLT_of_ge`, `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₂`
    are mathlib's, so `free_of_hasProjectiveDimensionLT_one` is a 6-line derivation
    rather than a re-proof;
  * the only genuinely mathlib-absent piece is
    `OnePrime.hasProjectiveDimensionLT_of_isFiniteLength` — the induction over
    mathlib's `IsFiniteLength` (`of_subsingleton` / `of_simple_quotient`) bounding the
    projective dimension by `xs.length + 1`. Mathlib has no
    `IsFiniteLength → projectiveDimension` lemma, so this is ported.
  * `le_zero_of_add_natCast_le` (`WithBot ℕ∞` arithmetic) is **not** in mathlib; it is
    kept, with the v4.34 `ENat` renames (`coe_add`/`coe_le_coe`/`coe_lt_top` →
    `natCast_add`/`natCast_le_natCast`/`natCast_lt_top`).
-/
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors

set_option autoImplicit false

open CategoryTheory

universe u v

namespace OnePrime

universe w

/-- If `a + n ≤ n` in `WithBot ℕ∞` for a natural `n`, then `a ≤ 0`. (Not in mathlib;
ported from the pin.) -/
private theorem le_zero_of_add_natCast_le {a : WithBot ℕ∞} {n : ℕ}
    (h : a + (n : WithBot ℕ∞) ≤ n) : a ≤ 0 := by
  induction a with
  | bot => exact bot_le
  | coe a =>
    induction a with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, top_add, WithBot.coe_le_coe] at h
      exact absurd h (not_le.mpr (ENat.natCast_lt_top n))
    | coe e =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe, ← ENat.natCast_add,
        ENat.natCast_le_natCast] at h
      have he : e = 0 := by omega
      subst he
      exact le_of_eq (by simp)

/-- A finite-length module over a Noetherian local ring has projective dimension less
than the length of any regular system of parameters, plus one. Ported from the pin;
mathlib has no `IsFiniteLength → projectiveDimension` lemma. -/
private theorem hasProjectiveDimensionLT_of_isFiniteLength {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] [Small.{w} R] (xs : List R)
    (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    {N : Type w} [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N) :
    HasProjectiveDimensionLT (ModuleCat.of R N) (xs.length + 1) := by
  induction hN with
  | @of_subsingleton N _ _ _ =>
    have : HasProjectiveDimensionLT (ModuleCat.of R N) 0 :=
      (ModuleCat.isZero_of_subsingleton (ModuleCat.of R N)).hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge (ModuleCat.of R N) 0 (xs.length + 1) (Nat.zero_le _)
  | @of_simple_quotient N _ _ P hsimple hP ih =>

    obtain ⟨I, hImax, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    have hI : I = Ideal.ofList xs := (IsLocalRing.eq_maximalIdeal hImax).trans hspan.symm
    have hk : HasProjectiveDimensionLT (ModuleCat.of R (Shrink.{w} (R ⧸ Ideal.ofList xs))) (xs.length + 1) :=
      (projectiveDimension_le_iff _ _).mp (ModuleCat.projectiveDimension_quotient_eq_length.{w} xs hxs).le
    let eN : Shrink.{w} (R ⧸ Ideal.ofList xs) ≃ₗ[R] N ⧸ P :=
      ((e.trans (Submodule.quotEquivOfEq I (Ideal.ofList xs) hI)).trans (Shrink.linearEquiv R _).symm).symm
    have h3 : HasProjectiveDimensionLT (ModuleCat.of R (N ⧸ P)) (xs.length + 1) :=
      hasProjectiveDimensionLT_of_iso eN.toModuleIso _

    have hS := LinearMap.shortExact_shortComplexKer (Submodule.mkQ_surjective P)
    have h1 : HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker P.mkQ)) (xs.length + 1) :=
      hasProjectiveDimensionLT_of_iso (LinearEquiv.ofEq _ _ (Submodule.ker_mkQ P).symm).toModuleIso _
    exact hS.hasProjectiveDimensionLT_X₂ (xs.length + 1) h1 h3

/-- A finite module of projective dimension `< 1` over a local ring is free. Ported
from the pin; a thin derivation from mathlib's projective-dimension API. -/
private theorem free_of_hasProjectiveDimensionLT_one {R : Type u} [CommRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (h : HasProjectiveDimensionLT (ModuleCat.of R (ULift.{u} M)) 1) : Module.Free R M := by
  have h1 : Projective (ModuleCat.of R (ULift.{u} M)) := projective_iff_hasProjectiveDimensionLT_one.mpr h
  have h2 : Module.Projective R (ULift.{u} M) := (IsProjective.iff_projective (R := R) (ULift.{u} M)).mpr h1
  have h3 : Module.Projective R M := Module.Projective.of_equiv (ULift.moduleEquiv (R := R) (M := M))
  exact Module.free_of_flat_of_isLocalRing

end OnePrime

/-- **Freeness from a full-length weakly regular sequence.** Stated verbatim from
`Theorems/Thm_Module_free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal.lean`. -/
theorem Module.free_of_isWeaklyRegular_of_isRegular_ofList_eq_maximalIdeal
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (xs : List R) (hxs : RingTheory.Sequence.IsRegular R xs)
    (hspan : Ideal.ofList xs = IsLocalRing.maximalIdeal R)
    (s : List R) (hs : ∀ r ∈ s, r ∈ IsLocalRing.maximalIdeal R)
    (hreg : RingTheory.Sequence.IsWeaklyRegular M s) (hlen : s.length = xs.length)
    (hfl : IsFiniteLength R (M ⧸ (Ideal.ofList s • ⊤ : Submodule R M))) :
    Module.Free R M := by

  rcases subsingleton_or_nontrivial M with hM | hM
  · infer_instance

  have key := ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
    (ModuleCat.of R (ULift.{u} M)) s
    (((ULift.moduleEquiv (R := R) (M := M)).isWeaklyRegular_congr s).mpr hreg) hs

  have e : (ULift.{u} M ⧸ (Ideal.ofList s • ⊤ : Submodule R (ULift.{u} M))) ≃ₗ[R]
      M ⧸ (Ideal.ofList s • ⊤ : Submodule R M) :=
    Submodule.Quotient.equiv _ _ (ULift.moduleEquiv (R := R) (M := M)) (by
      rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range])
  have hfl' : IsFiniteLength R (ULift.{u} M ⧸ (Ideal.ofList s • ⊤ : Submodule R (ULift.{u} M))) :=
    e.symm.isFiniteLength hfl

  have hlt := OnePrime.hasProjectiveDimensionLT_of_isFiniteLength xs hxs hspan hfl'
  have hle : projectiveDimension (ModuleCat.of R (ULift.{u} M)) + (s.length : WithBot ℕ∞) ≤ xs.length := by
    rw [← key]
    exact (projectiveDimension_le_iff _ _).mpr hlt
  rw [hlen] at hle

  have h0 : HasProjectiveDimensionLT (ModuleCat.of R (ULift.{u} M)) 1 :=
    (projectiveDimension_le_iff _ 0).mp (by exact_mod_cast OnePrime.le_zero_of_add_natCast_le hle)
  exact OnePrime.free_of_hasProjectiveDimensionLT_one h0
