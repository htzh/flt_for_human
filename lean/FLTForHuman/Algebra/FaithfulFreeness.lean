/-
  Faithful freeness forces a compatible surjection to be bijective.

  Two generic algebra facts that the T-side patching exit consumes:

  * `RingHom.bijective_of_surjective_of_smul_eq` — a surjective ring hom `g : S →+* T`
    whose action on a free nontrivial `S`-module `N` agrees with the `T`-action
    (`g s • n = s • n`) is bijective: its kernel annihilates `N`, hence is `⊥`
    because `N` is faithful.
  * `Module.Free.of_surjective_of_smul_eq` — the same hypotheses make `N` free over
    `T`: transport a basis along the induced ring equivalence.

  The two statements are the pin's `Theorems/` wrappers verbatim; the proofs are
  transcribed from the `P2M/Sol/S_*` files, pinned `aa2d8b3`:

  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_RingHom_bijective_of_surjective_of_smul_eq.lean
  * https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b3/P2M/Sol/S_Module_Free_of_surjective_of_smul_eq.lean

  The pin proves the bijectivity twice: `S_Module_Free_of_surjective_of_smul_eq`
  carries a private `FrobChareqDock.bijective_aux` (pin lines 7–16) that is
  byte-identical to the first file's `solution` (pin lines 7–13). Here the
  bijectivity is proved **once**, and `Module.Free T N` is derived from it, exactly
  as the pin's own `Module.Free` `solution` already does with `Module.Free.of_basis`
  and `RingEquiv.ofBijective`. The duplicate `bijective_aux` is not ported
  (playbook §2).
-/
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Module.Torsion.Basic

set_option autoImplicit false

/-- **A compatible surjection out of a faithful free action is bijective.** Stated
verbatim from `Theorems/Thm_RingHom_bijective_of_surjective_of_smul_eq.lean`. -/
theorem RingHom.bijective_of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N] [Nontrivial N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Function.Bijective g := by
  refine ⟨?_, hsurj⟩
  rw [RingHom.injective_iff_ker_eq_bot, eq_bot_iff]
  intro s hs
  have hann : s ∈ Module.annihilator S N := Module.mem_annihilator.mpr fun n => by
    rw [← hg s n, RingHom.mem_ker.mp hs, zero_smul]
  rwa [(Module.annihilator_eq_bot (R := S) (M := N)).mpr inferInstance] at hann

/-- **Freeness transports across a compatible surjection.** Stated verbatim from
`Theorems/Thm_Module_Free_of_surjective_of_smul_eq.lean`.

Derived from `RingHom.bijective_of_surjective_of_smul_eq` (this module) rather than
re-proving the bijectivity, as the pin's second file did. -/
theorem Module.Free.of_surjective_of_smul_eq {S T N : Type*} [CommRing S] [Ring T]
    [AddCommGroup N] [Module S N] [Module T N] [Module.Free S N]
    (g : S →+* T) (hg : ∀ (s : S) (n : N), g s • n = s • n) (hsurj : Function.Surjective g) :
    Module.Free T N := by
  rcases subsingleton_or_nontrivial N with _ | _
  · infer_instance
  · exact Module.Free.of_basis <| (Module.Free.chooseBasis S N).mapCoeffs
      (RingEquiv.ofBijective g (RingHom.bijective_of_surjective_of_smul_eq g hg hsurj))
      (fun c x => hg c x)
