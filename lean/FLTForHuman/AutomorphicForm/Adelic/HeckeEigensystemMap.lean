/-
  Maps of Hecke eigensystems along ring homomorphisms.

  A ring hom `ι : R →+* S` carries an `R`-valued `HeckeEigensystem F R` to an
  `S`-valued one by applying `ι` to the eigenvalue families `a`/`b` (`map`), with the
  expected functoriality (`map_id`, `map_map`), compatibility with `twist`,
  and preservation of `AgreesAwayFromFinite`.

  Transcribed verbatim from `Definitions/Def_AutomorphicForm_HeckeEigensystemMap.lean`
  (pinned `aa2d8b3`, 48 lines / 5 declarations). The pin's
  `import Definitions.Def_AutomorphicForm_HeckeEigensystem` is replaced by the port's
  `AutomorphicForm/Adelic/HeckeEigensystem`; the pin namespace
  `AutomorphicForm.HeckeEigensystem` is kept. Every declaration is residue (mathlib
  `v4.34.0` has no counterpart), with no proof-level drift.
-/
import FLTForHuman.AutomorphicForm.Adelic.HeckeEigensystem

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace AutomorphicForm

namespace HeckeEigensystem

variable {F : Type*} [Field F] [NumberField F] {R : Type*} [CommRing R]
  {S : Type*} [CommRing S]

def map (ι : R →+* S) (Φ : HeckeEigensystem F R) : HeckeEigensystem F S where
  level := Φ.level
  level_ne_bot := Φ.level_ne_bot
  a := fun v => ι (Φ.a v)
  b := fun v => ι (Φ.b v)

@[simp] theorem map_level (ι : R →+* S) (Φ : HeckeEigensystem F R) :
    (Φ.map ι).level = Φ.level := rfl

@[simp] theorem map_a (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).a v = ι (Φ.a v) := rfl

@[simp] theorem map_b (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (v : HeightOneSpectrum (𝓞 F)) : (Φ.map ι).b v = ι (Φ.b v) := rfl

theorem map_id (Φ : HeckeEigensystem F R) : Φ.map (RingHom.id R) = Φ := rfl

theorem map_map {T : Type*} [CommRing T] (ι : R →+* S) (κ : S →+* T)
    (Φ : HeckeEigensystem F R) : (Φ.map ι).map κ = Φ.map (κ.comp ι) := rfl

theorem map_twist (ι : R →+* S) (Φ : HeckeEigensystem F R)
    (χ : HeightOneSpectrum (𝓞 F) → R) :
    (Φ.twist χ).map ι = (Φ.map ι).twist fun v => ι (χ v) := by
  simp only [map, twist]
  congr 1 <;> funext v
  · exact map_mul ι (χ v) (Φ.a v)
  · rw [map_mul, map_pow]

theorem AgreesAwayFromFinite.map {Φ Φ' : HeckeEigensystem F R}
    (h : AgreesAwayFromFinite Φ Φ') (ι : R →+* S) :
    AgreesAwayFromFinite (Φ.map ι) (Φ'.map ι) := by
  obtain ⟨S₀, hS₀⟩ := h
  exact ⟨S₀, fun v hv => ⟨congrArg ι (hS₀ v hv).1, congrArg ι (hS₀ v hv).2⟩⟩

end HeckeEigensystem

end AutomorphicForm
