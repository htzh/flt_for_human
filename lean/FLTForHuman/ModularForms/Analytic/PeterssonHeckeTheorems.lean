/-
  The Petersson adjointness of the Hecke operator on the `ε`-nebentypus component:
  `⟨T_p f, g⟩ = conj ε(p) ⟨f, T_p g⟩`, where
  `T_p f = heckeU k p f + ε(p) • (f ∣ heckeDiagMatrix p)`.

  Tier-1 façade over the tier-3 engine
  `FLTForHuman/ModularForms/Analytic/PeterssonHecke.lean` (118 public
  declarations, registered in `spec/UNWIRED-PUBLIC.md`). The statement is the pin's
  `Theorems/Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean`
  verbatim; the proof is the one-line application of the engine's
  `CuspForm.PetHeckeAdj.main`, exactly as the pin's `solution` forwards.
-/
import FLTForHuman.ModularForms.Analytic.PeterssonHecke

set_option autoImplicit false

open CongruenceSubgroup ModularForm
open scoped ModularForm UpperHalfPlane MatrixGroups Modular

namespace CuspForm

-- pin: peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
--   (Thm_CuspForm_peterssonOn_hecke_eq_conj_mul_of_hasNebentypus.lean:12)
set_option linter.style.haveILetI false in
theorem peterssonOn_hecke_eq_conj_mul_of_hasNebentypus
    (N : ℕ) [NeZero N] (k : ℤ) (ε : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (hpN : ¬ p ∣ N)
    (f g : CuspForm (Gamma1 N) k) (hf : CuspForm.HasNebentypus ε f)
    (hg : CuspForm.HasNebentypus ε g) :
    CuspForm.peterssonOn (Gamma1 N) k
        (heckeU k p ⇑f + ε (p : ZMod N) • (⇑f ∣[k] heckeDiagMatrix p)) ⇑g
      = starRingEnd ℂ (ε (p : ZMod N)) *
        CuspForm.peterssonOn (Gamma1 N) k ⇑f
          (heckeU k p ⇑g + ε (p : ZMod N) • (⇑g ∣[k] heckeDiagMatrix p)) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  exact PetHeckeAdj.main hp hpN ε f g hf hg

end CuspForm
