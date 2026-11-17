/-
  Pin sources whose statements the port owns rather than diffs.

  This module declares nothing and imports nothing. It carries the `spec-pin:` lines
  that were removed from a port module when that module's interface deliberately
  departed from the pin's shape; `spec/check_port.py` reads them here (no declarations,
  so nothing to diff) and `frontier.py` reads them from this file as well, which keeps
  the pin marked *ported* and stops it being proposed for porting again.

  The changes themselves are registered in `topics/TOPIC-interface-changes.md`, with the
  pin shape, the port shape and the bridges between them. Add a `spec-pin:` line here
  only together with an entry there.

  ModularForms/QCoeff — the `q`-coefficient floor. Its interface is the port's
  `HasQCoeff` certificate rather than the pin's three regularity conditions, and the
  q-expansion analysis behind it is public here (topics/TOPIC-interface-changes.md
  Entry 1):

    spec-pin: Definitions/Def_FLTPrelim_Modularity.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_CuspForm_IsEigenformWith_heckeU_add_smul_slash_heckeDiagMatrix_degeneracy_eq_qCoeff_smul.lean

  ModularForms/QCoeffClass — the bundled `hasSum_qCoeff` producer (pin: a `variable`
  section, so the checker's stored text omits the section binders) and the bundled
  equality principle, which is the instance-level facade on `QCoeff`:

    spec-pin: Theorems/Thm_ModularFormClass_eq_of_forall_qCoeff_eq.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean

  ModularForms/HeckeQCoeff — the Hecke action on `q`-coefficients. The function-level
  coefficient identities take the certificate instead of the three regularity
  conditions, so the module is unpinned; the rest of its declarations sit on the same
  wire and are listed here with it:

    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_heckeU.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_heckeT.lean
    spec-pin: Theorems/Thm_UpperHalfPlane_qCoeff_comp_heckeDiagMatrix_smul.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_heckeU.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_heckeT.lean
    spec-pin: Theorems/Thm_ModularFormClass_qCoeff_comp_heckeDiagMatrix_smul.lean
    spec-pin: Theorems/Thm_ModularFormClass_qExpansion_heckeU_eq_heckeU.lean
    spec-pin: Theorems/Thm_ModularFormClass_qExpansion_heckeT_eq_heckeT.lean
    spec-pin: Theorems/Thm_ModularForm_qExpansion_heckeDiagMatrix_smul_eq_qExpand_of_levelOne.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeU_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeU_int.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_coeffHeckeU_comm.lean
    spec-pin: Theorems/Thm_ModularForm_coeffHeckeT_int.lean
    spec-pin: P2M/Sol/S_UpperHalfPlane_qCoeff_heckeU.lean

  Re-wiring a parked module needs `own:` rows back for the declarations whose pin has no
  comparable statement: `ModularFormClass.qCoeff_add'`, `…qCoeff_sub'` and
  `…qCoeff_const_smul'` are the general spellings of the pin's concrete per-file copies.
-/
