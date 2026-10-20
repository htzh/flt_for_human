/-
  Chevalley's extension theorem for valuation subrings of an algebraically closed
  field, in three steps:

      `ValuationSubring.exists_ringHom_extend_of_isAlgClosed` (343 pin lines)
      `IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one` (67)
      `IsAlgClosed.exists_valuationSubring_ringHom_retraction` (26)

  The port of the three pin leaves of those names (`Theorems/Thm_…` for the
  statements, `P2M/Sol/S_…` for the proofs). The pin's inner namespaces
  `ChevalleyHom`, `ChevalleyHom.IsGraph` (with its `section Maximal` and
  `section Extend` and their `include hmax`) are kept verbatim, as are the pin's
  short names; the pin's `solution` wrappers are not ported.

  The mathematics. Write a ring hom `φ : R →+* Ω` as its graph, a subring
  `Γ₀ ⊆ L × Ω` meeting the `Ω`-axis only at `0` (`IsGraph`); Zorn gives a maximal
  such `Γ ⊇ Γ₀` (`exists_maximal`). For a maximal graph `Γ` the projection
  `dom Γ ⊆ L` is a local ring with maximal ideal the graph of `0`
  (`isLocalRing`, `mem_maximalIdeal_iff`), and it is closed under inverse
  (`inv_mem`, via the subring of quotients `p.1 / s.1`). Its `hom` is the induced
  map `dom Γ →+* Ω`. The extension step `mem_dom_of_hom` shows that any `z ∈ L`
  whose image under a candidate hom — killed on the maximal ideal as `θ`, and
  vanishing on the polynomials that vanish at `z` — is already in `dom Γ`:
  the kernel of `aeval z` pushed to the residue field is principal, and
  `IsAlgClosed.exists_root` produces the value `ω` that defines `Γ' ⊇ Γ`, equal by
  maximality. Composing with a local subring `V` dominating `dom Γ`
  (`LocalSubring.exists_le_valuationSubring`) gives `z ∈ V → z ∈ dom Γ`, so `dom Γ`
  is a valuation subring (`main`), and `hom` is the required extension. The two
  retractions instantiate `φ` with the identity of an algebraically closed field.

  Assumes: mathlib `v4.34.0` only — nothing from earlier modules of the port.

  spec-pin: Theorems/Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean
  spec-pin: P2M/Sol/S_ValuationSubring_exists_ringHom_extend_of_isAlgClosed.lean
  spec-pin: Theorems/Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.lean
  spec-pin: P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.lean
  spec-pin: Theorems/Thm_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean
  spec-pin: P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction.lean
  Drift against `v4.34.0` — statements untouched.

  * port:100, 107 — `dif_pos` → `dite_eq_left` (deprecated alias).
  * port:131 — `Set.mem_setOf_eq` → `Set.mem_ofPred_eq` (deprecated alias).
  * port:161, 244, 253, 280, 386, 395, 460, 463, 465, 468, 469 — eleven `haveI` become
    `have`; port:286, 464 — two `letI` become `let` (`linter.style.haveILetI`'s own
    suggestion; every one is a local class hypothesis found by instance search).
  * the pin's `import Mathlib` becomes the nine named modules above; its `solution`
    wrapper is not ported.

-/

import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Order.Zorn
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Tactic

set_option autoImplicit false

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

/-- A subring of `L × Ω` meeting the `Ω`-axis only at `0`: the graph of a partial
ring hom `L → Ω`. -/
def IsGraph (Γ : Subring (L × Ω)) : Prop := ∀ a : Ω, ((0 : L), a) ∈ Γ → a = 0

namespace IsGraph

variable {Γ : Subring (L × Ω)}

/-- A graph is single-valued. -/
theorem snd_eq (hΓ : IsGraph Γ) {x : L} {a b : Ω} (ha : (x, a) ∈ Γ) (hb : (x, b) ∈ Γ) : a = b := by
  have h := Γ.sub_mem ha hb
  rw [Prod.mk_sub_mk, sub_self] at h
  exact sub_eq_zero.mp (hΓ _ h)

/-- A graph's domain does not contain `0` at a nonzero value. -/
theorem fst_ne_zero (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) (ha : a ≠ 0) : x ≠ 0 := by
  rintro rfl; exact ha (hΓ a h)

/-- The domain of a graph, as a subring of `L`. -/
def dom (Γ : Subring (L × Ω)) : Subring L := Γ.map (RingHom.fst L Ω)

/-- Membership in the domain: some value is paired with `x`. -/
theorem mem_dom {x : L} : x ∈ dom Γ ↔ ∃ a, (x, a) ∈ Γ := by
  simp only [dom, Subring.mem_map, RingHom.coe_fst, Prod.exists, exists_and_right, exists_eq_right]

/-- The value of the graph at `x`, `0` off the domain. -/
noncomputable def fn (Γ : Subring (L × Ω)) (x : L) : Ω :=
  open Classical in if h : ∃ a, (x, a) ∈ Γ then Classical.choose h else 0

/-- `fn` reads off the second coordinate. -/
theorem fn_spec (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) : fn Γ x = a := by
  unfold fn
  rw [dite_eq_left ⟨a, h⟩]
  exact hΓ.snd_eq (Classical.choose_spec (⟨a, h⟩ : ∃ a, (x, a) ∈ Γ)) h

/-- The graph meets the domain exactly in its own values. -/
theorem mem_of_mem_dom {x : L} (hx : x ∈ dom Γ) : (x, fn Γ x) ∈ Γ := by
  obtain ⟨a, ha⟩ := mem_dom.mp hx
  unfold fn
  rw [dite_eq_left ⟨a, ha⟩]
  exact Classical.choose_spec (⟨a, ha⟩ : ∃ a, (x, a) ∈ Γ)

/-- The ring hom of a graph, on its domain. -/
noncomputable def hom (hΓ : IsGraph Γ) : dom Γ →+* Ω where
  toFun x := fn Γ x
  map_one' := hΓ.fn_spec Γ.one_mem
  map_mul' x y := hΓ.fn_spec (by simpa using Γ.mul_mem (mem_of_mem_dom x.2) (mem_of_mem_dom y.2))
  map_zero' := hΓ.fn_spec Γ.zero_mem
  map_add' x y := hΓ.fn_spec (by simpa using Γ.add_mem (mem_of_mem_dom x.2) (mem_of_mem_dom y.2))

/-- `hom` is `fn`. -/
theorem hom_apply (hΓ : IsGraph Γ) (x : dom Γ) : hΓ.hom x = fn Γ x := rfl

/-- `hom` reads off the second coordinate on the graph. -/
theorem hom_eq_of_mem (hΓ : IsGraph Γ) {x : L} {a : Ω} (h : (x, a) ∈ Γ) :
    hΓ.hom ⟨x, mem_dom.mpr ⟨a, h⟩⟩ = a := hΓ.fn_spec h

end IsGraph

/-- The graph of a ring hom `R →+* Ω`, as a subring of `L × Ω`. -/
def graph (R : Subring L) (φ : R →+* Ω) : Subring (L × Ω) :=
  ((R.subtype).prod (φ)).range.copy {p | ∃ h : p.1 ∈ R, φ ⟨p.1, h⟩ = p.2} (by
    ext ⟨x, a⟩
    simp only [Set.mem_ofPred_eq, RingHom.coe_range, Set.mem_range, RingHom.prod_apply, Prod.mk.injEq,
      Subring.coe_subtype]
    constructor
    · rintro ⟨h, ha⟩; exact ⟨⟨x, h⟩, rfl, ha⟩
    · rintro ⟨⟨y, hy⟩, rfl, rfl⟩; exact ⟨hy, rfl⟩)

/-- Membership in the graph of `φ`. -/
theorem mem_graph {R : Subring L} {φ : R →+* Ω} {p : L × Ω} :
    p ∈ graph R φ ↔ ∃ h : p.1 ∈ R, φ ⟨p.1, h⟩ = p.2 := Iff.rfl

/-- The graph of a ring hom is a graph. -/
theorem isGraph_graph (R : Subring L) (φ : R →+* Ω) : IsGraph (graph R φ) := by
  rintro a ⟨h, ha⟩
  have h0 : (⟨(((0 : L), a) : L × Ω).1, h⟩ : R) = 0 := Subtype.ext rfl
  rw [h0, map_zero] at ha
  exact ha.symm

end ChevalleyHom

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

/-- The graphs above `Γ₀`. -/
def Above (Γ₀ : Subring (L × Ω)) : Set (Subring (L × Ω)) := {Γ | Γ₀ ≤ Γ ∧ IsGraph Γ}

/-- Zorn: `Γ₀` is contained in a maximal graph. -/
theorem exists_maximal (Γ₀ : Subring (L × Ω)) (h₀ : IsGraph Γ₀) :
    ∃ Γ, Γ₀ ≤ Γ ∧ Maximal (· ∈ Above Γ₀) Γ := by
  refine zorn_le_nonempty₀ (Above Γ₀) (fun c hc hchain y hy => ?_) Γ₀ ⟨le_rfl, h₀⟩
  have : Nonempty c := ⟨⟨y, hy⟩⟩
  have hdir : Directed (· ≤ ·) (fun Γ : c => (Γ : Subring (L × Ω))) :=
    hchain.directedOn.directed_val
  refine ⟨⨆ Γ : c, (Γ : Subring (L × Ω)), ⟨?_, ?_⟩, fun z hz => le_iSup (fun Γ : c => (Γ : Subring (L × Ω))) ⟨z, hz⟩⟩
  · exact (hc hy).1.trans (le_iSup (fun Γ : c => (Γ : Subring (L × Ω))) ⟨y, hy⟩)
  · intro a ha
    obtain ⟨Γ, hΓ⟩ := (Subring.mem_iSup_of_directed hdir).mp ha
    exact (hc Γ.2).2 a hΓ

section Maximal

variable {Γ₀ Γ : Subring (L × Ω)} (hmax : Maximal (· ∈ Above Γ₀) Γ)
include hmax

/-- A maximal graph is a graph. -/
theorem isGraph_of_maximal : IsGraph Γ := hmax.prop.2

/-- A maximal graph contains `Γ₀`. -/
theorem le_of_maximal : Γ₀ ≤ Γ := hmax.prop.1

/-- A maximal graph is not contained in a larger graph. -/
theorem eq_of_le (Γ' : Subring (L × Ω)) (hΓ' : IsGraph Γ') (hle : Γ ≤ Γ') : Γ' = Γ :=
  (hmax.eq_of_ge ⟨hmax.prop.1.trans hle, hΓ'⟩ hle)

/-- The domain of a maximal graph is closed under inverse. -/
theorem inv_mem {x : L} {a : Ω} (h : (x, a) ∈ Γ) (ha : a ≠ 0) : (x⁻¹, a⁻¹) ∈ Γ := by
  have hΓ := isGraph_of_maximal hmax

  let Γ' : Subring (L × Ω) :=
    { carrier := {q | ∃ p ∈ Γ, ∃ s ∈ Γ, s.2 ≠ 0 ∧ q = (p.1 / s.1, p.2 / s.2)}
      mul_mem' := by
        rintro _ _ ⟨p, hp, s, hs, hs0, rfl⟩ ⟨p', hp', s', hs', hs0', rfl⟩
        refine ⟨p * p', Γ.mul_mem hp hp', s * s', Γ.mul_mem hs hs', mul_ne_zero hs0 hs0', ?_⟩
        ext <;> simp [div_mul_div_comm]
      one_mem' := ⟨1, Γ.one_mem, 1, Γ.one_mem, one_ne_zero, by ext <;> simp⟩
      add_mem' := by
        rintro _ _ ⟨p, hp, s, hs, hs0, rfl⟩ ⟨p', hp', s', hs', hs0', rfl⟩
        have hs1 : s.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs) hs0
        have hs1' : s'.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs') hs0'
        refine ⟨p * s' + p' * s, Γ.add_mem (Γ.mul_mem hp hs') (Γ.mul_mem hp' hs), s * s',
          Γ.mul_mem hs hs', mul_ne_zero hs0 hs0', ?_⟩
        ext
        · simp only [Prod.fst_add, Prod.fst_mul]; rw [div_add_div _ _ hs1 hs1']; ring
        · simp only [Prod.snd_add, Prod.snd_mul]; rw [div_add_div _ _ hs0 hs0']; ring
      zero_mem' := ⟨0, Γ.zero_mem, 1, Γ.one_mem, one_ne_zero, by ext <;> simp⟩
      neg_mem' := by
        rintro _ ⟨p, hp, s, hs, hs0, rfl⟩
        exact ⟨-p, Γ.neg_mem hp, s, hs, hs0, by ext <;> simp [neg_div]⟩ }
  have hle : Γ ≤ Γ' := fun p hp => ⟨p, hp, 1, Γ.one_mem, one_ne_zero, by simp⟩
  have hΓ' : IsGraph Γ' := by
    rintro b ⟨p, hp, s, hs, hs0, hq⟩
    simp only [Prod.mk.injEq] at hq
    obtain ⟨h1, h2⟩ := hq
    have hs1 : s.1 ≠ 0 := hΓ.fst_ne_zero (by simpa using hs) hs0
    have hp1 : p.1 = 0 := by
      rcases div_eq_zero_iff.mp h1.symm with h | h
      · exact h
      · exact absurd h hs1
    have hp2 : p.2 = 0 := hΓ p.2 (by rwa [← hp1])
    rw [h2, hp2, zero_div]
  have heq := eq_of_le hmax Γ' hΓ' hle
  have : (x⁻¹, a⁻¹) ∈ Γ' := ⟨1, Γ.one_mem, (x, a), h, ha, by ext <;> simp⟩
  rwa [heq] at this

/-- The units of the domain are exactly the elements of nonzero value. -/
theorem isUnit_iff {x : IsGraph.dom Γ} : IsUnit x ↔ (isGraph_of_maximal hmax).hom x ≠ 0 := by
  have hΓ := isGraph_of_maximal hmax
  constructor
  · intro hu h0
    have := hu.map hΓ.hom
    rw [h0] at this
    exact not_isUnit_zero this
  · intro hne
    have hmem : ((x : L), IsGraph.fn Γ x) ∈ Γ := IsGraph.mem_of_mem_dom x.2
    have hinv := inv_mem hmax hmem hne
    have hx0 : (x : L) ≠ 0 := hΓ.fst_ne_zero hmem hne
    refine ⟨⟨x, ⟨(x : L)⁻¹, IsGraph.mem_dom.mpr ⟨_, hinv⟩⟩, ?_, ?_⟩, rfl⟩
    · exact Subtype.ext (mul_inv_cancel₀ hx0)
    · exact Subtype.ext (inv_mul_cancel₀ hx0)

/-- The domain of a maximal graph is a local ring. -/
theorem isLocalRing : IsLocalRing (IsGraph.dom Γ) := by
  have hΓ := isGraph_of_maximal hmax
  have : Nontrivial (IsGraph.dom Γ) := inferInstance
  refine IsLocalRing.of_nonunits_add fun a b ha hb => ?_
  rw [mem_nonunits_iff, isUnit_iff hmax, not_not] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/-- The maximal ideal of the domain is the graph of `0`. -/
theorem mem_maximalIdeal_iff (x : IsGraph.dom Γ) :
    haveI := isLocalRing hmax
    x ∈ IsLocalRing.maximalIdeal (IsGraph.dom Γ) ↔ (isGraph_of_maximal hmax).hom x = 0 := by
  have := isLocalRing hmax
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff hmax, not_not]

end Maximal

end ChevalleyHom

namespace ChevalleyHom

variable {L Ω : Type*} [Field L] [Field Ω]

section Extend

variable {Γ₀ Γ : Subring (L × Ω)} (hmax : Maximal (· ∈ Above Γ₀) Γ)
include hmax

open IsGraph Polynomial in

/-- The extension step: a `z ∈ L` which a candidate hom `θ` (killed on the maximal
ideal, and vanishing on the polynomials vanishing at `z`) does not see is already
in the domain of `Γ`. -/
theorem mem_dom_of_hom [IsAlgClosed Ω] (z : L) {F : Type*} [Field F]
    (θ : Polynomial (dom Γ) →+* F)
    (hθm : haveI := isLocalRing hmax; ∀ b ∈ IsLocalRing.maximalIdeal (dom Γ), θ (C b) = 0)
    (hθz : ∀ p : Polynomial (dom Γ), aeval z p = 0 → θ p = 0) :
    z ∈ dom Γ := by
  classical
  have := isLocalRing hmax
  have hΓ := isGraph_of_maximal hmax

  let B := dom Γ
  let m := IsLocalRing.maximalIdeal B
  let k := B ⧸ m
  let : Field k := Ideal.Quotient.field m
  let π : Polynomial B →+* Polynomial k := mapRingHom (Ideal.Quotient.mk m)
  have hπ : Function.Surjective π := map_surjective _ Ideal.Quotient.mk_surjective
  let ev : Polynomial B →+* L := (aeval z : Polynomial B →ₐ[B] L).toRingHom
  let K₀ : Ideal (Polynomial B) := RingHom.ker ev
  let Jk : Ideal (Polynomial k) := K₀.map π

  have hθker : ∀ q, π q = 0 → θ q = 0 := by
    intro q hq
    have hq' : q ∈ RingHom.ker π := hq
    rw [ker_mapRingHom, Ideal.mk_ker] at hq'
    have hle : Ideal.map (C : B →+* Polynomial B) m ≤ RingHom.ker θ :=
      Ideal.map_le_iff_le_comap.mpr fun b hb => Ideal.mem_comap.mpr (RingHom.mem_ker.mpr (hθm b hb))
    exact hle hq'

  have hJk : Jk ≠ ⊤ := by
    intro htop
    have h1 : (1 : Polynomial k) ∈ Jk := htop ▸ Submodule.mem_top
    obtain ⟨q, hq, hq1⟩ := (Ideal.mem_map_iff_of_surjective π hπ).mp h1
    have hq0 : θ q = 0 := hθz q hq
    have h1q : θ (1 - q) = 0 := hθker _ (by rw [map_sub, map_one, hq1, sub_self])
    rw [map_sub, map_one, hq0, sub_zero] at h1q
    exact one_ne_zero h1q

  obtain ⟨h, hh⟩ := (IsPrincipalIdealRing.principal Jk).principal
  have hhu : ¬ IsUnit h := fun hu => hJk (by rw [hh, Ideal.submodule_span_eq, Ideal.span_singleton_eq_top]; exact hu)
  have hker : ∀ b ∈ m, hΓ.hom b = 0 := fun b hb => (mem_maximalIdeal_iff hmax b).mp hb
  let ι : k →+* Ω := Ideal.Quotient.lift m hΓ.hom hker
  obtain ⟨ω, hω⟩ : ∃ ω : Ω, (h.map ι).eval ω = 0 := by
    by_cases h0 : h = 0
    · exact ⟨0, by simp [h0]⟩
    · have hdeg : (h.map ι).degree ≠ 0 := by
        rw [degree_map]
        exact fun hd => hhu (isUnit_iff_degree_eq_zero.mpr hd)
      obtain ⟨ω, hω⟩ := IsAlgClosed.exists_root (h.map ι) hdeg
      exact ⟨ω, hω⟩

  let G : Polynomial B →+* Ω := eval₂RingHom (ι.comp (Ideal.Quotient.mk m)) ω
  have hG : ∀ q ∈ K₀, G q = 0 := by
    intro q hq
    have hπq : π q ∈ Jk := Ideal.mem_map_of_mem π hq
    rw [hh, Ideal.submodule_span_eq, Ideal.mem_span_singleton] at hπq
    obtain ⟨r, hr⟩ := hπq
    have : G q = (π q).eval₂ ι ω := by
      simp only [G, π, coe_eval₂RingHom, coe_mapRingHom, eval₂_map]
    rw [this, hr, eval₂_mul, ← eval_map, hω, zero_mul]

  let S : Subring L := ev.range
  let e := RingHom.quotientKerEquivRange ev
  let g' : S →+* Ω := (Ideal.Quotient.lift K₀ G hG).comp e.symm.toRingHom
  have hg' : ∀ q : Polynomial B, g' ⟨ev q, ⟨q, rfl⟩⟩ = G q := by
    intro q
    have he : e (Ideal.Quotient.mk K₀ q) = ⟨ev q, ⟨q, rfl⟩⟩ := rfl
    show (Ideal.Quotient.lift K₀ G hG) (e.symm ⟨ev q, ⟨q, rfl⟩⟩) = G q
    rw [← he, RingEquiv.symm_apply_apply, Ideal.Quotient.lift_mk]

  let Γ' : Subring (L × Ω) := (S.subtype.prod g').range
  have hΓ' : IsGraph Γ' := by
    rintro a ⟨s, hs⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq, Subring.coe_subtype] at hs
    obtain ⟨hs1, hs2⟩ := hs
    have : s = 0 := Subtype.ext hs1
    rw [← hs2, this, map_zero]
  have evC : ∀ b : B, ev (C b) = (b : L) := fun b => by
    show aeval z (C b) = (b : L)
    rw [aeval_C]
    rfl
  have hle : Γ ≤ Γ' := by
    rintro ⟨x, a⟩ hxa
    have hx : x ∈ B := mem_dom.mpr ⟨a, hxa⟩
    have hmemS : x ∈ S := ⟨C ⟨x, hx⟩, evC ⟨x, hx⟩⟩
    refine ⟨⟨x, hmemS⟩, ?_⟩
    simp only [RingHom.prod_apply, Prod.mk.injEq, Subring.coe_subtype, true_and]
    have h1 : g' ⟨x, hmemS⟩ = G (C ⟨x, hx⟩) := by
      have h2 := hg' (C ⟨x, hx⟩)
      have h3 : (⟨ev (C ⟨x, hx⟩), ⟨C ⟨x, hx⟩, rfl⟩⟩ : S) = ⟨x, hmemS⟩ := Subtype.ext (evC ⟨x, hx⟩)
      rw [h3] at h2
      exact h2
    rw [h1]
    simp only [G, coe_eval₂RingHom, eval₂_C, RingHom.comp_apply]
    show ι (Ideal.Quotient.mk m ⟨x, hx⟩) = a
    rw [Ideal.Quotient.lift_mk]
    exact hΓ.hom_eq_of_mem hxa
  have heq := eq_of_le hmax Γ' hΓ' hle
  have evX : ev X = z := by show aeval z (X : Polynomial B) = z; exact aeval_X z
  have hz : ((z, g' ⟨z, ⟨X, evX⟩⟩) : L × Ω) ∈ Γ' := ⟨⟨z, ⟨X, evX⟩⟩, rfl⟩
  rw [heq] at hz
  exact mem_dom.mpr ⟨_, hz⟩

end Extend

open IsGraph Polynomial in
/-- Chevalley's theorem: a ring hom `R →+* Ω` with `Ω` algebraically closed extends to
a valuation subring of `L` containing `R`, with the maximal ideal as its kernel. -/
private theorem main [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O := by
  classical
  obtain ⟨Γ, -, hmax⟩ := exists_maximal (graph R φ) (isGraph_graph R φ)
  have hΓ := isGraph_of_maximal hmax
  have := isLocalRing hmax
  let B := dom Γ

  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk B : LocalSubring L)
  obtain ⟨hBV, hloc⟩ := LocalSubring.le_def.mp hV

  have key : ∀ z : L, z ∈ V → z ∈ B := by
    intro z hz
    let incl : B →+* V := Subring.inclusion hBV
    have : IsLocalHom incl := hloc
    let θ : Polynomial B →+* IsLocalRing.ResidueField V :=
      (IsLocalRing.residue V).comp (eval₂RingHom incl ⟨z, hz⟩)
    refine mem_dom_of_hom hmax z θ (fun b hb => ?_) (fun p hp => ?_)
    · simp only [θ, RingHom.comp_apply, coe_eval₂RingHom, eval₂_C, IsLocalRing.residue_eq_zero_iff]
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hb ⊢
      exact fun hu => hb (IsUnit.of_map incl _ hu)
    · simp only [θ, RingHom.comp_apply, coe_eval₂RingHom]
      have hval : (V.subtype) (eval₂ incl ⟨z, hz⟩ p) = aeval z p := by
        rw [hom_eval₂]
        rfl
      have : eval₂ incl ⟨z, hz⟩ p = 0 := by
        apply Subtype.val_injective
        show (V.subtype) (eval₂ incl ⟨z, hz⟩ p) = ((0 : V) : L)
        rw [hval, hp]
        rfl
      rw [this, map_zero]
  have hval : ∀ z : L, z ∈ B ∨ z⁻¹ ∈ B := fun z =>
    (V.mem_or_inv_mem z).imp (key z) (key z⁻¹)
  let O : ValuationSubring L := { toSubring := B, mem_or_inv_mem' := hval }
  have hR : R ≤ O.toSubring := fun r hr => mem_dom.mpr ⟨φ ⟨r, hr⟩, mem_graph.mpr ⟨hr, rfl⟩ |> le_of_maximal hmax⟩
  refine ⟨O, hR, hΓ.hom, ?_, ?_⟩
  · ext r
    exact hΓ.hom_eq_of_mem (le_of_maximal hmax (mem_graph.mpr ⟨r.2, rfl⟩))
  · ext x
    rw [RingHom.mem_ker]
    exact (mem_maximalIdeal_iff hmax x).symm

end ChevalleyHom

namespace ValuationSubring

/-- Chevalley's theorem: a ring hom from a subring of `L` into an algebraically closed
field extends to a valuation subring of `L`, with kernel the maximal ideal. -/
theorem exists_ringHom_extend_of_isAlgClosed
    {L Ω : Type*} [Field L] [Field Ω] [IsAlgClosed Ω] (R : Subring L) (φ : R →+* Ω) :
    ∃ (O : ValuationSubring L) (h : R ≤ O.toSubring) (ψ : O →+* Ω),
      ψ.comp (Subring.inclusion h) = φ ∧ RingHom.ker ψ = IsLocalRing.maximalIdeal O :=
  ChevalleyHom.main R φ

end ValuationSubring

namespace IsAlgClosed

/-- The retraction of an extension of algebraically closed fields onto the base,
which moreover sends a prescribed finite set of nonzero elements of `E` to valuation
`1`. -/
theorem exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (S : Finset E) (hS : (0 : E) ∉ S) :
    ∃ (A : ValuationSubring E) (hK : ∀ c : K, algebraMap K E c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      (∀ c : K, σ ⟨algebraMap K E c, hK c⟩ = c) ∧
      ∀ s ∈ S, A.valuation s = 1 := by
  classical

  let T : Finset E := S ∪ S.image (·⁻¹)
  let R : Subalgebra K E := Algebra.adjoin K (↑T : Set E)
  have hSmemR : ∀ s ∈ S, (s : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _ hs))
  have hSinvR : ∀ s ∈ S, (s⁻¹ : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)))

  have hRFG : R.FG := ⟨T, rfl⟩
  have : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).mp hRFG

  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (R := K) (A := R)
      (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  have : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  have : Algebra.IsIntegral K (R ⧸ m) := Algebra.IsIntegral.of_finite K (R ⧸ m)
  have hsurj : Function.Surjective (algebraMap K (R ⧸ m)) := by
    intro x
    have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    exact minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  let e : K ≃+* (R ⧸ m) :=
    RingEquiv.ofBijective (algebraMap K (R ⧸ m)) ⟨(algebraMap K _).injective, hsurj⟩
  let φ : R →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have hφK : ∀ c : K, φ (algebraMap K R c) = c := fun c => by
    show e.symm (Ideal.Quotient.mk m (algebraMap K R c)) = c
    have h1 : (Ideal.Quotient.mk m) (algebraMap K R c) = algebraMap K (R ⧸ m) c := rfl
    rw [h1]; exact e.symm_apply_apply c

  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) R.toSubring φ
  have hKO : ∀ c : K, algebraMap K E c ∈ O := fun c => hRO (R.algebraMap_mem c)
  refine ⟨O, hKO, ψ, hker, ?_, ?_⟩
  · intro c
    have h0 : (⟨algebraMap K E c, hKO c⟩ : O)
        = Subring.inclusion hRO ⟨algebraMap K E c, R.algebraMap_mem c⟩ := rfl
    rw [h0, ← RingHom.comp_apply, hψ]
    exact hφK c
  ·
    intro s hs
    have hs0 : s ≠ 0 := fun h => hS (h ▸ hs)
    have hsO : s ∈ O := hRO (hSmemR s hs)
    have hsiO : s⁻¹ ∈ O := hRO (hSinvR s hs)
    have hsu : IsUnit (⟨s, hsO⟩ : O) :=
      ⟨⟨⟨s, hsO⟩, ⟨s⁻¹, hsiO⟩,
          Subtype.ext (mul_inv_cancel₀ hs0), Subtype.ext (inv_mul_cancel₀ hs0)⟩, rfl⟩
    exact (O.valuation_eq_one_iff ⟨s, hsO⟩).mp hsu

/-- The retraction of an extension of algebraically closed fields onto the base:
a valuation subring of `K'` containing `K` and a ring hom back to `K` which is the
identity on `K` and has the maximal ideal as kernel. -/
theorem exists_valuationSubring_ringHom_retraction
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by
  let f : K →+* K' := algebraMap K K'
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) f.range e.symm.toRingHom
  refine ⟨O, fun c => hRO ⟨c, rfl⟩, ψ, hker, fun c => ?_⟩
  have h1 : ψ (Subring.inclusion hRO ⟨f c, ⟨c, rfl⟩⟩) = e.symm ⟨f c, ⟨c, rfl⟩⟩ := by
    rw [← RingHom.comp_apply, hψ]; rfl
  have h2 : e.symm ⟨f c, ⟨c, rfl⟩⟩ = c := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h2] at h1
  exact h1

end IsAlgClosed
