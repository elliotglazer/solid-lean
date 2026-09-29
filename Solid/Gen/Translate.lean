module

public import Solid.Calc.Definability
public import Solid.Calc.Theory

/-!
# The translation lemma of the first-order bridge

A *syntactic* interpretation of a signature `Sig'` in a structure `M` is an
interpretation whose domains, equivalences and relations are first-order
definable in `M` (with parameters): a `GenInterp M.U M.defSys.toClassSys
Sig'`.  The translation lemma says that every relation first-order definable
(with parameters) in the interpreted structure `N = I.model` has definable
preimages in `M`, i.e. `N.defSys ≤ I.induced`.  This is the usual
translation `φ ↦ φ^I` of formulas along an interpretation, obtained here
without writing the translated formula down: the induced class system is a
class system containing the atoms of `N`, so it contains every relation
defined by a formula of `N` (`Formula.def_mem`); fixing the parameters keeps
it in the system; and the preimage of a relation only depends on its tuples
of the profile in question.

Instantiating the semantic solidity theorem `ClauseFamily.solid` with the
definable class systems everywhere then gives Enayat's first-order statement
(`ClauseFamily.solid_fo`), and for `T_L` in particular (`TL_solid_fo`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-! ### Fixing parameters in a class system -/

namespace ClassSys

variable {U : ℕ → Type u} (𝒟 : ClassSys U)

/-- Instantiating the last coordinate by a parameter. -/
theorem withParam_mem {k : ℕ} (p : Sorted.El U) {C : Sorted.Rel U (k + 1)} (hC : C ∈ 𝒟.D (k + 1)) :
    ({t | Fin.snoc (α := fun _ => Sorted.El U) t p ∈ C} : Sorted.Rel U k) ∈ 𝒟.D k := by
  have h := 𝒟.exists_mem p.1 (𝒟.inter_mem
    (𝒟.reindex_mem (fun _ : Fin 1 => Fin.last k) (𝒟.param_mem p)) hC)
  have e : ({t | Fin.snoc (α := fun _ => Sorted.El U) t p ∈ C} : Sorted.Rel U k) =
      Sorted.exists_ U p.1 (Sorted.reindex U (fun _ : Fin 1 => Fin.last k) (Sorted.paramRel U p) ∩ C) := by
    ext t
    show Fin.snoc t p ∈ C ↔ ∃ z : Sorted.El U, z.1 = p.1 ∧
      Fin.snoc t z ∈ (Sorted.reindex U (fun _ : Fin 1 => Fin.last k) (Sorted.paramRel U p) ∩ C)
    constructor
    · intro h
      refine ⟨p, rfl, ?_, h⟩
      show Fin.snoc (α := fun _ => Sorted.El U) t p (Fin.last k) = p
      rw [Fin.snoc_last]
    · rintro ⟨z, -, hz, hzC⟩
      have hzp : z = p := by
        have := hz
        simp only [Sorted.reindex, Sorted.paramRel, Set.mem_setOf_eq, Function.comp_apply,
          Fin.snoc_last] at this
        exact this
      rw [hzp] at hzC
      exact hzC
  rw [e]; exact h

/-- Fixing the trailing coordinates by parameters. -/
theorem fixTail_mem : ∀ {m k : ℕ} {C : Sorted.Rel U (k + m)}, C ∈ 𝒟.D (k + m) →
    ∀ η : Fin m → Sorted.El U, ({u | Fin.append u η ∈ C} : Sorted.Rel U k) ∈ 𝒟.D k
  | 0, k, C, hC, η => by
    have e : ({u | Fin.append u η ∈ C} : Sorted.Rel U k) = C := by
      ext u
      show Fin.append u η ∈ C ↔ u ∈ C
      have : Fin.append u η = u := by
        funext i
        exact Fin.append_left u η ⟨i.1, by omega⟩
      rw [this]
    rw [e]; exact hC
  | m + 1, k, C, hC, η => by
    have h1 := 𝒟.withParam_mem (k := k + m) (η (Fin.last m)) hC
    have h2 := fixTail_mem h1 (Fin.init η)
    have e : ({u | Fin.append u η ∈ C} : Sorted.Rel U k) =
        {u | Fin.append u (Fin.init η) ∈ ({t | Fin.snoc (α := fun _ => Sorted.El U) t (η (Fin.last m)) ∈ C} :
          Sorted.Rel U (k + m))} := by
      ext u
      show Fin.append u η ∈ C ↔ Fin.snoc (Fin.append u (Fin.init η)) (η (Fin.last m)) ∈ C
      rw [← Formula.append_snoc u (Fin.init η) (η (Fin.last m)), Fin.snoc_init_self]
    rw [e]; exact h2

/-- Fixing the leading coordinates by parameters. -/
theorem fixInit_mem {m k : ℕ} {C : Sorted.Rel U (m + k)} (hC : C ∈ 𝒟.D (m + k))
    (η : Fin m → Sorted.El U) : ({u | Fin.append η u ∈ C} : Sorted.Rel U k) ∈ 𝒟.D k := by
  have h1 := 𝒟.reindex_mem (ClassSystem.TDef.rot m k) hC
  have h2 := 𝒟.fixTail_mem h1 η
  have e : ({u | Fin.append η u ∈ C} : Sorted.Rel U k) =
      {u | Fin.append u η ∈ Sorted.reindex U (ClassSystem.TDef.rot m k) C} := by
    ext u
    show Fin.append η u ∈ C ↔ (Fin.append u η) ∘ ClassSystem.TDef.rot m k ∈ C
    rw [ClassSystem.TDef.append_comp_rot]
  rw [e]; exact h2

end ClassSys

/-! ### The translation lemma -/

namespace GenInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} {Sig : Signature} (I : GenInterp U 𝒟 Sig)

/-- The preimage of a relation for the profile `b` only depends on its tuples
of profile `b`. -/
theorem preimage_inter_profileRel {k : ℕ} (b : Fin k → ℕ) (C : Sorted.Rel I.Carrier k) :
    I.preimage b (C ∩ Sorted.profileRel I.Carrier b) = I.preimage b C := by
  ext t
  constructor
  · rintro ⟨u, hu, hC, -⟩
    exact ⟨u, hu, hC⟩
  · rintro ⟨u, hu, hC⟩
    exact ⟨u, hu, hC, fun i => (hu i).1⟩

/-- **Translation lemma.**  Every relation first-order definable with
parameters in the interpreted structure has admissible preimages: the
definable class system of `I.model` lies below the induced one. -/
theorem defSys_le_induced : ∀ (k : ℕ) (C : Sorted.Rel I.Carrier k),
    C ∈ I.model.defSys.D k → C ∈ I.induced.D k := by
  intro k C hC
  refine (I.mem_induced_iff C).2 fun b => ?_
  obtain ⟨a, ps, φ, p, -, hφ⟩ := (I.model.mem_defSys_iff C).1 hC b
  -- the definition of `C` at the profile `b`, as a relation of the induced system
  have hdef : φ.Def I.model ∈ I.induced.D (a + k) := Formula.def_mem I.induced φ
  have hfix : ({t | Fin.append p t ∈ φ.Def I.model} : Sorted.Rel I.Carrier k) ∈ I.induced.D k :=
    I.induced.toClassSys.fixInit_mem hdef p
  have hC' : (C ∩ Sorted.profileRel I.Carrier b : Sorted.Rel I.Carrier k) =
      ({t | Fin.append p t ∈ φ.Def I.model} ∩ Sorted.profileRel I.Carrier b : Sorted.Rel I.Carrier k) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Formula.mem_Def]
    constructor
    · rintro ⟨hCt, hb⟩; exact ⟨(hφ t hb).1 hCt, hb⟩
    · rintro ⟨hs, hb⟩; exact ⟨(hφ t hb).2 hs, hb⟩
  rw [← I.preimage_inter_profileRel b C, hC']
  exact (I.mem_induced_iff _).1 (I.induced.inter_mem hfix (I.induced.toClassSys.profileRel_mem b)) b

end GenInterp

/-! ### First-order solidity -/

namespace ClauseFamily

variable (F : ClauseFamily.{u})

/-- **First-order solidity of `T(𝔉)`** (Enayat's notion): for models
`M ⊳ N ⊳ P` of `T(𝔉)` — each a model for its own first-order definable
class system — given by syntactic interpretations `I` (of `N` in `M`) and `J`
(of `P` in `N`), and an `M`-definable isomorphism `M ≅ P`, there is an
`M`-definable isomorphism `M ≅ N`. -/
theorem solid_fo (M : Str.{u} F.sig) (hM : F.IsGenModel ⟨M, M.defSys⟩)
    (I : GenInterp M.U M.defSys.toClassSys F.sig) (hN : F.IsGenModel ⟨I.model, I.model.defSys⟩)
    (J : GenInterp I.model.U I.model.defSys.toClassSys F.sig)
    (hP : F.IsGenModel ⟨J.model, J.model.defSys⟩)
    (i : GenIso M J.model) (hi : i.DefinableIn M.defSys.toClassSys (I.pres.comp J.pres)) :
    ∃ h : GenIso M I.model, h.DefinableIn M.defSys.toClassSys I.pres :=
  F.solid ⟨M, M.defSys⟩ hM I I.model.defSys I.defSys_le_induced hN J J.model.defSys hP i hi

end ClauseFamily

end SolidLean.Solid

namespace SolidLean.Calc

open SolidLean.Solid

/-- First-order solidity of `T_L`. -/
theorem TL_solid_fo (M : Str.{u} LAnn.{u}.sig) (hM : LAnn.IsGenModel ⟨M, M.defSys⟩)
    (I : GenInterp M.U M.defSys.toClassSys LAnn.sig)
    (hN : LAnn.IsGenModel ⟨I.model, I.model.defSys⟩)
    (J : GenInterp I.model.U I.model.defSys.toClassSys LAnn.sig)
    (hP : LAnn.IsGenModel ⟨J.model, J.model.defSys⟩)
    (i : GenIso M J.model) (hi : i.DefinableIn M.defSys.toClassSys (I.pres.comp J.pres)) :
    ∃ h : GenIso M I.model, h.DefinableIn M.defSys.toClassSys I.pres :=
  LAnn.solid_fo M hM I hN J hP i hi

end SolidLean.Calc
