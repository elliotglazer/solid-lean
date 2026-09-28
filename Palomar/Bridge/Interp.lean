import Palomar.Bridge.ModelH
import Solid.Interpretation
import Solid.Gen.Translate

/-!
# Bridge, part 3: interpretations, presentations and definable isomorphisms

A `Palomar` interpretation of the language of `H` in `T` is an interpretation
of the development (`SInterp`) for the definable class system of `T`, with
the same interpreted tower and the same presentation.  Presentations and their
composites, and isomorphisms with their definability, correspond likewise.
The translation lemma `SInterp.defSys_le_induced` says that the definable
classes of the interpreted tower lie below the induced class system, which
is the hypothesis `𝒩 ⊆ I.induced` of `tower_solid`.
-/

universe u

namespace SolidLean.Solid

open Classical

/-! ### The translation lemma for interpretations of the tower signature -/

namespace SortInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} (I : SortInterp U 𝒟)

/-- The preimage of a relation for the profile `b` only depends on its tuples
of profile `b`. -/
theorem preimage_inter_profileRel' {k : ℕ} (b : Fin k → ℕ) (C : Sorted.Rel I.Carrier k) :
    I.preimage b (C ∩ Sorted.profileRel I.Carrier b) = I.preimage b C := by
  ext t
  constructor
  · rintro ⟨u, hu, hC, -⟩
    exact ⟨u, hu, hC⟩
  · rintro ⟨u, hu, hC⟩
    exact ⟨u, hu, hC, fun i => (hu i).1⟩

end SortInterp

namespace SInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} (I : SInterp U 𝒟)

/-- **Translation lemma.**  Every relation first-order definable with
parameters in the interpreted tower has admissible preimages, so the definable
class system of `I.model` lies below the induced one. -/
theorem defSys_le_induced : ∀ (k : ℕ) (C : Sorted.Rel I.Carrier k),
    C ∈ I.model.toStr.defSys.D k → C ∈ I.induced.D k := by
  intro k C hC
  refine (I.mem_inducedSys_iff C).2 fun b => ?_
  obtain ⟨a, ps, φ, p, -, hφ⟩ := (I.model.toStr.mem_defSys_iff C).1 hC b
  have hdef : φ.Def I.model.toStr ∈ I.induced.toStrSys.D (a + k) :=
    Formula.def_mem I.induced.toStrSys φ
  have hfix : ({t | Fin.append p t ∈ φ.Def I.model.toStr} : Sorted.Rel I.Carrier k) ∈ I.induced.D k :=
    I.induced.toClassSys.fixInit_mem hdef p
  have hC' : (C ∩ Sorted.profileRel I.Carrier b : Sorted.Rel I.Carrier k) =
      ({t | Fin.append p t ∈ φ.Def I.model.toStr} ∩ Sorted.profileRel I.Carrier b :
        Sorted.Rel I.Carrier k) := by
    ext t
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Formula.mem_Def]
    constructor
    · rintro ⟨hCt, hb⟩; exact ⟨(hφ t hb).1 hCt, hb⟩
    · rintro ⟨hs, hb⟩; exact ⟨(hφ t hb).2 hs, hb⟩
  rw [← I.preimage_inter_profileRel' b C, hC']
  exact (I.mem_inducedSys_iff _).1
    (I.induced.inter_mem hfix (I.induced.toClassSys.profileRel_mem b)) b

end SInterp

end SolidLean.Solid

namespace SolidLean.Palomar

open SolidLean.Solid

/-! ### Interpretations -/

namespace Interp

variable {T : Tower.{u}} (I : Interp T)

/-- A `Palomar` interpretation as an interpretation of the development, for
the definable class system. -/
noncomputable def toSolid : SInterp T.toMem.U T.defSys.toClassSys where
  a := I.a
  dom := I.dom
  eqv := I.eqv
  eqv_refl := I.eqv_refl
  eqv_symm := I.eqv_symm
  eqv_trans := I.eqv_trans
  eqv_dom := I.eqv_dom
  dom_def n := (T.definableSet_iff _ _).1 (I.dom_def n)
  eqv_def n := (T.defOn_iff _ _ _).1 (I.eqv_def n)
  memC := I.memC
  memC_congr := I.memC_congr
  jC := I.jC
  jC_total := I.jC_total
  jC_func := I.jC_func
  jC_congr := I.jC_congr
  jC_congr_right := I.jC_congr_right
  kappaC := I.kappaC
  kappaC_exists := I.kappaC_exists
  kappaC_unique := I.kappaC_unique
  kappaC_congr := I.kappaC_congr
  memC_def n := (T.defOn_iff _ _ _).1 (I.memC_def n)
  jC_def n := (T.definable_iff _ _).1 (I.jC_def n)
  kappaC_def n := (T.definableSet_iff _ _).1 (I.kappaC_def n)

/-- The interpreted towers agree. -/
theorem toSolid_model : I.toSolid.model = I.Model.toMem := rfl

end Interp

/-! ### Presentations -/

namespace Presentation

variable {T P : Tower.{u}}

/-- A `Palomar` presentation as a presentation of the development. -/
def toSolid (p : Presentation T P) : Solid.Presentation T.toMem.U P.toMem.U where
  a := p.a
  rep := p.rep
  surj := p.surj

theorem toSolid_comp {N : Tower.{u}} (p : Presentation T N) (q : Presentation N P) :
    (p.comp q).toSolid = p.toSolid.comp q.toSolid := rfl

end Presentation

theorem Interp.toSolid_pres {T : Tower.{u}} (I : Interp T) : I.pres.toSolid = I.toSolid.pres := rfl

/-! ### Isomorphisms -/

namespace Iso

variable {T N : Tower.{u}}

/-- A `Palomar` isomorphism as a tower isomorphism. -/
def toSolid (i : Iso T N) : TowerIso T.toMem N.toMem where
  toFun := i.toFun
  bijective := i.bijective
  mem_iff := i.mem_iff
  j_comm := i.j_comm
  κ_comm := i.κ_comm

/-- A tower isomorphism as a `Palomar` isomorphism. -/
def ofSolid (i : TowerIso T.toMem N.toMem) : Iso T N where
  toFun := i.toFun
  bijective := i.bijective
  mem_iff := i.mem_iff
  j_comm := i.j_comm
  κ_comm := i.κ_comm

theorem definableIn_iff (i : Iso T N) (pr : Presentation T N) :
    i.DefinableIn pr ↔ i.toSolid.DefinableIn T.defSys pr.toSolid := by
  unfold DefinableIn TowerIso.DefinableIn
  exact forall_congr' fun n => T.definable_iff 2 _

theorem definableIn_ofSolid_iff (i : TowerIso T.toMem N.toMem) (pr : Presentation T N) :
    (ofSolid i).DefinableIn pr ↔ i.DefinableIn T.defSys pr.toSolid := by
  unfold DefinableIn TowerIso.DefinableIn
  exact forall_congr' fun n => T.definable_iff 2 _

end Iso

end SolidLean.Palomar
