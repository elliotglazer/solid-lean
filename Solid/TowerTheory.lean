module

public import Solid.SetTheory

/-!
# The tower theory `H`

Draft 2, §2.1.  A model of `H` is a tower with a class system such that

1. each sort, with the classes restricted to it, satisfies ZFC (Separation
   and Replacement for classes of the system);
2. in sort `n+1`, `κ n` is inaccessible and `j n` is a membership
   isomorphism from sort `n` onto the rank segment `V(κ n)`;
3. in sort `n+2`, `κ (n+1)` is the least inaccessible above `j (n+1) (κ n)`;
4. in sort `1`, there is no greatest inaccessible below `κ 0`.

Every scheme is stated for the classes of the system, so these are the
axioms of `H` read schematically over a semantic notion of definability.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-- The data of a structure for `H`: a tower and a class system on it. -/
structure TowerWithClasses where
  T : MemTower.{u}
  𝒟 : ClassSystem T

namespace TowerWithClasses

variable (M : TowerWithClasses.{u})

/-- Definability of a relation on sort `n`. -/
def DefOn (n k : ℕ) (C : (M.T.sortStr n).Rel k) : Prop := M.𝒟.DefOn n k C

/-- The ZFC axioms in sort `n`, with schemes over the classes of sort `n`. -/
def SortZFC (n : ℕ) : Prop := SetAxioms (M.T.sortStr n) (M.DefOn n)

end TowerWithClasses

/-- The axioms of `H`. -/
structure IsTowerModel (M : TowerWithClasses.{u}) : Prop where
  zfc : ∀ n, M.SortZFC n
  j_injective : ∀ n (x y : M.T.U n), M.T.j n x = M.T.j n y → x = y
  j_mem_iff : ∀ n (x y : M.T.U n), M.T.mem (M.T.j n x) (M.T.j n y) ↔ M.T.mem x y
  kappa_inaccessible : ∀ n, (M.T.sortStr (n + 1)).Inaccessible (M.T.κ n)
  /-- The image of `j n` is exactly the rank segment at `κ n`. -/
  j_image : ∀ n, ∃ v : M.T.U (n + 1), (M.T.sortStr (n + 1)).IsV (M.T.κ n) v ∧
    ∀ y, M.T.mem y v ↔ ∃ x, M.T.j n x = y
  next_inaccessible : ∀ n,
    (M.T.sortStr (n + 2)).NextInaccessible (M.T.j (n + 1) (M.T.κ n)) (M.T.κ (n + 1))
  bottom : (M.T.sortStr 1).NoGreatestInaccessibleBelow (M.T.κ 0)

namespace IsTowerModel

/-- The set of sort `n` inside sort `n+1`: the element whose members are the
images of sort `n`.  Unique by extensionality. -/
theorem exists_image_set {M : TowerWithClasses.{u}} (hM : IsTowerModel M) (n : ℕ) :
    ∃ v : M.T.U (n + 1), ∀ y, M.T.mem y v ↔ ∃ x, M.T.j n x = y := by
  obtain ⟨v, -, hv⟩ := hM.j_image n
  exact ⟨v, hv⟩

end IsTowerModel

end SolidLean.Solid
