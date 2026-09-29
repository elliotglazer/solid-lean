module

public import Palomar.Bridge.Tower
public import Solid.TowerTheory

/-!
# Bridge, part 2: the axioms of `H`

A `Palomar` model of `H` is a model of `H` in the development's sense, for
the definable class system.  `Tower.IsModelH T` gives
`IsTowerModel ⟨T.toMem, T.defSys⟩`.  The set-theoretic notions of the two
files are the same definitions, so most clauses are definitional.
-/

@[expose] public section

universe u

namespace SolidLean.Palomar

open SolidLean.Solid

/-! ### The ZFC axioms -/

/-- The `Palomar` ZFC axioms for `(X, mem)` and a definability predicate give
the development's, for any smaller definability predicate. -/
theorem setAxioms_toSolid {X : Type u} {mem : X → X → Prop}
    {Def Def' : (k : ℕ) → Set (Fin k → X) → Prop} (hD : ∀ k C, Def' k C → Def k C)
    (h : SetAxioms mem Def) : Solid.SetAxioms ⟨X, mem⟩ Def' where
  ext := h.ext
  empty := h.empty
  pair := h.pair
  union := h.union
  power := h.power
  infinity := h.infinity
  separation := fun C hC p x => h.separation C (hD _ C hC) p x
  replacement := fun C hC p x hu => h.replacement C (hD _ C hC) p x hu
  foundation := h.foundation
  choice := h.choice

/-! ### The tower axioms -/

namespace Tower

variable {T : Tower.{u}}

/-- A `Palomar` model of `H` is a model of `H` with its definable classes. -/
theorem IsModelH.toSolid (hT : T.IsModelH) : IsTowerModel ⟨T.toMem, T.defSys⟩ where
  zfc n := setAxioms_toSolid (fun k C hC => (T.defOn_iff n k C).2 hC) (hT.zfc n)
  j_injective := hT.j_injective
  j_mem_iff := hT.j_mem_iff
  kappa_inaccessible := hT.kappa_inaccessible
  j_image := hT.j_image
  next_inaccessible := hT.next_inaccessible
  bottom := hT.bottom

end Tower

end SolidLean.Palomar
