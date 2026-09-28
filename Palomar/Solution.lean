import Palomar.Statement
import Palomar.Bridge.Interp
import Solid.Solidity

/-!
# The tower theory `H` is solid: the proof

The target of `Palomar/Challenge.lean`, proved from the development's
`tower_solid` (Theorem 2.1 of *Solid idealized Lean*).  A `Palomar` model of
`H` is a model of `H` with its definable class system.  A `Palomar`
interpretation is an interpretation for that class system with the same
interpreted tower.  The definable classes of the interpreted tower lie below
the induced ones (the translation lemma), and isomorphisms with their
definability correspond.  This file imports `Palomar.Statement`, the
generated copy of the definitions of the Challenge, never the Challenge
itself.
-/

universe u

namespace SolidLean.Palomar

open SolidLean.Solid

/-- **The tower theory `H` is solid** (Theorem 2.1 of *Solid idealized Lean*), for
interpretations in one-coordinate normal form. -/
theorem tower_theory_solid : Solid.{u} := by
  intro T hT I hI J hJ i hi
  let M : TowerWithClasses.{u} := ⟨T.toMem, T.defSys⟩
  have hM : IsTowerModel M := hT.toSolid
  let I' : Solid.Interp M := I.toSolid
  let 𝒩 : ClassSystem I'.model := I.Model.defSys
  have h𝒩 : ∀ k (C : I'.model.Rel k), C ∈ 𝒩.D k → C ∈ I'.induced.D k :=
    fun k C hC => I'.defSys_le_induced k C hC
  have hN : IsTowerModel ⟨I'.model, 𝒩⟩ := hI.toSolid
  let J' : Solid.Interp ⟨I'.model, 𝒩⟩ := J.toSolid
  let 𝒬 : ClassSystem J'.model := J.Model.defSys
  have hP : IsTowerModel ⟨J'.model, 𝒬⟩ := hJ.toSolid
  let i' : TowerIso M.T J'.model := i.toSolid
  have hi' : i'.DefinableIn M.𝒟 (I'.pres.comp J'.pres) := (i.definableIn_iff _).1 hi
  obtain ⟨h', hh'⟩ := tower_solid M hM I' 𝒩 h𝒩 hN J' 𝒬 hP i' hi'
  exact ⟨Iso.ofSolid (T := T) (N := I.Model) h', (Iso.definableIn_ofSolid_iff (T := T) (N := I.Model) h' I.pres).2 hh'⟩

end SolidLean.Palomar
