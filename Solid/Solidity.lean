import Solid.Assemble
import Solid.Step5
import Solid.Step5b
import Solid.Step6

/-!
# Solidity of the tower theory

Draft 2, Definition 1.1 and Theorem 2.1.  `TowerTheorySolid` is Enayat's
solidity for `H` in the category of §1: for models `M ⊳ N ⊳ P` with an
`M`-definable isomorphism `M → P`, there is an `M`-definable isomorphism
`M → N`.

The proof follows the six steps of draft 2 §2:

* Steps 1–3 (`Config.collapseData`, from `Solid.Step1`, `Solid.Step1b`,
  `Solid.Level`, `Solid.Assemble`): inside sorts of `N`, each sort of `P`
  collapses onto a transitive subset-closed set, compatibly with the
  transitions and definably;
* Step 4 (`Solid.Collapse`): the collapsed sets are rank segments at
  inaccessible heights satisfying the ladder clauses;
* Step 5 (`Solid.Step5`, `Solid.Step5b`): the bottom height is `κ 0` of
  `N`;
* Step 6 (`Solid.Step6`): assembly of the definable isomorphism.
-/

universe u

namespace SolidLean.Solid

open Classical

/-- Enayat's solidity for the tower theory, in the finitary many-sorted
category of draft 2 §1 (one-coordinate normal form).  The middle model `N`
carries any class system `𝒩` contained in the one induced from `M` and
satisfies `H` for it; the inner model `P` carries an arbitrary class system.
For first-order models with their definable relations these are exactly the
hypotheses of Enayat's definition. -/
def TowerTheorySolid : Prop :=
  ∀ (M : TowerWithClasses.{u}), IsTowerModel M →
  ∀ (I : Interp M) (𝒩 : ClassSystem I.model),
    (∀ k (C : I.model.Rel k), C ∈ 𝒩.D k → C ∈ I.induced.D k) → IsTowerModel ⟨I.model, 𝒩⟩ →
  ∀ (J : Interp ⟨I.model, 𝒩⟩) (𝒬 : ClassSystem J.model), IsTowerModel ⟨J.model, 𝒬⟩ →
  ∀ (i : TowerIso M.T J.model), i.DefinableIn M.𝒟 (I.pres.comp J.pres) →
  ∃ h : TowerIso M.T I.model, h.DefinableIn M.𝒟 I.pres

/-- The special case in which `N` and `P` carry the induced class systems. -/
def TowerTheorySolidInduced : Prop :=
  ∀ (M : TowerWithClasses.{u}), IsTowerModel M →
  ∀ (I : Interp M), I.Models →
  ∀ (J : Interp I.asModel), J.Models →
  ∀ (i : TowerIso M.T J.model), i.DefinableIn M.𝒟 (I.pres.comp J.pres) →
  ∃ h : TowerIso M.T I.model, h.DefinableIn M.𝒟 I.pres

/-- **Theorem 2.1 (draft 2).**  The tower theory `H` is solid. -/
theorem tower_solid : TowerTheorySolid.{u} := by
  intro M hM I 𝒩 h𝒩 hI J 𝒬 hJ i hi
  let c : Config.{u} := ⟨M, hM, I, 𝒩, h𝒩, hI, J, 𝒬, hJ, i, hi⟩
  obtain ⟨C⟩ := c.collapseData_exists
  obtain ⟨h0, hle⟩ := C.bottom_le_kappa c.hN c.hP
  refine c.assemble_iso C ⟨h0, ?_⟩
  rcases hle with hlt | heq
  · -- `δ 0 < κ 0` would put every collapsed sort below `κ 0`; Step 5 rules it out.
    exact absurd (C.below_propagates c.hN c.hP h0 hlt) (c.not_all_below_bottom C)
  · exact heq

theorem tower_solid_induced : TowerTheorySolidInduced.{u} :=
  fun M hM I hI J hJ i hi => tower_solid M hM I I.induced (fun _ _ h => h) hI J J.induced hJ i hi

end SolidLean.Solid
