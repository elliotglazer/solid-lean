module

public import Palomar.Statement
public import Solid.Gen.Definable
public import Solid.Gen.Clauses

/-!
# Bridge, part 1: towers, formulas and definability

The statement of `Palomar.Challenge` is written in its own self-contained
many-sorted logic.  This file identifies it with the development's.  A
`Palomar.Tower` is a `MemTower`, the formulas of `Palomar.Formula` translate
into the formulas of the tower signature `TowerSig` and back with the same
satisfaction, and `Palomar`'s notion of definability is membership in the
definable class system `Str.defSys` of the tower.
-/

@[expose] public section

universe u

namespace SolidLean.Palomar

open SolidLean.Solid

/-! ### Towers -/

/-- A `Palomar` tower as a tower of the development. -/
abbrev Tower.toMem (T : Tower.{u}) : MemTower.{u} := ⟨T.U, T.mem, T.j, T.κ⟩

/-- A tower of the development as a `Palomar` tower. -/
abbrev _root_.SolidLean.Solid.MemTower.toPal (M : MemTower.{u}) : Tower.{u} := ⟨M.U, M.mem, M.j, M.κ⟩

@[simp] theorem Tower.toMem_toPal (T : Tower.{u}) : T.toMem.toPal = T := rfl
@[simp] theorem _root_.SolidLean.Solid.MemTower.toPal_toMem (M : MemTower.{u}) : M.toPal.toMem = M := rfl

/-! ### Formulas -/

namespace Formula

/-- Translation into the formulas of the tower signature. -/
def toSolid : ∀ {k : ℕ} {s : Fin k → ℕ}, Formula k s → Solid.Formula TowerSig k s
  | _, s, .mem n i₀ i₁ h₀ h₁ => .rel (.memZ n) ![i₀, i₁] (by
      intro i
      match i with
      | 0 => exact h₀
      | 1 => exact h₁)
  | _, s, .jmap n i₀ i₁ h₀ h₁ => .rel (.liftZ n) ![i₀, i₁] (by
      intro i
      match i with
      | 0 => exact h₀
      | 1 => exact h₁)
  | _, s, .kappa n i hi => .rel (.bnd n) ![i] (by
      intro i'
      match i' with
      | 0 => exact hi)
  | _, _, .eq i₀ i₁ h => .eq i₀ i₁ h
  | _, _, .false_ => .false_
  | _, _, .imp φ ψ => .imp φ.toSolid ψ.toSolid
  | _, _, .ex n φ => .ex n φ.toSolid

/-- Translation from the formulas of the tower signature. -/
def ofSolid : ∀ {k : ℕ} {s : Fin k → ℕ}, Solid.Formula TowerSig k s → Formula k s
  | _, _, .rel (.memZ n) v hv => .mem n (v 0) (v 1) (hv 0) (hv 1)
  | _, _, .rel (.liftZ n) v hv => .jmap n (v 0) (v 1) (hv 0) (hv 1)
  | _, _, .rel (.bnd n) v hv => .kappa n (v 0) (hv 0)
  | _, _, .eq i₀ i₁ h => .eq i₀ i₁ h
  | _, _, .false_ => .false_
  | _, _, .imp φ ψ => .imp (ofSolid φ) (ofSolid ψ)
  | _, _, .ex n φ => .ex n (ofSolid φ)

theorem sat_toSolid (T : Tower.{u}) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula k s) (t : Fin k → T.El),
      φ.toSolid.Sat T.toMem.toStr t ↔ φ.Sat T t
  | _, _, .mem n i₀ i₁ _ _, t => by
    show (fun i => t (![i₀, i₁] i)) ∈ T.toMem.memRel n ↔ _
    simp only [MemTower.memRel, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact Iff.rfl
  | _, _, .jmap n i₀ i₁ _ _, t => by
    show (fun i => t (![i₀, i₁] i)) ∈ T.toMem.jRel n ↔ _
    simp only [MemTower.jRel, Set.mem_ofPred_eq, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    exact Iff.rfl
  | _, _, .kappa n i _, t => by
    show (fun i' => t (![i] i')) ∈ T.toMem.kappaRel n ↔ _
    simp only [MemTower.kappaRel, Set.mem_ofPred_eq, Matrix.cons_val_fin_one]
    exact Iff.rfl
  | _, _, .eq _ _ _, _ => Iff.rfl
  | _, _, .false_, _ => Iff.rfl
  | _, _, .imp φ ψ, t => by
    show (φ.toSolid.Sat T.toMem.toStr t → ψ.toSolid.Sat T.toMem.toStr t) ↔ (φ.Sat T t → ψ.Sat T t)
    rw [sat_toSolid T φ t, sat_toSolid T ψ t]
  | _, _, .ex n φ, t => by
    show (∃ x : T.El, x.1 = n ∧ φ.toSolid.Sat T.toMem.toStr (Fin.snoc t x)) ↔
      ∃ x : T.El, x.1 = n ∧ φ.Sat T (Fin.snoc t x)
    simp only [sat_toSolid T φ]

theorem sat_ofSolid (T : Tower.{u}) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Solid.Formula TowerSig k s) (t : Fin k → T.El),
      (ofSolid φ).Sat T t ↔ φ.Sat T.toMem.toStr t
  | _, _, .rel (.memZ n) v _, t => by
    show _ ↔ (fun i => t (v i)) ∈ T.toMem.memRel n
    exact Iff.rfl
  | _, _, .rel (.liftZ n) v _, t => by
    show _ ↔ (fun i => t (v i)) ∈ T.toMem.jRel n
    exact Iff.rfl
  | _, _, .rel (.bnd n) v _, t => by
    show _ ↔ (fun i => t (v i)) ∈ T.toMem.kappaRel n
    exact Iff.rfl
  | _, _, .eq _ _ _, _ => Iff.rfl
  | _, _, .false_, _ => Iff.rfl
  | _, _, .imp φ ψ, t => by
    show ((ofSolid φ).Sat T t → (ofSolid ψ).Sat T t) ↔ (φ.Sat T.toMem.toStr t → ψ.Sat T.toMem.toStr t)
    rw [sat_ofSolid T φ t, sat_ofSolid T ψ t]
  | _, _, .ex n φ, t => by
    show (∃ x : T.El, x.1 = n ∧ (ofSolid φ).Sat T (Fin.snoc t x)) ↔
      ∃ x : T.El, x.1 = n ∧ φ.Sat T.toMem.toStr (Fin.snoc t x)
    simp only [sat_ofSolid T φ]

end Formula

/-! ### Definability -/

namespace Tower

variable (T : Tower.{u})

/-- `Palomar`'s definability is membership in the definable class system. -/
theorem definable_iff (k : ℕ) (C : T.Rel k) : T.Definable k C ↔ C ∈ T.toMem.toStr.defSys.D k := by
  rw [Str.mem_defSys_iff]
  constructor
  · intro h s
    obtain ⟨a, ps, φ, p, hp, hφ⟩ := h s
    exact ⟨a, ps, φ.toSolid, p, hp, fun t ht => (hφ t ht).trans (Formula.sat_toSolid T φ _).symm⟩
  · intro h s
    obtain ⟨a, ps, φ, p, hp, hφ⟩ := h s
    exact ⟨a, ps, Formula.ofSolid φ, p, hp, fun t ht => (hφ t ht).trans (Formula.sat_ofSolid T φ _).symm⟩

/-- The definable class system of a tower. -/
noncomputable def defSys : ClassSystem T.toMem where
  toClassSys := T.toMem.toStr.defSys.toClassSys
  memRel_mem n := T.toMem.toStr.defSys.rel_mem (.memZ n)
  j_mem n := T.toMem.toStr.defSys.rel_mem (.liftZ n)
  kappa_mem n := T.toMem.toStr.defSys.rel_mem (.bnd n)

theorem mem_defSys_iff (k : ℕ) (C : T.Rel k) : C ∈ T.defSys.D k ↔ T.Definable k C :=
  (T.definable_iff k C).symm

theorem defOn_iff (n k : ℕ) (C : Set (Fin k → T.U n)) : T.DefOn n k C ↔ T.defSys.DefOn n k C :=
  T.definable_iff k _

theorem definableSet_iff (n : ℕ) (S : Set (T.U n)) : T.DefinableSet n S ↔ T.defSys.DefinableSet n S :=
  T.definable_iff 1 _

end Tower

end SolidLean.Palomar
