module

public import Solid.Absolute
public import Solid.SortModel

/-!
# Transitions of a tower model as inner embeddings

In a model of `H`, `j n` is a membership isomorphism of sort `n` onto the
rank segment `V(κ n)` of sort `n+1`, which is transitive and closed under
subsets (`Solid.Rank`).  Hence `j n`, and every iterated transition
`liftLE`, is an `InnerEmb` between the sort models, and all the notions of
`Solid.SetTheory` are absolute along them (`Solid.Absolute`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

namespace IsTowerModel

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-- The image of sort `n` in sort `n+1`, as a set. -/
noncomputable def imageSet (n : ℕ) : M.T.U (n + 1) := Classical.choose (hM.j_image n)

theorem imageSet_isV (n : ℕ) : (M.T.sortStr (n + 1)).IsV (M.T.κ n) (hM.imageSet n) :=
  (Classical.choose_spec (hM.j_image n)).1

theorem mem_imageSet_iff (n : ℕ) (y : M.T.U (n + 1)) :
    M.T.mem y (hM.imageSet n) ↔ ∃ x, M.T.j n x = y :=
  (Classical.choose_spec (hM.j_image n)).2 y

/-- `j n` as an inner embedding of sort `n` into sort `n+1`. -/
noncomputable def jEmb (n : ℕ) : InnerEmb (hM.sortModel n) (hM.sortModel (n + 1)) where
  φ := M.T.j n
  injective := fun x y h => hM.j_injective n x y h
  mem_iff := hM.j_mem_iff n
  trans := by
    intro x z hz
    have hx : M.T.mem (M.T.j n x) (hM.imageSet n) := (hM.mem_imageSet_iff n _).2 ⟨x, rfl⟩
    have hzv : M.T.mem z (hM.imageSet n) :=
      ZFCModel.IsV.transitive (hM.sortModel (n + 1)) (hM.imageSet_isV n) _ hx z hz
    exact (hM.mem_imageSet_iff n z).1 hzv
  supertrans := by
    intro x z hz
    have hx : M.T.mem (M.T.j n x) (hM.imageSet n) := (hM.mem_imageSet_iff n _).2 ⟨x, rfl⟩
    have hzv : M.T.mem z (hM.imageSet n) :=
      ZFCModel.IsV.subset_closed (hM.sortModel (n + 1)) (hM.imageSet_isV n) hx hz
    exact (hM.mem_imageSet_iff n z).1 hzv

@[simp] theorem jEmb_φ (n : ℕ) (x : M.T.U n) : (hM.jEmb n).φ x = M.T.j n x := rfl

/-- The identity inner embedding. -/
def _root_.SolidLean.Solid.InnerEmb.id (Z : ZFCModel.{u}) : InnerEmb Z Z where
  φ := fun x => x
  injective := fun _ _ h => h
  mem_iff := fun _ _ => Iff.rfl
  trans := fun _ z _ => ⟨z, rfl⟩
  supertrans := fun _ z _ => ⟨z, rfl⟩

include hM in
theorem liftLE_props {m n : ℕ} (h : m ≤ n) :
    (∀ x y : M.T.U m, M.T.liftLE h x = M.T.liftLE h y → x = y) ∧
    (∀ x y : M.T.U m, M.T.mem (M.T.liftLE h x) (M.T.liftLE h y) ↔ M.T.mem x y) ∧
    (∀ (x : M.T.U m) (z : M.T.U n), M.T.mem z (M.T.liftLE h x) → ∃ x', M.T.liftLE h x' = z) ∧
    (∀ (x : M.T.U m) (z : M.T.U n), (M.T.sortStr n).Subset z (M.T.liftLE h x) →
      ∃ x', M.T.liftLE h x' = z) := by
  induction h with
  | refl =>
    refine ⟨fun x y hxy => ?_, fun x y => ?_, fun x z _ => ⟨z, MemTower.liftLE_self _ z⟩,
      fun x z _ => ⟨z, MemTower.liftLE_self _ z⟩⟩
    · rwa [MemTower.liftLE_self, MemTower.liftLE_self] at hxy
    · rw [MemTower.liftLE_self, MemTower.liftLE_self]
  | @step n hmn ih =>
    obtain ⟨hinj, hmem, htr, hsup⟩ := ih
    refine ⟨fun x y hxy => ?_, fun x y => ?_, fun x z hz => ?_, fun x z hz => ?_⟩
    · rw [M.T.liftLE_succ hmn, M.T.liftLE_succ hmn] at hxy
      exact hinj x y (hM.j_injective n _ _ hxy)
    · rw [M.T.liftLE_succ hmn, M.T.liftLE_succ hmn, hM.j_mem_iff, hmem]
    · rw [M.T.liftLE_succ hmn] at hz
      obtain ⟨y, rfl⟩ := (hM.jEmb n).trans _ z hz
      obtain ⟨x', rfl⟩ := htr x y ((hM.j_mem_iff n _ _).1 hz)
      exact ⟨x', M.T.liftLE_succ hmn x'⟩
    · rw [M.T.liftLE_succ hmn] at hz
      obtain ⟨y, rfl⟩ := (hM.jEmb n).supertrans _ z hz
      obtain ⟨x', rfl⟩ := hsup x y (((hM.jEmb n).subset_iff y _).1 hz)
      exact ⟨x', M.T.liftLE_succ hmn x'⟩

/-- An iterated transition as an inner embedding. -/
noncomputable def liftEmb {m n : ℕ} (h : m ≤ n) : InnerEmb (hM.sortModel m) (hM.sortModel n) where
  φ := M.T.liftLE h
  injective := fun x y hxy => (hM.liftLE_props h).1 x y hxy
  mem_iff := (hM.liftLE_props h).2.1
  trans := (hM.liftLE_props h).2.2.1
  supertrans := (hM.liftLE_props h).2.2.2

@[simp] theorem liftEmb_φ {m n : ℕ} (h : m ≤ n) (x : M.T.U m) :
    (hM.liftEmb h).φ x = M.T.liftLE h x := rfl

include hM in
theorem liftLE_injective {m n : ℕ} (h : m ≤ n) {x y : M.T.U m}
    (hxy : M.T.liftLE h x = M.T.liftLE h y) : x = y :=
  (hM.liftEmb h).injective hxy

include hM in
theorem liftLE_mem_iff {m n : ℕ} (h : m ≤ n) (x y : M.T.U m) :
    M.T.mem (M.T.liftLE h x) (M.T.liftLE h y) ↔ M.T.mem x y :=
  (hM.liftEmb h).mem_iff x y

end IsTowerModel

namespace MemTower

variable (M : MemTower.{u})

theorem liftLE_trans {m n k : ℕ} (h1 : m ≤ n) (h2 : n ≤ k) (x : M.U m) :
    M.liftLE h2 (M.liftLE h1 x) = M.liftLE (h1.trans h2) x := by
  unfold liftLE
  exact (Nat.leRecOn_trans h1 h2 x).symm

/-- Proof irrelevance for the lift. -/
theorem liftLE_congr {m n : ℕ} (h h' : m ≤ n) (x : M.U m) : M.liftLE h x = M.liftLE h' x := rfl

end MemTower

namespace IsTowerModel

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-- The members of the lifted image set of sort `n` in sort `k` are exactly the
lifts of sort `n`. -/
theorem j_eq_liftLE (n : ℕ) (x : M.T.U n) : M.T.j n x = M.T.liftLE (Nat.le_succ n) x := by
  rw [M.T.liftLE_succ (le_refl n) x, MemTower.liftLE_self]

theorem mem_lift_imageSet_iff {n k : ℕ} (h : n + 1 ≤ k) (z : M.T.U k) :
    M.T.mem z (M.T.liftLE h (hM.imageSet n)) ↔
      ∃ x : M.T.U n, M.T.liftLE (Nat.le_of_succ_le h) x = z := by
  constructor
  · intro hz
    obtain ⟨y, rfl⟩ := (hM.liftEmb h).trans _ z hz
    have hy : M.T.mem y (hM.imageSet n) := (hM.liftLE_mem_iff h y _).1 hz
    obtain ⟨x, rfl⟩ := (hM.mem_imageSet_iff n y).1 hy
    refine ⟨x, ?_⟩
    show M.T.liftLE _ x = M.T.liftLE h (M.T.j n x)
    rw [j_eq_liftLE, M.T.liftLE_trans]
  · rintro ⟨x, rfl⟩
    have : M.T.liftLE (Nat.le_of_succ_le h) x = M.T.liftLE h (M.T.j n x) := by
      rw [j_eq_liftLE, M.T.liftLE_trans]
    rw [this, hM.liftLE_mem_iff]
    exact (hM.mem_imageSet_iff n _).2 ⟨x, rfl⟩

end IsTowerModel

end SolidLean.Solid
