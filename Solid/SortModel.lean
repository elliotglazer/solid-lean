module

public import Solid.Def
public import Solid.Interpretation

/-!
# Each sort of a tower model is a `ZFCModel`

The classes of sort `n` of a tower with classes form a `SetClassSystem` on
the membership structure `sortStr n` (`ClassSystem.sortSystem`), and the
first axiom of `H` says that this is a model of ZFC with schemes over those
classes (`IsTowerModel.sortModel`).  Through this, everything proved for an
abstract `ZFCModel` in `Solid.Internal` and later files applies inside every
sort of every model of `H`, including the interpreted ones.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

namespace MemTower

variable (M : MemTower.{u})

theorem inj_toSort {n : ℕ} (z : M.El) (h : z.1 = n) : M.inj (Sorted.toSort M.U z h) = z :=
  Sorted.inj_toSort M.U z h

/-- The element of sort `n` underlying an element of the union known to have
sort `n`. -/
abbrev toSort {n : ℕ} (z : M.El) (h : z.1 = n) : M.U n := Sorted.toSort M.U z h

theorem inj_injective' {n : ℕ} {x y : M.U n} (h : M.inj x = M.inj y) : x = y :=
  Sorted.inj_injective M.U h

theorem inj_eq_inj_iff {m n : ℕ} {x : M.U m} {y : M.U n} :
    M.inj x = M.inj y ↔ ∃ h : m = n, h ▸ x = y := by
  constructor
  · intro h
    have hmn : m = n := congrArg Sigma.fst h
    subst hmn
    exact ⟨rfl, inj_injective' M h⟩
  · rintro ⟨h, hx⟩
    subst h; subst hx; rfl

theorem mem_sortTuple_iff {n k : ℕ} (t : Fin k → M.El) :
    t ∈ M.sortTuple n k ↔ ∃ s : Fin k → M.U n, ∀ i, t i = M.inj (s i) := by
  constructor
  · intro h
    exact ⟨fun i => M.toSort (t i) (h i), fun i => (M.inj_toSort (t i) (h i)).symm⟩
  · rintro ⟨s, hs⟩ i
    rw [hs i]

theorem mem_liftRel_iff {n k : ℕ} (C : (M.sortStr n).Rel k) (t : Fin k → M.El) :
    t ∈ M.liftRel C ↔ ∃ s : Fin k → M.U n, (∀ i, t i = M.inj (s i)) ∧ s ∈ C := Iff.rfl

/-- The tuple of sort-`n` elements underlying a tuple is unique. -/
theorem sort_tuple_unique {n k : ℕ} {t : Fin k → M.El} {s s' : Fin k → M.U n}
    (hs : ∀ i, t i = M.inj (s i)) (hs' : ∀ i, t i = M.inj (s' i)) : s = s' := by
  funext i
  exact inj_injective' M ((hs i).symm.trans (hs' i))

theorem inj_comp_mem_liftRel_iff {n k : ℕ} (C : (M.sortStr n).Rel k) (s : Fin k → M.U n) :
    (fun i => M.inj (s i)) ∈ M.liftRel C ↔ s ∈ C := by
  constructor
  · rintro ⟨s', hs', hC⟩
    have : s = s' := M.sort_tuple_unique (fun _ => rfl) hs'
    subst this; exact hC
  · intro hC; exact ⟨s, fun _ => rfl, hC⟩

/-! ### Lifting identities -/

theorem liftRel_univ (n k : ℕ) : M.liftRel (Set.univ : (M.sortStr n).Rel k) = M.sortTuple n k := by
  ext t
  rw [mem_liftRel_iff, mem_sortTuple_iff]
  constructor
  · rintro ⟨s, hs, -⟩; exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩; exact ⟨s, hs, trivial⟩

theorem liftRel_inter {n k : ℕ} (C C' : (M.sortStr n).Rel k) :
    M.liftRel (C ∩ C') = M.liftRel C ∩ M.liftRel C' := by
  ext t
  simp only [Set.mem_inter_iff, mem_liftRel_iff]
  constructor
  · rintro ⟨s, hs, hC, hC'⟩; exact ⟨⟨s, hs, hC⟩, ⟨s, hs, hC'⟩⟩
  · rintro ⟨⟨s, hs, hC⟩, ⟨s', hs', hC'⟩⟩
    have := M.sort_tuple_unique hs hs'
    subst this
    exact ⟨s, hs, hC, hC'⟩

theorem liftRel_compl {n k : ℕ} (C : (M.sortStr n).Rel k) :
    M.liftRel Cᶜ = M.sortTuple n k ∩ (M.liftRel C)ᶜ := by
  ext t
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, mem_liftRel_iff, mem_sortTuple_iff]
  constructor
  · rintro ⟨s, hs, hC⟩
    refine ⟨⟨s, hs⟩, ?_⟩
    rintro ⟨s', hs', hC'⟩
    have := M.sort_tuple_unique hs hs'
    subst this
    exact hC hC'
  · rintro ⟨⟨s, hs⟩, h⟩
    exact ⟨s, hs, fun hC => h ⟨s, hs, hC⟩⟩

theorem liftRel_reindex {n k l : ℕ} (f : Fin k → Fin l) (C : (M.sortStr n).Rel k) :
    M.liftRel ({s | (s ∘ f) ∈ C} : (M.sortStr n).Rel l) =
      M.sortTuple n l ∩ M.reindex f (M.liftRel C) := by
  ext t
  simp only [Set.mem_inter_iff, MemTower.reindex, Set.mem_setOf_eq, mem_liftRel_iff,
    mem_sortTuple_iff]
  constructor
  · rintro ⟨s, hs, hC⟩
    exact ⟨⟨s, hs⟩, s ∘ f, fun i => hs (f i), hC⟩
  · rintro ⟨⟨s, hs⟩, s', hs', hC⟩
    have : s ∘ f = s' := M.sort_tuple_unique (t := t ∘ f) (fun i => hs (f i)) hs'
    subst this
    exact ⟨s, hs, hC⟩

theorem liftRel_exists {n k : ℕ} (C : (M.sortStr n).Rel (k + 1)) :
    M.liftRel ({s | ∃ x, Fin.snoc s x ∈ C} : (M.sortStr n).Rel k) =
      M.exists_ n (M.liftRel C) := by
  ext t
  simp only [MemTower.exists_, Set.mem_setOf_eq, mem_liftRel_iff]
  constructor
  · rintro ⟨s, hs, x, hC⟩
    refine ⟨M.inj x, rfl, Fin.snoc s x, ?_, hC⟩
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]; exact hs i
  · rintro ⟨z, hz, s', hs', hC⟩
    refine ⟨fun i => s' (Fin.castSucc i), fun i => ?_, s' (Fin.last k), ?_⟩
    · have := hs' (Fin.castSucc i)
      simpa only [Fin.snoc_castSucc] using this
    · have : (Fin.snoc (fun i => s' (Fin.castSucc i)) (s' (Fin.last k)) : Fin (k + 1) → M.U n) = s' := by
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp only [Fin.snoc_last]
        · simp only [Fin.snoc_castSucc]
      rw [this]; exact hC

theorem liftRel_param {n : ℕ} (p : M.U n) :
    M.liftRel ({s | s 0 = p} : (M.sortStr n).Rel 1) = M.paramRel (M.inj p) := by
  ext t
  simp only [MemTower.paramRel, Set.mem_setOf_eq, mem_liftRel_iff]
  constructor
  · rintro ⟨s, hs, hp⟩
    rw [hs 0]; exact congrArg _ hp
  · intro h
    refine ⟨fun _ => p, fun i => ?_, rfl⟩
    have : i = 0 := Subsingleton.elim i 0
    subst this; exact h

theorem liftRel_eq (n : ℕ) :
    M.liftRel ({s | s 0 = s 1} : (M.sortStr n).Rel 2) = M.sortTuple n 2 ∩ M.eqRel := by
  ext t
  simp only [Set.mem_inter_iff, MemTower.eqRel, Set.mem_setOf_eq, mem_liftRel_iff,
    mem_sortTuple_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨⟨s, hs⟩, by rw [hs 0, hs 1, h]⟩
  · rintro ⟨⟨s, hs⟩, h⟩
    refine ⟨s, hs, ?_⟩
    apply inj_injective' M
    rw [← hs 0, ← hs 1]; exact h

theorem liftRel_mem (n : ℕ) :
    M.liftRel ({s | M.mem (s 0) (s 1)} : (M.sortStr n).Rel 2) = M.memRel n := by
  ext t
  simp only [MemTower.memRel, Set.mem_setOf_eq, mem_liftRel_iff]
  constructor
  · rintro ⟨s, hs, h⟩
    exact ⟨s 0, s 1, hs 0, hs 1, h⟩
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨![x, y], Fin.forall_fin_two.2 ⟨hx, hy⟩, hxy⟩

end MemTower

namespace ClassSystem

variable {M : MemTower.{u}} (𝒟 : ClassSystem M)

/-- The classes of sort `n`, as a class system on the membership structure of
that sort. -/
def sortSystem (n : ℕ) : SetClassSystem (M.sortStr n) where
  D k := {C | M.liftRel C ∈ 𝒟.D k}
  eq_mem := by
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_eq n]
    exact 𝒟.inter_mem (𝒟.sortTuple_mem n 2) 𝒟.eq_mem
  memRel_mem := by
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_mem n]
    exact 𝒟.memRel_mem n
  param_mem := by
    intro p
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_param p]
    exact 𝒟.param_mem _
  univ_mem := by
    intro k
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_univ n k]
    exact 𝒟.sortTuple_mem n k
  inter_mem := by
    intro k C C' hC hC'
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_inter]
    exact 𝒟.inter_mem hC hC'
  compl_mem := by
    intro k C hC
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_compl]
    exact 𝒟.inter_mem (𝒟.sortTuple_mem n k) (𝒟.compl_mem hC)
  reindex_mem := by
    intro k l f C hC
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_reindex]
    exact 𝒟.inter_mem (𝒟.sortTuple_mem n l) (𝒟.reindex_mem f hC)
  exists_mem := by
    intro k C hC
    show M.liftRel _ ∈ 𝒟.D _
    rw [M.liftRel_exists]
    exact 𝒟.exists_mem n hC

theorem mem_sortSystem_iff (n k : ℕ) (C : (M.sortStr n).Rel k) :
    C ∈ (𝒟.sortSystem n).D k ↔ M.liftRel C ∈ 𝒟.D k := Iff.rfl

end ClassSystem

namespace IsTowerModel

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-- Sort `n` of a model of `H`, as a model of ZFC. -/
abbrev sortModel (n : ℕ) : ZFCModel.{u} where
  S := M.T.sortStr n
  𝒞 := M.𝒟.sortSystem n
  ax := hM.zfc n

@[simp] theorem sortModel_S (n : ℕ) : (hM.sortModel n).S = M.T.sortStr n := rfl

theorem sortModel_X (n : ℕ) : (hM.sortModel n).S.X = M.T.U n := rfl

theorem sortModel_mem (n : ℕ) (x y : M.T.U n) :
    (hM.sortModel n).S.mem x y ↔ M.T.mem x y := Iff.rfl

end IsTowerModel

end SolidLean.Solid
