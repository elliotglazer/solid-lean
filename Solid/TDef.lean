module

public import Solid.SortModel
public import Solid.Def

/-!
# A definability calculus for tower class systems

The many-sorted counterpart of `Solid.Def`: `𝒟.TDef k P` says that the
predicate `P` on `k`-tuples of elements of the union of sorts is a class of
the tower system `𝒟`.  Quantifiers are sort-bounded.  Relations of a single
sort certified by `Solid.Def` in the sort's class system enter through
`TDef.lift`.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-! ### `Fin.snoc` at literal indices, for small arities -/

namespace Fin

variable {α : Type*}

@[simp] theorem snoc_one_zero (t : Fin 1 → α) (z : α) : (Fin.snoc t z : Fin 2 → α) 0 = t 0 := rfl
@[simp] theorem snoc_one_one (t : Fin 1 → α) (z : α) : (Fin.snoc t z : Fin 2 → α) 1 = z := rfl
@[simp] theorem snoc_two_zero (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 0 = t 0 := rfl
@[simp] theorem snoc_two_one (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 1 = t 1 := rfl
@[simp] theorem snoc_two_two (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 2 = z := rfl
@[simp] theorem snoc_three_zero (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 0 = t 0 := rfl
@[simp] theorem snoc_three_one (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 1 = t 1 := rfl
@[simp] theorem snoc_three_two (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 2 = t 2 := rfl
@[simp] theorem snoc_three_three (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 3 = z := rfl
@[simp] theorem snoc_four_zero (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 0 = t 0 := rfl
@[simp] theorem snoc_four_one (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 1 = t 1 := rfl
@[simp] theorem snoc_four_two (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 2 = t 2 := rfl
@[simp] theorem snoc_four_three (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 3 = t 3 := rfl
@[simp] theorem snoc_four_four (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 4 = z := rfl

end Fin

namespace ClassSystem

variable {M : MemTower.{u}} (𝒟 : ClassSystem M)

/-- `P` is a definable `k`-ary relation on the union of sorts. -/
def TDef (k : ℕ) (P : (Fin k → M.El) → Prop) : Prop := ({t | P t} : M.Rel k) ∈ 𝒟.D k

namespace TDef

variable {𝒟}

theorem congr {k : ℕ} {P Q : (Fin k → M.El) → Prop} (h : ∀ t, P t ↔ Q t)
    (hP : 𝒟.TDef k P) : 𝒟.TDef k Q := by
  have : ({t | Q t} : M.Rel k) = {t | P t} := by ext t; exact (h t).symm
  unfold TDef; rw [this]; exact hP

theorem and_ {k : ℕ} {P Q : (Fin k → M.El) → Prop} (hP : 𝒟.TDef k P) (hQ : 𝒟.TDef k Q) :
    𝒟.TDef k (fun t => P t ∧ Q t) := 𝒟.inter_mem hP hQ

theorem not_ {k : ℕ} {P : (Fin k → M.El) → Prop} (hP : 𝒟.TDef k P) :
    𝒟.TDef k (fun t => ¬ P t) := 𝒟.compl_mem hP

theorem or_ {k : ℕ} {P Q : (Fin k → M.El) → Prop} (hP : 𝒟.TDef k P) (hQ : 𝒟.TDef k Q) :
    𝒟.TDef k (fun t => P t ∨ Q t) :=
  congr (fun _ => by rw [not_and_or, not_not, not_not]) (not_ (and_ (not_ hP) (not_ hQ)))

theorem imp_ {k : ℕ} {P Q : (Fin k → M.El) → Prop} (hP : 𝒟.TDef k P) (hQ : 𝒟.TDef k Q) :
    𝒟.TDef k (fun t => P t → Q t) :=
  congr (fun _ => (imp_iff_not_or).symm) (or_ (not_ hP) hQ)

/-- Existential quantification over sort `n`, in the last position. -/
theorem exists_ (n : ℕ) {k : ℕ} {P : (Fin (k + 1) → M.El) → Prop} (hP : 𝒟.TDef (k + 1) P) :
    𝒟.TDef k (fun t => ∃ x : M.U n, P (Fin.snoc t (M.inj x))) := by
  refine congr ?_ (𝒟.exists_mem n hP)
  intro t
  show (∃ z : M.El, z.1 = n ∧ P (Fin.snoc t z)) ↔ _
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨M.toSort z hz, ?_⟩
    rw [M.inj_toSort]; exact h
  · rintro ⟨x, h⟩; exact ⟨M.inj x, rfl, h⟩

theorem forall_ (n : ℕ) {k : ℕ} {P : (Fin (k + 1) → M.El) → Prop} (hP : 𝒟.TDef (k + 1) P) :
    𝒟.TDef k (fun t => ∀ x : M.U n, P (Fin.snoc t (M.inj x))) :=
  congr (fun _ => not_exists_not) (not_ (exists_ n (not_ hP)))

theorem reindex {m k : ℕ} (f : Fin m → Fin k) {P : (Fin m → M.El) → Prop} (hP : 𝒟.TDef m P) :
    𝒟.TDef k (fun t => P (t ∘ f)) := 𝒟.reindex_mem f hP

theorem eq {k : ℕ} (i j : Fin k) : 𝒟.TDef k (fun t => t i = t j) :=
  reindex ![i, j] 𝒟.eq_mem

theorem sort {k : ℕ} (i : Fin k) (n : ℕ) : 𝒟.TDef k (fun t => (t i).1 = n) :=
  reindex (fun _ => i) (𝒟.sort_mem n)

theorem param {k : ℕ} (i : Fin k) (p : M.El) : 𝒟.TDef k (fun t => t i = p) :=
  reindex (fun _ => i) (𝒟.param_mem p)

theorem kappa {k : ℕ} (i : Fin k) (n : ℕ) : 𝒟.TDef k (fun t => t i = M.inj (M.κ n)) :=
  reindex (fun _ => i) (𝒟.kappa_mem n)

/-- A relation of one sort certified in the sort's system. -/
theorem lift {k : ℕ} (n : ℕ) {C : (M.sortStr n).Rel k} (hC : C ∈ (𝒟.sortSystem n).D k) :
    𝒟.TDef k (fun t => ∃ s : Fin k → M.U n, (∀ i, t i = M.inj (s i)) ∧ s ∈ C) := hC

/-- Membership between two positions in sort `n`. -/
theorem mem_sort {k : ℕ} (n : ℕ) (i j : Fin k) :
    𝒟.TDef k (fun t => ∃ x y : M.U n, t i = M.inj x ∧ t j = M.inj y ∧ M.mem x y) :=
  reindex ![i, j] (𝒟.memRel_mem n)

/-- The transition from sort `n` between two positions. -/
theorem j_sort {k : ℕ} (n : ℕ) (i j : Fin k) :
    𝒟.TDef k (fun t => ∃ x : M.U n, t i = M.inj x ∧ t j = M.inj (M.j n x)) :=
  reindex ![i, j] (𝒟.j_mem n)

/-- Instantiating the last variable with a parameter. -/
theorem withParam {k : ℕ} (p : M.El) {P : (Fin (k + 1) → M.El) → Prop} (hP : 𝒟.TDef (k + 1) P) :
    𝒟.TDef k (fun t => P (Fin.snoc t p)) := by
  refine congr ?_ (𝒟.exists_mem p.1 (𝒟.inter_mem (param (Fin.last k) p) hP))
  intro t
  show (∃ z : M.El, z.1 = p.1 ∧ Fin.snoc t z ∈ ({t | t (Fin.last k) = p} ∩ {t | P t})) ↔ _
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Fin.snoc_last]
  constructor
  · rintro ⟨z, -, rfl, h⟩; exact h
  · intro h; exact ⟨p, rfl, rfl, h⟩

/-- The graph of an iterated transition. -/
theorem liftGraph {m n : ℕ} (h : m ≤ n) :
    𝒟.TDef 2 (fun t => ∃ x : M.U m, t 0 = M.inj x ∧ t 1 = M.inj (M.liftLE h x)) := by
  induction h with
  | refl =>
    refine congr ?_ (and_ (sort 0 m) (eq 0 1))
    intro t
    constructor
    · rintro ⟨h0, h01⟩
      refine ⟨M.toSort (t 0) h0, (M.inj_toSort _ _).symm, ?_⟩
      rw [MemTower.liftLE_self, ← h01, M.inj_toSort]
    · rintro ⟨x, hx, hy⟩
      rw [MemTower.liftLE_self] at hy
      exact ⟨by rw [hx], hx.trans hy.symm⟩
  | @step n hmn ih =>
    refine congr ?_ (exists_ n (and_ (reindex ![0, 2] ih) (j_sort n 2 1)))
    intro t
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
    constructor
    · rintro ⟨y, ⟨x, hx, hy⟩, x', hx', ht1⟩
      refine ⟨x, hx, ?_⟩
      have h1 := M.inj_injective' hy
      have h2 := M.inj_injective' hx'
      rw [M.liftLE_succ hmn, ← h1, h2]
      exact ht1
    · rintro ⟨x, hx, ht1⟩
      refine ⟨M.liftLE hmn x, ⟨x, hx, rfl⟩, M.liftLE hmn x, rfl, ?_⟩
      rw [M.liftLE_succ hmn] at ht1
      exact ht1

/-! ### From tower classes to sort classes -/

/-- A unary tower class of elements of sort `s` is a class of the sort system. -/
theorem toDef1 {s : ℕ} {P : M.U s → Prop}
    (h : 𝒟.TDef 1 (fun t => ∃ z : M.U s, t 0 = M.inj z ∧ P z)) :
    (𝒟.sortSystem s).Def 1 (fun t => P (t 0)) := by
  show M.liftRel _ ∈ 𝒟.D 1
  have : M.liftRel ({t | P (t 0)} : (M.sortStr s).Rel 1) = {t | ∃ z : M.U s, t 0 = M.inj z ∧ P z} := by
    ext t
    rw [M.mem_liftRel_iff]
    constructor
    · rintro ⟨u, hu, hP⟩; exact ⟨u 0, hu 0, hP⟩
    · rintro ⟨z, hz, hP⟩
      refine ⟨fun _ => z, fun i => ?_, hP⟩
      have : i = 0 := Subsingleton.elim i 0
      subst this; exact hz
  rw [this]; exact h

/-- A binary tower class of elements of sort `s` is a class of the sort system. -/
theorem toDef2 {s : ℕ} {P : M.U s → M.U s → Prop}
    (h : 𝒟.TDef 2 (fun t => ∃ z w : M.U s, t 0 = M.inj z ∧ t 1 = M.inj w ∧ P z w)) :
    (𝒟.sortSystem s).Def 2 (fun t => P (t 0) (t 1)) := by
  show M.liftRel _ ∈ 𝒟.D 2
  have : M.liftRel ({t | P (t 0) (t 1)} : (M.sortStr s).Rel 2) =
      {t | ∃ z w : M.U s, t 0 = M.inj z ∧ t 1 = M.inj w ∧ P z w} := by
    ext t
    rw [M.mem_liftRel_iff]
    constructor
    · rintro ⟨u, hu, hP⟩; exact ⟨u 0, u 1, hu 0, hu 1, hP⟩
    · rintro ⟨z, w, hz, hw, hP⟩
      exact ⟨![z, w], Fin.forall_fin_two.2 ⟨hz, hw⟩, hP⟩
  rw [this]; exact h

/-- `∀ i : Fin 3`, unfolded. -/
theorem _root_.Fin.forall_fin_three {P : Fin 3 → Prop} : (∀ i, P i) ↔ P 0 ∧ P 1 ∧ P 2 := by
  constructor
  · intro h; exact ⟨h 0, h 1, h 2⟩
  · rintro ⟨h0, h1, h2⟩ i
    match i with
    | ⟨0, _⟩ => exact h0
    | ⟨1, _⟩ => exact h1
    | ⟨2, _⟩ => exact h2

/-- A unary relation of sort `n` at a position. -/
theorem lift1 {k : ℕ} (n : ℕ) {P : M.U n → Prop} (h : (𝒟.sortSystem n).Def 1 (fun t => P (t 0)))
    (i : Fin k) : 𝒟.TDef k (fun t => ∃ x : M.U n, t i = M.inj x ∧ P x) := by
  refine congr ?_ (reindex (fun _ : Fin 1 => i) (lift n h))
  intro t
  constructor
  · rintro ⟨s, hs, hP⟩; exact ⟨s 0, hs 0, hP⟩
  · rintro ⟨x, hx, hP⟩
    refine ⟨fun _ => x, fun l => ?_, hP⟩
    have : l = 0 := Subsingleton.elim l 0
    subst this; exact hx

/-- A binary relation of sort `n` at two positions. -/
theorem lift2 {k : ℕ} (n : ℕ) {P : M.U n → M.U n → Prop}
    (h : (𝒟.sortSystem n).Def 2 (fun t => P (t 0) (t 1))) (i j : Fin k) :
    𝒟.TDef k (fun t => ∃ x y : M.U n, t i = M.inj x ∧ t j = M.inj y ∧ P x y) := by
  refine congr ?_ (reindex ![i, j] (lift n h))
  intro t
  constructor
  · rintro ⟨s, hs, hP⟩; exact ⟨s 0, s 1, hs 0, hs 1, hP⟩
  · rintro ⟨x, y, hx, hy, hP⟩
    exact ⟨![x, y], Fin.forall_fin_two.2 ⟨hx, hy⟩, hP⟩

/-- A ternary relation of sort `n` at three positions. -/
theorem lift3 {k : ℕ} (n : ℕ) {P : M.U n → M.U n → M.U n → Prop}
    (h : (𝒟.sortSystem n).Def 3 (fun t => P (t 0) (t 1) (t 2))) (i j l : Fin k) :
    𝒟.TDef k (fun t => ∃ x y z : M.U n, t i = M.inj x ∧ t j = M.inj y ∧ t l = M.inj z ∧
      P x y z) := by
  refine congr ?_ (reindex ![i, j, l] (lift n h))
  intro t
  constructor
  · rintro ⟨s, hs, hP⟩; exact ⟨s 0, s 1, s 2, hs 0, hs 1, hs 2, hP⟩
  · rintro ⟨x, y, z, hx, hy, hz, hP⟩
    exact ⟨![x, y, z], Fin.forall_fin_three.2 ⟨hx, hy, hz⟩, hP⟩

end TDef

end ClassSystem

end SolidLean.Solid
