import Solid.Gen.Clauses

/-!
# The class system of first-order definable relations

A relation on the union of the sorts of a structure `M` is *locally
definable* when, for every profile of sorts, its restriction to the tuples of
that profile is defined by a first-order formula with parameters.  These
relations form a class system containing the relation atoms
(`Str.defSys`).  This is the class system that Enayat's definition of
solidity refers to: instantiating the semantic solidity theorems at it gives
the first-order statement.  (The remaining first-order ingredient, that a
syntactic interpretation carries the definable classes of the interpreted
structure to classes with definable preimages, is `GenInterp.defSys_le_induced`
in `Solid.Gen.Translate`.)
-/

universe u

namespace SolidLean.Solid

open Classical

namespace Formula

variable {Sig : Signature}

/-- Parameters in front of an environment. -/
theorem append_snoc {α : Type*} {a k : ℕ} (p : Fin a → α) (t : Fin k → α) (x : α) :
    Fin.append p (Fin.snoc (α := fun _ => α) t x) =
      Fin.snoc (α := fun _ => α) (Fin.append p t) x := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have : Fin.castAdd (k + 1) j = Fin.castSucc (Fin.castAdd k j) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc, Fin.append_left]
  · rw [Fin.append_right]
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have : Fin.natAdd a (Fin.last k) = Fin.last (a + k) := Fin.ext rfl
      rw [this, Fin.snoc_last, Fin.snoc_last]
    · have : Fin.natAdd a (Fin.castSucc j) = Fin.castSucc (Fin.natAdd a j) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.append_right]

theorem elim0_append_cast {α : Type*} {k : ℕ} (v : Fin k → α) (i : Fin k) :
    Fin.append (Fin.elim0 : Fin 0 → α) v (Fin.cast (Nat.zero_add k).symm i) = v i := by
  have : Fin.cast (Nat.zero_add k).symm i = Fin.natAdd 0 i := Fin.ext (Nat.zero_add _).symm
  rw [this, Fin.append_right]

/-- Definability at a profile, with parameters of declared sorts. -/
def SortedDef (M : Str.{u} Sig) {k : ℕ} (s : Fin k → ℕ) (C : Sorted.Rel M.U k) : Prop :=
  ∃ (a : ℕ) (ps : Fin a → ℕ) (φ : Formula Sig (a + k) (Fin.append ps s)) (p : Fin a → Sorted.El M.U),
    (∀ i, (p i).1 = ps i) ∧ ∀ t ∈ Sorted.profileRel M.U s, (t ∈ C ↔ φ.Sat M (Fin.append p t))

variable {M : Str.{u} Sig}

/-- A parameter-free definition. -/
theorem SortedDef.of_formula {k : ℕ} {s : Fin k → ℕ} {C : Sorted.Rel M.U k}
    (φ : Formula Sig (0 + k) (Fin.append Fin.elim0 s))
    (h : ∀ t ∈ Sorted.profileRel M.U s, (t ∈ C ↔ φ.Sat M (Fin.append Fin.elim0 t))) :
    SortedDef M s C :=
  ⟨0, Fin.elim0, φ, Fin.elim0, fun i => i.elim0, h⟩

/-- The empty relation is definable at every profile. -/
theorem SortedDef.empty {k : ℕ} (s : Fin k → ℕ) : SortedDef M s (∅ : Sorted.Rel M.U k) :=
  SortedDef.of_formula .false_ (fun _ _ => by simp)

theorem SortedDef.univ {k : ℕ} (s : Fin k → ℕ) : SortedDef M s (Set.univ : Sorted.Rel M.U k) :=
  SortedDef.of_formula true_ (fun _ _ => by simp)

/-- A relation that misses the profile entirely is definable there. -/
theorem SortedDef.of_disjoint {k : ℕ} (s : Fin k → ℕ) {C : Sorted.Rel M.U k}
    (h : ∀ t ∈ Sorted.profileRel M.U s, t ∉ C) : SortedDef M s C :=
  SortedDef.of_formula .false_ (fun t ht => by simp [h t ht])

theorem SortedDef.compl {k : ℕ} {s : Fin k → ℕ} {C : Sorted.Rel M.U k} (h : SortedDef M s C) :
    SortedDef M s Cᶜ := by
  obtain ⟨a, ps, φ, p, hp, hφ⟩ := h
  exact ⟨a, ps, not φ, p, hp, fun t ht => by rw [Set.mem_compl_iff, hφ t ht, Sat_not]⟩

/-- The renaming that embeds the parameters of a first definition into a
combined parameter list. -/
def mergeL (a₁ a₂ k : ℕ) : Fin (a₁ + k) → Fin (a₁ + a₂ + k) :=
  Fin.addCases (fun i => Fin.castAdd k (Fin.castAdd a₂ i)) (fun j => Fin.natAdd (a₁ + a₂) j)

def mergeR (a₁ a₂ k : ℕ) : Fin (a₂ + k) → Fin (a₁ + a₂ + k) :=
  Fin.addCases (fun i => Fin.castAdd k (Fin.natAdd a₁ i)) (fun j => Fin.natAdd (a₁ + a₂) j)

theorem append_comp_mergeL {α : Type*} {a₁ a₂ k : ℕ} (p₁ : Fin a₁ → α) (p₂ : Fin a₂ → α)
    (t : Fin k → α) : (fun i => Fin.append (Fin.append p₁ p₂) t (mergeL a₁ a₂ k i)) = Fin.append p₁ t := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [mergeL]

theorem append_comp_mergeR {α : Type*} {a₁ a₂ k : ℕ} (p₁ : Fin a₁ → α) (p₂ : Fin a₂ → α)
    (t : Fin k → α) : (fun i => Fin.append (Fin.append p₁ p₂) t (mergeR a₁ a₂ k i)) = Fin.append p₂ t := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [mergeR]

theorem SortedDef.inter {k : ℕ} {s : Fin k → ℕ} {C C' : Sorted.Rel M.U k} (h : SortedDef M s C)
    (h' : SortedDef M s C') : SortedDef M s (C ∩ C') := by
  obtain ⟨a₁, ps₁, φ₁, p₁, hp₁, hφ₁⟩ := h
  obtain ⟨a₂, ps₂, φ₂, p₂, hp₂, hφ₂⟩ := h'
  refine ⟨a₁ + a₂, Fin.append ps₁ ps₂,
    and (rename (mergeL a₁ a₂ k) (fun i => congrFun (append_comp_mergeL ps₁ ps₂ s) i) φ₁)
        (rename (mergeR a₁ a₂ k) (fun i => congrFun (append_comp_mergeR ps₁ ps₂ s) i) φ₂),
    Fin.append p₁ p₂, ?_, fun t ht => ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [hp₁, hp₂]
  · rw [Set.mem_inter_iff, hφ₁ t ht, hφ₂ t ht, Sat_and, sat_rename, sat_rename,
      append_comp_mergeL, append_comp_mergeR]

/-- The renaming for substitution of variables in the environment part. -/
def reindexParams (a : ℕ) {k l : ℕ} (f : Fin k → Fin l) : Fin (a + k) → Fin (a + l) :=
  Fin.addCases (fun i => Fin.castAdd l i) (fun j => Fin.natAdd a (f j))

theorem append_comp_reindexParams {α : Type*} {a k l : ℕ} (p : Fin a → α) (t : Fin l → α)
    (f : Fin k → Fin l) :
    (fun i => Fin.append p t (reindexParams a f i)) = Fin.append p (fun j => t (f j)) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [reindexParams]

theorem SortedDef.reindex {k l : ℕ} (f : Fin k → Fin l) {s : Fin l → ℕ} {C : Sorted.Rel M.U k}
    (h : SortedDef M (fun j => s (f j)) C) : SortedDef M s (Sorted.reindex M.U f C) := by
  obtain ⟨a, ps, φ, p, hp, hφ⟩ := h
  refine ⟨a, ps, rename (reindexParams a f) (fun i => congrFun (append_comp_reindexParams ps s f) i) φ,
    p, hp, fun t ht => ?_⟩
  have ht' : (fun j => t (f j)) ∈ Sorted.profileRel M.U (fun j => s (f j)) := fun j => ht (f j)
  show (fun j => t (f j)) ∈ C ↔ _
  rw [hφ _ ht', sat_rename, append_comp_reindexParams]

theorem SortedDef.exists_ (n : ℕ) {k : ℕ} {s : Fin k → ℕ} {C : Sorted.Rel M.U (k + 1)}
    (h : SortedDef M (Fin.snoc (α := fun _ => ℕ) s n) C) :
    SortedDef M s (Sorted.exists_ M.U n C) := by
  obtain ⟨a, ps, φ, p, hp, hφ⟩ := h
  refine ⟨a, ps, .ex n (rename id (fun i => (congrFun (append_snoc ps s n) i).symm) φ), p, hp,
    fun t ht => ?_⟩
  show (∃ x : Sorted.El M.U, x.1 = n ∧ Fin.snoc t x ∈ C) ↔
    ∃ x : Sorted.El M.U, x.1 = n ∧ _
  constructor
  · rintro ⟨x, hx, hC⟩
    refine ⟨x, hx, ?_⟩
    rw [sat_rename]
    have hsn : Fin.snoc (α := fun _ => Sorted.El M.U) t x ∈
        Sorted.profileRel M.U (Fin.snoc (α := fun _ => ℕ) s n) := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [hx]
      · simp [ht i]
    have := (hφ _ hsn).1 hC
    rw [append_snoc p t x] at this
    exact this
  · rintro ⟨x, hx, hφ'⟩
    refine ⟨x, hx, ?_⟩
    rw [sat_rename] at hφ'
    have hsn : Fin.snoc (α := fun _ => Sorted.El M.U) t x ∈
        Sorted.profileRel M.U (Fin.snoc (α := fun _ => ℕ) s n) := by
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp [hx]
      · simp [ht i]
    rw [hφ _ hsn, append_snoc p t x]
    exact hφ'

/-- The relation atoms. -/
theorem SortedDef.rel (r : Sig.Rel) (s : Fin (Sig.arity r) → ℕ) : SortedDef M s (M.rel r) := by
  by_cases hs : ∀ i, s i = Sig.sortAt r i
  · refine SortedDef.of_formula (.rel r (fun i => Fin.cast (Nat.zero_add _).symm i) (fun i => ?_))
      (fun t _ => ?_)
    · rw [Fin.elim0_append]; simp [hs i]
    · rw [Sat_rel, Fin.elim0_append]
      show t ∈ M.rel r ↔ (fun i => t (Fin.cast _ (Fin.cast _ i))) ∈ M.rel r
      simp
  · refine SortedDef.of_disjoint s (fun t ht hC => hs (fun i => ?_))
    rw [← ht i]
    exact M.rel_sorts r t hC i

/-- The equality atom. -/
theorem SortedDef.eq (s : Fin 2 → ℕ) : SortedDef M s (Sorted.eqRel M.U) := by
  by_cases h01 : s 0 = s 1
  · refine SortedDef.of_formula (.eq (Fin.cast (Nat.zero_add _).symm 0) (Fin.cast (Nat.zero_add _).symm 1)
      (by rw [Fin.elim0_append]; simp [h01])) (fun t _ => ?_)
    rw [Sat_eq, Fin.elim0_append]
    show t 0 = t 1 ↔ t (Fin.cast _ (Fin.cast _ 0)) = t (Fin.cast _ (Fin.cast _ 1))
    simp
  · refine SortedDef.of_disjoint s (fun t ht hC => h01 ?_)
    rw [← ht 0, ← ht 1]
    show (t 0).1 = (t 1).1
    rw [show t 0 = t 1 from hC]

/-- The sort atoms. -/
theorem SortedDef.sort (n : ℕ) (s : Fin 1 → ℕ) : SortedDef M s (Sorted.sortRel M.U n) := by
  by_cases h : s 0 = n
  · refine SortedDef.of_formula true_ (fun t ht => ?_)
    simp only [Sat_true, iff_true]
    show (t 0).1 = n
    rw [ht 0, h]
  · refine SortedDef.of_disjoint s (fun t ht hC => h ?_)
    rw [← ht 0]
    exact hC

/-- The parameter atoms. -/
theorem SortedDef.param (q : Sorted.El M.U) (s : Fin 1 → ℕ) :
    SortedDef M s (Sorted.paramRel M.U q) := by
  by_cases h : s 0 = q.1
  · have hs0 : Fin.append ![q.1] s 0 = q.1 := by
      have : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := Fin.ext rfl
      rw [this, Fin.append_left]; rfl
    have hs1 : Fin.append ![q.1] s 1 = q.1 := by
      have : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := Fin.ext rfl
      rw [this, Fin.append_right]; exact h
    refine ⟨1, ![q.1], .eq 0 1 (hs0.trans hs1.symm), ![q], Fin.forall_fin_one.2 rfl, fun t _ => ?_⟩
    rw [Sat_eq]
    show t 0 = q ↔ Fin.append ![q] t 0 = Fin.append ![q] t 1
    have e0 : Fin.append ![q] t 0 = q := by
      have : (0 : Fin (1 + 1)) = Fin.castAdd 1 (0 : Fin 1) := Fin.ext rfl
      rw [this, Fin.append_left]; rfl
    have e1 : Fin.append ![q] t 1 = t 0 := by
      have : (1 : Fin (1 + 1)) = Fin.natAdd 1 (0 : Fin 1) := Fin.ext rfl
      rw [this, Fin.append_right]
    rw [e0, e1]
    exact eq_comm
  · refine SortedDef.of_disjoint s (fun t ht hC => h ?_)
    rw [← ht 0]
    show (t 0).1 = q.1
    rw [show t 0 = q from hC]

end Formula

/-! ### The class system of locally definable relations -/

namespace Str

variable {Sig : Signature} (M : Str.{u} Sig)

/-- The locally definable relations: definable with parameters on every
profile of sorts. -/
def defSys : StrSys M where
  D k := {C | ∀ s : Fin k → ℕ, Formula.SortedDef M s C}
  eq_mem s := Formula.SortedDef.eq s
  sort_mem n s := Formula.SortedDef.sort n s
  param_mem q s := Formula.SortedDef.param q s
  univ_mem k s := Formula.SortedDef.univ s
  inter_mem := by
    intro k C C' hC hC' s
    have hC' : ∀ s, Formula.SortedDef M s C' := hC'
    have hC : ∀ s, Formula.SortedDef M s C := hC
    exact (hC s).inter (hC' s)
  compl_mem := by
    intro k C hC s
    have hC : ∀ s, Formula.SortedDef M s C := hC
    exact (hC s).compl
  reindex_mem := by
    intro k l f C hC s
    have hC : ∀ s, Formula.SortedDef M s C := hC
    exact Formula.SortedDef.reindex f (hC _)
  exists_mem := by
    intro n k C hC s
    have hC : ∀ s, Formula.SortedDef M s C := hC
    exact Formula.SortedDef.exists_ n (hC _)
  rel_mem r s := Formula.SortedDef.rel r s

theorem mem_defSys_iff {k : ℕ} (C : Sorted.Rel M.U k) :
    C ∈ M.defSys.D k ↔ ∀ s : Fin k → ℕ, Formula.SortedDef M s C := Iff.rfl

end Str

end SolidLean.Solid
