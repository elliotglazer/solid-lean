module

public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Order.BooleanAlgebra.Set

/-!
# Many-sorted membership towers and class systems

This is the statement layer of draft 2, §1.  A `MemTower` is a structure
for the signature of the tower theory `H`: sorts indexed by `ℕ`, a
membership relation on each sort, transition maps `j n : Sort n → Sort (n+1)`
and boundary constants `κ n : Sort (n+1)`.

Definability is treated semantically.  A `ClassSystem` on a tower is a
family of relations (of every finite arity, over the disjoint union of the
sorts) that contains the atomic relations and every singleton, and is closed
under the first-order operations with *sort-bounded* existential
quantification.  The definable-with-parameters relations of a first-order
model of `H` form such a system; that bridge is a separate lemma and is not
part of this file.  Every scheme of `H` is stated for classes of the system,
so a model of `H` in this sense is a pair `(tower, system)`.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-! ### Sorted carriers

Everything about classes that does not mention membership, transitions or
constants is stated for a bare family of sorts `U : ℕ → Type u`.  This is
the base type for interpretations: a tower can be interpreted inside any
sorted structure with a class system, not only inside another tower. -/

namespace Sorted

variable (U : ℕ → Type u)

/-- The disjoint union of the sorts; classes are relations on it. -/
abbrev El : Type u := Σ n, U n

/-- Inject an element of a sort into the union. -/
abbrev inj {n : ℕ} (x : U n) : El U := ⟨n, x⟩

/-- Relations of arity `k` over the union. -/
abbrev Rel (k : ℕ) : Type u := Set (Fin k → El U)

/-- Equality. -/
abbrev eqRel : Rel U 2 := {t | t 0 = t 1}

/-- The sort predicate. -/
abbrev sortRel (n : ℕ) : Rel U 1 := {t | (t 0).1 = n}

/-- A parameter: the singleton of an arbitrary element. -/
abbrev paramRel (p : El U) : Rel U 1 := {t | t 0 = p}

/-- Substitution of variables: precomposition with a map of indices.  This
covers permutation, identification and the addition of dummy variables. -/
abbrev reindex {k l : ℕ} (f : Fin k → Fin l) (C : Rel U k) : Rel U l :=
  {t | (t ∘ f) ∈ C}

/-- Existential quantification of the last variable, bounded by sort `n`. -/
abbrev exists_ (n : ℕ) {k : ℕ} (C : Rel U (k + 1)) : Rel U k :=
  {t | ∃ x : El U, x.1 = n ∧ Fin.snoc t x ∈ C}

/-- Universal quantification bounded by a sort, derived from the existential. -/
abbrev forall_ (n : ℕ) {k : ℕ} (C : Rel U (k + 1)) : Rel U k :=
  (exists_ U n Cᶜ)ᶜ

/-- Tuples all of whose entries lie in sort `n`. -/
def sortTuple (n k : ℕ) : Rel U k := {t | ∀ i, (t i).1 = n}

/-- A relation on sort `n`, viewed as a relation on the union. -/
abbrev liftRel {n k : ℕ} (C : Set (Fin k → U n)) : Rel U k :=
  {t | ∃ s : Fin k → U n, (∀ i, t i = inj U (s i)) ∧ s ∈ C}

/-- Sets of elements of a fixed sort, viewed as unary relations. -/
abbrev SortClass (n : ℕ) (S : Set (U n)) : Rel U 1 :=
  {t | ∃ x : U n, t 0 = inj U x ∧ x ∈ S}

/-- The element of sort `n` underlying an element of the union known to have
sort `n`. -/
def toSort {n : ℕ} (z : El U) (h : z.1 = n) : U n := h ▸ z.2

theorem inj_toSort {n : ℕ} (z : El U) (h : z.1 = n) : inj U (toSort U z h) = z := by
  obtain ⟨m, x⟩ := z
  cases h
  rfl

theorem inj_injective {n : ℕ} {x y : U n} (h : inj U x = inj U y) : x = y :=
  eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem mem_forall_iff (n : ℕ) {k : ℕ} (C : Rel U (k + 1)) (t : Fin k → El U) :
    t ∈ forall_ U n C ↔ ∀ x : El U, x.1 = n → Fin.snoc t x ∈ C := by
  simp only [forall_, exists_, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists, not_and, not_not]

end Sorted

/-- A class system on a sorted carrier: relations closed under the
first-order operations with sort-bounded quantifiers, containing equality,
the sort predicates and all parameters.  `D k` is the set of admissible
relations of arity `k`.  The atoms are per sort, so that the parametrically
definable relations of a first-order model form a class system. -/
structure ClassSys (U : ℕ → Type u) where
  D : (k : ℕ) → Set (Sorted.Rel U k)
  eq_mem : Sorted.eqRel U ∈ D 2
  sort_mem : ∀ n, Sorted.sortRel U n ∈ D 1
  param_mem : ∀ p, Sorted.paramRel U p ∈ D 1
  univ_mem : ∀ k, (Set.univ : Sorted.Rel U k) ∈ D k
  inter_mem : ∀ {k} {C C' : Sorted.Rel U k}, C ∈ D k → C' ∈ D k → C ∩ C' ∈ D k
  compl_mem : ∀ {k} {C : Sorted.Rel U k}, C ∈ D k → Cᶜ ∈ D k
  reindex_mem : ∀ {k l} (f : Fin k → Fin l) {C : Sorted.Rel U k},
    C ∈ D k → Sorted.reindex U f C ∈ D l
  exists_mem : ∀ (n : ℕ) {k} {C : Sorted.Rel U (k + 1)},
    C ∈ D (k + 1) → Sorted.exists_ U n C ∈ D k

namespace ClassSys

variable {U : ℕ → Type u} (𝒟 : ClassSys U)

theorem union_mem {k : ℕ} {C C' : Sorted.Rel U k} (h : C ∈ 𝒟.D k) (h' : C' ∈ 𝒟.D k) :
    C ∪ C' ∈ 𝒟.D k := by
  have : C ∪ C' = (Cᶜ ∩ C'ᶜ)ᶜ := by
    rw [Set.compl_inter, compl_compl, compl_compl]
  rw [this]
  exact 𝒟.compl_mem (𝒟.inter_mem (𝒟.compl_mem h) (𝒟.compl_mem h'))

theorem empty_mem (k : ℕ) : (∅ : Sorted.Rel U k) ∈ 𝒟.D k := by
  have : (∅ : Sorted.Rel U k) = (Set.univ)ᶜ := by simp
  rw [this]; exact 𝒟.compl_mem (𝒟.univ_mem k)

theorem forall_mem (n : ℕ) {k : ℕ} {C : Sorted.Rel U (k + 1)} (h : C ∈ 𝒟.D (k + 1)) :
    Sorted.forall_ U n C ∈ 𝒟.D k :=
  𝒟.compl_mem (𝒟.exists_mem n (𝒟.compl_mem h))

/-- A finite intersection of admissible relations is admissible. -/
theorem iInter_mem {k : ℕ} : ∀ {m : ℕ} (F : Fin m → Sorted.Rel U k),
    (∀ i, F i ∈ 𝒟.D k) → (⋂ i, F i) ∈ 𝒟.D k := by
  intro m
  induction m with
  | zero =>
    intro F _
    have : (⋂ i : Fin 0, F i) = Set.univ := by
      ext t; simp
    rw [this]; exact 𝒟.univ_mem k
  | succ m ih =>
    intro F hF
    have : (⋂ i : Fin (m + 1), F i) = F 0 ∩ ⋂ i : Fin m, F i.succ := by
      ext t; simp [Fin.forall_fin_succ]
    rw [this]
    exact 𝒟.inter_mem (hF 0) (ih (fun i => F i.succ) (fun i => hF i.succ))

theorem sortTuple_mem (n k : ℕ) : Sorted.sortTuple U n k ∈ 𝒟.D k := by
  have : Sorted.sortTuple U n k =
      (⋂ i : Fin k, Sorted.reindex U (fun _ : Fin 1 => i) (Sorted.sortRel U n) : Sorted.Rel U k) := by
    ext t
    simp only [Sorted.sortTuple, Set.mem_iInter, Sorted.reindex, Sorted.sortRel,
      Set.mem_setOf_eq, Function.comp_apply]
  rw [this]
  exact 𝒟.iInter_mem _ (fun i => 𝒟.reindex_mem _ (𝒟.sort_mem n))

/-- A set of elements of sort `n` is definable when its unary relation is. -/
def DefinableSet (n : ℕ) (S : Set (U n)) : Prop :=
  Sorted.SortClass U n S ∈ 𝒟.D 1

/-- Definability of a relation on sort `n`, read through the classes. -/
def DefOn (n : ℕ) (k : ℕ) (C : Set (Fin k → U n)) : Prop :=
  Sorted.liftRel U C ∈ 𝒟.D k

end ClassSys

/-! ### Towers -/

/-- A structure for the signature of the tower theory. -/
structure MemTower where
  U : ℕ → Type u
  mem : {n : ℕ} → U n → U n → Prop
  j : (n : ℕ) → U n → U (n + 1)
  κ : (n : ℕ) → U (n + 1)

namespace MemTower

variable (M : MemTower.{u})

/-- The disjoint union of the sorts; classes are relations on it. -/
abbrev El : Type u := Sorted.El M.U

/-- The sort of an element. -/
def sortOf (x : M.El) : ℕ := x.1

/-- Inject an element of a sort into the union. -/
abbrev inj {n : ℕ} (x : M.U n) : M.El := Sorted.inj M.U x

/-- Relations of arity `k` over the union. -/
abbrev Rel (k : ℕ) : Type u := Sorted.Rel M.U k

/-! ### Atomic relations -/

/-- Equality. -/
abbrev eqRel : M.Rel 2 := Sorted.eqRel M.U

/-- Membership within sort `n`. -/
def memRel (n : ℕ) : M.Rel 2 :=
  {t | ∃ x y : M.U n, t 0 = M.inj x ∧ t 1 = M.inj y ∧ M.mem x y}

/-- Membership within any sort (auxiliary; not an atom, since it spans all
profiles). -/
def memRelAll : M.Rel 2 :=
  {t | ∃ (n : ℕ) (x y : M.U n), t 0 = M.inj x ∧ t 1 = M.inj y ∧ M.mem x y}

/-- The sort predicate. -/
abbrev sortRel (n : ℕ) : M.Rel 1 := Sorted.sortRel M.U n

/-- The graph of the transition map from sort `n`. -/
def jRel (n : ℕ) : M.Rel 2 :=
  {t | ∃ x : M.U n, t 0 = M.inj x ∧ t 1 = M.inj (M.j n x)}

/-- The graph of all transition maps (auxiliary). -/
def jRelAll : M.Rel 2 :=
  {t | ∃ (n : ℕ) (x : M.U n), t 0 = M.inj x ∧ t 1 = M.inj (M.j n x)}

/-- The boundary constants. -/
def kappaRel (n : ℕ) : M.Rel 1 := {t | t 0 = M.inj (M.κ n)}

/-- A parameter: the singleton of an arbitrary element. -/
abbrev paramRel (p : M.El) : M.Rel 1 := Sorted.paramRel M.U p

/-! ### First-order operations on relations -/

abbrev reindex {k l : ℕ} (f : Fin k → Fin l) (C : M.Rel k) : M.Rel l :=
  Sorted.reindex M.U f C

abbrev exists_ (n : ℕ) {k : ℕ} (C : M.Rel (k + 1)) : M.Rel k := Sorted.exists_ M.U n C

abbrev forall_ (n : ℕ) {k : ℕ} (C : M.Rel (k + 1)) : M.Rel k := Sorted.forall_ M.U n C

abbrev sortTuple (n k : ℕ) : M.Rel k := Sorted.sortTuple M.U n k

theorem mem_forall_iff (n : ℕ) {k : ℕ} (C : M.Rel (k + 1)) (t : Fin k → M.El) :
    t ∈ M.forall_ n C ↔ ∀ x : M.El, x.1 = n → Fin.snoc t x ∈ C :=
  Sorted.mem_forall_iff M.U n C t

/-- The sort profile of a relation: every tuple in it has the stated sorts. -/
def HasProfile {k : ℕ} (a : Fin k → ℕ) (C : M.Rel k) : Prop :=
  ∀ t ∈ C, ∀ i, (t i).1 = a i

end MemTower

/-- A class system on a tower: a class system on its sorts containing the
membership, transition and constant atoms. -/
structure ClassSystem (M : MemTower.{u}) extends ClassSys M.U where
  memRel_mem : ∀ n, M.memRel n ∈ D 2
  j_mem : ∀ n, M.jRel n ∈ D 2
  kappa_mem : ∀ n, M.kappaRel n ∈ D 1

namespace ClassSystem

variable {M : MemTower.{u}} (𝒟 : ClassSystem M)

/-- Membership of a relation in the system. -/
def Definable {k : ℕ} (C : M.Rel k) : Prop := C ∈ 𝒟.D k

theorem union_mem {k : ℕ} {C C' : M.Rel k} (h : C ∈ 𝒟.D k) (h' : C' ∈ 𝒟.D k) :
    C ∪ C' ∈ 𝒟.D k := 𝒟.toClassSys.union_mem h h'

theorem empty_mem (k : ℕ) : (∅ : M.Rel k) ∈ 𝒟.D k := 𝒟.toClassSys.empty_mem k

theorem forall_mem (n : ℕ) {k : ℕ} {C : M.Rel (k + 1)} (h : C ∈ 𝒟.D (k + 1)) :
    M.forall_ n C ∈ 𝒟.D k := 𝒟.toClassSys.forall_mem n h

theorem iInter_mem {k : ℕ} {m : ℕ} (F : Fin m → M.Rel k) (hF : ∀ i, F i ∈ 𝒟.D k) :
    (⋂ i, F i) ∈ 𝒟.D k := 𝒟.toClassSys.iInter_mem F hF

theorem sortTuple_mem (n k : ℕ) : M.sortTuple n k ∈ 𝒟.D k := 𝒟.toClassSys.sortTuple_mem n k

/-- Sets of elements of a fixed sort, viewed as unary relations. -/
abbrev SortClass (n : ℕ) (S : Set (M.U n)) : M.Rel 1 := Sorted.SortClass M.U n S

/-- A set of elements of sort `n` is definable when its unary relation is. -/
abbrev DefinableSet (n : ℕ) (S : Set (M.U n)) : Prop := 𝒟.toClassSys.DefinableSet n S

end ClassSystem

/-! ### Lifting along transitions -/

namespace MemTower

variable (M : MemTower.{u})

/-- Iterated transition map from sort `m` to sort `n ≥ m`. -/
def liftLE {m n : ℕ} (h : m ≤ n) (x : M.U m) : M.U n :=
  Nat.leRecOn h (fun {k} y => M.j k y) x

theorem liftLE_self {m : ℕ} (x : M.U m) : M.liftLE (le_refl m) x = x := by
  unfold liftLE; exact Nat.leRecOn_self x

theorem liftLE_succ {m n : ℕ} (h : m ≤ n) (x : M.U m) :
    M.liftLE (Nat.le_succ_of_le h) x = M.j n (M.liftLE h x) := by
  unfold liftLE; exact Nat.leRecOn_succ h x

end MemTower

/-! ### Presentations and definable isomorphisms -/

/-- A presentation of the tower `P` inside the tower `M`: elements of sort `n`
of `P` are represented by elements of sort `a n` of `M`, surjectively. -/
structure Presentation (U V : ℕ → Type u) where
  a : ℕ → ℕ
  rep : ∀ n, U (a n) → Option (V n)
  surj : ∀ n (p : V n), ∃ x, rep n x = some p

namespace Presentation

/-- Composition: represent `P` in `M` through `N`. -/
def comp {U V W : ℕ → Type u} (p : Presentation U V) (q : Presentation V W) :
    Presentation U W where
  a n := p.a (q.a n)
  rep n x := (p.rep (q.a n) x).bind (q.rep n)
  surj := by
    intro n z
    obtain ⟨y, hy⟩ := q.surj n z
    obtain ⟨x, hx⟩ := p.surj (q.a n) y
    exact ⟨x, by simp [hx, hy]⟩

end Presentation

end SolidLean.Solid
