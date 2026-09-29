module

public import Solid.Tower

/-!
# Internal set theory of one sort

A `MemStr` is a single membership structure.  Everything set-theoretic that
the tower proof needs is *defined* here as a predicate on such a structure,
in the first-order language of membership: Kuratowski pairs, functions,
ordinals, the rank hierarchy, cardinals, inaccessibility, and the two ladder
clauses.  Nothing is assumed about the structure; the axioms of ZFC with
Separation and Replacement restricted to a class system are packaged in
`SetAxioms`.

The lemmas about these notions (existence of the rank hierarchy, the
Mostowski collapse, Cantor's theorem, absoluteness) belong to
`Solid.Internal` and are the substantive internal-set-theory obligations of
draft 2 §2.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-- A single-sorted membership structure. -/
structure MemStr where
  X : Type u
  mem : X → X → Prop

namespace MemStr

variable (S : MemStr.{u})

/-- Relations of arity `k` on the carrier. -/
abbrev Rel (k : ℕ) : Type u := Set (Fin k → S.X)

/-! ### Elementary notions -/

def Subset (x y : S.X) : Prop := ∀ z, S.mem z x → S.mem z y

def IsEmptySet (x : S.X) : Prop := ∀ z, ¬ S.mem z x

def Nonempty (x : S.X) : Prop := ∃ z, S.mem z x

def IsPairSet (a b p : S.X) : Prop := ∀ z, S.mem z p ↔ z = a ∨ z = b

def IsSingleton (a s : S.X) : Prop := ∀ z, S.mem z s ↔ z = a

/-- Kuratowski ordered pair `{{a}, {a, b}}`. -/
def IsOrdPair (a b p : S.X) : Prop :=
  ∃ s d, S.IsSingleton a s ∧ S.IsPairSet a b d ∧ S.IsPairSet s d p

def IsUnionSet (x u : S.X) : Prop := ∀ z, S.mem z u ↔ ∃ y, S.mem y x ∧ S.mem z y

def IsPowerSet (x p : S.X) : Prop := ∀ z, S.mem z p ↔ S.Subset z x

/-- `s = x ∪ {x}`. -/
def IsSucc (x s : S.X) : Prop := ∀ z, S.mem z s ↔ S.mem z x ∨ z = x

def Transitive (x : S.X) : Prop := ∀ y, S.mem y x → S.Subset y x

/-! ### Relations and functions as sets of ordered pairs -/

def IsRelation (r : S.X) : Prop := ∀ p, S.mem p r → ∃ a b, S.IsOrdPair a b p

/-- `f(a) = b`. -/
def FunApp (f a b : S.X) : Prop := ∃ p, S.mem p f ∧ S.IsOrdPair a b p

def InDom (f a : S.X) : Prop := ∃ b, S.FunApp f a b

def IsFunction (f : S.X) : Prop :=
  S.IsRelation f ∧ ∀ a b b', S.FunApp f a b → S.FunApp f a b' → b = b'

def IsFunctionOn (f d : S.X) : Prop :=
  S.IsFunction f ∧ ∀ a, S.InDom f a ↔ S.mem a d

def Injective (f : S.X) : Prop :=
  ∀ a a' b, S.FunApp f a b → S.FunApp f a' b → a = a'

def MapsInto (f c : S.X) : Prop := ∀ a b, S.FunApp f a b → S.mem b c

def IsInjectionInto (f d c : S.X) : Prop :=
  S.IsFunctionOn f d ∧ S.Injective f ∧ S.MapsInto f c

def IsBijectionOnto (f d c : S.X) : Prop :=
  S.IsInjectionInto f d c ∧ ∀ b, S.mem b c → ∃ a, S.FunApp f a b

/-! ### Ordinals -/

/-- Transitive, all members transitive, and linearly ordered by membership. -/
def IsOrdinal (x : S.X) : Prop :=
  S.Transitive x ∧ (∀ y, S.mem y x → S.Transitive y) ∧
    ∀ y z, S.mem y x → S.mem z x → S.mem y z ∨ y = z ∨ S.mem z y

def IsLimitOrd (x : S.X) : Prop :=
  S.IsOrdinal x ∧ S.Nonempty x ∧ ∀ y, S.mem y x → ∃ s, S.IsSucc y s ∧ S.mem s x

def IsSuccOrd (x : S.X) : Prop := S.IsOrdinal x ∧ ∃ y, S.IsSucc y x

/-! ### The rank hierarchy -/

/-- A partial attempt at the function `α ↦ V_α`: wherever defined it satisfies
the recursion clauses. -/
def IsVAttempt (f : S.X) : Prop :=
  S.IsFunction f ∧ ∀ β v, S.FunApp f β v →
    S.IsOrdinal β ∧
    (S.IsEmptySet β → S.IsEmptySet v) ∧
    (∀ γ, S.IsSucc γ β → ∃ w, S.FunApp f γ w ∧ S.IsPowerSet w v) ∧
    (S.IsLimitOrd β → ∀ z, S.mem z v ↔ ∃ γ w, S.mem γ β ∧ S.FunApp f γ w ∧ S.mem z w)

/-- `v = V_α`: some attempt defined on all of `α ∪ {α}` takes the value `v`
at `α`. -/
def IsV (α v : S.X) : Prop :=
  S.IsOrdinal α ∧ ∃ f, S.IsVAttempt f ∧
    (∀ γ, S.mem γ α ∨ γ = α → S.InDom f γ) ∧ S.FunApp f α v

/-- `v` is a rank segment `V_α` for some ordinal `α`. -/
def IsRankSegment (v : S.X) : Prop := ∃ α, S.IsV α v

/-! ### Cardinals and inaccessibility -/

def IsCardinal (κ : S.X) : Prop :=
  S.IsOrdinal κ ∧ ∀ β, S.mem β κ → ¬ ∃ f, S.IsBijectionOnto f β κ

/-- Every function from a smaller ordinal into `κ` is bounded below `κ`. -/
def IsRegular (κ : S.X) : Prop :=
  S.IsOrdinal κ ∧ ∀ β f, S.mem β κ → S.IsFunctionOn f β → S.MapsInto f κ →
    ∃ γ, S.mem γ κ ∧ ∀ a b, S.FunApp f a b → S.mem b γ

/-- For every `β < κ`, the power set of `β` injects into some `γ < κ`. -/
def IsStrongLimit (κ : S.X) : Prop :=
  S.IsOrdinal κ ∧ ∀ β, S.mem β κ → ∀ p, S.IsPowerSet β p →
    ∃ γ f, S.mem γ κ ∧ S.IsInjectionInto f p γ

/-- Uncountable (some limit ordinal lies below), regular, strong limit. -/
def Inaccessible (κ : S.X) : Prop :=
  S.IsCardinal κ ∧ (∃ ω, S.mem ω κ ∧ S.IsLimitOrd ω) ∧ S.IsRegular κ ∧ S.IsStrongLimit κ

/-- `β` is the least inaccessible above `α`. -/
def NextInaccessible (α β : S.X) : Prop :=
  S.Inaccessible β ∧ S.mem α β ∧ ∀ γ, S.mem α γ → S.mem γ β → ¬ S.Inaccessible γ

/-- No greatest inaccessible below `κ`. -/
def NoGreatestInaccessibleBelow (κ : S.X) : Prop :=
  ∀ α, S.mem α κ → S.Inaccessible α → ∃ β, S.mem β κ ∧ S.mem α β ∧ S.Inaccessible β

/-! ### Membership-preserving maps between structures -/

end MemStr

/-- A class system on a single membership structure. -/
structure SetClassSystem (S : MemStr.{u}) where
  D : (k : ℕ) → Set (S.Rel k)
  eq_mem : ({t | t 0 = t 1} : S.Rel 2) ∈ D 2
  memRel_mem : ({t | S.mem (t 0) (t 1)} : S.Rel 2) ∈ D 2
  param_mem : ∀ p : S.X, ({t | t 0 = p} : S.Rel 1) ∈ D 1
  univ_mem : ∀ k, (Set.univ : S.Rel k) ∈ D k
  inter_mem : ∀ {k} {C C' : S.Rel k}, C ∈ D k → C' ∈ D k → C ∩ C' ∈ D k
  compl_mem : ∀ {k} {C : S.Rel k}, C ∈ D k → Cᶜ ∈ D k
  reindex_mem : ∀ {k l} (f : Fin k → Fin l) {C : S.Rel k},
    C ∈ D k → ({t | (t ∘ f) ∈ C} : S.Rel l) ∈ D l
  exists_mem : ∀ {k} {C : S.Rel (k + 1)},
    C ∈ D (k + 1) → ({t | ∃ x, Fin.snoc t x ∈ C} : S.Rel k) ∈ D k

/-- The axioms of ZFC for a membership structure, with Separation and
Replacement restricted to the classes of a given family `Def` (parameters are
the leading coordinates; the quantified coordinate is last). -/
structure SetAxioms (S : MemStr.{u}) (Def : (k : ℕ) → S.Rel k → Prop) : Prop where
  ext : ∀ x y, (∀ z, S.mem z x ↔ S.mem z y) → x = y
  empty : ∃ e, S.IsEmptySet e
  pair : ∀ a b, ∃ p, S.IsPairSet a b p
  union : ∀ x, ∃ u, S.IsUnionSet x u
  power : ∀ x, ∃ p, S.IsPowerSet x p
  infinity : ∃ I, (∃ e, S.IsEmptySet e ∧ S.mem e I) ∧
    ∀ x, S.mem x I → ∃ s, S.IsSucc x s ∧ S.mem s I
  separation : ∀ {k} (C : S.Rel (k + 1)), Def (k + 1) C → ∀ (p : Fin k → S.X) (x : S.X),
    ∃ s, ∀ y, S.mem y s ↔ S.mem y x ∧ Fin.snoc p y ∈ C
  replacement : ∀ {k} (C : S.Rel (k + 2)), Def (k + 2) C → ∀ (p : Fin k → S.X) (x : S.X),
    (∀ y, S.mem y x → ∃! z, Fin.snoc (Fin.snoc p y) z ∈ C) →
    ∃ s, ∀ z, S.mem z s ↔ ∃ y, S.mem y x ∧ Fin.snoc (Fin.snoc p y) z ∈ C
  foundation : ∀ x, S.Nonempty x → ∃ y, S.mem y x ∧ ∀ z, S.mem z y → ¬ S.mem z x
  choice : ∀ x, (∀ y, S.mem y x → S.Nonempty y) →
    ∃ f, S.IsFunctionOn f x ∧ ∀ y v, S.FunApp f y v → S.mem v y

/-- A model of ZFC in the class-system sense: a structure, a class system,
and the axioms for that system. -/
structure ZFCModel where
  S : MemStr.{u}
  𝒞 : SetClassSystem S
  ax : SetAxioms S (fun k C => C ∈ 𝒞.D k)

/-! ### Reading a sort of a tower as a membership structure -/

namespace MemTower

variable (M : MemTower.{u})

/-- Sort `n` as a membership structure. -/
abbrev sortStr (n : ℕ) : MemStr.{u} := ⟨M.U n, fun x y => M.mem x y⟩

/-- A relation on sort `n`, viewed as a relation on the union. -/
abbrev liftRel {n k : ℕ} (C : (M.sortStr n).Rel k) : M.Rel k := Sorted.liftRel M.U C

end MemTower

namespace ClassSystem

variable {M : MemTower.{u}} (𝒟 : ClassSystem M)

/-- Definability of a relation on sort `n`, read through the tower's classes. -/
abbrev DefOn (n : ℕ) (k : ℕ) (C : (M.sortStr n).Rel k) : Prop := 𝒟.toClassSys.DefOn n k C

end ClassSystem

end SolidLean.Solid
