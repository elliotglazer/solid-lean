import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Set.Basic

/-!
# The tower theory `H` is solid — the statement

`H` is the many-sorted first-order theory of a tower of universes
`Z₀, Z₁, …`: each sort satisfies ZFC (with Separation and Replacement as
schemes over all formulas of the language, parameters allowed); sort `Zₙ₊₁`
carries a distinguished inaccessible cardinal `κₙ`, and the transition map
`jₙ : Zₙ → Zₙ₊₁` is a membership isomorphism of `Zₙ` onto the rank segment
`V(κₙ)`; `κₙ₊₁` is the least inaccessible above `jₙ₊₁(κₙ)`; and in `Z₁` there
is no greatest inaccessible below `κ₀`.

Enayat's *solidity*: a theory `T` is solid when, for models `M ⊳ N ⊳ P` (each
interpreted in the previous one) with an `M`-definable isomorphism `M ≅ P`,
there is an `M`-definable isomorphism `M ≅ N`.  Solid theories are tight, so
`T` determines its models up to definable isomorphism in the way ZF and PA do.

This file states that `H` is solid.  Everything is defined here, from the
first-order syntax up; the only theorem, at the end, is `tower_theory_solid`,
to be proved elsewhere.  The many-sorted logic is written out rather than
taken from a library: a structure for the language is a `Tower` (sorts,
membership, transition maps, distinguished cardinals), and `Formula` is the
inductive type of its many-sorted first-order formulas, with satisfaction
`Formula.Sat`.

**Reading guide.**
* `Tower`: a structure for the language; `El` is the disjoint union of its
  sorts and a relation of arity `k` is a set of `k`-tuples of `El`.
* `Formula k s`: formulas with `k` free variables of sorts `s`, de Bruijn
  style (`ex n φ` binds the last variable of `φ`, of sort `n`); the atoms are
  membership and the transition graphs within a sort, the distinguished
  cardinals, and equality.  `Definable T k C`: for each assignment of sorts to
  the `k` coordinates, the tuples of `C` of those sorts are those satisfying
  a formula with parameters.
* `IsModelH T`: the axioms of `H`, with the schemes of Separation and
  Replacement stated for all definable classes — i.e. `T` is a model of the
  first-order theory `H`.
* `Interp T`: a finitary interpretation of the language in `T` in
  one-coordinate normal form (the `n`-th interpreted sort is a definable set
  of elements of a single sort `a n` of `T`, modulo a definable equivalence;
  in a model of `H` finite tuples are coded by single elements, so this loses
  no generality — that reduction is not part of the statement).  `I.Model` is
  the interpreted tower and `I.pres` the presentation of its elements by
  elements of `T`.
* `Iso T T'` is an isomorphism of towers, and `Iso.DefinableIn i pr` says that
  `i : Iso T P` is `T`-definable with respect to a presentation `pr` of `P`
  in `T`, sort by sort.
* `Solid`: Enayat's condition for `H`, with `P = J.Model` presented in `T`
  through the composite presentation.
-/

universe u

namespace SolidLean.Palomar

/-! ### Towers: structures for the language of `H` -/

/-- A structure for the language of `H`: sorts `U n`, membership within each
sort, transition maps `j n : U n → U (n + 1)`, and the distinguished cardinals
`κ n : U (n + 1)`. -/
structure Tower where
  U : ℕ → Type u
  mem : {n : ℕ} → U n → U n → Prop
  j : (n : ℕ) → U n → U (n + 1)
  κ : (n : ℕ) → U (n + 1)

namespace Tower

variable (T : Tower.{u})

/-- The disjoint union of the sorts. -/
abbrev El : Type u := Σ n, T.U n

/-- An element of a sort, in the union. -/
abbrev inj {n : ℕ} (x : T.U n) : T.El := ⟨n, x⟩

/-- Relations of arity `k` on the union. -/
abbrev Rel (k : ℕ) : Type u := Set (Fin k → T.El)

/-- A relation on sort `n`, viewed as a relation on the union. -/
abbrev liftRel {n k : ℕ} (C : Set (Fin k → T.U n)) : T.Rel k :=
  {t | ∃ s : Fin k → T.U n, (∀ i, t i = T.inj (s i)) ∧ s ∈ C}

end Tower

/-! ### Many-sorted first-order formulas and definability -/

/-- Formulas with `k` free variables of sorts `s`.  `mem n i₀ i₁` is
"`x_{i₀} ∈ x_{i₁}`" in sort `n`, `jmap n i₀ i₁` is "`x_{i₁} = jₙ x_{i₀}`",
`kappa n i` is "`xᵢ = κₙ`", `eq i₀ i₁` is "`x_{i₀} = x_{i₁}`"; `ex n φ` binds the
last variable of `φ`, of sort `n`. -/
inductive Formula : (k : ℕ) → (Fin k → ℕ) → Type
  | mem {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (i₀ i₁ : Fin k) (h₀ : s i₀ = n) (h₁ : s i₁ = n) : Formula k s
  | jmap {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (i₀ i₁ : Fin k) (h₀ : s i₀ = n) (h₁ : s i₁ = n + 1) :
      Formula k s
  | kappa {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (i : Fin k) (hi : s i = n + 1) : Formula k s
  | eq {k : ℕ} {s : Fin k → ℕ} (i₀ i₁ : Fin k) (h : s i₀ = s i₁) : Formula k s
  | false_ {k : ℕ} {s : Fin k → ℕ} : Formula k s
  | imp {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula k s) : Formula k s
  | ex {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (φ : Formula (k + 1) (Fin.snoc s n)) : Formula k s

/-- Satisfaction of a formula in a tower, at a tuple of elements of the union. -/
def Formula.Sat (T : Tower.{u}) : {k : ℕ} → {s : Fin k → ℕ} → Formula k s → (Fin k → T.El) → Prop
  | _, _, .mem n i₀ i₁ _ _, t => ∃ x y : T.U n, t i₀ = T.inj x ∧ t i₁ = T.inj y ∧ T.mem x y
  | _, _, .jmap n i₀ i₁ _ _, t => ∃ x : T.U n, t i₀ = T.inj x ∧ t i₁ = T.inj (T.j n x)
  | _, _, .kappa n i _, t => t i = T.inj (T.κ n)
  | _, _, .eq i₀ i₁ _, t => t i₀ = t i₁
  | _, _, .false_, _ => False
  | _, _, .imp φ ψ, t => Sat T φ t → Sat T ψ t
  | _, _, .ex n φ, t => ∃ x : T.El, x.1 = n ∧ Sat T φ (Fin.snoc t x)

namespace Tower

variable (T : Tower.{u})

/-- `C` is definable with parameters: for every assignment `s` of sorts to
the coordinates, the tuples of `C` of sorts `s` are exactly those satisfying
some formula `φ` at some parameters `p` (of sorts `ps`, placed before the
coordinates). -/
def Definable (k : ℕ) (C : T.Rel k) : Prop :=
  ∀ s : Fin k → ℕ, ∃ (a : ℕ) (ps : Fin a → ℕ) (φ : Formula (a + k) (Fin.append ps s))
    (p : Fin a → T.El), (∀ i, (p i).1 = ps i) ∧
      ∀ t : Fin k → T.El, (∀ i, (t i).1 = s i) → (t ∈ C ↔ φ.Sat T (Fin.append p t))

/-- Definability of a relation on sort `n`. -/
def DefOn (n k : ℕ) (C : Set (Fin k → T.U n)) : Prop := T.Definable k (T.liftRel C)

/-- Definability of a set of elements of sort `n`. -/
def DefinableSet (n : ℕ) (S : Set (T.U n)) : Prop :=
  T.Definable 1 {t | ∃ x : T.U n, t 0 = T.inj x ∧ x ∈ S}

end Tower

/-! ### Set-theoretic notions in a membership structure `(X, mem)` -/

section SetNotions

variable {X : Type u} (mem : X → X → Prop)

def Subset (x y : X) : Prop := ∀ z, mem z x → mem z y
def IsEmptySet (x : X) : Prop := ∀ z, ¬ mem z x
def Nonempty (x : X) : Prop := ∃ z, mem z x
def IsPairSet (a b p : X) : Prop := ∀ z, mem z p ↔ z = a ∨ z = b
def IsSingleton (a s : X) : Prop := ∀ z, mem z s ↔ z = a
/-- Kuratowski ordered pair `{{a}, {a, b}}`. -/
def IsOrdPair (a b p : X) : Prop :=
  ∃ s d, IsSingleton mem a s ∧ IsPairSet mem a b d ∧ IsPairSet mem s d p
def IsUnionSet (x u : X) : Prop := ∀ z, mem z u ↔ ∃ y, mem y x ∧ mem z y
def IsPowerSet (x p : X) : Prop := ∀ z, mem z p ↔ Subset mem z x
/-- `s = x ∪ {x}`. -/
def IsSucc (x s : X) : Prop := ∀ z, mem z s ↔ mem z x ∨ z = x
def Transitive (x : X) : Prop := ∀ y, mem y x → Subset mem y x

def IsRelation (r : X) : Prop := ∀ p, mem p r → ∃ a b, IsOrdPair mem a b p
/-- `f(a) = b`. -/
def FunApp (f a b : X) : Prop := ∃ p, mem p f ∧ IsOrdPair mem a b p
def InDom (f a : X) : Prop := ∃ b, FunApp mem f a b
def IsFunction (f : X) : Prop :=
  IsRelation mem f ∧ ∀ a b b', FunApp mem f a b → FunApp mem f a b' → b = b'
def IsFunctionOn (f d : X) : Prop := IsFunction mem f ∧ ∀ a, InDom mem f a ↔ mem a d
def Injective (f : X) : Prop := ∀ a a' b, FunApp mem f a b → FunApp mem f a' b → a = a'
def MapsInto (f c : X) : Prop := ∀ a b, FunApp mem f a b → mem b c
def IsInjectionInto (f d c : X) : Prop := IsFunctionOn mem f d ∧ Injective mem f ∧ MapsInto mem f c
def IsBijectionOnto (f d c : X) : Prop :=
  IsInjectionInto mem f d c ∧ ∀ b, mem b c → ∃ a, FunApp mem f a b

/-- Transitive, all members transitive, and linearly ordered by membership. -/
def IsOrdinal (x : X) : Prop :=
  Transitive mem x ∧ (∀ y, mem y x → Transitive mem y) ∧
    ∀ y z, mem y x → mem z x → mem y z ∨ y = z ∨ mem z y
def IsLimitOrd (x : X) : Prop :=
  IsOrdinal mem x ∧ Nonempty mem x ∧ ∀ y, mem y x → ∃ s, IsSucc mem y s ∧ mem s x

/-- A partial attempt at the function `α ↦ V_α`: wherever defined it satisfies
the recursion clauses. -/
def IsVAttempt (f : X) : Prop :=
  IsFunction mem f ∧ ∀ β v, FunApp mem f β v →
    IsOrdinal mem β ∧
    (IsEmptySet mem β → IsEmptySet mem v) ∧
    (∀ γ, IsSucc mem γ β → ∃ w, FunApp mem f γ w ∧ IsPowerSet mem w v) ∧
    (IsLimitOrd mem β → ∀ z, mem z v ↔ ∃ γ w, mem γ β ∧ FunApp mem f γ w ∧ mem z w)
/-- `v = V_α`: some attempt defined on all of `α ∪ {α}` takes the value `v` at `α`. -/
def IsV (α v : X) : Prop :=
  IsOrdinal mem α ∧ ∃ f, IsVAttempt mem f ∧
    (∀ γ, mem γ α ∨ γ = α → InDom mem f γ) ∧ FunApp mem f α v

def IsCardinal (κ : X) : Prop :=
  IsOrdinal mem κ ∧ ∀ β, mem β κ → ¬ ∃ f, IsBijectionOnto mem f β κ
/-- Every function from a smaller ordinal into `κ` is bounded below `κ`. -/
def IsRegular (κ : X) : Prop :=
  IsOrdinal mem κ ∧ ∀ β f, mem β κ → IsFunctionOn mem f β → MapsInto mem f κ →
    ∃ γ, mem γ κ ∧ ∀ a b, FunApp mem f a b → mem b γ
/-- For every `β < κ`, the power set of `β` injects into some `γ < κ`. -/
def IsStrongLimit (κ : X) : Prop :=
  IsOrdinal mem κ ∧ ∀ β, mem β κ → ∀ p, IsPowerSet mem β p →
    ∃ γ f, mem γ κ ∧ IsInjectionInto mem f p γ
/-- Uncountable (some limit ordinal lies below), regular, strong limit. -/
def Inaccessible (κ : X) : Prop :=
  IsCardinal mem κ ∧ (∃ ω, mem ω κ ∧ IsLimitOrd mem ω) ∧ IsRegular mem κ ∧ IsStrongLimit mem κ
/-- `β` is the least inaccessible above `α`. -/
def NextInaccessible (α β : X) : Prop :=
  Inaccessible mem β ∧ mem α β ∧ ∀ γ, mem α γ → mem γ β → ¬ Inaccessible mem γ
/-- No greatest inaccessible below `κ`. -/
def NoGreatestInaccessibleBelow (κ : X) : Prop :=
  ∀ α, mem α κ → Inaccessible mem α → ∃ β, mem β κ ∧ mem α β ∧ Inaccessible mem β

/-- The axioms of ZFC for `(X, mem)`, with Separation and Replacement for the
classes satisfying `Def` (parameters are the leading coordinates; the
quantified coordinate is last). -/
structure SetAxioms (Def : (k : ℕ) → Set (Fin k → X) → Prop) : Prop where
  ext : ∀ x y, (∀ z, mem z x ↔ mem z y) → x = y
  empty : ∃ e, IsEmptySet mem e
  pair : ∀ a b, ∃ p, IsPairSet mem a b p
  union : ∀ x, ∃ u, IsUnionSet mem x u
  power : ∀ x, ∃ p, IsPowerSet mem x p
  infinity : ∃ I, (∃ e, IsEmptySet mem e ∧ mem e I) ∧
    ∀ x, mem x I → ∃ s, IsSucc mem x s ∧ mem s I
  separation : ∀ {k} (C : Set (Fin (k + 1) → X)), Def (k + 1) C → ∀ (p : Fin k → X) (x : X),
    ∃ s, ∀ y, mem y s ↔ mem y x ∧ Fin.snoc p y ∈ C
  replacement : ∀ {k} (C : Set (Fin (k + 2) → X)), Def (k + 2) C → ∀ (p : Fin k → X) (x : X),
    (∀ y, mem y x → ∃! z, Fin.snoc (Fin.snoc p y) z ∈ C) →
    ∃ s, ∀ z, mem z s ↔ ∃ y, mem y x ∧ Fin.snoc (Fin.snoc p y) z ∈ C
  foundation : ∀ x, Nonempty mem x → ∃ y, mem y x ∧ ∀ z, mem z y → ¬ mem z x
  choice : ∀ x, (∀ y, mem y x → Nonempty mem y) →
    ∃ f, IsFunctionOn mem f x ∧ ∀ y v, FunApp mem f y v → mem v y

end SetNotions

/-! ### The axioms of `H` -/

/-- `T` is a model of `H`: every sort satisfies ZFC, with the schemes for all
definable classes; `jₙ` is injective and preserves membership; `κₙ` is
inaccessible in sort `n + 1` and the image of `jₙ` is the rank segment
`V(κₙ)`; `κₙ₊₁` is the least inaccessible above `jₙ₊₁(κₙ)`; and there is no
greatest inaccessible below `κ₀`. -/
structure Tower.IsModelH (T : Tower.{u}) : Prop where
  zfc : ∀ n, SetAxioms (T.mem (n := n)) (T.DefOn n)
  j_injective : ∀ n (x y : T.U n), T.j n x = T.j n y → x = y
  j_mem_iff : ∀ n (x y : T.U n), T.mem (T.j n x) (T.j n y) ↔ T.mem x y
  kappa_inaccessible : ∀ n, Inaccessible (T.mem (n := n + 1)) (T.κ n)
  j_image : ∀ n, ∃ v : T.U (n + 1), IsV (T.mem (n := n + 1)) (T.κ n) v ∧
    ∀ y, T.mem y v ↔ ∃ x, T.j n x = y
  next_inaccessible : ∀ n, NextInaccessible (T.mem (n := n + 2)) (T.j (n + 1) (T.κ n)) (T.κ (n + 1))
  bottom : NoGreatestInaccessibleBelow (T.mem (n := 1)) (T.κ 0)

/-! ### Interpretations -/

/-- A finitary interpretation of the language of `H` in `T`, in one-coordinate
normal form: the `n`-th interpreted sort is the definable set `dom n` of
elements of sort `a n`, modulo the definable equivalence `eqv n`; membership,
the transition maps and the distinguished cardinals are given by definable
relations respecting the equivalences. -/
structure Interp (T : Tower.{u}) where
  a : ℕ → ℕ
  dom : ∀ n, Set (T.U (a n))
  eqv : ∀ n, T.U (a n) → T.U (a n) → Prop
  eqv_refl : ∀ n x, x ∈ dom n → eqv n x x
  eqv_symm : ∀ n x y, eqv n x y → eqv n y x
  eqv_trans : ∀ n x y z, eqv n x y → eqv n y z → eqv n x z
  eqv_dom : ∀ n x y, eqv n x y → x ∈ dom n ∧ y ∈ dom n
  dom_def : ∀ n, T.DefinableSet (a n) (dom n)
  eqv_def : ∀ n, T.DefOn (a n) 2 {t | eqv n (t 0) (t 1)}
  memC : ∀ n, T.U (a n) → T.U (a n) → Prop
  memC_congr : ∀ n x x' y y', eqv n x x' → eqv n y y' → (memC n x y ↔ memC n x' y')
  jC : ∀ n, T.U (a n) → T.U (a (n + 1)) → Prop
  jC_total : ∀ n x, x ∈ dom n → ∃ y, y ∈ dom (n + 1) ∧ jC n x y
  jC_func : ∀ n x y y', y ∈ dom (n + 1) → y' ∈ dom (n + 1) →
    jC n x y → jC n x y' → eqv (n + 1) y y'
  jC_congr : ∀ n x x' y, eqv n x x' → jC n x y → jC n x' y
  jC_congr_right : ∀ n x y y', eqv (n + 1) y y' → jC n x y → jC n x y'
  kappaC : ∀ n, T.U (a (n + 1)) → Prop
  kappaC_exists : ∀ n, ∃ y, y ∈ dom (n + 1) ∧ kappaC n y
  kappaC_unique : ∀ n y y', y ∈ dom (n + 1) → y' ∈ dom (n + 1) →
    kappaC n y → kappaC n y' → eqv (n + 1) y y'
  kappaC_congr : ∀ n y y', eqv (n + 1) y y' → kappaC n y → kappaC n y'
  memC_def : ∀ n, T.DefOn (a n) 2 {t | memC n (t 0) (t 1)}
  jC_def : ∀ n, T.Definable 2 {t | ∃ x y, t 0 = T.inj x ∧ t 1 = T.inj y ∧ jC n x y}
  kappaC_def : ∀ n, T.DefinableSet (a (n + 1)) {y | kappaC n y}

namespace Interp

variable {T : Tower.{u}} (I : Interp T)

/-- The domain of interpreted sort `n`. -/
abbrev Dom (n : ℕ) : Type u := {x : T.U (I.a n) // x ∈ I.dom n}

/-- The equivalence on the domain of interpreted sort `n`. -/
def setoid (n : ℕ) : Setoid (I.Dom n) where
  r x y := I.eqv n x.1 y.1
  iseqv := ⟨fun x => I.eqv_refl n x.1 x.2, fun h => I.eqv_symm _ _ _ h,
    fun h h' => I.eqv_trans _ _ _ _ h h'⟩

/-- Interpreted sort `n`: the quotient of the domain by the equivalence. -/
abbrev Carrier (n : ℕ) : Type u := Quotient (I.setoid n)

/-- The class of a domain element. -/
def cls {n : ℕ} (x : I.Dom n) : I.Carrier n := Quotient.mk (I.setoid n) x

/-- Interpreted membership. -/
def memQ {n : ℕ} : I.Carrier n → I.Carrier n → Prop :=
  Quotient.lift₂ (fun x y : I.Dom n => I.memC n x.1 y.1) (by
    intro x y x' y' hx hy
    exact propext (I.memC_congr n x.1 x'.1 y.1 y'.1 hx hy))

/-- A `jC`-image of a domain element. -/
noncomputable def jImage {n : ℕ} (x : I.Dom n) : I.Dom (n + 1) :=
  ⟨Classical.choose (I.jC_total n x.1 x.2), (Classical.choose_spec (I.jC_total n x.1 x.2)).1⟩

theorem jImage_spec {n : ℕ} (x : I.Dom n) : I.jC n x.1 (I.jImage x).1 :=
  (Classical.choose_spec (I.jC_total n x.1 x.2)).2

/-- The interpreted transition map. -/
noncomputable def jQ (n : ℕ) : I.Carrier n → I.Carrier (n + 1) :=
  Quotient.lift (fun x : I.Dom n => I.cls (I.jImage x)) (by
    intro x y hxy
    apply Quotient.sound
    show I.eqv (n + 1) _ _
    have h1 : I.jC n y.1 (I.jImage x).1 := I.jC_congr n x.1 y.1 _ hxy (I.jImage_spec x)
    exact I.jC_func n y.1 _ _ (I.jImage x).2 (I.jImage y).2 h1 (I.jImage_spec y))

/-- The interpreted distinguished cardinal. -/
noncomputable def kappaQ (n : ℕ) : I.Carrier (n + 1) :=
  I.cls ⟨Classical.choose (I.kappaC_exists n), (Classical.choose_spec (I.kappaC_exists n)).1⟩

/-- The interpreted tower. -/
noncomputable def Model : Tower.{u} where
  U := I.Carrier
  mem := fun {n} x y => I.memQ (n := n) x y
  j := I.jQ
  κ := I.kappaQ

end Interp

/-! ### Presentations and definable isomorphisms -/

/-- A presentation of the tower `P` inside the tower `T`: elements of sort `n`
of `P` are represented, surjectively, by elements of sort `a n` of `T`. -/
structure Presentation (T P : Tower.{u}) where
  a : ℕ → ℕ
  rep : ∀ n, T.U (a n) → Option (P.U n)
  surj : ∀ n (p : P.U n), ∃ x, rep n x = some p

namespace Presentation

/-- Composition: represent `P` in `T` through `N`. -/
def comp {T N P : Tower.{u}} (p : Presentation T N) (q : Presentation N P) : Presentation T P where
  a n := p.a (q.a n)
  rep n x := (p.rep (q.a n) x).bind (q.rep n)
  surj := by
    intro n z
    obtain ⟨y, hy⟩ := q.surj n z
    obtain ⟨x, hx⟩ := p.surj (q.a n) y
    exact ⟨x, by simp [hx, hy]⟩

end Presentation

open Classical in
/-- The presentation of the interpreted tower in `T`: an element of the
domain of interpreted sort `n` represents its class. -/
noncomputable def Interp.pres {T : Tower.{u}} (I : Interp T) : Presentation T I.Model where
  a := I.a
  rep n x := if h : x ∈ I.dom n then some (I.cls ⟨x, h⟩) else none
  surj := by
    intro n p
    induction p using Quotient.ind with
    | _ x => exact ⟨x.1, by rw [dite_eq_left x.2]; rfl⟩

/-- An isomorphism of towers. -/
structure Iso (T N : Tower.{u}) where
  toFun : ∀ n, T.U n → N.U n
  bijective : ∀ n, Function.Bijective (toFun n)
  mem_iff : ∀ n (x y : T.U n), N.mem (toFun n x) (toFun n y) ↔ T.mem x y
  j_comm : ∀ n (x : T.U n), toFun (n + 1) (T.j n x) = N.j n (toFun n x)
  κ_comm : ∀ n, toFun (n + 1) (T.κ n) = N.κ n

/-- `i : T → P` is `T`-definable with respect to the presentation `pr` of `P`
in `T`: for every sort `n`, the relation "`y` represents `i x`" between
elements `x` of sort `n` and elements `y` of sort `pr.a n` is definable. -/
def Iso.DefinableIn {T P : Tower.{u}} (i : Iso T P) (pr : Presentation T P) : Prop :=
  ∀ n, T.Definable 2 {t | ∃ (x : T.U n) (y : T.U (pr.a n)),
    t 0 = T.inj x ∧ t 1 = T.inj y ∧ pr.rep n y = some (i.toFun n x)}

/-! ### Solidity -/

/-- **Enayat's solidity for `H`.**  For every model `T` of `H`, every
interpretation `I` in `T` whose interpreted tower is a model of `H`, every
interpretation `J` in `I.Model` whose interpreted tower is a model of `H`,
and every isomorphism `T ≅ J.Model` that is `T`-definable with respect to the
composite presentation, there is a `T`-definable isomorphism `T ≅ I.Model`. -/
def Solid : Prop :=
  ∀ (T : Tower.{u}), T.IsModelH →
    ∀ (I : Interp T), I.Model.IsModelH →
      ∀ (J : Interp I.Model), J.Model.IsModelH →
        ∀ (i : Iso T J.Model), i.DefinableIn (I.pres.comp J.pres) →
          ∃ h : Iso T I.Model, h.DefinableIn I.pres

/-- **The tower theory `H` is solid** (Theorem 2.1 of *Solid idealized Lean*). -/
theorem tower_theory_solid : Solid.{u} := by
  sorry

end SolidLean.Palomar
