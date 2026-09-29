module

public import Solid.Gen.Core

/-!
# Relational signatures, structures, and isomorphisms

A `Signature` has relation symbols with arities given by lists of sort
indices (sorts are indexed by `ℕ` throughout; any countable sort set is
encoded).  A `Str Sig` is a sorted carrier with one relation per symbol, given
as a set of sorted tuples of the union.  A class system on a structure
(`StrSys`) is a class system on the carrier containing the relation atoms.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-- A relational signature with `ℕ`-indexed sorts: each symbol has an arity
and a sort for each argument position. -/
structure Signature where
  Rel : Type
  arity : Rel → ℕ
  sortAt : (r : Rel) → Fin (arity r) → ℕ

/-- A structure for a signature. -/
structure Str (Sig : Signature) where
  U : ℕ → Type u
  rel : (r : Sig.Rel) → Sorted.Rel U (Sig.arity r)
  rel_sorts : ∀ r t, t ∈ rel r → ∀ i, (t i).1 = Sig.sortAt r i

/-- A class system on a structure: a class system on its carrier containing
the relation atoms. -/
structure StrSys {Sig : Signature} (M : Str.{u} Sig) extends ClassSys M.U where
  rel_mem : ∀ r, M.rel r ∈ D (Sig.arity r)

/-- A structure with a class system. -/
structure StrWithSys (Sig : Signature) where
  M : Str.{u} Sig
  𝒟 : StrSys M

/-- An isomorphism of structures. -/
structure GenIso {Sig : Signature} (M N : Str.{u} Sig) where
  toFun : ∀ n, M.U n → N.U n
  bijective : ∀ n, Function.Bijective (toFun n)
  rel_iff : ∀ r (t : Fin (Sig.arity r) → Sorted.El M.U),
    t ∈ M.rel r ↔ (fun i => (⟨(t i).1, toFun (t i).1 (t i).2⟩ : Sorted.El N.U)) ∈ N.rel r

namespace GenIso

variable {Sig : Signature} {M N : Str.{u} Sig} (i : GenIso M N)

/-- The action on the union of sorts. -/
def mapEl (z : Sorted.El M.U) : Sorted.El N.U := ⟨z.1, i.toFun z.1 z.2⟩

@[simp] theorem mapEl_inj {n : ℕ} (x : M.U n) : i.mapEl (Sorted.inj M.U x) = Sorted.inj N.U (i.toFun n x) :=
  rfl

theorem mapEl_injective : Function.Injective i.mapEl := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hnm : n = m := congrArg Sigma.fst h
  subst hnm
  have := (i.bijective n).1 (Sorted.inj_injective N.U h)
  exact Sigma.ext rfl (heq_of_eq this)

theorem mapEl_surjective : Function.Surjective i.mapEl := by
  rintro ⟨n, y⟩
  obtain ⟨x, rfl⟩ := (i.bijective n).2 y
  exact ⟨⟨n, x⟩, rfl⟩

/-- `i : M → P` is `𝒟`-definable with respect to a presentation of `P` in `M`:
the graph relating `x` to a representative of `i x` is admissible. -/
def DefinableIn (𝒟 : ClassSys M.U) (p : Presentation M.U N.U) : Prop :=
  ∀ n, ({t | ∃ (x : M.U n) (y : M.U (p.a n)),
    t 0 = Sorted.inj M.U x ∧ t 1 = Sorted.inj M.U y ∧ p.rep n y = some (i.toFun n x)} :
      Sorted.Rel M.U 2) ∈ 𝒟.D 2

/-- The inverse isomorphism. -/
noncomputable def symm : GenIso N M where
  toFun n := Function.surjInv (i.bijective n).2
  bijective n := by
    have hinv : Function.LeftInverse (i.toFun n) (Function.surjInv (i.bijective n).2) :=
      Function.surjInv_eq (i.bijective n).2
    constructor
    · intro x y hxy
      have := congrArg (i.toFun n) hxy
      rw [hinv, hinv] at this
      exact this
    · intro x
      refine ⟨i.toFun n x, ?_⟩
      apply (i.bijective n).1
      rw [hinv]
  rel_iff r t := by
    have hinv : ∀ n, Function.LeftInverse (i.toFun n) (Function.surjInv (i.bijective n).2) :=
      fun n => Function.surjInv_eq (i.bijective n).2
    rw [i.rel_iff r]
    have : (fun i' => (⟨(t i').1, i.toFun (t i').1 (Function.surjInv (i.bijective (t i').1).2 (t i').2)⟩ :
        Sorted.El N.U)) = t := by
      funext i'
      exact Sigma.ext rfl (heq_of_eq (hinv _ _))
    rw [this]

theorem toFun_symm {n : ℕ} (y : N.U n) : i.toFun n (i.symm.toFun n y) = y :=
  Function.surjInv_eq (i.bijective n).2 y

theorem symm_toFun {n : ℕ} (x : M.U n) : i.symm.toFun n (i.toFun n x) = x :=
  (i.bijective n).1 (i.toFun_symm (i.toFun n x))

end GenIso

end SolidLean.Solid
