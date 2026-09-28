import Foundation.FirstOrder.LK.Completeness
import Solid.FO.Bridge
import Solid.FO.Sound

/-!
# The single-sorted rendering, and provability by completeness

The many-sorted sentences of `FO/Axioms.lean` are rendered in the
single-sorted first-order logic of the `Foundation` library: a sort becomes a
unary predicate, a quantifier over a sort is relativized to it, equality
becomes the designated equality relation.  A first-order structure of the
rendered language whose equality is real determines a sorted structure
(`Render.sorted`), and satisfaction is preserved (`Render.tr_sat`).

Conversely a sorted structure determines a first-order structure on the union
of its sorts (`Render.unsorted`), again preserving satisfaction
(`Render.tr_sat'`).

Combined with `FO/Bridge.lean`, `FO/Sound.lean` and Foundation's soundness and
completeness theorems, this gives: a sentence is derivable in Foundation's
sequent calculus `LK` from the rendered axioms of `T(𝔉)` iff it is true in
every semantic model of `T(𝔉)` (`Render.provable_iff_semantic`).
-/

universe u v

namespace SolidLean.Solid

open FFL FirstOrder

namespace Render

/-- Relation symbols of the single-sorted rendering of a signature: the
symbols of the signature, one sort predicate per sort, and equality. -/
inductive LRel (Sig : Signature) : ℕ → Type
  | rel (r : Sig.Rel) : LRel Sig (Sig.arity r)
  | sort (n : ℕ) : LRel Sig 1
  | eq : LRel Sig 2

/-- The single-sorted (relational) language of a signature. -/
abbrev lang (Sig : Signature) : Language.{0} := ⟨fun _ => Empty, LRel Sig⟩

instance (Sig : Signature) : (lang Sig).Eq := ⟨LRel.eq⟩

variable {Sig : Signature}

/-- The rendering of a many-sorted formula: variable `i` of `k` becomes the
bound variable `Fin.rev i` (the last variable of a snoc-context is the
innermost bound variable), sorts relativize the quantifiers. -/
def tr : {k : ℕ} → {s : Fin k → ℕ} → Formula Sig k s → Semiformula (lang Sig) Empty k
  | _, _, .rel r v _ => Semiformula.rel (LRel.rel r) (fun i => Semiterm.bvar (Fin.rev (v i)))
  | _, _, .eq i j _ => Semiformula.rel LRel.eq ![Semiterm.bvar (Fin.rev i), Semiterm.bvar (Fin.rev j)]
  | _, _, .false_ => Semiformula.falsum
  | _, _, .imp φ ψ => tr φ 🡒 tr ψ
  | _, _, .ex n φ =>
    Semiformula.exs (Semiformula.and (Semiformula.rel (LRel.sort n) ![Semiterm.bvar 0]) (tr φ))

/-- The rendering of a sentence. -/
abbrev trS (σ : Sentence Sig) : FirstOrder.Sentence (lang Sig) := tr σ

/-- The rendered theory: the equality axioms and the rendered sentences. -/
def trT (T : Set (Sentence Sig)) : Theory (lang Sig) := 𝗘𝗤 (lang Sig) ∪ (trS '' T)

instance (T : Set (Sentence Sig)) : 𝗘𝗤 (lang Sig) ⪯ trT T :=
  Entailment.WeakerThan.ofSubset (Set.subset_union_left)

theorem mem_trT {T : Set (Sentence Sig)} {σ : Sentence Sig} (h : σ ∈ T) : trS σ ∈ trT T :=
  Or.inr ⟨σ, h, rfl⟩

/-! ### The sorted structure of a first-order structure -/

variable (Sig) (D : Type v) [Tarski.Structure (lang Sig) D]

/-- The sorted structure: sort `n` is the extension of the sort predicate,
each symbol its relation on well-sorted tuples. -/
def sorted : Str.{v} Sig where
  U n := {x : D // Tarski.Structure.rel (L := lang Sig) (LRel.sort n) ![x]}
  rel r := {t | (∀ i, (t i).1 = Sig.sortAt r i) ∧
    Tarski.Structure.rel (L := lang Sig) (LRel.rel r) (fun i => (t i).2.val)}
  rel_sorts _ _ ht := ht.1

variable {Sig D}

/-- The value of an element of the sorted structure in the domain. -/
abbrev val (x : Sorted.El (sorted Sig D).U) : D := x.2.val

theorem el_ext {x y : Sorted.El (sorted Sig D).U} (h1 : x.1 = y.1) (h2 : val x = val y) : x = y := by
  obtain ⟨n, x⟩ := x
  obtain ⟨m, y⟩ := y
  cases h1
  exact congrArg _ (Subtype.ext h2)

/-- The environment of a sorted tuple, in the reversed order of the rendering. -/
abbrev env {k : ℕ} (t : Fin k → Sorted.El (sorted Sig D).U) : Fin k → D := fun i => val (t (Fin.rev i))

theorem env_snoc {k : ℕ} (t : Fin k → Sorted.El (sorted Sig D).U) (x : Sorted.El (sorted Sig D).U) :
    env (Fin.snoc (α := fun _ => Sorted.El (sorted Sig D).U) t x) = (val x :> env t) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [env, Fin.rev_zero]
  · simp [env, Fin.rev_succ]

theorem sort_of_env {n : ℕ} (x : Sorted.El (sorted Sig D).U) (hx : x.1 = n) :
    Tarski.Structure.rel (L := lang Sig) (LRel.sort n) ![val x] := by
  obtain ⟨m, x⟩ := x
  cases hx
  exact x.2

/-- **Satisfaction is preserved by the rendering**, on well-sorted tuples. -/
theorem tr_sat [Tarski.Structure.Eq (lang Sig) D] :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s) (t : Fin k → Sorted.El (sorted Sig D).U),
      (∀ i, (t i).1 = s i) →
      (φ.Sat (sorted Sig D) t ↔ Semiformula.Eval (env t) Empty.elim (tr φ))
  | _, _, .rel r v hv, t, ht => by
    show ((∀ i, (t (v i)).1 = Sig.sortAt r i) ∧
        Tarski.Structure.rel (L := lang Sig) (LRel.rel r) (fun i => val (t (v i)))) ↔
      Semiformula.Eval (env t) Empty.elim
        (Semiformula.rel (L := lang Sig) (LRel.rel r) (fun i => Semiterm.bvar (Fin.rev (v i))))
    rw [Semiformula.eval_rel]
    have e : (Semiterm.val (L := lang Sig) (env t) Empty.elim ∘ fun i => Semiterm.bvar (Fin.rev (v i))) =
        fun i => val (t (v i)) := by
      funext i; simp [env]
    rw [e]
    exact ⟨fun h => h.2, fun h => ⟨fun i => (ht _).trans (hv i), h⟩⟩
  | _, _, .eq i j h, t, ht => by
    show t i = t j ↔ Semiformula.Eval (env t) Empty.elim
      (Semiformula.rel (L := lang Sig) LRel.eq ![Semiterm.bvar (Fin.rev i), Semiterm.bvar (Fin.rev j)])
    rw [Semiformula.eval_rel]
    have e : (Semiterm.val (L := lang Sig) (env t) Empty.elim ∘ ![Semiterm.bvar (Fin.rev i), Semiterm.bvar (Fin.rev j)]) =
        ![val (t i), val (t j)] := by
      funext l; match l with | 0 => simp [env] | 1 => simp [env]
    rw [e]
    have key : Tarski.Structure.rel (L := lang Sig) LRel.eq ![val (t i), val (t j)] ↔
        val (t i) = val (t j) :=
      Tarski.Structure.eq_lang (L := lang Sig) (M := D) (v := ![val (t i), val (t j)])
    rw [key]
    constructor
    · intro h'; rw [h']
    · intro h'
      exact el_ext ((ht i).trans (h.trans (ht j).symm)) h'
  | _, _, .false_, t, _ => by
    show False ↔ Semiformula.Eval (env t) Empty.elim Semiformula.falsum
    exact Iff.rfl
  | _, _, .imp φ ψ, t, ht => by
    show (_ → _) ↔ Semiformula.Eval (env t) Empty.elim (tr φ 🡒 tr ψ)
    rw [LogicalConnective.HomClass.map_imply, FFL.LogicalConnective.Prop.arrow_eq, tr_sat φ t ht, tr_sat ψ t ht]
  | _, _, .ex n φ, t, ht => by
    show (∃ x : Sorted.El (sorted Sig D).U, x.1 = n ∧ φ.Sat (sorted Sig D) (Fin.snoc t x)) ↔
      Semiformula.Eval (env t) Empty.elim (Semiformula.exs
        (Semiformula.and (Semiformula.rel (L := lang Sig) (LRel.sort n) ![Semiterm.bvar 0]) (tr φ)))
    refine Iff.trans ?_ Semiformula.eval_ex.symm
    constructor
    · rintro ⟨x, hx, hφ⟩
      refine ⟨val x, ?_⟩
      show Semiformula.Eval _ _ (Semiformula.rel (LRel.sort n) ![Semiterm.bvar 0] ⋏ tr φ)
      rw [LogicalConnective.HomClass.map_and, FFL.LogicalConnective.Prop.and_eq, Semiformula.eval_rel]
      refine ⟨?_, ?_⟩
      · have hs := sort_of_env x hx
        rw [← Matrix.constant_eq_singleton] at hs
        simpa [Function.comp_def] using hs
      · rw [← env_snoc]
        exact (tr_sat φ _ (by
          intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simpa using hx
          · simpa using ht i)).1 hφ
    · rintro ⟨d, hd⟩
      change Semiformula.Eval _ _ (Semiformula.rel (LRel.sort n) ![Semiterm.bvar 0] ⋏ tr φ) at hd
      rw [LogicalConnective.HomClass.map_and, FFL.LogicalConnective.Prop.and_eq, Semiformula.eval_rel] at hd
      obtain ⟨hs, hφ⟩ := hd
      have hs' : Tarski.Structure.rel (L := lang Sig) (LRel.sort n) ![d] := by
        rw [← Matrix.constant_eq_singleton]
        simpa [Function.comp_def] using hs
      refine ⟨⟨n, ⟨d, hs'⟩⟩, rfl, ?_⟩
      refine (tr_sat φ _ (by
          intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp
          · simpa using ht i)).2 ?_
      rw [env_snoc]
      exact hφ

theorem holds_iff [Tarski.Structure.Eq (lang Sig) D] (σ : Sentence Sig) :
    Sentence.Holds σ (sorted Sig D) ↔ Semiformula.Realize (L := lang Sig) D (trS σ) := by
  have e : env (Fin.elim0 : Fin 0 → Sorted.El (sorted Sig D).U) = ![] := funext fun i => i.elim0
  have := tr_sat (D := D) σ Fin.elim0 (fun i => i.elim0)
  rw [e] at this
  exact this

/-- A first-order structure of the rendered theory, with real equality, gives
a sorted model of the sentences. -/
theorem models_of_models [Nonempty D] [Tarski.Structure.Eq (lang Sig) D] (T : Set (Sentence Sig))
    (h : D↓[lang Sig] ⊧* trT T) : (sorted Sig D).Models T := by
  intro σ hσ
  rw [holds_iff]
  exact models_iff.mp (h.models_set (mem_trT hσ))

/-! ### The first-order structure of a sorted structure -/

/-- The interpretation of the rendered relation symbols on the union of the
sorts of a sorted structure. -/
def interpRel (N : Str.{v} Sig) : {k : ℕ} → LRel Sig k → (Fin k → Sorted.El N.U) → Prop
  | _, .rel r => fun v => v ∈ N.rel r
  | _, .sort n => fun v => (v 0).1 = n
  | _, .eq => fun v => v 0 = v 1

/-- The single-sorted structure of a sorted structure: its domain is the
union of the sorts. -/
@[instance_reducible] def unsorted (N : Str.{v} Sig) : Tarski.Structure (lang Sig) (Sorted.El N.U) where
  func _ f := f.elim
  rel _ r := interpRel N r

set_option linter.style.haveILetI false in
theorem unsorted_eq (N : Str.{v} Sig) :
    @Tarski.Structure.Eq (lang Sig) (Sorted.El N.U) (unsorted N) inferInstance := by
  letI := unsorted N
  refine ⟨fun a b => ?_⟩
  show Semiformula.Eval (s := unsorted N) ![a, b] Empty.elim
    (Semiformula.rel (L := lang Sig) LRel.eq Semiterm.bvar) ↔ a = b
  rw [Semiformula.eval_rel]
  exact Iff.rfl

/-- The environment of a tuple, in the reversed order of the rendering. -/
abbrev env' {N : Str.{v} Sig} {k : ℕ} (t : Fin k → Sorted.El N.U) : Fin k → Sorted.El N.U :=
  fun i => t (Fin.rev i)

theorem env'_snoc {N : Str.{v} Sig} {k : ℕ} (t : Fin k → Sorted.El N.U) (x : Sorted.El N.U) :
    env' (Fin.snoc (α := fun _ => Sorted.El N.U) t x) = (x :> env' t) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [env', Fin.rev_zero]
  · simp [env', Fin.rev_succ]

/-- **Satisfaction is preserved by the rendering**, read in the single-sorted
structure of a sorted structure. -/
theorem tr_sat' (N : Str.{v} Sig) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s) (t : Fin k → Sorted.El N.U),
      (∀ i, (t i).1 = s i) →
      (φ.Sat N t ↔ Semiformula.Eval (s := unsorted N) (env' t) Empty.elim (tr φ))
  | _, _, .rel r v hv, t, ht => by
    show (fun i => t (v i)) ∈ N.rel r ↔
      Semiformula.Eval (s := unsorted N) (env' t) Empty.elim
        (Semiformula.rel (L := lang Sig) (LRel.rel r) (fun i => Semiterm.bvar (Fin.rev (v i))))
    rw [Semiformula.eval_rel]
    have e : (Semiterm.val (L := lang Sig) (s := unsorted N) (env' t) Empty.elim ∘
        fun i => Semiterm.bvar (Fin.rev (v i))) = fun i => t (v i) := by
      funext i; simp [env']
    rw [e]
    exact Iff.rfl
  | _, _, .eq i j h, t, ht => by
    show t i = t j ↔ Semiformula.Eval (s := unsorted N) (env' t) Empty.elim
      (Semiformula.rel (L := lang Sig) LRel.eq ![Semiterm.bvar (Fin.rev i), Semiterm.bvar (Fin.rev j)])
    rw [Semiformula.eval_rel]
    have e : (Semiterm.val (L := lang Sig) (s := unsorted N) (env' t) Empty.elim ∘
        ![Semiterm.bvar (Fin.rev i), Semiterm.bvar (Fin.rev j)]) = ![t i, t j] := by
      funext l; match l with | 0 => simp [env'] | 1 => simp [env']
    rw [e]
    exact Iff.rfl
  | _, _, .false_, t, _ => by
    show False ↔ Semiformula.Eval (s := unsorted N) (env' t) Empty.elim Semiformula.falsum
    exact Iff.rfl
  | _, _, .imp φ ψ, t, ht => by
    show (_ → _) ↔ Semiformula.Eval (s := unsorted N) (env' t) Empty.elim (tr φ 🡒 tr ψ)
    rw [LogicalConnective.HomClass.map_imply, FFL.LogicalConnective.Prop.arrow_eq,
      tr_sat' N φ t ht, tr_sat' N ψ t ht]
  | _, _, .ex n φ, t, ht => by
    show (∃ x : Sorted.El N.U, x.1 = n ∧ φ.Sat N (Fin.snoc t x)) ↔
      Semiformula.Eval (s := unsorted N) (env' t) Empty.elim (Semiformula.exs
        (Semiformula.and (Semiformula.rel (L := lang Sig) (LRel.sort n) ![Semiterm.bvar 0]) (tr φ)))
    refine Iff.trans ?_ Semiformula.eval_ex.symm
    constructor
    · rintro ⟨x, hx, hφ⟩
      refine ⟨x, ?_⟩
      show Semiformula.Eval (s := unsorted N) _ _
        (Semiformula.rel (L := lang Sig) (LRel.sort n) ![Semiterm.bvar 0] ⋏ tr φ)
      rw [LogicalConnective.HomClass.map_and, FFL.LogicalConnective.Prop.and_eq, Semiformula.eval_rel]
      refine ⟨hx, ?_⟩
      rw [← env'_snoc]
      exact (tr_sat' N φ _ (by
        intro i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hx
        · simpa using ht i)).1 hφ
    · rintro ⟨x, hx⟩
      change Semiformula.Eval (s := unsorted N) _ _
        (Semiformula.rel (L := lang Sig) (LRel.sort n) ![Semiterm.bvar 0] ⋏ tr φ) at hx
      rw [LogicalConnective.HomClass.map_and, FFL.LogicalConnective.Prop.and_eq,
        Semiformula.eval_rel] at hx
      obtain ⟨hs, hφ⟩ := hx
      have hs' : x.1 = n := hs
      refine ⟨x, hs', ?_⟩
      refine (tr_sat' N φ _ (by
          intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simpa using hs'
          · simpa using ht i)).2 ?_
      rw [env'_snoc]
      exact hφ

theorem holds_iff_unsorted (N : Str.{v} Sig) (σ : Sentence Sig) :
    Sentence.Holds σ N ↔ Semiformula.Realize (s := unsorted N) (Sorted.El N.U) (trS σ) := by
  have e : env' (Fin.elim0 : Fin 0 → Sorted.El N.U) = ![] := funext fun i => i.elim0
  have := tr_sat' N σ Fin.elim0 (fun i => i.elim0)
  rw [e] at this
  exact this

set_option linter.style.haveILetI false in
/-- The single-sorted structure of a sorted model of `T` is a model of the
rendered theory. -/
theorem unsorted_models (N : Str.{v} Sig) [Nonempty (Sorted.El N.U)] (T : Set (Sentence Sig))
    (h : N.Models T) : (@Language.str (Sorted.El N.U) _ (lang Sig) (unsorted N)) ⊧* trT T := by
  letI := unsorted N
  haveI := unsorted_eq N
  refine ⟨fun φ hφ => ?_⟩
  rcases hφ with hφ | ⟨σ, hσ, rfl⟩
  · exact (Tarski.Structure.Eq.models_eq (lang Sig) (Sorted.El N.U)).models_set hφ
  · exact models_iff.2 ((holds_iff_unsorted N σ).1 (h σ hσ))

/-! ### Provability by completeness -/

/-- **Provability from semantic truth.**  A sentence true in every semantic
model of `T(𝔉)` (every structure that is a general model of the clause family
with its definable classes) is derivable in Foundation's sequent calculus from
the rendered axioms `T(𝔉)`. -/
theorem provable_of_semantic {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    (σ : Sentence (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig)
    (h : ∀ (M : Str.{v} (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig),
      (ClauseFamily.ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩ → Sentence.Holds σ M) :
    trT (ClauseFamily.TLax.{v} Sym arity sortAt φ) ⊢ trS σ := by
  apply Theory.Proof.complete_on_eq_models.{0, v}
  intro D _ _ _ hD
  rw [models_iff, ← holds_iff]
  exact h _ (ClauseFamily.isGenModel_of_models (models_of_models _ hD))

set_option linter.style.haveILetI false in
/-- **Semantic truth from provability** (soundness): a sentence derivable
from the rendered axioms of `T(𝔉)` holds in every semantic model of
`T(𝔉)`. -/
theorem semantic_of_provable {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    (σ : Sentence (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig)
    (h : trT (ClauseFamily.TLax.{v} Sym arity sortAt φ) ⊢ trS σ)
    (M : Str.{v} (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig)
    (hM : (ClauseFamily.ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩) :
    Sentence.Holds σ M := by
  obtain ⟨e, -⟩ := (hM.tower.zfc 0).empty
  haveI : Nonempty (Sorted.El M.U) := ⟨Sorted.inj M.U e⟩
  letI := unsorted M
  have hmod := unsorted_models M _ (ClauseFamily.models_of_isGenModel hM)
  have hσ := models_of_provable hmod h
  rw [models_iff] at hσ
  exact (holds_iff_unsorted M σ).2 hσ

/-- **Derivability is truth in all semantic models**: for a clause family
given by formulas, a sentence is derivable in `LK` from the rendered axioms
of `T(𝔉)` iff it holds in every structure that is a model of `T(𝔉)` with its
definable classes. -/
theorem provable_iff_semantic {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    (σ : Sentence (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig) :
    trT (ClauseFamily.TLax.{v} Sym arity sortAt φ) ⊢ trS σ ↔
      ∀ (M : Str.{v} (ClauseFamily.ofFormulas.{v} Sym arity sortAt φ).sig),
        (ClauseFamily.ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩ → Sentence.Holds σ M :=
  ⟨semantic_of_provable σ, provable_of_semantic σ⟩

end Render

end SolidLean.Solid
