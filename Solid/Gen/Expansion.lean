module

public import Solid.Gen.GenInterp
public import Solid.Gen.Transport
public import Solid.Solidity

/-!
# Expansions of the tower theory by clause-defined symbols

The theory `T(𝔉)` of a *clause family* `𝔉` has the tower signature (one
membership, one transition graph and one boundary predicate per sort) plus one
relation symbol per member of `𝔉`; its models are the models of `H` (for the
class system of the whole structure) in which each extra symbol denotes its
*clause*, a relation on the underlying tower fixed uniformly for all towers
and invariant under tower isomorphisms.  Such an expansion is bi-interpretable
with `H` in the most direct way (reduct/expansion), and this file proves that
it is solid whenever `H` is (`ClauseFamily.solid`).  The idealized annotated Lean
is presented as such an expansion in `Solid.Calc.Theory`.

This file also constructs the canonical expansion of any model of `H`
(`ClauseFamily.expand`), so that `T(𝔉)` is consistent relative to `H`.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-- The symbols of the tower signature as relation symbols. -/
inductive TowerSym
  | memZ (n : ℕ)
  | liftZ (n : ℕ)
  | bnd (n : ℕ)

/-- Arities of the tower symbols. -/
abbrev TowerSym.arity : TowerSym → ℕ
  | .memZ _ => 2
  | .liftZ _ => 2
  | .bnd _ => 1

/-- Argument sorts of the tower symbols. -/
abbrev TowerSym.sortAt : (r : TowerSym) → Fin r.arity → ℕ
  | .memZ n, _ => n
  | .liftZ n, i => if i.1 = 0 then n else n + 1
  | .bnd n, _ => n + 1

/-- A clause family: extra symbols, each interpreted in every tower by a
relation ("clause") of the declared sorts, definable in every class system and
invariant under tower isomorphisms. -/
structure ClauseFamily where
  Sym : Type
  arity : Sym → ℕ
  sortAt : (f : Sym) → Fin (arity f) → ℕ
  G : (f : Sym) → (T : MemTower.{u}) → T.Rel (arity f)
  G_sorts : ∀ f (T : MemTower.{u}) t, t ∈ G f T → ∀ i, (t i).1 = sortAt f i
  G_def : ∀ f (T : TowerWithClasses.{u}), G f T.T ∈ T.𝒟.D (arity f)
  G_iso : ∀ f {T T' : MemTower.{u}} (e : TowerIso T T') (t : Fin (arity f) → T.El),
    t ∈ G f T ↔ (fun i => e.mapEl (t i)) ∈ G f T'

namespace ClauseFamily

variable (F : ClauseFamily.{u})

/-- The signature of `T(𝔉)`.  An `abbrev`, so that the arities of the tower
symbols unfold to numerals during unification. -/
abbrev sig : Signature where
  Rel := TowerSym ⊕ F.Sym
  arity := fun r => match r with
    | .inl s => s.arity
    | .inr f => F.arity f
  sortAt := fun r => match r with
    | .inl s => s.sortAt
    | .inr f => F.sortAt f

end ClauseFamily

/-! ### Tuples of length one and two -/

theorem vec_eq_two {α : Type*} (t : Fin 2 → α) : t = ![t 0, t 1] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem vec_eq_one {α : Type*} (t : Fin 1 → α) : t = ![t 0] := by
  funext i
  match i with
  | 0 => rfl

theorem map_vec_two {α β : Type*} (g : α → β) (a b : α) :
    (fun i => g (![a, b] i)) = ![g a, g b] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem map_vec_one {α β : Type*} (g : α → β) (a : α) :
    (fun i => g (![a] i)) = ![g a] := by
  funext i
  match i with
  | 0 => rfl

namespace ClauseFamily

variable {F : ClauseFamily.{u}}

/-- Well-formedness of the tower symbols: the transition relations are graphs
of total functions and the boundary predicates are singletons. -/
structure IsWF (M : Str.{u} F.sig) : Prop where
  liftZ_total : ∀ n (x : M.U n), ∃ y : M.U (n + 1),
    ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.liftZ n))
  liftZ_unique : ∀ n (x : M.U n) (y y' : M.U (n + 1)),
    ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.liftZ n)) →
    ![Sorted.inj M.U x, Sorted.inj M.U y'] ∈ M.rel (.inl (.liftZ n)) → y = y'
  bnd_exists : ∀ n, ∃ y : M.U (n + 1), ![Sorted.inj M.U y] ∈ M.rel (.inl (.bnd n))
  bnd_unique : ∀ n (y y' : M.U (n + 1)), ![Sorted.inj M.U y] ∈ M.rel (.inl (.bnd n)) →
    ![Sorted.inj M.U y'] ∈ M.rel (.inl (.bnd n)) → y = y'

/-- The underlying tower of a well-formed structure. -/
noncomputable def Δ (M : Str.{u} F.sig) (h : IsWF M) : MemTower.{u} where
  U := M.U
  mem := fun {n} x y => ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.memZ n))
  j := fun n x => Classical.choose (h.liftZ_total n x)
  κ := fun n => Classical.choose (h.bnd_exists n)

namespace Δ

variable {M : Str.{u} F.sig} (h : IsWF M)

@[simp] theorem U_eq : (Δ M h).U = M.U := rfl

theorem mem_iff {n : ℕ} (x y : M.U n) :
    (Δ M h).mem x y ↔ ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.memZ n)) := Iff.rfl

theorem j_spec (n : ℕ) (x : M.U n) :
    ![Sorted.inj M.U x, Sorted.inj M.U ((Δ M h).j n x)] ∈ M.rel (.inl (.liftZ n)) :=
  Classical.choose_spec (h.liftZ_total n x)

theorem j_iff (n : ℕ) (x : M.U n) (y : M.U (n + 1)) :
    ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.liftZ n)) ↔ y = (Δ M h).j n x :=
  ⟨fun hy => h.liftZ_unique n x _ _ hy (j_spec h n x), fun hy => hy ▸ j_spec h n x⟩

theorem κ_spec (n : ℕ) : ![Sorted.inj M.U ((Δ M h).κ n)] ∈ M.rel (.inl (.bnd n)) :=
  Classical.choose_spec (h.bnd_exists n)

theorem κ_iff (n : ℕ) (y : M.U (n + 1)) :
    ![Sorted.inj M.U y] ∈ M.rel (.inl (.bnd n)) ↔ y = (Δ M h).κ n :=
  ⟨fun hy => h.bnd_unique n y _ hy (κ_spec h n), fun hy => hy ▸ κ_spec h n⟩

/-- Tuples in the membership relation of sort `n`. -/
theorem mem_memZ_iff (n : ℕ) (t : Fin 2 → Sorted.El M.U) :
    t ∈ M.rel (.inl (.memZ n)) ↔ ∃ x y : M.U n, t = ![Sorted.inj M.U x, Sorted.inj M.U y] ∧
      ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.memZ n)) := by
  constructor
  · intro ht
    have hs := M.rel_sorts (.inl (.memZ n)) t ht
    have h0 : (t 0).1 = n := hs (0 : Fin 2)
    have h1 : (t 1).1 = n := hs (1 : Fin 2)
    have e : t = ![Sorted.inj M.U (Sorted.toSort M.U (t 0) h0),
        Sorted.inj M.U (Sorted.toSort M.U (t 1) h1)] := by
      rw [Sorted.inj_toSort, Sorted.inj_toSort]; exact vec_eq_two t
    exact ⟨_, _, e, e ▸ ht⟩
  · rintro ⟨x, y, rfl, h⟩; exact h

/-- Tuples in the transition relation of sort `n`. -/
theorem mem_liftZ_iff (n : ℕ) (t : Fin 2 → Sorted.El M.U) :
    t ∈ M.rel (.inl (.liftZ n)) ↔ ∃ (x : M.U n) (y : M.U (n + 1)),
      t = ![Sorted.inj M.U x, Sorted.inj M.U y] ∧
      ![Sorted.inj M.U x, Sorted.inj M.U y] ∈ M.rel (.inl (.liftZ n)) := by
  constructor
  · intro ht
    have hs := M.rel_sorts (.inl (.liftZ n)) t ht
    have h0 : (t 0).1 = n := hs (0 : Fin 2)
    have h1 : (t 1).1 = n + 1 := hs (1 : Fin 2)
    have e : t = ![Sorted.inj M.U (Sorted.toSort M.U (t 0) h0),
        Sorted.inj M.U (Sorted.toSort M.U (t 1) h1)] := by
      rw [Sorted.inj_toSort, Sorted.inj_toSort]; exact vec_eq_two t
    exact ⟨_, _, e, e ▸ ht⟩
  · rintro ⟨x, y, rfl, h⟩; exact h

/-- Tuples in the boundary predicate of sort `n`. -/
theorem mem_bnd_iff (n : ℕ) (t : Fin 1 → Sorted.El M.U) :
    t ∈ M.rel (.inl (.bnd n)) ↔ ∃ y : M.U (n + 1),
      t = ![Sorted.inj M.U y] ∧ ![Sorted.inj M.U y] ∈ M.rel (.inl (.bnd n)) := by
  constructor
  · intro ht
    have hs := M.rel_sorts (.inl (.bnd n)) t ht
    have h0 : (t 0).1 = n + 1 := hs (0 : Fin 1)
    have e : t = ![Sorted.inj M.U (Sorted.toSort M.U (t 0) h0)] := by
      rw [Sorted.inj_toSort]; exact vec_eq_one t
    exact ⟨_, e, e ▸ ht⟩
  · rintro ⟨y, rfl, h⟩; exact h

/-- The membership atom of `Δ M` is the membership symbol. -/
theorem memRel_eq (n : ℕ) : (Δ M h).memRel n = M.rel (.inl (.memZ n)) := by
  ext t
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    rw [vec_eq_two t, hx, hy]
    exact hxy
  · intro ht
    obtain ⟨x, y, rfl, hxy⟩ := (mem_memZ_iff n t).1 ht
    exact ⟨x, y, rfl, rfl, hxy⟩

/-- The transition atom of `Δ M` is the transition symbol. -/
theorem jRel_eq (n : ℕ) : (Δ M h).jRel n = M.rel (.inl (.liftZ n)) := by
  ext t
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [vec_eq_two t, hx, hy]
    exact j_spec h n x
  · intro ht
    obtain ⟨x, y, rfl, hxy⟩ := (mem_liftZ_iff n t).1 ht
    rw [(j_iff h n x y).1 hxy]
    exact ⟨x, rfl, rfl⟩

/-- The boundary atom of `Δ M` is the boundary symbol. -/
theorem kappaRel_eq (n : ℕ) : (Δ M h).kappaRel n = M.rel (.inl (.bnd n)) := by
  ext t
  constructor
  · intro hx
    have hx' : t 0 = Sorted.inj M.U ((Δ M h).κ n) := hx
    rw [vec_eq_one t, hx']
    exact κ_spec h n
  · intro ht
    obtain ⟨y, rfl, hy⟩ := (mem_bnd_iff n t).1 ht
    show Sorted.inj M.U y = Sorted.inj M.U ((Δ M h).κ n)
    rw [(κ_iff h n y).1 hy]

end Δ

/-- The class system of a structure, read on its underlying tower. -/
noncomputable def ΔSys (M : StrWithSys.{u} F.sig) (h : IsWF M.M) : ClassSystem (Δ M.M h) where
  toClassSys := M.𝒟.toClassSys
  memRel_mem n := by rw [Δ.memRel_eq]; exact M.𝒟.rel_mem (.inl (.memZ n))
  j_mem n := by rw [Δ.jRel_eq]; exact M.𝒟.rel_mem (.inl (.liftZ n))
  kappa_mem n := by rw [Δ.kappaRel_eq]; exact M.𝒟.rel_mem (.inl (.bnd n))

/-- The axioms of `T(𝔉)`: well-formedness of the tower symbols, the axioms of
`H` for the underlying tower with the structure's class system, and one
defining axiom per extra symbol. -/
structure IsGenModel (M : StrWithSys.{u} F.sig) : Prop where
  wf : IsWF M.M
  tower : IsTowerModel ⟨Δ M.M wf, ΔSys M wf⟩
  clause : ∀ f, M.M.rel (.inr f) = F.G f (Δ M.M wf)

end ClauseFamily

/-! ### Extensionality of class systems -/

theorem ClassSys.ext {U : ℕ → Type u} {𝒟 𝒟' : ClassSys U} (h : ∀ k, 𝒟.D k = 𝒟'.D k) :
    𝒟 = 𝒟' := by
  have hD : 𝒟.D = 𝒟'.D := funext h
  cases 𝒟; cases 𝒟'
  cases hD
  rfl

theorem ClassSystem.ext {T : MemTower.{u}} {𝒟 𝒟' : ClassSystem T}
    (h : ∀ k, 𝒟.D k = 𝒟'.D k) : 𝒟 = 𝒟' := by
  have hD : 𝒟.toClassSys = 𝒟'.toClassSys := ClassSys.ext h
  cases 𝒟; cases 𝒟'
  cases hD
  rfl

theorem IsTowerModel.congr_sys {T : MemTower.{u}} {𝒟 𝒟' : ClassSystem T} (h : 𝒟 = 𝒟')
    (hT : IsTowerModel ⟨T, 𝒟⟩) : IsTowerModel ⟨T, 𝒟'⟩ := by
  subst h; exact hT

/-! ### The tower reduct of an interpretation -/

namespace GenInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} {F : ClauseFamily.{u}} (I : GenInterp U 𝒟 F.sig)

/-- Membership in the interpreted relation for a tuple of classes, given a
tuple of representatives. -/
theorem mem_relQ_iff_of_rep (r : F.sig.Rel) (q : Fin (F.sig.arity r) → Sorted.El I.Carrier)
    (u : Fin (F.sig.arity r) → Sorted.El U)
    (h : ∀ i, (q i).1 = F.sig.sortAt r i ∧ I.Rep (u i) (q i)) :
    q ∈ I.relQ r ↔ u ∈ I.relC r := by
  constructor
  · rintro ⟨u', hu', hrel⟩
    refine I.relC_congr r u' u (fun i => ?_) hrel
    obtain ⟨y, y', hy, hy', heqv⟩ := I.Rep_eqv (h i).1 (hu' i).2 (h i).2
    exact ⟨y, y', hy, hy', heqv⟩
  · intro hrel
    exact ⟨u, h, hrel⟩

theorem Rep_cls {n : ℕ} (x : I.Dom n) :
    I.Rep (Sorted.inj U x.1) (Sorted.inj I.Carrier (n := n) (I.cls x)) :=
  ⟨n, x, rfl, rfl⟩

/-- A component of a tuple in `relC r` lies in the corresponding domain. -/
theorem mem_dom_of_relC {r : F.sig.Rel} {t : Fin (F.sig.arity r) → Sorted.El U}
    (ht : t ∈ I.relC r) (i : Fin (F.sig.arity r)) {x : U (I.a (F.sig.sortAt r i))}
    (hx : t i = Sorted.inj U x) : x ∈ I.dom (F.sig.sortAt r i) := by
  obtain ⟨x', hx', hdom⟩ := I.relC_dom r t ht i
  rw [hx] at hx'
  rw [Sorted.inj_injective U hx']; exact hdom

/-- The tower reduct of an interpretation of `T(𝔉)` whose model is well
formed. -/
noncomputable def toTower (hN : ClauseFamily.IsWF I.model) : SInterp U 𝒟 where
  toSortInterp := I.toSortInterp
  memC n x y := ![Sorted.inj U x, Sorted.inj U y] ∈ I.relC (.inl (.memZ n))
  memC_congr n x x' y y' hx hy := by
    constructor
    · exact I.relC_congr _ _ _ (Fin.forall_fin_two.2 ⟨⟨x, x', rfl, rfl, hx⟩, ⟨y, y', rfl, rfl, hy⟩⟩)
    · exact I.relC_congr _ _ _ (Fin.forall_fin_two.2
        ⟨⟨x', x, rfl, rfl, I.eqv_symm _ _ _ hx⟩, ⟨y', y, rfl, rfl, I.eqv_symm _ _ _ hy⟩⟩)
  jC n x y := ![Sorted.inj U x, Sorted.inj U y] ∈ I.relC (.inl (.liftZ n))
  jC_total n x hx := by
    obtain ⟨q, hq⟩ := hN.liftZ_total n (I.cls ⟨x, hx⟩)
    induction q using Quotient.ind with
    | _ y =>
    refine ⟨y.1, y.2, ?_⟩
    exact (I.mem_relQ_iff_of_rep (.inl (.liftZ n))
      ![Sorted.inj I.Carrier (n := n) (I.cls ⟨x, hx⟩), Sorted.inj I.Carrier (n := n + 1) (I.cls y)]
      ![Sorted.inj U x, Sorted.inj U y.1]
      (Fin.forall_fin_two.2 ⟨⟨rfl, I.Rep_cls ⟨x, hx⟩⟩, ⟨rfl, I.Rep_cls y⟩⟩)).1 hq
  jC_func n x y y' hy hy' hxy hxy' := by
    have hx : x ∈ I.dom n := I.mem_dom_of_relC hxy (0 : Fin 2) rfl
    have h1 := (I.mem_relQ_iff_of_rep (.inl (.liftZ n))
      ![Sorted.inj I.Carrier (n := n) (I.cls ⟨x, hx⟩), Sorted.inj I.Carrier (n := n + 1) (I.cls ⟨y, hy⟩)]
      ![Sorted.inj U x, Sorted.inj U y]
      (Fin.forall_fin_two.2 ⟨⟨rfl, I.Rep_cls ⟨x, hx⟩⟩, ⟨rfl, I.Rep_cls ⟨y, hy⟩⟩⟩)).2 hxy
    have h2 := (I.mem_relQ_iff_of_rep (.inl (.liftZ n))
      ![Sorted.inj I.Carrier (n := n) (I.cls ⟨x, hx⟩), Sorted.inj I.Carrier (n := n + 1) (I.cls ⟨y', hy'⟩)]
      ![Sorted.inj U x, Sorted.inj U y']
      (Fin.forall_fin_two.2 ⟨⟨rfl, I.Rep_cls ⟨x, hx⟩⟩, ⟨rfl, I.Rep_cls ⟨y', hy'⟩⟩⟩)).2 hxy'
    exact (I.cls_eq_iff _ _).1 (hN.liftZ_unique n _ _ _ h1 h2)
  jC_congr n x x' y hxx' hxy :=
    I.relC_congr _ _ _ (Fin.forall_fin_two.2 ⟨⟨x, x', rfl, rfl, hxx'⟩,
      ⟨y, y, rfl, rfl, I.eqv_refl _ _ (I.mem_dom_of_relC hxy (1 : Fin 2) rfl)⟩⟩) hxy
  jC_congr_right n x y y' hyy' hxy :=
    I.relC_congr _ _ _ (Fin.forall_fin_two.2
      ⟨⟨x, x, rfl, rfl, I.eqv_refl _ _ (I.mem_dom_of_relC hxy (0 : Fin 2) rfl)⟩,
       ⟨y, y', rfl, rfl, hyy'⟩⟩) hxy
  kappaC n y := ![Sorted.inj U y] ∈ I.relC (.inl (.bnd n))
  kappaC_exists n := by
    obtain ⟨q, hq⟩ := hN.bnd_exists n
    induction q using Quotient.ind with
    | _ y =>
    refine ⟨y.1, y.2, ?_⟩
    exact (I.mem_relQ_iff_of_rep (.inl (.bnd n))
      ![Sorted.inj I.Carrier (n := n + 1) (I.cls y)] ![Sorted.inj U y.1]
      (Fin.forall_fin_one.2 ⟨rfl, I.Rep_cls y⟩)).1 hq
  kappaC_unique n y y' hy hy' hk hk' := by
    have h1 := (I.mem_relQ_iff_of_rep (.inl (.bnd n))
      ![Sorted.inj I.Carrier (n := n + 1) (I.cls ⟨y, hy⟩)] ![Sorted.inj U y]
      (Fin.forall_fin_one.2 ⟨rfl, I.Rep_cls ⟨y, hy⟩⟩)).2 hk
    have h2 := (I.mem_relQ_iff_of_rep (.inl (.bnd n))
      ![Sorted.inj I.Carrier (n := n + 1) (I.cls ⟨y', hy'⟩)] ![Sorted.inj U y']
      (Fin.forall_fin_one.2 ⟨rfl, I.Rep_cls ⟨y', hy'⟩⟩)).2 hk'
    exact (I.cls_eq_iff _ _).1 (hN.bnd_unique n _ _ h1 h2)
  kappaC_congr n y y' hyy' hk :=
    I.relC_congr _ _ _ (Fin.forall_fin_one.2 ⟨y, y', rfl, rfl, hyy'⟩) hk
  memC_def n := by
    show Sorted.liftRel U _ ∈ 𝒟.D 2
    have : Sorted.liftRel U {s : Fin 2 → U (I.a n) |
        ![Sorted.inj U (s 0), Sorted.inj U (s 1)] ∈ I.relC (.inl (.memZ n))} =
        I.relC (.inl (.memZ n)) := by
      ext t
      constructor
      · rintro ⟨s, hs, hC⟩
        have e : t = ![Sorted.inj U (s 0), Sorted.inj U (s 1)] := by
          funext i
          match i with
          | 0 => exact hs 0
          | 1 => exact hs 1
        rw [e]; exact hC
      · intro ht
        obtain ⟨x0, hx0, -⟩ := I.relC_dom (.inl (.memZ n)) t ht (0 : Fin 2)
        obtain ⟨x1, hx1, -⟩ := I.relC_dom (.inl (.memZ n)) t ht (1 : Fin 2)
        have e : t = ![Sorted.inj U x0, Sorted.inj U x1] := by
          funext i
          match i with
          | 0 => exact hx0
          | 1 => exact hx1
        refine ⟨![x0, x1], Fin.forall_fin_two.2 ⟨hx0, hx1⟩, ?_⟩
        show ![Sorted.inj U x0, Sorted.inj U x1] ∈ I.relC (.inl (.memZ n))
        subst e; exact ht
    rw [this]; exact I.relC_def (.inl (.memZ n))
  jC_def n := by
    show ({t | ∃ (x : U (I.a n)) (y : U (I.a (n + 1))), t 0 = Sorted.inj U x ∧ t 1 = Sorted.inj U y ∧
        ![Sorted.inj U x, Sorted.inj U y] ∈ I.relC (.inl (.liftZ n))} : Sorted.Rel U 2) ∈ 𝒟.D 2
    have : ({t | ∃ (x : U (I.a n)) (y : U (I.a (n + 1))), t 0 = Sorted.inj U x ∧ t 1 = Sorted.inj U y ∧
        ![Sorted.inj U x, Sorted.inj U y] ∈ I.relC (.inl (.liftZ n))} : Sorted.Rel U 2) =
        I.relC (.inl (.liftZ n)) := by
      ext t
      constructor
      · rintro ⟨x, y, hx, hy, hC⟩
        rw [vec_eq_two t, hx, hy]; exact hC
      · intro ht
        obtain ⟨x0, hx0, -⟩ := I.relC_dom (.inl (.liftZ n)) t ht (0 : Fin 2)
        obtain ⟨x1, hx1, -⟩ := I.relC_dom (.inl (.liftZ n)) t ht (1 : Fin 2)
        refine ⟨x0, x1, hx0, hx1, ?_⟩
        have e : t = ![Sorted.inj U x0, Sorted.inj U x1] := by
          funext i
          match i with
          | 0 => exact hx0
          | 1 => exact hx1
        subst e; exact ht
    rw [this]; exact I.relC_def (.inl (.liftZ n))
  kappaC_def n := by
    show Sorted.SortClass U _ _ ∈ 𝒟.D 1
    have : Sorted.SortClass U (I.a (n + 1)) {y | ![Sorted.inj U y] ∈ I.relC (.inl (.bnd n))} =
        I.relC (.inl (.bnd n)) := by
      ext t
      constructor
      · rintro ⟨x, hx, hC⟩
        rw [vec_eq_one t, hx]; exact hC
      · intro ht
        obtain ⟨x0, hx0, -⟩ := I.relC_dom (.inl (.bnd n)) t ht (0 : Fin 1)
        refine ⟨x0, hx0, ?_⟩
        have e : t = ![Sorted.inj U x0] := by
          funext i
          match i with
          | 0 => exact hx0
        show ![Sorted.inj U x0] ∈ I.relC (.inl (.bnd n))
        subst e; exact ht
    rw [this]; exact I.relC_def (.inl (.bnd n))

/-! #### The reduct's model is the underlying tower of the model -/

variable (hN : ClauseFamily.IsWF I.model)

theorem toTower_mem_iff {n : ℕ} (q q' : I.Carrier n) :
    (I.toTower hN).model.mem q q' ↔
      ![Sorted.inj I.Carrier (n := n) q, Sorted.inj I.Carrier (n := n) q'] ∈
        I.model.rel (.inl (.memZ n)) := by
  induction q using Quotient.ind with
  | _ x =>
  induction q' using Quotient.ind with
  | _ y =>
  show (I.toTower hN).memC n x.1 y.1 ↔ _
  exact (I.mem_relQ_iff_of_rep (.inl (.memZ n))
    ![Sorted.inj I.Carrier (n := n) (I.cls x), Sorted.inj I.Carrier (n := n) (I.cls y)]
    ![Sorted.inj U x.1, Sorted.inj U y.1]
    (Fin.forall_fin_two.2 ⟨⟨rfl, I.Rep_cls x⟩, ⟨rfl, I.Rep_cls y⟩⟩)).symm

theorem toTower_j_mem {n : ℕ} (q : I.Carrier n) :
    ![Sorted.inj I.Carrier (n := n) q, Sorted.inj I.Carrier (n := n + 1) ((I.toTower hN).model.j n q)] ∈
      I.model.rel (.inl (.liftZ n)) := by
  induction q using Quotient.ind with
  | _ x =>
  exact (I.mem_relQ_iff_of_rep (.inl (.liftZ n))
    ![Sorted.inj I.Carrier (n := n) (I.cls x),
      Sorted.inj I.Carrier (n := n + 1) (I.cls ((I.toTower hN).jImage x))]
    ![Sorted.inj U x.1, Sorted.inj U ((I.toTower hN).jImage x).1]
    (Fin.forall_fin_two.2 ⟨⟨rfl, I.Rep_cls x⟩, ⟨rfl, I.Rep_cls _⟩⟩)).2 ((I.toTower hN).jImage_spec x)

theorem toTower_κ_mem (n : ℕ) :
    ![Sorted.inj I.Carrier (n := n + 1) ((I.toTower hN).model.κ n)] ∈ I.model.rel (.inl (.bnd n)) :=
  (I.mem_relQ_iff_of_rep (.inl (.bnd n))
    ![Sorted.inj I.Carrier (n := n + 1) (I.cls ((I.toTower hN).kappaRep n))]
    ![Sorted.inj U ((I.toTower hN).kappaRep n).1]
    (Fin.forall_fin_one.2 ⟨rfl, I.Rep_cls _⟩)).2 ((I.toTower hN).kappaRep_spec n)

/-- The identity, as an isomorphism from the underlying tower of the model to
the model of the reduct. -/
noncomputable def ΔIso : TowerIso (ClauseFamily.Δ I.model hN) (I.toTower hN).model where
  toFun _ := id
  bijective _ := Function.bijective_id
  mem_iff n x y := (I.toTower_mem_iff hN x y).trans (ClauseFamily.Δ.mem_iff hN x y).symm
  j_comm n x := hN.liftZ_unique n x _ _ (ClauseFamily.Δ.j_spec hN n x) (I.toTower_j_mem hN x)
  κ_comm n := hN.bnd_unique n _ _ (ClauseFamily.Δ.κ_spec hN n) (I.toTower_κ_mem hN n)

theorem ΔIso_pullRel {k : ℕ} (C : (I.toTower hN).model.Rel k) : (I.ΔIso hN).pullRel C = C := rfl

theorem toTower_memRel_eq (n : ℕ) : (I.toTower hN).model.memRel n = I.model.rel (.inl (.memZ n)) := by
  have := (I.ΔIso hN).pullRel_memRel n
  rw [ΔIso_pullRel, ClauseFamily.Δ.memRel_eq] at this
  exact this

theorem toTower_jRel_eq (n : ℕ) : (I.toTower hN).model.jRel n = I.model.rel (.inl (.liftZ n)) := by
  have := (I.ΔIso hN).pullRel_jRel n
  rw [ΔIso_pullRel, ClauseFamily.Δ.jRel_eq] at this
  exact this

theorem toTower_kappaRel_eq (n : ℕ) :
    (I.toTower hN).model.kappaRel n = I.model.rel (.inl (.bnd n)) := by
  have := (I.ΔIso hN).pullRel_kappaRel n
  rw [ΔIso_pullRel, ClauseFamily.Δ.kappaRel_eq] at this
  exact this

/-- A class system on the model, read on the model of the reduct. -/
noncomputable def towerSys (𝒩 : StrSys I.model) : ClassSystem (I.toTower hN).model where
  toClassSys := 𝒩.toClassSys
  memRel_mem n := by rw [toTower_memRel_eq]; exact 𝒩.rel_mem (.inl (.memZ n))
  j_mem n := by rw [toTower_jRel_eq]; exact 𝒩.rel_mem (.inl (.liftZ n))
  kappa_mem n := by rw [toTower_kappaRel_eq]; exact 𝒩.rel_mem (.inl (.bnd n))

theorem towerSys_eq_map (𝒩 : StrSys I.model) :
    (ClauseFamily.ΔSys ⟨I.model, 𝒩⟩ hN).map (I.ΔIso hN) = I.towerSys hN 𝒩 :=
  ClassSystem.ext fun k => by ext C; exact Iff.rfl

/-- The model of the reduct satisfies `H` for the read class system. -/
theorem toTower_isTowerModel {𝒩 : StrSys I.model} (h : ClauseFamily.IsGenModel ⟨I.model, 𝒩⟩)
    (hN' : ClauseFamily.IsWF I.model := h.wf) :
    IsTowerModel ⟨(I.toTower hN').model, I.towerSys hN' 𝒩⟩ :=
  IsTowerModel.congr_sys (I.towerSys_eq_map hN' 𝒩) (IsTowerModel.transport (I.ΔIso hN') h.tower)

end GenInterp

/-! ### Isomorphisms of models as tower isomorphisms -/

namespace GenIso

variable {F : ClauseFamily.{u}} {M N : Str.{u} F.sig} (i : GenIso M N)

theorem rel_iff' (r : F.sig.Rel) (t : Fin (F.sig.arity r) → Sorted.El M.U) :
    t ∈ M.rel r ↔ (fun i' => i.mapEl (t i')) ∈ N.rel r := i.rel_iff r t

theorem rel_memZ (n : ℕ) (a b : Sorted.El M.U) :
    ![a, b] ∈ M.rel (.inl (.memZ n)) ↔ ![i.mapEl a, i.mapEl b] ∈ N.rel (.inl (.memZ n)) := by
  rw [i.rel_iff', map_vec_two]

theorem rel_liftZ (n : ℕ) (a b : Sorted.El M.U) :
    ![a, b] ∈ M.rel (.inl (.liftZ n)) ↔ ![i.mapEl a, i.mapEl b] ∈ N.rel (.inl (.liftZ n)) := by
  rw [i.rel_iff', map_vec_two]

theorem rel_bnd (n : ℕ) (a : Sorted.El M.U) :
    ![a] ∈ M.rel (.inl (.bnd n)) ↔ ![i.mapEl a] ∈ N.rel (.inl (.bnd n)) := by
  rw [i.rel_iff', map_vec_one]

/-- The tower isomorphism underlying an isomorphism of well-formed
structures. -/
noncomputable def toTowerIso (hM : ClauseFamily.IsWF M) (hN : ClauseFamily.IsWF N) :
    TowerIso (ClauseFamily.Δ M hM) (ClauseFamily.Δ N hN) where
  toFun := i.toFun
  bijective := i.bijective
  mem_iff n x y :=
    (ClauseFamily.Δ.mem_iff hN (i.toFun n x) (i.toFun n y)).trans
      ((i.rel_memZ n (Sorted.inj M.U x) (Sorted.inj M.U y)).symm.trans
        (ClauseFamily.Δ.mem_iff hM x y).symm)
  j_comm n x :=
    (ClauseFamily.Δ.j_iff hN n (i.toFun n x) (i.toFun (n + 1) ((ClauseFamily.Δ M hM).j n x))).1
      ((i.rel_liftZ n _ _).1 (ClauseFamily.Δ.j_spec hM n x))
  κ_comm n :=
    (ClauseFamily.Δ.κ_iff hN n (i.toFun (n + 1) ((ClauseFamily.Δ M hM).κ n))).1
      ((i.rel_bnd n _).1 (ClauseFamily.Δ.κ_spec hM n))

end GenIso

/-! ### Solidity of the expansion -/

namespace ClauseFamily

variable (F : ClauseFamily.{u})

/-- Solidity of `T(𝔉)`, in the same semantic form as `TowerTheorySolid`:
for models `M ⊳ N ⊳ P` of `T(𝔉)` (the middle model with any class system
below the induced one, the inner with any class system) and an
`M`-definable isomorphism `M ≅ P`, there is an `M`-definable isomorphism
`M ≅ N`. -/
def IsSolid : Prop :=
  ∀ (M : StrWithSys.{u} F.sig), F.IsGenModel M →
  ∀ (I : GenInterp M.M.U M.𝒟.toClassSys F.sig) (𝒩 : StrSys I.model),
    (∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩.D k → C ∈ I.induced.D k) →
    F.IsGenModel ⟨I.model, 𝒩⟩ →
  ∀ (J : GenInterp I.model.U 𝒩.toClassSys F.sig) (𝒬 : StrSys J.model), F.IsGenModel ⟨J.model, 𝒬⟩ →
  ∀ (i : GenIso M.M J.model), i.DefinableIn M.𝒟.toClassSys (I.pres.comp J.pres) →
  ∃ h : GenIso M.M I.model, h.DefinableIn M.𝒟.toClassSys I.pres

/-- **Expansions of `H` by clause-defined symbols are solid.** -/
theorem solid : F.IsSolid := by
  intro M hM I 𝒩 h𝒩 hN J 𝒬 hP i hi
  let T : TowerWithClasses.{u} := ⟨Δ M.M hM.wf, ΔSys M hM.wf⟩
  let I_T : Interp T := I.toTower hN.wf
  let 𝒩_T : ClassSystem I_T.model := I.towerSys hN.wf 𝒩
  let J_T : Interp ⟨I_T.model, 𝒩_T⟩ := J.toTower hP.wf
  let 𝒬_T : ClassSystem J_T.model := J.towerSys hP.wf 𝒬
  let i_T : TowerIso T.T J_T.model := (i.toTowerIso hM.wf hP.wf).trans (J.ΔIso hP.wf)
  have hi_T : i_T.DefinableIn T.𝒟 (I_T.pres.comp J_T.pres) := hi
  have h𝒩_T : ∀ k (C : I_T.model.Rel k), C ∈ 𝒩_T.D k → C ∈ I_T.induced.D k := h𝒩
  obtain ⟨h_T, hh⟩ := tower_solid T hM.tower I_T 𝒩_T h𝒩_T (I.toTower_isTowerModel hN)
    J_T 𝒬_T (J.toTower_isTowerModel hP) i_T hi_T
  refine ⟨{ toFun := h_T.toFun, bijective := h_T.bijective, rel_iff := ?_ }, hh⟩
  intro r t
  rcases r with r | f
  · rcases r with n | n | n
    · exact (Set.ext_iff.1 (Δ.memRel_eq hM.wf n) t).symm.trans
        ((Set.ext_iff.1 (h_T.pullRel_memRel n) t).symm.trans
          (Set.ext_iff.1 (I.toTower_memRel_eq hN.wf n) (fun i => h_T.mapEl (t i))))
    · exact (Set.ext_iff.1 (Δ.jRel_eq hM.wf n) t).symm.trans
        ((Set.ext_iff.1 (h_T.pullRel_jRel n) t).symm.trans
          (Set.ext_iff.1 (I.toTower_jRel_eq hN.wf n) (fun i => h_T.mapEl (t i))))
    · exact (Set.ext_iff.1 (Δ.kappaRel_eq hM.wf n) t).symm.trans
        ((Set.ext_iff.1 (h_T.pullRel_kappaRel n) t).symm.trans
          (Set.ext_iff.1 (I.toTower_kappaRel_eq hN.wf n) (fun i => h_T.mapEl (t i))))
  · rw [hM.clause f, hN.clause f]
    exact (F.G_iso f h_T t).trans (F.G_iso f (I.ΔIso hN.wf) (fun i => h_T.mapEl (t i))).symm

end ClauseFamily

end SolidLean.Solid
