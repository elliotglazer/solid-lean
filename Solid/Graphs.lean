module

public import Solid.TDef
public import Solid.Interpretation

/-!
# Definable graphs over presentations

Plumbing between the three levels of the solidity configuration
`M ⊳ N ⊳ P`: how representatives compose (`Presentation.comp_rep_eq_some_iff`),
how the representation relation of an interpretation reads in terms of its
presentation (`Interp.Rep_inj_iff'`), and closure properties of graphs of maps
out of a presented tower (`PGraph`): composition with the lifts of the
ambient tower and with the transitions of the presented tower.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-! ### Presentations -/

namespace Presentation

variable {M N P : MemTower.{u}}

theorem comp_rep_eq_some_iff (p : Presentation M.U N.U) (q : Presentation N.U P.U) (n : ℕ)
    (x : M.U (p.a (q.a n))) (z : P.U n) :
    (p.comp q).rep n x = some z ↔ ∃ y, p.rep (q.a n) x = some y ∧ q.rep n y = some z := by
  show (p.rep (q.a n) x).bind (q.rep n) = some z ↔ _
  cases p.rep (q.a n) x with
  | none => simp
  | some y =>
    simp only [Option.bind_some, Option.some.injEq]
    constructor
    · intro h; exact ⟨y, rfl, h⟩
    · rintro ⟨y', hy', h⟩; cases hy'; exact h

end Presentation

namespace Interp

variable {M : TowerWithClasses.{u}} (I : Interp M)

theorem pres_rep_eq_some_iff {n : ℕ} (x : M.T.U (I.a n)) (q : I.Carrier n) :
    I.pres.rep n x = some q ↔ ∃ h : x ∈ I.dom n, I.cls ⟨x, h⟩ = q := by
  show (if h : x ∈ I.dom n then some (I.cls ⟨x, h⟩) else none) = some q ↔ _
  by_cases h : x ∈ I.dom n
  · rw [dif_pos h]
    simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h, h'⟩, fun ⟨_, h'⟩ => h'⟩
  · rw [dif_neg h]
    simp only [reduceCtorEq, false_iff, not_exists]
    intro h'; exact (h h').elim

theorem pres_rep_cls {n : ℕ} (x : I.Dom n) : I.pres.rep n x.1 = some (I.cls x) :=
  (I.pres_rep_eq_some_iff x.1 (I.cls x)).2 ⟨x.2, rfl⟩

theorem pres_rep_dom {n : ℕ} {x : M.T.U (I.a n)} {q : I.Carrier n}
    (h : I.pres.rep n x = some q) : x ∈ I.dom n :=
  ((I.pres_rep_eq_some_iff x q).1 h).1

/-- Representation in terms of the presentation. -/
theorem Rep_inj_iff' {n : ℕ} (x : M.T.U (I.a n)) (q : I.Carrier n) :
    I.Rep (M.T.inj x) (I.model.inj (n := n) q) ↔ I.pres.rep n x = some q := by
  rw [I.Rep_inj_iff, I.pres_rep_eq_some_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    have := MemTower.inj_injective' _ hx'
    subst this
    exact ⟨x'.2, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨x, h⟩, rfl, rfl⟩

/-- Preimages of admissible relations of the interpreted tower are admissible. -/
theorem preimage_mem {k : ℕ} {C : I.model.Rel k} (hC : C ∈ I.induced.D k) (b : Fin k → ℕ) :
    I.preimage b C ∈ M.𝒟.D k := hC b

/-- A unary preimage, read through the presentation. -/
theorem mem_preimage_one_iff (n : ℕ) (C : I.model.Rel 1) (t : Fin 1 → M.T.El) :
    t ∈ I.preimage ![n] C ↔ ∃ (x : M.T.U (I.a n)) (q : I.Carrier n),
      t 0 = M.T.inj x ∧ I.pres.rep n x = some q ∧ ![I.model.inj (n := n) q] ∈ C := by
  constructor
  · rintro ⟨u, hu, huC⟩
    obtain ⟨x, hx, hu0⟩ := I.rep_of_sort (hu 0).1 (hu 0).2
    refine ⟨x.1, I.cls x, hx, I.pres_rep_cls x, ?_⟩
    have : u = ![I.model.inj (n := n) (I.cls x)] := by
      funext i
      have : i = 0 := Subsingleton.elim i 0
      subst this
      exact hu0
    rw [← this]; exact huC
  · rintro ⟨x, q, hx, hq, hC⟩
    refine ⟨![I.model.inj (n := n) q], fun i => ?_, hC⟩
    have : i = 0 := Subsingleton.elim i 0
    subst this
    refine ⟨rfl, ?_⟩
    rw [hx]
    exact (I.Rep_inj_iff' x q).2 hq

/-- A binary preimage, read through the presentation. -/
theorem mem_preimage_two_iff (n₀ n₁ : ℕ) (C : I.model.Rel 2) (t : Fin 2 → M.T.El) :
    t ∈ I.preimage ![n₀, n₁] C ↔
      ∃ (x₀ : M.T.U (I.a n₀)) (x₁ : M.T.U (I.a n₁)) (q₀ : I.Carrier n₀) (q₁ : I.Carrier n₁),
        t 0 = M.T.inj x₀ ∧ t 1 = M.T.inj x₁ ∧ I.pres.rep n₀ x₀ = some q₀ ∧
        I.pres.rep n₁ x₁ = some q₁ ∧
        ![I.model.inj (n := n₀) q₀, I.model.inj (n := n₁) q₁] ∈ C := by
  constructor
  · rintro ⟨u, hu, huC⟩
    obtain ⟨x₀, hx₀, hu0⟩ := I.rep_of_sort (hu 0).1 (hu 0).2
    obtain ⟨x₁, hx₁, hu1⟩ := I.rep_of_sort (hu 1).1 (hu 1).2
    refine ⟨x₀.1, x₁.1, I.cls x₀, I.cls x₁, hx₀, hx₁, I.pres_rep_cls x₀, I.pres_rep_cls x₁, ?_⟩
    have : u = ![I.model.inj (n := n₀) (I.cls x₀), I.model.inj (n := n₁) (I.cls x₁)] :=
      funext (Fin.forall_fin_two.2 ⟨hu0, hu1⟩)
    rw [← this]; exact huC
  · rintro ⟨x₀, x₁, q₀, q₁, hx₀, hx₁, hq₀, hq₁, hC⟩
    refine ⟨![I.model.inj (n := n₀) q₀, I.model.inj (n := n₁) q₁], Fin.forall_fin_two.2 ⟨?_, ?_⟩, hC⟩
    · refine ⟨rfl, ?_⟩
      show I.Rep (t 0) _
      rw [hx₀]; exact (I.Rep_inj_iff' x₀ q₀).2 hq₀
    · refine ⟨rfl, ?_⟩
      show I.Rep (t 1) _
      rw [hx₁]; exact (I.Rep_inj_iff' x₁ q₁).2 hq₁

end Interp

/-! ### Graphs of maps out of a presented tower -/

/-- The graph of `f : P n → N m` over representatives: relates a representative
of `q` to `f q`. -/
def PGraph {N P : MemTower.{u}} (p : Presentation N.U P.U) {n m : ℕ} (f : P.U n → N.U m) :
    N.Rel 2 :=
  {t | ∃ (u : N.U (p.a n)) (q : P.U n), t 0 = N.inj u ∧ t 1 = N.inj (f q) ∧ p.rep n u = some q}

namespace PGraph

open ClassSystem

variable {N P : MemTower.{u}} (𝒟 : ClassSystem N) (p : Presentation N.U P.U)

theorem tdef_iff {n m : ℕ} (f : P.U n → N.U m) :
    PGraph p f ∈ 𝒟.D 2 ↔ 𝒟.TDef 2 (fun t => ∃ (u : N.U (p.a n)) (q : P.U n),
      t 0 = N.inj u ∧ t 1 = N.inj (f q) ∧ p.rep n u = some q) := Iff.rfl

/-- Composing with a lift of the ambient tower. -/
theorem lift {n m m' : ℕ} (h : m ≤ m') {f : P.U n → N.U m} (hf : PGraph p f ∈ 𝒟.D 2) :
    PGraph p (fun q => N.liftLE h (f q)) ∈ 𝒟.D 2 := by
  rw [tdef_iff] at hf ⊢
  refine TDef.congr ?_ (TDef.exists_ m (TDef.and_ (TDef.reindex ![0, 2] hf)
    (TDef.reindex ![2, 1] (TDef.liftGraph h))))
  intro t
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
  constructor
  · rintro ⟨y, ⟨u, q, hu, hy, hq⟩, x, hx, ht1⟩
    refine ⟨u, q, hu, ?_, hq⟩
    rw [ht1, N.inj_injective' (hx.symm.trans hy)]
  · rintro ⟨u, q, hu, ht1, hq⟩
    exact ⟨f q, ⟨u, q, hu, rfl, hq⟩, f q, rfl, ht1⟩

end PGraph

namespace Interp

open ClassSystem

variable {M : TowerWithClasses.{u}} (I : Interp M)

/-- Composing a graph over the presentation of an interpreted tower with the
interpreted transition. -/
theorem PGraph_comp_j {n m : ℕ} {f : I.model.U (n + 1) → M.T.U m}
    (hf : PGraph I.pres f ∈ M.𝒟.D 2) :
    PGraph I.pres (fun q => f (I.model.j n q)) ∈ M.𝒟.D 2 := by
  rw [PGraph.tdef_iff] at hf ⊢
  have hdom : M.𝒟.TDef 1 (fun t => ∃ x : M.T.U (I.a n), t 0 = M.T.inj x ∧ x ∈ I.dom n) :=
    I.dom_def n
  have hjC : M.𝒟.TDef 2 (fun t => ∃ x y, t 0 = M.T.inj x ∧ t 1 = M.T.inj y ∧ I.jC n x y) :=
    I.jC_def n
  refine TDef.congr ?_ (TDef.exists_ (I.a (n + 1)) (TDef.and_
    (TDef.reindex (fun _ : Fin 1 => (0 : Fin 3)) hdom)
    (TDef.and_ (TDef.reindex ![0, 2] hjC) (TDef.reindex ![2, 1] hf))))
  intro t
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
  constructor
  · rintro ⟨u', ⟨u, hu, hud⟩, ⟨x, y, hx, hy, hjxy⟩, u'', q', hu'', ht1, hq'⟩
    have hxu : x = u := MemTower.inj_injective' _ (hx.symm.trans hu)
    have hyu' : y = u' := MemTower.inj_injective' _ hy.symm
    have hu''u' : u'' = u' := MemTower.inj_injective' _ hu''.symm
    rw [hxu, hyu'] at hjxy
    rw [hu''u'] at hq'
    obtain ⟨hu'd, hq'eq⟩ := (I.pres_rep_eq_some_iff u' q').1 hq'
    refine ⟨u, I.cls ⟨u, hud⟩, hu, ?_, I.pres_rep_cls ⟨u, hud⟩⟩
    rw [ht1, ← hq'eq]
    congr 2
    show I.cls ⟨u', hu'd⟩ = I.cls (I.jImage ⟨u, hud⟩)
    rw [I.cls_eq_iff]
    exact I.jC_func n u u' _ hu'd (I.jImage ⟨u, hud⟩).2 hjxy (I.jImage_spec ⟨u, hud⟩)
  · rintro ⟨u, q, hu, ht1, hq⟩
    obtain ⟨hud, rfl⟩ := (I.pres_rep_eq_some_iff u q).1 hq
    refine ⟨(I.jImage ⟨u, hud⟩).1, ⟨u, hu, hud⟩, ⟨u, _, hu, rfl, I.jImage_spec ⟨u, hud⟩⟩,
      (I.jImage ⟨u, hud⟩).1, I.cls (I.jImage ⟨u, hud⟩), rfl, ?_, I.pres_rep_cls _⟩
    rw [ht1]; rfl

/-- The graph of an isomorphism `i : M → P` in the sense of
`TowerIso.DefinableIn`, as a `TDef`. -/
theorem _root_.SolidLean.Solid.TowerIso.tdef_of_definableIn {M' P : MemTower.{u}}
    {𝒟 : ClassSystem M'} {p : Presentation M'.U P.U} {i : TowerIso M' P}
    (hi : i.DefinableIn 𝒟 p) (n : ℕ) :
    𝒟.TDef 2 (fun t => ∃ (x : M'.U n) (y : M'.U (p.a n)),
      t 0 = M'.inj x ∧ t 1 = M'.inj y ∧ p.rep n y = some (i.toFun n x)) := hi n

end Interp

end SolidLean.Solid
