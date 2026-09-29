module

public import Solid.Collapse

/-!
# The solidity configuration `M ⊳ N ⊳ P`

A `Config` bundles the data of the solidity statement: a model `M` of `H`,
an interpretation `I` of `H` in `M` (with `N := I.asModel`), an
interpretation `J` of `H` in `N` (with `P := J.asModel`), and an
`M`-definable isomorphism `i : M → P`.

The one general fact proved here is `Config.composite_def`: a relation
between `M` and `N` obtained by composing `i` with a relation admissible in
`N` (read through the representatives) is admissible in `M`.  Every
definability claim of Steps 1, 3, 5 and 6 is an instance.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical ClassSystem

/-- The configuration of the solidity theorem. -/
structure Config where
  M : TowerWithClasses.{u}
  hM : IsTowerModel M
  I : Interp M
  /-- The class system of the middle model: any system contained in the one
  induced from `M` (for a first-order interpretation, the definable
  relations of `N`). -/
  𝒩 : ClassSystem I.model
  h𝒩 : ∀ k (C : I.model.Rel k), C ∈ 𝒩.D k → C ∈ I.induced.D k
  hI : IsTowerModel ⟨I.model, 𝒩⟩
  J : Interp ⟨I.model, 𝒩⟩
  /-- The class system of the inner model: arbitrary. -/
  𝒬 : ClassSystem J.model
  hJ : IsTowerModel ⟨J.model, 𝒬⟩
  i : TowerIso M.T J.model
  hi : i.DefinableIn M.𝒟 (I.pres.comp J.pres)

namespace Config

variable (c : Config.{u})

/-- The middle model. -/
noncomputable abbrev N : TowerWithClasses.{u} := ⟨c.I.model, c.𝒩⟩

/-- The inner model. -/
noncomputable abbrev P : TowerWithClasses.{u} := ⟨c.J.model, c.𝒬⟩

theorem hN : IsTowerModel c.N := c.hI

theorem hP : IsTowerModel c.P := c.hJ

theorem P_T : c.P.T = c.J.model := rfl

/-- Composite definability: if `Q` is an admissible relation of `N` between
sorts `J.a n` (representatives of sort `n` of `P`) and `n₁`, then the
relation between `x : M n` and `r : M (I.a n₁)` saying "some representative
of `i x` and the element represented by `r` are `Q`-related" is admissible
in `M`. -/
theorem composite_def (n n₁ : ℕ) {Q : c.N.T.Rel 2} (hQ : Q ∈ c.N.𝒟.D 2) :
    c.M.𝒟.TDef 2 (fun t => ∃ (x : c.M.T.U n) (r : c.M.T.U (c.I.a n₁)),
      t 0 = c.M.T.inj x ∧ t 1 = c.M.T.inj r ∧
      ∃ (u : c.N.T.U (c.J.a n)) (y : c.N.T.U n₁),
        c.J.pres.rep n u = some (c.i.toFun n x) ∧ c.I.pres.rep n₁ r = some y ∧
        ![c.N.T.inj u, c.N.T.inj y] ∈ Q) := by
  have hpre : c.M.𝒟.TDef 2 (fun t => t ∈ c.I.preimage ![c.J.a n, n₁] Q) :=
    c.I.preimage_mem (c.h𝒩 _ _ hQ) ![c.J.a n, n₁]
  have hig := c.i.tdef_of_definableIn c.hi n
  refine TDef.congr ?_ (TDef.exists_ (c.I.a (c.J.a n))
    (TDef.and_ (TDef.reindex ![0, 2] hig) (TDef.reindex ![2, 1] hpre)))
  intro t
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc_two_zero, Fin.snoc_two_two]
  constructor
  · rintro ⟨m, ⟨x, m', hx, hm', hcomp⟩, hpre'⟩
    have hmm' : m' = m := MemTower.inj_injective' _ hm'.symm
    subst hmm'
    obtain ⟨u, hu, hJu⟩ := (Presentation.comp_rep_eq_some_iff _ _ _ _ _).1 hcomp
    obtain ⟨x₀, x₁, q₀, q₁, hx₀, hx₁, hq₀, hq₁, hQ'⟩ :=
      (c.I.mem_preimage_two_iff _ _ Q _).1 hpre'
    have hx₀m : x₀ = m' := MemTower.inj_injective' _ hx₀.symm
    subst hx₀m
    have hq₀u : q₀ = u := Option.some_injective _ (hq₀.symm.trans hu)
    subst hq₀u
    refine ⟨x, x₁, hx, hx₁, q₀, q₁, hJu, hq₁, hQ'⟩
  · rintro ⟨x, r, hx, hr, u, y, hJu, hIr, hQ'⟩
    obtain ⟨m, hm⟩ := c.I.pres.surj (c.J.a n) u
    refine ⟨m, ⟨x, m, hx, rfl, ?_⟩, ?_⟩
    · exact (Presentation.comp_rep_eq_some_iff _ _ _ _ _).2 ⟨u, hm, hJu⟩
    · exact (c.I.mem_preimage_two_iff _ _ Q _).2 ⟨m, r, u, y, rfl, hr, hm, hIr, hQ'⟩

/-- The relation "`lift y = f q`" between a representative of `q` and `y`, for
a map `f` with a definable graph. -/
theorem liftRel_def (n n₁ m : ℕ) (h : n₁ ≤ m) (f : c.P.T.U n → c.N.T.U m)
    (hf : PGraph c.J.pres f ∈ c.N.𝒟.D 2) :
    ({t | ∃ (u : c.N.T.U (c.J.a n)) (y : c.N.T.U n₁), t 0 = c.N.T.inj u ∧ t 1 = c.N.T.inj y ∧
      ∃ q, c.J.pres.rep n u = some q ∧ c.N.T.liftLE h y = f q} : c.N.T.Rel 2) ∈ c.N.𝒟.D 2 := by
  rw [PGraph.tdef_iff] at hf
  refine TDef.congr ?_ (TDef.exists_ m (TDef.and_ (TDef.reindex ![0, 2] hf)
    (TDef.reindex ![1, 2] (TDef.liftGraph h))))
  intro t
  simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
  constructor
  · rintro ⟨z, ⟨u, q, hu, hz, hq⟩, y, hy, hz'⟩
    refine ⟨u, y, hu, hy, q, hq, ?_⟩
    exact MemTower.inj_injective' _ (hz'.symm.trans hz)
  · rintro ⟨u, y, hu, hy, q, hq, hlift⟩
    exact ⟨f q, ⟨u, q, hu, rfl, hq⟩, y, hy, by rw [hlift]⟩

/-- Composite definability along a lift: the relation between `x : M n` and
`r : M (I.a n₁)` saying "`r` represents some `y` with `lift y = f (i x)`". -/
theorem composite_lift_def (n n₁ m : ℕ) (h : n₁ ≤ m) (f : c.P.T.U n → c.N.T.U m)
    (hf : PGraph c.J.pres f ∈ c.N.𝒟.D 2) :
    c.M.𝒟.TDef 2 (fun t => ∃ (x : c.M.T.U n) (r : c.M.T.U (c.I.a n₁)),
      t 0 = c.M.T.inj x ∧ t 1 = c.M.T.inj r ∧
      ∃ y : c.N.T.U n₁, c.I.pres.rep n₁ r = some y ∧ c.N.T.liftLE h y = f (c.i.toFun n x)) := by
  refine TDef.congr ?_ (c.composite_def n n₁ (c.liftRel_def n n₁ m h f hf))
  intro t
  constructor
  · rintro ⟨x, r, hx, hr, u, y, hJu, hIr, hQ'⟩
    obtain ⟨u', y', hu', hy', q, hq, hlift⟩ := hQ'
    have hu'u : u' = u := MemTower.inj_injective' _ hu'.symm
    have hy'y : y' = y := MemTower.inj_injective' _ hy'.symm
    subst hu'u hy'y
    have hq' : q = c.i.toFun n x := Option.some_injective _ (hq.symm.trans hJu)
    subst hq'
    exact ⟨x, r, hx, hr, y', hIr, hlift⟩
  · rintro ⟨x, r, hx, hr, y, hIr, hlift⟩
    obtain ⟨u, hu⟩ := c.J.pres.surj n (c.i.toFun n x)
    exact ⟨x, r, hx, hr, u, y, hu, hIr, u, y, rfl, rfl, c.i.toFun n x, hu, hlift⟩

end Config

end SolidLean.Solid
