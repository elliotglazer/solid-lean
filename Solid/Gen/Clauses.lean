import Solid.Gen.FO
import Solid.Gen.Expansion

/-!
# Clause families given by first-order formulas, and canonical expansions

A tower is a structure for the *tower signature* `TowerSig`; a clause family
whose clauses are given by first-order formulas of that signature
(`ClauseFamily.ofFormulas`) automatically satisfies the definability and
invariance requirements, by `Formula.def_mem` and `Formula.sat_map`.  Such a
family is what the paper calls a *definitional expansion* of `H`: its theory
`T(𝔉)` is `H` together with one defining axiom per symbol, and it is
first-order.

Conversely every model of `H` expands canonically to a model of `T(𝔉)`
(`ClauseFamily.expand`), so `T(𝔉)` is consistent relative to `H` and has, up
to the reduct, exactly the models of `H`.
-/

universe u

namespace SolidLean.Solid

open Classical

/-- The tower signature. -/
abbrev TowerSig : Signature := ⟨TowerSym, TowerSym.arity, TowerSym.sortAt⟩

namespace MemTower

variable (T : MemTower.{u})

/-- A tower as a structure for the tower signature.  An `abbrev`, so that its
carrier unfolds to the tower's during unification. -/
abbrev toStr : Str.{u} TowerSig where
  U := T.U
  rel
    | .memZ n => T.memRel n
    | .liftZ n => T.jRel n
    | .bnd n => T.kappaRel n
  rel_sorts := by
    rintro (n | n | n) t ht
    · obtain ⟨x, y, hx, hy, -⟩ := ht
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · show (t 0).1 = n; rw [hx]
      · show (t 1).1 = n; rw [hy]
    · obtain ⟨x, hx, hy⟩ := ht
      refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
      · show (t 0).1 = n; rw [hx]
      · show (t 1).1 = n + 1; rw [hy]
    · refine Fin.forall_fin_one.2 ?_
      show (t 0).1 = n + 1
      rw [show t 0 = T.inj (T.κ n) from ht]

@[simp] theorem toStr_U : T.toStr.U = T.U := rfl
@[simp] theorem toStr_memZ (n : ℕ) : T.toStr.rel (.memZ n) = T.memRel n := rfl
@[simp] theorem toStr_liftZ (n : ℕ) : T.toStr.rel (.liftZ n) = T.jRel n := rfl
@[simp] theorem toStr_bnd (n : ℕ) : T.toStr.rel (.bnd n) = T.kappaRel n := rfl

end MemTower

/-- A class system on a tower is a class system on the corresponding
structure. -/
def ClassSystem.toStrSys {T : MemTower.{u}} (𝒟 : ClassSystem T) : StrSys T.toStr where
  toClassSys := 𝒟.toClassSys
  rel_mem
    | .memZ n => 𝒟.memRel_mem n
    | .liftZ n => 𝒟.j_mem n
    | .bnd n => 𝒟.kappa_mem n

/-- A tower isomorphism as an isomorphism of structures. -/
def TowerIso.toGenIso {T T' : MemTower.{u}} (e : TowerIso T T') : GenIso T.toStr T'.toStr where
  toFun := e.toFun
  bijective := e.bijective
  rel_iff
    | .memZ n, t => (Set.ext_iff.1 (e.pullRel_memRel n) t).symm
    | .liftZ n, t => (Set.ext_iff.1 (e.pullRel_jRel n) t).symm
    | .bnd n, t => (Set.ext_iff.1 (e.pullRel_kappaRel n) t).symm

@[simp] theorem TowerIso.toGenIso_mapEl {T T' : MemTower.{u}} (e : TowerIso T T') (z : T.El) :
    e.toGenIso.mapEl z = e.mapEl z := rfl

/-! ### Profiles -/

namespace Sorted

variable (U : ℕ → Type u)

/-- The tuples with a given profile of sorts. -/
def profileRel {k : ℕ} (s : Fin k → ℕ) : Rel U k := {t | ∀ i, (t i).1 = s i}

theorem profileRel_eq {k : ℕ} (s : Fin k → ℕ) :
    profileRel U s = ⋂ i : Fin k, reindex U (fun _ : Fin 1 => i) (sortRel U (s i)) := by
  ext t
  simp only [profileRel, Set.mem_iInter, Set.mem_ofPred_eq]
  exact Iff.rfl

end Sorted

theorem ClassSys.profileRel_mem {U : ℕ → Type u} (𝒟 : ClassSys U) {k : ℕ} (s : Fin k → ℕ) :
    Sorted.profileRel U s ∈ 𝒟.D k := by
  rw [Sorted.profileRel_eq]
  exact 𝒟.iInter_mem _ (fun i => 𝒟.reindex_mem _ (𝒟.sort_mem (s i)))

/-! ### Clause families from formulas -/

namespace ClauseFamily

/-- The clause family whose clauses are given by first-order formulas of the
tower signature. -/
noncomputable def ofFormulas (Sym : Type) (arity : Sym → ℕ) (sortAt : (f : Sym) → Fin (arity f) → ℕ)
    (φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)) : ClauseFamily.{u} where
  Sym := Sym
  arity := arity
  sortAt := sortAt
  G f T := (φ f).Def T.toStr ∩ Sorted.profileRel T.U (sortAt f)
  G_sorts f T t ht := ht.2
  G_def f T := T.𝒟.toStrSys.inter_mem ((φ f).def_mem T.𝒟.toStrSys) (T.𝒟.profileRel_mem _)
  G_iso f T T' e t := by
    show (φ f).Sat T.toStr t ∧ (∀ i, (t i).1 = sortAt f i) ↔
      (φ f).Sat T'.toStr (fun i => e.mapEl (t i)) ∧ ∀ i, (e.mapEl (t i)).1 = sortAt f i
    rw [(φ f).sat_map e.toGenIso t]
    exact Iff.rfl

/-! ### The canonical expansion of a model of `H` -/

variable (F : ClauseFamily.{u})

/-- The expansion of a tower to a structure for `F.sig`: the tower symbols by
the tower, the extra symbols by their clauses. -/
noncomputable def expandStr (T : MemTower.{u}) : Str.{u} F.sig where
  U := T.U
  rel
    | .inl r => T.toStr.rel r
    | .inr f => F.G f T
  rel_sorts
    | .inl r, t, ht => T.toStr.rel_sorts r t ht
    | .inr f, t, ht => F.G_sorts f T t ht

/-- The expansion of a tower with classes. -/
noncomputable def expand (T : TowerWithClasses.{u}) : StrWithSys.{u} F.sig where
  M := F.expandStr T.T
  𝒟 :=
    { toClassSys := T.𝒟.toClassSys
      rel_mem
        | .inl r => T.𝒟.toStrSys.rel_mem r
        | .inr f => F.G_def f T }

theorem expand_wf (T : TowerWithClasses.{u}) : IsWF (F.expand T).M where
  liftZ_total n x := ⟨T.T.j n x, x, rfl, rfl⟩
  liftZ_unique n x y y' hy hy' := by
    obtain ⟨x₁, hx₁, hy₁⟩ := hy
    obtain ⟨x₂, hx₂, hy₂⟩ := hy'
    have e1 : x = x₁ := Sorted.inj_injective T.T.U hx₁
    have e2 : x = x₂ := Sorted.inj_injective T.T.U hx₂
    subst e1; subst e2
    exact (Sorted.inj_injective T.T.U hy₁).trans (Sorted.inj_injective T.T.U hy₂).symm
  bnd_exists n := ⟨T.T.κ n, rfl⟩
  bnd_unique n y y' hy hy' :=
    (Sorted.inj_injective T.T.U hy).trans (Sorted.inj_injective T.T.U hy').symm

/-- The identity, as an isomorphism from a tower to the underlying tower of
its expansion. -/
noncomputable def expandIso (T : TowerWithClasses.{u}) :
    TowerIso T.T (Δ (F.expand T).M (F.expand_wf T)) where
  toFun _ := id
  bijective _ := Function.bijective_id
  mem_iff n x y := by
    show ![T.T.inj x, T.T.inj y] ∈ T.T.memRel n ↔ T.T.mem x y
    constructor
    · rintro ⟨x', y', hx, hy, h⟩
      have e1 : x = x' := Sorted.inj_injective T.T.U hx
      have e2 : y = y' := Sorted.inj_injective T.T.U hy
      subst e1; subst e2; exact h
    · intro h; exact ⟨x, y, rfl, rfl, h⟩
  j_comm n x := (F.expand_wf T).liftZ_unique n x _ _ ⟨x, rfl, rfl⟩ (Δ.j_spec (F.expand_wf T) n x)
  κ_comm n := (F.expand_wf T).bnd_unique n _ _ rfl (Δ.κ_spec (F.expand_wf T) n)

theorem expandIso_pullRel (T : TowerWithClasses.{u}) {k : ℕ}
    (C : (Δ (F.expand T).M (F.expand_wf T)).Rel k) : (F.expandIso T).pullRel C = C := rfl

/-- **Every model of `H` expands to a model of `T(𝔉)`.** -/
theorem expand_isGenModel (T : TowerWithClasses.{u}) (hT : IsTowerModel T) :
    F.IsGenModel (F.expand T) where
  wf := F.expand_wf T
  tower := by
    refine IsTowerModel.congr_sys ?_ (IsTowerModel.transport (F.expandIso T) hT)
    exact ClassSystem.ext fun k => by ext C; exact Iff.rfl
  clause f := by
    ext t
    exact F.G_iso f (F.expandIso T) t

end ClauseFamily

end SolidLean.Solid
