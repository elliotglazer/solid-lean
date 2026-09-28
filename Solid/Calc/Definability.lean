import Solid.Calc.Substitution
import Solid.Gen.Definable
import Solid.TDef

/-!
# Definability of the evaluator's predicates

The value relation `Val` is the satisfaction of a tower formula, hence a
class of every class system on the tower (`Formula.def_mem`).  Fixing the
environment as parameters keeps it a class (`TDef.fixInit`), and reading it
on one sort makes it a class of that sort's system (`TDef.toDef1`), which is
what Separation and Replacement in the sort models need.
-/

universe u

namespace SolidLean.Solid.ClassSystem.TDef

variable {M : MemTower.{u}} {𝒟 : ClassSystem M}

/-- Fixing the trailing coordinates by parameters. -/
theorem fixTail : ∀ {m k : ℕ} {P : (Fin (k + m) → M.El) → Prop}, 𝒟.TDef (k + m) P →
    ∀ η : Fin m → M.El, 𝒟.TDef k (fun u => P (Fin.append u η))
  | 0, k, P, hP, η => by
    refine congr (fun u => ?_) hP
    have : Fin.append u η = u := by
      funext i
      exact Fin.append_left u η ⟨i.1, by omega⟩
    rw [this]
  | m + 1, k, P, hP, η => by
    have h1 : 𝒟.TDef (k + m) (fun t => P (Fin.snoc t (η (Fin.last m)))) :=
      withParam (k := k + m) (η (Fin.last m)) hP
    have h2 := fixTail h1 (Fin.init η)
    refine congr (fun u => ?_) h2
    show P (Fin.snoc (Fin.append u (Fin.init η)) (η (Fin.last m))) ↔ P (Fin.append u η)
    rw [← Formula.append_snoc u (Fin.init η) (η (Fin.last m)), Fin.snoc_init_self]

/-- The rotation exchanging the two blocks of a tuple. -/
def rot (m k : ℕ) : Fin (m + k) → Fin (k + m) :=
  Fin.addCases (motive := fun _ => Fin (k + m)) (fun j => Fin.natAdd k j) (fun j => Fin.castAdd m j)

theorem append_comp_rot {α : Type*} {m k : ℕ} (η : Fin m → α) (u : Fin k → α) :
    (Fin.append u η) ∘ rot m k = Fin.append η u := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · show Fin.append u η (rot m k (Fin.castAdd k j)) = Fin.append η u (Fin.castAdd k j)
    rw [rot, Fin.addCases_left, Fin.append_right, Fin.append_left]
  · show Fin.append u η (rot m k (Fin.natAdd m j)) = Fin.append η u (Fin.natAdd m j)
    rw [rot, Fin.addCases_right, Fin.append_left, Fin.append_right]

/-- Fixing the leading coordinates by parameters. -/
theorem fixInit {m k : ℕ} {P : (Fin (m + k) → M.El) → Prop} (hP : 𝒟.TDef (m + k) P)
    (η : Fin m → M.El) : 𝒟.TDef k (fun u => P (Fin.append η u)) := by
  have h1 := reindex (rot m k) hP
  have h2 := fixTail h1 η
  refine congr (fun u => ?_) h2
  show P ((Fin.append u η) ∘ rot m k) ↔ _
  rw [append_comp_rot]

end SolidLean.Solid.ClassSystem.TDef

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.ClassSystem SolidLean.Solid.TF

variable {T : MemTower.{u}} (𝒟 : ClassSystem T)

theorem append_one {α : Type*} {m : ℕ} (η : Fin m → α) (u : Fin 1 → α) :
    Fin.append η u = Fin.snoc (α := fun _ => α) η (u 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    exact Fin.append_right η u 0
  · rw [Fin.snoc_castSucc]
    exact Fin.append_left η u j

theorem append_two {α : Type*} {m : ℕ} (η : Fin m → α) (u : Fin 2 → α) :
    Fin.append η u = Fin.snoc (α := fun _ => α) (Fin.snoc (α := fun _ => α) η (u 0)) (u 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have : Fin.castAdd 2 j = Fin.castSucc (Fin.castSucc j) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.append_right]
    match j with
    | ⟨0, _⟩ =>
      have : Fin.natAdd m (⟨0, by omega⟩ : Fin 2) = Fin.castSucc (Fin.last m) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    | ⟨1, _⟩ =>
      have : Fin.natAdd m (⟨1, by omega⟩ : Fin 2) = Fin.last (m + 1) := Fin.ext rfl
      rw [this, Fin.snoc_last]
      rfl

/-- Satisfaction of a tower formula is a class. -/
theorem TDef_sat {k : ℕ} {s : Fin k → ℕ} (φ : TF k s) :
    𝒟.TDef k (fun t => φ.Sat T.toStr t) :=
  Formula.def_mem 𝒟.toStrSys φ

/-- The value relation is a class (environment and value as the tuple). -/
theorem TDef_val {m : ℕ} (Γ : Ctx m) (t : Term) :
    𝒟.TDef (m + 1) (fun v => Val T Γ t (Fin.init v) (v (Fin.last m))) := by
  refine TDef.congr (fun v => ?_)
    (TDef.and_ (TDef.sort (Fin.last m) (t.cls Γ)) (TDef_sat 𝒟 (eval Γ t)))
  show (v (Fin.last m)).1 = t.cls Γ ∧ (eval Γ t).Sat T.toStr v ↔ _
  unfold Val
  rw [Fin.snoc_init_self]

/-- The value relation with the environment fixed. -/
theorem TDef_val1 {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) :
    𝒟.TDef 1 (fun u => Val T Γ t η (u 0)) := by
  refine TDef.congr (fun u => ?_) (TDef.fixInit (TDef_val 𝒟 Γ t) η)
  show Val T Γ t (Fin.init (Fin.append η u)) (Fin.append η u (Fin.last m)) ↔ _
  rw [append_one η u, Fin.init_snoc, Fin.snoc_last]

/-- The value relation in a context extended by one binder, with the
environment fixed and the new variable's value and the value as the tuple. -/
theorem TDef_val2 {m : ℕ} (Γ : Ctx m) (A : Term) (i : ℕ) (t : Term) (η : Env T m) :
    𝒟.TDef 2 (fun u => Val T (Γ.snoc A i) t (Fin.snoc (α := fun _ => T.El) η (u 0)) (u 1)) := by
  refine TDef.congr (fun u => ?_) (TDef.fixInit (m := m) (k := 2) (TDef_val 𝒟 (Γ.snoc A i) t) η)
  rw [append_two η u, Fin.init_snoc, Fin.snoc_last]

/-- Satisfaction of a tower formula, with parameters, read on one sort. -/
theorem sortDef_sat {k n : ℕ} {s : Fin (k + 1) → ℕ} (φ : TF (k + 1) s) (params : Fin k → T.El) :
    (𝒟.sortSystem n).Def 1
      (fun u => φ.Sat T.toStr (Fin.snoc (α := fun _ => T.El) params (T.inj (u 0)))) := by
  refine TDef.toDef1 (s := n) (P := fun z => φ.Sat T.toStr (Fin.snoc (α := fun _ => T.El) params (T.inj z)))
    (TDef.congr (fun t => ?_) (TDef.and_ (TDef.sort 0 n) (TDef.fixInit (TDef_sat 𝒟 φ) params)))
  show (t 0).1 = n ∧ φ.Sat T.toStr (Fin.append params t) ↔ _
  rw [append_one params t]
  constructor
  · rintro ⟨h0, h⟩
    obtain ⟨z, hz⟩ := elSort T (t 0) h0
    exact ⟨z, hz, by rw [← hz]; exact h⟩
  · rintro ⟨z, hz, h⟩
    exact ⟨by rw [hz], by rw [hz]; exact h⟩

/-- The value relation at a fixed environment, on the sort of the term. -/
theorem sortDef_val {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) {n : ℕ} (hn : t.cls Γ = n) :
    (𝒟.sortSystem n).Def 1 (fun u => Val T Γ t η (T.inj (u 0))) := by
  refine TDef.toDef1 (s := n) (P := fun z => Val T Γ t η (T.inj z))
    (TDef.congr (fun u => ?_) (TDef_val1 𝒟 Γ t η))
  constructor
  · intro h
    obtain ⟨z, hz⟩ := elSort T (u 0) (h.sort.trans hn)
    exact ⟨z, hz, by rw [← hz]; exact h⟩
  · rintro ⟨z, hz, h⟩
    rw [hz]; exact h

/-- The dependent product condition is a class of sort `max i j`. -/
theorem sortDef_isPiFun {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term}
    (hB : B.cls (Γ.snoc A i) = j + 1) (η : Env T m) (vA : T.U (i + 1)) :
    (𝒟.sortSystem (max i j)).Def 1 (fun u => IsPiFun T Γ i j A B η vA (u 0)) := by
  have := sortDef_sat 𝒟 (n := max i j)
    (piBodyF Γ.levels i j (recast (by sorts) (eval (Γ.snoc A i) B)))
    (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
      (Fin.snoc (α := fun _ => T.El) η (T.inj vA)) (T.inj vA)) (T.inj vA))
  refine SetClassSystem.Def.congr (fun u => ?_) this
  exact Sat_piBodyF T hB η _ _ vA (u 0)

/-- The graph condition of an abstraction is a class of sort `max i j`. -/
theorem sortDef_lamBody {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b : Term}
    (hb : b.cls (Γ.snoc A i) = j) (η : Env T m) (vA : T.U (i + 1)) :
    (𝒟.sortSystem (max i j)).Def 1 (fun u => ∃ a : T.U i, T.mem (T.j i a) vA ∧
      ∃ vb : T.U j, Val T (Γ.snoc A i) b (Fin.snoc η (T.inj a)) (T.inj vb) ∧
        (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) a)
          (T.liftLE (le_max_right i j) vb) (u 0)) := by
  have := sortDef_sat 𝒟 (n := max i j)
    (lamBodyF Γ.levels i j (recast (by sorts) (eval (Γ.snoc A i) b)))
    (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) η (T.inj vA)) (T.inj vA))
  refine SetClassSystem.Def.congr (fun u => ?_) this
  exact Sat_lamBodyF T hb η _ vA (u 0)

/-- The relation `x = j^{M-i}(a) ∧ y = j^{M-j}(vB')` where `j_j(vB')` is the
value of `B` at `a`: the codomain family, used to bound the values of
functions in a product. -/
def CodRel {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) (x y : T.U (max i j)) : Prop :=
  ∃ a : T.U i, x = T.liftLE (le_max_left i j) a ∧
    ∃ vB : T.U (j + 1), Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ∧
      ∃ vB' : T.U j, vB = T.j j vB' ∧ y = T.liftLE (le_max_right i j) vB'

theorem sortDef_codRel {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) :
    (𝒟.sortSystem (max i j)).Def 2 (fun u => CodRel Γ i j A B η (u 0) (u 1)) := by
  refine TDef.toDef2 ?_
  have h5 : 𝒟.TDef 5 (fun s =>
      (∃ a₀ : T.U i, s 2 = T.inj a₀ ∧ s 0 = T.inj (T.liftLE (le_max_left i j) a₀)) ∧
      Val T (Γ.snoc A i) B (Fin.snoc (α := fun _ => T.El) η (s 2)) (s 3) ∧
      (∃ x₀ : T.U j, s 4 = T.inj x₀ ∧ s 3 = T.inj (T.j j x₀)) ∧
      (∃ b₀ : T.U j, s 4 = T.inj b₀ ∧ s 1 = T.inj (T.liftLE (le_max_right i j) b₀))) := by
    refine TDef.and_ ?_ (TDef.and_ ?_ (TDef.and_ (TDef.j_sort j 4 3) ?_))
    · refine TDef.congr (fun s => ?_) (TDef.reindex ![2, 0] (TDef.liftGraph (le_max_left i j)))
      simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    · refine TDef.congr (fun s => ?_) (TDef.reindex ![2, 3] (TDef_val2 𝒟 Γ A i B η))
      simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
    · refine TDef.congr (fun s => ?_) (TDef.reindex ![4, 1] (TDef.liftGraph (le_max_right i j)))
      simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine TDef.congr (fun t => ?_) (TDef.exists_ i (TDef.exists_ (j + 1) (TDef.exists_ j h5)))
  simp only [Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three,
    Fin.snoc_four_four, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two,
    Fin.snoc_three_three, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
  unfold CodRel
  constructor
  · rintro ⟨a, vB, vB', ⟨a₀, ha₀, h0⟩, hval, ⟨x₀, hx₀, h3⟩, ⟨b₀, hb₀, h1⟩⟩
    have e1 := Sorted.inj_injective T.U ha₀
    have e2 := Sorted.inj_injective T.U hx₀
    have e3 := Sorted.inj_injective T.U hb₀
    subst e1; subst e2; subst e3
    refine ⟨_, _, h0, h1, a, rfl, vB, hval, vB', Sorted.inj_injective T.U h3, rfl⟩
  · rintro ⟨x, y, hx, hy, a, rfl, vB, hval, vB', rfl, rfl⟩
    exact ⟨a, T.j j vB', vB', ⟨a, rfl, hx⟩, hval, ⟨vB', rfl, rfl⟩, ⟨vB', rfl, hy⟩⟩

end SolidLean.Calc
