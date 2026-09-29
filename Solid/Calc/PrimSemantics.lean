module

public import Solid.Calc.Semantics
public import Solid.Calc.Envs

/-!
# Reading the generic evaluator clause of primitive applications

`Val_prim` unfolds the value relation of `prim c args` into values of the
arguments and the defining clause `c.clauseF` of the primitive, read at the
tuple `(v̄, w)`.  The per-primitive readings of the clauses are in
`PrimRel.lean`.
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

local notation "cs" => Fin.castSucc

variable (T : MemTower.{u})

theorem append_zero_env {m : ℕ} (t : Fin (m + 1) → T.El) (vs : Fin 0 → T.El) :
    Fin.append t vs = t := by
  funext i; exact Fin.append_left t vs ⟨i.1, by omega⟩

/-- Reading of `existsVals`: the `n` existential values, the argument formulas
at each of them, and the clause at the whole tuple. -/
theorem Sat_existsVals {m : ℕ} (lev : Fin m → ℕ) (c : ℕ) :
    ∀ (n : ℕ) (sorts : Fin n → ℕ) (φ : (k : Fin n) → TF (m + 1) (Fin.snoc lev (sorts k)))
      (ψ : TF (m + 1 + n) (Fin.append (Fin.snoc lev c) sorts)) (t : Fin (m + 1) → T.El),
      (existsVals lev c n sorts φ ψ).Sat T.toStr t ↔
        ∃ vs : Fin n → T.El, (∀ k, (vs k).1 = sorts k) ∧
          (∀ k, (φ k).Sat T.toStr (Fin.snoc (α := fun _ => T.El) (Fin.init t) (vs k))) ∧
          ψ.Sat T.toStr (Fin.append t vs)
  | 0, sorts, φ, ψ, t => by
    simp only [existsVals, Sat_recast]
    constructor
    · intro h
      refine ⟨fun k => k.elim0, fun k => k.elim0, fun k => k.elim0, ?_⟩
      rw [append_zero_env]; exact h
    · rintro ⟨vs, -, -, h⟩
      rw [append_zero_env] at h; exact h
  | n + 1, sorts, φ, ψ, t => by
    simp only [existsVals]
    refine (Sat_existsVals lev c n (Fin.init sorts) (fun k => φ (cs k)) _ t).trans ?_
    simp only [Formula.Sat_ex, Formula.Sat_and, Formula.sat_rename, id_eq, place1_env]
    have e1 : ∀ (vs : Fin n → T.El) (x : T.El),
        Fin.snoc (α := fun _ => T.El)
          (fun l => Fin.snoc (α := fun _ => T.El) (Fin.append t vs) x (embEnv m (n + 1) l))
          (Fin.snoc (α := fun _ => T.El) (Fin.append t vs) x (Fin.last (m + 1 + n))) =
        Fin.snoc (α := fun _ => T.El) (Fin.init t) x := by
      intro vs x
      rw [Fin.snoc_last]
      congr 1
      funext l
      show Fin.snoc (α := fun _ => T.El) (Fin.append t vs) x (cs (Fin.castAdd n (cs l))) = t (cs l)
      rw [Fin.snoc_castSucc, Fin.append_left]
    constructor
    · rintro ⟨vs, hs, hφ, x, hx, hlast, hψ⟩
      rw [e1] at hlast
      refine ⟨Fin.snoc vs x, ?_, ?_, ?_⟩
      · intro k; refine Fin.lastCases ?_ (fun k => ?_) k
        · simpa using hx
        · rw [Fin.snoc_castSucc]; exact hs k
      · intro k; refine Fin.lastCases ?_ (fun k => ?_) k
        · simpa using hlast
        · rw [Fin.snoc_castSucc]; exact hφ k
      · rw [Formula.append_snoc]; exact hψ
    · rintro ⟨vs, hs, hφ, hψ⟩
      refine ⟨Fin.init vs, fun k => hs (cs k), fun k => hφ (cs k), vs (Fin.last n), hs (Fin.last n),
        ?_, ?_⟩
      · rw [e1]; exact hφ (Fin.last n)
      · rw [← Formula.append_snoc, Fin.snoc_init_self]; exact hψ

/-- The clause layout `(v̄, w)` read inside `(η, w, v̄)`. -/
theorem clausePos_env {m n : ℕ} (η : Env T m) (w : T.El) (vs : Fin n → T.El) :
    (fun i => Fin.append (Fin.snoc (α := fun _ => T.El) η w) vs (clausePos m n i)) =
      Fin.snoc (α := fun _ => T.El) vs w := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [clausePos]
  · simp [clausePos]

/-- The value relation of a primitive application whose arguments have the
declared sorts: values of the arguments, and the clause at `(v̄, w)`. -/
theorem Val_prim' {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args : Fin n → Term)
    (hg : ∀ k, (args k).cls Γ = c.argSort k) (η : Env T m) (w : T.El) :
    Val T Γ (.prim c args) η w ↔
      w.1 = c.level ∧ ∃ vs : Fin n → T.El, (∀ k, Val T Γ (args k) η (vs k)) ∧
        c.clauseF.Sat T.toStr (Fin.snoc (α := fun _ => T.El) vs w) := by
  have e : Val T Γ (.prim c args) η w ↔
      w.1 = c.level ∧ (eval Γ (.prim c args)).Sat T.toStr (Fin.snoc (α := fun _ => T.El) η w) :=
    Iff.rfl
  rw [e, eval, dif_pos hg]
  unfold primF
  rw [Sat_existsVals]
  simp only [Formula.sat_rename, Fin.init_snoc, id_eq, clausePos_env]
  refine and_congr Iff.rfl (exists_congr fun vs => ?_)
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun k => ⟨(h1 k).trans (hg k).symm, h2 k⟩, h3⟩
  · rintro ⟨h12, h3⟩
    exact ⟨fun k => (h12 k).1.trans (hg k), fun k => (h12 k).2, h3⟩

/-- No value when an argument has the wrong sort. -/
theorem not_Val_prim {m : ℕ} (Γ : Ctx m) {n : ℕ} (c : Prim n) (args : Fin n → Term)
    (η : Env T m) (w : T.El) (hg : ¬ ∀ k, (args k).cls Γ = c.argSort k) :
    ¬ Val T Γ (.prim c args) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval, dif_neg hg]

/-- The clause of a primitive at sorted values. -/
def PrimRel {n : ℕ} (c : Prim n) (vs : (k : Fin n) → T.U (c.argSort k)) (w : T.U c.level) : Prop :=
  c.clauseF.Sat T.toStr (Fin.snoc (α := fun _ => T.El) (fun k => T.inj (vs k)) (T.inj w))

/-- `Val_prim'` with sorted values. -/
theorem Val_prim {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args : Fin n → Term)
    (hg : ∀ k, (args k).cls Γ = c.argSort k) (η : Env T m) (w : T.U c.level) :
    Val T Γ (.prim c args) η (T.inj w) ↔
      ∃ vs : (k : Fin n) → T.U (c.argSort k), (∀ k, Val T Γ (args k) η (T.inj (vs k))) ∧
        PrimRel T c vs w := by
  rw [Val_prim' T c args hg]
  simp only [true_and]
  constructor
  · rintro ⟨vs, h1, h2⟩
    have hs : ∀ k, (vs k).1 = c.argSort k := fun k => (h1 k).sort.trans (hg k)
    refine ⟨fun k => Sorted.toSort T.U (vs k) (hs k), fun k => ?_, ?_⟩
    · simp only [Sorted.inj_toSort]; exact h1 k
    · unfold PrimRel
      simp only [Sorted.inj_toSort]
      exact h2
  · rintro ⟨vs, h1, h2⟩
    exact ⟨fun k => T.inj (vs k), h1, h2⟩

end SolidLean.Calc
