module

public import Solid.Calc.Contexts
public import Solid.Calc.Semantics

/-!
# Insertion and removal on environments; the value relation on variables

Environment operations matching `Ctx.insert` and `Ctx.sub`, their
commutation with extension at the end, and the reading of the value
relation on variables without a well-sortedness assumption.
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid

variable (T : MemTower.{u})

namespace Env

/-- The prefix of length `p` of an environment. -/
def prefix_ {p k : ℕ} (η : Env T (p + k)) : Env T p := fun l => η (Fin.castAdd k l)

/-- Insertion of `e` values at position `p`. -/
def insert (p e : ℕ) {e' : ℕ} (η : Env T (p + e')) (ξ : Fin e → T.El) : Env T (p + e + e') :=
  fun l =>
    if h1 : l.1 < p then η ⟨l.1, by omega⟩
    else if h2 : l.1 < p + e then ξ ⟨l.1 - p, by omega⟩
    else η ⟨l.1 - e, by omega⟩

theorem insert_lt {p e e' : ℕ} (η : Env T (p + e')) (ξ : Fin e → T.El) (l : Fin (p + e + e'))
    (h : l.1 < p) : insert T p e η ξ l = η ⟨l.1, by omega⟩ := by
  simp [insert, h]

theorem insert_mid {p e e' : ℕ} (η : Env T (p + e')) (ξ : Fin e → T.El) (l : Fin (p + e + e'))
    (h1 : ¬ l.1 < p) (h2 : l.1 < p + e) : insert T p e η ξ l = ξ ⟨l.1 - p, by omega⟩ := by
  simp [insert, h1, h2]

theorem insert_ge {p e e' : ℕ} (η : Env T (p + e')) (ξ : Fin e → T.El) (l : Fin (p + e + e'))
    (h2 : ¬ l.1 < p + e) : insert T p e η ξ l = η ⟨l.1 - e, by omega⟩ := by
  have h1 : ¬ l.1 < p := by omega
  simp [insert, h1, h2]

theorem insert_snoc {p e e' : ℕ} (η : Env T (p + e')) (ξ : Fin e → T.El) (x : T.El) :
    Fin.snoc (α := fun _ => T.El) (insert T p e η ξ) x =
      insert T p e (e' := e' + 1) (Fin.snoc (α := fun _ => T.El) η x) ξ := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · rw [Fin.snoc_last, insert_ge _ _ _ _ (by simp <;> omega)]
    rw [show (⟨(Fin.last (p + e + e')).1 - e, _⟩ : Fin (p + e' + 1)) = Fin.last (p + e') from
      Fin.ext (by simp <;> omega)]
    simp
  · rw [Fin.snoc_castSucc]
    by_cases h1 : l.1 < p
    · rw [insert_lt _ _ _ _ h1, insert_lt _ _ _ _ (by simpa using h1)]
      rw [show (⟨(Fin.castSucc l).1, _⟩ : Fin (p + e' + 1)) = Fin.castSucc ⟨l.1, by omega⟩ from
        Fin.ext rfl, Fin.snoc_castSucc]
    · by_cases h2 : l.1 < p + e
      · rw [insert_mid _ _ _ _ h1 h2, insert_mid _ _ _ _ (by simpa using h1) (by simpa using h2)]
        rfl
      · rw [insert_ge _ _ _ _ h2, insert_ge _ _ _ _ (by simpa using h2)]
        rw [show (⟨(Fin.castSucc l).1 - e, _⟩ : Fin (p + e' + 1)) =
          Fin.castSucc ⟨l.1 - e, by omega⟩ from Fin.ext rfl, Fin.snoc_castSucc]

/-- Removal of the value at position `p`. -/
def remove (p : ℕ) {d : ℕ} (η : Env T (p + 1 + d)) : Env T (p + d) :=
  fun l => if h1 : l.1 < p then η ⟨l.1, by omega⟩ else η ⟨l.1 + 1, by omega⟩

theorem remove_lt {p d : ℕ} (η : Env T (p + 1 + d)) (l : Fin (p + d)) (h : l.1 < p) :
    remove T p η l = η ⟨l.1, by omega⟩ := by
  simp [remove, h]

theorem remove_ge {p d : ℕ} (η : Env T (p + 1 + d)) (l : Fin (p + d)) (h : ¬ l.1 < p) :
    remove T p η l = η ⟨l.1 + 1, by omega⟩ := by
  simp [remove, h]

theorem remove_snoc {p d : ℕ} (η : Env T (p + 1 + d)) (x : T.El) :
    Fin.snoc (α := fun _ => T.El) (remove T p η) x =
      remove T p (d := d + 1) (Fin.snoc (α := fun _ => T.El) η x) := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · rw [Fin.snoc_last, remove_ge _ _ _ (by simp <;> omega)]
    rw [show (⟨(Fin.last (p + d)).1 + 1, _⟩ : Fin (p + 1 + d + 1)) = Fin.last (p + 1 + d) from
      Fin.ext (by simp <;> omega)]
    simp
  · rw [Fin.snoc_castSucc]
    by_cases h1 : l.1 < p
    · rw [remove_lt _ _ _ h1, remove_lt _ _ _ (by simpa using h1)]
      rw [show (⟨(Fin.castSucc l).1, _⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨l.1, by omega⟩ from
        Fin.ext rfl, Fin.snoc_castSucc]
    · rw [remove_ge _ _ _ h1, remove_ge _ _ _ (by simpa using h1)]
      rw [show (⟨(Fin.castSucc l).1 + 1, _⟩ : Fin (p + 1 + d + 1)) =
        Fin.castSucc ⟨l.1 + 1, by omega⟩ from Fin.ext rfl, Fin.snoc_castSucc]

end Env

/-! ### Variables, without a well-sortedness assumption -/

theorem Val_var' {m : ℕ} (Γ : Ctx m) (η : Env T m) (x : ℕ) (w : T.El) :
    Val T Γ (.var x) η w ↔ ∃ h : x < m, w = η ⟨x, h⟩ ∧ w.1 = Γ.lev x := by
  unfold Val eval
  by_cases h : x < m
  · rw [dif_pos h]
    simp only [Formula.Sat_eq]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, Term.cls_var]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h, h2.symm, h1⟩
    · rintro ⟨h', hw, h1⟩
      subst hw
      exact ⟨h1, rfl⟩
  · rw [dif_neg h]
    simp only [Formula.Sat_false, and_false, false_iff, not_exists]
    intro h'; exact absurd h' h

/-! ### Failing guards -/

theorem not_Val_of_false {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) (w : T.El)
    (h : HEq (eval Γ t) (Formula.false_ (Sig := TowerSig) (s := Fin.snoc Γ.levels (t.cls Γ)))) :
    ¬ Val T Γ t η w := by
  intro hv
  have := hv.2
  rw [Formula.Sat_heq rfl h] at this
  exact this

theorem not_Val_pi_prop {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) (w : T.El)
    (h : ¬ (A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = 1)) : ¬ Val T Γ (.pi .prop i j A B) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval]
  by_cases hA : A.cls Γ = i + 1
  · rw [dif_pos hA]
    have hB : ¬ B.cls (Γ.snoc A i) = 1 := fun hB => h ⟨hA, hB⟩
    rw [dif_neg hB]
  · rw [dif_neg hA]

theorem not_Val_pi_data {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) (w : T.El)
    (h : ¬ (A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = j + 1)) : ¬ Val T Γ (.pi .data i j A B) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval]
  by_cases hA : A.cls Γ = i + 1
  · rw [dif_pos hA]
    have hB : ¬ B.cls (Γ.snoc A i) = j + 1 := fun hB => h ⟨hA, hB⟩
    rw [dif_neg hB]
  · rw [dif_neg hA]

theorem not_Val_lam_data {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A b : Term) (η : Env T m) (w : T.El)
    (h : ¬ (A.cls Γ = i + 1 ∧ b.cls (Γ.snoc A i) = j)) : ¬ Val T Γ (.lam .data i j A b) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval]
  by_cases hA : A.cls Γ = i + 1
  · rw [dif_pos hA]
    have hb : ¬ b.cls (Γ.snoc A i) = j := fun hb => h ⟨hA, hb⟩
    rw [dif_neg hb]
  · rw [dif_neg hA]

theorem not_Val_app_data {m : ℕ} (Γ : Ctx m) (j : ℕ) (f a : Term) (η : Env T m) (w : T.El)
    (h : ¬ (j ≤ f.cls Γ ∧ a.cls Γ ≤ f.cls Γ)) : ¬ Val T Γ (.app .data j f a) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval]
  by_cases hj : j ≤ f.cls Γ
  · rw [dif_pos hj]
    have ha : ¬ a.cls Γ ≤ f.cls Γ := fun ha => h ⟨hj, ha⟩
    rw [dif_neg ha]
  · rw [dif_neg hj]

theorem not_Val_let {m : ℕ} (Γ : Ctx m) (j : ℕ) (A v b : Term) (η : Env T m) (w : T.El)
    (h : ¬ b.cls (Γ.snoc A (v.cls Γ)) = j) : ¬ Val T Γ (.letE j A v b) η w := by
  refine not_Val_of_false T _ _ _ _ ?_
  rw [eval, dif_neg h]

end SolidLean.Calc
