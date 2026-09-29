module

public import Solid.Calc.Typing

/-!
# Insertion and substitution on contexts and environments

The syntactic operations `shift` and `subst` act on terms written for a
context; here are the matching operations on contexts (and, later, on
environments): inserting `e` binders at position `p` (shifting the tail),
and removing the variable at position `p` by substituting a term for it in
the tail.  The lemmas relate these to extension by one binder at the end,
which is what the inductive cases of the semantic weakening and substitution
lemmas need.
-/

@[expose] public section

namespace SolidLean.Calc

open Term

namespace Ctx

/-- The prefix of length `p` of a context. -/
def prefix_ {p k : ℕ} (Γ : Ctx (p + k)) : Ctx p := fun l => Γ (Fin.castAdd k l)

/-- Insertion of `e` binders at position `p`, shifting the tail. -/
def insert (p e : ℕ) {e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) : Ctx (p + e + e') :=
  fun l =>
    if h1 : l.1 < p then Γ ⟨l.1, by omega⟩
    else if h2 : l.1 < p + e then Δ ⟨l.1 - p, by omega⟩
    else ((shift p e (Γ ⟨l.1 - e, by omega⟩).1), (Γ ⟨l.1 - e, by omega⟩).2)

theorem insert_lt {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) (l : Fin (p + e + e'))
    (h : l.1 < p) : insert p e Γ Δ l = Γ ⟨l.1, by omega⟩ := by
  simp [insert, h]

theorem insert_mid {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) (l : Fin (p + e + e'))
    (h1 : ¬ l.1 < p) (h2 : l.1 < p + e) : insert p e Γ Δ l = Δ ⟨l.1 - p, by omega⟩ := by
  simp [insert, h1, h2]

theorem insert_ge {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) (l : Fin (p + e + e'))
    (h2 : ¬ l.1 < p + e) :
    insert p e Γ Δ l = ((shift p e (Γ ⟨l.1 - e, by omega⟩).1), (Γ ⟨l.1 - e, by omega⟩).2) := by
  have h1 : ¬ l.1 < p := by omega
  simp [insert, h1, h2]

/-- Insertion commutes with extension at the end. -/
theorem insert_snoc {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) (B : Term) (l : ℕ) :
    (insert p e Γ Δ).snoc (shift p e B) l = insert p e (e' := e' + 1) (Γ.snoc B l) Δ := by
  funext x
  refine Fin.lastCases ?_ (fun x => ?_) x
  · rw [snoc, Fin.snoc_last, insert_ge _ _ _ (by simp <;> omega)]
    simp only [snoc]
    rw [show (⟨(Fin.last (p + e + e')).1 - e, _⟩ : Fin (p + e' + 1)) = Fin.last (p + e') from
      Fin.ext (by simp <;> omega), Fin.snoc_last]
  · rw [snoc, Fin.snoc_castSucc]
    by_cases h1 : x.1 < p
    · rw [insert_lt _ _ _ h1, insert_lt _ _ _ (by simpa using h1)]
      simp only [snoc]
      rw [show (⟨(Fin.castSucc x).1, _⟩ : Fin (p + e' + 1)) = Fin.castSucc ⟨x.1, by omega⟩ from
        Fin.ext rfl, Fin.snoc_castSucc]
    · by_cases h2 : x.1 < p + e
      · rw [insert_mid _ _ _ h1 h2, insert_mid _ _ _ (by simpa using h1) (by simpa using h2)]
        rfl
      · rw [insert_ge _ _ _ h2, insert_ge _ _ _ (by simpa using h2)]
        simp only [snoc]
        rw [show (⟨(Fin.castSucc x).1 - e, _⟩ : Fin (p + e' + 1)) =
          Fin.castSucc ⟨x.1 - e, by omega⟩ from Fin.ext rfl, Fin.snoc_castSucc]

theorem lev_insert_lt {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) {x : ℕ} (h : x < p) :
    (insert p e Γ Δ).lev x = Γ.lev x := by
  simp only [lev]
  rw [dif_pos (by omega), dif_pos (by omega), insert_lt _ _ _ h]

theorem lev_insert_ge {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) {x : ℕ} (h : p ≤ x) :
    (insert p e Γ Δ).lev (x + e) = Γ.lev x := by
  simp only [lev]
  by_cases hx : x < p + e'
  · rw [dif_pos (by omega), dif_pos hx, insert_ge _ _ _ (by simp <;> omega)]
    simp
  · rw [dif_neg (by omega), dif_neg hx]

/-- The classifier is invariant under shifting into an inserted context. -/
theorem cls_shift_insert {p e e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ) (t : Term) :
    (shift p e t).cls (insert p e Γ Δ) = t.cls Γ :=
  Term.cls_shift Γ (insert p e Γ Δ) p e (fun _ h => lev_insert_lt Γ Δ h)
    (fun _ h => lev_insert_ge Γ Δ h) t

/-- Substitution of `a` for the variable at position `p`, in the tail. -/
def sub (p : ℕ) (a : Term) {d : ℕ} (Γ : Ctx (p + 1 + d)) : Ctx (p + d) :=
  fun l =>
    if h1 : l.1 < p then Γ ⟨l.1, by omega⟩
    else (Term.subst p a (l.1 - p) (Γ ⟨l.1 + 1, by omega⟩).1, (Γ ⟨l.1 + 1, by omega⟩).2)

theorem sub_lt {p d : ℕ} (a : Term) (Γ : Ctx (p + 1 + d)) (l : Fin (p + d)) (h : l.1 < p) :
    sub p a Γ l = Γ ⟨l.1, by omega⟩ := by
  simp [sub, h]

theorem sub_ge {p d : ℕ} (a : Term) (Γ : Ctx (p + 1 + d)) (l : Fin (p + d)) (h : ¬ l.1 < p) :
    sub p a Γ l = (Term.subst p a (l.1 - p) (Γ ⟨l.1 + 1, by omega⟩).1, (Γ ⟨l.1 + 1, by omega⟩).2) := by
  simp [sub, h]

/-- Substitution commutes with extension at the end. -/
theorem sub_snoc {p d : ℕ} (a : Term) (Γ : Ctx (p + 1 + d)) (B : Term) (l : ℕ) :
    (sub p a Γ).snoc (Term.subst p a d B) l = sub p a (d := d + 1) (Γ.snoc B l) := by
  funext x
  refine Fin.lastCases ?_ (fun x => ?_) x
  · rw [snoc, Fin.snoc_last, sub_ge _ _ _ (by simp <;> omega)]
    simp only [snoc]
    rw [show (⟨(Fin.last (p + d)).1 + 1, _⟩ : Fin (p + 1 + d + 1)) = Fin.last (p + 1 + d) from
      Fin.ext (by simp <;> omega), Fin.snoc_last]
    simp
  · rw [snoc, Fin.snoc_castSucc]
    by_cases h1 : x.1 < p
    · rw [sub_lt _ _ _ h1, sub_lt _ _ _ (by simpa using h1)]
      simp only [snoc]
      rw [show (⟨(Fin.castSucc x).1, _⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨x.1, by omega⟩ from
        Fin.ext rfl, Fin.snoc_castSucc]
    · rw [sub_ge _ _ _ h1, sub_ge _ _ _ (by simpa using h1)]
      simp only [snoc]
      rw [show (⟨(Fin.castSucc x).1 + 1, _⟩ : Fin (p + 1 + d + 1)) =
        Fin.castSucc ⟨x.1 + 1, by omega⟩ from Fin.ext rfl, Fin.snoc_castSucc]
      rfl

theorem lev_sub_lt {p d : ℕ} (a : Term) (Γ : Ctx (p + 1 + d)) {x : ℕ} (h : x < p) :
    (sub p a Γ).lev x = Γ.lev x := by
  simp only [lev]
  rw [dif_pos (by omega), dif_pos (by omega), sub_lt _ _ _ h]

theorem lev_sub_gt {p d : ℕ} (a : Term) (Γ : Ctx (p + 1 + d)) {x : ℕ} (h : p < x) :
    (sub p a Γ).lev (x - 1) = Γ.lev x := by
  simp only [lev]
  by_cases hx : x < p + 1 + d
  · rw [dif_pos (by omega), dif_pos hx, sub_ge _ _ _ (by simp <;> omega)]
    simp only
    congr 2
    exact Fin.ext (by simp <;> omega)
  · rw [dif_neg (by omega), dif_neg hx]

end Ctx

end SolidLean.Calc
