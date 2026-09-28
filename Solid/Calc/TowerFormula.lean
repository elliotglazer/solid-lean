import Solid.Gen.Clauses

/-!
# Formulas of the tower signature: atoms, lifts, and set-theoretic notions

A small toolkit for writing clauses: the atoms of `TowerSig` with their sort
obligations, iterated lifts `j^{d}` between sorts, and the set-theoretic
notions used by the evaluator (Kuratowski pairs, function application, the
typing membership `j_r(x) ∈ A`).  Each comes with a satisfaction lemma
reading it in a tower.
-/

universe u

namespace SolidLean.Solid

open Classical

/-- Formulas of the tower signature. -/
abbrev TF (k : ℕ) (s : Fin k → ℕ) := Formula TowerSig k s

namespace TF

variable {k : ℕ} {s : Fin k → ℕ}

/-! ### Atoms -/

/-- `x_i ∈ x_j`, in sort `n`. -/
def memF (n : ℕ) (i j : Fin k) (hi : s i = n) (hj : s j = n) : TF k s :=
  .rel (.memZ n) ![i, j] (Fin.forall_fin_two.2 ⟨hi, hj⟩)

/-- `x_j = j_n(x_i)`. -/
def liftZF (n : ℕ) (i j : Fin k) (hi : s i = n) (hj : s j = n + 1) : TF k s :=
  .rel (.liftZ n) ![i, j] (Fin.forall_fin_two.2 ⟨hi, hj⟩)

/-- `x_i = κ_n`. -/
def bndF (n : ℕ) (i : Fin k) (hi : s i = n + 1) : TF k s :=
  .rel (.bnd n) ![i] (Fin.forall_fin_one.2 hi)

variable (T : MemTower.{u})

theorem Sat_memF {n : ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n} {t : Fin k → T.El}
    (x y : T.U n) (hx : t i = T.inj x) (hy : t j = T.inj y) :
    (memF n i j hi hj).Sat T.toStr t ↔ T.mem x y := by
  show ![t i, t j] ∈ T.memRel n ↔ _
  constructor
  · rintro ⟨x', y', hx', hy', h⟩
    have hx'' : t i = T.inj x' := hx'
    have hy'' : t j = T.inj y' := hy'
    rw [hx] at hx''
    rw [hy] at hy''
    rw [Sorted.inj_injective T.U hx'', Sorted.inj_injective T.U hy'']
    exact h
  · intro h
    exact ⟨x, y, hx, hy, h⟩

theorem Sat_liftZF {n : ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n + 1} {t : Fin k → T.El}
    (x : T.U n) (hx : t i = T.inj x) :
    (liftZF n i j hi hj).Sat T.toStr t ↔ t j = T.inj (T.j n x) := by
  show ![t i, t j] ∈ T.jRel n ↔ _
  constructor
  · rintro ⟨x', hx', hy'⟩
    have hx'' : t i = T.inj x' := hx'
    have hy'' : t j = T.inj (T.j n x') := hy'
    rw [hx] at hx''
    rw [← Sorted.inj_injective T.U hx''] at hy''
    exact hy''
  · intro h
    exact ⟨x, hx, h⟩

theorem Sat_bndF {n : ℕ} {i : Fin k} {hi : s i = n + 1} {t : Fin k → T.El} :
    (bndF n i hi).Sat T.toStr t ↔ t i = T.inj (T.κ n) := Iff.rfl

/-! ### Iterated lifts -/

end TF

namespace MemTower

variable (T : MemTower.{u})

/-- The iterated transition map `j^{d} : U s → U (s + d)`. -/
def liftN (n : ℕ) : (d : ℕ) → T.U n → T.U (n + d)
  | 0, x => x
  | d + 1, x => T.j (n + d) (liftN n d x)

@[simp] theorem liftN_zero (n : ℕ) (x : T.U n) : T.liftN n 0 x = x := rfl

theorem liftN_succ (n d : ℕ) (x : T.U n) : T.liftN n (d + 1) x = T.j (n + d) (T.liftN n d x) := rfl

theorem liftN_eq_liftLE (n : ℕ) : ∀ (d : ℕ) (x : T.U n), T.liftN n d x = T.liftLE (Nat.le_add_right n d) x
  | 0, x => by rw [liftN_zero, MemTower.liftLE_self]
  | d + 1, x => by
    rw [liftN_succ, liftN_eq_liftLE n d x]
    exact (T.liftLE_succ (Nat.le_add_right n d) x).symm

/-- The lift by `d` steps, as an element of the union, is the lift to any sort
equal to `n + d`. -/
theorem inj_liftN {n n' d : ℕ} (h : n ≤ n') (hd : n + d = n') (x : T.U n) :
    T.inj (T.liftN n d x) = T.inj (T.liftLE h x) := by
  subst hd
  rw [liftN_eq_liftLE]

end MemTower

namespace TF

variable {k : ℕ} {s : Fin k → ℕ}

/-- `x_j = j^{d}(x_i)`, from sort `n` to sort `n + d`. -/
def liftNF (n : ℕ) : (d : ℕ) → {k : ℕ} → {s : Fin k → ℕ} → (i j : Fin k) → s i = n → s j = n + d →
    TF k s
  | 0, _, _, i, j, hi, hj => .eq i j (hi.trans hj.symm)
  | d + 1, _, s, i, j, hi, hj =>
    -- ∃ y : n + d, y = j^d(x_i) ∧ x_j = j(y)
    .ex (n + d) (Formula.and
      (liftNF n d (Fin.castSucc i) (Fin.last _) (by simp [hi]) (by simp))
      (liftZF (n + d) (Fin.last _) (Fin.castSucc j) (by simp) (by rw [Fin.snoc_castSucc, hj]; rfl)))

variable (T : MemTower.{u})

theorem Sat_liftNF (n : ℕ) : ∀ (d : ℕ) {k : ℕ} {s : Fin k → ℕ} (i j : Fin k) (hi : s i = n)
    (hj : s j = n + d) (t : Fin k → T.El) (x : T.U n) (hx : t i = T.inj x),
    (liftNF n d i j hi hj).Sat T.toStr t ↔ t j = T.inj (T.liftN n d x)
  | 0, _, _, i, j, _, _, t, x, hx => by
    show t i = t j ↔ t j = T.inj x
    rw [hx]; exact eq_comm
  | d + 1, _, _, i, j, hi, hj, t, x, hx => by
    show (∃ y : T.El, y.1 = n + d ∧ _) ↔ _
    constructor
    · rintro ⟨y, hy, h⟩
      rw [Formula.Sat_and] at h
      obtain ⟨h1, h2⟩ := h
      have h1' := (Sat_liftNF n d (Fin.castSucc i) (Fin.last _) _ _ (Fin.snoc t y) x
        (by simp [hx])).1 h1
      simp only [Fin.snoc_last] at h1'
      have h2' := (Sat_liftZF T (t := Fin.snoc t y) (T.liftN n d x) (by simp [h1'])).1 h2
      rw [MemTower.liftN_succ]
      simp only [Fin.snoc_castSucc] at h2'
      exact h2'
    · intro h
      refine ⟨T.inj (T.liftN n d x), rfl, ?_⟩
      rw [Formula.Sat_and]
      constructor
      · refine (Sat_liftNF n d (Fin.castSucc i) (Fin.last _) _ _ _ x (by simp [hx])).2 ?_
        simp
      · refine (Sat_liftZF T (t := Fin.snoc t (T.inj (T.liftN n d x))) (T.liftN n d x)
          (by simp)).2 ?_
        rw [MemTower.liftN_succ] at h
        simp only [Fin.snoc_castSucc]
        exact h

end TF

end SolidLean.Solid
