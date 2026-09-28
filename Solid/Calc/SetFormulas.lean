import Solid.Calc.TowerFormula
import Solid.SetTheory

/-!
# Set-theoretic notions as formulas of the tower signature

Pairs, ordered pairs, functions and application, written once as formulas in
a fixed sort `n` over a small context, to be instantiated at any positions by
`TF.at`.  Each has a satisfaction lemma reading it through the definitions of
`Solid.SetTheory` on the sort `T.sortStr n`.
-/

universe u

namespace SolidLean.Solid

open Classical

theorem forall_fin_three {p : Fin 3 → Prop} : (∀ i, p i) ↔ p 0 ∧ p 1 ∧ p 2 :=
  Fin.forall_fin_succ.trans (and_congr_right fun _ => Fin.forall_fin_two)

namespace TF

variable {k : ℕ} {s : Fin k → ℕ}

/-- Instantiate a formula in the constant sort `n` at positions `v`. -/
abbrev at_ {a n : ℕ} (φ : TF a (fun _ => n)) (v : Fin a → Fin k) (hv : ∀ i, s (v i) = n) : TF k s :=
  Formula.rename v hv φ

theorem Sat_at {T : MemTower.{u}} {a n : ℕ} (φ : TF a (fun _ => n)) (v : Fin a → Fin k)
    (hv : ∀ i, s (v i) = n) (t : Fin k → T.El) :
    (at_ φ v hv).Sat T.toStr t ↔ φ.Sat T.toStr (fun i => t (v i)) :=
  Formula.sat_rename (M := T.toStr) v hv φ t

/-- A sort assignment with constant value `n`. -/
def IsConst {a : ℕ} (s : Fin a → ℕ) (n : ℕ) : Prop := ∀ i, s i = n

theorem IsConst.const (a n : ℕ) : IsConst (fun _ : Fin a => n) n := fun _ => rfl

theorem IsConst.snoc {a : ℕ} {s : Fin a → ℕ} {n : ℕ} (h : IsConst s n) :
    IsConst (Fin.snoc (α := fun _ => ℕ) s n) n := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · simp [h i]

/-- Existential quantification in a constant sort. -/
def exC {a : ℕ} {s : Fin a → ℕ} (n : ℕ) (φ : TF (a + 1) (Fin.snoc s n)) : TF a s := .ex n φ

/-- Universal quantification in a constant sort. -/
def allC {a : ℕ} {s : Fin a → ℕ} (n : ℕ) (φ : TF (a + 1) (Fin.snoc s n)) : TF a s :=
  Formula.all n φ

variable (T : MemTower.{u})

theorem snoc_inj {a n : ℕ} (x : Fin a → T.U n) (z : T.U n) :
    Fin.snoc (α := fun _ => T.El) (fun i => T.inj (x i)) (T.inj z) =
      fun i => T.inj (Fin.snoc (α := fun _ => T.U n) x z i) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

theorem Sat_exC {a : ℕ} {s : Fin a → ℕ} {n : ℕ} (φ : TF (a + 1) (Fin.snoc s n)) (x : Fin a → T.U n) :
    (exC n φ).Sat T.toStr (fun i => T.inj (x i)) ↔
      ∃ z : T.U n, φ.Sat T.toStr (fun i => T.inj (Fin.snoc (α := fun _ => T.U n) x z i)) := by
  show (∃ z : T.El, z.1 = n ∧ _) ↔ _
  constructor
  · rintro ⟨z, hz, h⟩
    refine ⟨Sorted.toSort T.U z hz, ?_⟩
    rw [← snoc_inj]
    have e : T.inj (Sorted.toSort T.U z hz) = z := Sorted.inj_toSort T.U z hz
    rw [e]
    exact h
  · rintro ⟨z, h⟩
    refine ⟨T.inj z, rfl, ?_⟩
    rw [snoc_inj]
    exact h

theorem Sat_allC {a : ℕ} {s : Fin a → ℕ} {n : ℕ} (φ : TF (a + 1) (Fin.snoc s n)) (x : Fin a → T.U n) :
    (allC n φ).Sat T.toStr (fun i => T.inj (x i)) ↔
      ∀ z : T.U n, φ.Sat T.toStr (fun i => T.inj (Fin.snoc (α := fun _ => T.U n) x z i)) := by
  unfold allC
  rw [Formula.Sat_all]
  constructor
  · intro h z
    have := h (T.inj z) rfl
    rw [snoc_inj] at this
    exact this
  · intro h z hz
    have := h (Sorted.toSort T.U z hz)
    rw [← snoc_inj] at this
    have e : T.inj (Sorted.toSort T.U z hz) = z := Sorted.inj_toSort T.U z hz
    rw [e] at this
    exact this

/-! ### Notions in a constant sort -/

section Const

variable {a : ℕ} {s : Fin a → ℕ} {n : ℕ}

local notation "cs" => Fin.castSucc

/-- `x_i ∈ x_j`. -/
def memC (hs : IsConst s n) (i j : Fin a) : TF a s := memF n i j (hs i) (hs j)

/-- `x_i = x_j`. -/
def eqC (hs : IsConst s n) (i j : Fin a) : TF a s := .eq i j ((hs i).trans (hs j).symm)

/-- `x_p = {x_i, x_j}`. -/
def pairC (hs : IsConst s n) (i j p : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (cs p))
    (Formula.or (eqC hs.snoc (Fin.last a) (cs i)) (eqC hs.snoc (Fin.last a) (cs j))))

/-- `x_p = {x_i}`. -/
def singC (hs : IsConst s n) (i p : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (cs p)) (eqC hs.snoc (Fin.last a) (cs i)))

/-- `x_p = ⟨x_i, x_j⟩` (Kuratowski). -/
def ordPairC (hs : IsConst s n) (i j p : Fin a) : TF a s :=
  exC n (exC n (Formula.and (singC hs.snoc.snoc (cs (cs i)) (cs (Fin.last a)))
    (Formula.and (pairC hs.snoc.snoc (cs (cs i)) (cs (cs j)) (Fin.last (a + 1)))
      (pairC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)) (cs (cs p))))))

/-- `x_y = x_f(x_x)`: `⟨x_x, x_y⟩ ∈ x_f`. -/
def funAppC (hs : IsConst s n) (f x y : Fin a) : TF a s :=
  exC n (Formula.and (ordPairC hs.snoc (cs x) (cs y) (Fin.last a)) (memC hs.snoc (Fin.last a) (cs f)))

/-- `x_r` is a set of ordered pairs. -/
def isRelC (hs : IsConst s n) (r : Fin a) : TF a s :=
  allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs r))
    (exC n (exC n (ordPairC hs.snoc.snoc.snoc (cs (Fin.last (a + 1))) (Fin.last (a + 2))
      (cs (cs (Fin.last a)))))))

/-- `x_f` is a function. -/
def isFunC (hs : IsConst s n) (f : Fin a) : TF a s :=
  Formula.and (isRelC hs f)
    (allC n (allC n (allC n (Formula.imp
      (funAppC hs.snoc.snoc.snoc (cs (cs (cs f))) (cs (cs (Fin.last a))) (cs (Fin.last (a + 1))))
      (Formula.imp
        (funAppC hs.snoc.snoc.snoc (cs (cs (cs f))) (cs (cs (Fin.last a))) (Fin.last (a + 2)))
        (eqC hs.snoc.snoc.snoc (cs (Fin.last (a + 1))) (Fin.last (a + 2))))))))

/-- `x_x ∈ dom x_f`. -/
def inDomC (hs : IsConst s n) (f x : Fin a) : TF a s :=
  exC n (funAppC hs.snoc (cs f) (cs x) (Fin.last a))

variable (T : MemTower.{u})

theorem Sat_memC (hs : IsConst s n) (i j : Fin a) (x : Fin a → T.U n) :
    (memC hs i j).Sat T.toStr (fun l => T.inj (x l)) ↔ T.mem (x i) (x j) :=
  Sat_memF T (x i) (x j) rfl rfl

theorem Sat_eqC (hs : IsConst s n) (i j : Fin a) (x : Fin a → T.U n) :
    (eqC hs i j).Sat T.toStr (fun l => T.inj (x l)) ↔ x i = x j := by
  show T.inj (x i) = T.inj (x j) ↔ _
  exact ⟨fun h => Sorted.inj_injective T.U h, fun h => by rw [h]⟩

theorem Sat_pairC (hs : IsConst s n) (i j p : Fin a) (x : Fin a → T.U n) :
    (pairC hs i j p).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsPairSet (x i) (x j) (x p) := by
  unfold pairC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Formula.Sat_or, Sat_eqC, Fin.snoc_last,
    Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_singC (hs : IsConst s n) (i p : Fin a) (x : Fin a → T.U n) :
    (singC hs i p).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsSingleton (x i) (x p) := by
  unfold singC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Sat_eqC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_ordPairC (hs : IsConst s n) (i j p : Fin a) (x : Fin a → T.U n) :
    (ordPairC hs i j p).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).IsOrdPair (x i) (x j) (x p) := by
  unfold ordPairC
  simp only [Sat_exC, Formula.Sat_and, Sat_singC, Sat_pairC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_funAppC (hs : IsConst s n) (f y z : Fin a) (x : Fin a → T.U n) :
    (funAppC hs f y z).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).FunApp (x f) (x y) (x z) := by
  unfold funAppC
  simp only [Sat_exC, Formula.Sat_and, Sat_ordPairC, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  show (∃ q, (T.sortStr n).IsOrdPair (x y) (x z) q ∧ T.mem q (x f)) ↔ ∃ q, T.mem q (x f) ∧ _
  exact ⟨fun ⟨q, h1, h2⟩ => ⟨q, h2, h1⟩, fun ⟨q, h1, h2⟩ => ⟨q, h2, h1⟩⟩

theorem Sat_isRelC (hs : IsConst s n) (r : Fin a) (x : Fin a → T.U n) :
    (isRelC hs r).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsRelation (x r) := by
  unfold isRelC
  simp only [Sat_allC, Formula.Sat_imp, Sat_memC, Sat_exC, Sat_ordPairC, Fin.snoc_last,
    Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_isFunC (hs : IsConst s n) (f : Fin a) (x : Fin a → T.U n) :
    (isFunC hs f).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsFunction (x f) := by
  unfold isFunC
  simp only [Formula.Sat_and, Sat_isRelC, Sat_allC, Formula.Sat_imp, Sat_funAppC, Sat_eqC,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_inDomC (hs : IsConst s n) (f y : Fin a) (x : Fin a → T.U n) :
    (inDomC hs f y).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).InDom (x f) (x y) := by
  unfold inDomC
  simp only [Sat_exC, Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

end Const

/-! ### Emptiness and truth values (constant sort) -/

section Const2

variable {a : ℕ} {s : Fin a → ℕ} {n : ℕ}

local notation "cs" => Fin.castSucc

/-- `x_i = ∅`. -/
def isEmptyC (hs : IsConst s n) (i : Fin a) : TF a s :=
  allC n (Formula.not (memC hs.snoc (Fin.last a) (cs i)))

/-- `x_i = {∅}`: the truth value "true". -/
def isTrueC (hs : IsConst s n) (i : Fin a) : TF a s :=
  exC n (Formula.and (isEmptyC hs.snoc (Fin.last a)) (singC hs.snoc (Fin.last a) (cs i)))

/-- `x_i` is the truth value of `ψ`: `{∅}` if `ψ`, `∅` otherwise. -/
def tvC (hs : IsConst s n) (i : Fin a) (ψ : TF a s) : TF a s :=
  Formula.and (Formula.imp ψ (isTrueC hs i)) (Formula.imp (Formula.not ψ) (isEmptyC hs i))

variable (T : MemTower.{u})

theorem Sat_isEmptyC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (isEmptyC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsEmptySet (x i) := by
  unfold isEmptyC
  simp only [Sat_allC, Formula.Sat_not, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_isTrueC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (isTrueC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔
      ∃ e, (T.sortStr n).IsEmptySet e ∧ (T.sortStr n).IsSingleton e (x i) := by
  unfold isTrueC
  simp only [Sat_exC, Formula.Sat_and, Sat_isEmptyC, Sat_singC, Fin.snoc_last, Fin.snoc_castSucc]

theorem Sat_tvC (hs : IsConst s n) (i : Fin a) (ψ : TF a s) (x : Fin a → T.U n) :
    (tvC hs i ψ).Sat T.toStr (fun l => T.inj (x l)) ↔
      (ψ.Sat T.toStr (fun l => T.inj (x l)) →
          ∃ e, (T.sortStr n).IsEmptySet e ∧ (T.sortStr n).IsSingleton e (x i)) ∧
      (¬ ψ.Sat T.toStr (fun l => T.inj (x l)) → (T.sortStr n).IsEmptySet (x i)) := by
  unfold tvC
  simp only [Formula.Sat_and, Formula.Sat_imp, Formula.Sat_not, Sat_isTrueC, Sat_isEmptyC]

end Const2

/-! ### Mixed sorts: recasting, typing membership, universes -/

/-- Recast a formula along a pointwise equality of sort assignments. -/
abbrev recast {k : ℕ} {s s' : Fin k → ℕ} (h : ∀ i, s' i = s i) (φ : TF k s) : TF k s' :=
  Formula.rename id h φ

theorem Sat_recast {T : MemTower.{u}} {k : ℕ} {s s' : Fin k → ℕ} (h : ∀ i, s' i = s i) (φ : TF k s)
    (t : Fin k → T.El) : (recast h φ).Sat T.toStr t ↔ φ.Sat T.toStr t :=
  Formula.sat_rename (M := T.toStr) id h φ t

/-- `j_r(x_i) ∈ x_j`, for `x_i` of sort `r` and `x_j` of sort `r + 1`: the
membership of an element in its type. -/
def tmemF {k : ℕ} {s : Fin k → ℕ} (r : ℕ) (i j : Fin k) (hi : s i = r) (hj : s j = r + 1) :
    TF k s :=
  .ex (r + 1) (Formula.and (liftZF r (Fin.castSucc i) (Fin.last k) (by simp [hi]) (by simp))
    (memF (r + 1) (Fin.last k) (Fin.castSucc j) (by simp) (by simp [hj])))

theorem Sat_tmemF (T : MemTower.{u}) {k : ℕ} {s : Fin k → ℕ} {r : ℕ} {i j : Fin k} {hi : s i = r}
    {hj : s j = r + 1} {t : Fin k → T.El} (x : T.U r) (A : T.U (r + 1)) (hx : t i = T.inj x)
    (hA : t j = T.inj A) : (tmemF r i j hi hj).Sat T.toStr t ↔ T.mem (T.j r x) A := by
  show (∃ y : T.El, y.1 = r + 1 ∧ _) ↔ _
  constructor
  · rintro ⟨y, hy, h⟩
    rw [Formula.Sat_and] at h
    obtain ⟨h1, h2⟩ := h
    have h1' := (Sat_liftZF T (t := Fin.snoc t y) x (by simp [hx])).1 h1
    simp only [Fin.snoc_last] at h1'
    have h2' := (Sat_memF T (t := Fin.snoc t y) (T.j r x) A (by simp [h1']) (by simp [hA])).1 h2
    exact h2'
  · intro h
    refine ⟨T.inj (T.j r x), rfl, ?_⟩
    rw [Formula.Sat_and]
    refine ⟨(Sat_liftZF T (t := Fin.snoc t _) x (by simp [hx])).2 (by simp), ?_⟩
    exact (Sat_memF T (t := Fin.snoc t _) (T.j r x) A (by simp) (by simp [hA])).2 h

end TF

end SolidLean.Solid
