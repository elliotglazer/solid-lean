module

public import Solid.Calc.Syntax
public import Solid.Calc.SetFormulas
public import Solid.Gen.Definable
public import Solid.Calc.SnocLits
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

/-!
# The evaluator clauses of the primitives (draft 2, §3.4 and §4.3)

Each primitive `c : Prim n` has a clause `clauseF c`, a formula in the
`n + 1` variables `(v̄, w)`: the values of its arguments and the value of the
application, of sorts `c.sorts`.  The generic evaluator clause `primF`
(used by `eval`) quantifies the argument values, requires each to satisfy the
argument's evaluator formula, and applies the clause.
-/

@[expose] public section

universe u

namespace SolidLean.Solid.TF

variable {k : ℕ} {s : Fin k → ℕ}

/-- `x_p` has sort `n` (as a formula: `∃ y : n, y = x_p`).  The position atoms
below are guarded by it, so that their satisfaction determines the sort of
the entries they mention (which makes their readings unconditional). -/
def sortF (n : ℕ) (p : Fin k) (hp : s p = n) : TF k s :=
  .ex n (.eq (Fin.last k) (Fin.castSucc p) (by simp [hp]))

theorem Sat_sortF (T : MemTower.{u}) (n : ℕ) (p : Fin k) (hp : s p = n) (t : Fin k → T.El) :
    (sortF n p hp).Sat T.toStr t ↔ (t p).1 = n := by
  show (∃ y : T.El, y.1 = n ∧ (Fin.snoc (α := fun _ => T.El) t y) (Fin.last k) =
    (Fin.snoc (α := fun _ => T.El) t y) (Fin.castSucc p)) ↔ _
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · rintro ⟨y, hy, rfl⟩; exact hy
  · intro h; exact ⟨t p, h, rfl⟩

/-- `x_j = j^{m-n}(x_i)`: the lift from sort `n` to sort `m ≥ n`. -/
def liftLEF (n m : ℕ) (h : n ≤ m) (i j : Fin k) (hi : s i = n) (hj : s j = m) : TF k s :=
  Formula.and (sortF n i hi) (liftNF n (m - n) i j hi (by rw [hj]; omega))

/-- `x_s = x_x ∪ {x_x}`. -/
def isSuccC {a n : ℕ} {s : Fin a → ℕ} (hs : IsConst s n) (x t : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (Fin.castSucc t))
    (Formula.or (memC hs.snoc (Fin.last a) (Fin.castSucc x))
      (eqC hs.snoc (Fin.last a) (Fin.castSucc x))))

/-- `x_i` is inductive: contains the empty set and is closed under successor. -/
def inductiveC {a n : ℕ} {s : Fin a → ℕ} (hs : IsConst s n) (i : Fin a) : TF a s :=
  Formula.and
    (exC n (Formula.and (isEmptyC hs.snoc (Fin.last a)) (memC hs.snoc (Fin.last a) (Fin.castSucc i))))
    (allC n (Formula.imp (memC hs.snoc (Fin.last a) (Fin.castSucc i))
      (exC n (Formula.and (isSuccC hs.snoc.snoc (Fin.castSucc (Fin.last a)) (Fin.last (a + 1)))
        (memC hs.snoc.snoc (Fin.last (a + 1)) (Fin.castSucc (Fin.castSucc i)))))))

/-- `x_i = ω`: the least inductive set. -/
def isOmegaC {a n : ℕ} {s : Fin a → ℕ} (hs : IsConst s n) (i : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (Fin.castSucc i))
    (allC n (Formula.imp (inductiveC hs.snoc.snoc (Fin.last (a + 1)))
      (memC hs.snoc.snoc (Fin.castSucc (Fin.last a)) (Fin.last (a + 1))))))

/-! ### Atoms at positions, in a mixed-sort layout -/

/-- `x_p = ∅` (sort `n`). -/
def emptyF (n : ℕ) (p : Fin k) (hp : s p = n) : TF k s :=
  Formula.and (sortF n p hp) (at_ (isEmptyC (IsConst.const 1 n) 0) ![p] (Fin.forall_fin_one.2 hp))

/-- `x_p = {∅}` (sort `n`). -/
def trueF (n : ℕ) (p : Fin k) (hp : s p = n) : TF k s :=
  Formula.and (sortF n p hp) (at_ (isTrueC (IsConst.const 1 n) 0) ![p] (Fin.forall_fin_one.2 hp))

/-- `x_r = ⟨x_p, x_q⟩` (sort `n`). -/
def ordPairF (n : ℕ) (p q r : Fin k) (hp : s p = n) (hq : s q = n) (hr : s r = n) : TF k s :=
  Formula.and (sortF n p hp) (Formula.and (sortF n q hq) (Formula.and (sortF n r hr)
    (at_ (ordPairC (IsConst.const 3 n) 0 1 2) ![p, q, r] (forall_fin_three.2 ⟨hp, hq, hr⟩))))

/-- `x_f(x_x) = x_y` (sort `n`). -/
def funAppF (n : ℕ) (f x y : Fin k) (hf : s f = n) (hx : s x = n) (hy : s y = n) : TF k s :=
  Formula.and (sortF n f hf) (Formula.and (sortF n x hx) (Formula.and (sortF n y hy)
    (at_ (funAppC (IsConst.const 3 n) 0 1 2) ![f, x, y] (forall_fin_three.2 ⟨hf, hx, hy⟩))))

/-- `x_f` is a function (sort `n`). -/
def isFunF (n : ℕ) (f : Fin k) (hf : s f = n) : TF k s :=
  Formula.and (sortF n f hf) (at_ (isFunC (IsConst.const 1 n) 0) ![f] (Fin.forall_fin_one.2 hf))

/-- `x_x ∈ dom x_f` (sort `n`). -/
def inDomF (n : ℕ) (f x : Fin k) (hf : s f = n) (hx : s x = n) : TF k s :=
  Formula.and (sortF n f hf) (Formula.and (sortF n x hx)
    (at_ (inDomC (IsConst.const 2 n) 0 1) ![f, x] (Fin.forall_fin_two.2 ⟨hf, hx⟩)))

/-- `x_t = x_x ∪ {x_x}` (sort `n`). -/
def isSuccF (n : ℕ) (x t : Fin k) (hx : s x = n) (ht : s t = n) : TF k s :=
  Formula.and (sortF n x hx) (Formula.and (sortF n t ht)
    (at_ (isSuccC (IsConst.const 2 n) 0 1) ![x, t] (Fin.forall_fin_two.2 ⟨hx, ht⟩)))

/-- `x_p = ω` (sort `n`). -/
def isOmegaF (n : ℕ) (p : Fin k) (hp : s p = n) : TF k s :=
  Formula.and (sortF n p hp) (at_ (isOmegaC (IsConst.const 1 n) 0) ![p] (Fin.forall_fin_one.2 hp))

variable (T : MemTower.{u})

theorem Sat_liftLEF (n m : ℕ) (h : n ≤ m) (i j : Fin k) (hi : s i = n) (hj : s j = m)
    (t : Fin k → T.El) (x : T.U n) (hx : t i = T.inj x) :
    (liftLEF n m h i j hi hj).Sat T.toStr t ↔ t j = T.inj (T.liftLE h x) := by
  unfold liftLEF
  rw [Formula.Sat_and, Sat_sortF, Sat_liftNF T n (m - n) i j hi _ t x hx, T.inj_liftN h (by omega), hx]
  simp

end SolidLean.Solid.TF

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

namespace Prim

/-- The sorts of the layout `(v̄, w)` of the clause of a primitive. -/
def sorts : {n : ℕ} → Prim n → Fin (n + 1) → ℕ
  | _, .false_ => ![1]
  | _, .falseElim j => ![j + 1, 0, j]
  | _, .eq i => ![i + 1, i, i, 1]
  | _, .refl i => ![i + 1, i, 0]
  | _, .eqRec i j => ![i + 1, i, max i (j + 1), j, i, 0, j]
  | _, .sigma i j => ![i + 1, max i (j + 1), max i j + 1]
  | _, .pair i j => ![i + 1, max i (j + 1), i, j, max i j]
  | _, .fst i j => ![i + 1, max i (j + 1), max i j, i]
  | _, .snd i j => ![i + 1, max i (j + 1), max i j, j]
  | _, .lift i d => ![i + 1, i + d + 1]
  | _, .up i d => ![i + 1, i, i + d]
  | _, .down i d => ![i + 1, i + d, i]
  | _, .trunc i => ![i + 1, 1]
  | _, .truncMk i => ![i + 1, i, 0]
  | _, .truncRec i => ![i + 1, 1, 0, 0, 0]
  | _, .propext => ![1, 1, 0, 0, 0]
  | _, .dne => ![1, 0, 0]
  | _, .uchoice i => ![i + 1, 0, 0, i]
  | _, .choice i j => ![i + 1, max i (j + 1), 0, 0]
  | _, .sum i j => ![i + 1, j + 1, max i j + 1]
  | _, .inl i j => ![i + 1, j + 1, i, max i j]
  | _, .inr i j => ![i + 1, j + 1, j, max i j]
  | _, .sumRec i j k => ![i + 1, j + 1, max (max i j) (k + 1), max i k, max j k, max i j, k]
  | _, .nat => ![2]
  | _, .zero => ![1]
  | _, .succ => ![1, 1]
  | _, .natRec j => ![j + 1, j, max 1 (max j j), 1, j]
  | _, .quot i => ![i + 1, max i (max i 1), i + 1]
  | _, .quotMk i => ![i + 1, max i (max i 1), i, i]
  | _, .quotLift i j => ![i + 1, max i (max i 1), j + 1, max i j, 0, i, j]
  | _, .quotSound i => ![i + 1, max i (max i 1), i, i, 0, 0]
  | _, .quotInd i => ![i + 1, max i (max i 1), max i 1, 0, i, 0]

theorem sorts_eq {n : ℕ} (c : Prim n) :
    c.sorts = Fin.snoc (α := fun _ => ℕ) c.argSort c.level := by
  funext k
  refine Fin.lastCases ?_ (fun k => ?_) k
  · rw [Fin.snoc_last]
    cases c <;> simp [sorts, level] <;> omega
  · rw [Fin.snoc_castSucc]
    cases c <;> (try exact k.elim0) <;> fin_cases k <;> rfl

end Prim

namespace TFx

open SolidLean.Solid.TF

variable {k : ℕ} {s : Fin k → ℕ}

local notation "cs" => Fin.castSucc

/-- `⟨x_y, x_z⟩ ∈ x_E` (sort `i`). -/
def pairMemF (i : ℕ) (y z E : Fin k) (hy : s y = i) (hz : s z = i) (hE : s E = i) : TF k s :=
  .ex i (Formula.and (ordPairF i (cs y) (cs z) (Fin.last k) (by exact id (by simp [hy])) (by exact id (by simp [hz])) (by exact id (by simp)))
    (memF i (Fin.last k) (cs E) (by exact id (by simp)) (by exact id (by simp [hE]))))

/-- `x_E ⊆ A × A`, for `x_A` of sort `i + 1` (elements of sort `i` via `j`). -/
def subsetPairsF (i : ℕ) (E A : Fin k) (hE : s E = i) (hA : s A = i + 1) : TF k s :=
  Formula.and (sortF i E hE) (Formula.and (sortF (i + 1) A hA) (Formula.all i (Formula.imp (memF i (Fin.last k) (cs E) (by exact id (by simp)) (by exact id (by simp [hE])))
    (.ex i (.ex i (Formula.and
      (tmemF i (cs (Fin.last (k + 1))) (cs (cs (cs A))) (by exact id (by simp)) (by exact id (by simp [hA])))
      (Formula.and
        (tmemF i (Fin.last (k + 2)) (cs (cs (cs A))) (by exact id (by simp)) (by exact id (by simp [hA])))
        (ordPairF i (cs (Fin.last (k + 1))) (Fin.last (k + 2)) (cs (cs (Fin.last k)))
          (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp))))))))))

/-- `x_E` is reflexive on `A`. -/
def reflF (i : ℕ) (E A : Fin k) (hE : s E = i) (hA : s A = i + 1) : TF k s :=
  Formula.and (sortF i E hE) (Formula.and (sortF (i + 1) A hA)
    (Formula.all i (Formula.imp (tmemF i (Fin.last k) (cs A) (by exact id (by simp)) (by exact id (by simp [hA])))
      (pairMemF i (Fin.last k) (Fin.last k) (cs E) (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE]))))))

/-- `x_E` is symmetric. -/
def symmF (i : ℕ) (E : Fin k) (hE : s E = i) : TF k s :=
  Formula.and (sortF i E hE) (Formula.all i (Formula.all i (Formula.imp
    (pairMemF i (cs (Fin.last k)) (Fin.last (k + 1)) (cs (cs E)) (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE])))
    (pairMemF i (Fin.last (k + 1)) (cs (Fin.last k)) (cs (cs E)) (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE]))))))

/-- `x_E` is transitive. -/
def transF (i : ℕ) (E : Fin k) (hE : s E = i) : TF k s :=
  Formula.and (sortF i E hE) (Formula.all i (Formula.all i (Formula.all i (Formula.imp
    (pairMemF i (cs (cs (Fin.last k))) (cs (Fin.last (k + 1))) (cs (cs (cs E)))
      (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE])))
    (Formula.imp
      (pairMemF i (cs (Fin.last (k + 1))) (Fin.last (k + 2)) (cs (cs (cs E)))
        (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE])))
      (pairMemF i (cs (cs (Fin.last k))) (Fin.last (k + 2)) (cs (cs (cs E)))
        (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE]))))))))

/-- `R y z` holds: `x_R(lift x_y) = lift g` with `g(lift x_z) = lift {∅}`, for `x_R` the value
of a relation `A → A → U_0` (a function of sort `max i (max i 1)` into lifts of functions
of sort `max i 1` into lifts of truth values).
Layout: `… | ly t g lz u v`. -/
def relHoldsF (i : ℕ) (R y z : Fin k) (hR : s R = max i (max i 1)) (hy : s y = i) (hz : s z = i) :
    TF k s :=
  .ex (max i (max i 1)) (Formula.and
    (liftLEF i (max i (max i 1)) (le_max_left _ _) (cs y) (Fin.last k) (by exact id (by simp [hy]))
      (by exact id (by simp)))
    (.ex (max i (max i 1)) (Formula.and
      (funAppF (max i (max i 1)) (cs (cs R)) (cs (Fin.last k)) (Fin.last (k + 1))
        (by exact id (by simp [hR])) (by exact id (by simp)) (by exact id (by simp)))
      (.ex (max i 1) (Formula.and
        (liftLEF (max i 1) (max i (max i 1)) (le_max_right _ _) (Fin.last (k + 2)) (cs (Fin.last (k + 1)))
          (by exact id (by simp)) (by exact id (by simp)))
        (.ex (max i 1) (Formula.and
          (liftLEF i (max i 1) (le_max_left _ _) (cs (cs (cs (cs z)))) (Fin.last (k + 3))
            (by exact id (by simp [hz])) (by exact id (by simp)))
          (.ex (max i 1) (Formula.and
            (funAppF (max i 1) (cs (cs (Fin.last (k + 2)))) (cs (Fin.last (k + 3))) (Fin.last (k + 4))
              (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp)))
            (.ex 1 (Formula.and
              (liftLEF 1 (max i 1) (le_max_right _ _) (Fin.last (k + 5)) (cs (Fin.last (k + 4)))
                (by exact id (by simp)) (by exact id (by simp)))
              (trueF 1 (Fin.last (k + 5)) (by exact id (by simp))))))))))))))

/-- `x_E` contains `R` on `A`. -/
def containsF (i : ℕ) (E A R : Fin k) (hE : s E = i) (hA : s A = i + 1) (hR : s R = max i (max i 1)) :
    TF k s :=
  Formula.and (sortF i E hE) (Formula.and (sortF (i + 1) A hA) (Formula.and (sortF (max i (max i 1)) R hR)
    (Formula.all i (Formula.all i (Formula.imp
    (tmemF i (cs (Fin.last k)) (cs (cs A)) (by exact id (by simp)) (by exact id (by simp [hA])))
    (Formula.imp (tmemF i (Fin.last (k + 1)) (cs (cs A)) (by exact id (by simp)) (by exact id (by simp [hA])))
      (Formula.imp
        (relHoldsF i (cs (cs R)) (cs (Fin.last k)) (Fin.last (k + 1)) (by exact id (by simp [hR])) (by exact id (by simp)) (by exact id (by simp)))
        (pairMemF i (cs (Fin.last k)) (Fin.last (k + 1)) (cs (cs E)) (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [hE]))))))))))

/-- `x_E` is an equivalence relation on `A` containing `R`. -/
def equivRelF (i : ℕ) (E A R : Fin k) (hE : s E = i) (hA : s A = i + 1) (hR : s R = max i (max i 1)) :
    TF k s :=
  Formula.and (subsetPairsF i E A hE hA) (Formula.and (reflF i E A hE hA)
    (Formula.and (symmF i E hE) (Formula.and (transF i E hE) (containsF i E A R hE hA hR))))

/-- `x_a ~ x_x`: the pair lies in every equivalence relation on `A` containing `R`. -/
def equivF (i : ℕ) (A R a x : Fin k) (hA : s A = i + 1) (hR : s R = max i (max i 1)) (ha : s a = i)
    (hx : s x = i) : TF k s :=
  Formula.and (sortF (i + 1) A hA) (Formula.and (sortF (max i (max i 1)) R hR) (Formula.and (sortF i a ha)
    (Formula.and (sortF i x hx) (Formula.all i (Formula.imp
      (equivRelF i (Fin.last k) (cs A) (cs R) (by exact id (by simp)) (by exact id (by simp [hA])) (by exact id (by simp [hR])))
      (pairMemF i (cs a) (cs x) (Fin.last k) (by exact id (by simp [ha])) (by exact id (by simp [hx])) (by exact id (by simp))))))))

end TFx

/-- `x_w` (of sort `n`) is the truth value of `ψ`. -/
def tvF {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (w : Fin k) (hw : s w = n) (ψ : TF k s) : TF k s :=
  Formula.and (sortF n w hw) (Formula.and
    (Formula.imp ψ (at_ (isTrueC (IsConst.const 1 n) 0) ![w] (Fin.forall_fin_one.2 hw)))
    (Formula.imp (Formula.not ψ) (at_ (isEmptyC (IsConst.const 1 n) 0) ![w] (Fin.forall_fin_one.2 hw))))

namespace Prim

open SolidLean.Solid.TF TFx

/-! #### Bodies of the set-forming clauses, over an arbitrary sort assignment

These are the parts of the clauses that Separation uses to build the sets. -/

/-- `q = ⟨lift a, lift b⟩` with `j a ∈ A`, `B(lift a) = lift vBa`, `j b ∈ vBa`
(layout `A B w p q | a u v vBa b u' v'`). -/
def sigmaBodyF (i j : ℕ) {s : Fin 5 → ℕ} (h0 : s 0 = i + 1) (h1 : s 1 = max i (j + 1))
    (h4 : s 4 = max i j) : TF 5 s :=
  .ex i (Formula.and (tmemF i 5 0 (by exact id (by simp)) (by exact id (by simp [h0])))
    (.ex (max i (j + 1)) (Formula.and (liftLEF i (max i (j + 1)) (le_max_left _ _) 5 6 (by exact id (by simp)) (by exact id (by simp)))
      (.ex (max i (j + 1)) (Formula.and (funAppF (max i (j + 1)) 1 6 7 (by exact id (by simp [h1])) (by exact id (by simp)) (by exact id (by simp)))
        (.ex (j + 1) (Formula.and (liftLEF (j + 1) (max i (j + 1)) (le_max_right _ _) 8 7 (by exact id (by simp)) (by exact id (by simp)))
          (.ex j (Formula.and (tmemF j 9 8 (by exact id (by simp)) (by exact id (by simp)))
            (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 5 10 (by exact id (by simp)) (by exact id (by simp)))
              (.ex (max i j) (Formula.and (liftLEF j (max i j) (le_max_right _ _) 9 11 (by exact id (by simp)) (by exact id (by simp)))
                (ordPairF (max i j) 10 11 4 (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [h4]))))))))))))))))

/-- `q = ⟨∅, lift a⟩` with `j a ∈ A`, or `q = ⟨{∅}, lift b⟩` with `j b ∈ B`
(layout `A B w p q | x u z`). -/
def sumBodyF (i j : ℕ) {s : Fin 5 → ℕ} (h0 : s 0 = i + 1) (h1 : s 1 = j + 1) (h4 : s 4 = max i j) :
    TF 5 s :=
  Formula.and (sortF (i + 1) 0 h0) (Formula.and (sortF (j + 1) 1 h1) (Formula.and (sortF (max i j) 4 h4)
  (Formula.or
    (.ex i (Formula.and (tmemF i 5 0 (by exact id (by simp)) (by exact id (by simp [h0])))
      (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 5 6 (by exact id (by simp)) (by exact id (by simp)))
        (.ex (max i j) (Formula.and (emptyF (max i j) 7 (by exact id (by simp)))
          (ordPairF (max i j) 7 6 4 (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [h4])))))))))
    (.ex j (Formula.and (tmemF j 5 1 (by exact id (by simp)) (by exact id (by simp [h1])))
      (.ex (max i j) (Formula.and (liftLEF j (max i j) (le_max_right _ _) 5 6 (by exact id (by simp)) (by exact id (by simp)))
        (.ex (max i j) (Formula.and (trueF (max i j) 7 (by exact id (by simp)))
          (ordPairF (max i j) 7 6 4 (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [h4]))))))))))))

/-- `x ∈ c ↔ (j x ∈ A ∧ a ~ x)`: `c` is the class of `a` (layout `A R a c | x`). -/
def classBodyF (i : ℕ) {s : Fin 4 → ℕ} (h0 : s 0 = i + 1) (h1 : s 1 = max i (max i 1)) (h2 : s 2 = i)
    (h3 : s 3 = i) : TF 4 s :=
  Formula.and (sortF (i + 1) 0 h0) (Formula.and (sortF (max i (max i 1)) 1 h1) (Formula.and (sortF i 2 h2)
    (Formula.and (sortF i 3 h3)
      (Formula.all i (Formula.iff (memF i 4 3 (by exact id (by simp)) (by exact id (by simp [h3])))
        (Formula.and (tmemF i 4 0 (by exact id (by simp)) (by exact id (by simp [h0])))
          (TFx.equivF i 0 1 2 4 (by exact id (by simp [h0])) (by exact id (by simp [h1])) (by exact id (by simp [h2])) (by exact id (by simp)))))))))

/-- `∃ a, j a ∈ A ∧ c is the class of a` (layout `A R w Q c | a`). -/
def quotBodyF (i : ℕ) {s : Fin 5 → ℕ} (h0 : s 0 = i + 1) (h1 : s 1 = max i (max i 1)) (h4 : s 4 = i) :
    TF 5 s :=
  .ex i (Formula.and (tmemF i 5 0 (by exact id (by simp)) (by exact id (by simp [h0])))
    (Formula.rename ![0, 1, 5, 4] (fun l => by fin_cases l <;> simp [h0, h1, h4])
      (classBodyF i (s := ![i + 1, max i (max i 1), i, i]) (by exact id rfl) (by exact id rfl) (by exact id rfl)
        (by exact id rfl))))

/-- `p = ⟨a, b⟩` with `f(lift a) = f(lift b)` (layout `A f p | a b u v`): the kernel of `f`. -/
def kernelBodyF (i j : ℕ) {s : Fin 3 → ℕ} (h1 : s 1 = max i j) (h2 : s 2 = i) : TF 3 s :=
  .ex i (.ex i (Formula.and (ordPairF i 3 4 2 (by exact id (by simp)) (by exact id (by simp)) (by exact id (by simp [h2])))
    (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 3 5 (by exact id (by simp)) (by exact id (by simp)))
      (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 4 6 (by exact id (by simp)) (by exact id (by simp)))
        (.ex (max i j) (Formula.and (funAppF (max i j) 1 5 7 (by exact id (by simp [h1])) (by exact id (by simp)) (by exact id (by simp)))
          (funAppF (max i j) 1 6 7 (by exact id (by simp [h1])) (by exact id (by simp)) (by exact id (by simp)))))))))))

/-- The clause of a primitive: a formula in the layout `(v̄, w)` of sorts `c.sorts`
(the arguments' values, then the value of the application). -/
def clauseF : {n : ℕ} → (c : Prim n) → TF (n + 1) c.sorts
  -- w = ∅ (the false truth value)
  | _, .false_ => emptyF 1 0 (by exact id rfl)
  -- w = ∅ (any fixed value; the premise is never satisfied)
  | _, .falseElim j => emptyF j 2 (by exact id rfl)
  -- w is the truth value of a = b
  | _, .eq i => tvF 1 3 (by exact id rfl) (.eq 1 2 (by exact id rfl))
  | _, .refl i => emptyF 0 2 (by exact id rfl)
  -- w = c
  | _, .eqRec i j => .eq 6 3 (by exact id rfl)
  -- w = j(p), p = {⟨lift a, lift b⟩ : j a ∈ A, b ∈ B(a)}     (layout A B w | p q a u v vBa b u' v')
  | _, .sigma i j =>
    .ex (max i j) (Formula.and (liftZF (max i j) 3 2 (by exact id rfl) (by exact id rfl))
      (Formula.all (max i j) (Formula.iff (memF (max i j) 4 3 (by exact id rfl) (by exact id rfl))
        (sigmaBodyF i j (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  -- w = ⟨lift a, lift b⟩     (layout A B a b w | u v)
  | _, .pair i j =>
    .ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 2 5 (by exact id rfl) (by exact id rfl))
      (.ex (max i j) (Formula.and (liftLEF j (max i j) (le_max_right _ _) 3 6 (by exact id rfl) (by exact id rfl))
        (ordPairF (max i j) 5 6 4 (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  -- s = ⟨lift w, v⟩     (layout A B s w | u v)
  | _, .fst i j =>
    .ex (max i j) (.ex (max i j) (Formula.and (ordPairF (max i j) 4 5 2 (by exact id rfl) (by exact id rfl) (by exact id rfl))
      (liftLEF i (max i j) (le_max_left _ _) 3 4 (by exact id rfl) (by exact id rfl))))
  -- s = ⟨u, lift w⟩
  | _, .snd i j =>
    .ex (max i j) (.ex (max i j) (Formula.and (ordPairF (max i j) 4 5 2 (by exact id rfl) (by exact id rfl) (by exact id rfl))
      (liftLEF j (max i j) (le_max_right _ _) 3 5 (by exact id rfl) (by exact id rfl))))
  -- w = lift A
  | _, .lift i d => liftLEF (i + 1) (i + d + 1) (by omega) 0 1 (by exact id rfl) (by exact id rfl)
  -- w = lift a
  | _, .up i d => liftLEF i (i + d) (by omega) 1 2 (by exact id rfl) (by exact id rfl)
  -- lift w = a
  | _, .down i d => liftLEF i (i + d) (by omega) 2 1 (by exact id rfl) (by exact id rfl)
  -- w is the truth value of "A is inhabited"     (layout A w | a)
  | _, .trunc i => tvF 1 1 (by exact id rfl) (.ex i (tmemF i 2 0 (by exact id rfl) (by exact id rfl)))
  | _, .truncMk i => emptyF 0 2 (by exact id rfl)
  | _, .truncRec i => emptyF 0 4 (by exact id rfl)
  | _, .propext => emptyF 0 4 (by exact id rfl)
  | _, .dne => emptyF 0 2 (by exact id rfl)
  -- j w ∈ A and w is the only element     (layout A h u w | w')
  | _, .uchoice i =>
    Formula.and (tmemF i 3 0 (by exact id rfl) (by exact id rfl))
      (Formula.all i (Formula.imp (tmemF i 4 0 (by exact id rfl) (by exact id rfl)) (.eq 4 3 (by exact id rfl))))
  | _, .choice i j => emptyF 0 3 (by exact id rfl)
  -- w = j(p), p = {⟨∅, lift a⟩ : j a ∈ A} ∪ {⟨{∅}, lift b⟩ : j b ∈ B}    (layout A B w | p q x u z)
  | _, .sum i j =>
    .ex (max i j) (Formula.and (liftZF (max i j) 3 2 (by exact id rfl) (by exact id rfl))
      (Formula.all (max i j) (Formula.iff (memF (max i j) 4 3 (by exact id rfl) (by exact id rfl))
        (sumBodyF i j (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  -- w = ⟨∅, lift a⟩     (layout A B a w | u z)
  | _, .inl i j =>
    .ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 2 4 (by exact id rfl) (by exact id rfl))
      (.ex (max i j) (Formula.and (emptyF (max i j) 5 (by exact id rfl)) (ordPairF (max i j) 5 4 3 (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  | _, .inr i j =>
    .ex (max i j) (Formula.and (liftLEF j (max i j) (le_max_right _ _) 2 4 (by exact id rfl) (by exact id rfl))
      (.ex (max i j) (Formula.and (trueF (max i j) 5 (by exact id rfl)) (ordPairF (max i j) 5 4 3 (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  -- (s = ⟨∅, lift a⟩ ∧ f(lift a) = lift w) ∨ (s = ⟨{∅}, lift b⟩ ∧ g(lift b) = lift w)
  --   (layout A B C f g s w | x u z u' v)
  | _, .sumRec i j k =>
    Formula.or
      (.ex i (.ex (max i j) (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 7 8 (by exact id rfl) (by exact id rfl))
        (Formula.and (emptyF (max i j) 9 (by exact id rfl)) (Formula.and (ordPairF (max i j) 9 8 5 (by exact id rfl) (by exact id rfl) (by exact id rfl))
          (.ex (max i k) (.ex (max i k) (Formula.and (liftLEF i (max i k) (le_max_left _ _) 7 10 (by exact id rfl) (by exact id rfl))
            (Formula.and (funAppF (max i k) 3 10 11 (by exact id rfl) (by exact id rfl) (by exact id rfl))
              (liftLEF k (max i k) (le_max_right _ _) 6 11 (by exact id rfl) (by exact id rfl))))))))))))
      (.ex j (.ex (max i j) (.ex (max i j) (Formula.and (liftLEF j (max i j) (le_max_right _ _) 7 8 (by exact id rfl) (by exact id rfl))
        (Formula.and (trueF (max i j) 9 (by exact id rfl)) (Formula.and (ordPairF (max i j) 9 8 5 (by exact id rfl) (by exact id rfl) (by exact id rfl))
          (.ex (max j k) (.ex (max j k) (Formula.and (liftLEF j (max j k) (le_max_left _ _) 7 10 (by exact id rfl) (by exact id rfl))
            (Formula.and (funAppF (max j k) 4 10 11 (by exact id rfl) (by exact id rfl) (by exact id rfl))
              (liftLEF k (max j k) (le_max_right _ _) 6 11 (by exact id rfl) (by exact id rfl))))))))))))
  -- w = j(ω)     (layout w | o)
  | _, .nat => .ex 1 (Formula.and (isOmegaF 1 1 (by exact id rfl)) (liftZF 1 1 0 (by exact id rfl) (by exact id rfl)))
  | _, .zero => emptyF 1 0 (by exact id rfl)
  | _, .succ => isSuccF 1 0 1 (by exact id rfl) (by exact id rfl)
  -- ∃ d = n ∪ {n}, ∃ F : function on lift d with F(∅) = z, F(lift (k+1)) = g(F(lift k)) where
  --   s(lift k) = lift g, and w = F(lift n)     (layout C z s n w | d D F …)
  | _, .natRec j =>
    if hj : 1 ≤ j then
    .ex 1 (Formula.and (isSuccF 1 3 5 (by exact id rfl) (by exact id rfl))
      (.ex j (Formula.and (liftLEF 1 j hj 5 6 (by exact id rfl) (by exact id rfl))
        (.ex j (Formula.and (isFunF j 7 (by exact id rfl))
          (Formula.and (Formula.all j (Formula.iff (inDomF j 7 8 (by exact id rfl) (by exact id rfl))
              (memF j 8 6 (by exact id rfl) (by exact id rfl))))
            (Formula.and (.ex j (Formula.and (emptyF j 8 (by exact id rfl))
                (funAppF j 7 8 1 (by exact id rfl) (by exact id rfl) (by exact id rfl))))
              (Formula.and
                -- ∀ k ∈ n, ∀ k1 = k ∪ {k}, ∀ lk = lift k, ∀ lk1 = lift k1, ∀ fk = F(lk),
                --   ∀ lk' = lift k (sort of s), ∀ sk = s(lk'), ∀ g with lift g = sk, ∀ lfk = lift fk,
                --   ∀ r' = g(lfk), ∀ r with lift r = r', F(lk1) = r
                --   (positions 8 9 10 11 12 13 14 15 16 17 18)
                (Formula.all 1 (Formula.imp (memF 1 8 3 (by exact id rfl) (by exact id rfl))
                  (Formula.all 1 (Formula.imp (isSuccF 1 8 9 (by exact id rfl) (by exact id rfl))
                    (Formula.all j (Formula.imp (liftLEF 1 j hj 8 10 (by exact id rfl) (by exact id rfl))
                      (Formula.all j (Formula.imp (liftLEF 1 j hj 9 11 (by exact id rfl) (by exact id rfl))
                        (Formula.all j (Formula.imp (funAppF j 7 10 12 (by exact id rfl) (by exact id rfl)
                            (by exact id rfl))
                          (Formula.all (max 1 (max j j)) (Formula.imp (liftLEF 1 (max 1 (max j j))
                              (le_max_left _ _) 8 13 (by exact id rfl) (by exact id rfl))
                            (Formula.all (max 1 (max j j)) (Formula.imp (funAppF (max 1 (max j j)) 2 13 14
                                (by exact id rfl) (by exact id rfl) (by exact id rfl))
                              (Formula.all (max j j) (Formula.imp (liftLEF (max j j) (max 1 (max j j))
                                  (le_max_right _ _) 15 14 (by exact id rfl) (by exact id rfl))
                                (Formula.all (max j j) (Formula.imp (liftLEF j (max j j) (le_max_left _ _)
                                    12 16 (by exact id rfl) (by exact id rfl))
                                  (Formula.all (max j j) (Formula.imp (funAppF (max j j) 15 16 17
                                      (by exact id rfl) (by exact id rfl) (by exact id rfl))
                                    (Formula.all j (Formula.imp (liftLEF j (max j j) (le_max_right _ _)
                                        18 17 (by exact id rfl) (by exact id rfl))
                                      (funAppF j 7 11 18 (by exact id rfl) (by exact id rfl)
                                        (by exact id rfl))))))))))))))))))))))))
                (.ex j (Formula.and (liftLEF 1 j hj 3 8 (by exact id rfl) (by exact id rfl))
                  (funAppF j 7 8 4 (by exact id rfl) (by exact id rfl) (by exact id rfl))))))))))))
    else .false_
  -- w = j(Q), Q = the set of ~-classes     (layout A R w | Q c a)
  | _, .quot i =>
    .ex i (Formula.and (liftZF i 3 2 (by exact id rfl) (by exact id rfl))
      (Formula.all i (Formula.iff (memF i 4 3 (by exact id rfl) (by exact id rfl))
        (quotBodyF i (by exact id rfl) (by exact id rfl) (by exact id rfl)))))
  -- w = the class of a     (layout A R a w | x)
  | _, .quotMk i =>
    classBodyF i (by exact id rfl) (by exact id rfl) (by exact id rfl) (by exact id rfl)
  -- ∃ a ∈ q, f(lift a) = lift w     (layout A R C f h q w | a u v)
  | _, .quotLift i j =>
    .ex i (Formula.and (memF i 7 5 (by exact id rfl) (by exact id rfl))
      (.ex (max i j) (Formula.and (liftLEF i (max i j) (le_max_left _ _) 7 8 (by exact id rfl) (by exact id rfl))
        (.ex (max i j) (Formula.and (funAppF (max i j) 3 8 9 (by exact id rfl) (by exact id rfl) (by exact id rfl))
          (liftLEF j (max i j) (le_max_right _ _) 6 9 (by exact id rfl) (by exact id rfl)))))))
  | _, .quotSound i => emptyF 0 5 (by exact id rfl)
  | _, .quotInd i => emptyF 0 5 (by exact id rfl)

end Prim

/-! ### The generic evaluator clause of a primitive application -/

local notation "cs" => Fin.castSucc

/-- Place the context variables by `f` and one more variable at `p`. -/
def place1 {m k : ℕ} (f : Fin m → Fin k) (p : Fin k) : Fin (m + 1) → Fin k :=
  Fin.snoc (α := fun _ => Fin k) f p

/-- Place the context variables by `f` and two more variables at `p`, `q`. -/
def place2 {m k : ℕ} (f : Fin m → Fin k) (p q : Fin k) : Fin (m + 2) → Fin k :=
  Fin.snoc (α := fun _ => Fin k) (Fin.snoc (α := fun _ => Fin k) f p) q

@[simp] theorem place1_last {m k : ℕ} (f : Fin m → Fin k) (p : Fin k) :
    place1 f p (Fin.last m) = p := by simp [place1]
@[simp] theorem place1_cs {m k : ℕ} (f : Fin m → Fin k) (p : Fin k) (l : Fin m) :
    place1 f p (cs l) = f l := by simp [place1]
@[simp] theorem place2_last {m k : ℕ} (f : Fin m → Fin k) (p q : Fin k) :
    place2 f p q (Fin.last (m + 1)) = q := by simp [place2]
@[simp] theorem place2_cs_last {m k : ℕ} (f : Fin m → Fin k) (p q : Fin k) :
    place2 f p q (cs (Fin.last m)) = p := by simp [place2]
@[simp] theorem place2_cs_cs {m k : ℕ} (f : Fin m → Fin k) (p q : Fin k) (l : Fin m) :
    place2 f p q (cs (cs l)) = f l := by simp [place2]


section Generic

variable {m : ℕ} (lev : Fin m → ℕ)

/-- The environment positions in the layout `(η, w, v̄)`. -/
def embEnv (m n : ℕ) : Fin m → Fin (m + 1 + n) := fun l => Fin.castAdd n (Fin.castSucc l)

/-- `∃ v_0 … v_{n-1}. ⋀_k φ_k(η, v_k) ∧ ψ(η, w, v̄)`, for `φ_k` in the layout `(η, v_k)`
and `ψ` in the layout `(η, w, v̄)`. -/
def existsVals (c : ℕ) : (n : ℕ) → (sorts : Fin n → ℕ) →
    ((k : Fin n) → TF (m + 1) (Fin.snoc lev (sorts k))) →
    TF (m + 1 + n) (Fin.append (Fin.snoc lev c) sorts) → TF (m + 1) (Fin.snoc lev c)
  | 0, sorts, _, ψ =>
    recast (fun i => by
      have : Fin.append (Fin.snoc (α := fun _ => ℕ) lev c) sorts = Fin.snoc (α := fun _ => ℕ) lev c := by
        funext i; exact Fin.append_left _ _ ⟨i.1, by omega⟩
      rw [this]) ψ
  | n + 1, sorts, φ, ψ =>
    existsVals c n (Fin.init sorts) (fun k => φ (Fin.castSucc k))
      (.ex (sorts (Fin.last n)) (recast (fun i => by
          rw [← Formula.append_snoc (Fin.snoc lev c) (Fin.init sorts) (sorts (Fin.last n)),
            Fin.snoc_init_self])
        (Formula.and
          (Formula.rename (place1 (embEnv m (n + 1)) (Fin.last (m + 1 + n))) (fun i => by
            refine Fin.lastCases ?_ (fun l => ?_) i
            · simp only [place1, Fin.snoc_last]
              rw [show Fin.last (m + 1 + n) = Fin.natAdd (m + 1) (Fin.last n) from Fin.ext rfl,
                Fin.append_right]
            · simp only [place1, Fin.snoc_castSucc, embEnv]
              rw [Fin.append_left, Fin.snoc_castSucc]) (φ (Fin.last n)))
          ψ)))

/-- The positions of the clause layout `(v̄, w)` inside `(η, w, v̄)`. -/
def clausePos (m n : ℕ) : Fin (n + 1) → Fin (m + 1 + n) :=
  Fin.snoc (α := fun _ => Fin (m + 1 + n)) (fun k => Fin.natAdd (m + 1) k) (Fin.castAdd n (Fin.last m))

theorem clausePos_sorts {n : ℕ} (c : Prim n) (i : Fin (n + 1)) :
    Fin.append (Fin.snoc (α := fun _ => ℕ) lev c.level) c.argSort (clausePos m n i) = c.sorts i := by
  rw [Prim.sorts_eq]
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [clausePos]
  · simp [clausePos]

/-- The evaluator clause of `prim c args`: the arguments' formulas `φ` (in the
layout `(η, v_k)`) and the clause of `c`. -/
def primF {n : ℕ} (c : Prim n) (φ : (k : Fin n) → TF (m + 1) (Fin.snoc lev (c.argSort k))) :
    TF (m + 1) (Fin.snoc lev c.level) :=
  existsVals lev c.level n c.argSort φ
    (Formula.rename (clausePos m n) (clausePos_sorts lev c) c.clauseF)

end Generic

end SolidLean.Calc
