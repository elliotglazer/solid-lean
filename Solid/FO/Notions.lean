import Solid.Calc.SetFormulas

/-!
# The internal set-theoretic notions as formulas

Constant-sort tower formulas for every notion of `SetTheory.lean` that the
axioms of `H` mention (subsets, unions, power sets, successors, ordinals,
rank attempts, cardinals, inaccessibility), each with a satisfaction lemma
reading it as the corresponding Lean-level notion in a sort of a tower.
This is what lets the axioms of `H` be written down as sentences
(`FO/Axioms.lean`).

The formulas mirror the definitions in `SetTheory.lean` connective by
connective, so each satisfaction lemma is `simp only [...]; exact Iff.rfl`.
-/

universe u

namespace SolidLean.Solid.TF

open Classical

variable {a : ℕ} {s : Fin a → ℕ} {n : ℕ}

local notation "cs" => Fin.castSucc

/-! ### Elementary notions -/

/-- `x_i ⊆ x_j`. -/
def subsetC (hs : IsConst s n) (i j : Fin a) : TF a s :=
  allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs i)) (memC hs.snoc (Fin.last a) (cs j)))

/-- `x_i ≠ ∅`. -/
def nonemptyC (hs : IsConst s n) (i : Fin a) : TF a s :=
  exC n (memC hs.snoc (Fin.last a) (cs i))

/-- `x_u = ⋃ x_x`. -/
def unionSetC (hs : IsConst s n) (x u : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (cs u))
    (exC n (Formula.and (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs x)))
      (memC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1))))))

/-- `x_p = 𝒫(x_x)`. -/
def powerSetC (hs : IsConst s n) (x p : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (cs p)) (subsetC hs.snoc (Fin.last a) (cs x)))

/-- `x_t = x_x ∪ {x_x}`. -/
def succC (hs : IsConst s n) (x t : Fin a) : TF a s :=
  allC n (Formula.iff (memC hs.snoc (Fin.last a) (cs t))
    (Formula.or (memC hs.snoc (Fin.last a) (cs x)) (eqC hs.snoc (Fin.last a) (cs x))))

/-- `x_x` is transitive. -/
def transC (hs : IsConst s n) (x : Fin a) : TF a s :=
  allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs x)) (subsetC hs.snoc (Fin.last a) (cs x)))

/-- `x_x` is an ordinal. -/
def ordC (hs : IsConst s n) (x : Fin a) : TF a s :=
  Formula.and (transC hs x)
    (Formula.and (allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs x)) (transC hs.snoc (Fin.last a))))
      (allC n (allC n (Formula.imp (memC hs.snoc.snoc (cs (Fin.last a)) (cs (cs x)))
        (Formula.imp (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs x)))
          (Formula.or (memC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))
            (Formula.or (eqC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))
              (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (Fin.last a))))))))))

/-- `x_x` is a limit ordinal. -/
def limitOrdC (hs : IsConst s n) (x : Fin a) : TF a s :=
  Formula.and (ordC hs x)
    (Formula.and (nonemptyC hs x)
      (allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs x))
        (exC n (Formula.and (succC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))
          (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs x))))))))

/-! ### Functions -/

/-- `x_f` is a function with domain `x_d`. -/
def funOnC (hs : IsConst s n) (f d : Fin a) : TF a s :=
  Formula.and (isFunC hs f)
    (allC n (Formula.iff (inDomC hs.snoc (cs f) (Fin.last a)) (memC hs.snoc (Fin.last a) (cs d))))

/-- `x_f` is injective. -/
def injC (hs : IsConst s n) (f : Fin a) : TF a s :=
  allC n (allC n (allC n (Formula.imp
    (funAppC hs.snoc.snoc.snoc (cs (cs (cs f))) (cs (cs (Fin.last a))) (Fin.last (a + 2)))
    (Formula.imp
      (funAppC hs.snoc.snoc.snoc (cs (cs (cs f))) (cs (Fin.last (a + 1))) (Fin.last (a + 2)))
      (eqC hs.snoc.snoc.snoc (cs (cs (Fin.last a))) (cs (Fin.last (a + 1))))))))

/-- `x_f` maps into `x_c`. -/
def mapsIntoC (hs : IsConst s n) (f c : Fin a) : TF a s :=
  allC n (allC n (Formula.imp
    (funAppC hs.snoc.snoc (cs (cs f)) (cs (Fin.last a)) (Fin.last (a + 1)))
    (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs c)))))

/-- `x_f : x_d ↪ x_c`. -/
def injIntoC (hs : IsConst s n) (f d c : Fin a) : TF a s :=
  Formula.and (funOnC hs f d) (Formula.and (injC hs f) (mapsIntoC hs f c))

/-- `x_f : x_d ≅ x_c`. -/
def bijOntoC (hs : IsConst s n) (f d c : Fin a) : TF a s :=
  Formula.and (injIntoC hs f d c)
    (allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs c))
      (exC n (funAppC hs.snoc.snoc (cs (cs f)) (Fin.last (a + 1)) (cs (Fin.last a))))))

/-! ### The rank hierarchy -/

/-- `x_f` is a partial attempt at `α ↦ V_α`. -/
def vAttemptC (hs : IsConst s n) (f : Fin a) : TF a s :=
  Formula.and (isFunC hs f)
    (allC n (allC n (Formula.imp
      (funAppC hs.snoc.snoc (cs (cs f)) (cs (Fin.last a)) (Fin.last (a + 1)))
      (Formula.and (ordC hs.snoc.snoc (cs (Fin.last a)))
        (Formula.and
          (Formula.imp (isEmptyC hs.snoc.snoc (cs (Fin.last a))) (isEmptyC hs.snoc.snoc (Fin.last (a + 1))))
          (Formula.and
            (allC n (Formula.imp
              (succC hs.snoc.snoc.snoc (Fin.last (a + 2)) (cs (cs (Fin.last a))))
              (exC n (Formula.and
                (funAppC hs.snoc.snoc.snoc.snoc (cs (cs (cs (cs f)))) (cs (Fin.last (a + 2))) (Fin.last (a + 3)))
                (powerSetC hs.snoc.snoc.snoc.snoc (Fin.last (a + 3)) (cs (cs (Fin.last (a + 1)))))))))
            (Formula.imp (limitOrdC hs.snoc.snoc (cs (Fin.last a)))
              (allC n (Formula.iff
                (memC hs.snoc.snoc.snoc (Fin.last (a + 2)) (cs (Fin.last (a + 1))))
                (exC n (exC n (Formula.and
                  (memC hs.snoc.snoc.snoc.snoc.snoc (cs (Fin.last (a + 3))) (cs (cs (cs (cs (Fin.last a))))))
                  (Formula.and
                    (funAppC hs.snoc.snoc.snoc.snoc.snoc (cs (cs (cs (cs (cs f))))) (cs (Fin.last (a + 3))) (Fin.last (a + 4)))
                    (memC hs.snoc.snoc.snoc.snoc.snoc (cs (cs (Fin.last (a + 2)))) (Fin.last (a + 4))))))))))))))))

/-- `x_v = V_{x_α}`. -/
def isVC (hs : IsConst s n) (α v : Fin a) : TF a s :=
  Formula.and (ordC hs α)
    (exC n (Formula.and (vAttemptC hs.snoc (Fin.last a))
      (Formula.and
        (allC n (Formula.imp
          (Formula.or (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs α)))
            (eqC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs α))))
          (inDomC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))))
        (funAppC hs.snoc (Fin.last a) (cs α) (cs v)))))

/-! ### Cardinals and inaccessibility -/

/-- `x_κ` is a cardinal. -/
def cardinalC (hs : IsConst s n) (κ : Fin a) : TF a s :=
  Formula.and (ordC hs κ)
    (allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs κ))
      (Formula.not (exC n (bijOntoC hs.snoc.snoc (Fin.last (a + 1)) (cs (Fin.last a)) (cs (cs κ)))))))

/-- `x_κ` is regular. -/
def regularC (hs : IsConst s n) (κ : Fin a) : TF a s :=
  Formula.and (ordC hs κ)
    (allC n (allC n (Formula.imp (memC hs.snoc.snoc (cs (Fin.last a)) (cs (cs κ)))
      (Formula.imp (funOnC hs.snoc.snoc (Fin.last (a + 1)) (cs (Fin.last a)))
        (Formula.imp (mapsIntoC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs κ)))
          (exC n (Formula.and (memC hs.snoc.snoc.snoc (Fin.last (a + 2)) (cs (cs (cs κ))))
            (allC n (allC n (Formula.imp
              (funAppC hs.snoc.snoc.snoc.snoc.snoc (cs (cs (cs (Fin.last (a + 1)))))
                (cs (Fin.last (a + 3))) (Fin.last (a + 4)))
              (memC hs.snoc.snoc.snoc.snoc.snoc (Fin.last (a + 4)) (cs (cs (Fin.last (a + 2)))))))))))))))

/-- `x_κ` is a strong limit. -/
def strongLimitC (hs : IsConst s n) (κ : Fin a) : TF a s :=
  Formula.and (ordC hs κ)
    (allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs κ))
      (allC n (Formula.imp (powerSetC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))
        (exC n (exC n (Formula.and
          (memC hs.snoc.snoc.snoc.snoc (cs (Fin.last (a + 2))) (cs (cs (cs (cs κ)))))
          (injIntoC hs.snoc.snoc.snoc.snoc (Fin.last (a + 3)) (cs (cs (Fin.last (a + 1))))
            (cs (Fin.last (a + 2)))))))))))

/-- `x_κ` is inaccessible. -/
def inaccC (hs : IsConst s n) (κ : Fin a) : TF a s :=
  Formula.and (cardinalC hs κ)
    (Formula.and
      (exC n (Formula.and (memC hs.snoc (Fin.last a) (cs κ)) (limitOrdC hs.snoc (Fin.last a))))
      (Formula.and (regularC hs κ) (strongLimitC hs κ)))

/-- `x_β` is the least inaccessible above `x_α`. -/
def nextInaccC (hs : IsConst s n) (α β : Fin a) : TF a s :=
  Formula.and (inaccC hs β)
    (Formula.and (memC hs α β)
      (allC n (Formula.imp (memC hs.snoc (cs α) (Fin.last a))
        (Formula.imp (memC hs.snoc (Fin.last a) (cs β))
          (Formula.not (inaccC hs.snoc (Fin.last a)))))))

/-- No greatest inaccessible below `x_κ`. -/
def noGreatestInaccC (hs : IsConst s n) (κ : Fin a) : TF a s :=
  allC n (Formula.imp (memC hs.snoc (Fin.last a) (cs κ))
    (Formula.imp (inaccC hs.snoc (Fin.last a))
      (exC n (Formula.and (memC hs.snoc.snoc (Fin.last (a + 1)) (cs (cs κ)))
        (Formula.and (memC hs.snoc.snoc (cs (Fin.last a)) (Fin.last (a + 1)))
          (inaccC hs.snoc.snoc (Fin.last (a + 1))))))))

/-! ### Satisfaction lemmas -/

variable (T : MemTower.{u})

theorem Sat_subsetC (hs : IsConst s n) (i j : Fin a) (x : Fin a → T.U n) :
    (subsetC hs i j).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).Subset (x i) (x j) := by
  unfold subsetC
  simp only [Sat_allC, Formula.Sat_imp, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_nonemptyC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (nonemptyC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).Nonempty (x i) := by
  unfold nonemptyC
  simp only [Sat_exC, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_unionSetC (hs : IsConst s n) (i u : Fin a) (x : Fin a → T.U n) :
    (unionSetC hs i u).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsUnionSet (x i) (x u) := by
  unfold unionSetC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Sat_exC, Formula.Sat_and, Fin.snoc_last,
    Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_powerSetC (hs : IsConst s n) (i p : Fin a) (x : Fin a → T.U n) :
    (powerSetC hs i p).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsPowerSet (x i) (x p) := by
  unfold powerSetC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Sat_subsetC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_succC (hs : IsConst s n) (i t : Fin a) (x : Fin a → T.U n) :
    (succC hs i t).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsSucc (x i) (x t) := by
  unfold succC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Formula.Sat_or, Sat_eqC, Fin.snoc_last,
    Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_transC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (transC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).Transitive (x i) := by
  unfold transC
  simp only [Sat_allC, Formula.Sat_imp, Sat_memC, Sat_subsetC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_ordC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (ordC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsOrdinal (x i) := by
  unfold ordC
  simp only [Formula.Sat_and, Sat_transC, Sat_allC, Formula.Sat_imp, Sat_memC, Formula.Sat_or,
    Sat_eqC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_limitOrdC (hs : IsConst s n) (i : Fin a) (x : Fin a → T.U n) :
    (limitOrdC hs i).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsLimitOrd (x i) := by
  unfold limitOrdC
  simp only [Formula.Sat_and, Sat_ordC, Sat_nonemptyC, Sat_allC, Formula.Sat_imp, Sat_memC,
    Sat_exC, Sat_succC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_funOnC (hs : IsConst s n) (f d : Fin a) (x : Fin a → T.U n) :
    (funOnC hs f d).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsFunctionOn (x f) (x d) := by
  unfold funOnC
  simp only [Formula.Sat_and, Sat_isFunC, Sat_allC, Formula.Sat_iff, Sat_inDomC, Sat_memC,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_injC (hs : IsConst s n) (f : Fin a) (x : Fin a → T.U n) :
    (injC hs f).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).Injective (x f) := by
  unfold injC
  simp only [Sat_allC, Formula.Sat_imp, Sat_funAppC, Sat_eqC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_mapsIntoC (hs : IsConst s n) (f c : Fin a) (x : Fin a → T.U n) :
    (mapsIntoC hs f c).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).MapsInto (x f) (x c) := by
  unfold mapsIntoC
  simp only [Sat_allC, Formula.Sat_imp, Sat_funAppC, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_injIntoC (hs : IsConst s n) (f d c : Fin a) (x : Fin a → T.U n) :
    (injIntoC hs f d c).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).IsInjectionInto (x f) (x d) (x c) := by
  unfold injIntoC
  simp only [Formula.Sat_and, Sat_funOnC, Sat_injC, Sat_mapsIntoC]
  exact Iff.rfl

theorem Sat_bijOntoC (hs : IsConst s n) (f d c : Fin a) (x : Fin a → T.U n) :
    (bijOntoC hs f d c).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).IsBijectionOnto (x f) (x d) (x c) := by
  unfold bijOntoC
  simp only [Formula.Sat_and, Sat_injIntoC, Sat_allC, Formula.Sat_imp, Sat_memC, Sat_exC,
    Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_vAttemptC (hs : IsConst s n) (f : Fin a) (x : Fin a → T.U n) :
    (vAttemptC hs f).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsVAttempt (x f) := by
  unfold vAttemptC
  simp only [Formula.Sat_and, Sat_isFunC, Sat_allC, Formula.Sat_imp, Sat_funAppC, Sat_ordC,
    Sat_isEmptyC, Sat_succC, Sat_exC, Sat_powerSetC, Sat_limitOrdC, Formula.Sat_iff, Sat_memC,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_isVC (hs : IsConst s n) (α v : Fin a) (x : Fin a → T.U n) :
    (isVC hs α v).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsV (x α) (x v) := by
  unfold isVC
  simp only [Formula.Sat_and, Sat_ordC, Sat_exC, Sat_vAttemptC, Sat_allC, Formula.Sat_imp,
    Formula.Sat_or, Sat_memC, Sat_eqC, Sat_inDomC, Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_cardinalC (hs : IsConst s n) (κ : Fin a) (x : Fin a → T.U n) :
    (cardinalC hs κ).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsCardinal (x κ) := by
  unfold cardinalC
  simp only [Formula.Sat_and, Sat_ordC, Sat_allC, Formula.Sat_imp, Sat_memC, Formula.Sat_not,
    Sat_exC, Sat_bijOntoC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_regularC (hs : IsConst s n) (κ : Fin a) (x : Fin a → T.U n) :
    (regularC hs κ).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsRegular (x κ) := by
  unfold regularC
  simp only [Formula.Sat_and, Sat_ordC, Sat_allC, Formula.Sat_imp, Sat_memC, Sat_funOnC,
    Sat_mapsIntoC, Sat_exC, Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_strongLimitC (hs : IsConst s n) (κ : Fin a) (x : Fin a → T.U n) :
    (strongLimitC hs κ).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).IsStrongLimit (x κ) := by
  unfold strongLimitC
  simp only [Formula.Sat_and, Sat_ordC, Sat_allC, Formula.Sat_imp, Sat_memC, Sat_powerSetC,
    Sat_exC, Sat_injIntoC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_inaccC (hs : IsConst s n) (κ : Fin a) (x : Fin a → T.U n) :
    (inaccC hs κ).Sat T.toStr (fun l => T.inj (x l)) ↔ (T.sortStr n).Inaccessible (x κ) := by
  unfold inaccC
  simp only [Formula.Sat_and, Sat_cardinalC, Sat_exC, Sat_memC, Sat_limitOrdC, Sat_regularC,
    Sat_strongLimitC, Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_nextInaccC (hs : IsConst s n) (α β : Fin a) (x : Fin a → T.U n) :
    (nextInaccC hs α β).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).NextInaccessible (x α) (x β) := by
  unfold nextInaccC
  simp only [Formula.Sat_and, Sat_inaccC, Sat_memC, Sat_allC, Formula.Sat_imp, Formula.Sat_not,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_noGreatestInaccC (hs : IsConst s n) (κ : Fin a) (x : Fin a → T.U n) :
    (noGreatestInaccC hs κ).Sat T.toStr (fun l => T.inj (x l)) ↔
      (T.sortStr n).NoGreatestInaccessibleBelow (x κ) := by
  unfold noGreatestInaccC
  simp only [Sat_allC, Formula.Sat_imp, Sat_memC, Sat_inaccC, Sat_exC, Formula.Sat_and,
    Fin.snoc_last, Fin.snoc_castSucc]
  exact Iff.rfl

end SolidLean.Solid.TF
