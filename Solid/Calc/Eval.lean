module

public import Solid.Calc.PrimClauses

/-!
# The evaluator of the core calculus as formulas of the tower signature

For a context `Γ` of length `m` and a term `t`, `eval Γ t` is a formula in
`m + 1` variables `(η, w)`: the environment `η` (variable `x` of sort
`lev(Γ, x)`) and the value `w` of sort `c(Γ, t)`.  Draft 2, §4.3, in the
set-encoded signature: the value of a term with classifier `c` is a set of
tower sort `c`; a type `A : U_r` has value in sort `r + 1` and its elements
have values `x` in sort `r` with `j_r(x) ∈ ⟦A⟧`; the universe `U_n` is the
set of `j`-images of sort `n + 1` (the truth values for `n = 0`); products,
abstractions and applications are the dependent product, the graph and
graph evaluation, with lifts between sorts where the levels differ.

The clauses are written for terms whose annotations are coherent (Lemma 3.2
of draft 2 says that certified terms are); an incoherent term gets the
formula `false`.
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

local notation "cs" => Fin.castSucc

/-- Discharge sort obligations of the shape `Fin.snoc … (cs (… (Fin.last _))) = _`. -/
macro "sorts" : tactic =>
  `(tactic| first
    | (intro l
       refine Fin.lastCases ?_ (fun l => ?_) l
       all_goals try (refine Fin.lastCases ?_ (fun l => ?_) l)
       all_goals simp [Ctx.levels_snoc, *])
    | simp [Ctx.levels_snoc, *])

/-- The value of `U_n` at position `w` (sort `n + 2`): the set `{∅, {∅}}` of
truth values for `n = 0`, and the set of all `j²(x)`, `x` of sort `n + 1`,
for `n = n' + 1`. -/
def univF {k : ℕ} {s : Fin k → ℕ} : (n : ℕ) → (w : Fin k) → s w = n + 2 → TF k s
  | 0, w, hw =>
    Formula.all 2 (Formula.iff (memF 2 (Fin.last k) (cs w) (by simp) (by simp [hw]))
      (Formula.or (at_ (isEmptyC (IsConst.const 1 2) 0) ![Fin.last k] (Fin.forall_fin_one.2 (by simp)))
        (at_ (isTrueC (IsConst.const 1 2) 0) ![Fin.last k] (Fin.forall_fin_one.2 (by simp)))))
  | n + 1, w, hw =>
    Formula.all (n + 3) (Formula.iff (memF (n + 3) (Fin.last k) (cs w) (by simp) (by simp [hw]))
      (.ex (n + 1) (liftNF (n + 1) 2 (Fin.last (k + 1)) (cs (Fin.last k)) (by simp) (by simp))))

section Clauses

variable {m : ℕ} (lev : Fin m → ℕ)

/-- The well-formedness guard of a product `Π(x : A). B` (of either kind):
`A` has a unique value `vA`, and `B` has a unique value at every element of
`vA`, lying in the universe `U_j`.  The value variable `w` (of sort `r`) is
not used.  Certified products always satisfy it (Theorem 4.1); it makes a
product's value exist only when the family it binds is a type family, which
is what the soundness argument for application needs. -/
def famOkF (i j r : ℕ) (φA : TF (m + 1) (Fin.snoc lev (i + 1)))
    (φB : TF (m + 2) (Fin.snoc (Fin.snoc lev i) (j + 1))) : TF (m + 1) (Fin.snoc lev r) :=
  -- layout: η, w : r, vA : i + 1
  .ex (i + 1) (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φA)
    (Formula.and
      -- ∀ vA' : i + 1, φA(η, vA') → vA' = vA
      (Formula.all (i + 1) (Formula.imp
        (Formula.rename (place1 (fun l => cs (cs (cs l))) (Fin.last (m + 2))) (by sorts) φA)
        (.eq (Fin.last (m + 2)) (cs (Fin.last (m + 1))) (by sorts))))
      -- ∀ a : i, j_i(a) ∈ vA → ∃ vB : j + 1, φB(η, a, vB) ∧
      --   (∀ vB' : j + 1, φB(η, a, vB') → vB' = vB) ∧ ∃ u : j + 2, u = U_j ∧ j_{j+1}(vB) ∈ u
      (Formula.all i (Formula.imp
        (tmemF i (Fin.last (m + 2)) (cs (Fin.last (m + 1))) (by sorts) (by sorts))
        (.ex (j + 1) (Formula.and
          (Formula.rename (place2 (fun l => cs (cs (cs (cs l)))) (cs (Fin.last (m + 2)))
            (Fin.last (m + 3))) (by sorts) φB)
          (Formula.and
            (Formula.all (j + 1) (Formula.imp
              (Formula.rename (place2 (fun l => cs (cs (cs (cs (cs l))))) (cs (cs (Fin.last (m + 2))))
                (Fin.last (m + 4))) (by sorts) φB)
              (.eq (Fin.last (m + 4)) (cs (Fin.last (m + 3))) (by sorts))))
            (.ex (j + 2) (Formula.and
              (univF j (Fin.last (m + 4)) (by simp))
              (tmemF (j + 1) (cs (Fin.last (m + 3))) (Fin.last (m + 4)) (by sorts) (by sorts)))))))))))

/-- `Π[prop; i, 0](x : A). B`: the truth value of `∀ a : A, B(a)`. -/
def piPropF (i : ℕ) (φA : TF (m + 1) (Fin.snoc lev (i + 1)))
    (φB : TF (m + 2) (Fin.snoc (Fin.snoc lev i) 1)) : TF (m + 1) (Fin.snoc lev 1) :=
  -- layout: η, w : 1, vA : i + 1
  .ex (i + 1) (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φA)
    -- w is the truth value of: ∀ a : i, j_i(a) ∈ vA → ∃ vB : 1, φB(η, a, vB) ∧ vB = {∅}
    (tvF 1 (cs (Fin.last m)) (by sorts)
      (Formula.all i (Formula.imp
        (tmemF i (Fin.last (m + 2)) (cs (Fin.last (m + 1))) (by sorts) (by sorts))
        (.ex 1 (Formula.and
          (Formula.rename (place2 (fun l => cs (cs (cs (cs l)))) (cs (Fin.last (m + 2)))
            (Fin.last (m + 3))) (by sorts) φB)
          (at_ (isTrueC (IsConst.const 1 1) 0) ![Fin.last (m + 3)]
            (Fin.forall_fin_one.2 (by simp)))))))))

/-- The dependent product condition on `f` (the last variable, of sort
`M = max i j`; layout `η, w, vA, p, f`): `f` is a function whose domain is
the lift of the elements of `vA`, and whose values at `a` lie in the lift
of `B(a)`. -/
def piBodyF (i j : ℕ) (φB : TF (m + 2) (Fin.snoc (Fin.snoc lev i) (j + 1))) :
    TF (m + 4) (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc lev (max i j + 1)) (i + 1)) (max i j)) (max i j)) :=
  Formula.and
    -- f is a function
    (at_ (isFunC (IsConst.const 1 (max i j)) 0) ![Fin.last (m + 3)]
      (Fin.forall_fin_one.2 (by sorts)))
    (Formula.and
      -- ∀ u : M, u ∈ dom f ↔ ∃ a : i, j_i(a) ∈ vA ∧ u = j^{M-i}(a)
      (Formula.all (max i j) (Formula.iff
        (at_ (inDomC (IsConst.const 2 (max i j)) 0 1)
          ![cs (Fin.last (m + 3)), Fin.last (m + 4)]
          (Fin.forall_fin_two.2 ⟨by sorts, by sorts⟩))
        (.ex i (Formula.and
          (tmemF i (Fin.last (m + 5)) (cs (cs (cs (cs (Fin.last (m + 1))))))
            (by sorts) (by sorts))
          (liftNF i (max i j - i) (Fin.last (m + 5)) (cs (Fin.last (m + 4)))
            (by sorts) (by simp <;> omega))))))
      -- ∀ a : i, j_i(a) ∈ vA → ∀ u : M, u = j^{M-i}(a) → ∀ v : M, v = f(u) →
      --   ∃ vB : j + 1, φB(η, a, vB) ∧ ∃ b : j, j_j(b) ∈ vB ∧ v = j^{M-j}(b)
      (Formula.all i (Formula.imp
        (tmemF i (Fin.last (m + 4)) (cs (cs (cs (Fin.last (m + 1)))))
          (by sorts) (by sorts))
        (Formula.all (max i j) (Formula.imp
          (liftNF i (max i j - i) (cs (Fin.last (m + 4))) (Fin.last (m + 5))
            (by sorts) (by simp <;> omega))
          (Formula.all (max i j) (Formula.imp
            (at_ (funAppC (IsConst.const 3 (max i j)) 0 1 2)
              ![cs (cs (cs (Fin.last (m + 3)))), cs (Fin.last (m + 5)), Fin.last (m + 6)]
              (forall_fin_three.2 ⟨by sorts, by sorts, by sorts⟩))
            (.ex (j + 1) (Formula.and
              (Formula.rename
                (place2 (fun l => cs (cs (cs (cs (cs (cs (cs (cs l))))))))
                  (cs (cs (cs (Fin.last (m + 4))))) (Fin.last (m + 7)))
                (by sorts) φB)
              (.ex j (Formula.and
                (tmemF j (Fin.last (m + 8)) (cs (Fin.last (m + 7))) (by sorts) (by sorts))
                (liftNF j (max i j - j) (Fin.last (m + 8)) (cs (cs (Fin.last (m + 6))))
                  (by sorts) (by simp <;> omega)))))))))))))

/-- `Π[data; i, j](x : A). B`: the dependent product, as a set of sort
`max i j + 1`. -/
def piDataF (i j : ℕ) (φA : TF (m + 1) (Fin.snoc lev (i + 1)))
    (φB : TF (m + 2) (Fin.snoc (Fin.snoc lev i) (j + 1))) :
    TF (m + 1) (Fin.snoc lev (max i j + 1)) :=
  -- layout: η, w : M + 1, vA : i + 1, p : M, f : M   (M = max i j)
  .ex (i + 1) (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φA)
    (.ex (max i j) (Formula.and
      -- w = j_M(p)
      (liftZF (max i j) (Fin.last (m + 2)) (cs (cs (Fin.last m))) (by sorts) (by sorts))
      (Formula.all (max i j) (Formula.iff
        -- f ∈ p
        (memF (max i j) (Fin.last (m + 3)) (cs (Fin.last (m + 2))) (by sorts) (by sorts))
        (piBodyF lev i j φB))))))

/-- The graph condition on `q` (the last variable, of sort `M`; layout
`η, w, vA, q`): `q = ⟨j^{M-i}(a), j^{M-j}(b(a))⟩` for some `a ∈ A`. -/
def lamBodyF (i j : ℕ) (φb : TF (m + 2) (Fin.snoc (Fin.snoc lev i) j)) :
    TF (m + 3) (Fin.snoc (Fin.snoc (Fin.snoc lev (max i j)) (i + 1)) (max i j)) :=
  -- ∃ a : i, j_i(a) ∈ vA ∧ ∃ u : M, u = j^{M-i}(a) ∧ ∃ vb : j, φb(η, a, vb) ∧
  --   ∃ v : M, v = j^{M-j}(vb) ∧ q = ⟨u, v⟩
  .ex i (Formula.and
    (tmemF i (Fin.last (m + 3)) (cs (cs (Fin.last (m + 1)))) (by sorts) (by sorts))
    (.ex (max i j) (Formula.and
      (liftNF i (max i j - i) (cs (Fin.last (m + 3))) (Fin.last (m + 4))
        (by sorts) (by simp <;> omega))
      (.ex j (Formula.and
        (Formula.rename
          (place2 (fun l => cs (cs (cs (cs (cs (cs l)))))) (cs (cs (Fin.last (m + 3))))
            (Fin.last (m + 5)))
          (by sorts) φb)
        (.ex (max i j) (Formula.and
          (liftNF j (max i j - j) (cs (Fin.last (m + 5))) (Fin.last (m + 6))
            (by sorts) (by simp <;> omega))
          (at_ (ordPairC (IsConst.const 3 (max i j)) 0 1 2)
            ![cs (cs (Fin.last (m + 4))), Fin.last (m + 6), cs (cs (cs (cs (Fin.last (m + 2)))))]
            (forall_fin_three.2 ⟨by sorts, by sorts, by sorts⟩)))))))))

/-- `λ[data; i, j](x : A). b`: the graph `{⟨j^{M-i}(a), j^{M-j}(b(a))⟩ : a ∈ A}`,
a set of sort `max i j`. -/
def lamDataF (i j : ℕ) (φA : TF (m + 1) (Fin.snoc lev (i + 1)))
    (φb : TF (m + 2) (Fin.snoc (Fin.snoc lev i) j)) : TF (m + 1) (Fin.snoc lev (max i j)) :=
  -- layout: η, w : M, vA : i + 1, q : M
  .ex (i + 1) (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φA)
    (Formula.all (max i j) (Formula.iff
      -- q ∈ w
      (memF (max i j) (Fin.last (m + 2)) (cs (cs (Fin.last m))) (by sorts) (by sorts))
      (lamBodyF lev i j φb))))

/-- `app[data; j](f, a)`: graph evaluation, with the argument lifted to the
sort of `f` and the value lowered to sort `j`. -/
def appDataF (j cf ca : ℕ) (hj : j ≤ cf) (ha : ca ≤ cf) (φf : TF (m + 1) (Fin.snoc lev cf))
    (φa : TF (m + 1) (Fin.snoc lev ca)) : TF (m + 1) (Fin.snoc lev j) :=
  -- layout: η, w : j, vf : cf, va : ca, u : cf, v : cf;  u = j^{cf-ca}(va), v = vf(u), v = j^{cf-j}(w)
  .ex cf (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φf)
    (.ex ca (Formula.and
      (Formula.rename (place1 (fun l => cs (cs (cs l))) (Fin.last (m + 2))) (by sorts) φa)
      (.ex cf (Formula.and
        (liftNF ca (cf - ca) (cs (Fin.last (m + 2))) (Fin.last (m + 3)) (by sorts) (by simp <;> omega))
        (.ex cf (Formula.and
          (at_ (funAppC (IsConst.const 3 cf) 0 1 2)
            ![cs (cs (cs (Fin.last (m + 1)))), cs (Fin.last (m + 3)), Fin.last (m + 4)]
            (forall_fin_three.2 ⟨by sorts, by sorts, by sorts⟩))
          (liftNF j (cf - j) (cs (cs (cs (cs (Fin.last m))))) (Fin.last (m + 4))
            (by sorts) (by simp <;> omega)))))))))

/-- `let[j](x : A := v). b`. -/
def letF (j cv : ℕ) (φv : TF (m + 1) (Fin.snoc lev cv))
    (φb : TF (m + 2) (Fin.snoc (Fin.snoc lev cv) j)) : TF (m + 1) (Fin.snoc lev j) :=
  -- layout: η, w : j, vv : cv
  .ex cv (Formula.and
    (Formula.rename (place1 (fun l => cs (cs l)) (Fin.last (m + 1))) (by sorts) φv)
    (Formula.rename (place2 (fun l => cs (cs l)) (Fin.last (m + 1)) (cs (Fin.last m)))
      (by sorts) φb))

end Clauses

/-- The evaluator. -/
def eval : {m : ℕ} → (Γ : Ctx m) → (t : Term) → TF (m + 1) (Fin.snoc Γ.levels (t.cls Γ))
  | m, Γ, .var x =>
    if h : x < m then
      .eq (cs ⟨x, h⟩) (Fin.last m) (by
        rw [Fin.snoc_castSucc, Fin.snoc_last]
        exact (Γ.lev_of_lt ⟨x, h⟩).symm)
    else .false_
  | m, _, .univ n => univF n (Fin.last m) (by simp)
  | _, Γ, .pi .prop i _ A B =>
    if hA : A.cls Γ = i + 1 then
    if hB : B.cls (Γ.snoc A i) = 1 then
      Formula.and
        (famOkF Γ.levels i 0 1 (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) B)))
        (piPropF Γ.levels i (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) B)))
    else .false_ else .false_
  | _, Γ, .pi .data i j A B =>
    if hA : A.cls Γ = i + 1 then
    if hB : B.cls (Γ.snoc A i) = j + 1 then
      Formula.and
        (famOkF Γ.levels i j (max i j + 1) (recast (by sorts) (eval Γ A))
          (recast (by sorts) (eval (Γ.snoc A i) B)))
        (piDataF Γ.levels i j (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) B)))
    else .false_ else .false_
  | m, _, .lam .prop _ _ _ _ =>
    at_ (isEmptyC (IsConst.const 1 0) 0) ![Fin.last m] (Fin.forall_fin_one.2 (by simp))
  | _, Γ, .lam .data i j A b =>
    if hA : A.cls Γ = i + 1 then
    if hb : b.cls (Γ.snoc A i) = j then
      lamDataF Γ.levels i j (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) b))
    else .false_ else .false_
  | m, _, .app .prop _ _ _ =>
    at_ (isEmptyC (IsConst.const 1 0) 0) ![Fin.last m] (Fin.forall_fin_one.2 (by simp))
  | _, Γ, .app .data j f a =>
    if hj : j ≤ f.cls Γ then
    if ha : a.cls Γ ≤ f.cls Γ then
      appDataF Γ.levels j (f.cls Γ) (a.cls Γ) hj ha (eval Γ f) (eval Γ a)
    else .false_ else .false_
  | _, Γ, .letE j A v b =>
    if hb : b.cls (Γ.snoc A (v.cls Γ)) = j then
      letF Γ.levels j (v.cls Γ) (eval Γ v) (recast (by sorts) (eval (Γ.snoc A (v.cls Γ)) b))
    else .false_
  | _, Γ, .prim c args =>
    if h : ∀ k, (args k).cls Γ = c.argSort k then
      primF Γ.levels c (fun k => recast (fun i => by rw [h k]) (eval Γ (args k)))
    else .false_

end SolidLean.Calc
