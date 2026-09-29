module

public import Solid.Calc.Typing
public import Solid.Calc.SnocLits
public import Solid.Calc.DiacSimp

/-!
# Double negation elimination is derivable: Diaconescu's argument in the core calculus

The primitive `dne (P : U_0) (h : (P → False) → False) : P` of §3.4 is redundant: this
file builds a closed term `dneTerm` and a certified derivation

* `dne_derivable : Typed Γ0 dneTerm (Π (P : U_0). ((P → False) → False) → P) 0`,
* `dne_derived`: in any well-formed context, applying `dneTerm` to `P : U_0` and to
  `h : (P → False) → False` (the declared argument types of `dne`) gives a term of type `P`
  (its declared result type),
* `dneTerm_usesDne : dneTerm.usesDne = false`: the term does not mention `dne`.

The derivation is the Diaconescu–Goodman–Myhill argument, with the propositional axiom of
choice `choice[1,1]`, propositional extensionality `propext`, Σ-types, `Lift`, `Trunc` and
the equality eliminator `Eq.rec[1,0]`:

* Propositions are elements of `U_0`; `True := False → False`, `¬A := A → False`, and
  `∨`, `∧` are the impredicative encodings (`Π (C : U_0). …`).
* For a pair of propositions `p : PairP := Σ (q₀ : U_0). U_0`, the selection type is
  `Sel p := Σ (x : U_0). Lift ((True = x ∧ p.1) ∨ (x = False ∧ p.2))`.  Indexing by the
  two propositions `True`, `False` (rather than by `0`, `1` in `Nat`) makes the final step
  `True ≠ False` a single transport `Eq.rec` of `trivial : True` along `True = False` with
  the motive `y ↦ y`, so no recursor on `Nat` is needed.
* The index type of the choice is `IdxT := Σ (p : PairP). Lift (Trunc (Sel p))`, the family
  is `q ↦ Sel q.1`, and `choice` gives `Trunc (Π q. Sel q.1)`, eliminated by `Trunc.rec`
  into the proposition `P`.
* Given a choice function `f` and `P : U_0`, with `pairU := (True, P)` and `pairV := (P, True)`,
  the chosen elements `xU := (f pU).1` and `xV := (f pV).1` satisfy `True = xU ∨ (xU = False ∧ P)`
  and `(True = xV ∧ P) ∨ xV = False`.  Three of the four cases give `P`; in the remaining case
  `True = xU`, `xV = False`, and assuming `P` (to refute it, since `¬¬P` is given) we get
  `pairU = pairV` (by `propext` and one `Eq.rec`), hence `pU = pV` (transport along a motive
  quantifying over the `Lift (Trunc _)` component, which is definitionally proof irrelevant
  through `up (down _)`), hence `xU = xV`, hence a proof of `True` transports to a proof of
  `False`.

The file is organized as: the closed constants and the impredicative encodings with their
typings; the Σ/Lift/Trunc/Eq wrappers and the equality eliminator with a proposition-valued
motive (`typed_eqRec`); the families of the argument and their typings; the terms of the
argument (`pU`, `xU`, …) with their typings and the needed definitional equalities; a
compositional library computing `shift` and `subst` on all these encodings (the simp set
`diac_simps`, used through `calc_simp`); and finally the derivation in the concrete
contexts `Γ0 ⊂ … ⊂ Γ6`.
-/

@[expose] public section

namespace SolidLean.Calc

open Term

/-! ### Tools -/


theorem vecFun_cons {α β : Type*} {n : ℕ} (f : α → β) (a : α) (v : Fin n → α) :
    (fun k => f (Matrix.vecCons a v k)) = Matrix.vecCons (f a) (fun k => f (v k)) := by
  funext k
  refine Fin.cases rfl (fun k => rfl) k

theorem vecFun_empty {α β : Type*} (f : α → β) :
    (fun k : Fin 0 => f (Matrix.vecEmpty k)) = Matrix.vecEmpty := by
  funext k; exact k.elim0

theorem Typed.cast {m : ℕ} {Γ : Ctx m} {t A A' : Term} {r : ℕ} (h : Typed Γ t A r) (e : A = A') :
    Typed Γ t A' r := e ▸ h

theorem Typed.castT {m : ℕ} {Γ : Ctx m} {t t' A : Term} {r : ℕ} (h : Typed Γ t A r) (e : t = t') :
    Typed Γ t' A r := e ▸ h

/-- Both binder-level rules for a variable, with the computed type given. -/
theorem typed_var {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ) (x : Fin m) {A : Term}
    (e : Term.shift x (m - x) (Γ x).1 = A) : Typed Γ (var x) A (Γ x).2 :=
  (Typed.var x hΓ).cast e


/-! ### Base constants -/

def FalseT : Term := prim .false_ ![]
def U0 : Term := univ 0
/-- `¬ A := A → False`. -/
def notT (A : Term) : Term := pi .prop 0 0 A FalseT
/-- `True := False → False` (a closed proposition). -/
def TrueT : Term := notT FalseT
/-- The canonical proof of `True`, at depth `d`. -/
def trivT (d : ℕ) : Term := lam .prop 0 0 FalseT (var d)

section Base
variable {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ)
include hΓ

set_option linter.unusedSectionVars false in
theorem typed_false : Typed Γ FalseT (univ 0) 1 :=
  Typed.prim .false_ ![] trivial (fun k => k.elim0)

theorem typed_U0 : Typed Γ U0 (univ 1) 2 := Typed.univ 0 hΓ

theorem typed_notT {A : Term} (hA : Typed Γ A (univ 0) 1) : Typed Γ (notT A) (univ 0) 1 :=
  Typed.piProp hA (typed_false (CtxOk.snoc hΓ hA))

theorem typed_TrueT : Typed Γ TrueT (univ 0) 1 := typed_notT hΓ (typed_false hΓ)

end Base

/-- Weakening with the shifts computed. -/
theorem weak' {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) {B : Term} {l : ℕ}
    (hB : Typed Γ B (univ l) (l + 1)) {t' A' : Term} (et : Term.shift m 1 t = t')
    (eA : Term.shift m 1 A = A') : Typed (Γ.snoc B l) t' A' r :=
  ((Typed.weak h hB).castT et).cast eA


theorem Typed.castL {m : ℕ} {Γ : Ctx m} {t A : Term} {r r' : ℕ} (h : Typed Γ t A r) (e : r = r') :
    Typed Γ t A r' := e ▸ h

/-- A variable with everything computed. -/
theorem typed_var' {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ) (x : Fin m) {n : ℕ} {A : Term} {r : ℕ}
    (ex : x.val = n) (eA : Term.shift x (m - x) (Γ x).1 = A) (er : (Γ x).2 = r) :
    Typed Γ (var n) A r :=
  (((Typed.var x hΓ).castT (by rw [ex])).cast eA).castL er


/-! ### Shift and substitution laws -/

theorem shift_shift' (n k e₁ e₂ : ℕ) (hk : k ≤ e₁) :
    ∀ t : Term, shift (n + k) e₂ (shift n e₁ t) = shift n (e₁ + e₂) t
  | var x => by
    by_cases h : x < n
    · have h2 : x < n + k := Nat.lt_add_right k h
      simp [shift, h, h2]
    · have h' : ¬ x + e₁ < n + k := by omega
      simp [shift, h, h', Nat.add_assoc]
  | univ _ => rfl
  | pi k' i j A B => by simp only [shift, shift_shift' n k e₁ e₂ hk A, shift_shift' n k e₁ e₂ hk B]
  | lam k' i j A b => by simp only [shift, shift_shift' n k e₁ e₂ hk A, shift_shift' n k e₁ e₂ hk b]
  | app k' j f a => by simp only [shift, shift_shift' n k e₁ e₂ hk f, shift_shift' n k e₁ e₂ hk a]
  | letE j A v b => by
    simp only [shift, shift_shift' n k e₁ e₂ hk A, shift_shift' n k e₁ e₂ hk v, shift_shift' n k e₁ e₂ hk b]
  | prim c args => by
    simp only [shift]
    congr 1
    funext k'
    exact shift_shift' n k e₁ e₂ hk (args k')

theorem shift_shift (n e₁ e₂ : ℕ) (t : Term) : shift (n + e₁) e₂ (shift n e₁ t) = shift n (e₁ + e₂) t :=
  shift_shift' n e₁ e₁ e₂ (le_refl e₁) t

theorem shift_succ_shift_two (n : ℕ) (t : Term) : shift (n + 1) 1 (shift n 2 t) = shift n 3 t :=
  shift_shift' n 1 2 1 (by decide) t

theorem shift_self_shift (n e₁ e₂ : ℕ) (t : Term) : shift n e₂ (shift n e₁ t) = shift n (e₁ + e₂) t :=
  shift_shift' n 0 e₁ e₂ (Nat.zero_le _) t

theorem shift_succ_shift (n : ℕ) (t : Term) : shift (n + 1) 1 (shift n 1 t) = shift n 2 t :=
  shift_shift n 1 1 t

theorem subst_shift_succ' (m k e d : ℕ) (hk : k ≤ e) (a : Term) :
    ∀ t : Term, subst (m + k) a d (shift m (e + 1) t) = shift m e t
  | var x => by
    by_cases h : x < m
    · have h1 : x < m + k := by omega
      simp [shift, subst, h, h1]
    · have h1 : ¬ x + (e + 1) < m + k := by omega
      have h2 : x + (e + 1) ≠ m + k := by omega
      have h3 : x + (e + 1) - 1 = x + e := by omega
      simp [shift, subst, h, h1, h2, h3]
  | univ _ => rfl
  | pi k' i j A B => by
    simp only [shift, subst, subst_shift_succ' m k e d hk a A, subst_shift_succ' m k e (d + 1) hk a B]
  | lam k' i j A b => by
    simp only [shift, subst, subst_shift_succ' m k e d hk a A, subst_shift_succ' m k e (d + 1) hk a b]
  | app k' j f x => by
    simp only [shift, subst, subst_shift_succ' m k e d hk a f, subst_shift_succ' m k e d hk a x]
  | letE j A v b => by
    simp only [shift, subst, subst_shift_succ' m k e d hk a A, subst_shift_succ' m k e d hk a v,
      subst_shift_succ' m k e (d + 1) hk a b]
  | prim c args => by
    simp only [shift, subst]
    congr 1
    funext k'
    exact subst_shift_succ' m k e d hk a (args k')

theorem subst_shift_succ (m e d : ℕ) (a : Term) (t : Term) :
    subst m a d (shift m (e + 1) t) = shift m e t :=
  subst_shift_succ' m 0 e d (Nat.zero_le e) a t

theorem subst_shift_one (m d : ℕ) (a : Term) (t : Term) : subst m a d (shift m 1 t) = t := by
  rw [subst_shift_succ m 0 d a t, shift_zero]

theorem subst_shift_two (m d : ℕ) (a : Term) (t : Term) : subst m a d (shift m 2 t) = shift m 1 t :=
  subst_shift_succ m 1 d a t

theorem subst_shift_three (m d : ℕ) (a : Term) (t : Term) : subst m a d (shift m 3 t) = shift m 2 t :=
  subst_shift_succ m 2 d a t

theorem subst_succ_shift_two (m d : ℕ) (a : Term) (t : Term) :
    subst (m + 1) a d (shift m 2 t) = shift m 1 t :=
  subst_shift_succ' m 1 1 d (le_refl 1) a t

theorem subst_succ2_shift_three (m d : ℕ) (a : Term) (t : Term) :
    subst (m + 2) a d (shift m 3 t) = shift m 2 t :=
  subst_shift_succ' m 2 2 d (le_refl 2) a t

theorem subst_var_lt {m x : ℕ} (h : x < m) (d : ℕ) (a : Term) : subst m a d (var x) = var x := by
  simp [subst, h]

theorem subst_var_self (m d : ℕ) (a : Term) : subst m a d (var m) = shift m d a := by
  simp [subst]


/-- The normalization of shifts and substitutions on the terms of this file. -/
macro "sub_simp" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [subst_shift_one, subst_shift_two, subst_shift_three, subst_succ_shift_two, subst_succ2_shift_three, subst, shift, shift_shift, shift_succ_shift_two, shift_self_shift, shift_zero, lt_self_iff_false, Nat.lt_irrefl, Nat.lt_add_one, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, Nat.lt_succ_self, Nat.left_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_zero, Nat.add_one_ne_zero, and_false, ite_true, ite_false, eq_self_iff_true, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.add_sub_cancel_left, Nat.zero_add, Nat.add_zero, vecFun_cons, vecFun_empty, Nat.lt_add_left_iff_pos] $[$loc]?)

/-! ### Propositional encodings (impredicative) -/

/-- `A ∨ B := Π (C : U_0). (A → C) → (B → C) → C`. -/
def orT (d : ℕ) (A B : Term) : Term :=
  pi .prop 1 0 U0 (pi .prop 0 0 (pi .prop 0 0 (shift d 1 A) (var d))
    (pi .prop 0 0 (pi .prop 0 0 (shift d 2 B) (var d)) (var d)))
def inlT (d : ℕ) (A B a : Term) : Term :=
  lam .prop 1 0 U0 (lam .prop 0 0 (pi .prop 0 0 (shift d 1 A) (var d))
    (lam .prop 0 0 (pi .prop 0 0 (shift d 2 B) (var d)) (app .prop 0 (var (d + 1)) (shift d 3 a))))
def inrT (d : ℕ) (A B b : Term) : Term :=
  lam .prop 1 0 U0 (lam .prop 0 0 (pi .prop 0 0 (shift d 1 A) (var d))
    (lam .prop 0 0 (pi .prop 0 0 (shift d 2 B) (var d)) (app .prop 0 (var (d + 2)) (shift d 3 b))))
/-- `A ∧ B := Π (C : U_0). (A → B → C) → C`. -/
def andT (d : ℕ) (A B : Term) : Term :=
  pi .prop 1 0 U0 (pi .prop 0 0 (pi .prop 0 0 (shift d 1 A) (pi .prop 0 0 (shift d 2 B) (var d))) (var d))
def andI (d : ℕ) (A B a b : Term) : Term :=
  lam .prop 1 0 U0 (lam .prop 0 0 (pi .prop 0 0 (shift d 1 A) (pi .prop 0 0 (shift d 2 B) (var d)))
    (app .prop 0 (app .prop 0 (var (d + 1)) (shift d 2 a)) (shift d 2 b)))

section Enc
variable {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ)
include hΓ


theorem typed_trivT : Typed Γ (trivT m) TrueT 0 := by
  refine Typed.lamProp (typed_false hΓ) ?_
  refine typed_var' (CtxOk.snoc hΓ (typed_false hΓ)) (Fin.last m) (by simp) ?_ (by simp [Ctx.snoc])
  simp [Ctx.snoc, FalseT, Term.shift, vecFun_empty]

variable {A B : Term} (hA : Typed Γ A (univ 0) 1) (hB : Typed Γ B (univ 0) 1)
include hA hB

set_option linter.unusedSectionVars false in
/-- The context `Γ, C : U_0` and the variable `C`. -/
theorem or_ctx1 : CtxOk (Γ.snoc U0 1) ∧ Typed (Γ.snoc U0 1) (var m) (univ 0) 1 := by
  have hΓ1 : CtxOk (Γ.snoc U0 1) := CtxOk.snoc hΓ (typed_U0 hΓ)
  exact ⟨hΓ1, typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])⟩

theorem typed_orT : Typed Γ (orT m A B) (univ 0) 1 := by
  obtain ⟨hΓ1, hC⟩ := or_ctx1 hΓ hA hB
  refine Typed.piProp (typed_U0 hΓ) ?_
  have hA1 : Typed (Γ.snoc U0 1) (shift m 1 A) (univ 0) 1 := Typed.weak hA (typed_U0 hΓ)
  have hAC : Typed (Γ.snoc U0 1) (pi .prop 0 0 (shift m 1 A) (var m)) (univ 0) 1 :=
    Typed.piProp hA1 (typed_var' (CtxOk.snoc hΓ1 hA1) (Fin.castSucc (Fin.last m)) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.piProp hAC ?_
  have hΓ2 : CtxOk ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) := CtxOk.snoc hΓ1 hAC
  have hB2 : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) (shift m 2 B) (univ 0) 1 :=
    (Typed.weak (Typed.weak hB (typed_U0 hΓ)) hAC).castT (shift_succ_shift m B)
  have hBC : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0)
      (pi .prop 0 0 (shift m 2 B) (var m)) (univ 0) 1 :=
    Typed.piProp hB2 (typed_var' (CtxOk.snoc hΓ2 hB2) (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.piProp hBC ?_
  exact typed_var' (CtxOk.snoc hΓ2 hBC) (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp)
    (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])

theorem typed_inlT {a : Term} (ha : Typed Γ a A 0) : Typed Γ (inlT m A B a) (orT m A B) 0 := by
  obtain ⟨hΓ1, hC⟩ := or_ctx1 hΓ hA hB
  refine Typed.lamProp (typed_U0 hΓ) ?_
  have hA1 : Typed (Γ.snoc U0 1) (shift m 1 A) (univ 0) 1 := Typed.weak hA (typed_U0 hΓ)
  have hAC : Typed (Γ.snoc U0 1) (pi .prop 0 0 (shift m 1 A) (var m)) (univ 0) 1 :=
    Typed.piProp hA1 (typed_var' (CtxOk.snoc hΓ1 hA1) (Fin.castSucc (Fin.last m)) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.lamProp hAC ?_
  have hΓ2 : CtxOk ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) := CtxOk.snoc hΓ1 hAC
  have hB2 : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) (shift m 2 B) (univ 0) 1 :=
    (Typed.weak (Typed.weak hB (typed_U0 hΓ)) hAC).castT (shift_succ_shift m B)
  have hBC : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0)
      (pi .prop 0 0 (shift m 2 B) (var m)) (univ 0) 1 :=
    Typed.piProp hB2 (typed_var' (CtxOk.snoc hΓ2 hB2) (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.lamProp hBC ?_
  have hΓ3 := CtxOk.snoc hΓ2 hBC
  have hf : Typed (((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0).snoc
      (pi .prop 0 0 (shift m 2 B) (var m)) 0) (var (m + 1)) (pi .prop 0 0 (shift m 3 A) (var m)) 0 :=
    typed_var' hΓ3 (Fin.castSucc (Fin.last (m + 1))) (by simp) (by
      simp only [Ctx.snoc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last, Term.shift]
      rw [show m + 3 - (m + 1) = 2 by omega, shift_shift m 1 2]
      simp) (by simp [Ctx.snoc])
  have ha3 : Typed (((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0).snoc
      (pi .prop 0 0 (shift m 2 B) (var m)) 0) (shift m 3 a) (shift m 3 A) 0 := by
    have h := Typed.weak (Typed.weak (Typed.weak ha (typed_U0 hΓ)) hAC) hBC
    simp only [shift_shift, Nat.add_assoc, Nat.reduceAdd] at h
    exact h
  have := Typed.appProp hf ha3
  rwa [subst_var_lt (by omega)] at this

theorem typed_inrT {b : Term} (hb : Typed Γ b B 0) : Typed Γ (inrT m A B b) (orT m A B) 0 := by
  obtain ⟨hΓ1, hC⟩ := or_ctx1 hΓ hA hB
  refine Typed.lamProp (typed_U0 hΓ) ?_
  have hA1 : Typed (Γ.snoc U0 1) (shift m 1 A) (univ 0) 1 := Typed.weak hA (typed_U0 hΓ)
  have hAC : Typed (Γ.snoc U0 1) (pi .prop 0 0 (shift m 1 A) (var m)) (univ 0) 1 :=
    Typed.piProp hA1 (typed_var' (CtxOk.snoc hΓ1 hA1) (Fin.castSucc (Fin.last m)) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.lamProp hAC ?_
  have hΓ2 : CtxOk ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) := CtxOk.snoc hΓ1 hAC
  have hB2 : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0) (shift m 2 B) (univ 0) 1 :=
    (Typed.weak (Typed.weak hB (typed_U0 hΓ)) hAC).castT (shift_succ_shift m B)
  have hBC : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0)
      (pi .prop 0 0 (shift m 2 B) (var m)) (univ 0) 1 :=
    Typed.piProp hB2 (typed_var' (CtxOk.snoc hΓ2 hB2) (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp)
      (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc]))
  refine Typed.lamProp hBC ?_
  have hΓ3 := CtxOk.snoc hΓ2 hBC
  have hg : Typed (((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0).snoc
      (pi .prop 0 0 (shift m 2 B) (var m)) 0) (var (m + 2)) (pi .prop 0 0 (shift m 3 B) (var m)) 0 :=
    typed_var' hΓ3 (Fin.last (m + 2)) (by simp) (by
      simp only [Ctx.snoc, Fin.snoc_last, Fin.val_last, Term.shift]
      rw [show m + 3 - (m + 2) = 1 by omega, shift_shift m 2 1]
      simp) (by simp [Ctx.snoc])
  have hb3 : Typed (((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (var m)) 0).snoc
      (pi .prop 0 0 (shift m 2 B) (var m)) 0) (shift m 3 b) (shift m 3 B) 0 := by
    have h := Typed.weak (Typed.weak (Typed.weak hb (typed_U0 hΓ)) hAC) hBC
    simp only [shift_shift, Nat.add_assoc, Nat.reduceAdd] at h
    exact h
  have := Typed.appProp hg hb3
  rwa [subst_var_lt (by omega)] at this

theorem typed_andT : Typed Γ (andT m A B) (univ 0) 1 := by
  obtain ⟨hΓ1, hC⟩ := or_ctx1 hΓ hA hB
  refine Typed.piProp (typed_U0 hΓ) ?_
  have hA1 : Typed (Γ.snoc U0 1) (shift m 1 A) (univ 0) 1 := Typed.weak hA (typed_U0 hΓ)
  have hB2 : Typed ((Γ.snoc U0 1).snoc (shift m 1 A) 0) (shift m 2 B) (univ 0) 1 :=
    (Typed.weak (Typed.weak hB (typed_U0 hΓ)) hA1).castT (shift_succ_shift m B)
  have hK : Typed (Γ.snoc U0 1) (pi .prop 0 0 (shift m 1 A) (pi .prop 0 0 (shift m 2 B) (var m))) (univ 0) 1 :=
    Typed.piProp hA1 (Typed.piProp hB2 (typed_var' (CtxOk.snoc (CtxOk.snoc hΓ1 hA1) hB2)
      (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp) (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])))
  refine Typed.piProp hK ?_
  exact typed_var' (CtxOk.snoc hΓ1 hK) (Fin.castSucc (Fin.last m)) (by simp)
    (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])

theorem typed_andI {a b : Term} (ha : Typed Γ a A 0) (hb : Typed Γ b B 0) :
    Typed Γ (andI m A B a b) (andT m A B) 0 := by
  obtain ⟨hΓ1, hC⟩ := or_ctx1 hΓ hA hB
  refine Typed.lamProp (typed_U0 hΓ) ?_
  have hA1 : Typed (Γ.snoc U0 1) (shift m 1 A) (univ 0) 1 := Typed.weak hA (typed_U0 hΓ)
  have hB2 : Typed ((Γ.snoc U0 1).snoc (shift m 1 A) 0) (shift m 2 B) (univ 0) 1 :=
    (Typed.weak (Typed.weak hB (typed_U0 hΓ)) hA1).castT (shift_succ_shift m B)
  have hK : Typed (Γ.snoc U0 1) (pi .prop 0 0 (shift m 1 A) (pi .prop 0 0 (shift m 2 B) (var m))) (univ 0) 1 :=
    Typed.piProp hA1 (Typed.piProp hB2 (typed_var' (CtxOk.snoc (CtxOk.snoc hΓ1 hA1) hB2)
      (Fin.castSucc (Fin.castSucc (Fin.last m))) (by simp) (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])))
  refine Typed.lamProp hK ?_
  have hΓ2 := CtxOk.snoc hΓ1 hK
  have hk : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (pi .prop 0 0 (shift m 2 B) (var m))) 0)
      (var (m + 1)) (pi .prop 0 0 (shift m 2 A) (pi .prop 0 0 (shift m 3 B) (var m))) 0 :=
    typed_var' hΓ2 (Fin.last (m + 1)) (by simp) (by
      simp only [Ctx.snoc, Fin.snoc_last, Fin.val_last]
      rw [show m + 2 - (m + 1) = 1 by omega]
      sub_simp) (by simp [Ctx.snoc])
  have ha2 : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (pi .prop 0 0 (shift m 2 B) (var m))) 0)
      (shift m 2 a) (shift m 2 A) 0 := by
    have h := Typed.weak (Typed.weak ha (typed_U0 hΓ)) hK
    rw [shift_succ_shift, shift_succ_shift] at h
    exact h
  have hb2' : Typed ((Γ.snoc U0 1).snoc (pi .prop 0 0 (shift m 1 A) (pi .prop 0 0 (shift m 2 B) (var m))) 0)
      (shift m 2 b) (shift m 2 B) 0 := by
    have h := Typed.weak (Typed.weak hb (typed_U0 hΓ)) hK
    rw [shift_succ_shift, shift_succ_shift] at h
    exact h
  have h1 := Typed.appProp hk ha2
  simp only [subst, subst_succ2_shift_three] at h1
  sub_simp at h1
  have h2 := Typed.appProp h1 hb2'
  sub_simp at h2
  exact h2

/-- The projections of a conjunction. -/
def andE1 (d : ℕ) (h A B : Term) : Term :=
  app .prop 0 (app .prop 0 h A) (lam .prop 0 0 A (lam .prop 0 0 (shift d 1 B) (var d)))
def andE2 (d : ℕ) (h A B : Term) : Term :=
  app .prop 0 (app .prop 0 h B) (lam .prop 0 0 A (lam .prop 0 0 (shift d 1 B) (var (d + 1))))

theorem typed_andE1 {h : Term} (hh : Typed Γ h (andT m A B) 0) : Typed Γ (andE1 m h A B) A 0 := by
  have h1 := Typed.appProp hh hA
  sub_simp at h1
  have hB1 : Typed (Γ.snoc A 0) (shift m 1 B) (univ 0) 1 := Typed.weak hB hA
  have hk : Typed Γ (lam .prop 0 0 A (lam .prop 0 0 (shift m 1 B) (var m)))
      (pi .prop 0 0 A (pi .prop 0 0 (shift m 1 B) (shift m 2 A))) 0 :=
    Typed.lamProp hA (Typed.lamProp hB1 (typed_var' (CtxOk.snoc (CtxOk.snoc hΓ hA) hB1)
      (Fin.castSucc (Fin.last m)) (by simp) (by
        simp only [Ctx.snoc, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
        rw [show m + 2 - m = 2 by omega]) (by simp [Ctx.snoc])))
  have h2 := Typed.appProp h1 hk
  rwa [subst_shift_one] at h2

theorem typed_andE2 {h : Term} (hh : Typed Γ h (andT m A B) 0) : Typed Γ (andE2 m h A B) B 0 := by
  have h1 := Typed.appProp hh hB
  sub_simp at h1
  have hB1 : Typed (Γ.snoc A 0) (shift m 1 B) (univ 0) 1 := Typed.weak hB hA
  have hk : Typed Γ (lam .prop 0 0 A (lam .prop 0 0 (shift m 1 B) (var (m + 1))))
      (pi .prop 0 0 A (pi .prop 0 0 (shift m 1 B) (shift m 2 B))) 0 :=
    Typed.lamProp hA (Typed.lamProp hB1 (typed_var' (CtxOk.snoc (CtxOk.snoc hΓ hA) hB1)
      (Fin.last (m + 1)) (by simp) (by
        simp only [Ctx.snoc, Fin.snoc_last, Fin.val_last]
        rw [show m + 2 - (m + 1) = 1 by omega, shift_shift m 1 1]) (by simp [Ctx.snoc])))
  have h2 := Typed.appProp h1 hk
  rwa [subst_shift_one] at h2

end Enc

/-- Elimination of a disjunction into `C`. -/
def orElim (h C f g : Term) : Term := app .prop 0 (app .prop 0 (app .prop 0 h C) f) g

theorem typed_orElim {m : ℕ} {Γ : Ctx m} (A B : Term) {h C f g : Term} (hh : Typed Γ h (orT m A B) 0)
    (hC : Typed Γ C (univ 0) 1) (hf : Typed Γ f (pi .prop 0 0 A (shift m 1 C)) 0)
    (hg : Typed Γ g (pi .prop 0 0 B (shift m 1 C)) 0) : Typed Γ (orElim h C f g) C 0 := by
  have h1 := Typed.appProp hh hC
  sub_simp at h1
  have h2 := Typed.appProp h1 hf
  sub_simp at h2
  have h3 := Typed.appProp h2 hg
  sub_simp at h3
  exact h3

/-! ### β-conversion of types, Σ-types with λ-families, lifts, truncation, equality -/

section Prims
variable {m : ℕ} {Γ : Ctx m}

/-- `t : (λ x:A. B) a` gives `t : B[a]`. -/
theorem betaTy {i r : ℕ} {A Bb a t : Term}
    (hA : Typed Γ A (univ i) (i + 1)) (hB : Typed (Γ.snoc A i) Bb (univ r) (r + 1)) (ha : Typed Γ a A i)
    (ht : Typed Γ t (app .data (r + 1) (lam .data i (r + 1) A Bb) a) r) : Typed Γ t (subst m a 0 Bb) r :=
  ht.conv (DefEq.betaData (Nat.succ_pos r) hA hB ha)

theorem betaTyRev {i r : ℕ} {A Bb a t : Term}
    (hA : Typed Γ A (univ i) (i + 1)) (hB : Typed (Γ.snoc A i) Bb (univ r) (r + 1)) (ha : Typed Γ a A i)
    (ht : Typed Γ t (subst m a 0 Bb) r) : Typed Γ t (app .data (r + 1) (lam .data i (r + 1) A Bb) a) r :=
  ht.conv (DefEq.symm (DefEq.betaData (Nat.succ_pos r) hA hB ha))

/-- Σ-types over `U_1` with a λ-family. -/
def sigT (A Bb : Term) : Term := prim (.sigma 1 1) ![A, lam .data 1 2 A Bb]
def pairT (A Bb a b : Term) : Term := prim (.pair 1 1) ![A, lam .data 1 2 A Bb, a, b]
def fstT (A Bb s : Term) : Term := prim (.fst 1 1) ![A, lam .data 1 2 A Bb, s]
def sndT (A Bb s : Term) : Term := prim (.snd 1 1) ![A, lam .data 1 2 A Bb, s]

variable {A Bb : Term} (hA : Typed Γ A (univ 1) 2) (hB : Typed (Γ.snoc A 1) Bb (univ 1) 2)
include hA hB

theorem typed_fam : Typed Γ (lam .data 1 2 A Bb) (pi .data 1 2 A (univ 1)) 2 :=
  Typed.lamData (by decide) hA hB

theorem typed_sigT : Typed Γ (sigT A Bb) (univ 1) 2 :=
  Typed.prim (.sigma 1 1) ![A, lam .data 1 2 A Bb] (le_refl 1)
    (fun k => match k with | 0 => hA | 1 => typed_fam hA hB)

theorem typed_pairT {a b : Term} (ha : Typed Γ a A 1) (hb : Typed Γ b (subst m a 0 Bb) 1) :
    Typed Γ (pairT A Bb a b) (sigT A Bb) 1 :=
  Typed.prim (.pair 1 1) ![A, lam .data 1 2 A Bb, a, b] (le_refl 1)
    (fun k => match k with
      | 0 => hA | 1 => typed_fam hA hB | 2 => ha
      | 3 => betaTyRev hA hB ha hb)

theorem typed_fstT {s : Term} (hs : Typed Γ s (sigT A Bb) 1) : Typed Γ (fstT A Bb s) A 1 :=
  Typed.prim (.fst 1 1) ![A, lam .data 1 2 A Bb, s] trivial
    (fun k => match k with | 0 => hA | 1 => typed_fam hA hB | 2 => hs)

theorem typed_sndT {s : Term} (hs : Typed Γ s (sigT A Bb) 1) :
    Typed Γ (sndT A Bb s) (subst m (fstT A Bb s) 0 Bb) 1 :=
  betaTy hA hB (typed_fstT hA hB hs)
    (Typed.prim (.snd 1 1) ![A, lam .data 1 2 A Bb, s] trivial
      (fun k => match k with | 0 => hA | 1 => typed_fam hA hB | 2 => hs))

end Prims

section Prims2
variable {m : ℕ} {Γ : Ctx m}

def liftT (Q : Term) : Term := prim (.lift 0 1) ![Q]
def upT (Q q : Term) : Term := prim (.up 0 1) ![Q, q]
def downT (Q l : Term) : Term := prim (.down 0 1) ![Q, l]
def truncT (X : Term) : Term := prim (.trunc 1) ![X]
def truncMkT (X x : Term) : Term := prim (.truncMk 1) ![X, x]
def truncRecT (X P f h : Term) : Term := prim (.truncRec 1) ![X, P, f, h]
def eqT (A a b : Term) : Term := prim (.eq 1) ![A, a, b]
def reflT (A a : Term) : Term := prim (.refl 1) ![A, a]
def propextT (P Q f g : Term) : Term := prim .propext ![P, Q, f, g]
def falseElimT (C h : Term) : Term := prim (.falseElim 0) ![C, h]

theorem typed_liftT {Q : Term} (hQ : Typed Γ Q (univ 0) 1) : Typed Γ (liftT Q) (univ 1) 2 :=
  Typed.prim (.lift 0 1) ![Q] trivial (fun k => match k with | 0 => hQ)

theorem typed_upT {Q q : Term} (hQ : Typed Γ Q (univ 0) 1) (hq : Typed Γ q Q 0) :
    Typed Γ (upT Q q) (liftT Q) 1 :=
  Typed.prim (.up 0 1) ![Q, q] trivial (fun k => match k with | 0 => hQ | 1 => hq)

theorem typed_downT {Q l : Term} (hQ : Typed Γ Q (univ 0) 1) (hl : Typed Γ l (liftT Q) 1) :
    Typed Γ (downT Q l) Q 0 :=
  Typed.prim (.down 0 1) ![Q, l] trivial (fun k => match k with | 0 => hQ | 1 => hl)

theorem typed_truncT {X : Term} (hX : Typed Γ X (univ 1) 2) : Typed Γ (truncT X) (univ 0) 1 :=
  Typed.prim (.trunc 1) ![X] trivial (fun k => match k with | 0 => hX)

theorem typed_truncMkT {X x : Term} (hX : Typed Γ X (univ 1) 2) (hx : Typed Γ x X 1) :
    Typed Γ (truncMkT X x) (truncT X) 0 :=
  Typed.prim (.truncMk 1) ![X, x] trivial (fun k => match k with | 0 => hX | 1 => hx)

theorem typed_truncRecT {X P f h : Term} (hX : Typed Γ X (univ 1) 2) (hP : Typed Γ P (univ 0) 1)
    (hf : Typed Γ f (pi .prop 1 0 X (shift m 1 P)) 0) (hh : Typed Γ h (truncT X) 0) :
    Typed Γ (truncRecT X P f h) P 0 :=
  Typed.prim (.truncRec 1) ![X, P, f, h] trivial
    (fun k => match k with | 0 => hX | 1 => hP | 2 => hf | 3 => hh)

theorem typed_eqT {A a b : Term} (hA : Typed Γ A (univ 1) 2) (ha : Typed Γ a A 1) (hb : Typed Γ b A 1) :
    Typed Γ (eqT A a b) (univ 0) 1 :=
  Typed.prim (.eq 1) ![A, a, b] trivial (fun k => match k with | 0 => hA | 1 => ha | 2 => hb)

theorem typed_reflT {A a : Term} (hA : Typed Γ A (univ 1) 2) (ha : Typed Γ a A 1) :
    Typed Γ (reflT A a) (eqT A a a) 0 :=
  Typed.prim (.refl 1) ![A, a] trivial (fun k => match k with | 0 => hA | 1 => ha)

theorem typed_propextT {P Q f g : Term} (hP : Typed Γ P (univ 0) 1) (hQ : Typed Γ Q (univ 0) 1)
    (hf : Typed Γ f (pi .prop 0 0 P (shift m 1 Q)) 0) (hg : Typed Γ g (pi .prop 0 0 Q (shift m 1 P)) 0) :
    Typed Γ (propextT P Q f g) (eqT U0 P Q) 0 :=
  Typed.prim .propext ![P, Q, f, g] trivial (fun k => match k with | 0 => hP | 1 => hQ | 2 => hf | 3 => hg)

theorem typed_falseElimT {C h : Term} (hC : Typed Γ C (univ 0) 1) (hh : Typed Γ h FalseT 0) :
    Typed Γ (falseElimT C h) C 0 :=
  Typed.prim (.falseElim 0) ![C, h] trivial (fun k => match k with | 0 => hC | 1 => hh)

/-- Congruence of `Eq` in its last argument. -/
theorem defEq_eqT_right {A a b b' : Term} (hA : Typed Γ A (univ 1) 2) (ha : Typed Γ a A 1)
    (hb : DefEq Γ b b' A 1) : DefEq Γ (eqT A a b) (eqT A a b') (univ 0) 1 :=
  DefEq.congrPrim (.eq 1) ![A, a, b] ![A, a, b'] trivial
    (fun k => match k with | 0 => DefEq.refl hA | 1 => DefEq.refl ha | 2 => hb)

/-- Congruence of `pair` in its last argument. -/
theorem defEq_pairT_last {A Bb a b b' : Term} (hA : Typed Γ A (univ 1) 2) (hB : Typed (Γ.snoc A 1) Bb (univ 1) 2)
    (ha : Typed Γ a A 1) (hb : DefEq Γ b b' (app .data 2 (lam .data 1 2 A Bb) a) 1) :
    DefEq Γ (pairT A Bb a b) (pairT A Bb a b') (sigT A Bb) 1 :=
  DefEq.congrPrim (.pair 1 1) ![A, lam .data 1 2 A Bb, a, b] ![A, lam .data 1 2 A Bb, a, b'] (le_refl 1)
    (fun k => match k with
      | 0 => DefEq.refl hA | 1 => DefEq.refl (typed_fam hA hB) | 2 => DefEq.refl ha | 3 => hb)

/-- Congruence of `up`. -/
theorem defEq_upT {Q q q' : Term} (hQ : Typed Γ Q (univ 0) 1) (h : DefEq Γ q q' Q 0) :
    DefEq Γ (upT Q q) (upT Q q') (liftT Q) 1 :=
  DefEq.congrPrim (.up 0 1) ![Q, q] ![Q, q'] trivial (fun k => match k with | 0 => DefEq.refl hQ | 1 => h)

/-- `up (down l) ≡ l`. -/
theorem defEq_upDown {Q l : Term} (hQ : Typed Γ Q (univ 0) 1) (hl : Typed Γ l (liftT Q) 1) :
    DefEq Γ (upT Q (downT Q l)) l (liftT Q) 1 :=
  DefEq.upDown (i := 0) (d := 1) (A := Q) (a := l) (fun k => match k with | 0 => hQ | 1 => hl)

/-- Two elements of a lifted proposition are definitionally equal. -/
theorem defEq_lift_irrel {Q l l' : Term} (hQ : Typed Γ Q (univ 0) 1) (hl : Typed Γ l (liftT Q) 1)
    (hl' : Typed Γ l' (liftT Q) 1) : DefEq Γ l l' (liftT Q) 1 :=
  DefEq.trans (DefEq.symm (defEq_upDown hQ hl))
    (DefEq.trans (defEq_upT hQ (DefEq.proofIrrel (typed_downT hQ hl) (typed_downT hQ hl'))) (defEq_upDown hQ hl'))

/-- The motive `λ y p. Cb` of an equality elimination. -/
def motiveT (m : ℕ) (A a Cb : Term) : Term :=
  lam .data 1 1 A (lam .data 0 1 (eqT (shift m 1 A) (shift m 1 a) (var m)) Cb)

/-- The equality eliminator with a proposition-valued motive `λ y p. Cb`,
everything β-reduced.  The typing of the two instances of the motive body is
supplied. -/
theorem typed_eqRec {A a Cb c b p : Term} (hΓ : CtxOk Γ)
    (hA : Typed Γ A (univ 1) 2) (ha : Typed Γ a A 1)
    (hC : Typed ((Γ.snoc A 1).snoc (eqT (shift m 1 A) (shift m 1 a) (var m)) 0) Cb (univ 0) 1)
    (hCa : Typed (Γ.snoc (eqT A a a) 0) (subst m a 1 Cb) (univ 0) 1)
    (hb : Typed Γ b A 1) (hp : Typed Γ p (eqT A a b) 0)
    (hCb : Typed (Γ.snoc (eqT A a b) 0) (subst m b 1 Cb) (univ 0) 1)
    (hc : Typed Γ c (subst m (reflT A a) 0 (subst m a 1 Cb)) 0) :
    Typed Γ (prim (.eqRec 1 0) ![A, a, motiveT m A a Cb, c, b, p]) (subst m p 0 (subst m b 1 Cb)) 0 := by
  have hA1 : Typed (Γ.snoc A 1) (shift m 1 A) (univ 1) 2 := Typed.weak hA hA
  have ha1 : Typed (Γ.snoc A 1) (shift m 1 a) (shift m 1 A) 1 := Typed.weak ha hA
  have hy : Typed (Γ.snoc A 1) (var m) (shift m 1 A) 1 :=
    typed_var' (CtxOk.snoc hΓ hA) (Fin.last m) (by simp) (by simp [Ctx.snoc]) (by simp [Ctx.snoc])
  have hEq : Typed (Γ.snoc A 1) (eqT (shift m 1 A) (shift m 1 a) (var m)) (univ 0) 1 := typed_eqT hA1 ha1 hy
  have hbody : Typed (Γ.snoc A 1) (lam .data 0 1 (eqT (shift m 1 A) (shift m 1 a) (var m)) Cb)
      (pi .data 0 1 (eqT (shift m 1 A) (shift m 1 a) (var m)) (univ 0)) 1 :=
    Typed.lamData (le_refl 1) hEq hC
  have hCm : Typed Γ (motiveT m A a Cb) (pi .data 1 1 A (pi .data 0 1 (eqT (shift m 1 A) (shift m 1 a) (var m)) (univ 0))) 1 :=
    Typed.lamData (le_refl 1) hA hbody
  -- the instance of the motive at `a, refl`
  have hrefl : Typed Γ (reflT A a) (eqT A a a) 0 := typed_reflT hA ha
  have heqaa : Typed Γ (eqT A a a) (univ 0) 1 := typed_eqT hA ha ha
  have d1 := DefEq.betaData (le_refl 1) hA hbody ha
  simp only [eqT] at d1
  sub_simp at d1
  have d2 := DefEq.congrAppData (le_refl 1) d1 (DefEq.refl hrefl)
  have d3 := DefEq.betaData (le_refl 1) heqaa hCa hrefl
  have d := DefEq.trans d2 d3
  have hc' : Typed Γ c (app .data 1 (app .data 1 (motiveT m A a Cb) a) (reflT A a)) 0 :=
    hc.conv (DefEq.symm d)
  -- the instance of the motive at `b, p`
  have heqab : Typed Γ (eqT A a b) (univ 0) 1 := typed_eqT hA ha hb
  have e1 := DefEq.betaData (le_refl 1) hA hbody hb
  simp only [eqT] at e1
  sub_simp at e1
  have e2 := DefEq.congrAppData (le_refl 1) e1 (DefEq.refl hp)
  have e3 := DefEq.betaData (le_refl 1) heqab hCb hp
  have e := DefEq.trans e2 e3
  have hres : Typed Γ (prim (.eqRec 1 0) ![A, a, motiveT m A a Cb, c, b, p])
      (app .data 1 (app .data 1 (motiveT m A a Cb) b) p) 0 :=
    Typed.prim (.eqRec 1 0) ![A, a, motiveT m A a Cb, c, b, p] trivial
      (fun k => match k with | 0 => hA | 1 => ha | 2 => hCm | 3 => hc' | 4 => hb | 5 => hp)
  exact hres.conv e

end Prims2

/-! ### The specific families of Diaconescu's argument -/

section Consts

theorem shift_FalseT (d e : ℕ) : shift d e FalseT = FalseT := by simp only [FalseT, shift, vecFun_empty]
theorem shift_U0 (d e : ℕ) : shift d e U0 = U0 := rfl
theorem shift_notT (d e : ℕ) (A : Term) : shift d e (notT A) = notT (shift d e A) := by
  simp only [notT, shift, shift_FalseT]
theorem shift_TrueT (d e : ℕ) : shift d e TrueT = TrueT := by simp only [TrueT, shift_notT, shift_FalseT]
theorem subst_FalseT (m d : ℕ) (a : Term) : subst m a d FalseT = FalseT := by simp only [FalseT, subst, vecFun_empty]
theorem subst_U0 (m d : ℕ) (a : Term) : subst m a d U0 = U0 := rfl
theorem subst_notT (m d : ℕ) (a A : Term) : subst m a d (notT A) = notT (subst m a d A) := by
  simp only [notT, subst, subst_FalseT]
theorem subst_TrueT (m d : ℕ) (a : Term) : subst m a d TrueT = TrueT := by
  simp only [TrueT, subst_notT, subst_FalseT]

theorem subst_shift_four (m d : ℕ) (a : Term) (t : Term) : subst m a d (shift m 4 t) = shift m 3 t :=
  subst_shift_succ m 3 d a t
theorem subst_shift_five (m d : ℕ) (a : Term) (t : Term) : subst m a d (shift m 5 t) = shift m 4 t :=
  subst_shift_succ m 4 d a t

theorem nat_add_lt_self_iff (d k : ℕ) : (d + k < d) ↔ False := ⟨fun h => by omega, fun h => h.elim⟩
theorem nat_add_succ_eq_self_iff (d k : ℕ) : (d + (k + 1) = d) ↔ False := ⟨fun h => by omega, fun h => h.elim⟩
theorem nat_add_succ_sub_one (d k : ℕ) : d + (k + 1) - 1 = d + k := by omega
theorem nat_lt_add_succ (d k : ℕ) : (d < d + (k + 1)) ↔ True := ⟨fun _ => trivial, fun _ => by omega⟩
theorem nat_add_lt_add_iff (d j k : ℕ) : (d + j < d + k) ↔ j < k := by constructor <;> intro h <;> omega
theorem nat_add_eq_add_iff (d j k : ℕ) : (d + j = d + k) ↔ j = k := by constructor <;> intro h <;> omega
theorem nat_lt_add_left_iff' (d j k : ℕ) (h : j < k) : (j < d + k) ↔ True := ⟨fun _ => trivial, fun _ => by omega⟩
theorem nat_eq_add_left_iff' (d j k : ℕ) (h : j < k) : (j = d + k) ↔ False := ⟨fun h' => by omega, fun h => h.elim⟩
theorem nat_lt_succ_of_lt_iff (j d : ℕ) (h : j < d) : (j < d + 1) ↔ True := ⟨fun _ => trivial, fun _ => by omega⟩
theorem nat_lt_iff_true (j d : ℕ) (h : j < d) : (j < d) ↔ True := ⟨fun _ => trivial, fun _ => h⟩
theorem nat_eq_iff_false (j d : ℕ) (h : j < d) : (j = d) ↔ False := ⟨fun h' => by omega, fun h => h.elim⟩

end Consts

/-- Pairs of propositions `Σ (q₀ : U_0). U_0`. -/
def PairP : Term := sigT U0 U0
def mkPair (a b : Term) : Term := pairT U0 U0 a b
def pfst (s : Term) : Term := fstT U0 U0 s
def psnd (s : Term) : Term := sndT U0 U0 s

theorem shift_PairP (d e : ℕ) : shift d e PairP = PairP := by
  simp only [PairP, sigT, U0, shift, vecFun_cons, vecFun_empty]
theorem subst_PairP (m d : ℕ) (a : Term) : subst m a d PairP = PairP := by
  simp only [PairP, sigT, U0, subst, vecFun_cons, vecFun_empty]

/-- The normalization of shifts and substitutions, with the constants. -/
macro "sub_simp'" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp (disch := omega) only [shift_FalseT, shift_U0, shift_TrueT, shift_PairP, subst_FalseT, subst_U0, subst_TrueT, subst_PairP, subst_shift_succ', subst_shift_succ, subst, shift, shift_shift', shift_self_shift, shift_zero, lt_self_iff_false, Nat.lt_irrefl, Nat.lt_add_one, Nat.lt_add_right_iff_pos, Nat.zero_lt_succ, Nat.lt_succ_self, Nat.left_eq_add, Nat.add_eq_zero_iff, Nat.succ_ne_zero, Nat.add_one_ne_zero, nat_add_lt_self_iff, nat_add_succ_eq_self_iff, nat_add_succ_sub_one, nat_lt_add_succ, nat_add_lt_add_iff, nat_add_eq_add_iff, nat_lt_add_left_iff', nat_eq_add_left_iff', nat_lt_iff_true, nat_eq_iff_false, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceEqDiff, and_false, ite_true, ite_false, eq_self_iff_true, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.add_sub_cancel_left, Nat.zero_add, Nat.add_zero, vecFun_cons, vecFun_empty, Nat.lt_add_left_iff_pos] $[$loc]?)

/-- `x ∈ p`: `(True = x ∧ p.1) ∨ (x = False ∧ p.2)`, for `x : U_0`. -/
def memP (d : ℕ) (p x : Term) : Term :=
  orT d (andT d (eqT U0 TrueT x) (pfst p)) (andT d (eqT U0 x FalseT) (psnd p))
/-- The family `x ↦ Lift (x ∈ p)`, in the context extended by `x : U_0`. -/
def selFam (d : ℕ) (p : Term) : Term := liftT (memP (d + 1) (shift d 1 p) (var d))
/-- `Σ (x : U_0). Lift (x ∈ p)`. -/
def Sel (d : ℕ) (p : Term) : Term := sigT U0 (selFam d p)
def mkSel (d : ℕ) (p x w : Term) : Term := pairT U0 (selFam d p) x w
def selX (d : ℕ) (p s : Term) : Term := fstT U0 (selFam d p) s
def selW (d : ℕ) (p s : Term) : Term := sndT U0 (selFam d p) s
/-- The family `p ↦ Lift (Trunc (Sel p))` over `PairP`, in the context extended by `p`. -/
def bfam (d : ℕ) : Term := liftT (truncT (Sel (d + 1) (var d)))
/-- The index type `Σ (p : PairP). Lift (Trunc (Sel p))`. -/
def IdxT (d : ℕ) : Term := sigT PairP (bfam d)
def mkIdx (d : ℕ) (p w : Term) : Term := pairT PairP (bfam d) p w
def ifst (d : ℕ) (s : Term) : Term := fstT PairP (bfam d) s
def isnd (d : ℕ) (s : Term) : Term := sndT PairP (bfam d) s
/-- The choice family `q ↦ Sel (ifst q)`, in the context extended by `q`. -/
def cfam (d : ℕ) : Term := Sel (d + 1) (ifst (d + 1) (var d))
def cfamL (d : ℕ) : Term := lam .data 1 2 (IdxT d) (cfam d)
/-- `q ↦ down (isnd q) : Π q. Trunc (cfam q)`. -/
def hInh (d : ℕ) : Term := lam .prop 1 0 (IdxT d) (downT (truncT (cfam d)) (isnd (d + 1) (var d)))
def choiceTm (d : ℕ) : Term := prim (.choice 1 1) ![IdxT d, cfamL d, hInh d]
/-- The type of the choice function. -/
def FunTy (d : ℕ) : Term := pi .data 1 1 (IdxT d) (app .data 2 (cfamL (d + 1)) (var d))

macro "unfold_defs" loc:(Lean.Parser.Tactic.location)? : tactic => `(tactic| simp only [selFam, memP, liftT, orT, andT, eqT, pfst, psnd, fstT, sndT, Sel, sigT, bfam, truncT, IdxT, cfam, cfamL, ifst, isnd, mkIdx, pairT, FunTy, TrueT, notT, PairP, hInh, downT, mkSel, selX, selW, mkPair, upT, truncMkT, reflT, inlT, inrT, andI, andE1, andE2, orElim, trivT, propextT, falseElimT, truncRecT, motiveT, U0] $[$loc]?)

section Eqns

theorem subst_selFam (d : ℕ) (p x : Term) : subst d x 0 (selFam d p) = liftT (memP d p x) := by
  unfold_defs; sub_simp'

theorem subst_bfam (d : ℕ) (p : Term) : subst d p 0 (bfam d) = liftT (truncT (Sel d p)) := by
  unfold_defs; sub_simp'

theorem subst_cfam (d : ℕ) : subst (d + 1) (var d) 0 (cfam (d + 1)) = cfam d := by
  unfold_defs; sub_simp'

theorem subst_cfam' (d : ℕ) (q : Term) : subst d q 0 (cfam d) = Sel d (ifst d q) := by
  unfold_defs; sub_simp'

theorem subst_funBody (d : ℕ) (q : Term) :
    subst d q 0 (app .data 2 (cfamL (d + 1)) (var d)) = app .data 2 (cfamL d) q := by
  unfold_defs; sub_simp'

theorem shift_IdxT (d k : ℕ) : shift d k (IdxT d) = IdxT (d + k) := by
  unfold_defs; sub_simp'; simp only [Nat.add_comm]

theorem shift_cfamL (d k : ℕ) : shift d k (cfamL d) = cfamL (d + k) := by
  unfold_defs; sub_simp'; simp only [Nat.add_comm]

theorem shift_FunTy (d k : ℕ) : shift d k (FunTy d) = FunTy (d + k) := by
  unfold_defs; sub_simp'; simp only [Nat.add_comm]

end Eqns

theorem DefEq.castS {m : ℕ} {Γ : Ctx m} {t s s' A : Term} {r : ℕ} (h : DefEq Γ t s A r) (e : s = s') :
    DefEq Γ t s' A r := e ▸ h

theorem DefEq.castA {m : ℕ} {Γ : Ctx m} {t s A A' : Term} {r : ℕ} (h : DefEq Γ t s A r) (e : A = A') :
    DefEq Γ t s A' r := e ▸ h

/-! ### Typing of the families -/

section Fam
variable {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ)
include hΓ

theorem typed_PairP : Typed Γ PairP (univ 1) 2 :=
  typed_sigT (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))

theorem typed_mkPair {a b : Term} (ha : Typed Γ a U0 1) (hb : Typed Γ b U0 1) :
    Typed Γ (mkPair a b) PairP 1 :=
  typed_pairT (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) ha hb

theorem typed_pfst {s : Term} (hs : Typed Γ s PairP 1) : Typed Γ (pfst s) U0 1 :=
  typed_fstT (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) hs

theorem typed_psnd {s : Term} (hs : Typed Γ s PairP 1) : Typed Γ (psnd s) U0 1 :=
  typed_sndT (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) hs

theorem typed_memP {p x : Term} (hp : Typed Γ p PairP 1) (hx : Typed Γ x U0 1) :
    Typed Γ (memP m p x) (univ 0) 1 :=
  typed_orT hΓ (typed_andT hΓ (typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) hx) (typed_pfst hΓ hp))
    (typed_andT hΓ (typed_eqT (typed_U0 hΓ) hx (typed_false hΓ)) (typed_psnd hΓ hp))

theorem typed_selFam {p : Term} (hp : Typed Γ p PairP 1) : Typed (Γ.snoc U0 1) (selFam m p) (univ 1) 2 := by
  have hΓ1 : CtxOk (Γ.snoc U0 1) := CtxOk.snoc hΓ (typed_U0 hΓ)
  have hp1 : Typed (Γ.snoc U0 1) (shift m 1 p) PairP 1 :=
    (Typed.weak hp (typed_U0 hΓ)).cast (shift_PairP m 1)
  have hx : Typed (Γ.snoc U0 1) (var m) U0 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_U0]) (by simp [Ctx.snoc])
  exact typed_liftT (typed_memP hΓ1 hp1 hx)

theorem typed_Sel {p : Term} (hp : Typed Γ p PairP 1) : Typed Γ (Sel m p) (univ 1) 2 :=
  typed_sigT (typed_U0 hΓ) (typed_selFam hΓ hp)

theorem typed_mkSel {p x w : Term} (hp : Typed Γ p PairP 1) (hx : Typed Γ x U0 1)
    (hw : Typed Γ w (liftT (memP m p x)) 1) : Typed Γ (mkSel m p x w) (Sel m p) 1 :=
  typed_pairT (typed_U0 hΓ) (typed_selFam hΓ hp) hx (hw.cast (subst_selFam m p x).symm)

theorem typed_selX {p s : Term} (hp : Typed Γ p PairP 1) (hs : Typed Γ s (Sel m p) 1) :
    Typed Γ (selX m p s) U0 1 :=
  typed_fstT (typed_U0 hΓ) (typed_selFam hΓ hp) hs

theorem typed_selW {p s : Term} (hp : Typed Γ p PairP 1) (hs : Typed Γ s (Sel m p) 1) :
    Typed Γ (selW m p s) (liftT (memP m p (selX m p s))) 1 :=
  (typed_sndT (typed_U0 hΓ) (typed_selFam hΓ hp) hs).cast (subst_selFam m p _)

theorem typed_bfam : Typed (Γ.snoc PairP 1) (bfam m) (univ 1) 2 := by
  have hΓ1 : CtxOk (Γ.snoc PairP 1) := CtxOk.snoc hΓ (typed_PairP hΓ)
  have hp : Typed (Γ.snoc PairP 1) (var m) PairP 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_PairP]) (by simp [Ctx.snoc])
  exact typed_liftT (typed_truncT (typed_Sel hΓ1 hp))

theorem typed_IdxT : Typed Γ (IdxT m) (univ 1) 2 := typed_sigT (typed_PairP hΓ) (typed_bfam hΓ)

theorem typed_mkIdx {p w : Term} (hp : Typed Γ p PairP 1) (hw : Typed Γ w (liftT (truncT (Sel m p))) 1) :
    Typed Γ (mkIdx m p w) (IdxT m) 1 :=
  typed_pairT (typed_PairP hΓ) (typed_bfam hΓ) hp (hw.cast (subst_bfam m p).symm)

theorem typed_ifst {s : Term} (hs : Typed Γ s (IdxT m) 1) : Typed Γ (ifst m s) PairP 1 :=
  typed_fstT (typed_PairP hΓ) (typed_bfam hΓ) hs

theorem typed_isnd {s : Term} (hs : Typed Γ s (IdxT m) 1) :
    Typed Γ (isnd m s) (liftT (truncT (Sel m (ifst m s)))) 1 :=
  (typed_sndT (typed_PairP hΓ) (typed_bfam hΓ) hs).cast (subst_bfam m _)

theorem typed_cfam : Typed (Γ.snoc (IdxT m) 1) (cfam m) (univ 1) 2 := by
  have hΓ1 : CtxOk (Γ.snoc (IdxT m) 1) := CtxOk.snoc hΓ (typed_IdxT hΓ)
  have hq : Typed (Γ.snoc (IdxT m) 1) (var m) (IdxT (m + 1)) 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_IdxT]) (by simp [Ctx.snoc])
  exact typed_Sel hΓ1 (typed_ifst hΓ1 hq)

theorem typed_cfamL : Typed Γ (cfamL m) (pi .data 1 2 (IdxT m) (univ 1)) 2 :=
  typed_fam (typed_IdxT hΓ) (typed_cfam hΓ)

theorem typed_hInh : Typed Γ (hInh m) (pi .prop 1 0 (IdxT m) (truncT (app .data 2 (cfamL (m + 1)) (var m)))) 0 := by
  have hΓ1 : CtxOk (Γ.snoc (IdxT m) 1) := CtxOk.snoc hΓ (typed_IdxT hΓ)
  have hq : Typed (Γ.snoc (IdxT m) 1) (var m) (IdxT (m + 1)) 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_IdxT]) (by simp [Ctx.snoc])
  refine Typed.lamProp (typed_IdxT hΓ) ?_
  have hbody : Typed (Γ.snoc (IdxT m) 1) (downT (truncT (cfam m)) (isnd (m + 1) (var m))) (truncT (cfam m)) 0 :=
    typed_downT (typed_truncT (typed_cfam hΓ)) (typed_isnd hΓ1 hq)
  refine hbody.conv ?_
  refine DefEq.congrPrim (.trunc 1) ![cfam m] ![app .data 2 (cfamL (m + 1)) (var m)] trivial ?_
  intro k
  match k with
  | 0 =>
    refine DefEq.symm ?_
    have h := DefEq.betaData (by decide) (typed_IdxT hΓ1) (typed_cfam hΓ1) hq
    exact h.castS (subst_cfam m)

theorem typed_choiceTm : Typed Γ (choiceTm m) (truncT (FunTy m)) 0 := by
  have h := Typed.prim (.choice 1 1) ![IdxT m, cfamL m, hInh m] (le_refl 1)
    (fun k => match k with
      | 0 => typed_IdxT hΓ
      | 1 => typed_cfamL hΓ
      | 2 => (typed_hInh hΓ).cast (by
          show _ = pi .prop 1 0 (IdxT m) (prim (.trunc 1) ![app .data 2 (shift m 1 (cfamL m)) (var m)])
          rw [shift_cfamL]
          rfl))
  refine h.cast ?_
  show prim (.trunc 1) ![pi .data 1 1 (IdxT m) (app .data 2 (shift m 1 (cfamL m)) (var m))] = _
  rw [shift_cfamL]
  rfl

/-- Applying the choice function. -/
theorem typed_appF {f q : Term} (hf : Typed Γ f (FunTy m) 1) (hq : Typed Γ q (IdxT m) 1) :
    Typed Γ (app .data 1 f q) (Sel m (ifst m q)) 1 := by
  have h := Typed.appData (le_refl 1) hf hq
  rw [subst_funBody] at h
  exact (betaTy (typed_IdxT hΓ) (typed_cfam hΓ) hq h).cast (subst_cfam' m q)

theorem typed_FunTy : Typed Γ (FunTy m) (univ 1) 2 := by
  have hΓ1 : CtxOk (Γ.snoc (IdxT m) 1) := CtxOk.snoc hΓ (typed_IdxT hΓ)
  have hq : Typed (Γ.snoc (IdxT m) 1) (var m) (IdxT (m + 1)) 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_IdxT]) (by simp [Ctx.snoc])
  have h := Typed.appData (i := 1) (j := 2) (by decide) (typed_cfamL hΓ1) hq
  exact Typed.piData (le_refl 1) (typed_IdxT hΓ) h

end Fam

/-! ### The terms of the argument, at depth `d` (`P = var 0`, `nn = var 1`, `f = var 2`) -/

def pairU : Term := mkPair TrueT (var 0)
def pairV : Term := mkPair (var 0) TrueT
def eqTT : Term := eqT U0 TrueT TrueT
def eqFF : Term := eqT U0 FalseT FalseT
/-- `True ∈ pairU`: `inl ⟨refl, trivial⟩`. -/
def memU (d : ℕ) : Term :=
  inlT d (andT d eqTT (pfst pairU)) (andT d (eqT U0 TrueT FalseT) (psnd pairU))
    (andI d eqTT (pfst pairU) (reflT U0 TrueT) (trivT d))
/-- `False ∈ pairV`: `inr ⟨refl, trivial⟩`. -/
def memV (d : ℕ) : Term :=
  inrT d (andT d (eqT U0 TrueT FalseT) (pfst pairV)) (andT d eqFF (psnd pairV))
    (andI d eqFF (psnd pairV) (reflT U0 FalseT) (trivT d))
def selU (d : ℕ) : Term := mkSel d pairU TrueT (upT (memP d pairU TrueT) (memU d))
def selV (d : ℕ) : Term := mkSel d pairV FalseT (upT (memP d pairV FalseT) (memV d))
def wU (d : ℕ) : Term := upT (truncT (Sel d pairU)) (truncMkT (Sel d pairU) (selU d))
def wV (d : ℕ) : Term := upT (truncT (Sel d pairV)) (truncMkT (Sel d pairV) (selV d))
def pU (d : ℕ) : Term := mkIdx d pairU (wU d)
def pV (d : ℕ) : Term := mkIdx d pairV (wV d)
def fU (d : ℕ) : Term := app .data 1 (var 2) (pU d)
def fV (d : ℕ) : Term := app .data 1 (var 2) (pV d)
def xU (d : ℕ) : Term := selX d (ifst d (pU d)) (fU d)
def xV (d : ℕ) : Term := selX d (ifst d (pV d)) (fV d)
def hU (d : ℕ) : Term := downT (memP d (ifst d (pU d)) (xU d)) (selW d (ifst d (pU d)) (fU d))
def hV (d : ℕ) : Term := downT (memP d (ifst d (pV d)) (xV d)) (selW d (ifst d (pV d)) (fV d))
/-- The two disjuncts of `hU` and of `hV`. -/
def AU (d : ℕ) : Term := andT d (eqT U0 TrueT (xU d)) (pfst (ifst d (pU d)))
def BU (d : ℕ) : Term := andT d (eqT U0 (xU d) FalseT) (psnd (ifst d (pU d)))
def AV (d : ℕ) : Term := andT d (eqT U0 TrueT (xV d)) (pfst (ifst d (pV d)))
def BV (d : ℕ) : Term := andT d (eqT U0 (xV d) FalseT) (psnd (ifst d (pV d)))

section Terms
variable {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ) (hP : Typed Γ (var 0) U0 1) (hf : Typed Γ (var 2) (FunTy m) 1)
include hΓ hP

theorem typed_pairU : Typed Γ pairU PairP 1 := typed_mkPair hΓ (typed_TrueT hΓ) hP
theorem typed_pairV : Typed Γ pairV PairP 1 := typed_mkPair hΓ hP (typed_TrueT hΓ)

/-- `pfst (pairU) ≡ True`. -/
theorem defEq_pfst_pairU : DefEq Γ (pfst pairU) TrueT U0 1 :=
  DefEq.sigmaFst (le_refl 1) (fun k => match k with
    | 0 => typed_U0 hΓ
    | 1 => typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    | 2 => typed_TrueT hΓ
    | 3 => betaTyRev (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) (typed_TrueT hΓ) hP)

/-- `psnd (pairV) ≡ True`. -/
theorem defEq_psnd_pairV : DefEq Γ (psnd pairV) TrueT U0 1 := by
  have h := DefEq.sigmaSnd (i := 1) (j := 1) (le_refl 1) (fun k => match k with
    | 0 => typed_U0 hΓ
    | 1 => typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    | 2 => hP
    | 3 => betaTyRev (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) hP (typed_TrueT hΓ))
  refine DefEq.conv h ?_
  exact DefEq.betaData (by decide) (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    (typed_pfst hΓ (typed_pairV hΓ hP))

/-- `pfst (pairV) ≡ P`. -/
theorem defEq_pfst_pairV : DefEq Γ (pfst pairV) (var 0) U0 1 :=
  DefEq.sigmaFst (le_refl 1) (fun k => match k with
    | 0 => typed_U0 hΓ
    | 1 => typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    | 2 => hP
    | 3 => betaTyRev (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) hP (typed_TrueT hΓ))

/-- `psnd (pairU) ≡ P`. -/
theorem defEq_psnd_pairU : DefEq Γ (psnd pairU) (var 0) U0 1 := by
  have h := DefEq.sigmaSnd (i := 1) (j := 1) (le_refl 1) (fun k => match k with
    | 0 => typed_U0 hΓ
    | 1 => typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    | 2 => typed_TrueT hΓ
    | 3 => betaTyRev (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ))) (typed_TrueT hΓ) hP)
  refine DefEq.conv h ?_
  exact DefEq.betaData (by decide) (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    (typed_pfst hΓ (typed_pairU hΓ hP))

theorem typed_memU : Typed Γ (memU m) (memP m pairU TrueT) 0 := by
  have hpU := typed_pairU hΓ hP
  have hEq : Typed Γ eqTT (univ 0) 1 := typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_TrueT hΓ)
  have hEq' : Typed Γ (eqT U0 TrueT FalseT) (univ 0) 1 := typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_false hΓ)
  have htU : Typed Γ (trivT m) (pfst pairU) 0 :=
    (typed_trivT hΓ).conv (DefEq.symm (defEq_pfst_pairU hΓ hP))
  exact typed_inlT hΓ (typed_andT hΓ hEq (typed_pfst hΓ hpU)) (typed_andT hΓ hEq' (typed_psnd hΓ hpU))
    (typed_andI hΓ hEq (typed_pfst hΓ hpU) (typed_reflT (typed_U0 hΓ) (typed_TrueT hΓ)) htU)

theorem typed_memV : Typed Γ (memV m) (memP m pairV FalseT) 0 := by
  have hpV := typed_pairV hΓ hP
  have hEq : Typed Γ eqFF (univ 0) 1 := typed_eqT (typed_U0 hΓ) (typed_false hΓ) (typed_false hΓ)
  have hEq' : Typed Γ (eqT U0 TrueT FalseT) (univ 0) 1 := typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_false hΓ)
  have htV : Typed Γ (trivT m) (psnd pairV) 0 :=
    (typed_trivT hΓ).conv (DefEq.symm (defEq_psnd_pairV hΓ hP))
  exact typed_inrT hΓ (typed_andT hΓ hEq' (typed_pfst hΓ hpV)) (typed_andT hΓ hEq (typed_psnd hΓ hpV))
    (typed_andI hΓ hEq (typed_psnd hΓ hpV) (typed_reflT (typed_U0 hΓ) (typed_false hΓ)) htV)

theorem typed_selU : Typed Γ (selU m) (Sel m pairU) 1 :=
  typed_mkSel hΓ (typed_pairU hΓ hP) (typed_TrueT hΓ)
    (typed_upT (typed_memP hΓ (typed_pairU hΓ hP) (typed_TrueT hΓ)) (typed_memU hΓ hP))

theorem typed_selV : Typed Γ (selV m) (Sel m pairV) 1 :=
  typed_mkSel hΓ (typed_pairV hΓ hP) (typed_false hΓ)
    (typed_upT (typed_memP hΓ (typed_pairV hΓ hP) (typed_false hΓ)) (typed_memV hΓ hP))

theorem typed_wU : Typed Γ (wU m) (liftT (truncT (Sel m pairU))) 1 :=
  typed_upT (typed_truncT (typed_Sel hΓ (typed_pairU hΓ hP)))
    (typed_truncMkT (typed_Sel hΓ (typed_pairU hΓ hP)) (typed_selU hΓ hP))

theorem typed_wV : Typed Γ (wV m) (liftT (truncT (Sel m pairV))) 1 :=
  typed_upT (typed_truncT (typed_Sel hΓ (typed_pairV hΓ hP)))
    (typed_truncMkT (typed_Sel hΓ (typed_pairV hΓ hP)) (typed_selV hΓ hP))

theorem typed_pU : Typed Γ (pU m) (IdxT m) 1 := typed_mkIdx hΓ (typed_pairU hΓ hP) (typed_wU hΓ hP)
theorem typed_pV : Typed Γ (pV m) (IdxT m) 1 := typed_mkIdx hΓ (typed_pairV hΓ hP) (typed_wV hΓ hP)

/-- `ifst (pU) ≡ pairU`. -/
theorem defEq_ifst_pU : DefEq Γ (ifst m (pU m)) pairU PairP 1 :=
  DefEq.sigmaFst (le_refl 1) (fun k => match k with
    | 0 => typed_PairP hΓ
    | 1 => typed_fam (typed_PairP hΓ) (typed_bfam hΓ)
    | 2 => typed_pairU hΓ hP
    | 3 => betaTyRev (typed_PairP hΓ) (typed_bfam hΓ) (typed_pairU hΓ hP)
        ((typed_wU hΓ hP).cast (subst_bfam m _).symm))

theorem defEq_ifst_pV : DefEq Γ (ifst m (pV m)) pairV PairP 1 :=
  DefEq.sigmaFst (le_refl 1) (fun k => match k with
    | 0 => typed_PairP hΓ
    | 1 => typed_fam (typed_PairP hΓ) (typed_bfam hΓ)
    | 2 => typed_pairV hΓ hP
    | 3 => betaTyRev (typed_PairP hΓ) (typed_bfam hΓ) (typed_pairV hΓ hP)
        ((typed_wV hΓ hP).cast (subst_bfam m _).symm))

/-- `psnd (ifst pU) ≡ P`. -/
theorem defEq_psnd_ifst_pU : DefEq Γ (psnd (ifst m (pU m))) (var 0) U0 1 := by
  have hB := typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
  have h1 := DefEq.congrPrim (.snd 1 1) ![U0, lam .data 1 2 U0 U0, ifst m (pU m)]
    ![U0, lam .data 1 2 U0 U0, pairU] trivial (fun k => match k with
      | 0 => DefEq.refl (typed_U0 hΓ)
      | 1 => DefEq.refl hB
      | 2 => defEq_ifst_pU hΓ hP)
  have h2 := DefEq.conv h1 (DefEq.betaData (by decide) (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
    (typed_pfst hΓ (typed_ifst hΓ (typed_pU hΓ hP))))
  exact DefEq.trans h2 (defEq_psnd_pairU hΓ hP)

/-- `pfst (ifst pV) ≡ P`. -/
theorem defEq_pfst_ifst_pV : DefEq Γ (pfst (ifst m (pV m))) (var 0) U0 1 := by
  have hB := typed_fam (typed_U0 hΓ) (typed_U0 (CtxOk.snoc hΓ (typed_U0 hΓ)))
  have h1 := DefEq.congrPrim (.fst 1 1) ![U0, lam .data 1 2 U0 U0, ifst m (pV m)]
    ![U0, lam .data 1 2 U0 U0, pairV] trivial (fun k => match k with
      | 0 => DefEq.refl (typed_U0 hΓ)
      | 1 => DefEq.refl hB
      | 2 => defEq_ifst_pV hΓ hP)
  exact DefEq.trans h1 (defEq_pfst_pairV hΓ hP)

include hf

theorem typed_fU : Typed Γ (fU m) (Sel m (ifst m (pU m))) 1 := typed_appF hΓ hf (typed_pU hΓ hP)
theorem typed_fV : Typed Γ (fV m) (Sel m (ifst m (pV m))) 1 := typed_appF hΓ hf (typed_pV hΓ hP)
theorem typed_xU : Typed Γ (xU m) U0 1 := typed_selX hΓ (typed_ifst hΓ (typed_pU hΓ hP)) (typed_fU hΓ hP hf)
theorem typed_xV : Typed Γ (xV m) U0 1 := typed_selX hΓ (typed_ifst hΓ (typed_pV hΓ hP)) (typed_fV hΓ hP hf)
theorem typed_hU : Typed Γ (hU m) (memP m (ifst m (pU m)) (xU m)) 0 :=
  typed_downT (typed_memP hΓ (typed_ifst hΓ (typed_pU hΓ hP)) (typed_xU hΓ hP hf))
    (typed_selW hΓ (typed_ifst hΓ (typed_pU hΓ hP)) (typed_fU hΓ hP hf))
theorem typed_hV : Typed Γ (hV m) (memP m (ifst m (pV m)) (xV m)) 0 :=
  typed_downT (typed_memP hΓ (typed_ifst hΓ (typed_pV hΓ hP)) (typed_xV hΓ hP hf))
    (typed_selW hΓ (typed_ifst hΓ (typed_pV hΓ hP)) (typed_fV hΓ hP hf))

theorem typed_AU : Typed Γ (AU m) (univ 0) 1 :=
  typed_andT hΓ (typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_xU hΓ hP hf))
    (typed_pfst hΓ (typed_ifst hΓ (typed_pU hΓ hP)))
theorem typed_BU : Typed Γ (BU m) (univ 0) 1 :=
  typed_andT hΓ (typed_eqT (typed_U0 hΓ) (typed_xU hΓ hP hf) (typed_false hΓ))
    (typed_psnd hΓ (typed_ifst hΓ (typed_pU hΓ hP)))
theorem typed_AV : Typed Γ (AV m) (univ 0) 1 :=
  typed_andT hΓ (typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_xV hΓ hP hf))
    (typed_pfst hΓ (typed_ifst hΓ (typed_pV hΓ hP)))
theorem typed_BV : Typed Γ (BV m) (univ 0) 1 :=
  typed_andT hΓ (typed_eqT (typed_U0 hΓ) (typed_xV hΓ hP hf) (typed_false hΓ))
    (typed_psnd hΓ (typed_ifst hΓ (typed_pV hΓ hP)))

/-- From `b : BU`, `P`. -/
theorem typed_PfromBU {b : Term} (hb : Typed Γ b (BU m) 0) :
    Typed Γ (andE2 m b (eqT U0 (xU m) FalseT) (psnd (ifst m (pU m)))) (var 0) 0 :=
  (typed_andE2 hΓ (typed_eqT (typed_U0 hΓ) (typed_xU hΓ hP hf) (typed_false hΓ))
    (typed_psnd hΓ (typed_ifst hΓ (typed_pU hΓ hP))) hb).conv (defEq_psnd_ifst_pU hΓ hP)

/-- From `a : AV`, `P`. -/
theorem typed_PfromAV {a : Term} (ha : Typed Γ a (AV m) 0) :
    Typed Γ (andE2 m a (eqT U0 TrueT (xV m)) (pfst (ifst m (pV m)))) (var 0) 0 :=
  (typed_andE2 hΓ (typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_xV hΓ hP hf))
    (typed_pfst hΓ (typed_ifst hΓ (typed_pV hΓ hP))) ha).conv (defEq_pfst_ifst_pV hΓ hP)

/-- The first components. -/
theorem typed_eq_of_AU {a : Term} (ha : Typed Γ a (AU m) 0) :
    Typed Γ (andE1 m a (eqT U0 TrueT (xU m)) (pfst (ifst m (pU m)))) (eqT U0 TrueT (xU m)) 0 :=
  typed_andE1 hΓ (typed_eqT (typed_U0 hΓ) (typed_TrueT hΓ) (typed_xU hΓ hP hf))
    (typed_pfst hΓ (typed_ifst hΓ (typed_pU hΓ hP))) ha

theorem typed_eq_of_BV {b : Term} (hb : Typed Γ b (BV m) 0) :
    Typed Γ (andE1 m b (eqT U0 (xV m) FalseT) (psnd (ifst m (pV m)))) (eqT U0 (xV m) FalseT) 0 :=
  typed_andE1 hΓ (typed_eqT (typed_U0 hΓ) (typed_xV hΓ hP hf) (typed_false hΓ))
    (typed_psnd hΓ (typed_ifst hΓ (typed_pV hΓ hP))) hb

end Terms


/-! ### Shifts and substitutions on the encoded terms, compositionally -/

section Lib

@[diac_simps] theorem shift_var_lt (d k x : ℕ) (h : x < d) : shift d k (var x) = var x := by
  simp [shift, h]
@[diac_simps] theorem shift_var_ge (d k x : ℕ) (h : d ≤ x) : shift d k (var x) = var (x + k) := by
  simp [shift, Nat.not_lt.2 h]
@[diac_simps] theorem subst_var_lt' (m e x : ℕ) (a : Term) (h : x < m) : subst m a e (var x) = var x := by
  simp [subst, h]
@[diac_simps] theorem subst_var_eq (m e : ℕ) (a : Term) : subst m a e (var m) = shift m e a := by
  simp [subst]
@[diac_simps] theorem subst_var_gt (m e x : ℕ) (a : Term) (h : m < x) : subst m a e (var x) = var (x - 1) := by
  simp [subst, Nat.not_lt.2 h.le, h.ne']
@[diac_simps] theorem shift_pi (d k : ℕ) (b : Kind) (i j : ℕ) (A B : Term) :
    shift d k (pi b i j A B) = pi b i j (shift d k A) (shift d k B) := rfl
@[diac_simps] theorem shift_lam (d k : ℕ) (b : Kind) (i j : ℕ) (A t : Term) :
    shift d k (lam b i j A t) = lam b i j (shift d k A) (shift d k t) := rfl
@[diac_simps] theorem shift_app (d k : ℕ) (b : Kind) (j : ℕ) (f a : Term) :
    shift d k (app b j f a) = app b j (shift d k f) (shift d k a) := rfl
@[diac_simps] theorem shift_univ (d k n : ℕ) : shift d k (univ n) = univ n := rfl
@[diac_simps] theorem subst_pi (m e : ℕ) (a : Term) (b : Kind) (i j : ℕ) (A B : Term) :
    subst m a e (pi b i j A B) = pi b i j (subst m a e A) (subst m a (e + 1) B) := rfl
@[diac_simps] theorem subst_lam (m e : ℕ) (a : Term) (b : Kind) (i j : ℕ) (A t : Term) :
    subst m a e (lam b i j A t) = lam b i j (subst m a e A) (subst m a (e + 1) t) := rfl
@[diac_simps] theorem subst_app (m e : ℕ) (a : Term) (b : Kind) (j : ℕ) (f x : Term) :
    subst m a e (app b j f x) = app b j (subst m a e f) (subst m a e x) := rfl
@[diac_simps] theorem subst_univ (m e : ℕ) (a : Term) (n : ℕ) : subst m a e (univ n) = univ n := rfl

attribute [diac_simps] shift_zero shift_U0 subst_U0 shift_FalseT subst_FalseT shift_TrueT subst_TrueT
  shift_PairP subst_PairP shift_notT subst_notT

/-- Shifts at different indices commute. -/
theorem shift_comm (d d' k e : ℕ) (h : d ≤ d') :
    ∀ t : Term, shift d k (shift d' e t) = shift (d' + k) e (shift d k t)
  | var x => by
    by_cases h1 : x < d
    · have h2 : x < d' := by omega
      have h3 : x < d' + k := by omega
      simp only [shift, h1, h2, h3, ite_true]
    · by_cases h2 : x < d'
      · have h3 : x + k < d' + k := by omega
        simp only [shift, h1, h2, h3, ite_true, ite_false]
      · have h3 : ¬ x + e < d := by omega
        have h4 : ¬ x + k < d' + k := by omega
        simp only [shift, h1, h2, h3, h4, ite_false]
        rw [Nat.add_right_comm]
  | univ _ => rfl
  | pi k' i j A B => by simp only [shift, shift_comm d d' k e h A, shift_comm d d' k e h B]
  | lam k' i j A b => by simp only [shift, shift_comm d d' k e h A, shift_comm d d' k e h b]
  | app k' j f a => by simp only [shift, shift_comm d d' k e h f, shift_comm d d' k e h a]
  | letE j A v b => by
    simp only [shift, shift_comm d d' k e h A, shift_comm d d' k e h v, shift_comm d d' k e h b]
  | prim c args => by
    simp only [shift]
    congr 1
    funext k'
    exact shift_comm d d' k e h (args k')

/-- Two shifts at overlapping indices merge. -/
theorem shift_shift'' (n n' e₁ e₂ : ℕ) (h1 : n ≤ n') (h2 : n' ≤ n + e₁) (t : Term) :
    shift n' e₂ (shift n e₁ t) = shift n (e₁ + e₂) t := by
  obtain ⟨k, rfl⟩ : ∃ k, n' = n + k := ⟨n' - n, by omega⟩
  exact shift_shift' n k e₁ e₂ (by omega) t

/-- Substitution passes through a shift of a term of the right depth. -/
theorem subst_shift_comm (m e' k d : ℕ) (a : Term) (hk : k ≤ e') (h1 : m < d)
    (h2 : d ≤ m + 1 + (e' - k)) :
    ∀ t : Term, subst m a e' (shift d k t) = shift (d - 1) k (subst m a (e' - k) t)
  | var x => by
    by_cases hx : x < m
    · have hd : x < d := by omega
      have hd' : x < d - 1 := by omega
      simp only [shift, subst, hx, hd, hd', ite_true]
    · by_cases hm : x = m
      · subst hm
        have hd : x < d := h1
        simp only [shift, subst, hd, hx, ite_true, ite_false]
        have e : d - 1 = x + (d - 1 - x) := by omega
        rw [e, shift_shift' x (d - 1 - x) (e' - k) k (by omega), Nat.sub_add_cancel hk]
      · have hgt : m < x := by omega
        by_cases hd : x < d
        · have hd' : x - 1 < d - 1 := by omega
          simp only [shift, subst, hx, hm, hd, hd', ite_true, ite_false]
        · have h3 : ¬ x + k < m := by omega
          have h4 : ¬ x + k = m := by omega
          have h5 : ¬ x - 1 < d - 1 := by omega
          simp only [shift, subst, hx, hm, hd, h3, h4, h5, ite_false]
          congr 1
          omega
  | univ _ => rfl
  | pi k' i j A B => by
    simp only [shift, subst, subst_shift_comm m e' k d a hk h1 h2 A]
    rw [subst_shift_comm m (e' + 1) k d a (by omega) h1 (by omega) B,
      show e' + 1 - k = e' - k + 1 by omega]
  | lam k' i j A b => by
    simp only [shift, subst, subst_shift_comm m e' k d a hk h1 h2 A]
    rw [subst_shift_comm m (e' + 1) k d a (by omega) h1 (by omega) b,
      show e' + 1 - k = e' - k + 1 by omega]
  | app k' j f x => by
    simp only [shift, subst, subst_shift_comm m e' k d a hk h1 h2 f, subst_shift_comm m e' k d a hk h1 h2 x]
  | letE j A v b => by
    simp only [shift, subst, subst_shift_comm m e' k d a hk h1 h2 A, subst_shift_comm m e' k d a hk h1 h2 v]
    rw [subst_shift_comm m (e' + 1) k d a (by omega) h1 (by omega) b,
      show e' + 1 - k = e' - k + 1 by omega]
  | prim c args => by
    simp only [shift, subst]
    congr 1
    funext k'
    exact subst_shift_comm m e' k d a hk h1 h2 (args k')

attribute [diac_simps] shift_comm shift_shift'' subst_shift_comm

/-- The normalization of shifts and substitutions on the encoded terms. -/
macro "calc_simp" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| (simp (disch := omega) only [diac_simps, Nat.add_sub_cancel, Nat.add_sub_cancel_left,
      Nat.sub_add_cancel, Nat.add_assoc, Nat.reduceAdd, Nat.reduceSub, Nat.reduceSubDiff, Nat.add_zero,
      Nat.zero_add, Nat.sub_zero, Nat.add_one_sub_one, vecFun_cons, vecFun_empty] $[$loc]? <;>
    try simp only [Nat.add_comm, Nat.add_left_comm] $[$loc]?))

/-! The generic wrappers. -/

@[diac_simps] theorem shift_eqT (d k : ℕ) (A a b : Term) :
    shift d k (eqT A a b) = eqT (shift d k A) (shift d k a) (shift d k b) := by
  simp only [eqT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_eqT (m e : ℕ) (x A a b : Term) :
    subst m x e (eqT A a b) = eqT (subst m x e A) (subst m x e a) (subst m x e b) := by
  simp only [eqT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_reflT (d k : ℕ) (A a : Term) :
    shift d k (reflT A a) = reflT (shift d k A) (shift d k a) := by
  simp only [reflT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_reflT (m e : ℕ) (x A a : Term) :
    subst m x e (reflT A a) = reflT (subst m x e A) (subst m x e a) := by
  simp only [reflT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_liftT (d k : ℕ) (Q : Term) : shift d k (liftT Q) = liftT (shift d k Q) := by
  simp only [liftT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_liftT (m e : ℕ) (x Q : Term) : subst m x e (liftT Q) = liftT (subst m x e Q) := by
  simp only [liftT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_upT (d k : ℕ) (Q q : Term) :
    shift d k (upT Q q) = upT (shift d k Q) (shift d k q) := by
  simp only [upT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_upT (m e : ℕ) (x Q q : Term) :
    subst m x e (upT Q q) = upT (subst m x e Q) (subst m x e q) := by
  simp only [upT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_downT (d k : ℕ) (Q q : Term) :
    shift d k (downT Q q) = downT (shift d k Q) (shift d k q) := by
  simp only [downT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_downT (m e : ℕ) (x Q q : Term) :
    subst m x e (downT Q q) = downT (subst m x e Q) (subst m x e q) := by
  simp only [downT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_truncT (d k : ℕ) (X : Term) : shift d k (truncT X) = truncT (shift d k X) := by
  simp only [truncT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_truncT (m e : ℕ) (x X : Term) :
    subst m x e (truncT X) = truncT (subst m x e X) := by
  simp only [truncT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_truncMkT (d k : ℕ) (X t : Term) :
    shift d k (truncMkT X t) = truncMkT (shift d k X) (shift d k t) := by
  simp only [truncMkT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_truncMkT (m e : ℕ) (x X t : Term) :
    subst m x e (truncMkT X t) = truncMkT (subst m x e X) (subst m x e t) := by
  simp only [truncMkT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_sigT (d k : ℕ) (A Bb : Term) :
    shift d k (sigT A Bb) = sigT (shift d k A) (shift d k Bb) := by
  simp only [sigT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_sigT (m e : ℕ) (x A Bb : Term) :
    subst m x e (sigT A Bb) = sigT (subst m x e A) (subst m x (e + 1) Bb) := by
  simp only [sigT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_pairT (d k : ℕ) (A Bb a b : Term) :
    shift d k (pairT A Bb a b) = pairT (shift d k A) (shift d k Bb) (shift d k a) (shift d k b) := by
  simp only [pairT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_pairT (m e : ℕ) (x A Bb a b : Term) :
    subst m x e (pairT A Bb a b) =
      pairT (subst m x e A) (subst m x (e + 1) Bb) (subst m x e a) (subst m x e b) := by
  simp only [pairT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_fstT (d k : ℕ) (A Bb s : Term) :
    shift d k (fstT A Bb s) = fstT (shift d k A) (shift d k Bb) (shift d k s) := by
  simp only [fstT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_fstT (m e : ℕ) (x A Bb s : Term) :
    subst m x e (fstT A Bb s) = fstT (subst m x e A) (subst m x (e + 1) Bb) (subst m x e s) := by
  simp only [fstT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_sndT (d k : ℕ) (A Bb s : Term) :
    shift d k (sndT A Bb s) = sndT (shift d k A) (shift d k Bb) (shift d k s) := by
  simp only [sndT, shift, vecFun_cons, vecFun_empty]
@[diac_simps] theorem subst_sndT (m e : ℕ) (x A Bb s : Term) :
    subst m x e (sndT A Bb s) = sndT (subst m x e A) (subst m x (e + 1) Bb) (subst m x e s) := by
  simp only [sndT, subst, vecFun_cons, vecFun_empty]
@[diac_simps] theorem shift_pfst (d k : ℕ) (s : Term) : shift d k (pfst s) = pfst (shift d k s) := by
  simp only [pfst, shift_fstT, shift_U0]
@[diac_simps] theorem subst_pfst (m e : ℕ) (x s : Term) : subst m x e (pfst s) = pfst (subst m x e s) := by
  simp only [pfst, subst_fstT, subst_U0]
@[diac_simps] theorem shift_psnd (d k : ℕ) (s : Term) : shift d k (psnd s) = psnd (shift d k s) := by
  simp only [psnd, shift_sndT, shift_U0]
@[diac_simps] theorem subst_psnd (m e : ℕ) (x s : Term) : subst m x e (psnd s) = psnd (subst m x e s) := by
  simp only [psnd, subst_sndT, subst_U0]
@[diac_simps] theorem shift_mkPair (d k : ℕ) (a b : Term) :
    shift d k (mkPair a b) = mkPair (shift d k a) (shift d k b) := by
  simp only [mkPair, shift_pairT, shift_U0]
@[diac_simps] theorem subst_mkPair (m e : ℕ) (x a b : Term) :
    subst m x e (mkPair a b) = mkPair (subst m x e a) (subst m x e b) := by
  simp only [mkPair, subst_pairT, subst_U0]

/-! The depth-indexed encodings, shifted at a lower index. -/

@[diac_simps] theorem shift_orT' (d d' k : ℕ) (h : d ≤ d') (A B : Term) :
    shift d k (orT d' A B) = orT (d' + k) (shift d k A) (shift d k B) := by
  unfold orT; calc_simp
@[diac_simps] theorem shift_andT' (d d' k : ℕ) (h : d ≤ d') (A B : Term) :
    shift d k (andT d' A B) = andT (d' + k) (shift d k A) (shift d k B) := by
  unfold andT; calc_simp
@[diac_simps] theorem shift_inlT' (d d' k : ℕ) (h : d ≤ d') (A B a : Term) :
    shift d k (inlT d' A B a) = inlT (d' + k) (shift d k A) (shift d k B) (shift d k a) := by
  unfold inlT; calc_simp
@[diac_simps] theorem shift_inrT' (d d' k : ℕ) (h : d ≤ d') (A B b : Term) :
    shift d k (inrT d' A B b) = inrT (d' + k) (shift d k A) (shift d k B) (shift d k b) := by
  unfold inrT; calc_simp
@[diac_simps] theorem shift_andI' (d d' k : ℕ) (h : d ≤ d') (A B a b : Term) :
    shift d k (andI d' A B a b) = andI (d' + k) (shift d k A) (shift d k B) (shift d k a) (shift d k b) := by
  unfold andI; calc_simp
@[diac_simps] theorem shift_trivT' (d d' k : ℕ) (h : d ≤ d') : shift d k (trivT d') = trivT (d' + k) := by
  unfold trivT; calc_simp
@[diac_simps] theorem shift_memP' (d d' k : ℕ) (h : d ≤ d') (p x : Term) :
    shift d k (memP d' p x) = memP (d' + k) (shift d k p) (shift d k x) := by
  unfold memP; calc_simp
@[diac_simps] theorem shift_selFam' (d d' k : ℕ) (h : d ≤ d') (p : Term) :
    shift d k (selFam d' p) = selFam (d' + k) (shift d k p) := by
  unfold selFam; calc_simp
@[diac_simps] theorem shift_Sel' (d d' k : ℕ) (h : d ≤ d') (p : Term) :
    shift d k (Sel d' p) = Sel (d' + k) (shift d k p) := by
  unfold Sel; calc_simp
@[diac_simps] theorem shift_mkSel' (d d' k : ℕ) (h : d ≤ d') (p x w : Term) :
    shift d k (mkSel d' p x w) = mkSel (d' + k) (shift d k p) (shift d k x) (shift d k w) := by
  unfold mkSel; calc_simp
@[diac_simps] theorem shift_selX' (d d' k : ℕ) (h : d ≤ d') (p s : Term) :
    shift d k (selX d' p s) = selX (d' + k) (shift d k p) (shift d k s) := by
  unfold selX; calc_simp
@[diac_simps] theorem shift_selW' (d d' k : ℕ) (h : d ≤ d') (p s : Term) :
    shift d k (selW d' p s) = selW (d' + k) (shift d k p) (shift d k s) := by
  unfold selW; calc_simp
@[diac_simps] theorem shift_bfam' (d d' k : ℕ) (h : d ≤ d') : shift d k (bfam d') = bfam (d' + k) := by
  unfold bfam; calc_simp
@[diac_simps] theorem shift_IdxT' (d d' k : ℕ) (h : d ≤ d') : shift d k (IdxT d') = IdxT (d' + k) := by
  unfold IdxT; calc_simp
@[diac_simps] theorem shift_mkIdx' (d d' k : ℕ) (h : d ≤ d') (p w : Term) :
    shift d k (mkIdx d' p w) = mkIdx (d' + k) (shift d k p) (shift d k w) := by
  unfold mkIdx; calc_simp
@[diac_simps] theorem shift_ifst' (d d' k : ℕ) (h : d ≤ d') (s : Term) :
    shift d k (ifst d' s) = ifst (d' + k) (shift d k s) := by
  unfold ifst; calc_simp
@[diac_simps] theorem shift_isnd' (d d' k : ℕ) (h : d ≤ d') (s : Term) :
    shift d k (isnd d' s) = isnd (d' + k) (shift d k s) := by
  unfold isnd; calc_simp
@[diac_simps] theorem shift_cfam' (d d' k : ℕ) (h : d ≤ d') : shift d k (cfam d') = cfam (d' + k) := by
  unfold cfam; calc_simp
@[diac_simps] theorem shift_cfamL' (d d' k : ℕ) (h : d ≤ d') : shift d k (cfamL d') = cfamL (d' + k) := by
  unfold cfamL; calc_simp
@[diac_simps] theorem shift_FunTy' (d d' k : ℕ) (h : d ≤ d') : shift d k (FunTy d') = FunTy (d' + k) := by
  unfold FunTy; calc_simp

/-! The terms of the argument. -/

@[diac_simps] theorem shift_pairU (d k : ℕ) (h : 0 < d) : shift d k pairU = pairU := by
  unfold pairU; calc_simp
@[diac_simps] theorem shift_pairV (d k : ℕ) (h : 0 < d) : shift d k pairV = pairV := by
  unfold pairV; calc_simp
@[diac_simps] theorem shift_eqTT (d k : ℕ) : shift d k eqTT = eqTT := by unfold eqTT; calc_simp
@[diac_simps] theorem shift_eqFF (d k : ℕ) : shift d k eqFF = eqFF := by unfold eqFF; calc_simp
@[diac_simps] theorem shift_memU' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (memU d') = memU (d' + k) := by
  unfold memU; calc_simp
@[diac_simps] theorem shift_memV' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (memV d') = memV (d' + k) := by
  unfold memV; calc_simp
@[diac_simps] theorem shift_selU' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (selU d') = selU (d' + k) := by
  unfold selU; calc_simp
@[diac_simps] theorem shift_selV' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (selV d') = selV (d' + k) := by
  unfold selV; calc_simp
@[diac_simps] theorem shift_wU' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (wU d') = wU (d' + k) := by
  unfold wU; calc_simp
@[diac_simps] theorem shift_wV' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (wV d') = wV (d' + k) := by
  unfold wV; calc_simp
@[diac_simps] theorem shift_pU' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (pU d') = pU (d' + k) := by
  unfold pU; calc_simp
@[diac_simps] theorem shift_pV' (d d' k : ℕ) (h0 : 0 < d) (h : d ≤ d') :
    shift d k (pV d') = pV (d' + k) := by
  unfold pV; calc_simp
@[diac_simps] theorem shift_fU' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (fU d') = fU (d' + k) := by
  unfold fU; calc_simp
@[diac_simps] theorem shift_fV' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (fV d') = fV (d' + k) := by
  unfold fV; calc_simp
@[diac_simps] theorem shift_xU' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (xU d') = xU (d' + k) := by
  unfold xU; calc_simp
@[diac_simps] theorem shift_xV' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (xV d') = xV (d' + k) := by
  unfold xV; calc_simp
@[diac_simps] theorem shift_AU' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (AU d') = AU (d' + k) := by
  unfold AU; calc_simp
@[diac_simps] theorem shift_BU' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (BU d') = BU (d' + k) := by
  unfold BU; calc_simp
@[diac_simps] theorem shift_AV' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (AV d') = AV (d' + k) := by
  unfold AV; calc_simp
@[diac_simps] theorem shift_BV' (d d' k : ℕ) (h0 : 2 < d) (h : d ≤ d') :
    shift d k (BV d') = BV (d' + k) := by
  unfold BV; calc_simp

/-! Substitution into the depth-indexed encodings (the variable `m` may occur in the arguments). -/

@[diac_simps] theorem subst_orT' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (A B : Term) :
    subst m x e (orT d A B) = orT (d - 1) (subst m x e A) (subst m x e B) := by
  unfold orT; calc_simp
@[diac_simps] theorem subst_andT' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (A B : Term) :
    subst m x e (andT d A B) = andT (d - 1) (subst m x e A) (subst m x e B) := by
  unfold andT; calc_simp
@[diac_simps] theorem subst_memP' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p y : Term) :
    subst m x e (memP d p y) = memP (d - 1) (subst m x e p) (subst m x e y) := by
  unfold memP; calc_simp
@[diac_simps] theorem subst_selFam' (m e d : ℕ) (x : Term) (h0 : 1 ≤ e) (h1 : m < d) (h2 : d ≤ m + e)
    (p : Term) : subst m x e (selFam d p) = selFam (d - 1) (subst m x (e - 1) p) := by
  unfold selFam; calc_simp
@[diac_simps] theorem subst_Sel' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p : Term) :
    subst m x e (Sel d p) = Sel (d - 1) (subst m x e p) := by
  unfold Sel; calc_simp
@[diac_simps] theorem subst_mkSel' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p y w : Term) :
    subst m x e (mkSel d p y w) = mkSel (d - 1) (subst m x e p) (subst m x e y) (subst m x e w) := by
  unfold mkSel; calc_simp
@[diac_simps] theorem subst_selX' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p s : Term) :
    subst m x e (selX d p s) = selX (d - 1) (subst m x e p) (subst m x e s) := by
  unfold selX; calc_simp
@[diac_simps] theorem subst_selW' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p s : Term) :
    subst m x e (selW d p s) = selW (d - 1) (subst m x e p) (subst m x e s) := by
  unfold selW; calc_simp
@[diac_simps] theorem subst_bfam' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + e) :
    subst m x e (bfam d) = bfam (d - 1) := by
  unfold bfam; calc_simp
@[diac_simps] theorem subst_IdxT' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) :
    subst m x e (IdxT d) = IdxT (d - 1) := by
  unfold IdxT; calc_simp
@[diac_simps] theorem subst_mkIdx' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (p w : Term) :
    subst m x e (mkIdx d p w) = mkIdx (d - 1) (subst m x e p) (subst m x e w) := by
  unfold mkIdx; calc_simp
@[diac_simps] theorem subst_ifst' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (s : Term) :
    subst m x e (ifst d s) = ifst (d - 1) (subst m x e s) := by
  unfold ifst; calc_simp
@[diac_simps] theorem subst_isnd' (m e d : ℕ) (x : Term) (h1 : m < d) (h2 : d ≤ m + 1 + e) (s : Term) :
    subst m x e (isnd d s) = isnd (d - 1) (subst m x e s) := by
  unfold isnd; calc_simp

/-! Substitution into the closed-over terms (the variable `m` does not occur). -/

@[diac_simps] theorem subst_pairU (m e : ℕ) (x : Term) (h : 0 < m) : subst m x e pairU = pairU := by
  unfold pairU; calc_simp
@[diac_simps] theorem subst_pairV (m e : ℕ) (x : Term) (h : 0 < m) : subst m x e pairV = pairV := by
  unfold pairV; calc_simp
@[diac_simps] theorem subst_wU' (m e d : ℕ) (x : Term) (h0 : 0 < m) (h : m < d) :
    subst m x e (wU d) = wU (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_wU' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_wV' (m e d : ℕ) (x : Term) (h0 : 0 < m) (h : m < d) :
    subst m x e (wV d) = wV (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_wV' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_pU' (m e d : ℕ) (x : Term) (h0 : 0 < m) (h : m < d) :
    subst m x e (pU d) = pU (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_pU' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_pV' (m e d : ℕ) (x : Term) (h0 : 0 < m) (h : m < d) :
    subst m x e (pV d) = pV (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_pV' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_xU' (m e d : ℕ) (x : Term) (h0 : 2 < m) (h : m < d) :
    subst m x e (xU d) = xU (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_xU' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_xV' (m e d : ℕ) (x : Term) (h0 : 2 < m) (h : m < d) :
    subst m x e (xV d) = xV (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_xV' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_AU' (m e d : ℕ) (x : Term) (h0 : 2 < m) (h : m < d) :
    subst m x e (AU d) = AU (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_AU' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]
@[diac_simps] theorem subst_BV' (m e d : ℕ) (x : Term) (h0 : 2 < m) (h : m < d) :
    subst m x e (BV d) = BV (d - 1) := by
  obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [← shift_BV' m d 1 h0 (by omega), subst_shift_one, Nat.add_sub_cancel]

end Lib


/-! ### Transport along an equality of propositions, and the eliminator with computed instances -/

attribute [diac_simps] subst_shift_one subst_shift_succ

section Transport
variable {m : ℕ} {Γ : Ctx m}

/-- The equality eliminator with the two instances of the motive and the result computed. -/
theorem typed_eqRec' {A a Cb c b p E : Term} (hΓ : CtxOk Γ)
    (hA : Typed Γ A (univ 1) 2) (ha : Typed Γ a A 1)
    (hE : E = eqT (shift m 1 A) (shift m 1 a) (var m))
    (hC : Typed ((Γ.snoc A 1).snoc E 0) Cb (univ 0) 1)
    {Ca : Term} (eCa : subst m a 1 Cb = Ca) (hCa : Typed (Γ.snoc (eqT A a a) 0) Ca (univ 0) 1)
    (hb : Typed Γ b A 1) (hp : Typed Γ p (eqT A a b) 0)
    {Cb' : Term} (eCb : subst m b 1 Cb = Cb') (hCb : Typed (Γ.snoc (eqT A a b) 0) Cb' (univ 0) 1)
    {Cc : Term} (eCc : subst m (reflT A a) 0 Ca = Cc) (hc : Typed Γ c Cc 0)
    {R : Term} (eR : subst m p 0 Cb' = R) :
    Typed Γ (prim (.eqRec 1 0) ![A, a, motiveT m A a Cb, c, b, p]) R 0 := by
  subst hE eCa eCb eCc eR
  exact typed_eqRec hΓ hA ha hC hCa hb hp hCb hc

/-- Transport of a proof of `a` to a proof of `b` along `p : a = b` (`a b : U_0`). -/
def transportT (m : ℕ) (a c b p : Term) : Term :=
  prim (.eqRec 1 0) ![U0, a, motiveT m U0 a (var m), c, b, p]

theorem typed_transport {a c b p : Term} (hΓ : CtxOk Γ) (ha : Typed Γ a U0 1) (hb : Typed Γ b U0 1)
    (hp : Typed Γ p (eqT U0 a b) 0) (hc : Typed Γ c a 0) : Typed Γ (transportT m a c b p) b 0 := by
  have hΓ1 : CtxOk (Γ.snoc U0 1) := CtxOk.snoc hΓ (typed_U0 hΓ)
  have hy : Typed (Γ.snoc U0 1) (var m) U0 1 :=
    typed_var' hΓ1 (Fin.last m) (by simp) (by simp [Ctx.snoc, shift_U0]) (by simp [Ctx.snoc])
  have ha1 : Typed (Γ.snoc U0 1) (shift m 1 a) U0 1 := (Typed.weak ha (typed_U0 hΓ)).cast (shift_U0 m 1)
  have hE : Typed (Γ.snoc U0 1) (eqT U0 (shift m 1 a) (var m)) (univ 0) 1 :=
    typed_eqT (typed_U0 hΓ1) ha1 hy
  have hΓ2 : CtxOk ((Γ.snoc U0 1).snoc (eqT U0 (shift m 1 a) (var m)) 0) := CtxOk.snoc hΓ1 hE
  refine typed_eqRec' hΓ (typed_U0 hΓ) ha (E := eqT U0 (shift m 1 a) (var m)) (by rw [shift_U0]) ?_
    (Ca := shift m 1 a) (by calc_simp) ?_ hb hp (Cb' := shift m 1 b) (by calc_simp) ?_ (Cc := a)
    (by calc_simp) hc (by calc_simp)
  · exact typed_var' hΓ2 (Fin.castSucc (Fin.last m)) (by simp) (by simp [Ctx.snoc, U0, Term.shift]) (by simp [Ctx.snoc])
  · exact (Typed.weak ha (typed_eqT (typed_U0 hΓ) ha ha)).cast (shift_U0 m 1)
  · exact (Typed.weak hb (typed_eqT (typed_U0 hΓ) ha hb)).cast (shift_U0 m 1)

end Transport

/-! ### The derivation -/

/-- The contexts of the derivation: `P : U_0`, `nn : ¬¬P`, `f : FunTy`, `a : AU`, `b : BV`, `p : P`. -/
def Γ0 : Ctx 0 := fun i => i.elim0
def Γ1 : Ctx 1 := Γ0.snoc U0 1
def Γ2 : Ctx 2 := Γ1.snoc (notT (notT (var 0))) 0
def Γ3 : Ctx 3 := Γ2.snoc (FunTy 2) 1
def Γ4 : Ctx 4 := Γ3.snoc (AU 3) 0
def Γ4' : Ctx 4 := Γ3.snoc (BU 3) 0
def Γ5 : Ctx 5 := Γ4.snoc (BV 4) 0
def Γ5' : Ctx 5 := Γ4.snoc (AV 4) 0
def Γ6 : Ctx 6 := Γ5.snoc (var 0) 0

section Ctxs

theorem ok1 : CtxOk Γ1 := CtxOk.snoc (CtxOk.nil _) (typed_U0 (CtxOk.nil _))
theorem P1 : Typed Γ1 (var 0) U0 1 := typed_var' ok1 0 rfl (by show shift 0 1 U0 = U0; rfl) rfl
theorem ok2 : CtxOk Γ2 := CtxOk.snoc ok1 (typed_notT ok1 (typed_notT ok1 P1))
theorem P2 : Typed Γ2 (var 0) U0 1 := typed_var' ok2 0 rfl (by show shift 0 2 U0 = U0; rfl) rfl
theorem ok3 : CtxOk Γ3 := CtxOk.snoc ok2 (typed_FunTy ok2)
theorem P3 : Typed Γ3 (var 0) U0 1 := typed_var' ok3 0 rfl (by show shift 0 3 U0 = U0; rfl) rfl
theorem F3 : Typed Γ3 (var 2) (FunTy 3) 1 :=
  typed_var' ok3 2 rfl (by show shift 2 1 (FunTy 2) = FunTy 3; calc_simp) rfl
theorem ok4 : CtxOk Γ4 := CtxOk.snoc ok3 (typed_AU ok3 P3 F3)
theorem P4 : Typed Γ4 (var 0) U0 1 := typed_var' ok4 0 rfl (by show shift 0 4 U0 = U0; rfl) rfl
theorem F4 : Typed Γ4 (var 2) (FunTy 4) 1 :=
  typed_var' ok4 2 rfl (by show shift 2 2 (FunTy 2) = FunTy 4; calc_simp) rfl
theorem ok4' : CtxOk Γ4' := CtxOk.snoc ok3 (typed_BU ok3 P3 F3)
theorem P4' : Typed Γ4' (var 0) U0 1 := typed_var' ok4' 0 rfl (by show shift 0 4 U0 = U0; rfl) rfl
theorem F4' : Typed Γ4' (var 2) (FunTy 4) 1 :=
  typed_var' ok4' 2 rfl (by show shift 2 2 (FunTy 2) = FunTy 4; calc_simp) rfl
theorem B4' : Typed Γ4' (var 3) (BU 4) 0 :=
  typed_var' ok4' 3 rfl (by show shift 3 1 (BU 3) = BU 4; calc_simp) rfl
theorem ok5 : CtxOk Γ5 := CtxOk.snoc ok4 (typed_BV ok4 P4 F4)
theorem P5 : Typed Γ5 (var 0) U0 1 := typed_var' ok5 0 rfl (by show shift 0 5 U0 = U0; rfl) rfl
theorem NN5 : Typed Γ5 (var 1) (notT (notT (var 0))) 0 :=
  typed_var' ok5 1 rfl (by show shift 1 4 (notT (notT (var 0))) = _; calc_simp) rfl
theorem ok5' : CtxOk Γ5' := CtxOk.snoc ok4 (typed_AV ok4 P4 F4)
theorem P5' : Typed Γ5' (var 0) U0 1 := typed_var' ok5' 0 rfl (by show shift 0 5 U0 = U0; rfl) rfl
theorem F5' : Typed Γ5' (var 2) (FunTy 5) 1 :=
  typed_var' ok5' 2 rfl (by show shift 2 3 (FunTy 2) = FunTy 5; calc_simp) rfl
theorem AV5' : Typed Γ5' (var 4) (AV 5) 0 :=
  typed_var' ok5' 4 rfl (by show shift 4 1 (AV 4) = AV 5; calc_simp) rfl
theorem ok6 : CtxOk Γ6 := CtxOk.snoc ok5 P5
theorem P6 : Typed Γ6 (var 0) U0 1 := typed_var' ok6 0 rfl (by show shift 0 6 U0 = U0; rfl) rfl
theorem F6 : Typed Γ6 (var 2) (FunTy 6) 1 :=
  typed_var' ok6 2 rfl (by show shift 2 4 (FunTy 2) = FunTy 6; calc_simp) rfl
theorem A6 : Typed Γ6 (var 3) (AU 6) 0 :=
  typed_var' ok6 3 rfl (by show shift 3 3 (AU 3) = AU 6; calc_simp) rfl
theorem B6 : Typed Γ6 (var 4) (BV 6) 0 :=
  typed_var' ok6 4 rfl (by show shift 4 2 (BV 4) = BV 6; calc_simp) rfl

end Ctxs

/-! The contradiction, in `Γ6`: from `P`, `pairU = pairV`, so `pU = pV`, so `xU = xV`;
with `True = xU` and `xV = False` this transports `trivial : True` to a proof of `False`. -/

/-- `P = True` by extensionality. -/
def hPT : Term := propextT (var 0) TrueT (lam .prop 0 0 (var 0) (trivT 7)) (lam .prop 0 0 TrueT (var 5))

theorem typed_hPT : Typed Γ6 hPT (eqT U0 (var 0) TrueT) 0 := by
  have ok7a : CtxOk (Γ6.snoc (var 0) 0) := CtxOk.snoc ok6 P6
  have ok7b : CtxOk (Γ6.snoc TrueT 0) := CtxOk.snoc ok6 (typed_TrueT ok6)
  have hf : Typed Γ6 (lam .prop 0 0 (var 0) (trivT 7)) (pi .prop 0 0 (var 0) TrueT) 0 :=
    Typed.lamProp P6 (typed_trivT ok7a)
  have hg : Typed Γ6 (lam .prop 0 0 TrueT (var 5)) (pi .prop 0 0 TrueT (var 0)) 0 :=
    Typed.lamProp (typed_TrueT ok6) (typed_var' ok7b 5 rfl (by show shift 5 2 (var 0) = var 0; calc_simp) rfl)
  exact typed_propextT P6 (typed_TrueT ok6) (hf.cast (by calc_simp)) (hg.cast (by calc_simp))

/-- The motive `y ↦ mkPair y P = mkPair P y`. -/
def CbP : Term := eqT PairP (mkPair (var 6) (var 0)) (mkPair (var 0) (var 6))
/-- `pairU = pairV`, by transport along `P = True`. -/
def hpair : Term :=
  prim (.eqRec 1 0) ![U0, var 0, motiveT 6 U0 (var 0) CbP, reflT PairP (mkPair (var 0) (var 0)), TrueT, hPT]

theorem typed_hpair : Typed Γ6 hpair (eqT PairP pairU pairV) 0 := by
  have ok7 : CtxOk (Γ6.snoc U0 1) := CtxOk.snoc ok6 (typed_U0 ok6)
  have y7 : Typed (Γ6.snoc U0 1) (var 6) U0 1 := typed_var' ok7 6 rfl (by show shift 6 1 U0 = U0; rfl) rfl
  have P7 : Typed (Γ6.snoc U0 1) (var 0) U0 1 := typed_var' ok7 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have ok8 : CtxOk ((Γ6.snoc U0 1).snoc (eqT U0 (var 0) (var 6)) 0) :=
    CtxOk.snoc ok7 (typed_eqT (typed_U0 ok7) P7 y7)
  have y8 : Typed ((Γ6.snoc U0 1).snoc (eqT U0 (var 0) (var 6)) 0) (var 6) U0 1 :=
    typed_var' ok8 6 rfl (by show shift 6 2 U0 = U0; rfl) rfl
  have P8 : Typed ((Γ6.snoc U0 1).snoc (eqT U0 (var 0) (var 6)) 0) (var 0) U0 1 :=
    typed_var' ok8 0 rfl (by show shift 0 8 U0 = U0; rfl) rfl
  have ok7a : CtxOk (Γ6.snoc (eqT U0 (var 0) (var 0)) 0) := CtxOk.snoc ok6 (typed_eqT (typed_U0 ok6) P6 P6)
  have P7a : Typed (Γ6.snoc (eqT U0 (var 0) (var 0)) 0) (var 0) U0 1 :=
    typed_var' ok7a 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have ok7b : CtxOk (Γ6.snoc (eqT U0 (var 0) TrueT) 0) :=
    CtxOk.snoc ok6 (typed_eqT (typed_U0 ok6) P6 (typed_TrueT ok6))
  have P7b : Typed (Γ6.snoc (eqT U0 (var 0) TrueT) 0) (var 0) U0 1 :=
    typed_var' ok7b 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have hC : Typed ((Γ6.snoc U0 1).snoc (eqT U0 (var 0) (var 6)) 0) CbP (univ 0) 1 :=
    typed_eqT (typed_PairP ok8) (typed_mkPair ok8 y8 P8) (typed_mkPair ok8 P8 y8)
  exact typed_eqRec' ok6 (typed_U0 ok6) P6 (E := eqT U0 (var 0) (var 6)) (by calc_simp) hC
    (Ca := eqT PairP (mkPair (var 0) (var 0)) (mkPair (var 0) (var 0))) (by unfold CbP; calc_simp)
    (typed_eqT (typed_PairP ok7a) (typed_mkPair ok7a P7a P7a) (typed_mkPair ok7a P7a P7a))
    (typed_TrueT ok6) typed_hPT
    (Cb' := eqT PairP (mkPair TrueT (var 0)) (mkPair (var 0) TrueT)) (by unfold CbP; calc_simp)
    (typed_eqT (typed_PairP ok7b) (typed_mkPair ok7b (typed_TrueT ok7b) P7b)
      (typed_mkPair ok7b P7b (typed_TrueT ok7b)))
    (Cc := eqT PairP (mkPair (var 0) (var 0)) (mkPair (var 0) (var 0))) (by calc_simp)
    (typed_reflT (typed_PairP ok6) (typed_mkPair ok6 P6 P6))
    (by unfold pairU pairV; calc_simp)

/-- The motive `y ↦ Π (w : Lift (Trunc (Sel y))). pU = ⟨y, w⟩`. -/
def CbI : Term :=
  pi .prop 1 0 (liftT (truncT (Sel 8 (var 6)))) (eqT (IdxT 9) (pU 9) (mkIdx 9 (var 6) (var 8)))
/-- Its instance at `pairU`: `λ w. refl`, using the proof irrelevance of `Lift (Trunc _)`. -/
def cI : Term := lam .prop 1 0 (liftT (truncT (Sel 6 pairU))) (reflT (IdxT 7) (pU 7))
def hidxFun : Term := prim (.eqRec 1 0) ![PairP, pairU, motiveT 6 PairP pairU CbI, cI, pairV, hpair]
/-- `pU = pV`. -/
def hidx : Term := app .prop 0 hidxFun (wV 6)

theorem typed_hidxFun : Typed Γ6 hidxFun
    (pi .prop 1 0 (liftT (truncT (Sel 6 pairV))) (eqT (IdxT 7) (pU 7) (mkIdx 7 pairV (var 6)))) 0 := by
  -- the motive
  have ok7 : CtxOk (Γ6.snoc PairP 1) := CtxOk.snoc ok6 (typed_PairP ok6)
  have P7 : Typed (Γ6.snoc PairP 1) (var 0) U0 1 := typed_var' ok7 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have y7 : Typed (Γ6.snoc PairP 1) (var 6) PairP 1 :=
    typed_var' ok7 6 rfl (by show shift 6 1 PairP = PairP; calc_simp) rfl
  have ok8 : CtxOk ((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0) :=
    CtxOk.snoc ok7 (typed_eqT (typed_PairP ok7) (typed_pairU ok7 P7) y7)
  have P8 : Typed ((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0) (var 0) U0 1 :=
    typed_var' ok8 0 rfl (by show shift 0 8 U0 = U0; rfl) rfl
  have y8 : Typed ((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0) (var 6) PairP 1 :=
    typed_var' ok8 6 rfl (by show shift 6 2 PairP = PairP; calc_simp) rfl
  have hW8 : Typed ((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0) (liftT (truncT (Sel 8 (var 6))))
      (univ 1) 2 := typed_liftT (typed_truncT (typed_Sel ok8 y8))
  have ok9 : CtxOk (((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0).snoc (liftT (truncT (Sel 8 (var 6)))) 1) :=
    CtxOk.snoc ok8 hW8
  have P9 : Typed (((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0).snoc (liftT (truncT (Sel 8 (var 6)))) 1)
      (var 0) U0 1 := typed_var' ok9 0 rfl (by show shift 0 9 U0 = U0; rfl) rfl
  have y9 : Typed (((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0).snoc (liftT (truncT (Sel 8 (var 6)))) 1)
      (var 6) PairP 1 := typed_var' ok9 6 rfl (by show shift 6 3 PairP = PairP; calc_simp) rfl
  have w9 : Typed (((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0).snoc (liftT (truncT (Sel 8 (var 6)))) 1)
      (var 8) (liftT (truncT (Sel 9 (var 6)))) 1 :=
    typed_var' ok9 8 rfl (by show shift 8 1 (liftT (truncT (Sel 8 (var 6)))) = _; calc_simp) rfl
  have hC : Typed ((Γ6.snoc PairP 1).snoc (eqT PairP pairU (var 6)) 0) CbI (univ 0) 1 :=
    Typed.piProp hW8 (typed_eqT (typed_IdxT ok9) (typed_pU ok9 P9) (typed_mkIdx ok9 y9 w9))
  -- the instance at `pairU`
  have ok7a : CtxOk (Γ6.snoc (eqT PairP pairU pairU) 0) :=
    CtxOk.snoc ok6 (typed_eqT (typed_PairP ok6) (typed_pairU ok6 P6) (typed_pairU ok6 P6))
  have P7a : Typed (Γ6.snoc (eqT PairP pairU pairU) 0) (var 0) U0 1 :=
    typed_var' ok7a 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have hW7a : Typed (Γ6.snoc (eqT PairP pairU pairU) 0) (liftT (truncT (Sel 7 pairU))) (univ 1) 2 :=
    typed_liftT (typed_truncT (typed_Sel ok7a (typed_pairU ok7a P7a)))
  have ok8a : CtxOk ((Γ6.snoc (eqT PairP pairU pairU) 0).snoc (liftT (truncT (Sel 7 pairU))) 1) :=
    CtxOk.snoc ok7a hW7a
  have P8a : Typed ((Γ6.snoc (eqT PairP pairU pairU) 0).snoc (liftT (truncT (Sel 7 pairU))) 1) (var 0) U0 1 :=
    typed_var' ok8a 0 rfl (by show shift 0 8 U0 = U0; rfl) rfl
  have w8a : Typed ((Γ6.snoc (eqT PairP pairU pairU) 0).snoc (liftT (truncT (Sel 7 pairU))) 1) (var 7)
      (liftT (truncT (Sel 8 pairU))) 1 :=
    typed_var' ok8a 7 rfl (by show shift 7 1 (liftT (truncT (Sel 7 pairU))) = _; calc_simp) rfl
  have hCa : Typed (Γ6.snoc (eqT PairP pairU pairU) 0)
      (pi .prop 1 0 (liftT (truncT (Sel 7 pairU))) (eqT (IdxT 8) (pU 8) (mkIdx 8 pairU (var 7)))) (univ 0) 1 :=
    Typed.piProp hW7a (typed_eqT (typed_IdxT ok8a) (typed_pU ok8a P8a) (typed_mkIdx ok8a (typed_pairU ok8a P8a) w8a))
  -- the instance at `pairV`
  have ok7b : CtxOk (Γ6.snoc (eqT PairP pairU pairV) 0) :=
    CtxOk.snoc ok6 (typed_eqT (typed_PairP ok6) (typed_pairU ok6 P6) (typed_pairV ok6 P6))
  have P7b : Typed (Γ6.snoc (eqT PairP pairU pairV) 0) (var 0) U0 1 :=
    typed_var' ok7b 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have hW7b : Typed (Γ6.snoc (eqT PairP pairU pairV) 0) (liftT (truncT (Sel 7 pairV))) (univ 1) 2 :=
    typed_liftT (typed_truncT (typed_Sel ok7b (typed_pairV ok7b P7b)))
  have ok8b : CtxOk ((Γ6.snoc (eqT PairP pairU pairV) 0).snoc (liftT (truncT (Sel 7 pairV))) 1) :=
    CtxOk.snoc ok7b hW7b
  have P8b : Typed ((Γ6.snoc (eqT PairP pairU pairV) 0).snoc (liftT (truncT (Sel 7 pairV))) 1) (var 0) U0 1 :=
    typed_var' ok8b 0 rfl (by show shift 0 8 U0 = U0; rfl) rfl
  have w8b : Typed ((Γ6.snoc (eqT PairP pairU pairV) 0).snoc (liftT (truncT (Sel 7 pairV))) 1) (var 7)
      (liftT (truncT (Sel 8 pairV))) 1 :=
    typed_var' ok8b 7 rfl (by show shift 7 1 (liftT (truncT (Sel 7 pairV))) = _; calc_simp) rfl
  have hCb : Typed (Γ6.snoc (eqT PairP pairU pairV) 0)
      (pi .prop 1 0 (liftT (truncT (Sel 7 pairV))) (eqT (IdxT 8) (pU 8) (mkIdx 8 pairV (var 7)))) (univ 0) 1 :=
    Typed.piProp hW7b (typed_eqT (typed_IdxT ok8b) (typed_pU ok8b P8b) (typed_mkIdx ok8b (typed_pairV ok8b P8b) w8b))
  -- the proof at `pairU, refl`: `λ w. refl`, with `wU ≡ w` by proof irrelevance
  have hW6 : Typed Γ6 (liftT (truncT (Sel 6 pairU))) (univ 1) 2 :=
    typed_liftT (typed_truncT (typed_Sel ok6 (typed_pairU ok6 P6)))
  have ok7c : CtxOk (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) := CtxOk.snoc ok6 hW6
  have P7c : Typed (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (var 0) U0 1 :=
    typed_var' ok7c 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have v7c : Typed (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (var 6) (liftT (truncT (Sel 7 pairU))) 1 :=
    typed_var' ok7c 6 rfl (by show shift 6 1 (liftT (truncT (Sel 6 pairU))) = _; calc_simp) rfl
  have hQ : Typed (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (truncT (Sel 7 pairU)) (univ 0) 1 :=
    typed_truncT (typed_Sel ok7c (typed_pairU ok7c P7c))
  have hw : Typed (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (wU 7) (liftT (truncT (Sel 7 pairU))) 1 :=
    typed_wU ok7c P7c
  have dw : DefEq (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (wU 7) (var 6) (liftT (truncT (Sel 7 pairU))) 1 :=
    defEq_lift_irrel hQ hw v7c
  have dw' : DefEq (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (wU 7) (var 6)
      (app .data 2 (lam .data 1 2 PairP (bfam 7)) pairU) 1 :=
    DefEq.conv dw (DefEq.symm ((DefEq.betaData (by decide) (typed_PairP ok7c) (typed_bfam ok7c)
      (typed_pairU ok7c P7c)).castS (subst_bfam 7 pairU)))
  have dpair : DefEq (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (pU 7) (mkIdx 7 pairU (var 6)) (IdxT 7) 1 :=
    defEq_pairT_last (typed_PairP ok7c) (typed_bfam ok7c) (typed_pairU ok7c P7c) dw'
  have dEq : DefEq (Γ6.snoc (liftT (truncT (Sel 6 pairU))) 1) (eqT (IdxT 7) (pU 7) (pU 7))
      (eqT (IdxT 7) (pU 7) (mkIdx 7 pairU (var 6))) (univ 0) 1 :=
    defEq_eqT_right (typed_IdxT ok7c) (typed_pU ok7c P7c) dpair
  have hc : Typed Γ6 cI (pi .prop 1 0 (liftT (truncT (Sel 6 pairU))) (eqT (IdxT 7) (pU 7) (mkIdx 7 pairU (var 6)))) 0 :=
    Typed.lamProp hW6 ((typed_reflT (typed_IdxT ok7c) (typed_pU ok7c P7c)).conv dEq)
  exact typed_eqRec' ok6 (typed_PairP ok6) (typed_pairU ok6 P6) (E := eqT PairP pairU (var 6)) (by calc_simp)
    hC (by unfold CbI; calc_simp) hCa (typed_pairV ok6 P6) typed_hpair (by unfold CbI; calc_simp) hCb
    (by calc_simp) hc (by calc_simp)

theorem typed_hidx : Typed Γ6 hidx (eqT (IdxT 6) (pU 6) (pV 6)) 0 :=
  (Typed.appProp typed_hidxFun (typed_wV ok6 P6)).cast (by unfold pV; calc_simp)

/-- The motive `y ↦ xU = selX (f y)`. -/
def CbX : Term := eqT U0 (xU 8) (selX 8 (ifst 8 (var 6)) (app .data 1 (var 2) (var 6)))
/-- `xU = xV`. -/
def hx : Term := prim (.eqRec 1 0) ![IdxT 6, pU 6, motiveT 6 (IdxT 6) (pU 6) CbX, reflT U0 (xU 6), pV 6, hidx]

theorem typed_hx : Typed Γ6 hx (eqT U0 (xU 6) (xV 6)) 0 := by
  have ok7 : CtxOk (Γ6.snoc (IdxT 6) 1) := CtxOk.snoc ok6 (typed_IdxT ok6)
  have P7 : Typed (Γ6.snoc (IdxT 6) 1) (var 0) U0 1 := typed_var' ok7 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have q7 : Typed (Γ6.snoc (IdxT 6) 1) (var 6) (IdxT 7) 1 :=
    typed_var' ok7 6 rfl (by show shift 6 1 (IdxT 6) = IdxT 7; calc_simp) rfl
  have ok8 : CtxOk ((Γ6.snoc (IdxT 6) 1).snoc (eqT (IdxT 7) (pU 7) (var 6)) 0) :=
    CtxOk.snoc ok7 (typed_eqT (typed_IdxT ok7) (typed_pU ok7 P7) q7)
  have P8 : Typed ((Γ6.snoc (IdxT 6) 1).snoc (eqT (IdxT 7) (pU 7) (var 6)) 0) (var 0) U0 1 :=
    typed_var' ok8 0 rfl (by show shift 0 8 U0 = U0; rfl) rfl
  have F8 : Typed ((Γ6.snoc (IdxT 6) 1).snoc (eqT (IdxT 7) (pU 7) (var 6)) 0) (var 2) (FunTy 8) 1 :=
    typed_var' ok8 2 rfl (by show shift 2 6 (FunTy 2) = FunTy 8; calc_simp) rfl
  have q8 : Typed ((Γ6.snoc (IdxT 6) 1).snoc (eqT (IdxT 7) (pU 7) (var 6)) 0) (var 6) (IdxT 8) 1 :=
    typed_var' ok8 6 rfl (by show shift 6 2 (IdxT 6) = IdxT 8; calc_simp) rfl
  have hC : Typed ((Γ6.snoc (IdxT 6) 1).snoc (eqT (IdxT 7) (pU 7) (var 6)) 0) CbX (univ 0) 1 :=
    typed_eqT (typed_U0 ok8) (typed_xU ok8 P8 F8)
      (typed_selX ok8 (typed_ifst ok8 q8) (typed_appF ok8 F8 q8))
  have ok7a : CtxOk (Γ6.snoc (eqT (IdxT 6) (pU 6) (pU 6)) 0) :=
    CtxOk.snoc ok6 (typed_eqT (typed_IdxT ok6) (typed_pU ok6 P6) (typed_pU ok6 P6))
  have P7a : Typed (Γ6.snoc (eqT (IdxT 6) (pU 6) (pU 6)) 0) (var 0) U0 1 :=
    typed_var' ok7a 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have F7a : Typed (Γ6.snoc (eqT (IdxT 6) (pU 6) (pU 6)) 0) (var 2) (FunTy 7) 1 :=
    typed_var' ok7a 2 rfl (by show shift 2 5 (FunTy 2) = FunTy 7; calc_simp) rfl
  have ok7b : CtxOk (Γ6.snoc (eqT (IdxT 6) (pU 6) (pV 6)) 0) :=
    CtxOk.snoc ok6 (typed_eqT (typed_IdxT ok6) (typed_pU ok6 P6) (typed_pV ok6 P6))
  have P7b : Typed (Γ6.snoc (eqT (IdxT 6) (pU 6) (pV 6)) 0) (var 0) U0 1 :=
    typed_var' ok7b 0 rfl (by show shift 0 7 U0 = U0; rfl) rfl
  have F7b : Typed (Γ6.snoc (eqT (IdxT 6) (pU 6) (pV 6)) 0) (var 2) (FunTy 7) 1 :=
    typed_var' ok7b 2 rfl (by show shift 2 5 (FunTy 2) = FunTy 7; calc_simp) rfl
  exact typed_eqRec' ok6 (typed_IdxT ok6) (typed_pU ok6 P6) (E := eqT (IdxT 7) (pU 7) (var 6)) (by calc_simp)
    hC (Ca := eqT U0 (xU 7) (xU 7)) (by unfold CbX xU fU; calc_simp)
    (typed_eqT (typed_U0 ok7a) (typed_xU ok7a P7a F7a) (typed_xU ok7a P7a F7a))
    (typed_pV ok6 P6) typed_hidx (Cb' := eqT U0 (xU 7) (xV 7)) (by unfold CbX xV fV; calc_simp)
    (typed_eqT (typed_U0 ok7b) (typed_xU ok7b P7b F7b) (typed_xV ok7b P7b F7b))
    (Cc := eqT U0 (xU 6) (xU 6)) (by calc_simp) (typed_reflT (typed_U0 ok6) (typed_xU ok6 P6 F6))
    (by calc_simp)

/-- `True = xU` (from `a : AU`) and `xV = False` (from `b : BV`). -/
def h0 : Term := andE1 6 (var 3) (eqT U0 TrueT (xU 6)) (pfst (ifst 6 (pU 6)))
def h1 : Term := andE1 6 (var 4) (eqT U0 (xV 6) FalseT) (psnd (ifst 6 (pV 6)))
/-- `trivial : True`, transported to `xU`, then to `xV`, then to `False`. -/
def contra : Term :=
  transportT 6 (xV 6) (transportT 6 (xU 6) (transportT 6 TrueT (trivT 6) (xU 6) h0) (xV 6) hx) FalseT h1

theorem typed_contra : Typed Γ6 contra FalseT 0 :=
  typed_transport ok6 (typed_xV ok6 P6 F6) (typed_false ok6) (typed_eq_of_BV ok6 P6 F6 B6)
    (typed_transport ok6 (typed_xU ok6 P6 F6) (typed_xV ok6 P6 F6) typed_hx
      (typed_transport ok6 (typed_TrueT ok6) (typed_xU ok6 P6 F6) (typed_eq_of_AU ok6 P6 F6 A6)
        (typed_trivT ok6)))

/-! The case analysis. -/

/-- In `Γ5` (`a : AU`, `b : BV`): `False.elim (nn (λ p. contra))`. -/
def branchB : Term := falseElimT (var 0) (app .prop 0 (var 1) (lam .prop 0 0 (var 0) contra))

theorem typed_branchB : Typed Γ5 branchB (var 0) 0 :=
  typed_falseElimT P5 ((Typed.appProp NN5 (Typed.lamProp P5 typed_contra)).cast (by calc_simp))

/-- In `Γ4` (`a : AU`): cases on `hV`. -/
def branchA : Term :=
  orElim (hV 4) (var 0)
    (lam .prop 0 0 (AV 4) (andE2 5 (var 4) (eqT U0 TrueT (xV 5)) (pfst (ifst 5 (pV 5)))))
    (lam .prop 0 0 (BV 4) branchB)

theorem typed_branchA : Typed Γ4 branchA (var 0) 0 :=
  typed_orElim (AV 4) (BV 4) (typed_hV ok4 P4 F4) P4
    ((Typed.lamProp (typed_AV ok4 P4 F4) (typed_PfromAV ok5' P5' F5' AV5')).cast (by calc_simp))
    ((Typed.lamProp (typed_BV ok4 P4 F4) typed_branchB).cast (by calc_simp))

/-- In `Γ3` (`f : FunTy`): cases on `hU`. -/
def body2 : Term :=
  orElim (hU 3) (var 0) (lam .prop 0 0 (AU 3) branchA)
    (lam .prop 0 0 (BU 3) (andE2 4 (var 3) (eqT U0 (xU 4) FalseT) (psnd (ifst 4 (pU 4)))))

theorem typed_body2 : Typed Γ3 body2 (var 0) 0 :=
  typed_orElim (AU 3) (BU 3) (typed_hU ok3 P3 F3) P3
    ((Typed.lamProp (typed_AU ok3 P3 F3) typed_branchA).cast (by calc_simp))
    ((Typed.lamProp (typed_BU ok3 P3 F3) (typed_PfromBU ok4' P4' F4' B4')).cast (by calc_simp))

/-- In `Γ2` (`nn : ¬¬P`): eliminate the truncation of the choice function. -/
def body : Term := truncRecT (FunTy 2) (var 0) (lam .prop 1 0 (FunTy 2) body2) (choiceTm 2)

theorem typed_body : Typed Γ2 body (var 0) 0 :=
  typed_truncRecT (typed_FunTy ok2) P2 ((Typed.lamProp (typed_FunTy ok2) typed_body2).cast (by calc_simp))
    (typed_choiceTm ok2)

/-- The closed term `λ (P : U_0). λ (nn : ¬¬P). body`. -/
def dneTerm : Term := lam .prop 1 0 U0 (lam .prop 0 0 (notT (notT (var 0))) body)

/-- **Double negation elimination is derivable** without the primitive `dne`. -/
theorem dne_derivable : Typed Γ0 dneTerm (pi .prop 1 0 U0 (pi .prop 0 0 (notT (notT (var 0))) (var 0))) 0 :=
  Typed.lamProp (typed_U0 (CtxOk.nil _)) (Typed.lamProp (typed_notT ok1 (typed_notT ok1 P1)) typed_body)


/-! ### The derived `dne` in any context, and the absence of the primitive -/

/-- Weakening of a closed typing into any well-formed context. -/
theorem typed_weak_closed {t A : Term} {r : ℕ} (h : Typed Γ0 t A r) :
    ∀ {m : ℕ} {Γ : Ctx m}, CtxOk Γ → Typed Γ (shift 0 m t) (shift 0 m A) r
  | 0, Γ, _ => by
    have e : Γ = Γ0 := funext fun i => i.elim0
    subst e
    simpa only [shift_zero] using h
  | m + 1, Γ, hΓ => by
    cases hΓ with
    | snoc hΓ' hB =>
      have := Typed.weak (typed_weak_closed h hΓ') hB
      rwa [shift_shift'' 0 m m 1 (by omega) (by omega), shift_shift'' 0 m m 1 (by omega) (by omega)] at this

/-- **The primitive `dne` is derivable**: in any well-formed context, from `P : U_0` and
`h : (P → False) → False` (the declared argument types of `dne`), the application of the
closed term `dneTerm` has type `P` (the declared result type of `dne`). -/
theorem dne_derived {m : ℕ} {Γ : Ctx m} (hΓ : CtxOk Γ) {P h : Term} (hP : Typed Γ P (univ 0) 1)
    (hh : Typed Γ h (pi .prop 0 0 (pi .prop 0 0 P (prim .false_ ![])) (prim .false_ ![])) 0) :
    Typed Γ (app .prop 0 (app .prop 0 (shift 0 m dneTerm) P) h) P 0 := by
  have h1 : Typed Γ (shift 0 m dneTerm) (pi .prop 1 0 U0 (pi .prop 0 0 (notT (notT (var m))) (var m))) 0 :=
    (typed_weak_closed dne_derivable hΓ).cast (by calc_simp)
  have h2 : Typed Γ (app .prop 0 (shift 0 m dneTerm) P) (pi .prop 0 0 (notT (notT P)) (shift m 1 P)) 0 :=
    (Typed.appProp h1 hP).cast (by calc_simp)
  exact (Typed.appProp h2 hh).cast (by calc_simp)

/-- Whether a term mentions the primitive `dne`. -/
def Term.usesDne : Term → Bool
  | var _ => false
  | univ _ => false
  | pi _ _ _ A B => A.usesDne || B.usesDne
  | lam _ _ _ A b => A.usesDne || b.usesDne
  | app _ _ f a => f.usesDne || a.usesDne
  | letE _ A v b => A.usesDne || v.usesDne || b.usesDne
  | prim .dne _ => true
  | @prim n _ args => (List.finRange n).any fun k => (args k).usesDne

example : (prim .dne ![U0, var 0]).usesDne = true := by decide

/-- The certificate does not use the primitive `dne`. -/
theorem dneTerm_usesDne : dneTerm.usesDne = false := by decide

end SolidLean.Calc
