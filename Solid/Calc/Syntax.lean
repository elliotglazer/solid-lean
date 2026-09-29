module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.Tuple.Basic

/-!
# The core of the annotated calculus `L_ann`: syntax and classifier

Draft 2, §3.1, restricted to the core: universes, dependent products,
abstractions, applications and `let`, with the kind (`prop`/`data`) and the
universe levels recorded at binders and applications.  Variables are de Bruijn
*levels* (the `x`-th variable of the context, oldest first), so that a context
of length `m` is a tuple indexed by `Fin m` and is extended under a binder
exactly as `Fin.snoc` extends a tuple.

The classifier `c(Γ, e)` (the universe level of the type of `e`, read off
the annotations) determines the sort of the value of `e`: the value of a term
with classifier `c` lives in tower sort `c`.
-/

@[expose] public section

namespace SolidLean.Calc

/-- Kinds of products and abstractions. -/
inductive Kind
  | prop
  | data
  deriving DecidableEq, Repr

/-- The primitive constants of §3.4, with their level annotations; `Prim n`
is the primitives of arity `n`.  A primitive is used saturated: `prim c args`
is the constant `c` applied to its `n` arguments (its declared ground type is
a product, and unsaturated uses are its η-expansions). -/
inductive Prim : ℕ → Type
  /-- `False : U_0`. -/
  | false_ : Prim 0
  /-- `False.elim[j] (C : U_j) (h : False) : C`. -/
  | falseElim (j : ℕ) : Prim 2
  /-- `Eq[i] (A : U_i) (a b : A) : U_0`. -/
  | eq (i : ℕ) : Prim 3
  /-- `refl[i] (A : U_i) (a : A) : Eq A a a`. -/
  | refl (i : ℕ) : Prim 2
  /-- `Eq.rec[i, j] (A : U_i) (a : A) (C : Π(y : A). Π(p : Eq A a y). U_j) (c : C a refl)
  (b : A) (p : Eq A a b) : C b p`. -/
  | eqRec (i j : ℕ) : Prim 6
  /-- `Σ[i, j] (A : U_i) (B : Π(x : A). U_j) : U_{max i j}`, with `1 ≤ j`. -/
  | sigma (i j : ℕ) : Prim 2
  /-- `pair[i, j] A B (a : A) (b : B a) : Σ A B`. -/
  | pair (i j : ℕ) : Prim 4
  /-- `fst[i, j] A B (s : Σ A B) : A`. -/
  | fst (i j : ℕ) : Prim 3
  /-- `snd[i, j] A B (s : Σ A B) : B (fst s)`. -/
  | snd (i j : ℕ) : Prim 3
  /-- `Lift[i, d] (A : U_i) : U_{i+d}`. -/
  | lift (i d : ℕ) : Prim 1
  /-- `up[i, d] A (a : A) : Lift A`. -/
  | up (i d : ℕ) : Prim 2
  /-- `down[i, d] A (a : Lift A) : A`. -/
  | down (i d : ℕ) : Prim 2
  /-- `Trunc[i] (A : U_i) : U_0`. -/
  | trunc (i : ℕ) : Prim 1
  /-- `Trunc.mk[i] A (a : A) : Trunc A`. -/
  | truncMk (i : ℕ) : Prim 2
  /-- `Trunc.rec[i] A (P : U_0) (f : Π(x : A). P) (h : Trunc A) : P`. -/
  | truncRec (i : ℕ) : Prim 4
  /-- `propext (P Q : U_0) (f : P → Q) (g : Q → P) : Eq U_0 P Q`. -/
  | propext : Prim 4
  /-- `dne (P : U_0) (h : (P → False) → False) : P` (excluded middle). -/
  | dne : Prim 2
  /-- `uchoice[i] (A : U_i) (h : Trunc A) (u : Π(a b : A). Eq A a b) : A` (unique choice). -/
  | uchoice (i : ℕ) : Prim 3
  /-- `choice[i, j] (A : U_i) (B : Π(x : A). U_j) (h : Π(x : A). Trunc (B x)) :
  Trunc (Π(x : A). B x)` (propositional choice). -/
  | choice (i j : ℕ) : Prim 3
  /-- `Sum[i, j] (A : U_i) (B : U_j) : U_{max i j}`, with `1 ≤ max i j`. -/
  | sum (i j : ℕ) : Prim 2
  /-- `inl[i, j] A B (a : A) : Sum A B`. -/
  | inl (i j : ℕ) : Prim 3
  /-- `inr[i, j] A B (b : B) : Sum A B`. -/
  | inr (i j : ℕ) : Prim 3
  /-- `Sum.rec[i, j, k] A B (C : Π(s : Sum A B). U_k) (f : Π(a : A). C (inl a))
  (g : Π(b : B). C (inr b)) (s : Sum A B) : C s`. -/
  | sumRec (i j k : ℕ) : Prim 6
  /-- `Nat : U_1`. -/
  | nat : Prim 0
  /-- `zero : Nat`. -/
  | zero : Prim 0
  /-- `succ (n : Nat) : Nat`. -/
  | succ : Prim 1
  /-- `Nat.rec[j] (C : Π(n : Nat). U_j) (z : C zero) (s : Π(n : Nat). Π(h : C n). C (succ n))
  (n : Nat) : C n`. -/
  | natRec (j : ℕ) : Prim 4
  /-- `Quot[i] (A : U_i) (R : Π(a b : A). U_0) : U_i`, with `1 ≤ i`. -/
  | quot (i : ℕ) : Prim 2
  /-- `Quot.mk[i] A R (a : A) : Quot A R`. -/
  | quotMk (i : ℕ) : Prim 3
  /-- `Quot.lift[i, j] A R (C : U_j) (f : Π(a : A). C)
  (h : Π(a b : A). Π(r : R a b). Eq C (f a) (f b)) (q : Quot A R) : C`. -/
  | quotLift (i j : ℕ) : Prim 6
  /-- `Quot.sound[i] A R (a b : A) (r : R a b) : Eq (Quot A R) (mk a) (mk b)`. -/
  | quotSound (i : ℕ) : Prim 5
  /-- `Quot.ind[i] A R (P : Π(q : Quot A R). U_0) (h : Π(a : A). P (mk a)) (q : Quot A R) : P q`. -/
  | quotInd (i : ℕ) : Prim 5

/-- Raw annotated terms. -/
inductive Term
  /-- A variable, as a de Bruijn level. -/
  | var (x : ℕ)
  /-- The universe `U_n`. -/
  | univ (n : ℕ)
  /-- `Π[k; i, j](x : A). B`. -/
  | pi (k : Kind) (i j : ℕ) (A B : Term)
  /-- `λ[k; i, j](x : A). b`. -/
  | lam (k : Kind) (i j : ℕ) (A b : Term)
  /-- `app[k; j](f, a)`. -/
  | app (k : Kind) (j : ℕ) (f a : Term)
  /-- `let[j](x : A := v). b`. -/
  | letE (j : ℕ) (A v b : Term)
  /-- A primitive constant applied to its arguments. -/
  | prim {n : ℕ} (c : Prim n) (args : Fin n → Term)

namespace Prim

/-- The classifiers of the arguments of a primitive (the sorts of their values). -/
def argSort : {n : ℕ} → Prim n → Fin n → ℕ
  | _, .false_ => ![]
  | _, .falseElim j => ![j + 1, 0]
  | _, .eq i => ![i + 1, i, i]
  | _, .refl i => ![i + 1, i]
  | _, .eqRec i j => ![i + 1, i, max i (j + 1), j, i, 0]
  | _, .sigma i j => ![i + 1, max i (j + 1)]
  | _, .pair i j => ![i + 1, max i (j + 1), i, j]
  | _, .fst i j => ![i + 1, max i (j + 1), max i j]
  | _, .snd i j => ![i + 1, max i (j + 1), max i j]
  | _, .lift i _ => ![i + 1]
  | _, .up i _ => ![i + 1, i]
  | _, .down i d => ![i + 1, i + d]
  | _, .trunc i => ![i + 1]
  | _, .truncMk i => ![i + 1, i]
  | _, .truncRec i => ![i + 1, 1, 0, 0]
  | _, .propext => ![1, 1, 0, 0]
  | _, .dne => ![1, 0]
  | _, .uchoice i => ![i + 1, 0, 0]
  | _, .choice i j => ![i + 1, max i (j + 1), 0]
  | _, .sum i j => ![i + 1, j + 1]
  | _, .inl i j => ![i + 1, j + 1, i]
  | _, .inr i j => ![i + 1, j + 1, j]
  | _, .sumRec i j k => ![i + 1, j + 1, max (max i j) (k + 1), max i k, max j k, max i j]
  | _, .nat => ![]
  | _, .zero => ![]
  | _, .succ => ![1]
  | _, .natRec j => ![j + 1, j, max 1 (max j j), 1]
  | _, .quot i => ![i + 1, max i (max i 1)]
  | _, .quotMk i => ![i + 1, max i (max i 1), i]
  | _, .quotLift i j => ![i + 1, max i (max i 1), j + 1, max i j, 0, i]
  | _, .quotSound i => ![i + 1, max i (max i 1), i, i, 0]
  | _, .quotInd i => ![i + 1, max i (max i 1), max i 1, 0, i]

/-- The classifier of a saturated application of the primitive. -/
def level : {n : ℕ} → Prim n → ℕ
  | _, .false_ => 1
  | _, .falseElim j => j
  | _, .eq _ => 1
  | _, .refl _ => 0
  | _, .eqRec _ j => j
  | _, .sigma i j => max i j + 1
  | _, .pair i j => max i j
  | _, .fst i _ => i
  | _, .snd _ j => j
  | _, .lift i d => i + d + 1
  | _, .up i d => i + d
  | _, .down i _ => i
  | _, .trunc _ => 1
  | _, .truncMk _ => 0
  | _, .truncRec _ => 0
  | _, .propext => 0
  | _, .dne => 0
  | _, .uchoice i => i
  | _, .choice _ _ => 0
  | _, .sum i j => max i j + 1
  | _, .inl i j => max i j
  | _, .inr i j => max i j
  | _, .sumRec _ _ k => k
  | _, .nat => 2
  | _, .zero => 1
  | _, .succ => 1
  | _, .natRec j => j
  | _, .quot i => i + 1
  | _, .quotMk i => i
  | _, .quotLift _ j => j
  | _, .quotSound _ => 0
  | _, .quotInd _ => 0

/-- Side conditions on the level annotations of a primitive: data-valued
sums, products and eliminations need a positive level. -/
def Ok : {n : ℕ} → Prim n → Prop
  | _, .sigma _ j => 1 ≤ j
  | _, .pair _ j => 1 ≤ j
  | _, .sum i j => 1 ≤ max i j
  | _, .inl i j => 1 ≤ max i j
  | _, .inr i j => 1 ≤ max i j
  | _, .sumRec _ _ k => 1 ≤ k
  | _, .choice _ j => 1 ≤ j
  | _, .natRec j => 1 ≤ j
  | _, .quot i => 1 ≤ i
  | _, .quotMk i => 1 ≤ i
  | _, .quotLift i j => 1 ≤ i ∧ 1 ≤ j
  | _, .quotSound i => 1 ≤ i
  | _, .quotInd i => 1 ≤ i
  | _, _ => True

end Prim

/-- A context of length `m`: types with their levels, oldest first. -/
abbrev Ctx (m : ℕ) := Fin m → Term × ℕ

namespace Ctx

variable {m : ℕ}

/-- The level recorded for variable `x` (`0` if out of range). -/
def lev (Γ : Ctx m) (x : ℕ) : ℕ := if h : x < m then (Γ ⟨x, h⟩).2 else 0

/-- The levels of the variables, as a tuple. -/
def levels (Γ : Ctx m) : Fin m → ℕ := fun i => (Γ i).2

theorem lev_of_lt (Γ : Ctx m) (i : Fin m) : Γ.lev i = Γ.levels i := by
  simp [lev, levels, i.2]

/-- Extension by a binder. -/
def snoc (Γ : Ctx m) (A : Term) (i : ℕ) : Ctx (m + 1) := Fin.snoc Γ (A, i)

theorem lev_of_ge (Γ : Ctx m) {x : ℕ} (h : m ≤ x) : Γ.lev x = 0 := by
  simp [lev, Nat.not_lt.2 h]

theorem lev_snoc_lt (Γ : Ctx m) (A : Term) (i : ℕ) {x : ℕ} (h : x < m) :
    (Γ.snoc A i).lev x = Γ.lev x := by
  simp only [lev, snoc]
  rw [dif_pos (Nat.lt_succ_of_lt h), dif_pos h]
  have : (⟨x, Nat.lt_succ_of_lt h⟩ : Fin (m + 1)) = Fin.castSucc ⟨x, h⟩ := rfl
  rw [this, Fin.snoc_castSucc]

theorem lev_snoc_self (Γ : Ctx m) (A : Term) (i : ℕ) : (Γ.snoc A i).lev m = i := by
  simp only [lev, snoc]
  rw [dif_pos (Nat.lt_succ_self m)]
  have : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := rfl
  rw [this, Fin.snoc_last]

theorem levels_snoc (Γ : Ctx m) (A : Term) (i : ℕ) :
    (Γ.snoc A i).levels = Fin.snoc (α := fun _ => ℕ) Γ.levels i := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp [levels, snoc]
  · simp [levels, snoc]

end Ctx

namespace Term

/-- The classifier: the level of the type of `e` in `Γ`.  An `abbrev` (it is
not recursive), so that it unfolds on constructors during unification. -/
abbrev cls {m : ℕ} (Γ : Ctx m) : Term → ℕ
  | var x => Γ.lev x
  | univ n => n + 2
  | pi k i j _ _ => match k with
    | .prop => 1
    | .data => max i j + 1
  | lam k i j _ _ => match k with
    | .prop => 0
    | .data => max i j
  | app k j _ _ => match k with
    | .prop => 0
    | .data => j
  | letE j _ _ _ => j
  | prim c _ => c.level

variable {m : ℕ} (Γ : Ctx m)

@[simp] theorem cls_var (x : ℕ) : (var x).cls Γ = Γ.lev x := rfl
@[simp] theorem cls_univ (n : ℕ) : (univ n).cls Γ = n + 2 := rfl
@[simp] theorem cls_pi_prop (i j : ℕ) (A B : Term) : (pi .prop i j A B).cls Γ = 1 := rfl
@[simp] theorem cls_pi_data (i j : ℕ) (A B : Term) : (pi .data i j A B).cls Γ = max i j + 1 := rfl
@[simp] theorem cls_lam_prop (i j : ℕ) (A b : Term) : (lam .prop i j A b).cls Γ = 0 := rfl
@[simp] theorem cls_lam_data (i j : ℕ) (A b : Term) : (lam .data i j A b).cls Γ = max i j := rfl
@[simp] theorem cls_app_prop (j : ℕ) (f a : Term) : (app .prop j f a).cls Γ = 0 := rfl
@[simp] theorem cls_app_data (j : ℕ) (f a : Term) : (app .data j f a).cls Γ = j := rfl
@[simp] theorem cls_letE (j : ℕ) (A v b : Term) : (letE j A v b).cls Γ = j := rfl
@[simp] theorem cls_prim {n : ℕ} (c : Prim n) (args : Fin n → Term) : (prim c args).cls Γ = c.level := rfl

end Term

end SolidLean.Calc

namespace SolidLean.Calc

/-! ### Bounded terms and substitution -/

namespace Term

/-- All free variables are below `m` (under a binder the bound grows by one). -/
def Bounded : ℕ → Term → Prop
  | m, var x => x < m
  | _, univ _ => True
  | m, pi _ _ _ A B => Bounded m A ∧ Bounded (m + 1) B
  | m, lam _ _ _ A b => Bounded m A ∧ Bounded (m + 1) b
  | m, app _ _ f a => Bounded m f ∧ Bounded m a
  | m, letE _ A v b => Bounded m A ∧ Bounded m v ∧ Bounded (m + 1) b
  | m, prim _ args => ∀ k, Bounded m (args k)

theorem Bounded.mono {m m' : ℕ} (h : m ≤ m') : ∀ {t : Term}, Bounded m t → Bounded m' t
  | var _, hx => lt_of_lt_of_le hx h
  | univ _, _ => trivial
  | pi _ _ _ _ _, ⟨hA, hB⟩ => ⟨hA.mono h, hB.mono (Nat.succ_le_succ h)⟩
  | lam _ _ _ _ _, ⟨hA, hb⟩ => ⟨hA.mono h, hb.mono (Nat.succ_le_succ h)⟩
  | app _ _ _ _, ⟨hf, ha⟩ => ⟨hf.mono h, ha.mono h⟩
  | letE _ _ _ _, ⟨hA, hv, hb⟩ => ⟨hA.mono h, hv.mono h, hb.mono (Nat.succ_le_succ h)⟩
  | prim _ _, hargs => fun k => (hargs k).mono h

/-- Shift the variables of level at least `m` up by `e`: the term written for
a context of length at least `m` read in the context with `e` binders
inserted at position `m`. -/
def shift (m e : ℕ) : Term → Term
  | var x => if x < m then var x else var (x + e)
  | univ n => univ n
  | pi k i j A B => pi k i j (shift m e A) (shift m e B)
  | lam k i j A b => lam k i j (shift m e A) (shift m e b)
  | app k j f a => app k j (shift m e f) (shift m e a)
  | letE j A v b => letE j (shift m e A) (shift m e v) (shift m e b)
  | prim c args => prim c (fun k => shift m e (args k))

/-- Substitution of the variable of level `m` by `a` (which lives in the
context of length `m`) at binder depth `d`: variables above `m` are shifted
down, and `a` is shifted past the `d` binders crossed. -/
def subst (m : ℕ) (a : Term) : ℕ → Term → Term
  | d, var x => if x < m then var x else if x = m then shift m d a else var (x - 1)
  | _, univ n => univ n
  | d, pi k i j A B => pi k i j (subst m a d A) (subst m a (d + 1) B)
  | d, lam k i j A b => lam k i j (subst m a d A) (subst m a (d + 1) b)
  | d, app k j f e => app k j (subst m a d f) (subst m a d e)
  | d, letE j A v b => letE j (subst m a d A) (subst m a d v) (subst m a (d + 1) b)
  | d, prim c args => prim c (fun k => subst m a d (args k))

theorem shift_zero (m : ℕ) : ∀ t : Term, shift m 0 t = t
  | var x => by
    show (if x < m then var x else var (x + 0)) = var x
    split_ifs <;> rfl
  | univ _ => rfl
  | pi k i j A B => by simp only [shift, shift_zero m A, shift_zero m B]
  | lam k i j A b => by simp only [shift, shift_zero m A, shift_zero m b]
  | app k j f a => by simp only [shift, shift_zero m f, shift_zero m a]
  | letE j A v b => by simp only [shift, shift_zero m A, shift_zero m v, shift_zero m b]
  | prim c args => by
    show prim c (fun k => shift m 0 (args k)) = prim c args
    congr 1
    funext k
    exact shift_zero m (args k)

theorem Bounded.cast {n n' : ℕ} (h : n = n') {t : Term} (ht : Bounded n t) : Bounded n' t := h ▸ ht

theorem Bounded.shift {m e : ℕ} : ∀ {n : ℕ} {t : Term}, m ≤ n → Bounded n t → Bounded (n + e) (Term.shift m e t)
  | n, var x, _, hx => by
    show Bounded (n + e) (if x < m then var x else var (x + e))
    by_cases h : x < m
    · rw [if_pos h]; show x < n + e; have : x < n := hx; omega
    · rw [if_neg h]; show x + e < n + e; have : x < n := hx; omega
  | _, univ _, _, _ => trivial
  | n, pi _ _ _ A B, hn, ⟨hA, hB⟩ =>
    show Bounded (n + e) (Term.shift m e A) ∧ Bounded (n + e + 1) (Term.shift m e B) from
      ⟨hA.shift hn, (hB.shift (Nat.le_succ_of_le hn)).cast (by omega)⟩
  | n, lam _ _ _ A b, hn, ⟨hA, hb⟩ =>
    show Bounded (n + e) (Term.shift m e A) ∧ Bounded (n + e + 1) (Term.shift m e b) from
      ⟨hA.shift hn, (hb.shift (Nat.le_succ_of_le hn)).cast (by omega)⟩
  | n, app _ _ f a, hn, ⟨hf, ha⟩ =>
    show Bounded (n + e) (Term.shift m e f) ∧ Bounded (n + e) (Term.shift m e a) from ⟨hf.shift hn, ha.shift hn⟩
  | n, letE _ A v b, hn, ⟨hA, hv, hb⟩ =>
    show Bounded (n + e) (Term.shift m e A) ∧ Bounded (n + e) (Term.shift m e v) ∧
        Bounded (n + e + 1) (Term.shift m e b) from
      ⟨hA.shift hn, hv.shift hn, (hb.shift (Nat.le_succ_of_le hn)).cast (by omega)⟩
  | n, prim _ args, hn, hargs =>
    show ∀ k, Bounded (n + e) (Term.shift m e (args k)) from fun k => (hargs k).shift hn

/-- The classifier of a bounded term does not depend on the context beyond
the bound. -/
theorem cls_snoc {m : ℕ} (Γ : Ctx m) (B : Term) (l : ℕ) :
    ∀ {t : Term}, Bounded m t → t.cls (Γ.snoc B l) = t.cls Γ
  | var x, hx => by
    have hx' : x < m := hx
    simp only [cls_var, Ctx.lev, Ctx.snoc]
    rw [dif_pos (Nat.lt_succ_of_lt hx'), dif_pos hx']
    have : (⟨x, Nat.lt_succ_of_lt hx'⟩ : Fin (m + 1)) = Fin.castSucc ⟨x, hx'⟩ := rfl
    rw [this, Fin.snoc_castSucc]
  | univ _, _ => rfl
  | pi k _ _ _ _, _ => by cases k <;> rfl
  | lam k _ _ _ _, _ => by cases k <;> rfl
  | app k _ _ _, _ => by cases k <;> rfl
  | letE _ _ _ _, _ => rfl
  | prim _ _, _ => rfl

end Term

end SolidLean.Calc
