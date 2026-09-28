import Solid.Calc.Syntax

/-!
# Typing rules of the core calculus

Draft 2, §3.2, for the core: context formation, the typing judgment
`Γ ⊢ t : A @ r` (`r` the universe level of `A`), and typed definitional
equality `Γ ⊢ t ≡ s : A @ r` with `β`, `η`, `ζ`, proof irrelevance and
congruence.  Data products require the codomain level to be at least `1`
(a product into propositions is of kind `prop`), matching Lean's
impredicative `Prop`.

The classifier reads the level off the annotations (Lemma 3.2 of draft 2:
`cls_of_typed`), which is what makes the evaluator well defined on raw terms.
-/

namespace SolidLean.Calc

open Term

namespace Prim

/-- The declared types of the arguments of a primitive, in a context of length
`m` (the earlier arguments may occur; terms under a binder are shifted). -/
def argType (m : ℕ) : {n : ℕ} → (c : Prim n) → (Fin n → Term) → Fin n → Term
  | _, .false_, _ => ![]
  | _, .falseElim j, a => ![univ j, prim .false_ ![]]
  | _, .eq i, a => ![univ i, a 0, a 0]
  | _, .refl i, a => ![univ i, a 0]
  | _, .eqRec i j, a =>
    ![univ i, a 0,
      pi .data i (j + 1) (a 0) (pi .data 0 (j + 1)
        (prim (.eq i) ![shift m 1 (a 0), shift m 1 (a 1), var m]) (univ j)),
      app .data (j + 1) (app .data (j + 1) (a 2) (a 1)) (prim (.refl i) ![a 0, a 1]),
      a 0, prim (.eq i) ![a 0, a 1, a 4]]
  | _, .sigma i j, a => ![univ i, pi .data i (j + 1) (a 0) (univ j)]
  | _, .pair i j, a => ![univ i, pi .data i (j + 1) (a 0) (univ j), a 0, app .data (j + 1) (a 1) (a 2)]
  | _, .fst i j, a => ![univ i, pi .data i (j + 1) (a 0) (univ j), prim (.sigma i j) ![a 0, a 1]]
  | _, .snd i j, a => ![univ i, pi .data i (j + 1) (a 0) (univ j), prim (.sigma i j) ![a 0, a 1]]
  | _, .lift i _, _ => ![univ i]
  | _, .up i _, a => ![univ i, a 0]
  | _, .down i d, a => ![univ i, prim (.lift i d) ![a 0]]
  | _, .trunc i, _ => ![univ i]
  | _, .truncMk i, a => ![univ i, a 0]
  | _, .truncRec i, a => ![univ i, univ 0, pi .prop i 0 (a 0) (shift m 1 (a 1)), prim (.trunc i) ![a 0]]
  | _, .propext, a => ![univ 0, univ 0, pi .prop 0 0 (a 0) (shift m 1 (a 1)), pi .prop 0 0 (a 1) (shift m 1 (a 0))]
  | _, .dne, a => ![univ 0, pi .prop 0 0 (pi .prop 0 0 (a 0) (prim .false_ ![])) (prim .false_ ![])]
  | _, .uchoice i, a =>
    ![univ i, prim (.trunc i) ![a 0],
      pi .prop i 0 (a 0) (pi .prop i 0 (shift m 1 (a 0))
        (prim (.eq i) ![shift m 2 (a 0), var m, var (m + 1)]))]
  | _, .choice i j, a =>
    ![univ i, pi .data i (j + 1) (a 0) (univ j),
      pi .prop i 0 (a 0) (prim (.trunc j) ![app .data (j + 1) (shift m 1 (a 1)) (var m)])]
  | _, .sum i j, _ => ![univ i, univ j]
  | _, .inl i j, a => ![univ i, univ j, a 0]
  | _, .inr i j, a => ![univ i, univ j, a 1]
  | _, .sumRec i j k, a =>
    ![univ i, univ j,
      pi .data (max i j) (k + 1) (prim (.sum i j) ![a 0, a 1]) (univ k),
      pi .data i k (a 0) (app .data (k + 1) (shift m 1 (a 2)) (prim (.inl i j) ![shift m 1 (a 0), shift m 1 (a 1), var m])),
      pi .data j k (a 1) (app .data (k + 1) (shift m 1 (a 2)) (prim (.inr i j) ![shift m 1 (a 0), shift m 1 (a 1), var m])),
      prim (.sum i j) ![a 0, a 1]]
  | _, .nat, _ => ![]
  | _, .zero, _ => ![]
  | _, .succ, _ => ![prim .nat ![]]
  | _, .natRec j, a =>
    ![pi .data 1 (j + 1) (prim .nat ![]) (univ j),
      app .data (j + 1) (a 0) (prim .zero ![]),
      pi .data 1 (max j j) (prim .nat ![]) (pi .data j j (app .data (j + 1) (shift m 1 (a 0)) (var m))
        (app .data (j + 1) (shift m 2 (a 0)) (prim .succ ![var m]))),
      prim .nat ![]]
  | _, .quot i, a => ![univ i, pi .data i (max i 1) (a 0) (pi .data i 1 (shift m 1 (a 0)) (univ 0))]
  | _, .quotMk i, a => ![univ i, pi .data i (max i 1) (a 0) (pi .data i 1 (shift m 1 (a 0)) (univ 0)), a 0]
  | _, .quotLift i j, a =>
    ![univ i, pi .data i (max i 1) (a 0) (pi .data i 1 (shift m 1 (a 0)) (univ 0)), univ j,
      pi .data i j (a 0) (shift m 1 (a 2)),
      pi .prop i 0 (a 0) (pi .prop i 0 (shift m 1 (a 0)) (pi .prop 0 0
        (app .data 1 (app .data (max i 1) (shift m 2 (a 1)) (var m)) (var (m + 1)))
        (prim (.eq j) ![shift m 3 (a 2), app .data j (shift m 3 (a 3)) (var m),
          app .data j (shift m 3 (a 3)) (var (m + 1))]))),
      prim (.quot i) ![a 0, a 1]]
  | _, .quotSound i, a =>
    ![univ i, pi .data i (max i 1) (a 0) (pi .data i 1 (shift m 1 (a 0)) (univ 0)), a 0, a 0,
      app .data 1 (app .data (max i 1) (a 1) (a 2)) (a 3)]
  | _, .quotInd i, a =>
    ![univ i, pi .data i (max i 1) (a 0) (pi .data i 1 (shift m 1 (a 0)) (univ 0)),
      pi .data i 1 (prim (.quot i) ![a 0, a 1]) (univ 0),
      pi .prop i 0 (a 0) (app .data 1 (shift m 1 (a 2)) (prim (.quotMk i) ![shift m 1 (a 0), shift m 1 (a 1), var m])),
      prim (.quot i) ![a 0, a 1]]

/-- The declared result type of a primitive application. -/
def resultType (m : ℕ) : {n : ℕ} → (c : Prim n) → (Fin n → Term) → Term
  | _, .false_, _ => univ 0
  | _, .falseElim _, a => a 0
  | _, .eq _, _ => univ 0
  | _, .refl i, a => prim (.eq i) ![a 0, a 1, a 1]
  | _, .eqRec _ j, a => app .data (j + 1) (app .data (j + 1) (a 2) (a 4)) (a 5)
  | _, .sigma i j, _ => univ (max i j)
  | _, .pair i j, a => prim (.sigma i j) ![a 0, a 1]
  | _, .fst _ _, a => a 0
  | _, .snd i j, a => app .data (j + 1) (a 1) (prim (.fst i j) ![a 0, a 1, a 2])
  | _, .lift i d, _ => univ (i + d)
  | _, .up i d, a => prim (.lift i d) ![a 0]
  | _, .down _ _, a => a 0
  | _, .trunc _, _ => univ 0
  | _, .truncMk i, a => prim (.trunc i) ![a 0]
  | _, .truncRec _, a => a 1
  | _, .propext, a => prim (.eq 1) ![univ 0, a 0, a 1]
  | _, .dne, a => a 0
  | _, .uchoice _, a => a 0
  | _, .choice i j, a =>
    prim (.trunc (max i j)) ![pi .data i j (a 0) (app .data (j + 1) (shift m 1 (a 1)) (var m))]
  | _, .sum i j, _ => univ (max i j)
  | _, .inl i j, a => prim (.sum i j) ![a 0, a 1]
  | _, .inr i j, a => prim (.sum i j) ![a 0, a 1]
  | _, .sumRec _ _ k, a => app .data (k + 1) (a 2) (a 5)
  | _, .nat, _ => univ 1
  | _, .zero, _ => prim .nat ![]
  | _, .succ, _ => prim .nat ![]
  | _, .natRec j, a => app .data (j + 1) (a 0) (a 3)
  | _, .quot i, _ => univ i
  | _, .quotMk i, a => prim (.quot i) ![a 0, a 1]
  | _, .quotLift _ _, a => a 2
  | _, .quotSound i, a =>
    prim (.eq i) ![prim (.quot i) ![a 0, a 1], prim (.quotMk i) ![a 0, a 1, a 2],
      prim (.quotMk i) ![a 0, a 1, a 3]]
  | _, .quotInd _, a => app .data 1 (a 2) (a 4)

end Prim

mutual

/-- Well-formed contexts. -/
inductive CtxOk : {m : ℕ} → Ctx m → Prop
  | nil (Γ : Ctx 0) : CtxOk Γ
  | snoc {m : ℕ} {Γ : Ctx m} {A : Term} {i : ℕ} :
      CtxOk Γ → Typed Γ A (univ i) (i + 1) → CtxOk (Γ.snoc A i)

/-- `Γ ⊢ t : A @ r`. -/
inductive Typed : {m : ℕ} → Ctx m → Term → Term → ℕ → Prop
  | var {m : ℕ} {Γ : Ctx m} (x : Fin m) : CtxOk Γ →
      Typed Γ (var x) (Term.shift x (m - x) (Γ x).1) (Γ x).2
  | univ {m : ℕ} {Γ : Ctx m} (n : ℕ) : CtxOk Γ → Typed Γ (univ n) (univ (n + 1)) (n + 2)
  | piData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} : 1 ≤ j →
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) B (univ j) (j + 1) →
      Typed Γ (pi .data i j A B) (univ (max i j)) (max i j + 1)
  | piProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A B : Term} :
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) B (univ 0) 1 →
      Typed Γ (pi .prop i 0 A B) (univ 0) 1
  | lamData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b B : Term} : 1 ≤ j →
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) b B j →
      Typed Γ (lam .data i j A b) (pi .data i j A B) (max i j)
  | lamProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A b B : Term} :
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) b B 0 →
      Typed Γ (lam .prop i 0 A b) (pi .prop i 0 A B) 0
  | appData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f a A B : Term} : 1 ≤ j →
      Typed Γ f (pi .data i j A B) (max i j) → Typed Γ a A i →
      Typed Γ (app .data j f a) (Term.subst m a 0 B) j
  | appProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {f a A B : Term} :
      Typed Γ f (pi .prop i 0 A B) 0 → Typed Γ a A i →
      Typed Γ (app .prop 0 f a) (Term.subst m a 0 B) 0
  | letE {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v A b B : Term} :
      Typed Γ v A i → Typed (Γ.snoc A i) b B j →
      Typed Γ (letE j A v b) (Term.subst m v 0 B) j
  | weak {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} {B : Term} {l : ℕ} :
      Typed Γ t A r → Typed Γ B (univ l) (l + 1) →
      Typed (Γ.snoc B l) (Term.shift m 1 t) (Term.shift m 1 A) r
  | conv {m : ℕ} {Γ : Ctx m} {t A B : Term} {r : ℕ} :
      Typed Γ t A r → DefEq Γ A B (univ r) (r + 1) → Typed Γ t B r
  /-- A primitive constant applied to arguments of its declared types. -/
  | prim {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args : Fin n → Term) : c.Ok →
      (∀ k, Typed Γ (args k) (c.argType m args k) (c.argSort k)) →
      Typed Γ (prim c args) (c.resultType m args) c.level

/-- `Γ ⊢ t ≡ s : A @ r`. -/
inductive DefEq : {m : ℕ} → Ctx m → Term → Term → Term → ℕ → Prop
  | refl {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} : Typed Γ t A r → DefEq Γ t t A r
  | symm {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} : DefEq Γ t s A r → DefEq Γ s t A r
  | trans {m : ℕ} {Γ : Ctx m} {t s u A : Term} {r : ℕ} :
      DefEq Γ t s A r → DefEq Γ s u A r → DefEq Γ t u A r
  | conv {m : ℕ} {Γ : Ctx m} {t s A B : Term} {r : ℕ} :
      DefEq Γ t s A r → DefEq Γ A B (univ r) (r + 1) → DefEq Γ t s B r
  | betaData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b B a : Term} : 1 ≤ j →
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) b B j → Typed Γ a A i →
      DefEq Γ (app .data j (lam .data i j A b) a) (Term.subst m a 0 b) (Term.subst m a 0 B) j
  | betaProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A b B a : Term} :
      Typed Γ A (univ i) (i + 1) → Typed (Γ.snoc A i) b B 0 → Typed Γ a A i →
      DefEq Γ (app .prop 0 (lam .prop i 0 A b) a) (Term.subst m a 0 b) (Term.subst m a 0 B) 0
  | zeta {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v A b B : Term} :
      Typed Γ v A i → Typed (Γ.snoc A i) b B j →
      DefEq Γ (letE j A v b) (Term.subst m v 0 b) (Term.subst m v 0 B) j
  | eta {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f A B : Term} : 1 ≤ j →
      Typed Γ f (pi .data i j A B) (max i j) →
      DefEq Γ (lam .data i j A (app .data j (Term.shift m 1 f) (var m))) f (pi .data i j A B) (max i j)
  | proofIrrel {m : ℕ} {Γ : Ctx m} {h h' P : Term} :
      Typed Γ h P 0 → Typed Γ h' P 0 → DefEq Γ h h' P 0
  | congrPiData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A A' B B' : Term} : 1 ≤ j →
      DefEq Γ A A' (univ i) (i + 1) → DefEq (Γ.snoc A i) B B' (univ j) (j + 1) →
      DefEq Γ (pi .data i j A B) (pi .data i j A' B') (univ (max i j)) (max i j + 1)
  | congrPiProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A A' B B' : Term} :
      DefEq Γ A A' (univ i) (i + 1) → DefEq (Γ.snoc A i) B B' (univ 0) 1 →
      DefEq Γ (pi .prop i 0 A B) (pi .prop i 0 A' B') (univ 0) 1
  | congrLamData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A A' b b' B : Term} : 1 ≤ j →
      DefEq Γ A A' (univ i) (i + 1) → DefEq (Γ.snoc A i) b b' B j →
      DefEq Γ (lam .data i j A b) (lam .data i j A' b') (pi .data i j A B) (max i j)
  | congrLamProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A A' b b' B : Term} :
      DefEq Γ A A' (univ i) (i + 1) → DefEq (Γ.snoc A i) b b' B 0 →
      DefEq Γ (lam .prop i 0 A b) (lam .prop i 0 A' b') (pi .prop i 0 A B) 0
  | congrAppData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f f' a a' A B : Term} : 1 ≤ j →
      DefEq Γ f f' (pi .data i j A B) (max i j) → DefEq Γ a a' A i →
      DefEq Γ (app .data j f a) (app .data j f' a') (Term.subst m a 0 B) j
  | congrAppProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {f f' a a' A B : Term} :
      DefEq Γ f f' (pi .prop i 0 A B) 0 → DefEq Γ a a' A i →
      DefEq Γ (app .prop 0 f a) (app .prop 0 f' a') (Term.subst m a 0 B) 0
  | congrLet {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v v' A b b' B : Term} :
      DefEq Γ v v' A i → DefEq (Γ.snoc A i) b b' B j →
      DefEq Γ (letE j A v b) (letE j A v' b') (Term.subst m v 0 B) j
  | weak {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} {B : Term} {l : ℕ} :
      DefEq Γ t s A r → Typed Γ B (univ l) (l + 1) →
      DefEq (Γ.snoc B l) (Term.shift m 1 t) (Term.shift m 1 s) (Term.shift m 1 A) r
  /-- Congruence for primitive applications. -/
  | congrPrim {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args args' : Fin n → Term) : c.Ok →
      (∀ k, DefEq Γ (args k) (args' k) (c.argType m args k) (c.argSort k)) →
      DefEq Γ (prim c args) (prim c args') (c.resultType m args) c.level
  /-- `Eq.rec C c a refl ≡ c`. -/
  | eqRecRefl {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A a C c : Term} :
      (∀ k, Typed Γ (![A, a, C, c, a, prim (.refl i) ![A, a]] k)
        ((Prim.eqRec i j).argType m ![A, a, C, c, a, prim (.refl i) ![A, a]] k) ((Prim.eqRec i j).argSort k)) →
      DefEq Γ (prim (.eqRec i j) ![A, a, C, c, a, prim (.refl i) ![A, a]]) c
        ((Prim.eqRec i j).resultType m ![A, a, C, c, a, prim (.refl i) ![A, a]]) j
  /-- `fst (pair a b) ≡ a`. -/
  | sigmaFst {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B a b : Term} : 1 ≤ j →
      (∀ k, Typed Γ (![A, B, a, b] k) ((Prim.pair i j).argType m ![A, B, a, b] k) ((Prim.pair i j).argSort k)) →
      DefEq Γ (prim (.fst i j) ![A, B, prim (.pair i j) ![A, B, a, b]]) a A i
  /-- `snd (pair a b) ≡ b`. -/
  | sigmaSnd {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B a b : Term} : 1 ≤ j →
      (∀ k, Typed Γ (![A, B, a, b] k) ((Prim.pair i j).argType m ![A, B, a, b] k) ((Prim.pair i j).argSort k)) →
      DefEq Γ (prim (.snd i j) ![A, B, prim (.pair i j) ![A, B, a, b]]) b
        ((Prim.snd i j).resultType m ![A, B, prim (.pair i j) ![A, B, a, b]]) j
  /-- `pair (fst s) (snd s) ≡ s`. -/
  | sigmaEta {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B s : Term} : 1 ≤ j →
      (∀ k, Typed Γ (![A, B, s] k) ((Prim.fst i j).argType m ![A, B, s] k) ((Prim.fst i j).argSort k)) →
      DefEq Γ (prim (.pair i j) ![A, B, prim (.fst i j) ![A, B, s], prim (.snd i j) ![A, B, s]]) s
        (prim (.sigma i j) ![A, B]) (max i j)
  /-- `down (up a) ≡ a`. -/
  | downUp {m : ℕ} {Γ : Ctx m} {i d : ℕ} {A a : Term} :
      (∀ k, Typed Γ (![A, a] k) ((Prim.up i d).argType m ![A, a] k) ((Prim.up i d).argSort k)) →
      DefEq Γ (prim (.down i d) ![A, prim (.up i d) ![A, a]]) a A i
  /-- `up (down a) ≡ a`. -/
  | upDown {m : ℕ} {Γ : Ctx m} {i d : ℕ} {A a : Term} :
      (∀ k, Typed Γ (![A, a] k) ((Prim.down i d).argType m ![A, a] k) ((Prim.down i d).argSort k)) →
      DefEq Γ (prim (.up i d) ![A, prim (.down i d) ![A, a]]) a (prim (.lift i d) ![A]) (i + d)
  /-- `Sum.rec C f g (inl a) ≡ f a`. -/
  | sumRecInl {m : ℕ} {Γ : Ctx m} {i j k : ℕ} {A B C f g a : Term} : 1 ≤ k →
      (∀ l, Typed Γ (![A, B, C, f, g, prim (.inl i j) ![A, B, a]] l)
        ((Prim.sumRec i j k).argType m ![A, B, C, f, g, prim (.inl i j) ![A, B, a]] l)
        ((Prim.sumRec i j k).argSort l)) →
      Typed Γ a A i →
      DefEq Γ (prim (.sumRec i j k) ![A, B, C, f, g, prim (.inl i j) ![A, B, a]]) (app .data k f a)
        (app .data (k + 1) C (prim (.inl i j) ![A, B, a])) k
  /-- `Sum.rec C f g (inr b) ≡ g b`. -/
  | sumRecInr {m : ℕ} {Γ : Ctx m} {i j k : ℕ} {A B C f g b : Term} : 1 ≤ k →
      (∀ l, Typed Γ (![A, B, C, f, g, prim (.inr i j) ![A, B, b]] l)
        ((Prim.sumRec i j k).argType m ![A, B, C, f, g, prim (.inr i j) ![A, B, b]] l)
        ((Prim.sumRec i j k).argSort l)) →
      Typed Γ b B j →
      DefEq Γ (prim (.sumRec i j k) ![A, B, C, f, g, prim (.inr i j) ![A, B, b]]) (app .data k g b)
        (app .data (k + 1) C (prim (.inr i j) ![A, B, b])) k
  /-- `Nat.rec C z s zero ≡ z`. -/
  | natRecZero {m : ℕ} {Γ : Ctx m} {j : ℕ} {C z s : Term} : 1 ≤ j →
      (∀ k, Typed Γ (![C, z, s, prim .zero ![]] k) ((Prim.natRec j).argType m ![C, z, s, prim .zero ![]] k)
        ((Prim.natRec j).argSort k)) →
      DefEq Γ (prim (.natRec j) ![C, z, s, prim .zero ![]]) z (app .data (j + 1) C (prim .zero ![])) j
  /-- `Nat.rec C z s (succ n) ≡ s n (Nat.rec C z s n)`. -/
  | natRecSucc {m : ℕ} {Γ : Ctx m} {j : ℕ} {C z s n : Term} : 1 ≤ j →
      (∀ k, Typed Γ (![C, z, s, prim .succ ![n]] k) ((Prim.natRec j).argType m ![C, z, s, prim .succ ![n]] k)
        ((Prim.natRec j).argSort k)) →
      Typed Γ n (prim .nat ![]) 1 →
      DefEq Γ (prim (.natRec j) ![C, z, s, prim .succ ![n]])
        (app .data j (app .data (max j j) s n) (prim (.natRec j) ![C, z, s, n]))
        (app .data (j + 1) C (prim .succ ![n])) j
  /-- `Quot.lift C f h (mk a) ≡ f a`. -/
  | quotLiftMk {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A R C f h a : Term} : 1 ≤ i → 1 ≤ j →
      (∀ k, Typed Γ (![A, R, C, f, h, prim (.quotMk i) ![A, R, a]] k)
        ((Prim.quotLift i j).argType m ![A, R, C, f, h, prim (.quotMk i) ![A, R, a]] k)
        ((Prim.quotLift i j).argSort k)) →
      Typed Γ a A i →
      DefEq Γ (prim (.quotLift i j) ![A, R, C, f, h, prim (.quotMk i) ![A, R, a]]) (app .data j f a) C j

end

/-! ### Boundedness and classifier coherence (Lemma 3.2) -/

theorem Term.Bounded.subst {m : ℕ} {a : Term} (ha : Bounded m a) :
    ∀ (d : ℕ) {t : Term}, Bounded (m + 1 + d) t → Bounded (m + d) (Term.subst m a d t)
  | d, var x, hx => by
    show Bounded (m + d) (if x < m then var x else if x = m then Term.shift m d a else var (x - 1))
    by_cases h1 : x < m
    · rw [if_pos h1]; show x < m + d; omega
    · rw [if_neg h1]
      by_cases h2 : x = m
      · rw [if_pos h2]; exact ha.shift (le_refl m)
      · rw [if_neg h2]
        have : x < m + 1 + d := hx
        show x - 1 < m + d
        omega
  | _, univ _, _ => trivial
  | d, pi _ _ _ A B, ⟨hA, hB⟩ =>
    show Bounded (m + d) (Term.subst m a d A) ∧ Bounded (m + d + 1) (Term.subst m a (d + 1) B) from
      ⟨ha.subst d hA, (ha.subst (d + 1) (hB.cast (by omega))).cast (by omega)⟩
  | d, lam _ _ _ A b, ⟨hA, hb⟩ =>
    show Bounded (m + d) (Term.subst m a d A) ∧ Bounded (m + d + 1) (Term.subst m a (d + 1) b) from
      ⟨ha.subst d hA, (ha.subst (d + 1) (hb.cast (by omega))).cast (by omega)⟩
  | d, app _ _ f e, ⟨hf, he⟩ =>
    show Bounded (m + d) (Term.subst m a d f) ∧ Bounded (m + d) (Term.subst m a d e) from
      ⟨ha.subst d hf, ha.subst d he⟩
  | d, letE _ A v b, ⟨hA, hv, hb⟩ =>
    show Bounded (m + d) (Term.subst m a d A) ∧ Bounded (m + d) (Term.subst m a d v) ∧
        Bounded (m + d + 1) (Term.subst m a (d + 1) b) from
      ⟨ha.subst d hA, ha.subst d hv, (ha.subst (d + 1) (hb.cast (by omega))).cast (by omega)⟩
  | d, prim _ args, hargs =>
    show ∀ k, Bounded (m + d) (Term.subst m a d (args k)) from fun k => ha.subst d (hargs k)

/-- Substitution at depth `0` on a term bounded by `m + 1`. -/
theorem Term.Bounded.subst0 {m : ℕ} {a : Term} (ha : Bounded m a) {t : Term}
    (ht : Bounded (m + 1) t) : Bounded m (Term.subst m a 0 t) :=
  ha.subst 0 ht

namespace Term

@[simp] theorem Bounded_var {m x : ℕ} : Bounded m (var x) ↔ x < m := Iff.rfl
@[simp] theorem Bounded_univ {m n : ℕ} : Bounded m (univ n) ↔ True := Iff.rfl
@[simp] theorem Bounded_pi {m i j : ℕ} {k : Kind} {A B : Term} :
    Bounded m (pi k i j A B) ↔ Bounded m A ∧ Bounded (m + 1) B := Iff.rfl
@[simp] theorem Bounded_lam {m i j : ℕ} {k : Kind} {A b : Term} :
    Bounded m (lam k i j A b) ↔ Bounded m A ∧ Bounded (m + 1) b := Iff.rfl
@[simp] theorem Bounded_app {m j : ℕ} {k : Kind} {f a : Term} :
    Bounded m (app k j f a) ↔ Bounded m f ∧ Bounded m a := Iff.rfl
@[simp] theorem Bounded_letE {m j : ℕ} {A v b : Term} :
    Bounded m (letE j A v b) ↔ Bounded m A ∧ Bounded m v ∧ Bounded (m + 1) b := Iff.rfl
@[simp] theorem Bounded_prim {m n : ℕ} {c : Prim n} {args : Fin n → Term} :
    Bounded m (prim c args) ↔ ∀ k, Bounded m (args k) := Iff.rfl

/-- Shifting a term bounded by the shift position. -/
theorem Bounded.shift_le {m e n' : ℕ} {t : Term} (h : Bounded m t) (hle : m + e ≤ n') :
    Bounded n' (Term.shift m e t) := (h.shift (le_refl m)).mono hle

theorem Bounded.cons {m n : ℕ} {a : Term} {v : Fin n → Term} (ha : Bounded m a)
    (hv : ∀ k, Bounded m (v k)) : ∀ k, Bounded m (Matrix.vecCons a v k) :=
  fun k => Fin.cases (motive := fun k => Bounded m (Matrix.vecCons a v k)) ha hv k

theorem Bounded.nil {m : ℕ} : ∀ k : Fin 0, Bounded m (Matrix.vecEmpty k) := fun k => k.elim0

end Term

/-- The result type of a primitive application is bounded when its arguments are. -/
theorem Prim.resultType_bounded {m n : ℕ} (c : Prim n) {args : Fin n → Term}
    (hb : ∀ k, Bounded m (args k)) : Bounded m (c.resultType m args) := by
  cases c <;> simp (disch := first | exact hb _ | omega) [Prim.resultType, hb, Term.Bounded.shift_le,
    Fin.forall_fin_succ]

mutual

theorem bounded_of_ctxOk {m : ℕ} {Γ : Ctx m} : CtxOk Γ → ∀ x : Fin m, Bounded x (Γ x).1
  | .nil _ => fun x => x.elim0
  | @CtxOk.snoc m Γ A i hΓ hA => fun x => by
    refine Fin.lastCases ?_ (fun x => ?_) x
    · rw [show (Γ.snoc A i) (Fin.last m) = (A, i) from by simp [Ctx.snoc]]
      exact (bounded_of_typed hA).1
    · rw [show (Γ.snoc A i) (Fin.castSucc x) = Γ x from by simp [Ctx.snoc]]
      exact bounded_of_ctxOk hΓ x

theorem bounded_of_typed {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} :
    Typed Γ t A r → Bounded m t ∧ Bounded m A
  | @Typed.var m Γ x hΓ =>
    ⟨x.2, ((bounded_of_ctxOk hΓ x).shift (e := m - x) (le_refl _)).cast (by have := x.2; omega)⟩
  | .univ _ _ => ⟨trivial, trivial⟩
  | .piData _ hA hB => ⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hB).1⟩, trivial⟩
  | .piProp hA hB => ⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hB).1⟩, trivial⟩
  | .lamData _ hA hb =>
    ⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hb).1⟩,
     ⟨(bounded_of_typed hA).1, (bounded_of_typed hb).2⟩⟩
  | .lamProp hA hb =>
    ⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hb).1⟩,
     ⟨(bounded_of_typed hA).1, (bounded_of_typed hb).2⟩⟩
  | .appData _ hf ha =>
    ⟨⟨(bounded_of_typed hf).1, (bounded_of_typed ha).1⟩,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hf).2.2⟩
  | .appProp hf ha =>
    ⟨⟨(bounded_of_typed hf).1, (bounded_of_typed ha).1⟩,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hf).2.2⟩
  | .letE hv hb =>
    ⟨⟨(bounded_of_typed hv).2, (bounded_of_typed hv).1, (bounded_of_typed hb).1⟩,
     (bounded_of_typed hv).1.subst0 (bounded_of_typed hb).2⟩
  | @Typed.weak m _ _ _ _ _ _ ht _ => ⟨(bounded_of_typed ht).1.shift (le_refl m),
      (bounded_of_typed ht).2.shift (le_refl m)⟩
  | .conv ht hAB => ⟨(bounded_of_typed ht).1, (bounded_of_defEq hAB).2.1⟩
  | .prim c _ _ h =>
    ⟨fun k => (bounded_of_typed (h k)).1, Prim.resultType_bounded c fun k => (bounded_of_typed (h k)).1⟩

theorem bounded_of_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} :
    DefEq Γ t s A r → Bounded m t ∧ Bounded m s ∧ Bounded m A
  | .refl ht => ⟨(bounded_of_typed ht).1, (bounded_of_typed ht).1, (bounded_of_typed ht).2⟩
  | .symm h => ⟨(bounded_of_defEq h).2.1, (bounded_of_defEq h).1, (bounded_of_defEq h).2.2⟩
  | .trans h h' => ⟨(bounded_of_defEq h).1, (bounded_of_defEq h').2.1, (bounded_of_defEq h).2.2⟩
  | .conv h hAB => ⟨(bounded_of_defEq h).1, (bounded_of_defEq h).2.1, (bounded_of_defEq hAB).2.1⟩
  | .betaData _ hA hb ha =>
    ⟨⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hb).1⟩, (bounded_of_typed ha).1⟩,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hb).1,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hb).2⟩
  | .betaProp hA hb ha =>
    ⟨⟨⟨(bounded_of_typed hA).1, (bounded_of_typed hb).1⟩, (bounded_of_typed ha).1⟩,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hb).1,
     (bounded_of_typed ha).1.subst0 (bounded_of_typed hb).2⟩
  | .zeta hv hb =>
    ⟨⟨(bounded_of_typed hv).2, (bounded_of_typed hv).1, (bounded_of_typed hb).1⟩,
     (bounded_of_typed hv).1.subst0 (bounded_of_typed hb).1,
     (bounded_of_typed hv).1.subst0 (bounded_of_typed hb).2⟩
  | .eta _ hf =>
    ⟨⟨(bounded_of_typed hf).2.1, (bounded_of_typed hf).1.shift (le_refl m), Nat.lt_succ_self m⟩,
     (bounded_of_typed hf).1, (bounded_of_typed hf).2⟩
  | .proofIrrel hh hh' => ⟨(bounded_of_typed hh).1, (bounded_of_typed hh').1, (bounded_of_typed hh).2⟩
  | .congrPiData _ hA hB =>
    ⟨⟨(bounded_of_defEq hA).1, (bounded_of_defEq hB).1⟩,
     ⟨(bounded_of_defEq hA).2.1, (bounded_of_defEq hB).2.1⟩, trivial⟩
  | .congrPiProp hA hB =>
    ⟨⟨(bounded_of_defEq hA).1, (bounded_of_defEq hB).1⟩,
     ⟨(bounded_of_defEq hA).2.1, (bounded_of_defEq hB).2.1⟩, trivial⟩
  | .congrLamData _ hA hb =>
    ⟨⟨(bounded_of_defEq hA).1, (bounded_of_defEq hb).1⟩,
     ⟨(bounded_of_defEq hA).2.1, (bounded_of_defEq hb).2.1⟩,
     ⟨(bounded_of_defEq hA).1, (bounded_of_defEq hb).2.2⟩⟩
  | .congrLamProp hA hb =>
    ⟨⟨(bounded_of_defEq hA).1, (bounded_of_defEq hb).1⟩,
     ⟨(bounded_of_defEq hA).2.1, (bounded_of_defEq hb).2.1⟩,
     ⟨(bounded_of_defEq hA).1, (bounded_of_defEq hb).2.2⟩⟩
  | .congrAppData _ hf ha =>
    ⟨⟨(bounded_of_defEq hf).1, (bounded_of_defEq ha).1⟩,
     ⟨(bounded_of_defEq hf).2.1, (bounded_of_defEq ha).2.1⟩,
     (bounded_of_defEq ha).1.subst0 (bounded_of_defEq hf).2.2.2⟩
  | .congrAppProp hf ha =>
    ⟨⟨(bounded_of_defEq hf).1, (bounded_of_defEq ha).1⟩,
     ⟨(bounded_of_defEq hf).2.1, (bounded_of_defEq ha).2.1⟩,
     (bounded_of_defEq ha).1.subst0 (bounded_of_defEq hf).2.2.2⟩
  | .congrLet hv hb =>
    ⟨⟨(bounded_of_defEq hv).2.2, (bounded_of_defEq hv).1, (bounded_of_defEq hb).1⟩,
     ⟨(bounded_of_defEq hv).2.2, (bounded_of_defEq hv).2.1, (bounded_of_defEq hb).2.1⟩,
     (bounded_of_defEq hv).1.subst0 (bounded_of_defEq hb).2.2⟩
  | @DefEq.weak m _ _ _ _ _ _ _ h _ => ⟨(bounded_of_defEq h).1.shift (le_refl m),
      (bounded_of_defEq h).2.1.shift (le_refl m), (bounded_of_defEq h).2.2.shift (le_refl m)⟩
  | .congrPrim c _ _ _ h =>
    ⟨fun k => (bounded_of_defEq (h k)).1, fun k => (bounded_of_defEq (h k)).2.1,
     Prim.resultType_bounded c fun k => (bounded_of_defEq (h k)).1⟩
  | .eqRecRefl h =>
    ⟨fun k => (bounded_of_typed (h k)).1, (bounded_of_typed (h 3)).1,
     Prim.resultType_bounded _ fun k => (bounded_of_typed (h k)).1⟩
  | .sigmaFst _ h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨Bounded.cons (hb 0) (Bounded.cons (hb 1) (Bounded.cons hb Bounded.nil)), hb 2, hb 0⟩
  | .sigmaSnd _ h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨Bounded.cons (hb 0) (Bounded.cons (hb 1) (Bounded.cons hb Bounded.nil)), hb 3,
     ⟨hb 1, Bounded.cons (hb 0) (Bounded.cons (hb 1) (Bounded.cons hb Bounded.nil))⟩⟩
  | .sigmaEta _ h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨Bounded.cons (hb 0) (Bounded.cons (hb 1) (Bounded.cons hb (Bounded.cons hb Bounded.nil))), hb 2,
     Bounded.cons (hb 0) (Bounded.cons (hb 1) Bounded.nil)⟩
  | .downUp h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨Bounded.cons (hb 0) (Bounded.cons hb Bounded.nil), hb 1, hb 0⟩
  | .upDown h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨Bounded.cons (hb 0) (Bounded.cons hb Bounded.nil), hb 1, Bounded.cons (hb 0) Bounded.nil⟩
  | .sumRecInl _ h ha =>
    have hb := fun l => (bounded_of_typed (h l)).1
    ⟨hb, ⟨hb 3, (bounded_of_typed ha).1⟩, ⟨hb 2, hb 5⟩⟩
  | .sumRecInr _ h hb' =>
    have hb := fun l => (bounded_of_typed (h l)).1
    ⟨hb, ⟨hb 4, (bounded_of_typed hb').1⟩, ⟨hb 2, hb 5⟩⟩
  | .natRecZero _ h =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨hb, hb 1, ⟨hb 0, hb 3⟩⟩
  | .natRecSucc _ h hn =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨hb, ⟨⟨hb 2, (bounded_of_typed hn).1⟩,
      Bounded.cons (hb 0) (Bounded.cons (hb 1) (Bounded.cons (hb 2)
        (Bounded.cons (bounded_of_typed hn).1 Bounded.nil)))⟩, ⟨hb 0, hb 3⟩⟩
  | .quotLiftMk _ _ h ha =>
    have hb := fun k => (bounded_of_typed (h k)).1
    ⟨hb, ⟨hb 3, (bounded_of_typed ha).1⟩, hb 2⟩

end

end SolidLean.Calc

namespace SolidLean.Calc

open Term

/-- The classifier is preserved by shifting, for contexts agreeing on the
levels of the variables in the corresponding positions. -/
theorem Term.cls_shift {m' m'' : ℕ} (Γ : Ctx m') (Γ' : Ctx m'') (m e : ℕ)
    (h1 : ∀ x, x < m → Γ'.lev x = Γ.lev x) (h2 : ∀ x, m ≤ x → Γ'.lev (x + e) = Γ.lev x) :
    ∀ t : Term, (shift m e t).cls Γ' = t.cls Γ
  | var x => by
    show (if x < m then var x else var (x + e)).cls Γ' = Γ.lev x
    by_cases h : x < m
    · rw [if_pos h]; exact h1 x h
    · rw [if_neg h]; exact h2 x (Nat.le_of_not_lt h)
  | univ _ => rfl
  | pi k _ _ _ _ => by cases k <;> rfl
  | lam k _ _ _ _ => by cases k <;> rfl
  | app k _ _ _ => by cases k <;> rfl
  | letE _ _ _ _ => rfl
  | prim _ _ => rfl

/-- The classifier is preserved by substitution of a term of the right level
(draft 2, proof of Lemma 3.2). -/
theorem Term.cls_subst {m' m'' : ℕ} (Γ : Ctx m') (Γ' : Ctx m'') (m d : ℕ) (a : Term)
    (h1 : ∀ x, x < m → Γ'.lev x = Γ.lev x) (hm : (shift m d a).cls Γ' = Γ.lev m)
    (h3 : ∀ x, m < x → Γ'.lev (x - 1) = Γ.lev x) :
    ∀ t : Term, (Term.subst m a d t).cls Γ' = t.cls Γ
  | var x => by
    show (if x < m then var x else if x = m then shift m d a else var (x - 1)).cls Γ' = Γ.lev x
    by_cases h : x < m
    · rw [if_pos h]; exact h1 x h
    · rw [if_neg h]
      by_cases h' : x = m
      · rw [if_pos h', h']; exact hm
      · rw [if_neg h']; exact h3 x (by omega)
  | univ _ => rfl
  | pi k _ _ _ _ => by cases k <;> rfl
  | lam k _ _ _ _ => by cases k <;> rfl
  | app k _ _ _ => by cases k <;> rfl
  | letE _ _ _ _ => rfl
  | prim _ _ => rfl

/-- Substitution at depth `0` for the last variable of the context. -/
theorem Term.cls_subst0 {m : ℕ} (Γ : Ctx m) (A : Term) (i : ℕ) {a : Term} (ha : a.cls Γ = i)
    (t : Term) : (Term.subst m a 0 t).cls Γ = t.cls (Γ.snoc A i) := by
  refine Term.cls_subst (Γ.snoc A i) Γ m 0 a (fun x hx => (Γ.lev_snoc_lt A i hx).symm) ?_
    (fun x hx => ?_) t
  · rw [shift_zero, ha, Γ.lev_snoc_self]
  · rw [Γ.lev_of_ge (by omega), (Γ.snoc A i).lev_of_ge (by omega)]

/-- Shifting past the last variable of the context. -/
theorem Term.cls_shift1 {m : ℕ} (Γ : Ctx m) (B : Term) (l : ℕ) (t : Term) :
    (shift m 1 t).cls (Γ.snoc B l) = t.cls Γ :=
  Term.cls_shift Γ (Γ.snoc B l) m 1 (fun x hx => Γ.lev_snoc_lt B l hx)
    (fun x hx => by rw [Γ.lev_of_ge hx, (Γ.snoc B l).lev_of_ge (by omega)]) t

mutual

/-- **Lemma 3.2** (classifier coherence): the classifier of a typed term is
its level. -/
theorem cls_of_typed {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} : Typed Γ t A r → t.cls Γ = r
  | .var x _ => by simp [Ctx.lev_of_lt, Ctx.levels]
  | .univ _ _ => rfl
  | .piData _ _ _ => rfl
  | .piProp _ _ => rfl
  | .lamData _ _ _ => rfl
  | .lamProp _ _ => rfl
  | .appData _ _ _ => rfl
  | .appProp _ _ => rfl
  | .letE _ _ => rfl
  | @Typed.weak m Γ t A r B l ht _ => by
    rw [Term.cls_shift1]
    exact cls_of_typed ht
  | .conv ht _ => cls_of_typed ht
  | .prim _ _ _ _ => rfl

theorem cls_of_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} :
    DefEq Γ t s A r → t.cls Γ = r ∧ s.cls Γ = r
  | .refl ht => ⟨cls_of_typed ht, cls_of_typed ht⟩
  | .symm h => ⟨(cls_of_defEq h).2, (cls_of_defEq h).1⟩
  | .trans h h' => ⟨(cls_of_defEq h).1, (cls_of_defEq h').2⟩
  | .conv h _ => cls_of_defEq h
  | @DefEq.betaData m Γ i j A b B a _ _ hb ha =>
    ⟨rfl, by rw [Term.cls_subst0 Γ A i (cls_of_typed ha)]; exact cls_of_typed hb⟩
  | @DefEq.betaProp m Γ i A b B a _ hb ha =>
    ⟨rfl, by rw [Term.cls_subst0 Γ A i (cls_of_typed ha)]; exact cls_of_typed hb⟩
  | @DefEq.zeta m Γ i j v A b B hv hb =>
    ⟨rfl, by rw [Term.cls_subst0 Γ A i (cls_of_typed hv)]; exact cls_of_typed hb⟩
  | .eta _ hf => ⟨rfl, cls_of_typed hf⟩
  | .proofIrrel hh hh' => ⟨cls_of_typed hh, cls_of_typed hh'⟩
  | .congrPiData _ _ _ => ⟨rfl, rfl⟩
  | .congrPiProp _ _ => ⟨rfl, rfl⟩
  | .congrLamData _ _ _ => ⟨rfl, rfl⟩
  | .congrLamProp _ _ => ⟨rfl, rfl⟩
  | .congrAppData _ _ _ => ⟨rfl, rfl⟩
  | .congrAppProp _ _ => ⟨rfl, rfl⟩
  | .congrLet _ _ => ⟨rfl, rfl⟩
  | @DefEq.weak m Γ t s A r B l h _ => by
    rw [Term.cls_shift1, Term.cls_shift1]
    exact cls_of_defEq h
  | .congrPrim _ _ _ _ _ => ⟨rfl, rfl⟩
  | .eqRecRefl h => ⟨rfl, cls_of_typed (h 3)⟩
  | .sigmaFst _ h => ⟨rfl, cls_of_typed (h 2)⟩
  | .sigmaSnd _ h => ⟨rfl, cls_of_typed (h 3)⟩
  | .sigmaEta _ h => ⟨rfl, cls_of_typed (h 2)⟩
  | .downUp h => ⟨rfl, cls_of_typed (h 1)⟩
  | .upDown h => ⟨rfl, cls_of_typed (h 1)⟩
  | .sumRecInl _ _ _ => ⟨rfl, rfl⟩
  | .sumRecInr _ _ _ => ⟨rfl, rfl⟩
  | .natRecZero _ h => ⟨rfl, cls_of_typed (h 1)⟩
  | .natRecSucc _ _ _ => ⟨rfl, rfl⟩
  | .quotLiftMk _ _ _ _ => ⟨rfl, rfl⟩

end

end SolidLean.Calc
