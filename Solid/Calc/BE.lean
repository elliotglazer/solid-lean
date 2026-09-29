module

public import Solid.Gen.SortSolid
public import Solid.Gen.SortExpand
public import Solid.Calc.Theory

/-!
# The `B_n / E_n` presentation of `T_L` (draft 2, §6.3)

Draft 2 presents `T_L` with sorts `B_n` (type objects at level `n + 1`),
`E_n` (typed elements at level `n + 1`) and `Ω` (propositions, which are the
type objects at level `0`, so `Ω = B_0`), with projections `π_n`, the
universe objects `u_n`, the identification of `B_n` with the fiber of
`E_{n+1}` over `u_n`, the truth predicate `Tr`, the graph symbols of the
calculus on the `E`-sorts, and the relations `Code_n`, `Value_n` relating
each new sort to the internal set tower `Z`.  In the formalization the tower
sorts *are* the `Z_n`, so this presentation is the expansion of `T_L` by the
definable sorts

* `B_r = {A ∈ Z_{r+1} | A ∈ 𝒰_r}` (coded in `Z_{r+1}` by `Code_r`, the
  encoding symbol of the sort),
* `E_r = {⟨A, j a⟩ ∈ Z_{r+1} | A ∈ 𝒰_r, j a ∈ A}` (coded by `Value_r`),

with the further symbols defined by tower formulas on the codes.  It is an
instance of `SortExp`, so it is solid by `SortExp.solid`: this is the
"trivial sort encoding" identifying the two presentations.

New sort `2r` is `B_r` and new sort `2r + 1` is `E_r`; both are coded in
the tower sort `r + 1`.
-/

@[expose] public section

universe u

namespace SolidLean.Solid.Formula

variable {Sig : Signature}

/-- Conjunction of a finite family. -/
def bigAnd : ∀ {n k : ℕ} {s : Fin k → ℕ}, (Fin n → Formula Sig k s) → Formula Sig k s
  | 0, _, _, _ => true_
  | _ + 1, _, _, φ => and (φ 0) (bigAnd fun i => φ i.succ)

theorem Sat_bigAnd {M : Str.{u} Sig} : ∀ {n k : ℕ} {s : Fin k → ℕ} (φ : Fin n → Formula Sig k s)
    (t : Fin k → Sorted.El M.U), (bigAnd φ).Sat M t ↔ ∀ i, (φ i).Sat M t
  | 0, _, _, _, t => by
    show (true_ : Formula Sig _ _).Sat M t ↔ _
    rw [Sat_true]
    exact ⟨fun _ i => i.elim0, fun _ => trivial⟩
  | n + 1, _, _, φ, t => by
    show (and (φ 0) (bigAnd fun i => φ i.succ)).Sat M t ↔ _
    rw [Sat_and, Sat_bigAnd, Fin.forall_fin_succ]

theorem append_eq_snoc {α : Type*} {m k : ℕ} (s : Fin m → α) (b : Fin (k + 1) → α) :
    Fin.append s b = Fin.snoc (α := fun _ => α) (Fin.append s (Fin.init b)) (b (Fin.last k)) := by
  rw [← append_snoc, Fin.snoc_init_self]

/-- Existential quantification of a trailing block of variables of sorts `b`. -/
def exBlock : ∀ {m k : ℕ} {s : Fin m → ℕ} (b : Fin k → ℕ),
    Formula Sig (m + k) (Fin.append s b) → Formula Sig m s
  | m, 0, s, b, φ => rename (fun i => ⟨i.1, i.2⟩) (fun i => (Fin.append_left s b ⟨i.1, i.2⟩).symm) φ
  | _, k + 1, s, b, φ =>
    exBlock (Fin.init b) (.ex (b (Fin.last k))
      (rename id (fun i => (congrFun (append_eq_snoc s b) i).symm) φ))

theorem Sat_exBlock {M : Str.{u} Sig} : ∀ {m k : ℕ} {s : Fin m → ℕ} (b : Fin k → ℕ)
    (φ : Formula Sig (m + k) (Fin.append s b)) (t : Fin m → Sorted.El M.U),
    (exBlock b φ).Sat M t ↔ ∃ u : Fin k → Sorted.El M.U, (∀ i, (u i).1 = b i) ∧
      φ.Sat M (Fin.append t u)
  | m, 0, s, b, φ, t => by
    show (rename _ _ φ).Sat M t ↔ _
    rw [sat_rename]
    constructor
    · intro h
      refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
      have e : Fin.append t (Fin.elim0 : Fin 0 → Sorted.El M.U) = fun i : Fin (m + 0) => t ⟨i.1, i.2⟩ := by
        funext i
        exact Fin.append_left t Fin.elim0 ⟨i.1, i.2⟩
      rw [e]; exact h
    · rintro ⟨u, -, h⟩
      have hu : u = Fin.elim0 := funext fun i => i.elim0
      subst hu
      have e : Fin.append t (Fin.elim0 : Fin 0 → Sorted.El M.U) = fun i : Fin (m + 0) => t ⟨i.1, i.2⟩ := by
        funext i
        exact Fin.append_left t Fin.elim0 ⟨i.1, i.2⟩
      rw [e] at h; exact h
  | m, k + 1, s, b, φ, t => by
    show (exBlock (Fin.init b) (.ex (b (Fin.last k)) _)).Sat M t ↔ _
    rw [Sat_exBlock]
    constructor
    · rintro ⟨u, hu, x, hx, h⟩
      rw [sat_rename] at h
      refine ⟨Fin.snoc u x, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hx
        · simp only [Fin.snoc_castSucc]; exact hu i
      · rw [append_snoc]; exact h
    · rintro ⟨u, hu, h⟩
      refine ⟨Fin.init u, fun i => hu (Fin.castSucc i), u (Fin.last k), hu (Fin.last k), ?_⟩
      rw [sat_rename]
      show φ.Sat M (Fin.snoc (Fin.append t (Fin.init u)) (u (Fin.last k)))
      rw [← append_snoc, Fin.snoc_init_self]; exact h

end SolidLean.Solid.Formula

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

/-! ### The formulas of the presentation -/

namespace BE

/-- The tower sort coding new sort `m`: `B_r` and `E_r` are coded in sort `r + 1`. -/
def σ (m : ℕ) : ℕ := m / 2 + 1

theorem σ_B (r : ℕ) : σ (2 * r) = r + 1 := by unfold σ; omega

theorem σ_E (r : ℕ) : σ (2 * r + 1) = r + 1 := by unfold σ; omega

/-- `x_p` is a type object at level `r`: `j x_p ∈ 𝒰_r`. -/
def isTypeObjF {k : ℕ} {s : Fin k → ℕ} (r : ℕ) (p : Fin k) (hp : s p = r + 1) : TF k s :=
  .ex (r + 2) (Formula.and (univF r (Fin.last k) (by simp))
    (tmemF (r + 1) (Fin.castSucc p) (Fin.last k) (by simp [hp]) (by simp)))

/-- `x_e = ⟨x_A, j x_w⟩`, for `x_A, x_e` of sort `r + 1` and `x_w` of sort `r`. -/
def isPairOfF {k : ℕ} {s : Fin k → ℕ} (r : ℕ) (A w e : Fin k) (hA : s A = r + 1) (hw : s w = r)
    (he : s e = r + 1) : TF k s :=
  .ex (r + 1) (Formula.and (liftZF r (Fin.castSucc w) (Fin.last k) (by simp [hw]) (by simp))
    (ordPairF (r + 1) (Fin.castSucc A) (Fin.last k) (Fin.castSucc e) (by simp [hA]) (by simp)
      (by simp [he])))

/-- `x_e` is a typed element at level `r`: `x_e = ⟨A, j a⟩` with `A` a type
object at level `r` and `j a ∈ A`. -/
def isTypedElF {k : ℕ} {s : Fin k → ℕ} (r : ℕ) (e : Fin k) (he : s e = r + 1) : TF k s :=
  .ex (r + 1) (.ex r (Formula.and
    (isPairOfF r (Fin.castSucc (Fin.last k)) (Fin.last (k + 1)) (Fin.castSucc (Fin.castSucc e))
      (by simp) (by simp) (by simp [he]))
    (Formula.and
      (isTypeObjF r (Fin.castSucc (Fin.last k)) (by simp))
      (tmemF r (Fin.last (k + 1)) (Fin.castSucc (Fin.last k)) (by simp) (by simp)))))

/-- `x_w` is the underlying element of the typed element `x_e`. -/
def decodeF {k : ℕ} {s : Fin k → ℕ} (r : ℕ) (e w : Fin k) (he : s e = r + 1) (hw : s w = r) :
    TF k s :=
  .ex (r + 1) (isPairOfF r (Fin.last k) (Fin.castSucc w) (Fin.castSucc e) (by simp) (by simp [hw])
    (by simp [he]))

/-- The domain formula of new sort `m`: `B_r` for `m = 2r`, `E_r` for `m = 2r + 1`. -/
def domF (m : ℕ) : Formula TowerSig 1 ![σ m] :=
  if m % 2 = 0 then isTypeObjF (m / 2) 0 (by simp [σ]) else isTypedElF (m / 2) 0 (by simp [σ])

/-- The further symbols of the presentation. -/
inductive Sym'
  /-- `π_r ⊆ E_r × B_r`, the type of a typed element. -/
  | pi (r : ℕ)
  /-- `u_r ∈ B_{r+1}`, the universe object. -/
  | univ (r : ℕ)
  /-- The identification of `B_r` with the fiber of `E_{r+1}` over `u_r`. -/
  | fib (r : ℕ)
  /-- `Tr ⊆ Ω = B_0`, truth. -/
  | tr
  /-- The graph `⟦t⟧_Γ` of a term, on the `E`-sorts. -/
  | graph (s : Calc.Sym)

/-- New sort `B_r`. -/
abbrev B (r : ℕ) : ℕ ⊕ ℕ := Sum.inr (2 * r)

/-- New sort `E_r`. -/
abbrev E (r : ℕ) : ℕ ⊕ ℕ := Sum.inr (2 * r + 1)

/-- The levels of the arguments of a graph symbol: those of the context, then
the classifier of the term. -/
abbrev lev (s : Calc.Sym) : Fin (s.1 + 1) → ℕ :=
  Fin.snoc (α := fun _ => ℕ) s.2.1.levels (s.2.2.cls s.2.1)

abbrev arity : Sym' → ℕ
  | .pi _ => 2
  | .univ _ => 1
  | .fib _ => 2
  | .tr => 1
  | .graph s => s.1 + 1

abbrev sortAt : (f : Sym') → Fin (arity f) → ℕ ⊕ ℕ
  | .pi r => ![E r, B r]
  | .univ r => ![B (r + 1)]
  | .fib r => ![B r, E (r + 1)]
  | .tr => ![B 0]
  | .graph s => fun i => E (lev s i)

theorem sortAt_graph (s : Calc.Sym) (i : Fin (s.1 + 1)) :
    Sum.elim id σ (sortAt (.graph s) i) = lev s i + 1 := σ_E _

/-- The clause of a further symbol, on the codes of its arguments. -/
def symF : (f : Sym') → Formula TowerSig (arity f) (fun i => Sum.elim id σ (sortAt f i))
  | .pi r => .ex r (isPairOfF r 1 (Fin.last 2) 0 (by show σ (2 * r) = r + 1; exact σ_B r) (by simp)
      (by show σ (2 * r + 1) = r + 1; exact σ_E r))
  | .univ r => univF r 0 (by show σ (2 * (r + 1)) = r + 2; exact σ_B (r + 1))
  | .fib r => .ex (r + 2) (Formula.and (univF r (Fin.last 2) (by simp))
      (isPairOfF (r + 1) (Fin.last 2) 0 1 (by simp) (by show σ (2 * r) = r + 1; exact σ_B r)
        (by show σ (2 * (r + 1) + 1) = r + 1 + 1; exact σ_E (r + 1))))
  | .tr => trueF 1 0 (σ_B 0)
  | .graph s =>
    Formula.exBlock (lev s)
      (Formula.and
        (Formula.rename (Fin.natAdd (s.1 + 1)) (fun i => Fin.append_right _ _ i) (eval s.2.1 s.2.2))
        (Formula.bigAnd fun i => decodeF (lev s i)
          (Fin.castAdd (s.1 + 1) i) (Fin.natAdd (s.1 + 1) i)
          (by rw [Fin.append_left]; exact sortAt_graph s i) (by rw [Fin.append_right])))

end BE

/-- **The `B_n / E_n` presentation of `T_L`**, as a definable-sort expansion
of the set-encoded presentation. -/
noncomputable def BE : SortExp LAnn.{u} where
  σ := BE.σ
  domF := BE.domF
  Sym := BE.Sym'
  arity := BE.arity
  sortAt := BE.sortAt
  symF := BE.symF

/-- The models of the `B_n / E_n` presentation. -/
abbrev IsBEModel (N : StrWithSys.{u} BE.sig) : Prop := BE.IsModel N

/-- **The `B_n / E_n` presentation of the core annotated calculus is solid**:
the sort encoding transfers solidity from `T_L`. -/
theorem BE_solid : BE.{u}.IsSolid := SortExp.solid BE

/-- **Every model of `T_L` expands to a model of the `B_n / E_n` presentation**
(canonically: the new sorts are the defined subsets), whose base reduct is
isomorphic to the model (`SortExp.expBaseIso`). -/
theorem BE_expand (N : StrWithSys.{u} LAnn.sig) (hN : IsTLModel N) :
    IsBEModel ⟨BE.expModel hN, BE.expSys hN⟩ := BE.expand_isModel hN

/-- **Every model of the `B_n / E_n` presentation restricts to a model of `T_L`.**
With `BE_expand`, the two presentations have the same models up to the sort
encoding; with `BE_solid`, solidity transfers. -/
theorem BE_reduct (N : StrWithSys.{u} BE.sig) (hN : IsBEModel N) :
    IsTLModel ⟨BE.baseStr N.M, BE.baseSys N.𝒟⟩ := hN.base

end SolidLean.Calc
