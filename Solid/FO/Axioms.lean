import Solid.FO.Notions
import Solid.Gen.Definable
import Solid.Gen.Expansion
import Solid.Gen.Clauses

/-!
# The axioms of `H` and of `T(𝔉)` as first-order sentences

`H` is presented in the paper as a many-sorted first-order theory; the Lean
development states its axioms semantically (`IsTowerModel`, `SetAxioms`).
This file writes the axioms down as sentences of the many-sorted signature
`F.sig` of a clause family `F` — the tower symbols plus the symbols of `F`:

* for each sort `n`, the axioms of ZFC (`zfcAxioms n`), with Separation and
  Replacement as schemes ranging over all formulas of `F.sig` with parameters
  of arbitrary sorts;
* the well-formedness of the tower symbols (`liftZ n` is the graph of a total
  function, `bnd n` a singleton);
* the tower axioms (`j` is a membership embedding, `κ_n` inaccessible,
  `j` onto `V(κ_n)`, consecutive inaccessibles, no greatest inaccessible
  below `κ_0`);
* one defining axiom per symbol of `F`, when `F` is given by formulas.

`FO/Bridge.lean` shows that a structure satisfies these sentences iff it is a
model in the semantic sense with its definable class system
(`F.IsGenModel ⟨M, M.defSys⟩`).
-/

universe u

namespace SolidLean.Solid

open Classical

/-! ### Embedding tower formulas into an expanded signature -/

namespace Formula

variable {F : ClauseFamily.{u}}

/-- A formula of the tower signature as a formula of `F.sig`. -/
def inl : {k : ℕ} → {s : Fin k → ℕ} → Formula TowerSig k s → Formula F.sig k s
  | _, _, .rel r v hv => .rel (.inl r) v hv
  | _, _, .eq i j h => .eq i j h
  | _, _, .false_ => .false_
  | _, _, .imp φ ψ => .imp (inl φ) (inl ψ)
  | _, _, .ex n φ => .ex n (inl φ)

end Formula

/-- The tower reduct of a structure for `F.sig`. -/
abbrev Str.towerReduct {F : ClauseFamily.{u}} (M : Str.{u} F.sig) : Str.{u} TowerSig where
  U := M.U
  rel r := M.rel (.inl r)
  rel_sorts r t ht := M.rel_sorts (.inl r) t ht

theorem Formula.Sat_inl {F : ClauseFamily.{u}} (M : Str.{u} F.sig) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula TowerSig k s) (t : Fin k → Sorted.El M.U),
      (φ.inl (F := F)).Sat M t ↔ φ.Sat M.towerReduct t
  | _, _, .rel _ _ _, _ => Iff.rfl
  | _, _, .eq _ _ _, _ => Iff.rfl
  | _, _, .false_, _ => Iff.rfl
  | _, _, .imp φ ψ, t => by
    show (_ → _) ↔ (_ → _)
    rw [Sat_inl M φ t, Sat_inl M ψ t]
  | _, _, .ex n φ, t => by
    show (∃ x : Sorted.El M.U, x.1 = n ∧ _) ↔ ∃ x : Sorted.El M.U, x.1 = n ∧ _
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (Sat_inl M φ _).1 h⟩
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, (Sat_inl M φ _).2 h⟩

/-- The tower reduct of a well-formed structure is the structure of its
underlying tower. -/
theorem ClauseFamily.Δ_toStr_eq {F : ClauseFamily.{u}} {M : Str.{u} F.sig} (h : ClauseFamily.IsWF M) :
    (ClauseFamily.Δ M h).toStr = M.towerReduct := by
  unfold MemTower.toStr Str.towerReduct
  congr 1
  funext r
  cases r with
  | memZ n => exact ClauseFamily.Δ.memRel_eq h n
  | liftZ n => exact ClauseFamily.Δ.jRel_eq h n
  | bnd n => exact ClauseFamily.Δ.kappaRel_eq h n

/-! ### Sentences and closures -/

/-- Sentences: formulas without free variables. -/
abbrev Sentence (Sig : Signature) := Formula Sig 0 Fin.elim0

/-- Satisfaction of a sentence. -/
def Sentence.Holds {Sig : Signature} (σ : Sentence Sig) (M : Str.{u} Sig) : Prop := σ.Sat M Fin.elim0

/-- A structure is a model of a set of sentences. -/
def Str.Models {Sig : Signature} (M : Str.{u} Sig) (T : Set (Sentence Sig)) : Prop :=
  ∀ σ ∈ T, σ.Holds M

namespace Formula

variable {Sig : Signature}

/-- Change the sort assignment along a pointwise equality. -/
abbrev recast {k : ℕ} {s s' : Fin k → ℕ} (h : ∀ i, s' i = s i) (φ : Formula Sig k s) :
    Formula Sig k s' :=
  rename id h φ

theorem Sat_recast {M : Str.{u} Sig} {k : ℕ} {s s' : Fin k → ℕ} (h : ∀ i, s' i = s i)
    (φ : Formula Sig k s) (t : Fin k → Sorted.El M.U) : (recast h φ).Sat M t ↔ φ.Sat M t :=
  sat_rename id h φ t

theorem snoc_init_sorts {k : ℕ} (s : Fin (k + 1) → ℕ) :
    ∀ i, Fin.snoc (α := fun _ => ℕ) (Fin.init s) (s (Fin.last k)) i = s i := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · simp [Fin.init]

/-- Universal closure over all free variables (each at its own sort). -/
def closeAll : {k : ℕ} → {s : Fin k → ℕ} → Formula Sig k s → Sentence Sig
  | 0, _, φ => recast (fun i => i.elim0) φ
  | k + 1, s, φ => closeAll (all (s (Fin.last k)) (recast (snoc_init_sorts s) φ))

theorem Sat_closeAll {M : Str.{u} Sig} :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s),
      (closeAll φ).Holds M ↔ ∀ t : Fin k → Sorted.El M.U, (∀ i, (t i).1 = s i) → φ.Sat M t
  | 0, s, φ => by
    unfold closeAll Sentence.Holds
    rw [Sat_recast]
    constructor
    · intro h t _
      have : t = Fin.elim0 := funext fun i => i.elim0
      rw [this]; exact h
    · intro h
      exact h Fin.elim0 (fun i => i.elim0)
  | k + 1, s, φ => by
    unfold closeAll
    rw [Sat_closeAll]
    constructor
    · intro h t ht
      have h1 := h (Fin.init t) (fun i => ht i.castSucc)
      rw [Sat_all] at h1
      have h2 := h1 (t (Fin.last k)) (ht _)
      rw [Sat_recast] at h2
      have e : Fin.snoc (α := fun _ => Sorted.El M.U) (Fin.init t) (t (Fin.last k)) = t :=
        Fin.snoc_init_self t
      rw [e] at h2
      exact h2
    · intro h t ht
      rw [Sat_all]
      intro x hx
      rw [Sat_recast]
      refine h _ ?_
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa [Fin.init] using ht i

end Formula

namespace TF

/-- Universal closure of a constant-sort formula. -/
def closeC (n : ℕ) : {a : ℕ} → TF a (fun _ => n) → TF 0 (fun _ => n)
  | 0, φ => φ
  | a + 1, φ => closeC n (allC n (recast (IsConst.snoc (IsConst.const a n)) φ))

theorem Sat_closeC (T : MemTower.{u}) (n : ℕ) :
    ∀ {a : ℕ} (φ : TF a (fun _ => n)) (t : Fin 0 → T.El),
      (closeC n φ).Sat T.toStr t ↔ ∀ x : Fin a → T.U n, φ.Sat T.toStr (fun l => T.inj (x l))
  | 0, φ, t => by
    unfold closeC
    constructor
    · intro h x
      have : (fun l : Fin 0 => T.inj (x l)) = t := funext fun i => i.elim0
      rw [this]; exact h
    · intro h
      have := h (fun i => i.elim0)
      have e : (fun l : Fin 0 => T.inj ((fun i : Fin 0 => (i.elim0 : T.U n)) l)) = t :=
        funext fun i => i.elim0
      rw [e] at this; exact this
  | a + 1, φ, t => by
    unfold closeC
    rw [Sat_closeC T n]
    constructor
    · intro h y
      have h1 := (Sat_allC T _ (Fin.init y)).1 (h (Fin.init y)) (y (Fin.last a))
      erw [Formula.sat_rename] at h1
      have e : Fin.snoc (α := fun _ => T.U n) (Fin.init y) (y (Fin.last a)) = y := Fin.snoc_init_self y
      rw [e] at h1
      exact h1
    · intro h x
      rw [Sat_allC]
      intro z
      erw [Formula.sat_rename]
      exact h _

/-- A constant-sort sentence as a sentence. -/
abbrev toSentence {n : ℕ} (φ : TF 0 (fun _ => n)) : Sentence TowerSig :=
  Formula.recast (fun i => i.elim0) φ

theorem Holds_toSentence (T : MemTower.{u}) {n : ℕ} (φ : TF 0 (fun _ => n)) :
    (toSentence φ).Holds T.toStr ↔ φ.Sat T.toStr Fin.elim0 :=
  Formula.Sat_recast _ φ _

end TF


/-! ### The axioms of ZFC at a sort -/

namespace TF

variable (n : ℕ)

private abbrev h0 : IsConst (fun _ : Fin 0 => n) n := IsConst.const 0 n
private abbrev h1 : IsConst (fun _ : Fin 1 => n) n := IsConst.const 1 n
private abbrev h2 : IsConst (fun _ : Fin 2 => n) n := IsConst.const 2 n

/-- Extensionality. -/
def extAx : TF 0 (fun _ => n) :=
  closeC n (a := 2) (Formula.imp
    (allC n (Formula.iff (memC (h2 n).snoc 2 0) (memC (h2 n).snoc 2 1)))
    (eqC (h2 n) 0 1))

/-- The empty set. -/
def emptyAx : TF 0 (fun _ => n) := exC n (isEmptyC (h0 n).snoc 0)

/-- Pairing. -/
def pairAx : TF 0 (fun _ => n) := closeC n (a := 2) (exC n (pairC (h2 n).snoc 0 1 2))

/-- Union. -/
def unionAx : TF 0 (fun _ => n) := closeC n (a := 1) (exC n (unionSetC (h1 n).snoc 0 1))

/-- Power set. -/
def powerAx : TF 0 (fun _ => n) := closeC n (a := 1) (exC n (powerSetC (h1 n).snoc 0 1))

/-- Infinity. -/
def infAx : TF 0 (fun _ => n) :=
  exC n (Formula.and
    (exC n (Formula.and (isEmptyC (h0 n).snoc.snoc 1) (memC (h0 n).snoc.snoc 1 0)))
    (allC n (Formula.imp (memC (h0 n).snoc.snoc 1 0)
      (exC n (Formula.and (succC (h0 n).snoc.snoc.snoc 1 2) (memC (h0 n).snoc.snoc.snoc 2 0))))))

/-- Foundation. -/
def foundAx : TF 0 (fun _ => n) :=
  closeC n (a := 1) (Formula.imp (nonemptyC (h1 n) 0)
    (exC n (Formula.and (memC (h1 n).snoc 1 0)
      (allC n (Formula.imp (memC (h1 n).snoc.snoc 2 1) (Formula.not (memC (h1 n).snoc.snoc 2 0)))))))

/-- Choice. -/
def choiceAx : TF 0 (fun _ => n) :=
  closeC n (a := 1) (Formula.imp
    (allC n (Formula.imp (memC (h1 n).snoc 1 0) (nonemptyC (h1 n).snoc 1)))
    (exC n (Formula.and (funOnC (h1 n).snoc 1 0)
      (allC n (allC n (Formula.imp (funAppC (h1 n).snoc.snoc.snoc 1 2 3)
        (memC (h1 n).snoc.snoc.snoc 3 2)))))))

/-! ### Well-formedness of the tower symbols and the tower axioms -/

/-- `j_n` is total. -/
def liftTotalAx : Sentence TowerSig :=
  Formula.closeAll (k := 1) (s := ![n])
    (Formula.ex (n + 1) (liftZF n 0 1 (by simp) (by simp)))

/-- `j_n` is single-valued. -/
def liftUniqueAx : Sentence TowerSig :=
  Formula.closeAll (k := 3) (s := ![n, n + 1, n + 1])
    (Formula.imp (liftZF n 0 1 (by simp) (by simp))
      (Formula.imp (liftZF n 0 2 (by simp) (by simp)) (Formula.eq 1 2 (by simp))))

/-- `κ_n` exists. -/
def bndExistsAx : Sentence TowerSig :=
  Formula.closeAll (k := 0) (s := ![]) (Formula.ex (n + 1) (bndF n 0 (by simp)))

/-- `κ_n` is unique. -/
def bndUniqueAx : Sentence TowerSig :=
  Formula.closeAll (k := 2) (s := ![n + 1, n + 1])
    (Formula.imp (bndF n 0 (by simp)) (Formula.imp (bndF n 1 (by simp)) (Formula.eq 0 1 (by simp))))

/-- `j_n` is injective. -/
def jInjAx : Sentence TowerSig :=
  Formula.closeAll (k := 4) (s := ![n, n, n + 1, n + 1])
    (Formula.imp (liftZF n 0 2 (by simp) (by simp))
      (Formula.imp (liftZF n 1 3 (by simp) (by simp))
        (Formula.imp (Formula.eq 2 3 (by simp)) (Formula.eq 0 1 (by simp)))))

/-- `j_n` preserves and reflects membership. -/
def jMemAx : Sentence TowerSig :=
  Formula.closeAll (k := 4) (s := ![n, n, n + 1, n + 1])
    (Formula.imp (liftZF n 0 2 (by simp) (by simp))
      (Formula.imp (liftZF n 1 3 (by simp) (by simp))
        (Formula.iff (memF (n + 1) 2 3 (by simp) (by simp)) (memF n 0 1 (by simp) (by simp)))))

/-- `κ_n` is inaccessible (in sort `n + 1`). -/
def kappaInaccAx : Sentence TowerSig :=
  toSentence (allC (n + 1) (Formula.imp (bndF n 0 ((IsConst.const 0 (n + 1)).snoc 0))
    (inaccC (IsConst.const 0 (n + 1)).snoc 0)))

/-- `j_n` maps sort `n` onto `V(κ_n)`. -/
def jImageAx : Sentence TowerSig :=
  toSentence (exC (n + 1) (exC (n + 1) (Formula.and
    (bndF n 1 ((IsConst.const 0 (n + 1)).snoc.snoc 1))
    (Formula.and (isVC (IsConst.const 0 (n + 1)).snoc.snoc 1 0)
      (allC (n + 1) (Formula.iff (memC (IsConst.const 0 (n + 1)).snoc.snoc.snoc 2 0)
        (Formula.ex n (liftZF n 3 2 (by simp) (by simp)))))))))

/-- `κ_{n+1}` is the least inaccessible above `j(κ_n)` (in sort `n + 2`). -/
def nextInaccAx : Sentence TowerSig :=
  Formula.closeAll (k := 3) (s := ![n + 1, n + 2, n + 2])
    (Formula.imp (bndF n 0 (by simp))
      (Formula.imp (liftZF (n + 1) 0 1 (by simp) (by simp))
        (Formula.imp (bndF (n + 1) 2 (by simp))
          (at_ (nextInaccC (IsConst.const 2 (n + 2)) 0 1) ![1, 2] (by simp [Fin.forall_fin_two])))))

/-- No greatest inaccessible below `κ_0` (in sort `1`). -/
def bottomAx : Sentence TowerSig :=
  toSentence (allC 1 (Formula.imp (bndF 0 0 ((IsConst.const 0 1).snoc 0))
    (noGreatestInaccC (IsConst.const 0 1).snoc 0)))

end TF

/-! ### The schemes, over the expanded signature -/

namespace ClauseFamily

variable (F : ClauseFamily.{u})

/-- Membership at sort `n` in `F.sig`. -/
def memS (n : ℕ) {k : ℕ} {s : Fin k → ℕ} (i j : Fin k) (hi : s i = n) (hj : s j = n) :
    Formula F.sig k s :=
  (TF.memF n i j hi hj).inl

/-- The context `(base, x, s, y)` for the Separation scheme. -/
abbrev sepCtx (n : ℕ) {m : ℕ} (base : Fin m → ℕ) : Fin (m + 3) → ℕ :=
  Fin.snoc (Fin.snoc (Fin.snoc base n) n) n

/-- Move `ψ(base, y)` into the context `(base, x, s, y)`. -/
def sepBody (n : ℕ) {m : ℕ} {base : Fin m → ℕ} (ψ : Formula F.sig (m + 1) (Fin.snoc base n)) :
    Formula F.sig (m + 3) (sepCtx n base) :=
  Formula.rename
    (fun i => Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 2))
      (fun j => j.castSucc.castSucc.castSucc) i)
    (by intro i; refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [sepCtx]) ψ

/-- Separation for `ψ(base, y)`: `∀ base ∀ x ∃ s ∀ y (y ∈ s ↔ y ∈ x ∧ ψ)`. -/
def sepAx (n : ℕ) {m : ℕ} (base : Fin m → ℕ) (ψ : Formula F.sig (m + 1) (Fin.snoc base n)) :
    Sentence F.sig :=
  Formula.closeAll (Formula.all n (Formula.ex n (Formula.all n
    (Formula.iff (F.memS n (Fin.last (m + 2)) (Fin.last (m + 1)).castSucc (by simp) (by simp))
      (Formula.and
        (F.memS n (Fin.last (m + 2)) (Fin.last m).castSucc.castSucc (by simp) (by simp))
        (F.sepBody n ψ))))))

/-- The context `(base, x, y, z)`. -/
abbrev repCtx3 (n : ℕ) {m : ℕ} (base : Fin m → ℕ) : Fin (m + 3) → ℕ :=
  Fin.snoc (Fin.snoc (Fin.snoc base n) n) n

/-- The context `(base, x, ·, ·, ·)` with four variables of sort `n` after `base`. -/
abbrev repCtx4 (n : ℕ) {m : ℕ} (base : Fin m → ℕ) : Fin (m + 4) → ℕ :=
  Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc base n) n) n) n

/-- `ψ(base, y, z)` in the context `(base, x, y, z)`. -/
def repBody1 (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) :
    Formula F.sig (m + 3) (repCtx3 n base) :=
  Formula.rename
    (fun i => Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 2))
      (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 1)).castSucc
        (fun j => j.castSucc.castSucc.castSucc) i') i)
    (by
      intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [repCtx3]
      · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp [repCtx3]) ψ

/-- `ψ(base, y, z')` in the context `(base, x, y, z, z')`. -/
def repBody2 (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) :
    Formula F.sig (m + 4) (repCtx4 n base) :=
  Formula.rename
    (fun i => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 3))
      (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 1)).castSucc.castSucc
        (fun j => j.castSucc.castSucc.castSucc.castSucc) i') i)
    (by
      intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [repCtx4]
      · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp [repCtx4]) ψ

/-- `ψ(base, y, z)` in the context `(base, x, s, z, y)`. -/
def repBody3 (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) :
    Formula F.sig (m + 4) (repCtx4 n base) :=
  Formula.rename
    (fun i => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 2)).castSucc
      (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 3))
        (fun j => j.castSucc.castSucc.castSucc.castSucc) i') i)
    (by
      intro i
      refine Fin.lastCases ?_ (fun i' => ?_) i
      · simp [repCtx4]
      · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp [repCtx4]) ψ

/-- Replacement for `ψ(base, y, z)`:
`∀ base ∀ x [(∀ y ∈ x ∃! z ψ) → ∃ s ∀ z (z ∈ s ↔ ∃ y (y ∈ x ∧ ψ))]`. -/
def repAx (n : ℕ) {m : ℕ} (base : Fin m → ℕ)
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) : Sentence F.sig :=
  Formula.closeAll (k := m + 1) (s := Fin.snoc base n) (Formula.imp
    (Formula.all n (Formula.imp
      (F.memS n (Fin.last (m + 1)) (Fin.last m).castSucc (by simp) (by simp))
      (Formula.ex n (Formula.and (F.repBody1 n ψ)
        (Formula.all n (Formula.imp (F.repBody2 n ψ)
          (Formula.eq (Fin.last (m + 3)) (Fin.last (m + 2)).castSucc (by simp))))))))
    (Formula.ex n (Formula.all n (Formula.iff
      (F.memS n (Fin.last (m + 2)) (Fin.last (m + 1)).castSucc (by simp) (by simp))
      (Formula.ex n (Formula.and
        (F.memS n (Fin.last (m + 3)) (Fin.last m).castSucc.castSucc.castSucc (by simp) (by simp))
        (F.repBody3 n ψ)))))))

/-- The axioms of `H` over `F.sig`. -/
def Hax : Set (Sentence F.sig) :=
  {σ | (∃ n, σ = (TF.toSentence (TF.extAx n)).inl) ∨ (∃ n, σ = (TF.toSentence (TF.emptyAx n)).inl) ∨
    (∃ n, σ = (TF.toSentence (TF.pairAx n)).inl) ∨ (∃ n, σ = (TF.toSentence (TF.unionAx n)).inl) ∨
    (∃ n, σ = (TF.toSentence (TF.powerAx n)).inl) ∨ (∃ n, σ = (TF.toSentence (TF.infAx n)).inl) ∨
    (∃ n, σ = (TF.toSentence (TF.foundAx n)).inl) ∨ (∃ n, σ = (TF.toSentence (TF.choiceAx n)).inl) ∨
    (∃ (n m : ℕ) (base : Fin m → ℕ) (ψ : Formula F.sig (m + 1) (Fin.snoc base n)), σ = F.sepAx n base ψ) ∨
    (∃ (n m : ℕ) (base : Fin m → ℕ) (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)),
      σ = F.repAx n base ψ) ∨
    (∃ n, σ = (TF.liftTotalAx n).inl) ∨ (∃ n, σ = (TF.liftUniqueAx n).inl) ∨
    (∃ n, σ = (TF.bndExistsAx n).inl) ∨ (∃ n, σ = (TF.bndUniqueAx n).inl) ∨
    (∃ n, σ = (TF.jInjAx n).inl) ∨ (∃ n, σ = (TF.jMemAx n).inl) ∨
    (∃ n, σ = (TF.kappaInaccAx n).inl) ∨ (∃ n, σ = (TF.jImageAx n).inl) ∨
    (∃ n, σ = (TF.nextInaccAx n).inl) ∨ σ = TF.bottomAx.inl}

/-- The defining axiom of a symbol of a clause family given by formulas. -/
noncomputable def defAx (Sym : Type) (arity : Sym → ℕ) (sortAt : (f : Sym) → Fin (arity f) → ℕ)
    (φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)) (f : Sym) :
    Sentence (ofFormulas.{u} Sym arity sortAt φ).sig :=
  Formula.closeAll (Formula.iff (Formula.rel (Sum.inr f) (fun i => i) (fun _ => rfl)) (φ f).inl)

/-- The axioms of `T(𝔉)` for a clause family given by formulas: `H` plus one
defining axiom per symbol. -/
noncomputable def TLax (Sym : Type) (arity : Sym → ℕ) (sortAt : (f : Sym) → Fin (arity f) → ℕ)
    (φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)) :
    Set (Sentence (ofFormulas.{u} Sym arity sortAt φ).sig) :=
  (ofFormulas Sym arity sortAt φ).Hax ∪ Set.range (defAx Sym arity sortAt φ)

end ClauseFamily

end SolidLean.Solid
