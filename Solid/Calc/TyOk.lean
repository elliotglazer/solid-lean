import Solid.Calc.Contexts

/-!
# Well-classified types

A syntactic invariant of derivations, complementing Lemma 3.2: the type of a
certified term has classifier `r + 1`, and the same holds recursively for
the domain and codomain of every product appearing as a type.  This is the
part of "type correctness" that the evaluator's coherence guards need; it is
proved by a direct induction on derivations, with no inversion.
-/

namespace SolidLean.Calc

open Term

/-- The level of the codomain of a product of kind `k` annotated `j`. -/
def kindLevel : Kind → ℕ → ℕ
  | .data, j => j
  | .prop, _ => 0

/-- `A` is well classified as a type of level `r` in `Γ`. -/
def TyOk : {m : ℕ} → Ctx m → Term → ℕ → Prop
  | _, Γ, pi k i j A B, r =>
      (pi k i j A B).cls Γ = r + 1 ∧ TyOk Γ A i ∧ TyOk (Γ.snoc A i) B (kindLevel k j)
  | _, Γ, t, r => t.cls Γ = r + 1

/-- The parts of a product are well classified (vacuous for other terms). -/
def PiParts {m : ℕ} (Γ : Ctx m) (t : Term) : Prop :=
  ∀ k i j A B, t = pi k i j A B → TyOk Γ A i ∧ TyOk (Γ.snoc A i) B (kindLevel k j)

theorem TyOk.cls {m : ℕ} {Γ : Ctx m} {t : Term} {r : ℕ} (h : TyOk Γ t r) : t.cls Γ = r + 1 := by
  cases t with
  | pi k i j A B => exact h.1
  | _ => exact h

theorem TyOk.piParts {m : ℕ} {Γ : Ctx m} {t : Term} {r : ℕ} (h : TyOk Γ t r) : PiParts Γ t := by
  intro k i j A B ht
  subst ht
  exact h.2

theorem TyOk.of_cls {m : ℕ} {Γ : Ctx m} {t : Term} {r : ℕ} (hc : t.cls Γ = r + 1)
    (hp : PiParts Γ t) : TyOk Γ t r := by
  cases t with
  | pi k i j A B => exact ⟨hc, hp k i j A B rfl⟩
  | _ => exact hc

theorem PiParts.var {m : ℕ} (Γ : Ctx m) (x : ℕ) : PiParts Γ (var x) := fun _ _ _ _ _ h => by cases h
theorem PiParts.univ {m : ℕ} (Γ : Ctx m) (n : ℕ) : PiParts Γ (univ n) := fun _ _ _ _ _ h => by cases h
theorem PiParts.lam {m : ℕ} (Γ : Ctx m) (k i j A b) : PiParts Γ (lam k i j A b) :=
  fun _ _ _ _ _ h => by cases h
theorem PiParts.app {m : ℕ} (Γ : Ctx m) (k j f a) : PiParts Γ (app k j f a) :=
  fun _ _ _ _ _ h => by cases h
theorem PiParts.letE {m : ℕ} (Γ : Ctx m) (j A v b) : PiParts Γ (letE j A v b) :=
  fun _ _ _ _ _ h => by cases h
theorem PiParts.prim {m : ℕ} (Γ : Ctx m) {n : ℕ} (c : Prim n) (args : Fin n → Term) :
    PiParts Γ (prim c args) := fun _ _ _ _ _ h => by cases h

theorem TyOk.univ {m : ℕ} (Γ : Ctx m) (n : ℕ) : TyOk Γ (univ n) (n + 1) := rfl

theorem TyOk.pi_data {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : TyOk Γ A i)
    (hB : TyOk (Γ.snoc A i) B j) : TyOk Γ (pi .data i j A B) (max i j) := ⟨rfl, hA, hB⟩

theorem TyOk.pi_prop {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : TyOk Γ A i)
    (hB : TyOk (Γ.snoc A i) B 0) : TyOk Γ (pi .prop i j A B) 0 := ⟨rfl, hA, hB⟩

theorem PiParts.pi {m : ℕ} {Γ : Ctx m} {k : Kind} {i j : ℕ} {A B : Term} (hA : TyOk Γ A i)
    (hB : TyOk (Γ.snoc A i) B (kindLevel k j)) : PiParts Γ (pi k i j A B) := by
  intro k' i' j' A' B' h
  cases h
  exact ⟨hA, hB⟩

/-- The result type of a primitive application is well classified at the level
of the application, given the classifiers and the product parts of the
arguments (the result type is never itself a product). -/
theorem Prim.resultTyOk {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) {args : Fin n → Term}
    (hcls : ∀ k, (args k).cls Γ = c.argSort k) (hpp : ∀ k, PiParts Γ (args k)) :
    TyOk Γ (c.resultType m args) c.level := by
  cases c <;> first
    | exact TyOk.univ _ _
    | rfl
    | exact TyOk.of_cls (hcls 0) (hpp 0)
    | exact TyOk.of_cls (hcls 1) (hpp 1)
    | exact TyOk.of_cls (hcls 2) (hpp 2)

/-! ### Invariance under the level structure of the context -/

theorem Ctx.lev_congr {m : ℕ} {Γ Γ' : Ctx m} (h : Γ.levels = Γ'.levels) (x : ℕ) :
    Γ.lev x = Γ'.lev x := by
  simp only [Ctx.lev]
  split_ifs with hx
  · have := congrFun h ⟨x, hx⟩
    simpa [Ctx.levels] using this
  · rfl

theorem Term.cls_congr {m : ℕ} {Γ Γ' : Ctx m} (h : Γ.levels = Γ'.levels) (t : Term) :
    t.cls Γ = t.cls Γ' := by
  cases t with
  | var x => exact Ctx.lev_congr h x
  | _ => rfl

theorem TyOk.congr_levels {m : ℕ} {Γ Γ' : Ctx m} (h : Γ.levels = Γ'.levels) :
    ∀ (t : Term) (r : ℕ), TyOk Γ t r → TyOk Γ' t r
  | pi k i j A B, r, ⟨hc, hA, hB⟩ =>
    ⟨by rw [← Term.cls_congr h]; exact hc, TyOk.congr_levels h A i hA,
     TyOk.congr_levels (by rw [Ctx.levels_snoc, Ctx.levels_snoc, h]) B _ hB⟩
  | var x, r, hc => by show (var x).cls Γ' = r + 1; rw [← Term.cls_congr h]; exact hc
  | Term.univ n, r, hc => hc
  | lam k i j A b, r, hc => hc
  | app k j f a, r, hc => hc
  | letE j A v b, r, hc => hc
  | prim c args, r, hc => hc

/-! ### Shifting -/

theorem TyOk.shift (p e : ℕ) : ∀ (t : Term) {e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ)
    (r : ℕ), TyOk Γ t r → TyOk (Γ.insert p e Δ) (Term.shift p e t) r
  | pi k i j A B, e', Γ, Δ, r, ⟨hc, hA, hB⟩ => by
    refine ⟨?_, TyOk.shift p e A Γ Δ i hA, ?_⟩
    · show (Term.shift p e (pi k i j A B)).cls _ = r + 1
      rw [Ctx.cls_shift_insert]; exact hc
    · rw [Ctx.insert_snoc]
      exact TyOk.shift p e B (e' := e' + 1) (Γ.snoc A i) Δ _ hB
  | var x, e', Γ, Δ, r, hc => by
    obtain ⟨y, hy⟩ : ∃ y, Term.shift p e (var x) = var y := by
      simp only [Term.shift]; split_ifs <;> exact ⟨_, rfl⟩
    rw [hy]
    show (var y).cls _ = r + 1
    rw [← hy, Ctx.cls_shift_insert]; exact hc
  | Term.univ n, e', Γ, Δ, r, hc => hc
  | lam k i j A b, e', Γ, Δ, r, hc => by
    show (Term.shift p e (lam k i j A b)).cls _ = r + 1
    rw [Ctx.cls_shift_insert]; exact hc
  | app k j f a, e', Γ, Δ, r, hc => by
    show (Term.shift p e (app k j f a)).cls _ = r + 1
    rw [Ctx.cls_shift_insert]; exact hc
  | letE j A v b, e', Γ, Δ, r, hc => by
    show (Term.shift p e (letE j A v b)).cls _ = r + 1
    rw [Ctx.cls_shift_insert]; exact hc
  | prim c args, e', Γ, Δ, r, hc => by
    show (Term.shift p e (prim c args)).cls _ = r + 1
    rw [Ctx.cls_shift_insert]; exact hc

theorem Ctx.snoc_eq_insert {m : ℕ} (Γ : Ctx m) (B : Term) (l : ℕ) :
    Γ.snoc B l = Ctx.insert m 1 (e' := 0) Γ (fun _ => (B, l)) := by
  funext x
  refine Fin.lastCases ?_ (fun x => ?_) x
  · rw [Ctx.snoc, Fin.snoc_last, Ctx.insert_mid _ _ _ (by simp) (by simp)]
  · rw [Ctx.snoc, Fin.snoc_castSucc, Ctx.insert_lt _ _ _ (by simp)]
    exact congrArg Γ (Fin.ext rfl)

theorem TyOk.shift1 {m : ℕ} {Γ : Ctx m} {t : Term} {r : ℕ} (h : TyOk Γ t r) (B : Term) (l : ℕ) :
    TyOk (Γ.snoc B l) (Term.shift m 1 t) r := by
  rw [Ctx.snoc_eq_insert]
  exact TyOk.shift m 1 t (e' := 0) Γ _ r h

theorem PiParts.shift1 {m : ℕ} {Γ : Ctx m} {t : Term} (h : PiParts Γ t) (B : Term) (l : ℕ) :
    PiParts (Γ.snoc B l) (Term.shift m 1 t) := by
  intro k i j A' B' ht
  cases t with
  | pi k' i' j' A₀ B₀ =>
    simp only [Term.shift, Term.pi.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨hA, hB⟩ := h k' i' j' A₀ B₀ rfl
    refine ⟨hA.shift1 B l, ?_⟩
    rw [Ctx.snoc_eq_insert Γ B l, Ctx.insert_snoc]
    exact TyOk.shift m 1 B₀ (e' := 1) (Γ.snoc A₀ i') _ _ hB
  | var x => simp [Term.shift] at ht; split at ht <;> cases ht
  | univ n => cases ht
  | lam _ _ _ _ _ => cases ht
  | app _ _ _ _ => cases ht
  | letE _ _ _ _ => cases ht
  | prim _ _ => cases ht

/-! ### Substitution -/

/-- The context data of a substitution (cf. `SubOk`, without the environment). -/
structure SubCtx (p : ℕ) (s : Term) (Γ₀ : Ctx p) {d : ℕ} (Γ : Ctx (p + 1 + d)) : Prop where
  ctx : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l
  lev : Γ.lev p = s.cls Γ₀

theorem SubCtx.snoc {p : ℕ} {s : Term} {Γ₀ : Ctx p} {d : ℕ} {Γ : Ctx (p + 1 + d)}
    (h : SubCtx p s Γ₀ Γ) (A : Term) (i : ℕ) : SubCtx p s Γ₀ (d := d + 1) (Γ.snoc A i) where
  ctx l := by
    rw [Ctx.snoc, show (⟨l.1, by omega⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨l.1, by omega⟩ from
      Fin.ext rfl, Fin.snoc_castSucc]
    exact h.ctx l
  lev := by rw [Γ.lev_snoc_lt A i (by omega)]; exact h.lev

theorem Ctx.cls_subst_sub' {p d : ℕ} {s : Term} {Γ₀ : Ctx p} {Γ : Ctx (p + 1 + d)}
    (h : SubCtx p s Γ₀ Γ) (t : Term) : (Term.subst p s d t).cls (Γ.sub p s) = t.cls Γ :=
  Term.cls_subst Γ (Γ.sub p s) p d s (fun _ hx => Ctx.lev_sub_lt s Γ hx)
    (by
      rw [Term.cls_shift Γ₀ (Γ.sub p s) p d (fun x hx => ?_) (fun x hx => ?_) s, h.lev]
      · simp only [Ctx.lev]
        rw [dif_pos (by omega), dif_pos hx, Ctx.sub_lt _ _ _ hx, h.ctx ⟨x, hx⟩]
      · rw [Γ₀.lev_of_ge hx, (Γ.sub p s).lev_of_ge (by omega)])
    (fun _ hx => Ctx.lev_sub_gt s Γ hx) t

theorem Ctx.sub_eq_insert' {p d : ℕ} {s : Term} {Γ₀ : Ctx p} {Γ : Ctx (p + 1 + d)}
    (h : SubCtx p s Γ₀ Γ) :
    Γ.sub p s = Ctx.insert p d (e' := 0) Γ₀ (fun i => Γ.sub p s ⟨p + i.1, by omega⟩) := by
  funext l
  by_cases hl : l.1 < p
  · rw [Ctx.sub_lt _ _ _ hl, Ctx.insert_lt _ _ _ hl]
    exact h.ctx ⟨l.1, hl⟩
  · rw [Ctx.insert_mid _ _ _ hl (by omega)]
    congr 1
    exact Fin.ext (by simp; omega)

theorem TyOk.subst (p : ℕ) (s : Term) (Γ₀ : Ctx p) (hs : PiParts Γ₀ s) :
    ∀ (t : Term) {d : ℕ} (Γ : Ctx (p + 1 + d)) (h : SubCtx p s Γ₀ Γ) (r : ℕ),
      TyOk Γ t r → TyOk (Γ.sub p s) (Term.subst p s d t) r
  | pi k i j A B, d, Γ, h, r, ⟨hc, hA, hB⟩ => by
    refine ⟨?_, TyOk.subst p s Γ₀ hs A Γ h i hA, ?_⟩
    · show (Term.subst p s d (pi k i j A B)).cls _ = r + 1
      rw [Ctx.cls_subst_sub' h]; exact hc
    · rw [Ctx.sub_snoc]
      exact TyOk.subst p s Γ₀ hs B (d := d + 1) (Γ.snoc A i) (h.snoc A i) _ hB
  | var x, d, Γ, h, r, hc => by
    have hc' : Γ.lev x = r + 1 := hc
    show TyOk (Γ.sub p s) (if x < p then var x else if x = p then Term.shift p d s else var (x - 1)) r
    by_cases h1 : x < p
    · rw [if_pos h1]
      show (Γ.sub p s).lev x = r + 1
      rw [Ctx.lev_sub_lt _ _ h1]; exact hc'
    · rw [if_neg h1]
      by_cases h2 : x = p
      · rw [if_pos h2]
        subst h2
        refine TyOk.of_cls ?_ ?_
        · have := Ctx.cls_subst_sub' h (var x)
          simp only [Term.subst, if_neg h1, if_pos rfl, ite_true] at this
          rw [this]; exact hc'
        · rw [Ctx.sub_eq_insert' h]
          intro k i j A B ht
          cases s with
          | pi k' i' j' A₀ B₀ =>
            simp only [Term.shift, Term.pi.injEq] at ht
            obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ht
            obtain ⟨hA, hB⟩ := hs k' i' j' A₀ B₀ rfl
            refine ⟨TyOk.shift x d A₀ (e' := 0) Γ₀ _ i' hA, ?_⟩
            rw [Ctx.insert_snoc]
            exact TyOk.shift x d B₀ (e' := 1) (Γ₀.snoc A₀ i') _ _ hB
          | var y => simp [Term.shift] at ht; split at ht <;> cases ht
          | univ n => cases ht
          | lam _ _ _ _ _ => cases ht
          | app _ _ _ _ => cases ht
          | letE _ _ _ _ => cases ht
          | prim _ _ => cases ht
      · rw [if_neg h2]
        show (Γ.sub p s).lev (x - 1) = r + 1
        rw [Ctx.lev_sub_gt s Γ (by omega : p < x)]; exact hc'
  | Term.univ n, d, Γ, h, r, hc => hc
  | lam k i j A b, d, Γ, h, r, hc => by
    show (Term.subst p s d (lam k i j A b)).cls _ = r + 1
    rw [Ctx.cls_subst_sub' h]; exact hc
  | app k j f a, d, Γ, h, r, hc => by
    show (Term.subst p s d (app k j f a)).cls _ = r + 1
    rw [Ctx.cls_subst_sub' h]; exact hc
  | letE j A v b, d, Γ, h, r, hc => by
    show (Term.subst p s d (letE j A v b)).cls _ = r + 1
    rw [Ctx.cls_subst_sub' h]; exact hc
  | prim c args, d, Γ, h, r, hc => by
    show (Term.subst p s d (prim c args)).cls _ = r + 1
    rw [Ctx.cls_subst_sub' h]; exact hc

theorem SubCtx.zero {m : ℕ} (Γ : Ctx m) (A : Term) (i : ℕ) {s : Term} (hi : s.cls Γ = i) :
    SubCtx m s Γ (d := 0) (Γ.snoc A i) where
  ctx l := by
    rw [Ctx.snoc, show (⟨l.1, by omega⟩ : Fin (m + 1 + 0)) = Fin.castSucc l from Fin.ext rfl,
      Fin.snoc_castSucc]
  lev := by rw [Γ.lev_snoc_self, hi]

theorem Ctx.sub_snoc_zero {m : ℕ} (Γ : Ctx m) (A : Term) (i : ℕ) (s : Term) :
    Ctx.sub m s (d := 0) (Γ.snoc A i) = Γ := by
  funext l
  rw [Ctx.sub_lt _ _ _ l.2, Ctx.snoc,
    show (⟨l.1, by omega⟩ : Fin (m + 1 + 0)) = Fin.castSucc l from Fin.ext rfl, Fin.snoc_castSucc]

theorem TyOk.subst0 {m : ℕ} {Γ : Ctx m} {A : Term} {i : ℕ} {s : Term} (hs : PiParts Γ s)
    (hi : s.cls Γ = i) {B : Term} {j : ℕ} (hB : TyOk (Γ.snoc A i) B j) :
    TyOk Γ (Term.subst m s 0 B) j := by
  have := TyOk.subst m s Γ hs B (d := 0) (Γ.snoc A i) (SubCtx.zero Γ A i hi) j hB
  rwa [Ctx.sub_snoc_zero] at this

theorem PiParts.subst0 {m : ℕ} {Γ : Ctx m} {A : Term} {i : ℕ} {s : Term} (hs : PiParts Γ s)
    (hi : s.cls Γ = i) {b : Term} (hb : PiParts (Γ.snoc A i) b) :
    PiParts Γ (Term.subst m s 0 b) := by
  intro k i' j' A' B' ht
  cases b with
  | pi k₀ i₀ j₀ A₀ B₀ =>
    simp only [Term.subst, Term.pi.injEq] at ht
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := ht
    obtain ⟨hA, hB⟩ := hb k₀ i₀ j₀ A₀ B₀ rfl
    refine ⟨TyOk.subst0 hs hi hA, ?_⟩
    have := TyOk.subst m s Γ hs B₀ (d := 0 + 1) ((Γ.snoc A i).snoc A₀ i₀)
      ((SubCtx.zero Γ A i hi).snoc A₀ i₀) _ hB
    have e := (Ctx.sub_snoc (d := 0) s (Γ.snoc A i) A₀ i₀).symm
    rw [e, Ctx.sub_snoc_zero] at this
    exact this
  | var y =>
    simp only [Term.subst] at ht
    split at ht
    · cases ht
    · split at ht
      · rw [Term.shift_zero] at ht
        subst ht
        exact hs k i' j' A' B' rfl
      · cases ht
  | univ n => cases ht
  | lam _ _ _ _ _ => cases ht
  | app _ _ _ _ => cases ht
  | letE _ _ _ _ => cases ht
  | prim _ _ => cases ht

/-! ### The invariant -/

theorem Term.shift_shift (x m : ℕ) (hx : x ≤ m) :
    ∀ t : Term, Term.shift m 1 (Term.shift x (m - x) t) = Term.shift x (m + 1 - x) t
  | var y => by
    by_cases h : y < x
    · simp only [Term.shift, if_pos h, if_pos (show y < m by omega)]
    · simp only [Term.shift, if_neg h, if_neg (show ¬ y + (m - x) < m by omega)]
      congr 1; omega
  | univ n => rfl
  | pi k i j A B => by simp only [Term.shift, Term.shift_shift x m hx A, Term.shift_shift x m hx B]
  | lam k i j A b => by simp only [Term.shift, Term.shift_shift x m hx A, Term.shift_shift x m hx b]
  | app k j f a => by simp only [Term.shift, Term.shift_shift x m hx f, Term.shift_shift x m hx a]
  | letE j A v b => by
    simp only [Term.shift, Term.shift_shift x m hx A, Term.shift_shift x m hx v,
      Term.shift_shift x m hx b]
  | prim c args => by
    show prim c (fun k => Term.shift m 1 (Term.shift x (m - x) (args k))) =
      prim c (fun k => Term.shift x (m + 1 - x) (args k))
    congr 1
    funext k
    exact Term.shift_shift x m hx (args k)

mutual

theorem tyOk_of_ctxOk {m : ℕ} {Γ : Ctx m} :
    CtxOk Γ → ∀ x : Fin m, TyOk Γ (Term.shift x (m - x) (Γ x).1) (Γ x).2
  | .nil _ => fun x => x.elim0
  | @CtxOk.snoc m Γ A i hΓ hA => fun x => by
    refine Fin.lastCases ?_ (fun x => ?_) x
    · rw [show (Γ.snoc A i) (Fin.last m) = (A, i) from by simp [Ctx.snoc]]
      simp only [Fin.val_last, Nat.add_sub_cancel_left]
      exact (TyOk.of_cls (cls_of_typed hA) (tyOk_of_typed hA).2).shift1 A i
    · rw [show (Γ.snoc A i) (Fin.castSucc x) = Γ x from by simp [Ctx.snoc]]
      simp only [Fin.coe_castSucc]
      rw [← Term.shift_shift x m (by omega)]
      exact (tyOk_of_ctxOk hΓ x).shift1 A i

theorem tyOk_of_typed {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} :
    Typed Γ t A r → TyOk Γ A r ∧ PiParts Γ t
  | @Typed.var m Γ x hΓ => ⟨tyOk_of_ctxOk hΓ x, PiParts.var Γ x⟩
  | .univ n _ => ⟨TyOk.univ Γ (n + 1), PiParts.univ Γ n⟩
  | .piData _ hA hB =>
    ⟨TyOk.univ Γ _, PiParts.pi (TyOk.of_cls (cls_of_typed hA) (tyOk_of_typed hA).2)
      (TyOk.of_cls (cls_of_typed hB) (tyOk_of_typed hB).2)⟩
  | .piProp hA hB =>
    ⟨TyOk.univ Γ 0, PiParts.pi (TyOk.of_cls (cls_of_typed hA) (tyOk_of_typed hA).2)
      (TyOk.of_cls (cls_of_typed hB) (tyOk_of_typed hB).2)⟩
  | .lamData _ hA hb =>
    ⟨TyOk.pi_data (TyOk.of_cls (cls_of_typed hA) (tyOk_of_typed hA).2) (tyOk_of_typed hb).1,
     PiParts.lam Γ _ _ _ _ _⟩
  | .lamProp hA hb =>
    ⟨TyOk.pi_prop (TyOk.of_cls (cls_of_typed hA) (tyOk_of_typed hA).2) (tyOk_of_typed hb).1,
     PiParts.lam Γ _ _ _ _ _⟩
  | .appData _ hf ha =>
    ⟨TyOk.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hf).1.2.2,
     PiParts.app Γ _ _ _ _⟩
  | .appProp hf ha =>
    ⟨TyOk.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hf).1.2.2,
     PiParts.app Γ _ _ _ _⟩
  | .letE hv hb =>
    ⟨TyOk.subst0 (tyOk_of_typed hv).2 (cls_of_typed hv) (tyOk_of_typed hb).1,
     PiParts.letE Γ _ _ _ _⟩
  | .weak ht _ => ⟨(tyOk_of_typed ht).1.shift1 _ _, (tyOk_of_typed ht).2.shift1 _ _⟩
  | .conv ht hAB =>
    ⟨TyOk.of_cls (cls_of_defEq hAB).2 (tyOk_of_defEq hAB).2.2, (tyOk_of_typed ht).2⟩
  | .prim c args _ h =>
    ⟨Prim.resultTyOk c (fun k => cls_of_typed (h k)) (fun k => (tyOk_of_typed (h k)).2),
     PiParts.prim Γ c args⟩

theorem tyOk_of_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} :
    DefEq Γ t s A r → TyOk Γ A r ∧ PiParts Γ t ∧ PiParts Γ s
  | .refl ht => ⟨(tyOk_of_typed ht).1, (tyOk_of_typed ht).2, (tyOk_of_typed ht).2⟩
  | .symm h => ⟨(tyOk_of_defEq h).1, (tyOk_of_defEq h).2.2, (tyOk_of_defEq h).2.1⟩
  | .trans h h' => ⟨(tyOk_of_defEq h).1, (tyOk_of_defEq h).2.1, (tyOk_of_defEq h').2.2⟩
  | .conv h hAB =>
    ⟨TyOk.of_cls (cls_of_defEq hAB).2 (tyOk_of_defEq hAB).2.2, (tyOk_of_defEq h).2.1,
     (tyOk_of_defEq h).2.2⟩
  | .betaData _ _ hb ha =>
    ⟨TyOk.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hb).1, PiParts.app Γ _ _ _ _,
     PiParts.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hb).2⟩
  | .betaProp _ hb ha =>
    ⟨TyOk.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hb).1, PiParts.app Γ _ _ _ _,
     PiParts.subst0 (tyOk_of_typed ha).2 (cls_of_typed ha) (tyOk_of_typed hb).2⟩
  | .zeta hv hb =>
    ⟨TyOk.subst0 (tyOk_of_typed hv).2 (cls_of_typed hv) (tyOk_of_typed hb).1, PiParts.letE Γ _ _ _ _,
     PiParts.subst0 (tyOk_of_typed hv).2 (cls_of_typed hv) (tyOk_of_typed hb).2⟩
  | .eta _ hf => ⟨(tyOk_of_typed hf).1, PiParts.lam Γ _ _ _ _ _, (tyOk_of_typed hf).2⟩
  | .proofIrrel hh hh' => ⟨(tyOk_of_typed hh).1, (tyOk_of_typed hh).2, (tyOk_of_typed hh').2⟩
  | @DefEq.congrPiData m Γ i j A A' B B' _ hA hB =>
    ⟨TyOk.univ Γ _,
     PiParts.pi (TyOk.of_cls (cls_of_defEq hA).1 (tyOk_of_defEq hA).2.1)
       (TyOk.of_cls (cls_of_defEq hB).1 (tyOk_of_defEq hB).2.1),
     PiParts.pi (TyOk.of_cls (cls_of_defEq hA).2 (tyOk_of_defEq hA).2.2)
       (TyOk.congr_levels (by rw [Ctx.levels_snoc, Ctx.levels_snoc]) _ _
         (TyOk.of_cls (cls_of_defEq hB).2 (tyOk_of_defEq hB).2.2))⟩
  | @DefEq.congrPiProp m Γ i A A' B B' hA hB =>
    ⟨TyOk.univ Γ 0,
     PiParts.pi (TyOk.of_cls (cls_of_defEq hA).1 (tyOk_of_defEq hA).2.1)
       (TyOk.of_cls (cls_of_defEq hB).1 (tyOk_of_defEq hB).2.1),
     PiParts.pi (TyOk.of_cls (cls_of_defEq hA).2 (tyOk_of_defEq hA).2.2)
       (TyOk.congr_levels (by rw [Ctx.levels_snoc, Ctx.levels_snoc]) _ _
         (TyOk.of_cls (cls_of_defEq hB).2 (tyOk_of_defEq hB).2.2))⟩
  | .congrLamData _ hA hb =>
    ⟨TyOk.pi_data (TyOk.of_cls (cls_of_defEq hA).1 (tyOk_of_defEq hA).2.1) (tyOk_of_defEq hb).1,
     PiParts.lam Γ _ _ _ _ _, PiParts.lam Γ _ _ _ _ _⟩
  | .congrLamProp hA hb =>
    ⟨TyOk.pi_prop (TyOk.of_cls (cls_of_defEq hA).1 (tyOk_of_defEq hA).2.1) (tyOk_of_defEq hb).1,
     PiParts.lam Γ _ _ _ _ _, PiParts.lam Γ _ _ _ _ _⟩
  | .congrAppData _ hf ha =>
    ⟨TyOk.subst0 (tyOk_of_defEq ha).2.1 (cls_of_defEq ha).1 (tyOk_of_defEq hf).1.2.2,
     PiParts.app Γ _ _ _ _, PiParts.app Γ _ _ _ _⟩
  | .congrAppProp hf ha =>
    ⟨TyOk.subst0 (tyOk_of_defEq ha).2.1 (cls_of_defEq ha).1 (tyOk_of_defEq hf).1.2.2,
     PiParts.app Γ _ _ _ _, PiParts.app Γ _ _ _ _⟩
  | .congrLet hv hb =>
    ⟨TyOk.subst0 (tyOk_of_defEq hv).2.1 (cls_of_defEq hv).1 (tyOk_of_defEq hb).1,
     PiParts.letE Γ _ _ _ _, PiParts.letE Γ _ _ _ _⟩
  | .weak h _ =>
    ⟨(tyOk_of_defEq h).1.shift1 _ _, (tyOk_of_defEq h).2.1.shift1 _ _,
     (tyOk_of_defEq h).2.2.shift1 _ _⟩
  | .congrPrim c args args' _ h =>
    ⟨Prim.resultTyOk c (fun k => (cls_of_defEq (h k)).1) (fun k => (tyOk_of_defEq (h k)).2.1),
     PiParts.prim Γ c args, PiParts.prim Γ c args'⟩
  | .eqRecRefl h =>
    ⟨Prim.resultTyOk _ (fun k => cls_of_typed (h k)) (fun k => (tyOk_of_typed (h k)).2),
     PiParts.prim Γ _ _, (tyOk_of_typed (h 3)).2⟩
  | .sigmaFst _ h =>
    ⟨TyOk.of_cls (cls_of_typed (h 0)) (tyOk_of_typed (h 0)).2, PiParts.prim Γ _ _,
     (tyOk_of_typed (h 2)).2⟩
  | .sigmaSnd _ h => ⟨rfl, PiParts.prim Γ _ _, (tyOk_of_typed (h 3)).2⟩
  | .sigmaEta _ h => ⟨rfl, PiParts.prim Γ _ _, (tyOk_of_typed (h 2)).2⟩
  | .downUp h =>
    ⟨TyOk.of_cls (cls_of_typed (h 0)) (tyOk_of_typed (h 0)).2, PiParts.prim Γ _ _,
     (tyOk_of_typed (h 1)).2⟩
  | .upDown h => ⟨rfl, PiParts.prim Γ _ _, (tyOk_of_typed (h 1)).2⟩
  | .sumRecInl _ _ _ => ⟨rfl, PiParts.prim Γ _ _, PiParts.app Γ _ _ _ _⟩
  | .sumRecInr _ _ _ => ⟨rfl, PiParts.prim Γ _ _, PiParts.app Γ _ _ _ _⟩
  | .natRecZero _ h => ⟨rfl, PiParts.prim Γ _ _, (tyOk_of_typed (h 1)).2⟩
  | .natRecSucc _ _ _ => ⟨rfl, PiParts.prim Γ _ _, PiParts.app Γ _ _ _ _⟩
  | .quotLiftMk _ _ h _ =>
    ⟨TyOk.of_cls (cls_of_typed (h 2)) (tyOk_of_typed (h 2)).2, PiParts.prim Γ _ _,
     PiParts.app Γ _ _ _ _⟩

end

end SolidLean.Calc
