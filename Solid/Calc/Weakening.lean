import Solid.Calc.Envs
import Solid.Calc.PrimSemantics

/-!
# Semantic weakening: values are stable under insertion of binders

`Val_shift`: the value of `shift p e t` in the context with `e` binders
inserted at position `p` (at values `ξ`) is the value of `t` in the
original context.  By structural induction on `t`, generalizing over the
tail of the context (the binders crossed).
-/

universe u

namespace SolidLean.Calc

open SolidLean.Solid Term

variable (T : MemTower.{u})

/-! ### Congruences for the readings -/

theorem IsTV_congr (n : ℕ) {ψ ψ' : Prop} (h : ψ ↔ ψ') (w : T.U n) : IsTV T n ψ w ↔ IsTV T n ψ' w := by
  unfold IsTV; rw [h]

theorem IsPiFun_congr {m m' : ℕ} {Γ : Ctx m} {Γ' : Ctx m'} {i j : ℕ} {A B A' B' : Term}
    {η : Env T m} {η' : Env T m'} (vA : T.U (i + 1)) (f : T.U (max i j))
    (h : ∀ (a : T.U i) (vB : T.U (j + 1)),
      Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ↔
      Val T (Γ'.snoc A' i) B' (Fin.snoc η' (T.inj a)) (T.inj vB)) :
    IsPiFun T Γ i j A B η vA f ↔ IsPiFun T Γ' i j A' B' η' vA f := by
  unfold IsPiFun
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  refine forall_congr' fun a => imp_congr Iff.rfl (forall_congr' fun v => imp_congr Iff.rfl ?_)
  exact exists_congr fun vB => and_congr (h a vB) Iff.rfl

theorem FamOk_congr {m m' : ℕ} {Γ : Ctx m} {Γ' : Ctx m'} {i j : ℕ} {A B A' B' : Term}
    {η : Env T m} {η' : Env T m'}
    (hA : ∀ vA : T.U (i + 1), Val T Γ' A' η' (T.inj vA) ↔ Val T Γ A η (T.inj vA))
    (hB : ∀ (a : T.U i) (vB : T.U (j + 1)),
      Val T (Γ'.snoc A' i) B' (Fin.snoc η' (T.inj a)) (T.inj vB) ↔
      Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB)) :
    FamOk T Γ' i j A' B' η' ↔ FamOk T Γ i j A B η := by
  unfold FamOk
  exact exists_congr fun vA => and_congr (hA vA) (and_congr
    (forall_congr' fun vA' => imp_congr (hA vA') Iff.rfl)
    (forall_congr' fun a => imp_congr Iff.rfl (exists_congr fun vB => and_congr (hB a vB)
      (and_congr (forall_congr' fun vB' => imp_congr (hB a vB') Iff.rfl) Iff.rfl))))

/-- A value relation forces the sort of the value. -/
theorem Val_sort_iff {m m' : ℕ} (Γ : Ctx m) (Γ' : Ctx m') (t t' : Term) (η : Env T m) (η' : Env T m')
    (w : T.El) (hc : t'.cls Γ' = t.cls Γ)
    (h : ∀ w' : T.U (t.cls Γ), Val T Γ' t' η' (T.inj w') ↔ Val T Γ t η (T.inj w')) :
    Val T Γ' t' η' w ↔ Val T Γ t η w := by
  by_cases hw : w.1 = t.cls Γ
  · obtain ⟨w', rfl⟩ := elSort T w hw
    exact h w'
  · constructor
    · intro hv; exact absurd (hc ▸ hv.sort) hw
    · intro hv; exact absurd hv.sort hw

/-- `Val_app_data` with the classifiers of `f` and `a` generalized. -/
theorem Val_app_data' {m : ℕ} {Γ : Ctx m} {j : ℕ} {f a : Term} {n k : ℕ} (hf : f.cls Γ = n)
    (hak : a.cls Γ = k) (hj : j ≤ n) (ha : k ≤ n) (η : Env T m) (w : T.U j) :
    Val T Γ (.app .data j f a) η (T.inj w) ↔
      ∃ (vf : T.U n) (va : T.U k), Val T Γ f η (T.inj vf) ∧ Val T Γ a η (T.inj va) ∧
        (T.sortStr n).FunApp vf (T.liftLE ha va) (T.liftLE hj w) := by
  subst hf; subst hak; exact Val_app_data T hj ha η w

/-! ### Weakening -/

theorem Val_shift (p e : ℕ) : ∀ (t : Term) {e' : ℕ} (Γ : Ctx (p + e')) (Δ : Fin e → Term × ℕ)
    (η : Env T (p + e')) (ξ : Fin e → T.El) (w : T.El),
    Val T (Γ.insert p e Δ) (shift p e t) (Env.insert T p e η ξ) w ↔ Val T Γ t η w
  | var x, e', Γ, Δ, η, ξ, w => by
    show Val T _ (if x < p then var x else var (x + e)) _ w ↔ _
    rw [Val_var']
    by_cases h : x < p
    · rw [if_pos h, Val_var']
      constructor
      · rintro ⟨h1, hw, hs⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.insert_lt _ _ _ _ h]
        · rw [hs, Ctx.lev_insert_lt _ _ h]
      · rintro ⟨h1, hw, hs⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.insert_lt _ _ _ _ h]
        · rw [hs, Ctx.lev_insert_lt _ _ h]
    · rw [if_neg h, Val_var']
      have h' : p ≤ x := Nat.le_of_not_lt h
      constructor
      · rintro ⟨h1, hw, hs⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.insert_ge _ _ _ _ (by simp; omega)]
          congr 1; exact Fin.ext (by simp)
        · rw [hs, Ctx.lev_insert_ge _ _ h']
      · rintro ⟨h1, hw, hs⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.insert_ge _ _ _ _ (by simp; omega)]
          congr 1; exact Fin.ext (by simp)
        · rw [hs, Ctx.lev_insert_ge _ _ h']
  | univ n, e', Γ, Δ, η, ξ, w => by
    show Val T _ (univ n) _ w ↔ _
    refine Val_sort_iff T Γ _ (univ n) (univ n) η _ w rfl (fun w' => ?_)
    cases n with
    | zero => rw [Val_univ_zero, Val_univ_zero]
    | succ n => rw [Val_univ_succ, Val_univ_succ]
  | pi .prop i j A B, e', Γ, Δ, η, ξ, w => by
    show Val T _ (pi .prop i j (shift p e A) (shift p e B)) _ w ↔ _
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' : (shift p e A).cls (Γ.insert p e Δ) = i + 1 := by rw [Ctx.cls_shift_insert]; exact hA
      have hB' : (shift p e B).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = 1 := by
        rw [Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hB
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_pi_prop T hA' hB', Val_pi_prop T hA hB]
      have hBw : ∀ (a : T.U i) (vB : T.U (0 + 1)),
          Val T ((Γ.insert p e Δ).snoc (shift p e A) i) (shift p e B)
            (Fin.snoc (Env.insert T p e η ξ) (T.inj a)) (T.inj vB) ↔
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) := by
        intro a vB
        rw [Ctx.insert_snoc, Env.insert_snoc]
        exact Val_shift p e B (e' := e' + 1) (Γ.snoc A i) Δ (Fin.snoc (α := fun _ => T.El) η (T.inj a)) ξ _
      refine and_congr (FamOk_congr T (fun vA => Val_shift p e A Γ Δ η ξ _) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_shift p e A Γ Δ η ξ _) ?_
      exact IsTV_congr T 1 (forall_congr' fun a => imp_congr Iff.rfl (exists_congr fun vB =>
        and_congr (hBw a vB) Iff.rfl)) w'
    · have hg' : ¬ ((shift p e A).cls (Γ.insert p e Δ) = i + 1 ∧
          (shift p e B).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = 1) := by
        rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_pi_prop T _ _ _ _ _ _ _ hg') (not_Val_pi_prop T _ _ _ _ _ _ _ hg)
  | pi .data i j A B, e', Γ, Δ, η, ξ, w => by
    show Val T _ (pi .data i j (shift p e A) (shift p e B)) _ w ↔ _
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = j + 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' : (shift p e A).cls (Γ.insert p e Δ) = i + 1 := by rw [Ctx.cls_shift_insert]; exact hA
      have hB' : (shift p e B).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = j + 1 := by
        rw [Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hB
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_pi_data T hA' hB', Val_pi_data T hA hB]
      have hBw : ∀ (a : T.U i) (vB : T.U (j + 1)),
          Val T ((Γ.insert p e Δ).snoc (shift p e A) i) (shift p e B)
            (Fin.snoc (Env.insert T p e η ξ) (T.inj a)) (T.inj vB) ↔
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) := by
        intro a vB
        rw [Ctx.insert_snoc, Env.insert_snoc]
        exact Val_shift p e B (e' := e' + 1) (Γ.snoc A i) Δ (Fin.snoc (α := fun _ => T.El) η (T.inj a)) ξ _
      refine and_congr (FamOk_congr T (fun vA => Val_shift p e A Γ Δ η ξ _) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_shift p e A Γ Δ η ξ _) (exists_congr fun q =>
        and_congr Iff.rfl (forall_congr' fun f => iff_congr Iff.rfl ?_))
      exact IsPiFun_congr T vA f hBw
    · have hg' : ¬ ((shift p e A).cls (Γ.insert p e Δ) = i + 1 ∧
          (shift p e B).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = j + 1) := by
        rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_pi_data T _ _ _ _ _ _ _ hg') (not_Val_pi_data T _ _ _ _ _ _ _ hg)
  | lam .prop i j A b, e', Γ, Δ, η, ξ, w => by
    show Val T _ (lam .prop i j (shift p e A) (shift p e b)) _ w ↔ _
    refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
    rw [Val_lam_prop, Val_lam_prop]
  | lam .data i j A b, e', Γ, Δ, η, ξ, w => by
    show Val T _ (lam .data i j (shift p e A) (shift p e b)) _ w ↔ _
    by_cases hg : A.cls Γ = i + 1 ∧ b.cls (Γ.snoc A i) = j
    · obtain ⟨hA, hb⟩ := hg
      have hA' : (shift p e A).cls (Γ.insert p e Δ) = i + 1 := by rw [Ctx.cls_shift_insert]; exact hA
      have hb' : (shift p e b).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = j := by
        rw [Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hb
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_lam_data T hA' hb', Val_lam_data T hA hb]
      refine exists_congr fun vA => and_congr (Val_shift p e A Γ Δ η ξ _) (forall_congr' fun q =>
        iff_congr Iff.rfl (exists_congr fun a => and_congr Iff.rfl (exists_congr fun vb =>
          and_congr ?_ Iff.rfl)))
      rw [Ctx.insert_snoc, Env.insert_snoc]
      exact Val_shift p e b (e' := e' + 1) (Γ.snoc A i) Δ (Fin.snoc (α := fun _ => T.El) η (T.inj a)) ξ _
    · have hg' : ¬ ((shift p e A).cls (Γ.insert p e Δ) = i + 1 ∧
          (shift p e b).cls ((Γ.insert p e Δ).snoc (shift p e A) i) = j) := by
        rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_lam_data T _ _ _ _ _ _ _ hg') (not_Val_lam_data T _ _ _ _ _ _ _ hg)
  | app .prop j f a, e', Γ, Δ, η, ξ, w => by
    show Val T _ (app .prop j (shift p e f) (shift p e a)) _ w ↔ _
    refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
    rw [Val_app_prop, Val_app_prop]
  | app .data j f a, e', Γ, Δ, η, ξ, w => by
    show Val T _ (app .data j (shift p e f) (shift p e a)) _ w ↔ _
    by_cases hg : j ≤ f.cls Γ ∧ a.cls Γ ≤ f.cls Γ
    · obtain ⟨hj, ha⟩ := hg
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_app_data' T (Ctx.cls_shift_insert Γ Δ f) (Ctx.cls_shift_insert Γ Δ a) hj ha,
        Val_app_data' T rfl rfl hj ha]
      exact exists_congr fun vf => exists_congr fun va =>
        and_congr (Val_shift p e f Γ Δ η ξ _) (and_congr (Val_shift p e a Γ Δ η ξ _) Iff.rfl)
    · have hg' : ¬ (j ≤ (shift p e f).cls (Γ.insert p e Δ) ∧
          (shift p e a).cls (Γ.insert p e Δ) ≤ (shift p e f).cls (Γ.insert p e Δ)) := by
        rw [Ctx.cls_shift_insert, Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_app_data T _ _ _ _ _ _ hg') (not_Val_app_data T _ _ _ _ _ _ hg)
  | letE j A v b, e', Γ, Δ, η, ξ, w => by
    show Val T _ (letE j (shift p e A) (shift p e v) (shift p e b)) _ w ↔ _
    by_cases hg : b.cls (Γ.snoc A (v.cls Γ)) = j
    · have hg' : (shift p e b).cls ((Γ.insert p e Δ).snoc (shift p e A) ((shift p e v).cls (Γ.insert p e Δ))) = j := by
        rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hg
      rw [Val_let T hg', Val_let T hg]
      refine exists_congr fun vv => and_congr (Val_shift p e v Γ Δ η ξ _) ?_
      rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Env.insert_snoc]
      exact Val_shift p e b (e' := e' + 1) (Γ.snoc A (v.cls Γ)) Δ (Fin.snoc (α := fun _ => T.El) η vv) ξ w
    · have hg' : ¬ (shift p e b).cls ((Γ.insert p e Δ).snoc (shift p e A) ((shift p e v).cls (Γ.insert p e Δ))) = j := by
        rw [Ctx.cls_shift_insert, Ctx.insert_snoc, Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_let T _ _ _ _ _ _ _ hg') (not_Val_let T _ _ _ _ _ _ _ hg)
  | prim c args, e', Γ, Δ, η, ξ, w => by
    show Val T _ (prim c (fun k => shift p e (args k))) _ w ↔ _
    by_cases hg : ∀ k, (args k).cls Γ = c.argSort k
    · have hg' : ∀ k, (shift p e (args k)).cls (Γ.insert p e Δ) = c.argSort k := fun k => by
        rw [Ctx.cls_shift_insert]; exact hg k
      rw [Val_prim' T c _ hg', Val_prim' T c _ hg]
      exact and_congr Iff.rfl (exists_congr fun vs => and_congr
        (forall_congr' fun k => Val_shift p e (args k) Γ Δ η ξ (vs k)) Iff.rfl)
    · have hg' : ¬ ∀ k, (shift p e (args k)).cls (Γ.insert p e Δ) = c.argSort k := by
        simp only [Ctx.cls_shift_insert]; exact hg
      exact iff_of_false (not_Val_prim T _ _ _ _ _ hg') (not_Val_prim T _ _ _ _ _ hg)

end SolidLean.Calc
