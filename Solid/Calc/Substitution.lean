import Solid.Calc.Weakening

/-!
# Semantic substitution

`Val_subst`: if the term `s` has the unique value `vs` in the prefix context
`Γ₀` (environment `η₀`), then the value of `subst p s d t` in the context
with the variable `p` removed (and `s` substituted in the tail) is the
value of `t` in the original context, provided the environment assigns
`vs` to the variable `p`.  By structural induction on `t`, generalizing over
the tail of the context.
-/

universe u

namespace SolidLean.Calc

open SolidLean.Solid Term

variable (T : MemTower.{u})

/-- The data relating the original context/environment to the prefix in
which the substituted term lives. -/
structure SubOk (p : ℕ) (s : Term) (Γ₀ : Ctx p) (η₀ : Env T p) (vs : T.El) {d : ℕ}
    (Γ : Ctx (p + 1 + d)) (η : Env T (p + 1 + d)) : Prop where
  ctx : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l
  env : ∀ l : Fin p, η ⟨l.1, by omega⟩ = η₀ l
  val : η ⟨p, by omega⟩ = vs
  lev : Γ.lev p = s.cls Γ₀

namespace SubOk

variable {T}

theorem snoc {p : ℕ} {s : Term} {Γ₀ : Ctx p} {η₀ : Env T p} {vs : T.El} {d : ℕ}
    {Γ : Ctx (p + 1 + d)} {η : Env T (p + 1 + d)} (h : SubOk T p s Γ₀ η₀ vs Γ η)
    (A : Term) (i : ℕ) (x : T.El) :
    SubOk T p s Γ₀ η₀ vs (d := d + 1) (Γ.snoc A i) (Fin.snoc (α := fun _ => T.El) η x) where
  ctx l := by
    rw [Ctx.snoc, show (⟨l.1, by omega⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨l.1, by omega⟩ from
      Fin.ext rfl, Fin.snoc_castSucc]
    exact h.ctx l
  env l := by
    rw [show (⟨l.1, by omega⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨l.1, by omega⟩ from
      Fin.ext rfl, Fin.snoc_castSucc]
    exact h.env l
  val := by
    rw [show (⟨p, by omega⟩ : Fin (p + 1 + d + 1)) = Fin.castSucc ⟨p, by omega⟩ from
      Fin.ext rfl, Fin.snoc_castSucc]
    exact h.val
  lev := by rw [Γ.lev_snoc_lt A i (by omega)]; exact h.lev

end SubOk

namespace Ctx

/-- The substituted context is the prefix with the tail inserted. -/
theorem sub_eq_insert {p d : ℕ} (s : Term) (Γ : Ctx (p + 1 + d)) (Γ₀ : Ctx p)
    (hΓ : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l) :
    Γ.sub p s = Ctx.insert p d (e' := 0) Γ₀ (fun i => Γ.sub p s ⟨p + i.1, by omega⟩) := by
  funext l
  by_cases h : l.1 < p
  · rw [sub_lt _ _ _ h, insert_lt _ _ _ h]
    exact hΓ ⟨l.1, h⟩
  · rw [insert_mid _ _ _ h (by omega)]
    congr 1
    exact Fin.ext (by simp; omega)

theorem lev_sub_eq {p d : ℕ} (s : Term) (Γ : Ctx (p + 1 + d)) (Γ₀ : Ctx p)
    (hΓ : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l) {x : ℕ} (hx : x < p) :
    (Γ.sub p s).lev x = Γ₀.lev x := by
  simp only [lev]
  rw [dif_pos (by omega), dif_pos hx, sub_lt _ _ _ hx, hΓ ⟨x, hx⟩]

/-- The classifier of the shifted substituted term in the substituted context. -/
theorem cls_shift_sub {p d : ℕ} (s : Term) (Γ : Ctx (p + 1 + d)) (Γ₀ : Ctx p)
    (hΓ : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l) :
    (shift p d s).cls (Γ.sub p s) = s.cls Γ₀ :=
  Term.cls_shift Γ₀ (Γ.sub p s) p d (fun _ hx => lev_sub_eq s Γ Γ₀ hΓ hx)
    (fun x hx => by rw [Γ₀.lev_of_ge hx, (Γ.sub p s).lev_of_ge (by omega)]) s

/-- The classifier is invariant under substitution. -/
theorem cls_subst_sub {p d : ℕ} (s : Term) (Γ : Ctx (p + 1 + d)) (Γ₀ : Ctx p)
    (hΓ : ∀ l : Fin p, Γ ⟨l.1, by omega⟩ = Γ₀ l) (hp : Γ.lev p = s.cls Γ₀) (t : Term) :
    (Term.subst p s d t).cls (Γ.sub p s) = t.cls Γ :=
  Term.cls_subst Γ (Γ.sub p s) p d s (fun _ hx => lev_sub_lt s Γ hx)
    (by rw [cls_shift_sub s Γ Γ₀ hΓ, hp]) (fun _ hx => lev_sub_gt s Γ hx) t

end Ctx

namespace Env

theorem remove_eq_insert {p d : ℕ} (η : Env T (p + 1 + d)) (η₀ : Env T p)
    (hη : ∀ l : Fin p, η ⟨l.1, by omega⟩ = η₀ l) :
    Env.remove T p η = Env.insert T p d (e' := 0) η₀ (fun i => η ⟨p + 1 + i.1, by omega⟩) := by
  funext l
  by_cases h : l.1 < p
  · rw [remove_lt _ _ _ h, insert_lt _ _ _ _ h]
    exact hη ⟨l.1, h⟩
  · rw [remove_ge _ _ _ h, insert_mid _ _ _ _ h (by omega)]
    congr 1
    exact Fin.ext (by simp; omega)

end Env

/-! ### Substitution -/

theorem Val_subst (p : ℕ) (s : Term) (Γ₀ : Ctx p) (η₀ : Env T p) (vs : T.El)
    (hvs : ∀ w, Val T Γ₀ s η₀ w ↔ w = vs) :
    ∀ (t : Term) {d : ℕ} (Γ : Ctx (p + 1 + d)) (η : Env T (p + 1 + d)) (w : T.El)
      (hs : SubOk T p s Γ₀ η₀ vs Γ η),
      Val T (Γ.sub p s) (Term.subst p s d t) (Env.remove T p η) w ↔ Val T Γ t η w
  | var x, d, Γ, η, w, hs => by
    show Val T _ (if x < p then var x else if x = p then shift p d s else var (x - 1)) _ w ↔ _
    by_cases h : x < p
    · rw [if_pos h, Val_var', Val_var']
      constructor
      · rintro ⟨h1, hw, hl⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.remove_lt _ _ _ h]
        · rw [hl, Ctx.lev_sub_lt _ _ h]
      · rintro ⟨h1, hw, hl⟩
        refine ⟨by omega, ?_, ?_⟩
        · rw [hw, Env.remove_lt _ _ _ h]
        · rw [hl, Ctx.lev_sub_lt _ _ h]
    · rw [if_neg h]
      by_cases h' : x = p
      · rw [if_pos h', h', Ctx.sub_eq_insert s Γ Γ₀ hs.ctx, Env.remove_eq_insert T η η₀ hs.env,
          Val_shift T p d s, hvs, Val_var']
        constructor
        · intro hw
          refine ⟨by omega, by rw [hw, hs.val], ?_⟩
          rw [hw, hs.lev]
          exact ((hvs vs).2 rfl).sort
        · rintro ⟨_, hw, _⟩
          rw [hw, hs.val]
      · rw [if_neg h', Val_var', Val_var']
        have hx : p < x := by omega
        constructor
        · rintro ⟨h1, hw, hl⟩
          refine ⟨by omega, ?_, ?_⟩
          · rw [hw, Env.remove_ge _ _ _ (by simp; omega)]
            congr 1; exact Fin.ext (by simp; omega)
          · rw [hl, Ctx.lev_sub_gt _ _ hx]
        · rintro ⟨h1, hw, hl⟩
          refine ⟨by omega, ?_, ?_⟩
          · rw [hw, Env.remove_ge _ _ _ (by simp; omega)]
            congr 1; exact Fin.ext (by simp; omega)
          · rw [hl, Ctx.lev_sub_gt _ _ hx]
  | univ n, d, Γ, η, w, hs => by
    show Val T _ (univ n) _ w ↔ _
    refine Val_sort_iff T Γ _ (univ n) (univ n) η _ w rfl (fun w' => ?_)
    cases n with
    | zero => rw [Val_univ_zero, Val_univ_zero]
    | succ n => rw [Val_univ_succ, Val_univ_succ]
  | pi .prop i j A B, d, Γ, η, w, hs => by
    show Val T _ (pi .prop i j (Term.subst p s d A) (Term.subst p s (d + 1) B)) _ w ↔ _
    have hcA := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev A
    have hcB : (Term.subst p s (d + 1) B).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) =
        B.cls (Γ.snoc A i) := by
      rw [Ctx.sub_snoc]; exact Ctx.cls_subst_sub s _ Γ₀ (hs.snoc A i vs).ctx (hs.snoc A i vs).lev B
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' := hcA.trans hA
      have hB' := hcB.trans hB
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_pi_prop T hA' hB', Val_pi_prop T hA hB]
      have hBw : ∀ (a : T.U i) (vB : T.U (0 + 1)),
          Val T ((Γ.sub p s).snoc (Term.subst p s d A) i) (Term.subst p s (d + 1) B)
            (Fin.snoc (Env.remove T p η) (T.inj a)) (T.inj vB) ↔
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) := by
        intro a vB
        rw [Ctx.sub_snoc, Env.remove_snoc]
        exact Val_subst p s Γ₀ η₀ vs hvs B (d := d + 1) (Γ.snoc A i)
          (Fin.snoc (α := fun _ => T.El) η (T.inj a)) _ (hs.snoc A i _)
      refine and_congr (FamOk_congr T (fun vA => Val_subst p s Γ₀ η₀ vs hvs A Γ η _ hs) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_subst p s Γ₀ η₀ vs hvs A Γ η _ hs) ?_
      exact IsTV_congr T 1 (forall_congr' fun a => imp_congr Iff.rfl (exists_congr fun vB =>
        and_congr (hBw a vB) Iff.rfl)) w'
    · have hg' : ¬ ((Term.subst p s d A).cls (Γ.sub p s) = i + 1 ∧
          (Term.subst p s (d + 1) B).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) = 1) := by
        rw [hcA, hcB]; exact hg
      exact iff_of_false (not_Val_pi_prop T _ _ _ _ _ _ _ hg') (not_Val_pi_prop T _ _ _ _ _ _ _ hg)
  | pi .data i j A B, d, Γ, η, w, hs => by
    show Val T _ (pi .data i j (Term.subst p s d A) (Term.subst p s (d + 1) B)) _ w ↔ _
    have hcA := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev A
    have hcB : (Term.subst p s (d + 1) B).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) =
        B.cls (Γ.snoc A i) := by
      rw [Ctx.sub_snoc]; exact Ctx.cls_subst_sub s _ Γ₀ (hs.snoc A i vs).ctx (hs.snoc A i vs).lev B
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = j + 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' := hcA.trans hA
      have hB' := hcB.trans hB
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_pi_data T hA' hB', Val_pi_data T hA hB]
      have hBw : ∀ (a : T.U i) (vB : T.U (j + 1)),
          Val T ((Γ.sub p s).snoc (Term.subst p s d A) i) (Term.subst p s (d + 1) B)
            (Fin.snoc (Env.remove T p η) (T.inj a)) (T.inj vB) ↔
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) := by
        intro a vB
        rw [Ctx.sub_snoc, Env.remove_snoc]
        exact Val_subst p s Γ₀ η₀ vs hvs B (d := d + 1) (Γ.snoc A i)
          (Fin.snoc (α := fun _ => T.El) η (T.inj a)) _ (hs.snoc A i _)
      refine and_congr (FamOk_congr T (fun vA => Val_subst p s Γ₀ η₀ vs hvs A Γ η _ hs) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_subst p s Γ₀ η₀ vs hvs A Γ η _ hs)
        (exists_congr fun q => and_congr Iff.rfl (forall_congr' fun f => iff_congr Iff.rfl ?_))
      exact IsPiFun_congr T vA f hBw
    · have hg' : ¬ ((Term.subst p s d A).cls (Γ.sub p s) = i + 1 ∧
          (Term.subst p s (d + 1) B).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) = j + 1) := by
        rw [hcA, hcB]; exact hg
      exact iff_of_false (not_Val_pi_data T _ _ _ _ _ _ _ hg') (not_Val_pi_data T _ _ _ _ _ _ _ hg)
  | lam .prop i j A b, d, Γ, η, w, hs => by
    show Val T _ (lam .prop i j (Term.subst p s d A) (Term.subst p s (d + 1) b)) _ w ↔ _
    refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
    rw [Val_lam_prop, Val_lam_prop]
  | lam .data i j A b, d, Γ, η, w, hs => by
    show Val T _ (lam .data i j (Term.subst p s d A) (Term.subst p s (d + 1) b)) _ w ↔ _
    have hcA := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev A
    have hcb : (Term.subst p s (d + 1) b).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) =
        b.cls (Γ.snoc A i) := by
      rw [Ctx.sub_snoc]; exact Ctx.cls_subst_sub s _ Γ₀ (hs.snoc A i vs).ctx (hs.snoc A i vs).lev b
    by_cases hg : A.cls Γ = i + 1 ∧ b.cls (Γ.snoc A i) = j
    · obtain ⟨hA, hb⟩ := hg
      have hA' := hcA.trans hA
      have hb' := hcb.trans hb
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_lam_data T hA' hb', Val_lam_data T hA hb]
      refine exists_congr fun vA => and_congr (Val_subst p s Γ₀ η₀ vs hvs A Γ η _ hs)
        (forall_congr' fun q => iff_congr Iff.rfl (exists_congr fun a => and_congr Iff.rfl
          (exists_congr fun vb => and_congr ?_ Iff.rfl)))
      rw [Ctx.sub_snoc, Env.remove_snoc]
      exact Val_subst p s Γ₀ η₀ vs hvs b (d := d + 1) (Γ.snoc A i)
        (Fin.snoc (α := fun _ => T.El) η (T.inj a)) _ (hs.snoc A i _)
    · have hg' : ¬ ((Term.subst p s d A).cls (Γ.sub p s) = i + 1 ∧
          (Term.subst p s (d + 1) b).cls ((Γ.sub p s).snoc (Term.subst p s d A) i) = j) := by
        rw [hcA, hcb]; exact hg
      exact iff_of_false (not_Val_lam_data T _ _ _ _ _ _ _ hg') (not_Val_lam_data T _ _ _ _ _ _ _ hg)
  | app .prop j f a, d, Γ, η, w, hs => by
    show Val T _ (app .prop j (Term.subst p s d f) (Term.subst p s d a)) _ w ↔ _
    refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
    rw [Val_app_prop, Val_app_prop]
  | app .data j f a, d, Γ, η, w, hs => by
    show Val T _ (app .data j (Term.subst p s d f) (Term.subst p s d a)) _ w ↔ _
    have hcf := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev f
    have hca := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev a
    by_cases hg : j ≤ f.cls Γ ∧ a.cls Γ ≤ f.cls Γ
    · obtain ⟨hj, ha⟩ := hg
      refine Val_sort_iff T Γ _ _ _ η _ w rfl (fun w' => ?_)
      rw [Val_app_data' T hcf hca hj ha, Val_app_data' T rfl rfl hj ha]
      exact exists_congr fun vf => exists_congr fun va =>
        and_congr (Val_subst p s Γ₀ η₀ vs hvs f Γ η _ hs)
          (and_congr (Val_subst p s Γ₀ η₀ vs hvs a Γ η _ hs) Iff.rfl)
    · have hg' : ¬ (j ≤ (Term.subst p s d f).cls (Γ.sub p s) ∧
          (Term.subst p s d a).cls (Γ.sub p s) ≤ (Term.subst p s d f).cls (Γ.sub p s)) := by
        rw [hcf, hca]; exact hg
      exact iff_of_false (not_Val_app_data T _ _ _ _ _ _ hg') (not_Val_app_data T _ _ _ _ _ _ hg)
  | letE j A v b, d, Γ, η, w, hs => by
    show Val T _ (letE j (Term.subst p s d A) (Term.subst p s d v) (Term.subst p s (d + 1) b)) _ w ↔ _
    have hcv := Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev v
    have hcb : (Term.subst p s (d + 1) b).cls
        ((Γ.sub p s).snoc (Term.subst p s d A) ((Term.subst p s d v).cls (Γ.sub p s))) =
        b.cls (Γ.snoc A (v.cls Γ)) := by
      rw [hcv, Ctx.sub_snoc]
      exact Ctx.cls_subst_sub s _ Γ₀ (hs.snoc A (v.cls Γ) vs).ctx (hs.snoc A (v.cls Γ) vs).lev b
    by_cases hg : b.cls (Γ.snoc A (v.cls Γ)) = j
    · have hg' := hcb.trans hg
      rw [Val_let T hg', Val_let T hg]
      refine exists_congr fun vv => and_congr (Val_subst p s Γ₀ η₀ vs hvs v Γ η _ hs) ?_
      rw [hcv, Ctx.sub_snoc, Env.remove_snoc]
      exact Val_subst p s Γ₀ η₀ vs hvs b (d := d + 1) (Γ.snoc A (v.cls Γ))
        (Fin.snoc (α := fun _ => T.El) η vv) w (hs.snoc A (v.cls Γ) vv)
    · have hg' : ¬ (Term.subst p s (d + 1) b).cls
          ((Γ.sub p s).snoc (Term.subst p s d A) ((Term.subst p s d v).cls (Γ.sub p s))) = j := by
        rw [hcb]; exact hg
      exact iff_of_false (not_Val_let T _ _ _ _ _ _ _ hg') (not_Val_let T _ _ _ _ _ _ _ hg)
  | prim c args, d, Γ, η, w, hs => by
    show Val T _ (prim c (fun k => Term.subst p s d (args k))) _ w ↔ _
    have hc : ∀ k, (Term.subst p s d (args k)).cls (Γ.sub p s) = (args k).cls Γ :=
      fun k => Ctx.cls_subst_sub s Γ Γ₀ hs.ctx hs.lev (args k)
    by_cases hg : ∀ k, (args k).cls Γ = c.argSort k
    · have hg' : ∀ k, (Term.subst p s d (args k)).cls (Γ.sub p s) = c.argSort k := fun k =>
        (hc k).trans (hg k)
      rw [Val_prim' T c _ hg', Val_prim' T c _ hg]
      exact and_congr Iff.rfl (exists_congr fun us => and_congr
        (forall_congr' fun k => Val_subst p s Γ₀ η₀ vs hvs (args k) Γ η (us k) hs) Iff.rfl)
    · have hg' : ¬ ∀ k, (Term.subst p s d (args k)).cls (Γ.sub p s) = c.argSort k := by
        simp only [hc]; exact hg
      exact iff_of_false (not_Val_prim T _ _ _ _ _ hg') (not_Val_prim T _ _ _ _ _ hg)

/-- The special case of substitution for the last variable (`d = 0`): the
form used by the β/ζ rules. -/
theorem Val_subst0 {p : ℕ} (Γ : Ctx p) (A : Term) (i : ℕ) (s : Term) (η : Env T p) (vs : T.El)
    (hvs : ∀ w, Val T Γ s η w ↔ w = vs) (hi : s.cls Γ = i) (t : Term) (w : T.El) :
    Val T Γ (Term.subst p s 0 t) η w ↔
      Val T (Γ.snoc A i) t (Fin.snoc (α := fun _ => T.El) η vs) w := by
  have hs : SubOk T p s Γ η vs (d := 0) (Γ.snoc A i) (Fin.snoc (α := fun _ => T.El) η vs) :=
    { ctx := fun l => by
        rw [Ctx.snoc, show (⟨l.1, by omega⟩ : Fin (p + 1 + 0)) = Fin.castSucc l from Fin.ext rfl,
          Fin.snoc_castSucc]
      env := fun l => by
        rw [show (⟨l.1, by omega⟩ : Fin (p + 1 + 0)) = Fin.castSucc l from Fin.ext rfl,
          Fin.snoc_castSucc]
      val := by
        rw [show (⟨p, by omega⟩ : Fin (p + 1 + 0)) = Fin.last p from Fin.ext rfl, Fin.snoc_last]
      lev := by rw [Γ.lev_snoc_self, hi] }
  have := Val_subst T p s Γ η vs hvs t (d := 0) (Γ.snoc A i)
    (Fin.snoc (α := fun _ => T.El) η vs) w hs
  rw [← this]
  have e1 : Ctx.sub p s (d := 0) (Γ.snoc A i) = Γ := by
    funext l
    rw [Ctx.sub_lt _ _ _ l.2, Ctx.snoc,
      show (⟨l.1, by omega⟩ : Fin (p + 1 + 0)) = Fin.castSucc l from Fin.ext rfl, Fin.snoc_castSucc]
  have e2 : Env.remove T p (d := 0) (Fin.snoc (α := fun _ => T.El) η vs) = η := by
    funext l
    rw [Env.remove_lt _ _ _ l.2,
      show (⟨l.1, by omega⟩ : Fin (p + 1 + 0)) = Fin.castSucc l from Fin.ext rfl, Fin.snoc_castSucc]
  rw [e1, e2]

end SolidLean.Calc
