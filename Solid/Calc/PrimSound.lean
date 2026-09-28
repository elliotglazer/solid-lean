import Solid.Calc.SoundBase
import Solid.Calc.PrimSets

/-!
# Soundness: the cases of the primitives (draft 2, §3.4)

For each primitive `c`, the typing rule `Typed.prim` is sound: given the
motive for the arguments, the application has a unique value which lies in
the (unique) value of the result type, itself in the universe of the
application's level.  The computation rules are sound as well.

The cases are assembled by `case_prim` and `eq_prim_*`, used by the
induction in `Soundness.lean`.
-/

universe u

open Classical

namespace SolidLean.Calc

open SolidLean.Solid Term

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### Tools -/

/-- The motive from explicit values. -/
theorem PTy.mk {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ}
    (h : ∀ η, Valid hM Γ η → ∃ (vt : M.T.U r) (vA : M.T.U (r + 1)),
      (∀ w, Val M.T Γ t η w ↔ w = M.T.inj vt) ∧ (∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) ∧
      M.T.mem (M.T.j (r + 1) vA) (hM.univSet r) ∧ M.T.mem (M.T.j r vt) vA) :
    PTy hM Γ t A r := by
  intro η hv
  obtain ⟨vt, vA, hvt, hvA, hAU, hmem⟩ := h η hv
  simp only [hvt, hvA]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun w hw => ?_, fun w vA' hw hvA' => ?_⟩
  · subst hw; exact (TMem_inj _ _ _).2 hAU
  · subst hw; subst hvA'; exact (TMem_inj _ _ _).2 hmem

/-- The motive, read at a valid environment. -/
theorem PTy.vals {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : PTy hM Γ t A r) {η : Env M.T m}
    (hv : Valid hM Γ η) : ∃ (vt : M.T.U r) (vA : M.T.U (r + 1)),
      (∀ w, Val M.T Γ t η w ↔ w = M.T.inj vt) ∧ (∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) ∧
      M.T.mem (M.T.j (r + 1) vA) (hM.univSet r) ∧ M.T.mem (M.T.j r vt) vA := by
  obtain ⟨vt, hvt, hmem⟩ := PTy.term_val hM h hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.tyval hM h hv
  exact ⟨vt, vA, hvt, hvA, hAU, hmem vA ((hvA _).2 rfl)⟩

/-- Transport of the motive along an equivalence of type values. -/
theorem PTy.congr_type {m : ℕ} {Γ : Ctx m} {t A A' : Term} {r : ℕ} (h : PTy hM Γ t A r)
    (e : ∀ η, Valid hM Γ η → ∀ w, Val M.T Γ A η w ↔ Val M.T Γ A' η w) : PTy hM Γ t A' r := by
  intro η hv
  simp only [← e η hv]
  exact h η hv

/-- Transport of the motive along an equivalence of term values. -/
theorem PTy.congr_term {m : ℕ} {Γ : Ctx m} {t t' A : Term} {r : ℕ} (h : PTy hM Γ t A r)
    (e : ∀ η, Valid hM Γ η → ∀ w, Val M.T Γ t η w ↔ Val M.T Γ t' η w) : PTy hM Γ t' A r := by
  intro η hv
  simp only [← e η hv]
  exact h η hv

/-- Data applications with the same values of function and argument have the same values. -/
theorem Val_app_data_congr {m : ℕ} {Γ : Ctx m} {j : ℕ} {f f' x x' : Term} {η : Env M.T m}
    (hf : ∀ w, Val M.T Γ f η w ↔ Val M.T Γ f' η w) (hx : ∀ w, Val M.T Γ x η w ↔ Val M.T Γ x' η w)
    (hcf : f.cls Γ = f'.cls Γ) (hcx : x.cls Γ = x'.cls Γ) :
    ∀ w, Val M.T Γ (.app .data j f x) η w ↔ Val M.T Γ (.app .data j f' x') η w := by
  intro w
  by_cases hg : j ≤ f.cls Γ ∧ x.cls Γ ≤ f.cls Γ
  · obtain ⟨hj, hxf⟩ := hg
    refine Val_sort_iff M.T Γ Γ (.app .data j f' x') (.app .data j f x) η η w rfl fun w' => ?_
    rw [Val_app_data' M.T rfl rfl hj hxf, Val_app_data' M.T hcf.symm hcx.symm hj hxf]
    exact exists_congr fun vf => exists_congr fun va =>
      and_congr (hf _) (and_congr (hx _) Iff.rfl)
  · have hg' : ¬ (j ≤ f'.cls Γ ∧ x'.cls Γ ≤ f'.cls Γ) := by rw [← hcf, ← hcx]; exact hg
    exact iff_of_false (not_Val_app_data M.T _ _ _ _ _ _ hg) (not_Val_app_data M.T _ _ _ _ _ _ hg')

/-- Uniqueness of values from uniqueness among sorted values. -/
theorem val_unique_of_sorted {m : ℕ} {Γ : Ctx m} {t : Term} {η : Env M.T m} {n : ℕ}
    (hc : t.cls Γ = n) (v : M.T.U n) (h : ∀ w' : M.T.U n, Val M.T Γ t η (M.T.inj w') ↔ w' = v) :
    ∀ w, Val M.T Γ t η w ↔ w = M.T.inj v := by
  intro w
  constructor
  · intro hw
    obtain ⟨w', rfl⟩ := elSort M.T w (hw.sort.trans hc)
    rw [(h w').1 hw]
  · rintro rfl; exact (h v).2 rfl

/-- The value relation of a primitive application whose arguments have known values. -/
theorem Val_prim_of_vals {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args : Fin n → Term)
    (hg : ∀ k, (args k).cls Γ = c.argSort k) {η : Env M.T m} (va : Fin n → M.T.El)
    (hva : ∀ k w, Val M.T Γ (args k) η w ↔ w = va k) (w : M.T.El) :
    Val M.T Γ (.prim c args) η w ↔
      w.1 = c.level ∧ c.clauseF.Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) va w) := by
  rw [Val_prim' M.T c args hg]
  refine and_congr Iff.rfl ⟨?_, fun h => ⟨va, fun k => (hva k _).2 rfl, h⟩⟩
  rintro ⟨vs, hvs, h⟩
  have : vs = va := funext fun k => (hva k _).1 (hvs k)
  subst this; exact h

/-- Sorted version. -/
theorem Val_prim_of_vals' {m : ℕ} {Γ : Ctx m} {n : ℕ} (c : Prim n) (args : Fin n → Term)
    (hg : ∀ k, (args k).cls Γ = c.argSort k) {η : Env M.T m} (va : Fin n → M.T.El)
    (hva : ∀ k w, Val M.T Γ (args k) η w ↔ w = va k) {r : ℕ} (hr : c.level = r) (w : M.T.U r) :
    Val M.T Γ (.prim c args) η (M.T.inj w) ↔
      c.clauseF.Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) va (M.T.inj w)) := by
  rw [Val_prim_of_vals c args hg va hva]
  subst hr
  simp

/-- Data applications with known values of the function and the argument. -/
theorem Val_app_data_of_vals {m : ℕ} {Γ : Ctx m} {j : ℕ} {f a : Term} {n k : ℕ} (hf : f.cls Γ = n)
    (hak : a.cls Γ = k) (hj : j ≤ n) (ha : k ≤ n) {η : Env M.T m} {vf : M.T.U n} {va : M.T.U k}
    (hvf : ∀ w, Val M.T Γ f η w ↔ w = M.T.inj vf) (hva : ∀ w, Val M.T Γ a η w ↔ w = M.T.inj va)
    (w : M.T.U j) :
    Val M.T Γ (.app .data j f a) η (M.T.inj w) ↔
      (M.T.sortStr n).FunApp vf (M.T.liftLE ha va) (M.T.liftLE hj w) := by
  rw [Val_app_data' M.T hf hak hj ha]
  constructor
  · rintro ⟨vf', va', h1, h2, h3⟩
    rw [hvf] at h1; rw [hva] at h2
    rw [Sorted.inj_injective M.T.U h1, Sorted.inj_injective M.T.U h2] at h3
    exact h3
  · intro h
    exact ⟨vf, va, (hvf _).2 rfl, (hva _).2 rfl, h⟩

include hM in
/-- The unique value of a data application, given a function value defined at the argument. -/
theorem app_data_val {m : ℕ} {Γ : Ctx m} {j : ℕ} {f a : Term} {n k : ℕ} (hf : f.cls Γ = n)
    (hak : a.cls Γ = k) (hj : j ≤ n) (ha : k ≤ n) {η : Env M.T m} {vf : M.T.U n} {va : M.T.U k}
    (hvf : ∀ w, Val M.T Γ f η w ↔ w = M.T.inj vf) (hva : ∀ w, Val M.T Γ a η w ↔ w = M.T.inj va)
    (hfun : (M.T.sortStr n).IsFunction vf) {w : M.T.U j}
    (hw : (M.T.sortStr n).FunApp vf (M.T.liftLE ha va) (M.T.liftLE hj w)) :
    ∀ w', Val M.T Γ (.app .data j f a) η w' ↔ w' = M.T.inj w := by
  refine val_unique_of_sorted (by rw [Term.cls_app_data]) w (fun w' => ?_)
  rw [Val_app_data_of_vals hf hak hj ha hvf hva]
  constructor
  · intro h
    exact hM.liftLE_injective hj ((hM.sortModel n).funApp_unique hfun h hw)
  · rintro rfl; exact hw

/-- The values of a type argument `A : U_i`: its value is `j A'` for the set `A'` of its elements. -/
theorem type_arg_vals {m : ℕ} {Γ : Ctx m} {A : Term} {i : ℕ} (h : PTy hM Γ A (univ i) (i + 1))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ vA' : M.T.U i, (∀ w, Val M.T Γ A η w ↔ w = M.T.inj (M.T.j i vA')) ∧
      M.T.mem (M.T.j (i + 1) (M.T.j i vA')) (hM.univSet i) := by
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM h hv
  obtain ⟨vA', rfl⟩ := hM.exists_j_of_mem_univSet vA hAU
  exact ⟨vA', hvA, hAU⟩

/-- The value of an element `a : A`, with `A`'s value `j A'`. -/
theorem elem_arg_vals {m : ℕ} {Γ : Ctx m} {a A : Term} {i : ℕ} (h : PTy hM Γ a A i)
    {η : Env M.T m} (hv : Valid hM Γ η) {vA' : M.T.U i}
    (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj (M.T.j i vA')) :
    ∃ va : M.T.U i, (∀ w, Val M.T Γ a η w ↔ w = M.T.inj va) ∧ M.T.mem va vA' := by
  obtain ⟨va, hva, hmem⟩ := PTy.term_val hM h hv
  exact ⟨va, hva, (hM.j_mem_iff i va vA').1 (hmem _ ((hvA _).2 rfl))⟩

/-- The value of a proof `h : P` of a proposition: `P`'s value is `{∅}`. -/
theorem proof_arg_vals {m : ℕ} {Γ : Ctx m} {h P : Term} (hh : PTy hM Γ h P 0) {η : Env M.T m}
    (hv : Valid hM Γ η) {vP : M.T.U 1} (hvP : ∀ w, Val M.T Γ P η w ↔ w = M.T.inj vP) :
    vP = hM.singAt (hM.emptyAt 1) ∧ ∀ w, Val M.T Γ h η w ↔ w = M.T.inj (hM.emptyAt 0) := by
  obtain ⟨vh, vP', hvh, hvP', hPU, hmem⟩ := PTy.vals hM hh hv
  have e : vP' = vP := Sorted.inj_injective M.T.U ((hvP _).1 ((hvP' _).2 rfl))
  subst e
  have e1 := hM.eq_emptyAt_of_mem hPU hmem
  subst e1
  refine ⟨?_, hvh⟩
  rcases hM.tv_char hPU with rfl | rfl
  · exact absurd hmem (hM.not_mem_emptyAt _)
  · rfl

/-- A truth value `{∅}` contains `j ∅`. -/
theorem mem_j_emptyAt_singAt : M.T.mem (M.T.j 0 (hM.emptyAt 0)) (hM.singAt (hM.emptyAt 1)) := by
  rw [hM.j_emptyAt, hM.mem_singAt]

/-- `{∅}` is the truth value of a true proposition. -/
theorem singAt_eq_tvSet {ψ : Prop} (hψ : ψ) : hM.singAt (hM.emptyAt 1) = hM.tvSet ψ := by
  unfold IsTowerModel.tvSet; rw [if_pos hψ]

theorem tvSet_true {ψ : Prop} (hψ : ψ) : hM.tvSet ψ = hM.singAt (hM.emptyAt 1) :=
  (singAt_eq_tvSet hM hψ).symm

/-- Level-`0` values are `∅`: the level-`0` form of `PTy.mk`. -/
theorem PTy.mk0 {m : ℕ} {Γ : Ctx m} {t A : Term}
    (h : ∀ η, Valid hM Γ η → (∀ w, Val M.T Γ t η w ↔ w = M.T.inj (hM.emptyAt 0)) ∧
      (∀ w, Val M.T Γ A η w ↔ w = M.T.inj (hM.singAt (hM.emptyAt 1)))) :
    PTy hM Γ t A 0 := by
  refine PTy.mk hM fun η hv => ⟨hM.emptyAt 0, hM.singAt (hM.emptyAt 1), (h η hv).1, (h η hv).2, ?_,
    mem_j_emptyAt_singAt hM⟩
  rw [singAt_eq_tvSet hM True.intro]
  exact hM.tvSet_mem_univSet True

/-- Value tuples of arguments. -/
theorem vals_cons {m : ℕ} {Γ : Ctx m} {η : Env M.T m} {n : ℕ} {args : Fin (n + 1) → Term} {x : M.T.El}
    {xs : Fin n → M.T.El} (h0 : ∀ w, Val M.T Γ (args 0) η w ↔ w = x)
    (hs : ∀ k w, Val M.T Γ (args k.succ) η w ↔ w = xs k) :
    ∀ k w, Val M.T Γ (args k) η w ↔ w = Matrix.vecCons x xs k :=
  fun k => Fin.cases h0 hs k

theorem vals_nil {m : ℕ} {Γ : Ctx m} {η : Env M.T m} {args : Fin 0 → Term} :
    ∀ k w, Val M.T Γ (args k) η w ↔ w = (![] : Fin 0 → M.T.El) k :=
  fun k => k.elim0

/-- The motive for a type former: result type `univ n`, level `n + 1`. -/
theorem PTy.mk_univ {m : ℕ} {Γ : Ctx m} {t : Term} {n : ℕ}
    (h : ∀ η, Valid hM Γ η → ∃ vt : M.T.U (n + 1), (∀ w, Val M.T Γ t η w ↔ w = M.T.inj vt) ∧
      M.T.mem (M.T.j (n + 1) vt) (hM.univSet n)) :
    PTy hM Γ t (univ n) (n + 1) := by
  refine PTy.mk hM fun η hv => ?_
  obtain ⟨vt, hvt, hmem⟩ := h η hv
  exact ⟨vt, hM.univSet n, hvt, Val_univ_iff hM Γ η n, hM.univSet_mem n, hmem⟩

/-! ### Truth values -/

theorem emptyAt_ne_singAt : hM.emptyAt 1 ≠ hM.singAt (hM.emptyAt 1) := by
  intro h
  have := (hM.mem_singAt (hM.emptyAt 1) (hM.emptyAt 1)).2 rfl
  rw [← h] at this
  exact hM.not_mem_emptyAt _ this

theorem tvSet_true_iff {ψ : Prop} : hM.tvSet ψ = hM.singAt (hM.emptyAt 1) ↔ ψ := by
  unfold IsTowerModel.tvSet
  split_ifs with h
  · exact iff_of_true rfl h
  · exact iff_of_false (emptyAt_ne_singAt hM) h

/-- A proposition with an element is `{∅}`. -/
theorem tv_true_of_mem {vP : M.T.U 1} (hPU : M.T.mem (M.T.j 1 vP) (hM.univSet 0)) {x : M.T.U 0}
    (hx : M.T.mem (M.T.j 0 x) vP) : vP = hM.singAt (hM.emptyAt 1) := by
  rcases hM.tv_char hPU with rfl | rfl
  · exact absurd hx (hM.not_mem_emptyAt _)
  · rfl

/-! ### Values in extended contexts -/

/-- The last variable of an extended context. -/
theorem Val_var_last {m : ℕ} (Γ : Ctx m) (A : Term) (i : ℕ) (η : Env M.T m) (a : M.T.U i) (w : M.T.El) :
    Val M.T (Γ.snoc A i) (var m) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔ w = M.T.inj a := by
  rw [Val_var']
  constructor
  · rintro ⟨h, rfl, -⟩
    show Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a) (Fin.last m) = _
    rw [Fin.snoc_last]
  · rintro rfl
    refine ⟨Nat.lt_succ_self m, ?_, by rw [Ctx.lev_snoc_self]⟩
    show _ = Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a) (Fin.last m)
    rw [Fin.snoc_last]

/-- The second-to-last variable of a doubly extended context. -/
theorem Val_var_last2 {m : ℕ} (Γ : Ctx m) (A B : Term) (i l : ℕ) (η : Env M.T m) (a : M.T.U i) (y : M.T.El)
    (w : M.T.El) :
    Val M.T ((Γ.snoc A i).snoc B l) (var m)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y) w ↔
      w = M.T.inj a := by
  rw [Val_var']
  have hlev : ((Γ.snoc A i).snoc B l).lev m = i := by
    rw [Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self]
  constructor
  · rintro ⟨h, rfl, -⟩
    show Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y
      (Fin.castSucc (Fin.last m)) = _
    rw [Fin.snoc_castSucc, Fin.snoc_last]
  · rintro rfl
    refine ⟨by omega, ?_, by rw [hlev]⟩
    show _ = Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y
      (Fin.castSucc (Fin.last m))
    rw [Fin.snoc_castSucc, Fin.snoc_last]

/-- The third-to-last variable of a triply extended context. -/
theorem Val_var_last3 {m : ℕ} (Γ : Ctx m) (A B C : Term) (i l l' : ℕ) (η : Env M.T m) (a : M.T.U i)
    (y z : M.T.El) (w : M.T.El) :
    Val M.T (((Γ.snoc A i).snoc B l).snoc C l') (var m)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
        (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y) z) w ↔
      w = M.T.inj a := by
  rw [Val_var']
  have hlev : (((Γ.snoc A i).snoc B l).snoc C l').lev m = i := by
    rw [Ctx.lev_snoc_lt _ _ _ (by omega), Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self]
  constructor
  · rintro ⟨h, rfl, -⟩
    show Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y) z
      (Fin.castSucc (Fin.castSucc (Fin.last m))) = _
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]
  · rintro rfl
    refine ⟨by omega, ?_, by rw [hlev]⟩
    show _ = Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) y) z
      (Fin.castSucc (Fin.castSucc (Fin.last m)))
    rw [Fin.snoc_castSucc, Fin.snoc_castSucc, Fin.snoc_last]

theorem Term.shift_two (m : ℕ) (t : Term) : Term.shift (m + 1) 1 (Term.shift m 1 t) = Term.shift m 2 t := by
  have := Term.shift_shift m (m + 1) (Nat.le_succ m) t
  rwa [Nat.add_sub_cancel_left, show m + 1 + 1 - m = 2 by omega] at this

theorem Val_shift2 {m : ℕ} (Γ : Ctx m) (A B : Term) (i l : ℕ) (t : Term) (η : Env M.T m) (x y w : M.T.El) :
    Val M.T ((Γ.snoc A i).snoc B l) (Term.shift m 2 t)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) η x) y) w ↔ Val M.T Γ t η w := by
  rw [← Term.shift_two, Val_shift1, Val_shift1]

theorem Term.shift_three (m : ℕ) (t : Term) :
    Term.shift (m + 2) 1 (Term.shift m 2 t) = Term.shift m 3 t := by
  have := Term.shift_shift m (m + 2) (by omega) t
  rwa [show m + 2 - m = 2 by omega, show m + 2 + 1 - m = 3 by omega] at this

theorem Val_shift3 {m : ℕ} (Γ : Ctx m) (A B C : Term) (i l l' : ℕ) (t : Term) (η : Env M.T m)
    (x y z w : M.T.El) :
    Val M.T (((Γ.snoc A i).snoc B l).snoc C l') (Term.shift m 3 t)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
        (Fin.snoc (α := fun _ => M.T.El) η x) y) z) w ↔ Val M.T Γ t η w := by
  rw [← Term.shift_three, Val_shift1, Val_shift2]

/-! ### Reading product-typed arguments -/

/-- A proof of a proposition-kind product: at each element of the domain, the body's value is
a true proposition. -/
theorem pi_prop_of_pty {m : ℕ} {Γ : Ctx m} {i : ℕ} {f A B : Term} (hf : PTy hM Γ f (pi .prop i 0 A B) 0)
    {η : Env M.T m} (hv : Valid hM Γ η) (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1)
    {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) {a : M.T.U i}
    (ha : M.T.mem (M.T.j i a) vA) :
    ∃ vB : M.T.U 1,
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔ w = M.T.inj vB) ∧
      M.T.mem (M.T.j 1 vB) (hM.univSet 0) ∧ M.T.mem (M.T.j 0 (hM.emptyAt 0)) vB := by
  obtain ⟨vf, vPi, -, hvPi, -, hmem⟩ := PTy.vals hM hf hv
  exact pi_prop_elim hM hcA hcB ((hvPi _).2 rfl) hmem ((hvA _).2 rfl) ha

/-- A function of a data-kind product: its value, and its values at elements of the domain. -/
theorem pi_data_of_pty {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f A B : Term}
    (hf : PTy hM Γ f (pi .data i j A B) (max i j)) {η : Env M.T m} (hv : Valid hM Γ η)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) {vA : M.T.U (i + 1)}
    (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) :
    ∃ vf : M.T.U (max i j), (∀ w, Val M.T Γ f η w ↔ w = M.T.inj vf) ∧
      (M.T.sortStr (max i j)).IsFunction vf ∧
      ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA →
        (∃ v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) v) ∧
        ∃ vB : M.T.U (j + 1),
          (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
            w = M.T.inj vB) ∧
          M.T.mem (M.T.j (j + 1) vB) (hM.univSet j) ∧
          ∀ v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) v →
            ∃ b : M.T.U j, M.T.mem (M.T.j j b) vB ∧ v = M.T.liftLE (le_max_right i j) b := by
  obtain ⟨vf, vPi, hvf, hvPi, -, hmem⟩ := PTy.vals hM hf hv
  refine ⟨vf, hvf, ?_, fun a ha => ?_⟩
  · -- the function property, directly from the product
    have h := (Val_pi_data M.T hcA hcB η vPi).1 ((hvPi _).2 rfl)
    obtain ⟨-, vA₁, hvA₁, p, hp, hpi⟩ := h
    subst hp
    exact ((hpi vf).1 ((hM.j_mem_iff _ _ _).1 hmem)).1
  · obtain ⟨-, h2, vB, h3, h4, h5⟩ := pi_data_elim hM hcA hcB ((hvPi _).2 rfl) hmem ((hvA _).2 rfl) ha
    exact ⟨h2, vB, h3, h4, h5⟩

section Cases

variable {m : ℕ} {Γ : Ctx m}

/-! ### `⊥` and its eliminator -/

theorem case_false (args : Fin 0 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.false_).argSort k) :
    PTy hM Γ (prim .false_ args) (univ 0) 1 := by
  refine PTy.mk_univ hM fun η hv => ⟨hM.emptyAt 1, ?_, ?_⟩
  · refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Γ := Γ) (η := η) (Prim.false_) args hg ![] vals_nil
      (r := 1) rfl, clause_false M.T ![] _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 1⟩
  · rw [hM.mem_univSet_zero, hM.j_emptyAt]; exact Or.inl rfl

theorem case_falseElim (j : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.falseElim j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.falseElim j).argType m args k) ((Prim.falseElim j).argSort k)) :
    PTy hM Γ (prim (.falseElim j) args) (args 0) j := by
  intro η hv
  have h1 : PTy hM Γ (args 1) (prim .false_ ![]) 0 := ih 1
  obtain ⟨vh, vF, -, hvF, hFU, hmem⟩ := PTy.vals hM h1 hv
  -- the value of `⊥` is `∅`, which has no element: the premise is impossible
  exfalso
  have key := Val_prim_of_vals' (Γ := Γ) (η := η) (Prim.false_) ![] (fun k => k.elim0) ![] vals_nil
    (r := 0 + 1) rfl vF
  rw [clause_false M.T ![] _ vF rfl] at key
  exact key.1 ((hvF _).2 rfl) _ hmem

/-! ### Equality -/

theorem case_eq (i : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.eq i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.eq i).argType m args k) ((Prim.eq i).argSort k)) :
    PTy hM Γ (prim (.eq i) args) (univ 0) 1 := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (args 0) i := ih 1
  have h2 : PTy hM Γ (args 2) (args 0) i := ih 2
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h1 hv
  obtain ⟨vb, hvb, -⟩ := PTy.term_val hM h2 hv
  refine ⟨hM.tvSet (va = vb), ?_, hM.tvSet_mem_univSet _⟩
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.eq i) args hg _
    (vals_cons hvA (vals_cons hva (vals_cons hvb vals_nil))) (r := 1) rfl,
    clause_eq M.T i _ _ vA va vb w' rfl rfl rfl rfl, hM.isTV_iff]


/-- Classifier guards for explicit argument vectors. -/
macro "prim_guard" hg:term : tactic => `(tactic|
  (intro k; fin_cases k <;> first
    | exact $hg 0 | exact $hg 1 | exact $hg 2 | exact $hg 3 | exact $hg 4 | exact $hg 5 | rfl))

theorem case_refl (i : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.refl i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.refl i).argType m args k) ((Prim.refl i).argSort k)) :
    PTy hM Γ (prim (.refl i) args) (prim (.eq i) ![args 0, args 1, args 1]) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (args 0) i := ih 1
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h1 hv
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.refl i) args hg _
      (vals_cons hvA (vals_cons hva vals_nil)) (r := 0) rfl, clause_refl M.T i _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.eq i) ![args 0, args 1, args 1] (by prim_guard hg) _
      (vals_cons hvA (vals_cons hva (vals_cons hva vals_nil))) (r := 1) rfl,
      clause_eq M.T i _ _ vA va va w' rfl rfl rfl rfl, hM.isTV_iff, tvSet_true hM rfl]

/-! ### Lifting between universes -/

include hM in
theorem j_liftLE_comm {i d : ℕ} (a : M.T.U i) :
    M.T.liftLE (by omega : i + 1 ≤ i + d + 1) (M.T.j i a) = M.T.j (i + d) (M.T.liftLE (by omega) a) := by
  rw [IsTowerModel.j_eq_liftLE, IsTowerModel.j_eq_liftLE, M.T.liftLE_trans, M.T.liftLE_trans]

theorem case_lift (i d : ℕ) (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.lift i d).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.lift i d).argType m args k) ((Prim.lift i d).argSort k)) :
    PTy hM Γ (prim (.lift i d) args) (univ (i + d)) (i + d + 1) := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM h0 hv
  refine ⟨M.T.liftLE (by omega) vA, ?_, hM.mem_univSet_lift vA hAU d⟩
  refine val_unique_of_sorted (n := i + d + 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.lift i d) args hg _ (vals_cons hvA vals_nil)
    (r := i + d + 1) rfl, clause_lift M.T i d _ _ vA w' rfl rfl]

/-- The value of `lift A`, as a type. -/
theorem lift_type_val (i d : ℕ) (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.lift i d).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA) :
    ∀ w, Val M.T Γ (prim (.lift i d) args) η w ↔
      w = M.T.inj (M.T.liftLE (by omega : i + 1 ≤ i + d + 1) vA) := by
  refine val_unique_of_sorted (n := i + d + 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.lift i d) args hg _ (vals_cons hvA vals_nil)
    (r := i + d + 1) rfl, clause_lift M.T i d _ _ vA w' rfl rfl]

theorem case_up (i d : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.up i d).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.up i d).argType m args k) ((Prim.up i d).argSort k)) :
    PTy hM Γ (prim (.up i d) args) (prim (.lift i d) ![args 0]) (i + d) := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (args 0) i := ih 1
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, hmem⟩ := PTy.term_val hM h1 hv
  have hg' : ∀ k, (![args 0] k).cls Γ = (Prim.lift i d).argSort k :=
    fun k => by fin_cases k; exact hg 0
  refine ⟨M.T.liftLE (by omega : i ≤ i + d) va, M.T.liftLE (by omega : i + 1 ≤ i + d + 1) vA, ?_,
    lift_type_val i d ![args 0] hg' hvA,
    hM.mem_univSet_lift vA hAU d, ?_⟩
  · refine val_unique_of_sorted (n := i + d) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.up i d) args hg _
      (vals_cons hvA (vals_cons hva vals_nil)) (r := i + d) rfl, clause_up M.T i d _ _ va w' rfl rfl]
  · rw [← j_liftLE_comm hM, hM.liftLE_mem_iff]
    exact hmem vA ((hvA _).2 rfl)

theorem case_down (i d : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.down i d).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.down i d).argType m args k) ((Prim.down i d).argSort k)) :
    PTy hM Γ (prim (.down i d) args) (args 0) i := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (prim (.lift i d) ![args 0]) (i + d) := ih 1
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨va, hva, hmem⟩ := PTy.term_val hM h1 hv
  have hg' : ∀ k, (![args 0] k).cls Γ = (Prim.lift i d).argSort k :=
    fun k => by fin_cases k; exact hg 0
  have hmem' := hmem _ ((lift_type_val i d ![args 0] hg' hvA _).2 rfl)
  -- `j va ∈ lift (j A')`, so `va = lift w` for some `w ∈ A'`
  obtain ⟨y, hy, hy'⟩ := hM.mem_liftLE_elim _ hmem'
  obtain ⟨w, hw, rfl⟩ := (hM.mem_j_iff i vA' y).1 hy
  rw [j_liftLE_comm hM] at hy'
  have e := hM.j_injective _ _ _ hy'
  refine ⟨w, M.T.j i vA', ?_, hvA, hAU, (hM.j_mem_iff i w vA').2 hw⟩
  refine val_unique_of_sorted (n := i) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.down i d) args hg _
    (vals_cons hvA (vals_cons hva vals_nil)) (r := i) rfl, clause_down M.T i d _ _ va w' rfl rfl]
  constructor
  · intro h; rw [← e] at h; exact (hM.liftLE_injective _ h).symm
  · rintro rfl; exact e.symm

/-! ### Truncation -/

/-- The value of `Trunc A`, in any context. -/
theorem trunc_type_val {m' : ℕ} {Γ' : Ctx m'} (i : ℕ) (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.trunc i).argSort k)
    {η : Env M.T m'} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ' (args 0) η w ↔ w = M.T.inj vA) :
    ∀ w, Val M.T Γ' (prim (.trunc i) args) η w ↔
      w = M.T.inj (hM.tvSet (∃ a : M.T.U i, M.T.mem (M.T.j i a) vA)) := by
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.trunc i) args hg _ (vals_cons hvA vals_nil)
    (r := 1) rfl, clause_trunc M.T i _ _ vA w' rfl rfl, hM.isTV_iff]

theorem case_trunc (i : ℕ) (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.trunc i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.trunc i).argType m args k) ((Prim.trunc i).argSort k)) :
    PTy hM Γ (prim (.trunc i) args) (univ 0) 1 := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  exact ⟨_, trunc_type_val hM i args hg hvA, hM.tvSet_mem_univSet _⟩

theorem case_truncMk (i : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.truncMk i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.truncMk i).argType m args k) ((Prim.truncMk i).argSort k)) :
    PTy hM Γ (prim (.truncMk i) args) (prim (.trunc i) ![args 0]) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (args 0) i := ih 1
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, hmem⟩ := PTy.term_val hM h1 hv
  have hg' : ∀ k, (![args 0] k).cls Γ = (Prim.trunc i).argSort k :=
    fun k => by fin_cases k; exact hg 0
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.truncMk i) args hg _
      (vals_cons hvA (vals_cons hva vals_nil)) (r := 0) rfl, clause_truncMk M.T i _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · rw [← tvSet_true hM (show ∃ a : M.T.U i, M.T.mem (M.T.j i a) vA from ⟨va, hmem vA ((hvA _).2 rfl)⟩)]
    exact trunc_type_val hM i ![args 0] hg' hvA

/-! ### Natural numbers -/

theorem nat_type_val (args : Fin 0 → Term) {η : Env M.T m} :
    ∀ w, Val M.T Γ (prim .nat args) η w ↔ w = M.T.inj (M.T.j 1 hM.omegaSet) := by
  refine val_unique_of_sorted (n := 2) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Γ := Γ) (η := η) (Prim.nat) args (fun k => k.elim0) ![] vals_nil (r := 2) rfl,
    clause_nat M.T ![] _ w' rfl]
  constructor
  · rintro ⟨o, ho, rfl⟩; rw [hM.isOmega_unique ho]
  · rintro rfl; exact ⟨_, hM.isOmega_omegaSet, rfl⟩

theorem case_nat (args : Fin 0 → Term) : PTy hM Γ (prim .nat args) (univ 1) 2 :=
  PTy.mk_univ hM fun η _ => ⟨_, nat_type_val hM args, hM.j_j_mem_univSet_succ 0 _⟩

theorem case_zero (args : Fin 0 → Term) : PTy hM Γ (prim .zero args) (prim .nat ![]) 1 := by
  refine PTy.mk hM fun η hv => ⟨hM.emptyAt 1, M.T.j 1 hM.omegaSet, ?_, nat_type_val hM ![],
    hM.j_j_mem_univSet_succ 0 _, (hM.j_mem_iff 1 _ _).2 hM.emptyAt_mem_omega⟩
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Γ := Γ) (η := η) (Prim.zero) args (fun k => k.elim0) ![] vals_nil (r := 1) rfl,
    clause_zero M.T ![] _ w' rfl]
  exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 1⟩

theorem case_succ (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.succ).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.succ).argType m args k) ((Prim.succ).argSort k)) :
    PTy hM Γ (prim .succ args) (prim .nat ![]) 1 := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (prim .nat ![]) 1 := ih 0
  obtain ⟨vn, hvn, hmem⟩ := PTy.term_val hM h0 hv
  have hnω : M.T.mem vn hM.omegaSet :=
    (hM.j_mem_iff 1 _ _).1 (hmem _ ((nat_type_val hM ![] _).2 rfl))
  obtain ⟨sn, hsn⟩ := (hM.sortModel 1).exists_succ vn
  refine ⟨sn, M.T.j 1 hM.omegaSet, ?_, nat_type_val hM ![], hM.j_j_mem_univSet_succ 0 _,
    (hM.j_mem_iff 1 _ _).2 (hM.succ_mem_omega hnω hsn)⟩
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.succ) args hg _ (vals_cons hvn vals_nil)
    (r := 1) rfl, clause_succ M.T _ _ vn w' rfl rfl]
  exact ⟨fun h => hM.succ_unique h hsn, fun h => h ▸ hsn⟩

/-! ### Truncation eliminator, propositional extensionality, double negation, unique choice -/

theorem case_truncRec (i : ℕ) (args : Fin 4 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.truncRec i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.truncRec i).argType m args k) ((Prim.truncRec i).argSort k)) :
    PTy hM Γ (prim (.truncRec i) args) (args 1) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (univ 0) 1 := ih 1
  have h2 : PTy hM Γ (args 2) (pi .prop i 0 (args 0) (Term.shift m 1 (args 1))) 0 := ih 2
  have h3 : PTy hM Γ (args 3) (prim (.trunc i) ![args 0]) 0 := ih 3
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨vP, hvP, hPU⟩ := PTy.type_val hM h1 hv
  have hg' : ∀ k, (![args 0] k).cls Γ = (Prim.trunc i).argSort k :=
    fun k => by fin_cases k; exact hg 0
  obtain ⟨htv, -⟩ := proof_arg_vals hM h3 hv (trunc_type_val hM i ![args 0] hg' hvA)
  obtain ⟨a, ha⟩ := (tvSet_true_iff hM).1 htv
  have hcB : (Term.shift m 1 (args 1)).cls (Γ.snoc (args 0) i) = 1 := by
    rw [Term.cls_shift1]; exact hg 1
  obtain ⟨vB, hvB, -, hmem⟩ := pi_prop_of_pty hM h2 hv (hg 0) hcB hvA ha
  have e : vB = vP := by
    have := (hvB _).2 rfl
    rw [Val_shift1, hvP] at this
    exact Sorted.inj_injective M.T.U this
  subst e
  obtain ⟨vf, hvf, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vt, hvt, -⟩ := PTy.term_val hM h3 hv
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.truncRec i) args hg _
      (vals_cons hvA (vals_cons hvP (vals_cons hvf (vals_cons hvt vals_nil)))) (r := 0) rfl,
      clause_truncRec M.T i _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · rw [← tv_true_of_mem hM hPU hmem]; exact hvP

theorem case_propext (args : Fin 4 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.propext).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.propext).argType m args k) ((Prim.propext).argSort k)) :
    PTy hM Γ (prim .propext args) (prim (.eq 1) ![univ 0, args 0, args 1]) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ 0) 1 := ih 0
  have h1 : PTy hM Γ (args 1) (univ 0) 1 := ih 1
  have h2 : PTy hM Γ (args 2) (pi .prop 0 0 (args 0) (Term.shift m 1 (args 1))) 0 := ih 2
  have h3 : PTy hM Γ (args 3) (pi .prop 0 0 (args 1) (Term.shift m 1 (args 0))) 0 := ih 3
  obtain ⟨vP, hvP, hPU⟩ := PTy.type_val hM h0 hv
  obtain ⟨vQ, hvQ, hQU⟩ := PTy.type_val hM h1 hv
  have hcQ : (Term.shift m 1 (args 1)).cls (Γ.snoc (args 0) 0) = 1 := by
    rw [Term.cls_shift1]; exact hg 1
  have hcP : (Term.shift m 1 (args 0)).cls (Γ.snoc (args 1) 0) = 1 := by
    rw [Term.cls_shift1]; exact hg 0
  -- `P` inhabited implies `Q` inhabited, and conversely
  have hPQ : M.T.mem (M.T.j 0 (hM.emptyAt 0)) vP → M.T.mem (M.T.j 0 (hM.emptyAt 0)) vQ := by
    intro hp
    obtain ⟨vB, hvB, -, hmem⟩ := pi_prop_of_pty hM h2 hv (hg 0) hcQ hvP hp
    have e : vB = vQ := by
      have := (hvB _).2 rfl
      rw [Val_shift1, hvQ] at this
      exact Sorted.inj_injective M.T.U this
    subst e; exact hmem
  have hQP : M.T.mem (M.T.j 0 (hM.emptyAt 0)) vQ → M.T.mem (M.T.j 0 (hM.emptyAt 0)) vP := by
    intro hq
    obtain ⟨vB, hvB, -, hmem⟩ := pi_prop_of_pty hM h3 hv (hg 1) hcP hvQ hq
    have e : vB = vP := by
      have := (hvB _).2 rfl
      rw [Val_shift1, hvP] at this
      exact Sorted.inj_injective M.T.U this
    subst e; exact hmem
  have hPQ' : vP = vQ := by
    rw [hM.eq_tvSet_of_mem_univSet hPU, hM.eq_tvSet_of_mem_univSet hQU]
    unfold IsTowerModel.tvSet
    by_cases hp : M.T.mem (M.T.j 0 (hM.emptyAt 0)) vP
    · rw [if_pos hp, if_pos (hPQ hp)]
    · rw [if_neg hp, if_neg (fun hq => hp (hQP hq))]
  obtain ⟨vf, hvf, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vg, hvg, -⟩ := PTy.term_val hM h3 hv
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.propext) args hg _
      (vals_cons hvP (vals_cons hvQ (vals_cons hvf (vals_cons hvg vals_nil)))) (r := 0) rfl,
      clause_propext M.T _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.eq 1) ![univ 0, args 0, args 1] (by prim_guard hg) _
      (vals_cons (Val_univ_iff hM Γ η 0) (vals_cons hvP (vals_cons hvQ vals_nil))) (r := 1) rfl,
      clause_eq M.T 1 _ _ (hM.univSet 0) vP vQ w' rfl rfl rfl rfl, hM.isTV_iff, tvSet_true hM hPQ']

theorem case_dne (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.dne).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.dne).argType m args k) ((Prim.dne).argSort k)) :
    PTy hM Γ (prim .dne args) (args 0) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ 0) 1 := ih 0
  have h1 : PTy hM Γ (args 1) (pi .prop 0 0 (pi .prop 0 0 (args 0) (prim .false_ ![])) (prim .false_ ![])) 0 :=
    ih 1
  obtain ⟨vP, hvP, hPU⟩ := PTy.type_val hM h0 hv
  obtain ⟨vh, vY, hvh, hvY, -, hmem⟩ := PTy.vals hM h1 hv
  -- the value of `⊥` in any context is `∅`
  have hbot : ∀ {m' : ℕ} (Γ' : Ctx m') (η' : Env M.T m') (vB : M.T.U 1),
      Val M.T Γ' (prim .false_ ![]) η' (M.T.inj vB) ↔ (M.T.sortStr 1).IsEmptySet vB := by
    intro m' Γ' η' vB
    rw [Val_prim_of_vals' (Γ := Γ') (η := η') (Prim.false_) ![] (fun k => k.elim0) ![] vals_nil (r := 1) rfl,
      clause_false M.T ![] _ vB rfl]
  -- the value of `Y = (X → ⊥)` is a true proposition, hence `X`'s value is empty
  have hY := (Val_pi_prop M.T (i := 0) (j := 0) (A := pi .prop 0 0 (args 0) (prim .false_ ![]))
    (B := prim .false_ ![]) rfl rfl η vY).1 ((hvY _).2 rfl)
  obtain ⟨-, vX, hvX, htv⟩ := hY
  rw [hM.isTV_iff] at htv
  have hXempty : ∀ q : M.T.U 0, ¬ M.T.mem (M.T.j 0 q) vX := by
    intro q hq
    have hψ : ∀ a : M.T.U 0, M.T.mem (M.T.j 0 a) vX → ∃ vB : M.T.U 1,
        Val M.T (Γ.snoc (pi .prop 0 0 (args 0) (prim .false_ ![])) 0) (prim .false_ ![])
          (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ∧
        ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vB := by
      by_contra hn
      rw [htv] at hmem
      unfold IsTowerModel.tvSet at hmem
      rw [if_neg hn] at hmem
      exact hM.not_mem_emptyAt _ hmem
    obtain ⟨vB, hvB, e, he, hs⟩ := hψ q hq
    rw [hbot] at hvB
    exact hvB e ((hs e).2 rfl)
  -- the value of `X = (P → ⊥)` is a false proposition, hence `P`'s value is inhabited
  have hX := (Val_pi_prop M.T (i := 0) (j := 0) (A := args 0) (B := prim .false_ ![])
    (hg 0) rfl η vX).1 hvX
  obtain ⟨-, vP', hvP', htv'⟩ := hX
  have e : vP' = vP := Sorted.inj_injective M.T.U ((hvP _).1 hvP')
  subst e
  rw [hM.isTV_iff] at htv'
  have hnot : ¬ ∀ a : M.T.U 0, M.T.mem (M.T.j 0 a) vP' → ∃ vB : M.T.U 1,
      Val M.T (Γ.snoc (args 0) 0) (prim .false_ ![]) (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ∧
      ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vB := by
    intro hψ
    rw [htv', tvSet_true hM hψ] at hXempty
    exact hXempty _ (mem_j_emptyAt_singAt hM)
  have hinh : ∃ a : M.T.U 0, M.T.mem (M.T.j 0 a) vP' := by
    by_contra hn
    exact hnot (fun a ha => absurd ⟨a, ha⟩ hn)
  obtain ⟨a, ha⟩ := hinh
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.dne) args hg _
      (vals_cons hvP (vals_cons hvh vals_nil)) (r := 0) rfl, clause_dne M.T _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · rw [← tv_true_of_mem hM hPU ha]; exact hvP

theorem case_uchoice (i : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.uchoice i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.uchoice i).argType m args k) ((Prim.uchoice i).argSort k)) :
    PTy hM Γ (prim (.uchoice i) args) (args 0) i := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (prim (.trunc i) ![args 0]) 0 := ih 1
  have h2 : PTy hM Γ (args 2) (pi .prop i 0 (args 0) (pi .prop i 0 (Term.shift m 1 (args 0))
    (prim (.eq i) ![Term.shift m 2 (args 0), var m, var (m + 1)]))) 0 := ih 2
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM h0 hv
  have hg' : ∀ k, (![args 0] k).cls Γ = (Prim.trunc i).argSort k :=
    fun k => by fin_cases k; exact hg 0
  obtain ⟨htv, hvh⟩ := proof_arg_vals hM h1 hv (trunc_type_val hM i ![args 0] hg' hvA)
  obtain ⟨a₀, ha₀⟩ := (tvSet_true_iff hM).1 htv
  -- any two elements are equal
  have huniq : ∀ x y : M.T.U i, M.T.mem (M.T.j i x) vA → M.T.mem (M.T.j i y) vA → x = y := by
    intro x y hx hy
    have hcA' : (Term.shift m 1 (args 0)).cls (Γ.snoc (args 0) i) = i + 1 := by
      rw [Term.cls_shift1]; exact hg 0
    obtain ⟨vB, hvB, -, hmem⟩ := pi_prop_of_pty hM h2 hv (hg 0) rfl hvA hx
    have hB := (Val_pi_prop M.T (Γ := Γ.snoc (args 0) i) (i := i) (j := 0) hcA' rfl _ vB).1 ((hvB _).2 rfl)
    obtain ⟨-, vA', hvA', htv'⟩ := hB
    rw [Val_shift1, hvA] at hvA'
    have e : vA' = vA := Sorted.inj_injective M.T.U hvA'
    subst e
    rw [hM.isTV_iff] at htv'
    have hψ : ∀ b : M.T.U i, M.T.mem (M.T.j i b) vA' → ∃ vC : M.T.U 1,
        Val M.T ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i)
          (prim (.eq i) ![Term.shift m 2 (args 0), var m, var (m + 1)])
          (Fin.snoc (Fin.snoc η (M.T.inj x)) (M.T.inj b)) (M.T.inj vC) ∧
        ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vC := by
      by_contra hn
      rw [htv'] at hmem
      unfold IsTowerModel.tvSet at hmem
      rw [if_neg hn] at hmem
      exact hM.not_mem_emptyAt _ hmem
    obtain ⟨vC, hvC, e, he, hs⟩ := hψ y hy
    have hg : ∀ k, (![Term.shift m 2 (args 0), var m, var (m + 1)] k).cls
        ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) = (Prim.eq i).argSort k := by
      intro k; fin_cases k
      · show (Term.shift m 2 (args 0)).cls _ = i + 1
        rw [← Term.shift_two, Term.cls_shift1, Term.cls_shift1]; exact hg 0
      · show ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i).lev m = i
        rw [Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self]
      · show ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i).lev (m + 1) = i
        rw [Ctx.lev_snoc_self]
    have hv0 : ∀ w, Val M.T ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) (Term.shift m 2 (args 0))
        (Fin.snoc (Fin.snoc η (M.T.inj x)) (M.T.inj y)) w ↔ w = M.T.inj vA' := fun w => by
      rw [Val_shift2, hvA]
    have hv1 : ∀ w, Val M.T ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) (var m)
        (Fin.snoc (Fin.snoc η (M.T.inj x)) (M.T.inj y)) w ↔ w = M.T.inj x := fun w =>
      Val_var_last2 Γ _ _ i i η x _ w
    have hv2 : ∀ w, Val M.T ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) (var (m + 1))
        (Fin.snoc (Fin.snoc η (M.T.inj x)) (M.T.inj y)) w ↔ w = M.T.inj y := fun w =>
      Val_var_last (Γ.snoc (args 0) i) _ i _ y w
    rw [Val_prim_of_vals' (Prim.eq i) _ hg _ (vals_cons hv0 (vals_cons hv1 (vals_cons hv2 vals_nil)))
      (r := 1) rfl, clause_eq M.T i _ _ vA' x y vC rfl rfl rfl rfl, hM.isTV_iff] at hvC
    rw [hM.eq_emptyAt he] at hs
    rw [hvC] at hs
    exact (tvSet_true_iff hM).1 (hM.eq_singAt hs)
  obtain ⟨vh, hvh', -⟩ := PTy.term_val hM h1 hv
  obtain ⟨vu, hvu, -⟩ := PTy.term_val hM h2 hv
  refine ⟨a₀, vA, ?_, hvA, hAU, ha₀⟩
  refine val_unique_of_sorted (n := i) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.uchoice i) args hg _
    (vals_cons hvA (vals_cons hvh' (vals_cons hvu vals_nil))) (r := i) rfl,
    clause_uchoice M.T i _ _ vA w' rfl rfl]
  constructor
  · rintro ⟨hw, -⟩; exact huniq w' a₀ hw ha₀
  · intro h; rw [h]; exact ⟨ha₀, fun x hx => huniq x a₀ hx ha₀⟩


/-! ### Σ-types -/

/-- A type family `B : Π (x : A). U_j`: its value is a function whose value at `lift a` is the lift
of `j B(a)'`, for the set `B(a)'` of elements of `B(a)`. -/
theorem fam_of_pty {i j : ℕ} {A B : Term} (hB : PTy hM Γ B (pi .data i (j + 1) A (univ j)) (max i (j + 1)))
    {η : Env M.T m} (hv : Valid hM Γ η) (hcA : A.cls Γ = i + 1) {vA : M.T.U (i + 1)}
    (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) :
    ∃ vB : M.T.U (max i (j + 1)), (∀ w, Val M.T Γ B η w ↔ w = M.T.inj vB) ∧
      (M.T.sortStr (max i (j + 1))).IsFunction vB ∧
      (∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vBa' : M.T.U j,
        (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a)
          (M.T.liftLE (le_max_right _ _) (M.T.j j vBa'))) ∧
      ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ v,
        (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a) v →
        ∃ vBa' : M.T.U j, v = M.T.liftLE (le_max_right _ _) (M.T.j j vBa') ∧
          M.T.mem (M.T.j (j + 1) (M.T.j j vBa')) (hM.univSet j) := by
  obtain ⟨vB, hvB, hfun, hval⟩ := pi_data_of_pty hM hB hv hcA rfl hvA
  have key : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ v,
      (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a) v →
      ∃ vBa' : M.T.U j, v = M.T.liftLE (le_max_right _ _) (M.T.j j vBa') ∧
        M.T.mem (M.T.j (j + 1) (M.T.j j vBa')) (hM.univSet j) := by
    intro a ha v hv'
    obtain ⟨-, vU, hvU, -, hrng⟩ := hval a ha
    obtain ⟨b, hb, rfl⟩ := hrng v hv'
    have e : vU = hM.univSet j := by
      have := (hvU _).2 rfl
      rw [Val_univ_iff hM] at this
      exact Sorted.inj_injective M.T.U this
    subst e
    obtain ⟨b', rfl⟩ := hM.exists_j_of_mem_univSet b hb
    exact ⟨b', rfl, hb⟩
  refine ⟨vB, hvB, hfun, fun a ha => ?_, key⟩
  obtain ⟨⟨v, hv'⟩, -⟩ := hval a ha
  obtain ⟨vBa', rfl, -⟩ := key a ha v hv'
  exact ⟨vBa', hv'⟩

include hM in
/-- The Σ-set of a family, and the value of the type `Σ A B`. -/
theorem sigma_type_val (i j : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.sigma i j).argSort k)
    {η : Env M.T m} {vA' : M.T.U i} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA'))
    {vB : M.T.U (max i (j + 1))} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    (hfun : (M.T.sortStr (max i (j + 1))).IsFunction vB)
    (hB : ∀ a, M.T.mem a vA' → ∃ vBa' : M.T.U j, (M.T.sortStr (max i (j + 1))).FunApp vB
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) (M.T.j j vBa'))) :
    ∃ p : M.T.U (max i j), (∀ q, M.T.mem q p ↔ SigmaMem M.T i j (M.T.j i vA') vB q) ∧
      ∀ w, Val M.T Γ (prim (.sigma i j) args) η w ↔ w = M.T.inj (M.T.j (max i j) p) := by
  obtain ⟨p, hp⟩ := exists_sigmaSet hM vA' vB hfun hB
  refine ⟨p, hp, val_unique_of_sorted (n := max i j + 1) rfl _ fun w' => ?_⟩
  rw [Val_prim_of_vals' (Prim.sigma i j) args hg _
    (vals_cons hvA (vals_cons hvB vals_nil)) (r := max i j + 1) rfl,
    clause_sigma M.T i j _ _ (M.T.j i vA') vB w' rfl rfl rfl]
  constructor
  · rintro ⟨p', rfl, hp'⟩
    rw [hM.ext_of_iff hp' hp]
  · rintro rfl; exact ⟨p, rfl, hp⟩

theorem case_sigma (i j : ℕ) (args : Fin 2 → Term) (hok : (Prim.sigma i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.sigma i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.sigma i j).argType m args k) ((Prim.sigma i j).argSort k)) :
    PTy hM Γ (prim (.sigma i j) args) (univ (max i j)) (max i j + 1) := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)) := ih 1
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB, hvB, hfun, hB, -⟩ := fam_of_pty hM h1 hv (hg 0) hvA
  have hB' : ∀ a, M.T.mem a vA' → ∃ vBa' : M.T.U j, (M.T.sortStr (max i (j + 1))).FunApp vB
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) (M.T.j j vBa')) :=
    fun a ha => hB a ((hM.j_mem_iff i a vA').2 ha)
  obtain ⟨p, -, hval⟩ := sigma_type_val hM i j args hg hvA hvB hfun hB'
  exact ⟨_, hval, mem_univSet_of_pos hM (by simp only [Prim.Ok] at hok; omega) p⟩

/-- The data of the Σ-type of `pair`/`fst`/`snd`'s first two arguments. -/
theorem sigma_data {n : ℕ} (i j : ℕ) (args : Fin (n + 2) → Term)
    (hAB : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.sigma i j).argSort k)
    (h0 : PTy hM Γ (args 0) (univ i) (i + 1))
    (h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ (vA' : M.T.U i) (vB : M.T.U (max i (j + 1))) (p : M.T.U (max i j)),
      (∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA')) ∧
      M.T.mem (M.T.j (i + 1) (M.T.j i vA')) (hM.univSet i) ∧
      (∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB) ∧
      (M.T.sortStr (max i (j + 1))).IsFunction vB ∧
      (∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') → ∀ v,
        (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a) v →
        ∃ vBa' : M.T.U j, v = M.T.liftLE (le_max_right _ _) (M.T.j j vBa') ∧
          M.T.mem (M.T.j (j + 1) (M.T.j j vBa')) (hM.univSet j)) ∧
      (∀ q, M.T.mem q p ↔ SigmaMem M.T i j (M.T.j i vA') vB q) ∧
      (∀ w, Val M.T Γ (prim (.sigma i j) ![args 0, args 1]) η w ↔ w = M.T.inj (M.T.j (max i j) p)) := by
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB, hvB, hfun, hB, hval⟩ := fam_of_pty hM h1 hv (hAB 0) hvA
  have hB' : ∀ a, M.T.mem a vA' → ∃ vBa' : M.T.U j, (M.T.sortStr (max i (j + 1))).FunApp vB
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) (M.T.j j vBa')) :=
    fun a ha => hB a ((hM.j_mem_iff i a vA').2 ha)
  obtain ⟨p, hp, hpval⟩ := sigma_type_val hM i j ![args 0, args 1] hAB hvA hvB hfun hB'
  exact ⟨vA', vB, p, hvA, hAU, hvB, hfun, hval, hp, hpval⟩

theorem case_pair (i j : ℕ) (args : Fin 4 → Term) (hok : (Prim.pair i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.pair i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.pair i j).argType m args k) ((Prim.pair i j).argSort k)) :
    PTy hM Γ (prim (.pair i j) args) (prim (.sigma i j) ![args 0, args 1]) (max i j) := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (args 0) i := ih 2
  have h3 : PTy hM Γ (args 3) (app .data (j + 1) (args 1) (args 2)) j := ih 3
  have hAB : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.sigma i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1]
  obtain ⟨vA', vB, p, hvA, hAU, hvB, hfun, hval, hp, hpval⟩ := sigma_data hM i j args hAB h0 h1 hv
  obtain ⟨va, hva, ha⟩ := elem_arg_vals hM h2 hv hvA
  have ha' : M.T.mem (M.T.j i va) (M.T.j i vA') := (hM.j_mem_iff i va vA').2 ha
  obtain ⟨vb, vBa, hvb, hvBa, -, hb⟩ := PTy.vals hM h3 hv
  -- the type of `b` is `B a`, whose value is the lift of `j B(a)'`
  have happ := (Val_app_data_of_vals (hg 1) (hg 2) (le_max_right _ _)
    (le_max_left _ _) hvB hva vBa).1 ((hvBa _).2 rfl)
  obtain ⟨vBa', hvBa', -⟩ := hval va ha' _ happ
  have e : vBa = M.T.j j vBa' := hM.liftLE_injective _ hvBa'
  subst e
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (M.T.liftLE (le_max_left i j) va)
    (M.T.liftLE (le_max_right i j) vb)
  refine ⟨q, M.T.j (max i j) p, ?_, hpval, mem_univSet_of_pos hM (by simp only [Prim.Ok] at hok; omega) p,
    ?_⟩
  · refine val_unique_of_sorted (n := max i j) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.pair i j) args hg _
      (vals_cons hvA (vals_cons hvB (vals_cons hva (vals_cons hvb vals_nil)))) (r := max i j) rfl,
      clause_pair M.T i j _ _ va vb w' rfl rfl rfl]
    exact ⟨fun h => (hM.sortModel (max i j)).ordPair_unique h hq, fun h => h ▸ hq⟩
  · rw [hM.j_mem_iff, hp]
    exact ⟨va, ha', _, happ, M.T.j j vBa', rfl, vb, hb, hq⟩

include hM in
/-- The components of an element of a Σ-type. -/
theorem sigma_elem {i j : ℕ} {vA' : M.T.U i} {vB : M.T.U (max i (j + 1))} {p : M.T.U (max i j)}
    (hval : ∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') → ∀ v,
      (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a) v →
      ∃ vBa' : M.T.U j, v = M.T.liftLE (le_max_right _ _) (M.T.j j vBa') ∧
        M.T.mem (M.T.j (j + 1) (M.T.j j vBa')) (hM.univSet j))
    (hp : ∀ q, M.T.mem q p ↔ SigmaMem M.T i j (M.T.j i vA') vB q) {vs : M.T.U (max i j)}
    (hs : M.T.mem (M.T.j (max i j) vs) (M.T.j (max i j) p)) :
    ∃ (a : M.T.U i) (vBa' : M.T.U j) (b : M.T.U j), M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a)
        (M.T.liftLE (le_max_right _ _) (M.T.j j vBa')) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j vBa')) (hM.univSet j) ∧
      M.T.mem (M.T.j j b) (M.T.j j vBa') ∧
      (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) vs := by
  rw [hM.j_mem_iff, hp] at hs
  obtain ⟨a, ha, v, hv, vBa, rfl, b, hb, hq⟩ := hs
  obtain ⟨vBa', hvBa', hU⟩ := hval a ha _ hv
  have e : vBa = M.T.j j vBa' := hM.liftLE_injective _ hvBa'
  subst e
  exact ⟨a, vBa', b, ha, hv, hU, hb, hq⟩

include hM in
/-- The value of `fst A B s`. -/
theorem fst_val (i j : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.fst i j).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (max i (j + 1))} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {vs : M.T.U (max i j)} (hvs : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vs) {a : M.T.U i} {b : M.T.U j}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) vs) :
    ∀ w, Val M.T Γ (prim (.fst i j) args) η w ↔ w = M.T.inj a := by
  refine val_unique_of_sorted (n := i) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.fst i j) args hg _
    (vals_cons hvA (vals_cons hvB (vals_cons hvs vals_nil))) (r := i) rfl,
    clause_fst M.T i j _ _ vs w' rfl rfl]
  constructor
  · rintro ⟨v, hv⟩
    exact hM.liftLE_injective _ ((hM.sortModel (max i j)).ordPair_inj hv hq).1
  · rintro rfl; exact ⟨_, hq⟩

theorem case_fst (i j : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.fst i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.fst i j).argType m args k) ((Prim.fst i j).argSort k)) :
    PTy hM Γ (prim (.fst i j) args) (args 0) i := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (prim (.sigma i j) ![args 0, args 1]) (max i j) := ih 2
  have hAB : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.sigma i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1]
  obtain ⟨vA', vB, p, hvA, hAU, hvB, hfun, hval, hp, hpval⟩ := sigma_data hM i j args hAB h0 h1 hv
  obtain ⟨vs, hvs, hsmem⟩ := PTy.term_val hM h2 hv
  obtain ⟨a, vBa', b, ha, hBa, -, hb, hq⟩ := sigma_elem hM hval hp (hsmem _ ((hpval _).2 rfl))
  exact ⟨a, M.T.j i vA', fst_val hM i j args hg hvA hvB hvs hq, hvA, hAU, ha⟩

theorem case_snd (i j : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.snd i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.snd i j).argType m args k) ((Prim.snd i j).argSort k)) :
    PTy hM Γ (prim (.snd i j) args) (app .data (j + 1) (args 1) (prim (.fst i j) ![args 0, args 1, args 2])) j := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (prim (.sigma i j) ![args 0, args 1]) (max i j) := ih 2
  have hAB : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.sigma i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1]
  obtain ⟨vA', vB, p, hvA, hAU, hvB, hfun, hval, hp, hpval⟩ := sigma_data hM i j args hAB h0 h1 hv
  obtain ⟨vs, hvs, hsmem⟩ := PTy.term_val hM h2 hv
  obtain ⟨a, vBa', b, ha, hBa, hBU, hb, hq⟩ := sigma_elem hM hval hp (hsmem _ ((hpval _).2 rfl))
  have hg' : ∀ k, (![args 0, args 1, args 2] k).cls Γ = (Prim.fst i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; exact hg 2]
  have hfst := fst_val hM i j ![args 0, args 1, args 2] hg' hvA hvB hvs hq
  refine ⟨b, M.T.j j vBa', ?_, ?_, ?_, hb⟩
  · refine val_unique_of_sorted (n := j) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.snd i j) args hg _
      (vals_cons hvA (vals_cons hvB (vals_cons hvs vals_nil))) (r := j) rfl,
      clause_snd M.T i j _ _ vs w' rfl rfl]
    constructor
    · rintro ⟨u, hu⟩
      exact hM.liftLE_injective _ ((hM.sortModel (max i j)).ordPair_inj hu hq).2
    · rintro rfl; exact ⟨_, hq⟩
  · exact app_data_val hM (hg 1) rfl (le_max_right _ _) (le_max_left _ _) hvB hfst hfun hBa
  · exact hBU

/-! ### The eliminator of equality -/

/-- The value of `refl A a`. -/
theorem refl_val {m' : ℕ} {Γ' : Ctx m'} (i : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.refl i).argSort k)
    {η : Env M.T m'} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ' (args 0) η w ↔ w = M.T.inj vA)
    {va : M.T.U i} (hva : ∀ w, Val M.T Γ' (args 1) η w ↔ w = M.T.inj va) :
    ∀ w, Val M.T Γ' (prim (.refl i) args) η w ↔ w = M.T.inj (hM.emptyAt 0) := by
  refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.refl i) args hg _
    (vals_cons hvA (vals_cons hva vals_nil)) (r := 0) rfl, clause_refl M.T i _ _ w' rfl]
  exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩

/-- The value of `eq A a b`, in any context. -/
theorem eq_type_val {m' : ℕ} {Γ' : Ctx m'} (i : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.eq i).argSort k)
    {η : Env M.T m'} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ' (args 0) η w ↔ w = M.T.inj vA)
    {va vb : M.T.U i} (hva : ∀ w, Val M.T Γ' (args 1) η w ↔ w = M.T.inj va)
    (hvb : ∀ w, Val M.T Γ' (args 2) η w ↔ w = M.T.inj vb) :
    ∀ w, Val M.T Γ' (prim (.eq i) args) η w ↔ w = M.T.inj (hM.tvSet (va = vb)) := by
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.eq i) args hg _
    (vals_cons hvA (vals_cons hva (vals_cons hvb vals_nil))) (r := 1) rfl,
    clause_eq M.T i _ _ vA va vb w' rfl rfl rfl rfl, hM.isTV_iff]

theorem case_eqRec (i j : ℕ) (args : Fin 6 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.eqRec i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.eqRec i j).argType m args k) ((Prim.eqRec i j).argSort k)) :
    PTy hM Γ (prim (.eqRec i j) args) (app .data (j + 1) (app .data (j + 1) (args 2) (args 4)) (args 5)) j := by
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (args 0) i := ih 1
  have h3 : PTy hM Γ (args 3) (app .data (j + 1) (app .data (j + 1) (args 2) (args 1))
    (prim (.refl i) ![args 0, args 1])) j := ih 3
  have h4 : PTy hM Γ (args 4) (args 0) i := ih 4
  have h5 : PTy hM Γ (args 5) (prim (.eq i) ![args 0, args 1, args 4]) 0 := ih 5
  have hgr : ∀ k, (![args 0, args 1] k).cls Γ = (Prim.refl i).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1]
  have hge : ∀ k, (![args 0, args 1, args 4] k).cls Γ = (Prim.eq i).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; exact hg 4]
  -- the values of the two types coincide
  have e : ∀ η, Valid hM Γ η → ∀ w,
      Val M.T Γ (app .data (j + 1) (app .data (j + 1) (args 2) (args 1)) (prim (.refl i) ![args 0, args 1])) η w ↔
      Val M.T Γ (app .data (j + 1) (app .data (j + 1) (args 2) (args 4)) (args 5)) η w := by
    intro η hv
    obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
    obtain ⟨va, hva, -⟩ := PTy.term_val hM h1 hv
    obtain ⟨vb, hvb, -⟩ := PTy.term_val hM h4 hv
    obtain ⟨htv, hvp⟩ := proof_arg_vals hM h5 hv
      (eq_type_val hM i ![args 0, args 1, args 4] hge hvA hva hvb)
    have hab : va = vb := (tvSet_true_iff hM).1 htv
    subst hab
    refine Val_app_data_congr (Val_app_data_congr (fun _ => Iff.rfl) (fun w => ?_) rfl
      ((hg 1).trans (hg 4).symm)) (fun w => ?_) rfl
      (hg 5).symm
    · rw [hva, hvb]
    · rw [refl_val hM i ![args 0, args 1] hgr hvA hva, hvp]
  refine PTy.congr_term hM (PTy.congr_type hM h3 e) fun η hv w => ?_
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h1 hv
  obtain ⟨vC, hvC, -⟩ := PTy.term_val hM (ih 2) hv
  obtain ⟨vc, hvc, -⟩ := PTy.term_val hM h3 hv
  obtain ⟨vb, hvb, -⟩ := PTy.term_val hM h4 hv
  obtain ⟨vp, hvp, -⟩ := PTy.term_val hM h5 hv
  rw [hvc, Val_prim_of_vals (Prim.eqRec i j) args hg
    ![M.T.inj vA, M.T.inj va, M.T.inj vC, M.T.inj vc, M.T.inj vb, M.T.inj vp]
    (vals_cons hvA (vals_cons hva (vals_cons hvC (vals_cons hvc (vals_cons hvb (vals_cons hvp vals_nil))))))]
  constructor
  · rintro rfl
    refine ⟨rfl, ?_⟩
    rw [clause_eqRec M.T i j ![M.T.inj vA, M.T.inj va, M.T.inj vC, M.T.inj vc, M.T.inj vb, M.T.inj vp]
      _ vc vc rfl rfl]
  · rintro ⟨hw, h⟩
    obtain ⟨w', rfl⟩ := elSort M.T w hw
    rw [(clause_eqRec M.T i j ![M.T.inj vA, M.T.inj va, M.T.inj vC, M.T.inj vc, M.T.inj vb, M.T.inj vp]
      _ vc w' rfl rfl).1 h]
    rfl

/-! ### Sum types -/

theorem emptyAt_ne_singAt' (n : ℕ) : hM.emptyAt n ≠ hM.singAt (hM.emptyAt n) := by
  intro h
  have := (hM.mem_singAt (hM.emptyAt n) (hM.emptyAt n)).2 rfl
  rw [← h] at this
  exact hM.not_mem_emptyAt _ this

include hM in
/-- The two tags `∅` and `{∅}` of a sum are distinct. -/
theorem tag_ne {n : ℕ} {z e : M.T.U n} (hz : (M.T.sortStr n).IsEmptySet z)
    (he : (M.T.sortStr n).IsEmptySet e) {s : M.T.U n} (hs : (M.T.sortStr n).IsSingleton e s) : z ≠ s := by
  rw [hM.eq_emptyAt hz, hM.eq_singAt hs, hM.eq_emptyAt he]
  exact emptyAt_ne_singAt' hM n

include hM in
/-- The sum set of two types, and the value of the type `A + B`. -/
theorem sum_type_val (i j : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.sum i j).argSort k)
    {η : Env M.T m} {vA' : M.T.U i} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA'))
    {vB' : M.T.U j} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj (M.T.j j vB')) :
    ∃ p : M.T.U (max i j), (∀ q, M.T.mem q p ↔ SumMem M.T i j (M.T.j i vA') (M.T.j j vB') q) ∧
      ∀ w, Val M.T Γ (prim (.sum i j) args) η w ↔ w = M.T.inj (M.T.j (max i j) p) := by
  obtain ⟨p, hp⟩ := exists_sumSet hM vA' vB'
  refine ⟨p, hp, val_unique_of_sorted (n := max i j + 1) rfl _ fun w' => ?_⟩
  rw [Val_prim_of_vals' (Prim.sum i j) args hg _ (vals_cons hvA (vals_cons hvB vals_nil))
    (r := max i j + 1) rfl, clause_sum M.T i j _ _ (M.T.j i vA') (M.T.j j vB') w' rfl rfl rfl]
  constructor
  · rintro ⟨p', rfl, hp'⟩
    rw [hM.ext_of_iff hp' hp]
  · rintro rfl; exact ⟨p, rfl, hp⟩

/-- The data of the sum type of `inl`/`inr`/`sumRec`'s first two arguments. -/
theorem sum_data {n : ℕ} (i j : ℕ) (args : Fin (n + 2) → Term)
    (hAB : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.sum i j).argSort k)
    (h0 : PTy hM Γ (args 0) (univ i) (i + 1)) (h1 : PTy hM Γ (args 1) (univ j) (j + 1))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ (vA' : M.T.U i) (vB' : M.T.U j) (p : M.T.U (max i j)),
      (∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA')) ∧
      M.T.mem (M.T.j (i + 1) (M.T.j i vA')) (hM.univSet i) ∧
      (∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj (M.T.j j vB')) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j vB')) (hM.univSet j) ∧
      (∀ q, M.T.mem q p ↔ SumMem M.T i j (M.T.j i vA') (M.T.j j vB') q) ∧
      (∀ w, Val M.T Γ (prim (.sum i j) ![args 0, args 1]) η w ↔ w = M.T.inj (M.T.j (max i j) p)) := by
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB', hvB, hBU⟩ := type_arg_vals hM h1 hv
  obtain ⟨p, hp, hpval⟩ := sum_type_val hM i j ![args 0, args 1] hAB hvA hvB
  exact ⟨vA', vB', p, hvA, hAU, hvB, hBU, hp, hpval⟩

theorem case_sum (i j : ℕ) (args : Fin 2 → Term) (hok : (Prim.sum i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.sum i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.sum i j).argType m args k) ((Prim.sum i j).argSort k)) :
    PTy hM Γ (prim (.sum i j) args) (univ (max i j)) (max i j + 1) := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (univ j) (j + 1) := ih 1
  obtain ⟨vA', hvA, -⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB', hvB, -⟩ := type_arg_vals hM h1 hv
  obtain ⟨p, -, hval⟩ := sum_type_val hM i j args hg hvA hvB
  exact ⟨_, hval, mem_univSet_of_pos hM (by simp only [Prim.Ok] at hok; omega) p⟩

include hM in
/-- The value of `inl A B a`: the pair `⟨∅, lift a⟩`. -/
theorem inl_val (i j : ℕ) (args : Fin 3 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.inl i j).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (j + 1)} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {va : M.T.U i} (hva : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj va) {q : M.T.U (max i j)}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (hM.emptyAt (max i j)) (M.T.liftLE (le_max_left i j) va) q) :
    ∀ w, Val M.T Γ (prim (.inl i j) args) η w ↔ w = M.T.inj q := by
  refine val_unique_of_sorted (n := max i j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.inl i j) args hg _ (vals_cons hvA (vals_cons hvB (vals_cons hva vals_nil)))
    (r := max i j) rfl, clause_inl M.T i j _ _ va w' rfl rfl]
  constructor
  · rintro ⟨z, hz, hz'⟩
    rw [hM.eq_emptyAt hz] at hz'
    exact (hM.sortModel _).ordPair_unique hz' hq
  · rintro rfl; exact ⟨_, hM.emptyAt_spec _, hq⟩

include hM in
/-- The value of `inr A B b`: the pair `⟨{∅}, lift b⟩`. -/
theorem inr_val (i j : ℕ) (args : Fin 3 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.inr i j).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (j + 1)} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {vb : M.T.U j} (hvb : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vb) {q : M.T.U (max i j)}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (hM.singAt (hM.emptyAt (max i j)))
      (M.T.liftLE (le_max_right i j) vb) q) :
    ∀ w, Val M.T Γ (prim (.inr i j) args) η w ↔ w = M.T.inj q := by
  refine val_unique_of_sorted (n := max i j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.inr i j) args hg _ (vals_cons hvA (vals_cons hvB (vals_cons hvb vals_nil)))
    (r := max i j) rfl, clause_inr M.T i j _ _ vb w' rfl rfl]
  constructor
  · rintro ⟨z, ⟨e, he, hs⟩, hz'⟩
    rw [hM.eq_singAt hs, hM.eq_emptyAt he] at hz'
    exact (hM.sortModel _).ordPair_unique hz' hq
  · rintro rfl; exact ⟨_, ⟨_, hM.emptyAt_spec _, hM.singAt_spec _⟩, hq⟩

theorem case_inl (i j : ℕ) (args : Fin 3 → Term) (hok : (Prim.inl i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.inl i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.inl i j).argType m args k) ((Prim.inl i j).argSort k)) :
    PTy hM Γ (prim (.inl i j) args) (prim (.sum i j) ![args 0, args 1]) (max i j) := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (univ j) (j + 1) := ih 1
  have h2 : PTy hM Γ (args 2) (args 0) i := ih 2
  obtain ⟨vA', vB', p, hvA, -, hvB, -, hp, hpval⟩ := sum_data hM i j args (by prim_guard hg) h0 h1 hv
  obtain ⟨va, hva, ha⟩ := elem_arg_vals hM h2 hv hvA
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (hM.emptyAt (max i j))
    (M.T.liftLE (le_max_left i j) va)
  refine ⟨q, M.T.j (max i j) p, inl_val hM i j args hg hvA hvB hva hq, hpval,
    mem_univSet_of_pos hM (by simp only [Prim.Ok] at hok; omega) p, ?_⟩
  rw [hM.j_mem_iff, hp]
  exact Or.inl ⟨va, (hM.j_mem_iff i va vA').2 ha, _, hM.emptyAt_spec _, hq⟩

theorem case_inr (i j : ℕ) (args : Fin 3 → Term) (hok : (Prim.inr i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.inr i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.inr i j).argType m args k) ((Prim.inr i j).argSort k)) :
    PTy hM Γ (prim (.inr i j) args) (prim (.sum i j) ![args 0, args 1]) (max i j) := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (univ j) (j + 1) := ih 1
  have h2 : PTy hM Γ (args 2) (args 1) j := ih 2
  obtain ⟨vA', vB', p, hvA, -, hvB, -, hp, hpval⟩ := sum_data hM i j args (by prim_guard hg) h0 h1 hv
  obtain ⟨vb, hvb, hb⟩ := elem_arg_vals hM h2 hv hvB
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (hM.singAt (hM.emptyAt (max i j)))
    (M.T.liftLE (le_max_right i j) vb)
  refine ⟨q, M.T.j (max i j) p, inr_val hM i j args hg hvA hvB hvb hq, hpval,
    mem_univSet_of_pos hM (by simp only [Prim.Ok] at hok; omega) p, ?_⟩
  rw [hM.j_mem_iff, hp]
  exact Or.inr ⟨vb, (hM.j_mem_iff j vb vB').2 hb, _, ⟨_, hM.emptyAt_spec _, hM.singAt_spec _⟩, hq⟩

include hM in
/-- The value of the type `C s` for `C : A + B → U_k` and `s : A + B`, as a set `j vCs'`. -/
theorem fam_app_val {i k : ℕ} {C s : Term} (hcC : C.cls Γ = max i (k + 1)) (hcs : s.cls Γ = i)
    {η : Env M.T m} {vC : M.T.U (max i (k + 1))} (hvC : ∀ w, Val M.T Γ C η w ↔ w = M.T.inj vC)
    (hfun : (M.T.sortStr (max i (k + 1))).IsFunction vC) {vs : M.T.U i}
    (hvs : ∀ w, Val M.T Γ s η w ↔ w = M.T.inj vs) {vCs' : M.T.U k}
    (hCs : (M.T.sortStr (max i (k + 1))).FunApp vC (M.T.liftLE (le_max_left _ _) vs)
      (M.T.liftLE (le_max_right _ _) (M.T.j k vCs'))) :
    ∀ w, Val M.T Γ (app .data (k + 1) C s) η w ↔ w = M.T.inj (M.T.j k vCs') :=
  app_data_val hM hcC hcs (le_max_right _ _) (le_max_left _ _) hvC hvs hfun hCs

theorem case_sumRec (i j k : ℕ) (args : Fin 6 → Term) (hok : (Prim.sumRec i j k).Ok)
    (hg : ∀ l, (args l).cls Γ = (Prim.sumRec i j k).argSort l)
    (ih : ∀ l, PTy hM Γ (args l) ((Prim.sumRec i j k).argType m args l) ((Prim.sumRec i j k).argSort l)) :
    PTy hM Γ (prim (.sumRec i j k) args) (app .data (k + 1) (args 2) (args 5)) k := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (univ j) (j + 1) := ih 1
  have h2 : PTy hM Γ (args 2) (pi .data (max i j) (k + 1) (prim (.sum i j) ![args 0, args 1]) (univ k))
    (max (max i j) (k + 1)) := ih 2
  have h3 : PTy hM Γ (args 3) (pi .data i k (args 0) (app .data (k + 1) (Term.shift m 1 (args 2))
    (prim (.inl i j) ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m]))) (max i k) := ih 3
  have h4 : PTy hM Γ (args 4) (pi .data j k (args 1) (app .data (k + 1) (Term.shift m 1 (args 2))
    (prim (.inr i j) ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m]))) (max j k) := ih 4
  have h5 : PTy hM Γ (args 5) (prim (.sum i j) ![args 0, args 1]) (max i j) := ih 5
  obtain ⟨vA', vB', p, hvA, -, hvB, -, hp, hpval⟩ := sum_data hM i j args (by prim_guard hg) h0 h1 hv
  -- the family `C`
  obtain ⟨vC, hvC, hCfun, hC, hCval⟩ := fam_of_pty hM h2 hv rfl hpval
  -- the two branches
  obtain ⟨vf, hvf, hffun, hf⟩ := pi_data_of_pty hM h3 hv (hg 0) rfl hvA
  obtain ⟨vg, hvg, hgfun, hgv⟩ := pi_data_of_pty hM h4 hv (hg 1) rfl hvB
  -- the scrutinee
  obtain ⟨vs, hvs, hs⟩ := elem_arg_vals hM h5 hv hpval
  have hs' : M.T.mem (M.T.j (max i j) vs) (M.T.j (max i j) p) := (hM.j_mem_iff _ _ _).2 hs
  have hsum := (hp vs).1 hs
  -- the value of `C s`
  obtain ⟨vCs', hCs⟩ := hC vs hs'
  have hCsval := fam_app_val hM (i := max i j) (hg 2) (hg 5) hvC hCfun hvs hCs
  have hCsU : M.T.mem (M.T.j (k + 1) (M.T.j k vCs')) (hM.univSet k) := by
    obtain ⟨vBa', heq, hU⟩ := hCval vs hs' _ hCs
    have e : vBa' = vCs' := hM.j_injective k _ _ (hM.liftLE_injective _ heq).symm
    subst e; exact hU
  -- the values of the primitive
  have hvals : ∀ w', Val M.T Γ (prim (.sumRec i j k) args) η (M.T.inj w') ↔
      (∃ x : M.T.U i, ∃ z, (M.T.sortStr (max i j)).IsEmptySet z ∧
        (M.T.sortStr (max i j)).IsOrdPair z (M.T.liftLE (le_max_left i j) x) vs ∧
        (M.T.sortStr (max i k)).FunApp vf (M.T.liftLE (le_max_left i k) x) (M.T.liftLE (le_max_right i k) w')) ∨
      (∃ y : M.T.U j, ∃ z, (∃ e, (M.T.sortStr (max i j)).IsEmptySet e ∧ (M.T.sortStr (max i j)).IsSingleton e z) ∧
        (M.T.sortStr (max i j)).IsOrdPair z (M.T.liftLE (le_max_right i j) y) vs ∧
        (M.T.sortStr (max j k)).FunApp vg (M.T.liftLE (le_max_left j k) y) (M.T.liftLE (le_max_right j k) w')) := by
    intro w'
    rw [Val_prim_of_vals' (Prim.sumRec i j k) args hg _
      (vals_cons hvA (vals_cons hvB (vals_cons hvC (vals_cons hvf (vals_cons hvg (vals_cons hvs vals_nil))))))
      (r := k) rfl, clause_sumRec M.T i j k _ _ vf vg vs w' rfl rfl rfl rfl]
  rcases hsum with ⟨a, ha, z, hz, hq⟩ | ⟨b, hb, z, ⟨e, he, hsz⟩, hq⟩
  · -- `s = inl a`
    obtain ⟨⟨v, hv'⟩, vBody, hvBody, -, hrng⟩ := hf a ha
    obtain ⟨b, hb, rfl⟩ := hrng v hv'
    -- the body's value is `C (inl a)`, i.e. `j vCs'`
    have hgi : ∀ l, (![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] l).cls (Γ.snoc (args 0) i) =
        (Prim.inl i j).argSort l := by
      intro l; fin_cases l
      · show (Term.shift m 1 (args 0)).cls _ = i + 1
        rw [Term.cls_shift1]; exact hg 0
      · show (Term.shift m 1 (args 1)).cls _ = j + 1
        rw [Term.cls_shift1]; exact hg 1
      · show (Γ.snoc (args 0) i).lev m = i
        rw [Ctx.lev_snoc_self]
    have hshA : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 0)) (Fin.snoc η (M.T.inj a)) w ↔
        w = M.T.inj (M.T.j i vA') := fun w => by rw [Val_shift1]; exact hvA w
    have hshB : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj a)) w ↔
        w = M.T.inj (M.T.j j vB') := fun w => by rw [Val_shift1]; exact hvB w
    have hshC : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 2)) (Fin.snoc η (M.T.inj a)) w ↔
        w = M.T.inj vC := fun w => by rw [Val_shift1]; exact hvC w
    have hq0 : (M.T.sortStr (max i j)).IsOrdPair (hM.emptyAt (max i j)) (M.T.liftLE (le_max_left i j) a) vs := by
      rwa [hM.eq_emptyAt hz] at hq
    have hinl := inl_val hM i j ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] hgi
      (η := Fin.snoc η (M.T.inj a)) hshA hshB (Val_var_last Γ (args 0) i η a) hq0
    have hbody := fam_app_val hM (i := max i j) (by rw [Term.cls_shift1]; exact hg 2) rfl
      hshC hCfun hinl hCs
    have e : vBody = M.T.j k vCs' := Sorted.inj_injective M.T.U ((hbody _).1 ((hvBody _).2 rfl))
    subst e
    refine ⟨b, M.T.j k vCs', ?_, hCsval, hCsU, hb⟩
    refine val_unique_of_sorted (n := k) rfl _ fun w' => ?_
    rw [hvals]
    constructor
    · rintro (⟨x, z', hz', hq', happ⟩ | ⟨y, z', ⟨e', he', hs'⟩, hq', -⟩)
      · obtain ⟨-, hx⟩ := (hM.sortModel _).ordPair_inj hq' hq
        have ex : x = a := hM.liftLE_injective _ hx
        subst ex
        exact hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hffun happ hv')
      · exact absurd ((hM.sortModel _).ordPair_inj hq' hq).1 (tag_ne hM hz he' hs').symm
    · rintro rfl
      exact Or.inl ⟨a, z, hz, hq, hv'⟩
  · -- `s = inr b`
    obtain ⟨⟨v, hv'⟩, vBody, hvBody, -, hrng⟩ := hgv b hb
    obtain ⟨c, hc, rfl⟩ := hrng v hv'
    have hgi : ∀ l, (![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] l).cls (Γ.snoc (args 1) j) =
        (Prim.inr i j).argSort l := by
      intro l; fin_cases l
      · show (Term.shift m 1 (args 0)).cls _ = i + 1
        rw [Term.cls_shift1]; exact hg 0
      · show (Term.shift m 1 (args 1)).cls _ = j + 1
        rw [Term.cls_shift1]; exact hg 1
      · show (Γ.snoc (args 1) j).lev m = j
        rw [Ctx.lev_snoc_self]
    have hq' : (M.T.sortStr (max i j)).IsOrdPair (hM.singAt (hM.emptyAt (max i j)))
        (M.T.liftLE (le_max_right i j) b) vs := by
      rwa [hM.eq_singAt hsz, hM.eq_emptyAt he] at hq
    have hshA : ∀ w, Val M.T (Γ.snoc (args 1) j) (Term.shift m 1 (args 0)) (Fin.snoc η (M.T.inj b)) w ↔
        w = M.T.inj (M.T.j i vA') := fun w => by rw [Val_shift1]; exact hvA w
    have hshB : ∀ w, Val M.T (Γ.snoc (args 1) j) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj b)) w ↔
        w = M.T.inj (M.T.j j vB') := fun w => by rw [Val_shift1]; exact hvB w
    have hshC : ∀ w, Val M.T (Γ.snoc (args 1) j) (Term.shift m 1 (args 2)) (Fin.snoc η (M.T.inj b)) w ↔
        w = M.T.inj vC := fun w => by rw [Val_shift1]; exact hvC w
    have hinr := inr_val hM i j ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] hgi
      (η := Fin.snoc η (M.T.inj b)) hshA hshB (Val_var_last Γ (args 1) j η b) hq'
    have hbody := fam_app_val hM (i := max i j) (by rw [Term.cls_shift1]; exact hg 2) rfl
      hshC hCfun hinr hCs
    have e : vBody = M.T.j k vCs' := Sorted.inj_injective M.T.U ((hbody _).1 ((hvBody _).2 rfl))
    subst e
    refine ⟨c, M.T.j k vCs', ?_, hCsval, hCsU, hc⟩
    refine val_unique_of_sorted (n := k) rfl _ fun w' => ?_
    rw [hvals]
    constructor
    · rintro (⟨x, z', hz', hq'', -⟩ | ⟨y, z', ⟨e', he', hs'⟩, hq'', happ⟩)
      · exact absurd ((hM.sortModel _).ordPair_inj hq'' hq').1
          (tag_ne hM hz' (hM.emptyAt_spec _) (hM.singAt_spec _))
      · obtain ⟨-, hy⟩ := (hM.sortModel _).ordPair_inj hq'' hq'
        have ey : y = b := hM.liftLE_injective _ hy
        subst ey
        exact hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hgfun happ hv')
    · rintro rfl
      exact Or.inr ⟨b, _, ⟨_, hM.emptyAt_spec _, hM.singAt_spec _⟩, hq', hv'⟩

/-! ### The recursor of the natural numbers -/

/-- The value of `zero`, in any context. -/
theorem zero_val {m' : ℕ} (Γ' : Ctx m') (η' : Env M.T m') :
    ∀ w, Val M.T Γ' (prim .zero ![]) η' w ↔ w = M.T.inj (hM.emptyAt 1) := by
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Γ := Γ') (η := η') (Prim.zero) ![] (fun k => k.elim0) ![] vals_nil (r := 1) rfl,
    clause_zero M.T ![] _ w' rfl]
  exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 1⟩

include hM in
/-- The value of `succ t`, in any context. -/
theorem succ_val {m' : ℕ} (Γ' : Ctx m') (η' : Env M.T m') (args : Fin 1 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.succ).argSort k) {vn : M.T.U 1}
    (hvn : ∀ w, Val M.T Γ' (args 0) η' w ↔ w = M.T.inj vn) {sn : M.T.U 1}
    (hsn : (M.T.sortStr 1).IsSucc vn sn) :
    ∀ w, Val M.T Γ' (prim .succ args) η' w ↔ w = M.T.inj sn := by
  refine val_unique_of_sorted (n := 1) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.succ) args hg _ (vals_cons hvn vals_nil) (r := 1) rfl,
    clause_succ M.T _ _ vn w' rfl rfl]
  exact ⟨fun h => hM.succ_unique h hsn, fun h => h ▸ hsn⟩

include hM in
/-- The value of `C t` for `C : ℕ → U_j` and `t` a numeral `k` with `C(k) = j vCk'`. -/
theorem natFam_app_val {m' : ℕ} {Γ' : Ctx m'} {j : ℕ} {C t : Term} (hcC : C.cls Γ' = j + 1)
    (hct : t.cls Γ' = 1) {η' : Env M.T m'} {vC : M.T.U (j + 1)}
    (hvC : ∀ w, Val M.T Γ' C η' w ↔ w = M.T.inj vC) (hCfun : (M.T.sortStr (j + 1)).IsFunction vC)
    {k : M.T.U 1} (hvt : ∀ w, Val M.T Γ' t η' w ↔ w = M.T.inj k) {vCk' : M.T.U j}
    (hCk : (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) k) (M.T.j j vCk')) :
    ∀ w, Val M.T Γ' (app .data (j + 1) C t) η' w ↔ w = M.T.inj (M.T.j j vCk') :=
  app_data_val hM hcC hct (le_refl _) (by omega) hvC hvt hCfun (by rw [M.T.liftLE_self]; exact hCk)

/-- The data of `natRec`'s arguments: the family `C`, the values of `z`, `s`, `n`, and the
typing hypotheses of the recursion theorem. -/
theorem natRec_data (j : ℕ) (args : Fin 4 → Term) (hj : 1 ≤ j)
    (hg : ∀ k, (args k).cls Γ = (Prim.natRec j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.natRec j).argType m args k) ((Prim.natRec j).argSort k))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ (vC : M.T.U (j + 1)) (vz : M.T.U j) (vs : M.T.U (max 1 (max j j))) (vn : M.T.U 1),
      (∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vC) ∧ (M.T.sortStr (j + 1)).IsFunction vC ∧
      (∀ k : M.T.U 1, M.T.mem k hM.omegaSet → ∃ vCk' : M.T.U j,
        (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) k) (M.T.j j vCk') ∧
        M.T.mem (M.T.j (j + 1) (M.T.j j vCk')) (hM.univSet j)) ∧
      (∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vz) ∧ (∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vs) ∧
      (∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vn) ∧ M.T.mem vn hM.omegaSet ∧
      NatRecTyping hM hj vC vz vs := by
  have h0 : PTy hM Γ (args 0) (pi .data 1 (j + 1) (prim .nat ![]) (univ j)) (max 1 (j + 1)) := ih 0
  have h1 : PTy hM Γ (args 1) (app .data (j + 1) (args 0) (prim .zero ![])) j := ih 1
  have h2 : PTy hM Γ (args 2) (pi .data 1 (max j j) (prim .nat ![]) (pi .data j j
    (app .data (j + 1) (Term.shift m 1 (args 0)) (var m))
    (app .data (j + 1) (Term.shift m 2 (args 0)) (prim .succ ![var m])))) (max 1 (max j j)) := ih 2
  have h3 : PTy hM Γ (args 3) (prim .nat ![]) 1 := ih 3
  have hnat : ∀ w, Val M.T Γ (prim .nat ![]) η w ↔ w = M.T.inj (M.T.j 1 hM.omegaSet) := nat_type_val hM ![]
  -- the family `C : ℕ → U_j`
  obtain ⟨vC, hvC, hCfun, hC, hCval⟩ := fam_of_pty hM h0 hv rfl hnat
  have hC' : ∀ k : M.T.U 1, M.T.mem k hM.omegaSet → ∃ vCk' : M.T.U j,
      (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) k) (M.T.j j vCk') ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j vCk')) (hM.univSet j) := by
    intro k hk
    obtain ⟨vCk', h⟩ := hC k ((hM.j_mem_iff 1 _ _).2 hk)
    refine ⟨vCk', ?_, ?_⟩
    · rw [← M.T.liftLE_self (M.T.j j vCk')]; exact h
    · obtain ⟨vBa', heq, hU⟩ := hCval k ((hM.j_mem_iff 1 _ _).2 hk) _ h
      have e : vBa' = vCk' := hM.j_injective j _ _ (hM.liftLE_injective _ heq).symm
      subst e; exact hU
  have hcC : (args 0).cls Γ = j + 1 := hg 0
  -- `z : C 0`
  obtain ⟨vz, hvz, hzmem⟩ := PTy.term_val hM h1 hv
  obtain ⟨vC0', hC0, -⟩ := hC' (hM.emptyAt 1) hM.emptyAt_mem_omega
  have hz : M.T.mem (M.T.j j vz) (M.T.j j vC0') :=
    hzmem _ ((natFam_app_val hM hcC rfl hvC hCfun (zero_val hM Γ η) hC0 _).2 rfl)
  -- `s : Π (k : ℕ). C k → C (k + 1)`
  obtain ⟨vs, hvs, hsfun, hs⟩ := pi_data_of_pty hM h2 hv rfl rfl hnat
  -- `n : ℕ`
  obtain ⟨vn, hvn, hnmem⟩ := PTy.term_val hM h3 hv
  have hnω : M.T.mem vn hM.omegaSet := (hM.j_mem_iff 1 _ _).1 (hnmem _ ((hnat _).2 rfl))
  refine ⟨vC, vz, vs, vn, hvC, hCfun, hC', hvz, hvs, hvn, hnω, ?_⟩
  -- the typing hypotheses of the recursion theorem
  refine ⟨⟨M.T.j j vC0', hC0, hz⟩, hsfun, fun k hk k1 hk1 fk hfk => ?_⟩
  have hk' : M.T.mem (M.T.j 1 k) (M.T.j 1 hM.omegaSet) := (hM.j_mem_iff 1 _ _).2 hk
  obtain ⟨⟨v, hv'⟩, vB, hvB, -, hrng⟩ := hs k hk'
  obtain ⟨g, hgv, rfl⟩ := hrng v hv'
  refine ⟨g, hv', ?_⟩
  -- `C k` and `C (k + 1)`
  obtain ⟨vCk', hCk, -⟩ := hC' k hk
  obtain ⟨vCk1', hCk1, -⟩ := hC' k1 (hM.succ_mem_omega hk hk1)
  have hfk' : M.T.mem (M.T.j j fk) (M.T.j j vCk') := by
    obtain ⟨c, hc, hmem⟩ := hfk
    rw [(hM.sortModel (j + 1)).funApp_unique hCfun hc hCk] at hmem
    exact hmem
  -- the value of `C k` in the extended context
  have hshC : ∀ w, Val M.T (Γ.snoc (prim .nat ![]) 1) (Term.shift m 1 (args 0)) (Fin.snoc η (M.T.inj k)) w ↔
      w = M.T.inj vC := fun w => by rw [Val_shift1]; exact hvC w
  have hCkval := natFam_app_val hM (Γ' := Γ.snoc (prim .nat ![]) 1) (t := var m)
    (by rw [Term.cls_shift1]; exact hcC) (Ctx.lev_snoc_self Γ _ 1) hshC hCfun
    (Val_var_last Γ (prim .nat ![]) 1 η k) hCk
  -- `g` is a function from `C k` to `C (k + 1)`
  obtain ⟨hgfun, -, vB', hvB', -, hrng'⟩ := pi_data_elim hM (i := j) (j := j) rfl rfl ((hvB _).2 rfl) hgv
    ((hCkval _).2 rfl) hfk'
  obtain ⟨u, hu⟩ : ∃ u, (M.T.sortStr (max j j)).FunApp g (M.T.liftLE (le_max_left j j) fk) u :=
    (pi_data_elim hM (i := j) (j := j) rfl rfl ((hvB _).2 rfl) hgv ((hCkval _).2 rfl) hfk').2.1
  obtain ⟨r, hr, rfl⟩ := hrng' u hu
  refine ⟨hgfun, r, hu, M.T.j j vCk1', hCk1, ?_⟩
  -- the value of `C (k + 1)` in the doubly extended context
  have hsh2C : ∀ w, Val M.T ((Γ.snoc (prim .nat ![]) 1).snoc (app .data (j + 1) (Term.shift m 1 (args 0)) (var m)) j)
      (Term.shift m 2 (args 0)) (Fin.snoc (Fin.snoc η (M.T.inj k)) (M.T.inj fk)) w ↔ w = M.T.inj vC :=
    fun w => by rw [Val_shift2]; exact hvC w
  have hsucc := succ_val hM ((Γ.snoc (prim .nat ![]) 1).snoc (app .data (j + 1) (Term.shift m 1 (args 0)) (var m)) j)
    (Fin.snoc (Fin.snoc η (M.T.inj k)) (M.T.inj fk)) ![var m]
    (fun l => by
      fin_cases l
      show ((Γ.snoc (prim .nat ![]) 1).snoc _ j).lev m = 1
      rw [Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self])
    (Val_var_last2 Γ _ _ 1 j η k _) hk1
  have hCk1val := natFam_app_val hM (Γ' := (Γ.snoc (prim .nat ![]) 1).snoc _ j)
    (by rw [← Term.shift_two, Term.cls_shift1, Term.cls_shift1]; exact hcC) rfl hsh2C hCfun hsucc hCk1
  have e : vB' = M.T.j j vCk1' := Sorted.inj_injective M.T.U ((hCk1val _).1 ((hvB' _).2 rfl))
  subst e
  exact hr

/-- The value of `natRec C z s n`: the value at `lift n` of a recursion function for `n`. -/
theorem natRec_val (j : ℕ) (hj : 1 ≤ j) (args : Fin 4 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.natRec j).argSort k) {η : Env M.T m}
    {vC : M.T.U (j + 1)} {vz : M.T.U j} {vs : M.T.U (max 1 (max j j))} {vn : M.T.U 1}
    (hvC : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vC) (hvz : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vz)
    (hvs : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vs) (hvn : ∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vn)
    (hty : NatRecTyping hM hj vC vz vs) (hnω : M.T.mem vn hM.omegaSet) {d : M.T.U 1}
    (hd : (M.T.sortStr 1).IsSucc vn d) {F : M.T.U j} (hF : NatRecFun M.T j hj vz vs vn d F)
    (hInv : NatRecInv hj vC F d) {w : M.T.U j} (hw : (M.T.sortStr j).FunApp F (M.T.liftLE hj vn) w) :
    ∀ w', Val M.T Γ (prim (.natRec j) args) η w' ↔ w' = M.T.inj w := by
  have hnd : M.T.mem vn d := (hd vn).2 (Or.inr rfl)
  refine val_unique_of_sorted (n := j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.natRec j) args hg _
    (vals_cons hvC (vals_cons hvz (vals_cons hvs (vals_cons hvn vals_nil)))) (r := j) rfl,
    clause_natRec M.T j hj _ _ vz vs vn w' rfl rfl rfl rfl]
  constructor
  · rintro ⟨d', hd', F', hF', hw'⟩
    exact (natRec_agree hM hj vC vz vs hty hnω hd hd' (fun z hz => hz) hF hInv hF' vn hnd w w' hw hw').symm
  · rintro rfl
    exact ⟨d, hd, F, hF, hw⟩

theorem case_natRec (j : ℕ) (args : Fin 4 → Term) (hok : (Prim.natRec j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.natRec j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.natRec j).argType m args k) ((Prim.natRec j).argSort k)) :
    PTy hM Γ (prim (.natRec j) args) (app .data (j + 1) (args 0) (args 3)) j := by
  have hj : 1 ≤ j := hok
  refine PTy.mk hM fun η hv => ?_
  obtain ⟨vC, vz, vs, vn, hvC, hCfun, hC', hvz, hvs, hvn, hnω, hty⟩ := natRec_data hM j args hj hg ih hv
  -- the recursion function at `n`
  obtain ⟨d, hd, F, hF, hInv⟩ := natRec_exists hM hj vC vz vs hty vn hnω
  have hnd : M.T.mem vn d := (hd vn).2 (Or.inr rfl)
  obtain ⟨w, hw⟩ := (inDom_iff_mem_lift hM hj hF.2.1 vn).2 hnd
  -- the value of the result type `C n`
  obtain ⟨vCn', hCn, hCnU⟩ := hC' vn hnω
  have hCnval := natFam_app_val hM (hg 0) (hg 3) hvC hCfun hvn hCn
  refine ⟨w, M.T.j j vCn', natRec_val hM j hj args hg hvC hvz hvs hvn hty hnω hd hF hInv hw, hCnval, hCnU, ?_⟩
  obtain ⟨c, hc, hmem⟩ := hInv vn hnd w hw
  rw [(hM.sortModel (j + 1)).funApp_unique hCfun hc hCn] at hmem
  exact hmem

/-! ### Quotients -/

/-- A truth value containing `j ∅` is true. -/
theorem true_of_mem_tvSet {ψ : Prop} (h : M.T.mem (M.T.j 0 (hM.emptyAt 0)) (hM.tvSet ψ)) : ψ := by
  by_contra hn
  unfold IsTowerModel.tvSet at h
  rw [if_neg hn] at h
  exact hM.not_mem_emptyAt _ h

include hM in
/-- The set of classes, and the value of the type `Quot A R`. -/
theorem quot_type_val {m' : ℕ} {Γ' : Ctx m'} (i : ℕ) (args : Fin 2 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.quot i).argSort k)
    {η : Env M.T m'} {vA' : M.T.U i} (hvA : ∀ w, Val M.T Γ' (args 0) η w ↔ w = M.T.inj (M.T.j i vA'))
    {vR : M.T.U (max i (max i 1))} (hvR : ∀ w, Val M.T Γ' (args 1) η w ↔ w = M.T.inj vR) :
    ∃ Q : M.T.U i, (∀ c, M.T.mem c Q ↔ ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
        IsClassOf M.T i (M.T.j i vA') vR a c) ∧
      ∀ w, Val M.T Γ' (prim (.quot i) args) η w ↔ w = M.T.inj (M.T.j i Q) := by
  obtain ⟨Q, hQ⟩ := exists_quotSet hM vA' vR
  refine ⟨Q, hQ, val_unique_of_sorted (n := i + 1) rfl _ fun w' => ?_⟩
  rw [Val_prim_of_vals' (Prim.quot i) args hg _ (vals_cons hvA (vals_cons hvR vals_nil)) (r := i + 1) rfl,
    clause_quot M.T i _ _ (M.T.j i vA') vR w' rfl rfl rfl]
  constructor
  · rintro ⟨Q', rfl, hQ'⟩
    rw [hM.ext_of_iff hQ' hQ]
  · rintro rfl; exact ⟨Q, rfl, hQ⟩

include hM in
/-- The value of `Quot.mk A R a`: the class of `a`. -/
theorem quotMk_val {m' : ℕ} {Γ' : Ctx m'} (i : ℕ) (args : Fin 3 → Term)
    (hg : ∀ k, (args k).cls Γ' = (Prim.quotMk i).argSort k)
    {η : Env M.T m'} {vA' : M.T.U i} (hvA : ∀ w, Val M.T Γ' (args 0) η w ↔ w = M.T.inj (M.T.j i vA'))
    {vR : M.T.U (max i (max i 1))} (hvR : ∀ w, Val M.T Γ' (args 1) η w ↔ w = M.T.inj vR)
    {va : M.T.U i} (hva : ∀ w, Val M.T Γ' (args 2) η w ↔ w = M.T.inj va) {c : M.T.U i}
    (hc : IsClassOf M.T i (M.T.j i vA') vR va c) :
    ∀ w, Val M.T Γ' (prim (.quotMk i) args) η w ↔ w = M.T.inj c := by
  refine val_unique_of_sorted (n := i) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.quotMk i) args hg _ (vals_cons hvA (vals_cons hvR (vals_cons hva vals_nil)))
    (r := i) rfl, clause_quotMk M.T i _ _ (M.T.j i vA') vR va w' rfl rfl rfl rfl]
  exact ⟨fun h => isClassOf_unique hM vA' vR h hc, fun h => h ▸ hc⟩

/-- The data of a relation `R : A → A → U_0`: at each `a ∈ A`, `R a` is a function `g` whose value
at each `b ∈ A` is (the lift of) a truth value. -/
def RelData (i : ℕ) (vA' : M.T.U i) (vR : M.T.U (max i (max i 1))) : Prop :=
  (M.T.sortStr (max i (max i 1))).IsFunction vR ∧
  ∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') → ∃ g : M.T.U (max i 1),
    (M.T.sortStr (max i (max i 1))).FunApp vR (M.T.liftLE (le_max_left _ _) a)
      (M.T.liftLE (le_max_right _ _) g) ∧
    (M.T.sortStr (max i 1)).IsFunction g ∧
    ∀ b : M.T.U i, M.T.mem (M.T.j i b) (M.T.j i vA') → ∃ t : M.T.U 1,
      (M.T.sortStr (max i 1)).FunApp g (M.T.liftLE (le_max_left i 1) b) (M.T.liftLE (le_max_right i 1) t) ∧
      M.T.mem (M.T.j 1 t) (hM.univSet 0)

/-- The relation data of a relation argument. -/
theorem relData_of_pty {A R : Term} {i : ℕ}
    (h1 : PTy hM Γ R (pi .data i (max i 1) A (pi .data i 1 (Term.shift m 1 A) (univ 0))) (max i (max i 1)))
    {η : Env M.T m} (hv : Valid hM Γ η) (hcA : A.cls Γ = i + 1) {vA' : M.T.U i}
    (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj (M.T.j i vA')) :
    ∃ vR : M.T.U (max i (max i 1)), (∀ w, Val M.T Γ R η w ↔ w = M.T.inj vR) ∧ RelData hM i vA' vR := by
  obtain ⟨vR, hvR, hRfun, hR⟩ := pi_data_of_pty hM h1 hv hcA rfl hvA
  refine ⟨vR, hvR, hRfun, fun a ha => ?_⟩
  obtain ⟨⟨v, hv'⟩, vB, hvB, -, hrng⟩ := hR a ha
  obtain ⟨g, hg, rfl⟩ := hrng v hv'
  have hcA' : (Term.shift m 1 A).cls (Γ.snoc A i) = i + 1 := by rw [Term.cls_shift1]; exact hcA
  have hvA1 : Val M.T (Γ.snoc A i) (Term.shift m 1 A) (Fin.snoc η (M.T.inj a)) (M.T.inj (M.T.j i vA')) := by
    rw [Val_shift1]; exact (hvA _).2 rfl
  refine ⟨g, hv', ?_, fun b hb => ?_⟩
  · exact (pi_data_elim hM (i := i) (j := 1) hcA' rfl ((hvB _).2 rfl) hg hvA1 ha).1
  · obtain ⟨-, ⟨u, hu⟩, vU, hvU, -, hrng'⟩ := pi_data_elim hM (i := i) (j := 1) hcA' rfl ((hvB _).2 rfl) hg hvA1 hb
    obtain ⟨t, ht, rfl⟩ := hrng' u hu
    have e : vU = hM.univSet 0 := by
      have := (hvU _).2 rfl
      rw [Val_univ_iff hM] at this
      exact Sorted.inj_injective M.T.U this
    subst e
    exact ⟨t, hu, ht⟩

include hM in
/-- The value of `R a b`, in any context. -/
theorem rel_app_val {m' : ℕ} {Γ' : Ctx m'} {i : ℕ} {Rt at_ bt : Term} (hcR : Rt.cls Γ' = max i (max i 1))
    (hca : at_.cls Γ' = i) (hcb : bt.cls Γ' = i) {η : Env M.T m'} {vR : M.T.U (max i (max i 1))}
    (hvR : ∀ w, Val M.T Γ' Rt η w ↔ w = M.T.inj vR) (hRfun : (M.T.sortStr (max i (max i 1))).IsFunction vR)
    {a b : M.T.U i} (hva : ∀ w, Val M.T Γ' at_ η w ↔ w = M.T.inj a) (hvb : ∀ w, Val M.T Γ' bt η w ↔ w = M.T.inj b)
    {g : M.T.U (max i 1)} (hg : (M.T.sortStr (max i (max i 1))).FunApp vR (M.T.liftLE (le_max_left _ _) a)
      (M.T.liftLE (le_max_right _ _) g)) (hgfun : (M.T.sortStr (max i 1)).IsFunction g) {t : M.T.U 1}
    (ht : (M.T.sortStr (max i 1)).FunApp g (M.T.liftLE (le_max_left i 1) b) (M.T.liftLE (le_max_right i 1) t)) :
    ∀ w, Val M.T Γ' (app .data 1 (app .data (max i 1) Rt at_) bt) η w ↔ w = M.T.inj t := by
  have hinner := app_data_val hM hcR hca (le_max_right _ _) (le_max_left _ _) hvR hva hRfun hg
  exact app_data_val hM rfl hcb (le_max_right _ _) (le_max_left _ _) hinner hvb hgfun ht

/-- `RelHolds` in terms of the value `t` of `R a b`. -/
theorem relHolds_iff {i : ℕ} {vR : M.T.U (max i (max i 1))} (hRfun : (M.T.sortStr (max i (max i 1))).IsFunction vR)
    {a b : M.T.U i} {g : M.T.U (max i 1)} (hg : (M.T.sortStr (max i (max i 1))).FunApp vR
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) g))
    (hgfun : (M.T.sortStr (max i 1)).IsFunction g) {t : M.T.U 1}
    (ht : (M.T.sortStr (max i 1)).FunApp g (M.T.liftLE (le_max_left i 1) b) (M.T.liftLE (le_max_right i 1) t)) :
    RelHolds M.T i vR a b ↔ t = hM.singAt (hM.emptyAt 1) := by
  constructor
  · rintro ⟨t', ht', g', rfl, u, hu, v, rfl, e, he, hs⟩
    have e1 : g' = g := hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hRfun ht' hg)
    subst e1
    have e2 : v = t := hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hgfun hu ht)
    subst e2
    rw [hM.eq_singAt hs, hM.eq_emptyAt he]
  · intro h
    exact ⟨_, hg, g, rfl, _, ht, t, rfl, _, hM.emptyAt_spec 1, h ▸ hM.singAt_spec _⟩

theorem case_quot (i : ℕ) (args : Fin 2 → Term) (hok : (Prim.quot i).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.quot i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quot i).argType m args k) ((Prim.quot i).argSort k)) :
    PTy hM Γ (prim (.quot i) args) (univ i) (i + 1) := by
  refine PTy.mk_univ hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
    (max i (max i 1)) := ih 1
  obtain ⟨vA', hvA, -⟩ := type_arg_vals hM h0 hv
  obtain ⟨vR, hvR, -⟩ := PTy.term_val hM h1 hv
  obtain ⟨Q, -, hval⟩ := quot_type_val hM i args hg hvA hvR
  exact ⟨_, hval, mem_univSet_of_pos hM hok Q⟩

/-- The data of the quotient's first two arguments. -/
theorem quot_data {n : ℕ} (i : ℕ) (args : Fin (n + 2) → Term)
    (hAR : ∀ k : Fin 2, (![args 0, args 1] k).cls Γ = (Prim.quot i).argSort k)
    (h0 : PTy hM Γ (args 0) (univ i) (i + 1))
    (h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
      (max i (max i 1)))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ (vA' : M.T.U i) (vR : M.T.U (max i (max i 1))) (Q : M.T.U i),
      (∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA')) ∧
      M.T.mem (M.T.j (i + 1) (M.T.j i vA')) (hM.univSet i) ∧
      (∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vR) ∧ RelData hM i vA' vR ∧
      (∀ c, M.T.mem c Q ↔ ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧ IsClassOf M.T i (M.T.j i vA') vR a c) ∧
      (∀ w, Val M.T Γ (prim (.quot i) ![args 0, args 1]) η w ↔ w = M.T.inj (M.T.j i Q)) := by
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨vR, hvR, hRD⟩ := relData_of_pty hM h1 hv (hAR 0) hvA
  obtain ⟨Q, hQ, hQval⟩ := quot_type_val hM i ![args 0, args 1] hAR hvA hvR
  exact ⟨vA', vR, Q, hvA, hAU, hvR, hRD, hQ, hQval⟩

theorem case_quotMk (i : ℕ) (args : Fin 3 → Term) (hok : (Prim.quotMk i).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotMk i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quotMk i).argType m args k) ((Prim.quotMk i).argSort k)) :
    PTy hM Γ (prim (.quotMk i) args) (prim (.quot i) ![args 0, args 1]) i := by
  refine PTy.mk hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
    (max i (max i 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (args 0) i := ih 2
  obtain ⟨vA', vR, Q, hvA, -, hvR, -, hQ, hQval⟩ := quot_data hM i args (by prim_guard hg) h0 h1 hv
  obtain ⟨va, hva, ha⟩ := elem_arg_vals hM h2 hv hvA
  have ha' : M.T.mem (M.T.j i va) (M.T.j i vA') := (hM.j_mem_iff i va vA').2 ha
  obtain ⟨c, hc⟩ := exists_classSet hM vA' vR va
  refine ⟨c, M.T.j i Q, quotMk_val hM i args hg hvA hvR hva hc, hQval,
    mem_univSet_of_pos hM hok Q, ?_⟩
  rw [hM.j_mem_iff, hQ]
  exact ⟨va, ha', hc⟩

theorem case_quotSound (i : ℕ) (args : Fin 5 → Term) (hok : (Prim.quotSound i).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotSound i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quotSound i).argType m args k) ((Prim.quotSound i).argSort k)) :
    PTy hM Γ (prim (.quotSound i) args) (prim (.eq i) ![prim (.quot i) ![args 0, args 1],
      prim (.quotMk i) ![args 0, args 1, args 2], prim (.quotMk i) ![args 0, args 1, args 3]]) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
    (max i (max i 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (args 0) i := ih 2
  have h3 : PTy hM Γ (args 3) (args 0) i := ih 3
  have h4 : PTy hM Γ (args 4) (app .data 1 (app .data (max i 1) (args 1) (args 2)) (args 3)) 0 := ih 4
  obtain ⟨vA', vR, Q, hvA, -, hvR, ⟨hRfun, hRD⟩, hQ, hQval⟩ := quot_data hM i args (by prim_guard hg) h0 h1 hv
  obtain ⟨va, hva, ha⟩ := elem_arg_vals hM h2 hv hvA
  obtain ⟨vb, hvb, hb⟩ := elem_arg_vals hM h3 hv hvA
  have ha' : M.T.mem (M.T.j i va) (M.T.j i vA') := (hM.j_mem_iff i va vA').2 ha
  have hb' : M.T.mem (M.T.j i vb) (M.T.j i vA') := (hM.j_mem_iff i vb vA').2 hb
  obtain ⟨g, hRg, hgfun, hgb⟩ := hRD va ha'
  obtain ⟨t, ht, -⟩ := hgb vb hb'
  -- the proof `p : R a b` makes `R a b` true
  have hRab := rel_app_val hM (hg 1) (hg 2) (hg 3) hvR hRfun
    hva hvb hRg hgfun ht
  obtain ⟨htv, hvp⟩ := proof_arg_vals hM h4 hv hRab
  have hR : RelHolds M.T i vR va vb := (relHolds_iff hM hRfun hRg hgfun ht).2 htv
  -- the classes coincide
  obtain ⟨ca, hca⟩ := exists_classSet hM vA' vR va
  have hcb : IsClassOf M.T i (M.T.j i vA') vR vb ca :=
    isClassOf_congr hM vA' vR (Eqv_of_relHolds vA' vR ha' hb' hR) hca
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.quotSound i) args hg _
      (vals_cons hvA (vals_cons hvR (vals_cons hva (vals_cons hvb (vals_cons hvp vals_nil))))) (r := 0) rfl,
      clause_quotSound M.T i _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · have hmkA := quotMk_val hM i ![args 0, args 1, args 2] (by prim_guard hg) hvA hvR hva hca
    have hmkB := quotMk_val hM i ![args 0, args 1, args 3] (by prim_guard hg) hvA hvR hvb hcb
    intro w
    rw [eq_type_val hM i ![prim (.quot i) ![args 0, args 1], prim (.quotMk i) ![args 0, args 1, args 2],
      prim (.quotMk i) ![args 0, args 1, args 3]] (fun k => by fin_cases k <;> rfl) hQval hmkA hmkB,
      tvSet_true hM rfl]

theorem case_quotInd (i : ℕ) (args : Fin 5 → Term) (hok : (Prim.quotInd i).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotInd i).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quotInd i).argType m args k) ((Prim.quotInd i).argSort k)) :
    PTy hM Γ (prim (.quotInd i) args) (app .data 1 (args 2) (args 4)) 0 := by
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
    (max i (max i 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (pi .data i 1 (prim (.quot i) ![args 0, args 1]) (univ 0)) (max i 1) := ih 2
  have h3 : PTy hM Γ (args 3) (pi .prop i 0 (args 0) (app .data 1 (Term.shift m 1 (args 2))
    (prim (.quotMk i) ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m]))) 0 := ih 3
  have h4 : PTy hM Γ (args 4) (prim (.quot i) ![args 0, args 1]) i := ih 4
  obtain ⟨vA', vR, Q, hvA, -, hvR, -, hQ, hQval⟩ := quot_data hM i args (by prim_guard hg) h0 h1 hv
  -- the predicate `P : Quot A R → U_0`
  obtain ⟨vP, hvP, hPfun, -⟩ := pi_data_of_pty hM h2 hv rfl rfl hQval
  -- the class `q = [a]`
  obtain ⟨vq, hvq, hq⟩ := elem_arg_vals hM h4 hv hQval
  obtain ⟨a, ha, hc⟩ := (hQ vq).1 hq
  -- the body of `h` at `a`: `P [a]` is true
  have hcB : (app .data 1 (Term.shift m 1 (args 2)) (prim (.quotMk i)
    ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m])).cls (Γ.snoc (args 0) i) = 1 := rfl
  obtain ⟨vB, hvB, hBU, hmem⟩ := pi_prop_of_pty hM h3 hv (hg 0) hcB hvA ha
  have hshP : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 2)) (Fin.snoc η (M.T.inj a)) w ↔
      w = M.T.inj vP := fun w => by rw [Val_shift1]; exact hvP w
  have hshA : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 0)) (Fin.snoc η (M.T.inj a)) w ↔
      w = M.T.inj (M.T.j i vA') := fun w => by rw [Val_shift1]; exact hvA w
  have hshR : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj a)) w ↔
      w = M.T.inj vR := fun w => by rw [Val_shift1]; exact hvR w
  have hgi : ∀ l, (![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] l).cls (Γ.snoc (args 0) i) =
      (Prim.quotMk i).argSort l := by
    intro l; fin_cases l
    · show (Term.shift m 1 (args 0)).cls _ = i + 1
      rw [Term.cls_shift1]; exact hg 0
    · show (Term.shift m 1 (args 1)).cls _ = max i (max i 1)
      rw [Term.cls_shift1]; exact hg 1
    · show (Γ.snoc (args 0) i).lev m = i
      rw [Ctx.lev_snoc_self]
  have hmk := quotMk_val hM i ![Term.shift m 1 (args 0), Term.shift m 1 (args 1), var m] hgi hshA hshR
    (Val_var_last Γ (args 0) i η a) hc
  have hbody := (Val_app_data_of_vals (Γ := Γ.snoc (args 0) i) (k := i)
    (by rw [Term.cls_shift1]; exact hg 2)
    rfl (le_max_right i 1) (le_max_left i 1) hshP hmk vB).1 ((hvB _).2 rfl)
  have hBtrue : vB = hM.singAt (hM.emptyAt 1) := tv_true_of_mem hM hBU hmem
  subst hBtrue
  obtain ⟨vh, hvh, -⟩ := PTy.term_val hM h3 hv
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.quotInd i) args hg _
      (vals_cons hvA (vals_cons hvR (vals_cons hvP (vals_cons hvh (vals_cons hvq vals_nil))))) (r := 0) rfl,
      clause_quotInd M.T i _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · exact app_data_val hM (hg 2) (hg 4) (le_max_right i 1) (le_max_left i 1)
      hvP hvq hPfun hbody

/-- The data of `quotLift`'s arguments: the carrier, relation and set of classes, the codomain,
the function `f` (with its values at elements and its respect of `R`), and the class `q`. -/
theorem quotLift_data (i j : ℕ) (args : Fin 6 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotLift i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quotLift i j).argType m args k) ((Prim.quotLift i j).argSort k))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ (vA' : M.T.U i) (vR : M.T.U (max i (max i 1))) (Q : M.T.U i) (vB' : M.T.U j) (vf : M.T.U (max i j))
      (vh : M.T.U 0) (vq : M.T.U i),
      (∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA')) ∧
      (∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vR) ∧ RelData hM i vA' vR ∧
      (∀ c, M.T.mem c Q ↔ ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧ IsClassOf M.T i (M.T.j i vA') vR a c) ∧
      (∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj (M.T.j j vB')) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j vB')) (hM.univSet j) ∧
      (∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vf) ∧ (M.T.sortStr (max i j)).IsFunction vf ∧
      (∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') → ∃ b : M.T.U j,
        (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) ∧
        M.T.mem (M.T.j j b) (M.T.j j vB')) ∧
      (∀ a b, M.T.mem a vA' → M.T.mem b vA' → RelHolds M.T i vR a b →
        ∀ u v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) u →
          (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) b) v → u = v) ∧
      (∀ w, Val M.T Γ (args 4) η w ↔ w = M.T.inj vh) ∧
      (∀ w, Val M.T Γ (args 5) η w ↔ w = M.T.inj vq) ∧ M.T.mem vq Q := by
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (max i 1) (args 0) (pi .data i 1 (Term.shift m 1 (args 0)) (univ 0)))
    (max i (max i 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (univ j) (j + 1) := ih 2
  have h3 : PTy hM Γ (args 3) (pi .data i j (args 0) (Term.shift m 1 (args 2))) (max i j) := ih 3
  have h4 : PTy hM Γ (args 4) (pi .prop i 0 (args 0) (pi .prop i 0 (Term.shift m 1 (args 0)) (pi .prop 0 0
    (app .data 1 (app .data (max i 1) (Term.shift m 2 (args 1)) (var m)) (var (m + 1)))
    (prim (.eq j) ![Term.shift m 3 (args 2), app .data j (Term.shift m 3 (args 3)) (var m),
      app .data j (Term.shift m 3 (args 3)) (var (m + 1))])))) 0 := ih 4
  have h5 : PTy hM Γ (args 5) (prim (.quot i) ![args 0, args 1]) i := ih 5
  obtain ⟨vA', vR, Q, hvA, -, hvR, ⟨hRfun, hRD⟩, hQ, hQval⟩ := quot_data hM i args (by prim_guard hg) h0 h1 hv
  obtain ⟨vB', hvB, hBU⟩ := type_arg_vals hM h2 hv
  -- the function `f : A → B`
  have hcB1 : (Term.shift m 1 (args 2)).cls (Γ.snoc (args 0) i) = j + 1 := by
    rw [Term.cls_shift1]; exact hg 2
  obtain ⟨vf, hvf, hffun, hf⟩ := pi_data_of_pty hM h3 hv (hg 0) hcB1 hvA
  have hf' : ∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') →
      ∃ b : M.T.U j, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) ∧
        M.T.mem (M.T.j j b) (M.T.j j vB') := by
    intro a ha
    obtain ⟨⟨v, hv'⟩, vBa, hvBa, -, hrng⟩ := hf a ha
    obtain ⟨b, hb, rfl⟩ := hrng v hv'
    have e : vBa = M.T.j j vB' := by
      have := (hvBa _).2 rfl
      rw [Val_shift1, hvB] at this
      exact Sorted.inj_injective M.T.U this
    subst e
    exact ⟨b, hv', hb⟩
  -- `f` respects `R`
  have hresp : ∀ a b, M.T.mem a vA' → M.T.mem b vA' → RelHolds M.T i vR a b →
      ∀ u v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) u →
        (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) b) v → u = v := by
    intro a b ha hb hR u v hu hv'
    have ha' : M.T.mem (M.T.j i a) (M.T.j i vA') := (hM.j_mem_iff i a vA').2 ha
    have hb' : M.T.mem (M.T.j i b) (M.T.j i vA') := (hM.j_mem_iff i b vA').2 hb
    obtain ⟨fa, hfa, -⟩ := hf' a ha'
    obtain ⟨fb, hfb, -⟩ := hf' b hb'
    have eu : u = M.T.liftLE (le_max_right i j) fa := (hM.sortModel _).funApp_unique hffun hu hfa
    have ev : v = M.T.liftLE (le_max_right i j) fb := (hM.sortModel _).funApp_unique hffun hv' hfb
    subst eu; subst ev
    -- the value `t` of `R a b` is `{∅}`
    obtain ⟨g, hRg, hgfun, hgb⟩ := hRD a ha'
    obtain ⟨t, ht, -⟩ := hgb b hb'
    have htv : t = hM.singAt (hM.emptyAt 1) := (relHolds_iff hM hRfun hRg hgfun ht).1 hR
    subst htv
    -- unfold the three product layers of `h`'s type
    obtain ⟨vh, vPi, -, hvPi, -, hmem⟩ := PTy.vals hM h4 hv
    -- layer 1: at `a`
    obtain ⟨vB1, hvB1, -, hmem1⟩ := pi_prop_elim hM (hg 0) rfl ((hvPi _).2 rfl) hmem
      ((hvA _).2 rfl) ha'
    -- layer 2: at `b`
    have hcA1 : (Term.shift m 1 (args 0)).cls (Γ.snoc (args 0) i) = i + 1 := by
      rw [Term.cls_shift1]; exact hg 0
    have hvA1 : Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 0)) (Fin.snoc η (M.T.inj a))
        (M.T.inj (M.T.j i vA')) := by rw [Val_shift1]; exact (hvA _).2 rfl
    obtain ⟨vB2, hvB2, -, hmem2⟩ := pi_prop_elim hM hcA1 rfl ((hvB1 _).2 rfl) hmem1 hvA1 hb'
    -- layer 3: at a proof of `R a b`
    have hshR : ∀ w, Val M.T ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) (Term.shift m 2 (args 1))
        (Fin.snoc (Fin.snoc η (M.T.inj a)) (M.T.inj b)) w ↔ w = M.T.inj vR :=
      fun w => by rw [Val_shift2]; exact hvR w
    have hcR2 : (Term.shift m 2 (args 1)).cls ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) =
        max i (max i 1) := by
      rw [← Term.shift_two, Term.cls_shift1, Term.cls_shift1]; exact hg 1
    have hca2 : (var m).cls ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) = i := by
      show ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i).lev m = i
      rw [Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self]
    have hcb2 : (var (m + 1)).cls ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i) = i := by
      show ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i).lev (m + 1) = i
      rw [Ctx.lev_snoc_self]
    have hP := rel_app_val hM hcR2 hca2 hcb2 hshR hRfun (Val_var_last2 Γ _ _ i i η a _)
      (Val_var_last (Γ.snoc (args 0) i) _ i _ b) hRg hgfun ht
    obtain ⟨vB3, hvB3, -, hmem3⟩ := pi_prop_elim hM (i := 0) rfl rfl ((hvB2 _).2 rfl) hmem2 ((hP _).2 rfl)
      (mem_j_emptyAt_singAt hM)
    -- the body: `f a = f b`
    set Γ3 := ((Γ.snoc (args 0) i).snoc (Term.shift m 1 (args 0)) i).snoc
      (app .data 1 (app .data (max i 1) (Term.shift m 2 (args 1)) (var m)) (var (m + 1))) 0 with hΓ3
    set η3 : Env M.T (m + 3) := Fin.snoc (Fin.snoc (Fin.snoc η (M.T.inj a)) (M.T.inj b)) (M.T.inj (hM.emptyAt 0))
      with hη3
    have hcf3 : (Term.shift m 3 (args 3)).cls Γ3 = max i j := by
      rw [← Term.shift_three, Term.cls_shift1, ← Term.shift_two, Term.cls_shift1, Term.cls_shift1]
      exact hg 3
    have hcB3 : (Term.shift m 3 (args 2)).cls Γ3 = j + 1 := by
      rw [← Term.shift_three, Term.cls_shift1, ← Term.shift_two, Term.cls_shift1, Term.cls_shift1]
      exact hg 2
    have hca3 : (var m).cls Γ3 = i := by
      show Γ3.lev m = i
      rw [Ctx.lev_snoc_lt _ _ _ (by omega), Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self m), Ctx.lev_snoc_self]
    have hcb3 : (var (m + 1)).cls Γ3 = i := by
      show Γ3.lev (m + 1) = i
      rw [Ctx.lev_snoc_lt _ _ _ (Nat.lt_succ_self _), Ctx.lev_snoc_self]
    have hshf : ∀ w, Val M.T Γ3 (Term.shift m 3 (args 3)) η3 w ↔ w = M.T.inj vf :=
      fun w => by rw [Val_shift3]; exact hvf w
    have hshB : ∀ w, Val M.T Γ3 (Term.shift m 3 (args 2)) η3 w ↔ w = M.T.inj (M.T.j j vB') :=
      fun w => by rw [Val_shift3]; exact hvB w
    have hva3 : ∀ w, Val M.T Γ3 (var m) η3 w ↔ w = M.T.inj a := Val_var_last3 Γ _ _ _ i i 0 η a _ _
    have hvb3 : ∀ w, Val M.T Γ3 (var (m + 1)) η3 w ↔ w = M.T.inj b :=
      Val_var_last2 (Γ.snoc (args 0) i) _ _ i 0 (Fin.snoc η (M.T.inj a)) b _
    have hfa3 := app_data_val hM hcf3 hca3 (le_max_right i j) (le_max_left i j) hshf hva3 hffun hfa
    have hfb3 := app_data_val hM hcf3 hcb3 (le_max_right i j) (le_max_left i j) hshf hvb3 hffun hfb
    have hgi : ∀ l, (![Term.shift m 3 (args 2), app .data j (Term.shift m 3 (args 3)) (var m),
        app .data j (Term.shift m 3 (args 3)) (var (m + 1))] l).cls Γ3 = (Prim.eq j).argSort l := by
      intro l; fin_cases l
      · exact hcB3
      · rfl
      · rfl
    have heq := eq_type_val hM j _ hgi hshB hfa3 hfb3
    have e : vB3 = hM.tvSet (fa = fb) := Sorted.inj_injective M.T.U ((heq _).1 ((hvB3 _).2 rfl))
    subst e
    rw [true_of_mem_tvSet hM hmem3]
  obtain ⟨vq, hvq, hq⟩ := elem_arg_vals hM h5 hv hQval
  obtain ⟨vh, hvh, -⟩ := PTy.term_val hM h4 hv
  exact ⟨vA', vR, Q, vB', vf, vh, vq, hvA, hvR, ⟨hRfun, hRD⟩, hQ, hvB, hBU, hvf, hffun, hf', hresp, hvh, hvq, hq⟩

include hM in
/-- The value of `quotLift A R B f h q` for `q = [a₀]`: the value of `f` at `a₀`. -/
theorem quotLift_val (i j : ℕ) (args : Fin 6 → Term)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotLift i j).argSort k) {η : Env M.T m}
    {vA' : M.T.U i} {vR : M.T.U (max i (max i 1))} {vB' : M.T.U j} {vf : M.T.U (max i j)} {vh : M.T.U 0}
    {vq : M.T.U i}
    (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj (M.T.j i vA'))
    (hvR : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vR)
    (hvB : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj (M.T.j j vB'))
    (hvf : ∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vf) (hffun : (M.T.sortStr (max i j)).IsFunction vf)
    (hf' : ∀ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') → ∃ b : M.T.U j,
      (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) ∧
      M.T.mem (M.T.j j b) (M.T.j j vB'))
    (hresp : ∀ a b, M.T.mem a vA' → M.T.mem b vA' → RelHolds M.T i vR a b →
      ∀ u v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a) u →
        (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) b) v → u = v)
    (hvh : ∀ w, Val M.T Γ (args 4) η w ↔ w = M.T.inj vh)
    (hvq : ∀ w, Val M.T Γ (args 5) η w ↔ w = M.T.inj vq) {a₀ : M.T.U i}
    (ha₀ : M.T.mem (M.T.j i a₀) (M.T.j i vA')) (hc₀ : IsClassOf M.T i (M.T.j i vA') vR a₀ vq) {fa₀ : M.T.U j}
    (hfa₀ : (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a₀) (M.T.liftLE (le_max_right i j) fa₀)) :
    ∀ w, Val M.T Γ (prim (.quotLift i j) args) η w ↔ w = M.T.inj fa₀ := by
  -- the kernel of `f` is an equivalence relation containing `R`
  obtain ⟨E, hE⟩ := exists_kernelSet hM vA' (j := j) vf
  have hdom : ∀ a, M.T.mem a vA' → (M.T.sortStr (max i j)).InDom vf (M.T.liftLE (le_max_left i j) a) := by
    intro a ha
    obtain ⟨b, hb, -⟩ := hf' a ((hM.j_mem_iff i a vA').2 ha)
    exact ⟨_, hb⟩
  have hEquiv := kernel_equivRelOn hM vA' vR vf E hE hffun hdom hresp
  refine val_unique_of_sorted (n := j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.quotLift i j) args hg _
    (vals_cons hvA (vals_cons hvR (vals_cons hvB (vals_cons hvf (vals_cons hvh (vals_cons hvq vals_nil))))))
    (r := j) rfl, clause_quotLift M.T i j _ _ vf vq w' rfl rfl rfl]
  constructor
  · rintro ⟨a, ha, hw⟩
    -- `a ~ a₀`, so `f a = f a₀`
    have heqv : Eqv M.T i (M.T.j i vA') vR a₀ a :=
      eqv_of_mem_classOf vA' vR hc₀ (mem_classOf_self vA' vR ha₀ hc₀) ha
    obtain ⟨p, hp, hpE⟩ := heqv E hEquiv
    obtain ⟨-, a', b', hab, u, hu, hu'⟩ := (hE p).1 hpE
    obtain ⟨rfl, rfl⟩ := (hM.sortModel i).ordPair_inj hab hp
    have e1 := (hM.sortModel _).funApp_unique hffun hu hfa₀
    have e2 := (hM.sortModel _).funApp_unique hffun hu' hw
    exact hM.liftLE_injective _ (e2.symm.trans e1)
  · rintro rfl
    exact ⟨a₀, mem_classOf_self vA' vR ha₀ hc₀, hfa₀⟩

theorem case_quotLift (i j : ℕ) (args : Fin 6 → Term) (hok : (Prim.quotLift i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.quotLift i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.quotLift i j).argType m args k) ((Prim.quotLift i j).argSort k)) :
    PTy hM Γ (prim (.quotLift i j) args) (args 2) j := by
  refine PTy.mk hM fun η hv => ?_
  obtain ⟨vA', vR, Q, vB', vf, vh, vq, hvA, hvR, -, hQ, hvB, hBU, hvf, hffun, hf', hresp, hvh, hvq, hq⟩ :=
    quotLift_data hM i j args hg ih hv
  -- the class `q = [a₀]`
  obtain ⟨a₀, ha₀, hc₀⟩ := (hQ vq).1 hq
  obtain ⟨fa₀, hfa₀, hfa₀B⟩ := hf' a₀ ha₀
  exact ⟨fa₀, M.T.j j vB', quotLift_val hM i j args hg hvA hvR hvB hvf hffun hf' hresp hvh hvq ha₀ hc₀ hfa₀,
    hvB, hBU, hfa₀B⟩

/-! ### Choice -/

include hM in
/-- The value of a data product, given the family of values of its body. -/
theorem pi_data_type_val {i j : ℕ} {A B : Term} {η : Env M.T m} {vA' : M.T.U i}
    (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj (M.T.j i vA')) {F : M.T.U i → M.T.U j}
    (hF : ∀ a, M.T.mem a vA' →
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j (F a))) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j (F a))) (hM.univSet j))
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    ∃ p : M.T.U (max i j), (∀ f, M.T.mem f p ↔ IsPiFun M.T Γ i j A B η (M.T.j i vA') f) ∧
      ∀ w, Val M.T Γ (pi .data i j A B) η w ↔ w = M.T.inj (M.T.j (max i j) p) := by
  have hF' := family_iff hM hF
  obtain ⟨p, hp⟩ := exists_piSet hM η vA' F hF' hcB
  have hfam : FamOk M.T Γ i j A B η := by
    refine ⟨M.T.j i vA', (hvA _).2 rfl, fun vA₁ h => Sorted.inj_injective M.T.U ((hvA _).1 h),
      fun a ha => ?_⟩
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    refine ⟨M.T.j j (F a), (hF' a ha' _).2 rfl, fun vB' h => (hF' a ha' vB').1 h,
      hM.univSet j, (hM.isUnivSet_iff j _).2 rfl, (hF a ha').2⟩
  refine ⟨p, hp, fun w => ?_⟩
  constructor
  · intro hw
    have hs : w.1 = max i j + 1 := hw.sort
    obtain ⟨w', rfl⟩ := elSort M.T w hs
    rw [Val_pi_data M.T hcA hcB] at hw
    obtain ⟨-, vA₁, hvA₁, p₁, rfl, hp₁⟩ := hw
    have e := Sorted.inj_injective M.T.U ((hvA _).1 hvA₁)
    subst e
    congr 2
    exact hM.ext_of_iff hp₁ hp
  · rintro rfl
    rw [Val_pi_data M.T hcA hcB]
    exact ⟨hfam, M.T.j i vA', (hvA _).2 rfl, p, rfl, hp⟩

theorem case_choice (i j : ℕ) (args : Fin 3 → Term) (hok : (Prim.choice i j).Ok)
    (hg : ∀ k, (args k).cls Γ = (Prim.choice i j).argSort k)
    (ih : ∀ k, PTy hM Γ (args k) ((Prim.choice i j).argType m args k) ((Prim.choice i j).argSort k)) :
    PTy hM Γ (prim (.choice i j) args) (prim (.trunc (max i j))
      ![pi .data i j (args 0) (app .data (j + 1) (Term.shift m 1 (args 1)) (var m))]) 0 := by
  have hj : 1 ≤ j := hok
  refine PTy.mk0 hM fun η hv => ?_
  have h0 : PTy hM Γ (args 0) (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ (args 1) (pi .data i (j + 1) (args 0) (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ (args 2) (pi .prop i 0 (args 0)
    (prim (.trunc j) ![app .data (j + 1) (Term.shift m 1 (args 1)) (var m)])) 0 := ih 2
  obtain ⟨vA', hvA, hAU⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB, hvB, hfun, hB, hval⟩ := fam_of_pty hM h1 hv (hg 0) hvA
  have hcA : (args 0).cls Γ = i + 1 := hg 0
  -- the values of the body `B x`
  have hBval : ∀ a : M.T.U i, M.T.mem a vA' → ∃ vBa : M.T.U (j + 1),
      (∀ w, Val M.T (Γ.snoc (args 0) i) (app .data (j + 1) (Term.shift m 1 (args 1)) (var m))
        (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj vBa) ∧
      M.T.mem (M.T.j (j + 1) vBa) (hM.univSet j) := by
    intro a ha
    have ha' : M.T.mem (M.T.j i a) (M.T.j i vA') := (hM.j_mem_iff i a vA').2 ha
    obtain ⟨vBa', hBa⟩ := hB a ha'
    obtain ⟨vBa'', heq, hU⟩ := hval a ha' _ hBa
    have e : vBa'' = vBa' := hM.j_injective j _ _ (hM.liftLE_injective _ heq).symm
    rw [e] at hU
    refine ⟨M.T.j j vBa', ?_, hU⟩
    have hshB : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj a)) w ↔
        w = M.T.inj vB := fun w => by rw [Val_shift1]; exact hvB w
    exact app_data_val hM (a := var m) (by rw [Term.cls_shift1]; exact hg 1)
      (Ctx.lev_snoc_self Γ _ i) (le_max_right _ _) (le_max_left _ _) hshB (Val_var_last Γ (args 0) i η a)
      hfun hBa
  obtain ⟨F, hF⟩ := family_of hM hBval
  -- the product and its set of functions
  obtain ⟨p, hp, hpval⟩ := pi_data_type_val hM hvA hF hcA rfl
  -- each `B a` is inhabited
  have hinh : ∀ a : M.T.U i, M.T.mem a vA' → ∃ b : M.T.U j, M.T.mem b (F a) := by
    intro a ha
    have ha' : M.T.mem (M.T.j i a) (M.T.j i vA') := (hM.j_mem_iff i a vA').2 ha
    obtain ⟨vT, hvT, -, hmem⟩ := pi_prop_of_pty hM h2 hv hcA rfl hvA ha'
    have htr := trunc_type_val hM j ![app .data (j + 1) (Term.shift m 1 (args 1)) (var m)]
      (fun k => by fin_cases k; rfl) (hF a ha).1
    have e : vT = hM.tvSet (∃ b : M.T.U j, M.T.mem (M.T.j j b) (M.T.j j (F a))) :=
      Sorted.inj_injective M.T.U ((htr _).1 ((hvT _).2 rfl))
    subst e
    obtain ⟨b, hb⟩ := true_of_mem_tvSet hM hmem
    exact ⟨b, (hM.j_mem_iff j b (F a)).1 hb⟩
  -- the Σ-set, and a choice function inside it
  have hB' : ∀ a, M.T.mem a vA' → ∃ vBa' : M.T.U j, (M.T.sortStr (max i (j + 1))).FunApp vB
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) (M.T.j j vBa')) :=
    fun a ha => hB a ((hM.j_mem_iff i a vA').2 ha)
  obtain ⟨s, hs⟩ := exists_sigmaSet hM vA' vB hfun hB'
  -- membership in the Σ-set, in terms of `F`
  have hs' : ∀ q, M.T.mem q s ↔ ∃ a, M.T.mem a vA' ∧ ∃ b, M.T.mem b (F a) ∧
      (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) q := by
    intro q
    rw [hs]
    constructor
    · rintro ⟨a, ha, v, hv', vBa, rfl, b, hb, hq⟩
      have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
      obtain ⟨vBa', hvBa'⟩ := hB' a ha'
      have e := hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hfun hv' hvBa')
      subst e
      -- `vBa' = F a`
      have hFa : M.T.j j (F a) = M.T.j j vBa' := by
        have h1' := (hF a ha').1
        have h2' : ∀ w, Val M.T (Γ.snoc (args 0) i) (app .data (j + 1) (Term.shift m 1 (args 1)) (var m))
            (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j vBa') := by
          have hshB : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj a)) w ↔
              w = M.T.inj vB := fun w => by rw [Val_shift1]; exact hvB w
          exact app_data_val hM (a := var m) (by rw [Term.cls_shift1]; exact hg 1)
            (Ctx.lev_snoc_self Γ _ i) (le_max_right _ _) (le_max_left _ _) hshB
            (Val_var_last Γ (args 0) i η a) hfun hvBa'
        exact Sorted.inj_injective M.T.U ((h2' _).1 ((h1' _).2 rfl))
      have e3 : F a = vBa' := hM.j_injective j _ _ hFa
      refine ⟨a, ha', b, ?_, hq⟩
      rw [e3]; exact (hM.j_mem_iff j b vBa').1 hb
    · rintro ⟨a, ha, b, hb, hq⟩
      obtain ⟨vBa', hvBa'⟩ := hB' a ha
      have hFa : M.T.j j (F a) = M.T.j j vBa' := by
        have h1' := (hF a ha).1
        have h2' : ∀ w, Val M.T (Γ.snoc (args 0) i) (app .data (j + 1) (Term.shift m 1 (args 1)) (var m))
            (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j vBa') := by
          have hshB : ∀ w, Val M.T (Γ.snoc (args 0) i) (Term.shift m 1 (args 1)) (Fin.snoc η (M.T.inj a)) w ↔
              w = M.T.inj vB := fun w => by rw [Val_shift1]; exact hvB w
          exact app_data_val hM (a := var m) (by rw [Term.cls_shift1]; exact hg 1)
            (Ctx.lev_snoc_self Γ _ i) (le_max_right _ _) (le_max_left _ _) hshB
            (Val_var_last Γ (args 0) i η a) hfun hvBa'
        exact Sorted.inj_injective M.T.U ((h2' _).1 ((h1' _).2 rfl))
      have e3 : F a = vBa' := hM.j_injective j _ _ hFa
      refine ⟨a, (hM.j_mem_iff i a vA').2 ha, _, hvBa', M.T.j j vBa', rfl, b, ?_, hq⟩
      rw [← e3]; exact (hM.j_mem_iff j b (F a)).2 hb
  obtain ⟨f, hffun, hfdom, hfs⟩ := exists_choiceFun hM s (M.T.liftLE (le_max_left i j) vA')
    (fun q hq => by
      obtain ⟨a, ha, b, -, hq⟩ := (hs' q).1 hq
      exact ⟨_, _, (hM.liftLE_mem_iff _ _ _).2 ha, hq⟩)
    (fun x hx => by
      obtain ⟨a, ha, rfl⟩ := hM.mem_liftLE_elim _ hx
      obtain ⟨b, hb⟩ := hinh a ha
      obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (M.T.liftLE (le_max_left i j) a)
        (M.T.liftLE (le_max_right i j) b)
      exact ⟨q, _, (hs' q).2 ⟨a, ha, b, hb, hq⟩, hq⟩)
  -- `f` is in the product
  have hfPi : IsPiFun M.T Γ i j (args 0) (app .data (j + 1) (Term.shift m 1 (args 1)) (var m)) η
      (M.T.j i vA') f := by
    refine ⟨hffun, fun u => ?_, fun a ha v hv' => ?_⟩
    · rw [hfdom, hM.mem_liftLE_iff]
      exact exists_congr fun a => and_congr (hM.j_mem_iff i a vA').symm eq_comm
    · obtain ⟨q, hq, hpair⟩ := hv'
      obtain ⟨a', ha', b, hb, hq'⟩ := (hs' q).1 (hfs q hq)
      obtain ⟨e1, e2⟩ := (hM.sortModel (max i j)).ordPair_inj hpair hq'
      have ea := hM.liftLE_injective (le_max_left i j) e1
      subst ea
      exact ⟨M.T.j j (F a), ((hF a ha').1 _).2 rfl, b, (hM.j_mem_iff j b (F a)).2 hb, e2⟩
  obtain ⟨vh, hvh, -⟩ := PTy.term_val hM h2 hv
  constructor
  · refine val_unique_of_sorted (n := 0) rfl _ fun w' => ?_
    rw [Val_prim_of_vals' (Prim.choice i j) args hg _
      (vals_cons hvA (vals_cons hvB (vals_cons hvh vals_nil))) (r := 0) rfl,
      clause_choice M.T i j _ _ w' rfl]
    exact ⟨fun h => hM.eq_emptyAt h, fun h => h ▸ hM.emptyAt_spec 0⟩
  · intro w
    rw [trunc_type_val hM (max i j) _ (fun k => by fin_cases k; rfl) hpval,
      tvSet_true hM ⟨f, (hM.j_mem_iff _ _ _).2 ((hp f).2 hfPi)⟩]

/-! ### The typing rule of the primitives -/

/-- Soundness of `Typed.prim`: every primitive case. -/
theorem case_prim {n : ℕ} (c : Prim n) (args : Fin n → Term) (hok : c.Ok)
    (hg : ∀ k, (args k).cls Γ = c.argSort k)
    (ih : ∀ k, PTy hM Γ (args k) (c.argType m args k) (c.argSort k)) :
    PTy hM Γ (prim c args) (c.resultType m args) c.level := by
  cases c with
  | false_ => exact case_false hM args hg
  | falseElim j => exact case_falseElim hM j args hg ih
  | eq i => exact case_eq hM i args hg ih
  | refl i => exact case_refl hM i args hg ih
  | eqRec i j => exact case_eqRec hM i j args hg ih
  | sigma i j => exact case_sigma hM i j args hok hg ih
  | pair i j => exact case_pair hM i j args hok hg ih
  | fst i j => exact case_fst hM i j args hg ih
  | snd i j => exact case_snd hM i j args hg ih
  | lift i d => exact case_lift hM i d args hg ih
  | up i d => exact case_up hM i d args hg ih
  | down i d => exact case_down hM i d args hg ih
  | trunc i => exact case_trunc hM i args hg ih
  | truncMk i => exact case_truncMk hM i args hg ih
  | truncRec i => exact case_truncRec hM i args hg ih
  | propext => exact case_propext hM args hg ih
  | dne => exact case_dne hM args hg ih
  | uchoice i => exact case_uchoice hM i args hg ih
  | choice i j => exact case_choice hM i j args hok hg ih
  | sum i j => exact case_sum hM i j args hok hg ih
  | inl i j => exact case_inl hM i j args hok hg ih
  | inr i j => exact case_inr hM i j args hok hg ih
  | sumRec i j k => exact case_sumRec hM i j k args hok hg ih
  | nat => exact case_nat hM args
  | zero => exact case_zero hM args
  | succ => exact case_succ hM args hg ih
  | natRec j => exact case_natRec hM j args hok hg ih
  | quot i => exact case_quot hM i args hok hg ih
  | quotMk i => exact case_quotMk hM i args hok hg ih
  | quotLift i j => exact case_quotLift hM i j args hok hg ih
  | quotSound i => exact case_quotSound hM i args hok hg ih
  | quotInd i => exact case_quotInd hM i args hok hg ih

end Cases

end SolidLean.Calc
