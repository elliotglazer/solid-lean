module

public import Solid.Calc.Sets
public import Solid.Calc.TyOk

/-!
# Soundness of the core calculus: motives and the core cases

In a model of `H`, every certified term has a unique value under every
valid environment, its type has a unique value lying in the universe of
its level, the value of the term lies in the value of its type, and
definitionally equal terms have the same values.  This file sets up the
motives (`Valid`, `PTy`, `PEq`) and proves the cases of the induction for
the core constructors; the cases of the primitives are in `PrimSound.lean`
and the induction itself in `Soundness.lean`.
-/

@[expose] public section

universe u

open Classical

namespace SolidLean.Calc

open SolidLean.Solid Term

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### Membership of values -/

/-- `w` (of sort `r`) is an element of the type value `vA` (of sort `r + 1`). -/
def TMem (r : ℕ) (w vA : M.T.El) : Prop :=
  ∃ (w' : M.T.U r) (vA' : M.T.U (r + 1)), w = M.T.inj w' ∧ vA = M.T.inj vA' ∧ M.T.mem (M.T.j r w') vA'

theorem TMem_inj (r : ℕ) (w' : M.T.U r) (vA' : M.T.U (r + 1)) :
    TMem (M := M) r (M.T.inj w') (M.T.inj vA') ↔ M.T.mem (M.T.j r w') vA' := by
  constructor
  · rintro ⟨w'', vA'', h1, h2, h⟩
    rw [Sorted.inj_injective M.T.U h1, Sorted.inj_injective M.T.U h2]; exact h
  · intro h; exact ⟨w', vA', rfl, rfl, h⟩

theorem TMem.sort_left {r : ℕ} {w vA : M.T.El} (h : TMem (M := M) r w vA) : w.1 = r := by
  obtain ⟨w', vA', rfl, rfl, -⟩ := h; rfl

theorem TMem.sort_right {r : ℕ} {w vA : M.T.El} (h : TMem (M := M) r w vA) : vA.1 = r + 1 := by
  obtain ⟨w', vA', rfl, rfl, -⟩ := h; rfl

/-- The universe of level `r`, as a value. -/
noncomputable abbrev univVal (r : ℕ) : M.T.El := M.T.inj (hM.univSet r)

/-! ### Valid environments -/

/-- An environment is valid for a context when each variable's type has a
unique value in the universe of its level, containing the variable's value. -/
def Valid {m : ℕ} (Γ : Ctx m) (η : Env M.T m) : Prop :=
  ∀ x : Fin m, (∃! vA, Val M.T Γ (Term.shift x (m - x) (Γ x).1) η vA) ∧
    ∀ vA, Val M.T Γ (Term.shift x (m - x) (Γ x).1) η vA →
      TMem (Γ x).2 (η x) vA ∧ TMem ((Γ x).2 + 1) vA (univVal hM (Γ x).2)

/-- The motive for typing judgments. -/
def PTy {m : ℕ} (Γ : Ctx m) (t A : Term) (r : ℕ) : Prop :=
  ∀ η, Valid hM Γ η →
    (∃! w, Val M.T Γ t η w) ∧ (∃! vA, Val M.T Γ A η vA) ∧
    (∀ vA, Val M.T Γ A η vA → TMem (r + 1) vA (univVal hM r)) ∧
    (∀ w vA, Val M.T Γ t η w → Val M.T Γ A η vA → TMem r w vA)

/-- The motive for definitional equality. -/
def PEq {m : ℕ} (Γ : Ctx m) (t s A : Term) (r : ℕ) : Prop :=
  PTy hM Γ t A r ∧ ∀ η, Valid hM Γ η → ∀ w, Val M.T Γ t η w ↔ Val M.T Γ s η w

/-! ### Weakening by one binder -/

theorem Env.snoc_eq_insert {m : ℕ} (η : Env M.T m) (x : M.T.El) :
    Fin.snoc (α := fun _ => M.T.El) η x = Env.insert M.T m 1 (e' := 0) η (fun _ => x) := by
  funext l
  refine Fin.lastCases ?_ (fun l => ?_) l
  · rw [Fin.snoc_last, Env.insert_mid _ _ _ _ (by simp) (by simp)]
  · rw [Fin.snoc_castSucc, Env.insert_lt _ _ _ _ (by simp)]
    exact congrArg η (Fin.ext rfl)

theorem Val_shift1 {m : ℕ} (Γ : Ctx m) (B : Term) (l : ℕ) (t : Term) (η : Env M.T m)
    (x w : M.T.El) :
    Val M.T (Γ.snoc B l) (Term.shift m 1 t) (Fin.snoc (α := fun _ => M.T.El) η x) w ↔
      Val M.T Γ t η w := by
  rw [Ctx.snoc_eq_insert, Env.snoc_eq_insert]
  exact Val_shift M.T m 1 t (e' := 0) Γ _ η _ w

theorem Valid.snoc {m : ℕ} {Γ : Ctx m} {η : Env M.T m} (hv : Valid hM Γ η) {A : Term} {i : ℕ}
    (x : M.T.El) (hA : ∃! vA, Val M.T Γ A η vA)
    (hAu : ∀ vA, Val M.T Γ A η vA → TMem (i + 1) vA (univVal hM i))
    (hx : ∀ vA, Val M.T Γ A η vA → TMem i x vA) :
    Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η x) := by
  intro y
  refine Fin.lastCases ?_ (fun y => ?_) y
  · rw [show (Γ.snoc A i) (Fin.last m) = (A, i) from by simp [Ctx.snoc]]
    simp only [Fin.val_last, Nat.add_sub_cancel_left, Fin.snoc_last]
    simp only [Val_shift1]
    exact ⟨hA, fun vA h => ⟨hx vA h, hAu vA h⟩⟩
  · rw [show (Γ.snoc A i) (Fin.castSucc y) = Γ y from by simp [Ctx.snoc]]
    simp only [Fin.coe_castSucc, Fin.snoc_castSucc]
    rw [← Term.shift_shift y m (by omega)]
    simp only [Val_shift1]
    exact hv y

theorem Valid.of_snoc {m : ℕ} {Γ : Ctx m} {B : Term} {l : ℕ} {η : Env M.T (m + 1)}
    (hv : Valid hM (Γ.snoc B l) η) : Valid hM Γ (Fin.init η) := by
  intro y
  have := hv (Fin.castSucc y)
  rw [show (Γ.snoc B l) (Fin.castSucc y) = Γ y from by simp [Ctx.snoc]] at this
  simp only [Fin.coe_castSucc] at this
  rw [← Term.shift_shift y m (by omega), ← Fin.snoc_init_self η] at this
  simp only [Val_shift1, Fin.snoc_castSucc] at this
  exact this

/-! ### Elementary consequences -/

theorem exists_unique_iff {α : Sort*} {P : α → Prop} (h : ∃! x, P x) : ∃ x₀, ∀ x, P x ↔ x = x₀ := by
  obtain ⟨x₀, hx₀, huniq⟩ := h
  exact ⟨x₀, fun x => ⟨fun hx => huniq x hx, fun e => e ▸ hx₀⟩⟩

theorem Val_univ_iff {m : ℕ} (Γ : Ctx m) (η : Env M.T m) (n : ℕ) (w : M.T.El) :
    Val M.T Γ (univ n) η w ↔ w = univVal hM n := by
  constructor
  · intro hv
    have hs : w.1 = n + 2 := hv.sort
    obtain ⟨w', rfl⟩ := elSort M.T w hs
    show M.T.inj w' = M.T.inj (hM.univSet n)
    congr 1
    cases n with
    | zero => exact (hM.isUnivSet_iff 0 w').1 ((Val_univ_zero M.T Γ η w').1 hv)
    | succ n => exact (hM.isUnivSet_iff (n + 1) w').1 ((Val_univ_succ M.T Γ η n w').1 hv)
  · rintro rfl
    cases n with
    | zero => exact (Val_univ_zero M.T Γ η _).2 ((hM.isUnivSet_iff 0 _).2 rfl)
    | succ n => exact (Val_univ_succ M.T Γ η n _).2 ((hM.isUnivSet_iff (n + 1) _).2 rfl)

theorem univVal_mem (n : ℕ) : TMem (n + 2) (univVal hM n) (univVal hM (n + 1)) :=
  (TMem_inj _ _ _).2 (hM.univSet_mem n)

/-- Membership in a universe of positive level, for `j`-images. -/
theorem mem_univSet_of_pos {n : ℕ} (hn : 1 ≤ n) (p : M.T.U n) :
    M.T.mem (M.T.j (n + 1) (M.T.j n p)) (hM.univSet n) := by
  cases n with
  | zero => omega
  | succ n => exact hM.j_j_mem_univSet_succ n p


/-! ### Reading the motives -/

theorem PTy.type_val {m : ℕ} {Γ : Ctx m} {A : Term} {i : ℕ} (h : PTy hM Γ A (univ i) (i + 1))
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ vA : M.T.U (i + 1), (∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) ∧
      M.T.mem (M.T.j (i + 1) vA) (hM.univSet i) := by
  obtain ⟨h1, -, -, h4⟩ := h η hv
  obtain ⟨w₀, hw₀⟩ := exists_unique_iff h1
  have hU := h4 w₀ (univVal hM i) ((hw₀ w₀).2 rfl) ((Val_univ_iff hM Γ η i _).2 rfl)
  obtain ⟨w', u', hw, hu, hmem⟩ := hU
  refine ⟨w', ?_, ?_⟩
  · rw [← hw]; exact hw₀
  · rw [← Sorted.inj_injective M.T.U hu] at hmem; exact hmem

theorem PTy.term_val {m : ℕ} {Γ : Ctx m} {a A : Term} {i : ℕ} (h : PTy hM Γ a A i)
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ va : M.T.U i, (∀ w, Val M.T Γ a η w ↔ w = M.T.inj va) ∧
      ∀ vA : M.T.U (i + 1), Val M.T Γ A η (M.T.inj vA) → M.T.mem (M.T.j i va) vA := by
  obtain ⟨h1, h2, -, h4⟩ := h η hv
  obtain ⟨w₀, hw₀⟩ := exists_unique_iff h1
  obtain ⟨vA₀, hvA₀, -⟩ := h2
  obtain ⟨w', vA', hw, -, -⟩ := h4 w₀ vA₀ ((hw₀ w₀).2 rfl) hvA₀
  refine ⟨w', by rw [← hw]; exact hw₀, fun vA hvA => ?_⟩
  have := h4 w₀ (M.T.inj vA) ((hw₀ w₀).2 rfl) hvA
  rw [hw] at this
  exact (TMem_inj _ _ _).1 this

/-- The valid extension by an element of the (unique) value of `A`. -/
theorem Valid.snoc_elem {m : ℕ} {Γ : Ctx m} {η : Env M.T m} (hv : Valid hM Γ η) {A : Term}
    {i : ℕ} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA)
    (hAU : M.T.mem (M.T.j (i + 1) vA) (hM.univSet i)) (a : M.T.U i) (ha : M.T.mem (M.T.j i a) vA) :
    Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) := by
  refine Valid.snoc hM hv (M.T.inj a) ⟨_, (hvA _).2 rfl, fun w h => (hvA w).1 h⟩ (fun vA' h => ?_)
    (fun vA' h => ?_)
  · rw [(hvA vA').1 h]; exact (TMem_inj _ _ _).2 hAU
  · rw [(hvA vA').1 h]; exact (TMem_inj _ _ _).2 ha

/-- The value of the type of a certified term. -/
theorem PTy.tyval {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : PTy hM Γ t A r)
    {η : Env M.T m} (hv : Valid hM Γ η) :
    ∃ vA : M.T.U (r + 1), (∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA) ∧
      M.T.mem (M.T.j (r + 1) vA) (hM.univSet r) := by
  obtain ⟨-, h2, h3, -⟩ := h η hv
  obtain ⟨vA₀, hvA₀⟩ := exists_unique_iff h2
  obtain ⟨vA', u', hw, hu, hmem⟩ := h3 vA₀ ((hvA₀ vA₀).2 rfl)
  refine ⟨vA', by rw [← hw]; exact hvA₀, ?_⟩
  rw [← Sorted.inj_injective M.T.U hu] at hmem; exact hmem

/-- The values of a type family `B` over `A` (given `B : U_j` at each element),
as a function into sort `j` (the value at `a` is its `j`-image). -/
theorem family_of {m : ℕ} {Γ : Ctx m} {A B : Term} {i j : ℕ} {η : Env M.T m} {vA' : M.T.U i}
    (hBv : ∀ a : M.T.U i, M.T.mem a vA' → ∃ vB : M.T.U (j + 1),
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
        w = M.T.inj vB) ∧ M.T.mem (M.T.j (j + 1) vB) (hM.univSet j)) :
    ∃ F : M.T.U i → M.T.U j, ∀ a, M.T.mem a vA' →
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j (F a))) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j (F a))) (hM.univSet j) := by
  have : ∀ a : M.T.U i, ∃ F : M.T.U j, M.T.mem a vA' →
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j F)) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j F)) (hM.univSet j) := by
    intro a
    by_cases ha : M.T.mem a vA'
    · obtain ⟨vB, h1, h2⟩ := hBv a ha
      obtain ⟨vB', rfl⟩ := hM.exists_j_of_mem_univSet vB h2
      exact ⟨vB', fun _ => ⟨h1, h2⟩⟩
    · exact ⟨hM.emptyAt j, fun h => absurd h ha⟩
  choose F hF using this
  exact ⟨F, hF⟩

/-- The pointwise form of a family's values. -/
theorem family_iff {m : ℕ} {Γ : Ctx m} {A B : Term} {i j : ℕ} {η : Env M.T m} {vA' : M.T.U i}
    {F : M.T.U i → M.T.U j}
    (hF : ∀ a, M.T.mem a vA' →
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj (M.T.j j (F a))) ∧
      M.T.mem (M.T.j (j + 1) (M.T.j j (F a))) (hM.univSet j)) :
    ∀ a, M.T.mem a vA' → ∀ vB : M.T.U (j + 1),
      Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ↔ vB = M.T.j j (F a) := by
  intro a ha vB
  rw [(hF a ha).1]
  exact ⟨fun h => Sorted.inj_injective M.T.U h, fun h => by rw [h]⟩

/-! ### The cases of the induction: typing -/

theorem case_var {m : ℕ} {Γ : Ctx m} (x : Fin m) :
    PTy hM Γ (var x) (Term.shift x (m - x) (Γ x).1) (Γ x).2 := by
  intro η hv
  obtain ⟨hA, hmem⟩ := hv x
  obtain ⟨vA₀, hvA₀⟩ := exists_unique_iff hA
  have hs : (η x).1 = (Γ x).2 := (hmem vA₀ ((hvA₀ vA₀).2 rfl)).1.sort_left
  have hval : ∀ w, Val M.T Γ (var x) η w ↔ w = η x := by
    intro w
    rw [Val_var']
    constructor
    · rintro ⟨h, rfl, -⟩; exact congrArg η (Fin.ext rfl)
    · rintro rfl; exact ⟨x.2, congrArg η (Fin.ext rfl), by rw [hs, Ctx.lev_of_lt]; rfl⟩
  simp only [hval]
  exact ⟨⟨η x, rfl, fun w h => h⟩, hA, fun vA h => (hmem vA h).2,
    fun w vA hw hvA => hw ▸ (hmem vA hvA).1⟩

theorem case_univ {m : ℕ} (Γ : Ctx m) (n : ℕ) : PTy hM Γ (univ n) (univ (n + 1)) (n + 2) := by
  intro η hv
  simp only [Val_univ_iff hM]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vA h => ?_, fun w vA hw hvA => ?_⟩
  · subst h; exact univVal_mem hM (n + 1)
  · subst hw; subst hvA; exact univVal_mem hM n

theorem case_weak {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (ht : PTy hM Γ t A r) (B : Term)
    (l : ℕ) : PTy hM (Γ.snoc B l) (Term.shift m 1 t) (Term.shift m 1 A) r := by
  intro η hv
  have hv' := Valid.of_snoc hM hv
  rw [← Fin.snoc_init_self η]
  simp only [Val_shift1]
  exact ht _ hv'

theorem case_conv {m : ℕ} {Γ : Ctx m} {t A B : Term} {r : ℕ} (ht : PTy hM Γ t A r)
    (hAB : PEq hM Γ A B (univ r) (r + 1)) : PTy hM Γ t B r := by
  intro η hv
  have e := hAB.2 η hv
  simp only [← e]
  exact ht η hv

theorem case_piData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hj : 1 ≤ j)
    (hA : PTy hM Γ A (univ i) (i + 1)) (hB : PTy hM (Γ.snoc A i) B (univ j) (j + 1))
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PTy hM Γ (pi .data i j A B) (univ (max i j)) (max i j + 1) := by
  intro η hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA hv
  obtain ⟨vA', rfl⟩ := hM.exists_j_of_mem_univSet vA hAU
  have hvalid : ∀ a : M.T.U i, M.T.mem a vA' →
      Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) :=
    fun a ha => Valid.snoc_elem hM hv hvA hAU a ((hM.j_mem_iff i a vA').2 ha)
  obtain ⟨F, hF⟩ := family_of hM (fun a ha => PTy.type_val hM hB (hvalid a ha))
  have hF' := family_iff hM hF
  obtain ⟨p, hp⟩ := exists_piSet hM η vA' F hF' hcB
  have hfam : FamOk M.T Γ i j A B η := by
    refine ⟨M.T.j i vA', (hvA _).2 rfl, fun vA₁ h => Sorted.inj_injective M.T.U ((hvA _).1 h),
      fun a ha => ?_⟩
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    refine ⟨M.T.j j (F a), (hF' a ha' _).2 rfl, fun vB' h => (hF' a ha' vB').1 h,
      hM.univSet j, (hM.isUnivSet_iff j _).2 rfl, (hF a ha').2⟩
  have hval : ∀ w, Val M.T Γ (pi .data i j A B) η w ↔ w = M.T.inj (M.T.j (max i j) p) := by
    intro w
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
  simp only [hval, Val_univ_iff hM]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vU h => ?_, fun w vU hw hvU => ?_⟩
  · subst h; exact univVal_mem hM _
  · subst hw; subst hvU
    exact (TMem_inj _ _ _).2 (mem_univSet_of_pos hM (by omega) p)

theorem case_piProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A B : Term}
    (hA : PTy hM Γ A (univ i) (i + 1)) (hB : PTy hM (Γ.snoc A i) B (univ 0) 1)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) :
    PTy hM Γ (pi .prop i 0 A B) (univ 0) 1 := by
  intro η hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA hv
  have hvalid : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA →
      Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) :=
    fun a ha => Valid.snoc_elem hM hv hvA hAU a ha
  have hBv : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vB : M.T.U 1,
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj vB) ∧
      M.T.mem (M.T.j 1 vB) (hM.univSet 0) := fun a ha => PTy.type_val hM hB (hvalid a ha)
  have hfam : FamOk M.T Γ i 0 A B η := by
    refine ⟨vA, (hvA _).2 rfl, fun vA₁ h => Sorted.inj_injective M.T.U ((hvA _).1 h), fun a ha => ?_⟩
    obtain ⟨vB, h1, h2⟩ := hBv a ha
    exact ⟨vB, (h1 _).2 rfl, fun vB' h => Sorted.inj_injective M.T.U ((h1 _).1 h),
      hM.univSet 0, (hM.isUnivSet_iff 0 _).2 rfl, h2⟩
  let ψ : Prop := ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vB : M.T.U 1,
    Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ∧
      ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vB
  have hval : ∀ w, Val M.T Γ (pi .prop i 0 A B) η w ↔ w = M.T.inj (hM.tvSet ψ) := by
    intro w
    constructor
    · intro hw
      have hs : w.1 = 1 := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [Val_pi_prop M.T hcA hcB] at hw
      obtain ⟨-, vA₁, hvA₁, htv⟩ := hw
      have e := Sorted.inj_injective M.T.U ((hvA _).1 hvA₁)
      subst e
      rw [(hM.isTV_iff _ w').1 htv]
    · rintro rfl
      rw [Val_pi_prop M.T hcA hcB]
      exact ⟨hfam, vA, (hvA _).2 rfl, (hM.isTV_iff ψ _).2 rfl⟩
  simp only [hval, Val_univ_iff hM]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vU h => ?_, fun w vU hw hvU => ?_⟩
  · subst h; exact univVal_mem hM _
  · subst hw; subst hvU
    exact (TMem_inj _ _ _).2 (hM.tvSet_mem_univSet ψ)


include hM in
/-- The graph of an abstraction is a function in the product. -/
theorem graph_isPiFun {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b B : Term} {η : Env M.T m}
    {vA' : M.T.U i} {F : M.T.U i → M.T.U j}
    (hF' : ∀ a, M.T.mem a vA' → ∀ vB : M.T.U (j + 1),
      Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ↔ vB = M.T.j j (F a))
    (hbv : ∀ a, M.T.mem a vA' → ∃ vb : M.T.U j,
      (∀ w, Val M.T (Γ.snoc A i) b (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
        w = M.T.inj vb) ∧ M.T.mem vb (F a))
    (w : M.T.U (max i j))
    (hw : ∀ q, M.T.mem q w ↔ ∃ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      ∃ vb : M.T.U j, Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q) :
    IsPiFun M.T Γ i j A B η (M.T.j i vA') w := by
  let Z := hM.sortModel (max i j)
  refine ⟨⟨fun q hq => ?_, fun u v v' hv hv' => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩,
    fun a ha v hv => ?_⟩
  · obtain ⟨a, -, vb, -, hq⟩ := (hw q).1 hq
    exact ⟨_, _, hq⟩
  · obtain ⟨q, hq, hpair⟩ := hv
    obtain ⟨q', hq', hpair'⟩ := hv'
    obtain ⟨a, ha, vb, hvb, hq₁⟩ := (hw q).1 hq
    obtain ⟨a', ha', vb', hvb', hq₁'⟩ := (hw q').1 hq'
    obtain ⟨e1, e2⟩ := Z.ordPair_inj hpair hq₁
    obtain ⟨e1', e2'⟩ := Z.ordPair_inj hpair' hq₁'
    have ea := hM.liftLE_injective (le_max_left i j) (e1.symm.trans e1')
    subst ea
    obtain ⟨vb₀, h1, -⟩ := hbv a ((hM.j_mem_iff i a vA').1 ha)
    have := ((h1 _).1 hvb).trans ((h1 _).1 hvb').symm
    rw [e2, e2', Sorted.inj_injective M.T.U this]
  · obtain ⟨v, q, hq, hpair⟩ := hu
    obtain ⟨a, ha, vb, -, hq₁⟩ := (hw q).1 hq
    exact ⟨a, ha, (Z.ordPair_inj hpair hq₁).1⟩
  · obtain ⟨a, ha, rfl⟩ := hu
    obtain ⟨vb, h1, -⟩ := hbv a ((hM.j_mem_iff i a vA').1 ha)
    obtain ⟨q, hq⟩ := Z.exists_ordPair (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) vb)
    exact ⟨_, q, (hw q).2 ⟨a, ha, vb, (h1 _).2 rfl, hq⟩, hq⟩
  · obtain ⟨q, hq, hpair⟩ := hv
    obtain ⟨a', ha', vb, hvb, hq₁⟩ := (hw q).1 hq
    obtain ⟨e1, e2⟩ := Z.ordPair_inj hpair hq₁
    have ea := hM.liftLE_injective (le_max_left i j) e1
    subst ea
    have ha₀ : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    obtain ⟨vb₀, h1, h2⟩ := hbv a ha₀
    have e := Sorted.inj_injective M.T.U ((h1 _).1 hvb)
    subst e
    exact ⟨M.T.j j (F a), (hF' a ha₀ _).2 rfl, vb, (hM.j_mem_iff j _ _).2 h2, e2⟩

theorem case_lamData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b B : Term} (hj : 1 ≤ j)
    (hA : PTy hM Γ A (univ i) (i + 1)) (hb : PTy hM (Γ.snoc A i) b B j)
    (hcA : A.cls Γ = i + 1) (hcb : b.cls (Γ.snoc A i) = j) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PTy hM Γ (lam .data i j A b) (pi .data i j A B) (max i j) := by
  intro η hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA hv
  obtain ⟨vA', rfl⟩ := hM.exists_j_of_mem_univSet vA hAU
  have hvalid : ∀ a : M.T.U i, M.T.mem a vA' →
      Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) :=
    fun a ha => Valid.snoc_elem hM hv hvA hAU a ((hM.j_mem_iff i a vA').2 ha)
  obtain ⟨F, hF⟩ := family_of hM (fun a ha => PTy.tyval hM hb (hvalid a ha))
  have hF' := family_iff hM hF
  have hbv : ∀ a, M.T.mem a vA' → ∃ vb : M.T.U j,
      (∀ w, Val M.T (Γ.snoc A i) b (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
        w = M.T.inj vb) ∧ M.T.mem vb (F a) := by
    intro a ha
    obtain ⟨vb, h1, h2⟩ := PTy.term_val hM hb (hvalid a ha)
    refine ⟨vb, h1, (hM.j_mem_iff j _ _).1 (h2 _ ((hF' a ha _).2 rfl))⟩
  have hbv' : ∀ a, M.T.mem a vA' → ∀ vb : M.T.U j,
      Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) → M.T.mem vb (F a) := by
    intro a ha vb h
    obtain ⟨vb₀, h1, h2⟩ := hbv a ha
    rw [Sorted.inj_injective M.T.U ((h1 _).1 h)]; exact h2
  obtain ⟨Cod, hCod⟩ := exists_cod hM η vA' F hF'
  obtain ⟨w, hw⟩ := exists_lamGraph hM η vA' F hcb Cod hCod hbv'
  obtain ⟨p, hp⟩ := exists_piSet hM η vA' F hF' hcB
  have hfam : FamOk M.T Γ i j A B η := by
    refine ⟨M.T.j i vA', (hvA _).2 rfl, fun vA₁ h => Sorted.inj_injective M.T.U ((hvA _).1 h),
      fun a ha => ?_⟩
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    refine ⟨M.T.j j (F a), (hF' a ha' _).2 rfl, fun vB' h => (hF' a ha' vB').1 h,
      hM.univSet j, (hM.isUnivSet_iff j _).2 rfl, (hF a ha').2⟩
  have hval : ∀ w', Val M.T Γ (lam .data i j A b) η w' ↔ w' = M.T.inj w := by
    intro w'
    constructor
    · intro hw'
      have hs : w'.1 = max i j := hw'.sort
      obtain ⟨w'', rfl⟩ := elSort M.T w' hs
      rw [Val_lam_data M.T hcA hcb] at hw'
      obtain ⟨vA₁, hvA₁, hw''⟩ := hw'
      have e := Sorted.inj_injective M.T.U ((hvA _).1 hvA₁)
      subst e
      congr 1
      exact hM.ext_of_iff hw'' hw
    · rintro rfl
      rw [Val_lam_data M.T hcA hcb]
      exact ⟨M.T.j i vA', (hvA _).2 rfl, hw⟩
  have hPi : ∀ w', Val M.T Γ (pi .data i j A B) η w' ↔ w' = M.T.inj (M.T.j (max i j) p) := by
    intro w'
    constructor
    · intro hw'
      have hs : w'.1 = max i j + 1 := hw'.sort
      obtain ⟨w'', rfl⟩ := elSort M.T w' hs
      rw [Val_pi_data M.T hcA hcB] at hw'
      obtain ⟨-, vA₁, hvA₁, p₁, rfl, hp₁⟩ := hw'
      have e := Sorted.inj_injective M.T.U ((hvA _).1 hvA₁)
      subst e
      congr 2
      exact hM.ext_of_iff hp₁ hp
    · rintro rfl
      rw [Val_pi_data M.T hcA hcB]
      exact ⟨hfam, M.T.j i vA', (hvA _).2 rfl, p, rfl, hp⟩
  simp only [hval, hPi]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vPi h => ?_, fun w' vPi hw' hvPi => ?_⟩
  · subst h; exact (TMem_inj _ _ _).2 (mem_univSet_of_pos hM (by omega) p)
  · subst hw'; subst hvPi
    refine (TMem_inj _ _ _).2 ((hM.j_mem_iff _ _ _).2 ((hp w).2 ?_))
    exact graph_isPiFun hM hF' hbv w hw

theorem case_lamProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A b B : Term}
    (hA : PTy hM Γ A (univ i) (i + 1)) (hb : PTy hM (Γ.snoc A i) b B 0)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) :
    PTy hM Γ (lam .prop i 0 A b) (pi .prop i 0 A B) 0 := by
  intro η hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA hv
  have hvalid : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA →
      Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) :=
    fun a ha => Valid.snoc_elem hM hv hvA hAU a ha
  have hBv : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vB : M.T.U 1,
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) w ↔ w = M.T.inj vB) ∧
      M.T.mem (M.T.j 1 vB) (hM.univSet 0) := fun a ha => PTy.tyval hM hb (hvalid a ha)
  have hfam : FamOk M.T Γ i 0 A B η := by
    refine ⟨vA, (hvA _).2 rfl, fun vA₁ h => Sorted.inj_injective M.T.U ((hvA _).1 h), fun a ha => ?_⟩
    obtain ⟨vB, h1, h2⟩ := hBv a ha
    exact ⟨vB, (h1 _).2 rfl, fun vB' h => Sorted.inj_injective M.T.U ((h1 _).1 h),
      hM.univSet 0, (hM.isUnivSet_iff 0 _).2 rfl, h2⟩
  let ψ : Prop := ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vB : M.T.U 1,
    Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ∧
      ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vB
  have hψ : ψ := by
    intro a ha
    obtain ⟨vB, h1, h2⟩ := hBv a ha
    obtain ⟨vb, h3, h4⟩ := PTy.term_val hM hb (hvalid a ha)
    have hmem := h4 vB ((h1 _).2 rfl)
    rcases hM.tv_char h2 with rfl | rfl
    · exact absurd hmem (hM.not_mem_emptyAt _)
    · exact ⟨_, (h1 _).2 rfl, hM.emptyAt 1, hM.emptyAt_spec 1, hM.singAt_spec _⟩
  have hval : ∀ w, Val M.T Γ (lam .prop i 0 A b) η w ↔ w = M.T.inj (hM.emptyAt 0) := by
    intro w
    constructor
    · intro hw
      have hs : w.1 = 0 := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [Val_lam_prop] at hw
      rw [hM.eq_emptyAt hw]
    · rintro rfl
      rw [Val_lam_prop]; exact hM.emptyAt_spec 0
  have hPi : ∀ w, Val M.T Γ (pi .prop i 0 A B) η w ↔ w = M.T.inj (hM.tvSet ψ) := by
    intro w
    constructor
    · intro hw
      have hs : w.1 = 1 := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [Val_pi_prop M.T hcA hcB] at hw
      obtain ⟨-, vA₁, hvA₁, htv⟩ := hw
      have e := Sorted.inj_injective M.T.U ((hvA _).1 hvA₁)
      subst e
      rw [(hM.isTV_iff _ w').1 htv]
    · rintro rfl
      rw [Val_pi_prop M.T hcA hcB]
      exact ⟨hfam, vA, (hvA _).2 rfl, (hM.isTV_iff ψ _).2 rfl⟩
  simp only [hval, hPi]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vPi h => ?_, fun w vPi hw hvPi => ?_⟩
  · subst h; exact (TMem_inj _ _ _).2 (hM.tvSet_mem_univSet ψ)
  · subst hw; subst hvPi
    exact (TMem_inj _ _ _).2 ((hM.mem_tvSet ψ).2 hψ)


/-- What the value of a data product says about a function in it, at an
element of the domain: the codomain family is well defined there and the
function's value lies in it. -/
theorem pi_data_elim {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} {η : Env M.T m}
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) {vPi : M.T.U (max i j + 1)}
    (hvPi : Val M.T Γ (pi .data i j A B) η (M.T.inj vPi)) {vf : M.T.U (max i j)}
    (hf : M.T.mem (M.T.j (max i j) vf) vPi) {va : M.T.U i} {vA : M.T.U (i + 1)}
    (hvA : Val M.T Γ A η (M.T.inj vA)) (hva : M.T.mem (M.T.j i va) vA) :
    (M.T.sortStr (max i j)).IsFunction vf ∧
    (∃ v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) va) v) ∧
    ∃ vB : M.T.U (j + 1),
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj va)) w ↔
        w = M.T.inj vB) ∧
      M.T.mem (M.T.j (j + 1) vB) (hM.univSet j) ∧
      ∀ v, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) va) v →
        ∃ b : M.T.U j, M.T.mem (M.T.j j b) vB ∧ v = M.T.liftLE (le_max_right i j) b := by
  rw [Val_pi_data M.T hcA hcB] at hvPi
  obtain ⟨⟨vA₀, hvA₀, hAuniq, hfam⟩, vA₁, hvA₁, p, rfl, hpi⟩ := hvPi
  have e := hAuniq vA₁ hvA₁; subst e
  have e := hAuniq vA hvA; subst e
  obtain ⟨hfun, hdom, hrng⟩ := (hpi vf).1 ((hM.j_mem_iff _ _ _).1 hf)
  obtain ⟨vB, hvB, hBuniq, u, hu, hBU⟩ := hfam va hva
  refine ⟨hfun, (hdom _).2 ⟨va, hva, rfl⟩, vB, fun w => ⟨fun h => ?_, fun h => h ▸ hvB⟩, ?_,
    fun v hv => ?_⟩
  · have hs : w.1 = j + 1 := h.sort.trans hcB
    obtain ⟨w', rfl⟩ := elSort M.T w hs
    rw [hBuniq w' h]
  · rw [(hM.isUnivSet_iff j u).1 hu] at hBU; exact hBU
  · obtain ⟨vB', hvB', b, hb, rfl⟩ := hrng va hva v hv
    rw [hBuniq vB' hvB'] at hb
    exact ⟨b, hb, rfl⟩

theorem case_appData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f a A B : Term} (hj : 1 ≤ j)
    (hf : PTy hM Γ f (pi .data i j A B) (max i j)) (ha : PTy hM Γ a A i)
    (hcf : f.cls Γ = max i j) (hca : a.cls Γ = i) (hcA : A.cls Γ = i + 1)
    (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PTy hM Γ (app .data j f a) (Term.subst m a 0 B) j := by
  intro η hv
  obtain ⟨vf, hvf, hfmem⟩ := PTy.term_val hM hf hv
  obtain ⟨va, hva, hamem⟩ := PTy.term_val hM ha hv
  obtain ⟨vA, hvA, -⟩ := PTy.tyval hM ha hv
  obtain ⟨vPi, hvPi, -⟩ := PTy.tyval hM hf hv
  have hva_mem : M.T.mem (M.T.j i va) vA := hamem vA ((hvA _).2 rfl)
  obtain ⟨hfun, ⟨v₀, hv₀⟩, vB, hvB, hBU, hrng⟩ :=
    pi_data_elim hM hcA hcB ((hvPi _).2 rfl) (hfmem vPi ((hvPi _).2 rfl)) ((hvA _).2 rfl) hva_mem
  obtain ⟨b, hb, rfl⟩ := hrng v₀ hv₀
  have hsub : ∀ w, Val M.T Γ (Term.subst m a 0 B) η w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj va)) w :=
    fun w => Val_subst0 M.T Γ A i a η (M.T.inj va) hva hca B w
  have happ : ∀ w : M.T.U j, Val M.T Γ (app .data j f a) η (M.T.inj w) ↔
      ∃ (vf' : M.T.U (max i j)) (va' : M.T.U i), Val M.T Γ f η (M.T.inj vf') ∧
        Val M.T Γ a η (M.T.inj va') ∧
        (M.T.sortStr (max i j)).FunApp vf' (M.T.liftLE (le_max_left i j) va')
          (M.T.liftLE (le_max_right i j) w) :=
    fun w => Val_app_data' M.T hcf hca (le_max_right i j) (le_max_left i j) η w
  have hval : ∀ w, Val M.T Γ (app .data j f a) η w ↔ w = M.T.inj b := by
    intro w
    constructor
    · intro hw
      have hs : w.1 = j := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [happ] at hw
      obtain ⟨vf', va', h1, h2, h3⟩ := hw
      have e1 := Sorted.inj_injective M.T.U ((hvf _).1 h1); subst e1
      have e2 := Sorted.inj_injective M.T.U ((hva _).1 h2); subst e2
      have := (hM.sortModel (max i j)).funApp_unique hfun h3 hv₀
      rw [hM.liftLE_injective _ this]
    · rintro rfl
      rw [happ]
      exact ⟨vf, va, (hvf _).2 rfl, (hva _).2 rfl, hv₀⟩
  simp only [hval, hsub, hvB]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vB' h => ?_, fun w vB' hw hvB' => ?_⟩
  · subst h; exact (TMem_inj _ _ _).2 hBU
  · subst hw; subst hvB'; exact (TMem_inj _ _ _).2 hb

/-- What the value of a proposition-kind product says at an element of the
domain. -/
theorem pi_prop_elim {m : ℕ} {Γ : Ctx m} {i : ℕ} {A B : Term} {η : Env M.T m}
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) {vPi : M.T.U 1}
    (hvPi : Val M.T Γ (pi .prop i 0 A B) η (M.T.inj vPi)) {vf : M.T.U 0}
    (hf : M.T.mem (M.T.j 0 vf) vPi) {va : M.T.U i} {vA : M.T.U (i + 1)}
    (hvA : Val M.T Γ A η (M.T.inj vA)) (hva : M.T.mem (M.T.j i va) vA) :
    ∃ vB : M.T.U 1,
      (∀ w, Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj va)) w ↔
        w = M.T.inj vB) ∧
      M.T.mem (M.T.j 1 vB) (hM.univSet 0) ∧ M.T.mem (M.T.j 0 (hM.emptyAt 0)) vB := by
  rw [Val_pi_prop M.T hcA hcB] at hvPi
  obtain ⟨⟨vA₀, hvA₀, hAuniq, hfam⟩, vA₁, hvA₁, htv⟩ := hvPi
  have e := hAuniq vA₁ hvA₁; subst e
  have e := hAuniq vA hvA; subst e
  obtain ⟨vB, hvB, hBuniq, u, hu, hBU⟩ := hfam va hva
  rw [(hM.isUnivSet_iff 0 u).1 hu] at hBU
  refine ⟨vB, fun w => ⟨fun h => ?_, fun h => h ▸ hvB⟩, hBU, ?_⟩
  · have hs : w.1 = 1 := h.sort.trans hcB
    obtain ⟨w', rfl⟩ := elSort M.T w hs
    rw [hBuniq w' h]
  · rw [(hM.isTV_iff _ vPi).1 htv] at hf
    have hψ : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∃ vB : M.T.U 1,
        Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ∧
          ∃ e, (M.T.sortStr 1).IsEmptySet e ∧ (M.T.sortStr 1).IsSingleton e vB := by
      by_contra hn
      unfold IsTowerModel.tvSet at hf
      rw [if_neg hn] at hf
      exact hM.not_mem_emptyAt _ hf
    obtain ⟨vB', hvB', e, he, hs⟩ := hψ va hva
    have e1 := hBuniq vB' hvB'
    subst e1
    rw [hM.eq_emptyAt he] at hs
    rw [hM.j_emptyAt]
    exact (hs _).2 rfl

theorem case_appProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {f a A B : Term}
    (hf : PTy hM Γ f (pi .prop i 0 A B) 0) (ha : PTy hM Γ a A i)
    (hca : a.cls Γ = i) (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) :
    PTy hM Γ (app .prop 0 f a) (Term.subst m a 0 B) 0 := by
  intro η hv
  obtain ⟨vf, hvf, hfmem⟩ := PTy.term_val hM hf hv
  obtain ⟨va, hva, hamem⟩ := PTy.term_val hM ha hv
  obtain ⟨vA, hvA, -⟩ := PTy.tyval hM ha hv
  obtain ⟨vPi, hvPi, -⟩ := PTy.tyval hM hf hv
  have hva_mem : M.T.mem (M.T.j i va) vA := hamem vA ((hvA _).2 rfl)
  obtain ⟨vB, hvB, hBU, hmem⟩ :=
    pi_prop_elim hM hcA hcB ((hvPi _).2 rfl) (hfmem vPi ((hvPi _).2 rfl)) ((hvA _).2 rfl) hva_mem
  have hsub : ∀ w, Val M.T Γ (Term.subst m a 0 B) η w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj va)) w :=
    fun w => Val_subst0 M.T Γ A i a η (M.T.inj va) hva hca B w
  have hval : ∀ w, Val M.T Γ (app .prop 0 f a) η w ↔ w = M.T.inj (hM.emptyAt 0) := by
    intro w
    constructor
    · intro hw
      have hs : w.1 = 0 := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [Val_app_prop] at hw
      rw [hM.eq_emptyAt hw]
    · rintro rfl
      rw [Val_app_prop]; exact hM.emptyAt_spec 0
  simp only [hval, hsub, hvB]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vB' h => ?_, fun w vB' hw hvB' => ?_⟩
  · subst h; exact (TMem_inj _ _ _).2 hBU
  · subst hw; subst hvB'; exact (TMem_inj _ _ _).2 hmem

theorem case_letE {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v A b B : Term}
    (hv : PTy hM Γ v A i) (hb : PTy hM (Γ.snoc A i) b B j)
    (hcv : v.cls Γ = i) (hcb : b.cls (Γ.snoc A i) = j) :
    PTy hM Γ (letE j A v b) (Term.subst m v 0 B) j := by
  intro η hη
  obtain ⟨h1, h2, h3, h4⟩ := hv η hη
  obtain ⟨vv, hvv, hvmem⟩ := PTy.term_val hM hv hη
  have hvalid : Valid hM (Γ.snoc A i) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj vv)) :=
    Valid.snoc hM hη (M.T.inj vv) h2 h3 (fun vA hvA => h4 _ vA ((hvv _).2 rfl) hvA)
  obtain ⟨vb, hvb, hbmem⟩ := PTy.term_val hM hb hvalid
  obtain ⟨vB, hvB, hBU⟩ := PTy.tyval hM hb hvalid
  have hsub : ∀ w, Val M.T Γ (Term.subst m v 0 B) η w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj vv)) w :=
    fun w => Val_subst0 M.T Γ A i v η (M.T.inj vv) hvv hcv B w
  have hcb' : b.cls (Γ.snoc A (v.cls Γ)) = j := by rw [hcv]; exact hcb
  have hval : ∀ w, Val M.T Γ (letE j A v b) η w ↔ w = M.T.inj vb := by
    intro w
    rw [Val_let M.T hcb']
    simp only [hcv, hvv]
    constructor
    · rintro ⟨vv', rfl, h⟩; exact (hvb w).1 h
    · rintro rfl; exact ⟨_, rfl, (hvb _).2 rfl⟩
  simp only [hval, hsub, hvB]
  refine ⟨⟨_, rfl, fun w h => h⟩, ⟨_, rfl, fun w h => h⟩, fun vB' h => ?_, fun w vB' hw hvB' => ?_⟩
  · subst h; exact (TMem_inj _ _ _).2 hBU
  · subst hw; subst hvB'; exact (TMem_inj _ _ _).2 (hbmem vB ((hvB _).2 rfl))


/-! ### Values depend on the context only through its levels -/

theorem Ctx.levels_snoc_congr {m : ℕ} {Γ Γ' : Ctx m} (h : Γ.levels = Γ'.levels) (A A' : Term)
    (i : ℕ) : (Γ.snoc A i).levels = (Γ'.snoc A' i).levels := by
  rw [Ctx.levels_snoc, Ctx.levels_snoc, h]

theorem Val_congr_levels {m : ℕ} {Γ Γ' : Ctx m} (h : Γ.levels = Γ'.levels) :
    ∀ (t : Term) (η : Env M.T m) (w : M.T.El), Val M.T Γ t η w ↔ Val M.T Γ' t η w
  | var x, η, w => by
    rw [Val_var', Val_var', Ctx.lev_congr h]
  | Term.univ n, η, w => by
    refine Val_sort_iff M.T Γ' Γ (Term.univ n) (Term.univ n) η η w rfl (fun w' => ?_)
    cases n with
    | zero => rw [Val_univ_zero, Val_univ_zero]
    | succ n => rw [Val_univ_succ, Val_univ_succ]
  | pi .prop i j A B, η, w => by
    have hcA := Term.cls_congr h A
    have hcB := Term.cls_congr (Ctx.levels_snoc_congr h A A i) B
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' : A.cls Γ' = i + 1 := hcA ▸ hA
      have hB' : B.cls (Γ'.snoc A i) = 1 := hcB ▸ hB
      refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
      rw [Val_pi_prop M.T hA hB, Val_pi_prop M.T hA' hB']
      have hBw : ∀ (a : M.T.U i) (vB : M.T.U (0 + 1)),
          Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ↔
          Val M.T (Γ'.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) :=
        fun a vB => Val_congr_levels (Ctx.levels_snoc_congr h A A i) B _ _
      refine and_congr (FamOk_congr M.T (fun vA => Val_congr_levels h A η _) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_congr_levels h A η _) ?_
      exact IsTV_congr M.T 1 (forall_congr' fun a => imp_congr Iff.rfl (exists_congr fun vB =>
        and_congr (hBw a vB) Iff.rfl)) w'
    · have hg' : ¬ (A.cls Γ' = i + 1 ∧ B.cls (Γ'.snoc A i) = 1) := by
        rw [← hcA, ← hcB]; exact hg
      exact iff_of_false (not_Val_pi_prop M.T _ _ _ _ _ _ _ hg) (not_Val_pi_prop M.T _ _ _ _ _ _ _ hg')
  | pi .data i j A B, η, w => by
    have hcA := Term.cls_congr h A
    have hcB := Term.cls_congr (Ctx.levels_snoc_congr h A A i) B
    by_cases hg : A.cls Γ = i + 1 ∧ B.cls (Γ.snoc A i) = j + 1
    · obtain ⟨hA, hB⟩ := hg
      have hA' : A.cls Γ' = i + 1 := hcA ▸ hA
      have hB' : B.cls (Γ'.snoc A i) = j + 1 := hcB ▸ hB
      refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
      rw [Val_pi_data M.T hA hB, Val_pi_data M.T hA' hB']
      have hBw : ∀ (a : M.T.U i) (vB : M.T.U (j + 1)),
          Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ↔
          Val M.T (Γ'.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) :=
        fun a vB => Val_congr_levels (Ctx.levels_snoc_congr h A A i) B _ _
      refine and_congr (FamOk_congr M.T (fun vA => Val_congr_levels h A η _) hBw) ?_
      refine exists_congr fun vA => and_congr (Val_congr_levels h A η _) (exists_congr fun q =>
        and_congr Iff.rfl (forall_congr' fun f => iff_congr Iff.rfl ?_))
      exact IsPiFun_congr M.T vA f hBw
    · have hg' : ¬ (A.cls Γ' = i + 1 ∧ B.cls (Γ'.snoc A i) = j + 1) := by
        rw [← hcA, ← hcB]; exact hg
      exact iff_of_false (not_Val_pi_data M.T _ _ _ _ _ _ _ hg) (not_Val_pi_data M.T _ _ _ _ _ _ _ hg')
  | lam .prop i j A b, η, w => by
    refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
    rw [Val_lam_prop, Val_lam_prop]
  | lam .data i j A b, η, w => by
    have hcA := Term.cls_congr h A
    have hcb := Term.cls_congr (Ctx.levels_snoc_congr h A A i) b
    by_cases hg : A.cls Γ = i + 1 ∧ b.cls (Γ.snoc A i) = j
    · obtain ⟨hA, hb⟩ := hg
      have hA' : A.cls Γ' = i + 1 := hcA ▸ hA
      have hb' : b.cls (Γ'.snoc A i) = j := hcb ▸ hb
      refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
      rw [Val_lam_data M.T hA hb, Val_lam_data M.T hA' hb']
      refine exists_congr fun vA => and_congr (Val_congr_levels h A η _) (forall_congr' fun q =>
        iff_congr Iff.rfl (exists_congr fun a => and_congr Iff.rfl (exists_congr fun vb =>
          and_congr (Val_congr_levels (Ctx.levels_snoc_congr h A A i) b _ _) Iff.rfl)))
    · have hg' : ¬ (A.cls Γ' = i + 1 ∧ b.cls (Γ'.snoc A i) = j) := by
        rw [← hcA, ← hcb]; exact hg
      exact iff_of_false (not_Val_lam_data M.T _ _ _ _ _ _ _ hg) (not_Val_lam_data M.T _ _ _ _ _ _ _ hg')
  | app .prop j f a, η, w => by
    refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
    rw [Val_app_prop, Val_app_prop]
  | app .data j f a, η, w => by
    have hcf := Term.cls_congr h f
    have hca := Term.cls_congr h a
    by_cases hg : j ≤ f.cls Γ ∧ a.cls Γ ≤ f.cls Γ
    · obtain ⟨hj, ha⟩ := hg
      refine Val_sort_iff M.T Γ' Γ _ _ η η w rfl (fun w' => ?_)
      rw [Val_app_data' M.T rfl rfl hj ha, Val_app_data' M.T hcf.symm hca.symm hj ha]
      exact exists_congr fun vf => exists_congr fun va =>
        and_congr (Val_congr_levels h f η _) (and_congr (Val_congr_levels h a η _) Iff.rfl)
    · have hg' : ¬ (j ≤ f.cls Γ' ∧ a.cls Γ' ≤ f.cls Γ') := by
        rw [← hcf, ← hca]; exact hg
      exact iff_of_false (not_Val_app_data M.T _ _ _ _ _ _ hg) (not_Val_app_data M.T _ _ _ _ _ _ hg')
  | letE j A v b, η, w => by
    have hcv := Term.cls_congr h v
    have hcb := Term.cls_congr (Ctx.levels_snoc_congr h A A (v.cls Γ)) b
    by_cases hg : b.cls (Γ.snoc A (v.cls Γ)) = j
    · have hg' : b.cls (Γ'.snoc A (v.cls Γ')) = j := by rw [← hcv, ← hcb]; exact hg
      rw [Val_let M.T hg, Val_let M.T hg']
      refine exists_congr fun vv => and_congr (Val_congr_levels h v η _) ?_
      have e : (Γ'.snoc A (v.cls Γ')).levels = (Γ'.snoc A (v.cls Γ)).levels := by rw [hcv]
      rw [Val_congr_levels e b]
      exact Val_congr_levels (Ctx.levels_snoc_congr h A A (v.cls Γ)) b _ _
    · have hg' : ¬ b.cls (Γ'.snoc A (v.cls Γ')) = j := by rw [← hcv, ← hcb]; exact hg
      exact iff_of_false (not_Val_let M.T _ _ _ _ _ _ _ hg) (not_Val_let M.T _ _ _ _ _ _ _ hg')
  | prim c args, η, w => by
    have hc : ∀ k, (args k).cls Γ' = (args k).cls Γ := fun k => (Term.cls_congr h (args k)).symm
    by_cases hg : ∀ k, (args k).cls Γ = c.argSort k
    · have hg' : ∀ k, (args k).cls Γ' = c.argSort k := fun k => (hc k).trans (hg k)
      rw [Val_prim' M.T c _ hg, Val_prim' M.T c _ hg']
      exact and_congr Iff.rfl (exists_congr fun vs => and_congr
        (forall_congr' fun k => Val_congr_levels h (args k) η (vs k)) Iff.rfl)
    · have hg' : ¬ ∀ k, (args k).cls Γ' = c.argSort k := by simp only [hc]; exact hg
      exact iff_of_false (not_Val_prim M.T _ _ _ _ _ hg) (not_Val_prim M.T _ _ _ _ _ hg')


/-! ### The cases of the induction: definitional equality -/

/-- Terms of level `0` have the empty set as value. -/
theorem level0_val {m : ℕ} {Γ : Ctx m} {t A : Term} (h : PTy hM Γ t A 0) {η : Env M.T m}
    (hv : Valid hM Γ η) : ∀ w, Val M.T Γ t η w ↔ w = M.T.inj (hM.emptyAt 0) := by
  obtain ⟨vt, hvt, hmem⟩ := PTy.term_val hM h hv
  obtain ⟨vA, hvA, hAU⟩ := PTy.tyval hM h hv
  have := hM.eq_emptyAt_of_mem hAU (hmem vA ((hvA _).2 rfl))
  rw [this] at hvt
  exact hvt

theorem pty_subst0 {m : ℕ} {Γ : Ctx m} {i j : ℕ} {a A b B : Term} (ha : PTy hM Γ a A i)
    (hb : PTy hM (Γ.snoc A i) b B j) (hca : a.cls Γ = i) :
    PTy hM Γ (Term.subst m a 0 b) (Term.subst m a 0 B) j := by
  intro η hv
  obtain ⟨h1, h2, h3, h4⟩ := ha η hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM ha hv
  have hvalid := Valid.snoc hM hv (M.T.inj va) h2 h3 (fun vA hvA => h4 _ vA ((hva _).2 rfl) hvA)
  have e1 := Val_subst0 M.T Γ A i a η (M.T.inj va) hva hca b
  have e2 := Val_subst0 M.T Γ A i a η (M.T.inj va) hva hca B
  simp only [e1, e2]
  exact hb _ hvalid

theorem eq_refl {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : PTy hM Γ t A r) :
    PEq hM Γ t t A r := ⟨h, fun _ _ _ => Iff.rfl⟩

theorem eq_symm {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : PEq hM Γ t s A r) :
    PEq hM Γ s t A r := by
  refine ⟨fun η hv => ?_, fun η hv w => (h.2 η hv w).symm⟩
  have e := h.2 η hv
  simp only [← e]
  exact h.1 η hv

theorem eq_trans {m : ℕ} {Γ : Ctx m} {t s u A : Term} {r : ℕ} (h : PEq hM Γ t s A r)
    (h' : PEq hM Γ s u A r) : PEq hM Γ t u A r :=
  ⟨h.1, fun η hv w => (h.2 η hv w).trans (h'.2 η hv w)⟩

theorem eq_conv {m : ℕ} {Γ : Ctx m} {t s A B : Term} {r : ℕ} (h : PEq hM Γ t s A r)
    (hAB : PEq hM Γ A B (univ r) (r + 1)) : PEq hM Γ t s B r :=
  ⟨case_conv hM h.1 hAB, h.2⟩

theorem eq_betaData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b B a : Term} (hj : 1 ≤ j)
    (hA : PTy hM Γ A (univ i) (i + 1)) (hb : PTy hM (Γ.snoc A i) b B j) (ha : PTy hM Γ a A i)
    (hcA : A.cls Γ = i + 1) (hcb : b.cls (Γ.snoc A i) = j) (hcB : B.cls (Γ.snoc A i) = j + 1)
    (hca : a.cls Γ = i) :
    PEq hM Γ (app .data j (lam .data i j A b) a) (Term.subst m a 0 b) (Term.subst m a 0 B) j := by
  have hlam := case_lamData hM hj hA hb hcA hcb hcB
  have happ := case_appData hM hj hlam ha rfl hca hcA hcB
  have hsub := pty_subst0 hM ha hb hca
  refine ⟨happ, fun η hv w => ?_⟩
  obtain ⟨w₀, hw₀, -⟩ := PTy.term_val hM happ hv
  obtain ⟨w₁, hw₁, -⟩ := PTy.term_val hM hsub hv
  obtain ⟨vf, hvf, -⟩ := PTy.term_val hM hlam hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM ha hv
  rw [hw₀, hw₁]
  suffices w₀ = w₁ by rw [this]
  have h1 := (hw₀ _).2 rfl
  rw [Val_app_data' M.T (show (lam .data i j A b).cls Γ = max i j from rfl) hca
    (le_max_right i j) (le_max_left i j)] at h1
  obtain ⟨vf', va', hvf', hva', hfa⟩ := h1
  have e1 := Sorted.inj_injective M.T.U ((hvf _).1 hvf'); subst e1
  have e2 := Sorted.inj_injective M.T.U ((hva _).1 hva'); subst e2
  have h2 := (hvf _).2 rfl
  rw [Val_lam_data M.T hcA hcb] at h2
  obtain ⟨vA₁, -, hgraph⟩ := h2
  obtain ⟨q, hq, hpair⟩ := hfa
  obtain ⟨a₁, -, vb, hvb, hpair'⟩ := (hgraph q).1 hq
  obtain ⟨e3, e4⟩ := (hM.sortModel (max i j)).ordPair_inj hpair hpair'
  have e3' := hM.liftLE_injective _ e3; subst e3'
  have e4' := hM.liftLE_injective _ e4; subst e4'
  have h3 := (hw₁ _).2 rfl
  rw [Val_subst0 M.T Γ A i a η (M.T.inj va') hva hca] at h3
  obtain ⟨-, h2, h3', h4⟩ := ha η hv
  have hvalid := Valid.snoc hM hv (M.T.inj va') h2 h3' (fun vA hvA => h4 _ vA ((hva _).2 rfl) hvA)
  obtain ⟨vb₀, hvb₀, -⟩ := PTy.term_val hM hb hvalid
  exact Sorted.inj_injective M.T.U (((hvb₀ _).1 hvb).trans ((hvb₀ _).1 h3).symm)

theorem eq_betaProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A b B a : Term}
    (hA : PTy hM Γ A (univ i) (i + 1)) (hb : PTy hM (Γ.snoc A i) b B 0) (ha : PTy hM Γ a A i)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) (hca : a.cls Γ = i) :
    PEq hM Γ (app .prop 0 (lam .prop i 0 A b) a) (Term.subst m a 0 b) (Term.subst m a 0 B) 0 := by
  have hlam := case_lamProp hM hA hb hcA hcB
  have happ := case_appProp hM hlam ha hca hcA hcB
  have hsub := pty_subst0 hM ha hb hca
  exact ⟨happ, fun η hv w => by rw [level0_val hM happ hv, level0_val hM hsub hv]⟩

theorem eq_zeta {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v A b B : Term}
    (hv : PTy hM Γ v A i) (hb : PTy hM (Γ.snoc A i) b B j)
    (hcv : v.cls Γ = i) (hcb : b.cls (Γ.snoc A i) = j) :
    PEq hM Γ (letE j A v b) (Term.subst m v 0 b) (Term.subst m v 0 B) j := by
  refine ⟨case_letE hM hv hb hcv hcb, fun η hη w => ?_⟩
  obtain ⟨vv, hvv, -⟩ := PTy.term_val hM hv hη
  have hcb' : b.cls (Γ.snoc A (v.cls Γ)) = j := by rw [hcv]; exact hcb
  rw [Val_let M.T hcb', Val_subst0 M.T Γ A i v η (M.T.inj vv) hvv hcv]
  simp only [hcv, hvv]
  constructor
  · rintro ⟨_, rfl, h⟩; exact h
  · intro h; exact ⟨_, rfl, h⟩

theorem eq_eta {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f A B : Term} (hj : 1 ≤ j)
    (hf : PTy hM Γ f (pi .data i j A B) (max i j)) (hcf : f.cls Γ = max i j)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PEq hM Γ (lam .data i j A (app .data j (Term.shift m 1 f) (var m))) f
      (pi .data i j A B) (max i j) := by
  have hval : ∀ η, Valid hM Γ η → ∀ w,
      Val M.T Γ (lam .data i j A (app .data j (Term.shift m 1 f) (var m))) η w ↔
      Val M.T Γ f η w := by
    intro η hv w
    obtain ⟨vf, hvf, hfmem⟩ := PTy.term_val hM hf hv
    obtain ⟨vPi, hvPi, -⟩ := PTy.tyval hM hf hv
    have hPiv := (hvPi _).2 rfl
    rw [Val_pi_data M.T hcA hcB] at hPiv
    obtain ⟨⟨vA₀, hvA₀, hAuniq, -⟩, vA, hvA, p, rfl, hpi⟩ := hPiv
    have e := hAuniq vA hvA; subst e
    obtain ⟨hfun, hdom, hrng⟩ :=
      (hpi vf).1 ((hM.j_mem_iff _ _ _).1 (hfmem _ ((hvPi _).2 rfl)))
    let Z := hM.sortModel (max i j)
    -- the body's values
    have hcf' : (Term.shift m 1 f).cls (Γ.snoc A i) = max i j := by
      rw [Term.cls_shift1]; exact hcf
    have hcx : (var m).cls (Γ.snoc A i) = i := Γ.lev_snoc_self A i
    have hbody : ∀ (a : M.T.U i) (vb : M.T.U j),
        Val M.T (Γ.snoc A i) (app .data j (Term.shift m 1 f) (var m))
          (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) (M.T.inj vb) ↔
        (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) := by
      intro a vb
      rw [Val_app_data' M.T hcf' hcx (le_max_right i j) (le_max_left i j)]
      have hvar : ∀ w, Val M.T (Γ.snoc A i) (var m) (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
          w = M.T.inj a := by
        intro w
        rw [Val_var']
        have e : ∀ h : m < m + 1,
            Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a) ⟨m, h⟩ = M.T.inj a := by
          intro h
          rw [show (⟨m, h⟩ : Fin (m + 1)) = Fin.last m from Fin.ext rfl]
          exact Fin.snoc_last _ _
        constructor
        · rintro ⟨h, hw, -⟩
          rw [hw, e h]
        · rintro rfl
          exact ⟨Nat.lt_succ_self m, (e _).symm, by rw [Γ.lev_snoc_self]⟩
      simp only [Val_shift1, hvf, hvar]
      constructor
      · rintro ⟨vf', va', h1, h2, h3⟩
        have e1 := Sorted.inj_injective M.T.U h1; subst e1
        have e2 := Sorted.inj_injective M.T.U h2; subst e2
        exact h3
      · intro h3
        exact ⟨vf, a, rfl, rfl, h3⟩
    have hgraph : ∀ q, M.T.mem q vf ↔ ∃ a : M.T.U i, M.T.mem (M.T.j i a) vA ∧
        ∃ vb : M.T.U j, (M.T.sortStr (max i j)).FunApp vf (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q := by
      intro q
      constructor
      · intro hq
        obtain ⟨u, v, huv⟩ := hfun.1 q hq
        have happ : (M.T.sortStr (max i j)).FunApp vf u v := ⟨q, hq, huv⟩
        obtain ⟨a, ha, rfl⟩ := (hdom u).1 ⟨v, happ⟩
        obtain ⟨vB, -, b, -, rfl⟩ := hrng a ha v happ
        exact ⟨a, ha, b, happ, huv⟩
      · rintro ⟨a, -, vb, ⟨q', hq', hpair'⟩, hpair⟩
        rw [Z.ordPair_unique hpair hpair']
        exact hq'
    rw [hvf]
    constructor
    · intro hw
      have hs : w.1 = max i j := hw.sort
      obtain ⟨w', rfl⟩ := elSort M.T w hs
      rw [Val_lam_data M.T hcA
        (show (app .data j (Term.shift m 1 f) (var m)).cls (Γ.snoc A i) = j from rfl)] at hw
      obtain ⟨vA₁, hvA₁, hw'⟩ := hw
      have e := hAuniq vA₁ hvA₁; subst e
      congr 1
      refine hM.ext_of_iff hw' (fun q => ?_)
      rw [hgraph q]
      exact exists_congr fun a => and_congr Iff.rfl (exists_congr fun vb =>
        and_congr (hbody a vb).symm Iff.rfl)
    · rintro rfl
      rw [Val_lam_data M.T hcA
        (show (app .data j (Term.shift m 1 f) (var m)).cls (Γ.snoc A i) = j from rfl)]
      refine ⟨vA, hvA, fun q => ?_⟩
      rw [hgraph q]
      exact exists_congr fun a => and_congr Iff.rfl (exists_congr fun vb =>
        and_congr (hbody a vb).symm Iff.rfl)
  refine ⟨fun η hv => ?_, hval⟩
  have e := hval η hv
  simp only [e]
  exact hf η hv

theorem eq_proofIrrel {m : ℕ} {Γ : Ctx m} {h h' P : Term} (hh : PTy hM Γ h P 0)
    (hh' : PTy hM Γ h' P 0) : PEq hM Γ h h' P 0 :=
  ⟨hh, fun η hv w => by rw [level0_val hM hh hv, level0_val hM hh' hv]⟩


/-! ### Guarded congruences -/

theorem FamOk_congr_guard {m : ℕ} {Γ Γ' : Ctx m} {A A' B B' : Term} {i j : ℕ} {η : Env M.T m}
    {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ A η w ↔ w = M.T.inj vA)
    (eA : ∀ w, Val M.T Γ' A' η w ↔ Val M.T Γ A η w)
    (eB : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ w,
      Val M.T (Γ'.snoc A' i) B' (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w) :
    FamOk M.T Γ' i j A' B' η ↔ FamOk M.T Γ i j A B η := by
  unfold FamOk
  constructor
  · rintro ⟨vA₁, h1, h2, h3⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 ((eA _).1 h1))
    subst e
    refine ⟨vA₁, (hvA _).2 rfl, fun vA' h => h2 vA' ((eA _).2 h), fun a ha => ?_⟩
    obtain ⟨vB, h4, h5, u, hu, h6⟩ := h3 a ha
    exact ⟨vB, (eB a ha _).1 h4, fun vB' h => h5 vB' ((eB a ha _).2 h), u, hu, h6⟩
  · rintro ⟨vA₁, h1, h2, h3⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 h1)
    subst e
    refine ⟨vA₁, (eA _).2 ((hvA _).2 rfl), fun vA' h => h2 vA' ((eA _).1 h), fun a ha => ?_⟩
    obtain ⟨vB, h4, h5, u, hu, h6⟩ := h3 a ha
    exact ⟨vB, (eB a ha _).2 h4, fun vB' h => h5 vB' ((eB a ha _).1 h), u, hu, h6⟩

theorem IsPiFun_congr_guard {m : ℕ} {Γ Γ' : Ctx m} {A A' B B' : Term} {i j : ℕ} {η : Env M.T m}
    {vA : M.T.U (i + 1)}
    (eB : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ w,
      Val M.T (Γ'.snoc A' i) B' (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w)
    (f : M.T.U (max i j)) :
    IsPiFun M.T Γ' i j A' B' η vA f ↔ IsPiFun M.T Γ i j A B η vA f := by
  unfold IsPiFun
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun a => ⟨fun h ha v hv => ?_,
    fun h ha v hv => ?_⟩))
  · obtain ⟨vB, h1, h2⟩ := h ha v hv
    exact ⟨vB, (eB a ha _).1 h1, h2⟩
  · obtain ⟨vB, h1, h2⟩ := h ha v hv
    exact ⟨vB, (eB a ha _).2 h1, h2⟩

theorem eq_congrPiData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A A' B B' : Term} (hj : 1 ≤ j)
    (hA : PEq hM Γ A A' (univ i) (i + 1)) (hB : PEq hM (Γ.snoc A i) B B' (univ j) (j + 1))
    (hcA : A.cls Γ = i + 1) (hcA' : A'.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1)
    (hcB' : B'.cls (Γ.snoc A' i) = j + 1) :
    PEq hM Γ (pi .data i j A B) (pi .data i j A' B') (univ (max i j)) (max i j + 1) := by
  refine ⟨case_piData hM hj hA.1 hB.1 hcA hcB, fun η hv w => ?_⟩
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA.1 hv
  have eA : ∀ w, Val M.T Γ A' η w ↔ Val M.T Γ A η w := fun w => (hA.2 η hv w).symm
  have eB : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ w,
      Val M.T (Γ.snoc A' i) B' (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w := by
    intro a ha w
    rw [← Val_congr_levels (Ctx.levels_snoc_congr rfl A A' i) B']
    exact (hB.2 _ (Valid.snoc_elem hM hv hvA hAU a ha) w).symm
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_pi_data M.T hcA hcB, Val_pi_data M.T hcA' hcB']
  refine and_congr (FamOk_congr_guard hvA eA eB).symm ?_
  constructor
  · rintro ⟨vA₁, h1, p, hp, hpi⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 h1)
    rw [e] at hpi
    exact ⟨vA, (eA _).2 ((hvA _).2 rfl), p, hp, fun f => (hpi f).trans (IsPiFun_congr_guard eB f).symm⟩
  · rintro ⟨vA₁, h1, p, hp, hpi⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 ((eA _).1 h1))
    rw [e] at hpi
    exact ⟨vA, (hvA _).2 rfl, p, hp, fun f => (hpi f).trans (IsPiFun_congr_guard eB f)⟩

theorem eq_congrPiProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A A' B B' : Term}
    (hA : PEq hM Γ A A' (univ i) (i + 1)) (hB : PEq hM (Γ.snoc A i) B B' (univ 0) 1)
    (hcA : A.cls Γ = i + 1) (hcA' : A'.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1)
    (hcB' : B'.cls (Γ.snoc A' i) = 1) :
    PEq hM Γ (pi .prop i 0 A B) (pi .prop i 0 A' B') (univ 0) 1 := by
  refine ⟨case_piProp hM hA.1 hB.1 hcA hcB, fun η hv w => ?_⟩
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA.1 hv
  have eA : ∀ w, Val M.T Γ A' η w ↔ Val M.T Γ A η w := fun w => (hA.2 η hv w).symm
  have eB : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ w,
      Val M.T (Γ.snoc A' i) B' (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
      Val M.T (Γ.snoc A i) B (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w := by
    intro a ha w
    rw [← Val_congr_levels (Ctx.levels_snoc_congr rfl A A' i) B']
    exact (hB.2 _ (Valid.snoc_elem hM hv hvA hAU a ha) w).symm
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_pi_prop M.T hcA hcB, Val_pi_prop M.T hcA' hcB']
  refine and_congr (FamOk_congr_guard hvA eA eB).symm ?_
  constructor
  · rintro ⟨vA₁, h1, htv⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 h1)
    subst e
    refine ⟨vA₁, (eA _).2 ((hvA _).2 rfl), (IsTV_congr M.T 1 ?_ w').1 htv⟩
    exact forall_congr' fun a => ⟨fun h ha => (h ha).imp fun vB h' => ⟨(eB a ha _).2 h'.1, h'.2⟩,
      fun h ha => (h ha).imp fun vB h' => ⟨(eB a ha _).1 h'.1, h'.2⟩⟩
  · rintro ⟨vA₁, h1, htv⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 ((eA _).1 h1))
    subst e
    refine ⟨vA₁, (hvA _).2 rfl, (IsTV_congr M.T 1 ?_ w').1 htv⟩
    exact forall_congr' fun a => ⟨fun h ha => (h ha).imp fun vB h' => ⟨(eB a ha _).1 h'.1, h'.2⟩,
      fun h ha => (h ha).imp fun vB h' => ⟨(eB a ha _).2 h'.1, h'.2⟩⟩

theorem eq_congrLamData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A A' b b' B : Term} (hj : 1 ≤ j)
    (hA : PEq hM Γ A A' (univ i) (i + 1)) (hb : PEq hM (Γ.snoc A i) b b' B j)
    (hcA : A.cls Γ = i + 1) (hcA' : A'.cls Γ = i + 1) (hcb : b.cls (Γ.snoc A i) = j)
    (hcb' : b'.cls (Γ.snoc A' i) = j) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PEq hM Γ (lam .data i j A b) (lam .data i j A' b') (pi .data i j A B) (max i j) := by
  refine ⟨case_lamData hM hj hA.1 hb.1 hcA hcb hcB, fun η hv w => ?_⟩
  obtain ⟨vA, hvA, hAU⟩ := PTy.type_val hM hA.1 hv
  have eA : ∀ w, Val M.T Γ A' η w ↔ Val M.T Γ A η w := fun w => (hA.2 η hv w).symm
  have eb : ∀ a : M.T.U i, M.T.mem (M.T.j i a) vA → ∀ w,
      Val M.T (Γ.snoc A' i) b' (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w ↔
      Val M.T (Γ.snoc A i) b (Fin.snoc (α := fun _ => M.T.El) η (M.T.inj a)) w := by
    intro a ha w
    rw [← Val_congr_levels (Ctx.levels_snoc_congr rfl A A' i) b']
    exact (hb.2 _ (Valid.snoc_elem hM hv hvA hAU a ha) w).symm
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_lam_data M.T hcA hcb, Val_lam_data M.T hcA' hcb']
  constructor
  · rintro ⟨vA₁, h1, hg⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 h1)
    subst e
    refine ⟨vA₁, (eA _).2 ((hvA _).2 rfl), fun q => (hg q).trans ?_⟩
    exact exists_congr fun a => ⟨fun ⟨ha, vb, h2, h3⟩ => ⟨ha, vb, (eb a ha _).2 h2, h3⟩,
      fun ⟨ha, vb, h2, h3⟩ => ⟨ha, vb, (eb a ha _).1 h2, h3⟩⟩
  · rintro ⟨vA₁, h1, hg⟩
    have e : vA₁ = vA := Sorted.inj_injective M.T.U ((hvA _).1 ((eA _).1 h1))
    subst e
    refine ⟨vA₁, (hvA _).2 rfl, fun q => (hg q).trans ?_⟩
    exact exists_congr fun a => ⟨fun ⟨ha, vb, h2, h3⟩ => ⟨ha, vb, (eb a ha _).1 h2, h3⟩,
      fun ⟨ha, vb, h2, h3⟩ => ⟨ha, vb, (eb a ha _).2 h2, h3⟩⟩

theorem eq_congrLamProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {A A' b b' B : Term}
    (hA : PEq hM Γ A A' (univ i) (i + 1)) (hb : PEq hM (Γ.snoc A i) b b' B 0)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) :
    PEq hM Γ (lam .prop i 0 A b) (lam .prop i 0 A' b') (pi .prop i 0 A B) 0 := by
  refine ⟨case_lamProp hM hA.1 hb.1 hcA hcB, fun η hv w => ?_⟩
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_lam_prop, Val_lam_prop]

theorem eq_congrAppData {m : ℕ} {Γ : Ctx m} {i j : ℕ} {f f' a a' A B : Term} (hj : 1 ≤ j)
    (hf : PEq hM Γ f f' (pi .data i j A B) (max i j)) (ha : PEq hM Γ a a' A i)
    (hcf : f.cls Γ = max i j) (hcf' : f'.cls Γ = max i j) (hca : a.cls Γ = i) (hca' : a'.cls Γ = i)
    (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = j + 1) :
    PEq hM Γ (app .data j f a) (app .data j f' a') (Term.subst m a 0 B) j := by
  refine ⟨case_appData hM hj hf.1 ha.1 hcf hca hcA hcB, fun η hv w => ?_⟩
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_app_data' M.T hcf hca (le_max_right i j) (le_max_left i j),
    Val_app_data' M.T hcf' hca' (le_max_right i j) (le_max_left i j)]
  exact exists_congr fun vf => exists_congr fun va =>
    and_congr (hf.2 η hv _) (and_congr (ha.2 η hv _) Iff.rfl)

theorem eq_congrAppProp {m : ℕ} {Γ : Ctx m} {i : ℕ} {f f' a a' A B : Term}
    (hf : PEq hM Γ f f' (pi .prop i 0 A B) 0) (ha : PEq hM Γ a a' A i)
    (hca : a.cls Γ = i) (hcA : A.cls Γ = i + 1) (hcB : B.cls (Γ.snoc A i) = 1) :
    PEq hM Γ (app .prop 0 f a) (app .prop 0 f' a') (Term.subst m a 0 B) 0 := by
  refine ⟨case_appProp hM hf.1 ha.1 hca hcA hcB, fun η hv w => ?_⟩
  refine Val_sort_iff M.T Γ Γ _ _ η η w rfl (fun w' => ?_)
  rw [Val_app_prop, Val_app_prop]

theorem eq_congrLet {m : ℕ} {Γ : Ctx m} {i j : ℕ} {v v' A b b' B : Term}
    (hv : PEq hM Γ v v' A i) (hb : PEq hM (Γ.snoc A i) b b' B j)
    (hcv : v.cls Γ = i) (hcv' : v'.cls Γ = i) (hcb : b.cls (Γ.snoc A i) = j)
    (hcb' : b'.cls (Γ.snoc A i) = j) :
    PEq hM Γ (letE j A v b) (letE j A v' b') (Term.subst m v 0 B) j := by
  refine ⟨case_letE hM hv.1 hb.1 hcv hcb, fun η hη w => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hv.1 η hη
  obtain ⟨vv, hvv, -⟩ := PTy.term_val hM hv.1 hη
  have hvalid := Valid.snoc hM hη (M.T.inj vv) h2 h3 (fun vA hvA => h4 _ vA ((hvv _).2 rfl) hvA)
  have hcb₁ : b.cls (Γ.snoc A (v.cls Γ)) = j := by rw [hcv]; exact hcb
  have hcb₂ : b'.cls (Γ.snoc A (v'.cls Γ)) = j := by rw [hcv']; exact hcb'
  rw [Val_let M.T hcb₁, Val_let M.T hcb₂]
  simp only [hcv, hcv', hvv, ← hv.2 η hη]
  constructor
  · rintro ⟨_, rfl, h⟩; exact ⟨_, rfl, (hb.2 _ hvalid w).1 h⟩
  · rintro ⟨_, rfl, h⟩; exact ⟨_, rfl, (hb.2 _ hvalid w).2 h⟩

theorem eq_weak {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : PEq hM Γ t s A r) (B : Term)
    (l : ℕ) : PEq hM (Γ.snoc B l) (Term.shift m 1 t) (Term.shift m 1 s) (Term.shift m 1 A) r := by
  refine ⟨case_weak hM h.1 B l, fun η hv w => ?_⟩
  rw [← Fin.snoc_init_self η]
  simp only [Val_shift1]
  exact h.2 _ (Valid.of_snoc hM hv) w

end SolidLean.Calc
