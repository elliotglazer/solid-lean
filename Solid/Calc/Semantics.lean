module

public import Solid.Calc.Eval
public import Solid.Calc.Typing

/-!
# The value relation and its reading, constructor by constructor

`Val Γ t η w` reads the evaluator formula `eval Γ t` in a tower `T` at an
environment `η` (a tuple of elements of the union) and a value `w`, and
records that `w` has the sort of the classifier.  The lemmas `Val_*` unfold
it for each constructor into ordinary set-theoretic statements about `T`,
which is what the soundness proof works with.
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

local notation "cs" => Fin.castSucc

variable (T : MemTower.{u})

/-- Environments: tuples of elements of the union. -/
abbrev Env (m : ℕ) := Fin m → T.El

/-- An environment has the sorts declared by the context. -/
def EnvOk {m : ℕ} (Γ : Ctx m) (η : Env T m) : Prop := ∀ i, (η i).1 = Γ.levels i

theorem EnvOk.snoc {m : ℕ} {Γ : Ctx m} {η : Env T m} (h : EnvOk T Γ η) {A : Term} {i : ℕ}
    {x : T.El} (hx : x.1 = i) : EnvOk T (Γ.snoc A i) (Fin.snoc η x) := by
  intro l
  rw [Ctx.levels_snoc]
  refine Fin.lastCases ?_ (fun l => ?_) l
  · simp [hx]
  · simp [h l]

theorem EnvOk.of_snoc {m : ℕ} {Γ : Ctx m} {η : Env T m} {A : Term} {i : ℕ} {x : T.El}
    (h : EnvOk T (Γ.snoc A i) (Fin.snoc η x)) : EnvOk T Γ η ∧ x.1 = i := by
  constructor
  · intro l
    have := h (cs l)
    rw [Ctx.levels_snoc] at this
    simpa using this
  · have := h (Fin.last m)
    rw [Ctx.levels_snoc] at this
    simpa using this

/-- The value relation: `w` is the value of `t` at `η`. -/
def Val {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) (w : T.El) : Prop :=
  w.1 = t.cls Γ ∧ (eval Γ t).Sat T.toStr (Fin.snoc (α := fun _ => T.El) η w)

theorem Val.sort {m : ℕ} {Γ : Ctx m} {t : Term} {η : Env T m} {w : T.El} (h : Val T Γ t η w) :
    w.1 = t.cls Γ := h.1

theorem Val_inj_iff {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) (w : T.U (t.cls Γ)) :
    Val T Γ t η (T.inj w) ↔ (eval Γ t).Sat T.toStr (Fin.snoc (α := fun _ => T.El) η (T.inj w)) := by
  simp [Val]

theorem Val_inj_iff' {m : ℕ} (Γ : Ctx m) (t : Term) (η : Env T m) {n : ℕ} (hn : t.cls Γ = n)
    (w : T.U n) :
    Val T Γ t η (T.inj w) ↔ (eval Γ t).Sat T.toStr (Fin.snoc (α := fun _ => T.El) η (T.inj w)) := by
  subst hn; exact Val_inj_iff T Γ t η w

/-! ### Element-level readings of the atoms -/

section Atoms

variable {k : ℕ} {s : Fin k → ℕ}

theorem Sat_memF' {n : ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n} (t : Fin k → T.El) :
    (memF n i j hi hj).Sat T.toStr t ↔ ∃ x y : T.U n, t i = T.inj x ∧ t j = T.inj y ∧ T.mem x y := by
  show ![t i, t j] ∈ T.memRel n ↔ _
  exact Iff.rfl

theorem Sat_liftZF' {n : ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n + 1} (t : Fin k → T.El) :
    (liftZF n i j hi hj).Sat T.toStr t ↔ ∃ x : T.U n, t i = T.inj x ∧ t j = T.inj (T.j n x) := by
  show ![t i, t j] ∈ T.jRel n ↔ _
  exact Iff.rfl

theorem Sat_liftNF' {n d : ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n + d} (t : Fin k → T.El)
    (hti : (t i).1 = n) :
    (liftNF n d i j hi hj).Sat T.toStr t ↔ t j = T.inj (T.liftN n d (Sorted.toSort T.U (t i) hti)) :=
  Sat_liftNF T n d i j hi hj t _ (Sorted.inj_toSort T.U (t i) hti).symm

theorem Sat_tmemF' {r : ℕ} {i j : Fin k} {hi : s i = r} {hj : s j = r + 1} (t : Fin k → T.El)
    (hti : (t i).1 = r) (htj : (t j).1 = r + 1) :
    (tmemF r i j hi hj).Sat T.toStr t ↔
      T.mem (T.j r (Sorted.toSort T.U (t i) hti)) (Sorted.toSort T.U (t j) htj) :=
  Sat_tmemF T _ _ (Sorted.inj_toSort T.U (t i) hti).symm (Sorted.inj_toSort T.U (t j) htj).symm

/-- Membership between elements of the union, read in a sort. -/
def memEl (x y : T.El) : Prop := ∃ (n : ℕ) (x' y' : T.U n), x = T.inj x' ∧ y = T.inj y' ∧ T.mem x' y'

theorem memEl_inj {n : ℕ} (x y : T.U n) : memEl T (T.inj x) (T.inj y) ↔ T.mem x y := by
  constructor
  · rintro ⟨n', x', y', hx, hy, h⟩
    have hn : n = n' := congrArg Sigma.fst hx
    subst hn
    rw [Sorted.inj_injective T.U hx, Sorted.inj_injective T.U hy]
    exact h
  · intro h; exact ⟨n, x, y, rfl, rfl, h⟩

/-- Sorted tuples from a tuple of the union with known sorts. -/
def sortedOf {a n : ℕ} (u : Fin a → T.El) (hu : ∀ i, (u i).1 = n) : Fin a → T.U n :=
  fun i => Sorted.toSort T.U (u i) (hu i)

theorem inj_sortedOf {a n : ℕ} (u : Fin a → T.El) (hu : ∀ i, (u i).1 = n) :
    (fun i => T.inj (sortedOf T u hu i)) = u := by
  funext i; exact Sorted.inj_toSort T.U (u i) (hu i)

theorem Sat_at' {a n : ℕ} (φ : TF a (fun _ => n)) (v : Fin a → Fin k) (hv : ∀ i, s (v i) = n)
    (t : Fin k → T.El) (ht : ∀ i, (t (v i)).1 = n) :
    (at_ φ v hv).Sat T.toStr t ↔ φ.Sat T.toStr (fun i => T.inj (sortedOf T (fun i => t (v i)) ht i)) := by
  rw [Sat_at, inj_sortedOf]

end Atoms

end SolidLean.Calc

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

local notation "cs" => Fin.castSucc

variable (T : MemTower.{u})

/-! ### Tuples at positions -/

theorem elSort {n : ℕ} (x : T.El) (h : x.1 = n) : ∃ x' : T.U n, x = T.inj x' :=
  ⟨Sorted.toSort T.U x h, (Sorted.inj_toSort T.U x h).symm⟩

theorem exists_inj_mem_iff {n : ℕ} (z w : T.U n) :
    (∃ x y : T.U n, T.inj z = T.inj x ∧ T.inj w = T.inj y ∧ T.mem x y) ↔ T.mem z w := by
  constructor
  · rintro ⟨x, y, hx, hy, h⟩
    rw [Sorted.inj_injective T.U hx, Sorted.inj_injective T.U hy]; exact h
  · intro h; exact ⟨z, w, rfl, rfl, h⟩

theorem exists_inj_lift_iff {n : ℕ} (z : T.U n) (y : T.El) :
    (∃ x : T.U n, T.inj z = T.inj x ∧ y = T.inj (T.j n x)) ↔ y = T.inj (T.j n z) := by
  constructor
  · rintro ⟨x, hx, hy⟩
    rw [Sorted.inj_injective T.U hx]; exact hy
  · intro h; exact ⟨z, rfl, h⟩

theorem tuple1 {k : ℕ} (t : Fin k → T.El) (p : Fin k) {n : ℕ} (x : T.U n) (hx : t p = T.inj x) :
    (fun i => t (![p] i)) = fun i => T.inj (![x] i) := by
  funext i
  match i with
  | 0 => exact hx

theorem tuple2 {k : ℕ} (t : Fin k → T.El) (p q : Fin k) {n : ℕ} (x y : T.U n) (hx : t p = T.inj x)
    (hy : t q = T.inj y) : (fun i => t (![p, q] i)) = fun i => T.inj (![x, y] i) := by
  funext i
  match i with
  | 0 => exact hx
  | 1 => exact hy

theorem tuple3 {k : ℕ} (t : Fin k → T.El) (p q r : Fin k) {n : ℕ} (x y z : T.U n) (hx : t p = T.inj x)
    (hy : t q = T.inj y) (hz : t r = T.inj z) :
    (fun i => t (![p, q, r] i)) = fun i => T.inj (![x, y, z] i) := by
  funext i
  match i with
  | 0 => exact hx
  | 1 => exact hy
  | 2 => exact hz

/-! ### Variables and universes -/

theorem Val_var {m : ℕ} {Γ : Ctx m} {η : Env T m} (hη : EnvOk T Γ η) (x : ℕ) (w : T.El) :
    Val T Γ (.var x) η w ↔ ∃ h : x < m, w = η ⟨x, h⟩ := by
  unfold Val eval
  by_cases h : x < m
  · rw [dif_pos h]
    simp only [Formula.Sat_eq]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, Term.cls_var]
    constructor
    · rintro ⟨-, h2⟩; exact ⟨h, h2.symm⟩
    · rintro ⟨-, rfl⟩
      exact ⟨by rw [hη ⟨x, h⟩]; exact (Γ.lev_of_lt ⟨x, h⟩).symm, rfl⟩
  · rw [dif_neg h]
    simp only [Formula.Sat_false, and_false, false_iff, not_exists]
    intro h'; exact absurd h' h

/-- `u` is the universe `U_n`: the set of truth values for `n = 0`, the set
of all `j²(x)`, `x` of sort `n + 1`, for `n = n' + 1`. -/
def IsUnivSet : (n : ℕ) → T.U (n + 2) → Prop
  | 0, u => ∀ z : T.U 2, T.mem z u ↔ (T.sortStr 2).IsEmptySet z ∨
      ∃ e, (T.sortStr 2).IsEmptySet e ∧ (T.sortStr 2).IsSingleton e z
  | n + 1, u => ∀ z : T.U (n + 3), T.mem z u ↔ ∃ x : T.U (n + 1), z = T.liftN (n + 1) 2 x

theorem Sat_univF {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (w : Fin k) (hw : s w = n + 2) (t : Fin k → T.El)
    (u : T.U (n + 2)) (ht : t w = T.inj u) : (univF n w hw).Sat T.toStr t ↔ IsUnivSet T n u := by
  cases n with
  | zero =>
    unfold univF IsUnivSet
    simp only [Formula.Sat_all, Formula.Sat_iff, Formula.Sat_or, Sat_memF', Sat_at]
    simp only [Fin.snoc_last, Fin.snoc_castSucc, ht]
    constructor
    · intro h z
      have := h (T.inj z) rfl
      rw [exists_inj_mem_iff, tuple1 T _ _ z (by simp), Sat_isEmptyC, Sat_isTrueC] at this
      simpa using this
    · intro h z hz
      obtain ⟨z', rfl⟩ := elSort T z hz
      rw [exists_inj_mem_iff, tuple1 T _ _ z' (by simp), Sat_isEmptyC, Sat_isTrueC]
      simpa using h z'
  | succ n =>
    unfold univF IsUnivSet
    simp only [Formula.Sat_all, Formula.Sat_iff, Formula.Sat_ex, Sat_memF']
    simp only [Fin.snoc_last, Fin.snoc_castSucc, ht]
    constructor
    · intro h z
      have := h (T.inj z) rfl
      rw [exists_inj_mem_iff] at this
      rw [this]
      constructor
      · rintro ⟨x, hx, hl⟩
        obtain ⟨x', rfl⟩ := elSort T x hx
        rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x' (by simp)] at hl
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at hl
        exact ⟨x', Sorted.inj_injective T.U hl⟩
      · rintro ⟨x, rfl⟩
        refine ⟨T.inj x, rfl, ?_⟩
        rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x (by simp)]
        simp
    · intro h z hz
      obtain ⟨z', rfl⟩ := elSort T z hz
      rw [exists_inj_mem_iff, h z']
      constructor
      · rintro ⟨x, rfl⟩
        refine ⟨T.inj x, rfl, ?_⟩
        rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x (by simp)]
        simp
      · rintro ⟨x, hx, hl⟩
        obtain ⟨x', rfl⟩ := elSort T x hx
        rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x' (by simp)] at hl
        simp only [Fin.snoc_castSucc, Fin.snoc_last] at hl
        exact ⟨x', Sorted.inj_injective T.U hl⟩

theorem Val_univ_zero {m : ℕ} (Γ : Ctx m) (η : Env T m) (w : T.U 2) :
    Val T Γ (.univ 0) η (T.inj w) ↔
      ∀ z : T.U 2, T.mem z w ↔ (T.sortStr 2).IsEmptySet z ∨
        ∃ e, (T.sortStr 2).IsEmptySet e ∧ (T.sortStr 2).IsSingleton e z := by
  unfold Val eval univF
  simp only [Formula.Sat_all, Formula.Sat_iff, Formula.Sat_or, Sat_memF', Sat_at]
  simp only [Term.cls_univ, true_and, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h z
    have := h (T.inj z) rfl
    rw [exists_inj_mem_iff, tuple1 T _ _ z (by simp), Sat_isEmptyC, Sat_isTrueC] at this
    simpa using this
  · intro h z hz
    obtain ⟨z', rfl⟩ : ∃ z' : T.U 2, z = T.inj z' :=
      ⟨Sorted.toSort T.U z hz, (Sorted.inj_toSort _ _ _).symm⟩
    rw [exists_inj_mem_iff, tuple1 T _ _ z' (by simp), Sat_isEmptyC, Sat_isTrueC]
    simpa using h z'

/-! ### Renamed subformulas -/

theorem place1_env {m k : ℕ} (t : Fin k → T.El) (f : Fin m → Fin k) (p : Fin k) :
    (fun i => t (place1 f p i)) = Fin.snoc (α := fun _ => T.El) (fun l => t (f l)) (t p) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

theorem place2_env {m k : ℕ} (t : Fin k → T.El) (f : Fin m → Fin k) (p q : Fin k) :
    (fun i => t (place2 f p q i)) =
      Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) (fun l => t (f l)) (t p)) (t q) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp
  · refine Fin.lastCases ?_ (fun i => ?_) i <;> simp

theorem snoc_cs_cs {m : ℕ} (η : Env T m) (a b : T.El) :
    (fun l => Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) η a) b (cs (cs l))) = η := by
  funext l; simp

theorem snoc_cs3 {m : ℕ} (η : Env T m) (a b c : T.El) :
    (fun l => Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
      (Fin.snoc (α := fun _ => T.El) η a) b) c (cs (cs (cs l)))) = η := by
  funext l; simp

theorem snoc_cs4 {m : ℕ} (η : Env T m) (a b c d : T.El) :
    (fun l => Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
      (Fin.snoc (α := fun _ => T.El) η a) b) c) d (cs (cs (cs (cs l))))) = η := by
  funext l; simp

theorem snoc_cs5 {m : ℕ} (η : Env T m) (a b c d e : T.El) :
    (fun l => Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
      (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) η a) b) c) d) e
      (cs (cs (cs (cs (cs l)))))) = η := by
  funext l; simp

/-! ### `let` -/

theorem eval_letE_heq {m : ℕ} {Γ : Ctx m} {j : ℕ} {A v b : Term}
    (hb : b.cls (Γ.snoc A (v.cls Γ)) = j) :
    HEq (eval Γ (.letE j A v b))
      (letF Γ.levels j (v.cls Γ) (eval Γ v)
        (recast (by sorts) (eval (Γ.snoc A (v.cls Γ)) b))) := by
  rw [eval, dif_pos hb]

theorem Val_let {m : ℕ} {Γ : Ctx m} {j : ℕ} {A v b : Term} (hb : b.cls (Γ.snoc A (v.cls Γ)) = j)
    (η : Env T m) (w : T.El) :
    Val T Γ (.letE j A v b) η w ↔
      ∃ vv, Val T Γ v η vv ∧ Val T (Γ.snoc A (v.cls Γ)) b (Fin.snoc η vv) w := by
  unfold Val
  rw [Formula.Sat_heq rfl (eval_letE_heq hb)]
  · unfold letF
    simp only [Formula.Sat_ex, Formula.Sat_and, Formula.sat_rename, Sat_recast, place1_env, place2_env,
      snoc_cs_cs, Fin.snoc_last, Fin.snoc_castSucc, Term.cls_letE]
    constructor
    · rintro ⟨hw, x, hx, h1, h2⟩
      exact ⟨x, ⟨hx, h1⟩, ⟨by rw [hw, hb], h2⟩⟩
    · rintro ⟨x, ⟨hx, h1⟩, ⟨hw, h2⟩⟩
      exact ⟨by rw [hw, hb], x, hx, h1, h2⟩

/-! ### Universes (successor), proof-kind abstractions and applications -/

theorem Val_univ_succ {m : ℕ} (Γ : Ctx m) (η : Env T m) (n : ℕ) (w : T.U (n + 3)) :
    Val T Γ (.univ (n + 1)) η (T.inj w) ↔
      ∀ z : T.U (n + 3), T.mem z w ↔ ∃ x : T.U (n + 1), z = T.liftN (n + 1) 2 x := by
  unfold Val
  rw [eval]
  unfold univF
  simp only [Formula.Sat_all, Formula.Sat_iff, Formula.Sat_ex, Sat_memF']
  simp only [true_and, Fin.snoc_last, Fin.snoc_castSucc]
  constructor
  · intro h z
    have := h (T.inj z) rfl
    rw [exists_inj_mem_iff] at this
    rw [this]
    constructor
    · rintro ⟨x, hx, hl⟩
      obtain ⟨x', rfl⟩ : ∃ x' : T.U (n + 1), x = T.inj x' :=
        ⟨Sorted.toSort T.U x hx, (Sorted.inj_toSort _ _ _).symm⟩
      rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x' (by simp)] at hl
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hl
      exact ⟨x', Sorted.inj_injective T.U hl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨T.inj x, rfl, ?_⟩
      rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x (by simp)]
      simp
  · intro h z hz
    obtain ⟨z', rfl⟩ : ∃ z' : T.U (n + 3), z = T.inj z' :=
      ⟨Sorted.toSort T.U z hz, (Sorted.inj_toSort _ _ _).symm⟩
    rw [exists_inj_mem_iff, h z']
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨T.inj x, rfl, ?_⟩
      rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x (by simp)]
      simp
    · rintro ⟨x, hx, hl⟩
      obtain ⟨x', rfl⟩ : ∃ x' : T.U (n + 1), x = T.inj x' :=
        ⟨Sorted.toSort T.U x hx, (Sorted.inj_toSort _ _ _).symm⟩
      rw [Sat_liftNF T (n + 1) 2 _ _ _ _ _ x' (by simp)] at hl
      simp only [Fin.snoc_castSucc, Fin.snoc_last] at hl
      exact ⟨x', Sorted.inj_injective T.U hl⟩

theorem Val_lam_prop {m : ℕ} (Γ : Ctx m) (η : Env T m) (i j : ℕ) (A b : Term) (w : T.U 0) :
    Val T Γ (.lam .prop i j A b) η (T.inj w) ↔ (T.sortStr 0).IsEmptySet w := by
  unfold Val
  rw [eval, Sat_at, tuple1 T _ _ w (by simp), Sat_isEmptyC]
  simp

theorem Val_app_prop {m : ℕ} (Γ : Ctx m) (η : Env T m) (j : ℕ) (f a : Term) (w : T.U 0) :
    Val T Γ (.app .prop j f a) η (T.inj w) ↔ (T.sortStr 0).IsEmptySet w := by
  unfold Val
  rw [eval, Sat_at, tuple1 T _ _ w (by simp), Sat_isEmptyC]
  simp

/-! ### Data applications -/

theorem eval_app_data_heq {m : ℕ} {Γ : Ctx m} {j : ℕ} {f a : Term} (hj : j ≤ f.cls Γ)
    (ha : a.cls Γ ≤ f.cls Γ) :
    HEq (eval Γ (.app .data j f a))
      (appDataF Γ.levels j (f.cls Γ) (a.cls Γ) hj ha (eval Γ f) (eval Γ a)) := by
  rw [eval, dif_pos hj, dif_pos ha]

theorem Val_app_data {m : ℕ} {Γ : Ctx m} {j : ℕ} {f a : Term} (hj : j ≤ f.cls Γ)
    (ha : a.cls Γ ≤ f.cls Γ) (η : Env T m) (w : T.U j) :
    Val T Γ (.app .data j f a) η (T.inj w) ↔
      ∃ (vf : T.U (f.cls Γ)) (va : T.U (a.cls Γ)), Val T Γ f η (T.inj vf) ∧ Val T Γ a η (T.inj va) ∧
        (T.sortStr (f.cls Γ)).FunApp vf (T.liftLE ha va) (T.liftLE hj w) := by
  simp only [Val_inj_iff]
  rw [Val_inj_iff T Γ (.app .data j f a) η w, Formula.Sat_heq rfl (eval_app_data_heq hj ha)]
  unfold appDataF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.sat_rename, place1_env, snoc_cs_cs, snoc_cs3,
    Fin.snoc_last, Fin.snoc_castSucc, Sat_at]
  constructor
  · rintro ⟨vf, hvf, h1, va, hva, h2, u, hu, h3, v, hv, h4, h5⟩
    obtain ⟨vf', rfl⟩ := elSort T vf hvf
    obtain ⟨va', rfl⟩ := elSort T va hva
    obtain ⟨u', rfl⟩ := elSort T u hu
    obtain ⟨v', rfl⟩ := elSort T v hv
    rw [Sat_liftNF T _ _ _ _ _ _ _ va' (by simp)] at h3
    simp only [Fin.snoc_last] at h3
    rw [T.inj_liftN ha (by omega)] at h3
    rw [Sat_liftNF T _ _ _ _ _ _ _ w (by simp)] at h5
    simp only [Fin.snoc_last] at h5
    rw [T.inj_liftN hj (by omega)] at h5
    rw [tuple3 T _ _ _ _ vf' u' v' (by simp) (by simp) (by simp), Sat_funAppC] at h4
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h4
    refine ⟨vf', va', h1, h2, ?_⟩
    rw [← Sorted.inj_injective T.U h3, ← Sorted.inj_injective T.U h5]
    exact h4
  · rintro ⟨vf', va', h1, h2, h4⟩
    refine ⟨T.inj vf', rfl, h1, T.inj va', rfl, h2, T.inj (T.liftLE ha va'), rfl, ?_,
      T.inj (T.liftLE hj w), rfl, ?_, ?_⟩
    · rw [Sat_liftNF T _ _ _ _ _ _ _ va' (by simp), T.inj_liftN ha (by omega)]; simp
    · rw [tuple3 T _ _ _ _ vf' (T.liftLE ha va') (T.liftLE hj w) (by simp) (by simp) (by simp),
        Sat_funAppC]
      simpa using h4
    · rw [Sat_liftNF T _ _ _ _ _ _ _ w (by simp), T.inj_liftN hj (by omega)]; simp

/-! ### Data abstractions -/

theorem eval_lam_data_heq {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b : Term} (hA : A.cls Γ = i + 1)
    (hb : b.cls (Γ.snoc A i) = j) :
    HEq (eval Γ (.lam .data i j A b))
      (lamDataF Γ.levels i j (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) b))) := by
  rw [eval, dif_pos hA, dif_pos hb]

theorem Sat_lamBodyF {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b : Term}
    (hb : b.cls (Γ.snoc A i) = j) (η : Env T m) (w : T.El) (vA : T.U (i + 1)) (q : T.U (max i j)) :
    (lamBodyF Γ.levels i j (recast (by sorts) (eval (Γ.snoc A i) b))).Sat T.toStr
      (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
        (Fin.snoc (α := fun _ => T.El) η w) (T.inj vA)) (T.inj q)) ↔
      ∃ a : T.U i, T.mem (T.j i a) vA ∧
        ∃ vb : T.U j, Val T (Γ.snoc A i) b (Fin.snoc η (T.inj a)) (T.inj vb) ∧
          (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) a)
            (T.liftLE (le_max_right i j) vb) q := by
  simp only [Val_inj_iff' T (Γ.snoc A i) b _ hb]
  unfold lamBodyF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.sat_rename, Sat_recast, place2_env,
    Fin.snoc_last, Fin.snoc_castSucc, Sat_at]
  constructor
  · rintro ⟨a, ha, h3, u, hu, h4, vb, hvb, h5, v, hv, h6, h7⟩
    obtain ⟨a', rfl⟩ := elSort T a ha
    obtain ⟨u', rfl⟩ := elSort T u hu
    obtain ⟨vb', rfl⟩ := elSort T vb hvb
    obtain ⟨v', rfl⟩ := elSort T v hv
    rw [Sat_tmemF T a' vA (by simp) (by simp)] at h3
    rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp)] at h4
    simp only [Fin.snoc_last] at h4
    rw [T.inj_liftN (le_max_left i j) (by omega)] at h4
    rw [Sat_liftNF T _ _ _ _ _ _ _ vb' (by simp)] at h6
    simp only [Fin.snoc_last] at h6
    rw [T.inj_liftN (le_max_right i j) (by omega)] at h6
    rw [tuple3 T _ _ _ _ u' v' q (by simp) (by simp) (by simp), Sat_ordPairC] at h7
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons] at h7
    refine ⟨a', h3, vb', h5, ?_⟩
    rw [← Sorted.inj_injective T.U h4, ← Sorted.inj_injective T.U h6]
    exact h7
  · rintro ⟨a', h3, vb', h5, h7⟩
    refine ⟨T.inj a', rfl, ?_, T.inj (T.liftLE (le_max_left i j) a'), rfl, ?_, T.inj vb', rfl, h5,
      T.inj (T.liftLE (le_max_right i j) vb'), rfl, ?_, ?_⟩
    · rw [Sat_tmemF T a' vA (by simp) (by simp)]; exact h3
    · rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp), T.inj_liftN (le_max_left i j) (by omega)]; simp
    · rw [Sat_liftNF T _ _ _ _ _ _ _ vb' (by simp), T.inj_liftN (le_max_right i j) (by omega)]; simp
    · rw [tuple3 T _ _ _ _ (T.liftLE (le_max_left i j) a') (T.liftLE (le_max_right i j) vb') q
        (by simp) (by simp) (by simp), Sat_ordPairC]
      simpa using h7

theorem Val_lam_data {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A b : Term} (hA : A.cls Γ = i + 1)
    (hb : b.cls (Γ.snoc A i) = j) (η : Env T m) (w : T.U (max i j)) :
    Val T Γ (.lam .data i j A b) η (T.inj w) ↔
      ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧
        ∀ q : T.U (max i j), T.mem q w ↔ ∃ a : T.U i, T.mem (T.j i a) vA ∧
          ∃ vb : T.U j, Val T (Γ.snoc A i) b (Fin.snoc η (T.inj a)) (T.inj vb) ∧
            (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) a)
              (T.liftLE (le_max_right i j) vb) q := by
  simp only [Val_inj_iff' T Γ A η hA]
  rw [Val_inj_iff T Γ (.lam .data i j A b) η w, Formula.Sat_heq rfl (eval_lam_data_heq hA hb)]
  unfold lamDataF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_iff, Formula.sat_rename,
    Sat_recast, place1_env, Fin.snoc_last, Fin.snoc_castSucc, Sat_at, Sat_memF']
  constructor
  · rintro ⟨vA, hvA, h1, h2⟩
    obtain ⟨vA', rfl⟩ := elSort T vA hvA
    refine ⟨vA', h1, fun q => ?_⟩
    have h2q := h2 (T.inj q) rfl
    rw [exists_inj_mem_iff, Sat_lamBodyF T hb] at h2q
    exact h2q
  · rintro ⟨vA', h1, h2⟩
    refine ⟨T.inj vA', rfl, h1, fun q hq => ?_⟩
    obtain ⟨q', rfl⟩ := elSort T q hq
    rw [exists_inj_mem_iff, Sat_lamBodyF T hb]
    exact h2 q'

/-! ### Proposition-kind products -/

theorem eval_pi_prop_heq {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = 1) :
    HEq (eval Γ (.pi .prop i j A B))
      (Formula.and
        (famOkF Γ.levels i 0 1 (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) B)))
        (piPropF Γ.levels i (recast (by sorts) (eval Γ A)) (recast (by sorts) (eval (Γ.snoc A i) B)))) := by
  rw [eval, dif_pos hA, dif_pos hB]

/-- The family `B` over `A` is well defined: `A` has a unique value, and `B`
has a unique value at every element of it, lying in the universe `U_j`. -/
def FamOk {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) : Prop :=
  ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧ (∀ vA' : T.U (i + 1), Val T Γ A η (T.inj vA') → vA' = vA) ∧
    ∀ a : T.U i, T.mem (T.j i a) vA →
      ∃ vB : T.U (j + 1), Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ∧
        (∀ vB' : T.U (j + 1), Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB') → vB' = vB) ∧
        ∃ u : T.U (j + 2), IsUnivSet T j u ∧ T.mem (T.j (j + 1) vB) u

theorem Sat_famOkF {m : ℕ} {Γ : Ctx m} {i j r : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = j + 1) (η : Env T m) (w : T.El) :
    (famOkF Γ.levels i j r (recast (by sorts) (eval Γ A))
      (recast (by sorts) (eval (Γ.snoc A i) B))).Sat T.toStr (Fin.snoc (α := fun _ => T.El) η w) ↔
      FamOk T Γ i j A B η := by
  unfold famOkF FamOk
  simp only [Val_inj_iff' T Γ A η hA, Val_inj_iff' T (Γ.snoc A i) B _ hB]
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_imp, Formula.Sat_eq,
    Formula.sat_rename, Sat_recast, place1_env, place2_env, Fin.snoc_last, Fin.snoc_castSucc,
    snoc_cs_cs, snoc_cs3, snoc_cs4, snoc_cs5]
  constructor
  · rintro ⟨vA, hvA, h1, h2, h3⟩
    obtain ⟨vA', rfl⟩ := elSort T vA hvA
    refine ⟨vA', h1, fun vA'' h => Sorted.inj_injective T.U (h2 (T.inj vA'') rfl h), fun a ha => ?_⟩
    have := h3 (T.inj a) rfl (by rw [Sat_tmemF T a vA' (by simp) (by simp)]; exact ha)
    obtain ⟨vB, hvB, h4, h5, u, hu, h6, h7⟩ := this
    obtain ⟨vB', rfl⟩ := elSort T vB hvB
    obtain ⟨u', rfl⟩ := elSort T u hu
    refine ⟨vB', h4, fun vB'' h => Sorted.inj_injective T.U (h5 (T.inj vB'') rfl h), u', ?_, ?_⟩
    · rw [Sat_univF T j _ _ _ u' (by simp)] at h6; exact h6
    · rw [Sat_tmemF T vB' u' (by simp) (by simp)] at h7; exact h7
  · rintro ⟨vA', h1, h2, h3⟩
    refine ⟨T.inj vA', rfl, h1, fun x hx h => ?_, fun a ha hmem => ?_⟩
    · obtain ⟨x', rfl⟩ := elSort T x hx
      rw [h2 x' h]
    · obtain ⟨a', rfl⟩ := elSort T a ha
      rw [Sat_tmemF T a' vA' (by simp) (by simp)] at hmem
      obtain ⟨vB', h4, h5, u', h6, h7⟩ := h3 a' hmem
      refine ⟨T.inj vB', rfl, h4, fun y hy h => ?_, T.inj u', rfl, ?_, ?_⟩
      · obtain ⟨y', rfl⟩ := elSort T y hy
        rw [h5 y' h]
      · rw [Sat_univF T j _ _ _ u' (by simp)]; exact h6
      · rw [Sat_tmemF T vB' u' (by simp) (by simp)]; exact h7

/-- The truth value of a proposition. -/
def IsTV (n : ℕ) (ψ : Prop) (w : T.U n) : Prop :=
  (ψ → ∃ e, (T.sortStr n).IsEmptySet e ∧ (T.sortStr n).IsSingleton e w) ∧
  (¬ ψ → (T.sortStr n).IsEmptySet w)

theorem Sat_piPropF {m : ℕ} {Γ : Ctx m} {i : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = 1) (η : Env T m) (w : T.U 1) :
    (piPropF Γ.levels i (recast (by sorts) (eval Γ A))
      (recast (by sorts) (eval (Γ.snoc A i) B))).Sat T.toStr
        (Fin.snoc (α := fun _ => T.El) η (T.inj w)) ↔
      ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧
        IsTV T 1 (∀ a : T.U i, T.mem (T.j i a) vA → ∃ vB : T.U 1,
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ∧
            ∃ e, (T.sortStr 1).IsEmptySet e ∧ (T.sortStr 1).IsSingleton e vB) w := by
  simp only [Val_inj_iff' T Γ A η hA, Val_inj_iff' T (Γ.snoc A i) B _ hB]
  unfold piPropF tvF IsTV
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_imp, Formula.Sat_not,
    Formula.sat_rename, Sat_recast, place1_env, place2_env, Fin.snoc_last, Fin.snoc_castSucc, Sat_at,
    Sat_sortF, true_and]
  -- the inner proposition
  have key : ∀ vA' : T.U (i + 1),
      (∀ a : T.El, a.1 = i →
        (tmemF (s := Fin.snoc (Fin.snoc (Fin.snoc Γ.levels 1) (i + 1)) i) i (Fin.last (m + 2))
            (cs (Fin.last (m + 1))) (by simp) (by simp)).Sat T.toStr
          (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
            (Fin.snoc (α := fun _ => T.El) η (T.inj w)) (T.inj vA')) a) →
        ∃ vB : T.El, vB.1 = 1 ∧
          (eval (Γ.snoc A i) B).Sat T.toStr
            (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) η a) vB) ∧
          (isTrueC (IsConst.const 1 1) 0).Sat T.toStr (fun l =>
            Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
              (Fin.snoc (α := fun _ => T.El) η (T.inj w)) (T.inj vA')) a) vB (![Fin.last (m + 3)] l))) ↔
      (∀ a : T.U i, T.mem (T.j i a) vA' → ∃ vB : T.U 1,
        (eval (Γ.snoc A i) B).Sat T.toStr
          (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) η (T.inj a)) (T.inj vB)) ∧
          ∃ e, (T.sortStr 1).IsEmptySet e ∧ (T.sortStr 1).IsSingleton e vB) := by
    intro vA'
    constructor
    · intro h a ha
      have := h (T.inj a) rfl (by rw [Sat_tmemF T a vA' (by simp) (by simp)]; exact ha)
      obtain ⟨vB, hvB, h1, h2⟩ := this
      obtain ⟨vB', rfl⟩ := elSort T vB hvB
      rw [tuple1 T _ _ vB' (by simp), Sat_isTrueC] at h2
      exact ⟨vB', h1, by simpa using h2⟩
    · intro h a ha hmem
      obtain ⟨a', rfl⟩ := elSort T a ha
      rw [Sat_tmemF T a' vA' (by simp) (by simp)] at hmem
      obtain ⟨vB', h1, h2⟩ := h a' hmem
      refine ⟨T.inj vB', rfl, h1, ?_⟩
      rw [tuple1 T _ _ vB' (by simp), Sat_isTrueC]
      simpa using h2
  constructor
  · rintro ⟨vA, hvA, h1, h2, h3⟩
    obtain ⟨vA', rfl⟩ := elSort T vA hvA
    refine ⟨vA', h1, ?_, ?_⟩
    · intro hψ
      have := h2 ((key vA').2 hψ)
      rw [tuple1 T _ _ w (by simp), Sat_isTrueC] at this
      simpa using this
    · intro hψ
      have := h3 (fun h => hψ ((key vA').1 h))
      rw [tuple1 T _ _ w (by simp), Sat_isEmptyC] at this
      simpa using this
  · rintro ⟨vA', h1, h2, h3⟩
    refine ⟨T.inj vA', rfl, h1, ?_, ?_⟩
    · intro hψ
      rw [tuple1 T _ _ w (by simp), Sat_isTrueC]
      simpa using h2 ((key vA').1 hψ)
    · intro hψ
      rw [tuple1 T _ _ w (by simp), Sat_isEmptyC]
      simpa using h3 (fun h => hψ ((key vA').2 h))

theorem Val_pi_prop {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = 1) (η : Env T m) (w : T.U 1) :
    Val T Γ (.pi .prop i j A B) η (T.inj w) ↔
      FamOk T Γ i 0 A B η ∧
      ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧
        IsTV T 1 (∀ a : T.U i, T.mem (T.j i a) vA → ∃ vB : T.U 1,
          Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ∧
            ∃ e, (T.sortStr 1).IsEmptySet e ∧ (T.sortStr 1).IsSingleton e vB) w := by
  rw [Val_inj_iff T Γ (.pi .prop i j A B) η w, Formula.Sat_heq rfl (eval_pi_prop_heq hA hB),
    Formula.Sat_and, Sat_famOkF T hA hB, Sat_piPropF T hA hB]

/-! ### Data products -/

theorem eval_pi_data_heq {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = j + 1) :
    HEq (eval Γ (.pi .data i j A B))
      (Formula.and
        (famOkF Γ.levels i j (max i j + 1) (recast (by sorts) (eval Γ A))
          (recast (by sorts) (eval (Γ.snoc A i) B)))
        (piDataF Γ.levels i j (recast (by sorts) (eval Γ A))
          (recast (by sorts) (eval (Γ.snoc A i) B)))) := by
  rw [eval, dif_pos hA, dif_pos hB]

/-- The dependent product condition on a function `f` of sort `max i j`: its
domain is the lift of the elements of `A`, and its values at `a` lie in the
lift of `B(a)`. -/
def IsPiFun {m : ℕ} (Γ : Ctx m) (i j : ℕ) (A B : Term) (η : Env T m) (vA : T.U (i + 1))
    (f : T.U (max i j)) : Prop :=
  (T.sortStr (max i j)).IsFunction f ∧
  (∀ u : T.U (max i j), (T.sortStr (max i j)).InDom f u ↔
    ∃ a : T.U i, T.mem (T.j i a) vA ∧ u = T.liftLE (le_max_left i j) a) ∧
  (∀ a : T.U i, T.mem (T.j i a) vA → ∀ v : T.U (max i j),
    (T.sortStr (max i j)).FunApp f (T.liftLE (le_max_left i j) a) v →
    ∃ vB : T.U (j + 1), Val T (Γ.snoc A i) B (Fin.snoc η (T.inj a)) (T.inj vB) ∧
      ∃ b : T.U j, T.mem (T.j j b) vB ∧ v = T.liftLE (le_max_right i j) b)

theorem Sat_piBodyF {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term}
    (hB : B.cls (Γ.snoc A i) = j + 1) (η : Env T m) (w p : T.El) (vA' : T.U (i + 1))
    (f : T.U (max i j)) :
    (piBodyF Γ.levels i j (recast (by sorts) (eval (Γ.snoc A i) B))).Sat T.toStr
      (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El) (Fin.snoc (α := fun _ => T.El)
        (Fin.snoc (α := fun _ => T.El) η w) (T.inj vA')) p) (T.inj f)) ↔
      IsPiFun T Γ i j A B η vA' f := by
  unfold IsPiFun
  simp only [Val_inj_iff' T (Γ.snoc A i) B _ hB]
  unfold piBodyF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_iff, Formula.Sat_imp,
    Formula.sat_rename, Sat_recast, place2_env, Fin.snoc_last, Fin.snoc_castSucc, Sat_at]
  rw [tuple1 T _ _ f (by simp), Sat_isFunC]
  simp only [Matrix.cons_val_zero]
  refine and_congr Iff.rfl (and_congr ?_ ?_)
  · -- domain clause
    constructor
    · intro h u
      have hu := h (T.inj u) rfl
      rw [tuple2 T _ _ _ f u (by simp) (by simp), Sat_inDomC] at hu
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hu
      rw [hu]
      constructor
      · rintro ⟨a, ha, h4, h5⟩
        obtain ⟨a', rfl⟩ := elSort T a ha
        rw [Sat_tmemF T a' vA' (by simp) (by simp)] at h4
        rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp)] at h5
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at h5
        rw [T.inj_liftN (le_max_left i j) (by omega)] at h5
        exact ⟨a', h4, Sorted.inj_injective T.U h5⟩
      · rintro ⟨a', h4, rfl⟩
        refine ⟨T.inj a', rfl, ?_, ?_⟩
        · rw [Sat_tmemF T a' vA' (by simp) (by simp)]; exact h4
        · rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp), T.inj_liftN (le_max_left i j) (by omega)]; simp
    · intro h u hu
      obtain ⟨u', rfl⟩ := elSort T u hu
      rw [tuple2 T _ _ _ f u' (by simp) (by simp), Sat_inDomC]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [h u']
      constructor
      · rintro ⟨a', h4, rfl⟩
        refine ⟨T.inj a', rfl, ?_, ?_⟩
        · rw [Sat_tmemF T a' vA' (by simp) (by simp)]; exact h4
        · rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp), T.inj_liftN (le_max_left i j) (by omega)]; simp
      · rintro ⟨a, ha, h4, h5⟩
        obtain ⟨a', rfl⟩ := elSort T a ha
        rw [Sat_tmemF T a' vA' (by simp) (by simp)] at h4
        rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp)] at h5
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at h5
        rw [T.inj_liftN (le_max_left i j) (by omega)] at h5
        exact ⟨a', h4, Sorted.inj_injective T.U h5⟩
  · -- range clause
    constructor
    · intro h a' ha v hv
      have := h (T.inj a') rfl (by rw [Sat_tmemF T a' vA' (by simp) (by simp)]; exact ha)
        (T.inj (T.liftLE (le_max_left i j) a')) rfl
        (by rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp), T.inj_liftN (le_max_left i j) (by omega)]; simp)
        (T.inj v) rfl
        (by rw [tuple3 T _ _ _ _ f (T.liftLE (le_max_left i j) a') v (by simp) (by simp) (by simp),
              Sat_funAppC]; simpa using hv)
      obtain ⟨vB, hvB, h4, b, hb, h5, h6⟩ := this
      obtain ⟨vB', rfl⟩ := elSort T vB hvB
      obtain ⟨b', rfl⟩ := elSort T b hb
      rw [Sat_tmemF T b' vB' (by simp) (by simp)] at h5
      rw [Sat_liftNF T _ _ _ _ _ _ _ b' (by simp)] at h6
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at h6
      rw [T.inj_liftN (le_max_right i j) (by omega)] at h6
      exact ⟨vB', h4, b', h5, Sorted.inj_injective T.U h6⟩
    · intro h a ha h4 u hu h5 v hv h6
      obtain ⟨a', rfl⟩ := elSort T a ha
      obtain ⟨u', rfl⟩ := elSort T u hu
      obtain ⟨v', rfl⟩ := elSort T v hv
      rw [Sat_tmemF T a' vA' (by simp) (by simp)] at h4
      rw [Sat_liftNF T _ _ _ _ _ _ _ a' (by simp)] at h5
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at h5
      rw [T.inj_liftN (le_max_left i j) (by omega)] at h5
      rw [tuple3 T _ _ _ _ f u' v' (by simp) (by simp) (by simp), Sat_funAppC] at h6
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons] at h6
      rw [Sorted.inj_injective T.U h5] at h6
      obtain ⟨vB', h7, b', h8, rfl⟩ := h a' h4 v' h6
      refine ⟨T.inj vB', rfl, h7, T.inj b', rfl, ?_, ?_⟩
      · rw [Sat_tmemF T b' vB' (by simp) (by simp)]; exact h8
      · rw [Sat_liftNF T _ _ _ _ _ _ _ b' (by simp), T.inj_liftN (le_max_right i j) (by omega)]; simp

theorem Sat_piDataF {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = j + 1) (η : Env T m) (w : T.U (max i j + 1)) :
    (piDataF Γ.levels i j (recast (by sorts) (eval Γ A))
      (recast (by sorts) (eval (Γ.snoc A i) B))).Sat T.toStr
        (Fin.snoc (α := fun _ => T.El) η (T.inj w)) ↔
      ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧ ∃ p : T.U (max i j), w = T.j (max i j) p ∧
        ∀ f : T.U (max i j), T.mem f p ↔ IsPiFun T Γ i j A B η vA f := by
  simp only [Val_inj_iff' T Γ A η hA]
  unfold piDataF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_iff,
    Formula.sat_rename, Sat_recast, place1_env, Fin.snoc_last, Fin.snoc_castSucc, Sat_memF', Sat_liftZF']
  constructor
  · rintro ⟨vA, hvA, h1, p, hp, h2, h3⟩
    obtain ⟨vA', rfl⟩ := elSort T vA hvA
    obtain ⟨p', rfl⟩ := elSort T p hp
    rw [exists_inj_lift_iff] at h2
    refine ⟨vA', h1, p', Sorted.inj_injective T.U h2, fun f => ?_⟩
    have h3f := h3 (T.inj f) rfl
    rw [exists_inj_mem_iff, Sat_piBodyF T hB] at h3f
    exact h3f
  · rintro ⟨vA', h1, p', rfl, h3⟩
    refine ⟨T.inj vA', rfl, h1, T.inj p', rfl, ?_, fun f hf => ?_⟩
    · rw [exists_inj_lift_iff]
    obtain ⟨f', rfl⟩ := elSort T f hf
    rw [exists_inj_mem_iff, Sat_piBodyF T hB]
    exact h3 f'

theorem Val_pi_data {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (hA : A.cls Γ = i + 1)
    (hB : B.cls (Γ.snoc A i) = j + 1) (η : Env T m) (w : T.U (max i j + 1)) :
    Val T Γ (.pi .data i j A B) η (T.inj w) ↔
      FamOk T Γ i j A B η ∧
      ∃ vA : T.U (i + 1), Val T Γ A η (T.inj vA) ∧ ∃ p : T.U (max i j), w = T.j (max i j) p ∧
        ∀ f : T.U (max i j), T.mem f p ↔ IsPiFun T Γ i j A B η vA f := by
  rw [Val_inj_iff T Γ (.pi .data i j A B) η w, Formula.Sat_heq rfl (eval_pi_data_heq hA hB),
    Formula.Sat_and, Sat_famOkF T hA hB, Sat_piDataF T hA hB]

end SolidLean.Calc
