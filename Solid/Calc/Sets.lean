import Solid.Calc.Definability
import Solid.Lift

/-!
# The sets the evaluator needs, in a model of `H`

Existence and uniqueness of the universes `U_n`, of truth values, of
dependent products and of graphs, in the sort models of a tower model, and
the facts about universes that the soundness argument uses: the values of
types are `j`-images, and level-`0` values are the empty set.
-/

universe u

open Classical

namespace SolidLean.Solid.IsTowerModel

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

include hM in
theorem ext_of_iff {n : ℕ} {P : M.T.U n → Prop} {w w' : M.T.U n}
    (h : ∀ z, M.T.mem z w ↔ P z) (h' : ∀ z, M.T.mem z w' ↔ P z) : w = w' :=
  (hM.zfc n).ext w w' (fun z => (h z).trans (h' z).symm)

include hM in
/-- Membership in a `j`-image. -/
theorem mem_j_iff (n : ℕ) (x : M.T.U n) (z : M.T.U (n + 1)) :
    M.T.mem z (M.T.j n x) ↔ ∃ y, M.T.mem y x ∧ M.T.j n y = z :=
  (hM.jEmb n).mem_image_iff x z

include hM in
/-- Membership in a lift. -/
theorem mem_liftLE_iff {a b : ℕ} (h : a ≤ b) (x : M.T.U a) (z : M.T.U b) :
    M.T.mem z (M.T.liftLE h x) ↔ ∃ y, M.T.mem y x ∧ M.T.liftLE h y = z :=
  (hM.liftEmb h).mem_image_iff x z

/-! ### Empty sets and singletons -/

/-- The empty set of sort `n`. -/
noncomputable def emptyAt (n : ℕ) : M.T.U n := Classical.choose (hM.zfc n).empty

theorem emptyAt_spec (n : ℕ) : (M.T.sortStr n).IsEmptySet (hM.emptyAt n) :=
  Classical.choose_spec (hM.zfc n).empty

theorem eq_emptyAt {n : ℕ} {e : M.T.U n} (he : (M.T.sortStr n).IsEmptySet e) : e = hM.emptyAt n :=
  (hM.sortModel n).empty_unique he (hM.emptyAt_spec n)

theorem j_emptyAt (n : ℕ) : M.T.j n (hM.emptyAt n) = hM.emptyAt (n + 1) :=
  hM.eq_emptyAt (((hM.jEmb n).isEmptySet_iff _).2 (hM.emptyAt_spec n))

theorem not_mem_emptyAt {n : ℕ} (z : M.T.U n) : ¬ M.T.mem z (hM.emptyAt n) := hM.emptyAt_spec n z

/-- The singleton `{a}` of sort `n`. -/
noncomputable def singAt {n : ℕ} (a : M.T.U n) : M.T.U n :=
  Classical.choose ((hM.sortModel n).exists_singleton a)

theorem singAt_spec {n : ℕ} (a : M.T.U n) : (M.T.sortStr n).IsSingleton a (hM.singAt a) :=
  Classical.choose_spec ((hM.sortModel n).exists_singleton a)

theorem mem_singAt {n : ℕ} (a z : M.T.U n) : M.T.mem z (hM.singAt a) ↔ z = a := hM.singAt_spec a z

theorem eq_singAt {n : ℕ} {a s : M.T.U n} (hs : (M.T.sortStr n).IsSingleton a s) : s = hM.singAt a :=
  (hM.sortModel n).singleton_unique hs (hM.singAt_spec a)

theorem j_singAt {n : ℕ} (a : M.T.U n) : M.T.j n (hM.singAt a) = hM.singAt (M.T.j n a) :=
  hM.eq_singAt (((hM.jEmb n).isSingleton_iff a _).2 (hM.singAt_spec a))

/-! ### Universes -/

/-- The universe `U_n`, a set of sort `n + 2`. -/
noncomputable def univSet : (n : ℕ) → M.T.U (n + 2)
  | 0 => Classical.choose ((hM.zfc 2).pair (hM.emptyAt 2) (hM.singAt (hM.emptyAt 2)))
  | n + 1 => M.T.j (n + 2) (hM.imageSet (n + 1))

theorem mem_univSet_zero (z : M.T.U 2) :
    M.T.mem z (hM.univSet 0) ↔ z = hM.emptyAt 2 ∨ z = hM.singAt (hM.emptyAt 2) :=
  Classical.choose_spec ((hM.zfc 2).pair (hM.emptyAt 2) (hM.singAt (hM.emptyAt 2))) z

theorem mem_univSet_succ (n : ℕ) (z : M.T.U (n + 3)) :
    M.T.mem z (hM.univSet (n + 1)) ↔ ∃ x : M.T.U (n + 1), z = M.T.liftN (n + 1) 2 x := by
  show M.T.mem z (M.T.j (n + 2) (hM.imageSet (n + 1))) ↔ _
  rw [hM.mem_j_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (hM.mem_imageSet_iff _ y).1 hy
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨M.T.j (n + 1) x, (hM.mem_imageSet_iff _ _).2 ⟨x, rfl⟩, rfl⟩

theorem univ0_char (z : M.T.U 2) :
    ((M.T.sortStr 2).IsEmptySet z ∨
      ∃ e, (M.T.sortStr 2).IsEmptySet e ∧ (M.T.sortStr 2).IsSingleton e z) ↔
    z = hM.emptyAt 2 ∨ z = hM.singAt (hM.emptyAt 2) := by
  constructor
  · rintro (hz | ⟨e, he, hz⟩)
    · exact Or.inl (hM.eq_emptyAt hz)
    · right
      rw [hM.eq_emptyAt he] at hz
      exact hM.eq_singAt hz
  · rintro (rfl | rfl)
    · exact Or.inl (hM.emptyAt_spec 2)
    · exact Or.inr ⟨_, hM.emptyAt_spec 2, hM.singAt_spec _⟩

theorem isUnivSet_iff (n : ℕ) (u : M.T.U (n + 2)) :
    Calc.IsUnivSet M.T n u ↔ u = hM.univSet n := by
  cases n with
  | zero =>
    show (∀ z : M.T.U 2, M.T.mem z u ↔ _) ↔ _
    constructor
    · intro h
      exact hM.ext_of_iff (fun z => (h z).trans (hM.univ0_char z)) (hM.mem_univSet_zero)
    · rintro rfl z
      rw [hM.mem_univSet_zero, hM.univ0_char]
  | succ n =>
    show (∀ z : M.T.U (n + 3), M.T.mem z u ↔ _) ↔ _
    constructor
    · intro h
      exact hM.ext_of_iff h (hM.mem_univSet_succ n)
    · rintro rfl z
      exact hM.mem_univSet_succ n z

/-- `U_n` is a `j`-image. -/
theorem univSet_eq_j (n : ℕ) : ∃ x : M.T.U (n + 1), hM.univSet n = M.T.j (n + 1) x := by
  cases n with
  | zero =>
    obtain ⟨x, hx⟩ := (hM.zfc 1).pair (hM.emptyAt 1) (hM.singAt (hM.emptyAt 1))
    refine ⟨x, hM.ext_of_iff (hM.mem_univSet_zero) (fun z => ?_)⟩
    rw [hM.mem_j_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases (hx y).1 hy with rfl | rfl
      · exact Or.inl (hM.j_emptyAt 1)
      · right; rw [hM.j_singAt, hM.j_emptyAt]
    · rintro (rfl | rfl)
      · exact ⟨hM.emptyAt 1, (hx _).2 (Or.inl rfl), hM.j_emptyAt 1⟩
      · exact ⟨hM.singAt (hM.emptyAt 1), (hx _).2 (Or.inr rfl), by rw [hM.j_singAt, hM.j_emptyAt]⟩
  | succ n => exact ⟨hM.imageSet (n + 1), rfl⟩

theorem univSet_mem (n : ℕ) : M.T.mem (M.T.j (n + 2) (hM.univSet n)) (hM.univSet (n + 1)) := by
  obtain ⟨x, hx⟩ := hM.univSet_eq_j n
  rw [hM.mem_univSet_succ]
  exact ⟨x, by rw [hx]; rfl⟩

/-- The values of types are `j`-images. -/
theorem exists_j_of_mem_univSet {i : ℕ} (vA : M.T.U (i + 1))
    (h : M.T.mem (M.T.j (i + 1) vA) (hM.univSet i)) : ∃ vA' : M.T.U i, vA = M.T.j i vA' := by
  cases i with
  | zero =>
    rcases (hM.mem_univSet_zero _).1 h with h1 | h1
    · refine ⟨hM.emptyAt 0, hM.j_injective 1 _ _ ?_⟩
      rw [h1, hM.j_emptyAt, hM.j_emptyAt]
    · refine ⟨hM.singAt (hM.emptyAt 0), hM.j_injective 1 _ _ ?_⟩
      rw [h1, hM.j_singAt, hM.j_singAt, hM.j_emptyAt, hM.j_emptyAt]
  | succ n =>
    obtain ⟨x, hx⟩ := (hM.mem_univSet_succ n _).1 h
    exact ⟨x, hM.j_injective (n + 2) _ _ hx⟩

/-- A `j`-image of a set of sort `n + 1` lies in `U_{n+1}`. -/
theorem j_j_mem_univSet_succ (n : ℕ) (x : M.T.U (n + 1)) :
    M.T.mem (M.T.j (n + 2) (M.T.j (n + 1) x)) (hM.univSet (n + 1)) :=
  (hM.mem_univSet_succ n _).2 ⟨x, rfl⟩

/-! ### Level `0`: truth values -/

theorem tv_char {vP : M.T.U 1} (h : M.T.mem (M.T.j 1 vP) (hM.univSet 0)) :
    vP = hM.emptyAt 1 ∨ vP = hM.singAt (hM.emptyAt 1) := by
  rcases (hM.mem_univSet_zero _).1 h with h1 | h1
  · left
    exact hM.j_injective 1 _ _ (by rw [h1, hM.j_emptyAt])
  · right
    exact hM.j_injective 1 _ _ (by rw [h1, hM.j_singAt, hM.j_emptyAt])

/-- An element of a proposition is the empty set. -/
theorem eq_emptyAt_of_mem {vP : M.T.U 1} (h : M.T.mem (M.T.j 1 vP) (hM.univSet 0)) {w : M.T.U 0}
    (hw : M.T.mem (M.T.j 0 w) vP) : w = hM.emptyAt 0 := by
  rcases hM.tv_char h with rfl | rfl
  · exact absurd hw (hM.not_mem_emptyAt _)
  · rw [hM.mem_singAt] at hw
    exact hM.j_injective 0 _ _ (by rw [hw, hM.j_emptyAt])

/-- The truth value of a proposition, as a set of sort `1`. -/
noncomputable def tvSet (ψ : Prop) : M.T.U 1 :=
  if ψ then hM.singAt (hM.emptyAt 1) else hM.emptyAt 1

theorem isTV_iff (ψ : Prop) (w : M.T.U 1) : Calc.IsTV M.T 1 ψ w ↔ w = hM.tvSet ψ := by
  unfold Calc.IsTV tvSet
  by_cases hψ : ψ
  · rw [if_pos hψ]
    constructor
    · rintro ⟨h1, -⟩
      obtain ⟨e, he, hw⟩ := h1 hψ
      rw [hM.eq_emptyAt he] at hw
      exact hM.eq_singAt hw
    · rintro rfl
      exact ⟨fun _ => ⟨_, hM.emptyAt_spec 1, hM.singAt_spec _⟩, fun h => absurd hψ h⟩
  · rw [if_neg hψ]
    constructor
    · rintro ⟨-, h2⟩
      exact hM.eq_emptyAt (h2 hψ)
    · rintro rfl
      exact ⟨fun h => absurd h hψ, fun _ => hM.emptyAt_spec 1⟩

theorem tvSet_mem_univSet (ψ : Prop) : M.T.mem (M.T.j 1 (hM.tvSet ψ)) (hM.univSet 0) := by
  rw [hM.mem_univSet_zero]
  unfold tvSet
  split_ifs
  · right; rw [hM.j_singAt, hM.j_emptyAt]
  · left; rw [hM.j_emptyAt]

theorem mem_tvSet (ψ : Prop) : M.T.mem (M.T.j 0 (hM.emptyAt 0)) (hM.tvSet ψ) ↔ ψ := by
  unfold tvSet
  split_ifs with hψ
  · rw [hM.j_emptyAt, hM.mem_singAt]
    exact iff_of_true rfl hψ
  · exact iff_of_false (hM.not_mem_emptyAt _) hψ

/-- A proposition's value is a truth value. -/
theorem eq_tvSet_of_mem_univSet {vP : M.T.U 1} (h : M.T.mem (M.T.j 1 vP) (hM.univSet 0)) :
    vP = hM.tvSet (M.T.mem (M.T.j 0 (hM.emptyAt 0)) vP) := by
  rcases hM.tv_char h with rfl | rfl
  · unfold tvSet
    rw [if_neg (hM.not_mem_emptyAt _)]
  · unfold tvSet
    rw [if_pos (by rw [hM.j_emptyAt, hM.mem_singAt])]

end SolidLean.Solid.IsTowerModel

namespace SolidLean.Calc

open SolidLean.Solid

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### Products and graphs -/

section Pi

variable {m : ℕ} {Γ : Ctx m} {i j : ℕ} {A B : Term} (η : Env M.T m) (vA' : M.T.U i)
  (F : M.T.U i → M.T.U j)

include hM in
/-- The domain of the product: the lift of the elements of `A`. -/
theorem mem_dom_iff (u : M.T.U (max i j)) :
    M.T.mem u (M.T.liftLE (le_max_left i j) vA') ↔
      ∃ a, M.T.mem a vA' ∧ u = M.T.liftLE (le_max_left i j) a := by
  rw [hM.mem_liftLE_iff]
  exact exists_congr (fun a => and_congr Iff.rfl eq_comm)

variable (hF : ∀ a, M.T.mem a vA' → ∀ vB : M.T.U (j + 1),
  Val M.T (Γ.snoc A i) B (Fin.snoc η (M.T.inj a)) (M.T.inj vB) ↔ vB = M.T.j j (F a))

include hM hF in
/-- The codomain bound: the union of the lifts of the `B(a)`. -/
theorem exists_cod : ∃ Cod : M.T.U (max i j), ∀ v, M.T.mem v Cod ↔
    ∃ a, M.T.mem a vA' ∧ ∃ b : M.T.U j, M.T.mem b (F a) ∧ v = M.T.liftLE (le_max_right i j) b := by
  have hR := sortDef_codRel M.𝒟 Γ i j A B η
  obtain ⟨s, hs⟩ := (hM.sortModel (max i j)).replP hR (M.T.liftLE (le_max_left i j) vA') (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := (mem_dom_iff hM vA' x).1 hx
    refine ⟨M.T.liftLE (le_max_right i j) (F a),
      ⟨a, rfl, M.T.j j (F a), (hF a ha _).2 rfl, F a, rfl, rfl⟩, ?_⟩
    rintro y ⟨a', ha', vB, hvB, vB', rfl, rfl⟩
    have e1 := hM.liftLE_injective (le_max_left i j) ha'
    subst e1
    have e2 := (hF a ha _).1 hvB
    rw [hM.j_injective j _ _ e2])
  obtain ⟨Cod, hCod⟩ := (hM.zfc (max i j)).union s
  have hCod' : ∀ z, M.T.mem z Cod ↔ ∃ y, M.T.mem y s ∧ M.T.mem z y := hCod
  refine ⟨Cod, fun v => ?_⟩
  rw [hCod' v]
  constructor
  · rintro ⟨y, hy, hv⟩
    obtain ⟨x, hx, a, rfl, vB, hvB, vB', rfl, rfl⟩ := (hs y).1 hy
    obtain ⟨a', ha', hx'⟩ := (mem_dom_iff hM vA' _).1 hx
    have e1 := hM.liftLE_injective (le_max_left i j) hx'
    subst e1
    have e2 := (hF a ha' _).1 hvB
    rw [hM.j_injective j _ _ e2] at hv
    obtain ⟨b, hb, rfl⟩ := (hM.mem_liftLE_iff _ _ _).1 hv
    exact ⟨a, ha', b, hb, rfl⟩
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨M.T.liftLE (le_max_right i j) (F a), (hs _).2 ⟨M.T.liftLE (le_max_left i j) a,
      (mem_dom_iff hM vA' _).2 ⟨a, ha, rfl⟩, a, rfl, M.T.j j (F a), (hF a ha _).2 rfl, F a, rfl, rfl⟩, ?_⟩
    exact (hM.mem_liftLE_iff _ _ _).2 ⟨b, hb, rfl⟩

include hM hF in
/-- The dependent product, as a set of sort `max i j`. -/
theorem exists_piSet (hB : B.cls (Γ.snoc A i) = j + 1) :
    ∃ p : M.T.U (max i j), ∀ f, M.T.mem f p ↔ IsPiFun M.T Γ i j A B η (M.T.j i vA') f := by
  obtain ⟨Cod, hCod⟩ := exists_cod hM η vA' F hF
  let Z := hM.sortModel (max i j)
  obtain ⟨pr, hpr⟩ := Z.exists_prod (M.T.liftLE (le_max_left i j) vA') Cod
  obtain ⟨pw, hpw⟩ := Z.ax.power pr
  obtain ⟨p, hp⟩ := Z.sepP (sortDef_isPiFun M.𝒟 hB η (M.T.j i vA')) pw
  have hp' : ∀ y, M.T.mem y p ↔ M.T.mem y pw ∧ IsPiFun M.T Γ i j A B η (M.T.j i vA') y := hp
  refine ⟨p, fun f => ?_⟩
  rw [hp' f]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(hpw f).2 (fun q hq => ?_), h⟩
    obtain ⟨hfun, hdom, hrng⟩ := h
    obtain ⟨u, v, huv⟩ := hfun.1 q hq
    have happ : (M.T.sortStr (max i j)).FunApp f u v := ⟨q, hq, huv⟩
    obtain ⟨a, ha, rfl⟩ := (hdom u).1 ⟨v, happ⟩
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    obtain ⟨vB, hvB, b, hb, rfl⟩ := hrng a ha v happ
    have e := (hF a ha' vB).1 hvB
    subst e
    have hb' : M.T.mem b (F a) := (hM.j_mem_iff j b (F a)).1 hb
    exact (hpr q).2 ⟨_, _, (mem_dom_iff hM vA' _).2 ⟨a, ha', rfl⟩, (hCod _).2 ⟨a, ha', b, hb', rfl⟩, huv⟩

include hM in
/-- The graph of an abstraction whose body takes values in the family `F`. -/
theorem exists_lamGraph {b : Term} (hb : b.cls (Γ.snoc A i) = j) (Cod : M.T.U (max i j))
    (hCod : ∀ v, M.T.mem v Cod ↔
      ∃ a, M.T.mem a vA' ∧ ∃ b : M.T.U j, M.T.mem b (F a) ∧ v = M.T.liftLE (le_max_right i j) b)
    (hbv : ∀ a, M.T.mem a vA' → ∀ vb : M.T.U j,
      Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) → M.T.mem vb (F a)) :
    ∃ w : M.T.U (max i j), ∀ q, M.T.mem q w ↔ ∃ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      ∃ vb : M.T.U j, Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q := by
  let Z := hM.sortModel (max i j)
  obtain ⟨pr, hpr⟩ := Z.exists_prod (M.T.liftLE (le_max_left i j) vA') Cod
  have hdef : Z.𝒞.Def 1 (fun t => (fun q => ∃ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      ∃ vb : M.T.U j, Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q) (t 0)) :=
    sortDef_lamBody M.𝒟 hb η (M.T.j i vA')
  obtain ⟨w, hw⟩ := Z.sepP (P := fun q => ∃ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      ∃ vb : M.T.U j, Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q) hdef pr
  have hw' : ∀ q, M.T.mem q w ↔ M.T.mem q pr ∧ ∃ a : M.T.U i, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      ∃ vb : M.T.U j, Val M.T (Γ.snoc A i) b (Fin.snoc η (M.T.inj a)) (M.T.inj vb) ∧
        (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a)
          (M.T.liftLE (le_max_right i j) vb) q := hw
  refine ⟨w, fun q => ?_⟩
  rw [hw' q]
  constructor
  · exact fun h => h.2
  · rintro ⟨a, ha, vb, hvb, hq⟩
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    exact ⟨(hpr q).2 ⟨_, _, (mem_dom_iff hM vA' _).2 ⟨a, ha', rfl⟩,
      (hCod _).2 ⟨a, ha', vb, hbv a ha' vb hvb, rfl⟩, hq⟩, a, ha, vb, hvb, hq⟩

end Pi

end SolidLean.Calc
