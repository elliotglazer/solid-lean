module

public import Solid.Calc.PrimSemantics
public import Solid.Calc.SnocLits
public import Solid.Calc.PrimSimpAttr

/-!
# Reading the clauses of the primitives

For each primitive `c`, the satisfaction of `c.clauseF` at a tuple of values
is unfolded into a set-theoretic statement about the tower.  The readings
are stated for an unsorted tuple `vs` whose entries are known to be
injections of sorted elements (the form in which the soundness proof has
them).

The proofs are uniform: unfold the quantifiers into sorted quantifiers
(`exists_sorted`, `forall_sorted`), evaluate the positions (`snocL_*`), and
read the atoms in their "∃ sorted witnesses" form (`Sat_*'`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid.MemStr

variable (S : MemStr.{u})

/-- `x` is inductive: contains `∅` and is closed under successor. -/
def IsInductive (x : S.X) : Prop :=
  (∃ e, S.IsEmptySet e ∧ S.mem e x) ∧ ∀ y, S.mem y x → ∃ s, S.IsSucc y s ∧ S.mem s x

/-- `o = ω`: the intersection of all inductive sets. -/
def IsOmega (o : S.X) : Prop := ∀ z, S.mem z o ↔ ∀ I, S.IsInductive I → S.mem z I

end SolidLean.Solid.MemStr

namespace SolidLean.Solid.TF

open SolidLean.Solid

variable (T : MemTower.{u})

/-! ### Sorted quantifiers -/

theorem exists_sorted (n : ℕ) (P : T.El → Prop) :
    (∃ x : T.El, x.1 = n ∧ P x) ↔ ∃ x : T.U n, P (T.inj x) := by
  constructor
  · rintro ⟨x, hx, h⟩
    obtain ⟨x', rfl⟩ := Calc.elSort T x hx
    exact ⟨x', h⟩
  · rintro ⟨x, h⟩
    exact ⟨T.inj x, rfl, h⟩

theorem forall_sorted (n : ℕ) (P : T.El → Prop) :
    (∀ x : T.El, x.1 = n → P x) ↔ ∀ x : T.U n, P (T.inj x) := by
  constructor
  · intro h x; exact h (T.inj x) rfl
  · intro h x hx
    obtain ⟨x', rfl⟩ := Calc.elSort T x hx
    exact h x'

@[simp] theorem inj_eq_inj_iff' {n : ℕ} (x y : T.U n) : T.inj x = T.inj y ↔ x = y :=
  ⟨fun h => Sorted.inj_injective T.U h, fun h => by rw [h]⟩

/-! ### Constant-sort atoms: successor, inductive, ω -/

section Const

variable {a : ℕ} {s : Fin a → ℕ} {n : ℕ}

theorem Sat_isSuccC (hs : IsConst s n) (x t : Fin a) (v : Fin a → T.U n) :
    (isSuccC hs x t).Sat T.toStr (fun l => T.inj (v l)) ↔ (T.sortStr n).IsSucc (v x) (v t) := by
  unfold isSuccC
  simp only [Sat_allC, Formula.Sat_iff, Sat_memC, Formula.Sat_or, Sat_eqC, Fin.snoc_last,
    Fin.snoc_castSucc]
  exact Iff.rfl

theorem Sat_inductiveC (hs : IsConst s n) (i : Fin a) (v : Fin a → T.U n) :
    (inductiveC hs i).Sat T.toStr (fun l => T.inj (v l)) ↔ (T.sortStr n).IsInductive (v i) := by
  unfold inductiveC
  simp only [Formula.Sat_and, Sat_exC, Sat_allC, Formula.Sat_imp, Sat_isEmptyC, Sat_memC,
    Fin.snoc_last, Fin.snoc_castSucc]
  refine and_congr Iff.rfl (forall_congr' fun y => imp_congr Iff.rfl (exists_congr fun z => ?_))
  rw [Sat_isSuccC T]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]

theorem Sat_isOmegaC (hs : IsConst s n) (i : Fin a) (v : Fin a → T.U n) :
    (isOmegaC hs i).Sat T.toStr (fun l => T.inj (v l)) ↔ (T.sortStr n).IsOmega (v i) := by
  unfold isOmegaC
  simp only [Sat_allC, Formula.Sat_iff, Formula.Sat_imp, Sat_memC, Fin.snoc_last, Fin.snoc_castSucc]
  refine forall_congr' fun z => iff_congr Iff.rfl (forall_congr' fun I => imp_congr ?_ Iff.rfl)
  rw [Sat_inductiveC T]
  simp only [Fin.snoc_last]

end Const

/-! ### Atoms at positions, in the "∃ sorted witnesses" form -/

variable {k : ℕ} {s : Fin k → ℕ} {t : Fin k → T.El}

theorem Sat_at1 {n : ℕ} (φ : TF 1 (fun _ => n)) {p : Fin k} {hp : ∀ l, s (![p] l) = n} (x : T.U n)
    (hx : t p = T.inj x) : (at_ φ ![p] hp).Sat T.toStr t ↔ φ.Sat T.toStr (fun l => T.inj (![x] l)) := by
  rw [Sat_at, Calc.tuple1 T t p x hx]

theorem Sat_at2 {n : ℕ} (φ : TF 2 (fun _ => n)) {p q : Fin k} {hp : ∀ l, s (![p, q] l) = n}
    (x y : T.U n) (hx : t p = T.inj x) (hy : t q = T.inj y) :
    (at_ φ ![p, q] hp).Sat T.toStr t ↔ φ.Sat T.toStr (fun l => T.inj (![x, y] l)) := by
  rw [Sat_at, Calc.tuple2 T t p q x y hx hy]

theorem Sat_at3 {n : ℕ} (φ : TF 3 (fun _ => n)) {p q r : Fin k} {hp : ∀ l, s (![p, q, r] l) = n}
    (x y z : T.U n) (hx : t p = T.inj x) (hy : t q = T.inj y) (hz : t r = T.inj z) :
    (at_ φ ![p, q, r] hp).Sat T.toStr t ↔ φ.Sat T.toStr (fun l => T.inj (![x, y, z] l)) := by
  rw [Sat_at, Calc.tuple3 T t p q r x y z hx hy hz]

/-- The sort guard, as an existential. -/
theorem Sat_sortF' {n : ℕ} {p : Fin k} {hp : s p = n} :
    (sortF n p hp).Sat T.toStr t ↔ ∃ x : T.U n, t p = T.inj x := by
  rw [Sat_sortF]
  constructor
  · intro h; exact Calc.elSort T _ h
  · rintro ⟨x, hx⟩; rw [hx]

theorem Sat_liftLEF' {n m : ℕ} {h : n ≤ m} {i j : Fin k} {hi : s i = n} {hj : s j = m} :
    (liftLEF n m h i j hi hj).Sat T.toStr t ↔ ∃ x : T.U n, t i = T.inj x ∧ t j = T.inj (T.liftLE h x) := by
  constructor
  · intro hs
    obtain ⟨x, hx⟩ := (Sat_sortF' T).1 ((Formula.Sat_and _ _ _).mp hs).1
    exact ⟨x, hx, (Sat_liftLEF T n m h i j hi hj t x hx).1 hs⟩
  · rintro ⟨x, hx, h'⟩
    exact (Sat_liftLEF T n m h i j hi hj t x hx).2 h'

theorem Sat_tmemF_ex {r : ℕ} {i j : Fin k} {hi : s i = r} {hj : s j = r + 1} :
    (tmemF r i j hi hj).Sat T.toStr t ↔
      ∃ (x : T.U r) (A : T.U (r + 1)), t i = T.inj x ∧ t j = T.inj A ∧ T.mem (T.j r x) A := by
  constructor
  · intro hs
    have hs' := hs
    obtain ⟨y, hy, h12⟩ := hs
    obtain ⟨h1, h2⟩ := (Formula.Sat_and _ _ _).mp h12
    obtain ⟨x, hx⟩ := Calc.elSort T (t i) (by
      obtain ⟨x, hx, -⟩ := (Calc.Sat_liftZF' T _).1 h1
      simp only [Fin.snoc_castSucc] at hx
      rw [hx])
    obtain ⟨A, hA⟩ := Calc.elSort T (t j) (by
      obtain ⟨-, y', -, hy', -⟩ := (Calc.Sat_memF' T _).1 h2
      simp only [Fin.snoc_castSucc] at hy'
      rw [hy'])
    exact ⟨x, A, hx, hA, (Sat_tmemF T (hi := hi) (hj := hj) x A hx hA).1 hs'⟩
  · rintro ⟨x, A, hx, hA, h⟩
    exact (Sat_tmemF T x A hx hA).2 h

theorem Sat_emptyF' {n : ℕ} {p : Fin k} {hp : s p = n} :
    (emptyF n p hp).Sat T.toStr t ↔ ∃ x : T.U n, t p = T.inj x ∧ (T.sortStr n).IsEmptySet x := by
  unfold emptyF
  rw [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    rw [Sat_at1 T _ x hx, Sat_isEmptyC] at h
    exact ⟨x, hx, by simpa using h⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [Sat_at1 T _ x hx, Sat_isEmptyC]; simpa using h

theorem Sat_trueF' {n : ℕ} {p : Fin k} {hp : s p = n} :
    (trueF n p hp).Sat T.toStr t ↔ ∃ x : T.U n, t p = T.inj x ∧
      ∃ e, (T.sortStr n).IsEmptySet e ∧ (T.sortStr n).IsSingleton e x := by
  unfold trueF
  rw [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨x, hx⟩, h⟩
    rw [Sat_at1 T _ x hx, Sat_isTrueC] at h
    exact ⟨x, hx, by simpa using h⟩
  · rintro ⟨x, hx, h⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [Sat_at1 T _ x hx, Sat_isTrueC]; simpa using h

theorem Sat_ordPairF' {n : ℕ} {p q r : Fin k} {hp : s p = n} {hq : s q = n} {hr : s r = n} :
    (ordPairF n p q r hp hq hr).Sat T.toStr t ↔ ∃ x y z : T.U n, t p = T.inj x ∧ t q = T.inj y ∧
      t r = T.inj z ∧ (T.sortStr n).IsOrdPair x y z := by
  unfold ordPairF
  simp only [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, h⟩
    rw [Sat_at3 T _ x y z hx hy hz, Sat_ordPairC] at h
    exact ⟨x, y, z, hx, hy, hz, by simpa using h⟩
  · rintro ⟨x, y, z, hx, hy, hz, h⟩
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩, ?_⟩
    rw [Sat_at3 T _ x y z hx hy hz, Sat_ordPairC]; simpa using h

theorem Sat_funAppF' {n : ℕ} {f x y : Fin k} {hf : s f = n} {hx : s x = n} {hy : s y = n} :
    (funAppF n f x y hf hx hy).Sat T.toStr t ↔ ∃ g a b : T.U n, t f = T.inj g ∧ t x = T.inj a ∧
      t y = T.inj b ∧ (T.sortStr n).FunApp g a b := by
  unfold funAppF
  simp only [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨g, hg⟩, ⟨a, ha⟩, ⟨b, hb⟩, h⟩
    rw [Sat_at3 T _ g a b hg ha hb, Sat_funAppC] at h
    exact ⟨g, a, b, hg, ha, hb, by simpa using h⟩
  · rintro ⟨g, a, b, hg, ha, hb, h⟩
    refine ⟨⟨g, hg⟩, ⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    rw [Sat_at3 T _ g a b hg ha hb, Sat_funAppC]; simpa using h

theorem Sat_isFunF' {n : ℕ} {f : Fin k} {hf : s f = n} :
    (isFunF n f hf).Sat T.toStr t ↔ ∃ g : T.U n, t f = T.inj g ∧ (T.sortStr n).IsFunction g := by
  unfold isFunF
  rw [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨g, hg⟩, h⟩
    rw [Sat_at1 T _ g hg, Sat_isFunC] at h
    exact ⟨g, hg, by simpa using h⟩
  · rintro ⟨g, hg, h⟩
    refine ⟨⟨g, hg⟩, ?_⟩
    rw [Sat_at1 T _ g hg, Sat_isFunC]; simpa using h

theorem Sat_inDomF' {n : ℕ} {f x : Fin k} {hf : s f = n} {hx : s x = n} :
    (inDomF n f x hf hx).Sat T.toStr t ↔ ∃ g a : T.U n, t f = T.inj g ∧ t x = T.inj a ∧
      (T.sortStr n).InDom g a := by
  unfold inDomF
  simp only [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨g, hg⟩, ⟨a, ha⟩, h⟩
    rw [Sat_at2 T _ g a hg ha, Sat_inDomC] at h
    exact ⟨g, a, hg, ha, by simpa using h⟩
  · rintro ⟨g, a, hg, ha, h⟩
    refine ⟨⟨g, hg⟩, ⟨a, ha⟩, ?_⟩
    rw [Sat_at2 T _ g a hg ha, Sat_inDomC]; simpa using h

theorem Sat_isSuccF' {n : ℕ} {x y : Fin k} {hx : s x = n} {hy : s y = n} :
    (isSuccF n x y hx hy).Sat T.toStr t ↔ ∃ a b : T.U n, t x = T.inj a ∧ t y = T.inj b ∧
      (T.sortStr n).IsSucc a b := by
  unfold isSuccF
  simp only [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, h⟩
    rw [Sat_at2 T _ a b ha hb, Sat_isSuccC T] at h
    exact ⟨a, b, ha, hb, by simpa using h⟩
  · rintro ⟨a, b, ha, hb, h⟩
    refine ⟨⟨a, ha⟩, ⟨b, hb⟩, ?_⟩
    rw [Sat_at2 T _ a b ha hb, Sat_isSuccC T]; simpa using h

theorem Sat_isOmegaF' {n : ℕ} {p : Fin k} {hp : s p = n} :
    (isOmegaF n p hp).Sat T.toStr t ↔ ∃ o : T.U n, t p = T.inj o ∧ (T.sortStr n).IsOmega o := by
  unfold isOmegaF
  rw [Formula.Sat_and, Sat_sortF']
  constructor
  · rintro ⟨⟨o, ho⟩, h⟩
    rw [Sat_at1 T _ o ho, Sat_isOmegaC T] at h
    exact ⟨o, ho, by simpa using h⟩
  · rintro ⟨o, ho, h⟩
    refine ⟨⟨o, ho⟩, ?_⟩
    rw [Sat_at1 T _ o ho, Sat_isOmegaC T]; simpa using h

/-- `tvF` read: `w` is the truth value of `ψ`. -/
theorem Sat_tvF' {n : ℕ} {w : Fin k} {hw : s w = n} (ψ : TF k s) :
    (Calc.tvF n w hw ψ).Sat T.toStr t ↔ ∃ x : T.U n, t w = T.inj x ∧ Calc.IsTV T n (ψ.Sat T.toStr t) x := by
  unfold Calc.tvF Calc.IsTV
  simp only [Formula.Sat_and, Formula.Sat_imp, Formula.Sat_not, Sat_sortF']
  constructor
  · rintro ⟨⟨x, hx⟩, h1, h2⟩
    rw [Sat_at1 T _ x hx, Sat_isTrueC] at h1
    rw [Sat_at1 T _ x hx, Sat_isEmptyC] at h2
    exact ⟨x, hx, by simpa using h1, by simpa using h2⟩
  · rintro ⟨x, hx, h1, h2⟩
    refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · rw [Sat_at1 T _ x hx, Sat_isTrueC]; simpa using h1
    · rw [Sat_at1 T _ x hx, Sat_isEmptyC]; simpa using h2

end SolidLean.Solid.TF

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF SolidLean.Solid.Fin

variable (T : MemTower.{u})

attribute [prim_simps] Prim.clauseF Formula.Sat_ex Formula.Sat_all Formula.Sat_and Formula.Sat_or
  Formula.Sat_imp Formula.Sat_iff Formula.Sat_not Formula.Sat_eq exists_sorted forall_sorted
  snocL_0_0 snocL_1_0 snocL_1_1 snocL_2_0 snocL_2_1 snocL_2_2 snocL_3_0 snocL_3_1 snocL_3_2 snocL_3_3 snocL_4_0 snocL_4_1 snocL_4_2 snocL_4_3 snocL_4_4 snocL_5_0 snocL_5_1 snocL_5_2 snocL_5_3 snocL_5_4 snocL_5_5 snocL_6_0 snocL_6_1 snocL_6_2 snocL_6_3 snocL_6_4 snocL_6_5 snocL_6_6 snocL_7_0 snocL_7_1 snocL_7_2 snocL_7_3 snocL_7_4 snocL_7_5 snocL_7_6 snocL_7_7 snocL_8_0 snocL_8_1 snocL_8_2 snocL_8_3 snocL_8_4 snocL_8_5 snocL_8_6 snocL_8_7 snocL_8_8 snocL_9_0 snocL_9_1 snocL_9_2 snocL_9_3 snocL_9_4 snocL_9_5 snocL_9_6 snocL_9_7 snocL_9_8 snocL_9_9 snocL_10_0 snocL_10_1 snocL_10_2 snocL_10_3 snocL_10_4 snocL_10_5 snocL_10_6 snocL_10_7 snocL_10_8 snocL_10_9 snocL_10_10 snocL_11_0 snocL_11_1 snocL_11_2 snocL_11_3 snocL_11_4 snocL_11_5 snocL_11_6 snocL_11_7 snocL_11_8 snocL_11_9 snocL_11_10 snocL_11_11 snocL_12_0 snocL_12_1 snocL_12_2 snocL_12_3 snocL_12_4 snocL_12_5 snocL_12_6 snocL_12_7 snocL_12_8 snocL_12_9 snocL_12_10 snocL_12_11 snocL_12_12 snocL_13_0 snocL_13_1 snocL_13_2 snocL_13_3 snocL_13_4 snocL_13_5 snocL_13_6 snocL_13_7 snocL_13_8 snocL_13_9 snocL_13_10 snocL_13_11 snocL_13_12 snocL_13_13 snocL_14_0 snocL_14_1 snocL_14_2 snocL_14_3 snocL_14_4 snocL_14_5 snocL_14_6 snocL_14_7 snocL_14_8 snocL_14_9 snocL_14_10 snocL_14_11 snocL_14_12 snocL_14_13 snocL_14_14 snocL_15_0 snocL_15_1 snocL_15_2 snocL_15_3 snocL_15_4 snocL_15_5 snocL_15_6 snocL_15_7 snocL_15_8 snocL_15_9 snocL_15_10 snocL_15_11 snocL_15_12 snocL_15_13 snocL_15_14 snocL_15_15
  snocL_16_0 snocL_16_1 snocL_16_2 snocL_16_3 snocL_16_4 snocL_16_5 snocL_16_6 snocL_16_7 snocL_16_8 snocL_16_9 snocL_16_10 snocL_16_11 snocL_16_12 snocL_16_13 snocL_16_14 snocL_16_15 snocL_16_16 snocL_17_0 snocL_17_1 snocL_17_2 snocL_17_3 snocL_17_4 snocL_17_5 snocL_17_6 snocL_17_7 snocL_17_8 snocL_17_9 snocL_17_10 snocL_17_11 snocL_17_12 snocL_17_13 snocL_17_14 snocL_17_15 snocL_17_16 snocL_17_17 snocL_18_0 snocL_18_1 snocL_18_2 snocL_18_3 snocL_18_4 snocL_18_5 snocL_18_6 snocL_18_7 snocL_18_8 snocL_18_9 snocL_18_10 snocL_18_11 snocL_18_12 snocL_18_13 snocL_18_14 snocL_18_15 snocL_18_16 snocL_18_17 snocL_18_18 snocL_19_0 snocL_19_1 snocL_19_2 snocL_19_3 snocL_19_4 snocL_19_5 snocL_19_6 snocL_19_7 snocL_19_8 snocL_19_9 snocL_19_10 snocL_19_11 snocL_19_12 snocL_19_13 snocL_19_14 snocL_19_15 snocL_19_16 snocL_19_17 snocL_19_18 snocL_19_19 snocL_20_0 snocL_20_1 snocL_20_2 snocL_20_3 snocL_20_4 snocL_20_5 snocL_20_6 snocL_20_7 snocL_20_8 snocL_20_9 snocL_20_10 snocL_20_11 snocL_20_12 snocL_20_13 snocL_20_14 snocL_20_15 snocL_20_16 snocL_20_17 snocL_20_18 snocL_20_19 snocL_20_20
  Sat_memF' Sat_liftZF' SolidLean.Solid.TF.Sat_liftLEF' SolidLean.Solid.TF.Sat_tmemF_ex
  SolidLean.Solid.TF.Sat_emptyF' SolidLean.Solid.TF.Sat_trueF' SolidLean.Solid.TF.Sat_ordPairF'
  SolidLean.Solid.TF.Sat_funAppF' SolidLean.Solid.TF.Sat_isFunF' SolidLean.Solid.TF.Sat_inDomF'
  SolidLean.Solid.TF.Sat_isSuccF' SolidLean.Solid.TF.Sat_isOmegaF' SolidLean.Solid.TF.Sat_tvF'
  SolidLean.Solid.TF.Sat_sortF' SolidLean.Solid.TF.inj_eq_inj_iff' exists_eq_left exists_eq_left'
  exists_and_left exists_and_right exists_eq_right exists_eq_right' and_true true_and and_assoc
  exists_prop Fin.snoc_castSucc Fin.snoc_last Matrix.cons_val_zero Matrix.cons_val_one
  Matrix.cons_val_two Matrix.cons_val_three Matrix.cons_val_four Matrix.head_cons Matrix.tail_cons
  Matrix.cons_val_succ

/-- The standard unfolding of a clause at a tuple of sorted values. -/
macro "prim_simp" : tactic => `(tactic| simp only [prim_simps])

/-! ### The readings -/

theorem clause_false (vs : Fin 0 → T.El) (w : T.El) (w' : T.U 1) (hw : w = T.inj w') :
    (Prim.false_).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 1).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_falseElim (j : ℕ) (vs : Fin 2 → T.El) (w : T.El) (w' : T.U j) (hw : w = T.inj w') :
    (Prim.falseElim j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr j).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_eq (i : ℕ) (vs : Fin 3 → T.El) (w : T.El) (vA : T.U (i + 1)) (a b : T.U i)
    (w' : T.U 1) (h0 : vs 0 = T.inj vA) (h1 : vs 1 = T.inj a) (h2 : vs 2 = T.inj b)
    (hw : w = T.inj w') :
    (Prim.eq i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ IsTV T 1 (a = b) w' := by
  subst hw; prim_simp; simp [h1, h2]

theorem clause_refl (i : ℕ) (vs : Fin 2 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.refl i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_eqRec (i j : ℕ) (vs : Fin 6 → T.El) (w : T.El) (c : T.U j) (w' : T.U j)
    (h3 : vs 3 = T.inj c) (hw : w = T.inj w') :
    (Prim.eqRec i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ w' = c := by
  subst hw; prim_simp; simp [h3]

theorem clause_pair (i j : ℕ) (vs : Fin 4 → T.El) (w : T.El) (a : T.U i) (b : T.U j)
    (w' : T.U (max i j)) (h2 : vs 2 = T.inj a) (h3 : vs 3 = T.inj b) (hw : w = T.inj w') :
    (Prim.pair i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) a) (T.liftLE (le_max_right i j) b) w' := by
  subst hw; prim_simp; simp [h2, h3]

theorem clause_fst (i j : ℕ) (vs : Fin 3 → T.El) (w : T.El) (p : T.U (max i j)) (w' : T.U i)
    (h2 : vs 2 = T.inj p) (hw : w = T.inj w') :
    (Prim.fst i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ v : T.U (max i j), (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) w') v p := by
  subst hw; prim_simp; simp [h2]

theorem clause_snd (i j : ℕ) (vs : Fin 3 → T.El) (w : T.El) (p : T.U (max i j)) (w' : T.U j)
    (h2 : vs 2 = T.inj p) (hw : w = T.inj w') :
    (Prim.snd i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ u : T.U (max i j), (T.sortStr (max i j)).IsOrdPair u (T.liftLE (le_max_right i j) w') p := by
  subst hw; prim_simp; simp [h2]

theorem clause_lift (i d : ℕ) (vs : Fin 1 → T.El) (w : T.El) (vA : T.U (i + 1)) (w' : T.U (i + d + 1))
    (h0 : vs 0 = T.inj vA) (hw : w = T.inj w') :
    (Prim.lift i d).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ w' = T.liftLE (by omega) vA := by
  subst hw; prim_simp; simp [h0]

theorem clause_up (i d : ℕ) (vs : Fin 2 → T.El) (w : T.El) (a : T.U i) (w' : T.U (i + d))
    (h1 : vs 1 = T.inj a) (hw : w = T.inj w') :
    (Prim.up i d).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ w' = T.liftLE (by omega) a := by
  subst hw; prim_simp; simp [h1]

theorem clause_down (i d : ℕ) (vs : Fin 2 → T.El) (w : T.El) (a : T.U (i + d)) (w' : T.U i)
    (h1 : vs 1 = T.inj a) (hw : w = T.inj w') :
    (Prim.down i d).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ a = T.liftLE (by omega) w' := by
  subst hw; prim_simp; simp [h1]

theorem clause_trunc (i : ℕ) (vs : Fin 1 → T.El) (w : T.El) (vA : T.U (i + 1)) (w' : T.U 1)
    (h0 : vs 0 = T.inj vA) (hw : w = T.inj w') :
    (Prim.trunc i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      IsTV T 1 (∃ a : T.U i, T.mem (T.j i a) vA) w' := by
  subst hw; prim_simp; simp [h0]

theorem clause_truncMk (i : ℕ) (vs : Fin 2 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.truncMk i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_truncRec (i : ℕ) (vs : Fin 4 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.truncRec i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_propext (vs : Fin 4 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.propext).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_dne (vs : Fin 2 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.dne).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_uchoice (i : ℕ) (vs : Fin 3 → T.El) (w : T.El) (vA : T.U (i + 1)) (w' : T.U i)
    (h0 : vs 0 = T.inj vA) (hw : w = T.inj w') :
    (Prim.uchoice i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      T.mem (T.j i w') vA ∧ ∀ x : T.U i, T.mem (T.j i x) vA → x = w' := by
  subst hw; prim_simp; simp [h0]

theorem clause_choice (i j : ℕ) (vs : Fin 3 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.choice i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_inl (i j : ℕ) (vs : Fin 3 → T.El) (w : T.El) (a : T.U i) (w' : T.U (max i j))
    (h2 : vs 2 = T.inj a) (hw : w = T.inj w') :
    (Prim.inl i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ z, (T.sortStr (max i j)).IsEmptySet z ∧
        (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_left i j) a) w' := by
  subst hw; prim_simp; simp [h2]

theorem clause_inr (i j : ℕ) (vs : Fin 3 → T.El) (w : T.El) (b : T.U j) (w' : T.U (max i j))
    (h2 : vs 2 = T.inj b) (hw : w = T.inj w') :
    (Prim.inr i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ z, (∃ e, (T.sortStr (max i j)).IsEmptySet e ∧ (T.sortStr (max i j)).IsSingleton e z) ∧
        (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_right i j) b) w' := by
  subst hw; prim_simp; simp [h2]

theorem clause_zero (vs : Fin 0 → T.El) (w : T.El) (w' : T.U 1) (hw : w = T.inj w') :
    (Prim.zero).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 1).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_succ (vs : Fin 1 → T.El) (w : T.El) (n : T.U 1) (w' : T.U 1) (h0 : vs 0 = T.inj n)
    (hw : w = T.inj w') :
    (Prim.succ).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 1).IsSucc n w' := by
  subst hw; prim_simp; simp [h0]

theorem clause_nat (vs : Fin 0 → T.El) (w : T.El) (w' : T.U 2) (hw : w = T.inj w') :
    (Prim.nat).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ ∃ o : T.U 1, (T.sortStr 1).IsOmega o ∧ w' = T.j 1 o := by
  subst hw; prim_simp

theorem clause_quotSound (i : ℕ) (vs : Fin 5 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.quotSound i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_quotInd (i : ℕ) (vs : Fin 5 → T.El) (w : T.El) (w' : T.U 0) (hw : w = T.inj w') :
    (Prim.quotInd i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ (T.sortStr 0).IsEmptySet w' := by
  subst hw; prim_simp

theorem clause_quotLift (i j : ℕ) (vs : Fin 6 → T.El) (w : T.El) (f : T.U (max i j)) (q : T.U i)
    (w' : T.U j) (h3 : vs 3 = T.inj f) (h5 : vs 5 = T.inj q) (hw : w = T.inj w') :
    (Prim.quotLift i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ a : T.U i, T.mem a q ∧
        (T.sortStr (max i j)).FunApp f (T.liftLE (le_max_left i j) a) (T.liftLE (le_max_right i j) w') := by
  subst hw; prim_simp; simp [h3, h5]

/-! ### Equivalence relations and quotients: the semantic notions -/

/-- `⟨y, z⟩ ∈ E`. -/
def PairMem (i : ℕ) (y z E : T.U i) : Prop := ∃ p, (T.sortStr i).IsOrdPair y z p ∧ T.mem p E

/-- `R y z` holds, for `R` the value of a relation `A → A → U_0`: `R(lift y) = lift g` and
`g(lift z) = lift {∅}`. -/
def RelHolds (i : ℕ) (R : T.U (max i (max i 1))) (y z : T.U i) : Prop :=
  ∃ t, (T.sortStr (max i (max i 1))).FunApp R (T.liftLE (le_max_left _ _) y) t ∧
    ∃ g : T.U (max i 1), t = T.liftLE (le_max_right _ _) g ∧
      ∃ u, (T.sortStr (max i 1)).FunApp g (T.liftLE (le_max_left _ _) z) u ∧
        ∃ v : T.U 1, u = T.liftLE (le_max_right _ _) v ∧
          ∃ e, (T.sortStr 1).IsEmptySet e ∧ (T.sortStr 1).IsSingleton e v

/-- `E` is an equivalence relation on the elements of `vA` containing `R`. -/
def EquivRelOn (i : ℕ) (E : T.U i) (vA : T.U (i + 1)) (R : T.U (max i (max i 1))) : Prop :=
  (∀ p, T.mem p E → ∃ a b, T.mem (T.j i a) vA ∧ T.mem (T.j i b) vA ∧ (T.sortStr i).IsOrdPair a b p) ∧
  (∀ a, T.mem (T.j i a) vA → PairMem T i a a E) ∧
  (∀ a b, PairMem T i a b E → PairMem T i b a E) ∧
  (∀ a b c, PairMem T i a b E → PairMem T i b c E → PairMem T i a c E) ∧
  (∀ a b, T.mem (T.j i a) vA → T.mem (T.j i b) vA → RelHolds T i R a b → PairMem T i a b E)

/-- `a ~ x`: the pair lies in every equivalence relation on `vA` containing `R`. -/
def Eqv (i : ℕ) (vA : T.U (i + 1)) (R : T.U (max i (max i 1))) (a x : T.U i) : Prop :=
  ∀ E, EquivRelOn T i E vA R → PairMem T i a x E

section TFxRead

open TFx

variable {k : ℕ} {s : Fin k → ℕ} {t : Fin k → T.El}

theorem Sat_pairMemF' {i : ℕ} {y z E : Fin k} {hy : s y = i} {hz : s z = i} {hE : s E = i} :
    (pairMemF i y z E hy hz hE).Sat T.toStr t ↔
      ∃ vy vz vE : T.U i, t y = T.inj vy ∧ t z = T.inj vz ∧ t E = T.inj vE ∧ PairMem T i vy vz vE := by
  unfold pairMemF PairMem
  prim_simp
  aesop

theorem Sat_relHoldsF' {i : ℕ} {R y z : Fin k} {hR : s R = max i (max i 1)} {hy : s y = i} {hz : s z = i} :
    (relHoldsF i R y z hR hy hz).Sat T.toStr t ↔
      ∃ (vR : T.U (max i (max i 1))) (vy vz : T.U i), t R = T.inj vR ∧ t y = T.inj vy ∧ t z = T.inj vz ∧
        RelHolds T i vR vy vz := by
  unfold relHoldsF RelHolds
  prim_simp
  aesop

attribute [prim_simps] Sat_pairMemF' Sat_relHoldsF'

theorem Sat_subsetPairsF' {i : ℕ} {E A : Fin k} {hE : s E = i} {hA : s A = i + 1} :
    (subsetPairsF i E A hE hA).Sat T.toStr t ↔ ∃ (vE : T.U i) (vA : T.U (i + 1)), t E = T.inj vE ∧
      t A = T.inj vA ∧ ∀ p, T.mem p vE → ∃ a b, T.mem (T.j i a) vA ∧ T.mem (T.j i b) vA ∧
        (T.sortStr i).IsOrdPair a b p := by
  unfold subsetPairsF
  prim_simp
  aesop

theorem Sat_reflF' {i : ℕ} {E A : Fin k} {hE : s E = i} {hA : s A = i + 1} :
    (reflF i E A hE hA).Sat T.toStr t ↔ ∃ (vE : T.U i) (vA : T.U (i + 1)), t E = T.inj vE ∧
      t A = T.inj vA ∧ ∀ a, T.mem (T.j i a) vA → PairMem T i a a vE := by
  unfold reflF
  prim_simp
  aesop

theorem Sat_symmF' {i : ℕ} {E : Fin k} {hE : s E = i} :
    (symmF i E hE).Sat T.toStr t ↔ ∃ vE : T.U i, t E = T.inj vE ∧
      ∀ a b, PairMem T i a b vE → PairMem T i b a vE := by
  unfold symmF
  prim_simp
  aesop

theorem Sat_transF' {i : ℕ} {E : Fin k} {hE : s E = i} :
    (transF i E hE).Sat T.toStr t ↔ ∃ vE : T.U i, t E = T.inj vE ∧
      ∀ a b c, PairMem T i a b vE → PairMem T i b c vE → PairMem T i a c vE := by
  unfold transF
  prim_simp
  aesop

theorem Sat_containsF' {i : ℕ} {E A R : Fin k} {hE : s E = i} {hA : s A = i + 1}
    {hR : s R = max i (max i 1)} :
    (containsF i E A R hE hA hR).Sat T.toStr t ↔
      ∃ (vE : T.U i) (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))),
      t E = T.inj vE ∧ t A = T.inj vA ∧ t R = T.inj vR ∧
      ∀ a b, T.mem (T.j i a) vA → T.mem (T.j i b) vA → RelHolds T i vR a b → PairMem T i a b vE := by
  unfold containsF
  prim_simp
  aesop

attribute [prim_simps] Sat_subsetPairsF' Sat_reflF' Sat_symmF' Sat_transF' Sat_containsF'

theorem Sat_equivRelF' {i : ℕ} {E A R : Fin k} {hE : s E = i} {hA : s A = i + 1}
    {hR : s R = max i (max i 1)} :
    (equivRelF i E A R hE hA hR).Sat T.toStr t ↔
      ∃ (vE : T.U i) (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))),
      t E = T.inj vE ∧ t A = T.inj vA ∧ t R = T.inj vR ∧ EquivRelOn T i vE vA vR := by
  unfold equivRelF EquivRelOn
  prim_simp
  aesop

attribute [prim_simps] Sat_equivRelF'

theorem Sat_equivF' {i : ℕ} {A R a x : Fin k} {hA : s A = i + 1} {hR : s R = max i (max i 1)}
    {ha : s a = i} {hx : s x = i} :
    (equivF i A R a x hA hR ha hx).Sat T.toStr t ↔
      ∃ (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))) (va vx : T.U i),
      t A = T.inj vA ∧ t R = T.inj vR ∧ t a = T.inj va ∧ t x = T.inj vx ∧ Eqv T i vA vR va vx := by
  unfold equivF Eqv
  prim_simp
  aesop

attribute [prim_simps] Sat_equivF'

end TFxRead

/-! ### The remaining clauses -/

/-- Membership in the Σ-set: `q = ⟨lift a, lift b⟩` with `j a ∈ vA` and `j b ∈ B(a)`, where
`vB(lift a) = lift (B(a))`. -/
def SigmaMem (i j : ℕ) (vA : T.U (i + 1)) (vB : T.U (max i (j + 1))) (q : T.U (max i j)) : Prop :=
  ∃ a : T.U i, T.mem (T.j i a) vA ∧ ∃ v : T.U (max i (j + 1)),
    (T.sortStr (max i (j + 1))).FunApp vB (T.liftLE (le_max_left _ _) a) v ∧
    ∃ vBa : T.U (j + 1), v = T.liftLE (le_max_right _ _) vBa ∧ ∃ b : T.U j, T.mem (T.j j b) vBa ∧
      (T.sortStr (max i j)).IsOrdPair (T.liftLE (le_max_left i j) a) (T.liftLE (le_max_right i j) b) q

/-- Membership in the sum set: `⟨∅, lift a⟩` for `j a ∈ vA`, or `⟨{∅}, lift b⟩` for `j b ∈ vB`. -/
def SumMem (i j : ℕ) (vA : T.U (i + 1)) (vB : T.U (j + 1)) (q : T.U (max i j)) : Prop :=
  (∃ a : T.U i, T.mem (T.j i a) vA ∧ ∃ z, (T.sortStr (max i j)).IsEmptySet z ∧
    (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_left i j) a) q) ∨
  (∃ b : T.U j, T.mem (T.j j b) vB ∧ ∃ z, (∃ e, (T.sortStr (max i j)).IsEmptySet e ∧
    (T.sortStr (max i j)).IsSingleton e z) ∧ (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_right i j) b) q)

/-- The class of `a`: `{x : j x ∈ vA, a ~ x}`. -/
def IsClassOf (i : ℕ) (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))) (a c : T.U i) : Prop :=
  ∀ x, T.mem x c ↔ T.mem (T.j i x) vA ∧ Eqv T i vA vR a x

/-- The kernel of `f`: `p = ⟨a, b⟩` with `f(lift a) = f(lift b)`. -/
def KernelMem (i j : ℕ) (f : T.U (max i j)) (p : T.U i) : Prop :=
  ∃ a b : T.U i, (T.sortStr i).IsOrdPair a b p ∧ ∃ u : T.U (max i j),
    (T.sortStr (max i j)).FunApp f (T.liftLE (le_max_left i j) a) u ∧
    (T.sortStr (max i j)).FunApp f (T.liftLE (le_max_left i j) b) u

section BodyRead

variable {k : ℕ} {s : Fin k → ℕ} {t : Fin k → T.El}

theorem Sat_sigmaBodyF' {i j : ℕ} {s : Fin 5 → ℕ} {h0 : s 0 = i + 1} {h1 : s 1 = max i (j + 1)}
    {h4 : s 4 = max i j} {t : Fin 5 → T.El} :
    (Prim.sigmaBodyF i j h0 h1 h4).Sat T.toStr t ↔ ∃ (vA : T.U (i + 1)) (vB : T.U (max i (j + 1)))
      (q : T.U (max i j)), t 0 = T.inj vA ∧ t 1 = T.inj vB ∧ t 4 = T.inj q ∧ SigmaMem T i j vA vB q := by
  unfold Prim.sigmaBodyF SigmaMem
  prim_simp
  aesop

theorem Sat_sumBodyF' {i j : ℕ} {s : Fin 5 → ℕ} {h0 : s 0 = i + 1} {h1 : s 1 = j + 1}
    {h4 : s 4 = max i j} {t : Fin 5 → T.El} :
    (Prim.sumBodyF i j h0 h1 h4).Sat T.toStr t ↔ ∃ (vA : T.U (i + 1)) (vB : T.U (j + 1))
      (q : T.U (max i j)), t 0 = T.inj vA ∧ t 1 = T.inj vB ∧ t 4 = T.inj q ∧ SumMem T i j vA vB q := by
  unfold Prim.sumBodyF SumMem
  prim_simp
  aesop

theorem Sat_classBodyF' {i : ℕ} {s : Fin 4 → ℕ} {h0 : s 0 = i + 1} {h1 : s 1 = max i (max i 1)}
    {h2 : s 2 = i} {h3 : s 3 = i} {t : Fin 4 → T.El} :
    (Prim.classBodyF i h0 h1 h2 h3).Sat T.toStr t ↔
      ∃ (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))) (a c : T.U i),
      t 0 = T.inj vA ∧ t 1 = T.inj vR ∧ t 2 = T.inj a ∧ t 3 = T.inj c ∧ IsClassOf T i vA vR a c := by
  unfold Prim.classBodyF IsClassOf
  prim_simp
  aesop

attribute [prim_simps] Sat_sigmaBodyF' Sat_sumBodyF' Sat_classBodyF'

theorem Sat_quotBodyF' {i : ℕ} {s : Fin 5 → ℕ} {h0 : s 0 = i + 1} {h1 : s 1 = max i (max i 1)}
    {h4 : s 4 = i} {t : Fin 5 → T.El} :
    (Prim.quotBodyF i h0 h1 h4).Sat T.toStr t ↔
      ∃ (vA : T.U (i + 1)) (vR : T.U (max i (max i 1))) (c : T.U i),
      t 0 = T.inj vA ∧ t 1 = T.inj vR ∧ t 4 = T.inj c ∧
      ∃ a, T.mem (T.j i a) vA ∧ IsClassOf T i vA vR a c := by
  unfold Prim.quotBodyF
  prim_simp
  simp only [Formula.sat_rename]
  prim_simp
  aesop

theorem Sat_kernelBodyF' {i j : ℕ} {s : Fin 3 → ℕ} {h1 : s 1 = max i j} {h2 : s 2 = i}
    {t : Fin 3 → T.El} :
    (Prim.kernelBodyF i j h1 h2).Sat T.toStr t ↔ ∃ (f : T.U (max i j)) (p : T.U i),
      t 1 = T.inj f ∧ t 2 = T.inj p ∧ KernelMem T i j f p := by
  unfold Prim.kernelBodyF KernelMem
  prim_simp
  aesop

attribute [prim_simps] Sat_quotBodyF' Sat_kernelBodyF'

end BodyRead

theorem clause_sigma (i j : ℕ) (vs : Fin 2 → T.El) (w : T.El) (vA : T.U (i + 1))
    (vB : T.U (max i (j + 1))) (w' : T.U (max i j + 1)) (h0 : vs 0 = T.inj vA) (h1 : vs 1 = T.inj vB)
    (hw : w = T.inj w') :
    (Prim.sigma i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ p : T.U (max i j), w' = T.j (max i j) p ∧ ∀ q, T.mem q p ↔ SigmaMem T i j vA vB q := by
  subst hw; prim_simp; simp only [h0, h1, inj_eq_inj_iff']; aesop

theorem clause_sum (i j : ℕ) (vs : Fin 2 → T.El) (w : T.El) (vA : T.U (i + 1)) (vB : T.U (j + 1))
    (w' : T.U (max i j + 1)) (h0 : vs 0 = T.inj vA) (h1 : vs 1 = T.inj vB) (hw : w = T.inj w') :
    (Prim.sum i j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ p : T.U (max i j), w' = T.j (max i j) p ∧ ∀ q, T.mem q p ↔ SumMem T i j vA vB q := by
  subst hw; prim_simp; simp only [h0, h1, inj_eq_inj_iff']; aesop

theorem clause_sumRec (i j k : ℕ) (vs : Fin 6 → T.El) (w : T.El) (f : T.U (max i k)) (g : T.U (max j k))
    (sv : T.U (max i j)) (w' : T.U k) (h3 : vs 3 = T.inj f) (h4 : vs 4 = T.inj g) (h5 : vs 5 = T.inj sv)
    (hw : w = T.inj w') :
    (Prim.sumRec i j k).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      (∃ x : T.U i, ∃ z, (T.sortStr (max i j)).IsEmptySet z ∧
        (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_left i j) x) sv ∧
        (T.sortStr (max i k)).FunApp f (T.liftLE (le_max_left i k) x) (T.liftLE (le_max_right i k) w')) ∨
      (∃ y : T.U j, ∃ z, (∃ e, (T.sortStr (max i j)).IsEmptySet e ∧ (T.sortStr (max i j)).IsSingleton e z) ∧
        (T.sortStr (max i j)).IsOrdPair z (T.liftLE (le_max_right i j) y) sv ∧
        (T.sortStr (max j k)).FunApp g (T.liftLE (le_max_left j k) y) (T.liftLE (le_max_right j k) w')) := by
  subst hw; prim_simp; simp only [h3, h4, h5, inj_eq_inj_iff']; aesop

/-- The recursion condition: `F` is a function on `lift d` with `F(∅) = z` and
`F(lift (k+1)) = g(F(lift k))` for `k ∈ n`, where `s(lift k) = lift g`. -/
def NatRecFun (j : ℕ) (hj : 1 ≤ j) (z : T.U j) (s : T.U (max 1 (max j j))) (n d : T.U 1) (F : T.U j) :
    Prop :=
  (T.sortStr j).IsFunction F ∧ (∀ x, (T.sortStr j).InDom F x ↔ T.mem x (T.liftLE hj d)) ∧
  (∃ e, (T.sortStr j).IsEmptySet e ∧ (T.sortStr j).FunApp F e z) ∧
  ∀ k, T.mem k n → ∀ k1, (T.sortStr 1).IsSucc k k1 → ∀ fk, (T.sortStr j).FunApp F (T.liftLE hj k) fk →
    ∀ sk, (T.sortStr (max 1 (max j j))).FunApp s (T.liftLE (le_max_left _ _) k) sk →
    ∀ g : T.U (max j j), sk = T.liftLE (le_max_right _ _) g →
    ∀ r', (T.sortStr (max j j)).FunApp g (T.liftLE (le_max_left j j) fk) r' →
    ∀ r : T.U j, r' = T.liftLE (le_max_right j j) r → (T.sortStr j).FunApp F (T.liftLE hj k1) r

theorem clause_natRec (j : ℕ) (hj : 1 ≤ j) (vs : Fin 4 → T.El) (w : T.El) (z : T.U j)
    (s : T.U (max 1 (max j j))) (n : T.U 1) (w' : T.U j) (h1 : vs 1 = T.inj z) (h2 : vs 2 = T.inj s)
    (h3 : vs 3 = T.inj n) (hw : w = T.inj w') :
    (Prim.natRec j).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ d : T.U 1, (T.sortStr 1).IsSucc n d ∧ ∃ F : T.U j, NatRecFun T j hj z s n d F ∧
        (T.sortStr j).FunApp F (T.liftLE hj n) w' := by
  subst hw; unfold NatRecFun
  simp only [Prim.clauseF, dif_pos hj]
  prim_simp; simp only [h1, h2, h3, inj_eq_inj_iff']; aesop

theorem clause_quot (i : ℕ) (vs : Fin 2 → T.El) (w : T.El) (vA : T.U (i + 1))
    (vR : T.U (max i (max i 1))) (w' : T.U (i + 1)) (h0 : vs 0 = T.inj vA) (h1 : vs 1 = T.inj vR)
    (hw : w = T.inj w') :
    (Prim.quot i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔
      ∃ Q : T.U i, w' = T.j i Q ∧ ∀ c, T.mem c Q ↔ ∃ a, T.mem (T.j i a) vA ∧ IsClassOf T i vA vR a c := by
  subst hw
  prim_simp; simp only [h0, h1, inj_eq_inj_iff']; aesop

theorem clause_quotMk (i : ℕ) (vs : Fin 3 → T.El) (w : T.El) (vA : T.U (i + 1))
    (vR : T.U (max i (max i 1))) (a : T.U i) (w' : T.U i) (h0 : vs 0 = T.inj vA) (h1 : vs 1 = T.inj vR)
    (h2 : vs 2 = T.inj a) (hw : w = T.inj w') :
    (Prim.quotMk i).clauseF.Sat T.toStr (Fin.snoc vs w) ↔ IsClassOf T i vA vR a w' := by
  subst hw
  prim_simp; simp only [h0, h1, h2, inj_eq_inj_iff']; aesop

end SolidLean.Calc
