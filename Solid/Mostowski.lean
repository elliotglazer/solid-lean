module

public import Solid.Absolute

/-!
# The Mostowski collapse, internally

For a set `D` and a set relation `R ⊆ D × D` (coded as a set of Kuratowski
pairs, `FunApp R y x` meaning `y R x`) that is well-founded in the sense of
the ambient model, there is a unique collapse `c` on `D` with
`c x = {c y | y R x}` (`exists_collapse`).  Its construction is by
attempts: functions on downward-closed parts of `D` satisfying the
recursion; attempts agree (`collapseAttempt_agree`); the maximal attempt is
total by well-foundedness.  When `R` is extensional modulo a set
equivalence `E`, the collapse identifies exactly `E`-related elements
(`collapse_eq_iff`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open SetClassSystem

namespace MemStr

variable (S : MemStr.{u})

/-- A collapse attempt for `R` on `D`: a function on a downward-closed part of
`D` satisfying `g x = {g y | y R x}`. -/
def IsCollapseAttempt (D R g : S.X) : Prop :=
  S.IsFunction g ∧ (∀ x, S.InDom g x → S.mem x D) ∧
  (∀ x y, S.InDom g x → S.FunApp R y x → S.InDom g y) ∧
  ∀ x w, S.FunApp g x w → ∀ v, S.mem v w ↔ ∃ y, S.FunApp R y x ∧ S.FunApp g y v

/-- `R` is well-founded on `D`: every nonempty subset has an `R`-minimal
element. -/
def WellFoundedOn (D R : S.X) : Prop :=
  ∀ X, S.Subset X D → S.Nonempty X → ∃ x, S.mem x X ∧ ∀ y, S.mem y X → ¬ S.FunApp R y x

end MemStr

namespace SetClassSystem.Def

variable {S : MemStr.{u}} {𝒞 : SetClassSystem S}

open Fin (castSucc last)

theorem isCollapseAttempt {k : ℕ} (i j l : Fin k) :
    𝒞.Def k (fun t => S.IsCollapseAttempt (t i) (t j) (t l)) := by
  have h1 := forall_ (imp_ (inDom (castSucc l) (last k)) (mem (last k) (castSucc i))) (𝒞 := 𝒞)
  have h2 := forall_ (forall_ (imp_ (inDom (castSucc (castSucc l)) (castSucc (last k)))
    (imp_ (funApp (castSucc (castSucc j)) (last (k + 1)) (castSucc (last k)))
      (inDom (castSucc (castSucc l)) (last (k + 1)))))) (𝒞 := 𝒞)
  have h3 := forall_ (forall_ (imp_ (funApp (castSucc (castSucc l)) (castSucc (last k))
      (last (k + 1)))
    (forall_ (iff_ (mem (last (k + 2)) (castSucc (last (k + 1))))
      (exists_ (and_
        (funApp (castSucc (castSucc (castSucc (castSucc j)))) (last (k + 3))
          (castSucc (castSucc (castSucc (last k)))))
        (funApp (castSucc (castSucc (castSucc (castSucc l)))) (last (k + 3))
          (castSucc (last (k + 2)))))))))) (𝒞 := 𝒞)
  refine congr ?_ (and_ (isFunction l) (and_ h1 (and_ h2 h3)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

end SetClassSystem.Def

namespace ZFCModel

variable (Z : ZFCModel.{u})

local notation:50 x " ∈' " y => Z.S.mem x y

/-- Attempts agree wherever both are defined. -/
theorem collapseAttempt_agree {D R g g' : Z.S.X}
    (hR : ∀ y x, Z.S.FunApp R y x → (y ∈' D) ∧ (x ∈' D)) (hwf : Z.S.WellFoundedOn D R)
    (hg : Z.S.IsCollapseAttempt D R g) (hg' : Z.S.IsCollapseAttempt D R g')
    {x w w' : Z.S.X} (hw : Z.S.FunApp g x w) (hw' : Z.S.FunApp g' x w') : w = w' := by
  let Bad : Z.S.X → Prop := fun x => (x ∈' D) ∧
    ∃ w w', Z.S.FunApp g x w ∧ Z.S.FunApp g' x w' ∧ w ≠ w'
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    refine Def.congr ?_ ((((Def.and_ (Def.mem (0 : Fin 4) 1) (Def.exists_ (Def.exists_ (Def.and_
      (Def.funApp (Fin.castSucc (Fin.castSucc 2)) (Fin.castSucc (Fin.castSucc 0))
        (Fin.castSucc (Fin.last 4)))
      (Def.and_ (Def.funApp (Fin.castSucc (Fin.castSucc 3)) (Fin.castSucc (Fin.castSucc 0))
        (Fin.last 5))
        (Def.not_ (Def.eq (Fin.castSucc (Fin.last 4)) (Fin.last 5)))))))).withParam g').withParam
          g).withParam D)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  by_contra hne
  obtain ⟨X, hX⟩ := Z.sepP hdef D
  have hXD : Z.S.Subset X D := fun z hz => ((hX z).1 hz).1
  have hxD : x ∈' D := hg.2.1 x ⟨w, hw⟩
  obtain ⟨x0, hx0, hmin⟩ := hwf X hXD ⟨x, (hX x).2 ⟨hxD, hxD, w, w', hw, hw', hne⟩⟩
  obtain ⟨-, -, w0, w0', hw0, hw0', hne0⟩ := (hX x0).1 hx0
  apply hne0
  apply Z.ax.ext
  intro v
  rw [hg.2.2.2 x0 w0 hw0 v, hg'.2.2.2 x0 w0' hw0' v]
  have hagree : ∀ y, Z.S.FunApp R y x0 → ∀ u u', Z.S.FunApp g y u → Z.S.FunApp g' y u' → u = u' := by
    intro y hy u u' hu hu'
    by_contra hne'
    exact hmin y ((hX y).2 ⟨(hR y x0 hy).1, (hR y x0 hy).1, u, u', hu, hu', hne'⟩) hy
  constructor
  · rintro ⟨y, hy, hu⟩
    obtain ⟨u', hu'⟩ := hg'.2.2.1 x0 y ⟨w0', hw0'⟩ hy
    rw [hagree y hy v u' hu hu']
    exact ⟨y, hy, hu'⟩
  · rintro ⟨y, hy, hu'⟩
    obtain ⟨u, hu⟩ := hg.2.2.1 x0 y ⟨w0, hw0⟩ hy
    rw [← hagree y hy u v hu hu']
    exact ⟨y, hy, hu⟩

/-- Existence of the collapse. -/
theorem exists_collapse (D R : Z.S.X)
    (hR : ∀ y x, Z.S.FunApp R y x → (y ∈' D) ∧ (x ∈' D)) (hwf : Z.S.WellFoundedOn D R) :
    ∃ c, Z.S.IsCollapseAttempt D R c ∧ ∀ x, Z.S.InDom c x ↔ x ∈' D := by
  -- the part of `D` covered by some attempt
  let Cov : Z.S.X → Prop := fun x => ∃ g, Z.S.IsCollapseAttempt D R g ∧ Z.S.InDom g x
  have hCovdef : Z.𝒞.Def 1 (fun t => Cov (t 0)) := by
    refine Def.congr ?_ (((Def.exists_ (Def.and_
      (Def.isCollapseAttempt (Fin.castSucc 1) (Fin.castSucc 2) (Fin.last 3))
      (Def.inDom (Fin.last 3) (Fin.castSucc (0 : Fin 3))))).withParam R).withParam D)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  obtain ⟨Dstar, hDstar⟩ := Z.sepP hCovdef D
  -- the graph of the maximal attempt
  let Rel : Z.S.X → Z.S.X → Prop := fun y p => ∃ g w, Z.S.IsCollapseAttempt D R g ∧
    Z.S.FunApp g y w ∧ Z.S.IsOrdPair y w p
  have hReldef : Z.𝒞.Def 2 (fun t => Rel (t 0) (t 1)) := by
    refine Def.congr ?_ (((Def.exists_ (Def.exists_ (Def.and_
      (Def.isCollapseAttempt (Fin.castSucc (Fin.castSucc 2)) (Fin.castSucc (Fin.castSucc 3))
        (Fin.castSucc (Fin.last 4)))
      (Def.and_ (Def.funApp (Fin.castSucc (Fin.last 4)) (Fin.castSucc (Fin.castSucc 0))
        (Fin.last 5))
        (Def.isOrdPair (Fin.castSucc (Fin.castSucc (0 : Fin 4))) (Fin.last 5)
          (Fin.castSucc (Fin.castSucc 1))))))).withParam R).withParam D)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  have hRelfun : ∀ y, (y ∈' Dstar) → ∃! p, Rel y p := by
    intro y hy
    obtain ⟨-, g, hg, w, hw⟩ := (hDstar y).1 hy
    obtain ⟨p, hp⟩ := Z.exists_ordPair y w
    refine ⟨p, ⟨g, w, hg, hw, hp⟩, ?_⟩
    rintro p' ⟨g', w', hg', hw', hp'⟩
    have := Z.collapseAttempt_agree hR hwf hg' hg hw' hw
    subst this
    exact Z.ordPair_unique hp' hp
  obtain ⟨G, hG⟩ := Z.replP hReldef Dstar hRelfun
  -- characterization of `G`
  have hGapp : ∀ y w, Z.S.FunApp G y w ↔ (y ∈' Dstar) ∧ ∃ g, Z.S.IsCollapseAttempt D R g ∧
      Z.S.FunApp g y w := by
    intro y w
    constructor
    · rintro ⟨p, hp, hpair⟩
      obtain ⟨y', hy', g, w', hg, hw', hpair'⟩ := (hG p).1 hp
      obtain ⟨rfl, rfl⟩ := Z.ordPair_inj hpair hpair'
      exact ⟨hy', g, hg, hw'⟩
    · rintro ⟨hy, g, hg, hw⟩
      obtain ⟨p, hp⟩ := Z.exists_ordPair y w
      exact ⟨p, (hG p).2 ⟨y, hy, g, w, hg, hw, hp⟩, hp⟩
  have hGdom : ∀ y, Z.S.InDom G y ↔ y ∈' Dstar := by
    intro y
    constructor
    · rintro ⟨w, hw⟩; exact ((hGapp y w).1 hw).1
    · intro hy
      obtain ⟨-, g, hg, w, hw⟩ := (hDstar y).1 hy
      exact ⟨w, (hGapp y w).2 ⟨hy, g, hg, hw⟩⟩
  have hGatt : Z.S.IsCollapseAttempt D R G := by
    refine ⟨⟨fun p hp => ?_, fun y w w' hw hw' => ?_⟩, fun y hy => ?_, fun x y hx hxy => ?_,
      fun x w hw v => ?_⟩
    · obtain ⟨y, -, g, w, -, -, hpair⟩ := (hG p).1 hp
      exact ⟨y, w, hpair⟩
    · obtain ⟨-, g, hg, hw⟩ := (hGapp y w).1 hw
      obtain ⟨-, g', hg', hw'⟩ := (hGapp y w').1 hw'
      exact Z.collapseAttempt_agree hR hwf hg hg' hw hw'
    · exact ((hDstar y).1 ((hGdom y).1 hy)).1
    · obtain ⟨-, g, hg, hxg⟩ := (hDstar x).1 ((hGdom x).1 hx)
      exact (hGdom y).2 ((hDstar y).2 ⟨(hR y x hxy).1, g, hg, hg.2.2.1 x y hxg hxy⟩)
    · obtain ⟨hx, g, hg, hw⟩ := (hGapp x w).1 hw
      rw [hg.2.2.2 x w hw v]
      constructor
      · rintro ⟨y, hy, hv⟩
        refine ⟨y, hy, (hGapp y v).2 ⟨?_, g, hg, hv⟩⟩
        exact (hDstar y).2 ⟨(hR y x hy).1, g, hg, ⟨v, hv⟩⟩
      · rintro ⟨y, hy, hv⟩
        obtain ⟨-, g', hg', hv'⟩ := (hGapp y v).1 hv
        obtain ⟨u, hu⟩ := hg.2.2.1 x y ⟨w, hw⟩ hy
        rw [Z.collapseAttempt_agree hR hwf hg' hg hv' hu]
        exact ⟨y, hy, hu⟩
  -- `Dstar = D`
  refine ⟨G, hGatt, fun x => ?_⟩
  rw [hGdom x]
  refine ⟨fun h => ((hDstar x).1 h).1, fun hxD => ?_⟩
  by_contra hxn
  obtain ⟨X, hX⟩ := Z.exists_diff D Dstar
  obtain ⟨x0, hx0, hmin⟩ := hwf X (fun z hz => ((hX z).1 hz).1) ⟨x, (hX x).2 ⟨hxD, hxn⟩⟩
  obtain ⟨hx0D, hx0n⟩ := (hX x0).1 hx0
  -- everything below `x0` is covered
  have hbelow : ∀ y, Z.S.FunApp R y x0 → y ∈' Dstar := by
    intro y hy
    by_contra hyn
    exact hmin y ((hX y).2 ⟨(hR y x0 hy).1, hyn⟩) hy
  -- the value at `x0`
  let Pred : Z.S.X → Prop := fun y => Z.S.FunApp R y x0
  have hpreddef : Z.𝒞.Def 1 (fun t => Pred (t 0)) := by
    refine Def.congr ?_ (((Def.funApp (1 : Fin 3) 0 2).withParam x0).withParam R)
    intro t; exact Iff.rfl
  obtain ⟨pred, hpred⟩ := Z.sepP hpreddef D
  have hGrel : Z.𝒞.Def 2 (fun t => Z.S.FunApp G (t 0) (t 1)) := by
    refine Def.congr ?_ ((Def.funApp (2 : Fin 3) 0 1).withParam G)
    intro t; exact Iff.rfl
  obtain ⟨wx, hwx⟩ := Z.replP hGrel pred (by
    intro y hy
    obtain ⟨v, hv⟩ := (hGdom y).2 (hbelow y ((hpred y).1 hy).2)
    exact ⟨v, hv, fun v' hv' => Z.funApp_unique hGatt.1 hv' hv⟩)
  obtain ⟨p0, hp0⟩ := Z.exists_ordPair x0 wx
  obtain ⟨sp, hsp⟩ := Z.exists_singleton p0
  obtain ⟨G', hG'⟩ := Z.exists_union2 G sp
  have hG'app : ∀ y w, Z.S.FunApp G' y w ↔ Z.S.FunApp G y w ∨ (y = x0 ∧ w = wx) := by
    intro y w
    constructor
    · rintro ⟨p, hp, hpair⟩
      rcases (hG' p).1 hp with hp | hp
      · exact Or.inl ⟨p, hp, hpair⟩
      · rw [(hsp p).1 hp] at hpair
        obtain ⟨rfl, rfl⟩ := Z.ordPair_inj hpair hp0
        exact Or.inr ⟨rfl, rfl⟩
    · rintro (⟨p, hp, hpair⟩ | ⟨rfl, rfl⟩)
      · exact ⟨p, (hG' p).2 (Or.inl hp), hpair⟩
      · exact ⟨p0, (hG' p0).2 (Or.inr ((hsp p0).2 rfl)), hp0⟩
  have hx0nG : ¬ Z.S.InDom G x0 := fun h => hx0n ((hGdom x0).1 h)
  have hG'att : Z.S.IsCollapseAttempt D R G' := by
    refine ⟨⟨fun p hp => ?_, fun y w w' hw hw' => ?_⟩, fun y hy => ?_, fun x y hx hxy => ?_,
      fun x w hw v => ?_⟩
    · rcases (hG' p).1 hp with hp | hp
      · exact hGatt.1.1 p hp
      · rw [(hsp p).1 hp]; exact ⟨x0, wx, hp0⟩
    · rcases (hG'app y w).1 hw with hw | ⟨rfl, rfl⟩ <;>
        rcases (hG'app y w').1 hw' with hw' | ⟨h1, rfl⟩
      · exact Z.funApp_unique hGatt.1 hw hw'
      · subst h1; exact (hx0nG ⟨w, hw⟩).elim
      · exact (hx0nG ⟨w', hw'⟩).elim
      · rfl
    · obtain ⟨w, hw⟩ := hy
      rcases (hG'app y w).1 hw with hw | ⟨rfl, -⟩
      · exact hGatt.2.1 y ⟨w, hw⟩
      · exact hx0D
    · obtain ⟨w, hw⟩ := hx
      rcases (hG'app x w).1 hw with hw | ⟨rfl, -⟩
      · obtain ⟨u, hu⟩ := hGatt.2.2.1 x y ⟨w, hw⟩ hxy
        exact ⟨u, (hG'app y u).2 (Or.inl hu)⟩
      · obtain ⟨u, hu⟩ := (hGdom y).2 (hbelow y hxy)
        exact ⟨u, (hG'app y u).2 (Or.inl hu)⟩
    · rcases (hG'app x w).1 hw with hw | ⟨rfl, rfl⟩
      · rw [hGatt.2.2.2 x w hw v]
        constructor
        · rintro ⟨y, hy, hv⟩; exact ⟨y, hy, (hG'app y v).2 (Or.inl hv)⟩
        · rintro ⟨y, hy, hv⟩
          rcases (hG'app y v).1 hv with hv | ⟨rfl, rfl⟩
          · exact ⟨y, hy, hv⟩
          · exact (hx0nG (hGatt.2.2.1 x y ⟨w, hw⟩ hy)).elim
      · rw [hwx v]
        constructor
        · rintro ⟨y, hy, hv⟩
          exact ⟨y, ((hpred y).1 hy).2, (hG'app y v).2 (Or.inl hv)⟩
        · rintro ⟨y, hy, hv⟩
          rcases (hG'app y v).1 hv with hv | ⟨rfl, rfl⟩
          · exact ⟨y, (hpred y).2 ⟨(hR y _ hy).1, hy⟩, hv⟩
          · exact (hx0nG ((hGdom y).2 (hbelow y hy))).elim
  exact hx0n ((hDstar x0).2 ⟨hx0D, G', hG'att, wx, (hG'app x0 wx).2 (Or.inr ⟨rfl, rfl⟩)⟩)

/-! ### The collapse identifies exactly `E`-related elements -/

/-- If `R` is extensional modulo the set equivalence `E` (and `E` is a
congruence for `R`), then the collapse of `R` sends `x` and `y` to the same
value exactly when `x E y`. -/
theorem collapse_eq_iff {D R E c : Z.S.X}
    (hR : ∀ y x, Z.S.FunApp R y x → (y ∈' D) ∧ (x ∈' D)) (hwf : Z.S.WellFoundedOn D R)
    (hc : Z.S.IsCollapseAttempt D R c)
    (hE_congr : ∀ z z' y, Z.S.FunApp E z z' → (Z.S.FunApp R z y ↔ Z.S.FunApp R z' y))
    (hE_congr_right : ∀ z x y, Z.S.FunApp E x y → (Z.S.FunApp R z x ↔ Z.S.FunApp R z y))
    (hE_ext : ∀ x y, (x ∈' D) → (y ∈' D) →
      (∀ z, (z ∈' D) → (Z.S.FunApp R z x ↔ Z.S.FunApp R z y)) → Z.S.FunApp E x y)
    {x y w w' : Z.S.X} (hx : x ∈' D) (hy : y ∈' D) (hw : Z.S.FunApp c x w)
    (hw' : Z.S.FunApp c y w') : w = w' ↔ Z.S.FunApp E x y := by
  constructor
  · intro heq
    subst heq
    let Bad : Z.S.X → Prop := fun x => (x ∈' D) ∧
      ∃ y w, (y ∈' D) ∧ Z.S.FunApp c x w ∧ Z.S.FunApp c y w ∧ ¬ Z.S.FunApp E x y
    have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
      refine Def.congr ?_ ((((Def.and_ (Def.mem (0 : Fin 4) 1) (Def.exists_ (Def.exists_ (Def.and_
        (Def.mem (Fin.castSucc (Fin.last 4)) (Fin.castSucc (Fin.castSucc 1)))
        (Def.and_ (Def.funApp (Fin.castSucc (Fin.castSucc 2)) (Fin.castSucc (Fin.castSucc 0))
          (Fin.last 5))
          (Def.and_ (Def.funApp (Fin.castSucc (Fin.castSucc 2)) (Fin.castSucc (Fin.last 4))
            (Fin.last 5))
            (Def.not_ (Def.funApp (Fin.castSucc (Fin.castSucc 3)) (Fin.castSucc (Fin.castSucc 0))
              (Fin.castSucc (Fin.last 4)))))))))).withParam E).withParam c).withParam D)
      intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
    by_contra hne
    obtain ⟨X, hX⟩ := Z.sepP hdef D
    obtain ⟨x0, hx0, hmin⟩ := hwf X (fun z hz => ((hX z).1 hz).1)
      ⟨x, (hX x).2 ⟨hx, hx, y, w, hy, hw, hw', hne⟩⟩
    obtain ⟨hx0D, -, y0, w0, hy0D, hw0, hw0', hne0⟩ := (hX x0).1 hx0
    have hgood : ∀ z z', Z.S.FunApp R z x0 → (z' ∈' D) → ∀ u, Z.S.FunApp c z u → Z.S.FunApp c z' u →
        Z.S.FunApp E z z' := by
      intro z z' hz hz' u hu hu'
      by_contra hb
      exact hmin z ((hX z).2 ⟨(hR z x0 hz).1, (hR z x0 hz).1, z', u, hz', hu, hu', hb⟩) hz
    apply hne0
    apply hE_ext x0 y0 hx0D hy0D
    intro z hzD
    constructor
    · intro hz
      obtain ⟨u, hu⟩ := hc.2.2.1 x0 z ⟨w0, hw0⟩ hz
      have hu' : u ∈' w0 := (hc.2.2.2 x0 w0 hw0 u).2 ⟨z, hz, hu⟩
      obtain ⟨z', hz', hu''⟩ := (hc.2.2.2 y0 w0 hw0' u).1 hu'
      have hE := hgood z z' hz (hR z' y0 hz').1 u hu hu''
      exact (hE_congr z z' y0 hE).2 hz'
    · intro hz'
      obtain ⟨u, hu'⟩ := hc.2.2.1 y0 z ⟨w0, hw0'⟩ hz'
      have hu : u ∈' w0 := (hc.2.2.2 y0 w0 hw0' u).2 ⟨z, hz', hu'⟩
      obtain ⟨z0, hz0, hu0⟩ := (hc.2.2.2 x0 w0 hw0 u).1 hu
      have hE := hgood z0 z hz0 hzD u hu0 hu'
      exact (hE_congr z0 z x0 hE).1 hz0
  · intro hE
    apply Z.ax.ext
    intro v
    rw [hc.2.2.2 x w hw v, hc.2.2.2 y w' hw' v]
    constructor
    · rintro ⟨z, hz, hv⟩; exact ⟨z, (hE_congr_right z x y hE).1 hz, hv⟩
    · rintro ⟨z, hz, hv⟩; exact ⟨z, (hE_congr_right z x y hE).2 hz, hv⟩

/-- The image of the collapse is a transitive set. -/
theorem collapse_image_transitive {D R c : Z.S.X} (hc : Z.S.IsCollapseAttempt D R c)
    {x w v : Z.S.X} (hw : Z.S.FunApp c x w) (hv : v ∈' w) : ∃ y, Z.S.FunApp c y v := by
  obtain ⟨y, -, hy⟩ := (hc.2.2.2 x w hw v).1 hv
  exact ⟨y, hy⟩

end ZFCModel

end SolidLean.Solid
