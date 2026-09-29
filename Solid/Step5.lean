module

public import Solid.Collapse

/-!
# Step 5, first half: the bottom collapsed height is at most `κ 0`

`bottom_le_kappa`: the bottom height `δ 0` lies in some sort of `N`, hence
below the cutoff `κ s` of that sort; the cutoffs `κ 0 ∈ κ 1 ∈ ⋯ ∈ κ s`
form a ladder of consecutive inaccessibles, and an inaccessible with no
greatest inaccessible below it cannot lie strictly between two consecutive
ones nor equal a successor one; so `δ 0 ≤ κ 0`.

`below_propagates`: if `δ 0 < κ 0` then every `δ n < κ 0`, since `δ (n+1)`
is the least inaccessible above `δ n` while `κ 0`, an inaccessible above
`δ n`, is not the least one above anything (no greatest inaccessible below
it).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

namespace CollapseData

variable {N PC : TowerWithClasses.{u}} {p : Presentation N.T.U PC.T.U} (C : CollapseData N PC p)
  (hN : IsTowerModel N) (hP : IsTowerModel PC)

include hN hP in
/-- **Step 5, first half.** -/
theorem bottom_le_kappa : ∃ h0 : 1 ≤ C.b 1,
    N.T.mem (C.δ 0) (N.T.liftLE h0 (N.T.κ 0)) ∨ C.δ 0 = N.T.liftLE h0 (N.T.κ 0) := by
  set s := C.b 1 with hs
  have h0 : 1 ≤ s := le_trans (Nat.le_succ 1) (C.b_ge 1)
  refine ⟨h0, ?_⟩
  -- work in sort `t = s + 1`
  let t := s + 1
  let Z := hN.sortModel t
  let d : N.T.U t := N.T.j s (C.δ 0)
  let K : ∀ m, m + 1 ≤ t → N.T.U t := fun m hm => N.T.liftLE hm (N.T.κ m)
  have hd_inacc : (N.T.sortStr t).Inaccessible d :=
    ((hN.jEmb s).inaccessible_iff _).2 (C.δ_inaccessible hN hP 0)
  have hd_ng : (N.T.sortStr t).NoGreatestInaccessibleBelow d :=
    ((hN.jEmb s).noGreatestInaccessibleBelow_iff _).2 (C.δ_bottom hN hP)
  have hd_ord : (N.T.sortStr t).IsOrdinal d := hd_inacc.1.1
  have hK_inacc : ∀ m (hm : m + 1 ≤ t), (N.T.sortStr t).Inaccessible (K m hm) :=
    fun m hm => ((hN.liftEmb hm).inaccessible_iff _).2 (hN.kappa_inaccessible m)
  have hK_next : ∀ m (hm : m + 2 ≤ t),
      (N.T.sortStr t).NextInaccessible (K m (Nat.le_of_succ_le hm)) (K (m + 1) hm) := by
    intro m hm
    have h := ((hN.liftEmb hm).nextInaccessible_iff _ _).2 (hN.next_inaccessible m)
    simp only [IsTowerModel.liftEmb_φ] at h
    have : N.T.liftLE hm (N.T.j (m + 1) (N.T.κ m)) = K m (Nat.le_of_succ_le hm) := by
      show _ = N.T.liftLE _ (N.T.κ m)
      rw [IsTowerModel.j_eq_liftLE, N.T.liftLE_trans]
    rw [this] at h
    exact h
  -- `d ∈ κ s`
  have hd_Ks : N.T.mem d (K s (le_refl t)) := by
    have hKs : K s (le_refl t) = N.T.κ s := MemTower.liftLE_self _ _
    rw [hKs]
    have hdimg : N.T.mem d (hN.imageSet s) := (hN.mem_imageSet_iff s d).2 ⟨C.δ 0, rfl⟩
    have hV := hN.imageSet_isV s
    rcases ZFCModel.IsOrdinal.trichotomy Z hd_ord (hK_inacc s (le_refl t)).1.1 with h | h | h
    · rw [hKs] at h; exact h
    · exfalso
      rw [hKs] at h
      rw [h] at hdimg
      exact ZFCModel.IsV.not_mem_self Z hV hdimg
    · exfalso
      rw [hKs] at h
      exact ZFCModel.IsV.not_mem_self Z hV (ZFCModel.IsV.transitive Z hV d hdimg _ h)
  -- the ladder argument in sort `t`
  have hmain : N.T.mem d (K 0 (Nat.succ_le_succ (Nat.zero_le s))) ∨
      d = K 0 (Nat.succ_le_succ (Nat.zero_le s)) := by
    by_contra hcon
    have hK0d : N.T.mem (K 0 (Nat.succ_le_succ (Nat.zero_le s))) d := by
      rcases ZFCModel.IsOrdinal.trichotomy Z hd_ord (hK_inacc 0 _).1.1 with h | h | h
      · exact (hcon (Or.inl h)).elim
      · exact (hcon (Or.inr h)).elim
      · exact h
    have hind : ∀ m (hm : m ≤ s), N.T.mem (K m (Nat.succ_le_succ hm)) d := by
      intro m
      induction m with
      | zero => intro _; exact hK0d
      | succ m ih =>
        intro hm
        have hm' : m ≤ s := Nat.le_of_succ_le hm
        have hKm := ih hm'
        have hnext := hK_next m (Nat.succ_le_succ hm)
        rcases ZFCModel.IsOrdinal.trichotomy Z hd_ord (hK_inacc (m + 1) _).1.1 with h | h | h
        · exfalso
          exact hnext.2.2 d hKm h hd_inacc
        · exfalso
          obtain ⟨β, hβd, hKβ, hβi⟩ := hd_ng _ hKm (hK_inacc m _)
          rw [h] at hβd
          exact hnext.2.2 β hKβ hβd hβi
        · exact h
    exact ZFCModel.mem_asymm Z (hind s (le_refl s)) hd_Ks
  -- transfer back to sort `s`
  have hK0 : K 0 (Nat.succ_le_succ (Nat.zero_le s)) = N.T.j s (N.T.liftLE h0 (N.T.κ 0)) := by
    show N.T.liftLE _ (N.T.κ 0) = _
    rw [← N.T.liftLE_succ h0]
  rw [hK0] at hmain
  rcases hmain with h | h
  · exact Or.inl ((hN.j_mem_iff s _ _).1 h)
  · exact Or.inr (hN.j_injective s _ _ h)

include hN hP in
/-- **Step 5, propagation.** -/
theorem below_propagates (h0 : 1 ≤ C.b 1)
    (hlt : N.T.mem (C.δ 0) (N.T.liftLE h0 (N.T.κ 0))) :
    ∀ n, ∃ h : 1 ≤ C.b (n + 1), N.T.mem (C.δ n) (N.T.liftLE h (N.T.κ 0)) := by
  intro n
  induction n with
  | zero => exact ⟨h0, hlt⟩
  | succ n ih =>
    obtain ⟨h, hmem⟩ := ih
    have hs := C.b_mono (n + 1)
    have h' : 1 ≤ C.b (n + 2) := h.trans hs
    refine ⟨h', ?_⟩
    let Z := hN.sortModel (C.b (n + 2))
    have hmem' : N.T.mem (N.T.liftLE hs (C.δ n)) (N.T.liftLE h' (N.T.κ 0)) := by
      rw [← N.T.liftLE_trans h hs, hN.liftLE_mem_iff]
      exact hmem
    have hnext := C.δ_next hN hP n
    have hκi : (N.T.sortStr (C.b (n + 2))).Inaccessible (N.T.liftLE h' (N.T.κ 0)) :=
      ((hN.liftEmb h').inaccessible_iff _).2 (hN.kappa_inaccessible 0)
    have hκng : (N.T.sortStr (C.b (n + 2))).NoGreatestInaccessibleBelow (N.T.liftLE h' (N.T.κ 0)) :=
      ((hN.liftEmb h').noGreatestInaccessibleBelow_iff _).2 hN.bottom
    rcases ZFCModel.IsOrdinal.trichotomy Z (C.δ_ordinal hN hP (n + 1)) hκi.1.1 with h1 | h1 | h1
    · exact h1
    · exfalso
      have hδi : (N.T.sortStr (C.b (n + 2))).Inaccessible (N.T.liftLE hs (C.δ n)) :=
        ((hN.liftEmb hs).inaccessible_iff _).2 (C.δ_inaccessible hN hP n)
      obtain ⟨β, hβκ, hδβ, hβi⟩ := hκng _ hmem' hδi
      rw [← h1] at hβκ
      exact hnext.2.2 β hδβ hβκ hβi
    · exfalso
      exact hnext.2.2 _ hmem' h1 hκi

end CollapseData

end SolidLean.Solid
