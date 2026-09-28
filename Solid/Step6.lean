import Solid.Config

/-!
# Step 6: assembling the definable isomorphism `M → N`

Once the bottom collapsed height is `κ 0` of `N`, every collapsed height is
the corresponding cutoff (`δ n = κ n`, by uniqueness of the next
inaccessible), every collapsed set is the image of the corresponding sort of
`N` (`S n = V(κ n)`, by uniqueness of `V_α`), and `h n x := (lift)⁻¹ (e n (i n x))`
is an isomorphism `M → N`, definable because it is the composite of
definable graphs (`Config.composite_def`).
-/

universe u

namespace SolidLean.Solid

open Classical ClassSystem

namespace ZFCModel

variable (Z : ZFCModel.{u})

/-- The next inaccessible above `α` is unique. -/
theorem nextInaccessible_unique {α β β' : Z.S.X} (h : Z.S.NextInaccessible α β)
    (h' : Z.S.NextInaccessible α β') : β = β' := by
  rcases IsOrdinal.trichotomy Z h.1.1.1 h'.1.1.1 with h1 | h1 | h1
  · exact (h'.2.2 β h.2.1 h1 h.1).elim
  · exact h1
  · exact (h.2.2 β' h'.2.1 h1 h'.1).elim

end ZFCModel

namespace Config

variable (c : Config.{u}) (C : CollapseData c.N c.P c.J.pres)

/-- **Step 6a.** All collapsed heights are the cutoffs of `N`. -/
theorem δ_eq_lift_kappa (hbottom : ∃ h0 : 1 ≤ C.b 1, C.δ 0 = c.N.T.liftLE h0 (c.N.T.κ 0)) :
    ∀ n, ∃ h : n + 1 ≤ C.b (n + 1), C.δ n = c.N.T.liftLE h (c.N.T.κ n) := by
  intro n
  induction n with
  | zero => exact hbottom
  | succ n ih =>
    obtain ⟨h, hδ⟩ := ih
    have hs := C.b_mono (n + 1)
    have h2 : n + 2 ≤ C.b (n + 2) := Nat.le_of_succ_le (C.b_ge (n + 2))
    refine ⟨h2, ?_⟩
    have hA := C.δ_next c.hN c.hP n
    have hB := ((c.hN.liftEmb h2).nextInaccessible_iff _ _).2 (c.hN.next_inaccessible n)
    simp only [IsTowerModel.liftEmb_φ] at hB
    have heq : c.N.T.liftLE hs (C.δ n) = c.N.T.liftLE h2 (c.N.T.j (n + 1) (c.N.T.κ n)) := by
      rw [hδ, c.N.T.liftLE_trans, IsTowerModel.j_eq_liftLE, c.N.T.liftLE_trans]
    rw [heq] at hA
    exact ZFCModel.nextInaccessible_unique (c.hN.sortModel (C.b (n + 2))) hA hB

/-- **Step 6b.** The collapsed sets are the images of the sorts of `N`. -/
theorem S_eq_lift_imageSet (hbottom : ∃ h0 : 1 ≤ C.b 1, C.δ 0 = c.N.T.liftLE h0 (c.N.T.κ 0))
    (n : ℕ) : C.S n = c.N.T.liftLE (C.b_ge n) (c.hN.imageSet n) := by
  obtain ⟨h, hδ⟩ := c.δ_eq_lift_kappa C hbottom n
  have hs := C.b_mono n
  have hV1 := C.isV c.hN c.hP n
  have hV2 := (c.hN.liftEmb h).isV_of (c.hN.imageSet_isV n)
  simp only [IsTowerModel.liftEmb_φ] at hV2
  rw [← hδ] at hV2
  have := ZFCModel.IsV.unique (c.hN.sortModel (C.b (n + 1))) hV1 hV2
  apply c.hN.liftLE_injective hs
  rw [this, c.N.T.liftLE_trans]

section Assembly

variable (hbottom : ∃ h0 : 1 ≤ C.b 1, C.δ 0 = c.N.T.liftLE h0 (c.N.T.κ 0))

include hbottom

theorem e_mem_lift_imageSet (n : ℕ) (x : c.M.T.U n) :
    c.N.T.mem (C.e n (c.i.toFun n x)) (c.N.T.liftLE (C.b_ge n) (c.hN.imageSet n)) := by
  rw [← c.S_eq_lift_imageSet C hbottom n]
  exact C.e_mem n _

/-- The assembled map `M n → N n`: the element whose lift is `e n (i n x)`. -/
noncomputable def hfun (n : ℕ) (x : c.M.T.U n) : c.N.T.U n :=
  Classical.choose ((c.hN.mem_lift_imageSet_iff (C.b_ge n) _).1 (c.e_mem_lift_imageSet C hbottom n x))

theorem hfun_spec (n : ℕ) (x : c.M.T.U n) :
    c.N.T.liftLE (Nat.le_of_succ_le (C.b_ge n)) (c.hfun C hbottom n x) = C.e n (c.i.toFun n x) :=
  Classical.choose_spec
    ((c.hN.mem_lift_imageSet_iff (C.b_ge n) _).1 (c.e_mem_lift_imageSet C hbottom n x))

theorem hfun_eq_iff (n : ℕ) (x : c.M.T.U n) (y : c.N.T.U n) :
    c.hfun C hbottom n x = y ↔
      c.N.T.liftLE (Nat.le_of_succ_le (C.b_ge n)) y = C.e n (c.i.toFun n x) := by
  constructor
  · rintro rfl; exact c.hfun_spec C hbottom n x
  · intro h
    apply c.hN.liftLE_injective (Nat.le_of_succ_le (C.b_ge n))
    rw [c.hfun_spec, h]

/-- **Step 6c.** The assembled isomorphism. -/
noncomputable def hiso : TowerIso c.M.T c.I.model where
  toFun := c.hfun C hbottom
  bijective := by
    intro n
    constructor
    · intro x x' hxx'
      have h1 := c.hfun_spec C hbottom n x
      have h2 := c.hfun_spec C hbottom n x'
      rw [hxx', h2] at h1
      exact (c.i.bijective n).1 (C.e_injective n h1.symm)
    · intro y
      have hy : c.N.T.mem (c.N.T.liftLE (Nat.le_of_succ_le (C.b_ge n)) y) (C.S n) := by
        rw [c.S_eq_lift_imageSet C hbottom n, c.hN.mem_lift_imageSet_iff]
        exact ⟨y, rfl⟩
      obtain ⟨q, hq⟩ := C.e_surj n _ hy
      obtain ⟨x, rfl⟩ := (c.i.bijective n).2 q
      exact ⟨x, (c.hfun_eq_iff C hbottom n x y).2 hq.symm⟩
  mem_iff := by
    intro n x y
    show c.N.T.mem (c.hfun C hbottom n x) (c.hfun C hbottom n y) ↔ _
    rw [← c.hN.liftLE_mem_iff (Nat.le_of_succ_le (C.b_ge n)), c.hfun_spec, c.hfun_spec,
      C.e_mem_iff, c.i.mem_iff]
  j_comm := by
    intro n x
    show c.hfun C hbottom (n + 1) (c.M.T.j n x) = c.N.T.j n (c.hfun C hbottom n x)
    rw [c.hfun_eq_iff, c.i.j_comm, ← C.e_transition, ← c.hfun_spec C hbottom n x,
      IsTowerModel.j_eq_liftLE, c.N.T.liftLE_trans, c.N.T.liftLE_trans]
  κ_comm := by
    intro n
    show c.hfun C hbottom (n + 1) (c.M.T.κ n) = c.N.T.κ n
    rw [c.hfun_eq_iff, c.i.κ_comm]
    obtain ⟨h, hδ⟩ := c.δ_eq_lift_kappa C hbottom n
    exact hδ.symm

/-- **Step 6d.** The assembled isomorphism is definable. -/
theorem hiso_definable : (c.hiso C hbottom).DefinableIn c.M.𝒟 c.I.pres := by
  intro n
  refine TDef.congr ?_ (c.composite_lift_def n n (C.b n) (Nat.le_of_succ_le (C.b_ge n)) (C.e n)
    (C.e_definable n))
  intro t
  constructor
  · rintro ⟨x, r, hx, hr, y, hIr, hlift⟩
    refine ⟨x, r, hx, hr, ?_⟩
    rw [hIr]
    exact congrArg some ((c.hfun_eq_iff C hbottom n x y).2 hlift).symm
  · rintro ⟨x, r, hx, hr, hrep⟩
    exact ⟨x, r, hx, hr, c.hfun C hbottom n x, hrep, c.hfun_spec C hbottom n x⟩

/-- **Step 6.** -/
theorem assemble_iso : ∃ h : TowerIso c.M.T c.I.model, h.DefinableIn c.M.𝒟 c.I.pres :=
  ⟨c.hiso C hbottom, c.hiso_definable C hbottom⟩

end Assembly

end Config

end SolidLean.Solid
