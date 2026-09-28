import Solid.Config

/-!
# Step 5, second half: the finite-support cardinality obstruction

If every collapsed height lay below `κ 0` of `N`, every collapsed sort would
lie inside the image of sort `0` of `N`.  Sort `0` of `N` is presented by a
class of sort `K := I.a 0` of `M`; composing with `i`, sort `K+1` of `M`
would then inject `M`-definably into sort `K` of `M`, i.e. into the set
`V(κ K)` of sort `K+1`.  Replacement along the inverse of that injection
would make the universe of sort `K+1` a set, a member of itself.
-/

universe u

namespace SolidLean.Solid

open Classical ClassSystem

namespace Config

variable (c : Config.{u}) (C : CollapseData c.N c.P c.J.pres)

/-- **Step 5, second half.** -/
theorem not_all_below_bottom :
    ¬ ∀ n, ∃ h : 1 ≤ C.b (n + 1), c.N.T.mem (C.δ n) (c.N.T.liftLE h (c.N.T.κ 0)) := by
  intro hall
  -- the sorts involved
  set K := c.I.a 0 with hK
  set n := K + 1 with hn
  set t := C.b (n + 1) with ht
  have hs : C.b n ≤ t := C.b_mono n
  obtain ⟨h1, hδ⟩ := hall n
  have h0t : 0 ≤ t := Nat.zero_le t
  let ZN := c.hN.sortModel t
  -- every collapsed element of sort `n` of `P` lies in the image of sort `0` of `N`
  have hV0 := (c.hN.liftEmb h1).isV_of (c.hN.imageSet_isV 0)
  simp only [IsTowerModel.liftEmb_φ] at hV0
  have hVn := C.isV c.hN c.hP n
  have hsub := (ZFCModel.IsV.mono ZN hV0 hVn hδ).2
  have hex : ∀ x : c.M.T.U n, ∃ y : c.N.T.U 0,
      c.N.T.liftLE h0t y = c.N.T.liftLE hs (C.e n (c.i.toFun n x)) := by
    intro x
    have hmem : c.N.T.mem (c.N.T.liftLE hs (C.e n (c.i.toFun n x)))
        (c.N.T.liftLE h1 (c.hN.imageSet 0)) :=
      hsub _ ((c.hN.liftLE_mem_iff hs _ _).2 (C.e_mem n _))
    exact (c.hN.mem_lift_imageSet_iff h1 _).1 hmem
  let g : c.M.T.U n → c.N.T.U 0 := fun x => Classical.choose (hex x)
  have hg : ∀ x, c.N.T.liftLE h0t (g x) = c.N.T.liftLE hs (C.e n (c.i.toFun n x)) :=
    fun x => Classical.choose_spec (hex x)
  have hg_iff : ∀ x y, g x = y ↔ c.N.T.liftLE h0t y = c.N.T.liftLE hs (C.e n (c.i.toFun n x)) := by
    intro x y
    constructor
    · rintro rfl; exact hg x
    · intro h
      apply c.hN.liftLE_injective h0t
      rw [hg, h]
  have hg_inj : ∀ x x', g x = g x' → x = x' := by
    intro x x' h
    have := hg x
    rw [h, hg x'] at this
    exact (c.i.bijective n).1 (C.e_injective n (c.hN.liftLE_injective hs this.symm))
  -- the relation "`r` represents `g x`" is definable in `M`
  have hG := c.composite_lift_def n 0 t h0t (fun q => c.N.T.liftLE hs (C.e n q))
    (PGraph.lift c.N.𝒟 c.J.pres hs (C.e_definable n))
  have hG' : c.M.𝒟.TDef 2 (fun t => ∃ (x : c.M.T.U n) (r : c.M.T.U K),
      t 0 = c.M.T.inj x ∧ t 1 = c.M.T.inj r ∧ c.I.pres.rep 0 r = some (g x)) := by
    refine TDef.congr ?_ hG
    intro t
    constructor
    · rintro ⟨x, r, hx, hr, y, hIr, hlift⟩
      refine ⟨x, r, hx, hr, ?_⟩
      rw [hIr, (hg_iff x y).2 hlift]
    · rintro ⟨x, r, hx, hr, hIr⟩
      exact ⟨x, r, hx, hr, g x, hIr, hg x⟩
  -- push into sort `K + 1 = n` through `j K`
  let R : c.M.T.U n → c.M.T.U n → Prop := fun x r' =>
    ∃ r : c.M.T.U K, c.M.T.j K r = r' ∧ c.I.pres.rep 0 r = some (g x)
  have hR : (c.M.𝒟.sortSystem n).Def 2 (fun t => R (t 0) (t 1)) := by
    apply TDef.toDef2
    refine TDef.congr ?_ (TDef.exists_ K (TDef.and_ (TDef.reindex ![0, 2] hG')
      (TDef.j_sort K 2 1)))
    intro t
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
    constructor
    · rintro ⟨r, ⟨x, r₁, hx, hr₁, hrep⟩, r₂, hr₂, hj⟩
      have e1 : r₁ = r := MemTower.inj_injective' _ hr₁.symm
      have e2 : r₂ = r := MemTower.inj_injective' _ hr₂.symm
      rw [e1] at hrep
      rw [e2] at hj
      exact ⟨x, c.M.T.j K r, hx, hj, r, rfl, hrep⟩
    · rintro ⟨x, r', hx, hr', r, rfl, hrep⟩
      exact ⟨r, ⟨x, r, hx, rfl, hrep⟩, r, rfl, hr'⟩
  -- the contradiction in sort `n` of `M`
  let Z := c.hM.sortModel n
  have hRfun : ∀ x x' r', R x r' → R x' r' → x = x' := by
    rintro x x' r' ⟨r, rfl, hrep⟩ ⟨r₂, hr₂, hrep₂⟩
    have := c.hM.j_injective K _ _ hr₂
    subst this
    exact hg_inj x x' (Option.some_injective _ (hrep.symm.trans hrep₂))
  have hRtot : ∀ x, ∃ r', c.M.T.mem r' (c.hM.imageSet K) ∧ R x r' := by
    intro x
    obtain ⟨r, hr⟩ := c.I.pres.surj 0 (g x)
    exact ⟨c.M.T.j K r, (c.hM.mem_imageSet_iff K _).2 ⟨r, rfl⟩, r, rfl, hr⟩
  -- the image of `R` inside `V(κ K)`
  have himdef : Z.𝒞.Def 1 (fun t => ∃ x, R x (t 0)) := by
    refine SetClassSystem.Def.congr ?_ (SetClassSystem.Def.exists_
      (SetClassSystem.Def.reindex ![1, 0] hR))
    intro t
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.snoc_one_zero, Fin.snoc_one_one]
    try exact Iff.rfl
  obtain ⟨im, him⟩ := Z.sepP (P := fun r' => ∃ x, R x r') himdef (c.hM.imageSet K)
  -- replacement along the inverse of `R`
  have hinvdef : Z.𝒞.Def 2 (fun t => R (t 1) (t 0)) := by
    refine SetClassSystem.Def.congr ?_ (SetClassSystem.Def.reindex ![1, 0] hR)
    intro t
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  obtain ⟨U, hU⟩ := Z.replP hinvdef im (by
    intro r' hr'
    obtain ⟨-, x, hx⟩ := (him r').1 hr'
    exact ⟨x, hx, fun x' hx' => hRfun x' x r' hx' hx⟩)
  -- `U` contains everything, in particular itself
  have hUall : ∀ x : c.M.T.U n, c.M.T.mem x U := by
    intro x
    obtain ⟨r', hr'img, hR'⟩ := hRtot x
    exact (hU x).2 ⟨r', (him r').2 ⟨hr'img, x, hR'⟩, hR'⟩
  exact Z.mem_irrefl U (hUall U)

end Config

end SolidLean.Solid
