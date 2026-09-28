import Solid.Step1

/-!
# Steps 1 and 3: the collapse of one sort of `P`

With `D`, `R`, `E` and well-foundedness from `Solid.Step1`, the internal
Mostowski collapse of `(D, R)` exists in sort `J.a n + 1` of `N`.  It sends
`E`-equivalent representatives to the same value and inequivalent ones to
different values, hence descends to an injective membership-preserving map
`e₀` on sort `n` of `P` onto a transitive set `S₀`.

Step 3 (`S₀` is closed under subsets) is where the isomorphism `i` and
Separation in `M` enter: an `N`-subset `z` of `e₀ q` determines the
`M`-definable class `{x | e₀ (i x) ∈ z}` of sort `n` of `M`, contained in the
members of `i⁻¹ q`; Separation makes it a set `x₁`, and `e₀ (i x₁) = z`.
-/

universe u

namespace SolidLean.Solid

open Classical ClassSystem

namespace Config

variable (c : Config.{u}) (n : ℕ)

/-- **Steps 1 and 3.** -/
theorem levelCollapse_exists : Nonempty (LevelCollapse c.N c.P c.J.pres n (c.J.a n + 1)) := by
  let a := c.J.a n
  let s := a + 1
  let Zs := c.hN.sortModel s
  obtain ⟨D, hD⟩ := c.exists_D n
  obtain ⟨R, hR⟩ := c.exists_R n D hD
  obtain ⟨E, hE⟩ := c.exists_E n D hD
  have hRD : ∀ y x, Zs.S.FunApp R y x → Zs.S.mem y D ∧ Zs.S.mem x D := by
    intro y x h
    obtain ⟨u, u', rfl, rfl, hu, hu', -⟩ := (hR y x).1 h
    exact ⟨(hD _).2 ⟨u, rfl, hu⟩, (hD _).2 ⟨u', rfl, hu'⟩⟩
  have hwf := c.wf_R n D R hD hR
  obtain ⟨c₀, hc₀, hc₀dom⟩ := Zs.exists_collapse D R hRD hwf
  -- the equivalence is a congruence for the relation and extensional
  have hE_congr : ∀ z z' y, Zs.S.FunApp E z z' → (Zs.S.FunApp R z y ↔ Zs.S.FunApp R z' y) := by
    intro z z' y hzz'
    obtain ⟨u, u', rfl, rfl, hu, hu', heqv⟩ := (hE z z').1 hzz'
    rw [hR, hR]
    constructor
    · rintro ⟨v, v', hv, hv', -, hv'd, hm⟩
      have e := c.hN.j_injective a _ _ hv
      rw [← e] at hm
      exact ⟨u', v', rfl, hv', hu', hv'd,
        (c.J.memC_congr n u u' v' v' heqv (c.J.eqv_refl n v' hv'd)).1 hm⟩
    · rintro ⟨v, v', hv, hv', -, hv'd, hm⟩
      have e := c.hN.j_injective a _ _ hv
      rw [← e] at hm
      exact ⟨u, v', rfl, hv', hu, hv'd,
        (c.J.memC_congr n u u' v' v' heqv (c.J.eqv_refl n v' hv'd)).2 hm⟩
  have hE_congr_right : ∀ z x y, Zs.S.FunApp E x y → (Zs.S.FunApp R z x ↔ Zs.S.FunApp R z y) := by
    intro z x y hxy
    obtain ⟨u, u', rfl, rfl, hu, hu', heqv⟩ := (hE x y).1 hxy
    rw [hR, hR]
    constructor
    · rintro ⟨v, v', hv, hv', hvd, -, hm⟩
      have e := c.hN.j_injective a _ _ hv'
      rw [← e] at hm
      exact ⟨v, u', hv, rfl, hvd, hu', (c.J.memC_congr n v v u u' (c.J.eqv_refl n v hvd) heqv).1 hm⟩
    · rintro ⟨v, v', hv, hv', hvd, -, hm⟩
      have e := c.hN.j_injective a _ _ hv'
      rw [← e] at hm
      exact ⟨v, u, hv, rfl, hvd, hu, (c.J.memC_congr n v v u u' (c.J.eqv_refl n v hvd) heqv).2 hm⟩
  have hE_ext : ∀ x y, Zs.S.mem x D → Zs.S.mem y D →
      (∀ z, Zs.S.mem z D → (Zs.S.FunApp R z x ↔ Zs.S.FunApp R z y)) → Zs.S.FunApp E x y := by
    intro x y hx hy hext
    obtain ⟨u, rfl, hu⟩ := (hD x).1 hx
    obtain ⟨u', rfl, hu'⟩ := (hD y).1 hy
    refine (hE _ _).2 ⟨u, u', rfl, rfl, hu, hu', ?_⟩
    -- extensionality in `P`
    have hPext := (c.hP.zfc n).ext (c.J.cls ⟨u, hu⟩) (c.J.cls ⟨u', hu'⟩)
    have : c.J.cls ⟨u, hu⟩ = c.J.cls ⟨u', hu'⟩ := by
      apply hPext
      intro q
      induction q using Quotient.ind with
      | _ v =>
        show c.J.memC n v.1 u ↔ c.J.memC n v.1 u'
        have h1 := hext (c.N.T.j a v.1) ((hD _).2 ⟨v.1, rfl, v.2⟩)
        rw [hR, hR] at h1
        constructor
        · intro hm
          obtain ⟨w, w', hw, hw', -, -, hm'⟩ := h1.1 ⟨v.1, u, rfl, rfl, v.2, hu, hm⟩
          rw [← c.hN.j_injective a _ _ hw, ← c.hN.j_injective a _ _ hw'] at hm'
          exact hm'
        · intro hm
          obtain ⟨w, w', hw, hw', -, -, hm'⟩ := h1.2 ⟨v.1, u', rfl, rfl, v.2, hu', hm⟩
          rw [← c.hN.j_injective a _ _ hw, ← c.hN.j_injective a _ _ hw'] at hm'
          exact hm'
    exact (c.J.cls_eq_iff _ _).1 this
  -- values of the collapse on representatives
  have hval : ∀ u, u ∈ c.J.dom n → ∃ w, Zs.S.FunApp c₀ (c.N.T.j a u) w :=
    fun u hu => (hc₀dom _).2 ((hD _).2 ⟨u, rfl, hu⟩)
  have hceq : ∀ x y w w', Zs.S.mem x D → Zs.S.mem y D → Zs.S.FunApp c₀ x w →
      Zs.S.FunApp c₀ y w' → (w = w' ↔ Zs.S.FunApp E x y) :=
    fun x y w w' hx hy hw hw' =>
      Zs.collapse_eq_iff hRD hwf hc₀ hE_congr hE_congr_right hE_ext hx hy hw hw'
  have hEj : ∀ u u', u ∈ c.J.dom n → u' ∈ c.J.dom n →
      (Zs.S.FunApp E (c.N.T.j a u) (c.N.T.j a u') ↔ c.J.eqv n u u') := by
    intro u u' hu hu'
    rw [hE]
    constructor
    · rintro ⟨v, v', hv, hv', -, -, h⟩
      rw [← c.hN.j_injective a _ _ hv, ← c.hN.j_injective a _ _ hv'] at h
      exact h
    · intro h; exact ⟨u, u', rfl, rfl, hu, hu', h⟩
  -- the map on sort `n` of `P`
  let rep : c.J.model.U n → c.N.T.U a := fun q => Classical.choose (c.J.pres.surj n q)
  have hrep : ∀ q, c.J.pres.rep n (rep q) = some q :=
    fun q => Classical.choose_spec (c.J.pres.surj n q)
  have hrepd : ∀ q, rep q ∈ c.J.dom n := fun q => c.J.pres_rep_dom (hrep q)
  have hrepcls : ∀ q, c.J.cls ⟨rep q, hrepd q⟩ = q :=
    fun q => ((c.J.pres_rep_eq_some_iff _ _).1 (hrep q)).2
  let e₀ : c.J.model.U n → c.N.T.U s := fun q => Classical.choose (hval (rep q) (hrepd q))
  have he₀ : ∀ q, Zs.S.FunApp c₀ (c.N.T.j a (rep q)) (e₀ q) :=
    fun q => Classical.choose_spec (hval (rep q) (hrepd q))
  have hjD : ∀ u, u ∈ c.J.dom n → Zs.S.mem (c.N.T.j a u) D := fun u hu => (hD _).2 ⟨u, rfl, hu⟩
  have he₀_rep : ∀ u q, c.J.pres.rep n u = some q → Zs.S.FunApp c₀ (c.N.T.j a u) (e₀ q) := by
    intro u q hq
    obtain ⟨hu, hcls⟩ := (c.J.pres_rep_eq_some_iff u q).1 hq
    obtain ⟨w, hw⟩ := hval u hu
    have heqv : c.J.eqv n u (rep q) := (c.J.cls_eq_iff _ _).1 (hcls.trans (hrepcls q).symm)
    have := (hceq _ _ w (e₀ q) (hjD u hu) (hjD _ (hrepd q)) hw (he₀ q)).2
      ((hEj u _ hu (hrepd q)).2 heqv)
    rw [← this]; exact hw
  -- membership in `P` through representatives
  have hPmem : ∀ q q', c.J.model.mem q q' ↔ c.J.memC n (rep q) (rep q') := by
    intro q q'
    show c.J.model.mem q q' ↔ _
    conv_lhs => rw [← hrepcls q, ← hrepcls q']
    exact Iff.rfl
  -- the image set
  have hfdef : Zs.𝒞.Def 2 (fun t => Zs.S.FunApp c₀ (t 0) (t 1)) := by
    refine SetClassSystem.Def.congr ?_ ((SetClassSystem.Def.funApp (2 : Fin 3) 0 1).withParam c₀)
    intro t; exact Iff.rfl
  obtain ⟨S₀, hS₀⟩ := Zs.replP hfdef D (by
    intro y hy
    obtain ⟨w, hw⟩ := (hc₀dom y).2 hy
    exact ⟨w, hw, fun w' hw' => Zs.funApp_unique hc₀.1 hw' hw⟩)
  have he₀_mem : ∀ q, Zs.S.mem (e₀ q) S₀ := fun q => (hS₀ _).2 ⟨_, hjD _ (hrepd q), he₀ q⟩
  have he₀_surj : ∀ w, Zs.S.mem w S₀ → ∃ q, e₀ q = w := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := (hS₀ w).1 hw
    obtain ⟨u, rfl, hu⟩ := (hD y).1 hy
    refine ⟨c.J.cls ⟨u, hu⟩, ?_⟩
    exact Zs.funApp_unique hc₀.1 (he₀_rep u _ (c.J.pres_rep_cls ⟨u, hu⟩)) hyw
  have hS₀_trans : ∀ w, Zs.S.mem w S₀ → ∀ v, Zs.S.mem v w → Zs.S.mem v S₀ := by
    intro w hw v hv
    obtain ⟨y, hy, hyw⟩ := (hS₀ w).1 hw
    obtain ⟨y', hy'⟩ := Zs.collapse_image_transitive hc₀ hyw hv
    exact (hS₀ v).2 ⟨y', (hc₀dom y').1 ⟨v, hy'⟩, hy'⟩
  have he₀_inj : Function.Injective e₀ := by
    intro q q' h
    have hEqq := (hceq _ _ _ _ (hjD _ (hrepd q)) (hjD _ (hrepd q')) (he₀ q) (he₀ q')).1 h
    have heqv := (hEj _ _ (hrepd q) (hrepd q')).1 hEqq
    rw [← hrepcls q, ← hrepcls q']
    exact (c.J.cls_eq_iff _ _).2 heqv
  have he₀_mem_iff : ∀ q q', Zs.S.mem (e₀ q) (e₀ q') ↔ c.J.model.mem q q' := by
    intro q q'
    rw [hc₀.2.2.2 _ _ (he₀ q') (e₀ q), hPmem]
    constructor
    · rintro ⟨y, hy, hyq⟩
      obtain ⟨u, u', rfl, hu', hu, -, hm⟩ := (hR y _).1 hy
      have := c.hN.j_injective a _ _ hu'
      subst this
      have hEuq := (hceq _ _ _ _ (hjD u hu) (hjD _ (hrepd q)) hyq (he₀ q)).1 rfl
      have heqv := (hEj _ _ hu (hrepd q)).1 hEuq
      exact (c.J.memC_congr n u (rep q) (rep q') (rep q') heqv (c.J.eqv_refl n _ (hrepd q'))).1 hm
    · intro hm
      exact ⟨_, (hR _ _).2 ⟨rep q, rep q', rfl, rfl, hrepd q, hrepd q', hm⟩, he₀ q⟩
  -- definability of the graph
  have he₀_def : PGraph c.J.pres e₀ ∈ c.N.𝒟.D 2 := by
    rw [PGraph.tdef_iff]
    have hdom : c.N.𝒟.TDef 1 (fun t => ∃ u : c.N.T.U a, t 0 = c.N.T.inj u ∧ u ∈ c.J.dom n) :=
      c.J.dom_def n
    have hfun : (c.N.𝒟.sortSystem s).Def 2 (fun t => Zs.S.FunApp c₀ (t 0) (t 1)) := hfdef
    refine TDef.congr ?_ (TDef.exists_ s (TDef.and_ (TDef.reindex (fun _ : Fin 1 => (0 : Fin 3)) hdom)
      (TDef.and_ (TDef.j_sort a 0 2) (TDef.lift2 s hfun 2 1))))
    intro t
    simp only [Function.comp_apply, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two]
    constructor
    · rintro ⟨y, ⟨u, hu, hud⟩, ⟨u', hu', hy⟩, y', w, hy', hw, hfw⟩
      have e1 : u' = u := MemTower.inj_injective' _ (hu'.symm.trans hu)
      have e2 : y' = y := MemTower.inj_injective' _ hy'.symm
      have e3 : y = c.N.T.j a u := by rw [← e1]; exact MemTower.inj_injective' _ hy
      rw [e2, e3] at hfw
      refine ⟨u, c.J.cls ⟨u, hud⟩, hu, ?_, c.J.pres_rep_cls ⟨u, hud⟩⟩
      rw [hw]
      congr 1
      exact Zs.funApp_unique hc₀.1 hfw (he₀_rep u _ (c.J.pres_rep_cls ⟨u, hud⟩))
    · rintro ⟨u, q, hu, hw, hq⟩
      exact ⟨c.N.T.j a u, ⟨u, hu, c.J.pres_rep_dom hq⟩, ⟨u, hu, rfl⟩, _, e₀ q, rfl, hw, he₀_rep u q hq⟩
  -- Step 3: closure under subsets
  have hsuper : ∀ w z, Zs.S.mem w S₀ → Zs.S.Subset z w → Zs.S.mem z S₀ := by
    intro w z hw hzw
    obtain ⟨q, rfl⟩ := he₀_surj w hw
    obtain ⟨x0, hx0⟩ := (c.i.bijective n).2 q
    -- the class `{x | e₀ (i x) ∈ z}` of sort `n` of `M`
    have hQ : ({t | ∃ (u : c.N.T.U a) (y : c.N.T.U s), t 0 = c.N.T.inj u ∧ t 1 = c.N.T.inj y ∧
        ∃ q', c.J.pres.rep n u = some q' ∧ Zs.S.mem (e₀ q') z} : c.N.T.Rel 2) ∈ c.N.𝒟.D 2 := by
      have hg := he₀_def
      rw [PGraph.tdef_iff] at hg
      refine TDef.congr ?_ (TDef.and_ (TDef.sort 1 s) (TDef.exists_ s (TDef.withParam
        (c.N.T.inj z) (TDef.and_ (TDef.reindex ![0, 2] hg) (TDef.mem_sort s 2 3)))))
      intro t
      simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero,
        Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three]
      constructor
      · rintro ⟨hs, w', ⟨u, q', hu, hw', hq'⟩, x', z', hx', hz', hmem⟩
        have e1 : x' = w' := MemTower.inj_injective' _ hx'.symm
        have e2 : z' = z := MemTower.inj_injective' _ hz'.symm
        have e3 : w' = e₀ q' := MemTower.inj_injective' _ hw'
        rw [e1, e2, e3] at hmem
        exact ⟨u, c.N.T.toSort (t 1) hs, hu, (c.N.T.inj_toSort _ _).symm, q', hq', hmem⟩
      · rintro ⟨u, y, hu, hy, q', hq', hmem⟩
        exact ⟨by rw [hy], e₀ q', ⟨u, q', hu, rfl, hq'⟩, e₀ q', z, rfl, rfl, hmem⟩
    let Cz : c.M.T.U n → Prop := fun x => Zs.S.mem (e₀ (c.i.toFun n x)) z
    have hCz : c.M.𝒟.TDef 1 (fun t => ∃ x : c.M.T.U n, t 0 = c.M.T.inj x ∧ Cz x) := by
      refine TDef.congr ?_ (TDef.exists_ (c.I.a s) (c.composite_def n s hQ))
      intro t
      simp only [Fin.snoc_one_zero, Fin.snoc_one_one]
      constructor
      · rintro ⟨r, x, r', hx, hr', u, y, hJu, hIr, hQ'⟩
        obtain ⟨u', y', hu', hy', q', hq', hmem⟩ := hQ'
        have e1 : u' = u := MemTower.inj_injective' _ hu'.symm
        rw [e1] at hq'
        have e2 : q' = c.i.toFun n x := Option.some_injective _ (hq'.symm.trans hJu)
        rw [e2] at hmem
        exact ⟨x, hx, hmem⟩
      · rintro ⟨x, hx, hmem⟩
        obtain ⟨r, hr⟩ := c.I.pres.surj s z
        obtain ⟨u, hu⟩ := c.J.pres.surj n (c.i.toFun n x)
        exact ⟨r, x, r, hx, rfl, u, z, hu, hr, u, z, rfl, rfl, _, hu, hmem⟩
    let Zn := c.hM.sortModel n
    have hCzdef : Zn.𝒞.Def 1 (fun t => Cz (t 0)) := TDef.toDef1 hCz
    obtain ⟨x1, hx1⟩ := Zn.sepP (P := Cz) hCzdef x0
    -- `e₀ (i x1) = z`
    have hmemx1 : ∀ x, c.M.T.mem x x1 ↔ c.M.T.mem x x0 ∧ Zs.S.mem (e₀ (c.i.toFun n x)) z := hx1
    have hzS : ∀ v, Zs.S.mem v z → ∃ x, e₀ (c.i.toFun n x) = v := by
      intro v hv
      obtain ⟨q', rfl⟩ := he₀_surj v (hS₀_trans _ hw v (hzw v hv))
      obtain ⟨x, rfl⟩ := (c.i.bijective n).2 q'
      exact ⟨x, rfl⟩
    have heq : e₀ (c.i.toFun n x1) = z := by
      apply Zs.ax.ext
      intro v
      constructor
      · intro hv
        obtain ⟨q', rfl⟩ := he₀_surj v (hS₀_trans _ (he₀_mem _) v hv)
        obtain ⟨x, rfl⟩ := (c.i.bijective n).2 q'
        have hP := (he₀_mem_iff _ _).1 hv
        have hM := (c.i.mem_iff n x x1).1 hP
        exact ((hmemx1 x).1 hM).2
      · intro hv
        obtain ⟨x, rfl⟩ := hzS v hv
        have hvw : Zs.S.mem (e₀ (c.i.toFun n x)) (e₀ q) := hzw _ hv
        rw [← hx0] at hvw
        have hM : c.M.T.mem x x0 := (c.i.mem_iff n x x0).1 ((he₀_mem_iff _ _).1 hvw)
        have hx1' : c.M.T.mem x x1 := (hmemx1 x).2 ⟨hM, hv⟩
        exact (he₀_mem_iff _ _).2 ((c.i.mem_iff n x x1).2 hx1')
    rw [← heq]
    exact he₀_mem _
  refine ⟨⟨S₀, e₀, he₀_mem, he₀_surj, he₀_inj, he₀_mem_iff, ?_, ?_, he₀_def⟩⟩
  · exact fun w hw v hv => hS₀_trans w hw v hv
  · exact fun w z hw hzw => hsuper w z hw hzw

end Config

end SolidLean.Solid
