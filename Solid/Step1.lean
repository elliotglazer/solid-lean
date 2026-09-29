module

public import Solid.Config
public import Solid.Level

/-!
# Step 1: internal presentation and well-foundedness

For sort `n` of `P`, presented by the class `J.dom n` of sort `a := J.a n`
of `N` modulo `J.eqv n`, with membership `J.memC n`: inside sort `a + 1` of
`N`, where sort `a` is a set, the domain becomes a set `D`, and membership
and equivalence become set relations `R`, `E` on `D` (`exists_D`,
`exists_R`, `exists_E`).

Well-foundedness of `R` in the sense of `N` (`wf_R`) is by pullback along
`i`: a nonempty subset `X` of `D` determines an `M`-definable class of sort
`n` of `M` (Composite definability), whose image in sort `n+1` of `M` is a
nonempty definable subclass of the set `V(κ n)`; its foundation-minimal
element, sent back through `i`, is `R`-minimal in `X`.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical ClassSystem

namespace Config

variable (c : Config.{u}) (n : ℕ)

/-- The domain of sort `n` of `P`, as a set of sort `J.a n + 1` of `N`. -/
theorem exists_D : ∃ D : c.N.T.U (c.J.a n + 1), ∀ y, c.N.T.mem y D ↔
    ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n := by
  let Zs := c.hN.sortModel (c.J.a n + 1)
  let P : c.N.T.U (c.J.a n + 1) → Prop := fun y => ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n
  have hdef : Zs.𝒞.Def 1 (fun t => P (t 0)) := by
    apply TDef.toDef1
    have hdom : c.N.𝒟.TDef 1 (fun t => ∃ u : c.N.T.U (c.J.a n), t 0 = c.N.T.inj u ∧
      u ∈ c.J.dom n) := c.J.dom_def n
    refine TDef.congr ?_ (TDef.exists_ (c.J.a n) (TDef.and_ (TDef.j_sort (c.J.a n) 1 0)
      (TDef.reindex (fun _ : Fin 1 => (1 : Fin 2)) hdom)))
    intro t
    simp only [Function.comp_apply, Fin.snoc_one_zero, Fin.snoc_one_one]
    constructor
    · rintro ⟨u, ⟨u', hu', ht⟩, u'', hu'', hd⟩
      have e1 : u' = u := MemTower.inj_injective' _ hu'.symm
      have e2 : u'' = u := MemTower.inj_injective' _ hu''.symm
      rw [e1] at ht
      rw [e2] at hd
      exact ⟨c.N.T.j (c.J.a n) u, ht, u, rfl, hd⟩
    · rintro ⟨y, hy, u, rfl, hd⟩
      exact ⟨u, ⟨u, rfl, hy⟩, u, rfl, hd⟩
  obtain ⟨D, hD⟩ := Zs.sepP (P := P) hdef (c.hN.imageSet (c.J.a n))
  refine ⟨D, fun y => ?_⟩
  show Zs.S.mem y D ↔ _
  rw [hD y]
  constructor
  · exact fun h => h.2
  · rintro ⟨u, rfl, hd⟩
    exact ⟨(c.hN.mem_imageSet_iff _ _).2 ⟨u, rfl⟩, u, rfl, hd⟩

/-- A definable binary relation on the representatives, pushed through `j`
into a set of pairs over `D`. -/
theorem exists_pairSet (D : c.N.T.U (c.J.a n + 1))
    (hD : ∀ y, c.N.T.mem y D ↔ ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n)
    (B : c.N.T.U (c.J.a n) → c.N.T.U (c.J.a n) → Prop)
    (hB : c.N.DefOn (c.J.a n) 2 {t | B (t 0) (t 1)}) :
    ∃ R : c.N.T.U (c.J.a n + 1), ∀ y x, (c.N.T.sortStr (c.J.a n + 1)).FunApp R y x ↔
      ∃ u u', y = c.N.T.j (c.J.a n) u ∧ x = c.N.T.j (c.J.a n) u' ∧
        u ∈ c.J.dom n ∧ u' ∈ c.J.dom n ∧ B u u' := by
  let a := c.J.a n
  let s := a + 1
  let Zs := c.hN.sortModel s
  obtain ⟨r, hr⟩ := Zs.exists_prod D D
  let P : c.N.T.U s → Prop := fun p => ∃ u u',
    (c.N.T.sortStr s).IsOrdPair (c.N.T.j a u) (c.N.T.j a u') p ∧ B u u'
  have hB' : (c.N.𝒟.sortSystem a).Def 2 (fun t => B (t 0) (t 1)) := hB
  have hdef : Zs.𝒞.Def 1 (fun t => P (t 0)) := by
    apply TDef.toDef1
    -- positions: 0 p, 1 u, 2 u', 3 y, 4 y'
    refine TDef.congr ?_ (TDef.exists_ a (TDef.exists_ a (TDef.exists_ s (TDef.exists_ s
      (TDef.and_ (TDef.j_sort a 1 3) (TDef.and_ (TDef.j_sort a 2 4)
        (TDef.and_ (TDef.lift3 s (SetClassSystem.Def.isOrdPair 0 1 2) 3 4 0)
          (TDef.lift2 a hB' 1 2))))))))
    intro t
    simp only [Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one,
      Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two,
      Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two,
      Fin.snoc_four_three, Fin.snoc_four_four]
    constructor
    · rintro ⟨u, u', y, y', ⟨u₁, hu₁, hy₁⟩, ⟨u₂, hu₂, hy₂⟩, ⟨y₃, y₄, p, hy₃, hy₄, hp, hpair⟩,
        ⟨u₅, u₆, hu₅, hu₆, hBu⟩⟩
      have e1 : u₁ = u := MemTower.inj_injective' _ hu₁.symm
      have e2 : u₂ = u' := MemTower.inj_injective' _ hu₂.symm
      have e3 : y₃ = y := MemTower.inj_injective' _ hy₃.symm
      have e4 : y₄ = y' := MemTower.inj_injective' _ hy₄.symm
      have e5 : u₅ = u := MemTower.inj_injective' _ hu₅.symm
      have e6 : u₆ = u' := MemTower.inj_injective' _ hu₆.symm
      rw [e1] at hy₁; rw [e2] at hy₂; rw [e3, e4] at hpair; rw [e5, e6] at hBu
      have ey : y = c.N.T.j a u := MemTower.inj_injective' _ hy₁
      have ey' : y' = c.N.T.j a u' := MemTower.inj_injective' _ hy₂
      rw [ey, ey'] at hpair
      exact ⟨p, hp, u, u', hpair, hBu⟩
    · rintro ⟨p, hp, u, u', hpair, hBu⟩
      exact ⟨u, u', c.N.T.j a u, c.N.T.j a u', ⟨u, rfl, rfl⟩, ⟨u', rfl, rfl⟩,
        ⟨_, _, p, rfl, rfl, hp, hpair⟩, ⟨u, u', rfl, rfl, hBu⟩⟩
  obtain ⟨R, hR⟩ := Zs.sepP (P := P) hdef r
  refine ⟨R, fun y x => ?_⟩
  constructor
  · rintro ⟨p, hp, hpair⟩
    obtain ⟨hpr, u, u', hpair', hBu⟩ := (hR p).1 hp
    obtain ⟨a', b', ha', hb', hpair''⟩ := (hr p).1 hpr
    obtain ⟨rfl, rfl⟩ := Zs.ordPair_inj hpair hpair'
    obtain ⟨rfl, rfl⟩ := Zs.ordPair_inj hpair'' hpair'
    obtain ⟨u₁, hu₁, hd₁⟩ := (hD _).1 ha'
    obtain ⟨u₂, hu₂, hd₂⟩ := (hD _).1 hb'
    rw [c.hN.j_injective a _ _ hu₁] at hd₁
    rw [c.hN.j_injective a _ _ hu₂] at hd₂
    exact ⟨u, u', rfl, rfl, hd₁, hd₂, hBu⟩
  · rintro ⟨u, u', rfl, rfl, hd, hd', hBu⟩
    obtain ⟨p, hp⟩ := Zs.exists_ordPair (c.N.T.j a u) (c.N.T.j a u')
    refine ⟨p, (hR p).2 ⟨(hr p).2 ⟨_, _, (hD _).2 ⟨u, rfl, hd⟩, (hD _).2 ⟨u', rfl, hd'⟩, hp⟩,
      u, u', hp, hBu⟩, hp⟩

/-- Membership of sort `n` of `P` as a set relation on `D`. -/
theorem exists_R (D : c.N.T.U (c.J.a n + 1))
    (hD : ∀ y, c.N.T.mem y D ↔ ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n) :
    ∃ R : c.N.T.U (c.J.a n + 1), ∀ y x, (c.N.T.sortStr (c.J.a n + 1)).FunApp R y x ↔
      ∃ u u', y = c.N.T.j (c.J.a n) u ∧ x = c.N.T.j (c.J.a n) u' ∧
        u ∈ c.J.dom n ∧ u' ∈ c.J.dom n ∧ c.J.memC n u u' :=
  c.exists_pairSet n D hD (c.J.memC n) (c.J.memC_def n)

/-- The equivalence of sort `n` of `P` as a set relation on `D`. -/
theorem exists_E (D : c.N.T.U (c.J.a n + 1))
    (hD : ∀ y, c.N.T.mem y D ↔ ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n) :
    ∃ E : c.N.T.U (c.J.a n + 1), ∀ y x, (c.N.T.sortStr (c.J.a n + 1)).FunApp E y x ↔
      ∃ u u', y = c.N.T.j (c.J.a n) u ∧ x = c.N.T.j (c.J.a n) u' ∧
        u ∈ c.J.dom n ∧ u' ∈ c.J.dom n ∧ c.J.eqv n u u' :=
  c.exists_pairSet n D hD (c.J.eqv n) (c.J.eqv_def n)

/-- **Step 1, well-foundedness by pullback.** -/
theorem wf_R (D R : c.N.T.U (c.J.a n + 1))
    (hD : ∀ y, c.N.T.mem y D ↔ ∃ u, c.N.T.j (c.J.a n) u = y ∧ u ∈ c.J.dom n)
    (hR : ∀ y x, (c.N.T.sortStr (c.J.a n + 1)).FunApp R y x ↔
      ∃ u u', y = c.N.T.j (c.J.a n) u ∧ x = c.N.T.j (c.J.a n) u' ∧
        u ∈ c.J.dom n ∧ u' ∈ c.J.dom n ∧ c.J.memC n u u') :
    (c.N.T.sortStr (c.J.a n + 1)).WellFoundedOn D R := by
  intro X hXD hXne
  let a := c.J.a n
  let s := a + 1
  -- the class of `M` pulled back along `i`
  let CX : c.M.T.U n → Prop := fun x => ∃ u, c.J.pres.rep n u = some (c.i.toFun n x) ∧
    c.N.T.mem (c.N.T.j a u) X
  have hQ : ({t | ∃ (u : c.N.T.U a) (y : c.N.T.U s), t 0 = c.N.T.inj u ∧ t 1 = c.N.T.inj y ∧
      c.N.T.mem (c.N.T.j a u) X} : c.N.T.Rel 2) ∈ c.N.𝒟.D 2 := by
    refine TDef.congr ?_ (TDef.and_ (TDef.sort 1 s) (TDef.exists_ s (TDef.withParam
      (c.N.T.inj X) (TDef.and_ (TDef.j_sort a 0 2) (TDef.mem_sort s 2 3)))))
    intro t
    simp only [Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero,
      Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three]
    constructor
    · rintro ⟨hs, y', ⟨u, hu, hy'⟩, y'', X', hy'', hX', hmem⟩
      have e1 : y'' = y' := MemTower.inj_injective' _ hy''.symm
      have e2 : X' = X := MemTower.inj_injective' _ hX'.symm
      have e3 : y' = c.N.T.j a u := MemTower.inj_injective' _ hy'
      rw [e1, e2, e3] at hmem
      exact ⟨u, c.N.T.toSort (t 1) hs, hu, (c.N.T.inj_toSort _ _).symm, hmem⟩
    · rintro ⟨u, y, hu, hy, hmem⟩
      refine ⟨by rw [hy], c.N.T.j a u, ⟨u, hu, rfl⟩, c.N.T.j a u, X, rfl, rfl, hmem⟩
  have hCX : c.M.𝒟.TDef 1 (fun t => ∃ x : c.M.T.U n, t 0 = c.M.T.inj x ∧ CX x) := by
    refine TDef.congr ?_ (TDef.exists_ (c.I.a s) (c.composite_def n s hQ))
    intro t
    simp only [Fin.snoc_one_zero, Fin.snoc_one_one]
    constructor
    · rintro ⟨r, x, r', hx, hr', u, y, hJu, hIr, hQ'⟩
      obtain ⟨u', y', hu', hy', hmem⟩ := hQ'
      have e1 : u' = u := MemTower.inj_injective' _ hu'.symm
      rw [e1] at hmem
      exact ⟨x, hx, u, hJu, hmem⟩
    · rintro ⟨x, hx, u, hJu, hmem⟩
      obtain ⟨r, hr⟩ := c.I.pres.surj s X
      exact ⟨r, x, r, hx, rfl, u, X, hJu, hr, u, X, rfl, rfl, hmem⟩
  -- its image in sort `n + 1` of `M`
  let Zm := c.hM.sortModel (n + 1)
  let CX' : c.M.T.U (n + 1) → Prop := fun y => ∃ x, c.M.T.j n x = y ∧ CX x
  have hCX' : Zm.𝒞.Def 1 (fun t => CX' (t 0)) := by
    apply TDef.toDef1
    refine TDef.congr ?_ (TDef.exists_ n (TDef.and_ (TDef.j_sort n 1 0)
      (TDef.reindex (fun _ : Fin 1 => (1 : Fin 2)) hCX)))
    intro t
    simp only [Function.comp_apply, Fin.snoc_one_zero, Fin.snoc_one_one]
    constructor
    · rintro ⟨x, ⟨x', hx', ht⟩, x'', hx'', hC⟩
      have e1 : x' = x := MemTower.inj_injective' _ hx'.symm
      have e2 : x'' = x := MemTower.inj_injective' _ hx''.symm
      rw [e1] at ht; rw [e2] at hC
      exact ⟨c.M.T.j n x, ht, x, rfl, hC⟩
    · rintro ⟨y, hy, x, rfl, hC⟩
      exact ⟨x, ⟨x, rfl, hy⟩, x, rfl, hC⟩
  -- nonempty: a member of `X` comes from a representative
  obtain ⟨y0, hy0⟩ := hXne
  obtain ⟨u0, rfl, hu0d⟩ := (hD y0).1 (hXD y0 hy0)
  obtain ⟨x0, hx0⟩ := (c.i.bijective n).2 (c.J.cls ⟨u0, hu0d⟩)
  have hCX0 : CX x0 := ⟨u0, by rw [hx0]; exact c.J.pres_rep_cls ⟨u0, hu0d⟩, hy0⟩
  obtain ⟨y1, ⟨x1, rfl, u1, hJu1, hmem1⟩, hmin⟩ := Zm.class_foundationP hCX' (c.hM.imageSet n)
    (fun y ⟨x, hx, _⟩ => (c.hM.mem_imageSet_iff n y).2 ⟨x, hx⟩) ⟨_, x0, rfl, hCX0⟩
  refine ⟨c.N.T.j a u1, hmem1, fun y hy hRy => ?_⟩
  obtain ⟨u, u', rfl, hu', hud, hu'd, hmemC⟩ := (hR y _).1 hRy
  have e1 : u' = u1 := c.hN.j_injective a _ _ hu'.symm
  rw [e1] at hmemC
  obtain ⟨x, hx⟩ := (c.i.bijective n).2 (c.J.cls ⟨u, hud⟩)
  obtain ⟨hu1d, hcls1⟩ := (c.J.pres_rep_eq_some_iff u1 _).1 hJu1
  -- `i x ∈ i x1` in `P`, hence `x ∈ x1` in `M`
  have hPmem : c.J.model.mem (c.i.toFun n x) (c.i.toFun n x1) := by
    rw [hx, ← hcls1]
    exact hmemC
  have hMmem : c.M.T.mem x x1 := (c.i.mem_iff n x x1).1 hPmem
  apply hmin (c.M.T.j n x) ((c.hM.j_mem_iff n x x1).2 hMmem)
  exact ⟨x, rfl, u, by rw [hx]; exact c.J.pres_rep_cls ⟨u, hud⟩, hy⟩

end Config

end SolidLean.Solid
