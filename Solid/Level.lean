module

public import Solid.Collapse

/-!
# Collapses of a single sort, their lifts, and Step 2

A `LevelCollapse` is what Steps 1 and 3 produce for one sort `n` of the
presented tower, inside one sort `s` of the ambient tower.  Such data lifts
along the transitions of the ambient tower (`LevelCollapse.lift`).

Step 2 (`LevelCollapse.transition`): two collapses of sort `n`, the
transition of sort `n+1`'s collapse and the lift of sort `n`'s, agree, by
foundation applied to the definable class where they differ.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical ClassSystem

/-- A collapse of sort `n` of `PC` inside sort `s` of `N`. -/
structure LevelCollapse (N PC : TowerWithClasses.{u}) (p : Presentation N.T.U PC.T.U) (n s : ℕ) where
  S : N.T.U s
  e : PC.T.U n → N.T.U s
  e_mem : ∀ x, N.T.mem (e x) S
  e_surj : ∀ y, N.T.mem y S → ∃ x, e x = y
  e_injective : Function.Injective e
  e_mem_iff : ∀ x y, N.T.mem (e x) (e y) ↔ PC.T.mem x y
  S_trans : (N.T.sortStr s).Transitive S
  S_supertrans : ∀ y z, N.T.mem y S → (N.T.sortStr s).Subset z y → N.T.mem z S
  e_definable : PGraph p e ∈ N.𝒟.D 2

namespace LevelCollapse

variable {N PC : TowerWithClasses.{u}} {p : Presentation N.T.U PC.T.U} {n s : ℕ}
  (hN : IsTowerModel N)

/-- Lifting a collapse to a higher sort. -/
noncomputable def lift (L : LevelCollapse N PC p n s) {s' : ℕ} (h : s ≤ s') :
    LevelCollapse N PC p n s' where
  S := N.T.liftLE h L.S
  e := fun x => N.T.liftLE h (L.e x)
  e_mem := fun x => (hN.liftLE_mem_iff h _ _).2 (L.e_mem x)
  e_surj := by
    intro y hy
    obtain ⟨y₀, rfl⟩ := (hN.liftEmb h).trans _ y hy
    obtain ⟨x, rfl⟩ := L.e_surj y₀ ((hN.liftLE_mem_iff h _ _).1 hy)
    exact ⟨x, rfl⟩
  e_injective := fun x y hxy => L.e_injective (hN.liftLE_injective h hxy)
  e_mem_iff := fun x y => by rw [hN.liftLE_mem_iff, L.e_mem_iff]
  S_trans := ((hN.liftEmb h).transitive_iff L.S).2 L.S_trans
  S_supertrans := by
    intro y z hy hz
    obtain ⟨y₀, rfl⟩ := (hN.liftEmb h).trans _ y hy
    obtain ⟨z₀, rfl⟩ := (hN.liftEmb h).supertrans y₀ z hz
    have hz₀ : (N.T.sortStr s).Subset z₀ y₀ := ((hN.liftEmb h).subset_iff z₀ y₀).1 hz
    exact (hN.liftLE_mem_iff h _ _).2
      (L.S_supertrans y₀ z₀ ((hN.liftLE_mem_iff h _ _).1 hy) hz₀)
  e_definable := PGraph.lift N.𝒟 p h L.e_definable

@[simp] theorem lift_e (L : LevelCollapse N PC p n s) {s' : ℕ} (h : s ≤ s') (x : PC.T.U n) :
    (L.lift hN h).e x = N.T.liftLE h (L.e x) := rfl

@[simp] theorem lift_S (L : LevelCollapse N PC p n s) {s' : ℕ} (h : s ≤ s') :
    (L.lift hN h).S = N.T.liftLE h L.S := rfl

/-- The collapse as an inner embedding (given ZFC on both sides). -/
noncomputable def emb (hP : IsTowerModel PC) (L : LevelCollapse N PC p n s) :
    InnerEmb (hP.sortModel n) (hN.sortModel s) where
  φ := L.e
  injective := L.e_injective
  mem_iff := L.e_mem_iff
  trans := fun x z hz => L.e_surj z (L.S_trans _ (L.e_mem x) z hz)
  supertrans := fun x z hz => L.e_surj z (L.S_supertrans _ z (L.e_mem x) hz)

end LevelCollapse

/-! ### Step 2 -/

namespace Interp

variable {N : TowerWithClasses.{u}} (J : Interp N) (hN : IsTowerModel N)
  {𝒬 : ClassSystem J.model} (hP : IsTowerModel ⟨J.model, 𝒬⟩)

include hN hP in
/-- **Step 2.**  The lift of the collapse of sort `n` and the collapse of sort
`n+1` composed with the transition agree. -/
theorem levelCollapse_transition {n s s' : ℕ} (h : s ≤ s')
    (L : LevelCollapse N ⟨J.model, 𝒬⟩ J.pres n s)
    (L' : LevelCollapse N ⟨J.model, 𝒬⟩ J.pres (n + 1) s')
    (x : J.model.U n) : N.T.liftLE h (L.e x) = L'.e (J.model.j n x) := by
  let Z := hN.sortModel s'
  let f : J.model.U n → N.T.U s' := fun q => L'.e (J.model.j n q)
  let g : J.model.U n → N.T.U s' := fun q => N.T.liftLE h (L.e q)
  have hfdef : PGraph J.pres f ∈ N.𝒟.D 2 := J.PGraph_comp_j L'.e_definable
  have hgdef : PGraph J.pres g ∈ N.𝒟.D 2 := PGraph.lift N.𝒟 J.pres h L.e_definable
  -- both are membership isomorphisms onto transitive sets
  have hf_mem : ∀ q q', N.T.mem (f q) (f q') ↔ J.model.mem q q' := by
    intro q q'
    show N.T.mem (L'.e _) (L'.e _) ↔ _
    rw [L'.e_mem_iff]
    exact hP.j_mem_iff n q q'
  have hg_mem : ∀ q q', N.T.mem (g q) (g q') ↔ J.model.mem q q' := by
    intro q q'
    show N.T.mem (N.T.liftLE h _) (N.T.liftLE h _) ↔ _
    rw [hN.liftLE_mem_iff, L.e_mem_iff]
  have hf_trans : ∀ q w, N.T.mem w (f q) → ∃ q', f q' = w := by
    intro q w hw
    obtain ⟨y, rfl⟩ := (L'.emb hN hP).trans _ w hw
    have hy : J.model.mem y (J.model.j n q) := (L'.e_mem_iff _ _).1 hw
    have hyv : J.model.mem y (hP.imageSet n) :=
      ZFCModel.IsV.transitive (hP.sortModel (n + 1)) (hP.imageSet_isV n) _
        ((hP.mem_imageSet_iff n _).2 ⟨q, rfl⟩) y hy
    obtain ⟨q', rfl⟩ := (hP.mem_imageSet_iff n y).1 hyv
    exact ⟨q', rfl⟩
  have hg_trans : ∀ q w, N.T.mem w (g q) → ∃ q', g q' = w := by
    intro q w hw
    obtain ⟨y, rfl⟩ := (hN.liftEmb h).trans _ w hw
    obtain ⟨q', rfl⟩ := L.e_surj y (L.S_trans _ (L.e_mem q) y ((hN.liftLE_mem_iff h _ _).1 hw))
    exact ⟨q', rfl⟩
  -- the class where they differ
  let Bad : N.T.U s' → Prop := fun z => ∃ q, f q = z ∧ f q ≠ g q
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    apply TDef.toDef1
    rw [PGraph.tdef_iff] at hfdef hgdef
    refine TDef.congr ?_ (TDef.exists_ (J.pres.a n) (TDef.and_ (TDef.reindex ![1, 0] hfdef)
      (TDef.not_ (TDef.reindex ![1, 0] hgdef))))
    intro t
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.snoc_one_zero, Fin.snoc_one_one]
    constructor
    · rintro ⟨u, ⟨u', q, hu', ht, hq⟩, hng⟩
      refine ⟨f q, ht, q, rfl, fun heq => hng ⟨u', q, hu', ?_, hq⟩⟩
      rw [ht, heq]
    · rintro ⟨z, hz, q, rfl, hne⟩
      obtain ⟨u, hu⟩ := J.pres.surj n q
      refine ⟨u, ⟨u, q, rfl, hz, hu⟩, ?_⟩
      rintro ⟨u', q', hu', ht, hq'⟩
      have : u' = u := MemTower.inj_injective' _ hu'.symm
      subst this
      have : q' = q := Option.some_injective _ (hq'.symm.trans hu)
      subst this
      exact hne (MemTower.inj_injective' _ (hz.symm.trans ht))
  by_contra hne
  -- bounding set: the image of `f`
  have hbound : ∀ z, Bad z → N.T.mem z (L'.e (hP.imageSet n)) := by
    rintro z ⟨q, rfl, -⟩
    show N.T.mem (L'.e _) (L'.e _)
    rw [L'.e_mem_iff]
    exact (hP.mem_imageSet_iff n _).2 ⟨q, rfl⟩
  obtain ⟨z0, ⟨q0, rfl, hne0⟩, hmin⟩ := Z.class_foundationP hdef _ hbound
    ⟨_, x, rfl, fun heq => hne heq.symm⟩
  apply hne0
  apply Z.ax.ext
  intro w
  show N.T.mem w (f q0) ↔ N.T.mem w (g q0)
  constructor
  · intro hw
    obtain ⟨q', rfl⟩ := hf_trans q0 w hw
    have hq' : f q' = g q' := by
      by_contra hne'
      exact hmin _ hw ⟨q', rfl, hne'⟩
    rw [hq', hg_mem]
    exact (hf_mem q' q0).1 hw
  · intro hw
    obtain ⟨q', rfl⟩ := hg_trans q0 w hw
    have hmem : J.model.mem q' q0 := (hg_mem q' q0).1 hw
    have hw' : N.T.mem (f q') (f q0) := (hf_mem q' q0).2 hmem
    have hq' : f q' = g q' := by
      by_contra hne'
      exact hmin _ hw' ⟨q', rfl, hne'⟩
    rw [← hq']
    exact hw'

end Interp

end SolidLean.Solid
