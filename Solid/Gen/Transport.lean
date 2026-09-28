import Solid.Lift
import Solid.Interpretation

/-!
# Transport of class systems and of the axioms of `H` along tower isomorphisms

A tower isomorphism `e : T ≅ T'` carries a class system on `T` to one on
`T'` (`ClassSystem.map`), and a model of `H` to a model of `H`
(`IsTowerModel.transport`).  This is what identifies the tower obtained by
interpreting `D(N)` inside `D(M)` with `D(N)` itself.
-/

universe u

namespace SolidLean.Solid

open Classical

namespace TowerIso

variable {T T' : MemTower.{u}} (e : TowerIso T T')

/-- The action on the union of sorts. -/
def mapEl (z : T.El) : T'.El := ⟨z.1, e.toFun z.1 z.2⟩

@[simp] theorem mapEl_inj {n : ℕ} (x : T.U n) : e.mapEl (T.inj x) = T'.inj (e.toFun n x) := rfl

@[simp] theorem mapEl_fst (z : T.El) : (e.mapEl z).1 = z.1 := rfl

theorem mapEl_injective : Function.Injective e.mapEl := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hnm : n = m := congrArg Sigma.fst h
  subst hnm
  have := (e.bijective n).1 (Sorted.inj_injective T'.U h)
  exact Sigma.ext rfl (heq_of_eq this)

theorem mapEl_surjective : Function.Surjective e.mapEl := by
  rintro ⟨n, y⟩
  obtain ⟨x, rfl⟩ := (e.bijective n).2 y
  exact ⟨⟨n, x⟩, rfl⟩

/-- The inverse isomorphism. -/
noncomputable def symm : TowerIso T' T where
  toFun n := Function.surjInv (e.bijective n).2
  bijective n := by
    have hinv : Function.LeftInverse (e.toFun n) (Function.surjInv (e.bijective n).2) :=
      Function.surjInv_eq (e.bijective n).2
    constructor
    · intro x y hxy
      have := congrArg (e.toFun n) hxy
      rw [hinv, hinv] at this
      exact this
    · intro x
      refine ⟨e.toFun n x, ?_⟩
      apply (e.bijective n).1
      rw [hinv]
  mem_iff n x y := by
    have hinv : Function.LeftInverse (e.toFun n) (Function.surjInv (e.bijective n).2) :=
      Function.surjInv_eq (e.bijective n).2
    rw [← e.mem_iff, hinv, hinv]
  j_comm n x := by
    have hinv : ∀ m, Function.LeftInverse (e.toFun m) (Function.surjInv (e.bijective m).2) :=
      fun m => Function.surjInv_eq (e.bijective m).2
    apply (e.bijective (n + 1)).1
    rw [hinv, e.j_comm, hinv]
  κ_comm n := by
    have hinv : ∀ m, Function.LeftInverse (e.toFun m) (Function.surjInv (e.bijective m).2) :=
      fun m => Function.surjInv_eq (e.bijective m).2
    apply (e.bijective (n + 1)).1
    rw [hinv, e.κ_comm]

/-- Composition of tower isomorphisms. -/
def trans {T'' : MemTower.{u}} (e' : TowerIso T' T'') : TowerIso T T'' where
  toFun n x := e'.toFun n (e.toFun n x)
  bijective n := (e'.bijective n).comp (e.bijective n)
  mem_iff n x y := (e'.mem_iff n _ _).trans (e.mem_iff n x y)
  j_comm n x := by rw [e.j_comm, e'.j_comm]
  κ_comm n := by rw [e.κ_comm, e'.κ_comm]

theorem toFun_symm {n : ℕ} (y : T'.U n) : e.toFun n (e.symm.toFun n y) = y :=
  Function.surjInv_eq (e.bijective n).2 y

theorem symm_toFun {n : ℕ} (x : T.U n) : e.symm.toFun n (e.toFun n x) = x :=
  (e.bijective n).1 (e.toFun_symm (e.toFun n x))

theorem mapEl_symm (z : T'.El) : e.mapEl (e.symm.mapEl z) = z := by
  obtain ⟨n, y⟩ := z
  show T'.inj (e.toFun n (e.symm.toFun n y)) = T'.inj y
  rw [e.toFun_symm]

theorem symm_mapEl (z : T.El) : e.symm.mapEl (e.mapEl z) = z := by
  obtain ⟨n, x⟩ := z
  show T.inj (e.symm.toFun n (e.toFun n x)) = T.inj x
  rw [e.symm_toFun]

/-- The preimage of a relation on `T'`. -/
def pullRel {k : ℕ} (C' : T'.Rel k) : T.Rel k := {t | (fun i => e.mapEl (t i)) ∈ C'}

/-- The image of a relation on `T`. -/
def pushRel {k : ℕ} (C : T.Rel k) : T'.Rel k := {t | (fun i => e.symm.mapEl (t i)) ∈ C}

theorem pullRel_pushRel {k : ℕ} (C : T.Rel k) : e.pullRel (e.pushRel C) = C := by
  ext t
  show (fun i => e.symm.mapEl (e.mapEl (t i))) ∈ C ↔ t ∈ C
  simp only [symm_mapEl]

theorem pushRel_pullRel {k : ℕ} (C' : T'.Rel k) : e.pushRel (e.pullRel C') = C' := by
  ext t
  show (fun i => e.mapEl (e.symm.mapEl (t i))) ∈ C' ↔ t ∈ C'
  simp only [mapEl_symm]

theorem pullRel_memRel (n : ℕ) : e.pullRel (T'.memRel n) = T.memRel n := by
  ext t
  show (∃ x y : T'.U n, e.mapEl (t 0) = T'.inj x ∧ e.mapEl (t 1) = T'.inj y ∧ T'.mem x y) ↔ _
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    refine ⟨e.symm.toFun n x, e.symm.toFun n y, ?_, ?_, ?_⟩
    · rw [← e.symm_mapEl (t 0), hx]; rfl
    · rw [← e.symm_mapEl (t 1), hy]; rfl
    · rw [← e.mem_iff, e.toFun_symm, e.toFun_symm]; exact hxy
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨e.toFun n x, e.toFun n y, by rw [hx]; rfl, by rw [hy]; rfl, (e.mem_iff n x y).2 hxy⟩

theorem pullRel_jRel (n : ℕ) : e.pullRel (T'.jRel n) = T.jRel n := by
  ext t
  show (∃ x : T'.U n, e.mapEl (t 0) = T'.inj x ∧ e.mapEl (t 1) = T'.inj (T'.j n x)) ↔ _
  constructor
  · rintro ⟨x, hx, hy⟩
    refine ⟨e.symm.toFun n x, ?_, ?_⟩
    · rw [← e.symm_mapEl (t 0), hx]; rfl
    · rw [← e.symm_mapEl (t 1), hy]
      show T.inj (e.symm.toFun (n + 1) (T'.j n x)) = T.inj (T.j n (e.symm.toFun n x))
      rw [e.symm.j_comm]
  · rintro ⟨x, hx, hy⟩
    refine ⟨e.toFun n x, by rw [hx]; rfl, ?_⟩
    rw [hy]
    show T'.inj (e.toFun (n + 1) (T.j n x)) = _
    rw [e.j_comm]

theorem pullRel_kappaRel (n : ℕ) : e.pullRel (T'.kappaRel n) = T.kappaRel n := by
  ext t
  show e.mapEl (t 0) = T'.inj (T'.κ n) ↔ t 0 = T.inj (T.κ n)
  constructor
  · intro h
    rw [← e.symm_mapEl (t 0), h]
    show T.inj (e.symm.toFun (n + 1) (T'.κ n)) = _
    rw [e.symm.κ_comm]
  · intro h
    rw [h]
    show T'.inj (e.toFun (n + 1) (T.κ n)) = _
    rw [e.κ_comm]

end TowerIso

namespace ClassSystem

variable {T T' : MemTower.{u}} (e : TowerIso T T') (𝒟 : ClassSystem T)

/-- The class system carried along an isomorphism: relations whose pullback
is admissible. -/
def map : ClassSystem T' where
  D k := {C' | e.pullRel C' ∈ 𝒟.D k}
  eq_mem := by
    show e.pullRel _ ∈ 𝒟.D 2
    have : e.pullRel (T'.eqRel) = T.eqRel := by
      ext t
      show e.mapEl (t 0) = e.mapEl (t 1) ↔ t 0 = t 1
      exact ⟨fun h => e.mapEl_injective h, fun h => by rw [h]⟩
    rw [this]; exact 𝒟.eq_mem
  sort_mem n := by
    show e.pullRel _ ∈ 𝒟.D 1
    have : e.pullRel (T'.sortRel n) = T.sortRel n := by
      ext t; exact Iff.rfl
    rw [this]; exact 𝒟.sort_mem n
  param_mem p := by
    show e.pullRel _ ∈ 𝒟.D 1
    have : e.pullRel (T'.paramRel p) = T.paramRel (e.symm.mapEl p) := by
      ext t
      show e.mapEl (t 0) = p ↔ t 0 = e.symm.mapEl p
      constructor
      · rintro rfl; rw [e.symm_mapEl]
      · intro h; rw [h, e.mapEl_symm]
    rw [this]; exact 𝒟.param_mem _
  univ_mem k := by
    show e.pullRel _ ∈ 𝒟.D k
    have : e.pullRel (Set.univ : T'.Rel k) = Set.univ := by ext t; exact Iff.rfl
    rw [this]; exact 𝒟.univ_mem k
  inter_mem := by
    intro k C C' hC hC'
    show e.pullRel _ ∈ 𝒟.D k
    have : e.pullRel (C ∩ C') = e.pullRel C ∩ e.pullRel C' := by ext t; exact Iff.rfl
    rw [this]; exact 𝒟.inter_mem hC hC'
  compl_mem := by
    intro k C hC
    show e.pullRel _ ∈ 𝒟.D k
    have : e.pullRel Cᶜ = (e.pullRel C)ᶜ := by ext t; exact Iff.rfl
    rw [this]; exact 𝒟.compl_mem hC
  reindex_mem := by
    intro k l f C hC
    show e.pullRel _ ∈ 𝒟.D l
    have : e.pullRel (T'.reindex f C) = T.reindex f (e.pullRel C) := by ext t; exact Iff.rfl
    rw [this]; exact 𝒟.reindex_mem f hC
  exists_mem := by
    intro n k C hC
    show e.pullRel _ ∈ 𝒟.D k
    have : e.pullRel (T'.exists_ n C) = T.exists_ n (e.pullRel C) := by
      ext t
      show (∃ x : T'.El, x.1 = n ∧ Fin.snoc (α := fun _ => T'.El) (fun i => e.mapEl (t i)) x ∈ C) ↔
        ∃ x : T.El, x.1 = n ∧ (fun i => e.mapEl (Fin.snoc (α := fun _ => T.El) t x i)) ∈ C
      constructor
      · rintro ⟨x, hx, hC⟩
        refine ⟨e.symm.mapEl x, hx, ?_⟩
        have : (fun i => e.mapEl (Fin.snoc (α := fun _ => T.El) t (e.symm.mapEl x) i)) =
            Fin.snoc (α := fun _ => T'.El) (fun i => e.mapEl (t i)) x := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Fin.snoc_last, TowerIso.mapEl_symm]
          · simp only [Fin.snoc_castSucc]
        rw [this]; exact hC
      · rintro ⟨x, hx, hC⟩
        refine ⟨e.mapEl x, hx, ?_⟩
        have : (fun i => e.mapEl (Fin.snoc (α := fun _ => T.El) t x i)) =
            Fin.snoc (α := fun _ => T'.El) (fun i => e.mapEl (t i)) (e.mapEl x) := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Fin.snoc_last]
          · simp only [Fin.snoc_castSucc]
        rw [this] at hC; exact hC
    rw [this]; exact 𝒟.exists_mem n hC
  memRel_mem n := by
    show e.pullRel _ ∈ 𝒟.D 2
    rw [e.pullRel_memRel]; exact 𝒟.memRel_mem n
  j_mem n := by
    show e.pullRel _ ∈ 𝒟.D 2
    rw [e.pullRel_jRel]; exact 𝒟.j_mem n
  kappa_mem n := by
    show e.pullRel _ ∈ 𝒟.D 1
    rw [e.pullRel_kappaRel]; exact 𝒟.kappa_mem n

theorem mem_map_iff {k : ℕ} (C' : T'.Rel k) : C' ∈ (𝒟.map e).D k ↔ e.pullRel C' ∈ 𝒟.D k := Iff.rfl

theorem pushRel_mem_map {k : ℕ} {C : T.Rel k} (hC : C ∈ 𝒟.D k) : e.pushRel C ∈ (𝒟.map e).D k := by
  rw [mem_map_iff, e.pullRel_pushRel]; exact hC

end ClassSystem

/-! ### Transport of the axioms -/

/-- Transport of the ZFC axioms along an isomorphism of membership structures
that carries the definable classes backwards. -/
theorem SetAxioms.transfer {S S' : MemStr.{u}} {Def : (k : ℕ) → S.Rel k → Prop}
    {Def' : (k : ℕ) → S'.Rel k → Prop}
    (f : S.X → S'.X) (hsurj : ∀ y, ∃ x, f x = y) (hinj : ∀ {a b}, f a = f b → a = b)
    (hmem : ∀ x y, S'.mem (f x) (f y) ↔ S.mem x y)
    (hDef : ∀ k (C' : S'.Rel k), Def' k C' → Def k {s | (fun i => f (s i)) ∈ C'})
    (h : SetAxioms S Def) : SetAxioms S' Def' := by
  have hsnoc : ∀ {k} (p : Fin k → S.X) (y : S.X),
      (fun i => f (Fin.snoc (α := fun _ => S.X) p y i)) =
        Fin.snoc (α := fun _ => S'.X) (fun i => f (p i)) (f y) := by
    intro k p y
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [Fin.snoc_last]
    · simp only [Fin.snoc_castSucc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ext
    intro x' y' hxy
    obtain ⟨x, rfl⟩ := hsurj x'
    obtain ⟨y, rfl⟩ := hsurj y'
    congr 1
    apply h.ext
    intro z
    rw [← hmem, ← hmem]
    exact hxy (f z)
  · -- empty
    obtain ⟨e0, he0⟩ := h.empty
    refine ⟨f e0, fun z' hz => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj z'
    exact he0 z ((hmem _ _).1 hz)
  · -- pair
    intro a' b'
    obtain ⟨a, rfl⟩ := hsurj a'
    obtain ⟨b, rfl⟩ := hsurj b'
    obtain ⟨p, hp⟩ := h.pair a b
    refine ⟨f p, fun z' => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj z'
    rw [hmem, hp z]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (by rw [h1])
      · exact Or.inr (by rw [h1])
    · rintro (h1 | h1)
      · exact Or.inl (hinj h1)
      · exact Or.inr (hinj h1)
  · -- union
    intro x'
    obtain ⟨x, rfl⟩ := hsurj x'
    obtain ⟨u, hu⟩ := h.union x
    refine ⟨f u, fun z' => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj z'
    rw [hmem, hu z]
    constructor
    · rintro ⟨y, hy, hz⟩
      exact ⟨f y, (hmem _ _).2 hy, (hmem _ _).2 hz⟩
    · rintro ⟨y', hy', hz⟩
      obtain ⟨y, rfl⟩ := hsurj y'
      exact ⟨y, (hmem _ _).1 hy', (hmem _ _).1 hz⟩
  · -- power
    intro x'
    obtain ⟨x, rfl⟩ := hsurj x'
    obtain ⟨p, hp⟩ := h.power x
    refine ⟨f p, fun z' => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj z'
    rw [hmem, hp z]
    constructor
    · intro hsub w' hw'
      obtain ⟨w, rfl⟩ := hsurj w'
      exact (hmem _ _).2 (hsub w ((hmem _ _).1 hw'))
    · intro hsub w hw
      exact (hmem _ _).1 (hsub (f w) ((hmem _ _).2 hw))
  · -- infinity
    obtain ⟨I, ⟨e0, he0, he0I⟩, hI⟩ := h.infinity
    refine ⟨f I, ⟨f e0, fun z' hz => ?_, (hmem _ _).2 he0I⟩, fun x' hx => ?_⟩
    · obtain ⟨z, rfl⟩ := hsurj z'
      exact he0 z ((hmem _ _).1 hz)
    · obtain ⟨x, rfl⟩ := hsurj x'
      obtain ⟨s, hs, hsI⟩ := hI x ((hmem _ _).1 hx)
      refine ⟨f s, fun z' => ?_, (hmem _ _).2 hsI⟩
      obtain ⟨z, rfl⟩ := hsurj z'
      rw [hmem, hmem, hs z]
      constructor
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (by rw [h1])
      · rintro (h1 | h1)
        · exact Or.inl h1
        · exact Or.inr (hinj h1)
  · -- separation
    intro k C' hC' p' x'
    obtain ⟨x, rfl⟩ := hsurj x'
    choose p hp using fun i => hsurj (p' i)
    have hp' : p' = fun i => f (p i) := by funext i; exact (hp i).symm
    subst hp'
    obtain ⟨s, hs⟩ := h.separation _ (hDef _ C' hC') p x
    refine ⟨f s, fun y' => ?_⟩
    obtain ⟨y, rfl⟩ := hsurj y'
    rw [hmem, hs y, hmem]
    refine and_congr Iff.rfl ?_
    show (fun i => f (Fin.snoc (α := fun _ => S.X) p y i)) ∈ C' ↔
      Fin.snoc (α := fun _ => S'.X) (fun i => f (p i)) (f y) ∈ C'
    rw [hsnoc]
  · -- replacement
    intro k C' hC' p' x' hfun
    obtain ⟨x, rfl⟩ := hsurj x'
    choose p hp using fun i => hsurj (p' i)
    have hp' : p' = fun i => f (p i) := by funext i; exact (hp i).symm
    subst hp'
    have key : ∀ y z, Fin.snoc (Fin.snoc p y) z ∈ {s : Fin (k + 2) → S.X | (fun i => f (s i)) ∈ C'} ↔
        Fin.snoc (Fin.snoc (fun i => f (p i)) (f y)) (f z) ∈ C' := by
      intro y z
      show (fun i => f (Fin.snoc (α := fun _ => S.X) (Fin.snoc (α := fun _ => S.X) p y) z i)) ∈ C' ↔ _
      rw [hsnoc, hsnoc]
    have hfun' : ∀ y, S.mem y x →
        ∃! z, Fin.snoc (Fin.snoc p y) z ∈ {s : Fin (k + 2) → S.X | (fun i => f (s i)) ∈ C'} := by
      intro y hy
      obtain ⟨z', hz', huniq⟩ := hfun (f y) ((hmem _ _).2 hy)
      obtain ⟨z, rfl⟩ := hsurj z'
      refine ⟨z, (key y z).2 hz', fun w hw => ?_⟩
      exact hinj (huniq (f w) ((key y w).1 hw))
    obtain ⟨s, hs⟩ := h.replacement _ (hDef _ C' hC') p x hfun'
    refine ⟨f s, fun z' => ?_⟩
    obtain ⟨z, rfl⟩ := hsurj z'
    rw [hmem, hs z]
    constructor
    · rintro ⟨y, hy, hC⟩
      exact ⟨f y, (hmem _ _).2 hy, (key y z).1 hC⟩
    · rintro ⟨y', hy', hC⟩
      obtain ⟨y, rfl⟩ := hsurj y'
      exact ⟨y, (hmem _ _).1 hy', (key y z).2 hC⟩
  · -- foundation
    intro x' hne
    obtain ⟨x, rfl⟩ := hsurj x'
    obtain ⟨z', hz'⟩ := hne
    obtain ⟨z, rfl⟩ := hsurj z'
    obtain ⟨y, hy, hmin⟩ := h.foundation x ⟨z, (hmem _ _).1 hz'⟩
    refine ⟨f y, (hmem _ _).2 hy, fun w' hw hwx => ?_⟩
    obtain ⟨w, rfl⟩ := hsurj w'
    exact hmin w ((hmem _ _).1 hw) ((hmem _ _).1 hwx)
  · -- choice
    intro x' hne
    obtain ⟨x, rfl⟩ := hsurj x'
    have hne' : ∀ y, S.mem y x → S.Nonempty y := by
      intro y hy
      obtain ⟨z', hz'⟩ := hne (f y) ((hmem _ _).2 hy)
      obtain ⟨z, rfl⟩ := hsurj z'
      exact ⟨z, (hmem _ _).1 hz'⟩
    obtain ⟨F, hF, hFv⟩ := h.choice x hne'
    have hsing : ∀ a s, S'.IsSingleton (f a) (f s) ↔ S.IsSingleton a s := by
      intro a s
      constructor
      · intro hs z
        rw [← hmem, hs (f z)]
        exact ⟨fun h1 => hinj h1, fun h1 => by rw [h1]⟩
      · intro hs z'
        obtain ⟨z, rfl⟩ := hsurj z'
        rw [hmem, hs z]
        exact ⟨fun h1 => by rw [h1], fun h1 => hinj h1⟩
    have hpairset : ∀ a b d, S'.IsPairSet (f a) (f b) (f d) ↔ S.IsPairSet a b d := by
      intro a b d
      constructor
      · intro hd z
        rw [← hmem, hd (f z)]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl (hinj h1)
          · exact Or.inr (hinj h1)
        · rintro (h1 | h1)
          · exact Or.inl (by rw [h1])
          · exact Or.inr (by rw [h1])
      · intro hd z'
        obtain ⟨z, rfl⟩ := hsurj z'
        rw [hmem, hd z]
        constructor
        · rintro (h1 | h1)
          · exact Or.inl (by rw [h1])
          · exact Or.inr (by rw [h1])
        · rintro (h1 | h1)
          · exact Or.inl (hinj h1)
          · exact Or.inr (hinj h1)
    have hpair : ∀ a b p, S'.IsOrdPair (f a) (f b) (f p) ↔ S.IsOrdPair a b p := by
      intro a b p
      constructor
      · rintro ⟨s', d', hs', hd', hp'⟩
        obtain ⟨s, rfl⟩ := hsurj s'
        obtain ⟨d, rfl⟩ := hsurj d'
        exact ⟨s, d, (hsing _ _).1 hs', (hpairset _ _ _).1 hd', (hpairset _ _ _).1 hp'⟩
      · rintro ⟨s, d, hs, hd, hp⟩
        exact ⟨f s, f d, (hsing _ _).2 hs, (hpairset _ _ _).2 hd, (hpairset _ _ _).2 hp⟩
    have happ : ∀ a b, S'.FunApp (f F) (f a) (f b) ↔ S.FunApp F a b := by
      intro a b
      constructor
      · rintro ⟨p', hp', hpair'⟩
        obtain ⟨p, rfl⟩ := hsurj p'
        exact ⟨p, (hmem _ _).1 hp', (hpair _ _ _).1 hpair'⟩
      · rintro ⟨p, hp, hpair'⟩
        exact ⟨f p, (hmem _ _).2 hp, (hpair _ _ _).2 hpair'⟩
    refine ⟨f F, ⟨⟨fun p' hp' => ?_, fun a' b' c' hb hc => ?_⟩, fun a' => ?_⟩, fun y' v' hyv => ?_⟩
    · obtain ⟨p, rfl⟩ := hsurj p'
      obtain ⟨a, b, hab⟩ := hF.1.1 p ((hmem _ _).1 hp')
      exact ⟨f a, f b, (hpair _ _ _).2 hab⟩
    · obtain ⟨a, rfl⟩ := hsurj a'
      obtain ⟨b, rfl⟩ := hsurj b'
      obtain ⟨c, rfl⟩ := hsurj c'
      rw [hF.1.2 a b c ((happ _ _).1 hb) ((happ _ _).1 hc)]
    · obtain ⟨a, rfl⟩ := hsurj a'
      rw [hmem]
      constructor
      · rintro ⟨b', hb'⟩
        obtain ⟨b, rfl⟩ := hsurj b'
        exact (hF.2 a).1 ⟨b, (happ _ _).1 hb'⟩
      · intro ha
        obtain ⟨b, hb⟩ := (hF.2 a).2 ha
        exact ⟨f b, (happ _ _).2 hb⟩
    · obtain ⟨y, rfl⟩ := hsurj y'
      obtain ⟨v, rfl⟩ := hsurj v'
      exact (hmem _ _).2 (hFv y v ((happ _ _).1 hyv))

namespace IsTowerModel

variable {T T' : MemTower.{u}} (e : TowerIso T T') {𝒟 : ClassSystem T}

/-- Transport of the ZFC axioms of a sort along the bijection. -/
theorem setAxioms_transport (n : ℕ) (h : SetAxioms (T.sortStr n) (𝒟.DefOn n)) :
    SetAxioms (T'.sortStr n) ((𝒟.map e).DefOn n) := by
  refine SetAxioms.transfer (S := T.sortStr n) (S' := T'.sortStr n) (e.toFun n)
    (fun y => (e.bijective n).2 y) (fun h => (e.bijective n).1 h) (e.mem_iff n) ?_ h
  intro k C' hC'
  show Sorted.liftRel T.U _ ∈ 𝒟.D k
  have : Sorted.liftRel T.U {s : Fin k → T.U n | (fun i => e.toFun n (s i)) ∈ C'} =
      e.pullRel (Sorted.liftRel T'.U C') := by
    ext t
    constructor
    · rintro ⟨s, hs, hC⟩
      refine ⟨fun i => e.toFun n (s i), fun i => ?_, hC⟩
      show e.mapEl (t i) = _
      rw [hs i]; rfl
    · rintro ⟨s', hs', hC⟩
      refine ⟨fun i => e.symm.toFun n (s' i), fun i => ?_, ?_⟩
      · have : e.mapEl (t i) = Sorted.inj T'.U (s' i) := hs' i
        rw [← e.symm_mapEl (t i), this]; rfl
      · show (fun i => e.toFun n (e.symm.toFun n (s' i))) ∈ C'
        simp only [TowerIso.toFun_symm]; exact hC
  rw [this]; exact hC'

/-- The bijection on sort `n`, as an inner embedding between the sort models. -/
noncomputable def sortEmb (hT : IsTowerModel ⟨T, 𝒟⟩) (hT' : IsTowerModel ⟨T', 𝒟.map e⟩) (n : ℕ) :
    InnerEmb (hT.sortModel n) (hT'.sortModel n) where
  φ := e.toFun n
  injective := (e.bijective n).1
  mem_iff := e.mem_iff n
  trans := fun _ z _ => ⟨e.symm.toFun n z, e.toFun_symm z⟩
  supertrans := fun _ z _ => ⟨e.symm.toFun n z, e.toFun_symm z⟩

/-- Transport of the axioms of `H` along a tower isomorphism. -/
theorem transport (hT : IsTowerModel ⟨T, 𝒟⟩) : IsTowerModel ⟨T', 𝒟.map e⟩ := by
  have hzfc : ∀ n, SetAxioms (T'.sortStr n) ((𝒟.map e).DefOn n) :=
    fun n => setAxioms_transport e n (hT.zfc n)
  -- a temporary model to use the absoluteness lemmas
  let Z' : ℕ → ZFCModel.{u} := fun n => ⟨T'.sortStr n, (𝒟.map e).sortSystem n, hzfc n⟩
  let emb : ∀ n, InnerEmb (hT.sortModel n) (Z' n) := fun n =>
    { φ := e.toFun n
      injective := (e.bijective n).1
      mem_iff := e.mem_iff n
      trans := fun _ z _ => ⟨e.symm.toFun n z, e.toFun_symm z⟩
      supertrans := fun _ z _ => ⟨e.symm.toFun n z, e.toFun_symm z⟩ }
  refine ⟨hzfc, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n x' y' hxy
    rw [← e.toFun_symm x', ← e.toFun_symm y', ← e.j_comm, ← e.j_comm] at hxy
    have := hT.j_injective n _ _ ((e.bijective (n + 1)).1 hxy)
    rw [← e.toFun_symm x', ← e.toFun_symm y', this]
  · intro n x' y'
    rw [← e.toFun_symm x', ← e.toFun_symm y', ← e.j_comm, ← e.j_comm, e.mem_iff, e.mem_iff]
    exact hT.j_mem_iff n _ _
  · intro n
    have := ((emb (n + 1)).inaccessible_iff (T.κ n)).2 (hT.kappa_inaccessible n)
    rw [show (emb (n + 1)).φ (T.κ n) = T'.κ n from e.κ_comm n] at this
    exact this
  · intro n
    obtain ⟨v, hv, hmem⟩ := hT.j_image n
    refine ⟨e.toFun (n + 1) v, ?_, fun y' => ?_⟩
    · have := (emb (n + 1)).isV_of hv
      rw [show (emb (n + 1)).φ (T.κ n) = T'.κ n from e.κ_comm n] at this
      exact this
    · rw [← e.toFun_symm y', e.mem_iff, hmem]
      constructor
      · rintro ⟨x, hx⟩
        exact ⟨e.toFun n x, by rw [← e.j_comm, hx]⟩
      · rintro ⟨x', hx'⟩
        refine ⟨e.symm.toFun n x', ?_⟩
        apply (e.bijective (n + 1)).1
        rw [e.j_comm, e.toFun_symm, hx', e.toFun_symm]
  · intro n
    have := ((emb (n + 2)).nextInaccessible_iff _ _).2 (hT.next_inaccessible n)
    show (T'.sortStr (n + 2)).NextInaccessible (T'.j (n + 1) (T'.κ n)) (T'.κ (n + 1))
    rw [← e.κ_comm n, ← e.j_comm, ← e.κ_comm (n + 1)]
    exact this
  · have := ((emb 1).noGreatestInaccessibleBelow_iff _).2 hT.bottom
    show (T'.sortStr 1).NoGreatestInaccessibleBelow (T'.κ 0)
    rw [← e.κ_comm 0]
    exact this

end IsTowerModel

end SolidLean.Solid
