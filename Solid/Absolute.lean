module

public import Solid.Rank

/-!
# Absoluteness along inner embeddings

An `InnerEmb Z Z'` is an injective membership-preserving map from one ZFC
model into another whose image is transitive and closed under subsets (a
"supertransitive" inner part).  The transition maps of a tower model, and
the collapse maps of draft 2 §2 after Step 3, are such embeddings.

All the notions of `Solid.SetTheory` are absolute along such an embedding:
bounded ones directly, the others because their witnesses (functions between
sets of the image, power sets) are subsets of sets in the image and hence in
it.  The rank predicate `IsV` is shown upward absolute, which is all that is
used.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open SetClassSystem

namespace ZFCModel

variable (Z : ZFCModel.{u})

local notation:50 x " ∈' " y => Z.S.mem x y

/-- The union of two sets. -/
theorem exists_union2 (x y : Z.S.X) : ∃ u, ∀ z, (z ∈' u) ↔ (z ∈' x) ∨ (z ∈' y) := by
  obtain ⟨p, hp⟩ := Z.ax.pair x y
  obtain ⟨u, hu⟩ := Z.ax.union p
  refine ⟨u, fun z => ?_⟩
  rw [hu z]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases (hp w).1 hw with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (hz | hz)
    · exact ⟨x, (hp x).2 (Or.inl rfl), hz⟩
    · exact ⟨y, (hp y).2 (Or.inr rfl), hz⟩

/-- The cartesian product, as a set of Kuratowski pairs. -/
theorem exists_prod (x y : Z.S.X) :
    ∃ r, ∀ p, (p ∈' r) ↔ ∃ a b, (a ∈' x) ∧ (b ∈' y) ∧ Z.S.IsOrdPair a b p := by
  obtain ⟨u, hu⟩ := Z.exists_union2 x y
  obtain ⟨pu, hpu⟩ := Z.ax.power u
  obtain ⟨ppu, hppu⟩ := Z.ax.power pu
  let P : Z.S.X → Prop := fun p => ∃ a b, (a ∈' x) ∧ (b ∈' y) ∧ Z.S.IsOrdPair a b p
  have hdef : Z.𝒞.Def 1 (fun t => P (t 0)) := by
    refine Def.congr ?_ (((Def.exists_ (Def.exists_ (Def.and_
      (Def.mem (Fin.castSucc (Fin.last 3)) (Fin.castSucc (Fin.castSucc 1)))
      (Def.and_ (Def.mem (Fin.last 4) (Fin.castSucc (Fin.castSucc 2)))
        (Def.isOrdPair (Fin.castSucc (Fin.last 3)) (Fin.last 4)
          (Fin.castSucc (Fin.castSucc (0 : Fin 3)))))))).withParam y).withParam x)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  obtain ⟨r, hr⟩ := Z.sepP hdef ppu
  refine ⟨r, fun p => ?_⟩
  rw [hr p]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨a, b, ha, hb, s, d, hs, hd, hp⟩ := h
    apply (hppu p).2
    intro z hz
    apply (hpu z).2
    intro w hw
    rcases (hp z).1 hz with rfl | rfl
    · rw [(hs w).1 hw]; exact (hu a).2 (Or.inl ha)
    · rcases (hd w).1 hw with rfl | rfl
      · exact (hu w).2 (Or.inl ha)
      · exact (hu w).2 (Or.inr hb)

end ZFCModel

/-- An embedding of a ZFC model into another as a transitive, subset-closed
inner part. -/
structure InnerEmb (Z Z' : ZFCModel.{u}) where
  φ : Z.S.X → Z'.S.X
  injective : Function.Injective φ
  mem_iff : ∀ x y, Z'.S.mem (φ x) (φ y) ↔ Z.S.mem x y
  trans : ∀ x z, Z'.S.mem z (φ x) → ∃ x', φ x' = z
  supertrans : ∀ x z, Z'.S.Subset z (φ x) → ∃ x', φ x' = z

namespace InnerEmb

variable {Z Z' : ZFCModel.{u}} (e : InnerEmb Z Z')

local notation:50 x " ∈₁ " y => Z.S.mem x y
local notation:50 x " ∈₂ " y => Z'.S.mem x y

theorem φ_inj {x y : Z.S.X} (h : e.φ x = e.φ y) : x = y := e.injective h

theorem mem_image_iff (x : Z.S.X) (z : Z'.S.X) :
    (z ∈₂ e.φ x) ↔ ∃ x', (x' ∈₁ x) ∧ e.φ x' = z := by
  constructor
  · intro h
    obtain ⟨x', rfl⟩ := e.trans x z h
    exact ⟨x', (e.mem_iff x' x).1 h, rfl⟩
  · rintro ⟨x', hx', rfl⟩
    exact (e.mem_iff x' x).2 hx'

theorem subset_iff (x y : Z.S.X) : Z'.S.Subset (e.φ x) (e.φ y) ↔ Z.S.Subset x y := by
  constructor
  · intro h z hz
    exact (e.mem_iff z y).1 (h (e.φ z) ((e.mem_iff z x).2 hz))
  · intro h z' hz'
    obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff x z').1 hz'
    exact (e.mem_iff z y).2 (h z hz)

theorem subset_image_iff (z : Z'.S.X) (y : Z.S.X) :
    Z'.S.Subset z (e.φ y) ↔ ∃ x, e.φ x = z ∧ Z.S.Subset x y := by
  constructor
  · intro h
    obtain ⟨x, rfl⟩ := e.supertrans y z h
    exact ⟨x, rfl, (e.subset_iff x y).1 h⟩
  · rintro ⟨x, rfl, h⟩
    exact (e.subset_iff x y).2 h

/-! ### Bounded notions -/

theorem isEmptySet_iff (x : Z.S.X) : Z'.S.IsEmptySet (e.φ x) ↔ Z.S.IsEmptySet x := by
  constructor
  · intro h z hz; exact h (e.φ z) ((e.mem_iff z x).2 hz)
  · intro h z' hz'
    obtain ⟨z, hz, -⟩ := (e.mem_image_iff x z').1 hz'
    exact h z hz

theorem nonempty_iff (x : Z.S.X) : Z'.S.Nonempty (e.φ x) ↔ Z.S.Nonempty x := by
  constructor
  · rintro ⟨z', hz'⟩
    obtain ⟨z, hz, -⟩ := (e.mem_image_iff x z').1 hz'
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩; exact ⟨e.φ z, (e.mem_iff z x).2 hz⟩

theorem isPairSet_iff (a b p : Z.S.X) :
    Z'.S.IsPairSet (e.φ a) (e.φ b) (e.φ p) ↔ Z.S.IsPairSet a b p := by
  constructor
  · intro h z
    rw [← e.mem_iff, h (e.φ z)]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl (e.φ_inj h1)
      · exact Or.inr (e.φ_inj h1)
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  · intro h z'
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff p z').1 hz'
      rcases (h z).1 hz with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact (e.mem_iff a p).2 ((h a).2 (Or.inl rfl))
      · exact (e.mem_iff b p).2 ((h b).2 (Or.inr rfl))

theorem isSingleton_iff (a s : Z.S.X) :
    Z'.S.IsSingleton (e.φ a) (e.φ s) ↔ Z.S.IsSingleton a s := by
  constructor
  · intro h z
    rw [← e.mem_iff, h (e.φ z)]
    exact ⟨fun h1 => e.φ_inj h1, fun h1 => by rw [h1]⟩
  · intro h z'
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff s z').1 hz'
      rw [(h z).1 hz]
    · rintro rfl
      exact (e.mem_iff a s).2 ((h a).2 rfl)

theorem isOrdPair_iff (a b p : Z.S.X) :
    Z'.S.IsOrdPair (e.φ a) (e.φ b) (e.φ p) ↔ Z.S.IsOrdPair a b p := by
  constructor
  · rintro ⟨s', d', hs', hd', hp'⟩
    obtain ⟨s, -, rfl⟩ := (e.mem_image_iff p s').1 ((hp' s').2 (Or.inl rfl))
    obtain ⟨d, -, rfl⟩ := (e.mem_image_iff p d').1 ((hp' d').2 (Or.inr rfl))
    exact ⟨s, d, (e.isSingleton_iff a s).1 hs', (e.isPairSet_iff a b d).1 hd',
      (e.isPairSet_iff s d p).1 hp'⟩
  · rintro ⟨s, d, hs, hd, hp⟩
    exact ⟨e.φ s, e.φ d, (e.isSingleton_iff a s).2 hs, (e.isPairSet_iff a b d).2 hd,
      (e.isPairSet_iff s d p).2 hp⟩

/-- An ordered pair of image elements is in the image. -/
theorem isOrdPair_image {a b : Z.S.X} {p' : Z'.S.X} (h : Z'.S.IsOrdPair (e.φ a) (e.φ b) p') :
    ∃ p, e.φ p = p' ∧ Z.S.IsOrdPair a b p := by
  obtain ⟨p, hp⟩ := Z.exists_ordPair a b
  exact ⟨p, Z'.ordPair_unique ((e.isOrdPair_iff a b p).2 hp) h, hp⟩

/-- The components of an ordered pair in the image are in the image. -/
theorem isOrdPair_image' {a' b' : Z'.S.X} {p : Z.S.X} (h : Z'.S.IsOrdPair a' b' (e.φ p)) :
    ∃ a b, e.φ a = a' ∧ e.φ b = b' ∧ Z.S.IsOrdPair a b p := by
  obtain ⟨s', d', hs', hd', hp'⟩ := h
  obtain ⟨s, -, rfl⟩ := (e.mem_image_iff p s').1 ((hp' s').2 (Or.inl rfl))
  obtain ⟨d, -, rfl⟩ := (e.mem_image_iff p d').1 ((hp' d').2 (Or.inr rfl))
  obtain ⟨a, -, rfl⟩ := (e.mem_image_iff s a').1 ((hs' a').2 rfl)
  obtain ⟨b, -, rfl⟩ := (e.mem_image_iff d b').1 ((hd' b').2 (Or.inr rfl))
  exact ⟨a, b, rfl, rfl, (e.isOrdPair_iff a b p).1 ⟨e.φ s, e.φ d, hs', hd', hp'⟩⟩

theorem isUnionSet_iff (x u : Z.S.X) : Z'.S.IsUnionSet (e.φ x) (e.φ u) ↔ Z.S.IsUnionSet x u := by
  constructor
  · intro h z
    rw [← e.mem_iff, h (e.φ z)]
    constructor
    · rintro ⟨y', hy', hz⟩
      obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
      exact ⟨y, hy, (e.mem_iff z y).1 hz⟩
    · rintro ⟨y, hy, hz⟩
      exact ⟨e.φ y, (e.mem_iff y x).2 hy, (e.mem_iff z y).2 hz⟩
  · intro h z'
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff u z').1 hz'
      obtain ⟨y, hy, hz⟩ := (h z).1 hz
      exact ⟨e.φ y, (e.mem_iff y x).2 hy, (e.mem_iff z y).2 hz⟩
    · rintro ⟨y', hy', hz'⟩
      obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff y z').1 hz'
      exact (e.mem_iff z u).2 ((h z).2 ⟨y, hy, hz⟩)

theorem isPowerSet_iff (x p : Z.S.X) : Z'.S.IsPowerSet (e.φ x) (e.φ p) ↔ Z.S.IsPowerSet x p := by
  constructor
  · intro h z
    rw [← e.mem_iff, h (e.φ z), e.subset_iff]
  · intro h z'
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff p z').1 hz'
      exact (e.subset_iff z x).2 ((h z).1 hz)
    · intro hz'
      obtain ⟨z, rfl, hz⟩ := (e.subset_image_iff z' x).1 hz'
      exact (e.mem_iff z p).2 ((h z).2 hz)

/-- The power set (in `Z'`) of an image element is in the image. -/
theorem isPowerSet_image {x : Z.S.X} {p' : Z'.S.X} (h : Z'.S.IsPowerSet (e.φ x) p') :
    ∃ p, e.φ p = p' ∧ Z.S.IsPowerSet x p := by
  obtain ⟨p, hp⟩ := Z.ax.power x
  refine ⟨p, Z'.ax.ext _ _ fun z => ?_, hp⟩
  rw [((e.isPowerSet_iff x p).2 hp) z, h z]

theorem isSucc_iff (x s : Z.S.X) : Z'.S.IsSucc (e.φ x) (e.φ s) ↔ Z.S.IsSucc x s := by
  constructor
  · intro h z
    rw [← e.mem_iff, h (e.φ z), e.mem_iff]
    exact or_congr Iff.rfl ⟨fun h1 => e.φ_inj h1, fun h1 => by rw [h1]⟩
  · intro h z'
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff s z').1 hz'
      rcases (h z).1 hz with hz | rfl
      · exact Or.inl ((e.mem_iff z x).2 hz)
      · exact Or.inr rfl
    · rintro (hz' | rfl)
      · obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff x z').1 hz'
        exact (e.mem_iff z s).2 ((h z).2 (Or.inl hz))
      · exact (e.mem_iff x s).2 ((h x).2 (Or.inr rfl))

theorem transitive_iff (x : Z.S.X) : Z'.S.Transitive (e.φ x) ↔ Z.S.Transitive x := by
  constructor
  · intro h y hy
    exact (e.subset_iff y x).1 (h (e.φ y) ((e.mem_iff y x).2 hy))
  · intro h y' hy'
    obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
    exact (e.subset_iff y x).2 (h y hy)

theorem funApp_iff (f a b : Z.S.X) :
    Z'.S.FunApp (e.φ f) (e.φ a) (e.φ b) ↔ Z.S.FunApp f a b := by
  constructor
  · rintro ⟨p', hp', hpair⟩
    obtain ⟨p, hp, rfl⟩ := (e.mem_image_iff f p').1 hp'
    exact ⟨p, hp, (e.isOrdPair_iff a b p).1 hpair⟩
  · rintro ⟨p, hp, hpair⟩
    exact ⟨e.φ p, (e.mem_iff p f).2 hp, (e.isOrdPair_iff a b p).2 hpair⟩

/-- Arguments and values of an image function are in the image. -/
theorem funApp_image {f : Z.S.X} {a' b' : Z'.S.X} (h : Z'.S.FunApp (e.φ f) a' b') :
    ∃ a b, e.φ a = a' ∧ e.φ b = b' ∧ Z.S.FunApp f a b := by
  obtain ⟨p', hp', hpair⟩ := h
  obtain ⟨p, hp, rfl⟩ := (e.mem_image_iff f p').1 hp'
  obtain ⟨a, b, rfl, rfl, hab⟩ := e.isOrdPair_image' hpair
  exact ⟨a, b, rfl, rfl, p, hp, hab⟩

theorem inDom_iff (f a : Z.S.X) : Z'.S.InDom (e.φ f) (e.φ a) ↔ Z.S.InDom f a := by
  constructor
  · rintro ⟨b', hb'⟩
    obtain ⟨a2, b, ha2, rfl, hab⟩ := e.funApp_image hb'
    have := e.φ_inj ha2
    subst this
    exact ⟨b, hab⟩
  · rintro ⟨b, hb⟩
    exact ⟨e.φ b, (e.funApp_iff f a b).2 hb⟩

theorem isRelation_iff (f : Z.S.X) : Z'.S.IsRelation (e.φ f) ↔ Z.S.IsRelation f := by
  constructor
  · intro h p hp
    obtain ⟨a', b', hab⟩ := h (e.φ p) ((e.mem_iff p f).2 hp)
    obtain ⟨a, b, -, -, hab'⟩ := e.isOrdPair_image' hab
    exact ⟨a, b, hab'⟩
  · intro h p' hp'
    obtain ⟨p, hp, rfl⟩ := (e.mem_image_iff f p').1 hp'
    obtain ⟨a, b, hab⟩ := h p hp
    exact ⟨e.φ a, e.φ b, (e.isOrdPair_iff a b p).2 hab⟩

theorem isFunction_iff (f : Z.S.X) : Z'.S.IsFunction (e.φ f) ↔ Z.S.IsFunction f := by
  constructor
  · rintro ⟨hrel, hfun⟩
    refine ⟨(e.isRelation_iff f).1 hrel, fun a b b' hb hb' => ?_⟩
    exact e.φ_inj (hfun (e.φ a) (e.φ b) (e.φ b') ((e.funApp_iff f a b).2 hb)
      ((e.funApp_iff f a b').2 hb'))
  · rintro ⟨hrel, hfun⟩
    refine ⟨(e.isRelation_iff f).2 hrel, fun a' b' b'' hb' hb'' => ?_⟩
    obtain ⟨a, b, rfl, rfl, hab⟩ := e.funApp_image hb'
    obtain ⟨a2, b2, ha2, rfl, hab2⟩ := e.funApp_image hb''
    rw [e.φ_inj ha2] at hab2
    rw [hfun a b b2 hab hab2]

theorem isFunctionOn_iff (f d : Z.S.X) :
    Z'.S.IsFunctionOn (e.φ f) (e.φ d) ↔ Z.S.IsFunctionOn f d := by
  constructor
  · rintro ⟨hf, hdom⟩
    refine ⟨(e.isFunction_iff f).1 hf, fun a => ?_⟩
    rw [← e.inDom_iff, hdom (e.φ a), e.mem_iff]
  · rintro ⟨hf, hdom⟩
    refine ⟨(e.isFunction_iff f).2 hf, fun a' => ?_⟩
    constructor
    · rintro ⟨b', hb'⟩
      obtain ⟨a, b, rfl, rfl, hab⟩ := e.funApp_image hb'
      exact (e.mem_iff a d).2 ((hdom a).1 ⟨b, hab⟩)
    · intro ha'
      obtain ⟨a, ha, rfl⟩ := (e.mem_image_iff d a').1 ha'
      exact (e.inDom_iff f a).2 ((hdom a).2 ha)

theorem injective_iff (f : Z.S.X) : Z'.S.Injective (e.φ f) ↔ Z.S.Injective f := by
  constructor
  · intro h a a' b ha ha'
    exact e.φ_inj (h (e.φ a) (e.φ a') (e.φ b) ((e.funApp_iff f a b).2 ha)
      ((e.funApp_iff f a' b).2 ha'))
  · intro h a' a'' b' ha' ha''
    obtain ⟨a, b, rfl, rfl, hab⟩ := e.funApp_image ha'
    obtain ⟨a2, b2, rfl, hb2, hab2⟩ := e.funApp_image ha''
    rw [e.φ_inj hb2] at hab2
    rw [h a a2 b hab hab2]

theorem mapsInto_iff (f c : Z.S.X) : Z'.S.MapsInto (e.φ f) (e.φ c) ↔ Z.S.MapsInto f c := by
  constructor
  · intro h a b hab
    exact (e.mem_iff b c).1 (h (e.φ a) (e.φ b) ((e.funApp_iff f a b).2 hab))
  · intro h a' b' hab'
    obtain ⟨a, b, rfl, rfl, hab⟩ := e.funApp_image hab'
    exact (e.mem_iff b c).2 (h a b hab)

theorem isInjectionInto_iff (f d c : Z.S.X) :
    Z'.S.IsInjectionInto (e.φ f) (e.φ d) (e.φ c) ↔ Z.S.IsInjectionInto f d c := by
  unfold MemStr.IsInjectionInto
  rw [e.isFunctionOn_iff, e.injective_iff, e.mapsInto_iff]

theorem isBijectionOnto_iff (f d c : Z.S.X) :
    Z'.S.IsBijectionOnto (e.φ f) (e.φ d) (e.φ c) ↔ Z.S.IsBijectionOnto f d c := by
  unfold MemStr.IsBijectionOnto
  rw [e.isInjectionInto_iff]
  refine and_congr Iff.rfl ⟨fun h b hb => ?_, fun h b' hb' => ?_⟩
  · obtain ⟨a', ha'⟩ := h (e.φ b) ((e.mem_iff b c).2 hb)
    obtain ⟨a, b2, rfl, hb2, hab⟩ := e.funApp_image ha'
    have := e.φ_inj hb2
    subst this
    exact ⟨a, hab⟩
  · obtain ⟨b, hb, rfl⟩ := (e.mem_image_iff c b').1 hb'
    obtain ⟨a, ha⟩ := h b hb
    exact ⟨e.φ a, (e.funApp_iff f a b).2 ha⟩

theorem isOrdinal_iff (x : Z.S.X) : Z'.S.IsOrdinal (e.φ x) ↔ Z.S.IsOrdinal x := by
  constructor
  · rintro ⟨ht, hmt, hlin⟩
    refine ⟨(e.transitive_iff x).1 ht, fun y hy => ?_, fun y z hy hz => ?_⟩
    · exact (e.transitive_iff y).1 (hmt (e.φ y) ((e.mem_iff y x).2 hy))
    · rcases hlin (e.φ y) (e.φ z) ((e.mem_iff y x).2 hy) ((e.mem_iff z x).2 hz) with h | h | h
      · exact Or.inl ((e.mem_iff y z).1 h)
      · exact Or.inr (Or.inl (e.φ_inj h))
      · exact Or.inr (Or.inr ((e.mem_iff z y).1 h))
  · rintro ⟨ht, hmt, hlin⟩
    refine ⟨(e.transitive_iff x).2 ht, fun y' hy' => ?_, fun y' z' hy' hz' => ?_⟩
    · obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
      exact (e.transitive_iff y).2 (hmt y hy)
    · obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff x z').1 hz'
      rcases hlin y z hy hz with h | rfl | h
      · exact Or.inl ((e.mem_iff y z).2 h)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr ((e.mem_iff z y).2 h))

theorem isLimitOrd_iff (x : Z.S.X) : Z'.S.IsLimitOrd (e.φ x) ↔ Z.S.IsLimitOrd x := by
  unfold MemStr.IsLimitOrd
  rw [e.isOrdinal_iff, e.nonempty_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h y hy => ?_, fun h y' hy' => ?_⟩)
  · obtain ⟨s', hs', hsx⟩ := h (e.φ y) ((e.mem_iff y x).2 hy)
    obtain ⟨s, -, rfl⟩ := (e.mem_image_iff x s').1 hsx
    exact ⟨s, (e.isSucc_iff y s).1 hs', (e.mem_iff s x).1 hsx⟩
  · obtain ⟨y, hy, rfl⟩ := (e.mem_image_iff x y').1 hy'
    obtain ⟨s, hs, hsx⟩ := h y hy
    exact ⟨e.φ s, (e.isSucc_iff y s).2 hs, (e.mem_iff s x).2 hsx⟩

theorem isSuccOrd_iff (x : Z.S.X) : Z'.S.IsSuccOrd (e.φ x) ↔ Z.S.IsSuccOrd x := by
  unfold MemStr.IsSuccOrd
  rw [e.isOrdinal_iff]
  refine and_congr Iff.rfl ⟨fun ⟨y', hy'⟩ => ?_, fun ⟨y, hy⟩ => ⟨e.φ y, (e.isSucc_iff y x).2 hy⟩⟩
  obtain ⟨y, -, rfl⟩ := (e.mem_image_iff x y').1 (ZFCModel.IsSucc.self_mem Z' hy')
  exact ⟨y, (e.isSucc_iff y x).1 hy'⟩

/-! ### Sets of pairs between image sets are in the image -/

/-- A set of ordered pairs with components in image sets is in the image. -/
theorem relation_image {x y : Z.S.X} {f' : Z'.S.X}
    (h : ∀ p', (p' ∈₂ f') → ∃ a b, (a ∈₂ e.φ x) ∧ (b ∈₂ e.φ y) ∧ Z'.S.IsOrdPair a b p') :
    ∃ f, e.φ f = f' := by
  obtain ⟨r, hr⟩ := Z.exists_prod x y
  apply e.supertrans r f'
  intro p' hp'
  obtain ⟨a', b', ha', hb', hpair⟩ := h p' hp'
  obtain ⟨a, ha, rfl⟩ := (e.mem_image_iff x a').1 ha'
  obtain ⟨b, hb, rfl⟩ := (e.mem_image_iff y b').1 hb'
  obtain ⟨p, rfl, hp⟩ := e.isOrdPair_image hpair
  exact (e.mem_iff p r).2 ((hr p).2 ⟨a, b, ha, hb, hp⟩)

/-- A function (in `Z'`) from an image set into an image set is in the image. -/
theorem functionOn_image {x y : Z.S.X} {f' : Z'.S.X} (hf : Z'.S.IsFunctionOn f' (e.φ x))
    (hm : Z'.S.MapsInto f' (e.φ y)) : ∃ f, e.φ f = f' := by
  apply e.relation_image (x := x) (y := y)
  intro p' hp'
  obtain ⟨a, b, hab⟩ := hf.1.1 p' hp'
  have hfab : Z'.S.FunApp f' a b := ⟨p', hp', hab⟩
  exact ⟨a, b, (hf.2 a).1 ⟨b, hfab⟩, hm a b hfab, hab⟩

/-! ### Cardinals and inaccessibility -/

theorem isCardinal_iff (κ : Z.S.X) : Z'.S.IsCardinal (e.φ κ) ↔ Z.S.IsCardinal κ := by
  unfold MemStr.IsCardinal
  rw [e.isOrdinal_iff]
  refine and_congr Iff.rfl ⟨fun h β hβ ⟨f, hf⟩ => ?_, fun h β' hβ' ⟨f', hf'⟩ => ?_⟩
  · exact h (e.φ β) ((e.mem_iff β κ).2 hβ) ⟨e.φ f, (e.isBijectionOnto_iff f β κ).2 hf⟩
  · obtain ⟨β, hβ, rfl⟩ := (e.mem_image_iff κ β').1 hβ'
    obtain ⟨f, rfl⟩ := e.functionOn_image hf'.1.1 hf'.1.2.2
    exact h β hβ ⟨f, (e.isBijectionOnto_iff f β κ).1 hf'⟩

theorem isRegular_iff (κ : Z.S.X) : Z'.S.IsRegular (e.φ κ) ↔ Z.S.IsRegular κ := by
  unfold MemStr.IsRegular
  rw [e.isOrdinal_iff]
  refine and_congr Iff.rfl ⟨fun h β f hβ hf hm => ?_, fun h β' f' hβ' hf' hm' => ?_⟩
  · obtain ⟨γ', hγ', hb⟩ := h (e.φ β) (e.φ f) ((e.mem_iff β κ).2 hβ)
      ((e.isFunctionOn_iff f β).2 hf) ((e.mapsInto_iff f κ).2 hm)
    obtain ⟨γ, hγ, rfl⟩ := (e.mem_image_iff κ γ').1 hγ'
    refine ⟨γ, hγ, fun a b hab => ?_⟩
    exact (e.mem_iff b γ).1 (hb (e.φ a) (e.φ b) ((e.funApp_iff f a b).2 hab))
  · obtain ⟨β, hβ, rfl⟩ := (e.mem_image_iff κ β').1 hβ'
    obtain ⟨f, rfl⟩ := e.functionOn_image hf' hm'
    obtain ⟨γ, hγ, hb⟩ := h β f hβ ((e.isFunctionOn_iff f β).1 hf') ((e.mapsInto_iff f κ).1 hm')
    refine ⟨e.φ γ, (e.mem_iff γ κ).2 hγ, fun a' b' hab' => ?_⟩
    obtain ⟨a, b, rfl, rfl, hab⟩ := e.funApp_image hab'
    exact (e.mem_iff b γ).2 (hb a b hab)

theorem isStrongLimit_iff (κ : Z.S.X) : Z'.S.IsStrongLimit (e.φ κ) ↔ Z.S.IsStrongLimit κ := by
  unfold MemStr.IsStrongLimit
  rw [e.isOrdinal_iff]
  refine and_congr Iff.rfl ⟨fun h β hβ p hp => ?_, fun h β' hβ' p' hp' => ?_⟩
  · obtain ⟨γ', f', hγ', hf'⟩ := h (e.φ β) ((e.mem_iff β κ).2 hβ) (e.φ p)
      ((e.isPowerSet_iff β p).2 hp)
    obtain ⟨γ, hγ, rfl⟩ := (e.mem_image_iff κ γ').1 hγ'
    obtain ⟨f, rfl⟩ := e.functionOn_image hf'.1 hf'.2.2
    exact ⟨γ, f, hγ, (e.isInjectionInto_iff f p γ).1 hf'⟩
  · obtain ⟨β, hβ, rfl⟩ := (e.mem_image_iff κ β').1 hβ'
    obtain ⟨p, rfl, hp⟩ := e.isPowerSet_image hp'
    obtain ⟨γ, f, hγ, hf⟩ := h β hβ p hp
    exact ⟨e.φ γ, e.φ f, (e.mem_iff γ κ).2 hγ, (e.isInjectionInto_iff f p γ).2 hf⟩

theorem inaccessible_iff (κ : Z.S.X) : Z'.S.Inaccessible (e.φ κ) ↔ Z.S.Inaccessible κ := by
  unfold MemStr.Inaccessible
  rw [e.isCardinal_iff, e.isRegular_iff, e.isStrongLimit_iff]
  refine and_congr Iff.rfl (and_congr ⟨fun ⟨ω', hω', hl⟩ => ?_, fun ⟨ω, hω, hl⟩ => ?_⟩ Iff.rfl)
  · obtain ⟨ω, hω, rfl⟩ := (e.mem_image_iff κ ω').1 hω'
    exact ⟨ω, hω, (e.isLimitOrd_iff ω).1 hl⟩
  · exact ⟨e.φ ω, (e.mem_iff ω κ).2 hω, (e.isLimitOrd_iff ω).2 hl⟩

theorem nextInaccessible_iff (α β : Z.S.X) :
    Z'.S.NextInaccessible (e.φ α) (e.φ β) ↔ Z.S.NextInaccessible α β := by
  unfold MemStr.NextInaccessible
  rw [e.inaccessible_iff, e.mem_iff]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun h γ h1 h2 => ?_, fun h γ' h1 h2 => ?_⟩)
  · rw [← e.inaccessible_iff]
    exact h (e.φ γ) ((e.mem_iff α γ).2 h1) ((e.mem_iff γ β).2 h2)
  · obtain ⟨γ, hγ, rfl⟩ := (e.mem_image_iff β γ').1 h2
    rw [e.inaccessible_iff]
    exact h γ ((e.mem_iff α γ).1 h1) hγ

theorem noGreatestInaccessibleBelow_iff (κ : Z.S.X) :
    Z'.S.NoGreatestInaccessibleBelow (e.φ κ) ↔ Z.S.NoGreatestInaccessibleBelow κ := by
  constructor
  · intro h α hα hi
    obtain ⟨β', hβ', hαβ', hi'⟩ := h (e.φ α) ((e.mem_iff α κ).2 hα) ((e.inaccessible_iff α).2 hi)
    obtain ⟨β, hβ, rfl⟩ := (e.mem_image_iff κ β').1 hβ'
    exact ⟨β, hβ, (e.mem_iff α β).1 hαβ', (e.inaccessible_iff β).1 hi'⟩
  · intro h α' hα' hi'
    obtain ⟨α, hα, rfl⟩ := (e.mem_image_iff κ α').1 hα'
    obtain ⟨β, hβ, hαβ, hi⟩ := h α hα ((e.inaccessible_iff α).1 hi')
    exact ⟨e.φ β, (e.mem_iff β κ).2 hβ, (e.mem_iff α β).2 hαβ, (e.inaccessible_iff β).2 hi⟩

/-! ### The rank hierarchy, upward -/

theorem isVAttempt_of {f : Z.S.X} (hf : Z.S.IsVAttempt f) : Z'.S.IsVAttempt (e.φ f) := by
  refine ⟨(e.isFunction_iff f).2 hf.1, fun β' v' hβv' => ?_⟩
  obtain ⟨β, v, rfl, rfl, hβv⟩ := e.funApp_image hβv'
  obtain ⟨hord, hzero, hsucc, hlim⟩ := hf.2 β v hβv
  refine ⟨(e.isOrdinal_iff β).2 hord, fun h0 => ?_, fun γ' hγ' => ?_, fun hl z' => ?_⟩
  · exact (e.isEmptySet_iff v).2 (hzero ((e.isEmptySet_iff β).1 h0))
  · obtain ⟨γ, -, rfl⟩ := (e.mem_image_iff β γ').1 (ZFCModel.IsSucc.self_mem Z' hγ')
    obtain ⟨w, hw, hpw⟩ := hsucc γ ((e.isSucc_iff γ β).1 hγ')
    exact ⟨e.φ w, (e.funApp_iff f γ w).2 hw, (e.isPowerSet_iff w v).2 hpw⟩
  · have hl' := hlim ((e.isLimitOrd_iff β).1 hl)
    constructor
    · intro hz'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff v z').1 hz'
      obtain ⟨γ, w, hγ, hw, hzw⟩ := (hl' z).1 hz
      exact ⟨e.φ γ, e.φ w, (e.mem_iff γ β).2 hγ, (e.funApp_iff f γ w).2 hw, (e.mem_iff z w).2 hzw⟩
    · rintro ⟨γ', w', hγ', hw', hzw'⟩
      obtain ⟨γ, w, rfl, rfl, hw⟩ := e.funApp_image hw'
      obtain ⟨z, hz, rfl⟩ := (e.mem_image_iff w z').1 hzw'
      exact (e.mem_iff z v).2 ((hl' z).2 ⟨γ, w, (e.mem_iff γ β).1 hγ', hw, hz⟩)

theorem isV_of {α v : Z.S.X} (h : Z.S.IsV α v) : Z'.S.IsV (e.φ α) (e.φ v) := by
  obtain ⟨hord, f, hf, hd, hv⟩ := h
  refine ⟨(e.isOrdinal_iff α).2 hord, e.φ f, e.isVAttempt_of hf, fun γ' hγ' => ?_,
    (e.funApp_iff f α v).2 hv⟩
  rcases hγ' with hγ' | rfl
  · obtain ⟨γ, hγ, rfl⟩ := (e.mem_image_iff α γ').1 hγ'
    exact (e.inDom_iff f γ).2 (hd γ (Or.inl hγ))
  · exact (e.inDom_iff f α).2 (hd α (Or.inr rfl))

/-! ### Composition -/

/-- Inner embeddings compose. -/
def comp {Z'' : ZFCModel.{u}} (e' : InnerEmb Z' Z'') : InnerEmb Z Z'' where
  φ := e'.φ ∘ e.φ
  injective := e'.injective.comp e.injective
  mem_iff x y := by
    show Z''.S.mem (e'.φ (e.φ x)) (e'.φ (e.φ y)) ↔ _
    rw [e'.mem_iff, e.mem_iff]
  trans x z hz := by
    obtain ⟨y, rfl⟩ := e'.trans (e.φ x) z hz
    obtain ⟨x', rfl⟩ := e.trans x y ((e'.mem_iff y (e.φ x)).1 hz)
    exact ⟨x', rfl⟩
  supertrans x z hz := by
    obtain ⟨y, rfl⟩ := e'.supertrans (e.φ x) z hz
    obtain ⟨x', rfl⟩ := e.supertrans x y ((e'.subset_iff y (e.φ x)).1 hz)
    exact ⟨x', rfl⟩

@[simp] theorem comp_φ {Z'' : ZFCModel.{u}} (e' : InnerEmb Z' Z'') (x : Z.S.X) :
    (e.comp e').φ x = e'.φ (e.φ x) := rfl

end InnerEmb

end SolidLean.Solid
