module

public import Solid.Def

/-!
# Ordinals and the rank hierarchy, internally

Facts about ordinals, ordered pairs, functions and the attempts at
`α ↦ V_α` proved inside an arbitrary `ZFCModel`.  The rank hierarchy is
treated through attempts (`IsVAttempt`) without ever building it: the
results needed downstream are that attempts agree (`attempt_agree`), that
`V_α` is unique (`IsV.unique`), transitive and closed under subsets
(`IsV.transitive`, `IsV.subset_closed`), monotone (`IsV.mono`) and that
`α ∉ V_α` (`IsV.not_mem_self`).  Each foundation argument comes with the
definability certificate of the class it minimizes.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open SetClassSystem

namespace ZFCModel

variable (Z : ZFCModel.{u})

local notation:50 x " ∈' " y => Z.S.mem x y

/-! ### Pairs -/

theorem singleton_unique {a s s' : Z.S.X} (h : Z.S.IsSingleton a s) (h' : Z.S.IsSingleton a s') :
    s = s' :=
  Z.ax.ext s s' fun z => by rw [h z, h' z]

theorem pairSet_unique {a b d d' : Z.S.X} (h : Z.S.IsPairSet a b d) (h' : Z.S.IsPairSet a b d') :
    d = d' :=
  Z.ax.ext d d' fun z => by rw [h z, h' z]

theorem ordPair_unique {a b p p' : Z.S.X} (h : Z.S.IsOrdPair a b p) (h' : Z.S.IsOrdPair a b p') :
    p = p' := by
  obtain ⟨s, d, hs, hd, hp⟩ := h
  obtain ⟨s', d', hs', hd', hp'⟩ := h'
  have e1 := Z.singleton_unique hs hs'
  subst e1
  have e2 := Z.pairSet_unique hd hd'
  subst e2
  exact Z.pairSet_unique hp hp'

theorem ordPair_inj {a b a' b' p : Z.S.X} (h : Z.S.IsOrdPair a b p) (h' : Z.S.IsOrdPair a' b' p) :
    a = a' ∧ b = b' := by
  obtain ⟨s, d, hs, hd, hp⟩ := h
  obtain ⟨s', d', hs', hd', hp'⟩ := h'
  have haa : a = a' := by
    have hs'p : s' ∈' p := (hp' s').2 (Or.inl rfl)
    rcases (hp s').1 hs'p with h1 | h1
    · have : a' ∈' s := by rw [← h1]; exact (hs' a').2 rfl
      exact ((hs a').1 this).symm
    · have : a ∈' s' := by rw [h1]; exact (hd a).2 (Or.inl rfl)
      exact (hs' a).1 this
  refine ⟨haa, ?_⟩
  have hd'p : d' ∈' p := (hp' d').2 (Or.inr rfl)
  rcases (hp d').1 hd'p with h1 | h1
  · -- `d' = s`, so `b' = a`
    have hb'a : b' = a := (hs b').1 (by rw [← h1]; exact (hd' b').2 (Or.inr rfl))
    have hdp : d ∈' p := (hp d).2 (Or.inr rfl)
    rcases (hp' d).1 hdp with h2 | h2
    · have : b = a' := (hs' b).1 (by rw [← h2]; exact (hd b).2 (Or.inr rfl))
      rw [this, hb'a, haa]
    · have : b = a := (hs b).1 (by rw [← h1, ← h2]; exact (hd b).2 (Or.inr rfl))
      rw [this, hb'a]
  · -- `d' = d`
    have hb'd : b' ∈' d := by rw [← h1]; exact (hd' b').2 (Or.inr rfl)
    rcases (hd b').1 hb'd with h2 | h2
    · have hbd' : b ∈' d' := by rw [h1]; exact (hd b).2 (Or.inr rfl)
      rcases (hd' b).1 hbd' with h3 | h3
      · rw [h3, h2, haa]
      · exact h3
    · exact h2.symm

theorem mem_singleton_self {a s : Z.S.X} (h : Z.S.IsSingleton a s) : a ∈' s := (h a).2 rfl

/-! ### Functions -/

theorem funApp_unique {f a b b' : Z.S.X} (hf : Z.S.IsFunction f) (h : Z.S.FunApp f a b)
    (h' : Z.S.FunApp f a b') : b = b' :=
  hf.2 a b b' h h'

/-- The domain of a set of pairs is a set. -/
theorem exists_dom (f : Z.S.X) : ∃ d, ∀ a, (a ∈' d) ↔ Z.S.InDom f a := by
  obtain ⟨u1, hu1⟩ := Z.ax.union f
  obtain ⟨u2, hu2⟩ := Z.ax.union u1
  have hdef : Z.𝒞.Def 1 (fun t => Z.S.InDom f (t 0)) := by
    refine Def.congr ?_ ((Def.inDom 1 0).withParam f)
    intro t; exact Iff.rfl
  obtain ⟨d, hd⟩ := Z.sepP hdef u2
  refine ⟨d, fun a => ?_⟩
  rw [hd a]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨b, p, hp, s, d', hs, -, hpair⟩ := h
    exact (hu2 a).2 ⟨s, (hu1 s).2 ⟨p, hp, (hpair s).2 (Or.inl rfl)⟩, (hs a).2 rfl⟩

/-! ### Ordinals -/

theorem succ_unique {x s s' : Z.S.X} (h : Z.S.IsSucc x s) (h' : Z.S.IsSucc x s') : s = s' :=
  Z.ax.ext s s' fun z => by rw [h z, h' z]

theorem IsSucc.self_mem {x s : Z.S.X} (h : Z.S.IsSucc x s) : x ∈' s := (h x).2 (Or.inr rfl)

theorem IsSucc.mem_of_mem {x s z : Z.S.X} (h : Z.S.IsSucc x s) (hz : z ∈' x) : z ∈' s :=
  (h z).2 (Or.inl hz)

theorem IsOrdinal.succ {α s : Z.S.X} (hα : Z.S.IsOrdinal α) (hs : Z.S.IsSucc α s) :
    Z.S.IsOrdinal s := by
  refine ⟨?_, ?_, ?_⟩
  · intro y hy z hz
    rcases (hs y).1 hy with hy | rfl
    · exact (hs z).2 (Or.inl (hα.1 y hy z hz))
    · exact (hs z).2 (Or.inl hz)
  · intro y hy
    rcases (hs y).1 hy with hy | rfl
    · exact hα.2.1 y hy
    · exact hα.1
  · intro y z hy hz
    rcases (hs y).1 hy with hy | rfl <;> rcases (hs z).1 hz with hz | rfl
    · exact hα.2.2 y z hy hz
    · exact Or.inl hy
    · exact Or.inr (Or.inr hz)
    · exact Or.inr (Or.inl rfl)

theorem IsOrdinal.mem_trans {α β γ : Z.S.X} (hα : Z.S.IsOrdinal α) (hβ : β ∈' α) (hγ : γ ∈' β) :
    γ ∈' α :=
  hα.1 β hβ γ hγ

/-- Every ordinal is empty, a successor, or a limit. -/
theorem IsOrdinal.zero_or_succ_or_limit {α : Z.S.X} (hα : Z.S.IsOrdinal α) :
    Z.S.IsEmptySet α ∨ (∃ γ, Z.S.IsSucc γ α) ∨ Z.S.IsLimitOrd α := by
  by_cases h0 : Z.S.IsEmptySet α
  · exact Or.inl h0
  by_cases h1 : ∃ γ, Z.S.IsSucc γ α
  · exact Or.inr (Or.inl h1)
  refine Or.inr (Or.inr ⟨hα, ?_, ?_⟩)
  · by_contra hne
    exact h0 fun z hz => hne ⟨z, hz⟩
  · intro y hy
    obtain ⟨s, hs⟩ := Z.exists_succ y
    refine ⟨s, hs, ?_⟩
    have hsord : Z.S.IsOrdinal s := IsOrdinal.succ Z (IsOrdinal.mem Z hα hy) hs
    rcases IsOrdinal.trichotomy Z hsord hα with h | h | h
    · exact h
    · exact (h1 ⟨y, h ▸ hs⟩).elim
    · exfalso
      rcases (hs α).1 h with h' | h'
      · exact Z.mem_asymm h' hy
      · rw [h'] at hy; exact Z.mem_irrefl y hy

theorem IsLimitOrd.succ_mem {α y s : Z.S.X} (hα : Z.S.IsLimitOrd α) (hy : y ∈' α)
    (hs : Z.S.IsSucc y s) : s ∈' α := by
  obtain ⟨s', hs', hmem⟩ := hα.2.2 y hy
  rw [Z.succ_unique hs hs']; exact hmem

/-! ### Attempts at the rank hierarchy -/

section Attempts

variable {f : Z.S.X}

theorem IsVAttempt.ordinal (hf : Z.S.IsVAttempt f) {β v : Z.S.X} (h : Z.S.FunApp f β v) : Z.S.IsOrdinal β :=
  (hf.2 β v h).1

theorem IsVAttempt.zero (hf : Z.S.IsVAttempt f) {β v : Z.S.X} (h : Z.S.FunApp f β v) (h0 : Z.S.IsEmptySet β) :
    Z.S.IsEmptySet v :=
  (hf.2 β v h).2.1 h0

theorem IsVAttempt.succ (hf : Z.S.IsVAttempt f) {β v γ : Z.S.X} (h : Z.S.FunApp f β v) (hγ : Z.S.IsSucc γ β) :
    ∃ w, Z.S.FunApp f γ w ∧ Z.S.IsPowerSet w v :=
  (hf.2 β v h).2.2.1 γ hγ

theorem IsVAttempt.limit (hf : Z.S.IsVAttempt f) {β v : Z.S.X} (h : Z.S.FunApp f β v) (hβ : Z.S.IsLimitOrd β) :
    ∀ z, (z ∈' v) ↔ ∃ γ w, (γ ∈' β) ∧ Z.S.FunApp f γ w ∧ (z ∈' w) :=
  (hf.2 β v h).2.2.2 hβ

/-- Values of attempts are transitive and closed under subsets. -/
theorem IsVAttempt.good (hf : Z.S.IsVAttempt f) {β v : Z.S.X} (h : Z.S.FunApp f β v) :
    Z.S.Transitive v ∧ ∀ z y, (y ∈' v) → Z.S.Subset z y → z ∈' v := by
  -- the class of arguments with a bad value
  let Bad : Z.S.X → Prop := fun β' => ∃ v', Z.S.FunApp f β' v' ∧
    ¬ (Z.S.Transitive v' ∧ ∀ z y, (y ∈' v') → Z.S.Subset z y → z ∈' v')
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    refine Def.congr ?_ ((Def.exists_ (Def.and_ (Def.funApp (Fin.castSucc 1) (Fin.castSucc 0)
      (Fin.last 2)) (Def.not_ (Def.and_ (Def.transitive (Fin.last 2))
      (Def.forall_ (Def.forall_ (Def.imp_
        (Def.mem (Fin.last 4) (Fin.castSucc (Fin.castSucc (Fin.last 2))))
        (Def.imp_ (Def.subset (Fin.castSucc (Fin.last 3)) (Fin.last 4))
          (Def.mem (Fin.castSucc (Fin.last 3))
            (Fin.castSucc (Fin.castSucc (Fin.last 2)))))))))))).withParam f)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  by_contra hbad
  obtain ⟨d, hd⟩ := Z.exists_dom f
  obtain ⟨β0, ⟨v0, hv0, hbad0⟩, hmin⟩ := Z.class_foundationP hdef d
    (fun β' ⟨v', hv', _⟩ => (hd β').2 ⟨v', hv'⟩) ⟨β, v, h, hbad⟩
  have hgood : ∀ γ w, (γ ∈' β0) → Z.S.FunApp f γ w →
      Z.S.Transitive w ∧ ∀ z y, (y ∈' w) → Z.S.Subset z y → z ∈' w := by
    intro γ w hγ hw
    by_contra hb
    exact hmin γ hγ ⟨w, hw, hb⟩
  apply hbad0
  rcases IsOrdinal.zero_or_succ_or_limit Z (IsVAttempt.ordinal Z hf hv0) with h0 | ⟨γ, hγ⟩ | hlim
  · have hv0e := IsVAttempt.zero Z hf hv0 h0
    exact ⟨fun y hy => (hv0e y hy).elim, fun z y hy _ => (hv0e y hy).elim⟩
  · obtain ⟨w, hw, hpow⟩ := IsVAttempt.succ Z hf hv0 hγ
    obtain ⟨hwt, hwc⟩ := hgood γ w (IsSucc.self_mem Z hγ) hw
    refine ⟨fun y hy z hz => ?_, fun z y hy hzy => ?_⟩
    · have hyw : Z.S.Subset y w := (hpow y).1 hy
      exact (hpow z).2 (hwt z (hyw z hz))
    · exact (hpow z).2 fun x hx => (hpow y).1 hy x (hzy x hx)
  · have hl := IsVAttempt.limit Z hf hv0 hlim
    refine ⟨fun y hy z hz => ?_, fun z y hy hzy => ?_⟩
    · obtain ⟨γ, w, hγ, hw, hyw⟩ := (hl y).1 hy
      exact (hl z).2 ⟨γ, w, hγ, hw, (hgood γ w hγ hw).1 y hyw z hz⟩
    · obtain ⟨γ, w, hγ, hw, hyw⟩ := (hl y).1 hy
      exact (hl z).2 ⟨γ, w, hγ, hw, (hgood γ w hγ hw).2 z y hyw hzy⟩

theorem IsVAttempt.transitive (hf : Z.S.IsVAttempt f) {β v : Z.S.X} (h : Z.S.FunApp f β v) : Z.S.Transitive v :=
  (IsVAttempt.good Z hf h).1

theorem IsVAttempt.subset_closed (hf : Z.S.IsVAttempt f) {β v z y : Z.S.X} (h : Z.S.FunApp f β v) (hy : y ∈' v)
    (hzy : Z.S.Subset z y) : z ∈' v :=
  (IsVAttempt.good Z hf h).2 z y hy hzy

/-- Two attempts defined on all of `β` agree at `β`. -/
theorem attempt_agree {f g : Z.S.X} (hf : Z.S.IsVAttempt f) (hg : Z.S.IsVAttempt g)
    {β v w : Z.S.X} (hfd : ∀ γ, (γ ∈' β) → Z.S.InDom f γ) (hgd : ∀ γ, (γ ∈' β) → Z.S.InDom g γ)
    (hv : Z.S.FunApp f β v) (hw : Z.S.FunApp g β w) : v = w := by
  obtain ⟨sβ, hsβ⟩ := Z.exists_succ β
  let Bad : Z.S.X → Prop := fun β' => (β' ∈' sβ) ∧
    ∃ v' w', Z.S.FunApp f β' v' ∧ Z.S.FunApp g β' w' ∧ v' ≠ w'
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    refine Def.congr ?_ ((((Def.and_ (Def.mem (0 : Fin 4) 1) (Def.exists_ (Def.exists_ (Def.and_
      (Def.funApp (Fin.castSucc (Fin.castSucc 2)) (Fin.castSucc (Fin.castSucc 0))
        (Fin.castSucc (Fin.last 4)))
      (Def.and_ (Def.funApp (Fin.castSucc (Fin.castSucc 3)) (Fin.castSucc (Fin.castSucc 0))
        (Fin.last 5))
        (Def.not_ (Def.eq (Fin.castSucc (Fin.last 4)) (Fin.last 5)))))))).withParam g).withParam
          f).withParam sβ)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  have hβord : Z.S.IsOrdinal β := IsVAttempt.ordinal Z hf hv
  have hsord : Z.S.IsOrdinal sβ := IsOrdinal.succ Z hβord hsβ
  by_contra hne
  obtain ⟨β0, ⟨hβ0s, v0, w0, hv0, hw0, hne0⟩, hmin⟩ := Z.class_foundationP hdef sβ
    (fun β' h => h.1) ⟨β, (IsSucc.self_mem Z hsβ), v, w, hv, hw, hne⟩
  -- everything below `β0` lies in `β`, hence in the domains, and agrees
  have hbelow : ∀ γ, (γ ∈' β0) → γ ∈' β := by
    intro γ hγ
    rcases (hsβ β0).1 hβ0s with h | rfl
    · exact hβord.1 β0 h γ hγ
    · exact hγ
  have hagree : ∀ γ v' w', (γ ∈' β0) → Z.S.FunApp f γ v' → Z.S.FunApp g γ w' → v' = w' := by
    intro γ v' w' hγ hv' hw'
    by_contra hne'
    exact hmin γ hγ ⟨(hsβ γ).2 (Or.inl (hbelow γ hγ)), v', w', hv', hw', hne'⟩
  apply hne0
  rcases IsOrdinal.zero_or_succ_or_limit Z (IsVAttempt.ordinal Z hf hv0) with h0 | ⟨γ, hγ⟩ | hlim
  · exact Z.empty_unique (IsVAttempt.zero Z hf hv0 h0) (IsVAttempt.zero Z hg hw0 h0)
  · obtain ⟨u, hu, hpu⟩ := IsVAttempt.succ Z hf hv0 hγ
    obtain ⟨u', hu', hpu'⟩ := IsVAttempt.succ Z hg hw0 hγ
    have := hagree γ u u' (IsSucc.self_mem Z hγ) hu hu'
    subst this
    exact Z.ax.ext v0 w0 fun z => by rw [hpu z, hpu' z]
  · have hl := IsVAttempt.limit Z hf hv0 hlim
    have hl' := IsVAttempt.limit Z hg hw0 hlim
    apply Z.ax.ext v0 w0
    intro z
    rw [hl z, hl' z]
    constructor
    · rintro ⟨γ, u, hγ, hu, hz⟩
      obtain ⟨u', hu'⟩ := hgd γ (hbelow γ hγ)
      have := hagree γ u u' hγ hu hu'
      subst this
      exact ⟨γ, u, hγ, hu', hz⟩
    · rintro ⟨γ, u', hγ, hu', hz⟩
      obtain ⟨u, hu⟩ := hfd γ (hbelow γ hγ)
      have := hagree γ u u' hγ hu hu'
      subst this
      exact ⟨γ, u, hγ, hu, hz⟩

/-- Along an attempt defined below `α`, values at smaller ordinals are members
and subsets of the value at `α`. -/
theorem IsVAttempt.mono (hf : Z.S.IsVAttempt f) {α v β w : Z.S.X} (hd : ∀ γ, (γ ∈' α) ∨ γ = α → Z.S.InDom f γ)
    (hv : Z.S.FunApp f α v) (hβ : β ∈' α) (hw : Z.S.FunApp f β w) :
    (w ∈' v) ∧ Z.S.Subset w v := by
  obtain ⟨sα, hsα⟩ := Z.exists_succ α
  let Bad : Z.S.X → Prop := fun α' => (α' ∈' sα) ∧ ∃ v', Z.S.FunApp f α' v' ∧
    ∃ β' w', (β' ∈' α') ∧ Z.S.FunApp f β' w' ∧ ¬ ((w' ∈' v') ∧ Z.S.Subset w' v')
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    have hinner := Def.exists_ (Def.exists_ (Def.and_
      (Def.mem (Fin.castSucc (Fin.last 4)) (Fin.castSucc (Fin.castSucc (Fin.castSucc 0))))
      (Def.and_ (Def.funApp (Fin.castSucc (Fin.castSucc (Fin.castSucc 2)))
        (Fin.castSucc (Fin.last 4)) (Fin.last 5))
        (Def.not_ (Def.and_ (Def.mem (Fin.last 5) (Fin.castSucc (Fin.castSucc (Fin.last 3))))
          (Def.subset (Fin.last 5) (Fin.castSucc (Fin.castSucc (Fin.last 3))))))))) (𝒞 := Z.𝒞)
    have hmid := Def.exists_ (Def.and_
      (Def.funApp (Fin.castSucc 2) (Fin.castSucc 0) (Fin.last 3)) hinner)
    refine Def.congr ?_ (((Def.and_ (Def.mem (0 : Fin 3) 1) hmid).withParam f).withParam sα)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  have hαord : Z.S.IsOrdinal α := IsVAttempt.ordinal Z hf hv
  by_contra hne
  obtain ⟨α0, ⟨hα0s, v0, hv0, β0, w0, hβ0, hw0, hbad0⟩, hmin⟩ := Z.class_foundationP hdef sα
    (fun _ h => h.1) ⟨α, (IsSucc.self_mem Z hsα), v, hv, β, w, hβ, hw, hne⟩
  have hbelow : ∀ γ, (γ ∈' α0) → (γ ∈' α) ∨ γ = α := by
    intro γ hγ
    rcases (hsα α0).1 hα0s with h | rfl
    · exact Or.inl (hαord.1 α0 h γ hγ)
    · exact Or.inl hγ
  have hgood : ∀ γ v' β' w', (γ ∈' α0) → Z.S.FunApp f γ v' → (β' ∈' γ) → Z.S.FunApp f β' w' →
      (w' ∈' v') ∧ Z.S.Subset w' v' := by
    intro γ v' β' w' hγ hv' hβ' hw'
    by_contra hb
    refine hmin γ hγ ⟨?_, v', hv', β', w', hβ', hw', hb⟩
    rcases hbelow γ hγ with h | rfl
    · exact (hsα γ).2 (Or.inl h)
    · exact (IsSucc.self_mem Z hsα)
  apply hbad0
  have hα0ord := IsVAttempt.ordinal Z hf hv0
  rcases IsOrdinal.zero_or_succ_or_limit Z hα0ord with h0 | ⟨γ, hγ⟩ | hlim
  · exact (h0 β0 hβ0).elim
  · obtain ⟨u, hu, hpu⟩ := IsVAttempt.succ Z hf hv0 hγ
    have hut : Z.S.Transitive u := IsVAttempt.transitive Z hf hu
    rcases (hγ β0).1 hβ0 with hβ0γ | rfl
    · obtain ⟨h1, h2⟩ := hgood γ u β0 w0 (IsSucc.self_mem Z hγ) hu hβ0γ hw0
      exact ⟨(hpu w0).2 h2, fun z hz => (hpu z).2 (hut z (h2 z hz))⟩
    · have := Z.funApp_unique hf.1 hu hw0
      subst this
      exact ⟨(hpu u).2 fun z hz => hz, fun z hz => (hpu z).2 (hut z hz)⟩
  · have hl := IsVAttempt.limit Z hf hv0 hlim
    obtain ⟨s, hs⟩ := Z.exists_succ β0
    have hsα0 : s ∈' α0 := IsLimitOrd.succ_mem Z hlim hβ0 hs
    obtain ⟨u, hu⟩ := hd s (hbelow s hsα0)
    obtain ⟨w', hw', hpw⟩ := IsVAttempt.succ Z hf hu hs
    have := Z.funApp_unique hf.1 hw' hw0
    subst this
    refine ⟨(hl w').2 ⟨s, u, hsα0, hu, (hpw w').2 fun z hz => hz⟩, fun z hz => ?_⟩
    exact (hl z).2 ⟨β0, w', hβ0, hw0, hz⟩

/-- `α ∉ V_α`. -/
theorem IsVAttempt.not_mem_self (hf : Z.S.IsVAttempt f) {α v : Z.S.X} (hd : ∀ γ, (γ ∈' α) ∨ γ = α → Z.S.InDom f γ)
    (hv : Z.S.FunApp f α v) : ¬ (α ∈' v) := by
  obtain ⟨sα, hsα⟩ := Z.exists_succ α
  let Bad : Z.S.X → Prop := fun α' => (α' ∈' sα) ∧ ∃ v', Z.S.FunApp f α' v' ∧ (α' ∈' v')
  have hdef : Z.𝒞.Def 1 (fun t => Bad (t 0)) := by
    refine Def.congr ?_ (((Def.and_ (Def.mem 0 1) (Def.exists_ (Def.and_
      (Def.funApp (Fin.castSucc 2) (Fin.castSucc 0) (Fin.last 3))
      (Def.mem (Fin.castSucc 0) (Fin.last 3))))).withParam f).withParam sα)
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl
  have hαord : Z.S.IsOrdinal α := IsVAttempt.ordinal Z hf hv
  intro hmem
  obtain ⟨α0, ⟨hα0s, v0, hv0, hmem0⟩, hmin⟩ := Z.class_foundationP hdef sα
    (fun _ h => h.1) ⟨α, (IsSucc.self_mem Z hsα), v, hv, hmem⟩
  have hbelow : ∀ γ, (γ ∈' α0) → γ ∈' sα := by
    intro γ hγ
    rcases (hsα α0).1 hα0s with h | rfl
    · exact (hsα γ).2 (Or.inl (hαord.1 α0 h γ hγ))
    · exact (hsα γ).2 (Or.inl hγ)
  rcases IsOrdinal.zero_or_succ_or_limit Z (IsVAttempt.ordinal Z hf hv0) with h0 | ⟨γ, hγ⟩ | hlim
  · exact IsVAttempt.zero Z hf hv0 h0 α0 hmem0
  · obtain ⟨u, hu, hpu⟩ := IsVAttempt.succ Z hf hv0 hγ
    have : γ ∈' u := (hpu α0).1 hmem0 γ (IsSucc.self_mem Z hγ)
    exact hmin γ (IsSucc.self_mem Z hγ) ⟨hbelow γ (IsSucc.self_mem Z hγ), u, hu, this⟩
  · obtain ⟨γ, w, hγ, hw, hmemw⟩ := (IsVAttempt.limit Z hf hv0 hlim α0).1 hmem0
    have : γ ∈' w := IsVAttempt.transitive Z hf hw α0 hmemw γ hγ
    exact hmin γ hγ ⟨hbelow γ hγ, w, hw, this⟩

end Attempts

/-! ### Consequences for `V_α` -/

theorem IsV.unique {α v w : Z.S.X} (hv : Z.S.IsV α v) (hw : Z.S.IsV α w) : v = w := by
  obtain ⟨-, f, hf, hfd, hfv⟩ := hv
  obtain ⟨-, g, hg, hgd, hgw⟩ := hw
  exact Z.attempt_agree hf hg (fun γ hγ => hfd γ (Or.inl hγ)) (fun γ hγ => hgd γ (Or.inl hγ))
    hfv hgw

theorem IsV.transitive {α v : Z.S.X} (hv : Z.S.IsV α v) : Z.S.Transitive v := by
  obtain ⟨-, f, hf, -, hfv⟩ := hv
  exact IsVAttempt.transitive Z hf hfv

theorem IsV.subset_closed {α v z y : Z.S.X} (hv : Z.S.IsV α v) (hy : y ∈' v)
    (hzy : Z.S.Subset z y) : z ∈' v := by
  obtain ⟨-, f, hf, -, hfv⟩ := hv
  exact IsVAttempt.subset_closed Z hf hfv hy hzy

theorem IsV.not_mem_self {α v : Z.S.X} (hv : Z.S.IsV α v) : ¬ (α ∈' v) := by
  obtain ⟨-, f, hf, hfd, hfv⟩ := hv
  exact IsVAttempt.not_mem_self Z hf hfd hfv

/-- `V_β ∈ V_α` and `V_β ⊆ V_α` for `β ∈ α`. -/
theorem IsV.mono {α v β w : Z.S.X} (hv : Z.S.IsV α v) (hw : Z.S.IsV β w) (hβ : β ∈' α) :
    (w ∈' v) ∧ Z.S.Subset w v := by
  obtain ⟨-, f, hf, hfd, hfv⟩ := hv
  obtain ⟨hβord, g, hg, hgd, hgw⟩ := hw
  obtain ⟨w', hw'⟩ := hfd β (Or.inl hβ)
  have : w' = w := Z.attempt_agree hf hg
    (fun γ hγ => hfd γ (Or.inl ((IsVAttempt.ordinal Z hf hfv).1 β hβ γ hγ)))
    (fun γ hγ => hgd γ (Or.inl hγ)) hw' hgw
  subst this
  exact IsVAttempt.mono Z hf hfd hfv hβ hw'

end ZFCModel

end SolidLean.Solid
