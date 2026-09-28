import Solid.SetTheory

/-!
# Internal set theory over a `ZFCModel`

The lemmas of ordinary set theory that the tower proof needs, proved from
`SetAxioms` with Separation and Replacement taken only for classes of the
model's class system.  Every use of Separation therefore comes with a
definability proof, built from the closure properties of `SetClassSystem`.

This file covers: definability helpers, basic set existence (intersection,
difference, singletons, ordered pairs), foundation for definable classes,
and the first facts about ordinals.  Transfinite recursion, the rank
hierarchy, Mostowski collapse and Cantor follow in later files.
-/

universe u

namespace SolidLean.Solid

namespace SetClassSystem

variable {S : MemStr.{u}} (𝒞 : SetClassSystem S)

theorem union_mem {k : ℕ} {C C' : S.Rel k} (h : C ∈ 𝒞.D k) (h' : C' ∈ 𝒞.D k) :
    C ∪ C' ∈ 𝒞.D k := by
  have : C ∪ C' = (Cᶜ ∩ C'ᶜ)ᶜ := by rw [Set.compl_inter, compl_compl, compl_compl]
  rw [this]
  exact 𝒞.compl_mem (𝒞.inter_mem (𝒞.compl_mem h) (𝒞.compl_mem h'))

theorem empty_mem (k : ℕ) : (∅ : S.Rel k) ∈ 𝒞.D k := by
  have : (∅ : S.Rel k) = (Set.univ)ᶜ := by simp
  rw [this]; exact 𝒞.compl_mem (𝒞.univ_mem k)

/-- The unary class `{y | y ∈ p}` for a parameter `p`. -/
theorem memParam_mem (p : S.X) : ({t | S.mem (t 0) p} : S.Rel 1) ∈ 𝒞.D 1 := by
  have : ({t | S.mem (t 0) p} : S.Rel 1) =
      {t | ∃ x, Fin.snoc t x ∈
        (({t | S.mem (t 0) (t 1)} : S.Rel 2) ∩ {t | (t ∘ fun _ : Fin 1 => (1 : Fin 2)) ∈
          ({t | t 0 = p} : S.Rel 1)})} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Function.comp_apply]
    constructor
    · intro h; exact ⟨p, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  rw [this]
  exact 𝒞.exists_mem (𝒞.inter_mem 𝒞.memRel_mem (𝒞.reindex_mem _ (𝒞.param_mem p)))

/-- The unary class `{y | p ∈ y}` for a parameter `p`. -/
theorem paramMem_mem (p : S.X) : ({t | S.mem p (t 0)} : S.Rel 1) ∈ 𝒞.D 1 := by
  have : ({t | S.mem p (t 0)} : S.Rel 1) =
      {t | ∃ x, Fin.snoc t x ∈
        (({t | S.mem (t 1) (t 0)} : S.Rel 2) ∩ {t | (t ∘ fun _ : Fin 1 => (1 : Fin 2)) ∈
          ({t | t 0 = p} : S.Rel 1)})} := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Function.comp_apply]
    constructor
    · intro h; exact ⟨p, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact hx
  rw [this]
  refine 𝒞.exists_mem (𝒞.inter_mem ?_ (𝒞.reindex_mem _ (𝒞.param_mem p)))
  have : ({t | S.mem (t 1) (t 0)} : S.Rel 2) =
      {t | (t ∘ ![1, 0]) ∈ ({t | S.mem (t 0) (t 1)} : S.Rel 2)} := by
    ext t; simp [Function.comp]
  rw [this]
  exact 𝒞.reindex_mem _ 𝒞.memRel_mem

end SetClassSystem

namespace ZFCModel

variable (Z : ZFCModel.{u})

local notation:50 x " ∈' " y => Z.S.mem x y

/-! ### Basic set existence -/

/-- Separation with no parameters, for a definable unary class. -/
theorem sep {C : Z.S.Rel 1} (hC : C ∈ Z.𝒞.D 1) (x : Z.S.X) :
    ∃ s, ∀ y, (y ∈' s) ↔ (y ∈' x) ∧ ![y] ∈ C := by
  have := Z.ax.separation (k := 0) C hC (fun i => i.elim0) x
  obtain ⟨s, hs⟩ := this
  refine ⟨s, fun y => ?_⟩
  rw [hs y]
  have : (Fin.snoc (fun i : Fin 0 => i.elim0) y : Fin 1 → Z.S.X) = ![y] := by
    funext i
    exact Fin.cases rfl (fun i => i.elim0) i
  rw [this]

theorem exists_inter (x p : Z.S.X) : ∃ s, ∀ y, (y ∈' s) ↔ (y ∈' x) ∧ (y ∈' p) := by
  obtain ⟨s, hs⟩ := Z.sep (Z.𝒞.memParam_mem p) x
  exact ⟨s, fun y => by rw [hs y]; rfl⟩

theorem exists_diff (x p : Z.S.X) : ∃ s, ∀ y, (y ∈' s) ↔ (y ∈' x) ∧ ¬ (y ∈' p) := by
  obtain ⟨s, hs⟩ := Z.sep (Z.𝒞.compl_mem (Z.𝒞.memParam_mem p)) x
  exact ⟨s, fun y => by rw [hs y]; rfl⟩

theorem exists_singleton (a : Z.S.X) : ∃ s, Z.S.IsSingleton a s := by
  obtain ⟨p, hp⟩ := Z.ax.pair a a
  refine ⟨p, fun z => ?_⟩
  rw [hp z]; simp

theorem exists_ordPair (a b : Z.S.X) : ∃ p, Z.S.IsOrdPair a b p := by
  obtain ⟨s, hs⟩ := Z.exists_singleton a
  obtain ⟨d, hd⟩ := Z.ax.pair a b
  obtain ⟨p, hp⟩ := Z.ax.pair s d
  exact ⟨p, s, d, hs, hd, hp⟩

theorem empty_unique {e e' : Z.S.X} (he : Z.S.IsEmptySet e) (he' : Z.S.IsEmptySet e') : e = e' :=
  Z.ax.ext e e' fun z => ⟨fun h => (he z h).elim, fun h => (he' z h).elim⟩

/-! ### Foundation for definable classes -/

/-- A nonempty definable class contained in the members of a set has a
membership-minimal element. -/
theorem class_foundation {C : Z.S.Rel 1} (hC : C ∈ Z.𝒞.D 1) (x : Z.S.X)
    (hsub : ∀ y, ![y] ∈ C → y ∈' x) (hne : ∃ y, ![y] ∈ C) :
    ∃ y, ![y] ∈ C ∧ ∀ z, (z ∈' y) → ![z] ∉ C := by
  obtain ⟨s, hs⟩ := Z.sep hC x
  obtain ⟨y0, hy0⟩ := hne
  have hne' : Z.S.Nonempty s := ⟨y0, (hs y0).2 ⟨hsub y0 hy0, hy0⟩⟩
  obtain ⟨y, hy, hmin⟩ := Z.ax.foundation s hne'
  refine ⟨y, ((hs y).1 hy).2, fun z hz hzC => ?_⟩
  exact hmin z hz ((hs z).2 ⟨hsub z hzC, hzC⟩)

/-- No set is a member of itself. -/
theorem mem_irrefl (x : Z.S.X) : ¬ (x ∈' x) := by
  intro hx
  obtain ⟨s, hs⟩ := Z.exists_singleton x
  obtain ⟨y, hy, hmin⟩ := Z.ax.foundation s ⟨x, (hs x).2 rfl⟩
  have : y = x := (hs y).1 hy
  subst this
  exact hmin y hx ((hs y).2 rfl)

/-- Membership is asymmetric. -/
theorem mem_asymm {x y : Z.S.X} (hxy : x ∈' y) (hyx : y ∈' x) : False := by
  obtain ⟨p, hp⟩ := Z.ax.pair x y
  obtain ⟨m, hm, hmin⟩ := Z.ax.foundation p ⟨x, (hp x).2 (Or.inl rfl)⟩
  rcases (hp m).1 hm with rfl | rfl
  · exact hmin y hyx ((hp y).2 (Or.inr rfl))
  · exact hmin x hxy ((hp x).2 (Or.inl rfl))

/-! ### Ordinals -/

/-- Members of ordinals are ordinals. -/
theorem IsOrdinal.mem {α β : Z.S.X} (hα : Z.S.IsOrdinal α) (hβ : β ∈' α) :
    Z.S.IsOrdinal β := by
  obtain ⟨htrans, hmemtrans, hlin⟩ := hα
  refine ⟨hmemtrans β hβ, fun y hy => hmemtrans y (htrans β hβ y hy), fun y z hy hz => ?_⟩
  exact hlin y z (htrans β hβ y hy) (htrans β hβ z hz)

/-- An ordinal is not a member of itself; two ordinals are not members of
each other. -/
theorem IsOrdinal.not_mem_self {α : Z.S.X} (_ : Z.S.IsOrdinal α) : ¬ (α ∈' α) :=
  Z.mem_irrefl α

/-- The successor of a set exists. -/
theorem exists_succ (x : Z.S.X) : ∃ s, Z.S.IsSucc x s := by
  obtain ⟨sx, hsx⟩ := Z.exists_singleton x
  obtain ⟨p, hp⟩ := Z.ax.pair x sx
  obtain ⟨u, hu⟩ := Z.ax.union p
  refine ⟨u, fun z => ?_⟩
  rw [hu z]
  constructor
  · rintro ⟨y, hy, hz⟩
    rcases (hp y).1 hy with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr ((hsx z).1 hz)
  · rintro (hz | rfl)
    · exact ⟨x, (hp x).2 (Or.inl rfl), hz⟩
    · exact ⟨sx, (hp sx).2 (Or.inr rfl), (hsx z).2 rfl⟩

/-- A proper transitive subset of an ordinal that is itself an ordinal is a
member of it: the least element of the difference is the subset. -/
theorem IsOrdinal.mem_of_ssubset {α β : Z.S.X} (hα : Z.S.IsOrdinal α) (hβ : Z.S.IsOrdinal β)
    (hsub : Z.S.Subset α β) (hne : α ≠ β) : α ∈' β := by
  obtain ⟨d, hd⟩ := Z.exists_diff β α
  have hdne : Z.S.Nonempty d := by
    by_contra h
    apply hne
    apply Z.ax.ext
    intro z
    refine ⟨fun hz => hsub z hz, fun hz => ?_⟩
    by_contra hza
    exact h ⟨z, (hd z).2 ⟨hz, hza⟩⟩
  obtain ⟨γ, hγ, hmin⟩ := Z.ax.foundation d hdne
  obtain ⟨hγβ, hγα⟩ := (hd γ).1 hγ
  have : γ = α := by
    apply Z.ax.ext
    intro δ
    constructor
    · intro hδ
      have hδβ : δ ∈' β := hβ.1 γ hγβ δ hδ
      by_contra hδα
      exact hmin δ hδ ((hd δ).2 ⟨hδβ, hδα⟩)
    · intro hδ
      have hδβ : δ ∈' β := hsub δ hδ
      rcases hβ.2.2 δ γ hδβ hγβ with h | rfl | h
      · exact h
      · exact (hγα hδ).elim
      · exact (hγα (hα.1 δ hδ γ h)).elim
  subst this
  exact hγβ

/-- The intersection of two ordinals is an ordinal contained in both. -/
theorem IsOrdinal.exists_inter {α β : Z.S.X} (hα : Z.S.IsOrdinal α) (hβ : Z.S.IsOrdinal β) :
    ∃ γ, Z.S.IsOrdinal γ ∧ (∀ z, (z ∈' γ) ↔ (z ∈' α) ∧ (z ∈' β)) := by
  obtain ⟨γ, hγ⟩ := Z.exists_inter α β
  refine ⟨γ, ⟨?_, ?_, ?_⟩, hγ⟩
  · intro y hy z hz
    obtain ⟨hyα, hyβ⟩ := (hγ y).1 hy
    exact (hγ z).2 ⟨hα.1 y hyα z hz, hβ.1 y hyβ z hz⟩
  · intro y hy
    exact hα.2.1 y ((hγ y).1 hy).1
  · intro y z hy hz
    exact hα.2.2 y z ((hγ y).1 hy).1 ((hγ z).1 hz).1

/-- Trichotomy of ordinals. -/
theorem IsOrdinal.trichotomy {α β : Z.S.X} (hα : Z.S.IsOrdinal α) (hβ : Z.S.IsOrdinal β) :
    (α ∈' β) ∨ α = β ∨ (β ∈' α) := by
  obtain ⟨γ, hγ, hmem⟩ := IsOrdinal.exists_inter Z hα hβ
  have hγα : Z.S.Subset γ α := fun z hz => ((hmem z).1 hz).1
  have hγβ : Z.S.Subset γ β := fun z hz => ((hmem z).1 hz).2
  by_cases h1 : γ = α
  · by_cases h2 : γ = β
    · exact Or.inr (Or.inl (h1.symm.trans h2))
    · subst h1
      exact Or.inl (IsOrdinal.mem_of_ssubset Z hγ hβ hγβ h2)
  · by_cases h2 : γ = β
    · subst h2
      exact Or.inr (Or.inr (IsOrdinal.mem_of_ssubset Z hγ hα hγα h1))
    · exfalso
      have hγα' := IsOrdinal.mem_of_ssubset Z hγ hα hγα h1
      have hγβ' := IsOrdinal.mem_of_ssubset Z hγ hβ hγβ h2
      exact Z.mem_irrefl γ ((hmem γ).2 ⟨hγα', hγβ'⟩)

end ZFCModel

end SolidLean.Solid
