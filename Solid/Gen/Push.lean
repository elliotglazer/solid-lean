module

public import Solid.Gen.Expansion
public import Solid.Gen.Clauses

/-!
# Pushing an interpretation along a coding of its ambient carrier

A *coding* of a sorted carrier `U` into a sorted carrier `V` sends each sort
`k` of `U` injectively into a sort `ρ k` of `V`.  An interpretation `I` of a
signature in `(U, 𝒟)` pushes forward along a coding to an interpretation
`I.push γ` in `(V, 𝒟')`, provided the class systems are compatible
(images of classes of a fixed sort profile are classes, and preimages of
classes are classes).  The pushed interpretation has an isomorphic model
(`pushIso`), and its induced class system contains the transport of the
induced system of `I`.

Two uses: a bijective coding (`Coding.ofEquiv`) transports interpretations
along an isomorphism of ambient structures; the coding of an expanded
structure into its base sorts (`SortExp.lean`) converts interpretations in a
structure with definable extra sorts into interpretations in its reduct.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-! ### Codings -/

/-- A coding of the sorted carrier `U` into `V`: sort `k` goes injectively to
sort `ρ k`. -/
structure Coding (U V : ℕ → Type u) where
  ρ : ℕ → ℕ
  c : ∀ k, U k → V (ρ k)
  inj : ∀ k, Function.Injective (c k)

namespace Coding

variable {U V : ℕ → Type u} (γ : Coding U V)

/-- The coding on the union of sorts. -/
def el (z : Sorted.El U) : Sorted.El V := ⟨γ.ρ z.1, γ.c z.1 z.2⟩

@[simp] theorem el_inj {k : ℕ} (x : U k) : γ.el (Sorted.inj U x) = Sorted.inj V (γ.c k x) := rfl

theorem el_fst (z : Sorted.El U) : (γ.el z).1 = γ.ρ z.1 := rfl

/-- Two elements of the same sort with the same code are equal. -/
theorem el_injective_of_sort {z z' : Sorted.El U} (hs : z.1 = z'.1) (h : γ.el z = γ.el z') : z = z' := by
  obtain ⟨k, x⟩ := z
  obtain ⟨k', x'⟩ := z'
  have hk : k = k' := hs
  subst hk
  have := (Sigma.mk.inj_iff.mp h).2
  exact Sigma.ext rfl (heq_of_eq (γ.inj k (eq_of_heq this)))

/-- The image of a relation. -/
def img {k : ℕ} (A : Sorted.Rel U k) : Sorted.Rel V k := {t | ∃ u ∈ A, t = fun i => γ.el (u i)}

/-- The preimage of a relation at a sort profile. -/
def pre {k : ℕ} (b : Fin k → ℕ) (B : Sorted.Rel V k) : Sorted.Rel U k :=
  {t | (∀ i, (t i).1 = b i) ∧ (fun i => γ.el (t i)) ∈ B}

theorem mem_img_iff {k : ℕ} (A : Sorted.Rel U k) (t : Fin k → Sorted.El V) :
    t ∈ γ.img A ↔ ∃ u ∈ A, t = fun i => γ.el (u i) := Iff.rfl

/-- A tuple of a fixed profile is determined by its coded tuple. -/
theorem eq_of_el_eq_profile {k : ℕ} {b : Fin k → ℕ} {u u' : Fin k → Sorted.El U}
    (hu : ∀ i, (u i).1 = b i) (hu' : ∀ i, (u' i).1 = b i)
    (h : (fun i => γ.el (u i)) = fun i => γ.el (u' i)) : u = u' := by
  funext i
  exact γ.el_injective_of_sort ((hu i).trans (hu' i).symm) (congrFun h i)

/-- Compatibility of class systems with a coding: images of classes of a fixed
profile are classes, preimages of classes are classes. -/
structure Compat (𝒟 : ClassSys U) (𝒟' : ClassSys V) : Prop where
  img_mem : ∀ {k} (A : Sorted.Rel U k) (b : Fin k → ℕ), A ∈ 𝒟.D k →
    (∀ t ∈ A, ∀ i, (t i).1 = b i) → γ.img A ∈ 𝒟'.D k
  pre_mem : ∀ {k} (B : Sorted.Rel V k) (b : Fin k → ℕ), B ∈ 𝒟'.D k → γ.pre b B ∈ 𝒟.D k

/-! #### Bijective codings -/

/-- The coding given by a family of equivalences (sort-preserving). -/
def ofEquiv (e : ∀ n, U n ≃ V n) : Coding U V where
  ρ := id
  c n := e n
  inj n := (e n).injective

theorem ofEquiv_el_surjective (e : ∀ n, U n ≃ V n) : Function.Surjective (ofEquiv e).el := by
  rintro ⟨n, y⟩
  exact ⟨⟨n, (e n).symm y⟩, by simp [el, ofEquiv]⟩

theorem ofEquiv_el_injective (e : ∀ n, U n ≃ V n) : Function.Injective (ofEquiv e).el := by
  rintro ⟨n, x⟩ ⟨m, y⟩ h
  have hnm : n = m := congrArg Sigma.fst h
  subst hnm
  have := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact Sigma.ext rfl (heq_of_eq ((e n).injective this))

/-- The class system carried along a bijective coding. -/
def mapSys (e : ∀ n, U n ≃ V n) (𝒟 : ClassSys U) : ClassSys V where
  D k := {B | {t | (fun i => (ofEquiv e).el (t i)) ∈ B} ∈ 𝒟.D k}
  eq_mem := by
    have : ({t | (fun i => (ofEquiv e).el (t i)) ∈ Sorted.eqRel V} : Sorted.Rel U 2) = Sorted.eqRel U := by
      ext t
      show (ofEquiv e).el (t 0) = (ofEquiv e).el (t 1) ↔ t 0 = t 1
      exact ⟨fun h => ofEquiv_el_injective e h, fun h => by rw [h]⟩
    show _ ∈ 𝒟.D 2
    rw [this]; exact 𝒟.eq_mem
  sort_mem n := by
    have : ({t | (fun i => (ofEquiv e).el (t i)) ∈ Sorted.sortRel V n} : Sorted.Rel U 1) =
        Sorted.sortRel U n := by
      ext t; exact Iff.rfl
    show _ ∈ 𝒟.D 1
    rw [this]; exact 𝒟.sort_mem n
  param_mem p := by
    obtain ⟨z, rfl⟩ := ofEquiv_el_surjective e p
    have : ({t | (fun i => (ofEquiv e).el (t i)) ∈ Sorted.paramRel V ((ofEquiv e).el z)} : Sorted.Rel U 1) =
        Sorted.paramRel U z := by
      ext t
      show (ofEquiv e).el (t 0) = (ofEquiv e).el z ↔ t 0 = z
      exact ⟨fun h => ofEquiv_el_injective e h, fun h => by rw [h]⟩
    show _ ∈ 𝒟.D 1
    rw [this]; exact 𝒟.param_mem z
  univ_mem k := by
    show {t : Fin k → Sorted.El U | _ ∈ (Set.univ : Sorted.Rel V k)} ∈ 𝒟.D k
    have : {t : Fin k → Sorted.El U | (fun i => (ofEquiv e).el (t i)) ∈ (Set.univ : Sorted.Rel V k)} =
        Set.univ := by ext t; simp
    rw [this]; exact 𝒟.univ_mem k
  inter_mem := by
    intro k B B' hB hB'
    exact 𝒟.inter_mem hB hB'
  compl_mem := by
    intro k B hB
    exact 𝒟.compl_mem hB
  reindex_mem := by
    intro k l f B hB
    exact 𝒟.reindex_mem f hB
  exists_mem := by
    intro n k B hB
    have : ({t | (fun i => (ofEquiv e).el (t i)) ∈ Sorted.exists_ V n B} : Sorted.Rel U k) =
        Sorted.exists_ U n {t | (fun i => (ofEquiv e).el (t i)) ∈ B} := by
      ext t
      show (∃ y : Sorted.El V, y.1 = n ∧ Fin.snoc (α := fun _ => Sorted.El V) (fun i => (ofEquiv e).el (t i)) y ∈ B) ↔
        ∃ x : Sorted.El U, x.1 = n ∧ (fun i => (ofEquiv e).el (Fin.snoc (α := fun _ => Sorted.El U) t x i)) ∈ B
      constructor
      · rintro ⟨y, hy, hB'⟩
        obtain ⟨x, rfl⟩ := ofEquiv_el_surjective e y
        refine ⟨x, hy, ?_⟩
        convert hB' using 1
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp
        · simp
      · rintro ⟨x, hx, hB'⟩
        refine ⟨(ofEquiv e).el x, hx, ?_⟩
        convert hB' using 1
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp
        · simp
    show _ ∈ 𝒟.D k
    rw [this]; exact 𝒟.exists_mem n hB

theorem mem_mapSys_iff (e : ∀ n, U n ≃ V n) (𝒟 : ClassSys U) {k : ℕ} (B : Sorted.Rel V k) :
    B ∈ (mapSys e 𝒟).D k ↔ {t | (fun i => (ofEquiv e).el (t i)) ∈ B} ∈ 𝒟.D k := Iff.rfl

/-- A bijective coding is compatible with the carried class system. -/
theorem compat_mapSys (e : ∀ n, U n ≃ V n) (𝒟 : ClassSys U) : (ofEquiv e).Compat 𝒟 (mapSys e 𝒟) where
  img_mem := by
    intro k A b hA _
    rw [mem_mapSys_iff]
    have : {t | (fun i => (ofEquiv e).el (t i)) ∈ (ofEquiv e).img A} = A := by
      ext t
      constructor
      · rintro ⟨u, hu, h⟩
        have : t = u := funext fun i => ofEquiv_el_injective e (congrFun h i)
        rw [this]; exact hu
      · intro ht; exact ⟨t, ht, rfl⟩
    rw [this]; exact hA
  pre_mem := by
    intro k B b hB
    have : (ofEquiv e).pre b B = Sorted.profileRel U b ∩ {t | (fun i => (ofEquiv e).el (t i)) ∈ B} := by
      ext t; exact Iff.rfl
    rw [this]
    exact 𝒟.inter_mem (𝒟.profileRel_mem b) hB

end Coding

/-! ### Pushing an interpretation along a coding -/

namespace GenInterp

variable {U V : ℕ → Type u} {𝒟 : ClassSys U} {𝒟' : ClassSys V} {Sig : Signature}
  (I : GenInterp U 𝒟 Sig) (γ : Coding U V) (hγ : γ.Compat 𝒟 𝒟')

/-- Tuples of `relC r` have the profile `I.a ∘ Sig.sortAt r`. -/
theorem relC_profile (r : Sig.Rel) (t : Fin (Sig.arity r) → Sorted.El U) (ht : t ∈ I.relC r) (i) :
    (t i).1 = I.a (Sig.sortAt r i) := by
  obtain ⟨x, hx, -⟩ := I.relC_dom r t ht i
  rw [hx]

/-- The pushed interpretation. -/
noncomputable def push : GenInterp V 𝒟' Sig where
  a n := γ.ρ (I.a n)
  dom n := γ.c (I.a n) '' I.dom n
  eqv n x y := ∃ x' y', γ.c (I.a n) x' = x ∧ γ.c (I.a n) y' = y ∧ I.eqv n x' y'
  eqv_refl := by
    rintro n x ⟨x', hx', rfl⟩
    exact ⟨x', x', rfl, rfl, I.eqv_refl n x' hx'⟩
  eqv_symm := by
    rintro n x y ⟨x', y', rfl, rfl, h⟩
    exact ⟨y', x', rfl, rfl, I.eqv_symm n x' y' h⟩
  eqv_trans := by
    rintro n x y z ⟨x', y', rfl, rfl, h⟩ ⟨y'', z', hy'', rfl, h'⟩
    have := γ.inj _ hy''
    subst this
    exact ⟨x', z', rfl, rfl, I.eqv_trans n x' y'' z' h h'⟩
  eqv_dom := by
    rintro n x y ⟨x', y', rfl, rfl, h⟩
    have hd := I.eqv_dom n x' y' h
    exact ⟨⟨x', hd.1, rfl⟩, ⟨y', hd.2, rfl⟩⟩
  dom_def := by
    intro n
    have : Sorted.SortClass V (γ.ρ (I.a n)) (γ.c (I.a n) '' I.dom n) =
        γ.img (Sorted.SortClass U (I.a n) (I.dom n)) := by
      ext t
      constructor
      · rintro ⟨y, hy, x, hx, rfl⟩
        refine ⟨fun _ => Sorted.inj U x, ⟨x, rfl, hx⟩, ?_⟩
        funext i
        have : i = 0 := Subsingleton.elim _ _
        subst this
        rw [hy]; rfl
      · rintro ⟨u, ⟨x, hu0, hx⟩, rfl⟩
        refine ⟨γ.c (I.a n) x, ?_, x, hx, rfl⟩
        show γ.el (u 0) = _
        rw [hu0]; rfl
    unfold ClassSys.DefinableSet
    rw [this]
    refine hγ.img_mem _ (fun _ => I.a n) (I.dom_def n) ?_
    rintro t ⟨x, hx, -⟩ i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    rw [hx]
  eqv_def := by
    intro n
    have : Sorted.liftRel V {s : Fin 2 → V (γ.ρ (I.a n)) |
        ∃ x' y', γ.c (I.a n) x' = s 0 ∧ γ.c (I.a n) y' = s 1 ∧ I.eqv n x' y'} =
        γ.img (Sorted.liftRel U {s : Fin 2 → U (I.a n) | I.eqv n (s 0) (s 1)}) := by
      ext t
      constructor
      · rintro ⟨s, hs, x', y', hx', hy', h⟩
        refine ⟨![Sorted.inj U x', Sorted.inj U y'], ⟨![x', y'], ?_, h⟩, ?_⟩
        · intro i
          match i with
          | 0 => rfl
          | 1 => rfl
        · funext i
          match i with
          | 0 =>
            show t 0 = γ.el (Sorted.inj U x')
            rw [hs 0, ← hx']; rfl
          | 1 =>
            show t 1 = γ.el (Sorted.inj U y')
            rw [hs 1, ← hy']; rfl
      · rintro ⟨u, ⟨s, hs, h⟩, rfl⟩
        refine ⟨fun i => γ.c (I.a n) (s i), fun i => ?_, s 0, s 1, rfl, rfl, h⟩
        show γ.el (u i) = _
        rw [hs i]; rfl
    unfold ClassSys.DefOn
    rw [this]
    refine hγ.img_mem _ (fun _ => I.a n) (I.eqv_def n) ?_
    rintro t ⟨s, hs, -⟩ i
    rw [hs i]
  relC r := γ.img (I.relC r)
  relC_dom := by
    rintro r t ⟨u, hu, rfl⟩ i
    obtain ⟨x, hx, hxd⟩ := I.relC_dom r u hu i
    refine ⟨γ.c _ x, ?_, x, hxd, rfl⟩
    show γ.el (u i) = _
    rw [hx]; rfl
  relC_congr := by
    rintro r t t' h ⟨u, hu, rfl⟩
    -- each coordinate of `t'` is the code of some `y'` equivalent to the coordinate of `u`
    have key : ∀ i, ∃ y' : U (I.a (Sig.sortAt r i)), t' i = Sorted.inj V (γ.c _ y') ∧
        ∃ x : U (I.a (Sig.sortAt r i)), u i = Sorted.inj U x ∧ I.eqv (Sig.sortAt r i) x y' := by
      intro i
      obtain ⟨x, x', hx, hx', x₀, y', hx₀, hy', he⟩ := h i
      obtain ⟨x₁, hx₁, -⟩ := I.relC_dom r u hu i
      have e1 : γ.el (u i) = Sorted.inj V x := hx
      rw [hx₁] at e1
      have e1' : γ.c _ x₁ = x := Sorted.inj_injective V e1
      rw [← e1'] at hx₀
      have e2 : x₀ = x₁ := γ.inj _ hx₀
      exact ⟨y', by rw [hx', hy'], x₁, hx₁, e2 ▸ he⟩
    choose y' hy' using key
    refine ⟨fun i => Sorted.inj U (y' i), ?_, ?_⟩
    · refine I.relC_congr r u _ (fun i => ?_) hu
      obtain ⟨x, hx, he⟩ := (hy' i).2
      exact ⟨x, y' i, hx, rfl, he⟩
    · funext i
      rw [(hy' i).1]; rfl
  relC_def := by
    intro r
    exact hγ.img_mem _ (fun i => I.a (Sig.sortAt r i)) (I.relC_def r) (fun t ht i => I.relC_profile r t ht i)

@[simp] theorem push_a (n : ℕ) : (I.push γ hγ).a n = γ.ρ (I.a n) := rfl

/-- The class of a domain element, pushed. -/
theorem push_dom_mem {n : ℕ} (x : I.Dom n) : γ.c (I.a n) x.1 ∈ (I.push γ hγ).dom n := ⟨x.1, x.2, rfl⟩

/-- A domain element of `I`, as a domain element of the pushed interpretation. -/
def pushDom {n : ℕ} (x : I.Dom n) : (I.push γ hγ).Dom n := ⟨γ.c (I.a n) x.1, I.push_dom_mem γ hγ x⟩

@[simp] theorem pushDom_val {n : ℕ} (x : I.Dom n) : (I.pushDom γ hγ x).1 = γ.c (I.a n) x.1 := rfl

/-- The map from the model of `I` to the model of the pushed interpretation. -/
noncomputable def pushMap (n : ℕ) : I.Carrier n → (I.push γ hγ).Carrier n :=
  Quotient.lift (fun x : I.Dom n => (I.push γ hγ).cls (I.pushDom γ hγ x))
    (by
      intro x y h
      apply Quotient.sound
      exact ⟨x.1, y.1, rfl, rfl, h⟩)

@[simp] theorem pushMap_cls {n : ℕ} (x : I.Dom n) :
    I.pushMap γ hγ n (I.cls x) = (I.push γ hγ).cls (I.pushDom γ hγ x) := rfl

/-- The map on the union of sorts. -/
noncomputable def pushEl (z : Sorted.El I.Carrier) : Sorted.El (I.push γ hγ).Carrier := ⟨z.1, I.pushMap γ hγ z.1 z.2⟩

@[simp] theorem pushEl_inj {n : ℕ} (q : I.Carrier n) :
    I.pushEl γ hγ (Sorted.inj I.Carrier q) = Sorted.inj (I.push γ hγ).Carrier (I.pushMap γ hγ n q) := rfl

theorem pushMap_injective (n : ℕ) : Function.Injective (I.pushMap γ hγ n) := by
  intro q q'
  induction q using Quotient.ind with
  | _ x =>
  induction q' using Quotient.ind with
  | _ y =>
  intro h
  obtain ⟨x', y', hx', hy', he⟩ := Quotient.exact h
  have ex := γ.inj _ hx'
  have ey := γ.inj _ hy'
  subst ex; subst ey
  exact Quotient.sound he

theorem pushMap_surjective (n : ℕ) : Function.Surjective (I.pushMap γ hγ n) := by
  intro q'
  induction q' using Quotient.ind with
  | _ v =>
  obtain ⟨x, hx, hv⟩ := v.2
  refine ⟨I.cls ⟨x, hx⟩, ?_⟩
  show (I.push γ hγ).cls (I.pushDom γ hγ ⟨x, hx⟩) = (I.push γ hγ).cls v
  congr 1
  exact Subtype.ext hv

/-- Representation in the pushed interpretation, for a source element of the
right sort. -/
theorem push_Rep_iff {y : Sorted.El U} {z : Sorted.El I.Carrier} (hy : y.1 = I.a z.1) :
    (I.push γ hγ).Rep (γ.el y) (I.pushEl γ hγ z) ↔ I.Rep y z := by
  constructor
  · rintro ⟨m, v, hyv, hzv⟩
    obtain ⟨m', q⟩ := z
    have hm : m' = m := congrArg Sigma.fst hzv
    subst hm
    have hq : I.pushMap γ hγ m' q = (I.push γ hγ).cls v := eq_of_heq (Sigma.mk.inj_iff.mp hzv).2
    obtain ⟨x₀, rfl⟩ := Quotient.exists_rep q
    have hq' : (I.push γ hγ).cls (I.pushDom γ hγ x₀) = (I.push γ hγ).cls v := hq
    obtain ⟨x', y', hx', hy', he⟩ := ((I.push γ hγ).cls_eq_iff _ _).1 hq'
    have ex : x' = x₀.1 := γ.inj _ hx'
    subst ex
    have hyy : y = Sorted.inj U y' := by
      refine γ.el_injective_of_sort ?_ ?_
      · exact hy
      · rw [hyv, ← hy']; rfl
    have hd := (I.eqv_dom _ _ _ he).2
    refine ⟨m', ⟨y', hd⟩, hyy, ?_⟩
    show Sorted.inj I.Carrier (I.cls x₀) = Sorted.inj I.Carrier (I.cls ⟨y', hd⟩)
    rw [I.model_inj_eq_iff, I.cls_eq_iff]
    exact he
  · rintro ⟨m, x, rfl, rfl⟩
    exact ⟨m, I.pushDom γ hγ x, rfl, rfl⟩

/-- Representation in the pushed interpretation, in general: the source element
is the code of a representative. -/
theorem push_Rep_iff' (y' : Sorted.El V) (q' : Sorted.El (I.push γ hγ).Carrier) :
    (I.push γ hγ).Rep y' q' ↔ ∃ (y : Sorted.El U) (z : Sorted.El I.Carrier),
      y.1 = I.a z.1 ∧ y' = γ.el y ∧ q' = I.pushEl γ hγ z ∧ I.Rep y z := by
  constructor
  · rintro ⟨n, x, rfl, rfl⟩
    obtain ⟨x₀, hx₀, hx⟩ := x.2
    refine ⟨Sorted.inj U x₀, Sorted.inj I.Carrier (n := n) (I.cls ⟨x₀, hx₀⟩), rfl, ?_, ?_,
      n, ⟨x₀, hx₀⟩, rfl, rfl⟩
    · exact congrArg (Sorted.inj V) hx.symm
    · show Sorted.inj (I.push γ hγ).Carrier ((I.push γ hγ).cls x) =
        Sorted.inj (I.push γ hγ).Carrier (I.pushMap γ hγ n (I.cls ⟨x₀, hx₀⟩))
      rw [I.pushMap_cls]
      have : x = I.pushDom γ hγ ⟨x₀, hx₀⟩ := Subtype.ext hx.symm
      rw [this]
  · rintro ⟨y, z, hy, rfl, rfl, hR⟩
    exact (I.push_Rep_iff γ hγ hy).2 hR

theorem pushEl_injective : Function.Injective (I.pushEl γ hγ) := by
  rintro ⟨n, q⟩ ⟨n', q'⟩ h
  have hn : n = n' := congrArg Sigma.fst h
  subst hn
  have hq : q = q' := I.pushMap_injective γ hγ n (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  rw [hq]

/-- The isomorphism from the model of `I` to the model of the pushed interpretation. -/
noncomputable def pushIso : GenIso I.model (I.push γ hγ).model where
  toFun := I.pushMap γ hγ
  bijective n := ⟨I.pushMap_injective γ hγ n, I.pushMap_surjective γ hγ n⟩
  rel_iff r q := by
    show q ∈ I.relQ r ↔ (fun i => I.pushEl γ hγ (q i)) ∈ (I.push γ hγ).relQ r
    constructor
    · rintro ⟨u, hu, hrel⟩
      refine ⟨fun i => γ.el (u i), fun i => ⟨(hu i).1, ?_⟩, u, hrel, rfl⟩
      refine (I.push_Rep_iff γ hγ ?_).2 (hu i).2
      rw [(hu i).1]
      exact I.relC_profile r u hrel i
    · rintro ⟨u', hu', u, hrel, rfl⟩
      refine ⟨u, fun i => ⟨(hu' i).1, ?_⟩, hrel⟩
      have h1 : (I.pushEl γ hγ (q i)).1 = Sig.sortAt r i := (hu' i).1
      refine (I.push_Rep_iff γ hγ ?_).1 (hu' i).2
      exact (I.relC_profile r u hrel i).trans (congrArg I.a h1.symm)

@[simp] theorem pushIso_toFun (n : ℕ) : (I.pushIso γ hγ).toFun n = I.pushMap γ hγ n := rfl

theorem pushIso_mapEl (z : Sorted.El I.Carrier) : (I.pushIso γ hγ).mapEl z = I.pushEl γ hγ z := rfl

/-- The pushed interpretation represents the code of a representative. -/
theorem push_pres_rep {n : ℕ} (x : U (I.a n)) (q : I.Carrier n) :
    (I.push γ hγ).pres.rep n (γ.c (I.a n) x) = some (I.pushMap γ hγ n q) ↔
      I.pres.rep n x = some q := by
  have h1 := (I.push γ hγ).Rep_inj_iff' (n := n) (γ.c (I.a n) x) (I.pushMap γ hγ n q)
  have h2 := I.Rep_inj_iff' (n := n) x q
  exact h1.symm.trans ((I.push_Rep_iff γ hγ (y := Sorted.inj U x) (z := Sorted.inj I.Carrier q) rfl).trans h2)

/-- The preimage under the pushed interpretation is the image of the preimage. -/
theorem push_preimage {k : ℕ} (b : Fin k → ℕ) (C' : Sorted.Rel (I.push γ hγ).Carrier k) :
    (I.push γ hγ).preimage b C' =
      γ.img (I.preimage b {q | (fun i => I.pushEl γ hγ (q i)) ∈ C'}) := by
  ext t
  constructor
  · rintro ⟨q', hq', hC⟩
    -- pull the classes back along the isomorphism
    have hsurj := (I.pushIso γ hγ).mapEl_surjective
    choose q hq using fun i => hsurj (q' i)
    have hq'eq : q' = fun i => I.pushEl γ hγ (q i) := by funext i; exact (hq i).symm
    -- representatives of the `q i`
    have key : ∀ i, ∃ x : I.Dom (b i), t i = Sorted.inj V (γ.c _ x.1) ∧
        q i = Sorted.inj I.Carrier (n := b i) (I.cls x) := by
      intro i
      have hs : (q i).1 = b i := by rw [← (hq' i).1, ← hq i]; rfl
      obtain ⟨v, hv, hqv⟩ := (I.push γ hγ).rep_of_sort (hq' i).1 (hq' i).2
      obtain ⟨x, hx, hxv⟩ := v.2
      -- the representative `x` of `t i` represents `q i`
      have hqv' : I.pushEl γ hγ (q i) = Sorted.inj (I.push γ hγ).Carrier ((I.push γ hγ).cls v) :=
        (hq i).trans hqv
      have hrep : (I.push γ hγ).Rep (γ.el (Sorted.inj U x)) (I.pushEl γ hγ (q i)) := by
        rw [hqv']
        refine ⟨b i, v, ?_, rfl⟩
        show Sorted.inj V (γ.c _ x) = Sorted.inj V v.1
        rw [hxv]
        rfl
      have hrep' := (I.push_Rep_iff γ hγ (by rw [hs])).1 hrep
      obtain ⟨x', hx', hqx'⟩ := I.rep_of_sort hs hrep'
      have : x'.1 = x := Sorted.inj_injective U hx'.symm
      refine ⟨⟨x, hx⟩, ?_, ?_⟩
      · rw [hv, ← hxv]
        rfl
      · rw [hqx']
        have e : x' = ⟨x, hx⟩ := Subtype.ext this
        rw [e]
    choose x hx using key
    refine ⟨fun i => Sorted.inj U (x i).1, ⟨q, fun i => ⟨?_, ?_⟩, ?_⟩, ?_⟩
    · rw [(hx i).2]
    · rw [(hx i).2]; exact ⟨b i, x i, rfl, rfl⟩
    · show (fun i => I.pushEl γ hγ (q i)) ∈ C'
      rw [← hq'eq]; exact hC
    · funext i; rw [(hx i).1]; rfl
  · rintro ⟨u, ⟨q, hq, hC⟩, rfl⟩
    refine ⟨fun i => I.pushEl γ hγ (q i), fun i => ⟨(hq i).1, ?_⟩, hC⟩
    refine (I.push_Rep_iff γ hγ ?_).2 (hq i).2
    obtain ⟨m, x, hux, hqx⟩ := (hq i).2
    rw [hux, hqx]

/-- Transport of the induced class system: a class of the pushed model whose
pull-back along the isomorphism is admissible for `I` is admissible for the
pushed interpretation. -/
theorem push_induced {k : ℕ} (C' : Sorted.Rel (I.push γ hγ).Carrier k)
    (h : {q | (fun i => I.pushEl γ hγ (q i)) ∈ C'} ∈ I.induced.D k) :
    C' ∈ (I.push γ hγ).induced.D k := by
  rw [(I.push γ hγ).mem_induced_iff]
  intro b
  rw [I.push_preimage]
  refine hγ.img_mem _ (fun i => I.a (b i)) ((I.mem_induced_iff _).1 h b) ?_
  rintro t ⟨q, hq, -⟩ i
  obtain ⟨m, x, hux, hqx⟩ := (hq i).2
  have hm : m = b i := by rw [← (hq i).1, hqx]
  subst hm
  rw [hux]

end GenInterp

/-! ### Definable isomorphisms, through representatives -/

namespace GenInterp

section DefinableIn

variable {M : Str.{u} Sig} {𝒟 : ClassSys M.U} (I : GenInterp M.U 𝒟 Sig)

/-- The graph of an isomorphism onto the interpreted structure, through
representatives: `t 1` represents the image of `t 0`. -/
def repGraph (h : GenIso M I.model) (n : ℕ) : Sorted.Rel M.U 2 :=
  {t | (t 0).1 = n ∧ (t 1).1 = I.a n ∧ I.Rep (t 1) (h.mapEl (t 0))}

theorem definableIn_pres_iff (h : GenIso M I.model) :
    h.DefinableIn 𝒟 I.pres ↔ ∀ n, I.repGraph h n ∈ 𝒟.D 2 := by
  unfold GenIso.DefinableIn
  refine forall_congr' fun n => ?_
  have e : ∀ t : Fin 2 → Sorted.El M.U, (∃ (x : M.U n) (y : M.U (I.a n)),
      t 0 = Sorted.inj M.U x ∧ t 1 = Sorted.inj M.U y ∧ I.pres.rep n y = some (h.toFun n x)) ↔
        t ∈ I.repGraph h n := by
    intro t
    constructor
    · rintro ⟨x, y, h0, h1, hr⟩
      refine ⟨by rw [h0], by rw [h1], ?_⟩
      rw [h0, h1]
      exact (I.Rep_inj_iff' y (h.toFun n x)).2 hr
    · rintro ⟨h0, h1, hr⟩
      have e0 := Sorted.inj_toSort M.U (t 0) h0
      have e1 := Sorted.inj_toSort M.U (t 1) h1
      refine ⟨Sorted.toSort M.U (t 0) h0, Sorted.toSort M.U (t 1) h1, e0.symm, e1.symm, ?_⟩
      refine (I.Rep_inj_iff' _ _).1 ?_
      show I.Rep (Sorted.inj M.U (Sorted.toSort M.U (t 1) h1)) (h.mapEl (Sorted.inj M.U (Sorted.toSort M.U (t 0) h0)))
      rw [e0, e1]
      exact hr
  exact Iff.of_eq (congrArg (· ∈ 𝒟.D 2) (Set.ext e))

/-- The graph of an isomorphism onto a doubly interpreted structure, through
representatives: `t 1` represents (in `I`) a representative (in `J`) of the
image of `t 0`. -/
def repGraph₂ {𝒩 : ClassSys I.Carrier} (J : GenInterp I.Carrier 𝒩 Sig) (i : GenIso M J.model) (n : ℕ) :
    Sorted.Rel M.U 2 :=
  {t | (t 0).1 = n ∧ (t 1).1 = I.a (J.a n) ∧
    ∃ q : Sorted.El I.Carrier, q.1 = J.a n ∧ I.Rep (t 1) q ∧ J.Rep q (i.mapEl (t 0))}

theorem definableIn_comp_iff {𝒩 : ClassSys I.Carrier} (J : GenInterp I.Carrier 𝒩 Sig) (i : GenIso M J.model) :
    i.DefinableIn 𝒟 (I.pres.comp J.pres) ↔ ∀ n, I.repGraph₂ J i n ∈ 𝒟.D 2 := by
  unfold GenIso.DefinableIn
  refine forall_congr' fun n => ?_
  have e : ∀ t : Fin 2 → Sorted.El M.U, (∃ (x : M.U n) (y : M.U (I.a (J.a n))),
      t 0 = Sorted.inj M.U x ∧ t 1 = Sorted.inj M.U y ∧
        (I.pres.rep (J.a n) y).bind (J.pres.rep n) = some (i.toFun n x)) ↔ t ∈ I.repGraph₂ J i n := by
    intro t
    constructor
    · rintro ⟨x, y, h0, h1, hr⟩
      obtain ⟨q, hq1, hq2⟩ := Option.bind_eq_some_iff.1 hr
      refine ⟨by rw [h0], by rw [h1], Sorted.inj I.Carrier q, rfl, ?_, ?_⟩
      · rw [h1]; exact (I.Rep_inj_iff' y q).2 hq1
      · rw [h0]; exact (J.Rep_inj_iff' q (i.toFun n x)).2 hq2
    · rintro ⟨h0, h1, q, hq, hr1, hr2⟩
      have e0 := Sorted.inj_toSort M.U (t 0) h0
      have e1 := Sorted.inj_toSort M.U (t 1) h1
      refine ⟨Sorted.toSort M.U (t 0) h0, Sorted.toSort M.U (t 1) h1, e0.symm, e1.symm, ?_⟩
      obtain ⟨m, q₀⟩ := q
      have hm : m = J.a n := hq
      subst hm
      refine Option.bind_eq_some_iff.2 ⟨q₀, (I.Rep_inj_iff' _ _).1 ?_, (J.Rep_inj_iff' _ _).1 ?_⟩
      · rw [e1]; exact hr1
      · show J.Rep (Sorted.inj I.Carrier q₀) (i.mapEl (Sorted.inj M.U (Sorted.toSort M.U (t 0) h0)))
        rw [e0]; exact hr2
  exact Iff.of_eq (congrArg (· ∈ 𝒟.D 2) (Set.ext e))

end DefinableIn

end GenInterp

/-! ### Transport along isomorphisms of structures -/

namespace GenIso

variable {Sig : Signature} {M N P : Str.{u} Sig}

/-- Composition of isomorphisms. -/
def trans (i : GenIso M N) (j : GenIso N P) : GenIso M P where
  toFun n := j.toFun n ∘ i.toFun n
  bijective n := (j.bijective n).comp (i.bijective n)
  rel_iff r t := (i.rel_iff r t).trans (j.rel_iff r _)

@[simp] theorem trans_toFun (i : GenIso M N) (j : GenIso N P) (n : ℕ) (x : M.U n) :
    (i.trans j).toFun n x = j.toFun n (i.toFun n x) := rfl

theorem trans_mapEl (i : GenIso M N) (j : GenIso N P) (z : Sorted.El M.U) :
    (i.trans j).mapEl z = j.mapEl (i.mapEl z) := rfl

/-- The sortwise equivalences of an isomorphism. -/
noncomputable def equivs (i : GenIso M N) (n : ℕ) : M.U n ≃ N.U n :=
  Equiv.ofBijective (i.toFun n) (i.bijective n)

@[simp] theorem equivs_apply (i : GenIso M N) (n : ℕ) (x : M.U n) : i.equivs n x = i.toFun n x := rfl

theorem ofEquiv_equivs_el (i : GenIso M N) (z : Sorted.El M.U) :
    (Coding.ofEquiv i.equivs).el z = i.mapEl z := rfl

/-- The class system transported along an isomorphism. -/
noncomputable def mapSys (i : GenIso M N) (𝒟 : StrSys M) : StrSys N where
  toClassSys := Coding.mapSys i.equivs 𝒟.toClassSys
  rel_mem r := by
    show {t | (fun k => (Coding.ofEquiv i.equivs).el (t k)) ∈ N.rel r} ∈ 𝒟.D _
    have : {t | (fun k => (Coding.ofEquiv i.equivs).el (t k)) ∈ N.rel r} = M.rel r := by
      ext t; exact (i.rel_iff r t).symm
    rw [this]; exact 𝒟.rel_mem r

theorem mem_mapSys_iff (i : GenIso M N) (𝒟 : StrSys M) {k : ℕ} (C : Sorted.Rel N.U k) :
    C ∈ (i.mapSys 𝒟).D k ↔ {t | (fun j => i.mapEl (t j)) ∈ C} ∈ 𝒟.D k := Iff.rfl

end GenIso

namespace ClauseFamily

variable {F : ClauseFamily.{u}} {M N : Str.{u} F.sig}

theorem IsWF.transport (i : GenIso M N) (h : IsWF M) : IsWF N where
  liftZ_total n y := by
    obtain ⟨x, rfl⟩ := (i.bijective n).2 y
    obtain ⟨x', hx'⟩ := h.liftZ_total n x
    refine ⟨i.toFun (n + 1) x', ?_⟩
    have := (i.rel_iff' _ _).1 hx'
    rw [map_vec_two] at this
    exact this
  liftZ_unique n y z z' hz hz' := by
    obtain ⟨x, rfl⟩ := (i.bijective n).2 y
    obtain ⟨x₁, rfl⟩ := (i.bijective (n + 1)).2 z
    obtain ⟨x₂, rfl⟩ := (i.bijective (n + 1)).2 z'
    have h1 : ![Sorted.inj M.U x, Sorted.inj M.U x₁] ∈ M.rel (.inl (.liftZ n)) := by
      rw [i.rel_iff', map_vec_two]; exact hz
    have h2 : ![Sorted.inj M.U x, Sorted.inj M.U x₂] ∈ M.rel (.inl (.liftZ n)) := by
      rw [i.rel_iff', map_vec_two]; exact hz'
    rw [h.liftZ_unique n x x₁ x₂ h1 h2]
  bnd_exists n := by
    obtain ⟨y, hy⟩ := h.bnd_exists n
    refine ⟨i.toFun (n + 1) y, ?_⟩
    have := (i.rel_iff' _ _).1 hy
    rw [map_vec_one] at this
    exact this
  bnd_unique n z z' hz hz' := by
    obtain ⟨x₁, rfl⟩ := (i.bijective (n + 1)).2 z
    obtain ⟨x₂, rfl⟩ := (i.bijective (n + 1)).2 z'
    have h1 : ![Sorted.inj M.U x₁] ∈ M.rel (.inl (.bnd n)) := by
      rw [i.rel_iff', map_vec_one]; exact hz
    have h2 : ![Sorted.inj M.U x₂] ∈ M.rel (.inl (.bnd n)) := by
      rw [i.rel_iff', map_vec_one]; exact hz'
    rw [h.bnd_unique n x₁ x₂ h1 h2]

/-- Models of `T(𝔉)` transport along isomorphisms, with the transported class
system. -/
theorem IsGenModel.transport (i : GenIso M N) {𝒟 : StrSys M} (h : IsGenModel ⟨M, 𝒟⟩) :
    IsGenModel ⟨N, i.mapSys 𝒟⟩ where
  wf := h.wf.transport i
  tower := by
    refine IsTowerModel.congr_sys ?_ (IsTowerModel.transport (i.toTowerIso h.wf (h.wf.transport i)) h.tower)
    exact ClassSystem.ext fun k => by ext C; exact Iff.rfl
  clause f := by
    ext t
    obtain ⟨s, rfl⟩ : ∃ s : Fin (F.arity f) → Sorted.El M.U, t = fun j => i.mapEl (s j) := by
      have := i.mapEl_surjective
      choose s hs using fun j => this (t j)
      exact ⟨s, funext fun j => (hs j).symm⟩
    rw [← i.rel_iff' (.inr f) s, h.clause f]
    exact F.G_iso f (i.toTowerIso h.wf (h.wf.transport i)) s

end ClauseFamily

end SolidLean.Solid
