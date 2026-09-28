import Solid.Tower

/-!
# Sort-level interpretations and the induced class system

The part of a one-coordinate interpretation that does not depend on the
target signature: each interpreted sort is a definable class of one source
sort modulo a definable equivalence.  The interpreted carriers are the
quotients; the *induced class system* on them consists of the relations
whose preimages under representation are admissible in the source.  This
is the generic core shared by interpretations of the tower signature
(`SInterp`) and of arbitrary relational signatures (`GenInterp`).
-/

universe u

namespace SolidLean.Solid

open Classical

/-- The sort-level data of a one-coordinate interpretation in a sorted
carrier with a class system. -/
structure SortInterp (U : ℕ → Type u) (𝒟 : ClassSys U) where
  a : ℕ → ℕ
  dom : ∀ n, Set (U (a n))
  eqv : ∀ n, U (a n) → U (a n) → Prop
  eqv_refl : ∀ n x, x ∈ dom n → eqv n x x
  eqv_symm : ∀ n x y, eqv n x y → eqv n y x
  eqv_trans : ∀ n x y z, eqv n x y → eqv n y z → eqv n x z
  eqv_dom : ∀ n x y, eqv n x y → x ∈ dom n ∧ y ∈ dom n
  dom_def : ∀ n, 𝒟.DefinableSet (a n) (dom n)
  eqv_def : ∀ n, 𝒟.DefOn (a n) 2 {t | eqv n (t 0) (t 1)}

namespace SortInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} (I : SortInterp U 𝒟)

/-- The domain of sort `n` as a subtype. -/
abbrev Dom (n : ℕ) : Type u := {x : U (I.a n) // x ∈ I.dom n}

/-- The equivalence on the domain of sort `n`. -/
def setoid (n : ℕ) : Setoid (I.Dom n) where
  r x y := I.eqv n x.1 y.1
  iseqv := ⟨fun x => I.eqv_refl n x.1 x.2, fun h => I.eqv_symm _ _ _ h,
    fun h h' => I.eqv_trans _ _ _ _ h h'⟩

/-- The carrier of interpreted sort `n`. -/
abbrev Carrier (n : ℕ) : Type u := Quotient (I.setoid n)

/-- The class of a domain element. -/
def cls {n : ℕ} (x : I.Dom n) : I.Carrier n := Quotient.mk (I.setoid n) x

theorem cls_eq_iff {n : ℕ} (x y : I.Dom n) : I.cls x = I.cls y ↔ I.eqv n x.1 y.1 :=
  Quotient.eq (r := I.setoid n)

/-- The representation relation between elements of the source and elements
of the interpreted structure: `y` represents `z` when `y` is a domain element
whose class is `z`. -/
def Rep (y : Sorted.El U) (z : Sorted.El I.Carrier) : Prop :=
  ∃ (n : ℕ) (x : I.Dom n), y = Sorted.inj U x.1 ∧ z = Sorted.inj I.Carrier (n := n) (I.cls x)

/-- The preimage of a relation on the interpreted structure under representation,
for a fixed profile `b` of interpreted sorts. -/
def preimage {k : ℕ} (b : Fin k → ℕ) (C : Sorted.Rel I.Carrier k) : Sorted.Rel U k :=
  {t | ∃ u : Fin k → Sorted.El I.Carrier, (∀ i, (u i).1 = b i ∧ I.Rep (t i) (u i)) ∧ u ∈ C}

/-- Tuples of representatives for the profile `b`. -/
def profile {k : ℕ} (b : Fin k → ℕ) : Sorted.Rel U k :=
  {t | ∀ i, ∃ z : Sorted.El I.Carrier, z.1 = b i ∧ I.Rep (t i) z}

/-- Admissible relations of the interpreted structure: those whose preimages are
admissible in the source, for every profile of sorts. -/
def inducedD (k : ℕ) : Set (Sorted.Rel I.Carrier k) :=
  {C | ∀ b : Fin k → ℕ, I.preimage b C ∈ 𝒟.D k}

/-- A source element represents at most one interpreted element of a given
sort. -/
theorem Rep_unique {y : Sorted.El U} {z z' : Sorted.El I.Carrier} (hz : I.Rep y z) (hz' : I.Rep y z')
    (hs : z.1 = z'.1) : z = z' := by
  obtain ⟨n, x, rfl, rfl⟩ := hz
  obtain ⟨n', x', hy, rfl⟩ := hz'
  have hn : n = n' := hs
  subst hn
  have hx : x.1 = x'.1 := Sorted.inj_injective U hy
  have : x = x' := Subtype.ext hx
  subst this
  rfl

/-- The representative tuple of a preimage element is unique. -/
theorem preimage_tuple_unique {k : ℕ} {b : Fin k → ℕ} {t : Fin k → Sorted.El U}
    {u u' : Fin k → Sorted.El I.Carrier}
    (hu : ∀ i, (u i).1 = b i ∧ I.Rep (t i) (u i))
    (hu' : ∀ i, (u' i).1 = b i ∧ I.Rep (t i) (u' i)) : u = u' := by
  funext i
  exact I.Rep_unique (hu i).2 (hu' i).2 (by rw [(hu i).1, (hu' i).1])

theorem preimage_univ {k : ℕ} (b : Fin k → ℕ) :
    I.preimage b (Set.univ : Sorted.Rel I.Carrier k) = I.profile b := by
  ext t
  constructor
  · rintro ⟨u, hu, -⟩ i
    exact ⟨u i, (hu i).1, (hu i).2⟩
  · intro ht
    choose u hu using ht
    exact ⟨u, hu, Set.mem_univ _⟩

theorem preimage_inter {k : ℕ} (b : Fin k → ℕ) (C C' : Sorted.Rel I.Carrier k) :
    I.preimage b (C ∩ C') = I.preimage b C ∩ I.preimage b C' := by
  ext t
  constructor
  · rintro ⟨u, hu, hC, hC'⟩
    exact ⟨⟨u, hu, hC⟩, ⟨u, hu, hC'⟩⟩
  · rintro ⟨⟨u, hu, hC⟩, ⟨u', hu', hC'⟩⟩
    have := I.preimage_tuple_unique hu hu'
    subst this
    exact ⟨u, hu, hC, hC'⟩

theorem preimage_compl {k : ℕ} (b : Fin k → ℕ) (C : Sorted.Rel I.Carrier k) :
    I.preimage b Cᶜ = I.profile b ∩ (I.preimage b C)ᶜ := by
  ext t
  constructor
  · rintro ⟨u, hu, hC⟩
    refine ⟨fun i => ⟨u i, (hu i).1, (hu i).2⟩, ?_⟩
    rintro ⟨u', hu', hC'⟩
    have := I.preimage_tuple_unique hu hu'
    subst this
    exact hC hC'
  · rintro ⟨hp, hn⟩
    choose u hu using hp
    refine ⟨u, hu, ?_⟩
    intro hC
    exact hn ⟨u, hu, hC⟩

theorem preimage_reindex {k l : ℕ} (f : Fin k → Fin l) (b : Fin l → ℕ) (C : Sorted.Rel I.Carrier k) :
    I.preimage b (Sorted.reindex I.Carrier f C) =
      I.profile b ∩ Sorted.reindex U f (I.preimage (b ∘ f) C) := by
  ext t
  constructor
  · rintro ⟨u, hu, hC⟩
    refine ⟨fun i => ⟨u i, (hu i).1, (hu i).2⟩, ?_⟩
    exact ⟨u ∘ f, fun i => hu (f i), hC⟩
  · rintro ⟨hp, u', hu', hC⟩
    choose u hu using hp
    have : u ∘ f = u' := by
      funext i
      exact I.Rep_unique (hu (f i)).2 (hu' i).2
        (by simp only [Function.comp_apply]; rw [(hu (f i)).1, (hu' i).1]; rfl)
    refine ⟨u, hu, ?_⟩
    show u ∘ f ∈ C
    rw [this]; exact hC

theorem preimage_exists {k : ℕ} (n : ℕ) (b : Fin k → ℕ) (C : Sorted.Rel I.Carrier (k + 1)) :
    I.preimage b (Sorted.exists_ I.Carrier n C) =
      Sorted.exists_ U (I.a n) (I.preimage (Fin.snoc b n) C) := by
  ext t
  constructor
  · rintro ⟨u, hu, z, hz, hC⟩
    obtain ⟨m, q⟩ := z
    have hm : m = n := hz
    subst hm
    induction q using Quotient.ind with
    | _ d =>
      refine ⟨Sorted.inj U d.1, rfl, ?_⟩
      refine ⟨Fin.snoc u (Sorted.inj I.Carrier (n := m) (I.cls d)), ?_, hC⟩
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact ⟨by simp only [Fin.snoc_last]; try rfl,
          by simp only [Fin.snoc_last]; exact ⟨m, d, rfl, rfl⟩⟩
      · simp only [Fin.snoc_castSucc]
        exact hu i
  · rintro ⟨y, hy, u', hu', hC⟩
    refine ⟨fun i => u' (Fin.castSucc i), fun i => ?_, u' (Fin.last k), ?_, ?_⟩
    · have := hu' (Fin.castSucc i)
      simpa only [Fin.snoc_castSucc] using this
    · have := (hu' (Fin.last k)).1
      simpa only [Fin.snoc_last] using this
    · have : (Fin.snoc (fun i => u' (Fin.castSucc i)) (u' (Fin.last k)) : Fin (k + 1) → Sorted.El I.Carrier) = u' := by
        funext i
        refine Fin.lastCases ?_ (fun i => ?_) i
        · simp
        · simp
      rw [this]; exact hC

/-- The profile class, coordinatewise: `t i` represents an element of sort
`b i` exactly when it is the injection of a domain element. -/
theorem mem_profile_iff {k : ℕ} (b : Fin k → ℕ) (t : Fin k → Sorted.El U) :
    t ∈ I.profile b ↔ ∀ i, ∃ x : U (I.a (b i)), t i = Sorted.inj U x ∧ x ∈ I.dom (b i) := by
  constructor
  · intro h i
    obtain ⟨z, hz, n, x, hx, rfl⟩ := h i
    have hn : n = b i := hz
    subst hn
    exact ⟨x.1, hx, x.2⟩
  · intro h i
    obtain ⟨x, hx, hxd⟩ := h i
    exact ⟨Sorted.inj I.Carrier (n := b i) (I.cls ⟨x, hxd⟩), rfl, b i, ⟨x, hxd⟩, hx, rfl⟩

/-- The profile class is admissible: it is a finite intersection of reindexed
domain classes. -/
theorem profile_mem {k : ℕ} (b : Fin k → ℕ) : I.profile b ∈ 𝒟.D k := by
  have : I.profile b = ⋂ i : Fin k,
      Sorted.reindex U (fun _ : Fin 1 => i) (Sorted.SortClass U (I.a (b i)) (I.dom (b i))) := by
    ext t
    rw [I.mem_profile_iff]
    simp only [Set.mem_iInter, Sorted.reindex, Sorted.SortClass, Set.mem_setOf_eq,
      Function.comp_apply]
  rw [this]
  exact 𝒟.iInter_mem _ (fun i => 𝒟.reindex_mem _ (I.dom_def (b i)))

theorem mem_inj_iff {n : ℕ} (z : Sorted.El U) (x : U n) :
    z = Sorted.inj U x ↔ ∃ h : z.1 = n, h ▸ z.2 = x := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h, hx⟩
    obtain ⟨m, y⟩ := z
    cases h
    simp only at hx
    subst hx
    rfl

/-- Unfolding `Rep` at a given interpreted sort. -/
theorem Rep_inj_iff {n : ℕ} (y : Sorted.El U) (q : I.Carrier n) :
    I.Rep y (Sorted.inj I.Carrier (n := n) q) ↔
      ∃ x : I.Dom n, y = Sorted.inj U x.1 ∧ I.cls x = q := by
  constructor
  · rintro ⟨m, x, rfl, hq⟩
    have hm : n = m := congrArg Sigma.fst hq
    subst hm
    refine ⟨x, rfl, ?_⟩
    exact (eq_of_heq (Sigma.mk.inj_iff.mp hq).2).symm
  · rintro ⟨x, rfl, rfl⟩
    exact ⟨n, x, rfl, rfl⟩

/-- The empty relation and the profile are the two possible preimages of a
sort atom. -/
theorem preimage_sortRel (b : Fin 1 → ℕ) (n : ℕ) :
    I.preimage b (Sorted.sortRel I.Carrier n) = if b 0 = n then I.profile b else ∅ := by
  ext t
  by_cases h : b 0 = n
  · simp only [h, if_true]
    constructor
    · rintro ⟨u, hu, -⟩ i
      exact ⟨u i, (hu i).1, (hu i).2⟩
    · intro ht
      choose u hu using ht
      refine ⟨u, hu, ?_⟩
      show (u 0).1 = n
      rw [(hu 0).1, h]
  · simp only [h, if_false, Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, hn⟩
    apply h
    rw [← (hu 0).1]; exact hn

theorem sort_atom (n : ℕ) : Sorted.sortRel I.Carrier n ∈ I.inducedD 1 := by
  intro b
  rw [I.preimage_sortRel]
  split_ifs
  · exact I.profile_mem b
  · exact 𝒟.empty_mem 1

/-- A representative of an interpreted element of known sort. -/
theorem rep_of_sort {y : Sorted.El U} {z : Sorted.El I.Carrier} {m : ℕ} (hz : z.1 = m) (hr : I.Rep y z) :
    ∃ x : I.Dom m, y = Sorted.inj U x.1 ∧ z = Sorted.inj I.Carrier (n := m) (I.cls x) := by
  obtain ⟨n, x, rfl, rfl⟩ := hr
  have : n = m := hz
  subst this
  exact ⟨x, rfl, rfl⟩

theorem model_inj_eq_iff {n : ℕ} (q q' : I.Carrier n) :
    Sorted.inj I.Carrier (n := n) q = Sorted.inj I.Carrier (n := n) q' ↔ q = q' := by
  constructor
  · intro h; exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · rintro rfl; rfl

/-- The equality atom.  Its preimage at profile `(m, m)` is the interpreted
equivalence on sort `m`; at any other profile it is empty. -/
theorem eq_atom : Sorted.eqRel I.Carrier ∈ I.inducedD 2 := by
  intro b
  by_cases h : b 1 = b 0
  · have : I.preimage b (Sorted.eqRel I.Carrier) =
        Sorted.liftRel U {s : Fin 2 → U (I.a (b 0)) | I.eqv (b 0) (s 0) (s 1)} := by
      ext t
      constructor
      · rintro ⟨u, hu, heq⟩
        obtain ⟨x, hx, hux⟩ := I.rep_of_sort (hu 0).1 (hu 0).2
        obtain ⟨y, hy, huy⟩ := I.rep_of_sort (by rw [(hu 1).1, h]) (hu 1).2
        have heq' : u 0 = u 1 := heq
        rw [hux, huy, I.model_inj_eq_iff, I.cls_eq_iff] at heq'
        exact ⟨![x.1, y.1], by simp [Fin.forall_fin_two, hx, hy], heq'⟩
      · rintro ⟨s, hs, hse⟩
        have hd := I.eqv_dom _ _ _ hse
        refine ⟨![Sorted.inj I.Carrier (n := b 0) (I.cls ⟨s 0, hd.1⟩),
          Sorted.inj I.Carrier (n := b 0) (I.cls ⟨s 1, hd.2⟩)], ?_, ?_⟩
        · rw [Fin.forall_fin_two]
          refine ⟨⟨rfl, b 0, ⟨s 0, hd.1⟩, hs 0, rfl⟩, ⟨h.symm, b 0, ⟨s 1, hd.2⟩, hs 1, rfl⟩⟩
        · show Sorted.inj I.Carrier (n := b 0) (I.cls ⟨s 0, hd.1⟩) = Sorted.inj I.Carrier (n := b 0) (I.cls ⟨s 1, hd.2⟩)
          rw [I.model_inj_eq_iff, I.cls_eq_iff]
          exact hse
    rw [this]
    exact I.eqv_def (b 0)
  · have : I.preimage b (Sorted.eqRel I.Carrier) = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, heq⟩
      have heq' : u 0 = u 1 := heq
      apply h
      rw [← (hu 1).1, ← (hu 0).1, heq']
    rw [this]
    exact 𝒟.empty_mem 2

/-- The parameter atom: the singleton of an interpreted element is the class
of its representatives, definable from the equivalence and one source
parameter. -/
theorem param_atom (p : Sorted.El I.Carrier) : Sorted.paramRel I.Carrier p ∈ I.inducedD 1 := by
  obtain ⟨m, q⟩ := p
  induction q using Quotient.ind with
  | _ d =>
  intro b
  change I.preimage b (Sorted.paramRel I.Carrier (Sorted.inj I.Carrier (n := m) (I.cls d))) ∈ 𝒟.D 1
  by_cases h : b 0 = m
  · have : I.preimage b (Sorted.paramRel I.Carrier (Sorted.inj I.Carrier (n := m) (I.cls d))) =
        Sorted.exists_ U (I.a m)
          (Sorted.liftRel U {s : Fin 2 → U (I.a m) | I.eqv m (s 0) (s 1)} ∩
            Sorted.reindex U (fun _ : Fin 1 => (1 : Fin 2)) (Sorted.paramRel U (Sorted.inj U d.1))) := by
      ext t
      constructor
      · rintro ⟨u, hu, heq⟩
        obtain ⟨x, hx, hux⟩ := I.rep_of_sort ((hu 0).1.trans h) (hu 0).2
        have heq' : u 0 = Sorted.inj I.Carrier (n := m) (I.cls d) := heq
        rw [hux, I.model_inj_eq_iff, I.cls_eq_iff] at heq'
        refine ⟨Sorted.inj U d.1, rfl, ⟨![x.1, d.1], ?_, heq'⟩, ?_⟩
        · rw [Fin.forall_fin_two]
          exact ⟨hx, rfl⟩
        · show (Fin.snoc t (Sorted.inj U d.1) : Fin 2 → Sorted.El U) 1 = Sorted.inj U d.1
          rfl
      · rintro ⟨y, hy, ⟨s, hs, hse⟩, hp⟩
        have h1 : (Fin.snoc t y : Fin 2 → Sorted.El U) 1 = Sorted.inj U d.1 := hp
        have h0 : (Fin.snoc t y : Fin 2 → Sorted.El U) 0 = t 0 := rfl
        have hs1 : s 1 = d.1 := Sorted.inj_injective U (by rw [← hs 1, h1])
        have hd := I.eqv_dom _ _ _ hse
        refine ⟨![Sorted.inj I.Carrier (n := m) (I.cls ⟨s 0, hd.1⟩)], ?_, ?_⟩
        · intro i
          have : i = 0 := Subsingleton.elim _ _
          subst this
          refine ⟨h.symm, m, ⟨s 0, hd.1⟩, ?_, rfl⟩
          rw [← h0, hs 0]
        · show Sorted.inj I.Carrier (n := m) (I.cls ⟨s 0, hd.1⟩) = Sorted.inj I.Carrier (n := m) (I.cls d)
          rw [I.model_inj_eq_iff, I.cls_eq_iff]
          show I.eqv m (s 0) d.1
          rw [← hs1]; exact hse
    rw [this]
    refine 𝒟.exists_mem _ (𝒟.inter_mem (I.eqv_def m) (𝒟.reindex_mem _ (𝒟.param_mem _)))
  · have : I.preimage b (Sorted.paramRel I.Carrier (Sorted.inj I.Carrier (n := m) (I.cls d))) = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, heq⟩
      apply h
      have heq' : u 0 = Sorted.inj I.Carrier (n := m) (I.cls d) := heq
      rw [← (hu 0).1, heq']
    rw [this]
    exact 𝒟.empty_mem 1

theorem inducedD_inter {k : ℕ} {C C' : Sorted.Rel I.Carrier k} (hC : C ∈ I.inducedD k)
    (hC' : C' ∈ I.inducedD k) : C ∩ C' ∈ I.inducedD k := by
  intro b
  rw [I.preimage_inter]
  exact 𝒟.inter_mem (hC b) (hC' b)

theorem inducedD_reindex {k l : ℕ} (f : Fin k → Fin l) {C : Sorted.Rel I.Carrier k}
    (hC : C ∈ I.inducedD k) : Sorted.reindex I.Carrier f C ∈ I.inducedD l := by
  intro b
  rw [I.preimage_reindex]
  exact 𝒟.inter_mem (I.profile_mem b) (𝒟.reindex_mem f (hC (b ∘ f)))


/-- The induced class system on the interpreted carriers. -/
noncomputable def inducedSys : ClassSys I.Carrier where
  D := I.inducedD
  eq_mem := I.eq_atom
  sort_mem := I.sort_atom
  param_mem := I.param_atom
  univ_mem := by
    intro k b
    rw [I.preimage_univ]
    exact I.profile_mem b
  inter_mem := by
    intro k C C' hC hC'
    exact I.inducedD_inter hC hC'
  compl_mem := by
    intro k C hC b
    rw [I.preimage_compl]
    exact 𝒟.inter_mem (I.profile_mem b) (𝒟.compl_mem (hC b))
  reindex_mem := by
    intro k l f C hC
    exact I.inducedD_reindex f hC
  exists_mem := by
    intro n k C hC b
    rw [I.preimage_exists]
    exact 𝒟.exists_mem (I.a n) (hC (Fin.snoc b n))

theorem mem_inducedSys_iff {k : ℕ} (C : Sorted.Rel I.Carrier k) :
    C ∈ I.inducedSys.D k ↔ ∀ b : Fin k → ℕ, I.preimage b C ∈ 𝒟.D k := Iff.rfl

/-- The presentation of the interpreted carriers in the source. -/
noncomputable def pres : Presentation U I.Carrier where
  a := I.a
  rep n x := if h : x ∈ I.dom n then some (I.cls ⟨x, h⟩) else none
  surj := by
    intro n p
    induction p using Quotient.ind with
    | _ x => exact ⟨x.1, by simp [x.2, cls]⟩

theorem pres_rep_eq_some_iff {n : ℕ} (x : U (I.a n)) (q : I.Carrier n) :
    I.pres.rep n x = some q ↔ ∃ h : x ∈ I.dom n, I.cls ⟨x, h⟩ = q := by
  show (if h : x ∈ I.dom n then some (I.cls ⟨x, h⟩) else none) = some q ↔ _
  by_cases h : x ∈ I.dom n
  · rw [dif_pos h]
    simp only [Option.some.injEq]
    exact ⟨fun h' => ⟨h, h'⟩, fun ⟨_, h'⟩ => h'⟩
  · rw [dif_neg h]
    simp only [reduceCtorEq, false_iff, not_exists]
    intro h'; exact (h h').elim

theorem pres_rep_cls {n : ℕ} (x : I.Dom n) : I.pres.rep n x.1 = some (I.cls x) :=
  (I.pres_rep_eq_some_iff x.1 (I.cls x)).2 ⟨x.2, rfl⟩

theorem pres_rep_dom {n : ℕ} {x : U (I.a n)} {q : I.Carrier n}
    (h : I.pres.rep n x = some q) : x ∈ I.dom n :=
  ((I.pres_rep_eq_some_iff x q).1 h).1

/-- Representation in terms of the presentation. -/
theorem Rep_inj_iff' {n : ℕ} (x : U (I.a n)) (q : I.Carrier n) :
    I.Rep (Sorted.inj U x) (Sorted.inj I.Carrier q) ↔ I.pres.rep n x = some q := by
  rw [I.Rep_inj_iff, I.pres_rep_eq_some_iff]
  constructor
  · rintro ⟨x', hx', rfl⟩
    have := Sorted.inj_injective U hx'
    subst this
    exact ⟨x'.2, rfl⟩
  · rintro ⟨h, rfl⟩
    exact ⟨⟨x, h⟩, rfl, rfl⟩

end SortInterp

end SolidLean.Solid
