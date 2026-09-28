import Solid.TowerTheory
import Solid.Gen.Core

/-!
# Finitary interpretations, presentations, and definable isomorphisms

Draft 2, §1.2, in *one-coordinate normal form*: the `n`-th interpreted sort
is a definable class of a single source sort `a n`, modulo a definable
equivalence.  In a ZFC sort finite tuples are coded by single elements, so
this loses no generality against domains that are subsets of finite products;
that reduction is a remark in the paper and is not formalized here.

An interpretation `I` of the tower signature in `M` yields a tower
`I.model` (quotients of the domains) together with an induced class system
`I.induced` (a relation is admissible when each of its preimages under the
representation maps is admissible in `M`).  `I` interprets `H` in `M` when
`I.asModel` satisfies `IsTowerModel`.

A `Presentation` records how a tower's elements are represented by elements
of another tower, so that a tower isomorphism can be called definable in `M`
with respect to the presentation of its target.  Presentations compose,
which is what lets `P` in `M ⊳ N ⊳ P` be presented in `M`.
-/

universe u

namespace SolidLean.Solid

open Classical

/-- A finitary interpretation of the tower signature in `M`, in one-coordinate
normal form.  Membership, transition and boundary constants are given by
definable classes that respect the equivalence. -/
structure SInterp (U : ℕ → Type u) (𝒟 : ClassSys U) extends SortInterp U 𝒟 where
  memC : ∀ n, U (a n) → U (a n) → Prop
  memC_congr : ∀ n x x' y y', eqv n x x' → eqv n y y' → (memC n x y ↔ memC n x' y')
  jC : ∀ n, U (a n) → U (a (n + 1)) → Prop
  jC_total : ∀ n x, x ∈ dom n → ∃ y, y ∈ dom (n + 1) ∧ jC n x y
  jC_func : ∀ n x y y', y ∈ dom (n + 1) → y' ∈ dom (n + 1) →
    jC n x y → jC n x y' → eqv (n + 1) y y'
  jC_congr : ∀ n x x' y, eqv n x x' → jC n x y → jC n x' y
  jC_congr_right : ∀ n x y y', eqv (n + 1) y y' → jC n x y → jC n x y'
  kappaC : ∀ n, U (a (n + 1)) → Prop
  kappaC_exists : ∀ n, ∃ y, y ∈ dom (n + 1) ∧ kappaC n y
  kappaC_unique : ∀ n y y', y ∈ dom (n + 1) → y' ∈ dom (n + 1) →
    kappaC n y → kappaC n y' → eqv (n + 1) y y'
  kappaC_congr : ∀ n y y', eqv (n + 1) y y' → kappaC n y → kappaC n y'
  memC_def : ∀ n, 𝒟.DefOn (a n) 2 {t | memC n (t 0) (t 1)}
  jC_def : ∀ n,
    ({t | ∃ x y, t 0 = Sorted.inj U x ∧ t 1 = Sorted.inj U y ∧ jC n x y} : Sorted.Rel U 2) ∈ 𝒟.D 2
  kappaC_def : ∀ n, 𝒟.DefinableSet (a (n + 1)) {y | kappaC n y}

namespace SInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} (I : SInterp U 𝒟)

/-- Interpreted membership. -/
def memQ {n : ℕ} : I.Carrier n → I.Carrier n → Prop :=
  Quotient.lift₂ (fun x y : I.Dom n => I.memC n x.1 y.1) (by
    intro x y x' y' hx hy
    exact propext (I.memC_congr n x.1 x'.1 y.1 y'.1 hx hy))

/-- The chosen `jC`-image of a domain element. -/
noncomputable def jImage {n : ℕ} (x : I.Dom n) : I.Dom (n + 1) :=
  ⟨Classical.choose (I.jC_total n x.1 x.2), (Classical.choose_spec (I.jC_total n x.1 x.2)).1⟩

theorem jImage_spec {n : ℕ} (x : I.Dom n) : I.jC n x.1 (I.jImage x).1 :=
  (Classical.choose_spec (I.jC_total n x.1 x.2)).2

/-- Interpreted transition map. -/
noncomputable def jQ (n : ℕ) : I.Carrier n → I.Carrier (n + 1) :=
  Quotient.lift (fun x : I.Dom n => I.cls (I.jImage x)) (by
    intro x y hxy
    apply Quotient.sound
    show I.eqv (n + 1) _ _
    have h1 : I.jC n y.1 (I.jImage x).1 := I.jC_congr n x.1 y.1 _ hxy (I.jImage_spec x)
    exact I.jC_func n y.1 _ _ (I.jImage x).2 (I.jImage y).2 h1 (I.jImage_spec y))

/-- Interpreted boundary constant. -/
noncomputable def kappaQ (n : ℕ) : I.Carrier (n + 1) :=
  I.cls ⟨Classical.choose (I.kappaC_exists n), (Classical.choose_spec (I.kappaC_exists n)).1⟩

/-- The interpreted tower.  An `abbrev`, so that its sorts unfold to the
quotient carriers during unification. -/
noncomputable abbrev model : MemTower.{u} where
  U := I.Carrier
  mem := fun {n} x y => I.memQ (n := n) x y
  j := I.jQ
  κ := I.kappaQ

/-! ### The induced class system -/

theorem model_mem_cls {n : ℕ} (x y : I.Dom n) :
    I.model.mem (I.cls x) (I.cls y) ↔ I.memC n x.1 y.1 := Iff.rfl

theorem model_j_cls {n : ℕ} (x : I.Dom n) :
    I.model.j n (I.cls x) = I.cls (I.jImage x) := rfl

theorem jQ_cls {n : ℕ} (x : I.Dom n) : I.jQ n (I.cls x) = I.cls (I.jImage x) := rfl

/-- The membership atom. -/
theorem memRelAll_atom : I.model.memRelAll ∈ I.inducedD 2 := by
  intro b
  by_cases h : b 1 = b 0
  · have : I.preimage b I.model.memRelAll =
        Sorted.liftRel U {s : Fin 2 → U (I.a (b 0)) | I.memC (b 0) (s 0) (s 1)} ∩ I.profile b := by
      ext t
      constructor
      · rintro ⟨u, hu, m, q, q', hq, hq', hmem⟩
        obtain ⟨x, hx, hux⟩ := I.rep_of_sort (hu 0).1 (hu 0).2
        obtain ⟨y, hy, huy⟩ := I.rep_of_sort (by rw [(hu 1).1, h]) (hu 1).2
        have hm : m = b 0 := by rw [← (hu 0).1, hq]
        subst hm
        rw [hux, I.model_inj_eq_iff] at hq
        rw [huy, I.model_inj_eq_iff] at hq'
        subst hq; subst hq'
        refine ⟨⟨![x.1, y.1], by simp [Fin.forall_fin_two, hx, hy], hmem⟩, ?_⟩
        intro i; exact ⟨u i, (hu i).1, (hu i).2⟩
      · rintro ⟨⟨s, hs, hsm⟩, hp⟩
        obtain ⟨z0, hz0, hr0⟩ := hp 0
        obtain ⟨z1, hz1, hr1⟩ := hp 1
        obtain ⟨x0, hx0, rfl⟩ := I.rep_of_sort hz0 hr0
        obtain ⟨x1, hx1, rfl⟩ := I.rep_of_sort (hz1.trans h) hr1
        have e0 : s 0 = x0.1 := Sorted.inj_injective U (by rw [← hs 0, hx0])
        have e1 : s 1 = x1.1 := Sorted.inj_injective U (by rw [← hs 1, hx1])
        refine ⟨![I.model.inj (n := b 0) (I.cls x0), I.model.inj (n := b 0) (I.cls x1)], ?_, ?_⟩
        · rw [Fin.forall_fin_two]
          exact ⟨⟨hz0, hr0⟩, ⟨hz1, hr1⟩⟩
        · refine ⟨b 0, I.cls x0, I.cls x1, rfl, rfl, ?_⟩
          show I.memC (b 0) x0.1 x1.1
          rw [← e0, ← e1]; exact hsm
    rw [this]
    exact 𝒟.inter_mem (I.memC_def (b 0)) (I.profile_mem b)
  · have : I.preimage b I.model.memRelAll = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, m, q, q', hq, hq', -⟩
      apply h
      rw [← (hu 1).1, ← (hu 0).1, hq, hq']
    rw [this]
    exact 𝒟.empty_mem 2

/-- The transition atom. -/
theorem jRelAll_atom : I.model.jRelAll ∈ I.inducedD 2 := by
  intro b
  by_cases h : b 1 = b 0 + 1
  · have : I.preimage b I.model.jRelAll =
        ({t | ∃ x y, t 0 = Sorted.inj U x ∧ t 1 = Sorted.inj U y ∧ I.jC (b 0) x y} : Sorted.Rel U 2) ∩
          I.profile b := by
      ext t
      constructor
      · rintro ⟨u, hu, n, q, hq0, hq1⟩
        obtain ⟨x, hx, hux⟩ := I.rep_of_sort (hu 0).1 (hu 0).2
        obtain ⟨y, hy, huy⟩ := I.rep_of_sort (by rw [(hu 1).1, h]) (hu 1).2
        have hn : n = b 0 := by rw [← (hu 0).1, hq0]
        subst hn
        rw [hux, I.model_inj_eq_iff] at hq0
        subst hq0
        rw [huy, I.model_j_cls, I.model_inj_eq_iff, I.cls_eq_iff] at hq1
        refine ⟨⟨x.1, y.1, hx, hy, ?_⟩, fun i => ⟨u i, (hu i).1, (hu i).2⟩⟩
        exact I.jC_congr_right _ _ _ _ (I.eqv_symm _ _ _ hq1) (I.jImage_spec x)
      · rintro ⟨⟨x, y, hx, hy, hjc⟩, hp⟩
        obtain ⟨z0, hz0, hr0⟩ := hp 0
        obtain ⟨z1, hz1, hr1⟩ := hp 1
        obtain ⟨x0, hx0, rfl⟩ := I.rep_of_sort hz0 hr0
        obtain ⟨x1, hx1, rfl⟩ := I.rep_of_sort (hz1.trans h) hr1
        have e0 : x = x0.1 := Sorted.inj_injective U (by rw [← hx, hx0])
        have e1 : y = x1.1 := Sorted.inj_injective U (by rw [← hy, hx1])
        subst e0; subst e1
        refine ⟨![I.model.inj (n := b 0) (I.cls x0), I.model.inj (n := b 0 + 1) (I.cls x1)],
          ?_, b 0, I.cls x0, rfl, ?_⟩
        · rw [Fin.forall_fin_two]
          exact ⟨⟨hz0, hr0⟩, ⟨hz1, hr1⟩⟩
        · show I.model.inj (n := b 0 + 1) (I.cls x1) = I.model.inj (I.jQ (b 0) (I.cls x0))
          rw [I.jQ_cls, I.model_inj_eq_iff, I.cls_eq_iff]
          exact I.jC_func _ _ _ _ x1.2 (I.jImage x0).2 hjc (I.jImage_spec x0)
    rw [this]
    exact 𝒟.inter_mem (I.jC_def (b 0)) (I.profile_mem b)
  · have : I.preimage b I.model.jRelAll = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, n, q, hq0, hq1⟩
      apply h
      rw [← (hu 1).1, ← (hu 0).1, hq0, hq1]
    rw [this]
    exact 𝒟.empty_mem 2

/-- The chosen representative of the interpreted boundary constant. -/
noncomputable def kappaRep (n : ℕ) : I.Dom (n + 1) :=
  ⟨Classical.choose (I.kappaC_exists n), (Classical.choose_spec (I.kappaC_exists n)).1⟩

theorem kappaRep_spec (n : ℕ) : I.kappaC n (I.kappaRep n).1 :=
  (Classical.choose_spec (I.kappaC_exists n)).2

theorem model_kappa (n : ℕ) : I.model.κ n = I.cls (I.kappaRep n) := rfl

/-- The boundary-constant atom. -/
theorem kappa_atom (m : ℕ) : I.model.kappaRel m ∈ I.inducedD 1 := by
  intro b
  by_cases h : b 0 = m + 1
  · have : I.preimage b (I.model.kappaRel m) =
        Sorted.SortClass U (I.a (m + 1)) {y | I.kappaC m y} ∩ I.profile b := by
      ext t
      constructor
      · rintro ⟨u, hu, heq⟩
        obtain ⟨y, hy, huy⟩ := I.rep_of_sort ((hu 0).1.trans h) (hu 0).2
        have heq' : u 0 = I.model.inj (n := m + 1) (I.model.κ m) := heq
        rw [huy, I.model_kappa, I.model_inj_eq_iff, I.cls_eq_iff] at heq'
        refine ⟨⟨y.1, hy, ?_⟩, fun i => ⟨u i, (hu i).1, (hu i).2⟩⟩
        exact I.kappaC_congr _ _ _ (I.eqv_symm _ _ _ heq') (I.kappaRep_spec m)
      · rintro ⟨⟨y, hy, hk⟩, hp⟩
        obtain ⟨z0, hz0, hr0⟩ := hp 0
        obtain ⟨x0, hx0, rfl⟩ := I.rep_of_sort (hz0.trans h) hr0
        have e0 : y = x0.1 := Sorted.inj_injective U (by rw [← hy, hx0])
        subst e0
        refine ⟨![I.model.inj (n := m + 1) (I.cls x0)], ?_, ?_⟩
        · intro i
          have : i = 0 := Subsingleton.elim _ _
          subst this
          exact ⟨hz0, hr0⟩
        · show I.model.inj (n := m + 1) (I.cls x0) = I.model.inj (n := m + 1) (I.model.κ m)
          rw [I.model_kappa, I.model_inj_eq_iff, I.cls_eq_iff]
          exact I.kappaC_unique _ _ _ x0.2 (I.kappaRep m).2 hk (I.kappaRep_spec m)
    rw [this]
    exact 𝒟.inter_mem (I.kappaC_def m) (I.profile_mem b)
  · have : I.preimage b (I.model.kappaRel m) = ∅ := by
      ext t
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨u, hu, heq⟩
      apply h
      have heq' : u 0 = I.model.inj (n := m + 1) (I.model.κ m) := heq
      rw [← (hu 0).1, heq']
    rw [this]
    exact 𝒟.empty_mem 1

/-- The membership atom of sort `n`: the global membership relation cut down
to sort `n` in the first coordinate. -/
theorem memRel_atom (n : ℕ) : I.model.memRel n ∈ I.inducedD 2 := by
  have : I.model.memRel n =
      I.model.memRelAll ∩ I.model.reindex (fun _ : Fin 1 => (0 : Fin 2)) (I.model.sortRel n) := by
    ext t
    simp only [MemTower.memRel, MemTower.memRelAll, MemTower.sortRel,
      Set.mem_inter_iff, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨x, y, hx, hy, hxy⟩
      exact ⟨⟨n, x, y, hx, hy, hxy⟩, by rw [hx]⟩
    · rintro ⟨⟨m, x, y, hx, hy, hxy⟩, hs⟩
      have hm : m = n := by rw [hx] at hs; exact hs
      subst hm
      exact ⟨x, y, hx, hy, hxy⟩
  rw [this]
  exact I.inducedD_inter I.memRelAll_atom (I.inducedD_reindex _ (I.sort_atom n))

/-- The transition atom of sort `n`. -/
theorem j_atom (n : ℕ) : I.model.jRel n ∈ I.inducedD 2 := by
  have : I.model.jRel n =
      I.model.jRelAll ∩ I.model.reindex (fun _ : Fin 1 => (0 : Fin 2)) (I.model.sortRel n) := by
    ext t
    simp only [MemTower.jRel, MemTower.jRelAll, MemTower.sortRel,
      Set.mem_inter_iff, Set.mem_setOf_eq, Function.comp_apply]
    constructor
    · rintro ⟨x, hx, hy⟩
      exact ⟨⟨n, x, hx, hy⟩, by rw [hx]⟩
    · rintro ⟨⟨m, x, hx, hy⟩, hs⟩
      have hm : m = n := by rw [hx] at hs; exact hs
      subst hm
      exact ⟨x, hx, hy⟩
  rw [this]
  exact I.inducedD_inter I.jRelAll_atom (I.inducedD_reindex _ (I.sort_atom n))

/-- The induced class system: the sort-level induced system together with
the tower atoms. -/
noncomputable def induced : ClassSystem I.model where
  toClassSys := I.inducedSys
  memRel_mem := I.memRel_atom
  j_mem := I.j_atom
  kappa_mem := I.kappa_atom

/-- The presentation of the interpreted tower in the source (the sort-level
presentation, typed with the tower's carrier). -/
noncomputable abbrev pres : Presentation U I.model.U := I.toSortInterp.pres

/-- The interpreted structure for `H`. -/
noncomputable abbrev asModel : TowerWithClasses.{u} := ⟨I.model, I.induced⟩

/-- `I` interprets `H` in `M`. -/
def Models : Prop := IsTowerModel I.asModel

end SInterp

/-- An isomorphism of towers. -/
structure TowerIso (M N : MemTower.{u}) where
  toFun : ∀ n, M.U n → N.U n
  bijective : ∀ n, Function.Bijective (toFun n)
  mem_iff : ∀ n (x y : M.U n), N.mem (toFun n x) (toFun n y) ↔ M.mem x y
  j_comm : ∀ n (x : M.U n), toFun (n + 1) (M.j n x) = N.j n (toFun n x)
  κ_comm : ∀ n, toFun (n + 1) (M.κ n) = N.κ n

namespace TowerIso

/-- `i : M → P` is `𝒟`-definable with respect to a presentation of `P` in `M`:
the graph relating `x` to a representative of `i x` is admissible. -/
def DefinableIn {M P : MemTower.{u}} (𝒟 : ClassSystem M) (p : Presentation M.U P.U)
    (i : TowerIso M P) : Prop :=
  ∀ n, ({t | ∃ (x : M.U n) (y : M.U (p.a n)),
    t 0 = M.inj x ∧ t 1 = M.inj y ∧ p.rep n y = some (i.toFun n x)} : M.Rel 2) ∈ 𝒟.D 2

end TowerIso

/-- An interpretation of the tower signature in a tower with classes. -/
abbrev Interp (M : TowerWithClasses.{u}) : Type u := SInterp M.T.U M.𝒟.toClassSys

end SolidLean.Solid
