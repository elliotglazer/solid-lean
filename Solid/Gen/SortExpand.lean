module

public import Solid.Gen.SortSolid

/-!
# The canonical expansion of a model of `T(𝔉)` to a definable-sort expansion

Every model `N` of `T(𝔉)` is the base reduct of a model of the expanded
theory: the new sorts are the defined subsets, the encodings are the
inclusions, and the further symbols denote their clauses.  The expanded
model is built as an interpretation of the expanded signature in `N`
(`SortExp.expInterp`): sort `k` is interpreted on the coding sort `flatSort k`
with domain the defined subset and equality as the equivalence.  Its model
with the induced class system is a model of the expanded theory
(`SortExp.expand_isModel`), whose base reduct is isomorphic to `N`.

Together with `SortExp.solid`, this is the equivalence of the two
presentations: the models correspond, and solidity transfers.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-! ### Class systems with the same classes on each sort give the same models -/

namespace ClauseFamily

variable {F : ClauseFamily.{u}}

/-- `IsGenModel` only depends on the class system through its classes of a
single sort (`DefOn`). -/
theorem IsGenModel.congr {M : Str.{u} F.sig} {𝒟 𝒟' : StrSys M} (h : F.IsGenModel ⟨M, 𝒟⟩)
    (heq : ∀ n k (C : Set (Fin k → M.U n)),
      Sorted.liftRel M.U C ∈ 𝒟.D k ↔ Sorted.liftRel M.U C ∈ 𝒟'.D k) :
    F.IsGenModel ⟨M, 𝒟'⟩ where
  wf := h.wf
  tower := by
    have ht := h.tower
    have hz : ∀ n, (⟨Δ M h.wf, ΔSys ⟨M, 𝒟'⟩ h.wf⟩ : TowerWithClasses).SortZFC n := by
      intro n
      have e : (⟨Δ M h.wf, ΔSys ⟨M, 𝒟⟩ h.wf⟩ : TowerWithClasses).DefOn n =
          (⟨Δ M h.wf, ΔSys ⟨M, 𝒟'⟩ h.wf⟩ : TowerWithClasses).DefOn n := by
        funext k C
        exact propext (heq n k C)
      have := ht.zfc n
      unfold TowerWithClasses.SortZFC at this ⊢
      rw [← e]; exact this
    exact ⟨hz, ht.j_injective, ht.j_mem_iff, ht.kappa_inaccessible, ht.j_image,
      ht.next_inaccessible, ht.bottom⟩
  clause := h.clause

/-- The tower structure of a model of `T(𝔉)`. -/
noncomputable abbrev IsGenModel.tstr {M : StrWithSys.{u} F.sig} (h : F.IsGenModel M) : Str.{u} TowerSig :=
  (Δ M.M h.wf).toStr

end ClauseFamily

namespace SortExp

variable {F : ClauseFamily.{u}} (X : SortExp F)

section Expand

variable {N : StrWithSys.{u} F.sig} (hN : F.IsGenModel N)

/-- Membership of an element of the coding sort in the domain of sort `k`:
everything for a base sort, the defined subset for a new sort. -/
def InDom (k : ℕ) (z : Sorted.El N.M.U) : Prop :=
  ∀ m, k = nidx m → (X.domF m).Sat hN.tstr ![z]

theorem inDom_bidx (n : ℕ) (z : Sorted.El N.M.U) : X.InDom hN (bidx n) z := by
  intro m h
  exact absurd (congrArg (· % 2) h) (by simp [bidx, nidx])

theorem inDom_nidx_iff (m : ℕ) (z : Sorted.El N.M.U) :
    X.InDom hN (nidx m) z ↔ (X.domF m).Sat hN.tstr ![z] := by
  constructor
  · intro h; exact h m rfl
  · intro h m' hm'
    have : m' = m := by simp [nidx] at hm'; omega
    subst this; exact h

/-- The domain of sort `k`, as a set of the coding sort. -/
def expDom (k : ℕ) : Set (N.M.U (X.flatSort k)) := {x | X.InDom hN k (Sorted.inj N.M.U x)}

/-- The domain formula defines a class of the base model. -/
theorem domF_def_mem (m : ℕ) : (X.domF m).Def hN.tstr ∈ N.𝒟.D 1 :=
  (X.domF m).def_mem (ClauseFamily.ΔSys N hN.wf).toStrSys

/-- The class of elements in the domain of sort `k`. -/
theorem inDom_mem (k : ℕ) : ({t | X.InDom hN k (t 0)} : Sorted.Rel N.M.U 1) ∈ N.𝒟.D 1 := by
  by_cases h : k % 2 = 0
  · obtain ⟨n, rfl⟩ : ∃ n, k = bidx n := ⟨k / 2, eq_bidx_of_even h⟩
    have e : ({t | X.InDom hN (bidx n) (t 0)} : Sorted.Rel N.M.U 1) = Set.univ := by
      ext t; simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact X.inDom_bidx hN n (t 0)
    rw [e]; exact N.𝒟.univ_mem 1
  · obtain ⟨m, rfl⟩ : ∃ m, k = nidx m := ⟨k / 2, eq_nidx_of_odd h⟩
    have e : ({t | X.InDom hN (nidx m) (t 0)} : Sorted.Rel N.M.U 1) = (X.domF m).Def hN.tstr := by
      ext t
      show X.InDom hN (nidx m) (t 0) ↔ (X.domF m).Sat hN.tstr t
      rw [X.inDom_nidx_iff hN]
      have : t = ![t 0] := by
        funext i
        match i with
        | 0 => rfl
      exact Iff.of_eq (congrArg _ this.symm)
    rw [e]; exact X.domF_def_mem hN m

theorem sortAt_base_flat (r : F.sig.Rel) (i : Fin (F.sig.arity r)) :
    X.flatSort (bidx (F.sig.sortAt r i)) = F.sig.sortAt r i := X.flatSort_bidx _

/-- The interpretation of the expanded signature in the base model: sort `k`
on the coding sort `flatSort k`, with domain the defined subset and equality
as the equivalence; the base symbols denote the relations of `N`, the
encodings denote equality, the further symbols denote their clauses. -/
noncomputable def expInterp : GenInterp N.M.U N.𝒟.toClassSys X.sig where
  a := X.flatSort
  dom := X.expDom hN
  eqv k x y := x = y ∧ x ∈ X.expDom hN k
  eqv_refl _ x hx := ⟨rfl, hx⟩
  eqv_symm _ x y h := ⟨h.1.symm, h.1 ▸ h.2⟩
  eqv_trans _ x y z h h' := ⟨h.1.trans h'.1, h.2⟩
  eqv_dom _ x y h := ⟨h.2, h.1 ▸ h.2⟩
  dom_def k := by
    show Sorted.SortClass N.M.U (X.flatSort k) (X.expDom hN k) ∈ N.𝒟.D 1
    have e : Sorted.SortClass N.M.U (X.flatSort k) (X.expDom hN k) =
        Sorted.sortRel N.M.U (X.flatSort k) ∩ {t | X.InDom hN k (t 0)} := by
      ext t
      constructor
      · rintro ⟨x, hx, hxd⟩
        refine ⟨?_, ?_⟩
        · show (t 0).1 = X.flatSort k
          rw [hx]
        · show X.InDom hN k (t 0)
          rw [hx]; exact hxd
      · rintro ⟨h1, h2⟩
        exact ⟨Sorted.toSort N.M.U (t 0) h1, (Sorted.inj_toSort N.M.U (t 0) h1).symm, by
          show X.InDom hN k (Sorted.inj N.M.U (Sorted.toSort N.M.U (t 0) h1))
          rw [Sorted.inj_toSort]; exact h2⟩
    rw [e]
    exact N.𝒟.inter_mem (N.𝒟.sort_mem _) (X.inDom_mem hN k)
  eqv_def k := by
    show Sorted.liftRel N.M.U {t | t 0 = t 1 ∧ t 0 ∈ X.expDom hN k} ∈ N.𝒟.D 2
    have e : Sorted.liftRel N.M.U {t | t 0 = t 1 ∧ t 0 ∈ X.expDom hN k} =
        Sorted.eqRel N.M.U ∩ Sorted.profileRel N.M.U ![X.flatSort k, X.flatSort k] ∩
          Sorted.reindex N.M.U (fun _ : Fin 1 => (0 : Fin 2)) {t | X.InDom hN k (t 0)} := by
      ext t
      constructor
      · rintro ⟨s, hs, h01, hd⟩
        refine ⟨⟨?_, fun i => ?_⟩, ?_⟩
        · show t 0 = t 1
          rw [hs 0, hs 1, h01]
        · match i with
          | 0 => rw [hs 0]; rfl
          | 1 => rw [hs 1]; rfl
        · show X.InDom hN k (t 0)
          rw [hs 0]; exact hd
      · rintro ⟨⟨h01, hp⟩, hd⟩
        have h0 : (t 0).1 = X.flatSort k := hp 0
        have h1 : (t 1).1 = X.flatSort k := hp 1
        refine ⟨![Sorted.toSort N.M.U (t 0) h0, Sorted.toSort N.M.U (t 1) h1], fun i => ?_, ?_, ?_⟩
        · match i with
          | 0 => exact (Sorted.inj_toSort N.M.U (t 0) h0).symm
          | 1 => exact (Sorted.inj_toSort N.M.U (t 1) h1).symm
        · show Sorted.toSort N.M.U (t 0) h0 = Sorted.toSort N.M.U (t 1) h1
          apply Sorted.inj_injective N.M.U
          rw [Sorted.inj_toSort, Sorted.inj_toSort]
          exact (h01 : t 0 = t 1)
        · show X.InDom hN k (Sorted.inj N.M.U (Sorted.toSort N.M.U (t 0) h0))
          rw [Sorted.inj_toSort]; exact hd
    rw [e]
    exact N.𝒟.inter_mem (N.𝒟.inter_mem N.𝒟.eq_mem (N.𝒟.profileRel_mem _))
      (N.𝒟.reindex_mem _ (X.inDom_mem hN k))
  relC r := match r with
    | .base r => N.M.rel r
    | .enc m => {u | (u 0).1 = X.σ m ∧ u 1 = u 0 ∧ X.InDom hN (nidx m) (u 0)}
    | .new f => {u | (∀ i, (u i).1 = X.flatSort (idx (X.sortAt f i))) ∧
        (∀ i, X.InDom hN (idx (X.sortAt f i)) (u i)) ∧ (X.symF f).Sat hN.tstr u}
  relC_dom r t ht i := by
    cases r with
    | base r =>
      have hs : (t i).1 = X.flatSort (bidx (F.sig.sortAt r i)) := by
        rw [X.sortAt_base_flat]; exact N.M.rel_sorts r t ht i
      exact ⟨Sorted.toSort N.M.U (t i) hs, (Sorted.inj_toSort N.M.U (t i) hs).symm, by
        show X.InDom hN (bidx (F.sig.sortAt r i)) (Sorted.inj N.M.U (Sorted.toSort N.M.U (t i) hs))
        exact X.inDom_bidx hN _ _⟩
    | enc m =>
      obtain ⟨h0, h1, hd⟩ := ht
      match i with
      | 0 =>
        have hs : (t 0).1 = X.flatSort (nidx m) := by rw [X.flatSort_nidx]; exact h0
        exact ⟨Sorted.toSort N.M.U (t 0) hs, (Sorted.inj_toSort N.M.U (t 0) hs).symm, by
          show X.InDom hN (nidx m) (Sorted.inj N.M.U (Sorted.toSort N.M.U (t 0) hs))
          rw [Sorted.inj_toSort]; exact hd⟩
      | 1 =>
        have hs : (t 1).1 = X.flatSort (bidx (X.σ m)) := by rw [X.flatSort_bidx, h1]; exact h0
        exact ⟨Sorted.toSort N.M.U (t 1) hs, (Sorted.inj_toSort N.M.U (t 1) hs).symm, by
          show X.InDom hN (bidx (X.σ m)) (Sorted.inj N.M.U (Sorted.toSort N.M.U (t 1) hs))
          exact X.inDom_bidx hN _ _⟩
    | new f =>
      obtain ⟨hs, hd, -⟩ := ht
      exact ⟨Sorted.toSort N.M.U (t i) (hs i), (Sorted.inj_toSort N.M.U (t i) (hs i)).symm, by
        show X.InDom hN (idx (X.sortAt f i)) (Sorted.inj N.M.U (Sorted.toSort N.M.U (t i) (hs i)))
        rw [Sorted.inj_toSort]; exact hd i⟩
  relC_congr r t t' h ht := by
    have e : t' = t := by
      funext i
      obtain ⟨x, x', hx, hx', hxx', -⟩ := h i
      rw [hx, hx', hxx']
    rw [e]; exact ht
  relC_def r := by
    cases r with
    | base r => exact N.𝒟.rel_mem r
    | enc m =>
      show {u | (u 0).1 = X.σ m ∧ u 1 = u 0 ∧ X.InDom hN (nidx m) (u 0)} ∈ N.𝒟.D 2
      have e : ({u | (u 0).1 = X.σ m ∧ u 1 = u 0 ∧ X.InDom hN (nidx m) (u 0)} : Sorted.Rel N.M.U 2) =
          Sorted.reindex N.M.U (fun _ : Fin 1 => (0 : Fin 2)) (Sorted.sortRel N.M.U (X.σ m)) ∩
            Sorted.reindex N.M.U ![1, 0] (Sorted.eqRel N.M.U) ∩
            Sorted.reindex N.M.U (fun _ : Fin 1 => (0 : Fin 2)) {t | X.InDom hN (nidx m) (t 0)} := by
        ext u
        show ((u 0).1 = X.σ m ∧ u 1 = u 0 ∧ X.InDom hN (nidx m) (u 0)) ↔
          (((u ∘ fun _ : Fin 1 => (0 : Fin 2)) 0).1 = X.σ m ∧ (u ∘ ![1, 0]) 0 = (u ∘ ![1, 0]) 1) ∧
            X.InDom hN (nidx m) ((u ∘ fun _ : Fin 1 => (0 : Fin 2)) 0)
        exact ⟨fun ⟨h0, h1, hd⟩ => ⟨⟨h0, h1⟩, hd⟩, fun ⟨⟨h0, h1⟩, hd⟩ => ⟨h0, h1, hd⟩⟩
      rw [e]
      exact N.𝒟.inter_mem (N.𝒟.inter_mem (N.𝒟.reindex_mem _ (N.𝒟.sort_mem _))
        (N.𝒟.reindex_mem _ N.𝒟.eq_mem)) (N.𝒟.reindex_mem _ (X.inDom_mem hN _))
    | new f =>
      show {u | (∀ i, (u i).1 = X.flatSort (idx (X.sortAt f i))) ∧
        (∀ i, X.InDom hN (idx (X.sortAt f i)) (u i)) ∧ (X.symF f).Sat hN.tstr u} ∈ N.𝒟.D _
      have e : ({u | (∀ i, (u i).1 = X.flatSort (idx (X.sortAt f i))) ∧
          (∀ i, X.InDom hN (idx (X.sortAt f i)) (u i)) ∧ (X.symF f).Sat hN.tstr u} :
            Sorted.Rel N.M.U (X.arity f)) =
          Sorted.profileRel N.M.U (fun i => X.flatSort (idx (X.sortAt f i))) ∩
            (⋂ i, Sorted.reindex N.M.U (fun _ : Fin 1 => i) {t | X.InDom hN (idx (X.sortAt f i)) (t 0)}) ∩
            (X.symF f).Def hN.tstr := by
        ext u
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨⟨h1, Set.mem_iInter.2 fun i => ?_⟩, h3⟩
          exact h2 i
        · rintro ⟨⟨h1, h2⟩, h3⟩
          exact ⟨h1, fun i => Set.mem_iInter.1 h2 i, h3⟩
      refine Eq.mpr (congrArg (· ∈ N.𝒟.D (X.arity f)) e) ?_
      exact N.𝒟.inter_mem (N.𝒟.inter_mem (N.𝒟.profileRel_mem _)
        (N.𝒟.iInter_mem _ fun i => N.𝒟.reindex_mem _ (X.inDom_mem hN _)))
        ((X.symF f).def_mem (ClauseFamily.ΔSys N hN.wf).toStrSys)

/-- The expanded model. -/
noncomputable abbrev expModel : Str.{u} X.sig := (X.expInterp hN).model

/-- Its class system: the one induced by the interpretation. -/
noncomputable abbrev expSys : StrSys (X.expModel hN) := (X.expInterp hN).induced

/-! ### The base reduct of the expanded model is (isomorphic to) `N` -/

theorem expInterp_eqv_iff (k : ℕ) (x y : N.M.U (X.flatSort k)) :
    (X.expInterp hN).eqv k x y ↔ x = y ∧ x ∈ X.expDom hN k := Iff.rfl

/-- Representation is injective in the represented element (the equivalence is equality). -/
theorem expInterp_Rep_left_unique {y y' : Sorted.El N.M.U} {z : Sorted.El (X.expInterp hN).Carrier}
    (h : (X.expInterp hN).Rep y z) (h' : (X.expInterp hN).Rep y' z) : y = y' := by
  obtain ⟨x, x', rfl, rfl, heqv⟩ := (X.expInterp hN).Rep_eqv rfl h h'
  rw [heqv.1]

/-- The base target of the expansion interpretation. -/
noncomputable abbrev expBase : GenInterp N.M.U N.𝒟.toClassSys F.sig := (X.expInterp hN).baseTarget X

theorem expBase_Rep_left_unique {y y' : Sorted.El N.M.U} {z : Sorted.El (X.expBase hN).Carrier}
    (h : (X.expBase hN).Rep y z) (h' : (X.expBase hN).Rep y' z) : y = y' :=
  X.expInterp_Rep_left_unique hN (((X.expInterp hN).baseTarget_Rep X _ _).1 h)
    (((X.expInterp hN).baseTarget_Rep X _ _).1 h')

theorem exists_expBase_rep (n : ℕ) (x : N.M.U n) :
    ∃ q : (X.expBase hN).Carrier n, (X.expBase hN).Rep (Sorted.inj N.M.U x) (Sorted.inj _ q) := by
  let x' : N.M.U (X.flatSort (bidx n)) := cast (congrArg N.M.U (X.flatSort_bidx n).symm) x
  have hx' : x' ∈ (X.expBase hN).dom n := X.inDom_bidx hN n _
  refine ⟨(X.expBase hN).cls ⟨x', hx'⟩, n, ⟨x', hx'⟩, ?_, rfl⟩
  exact (sigma_cast_eq (β := N.M.U) (X.flatSort_bidx n).symm x).symm

/-- The isomorphism from `N` onto the model of the base target. -/
noncomputable def expBaseIso₀ : GenIso N.M (X.expBase hN).model where
  toFun n x := Classical.choose (X.exists_expBase_rep hN n x)
  bijective n := by
    constructor
    · intro x y hxy
      have hx := Classical.choose_spec (X.exists_expBase_rep hN n x)
      have hy := Classical.choose_spec (X.exists_expBase_rep hN n y)
      have hxy' : Classical.choose (X.exists_expBase_rep hN n x) =
          Classical.choose (X.exists_expBase_rep hN n y) := hxy
      rw [hxy'] at hx
      exact Sorted.inj_injective N.M.U (X.expBase_Rep_left_unique hN hx hy)
    · intro q
      obtain ⟨x', rfl⟩ := Quotient.exists_rep q
      let x : N.M.U n := cast (congrArg N.M.U (X.flatSort_bidx n)) x'.1
      refine ⟨x, ?_⟩
      have hx := Classical.choose_spec (X.exists_expBase_rep hN n x)
      have hq : (X.expBase hN).Rep (Sorted.inj N.M.U x) (Sorted.inj _ ((X.expBase hN).cls x')) := by
        refine ⟨n, x', ?_, rfl⟩
        exact sigma_cast_eq (β := N.M.U) (X.flatSort_bidx n) x'.1
      exact ((X.expBase hN).model_inj_eq_iff _ _).1 ((X.expBase hN).Rep_unique hx hq rfl)
  rel_iff r t := by
    show t ∈ N.M.rel r ↔ (fun i => ⟨(t i).1, Classical.choose (X.exists_expBase_rep hN (t i).1 (t i).2)⟩) ∈
      (X.expBase hN).relQ r
    have hrep : ∀ z : Sorted.El N.M.U, (X.expBase hN).Rep z
        ⟨z.1, Classical.choose (X.exists_expBase_rep hN z.1 z.2)⟩ := fun z =>
      Classical.choose_spec (X.exists_expBase_rep hN z.1 z.2)
    constructor
    · intro h
      exact ⟨t, fun i => ⟨N.M.rel_sorts r t h i, hrep (t i)⟩, h⟩
    · rintro ⟨u, hu, hrel⟩
      have : u = t := funext fun i => X.expBase_Rep_left_unique hN (hu i).2 (hrep (t i))
      rw [this] at hrel; exact hrel

theorem expBaseIso₀_Rep (z : Sorted.El N.M.U) :
    (X.expBase hN).Rep z ((X.expBaseIso₀ hN).mapEl z) :=
  Classical.choose_spec (X.exists_expBase_rep hN z.1 z.2)

/-- The isomorphism from `N` onto the base reduct of the expanded model. -/
noncomputable def expBaseIso : GenIso N.M (X.baseStr (X.expModel hN)) :=
  (X.expBaseIso₀ hN).trans ((X.expInterp hN).baseIso X).symm

theorem baseIso_symm_mapEl (z : Sorted.El (X.expBase hN).model.U) :
    ((X.expInterp hN).baseIso X).symm.mapEl z = z :=
  ((X.expInterp hN).baseIso X).mapEl_symm_apply z

theorem expBaseIso_mapEl (z : Sorted.El N.M.U) :
    (X.expBaseIso hN).mapEl z = (X.expBaseIso₀ hN).mapEl z := by
  show ((X.expInterp hN).baseIso X).symm.mapEl ((X.expBaseIso₀ hN).mapEl z) = _
  exact X.baseIso_symm_mapEl hN _

/-- The graph of the isomorphism, through representation: `w` is the image of
`z` iff `z` represents `w`. -/
theorem expBaseIso_eq_iff (z : Sorted.El N.M.U) (w : Sorted.El (X.baseU (X.expModel hN))) :
    (X.expBaseIso hN).mapEl z = w ↔ (X.expInterp hN).Rep z ((X.dbl (X.expModel hN)).el w) := by
  rw [X.expBaseIso_mapEl hN, ← (X.expInterp hN).baseTarget_Rep X]
  constructor
  · rintro rfl; exact X.expBaseIso₀_Rep hN z
  · intro h
    exact (X.expBase hN).Rep_unique (X.expBaseIso₀_Rep hN z) h
      (((X.expBase hN).Rep_fst h).trans (X.flatSort_bidx w.1))

/-- The class system of the base reduct agrees with the transported one on
the classes of a single sort. -/
theorem expSys_base_liftRel (n k : ℕ) (C : Set (Fin k → (X.baseStr (X.expModel hN)).U n)) :
    Sorted.liftRel _ C ∈ ((X.expBaseIso hN).mapSys N.𝒟).D k ↔
      Sorted.liftRel _ C ∈ (X.baseSys (X.expSys hN)).D k := by
  -- the pulled-back class
  have key : ∀ (b : Fin k → ℕ) (b' : Fin k → ℕ),
      (X.expInterp hN).preimage b' ((X.dbl (X.expModel hN)).img
        (Sorted.liftRel (X.baseU (X.expModel hN)) C ∩ Sorted.profileRel (X.baseU (X.expModel hN)) b)) =
      if (∀ j, b j = n) ∧ (∀ j, b' j = bidx n) then
        {u | (fun j => (X.expBaseIso hN).mapEl (u j)) ∈ Sorted.liftRel (X.baseU (X.expModel hN)) C}
      else ∅ := by
    intro b b'
    split_ifs with hbb
    · obtain ⟨hb, hb'⟩ := hbb
      ext u
      constructor
      · rintro ⟨q, hq, v, ⟨⟨s, hvs, hsC⟩, -⟩, rfl⟩
        refine ⟨s, fun j => ?_, hsC⟩
        show (X.expBaseIso hN).mapEl (u j) = Sorted.inj _ (s j)
        refine (X.expBaseIso_eq_iff hN _ _).2 ?_
        have h2 : (X.expInterp hN).Rep (u j) ((X.dbl (X.expModel hN)).el (v j)) := (hq j).2
        rw [hvs j] at h2; exact h2
      · rintro ⟨s, hs, hsC⟩
        refine ⟨fun j => (X.dbl (X.expModel hN)).el (Sorted.inj _ (s j)), fun j => ⟨?_, ?_⟩,
          fun j => Sorted.inj _ (s j), ⟨⟨s, fun j => rfl, hsC⟩, fun j => ?_⟩, rfl⟩
        · show bidx n = b' j
          exact (hb' j).symm
        · rw [← X.expBaseIso_eq_iff hN]; exact hs j
        · show n = b j
          exact (hb j).symm
    · ext u
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨q, hq, v, ⟨⟨s, hvs, -⟩, hvb⟩, rfl⟩
      apply hbb
      refine ⟨fun j => ?_, fun j => ?_⟩
      · have h0 : (v j).1 = b j := hvb j
        rw [hvs j] at h0; exact h0.symm
      · have h1 : ((X.dbl (X.expModel hN)).el (v j)).1 = b' j := (hq j).1
        rw [hvs j] at h1; exact h1.symm
  constructor
  · intro h b
    refine ((X.expInterp hN).mem_induced_iff _).2 fun b' => ?_
    refine Eq.mpr (congrArg (· ∈ N.𝒟.D k) (key b b')) ?_
    split_ifs
    · exact h
    · exact N.𝒟.empty_mem k
  · intro h
    have h1 := ((X.expInterp hN).mem_induced_iff _).1 (h fun _ => n) (fun _ => bidx n)
    have h2 := Eq.mp (congrArg (· ∈ N.𝒟.D k) (key (fun _ => n) (fun _ => bidx n))) h1
    rw [if_pos ⟨fun _ => rfl, fun _ => rfl⟩] at h2
    exact h2

/-- The base reduct of the expanded model, with the class system of the
reduct, is a model of `T(𝔉)`. -/
theorem expand_base : F.IsGenModel ⟨X.baseStr (X.expModel hN), X.baseSys (X.expSys hN)⟩ :=
  (ClauseFamily.IsGenModel.transport (X.expBaseIso hN) hN).congr (X.expSys_base_liftRel hN)

/-! ### The encodings and the further symbols -/

theorem Rep_sort {y : Sorted.El N.M.U} {z : Sorted.El (X.expInterp hN).Carrier}
    (h : (X.expInterp hN).Rep y z) : y.1 = X.flatSort z.1 := (X.expInterp hN).Rep_fst h

theorem Rep_inDom {y : Sorted.El N.M.U} {z : Sorted.El (X.expInterp hN).Carrier}
    (h : (X.expInterp hN).Rep y z) : X.InDom hN z.1 y := by
  obtain ⟨k, x, rfl, rfl⟩ := h
  exact x.2

theorem exists_rep_of_sort (k : ℕ) (y : Sorted.El N.M.U) (hy : y.1 = X.flatSort k) (hd : X.InDom hN k y) :
    ∃ q : (X.expInterp hN).Carrier k, (X.expInterp hN).Rep y (Sorted.inj _ q) := by
  have hx : Sorted.toSort N.M.U y hy ∈ X.expDom hN k := by
    show X.InDom hN k (Sorted.inj N.M.U (Sorted.toSort N.M.U y hy))
    rw [Sorted.inj_toSort]; exact hd
  exact ⟨(X.expInterp hN).cls ⟨Sorted.toSort N.M.U y hy, hx⟩, k, ⟨_, hx⟩,
    (Sorted.inj_toSort N.M.U y hy).symm, rfl⟩

/-- The interpreted encoding: two elements are related when they have a common
representative. -/
theorem relQ_enc_iff (m : ℕ) (z w : Sorted.El (X.expInterp hN).Carrier) :
    ![z, w] ∈ (X.expInterp hN).relQ (.enc m) ↔
      z.1 = nidx m ∧ w.1 = bidx (X.σ m) ∧ ∃ y, (X.expInterp hN).Rep y z ∧ (X.expInterp hN).Rep y w := by
  constructor
  · rintro ⟨u, hu, h0, h1, -⟩
    refine ⟨(hu 0).1, (hu 1).1, u 0, (hu 0).2, ?_⟩
    have := (hu 1).2
    rw [h1] at this; exact this
  · rintro ⟨hz, hw, y, hyz, hyw⟩
    refine ⟨![y, y], fun i => ?_, ?_, rfl, ?_⟩
    · match i with
      | 0 => exact ⟨hz, hyz⟩
      | 1 => exact ⟨hw, hyw⟩
    · show y.1 = X.σ m
      rw [X.Rep_sort hN hyz, hz, X.flatSort_nidx]
    · show X.InDom hN (nidx m) y
      have := X.Rep_inDom hN hyz
      rw [hz] at this; exact this

/-- Codes in the expanded model: `w` codes `z` when they have a common representative. -/
theorem code_iff (z : Sorted.El (X.expInterp hN).Carrier) (w : Sorted.El (X.baseU (X.expModel hN))) :
    X.Code (X.expModel hN) z w ↔
      ∃ y, (X.expInterp hN).Rep y z ∧ (X.expInterp hN).Rep y ((X.dbl (X.expModel hN)).el w) := by
  unfold Code
  split_ifs with h
  · constructor
    · intro h'
      obtain ⟨y, hy⟩ := (X.expInterp hN).exists_Rep z
      exact ⟨y, hy, by rw [h']; exact hy⟩
    · rintro ⟨y, h1, h2⟩
      refine (X.expInterp hN).Rep_unique h2 h1 ?_
      have e1 : y.1 = X.flatSort z.1 := X.Rep_sort hN h1
      have e2 : y.1 = X.flatSort (bidx w.1) := X.Rep_sort hN h2
      have e3 : X.flatSort (bidx w.1) = w.1 := X.flatSort_bidx _
      have e4 : X.flatSort z.1 = z.1 / 2 := by unfold flatSort; rw [if_pos h]
      show bidx w.1 = z.1
      rw [e3] at e2
      rw [e4] at e1
      rw [← e2, e1]
      exact (eq_bidx_of_even h).symm
  · refine (X.relQ_enc_iff hN (z.1 / 2) z _).trans ?_
    constructor
    · rintro ⟨-, -, y, h1, h2⟩; exact ⟨y, h1, h2⟩
    · rintro ⟨y, h1, h2⟩
      refine ⟨eq_nidx_of_odd h, ?_, y, h1, h2⟩
      have e1 : y.1 = X.flatSort z.1 := X.Rep_sort hN h1
      have e2 : y.1 = X.flatSort (bidx w.1) := X.Rep_sort hN h2
      have e3 : X.flatSort (bidx w.1) = w.1 := X.flatSort_bidx _
      have e4 : X.flatSort z.1 = X.σ (z.1 / 2) := by unfold flatSort; rw [if_neg h]
      show bidx w.1 = bidx (X.σ (z.1 / 2))
      rw [e3] at e2
      rw [e4] at e1
      rw [← e2, e1]

/-- Satisfaction transports from `N` to the base reduct of the expanded model. -/
theorem sat_transport {k : ℕ} {s : Fin k → ℕ} (φ : Formula TowerSig k s) (u : Fin k → Sorted.El N.M.U) :
    φ.Sat hN.tstr u ↔
      φ.Sat (ClauseFamily.Δ (X.baseStr (X.expModel hN)) (X.expand_base hN).wf).toStr
        (fun i => (X.expBaseIso hN).mapEl (u i)) :=
  φ.sat_map ((X.expBaseIso hN).toTowerIso hN.wf (X.expand_base hN).wf).toGenIso u

/-- **The canonical expansion is a model of the expanded theory.** -/
theorem expand_isModel : X.IsModel ⟨X.expModel hN, X.expSys hN⟩ where
  base := X.expand_base hN
  enc_total m z := by
    obtain ⟨x, rfl⟩ := Quotient.exists_rep z
    have hy : (Sorted.inj N.M.U x.1).1 = X.flatSort (bidx (X.σ m)) := by
      show X.flatSort (nidx m) = X.flatSort (bidx (X.σ m))
      rw [X.flatSort_nidx, X.flatSort_bidx]
    obtain ⟨w, hw⟩ := X.exists_rep_of_sort hN (bidx (X.σ m)) (Sorted.inj N.M.U x.1) hy
      (X.inDom_bidx hN _ _)
    refine ⟨w, (X.relQ_enc_iff hN m _ _).2 ⟨rfl, rfl, Sorted.inj N.M.U x.1, ⟨nidx m, x, rfl, rfl⟩, hw⟩⟩
  enc_unique m z w w' h h' := by
    obtain ⟨-, -, y, hyz, hyw⟩ := (X.relQ_enc_iff hN m _ _).1 h
    obtain ⟨-, -, y', hyz', hyw'⟩ := (X.relQ_enc_iff hN m _ _).1 h'
    have : y = y' := X.expInterp_Rep_left_unique hN hyz hyz'
    subst this
    exact ((X.expInterp hN).model_inj_eq_iff _ _).1 ((X.expInterp hN).Rep_unique hyw hyw' rfl)
  enc_inj m z z' w h h' := by
    obtain ⟨-, -, y, hyz, hyw⟩ := (X.relQ_enc_iff hN m _ _).1 h
    obtain ⟨-, -, y', hyz', hyw'⟩ := (X.relQ_enc_iff hN m _ _).1 h'
    have : y = y' := X.expInterp_Rep_left_unique hN hyw hyw'
    subst this
    exact ((X.expInterp hN).model_inj_eq_iff _ _).1 ((X.expInterp hN).Rep_unique hyz hyz' rfl)
  enc_dom m w := by
    obtain ⟨y, hy⟩ := (X.expBaseIso hN).mapEl_surjective (Sorted.inj (X.baseU (X.expModel hN)) (n := X.σ m) w)
    have hyw : (X.expInterp hN).Rep y (Sorted.inj (X.expInterp hN).Carrier (n := bidx (X.σ m)) w) :=
      (X.expBaseIso_eq_iff hN y _).1 hy
    have hys : y.1 = X.σ m := by rw [X.Rep_sort hN hyw]; exact X.flatSort_bidx _
    have e : (![Sorted.inj (X.baseU (X.expModel hN)) (n := X.σ m) w] :
        Fin 1 → Sorted.El (X.baseStr (X.expModel hN)).U) = fun i => (X.expBaseIso hN).mapEl (![y] i) := by
      funext i
      match i with
      | 0 => exact hy.symm
    have hR : (X.domF m).Sat (ClauseFamily.Δ (X.baseStr (X.expModel hN)) (X.expand_base hN).wf).toStr
        ![Sorted.inj (X.baseU (X.expModel hN)) (n := X.σ m) w] ↔ X.InDom hN (nidx m) y := by
      rw [X.inDom_nidx_iff hN]
      refine Iff.trans ?_ (X.sat_transport hN (X.domF m) ![y]).symm
      exact Iff.of_eq (congrArg (fun t => (X.domF m).Sat
        (ClauseFamily.Δ (X.baseStr (X.expModel hN)) (X.expand_base hN).wf).toStr t) e)
    refine Iff.trans ?_ hR.symm
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨-, -, y', hyz, hyw'⟩ := (X.relQ_enc_iff hN m _ _).1 hz
      have : y' = y := X.expInterp_Rep_left_unique hN hyw' hyw
      subst this
      have := X.Rep_inDom hN hyz
      exact this
    · intro hd
      obtain ⟨z, hz⟩ := X.exists_rep_of_sort hN (nidx m) y (by rw [hys, X.flatSort_nidx]) hd
      exact ⟨z, (X.relQ_enc_iff hN m _ _).2 ⟨rfl, rfl, y, hz, hyw⟩⟩
  sym f t := by
    constructor
    · rintro ⟨u, hu, hs, hd, hsat⟩
      refine ⟨fun i => (hu i).1, fun i => (X.expBaseIso hN).mapEl (u i), fun i => ?_, ?_⟩
      · exact (X.code_iff hN _ _).2 ⟨u i, (hu i).2, (X.expBaseIso_eq_iff hN _ _).1 rfl⟩
      · exact (X.sat_transport hN _ u).1 hsat
    · rintro ⟨hs, c, hc, hsat⟩
      have hc' : ∀ i, ∃ y, (X.expInterp hN).Rep y (t i) ∧ (X.expBaseIso hN).mapEl y = c i := by
        intro i
        obtain ⟨y, h1, h2⟩ := (X.code_iff hN _ _).1 (hc i)
        exact ⟨y, h1, (X.expBaseIso_eq_iff hN _ _).2 h2⟩
      choose u hu using hc'
      refine ⟨u, fun i => ⟨hs i, (hu i).1⟩, fun i => ?_, fun i => ?_, ?_⟩
      · rw [X.Rep_sort hN (hu i).1, hs i]
      · have := X.Rep_inDom hN (hu i).1
        rw [hs i] at this; exact this
      · rw [X.sat_transport hN]
        have : (fun i => (X.expBaseIso hN).mapEl (u i)) = c := funext fun i => (hu i).2
        rw [this]; exact hsat

end Expand

end SortExp

end SolidLean.Solid
