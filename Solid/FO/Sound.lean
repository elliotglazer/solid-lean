import Solid.FO.Bridge

/-!
# From semantic models to the sentences

The converse of `FO/Bridge.lean`: a structure that is a model of `T(𝔉)` in
the semantic sense, with its definable class system, satisfies every
sentence of `TLax` (`models_of_isGenModel`).  Together with
`isGenModel_of_models` this identifies the sentences with the semantic
axioms: `M.Models (TLax …) ↔ IsGenModel ⟨M, M.defSys⟩` (`models_iff_isGenModel`).
-/

universe u

namespace SolidLean.Solid

open Classical

namespace ClauseFamily

variable {F : ClauseFamily.{u}} {M : Str.{u} F.sig}

section Converse

variable (hwf : IsWF M)

/-- The underlying tower of a well-formed structure. -/
noncomputable abbrev Tv : MemTower.{u} := Δ M hwf

theorem holds_inl_of_tower {σ : Sentence TowerSig} (h : Sentence.Holds σ (Tv hwf).toStr) :
    Sentence.Holds (σ.inl (F := F)) M := by
  rw [Holds_inl, ← Δ_toStr_eq hwf]
  exact h

theorem holds_toSentence_of {n : ℕ} {φ : TF 0 (fun _ => n)}
    (h : φ.Sat (Tv hwf).toStr (fun l => (Tv hwf).inj ((fun i : Fin 0 => (i.elim0 : (Tv hwf).U n)) l))) :
    Sentence.Holds ((TF.toSentence φ).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  refine (TF.Holds_toSentence _ φ).2 ?_
  have e : (Fin.elim0 : Fin 0 → (Tv hwf).El) =
      fun l => (Tv hwf).inj ((fun i : Fin 0 => (i.elim0 : (Tv hwf).U n)) l) :=
    funext fun i => i.elim0
  rw [e]
  exact h

variable (hT : IsTowerModel ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩)

theorem append_one' {α : Type*} {m : ℕ} (η : Fin m → α) (u : Fin 1 → α) :
    Fin.append η u = Fin.snoc (α := fun _ => α) η (u 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last]
    exact Fin.append_right η u 0
  · rw [Fin.snoc_castSucc]
    exact Fin.append_left η u j

theorem append_two' {α : Type*} {m : ℕ} (η : Fin m → α) (u : Fin 2 → α) :
    Fin.append η u = Fin.snoc (α := fun _ => α) (Fin.snoc (α := fun _ => α) η (u 0)) (u 1) := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have : Fin.castAdd 2 j = Fin.castSucc (Fin.castSucc j) := Fin.ext rfl
    rw [this, Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.append_right]
    match j with
    | ⟨0, _⟩ =>
      have : Fin.natAdd m (⟨0, by omega⟩ : Fin 2) = Fin.castSucc (Fin.last m) := Fin.ext rfl
      rw [this, Fin.snoc_castSucc, Fin.snoc_last]
      rfl
    | ⟨1, _⟩ =>
      have : Fin.natAdd m (⟨1, by omega⟩ : Fin 2) = Fin.last (m + 1) := Fin.ext rfl
      rw [this, Fin.snoc_last]
      rfl

include hwf hT

local macro "zf_simp" : tactic => `(tactic| simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two])

/-! ### The ZFC axioms at each sort -/

theorem holds_extAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.extAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.extAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).ext (v 0) (v 1)

theorem holds_emptyAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.emptyAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.emptyAx
  refine (TF.Sat_exC _ _ _).2 ?_
  zf_simp
  exact (hT.zfc n).empty

theorem holds_pairAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.pairAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.pairAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).pair (v 0) (v 1)

theorem holds_unionAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.unionAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.unionAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).union (v 0)

theorem holds_powerAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.powerAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.powerAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).power (v 0)

theorem holds_infAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.infAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.infAx
  refine (TF.Sat_exC _ _ _).2 ?_
  zf_simp
  exact (hT.zfc n).infinity

theorem holds_foundAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.foundAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.foundAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).foundation (v 0)

theorem holds_choiceAx (n : ℕ) : Sentence.Holds ((TF.toSentence (TF.choiceAx n)).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  unfold TF.choiceAx
  refine (TF.Sat_closeC _ n _ _).2 fun v => ?_
  zf_simp
  exact (hT.zfc n).choice (v 0)

/-! ### Well-formedness and the tower axioms -/

omit hT in
theorem holds_liftTotalAx (n : ℕ) : Sentence.Holds ((TF.liftTotalAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.liftTotalAx
  rw [Formula.Sat_closeAll]
  intro t ht
  rw [Formula.Sat_ex]
  have h0 : (t 0).1 = n := ht 0
  have hx : t 0 = (Tv hwf).inj (Sorted.toSort (Tv hwf).U (t 0) h0) := (Sorted.inj_toSort _ _ _).symm
  refine ⟨(Tv hwf).inj ((Tv hwf).j n (Sorted.toSort (Tv hwf).U (t 0) h0)), rfl, ?_⟩
  exact (TF.Sat_liftZF (Tv hwf) (i := 0)
    (t := Fin.snoc t ((Tv hwf).inj ((Tv hwf).j n (Sorted.toSort (Tv hwf).U (t 0) h0))))
    (Sorted.toSort (Tv hwf).U (t 0) h0) hx).2 rfl

omit hT in
theorem holds_liftUniqueAx (n : ℕ) : Sentence.Holds ((TF.liftUniqueAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.liftUniqueAx
  rw [Formula.Sat_closeAll]
  intro t ht
  rw [Formula.Sat_imp, Formula.Sat_imp]
  intro h1 h2
  have h1' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 0) (ht 0))
    (Sorted.inj_toSort _ _ _).symm).1 h1
  have h2' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 0) (ht 0))
    (Sorted.inj_toSort _ _ _).symm).1 h2
  refine (Formula.Sat_eq _ _ _ _).2 ?_
  rw [h1', h2']

omit hT in
theorem holds_bndExistsAx (n : ℕ) : Sentence.Holds ((TF.bndExistsAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.bndExistsAx
  rw [Formula.Sat_closeAll]
  intro t _
  rw [Formula.Sat_ex]
  exact ⟨(Tv hwf).inj ((Tv hwf).κ n), rfl, rfl⟩

omit hT in
theorem holds_bndUniqueAx (n : ℕ) : Sentence.Holds ((TF.bndUniqueAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.bndUniqueAx
  rw [Formula.Sat_closeAll]
  intro t _
  rw [Formula.Sat_imp, Formula.Sat_imp]
  intro h1 h2
  have h1' : t 0 = (Tv hwf).inj ((Tv hwf).κ n) := h1
  have h2' : t 1 = (Tv hwf).inj ((Tv hwf).κ n) := h2
  refine (Formula.Sat_eq _ _ _ _).2 ?_
  rw [h1', h2']

theorem holds_jInjAx (n : ℕ) : Sentence.Holds ((TF.jInjAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.jInjAx
  rw [Formula.Sat_closeAll]
  intro t ht
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_imp]
  intro h1 h2 h3
  have h1' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 0) (ht 0))
    (Sorted.inj_toSort _ _ _).symm).1 h1
  have h2' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 1) (ht 1))
    (Sorted.inj_toSort _ _ _).symm).1 h2
  have h3' : t 2 = t 3 := h3
  rw [h1', h2'] at h3'
  have h4 := hT.j_injective n _ _ (Sorted.inj_injective _ h3')
  refine (Formula.Sat_eq _ _ _ _).2 ?_
  rw [← Sorted.inj_toSort _ (t 0) (ht 0), ← Sorted.inj_toSort _ (t 1) (ht 1), h4]
  rfl

theorem holds_jMemAx (n : ℕ) : Sentence.Holds ((TF.jMemAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.jMemAx
  rw [Formula.Sat_closeAll]
  intro t ht
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_iff]
  intro h1 h2
  have h1' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 0) (ht 0))
    (Sorted.inj_toSort _ _ _).symm).1 h1
  have h2' := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort _ (t 1) (ht 1))
    (Sorted.inj_toSort _ _ _).symm).1 h2
  refine (TF.Sat_memF (Tv hwf) _ _ h1' h2').trans ?_
  refine (hT.j_mem_iff n _ _).trans ?_
  exact (TF.Sat_memF (Tv hwf) _ _ (Sorted.inj_toSort _ (t 0) (ht 0)).symm
    (Sorted.inj_toSort _ (t 1) (ht 1)).symm).symm

theorem holds_kappaInaccAx (n : ℕ) : Sentence.Holds ((TF.kappaInaccAx n).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  refine (TF.Sat_allC _ _ _).2 fun k => ?_
  rw [Formula.Sat_imp]
  intro hk
  have hk' : k = (Tv hwf).κ n := Sorted.inj_injective _ hk
  subst hk'
  exact (TF.Sat_inaccC (Tv hwf) _ 0 _).2 (hT.kappa_inaccessible n)

theorem holds_jImageAx (n : ℕ) : Sentence.Holds ((TF.jImageAx n).inl (F := F)) M := by
  apply holds_toSentence_of hwf
  obtain ⟨v, hV, hmem⟩ := hT.j_image n
  refine (TF.Sat_exC _ _ _).2 ⟨v, ?_⟩
  refine (TF.Sat_exC _ _ _).2 ⟨(Tv hwf).κ n, ?_⟩
  rw [Formula.Sat_and, Formula.Sat_and]
  refine ⟨rfl, (TF.Sat_isVC (Tv hwf) _ 1 0 _).2 hV, ?_⟩
  refine (TF.Sat_allC _ _ _).2 fun y => ?_
  rw [Formula.Sat_iff, Formula.Sat_ex]
  refine (TF.Sat_memC (Tv hwf) _ 2 0 _).trans ((hmem y).trans ?_)
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨(Tv hwf).inj x, rfl, (TF.Sat_liftZF (Tv hwf) x rfl).2 rfl⟩
  · rintro ⟨x', hx', h4⟩
    refine ⟨Sorted.toSort (Tv hwf).U x' hx', ?_⟩
    have h5 := (TF.Sat_liftZF (Tv hwf) (Sorted.toSort (Tv hwf).U x' hx')
      (show x' = (Tv hwf).inj (Sorted.toSort (Tv hwf).U x' hx') from
        (Sorted.inj_toSort (Tv hwf).U x' hx').symm)).1 h4
    exact Sorted.inj_injective (Tv hwf).U h5.symm

theorem holds_nextInaccAx (n : ℕ) : Sentence.Holds ((TF.nextInaccAx n).inl (F := F)) M := by
  apply holds_inl_of_tower hwf
  unfold TF.nextInaccAx
  rw [Formula.Sat_closeAll]
  intro t _
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_imp]
  intro h0 h1 h2
  have h0' : t 0 = (Tv hwf).inj ((Tv hwf).κ n) := h0
  have h1' := (TF.Sat_liftZF (Tv hwf) ((Tv hwf).κ n) h0').1 h1
  have h2' : t 2 = (Tv hwf).inj ((Tv hwf).κ (n + 1)) := h2
  refine (TF.Sat_at _ _ _ _).2 ?_
  have e : (fun i => t (![1, 2] i)) =
      fun l => (Tv hwf).inj ((![(Tv hwf).j (n + 1) ((Tv hwf).κ n), (Tv hwf).κ (n + 1)] :
        Fin 2 → (Tv hwf).U (n + 2)) l) := by
    funext i; match i with | 0 => exact h1' | 1 => exact h2'
  rw [e]
  exact (TF.Sat_nextInaccC (Tv hwf) _ 0 1 _).2 (hT.next_inaccessible n)

theorem holds_bottomAx : Sentence.Holds (TF.bottomAx.inl (F := F)) M := by
  apply holds_toSentence_of hwf
  refine (TF.Sat_allC _ _ _).2 fun k => ?_
  rw [Formula.Sat_imp]
  intro hk
  have hk' : k = (Tv hwf).κ 0 := Sorted.inj_injective _ hk
  subst hk'
  exact (TF.Sat_noGreatestInaccC (Tv hwf) _ 0 _).2 hT.bottom

/-! ### The schemes -/

omit hT in
/-- The class of a formula in one variable of sort `n`, with the other
variables fixed, is in the definable class system. -/
theorem defOn_one (n : ℕ) {m : ℕ} {base : Fin m → ℕ} (ψ : Formula F.sig (m + 1) (Fin.snoc base n))
    (t : Fin m → Sorted.El M.U) (ht : ∀ i, (t i).1 = base i) :
    (ΔSys ⟨M, M.defSys⟩ hwf).DefOn n 1
      {u : Fin 1 → M.U n | ψ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) t (Sorted.inj M.U (u 0)))} := by
  show ∀ s : Fin 1 → ℕ, Formula.SortedDef M s (Sorted.liftRel M.U _)
  intro s
  by_cases hs : s 0 = n
  · refine ⟨m, base, Formula.recast (fun i => by rw [append_one' base s, hs]) ψ, t, ht,
      fun u hu => ?_⟩
    rw [Formula.Sat_recast, append_one']
    constructor
    · rintro ⟨u', hu', hC⟩
      rw [hu' 0]
      exact hC
    · intro h
      refine ⟨fun _ => Sorted.toSort M.U (u 0) ((hu 0).trans hs), fun i => ?_, ?_⟩
      · rw [Subsingleton.elim i 0, Sorted.inj_toSort]
      · show ψ.Sat M (Fin.snoc t (Sorted.inj M.U (Sorted.toSort M.U (u 0) _)))
        rw [Sorted.inj_toSort]
        exact h
  · refine Formula.SortedDef.of_disjoint s fun u hu => ?_
    rintro ⟨u', hu', -⟩
    apply hs
    rw [← hu 0, hu' 0]

theorem holds_sepAx (n : ℕ) {m : ℕ} (base : Fin m → ℕ) (ψ : Formula F.sig (m + 1) (Fin.snoc base n)) :
    Sentence.Holds (F.sepAx n base ψ) M := by
  unfold sepAx
  rw [Formula.Sat_closeAll]
  intro t ht
  rw [Formula.Sat_all]
  intro x hx
  rw [Formula.Sat_ex]
  obtain ⟨s, hs⟩ := (hT.zfc n).separation (k := 0)
    {u : Fin 1 → M.U n | ψ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) t (Sorted.inj M.U (u 0)))}
    (defOn_one hwf n ψ t ht) Fin.elim0 (Sorted.toSort M.U x hx)
  refine ⟨Sorted.inj M.U s, rfl, ?_⟩
  rw [Formula.Sat_all]
  intro y hy
  rw [Formula.Sat_iff, Formula.Sat_and, Sat_memS, Sat_memS, sepBody_env]
  simp only [Fin.snoc_last, Fin.snoc_castSucc]
  rw [← Sorted.inj_toSort M.U y hy, ← Sorted.inj_toSort M.U x hx]
  exact hs (Sorted.toSort M.U y hy)

omit hT in
/-- The class of a formula in two variables of sort `n`, with the other
variables fixed, is in the definable class system. -/
theorem defOn_two (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n))
    (t : Fin m → Sorted.El M.U) (ht : ∀ i, (t i).1 = base i) :
    (ΔSys ⟨M, M.defSys⟩ hwf).DefOn n 2
      {u : Fin 2 → M.U n | ψ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U)
        (Fin.snoc (α := fun _ => Sorted.El M.U) t (Sorted.inj M.U (u 0))) (Sorted.inj M.U (u 1)))} := by
  show ∀ s : Fin 2 → ℕ, Formula.SortedDef M s (Sorted.liftRel M.U _)
  intro s
  by_cases hs : s 0 = n ∧ s 1 = n
  · refine ⟨m, base, Formula.recast (fun i => by rw [append_two' base s, hs.1, hs.2]) ψ, t, ht,
      fun u hu => ?_⟩
    rw [Formula.Sat_recast, append_two']
    constructor
    · rintro ⟨u', hu', hC⟩
      rw [hu' 0, hu' 1]
      exact hC
    · intro h
      refine ⟨![Sorted.toSort M.U (u 0) ((hu 0).trans hs.1), Sorted.toSort M.U (u 1) ((hu 1).trans hs.2)],
        fun i => ?_, ?_⟩
      · match i with
        | 0 => exact (Sorted.inj_toSort _ _ _).symm
        | 1 => exact (Sorted.inj_toSort _ _ _).symm
      · show ψ.Sat M (Fin.snoc (Fin.snoc t (Sorted.inj M.U (Sorted.toSort M.U (u 0) _)))
          (Sorted.inj M.U (Sorted.toSort M.U (u 1) _)))
        rw [Sorted.inj_toSort, Sorted.inj_toSort]
        exact h
  · refine Formula.SortedDef.of_disjoint s fun u hu => ?_
    rintro ⟨u', hu', -⟩
    apply hs
    constructor
    · rw [← hu 0, hu' 0]
    · rw [← hu 1, hu' 1]

theorem holds_repAx (n : ℕ) {m : ℕ} (base : Fin m → ℕ)
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) :
    Sentence.Holds (F.repAx n base ψ) M := by
  unfold repAx
  rw [Formula.Sat_closeAll]
  intro t' ht'
  obtain ⟨t, x, rfl⟩ : ∃ (t : Fin m → Sorted.El M.U) (x : Sorted.El M.U),
      t' = Fin.snoc (α := fun _ => Sorted.El M.U) t x :=
    ⟨Fin.init t', t' (Fin.last m), (Fin.snoc_init_self t').symm⟩
  have ht : ∀ i, (t i).1 = base i := fun i => by simpa using ht' i.castSucc
  have hx : x.1 = n := by simpa using ht' (Fin.last m)
  rw [Formula.Sat_imp]
  intro hA
  rw [Formula.Sat_ex]
  -- the class
  set C : Set (Fin 2 → M.U n) := {u | ψ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U)
    (Fin.snoc (α := fun _ => Sorted.El M.U) t (Sorted.inj M.U (u 0))) (Sorted.inj M.U (u 1)))} with hCdef
  have hread : ∀ (y z : M.U n),
      Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) Fin.elim0 y) z ∈ C ↔
        ψ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U)
          (Fin.snoc (α := fun _ => Sorted.El M.U) t (Sorted.inj M.U y)) (Sorted.inj M.U z)) :=
    fun y z => Iff.rfl
  -- functionality, read from the formula
  have hfun : ∀ y, (Tv hwf).mem y (Sorted.toSort M.U x hx) →
      ∃! z, Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) Fin.elim0 y) z ∈ C := by
    intro y hyx
    rw [Formula.Sat_all] at hA
    have h1 := hA (Sorted.inj M.U y) rfl
    rw [Formula.Sat_imp, Sat_memS] at h1
    simp only [Fin.snoc_last, Fin.snoc_castSucc] at h1
    have hyx' : ![Sorted.inj M.U y, x] ∈ M.rel (.inl (.memZ n)) := by
      rw [← Sorted.inj_toSort M.U x hx]; exact hyx
    have h2 := h1 hyx'
    rw [Formula.Sat_ex] at h2
    obtain ⟨z, hz, h3⟩ := h2
    rw [Formula.Sat_and, repBody1_env] at h3
    obtain ⟨h4, h5⟩ := h3
    refine ⟨Sorted.toSort M.U z hz, ?_, ?_⟩
    · beta_reduce
      refine (hread _ _).2 ?_
      rw [Sorted.inj_toSort]; exact h4
    · intro z' hz'
      have hz'' := (hread _ _).1 hz'
      rw [Formula.Sat_all] at h5
      have h6 := h5 (Sorted.inj M.U z') rfl
      rw [Formula.Sat_imp, repBody2_env] at h6
      have h7 := (Formula.Sat_eq _ _ _ _).1 (h6 hz'')
      simp only [Fin.snoc_last, Fin.snoc_castSucc] at h7
      apply Sorted.inj_injective M.U
      rw [Sorted.inj_toSort]
      exact h7
  obtain ⟨s, hs⟩ := (hT.zfc n).replacement (k := 0) C (defOn_two hwf n ψ t ht) Fin.elim0
    (Sorted.toSort M.U x hx) hfun
  refine ⟨Sorted.inj M.U s, rfl, ?_⟩
  rw [Formula.Sat_all]
  intro z hz
  rw [Formula.Sat_iff, Sat_memS, Formula.Sat_ex]
  simp only [Formula.Sat_and, Sat_memS, repBody3_env, Fin.snoc_last, Fin.snoc_castSucc]
  rw [← Sorted.inj_toSort M.U z hz, ← Sorted.inj_toSort M.U x hx]
  refine (hs (Sorted.toSort M.U z hz)).trans ?_
  constructor
  · rintro ⟨y, hyx, hC⟩
    exact ⟨Sorted.inj M.U y, rfl, hyx, (hread _ _).1 hC⟩
  · rintro ⟨y, hy, hyx, hψ⟩
    refine ⟨Sorted.toSort M.U y hy, ?_, ?_⟩
    · rw [← Sorted.inj_toSort M.U y hy] at hyx; exact hyx
    · refine (hread _ _).2 ?_
      rw [Sorted.inj_toSort]; exact hψ

/-! ### Assembly -/

theorem models_Hax_of : M.Models F.Hax := by
  rintro σ (⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
    ⟨n, m, base, ψ, rfl⟩ | ⟨n, m, base, ψ, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ |
    ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | ⟨n, rfl⟩ | rfl)
  · exact holds_extAx hwf hT n
  · exact holds_emptyAx hwf hT n
  · exact holds_pairAx hwf hT n
  · exact holds_unionAx hwf hT n
  · exact holds_powerAx hwf hT n
  · exact holds_infAx hwf hT n
  · exact holds_foundAx hwf hT n
  · exact holds_choiceAx hwf hT n
  · exact holds_sepAx hwf hT n base ψ
  · exact holds_repAx hwf hT n base ψ
  · exact holds_liftTotalAx hwf n
  · exact holds_liftUniqueAx hwf n
  · exact holds_bndExistsAx hwf n
  · exact holds_bndUniqueAx hwf n
  · exact holds_jInjAx hwf hT n
  · exact holds_jMemAx hwf hT n
  · exact holds_kappaInaccAx hwf hT n
  · exact holds_jImageAx hwf hT n
  · exact holds_nextInaccAx hwf hT n
  · exact holds_bottomAx hwf hT

end Converse

/-- The defining axioms hold when the symbols are interpreted by their
clauses. -/
theorem holds_defAx {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig}
    (hM : (ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩) (f : Sym) :
    Sentence.Holds (defAx Sym arity sortAt φ f) M := by
  unfold defAx
  rw [Formula.Sat_closeAll]
  intro t ht
  refine (Formula.Sat_iff _ _ _).2 ?_
  have hc := hM.clause f
  show (fun i => t i) ∈ M.rel (Sum.inr f) ↔ _
  rw [hc]
  show (φ f).Sat (Δ M hM.wf).toStr t ∧ (∀ i, (t i).1 = sortAt f i) ↔ _
  refine Iff.trans ?_ (Formula.Sat_inl M _ _).symm
  refine Iff.trans ?_ (Sat_Δ_toStr hM.wf _ _)
  exact ⟨fun h => h.1, fun h => ⟨h, ht⟩⟩

/-- **A semantic model of `T(𝔉)` satisfies the sentences of `T(𝔉)`.** -/
theorem models_of_isGenModel {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig}
    (hM : (ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩) :
    M.Models (TLax Sym arity sortAt φ) := by
  rintro σ (hσ | ⟨f, rfl⟩)
  · exact models_Hax_of hM.wf hM.tower σ hσ
  · exact holds_defAx hM f

/-- **The sentences of `T(𝔉)` are exactly its semantic axioms**, for a
structure with its definable class system. -/
theorem models_iff_isGenModel {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    (M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig) :
    M.Models (TLax Sym arity sortAt φ) ↔ (ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩ :=
  ⟨isGenModel_of_models, models_of_isGenModel⟩

end ClauseFamily

end SolidLean.Solid
