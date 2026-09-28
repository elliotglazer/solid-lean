import Solid.Gen.SortExp

/-!
# Extending isomorphisms of base reducts to expanded models

An isomorphism `h₀` between the base reducts of two models of a definable-sort
expansion extends uniquely to an isomorphism of the expanded models: on a new
sort `m` it sends `z` to the unique `z'` whose encoding is `h₀` of the
encoding of `z`.  The extension exists because the domain formula is
invariant under `h₀` (satisfaction of tower formulas is invariant under
isomorphisms), and it respects the further symbols because their clauses
are.
-/

universe u

namespace SolidLean.Solid

open Classical

namespace SortExp

variable {F : ClauseFamily.{u}} (X : SortExp F)

section Extend

variable {N₀ N₁ : StrWithSys.{u} X.sig} (hN₀ : X.IsModel N₀) (hN₁ : X.IsModel N₁)
variable (h₀ : GenIso (X.baseStr N₀.M) (X.baseStr N₁.M))

include hN₀ hN₁ h₀

/-- Tower formulas over the base reducts are invariant under `h₀`. -/
theorem sat_base {k : ℕ} {s : Fin k → ℕ} (φ : Formula TowerSig k s)
    (t : Fin k → Sorted.El (X.baseU N₀.M)) :
    φ.Sat (ClauseFamily.Δ (X.baseStr N₀.M) hN₀.base.wf).toStr t ↔
      φ.Sat (ClauseFamily.Δ (X.baseStr N₁.M) hN₁.base.wf).toStr (fun i => h₀.mapEl (t i)) :=
  φ.sat_map (h₀.toTowerIso hN₀.base.wf hN₁.base.wf).toGenIso t

theorem sat_domF (m : ℕ) (w : N₀.M.U (bidx (X.σ m))) :
    (X.domF m).Sat (ClauseFamily.Δ (X.baseStr N₀.M) hN₀.base.wf).toStr
        ![Sorted.inj (X.baseU N₀.M) (n := X.σ m) w] ↔
      (X.domF m).Sat (ClauseFamily.Δ (X.baseStr N₁.M) hN₁.base.wf).toStr
        ![Sorted.inj (X.baseU N₁.M) (n := X.σ m) (h₀.toFun (X.σ m) w)] := by
  have h1 := X.sat_base hN₀ hN₁ h₀ (X.domF m) ![Sorted.inj (X.baseU N₀.M) (n := X.σ m) w]
  have e : (fun i => h₀.mapEl (![Sorted.inj (X.baseU N₀.M) (n := X.σ m) w] i)) =
      ![Sorted.inj (X.baseU N₁.M) (n := X.σ m) (h₀.toFun (X.σ m) w)] := by
    funext i
    match i with
    | 0 => rfl
  rw [e] at h1
  exact h1

theorem exists_new (m : ℕ) (z : N₀.M.U (nidx m)) :
    ∃ z' : N₁.M.U (nidx m), ![Sorted.inj N₁.M.U z',
      Sorted.inj N₁.M.U (h₀.toFun (X.σ m) (X.encFun hN₀ m z))] ∈ N₁.M.rel (.enc m) := by
  apply (hN₁.enc_dom m _).2
  rw [← X.sat_domF hN₀ hN₁ h₀]
  exact (hN₀.enc_dom m _).1 ⟨z, X.encFun_spec hN₀ m z⟩

/-- The extension of `h₀` to new sort `m`. -/
noncomputable def newFun (m : ℕ) (z : N₀.M.U (nidx m)) : N₁.M.U (nidx m) :=
  Classical.choose (X.exists_new hN₀ hN₁ h₀ m z)

theorem newFun_spec (m : ℕ) (z : N₀.M.U (nidx m)) :
    ![Sorted.inj N₁.M.U (X.newFun hN₀ hN₁ h₀ m z),
      Sorted.inj N₁.M.U (h₀.toFun (X.σ m) (X.encFun hN₀ m z))] ∈ N₁.M.rel (.enc m) :=
  Classical.choose_spec (X.exists_new hN₀ hN₁ h₀ m z)

theorem encFun_newFun (m : ℕ) (z : N₀.M.U (nidx m)) :
    X.encFun hN₁ m (X.newFun hN₀ hN₁ h₀ m z) = h₀.toFun (X.σ m) (X.encFun hN₀ m z) :=
  ((X.enc_iff hN₁ m _ _).1 (X.newFun_spec hN₀ hN₁ h₀ m z)).symm

theorem newFun_bijective (m : ℕ) : Function.Bijective (X.newFun hN₀ hN₁ h₀ m) := by
  constructor
  · intro z z' h
    have h1 := congrArg (X.encFun hN₁ m) h
    rw [X.encFun_newFun, X.encFun_newFun] at h1
    exact X.encFun_injective hN₀ m ((h₀.bijective (X.σ m)).1 h1)
  · intro z'
    obtain ⟨w, hw⟩ : ∃ w : N₀.M.U (bidx (X.σ m)), h₀.toFun (X.σ m) w = X.encFun hN₁ m z' :=
      (h₀.bijective (X.σ m)).2 _
    have hdom : (X.domF m).Sat (ClauseFamily.Δ (X.baseStr N₀.M) hN₀.base.wf).toStr
        ![Sorted.inj (X.baseU N₀.M) (n := X.σ m) w] := by
      rw [X.sat_domF hN₀ hN₁ h₀, hw]
      exact (hN₁.enc_dom m _).1 ⟨z', X.encFun_spec hN₁ m z'⟩
    obtain ⟨z, hz⟩ := (hN₀.enc_dom m w).2 hdom
    have hzw : w = X.encFun hN₀ m z := (X.enc_iff hN₀ m z w).1 hz
    refine ⟨z, X.encFun_injective hN₁ m ?_⟩
    rw [X.encFun_newFun, ← hzw, hw]

/-- The extension of `h₀` to all sorts. -/
noncomputable def extFun (k : ℕ) : N₀.M.U k → N₁.M.U k :=
  parityDep (fun k => k) (fun n => h₀.toFun n) (X.newFun hN₀ hN₁ h₀) k

/-- The extension on the union of sorts. -/
noncomputable def extEl (z : Sorted.El N₀.M.U) : Sorted.El N₁.M.U :=
  ⟨z.1, X.extFun hN₀ hN₁ h₀ z.1 z.2⟩

@[simp] theorem extEl_fst (z : Sorted.El N₀.M.U) : (X.extEl hN₀ hN₁ h₀ z).1 = z.1 := rfl

theorem extFun_bidx (n : ℕ) (x : N₀.M.U (bidx n)) :
    X.extFun hN₀ hN₁ h₀ (bidx n) x = h₀.toFun n x :=
  parityDep_bidx (fun k => k) (fun n => h₀.toFun n) (X.newFun hN₀ hN₁ h₀) n x

theorem extFun_nidx (m : ℕ) (z : N₀.M.U (nidx m)) :
    X.extFun hN₀ hN₁ h₀ (nidx m) z = X.newFun hN₀ hN₁ h₀ m z :=
  parityDep_nidx (fun k => k) (fun n => h₀.toFun n) (X.newFun hN₀ hN₁ h₀) m z

theorem extEl_bidx (n : ℕ) (x : N₀.M.U (bidx n)) :
    X.extEl hN₀ hN₁ h₀ (Sorted.inj N₀.M.U x) = Sorted.inj N₁.M.U (h₀.toFun n x) := by
  show (⟨bidx n, X.extFun hN₀ hN₁ h₀ (bidx n) x⟩ : Sorted.El N₁.M.U) = _
  rw [X.extFun_bidx hN₀ hN₁ h₀]

theorem extEl_dbl (w : Sorted.El (X.baseU N₀.M)) :
    X.extEl hN₀ hN₁ h₀ ((X.dbl N₀.M).el w) = (X.dbl N₁.M).el (h₀.mapEl w) := by
  obtain ⟨n, x⟩ := w
  exact X.extEl_bidx hN₀ hN₁ h₀ n x

theorem extEl_nidx (m : ℕ) (z : N₀.M.U (nidx m)) :
    X.extEl hN₀ hN₁ h₀ (Sorted.inj N₀.M.U z) = Sorted.inj N₁.M.U (X.newFun hN₀ hN₁ h₀ m z) := by
  show (⟨nidx m, X.extFun hN₀ hN₁ h₀ (nidx m) z⟩ : Sorted.El N₁.M.U) = _
  rw [X.extFun_nidx hN₀ hN₁ h₀]

theorem extFun_bijective (k : ℕ) : Function.Bijective (X.extFun hN₀ hN₁ h₀ k) :=
  parityDep_bijective (fun k => k) (fun n => h₀.toFun n) (X.newFun hN₀ hN₁ h₀) h₀.bijective
    (X.newFun_bijective hN₀ hN₁ h₀) k

theorem extEl_injective : Function.Injective (X.extEl hN₀ hN₁ h₀) := by
  rintro ⟨k, x⟩ ⟨k', x'⟩ h
  have hk : k = k' := congrArg Sigma.fst h
  subst hk
  have hx : x = x' := (X.extFun_bijective hN₀ hN₁ h₀ k).1 (eq_of_heq (Sigma.mk.inj_iff.mp h).2)
  rw [hx]

theorem rel_base_iff (r : F.sig.Rel) (t : Fin (F.sig.arity r) → Sorted.El N₀.M.U) :
    t ∈ N₀.M.rel (.base r) ↔ (fun j => X.extEl hN₀ hN₁ h₀ (t j)) ∈ N₁.M.rel (.base r) := by
  by_cases hs : ∀ j, (t j).1 = bidx (F.sig.sortAt r j)
  · obtain ⟨u, hu⟩ : ∃ u : Fin (F.sig.arity r) → Sorted.El (X.baseU N₀.M),
        ∀ j, (X.dbl N₀.M).el (u j) = t j :=
      ⟨fun j => ⟨F.sig.sortAt r j, Sorted.toSort N₀.M.U (t j) (hs j)⟩,
        fun j => Sorted.inj_toSort N₀.M.U (t j) (hs j)⟩
    have e1 : t = fun j => (X.dbl N₀.M).el (u j) := funext fun j => (hu j).symm
    subst e1
    show u ∈ (X.baseStr N₀.M).rel r ↔
      (fun j => X.extEl hN₀ hN₁ h₀ ((X.dbl N₀.M).el (u j))) ∈ N₁.M.rel (.base r)
    refine (h₀.rel_iff r u).trans ?_
    show (fun j => (X.dbl N₁.M).el (h₀.mapEl (u j))) ∈ N₁.M.rel (.base r) ↔ _
    have e2 : (fun j => X.extEl hN₀ hN₁ h₀ ((X.dbl N₀.M).el (u j))) =
        fun j => (X.dbl N₁.M).el (h₀.mapEl (u j)) :=
      funext fun j => X.extEl_dbl hN₀ hN₁ h₀ (u j)
    rw [e2]
  · constructor
    · intro h; exact (hs fun j => N₀.M.rel_sorts (.base r) t h j).elim
    · intro h; exact (hs fun j => N₁.M.rel_sorts (.base r) _ h j).elim

theorem rel_enc_iff (m : ℕ) (t : Fin 2 → Sorted.El N₀.M.U) :
    t ∈ N₀.M.rel (.enc m) ↔ (fun j => X.extEl hN₀ hN₁ h₀ (t j)) ∈ N₁.M.rel (.enc m) := by
  by_cases hs : (t 0).1 = nidx m ∧ (t 1).1 = bidx (X.σ m)
  · obtain ⟨h0, h1⟩ := hs
    obtain ⟨z, w, e⟩ : ∃ (z : N₀.M.U (nidx m)) (w : N₀.M.U (bidx (X.σ m))),
        t = ![Sorted.inj N₀.M.U z, Sorted.inj N₀.M.U w] := by
      refine ⟨Sorted.toSort N₀.M.U (t 0) h0, Sorted.toSort N₀.M.U (t 1) h1, ?_⟩
      funext j
      match j with
      | 0 => exact (Sorted.inj_toSort N₀.M.U (t 0) h0).symm
      | 1 => exact (Sorted.inj_toSort N₀.M.U (t 1) h1).symm
    subst e
    have e2 : (fun j => X.extEl hN₀ hN₁ h₀ (![Sorted.inj N₀.M.U z, Sorted.inj N₀.M.U w] j)) =
        ![Sorted.inj N₁.M.U (X.newFun hN₀ hN₁ h₀ m z), Sorted.inj N₁.M.U (h₀.toFun (X.σ m) w)] := by
      funext j
      match j with
      | 0 => exact X.extEl_nidx hN₀ hN₁ h₀ m z
      | 1 => exact X.extEl_bidx hN₀ hN₁ h₀ (X.σ m) w
    rw [e2]
    refine (X.enc_iff hN₀ m z w).trans ?_
    refine Iff.trans ?_ (X.enc_iff hN₁ m (X.newFun hN₀ hN₁ h₀ m z) (h₀.toFun (X.σ m) w)).symm
    rw [X.encFun_newFun]
    exact ⟨fun h => by rw [h], fun h => (h₀.bijective _).1 h⟩
  · constructor
    · intro h; exact (hs ⟨N₀.M.rel_sorts (.enc m) t h 0, N₀.M.rel_sorts (.enc m) t h 1⟩).elim
    · intro h; exact (hs ⟨N₁.M.rel_sorts (.enc m) _ h 0, N₁.M.rel_sorts (.enc m) _ h 1⟩).elim

theorem code_extEl (z : Sorted.El N₀.M.U) (w : Sorted.El (X.baseU N₀.M)) :
    X.Code N₁.M (X.extEl hN₀ hN₁ h₀ z) (h₀.mapEl w) ↔ X.Code N₀.M z w := by
  unfold Code
  show (if z.1 % 2 = 0 then (X.dbl N₁.M).el (h₀.mapEl w) = X.extEl hN₀ hN₁ h₀ z
    else ![X.extEl hN₀ hN₁ h₀ z, (X.dbl N₁.M).el (h₀.mapEl w)] ∈ N₁.M.rel (.enc (z.1 / 2))) ↔ _
  rw [← X.extEl_dbl hN₀ hN₁ h₀]
  split_ifs with h
  · exact ⟨fun h' => X.extEl_injective hN₀ hN₁ h₀ h', fun h' => by rw [h']⟩
  · have e : ![X.extEl hN₀ hN₁ h₀ z, X.extEl hN₀ hN₁ h₀ ((X.dbl N₀.M).el w)] =
        fun j => X.extEl hN₀ hN₁ h₀ (![z, (X.dbl N₀.M).el w] j) := by
      funext j
      match j with
      | 0 => rfl
      | 1 => rfl
    rw [e]
    exact (X.rel_enc_iff hN₀ hN₁ h₀ (z.1 / 2) _).symm

theorem rel_new_iff (f : X.Sym) (t : Fin (X.arity f) → Sorted.El N₀.M.U) :
    t ∈ N₀.M.rel (.new f) ↔ (fun j => X.extEl hN₀ hN₁ h₀ (t j)) ∈ N₁.M.rel (.new f) := by
  rw [hN₀.sym f t, hN₁.sym f]
  constructor
  · rintro ⟨hs, c, hc, hsat⟩
    refine ⟨hs, fun j => h₀.mapEl (c j), fun j => (X.code_extEl hN₀ hN₁ h₀ _ _).2 (hc j), ?_⟩
    exact (X.sat_base hN₀ hN₁ h₀ _ c).1 hsat
  · rintro ⟨hs, c', hc', hsat⟩
    refine ⟨hs, fun j => h₀.symm.mapEl (c' j), fun j => ?_, ?_⟩
    · have := hc' j
      rw [← h₀.mapEl_symm_apply (c' j)] at this
      exact (X.code_extEl hN₀ hN₁ h₀ _ _).1 this
    · refine (X.sat_base hN₀ hN₁ h₀ (X.symF f) (fun j => h₀.symm.mapEl (c' j))).2 ?_
      have : (fun i => h₀.mapEl (h₀.symm.mapEl (c' i))) = c' :=
        funext fun i => h₀.mapEl_symm_apply (c' i)
      rw [this]; exact hsat

/-- The extension of an isomorphism of base reducts to the expanded models. -/
noncomputable def extend : GenIso N₀.M N₁.M where
  toFun := X.extFun hN₀ hN₁ h₀
  bijective := X.extFun_bijective hN₀ hN₁ h₀
  rel_iff r t := by
    cases r with
    | base r => exact X.rel_base_iff hN₀ hN₁ h₀ r t
    | enc m => exact X.rel_enc_iff hN₀ hN₁ h₀ m t
    | new f => exact X.rel_new_iff hN₀ hN₁ h₀ f t

theorem extend_mapEl (z : Sorted.El N₀.M.U) : (X.extend hN₀ hN₁ h₀).mapEl z = X.extEl hN₀ hN₁ h₀ z := rfl

theorem extend_mapEl_dbl (w : Sorted.El (X.baseU N₀.M)) :
    (X.extend hN₀ hN₁ h₀).mapEl ((X.dbl N₀.M).el w) = (X.dbl N₁.M).el (h₀.mapEl w) :=
  X.extEl_dbl hN₀ hN₁ h₀ w

end Extend

end SortExp

end SolidLean.Solid
