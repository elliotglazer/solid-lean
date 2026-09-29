module

public import Solid.FO.Axioms

/-!
# From the sentences to the semantic axioms

A structure for `F.sig` that satisfies the sentences `F.Hax` is a model of
`H` in the semantic sense, with its definable class system:
`ClauseFamily.isGenModel_of_models`.  With the defining axioms of a clause
family given by formulas, it is a model of `T(𝔉)`
(`ClauseFamily.isGenModel_of_models_TL`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

namespace ClauseFamily

variable {F : ClauseFamily.{u}} {M : Str.{u} F.sig}

/-! ### Reading atoms on the tower reduct -/

theorem Sat_liftZF_reduct {k : ℕ} {s : Fin k → ℕ} {n : ℕ} {i j : Fin k} {hi : s i = n}
    {hj : s j = n + 1} (t : Fin k → Sorted.El M.U) :
    (TF.liftZF n i j hi hj).Sat M.towerReduct t ↔ ![t i, t j] ∈ M.rel (.inl (.liftZ n)) := by
  show (fun l => t (![i, j] l)) ∈ M.rel (.inl (.liftZ n)) ↔ _
  rw [show (fun l => t (![i, j] l)) = ![t i, t j] from map_vec_two t i j]

theorem Sat_bndF_reduct {k : ℕ} {s : Fin k → ℕ} {n : ℕ} {i : Fin k} {hi : s i = n + 1}
    (t : Fin k → Sorted.El M.U) :
    (TF.bndF n i hi).Sat M.towerReduct t ↔ ![t i] ∈ M.rel (.inl (.bnd n)) := by
  show (fun l => t (![i] l)) ∈ M.rel (.inl (.bnd n)) ↔ _
  rw [show (fun l => t (![i] l)) = ![t i] from map_vec_one t i]

theorem Holds_inl (σ : Sentence TowerSig) :
    Sentence.Holds (σ.inl (F := F)) M ↔ Sentence.Holds σ M.towerReduct :=
  Formula.Sat_inl M σ _

/-! ### Well-formedness -/

theorem isWF_of_models (hM : M.Models F.Hax) : IsWF M where
  liftZ_total n x := by
    have h := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨n, rfl⟩)))))))))))
    rw [Holds_inl, TF.liftTotalAx, Formula.Sat_closeAll] at h
    have h1 := h ![Sorted.inj M.U x] (by simp)
    rw [Formula.Sat_ex] at h1
    obtain ⟨y, hy, h2⟩ := h1
    have h3 := (Sat_liftZF_reduct _).1 h2
    refine ⟨Sorted.toSort M.U y hy, ?_⟩
    rw [Sorted.inj_toSort]
    simpa using h3
  liftZ_unique n x y y' hy hy' := by
    have h := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨n, rfl⟩))))))))))))
    rw [Holds_inl, TF.liftUniqueAx, Formula.Sat_closeAll] at h
    have h1 := h ![Sorted.inj M.U x, Sorted.inj M.U y, Sorted.inj M.U y'] (by
      intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl)
    rw [Formula.Sat_imp, Formula.Sat_imp] at h1
    have e : Sorted.inj M.U y = Sorted.inj M.U y' :=
      h1 ((Sat_liftZF_reduct _).2 (by simpa using hy)) ((Sat_liftZF_reduct _).2 (by simpa using hy'))
    exact Sorted.inj_injective M.U e
  bnd_exists n := by
    have h := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))))))
    rw [Holds_inl, TF.bndExistsAx, Formula.Sat_closeAll] at h
    have h1 := h Fin.elim0 (fun i => i.elim0)
    rw [Formula.Sat_ex] at h1
    obtain ⟨y, hy, h2⟩ := h1
    have h3 := (Sat_bndF_reduct _).1 h2
    refine ⟨Sorted.toSort M.U y hy, ?_⟩
    rw [Sorted.inj_toSort]
    have e : (Fin.snoc (α := fun _ => Sorted.El M.U) Fin.elim0 y : Fin 1 → Sorted.El M.U) 0 = y := rfl
    rw [e] at h3
    exact h3
  bnd_unique n y y' hy hy' := by
    have h := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))))))))
    rw [Holds_inl, TF.bndUniqueAx, Formula.Sat_closeAll] at h
    have h1 := h ![Sorted.inj M.U y, Sorted.inj M.U y'] (by intro i; match i with | 0 => rfl | 1 => rfl)
    rw [Formula.Sat_imp, Formula.Sat_imp] at h1
    have e : Sorted.inj M.U y = Sorted.inj M.U y' :=
      h1 ((Sat_bndF_reduct _).2 (by simpa using hy)) ((Sat_bndF_reduct _).2 (by simpa using hy'))
    exact Sorted.inj_injective M.U e


/-! ### Reading the tower-signature axioms in the underlying tower -/

section Tower

variable (hM : M.Models F.Hax)

/-- A tower-signature sentence of `F.Hax` holds in the underlying tower. -/
theorem holds_tower {σ : Sentence TowerSig} (h : σ.inl ∈ F.Hax) :
    Sentence.Holds σ (Δ M (isWF_of_models hM)).toStr := by
  rw [Δ_toStr_eq]
  exact (Holds_inl σ).1 (hM _ h)

/-- A constant-sort sentence of `F.Hax` holds in the underlying tower. -/
theorem sat_tower {n : ℕ} {φ : TF 0 (fun _ => n)} (h : (TF.toSentence φ).inl ∈ F.Hax) :
    φ.Sat (Δ M (isWF_of_models hM)).toStr Fin.elim0 :=
  (TF.Holds_toSentence _ φ).1 (holds_tower hM h)

theorem ext_of_models (n : ℕ) (x y : (Δ M (isWF_of_models hM)).U n)
    (h : ∀ z, (Δ M (isWF_of_models hM)).mem z x ↔ (Δ M (isWF_of_models hM)).mem z y) : x = y := by
  have hσ := sat_tower hM (φ := TF.extAx n) (Or.inl ⟨n, rfl⟩)
  unfold TF.extAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![x, y]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this h

theorem empty_of_models (n : ℕ) :
    ∃ e, ((Δ M (isWF_of_models hM)).sortStr n).IsEmptySet e := by
  have hσ := sat_tower hM (φ := TF.emptyAx n) (Or.inr (Or.inl ⟨n, rfl⟩))
  unfold TF.emptyAx at hσ
  have e : (Fin.elim0 : Fin 0 → (Δ M (isWF_of_models hM)).El) =
      fun l => (Δ M (isWF_of_models hM)).inj ((fun i : Fin 0 => (i.elim0 : (Δ M (isWF_of_models hM)).U n)) l) :=
    funext fun i => i.elim0
  rw [e] at hσ
  have := (TF.Sat_exC _ _ _).1 hσ
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this

theorem pair_of_models (n : ℕ) (a b : (Δ M (isWF_of_models hM)).U n) :
    ∃ p, ((Δ M (isWF_of_models hM)).sortStr n).IsPairSet a b p := by
  have hσ := sat_tower hM (φ := TF.pairAx n) (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))
  unfold TF.pairAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![a, b]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this

theorem union_of_models (n : ℕ) (x : (Δ M (isWF_of_models hM)).U n) :
    ∃ u, ((Δ M (isWF_of_models hM)).sortStr n).IsUnionSet x u := by
  have hσ := sat_tower hM (φ := TF.unionAx n) (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))
  unfold TF.unionAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![x]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this

theorem power_of_models (n : ℕ) (x : (Δ M (isWF_of_models hM)).U n) :
    ∃ p, ((Δ M (isWF_of_models hM)).sortStr n).IsPowerSet x p := by
  have hσ := sat_tower hM (φ := TF.powerAx n) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))
  unfold TF.powerAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![x]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this

theorem infinity_of_models (n : ℕ) :
    ∃ I, (∃ e, ((Δ M (isWF_of_models hM)).sortStr n).IsEmptySet e ∧ (Δ M (isWF_of_models hM)).mem e I) ∧
      ∀ x, (Δ M (isWF_of_models hM)).mem x I →
        ∃ s, ((Δ M (isWF_of_models hM)).sortStr n).IsSucc x s ∧ (Δ M (isWF_of_models hM)).mem s I := by
  have hσ := sat_tower hM (φ := TF.infAx n)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  unfold TF.infAx at hσ
  have e : (Fin.elim0 : Fin 0 → (Δ M (isWF_of_models hM)).El) =
      fun l => (Δ M (isWF_of_models hM)).inj ((fun i : Fin 0 => (i.elim0 : (Δ M (isWF_of_models hM)).U n)) l) :=
    funext fun i => i.elim0
  rw [e] at hσ
  have := (TF.Sat_exC _ _ _).1 hσ
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this

theorem foundation_of_models (n : ℕ) (x : (Δ M (isWF_of_models hM)).U n)
    (hx : ((Δ M (isWF_of_models hM)).sortStr n).Nonempty x) :
    ∃ y, (Δ M (isWF_of_models hM)).mem y x ∧
      ∀ z, (Δ M (isWF_of_models hM)).mem z y → ¬ (Δ M (isWF_of_models hM)).mem z x := by
  have hσ := sat_tower hM (φ := TF.foundAx n)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))
  unfold TF.foundAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![x]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this hx

theorem choice_of_models (n : ℕ) (x : (Δ M (isWF_of_models hM)).U n)
    (hx : ∀ y, (Δ M (isWF_of_models hM)).mem y x → ((Δ M (isWF_of_models hM)).sortStr n).Nonempty y) :
    ∃ f, ((Δ M (isWF_of_models hM)).sortStr n).IsFunctionOn f x ∧
      ∀ y v, ((Δ M (isWF_of_models hM)).sortStr n).FunApp f y v → (Δ M (isWF_of_models hM)).mem v y := by
  have hσ := sat_tower hM (φ := TF.choiceAx n)
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))
  unfold TF.choiceAx at hσ
  have := (TF.Sat_closeC _ n _ _).1 hσ ![x]
  simp only [TF.Sat_exC, TF.Sat_allC, Formula.Sat_imp, Formula.Sat_and, Formula.Sat_iff, Formula.Sat_not, TF.Sat_memC, TF.Sat_eqC, TF.Sat_isEmptyC, TF.Sat_pairC, TF.Sat_unionSetC, TF.Sat_powerSetC, TF.Sat_succC, TF.Sat_nonemptyC, TF.Sat_funOnC, TF.Sat_funAppC, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_one_zero, Fin.snoc_one_one, Fin.snoc_two_zero, Fin.snoc_two_one, Fin.snoc_two_two, Fin.snoc_three_zero, Fin.snoc_three_one, Fin.snoc_three_two, Fin.snoc_three_three, Fin.snoc_four_zero, Fin.snoc_four_one, Fin.snoc_four_two, Fin.snoc_four_three, Fin.snoc_four_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two] at this
  exact this hx

end Tower


/-! ### The schemes -/

theorem Sat_memS {n : ℕ} {k : ℕ} {s : Fin k → ℕ} {i j : Fin k} {hi : s i = n} {hj : s j = n}
    (t : Fin k → Sorted.El M.U) :
    (F.memS n i j hi hj).Sat M t ↔ ![t i, t j] ∈ M.rel (.inl (.memZ n)) := by
  unfold memS
  rw [Formula.Sat_inl]
  show (fun l => t (![i, j] l)) ∈ M.rel (.inl (.memZ n)) ↔ _
  rw [show (fun l => t (![i, j] l)) = ![t i, t j] from map_vec_two t i j]

theorem liftRel_inj_iff {n k : ℕ} (C : Set (Fin k → M.U n)) (q : Fin k → M.U n) :
    (fun i => Sorted.inj M.U (q i)) ∈ Sorted.liftRel M.U C ↔ q ∈ C := by
  constructor
  · rintro ⟨s, hs, hC⟩
    have : q = s := funext fun i => Sorted.inj_injective M.U (hs i)
    rw [this]; exact hC
  · intro h
    exact ⟨q, fun _ => rfl, h⟩

theorem sepBody_env (n : ℕ) {m : ℕ} {base : Fin m → ℕ} (ψ : Formula F.sig (m + 1) (Fin.snoc base n))
    (t : Fin m → Sorted.El M.U) (x s y : Sorted.El M.U) :
    (F.sepBody n ψ).Sat M (Fin.snoc (Fin.snoc (Fin.snoc t x) s) y) ↔ ψ.Sat M (Fin.snoc t y) := by
  unfold sepBody
  refine (Formula.sat_rename _ _ ψ _).trans ?_
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U) (Fin.snoc (Fin.snoc t x) s) y
      (Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 2))
        (fun j => j.castSucc.castSucc.castSucc) i)) = Fin.snoc t y := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simp
  rw [e]

theorem const_snoc (k n : ℕ) :
    Fin.snoc (α := fun _ => ℕ) (fun _ : Fin k => n) n = fun _ : Fin (k + 1) => n := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

theorem append_const_sorts {a : ℕ} (ps : Fin a → ℕ) (k n : ℕ) :
    ∀ i, Fin.snoc (α := fun _ => ℕ) (Fin.append ps (fun _ : Fin k => n)) n i =
      Fin.append ps (fun _ : Fin (k + 1) => n) i := by
  intro i
  rw [← const_snoc k n, Fin.append_snoc]

theorem separation_of_models (hM : M.Models F.Hax) (n : ℕ) {k : ℕ}
    (C : ((Δ M (isWF_of_models hM)).sortStr n).Rel (k + 1))
    (hC : (ΔSys ⟨M, M.defSys⟩ (isWF_of_models hM)).DefOn n (k + 1) C)
    (p : Fin k → (Δ M (isWF_of_models hM)).U n) (x : (Δ M (isWF_of_models hM)).U n) :
    ∃ s, ∀ y, (Δ M (isWF_of_models hM)).mem y s ↔
      (Δ M (isWF_of_models hM)).mem y x ∧ Fin.snoc p y ∈ C := by
  -- the class is definable with parameters
  have hdef : Formula.SortedDef M (fun _ : Fin (k + 1) => n) (Sorted.liftRel M.U C) := hC _
  obtain ⟨a, ps, φ, params, hps, hφ⟩ := hdef
  -- the instance of Separation
  let ψ : Formula F.sig (a + k + 1) (Fin.snoc (Fin.append ps (fun _ : Fin k => n)) n) :=
    Formula.recast (append_const_sorts ps k n) φ
  have hσ := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨n, a + k, Fin.append ps (fun _ : Fin k => n), ψ, rfl⟩)))))))))
  unfold sepAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  -- the parameters
  let t : Fin (a + k) → Sorted.El M.U := Fin.append params (fun i => Sorted.inj M.U (p i))
  have ht : ∀ i, (t i).1 = Fin.append ps (fun _ : Fin k => n) i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [t, Fin.append_left]; exact hps i
    · simp only [t, Fin.append_right]
  have h1 := hσ t ht
  rw [Formula.Sat_all] at h1
  have h2 := h1 (Sorted.inj M.U x) rfl
  rw [Formula.Sat_ex] at h2
  obtain ⟨s', hs', h3⟩ := h2
  refine ⟨Sorted.toSort M.U s' hs', fun y => ?_⟩
  rw [Formula.Sat_all] at h3
  have h4 := h3 (Sorted.inj M.U y) rfl
  rw [Formula.Sat_iff, Formula.Sat_and, Sat_memS, Sat_memS, sepBody_env] at h4
  simp only [Fin.snoc_last, Fin.snoc_castSucc] at h4
  -- read the three parts
  have hmem : (Δ M (isWF_of_models hM)).mem y (Sorted.toSort M.U s' hs') ↔
      ![Sorted.inj M.U y, s'] ∈ M.rel (.inl (.memZ n)) := by
    show ![Sorted.inj M.U y, Sorted.inj M.U (Sorted.toSort M.U s' hs')] ∈ M.rel (.inl (.memZ n)) ↔ _
    rw [Sorted.inj_toSort]
  have hmemx : (Δ M (isWF_of_models hM)).mem y x ↔
      ![Sorted.inj M.U y, Sorted.inj M.U x] ∈ M.rel (.inl (.memZ n)) := Iff.rfl
  have hprof : (fun i => Sorted.inj M.U (Fin.snoc (α := fun _ => (Δ M (isWF_of_models hM)).U n) p y i)) ∈
      Sorted.profileRel M.U (fun _ : Fin (k + 1) => n) := fun _ => rfl
  have e2 : (fun i => Sorted.inj M.U (Fin.snoc (α := fun _ => (Δ M (isWF_of_models hM)).U n) p y i)) =
      Fin.snoc (α := fun _ => Sorted.El M.U) (fun i => Sorted.inj M.U (p i)) (Sorted.inj M.U y) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last, Fin.snoc_last]
    · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  have e : Fin.append params (fun i => Sorted.inj M.U (Fin.snoc (α := fun _ => (Δ M (isWF_of_models hM)).U n) p y i)) =
      Fin.snoc t (Sorted.inj M.U y) := by
    rw [e2, Fin.append_snoc]
  have hC' : Fin.snoc p y ∈ C ↔ ψ.Sat M (Fin.snoc t (Sorted.inj M.U y)) := by
    refine (liftRel_inj_iff (n := n) C (Fin.snoc p y)).symm.trans ?_
    refine (hφ _ hprof).trans ?_
    refine Iff.trans ?_ (Formula.Sat_recast (append_const_sorts ps k n) φ _).symm
    rw [e]
  rw [hmem, hmemx, hC']
  exact h4


theorem repBody1_env (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) (t : Fin m → Sorted.El M.U)
    (x y z : Sorted.El M.U) :
    (F.repBody1 n ψ).Sat M (Fin.snoc (Fin.snoc (Fin.snoc t x) y) z) ↔ ψ.Sat M (Fin.snoc (Fin.snoc t y) z) := by
  unfold repBody1
  refine (Formula.sat_rename _ _ ψ _).trans ?_
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U) (Fin.snoc (Fin.snoc t x) y) z
      (Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 2))
        (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 3)) (Fin.last (m + 1)).castSucc
          (fun j => j.castSucc.castSucc.castSucc) i') i)) = Fin.snoc (Fin.snoc t y) z := by
    funext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp
  rw [e]

theorem repBody2_env (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) (t : Fin m → Sorted.El M.U)
    (x y z z' : Sorted.El M.U) :
    (F.repBody2 n ψ).Sat M (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc t x) y) z) z') ↔
      ψ.Sat M (Fin.snoc (Fin.snoc t y) z') := by
  unfold repBody2
  refine (Formula.sat_rename _ _ ψ _).trans ?_
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U) (Fin.snoc (Fin.snoc (Fin.snoc t x) y) z) z'
      (Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 3))
        (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 1)).castSucc.castSucc
          (fun j => j.castSucc.castSucc.castSucc.castSucc) i') i)) = Fin.snoc (Fin.snoc t y) z' := by
    funext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp
  rw [e]

theorem repBody3_env (n : ℕ) {m : ℕ} {base : Fin m → ℕ}
    (ψ : Formula F.sig (m + 2) (Fin.snoc (Fin.snoc base n) n)) (t : Fin m → Sorted.El M.U)
    (x s z y : Sorted.El M.U) :
    (F.repBody3 n ψ).Sat M (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc t x) s) z) y) ↔
      ψ.Sat M (Fin.snoc (Fin.snoc t y) z) := by
  unfold repBody3
  refine (Formula.sat_rename _ _ ψ _).trans ?_
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U) (Fin.snoc (Fin.snoc (Fin.snoc t x) s) z) y
      (Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 2)).castSucc
        (fun i' => Fin.lastCases (motive := fun _ => Fin (m + 4)) (Fin.last (m + 3))
          (fun j => j.castSucc.castSucc.castSucc.castSucc) i') i)) = Fin.snoc (Fin.snoc t y) z := by
    funext i
    refine Fin.lastCases ?_ (fun i' => ?_) i
    · simp
    · refine Fin.lastCases ?_ (fun j => ?_) i' <;> simp
  rw [e]

theorem append_const_sorts2 {a : ℕ} (ps : Fin a → ℕ) (k n : ℕ) :
    ∀ i, Fin.snoc (α := fun _ => ℕ) (Fin.snoc (Fin.append ps (fun _ : Fin k => n)) n) n i =
      Fin.append ps (fun _ : Fin (k + 2) => n) i := by
  intro i
  rw [← const_snoc (k + 1) n, ← const_snoc k n, Fin.append_snoc, Fin.append_snoc]

theorem snoc_inj_eq {n k : ℕ} (p : Fin k → M.U n) (y : M.U n) :
    (fun i => Sorted.inj M.U (Fin.snoc (α := fun _ => M.U n) p y i)) =
      Fin.snoc (α := fun _ => Sorted.El M.U) (fun i => Sorted.inj M.U (p i)) (Sorted.inj M.U y) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [Fin.snoc_last, Fin.snoc_last]
  · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]

theorem replacement_of_models (hM : M.Models F.Hax) (n : ℕ) {k : ℕ}
    (C : Set (Fin (k + 2) → M.U n))
    (hC : (ΔSys ⟨M, M.defSys⟩ (isWF_of_models hM)).DefOn n (k + 2) C)
    (p : Fin k → M.U n) (x : M.U n)
    (hfun : ∀ y, (Δ M (isWF_of_models hM)).mem y x →
      ∃! z, Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) p y) z ∈ C) :
    ∃ s, ∀ z, (Δ M (isWF_of_models hM)).mem z s ↔
      ∃ y, (Δ M (isWF_of_models hM)).mem y x ∧
        Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) p y) z ∈ C := by
  have hdef : Formula.SortedDef M (fun _ : Fin (k + 2) => n) (Sorted.liftRel M.U C) := hC _
  obtain ⟨a, ps, φ, params, hps, hφ⟩ := hdef
  let ψ : Formula F.sig (a + k + 2) (Fin.snoc (Fin.snoc (Fin.append ps (fun _ : Fin k => n)) n) n) :=
    Formula.recast (append_const_sorts2 ps k n) φ
  have hσ := hM _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl ⟨n, a + k, Fin.append ps (fun _ : Fin k => n), ψ, rfl⟩))))))))))
  unfold repAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  let t : Fin (a + k) → Sorted.El M.U := Fin.append params (fun i => Sorted.inj M.U (p i))
  have ht : ∀ i, (t i).1 = Fin.append ps (fun _ : Fin k => n) i := by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [t, Fin.append_left]; exact hps i
    · simp only [t, Fin.append_right]
  -- reading `ψ` on `C`
  have hread : ∀ (y z : M.U n),
      ψ.Sat M (Fin.snoc (Fin.snoc t (Sorted.inj M.U y)) (Sorted.inj M.U z)) ↔
        Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) p y) z ∈ C := by
    intro y z
    have hprof : (fun i => Sorted.inj M.U
        (Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) p y) z i)) ∈
        Sorted.profileRel M.U (fun _ : Fin (k + 2) => n) := fun _ => rfl
    have e : Fin.append params (fun i => Sorted.inj M.U
        (Fin.snoc (α := fun _ => M.U n) (Fin.snoc (α := fun _ => M.U n) p y) z i)) =
        Fin.snoc (Fin.snoc t (Sorted.inj M.U y)) (Sorted.inj M.U z) := by
      rw [snoc_inj_eq, snoc_inj_eq, Fin.append_snoc, Fin.append_snoc]
    refine Iff.symm ?_
    refine (liftRel_inj_iff (n := n) C _).symm.trans ?_
    refine (hφ _ hprof).trans ?_
    refine Iff.trans ?_ (Formula.Sat_recast (append_const_sorts2 ps k n) φ _).symm
    rw [e]
  have h1 := hσ (Fin.snoc t (Sorted.inj M.U x)) (by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp
    · simpa using ht j)
  rw [Formula.Sat_imp] at h1
  -- the functionality hypothesis, read in the formula
  have hA : (Formula.all n (Formula.imp
      (F.memS n (Fin.last (a + k + 1)) (Fin.last (a + k)).castSucc (by simp) (by simp))
      (Formula.ex n (Formula.and (F.repBody1 n ψ)
        (Formula.all n (Formula.imp (F.repBody2 n ψ)
          (Formula.eq (Fin.last (a + k + 3)) (Fin.last (a + k + 2)).castSucc (by simp)))))))).Sat M
      (Fin.snoc t (Sorted.inj M.U x)) := by
    rw [Formula.Sat_all]
    intro y hy
    rw [Formula.Sat_imp, Sat_memS]
    intro hyx
    simp only [Fin.snoc_last, Fin.snoc_castSucc] at hyx
    have hyx' : (Δ M (isWF_of_models hM)).mem (Sorted.toSort M.U y hy) x := by
      show ![Sorted.inj M.U (Sorted.toSort M.U y hy), Sorted.inj M.U x] ∈ M.rel (.inl (.memZ n))
      rw [Sorted.inj_toSort]; exact hyx
    obtain ⟨z, hz, huniq⟩ := hfun _ hyx'
    rw [Formula.Sat_ex]
    refine ⟨Sorted.inj M.U z, rfl, ?_⟩
    rw [Formula.Sat_and, repBody1_env]
    refine ⟨?_, ?_⟩
    · have := (hread (Sorted.toSort M.U y hy) z).2 hz
      rw [Sorted.inj_toSort] at this
      exact this
    · rw [Formula.Sat_all]
      intro z' hz'
      rw [Formula.Sat_imp, repBody2_env]
      intro hψ
      have hψ' := hψ
      rw [← Sorted.inj_toSort M.U y hy, ← Sorted.inj_toSort M.U z' hz'] at hψ'
      have := huniq _ ((hread _ _).1 hψ')
      refine (Formula.Sat_eq _ _ _ _).2 ?_
      simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [← this, Sorted.inj_toSort]
  have h2 := h1 hA
  rw [Formula.Sat_ex] at h2
  obtain ⟨s', hs', h3⟩ := h2
  refine ⟨Sorted.toSort M.U s' hs', fun z => ?_⟩
  rw [Formula.Sat_all] at h3
  have h4 := h3 (Sorted.inj M.U z) rfl
  rw [Formula.Sat_iff, Sat_memS, Formula.Sat_ex] at h4
  simp only [Formula.Sat_and, Sat_memS, repBody3_env, Fin.snoc_last, Fin.snoc_castSucc] at h4
  have hmem : (Δ M (isWF_of_models hM)).mem z (Sorted.toSort M.U s' hs') ↔
      ![Sorted.inj M.U z, s'] ∈ M.rel (.inl (.memZ n)) := by
    show ![Sorted.inj M.U z, Sorted.inj M.U (Sorted.toSort M.U s' hs')] ∈ M.rel (.inl (.memZ n)) ↔ _
    rw [Sorted.inj_toSort]
  rw [hmem, h4]
  constructor
  · rintro ⟨y, hy, hyx, hψ⟩
    refine ⟨Sorted.toSort M.U y hy, ?_, ?_⟩
    · show ![Sorted.inj M.U (Sorted.toSort M.U y hy), Sorted.inj M.U x] ∈ M.rel (.inl (.memZ n))
      rw [Sorted.inj_toSort]; exact hyx
    · rw [← Sorted.inj_toSort M.U y hy] at hψ
      exact (hread _ _).1 hψ
  · rintro ⟨y, hyx, hC'⟩
    exact ⟨Sorted.inj M.U y, rfl, hyx, (hread _ _).2 hC'⟩


/-! ### The tower axioms -/

theorem snoc_zero_zero {α : Type*} (t : Fin 0 → α) (z : α) : (Fin.snoc t z : Fin 1 → α) 0 = z := rfl

section TowerAxioms

variable (hM : M.Models F.Hax)

/-- The underlying tower of a model of the axioms. -/
noncomputable abbrev Tw : MemTower.{u} := Δ M (isWF_of_models hM)

/-- A constant-sort sentence read as a statement about the tower, for the
`allC`/`exC` combinators at an empty context. -/
theorem sat_tower' {n : ℕ} {φ : TF 0 (fun _ => n)} (h : (TF.toSentence φ).inl ∈ F.Hax) :
    φ.Sat (Tw hM).toStr (fun l => (Tw hM).inj ((fun i : Fin 0 => (i.elim0 : (Tw hM).U n)) l)) := by
  have e : (Fin.elim0 : Fin 0 → (Tw hM).El) = fun l => (Tw hM).inj ((fun i : Fin 0 => (i.elim0 : (Tw hM).U n)) l) :=
    funext fun i => i.elim0
  rw [← e]
  exact sat_tower hM h

theorem j_injective_of_models (n : ℕ) (x y : (Tw hM).U n) (h : (Tw hM).j n x = (Tw hM).j n y) : x = y := by
  have hσ := holds_tower hM (σ := TF.jInjAx n) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))))))))
  unfold TF.jInjAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  have h1 := hσ ![(Tw hM).inj x, (Tw hM).inj y, (Tw hM).inj ((Tw hM).j n x), (Tw hM).inj ((Tw hM).j n y)]
    (by intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl)
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_imp] at h1
  have h2 := h1 ((TF.Sat_liftZF (Tw hM) x rfl).2 rfl) ((TF.Sat_liftZF (Tw hM) y rfl).2 rfl)
    (show (Tw hM).inj ((Tw hM).j n x) = (Tw hM).inj ((Tw hM).j n y) by rw [h])
  exact Sorted.inj_injective (Tw hM).U h2

theorem j_mem_iff_of_models (n : ℕ) (x y : (Tw hM).U n) :
    (Tw hM).mem ((Tw hM).j n x) ((Tw hM).j n y) ↔ (Tw hM).mem x y := by
  have hσ := holds_tower hM (σ := TF.jMemAx n) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))))))))))
  unfold TF.jMemAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  have h1 := hσ ![(Tw hM).inj x, (Tw hM).inj y, (Tw hM).inj ((Tw hM).j n x), (Tw hM).inj ((Tw hM).j n y)]
    (by intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl | 3 => rfl)
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_iff] at h1
  have h2 := h1 ((TF.Sat_liftZF (Tw hM) x rfl).2 rfl) ((TF.Sat_liftZF (Tw hM) y rfl).2 rfl)
  exact (TF.Sat_memF (Tw hM) ((Tw hM).j n x) ((Tw hM).j n y) rfl rfl).symm.trans (h2.trans (TF.Sat_memF (Tw hM) x y rfl rfl))

theorem kappa_inaccessible_of_models (n : ℕ) : ((Tw hM).sortStr (n + 1)).Inaccessible ((Tw hM).κ n) := by
  have hσ := sat_tower' hM (φ := TF.allC (n + 1) (Formula.imp (TF.bndF n 0 ((TF.IsConst.const 0 (n + 1)).snoc 0))
    (TF.inaccC (TF.IsConst.const 0 (n + 1)).snoc 0))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))))))))))
  have h1 := (TF.Sat_allC (Tw hM) _ _).1 hσ ((Tw hM).κ n)
  rw [Formula.Sat_imp] at h1
  exact (TF.Sat_inaccC (Tw hM) _ 0 _).1 (h1 rfl)

theorem j_image_of_models (n : ℕ) :
    ∃ v : (Tw hM).U (n + 1), ((Tw hM).sortStr (n + 1)).IsV ((Tw hM).κ n) v ∧ ∀ y, (Tw hM).mem y v ↔ ∃ x, (Tw hM).j n x = y := by
  have hσ := sat_tower' hM (φ := TF.exC (n + 1) (TF.exC (n + 1) (Formula.and
    (TF.bndF n 1 ((TF.IsConst.const 0 (n + 1)).snoc.snoc 1))
    (Formula.and (TF.isVC (TF.IsConst.const 0 (n + 1)).snoc.snoc 1 0)
      (TF.allC (n + 1) (Formula.iff (TF.memC (TF.IsConst.const 0 (n + 1)).snoc.snoc.snoc 2 0)
        (Formula.ex n (TF.liftZF n 3 2 (by simp) (by simp))))))))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))))))))))))))
  obtain ⟨v, h1⟩ := (TF.Sat_exC (Tw hM) _ _).1 hσ
  obtain ⟨k, h2⟩ := (TF.Sat_exC (Tw hM) _ _).1 h1
  rw [Formula.Sat_and, Formula.Sat_and] at h2
  obtain ⟨hk, hV, hall⟩ := h2
  have hk' : k = (Tw hM).κ n := Sorted.inj_injective (Tw hM).U hk
  have hV' : ((Tw hM).sortStr (n + 1)).IsV k v := (TF.Sat_isVC (Tw hM) _ 1 0 _).1 hV
  rw [hk'] at hV'
  refine ⟨v, hV', fun y => ?_⟩
  have h3 := (TF.Sat_allC (Tw hM) _ _).1 hall y
  rw [Formula.Sat_iff, Formula.Sat_ex] at h3
  have hmem : (Tw hM).mem y v ↔ _ := (TF.Sat_memC (Tw hM) _ 2 0 _).symm.trans h3
  rw [hmem]
  constructor
  · rintro ⟨x', hx', h4⟩
    refine ⟨Sorted.toSort (Tw hM).U x' hx', ?_⟩
    have h5 := (TF.Sat_liftZF (Tw hM) (Sorted.toSort (Tw hM).U x' hx')
      (show x' = (Tw hM).inj (Sorted.toSort (Tw hM).U x' hx') from (Sorted.inj_toSort (Tw hM).U x' hx').symm)).1 h4
    exact Sorted.inj_injective (Tw hM).U h5.symm
  · rintro ⟨x, rfl⟩
    exact ⟨(Tw hM).inj x, rfl, (TF.Sat_liftZF (Tw hM) x rfl).2 rfl⟩

theorem next_inaccessible_of_models (n : ℕ) :
    ((Tw hM).sortStr (n + 2)).NextInaccessible ((Tw hM).j (n + 1) ((Tw hM).κ n)) ((Tw hM).κ (n + 1)) := by
  have hσ := holds_tower hM (σ := TF.nextInaccAx n) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩)))))))))))))))))))
  unfold TF.nextInaccAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  have h1 := hσ ![(Tw hM).inj ((Tw hM).κ n), (Tw hM).inj ((Tw hM).j (n + 1) ((Tw hM).κ n)), (Tw hM).inj ((Tw hM).κ (n + 1))]
    (by intro i; match i with | 0 => rfl | 1 => rfl | 2 => rfl)
  rw [Formula.Sat_imp, Formula.Sat_imp, Formula.Sat_imp] at h1
  have h2 := (TF.Sat_at _ _ _ _).1 (h1 rfl ((TF.Sat_liftZF (Tw hM) ((Tw hM).κ n) rfl).2 rfl) rfl)
  have e : (fun i => (![(Tw hM).inj ((Tw hM).κ n), (Tw hM).inj ((Tw hM).j (n + 1) ((Tw hM).κ n)), (Tw hM).inj ((Tw hM).κ (n + 1))] : Fin 3 → (Tw hM).El)
      (![1, 2] i)) = fun l => (Tw hM).inj ((![(Tw hM).j (n + 1) ((Tw hM).κ n), (Tw hM).κ (n + 1)] : Fin 2 → (Tw hM).U (n + 2)) l) := by
    funext i; match i with | 0 => rfl | 1 => rfl
  rw [e] at h2
  exact (TF.Sat_nextInaccC (Tw hM) _ 0 1 _).1 h2

theorem bottom_of_models : ((Tw hM).sortStr 1).NoGreatestInaccessibleBelow ((Tw hM).κ 0) := by
  have hσ := sat_tower' hM (φ := TF.allC 1 (Formula.imp (TF.bndF 0 0 ((TF.IsConst.const 0 1).snoc 0))
    (TF.noGreatestInaccC (TF.IsConst.const 0 1).snoc 0))) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))))))))))))))
  have h1 := (TF.Sat_allC (Tw hM) _ _).1 hσ ((Tw hM).κ 0)
  rw [Formula.Sat_imp] at h1
  exact (TF.Sat_noGreatestInaccC (Tw hM) _ 0 _).1 (h1 rfl)

end TowerAxioms


theorem Δ_toStr_rel (h : IsWF M) (r : TowerSym) : (Δ M h).toStr.rel r = M.rel (.inl r) := by
  cases r with
  | memZ n => exact Δ.memRel_eq h n
  | liftZ n => exact Δ.jRel_eq h n
  | bnd n => exact Δ.kappaRel_eq h n

/-- Satisfaction in the tower reduct and in the underlying tower agree. -/
theorem Sat_Δ_toStr (h : IsWF M) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula TowerSig k s) (t : Fin k → Sorted.El M.U),
      φ.Sat (Δ M h).toStr t ↔ φ.Sat M.towerReduct t
  | _, _, .rel r v _, t => by
    show (fun i => t (v i)) ∈ (Δ M h).toStr.rel r ↔ (fun i => t (v i)) ∈ M.rel (.inl r)
    rw [Δ_toStr_rel h r]
    exact Iff.rfl
  | _, _, .eq _ _ _, _ => Iff.rfl
  | _, _, .false_, _ => Iff.rfl
  | _, _, .imp φ ψ, t => by
    show (_ → _) ↔ (_ → _)
    rw [Sat_Δ_toStr h φ t, Sat_Δ_toStr h ψ t]
  | _, _, .ex n φ, t => by
    show (∃ x : Sorted.El M.U, x.1 = n ∧ _) ↔ ∃ x : Sorted.El M.U, x.1 = n ∧ _
    constructor
    · rintro ⟨x, hx, hφ⟩; exact ⟨x, hx, (Sat_Δ_toStr h φ _).1 hφ⟩
    · rintro ⟨x, hx, hφ⟩; exact ⟨x, hx, (Sat_Δ_toStr h φ _).2 hφ⟩

/-! ### Assembly -/

/-- A structure satisfying the sentences `F.Hax` is a model of the tower
axioms in the semantic sense, with its definable class system. -/
theorem isTowerModel_of_models (hM : M.Models F.Hax) :
    IsTowerModel ⟨Δ M (isWF_of_models hM), ΔSys ⟨M, M.defSys⟩ (isWF_of_models hM)⟩ where
  zfc n := by
    show SetAxioms _ _
    exact {
      ext := ext_of_models hM n
      empty := empty_of_models hM n
      pair := pair_of_models hM n
      union := union_of_models hM n
      power := power_of_models hM n
      infinity := infinity_of_models hM n
      separation := fun C hC p x => separation_of_models hM n C hC p x
      replacement := fun C hC p x hfun => replacement_of_models hM n C hC p x hfun
      foundation := foundation_of_models hM n
      choice := choice_of_models hM n }
  j_injective := j_injective_of_models hM
  j_mem_iff := j_mem_iff_of_models hM
  kappa_inaccessible := kappa_inaccessible_of_models hM
  j_image := j_image_of_models hM
  next_inaccessible := next_inaccessible_of_models hM
  bottom := bottom_of_models hM

/-- The defining axioms give the clauses. -/
theorem clause_of_models {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig}
    (hM : M.Models (TLax Sym arity sortAt φ)) (f : Sym) :
    M.rel (.inr f) = (ofFormulas Sym arity sortAt φ).G f (Δ M (isWF_of_models fun σ h => hM σ (Or.inl h))) := by
  have hwf : IsWF M := isWF_of_models fun σ h => hM σ (Or.inl h)
  have hσ := hM _ (Or.inr ⟨f, rfl⟩)
  unfold defAx at hσ
  rw [Formula.Sat_closeAll] at hσ
  ext t
  constructor
  · intro ht
    have hs : ∀ i, (t i).1 = sortAt f i := M.rel_sorts (.inr f) t ht
    refine ⟨?_, hs⟩
    have h1 := (Formula.Sat_iff _ _ _).1 (hσ t hs)
    exact (Sat_Δ_toStr hwf _ _).2 ((Formula.Sat_inl M _ _).1 (h1.1 ht))
  · rintro ⟨hφ, hs⟩
    have h1 := (Formula.Sat_iff _ _ _).1 (hσ t hs)
    exact h1.2 ((Formula.Sat_inl M _ _).2 ((Sat_Δ_toStr hwf _ _).1 hφ))

/-- **A model of the sentences of `T(𝔉)` is a model of `T(𝔉)`** in the semantic
sense, with its definable class system. -/
theorem isGenModel_of_models {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
    {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
    {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig}
    (hM : M.Models (TLax Sym arity sortAt φ)) :
    (ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩ where
  wf := isWF_of_models fun σ h => hM σ (Or.inl h)
  tower := isTowerModel_of_models fun σ h => hM σ (Or.inl h)
  clause := clause_of_models hM

end ClauseFamily

end SolidLean.Solid
