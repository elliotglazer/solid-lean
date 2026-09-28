import Solid.FO.Axioms

/-!
# From the sentences to the semantic axioms

A structure for `F.sig` that satisfies the sentences `F.Hax` is a model of
`H` in the semantic sense, with its definable class system:
`ClauseFamily.isGenModel_of_models`.  With the defining axioms of a clause
family given by formulas, it is a model of `T(𝔉)`
(`ClauseFamily.isGenModel_of_models_TL`).
-/

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

end ClauseFamily

end SolidLean.Solid
