module

public import Solid.Calc.Theory
public import Solid.Calc.Soundness

/-!
# Adequacy: soundness read in the models of `T_L`

The graph symbol `R_{Γ,t}` of `T_L` is defined by the evaluator clause
`eval Γ t`, which is what the value relation `Val` reads.  So in the
canonical `T_L`-model of a model of `H`, the symbol `R_{Γ,t}` of a certified
term is the graph of a function of the valid environments (Theorem 4.1 read
in `T_L`), and for a closed certified term it is a singleton.
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid

/-- Membership in a graph symbol of the canonical expansion. -/
theorem mem_expand_rel_iff (T : TowerWithClasses.{u}) {m : ℕ} (Γ : Ctx m) (t : Term)
    (v : Fin (m + 1) → T.T.El) :
    v ∈ (LAnn.expand T).M.rel (.inr ⟨m, (Γ, t)⟩) ↔
      (∀ i : Fin m, (v (Fin.castSucc i)).1 = Γ.levels i) ∧
      Val T.T Γ t (Fin.init v) (v (Fin.last m)) := by
  show (eval Γ t).Sat T.T.toStr v ∧
    (∀ i, (v i).1 = Fin.snoc (α := fun _ => ℕ) Γ.levels (t.cls Γ) i) ↔ _
  unfold Val
  rw [Fin.snoc_init_self, Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h3, h1⟩
  · rintro ⟨h2, h3, h1⟩; exact ⟨h1, h2, h3⟩

/-- **Adequacy for closed terms**: in the canonical `T_L`-model of a model of
`H`, the graph symbol of a closed certified term `t : A @ r` is a singleton
`{⟦t⟧}` with `⟦t⟧` of sort `r`, and `⟦t⟧ ∈ ⟦A⟧ ∈ U_r`. -/
theorem adequacy_closed {M : TowerWithClasses.{u}} (hM : IsTowerModel M) {Γ : Ctx 0} {t A : Term}
    {r : ℕ} (ht : Typed Γ t A r) :
    ∃ (w : M.T.U r) (vA : M.T.U (r + 1)),
      (∀ v : Fin 1 → M.T.El, v ∈ (LAnn.expand M).M.rel (.inr ⟨0, (Γ, t)⟩) ↔ v = fun _ => M.T.inj w) ∧
      (∀ v : Fin 1 → M.T.El, v ∈ (LAnn.expand M).M.rel (.inr ⟨0, (Γ, A)⟩) ↔ v = fun _ => M.T.inj vA) ∧
      M.T.mem (M.T.j (r + 1) vA) (hM.univSet r) ∧ M.T.mem (M.T.j r w) vA := by
  obtain ⟨w, vA, hw, hvA, hAU, hmem⟩ := soundness_closed hM ht
  refine ⟨w, vA, fun v => ?_, fun v => ?_, hAU, hmem⟩
  · rw [mem_expand_rel_iff]
    have e : Fin.init v = fun i => i.elim0 := funext fun i => i.elim0
    rw [e, hw]
    constructor
    · rintro ⟨-, h⟩
      funext i
      rw [Subsingleton.elim i (Fin.last 0)]; exact h
    · rintro rfl
      exact ⟨fun i => i.elim0, rfl⟩
  · rw [mem_expand_rel_iff]
    have e : Fin.init v = fun i => i.elim0 := funext fun i => i.elim0
    rw [e, hvA]
    constructor
    · rintro ⟨-, h⟩
      funext i
      rw [Subsingleton.elim i (Fin.last 0)]; exact h
    · rintro rfl
      exact ⟨fun i => i.elim0, rfl⟩

end SolidLean.Calc
