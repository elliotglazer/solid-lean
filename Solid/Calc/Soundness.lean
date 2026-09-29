module

public import Solid.Calc.SoundBase
public import Solid.Calc.PrimSound
public import Solid.Calc.PrimEq

/-!
# Soundness of the annotated calculus (draft 2, Theorem 4.1)

The induction on derivations, assembling the cases of `SoundBase.lean`
(core constructors) and `PrimSound.lean` (primitives).
-/

@[expose] public section

universe u

open Classical

namespace SolidLean.Calc

open SolidLean.Solid Term

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### The theorem -/

mutual

theorem sound_typed {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} :
    Typed Γ t A r → PTy hM Γ t A r
  | .var x _ => case_var hM x
  | .univ n _ => case_univ hM Γ n
  | .piData hj hA hB =>
    case_piData hM hj (sound_typed hA) (sound_typed hB) (cls_of_typed hA) (cls_of_typed hB)
  | .piProp hA hB =>
    case_piProp hM (sound_typed hA) (sound_typed hB) (cls_of_typed hA) (cls_of_typed hB)
  | .lamData hj hA hb =>
    case_lamData hM hj (sound_typed hA) (sound_typed hb) (cls_of_typed hA) (cls_of_typed hb)
      (tyOk_of_typed hb).1.cls
  | .lamProp hA hb =>
    case_lamProp hM (sound_typed hA) (sound_typed hb) (cls_of_typed hA) (tyOk_of_typed hb).1.cls
  | .appData hj hf ha =>
    case_appData hM hj (sound_typed hf) (sound_typed ha) (cls_of_typed hf) (cls_of_typed ha)
      (tyOk_of_typed hf).1.2.1.cls (tyOk_of_typed hf).1.2.2.cls
  | .appProp hf ha =>
    case_appProp hM (sound_typed hf) (sound_typed ha) (cls_of_typed ha)
      (tyOk_of_typed hf).1.2.1.cls (tyOk_of_typed hf).1.2.2.cls
  | .letE hv hb => case_letE hM (sound_typed hv) (sound_typed hb) (cls_of_typed hv) (cls_of_typed hb)
  | .weak ht _ => case_weak hM (sound_typed ht) _ _
  | .conv ht hAB => case_conv hM (sound_typed ht) (sound_defEq hAB)
  | .prim c args hok hT =>
    case_prim hM c args hok (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))

theorem sound_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} :
    DefEq Γ t s A r → PEq hM Γ t s A r
  | .refl ht => eq_refl hM (sound_typed ht)
  | .symm h => eq_symm hM (sound_defEq h)
  | .trans h h' => eq_trans hM (sound_defEq h) (sound_defEq h')
  | .conv h hAB => eq_conv hM (sound_defEq h) (sound_defEq hAB)
  | .betaData hj hA hb ha =>
    eq_betaData hM hj (sound_typed hA) (sound_typed hb) (sound_typed ha) (cls_of_typed hA)
      (cls_of_typed hb) (tyOk_of_typed hb).1.cls (cls_of_typed ha)
  | .betaProp hA hb ha =>
    eq_betaProp hM (sound_typed hA) (sound_typed hb) (sound_typed ha) (cls_of_typed hA)
      (tyOk_of_typed hb).1.cls (cls_of_typed ha)
  | .zeta hv hb => eq_zeta hM (sound_typed hv) (sound_typed hb) (cls_of_typed hv) (cls_of_typed hb)
  | .eta hj hf =>
    eq_eta hM hj (sound_typed hf) (cls_of_typed hf) (tyOk_of_typed hf).1.2.1.cls
      (tyOk_of_typed hf).1.2.2.cls
  | .proofIrrel hh hh' => eq_proofIrrel hM (sound_typed hh) (sound_typed hh')
  | @DefEq.congrPiData m Γ i j A A' B B' hj hA hB =>
    eq_congrPiData hM hj (sound_defEq hA) (sound_defEq hB) (cls_of_defEq hA).1 (cls_of_defEq hA).2
      (cls_of_defEq hB).1
      ((Term.cls_congr (Ctx.levels_snoc_congr rfl A' A i) B').trans (cls_of_defEq hB).2)
  | @DefEq.congrPiProp m Γ i A A' B B' hA hB =>
    eq_congrPiProp hM (sound_defEq hA) (sound_defEq hB) (cls_of_defEq hA).1 (cls_of_defEq hA).2
      (cls_of_defEq hB).1
      ((Term.cls_congr (Ctx.levels_snoc_congr rfl A' A i) B').trans (cls_of_defEq hB).2)
  | @DefEq.congrLamData m Γ i j A A' b b' B hj hA hb =>
    eq_congrLamData hM hj (sound_defEq hA) (sound_defEq hb) (cls_of_defEq hA).1 (cls_of_defEq hA).2
      (cls_of_defEq hb).1
      ((Term.cls_congr (Ctx.levels_snoc_congr rfl A' A i) b').trans (cls_of_defEq hb).2)
      (tyOk_of_defEq hb).1.cls
  | .congrLamProp hA hb =>
    eq_congrLamProp hM (sound_defEq hA) (sound_defEq hb) (cls_of_defEq hA).1 (tyOk_of_defEq hb).1.cls
  | .congrAppData hj hf ha =>
    eq_congrAppData hM hj (sound_defEq hf) (sound_defEq ha) (cls_of_defEq hf).1 (cls_of_defEq hf).2
      (cls_of_defEq ha).1 (cls_of_defEq ha).2 (tyOk_of_defEq hf).1.2.1.cls (tyOk_of_defEq hf).1.2.2.cls
  | .congrAppProp hf ha =>
    eq_congrAppProp hM (sound_defEq hf) (sound_defEq ha) (cls_of_defEq ha).1
      (tyOk_of_defEq hf).1.2.1.cls (tyOk_of_defEq hf).1.2.2.cls
  | .congrLet hv hb =>
    eq_congrLet hM (sound_defEq hv) (sound_defEq hb) (cls_of_defEq hv).1 (cls_of_defEq hv).2
      (cls_of_defEq hb).1 (cls_of_defEq hb).2
  | .weak h _ => eq_weak hM (sound_defEq h) _ _
  | .congrPrim c args args' hok hd =>
    eq_congrPrim hM c args args' hok (fun k => (cls_of_defEq (hd k)).1) (fun k => (cls_of_defEq (hd k)).2)
      (fun k => sound_defEq (hd k))
  | @DefEq.eqRecRefl m Γ i j A a C c hT =>
    eq_eqRecRefl hM i j A a C c (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.sigmaFst m Γ i j A B a b hj hT =>
    eq_sigmaFst hM i j A B a b hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.sigmaSnd m Γ i j A B a b hj hT =>
    eq_sigmaSnd hM i j A B a b hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.sigmaEta m Γ i j A B s hj hT =>
    eq_sigmaEta hM i j A B s hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.downUp m Γ i d A a hT =>
    eq_downUp hM i d A a (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.upDown m Γ i d A a hT =>
    eq_upDown hM i d A a (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.sumRecInl m Γ i j k A B C f g a hk hT ha =>
    eq_sumRecInl hM i j k A B C f g a hk (fun l => cls_of_typed (hT l)) (fun l => sound_typed (hT l))
      (cls_of_typed ha) (sound_typed ha)
  | @DefEq.sumRecInr m Γ i j k A B C f g b hk hT hb =>
    eq_sumRecInr hM i j k A B C f g b hk (fun l => cls_of_typed (hT l)) (fun l => sound_typed (hT l))
      (cls_of_typed hb) (sound_typed hb)
  | @DefEq.natRecZero m Γ j C z s hj hT =>
    eq_natRecZero hM j C z s hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
  | @DefEq.natRecSucc m Γ j C z s n hj hT hn =>
    eq_natRecSucc hM j C z s n hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
      (cls_of_typed hn) (sound_typed hn)
  | @DefEq.quotLiftMk m Γ i j A R C f h a hi hj hT ha =>
    eq_quotLiftMk hM i j A R C f h a hi hj (fun k => cls_of_typed (hT k)) (fun k => sound_typed (hT k))
      (cls_of_typed ha) (sound_typed ha)

end

/-- **Soundness** (draft 2, Theorem 4.1).  In a model of `H`, a certified
term `Γ ⊢ t : A @ r` has, under every valid environment, a unique value; its
type has a unique value, lying in the universe `U_r`; and the value of the
term is an element (via `j_r`) of the value of its type. -/
theorem soundness {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (ht : Typed Γ t A r) (η : Env M.T m)
    (hv : Valid hM Γ η) :
    (∃! w, Val M.T Γ t η w) ∧ (∃! vA, Val M.T Γ A η vA) ∧
    (∀ vA, Val M.T Γ A η vA → TMem (r + 1) vA (univVal hM r)) ∧
    (∀ w vA, Val M.T Γ t η w → Val M.T Γ A η vA → TMem r w vA) :=
  sound_typed hM ht η hv

/-- **Soundness for definitional equality**: definitionally equal certified
terms have the same values. -/
theorem soundness_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : DefEq Γ t s A r)
    (η : Env M.T m) (hv : Valid hM Γ η) (w : M.T.El) : Val M.T Γ t η w ↔ Val M.T Γ s η w :=
  (sound_defEq hM h).2 η hv w

/-- The empty environment is valid for the empty context. -/
theorem Valid.nil (Γ : Ctx 0) : Valid hM Γ (fun i => i.elim0) := fun i => i.elim0

/-- Soundness for closed terms. -/
theorem soundness_closed {Γ : Ctx 0} {t A : Term} {r : ℕ} (ht : Typed Γ t A r) :
    ∃ (w : M.T.U r) (vA : M.T.U (r + 1)),
      (∀ w', Val M.T Γ t (fun i => i.elim0) w' ↔ w' = M.T.inj w) ∧
      (∀ vA', Val M.T Γ A (fun i => i.elim0) vA' ↔ vA' = M.T.inj vA) ∧
      M.T.mem (M.T.j (r + 1) vA) (hM.univSet r) ∧ M.T.mem (M.T.j r w) vA := by
  have h := sound_typed hM ht
  obtain ⟨w, hw, hmem⟩ := PTy.term_val hM h (Valid.nil hM Γ)
  obtain ⟨vA, hvA, hAU⟩ := PTy.tyval hM h (Valid.nil hM Γ)
  exact ⟨w, vA, hw, hvA, hAU, hmem vA ((hvA _).2 rfl)⟩

end SolidLean.Calc
