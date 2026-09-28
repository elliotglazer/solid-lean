import Solid.FO.Render
import Solid.Calc.Adequacy

/-!
# `H` and `T_L` as first-order theories, and what they prove

The tower theory `H` and the theory `T_L` of the core annotated calculus are
written as theories of the `Foundation` library (`H_FO`, `TL_FO`), so that
`⊢` is derivability in a sequent calculus for first-order logic.  The
semantic theorems of `Calc/Soundness.lean` and `Calc/Adequacy.lean` then
become provability statements, by the completeness theorem
(`Render.provable_of_semantic`):

* **Theorem 4.1 as an `H`-scheme** (`H_soundness`, `H_soundness_defEq`):
  for every certified judgement `Γ ⊢ t : A @ r`, `H` proves the sentence
  `soundSentence Γ t A r` — for every valid environment the evaluator
  formula of `t` has a unique value of sort `r`, that of `A` a unique value
  of sort `r + 1` lying in `U_r`, and the former lies in the latter; and for
  every certified definitional equality the two evaluator formulas agree.
* **Claim 6.1 (i)** (`TL_adequacy`): `T_L` proves the same about its graph
  symbols `R_{Γ,t}`, `R_{Γ,A}`.
* **Claim 6.1 (ii)** (`H_truth`, `TL_truth`): if `p : φ` is certified for a
  closed proposition `φ`, `H` and `T_L` prove that the value of `φ` is
  inhabited.

The sentences are built from the evaluator formulas by the explicit
combinators below; their satisfaction is computed once (`Sat_concF`,
`Sat_validF`) and matched against the semantic theorems.
-/

universe u v

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF SolidLean.Solid.ClauseFamily SolidLean.Solid.Render
open FFL FirstOrder

local notation "cs" => Fin.castSucc

/-! ### Formula combinators -/

section Combinators

variable {Sig : Signature} {k : ℕ} {s : Fin k → ℕ}

/-- A formula in the variables `x̄, w` read in the context `x̄, y, w`: the
new variable `y` (of sort `p`) is inserted just before the last one. -/
def insertBefore (p : ℕ) {n : ℕ} (φ : Formula Sig (k + 1) (Fin.snoc s n)) :
    Formula Sig (k + 2) (Fin.snoc (Fin.snoc s p) n) :=
  Formula.rename (Fin.snoc (α := fun _ => Fin (k + 2)) (fun i => cs (cs i)) (Fin.last (k + 1)))
    (fun i => by
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simp
      · simp) φ

theorem Sat_insertBefore {M : Str.{u} Sig} (p : ℕ) {n : ℕ} (φ : Formula Sig (k + 1) (Fin.snoc s n))
    (t : Fin k → Sorted.El M.U) (y x : Sorted.El M.U) :
    (insertBefore p φ).Sat M (Fin.snoc (α := fun _ => Sorted.El M.U)
      (Fin.snoc (α := fun _ => Sorted.El M.U) t y) x) ↔
    φ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) t x) := by
  unfold insertBefore
  rw [Formula.sat_rename]
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U)
      (Fin.snoc (α := fun _ => Sorted.El M.U) t y) x
      (Fin.snoc (α := fun _ => Fin (k + 2)) (fun i => cs (cs i)) (Fin.last (k + 1)) i)) =
      Fin.snoc (α := fun _ => Sorted.El M.U) t x := by
    funext i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp
    · simp
  rw [e]

/-- A formula in the variables `x̄, w` read in the context `x̄, w, y`: a new
last variable `y` (of sort `p`). -/
def addLast (p : ℕ) {n : ℕ} (φ : Formula Sig (k + 1) (Fin.snoc s n)) :
    Formula Sig (k + 2) (Fin.snoc (Fin.snoc s n) p) :=
  Formula.rename cs (fun i => by simp) φ

theorem Sat_addLast {M : Str.{u} Sig} (p : ℕ) {n : ℕ} (φ : Formula Sig (k + 1) (Fin.snoc s n))
    (t : Fin k → Sorted.El M.U) (x y : Sorted.El M.U) :
    (addLast p φ).Sat M (Fin.snoc (α := fun _ => Sorted.El M.U)
      (Fin.snoc (α := fun _ => Sorted.El M.U) t x) y) ↔
    φ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) t x) := by
  unfold addLast
  rw [Formula.sat_rename]
  have e : (fun i => Fin.snoc (α := fun _ => Sorted.El M.U)
      (Fin.snoc (α := fun _ => Sorted.El M.U) t x) y (cs i)) =
      Fin.snoc (α := fun _ => Sorted.El M.U) t x := by
    funext i; simp
  rw [e]

/-- `∃! w : n. φ(x̄, w)`. -/
def existsUniqueF (n : ℕ) (φ : Formula Sig (k + 1) (Fin.snoc s n)) : Formula Sig k s :=
  .ex n (Formula.and φ (Formula.all n (Formula.imp (insertBefore n φ)
    (.eq (cs (Fin.last k)) (Fin.last (k + 1)) (by simp)))))

theorem Sat_existsUniqueF {M : Str.{u} Sig} (n : ℕ) (φ : Formula Sig (k + 1) (Fin.snoc s n))
    (t : Fin k → Sorted.El M.U) :
    (existsUniqueF n φ).Sat M t ↔
      ∃! x : Sorted.El M.U, x.1 = n ∧ φ.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) t x) := by
  unfold existsUniqueF
  simp only [Formula.Sat_ex, Formula.Sat_and, Formula.Sat_all, Formula.Sat_imp, Sat_insertBefore,
    Formula.Sat_eq, Fin.snoc_castSucc, Fin.snoc_last]
  constructor
  · rintro ⟨x, hx, hφ, hu⟩
    exact ⟨x, ⟨hx, hφ⟩, fun y ⟨hy, hφy⟩ => (hu y hy hφy).symm⟩
  · rintro ⟨x, ⟨hx, hφ⟩, hu⟩
    exact ⟨x, hx, hφ, fun y hy hφy => (hu y ⟨hy, hφy⟩).symm⟩

/-- The conjunction of a list of formulas. -/
def andList : List (Formula Sig k s) → Formula Sig k s
  | [] => Formula.true_
  | φ :: l => Formula.and φ (andList l)

theorem Sat_andList {M : Str.{u} Sig} :
    ∀ (l : List (Formula Sig k s)) (t : Fin k → Sorted.El M.U),
      (andList l).Sat M t ↔ ∀ φ ∈ l, φ.Sat M t
  | [], t => by simp [andList, Formula.true_]
  | φ :: l, t => by simp [andList, Sat_andList l t]

end Combinators

/-! ### Membership of values, universes, validity -/

section Tower

variable {k : ℕ} {s : Fin k → ℕ}

/-- `j_r(x_i) ∈ x_j`, with `x_i` of sort `r` and `x_j` of sort `r + 1`. -/
def jMemF (r : ℕ) (i j : Fin k) (hi : s i = r) (hj : s j = r + 1) : TF k s :=
  .ex (r + 1) (Formula.and (liftZF r (cs i) (Fin.last k) (by simp [hi]) (by simp))
    (memF (r + 1) (Fin.last k) (cs j) (by simp) (by simp [hj])))

theorem Sat_jMemF (N : TowerWithClasses.{u}) {r : ℕ} {i j : Fin k} {hi : s i = r} {hj : s j = r + 1}
    (t : Fin k → N.T.El) :
    (jMemF r i j hi hj).Sat N.T.toStr t ↔ TMem (M := N) r (t i) (t j) := by
  unfold jMemF TMem
  simp only [Formula.Sat_ex, Formula.Sat_and, Sat_liftZF', Sat_memF', Fin.snoc_castSucc,
    Fin.snoc_last]
  constructor
  · rintro ⟨z, hz, ⟨x, hx, rfl⟩, ⟨x', y, hx', hy, h⟩⟩
    rw [← Sorted.inj_injective N.T.U hx'] at h
    exact ⟨x, y, hx, hy, h⟩
  · rintro ⟨x, y, hx, hy, h⟩
    exact ⟨N.T.inj (N.T.j r x), rfl, ⟨x, hx, rfl⟩, ⟨_, y, rfl, hy, h⟩⟩

theorem El.eq_inj {U : ℕ → Type u} (e : Sorted.El U) {n : ℕ} (h : e.1 = n) :
    ∃ e' : U n, e = Sorted.inj U e' := by
  obtain ⟨m, e⟩ := e
  cases h
  exact ⟨e, rfl⟩

/-- `x_w ∈ U_r`, for the last variable `w` of the context `x̄, w`, of sort
`r + 1`: there is `u` of sort `r + 2` which is the universe `U_r` with
`j(x_w) ∈ u`. -/
def inUnivF {m : ℕ} (lev : Fin m → ℕ) (r : ℕ) : TF (m + 1) (Fin.snoc lev (r + 1)) :=
  .ex (r + 2) (Formula.and (univF r (Fin.last (m + 1)) (by simp))
    (jMemF (r + 1) (cs (Fin.last m)) (Fin.last (m + 1)) (by simp) (by simp)))

theorem Sat_inUnivF {N : TowerWithClasses.{u}} (hN : IsTowerModel N) {m : ℕ} (lev : Fin m → ℕ)
    (r : ℕ) (t : Fin m → N.T.El) (vA : N.T.El) :
    (inUnivF lev r).Sat N.T.toStr (Fin.snoc (α := fun _ => N.T.El) t vA) ↔
      TMem (M := N) (r + 1) vA (univVal hN r) := by
  unfold inUnivF
  rw [Formula.Sat_ex]
  constructor
  · rintro ⟨u, hu, h⟩
    rw [Formula.Sat_and] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨u', rfl⟩ := El.eq_inj u hu
    have h1' := (Sat_univF N.T r _ _ _ u' (by simp)).1 h1
    rw [hN.isUnivSet_iff] at h1'
    have h2' := (Sat_jMemF N _).1 h2
    simp only [Fin.snoc_castSucc, Fin.snoc_last] at h2'
    subst h1'
    exact h2'
  · intro h
    refine ⟨univVal hN r, rfl, ?_⟩
    rw [Formula.Sat_and]
    refine ⟨?_, ?_⟩
    · exact (Sat_univF N.T r _ _ _ (hN.univSet r) (by simp)).2 ((hN.isUnivSet_iff r _).2 rfl)
    · refine (Sat_jMemF N _).2 ?_
      simpa using h

/-- The validity condition of the variable `x` of a context: the type of
`x` has a unique value, which contains the value of `x` and lies in the
universe of the level of `x`.  (When the classifier of the type of `x` is
not of the required sort, the condition is `⊥`.) -/
noncomputable def validAtF {m : ℕ} (Γ : Ctx m) (x : Fin m) : TF m Γ.levels :=
  if h : (Term.shift x (m - x) (Γ x).1).cls Γ = (Γ x).2 + 1 then
    Formula.and
      (existsUniqueF ((Γ x).2 + 1)
        (Formula.recast (fun i => by rw [h]) (eval Γ (Term.shift x (m - x) (Γ x).1))))
      (Formula.all ((Γ x).2 + 1) (Formula.imp
        (Formula.recast (fun i => by rw [h]) (eval Γ (Term.shift x (m - x) (Γ x).1)))
        (Formula.and (jMemF (Γ x).2 (cs x) (Fin.last m) (by simp [Ctx.levels]) (by simp))
          (inUnivF Γ.levels (Γ x).2))))
  else Formula.false_

/-- The validity condition of a context (draft 2, §4.2), as a formula in the
variables of the context. -/
noncomputable def validF {m : ℕ} (Γ : Ctx m) : TF m Γ.levels :=
  andList ((List.finRange m).map (validAtF Γ))

end Tower

/-! ### Satisfaction in a structure for an expanded signature -/

theorem Sat_inl_Δ {F : ClauseFamily.{u}} {M : Str.{u} F.sig} (hwf : IsWF M) {k : ℕ} {s : Fin k → ℕ}
    (ψ : TF k s) (t : Fin k → Sorted.El M.U) :
    (ψ.inl (F := F)).Sat M t ↔ ψ.Sat (Δ M hwf).toStr t :=
  (Formula.Sat_inl M ψ t).trans (Sat_Δ_toStr hwf ψ t).symm

theorem Sat_validF' {N : TowerWithClasses.{u}} (hN : IsTowerModel N) {m : ℕ} (Γ : Ctx m)
    (η : Env N.T m) : (validF Γ).Sat N.T.toStr η ↔ Valid hN Γ η := by
  unfold validF Valid
  rw [Sat_andList]
  simp only [List.forall_mem_map, List.mem_finRange, true_implies]
  refine forall_congr' fun x => ?_
  unfold validAtF
  split_ifs with h
  · have hV : ∀ vA, Val N.T Γ (Term.shift x (m - x) (Γ x).1) η vA ↔
        vA.1 = (Γ x).2 + 1 ∧
          (Formula.recast (fun i => by rw [h]) (eval Γ (Term.shift x (m - x) (Γ x).1))).Sat
            N.T.toStr (Fin.snoc (α := fun _ => N.T.El) η vA) := fun vA => by
      unfold Val
      exact and_congr (by rw [h]) (Formula.Sat_recast _ _ _).symm
    rw [Formula.Sat_and, Sat_existsUniqueF, Formula.Sat_all]
    refine and_congr (existsUnique_congr fun vA => (hV vA).symm) ?_
    refine ⟨fun H vA hvA => ?_, fun H vA hvA hs => ?_⟩
    · obtain ⟨h1, h2⟩ := (hV vA).1 hvA
      have := H vA h1 h2
      rw [Formula.Sat_and, Sat_jMemF N, Sat_inUnivF hN] at this
      simpa using this
    · have := H vA ((hV vA).2 ⟨hvA, hs⟩)
      rw [Formula.Sat_and, Sat_jMemF N, Sat_inUnivF hN]
      simpa using this
  · rw [Formula.Sat_false]
    constructor
    · exact False.elim
    · rintro ⟨⟨vA, hvA, -⟩, H⟩
      exact h (hvA.sort.symm.trans (H vA hvA).1.sort_right)

theorem Sat_validF {F : ClauseFamily.{u}} {M : Str.{u} F.sig} {hwf : IsWF M}
    {𝒟 : ClassSystem (Δ M hwf)} (hN : IsTowerModel ⟨Δ M hwf, 𝒟⟩) {m : ℕ} (Γ : Ctx m)
    (η : Fin m → Sorted.El M.U) :
    ((validF Γ).inl (F := F)).Sat M η ↔ Valid hN Γ η :=
  (Sat_inl_Δ hwf _ _).trans (Sat_validF' hN Γ η)

/-- The conclusion of Theorem 4.1 for value predicates `φt` (in `x̄, w`,
`w` of sort `r`) and `φA` (in `x̄, vA`, `vA` of sort `r + 1`): `φt` has a
unique value, `φA` a unique value which lies in `U_r`, and every value of
`φt` lies in every value of `φA`. -/
def concF {F : ClauseFamily.{u}} {m : ℕ} {lev : Fin m → ℕ} (r : ℕ)
    (φt : Formula F.sig (m + 1) (Fin.snoc lev r)) (φA : Formula F.sig (m + 1) (Fin.snoc lev (r + 1))) :
    Formula F.sig m lev :=
  Formula.and (existsUniqueF r φt)
  (Formula.and (existsUniqueF (r + 1) φA)
  (Formula.and (Formula.all (r + 1) (Formula.imp φA (inUnivF lev r).inl))
    (Formula.all r (Formula.all (r + 1) (Formula.imp (addLast (r + 1) φt)
      (Formula.imp (insertBefore r φA)
        (jMemF r (cs (Fin.last m)) (Fin.last (m + 1)) (by simp) (by simp)).inl))))))

theorem Sat_concF {F : ClauseFamily.{u}} {M : Str.{u} F.sig} {hwf : IsWF M}
    {𝒟 : ClassSystem (Δ M hwf)} (hN : IsTowerModel ⟨Δ M hwf, 𝒟⟩) {m : ℕ} {lev : Fin m → ℕ} (r : ℕ)
    (φt : Formula F.sig (m + 1) (Fin.snoc lev r)) (φA : Formula F.sig (m + 1) (Fin.snoc lev (r + 1)))
    (η : Fin m → Sorted.El M.U) :
    (concF r φt φA).Sat M η ↔
      (∃! w : Sorted.El M.U, w.1 = r ∧ φt.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η w)) ∧
      (∃! vA : Sorted.El M.U, vA.1 = r + 1 ∧
        φA.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η vA)) ∧
      (∀ vA : Sorted.El M.U, vA.1 = r + 1 →
        φA.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η vA) →
        TMem (M := ⟨Δ M hwf, 𝒟⟩) (r + 1) vA (univVal hN r)) ∧
      (∀ w : Sorted.El M.U, w.1 = r → ∀ vA : Sorted.El M.U, vA.1 = r + 1 →
        φt.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η w) →
        φA.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η vA) →
        TMem (M := ⟨Δ M hwf, 𝒟⟩) r w vA) := by
  unfold concF
  rw [Formula.Sat_and, Formula.Sat_and, Formula.Sat_and, Sat_existsUniqueF, Sat_existsUniqueF]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ?_ ?_))
  · rw [Formula.Sat_all]
    refine forall_congr' fun vA => forall_congr' fun _ => ?_
    rw [Formula.Sat_imp]
    exact imp_congr Iff.rfl ((Sat_inl_Δ hwf _ _).trans (Sat_inUnivF hN lev r η vA))
  · rw [Formula.Sat_all]
    refine forall_congr' fun w => forall_congr' fun _ => ?_
    rw [Formula.Sat_all]
    refine forall_congr' fun vA => forall_congr' fun _ => ?_
    rw [Formula.Sat_imp, Sat_addLast, Formula.Sat_imp, Sat_insertBefore]
    refine imp_congr Iff.rfl (imp_congr Iff.rfl ?_)
    refine (Sat_inl_Δ hwf _ _).trans ((Sat_jMemF ⟨Δ M hwf, 𝒟⟩ _).trans ?_)
    simp only [Fin.snoc_castSucc, Fin.snoc_last]

/-- The soundness statement for `φt`, `φA` holds under every valid
environment, when they read as the value relations of a certified `t : A`. -/
theorem sound_of_val {F : ClauseFamily.{u}} {M : Str.{u} F.sig} {hwf : IsWF M}
    (hN : IsTowerModel ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩)
    {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r)
    {φt : Formula F.sig (m + 1) (Fin.snoc Γ.levels r)}
    {φA : Formula F.sig (m + 1) (Fin.snoc Γ.levels (r + 1))}
    (η : Fin m → Sorted.El M.U)
    (hVt : ∀ w, Val (Δ M hwf) Γ t η w ↔
      w.1 = r ∧ φt.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η w))
    (hVA : ∀ vA, Val (Δ M hwf) Γ A η vA ↔
      vA.1 = r + 1 ∧ φA.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η vA)) :
    (Formula.imp (validF Γ).inl (concF r φt φA)).Sat M η := by
  rw [Formula.Sat_imp, Sat_validF hN Γ η, Sat_concF hN]
  intro hv
  obtain ⟨H1, H2, H3, H4⟩ := soundness hN h η hv
  exact ⟨(existsUnique_congr hVt).1 H1, (existsUnique_congr hVA).1 H2,
    fun vA hvA hsat => H3 vA ((hVA vA).2 ⟨hvA, hsat⟩),
    fun w hw vA hvA hwt hvAA => H4 w vA ((hVt w).2 ⟨hw, hwt⟩) ((hVA vA).2 ⟨hvA, hvAA⟩)⟩

/-! ### Theorem 4.1 as an `H`-scheme -/

/-- The soundness sentence of a certified judgement `Γ ⊢ t : A @ r`: for
every valid environment, the evaluator formula of `t` has a unique value of
sort `r`, that of `A` a unique value of sort `r + 1` lying in `U_r`, and the
former lies in the latter.  A sentence of the signature of any clause
family (it uses only the tower symbols). -/
noncomputable def soundSentence (F : ClauseFamily.{u}) {m : ℕ} (Γ : Ctx m) (t A : Term) (r : ℕ)
    (ht : t.cls Γ = r) (hA : A.cls Γ = r + 1) : Sentence F.sig :=
  Formula.closeAll (Formula.imp (validF Γ).inl
    (concF r (Formula.recast (fun i => by rw [ht]) (eval Γ t)).inl
      (Formula.recast (fun i => by rw [hA]) (eval Γ A)).inl))

/-- The value relation of `t` read through the (recast, embedded) evaluator
formula. -/
theorem Val_iff_inl {F : ClauseFamily.{u}} {M : Str.{u} F.sig} (hwf : IsWF M) {m : ℕ} (Γ : Ctx m)
    (t : Term) {r : ℕ} (ht : t.cls Γ = r) (η : Fin m → Sorted.El M.U) (w : Sorted.El M.U) :
    Val (Δ M hwf) Γ t η w ↔ w.1 = r ∧
      ((Formula.recast (s' := Fin.snoc Γ.levels r) (fun i => by rw [ht]) (eval Γ t)).inl (F := F)).Sat M
        (Fin.snoc (α := fun _ => Sorted.El M.U) η w) := by
  unfold Val
  exact and_congr (by rw [ht]) ((Sat_inl_Δ hwf _ _).trans (Formula.Sat_recast _ _ _)).symm

theorem soundSentence_holds {F : ClauseFamily.{u}} {M : Str.{u} F.sig} (hwf : IsWF M)
    (hN : IsTowerModel ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩)
    {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    Sentence.Holds (soundSentence F Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) M := by
  unfold soundSentence
  rw [Formula.Sat_closeAll]
  intro η hη
  exact sound_of_val hN h η (Val_iff_inl hwf Γ t (cls_of_typed h) η)
    (Val_iff_inl hwf Γ A (tyOk_of_typed h).1.cls η)

/-- The sentence of a certified definitional equality `Γ ⊢ t ≡ s : A @ r`:
the two evaluator formulas agree under every valid environment. -/
noncomputable def defEqSentence (F : ClauseFamily.{u}) {m : ℕ} (Γ : Ctx m) (t s : Term) (r : ℕ)
    (ht : t.cls Γ = r) (hs : s.cls Γ = r) : Sentence F.sig :=
  Formula.closeAll (Formula.imp (validF Γ).inl
    (Formula.all r (Formula.iff (Formula.recast (fun i => by rw [ht]) (eval Γ t)).inl
      (Formula.recast (fun i => by rw [hs]) (eval Γ s)).inl)))

theorem defEqSentence_holds {F : ClauseFamily.{u}} {M : Str.{u} F.sig} (hwf : IsWF M)
    (hN : IsTowerModel ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩)
    {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : DefEq Γ t s A r) :
    Sentence.Holds (defEqSentence F Γ t s r (cls_of_defEq h).1 (cls_of_defEq h).2) M := by
  unfold defEqSentence
  rw [Formula.Sat_closeAll]
  intro η hη
  rw [Formula.Sat_imp, Sat_validF hN Γ η]
  intro hv
  rw [Formula.Sat_all]
  intro w hw
  rw [Formula.Sat_iff]
  have e := soundness_defEq hN h η hv w
  rw [Val_iff_inl hwf Γ t (cls_of_defEq h).1 η w, Val_iff_inl hwf Γ s (cls_of_defEq h).2 η w] at e
  exact ⟨fun ht => (e.1 ⟨hw, ht⟩).2, fun hs => (e.2 ⟨hw, hs⟩).2⟩

/-- **Theorem 4.1, provably in `T(𝔉)`** for any clause family given by
formulas: the soundness sentence of every certified judgement is derivable
from the rendered axioms. -/
theorem soundness_provable {Sym' : Type} {arity : Sym' → ℕ} {sortAt : (f : Sym') → Fin (arity f) → ℕ}
    {φ : (f : Sym') → Formula TowerSig (arity f) (sortAt f)}
    {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    trT (TLax.{v} Sym' arity sortAt φ) ⊢ trS (soundSentence (ofFormulas.{v} Sym' arity sortAt φ)
      Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) :=
  provable_of_semantic _ fun _ hM => soundSentence_holds hM.wf hM.tower h

theorem soundness_defEq_provable {Sym' : Type} {arity : Sym' → ℕ}
    {sortAt : (f : Sym') → Fin (arity f) → ℕ}
    {φ : (f : Sym') → Formula TowerSig (arity f) (sortAt f)}
    {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : DefEq Γ t s A r) :
    trT (TLax.{v} Sym' arity sortAt φ) ⊢ trS (defEqSentence (ofFormulas.{v} Sym' arity sortAt φ)
      Γ t s r (cls_of_defEq h).1 (cls_of_defEq h).2) :=
  provable_of_semantic _ fun _ hM => defEqSentence_holds hM.wf hM.tower h

/-! ### `H` and `T_L` as first-order theories -/

/-- The clause family with no symbols: its theory `T(𝔉)` is `H` itself. -/
noncomputable def HFam : ClauseFamily.{v} :=
  ofFormulas Empty (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)

theorem TLax_empty :
    TLax.{v} Empty (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) = HFam.{v}.Hax := by
  unfold TLax
  rw [Set.range_eq_empty, Set.union_empty]
  rfl

/-- **`H` as a first-order theory** of the Foundation library: the rendering
of the sentences `Hax` (the ZFC axioms at every sort, with Separation and
Replacement as schemes; the well-formedness of the tower symbols; the tower
axioms), with the equality axioms. -/
noncomputable def H_FO : Theory (lang HFam.{v}.sig) := trT HFam.{v}.Hax

/-- **`T_L` as a first-order theory**: `H` together with one defining axiom
per graph symbol `R_{Γ,t}`. -/
noncomputable def TL_FO : Theory (lang LAnn.{v}.sig) :=
  trT (TLax.{v} Sym (fun s => s.1 + 1) (fun s => Fin.snoc s.2.1.levels (s.2.2.cls s.2.1))
    (fun s => eval s.2.1 s.2.2))

/-- **Theorem 4.1 as an `H`-scheme**: `H` proves the soundness sentence of
every certified judgement `Γ ⊢ t : A @ r`. -/
theorem H_soundness {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    H_FO.{v} ⊢ trS (soundSentence HFam.{v} Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) := by
  have := soundness_provable.{v} (Sym' := Empty) (arity := fun e => e.elim)
    (sortAt := fun e => e.elim) (φ := fun e => e.elim) h
  rw [TLax_empty] at this
  exact this

/-- `H` proves that definitionally equal certified terms have the same value. -/
theorem H_soundness_defEq {m : ℕ} {Γ : Ctx m} {t s A : Term} {r : ℕ} (h : DefEq Γ t s A r) :
    H_FO.{v} ⊢ trS (defEqSentence HFam.{v} Γ t s r (cls_of_defEq h).1 (cls_of_defEq h).2) := by
  have := soundness_defEq_provable.{v} (Sym' := Empty) (arity := fun e => e.elim)
    (sortAt := fun e => e.elim) (φ := fun e => e.elim) h
  rw [TLax_empty] at this
  exact this

/-- `T_L` proves the soundness sentence of every certified judgement (in
terms of the evaluator formulas). -/
theorem TL_soundness {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    TL_FO.{v} ⊢ trS (soundSentence LAnn.{v} Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) :=
  soundness_provable h

/-! ### Claim 6.1 (i): adequacy, provably in `T_L` -/

/-- The atom `R_{Γ,t}(x̄, w)` of `T_L`. -/
def graphF {m : ℕ} (Γ : Ctx m) (t : Term) :
    Formula LAnn.{v}.sig (m + 1) (Fin.snoc Γ.levels (t.cls Γ)) :=
  .rel (Sum.inr ⟨m, (Γ, t)⟩) (fun i => i) (fun _ => rfl)

/-- In a model of `T_L`, the atom `R_{Γ,t}` is the value relation. -/
theorem Sat_graphF {M : Str.{v} LAnn.{v}.sig} (hM : LAnn.{v}.IsGenModel ⟨M, M.defSys⟩) {m : ℕ}
    (Γ : Ctx m) (t : Term) (η : Fin m → Sorted.El M.U) (hη : ∀ i, (η i).1 = Γ.levels i)
    (w : Sorted.El M.U) :
    (graphF Γ t).Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η w) ↔ Val (Δ M hM.wf) Γ t η w := by
  have hc := hM.clause ⟨m, (Γ, t)⟩
  have key : (graphF Γ t).Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) η w) ↔
      Fin.snoc (α := fun _ => Sorted.El M.U) η w ∈ LAnn.{v}.G ⟨m, (Γ, t)⟩ (Δ M hM.wf) := by
    show Fin.snoc (α := fun _ => Sorted.El M.U) η w ∈ M.rel (Sum.inr ⟨m, (Γ, t)⟩) ↔ _
    exact Set.ext_iff.1 hc _
  refine key.trans ?_
  show (eval Γ t).Sat (Δ M hM.wf).toStr (Fin.snoc (α := fun _ => Sorted.El M.U) η w) ∧
    (∀ i, (Fin.snoc (α := fun _ => Sorted.El M.U) η w i).1 = Fin.snoc (α := fun _ => ℕ) Γ.levels (t.cls Γ) i) ↔ _
  unfold Val
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1⟩
    simpa using h2 (Fin.last m)
  · rintro ⟨h1, h2⟩
    refine ⟨h2, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa using h1
    · simpa using hη i

theorem Val_iff_graphF {M : Str.{v} LAnn.{v}.sig} (hM : LAnn.{v}.IsGenModel ⟨M, M.defSys⟩) {m : ℕ}
    (Γ : Ctx m) (t : Term) {r : ℕ} (ht : t.cls Γ = r) (η : Fin m → Sorted.El M.U)
    (hη : ∀ i, (η i).1 = Γ.levels i) (w : Sorted.El M.U) :
    Val (Δ M hM.wf) Γ t η w ↔ w.1 = r ∧
      (Formula.recast (s' := Fin.snoc Γ.levels r) (fun i => by rw [ht]) (graphF Γ t)).Sat M
        (Fin.snoc (α := fun _ => Sorted.El M.U) η w) := by
  rw [Formula.Sat_recast, Sat_graphF hM Γ t η hη w]
  exact ⟨fun h => ⟨h.sort.trans ht, h⟩, fun h => h.2⟩

/-- The adequacy sentence of a certified judgement `Γ ⊢ t : A @ r`: for every
valid environment, `R_{Γ,t}` has a unique value of sort `r`, `R_{Γ,A}` a
unique value of sort `r + 1` lying in `U_r`, and the former lies in the
latter. -/
noncomputable def adequacySentence {m : ℕ} (Γ : Ctx m) (t A : Term) (r : ℕ) (ht : t.cls Γ = r)
    (hA : A.cls Γ = r + 1) : Sentence LAnn.{v}.sig :=
  Formula.closeAll (Formula.imp (validF Γ).inl
    (concF r (Formula.recast (fun i => by rw [ht]) (graphF Γ t))
      (Formula.recast (fun i => by rw [hA]) (graphF Γ A))))

theorem adequacySentence_holds {M : Str.{v} LAnn.{v}.sig} (hM : LAnn.{v}.IsGenModel ⟨M, M.defSys⟩)
    {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    Sentence.Holds (adequacySentence Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) M := by
  unfold adequacySentence
  rw [Formula.Sat_closeAll]
  intro η hη
  exact sound_of_val hM.tower h η (Val_iff_graphF hM Γ t (cls_of_typed h) η hη)
    (Val_iff_graphF hM Γ A (tyOk_of_typed h).1.cls η hη)

/-- **Claim 6.1 (i)**: `T_L` proves the adequacy sentence of every certified
judgement. -/
theorem TL_adequacy {m : ℕ} {Γ : Ctx m} {t A : Term} {r : ℕ} (h : Typed Γ t A r) :
    TL_FO.{v} ⊢ trS (adequacySentence Γ t A r (cls_of_typed h) (tyOk_of_typed h).1.cls) :=
  provable_of_semantic _ fun _ hM => adequacySentence_holds hM h

/-! ### Claim 6.1 (ii): truth of derivable propositions -/

/-- `Tr(x_0)`: the value `x_0` (of sort `1`) of a proposition is inhabited —
some `x` of sort `0` has `j_0(x) ∈ x_0`. -/
def trF (lev : Fin 0 → ℕ) : TF 1 (Fin.snoc lev 1) :=
  .ex 0 (jMemF 0 (Fin.last 1) (cs (Fin.last 0)) (Fin.snoc_last _ _)
    ((Fin.snoc_castSucc _ _ _).trans (Fin.snoc_last _ _)))

/-- The truth sentence of a closed proposition `φ`, for a value predicate
`φv` of `φ` (in the single variable `x_0` of sort `1`): every value of `φ`
is inhabited. -/
noncomputable def truthSentence (F : ClauseFamily.{u}) (Γ₀ : Ctx 0)
    (φv : Formula F.sig 1 (Fin.snoc Γ₀.levels 1)) : Sentence F.sig :=
  Formula.closeAll (Formula.imp φv (trF Γ₀.levels).inl)

theorem truthSentence_holds {F : ClauseFamily.{u}} {M : Str.{u} F.sig} {hwf : IsWF M}
    (hN : IsTowerModel ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩)
    {Γ₀ : Ctx 0} {p φ : Term} (h : Typed Γ₀ p φ 0) {φv : Formula F.sig 1 (Fin.snoc Γ₀.levels 1)}
    (hV : ∀ v, Val (Δ M hwf) Γ₀ φ (fun i => i.elim0) v ↔ v.1 = 1 ∧
      φv.Sat M (Fin.snoc (α := fun _ => Sorted.El M.U) (fun i => i.elim0) v)) :
    Sentence.Holds (truthSentence F Γ₀ φv) M := by
  unfold truthSentence
  rw [Formula.Sat_closeAll]
  intro η hη
  rw [Formula.Sat_imp]
  intro hsat
  have e : η = Fin.snoc (α := fun _ => Sorted.El M.U) (fun i => i.elim0) (η (Fin.last 0)) := by
    funext i
    refine Fin.lastCases ?_ (fun i => i.elim0) i
    simp
  obtain ⟨H1, -, -, H4⟩ := soundness hN h (fun i => i.elim0) (Valid.nil hN Γ₀)
  obtain ⟨w, hw, -⟩ := H1
  have hvφ : Val (Δ M hwf) Γ₀ φ (fun i => i.elim0) (η (Fin.last 0)) :=
    (hV _).2 ⟨by simpa using hη (Fin.last 0), by rw [← e]; exact hsat⟩
  have hmem := H4 w _ hw hvφ
  refine (Sat_inl_Δ hwf _ _).2 ?_
  refine (Formula.Sat_ex _ _ _).2 ⟨w, hmem.sort_left, ?_⟩
  exact (Sat_jMemF ⟨Δ M hwf, ΔSys ⟨M, M.defSys⟩ hwf⟩ _).2 hmem

/-- **Claim 6.1 (ii) for `H`**: if `p : φ` is certified for a closed
proposition `φ`, `H` proves that the value of `φ` is inhabited. -/
theorem H_truth {Γ₀ : Ctx 0} {p φ : Term} (h : Typed Γ₀ p φ 0) :
    H_FO.{v} ⊢ trS (truthSentence HFam.{v} Γ₀
      (Formula.recast (fun i => by rw [(tyOk_of_typed h).1.cls]) (eval Γ₀ φ)).inl) := by
  have := provable_of_semantic.{v} (Sym := Empty) (arity := fun e => e.elim)
    (sortAt := fun e => e.elim) (φ := fun e => e.elim)
    (truthSentence HFam.{v} Γ₀
      (Formula.recast (fun i => by rw [(tyOk_of_typed h).1.cls]) (eval Γ₀ φ)).inl)
    fun _ hM => truthSentence_holds hM.tower h
      (Val_iff_inl hM.wf Γ₀ φ (tyOk_of_typed h).1.cls (fun i => i.elim0))
  rw [TLax_empty] at this
  exact this

/-- **Claim 6.1 (ii) for `T_L`**: if `p : φ` is certified for a closed
proposition `φ`, `T_L` proves that the value of `φ` is inhabited. -/
theorem TL_truth {Γ₀ : Ctx 0} {p φ : Term} (h : Typed Γ₀ p φ 0) :
    TL_FO.{v} ⊢ trS (truthSentence LAnn.{v} Γ₀
      (Formula.recast (fun i => by rw [(tyOk_of_typed h).1.cls]) (graphF Γ₀ φ))) :=
  provable_of_semantic _ fun _ hM => truthSentence_holds hM.tower h
    (Val_iff_graphF hM Γ₀ φ (tyOk_of_typed h).1.cls (fun i => i.elim0) (fun i => i.elim0))

end SolidLean.Calc
