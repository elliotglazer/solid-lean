import Solid.FO.Provable

/-!
# `T_L` is a conservative extension of `H`

In the set-encoded presentation, `T_L` is `H` with one symbol per context
and term, each defined by a formula of the tower signature.  Every model of
`H` expands to a model of `T_L` and the definable classes do not change, so a
sentence of the tower signature is provable from `T_L` iff it is provable
from `H` (`TL_conservative`): the set-theoretic content of `T_L` is exactly
`H` (draft 2, §7.5, in the encoded presentation, where `D` is the reduct and
`F` the expansion).

The tool is the elimination of the defined symbols from formulas
(`Formula.elim`): in a model of `T(𝔉)` a formula of `F.sig` and its
elimination have the same extension (`Sat_elim`), so the definable classes of
a model of `T(𝔉)` are those of its underlying tower.
-/

universe u v

namespace SolidLean.Solid

open Classical

namespace ClauseFamily

/-! ### Monotonicity of the tower axioms in the class system -/

/-- The tower axioms for a class system hold for any smaller one. -/
theorem _root_.SolidLean.Solid.IsTowerModel.mono {T : MemTower.{u}} {𝒟 𝒟' : ClassSystem T}
    (hle : ∀ k (C : Sorted.Rel T.U k), C ∈ 𝒟'.D k → C ∈ 𝒟.D k) (hT : IsTowerModel ⟨T, 𝒟⟩) :
    IsTowerModel ⟨T, 𝒟'⟩ where
  zfc n := SetAxioms.transfer id (fun y => ⟨y, rfl⟩) id (fun _ _ => Iff.rfl)
    (fun _ _ hC' => hle _ _ hC') (hT.zfc n)
  j_injective := hT.j_injective
  j_mem_iff := hT.j_mem_iff
  kappa_inaccessible := hT.kappa_inaccessible
  j_image := hT.j_image
  next_inaccessible := hT.next_inaccessible
  bottom := hT.bottom

/-! ### Eliminating the defined symbols -/

section Elim

variable {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
  {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}

/-- A formula of `F.sig`, for `F` given by formulas, as a formula of the
tower signature: each defined symbol is replaced by its clause. -/
noncomputable def _root_.SolidLean.Solid.Formula.elim :
    {k : ℕ} → {s : Fin k → ℕ} → Formula (ofFormulas.{u} Sym arity sortAt φ).sig k s →
      Formula TowerSig k s
  | _, _, .rel (.inl r) v hv => .rel r v hv
  | _, _, .rel (.inr f) v hv => Formula.rename v hv (φ f)
  | _, _, .eq i j h => .eq i j h
  | _, _, .false_ => .false_
  | _, _, .imp ψ χ => .imp ψ.elim χ.elim
  | _, _, .ex n ψ => .ex n ψ.elim

/-- In a model of `T(𝔉)`, a formula and its elimination agree on
well-sorted tuples. -/
theorem Sat_elim {N : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig} {𝒟 : StrSys N}
    (hN : (ofFormulas Sym arity sortAt φ).IsGenModel ⟨N, 𝒟⟩) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (ψ : Formula (ofFormulas.{u} Sym arity sortAt φ).sig k s)
      (t : Fin k → Sorted.El N.U), (∀ i, (t i).1 = s i) →
      (ψ.Sat N t ↔ ψ.elim.Sat (Δ N hN.wf).toStr t)
  | _, _, .rel (.inl r) v _, t, _ => by
    show (fun i => t (v i)) ∈ N.rel (.inl r) ↔ (fun i => t (v i)) ∈ (Δ N hN.wf).toStr.rel r
    rw [Δ_toStr_rel]
    exact Iff.rfl
  | _, _, .rel (.inr f) v hv, t, ht => by
    have hc := hN.clause f
    have key : (fun i => t (v i)) ∈ N.rel (.inr f) ↔
        (fun i => t (v i)) ∈ (ofFormulas.{u} Sym arity sortAt φ).G f (Δ N hN.wf) :=
      Set.ext_iff.1 hc _
    refine key.trans ?_
    show (φ f).Sat (Δ N hN.wf).toStr (fun i => t (v i)) ∧ (∀ i, (t (v i)).1 = sortAt f i) ↔
      (Formula.rename v hv (φ f)).Sat (Δ N hN.wf).toStr t
    refine Iff.trans ?_ (Formula.sat_rename (M := (Δ N hN.wf).toStr) v hv (φ f) t).symm
    exact ⟨fun h => h.1, fun h => ⟨h, fun i => (ht (v i)).trans (hv i)⟩⟩
  | _, _, .eq _ _ _, _, _ => Iff.rfl
  | _, _, .false_, _, _ => Iff.rfl
  | _, _, .imp ψ χ, t, ht => by
    show (_ → _) ↔ (_ → _)
    rw [Sat_elim hN ψ t ht, Sat_elim hN χ t ht]
  | _, _, .ex n ψ, t, ht => by
    show (∃ x : Sorted.El N.U, x.1 = n ∧ _) ↔ ∃ x : Sorted.El N.U, x.1 = n ∧ _
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, (Sat_elim hN ψ _ ?_).1 h⟩
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa using ht i
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, (Sat_elim hN ψ _ ?_).2 h⟩
      intro i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · simpa using hx
      · simpa using ht i

theorem append_sorts {a k : ℕ} {ps : Fin a → ℕ} {s : Fin k → ℕ} {U : ℕ → Type u}
    (p : Fin a → Sorted.El U) (t : Fin k → Sorted.El U) (hp : ∀ i, (p i).1 = ps i)
    (ht : ∀ i, (t i).1 = s i) : ∀ i, (Fin.append p t i).1 = Fin.append ps s i := by
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [Fin.append_left]; exact hp i
  · simp only [Fin.append_right]; exact ht i

/-- A class definable in a model of `T(𝔉)` is definable in its underlying
tower. -/
theorem sortedDef_elim {N : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig} {𝒟 : StrSys N}
    (hN : (ofFormulas Sym arity sortAt φ).IsGenModel ⟨N, 𝒟⟩) {k : ℕ} {s : Fin k → ℕ}
    {C : Sorted.Rel N.U k} (h : Formula.SortedDef N s C) :
    Formula.SortedDef (Δ N hN.wf).toStr s C := by
  obtain ⟨a, ps, ψ, p, hps, hψ⟩ := h
  refine ⟨a, ps, ψ.elim, p, hps, fun t ht => ?_⟩
  exact (hψ t ht).trans (Sat_elim hN ψ _ (append_sorts p t hps ht))

/-- A class definable in the underlying tower is definable in the model. -/
theorem sortedDef_inl {F : ClauseFamily.{u}} {N : Str.{u} F.sig} (hwf : IsWF N) {k : ℕ}
    {s : Fin k → ℕ} {C : Sorted.Rel N.U k} (h : Formula.SortedDef (Δ N hwf).toStr s C) :
    Formula.SortedDef N s C := by
  obtain ⟨a, ps, ψ, p, hps, hψ⟩ := h
  refine ⟨a, ps, ψ.inl, p, hps, fun t ht => ?_⟩
  exact (hψ t ht).trans (Calc.Sat_inl_Δ hwf ψ _).symm

end Elim

/-! ### Expansions with definable classes -/

section Expand

variable {Sym : Type} {arity : Sym → ℕ} {sortAt : (f : Sym) → Fin (arity f) → ℕ}
  {φ : (f : Sym) → Formula TowerSig (arity f) (sortAt f)}
  {Sym' : Type} {arity' : Sym' → ℕ} {sortAt' : (f : Sym') → Fin (arity' f) → ℕ}
  {φ' : (f : Sym') → Formula TowerSig (arity' f) (sortAt' f)}

/-- The expansion of the underlying tower of a model of `T(𝔉)` (with its
definable classes) to the signature of `T(𝔉')` is a model of `T(𝔉')` with
its definable classes. -/
theorem expand_isGenModel_defSys {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig}
    (hM : (ofFormulas Sym arity sortAt φ).IsGenModel ⟨M, M.defSys⟩) :
    (ofFormulas.{u} Sym' arity' sortAt' φ').IsGenModel
      ⟨(ofFormulas.{u} Sym' arity' sortAt' φ').expandStr (Δ M hM.wf),
        ((ofFormulas.{u} Sym' arity' sortAt' φ').expandStr (Δ M hM.wf)).defSys⟩ := by
  have hN0 := (ofFormulas.{u} Sym' arity' sortAt' φ').expand_isGenModel
    ⟨Δ M hM.wf, ΔSys ⟨M, M.defSys⟩ hM.wf⟩ hM.tower
  refine ⟨hN0.wf, ?_, hN0.clause⟩
  refine IsTowerModel.mono ?_ hN0.tower
  intro k C hC
  -- `C` is definable in the expansion; hence in its tower, which is the tower of `M`;
  -- hence in `M`.
  show ∀ s, Formula.SortedDef M s C
  intro s
  have h1 : Formula.SortedDef ((ofFormulas.{u} Sym' arity' sortAt' φ').expandStr (Δ M hM.wf)) s C :=
    hC s
  have h2 := sortedDef_elim hN0 h1
  obtain ⟨a, ps, ψ, p, hps, hψ⟩ := h2
  refine ⟨a, ps, ψ.inl, p, hps, fun t ht => ?_⟩
  refine (hψ t ht).trans ?_
  refine (Sat_Δ_toStr hN0.wf ψ _).trans ?_
  exact (Calc.Sat_inl_Δ hM.wf ψ _).symm

/-- A tower-signature sentence holds in the expansion iff it holds in the
original structure. -/
theorem holds_inl_expand {M : Str.{u} (ofFormulas.{u} Sym arity sortAt φ).sig} (hwf : IsWF M)
    (σ : Sentence TowerSig) :
    Sentence.Holds (σ.inl (F := ofFormulas.{u} Sym' arity' sortAt' φ'))
        ((ofFormulas.{u} Sym' arity' sortAt' φ').expandStr (Δ M hwf)) ↔
      Sentence.Holds (σ.inl (F := ofFormulas.{u} Sym arity sortAt φ)) M := by
  rw [Holds_inl, Holds_inl]
  show Sentence.Holds σ (Δ M hwf).toStr ↔ _
  rw [Δ_toStr_eq]

end Expand

end ClauseFamily

end SolidLean.Solid

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.ClauseFamily SolidLean.Solid.Render
open FFL FirstOrder

/-- **`T_L` is a conservative extension of `H`**: a sentence of the tower
signature is provable from `T_L` iff it is provable from `H`. -/
theorem TL_conservative (σ : Sentence TowerSig) :
    TL_FO.{v} ⊢ trS (σ.inl (F := LAnn.{v})) ↔ H_FO.{v} ⊢ trS (σ.inl (F := HFam.{v})) := by
  have e1 := provable_iff_semantic.{v} (Sym := Sym) (arity := fun s => s.1 + 1)
    (sortAt := fun s => Fin.snoc s.2.1.levels (s.2.2.cls s.2.1)) (φ := fun s => eval s.2.1 s.2.2)
    (σ.inl (F := LAnn.{v}))
  have e2 := provable_iff_semantic.{v} (Sym := Empty) (arity := fun e => e.elim)
    (sortAt := fun e => e.elim) (φ := fun e => e.elim) (σ.inl (F := HFam.{v}))
  rw [TLax_empty] at e2
  refine e1.trans (Iff.trans ?_ e2.symm)
  constructor
  · intro h M hM
    have := h _ (expand_isGenModel_defSys (Sym' := Sym) hM)
    exact (holds_inl_expand hM.wf σ).1 this
  · intro h N hN
    have := h _ (expand_isGenModel_defSys (Sym' := Empty) (arity' := fun e => e.elim)
      (sortAt' := fun e => e.elim) (φ' := fun e => e.elim) hN)
    exact (holds_inl_expand hN.wf σ).1 this

end SolidLean.Calc
