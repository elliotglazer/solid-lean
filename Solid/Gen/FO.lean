module

public import Solid.Gen.Signature

/-!
# Many-sorted first-order formulas

Formulas over a relational signature, with `k` free variables carrying sorts
`s : Fin k → ℕ` (de Bruijn style; the quantifier binds the last variable, as
`Sorted.exists_` does).  Satisfaction is defined on sorted tuples of the
union, so that the relation a formula defines is a `Sorted.Rel`.  The two
basic facts: the relation defined by a formula belongs to every class system
containing the relation atoms (`Formula.def_mem`), and it is invariant under
isomorphisms (`Formula.sat_map`).
-/

@[expose] public section

universe u

namespace SolidLean.Solid

/-- Well-sorted first-order formulas with `k` free variables of sorts `s`. -/
inductive Formula (Sig : Signature) : (k : ℕ) → (Fin k → ℕ) → Type
  | rel {k : ℕ} {s : Fin k → ℕ} (r : Sig.Rel) (v : Fin (Sig.arity r) → Fin k)
      (hv : ∀ i, s (v i) = Sig.sortAt r i) : Formula Sig k s
  | eq {k : ℕ} {s : Fin k → ℕ} (i j : Fin k) (h : s i = s j) : Formula Sig k s
  | false_ {k : ℕ} {s : Fin k → ℕ} : Formula Sig k s
  | imp {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s) : Formula Sig k s
  | ex {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (φ : Formula Sig (k + 1) (Fin.snoc s n)) : Formula Sig k s

namespace Formula

variable {Sig : Signature}

/-- Satisfaction in a structure, on tuples of the union. -/
def Sat (M : Str.{u} Sig) : {k : ℕ} → {s : Fin k → ℕ} → Formula Sig k s →
    (Fin k → Sorted.El M.U) → Prop
  | _, _, .rel r v _, t => (fun i => t (v i)) ∈ M.rel r
  | _, _, .eq i j _, t => t i = t j
  | _, _, .false_, _ => False
  | _, _, .imp φ ψ, t => Sat M φ t → Sat M ψ t
  | _, _, .ex n φ, t => ∃ x : Sorted.El M.U, x.1 = n ∧ Sat M φ (Fin.snoc t x)

/-- The relation defined by a formula. -/
def Def (M : Str.{u} Sig) {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s) : Sorted.Rel M.U k :=
  {t | φ.Sat M t}

@[simp] theorem mem_Def {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : t ∈ φ.Def M ↔ φ.Sat M t := Iff.rfl

@[simp] theorem Sat_rel {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (r : Sig.Rel)
    (v : Fin (Sig.arity r) → Fin k) (hv) (t : Fin k → Sorted.El M.U) :
    (rel (s := s) r v hv).Sat M t ↔ (fun i => t (v i)) ∈ M.rel r := Iff.rfl

@[simp] theorem Sat_eq {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (i j : Fin k) (h : s i = s j)
    (t : Fin k → Sorted.El M.U) : (eq i j h).Sat M t ↔ t i = t j := Iff.rfl

@[simp] theorem Sat_false {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (t : Fin k → Sorted.El M.U) :
    (false_ (s := s)).Sat M t ↔ False := Iff.rfl

@[simp] theorem Sat_imp {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : (imp φ ψ).Sat M t ↔ (φ.Sat M t → ψ.Sat M t) := Iff.rfl

@[simp] theorem Sat_ex {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (n : ℕ)
    (φ : Formula Sig (k + 1) (Fin.snoc s n)) (t : Fin k → Sorted.El M.U) :
    (ex n φ).Sat M t ↔ ∃ x : Sorted.El M.U, x.1 = n ∧ φ.Sat M (Fin.snoc t x) := Iff.rfl

/-- Satisfaction transports along a heterogeneous equality of formulas whose
sort assignments agree. -/
theorem Sat_heq {M : Str.{u} Sig} {k : ℕ} {s s' : Fin k → ℕ} (hs : s = s') {φ : Formula Sig k s}
    {φ' : Formula Sig k s'} (h : HEq φ φ') (t : Fin k → Sorted.El M.U) : φ.Sat M t ↔ φ'.Sat M t := by
  subst hs
  rw [eq_of_heq h]

/-! ### Definability -/

/-- The relation defined by a formula belongs to every class system that
contains the relation atoms. -/
theorem def_mem {M : Str.{u} Sig} (𝒟 : StrSys M) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s), φ.Def M ∈ 𝒟.D k
  | _, _, .rel r v _ => 𝒟.reindex_mem v (𝒟.rel_mem r)
  | _, _, .eq i j h => by
    have : Def M (.eq i j h) = Sorted.reindex M.U ![i, j] (Sorted.eqRel M.U) := by
      ext t; exact Iff.rfl
    rw [this]; exact 𝒟.reindex_mem _ 𝒟.eq_mem
  | _, _, .false_ => 𝒟.empty_mem _
  | _, _, .imp φ ψ => by
    have : Def M (.imp φ ψ) = (φ.Def M)ᶜ ∪ ψ.Def M := by
      ext t
      show (φ.Sat M t → ψ.Sat M t) ↔ ¬ φ.Sat M t ∨ ψ.Sat M t
      exact imp_iff_not_or
    rw [this]; exact 𝒟.union_mem (𝒟.compl_mem (def_mem 𝒟 φ)) (def_mem 𝒟 ψ)
  | _, _, .ex n φ => 𝒟.exists_mem n (def_mem 𝒟 φ)

/-! ### Invariance under isomorphisms -/

theorem snoc_map {M N : Str.{u} Sig} (e : GenIso M N) {k : ℕ} (t : Fin k → Sorted.El M.U)
    (x : Sorted.El M.U) :
    (fun i => e.mapEl (Fin.snoc (α := fun _ => Sorted.El M.U) t x i)) =
      Fin.snoc (α := fun _ => Sorted.El N.U) (fun i => e.mapEl (t i)) (e.mapEl x) := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp only [Fin.snoc_last]
  · simp only [Fin.snoc_castSucc]

/-- Satisfaction is invariant under isomorphisms. -/
theorem sat_map {M N : Str.{u} Sig} (e : GenIso M N) :
    ∀ {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s) (t : Fin k → Sorted.El M.U),
      φ.Sat M t ↔ φ.Sat N (fun i => e.mapEl (t i))
  | _, _, .rel r v _, t => e.rel_iff r _
  | _, _, .eq i j _, t => by
    show t i = t j ↔ e.mapEl (t i) = e.mapEl (t j)
    exact ⟨fun h => by rw [h], fun h => e.mapEl_injective h⟩
  | _, _, .false_, _ => Iff.rfl
  | _, _, .imp φ ψ, t => by
    show (φ.Sat M t → ψ.Sat M t) ↔ (φ.Sat N _ → ψ.Sat N _)
    rw [sat_map e φ t, sat_map e ψ t]
  | _, _, .ex n φ, t => by
    show (∃ x : Sorted.El M.U, x.1 = n ∧ φ.Sat M (Fin.snoc t x)) ↔
      ∃ y : Sorted.El N.U, y.1 = n ∧ φ.Sat N (Fin.snoc (fun i => e.mapEl (t i)) y)
    constructor
    · rintro ⟨x, hx, hφ⟩
      refine ⟨e.mapEl x, hx, ?_⟩
      rw [← snoc_map, ← sat_map e]; exact hφ
    · rintro ⟨y, hy, hφ⟩
      obtain ⟨x, rfl⟩ := e.mapEl_surjective y
      refine ⟨x, hy, ?_⟩
      rw [sat_map e, snoc_map]; exact hφ

/-! ### Variable renaming -/

/-- The renaming of the bound variable under a quantifier. -/
def liftRen {k k' : ℕ} (f : Fin k → Fin k') : Fin (k + 1) → Fin (k' + 1) :=
  Fin.snoc (fun i => Fin.castSucc (f i)) (Fin.last k')

theorem liftRen_sorts {k k' : ℕ} {s : Fin k → ℕ} {s' : Fin k' → ℕ} (f : Fin k → Fin k')
    (hf : ∀ i, s' (f i) = s i) (n : ℕ) :
    ∀ i, Fin.snoc (α := fun _ => ℕ) s' n (liftRen f i) = Fin.snoc (α := fun _ => ℕ) s n i := by
  intro i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [liftRen]
  · simp [liftRen, hf]

/-- Renaming of variables along a sort-preserving map. -/
def rename : {k : ℕ} → {s : Fin k → ℕ} → {k' : ℕ} → {s' : Fin k' → ℕ} →
    (f : Fin k → Fin k') → (∀ i, s' (f i) = s i) → Formula Sig k s → Formula Sig k' s'
  | _, _, _, _, f, hf, .rel r v hv => .rel r (fun i => f (v i)) (fun i => (hf _).trans (hv i))
  | _, _, _, _, f, hf, .eq i j h => .eq (f i) (f j) ((hf i).trans (h.trans (hf j).symm))
  | _, _, _, _, _, _, .false_ => .false_
  | _, _, _, _, f, hf, .imp φ ψ => .imp (rename f hf φ) (rename f hf ψ)
  | _, _, _, _, f, hf, .ex n φ => .ex n (rename (liftRen f) (liftRen_sorts f hf n) φ)

theorem snoc_comp_liftRen {M : Str.{u} Sig} {k k' : ℕ} (f : Fin k → Fin k')
    (t : Fin k' → Sorted.El M.U) (x : Sorted.El M.U) :
    (fun i => Fin.snoc (α := fun _ => Sorted.El M.U) t x (liftRen f i)) =
      Fin.snoc (α := fun _ => Sorted.El M.U) (fun i => t (f i)) x := by
  funext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [liftRen]
  · simp [liftRen]

theorem sat_rename {M : Str.{u} Sig} :
    ∀ {k : ℕ} {s : Fin k → ℕ} {k' : ℕ} {s' : Fin k' → ℕ} (f : Fin k → Fin k')
      (hf : ∀ i, s' (f i) = s i) (φ : Formula Sig k s) (t : Fin k' → Sorted.El M.U),
      (rename f hf φ).Sat M t ↔ φ.Sat M (fun i => t (f i))
  | _, _, _, _, _, _, .rel _ _ _, _ => Iff.rfl
  | _, _, _, _, _, _, .eq _ _ _, _ => Iff.rfl
  | _, _, _, _, _, _, .false_, _ => Iff.rfl
  | _, _, _, _, f, hf, .imp φ ψ, t => by
    show ((rename f hf φ).Sat M t → (rename f hf ψ).Sat M t) ↔ _
    rw [sat_rename f hf φ, sat_rename f hf ψ]
    exact Iff.rfl
  | _, _, _, _, f, hf, .ex n φ, t => by
    show (∃ x : Sorted.El M.U, x.1 = n ∧ (rename (liftRen f) _ φ).Sat M (Fin.snoc t x)) ↔
      ∃ x : Sorted.El M.U, x.1 = n ∧ φ.Sat M (Fin.snoc (fun i => t (f i)) x)
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, ?_⟩
      rw [sat_rename, snoc_comp_liftRen] at h
      exact h
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, ?_⟩
      rw [sat_rename, snoc_comp_liftRen]
      exact h

/-! ### Derived connectives -/

/-- Negation. -/
def not {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s) : Formula Sig k s := .imp φ .false_

/-- Conjunction. -/
def and {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s) : Formula Sig k s :=
  not (.imp φ (not ψ))

/-- Disjunction. -/
def or {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s) : Formula Sig k s := .imp (not φ) ψ

/-- Biconditional. -/
def iff {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s) : Formula Sig k s :=
  and (.imp φ ψ) (.imp ψ φ)

/-- Universal quantification over a sort. -/
def all {k : ℕ} {s : Fin k → ℕ} (n : ℕ) (φ : Formula Sig (k + 1) (Fin.snoc s n)) :
    Formula Sig k s := not (.ex n (not φ))

/-- Truth. -/
def true_ {k : ℕ} {s : Fin k → ℕ} : Formula Sig k s := not .false_

@[simp] theorem Sat_not {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : (not φ).Sat M t ↔ ¬ φ.Sat M t := Iff.rfl

@[simp] theorem Sat_and {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : (and φ ψ).Sat M t ↔ φ.Sat M t ∧ ψ.Sat M t := by
  show ¬ (φ.Sat M t → ¬ ψ.Sat M t) ↔ _
  constructor
  · intro h
    by_contra h'
    exact h (fun hφ hψ => h' ⟨hφ, hψ⟩)
  · rintro ⟨hφ, hψ⟩ h
    exact h hφ hψ

@[simp] theorem Sat_or {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : (or φ ψ).Sat M t ↔ φ.Sat M t ∨ ψ.Sat M t := by
  show (¬ φ.Sat M t → ψ.Sat M t) ↔ _
  constructor
  · intro h
    by_cases hφ : φ.Sat M t
    · exact Or.inl hφ
    · exact Or.inr (h hφ)
  · rintro (h | h) hn
    · exact absurd h hn
    · exact h

@[simp] theorem Sat_iff {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (φ ψ : Formula Sig k s)
    (t : Fin k → Sorted.El M.U) : (iff φ ψ).Sat M t ↔ (φ.Sat M t ↔ ψ.Sat M t) := by
  rw [iff, Sat_and]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

@[simp] theorem Sat_all {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (n : ℕ)
    (φ : Formula Sig (k + 1) (Fin.snoc s n)) (t : Fin k → Sorted.El M.U) :
    (all n φ).Sat M t ↔ ∀ x : Sorted.El M.U, x.1 = n → φ.Sat M (Fin.snoc t x) := by
  show ¬ (∃ x : Sorted.El M.U, x.1 = n ∧ ¬ φ.Sat M (Fin.snoc t x)) ↔ _
  constructor
  · intro h x hx
    by_contra h'
    exact h ⟨x, hx, h'⟩
  · rintro h ⟨x, hx, h'⟩
    exact h' (h x hx)

@[simp] theorem Sat_true {M : Str.{u} Sig} {k : ℕ} {s : Fin k → ℕ} (t : Fin k → Sorted.El M.U) :
    (true_ (Sig := Sig) (s := s)).Sat M t ↔ True := by
  show ¬ False ↔ True
  simp

end Formula

end SolidLean.Solid
