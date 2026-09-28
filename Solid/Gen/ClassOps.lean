import Solid.Gen.Definable

/-!
# Derived operations of class systems

Quantifying away a block of trailing coordinates of fixed sorts
(`existsTail`), images of a class under a coordinatewise admissible relation
(`imageRel_mem`), and relational composition of binary classes
(`comp2_mem`).  These are the closure properties used to move classes along
codings of sorts.
-/

universe u

namespace SolidLean.Solid

open Classical

namespace Sorted

variable (U : ℕ → Type u)

/-- The class `{t | ∃ u of sorts b, append t u ∈ Q}`. -/
def existsTail : ∀ {m k : ℕ} (b : Fin k → ℕ) (Q : Rel U (m + k)), Rel U m
  | _, 0, _, Q => {t | Fin.append t (Fin.elim0 : Fin 0 → El U) ∈ Q}
  | m, k + 1, b, Q => existsTail (Fin.init b) (exists_ U (b (Fin.last k)) Q)

theorem append_elim0 {α : Type*} {m : ℕ} (t : Fin m → α) :
    Fin.append t (Fin.elim0 : Fin 0 → α) = t := by
  funext i
  exact Fin.append_left t Fin.elim0 ⟨i.1, by omega⟩

theorem mem_existsTail_iff : ∀ {m k : ℕ} (b : Fin k → ℕ) (Q : Rel U (m + k)) (t : Fin m → El U),
    t ∈ existsTail U b Q ↔ ∃ u : Fin k → El U, (∀ i, (u i).1 = b i) ∧ Fin.append t u ∈ Q
  | m, 0, b, Q, t => by
    show Fin.append t (Fin.elim0 : Fin 0 → El U) ∈ Q ↔ _
    constructor
    · intro h
      exact ⟨Fin.elim0, fun i => i.elim0, h⟩
    · rintro ⟨u, -, h⟩
      have : u = Fin.elim0 := funext fun i => i.elim0
      rw [this] at h; exact h
  | m, k + 1, b, Q, t => by
    show t ∈ existsTail U (Fin.init b) (exists_ U (b (Fin.last k)) Q) ↔ _
    rw [mem_existsTail_iff]
    constructor
    · rintro ⟨u, hu, x, hx, h⟩
      refine ⟨Fin.snoc u x, fun i => ?_, ?_⟩
      · refine Fin.lastCases ?_ (fun i => ?_) i
        · simpa using hx
        · simp only [Fin.snoc_castSucc]; exact hu i
      · rw [Formula.append_snoc]; exact h
    · rintro ⟨u, hu, h⟩
      refine ⟨Fin.init u, fun i => hu (Fin.castSucc i), u (Fin.last k), hu (Fin.last k), ?_⟩
      rw [← Formula.append_snoc, Fin.snoc_init_self]; exact h

end Sorted

namespace ClassSys

variable {U : ℕ → Type u} (𝒟 : ClassSys U)

theorem existsTail_mem : ∀ {m k : ℕ} (b : Fin k → ℕ) {Q : Sorted.Rel U (m + k)}, Q ∈ 𝒟.D (m + k) →
    Sorted.existsTail U b Q ∈ 𝒟.D m
  | m, 0, b, Q, hQ => by
    show {t | Fin.append t (Fin.elim0 : Fin 0 → Sorted.El U) ∈ Q} ∈ 𝒟.D m
    have : {t | Fin.append t (Fin.elim0 : Fin 0 → Sorted.El U) ∈ Q} = Q := by
      ext t
      show Fin.append t Fin.elim0 ∈ Q ↔ t ∈ Q
      rw [Sorted.append_elim0]
    rw [this]; exact hQ
  | m, k + 1, b, Q, hQ =>
    existsTail_mem (Fin.init b) (𝒟.exists_mem (b (Fin.last k)) hQ)

/-- The image of a class under coordinatewise admissible binary relations
(`R i` relates the `i`-th coordinate of the source to that of the image),
for tuples of a fixed profile. -/
def imageRel {k : ℕ} (A : Sorted.Rel U k) (R : Fin k → Sorted.Rel U 2) : Sorted.Rel U k :=
  {t | ∃ u ∈ A, ∀ i, ![u i, t i] ∈ R i}

theorem append_natAdd_apply {α : Type*} {k : ℕ} (t u : Fin k → α) (i : Fin k) :
    Fin.append t u (Fin.natAdd k i) = u i := Fin.append_right t u i

theorem append_castAdd_apply {α : Type*} {k : ℕ} (t u : Fin k → α) (i : Fin k) :
    Fin.append t u (Fin.castAdd k i) = t i := Fin.append_left t u i

theorem imageRel_mem {k : ℕ} (b : Fin k → ℕ) {A : Sorted.Rel U k} (hA : A ∈ 𝒟.D k)
    (hb : ∀ t ∈ A, ∀ i, (t i).1 = b i) {R : Fin k → Sorted.Rel U 2} (hR : ∀ i, R i ∈ 𝒟.D 2) :
    imageRel A R ∈ 𝒟.D k := by
  -- the class of pairs `(t, u)` with `u ∈ A` and `R i (u i) (t i)`, then quantify `u` away
  let Q : Sorted.Rel U (k + k) :=
    Sorted.reindex U (Fin.natAdd k) A ∩
      ⋂ i : Fin k, Sorted.reindex U (![Fin.natAdd k i, Fin.castAdd k i]) (R i)
  have hQ : Q ∈ 𝒟.D (k + k) :=
    𝒟.inter_mem (𝒟.reindex_mem _ hA) (𝒟.iInter_mem _ fun i => 𝒟.reindex_mem _ (hR i))
  have : imageRel A R = Sorted.existsTail U b Q := by
    ext t
    rw [Sorted.mem_existsTail_iff]
    constructor
    · rintro ⟨u, hu, hRu⟩
      refine ⟨u, hb u hu, ?_, ?_⟩
      · show (Fin.append t u ∘ Fin.natAdd k) ∈ A
        have : Fin.append t u ∘ Fin.natAdd k = u := funext fun i => append_natAdd_apply t u i
        rw [this]; exact hu
      · simp only [Set.mem_iInter]
        intro i
        show (Fin.append t u ∘ ![Fin.natAdd k i, Fin.castAdd k i]) ∈ R i
        have : Fin.append t u ∘ ![Fin.natAdd k i, Fin.castAdd k i] = ![u i, t i] := by
          funext j
          match j with
          | 0 => exact append_natAdd_apply t u i
          | 1 => exact append_castAdd_apply t u i
        rw [this]; exact hRu i
    · rintro ⟨u, -, hu, hRu⟩
      refine ⟨u, ?_, fun i => ?_⟩
      · have : Fin.append t u ∘ Fin.natAdd k = u := funext fun i => append_natAdd_apply t u i
        rw [← this]; exact hu
      · simp only [Set.mem_iInter] at hRu
        have h : (Fin.append t u ∘ ![Fin.natAdd k i, Fin.castAdd k i]) ∈ R i := hRu i
        have : Fin.append t u ∘ ![Fin.natAdd k i, Fin.castAdd k i] = ![u i, t i] := by
          funext j
          match j with
          | 0 => exact append_natAdd_apply t u i
          | 1 => exact append_castAdd_apply t u i
        rw [this] at h; exact h
  rw [this]
  exact 𝒟.existsTail_mem b hQ

/-- Relational composition of binary classes, through a middle coordinate of
sort `n`. -/
theorem comp2_mem (n : ℕ) {R S : Sorted.Rel U 2} (hR : R ∈ 𝒟.D 2) (hS : S ∈ 𝒟.D 2) :
    ({t | ∃ y : Sorted.El U, y.1 = n ∧ ![t 0, y] ∈ R ∧ ![y, t 1] ∈ S} : Sorted.Rel U 2) ∈ 𝒟.D 2 := by
  have h := 𝒟.exists_mem n (𝒟.inter_mem (𝒟.reindex_mem (![0, 2] : Fin 2 → Fin 3) hR)
    (𝒟.reindex_mem (![2, 1] : Fin 2 → Fin 3) hS))
  convert h using 1
  ext t
  show (∃ y : Sorted.El U, y.1 = n ∧ ![t 0, y] ∈ R ∧ ![y, t 1] ∈ S) ↔
    ∃ y : Sorted.El U, y.1 = n ∧ (Fin.snoc t y ∘ ![0, 2]) ∈ R ∧ (Fin.snoc t y ∘ ![2, 1]) ∈ S
  have e1 : ∀ y, (Fin.snoc (α := fun _ => Sorted.El U) t y ∘ ![0, 2]) = ![t 0, y] := by
    intro y; funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  have e2 : ∀ y, (Fin.snoc (α := fun _ => Sorted.El U) t y ∘ ![2, 1]) = ![y, t 1] := by
    intro y; funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  simp only [e1, e2]

/-- The converse of a binary class. -/
theorem converse_mem {R : Sorted.Rel U 2} (hR : R ∈ 𝒟.D 2) :
    ({t | ![t 1, t 0] ∈ R} : Sorted.Rel U 2) ∈ 𝒟.D 2 := by
  have := 𝒟.reindex_mem (![1, 0] : Fin 2 → Fin 2) hR
  convert this using 1
  ext t
  show ![t 1, t 0] ∈ R ↔ (t ∘ ![1, 0]) ∈ R
  have : t ∘ ![1, 0] = ![t 1, t 0] := by
    funext j
    match j with
    | 0 => rfl
    | 1 => rfl
  rw [this]

end ClassSys

end SolidLean.Solid
