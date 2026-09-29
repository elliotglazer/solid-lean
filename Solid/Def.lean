module

public import Solid.Internal

/-!
# A definability calculus for class systems

`𝒞.Def k P` says that the `k`-ary predicate `P` (on tuples of elements) is a
class of the system `𝒞`.  The combinators below mirror the closure
properties of `SetClassSystem` and let every set-theoretic notion of
`Solid.SetTheory` be certified definable once and for all, at arbitrary
variable positions.  New variables introduced by a quantifier occupy the
*last* position (`Fin.last`), old variables are shifted by `Fin.castSucc`;
the `Fin.snoc` simp lemmas discharge the bookkeeping.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

namespace SetClassSystem

variable {S : MemStr.{u}} (𝒞 : SetClassSystem S)

/-- `P` is a definable `k`-ary predicate. -/
def Def (k : ℕ) (P : (Fin k → S.X) → Prop) : Prop := ({t | P t} : S.Rel k) ∈ 𝒞.D k

namespace Def

variable {𝒞}

theorem congr {k : ℕ} {P Q : (Fin k → S.X) → Prop} (h : ∀ t, P t ↔ Q t)
    (hP : 𝒞.Def k P) : 𝒞.Def k Q := by
  have : ({t | Q t} : S.Rel k) = {t | P t} := by ext t; exact (h t).symm
  unfold Def; rw [this]; exact hP

theorem true_ (k : ℕ) : 𝒞.Def k (fun _ => True) := 𝒞.univ_mem k

theorem false_ (k : ℕ) : 𝒞.Def k (fun _ => False) := 𝒞.empty_mem k

theorem and_ {k : ℕ} {P Q : (Fin k → S.X) → Prop} (hP : 𝒞.Def k P) (hQ : 𝒞.Def k Q) :
    𝒞.Def k (fun t => P t ∧ Q t) := 𝒞.inter_mem hP hQ

theorem not_ {k : ℕ} {P : (Fin k → S.X) → Prop} (hP : 𝒞.Def k P) :
    𝒞.Def k (fun t => ¬ P t) := 𝒞.compl_mem hP

theorem or_ {k : ℕ} {P Q : (Fin k → S.X) → Prop} (hP : 𝒞.Def k P) (hQ : 𝒞.Def k Q) :
    𝒞.Def k (fun t => P t ∨ Q t) :=
  congr (fun _ => by rw [not_and_or, not_not, not_not]) (not_ (and_ (not_ hP) (not_ hQ)))

theorem imp_ {k : ℕ} {P Q : (Fin k → S.X) → Prop} (hP : 𝒞.Def k P) (hQ : 𝒞.Def k Q) :
    𝒞.Def k (fun t => P t → Q t) :=
  congr (fun _ => (imp_iff_not_or).symm) (or_ (not_ hP) hQ)

theorem iff_ {k : ℕ} {P Q : (Fin k → S.X) → Prop} (hP : 𝒞.Def k P) (hQ : 𝒞.Def k Q) :
    𝒞.Def k (fun t => P t ↔ Q t) :=
  congr (fun _ => iff_iff_implies_and_implies.symm) (and_ (imp_ hP hQ) (imp_ hQ hP))

theorem exists_ {k : ℕ} {P : (Fin (k + 1) → S.X) → Prop} (hP : 𝒞.Def (k + 1) P) :
    𝒞.Def k (fun t => ∃ x, P (Fin.snoc t x)) := 𝒞.exists_mem hP

theorem forall_ {k : ℕ} {P : (Fin (k + 1) → S.X) → Prop} (hP : 𝒞.Def (k + 1) P) :
    𝒞.Def k (fun t => ∀ x, P (Fin.snoc t x)) :=
  congr (fun _ => not_exists_not) (not_ (exists_ (not_ hP)))

theorem reindex {m k : ℕ} (f : Fin m → Fin k) {P : (Fin m → S.X) → Prop} (hP : 𝒞.Def m P) :
    𝒞.Def k (fun t => P (t ∘ f)) := 𝒞.reindex_mem f hP

theorem eq {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => t i = t j) :=
  reindex ![i, j] 𝒞.eq_mem

theorem mem {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.mem (t i) (t j)) :=
  reindex ![i, j] 𝒞.memRel_mem

theorem param {k : ℕ} (i : Fin k) (p : S.X) : 𝒞.Def k (fun t => t i = p) :=
  reindex (fun _ => i) (𝒞.param_mem p)

/-- Instantiating the last variable with a parameter. -/
theorem withParam {k : ℕ} (p : S.X) {P : (Fin (k + 1) → S.X) → Prop} (hP : 𝒞.Def (k + 1) P) :
    𝒞.Def k (fun t => P (Fin.snoc t p)) := by
  refine congr ?_ (exists_ (and_ (param (Fin.last k) p) hP))
  intro t
  simp only [Fin.snoc_last]
  constructor
  · rintro ⟨x, rfl, h⟩; exact h
  · intro h; exact ⟨p, rfl, h⟩

/-! ### Certificates for the notions of `Solid.SetTheory` -/

section Notions

open Fin (castSucc last)

theorem subset {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.Subset (t i) (t j)) := by
  refine congr ?_ (forall_ (imp_ (mem (last k) (castSucc i)) (mem (last k) (castSucc j))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isEmptySet {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsEmptySet (t i)) := by
  refine congr ?_ (forall_ (not_ (mem (last k) (castSucc i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem nonempty {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.Nonempty (t i)) := by
  refine congr ?_ (exists_ (mem (last k) (castSucc i)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isPairSet {k : ℕ} (i j l : Fin k) :
    𝒞.Def k (fun t => S.IsPairSet (t i) (t j) (t l)) := by
  refine congr ?_ (forall_ (iff_ (mem (last k) (castSucc l))
    (or_ (eq (last k) (castSucc i)) (eq (last k) (castSucc j)))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isSingleton {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.IsSingleton (t i) (t j)) := by
  refine congr ?_ (forall_ (iff_ (mem (last k) (castSucc j)) (eq (last k) (castSucc i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isOrdPair {k : ℕ} (i j l : Fin k) :
    𝒞.Def k (fun t => S.IsOrdPair (t i) (t j) (t l)) := by
  refine congr ?_ (exists_ (exists_ (and_
    (isSingleton (castSucc (castSucc i)) (castSucc (last k)))
    (and_ (isPairSet (castSucc (castSucc i)) (castSucc (castSucc j)) (last (k + 1)))
      (isPairSet (castSucc (last k)) (last (k + 1)) (castSucc (castSucc l)))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isUnionSet {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.IsUnionSet (t i) (t j)) := by
  refine congr ?_ (forall_ (iff_ (mem (last k) (castSucc j))
    (exists_ (and_ (mem (last (k + 1)) (castSucc (castSucc i)))
      (mem (castSucc (last k)) (last (k + 1)))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isPowerSet {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.IsPowerSet (t i) (t j)) := by
  refine congr ?_ (forall_ (iff_ (mem (last k) (castSucc j)) (subset (last k) (castSucc i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isSucc {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.IsSucc (t i) (t j)) := by
  refine congr ?_ (forall_ (iff_ (mem (last k) (castSucc j))
    (or_ (mem (last k) (castSucc i)) (eq (last k) (castSucc i)))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem transitive {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.Transitive (t i)) := by
  refine congr ?_ (forall_ (imp_ (mem (last k) (castSucc i)) (subset (last k) (castSucc i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isRelation {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsRelation (t i)) := by
  refine congr ?_ (forall_ (imp_ (mem (last k) (castSucc i))
    (exists_ (exists_ (isOrdPair (castSucc (last (k + 1))) (last (k + 2))
      (castSucc (castSucc (last k))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem funApp {k : ℕ} (i j l : Fin k) : 𝒞.Def k (fun t => S.FunApp (t i) (t j) (t l)) := by
  refine congr ?_ (exists_ (and_ (mem (last k) (castSucc i))
    (isOrdPair (castSucc j) (castSucc l) (last k))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem inDom {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.InDom (t i) (t j)) := by
  refine congr ?_ (exists_ (funApp (castSucc i) (castSucc j) (last k)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isFunction {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsFunction (t i)) := by
  refine congr ?_ (and_ (isRelation i) (forall_ (forall_ (forall_ (imp_
    (funApp (castSucc (castSucc (castSucc i))) (castSucc (castSucc (last k)))
      (castSucc (last (k + 1))))
    (imp_ (funApp (castSucc (castSucc (castSucc i))) (castSucc (castSucc (last k)))
        (last (k + 2)))
      (eq (castSucc (last (k + 1))) (last (k + 2)))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isFunctionOn {k : ℕ} (i j : Fin k) :
    𝒞.Def k (fun t => S.IsFunctionOn (t i) (t j)) := by
  refine congr ?_ (and_ (isFunction i)
    (forall_ (iff_ (inDom (castSucc i) (last k)) (mem (last k) (castSucc j)))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem injective {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.Injective (t i)) := by
  refine congr ?_ (forall_ (forall_ (forall_ (imp_
    (funApp (castSucc (castSucc (castSucc i))) (castSucc (castSucc (last k))) (last (k + 2)))
    (imp_ (funApp (castSucc (castSucc (castSucc i))) (castSucc (last (k + 1))) (last (k + 2)))
      (eq (castSucc (castSucc (last k))) (castSucc (last (k + 1)))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem mapsInto {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.MapsInto (t i) (t j)) := by
  refine congr ?_ (forall_ (forall_ (imp_
    (funApp (castSucc (castSucc i)) (castSucc (last k)) (last (k + 1)))
    (mem (last (k + 1)) (castSucc (castSucc j))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isInjectionInto {k : ℕ} (i j l : Fin k) :
    𝒞.Def k (fun t => S.IsInjectionInto (t i) (t j) (t l)) :=
  and_ (isFunctionOn i j) (and_ (injective i) (mapsInto i l))

theorem isBijectionOnto {k : ℕ} (i j l : Fin k) :
    𝒞.Def k (fun t => S.IsBijectionOnto (t i) (t j) (t l)) := by
  refine congr ?_ (and_ (isInjectionInto i j l) (forall_ (imp_ (mem (last k) (castSucc l))
    (exists_ (funApp (castSucc (castSucc i)) (last (k + 1)) (castSucc (last k)))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isOrdinal {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsOrdinal (t i)) := by
  refine congr ?_ (and_ (transitive i) (and_
    (forall_ (imp_ (mem (last k) (castSucc i)) (transitive (last k))))
    (forall_ (forall_ (imp_ (mem (castSucc (last k)) (castSucc (castSucc i)))
      (imp_ (mem (last (k + 1)) (castSucc (castSucc i)))
        (or_ (mem (castSucc (last k)) (last (k + 1)))
          (or_ (eq (castSucc (last k)) (last (k + 1)))
            (mem (last (k + 1)) (castSucc (last k)))))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isLimitOrd {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsLimitOrd (t i)) := by
  refine congr ?_ (and_ (isOrdinal i) (and_ (nonempty i)
    (forall_ (imp_ (mem (last k) (castSucc i))
      (exists_ (and_ (isSucc (castSucc (last k)) (last (k + 1)))
        (mem (last (k + 1)) (castSucc (castSucc i)))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isSuccOrd {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsSuccOrd (t i)) := by
  refine congr ?_ (and_ (isOrdinal i) (exists_ (isSucc (last k) (castSucc i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isVAttempt {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsVAttempt (t i)) := by
  have hsucc := forall_ (imp_ (isSucc (last (k + 2)) (castSucc (castSucc (last k))))
    (exists_ (and_
      (funApp (castSucc (castSucc (castSucc (castSucc i)))) (castSucc (last (k + 2)))
        (last (k + 3)))
      (isPowerSet (last (k + 3)) (castSucc (castSucc (last (k + 1)))))))) (𝒞 := 𝒞)
  have hlim := imp_ (isLimitOrd (castSucc (last k)))
    (forall_ (iff_ (mem (last (k + 2)) (castSucc (last (k + 1))))
      (exists_ (exists_ (and_
        (mem (castSucc (last (k + 3))) (castSucc (castSucc (castSucc (castSucc (last k))))))
        (and_ (funApp (castSucc (castSucc (castSucc (castSucc (castSucc i)))))
            (castSucc (last (k + 3))) (last (k + 4)))
          (mem (castSucc (castSucc (last (k + 2)))) (last (k + 4))))))))) (𝒞 := 𝒞)
  have hbody := imp_ (funApp (castSucc (castSucc i)) (castSucc (last k)) (last (k + 1)))
    (and_ (isOrdinal (castSucc (last k)))
      (and_ (imp_ (isEmptySet (castSucc (last k))) (isEmptySet (last (k + 1))))
        (and_ hsucc hlim)))
  refine congr ?_ (and_ (isFunction i) (forall_ (forall_ hbody)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isV {k : ℕ} (i j : Fin k) : 𝒞.Def k (fun t => S.IsV (t i) (t j)) := by
  refine congr ?_ (and_ (isOrdinal i) (exists_ (and_ (isVAttempt (last k))
    (and_ (forall_ (imp_
        (or_ (mem (last (k + 1)) (castSucc (castSucc i)))
          (eq (last (k + 1)) (castSucc (castSucc i))))
        (inDom (castSucc (last k)) (last (k + 1)))))
      (funApp (last k) (castSucc i) (castSucc j))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isRankSegment {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsRankSegment (t i)) := by
  refine congr ?_ (exists_ (isV (last k) (castSucc i)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isCardinal {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsCardinal (t i)) := by
  refine congr ?_ (and_ (isOrdinal i) (forall_ (imp_ (mem (last k) (castSucc i))
    (not_ (exists_ (isBijectionOnto (last (k + 1)) (castSucc (last k))
      (castSucc (castSucc i))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isRegular {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsRegular (t i)) := by
  have hbdd := forall_ (forall_ (imp_
    (funApp (castSucc (castSucc (castSucc (last (k + 1))))) (castSucc (last (k + 3)))
      (last (k + 4)))
    (mem (last (k + 4)) (castSucc (castSucc (last (k + 2))))))) (𝒞 := 𝒞)
  have hbody := imp_ (mem (castSucc (last k)) (castSucc (castSucc i)))
    (imp_ (isFunctionOn (last (k + 1)) (castSucc (last k)))
      (imp_ (mapsInto (last (k + 1)) (castSucc (castSucc i)))
        (exists_ (and_ (mem (last (k + 2)) (castSucc (castSucc (castSucc i)))) hbdd))))
  refine congr ?_ (and_ (isOrdinal i) (forall_ (forall_ hbody)))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem isStrongLimit {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsStrongLimit (t i)) := by
  refine congr ?_ (and_ (isOrdinal i) (forall_ (imp_ (mem (last k) (castSucc i))
    (forall_ (imp_ (isPowerSet (castSucc (last k)) (last (k + 1)))
      (exists_ (exists_ (and_
        (mem (castSucc (last (k + 2))) (castSucc (castSucc (castSucc (castSucc i)))))
        (isInjectionInto (last (k + 3)) (castSucc (castSucc (last (k + 1))))
          (castSucc (last (k + 2))))))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem inaccessible {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.Inaccessible (t i)) := by
  refine congr ?_ (and_ (isCardinal i) (and_
    (exists_ (and_ (mem (last k) (castSucc i)) (isLimitOrd (last k))))
    (and_ (isRegular i) (isStrongLimit i))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem nextInaccessible {k : ℕ} (i j : Fin k) :
    𝒞.Def k (fun t => S.NextInaccessible (t i) (t j)) := by
  refine congr ?_ (and_ (inaccessible j) (and_ (mem i j)
    (forall_ (imp_ (mem (castSucc i) (last k))
      (imp_ (mem (last k) (castSucc j)) (not_ (inaccessible (last k))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

theorem noGreatestInaccessibleBelow {k : ℕ} (i : Fin k) :
    𝒞.Def k (fun t => S.NoGreatestInaccessibleBelow (t i)) := by
  refine congr ?_ (forall_ (imp_ (mem (last k) (castSucc i))
    (imp_ (inaccessible (last k))
      (exists_ (and_ (mem (last (k + 1)) (castSucc (castSucc i)))
        (and_ (mem (castSucc (last k)) (last (k + 1))) (inaccessible (last (k + 1)))))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]; exact Iff.rfl

end Notions

end Def

end SetClassSystem

namespace ZFCModel

variable (Z : ZFCModel.{u})

local notation:50 x " ∈' " y => Z.S.mem x y

/-- Separation for a definable unary predicate. -/
theorem sepP {P : Z.S.X → Prop} (hP : Z.𝒞.Def 1 (fun t => P (t 0))) (x : Z.S.X) :
    ∃ s, ∀ y, (y ∈' s) ↔ (y ∈' x) ∧ P y := by
  obtain ⟨s, hs⟩ := Z.sep hP x
  exact ⟨s, fun y => by rw [hs y]; exact Iff.rfl⟩

/-- Replacement for a definable binary predicate, functional on the members
of `x`. -/
theorem replP {R : Z.S.X → Z.S.X → Prop} (hR : Z.𝒞.Def 2 (fun t => R (t 0) (t 1)))
    (x : Z.S.X) (hfun : ∀ y, (y ∈' x) → ∃! z, R y z) :
    ∃ s, ∀ z, (z ∈' s) ↔ ∃ y, (y ∈' x) ∧ R y z := by
  have key : ∀ y z : Z.S.X,
      (Fin.snoc (Fin.snoc (fun i : Fin 0 => i.elim0) y) z : Fin 2 → Z.S.X) = ![y, z] := by
    intro y z; funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
  have := Z.ax.replacement (k := 0) {t | R (t 0) (t 1)} hR (fun i => i.elim0) x (by
    intro y hy
    obtain ⟨z, hz, huniq⟩ := hfun y hy
    refine ⟨z, ?_, fun z' hz' => huniq z' ?_⟩
    · show R _ _; rw [key]; exact hz
    · have : R (![y, z'] 0) (![y, z'] 1) := by rw [← key]; exact hz'
      exact this)
  obtain ⟨s, hs⟩ := this
  refine ⟨s, fun z => ?_⟩
  rw [hs z]
  constructor
  · rintro ⟨y, hy, h⟩
    refine ⟨y, hy, ?_⟩
    have : R (![y, z] 0) (![y, z] 1) := by rw [← key]; exact h
    exact this
  · rintro ⟨y, hy, h⟩
    refine ⟨y, hy, ?_⟩
    show R _ _; rw [key]; exact h

/-- Foundation for a definable predicate contained in the members of a set. -/
theorem class_foundationP {P : Z.S.X → Prop} (hP : Z.𝒞.Def 1 (fun t => P (t 0)))
    (x : Z.S.X) (hsub : ∀ y, P y → y ∈' x) (hne : ∃ y, P y) :
    ∃ y, P y ∧ ∀ z, (z ∈' y) → ¬ P z := by
  obtain ⟨s, hs⟩ := Z.sepP hP x
  obtain ⟨y0, hy0⟩ := hne
  obtain ⟨y, hy, hmin⟩ := Z.ax.foundation s ⟨y0, (hs y0).2 ⟨hsub y0 hy0, hy0⟩⟩
  exact ⟨y, ((hs y).1 hy).2, fun z hz hzP => hmin z hz ((hs z).2 ⟨hsub z hzP, hzP⟩)⟩

end ZFCModel

end SolidLean.Solid
