import Solid.Lift
import Solid.Graphs
import Solid.Mostowski

/-!
# Collapse data and its consequences (Step 4)

`CollapseData` records what Steps 1–3 of draft 2 §2 produce for a tower `P`
presented in a tower `N`: for every `n`, an injective membership-preserving
map `e n` from sort `n` of `P` onto the members of a transitive,
subset-closed set `S n` of some sort `b n` of `N`, compatible with the
transitions, and definable over the presentation.

Step 4 is then a matter of transport: `e (n+1)` is an inner embedding of
sort `n+1` of `P` into sort `b (n+1)` of `N`, so the axioms of `H` in `P`
transfer.  With `δ n := e (n+1) (κ n)` this gives `S n = V(δ n)` (after
lifting), inaccessibility of `δ n`, the next-inaccessible clause and the
bottom clause (`CollapseData.isV`, `δ_inaccessible`, `δ_next`, `δ_bottom`).
-/

universe u

namespace SolidLean.Solid

open Classical

/-- Steps 1–3: collapse data for `P` presented in `N`. -/
structure CollapseData (N PC : TowerWithClasses.{u}) (p : Presentation N.T.U PC.T.U) where
  b : ℕ → ℕ
  b_mono : ∀ n, b n ≤ b (n + 1)
  b_ge : ∀ n, n + 1 ≤ b n
  S : ∀ n, N.T.U (b n)
  e : ∀ n, PC.T.U n → N.T.U (b n)
  e_mem : ∀ n x, N.T.mem (e n x) (S n)
  e_surj : ∀ n y, N.T.mem y (S n) → ∃ x, e n x = y
  e_injective : ∀ n, Function.Injective (e n)
  e_mem_iff : ∀ n x y, N.T.mem (e n x) (e n y) ↔ PC.T.mem x y
  S_trans : ∀ n, (N.T.sortStr (b n)).Transitive (S n)
  S_supertrans : ∀ n y z, N.T.mem y (S n) → (N.T.sortStr (b n)).Subset z y → N.T.mem z (S n)
  e_transition : ∀ n x, N.T.liftLE (b_mono n) (e n x) = e (n + 1) (PC.T.j n x)
  e_definable : ∀ n, PGraph p (e n) ∈ N.𝒟.D 2

namespace CollapseData

variable {N PC : TowerWithClasses.{u}} {p : Presentation N.T.U PC.T.U} (C : CollapseData N PC p)
  (hN : IsTowerModel N) (hP : IsTowerModel PC)

/-- The collapse of sort `n` as an inner embedding. -/
noncomputable def emb (n : ℕ) : InnerEmb (hP.sortModel n) (hN.sortModel (C.b n)) where
  φ := C.e n
  injective := C.e_injective n
  mem_iff := C.e_mem_iff n
  trans := by
    intro x z hz
    exact C.e_surj n z (C.S_trans n _ (C.e_mem n x) z hz)
  supertrans := by
    intro x z hz
    exact C.e_surj n z (C.S_supertrans n _ z (C.e_mem n x) hz)

@[simp] theorem emb_φ (n : ℕ) (x : PC.T.U n) : (C.emb hN hP n).φ x = C.e n x := rfl

/-- The collapsed heights. -/
noncomputable def δ (n : ℕ) : N.T.U (C.b (n + 1)) := C.e (n + 1) (PC.T.κ n)

include hN in
theorem mem_lift_S_iff (n : ℕ) (z : N.T.U (C.b (n + 1))) :
    N.T.mem z (N.T.liftLE (C.b_mono n) (C.S n)) ↔
      ∃ x, N.T.liftLE (C.b_mono n) (C.e n x) = z := by
  have key := (hN.liftEmb (C.b_mono n)).mem_image_iff (C.S n) z
  change N.T.mem z (N.T.liftLE _ (C.S n)) ↔
    ∃ y, N.T.mem y (C.S n) ∧ N.T.liftLE _ y = z at key
  rw [key]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := C.e_surj n y hy
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    exact ⟨C.e n x, C.e_mem n x, rfl⟩

include hN hP in
/-- Step 4: the lifted collapsed set is the rank segment at the collapsed
height. -/
theorem isV (n : ℕ) :
    (N.T.sortStr (C.b (n + 1))).IsV (C.δ n) (N.T.liftLE (C.b_mono n) (C.S n)) := by
  obtain ⟨v, hv, hmem⟩ := hP.j_image n
  have h := (C.emb hN hP (n + 1)).isV_of hv
  simp only [emb_φ] at h
  have : C.e (n + 1) v = N.T.liftLE (C.b_mono n) (C.S n) := by
    apply (hN.sortModel (C.b (n + 1))).ax.ext
    intro z
    show N.T.mem z (C.e (n + 1) v) ↔ N.T.mem z (N.T.liftLE _ (C.S n))
    rw [C.mem_lift_S_iff hN n z]
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := ((C.emb hN hP (n + 1)).mem_image_iff v z).1 hz
      obtain ⟨x, rfl⟩ := (hmem y).1 hy
      exact ⟨x, C.e_transition n x⟩
    · rintro ⟨x, rfl⟩
      rw [C.e_transition n x]
      exact ((C.emb hN hP (n + 1)).mem_image_iff v _).2
        ⟨PC.T.j n x, (hmem _).2 ⟨x, rfl⟩, rfl⟩
  rw [← this]
  exact h

include hN hP in
theorem δ_inaccessible (n : ℕ) : (N.T.sortStr (C.b (n + 1))).Inaccessible (C.δ n) :=
  ((C.emb hN hP (n + 1)).inaccessible_iff _).2 (hP.kappa_inaccessible n)

include hN hP in
theorem δ_next (n : ℕ) : (N.T.sortStr (C.b (n + 2))).NextInaccessible
    (N.T.liftLE (C.b_mono (n + 1)) (C.δ n)) (C.δ (n + 1)) := by
  have h := ((C.emb hN hP (n + 2)).nextInaccessible_iff _ _).2 (hP.next_inaccessible n)
  simp only [emb_φ] at h
  unfold δ
  rw [C.e_transition (n + 1)]
  exact h

include hN hP in
theorem δ_bottom : (N.T.sortStr (C.b 1)).NoGreatestInaccessibleBelow (C.δ 0) :=
  ((C.emb hN hP 1).noGreatestInaccessibleBelow_iff _).2 hP.bottom

include hN hP in
theorem δ_ordinal (n : ℕ) : (N.T.sortStr (C.b (n + 1))).IsOrdinal (C.δ n) :=
  (C.δ_inaccessible hN hP n).1.1

end CollapseData

end SolidLean.Solid
