module

public import Solid.Gen.BaseSys
public import Solid.Gen.Translate

/-!
# Expansions by definable sorts

A *definable-sort expansion* `X` of a clause family `F` adds to the signature
of `T(𝔉)`:

* new sorts `m` (one for each `m : ℕ`), each meant to be a copy of a
  definable subset of the base sort `X.σ m` (the subset is given by a formula
  `X.domF m` of the tower signature);
* for each new sort `m`, an *encoding* symbol `enc m` relating the new sort
  to the base sort `X.σ m`;
* further relation symbols `X.Sym` on the base and new sorts, each with a
  clause (a formula of the tower signature read through the encodings).

Sorts of the expanded signature are indexed by `ℕ`: base sort `n` at
`2n`, new sort `m` at `2m + 1`.  The models of the expanded theory are the
structures whose base reduct is a model of `T(𝔉)`, in which each `enc m` is
the graph of a bijection from the new sort `m` onto the definable subset,
and in which every further symbol denotes its clause (`SortExp.IsModel`).

The main theorem (`SortExp.solid`) is that such an expansion of a solid
clause-family theory is solid: interpretations between models of the
expanded theory become interpretations between the base reducts once the
elements of the new sorts are replaced by their codes (`GenInterp.push`
along the coding `SortExp.flat`), and definable isomorphisms transfer both
ways.  This is the "trivial sort encoding" of draft 2 §6.3.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

/-- A definable-sort expansion of a clause family. -/
structure SortExp (F : ClauseFamily.{u}) where
  /-- The base sort in which new sort `m` is coded. -/
  σ : ℕ → ℕ
  /-- The definable subset of the base sort `σ m` that new sort `m` is a copy of. -/
  domF : (m : ℕ) → Formula TowerSig 1 ![σ m]
  /-- Further relation symbols. -/
  Sym : Type
  arity : Sym → ℕ
  /-- Argument sorts: `inl n` is base sort `n`, `inr m` is new sort `m`. -/
  sortAt : (f : Sym) → Fin (arity f) → ℕ ⊕ ℕ
  /-- The clause of a further symbol, on the codes of its arguments. -/
  symF : (f : Sym) → Formula TowerSig (arity f) (fun i => Sum.elim id σ (sortAt f i))

/-- The relation symbols of the expanded signature. -/
inductive ExpRel {F : ClauseFamily.{u}} (X : SortExp F)
  | base (r : F.sig.Rel)
  | enc (m : ℕ)
  | new (f : X.Sym)

namespace SortExp

/-- Sort index of base sort `n`. -/
abbrev bidx (n : ℕ) : ℕ := 2 * n

/-- Sort index of new sort `m`. -/
abbrev nidx (m : ℕ) : ℕ := 2 * m + 1

/-- Sort index of a base or new sort. -/
def idx : ℕ ⊕ ℕ → ℕ := Sum.elim bidx nidx

theorem bidx_injective : Function.Injective bidx := fun a b h => by simp [bidx] at h; omega

theorem bidx_mod (n : ℕ) : bidx n % 2 = 0 := by simp [bidx]

theorem bidx_div (n : ℕ) : bidx n / 2 = n := by simp [bidx]

theorem nidx_mod (m : ℕ) : nidx m % 2 = 1 := by simp [nidx]

theorem nidx_div (m : ℕ) : nidx m / 2 = m := by simp only [nidx]; omega

theorem eq_bidx_of_even {k : ℕ} (h : k % 2 = 0) : k = bidx (k / 2) := by simp [bidx]; omega

theorem eq_nidx_of_odd {k : ℕ} (h : ¬ k % 2 = 0) : k = nidx (k / 2) := by simp [nidx]; omega

theorem nidx_mod_ne (m : ℕ) : ¬ nidx m % 2 = 0 := by rw [nidx_mod]; exact one_ne_zero

/-! ### Assembling sortwise data by parity -/

section Parity

variable {U V : ℕ → Type u}

theorem sigma_cast_eq {β : ℕ → Type u} {a b : ℕ} (h : a = b) (x : β a) :
    (⟨b, cast (congrArg β h) x⟩ : Σ n, β n) = ⟨a, x⟩ := by subst h; rfl

/-- A sortwise function assembled from its components on the base sorts (`2n`)
and on the new sorts (`2m + 1`); the target sort may depend on the source sort. -/
noncomputable def parityDep (ρ : ℕ → ℕ) (f₀ : ∀ n, U (bidx n) → V (ρ (bidx n)))
    (f₁ : ∀ m, U (nidx m) → V (ρ (nidx m))) (k : ℕ) : U k → V (ρ k) :=
  if h : k % 2 = 0 then
    fun x => cast (congrArg (fun j => V (ρ j)) (eq_bidx_of_even h).symm)
      (f₀ (k / 2) (cast (congrArg U (eq_bidx_of_even h)) x))
  else
    fun x => cast (congrArg (fun j => V (ρ j)) (eq_nidx_of_odd h).symm)
      (f₁ (k / 2) (cast (congrArg U (eq_nidx_of_odd h)) x))

theorem parityDep_bidx (ρ : ℕ → ℕ) (f₀ : ∀ n, U (bidx n) → V (ρ (bidx n)))
    (f₁ : ∀ m, U (nidx m) → V (ρ (nidx m))) (n : ℕ) (x : U (bidx n)) :
    parityDep ρ f₀ f₁ (bidx n) x = f₀ n x := by
  unfold parityDep
  rw [dif_pos (bidx_mod n)]
  have key : ∀ (n' : ℕ) (hn : n' = n) (x' : U (bidx n')), HEq x' x →
      cast (congrArg (fun j => V (ρ j)) (congrArg bidx hn)) (f₀ n' x') = f₀ n x := by
    intro n' hn x' hx
    subst hn
    have hx' := eq_of_heq hx
    subst hx'
    rfl
  exact key _ (bidx_div n) _ (cast_heq _ _)

theorem parityDep_nidx (ρ : ℕ → ℕ) (f₀ : ∀ n, U (bidx n) → V (ρ (bidx n)))
    (f₁ : ∀ m, U (nidx m) → V (ρ (nidx m))) (m : ℕ) (x : U (nidx m)) :
    parityDep ρ f₀ f₁ (nidx m) x = f₁ m x := by
  unfold parityDep
  rw [dif_neg (nidx_mod_ne m)]
  have key : ∀ (m' : ℕ) (hm : m' = m) (x' : U (nidx m')), HEq x' x →
      cast (congrArg (fun j => V (ρ j)) (congrArg nidx hm)) (f₁ m' x') = f₁ m x := by
    intro m' hm x' hx
    subst hm
    have hx' := eq_of_heq hx
    subst hx'
    rfl
  exact key _ (nidx_div m) _ (cast_heq _ _)

theorem parityDep_bijective (ρ : ℕ → ℕ) (f₀ : ∀ n, U (bidx n) → V (ρ (bidx n)))
    (f₁ : ∀ m, U (nidx m) → V (ρ (nidx m))) (h₀ : ∀ n, Function.Bijective (f₀ n))
    (h₁ : ∀ m, Function.Bijective (f₁ m)) (k : ℕ) : Function.Bijective (parityDep ρ f₀ f₁ k) := by
  by_cases h : k % 2 = 0
  · obtain ⟨n, rfl⟩ : ∃ n, k = bidx n := ⟨k / 2, eq_bidx_of_even h⟩
    have : parityDep ρ f₀ f₁ (bidx n) = f₀ n := funext (parityDep_bidx ρ f₀ f₁ n)
    rw [this]; exact h₀ n
  · obtain ⟨m, rfl⟩ : ∃ m, k = nidx m := ⟨k / 2, eq_nidx_of_odd h⟩
    have : parityDep ρ f₀ f₁ (nidx m) = f₁ m := funext (parityDep_nidx ρ f₀ f₁ m)
    rw [this]; exact h₁ m

end Parity

variable {F : ClauseFamily.{u}} (X : SortExp F)

/-- The base sort in which a sort is coded. -/
def bsort : ℕ ⊕ ℕ → ℕ := Sum.elim id X.σ

/-- The expanded signature. -/
abbrev sig : Signature where
  Rel := ExpRel X
  arity r := match r with
    | .base r => F.sig.arity r
    | .enc _ => 2
    | .new f => X.arity f
  sortAt r := match r with
    | .base r => fun i => bidx (F.sig.sortAt r i)
    | .enc m => ![nidx m, bidx (X.σ m)]
    | .new f => fun i => idx (X.sortAt f i)

/-! ### The base reduct -/

/-- The carrier of the base sorts of an expanded structure. -/
abbrev baseU (N : Str.{u} X.sig) : ℕ → Type u := fun n => N.U (bidx n)

/-- The coding of the base carrier into the expanded carrier (a sort embedding). -/
def dbl (N : Str.{u} X.sig) : Coding (X.baseU N) N.U where
  ρ := bidx
  c _ x := x
  inj _ _ _ h := h

theorem dbl_el (N : Str.{u} X.sig) (z : Sorted.El (X.baseU N)) : (X.dbl N).el z = ⟨bidx z.1, z.2⟩ := rfl

theorem dbl_isEmb (N : Str.{u} X.sig) : (X.dbl N).IsEmb where
  ρ_inj := bidx_injective
  c_surj _ x := ⟨x, rfl⟩

theorem dbl_el_injective (N : Str.{u} X.sig) : Function.Injective (X.dbl N).el := fun z z' h =>
  (X.dbl N).el_injective_of_sort (bidx_injective (congrArg Sigma.fst h)) h

theorem mem_dbl_img_iff (N : Str.{u} X.sig) {k : ℕ} (A : Sorted.Rel (X.baseU N) k)
    (u : Fin k → Sorted.El (X.baseU N)) :
    (fun i => (X.dbl N).el (u i)) ∈ (X.dbl N).img A ↔ u ∈ A := by
  constructor
  · rintro ⟨u', hu', h⟩
    have : u = u' := funext fun i => X.dbl_el_injective N (congrFun h i)
    rw [this]; exact hu'
  · intro hu; exact ⟨u, hu, rfl⟩

/-- The base reduct of an expanded structure. -/
def baseStr (N : Str.{u} X.sig) : Str.{u} F.sig where
  U := X.baseU N
  rel r := {t | (fun i => (X.dbl N).el (t i)) ∈ N.rel (.base r)}
  rel_sorts r t ht i := by
    have := N.rel_sorts (.base r) _ ht i
    exact bidx_injective this

@[simp] theorem baseStr_U (N : Str.{u} X.sig) : (X.baseStr N).U = X.baseU N := rfl

theorem mem_baseStr_rel (N : Str.{u} X.sig) (r : F.sig.Rel) (t : Fin (F.sig.arity r) → Sorted.El (X.baseU N)) :
    t ∈ (X.baseStr N).rel r ↔ (fun i => (X.dbl N).el (t i)) ∈ N.rel (.base r) := Iff.rfl

/-- The class system of the base reduct. -/
noncomputable def baseSys {N : Str.{u} X.sig} (𝒩 : StrSys N) : StrSys (X.baseStr N) where
  toClassSys := (X.dbl N).baseSys (X.dbl_isEmb N) 𝒩.toClassSys
  rel_mem r := by
    intro b
    have : (X.dbl N).img ((X.baseStr N).rel r ∩ Sorted.profileRel (X.baseU N) b) =
        N.rel (.base r) ∩ Sorted.profileRel N.U (fun i => bidx (b i)) := by
      ext t
      have hC := (X.dbl N).mem_img_profile_iff (X.dbl_isEmb N)
        (C := ((X.baseStr N).rel r : Sorted.Rel (X.baseU N) (F.sig.arity r))) b t
      refine hC.trans ?_
      constructor
      · rintro ⟨ht, hC⟩
        refine ⟨?_, ht⟩
        have hC' : (fun i => (X.dbl N).el ((X.dbl N).lift (X.dbl_isEmb N) b t ht i)) ∈ N.rel (.base r) := hC
        have : (fun i => (X.dbl N).el ((X.dbl N).lift (X.dbl_isEmb N) b t ht i)) = t :=
          funext fun i => (X.dbl N).el_lift (X.dbl_isEmb N) b t ht i
        rw [this] at hC'; exact hC'
      · rintro ⟨hr, ht⟩
        have ht' : ∀ i, (t i).1 = bidx (b i) := ht
        refine ⟨ht', ?_⟩
        show (fun i => (X.dbl N).el ((X.dbl N).lift (X.dbl_isEmb N) b t ht' i)) ∈ N.rel (.base r)
        have : (fun i => (X.dbl N).el ((X.dbl N).lift (X.dbl_isEmb N) b t ht' i)) = t :=
          funext fun i => (X.dbl N).el_lift (X.dbl_isEmb N) b t ht' i
        rw [this]; exact hr
    rw [this]
    exact 𝒩.inter_mem (𝒩.rel_mem (ExpRel.base r)) (𝒩.profileRel_mem _)

theorem mem_baseSys_iff {N : Str.{u} X.sig} (𝒩 : StrSys N) {k : ℕ} (C : Sorted.Rel (X.baseU N) k) :
    C ∈ (X.baseSys 𝒩).D k ↔
      ∀ b : Fin k → ℕ, (X.dbl N).img (C ∩ Sorted.profileRel (X.baseU N) b) ∈ 𝒩.D k := Iff.rfl

theorem _root_.SolidLean.Solid.Coding.img_inter_profile {U V : ℕ → Type u} (γ : Coding U V)
    (hρ : Function.Injective γ.ρ) {k : ℕ} (A : Sorted.Rel U k) (b : Fin k → ℕ) :
    γ.img (A ∩ Sorted.profileRel U b) = γ.img A ∩ Sorted.profileRel V (fun i => γ.ρ (b i)) := by
  ext t
  constructor
  · rintro ⟨u, ⟨hu, hub⟩, rfl⟩
    exact ⟨⟨u, hu, rfl⟩, fun i => by rw [γ.el_fst, hub i]⟩
  · rintro ⟨⟨u, hu, rfl⟩, ht⟩
    exact ⟨u, ⟨hu, fun i => hρ (ht i)⟩, rfl⟩

/-- A class of the base carrier whose doubled image is admissible is admissible
for the base class system. -/
theorem mem_baseSys_of_img {N : Str.{u} X.sig} (𝒩 : StrSys N) {k : ℕ} {C : Sorted.Rel (X.baseU N) k}
    (h : (X.dbl N).img C ∈ 𝒩.D k) : C ∈ (X.baseSys 𝒩).D k := by
  intro b
  rw [(X.dbl N).img_inter_profile bidx_injective]
  exact 𝒩.inter_mem h (𝒩.profileRel_mem _)

/-! ### Codes and models -/

/-- `w` (of a base sort) is the code of `z`: `z` itself if `z` is of a base
sort, the `enc`-image of `z` if `z` is of a new sort. -/
def Code (N : Str.{u} X.sig) (z : Sorted.El N.U) (w : Sorted.El (X.baseU N)) : Prop :=
  if z.1 % 2 = 0 then (X.dbl N).el w = z else ![z, (X.dbl N).el w] ∈ N.rel (.enc (z.1 / 2))

theorem Code_bidx (N : Str.{u} X.sig) {n : ℕ} (x : N.U (bidx n)) (w : Sorted.El (X.baseU N)) :
    X.Code N (Sorted.inj N.U x) w ↔ w = Sorted.inj (X.baseU N) (n := n) x := by
  unfold Code
  rw [if_pos (bidx_mod n)]
  constructor
  · intro h
    obtain ⟨n', w'⟩ := w
    have h1 : bidx n' = bidx n := congrArg Sigma.fst h
    have hn : n' = n := bidx_injective h1
    subst hn
    have hw : w' = x := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    rw [hw]
  · rintro rfl; rfl

theorem Code_nidx (N : Str.{u} X.sig) {m : ℕ} (z : N.U (nidx m)) (w : Sorted.El (X.baseU N)) :
    X.Code N (Sorted.inj N.U z) w ↔ ![Sorted.inj N.U z, (X.dbl N).el w] ∈ N.rel (.enc m) := by
  unfold Code
  have h1 : ¬ (Sorted.inj N.U z).1 % 2 = 0 := by simp [nidx_mod]
  rw [if_neg h1]
  have h2 : (Sorted.inj N.U z).1 / 2 = m := nidx_div m
  rw [h2]

/-- The models of the expanded theory. -/
structure IsModel (N : StrWithSys.{u} X.sig) : Prop where
  /-- The base reduct is a model of `T(𝔉)`. -/
  base : F.IsGenModel ⟨X.baseStr N.M, X.baseSys N.𝒟⟩
  /-- Each encoding is the graph of a function ... -/
  enc_total : ∀ m (z : N.M.U (nidx m)), ∃ w : N.M.U (bidx (X.σ m)),
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U w] ∈ N.M.rel (.enc m)
  enc_unique : ∀ m (z : N.M.U (nidx m)) (w w' : N.M.U (bidx (X.σ m))),
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U w] ∈ N.M.rel (.enc m) →
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U w'] ∈ N.M.rel (.enc m) → w = w'
  /-- ... which is injective ... -/
  enc_inj : ∀ m (z z' : N.M.U (nidx m)) (w : N.M.U (bidx (X.σ m))),
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U w] ∈ N.M.rel (.enc m) →
    ![Sorted.inj N.M.U z', Sorted.inj N.M.U w] ∈ N.M.rel (.enc m) → z = z'
  /-- ... with image the definable subset. -/
  enc_dom : ∀ m (w : N.M.U (bidx (X.σ m))),
    (∃ z : N.M.U (nidx m), ![Sorted.inj N.M.U z, Sorted.inj N.M.U w] ∈ N.M.rel (.enc m)) ↔
      (X.domF m).Sat (ClauseFamily.Δ (X.baseStr N.M) base.wf).toStr ![Sorted.inj (X.baseU N.M) (n := X.σ m) w]
  /-- Every further symbol denotes its clause, read on the codes. -/
  sym : ∀ f (t : Fin (X.arity f) → Sorted.El N.M.U), t ∈ N.M.rel (.new f) ↔
    (∀ i, (t i).1 = idx (X.sortAt f i)) ∧ ∃ c : Fin (X.arity f) → Sorted.El (X.baseU N.M),
      (∀ i, X.Code N.M (t i) (c i)) ∧ (X.symF f).Sat (ClauseFamily.Δ (X.baseStr N.M) base.wf).toStr c

/-! ### Codes: flattening a model onto its base sorts -/

/-- The base sort coding a sort: base sorts code themselves, new sort `m` is
coded in `σ m`. -/
def flatSort (k : ℕ) : ℕ := if k % 2 = 0 then k / 2 else X.σ (k / 2)

theorem flatSort_bidx (n : ℕ) : X.flatSort (bidx n) = n := by
  unfold flatSort; rw [if_pos (bidx_mod n), bidx_div]

theorem flatSort_nidx (m : ℕ) : X.flatSort (nidx m) = X.σ m := by
  unfold flatSort; rw [if_neg (nidx_mod_ne m), nidx_div]

section Flat

variable {N : StrWithSys.{u} X.sig} (hN : X.IsModel N)

/-- The encoding function of new sort `m`. -/
noncomputable def encFun (m : ℕ) (z : N.M.U (nidx m)) : N.M.U (bidx (X.σ m)) :=
  Classical.choose (hN.enc_total m z)

theorem encFun_spec (m : ℕ) (z : N.M.U (nidx m)) :
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U (X.encFun hN m z)] ∈ N.M.rel (.enc m) :=
  Classical.choose_spec (hN.enc_total m z)

theorem enc_iff (m : ℕ) (z : N.M.U (nidx m)) (w : N.M.U (bidx (X.σ m))) :
    ![Sorted.inj N.M.U z, Sorted.inj N.M.U w] ∈ N.M.rel (.enc m) ↔ w = X.encFun hN m z :=
  ⟨fun h => hN.enc_unique m z w _ h (X.encFun_spec hN m z),
   fun h => by rw [h]; exact X.encFun_spec hN m z⟩

theorem encFun_injective (m : ℕ) : Function.Injective (X.encFun hN m) := fun z z' h =>
  hN.enc_inj m z z' _ (X.encFun_spec hN m z) (by rw [h]; exact X.encFun_spec hN m z')

/-- The code of a base element: itself. -/
def flatBase (N : Str.{u} X.sig) (n : ℕ) (x : N.U (bidx n)) : X.baseU N (X.flatSort (bidx n)) :=
  cast (congrArg (X.baseU N) (X.flatSort_bidx n).symm) x

/-- The code of a new element: its encoding. -/
noncomputable def flatNew (m : ℕ) (z : N.M.U (nidx m)) : X.baseU N.M (X.flatSort (nidx m)) :=
  cast (congrArg (X.baseU N.M) (X.flatSort_nidx m).symm) (X.encFun hN m z)

/-- The coding of a model onto its base sorts: base elements code themselves,
new elements are coded by their encodings. -/
noncomputable def flat : Coding N.M.U (X.baseU N.M) where
  ρ := X.flatSort
  c := parityDep X.flatSort (X.flatBase N.M) (X.flatNew hN)
  inj k := by
    by_cases h : k % 2 = 0
    · obtain ⟨n, rfl⟩ : ∃ n, k = bidx n := ⟨k / 2, eq_bidx_of_even h⟩
      intro x y hxy
      rw [parityDep_bidx, parityDep_bidx] at hxy
      exact (cast_inj _).mp hxy
    · obtain ⟨m, rfl⟩ : ∃ m, k = nidx m := ⟨k / 2, eq_nidx_of_odd h⟩
      intro x y hxy
      rw [parityDep_nidx, parityDep_nidx] at hxy
      exact X.encFun_injective hN m ((cast_inj _).mp hxy)

@[simp] theorem flat_ρ (k : ℕ) : (X.flat hN).ρ k = X.flatSort k := rfl

theorem flat_c_bidx (n : ℕ) (x : N.M.U (bidx n)) : (X.flat hN).c (bidx n) x = X.flatBase N.M n x :=
  parityDep_bidx X.flatSort (X.flatBase N.M) (X.flatNew hN) n x

theorem flat_c_nidx (m : ℕ) (z : N.M.U (nidx m)) : (X.flat hN).c (nidx m) z = X.flatNew hN m z :=
  parityDep_nidx X.flatSort (X.flatBase N.M) (X.flatNew hN) m z

theorem flat_el_bidx (n : ℕ) (x : N.M.U (bidx n)) :
    (X.flat hN).el (Sorted.inj N.M.U x) = Sorted.inj (X.baseU N.M) (n := n) x := by
  show (⟨X.flatSort (bidx n), (X.flat hN).c (bidx n) x⟩ : Sorted.El (X.baseU N.M)) = ⟨n, x⟩
  rw [X.flat_c_bidx hN]
  exact sigma_cast_eq (β := X.baseU N.M) (X.flatSort_bidx n).symm x

theorem flat_el_nidx (m : ℕ) (z : N.M.U (nidx m)) :
    (X.flat hN).el (Sorted.inj N.M.U z) = Sorted.inj (X.baseU N.M) (n := X.σ m) (X.encFun hN m z) := by
  show (⟨X.flatSort (nidx m), (X.flat hN).c (nidx m) z⟩ : Sorted.El (X.baseU N.M)) = ⟨X.σ m, _⟩
  rw [X.flat_c_nidx hN]
  exact sigma_cast_eq (β := X.baseU N.M) (X.flatSort_nidx m).symm _

theorem dbl_flat_bidx (n : ℕ) (x : N.M.U (bidx n)) :
    (X.dbl N.M).el ((X.flat hN).el (Sorted.inj N.M.U x)) = Sorted.inj N.M.U x := by
  rw [X.flat_el_bidx hN]; rfl

theorem dbl_flat_nidx (m : ℕ) (z : N.M.U (nidx m)) :
    (X.dbl N.M).el ((X.flat hN).el (Sorted.inj N.M.U z)) = Sorted.inj N.M.U (X.encFun hN m z) := by
  rw [X.flat_el_nidx hN]; rfl

/-- The relation "`w` is the code of `z`", for `z` of sort `k`: equality on a
base sort, the encoding on a new sort. -/
def codeRel (N : Str.{u} X.sig) (k : ℕ) : Sorted.Rel N.U 2 :=
  if k % 2 = 0 then Sorted.eqRel N.U ∩ Sorted.profileRel N.U ![k, k] else N.rel (.enc (k / 2))

theorem codeRel_mem {N : Str.{u} X.sig} (𝒩 : StrSys N) (k : ℕ) : X.codeRel N k ∈ 𝒩.D 2 := by
  unfold codeRel
  split_ifs
  · exact 𝒩.inter_mem 𝒩.eq_mem (𝒩.profileRel_mem _)
  · exact 𝒩.rel_mem (.enc (k / 2))

theorem mem_codeRel_iff (z w : Sorted.El N.M.U) :
    ![z, w] ∈ X.codeRel N.M z.1 ↔ w = (X.dbl N.M).el ((X.flat hN).el z) := by
  obtain ⟨k, x⟩ := z
  by_cases h : k % 2 = 0
  · obtain ⟨n, rfl⟩ : ∃ n, k = bidx n := ⟨k / 2, eq_bidx_of_even h⟩
    show ![Sorted.inj N.M.U x, w] ∈ X.codeRel N.M (bidx n) ↔ _
    rw [X.dbl_flat_bidx hN]
    unfold codeRel
    rw [if_pos (bidx_mod n)]
    constructor
    · rintro ⟨h1, -⟩
      exact (h1 : Sorted.inj N.M.U x = w).symm
    · rintro rfl
      refine ⟨rfl, fun i => ?_⟩
      match i with
      | 0 => rfl
      | 1 => rfl
  · obtain ⟨m, rfl⟩ : ∃ m, k = nidx m := ⟨k / 2, eq_nidx_of_odd h⟩
    show ![Sorted.inj N.M.U x, w] ∈ X.codeRel N.M (nidx m) ↔ _
    rw [X.dbl_flat_nidx hN]
    unfold codeRel
    rw [if_neg (nidx_mod_ne m), nidx_div]
    constructor
    · intro hw
      have hs : w.1 = bidx (X.σ m) := N.M.rel_sorts (.enc m) _ hw 1
      obtain ⟨k', w'⟩ := w
      have hk : k' = bidx (X.σ m) := hs
      subst hk
      have := (X.enc_iff hN m x w').1 hw
      rw [this]
    · rintro rfl
      exact X.encFun_spec hN m x

/-- The flattening coding is compatible with the class systems of the model and
of its base reduct. -/
theorem flat_compat : (X.flat hN).Compat N.𝒟.toClassSys (X.baseSys N.𝒟).toClassSys where
  img_mem := by
    intro k A b hA hb
    apply X.mem_baseSys_of_img
    have e : (X.dbl N.M).img ((X.flat hN).img A) = ClassSys.imageRel A (fun i => X.codeRel N.M (b i)) := by
      ext t
      constructor
      · rintro ⟨u', ⟨u, hu, rfl⟩, rfl⟩
        refine ⟨u, hu, fun i => ?_⟩
        show ![u i, (X.dbl N.M).el ((X.flat hN).el (u i))] ∈ X.codeRel N.M (b i)
        rw [← hb u hu i]
        exact (X.mem_codeRel_iff hN (u i) _).2 rfl
      · rintro ⟨u, hu, hR⟩
        refine ⟨fun i => (X.flat hN).el (u i), ⟨u, hu, rfl⟩, ?_⟩
        funext i
        have h1 : ![u i, t i] ∈ X.codeRel N.M (b i) := hR i
        rw [← hb u hu i] at h1
        exact (X.mem_codeRel_iff hN (u i) (t i)).1 h1
    rw [e]
    exact N.𝒟.imageRel_mem b hA hb (fun i => X.codeRel_mem N.𝒟 (b i))
  pre_mem := by
    intro k B b hB
    have hB' := hB (fun i => X.flatSort (b i))
    have e : (X.flat hN).pre b B = Sorted.profileRel N.M.U b ∩
        ClassSys.imageRel ((X.dbl N.M).img (B ∩ Sorted.profileRel (X.baseU N.M) (fun i => X.flatSort (b i))))
          (fun i => {s | ![s 1, s 0] ∈ X.codeRel N.M (b i)}) := by
      ext t
      constructor
      · rintro ⟨ht, htB⟩
        refine ⟨ht, fun i => (X.dbl N.M).el ((X.flat hN).el (t i)),
          ⟨fun i => (X.flat hN).el (t i), ⟨htB, fun i => ?_⟩, rfl⟩, fun i => ?_⟩
        · show X.flatSort (t i).1 = X.flatSort (b i)
          rw [ht i]
        · show ![t i, (X.dbl N.M).el ((X.flat hN).el (t i))] ∈ X.codeRel N.M (b i)
          rw [← ht i]
          exact (X.mem_codeRel_iff hN (t i) _).2 rfl
      · rintro ⟨ht, s, ⟨v, ⟨hvB, -⟩, rfl⟩, hR⟩
        refine ⟨ht, ?_⟩
        have hv : ∀ i, (X.flat hN).el (t i) = v i := by
          intro i
          have h1 : ![t i, (X.dbl N.M).el (v i)] ∈ X.codeRel N.M (b i) := hR i
          rw [← ht i] at h1
          exact X.dbl_el_injective N.M ((X.mem_codeRel_iff hN _ _).1 h1).symm
        have : (fun i => (X.flat hN).el (t i)) = v := funext hv
        rw [this]; exact hvB
    rw [e]
    refine N.𝒟.inter_mem (N.𝒟.profileRel_mem b) ?_
    refine N.𝒟.imageRel_mem (fun i => bidx (X.flatSort (b i))) hB' ?_
      (fun i => N.𝒟.converse_mem (X.codeRel_mem N.𝒟 (b i)))
    rintro s ⟨v, ⟨-, hvp⟩, rfl⟩ i
    show bidx (v i).1 = bidx (X.flatSort (b i))
    rw [hvp i]

end Flat

end SortExp

/-! ### Interpretations: restriction of the target to the base sorts -/

namespace GenInterp

open SortExp

variable {F : ClauseFamily.{u}} (X : SortExp F)
variable {U : ℕ → Type u} {𝒟 : ClassSys U} (I : GenInterp U 𝒟 X.sig)

/-- The interpretation of the base reduct of the model, in the same ambient. -/
def baseTarget : GenInterp U 𝒟 F.sig where
  a n := I.a (bidx n)
  dom n := I.dom (bidx n)
  eqv n := I.eqv (bidx n)
  eqv_refl n := I.eqv_refl (bidx n)
  eqv_symm n := I.eqv_symm (bidx n)
  eqv_trans n := I.eqv_trans (bidx n)
  eqv_dom n := I.eqv_dom (bidx n)
  dom_def n := I.dom_def (bidx n)
  eqv_def n := I.eqv_def (bidx n)
  relC r := I.relC (.base r)
  relC_dom r := I.relC_dom (.base r)
  relC_congr r := I.relC_congr (.base r)
  relC_def r := I.relC_def (.base r)

@[simp] theorem baseTarget_a (n : ℕ) : (I.baseTarget X).a n = I.a (bidx n) := rfl

/-- The carrier of the base-target interpretation is the base carrier of the model. -/
theorem baseTarget_Carrier (n : ℕ) : (I.baseTarget X).Carrier n = X.baseU I.model n := rfl

/-- Representation for the base target. -/
theorem baseTarget_Rep (y : Sorted.El U) (z : Sorted.El (X.baseU I.model)) :
    (I.baseTarget X).Rep y z ↔ I.Rep y ((X.dbl I.model).el z) := by
  constructor
  · rintro ⟨n, x, rfl, rfl⟩
    exact ⟨bidx n, x, rfl, rfl⟩
  · rintro ⟨n', x', rfl, h⟩
    obtain ⟨n, q⟩ := z
    have hn : bidx n = n' := congrArg Sigma.fst h
    subst hn
    have hq : q = I.cls x' := eq_of_heq (Sigma.mk.inj_iff.mp h).2
    subst hq
    exact ⟨n, x', rfl, rfl⟩

/-- The model of the base target is the base reduct of the model. -/
theorem baseTarget_model_rel (r : F.sig.Rel) (t : Fin (F.sig.arity r) → Sorted.El (X.baseU I.model)) :
    t ∈ (I.baseTarget X).model.rel r ↔ t ∈ (X.baseStr I.model).rel r := by
  show t ∈ (I.baseTarget X).relQ r ↔ (fun i => (X.dbl I.model).el (t i)) ∈ I.relQ (.base r)
  constructor
  · rintro ⟨u, hu, hrel⟩
    refine ⟨u, fun i => ⟨?_, ?_⟩, hrel⟩
    · show bidx (t i).1 = bidx (F.sig.sortAt r i)
      rw [(hu i).1]
    · exact ((I.baseTarget_Rep X) _ _).1 (hu i).2
  · rintro ⟨u, hu, hrel⟩
    refine ⟨u, fun i => ⟨?_, ?_⟩, hrel⟩
    · exact bidx_injective (hu i).1
    · exact ((I.baseTarget_Rep X) _ _).2 (hu i).2

/-- The identity, as an isomorphism from the model of the base target to the
base reduct of the model. -/
def baseTargetIso : GenIso (I.baseTarget X).model (X.baseStr I.model) where
  toFun _ x := x
  bijective _ := Function.bijective_id
  rel_iff r t := I.baseTarget_model_rel X r t

theorem baseTargetIso_mapEl (z : Sorted.El (I.baseTarget X).model.U) :
    (I.baseTargetIso X).mapEl z = z := rfl

/-- The identity, as an isomorphism from the base reduct of the model to the
model of the base target. -/
def baseIso : GenIso (X.baseStr I.model) (I.baseTarget X).model where
  toFun _ x := x
  bijective _ := Function.bijective_id
  rel_iff r t := (I.baseTarget_model_rel X r t).symm

theorem baseIso_mapEl (z : Sorted.El (X.baseU I.model)) : (I.baseIso X).mapEl z = z := rfl

/-- The preimage under the base target is the preimage of the doubled image. -/
theorem baseTarget_preimage {k : ℕ} (b : Fin k → ℕ) (D : Sorted.Rel (X.baseU I.model) k) :
    (I.baseTarget X).preimage b D =
      I.preimage (fun i => bidx (b i)) ((X.dbl I.model).img (D ∩ Sorted.profileRel (X.baseU I.model) b)) := by
  ext t
  constructor
  · rintro ⟨u, hu, hD⟩
    refine ⟨fun i => (X.dbl I.model).el (u i), fun i => ⟨?_, ?_⟩, u, ⟨hD, fun i => (hu i).1⟩, rfl⟩
    · show bidx (u i).1 = bidx (b i)
      rw [(hu i).1]
    · exact (I.baseTarget_Rep X _ _).1 (hu i).2
  · rintro ⟨u', hu', u, ⟨hD, hub⟩, rfl⟩
    refine ⟨u, fun i => ⟨hub i, ?_⟩, hD⟩
    exact (I.baseTarget_Rep X _ _).2 (hu' i).2

/-- Classes of the base reduct admissible for a class system below the induced
one are admissible for the induced system of the base target. -/
theorem baseTarget_induced_of {𝒩 : StrSys I.model}
    (h𝒩 : ∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩.D k → C ∈ I.induced.D k)
    {k : ℕ} {D : Sorted.Rel (X.baseU I.model) k} (hD : D ∈ (X.baseSys 𝒩).D k) :
    D ∈ (I.baseTarget X).induced.D k := by
  refine ((I.baseTarget X).mem_induced_iff D).2 fun b => ?_
  rw [I.baseTarget_preimage X]
  exact (I.mem_induced_iff _).1 (h𝒩 _ _ (hD b)) _

end GenInterp

namespace GenIso

variable {F : ClauseFamily.{u}} (X : SortExp F)

theorem mapEl_symm_apply {Sig : Signature} {M N : Str.{u} Sig} (i : GenIso M N) (z : Sorted.El N.U) :
    i.mapEl (i.symm.mapEl z) = z :=
  Sigma.ext rfl (heq_of_eq (Function.surjInv_eq (i.bijective z.1).2 z.2))

/-- The restriction of an isomorphism of expanded structures to the base reducts. -/
def base {N N' : Str.{u} X.sig} (i : GenIso N N') : GenIso (X.baseStr N) (X.baseStr N') where
  toFun n := i.toFun (SortExp.bidx n)
  bijective n := i.bijective (SortExp.bidx n)
  rel_iff r t := i.rel_iff (.base r) (fun j => (X.dbl N).el (t j))

theorem base_toFun {N N' : Str.{u} X.sig} (i : GenIso N N') (n : ℕ) (x : N.U (SortExp.bidx n)) :
    (i.base X).toFun n x = i.toFun (SortExp.bidx n) x := rfl

theorem dbl_base_mapEl {N N' : Str.{u} X.sig} (i : GenIso N N') (w : Sorted.El (X.baseU N)) :
    (X.dbl N').el ((i.base X).mapEl w) = i.mapEl ((X.dbl N).el w) := rfl

end GenIso

end SolidLean.Solid
