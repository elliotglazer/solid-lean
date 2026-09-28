import Solid.Gen.Push
import Solid.Gen.ClassOps

/-!
# The class system pulled back along a sort embedding

A *sort embedding* is a coding `γ : Coding U V` whose sort map `ρ` is
injective and whose maps `c k : U k → V (ρ k)` are bijective: the sorts of `U`
are (renamed) sorts of `V`.  A class system `𝒟'` on `V` pulls back to the
class system on `U` whose classes are those whose images, profile by profile,
are classes of `𝒟'` (`Coding.baseSys`).  This is the class system of the
reduct of a structure with extra sorts to its original sorts.
-/

universe u

namespace SolidLean.Solid

open Classical

namespace Coding

variable {U V : ℕ → Type u} (γ : Coding U V)

/-- A sort embedding: injective on sorts, bijective on each sort. -/
structure IsEmb : Prop where
  ρ_inj : Function.Injective γ.ρ
  c_surj : ∀ k, Function.Surjective (γ.c k)

variable (hγ : γ.IsEmb)

/-- The element of sort `k` coding a given element of sort `ρ k`. -/
noncomputable def unc (k : ℕ) (y : V (γ.ρ k)) : U k := Function.surjInv (hγ.c_surj k) y

theorem c_unc (k : ℕ) (y : V (γ.ρ k)) : γ.c k (γ.unc hγ k y) = y :=
  Function.surjInv_eq (hγ.c_surj k) y

theorem unc_c (k : ℕ) (x : U k) : γ.unc hγ k (γ.c k x) = x :=
  γ.inj k (γ.c_unc hγ k (γ.c k x))

/-- The tuple of sorts `b` coding a tuple of sorts `ρ ∘ b`. -/
noncomputable def lift {k : ℕ} (b : Fin k → ℕ) (t : Fin k → Sorted.El V) (ht : ∀ i, (t i).1 = γ.ρ (b i)) :
    Fin k → Sorted.El U :=
  fun i => Sorted.inj U (γ.unc hγ (b i) (Sorted.toSort V (t i) (ht i)))

theorem el_lift {k : ℕ} (b : Fin k → ℕ) (t : Fin k → Sorted.El V) (ht : ∀ i, (t i).1 = γ.ρ (b i)) (i : Fin k) :
    γ.el (γ.lift hγ b t ht i) = t i := by
  show Sorted.inj V (γ.c (b i) (γ.unc hγ (b i) (Sorted.toSort V (t i) (ht i)))) = t i
  rw [γ.c_unc, Sorted.inj_toSort]

theorem lift_sort {k : ℕ} (b : Fin k → ℕ) (t : Fin k → Sorted.El V) (ht : ∀ i, (t i).1 = γ.ρ (b i)) (i : Fin k) :
    (γ.lift hγ b t ht i).1 = b i := rfl

/-- Membership in the image of a class intersected with a profile. -/
theorem mem_img_profile_iff {k : ℕ} (C : Sorted.Rel U k) (b : Fin k → ℕ) (t : Fin k → Sorted.El V) :
    t ∈ γ.img (C ∩ Sorted.profileRel U b) ↔
      ∃ ht : ∀ i, (t i).1 = γ.ρ (b i), γ.lift hγ b t ht ∈ C := by
  constructor
  · rintro ⟨u, ⟨hu, hub⟩, rfl⟩
    have ht : ∀ i, (γ.el (u i)).1 = γ.ρ (b i) := fun i => by rw [γ.el_fst, hub i]
    refine ⟨ht, ?_⟩
    have : γ.lift hγ b (fun i => γ.el (u i)) ht = u := by
      funext i
      refine γ.el_injective_of_sort ?_ (γ.el_lift hγ b _ ht i)
      rw [γ.lift_sort]; exact (hub i).symm
    rw [this]; exact hu
  · rintro ⟨ht, hC⟩
    exact ⟨γ.lift hγ b t ht, ⟨hC, fun i => γ.lift_sort hγ b t ht i⟩, funext fun i => (γ.el_lift hγ b t ht i).symm⟩

/-- The pulled-back class system. -/
noncomputable def baseSys (𝒟' : ClassSys V) : ClassSys U where
  D k := {C | ∀ b : Fin k → ℕ, γ.img (C ∩ Sorted.profileRel U b) ∈ 𝒟'.D k}
  eq_mem := by
    intro b
    by_cases h : b 0 = b 1
    · have : γ.img (Sorted.eqRel U ∩ Sorted.profileRel U b) =
          Sorted.eqRel V ∩ Sorted.profileRel V (fun i => γ.ρ (b i)) := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        constructor
        · rintro ⟨ht, hC⟩
          refine ⟨?_, ht⟩
          show t 0 = t 1
          have e := congrArg γ.el (hC : γ.lift hγ b t ht 0 = γ.lift hγ b t ht 1)
          rwa [γ.el_lift, γ.el_lift] at e
        · rintro ⟨h01, ht⟩
          have ht' : ∀ i, (t i).1 = γ.ρ (b i) := ht
          refine ⟨ht', ?_⟩
          show γ.lift hγ b t ht' 0 = γ.lift hγ b t ht' 1
          refine γ.el_injective_of_sort ?_ ?_
          · rw [γ.lift_sort, γ.lift_sort, h]
          · rw [γ.el_lift, γ.el_lift]; exact h01
      rw [this]
      exact 𝒟'.inter_mem 𝒟'.eq_mem (𝒟'.profileRel_mem _)
    · have : γ.img (Sorted.eqRel U ∩ Sorted.profileRel U b) = ∅ := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        simp only [Set.mem_empty_iff_false, iff_false, not_exists]
        intro ht hC
        apply h
        have e := congrArg Sigma.fst (hC : γ.lift hγ b t ht 0 = γ.lift hγ b t ht 1)
        rwa [γ.lift_sort, γ.lift_sort] at e
      rw [this]; exact 𝒟'.empty_mem 2
  sort_mem n := by
    intro b
    by_cases h : b 0 = n
    · have : γ.img (Sorted.sortRel U n ∩ Sorted.profileRel U b) = Sorted.profileRel V (fun i => γ.ρ (b i)) := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        constructor
        · rintro ⟨ht, -⟩; exact ht
        · intro ht
          have ht' : ∀ i, (t i).1 = γ.ρ (b i) := ht
          refine ⟨ht', ?_⟩
          show (γ.lift hγ b t ht' 0).1 = n
          rw [γ.lift_sort, h]
      rw [this]; exact 𝒟'.profileRel_mem _
    · have : γ.img (Sorted.sortRel U n ∩ Sorted.profileRel U b) = ∅ := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        simp only [Set.mem_empty_iff_false, iff_false, not_exists]
        intro ht hC
        apply h
        have : (γ.lift hγ b t ht 0).1 = n := hC
        rwa [γ.lift_sort] at this
      rw [this]; exact 𝒟'.empty_mem 1
  param_mem p := by
    intro b
    by_cases h : b 0 = p.1
    · have : γ.img (Sorted.paramRel U p ∩ Sorted.profileRel U b) = Sorted.paramRel V (γ.el p) := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        constructor
        · rintro ⟨ht, hC⟩
          show t 0 = γ.el p
          rw [← γ.el_lift hγ b t ht 0]
          exact congrArg γ.el hC
        · intro h0
          have h0' : t 0 = γ.el p := h0
          have ht : ∀ i, (t i).1 = γ.ρ (b i) := by
            intro i
            have : i = 0 := Subsingleton.elim _ _
            subst this
            rw [h0', γ.el_fst, h]
          refine ⟨ht, ?_⟩
          show γ.lift hγ b t ht 0 = p
          refine γ.el_injective_of_sort ?_ ?_
          · rw [γ.lift_sort]; exact h
          · rw [γ.el_lift]; exact h0'
      rw [this]; exact 𝒟'.param_mem _
    · have : γ.img (Sorted.paramRel U p ∩ Sorted.profileRel U b) = ∅ := by
        ext t
        rw [γ.mem_img_profile_iff hγ]
        simp only [Set.mem_empty_iff_false, iff_false, not_exists]
        intro ht hC
        apply h
        have e := congrArg Sigma.fst (hC : γ.lift hγ b t ht 0 = p)
        rwa [γ.lift_sort] at e
      rw [this]; exact 𝒟'.empty_mem 1
  univ_mem k := by
    intro b
    have : γ.img ((Set.univ : Sorted.Rel U k) ∩ Sorted.profileRel U b) =
        Sorted.profileRel V (fun i => γ.ρ (b i)) := by
      ext t
      rw [γ.mem_img_profile_iff hγ]
      exact ⟨fun ⟨ht, _⟩ => ht, fun ht => ⟨(ht : ∀ i, (t i).1 = γ.ρ (b i)), Set.mem_univ _⟩⟩
    rw [this]; exact 𝒟'.profileRel_mem _
  inter_mem := by
    intro k C C' hC hC' b
    have : γ.img ((C ∩ C') ∩ Sorted.profileRel U b) =
        γ.img (C ∩ Sorted.profileRel U b) ∩ γ.img (C' ∩ Sorted.profileRel U b) := by
      ext t
      rw [Set.mem_inter_iff, γ.mem_img_profile_iff hγ, γ.mem_img_profile_iff hγ, γ.mem_img_profile_iff hγ]
      constructor
      · rintro ⟨ht, h1, h2⟩; exact ⟨⟨ht, h1⟩, ⟨ht, h2⟩⟩
      · rintro ⟨⟨ht, h1⟩, ⟨ht', h2⟩⟩; exact ⟨ht, h1, h2⟩
    rw [this]; exact 𝒟'.inter_mem (hC b) (hC' b)
  compl_mem := by
    intro k C hC b
    have : γ.img (Cᶜ ∩ Sorted.profileRel U b) =
        Sorted.profileRel V (fun i => γ.ρ (b i)) ∩ (γ.img (C ∩ Sorted.profileRel U b))ᶜ := by
      ext t
      rw [Set.mem_inter_iff, Set.mem_compl_iff, γ.mem_img_profile_iff hγ, γ.mem_img_profile_iff hγ]
      constructor
      · rintro ⟨ht, h1⟩
        exact ⟨ht, fun hh => h1 hh.2⟩
      · rintro ⟨ht, h1⟩
        have ht' : ∀ i, (t i).1 = γ.ρ (b i) := ht
        exact ⟨ht', fun h2 => h1 ⟨ht', h2⟩⟩
    rw [this]; exact 𝒟'.inter_mem (𝒟'.profileRel_mem _) (𝒟'.compl_mem (hC b))
  reindex_mem := by
    intro k l f C hC b
    have : γ.img (Sorted.reindex U f C ∩ Sorted.profileRel U b) =
        Sorted.reindex V f (γ.img (C ∩ Sorted.profileRel U (b ∘ f))) ∩
          Sorted.profileRel V (fun i => γ.ρ (b i)) := by
      ext t
      rw [Set.mem_inter_iff, γ.mem_img_profile_iff hγ]
      constructor
      · rintro ⟨ht, hC'⟩
        refine ⟨?_, ht⟩
        show (t ∘ f) ∈ γ.img (C ∩ Sorted.profileRel U (b ∘ f))
        rw [γ.mem_img_profile_iff hγ]
        exact ⟨fun i => ht (f i), hC'⟩
      · rintro ⟨h1, ht⟩
        have ht'' : ∀ i, (t i).1 = γ.ρ (b i) := ht
        have h1' : (t ∘ f) ∈ γ.img (C ∩ Sorted.profileRel U (b ∘ f)) := h1
        rw [γ.mem_img_profile_iff hγ] at h1'
        obtain ⟨ht', hC'⟩ := h1'
        refine ⟨ht'', ?_⟩
        show (γ.lift hγ b t ht'' ∘ f) ∈ C
        have : γ.lift hγ b t ht'' ∘ f = γ.lift hγ (b ∘ f) (t ∘ f) ht' := by
          funext i; rfl
        rw [this]; exact hC'
    rw [this]; exact 𝒟'.inter_mem (𝒟'.reindex_mem f (hC (b ∘ f))) (𝒟'.profileRel_mem _)
  exists_mem := by
    intro n k C hC b
    have : γ.img (Sorted.exists_ U n C ∩ Sorted.profileRel U b) =
        Sorted.exists_ V (γ.ρ n) (γ.img (C ∩ Sorted.profileRel U (Fin.snoc b n))) := by
      ext t
      rw [γ.mem_img_profile_iff hγ]
      constructor
      · rintro ⟨ht, x, hx, hC'⟩
        refine ⟨γ.el x, by rw [γ.el_fst, hx], ?_⟩
        rw [γ.mem_img_profile_iff hγ]
        have ht' : ∀ i, (Fin.snoc (α := fun _ => Sorted.El V) t (γ.el x) i).1 =
            γ.ρ (Fin.snoc (α := fun _ => ℕ) b n i) := by
          intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Fin.snoc_last]; rw [γ.el_fst, hx]
          · simp only [Fin.snoc_castSucc]; exact ht i
        refine ⟨ht', ?_⟩
        have : γ.lift hγ (Fin.snoc b n) (Fin.snoc t (γ.el x)) ht' =
            Fin.snoc (α := fun _ => Sorted.El U) (γ.lift hγ b t ht) x := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Fin.snoc_last]
            refine γ.el_injective_of_sort ?_ ?_
            · rw [γ.lift_sort]; simp only [Fin.snoc_last]; exact hx.symm
            · rw [γ.el_lift]; simp only [Fin.snoc_last]
          · simp only [Fin.snoc_castSucc]
            refine γ.el_injective_of_sort ?_ ?_
            · rw [γ.lift_sort, γ.lift_sort]; simp only [Fin.snoc_castSucc]
            · rw [γ.el_lift, γ.el_lift]; simp only [Fin.snoc_castSucc]
        rw [this]; exact hC'
      · rintro ⟨y, hy, h⟩
        rw [γ.mem_img_profile_iff hγ] at h
        obtain ⟨ht', hC'⟩ := h
        have ht : ∀ i, (t i).1 = γ.ρ (b i) := fun i => by
          have := ht' (Fin.castSucc i)
          simpa using this
        refine ⟨ht, γ.lift hγ (Fin.snoc b n) (Fin.snoc t y) ht' (Fin.last k), by rw [γ.lift_sort]; simp, ?_⟩
        have : Fin.snoc (α := fun _ => Sorted.El U) (γ.lift hγ b t ht)
            (γ.lift hγ (Fin.snoc b n) (Fin.snoc t y) ht' (Fin.last k)) =
            γ.lift hγ (Fin.snoc b n) (Fin.snoc t y) ht' := by
          funext i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · simp only [Fin.snoc_last]
          · simp only [Fin.snoc_castSucc]
            refine γ.el_injective_of_sort ?_ ?_
            · rw [γ.lift_sort, γ.lift_sort]; simp only [Fin.snoc_castSucc]
            · rw [γ.el_lift, γ.el_lift]; simp only [Fin.snoc_castSucc]
        rw [this]; exact hC'
    rw [this]; exact 𝒟'.exists_mem _ (hC _)

theorem mem_baseSys_iff (𝒟' : ClassSys V) {k : ℕ} (C : Sorted.Rel U k) :
    C ∈ (γ.baseSys hγ 𝒟').D k ↔ ∀ b : Fin k → ℕ, γ.img (C ∩ Sorted.profileRel U b) ∈ 𝒟'.D k := Iff.rfl

/-- A class of `𝒟'` on the image sorts pulls back to a class of the pulled-back
system. -/
theorem pre_mem_baseSys (𝒟' : ClassSys V) {k : ℕ} (b : Fin k → ℕ) {B : Sorted.Rel V k} (hB : B ∈ 𝒟'.D k) :
    γ.pre b B ∈ (γ.baseSys hγ 𝒟').D k := by
  intro b'
  by_cases hb : b' = b
  · subst hb
    have : γ.img (γ.pre b' B ∩ Sorted.profileRel U b') = B ∩ Sorted.profileRel V (fun i => γ.ρ (b' i)) := by
      ext t
      rw [γ.mem_img_profile_iff hγ]
      constructor
      · rintro ⟨ht, -, hB'⟩
        refine ⟨?_, ht⟩
        have : (fun i => γ.el (γ.lift hγ b' t ht i)) = t := funext fun i => γ.el_lift hγ b' t ht i
        rw [this] at hB'; exact hB'
      · rintro ⟨hBt, ht⟩
        refine ⟨ht, fun i => γ.lift_sort hγ b' t ht i, ?_⟩
        show (fun i => γ.el (γ.lift hγ b' t ht i)) ∈ B
        have : (fun i => γ.el (γ.lift hγ b' t ht i)) = t := funext fun i => γ.el_lift hγ b' t ht i
        rw [this]; exact hBt
    rw [this]; exact 𝒟'.inter_mem hB (𝒟'.profileRel_mem _)
  · have : γ.img (γ.pre b B ∩ Sorted.profileRel U b') = ∅ := by
      ext t
      rw [γ.mem_img_profile_iff hγ]
      simp only [Set.mem_empty_iff_false, iff_false, not_exists]
      rintro ht ⟨hpre, -⟩
      apply hb
      funext i
      rw [← γ.lift_sort hγ b' t ht i, hpre i]
    rw [this]; exact 𝒟'.empty_mem k

end Coding

end SolidLean.Solid
