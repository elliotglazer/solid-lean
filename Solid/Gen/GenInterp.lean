import Solid.Gen.Signature

/-!
# One-coordinate interpretations of a relational signature

A `GenInterp U 𝒟 Sig` interprets the signature `Sig` in the sorted carrier
`U` with class system `𝒟`: each sort by a definable class of one source
sort modulo a definable equivalence (`SortInterp`), each relation symbol by a
definable class of source tuples respecting the equivalences.  The
interpreted structure `model : Str Sig` carries the induced class system
(`induced : StrSys model`).
-/

universe u

namespace SolidLean.Solid

open Classical

/-- A one-coordinate interpretation of `Sig` in `(U, 𝒟)`. -/
structure GenInterp (U : ℕ → Type u) (𝒟 : ClassSys U) (Sig : Signature)
    extends SortInterp U 𝒟 where
  relC : ∀ r, Sorted.Rel U (Sig.arity r)
  relC_dom : ∀ r t, t ∈ relC r → ∀ i, ∃ x : U (a (Sig.sortAt r i)),
    t i = Sorted.inj U x ∧ x ∈ dom (Sig.sortAt r i)
  relC_congr : ∀ r (t t' : Fin (Sig.arity r) → Sorted.El U),
    (∀ i, ∃ x x' : U (a (Sig.sortAt r i)), t i = Sorted.inj U x ∧ t' i = Sorted.inj U x' ∧
      eqv (Sig.sortAt r i) x x') → t ∈ relC r → t' ∈ relC r
  relC_def : ∀ r, relC r ∈ 𝒟.D (Sig.arity r)

namespace GenInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} {Sig : Signature} (I : GenInterp U 𝒟 Sig)

/-- The interpreted relation: tuples of classes of a tuple in `relC`. -/
def relQ (r : Sig.Rel) : Sorted.Rel I.Carrier (Sig.arity r) :=
  {t | ∃ u : Fin (Sig.arity r) → Sorted.El U,
    (∀ i, (t i).1 = Sig.sortAt r i ∧ I.Rep (u i) (t i)) ∧ u ∈ I.relC r}

/-- The interpreted structure. -/
noncomputable def model : Str.{u} Sig where
  U := I.Carrier
  rel := I.relQ
  rel_sorts := by
    rintro r t ⟨u, hu, -⟩ i
    exact (hu i).1

@[simp] theorem model_U : I.model.U = I.Carrier := rfl

/-- Two representatives of the same class are equivalent. -/
theorem Rep_eqv {y y' : Sorted.El U} {z : Sorted.El I.Carrier} {n : ℕ} (hz : z.1 = n)
    (h : I.Rep y z) (h' : I.Rep y' z) :
    ∃ x x' : U (I.a n), y = Sorted.inj U x ∧ y' = Sorted.inj U x' ∧ I.eqv n x x' := by
  obtain ⟨n₀, x, rfl, rfl⟩ := h
  obtain ⟨n', x', rfl, hz'⟩ := h'
  have hn : n₀ = n' := congrArg Sigma.fst hz'
  subst hn
  have hn' : n₀ = n := hz
  subst hn'
  exact ⟨x, x', rfl, rfl, (I.cls_eq_iff _ _).1 ((I.model_inj_eq_iff _ _).1 hz')⟩

theorem preimage_relQ (r : Sig.Rel) (b : Fin (Sig.arity r) → ℕ) :
    I.preimage b (I.relQ r) =
      if (∀ i, b i = Sig.sortAt r i) then I.relC r ∩ I.profile b else ∅ := by
  ext t
  by_cases h : ∀ i, b i = Sig.sortAt r i
  · rw [if_pos h]
    constructor
    · rintro ⟨u, hu, u', hu', hrel⟩
      refine ⟨?_, fun i => ⟨u i, (hu i).1, (hu i).2⟩⟩
      refine I.relC_congr r u' t (fun i => ?_) hrel
      obtain ⟨x, x', hx, hx', heqv⟩ := I.Rep_eqv (hu' i).1 (hu' i).2 (hu i).2
      exact ⟨x, x', hx, hx', heqv⟩
    · rintro ⟨hrel, hp⟩
      refine ⟨fun i => Sorted.inj I.Carrier (n := Sig.sortAt r i)
        (I.cls ⟨Classical.choose (I.relC_dom r t hrel i),
          (Classical.choose_spec (I.relC_dom r t hrel i)).2⟩), fun i => ⟨(h i).symm, ?_⟩, ?_⟩
      · refine ⟨Sig.sortAt r i, _, (Classical.choose_spec (I.relC_dom r t hrel i)).1, rfl⟩
      · exact ⟨t, fun i => ⟨rfl, Sig.sortAt r i, _,
          (Classical.choose_spec (I.relC_dom r t hrel i)).1, rfl⟩, hrel⟩
  · rw [if_neg h]
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, u', hu', -⟩
    apply h
    intro i
    rw [← (hu i).1, (hu' i).1]

/-- The relation atoms of the interpreted structure are admissible. -/
theorem relQ_atom (r : Sig.Rel) : I.relQ r ∈ I.inducedD (Sig.arity r) := by
  intro b
  rw [I.preimage_relQ]
  split_ifs
  · exact 𝒟.inter_mem (I.relC_def r) (I.profile_mem b)
  · exact 𝒟.empty_mem _

/-- The induced class system on the interpreted structure. -/
noncomputable def induced : StrSys I.model where
  toClassSys := I.inducedSys
  rel_mem := I.relQ_atom

/-- The interpreted structure with its induced class system. -/
noncomputable def asModel : StrWithSys.{u} Sig := ⟨I.model, I.induced⟩

theorem mem_induced_iff {k : ℕ} (C : Sorted.Rel I.Carrier k) :
    C ∈ I.induced.D k ↔ ∀ b : Fin k → ℕ, I.preimage b C ∈ 𝒟.D k := Iff.rfl

/-- Membership in the interpreted relation, for a tuple of classes. -/
theorem mem_relQ_cls_iff (r : Sig.Rel) (x : (i : Fin (Sig.arity r)) → I.Dom (Sig.sortAt r i)) :
    (fun i => Sorted.inj I.Carrier (n := Sig.sortAt r i) (I.cls (x i))) ∈ I.relQ r ↔
      (fun i => Sorted.inj U (x i).1) ∈ I.relC r := by
  constructor
  · rintro ⟨u, hu, hrel⟩
    refine I.relC_congr r u _ (fun i => ?_) hrel
    obtain ⟨y, y', hy, hy', heqv⟩ := I.Rep_eqv (hu i).1 (hu i).2 ⟨Sig.sortAt r i, x i, rfl, rfl⟩
    exact ⟨y, y', hy, hy', heqv⟩
  · intro hrel
    exact ⟨fun i => Sorted.inj U (x i).1, fun i => ⟨rfl, Sig.sortAt r i, x i, rfl, rfl⟩, hrel⟩

end GenInterp

end SolidLean.Solid
