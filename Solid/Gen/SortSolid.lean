module

public import Solid.Gen.SortIso

/-!
# Solidity of definable-sort expansions

The expansion `T(𝔉, X)` of a solid clause-family theory `T(𝔉)` by definable
sorts is solid (`SortExp.solid`).  Given models `N₀ ⊳ N₁ ⊳ N₂` of the
expanded theory through interpretations `I`, `J` and an `N₀`-definable
isomorphism `N₀ ≅ N₂`, the interpretations are flattened onto the base
sorts (`flatI`, `flatJ`: the base reduct of the target, pushed along the
coding of new elements by their encodings), the isomorphism is restricted to
the base reducts, and solidity of `T(𝔉)` gives a definable isomorphism of
base reducts, which extends to the expanded models (`SortExp.extend`).

The definability bookkeeping is done through representatives: the graph of
the transferred isomorphism is a relational composition of the graph of the
original one with the code relations, and the graph of the extended
isomorphism on a new sort is a composition of the graph on the coding sort
with the encoding relations.
-/

@[expose] public section

universe u

namespace SolidLean.Solid

open Classical

namespace GenInterp

variable {U : ℕ → Type u} {𝒟 : ClassSys U} {Sig : Signature} (I : GenInterp U 𝒟 Sig)

theorem Rep_fst {y : Sorted.El U} {z : Sorted.El I.Carrier} (h : I.Rep y z) : y.1 = I.a z.1 := by
  obtain ⟨n, x, rfl, rfl⟩ := h
  rfl

theorem exists_Rep (z : Sorted.El I.Carrier) : ∃ y : Sorted.El U, I.Rep y z := by
  obtain ⟨n, q⟩ := z
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  exact ⟨Sorted.inj U x.1, n, x, rfl, rfl⟩

end GenInterp

namespace SortExp

variable {F : ClauseFamily.{u}} (X : SortExp F)

/-- Solidity of the expanded theory, in the same form as `ClauseFamily.IsSolid`. -/
def IsSolid : Prop :=
  ∀ (N : StrWithSys.{u} X.sig), X.IsModel N →
  ∀ (I : GenInterp N.M.U N.𝒟.toClassSys X.sig) (𝒩 : StrSys I.model),
    (∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩.D k → C ∈ I.induced.D k) →
    X.IsModel ⟨I.model, 𝒩⟩ →
  ∀ (J : GenInterp I.model.U 𝒩.toClassSys X.sig) (𝒬 : StrSys J.model), X.IsModel ⟨J.model, 𝒬⟩ →
  ∀ (i : GenIso N.M J.model), i.DefinableIn N.𝒟.toClassSys (I.pres.comp J.pres) →
  ∃ h : GenIso N.M I.model, h.DefinableIn N.𝒟.toClassSys I.pres

/-- Encodings are injective, on the union of sorts. -/
theorem enc_inj_el {N : StrWithSys.{u} X.sig} (hN : X.IsModel N) (m : ℕ) {z z' w : Sorted.El N.M.U}
    (hz : z.1 = nidx m) (hz' : z'.1 = nidx m)
    (h : ![z, w] ∈ N.M.rel (.enc m)) (h' : ![z', w] ∈ N.M.rel (.enc m)) : z = z' := by
  have hw : w.1 = bidx (X.σ m) := N.M.rel_sorts (.enc m) _ h 1
  obtain ⟨k, x⟩ := z
  obtain ⟨k', x'⟩ := z'
  obtain ⟨kw, xw⟩ := w
  have e1 : k = nidx m := hz
  have e2 : k' = nidx m := hz'
  have e3 : kw = bidx (X.σ m) := hw
  subst e1 e2 e3
  have := hN.enc_inj m x x' xw h h'
  rw [this]

section Transfer

variable {N₀ : StrWithSys.{u} X.sig} (hN₀ : X.IsModel N₀)
variable (I : GenInterp N₀.M.U N₀.𝒟.toClassSys X.sig)

/-- The base reduct of the interpreted model, as an interpretation in the base
reduct of the ambient model: the base target pushed along the flattening coding. -/
noncomputable def flatI : GenInterp (X.baseU N₀.M) (X.baseSys N₀.𝒟).toClassSys F.sig :=
  (I.baseTarget X).push (X.flat hN₀) (X.flat_compat hN₀)

/-- The base reduct of the interpreted model is the flattened interpretation's model. -/
noncomputable def flatIso : GenIso (X.baseStr I.model) (X.flatI hN₀ I).model :=
  (I.baseIso X).trans ((I.baseTarget X).pushIso (X.flat hN₀) (X.flat_compat hN₀))

theorem flatIso_mapEl (q : Sorted.El (X.baseU I.model)) :
    (X.flatIso hN₀ I).mapEl q = (I.baseTarget X).pushEl (X.flat hN₀) (X.flat_compat hN₀) q := rfl

@[simp] theorem flatI_a (n : ℕ) : (X.flatI hN₀ I).a n = X.flatSort (I.a (bidx n)) := rfl

/-- Representation in the flattened interpretation. -/
theorem flatI_Rep_iff (y' : Sorted.El (X.baseU N₀.M)) (q' : Sorted.El (X.flatI hN₀ I).Carrier) :
    (X.flatI hN₀ I).Rep y' q' ↔ ∃ (y : Sorted.El N₀.M.U) (z : Sorted.El (X.baseU I.model)),
      y.1 = I.a (bidx z.1) ∧ y' = (X.flat hN₀).el y ∧ q' = (X.flatIso hN₀ I).mapEl z ∧
        I.Rep y ((X.dbl I.model).el z) := by
  refine ((I.baseTarget X).push_Rep_iff' (X.flat hN₀) (X.flat_compat hN₀) y' q').trans ?_
  constructor
  · rintro ⟨y, z, hy, rfl, rfl, hR⟩
    exact ⟨y, z, hy, rfl, rfl, (I.baseTarget_Rep X y z).1 hR⟩
  · rintro ⟨y, z, hy, rfl, rfl, hR⟩
    exact ⟨y, z, hy, rfl, rfl, (I.baseTarget_Rep X y z).2 hR⟩

/-- The class system of the middle model, transported to the flattened model. -/
noncomputable def midSys (𝒩₁ : StrSys I.model) : StrSys (X.flatI hN₀ I).model :=
  (X.flatIso hN₀ I).mapSys (X.baseSys 𝒩₁)

theorem midSys_le_induced (𝒩₁ : StrSys I.model)
    (h𝒩₁ : ∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩₁.D k → C ∈ I.induced.D k) :
    ∀ k (C : Sorted.Rel (X.flatI hN₀ I).model.U k),
      C ∈ (X.midSys hN₀ I 𝒩₁).D k → C ∈ (X.flatI hN₀ I).induced.D k := by
  intro k C hC
  have hC' : {q | (fun j => (I.baseTarget X).pushEl (X.flat hN₀) (X.flat_compat hN₀) (q j)) ∈ C} ∈
      (X.baseSys 𝒩₁).D k := hC
  exact (I.baseTarget X).push_induced _ _ C (I.baseTarget_induced_of X h𝒩₁ hC')

variable {𝒩₁ : StrSys I.model} (hN₁ : X.IsModel ⟨I.model, 𝒩₁⟩)
variable (J : GenInterp I.model.U 𝒩₁.toClassSys X.sig)

/-- The base reduct of the inner model, interpreted in the base reduct of the middle model. -/
noncomputable def flatJ₁ : GenInterp (X.baseU I.model) (X.baseSys 𝒩₁).toClassSys F.sig :=
  (J.baseTarget X).push (X.flat hN₁) (X.flat_compat hN₁)

/-- The base reduct of the inner model, interpreted in the flattened middle model. -/
noncomputable def flatJ : GenInterp (X.flatI hN₀ I).model.U (X.midSys hN₀ I 𝒩₁).toClassSys F.sig :=
  (X.flatJ₁ I hN₁ J).push (Coding.ofEquiv (X.flatIso hN₀ I).equivs) (Coding.compat_mapSys _ _)

noncomputable def flatJIso : GenIso (X.baseStr J.model) (X.flatJ hN₀ I hN₁ J).model :=
  (J.baseIso X).trans (((J.baseTarget X).pushIso (X.flat hN₁) (X.flat_compat hN₁)).trans
    ((X.flatJ₁ I hN₁ J).pushIso (Coding.ofEquiv (X.flatIso hN₀ I).equivs) (Coding.compat_mapSys _ _)))

@[simp] theorem flatJ_a (n : ℕ) : (X.flatJ hN₀ I hN₁ J).a n = X.flatSort (J.a (bidx n)) := rfl

/-- Representation in the flattened inner interpretation. -/
theorem flatJ_Rep_iff (q' : Sorted.El (X.flatI hN₀ I).Carrier) (p' : Sorted.El (X.flatJ hN₀ I hN₁ J).Carrier) :
    (X.flatJ hN₀ I hN₁ J).Rep q' p' ↔ ∃ (q₀ : Sorted.El I.model.U) (p : Sorted.El (X.baseU J.model)),
      q₀.1 = J.a (bidx p.1) ∧ q' = (X.flatIso hN₀ I).mapEl ((X.flat hN₁).el q₀) ∧
        p' = (X.flatJIso hN₀ I hN₁ J).mapEl p ∧ J.Rep q₀ ((X.dbl J.model).el p) := by
  refine ((X.flatJ₁ I hN₁ J).push_Rep_iff' _ _ q' p').trans ?_
  constructor
  · rintro ⟨q, p₁, -, rfl, rfl, hR⟩
    obtain ⟨q₀, p, hq₀, rfl, rfl, hR'⟩ :=
      ((J.baseTarget X).push_Rep_iff' (X.flat hN₁) (X.flat_compat hN₁) q p₁).1 hR
    exact ⟨q₀, p, hq₀, rfl, rfl, (J.baseTarget_Rep X q₀ p).1 hR'⟩
  · rintro ⟨q₀, p, hq₀, rfl, rfl, hR⟩
    refine ⟨(X.flat hN₁).el q₀, (J.baseTarget X).pushEl _ _ p, ?_, rfl, rfl, ?_⟩
    · show X.flatSort q₀.1 = X.flatSort (J.a (bidx p.1))
      rw [hq₀]
    · exact ((J.baseTarget X).push_Rep_iff' _ _ _ _).2
        ⟨q₀, p, hq₀, rfl, rfl, (J.baseTarget_Rep X _ _).2 hR⟩

/-- Definability of the transferred isomorphism. -/
theorem transfer_definable (h𝒩₁ : ∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩₁.D k → C ∈ I.induced.D k)
    (i : GenIso N₀.M J.model) (hi : i.DefinableIn N₀.𝒟.toClassSys (I.pres.comp J.pres)) :
    ((i.base X).trans (X.flatJIso hN₀ I hN₁ J)).DefinableIn (X.baseSys N₀.𝒟).toClassSys
      ((X.flatI hN₀ I).pres.comp (X.flatJ hN₀ I hN₁ J).pres) := by
  refine (GenInterp.definableIn_comp_iff (M := X.baseStr N₀.M) (X.flatI hN₀ I) (X.flatJ hN₀ I hN₁ J)
    ((i.base X).trans (X.flatJIso hN₀ I hN₁ J))).2 fun n => ?_
  apply X.mem_baseSys_of_img
  have hi' := (I.definableIn_comp_iff J i).1 hi (bidx n)
  have hP : I.preimage ![J.a (bidx n), bidx (X.flatSort (J.a (bidx n)))]
      (X.codeRel I.model (J.a (bidx n))) ∈ N₀.𝒟.D 2 :=
    (I.mem_induced_iff _).1 (h𝒩₁ _ _ (X.codeRel_mem 𝒩₁ _)) _
  have hQ := N₀.𝒟.comp2_mem (I.a (bidx (X.flatSort (J.a (bidx n))))) hP
    (X.codeRel_mem N₀.𝒟 (I.a (bidx (X.flatSort (J.a (bidx n))))))
  have hR := N₀.𝒟.comp2_mem (I.a (J.a (bidx n))) hi' hQ
  convert hR using 1
  ext t'
  constructor
  · rintro ⟨t, ⟨h0, h1, q', hq', hI, hJ⟩, rfl⟩
    obtain ⟨y, z, hy, hty, hq'z, hRy⟩ := (X.flatI_Rep_iff hN₀ I _ _).1 hI
    obtain ⟨q₀, p, hq₀, hq'q, hp, hRq⟩ := (X.flatJ_Rep_iff hN₀ I hN₁ J _ _).1 hJ
    have hz : z = (X.flat hN₁).el q₀ := (X.flatIso hN₀ I).mapEl_injective (hq'z.symm.trans hq'q)
    have hp' : p = (i.base X).mapEl (t 0) := (X.flatJIso hN₀ I hN₁ J).mapEl_injective hp.symm
    have hzm : z.1 = X.flatSort (J.a (bidx n)) := by rw [hq'z] at hq'; exact hq'
    have hpn : p.1 = n := by rw [hp']; exact h0
    have hq₀n : q₀.1 = J.a (bidx n) := by rw [hq₀, hpn]
    obtain ⟨s₀, hs₀⟩ := I.exists_Rep q₀
    have hs₀n : s₀.1 = I.a (J.a (bidx n)) := by rw [I.Rep_fst hs₀, hq₀n]
    refine ⟨s₀, hs₀n, ⟨?_, hs₀n, q₀, hq₀n, hs₀, ?_⟩, y, ?_, ⟨![q₀, (X.dbl I.model).el z], fun j => ?_, ?_⟩, ?_⟩
    · show bidx (t 0).1 = bidx n
      rw [h0]
    · show J.Rep q₀ (i.mapEl ((X.dbl N₀.M).el (t 0)))
      rw [← GenIso.dbl_base_mapEl, ← hp']
      exact hRq
    · rw [hy, hzm]
    · match j with
      | 0 => exact ⟨hq₀n, hs₀⟩
      | 1 =>
        refine ⟨?_, hRy⟩
        show bidx z.1 = bidx (X.flatSort (J.a (bidx n)))
        rw [hzm]
    · show ![q₀, (X.dbl I.model).el z] ∈ X.codeRel I.model (J.a (bidx n))
      rw [← hq₀n]
      exact (X.mem_codeRel_iff hN₁ q₀ _).2 (by rw [hz])
    · show ![y, (X.dbl N₀.M).el (t 1)] ∈ X.codeRel N₀.M (I.a (bidx (X.flatSort (J.a (bidx n)))))
      rw [← hzm, ← hy]
      exact (X.mem_codeRel_iff hN₀ y _).2 (by rw [hty])
  · rintro ⟨s₀, hs₀, ⟨h0, -, q₀, hq₀, hs₀q, hJq⟩, y₀, hy₀, ⟨u, hu, hu'⟩, hcode₀⟩
    have hu0 : u 0 = q₀ := I.Rep_unique (hu 0).2 hs₀q ((hu 0).1.trans hq₀.symm)
    have hu'' : ![q₀, u 1] ∈ X.codeRel I.model q₀.1 := by
      have e : u = ![u 0, u 1] := by
        funext j
        match j with
        | 0 => rfl
        | 1 => rfl
      rw [e, hu0] at hu'
      rw [hq₀]; exact hu'
    have hw : u 1 = (X.dbl I.model).el ((X.flat hN₁).el q₀) := (X.mem_codeRel_iff hN₁ q₀ _).1 hu''
    have hcode₀' : ![y₀, t' 1] ∈ X.codeRel N₀.M y₀.1 := by rw [hy₀]; exact hcode₀
    have ht1 : t' 1 = (X.dbl N₀.M).el ((X.flat hN₀).el y₀) := (X.mem_codeRel_iff hN₀ y₀ _).1 hcode₀'
    obtain ⟨x, hx⟩ : ∃ x : N₀.M.U (bidx n), t' 0 = (X.dbl N₀.M).el ⟨n, x⟩ :=
      ⟨Sorted.toSort N₀.M.U (t' 0) h0, (Sorted.inj_toSort N₀.M.U (t' 0) h0).symm⟩
    refine ⟨![⟨n, x⟩, (X.flat hN₀).el y₀], ⟨rfl, ?_, (X.flatIso hN₀ I).mapEl ((X.flat hN₁).el q₀), ?_, ?_, ?_⟩, ?_⟩
    · show X.flatSort y₀.1 = X.flatSort (I.a (bidx (X.flatSort (J.a (bidx n)))))
      rw [hy₀]
    · show X.flatSort q₀.1 = X.flatSort (J.a (bidx n))
      rw [hq₀]
    · refine (X.flatI_Rep_iff hN₀ I _ _).2 ⟨y₀, (X.flat hN₁).el q₀, ?_, rfl, rfl, ?_⟩
      · show y₀.1 = I.a (bidx (X.flatSort q₀.1))
        rw [hy₀, hq₀]
      · rw [← hw]; exact (hu 1).2
    · refine (X.flatJ_Rep_iff hN₀ I hN₁ J _ _).2 ⟨q₀, (i.base X).mapEl ⟨n, x⟩, hq₀, rfl, rfl, ?_⟩
      show J.Rep q₀ (i.mapEl ((X.dbl N₀.M).el ⟨n, x⟩))
      rw [← hx]
      exact hJq
    · funext j
      match j with
      | 0 => exact hx
      | 1 => exact ht1

end Transfer

section Conclude

variable {N₀ : StrWithSys.{u} X.sig} (hN₀ : X.IsModel N₀)
variable (I : GenInterp N₀.M.U N₀.𝒟.toClassSys X.sig)
variable {𝒩₁ : StrSys I.model} (hN₁ : X.IsModel ⟨I.model, 𝒩₁⟩)

/-- On a base sort, the graph of the extension of a definable isomorphism of
base reducts is admissible: it is the composition of the flattened graph with
the code relation. -/
theorem repGraph_bidx_mem (h' : GenIso (X.baseStr N₀.M) (X.flatI hN₀ I).model)
    (hh' : h'.DefinableIn (X.baseSys N₀.𝒟).toClassSys (X.flatI hN₀ I).pres) (n : ℕ) :
    I.repGraph (X.extend hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm)) (bidx n) ∈ N₀.𝒟.D 2 := by
  have hh'n := ((X.flatI hN₀ I).definableIn_pres_iff (M := X.baseStr N₀.M) h').1 hh' n
  have hR : (X.dbl N₀.M).img ((X.flatI hN₀ I).repGraph (M := X.baseStr N₀.M) h' n) ∈ N₀.𝒟.D 2 := by
    have := hh'n ![n, (X.flatI hN₀ I).a n]
    have e : (X.flatI hN₀ I).repGraph (M := X.baseStr N₀.M) h' n ∩
        Sorted.profileRel (X.baseU N₀.M) ![n, (X.flatI hN₀ I).a n] =
          (X.flatI hN₀ I).repGraph (M := X.baseStr N₀.M) h' n := by
      apply Set.inter_eq_left.2
      rintro t ⟨h0, h1, -⟩ j
      match j with
      | 0 => exact h0
      | 1 => exact h1
    have e2 : (X.dbl N₀.M).img ((X.flatI hN₀ I).repGraph (M := X.baseStr N₀.M) h' n ∩
        Sorted.profileRel (X.baseU N₀.M) ![n, (X.flatI hN₀ I).a n]) =
          (X.dbl N₀.M).img ((X.flatI hN₀ I).repGraph (M := X.baseStr N₀.M) h' n) :=
      congrArg (fun A : Sorted.Rel (X.baseU N₀.M) 2 => (X.dbl N₀.M).img A) e
    exact Eq.mp (congrArg (· ∈ N₀.𝒟.D 2) e2) this
  have hC := N₀.𝒟.comp2_mem (bidx ((X.flatI hN₀ I).a n)) hR
    (N₀.𝒟.converse_mem (X.codeRel_mem N₀.𝒟 (I.a (bidx n))))
  have hfinal := N₀.𝒟.inter_mem (N₀.𝒟.profileRel_mem ![bidx n, I.a (bidx n)]) hC
  convert hfinal using 1
  ext t
  constructor
  · rintro ⟨h0, h1, hrep⟩
    obtain ⟨x, hx⟩ : ∃ x : N₀.M.U (bidx n), t 0 = (X.dbl N₀.M).el ⟨n, x⟩ :=
      ⟨Sorted.toSort N₀.M.U (t 0) h0, (Sorted.inj_toSort N₀.M.U (t 0) h0).symm⟩
    refine ⟨fun j => ?_, (X.dbl N₀.M).el ((X.flat hN₀).el (t 1)), ?_,
      ⟨![⟨n, x⟩, (X.flat hN₀).el (t 1)], ⟨rfl, ?_, ?_⟩, ?_⟩, ?_⟩
    · match j with
      | 0 => exact h0
      | 1 => exact h1
    · show bidx (X.flatSort (t 1).1) = bidx (X.flatSort (I.a (bidx n)))
      rw [h1]
    · show X.flatSort (t 1).1 = X.flatSort (I.a (bidx n))
      rw [h1]
    · have e : h'.mapEl ⟨n, x⟩ =
          (X.flatIso hN₀ I).mapEl ((h'.trans (X.flatIso hN₀ I).symm).mapEl ⟨n, x⟩) := by
        rw [GenIso.trans_mapEl, GenIso.mapEl_symm_apply]
      show (X.flatI hN₀ I).Rep ((X.flat hN₀).el (t 1)) (h'.mapEl ⟨n, x⟩)
      rw [e]
      refine (X.flatI_Rep_iff hN₀ I _ _).2 ⟨t 1, _, h1, rfl, rfl, ?_⟩
      have e2 : (X.dbl I.model).el ((h'.trans (X.flatIso hN₀ I).symm).mapEl ⟨n, x⟩) =
          (X.extend hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm)).mapEl ((X.dbl N₀.M).el ⟨n, x⟩) :=
        (X.extend_mapEl_dbl hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm) ⟨n, x⟩).symm
      rw [e2, ← hx]
      exact hrep
    · funext j
      match j with
      | 0 => exact hx
      | 1 => rfl
    · show ![t 1, (X.dbl N₀.M).el ((X.flat hN₀).el (t 1))] ∈ X.codeRel N₀.M (I.a (bidx n))
      rw [← h1]
      exact (X.mem_codeRel_iff hN₀ (t 1) _).2 rfl
  · rintro ⟨hprof, c, -, ⟨s, ⟨hs0, -, hrep'⟩, hsc⟩, hcode⟩
    have ht0 : t 0 = (X.dbl N₀.M).el (s 0) := congrFun hsc 0
    have hc : c = (X.dbl N₀.M).el (s 1) := congrFun hsc 1
    obtain ⟨y, z, hy, hs1y, hz, hRy⟩ := (X.flatI_Rep_iff hN₀ I _ _).1 hrep'
    have hz' : z = (h'.trans (X.flatIso hN₀ I).symm).mapEl (s 0) := by
      apply (X.flatIso hN₀ I).mapEl_injective
      have e3 : (h'.trans (X.flatIso hN₀ I).symm).mapEl (s 0) =
          (X.flatIso hN₀ I).symm.mapEl (h'.mapEl (s 0)) := rfl
      rw [← hz, e3, GenIso.mapEl_symm_apply]
      rfl
    have hz1 : z.1 = n := by rw [hz']; exact hs0
    have hcode' : ![t 1, c] ∈ X.codeRel N₀.M (t 1).1 := by rw [hprof 1]; exact hcode
    have hc' : c = (X.dbl N₀.M).el ((X.flat hN₀).el (t 1)) := (X.mem_codeRel_iff hN₀ (t 1) c).1 hcode'
    have hyt : y = t 1 := by
      apply (X.flat hN₀).el_injective_of_sort
      · rw [hy, hz1, hprof 1]
        rfl
      · apply X.dbl_el_injective
        rw [← hc', hc, hs1y]
    refine ⟨hprof 0, hprof 1, ?_⟩
    have e2 : (X.extend hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm)).mapEl ((X.dbl N₀.M).el (s 0)) =
        (X.dbl I.model).el ((h'.trans (X.flatIso hN₀ I).symm).mapEl (s 0)) :=
      X.extend_mapEl_dbl hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm) (s 0)
    rw [← hyt, ht0, e2, ← hz']
    exact hRy

include hN₀ hN₁ in
/-- On a new sort, the graph of an isomorphism is admissible once it is on
the coding sort: it is the composition of the encoding, the graph on the
coding sort and the (interpreted) encoding. -/
theorem repGraph_nidx_mem (h : GenIso N₀.M I.model)
    (h𝒩₁ : ∀ k (C : Sorted.Rel I.model.U k), C ∈ 𝒩₁.D k → C ∈ I.induced.D k)
    (hbase : ∀ n, I.repGraph h (bidx n) ∈ N₀.𝒟.D 2) (m : ℕ) :
    I.repGraph h (nidx m) ∈ N₀.𝒟.D 2 := by
  have hP : I.preimage ![nidx m, bidx (X.σ m)] (I.model.rel (.enc m)) ∈ N₀.𝒟.D 2 :=
    (I.mem_induced_iff _).1 (h𝒩₁ _ _ (𝒩₁.rel_mem (.enc m))) _
  have hS := N₀.𝒟.comp2_mem (I.a (bidx (X.σ m))) (hbase (X.σ m)) (N₀.𝒟.converse_mem hP)
  have hC := N₀.𝒟.comp2_mem (bidx (X.σ m)) (N₀.𝒟.rel_mem (.enc m)) hS
  have hfinal := N₀.𝒟.inter_mem (N₀.𝒟.profileRel_mem ![nidx m, I.a (nidx m)]) hC
  convert hfinal using 1
  ext t
  constructor
  · rintro ⟨h0, h1, hrep⟩
    obtain ⟨z, hz⟩ : ∃ z : N₀.M.U (nidx m), t 0 = Sorted.inj N₀.M.U z :=
      ⟨Sorted.toSort N₀.M.U (t 0) h0, (Sorted.inj_toSort N₀.M.U (t 0) h0).symm⟩
    obtain ⟨s₁, hs₁⟩ := I.exists_Rep (h.mapEl (Sorted.inj N₀.M.U (X.encFun hN₀ m z)))
    have henc : ![t 0, Sorted.inj N₀.M.U (X.encFun hN₀ m z)] ∈ N₀.M.rel (.enc m) := by
      rw [hz]; exact X.encFun_spec hN₀ m z
    have henc' : ![h.mapEl (t 0), h.mapEl (Sorted.inj N₀.M.U (X.encFun hN₀ m z))] ∈
        I.model.rel (.enc m) := by
      have this : (fun j => h.mapEl (![t 0, Sorted.inj N₀.M.U (X.encFun hN₀ m z)] j)) ∈
        I.model.rel (.enc m) := (h.rel_iff (.enc m) _).1 henc
      have e : (fun j => h.mapEl (![t 0, Sorted.inj N₀.M.U (X.encFun hN₀ m z)] j)) =
          ![h.mapEl (t 0), h.mapEl (Sorted.inj N₀.M.U (X.encFun hN₀ m z))] := by
        funext j
        match j with
        | 0 => rfl
        | 1 => rfl
      rw [e] at this; exact this
    refine ⟨fun j => ?_, Sorted.inj N₀.M.U (X.encFun hN₀ m z), rfl, henc, s₁, I.Rep_fst hs₁,
      ⟨rfl, I.Rep_fst hs₁, hs₁⟩,
      ![h.mapEl (t 0), h.mapEl (Sorted.inj N₀.M.U (X.encFun hN₀ m z))], fun j => ?_, henc'⟩
    · match j with
      | 0 => exact h0
      | 1 => exact h1
    · match j with
      | 0 => exact ⟨h0, hrep⟩
      | 1 => exact ⟨rfl, hs₁⟩
  · rintro ⟨hprof, c₀, hc₀, henc, s₁, -, ⟨-, -, hrep₁⟩, u, hu, hu'⟩
    have hu1 : u 1 = h.mapEl c₀ := I.Rep_unique (hu 1).2 hrep₁ ((hu 1).1.trans hc₀.symm)
    have henc' : ![h.mapEl (t 0), h.mapEl c₀] ∈ I.model.rel (.enc m) := by
      have this : (fun j => h.mapEl (![t 0, c₀] j)) ∈ I.model.rel (.enc m) :=
        (h.rel_iff (.enc m) _).1 henc
      have e : (fun j => h.mapEl (![t 0, c₀] j)) = ![h.mapEl (t 0), h.mapEl c₀] := by
        funext j
        match j with
        | 0 => rfl
        | 1 => rfl
      rw [e] at this; exact this
    have hu'' : ![u 0, h.mapEl c₀] ∈ I.model.rel (.enc m) := by
      have e : u = ![u 0, u 1] := by
        funext j
        match j with
        | 0 => rfl
        | 1 => rfl
      rw [e, hu1] at hu'; exact hu'
    have hu0 : u 0 = h.mapEl (t 0) := X.enc_inj_el hN₁ m (hu 0).1 (hprof 0) hu'' henc'
    refine ⟨hprof 0, hprof 1, ?_⟩
    rw [← hu0]; exact (hu 0).2

end Conclude

/-- **Definable-sort expansions of solid clause-family theories are solid.** -/
theorem solid : X.IsSolid := by
  intro N₀ hN₀ I 𝒩₁ h𝒩₁ hN₁ J 𝒩₂ hN₂ i hi
  obtain ⟨h', hh'⟩ := F.solid ⟨X.baseStr N₀.M, X.baseSys N₀.𝒟⟩ hN₀.base (X.flatI hN₀ I)
    (X.midSys hN₀ I 𝒩₁) (X.midSys_le_induced hN₀ I 𝒩₁ h𝒩₁)
    (ClauseFamily.IsGenModel.transport (X.flatIso hN₀ I) hN₁.base)
    (X.flatJ hN₀ I hN₁ J) ((X.flatJIso hN₀ I hN₁ J).mapSys (X.baseSys 𝒩₂))
    (ClauseFamily.IsGenModel.transport (X.flatJIso hN₀ I hN₁ J) hN₂.base)
    ((i.base X).trans (X.flatJIso hN₀ I hN₁ J)) (X.transfer_definable hN₀ I hN₁ J h𝒩₁ i hi)
  refine ⟨X.extend hN₀ hN₁ (h'.trans (X.flatIso hN₀ I).symm), ?_⟩
  refine (I.definableIn_pres_iff (M := N₀.M) _).2 fun k => ?_
  by_cases hk : k % 2 = 0
  · obtain ⟨n, rfl⟩ : ∃ n, k = bidx n := ⟨k / 2, eq_bidx_of_even hk⟩
    exact X.repGraph_bidx_mem hN₀ I hN₁ h' hh' n
  · obtain ⟨m, rfl⟩ : ∃ m, k = nidx m := ⟨k / 2, eq_nidx_of_odd hk⟩
    exact X.repGraph_nidx_mem hN₀ I hN₁ _ h𝒩₁ (X.repGraph_bidx_mem hN₀ I hN₁ h' hh') m

end SortExp

end SolidLean.Solid
