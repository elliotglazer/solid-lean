module

public import Solid.Calc.Sets
public import Solid.Calc.PrimRel

/-!
# The sets the primitives need, in a model of `H`

Successors and ω in sort `1`, the Σ- and Sum-sets, lifting of universe
membership, quotient sets and classes, and the recursion theorem for the
natural numbers eliminator, in the sort models of a tower model.
-/

@[expose] public section

universe u

open Classical

namespace SolidLean.Solid.SetClassSystem.Def

variable {S : MemStr.{u}} {𝒞 : SetClassSystem S}

theorem isInductive {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsInductive (t i)) := by
  unfold MemStr.IsInductive
  refine and_ ?_ ?_
  · refine congr ?_ (exists_ (and_ (isEmptySet (Fin.last k)) (mem (Fin.last k) (Fin.castSucc i))))
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]
  · refine congr ?_ (forall_ (imp_ (mem (Fin.last k) (Fin.castSucc i)) (exists_ (and_
      (isSucc (Fin.castSucc (Fin.last k)) (Fin.last (k + 1))) (mem (Fin.last (k + 1)) (Fin.castSucc (Fin.castSucc i)))))))
    intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem isOmega {k : ℕ} (i : Fin k) : 𝒞.Def k (fun t => S.IsOmega (t i)) := by
  unfold MemStr.IsOmega
  refine congr ?_ (forall_ (iff_ (mem (Fin.last k) (Fin.castSucc i)) (forall_ (imp_
    (isInductive (Fin.last (k + 1))) (mem (Fin.castSucc (Fin.last k)) (Fin.last (k + 1)))))))
  intro t; simp only [Fin.snoc_castSucc, Fin.snoc_last]

end SolidLean.Solid.SetClassSystem.Def

namespace SolidLean.Solid.IsTowerModel

open SolidLean.Solid

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### Elementary facts -/

include hM in
theorem succ_unique {n : ℕ} {x s s' : M.T.U n} (h : (M.T.sortStr n).IsSucc x s)
    (h' : (M.T.sortStr n).IsSucc x s') : s = s' :=
  hM.ext_of_iff h h'

theorem liftLE_emptyAt {m n : ℕ} (h : m ≤ n) : M.T.liftLE h (hM.emptyAt m) = hM.emptyAt n :=
  hM.eq_emptyAt (((hM.liftEmb h).isEmptySet_iff _).2 (hM.emptyAt_spec m))

theorem liftLE_singAt {m n : ℕ} (h : m ≤ n) (a : M.T.U m) :
    M.T.liftLE h (hM.singAt a) = hM.singAt (M.T.liftLE h a) :=
  hM.eq_singAt (((hM.liftEmb h).isSingleton_iff a _).2 (hM.singAt_spec a))

/-- Types lift to types: a `j`-image in `U_i` lifted by `d` is in `U_{i+d}`. -/
theorem mem_univSet_lift {i : ℕ} (vA : M.T.U (i + 1)) (h : M.T.mem (M.T.j (i + 1) vA) (hM.univSet i))
    (d : ℕ) : M.T.mem (M.T.j (i + d + 1) (M.T.liftLE (by omega) vA)) (hM.univSet (i + d)) := by
  induction d with
  | zero => rw [MemTower.liftLE_self]; exact h
  | succ d _ =>
    rw [M.T.liftLE_succ (by omega : i + 1 ≤ i + d + 1)]
    exact hM.j_j_mem_univSet_succ (i + d) _

include hM in
/-- Elements of a lifted type are lifts. -/
theorem mem_liftLE_elim {a b : ℕ} (h : a ≤ b) {x : M.T.U a} {z : M.T.U b}
    (hz : M.T.mem z (M.T.liftLE h x)) : ∃ y, M.T.mem y x ∧ M.T.liftLE h y = z :=
  (hM.mem_liftLE_iff h x z).1 hz

/-! ### Successors and ω in sort `1` -/

include hM in
theorem exists_omega : ∃ o : M.T.U 1, (M.T.sortStr 1).IsOmega o := by
  obtain ⟨I, hI0, hIs⟩ := (hM.zfc 1).infinity
  have hdef : (hM.sortModel 1).𝒞.Def 1 (fun t => ∀ J, (M.T.sortStr 1).IsInductive J → M.T.mem (t 0) J) := by
    refine SetClassSystem.Def.congr (fun t => ?_) (SetClassSystem.Def.forall_
      (SetClassSystem.Def.imp_ (SetClassSystem.Def.isInductive 1) (SetClassSystem.Def.mem 0 1)))
    simp only [Fin.snocL_1_0, Fin.snocL_1_1]
  obtain ⟨o, ho⟩ := (hM.sortModel 1).sepP
    (P := fun x => ∀ J, (M.T.sortStr 1).IsInductive J → M.T.mem x J) hdef I
  refine ⟨o, fun z => ?_⟩
  rw [ho z]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨h I ⟨hI0, hIs⟩, h⟩

/-- ω, as a set of sort `1`. -/
noncomputable def omegaSet : M.T.U 1 := Classical.choose hM.exists_omega

theorem isOmega_omegaSet : (M.T.sortStr 1).IsOmega hM.omegaSet := Classical.choose_spec hM.exists_omega

theorem isOmega_unique {o : M.T.U 1} (h : (M.T.sortStr 1).IsOmega o) : o = hM.omegaSet :=
  hM.ext_of_iff h hM.isOmega_omegaSet

theorem mem_omega_iff (z : M.T.U 1) :
    M.T.mem z hM.omegaSet ↔ ∀ J, (M.T.sortStr 1).IsInductive J → M.T.mem z J :=
  hM.isOmega_omegaSet z

theorem emptyAt_mem_omega : M.T.mem (hM.emptyAt 1) hM.omegaSet := by
  rw [hM.mem_omega_iff]
  intro J hJ
  obtain ⟨e, he, heJ⟩ := hJ.1
  rw [hM.eq_emptyAt he] at heJ
  exact heJ

theorem succ_mem_omega {k s : M.T.U 1} (hk : M.T.mem k hM.omegaSet) (hs : (M.T.sortStr 1).IsSucc k s) :
    M.T.mem s hM.omegaSet := by
  rw [hM.mem_omega_iff] at hk ⊢
  intro J hJ
  obtain ⟨s', hs', hs'J⟩ := hJ.2 k (hk J hJ)
  rw [hM.succ_unique hs hs']
  exact hs'J

theorem isInductive_omega : (M.T.sortStr 1).IsInductive hM.omegaSet :=
  ⟨⟨_, hM.emptyAt_spec 1, hM.emptyAt_mem_omega⟩, fun k hk =>
    let ⟨s, hs⟩ := (hM.sortModel 1).exists_succ k
    ⟨s, hs, hM.succ_mem_omega hk hs⟩⟩

/-- Induction over ω for a definable predicate of sort `1`. -/
theorem omega_induction {P : M.T.U 1 → Prop} (hP : (hM.sortModel 1).𝒞.Def 1 (fun t => P (t 0)))
    (h0 : ∀ e, (M.T.sortStr 1).IsEmptySet e → P e)
    (hs : ∀ k, M.T.mem k hM.omegaSet → P k → ∀ s, (M.T.sortStr 1).IsSucc k s → P s) :
    ∀ k, M.T.mem k hM.omegaSet → P k := by
  obtain ⟨S, hS⟩ := (hM.sortModel 1).sepP hP hM.omegaSet
  have hSind : (M.T.sortStr 1).IsInductive S := by
    refine ⟨⟨_, hM.emptyAt_spec 1, (hS _).2 ⟨hM.emptyAt_mem_omega, h0 _ (hM.emptyAt_spec 1)⟩⟩,
      fun k hk => ?_⟩
    obtain ⟨hkω, hPk⟩ := (hS k).1 hk
    obtain ⟨s, hs'⟩ := (hM.sortModel 1).exists_succ k
    exact ⟨s, hs', (hS s).2 ⟨hM.succ_mem_omega hkω hs', hs k hkω hPk s hs'⟩⟩
  intro k hk
  exact ((hS k).1 ((hM.mem_omega_iff k).1 hk S hSind)).2

/-- Elements of ω are transitive. -/
theorem omega_transitive : ∀ k, M.T.mem k hM.omegaSet → (M.T.sortStr 1).Transitive k := by
  refine hM.omega_induction (SetClassSystem.Def.transitive 0) (fun e he => ?_) (fun k _ hk s hs => ?_)
  · intro y hy; exact absurd hy (he y)
  · intro y hy z hz
    rcases (hs y).1 hy with hyk | rfl
    · exact (hs z).2 (Or.inl (hk y hyk z hz))
    · exact (hs z).2 (Or.inl hz)

/-- ω is transitive. -/
theorem omega_trans_set : (M.T.sortStr 1).Transitive hM.omegaSet := by
  have : ∀ k, M.T.mem k hM.omegaSet → (M.T.sortStr 1).Subset k hM.omegaSet := by
    refine hM.omega_induction ?_ (fun e he => ?_) (fun k hk ih s hs => ?_)
    · refine SetClassSystem.Def.congr (fun t => ?_)
        ((SetClassSystem.Def.subset 0 1).withParam hM.omegaSet)
      simp only [Fin.snocL_1_0, Fin.snocL_1_1]
    · intro y hy; exact absurd hy (he y)
    · intro y hy
      rcases (hs y).1 hy with hyk | rfl
      · exact ih y hyk
      · exact hk
  exact this

theorem mem_omega_of_mem {k n : M.T.U 1} (hn : M.T.mem n hM.omegaSet) (hk : M.T.mem k n) :
    M.T.mem k hM.omegaSet :=
  hM.omega_trans_set n hn k hk

end SolidLean.Solid.IsTowerModel

namespace SolidLean.Calc

open SolidLean.Solid SolidLean.Solid.TF

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

/-! ### Sort-definability of tower formulas with parameters, binary version -/

open SolidLean.Solid.ClassSystem in
theorem sortDef_sat2 {k n : ℕ} {s : Fin (k + 2) → ℕ} (φ : TF (k + 2) s) (params : Fin k → M.T.El) :
    (M.𝒟.sortSystem n).Def 2 (fun u => φ.Sat M.T.toStr
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) params (M.T.inj (u 0)))
        (M.T.inj (u 1)))) := by
  refine TDef.toDef2 (s := n) (P := fun z w => φ.Sat M.T.toStr
    (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) params (M.T.inj z)) (M.T.inj w)))
    (TDef.congr (fun t => ?_) (TDef.and_ (TDef.sort 0 n) (TDef.and_ (TDef.sort 1 n)
      (TDef.fixInit (m := k) (k := 2) (TDef_sat M.𝒟 φ) params))))
  show (t 0).1 = n ∧ (t 1).1 = n ∧ φ.Sat M.T.toStr (Fin.append params t) ↔ _
  rw [append_two params t]
  constructor
  · rintro ⟨h0, h1, h⟩
    obtain ⟨z, hz⟩ := elSort M.T (t 0) h0
    obtain ⟨w, hw⟩ := elSort M.T (t 1) h1
    exact ⟨z, w, hz, hw, by rw [← hz, ← hw]; exact h⟩
  · rintro ⟨z, w, hz, hw, h⟩
    exact ⟨by rw [hz], by rw [hw], by rw [hz, hw]; exact h⟩

/-- The empty environment. -/
def env0 : Fin 0 → M.T.El := fun l => l.elim0

/-! ### Σ-sets and Sum-sets -/

section SigmaSum

variable {i j : ℕ}

/-- The codomain relation of a family value `vB`: `x = lift a` and `y = lift B(a)'`, where
`vB(lift a) = lift (j B(a)')`. -/
def SigmaCodRel (vB : M.T.U (max i (j + 1))) (x y : M.T.U (max i j)) : Prop :=
  ∃ a : M.T.U i, x = M.T.liftLE (le_max_left i j) a ∧ ∃ v : M.T.U (max i (j + 1)),
    (M.T.sortStr (max i (j + 1))).FunApp vB (M.T.liftLE (le_max_left _ _) a) v ∧
    ∃ vBa : M.T.U (j + 1), v = M.T.liftLE (le_max_right _ _) vBa ∧
    ∃ vBa' : M.T.U j, vBa = M.T.j j vBa' ∧ y = M.T.liftLE (le_max_right i j) vBa'

/-- `SigmaCodRel` as a tower formula (layout `B x y | a u v vBa vBa'`). -/
def sigmaCodF (i j : ℕ) : TF 3 ![max i (j + 1), max i j, max i j] :=
  .ex i (Formula.and (liftLEF i (max i j) (le_max_left _ _) 3 1 (by exact id rfl) (by exact id rfl))
    (.ex (max i (j + 1)) (Formula.and (liftLEF i (max i (j + 1)) (le_max_left _ _) 3 4 (by exact id rfl)
        (by exact id rfl))
      (.ex (max i (j + 1)) (Formula.and (funAppF (max i (j + 1)) 0 4 5 (by exact id rfl) (by exact id rfl)
          (by exact id rfl))
        (.ex (j + 1) (Formula.and (liftLEF (j + 1) (max i (j + 1)) (le_max_right _ _) 6 5 (by exact id rfl)
            (by exact id rfl))
          (.ex j (Formula.and (liftZF j 7 6 (by exact id rfl) (by exact id rfl))
            (liftLEF j (max i j) (le_max_right _ _) 7 2 (by exact id rfl) (by exact id rfl)))))))))))

theorem Sat_sigmaCodF (vB : M.T.U (max i (j + 1))) (x y : M.T.U (max i j)) :
    (sigmaCodF i j).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj vB))
        (M.T.inj x)) (M.T.inj y)) ↔ SigmaCodRel vB x y := by
  unfold sigmaCodF SigmaCodRel
  prim_simp

include hM in
/-- The Σ-set of a family value `vB` over `vA'` (elements of sort `i`). -/
theorem exists_sigmaSet (vA' : M.T.U i) (vB : M.T.U (max i (j + 1)))
    (hfun : (M.T.sortStr (max i (j + 1))).IsFunction vB)
    (hB : ∀ a, M.T.mem a vA' → ∃ vBa' : M.T.U j, (M.T.sortStr (max i (j + 1))).FunApp vB
      (M.T.liftLE (le_max_left _ _) a) (M.T.liftLE (le_max_right _ _) (M.T.j j vBa'))) :
    ∃ p : M.T.U (max i j), ∀ q, M.T.mem q p ↔ SigmaMem M.T i j (M.T.j i vA') vB q := by
  let Z := hM.sortModel (max i j)
  -- the codomain
  have hR : Z.𝒞.Def 2 (fun u => SigmaCodRel vB (u 0) (u 1)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat2 (M := M) (n := max i j) (sigmaCodF i j) (Fin.snoc env0 (M.T.inj vB)))
    exact Sat_sigmaCodF vB (u 0) (u 1)
  obtain ⟨S, hS⟩ := Z.replP hR (M.T.liftLE (le_max_left i j) vA') (by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := hM.mem_liftLE_elim _ hx
    obtain ⟨vBa', hvBa'⟩ := hB a ha
    refine ⟨M.T.liftLE (le_max_right i j) vBa', ⟨a, rfl, _, hvBa', M.T.j j vBa', rfl, vBa', rfl, rfl⟩, ?_⟩
    rintro y ⟨a', ha', v, hv, vBa, rfl, vBa'', rfl, rfl⟩
    have e1 := hM.liftLE_injective (le_max_left i j) ha'
    subst e1
    have e2 := (hM.sortModel (max i (j + 1))).funApp_unique hfun hv hvBa'
    have e3 := hM.liftLE_injective (le_max_right _ _) e2
    rw [hM.j_injective j _ _ e3])
  obtain ⟨Cod, hCod⟩ := (hM.zfc (max i j)).union S
  have hCod' : ∀ z, M.T.mem z Cod ↔ ∃ y, M.T.mem y S ∧ M.T.mem z y := hCod
  obtain ⟨pr, hpr⟩ := Z.exists_prod (M.T.liftLE (le_max_left i j) vA') Cod
  have hdef : Z.𝒞.Def 1 (fun u => SigmaMem M.T i j (M.T.j i vA') vB (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := max i j) (Prim.sigmaBodyF i j
        (s := ![i + 1, max i (j + 1), max i j + 1, max i j, max i j]) (by exact id rfl) (by exact id rfl)
        (by exact id rfl))
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj (M.T.j i vA'))) (M.T.inj vB))
          (M.T.inj (hM.emptyAt (max i j + 1)))) (M.T.inj (hM.emptyAt (max i j)))))
    rw [Sat_sigmaBodyF']
    prim_simp
  obtain ⟨p, hp⟩ := Z.sepP hdef pr
  have hp' : ∀ y, M.T.mem y p ↔ M.T.mem y pr ∧ SigmaMem M.T i j (M.T.j i vA') vB y := hp
  refine ⟨p, fun q => ?_⟩
  rw [hp' q]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨a, ha, v, hv, vBa, rfl, b, hb, hq⟩ := h
    have ha' : M.T.mem a vA' := (hM.j_mem_iff i a vA').1 ha
    obtain ⟨vBa', hvBa'⟩ := hB a ha'
    have e2 := (hM.sortModel (max i (j + 1))).funApp_unique hfun hv hvBa'
    have e3 := hM.liftLE_injective (le_max_right _ _) e2
    subst e3
    refine (hpr q).2 ⟨_, _, (hM.liftLE_mem_iff _ _ _).2 ha', ?_, hq⟩
    refine (hCod' _).2 ⟨M.T.liftLE (le_max_right i j) vBa', (hS _).2 ⟨_, (hM.liftLE_mem_iff _ _ _).2 ha',
      a, rfl, _, hv, M.T.j j vBa', rfl, vBa', rfl, rfl⟩, ?_⟩
    exact (hM.liftLE_mem_iff _ _ _).2 ((hM.j_mem_iff j b vBa').1 hb)

include hM in
/-- The Sum-set of `vA'` and `vB'` (elements of sorts `i` and `j`). -/
theorem exists_sumSet (vA' : M.T.U i) (vB' : M.T.U j) :
    ∃ p : M.T.U (max i j), ∀ q, M.T.mem q p ↔ SumMem M.T i j (M.T.j i vA') (M.T.j j vB') q := by
  let Z := hM.sortModel (max i j)
  obtain ⟨tags, htags⟩ := (hM.zfc (max i j)).pair (hM.emptyAt (max i j))
    (hM.singAt (hM.emptyAt (max i j)))
  obtain ⟨un, hun⟩ := Z.exists_union2 (M.T.liftLE (le_max_left i j) vA') (M.T.liftLE (le_max_right i j) vB')
  obtain ⟨pr, hpr⟩ := Z.exists_prod tags un
  have hdef : Z.𝒞.Def 1 (fun u => SumMem M.T i j (M.T.j i vA') (M.T.j j vB') (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := max i j) (Prim.sumBodyF i j
        (s := ![i + 1, j + 1, max i j + 1, max i j, max i j]) (by exact id rfl) (by exact id rfl)
        (by exact id rfl))
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj (M.T.j i vA'))) (M.T.inj (M.T.j j vB')))
          (M.T.inj (hM.emptyAt (max i j + 1)))) (M.T.inj (hM.emptyAt (max i j)))))
    rw [Sat_sumBodyF']
    prim_simp
  obtain ⟨p, hp⟩ := Z.sepP hdef pr
  have hp' : ∀ y, M.T.mem y p ↔ M.T.mem y pr ∧ SumMem M.T i j (M.T.j i vA') (M.T.j j vB') y := hp
  refine ⟨p, fun q => ?_⟩
  rw [hp' q]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rcases h with ⟨a, ha, z, hz, hq⟩ | ⟨b, hb, z, hz, hq⟩
    · refine (hpr q).2 ⟨z, _, (htags z).2 (Or.inl (hM.eq_emptyAt hz)), (hun _).2 (Or.inl ?_), hq⟩
      exact (hM.liftLE_mem_iff _ _ _).2 ((hM.j_mem_iff i a vA').1 ha)
    · obtain ⟨e, he, hz⟩ := hz
      rw [hM.eq_emptyAt he] at hz
      refine (hpr q).2 ⟨z, _, (htags z).2 (Or.inr (hM.eq_singAt hz)), (hun _).2 (Or.inr ?_), hq⟩
      exact (hM.liftLE_mem_iff _ _ _).2 ((hM.j_mem_iff j b vB').1 hb)

end SigmaSum

/-! ### Quotients -/

section Quot

variable {i : ℕ} (vA' : M.T.U i) (vR : M.T.U (max i (max i 1)))

/-- `~` is reflexive on the elements of `A`. -/
theorem Eqv_refl {a : M.T.U i} (ha : M.T.mem (M.T.j i a) (M.T.j i vA')) :
    Eqv M.T i (M.T.j i vA') vR a a :=
  fun _ hE => hE.2.1 a ha

theorem Eqv_symm {a b : M.T.U i} (h : Eqv M.T i (M.T.j i vA') vR a b) :
    Eqv M.T i (M.T.j i vA') vR b a :=
  fun E hE => hE.2.2.1 a b (h E hE)

theorem Eqv_trans {a b c : M.T.U i} (h : Eqv M.T i (M.T.j i vA') vR a b)
    (h' : Eqv M.T i (M.T.j i vA') vR b c) : Eqv M.T i (M.T.j i vA') vR a c :=
  fun E hE => hE.2.2.2.1 a b c (h E hE) (h' E hE)

theorem Eqv_of_relHolds {a b : M.T.U i} (ha : M.T.mem (M.T.j i a) (M.T.j i vA'))
    (hb : M.T.mem (M.T.j i b) (M.T.j i vA')) (h : RelHolds M.T i vR a b) :
    Eqv M.T i (M.T.j i vA') vR a b :=
  fun E hE => hE.2.2.2.2 a b ha hb h

include hM in
theorem isClassOf_unique {a c c' : M.T.U i} (h : IsClassOf M.T i (M.T.j i vA') vR a c)
    (h' : IsClassOf M.T i (M.T.j i vA') vR a c') : c = c' :=
  hM.ext_of_iff h h'

include hM in
theorem isClassOf_congr {a b c : M.T.U i} (hab : Eqv M.T i (M.T.j i vA') vR a b)
    (h : IsClassOf M.T i (M.T.j i vA') vR a c) : IsClassOf M.T i (M.T.j i vA') vR b c := by
  intro x
  rw [h x]
  exact and_congr Iff.rfl ⟨fun hx => Eqv_trans vA' vR (Eqv_symm vA' vR hab) hx,
    fun hx => Eqv_trans vA' vR hab hx⟩

theorem mem_classOf_self {a c : M.T.U i} (ha : M.T.mem (M.T.j i a) (M.T.j i vA'))
    (h : IsClassOf M.T i (M.T.j i vA') vR a c) : M.T.mem a c :=
  (h a).2 ⟨ha, Eqv_refl vA' vR ha⟩

theorem eqv_of_mem_classOf {a c x y : M.T.U i} (h : IsClassOf M.T i (M.T.j i vA') vR a c)
    (hx : M.T.mem x c) (hy : M.T.mem y c) : Eqv M.T i (M.T.j i vA') vR x y :=
  Eqv_trans vA' vR (Eqv_symm vA' vR ((h x).1 hx).2) ((h y).1 hy).2

include hM in
/-- The class of `a`. -/
theorem exists_classSet (a : M.T.U i) :
    ∃ c : M.T.U i, IsClassOf M.T i (M.T.j i vA') vR a c := by
  let Z := hM.sortModel i
  have hdef : Z.𝒞.Def 1 (fun u => Eqv M.T i (M.T.j i vA') vR a (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := i) (TFx.equivF i (s := ![i + 1, max i (max i 1), i, i]) 0 1 2 3 (by exact id rfl)
        (by exact id rfl) (by exact id rfl) (by exact id rfl))
        (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj (M.T.j i vA'))) (M.T.inj vR)) (M.T.inj a)))
    rw [Sat_equivF']
    prim_simp
  obtain ⟨c, hc⟩ := Z.sepP hdef vA'
  have hc' : ∀ x, M.T.mem x c ↔ M.T.mem x vA' ∧ Eqv M.T i (M.T.j i vA') vR a x := hc
  refine ⟨c, fun x => ?_⟩
  rw [hc' x, hM.j_mem_iff]

include hM in
/-- The set of classes. -/
theorem exists_quotSet : ∃ Q : M.T.U i, ∀ c, M.T.mem c Q ↔
    ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧ IsClassOf M.T i (M.T.j i vA') vR a c := by
  let Z := hM.sortModel i
  obtain ⟨pw, hpw⟩ := (hM.zfc i).power vA'
  have hdef : Z.𝒞.Def 1 (fun u => ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      IsClassOf M.T i (M.T.j i vA') vR a (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := i) (Prim.quotBodyF i (s := ![i + 1, max i (max i 1), i + 1, i, i]) (by exact id rfl)
        (by exact id rfl) (by exact id rfl))
        (Fin.snoc (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj (M.T.j i vA'))) (M.T.inj vR))
          (M.T.inj (hM.emptyAt (i + 1)))) (M.T.inj (hM.emptyAt i))))
    rw [Sat_quotBodyF']
    prim_simp
  obtain ⟨Q, hQ⟩ := Z.sepP (P := fun c => ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
    IsClassOf M.T i (M.T.j i vA') vR a c) hdef pw
  have hQ' : ∀ c, M.T.mem c Q ↔ M.T.mem c pw ∧ ∃ a, M.T.mem (M.T.j i a) (M.T.j i vA') ∧
      IsClassOf M.T i (M.T.j i vA') vR a c := hQ
  refine ⟨Q, fun c => ?_⟩
  rw [hQ' c]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨(hpw c).2 (fun x hx => ?_), h⟩
    obtain ⟨a, -, hc⟩ := h
    exact (hM.j_mem_iff i x vA').1 ((hc x).1 hx).1

include hM in
/-- The kernel of a function `f` of sort `max i j` on the lift of `vA'`, as a relation on `vA'`. -/
theorem exists_kernelSet {j : ℕ} (f : M.T.U (max i j)) : ∃ E : M.T.U i, ∀ p, M.T.mem p E ↔
    (∃ a b, M.T.mem a vA' ∧ M.T.mem b vA' ∧ (M.T.sortStr i).IsOrdPair a b p) ∧ KernelMem M.T i j f p := by
  let Z := hM.sortModel i
  obtain ⟨pr, hpr⟩ := Z.exists_prod vA' vA'
  have hdef : Z.𝒞.Def 1 (fun u => KernelMem M.T i j f (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := i) (Prim.kernelBodyF i j (s := ![i + 1, max i j, i]) (by exact id rfl)
        (by exact id rfl))
        (Fin.snoc (Fin.snoc env0 (M.T.inj (M.T.j i vA'))) (M.T.inj f)))
    rw [Sat_kernelBodyF']
    prim_simp
  obtain ⟨E, hE⟩ := Z.sepP hdef pr
  have hE' : ∀ p, M.T.mem p E ↔ M.T.mem p pr ∧ KernelMem M.T i j f p := hE
  have hpr' : ∀ p, M.T.mem p pr ↔ ∃ a b, M.T.mem a vA' ∧ M.T.mem b vA' ∧ (M.T.sortStr i).IsOrdPair a b p :=
    hpr
  refine ⟨E, fun p => ?_⟩
  rw [hE' p, hpr' p]

include hM in
/-- The kernel of `f` is an equivalence relation on `A` containing `R` whenever `f`
respects `R`. -/
theorem kernel_equivRelOn {j : ℕ} (f : M.T.U (max i j)) (E : M.T.U i)
    (hE : ∀ p, M.T.mem p E ↔
      (∃ a b, M.T.mem a vA' ∧ M.T.mem b vA' ∧ (M.T.sortStr i).IsOrdPair a b p) ∧ KernelMem M.T i j f p)
    (hfun : (M.T.sortStr (max i j)).IsFunction f)
    (hdom : ∀ a, M.T.mem a vA' → (M.T.sortStr (max i j)).InDom f (M.T.liftLE (le_max_left i j) a))
    (hresp : ∀ a b, M.T.mem a vA' → M.T.mem b vA' → RelHolds M.T i vR a b →
      ∀ u v, (M.T.sortStr (max i j)).FunApp f (M.T.liftLE (le_max_left i j) a) u →
        (M.T.sortStr (max i j)).FunApp f (M.T.liftLE (le_max_left i j) b) v → u = v) :
    EquivRelOn M.T i E (M.T.j i vA') vR := by
  let Z := hM.sortModel i
  have hmem : ∀ a b, M.T.mem a vA' → M.T.mem b vA' →
      (PairMem M.T i a b E ↔ ∃ u, (M.T.sortStr (max i j)).FunApp f (M.T.liftLE (le_max_left i j) a) u ∧
        (M.T.sortStr (max i j)).FunApp f (M.T.liftLE (le_max_left i j) b) u) := by
    intro a b ha hb
    constructor
    · rintro ⟨p, hp, hpE⟩
      obtain ⟨-, a', b', hab, u, hu, hv⟩ := (hE p).1 hpE
      obtain ⟨rfl, rfl⟩ := Z.ordPair_inj hab hp
      exact ⟨u, hu, hv⟩
    · rintro ⟨u, hu, hv⟩
      obtain ⟨p, hp⟩ := Z.exists_ordPair a b
      exact ⟨p, hp, (hE p).2 ⟨⟨a, b, ha, hb, hp⟩, a, b, hp, u, hu, hv⟩⟩
  refine ⟨fun p hp => ?_, fun a ha => ?_, fun a b hab => ?_, fun a b c hab hbc => ?_,
    fun a b ha hb hR => ?_⟩
  · obtain ⟨⟨a, b, ha, hb, hp⟩, -⟩ := (hE p).1 hp
    exact ⟨a, b, (hM.j_mem_iff i a vA').2 ha, (hM.j_mem_iff i b vA').2 hb, hp⟩
  · have ha' := (hM.j_mem_iff i a vA').1 ha
    obtain ⟨u, hu⟩ := hdom a ha'
    exact (hmem a a ha' ha').2 ⟨u, hu, hu⟩
  · obtain ⟨p, hp, hpE⟩ := hab
    obtain ⟨⟨a', b', ha, hb, hab'⟩, -⟩ := (hE p).1 hpE
    obtain ⟨e1, e2⟩ := Z.ordPair_inj hab' hp
    rw [e1] at ha; rw [e2] at hb
    obtain ⟨u, hu, hv⟩ := (hmem a b ha hb).1 ⟨p, hp, hpE⟩
    exact (hmem b a hb ha).2 ⟨u, hv, hu⟩
  · obtain ⟨p, hp, hpE⟩ := hab
    obtain ⟨⟨a', b', ha, hb, hab'⟩, -⟩ := (hE p).1 hpE
    obtain ⟨e1, e2⟩ := Z.ordPair_inj hab' hp
    rw [e1] at ha; rw [e2] at hb
    obtain ⟨q, hq, hqE⟩ := hbc
    obtain ⟨⟨b'', c', hb', hc, hbc'⟩, -⟩ := (hE q).1 hqE
    obtain ⟨e3, e4⟩ := Z.ordPair_inj hbc' hq
    rw [e4] at hc
    obtain ⟨u, hu, hv⟩ := (hmem a b ha hb).1 ⟨p, hp, hpE⟩
    obtain ⟨u', hu', hv'⟩ := (hmem b c hb hc).1 ⟨q, hq, hqE⟩
    have := (hM.sortModel (max i j)).funApp_unique hfun hv hu'
    subst this
    exact (hmem a c ha hc).2 ⟨u, hu, hv'⟩
  · have ha' := (hM.j_mem_iff i a vA').1 ha
    have hb' := (hM.j_mem_iff i b vA').1 hb
    obtain ⟨u, hu⟩ := hdom a ha'
    obtain ⟨v, hv⟩ := hdom b hb'
    have := hresp a b ha' hb' hR u v hu hv
    subst this
    exact (hmem a b ha' hb').2 ⟨u, hu, hv⟩

end Quot

/-! ### The recursion theorem for `Nat.rec` -/

section NatRec

variable {j : ℕ} (hj : 1 ≤ j)

/-- The typing invariant of a recursion function: its values at `m ∈ d` lie in `C(m)`. -/
def NatRecInv (vC : M.T.U (j + 1)) (F : M.T.U j) (d : M.T.U 1) : Prop :=
  ∀ m, M.T.mem m d → ∀ v, (M.T.sortStr j).FunApp F (M.T.liftLE hj m) v →
    ∃ c, (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) m) c ∧ M.T.mem (M.T.j j v) c

/-- The induction predicate for existence, as a tower formula
(layout `C z s k | d D F`, then the bound variables of the conditions). -/
def natRecExF : TF 4 ![j + 1, j, max 1 (max j j), 1] :=
  .ex 1 (Formula.and (isSuccF 1 3 4 (by exact id rfl) (by exact id rfl))
    (.ex j (Formula.and (liftLEF 1 j hj 4 5 (by exact id rfl) (by exact id rfl))
      (.ex j (Formula.and (isFunF j 6 (by exact id rfl))
        (Formula.and (Formula.all j (Formula.iff (inDomF j 6 7 (by exact id rfl) (by exact id rfl))
            (memF j 7 5 (by exact id rfl) (by exact id rfl))))
          (Formula.and (.ex j (Formula.and (emptyF j 7 (by exact id rfl))
              (funAppF j 6 7 1 (by exact id rfl) (by exact id rfl) (by exact id rfl))))
            (Formula.and
              -- positions: k' 7, k1 8, lk 9, lk1 10, fk 11, lk' 12, sk 13, g 14, lfk 15, r'' 16, r 17
              (Formula.all 1 (Formula.imp (memF 1 7 3 (by exact id rfl) (by exact id rfl))
                (Formula.all 1 (Formula.imp (isSuccF 1 7 8 (by exact id rfl) (by exact id rfl))
                  (Formula.all j (Formula.imp (liftLEF 1 j hj 7 9 (by exact id rfl) (by exact id rfl))
                    (Formula.all j (Formula.imp (liftLEF 1 j hj 8 10 (by exact id rfl) (by exact id rfl))
                      (Formula.all j (Formula.imp (funAppF j 6 9 11 (by exact id rfl) (by exact id rfl)
                          (by exact id rfl))
                        (Formula.all (max 1 (max j j)) (Formula.imp (liftLEF 1 (max 1 (max j j))
                            (le_max_left _ _) 7 12 (by exact id rfl) (by exact id rfl))
                          (Formula.all (max 1 (max j j)) (Formula.imp (funAppF (max 1 (max j j)) 2 12 13
                              (by exact id rfl) (by exact id rfl) (by exact id rfl))
                            (Formula.all (max j j) (Formula.imp (liftLEF (max j j) (max 1 (max j j))
                                (le_max_right _ _) 14 13 (by exact id rfl) (by exact id rfl))
                              (Formula.all (max j j) (Formula.imp (liftLEF j (max j j) (le_max_left _ _)
                                  11 15 (by exact id rfl) (by exact id rfl))
                                (Formula.all (max j j) (Formula.imp (funAppF (max j j) 14 15 16
                                    (by exact id rfl) (by exact id rfl) (by exact id rfl))
                                  (Formula.all j (Formula.imp (liftLEF j (max j j) (le_max_right _ _)
                                      17 16 (by exact id rfl) (by exact id rfl))
                                    (funAppF j 6 10 17 (by exact id rfl) (by exact id rfl)
                                      (by exact id rfl))))))))))))))))))))))))
              (Formula.all 1 (Formula.imp (memF 1 7 4 (by exact id rfl) (by exact id rfl))
                (Formula.all j (Formula.imp (liftLEF 1 j hj 7 8 (by exact id rfl) (by exact id rfl))
                  (Formula.all j (Formula.imp (funAppF j 6 8 9 (by exact id rfl) (by exact id rfl)
                      (by exact id rfl))
                    (.ex (j + 1) (Formula.and (liftLEF 1 (j + 1) (by omega) 7 10 (by exact id rfl)
                        (by exact id rfl))
                      (.ex (j + 1) (Formula.and (funAppF (j + 1) 0 10 11 (by exact id rfl)
                          (by exact id rfl) (by exact id rfl))
                        (tmemF j 9 11 (by exact id rfl) (by exact id rfl))))))))))))))))))))

theorem Sat_natRecExF (vC : M.T.U (j + 1)) (z : M.T.U j) (s : M.T.U (max 1 (max j j))) (k : M.T.U 1) :
    (natRecExF hj).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj vC))
        (M.T.inj z)) (M.T.inj s)) (M.T.inj k)) ↔
      ∃ d, (M.T.sortStr 1).IsSucc k d ∧ ∃ F, NatRecFun M.T j hj z s k d F ∧ NatRecInv hj vC F d := by
  unfold natRecExF NatRecFun NatRecInv
  prim_simp
  aesop

/-- The agreement predicate (layout `d F F' k`): `k ∈ d → F(lift k) = F'(lift k)`. -/
def agreeF : TF 4 ![1, j, j, 1] :=
  Formula.imp (memF 1 3 0 (by exact id rfl) (by exact id rfl))
    (Formula.all j (Formula.imp (liftLEF 1 j hj 3 4 (by exact id rfl) (by exact id rfl))
      (Formula.all j (Formula.imp (funAppF j 1 4 5 (by exact id rfl) (by exact id rfl) (by exact id rfl))
        (Formula.all j (Formula.imp (funAppF j 2 4 6 (by exact id rfl) (by exact id rfl) (by exact id rfl))
          (Formula.eq 5 6 (by exact id rfl))))))))

theorem Sat_agreeF (d : M.T.U 1) (F F' : M.T.U j) (k : M.T.U 1) :
    (agreeF hj).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj d))
        (M.T.inj F)) (M.T.inj F')) (M.T.inj k)) ↔
      (M.T.mem k d → ∀ v v', (M.T.sortStr j).FunApp F (M.T.liftLE hj k) v →
        (M.T.sortStr j).FunApp F' (M.T.liftLE hj k) v' → v = v') := by
  unfold agreeF
  prim_simp
  aesop

/-! #### Functions: singletons and extensions -/

include hM in
/-- The function `{⟨a, b⟩}`. -/
theorem exists_singleFun {n : ℕ} (a b : M.T.U n) : ∃ F : M.T.U n, (M.T.sortStr n).IsFunction F ∧
    (∀ x, (M.T.sortStr n).InDom F x ↔ x = a) ∧
    (∀ x y, (M.T.sortStr n).FunApp F x y ↔ x = a ∧ y = b) := by
  let Z := hM.sortModel n
  obtain ⟨p, hp⟩ := Z.exists_ordPair a b
  have hmem : ∀ x y, (M.T.sortStr n).FunApp (hM.singAt p) x y ↔ x = a ∧ y = b := by
    intro x y
    constructor
    · rintro ⟨q, hq, hxy⟩
      have hq' : q = p := (hM.mem_singAt p q).1 hq
      subst hq'
      exact Z.ordPair_inj hxy hp
    · rintro ⟨rfl, rfl⟩
      exact ⟨p, (hM.mem_singAt _ _).2 rfl, hp⟩
  refine ⟨hM.singAt p, ⟨fun q hq => ?_, fun x y y' h h' => ?_⟩, fun x => ?_, hmem⟩
  · have hq' : q = p := (hM.mem_singAt p q).1 hq
    subst hq'; exact ⟨a, b, hp⟩
  · obtain ⟨-, rfl⟩ := (hmem x y).1 h
    obtain ⟨-, rfl⟩ := (hmem x y').1 h'
    rfl
  · constructor
    · rintro ⟨y, hy⟩; exact ((hmem x y).1 hy).1
    · intro h; rw [h]; exact ⟨b, (hmem a b).2 ⟨rfl, rfl⟩⟩

include hM in
/-- Extending a function by one value outside its domain. -/
theorem exists_extendFun {n : ℕ} (F : M.T.U n) (hF : (M.T.sortStr n).IsFunction F) (a b : M.T.U n)
    (ha : ¬ (M.T.sortStr n).InDom F a) : ∃ F1 : M.T.U n, (M.T.sortStr n).IsFunction F1 ∧
    (∀ x, (M.T.sortStr n).InDom F1 x ↔ (M.T.sortStr n).InDom F x ∨ x = a) ∧
    (∀ x y, (M.T.sortStr n).FunApp F1 x y ↔ (M.T.sortStr n).FunApp F x y ∨ (x = a ∧ y = b)) := by
  let Z := hM.sortModel n
  obtain ⟨p, hp⟩ := Z.exists_ordPair a b
  obtain ⟨F1, hF1⟩ := Z.exists_union2 F (hM.singAt p)
  have hmem : ∀ x y, (M.T.sortStr n).FunApp F1 x y ↔
      (M.T.sortStr n).FunApp F x y ∨ (x = a ∧ y = b) := by
    intro x y
    constructor
    · rintro ⟨q, hq, hxy⟩
      rcases (hF1 q).1 hq with hq | hq
      · exact Or.inl ⟨q, hq, hxy⟩
      · have hq' : q = p := (hM.mem_singAt p q).1 hq
        subst hq'
        exact Or.inr (Z.ordPair_inj hxy hp)
    · rintro (⟨q, hq, hxy⟩ | ⟨rfl, rfl⟩)
      · exact ⟨q, (hF1 q).2 (Or.inl hq), hxy⟩
      · exact ⟨p, (hF1 p).2 (Or.inr ((hM.mem_singAt _ _).2 rfl)), hp⟩
  refine ⟨F1, ⟨fun q hq => ?_, fun x y y' h h' => ?_⟩, fun x => ?_, hmem⟩
  · rcases (hF1 q).1 hq with hq | hq
    · exact hF.1 q hq
    · have hq' : q = p := (hM.mem_singAt p q).1 hq
      subst hq'; exact ⟨a, b, hp⟩
  · rcases (hmem x y).1 h with h1 | ⟨rfl, rfl⟩ <;> rcases (hmem x y').1 h' with h2 | ⟨h3, rfl⟩
    · exact Z.funApp_unique hF h1 h2
    · exact absurd ⟨y, h3 ▸ h1⟩ ha
    · exact absurd ⟨y', h2⟩ ha
    · rfl
  · constructor
    · rintro ⟨y, hy⟩
      rcases (hmem x y).1 hy with h1 | ⟨rfl, -⟩
      · exact Or.inl ⟨y, h1⟩
      · exact Or.inr rfl
    · rintro (⟨y, hy⟩ | h)
      · exact ⟨y, (hmem x y).2 (Or.inl hy)⟩
      · rw [h]; exact ⟨b, (hmem a b).2 (Or.inr ⟨rfl, rfl⟩)⟩

include hM in
theorem inDom_iff_mem_lift {F : M.T.U j} {d : M.T.U 1}
    (hdom : ∀ x, (M.T.sortStr j).InDom F x ↔ M.T.mem x (M.T.liftLE hj d)) (m : M.T.U 1) :
    (M.T.sortStr j).InDom F (M.T.liftLE hj m) ↔ M.T.mem m d := by
  rw [hdom, hM.liftLE_mem_iff]

/-! #### The recursion theorem -/

/-- The typing hypotheses on `z` and `s` used by the recursion theorem. -/
def NatRecTyping (vC : M.T.U (j + 1)) (z : M.T.U j) (s : M.T.U (max 1 (max j j))) : Prop :=
  (∃ c, (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) (hM.emptyAt 1)) c ∧ M.T.mem (M.T.j j z) c) ∧
  (M.T.sortStr (max 1 (max j j))).IsFunction s ∧
  ∀ k, M.T.mem k hM.omegaSet → ∀ k1, (M.T.sortStr 1).IsSucc k k1 → ∀ fk,
    (∃ c, (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) k) c ∧ M.T.mem (M.T.j j fk) c) →
    ∃ g : M.T.U (max j j), (M.T.sortStr (max 1 (max j j))).FunApp s (M.T.liftLE (le_max_left _ _) k)
        (M.T.liftLE (le_max_right _ _) g) ∧ (M.T.sortStr (max j j)).IsFunction g ∧
      ∃ r : M.T.U j, (M.T.sortStr (max j j)).FunApp g (M.T.liftLE (le_max_left j j) fk)
          (M.T.liftLE (le_max_right j j) r) ∧
        ∃ c1, (M.T.sortStr (j + 1)).FunApp vC (M.T.liftLE (by omega) k1) c1 ∧ M.T.mem (M.T.j j r) c1

include hM in
/-- Existence of the recursion function, with its typing invariant. -/
theorem natRec_exists (vC : M.T.U (j + 1)) (z : M.T.U j) (s : M.T.U (max 1 (max j j)))
    (hty : NatRecTyping hM hj vC z s) :
    ∀ n, M.T.mem n hM.omegaSet → ∃ d, (M.T.sortStr 1).IsSucc n d ∧
      ∃ F, NatRecFun M.T j hj z s n d F ∧ NatRecInv hj vC F d := by
  obtain ⟨hz, hsfun, hs⟩ := hty
  let Z1 := hM.sortModel 1
  let Zj := hM.sortModel j
  let Zjj := hM.sortModel (max j j)
  let Zs := hM.sortModel (max 1 (max j j))
  have hP : Z1.𝒞.Def 1 (fun t => (fun k => ∃ d, (M.T.sortStr 1).IsSucc k d ∧
      ∃ F, NatRecFun M.T j hj z s k d F ∧ NatRecInv hj vC F d) (t 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := 1) (natRecExF hj)
        (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj vC)) (M.T.inj z)) (M.T.inj s)))
    exact Sat_natRecExF hj vC z s (u 0)
  refine hM.omega_induction hP (fun e he => ?_) (fun k hk ih n1 hn1 => ?_)
  · -- base case
    have he' : e = hM.emptyAt 1 := hM.eq_emptyAt he
    subst he'
    obtain ⟨d, hd⟩ := Z1.exists_succ (hM.emptyAt 1)
    obtain ⟨F, hFfun, hFdom, hFapp⟩ := exists_singleFun hM (M.T.liftLE hj (hM.emptyAt 1)) z
    have hle : M.T.liftLE hj (hM.emptyAt 1) = hM.emptyAt j := hM.liftLE_emptyAt hj
    refine ⟨d, hd, F, ⟨hFfun, fun x => ?_, ⟨hM.emptyAt j, hM.emptyAt_spec j, ?_⟩, fun k hk => ?_⟩,
      fun m hm v hv => ?_⟩
    · rw [hFdom, hM.mem_liftLE_iff]
      constructor
      · rintro rfl; exact ⟨_, (hd _).2 (Or.inr rfl), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        rcases (hd y).1 hy with hy | rfl
        · exact absurd hy (hM.not_mem_emptyAt y)
        · rfl
    · rw [← hle]; exact (hFapp _ _).2 ⟨rfl, rfl⟩
    · exact absurd hk (hM.not_mem_emptyAt k)
    · rcases (hd m).1 hm with hm | rfl
      · exact absurd hm (hM.not_mem_emptyAt m)
      · obtain ⟨-, rfl⟩ := (hFapp _ _).1 hv
        exact hz
  · -- inductive step
    obtain ⟨d, hd, F, hF, hInv⟩ := ih
    obtain ⟨hFfun, hFdom, hF0, hFstep⟩ := hF
    obtain ⟨d1, hd1⟩ := Z1.exists_succ n1
    have hd1 : ∀ z, M.T.mem z d1 ↔ M.T.mem z n1 ∨ z = n1 := hd1
    have hn1 : ∀ z, M.T.mem z n1 ↔ M.T.mem z k ∨ z = k := hn1
    have hd : ∀ z, M.T.mem z d ↔ M.T.mem z k ∨ z = k := hd
    have hkd : M.T.mem k d := (hd k).2 (Or.inr rfl)
    obtain ⟨fk, hfk⟩ := (inDom_iff_mem_lift hM hj hFdom k).2 hkd
    obtain ⟨g, hsk, hgfun, r, hr, c1, hc1, hrc1⟩ := hs k hk n1 hn1 fk (hInv k hkd fk hfk)
    have hn1d : ¬ M.T.mem n1 d := by
      intro h
      rcases (hd n1).1 h with h | h
      · exact Z1.mem_asymm h ((hn1 k).2 (Or.inr rfl))
      · exact Z1.mem_irrefl k (h ▸ (hn1 k).2 (Or.inr rfl))
    have hn1dom : ¬ (M.T.sortStr j).InDom F (M.T.liftLE hj n1) := by
      rw [inDom_iff_mem_lift hM hj hFdom]; exact hn1d
    obtain ⟨F1, hF1fun, hF1dom, hF1app⟩ := exists_extendFun hM F hFfun (M.T.liftLE hj n1) r hn1dom
    have hd1' : ∀ z, M.T.mem z d1 ↔ M.T.mem z d ∨ z = n1 := by
      intro z
      rw [hd1 z, hn1 z, hd z]
    -- values of `F1` at old points are values of `F`
    have hold : ∀ m, M.T.mem m d → ∀ v, (M.T.sortStr j).FunApp F1 (M.T.liftLE hj m) v →
        (M.T.sortStr j).FunApp F (M.T.liftLE hj m) v := by
      intro m hm v hv
      rcases (hF1app _ _).1 hv with h | ⟨h, -⟩
      · exact h
      · exact absurd (hM.liftLE_injective hj h ▸ hm) hn1d
    refine ⟨d1, hd1, F1, ⟨hF1fun, fun x => ?_, ?_,
      fun k' hk' k1' hk1' fk' hfk' sk' hsk' g' hg' r'' hr'' r' hr' => ?_⟩, fun m hm v hv => ?_⟩
    · rw [hF1dom, hFdom, hM.mem_liftLE_iff, hM.mem_liftLE_iff]
      constructor
      · rintro (⟨y, hy, rfl⟩ | rfl)
        · exact ⟨y, (hd1' y).2 (Or.inl hy), rfl⟩
        · exact ⟨n1, (hd1' n1).2 (Or.inr rfl), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        rcases (hd1' y).1 hy with hy | rfl
        · exact Or.inl ⟨y, hy, rfl⟩
        · exact Or.inr rfl
    · obtain ⟨e, he, hFe⟩ := hF0
      exact ⟨e, he, (hF1app _ _).2 (Or.inl hFe)⟩
    · rcases (hn1 k').1 hk' with hk'k | hk'k
      · -- `k' ∈ k`: the old step
        have hk'd : M.T.mem k' d := (hd k').2 (Or.inl hk'k)
        exact (hF1app _ _).2 (Or.inl (hFstep k' hk'k k1' hk1' fk' (hold k' hk'd fk' hfk') sk' hsk' g' hg'
          r'' hr'' r' hr'))
      · -- `k' = k`: the new value
        subst hk'k
        have e1 : k1' = n1 := hM.succ_unique hk1' hn1
        subst e1
        have e2 : fk' = fk := Zj.funApp_unique hFfun (hold k' hkd fk' hfk') hfk
        subst e2
        subst hg'
        have e3 : g' = g := hM.liftLE_injective _ (Zs.funApp_unique hsfun hsk' hsk)
        subst e3
        subst hr'
        have e4 : r' = r := hM.liftLE_injective _ (Zjj.funApp_unique hgfun hr'' hr)
        subst e4
        exact (hF1app _ _).2 (Or.inr ⟨rfl, rfl⟩)
    · rcases (hd1' m).1 hm with hm' | rfl
      · exact hInv m hm' v (hold m hm' v hv)
      · rcases (hF1app _ _).1 hv with h | ⟨-, rfl⟩
        · exact absurd ⟨v, h⟩ hn1dom
        · exact ⟨c1, hc1, hrc1⟩

include hM in
/-- Agreement of recursion functions: a recursion function for `n` with the typing invariant
agrees with any recursion function for `n' ⊇ n` on its domain. -/
theorem natRec_agree (vC : M.T.U (j + 1)) (z : M.T.U j) (s : M.T.U (max 1 (max j j)))
    (hty : NatRecTyping hM hj vC z s)
    {n n' d d' : M.T.U 1} {F F' : M.T.U j} (hn : M.T.mem n hM.omegaSet)
    (hd : (M.T.sortStr 1).IsSucc n d) (hd' : (M.T.sortStr 1).IsSucc n' d')
    (hnn' : (M.T.sortStr 1).Subset n n') (hF : NatRecFun M.T j hj z s n d F) (hInv : NatRecInv hj vC F d)
    (hF' : NatRecFun M.T j hj z s n' d' F') :
    ∀ k, M.T.mem k d → ∀ v v', (M.T.sortStr j).FunApp F (M.T.liftLE hj k) v →
      (M.T.sortStr j).FunApp F' (M.T.liftLE hj k) v' → v = v' := by
  obtain ⟨-, hsfun, hs⟩ := hty
  let Z1 := hM.sortModel 1
  let Zj := hM.sortModel j
  obtain ⟨hFfun, hFdom, hF0, hFstep⟩ := hF
  obtain ⟨hF'fun, hF'dom, hF'0, hF'step⟩ := hF'
  have hd : ∀ z, M.T.mem z d ↔ M.T.mem z n ∨ z = n := hd
  have hd' : ∀ z, M.T.mem z d' ↔ M.T.mem z n' ∨ z = n' := hd'
  have hP : Z1.𝒞.Def 1 (fun t => (fun k => M.T.mem k d → ∀ v v',
      (M.T.sortStr j).FunApp F (M.T.liftLE hj k) v →
      (M.T.sortStr j).FunApp F' (M.T.liftLE hj k) v' → v = v') (t 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := 1) (agreeF hj)
        (Fin.snoc (Fin.snoc (Fin.snoc env0 (M.T.inj d)) (M.T.inj F)) (M.T.inj F')))
    exact Sat_agreeF hj d F F' (u 0)
  have key : ∀ k, M.T.mem k hM.omegaSet → M.T.mem k d → ∀ v v',
      (M.T.sortStr j).FunApp F (M.T.liftLE hj k) v →
      (M.T.sortStr j).FunApp F' (M.T.liftLE hj k) v' → v = v' := by
    refine hM.omega_induction hP (fun e he _ v v' hv hv' => ?_) (fun k hk ih k1 hk1 hk1d v v' hv hv' => ?_)
    · -- base
      have he' : e = hM.emptyAt 1 := hM.eq_emptyAt he
      subst he'
      rw [hM.liftLE_emptyAt hj] at hv hv'
      obtain ⟨e0, he0, hFe0⟩ := hF0
      obtain ⟨e0', he0', hF'e0⟩ := hF'0
      rw [hM.eq_emptyAt he0] at hFe0
      rw [hM.eq_emptyAt he0'] at hF'e0
      rw [Zj.funApp_unique hFfun hv hFe0, Zj.funApp_unique hF'fun hv' hF'e0]
    · -- step
      have hk1 : ∀ z, M.T.mem z k1 ↔ M.T.mem z k ∨ z = k := hk1
      have hkn : M.T.mem k n := by
        rcases (hd k1).1 hk1d with h | h
        · exact hM.omega_transitive n hn k1 h k ((hk1 k).2 (Or.inr rfl))
        · rw [← h]; exact (hk1 k).2 (Or.inr rfl)
      have hkd : M.T.mem k d := (hd k).2 (Or.inl hkn)
      have hkn' : M.T.mem k n' := hnn' k hkn
      obtain ⟨fk, hfk⟩ := (inDom_iff_mem_lift hM hj hFdom k).2 hkd
      obtain ⟨fk', hfk'⟩ := (inDom_iff_mem_lift hM hj hF'dom k).2 ((hd' k).2 (Or.inl hkn'))
      have e1 : fk = fk' := ih hkd fk fk' hfk hfk'
      subst e1
      obtain ⟨g, hsk, -, r, hr, -⟩ := hs k hk k1 hk1 fk (hInv k hkd fk hfk)
      have h1 := hFstep k hkn k1 hk1 fk hfk _ hsk g rfl _ hr r rfl
      have h2 := hF'step k hkn' k1 hk1 fk hfk' _ hsk g rfl _ hr r rfl
      rw [Zj.funApp_unique hFfun hv h1, Zj.funApp_unique hF'fun hv' h2]
  intro k hkd
  refine key k ?_ hkd
  rcases (hd k).1 hkd with h | rfl
  · exact hM.mem_omega_of_mem hn h
  · exact hn

end NatRec

/-! ### Choice functions -/

section Choice

variable {n : ℕ}

/-- `F` is the fiber of `p` over `x`: `{q ∈ p : ∃ y, q = ⟨x, y⟩}`. -/
def IsFiber (p x F : M.T.U n) : Prop :=
  ∀ q, M.T.mem q F ↔ M.T.mem q p ∧ ∃ y, (M.T.sortStr n).IsOrdPair x y q

/-- `IsFiber` as a tower formula (layout `p x F | q y`). -/
def fiberF (n : ℕ) : TF 3 ![n, n, n] :=
  Formula.all n (Formula.iff (memF n 3 2 (by exact id rfl) (by exact id rfl))
    (Formula.and (memF n 3 0 (by exact id rfl) (by exact id rfl))
      (.ex n (ordPairF n 1 4 3 (by exact id rfl) (by exact id rfl) (by exact id rfl)))))

theorem Sat_fiberF (p x F : M.T.U n) :
    (fiberF n).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj p)) (M.T.inj x)) (M.T.inj F)) ↔
      IsFiber p x F := by
  unfold fiberF IsFiber
  prim_simp

/-- The fiber predicate `∃ y, q = ⟨x, y⟩` as a tower formula (layout `x q | y`). -/
def fiberMemF (n : ℕ) : TF 2 ![n, n] :=
  .ex n (ordPairF n 0 2 1 (by exact id rfl) (by exact id rfl) (by exact id rfl))

theorem Sat_fiberMemF (x q : M.T.U n) :
    (fiberMemF n).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj x)) (M.T.inj q)) ↔
      ∃ y, (M.T.sortStr n).IsOrdPair x y q := by
  unfold fiberMemF
  prim_simp

/-- The range predicate `∃ F ∈ X, f'(F) = c` as a tower formula (layout `X f' c | F`). -/
def rangeF (n : ℕ) : TF 3 ![n, n, n] :=
  .ex n (Formula.and (memF n 3 0 (by exact id rfl) (by exact id rfl))
    (funAppF n 1 3 2 (by exact id rfl) (by exact id rfl) (by exact id rfl)))

theorem Sat_rangeF (X f' c : M.T.U n) :
    (rangeF n).Sat M.T.toStr (Fin.snoc (α := fun _ => M.T.El) (Fin.snoc (α := fun _ => M.T.El)
      (Fin.snoc (α := fun _ => M.T.El) (env0 (M := M)) (M.T.inj X)) (M.T.inj f')) (M.T.inj c)) ↔
      ∃ F, M.T.mem F X ∧ (M.T.sortStr n).FunApp f' F c := by
  unfold rangeF
  prim_simp

include hM in
theorem exists_fiber (p x : M.T.U n) : ∃ F, IsFiber p x F := by
  let Z := hM.sortModel n
  have hdef : Z.𝒞.Def 1 (fun u => ∃ y, (M.T.sortStr n).IsOrdPair x y (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := n) (fiberMemF n) (Fin.snoc env0 (M.T.inj x)))
    exact Sat_fiberMemF x (u 0)
  obtain ⟨F, hF⟩ := Z.sepP (P := fun q => ∃ y, (M.T.sortStr n).IsOrdPair x y q) hdef p
  exact ⟨F, hF⟩

include hM in
theorem isFiber_unique {p x F F' : M.T.U n} (h : IsFiber p x F) (h' : IsFiber p x F') : F = F' :=
  hM.ext_of_iff h h'

include hM in
/-- A choice function: given a set `p` of pairs over `dom` whose fibers over the elements of
`dom` are nonempty, there is a function `f ⊆ p` with domain `dom`. -/
theorem exists_choiceFun (p dom : M.T.U n)
    (hp : ∀ q, M.T.mem q p → ∃ x y, M.T.mem x dom ∧ (M.T.sortStr n).IsOrdPair x y q)
    (hne : ∀ x, M.T.mem x dom → ∃ q y, M.T.mem q p ∧ (M.T.sortStr n).IsOrdPair x y q) :
    ∃ f : M.T.U n, (M.T.sortStr n).IsFunction f ∧ (∀ u, (M.T.sortStr n).InDom f u ↔ M.T.mem u dom) ∧
      ∀ q, M.T.mem q f → M.T.mem q p := by
  let Z := hM.sortModel n
  -- the set of fibers
  have hR : Z.𝒞.Def 2 (fun u => IsFiber p (u 0) (u 1)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat2 (M := M) (n := n) (fiberF n) (Fin.snoc env0 (M.T.inj p)))
    exact Sat_fiberF p (u 0) (u 1)
  obtain ⟨X, hX⟩ := Z.replP hR dom (fun x _ => by
    obtain ⟨F, hF⟩ := exists_fiber hM p x
    exact ⟨F, hF, fun F' hF' => isFiber_unique hM hF' hF⟩)
  have hX' : ∀ F, M.T.mem F X ↔ ∃ x, M.T.mem x dom ∧ IsFiber p x F := hX
  -- a choice function on the fibers
  obtain ⟨f', ⟨hf'fun, hf'dom⟩, hf'val⟩ := (hM.zfc n).choice X (fun F hF => by
    obtain ⟨x, hx, hF⟩ := (hX' F).1 hF
    obtain ⟨q, y, hq, hxy⟩ := hne x hx
    exact ⟨q, (hF q).2 ⟨hq, y, hxy⟩⟩)
  -- its range
  have hdef : Z.𝒞.Def 1 (fun u => ∃ F, M.T.mem F X ∧ (M.T.sortStr n).FunApp f' F (u 0)) := by
    refine SetClassSystem.Def.congr (fun u => ?_)
      (sortDef_sat M.𝒟 (n := n) (rangeF n) (Fin.snoc (Fin.snoc env0 (M.T.inj X)) (M.T.inj f')))
    exact Sat_rangeF X f' (u 0)
  obtain ⟨f, hf⟩ := Z.sepP (P := fun c => ∃ F, M.T.mem F X ∧ (M.T.sortStr n).FunApp f' F c) hdef p
  have hf' : ∀ c, M.T.mem c f ↔ M.T.mem c p ∧ ∃ F, M.T.mem F X ∧ (M.T.sortStr n).FunApp f' F c := hf
  -- an element of `f` over `x` lies in the fiber over `x`
  have key : ∀ c x y, M.T.mem c f → (M.T.sortStr n).IsOrdPair x y c →
      ∃ F, M.T.mem F X ∧ IsFiber p x F ∧ (M.T.sortStr n).FunApp f' F c := by
    intro c x y hc hxy
    obtain ⟨-, F, hFX, hFc⟩ := (hf' c).1 hc
    obtain ⟨x₁, -, hF⟩ := (hX' F).1 hFX
    have hcF : M.T.mem c F := hf'val F c hFc
    obtain ⟨-, y₁, hxy₁⟩ := (hF c).1 hcF
    obtain ⟨rfl, -⟩ := Z.ordPair_inj hxy₁ hxy
    exact ⟨F, hFX, hF, hFc⟩
  refine ⟨f, ⟨fun c hc => ?_, fun x v v' hv hv' => ?_⟩, fun u => ⟨fun hu => ?_, fun hu => ?_⟩,
    fun c hc => ((hf' c).1 hc).1⟩
  · obtain ⟨x, y, -, hxy⟩ := hp c (((hf' c).1 hc).1)
    exact ⟨x, y, hxy⟩
  · obtain ⟨c, hc, hxv⟩ := hv
    obtain ⟨c', hc', hxv'⟩ := hv'
    obtain ⟨F, hFX, hF, hFc⟩ := key c x v hc hxv
    obtain ⟨F', -, hF', hFc'⟩ := key c' x v' hc' hxv'
    have e := isFiber_unique hM hF hF'
    subst e
    have e2 := Z.funApp_unique hf'fun hFc hFc'
    subst e2
    exact (Z.ordPair_inj hxv hxv').2
  · obtain ⟨v, c, hc, hxv⟩ := hu
    obtain ⟨x, y, hx, hxy⟩ := hp c ((hf' c).1 hc).1
    obtain ⟨rfl, -⟩ := Z.ordPair_inj hxy hxv
    exact hx
  · obtain ⟨F, hF⟩ := exists_fiber hM p u
    have hFX : M.T.mem F X := (hX' F).2 ⟨u, hu, hF⟩
    obtain ⟨c, hc⟩ := (hf'dom F).2 hFX
    have hcF : M.T.mem c F := hf'val F c hc
    obtain ⟨hcp, y, huy⟩ := (hF c).1 hcF
    exact ⟨y, c, (hf' c).2 ⟨hcp, F, hFX, hc⟩, huy⟩

end Choice

end SolidLean.Calc
