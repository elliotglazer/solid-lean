import Solid.Calc.PrimSound

/-!
# Soundness: the computation rules of the primitives (draft 2, §3.4)

For each computation rule `DefEq.*` of a primitive, the two sides have the
same values (and the left-hand side is certified).  Together with the
congruence rule `DefEq.congrPrim`, these are the primitive cases of the
induction in `Soundness.lean`.
-/

universe u

open Classical

namespace SolidLean.Calc

open SolidLean.Solid Term

variable {M : TowerWithClasses.{u}} (hM : IsTowerModel M)

section Eq

variable {m : ℕ} {Γ : Ctx m}

/-! ### Values of the constructors involved -/

include hM in
/-- The value of `pair A B a b`. -/
theorem pair_val (i j : ℕ) (args : Fin 4 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.pair i j).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (max i (j + 1))} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {va : M.T.U i} (hva : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj va)
    {vb : M.T.U j} (hvb : ∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vb) {q : M.T.U (max i j)}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) va) (M.T.liftLE (le_max_right i j) vb) q) :
    ∀ w, Val M.T Γ (prim (.pair i j) args) η w ↔ w = M.T.inj q := by
  refine val_unique_of_sorted (n := max i j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.pair i j) args hg _
    (vals_cons hvA (vals_cons hvB (vals_cons hva (vals_cons hvb vals_nil)))) (r := max i j) rfl,
    clause_pair M.T i j _ _ va vb w' rfl rfl rfl]
  exact ⟨fun h => (hM.sortModel (max i j)).ordPair_unique h hq, fun h => h ▸ hq⟩

include hM in
/-- The value of `snd A B s`. -/
theorem snd_val (i j : ℕ) (args : Fin 3 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.snd i j).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (max i (j + 1))} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {vs : M.T.U (max i j)} (hvs : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vs) {a : M.T.U i} {b : M.T.U j}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (M.T.liftLE (le_max_left i j) a) (M.T.liftLE (le_max_right i j) b) vs) :
    ∀ w, Val M.T Γ (prim (.snd i j) args) η w ↔ w = M.T.inj b := by
  refine val_unique_of_sorted (n := j) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.snd i j) args hg _
    (vals_cons hvA (vals_cons hvB (vals_cons hvs vals_nil))) (r := j) rfl,
    clause_snd M.T i j _ _ vs w' rfl rfl]
  constructor
  · rintro ⟨u, hu⟩
    exact hM.liftLE_injective _ ((hM.sortModel (max i j)).ordPair_inj hu hq).2
  · rintro rfl; exact ⟨_, hq⟩

/-- The value of `up A a`. -/
theorem up_val (i d : ℕ) (args : Fin 2 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.up i d).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {va : M.T.U i} (hva : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj va) :
    ∀ w, Val M.T Γ (prim (.up i d) args) η w ↔ w = M.T.inj (M.T.liftLE (by omega : i ≤ i + d) va) := by
  refine val_unique_of_sorted (n := i + d) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.up i d) args hg _
    (vals_cons hvA (vals_cons hva vals_nil)) (r := i + d) rfl, clause_up M.T i d _ _ va w' rfl rfl]

include hM in
/-- The value of `down A a` when `a`'s value is a lift. -/
theorem down_val (i d : ℕ) (args : Fin 2 → Term) (hg : ∀ k, (args k).cls Γ = (Prim.down i d).argSort k)
    {η : Env M.T m} {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {va : M.T.U (i + d)} (hva : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj va) {w₀ : M.T.U i}
    (hw₀ : va = M.T.liftLE (by omega : i ≤ i + d) w₀) :
    ∀ w, Val M.T Γ (prim (.down i d) args) η w ↔ w = M.T.inj w₀ := by
  refine val_unique_of_sorted (n := i) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.down i d) args hg _
    (vals_cons hvA (vals_cons hva vals_nil)) (r := i) rfl, clause_down M.T i d _ _ va w' rfl rfl, hw₀]
  exact ⟨fun h => (hM.liftLE_injective _ h).symm, fun h => by rw [h]⟩

include hM in
/-- The value of `sumRec` at a left injection. -/
theorem sumRec_val_inl (i j k : ℕ) (args : Fin 6 → Term)
    (hg : ∀ l, (args l).cls Γ = (Prim.sumRec i j k).argSort l) {η : Env M.T m}
    {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (j + 1)} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {vC : M.T.U (max (max i j) (k + 1))} (hvC : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vC)
    {vf : M.T.U (max i k)} (hvf : ∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vf)
    (hffun : (M.T.sortStr (max i k)).IsFunction vf)
    {vg : M.T.U (max j k)} (hvg : ∀ w, Val M.T Γ (args 4) η w ↔ w = M.T.inj vg)
    {vs : M.T.U (max i j)} (hvs : ∀ w, Val M.T Γ (args 5) η w ↔ w = M.T.inj vs) {a : M.T.U i}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (hM.emptyAt (max i j)) (M.T.liftLE (le_max_left i j) a) vs)
    {b : M.T.U k} (hb : (M.T.sortStr (max i k)).FunApp vf (M.T.liftLE (le_max_left i k) a)
      (M.T.liftLE (le_max_right i k) b)) :
    ∀ w, Val M.T Γ (prim (.sumRec i j k) args) η w ↔ w = M.T.inj b := by
  refine val_unique_of_sorted (n := k) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.sumRec i j k) args hg _
    (vals_cons hvA (vals_cons hvB (vals_cons hvC (vals_cons hvf (vals_cons hvg (vals_cons hvs vals_nil))))))
    (r := k) rfl, clause_sumRec M.T i j k _ _ vf vg vs w' rfl rfl rfl rfl]
  constructor
  · rintro (⟨x, z', hz', hq', happ⟩ | ⟨y, z', ⟨e', he', hs'⟩, hq', -⟩)
    · obtain ⟨-, hx⟩ := (hM.sortModel _).ordPair_inj hq' hq
      have ex : x = a := hM.liftLE_injective _ hx
      subst ex
      exact hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hffun happ hb)
    · exact absurd ((hM.sortModel _).ordPair_inj hq' hq).1 (tag_ne hM (hM.emptyAt_spec _) he' hs').symm
  · rintro rfl
    exact Or.inl ⟨a, _, hM.emptyAt_spec _, hq, hb⟩

include hM in
/-- The value of `sumRec` at a right injection. -/
theorem sumRec_val_inr (i j k : ℕ) (args : Fin 6 → Term)
    (hg : ∀ l, (args l).cls Γ = (Prim.sumRec i j k).argSort l) {η : Env M.T m}
    {vA : M.T.U (i + 1)} (hvA : ∀ w, Val M.T Γ (args 0) η w ↔ w = M.T.inj vA)
    {vB : M.T.U (j + 1)} (hvB : ∀ w, Val M.T Γ (args 1) η w ↔ w = M.T.inj vB)
    {vC : M.T.U (max (max i j) (k + 1))} (hvC : ∀ w, Val M.T Γ (args 2) η w ↔ w = M.T.inj vC)
    {vf : M.T.U (max i k)} (hvf : ∀ w, Val M.T Γ (args 3) η w ↔ w = M.T.inj vf)
    {vg : M.T.U (max j k)} (hvg : ∀ w, Val M.T Γ (args 4) η w ↔ w = M.T.inj vg)
    (hgfun : (M.T.sortStr (max j k)).IsFunction vg)
    {vs : M.T.U (max i j)} (hvs : ∀ w, Val M.T Γ (args 5) η w ↔ w = M.T.inj vs) {b : M.T.U j}
    (hq : (M.T.sortStr (max i j)).IsOrdPair (hM.singAt (hM.emptyAt (max i j)))
      (M.T.liftLE (le_max_right i j) b) vs)
    {c : M.T.U k} (hc : (M.T.sortStr (max j k)).FunApp vg (M.T.liftLE (le_max_left j k) b)
      (M.T.liftLE (le_max_right j k) c)) :
    ∀ w, Val M.T Γ (prim (.sumRec i j k) args) η w ↔ w = M.T.inj c := by
  refine val_unique_of_sorted (n := k) rfl _ fun w' => ?_
  rw [Val_prim_of_vals' (Prim.sumRec i j k) args hg _
    (vals_cons hvA (vals_cons hvB (vals_cons hvC (vals_cons hvf (vals_cons hvg (vals_cons hvs vals_nil))))))
    (r := k) rfl, clause_sumRec M.T i j k _ _ vf vg vs w' rfl rfl rfl rfl]
  constructor
  · rintro (⟨x, z', hz', hq', -⟩ | ⟨y, z', ⟨e', he', hs'⟩, hq', happ⟩)
    · exact absurd ((hM.sortModel _).ordPair_inj hq' hq).1
        (tag_ne hM hz' (hM.emptyAt_spec _) (hM.singAt_spec _))
    · obtain ⟨-, hy⟩ := (hM.sortModel _).ordPair_inj hq' hq
      have ey : y = b := hM.liftLE_injective _ hy
      subst ey
      exact hM.liftLE_injective _ ((hM.sortModel _).funApp_unique hgfun happ hc)
  · rintro rfl
    exact Or.inr ⟨b, _, ⟨_, hM.emptyAt_spec _, hM.singAt_spec _⟩, hq, hc⟩

/-! ### Congruence -/

theorem eq_congrPrim {n : ℕ} (c : Prim n) (args args' : Fin n → Term) (hok : c.Ok)
    (hg : ∀ k, (args k).cls Γ = c.argSort k) (hg' : ∀ k, (args' k).cls Γ = c.argSort k)
    (ih : ∀ k, PEq hM Γ (args k) (args' k) (c.argType m args k) (c.argSort k)) :
    PEq hM Γ (prim c args) (prim c args') (c.resultType m args) c.level := by
  refine ⟨case_prim hM c args hok hg (fun k => (ih k).1), fun η hv w => ?_⟩
  rw [Val_prim' M.T c args hg, Val_prim' M.T c args' hg']
  refine and_congr Iff.rfl (exists_congr fun vs => and_congr (forall_congr' fun k => ?_) Iff.rfl)
  exact (ih k).2 η hv (vs k)

/-! ### `Eq.rec C c a refl ≡ c` -/

theorem eq_eqRecRefl (i j : ℕ) (A a C c : Term)
    (hg : ∀ k, (![A, a, C, c, a, prim (.refl i) ![A, a]] k).cls Γ = (Prim.eqRec i j).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, a, C, c, a, prim (.refl i) ![A, a]] k)
      ((Prim.eqRec i j).argType m ![A, a, C, c, a, prim (.refl i) ![A, a]] k) ((Prim.eqRec i j).argSort k)) :
    PEq hM Γ (prim (.eqRec i j) ![A, a, C, c, a, prim (.refl i) ![A, a]]) c
      ((Prim.eqRec i j).resultType m ![A, a, C, c, a, prim (.refl i) ![A, a]]) j := by
  refine ⟨case_prim hM _ _ trivial hg ih, fun η hv w => ?_⟩
  have hvals : ∀ k, ∃ v, ∀ w, Val M.T Γ (![A, a, C, c, a, prim (.refl i) ![A, a]] k) η w ↔ w = v :=
    fun k => ⟨_, (PTy.term_val hM (ih k) hv).choose_spec.1⟩
  choose va hva using hvals
  have h3 : PTy hM Γ c (app .data (j + 1) (app .data (j + 1) C a) (prim (.refl i) ![A, a])) j := ih 3
  obtain ⟨vc, hvc, -⟩ := PTy.term_val hM h3 hv
  have e3 : va 3 = M.T.inj vc := ((hva 3 _).1 ((hvc _).2 rfl)).symm
  rw [Val_prim_of_vals (Prim.eqRec i j) _ hg va hva, hvc]
  constructor
  · rintro ⟨hw, h⟩
    obtain ⟨w', rfl⟩ := elSort M.T w hw
    rw [(clause_eqRec M.T i j va _ vc w' e3 rfl).1 h]
    rfl
  · rintro rfl
    exact ⟨rfl, (clause_eqRec M.T i j va _ vc vc e3 rfl).2 rfl⟩

/-! ### Σ-types -/

theorem eq_sigmaFst (i j : ℕ) (A B a b : Term) (hj : 1 ≤ j)
    (hg : ∀ k, (![A, B, a, b] k).cls Γ = (Prim.pair i j).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, B, a, b] k) ((Prim.pair i j).argType m ![A, B, a, b] k)
      ((Prim.pair i j).argSort k)) :
    PEq hM Γ (prim (.fst i j) ![A, B, prim (.pair i j) ![A, B, a, b]]) a A i := by
  have hpair : PTy hM Γ (prim (.pair i j) ![A, B, a, b]) (prim (.sigma i j) ![A, B]) (max i j) :=
    case_pair hM i j ![A, B, a, b] hj hg ih
  have hg' : ∀ k, (![A, B, prim (.pair i j) ![A, B, a, b]] k).cls Γ = (Prim.fst i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; rfl]
  have ih' : ∀ k, PTy hM Γ (![A, B, prim (.pair i j) ![A, B, a, b]] k)
      ((Prim.fst i j).argType m ![A, B, prim (.pair i j) ![A, B, a, b]] k) ((Prim.fst i j).argSort k) :=
    fun k => by fin_cases k <;> [exact ih 0; exact ih 1; exact hpair]
  refine ⟨case_fst hM i j _ hg' ih', fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ B (pi .data i (j + 1) A (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ a A i := ih 2
  have h3 : PTy hM Γ b (app .data (j + 1) B a) j := ih 3
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨vB, hvB, -⟩ := PTy.term_val hM h1 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vb, hvb, -⟩ := PTy.term_val hM h3 hv
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (M.T.liftLE (le_max_left i j) va)
    (M.T.liftLE (le_max_right i j) vb)
  have hpv := pair_val hM i j ![A, B, a, b] hg hvA hvB hva hvb hq
  rw [fst_val hM i j _ hg' hvA hvB hpv hq, hva]

theorem eq_sigmaSnd (i j : ℕ) (A B a b : Term) (hj : 1 ≤ j)
    (hg : ∀ k, (![A, B, a, b] k).cls Γ = (Prim.pair i j).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, B, a, b] k) ((Prim.pair i j).argType m ![A, B, a, b] k)
      ((Prim.pair i j).argSort k)) :
    PEq hM Γ (prim (.snd i j) ![A, B, prim (.pair i j) ![A, B, a, b]]) b
      ((Prim.snd i j).resultType m ![A, B, prim (.pair i j) ![A, B, a, b]]) j := by
  have hpair : PTy hM Γ (prim (.pair i j) ![A, B, a, b]) (prim (.sigma i j) ![A, B]) (max i j) :=
    case_pair hM i j ![A, B, a, b] hj hg ih
  have hg' : ∀ k, (![A, B, prim (.pair i j) ![A, B, a, b]] k).cls Γ = (Prim.snd i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; rfl]
  have ih' : ∀ k, PTy hM Γ (![A, B, prim (.pair i j) ![A, B, a, b]] k)
      ((Prim.snd i j).argType m ![A, B, prim (.pair i j) ![A, B, a, b]] k) ((Prim.snd i j).argSort k) :=
    fun k => by fin_cases k <;> [exact ih 0; exact ih 1; exact hpair]
  refine ⟨case_snd hM i j _ hg' ih', fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ B (pi .data i (j + 1) A (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ a A i := ih 2
  have h3 : PTy hM Γ b (app .data (j + 1) B a) j := ih 3
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨vB, hvB, -⟩ := PTy.term_val hM h1 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vb, hvb, -⟩ := PTy.term_val hM h3 hv
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (M.T.liftLE (le_max_left i j) va)
    (M.T.liftLE (le_max_right i j) vb)
  have hpv := pair_val hM i j ![A, B, a, b] hg hvA hvB hva hvb hq
  rw [snd_val hM i j _ hg' hvA hvB hpv hq, hvb]

theorem eq_sigmaEta (i j : ℕ) (A B s : Term) (hj : 1 ≤ j)
    (hg : ∀ k, (![A, B, s] k).cls Γ = (Prim.fst i j).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, B, s] k) ((Prim.fst i j).argType m ![A, B, s] k) ((Prim.fst i j).argSort k)) :
    PEq hM Γ (prim (.pair i j) ![A, B, prim (.fst i j) ![A, B, s], prim (.snd i j) ![A, B, s]]) s
      (prim (.sigma i j) ![A, B]) (max i j) := by
  have hfst : PTy hM Γ (prim (.fst i j) ![A, B, s]) A i := case_fst hM i j ![A, B, s] hg ih
  have hsnd : PTy hM Γ (prim (.snd i j) ![A, B, s]) (app .data (j + 1) B (prim (.fst i j) ![A, B, s])) j :=
    case_snd hM i j ![A, B, s] hg ih
  have hg' : ∀ k, (![A, B, prim (.fst i j) ![A, B, s], prim (.snd i j) ![A, B, s]] k).cls Γ =
      (Prim.pair i j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; rfl; rfl]
  have ih' : ∀ k, PTy hM Γ (![A, B, prim (.fst i j) ![A, B, s], prim (.snd i j) ![A, B, s]] k)
      ((Prim.pair i j).argType m ![A, B, prim (.fst i j) ![A, B, s], prim (.snd i j) ![A, B, s]] k)
      ((Prim.pair i j).argSort k) :=
    fun k => by fin_cases k <;> [exact ih 0; exact ih 1; exact hfst; exact hsnd]
  refine ⟨case_pair hM i j _ hj hg' ih', fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ B (pi .data i (j + 1) A (univ j)) (max i (j + 1)) := ih 1
  have h2 : PTy hM Γ s (prim (.sigma i j) ![A, B]) (max i j) := ih 2
  obtain ⟨vA', vB, p, hvA, -, hvB, -, hval, hp, hpval⟩ := sigma_data hM i j ![A, B, s]
    (fun k => by fin_cases k <;> [exact hg 0; exact hg 1]) h0 h1 hv
  obtain ⟨vs, hvs, hsmem⟩ := PTy.term_val hM h2 hv
  obtain ⟨a, vBa', b, -, -, -, -, hq⟩ := sigma_elem hM hval hp (hsmem _ ((hpval _).2 rfl))
  have hfv := fst_val hM i j ![A, B, s] hg hvA hvB hvs hq
  have hsv := snd_val hM i j ![A, B, s] hg hvA hvB hvs hq
  rw [pair_val hM i j _ hg' hvA hvB hfv hsv hq, hvs]

/-! ### Lifting -/

theorem eq_downUp (i d : ℕ) (A a : Term) (hg : ∀ k, (![A, a] k).cls Γ = (Prim.up i d).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, a] k) ((Prim.up i d).argType m ![A, a] k) ((Prim.up i d).argSort k)) :
    PEq hM Γ (prim (.down i d) ![A, prim (.up i d) ![A, a]]) a A i := by
  have hup : PTy hM Γ (prim (.up i d) ![A, a]) (prim (.lift i d) ![A]) (i + d) := case_up hM i d ![A, a] hg ih
  have hg' : ∀ k, (![A, prim (.up i d) ![A, a]] k).cls Γ = (Prim.down i d).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; rfl]
  have ih' : ∀ k, PTy hM Γ (![A, prim (.up i d) ![A, a]] k)
      ((Prim.down i d).argType m ![A, prim (.up i d) ![A, a]] k) ((Prim.down i d).argSort k) :=
    fun k => by fin_cases k <;> [exact ih 0; exact hup]
  refine ⟨case_down hM i d _ hg' ih', fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ a A i := ih 1
  obtain ⟨vA, hvA, -⟩ := PTy.type_val hM h0 hv
  obtain ⟨va, hva, -⟩ := PTy.term_val hM h1 hv
  have huv := up_val i d ![A, a] hg hvA hva
  rw [down_val hM i d _ hg' hvA huv rfl, hva]

theorem eq_upDown (i d : ℕ) (A a : Term) (hg : ∀ k, (![A, a] k).cls Γ = (Prim.down i d).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, a] k) ((Prim.down i d).argType m ![A, a] k) ((Prim.down i d).argSort k)) :
    PEq hM Γ (prim (.up i d) ![A, prim (.down i d) ![A, a]]) a (prim (.lift i d) ![A]) (i + d) := by
  have hdown : PTy hM Γ (prim (.down i d) ![A, a]) A i := case_down hM i d ![A, a] hg ih
  have hg' : ∀ k, (![A, prim (.down i d) ![A, a]] k).cls Γ = (Prim.up i d).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; rfl]
  have ih' : ∀ k, PTy hM Γ (![A, prim (.down i d) ![A, a]] k)
      ((Prim.up i d).argType m ![A, prim (.down i d) ![A, a]] k) ((Prim.up i d).argSort k) :=
    fun k => by fin_cases k <;> [exact ih 0; exact hdown]
  refine ⟨case_up hM i d _ hg' ih', fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ a (prim (.lift i d) ![A]) (i + d) := ih 1
  obtain ⟨vA', hvA, -⟩ := type_arg_vals hM h0 hv
  obtain ⟨va, hva, hmem⟩ := PTy.term_val hM h1 hv
  have hg1 : ∀ k, (![A] k).cls Γ = (Prim.lift i d).argSort k := fun k => by fin_cases k; exact hg 0
  have hmem' := hmem _ ((lift_type_val i d ![A] hg1 hvA _).2 rfl)
  obtain ⟨y, hy, hy'⟩ := hM.mem_liftLE_elim _ hmem'
  obtain ⟨w₀, -, rfl⟩ := (hM.mem_j_iff i vA' y).1 hy
  rw [j_liftLE_comm hM] at hy'
  have e := hM.j_injective _ _ _ hy'
  have hdv := down_val hM i d ![A, a] hg hvA hva e.symm
  rw [up_val i d _ hg' hvA hdv, hva, e]

/-! ### Sums -/

theorem eq_sumRecInl (i j k : ℕ) (A B C f g a : Term) (hk : 1 ≤ k)
    (hg : ∀ l, (![A, B, C, f, g, prim (.inl i j) ![A, B, a]] l).cls Γ = (Prim.sumRec i j k).argSort l)
    (ih : ∀ l, PTy hM Γ (![A, B, C, f, g, prim (.inl i j) ![A, B, a]] l)
      ((Prim.sumRec i j k).argType m ![A, B, C, f, g, prim (.inl i j) ![A, B, a]] l)
      ((Prim.sumRec i j k).argSort l))
    (hca : a.cls Γ = i) (ha : PTy hM Γ a A i) :
    PEq hM Γ (prim (.sumRec i j k) ![A, B, C, f, g, prim (.inl i j) ![A, B, a]]) (app .data k f a)
      (app .data (k + 1) C (prim (.inl i j) ![A, B, a])) k := by
  refine ⟨case_sumRec hM i j k _ hk hg ih, fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ B (univ j) (j + 1) := ih 1
  have h2 : PTy hM Γ C (pi .data (max i j) (k + 1) (prim (.sum i j) ![A, B]) (univ k)) (max (max i j) (k + 1)) :=
    ih 2
  have h3 : PTy hM Γ f (pi .data i k A (app .data (k + 1) (Term.shift m 1 C)
    (prim (.inl i j) ![Term.shift m 1 A, Term.shift m 1 B, var m]))) (max i k) := ih 3
  have h4 : PTy hM Γ g (pi .data j k B (app .data (k + 1) (Term.shift m 1 C)
    (prim (.inr i j) ![Term.shift m 1 A, Term.shift m 1 B, var m]))) (max j k) := ih 4
  obtain ⟨vA', hvA, -⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB', hvB, -⟩ := type_arg_vals hM h1 hv
  obtain ⟨vC, hvC, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vf, hvf, hffun, hf⟩ := pi_data_of_pty hM h3 hv (hg 0) rfl hvA
  obtain ⟨vg, hvg, -⟩ := PTy.term_val hM h4 hv
  obtain ⟨va, hva, hamem⟩ := elem_arg_vals hM ha hv hvA
  have ha' : M.T.mem (M.T.j i va) (M.T.j i vA') := (hM.j_mem_iff i va vA').2 hamem
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (hM.emptyAt (max i j))
    (M.T.liftLE (le_max_left i j) va)
  have hinl := inl_val hM i j ![A, B, a] (fun l => by fin_cases l <;> [exact hg 0; exact hg 1; exact hca])
    hvA hvB hva hq
  obtain ⟨⟨v, hv'⟩, _, -, -, hrng⟩ := hf va ha'
  obtain ⟨b, -, rfl⟩ := hrng v hv'
  have hcf : f.cls Γ = max i k := hg 3
  rw [sumRec_val_inl hM i j k _ hg hvA hvB hvC hvf hffun hvg hinl hq hv',
    app_data_val hM hcf hca (le_max_right i k) (le_max_left i k) hvf hva hffun hv']

theorem eq_sumRecInr (i j k : ℕ) (A B C f g b : Term) (hk : 1 ≤ k)
    (hg : ∀ l, (![A, B, C, f, g, prim (.inr i j) ![A, B, b]] l).cls Γ = (Prim.sumRec i j k).argSort l)
    (ih : ∀ l, PTy hM Γ (![A, B, C, f, g, prim (.inr i j) ![A, B, b]] l)
      ((Prim.sumRec i j k).argType m ![A, B, C, f, g, prim (.inr i j) ![A, B, b]] l)
      ((Prim.sumRec i j k).argSort l))
    (hcb : b.cls Γ = j) (hb : PTy hM Γ b B j) :
    PEq hM Γ (prim (.sumRec i j k) ![A, B, C, f, g, prim (.inr i j) ![A, B, b]]) (app .data k g b)
      (app .data (k + 1) C (prim (.inr i j) ![A, B, b])) k := by
  refine ⟨case_sumRec hM i j k _ hk hg ih, fun η hv w => ?_⟩
  have h0 : PTy hM Γ A (univ i) (i + 1) := ih 0
  have h1 : PTy hM Γ B (univ j) (j + 1) := ih 1
  have h2 : PTy hM Γ C (pi .data (max i j) (k + 1) (prim (.sum i j) ![A, B]) (univ k)) (max (max i j) (k + 1)) :=
    ih 2
  have h3 : PTy hM Γ f (pi .data i k A (app .data (k + 1) (Term.shift m 1 C)
    (prim (.inl i j) ![Term.shift m 1 A, Term.shift m 1 B, var m]))) (max i k) := ih 3
  have h4 : PTy hM Γ g (pi .data j k B (app .data (k + 1) (Term.shift m 1 C)
    (prim (.inr i j) ![Term.shift m 1 A, Term.shift m 1 B, var m]))) (max j k) := ih 4
  obtain ⟨vA', hvA, -⟩ := type_arg_vals hM h0 hv
  obtain ⟨vB', hvB, -⟩ := type_arg_vals hM h1 hv
  obtain ⟨vC, hvC, -⟩ := PTy.term_val hM h2 hv
  obtain ⟨vf, hvf, -⟩ := PTy.term_val hM h3 hv
  obtain ⟨vg, hvg, hgfun, hgv⟩ := pi_data_of_pty hM h4 hv (hg 1) rfl hvB
  obtain ⟨vb, hvb, hbmem⟩ := elem_arg_vals hM hb hv hvB
  have hb' : M.T.mem (M.T.j j vb) (M.T.j j vB') := (hM.j_mem_iff j vb vB').2 hbmem
  obtain ⟨q, hq⟩ := (hM.sortModel (max i j)).exists_ordPair (hM.singAt (hM.emptyAt (max i j)))
    (M.T.liftLE (le_max_right i j) vb)
  have hinr := inr_val hM i j ![A, B, b] (fun l => by fin_cases l <;> [exact hg 0; exact hg 1; exact hcb])
    hvA hvB hvb hq
  obtain ⟨⟨v, hv'⟩, _, -, -, hrng⟩ := hgv vb hb'
  obtain ⟨c, -, rfl⟩ := hrng v hv'
  have hcg : g.cls Γ = max j k := hg 4
  rw [sumRec_val_inr hM i j k _ hg hvA hvB hvC hvf hvg hgfun hinr hq hv',
    app_data_val hM hcg hcb (le_max_right j k) (le_max_left j k) hvg hvb hgfun hv']

/-! ### Natural numbers -/

theorem eq_natRecZero (j : ℕ) (C z s : Term) (hj : 1 ≤ j)
    (hg : ∀ k, (![C, z, s, prim .zero ![]] k).cls Γ = (Prim.natRec j).argSort k)
    (ih : ∀ k, PTy hM Γ (![C, z, s, prim .zero ![]] k) ((Prim.natRec j).argType m ![C, z, s, prim .zero ![]] k)
      ((Prim.natRec j).argSort k)) :
    PEq hM Γ (prim (.natRec j) ![C, z, s, prim .zero ![]]) z (app .data (j + 1) C (prim .zero ![])) j := by
  refine ⟨case_natRec hM j _ hj hg ih, fun η hv w => ?_⟩
  obtain ⟨vC, vz, vs, vn, hvC, hCfun, hC', hvz, hvs, hvn, hnω, hty⟩ := natRec_data hM j _ hj hg ih hv
  -- `n = ∅`
  have hn0 : vn = hM.emptyAt 1 :=
    Sorted.inj_injective M.T.U (((zero_val hM Γ η) _).1 ((hvn _).2 rfl))
  subst hn0
  obtain ⟨d, hd, F, hF, hInv⟩ := natRec_exists hM hj vC vz vs hty _ hnω
  obtain ⟨e, he, hFe⟩ := hF.2.2.1
  have hw : (M.T.sortStr j).FunApp F (M.T.liftLE hj (hM.emptyAt 1)) vz := by
    rw [hM.liftLE_emptyAt hj, ← hM.eq_emptyAt he]; exact hFe
  rw [natRec_val hM j hj _ hg hvC hvz hvs hvn hty hnω hd hF hInv hw]
  exact (hvz w).symm

theorem eq_natRecSucc (j : ℕ) (C z s n : Term) (hj : 1 ≤ j)
    (hg : ∀ k, (![C, z, s, prim .succ ![n]] k).cls Γ = (Prim.natRec j).argSort k)
    (ih : ∀ k, PTy hM Γ (![C, z, s, prim .succ ![n]] k) ((Prim.natRec j).argType m ![C, z, s, prim .succ ![n]] k)
      ((Prim.natRec j).argSort k))
    (hcn : n.cls Γ = 1) (hn : PTy hM Γ n (prim .nat ![]) 1) :
    PEq hM Γ (prim (.natRec j) ![C, z, s, prim .succ ![n]])
      (app .data j (app .data (max j j) s n) (prim (.natRec j) ![C, z, s, n]))
      (app .data (j + 1) C (prim .succ ![n])) j := by
  refine ⟨case_natRec hM j _ hj hg ih, fun η hv w => ?_⟩
  obtain ⟨vC, vz, vs, vn1, hvC, hCfun, hC', hvz, hvs, hvn1, hn1ω, hty⟩ := natRec_data hM j _ hj hg ih hv
  -- the value of `n`, and `n + 1`
  obtain ⟨vn, hvn, hnmem⟩ := PTy.term_val hM hn hv
  have hnω : M.T.mem vn hM.omegaSet := (hM.j_mem_iff 1 _ _).1 (hnmem _ ((nat_type_val hM ![] _).2 rfl))
  obtain ⟨sn, hsn⟩ := (hM.sortModel 1).exists_succ vn
  have hsv := succ_val hM Γ η ![n] (fun k => by fin_cases k; exact hcn) hvn hsn
  have e1 : sn = vn1 := (Sorted.inj_injective M.T.U ((hsv _).1 ((hvn1 _).2 rfl))).symm
  subst e1
  -- the recursion function for `n + 1`, and its values at `n` and `n + 1`
  obtain ⟨d, hd, F, hF, hInv⟩ := natRec_exists hM hj vC vz vs hty _ hn1ω
  have hnd : M.T.mem vn d := (hd vn).2 (Or.inl ((hsn vn).2 (Or.inr rfl)))
  obtain ⟨fn, hfn⟩ := (inDom_iff_mem_lift hM hj hF.2.1 vn).2 hnd
  have hsnd : M.T.mem sn d := (hd sn).2 (Or.inr rfl)
  obtain ⟨fsn, hfsn⟩ := (inDom_iff_mem_lift hM hj hF.2.1 sn).2 hsnd
  -- the value of the inner `natRec` at `n`: the same `F`, restricted
  obtain ⟨d', hd', F', hF', hInv'⟩ := natRec_exists hM hj vC vz vs hty vn hnω
  have hnd' : M.T.mem vn d' := (hd' vn).2 (Or.inr rfl)
  obtain ⟨fn', hfn'⟩ := (inDom_iff_mem_lift hM hj hF'.2.1 vn).2 hnd'
  have hsub : (M.T.sortStr 1).Subset vn sn := fun z hz => (hsn z).2 (Or.inl hz)
  have efn : fn' = fn := natRec_agree hM hj vC vz vs hty hnω hd' hd hsub hF' hInv' hF vn hnd' fn' fn hfn' hfn
  subst efn
  have hg' : ∀ k, (![C, z, s, n] k).cls Γ = (Prim.natRec j).argSort k :=
    fun k => by fin_cases k <;> [exact hg 0; exact hg 1; exact hg 2; exact hcn]
  have hinner := natRec_val hM j hj ![C, z, s, n] hg' hvC hvz hvs hvn hty hnω hd' hF' hInv' hfn'
  -- the step: `F (n + 1) = s n (F n)`
  have hty' := hty
  obtain ⟨-, hsfun, hstep⟩ := hty'
  obtain ⟨g, hsg, hgfun, r, hr, -⟩ := hstep vn hnω sn hsn fn' (hInv' vn hnd' fn' hfn')
  have hFsn := hF.2.2.2 vn ((hsn vn).2 (Or.inr rfl)) sn hsn fn' hfn _ hsg g rfl _ hr r rfl
  have er : fsn = r := (hM.sortModel j).funApp_unique hF.1 hfsn hFsn
  subst er
  -- the values of the two sides
  have houter := natRec_val hM j hj _ hg hvC hvz hvs hvn1 hty hn1ω hd hF hInv hfsn
  have hvs' : ∀ w, Val M.T Γ s η w ↔ w = M.T.inj vs := hvs
  have hcs : s.cls Γ = max 1 (max j j) := hg 2
  have hsn_val := app_data_val hM hcs hcn (le_max_right _ _) (le_max_left _ _) hvs' hvn hsfun hsg
  rw [houter, app_data_val hM (n := max j j) (k := j) rfl rfl (le_max_right j j) (le_max_left j j) hsn_val
    hinner hgfun hr]

/-! ### Quotients -/

theorem eq_quotLiftMk (i j : ℕ) (A R C f h a : Term) (hi : 1 ≤ i) (hj : 1 ≤ j)
    (hg : ∀ k, (![A, R, C, f, h, prim (.quotMk i) ![A, R, a]] k).cls Γ = (Prim.quotLift i j).argSort k)
    (ih : ∀ k, PTy hM Γ (![A, R, C, f, h, prim (.quotMk i) ![A, R, a]] k)
      ((Prim.quotLift i j).argType m ![A, R, C, f, h, prim (.quotMk i) ![A, R, a]] k)
      ((Prim.quotLift i j).argSort k))
    (hca : a.cls Γ = i) (ha : PTy hM Γ a A i) :
    PEq hM Γ (prim (.quotLift i j) ![A, R, C, f, h, prim (.quotMk i) ![A, R, a]]) (app .data j f a) C j := by
  refine ⟨case_quotLift hM i j _ ⟨hi, hj⟩ hg ih, fun η hv w => ?_⟩
  obtain ⟨vA', vR, Q, vB', vf, vh, vq, hvA, hvR, -, hQ, hvB, hBU, hvf, hffun, hf', hresp, hvh, hvq, hq⟩ :=
    quotLift_data hM i j _ hg ih hv
  obtain ⟨va, hva, hamem⟩ := elem_arg_vals hM ha hv hvA
  have ha' : M.T.mem (M.T.j i va) (M.T.j i vA') := (hM.j_mem_iff i va vA').2 hamem
  obtain ⟨c, hc⟩ := exists_classSet hM vA' vR va
  have hmk := quotMk_val hM i ![A, R, a] (fun k => by fin_cases k <;> [exact hg 0; exact hg 1; exact hca])
    hvA hvR hva hc
  have e : vq = c := Sorted.inj_injective M.T.U ((hmk _).1 ((hvq _).2 rfl))
  subst e
  obtain ⟨fa, hfa, -⟩ := hf' va ha'
  have hvf' : ∀ w, Val M.T Γ f η w ↔ w = M.T.inj vf := hvf
  have hcf : f.cls Γ = max i j := hg 3
  rw [quotLift_val hM i j _ hg hvA hvR hvB hvf hffun hf' hresp hvh hvq ha' hc hfa,
    app_data_val hM hcf hca (le_max_right i j) (le_max_left i j) hvf' hva hffun hfa]

end Eq

end SolidLean.Calc
