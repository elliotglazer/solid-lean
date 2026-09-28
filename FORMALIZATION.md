# The formalization: what is checked, how it is organized, where it departs from the paper

Companion to `Solid-idealized-Lean.md` (section numbers below refer to it) and to its §8, which gives the claim-by-claim status. This file is the map of the Lean development `Solid/`: the statement that is checked, the architecture in import order, the design decisions that differ from the paper's presentation, and the points at which the formalization refines the text.

Everything in `Solid/` compiles with Lean 4.33.0 and Mathlib v4.33.0, with no `sorry`; every theorem named here depends only on the axioms `propext`, `Classical.choice`, `Quot.sound` (`lake env lean scratch/Axioms.lean`). 65 modules, about 22,000 lines.

## 1. What is checked

Four theorems, each for *arbitrary* models with a class system, never for standard models:

1. **H is solid** (`Solidity.lean`: `tower_solid`). For models `M ⊳ N ⊳ P` of the tower theory `H` (`IsTowerModel`), where `N` carries a class system below the one induced from `M` and `P` an arbitrary one, an `M`-definable isomorphism `M ≅ P` yields an `M`-definable isomorphism `M ≅ N`. Interpretations are in one-coordinate normal form (§1.2 of the paper; each interpreted sort is a definable class of one sort modulo a definable equivalence), and "definable" is membership in a class system, so the theorem applies to any notion of definability closed under the first-order operations, in particular to parametric first-order definability (`Gen/Definable.lean`: `Str.defSys`; first-order form `Gen/Translate.lean`: `solid_fo`).
2. **Clause expansions of H are solid** (`Gen/Expansion.lean`: `ClauseFamily.solid`), and every model of `H` expands to a model of the expansion (`Gen/Clauses.lean`: `expand_isGenModel`). A clause family adds to the tower signature relation symbols each defined by a clause that is definable in every class system and invariant under tower isomorphisms; formula clauses qualify (`ClauseFamily.ofFormulas`).
3. **The calculus.** `T_L` is the clause family with one symbol `R_{Γ,t}` per context and annotated term, defined by the evaluator clause `eval Γ t` (`Calc/Theory.lean`: `LAnn`); so `T_L` is solid (`TL_solid`, `TL_solid_fo`) and has the models of `H` (`TL_expand`). Soundness, Theorem 4.1: every certified `Γ ⊢ t : A @ r` has, in every model of `H` and every valid environment, a unique value, lying in the unique value of `A`, which lies in `U_r` (`Calc/Soundness.lean`: `soundness`, `soundness_defEq`), for the whole calculus of §3 and §3.4: universes, Π/λ/app/let in both kinds, the 32 primitives and their 12 computation rules. Adequacy: in the canonical `T_L`-model of a model of `H`, `R_{Γ,t}` is the value relation, and for closed terms the singleton of the value (`Calc/Adequacy.lean`: `adequacy_closed`). Lemma 3.2 (`Calc/Typing.lean`: `cls_of_typed`) and the type-classifier invariant (`Calc/TyOk.lean`: `tyOk_of_typed`).
4. **Definable-sort expansions** (§6.3). An expansion of a solid clause-family theory by definable sorts — new sorts that are copies of definable subsets of old sorts, with an encoding symbol each and further symbols defined by clauses — is solid (`Gen/SortSolid.lean`: `SortExp.solid`), every model of the base theory expands canonically (`Gen/SortExpand.lean`: `SortExp.expand_isModel`), and isomorphisms of base reducts extend (`Gen/SortIso.lean`: `SortExp.extend`). The instance is the `B_n/E_n` presentation of `T_L` (`Calc/BE.lean`: `BE`, `BE_solid`, `BE_expand`, `BE_reduct`).

## 2. Architecture, in import order

### Layer 1 — the tower theory H and its solidity (`Solid/*.lean`, paper §1–2)

| File | Content |
| --- | --- |
| `Tower.lean` | `MemTower` (sorted carrier, membership, transitions `j`, cutoffs `κ`), `ClassSystem` with per-sort atoms, `liftLE` (iterated transitions), `Presentation` |
| `SetTheory.lean` | `MemStr`, the internal notions (ordinals, functions, ranks, inaccessibility, …), `SetClassSystem`, `SetAxioms`, `ZFCModel` |
| `TowerTheory.lean` | `TowerWithClasses`, `IsTowerModel` — the axioms of `H` (§2.1) |
| `Interpretation.lean` | `SInterp`/`Interp` (one-coordinate normal form), the induced class system, presentations, `TowerIso.DefinableIn` |
| `Internal.lean` | Separation helpers, foundation for definable classes, ordinal trichotomy |
| `Def.lean` | the definability calculus `𝒞.Def k P` with combinators and certificates for every notion of `SetTheory.lean`; `sepP`, `replP`, `class_foundationP` |
| `SortModel.lean` | each sort of a model of `H` is a `ZFCModel` |
| `Rank.lean` | pairs, functions, domains; rank theory through attempts: `V_α` unique, transitive, subset-closed, monotone, `α ∉ V_α` |
| `Absolute.lean` | `InnerEmb` and absoluteness of every notion along it, including `Inaccessible`, `NextInaccessible`, `NoGreatestInaccessibleBelow`; `IsV` upward |
| `Lift.lean` | `j n` and `liftLE` are inner embeddings between the sort models |
| `Mostowski.lean` | internal collapse of a well-founded set relation by attempts; uniqueness modulo a set equivalence |
| `TDef.lean` | the many-sorted definability calculus `𝒟.TDef k P`; bridges to sort systems |
| `Graphs.lean` | representatives and composition of presentations; `PGraph`, closed under lifts and transitions |
| `Collapse.lean` | `CollapseData` (the output of Steps 1–3) and Step 4 by transport along `e (n+1)` |
| `Config.lean` | the configuration `M ⊳ N ⊳ P`; composite definability (`composite_def`, `composite_lift_def`) |
| `Level.lean` | one-sort collapses and their lifts; Step 2 (uniqueness of the collapse, by foundation) |
| `Step1.lean`, `Step1b.lean` | domain, membership and equivalence of an interpreted sort as sets; Step 1 (well-foundedness by pullback along `i`); the collapse of one sort of `P`; Step 3 (subset-closure via Separation in `M`) |
| `Assemble.lean` | monotone placement of sorts, `Config.collapseData` |
| `Step5.lean`, `Step5b.lean` | Step 5a (`bottom_le_kappa`, the ladder of named cutoffs) and propagation; Step 5b (`not_all_below_bottom`, the finite-support obstruction) |
| `Step6.lean` | Step 6: `δ n = κ n`, `S n = V(κ n)`, the assembled definable isomorphism |
| `Solidity.lean` | `TowerTheorySolid`, `tower_solid` |

### Layer 2 — general interpretations, clause expansions, the first-order bridge (`Solid/Gen/`, paper §1, §4, §6)

| File | Content |
| --- | --- |
| `Core.lean`, `Signature.lean`, `GenInterp.lean` | sorted carriers with class systems; relational signatures (`arity`, `sortAt`); `GenInterp`, interpretations of an arbitrary signature in a carrier, induced class systems, presentations, definable isomorphisms, composition |
| `Transport.lean` | transport of class systems, of `SetAxioms` and of `IsTowerModel` along isomorphisms; `TowerIso.symm/trans/pullRel` |
| `Expansion.lean` | `TowerSym`, `ClauseFamily`, its signature, `IsWF`, the tower reduct `Δ`/`ΔSys`, `IsGenModel`, `GenInterp.toTower`; **`ClauseFamily.solid`** |
| `FO.lean` | many-sorted first-order formulas, `Sat`, `Def`, `def_mem` (definable ⇒ in every class system), `sat_map` (invariance under isomorphism), renaming, derived connectives |
| `Clauses.lean` | the tower signature as a `Signature`, `MemTower.toStr`, `ClassSystem.toStrSys`, **`ClauseFamily.ofFormulas`**, **`ClauseFamily.expand` + `expand_isGenModel`** |
| `Definable.lean` | relations definable with parameters (`Formula.SortedDef`) form a class system: **`Str.defSys`** |
| `Translate.lean` | fixing parameters in a class system; **`GenInterp.defSys_le_induced`** (the translation lemma: relations definable in an interpreted structure have definable preimages); **`ClauseFamily.solid_fo`**, **`TL_solid_fo`** |
| `Push.lean` | codings of sorted carriers, images and preimages of classes, `GenInterp.push` (an interpretation pushed along a compatible coding, with `pushIso`), definable isomorphisms through representatives (`repGraph`, `definableIn_pres_iff`, `definableIn_comp_iff`) |
| `ClassOps.lean` | closure operations of class systems: quantifying away coordinates, images under admissible relations, relational composition and converse |
| `BaseSys.lean` | the class system of a reduct to a subfamily of sorts |
| `SortExp.lean` | **`SortExp F`**, definable-sort expansions of a clause family, their models (`IsModel`), the base reduct, the flattening coding `flat` and its compatibility |
| `SortIso.lean` | **`SortExp.extend`**: an isomorphism of base reducts extends to the expansion |
| `SortSolid.lean` | **`SortExp.solid`**: flatten the interpretations onto the base sorts, apply `F.solid`, extend |
| `SortExpand.lean` | **`SortExp.expand_isModel`**: the canonical expansion of a model of the base theory, built as an interpretation of the expanded signature |

### Layer 3 — the calculus L_ann and T_L (`Solid/Calc/`, paper §3–5)

| File | Content |
| --- | --- |
| `Syntax.lean` | terms (de Bruijn levels; var/univ/pi/lam/app/letE with kinds and levels; the 32 primitives `Prim` with argument sorts, types, result types, levels, side conditions `Prim.Ok`), contexts `Ctx m`, the classifier `Term.cls` |
| `Typing.lean` | `CtxOk`/`Typed`/`DefEq` (mutual): the rules of §3.2, the primitive rule and the 12 computation rules; Lemma 3.2 **`cls_of_typed`**, `cls_of_defEq` |
| `TowerFormula.lean`, `SetFormulas.lean` | atoms of the tower signature with sort obligations, iterated lifts, constant-sort notions (pairs, functions, application, truth values) with satisfaction lemmas |
| `Eval.lean` | the evaluator `eval Γ t`: one tower formula per term, by recursion on raw annotated syntax (§4.3); incoherent annotations evaluate to `false` |
| `Theory.lean` | `Sym := Σ m, Ctx m × Term`, **`LAnn`** (T_L as a clause family), **`TL_solid`**, **`TL_expand`** |
| `Semantics.lean` | the value relation `Val`, valid environments `EnvOk`, `IsTV`, `IsPiFun`, `IsUnivSet`, `FamOk`, and the element-level reading of every clause |
| `Contexts.lean`, `Envs.lean`, `Weakening.lean`, `Substitution.lean` | insertion of binders and substitution on contexts and environments; **`Val_shift`**, **`Val_subst`** (§4.4) |
| `Definability.lean` | satisfaction with parameters is a class of the sort system (`sortDef_sat`, …) |
| `Sets.lean` | in a model of `H`: the universes `univSet n`, truth values, dependent products (Power Set + Separation), graphs, codomains (Replacement + Union) |
| `TyOk.lean` | the type-classifier invariant **`tyOk_of_typed`** |
| `SnocLits.lean`, `PrimSimpAttr.lean` | bookkeeping for environment literals and simp sets |
| `PrimClauses.lean`, `PrimSemantics.lean`, `PrimRel.lean` | the evaluator clause of each primitive and its element-level reading; generic tools |
| `PrimSets.lean` | the set constructions the primitives need: pairs, tagged unions, ω and recursion, quotients, truncation, equality types, the choice function (`exists_choiceFun`, by Replacement, Separation and the sort's Choice) |
| `SoundBase.lean`, `PrimSound.lean`, `PrimEq.lean` | the soundness cases: one lemma per rule of the core, one per primitive (`case_prim`), one per computation rule |
| `Soundness.lean` | `TMem`, `Valid`, the mutual induction `sound_typed`/`sound_defEq`; **`soundness`**, **`soundness_defEq`**, `soundness_closed` |
| `Adequacy.lean` | `mem_expand_rel_iff`, **`adequacy_closed`** |
| `BE.lean` | the `B_n/E_n` presentation as `BE : SortExp LAnn`; **`BE_solid`**, **`BE_expand`**, **`BE_reduct`** |

## 3. Design decisions

These are choices of presentation; each is a strengthening or a rearrangement of the paper's argument, not a change of statement.

1. **One-coordinate normal form.** An interpreted sort is a definable class of a single source sort modulo a definable equivalence (`SortInterp`: `a`, `dom`, `eqv`). In a ZFC sort finite tuples are coded by single elements, so this loses no generality against tuple domains; that reduction is a remark in the paper and is not formalized. Equality is interpreted as an arbitrary definable equivalence throughout; the quotient case is never assumed away (paper, Remark (iv) after Theorem 2.1).
2. **Class systems instead of a fixed notion of definability.** `tower_solid` is stated for models carrying class systems: `M` an arbitrary one, `N` one lying below the system induced from `M` through the interpretation (Enayat's hypothesis gives `N ⊨ H` only for `N`'s own definable classes), `P` arbitrary. The parametrically definable relations of a first-order structure form such a system (`Str.defSys`), and syntactic interpretations satisfy the "below the induced system" condition (`defSys_le_induced`); this is how the semantic theorem yields Enayat's first-order statement (`solid_fo`).
3. **Per-sort atoms.** A class system's atoms (`memRel n`, `jRel n`) are stated per sort; the global relations over all sorts are not classes, since a first-order definable relation has a fixed finite profile.
4. **The set-encoded signature.** `T_L` is formalized with the tower sorts `Z_n` as its sorts and one relation symbol per (context, term), rather than with the sorts `B_n, E_n, Ω` and the constants `code_n, value_n` of §6: `D` is then the reduct, `F` the expansion by clauses, and `ε, ρ` are identities, so §§5–7 collapse to the two general theorems of Layer 2. The internal set tower of §5 (`Z_n` as a W-type quotient inside L_ann) is not constructed; the tower is primitive, which makes the round trip `ε` trivial. The presentation of §6.3 is recovered by the definable-sort expansion `BE`, in which `Ω = B_0` and `Code_r`, `Value_r` are the encoding symbols of the new sorts.
5. **Values in the sort of their classifier.** A term with classifier `c` has its value in sort `c`; types live one sort above their elements, membership is read through `j`; universes are `j`-images, `U_0` the set of truth values (`Calc/Eval.lean`, `Calc/Sets.lean`).
6. **Heights live one sort up** (Step 4): `δ n := e (n+1) (κ n)` is placed in sort `b (n+1)` and `S n = V(δ n)` is asserted after lifting, so Step 4 is pure transport of `P`'s axioms along the inner embedding `e (n+1)`; no downward absoluteness of `IsV` is needed, and no existence theorem for `V_α` — only the attempt-level facts.
7. **Step 2 by foundation, not by induction over `P`**; **Step 3 is exactly supertransitivity** of the collapsed set, which is what makes `e (n+1)` an inner embedding; **Step 6 definability is one lemma** (`Config.composite_lift_def`), which also drives Step 5b.
8. **`IsTowerModel` was never strengthened**: transitivity and subset-closure of `V(κ n)` are derived from the axiom `j_image` via the rank theory, and absoluteness of inaccessibility along the transitions is proved, not assumed.

## 4. Where the formalization refines the paper

Points at which the text had to be sharpened for the proof to go through; each is recorded in the paper's §8.

1. **Nat-rec successor rule** (§3.4). The right-hand side of `natRecSucc` had an ill-sorted inner application; the step function lives at sort `max j j`.
2. **Side conditions `Prim.Ok`** (§3.4). Σ, sums, sum-rec, Nat-rec, quotients and choice need level ≥ 1 in the data position; in particular `choice` needs `1 ≤ j`, because the choice function is built by Replacement and Separation at sort `j`, which needs a full universe there.
3. **The product guard `famOkF`** (§4.3). A product `Π(x:A).B` has a value only if `A` has a unique value `vA` and `B` has a unique value in `U_j` at every element of `vA`. On certified terms the guard is always satisfied, so it does not change the interpretation of the calculus; it is what lets the application case of the soundness proof reason about the codomain family from the value of the type of `f` alone, without inversion lemmas. The guard is first-order, so `T_L` remains a clause expansion of `H`.
4. **Step 5b uses no choice function and no Cantor.** The definable relation "`r ∈ M_K` represents the `N_0`-element under `e (i x)`" is total and injective in `x`; Replacement along its inverse makes the universe of sort `K+1` a set, contradicting irreflexivity.
5. **The type-classifier invariant** (`TyOk`): the type of a certified term has classifier `r + 1`, recursively through the domain and codomain of every product appearing as a type. It complements Lemma 3.2 and is proved by a direct induction, with no inversion lemmas.
6. **`Ω = B_0`, and `Code_n`, `Value_n` are the encoding symbols** of the sorts in the `B_n/E_n` presentation; axiom 6 of the representation scheme is void once the tower is primitive.

## 5. Not formalized

- The syntactic side: derivability in `H` and in `T_L` (Theorem 4.1 as a proof-producing function, Claim 6.1 (i)–(ii), the provable forms of §7.4–7.5). Everything is semantic; completeness supplies provability.
- The primitive stock beyond the 32 constants: W-types, accessibility and the indexed inductive discipline (Nat stands in for the recursive types).
- The internal tower of §5 and the round trip `ε` (replaced by the encoded presentation, decision 4), and the identification of the paper's `T_L` (symbols for primitives, graphs by recursion) with the formal one (a symbol per term).
- The finite-tuple normalization of §1.2 (decision 1), and Lemma 1.2 as a general transfer lemma (the two transfers the development needs are proved directly).
- Level determinacy (§3.3 ii), shown unnecessary: neither soundness nor solidity uses it.

## 6. Building

    lake build Solid                    # ~700 jobs
    lake env lean scratch/Axioms.lean   # axiom report for every main theorem
