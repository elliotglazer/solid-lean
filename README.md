# solid-lean

Machine-checked solidity of an idealized Lean.

The paper `Solid-idealized-Lean.md` specifies an idealized dependent type theory
L_ann — Lean's kernel type theory with a fixed stock of inductive types,
annotated so that the universe level and the proof/data kind of every subterm
can be read off the syntax — and extends it by a representation scheme to a
theory L_solid that is bi-interpretable with H, the many-sorted theory of a
tower of ZFC universes cut at consecutive inaccessibles. H is *solid* in
Enayat's sense, and therefore so is L_solid: it determines its models up to
definable isomorphism in the way ZF or PA does and ordinary type theories do
not.

The Lean 4 library `Solid/` checks the theorem for the relational form T_L of
L_solid: `lake build Solid` succeeds with no `sorry`, and every main theorem
depends only on `propext`, `Classical.choice`, `Quot.sound`.

## Layout

| Path | What it is |
| --- | --- |
| `Solid-idealized-Lean.md` | The paper. Section numbers below refer to it; its §8 records, claim by claim, what is proved, what is sketched, and what is machine-checked. |
| `FORMALIZATION.md` | The map of the Lean development: what is checked, the modules in import order, design decisions, and where the formalization refines the paper. |
| `Solid/` | The library (65 files, ~22k lines). Depends only on Mathlib. |
| `Solid/*.lean` (top level) | The many-sorted set tower H and its solidity (`tower_solid`). |
| `Solid/Gen/` | Generic first-order machinery: signatures, interpretations, class systems, clause expansions and their solidity, the first-order bridge, definable-sort expansions. |
| `Solid/Calc/` | The calculus L_ann: syntax, typing, evaluator clauses, semantics, soundness and adequacy, the theory T_L, the B_n/E_n presentation. |
| `Solid.lean` | Imports everything in `Solid/`. |
| `scratch/Axioms.lean` | `#print axioms` for every main theorem. |

## Main results

Layer 1 — the tower theory H (paper §1–2)

| Statement | Where |
| --- | --- |
| For models M ⊳ N ⊳ P of H and an M-definable isomorphism M ≅ P, there is an M-definable M ≅ N | `Solidity.lean`: `tower_solid` |
| The axioms of H (`IsTowerModel`), class systems, interpretations, the induced class system | `TowerTheory.lean`, `Tower.lean`, `Interpretation.lean` |
| Steps 1–6 of the proof: internal collapse, uniqueness, transport, the ladder, the finite-support obstruction, assembly | `Step1.lean` … `Step6.lean`, `Collapse.lean`, `Config.lean`, `Level.lean`, `Assemble.lean` |
| Internal set theory of a model: rank, absoluteness, Mostowski collapse, definability calculus | `Rank.lean`, `Absolute.lean`, `Mostowski.lean`, `Def.lean`, `TDef.lean`, `SortModel.lean` |

Layer 2 — clause expansions and the first-order bridge (paper §4, §6)

| Statement | Where |
| --- | --- |
| Expansions of H by clause-defined symbols are solid | `Gen/Expansion.lean`: `ClauseFamily.solid` |
| Every model of H expands to a model of the expansion | `Gen/Clauses.lean`: `ClauseFamily.expand_isGenModel` |
| Formulas, satisfaction, invariance under isomorphism, the definable class system `Str.defSys` | `Gen/FO.lean`, `Gen/Definable.lean` |
| Translation lemma: a syntactic interpretation's definable relations have definable preimages | `Gen/Translate.lean`: `GenInterp.defSys_le_induced` |
| Enayat's first-order form of solidity for clause expansions and for T_L | `Gen/Translate.lean`: `ClauseFamily.solid_fo`, `TL_solid_fo` |

Layer 3 — the calculus L_ann and T_L (paper §3–5)

| Statement | Where |
| --- | --- |
| Syntax (universes, Π/λ/app in data and proposition kinds, let, 32 primitives), typing, definitional equality | `Calc/Syntax.lean`, `Calc/Typing.lean` |
| Evaluator clauses, one tower formula per term | `Calc/Eval.lean`, `Calc/PrimClauses.lean` |
| Soundness (Theorem 4.1): every certified term has a unique value in every model of H, in its type's value | `Calc/Soundness.lean`: `soundness`, `soundness_defEq`; primitives in `Calc/PrimSound.lean`, `Calc/PrimEq.lean` |
| Lemma 3.2 (classifier coherence) and the type-classifier invariant | `Calc/Typing.lean`: `cls_of_typed`; `Calc/TyOk.lean`: `tyOk_of_typed` |
| T_L as a clause family; it is solid, with the models of H | `Calc/Theory.lean`: `LAnn`, `TL_solid`, `TL_expand` |
| Adequacy (closed terms) | `Calc/Adequacy.lean`: `adequacy_closed` |

Layer 4 — the sort encoding and the B_n/E_n presentation (paper §6.3)

| Statement | Where |
| --- | --- |
| Definable-sort expansions of a clause family (`SortExp`) and their models | `Gen/SortExp.lean` |
| A definable-sort expansion of a solid theory is solid | `Gen/SortSolid.lean`: `SortExp.solid` |
| Every model of the base theory expands canonically to a model of the expansion | `Gen/SortExpand.lean`: `SortExp.expand_isModel` |
| Isomorphisms of base reducts extend to the expansion | `Gen/SortIso.lean`: `SortExp.extend` |
| The B_n/E_n presentation of T_L; it is solid and has the same models as T_L | `Calc/BE.lean`: `BE`, `BE_solid`, `BE_expand`, `BE_reduct` |
| Supporting machinery: pushing interpretations along codings, class-system operations, reduct systems | `Gen/Push.lean`, `Gen/ClassOps.lean`, `Gen/BaseSys.lean` |

## Suggested reading order

1. The paper's introduction and §8, then `FORMALIZATION.md`.
2. `Solid/Solidity.lean` (the statement), `Solid/TowerTheory.lean` (the axioms).
3. `Solid/Gen/Expansion.lean` (how solidity transfers to expansions).
4. `Solid/Calc/Typing.lean` and `Solid/Calc/Eval.lean` (the calculus and its clauses),
   then `Solid/Calc/Soundness.lean`.
5. `Solid/Gen/SortExp.lean` → `SortSolid.lean` → `Calc/BE.lean`.

## Building

Lean `v4.34.0`, Mathlib `v4.34.0` and the `Foundation` library (first-order logic with completeness, used by `Solid/FO`) pinned in `lake-manifest.json`.

    lake build Solid                    # ~700 jobs
    lake env lean scratch/Axioms.lean   # axiom report for every main theorem

## Where the formalization refines the paper

Listed in `FORMALIZATION.md`, §4, and in the paper's §8: the Nat-rec successor
rule and the side conditions of the primitives (§3.4), the product guard in the
evaluator (§4.3), and the identification Ω = B_0 with `Code_n`, `Value_n` as the
encoding symbols of the new sorts in the B_n/E_n presentation (§6.3).
