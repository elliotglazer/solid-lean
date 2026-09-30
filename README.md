# solid-lean

Machine-checked solidity of an idealized Lean.

The paper `Solid-idealized-Lean.md` specifies an idealized dependent type theory
L_ann. It is Lean's kernel type theory with a fixed stock of inductive types,
annotated so that the universe level and the proof/data kind of every subterm
can be read off the syntax. The paper extends it by a representation scheme to
a theory L_solid that is bi-interpretable with H, the many-sorted theory of a
tower of ZFC universes cut at consecutive inaccessibles. H is *solid* in
Enayat's sense, and therefore so is L_solid. A solid theory determines its
models up to definable isomorphism in the way ZF or PA does and ordinary type
theories do not.

The Lean 4 library `Solid/` checks the theorem for the relational form T_L of
L_solid. `lake build Solid` succeeds with no `sorry`, and every main theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`.

The tower half of the theorem, "H is solid" (Theorem 2.1 of the paper), is a registered
entry of the Palomar registry: [PALOMAR-2026-09-30-000022](https://palomar-registry.org/entry?id=PALOMAR-2026-09-30-000022&version=1), version 1, verified at commit
`337e7a5afd81ee7236c0e0dceadbc8cfc313f83f` against the trusted statement in `Palomar/Challenge.lean`.

## Layout

| Path | What it is |
| --- | --- |
| `Solid-idealized-Lean.md` | The paper. Section numbers below refer to it; its §8 records, claim by claim, what is proved, what is sketched, and what is machine-checked. |
| `FORMALIZATION.md` | The map of the Lean development: what is checked, the modules in import order, design decisions, and where the formalization refines the paper. |
| `Solid/` | The library (74 files, about 27,000 lines). Depends on Mathlib and on the Foundation library (first-order logic with soundness and completeness). |
| `Solid/*.lean` (top level) | The many-sorted set tower H and its solidity (`tower_solid`). |
| `Solid/Gen/` | Generic first-order definitions and lemmas: signatures, interpretations, class systems, clause expansions and their solidity, the first-order bridge, definable-sort expansions. |
| `Solid/Calc/` | The calculus L_ann: syntax, typing, evaluator clauses, semantics, soundness and adequacy, the theory T_L, the B_n/E_n presentation. |
| `Solid/FO/` | H and T_L as first-order theories: the axioms as many-sorted sentences, their equivalence with the semantic axioms, the rendering in the Foundation library, and provability (Theorem 4.1 as an H-scheme, Claim 6.1 (i)–(ii), conservativity of T_L over H) by completeness. |
| `Solid.lean` | Imports everything in `Solid/`. |
| `Palomar/` | The registered statement and its proof, for the [comparator](https://github.com/leanprover/comparator) and the Palomar registry. `Challenge.lean` states Theorem 2.1, "H is solid", in about 400 lines that import only Mathlib basics, with the target left as `sorry`. `Statement.lean` is the generated copy of its definitions. `Bridge/` and `Solution.lean` prove the target from `tower_solid`. `comparator.json` at the root is the judge's configuration and `formalization.yaml` the registry metadata. Registered as [PALOMAR-2026-09-30-000022](https://palomar-registry.org/entry?id=PALOMAR-2026-09-30-000022&version=1). |
| `scratch/Axioms.lean` | `#print axioms` for every main theorem, including the registered one. |
| `scripts/sync_statement.py` | Regenerates or checks `Palomar/Statement.lean`. |

## Main results

### The tower theory H (paper §1–2)

| Statement | Where |
| --- | --- |
| For models M ⊳ N ⊳ P of H and an M-definable isomorphism M ≅ P, there is an M-definable M ≅ N | `Solidity.lean`: `tower_solid` |
| The same as a self-contained first-order statement in Enayat's form. The trusted file defines structures, many-sorted formulas, definability with parameters, the axioms of H with the schemes over all definable classes, interpretations in one-coordinate normal form, and definable isomorphisms; nothing from `Solid/` is trusted. | `Palomar/Challenge.lean`: `Solid`, `tower_theory_solid`; proved in `Palomar/Solution.lean`; registry entry [PALOMAR-2026-09-30-000022](https://palomar-registry.org/entry?id=PALOMAR-2026-09-30-000022&version=1) |
| The axioms of H (`IsTowerModel`), class systems, interpretations, the induced class system | `TowerTheory.lean`, `Tower.lean`, `Interpretation.lean` |
| Steps 1–6 of the proof: internal collapse, uniqueness, transport, the ladder, the finite-support obstruction, assembly | `Step1.lean` … `Step6.lean`, `Collapse.lean`, `Config.lean`, `Level.lean`, `Assemble.lean` |
| Internal set theory of a model: rank, absoluteness, Mostowski collapse, definability calculus | `Rank.lean`, `Absolute.lean`, `Mostowski.lean`, `Def.lean`, `TDef.lean`, `SortModel.lean` |

### Clause expansions and the first-order bridge (paper §4, §6)

| Statement | Where |
| --- | --- |
| Expansions of H by clause-defined symbols are solid | `Gen/Expansion.lean`: `ClauseFamily.solid` |
| Every model of H expands to a model of the expansion | `Gen/Clauses.lean`: `ClauseFamily.expand_isGenModel` |
| Formulas, satisfaction, invariance under isomorphism, the definable class system `Str.defSys` | `Gen/FO.lean`, `Gen/Definable.lean` |
| Translation lemma: a syntactic interpretation's definable relations have definable preimages | `Gen/Translate.lean`: `GenInterp.defSys_le_induced` |
| Enayat's first-order form of solidity for clause expansions and for T_L | `Gen/Translate.lean`: `ClauseFamily.solid_fo`, `TL_solid_fo` |

### The calculus L_ann and T_L (paper §3–5)

| Statement | Where |
| --- | --- |
| Syntax (universes, Π/λ/app in data and proposition kinds, let, 32 primitives), typing, definitional equality | `Calc/Syntax.lean`, `Calc/Typing.lean` |
| Evaluator clauses, one tower formula per term | `Calc/Eval.lean`, `Calc/PrimClauses.lean` |
| Soundness (Theorem 4.1): every certified term has a unique value in every model of H, in its type's value | `Calc/Soundness.lean`: `soundness`, `soundness_defEq`; primitives in `Calc/PrimSound.lean`, `Calc/PrimEq.lean` |
| Lemma 3.2 (classifier coherence) and the type-classifier invariant | `Calc/Typing.lean`: `cls_of_typed`; `Calc/TyOk.lean`: `tyOk_of_typed` |
| T_L as a clause family; it is solid, with the models of H | `Calc/Theory.lean`: `LAnn`, `TL_solid`, `TL_expand` |
| Adequacy (closed terms) | `Calc/Adequacy.lean`: `adequacy_closed` |
| The primitive `dne` is redundant. A certified closed term of type `Π (P : U_0). ((P → False) → False) → P`, built from propositional choice, `propext`, Σ, Lift, Trunc and `Eq.rec` by Diaconescu's argument, derives the rule of `dne` in every well-formed context, and the term does not mention `dne` | `Calc/Diaconescu.lean`: `dne_derivable`, `dne_derived`, `dneTerm_usesDne` |

### The sort encoding and the B_n/E_n presentation (paper §6.3)

| Statement | Where |
| --- | --- |
| Definable-sort expansions of a clause family (`SortExp`) and their models | `Gen/SortExp.lean` |
| A definable-sort expansion of a solid theory is solid | `Gen/SortSolid.lean`: `SortExp.solid` |
| Every model of the base theory expands canonically to a model of the expansion | `Gen/SortExpand.lean`: `SortExp.expand_isModel` |
| Isomorphisms of base reducts extend to the expansion | `Gen/SortIso.lean`: `SortExp.extend` |
| The B_n/E_n presentation of T_L; it is solid and has the same models as T_L | `Calc/BE.lean`: `BE`, `BE_solid`, `BE_expand`, `BE_reduct` |
| Supporting lemmas: pushing interpretations along codings, class-system operations, reduct systems | `Gen/Push.lean`, `Gen/ClassOps.lean`, `Gen/BaseSys.lean` |

### The first-order presentation and provability (paper §2.1, §4, §6.3, §7.5)

| Statement | Where |
| --- | --- |
| The axioms of H, and of any clause expansion T(𝔉), as many-sorted sentences: ZFC at every sort with Separation and Replacement as schemes, well-formedness of the tower symbols, the tower axioms, one defining axiom per symbol | `FO/Notions.lean`, `FO/Axioms.lean`: `Hax`, `TLax` |
| A structure satisfies the sentences iff it is a semantic model with its definable classes | `FO/Bridge.lean`, `FO/Sound.lean`: `ClauseFamily.models_iff_isGenModel` |
| The rendering in single-sorted first-order logic (sorts as predicates), both ways; derivability in the sequent calculus LK from the rendered axioms is exactly truth in every semantic model | `FO/Render.lean`: `Render.provable_iff_semantic` |
| H and T_L as Foundation theories; Theorem 4.1 as an H-scheme, provably (every certified judgement's soundness sentence; every certified definitional equality); Claim 6.1 (i) and (ii) | `FO/Provable.lean`: `H_FO`, `TL_FO`, `H_soundness`, `H_soundness_defEq`, `TL_adequacy`, `H_truth`, `TL_truth` |
| T_L is a conservative extension of H (§7.5 in the encoded presentation) | `FO/Conservative.lean`: `TL_conservative` |

## Suggested reading order

1. The paper's introduction and §8, then `FORMALIZATION.md`.
2. `Solid/Solidity.lean` (the statement), `Solid/TowerTheory.lean` (the axioms).
3. `Solid/Gen/Expansion.lean` (how solidity transfers to expansions).
4. `Solid/Calc/Typing.lean` and `Solid/Calc/Eval.lean` (the calculus and its clauses),
   then `Solid/Calc/Soundness.lean`; `Solid/Calc/Diaconescu.lean` for a derivation inside the calculus.
5. `Solid/Gen/SortExp.lean`, then `SortSolid.lean`, then `Calc/BE.lean`.
6. `Solid/FO/Axioms.lean` (the sentences), `FO/Bridge.lean` and `FO/Sound.lean`
   (the sentences are equivalent to the semantic axioms), `FO/Render.lean` (the
   Foundation rendering, soundness and completeness), `FO/Provable.lean` (what H
   and T_L prove).

## Building

Lean `v4.35.0-rc3`, Mathlib `v4.35.0-rc3` and the `Foundation` library (first-order logic with completeness, used by `Solid/FO`) are pinned in `lake-manifest.json`. Every file uses the module system (`module` header, `public import`, `@[expose] public section`), as the Palomar registry requires.

    lake build Solid Palomar            # ~1100 jobs (Mathlib and Foundation cones included)
    lake env lean scratch/Axioms.lean   # axiom report for every main theorem
    python3 scripts/sync_statement.py --check   # Palomar/Statement.lean is the copy of the Challenge

To run the judge on the registered statement (`comparator.json`), build
[`lean4export`](https://github.com/leanprover/lean4export) at tag `v4.35.0-rc3` and the
[comparator](https://github.com/leanprover/comparator) at its `v4.35.0-rc3` revision
(`fd5d5bcf`), then run from the repository root

    COMPARATOR_LANDRUN=<comparator>/scripts/fake-landrun.sh \
    COMPARATOR_LEAN4EXPORT=<lean4export>/.lake/build/bin/lean4export \
    lake env <comparator>/.lake/build/bin/comparator comparator.json

The shim replaces the `landrun` sandbox, which the registry runs for real. The CI
workflow does all of this on every push.

## Where the formalization refines the paper

Listed in `FORMALIZATION.md`, §4, and in the paper's §8: the Nat-rec successor
rule and the side conditions of the primitives (§3.4), the product guard in the
evaluator (§4.3), and the identification Ω = B_0 with `Code_n`, `Value_n` as the
encoding symbols of the new sorts in the B_n/E_n presentation (§6.3).
