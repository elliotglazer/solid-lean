module

public import Solid.Calc.Eval

/-!
# The theory `T_L` of the core annotated calculus, and its solidity

`T_L` is the expansion of the tower theory `H` by one relation symbol
`R_{Γ,t}` per context `Γ` and term `t` of the core calculus, each defined by
the evaluator clause `eval Γ t` (draft 2, §6.3 in the set-encoded
signature; the symbol `R_{Γ,t}` is the graph `⟦t⟧_Γ`).  Its models are the
models of `H` (`ClauseFamily.expand`), and it is solid (`ClauseFamily.solid`).
-/

@[expose] public section

universe u

namespace SolidLean.Calc

open SolidLean.Solid

/-- The symbols of `T_L`: one graph symbol per context and term. -/
abbrev Sym : Type := Σ m : ℕ, Ctx m × Term

/-- The clause family of the core calculus: `R_{Γ,t}` has arity `|Γ| + 1`,
argument sorts the levels of `Γ` and the classifier of `t`, and clause
`eval Γ t`. -/
noncomputable def LAnn : ClauseFamily.{u} :=
  ClauseFamily.ofFormulas Sym (fun s => s.1 + 1) (fun s => Fin.snoc s.2.1.levels (s.2.2.cls s.2.1))
    (fun s => eval s.2.1 s.2.2)

/-- The theory `T_L`: the axioms of `H` for the tower symbols, and the
defining axiom of each graph symbol. -/
abbrev IsTLModel (M : StrWithSys.{u} LAnn.sig) : Prop := LAnn.IsGenModel M

/-- **The core annotated calculus is solid** (draft 2, Theorem 7.2, in the
set-encoded signature). -/
theorem TL_solid : LAnn.{u}.IsSolid := ClauseFamily.solid LAnn

/-- **Every model of `H` expands to a model of `T_L`** (draft 2, Proposition 7.1). -/
theorem TL_expand (T : TowerWithClasses.{u}) (hT : IsTowerModel T) :
    IsTLModel (LAnn.expand T) := LAnn.expand_isGenModel T hT

end SolidLean.Calc
