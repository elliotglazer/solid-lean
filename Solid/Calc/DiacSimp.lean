module

public import Mathlib.Tactic.Core

/-!
# The simp set for shifts and substitutions on the terms of Diaconescu's argument
-/

public meta section

/-- Simp lemmas computing `shift` and `subst` on the encoded terms of `Solid.Calc.Diaconescu`. -/
register_simp_attr diac_simps
