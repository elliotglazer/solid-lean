module

public import Mathlib.Tactic.Core

/-!
# The simp set for reading the clauses of the primitives
-/

public meta section

/-- Simp lemmas unfolding the satisfaction of a clause at a tuple of sorted values. -/
register_simp_attr prim_simps
