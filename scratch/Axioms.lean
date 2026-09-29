module

public import Solid
public import Palomar.Solution

@[expose] public section

open SolidLean.Solid
#print axioms SInterp.induced
#print axioms TowerTheorySolid
#print axioms tower_solid
#print axioms tower_solid_induced
#check @tower_solid

#print axioms ClauseFamily.solid
#print axioms ClauseFamily.IsSolid
#check @ClauseFamily.solid

open SolidLean.Calc in #print axioms SolidLean.Calc.TL_solid
open SolidLean.Calc in #print axioms SolidLean.Calc.TL_expand
#check @SolidLean.Calc.TL_solid
#print SolidLean.Solid.ClauseFamily.IsSolid

#print axioms SolidLean.Calc.soundness
#print axioms SolidLean.Calc.soundness_defEq
#print axioms SolidLean.Calc.soundness_closed
#print axioms SolidLean.Calc.tyOk_of_typed
#check @SolidLean.Calc.soundness
#check @SolidLean.Calc.soundness_closed
#print axioms SolidLean.Calc.adequacy_closed
#check @SolidLean.Calc.adequacy_closed

#print axioms SolidLean.Calc.case_prim
#print axioms SolidLean.Calc.eq_congrPrim
#print axioms SolidLean.Calc.exists_choiceFun
#print axioms SolidLean.Calc.natRec_exists

#print axioms SolidLean.Solid.GenInterp.defSys_le_induced
#print axioms SolidLean.Solid.ClauseFamily.solid_fo
#print axioms SolidLean.Calc.TL_solid_fo
#check @SolidLean.Calc.TL_solid_fo

#print axioms SolidLean.Solid.SortExp.solid
#check @SolidLean.Solid.SortExp.solid
#print axioms SolidLean.Calc.BE_solid
#check @SolidLean.Calc.BE_solid
#print SolidLean.Solid.SortExp.IsSolid
#print axioms SolidLean.Solid.SortExp.expand_isModel
#print axioms SolidLean.Calc.BE_expand
#print axioms SolidLean.Calc.BE_reduct
#check @SolidLean.Calc.BE_expand
#check @SolidLean.Calc.BE_reduct

-- First-order presentation (FO/)
#print axioms SolidLean.Solid.ClauseFamily.isGenModel_of_models
#check @SolidLean.Solid.ClauseFamily.isGenModel_of_models
#print axioms SolidLean.Solid.Render.tr_sat
#print axioms SolidLean.Solid.Render.provable_of_semantic
#check @SolidLean.Solid.Render.provable_of_semantic
#print axioms SolidLean.Calc.H_soundness
#check @SolidLean.Calc.H_soundness
#print axioms SolidLean.Calc.H_soundness_defEq
#check @SolidLean.Calc.H_soundness_defEq
#print axioms SolidLean.Calc.TL_soundness
#print axioms SolidLean.Calc.TL_adequacy
#check @SolidLean.Calc.TL_adequacy
#print axioms SolidLean.Calc.H_truth
#check @SolidLean.Calc.H_truth
#print axioms SolidLean.Calc.TL_truth
#check @SolidLean.Calc.TL_truth
#print axioms SolidLean.Solid.ClauseFamily.models_iff_isGenModel
#check @SolidLean.Solid.ClauseFamily.models_iff_isGenModel
#print axioms SolidLean.Solid.Render.provable_iff_semantic
#check @SolidLean.Solid.Render.provable_iff_semantic
#print axioms SolidLean.Calc.TL_conservative
#check @SolidLean.Calc.TL_conservative
#print SolidLean.Calc.H_FO
#print SolidLean.Calc.TL_FO

-- Double negation elimination is derivable (the primitive `dne` is redundant)
#print axioms SolidLean.Calc.dne_derivable
#check @SolidLean.Calc.dne_derivable
#print axioms SolidLean.Calc.dne_derived
#check @SolidLean.Calc.dne_derived
#print axioms SolidLean.Calc.dneTerm_usesDne

-- The Palomar statement: Enayat's solidity of H in the self-contained many-sorted logic of
-- Palomar/Challenge.lean (proved in Palomar/Solution.lean from tower_solid)
#print axioms SolidLean.Palomar.tower_theory_solid
#check @SolidLean.Palomar.tower_theory_solid
