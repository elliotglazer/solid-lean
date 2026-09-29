module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# `Fin.snoc` at literal indices (generated)

Evaluation of `Fin.snoc t z k` for literal `k`, for the arities the clause
readings of the primitives need.  All are `rfl`.
-/

@[expose] public section

namespace SolidLean.Solid.Fin

variable {α : Type*}

@[simp] theorem snocL_0_0 (t : Fin 0 → α) (z : α) : (Fin.snoc t z : Fin 1 → α) 0 = z := rfl
@[simp] theorem snocL_1_0 (t : Fin 1 → α) (z : α) : (Fin.snoc t z : Fin 2 → α) 0 = t 0 := rfl
@[simp] theorem snocL_1_1 (t : Fin 1 → α) (z : α) : (Fin.snoc t z : Fin 2 → α) 1 = z := rfl
@[simp] theorem snocL_2_0 (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 0 = t 0 := rfl
@[simp] theorem snocL_2_1 (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 1 = t 1 := rfl
@[simp] theorem snocL_2_2 (t : Fin 2 → α) (z : α) : (Fin.snoc t z : Fin 3 → α) 2 = z := rfl
@[simp] theorem snocL_3_0 (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 0 = t 0 := rfl
@[simp] theorem snocL_3_1 (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 1 = t 1 := rfl
@[simp] theorem snocL_3_2 (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 2 = t 2 := rfl
@[simp] theorem snocL_3_3 (t : Fin 3 → α) (z : α) : (Fin.snoc t z : Fin 4 → α) 3 = z := rfl
@[simp] theorem snocL_4_0 (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 0 = t 0 := rfl
@[simp] theorem snocL_4_1 (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 1 = t 1 := rfl
@[simp] theorem snocL_4_2 (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 2 = t 2 := rfl
@[simp] theorem snocL_4_3 (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 3 = t 3 := rfl
@[simp] theorem snocL_4_4 (t : Fin 4 → α) (z : α) : (Fin.snoc t z : Fin 5 → α) 4 = z := rfl
@[simp] theorem snocL_5_0 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 0 = t 0 := rfl
@[simp] theorem snocL_5_1 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 1 = t 1 := rfl
@[simp] theorem snocL_5_2 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 2 = t 2 := rfl
@[simp] theorem snocL_5_3 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 3 = t 3 := rfl
@[simp] theorem snocL_5_4 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 4 = t 4 := rfl
@[simp] theorem snocL_5_5 (t : Fin 5 → α) (z : α) : (Fin.snoc t z : Fin 6 → α) 5 = z := rfl
@[simp] theorem snocL_6_0 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 0 = t 0 := rfl
@[simp] theorem snocL_6_1 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 1 = t 1 := rfl
@[simp] theorem snocL_6_2 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 2 = t 2 := rfl
@[simp] theorem snocL_6_3 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 3 = t 3 := rfl
@[simp] theorem snocL_6_4 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 4 = t 4 := rfl
@[simp] theorem snocL_6_5 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 5 = t 5 := rfl
@[simp] theorem snocL_6_6 (t : Fin 6 → α) (z : α) : (Fin.snoc t z : Fin 7 → α) 6 = z := rfl
@[simp] theorem snocL_7_0 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 0 = t 0 := rfl
@[simp] theorem snocL_7_1 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 1 = t 1 := rfl
@[simp] theorem snocL_7_2 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 2 = t 2 := rfl
@[simp] theorem snocL_7_3 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 3 = t 3 := rfl
@[simp] theorem snocL_7_4 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 4 = t 4 := rfl
@[simp] theorem snocL_7_5 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 5 = t 5 := rfl
@[simp] theorem snocL_7_6 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 6 = t 6 := rfl
@[simp] theorem snocL_7_7 (t : Fin 7 → α) (z : α) : (Fin.snoc t z : Fin 8 → α) 7 = z := rfl
@[simp] theorem snocL_8_0 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 0 = t 0 := rfl
@[simp] theorem snocL_8_1 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 1 = t 1 := rfl
@[simp] theorem snocL_8_2 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 2 = t 2 := rfl
@[simp] theorem snocL_8_3 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 3 = t 3 := rfl
@[simp] theorem snocL_8_4 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 4 = t 4 := rfl
@[simp] theorem snocL_8_5 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 5 = t 5 := rfl
@[simp] theorem snocL_8_6 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 6 = t 6 := rfl
@[simp] theorem snocL_8_7 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 7 = t 7 := rfl
@[simp] theorem snocL_8_8 (t : Fin 8 → α) (z : α) : (Fin.snoc t z : Fin 9 → α) 8 = z := rfl
@[simp] theorem snocL_9_0 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 0 = t 0 := rfl
@[simp] theorem snocL_9_1 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 1 = t 1 := rfl
@[simp] theorem snocL_9_2 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 2 = t 2 := rfl
@[simp] theorem snocL_9_3 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 3 = t 3 := rfl
@[simp] theorem snocL_9_4 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 4 = t 4 := rfl
@[simp] theorem snocL_9_5 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 5 = t 5 := rfl
@[simp] theorem snocL_9_6 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 6 = t 6 := rfl
@[simp] theorem snocL_9_7 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 7 = t 7 := rfl
@[simp] theorem snocL_9_8 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 8 = t 8 := rfl
@[simp] theorem snocL_9_9 (t : Fin 9 → α) (z : α) : (Fin.snoc t z : Fin 10 → α) 9 = z := rfl
@[simp] theorem snocL_10_0 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 0 = t 0 := rfl
@[simp] theorem snocL_10_1 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 1 = t 1 := rfl
@[simp] theorem snocL_10_2 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 2 = t 2 := rfl
@[simp] theorem snocL_10_3 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 3 = t 3 := rfl
@[simp] theorem snocL_10_4 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 4 = t 4 := rfl
@[simp] theorem snocL_10_5 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 5 = t 5 := rfl
@[simp] theorem snocL_10_6 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 6 = t 6 := rfl
@[simp] theorem snocL_10_7 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 7 = t 7 := rfl
@[simp] theorem snocL_10_8 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 8 = t 8 := rfl
@[simp] theorem snocL_10_9 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 9 = t 9 := rfl
@[simp] theorem snocL_10_10 (t : Fin 10 → α) (z : α) : (Fin.snoc t z : Fin 11 → α) 10 = z := rfl
@[simp] theorem snocL_11_0 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 0 = t 0 := rfl
@[simp] theorem snocL_11_1 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 1 = t 1 := rfl
@[simp] theorem snocL_11_2 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 2 = t 2 := rfl
@[simp] theorem snocL_11_3 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 3 = t 3 := rfl
@[simp] theorem snocL_11_4 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 4 = t 4 := rfl
@[simp] theorem snocL_11_5 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 5 = t 5 := rfl
@[simp] theorem snocL_11_6 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 6 = t 6 := rfl
@[simp] theorem snocL_11_7 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 7 = t 7 := rfl
@[simp] theorem snocL_11_8 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 8 = t 8 := rfl
@[simp] theorem snocL_11_9 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 9 = t 9 := rfl
@[simp] theorem snocL_11_10 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 10 = t 10 := rfl
@[simp] theorem snocL_11_11 (t : Fin 11 → α) (z : α) : (Fin.snoc t z : Fin 12 → α) 11 = z := rfl
@[simp] theorem snocL_12_0 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 0 = t 0 := rfl
@[simp] theorem snocL_12_1 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 1 = t 1 := rfl
@[simp] theorem snocL_12_2 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 2 = t 2 := rfl
@[simp] theorem snocL_12_3 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 3 = t 3 := rfl
@[simp] theorem snocL_12_4 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 4 = t 4 := rfl
@[simp] theorem snocL_12_5 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 5 = t 5 := rfl
@[simp] theorem snocL_12_6 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 6 = t 6 := rfl
@[simp] theorem snocL_12_7 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 7 = t 7 := rfl
@[simp] theorem snocL_12_8 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 8 = t 8 := rfl
@[simp] theorem snocL_12_9 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 9 = t 9 := rfl
@[simp] theorem snocL_12_10 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 10 = t 10 := rfl
@[simp] theorem snocL_12_11 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 11 = t 11 := rfl
@[simp] theorem snocL_12_12 (t : Fin 12 → α) (z : α) : (Fin.snoc t z : Fin 13 → α) 12 = z := rfl
@[simp] theorem snocL_13_0 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 0 = t 0 := rfl
@[simp] theorem snocL_13_1 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 1 = t 1 := rfl
@[simp] theorem snocL_13_2 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 2 = t 2 := rfl
@[simp] theorem snocL_13_3 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 3 = t 3 := rfl
@[simp] theorem snocL_13_4 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 4 = t 4 := rfl
@[simp] theorem snocL_13_5 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 5 = t 5 := rfl
@[simp] theorem snocL_13_6 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 6 = t 6 := rfl
@[simp] theorem snocL_13_7 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 7 = t 7 := rfl
@[simp] theorem snocL_13_8 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 8 = t 8 := rfl
@[simp] theorem snocL_13_9 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 9 = t 9 := rfl
@[simp] theorem snocL_13_10 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 10 = t 10 := rfl
@[simp] theorem snocL_13_11 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 11 = t 11 := rfl
@[simp] theorem snocL_13_12 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 12 = t 12 := rfl
@[simp] theorem snocL_13_13 (t : Fin 13 → α) (z : α) : (Fin.snoc t z : Fin 14 → α) 13 = z := rfl
@[simp] theorem snocL_14_0 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 0 = t 0 := rfl
@[simp] theorem snocL_14_1 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 1 = t 1 := rfl
@[simp] theorem snocL_14_2 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 2 = t 2 := rfl
@[simp] theorem snocL_14_3 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 3 = t 3 := rfl
@[simp] theorem snocL_14_4 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 4 = t 4 := rfl
@[simp] theorem snocL_14_5 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 5 = t 5 := rfl
@[simp] theorem snocL_14_6 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 6 = t 6 := rfl
@[simp] theorem snocL_14_7 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 7 = t 7 := rfl
@[simp] theorem snocL_14_8 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 8 = t 8 := rfl
@[simp] theorem snocL_14_9 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 9 = t 9 := rfl
@[simp] theorem snocL_14_10 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 10 = t 10 := rfl
@[simp] theorem snocL_14_11 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 11 = t 11 := rfl
@[simp] theorem snocL_14_12 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 12 = t 12 := rfl
@[simp] theorem snocL_14_13 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 13 = t 13 := rfl
@[simp] theorem snocL_14_14 (t : Fin 14 → α) (z : α) : (Fin.snoc t z : Fin 15 → α) 14 = z := rfl
@[simp] theorem snocL_15_0 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 0 = t 0 := rfl
@[simp] theorem snocL_15_1 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 1 = t 1 := rfl
@[simp] theorem snocL_15_2 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 2 = t 2 := rfl
@[simp] theorem snocL_15_3 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 3 = t 3 := rfl
@[simp] theorem snocL_15_4 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 4 = t 4 := rfl
@[simp] theorem snocL_15_5 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 5 = t 5 := rfl
@[simp] theorem snocL_15_6 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 6 = t 6 := rfl
@[simp] theorem snocL_15_7 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 7 = t 7 := rfl
@[simp] theorem snocL_15_8 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 8 = t 8 := rfl
@[simp] theorem snocL_15_9 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 9 = t 9 := rfl
@[simp] theorem snocL_15_10 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 10 = t 10 := rfl
@[simp] theorem snocL_15_11 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 11 = t 11 := rfl
@[simp] theorem snocL_15_12 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 12 = t 12 := rfl
@[simp] theorem snocL_15_13 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 13 = t 13 := rfl
@[simp] theorem snocL_15_14 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 14 = t 14 := rfl
@[simp] theorem snocL_15_15 (t : Fin 15 → α) (z : α) : (Fin.snoc t z : Fin 16 → α) 15 = z := rfl
@[simp] theorem snocL_16_0 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 0 = t 0 := rfl
@[simp] theorem snocL_16_1 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 1 = t 1 := rfl
@[simp] theorem snocL_16_2 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 2 = t 2 := rfl
@[simp] theorem snocL_16_3 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 3 = t 3 := rfl
@[simp] theorem snocL_16_4 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 4 = t 4 := rfl
@[simp] theorem snocL_16_5 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 5 = t 5 := rfl
@[simp] theorem snocL_16_6 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 6 = t 6 := rfl
@[simp] theorem snocL_16_7 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 7 = t 7 := rfl
@[simp] theorem snocL_16_8 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 8 = t 8 := rfl
@[simp] theorem snocL_16_9 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 9 = t 9 := rfl
@[simp] theorem snocL_16_10 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 10 = t 10 := rfl
@[simp] theorem snocL_16_11 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 11 = t 11 := rfl
@[simp] theorem snocL_16_12 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 12 = t 12 := rfl
@[simp] theorem snocL_16_13 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 13 = t 13 := rfl
@[simp] theorem snocL_16_14 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 14 = t 14 := rfl
@[simp] theorem snocL_16_15 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 15 = t 15 := rfl
@[simp] theorem snocL_16_16 (t : Fin 16 → α) (z : α) : (Fin.snoc t z : Fin 17 → α) 16 = z := rfl
@[simp] theorem snocL_17_0 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 0 = t 0 := rfl
@[simp] theorem snocL_17_1 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 1 = t 1 := rfl
@[simp] theorem snocL_17_2 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 2 = t 2 := rfl
@[simp] theorem snocL_17_3 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 3 = t 3 := rfl
@[simp] theorem snocL_17_4 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 4 = t 4 := rfl
@[simp] theorem snocL_17_5 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 5 = t 5 := rfl
@[simp] theorem snocL_17_6 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 6 = t 6 := rfl
@[simp] theorem snocL_17_7 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 7 = t 7 := rfl
@[simp] theorem snocL_17_8 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 8 = t 8 := rfl
@[simp] theorem snocL_17_9 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 9 = t 9 := rfl
@[simp] theorem snocL_17_10 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 10 = t 10 := rfl
@[simp] theorem snocL_17_11 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 11 = t 11 := rfl
@[simp] theorem snocL_17_12 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 12 = t 12 := rfl
@[simp] theorem snocL_17_13 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 13 = t 13 := rfl
@[simp] theorem snocL_17_14 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 14 = t 14 := rfl
@[simp] theorem snocL_17_15 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 15 = t 15 := rfl
@[simp] theorem snocL_17_16 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 16 = t 16 := rfl
@[simp] theorem snocL_17_17 (t : Fin 17 → α) (z : α) : (Fin.snoc t z : Fin 18 → α) 17 = z := rfl
@[simp] theorem snocL_18_0 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 0 = t 0 := rfl
@[simp] theorem snocL_18_1 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 1 = t 1 := rfl
@[simp] theorem snocL_18_2 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 2 = t 2 := rfl
@[simp] theorem snocL_18_3 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 3 = t 3 := rfl
@[simp] theorem snocL_18_4 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 4 = t 4 := rfl
@[simp] theorem snocL_18_5 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 5 = t 5 := rfl
@[simp] theorem snocL_18_6 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 6 = t 6 := rfl
@[simp] theorem snocL_18_7 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 7 = t 7 := rfl
@[simp] theorem snocL_18_8 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 8 = t 8 := rfl
@[simp] theorem snocL_18_9 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 9 = t 9 := rfl
@[simp] theorem snocL_18_10 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 10 = t 10 := rfl
@[simp] theorem snocL_18_11 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 11 = t 11 := rfl
@[simp] theorem snocL_18_12 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 12 = t 12 := rfl
@[simp] theorem snocL_18_13 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 13 = t 13 := rfl
@[simp] theorem snocL_18_14 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 14 = t 14 := rfl
@[simp] theorem snocL_18_15 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 15 = t 15 := rfl
@[simp] theorem snocL_18_16 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 16 = t 16 := rfl
@[simp] theorem snocL_18_17 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 17 = t 17 := rfl
@[simp] theorem snocL_18_18 (t : Fin 18 → α) (z : α) : (Fin.snoc t z : Fin 19 → α) 18 = z := rfl
@[simp] theorem snocL_19_0 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 0 = t 0 := rfl
@[simp] theorem snocL_19_1 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 1 = t 1 := rfl
@[simp] theorem snocL_19_2 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 2 = t 2 := rfl
@[simp] theorem snocL_19_3 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 3 = t 3 := rfl
@[simp] theorem snocL_19_4 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 4 = t 4 := rfl
@[simp] theorem snocL_19_5 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 5 = t 5 := rfl
@[simp] theorem snocL_19_6 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 6 = t 6 := rfl
@[simp] theorem snocL_19_7 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 7 = t 7 := rfl
@[simp] theorem snocL_19_8 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 8 = t 8 := rfl
@[simp] theorem snocL_19_9 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 9 = t 9 := rfl
@[simp] theorem snocL_19_10 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 10 = t 10 := rfl
@[simp] theorem snocL_19_11 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 11 = t 11 := rfl
@[simp] theorem snocL_19_12 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 12 = t 12 := rfl
@[simp] theorem snocL_19_13 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 13 = t 13 := rfl
@[simp] theorem snocL_19_14 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 14 = t 14 := rfl
@[simp] theorem snocL_19_15 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 15 = t 15 := rfl
@[simp] theorem snocL_19_16 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 16 = t 16 := rfl
@[simp] theorem snocL_19_17 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 17 = t 17 := rfl
@[simp] theorem snocL_19_18 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 18 = t 18 := rfl
@[simp] theorem snocL_19_19 (t : Fin 19 → α) (z : α) : (Fin.snoc t z : Fin 20 → α) 19 = z := rfl
@[simp] theorem snocL_20_0 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 0 = t 0 := rfl
@[simp] theorem snocL_20_1 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 1 = t 1 := rfl
@[simp] theorem snocL_20_2 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 2 = t 2 := rfl
@[simp] theorem snocL_20_3 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 3 = t 3 := rfl
@[simp] theorem snocL_20_4 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 4 = t 4 := rfl
@[simp] theorem snocL_20_5 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 5 = t 5 := rfl
@[simp] theorem snocL_20_6 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 6 = t 6 := rfl
@[simp] theorem snocL_20_7 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 7 = t 7 := rfl
@[simp] theorem snocL_20_8 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 8 = t 8 := rfl
@[simp] theorem snocL_20_9 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 9 = t 9 := rfl
@[simp] theorem snocL_20_10 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 10 = t 10 := rfl
@[simp] theorem snocL_20_11 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 11 = t 11 := rfl
@[simp] theorem snocL_20_12 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 12 = t 12 := rfl
@[simp] theorem snocL_20_13 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 13 = t 13 := rfl
@[simp] theorem snocL_20_14 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 14 = t 14 := rfl
@[simp] theorem snocL_20_15 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 15 = t 15 := rfl
@[simp] theorem snocL_20_16 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 16 = t 16 := rfl
@[simp] theorem snocL_20_17 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 17 = t 17 := rfl
@[simp] theorem snocL_20_18 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 18 = t 18 := rfl
@[simp] theorem snocL_20_19 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 19 = t 19 := rfl
@[simp] theorem snocL_20_20 (t : Fin 20 → α) (z : α) : (Fin.snoc t z : Fin 21 → α) 20 = z := rfl

end SolidLean.Solid.Fin
