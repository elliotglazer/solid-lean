import Solid.Step1b

/-!
# Steps 1–3 assembled: collapse data for the configuration

The collapses of the individual sorts (`Solid.Step1b`) are lifted to a
monotone sequence of sorts `b n ≥ n + 1` of `N` and glued by Step 2
(`Solid.Level`) into `CollapseData`.
-/

universe u

namespace SolidLean.Solid

open Classical

namespace Config

/-- The sorts of `N` in which the collapses are placed: monotone, above
`n + 1` and above the presenting sort of sort `n` of `P`. -/
def bSort (c : Config.{u}) : ℕ → ℕ
  | 0 => max 1 (c.J.a 0 + 1)
  | n + 1 => max (c.bSort n) (max (n + 2) (c.J.a (n + 1) + 1))

variable (c : Config.{u})

theorem bSort_mono (n : ℕ) : c.bSort n ≤ c.bSort (n + 1) := le_max_left _ _

theorem bSort_ge (n : ℕ) : n + 1 ≤ c.bSort n := by
  cases n with
  | zero => exact le_max_left _ _
  | succ n => exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem bSort_ge_a (n : ℕ) : c.J.a n + 1 ≤ c.bSort n := by
  cases n with
  | zero => exact le_max_right _ _
  | succ n => exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- The chosen collapse of sort `n`, in sort `J.a n + 1`. -/
noncomputable def level₀ (n : ℕ) : LevelCollapse c.N c.P c.J.pres n (c.J.a n + 1) :=
  Classical.choice (c.levelCollapse_exists n)

/-- The collapse of sort `n`, lifted to sort `bSort n`. -/
noncomputable def level (n : ℕ) : LevelCollapse c.N c.P c.J.pres n (c.bSort n) :=
  (c.level₀ n).lift c.hN (c.bSort_ge_a n)

/-- **Steps 1–4.** -/
noncomputable def collapseData : CollapseData c.N c.P c.J.pres where
  b := c.bSort
  b_mono := c.bSort_mono
  b_ge := c.bSort_ge
  S n := (c.level n).S
  e n := (c.level n).e
  e_mem n := (c.level n).e_mem
  e_surj n := (c.level n).e_surj
  e_injective n := (c.level n).e_injective
  e_mem_iff n := (c.level n).e_mem_iff
  S_trans n := (c.level n).S_trans
  S_supertrans n := (c.level n).S_supertrans
  e_transition n x :=
    c.J.levelCollapse_transition c.hN c.hP (c.bSort_mono n) (c.level n) (c.level (n + 1)) x
  e_definable n := (c.level n).e_definable

theorem collapseData_exists : Nonempty (CollapseData c.N c.P c.J.pres) := ⟨c.collapseData⟩

end Config

end SolidLean.Solid
