import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

universe u

namespace Function

@[simp]
theorem apply_iterate_apply {α : Type u} (f : α → α) (n : ℕ) (x : α) :
    f (f^[n] x) = f^[n] (f x) := by
  have := Function.iterate_add_apply f 1 n x
  simp only [iterate_succ, iterate_zero, comp_apply, id_eq] at this
  rw [←this]
  rw [←Function.iterate_succ_apply]
  congr
  linarith
