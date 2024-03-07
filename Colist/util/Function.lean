import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

universe u

namespace Function

theorem apply_iterate_apply {α : Type u} (f : α → α) (n : ℕ) (x : α) :
    f (f^[n] x) = f^[n] (f x) := by
  have := Function.iterate_add_apply f 1 n x
  simp only [iterate_succ, iterate_zero, comp_apply, id_eq] at this
  rw [←this]
  rw [←Function.iterate_succ_apply]
  congr
  linarith

@[simp]
theorem iterate_const {α : Type u} {const : α} {n : ℕ} :
    (¬ n = 0) → (fun _ => const)^[n] = (fun _ => const) := by
  intro ne_zero
  have hn : 1 ≤ n :=  by
    omega
  induction n, hn using Nat.le_induction with
  | base =>
    simp_all only [ne_eq, one_ne_zero, not_false_eq_true, iterate_succ, iterate_zero, id_comp]
  | succ m lt_m ih =>
    have := ih (by omega)
    funext
    simp_all only [ne_eq, implies_true, add_eq_zero, one_ne_zero, and_false, not_false_eq_true,
      iterate_succ, comp_apply]
