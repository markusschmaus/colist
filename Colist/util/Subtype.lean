import Mathlib.Data.Subtype
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic

universe u v

@[simp]
theorem Subtype.iterate_map_coe {α : Type u} {p : α → Prop}
    (f : α → α) (h : ∀ (a : α), p a → p (f a)) {n : Nat}:
    ∀ (a : Subtype p), ↑((Subtype.map f h)^[n] a) = f^[n] ↑a := by
  induction n with
  | zero =>
    intro a
    rfl
  | succ n ih =>
    intro a
    simp only [Function.iterate_succ_apply, ih (map f h a), map_coe]
