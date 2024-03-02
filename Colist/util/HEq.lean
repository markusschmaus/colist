import Std.Logic
import Mathlib.Logic.Basic

theorem heq_of_cast_funext {α α': Sort u} {β :Sort v} {f : α → β} {g : α' → β} (type_eq : α = α') :
    (∀ (x : α), f x = g (cast type_eq x)) ↔ HEq f g := by
  constructor
  · intro funext
    apply heq_of_cast_eq (implies_congr type_eq rfl)
    subst type_eq
    simp_all only [cast_eq]
    funext
    simp_all only
  · intro heq x
    exact congr_heq heq (heq_of_cast_eq type_eq rfl)
