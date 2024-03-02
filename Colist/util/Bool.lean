import Mathlib.Logic.Basic

def decidableFromBool {α : Type u} (f : α → Bool) {p : α → Prop} (sem : {x : α} → f x = true ↔ p x) {x : α} : Decidable (p x) :=
  if h : f x then
    isTrue <| sem.mp h
  else
    isFalse <| sem.not.mp h
