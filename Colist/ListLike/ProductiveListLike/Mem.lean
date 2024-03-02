import Colist.ListLike.ProductiveListLike.Basic

universe u v

namespace ProductiveListLike

abbrev Mem {α : Type u} {β : Type v} [ProductiveListLike α β] (a : α) (as : β) : Prop :=
  ∃ (n : Nat) (not_nil : ¬ PartialListLike.isNil (PartialListLike.tail^[n] as)),
  PartialListLike.head (PartialListLike.tail^[n] as) not_nil = a

namespace Mem

theorem head {α : Type u} {β : Type v} [ProductiveListLike α β] {a : α} {as : β}
    {not_nil : ¬ PartialListLike.isNil as} :
    (PartialListLike.head as not_nil) = a → Mem a as := by
  intro head_eq
  use 0
  simp_all only [Function.iterate_zero, id_eq, not_false_eq_true, exists_const]

theorem tail {α : Type u} {β : Type v} [ProductiveListLike α β] {a : α} {as : β} :
    Mem a (PartialListLike.tail as) → Mem a as := by
  intro ⟨n, not_nil, _⟩
  use (n + 1)
  use not_nil
  simp_all only [Function.iterate_succ, Function.comp_apply]

instance (α : Type u) {β : Type v} [ProductiveListLike α β] : Membership α β where
  mem := Mem
