import Colist.ListLike.ListLike

universe u v

abbrev StreamListLike (stream : Type u) (α : Type v) [Stream stream α] := Option (α × stream)

namespace StreamListLike

instance {α : Type u} {x : Option α} : Decidable (x = none) :=
  decidableFromBool Option.isNone Option.isNone_iff_eq_none

instance {stream : Type u} {α : Type v} [Stream stream α] : PartialListLike α (StreamListLike stream α) where
  isNil (as : StreamListLike stream α) := as = none
  head (as : StreamListLike stream α) (h : ¬ (as = none)) :=
    match as with
    | none => absurd rfl h
    | some (a, _) => a
  terminal_isNil as := by
    simp_all only [implies_true]
  tail (as : StreamListLike stream α) :=
    match as with
    | none => none
    | some (_, as) => Stream.next? as
