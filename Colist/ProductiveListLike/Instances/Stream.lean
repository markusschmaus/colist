import Colist.ProductiveListLike.Class.Basic
import Colist.util.Option

universe u v

abbrev StreamListLike (stream : Type u) (α : Type v) [Stream stream α] := Option (α × stream)

namespace StreamListLike

-- instance {stream : Type u} {α : Type v} [Stream stream α] : ProductiveListLike α (StreamListLike stream α) where
--   isNil (as : StreamListLike stream α) := as = none
--   head (as : StreamListLike stream α) (h : ¬ (as = none)) :=
--     match as with
--     | none => absurd rfl h
--     | some (a, _) => a
--   tail (as : StreamListLike stream α) :=
--     match as with
--     | none => none
--     | some (_, as) => Stream.next? as
--   terminal_isNil as := by
--     simp_all only [implies_true]
