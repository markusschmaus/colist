import Colist.ListLike.Class.Basic
import Colist.util.Option
import Colist.util.Function

universe u

instance instListListLike {α : Type u} : ListLike α (Option α) where
  isNil as := as = none
  head as h := Option.get as (h |> Option.not_isSome_iff_eq_none.not_right.mpr)
  tail _ := none
  terminal_isNil as := by
    simp_all only [implies_true]
  consistent_mem a as:= by
    simp only [Option.mem_def]
    constructor
    · simp only [forall_exists_index, PartialListLike.tail]
      intro mem
      by_cases m_zero : mem = 0
      · simp_all only [Function.iterate_zero, id_eq, Option.some_get, implies_true]
      simp_all only [not_false_eq_true, Function.iterate_const, not_true_eq_false, Option.some_get,
        IsEmpty.forall_iff]
    · intro mem
      use 0
      simp_all only [Function.iterate_zero, id_eq, Option.get_some, not_false_eq_true, exists_const]
  finite as := by
    use 1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
