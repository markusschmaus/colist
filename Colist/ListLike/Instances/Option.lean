import Colist.ListLike.ListLike

universe u

instance {α : Type u} {as : Option α} : Decidable (as = none) :=
  decidableFromBool Option.isNone Option.isNone_iff_eq_none

instance instListListLike {α : Type u} : ListLike α (Option α) where
  isNil as := as = none
  head as h := Option.get as (h |> Option.not_isSome_iff_eq_none.not_right.mpr)
  tail _ := none
  terminal_isNil as := by
    simp_all only [implies_true]
  finite as := by
    use 1
    simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id_eq]
