import Colist.ListLike.ListLike

universe u

instance {α : Type u} {as : List α} : Decidable (as = []) :=
  decidableFromBool List.isEmpty List.isEmpty_iff_eq_nil

instance instListListLike {α : Type u} : ListLike α (List α) where
  isNil as := as = []
  head := List.head
  tail := List.tail
  terminal_isNil as := by
    simp_all only [List.tail_nil, implies_true]
  finite as := by
    use as.length
    simp only []
    apply List.eq_nil_of_length_eq_zero
    have (n : ℕ) : List.length (List.tail^[n] as) = List.length as - n := by
      revert as
      induction n with
      | zero => intro as; simp only [Nat.zero_eq, Function.iterate_zero, id_eq, ge_iff_le,
        nonpos_iff_eq_zero, tsub_zero]
      | succ n ih =>
        intro as
        simp only [Function.iterate_succ, Function.comp_apply, ih, List.length_tail]
        simp only [Nat.succ_eq_one_add, Nat.sub_add_eq]
    have := this as.length
    simp_all only [le_refl, tsub_eq_zero_of_le]
