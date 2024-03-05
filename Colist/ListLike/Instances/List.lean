import Colist.ListLike.ListLike.Basic
import Colist.util.List
universe u

namespace List

theorem mem_of_mem_iterate_tail {α : Type u} {a : α} {as : List α} {n : ℕ} :
    a ∈ List.tail^[n] as → a ∈ as := by
  revert as
  induction n with
  | zero =>
    simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, implies_true, forall_const]
  | succ n ih =>
    intro as
    have := ih (as := List.tail as)
    simp_all only [implies_true, Function.iterate_succ, Function.comp_apply, mem_of_mem_tail]

instance instListLike {α : Type u} : ListLike α (List α) where
  isNil as := as = []
  head := List.head
  tail := List.tail
  terminal_isNil as := by
    simp_all only [List.tail_nil, implies_true]
  consistent_mem a as := by
    constructor
    · simp? [PartialListLike.Mem]
      intro n not_nil mem
      have := head_mem not_nil |> mem_of_mem_iterate_tail
      simp_all only
    · intro mem
      induction mem with
      | head as' =>
        use 0
        simp_all only [Function.iterate_zero, id_eq, List.head_cons, not_false_eq_true,
          exists_const]
      | tail as' _ mem' =>
        have ⟨n , _⟩ := mem'
        use n.succ
        simp_all only [Function.iterate_succ, Function.comp_apply, List.tail_cons]
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
