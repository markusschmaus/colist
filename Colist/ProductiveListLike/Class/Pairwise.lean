import Colist.ProductiveListLike.Class.Basic

universe u v

namespace ProductiveListLike

abbrev Pairwise {α : Type u} {β : Type v} [ProductiveListLike α β]
    (R : α → α → Prop) (as : β) : Prop :=
  ∀ (n m : Nat)
    (n_not_nil : ¬ PartialListLike.isNil (PartialListLike.tail^[n] as))
    (m_not_nil : ¬ PartialListLike.isNil (PartialListLike.tail^[m] as)),
  (n < m) →
  R (PartialListLike.head (PartialListLike.tail^[n] as) n_not_nil)
    (PartialListLike.head (PartialListLike.tail^[m] as) m_not_nil)

namespace Pairwise

theorem nil {α : Type u} {β : Type v} [ProductiveListLike α β]
    {R : α → α → Prop} {as : β} (is_nil : PartialListLike.isNil as) : Pairwise R as := by
  unfold Pairwise
  intro n m n_not_nil
  simp_all only [iterate_terminal_isNil, not_true_eq_false, IsEmpty.forall_iff]

-- theorem cons {α : Type u} {β : Type v} [ProductiveListLike α β]
--     {R : α → α → Prop} {as : β} (not_nil : ¬ PartialListLike.isNil as):
--     (∀ (a' : α), a' ∈ (PartialListLike.tail as) → R (PartialListLike.head as not_nil) a') →
--     Pairwise R (PartialListLike.tail as) → Pairwise R as := by
--   unfold Pairwise
--   intro head_R tail_R
--   intro n m n_not_nil m_not_nil n_lt_m
--   by_cases n_zero : n = 0
--   · simp_all only [Membership.mem, Mem, forall_exists_index, Nat.zero_eq,
--       Function.iterate_zero, id_eq]
--     have ⟨k, k_def⟩ := Nat.exists_eq_succ_of_ne_zero (n := m) (by omega)
--     subst k_def
--     refine' head_R _ k _ _
--     · simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, not_false_eq_true,
--         Function.iterate_succ, Function.comp_apply, Nat.zero_lt_succ]
--     · simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, not_false_eq_true,
--         Nat.zero_lt_succ, Function.iterate_succ, Function.comp_apply]
--   · have ⟨n', n'_def⟩ := Nat.exists_eq_succ_of_ne_zero (n := n) (by omega)
--     subst n'_def
--     have ⟨m', m'_def⟩ := Nat.exists_eq_succ_of_ne_zero (n := m) (by omega)
--     subst m'_def
--     apply tail_R
--     omega
