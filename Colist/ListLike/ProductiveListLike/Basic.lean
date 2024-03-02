import Colist.ListLike.PartialListLike.Basic


class ProductiveListLike (α : Type u) (β : Type v) extends PartialListLike α β : Type (max u v) where
  terminal_isNil (as : β) : isNil as → isNil (tail as)

namespace ProductiveListLike

theorem iterate_terminal_isNil {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : β) (n : ℕ) :
    PartialListLike.isNil α as → PartialListLike.isNil α ((PartialListLike.tail α)^[n] as) := by
  revert as
  induction n with
  | zero =>
    simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, implies_true]
  | succ n ih =>
    intro as
    have := ih (as := PartialListLike.tail α as)
    have := inst.terminal_isNil (as := as)
    simp_all only [implies_true, Function.iterate_succ, Function.comp_apply]


@[simp]
theorem isFinite_tail {α : Type u} {β : Type v} [inst : ProductiveListLike α β] {as : β} :
    PartialListLike.isFinite α (inst.tail as) ↔ PartialListLike.isFinite α as := by
  simp only [PartialListLike.isFinite]
  constructor
  · intro ⟨n, is_nil⟩
    use n.succ
    simp_all only [Function.iterate_succ_apply]
  · intro ⟨n, is_nil⟩
    use n.pred
    by_cases n_zero : n = 0
    · have := inst.terminal_isNil
      simp_all only [Function.iterate_zero, id_eq, Nat.pred_zero]
    · rw [←Nat.succ_pred n_zero] at is_nil
      simp_all only [Function.iterate_succ, Function.comp_apply]

@[simp]
theorem isFinite_iterate_tail {α : Type u} {β : Type v} [inst : ProductiveListLike α β] {as : β} {n : ℕ} :
    PartialListLike.isFinite α (inst.tail^[n] as) ↔ PartialListLike.isFinite α as := by
  revert as
  induction n with
  | zero =>
    intro as
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro as
    simp_all only [Function.iterate_succ, Function.comp_apply, isFinite_tail]

instance setoid (α : Type u) : ClassSetoid (ProductiveListLike α) where
  r x₁ x₂ := PartialListLike.setoid α |>.r
    (x₁.subst x₁.inst.toPartialListLike)
    (x₂.subst x₂.inst.toPartialListLike)
  iseqv := by
    apply Equivalence.comap
    exact  Setoid.iseqv