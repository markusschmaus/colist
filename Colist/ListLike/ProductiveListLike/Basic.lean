import Colist.ListLike.PartialListLike.Basic


class ProductiveListLike (α : outParam (Type u)) (β : Type v)
    extends PartialListLike α β : Type (max u v) where
  terminal_isNil (as : β) : isNil as → isNil (tail as)
  consistent_mem (a : α) (as : β) :
    PartialListLike.Mem a as ↔ toPartialListLike.instMembership.mem a as

namespace ProductiveListLike

theorem iterate_terminal_isNil {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : β) (n : ℕ) :
    PartialListLike.isNil as → PartialListLike.isNil (PartialListLike.tail^[n] as) := by
  revert as
  induction n with
  | zero =>
    simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq, implies_true]
  | succ n ih =>
    intro as
    have := ih (as := PartialListLike.tail as)
    have := inst.terminal_isNil (as := as)
    simp_all only [implies_true, Function.iterate_succ, Function.comp_apply]

@[simp]
theorem isFinite_tail {α : Type u} {β : Type v}
    [inst : ProductiveListLike α β] {as : β} :
    PartialListLike.isFinite (inst.tail as) ↔ PartialListLike.isFinite as := by
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
theorem isFinite_iterate_tail {α : Type u} {β : Type v}
    [inst : ProductiveListLike α β] {as : β} {n : ℕ} :
    PartialListLike.isFinite (inst.tail^[n] as) ↔ PartialListLike.isFinite as := by
  revert as
  induction n with
  | zero =>
    intro as
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro as
    simp_all only [Function.iterate_succ, Function.comp_apply, isFinite_tail]

@[simp]
theorem isNil_tail {α : Type u} {β : Type v}
    [inst : ProductiveListLike α β] {as : β} :
    PartialListLike.isNil as → PartialListLike.isNil (PartialListLike.tail as) :=
  fun a => terminal_isNil as a

@[simp]
theorem isNil_iterate_tail {α : Type u} {β : Type v}
    [inst : ProductiveListLike α β] {as : β} {n : ℕ} :
    PartialListLike.isNil as → PartialListLike.isNil (PartialListLike.tail^[n] as) := by
  revert as
  induction n with
  | zero =>
    intro as
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq, imp_self]
  | succ n ih =>
    intro as
    simp_all only [Function.iterate_succ, Function.comp_apply, isNil_tail, implies_true]

@[simp]
theorem isNil_iterate_tail_of_isNil_iterate_tail {α : Type u} {β : Type v}
    {inst : ProductiveListLike α β} {as : β} {n m: ℕ} :
    (n ≤ m) →
    inst.isNil (inst.tail^[n] as) →
    inst.isNil (inst.tail^[m] as) := by
  intro n_le_m
  have ⟨k, k_def⟩ := Nat.exists_eq_add_of_le n_le_m
  rw [add_comm] at k_def
  subst k_def
  have := isNil_iterate_tail (as := PartialListLike.tail^[n] as) (n := k)
  simp only [←Function.iterate_add_apply] at this
  simp_all only [le_add_iff_nonneg_left, zero_le, implies_true]

instance setoid (α : Type u) : ClassSetoid (ProductiveListLike α) where
  r x₁ x₂ := PartialListLike.setoid α |>.r
    (x₁.subst x₁.inst.toPartialListLike)
    (x₂.subst x₂.inst.toPartialListLike)
  iseqv := by
    apply Equivalence.comap
    exact  Setoid.iseqv
