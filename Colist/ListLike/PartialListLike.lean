import Mathlib.Tactic
import Colist.ClassSetoid
import Colist.Bool

class PartialListLike (α : Type u) (β : Type v) : Type (max u v) where
  isNil : β → Prop
  head (as : β) : ¬ isNil as → α
  tail : β → β
  [instDecidableIsNil (as : β) : Decidable (isNil as)]
  terminal_isNil : ∀ (as : β), isNil as → isNil (tail as)

instance {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β}: Decidable (inst.isNil as) := inst.instDecidableIsNil as

namespace PartialListLike

abbrev isFinite (α : Type u) {β : Type v} [inst : PartialListLike α β] (as : β) : Prop :=
  ∃ (n : ℕ), inst.isNil (inst.tail^[n] as)

@[simp]
theorem isFinite_tail {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β} :
    isFinite α (inst.tail as) ↔ isFinite α as := by
  simp only [isFinite]
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
theorem isFinite_iterate_tail {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β} {n : ℕ} :
    isFinite α (inst.tail^[n] as) ↔ isFinite α as := by
  revert as
  induction n with
  | zero =>
    intro as
    simp only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro as
    simp_all only [Function.iterate_succ, Function.comp_apply, isFinite_tail]

structure equivExt {α : Type u} (x₁ : ClassSetoid.Imp (PartialListLike α))
    (x₂ : ClassSetoid.Imp (PartialListLike α)) : Prop where
  intro ::
  isNil_eq : x₁.inst.isNil x₁.value ↔ x₂.inst.isNil x₂.value
  head_heq : HEq (x₁.inst.head x₁.value) (x₂.inst.head x₂.value)

instance equivExt.instSetoid {α : Type u} : Setoid (ClassSetoid.Imp <| PartialListLike α) where
  r := equivExt
  iseqv := by
    constructor
    · intro x
      constructor
      · simp only
      · simp only [heq_eq_eq]
    · intro _ _ h
      constructor
      · simp only [h.isNil_eq]
      · simp only [h.head_heq.symm]
    · intro _ _ _ h₁₂ h₂₃
      constructor
      · simp only [h₁₂.isNil_eq, h₂₃.isNil_eq]
      · have := h₁₂.head_heq
        simp only [h₁₂.head_heq.trans h₂₃.head_heq]

def equiv {α : Type u} (x₁ : ClassSetoid.Imp (PartialListLike α))
    (x₂ : ClassSetoid.Imp (PartialListLike α)) : Prop :=
  ∀ (n : ℕ), equivExt ⟨x₁.imp, x₁.inst, (x₁.inst.tail^[n] x₁.value)⟩ ⟨x₂.imp, x₂.inst, (x₂.inst.tail^[n] x₂.value)⟩

instance setoid (α : Type u) : ClassSetoid (PartialListLike α) where
  r := equiv
  iseqv := by
    constructor
    · intro _ _
      apply equivExt.instSetoid.iseqv.refl
    · intro _ _ h _
      simp only [equiv] at h
      apply equivExt.instSetoid.iseqv.symm
      simp_all only [Setoid.r]
    · intro _ x₂ _ h₁₂ h₂₃ n
      simp only [equiv] at h₁₂ h₂₃
      apply equivExt.instSetoid.iseqv.trans (y := ⟨x₂.imp, x₂.inst, (x₂.inst.tail)^[n] x₂.value⟩)
      all_goals simp_all only [Setoid.r]
