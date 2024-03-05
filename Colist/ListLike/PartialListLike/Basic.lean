import Mathlib.Tactic
import Colist.ClassSetoid
import Colist.util.Bool

class PartialListLike (α : outParam (Type u)) (β : Type v) : Type (max u v) where
  isNil : β → Prop
  [instDecidableIsNil (as : β) : Decidable (isNil as)]
  head (as : β) : ¬ isNil as → α
  tail : β → β
  [instMembership : Membership α β]

instance {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β}: Decidable (inst.isNil as) := inst.instDecidableIsNil as

namespace PartialListLike

abbrev isFinite {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) :
    Prop := ∃ (n : ℕ), inst.isNil (inst.tail^[n] as)

abbrev Mem {α : Type u} {β : Type v} [inst : PartialListLike α β] (a : α) (as : β) :
    Prop := ∃ (n : Nat) (is_nil : _), a = PartialListLike.head (PartialListLike.tail^[n] as) is_nil

def contains {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) (a : α) :
    Prop := inst.instMembership.mem a as

theorem contains_of_mem {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β} {a : α} :
    inst.instMembership.mem a as ↔ inst.contains as a := ⟨fun a => a, fun a => a⟩

abbrev head? {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) :
    Option α :=
  if h : inst.isNil as then none else some (inst.head as h)

@[simp]
theorem head?_not_nil {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} (not_nil : ¬ PartialListLike.isNil as) :
    head? as = some (PartialListLike.head as not_nil) := by
  simp_all only [head?, dite_false]

@[simp]
theorem head?_nil {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} (nil : PartialListLike.isNil as) :
    head? as = none := by
  simp_all only [head?, dite_true]

theorem head_eq_of_some_head?_eq {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} {head : α} : inst.head? as = some head →
    ∃ not_nil : ¬ inst.isNil as, inst.head as not_nil = head := by
  intro head?_eq
  have not_nil : ¬ inst.isNil as := by
    revert head?_eq
    apply imp_not_comm.mp
    intro is_nil
    rw [head?_nil]
    · simp_all only [not_false_eq_true]
    · simp_all only
  use not_nil
  simp_all only [not_false_eq_true, head?_not_nil, Option.some.injEq]

theorem some_head?_eq_of_head_eq {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} {head : α} {not_nil : ¬ inst.isNil as} : inst.head as not_nil = head →
    inst.head? as = some head := by
  intro head_eq
  simp_all only [not_false_eq_true, head?_not_nil]

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
