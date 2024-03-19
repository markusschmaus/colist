import Mathlib.Tactic
import Colist.ClassSetoid
import Colist.util.Bool

class PartialListLike (α : outParam (Type u)) (β : Type v) : Type (max u v) where
  isNil : β → Prop
  [instDecidableIsNil (as : β) : Decidable (isNil as)]
  head (as : β) : ¬ isNil as → α
  tail : β → β
  [instMembership : Membership α β]

instance {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β} :
    Decidable (inst.isNil as) := inst.instDecidableIsNil as

namespace PartialListLike

def isNil_exp (α : Type u) (β : Type v) (inst : PartialListLike α β) (as : β) :=
  isNil (α := α) (β := β) (self := inst) as

theorem isNil_exp_of_isNil {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} :
    isNil (self := inst) as = isNil_exp α β inst as := rfl

def head_exp (α : Type u) (β : Type v) (inst : PartialListLike α β) (as : β) (not_nil : ¬ isNil as) :=
  PartialListLike.head (α := α) (β := β) (self := inst) as not_nil

theorem head_exp_of_head {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} {not_nil : ¬ isNil as} :
    head (self := inst) as not_nil = head_exp α β inst as not_nil := rfl

def tail_exp (α : Type u) (β : Type v) (inst : PartialListLike α β) (as : β) :=
  tail (α := α) (β := β) (self := inst) as

theorem tail_exp_of_tail {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} :
    tail (self := inst) as = tail_exp α β inst as := rfl

abbrev isFinite {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) :
    Prop := ∃ (n : ℕ), inst.isNil (inst.tail^[n] as)

abbrev Mem {α : Type u} {β : Type v} [inst : PartialListLike α β] (a : α) (as : β) :
    Prop := ∃ (n : Nat) (not_nil : _), a = PartialListLike.head (PartialListLike.tail^[n] as) not_nil

def contains {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) (a : α) :
    Prop := inst.instMembership.mem a as

theorem contains_of_mem {α : Type u} {β : Type v} [inst : PartialListLike α β] {as : β} {a : α} :
    inst.instMembership.mem a as ↔ inst.contains as a := ⟨fun a => a, fun a => a⟩

abbrev head? {α : Type u} {β : Type v} [inst : PartialListLike α β] (as : β) :
    Option α :=
  if h : inst.isNil as then none else some (inst.head as h)

@[simp]
theorem head?_some_of_not_nil {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} (not_nil : ¬ inst.isNil as) :
    head? as = some (PartialListLike.head as not_nil) := by
  simp_all only [head?, dite_false]

@[simp]
theorem head?_none_iff_nil {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} : head? as = none ↔ (PartialListLike.isNil as) := by
  constructor
  · simp only [dite_eq_left_iff, imp_false, not_not, imp_self]
  · simp_all only [head?, dite_true, implies_true]

theorem head_eq_of_head?_eq {α : Type u} {β : Type v} {inst : PartialListLike α β}
    {inst' : PartialListLike α β} {as as' : β} {not_nil : _} {not_nil' : _} :
    as = as' → inst.head? as = inst'.head? as →
    inst.head as not_nil = inst'.head as' not_nil' := by
  intro as_eq
  subst as_eq
  rw [head?_some_of_not_nil (inst := inst) not_nil]
  rw [head?_some_of_not_nil (inst := inst') not_nil']
  simp only [Option.some.injEq, imp_self]

theorem head_eq_of_some_head?_eq {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} {head : α} : inst.head? as = some head →
    ∃ not_nil : ¬ inst.isNil as, inst.head as not_nil = head := by
  intro head?_eq
  have not_nil : ¬ inst.isNil as := by
    revert head?_eq
    apply imp_not_comm.mp
    intro is_nil
    rw [head?_none_iff_nil.mpr]
    · simp_all only [not_false_eq_true]
    · simp_all only
  use not_nil
  simp_all only [not_false_eq_true, head?_some_of_not_nil, Option.some.injEq]

theorem some_head?_eq_of_head_eq {α : Type u} {β : Type v} [inst : PartialListLike α β]
    {as : β} {head : α} {not_nil : ¬ inst.isNil as} : inst.head as not_nil = head →
    inst.head? as = some head := by
  intro head_eq
  simp_all only [not_false_eq_true, head?_some_of_not_nil]

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

theorem consistent_mem' {α : Type u} {β : Type v} [inst : PartialListLike α β]
    (head_tail : (a : α) → (as : β) →
      (inst.instMembership.mem a as ↔ inst.instMembership.mem a (inst.tail as) ∨
      ∃ not_nil, a = inst.head as not_nil))
    (mem_nil : (a : α) → (as : β) → inst.instMembership.mem a as → ¬ inst.isNil as)
    (finite : (as : β) → inst.isFinite as) :
    (a : α) → (as : β) → (inst.Mem a as ↔ inst.instMembership.mem a as) := by
  intro a as
  constructor
  · intro ⟨n, not_nil, a_eq⟩
    clear finite
    clear mem_nil
    induction n generalizing as with
    | zero =>
      rw [head_tail a as]
      apply Or.inr
      use not_nil
      simp_all only [Function.iterate_zero, id_eq, exists_prop, and_true]
    | succ n ih =>
      apply head_tail a as |>.mpr
      apply Or.inl
      apply ih (inst.tail as) not_nil
      rw [a_eq]
      simp only [Function.iterate_succ, Function.comp_apply]
  · replace ⟨n, finite⟩ := finite as
    induction n generalizing as with
    | zero =>
      intro mem
      replace := mem_nil a as mem
      simp only [Nat.zero_eq, Function.iterate_zero, id_eq] at finite
      contradiction
    | succ n ih =>
      intro mem
      replace ih := ih (inst.tail as) finite
      induction head_tail a as |>.mp mem with
      | inl mem =>
        have ⟨n, not_nil, a_eq⟩ := ih mem
        use n.succ
        use not_nil
        exact a_eq
      | inr head_eq =>
        replace ⟨not_nil, head_eq⟩ := head_eq
        use 0
        use not_nil
        exact head_eq
