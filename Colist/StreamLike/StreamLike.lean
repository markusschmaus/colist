import Mathlib.Tactic
import Colist.ClassSetoid
import Colist.Bool

class StreamLike (α : Type u) (β : Type v) : Type (max u v) where
  head : β → α
  tail : β → β

namespace StreamLike

structure equivExt {α : Type u} (x₁ : ClassSetoid.Imp (StreamLike α))
    (x₂ : ClassSetoid.Imp (StreamLike α)) : Prop where
  intro ::
  head_heq : x₁.inst.head x₁.value = x₂.inst.head x₂.value

instance equivExt.instSetoid {α : Type u} : Setoid (ClassSetoid.Imp <| StreamLike α) where
  r := equivExt
  iseqv := by
    constructor
    · intro x
      constructor
      rfl
    · intro _ _ h
      constructor
      exact h.head_heq.symm
    · intro _ _ _ h₁₂ h₂₃
      constructor
      have h₁₂' := h₁₂.head_heq
      have h₂₃' := h₂₃.head_heq
      simp_all only

def equiv {α : Type u} (x₁ : ClassSetoid.Imp (StreamLike α))
    (x₂ : ClassSetoid.Imp (StreamLike α)) : Prop :=
  ∀ (n : ℕ), equivExt ⟨x₁.imp, x₁.inst, (x₁.inst.tail^[n] x₁.value)⟩ ⟨x₂.imp, x₂.inst, (x₂.inst.tail^[n] x₂.value)⟩

instance setoid (α : Type u) : ClassSetoid (StreamLike α) where
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
