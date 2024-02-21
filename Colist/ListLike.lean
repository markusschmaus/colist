import Mathlib.Tactic
import Colist.PartialListLike

universe u v w

class ListLike (α : Type u) (β : Type v) extends PartialListLike α β : Type (max u v) where
  finite (as : β) : PartialListLike.isFinite α as

namespace ListLike

structure equivExt {α : Type u} (x₁ : Data.Imp (ListLike α))
    (x₂ : Data.Imp (ListLike α)) : Prop where
  intro ::
  isNil_eq : x₁.inst.isNil x₁.value ↔ x₂.inst.isNil x₂.value
  head_heq : HEq (x₁.inst.head x₁.value) (x₂.inst.head x₂.value)

instance equivExt.instSetoid {α : Type u} : Setoid (Data.Imp <| ListLike α) where
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

def equiv {α : Type u} (x₁ : Data.Imp (ListLike α))
    (x₂ : Data.Imp (ListLike α)) : Prop :=
  ∀ (n : ℕ), equivExt ⟨x₁.imp, x₁.inst, (x₁.inst.tail^[n] x₁.value)⟩ ⟨x₂.imp, x₂.inst, (x₂.inst.tail^[n] x₂.value)⟩

instance instSetoid (α : Type u) : Setoid (Data.Imp <| ListLike α) where
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
