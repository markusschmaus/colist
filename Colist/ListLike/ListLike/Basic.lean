import Mathlib.Tactic
import Colist.ListLike.ProductiveListLike.Basic

universe u v w

class ListLike (α : outParam (Type u)) (β : Type v) extends ProductiveListLike α β : Type (max u v) where
  finite (as : β) : PartialListLike.isFinite as
namespace ListLike

abbrev FiniteProductiveListLike (α : Type u) (β : Type v) [inst : ProductiveListLike α β] :=
  Subtype fun as : β => PartialListLike.isFinite (inst := inst.toPartialListLike) as

namespace FiniteProductiveListLike

instance Membership (α : Type u) (β : Type v) [inst : ProductiveListLike α β] :
    Membership α (FiniteProductiveListLike α β) where
  mem a as := inst.instMembership.mem a as.val

instance instPartialListLike (α : Type u) (β : Type v) [inst : ProductiveListLike α β] :
    PartialListLike α (FiniteProductiveListLike α β) where
  isNil as := inst.isNil as.val
  head as := inst.head as.val
  tail as := Subtype.mk (inst.tail as.val) <| by
    obtain ⟨n, val_nil⟩ := as.property
    use n.pred
    rw [←Function.iterate_succ_apply]
    by_cases n_zero : n = 0
    · subst n_zero
      have := inst.terminal_isNil as.val
      simp_all only [Function.iterate_zero, id_eq, forall_true_left, Nat.pred_zero,
        Function.iterate_succ, Function.comp_apply]
    · have := Nat.succ_pred n_zero
      simp_all only

@[simp]
theorem isNil_val {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : FiniteProductiveListLike α β) :
    (PartialListLike.isNil as) = (PartialListLike.isNil as.val) := rfl

@[simp]
theorem head_val {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : FiniteProductiveListLike α β) :
    (PartialListLike.head as) = (PartialListLike.head as.val) := rfl

@[simp]
theorem tail_val {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : FiniteProductiveListLike α β) :
    (PartialListLike.tail as).val = (PartialListLike.tail as.val) := rfl

@[simp]
theorem iterate_tail_val {α : Type u} {β : Type v} [inst : ProductiveListLike α β]
    (as : FiniteProductiveListLike α β) (n : Nat):
    (PartialListLike.tail^[n] as).val = (PartialListLike.tail^[n] as.val) := by
  revert as
  induction n with
  | zero =>
    intro as
    simp_all only [Nat.zero_eq, Function.iterate_zero, id_eq]
  | succ n ih =>
    intro as
    have := ih (PartialListLike.tail as)
    simp_all only [Subtype.forall, forall_exists_index, tail_val, Function.iterate_succ,
      Function.comp_apply]

instance instProductiveListLike (α : Type u) (β : Type v) [inst : ProductiveListLike α β] :
    ProductiveListLike α (FiniteProductiveListLike α β) where
  toPartialListLike := instPartialListLike α β
  terminal_isNil as := inst.terminal_isNil as.val
  consistent_mem a as := by
    have := inst.consistent_mem a as.val
    simp_all only [PartialListLike.Mem, head_val, iterate_tail_val, isNil_val, Membership.mem]

instance instSubtypeListLike (α : Type u) (β : Type v) [inst : ProductiveListLike α β] :
    ListLike α (FiniteProductiveListLike α β) where
  toProductiveListLike := instProductiveListLike α β
  finite as := by
    have := as.property
    simp_all only [PartialListLike.isFinite, isNil_val, iterate_tail_val]

-- structure equivExt {α : Type u} (x₁ : ClassSetoid.Imp (ListLike α))
--     (x₂ : ClassSetoid.Imp (ListLike α)) : Prop where
--   intro ::
--   isNil_eq : x₁.inst.isNil x₁.value ↔ x₂.inst.isNil x₂.value
--   head_heq : HEq (x₁.inst.head x₁.value) (x₂.inst.head x₂.value)

-- instance equivExt.instSetoid {α : Type u} : Setoid (ClassSetoid.Imp <| ListLike α) where
--   r := equivExt
--   iseqv := by
--     constructor
--     · intro x
--       constructor
--       · simp only
--       · simp only [heq_eq_eq]
--     · intro _ _ h
--       constructor
--       · simp only [h.isNil_eq]
--       · simp only [h.head_heq.symm]
--     · intro _ _ _ h₁₂ h₂₃
--       constructor
--       · simp only [h₁₂.isNil_eq, h₂₃.isNil_eq]
--       · have := h₁₂.head_heq
--         simp only [h₁₂.head_heq.trans h₂₃.head_heq]

-- def equiv {α : Type u} (x₁ : ClassSetoid.Imp (ListLike α))
--     (x₂ : ClassSetoid.Imp (ListLike α)) : Prop :=
--   ∀ (n : ℕ), equivExt ⟨x₁.imp, x₁.inst, (x₁.inst.tail^[n] x₁.value)⟩ ⟨x₂.imp, x₂.inst, (x₂.inst.tail^[n] x₂.value)⟩

-- instance instSetoid (α : Type u) : Setoid (ClassSetoid.Imp <| ListLike α) where
--   r := equiv
--   iseqv := by
--     constructor
--     · intro _ _
--       apply equivExt.instSetoid.iseqv.refl
--     · intro _ _ h _
--       simp only [equiv] at h
--       apply equivExt.instSetoid.iseqv.symm
--       simp_all only [Setoid.r]
--     · intro _ x₂ _ h₁₂ h₂₃ n
--       simp only [equiv] at h₁₂ h₂₃
--       apply equivExt.instSetoid.iseqv.trans (y := ⟨x₂.imp, x₂.inst, (x₂.inst.tail)^[n] x₂.value⟩)
--       all_goals simp_all only [Setoid.r]
