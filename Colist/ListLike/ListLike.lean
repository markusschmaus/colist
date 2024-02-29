import Mathlib.Tactic
import Colist.ListLike.PartialListLike

universe u v w

class ListLike (α : Type u) (β : Type v) extends PartialListLike α β : Type (max u v) where
  finite (as : β) : PartialListLike.isFinite α as
namespace ListLike

abbrev FinitePartialListLike (α : Type u) (β : Type v) [inst : PartialListLike α β] :=
  Subtype fun as : β => PartialListLike.isFinite (inst := inst) as

instance instSubtypePartialListLike (α : Type u) (β : Type v) [inst : PartialListLike α β] :
    PartialListLike α (FinitePartialListLike α β) where
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
  terminal_isNil as := inst.terminal_isNil as.val

instance instSubtypeListLike (α : Type u) (β : Type v) [inst : PartialListLike α β] :
    ListLike α (FinitePartialListLike α β) where
  toPartialListLike := instSubtypePartialListLike α β
  finite as := by
    unfold PartialListLike.isFinite at *
    obtain ⟨n, val_nil⟩ := as.property
    use n
    revert as val_nil
    induction n with
    | zero =>
      intro as val_nil
      exact val_nil
    | succ n ih =>
      intro as val_nil
      have := ih (PartialListLike.tail α as) val_nil
      simp_all only [Subtype.forall, forall_exists_index, Function.iterate_succ,
        Function.comp_apply]

structure equivExt {α : Type u} (x₁ : ClassSetoid.Imp (ListLike α))
    (x₂ : ClassSetoid.Imp (ListLike α)) : Prop where
  intro ::
  isNil_eq : x₁.inst.isNil x₁.value ↔ x₂.inst.isNil x₂.value
  head_heq : HEq (x₁.inst.head x₁.value) (x₂.inst.head x₂.value)

instance equivExt.instSetoid {α : Type u} : Setoid (ClassSetoid.Imp <| ListLike α) where
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

def equiv {α : Type u} (x₁ : ClassSetoid.Imp (ListLike α))
    (x₂ : ClassSetoid.Imp (ListLike α)) : Prop :=
  ∀ (n : ℕ), equivExt ⟨x₁.imp, x₁.inst, (x₁.inst.tail^[n] x₁.value)⟩ ⟨x₂.imp, x₂.inst, (x₂.inst.tail^[n] x₂.value)⟩

instance instSetoid (α : Type u) : Setoid (ClassSetoid.Imp <| ListLike α) where
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
