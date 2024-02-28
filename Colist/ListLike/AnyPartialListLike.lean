import Colist.ListLike.PartialListLike

universe u v w

abbrev AnyPartialListLike (α : Type u) := (PartialListLike.setoid α).Quotient

namespace AnyPartialListLike

@[simp]
abbrev mk {α : Type u} {β : Type v} [inst : PartialListLike α β] (x : β) :=
  (PartialListLike.setoid α).mkQuotient x

instance {α : Type u} {L : Type u → Type v} [PartialListLike α (L α)] : CoeOut (L α) (AnyPartialListLike α) where
  coe := mk

abbrev isNil {α : Type u} : AnyPartialListLike α → Prop := ClassSetoid.lift (PartialListLike.setoid α) (·.isNil) <| by
  constructor
  · simp only [implies_true]
  · simp only [Setoid.r, heq_eq_eq, eq_iff_iff]
    intro _ _ _ _ _ _ h
    have := (h 0).isNil_eq
    simp_all only [Function.iterate_zero, id_eq]

instance instDecidableIsNil {α : Type u} : (as : AnyPartialListLike α) → Decidable (isNil as) := ClassSetoid.lift (PartialListLike.setoid α) (·.instDecidableIsNil) <| by
  constructor
  · exact fun x => rfl
  · intro _ _ inst inst' x x' equiv
    have isNil_eq := equiv 0 |>.isNil_eq
    have type_eq : Decidable (PartialListLike.isNil α x) = Decidable (PartialListLike.isNil α x') := by
      simp_all only [Function.iterate_zero, id_eq]
    apply Subsingleton.helim type_eq

abbrev head {α : Type u} : (as : AnyPartialListLike α) → ¬ isNil as → α :=
    ClassSetoid.lift (PartialListLike.setoid α) (·.head) <| by
  constructor
  · intro x
    have : HEq (isNil ⟦x⟧) (x.inst.isNil x.value) := by
      unfold isNil
      refine ClassSetoid.lift_mk_heq (PartialListLike.setoid α) (·.isNil) _ _ _
    rw [eq_of_heq this]
  · simp only [Setoid.r]
    intro _ _ _ _ _ _ h
    have := (h 0).head_heq
    simp_all only [Function.iterate_zero, id_eq]

abbrev tail {α : Type u} : AnyPartialListLike α → AnyPartialListLike α :=
    ClassSetoid.liftEndo (PartialListLike.setoid α) (·.tail) <| by
  simp_all [Setoid.r, PartialListLike.equiv, PartialListLike.equivExt]
  intro _ _ h n
  have := h n.succ
  simp_all only [Function.iterate_succ, Function.comp_apply]

theorem terminal_isNil {α : Type u} (as : AnyPartialListLike α) : isNil as → isNil (tail as) := by
    obtain ⟨x, rep⟩ := Quotient.exists_rep as
    rw [← rep]
    exact x.inst.terminal_isNil x.value

instance instPartialListLike {α : Type u} : PartialListLike α (AnyPartialListLike α) where
  isNil := isNil
  head := head
  tail := tail
  terminal_isNil := terminal_isNil

@[simp]
theorem isFinite_mk {α : Type u} {β : Type v} [PartialListLike α β] {x : β} :
    PartialListLike.isFinite α (mk x : AnyPartialListLike α) ↔ PartialListLike.isFinite α x := by
  simp only [PartialListLike.isFinite, PartialListLike.isNil, PartialListLike.tail,
    ClassSetoid.iterate_liftEndo_mk, ClassSetoid.lift_mk]
