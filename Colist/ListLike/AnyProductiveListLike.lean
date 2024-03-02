import Colist.ListLike.ProductiveListLike.Basic

universe u v w

abbrev AnyProductiveListLike (α : Type u) := (ProductiveListLike.setoid α).Quotient

namespace AnyProductiveListLike

@[simp]
abbrev mk {α : Type u} {β : Type v} [inst : ProductiveListLike α β] (x : β) :=
  (ProductiveListLike.setoid α).mkQuotient x

instance {α : Type u} {L : Type u → Type v} [ProductiveListLike α (L α)] :
    CoeOut (L α) (AnyProductiveListLike α) where
  coe := mk

abbrev isNil {α : Type u} : AnyProductiveListLike α → Prop :=
    ClassSetoid.lift (ProductiveListLike.setoid α) (·.isNil) <| by
  constructor
  · simp only [implies_true]
  · simp only [Setoid.r, heq_eq_eq, eq_iff_iff]
    intro _ _ _ _ _ _ h
    have := (h 0).isNil_eq
    simp_all only [Function.iterate_zero, id_eq]


instance instDecidableIsNil {α : Type u} :
    (as : AnyProductiveListLike α) → Decidable (isNil as) :=
    ClassSetoid.lift (ProductiveListLike.setoid α) (·.instDecidableIsNil) <| by
  constructor
  · exact fun x => rfl
  · intro _ _ inst inst' x x' equiv
    have isNil_eq := equiv 0 |>.isNil_eq
    have type_eq :
        Decidable (PartialListLike.isNil α x) =
        Decidable (PartialListLike.isNil α x') := by
      simp_all only [Function.iterate_zero, id_eq]
    apply Subsingleton.helim type_eq

abbrev head {α : Type u} : (as : AnyProductiveListLike α) → ¬ isNil as → α :=
    ClassSetoid.lift (ProductiveListLike.setoid α) (·.head) <| by
  constructor
  · intro x
    have : HEq (isNil ⟦x⟧) (x.inst.isNil x.value) := by
      unfold isNil
      refine ClassSetoid.lift_mk_heq _
    rw [eq_of_heq this]
  · simp only [Setoid.r]
    intro _ _ _ _ _ _ h
    have := (h 0).head_heq
    simp_all only [Function.iterate_zero, id_eq]

abbrev tail {α : Type u} : AnyProductiveListLike α → AnyProductiveListLike α :=
    ClassSetoid.liftEndo (ProductiveListLike.setoid α) (·.tail) <| by
  simp_all only [ClassSetoid.liftGen.Precondition, Setoid.r,
    PartialListLike.equiv, id_eq]
  intro _ _ h n
  have := h n.succ
  simp_all only [Function.iterate_succ, Function.comp_apply]

theorem terminal_isNil {α : Type u} (as : AnyProductiveListLike α) :
    isNil as → isNil (tail as) := by
  obtain ⟨x, rep⟩ := Quotient.exists_rep as
  rw [← rep]
  exact x.inst.terminal_isNil x.value

instance instProductiveListLike {α : Type u} :
    ProductiveListLike α (AnyProductiveListLike α) where
  isNil := isNil
  head := head
  tail := tail
  terminal_isNil := terminal_isNil

@[simp]
theorem isFinite_mk {α : Type u} {β : Type v} [ProductiveListLike α β] {x : β} :
    PartialListLike.isFinite α (mk x : AnyProductiveListLike α) ↔ PartialListLike.isFinite α x := by
  simp only [PartialListLike.isFinite, PartialListLike.isNil, PartialListLike.tail,
    ClassSetoid.iterate_liftEndo_mk, ClassSetoid.lift_mk]
