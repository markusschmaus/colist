import Colist.ProductiveListLike.Class.Basic

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
        Decidable (PartialListLike.isNil x) =
        Decidable (PartialListLike.isNil x') := by
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

abbrev contains {α : Type u} : AnyProductiveListLike α → α → Prop :=
    ClassSetoid.lift (ProductiveListLike.setoid α) (·.contains) <| by
  constructor
  · simp only [implies_true]
  · simp_all only [heq_eq_eq]
    intro _ _ inst₁ inst₂ x₁ x₂ equiv
    funext
    simp only [PartialListLike.contains, ← inst₁.consistent_mem, PartialListLike.Mem, ←
      inst₂.consistent_mem, eq_iff_iff]
    constructor
    · intro ⟨n, is_nil, x_eq⟩
      have is_nil' := equiv n |>.isNil_eq.not.mp is_nil
      use n
      use is_nil'
      simp_all only
      refine' congr_heq (equiv n |>.head_heq) _
      apply heq_prop
    · intro ⟨n, is_nil, x_eq⟩
      have is_nil' := equiv n |>.isNil_eq.not.mpr is_nil
      use n
      use is_nil'
      simp_all only
      refine' congr_heq (equiv n |>.head_heq).symm _
      apply heq_prop

instance instMembership {α : Type u} : Membership α (AnyProductiveListLike α) where
  mem a as := contains as a

instance instPartialListLike {α : Type u} :
    PartialListLike α (AnyProductiveListLike α) where
  isNil := isNil
  head := head
  tail := tail

instance instProductiveListLike {α : Type u} :
    ProductiveListLike α (AnyProductiveListLike α) where
  toPartialListLike := instPartialListLike
  consistent_mem a as := by
    obtain ⟨imp, inst, x, rep⟩ := ClassSetoid.exists_rep as
    rw [← rep]; clear rep
    have := inst.consistent_mem a x
    simp_all only [PartialListLike.Mem, PartialListLike.contains, PartialListLike.head,
      PartialListLike.tail, ClassSetoid.iterate_liftEndo_mk, PartialListLike.isNil,
      ClassSetoid.lift_mk, not_false_eq_true, ClassSetoid.lift_prop_mk, Membership.mem,
      implies_true]
  terminal_isNil as := by
    obtain ⟨x, rep⟩ := Quotient.exists_rep as
    rw [← rep]
    exact x.inst.terminal_isNil x.value

@[simp]
theorem isFinite_mk {α : Type u} {β : Type v} [ProductiveListLike α β] {x : β} :
    PartialListLike.isFinite (mk x : AnyProductiveListLike α) ↔ PartialListLike.isFinite x := by
  simp only [PartialListLike.isFinite, PartialListLike.isNil, PartialListLike.tail,
    ClassSetoid.iterate_liftEndo_mk, ClassSetoid.lift_mk]
