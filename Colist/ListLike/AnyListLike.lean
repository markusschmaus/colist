import Colist.ListLike.AnyProductiveListLike
import Colist.ListLike.ListLike.Basic
import Colist.util.Subtype

universe u v

abbrev AnyListLike (α : Type u) :=
  Subtype (fun (as : AnyProductiveListLike α) => PartialListLike.isFinite as)

namespace AnyListLike

abbrev mk {α : Type u} {β : Type v} [inst : ListLike α β] (x : β) : AnyListLike α :=
  Subtype.mk (AnyProductiveListLike.mk x) <| by
    simp only [AnyProductiveListLike.isFinite_mk, inst.finite]

instance {α : Type u} {L : Type u → Type v} [ListLike α (L α)] : CoeOut (L α) (AnyListLike α) where
  coe := mk

abbrev tail {α : Type u} : AnyListLike α → AnyListLike α := Subtype.map AnyProductiveListLike.tail <| by
  intro x finite
  obtain ⟨n, is_nil⟩ := finite
  obtain ⟨_, inst, x', rep⟩ := ProductiveListLike.setoid α |>.exists_rep x
  rw [←rep] at is_nil ⊢
  use n.pred
  simp only [PartialListLike.isNil, PartialListLike.tail, ClassSetoid.liftGen_mk, id_eq,
    ClassSetoid.iterate_liftEndo_mk, ClassSetoid.lift_mk] at is_nil ⊢
  rw [←Function.iterate_succ_apply _ _ x']
  by_cases h : n ≠ 0
  · simp only [Nat.succ_pred h, is_nil]
  · rw [not_ne_iff.mp h] at is_nil ⊢
    simp only [Function.iterate_zero, id_eq, Nat.pred_zero, Nat.reduceSucc, Function.iterate_succ,
      Function.comp_apply] at is_nil ⊢
    exact inst.terminal_isNil x' is_nil

instance {α : Type u} : ListLike α (AnyListLike α) where
  isNil x := PartialListLike.isNil x.val
  head x := PartialListLike.head x.val
  tail := tail
  terminal_isNil x := ProductiveListLike.terminal_isNil (α := α) x.val
  finite x := by
    have finite := x.property
    unfold PartialListLike.isFinite at *
    simp_all only [PartialListLike.isNil, PartialListLike.tail, Subtype.iterate_map_coe]
