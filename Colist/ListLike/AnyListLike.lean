import Colist.ListLike.AnyPartialListLike
import Colist.ListLike.ListLike

universe u v

def Colist (α : Type u) := Subtype (fun (as : AnyPartialListLike α) => PartialListLike.isFinite α as)

namespace Colist

def mk {α : Type u} {β : Type v} [inst : ListLike α β] (x : β) : Colist α :=
  Subtype.mk (AnyPartialListLike.mk x) <| by
    simp only [AnyPartialListLike.isFinite_mk, inst.finite]

instance {α : Type u} {L : Type u → Type v} [ListLike α (L α)] : CoeOut (L α) (Colist α) where
  coe := mk

def tail {α : Type u} (x : Colist α) : Colist α := Subtype.mk (PartialListLike.tail α x.val) <| by
    obtain ⟨_, inst, x', rep⟩ := AnyPartialListLike.exists_rep x.val
    have finite := x.property
    rw [←rep] at *
    simp only [PartialListLike.isFinite, AnyPartialListLike.tail_mk, AnyPartialListLike.iterate_tail_mk,
      AnyPartialListLike.isNil_mk] at *
    obtain ⟨n, is_nil⟩ := finite
    use n.pred
    rw [←Function.iterate_succ_apply _ _ x']
    by_cases h : n ≠ 0
    · simp only [Nat.succ_pred h, is_nil]
    · rw [not_ne_iff.mp h] at is_nil ⊢
      simp only [Function.iterate_zero, id_eq, ne_eq, not_not, Nat.pred_zero, Nat.reduceSucc,
        Function.iterate_succ, Function.comp_apply] at *
      exact inst.terminal_isNil x' is_nil

@[simp]
theorem tail_val {α : Type u} {x : Colist α} : x.tail.val = PartialListLike.tail α x.val := rfl

@[simp]
theorem iterate_tail_val {α : Type u} {x : Colist α} {n : Nat} :
    (tail^[n] x).val = (PartialListLike.tail α)^[n] x.val := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    simp only [Function.iterate_succ, Function.comp_apply]
    rw [←tail_val (x := x)]
    simp only [ih, tail_val]

instance {α : Type u} : ListLike α (Colist α) where
  isNil x := PartialListLike.isNil α x.val
  head x := PartialListLike.head x.val
  tail := tail
  terminal_isNil x := PartialListLike.terminal_isNil x.val
  finite x := by
    have finite := x.property
    unfold PartialListLike.isFinite at *
    simp_all only [PartialListLike.tail, iterate_tail_val]


@[simp]
theorem isNil_mk (α : Type u) {β : Type v} [ListLike α β] {x : β} :
    PartialListLike.isNil α (mk x : Colist α) ↔ PartialListLike.isNil α x := by
  exact { mp := fun a => a, mpr := fun a => a }


@[simp]
theorem head_mk {α : Type u} {β : Type v} [ListLike α β] {x : β} {h : ¬ PartialListLike.isNil α x} :
    PartialListLike.head (mk x : Colist α) h = PartialListLike.head x h := rfl

@[simp]
theorem tail_mk {α : Type u} {β : Type v} [ListLike α β] {x : β} :
    PartialListLike.tail α (mk x : Colist α) = mk (PartialListLike.tail α x) := rfl

@[simp]
theorem iterate_tail_mk (n : Nat) {α : Type u} {β : Type v} [inst : ListLike α β] {x : β} :
    (PartialListLike.tail α)^[n] (mk x : Colist α) = mk ((PartialListLike.tail α)^[n] x) := by
  apply Subtype.mk_eq_mk.mpr
  simp only [PartialListLike.tail, mk, iterate_tail_val, ← AnyPartialListLike.iterate_tail_mk]

@[simp]
theorem isFinite_mk {α : Type u} {β : Type v} [ListLike α β] {x : β} :
    PartialListLike.isFinite α (mk x : Colist α) ↔ PartialListLike.isFinite α x := by
  simp only [PartialListLike.isFinite, iterate_tail_mk, isNil_mk]
