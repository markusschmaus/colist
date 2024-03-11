import Colist.util.HEq
import Colist.ProductiveListLike.Any.Basic
import Colist.ListLike.Any.Basic
import Colist.ProductiveListLike.Class.Functor

universe u v w

namespace ListLike

abbrev Mapped (α : Type u) (α' : Type v) (β : Type w) :=
  Subtype (fun x : ProductiveListLike.Mapped α α' β => PartialListLike.isFinite x)

@[simp]
theorem mk_val_inst_Mapped {α : Type u} {α' : Type v} {β : Type w}
    {x : ProductiveListLike.Mapped α α' β} {h : _} :
    (⟨x, h⟩ : Mapped α α' β).val.inst = x.inst := rfl

@[simp]
theorem iterate_tail_inst_Mapped {α : Type u} {α' : Type v} {β : Type w}
    {x : Mapped α α' β} {n : Nat}  :
    (PartialListLike.tail^[n] x).val.inst = x.val.inst := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    have := ih (x := PartialListLike.tail x)
    simp_all only [Function.iterate_succ, Function.comp_apply]
    exact rfl

@[simp]
theorem iterate_tail_f_Mapped {α : Type u} {α' : Type v} {β : Type w}
    {x : Mapped α α' β} {n : Nat}  :
    (PartialListLike.tail^[n] x).val.f = x.val.f := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    have := ih (x := PartialListLike.tail x)
    simp_all only [Function.iterate_succ, Function.comp_apply]
    exact rfl

@[simp]
theorem isNil_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} :
    PartialListLike.isNil x ↔ PartialListLike.isNil x.val :=
  { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β}
    {h : _} : PartialListLike.head x h = PartialListLike.head x.val h := rfl

@[simp]
theorem tail_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} :
    PartialListLike.tail x = (PartialListLike.tail x.val) := rfl

@[simp]
theorem iterate_tail_Mapped {α : Type u} {α' : Type v} {β : Type w}
    {x : Mapped α α' β} {n : Nat} :
    (PartialListLike.tail^[n] x) = (PartialListLike.tail^[n] x.val) := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    simp only [Function.iterate_succ, Function.comp_apply, ih, tail_Mapped]

abbrev map {α : Type u} {α' : Type v} {β : Type w} [inst : ListLike α β]
    (f : α → α') (b : β) : Mapped α α' β :=
  Subtype.mk {base := b, inst := inst.toProductiveListLike, f := f} <| by
    have := inst.finite b
    simp_all only [ProductiveListLike.Mapped.isFinite_Mapped]

@[simp]
theorem base_map {α : Type u} {α' : Type v} {β : Type w} [inst : ListLike α β]
    {f : α → α'} {b : β} :
    (map f b).val.base = b := rfl

@[simp]
theorem f_map {α : Type u} {α' : Type v} {β : Type w} [inst : ListLike α β]
    {f : α → α'} {b : β} :
    (map f b).val.f = f := rfl
