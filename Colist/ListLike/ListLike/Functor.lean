import Colist.HEq
import Colist.ListLike.AnyPartialListLike
import Colist.ListLike.AnyListLike
import Colist.ListLike.Instances.List
import Colist.ListLike.PartialListLike.Functor

universe u v

namespace ListLike

abbrev Mapped (α α' : Type u) (β : Type v) :=
  Subtype (fun x : PartialListLike.Mapped α α' β => PartialListLike.isFinite α' x)

@[simp]
theorem mk_val_inst_Mapped {α α' : Type u} {β : Type v} {x : PartialListLike.Mapped α α' β} {h : _} :
    (⟨x, h⟩ : Mapped α α' β).val.inst = x.inst := rfl

@[simp]
theorem iterate_tail_inst_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat}  :
    ((PartialListLike.tail α')^[n] x).val.inst = x.val.inst := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    have := ih (x := PartialListLike.tail α' x)
    simp_all only [Function.iterate_succ, Function.comp_apply]
    exact rfl

@[simp]
theorem iterate_tail_f_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat}  :
    ((PartialListLike.tail α')^[n] x).val.f = x.val.f := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    have := ih (x := PartialListLike.tail α' x)
    simp_all only [Function.iterate_succ, Function.comp_apply]
    exact rfl

@[simp]
theorem isNil_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.isNil α' x ↔ PartialListLike.isNil α' x.val :=
  { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {h : _}:
    PartialListLike.head x h = PartialListLike.head (α := α') x.val h := rfl

@[simp]
theorem tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.tail α' x = (PartialListLike.tail α' x.val) := rfl

@[simp]
theorem iterate_tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat} :
    ((PartialListLike.tail α')^[n] x) = ((PartialListLike.tail α')^[n] x.val) := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    simp only [Function.iterate_succ, Function.comp_apply, ih, tail_Mapped]

abbrev map {α α' : Type u} {β : Type v} [inst : ListLike α β] (f : α → α') (b : β) : Mapped α α' β :=
  Subtype.mk {base := b, inst := inst.toPartialListLike, f := f} <| by
    have := inst.finite b
    simp_all only [PartialListLike.isFinite_Mapped]

@[simp]
theorem base_map {α α' : Type u} {β : Type v} [inst : ListLike α β] {f : α → α'} {b : β} :
    (map f b).val.base = b := rfl

@[simp]
theorem f_map {α α' : Type u} {β : Type v} [inst : ListLike α β] {f : α → α'} {b : β} :
    (map f b).val.f = f := rfl

end ListLike

namespace AnyListLike

abbrev map {α α': Type u} (f : α → α'): AnyListLike α → AnyListLike α' :=
    Subtype.map (f <$> ·) <| by
  intro as
  intro h
  simp_all only [AnyPartialListLike.isFinite_map]

instance instFunctor : Functor AnyListLike where
  map := map

@[simp]
theorem map_mk {α α': Type u} (f : α → α') {imp : Type u} [inst : ListLike α imp] (x : imp) :
    (f <$> mk x : AnyListLike α') = mk (ListLike.map f x) := by
  apply Subtype.eq
  simp only [Functor.map, Subtype.map_coe, AnyPartialListLike.mk, AnyPartialListLike.map_mk',
    ClassSetoid.eq, Setoid.r, PartialListLike.equiv, PartialListLike.iterate_tail_Mapped,
    PartialListLike.base_map, PartialListLike.f_map]
  intro n
  constructor
  · simp only [PartialListLike.isNil_Mapped, ListLike.isNil_Mapped, ListLike.iterate_tail_Mapped,
    PartialListLike.iterate_tail_Mapped]
  · refine (heq_of_cast_funext ?_).mp ?_
    · simp only [PartialListLike.isNil_Mapped, ListLike.isNil_Mapped, ListLike.iterate_tail_Mapped,
      PartialListLike.iterate_tail_Mapped]
    · intro h
      congr
      simp only [PartialListLike.map, ListLike.iterate_tail_Mapped,
        PartialListLike.iterate_tail_Mapped]

@[simp]
theorem map_val {α α': Type u} (f : α → α') (x : AnyListLike α) :
    (f <$> x).val = f <$> x.val := by
  simp only [Functor.map, Subtype.map_coe]

instance instLawfulFunctor : LawfulFunctor AnyListLike where
  map_const := by
    exact fun {α β} => rfl
  id_map x := by
    apply Subtype.eq
    simp only [map_val, id_map]
  comp_map f g x := by
    apply Subtype.eq
    simp only [map_val, comp_map]
