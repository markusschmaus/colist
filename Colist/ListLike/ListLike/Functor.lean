import Colist.util.HEq
import Colist.ListLike.AnyProductiveListLike
import Colist.ListLike.AnyListLike
import Colist.ListLike.Instances.List
import Colist.ListLike.ProductiveListLike.Functor

universe u v

namespace ListLike

abbrev Mapped (α α' : Type u) (β : Type v) :=
  Subtype (fun x : ProductiveListLike.Mapped α α' β => PartialListLike.isFinite x)

@[simp]
theorem mk_val_inst_Mapped {α α' : Type u} {β : Type v}
    {x : ProductiveListLike.Mapped α α' β} {h : _} :
    (⟨x, h⟩ : Mapped α α' β).val.inst = x.inst := rfl

@[simp]
theorem iterate_tail_inst_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat}  :
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
theorem iterate_tail_f_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat}  :
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
theorem isNil_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.isNil x ↔ PartialListLike.isNil x.val :=
  { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {h : _}:
    PartialListLike.head x h = PartialListLike.head x.val h := rfl

@[simp]
theorem tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.tail x = (PartialListLike.tail x.val) := rfl

@[simp]
theorem iterate_tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat} :
    (PartialListLike.tail^[n] x) = (PartialListLike.tail^[n] x.val) := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    simp only [Function.iterate_succ, Function.comp_apply, ih, tail_Mapped]

abbrev map {α α' : Type u} {β : Type v} [inst : ListLike α β] (f : α → α') (b : β) : Mapped α α' β :=
  Subtype.mk {base := b, inst := inst.toProductiveListLike, f := f} <| by
    have := inst.finite b
    simp_all only [ProductiveListLike.Mapped.isFinite_Mapped]

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
  simp_all only [AnyProductiveListLike.isFinite_map]

instance instFunctor : Functor AnyListLike where
  map := map

@[simp]
theorem map_mk {α α': Type u} (f : α → α') {imp : Type u} [inst : ListLike α imp] (x : imp) :
    (f <$> mk x : AnyListLike α') = mk (ListLike.map f x) := by
  apply Subtype.eq
  simp only [Functor.map, Subtype.map_coe, AnyProductiveListLike.mk, AnyProductiveListLike.map_mk',
    ClassSetoid.eq, Setoid.r, PartialListLike.equiv, ProductiveListLike.Mapped.iterate_tail_Mapped,
    ProductiveListLike.base_map, ProductiveListLike.f_map]
  intro n
  constructor
  · simp only [ProductiveListLike.Mapped.isNil_Mapped, ListLike.isNil_Mapped, ListLike.iterate_tail_Mapped,
    ProductiveListLike.Mapped.iterate_tail_Mapped]
  · refine (heq_of_cast_funext ?_).mp ?_
    · simp only [ProductiveListLike.Mapped.isNil_Mapped, ListLike.isNil_Mapped, ListLike.iterate_tail_Mapped,
      ProductiveListLike.Mapped.iterate_tail_Mapped]
    · intro h
      congr
      simp only [ProductiveListLike.map, ListLike.iterate_tail_Mapped,
        ProductiveListLike.Mapped.iterate_tail_Mapped]

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
