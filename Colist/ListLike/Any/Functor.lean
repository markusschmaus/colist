import Colist.ProductiveListLike.Any.Functor
import Colist.ListLike.Class.Functor

universe u v

namespace AnyListLike

abbrev map {α α' : Type u} (f : α → α'): AnyListLike α → AnyListLike α' :=
    Subtype.map (f <$> ·) <| by
  intro as
  intro h
  simp_all only [AnyProductiveListLike.isFinite_map]

instance instFunctor : Functor AnyListLike where
  map := map

@[simp]
theorem map_mk {α α' : Type u} (f : α → α') {imp : Type u} [inst : ListLike α imp]
    (x : imp) : (f <$> mk x : AnyListLike α') = mk (ListLike.map f x) := by
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
theorem map_val {α α' : Type u} (f : α → α') (x : AnyListLike α) :
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
