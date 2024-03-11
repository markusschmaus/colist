import Colist.ProductiveListLike.Any.Basic
import Colist.ProductiveListLike.Class.Functor

universe u w

namespace AnyProductiveListLike

abbrev map {α α' : Type u} (f : α → α'): AnyProductiveListLike α → AnyProductiveListLike α' :=
  let inst' {imp : Type u} (_ : ProductiveListLike α imp) :
      ProductiveListLike α' (ProductiveListLike.Mapped α α' imp) :=
    inferInstance
  let map {imp : Type u} (inst : ProductiveListLike α imp) (x : imp) :
      ProductiveListLike.Mapped α α' imp :=
    ProductiveListLike.map f x
  ClassSetoid.liftGen (ProductiveListLike.setoid α)
      (ProductiveListLike.setoid α') inst' map <| by
    simp_all only [ClassSetoid.liftGen.Precondition, Setoid.r, PartialListLike.equiv]
    intro a b h n
    have isNil_eq := h n |>.isNil_eq
    have head_heq := h n |>.head_heq
    simp_all only
    rw [ProductiveListLike.iterate_tail_map (inst := a.inst)] at *
    rw [ProductiveListLike.iterate_tail_map (inst := b.inst)] at *
    constructor
    · exact isNil_eq
    · simp_all only

      refine (heq_of_cast_funext ?_).mp ?_
      · rw [ProductiveListLike.isNil_map (inst := a.inst)] at *
        rw [ProductiveListLike.isNil_map (inst := b.inst)] at *
        simp_all only
      · intro x
        rw [ProductiveListLike.head_map (inst := a.inst)] at *
        rw [ProductiveListLike.head_map (inst := b.inst)] at *
        apply congr_arg
        refine (heq_of_cast_funext ?_).mpr head_heq ?_
        simp_all only

instance instFunctor : Functor AnyProductiveListLike where
  map := map

@[simp]
theorem map_mk {α α' : Type u} (f : α → α') {imp : Type u}
    [inst : ProductiveListLike α imp] (x : imp) :
    (f <$> mk x : AnyProductiveListLike α') = mk (ProductiveListLike.map f x) := rfl

@[simp]
theorem map_mk' {α α' : Type u} (f : α → α') {imp : Type u}
    [inst : ProductiveListLike α imp] (x : imp) :
    (map f (mk x) : AnyProductiveListLike α') = mk (ProductiveListLike.map f x) := rfl

@[simp]
theorem isNil_map {α α' : Type u} {f : α → α'} {x : AnyProductiveListLike α} :
    AnyProductiveListLike.isNil (f <$> x) ↔ AnyProductiveListLike.isNil x := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk, ClassSetoid.lift_mk, ProductiveListLike.Mapped.isNil_Mapped,
    ProductiveListLike.base_map]

@[simp]
theorem head_map {α α' : Type u} {f : α → α'} {x : AnyProductiveListLike α} {h : _} :
    (f <$> x).head h = f (x.head (isNil_map.not.mp h)) := by

  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk]
  apply ClassSetoid.lift_prop_mk

@[simp]
theorem tail_map {α α' : Type u} (f : α → α') (x : AnyProductiveListLike α) :
    (f <$> x).tail = f <$> x.tail := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk, ClassSetoid.liftGen_mk, id_eq, ProductiveListLike.tail_map]

@[simp]
theorem isFinite_map {α α' : Type u} (f : α → α') (x : AnyProductiveListLike α) :
    PartialListLike.isFinite (f <$> x) ↔ PartialListLike.isFinite x := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  rw [←rep]
  simp only [map_mk, mk, isFinite_mk, ProductiveListLike.Mapped.isFinite_Mapped,
    ProductiveListLike.base_map]

instance instLawfulFunctor : LawfulFunctor AnyProductiveListLike where
  map_const := by
    exact fun {α β} => rfl
  id_map x := by
    obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
    rw [←rep]
    simp only [map_mk, mk, ClassSetoid.eq, Setoid.r, PartialListLike.equiv,
      ProductiveListLike.iterate_tail_map]
    intro n
    constructor
    · exact { mp := fun a => a, mpr := fun a => a }
    · refine' HEq.refl _
  comp_map f g x := by
    obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
    rw [←rep]
    simp only [map_mk, mk, ClassSetoid.eq, Setoid.r, PartialListLike.equiv,
      ProductiveListLike.iterate_tail_map]
    intro n
    constructor
    · exact { mp := fun a => a, mpr := fun a => a }
    · refine' HEq.refl _
