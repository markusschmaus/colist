import Colist.util.HEq
import Colist.ListLike.AnyProductiveListLike

universe u v

namespace ProductiveListLike

structure Mapped (α α' : Type u) (β : Type v) where
  [inst : ProductiveListLike α β]
  base : β
  f : α → α'

instance Mapped.instProductiveListLike {α α' : Type u} {β : Type v} :
    ProductiveListLike α' (Mapped α α' β) where
  isNil x := x.inst.isNil x.base
  head x h := x.f <| x.inst.head x.base h
  tail x := {base := x.inst.tail x.base, inst := x.inst, f := x.f}
  terminal_isNil x := x.inst.terminal_isNil x.base

@[simp]
theorem isNil_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.isNil α' x ↔ x.inst.isNil x.base := { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {h : _}:
    PartialListLike.head x h = x.f (x.inst.head x.base h) := rfl

@[simp]
theorem tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    (PartialListLike.tail α' x) = Mapped.mk (inst := x.inst) (x.inst.tail x.base) x.f := rfl

@[simp]
theorem iterate_tail_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} {n : Nat} :
    ((PartialListLike.tail α')^[n] x) = Mapped.mk (inst := x.inst)
    (x.inst.tail^[n] x.base) x.f := by
  revert x
  induction n with
  | zero =>
    intro x
    rfl
  | succ n ih =>
    intro x
    simp only [Function.iterate_succ, Function.comp_apply, ih, tail_Mapped]

@[simp]
theorem isFinite_Mapped {α α' : Type u} {β : Type v} {x : Mapped α α' β} :
    PartialListLike.isFinite α' x ↔ PartialListLike.isFinite
    (inst := x.inst.toPartialListLike) x.base := by
  constructor
  · intro ⟨n, tail_nil⟩
    use n
    revert x
    induction n with
    | zero =>
      intro x tail_nil
      exact tail_nil
    | succ n ih =>
      intro x tail_nil
      have := ih (x := PartialListLike.tail α' x)
      simp_all only [iterate_tail_Mapped, isNil_Mapped, implies_true, Function.iterate_succ,
        Function.comp_apply, tail_Mapped, forall_true_left]
  · intro ⟨n, tail_nil⟩
    use n
    revert x
    induction n with
    | zero =>
      intro x tail_nil
      exact tail_nil
    | succ n ih =>
      intro x tail_nil
      have := ih (x := PartialListLike.tail α' x)
      simp_all only [iterate_tail_Mapped, isNil_Mapped, implies_true, Function.iterate_succ,
        Function.comp_apply, tail_Mapped, forall_true_left]

def map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β] (f : α → α')
    (b : β) : Mapped α α' β :=
  {base := b, inst := inferInstance, f := f}

@[simp]
theorem base_map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    (map f b).base = b := rfl

@[simp]
theorem f_map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    (map f b).f = f := rfl

@[simp]
theorem isNil_map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    PartialListLike.isNil α' (map f b) = PartialListLike.isNil α b := rfl

@[simp]
theorem head_map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} {h : ¬ PartialListLike.isNil α b} :
    PartialListLike.head (α := α') (map f b) h = f (PartialListLike.head b h) := rfl

@[simp]
theorem tail_map {α α' : Type u} {β : Type v} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    PartialListLike.tail α' (map f b) = map f (PartialListLike.tail α b) := rfl

@[simp]
theorem iterate_tail_map {α α' : Type u} {β : Type v}
    [inst : ProductiveListLike α β] {f : α → α'} {b : β} {n : Nat} :
    (PartialListLike.tail α')^[n] (map f b) = map f ((PartialListLike.tail α)^[n] b) := by
  revert b
  induction n with
  | zero =>
    intro b
    rfl
  | succ n ih =>
    intro b
    simp only [Function.iterate_succ, Function.comp_apply, tail_map, ih]

@[simp]
theorem isFinite_map {α α' : Type u} {β : Type v} [ProductiveListLike α β]
    {f : α → α'} {b : β} {n : Nat} :
    PartialListLike.isFinite α' (map f b) ↔ PartialListLike.isFinite α b := by
  simp only [isFinite_Mapped, base_map]

end ProductiveListLike

namespace AnyProductiveListLike

abbrev map {α α': Type u} (f : α → α'): AnyProductiveListLike α → AnyProductiveListLike α' :=
  let inst' {imp : Type u} (_ : ProductiveListLike α imp) :
      ProductiveListLike α' (ProductiveListLike.Mapped α α' imp) :=
    inferInstance
  let map {imp : Type u} (inst : ProductiveListLike α imp) (x : imp) :
      ProductiveListLike.Mapped α α' imp :=
    ProductiveListLike.map f x
  ClassSetoid.liftGen (ProductiveListLike.setoid α) (ProductiveListLike.setoid α') inst' map <| by
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
theorem map_mk {α α': Type u} (f : α → α') {imp : Type u}
    [inst : ProductiveListLike α imp] (x : imp) :
    (f <$> mk x : AnyProductiveListLike α') = mk (ProductiveListLike.map f x) := rfl

@[simp]
theorem map_mk' {α α': Type u} (f : α → α') {imp : Type u}
    [inst : ProductiveListLike α imp] (x : imp) :
    (map f (mk x) : AnyProductiveListLike α') = mk (ProductiveListLike.map f x) := rfl

@[simp]
theorem isNil_map {α α': Type u} {f : α → α'} {x : AnyProductiveListLike α} :
    AnyProductiveListLike.isNil (f <$> x) ↔ AnyProductiveListLike.isNil x := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk, ClassSetoid.lift_mk, ProductiveListLike.isNil_Mapped,
    ProductiveListLike.base_map]

@[simp]
theorem head_map {α α': Type u} {f : α → α'} {x : AnyProductiveListLike α} {h : _} :
    (f <$> x).head h = f (x.head (isNil_map.not.mp h)) := by

  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk]
  apply ClassSetoid.lift_prop_mk

@[simp]
theorem tail_map {α α': Type u} (f : α → α') (x : AnyProductiveListLike α) :
    (f <$> x).tail = f <$> x.tail := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  subst rep
  simp only [map_mk, mk, ClassSetoid.liftGen_mk, id_eq, ProductiveListLike.tail_map]

@[simp]
theorem isFinite_map {α α': Type u} (f : α → α') (x : AnyProductiveListLike α) :
    PartialListLike.isFinite α' (f <$> x) ↔ PartialListLike.isFinite α x := by
  obtain ⟨imp, inst, x', rep⟩ := (ProductiveListLike.setoid _).exists_rep x
  rw [←rep]
  simp only [map_mk, mk, isFinite_mk, ProductiveListLike.isFinite_Mapped,
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
