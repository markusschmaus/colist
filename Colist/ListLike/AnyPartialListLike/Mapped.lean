import Colist.ListLike.AnyPartialListLike
import Colist.ListLike.Instances.List

universe u v

namespace PartialListLike

structure Mapped (α α' : Type u) (β : Type v) where
  base : β
  [inst : PartialListLike α β]
  f : α → α'

instance Mapped.instPartialListLike {α α' : Type u} {β : Type v} : PartialListLike α' (Mapped α α' β) where
  isNil x := x.inst.isNil x.base
  head x h := x.f <| x.inst.head x.base h
  tail x := {base := x.inst.tail x.base, inst := x.inst, f := x.f}
  terminal_isNil x := x.inst.terminal_isNil x.base

def map {α α' : Type u} {β : Type v} [inst : PartialListLike α β] (f : α → α') (b : β) : Mapped α α' β :=
  {base := b, inst := inst, f := f}

@[simp]
theorem isNil_map {α α' : Type u} {β : Type v} [inst : PartialListLike α β] {f : α → α'} {b : β} :
    PartialListLike.isNil α' (map f b (inst := inst)) = inst.isNil b := rfl

@[simp]
theorem head_map {α α' : Type u} {β : Type v} [inst : PartialListLike α β] {f : α → α'} {b : β} {h : ¬ PartialListLike.isNil α b} :
    PartialListLike.head (α := α') (map f b (inst := inst)) h = f (inst.head b h) := rfl

@[simp]
theorem tail_map {α α' : Type u} {β : Type v} [inst : PartialListLike α β] {f : α → α'} {b : β} :
    PartialListLike.tail α' (map f b (inst := inst)) = map f (inst.tail b) := rfl

@[simp]
theorem iterate_tail_map {α α' : Type u} {β : Type v} [inst : PartialListLike α β] {f : α → α'} {b : β} {n : Nat} :
    (PartialListLike.tail α')^[n] (map f b (inst := inst)) = map f (inst.tail^[n] b) := by
  revert b
  induction n with
  | zero =>
    intro b
    rfl
  | succ n ih =>
    intro b
    simp only [Function.iterate_succ, Function.comp_apply, tail_map, ih]

end PartialListLike

theorem heq_of_cast_funext {α α': Sort u} {β :Sort v} {f : α → β} {g : α' → β} (type_eq : α = α') :
    (∀ (x : α), f x = g (cast type_eq x)) ↔ HEq f g := by
  constructor
  · intro funext
    apply heq_of_cast_eq (implies_congr type_eq rfl)
    subst type_eq
    simp_all only [cast_eq]
    funext
    simp_all only
  · intro heq x
    exact congr_heq heq (heq_of_cast_eq type_eq rfl)

namespace AnyPartialListLike

def map {α α': Type u} (f : α → α'): AnyPartialListLike α → AnyPartialListLike α' :=
  let inst' {imp : Type u} (_ : PartialListLike α imp) : PartialListLike α' (PartialListLike.Mapped α α' imp) :=
    PartialListLike.Mapped.instPartialListLike (α := α) (α' := α')
  let map {imp : Type u} (inst : PartialListLike α imp) (x : imp) : PartialListLike.Mapped α α' imp :=
    PartialListLike.map f x (inst := inst)
  ClassSetoid.liftGen (PartialListLike.instSetoid α) (PartialListLike.instSetoid α') inst' map <| by
    simp_all only [ClassSetoid.liftGen.Precondition, Setoid.r, PartialListLike.equiv]
    intro a b h n
    have isNil_eq := h n |>.isNil_eq
    have head_heq := h n |>.head_heq
    simp_all only
    rw [PartialListLike.iterate_tail_map (inst := a.inst)] at *
    rw [PartialListLike.iterate_tail_map (inst := b.inst)] at *
    constructor
    · exact isNil_eq
    · simp_all only

      refine (heq_of_cast_funext ?_).mp ?_
      · rw [PartialListLike.isNil_map (inst := a.inst)] at *
        rw [PartialListLike.isNil_map (inst := b.inst)] at *
        simp_all only
      · intro x
        rw [PartialListLike.head_map (inst := a.inst)] at *
        rw [PartialListLike.head_map (inst := b.inst)] at *
        apply congr_arg
        refine (heq_of_cast_funext ?_).mpr head_heq ?_
        simp_all only

instance instFunctor : Functor AnyPartialListLike where
  map := map

-- instance instLawfulFunctor : LawfulFunctor AnyPartialListLike where
--   map_const := by
--     exact fun {α β} => rfl
--   id_map x := by
--     obtain ⟨x', rep⟩ := ClassSetoid.exists_rep x
--     sorry
--   comp_map f g x := by
--     sorry
