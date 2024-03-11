import Colist.util.HEq
import Colist.ProductiveListLike.Class.Basic

universe u v w

namespace ProductiveListLike

structure Mapped (α : Type u) (α' : Type v) (β : Type w) where
  [inst : ProductiveListLike α β]
  base : β
  f : α → α'

namespace Mapped

instance instMembership {α : Type u} {α' : Type v} {β : Type w} :
    Membership α' (Mapped α α' β) where
  mem a' as := ∃ a : α, a' = as.f a ∧ as.inst.instMembership.mem a as.base

instance instPartialListLike {α : Type u} {α' : Type v} {β : Type w} :
    PartialListLike α' (Mapped α α' β) where
  isNil as := as.inst.isNil as.base
  head as h := as.f <| as.inst.head as.base h
  tail as := {base := as.inst.tail as.base, inst := as.inst, f := as.f}

theorem mk.explode {α : Type u} {α' : Type v} {β : Type w} (as : Mapped α α' β) :
    as = Mapped.mk (inst := as.inst) as.base as.f := rfl

@[simp]
theorem isNil_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} :
    PartialListLike.isNil x ↔ x.inst.isNil x.base := { mp := fun a => a, mpr := fun a => a }

@[simp]
theorem head_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} {h : _}:
    PartialListLike.head x h = x.f (x.inst.head x.base h) := rfl

@[simp]
theorem tail_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} :
    (PartialListLike.tail x) = Mapped.mk (inst := x.inst) (x.inst.tail x.base) x.f := rfl

@[simp]
theorem iterate_tail_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} {n : Nat} :
    (PartialListLike.tail^[n] x) = Mapped.mk (inst := x.inst)
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
theorem isFinite_Mapped {α : Type u} {α' : Type v} {β : Type w} {x : Mapped α α' β} :
    PartialListLike.isFinite x ↔ PartialListLike.isFinite
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
      have := ih (x := PartialListLike.tail x)
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
      have := ih (x := PartialListLike.tail x)
      simp_all only [iterate_tail_Mapped, isNil_Mapped, implies_true, Function.iterate_succ,
        Function.comp_apply, tail_Mapped, forall_true_left]


@[simp]
theorem Mem_Mapped {α : Type u} {α' : Type v} {β : Type w} {as : Mapped α α' β} {a' : α'}:
    PartialListLike.Mem (a') as ↔
    ∃ a : α, a' = as.f a ∧ PartialListLike.Mem (inst := as.inst.toPartialListLike) a as.base := by
  constructor
  · unfold PartialListLike.Mem
    simp only [iterate_tail_Mapped, head_Mapped, isNil_Mapped]
    intro ⟨n, is_nil, eq⟩
    use (as.inst.head (as.inst.tail^[n] as.base) ?not_nil)
    rotate_right
    · simp_all only [not_false_eq_true]
    simp_all only [true_and]
    use n
    simp_all only [not_false_eq_true, exists_const]
  · unfold PartialListLike.Mem
    simp only [iterate_tail_Mapped, head_Mapped, isNil_Mapped]
    intro ⟨a, ⟨eq', ⟨n, ⟨is_nil, eq⟩⟩⟩⟩
    use n
    simp_all only [not_false_eq_true, exists_const]

instance instProductiveListLike {α : Type u} {α' : Type v} {β : Type w} :
    ProductiveListLike α' (Mapped α α' β) where
  isNil as := as.inst.isNil as.base
  head as h := as.f <| as.inst.head as.base h
  tail as := {base := as.inst.tail as.base, inst := as.inst, f := as.f}
  consistent_mem a' as := by
    simp?
    constructor
    · intro ⟨a, ⟨_, _⟩⟩
      have := as.inst.consistent_mem a as.base
      simp only [Membership.mem]
      use a
      simp_all only [iff_true, and_self]
    · intro ⟨a, ⟨_, _⟩⟩
      have := as.inst.consistent_mem a as.base
      use a
      simp_all only [iff_true, and_self]
  terminal_isNil as := as.inst.terminal_isNil as.base

end Mapped

def map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β] (f : α → α')
    (b : β) : Mapped α α' β :=
  {base := b, inst := inferInstance, f := f}

@[simp]
theorem base_map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    (map f b).base = b := rfl

@[simp]
theorem f_map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    (map f b).f = f := rfl

@[simp]
theorem isNil_map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    PartialListLike.isNil (map f b) = PartialListLike.isNil b := rfl

@[simp]
theorem head_map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} {h : ¬ PartialListLike.isNil b} :
    PartialListLike.head (α := α') (map f b) h = f (PartialListLike.head b h) := rfl

@[simp]
theorem tail_map {α : Type u} {α' : Type v} {β : Type w} [inst : ProductiveListLike α β]
    {f : α → α'} {b : β} :
    PartialListLike.tail (map f b) = map f (PartialListLike.tail b) := rfl

@[simp]
theorem iterate_tail_map {α : Type u} {α' : Type v} {β : Type w}
    [inst : ProductiveListLike α β] {f : α → α'} {b : β} {n : Nat} :
    PartialListLike.tail^[n] (map f b) = map f (PartialListLike.tail^[n] b) := by
  revert b
  induction n with
  | zero =>
    intro b
    rfl
  | succ n ih =>
    intro b
    simp only [Function.iterate_succ, Function.comp_apply, tail_map, ih]

@[simp]
theorem isFinite_map {α : Type u} {α' : Type v} {β : Type w} [ProductiveListLike α β]
    {f : α → α'} {b : β} {n : Nat} :
    PartialListLike.isFinite (map f b) ↔ PartialListLike.isFinite b := by
  simp only [Mapped.isFinite_Mapped, base_map]
