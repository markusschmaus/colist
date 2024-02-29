import Colist.ListLike.AnyListLike

universe u v

namespace ListLike

structure Filtered (α : Type u) (β : Type v) where
  [inst : ListLike α β]
  p : α → Prop
  [decP : DecidablePred p]
  head? : Option α
  baseTail : β
  valid : (h : ¬ head = none) → p (head.get (Option.ne_none_iff_isSome.mp h))
  terminal_none : head = none → inst.isNil tail

namespace Filtered

def tail {α : Type u} {β : Type v} (x : Filtered α β) : Filtered α β :=

  let rec loop (iter : Nat) (baseTail : β) : (Option (Subtype x.p)) × β :=
    if is_nil : x.inst.isNil baseTail then (none, baseTail)
    else
      let head := x.inst.head baseTail is_nil
      let _ := x.decP head
      if proof : x.p head then (some ⟨head, proof⟩, x.inst.tail baseTail)
      else
        loop (iter.succ) (x.inst.tail baseTail)
  termination_by

instance Mapped.instListLike {α : Type u} {β : Type v} :
    ListLike α (Filtered α β) where
  isNil x := x.head = none
  head x h := x.head.get (Option.ne_none_iff_isSome.mp h)
  tail x := Filtered.mk x.p
  terminal_isNil x := x.inst.terminal_isNil x.base
