import Colist.StreamLike.StreamLike

universe u v w

abbrev AnyStreamLike (α : Type u) := (StreamLike.setoid α).Quotient

namespace AnyStreamLike

def mk {α : Type u} {β : Type v} [inst : StreamLike α β] (x : β) := (StreamLike.setoid α).mkQuotient x

def head {α : Type u} : (AnyStreamLike α) → α := (StreamLike.setoid α).lift (·.head) <| by
  constructor
  · intro _
    rfl
  · simp only [Setoid.r]
    intro _ _ _ _ _ _ h
    apply heq_of_eq
    have := (h 0).head_heq
    simp_all only [Function.iterate_zero, id_eq]

def tail {α : Type u} : AnyStreamLike α → AnyStreamLike α := (StreamLike.setoid α).liftEndo (·.tail) <| by
  simp_all [Setoid.r, StreamLike.equiv, StreamLike.equivExt]
  intro _ _ h n
  have := h n.succ
  simp_all only [Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_mk_imp {α : Type u} (x : ClassSetoid.Imp (StreamLike α)) :
    tail ⟦x⟧ = ⟦⟨x.imp, x.inst, x.inst.tail x.value⟩⟧ := rfl

@[simp]
theorem iterate_tail_mk_imp (n : Nat) {α : Type u} (x : ClassSetoid.Imp (StreamLike α)) :
    tail^[n] ⟦x⟧ = ⟦⟨x.imp, x.inst, (x.inst.tail^[n] x.value)⟩⟧ := by
  apply ClassSetoid.iterate_liftGen_mk
  intro a b h n
  simp only [Setoid.r, StreamLike.equiv, id_eq] at *
  exact h n.succ

instance instStreamLike {α : Type u} : StreamLike α (AnyStreamLike α) where
  head := head
  tail := tail

@[simp]
theorem tail_mk {α : Type u} {β : Type v} [StreamLike α β] {x : β} :
    StreamLike.tail α (mk x : AnyStreamLike α) = mk (StreamLike.tail α x) := rfl

@[simp]
theorem iterate_tail_mk (n : Nat) {α : Type u} {β : Type v} [inst : StreamLike α β] {x : β} :
    (StreamLike.tail α)^[n] (mk x : AnyStreamLike α) = mk ((StreamLike.tail α)^[n] x) := by
  simp only [StreamLike.tail, mk, ClassSetoid.mkQuotient, iterate_tail_mk_imp]
