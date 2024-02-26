import Colist.StreamLike.StreamLike

universe u v w

def AnyStreamLike (α : Type u) := Quotient (StreamLike.instSetoid α)

namespace AnyStreamLike

def mk {α : Type u} {β : Type v} [inst : StreamLike α β] (x : β): AnyStreamLike α :=
  Quotient.mk (StreamLike.instSetoid α) ⟨β, inst, x⟩

instance {α : Type u} {L : Type u → Type v} [StreamLike α (L α)] : CoeOut (L α) (AnyStreamLike α) where
  coe := mk

theorem exists_rep {α : Type u} (as : AnyStreamLike α) : ∃ (β : Type v)
    (inst : StreamLike α β) (x : β), mk (inst := inst) x = as := by
  obtain ⟨x, rep⟩ := Quotient.exists_rep as
  use x.imp
  use x.inst
  use x.value
  exact rep
def head {α : Type u} : (AnyStreamLike α) → α := AnyOf.lift (StreamLike.instSetoid α) (·.head) <| by
  constructor
  · intro x
    rfl
  · simp only [Setoid.r]
    intro _ _ _ _ _ _ h
    apply heq_of_eq
    have := (h 0).head_heq
    simp_all only [Function.iterate_zero, id_eq]

def tail {α : Type u} : AnyStreamLike α → AnyStreamLike α := AnyOf.liftGenId (StreamLike.instSetoid α) (·.tail) <| by
  simp_all [Setoid.r, StreamLike.equiv, StreamLike.equivExt]
  intro _ _ h n
  have := h n.succ
  simp_all only [Function.iterate_succ, Function.comp_apply]

@[simp]
theorem tail_mk_imp {α : Type u} (x : AnyOf.Imp (StreamLike α)) :
    tail ⟦x⟧ = ⟦⟨x.imp, x.inst, x.inst.tail x.value⟩⟧ := rfl

@[simp]
theorem iterate_tail_mk_imp (n : Nat) {α : Type u} (x : AnyOf.Imp (StreamLike α)) :
    tail^[n] ⟦x⟧ = ⟦⟨x.imp, x.inst, (x.inst.tail^[n] x.value)⟩⟧ := by
  apply AnyOf.iterate_liftGen_mk
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
  simp only [StreamLike.tail, mk, iterate_tail_mk_imp]
